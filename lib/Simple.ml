open Formula
open Printf
let _ = ignore (sprintf "")
(* do a depth_first to get truth, and a depth_first to get valuation?  no, can't do that with Unions that returns different valuations*)


let aware_union (sva:SSS.t) (svb:SSS.t) =
  let rec aux bacc set_acc seq_svb = match seq_svb () with
    | Seq.Nil -> bacc, set_acc
    | Seq.Cons (v, tail_seq_svb) -> if SSS.mem v set_acc then aux bacc set_acc tail_seq_svb
        else (aux true (SSS.add v set_acc) tail_seq_svb)
  in aux false sva (SSS.to_seq svb)

exception ExitBool of bool
(* solves v := f, return the valuation it is currently using and the truth value *)
let rec depth_first_single v f = 
  (* let _ = eprintf "solve(%s, %s)\n" (Formula.Print.ss v) (Formula.Print.formula f) in*)
  match f with
  | Base b -> b
  | Var (b, s) -> Helper.solve_call v b s
  | ListF(Conj, []) -> true
  | ListF(Disj, []) -> false
  | ListF(_, [f]) -> depth_first_single v f
  | ListF(fop, f::lf) ->
    (*let f, lf = Helper.random_pop (f,lf) in*) (* 50% slower *)
    let res = depth_first_single v f in (
    match fop with
      | Conj -> if not res then res else depth_first_single v (ListF(fop, lf))
      | Disj -> if res then res else depth_first_single v (ListF(fop, lf))
    )
  (* naming : <.. psi ..>phi *)
  | Modal(diam, p, phi) -> (match phi with
    | Base b -> b
    | _ -> match p with
      | Assign(s, psi) -> (
        let res = depth_first_single v psi in
        if res then depth_first_single (Valuation.add s v) phi
        else depth_first_single (Valuation.remove s v) phi )
      | Test psi -> (* choice : solve psi first *)
          let res = depth_first_single v psi in
          if not res then res else depth_first_single v phi
      | ListP(_, []) -> depth_first_single v phi
      | ListP(Seq, p::lp) -> depth_first_single v (Modal(diam, p, Modal(diam, ListP(Seq, lp), phi)))
      | ListP(U, p::lp) -> (
        let p, lp = Helper.random_pop (p,lp) in
        let res = depth_first_single v (Modal(diam, p, phi)) in
        if diam then
          if res then res else depth_first_single v (Modal(diam, ListP(U, lp), phi))
        else
          if not res then res else depth_first_single v (Modal(diam, ListP(U, lp), phi))
      )
      | Kleene p -> let res = depth_first_single v phi in if res && diam || not res && not diam then res
      else apply_kleene_check_single diam v p phi (* this doesn't return the valuation that makes phi true, but do we even need it ?*)
  )
(* given a set of valuation, verify if any (diam) or all (not diam) makes phi true *)
and kleene_step diam (sv:SSS.t) phi =
  (* let _ = eprintf "Kleene step with sv=%s\n" (Formula.Print.sss sv) in*)
  let rec aux seq_v = match seq_v () with
    | Seq.Nil -> false
    | Seq.Cons (v, tail_seq_v) -> let res = depth_first_single v phi in (
      if (res && diam) || (not res && not diam) then res
      else aux tail_seq_v
    )
  in aux (SSS.to_seq sv)
(* apply the program p to the set of valuation sv, returns the new set of valuations *)
and apply_program (sv:SSS.t) p =
  let rec aux set_acc seq_v = 
    match seq_v () with
    | Seq.Nil -> set_acc
    | Seq.Cons (v, tail_seq_v) ->
        let newv = (apply_program_single v p) in
let unioned = SSS.union newv set_acc in
    (* let _ =eprintf "apply_prog, %s to %s, new set = %s\n" (Formula.Print.ss v) (Formula.Print.sss newv) (Formula.Print.sss unioned) in*)
    aux unioned tail_seq_v
        (*aux (SSS.union (apply_program_single v p) set_acc) tail_seq_v*)
  in aux SSS.empty (SSS.to_seq sv)

(* apply the program p to a valuation v *)
and apply_program_single v p = 
  (* let _ = eprintf "apply_prog_single %s %s\n" (Formula.Print.ss v) (Formula.Print.program p) in*)
  match p with
  | Assign(s, psi) -> (
    let res = depth_first_single v psi in
    if res then SSS.singleton (Valuation.add s v)
    else SSS.singleton (Valuation.remove s v)
  )
  | Test psi ->
      let res = depth_first_single v psi in
      if not res then SSS.empty else SSS.singleton v
  | ListP(_, []) -> SSS.singleton v
  | ListP(Seq, [p]) -> apply_program_single v p (* 5% speedup *)
  | ListP(U, [p]) -> apply_program_single v p
  | ListP(Seq, p::lp) -> let sv = apply_program_single v p in apply_program sv (ListP(Seq, lp))
  | ListP(U, p::lp) -> SSS.union (apply_program_single v p) (apply_program_single v (ListP(U, lp)))
  | Kleene p -> apply_kleene (SSS.singleton v) (SSS.singleton v) p

(* apply the program p* to the set of valuations svals *)
and apply_kleene (svals:SSS.t) (sv:SSS.t) p =
  let new_sv = apply_program sv p in
  let added_something, new_svals = aware_union svals new_sv in
  if added_something then
    apply_kleene new_svals new_sv p
  else
   svals 

  (* solve {a} |= <p*>phi (or [p*]phi) *)
and apply_kleene_check_single diam v p phi : bool =
  apply_kleene_check SSS.empty (SSS.singleton v) p diam phi
  (* solve {{a}, {b}} |= <p*>phi (or [p*]phi) *)
and apply_kleene_check (already_checked_vals:SSS.t) (to_check_vals:SSS.t) p diam phi :bool = 
  let new_already_checked_vals = SSS.union already_checked_vals to_check_vals in
  let new_vals = apply_program to_check_vals p in
  let real_new_vals = SSS.diff new_vals already_checked_vals in
  let phitrue = kleene_step diam real_new_vals phi in
  if (phitrue && diam) || (not phitrue && not diam) then phitrue
  else (
    if SSS.cardinal real_new_vals > 0 then
      let new_already_checked_vals = SSS.union new_already_checked_vals real_new_vals in
      apply_kleene_check new_already_checked_vals real_new_vals p diam phi
    else
     false
  )

  (* add a reference to count the amount of node we go through *)
let solve (f:Formula.formula) = Some (depth_first_single (Valuation.empty) f)
let solve_std (f:Formula.formula) = Some (depth_first_single (Valuation.empty) f), 0

let rec playout v f = match f with
  | Base b -> b
  | Var (b, s) -> Helper.solve_call v b s
  | ListF(Conj, []) -> true
  | ListF(Disj, []) -> false
  | ListF(_, [f]) -> playout v f
  | ListF(fop, f::lf) ->(
    match fop with
      | Conj -> 
          let res = playout v f in (
          if not res then res else playout v (ListF(fop, lf)) )
      | Disj -> let f = Helper.random_select (f, lf) in playout v f
  )
  | Modal(diam, p, phi) -> (match phi with
    | Base b -> b
    | _ -> match p with
      | Assign(s, psi) -> (
        let res = playout v psi in
        if res then playout (Valuation.add s v) phi
        else playout (Valuation.remove s v) phi )
      | Test psi -> (* choice : solve psi first *)
          let res = playout v psi in
          if not res then res else playout v phi
      | ListP(_, []) -> playout v phi
      | ListP(Seq, p::lp) -> playout v (Modal(diam, p, Modal(diam, ListP(Seq, lp), phi)))
      | ListP(U, p::lp) -> (
        if diam then
          let p = Helper.random_select (p,lp) in
          let res = playout v (Modal(diam, p, phi)) in
          if res then res else playout v (Modal(diam, ListP(U, lp), phi))
        else
          let p,lp = Helper.random_pop (p,lp) in
          let res = playout v (Modal(diam, p, phi)) in
          if not res then res else playout v (Modal(diam, ListP(U, lp), phi))
      )
      | Kleene p -> let res = playout v phi in if res && diam || not res && not diam then res else (ignore p;false))
      (*TODO add a random amount of applying the program ?*)
