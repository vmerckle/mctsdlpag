open Formula

let neversmall f = ignore f; false
(* fast approximate size *)
let size (f:Formula.formula) = let rec aux acc = function
    | Base _ | Var _ -> 1+acc
    | ListF(_, []) -> 0
    | ListF(_, [f]) -> aux acc f
    | ListF(fop, f::lf) -> aux ((aux 0 f)+acc+1) (ListF(fop, lf))
    | Modal(_, p, phi) -> let s = aux acc phi in
      begin 
      match p with
        | Assign(_, f) -> 2 * (aux 2 f) + s
        | Test f -> aux 1 f + s
        | ListP(_, []) -> s
        | ListP(_, [p]) -> aux acc (Modal(true, p, phi))
        | ListP(Seq, p::lp) -> aux 0 (Modal(true, p, phi)) + aux acc (Modal(true, ListP(Seq, lp), Base true))
        | ListP(U, p::lp) -> acc + s * (aux 0 (Modal(true, p, Base true))) + aux 0 (Modal(true, (ListP(U, lp)), phi))
        | Kleene p -> acc + s * (aux 0 (Modal(true, p, phi)))
      end
  in aux 0 f
let smallsize f = size f < 100

exception Above

let sizepaper (maxsize:int) (f:Formula.formula) : int = 
  let rec aux (maxsize:int) = function
    | Base _ | Var _ -> 1
    | ListF(_, []) -> 0
    | ListF(fop, f::lf) -> let maxsize, s = short f maxsize in s + aux maxsize (ListF(fop, lf))
    | Modal(_, p, phi) -> 
      begin 
      match p with
        | Assign(_, f) -> let maxsize,s = short phi maxsize in 2 * (aux (maxsize/2) f) + s
        | Test f -> let maxsize,s = short phi maxsize in aux maxsize f + s
        | ListP(_, []) -> let _,s = short phi maxsize in s
        | ListP(Seq, p::lp) -> let new_f = Modal(true, p, Modal(true, ListP(Seq, lp), phi)) in aux maxsize new_f
        | ListP(U, p::lp) -> let s = aux maxsize (Modal(true, p, phi)) in
        if s > maxsize then raise Above else (s + aux (maxsize -s) (Modal(true, ListP(U, lp), phi)))
        | Kleene p -> let nb_valsp = MCTSutils.twopow (Valuation.cardinal (Helper.variables_in_f (Modal(true, p, Base true)))) in
        let plist = List.init nb_valsp (fun n -> ListP(Seq, List.init n (fun _ -> p))) in
          aux maxsize (Modal(true, ListP(U, plist), phi))
      end
  and short f maxsize = let s = aux maxsize f in
    if s >maxsize then raise Above else (maxsize - s),s
  in aux maxsize f


let sizeagain f maxsize = 
  try let s = sizepaper maxsize f in s < maxsize
  with Above -> false

let smallsizev2 f =  sizeagain f 100
let _ = ignore smallsizev2

let rec propositional = function
    | Base _ | Var _ -> true
    | ListF(_, []) -> true
    | ListF(_, [f]) -> propositional f
    | ListF(fop, f::lf) -> propositional f && propositional (ListF(fop, lf))
    | Modal _ -> false

let rec deterministic = function
    | Base _ | Var _ -> true
    | ListF(_, []) -> true
    | ListF(_, [f]) -> deterministic f
    | ListF(fop, f::lf) -> deterministic f && deterministic (ListF(fop, lf))
    | Modal(_, p, phi) -> deterministic phi && deterministicp p
  and deterministicp = function
    | Assign _ -> true
    | Test _ -> true
    | ListP(_, []) -> true
    | ListP(Seq, p::lp) -> deterministicp p && deterministicp (ListP(Seq, lp))
    | ListP(U, _) -> false
    | Kleene _ -> false

let rec allbutkleene = function
    | Base _ | Var _ -> true
    | ListF(_, []) -> true
    | ListF(_, [f]) -> allbutkleene f
    | ListF(fop, f::lf) -> allbutkleene f && allbutkleene (ListF(fop, lf))
    | Modal(_, p, phi) -> allbutkleene phi && allbutkleenep p
  and allbutkleenep = function
    | Assign _ -> true
    | Test _ -> true
    | ListP(_, []) -> true
    | ListP(Seq, p::lp) -> allbutkleenep p && allbutkleenep (ListP(Seq, lp))
    | ListP(U, p::lp) -> allbutkleenep p && allbutkleenep (ListP(Seq, lp))
    | Kleene _ -> false
(*
(* how deeply undeterministic our formula is *)
(* compute worst case number of valuation? *) (* TODO redo this, it's wrong *)
let udeter_depth(f:Formula.formula) = let rec aux acc = function
    | Base _ | Var _ -> 0
    | ListF(_, []) -> 0
    | ListF(_, [f]) -> aux acc f
    | ListF(fop, f::lf) -> aux ((aux 0 f)+acc) (ListF(fop, lf))
    | Modal(_, p, phi) -> let s = aux 0 phi in
      begin 
      match p with
        | Assign(_, f) | Test f -> acc * max (aux 0 f) s
        | ListP(_, []) -> acc * s
        | ListP(U, [p]) -> aux acc (Modal(true, p, phi))
        | ListP(Seq, p::lp) -> (aux 0 (Modal(true, p, phi))) + (aux acc (Modal(true, ListP(Seq, lp), Base true)))
        | ListP(U, p::lp) -> acc * (aux 0 (Modal(true, p, phi))) + acc *(aux 0 (Modal(true, ListP(Seq, lp), Base true)))
        | Kleene p -> acc + 50*s* (aux 0 (Modal(true, p, phi)))
      end
  in aux 0 f
  *)
