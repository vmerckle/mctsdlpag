open Formula

let solve_call v b s = let x = (Valuation.mem s v) in if b then x else not x

let direct_solve v f = match f with
  | Base b -> Some b
  | Var(b, s) -> Some (solve_call v b s)
  | ListF(_, []) -> Some true
  | _ -> None


(* return list without its i-th element *)
let remove_nth l n = let rec aux lacc nacc l = match l with
    | [] -> assert false
    | _::t when nacc = n -> (List.rev_append lacc t)
    | h::t -> aux (h::lacc) (nacc+1) t
  in aux [] 0 l

(* return random element of a non empty list *)
let random_select (x,l) =
  let l = x::l in
  let n = Random.int (List.length l) in
  List.nth l n
(* return random element of a list, and the list without that element *)
let random_pop (x,l) =
  let l = x::l in
  let n = Random.int (List.length l) in
  List.nth l n, remove_nth l n


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
let rec notmodal = function
    | Base _ | Var _ -> true
    | ListF(_, []) -> true
    | ListF(_, [f]) -> notmodal f
    | ListF(fop, f::lf) -> notmodal f && notmodal (ListF(fop, lf))
    | Modal _ -> false

let rec deteronly = function
    | Base _ | Var _ -> true
    | ListF(_, []) -> true
    | ListF(_, [f]) -> deteronly f
    | ListF(fop, f::lf) -> deteronly f && deteronly (ListF(fop, lf))
    | Modal(_, p, phi) -> deteronly phi && deteronlyp p
  and deteronlyp = function
    | Assign _ -> true
    | Test _ -> true
    | ListP(_, []) -> true
    | ListP(Seq, p::lp) -> deteronlyp p && deteronlyp (ListP(Seq, lp))
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

(* return the set of variables used in f *)
let variables_in_f f = let rec aux sacc = function
    | Base _ -> sacc
    | Var (_, s) -> Valuation.add s sacc
    | ListF(_, []) -> sacc
    | ListF(_, [f]) -> aux sacc f
    | ListF(fop, f::lf) ->aux (aux sacc f) (ListF(fop, lf))
    | Modal(_, p, phi) -> aux (auxp sacc p) phi
  and auxp sacc = function
    | Assign(_, f) -> aux sacc f (* the variable being assigned is not necessarly used *)
    | Test f -> aux sacc f
    | ListP(_, []) -> sacc
    | ListP(_, [p]) -> auxp sacc p
    | ListP(pop, p::lp) -> auxp (auxp sacc p) (ListP(pop, lp))
    | Kleene p -> auxp sacc p
  in aux Valuation.empty f

(* return the variables in v that appear in f *)
let reduce v f = Valuation.inter v (variables_in_f f)
