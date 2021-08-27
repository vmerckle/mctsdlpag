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
