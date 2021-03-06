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
