open Formula

let solve_call v b s = let x = (SS.mem s v) in if b then x else not x

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

(* Look through the formula for top&bot and update ? *)
let xxupdate = ()

