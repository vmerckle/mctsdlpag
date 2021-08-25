open Printf
open Formula

let hashtbl_model_to_int = Hashtbl.create 200000
let hashtbl_int_to_node = Hashtbl.create 200000
let counter = ref 2

module Print = struct
  let hashtbl h print_key print_value =
    let rec aux (acc_s:string) seq_hs = match seq_hs () with
      | Seq.Nil -> acc_s
      | Seq.Cons ((key, value), tail_seq) -> aux ((sprintf "%s -> %s\n" (print_key key) (print_value value))^acc_s) tail_seq
    in aux "" (Hashtbl.to_seq h)
end

(*REM Faster than doing hash.mem, then hash.find *)
let find_model (v:Formula.Valuation.t) (f:Formula.formula) =
  try
    Some (Hashtbl.find hashtbl_model_to_int (v,f))
  with Not_found -> None

let to_int (v:Formula.Valuation.t) (f:Formula.formula) = match f with
  | Base _ | Var(_,_) -> assert false
  | _ ->
  match find_model v f with
    | Some i -> i
    | None ->
    Hashtbl.replace hashtbl_model_to_int (v,f) !counter;
    counter := !counter + 1;
    !counter - 1

let set_node (i:int) (node:Node.treeNode) =
  Hashtbl.replace hashtbl_int_to_node i node
let register_node node =
  set_node !counter node;
  counter := !counter + 1;
  !counter - 1

let get_node (i:int) =
  Hashtbl.find hashtbl_int_to_node i

(*REM List.map not tail recursive *)
let listf_to_int lf = let rec aux lacc = function
    | [] -> lacc
    | f::lf -> aux ((to_int f)::lacc) lf
in aux [] lf

