(* todo : replace middle(some b,,,,) by leaf b *)
(* replace unexplored stuff by something else, way too complex? *)

open Printf
open Formula
open Node

let _ = ignore (sprintf "")

module D = Dlpag
(*
module Print = struct
  let formula_to_int = Hash.Print.hashtbl Formula.Print.formula (sprintf "%d")
  let int_to_node = Hash.Print.hashtbl (sprintf "%d") node
end*)


(* type unexploredNode = PreNodeSingle of model
                    | PreNodeAnd of model * model 
                    | PreNodeAndNode of unexploredNode * model 
                    | PreNodeNot of model
type nop = And | Or | Not
type treeNode = | Unexplored of unexploredNode
                | Middle of bool option ref * nop * int list * Statistics.t
                | Leaf of bool
                | RunLeaf of model
                (* v psi s phi / v\models<s <- psi>phi *)
                | RunAssign of Valuation.t * Formula.formula * string * Formula.formula *)

let oracle v f = Simple.depth_first_single v f
let small_enough = ref Deciders.neversmall
let constant = ref (sqrt 2.)
(*let small_enough f = ignore f;false (* Helper.allbutkleene f *)*)
 (* (Helper.notmodal f)|| false (* (Helper.size f) < 1*)*)
(*let size = (Helper.size f)  in
(*let _= printf "size= %d\n%s\n" size (Formula.Print.formula f) in*)
(*let _= printf "%d\t" size  in*)
size < 100*)

exception FoundI of int
exception Found of bool * int

module Print = struct
  let boolopt = function
    | None -> "none"
    | Some b -> sprintf "Some %B" b
  let noperator = function
    | And -> "And"
    | Or -> "Or"
    | Not -> "Not"
  let rec unexploredNode = function
    | PreNodeSingle m -> sprintf "single(%s)" (Formula.Print.model m)
    | PreNodeAnd(m1, m2) -> sprintf "and(%s, %s)"  (Formula.Print.model m1) (Formula.Print.model m2)
    | PreNodeAndNode(u, m) -> sprintf "andn(%s, %s)" (unexploredNode u) (Formula.Print.model m)
    | PreNodeNot m -> sprintf "not(%s)" (Formula.Print.model m)
  let rec treeNode = function
    | Unexplored(u) -> sprintf "unexp(%s)" (unexploredNode u)
    | Middle(bo, nop, li, stat) -> sprintf "Middle(%s, %s, %s, %s)\n%s" (boolopt !bo) (noperator nop) (Formula.Print.list (sprintf "%d") li) (Statistics.Print.statistics stat) (int_formula li)
    | Leaf b -> sprintf "leaf(%B)" b
    | CountedLeaf b -> sprintf "countedLeaf(%B)" b
    | RunLeaf m -> sprintf "runleaf(%s)" (Formula.Print.model m)
    | RunAssign(v,psi,s,phi) -> sprintf "runassign(%s,%s,%s,%s)" (Formula.Print.valuation v) (Formula.Print.formula psi) s (Formula.Print.formula phi)
    and one_int_formula i = let node = Hash.get_node i in
  sprintf "\t%d -> %s\n" i (treeNode node)
  and int_formula li = (String.concat "" (List.map one_int_formula li))
end

(*REM could convert to (v, f:InternalFormulaType) if there is some heavy lifting.. *)
(* Converts v,f to unexpl(v, f) with room for preprocessing *)
let rec model_to_unexplored(v:Valuation.t) (f:Formula.formula) = 
  match f with
    | Base _ | Var _ | ListF(_, []) -> Leaf(oracle v f)
    | Modal(_, _, Base b) -> Leaf b
    | _ ->
  if (!small_enough f) then RunLeaf(v, f)
  else match f with
    | Base _ | Var _ | ListF(_, []) -> Leaf(oracle v f)
    | ListF(_, [f]) -> model_to_unexplored v f
    | ListF(_, _) -> Unexplored(PreNodeSingle(v,f))
    | Modal(_, _, Base b) -> Leaf b
    | Modal(diam, p, phi) -> match p with
      | Assign(s, psi) -> begin
        match psi with (* very fast assign *)
          | Base _ | Var _ | ListF(_, []) ->(
            if oracle v psi then
              model_to_unexplored (Valuation.add s v) phi
            else
              model_to_unexplored (Valuation.remove s v) phi
          )
          | _ -> if !small_enough psi then RunAssign(v, psi, s, phi)
               else Unexplored(PreNodeSingle(v, f))
      end
      | ListP(_, []) -> model_to_unexplored v phi
      | ListP(_, [p]) -> model_to_unexplored v (Modal(diam, p, phi))
      | ListP(Seq, p::lp) -> let newf = Modal(diam, p, Modal(diam, ListP(Seq, lp), phi)) in model_to_unexplored v newf
      | _ -> Unexplored(PreNodeSingle(v, f))

(* v,f -> int <- unexploredNode *)
let register_unexploredf v f = Hash.register_node (model_to_unexplored v f)
(* list of formula to unexplored nodes, to list of integers *)
let register_listunexploredf v lf = let rec aux lacc = function
  | [] -> lacc (* TODO remove tailcall? *)
  | f::lf -> (aux [@tailcall]) ((register_unexploredf v f)::lacc) lf
in aux [] lf

let programlist_to_formula diam lp phi = let rec aux lacc = function
  | [] -> lacc
  | p::lp -> aux ((Modal(diam, p, phi))::lacc) lp
in aux [] lp

let diamswitch diam = function
  | And when not diam -> Or
  | Or when not diam -> And
  | x -> x
(* explore a model *)
let rec model_to_explored ((v, f):model) = 
  let fop_to_nop = function
    | Conj -> And
    | Disj -> Or
  in
  match f with
    | Base _ | Var _ | ListF(_, []) | ListF(_, [_]) | Modal(_, _, Base _) -> assert false (* f didn't go through model_to_unexplored : strange *)
    | ListF(fop, lf) -> Middle(ref None, fop_to_nop fop, register_listunexploredf v lf, Statistics.init (List.length lf))
    | Modal(diam, p, phi) -> match p with
      | Assign(s, psi) -> begin
        let and1 = Hash.register_node (Unexplored(PreNodeAnd((v, psi), ((Valuation.add s v),phi)))) in
        let and2 = Hash.register_node (Unexplored(PreNodeAndNode(PreNodeNot(v, psi), ((Valuation.remove s v),phi)))) in
        Middle(ref None, Or, [and1; and2], Statistics.init 2)
      end
      | ListP(_, [p]) -> model_to_explored (v,(Modal(diam, p, phi)))
      | ListP(_, []) -> assert false (* should also have been taken into account by the unexplored above, right ?*)
      | Test psi -> 
          let ipsi = register_unexploredf v psi in
          let iphi = register_unexploredf v phi in
          Middle(ref None, And, [ipsi; iphi], Statistics.init 2)
      | ListP(Seq, _::_) -> assert false (* not sure
          begin
        let newf = Modal(diam, p, Modal(diam, ListP(Seq, lp), phi)) in
        model_to_explored v newf
      end *)
      | ListP(U, p::lp) -> Middle(ref None, diamswitch diam Or, register_listunexploredf v (programlist_to_formula diam (p::lp) phi), Statistics.init (List.length (p::lp)))
      | Kleene p -> begin
          let iphi = register_unexploredf v phi in
          let newf = Modal(diam, Kleene p, phi) in
          let newnewf = Modal(diam, p, newf) in
          let li = (match Hash.find_model v newnewf with
            | Some _ -> [iphi]
            | None -> let inewnewf = register_unexploredf v newnewf in [iphi; inewnewf] )
        in Middle(ref None, diamswitch diam Or, li , Statistics.init (List.length li))
      end
          (* how to remove the stupid link to stop this?*)
      (* I think this problem is solved *)

(* replace node with its explored version *)
let explore_unexplored (node:treeNode) = 
    match node with
      | Unexplored(PreNodeSingle(m)) -> model_to_explored m
      | Unexplored(PreNodeAnd((v1, f1), (v2, f2))) -> begin
        let i1 = register_unexploredf v1 f1 in
        let i2 = register_unexploredf v2 f2 in
        Middle(ref None, And, [i1; i2], Statistics.init 2)
      end
      | Unexplored(PreNodeAndNode(unexplNot, (v1, f1))) -> begin
        let i1 = register_unexploredf v1 f1
        and i2 = Hash.register_node (Unexplored(unexplNot)) in
        Middle(ref None, And, [i1; i2], Statistics.init 2)
      end
      | Unexplored(PreNodeNot(v1, f1)) -> begin
        let i = register_unexploredf v1 f1 in
        Middle(ref None, Not, [i], Statistics.init 1)
      end
      | _ -> assert false

(* expand the childless node : new node *)
let expandN (n:treeNode) = match n with
  | Middle ({contents=Some b}, _, _, _) -> Leaf b (*REM who knew reference were just a sugarcoat around records.. *)
  | Middle _ -> assert false (*selected a middle node.. *)
  | Leaf b -> Leaf b
  | RunLeaf(v, f) -> Leaf (oracle v f)
  | RunAssign(v, psi, s, phi) -> begin
    if oracle v psi then
      Unexplored(PreNodeSingle(Valuation.add s v, phi))
    else
      Unexplored(PreNodeSingle(Valuation.remove s v, phi))
  end
  | _ -> explore_unexplored n

let expandI (i:int) = match expandN (Hash.get_node i) with
  | Leaf b -> CountedLeaf b
  | n -> n
let expand (i:int) = expandI i

let compute_score parent_nop parent_stats  i :float = match Hash.get_node i with 
  | Leaf _ | Middle({contents=Some _}, _, _, _) | Unexplored _ -> raise (FoundI i)
  | RunLeaf _ -> raise (FoundI i) (* TODO heuristic *)
  | RunAssign _ -> raise (FoundI i) (*TODO same *)
  | CountedLeaf _ -> float_of_int min_int
  | Middle({contents=None}, _, _, stats) -> UCT.compute_score parent_stats stats parent_nop !constant


let rec select_aux i path = match Hash.get_node i with
  | CountedLeaf _ -> assert false
  | Unexplored _ | Leaf _ | RunLeaf _ | RunAssign _ -> i, path
  | Middle({contents=Some _}, _, _, _) -> i,path (* solved middle node.. *)
  | Middle({contents=None}, nop, li, stats) -> select_from_list nop stats li (i::path)

and select_from_list parent_nop parent_stats li path = let rec aux bestScore bestI = function
    | [] -> bestI
    | i::li -> let s = compute_score parent_nop parent_stats i in
      if bestI = -1 || s > bestScore then
        aux s i li
      else
        aux bestScore bestI li
  in try
    let i = aux 0. (-1) li
    in select_aux i path
  with FoundI i -> i, path
let select i = select_aux i []
let playout v f = Simple.playout v f
let simulate i = match Hash.get_node i with
  | CountedLeaf _ | Leaf _ -> None
  | Middle({contents=Some _}, _, _, _) -> None
  | Middle({contents=None}, _, _, _) -> assert false  (* middle node... *)
  | RunLeaf _ | RunAssign _ -> None (*TODO have a better idea *)
  | Unexplored(PreNodeSingle(v, f)) -> Some (playout v f)
  | Unexplored(PreNodeNot(v, f)) -> Some (not (playout v f))
  | Unexplored(PreNodeAnd((v1, f1), (v2, f2))) -> Some ((playout v1 f1) && (playout v2 f2))
  | Unexplored(PreNodeAndNode(u, (v2, f2))) -> 
      match u with PreNodeNot (v,f) -> Some ((not(playout v f)) && playout v2 f2)
      | _ -> assert false (* 100% sure we don't go there *)
let update_node node res boolnode = match node with
    | Middle({contents=None}, nop, li, stats) -> begin
      let newbool, newstat = UCT.update_res stats nop res boolnode in
      match newbool with
        | None -> None, Middle({contents=None}, nop, li, newstat)
        | Some b -> Some b, CountedLeaf b
    end
    | Leaf _ -> assert false
    | CountedLeaf b -> Some b, CountedLeaf b
    | x -> None, x

(* res = playout result, boolnode = Some b if a child is now true *)
let update_single i res boolnode = 
  let newbool, newnode = update_node (Hash.get_node i) res boolnode
  in Hash.set_node i newnode ;
  newbool

let rec update_aux path res boolnode =
  match path with
  | [] -> ()
  | i::li -> let newbool = update_single i res boolnode in
    update_aux li res newbool
let update exp_node exp_i path res = 
  Hash.set_node exp_i exp_node ;
  update_aux (exp_i::path) res None

(* labeled arguments are implemented as type lel.. *)
let solve_new (f:Formula.formula) ~quicksolver ~n:(n:int) ~c =
  let _ = small_enough := quicksolver in
  let _ = constant := c in
  let iroot = register_unexploredf Valuation.empty f in
  try
    for i = 0 to n do
      (*let _ = printf "i=%d, iroot= %s\n" i (Print.treeNode (Hash.get_node iroot)) in*)
      match Hash.get_node iroot with
        | CountedLeaf b -> raise (Found(b, i))
        | Leaf b -> raise (Found (b, i))
        | _ -> begin
          let i_selected_node, path = select iroot in
      (*let _ = printf "i=%d, selected(%d)= %s\n" i i_selected_node (Print.treeNode (Hash.get_node i_selected_node)) in*)
          let expanded_node = expand i_selected_node in
          let res = simulate i_selected_node in
          let _ = update expanded_node i_selected_node path res in
          ()
        end
    done ; (None, n)
  with Found(ob, n) -> Some ob, n

let solve old_f ~n ~quicksolver ~constant =  let ob, iter = solve_new ~quicksolver ~n ~c:constant (Formula.formula_retread old_f)
in ob, [sprintf "%d" iter]
