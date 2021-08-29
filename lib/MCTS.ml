open Printf
open MCTSutils

(*type stats = { n : int;
      nwin : int;
      ntoprove : int;
}

type oparbre = And | Or | Not
type feuilletype = Formu of SS.t * iformula | Direct of bool
type state = Proven of bool | Ni
type arbre = Noeud of (state * arbre list * oparbre * stats) | Feuille of feuilletype *)

exception Found of state * int
exception Unexpec 
let uctconstant = ref (sqrt 2.0)
let pp = ref false

let isProven t = match t with
  | Feuille(Direct b) | Noeud(Proven b, _,_,_) -> Proven b
  | _ -> Ni (*check children's state now?*)
 
let resolved t = match isProven t with
Proven _ -> true
  | _ -> false


(* select one node with highest UCT or never explored in a list, returns it and its position in the list *)
let selectone n l = let _= if false then eprintf "\nDeciding between %d ..\n%s" (List.length l) (Print.list' "" "\n-->" "\n\n"  Print.arbreK l)in match l with [] -> assert false
  | l -> let rec aux maxUCT maxNode maxNum num l = match l with
    | [] -> maxNode, maxNum
    | h::t ->  if resolved h then aux maxUCT maxNode maxNum (num+1) t
    else
        begin match h with
      | Feuille(Direct _) -> aux maxUCT maxNode maxNum (num+1) t
      | Feuille(Formu(_, _)) as x -> x, num
      | Noeud(_, _ , _ , stat) as newp when stat.n = 0 -> newp, num
      | Noeud(_, _ , _, stat) as newp -> let score = UCT.uCB n stat.n stat.nwin !uctconstant in
      let _= if stat.n > (-1) then if false then eprintf "select : %s(max=%f) -> %f\n" (Print.arbre newp) maxUCT score in 
        if score > maxUCT then aux score newp num (num+1) t  else aux maxUCT maxNode maxNum (num+1) t
      end
  in let choice, num = aux (-0.9) (Feuille(Direct true)) (-1) 0 l in let _= if false then eprintf "Chosen the %d = %s\n\n" (num+1) (Print.arbre choice) in choice,num

let notyetExplored stat = stat.n = 0
(* goes through a tree t by selection to find a node not yet played out once = a feuille or
 a noeud with zero played 
 returns : the updated selected node, and a path to it [1,2,1] = take first child, take second, take first and you are on the node*)
let selectexpand t =  
  match t with
  | Feuille(Direct _) -> let _= eprintf "found a feuille directly " in raise Unexpec (* shouldn't happen *)
  | _ -> begin 
    let rec aux path tree = let _= if false then eprintf "selectexpand : %s\n" (Print.arbre tree) in 
    match tree with
    | Feuille(Direct _) ->let _= eprintf "ffound a feuille directly " in  raise Unexpec(* shouldn't happen *)
    | Feuille(Formu(v, f)) as tt -> let f = if (!pp && propositional f) then quicksolve tt else f in (splitIF v f, path)
    | Noeud(_, l, _, stat) as newp -> if (notyetExplored stat) then (newp, path) else let choice,num = selectone stat.n l in
      aux (num::path) choice
   in let newp, path = aux [] t in
   (newp, List.rev path)
  end

let chooseone t =
  let i = Random.int (List.length t) in
  List.nth t i

let rec playout t =
  match t with
  | Feuille(Direct b) -> b
  | Feuille(Formu(v, f)) -> playout (splitIF v f)
  | Noeud(_, l, op, s) ->  match l with 
    | [] -> false
    | [h] -> let x = playout h (* necessary & opti *) in (match op with Not -> not x | _-> x)
    | h::t ->  match op with
        | And -> playout h  && playout (Noeud(Ni, t, op, s))
        | Or -> let newp = chooseone (h::t) in playout newp
        | Not -> not (playout h )


let replace l i newp = let rec aux liste count acc = match liste with
  [] -> List.rev acc
        | _::t when count=i -> (List.rev (newp::acc)) @ t
        | h::t -> aux t (count+1) (h::acc)
     in aux l 0 []

let nprovecalc ntoprove childB op = match op with
    And -> (match childB with Ni -> ntoprove, Ni
      | Proven true -> ntoprove - 1, (if (ntoprove -1) = 0 then Proven true else Ni)
      | Proven false -> 0, Proven false )
    | Or -> (match childB with Ni -> ntoprove, Ni
      | Proven true -> 0, Proven true
      | Proven false -> ntoprove - 1, (if (ntoprove -1) = 0 then Proven false else Ni))
    | Not -> match childB with Ni -> 1, Ni
      | Proven childB -> 0, Proven (not childB)
(* return t with all nodes in path updated with res=bool, b=state of the last number of path and newp its node *)
let rec update tree newp path res = match path with [] -> newp 
    | h::t-> match tree with
        | Noeud(_, l, op, stat) -> let newt = update (List.nth l h) newp t res in
        let newl = replace l h newt in
        let b = isProven newt in
        let newnprove, newb = nprovecalc stat.ntoprove b op in
        let nstat = {n=stat.n+1 ; nwin=stat.nwin + (if res then 1 else 0); ntoprove=newnprove} in
        Noeud(newb, newl, op, nstat)
        | _ -> raise Unexpec

(* take a node, its proven state and last res from playout -> return the node with updated stats *)
(* here we don't replace a proven Noeud by a feuille so that we don't forget some part of the tree, as we might need this subtree as part of the proof *)
let updatenode x res b = match x with
  Noeud(_, l, op, s) -> Noeud(b, l, op, {n=s.n+1; nwin=s.nwin + (if res then 1 else 0); ntoprove=s.ntoprove})
  |y -> y

let solve_fi f n =
  let t = ref (splitIF (SS.empty) f )in
  try
    for i=0 to n do
      let _= if false then eprintf "arbre now = %s\n" (Print.arbre !t) in 
      let _= if false then eprintf "%d ----------------- New MCTS LOOP\n" i in 
      let proof = isProven !t in match proof with
      | Proven b -> raise (Found(Proven b, i))
      | Ni -> begin
        let newp, path = selectexpand !t in
        let _= if false then eprintf "Path now = %s\n" (String.concat "," (List.map string_of_int path)) in 
        let b = isProven newp in
        let res = match b with
        | Proven b -> b
        | Ni -> playout newp (* disabling random playouts -> 50% speedup ~ *)
        in
        let newps = updatenode newp res b in
        (*let _= eprintf "newp = %s, res = %b\n" (Print.arbre newp) res in 
        let _= eprintf "newps = %s, res = %b\n" (Print.arbre newps) res in *)
        t := update !t newps path res 
      end
    done ; (Ni,n)
  with Found (x,i) -> x,i
  
let solve df ~n ~constant ~quicksolver =
  if quicksolver = "propositional" then pp := true else pp := false ;
  uctconstant := constant;
  let f = MCTSutils.formToIForm df in
  (*let tree = MCTSutils.splitIF (MCTSutils.SS.empty) f in*)
  let bdag, nodecount = solve_fi f n in MCTSutils.toOption bdag, [sprintf "%d" nodecount]
