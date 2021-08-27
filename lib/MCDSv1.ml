open Printf

module D = Dlpag

(* type iformula = CallF of bool * string | Base of bool | ListF of (Ast.T.foperator * iformula list) | Modal of (bool * iprogram * iformula) (*| Not of iformula*)

and iprogram  = Assign of (string * iformula) | Test of iformula | ListP of (Ast.T.poperator * iprogram list) | LE of (int * iprogram) *)

(*type feuilletype = Formu of SS.t * iformula | Direct of bool *)
exception Found of MCTSutils.state * int
exception Unexpected of string


type stats = { n : int;
      nwin : int;
}
let ddebug = false

(* either it's proven, or a node, or an unexpanded  formula, or unexplored And/or *)
type dag = Proof of bool | PNoeud of int | Formu of MCTSutils.SS.t * MCTSutils.iformula 
type oparbre = And | Or | Not

(* int to *)
(* explored flag * AND/OR/NOT * enfants * statistics *)
type dagnoeud = Noeud of bool * oparbre * dag list * stats | Proven of bool

let counter = ref 0
(* formula -> int *)
let hfi = Hashtbl.create 200000
(* int -> node *)
let hin = Hashtbl.create 200000
let getNode i = try 
  Hashtbl.find hin i
with Not_found -> raise (Unexpected (sprintf "how? %d" i))

module Print =
  struct
    let vf (v,f) = sprintf "%s|=%s" ((MCTSutils.Print.set' "{" "," "}") v) (MCTSutils.Print.iformula f)
    let dag = function
      | Proof b -> sprintf "%b" b
      | PNoeud i -> sprintf "->%d" i
      | Formu (v,f) -> vf (v,f)
    let oparbre = function
      | And -> "And"
      | Or -> "Or "
      | Not -> "Not"
    let stats = function
      {n; nwin} -> sprintf "(n:%d, nwin:%d)" n nwin
    let sbool = function true -> "T" | false -> "F"
    let rec fulldag depth d = match d with
      | PNoeud i when depth <= 0-> (match (getNode i) with Proven b -> sprintf "{%b}" b | _ -> sprintf "->%d" i)
      | PNoeud i -> sprintf "%d->%s" i (fulldagnoeud (depth -1) (getNode i))
      | other -> dag other
    and listdag depth dl sep = (String.concat sep (List.map (fulldag depth) dl))
    and fulldagnoeud depth = function
      | Noeud(ex, op, dl, s) -> sprintf "N(%s, %s, %s, [%s])" (sbool ex) (stats s) (oparbre op) (listdag depth dl "; ")
      | Proven b -> sprintf "{%b}" b
    let dagnoeud d = fulldagnoeud 0 d

    let hashish h keyp valp = 
      let rec aux x ss = match x () with
      Seq.Nil -> ss
      | Seq.Cons ((k, v), t) -> aux t ((sprintf "%s -> %s" (keyp k) (valp v))::ss)
      in let s = aux (Hashtbl.to_seq h) [] in
   String.concat "\n" s ^ "\n"

    let intlist l = sprintf "[%s]" (String.concat ";" (List.map string_of_int l))
end




(* key : (val,formula) 
   value : int counter *)
type key = MCTSutils.SS.t * MCTSutils.iformula

let useCounter counter =
  let x = !counter in (counter := !counter + 1 ; x)

let printList l = sprintf "%s" (String.concat "," (List.map (function i -> sprintf "%d" i) l))
let hashVFormulaToInt hh (vf:key) counter = 
  if Hashtbl.mem hh vf then ( Hashtbl.find hh vf ) (* micro opt possible *)
  else ( Hashtbl.replace hh vf !counter; counter := !counter + 1; !counter - 1 )

(* key : int, 
   value : dagnoeud *)
(* there are def ways to code this better TODO *)
let hashIntToNode hh i noeud = 
  Hashtbl.replace hh i noeud

let ptoFormu v f b p = Formu(v, MCTSutils.Modal(b, p, f)) 
let _ = ptoFormu (* TODO *)

let toFormu (v:MCTSutils.SS.t) f = Formu(v, f)

let statInit = {n=0; nwin=0}


let bDiff = function true -> Or | false -> And (* simple diff between box and diamonds *)

let ptoFormu v f b p = Formu(v, MCTSutils.Modal(b, p, f))

(* Take formula, return associated node *)
(* a|=a^b -> And(a|=a, a|=b) *)
let rec splitF v f = ( match f with 
    | MCTSutils.CallF (b, s) -> Proven ( let x = (MCTSutils.SS.mem s v) in if b then x else not x)
    | MCTSutils.Base b ->  Proven b
    | MCTSutils.ListF(op, l) -> Noeud(false, (match op with D.Ast.T.Conj -> And | D.Ast.T.Disj -> Or), List.map (toFormu v) l, statInit)
    | MCTSutils.Modal(b, p, f) -> (match p with
      | MCTSutils.Assign(s, fa) -> let vs = MCTSutils.SS.add s v and vns = MCTSutils.SS.remove s v in 
      let ndouble = splitF v fa in 
        let idouble = hashVFormulaToInt hfi (v, fa) counter in 
        let inot = useCounter counter in
        let iand1 = useCounter counter in
        let iand2 = useCounter counter in
        let nand1 = Noeud(false, And, [PNoeud(idouble); Formu(vs, f)], statInit) in 
        let nnot = Noeud(true, Not, [PNoeud(idouble)], statInit) in  (* TODO no need to visit a Not? *)
        let nand2 = Noeud(false, And, [PNoeud(inot); Formu(vns, f)], statInit) in 
        let _ = hashIntToNode hin iand1 nand1 in 
        let _ = hashIntToNode hin iand2 nand2 in 
        let _ = hashIntToNode hin inot nnot in
        let _ = hashIntToNode hin idouble ndouble in 
        Noeud(false, Or, [PNoeud iand1; PNoeud iand2], statInit)
      | MCTSutils.Test fp -> Noeud(false, And, [Formu(v, fp); Formu(v, f)], statInit)
      | MCTSutils.ListP(D.Ast.T.Seq, l) ->(match l with 
        | [] -> Noeud(false, And, [Formu(v, f)], statInit)
        | [h] -> Noeud(false, And, [(Formu(v, MCTSutils.Modal(b, h, f)))], statInit)
        | h::t -> Noeud(false, And, [Formu(v, MCTSutils.Modal(b, h, MCTSutils.Modal(b, MCTSutils.ListP(D.Ast.T.Seq, t), f)))], statInit)
      )
      | MCTSutils.ListP(D.Ast.T.U, l) -> Noeud(false, bDiff b, List.map (ptoFormu v f b) l, statInit)
      | MCTSutils.LE(n, p) -> ( match n with
        |0 -> Noeud(false, And, [Formu(v, f)], statInit)
        |1 -> Noeud(false, bDiff b, [Formu(v, f); Formu(v, (MCTSutils.Modal(b, p, f)))], statInit)
        |n -> Noeud(false, bDiff b, [Formu(v, f); Formu(v, (MCTSutils.Modal(b, p, Modal(b, LE(n-1, p), f))))], statInit)
      )
    )
  )

(* From Valuation |= formula, creates : (v, formula) -> identifier -> Node *)
(* a |= b^a  - expand -> (a, b^a) -> 123 -> AND(a|=b, a|=a) *)
(* returns identifier *)
let expand v f =
  let vfi = hashVFormulaToInt hfi (v, f) counter in
  let t = splitF v f in
  ( hashIntToNode hin vfi t ; vfi)


let uCB ntotal n nwin = 
  let ntotal, n, nwin = float_of_int ntotal, float_of_int n, float_of_int nwin in 
  nwin/.n +. 0.4 *. sqrt(log(ntotal)/.n)


let calcUCB op n stat = 
  match op with
    | Or | Not|And -> uCB n stat.n stat.nwin
    (*| And -> uCB n stat.n (stat.n - stat.nwin) *)(*we focus on finding a false*)

type scoreR = Unexplored | Score of float | Solved of bool

(* dag -> scoreR *)
let score h n op = match h with
  Proof b-> Solved b
  | Formu(_, _) ->   Unexplored
  | PNoeud(i) -> match getNode i with
    | Proven b ->  Solved b
    | Noeud(_, _, _ ,stat) when stat.n = 0 -> Unexplored
    | Noeud(false, _, _ ,_) -> Unexplored
    | Noeud(true, _, _ ,stat) -> let x = calcUCB op n stat in  Score x

let feuille h = match h with
  Proof _-> true,(-1)
  | Formu(_, _) -> true, (-1)
  | PNoeud(i) -> match getNode i with
    | Proven _ -> true, (-1)
    | Noeud(false, _, _ ,_) -> true, (-1) (* not yet explored, so it's a leaf *)
    | Noeud(true, _, _ ,_) -> false, i

(* dag list -> best dag to explore *)
let selectL n l op = if List.length l = 1 then let _= if false then eprintf "selected one out of one\n" in List.hd l, 0 else
  let _= if false then eprintf "(n=%d) selecting %d\n" n (List.length l) in
  let rec aux l bestScore (bestDag:dag) num = match l with
  | [] -> bestDag, num
  (*| [h] -> h, num*)
  | h::t -> match score h n op with
    Unexplored -> h, num
    | Score(s) when s > bestScore -> aux t s h (num+1)
    | Score _ -> aux t bestScore bestDag (num+1)
    | Solved b -> Proof b, num(*aux t bestScore (if bestScore < 0. then (Proof b) else bestDag) (num+1) (*TODO choose it directly *)*)
  in aux l (-1.0) (Proof(false)) 0

(* id -> explorable dag *)
let rec selecti n id path = 
  let _=if ddebug then eprintf "--->%d\n" id in 
  let node = getNode id in match node with
  | Proven b -> raise (Found(MCTSutils.Proven b, -1337))
  | Noeud(_, op, l, _) -> let _=if ddebug then eprintf "%s\n\n" (Print.listdag 1 l "\n") in 
      let snode, num = (selectL n l op) in match feuille snode with
      false, idd -> selecti n idd (idd::path)
    | true, _ -> snode, path, num

(*let addWin (f:dagnoeud)*)

let replace l x i = let rec aux l j acc = match l with
  [] -> acc
  | _::t when j=i -> aux t (j+1) (x::acc)
  | h::t -> aux t (j+1) (h::acc)
in List.rev (aux l 0 [])

(* dag that's maybe a formula -> dag that's definitely a PNoeud*)
let xexpand dag = match dag with
  | Proof _ as p  -> p (* raise (Unexpected "not supposed to select a proof") *)
  | PNoeud _ as b -> b
  | Formu(v,f) -> let i = (expand v f) in PNoeud i
  (* TODO, hashtable should have only two place for top and bot, and everyone pointing to those *)

(* v,f [3, 0], num -> (v,f -> 37 -> node) and replace (v,f) by the node, inside 3, at position num *)
(* TODO this should accept parent's ID, not the whole path.. *)
(* many ways to reduce hashtable usage in some place, *)
(* expand a node and update its parent, return new node *)
let expandx node path num =  
  match path with
    [] -> raise (Unexpected ("need a prent " ^ (printList path)))
  | iparent::_ -> let nnode = xexpand node in let newparent =
    match getNode iparent with
        Proven _ -> raise (Unexpected "parent can't be a simple proof")
      | Noeud(_, op, l, stat) -> Noeud(true, op, replace l nnode num, stat)
  in hashIntToNode hin iparent newparent ; nnode

(* is that dag's figured out? *)
let dagDirectTruth d = match d with
  Proof b -> Some b
  | PNoeud i -> (match getNode i with Proven b -> Some b | _ -> None)
  | Formu(_,_) -> None

  (* AND(top, formula, top) -> [formula], None
   Not(bot) ->  [], Some true *)
let reduce op l = let rec aux l nl booli =  match l with
  | [] -> nl, None
  | [h] -> (match dagDirectTruth h with
    | None -> (h::nl), None
    | Some b -> match op with
      | Not -> [], Some(not b)
      | And -> if not b then [], Some false else if booli then [], Some true else nl, None
      | Or -> if b then [], Some true else if booli then [], Some false else nl, None
  )
  | h::t -> match dagDirectTruth h with
    | None ->  aux t (h::nl) false
    | Some b -> match op with
      | Not -> [], Some(not b)
      | And -> (if b then aux t nl true else [], Some false)
      | Or  -> (if b then [], Some true else aux t nl true)
in aux l [] true



(* [a,b..c] (all numbers to a dagnoeud, not a proof)) : a (usually) has an additional proof as child and might now be a proof *)
let rec goodupdate path = match path with
      | [] -> ()
      | h::t -> let newnode,cont = (match getNode h with
        | Proven _ -> raise (Unexpected "can't be a proven here")
        | Noeud(_, op, l, st) -> let nl, res = reduce op l in
          match res with
            None -> Noeud(true, op, nl, st), false
            | Some b ->  Proven b, true
      ) in hashIntToNode hin h newnode ; if cont then goodupdate t

let chooseone t =
  let i = Random.int (List.length t) in
  List.nth t i
let rec playoutdag dag = match dag with
  Proof b -> b
      | Formu(v,f) -> MCTS.playout (MCTSutils.splitIF v f)
      | PNoeud i -> playout (getNode i)
and playout dagnoeud = match dagnoeud with
  Proven b -> b
      | Noeud(_, op, l, _) -> match op with
          Not -> not (playoutdag (List.hd l))
        | And -> playoutdag (chooseone l) (*(match l with [] -> true | h::t -> playoutdag h && playout (Noeud(x, op, t, y)))*)
        | Or -> playoutdag (chooseone l)


   (* update stat of a PNoeud->Noeud *)
let updateNoeud dagnoeud (resultat:bool) id = let nnoeud = (match dagnoeud with
  Proven _ as p -> p
        | Noeud(_, op, l, stat) -> let _= if false then eprintf "id=%d updatenoeud n:%d, nwin:%d -> %d\n" id stat.n stat.nwin (stat.nwin + (if resultat then 1 else 0)) in   Noeud(true, op, l, {n=stat.n+1 ; nwin=stat.nwin + (if resultat then 1 else 0)}) 
) in hashIntToNode hin id nnoeud

let rec updatePath path res = match path with
[] -> ()
        | h::t -> updateNoeud (getNode h) res h ; updatePath t res

let debugHash content = 
      let _=eprintf "            Hashtable formula -> int : %d entries\n" (Hashtbl.length hfi) in
      let _= if content then eprintf "%s" (Print.hashish hfi Print.vf string_of_int) in
      let _=eprintf "            Hashtable int -> dagnoeud : %d entries\n" (Hashtbl.length hin) in
      let _= if content then eprintf "%s" (Print.hashish hin string_of_int Print.dagnoeud) in ()

let solve_fi f (n : int) =
  let v = MCTSutils.SS.empty in (* start valuation *)
  let rooti = expand v f in  (*(v, f) -> 0 -> root Node *)
  try
    for i=0 to n do
      let _= if ddebug then eprintf "------------------- turn %d ----------------------------- \n\n" i in
      let _= if ddebug then eprintf "Solving %s\n" (Print.fulldagnoeud 0 (getNode rooti)) in
      match getNode rooti with
        | Proven b -> raise (Found(MCTSutils.Proven b, i))
        | _ -> let dagnode, path, num = selecti i rooti [rooti] in 
               let pnoeud = expandx dagnode path num in 
               let _= if ddebug then eprintf "Select %s ---> [%s]\n" (Print.intlist (List.rev path)) (Print.fulldag 1 dagnode) in 
               let _=if ddebug then eprintf "Expand %s ---> [%s]\n" (Print.intlist (List.rev path)) (Print.fulldag 1 pnoeud) in 
               let res= (match pnoeud with
                    | PNoeud id -> (match getNode id with
                      | Proven b -> goodupdate path ;  b
                      | Noeud(_, op, _, _) as nn -> let res = playout nn in updateNoeud nn res id ; (match op with Not -> not res | _ -> res )
                    )
                    | Proof b -> goodupdate path ; b 
                    | _ -> raise (Unexpected ("can't be formula now") )) in
               updatePath path res
    done ; (MCTSutils.Ni,n)
  with Found (x,i) -> 
    (*let _= debugHash false in *)
  x,i

let solve f n =
  let fi = MCTSutils.formToIForm f in
  let res, nc = solve_fi fi n in MCTSutils.toOption res, nc
