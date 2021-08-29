open Printf

module D = Dlpag

module CSet = Set.Make (struct type t = D.Circuit.T.callable let compare = compare end)
module SS = Set.Make (struct type t = string let compare = compare end)

exception Not_implem of string

type iformula = CallF of bool * string | Base of bool | ListF of (D.Ast.T.foperator * iformula list) | Modal of (bool * iprogram * iformula) (*| Not of iformula*)

and iprogram  = Assign of (string * iformula) | Test of iformula | ListP of (D.Ast.T.poperator * iprogram list) | LE of (int * iprogram)


(*** Usual matching ***)
(*
  | Formu(v, f) -> (match f with
    | CallF (b, s) -> 
    | Base b ->  
    | ListF(Ast.T.Conj, l) -> 
    | ListF(Ast.T.Disj, l) -> 
    | Modal(b, p, f) -> (match p with
      | Assign(s, fa) -> let vs = SS.add s v and vns = SS.remove s v in 
      | Test fp -> 
      | ListP(Ast.T.Seq, l) -> (match l with 
        | [] -> 
        | [h] -> 
        | h::t -> 
      )
      | ListP(Ast.T.U, l) -> 
      | LE(n, p) -> ( match n with
        |0 -> 
        |1 -> 
        |n ->
      )
    )
  )
*)

type stats = { n : int;
      nwin : int;
      ntoprove : int;
}

type oparbre = And | Or | Not
type feuilletype = Formu of SS.t * iformula | Direct of bool
type state = Proven of bool | Ni
type arbre = Noeud of (state * arbre list * oparbre * stats) | Feuille of feuilletype


module Print =
struct

let list' ld id rd pr l = sprintf "%s%s%s" ld (String.concat id (List.map pr l)) rd
let list pr = list' "[" "; " "]" pr

  let rec iformula = function
    | CallF(b, s) -> sprintf "%s%s" (if b then "" else "-") s
    | Base true -> sprintf "T"
    | Base false -> sprintf "-T"
    | ListF(D.Ast.T.Conj, l) -> sprintf  "(%s)" (D.Print.list' "" "^" "" iformula l) 
    | ListF(D.Ast.T.Disj, l) -> sprintf  "(%s)" (D.Print.list' "" " v " "" iformula l) 
    | Modal(true, p, f) -> sprintf "<%s>%s" (program p) (iformula f)
    | Modal(false, p, f) -> sprintf "[%s]%s" (program p) (iformula f)
  and program = function
    | Assign(s, f) -> (match f with
      | Base true -> sprintf "+%s" s
      | Base false -> sprintf "-%s" s
      | _ -> sprintf "%s <- %s" s (iformula f) )
    | Test f -> sprintf "(%s)?" (iformula f)
    | ListP(D.Ast.T.Seq, l) -> sprintf "%s" (D.Print.list' "" "; " "" program l)
    | ListP(D.Ast.T.U, l) -> sprintf "%s" (D.Print.list' "" " U " "" program l)
    | LE(n, p) -> sprintf "(%s)^<=%d" (program p) n

  let set' ld id rd l = match l with
    | l when SS.cardinal l = 0-> ""
    | l -> sprintf "%s%s%s " ld (String.concat id (SS.elements l)) rd
  let rec arbre = function
    (*| Noeud(_, l, op, _) -> sprintf "%s(%s)"  ((function And -> "And" | Or -> "Or " | Not -> "Not") op)  (Print.list' "" ", " "" arbre l)*)
    | Noeud(st, l, op, _) -> sprintf "%s%s(%s)"  ((function And -> "And" | Or -> "Or" | Not -> "Not") op)  ((function Ni -> "" | Proven true -> "(T)" | Proven false -> "(F)")st) (D.Print.list' "" ", " "" arbre l)
    | Feuille(Formu(v, f)) -> sprintf "%s|=%s" (set' "{" "," "}" v) (iformula f)
   | Feuille(Direct(b)) -> ((function true -> "T" | false -> "F") b)

  let rec arbreK = function
    (*| Noeud(_, l, op, _) -> sprintf "%s(%s)"  ((function And -> "And" | Or -> "Or " | Not -> "Not") op)  (Print.list' "" ", " "" arbre l)*)
    | Noeud(st, l, op, se) -> sprintf "[%d]%s%s(%s)"  se.n ((function And -> "And" | Or -> "Or" | Not -> "Not") op)  ((function Ni -> "" | Proven true -> "(T)" | Proven false -> "(F)")st) (D.Print.list' "" ", " "" arbreK l)
    | Feuille(Formu(v, f)) -> sprintf "%s|=%s" (set' "{" "," "}" v) (iformula f)
   | Feuille(Direct(b)) -> ((function true -> "T" | false -> "F") b)

   let arbreq = function
    (*| Noeud(_, l, op, _) -> sprintf "%s(%s)"  ((function And -> "And" | Or -> "Or " | Not -> "Not") op)  (Print.list' "" ", " "" arbre l)*)
    | Noeud(st, l, op, _) -> sprintf "%s%s(%d)"  ((function And -> "And" | Or -> "Or" | Not -> "Not") op)  ((function Ni -> "" | Proven true -> "(T)" | Proven false -> "(F)")st) (List.length l)
    | Feuille(Formu(v, _)) -> sprintf "%s|=" (set' "{" "," "}" v) 
    | Feuille(Direct(b)) -> ((function true -> "T" | false -> "F") b)
end

let rec countP p = match p with
  | D.Formula.Assign(a, psi) -> CSet.add a (countF psi)
  | D.Formula.ListP(_, l) -> List.fold_right CSet.union (List.map countP l) CSet.empty
  | D.Formula.Test psi -> countF psi
  | D.Formula.Kleene p -> countP p
  | D.Formula.Converse _ -> raise (Not_implem "Converse")
and countF f = match f with
  | D.Formula.CallF(_, a) ->CSet.singleton a
  | D.Formula.Base _ -> CSet.empty
  | D.Formula.ListF(_, l) -> List.fold_right CSet.union(List.map countF l) CSet.empty
  | D.Formula.Modal(_, p, f) -> CSet.union (countP p) (countF f)

let acountF f = CSet.cardinal (countF f)
let acountP p = CSet.cardinal (countP p)

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

(* avoid overflow *)
let twopow n = match n with
n  when n <= 32 -> pow 2 n
  | _ -> max_int


let rec formToIForm (f:D.Formula.formula) : iformula = match f with
  | D.Formula.CallF(b, a) -> let _= if false then eprintf "---> %s %b\n" (D.Circuit.Print.callable a) b in 
      let s = D.Circuit.Print.callable a in CallF(b, s)
  | D.Formula.Base b -> Base b
  | D.Formula.ListF(op, l) -> ListF(op, List.map formToIForm l)
  | D.Formula.Modal(b, p, f) -> let fi = formToIForm f in
    match p with
    | D.Formula.ListP(D.Ast.T.Seq, xt) ->  (* this isn't working properly obviously TODO *)
        ( match xt with
        | [] -> formToIForm f (* skip.. = <;> *)
        | [h] -> Modal(b, progToIProg h, fi)
        | h::t -> Modal(b, progToIProg h, formToIForm (D.Formula.Modal(b, ListP(D.Ast.T.Seq, t), f)))
      )
    | _ -> Modal(b, progToIProg p, fi)

and progToIProg (p:D.Formula.program) : iprogram = match p with
  | D.Formula.Assign(a, psi) -> Assign(D.Circuit.Print.callable a, formToIForm psi)
  | D.Formula.ListP(op, l) -> ListP(op, List.map progToIProg l) (*should convert Seq close to above, but not really necessary as we won't use this function directly *)
  | D.Formula.Test psi -> Test (formToIForm psi)
  | D.Formula.Kleene p -> LE(twopow (acountP p) , progToIProg p)
  | D.Formula.Converse _ -> raise (Not_implem "Converse")

let statInit l = {n=0; nwin=0; ntoprove=l}
let toFormu (v:SS.t) (f:iformula) : arbre = Feuille(Formu(v, f))
let ptoFormu v f b p = Feuille(Formu(v, Modal(b, p, f)))
let bDiff = function true -> Or | false -> And (* simple diff between box and diamonds *)

(* valuation,formula -> tree *)
let splitIF (v:SS.t) (f:iformula) : arbre = match f with
  | CallF (b, s) -> Feuille (Direct (let x =(SS.mem s v) in if b then x else not x))
  | Base b ->  Feuille (Direct b)
  | ListF(D.Ast.T.Conj, l) -> Noeud(Ni, List.map (toFormu v) l, And, statInit (List.length l))
  | ListF(D.Ast.T.Disj, l) -> Noeud(Ni, List.map (toFormu v) l, Or, statInit (List.length l))
  | Modal(b, p, f) -> match p with
    | Assign(s, fa) -> let vs = SS.add s v and vns = SS.remove s v in
        Noeud(Ni, [Noeud(Ni, [Feuille(Formu(v, fa)); Feuille(Formu(vs, f))], And, statInit 2);
               Noeud(Ni, [Noeud(Ni, [Feuille(Formu(v, fa))], Not, statInit 1); Feuille(Formu(vns, f))], And, statInit 2) ] , Or, statInit 2)
    | Test fp -> Noeud(Ni, [Feuille(Formu(v, fp)); Feuille(Formu(v, f))], And, statInit 2)
    | ListP(D.Ast.T.Seq, l) -> (match l with 
        | [] -> toFormu v f (* <;>f -> f *)
        | [h] -> Feuille(Formu(v, Modal(b, h, f))) (* <p;> -> <p> *)
        | h::t -> Feuille(Formu(v, Modal(b, h, Modal(b, ListP(D.Ast.T.Seq, t), f))))(*<p;q>-> <p><q>*)
    )
    | ListP(D.Ast.T.U, l) -> Noeud(Ni, List.map (ptoFormu v f b) l, bDiff b,statInit (List.length l))
    | LE(n, p) -> match n with
        |0 -> toFormu v f (* <p^<=0>f -> f *)
        |1 -> Noeud(Ni, [toFormu v (Modal(b, p, f));toFormu v f], bDiff b, statInit 2) (*opti*)
        |n -> Noeud(Ni, [toFormu v (Modal(b, p, Modal(b, LE(n-1, p), f)));toFormu v f], bDiff b, statInit 2)

let kek n st = let rec aux n s = match n with
0 -> s
        | n -> aux (n-1) (s^st)
in aux n ""

(* depth first naive solver *)
let rec playthrough t b n = 
  let _= if b then eprintf "%s%s {\n" (kek n "---- ") (Print.arbre t) in 
  let x =
  match t with
  | Feuille(Direct b) -> b
  | Feuille(Formu(v, f)) -> let x = playthrough (splitIF v f) b (n+1) in x
  | Noeud(_, l, op, s) ->  match l with 
    | [] -> false
    | [h] -> let x = playthrough h b (n+1) (* necessary & opti *) in (match op with Not -> not x | _-> x)
    | h::t ->  match op with
        | And -> playthrough h b (n+1)  && playthrough (Noeud(Ni, t, op, s)) b (n+1)
        | Or -> playthrough h b (n+1) || playthrough (Noeud(Ni, t, op, s)) b (n+1)
        | Not -> not (playthrough h b (n+1))
   in
  let _= if b then eprintf "%s} %b \n" (kek n "     ") x  in x

let quicksolve t = let b = playthrough t false 0 in
  Base b

let propositional f = match f with
  | CallF _ | Base _ | ListF _ -> true
  | _ -> false
(* count nodes slow version*)
let rec playthroughc t = 
  match t with
  | Feuille(Direct b) -> b,1
  | Feuille(Formu(v, f)) -> let x,y = playthroughc (splitIF v f) in x,y+1
  | Noeud(_, l, op, s) ->  match l with 
    | [] -> false,0
    | [h] -> let x,y = playthroughc h (* necessary & opti *) in (match op with Not -> not x | _-> x), y+1
    | h::t ->  match op with
        | And -> let bx, nx = playthroughc h in if not bx then bx, nx+1 else let by, ny = playthroughc (Noeud(Ni, t, op, s)) in bx && by , nx+ny+1
        | Or -> let bx, nx = playthroughc h in if bx then bx, nx+1 else let by, ny = playthroughc (Noeud(Ni, t, op, s)) in bx || by , nx+ny+1
        | Not -> not (fst(playthroughc h) ),0



(* count ... something ?nodes terminal version*)
let rec playthroughcount t c = 
  match t with
  | Feuille(Direct _) -> c+1
  | Feuille(Formu(v, f)) -> playthroughcount (splitIF v f) (1+c)
  | Noeud(_, l, op, s) ->  match l with 
    | [] -> c
    | [h] -> playthroughcount h (c+1)
    | h::t ->  match op with
        | And|Or -> playthroughcount h (playthroughcount (Noeud(Ni, t, op, s)) (c+1))
        | Not -> playthroughcount h (c+1)

let solve f verbose n =
  let fi = formToIForm f in
  let tree = splitIF (SS.empty) fi in
  playthrough tree verbose n

let toOption = function
  | Proven b -> Some b
  | Ni -> None
