(* getting the determinist or not info at the same time is a mistake, complexifies stuff a LOT *)
(* I think that's an easy mistake to do with recursive stuff, you always try to make everything at the same time *)

(*
open Printf
let _ = ignore (sprintf "")

module D = Dlpag

type operator = And | Or
type iformula = Base of bool | Var of string * bool | ListF of operator * formula list | Program of program * formula
and program = Assign of string * formula | Star of program
(* deter? * formula *)
(* could add size later.. *)
and formula = Formula of bool * iformula

module Print = struct
  let list' ll sep rr funl l = sprintf "%s%s%s" ll (String.concat sep (List.map funl l)) rr
  let list = list' "[" ";" "]"
  let operator = function
    And -> "And"
    | Or -> "Or"
  let rec formula = function Formula(_, f) -> iformula f
  and iformula = function
    | Base b -> sprintf "%B" b
    | Var (s, b) -> sprintf "%s%s" ((function true -> "+" | false -> "-") b) s
    | ListF(op, fl) -> sprintf "%s%s" (operator op) (list formula fl)
    | Program(p, f) -> sprintf "Program(%s, %s)" (program p) (formula f)
  and program = function
    | Assign(s, f) -> sprintf "%s <- %s" s (formula f)
    | Star p -> sprintf "(%s)*" (program p)
end

(*** Converting Dlpag's formula to our formula type *)
let rec dlpagf_to_formula (f:D.Formula.formula) = match f with
  | D.Formula.CallF(b, a) -> Formula(true, Var(D.Circuit.Print.callable a, b))
  | D.Formula.Base b -> Formula(true, Base b)
  | D.Formula.ListF(op, l) -> listF_to_listF op l
  | D.Formula.Modal(diam, p, f) -> let Formula(bf, ff) as fx = dlpagf_to_formula f in (* is fx even used? *)
    match p with
    | D.Formula.Test psi -> let Formula(bpsi, fpsi) as fp = dlpagf_to_formula f in
      twof_to_formula bf bpsi And ff fpsi
    | D.Formula.ListP(D.Ast.T.Seq, pl) -> seqprog_to_formula diam pl f
    | D.Formula.ListP(D.Ast.T.U, pl) -> union_to_formula diam pl f
    | D.Formula.Assign(a, psi) -> let a = D.Circuit.Print.callable a in
      Formula(false, Base true) (*Assign a <- psi*) (*TODO*)
    | D.Formula.Kleene p -> (match diam with true -> Formula(false, Program(Star(Assign("k", Formula(false, Base true))), fx)) (*TODO*)
                  | false -> Formula(false, Base true) )
    | D.Formula.Converse _ -> failwith "okay"
and op_to_op = function
  | D.Ast.T.Conj -> And
  | D.Ast.T.Disj -> Or
and listF_to_listF op l = let op = op_to_op op in
  let rec aux bacc lacc l = match l with
    | [] -> Formula(bacc, ListF(op,lacc))
    | h::t -> let Formula(b, _) as f = dlpagf_to_formula h in
      aux (b && bacc) (f::lacc) t
  in aux true [] l
and seqprog_to_formula diam pl (f:D.Formula.formula) = match pl with
  | [] -> dlpagf_to_formula f
  | h::t -> dlpagf_to_formula (D.Formula.Modal(diam, h, D.Formula.Modal(diam, D.Formula.ListP(D.Ast.T.Seq, t), f)))
and twof_to_formula b1 b2 op f1 f2 = Formula(b1 && b2, ListF(op, [Formula(b1, f1);Formula(b2, f2)]))
and union_to_formula diam pl (f:D.Formula.formula) =
  if diam then
    
  else
    Formula(

and progs_and_f_to_formulas box pl f = let rec aux lacc pl = match pl with
    [] -> lacc
    | h::t -> aux ((dlpagf_to_formula (D.Formula.Modal(box, h, f)))::lacc) t
in aux [] pl
(***    *)


let solve (f:D.Formula.formula) (verbose:bool) (n:int) = ignore f; ignore verbose; ignore n; None

*)
