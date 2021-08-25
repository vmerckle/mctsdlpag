open Formula

type unexploredNode = PreNodeSingle of model
                    | PreNodeAnd of model * model 
                    | PreNodeAndNode of unexploredNode * model 
                    | PreNodeNot of model
type nop = And | Or | Not
type treeNode = | Unexplored of unexploredNode
                | Middle of bool option ref * nop * int list * Statistics.t
                | Leaf of bool
                | CountedLeaf of bool
                | RunLeaf of model
                (* v psi s phi / v\models<s <- psi>phi *)
                | RunAssign of Valuation.t * Formula.formula * string * Formula.formula

