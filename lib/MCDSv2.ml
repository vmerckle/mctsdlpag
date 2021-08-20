open Printf

module D = Dlpag

let rec to_node (f:Formula.formula) = match f with
  | Base b -> Node
