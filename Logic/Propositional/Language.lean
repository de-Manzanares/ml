namespace Logic.Propositional

abbrev PropVar := Nat

inductive Connective where
  | neg : Connective
  | or : Connective
deriving Repr, DecidableEq

inductive Symbol where
  | propvar : PropVar → Symbol
  | lparen : Symbol
  | rparen : Symbol
  | connective : Connective → Symbol
deriving Repr, DecidableEq

abbrev Expression := List Symbol -- a finite sequence of symbols

end Logic.Propositional
