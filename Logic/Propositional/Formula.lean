import Logic.Propositional.Language

namespace Logic.Propositional

inductive Formula where
  | propvar : PropVar → Formula
  | neg : Formula → Formula
  | or : Formula → Formula → Formula
deriving Repr, DecidableEq

inductive IsFormula : Expression → Prop where
  | is_propvar : ∀ (p : PropVar),
      IsFormula [Symbol.propvar p]

  | is_neg : ∀ (A : Expression),
      IsFormula A → IsFormula ([Symbol.connective Connective.neg] ++ A)

  | is_or : ∀ (A B : Expression),
      IsFormula A → IsFormula B →
      IsFormula ( [Symbol.lparen] ++
                  A ++
                  [Symbol.connective Connective.or] ++
                  B ++
                  [Symbol.rparen]
                )

example : IsFormula [Symbol.propvar 0] := IsFormula.is_propvar 0

end Logic.Propositional
