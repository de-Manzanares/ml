import Logic.Propositional.Semantics

import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Basic

namespace Logic.Propositional

/-- Theorem 2.2.4:

  Γ⊧B ↔ Γ∪{¬B} is unsatisfiable

  A formula B is a tautological consequence of a set of formulas Γ
  if and only if
  Γ ∪ {¬B} is unsatisfiable.
-/
theorem theorem_2_2_4 (Γ : Set Formula) (B : Formula) :
  tautologicalConsequence Γ B ↔
  unsatisfiableSet (Γ ∪ {Formula.neg B}) := by

  constructor

  · -- Γ⊧B → Γ∪{¬B} is unsatisfiable
    -- Proof by contrapositive
    -- Γ∪{¬B} is satisfiable → Γ⊭B
    -- if Γ∪{¬B} is satisfiable then there exists a truth assignment such that φ(Γ)=T and φ(¬B)=T
    -- Hence, φ(B)=F and Γ⊭B
    contrapose
    unfold unsatisfiableSet satisfiableSet tautologicalConsequence
    push Not
    intro h
    simpa using h

  · -- Γ∪{¬B} is unsatisfiable → Γ⊧B
    -- Proof by contrapositive
    -- Γ⊭B → Γ∪{¬B} is satisfiable
    -- if Γ⊭B then there exists a truth assignment such that φ(Γ)=T and φ(B)=F
    -- Hence φ(¬B)=T and Γ∪{¬B} is satisfiable
    contrapose
    unfold tautologicalConsequence unsatisfiableSet satisfiableSet
    push Not
    intro h
    simpa using h

end Logic.Propositional
