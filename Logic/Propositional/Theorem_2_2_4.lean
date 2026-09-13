import Logic.Propositional.Definitions_2_2

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
  tautologicalConsequence Γ B
  ↔
  unsatisfiableSet (Γ ∪ {Formula.neg B}) := by

  -- break ↔ into two implications
  constructor

  --------------------------------------------------------------------------------

  -- forward implication
  -- Γ⊧B → Γ∪{¬B} is unsatisfiable
  -- proof by contrapositive
  -- Γ∪{¬B} is satisfiable → Γ⊭B
  contrapose

  -- assume Γ∪{¬B} is satisfiable
  intro sat
  unfold unsatisfiableSet at sat
  push Not at sat

  -- if Γ∪{¬B} is satisfiable then there exists a truth assignment φ that satisfies Γ∪{¬B}
  unfold satisfiableSet at sat
  obtain ⟨φ, hUSat⟩ := sat

  -- the goal is now to show that there exists a truth assignment φ that satisfies Γ but does not satisfy B
  unfold tautologicalConsequence
  push Not

  -- claim: φ satisfies Γ but does not satisfy B
  use φ

  -- break down the goal into two parts: φ satisfies Γ and φ does not satisfy B
  constructor

  -- assume A ∈ Γ, we need to show that φ satisfies A
  intro A hA
  exact hUSat A (Or.inl hA)

  -- assume A ∈ {¬B}, we need to show that φ does not satisfy B
  simpa [Satisfies, eval] using hUSat (Formula.neg B) (Or.inr rfl)

  --------------------------------------------------------------------------------

  -- reverse implication
  -- Γ∪{¬B} is unsatisfiable → Γ⊧B
  -- proof by contrapositive
  -- Γ⊭B → Γ∪{¬B} is satisfiable
  contrapose

  -- assume Γ⊭B (B is not a tautological consequence of Γ)
  intro ntc
  unfold tautologicalConsequence at ntc

  -- if ntc, then there exists a truth assignment φ
  -- such that φ satisfies Γ but does not satisfy B
  push Not at ntc
  obtain ⟨φ, hφΓ, hφB⟩ := ntc

  -- the goal is to show that there exists a truth assignment that satisfies Γ∪{¬B}
  unfold unsatisfiableSet
  push Not
  unfold satisfiableSet

  -- claim: φ satisfies Γ∪{¬B}
  use φ

  -- assume A ∈ Γ∪{¬B}, we need to show that φ satisfies A
  intro A hA

  cases hA with
  -- if A ∈ Γ, then φ satisfies A by hφΓ
  | inl hAΓ =>
    exact hφΓ A hAΓ

  -- if A∈{¬B} then A = ¬B, and φ satisfies ¬B by hφB
  | inr hAnegB =>
    cases hAnegB
    simpa [Satisfies, eval] using hφB
  -------------------------------------------------------------------------------∎

end Logic.Propositional
