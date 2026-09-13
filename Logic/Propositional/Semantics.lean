import Logic.Propositional.Definitions_2_2

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Push

namespace Logic.Propositional

----------------------------------------------------------------------------------------------------

@[simp]
lemma Satisfies.neg_iff (φ : TruthAssignment) (A : Formula) :
  Satisfies φ (Formula.neg A) ↔ ¬ Satisfies φ A := by

  constructor

  · -- forward implication
    unfold Satisfies
    push Not
    intro h
    unfold eval at h
    simpa using h

  · -- reverse implication
    unfold Satisfies
    push Not
    intro h
    unfold eval
    simpa using h

----------------------------------------------------------------------------------------------------

@[simp]
lemma SatisfiesSet.singleton_iff (φ : TruthAssignment) (A : Formula) :
  SatisfiesSet φ {A} ↔ Satisfies φ A := by

  constructor

  · -- forward implication
    unfold SatisfiesSet Satisfies
    intro h
    apply h
    rfl

  · -- reverse implication
    unfold Satisfies SatisfiesSet
    intro h B BinS
    have eq : B = A := BinS
    unfold Satisfies
    rw[eq]
    exact h

----------------------------------------------------------------------------------------------------

@[simp]
lemma SatisfiesSet.union_iff (φ : TruthAssignment) (Γ Δ : Set Formula) :
  SatisfiesSet φ (Γ ∪ Δ) ↔ SatisfiesSet φ Γ ∧ SatisfiesSet φ Δ := by

  constructor

  · -- forward implication
    unfold SatisfiesSet Satisfies
    intro h
    constructor
    · --
      intro A hA
      apply h
      left
      exact hA
    · --
      intro A hA
      apply h
      right
      exact hA

  · -- reverse implication
    unfold SatisfiesSet Satisfies
    intro h A hA
    cases hA with
    | inl hΓ => exact h.1 A hΓ
    | inr hΔ => exact h.2 A hΔ

----------------------------------------------------------------------------------------------------

end Logic.Propositional
