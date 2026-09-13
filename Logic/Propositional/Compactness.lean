import Logic.Propositional.Theorem_2_2_4

import Mathlib.Data.Set.Finite.Basic

namespace Logic.Propositional

/-- Theorem 2.2.5: Compactness Theorem for Propositional Logic, Version I

  If Γ is finitely satisfiable, then Γ is satisfiable.

  To be proven by results from Chapter 3
-/
theorem compactness_v1 (Γ : Set Formula) : finitelySatisfiableSet Γ → satisfiableSet Γ := by sorry

----------------------------------------------------------------------------------------------------

/-- Unsatisfiablility is monotone under inclusion

    If Γ0 is unsatisfiable and Γ0 ⊆ Γ1, then Γ1 is unsatisfiable.
-/
  lemma unsatisfiableSet_mono
    {Γ0 Γ1 : Set Formula}
    (hunsat : unsatisfiableSet Γ0)
    (hsub : Γ0 ⊆ Γ1) :
    -- for every truth assignment, there exists some A∈Γ0 left unsatisfied
    unsatisfiableSet Γ1 := by
    unfold unsatisfiableSet satisfiableSet at *
    push Not at *
    unfold SatisfiesSet at *
    push Not at *

    -- for some arbitrary truth assignment
    intro φ

    -- there exists some A∈Γ0 left unsatisfied
    have hunsatφ : ∃ A ∈ Γ0, ¬Satisfies φ A :=
      hunsat φ
    obtain ⟨A, AinΓ0, unsatA⟩ := hunsatφ

    -- this unsatisfied A∈Γ0 is also in Γ1, because Γ0⊆Γ1
    have AinΓ1 : A ∈ Γ1 :=
      hsub AinΓ0

    -- for every truth assignment, there exists some A∈Γ1 left unsatisfied
    exact ⟨A, AinΓ1, unsatA⟩

----------------------------------------------------------------------------------------------------

/-- Theorem 2.2.6: Compactness Theorem for Propositional Logic, Version II

  If Γ⊧B then there is a finite Δ⊆Γ such that Δ⊧B
-/
theorem compactness_v2 (Γ : Set Formula) (B : Formula):
  tautologicalConsequence Γ B
  →
  ∃ Δ, Set.Finite Δ ∧ Δ ⊆ Γ ∧ tautologicalConsequence Δ B := by

  -- assume Γ⊧B (B is a tautological consequence of Γ)
  intro tc

  -- Γ⊧B ↔ Γ∪{¬B} is unsatisfiable
  have unsat : unsatisfiableSet (Γ∪{Formula.neg B}) := (theorem_2_2_4 Γ B).mp tc

  -- there exists a finite subset of Γ∪{¬B} that is unsatisfiable
  have finunsat : ¬ finitelySatisfiableSet ( Γ ∪ {Formula.neg B}):= by
    apply mt (compactness_v1 (Γ∪{Formula.neg B})) unsat
  unfold finitelySatisfiableSet at finunsat
  push Not at finunsat
  obtain ⟨Δ0, h, nsatΔ0⟩ := finunsat
  obtain ⟨Δ0fin, Δ0sub⟩ := h

  -- define Δ
  let Δ := Γ ∩ Δ0
  use Δ

  -- Δ is finite, because it is the intersection of two sets, at least one of which is finite
  constructor
  exact Δ0fin.subset Set.inter_subset_right

  -- show that Δ⊆Γ, by definition
  constructor
  have h3 : Δ ⊆ Γ := by
    exact Set.inter_subset_left
  exact h3

  -- our goal is now to show that Δ⊧B
  -- we will proceed by showing that if Δ0⊆Δ∪{¬B} ∧ Δ0 is unsatisfiable, then Δ∪{¬B} is unsatisfiable

  -- Δ0 is a subset of Δ∪{¬B}
  have Δ0subΔunion : Δ0 ⊆ Δ ∪ {Formula.neg B}:= by
    -- take some A ∈ Δ0
    intro A AinΔ0
    -- that A is in Γ∪{¬B} because A∈Δ0 ∧ Δ0⊆Γ∪{¬B}
    have AinUnion : A ∈ Γ ∪ {Formula.neg B} := Δ0sub AinΔ0
    -- for some A ∈ Γ∪{¬B}
    cases AinUnion with
    -- either A ∈ Γ
    | inl AinΓ =>
      left
      exact ⟨AinΓ, AinΔ0⟩
    -- or A∈{¬B}
    | inr AinNegB =>
      right
      exact AinNegB

  -- Δ ∪ {¬B} is unsatisfiable
  have unsatΔunion : unsatisfiableSet (Δ ∪ {Formula.neg B}) :=
    unsatisfiableSet_mono nsatΔ0 Δ0subΔunion

  -- Δ∪{¬B} is unsatisfiable ↔ Δ⊧B
  exact (theorem_2_2_4 Δ B).mpr unsatΔunion

----------------------------------------------------------------------------------------------------

end Logic.Propositional
