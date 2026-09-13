import Logic.Propositional.Formula

import Mathlib.Basic.Finite.Defs

namespace Logic.Propositional

/-- a truth assignment assign each propositional variable a truth value (true or false) -/
abbrev TruthAssignment := PropVar → Bool

/-- check if a formula is satisfied by a truth assignment -/
def eval (φ : TruthAssignment) : Formula → Bool
  | Formula.propvar p => φ p
  | Formula.neg A => !(eval φ A)
  | Formula.or A B => (eval φ A) || (eval φ B)

/-- eval φ A = true -/
def Satisfies (φ : TruthAssignment) (A : Formula) : Prop :=
  eval φ A = true

/-- a tautology is a formula that is satisfied by every truth assignment -/
def tautology (A : Formula) : Prop :=
  ∀ φ, Satisfies φ A

/-- a formula is satisfiable if there exists a truth assignment that satisfies it -/
def satisfiable (A : Formula) : Prop :=
  ∃ φ, Satisfies φ A

def unsatisfiable (A : Formula) : Prop :=
  ¬ satisfiable A

/-- ∀ A ∈ Γ, Satisfies φ A -/
def SatisfiesSet (φ : TruthAssignment) (Γ : Set Formula) : Prop :=
  ∀ A ∈ Γ, Satisfies φ A

/-- a set of formulas is satisfiable if there exists a truth assignment
    that satisfies all formulas in the set -/
def satisfiableSet (Γ : Set Formula) : Prop :=
  ∃ φ , SatisfiesSet φ Γ

def unsatisfiableSet (Γ : Set Formula) : Prop :=
  ¬ satisfiableSet Γ

/-- Γ⊧B, read "B is a tautological consequence of Γ", means that
    every truth assignment that satisfies Γ also satisfies B -/
def tautologicalConsequence (Γ : Set Formula) (B : Formula) : Prop :=
  ∀ φ, SatisfiesSet φ Γ → Satisfies φ B

/-- A set Γ is finitely satisfiable if every finite subset of Γ is satisfiable -/
def finitelySatisfiableSet (Γ : Set Formula) : Prop :=
  ∀ Δ, (Set.Finite Δ ∧ Δ ⊆ Γ) → satisfiableSet Δ

end Logic.Propositional
