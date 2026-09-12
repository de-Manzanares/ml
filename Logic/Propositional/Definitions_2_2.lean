import Logic.Propositional.Formula

import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Use

namespace Logic.Propositional

/-- a truth assignment assign each propositional variable a truth value (true or false) -/
abbrev TruthAssignment := PropVar → Bool

/-- check if a formula is satisfied by a truth assignment -/
def satisfies (φ : TruthAssignment) : Formula → Bool
  | Formula.propvar p => φ p
  | Formula.neg A => !(satisfies φ A)
  | Formula.or A B => (satisfies φ A) || (satisfies φ B)

/-- a tautology is a formula that is satisfied by every truth assignment -/
def tautology (A : Formula) : Prop :=
  ∀ (φ : TruthAssignment), satisfies φ A = true

/-- a formula is satisfiable if there exists a truth assignment that satisfies it -/
def satisfiable (A : Formula) : Prop :=
  ∃ (φ : TruthAssignment), satisfies φ A = true

def unsatisfiable (A : Formula) : Prop :=
  ¬ satisfiable A

/-- finite or infinite set of formulas -/
abbrev FormulaSet := Formula → Prop

/-- a set of formulas is satisfiable if there exists a truth assignment that satisfies all formulas in the set -/
def satisfiableSet (Γ : FormulaSet) : Prop :=
  ∃ (φ : TruthAssignment), ∀ (A : Formula), Γ A → satisfies φ A = true

def unsatisfiableSet (Γ : FormulaSet) : Prop :=
  ¬ satisfiableSet Γ

/-- Γ⊧B, read "B is a tautological consequence of Γ", means that every truth assignment that satisfies Γ also satisfies B -/
def tautologicalConsequence (Γ : FormulaSet) (B : Formula) : Prop :=
  ∀ (φ : TruthAssignment),
    (∀ (A : Formula), Γ A → satisfies φ A = true) → satisfies φ B = true

/-- union of two sets of formulas -/
def setUnion (Γ Δ : FormulaSet) : FormulaSet :=
  fun A => Γ A ∨ Δ A

/-- singleton set containing a single formula -/
def singletonSet (B : Formula) : FormulaSet :=
  fun A => A = B

end Logic.Propositional
