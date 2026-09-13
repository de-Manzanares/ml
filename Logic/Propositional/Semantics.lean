import Logic.Propositional.Definitions_2_2

namespace Logic.Propositional

@[simp]
lemma Satisfies.neg_iff (φ : TruthAssignment) (A : Formula) :
    Satisfies φ (Formula.neg A) ↔ ¬ Satisfies φ A := by sorry

@[simp]
lemma SatisfiesSet.singleton_iff (φ : TruthAssignment) (A : Formula) :
    SatisfiesSet φ {A} ↔ Satisfies φ A := by sorry

@[simp]
lemma SatisfiesSet.union_iff (φ : TruthAssignment) (Γ Δ : Set Formula) :
    SatisfiesSet φ (Γ ∪ Δ) ↔ SatisfiesSet φ Γ ∧ SatisfiesSet φ Δ := by sorry

end Logic.Propositional
