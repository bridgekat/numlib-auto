import Numlib.Optimization.FischerBurmeister
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Complementarity problems -/

open scoped BigOperators

namespace ConnGouldToint.Chapter16

/-- The generalized complementarity conditions (16.3.1) on the two vectors. -/
def IsComplementary {ι : Type*} [Fintype ι] (a b : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧ ∑ i, a i * b i = 0

/-- The scalar complementarity residual (16.3.2). -/
noncomputable abbrev fischerBurmeister := Numlib.Optimization.fischerBurmeister

/-- The residual `Φ` in the system (16.3.3), evaluated on the two vectors. -/
noncomputable def complementarityResidual {ι : Type*} (a b : ι → ℝ) (i : ι) : ℝ :=
  fischerBurmeister (a i) (b i)

/-- The residual system (16.3.3) is equivalent to the complementarity conditions (16.3.1). -/
theorem complementarityResidual_eq_zero_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    complementarityResidual a b = 0 ↔ IsComplementary a b := by
  constructor
  · intro h
    have hc (i : ι) : 0 ≤ a i ∧ 0 ≤ b i ∧ a i * b i = 0 :=
      Numlib.Optimization.fischerBurmeister_eq_zero_iff.mp (congrFun h i)
    exact ⟨fun i ↦ (hc i).1, fun i ↦ (hc i).2.1,
      Finset.sum_eq_zero fun i _ ↦ (hc i).2.2⟩
  · rintro ⟨ha, hb, hsum⟩
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_nonneg (ha i) (hb i))).mp hsum
    funext i
    exact Numlib.Optimization.fischerBurmeister_eq_zero_iff.mpr
      ⟨ha i, hb i, hprod i (Finset.mem_univ i)⟩

/-- The least-squares complementarity merit (16.3.7) on the two vectors. -/
noncomputable def complementarityMerit {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  (∑ i, complementarityResidual a b i ^ 2) / 2

end ConnGouldToint.Chapter16
