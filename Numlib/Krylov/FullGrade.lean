import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import Numlib.LinearAlgebra.CyclicDecomposition

/-!
# Full-grade vectors and attainable minimal polynomials

Full-grade vectors for a finite-dimensional complex endomorphism form a dense set.
Every monic divisor of the operator minimal polynomial occurs as a vector minimal polynomial.

## Main results

* `Krylov.dense_fullGrade`: full-grade vectors are dense.
* `Krylov.exists_minpolyVec_eq_of_monic_dvd`: monic divisors are attained by vector minimal
  polynomials.
-/

open Polynomial

namespace Krylov

section Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A vector has the full minimal polynomial if and only if every cofactor obtained by
removing one linear factor acts nontrivially on that vector. -/
theorem minpolyVec_eq_minpoly_iff_cofactors (A : Module.End ℂ E) (v : E) :
    minpolyVec A v = minpoly ℂ A ↔
      ∀ z : ℂ, (minpoly ℂ A).IsRoot z → aeval A (minpoly ℂ A /ₘ (X - C z)) v ≠ 0 := by
  let m := minpoly ℂ A
  have hm := minpoly.monic (IsIntegral.of_finite ℂ A)
  change minpolyVec A v = m ↔ _
  constructor
  · intro h z hz hzero
    have hdvd := (minpolyVec_dvd_iff A v).2 hzero
    rw [h] at hdvd
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.2 hz)
    change m = (X - C z) * r at hr
    have hm0 : m ≠ 0 := hm.ne_zero
    have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr ▸ hm0)
    have hdiv : m /ₘ (X - C z) = r := by
      rw [hr, mul_divByMonic_cancel_left _ (monic_X_sub_C z)]
    rw [hdiv] at hdvd
    have hle := natDegree_le_of_dvd hdvd hr0
    have he : m.natDegree = 1 + r.natDegree := by
      rw [hr, natDegree_mul (X_sub_C_ne_zero z) hr0, natDegree_X_sub_C]
    omega
  · intro h
    by_contra hne
    obtain ⟨q, hq⟩ := (minpolyVec_dvd_iff A v).2 (show aeval A m v = 0 from by
      rw [minpoly.aeval, LinearMap.zero_apply])
    have hv := minpolyVec_monic A v (minpolyVec_ne_zero A v)
    have hqmon : q.Monic := hv.of_mul_monic_left (hq ▸ hm)
    have hq1 : q ≠ 1 := by
      intro hq1
      apply hne
      rw [hq, hq1, mul_one]
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q (hqmon.degree_pos.mpr hq1).ne'
    obtain ⟨r, hr⟩ := (dvd_iff_isRoot.2 hz)
    have hmz : m.IsRoot z := by
      rw [hq, IsRoot, eval_mul, hz.eq_zero, mul_zero]
    have hdiv : m /ₘ (X - C z) = minpolyVec A v * r := by
      rw [hq, hr, mul_left_comm, mul_divByMonic_cancel_left _ (monic_X_sub_C z)]
    exact h z hmz ((minpolyVec_dvd_iff A v).1 (hdiv ▸ dvd_mul_right _ _))

/-- For a finite-dimensional complex endomorphism, the vectors of full grade form a dense set. -/
theorem dense_fullGrade (A : Module.End ℂ E) :
    Dense {v : E | grade A v = (minpoly ℂ A).natDegree} := by
  intro v
  obtain ⟨w, hw⟩ := A.exists_minpolyVec_eq_minpoly
  let m := minpoly ℂ A
  let f (t : ℂ) := v + t • w
  let bad (z : ℂ) := {t : ℂ | aeval A (m /ₘ (X - C z)) (f t) = 0}
  have hbad z (hz : m.IsRoot z) : (bad z).Finite := by
    apply Set.Subsingleton.finite
    intro t ht s hs
    have hcoeff := (minpolyVec_eq_minpoly_iff_cofactors A w).1 hw z hz
    change aeval A (m /ₘ (X - C z)) (v + t • w) = 0 at ht
    change aeval A (m /ₘ (X - C z)) (v + s • w) = 0 at hs
    rw [map_add, map_smul] at ht hs
    exact smul_left_injective ℂ hcoeff (add_left_cancel (ht.trans hs.symm))
  let S := ⋃ z ∈ {z : ℂ | m.IsRoot z}, bad z
  have hS : S.Finite := (finite_setOfPred_isRoot (minpoly.ne_zero_of_finite ℂ A)).biUnion hbad
  have hcont : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hclosure := mem_closure_image hcont.continuousAt (hS.countable.dense_compl ℂ 0)
  apply closure_mono (s := f '' Sᶜ) _ (show v ∈ closure (f '' Sᶜ) from by simpa [f] using hclosure)
  rintro y ⟨t, ht, rfl⟩
  have hfull : minpolyVec A (f t) = m := (minpolyVec_eq_minpoly_iff_cofactors A (f t)).2
    fun z hz hzero => ht (Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hz, hzero⟩⟩)
  exact (natDegree_minpolyVec A (f t)).symm.trans (congrArg natDegree hfull)

end Density

section Divisor

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Every monic divisor of the operator minimal polynomial is the minimal polynomial of
some starting vector. -/
theorem exists_minpolyVec_eq_of_monic_dvd [Infinite K] (A : Module.End K E) {q : K[X]}
    (hq : q.Monic) (hd : q ∣ minpoly K A) : ∃ v, minpolyVec A v = q := by
  obtain ⟨w, hw⟩ := A.exists_minpolyVec_eq_minpoly
  obtain ⟨r, hr⟩ := hd
  have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr ▸ minpoly.ne_zero_of_finite K A)
  let v := aeval A r w
  have hv (p : K[X]) : minpolyVec A v ∣ p ↔ q ∣ p := by
    rw [minpolyVec_dvd_iff]
    change aeval A p (aeval A r w) = 0 ↔ _
    rw [← Module.End.mul_apply, ← map_mul, ← minpolyVec_dvd_iff, hw, hr]
    exact mul_dvd_mul_iff_right hr0
  have hfv := minpolyVec_monic A v (minpolyVec_ne_zero A v)
  exact ⟨v, eq_of_monic_of_associated hfv hq
    (associated_of_dvd_dvd ((hv q).2 dvd_rfl) ((hv _).1 dvd_rfl))⟩

end Divisor
end Krylov
