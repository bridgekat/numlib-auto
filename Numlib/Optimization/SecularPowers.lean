import Numlib.Optimization.SecularResolvent
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Powers of squared resolvents

A spectral Cauchy–Schwarz estimate controls the second derivative of a power of the
squared resolvent. The inverse square-root endpoint is concave but may be affine.
-/

open scoped BigOperators Topology
open Set Filter

namespace Optimization.SecularResolvent

section Scalar
variable {ι : Type*} [Fintype ι] (e γ : ι → ℝ)

/-- The spectral Cauchy–Schwarz inequality underlying the inverse square-root transform. -/
theorem spectralNormSq_mul_secondDeriv {t : ℝ} (ht : ∀ i, t + e i ≠ 0) :
    3 / 2 * (deriv (spectralNormSq e γ) t) ^ 2 ≤
      spectralNormSq e γ t * deriv (deriv (spectralNormSq e γ)) t := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => γ i / (t + e i)) (fun i => γ i / (t + e i) ^ 2)
  have h1 := iteratedDeriv_spectralNormSq e γ 1 ht
  have h2 := iteratedDeriv_spectralNormSq e γ 2 ht
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, pow_one, Nat.factorial, Nat.cast_mul,
    Nat.cast_one, mul_one] at h1 h2
  have heq1 : (∑ i, γ i / (t + e i) * (γ i / (t + e i) ^ 2)) =
      ∑ i, γ i ^ 2 / (t + e i) ^ 3 := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have heq2 : (∑ i, (γ i / (t + e i)) ^ 2) = spectralNormSq e γ t := by
    simp only [spectralNormSq, div_pow]
  have heq3 : (∑ i, (γ i / (t + e i) ^ 2) ^ 2) =
      ∑ i, γ i ^ 2 / (t + e i) ^ 4 := by simp only [div_pow, ← pow_mul]
  rw [heq1, heq2, heq3] at hcs
  rw [h1, h2]
  nlinarith

/-- Exact second derivative of a real power, at a positive spectral norm. -/
theorem deriv2_rpow_spectralNormSq (β : ℝ) {t : ℝ}
    (ht : ∀ i, t + e i ≠ 0) (hγ : ∃ i, γ i ≠ 0) :
    deriv (deriv (fun x => spectralNormSq e γ x ^ β)) t =
      β * spectralNormSq e γ t ^ (β - 2) *
        ((β - 1) * (deriv (spectralNormSq e γ) t) ^ 2 +
          spectralNormSq e γ t * deriv (deriv (spectralNormSq e γ)) t) := by
  let f := spectralNormSq e γ
  have hp : 0 < f t := spectralNormSq_pos e γ ht hγ
  have hc : ContDiffAt ℝ 3 f t := contDiffAt_spectralNormSq e γ ht 3
  have hd : HasDerivAt f (deriv f t) t := hc.differentiableAt (by simp) |>.hasDerivAt
  have hdd : HasDerivAt (deriv f) (deriv (deriv f) t) t :=
    (hc.derivWithin (m := 1) (by norm_num)).differentiableAt (by simp) |>.hasDerivAt
  have he : deriv (fun x => f x ^ β) =ᶠ[𝓝 t]
      (fun x => β * f x ^ (β - 1) * deriv f x) := by
    have hp' : ∀ᶠ x in 𝓝 t, 0 < f x := hc.continuousAt.eventually (lt_mem_nhds hp)
    have hc' : ∀ᶠ x in 𝓝 t, DifferentiableAt ℝ f x :=
      by
      filter_upwards [eventually_all.mpr (fun i =>
        (continuousAt_id.add continuousAt_const).eventually_ne (ht i))] with x hx
      exact (contDiffAt_spectralNormSq e γ hx 1).differentiableAt (by norm_num)
    filter_upwards [hp', hc'] with x hx hx'
    rw [(hx'.hasDerivAt.rpow_const (p := β) (Or.inl hx.ne')).deriv]
    ring
  rw [he.deriv_eq]
  have hd2 := ((hd.rpow_const (p := β - 1) (Or.inl hp.ne')).const_mul β |>.mul hdd).deriv
  change deriv ((fun y => β * f y ^ (β - 1)) * deriv f) t = _
  rw [hd2, show β - 1 - 1 = β - 2 by ring]
  have hpow : f t ^ (β - 1) = f t ^ (β - 2) * f t := by
    rw [show β - 1 = (β - 2) + 1 by ring, Real.rpow_add hp, Real.rpow_one]
  change _ = β * f t ^ (β - 2) * _
  rw [hpow]
  ring

end Scalar
section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- The spectral curvature inequality for the actual squared resolvent. -/
theorem normSqResolvent_mul_secondDeriv (g : E) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    3 / 2 * (deriv (normSqResolvent H g) t) ^ 2 ≤
      normSqResolvent H g t * deriv (deriv (normSqResolvent H g)) t := by
  have he := eventuallyEq_normSqResolvent hH g ht
  rw [he.eq_of_nhds, he.deriv_eq, he.deriv.deriv_eq]
  exact spectralNormSq_mul_secondDeriv _ _ ht

/-- Second derivative of a power of the actual squared resolvent. -/
theorem deriv2_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (β : ℝ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    deriv (deriv (fun x => normSqResolvent H g x ^ β)) t =
      β * normSqResolvent H g t ^ (β - 2) *
        ((β - 1) * (deriv (normSqResolvent H g) t) ^ 2 +
          normSqResolvent H g t * deriv (deriv (normSqResolvent H g)) t) := by
  have he := eventuallyEq_normSqResolvent hH g ht
  have hep : (fun x => normSqResolvent H g x ^ β) =ᶠ[𝓝 t]
      (fun x => spectralNormSq (hH.eigenvalues rfl)
        (fun i => (hH.eigenvectorBasis rfl).repr g i) x ^ β) :=
    he.fun_comp (fun y : ℝ => y ^ β)
  rw [hep.deriv.deriv_eq, he.eq_of_nhds, he.deriv_eq, he.deriv.deriv_eq]
  exact deriv2_rpow_spectralNormSq _ _ β ht (exists_repr_ne_zero hH hg)

/-- Powers are smooth wherever the squared resolvent is positive and nonsingular. -/
theorem contDiffAt_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (β : ℝ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fun x => normSqResolvent H g x ^ β) t :=
  (contDiffAt_normSqResolvent hH g ht k).rpow_const_of_ne
    (normSqResolvent_pos hH hg ht).ne'

/-- The first derivative is strictly negative on the positive shifted spectrum. -/
theorem deriv_normSqResolvent_neg {g : E} (hg : g ≠ 0) {t : ℝ}
    (ht : Admissible hH t) : deriv (normSqResolvent H g) t < 0 := by
  have hs := sign_iteratedDeriv_normSqResolvent hH hg 1 ht
  simpa using hs

/-- First derivative of a power of the actual squared resolvent. -/
theorem deriv_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (β : ℝ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    deriv (fun x => normSqResolvent H g x ^ β) t =
      deriv (normSqResolvent H g) t * β * normSqResolvent H g t ^ (β - 1) := by
  exact ((contDiffAt_normSqResolvent hH g ht 1).differentiableAt (by norm_num)
    |>.hasDerivAt.rpow_const (Or.inl (normSqResolvent_pos hH hg ht).ne')).deriv

/-- Positive powers have positive second derivative. -/
theorem deriv2_rpow_normSqResolvent_pos {g : E} (hg : g ≠ 0) {β t : ℝ}
    (hβ : 0 < β) (ht : Admissible hH t) :
    0 < deriv (deriv (fun x => normSqResolvent H g x ^ β)) t := by
  have ht' := fun i => ne_of_gt (ht i)
  rw [deriv2_rpow_normSqResolvent hH hg β ht']
  have hcs := normSqResolvent_mul_secondDeriv hH g ht'
  have hd := deriv_normSqResolvent_neg hH hg ht
  have hsq : 0 < (deriv (normSqResolvent H g) t) ^ 2 := sq_pos_of_ne_zero hd.ne
  have hbr : 0 < (β - 1) * (deriv (normSqResolvent H g) t) ^ 2 +
      normSqResolvent H g t * deriv (deriv (normSqResolvent H g)) t := by nlinarith
  exact mul_pos (mul_pos hβ (Real.rpow_pos_of_pos (normSqResolvent_pos hH hg ht') _)) hbr

/-- Negative powers down to the inverse square-root endpoint have nonpositive curvature. -/
theorem deriv2_rpow_normSqResolvent_nonpos {g : E} (hg : g ≠ 0) {β t : ℝ}
    (hβ : -(1 / 2 : ℝ) ≤ β) (hβ' : β < 0) (ht : Admissible hH t) :
    deriv (deriv (fun x => normSqResolvent H g x ^ β)) t ≤ 0 := by
  have ht' := fun i => ne_of_gt (ht i)
  rw [deriv2_rpow_normSqResolvent hH hg β ht']
  have hcs := normSqResolvent_mul_secondDeriv hH g ht'
  have hbr : 0 ≤ (β - 1) * (deriv (normSqResolvent H g) t) ^ 2 +
      normSqResolvent H g t * deriv (deriv (normSqResolvent H g)) t := by
    nlinarith [sq_nonneg (deriv (normSqResolvent H g) t)]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hβ'.le
      (Real.rpow_nonneg (normSqResolvent_pos hH hg ht').le _)) hbr

/-- Above the inverse square-root endpoint negative powers have strictly negative curvature. -/
theorem deriv2_rpow_normSqResolvent_neg {g : E} (hg : g ≠ 0) {β t : ℝ}
    (hβ : -(1 / 2 : ℝ) < β) (hβ' : β < 0) (ht : Admissible hH t) :
    deriv (deriv (fun x => normSqResolvent H g x ^ β)) t < 0 := by
  have ht' := fun i => ne_of_gt (ht i)
  rw [deriv2_rpow_normSqResolvent hH hg β ht']
  have hcs := normSqResolvent_mul_secondDeriv hH g ht'
  have hd := deriv_normSqResolvent_neg hH hg ht
  have hsq : 0 < (deriv (normSqResolvent H g) t) ^ 2 := sq_pos_of_ne_zero hd.ne
  have hbr : 0 < (β - 1) * (deriv (normSqResolvent H g) t) ^ 2 +
      normSqResolvent H g t * deriv (deriv (normSqResolvent H g)) t := by nlinarith
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos hβ' (Real.rpow_pos_of_pos (normSqResolvent_pos hH hg ht') _)) hbr

/-- Positive powers of a nonzero squared resolvent are strictly convex. -/
theorem strictConvexOn_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ} (hβ : 0 < β) :
    StrictConvexOn ℝ (Ioi a) (fun t => normSqResolvent H g t ^ β) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi a)
  · intro t ht
    exact (contDiffAt_rpow_normSqResolvent hH hg β
      (fun i => ne_of_gt (by linarith [ha i, ht.out])) 0).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioi a := interior_subset ht
    exact deriv2_rpow_normSqResolvent_pos hH hg hβ
      (fun i => by linarith [ha i, ht'.out])

/-- Negative powers are concave down to and including the inverse square-root endpoint. -/
theorem concaveOn_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ}
    (hβ : -(1 / 2 : ℝ) ≤ β) (hβ' : β < 0) :
    ConcaveOn ℝ (Ioi a) (fun t => normSqResolvent H g t ^ β) := by
  have hc (t : ℝ) (ht : t ∈ Ioi a) (k : WithTop ℕ∞) :
      ContDiffAt ℝ k (fun t => normSqResolvent H g t ^ β) t :=
    contDiffAt_rpow_normSqResolvent hH hg β
      (fun i => ne_of_gt (by linarith [ha i, ht.out])) k
  apply concaveOn_of_deriv2_nonpos (convex_Ioi a)
  · exact fun t ht => (hc t ht 0).continuousAt.continuousWithinAt
  · exact fun t ht =>
      ((hc t (interior_subset ht) 1).differentiableAt (by norm_num)).differentiableWithinAt
  · exact fun t ht => (((hc t (interior_subset ht) 2).derivWithin (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).differentiableWithinAt
  · intro t ht
    exact deriv2_rpow_normSqResolvent_nonpos hH hg hβ hβ'
      (fun i => by linarith [ha i, (interior_subset ht : t ∈ Ioi a).out])

/-- Strict concavity holds above the inverse square-root endpoint. -/
theorem strictConcaveOn_rpow_normSqResolvent {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) {β : ℝ}
    (hβ : -(1 / 2 : ℝ) < β) (hβ' : β < 0) :
    StrictConcaveOn ℝ (Ioi a) (fun t => normSqResolvent H g t ^ β) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi a)
  · intro t ht
    exact (contDiffAt_rpow_normSqResolvent hH hg β
      (fun i => ne_of_gt (by linarith [ha i, ht.out])) 0).continuousAt.continuousWithinAt
  · intro t ht
    exact deriv2_rpow_normSqResolvent_neg hH hg hβ hβ'
      (fun i => by linarith [ha i, (interior_subset ht : t ∈ Ioi a).out])

/-- Convexity and strict concavity regimes for powers of a nonzero squared resolvent.
The endpoint exponent `-1/2` is deliberately excluded from the strict concavity clause. -/
theorem rpow_normSqResolvent_convexity {g : E} (hg : g ≠ 0) (a : ℝ)
    (ha : ∀ i, 0 ≤ a + hH.eigenvalues rfl i) :
    (∀ β : ℝ, 0 < β → StrictConvexOn ℝ (Ioi a)
      (fun t => normSqResolvent H g t ^ β)) ∧
    (∀ β : ℝ, -(1 / 2 : ℝ) ≤ β → β < 0 → ConcaveOn ℝ (Ioi a)
      (fun t => normSqResolvent H g t ^ β)) ∧
    (∀ β : ℝ, -(1 / 2 : ℝ) < β → β < 0 → StrictConcaveOn ℝ (Ioi a)
      (fun t => normSqResolvent H g t ^ β)) :=
  ⟨fun _ hb => strictConvexOn_rpow_normSqResolvent hH hg a ha hb,
    fun _ hb hb' => concaveOn_rpow_normSqResolvent hH hg a ha hb hb',
    fun _ hb hb' => strictConcaveOn_rpow_normSqResolvent hH hg a ha hb hb'⟩

end Operator
end Optimization.SecularResolvent
