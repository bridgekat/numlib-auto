import Numlib.Optimization.DerivativeOracleMethods
import Mathlib.Basic.Real.Pointwise

/-!
# Scalar scaling of smooth oracle objectives

Positive output scaling and invertible scalar input scaling preserve boundedness below.
The actual infimum, gradient, full derivative tensors and homogeneous Lipschitz bounds
transform with their natural powers. The resulting smooth function class has the scaled
initial gap and highest-derivative Lipschitz budget.
-/

noncomputable section
open scoped ContDiff Pointwise

namespace Optimization.ZeroChains

variable {n p : ℕ}

/-- Scalar input and output scaling preserves every finite or infinite smoothness order. -/
theorem contDiff_rescale {f : Space n → ℝ} {q : ℕ∞ω} (hf : ContDiff ℝ q f)
    (a b : ℝ) : ContDiff ℝ q (rescale a b f) := by
  let B : Space n →L[ℝ] Space n := b • ContinuousLinearMap.id ℝ (Space n)
  exact contDiff_const.mul (hf.comp B.contDiff)

/-- The complete derivative tensor of a scaled objective, including order zero. -/
theorem iteratedFDeriv_rescale {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    {q : ℕ} (hq : q ≤ p) (a b : ℝ) (x : Space n) :
    iteratedFDeriv ℝ q (rescale a b f) x =
      (a * b ^ q) • iteratedFDeriv ℝ q f (b • x) := by
  let B : Space n →L[ℝ] Space n := b • ContinuousLinearMap.id ℝ (Space n)
  have hcomp : ContDiff ℝ p (f ∘ B) := hf.comp B.contDiff
  change iteratedFDeriv ℝ q (fun y => a • (f ∘ B) y) x = _
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (by exact_mod_cast hq)).contDiffAt,
    B.iteratedFDeriv_comp_right hf x (by exact_mod_cast hq)]
  ext v
  simp only [smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change a * (iteratedFDeriv ℝ q f (b • x)) (fun i => b • v i) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [mul_assoc]

/-- The actual gradient scales by the product of output and input scale factors. -/
theorem gradient_rescale {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (x : Space n) :
    gradient (rescale a b f) x = (a * b) • gradient f (b • x) := by
  ext i
  have h := mixedPartial_rescale hf le_rfl a b x (fun _ => i)
  simpa only [mixedPartial_one, pow_one, PiLp.smul_apply, smul_eq_mul] using h

/-- A scaled objective's entire value range is the scaled original range. -/
theorem range_rescale (f : Space n → ℝ) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Set.range (rescale a b f) = a • Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f (b • x), ⟨b • x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨b⁻¹ • x, by simp [rescale, smul_smul, hb]⟩

/-- Nonnegative output scaling transforms the actual infimum, even for unbounded objectives. -/
theorem sInf_range_rescale (f : Space n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≠ 0) :
    sInf (Set.range (rescale a b f)) = a * sInf (Set.range f) := by
  rw [range_rescale f a hb, Real.sInf_smul_of_nonneg ha, smul_eq_mul]

/-- Positive output scaling and invertible input scaling preserve boundedness below. -/
theorem bddBelow_range_rescale_iff (f : Space n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : b ≠ 0) :
    BddBelow (Set.range (rescale a b f)) ↔ BddBelow (Set.range f) := by
  rw [range_rescale f a hb]
  exact bddBelow_smul_iff_of_pos ha

end Optimization.ZeroChains

namespace Optimization.DerivativeOracle
open ZeroChains

/-- Positive scalar scaling transforms both the gap and highest-derivative Lipschitz
budgets of the actual smooth objective. -/
theorem FunctionClass.rescale {n p : ℕ} {Δ L a b : ℝ} {f : Space n → ℝ}
    (hf : FunctionClass p Δ L n f) (ha : 0 < a) (hb : 0 < b) :
    FunctionClass p (a * Δ) (a * b ^ (p + 1) * L) n (ZeroChains.rescale a b f) := by
  have hL := hf.lipschitz_nonneg
  refine ⟨contDiff_rescale hf.smooth a b,
    (bddBelow_range_rescale_iff f ha hb.ne').mpr hf.bounded_below,
    ?_, by positivity, ?_⟩
  · rw [sInf_range_rescale f ha.le hb.ne']
    simpa only [ZeroChains.rescale, smul_zero, ← mul_sub] using
      mul_le_mul_of_nonneg_left hf.initial_gap ha.le
  · intro x y
    have hs : ContDiff ℝ p f := hf.smooth.of_le (by simp)
    rw [iteratedFDeriv_rescale hs le_rfl, iteratedFDeriv_rescale hs le_rfl, ← smul_sub]
    let T := iteratedFDeriv ℝ p f (b • x) - iteratedFDeriv ℝ p f (b • y)
    apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
    intro v hv
    have hT := (T.norm_diagonal_le_diagonalNorm hv).trans (hf.lipschitz (b • x) (b • y))
    have hn : ‖b • x - b • y‖ = b * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    change ‖(a * b ^ p) • T.diagonal v‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha (pow_pos hb _))]
    calc
      (a * b ^ p) * ‖T.diagonal v‖ ≤ (a * b ^ p) * (L * (b * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left (by simpa only [hn] using hT) (by positivity)
      _ = a * b ^ (p + 1) * L * ‖x - y‖ := by rw [pow_succ]; ring

end Optimization.DerivativeOracle
