import Numlib.Optimization.Constrained.TargetMerit

/-!
# Uniform highest-derivative bounds for the actual target family

Every positive derivative of the target merit depends affinely on its target.
Two fixed target derivatives therefore control all targets in a bounded
interval. This uses the source merit regularity directly, without imposing
stronger separate objective or constraint derivative assumptions.
-/

namespace Constrained
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The actual squared target merit is an affine combination of targets zero
and one plus a target-dependent scalar constant. -/
theorem targetMerit_affine (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) :
    targetMerit f c t x = (1 - t) * targetMerit f c 0 x +
      t * targetMerit f c 1 x + (t ^ 2 - t) / 2 := by
  simp only [targetMerit]
  ring

/-- Every positive actual derivative of the target merit depends affinely on
its target, on the same open domain as the two fixed source merits. -/
theorem iteratedFDeriv_targetMerit_affine {f : E → ℝ} {c : E → F} {p : ℕ}
    (hp : 0 < p) {S : Set E} (hS : IsOpen S)
    (h0 : ContDiffOn ℝ p (targetMerit f c 0) S)
    (h1 : ContDiffOn ℝ p (targetMerit f c 1) S)
    {x : E} (hx : x ∈ S) (t : ℝ) :
    iteratedFDeriv ℝ p (targetMerit f c t) x =
      (1 - t) • iteratedFDeriv ℝ p (targetMerit f c 0) x +
        t • iteratedFDeriv ℝ p (targetMerit f c 1) x := by
  have hd0 := h0.contDiffAt (hS.mem_nhds hx)
  have hd1 := h1.contDiffAt (hS.mem_nhds hx)
  have he : targetMerit f c t =
      ((1 - t) • targetMerit f c 0 + t • targetMerit f c 1) +
        fun _ => (t ^ 2 - t) / 2 := by
    funext z
    exact targetMerit_affine f c t z
  rw [he, iteratedFDeriv_add_apply
      (f := (1 - t) • targetMerit f c 0 + t • targetMerit f c 1)
      (g := fun _ => (t ^ 2 - t) / 2)
      ((hd0.const_smul (1 - t)).add (hd1.const_smul t)) contDiffAt_const,
    iteratedFDeriv_add_apply (f := (1 - t) • targetMerit f c 0)
      (g := t • targetMerit f c 1) (hd0.const_smul (1 - t)) (hd1.const_smul t),
    iteratedFDeriv_const_smul_apply hd0, iteratedFDeriv_const_smul_apply hd1,
    iteratedFDeriv_const_of_ne (Nat.ne_of_gt hp)]
  simp

/-- Fixed Lipschitz constants at targets zero and one give a uniform actual
highest-derivative Lipschitz constant before every target in a bounded interval. -/
theorem exists_targetMerit_uniform_lipschitz {f : E → ℝ} {c : E → F} {p : ℕ}
    (hp : 0 < p) {C S : Set E} (hS : IsOpen S) (hCS : C ⊆ S)
    (h0 : ContDiffOn ℝ p (targetMerit f c 0) S)
    (h1 : ContDiffOn ℝ p (targetMerit f c 1) S)
    {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hl0 : ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c 0) x -
        iteratedFDeriv ℝ p (targetMerit f c 0) y‖ ≤ L0 * ‖x - y‖)
    (hl1 : ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c 1) x -
        iteratedFDeriv ℝ p (targetMerit f c 1) y‖ ≤ L1 * ‖x - y‖)
    (a b : ℝ) :
    ∃ L ≥ 0, ∀ t ∈ Icc a b, ∀ x ∈ C, ∀ y ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c t) x -
        iteratedFDeriv ℝ p (targetMerit f c t) y‖ ≤ L * ‖x - y‖ := by
  let B := |a| + |b|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(1 + B) * (L0 + L1), by positivity, ?_⟩
  intro t ht x hx y hy
  have htB : |t| ≤ B := by
    apply abs_le.mpr
    dsimp [B]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, ht.1]
    · linarith [le_abs_self b, abs_nonneg a, ht.2]
  have h1t : |1 - t| ≤ 1 + B := by
    have hh : |1 - t| ≤ 1 + |t| := by
      simpa only [sub_eq_add_neg, abs_one, abs_neg] using abs_add_le (1 : ℝ) (-t)
    linarith
  rw [iteratedFDeriv_targetMerit_affine hp hS h0 h1 (hCS hx),
    iteratedFDeriv_targetMerit_affine hp hS h0 h1 (hCS hy)]
  rw [show ((1 - t) • iteratedFDeriv ℝ p (targetMerit f c 0) x +
      t • iteratedFDeriv ℝ p (targetMerit f c 1) x) -
      ((1 - t) • iteratedFDeriv ℝ p (targetMerit f c 0) y +
      t • iteratedFDeriv ℝ p (targetMerit f c 1) y) =
      (1 - t) • (iteratedFDeriv ℝ p (targetMerit f c 0) x -
        iteratedFDeriv ℝ p (targetMerit f c 0) y) +
      t • (iteratedFDeriv ℝ p (targetMerit f c 1) x -
        iteratedFDeriv ℝ p (targetMerit f c 1) y) by
      simp only [smul_sub]; abel]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hz := norm_nonneg (x - y)
  have hA := mul_le_mul_of_nonneg_left (hl0 x hx y hy) (abs_nonneg (1 - t))
  have hD := mul_le_mul_of_nonneg_left (hl1 x hx y hy) (abs_nonneg t)
  have hE := mul_le_mul_of_nonneg_right h1t (mul_nonneg hL0 hz)
  have hF := mul_le_mul_of_nonneg_right
    (htB.trans (show B ≤ 1 + B by linarith)) (mul_nonneg hL1 hz)
  nlinarith

end Constrained
