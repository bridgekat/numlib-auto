import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Positivity
import NumlibSurface.ConnGouldToint.Chapter06.Section01

/-!
# The Cauchy point of a quadratic model

[conn2000trust], Section 6.3. The estimate compares a minimizer on the feasible arc
with a particular feasible step.
-/

namespace ConnGouldToint.Chapter06

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The curvature bound (6.3.1) for a quadratic model with constant Hessian `H`. -/
noncomputable def quadraticCurvatureBound (H : E →L[ℝ] E) : ℝ :=
  1 + ‖H‖

/-- The Cauchy arc in displacement coordinates, i.e. with the current iterate as origin. -/
def cauchyArc (p : Seminorm ℝ E) (g : E) (Δ : ℝ) : Set E :=
  {s | ∃ t : ℝ, 0 ≤ t ∧ s = (-t) • g ∧ p s ≤ Δ}

/-- The Cauchy point (6.3.3) minimizes the model over the Cauchy arc. -/
def IsCauchyPoint (m : E → ℝ) (p : Seminorm ℝ E) (g : E) (Δ : ℝ) (s : E) : Prop :=
  IsMinOn m (cauchyArc p g Δ) s ∧ s ∈ cauchyArc p g Δ

/-- The ratio (6.3.5) of the Euclidean norm of the gradient to its trust-region norm. -/
noncomputable def cauchyNormRatio (p : Seminorm ℝ E) (g : E) : ℝ :=
  ‖g‖ / p g

private theorem quadraticModel_cauchy (c : ℝ) (g : E) (H : E →L[ℝ] E) (t : ℝ) :
    quadraticModel c g H.toLinearMap ((-t) • g) =
      c - t * ‖g‖ ^ 2 + (1 / 2) * t ^ 2 * inner ℝ g (H g) := by
  simp only [quadraticModel, ContinuousLinearMap.coe_coe, map_smul,
    inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- Theorem 6.3.1. The decrease at a Cauchy point of a quadratic model is bounded
below by the product of half the gradient norm and the shorter of the curvature
and trust-region lengths. -/
theorem theorem_6_3_1 (c : ℝ) (g : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 → v = 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) {s : E}
    (hs : IsCauchyPoint (quadraticModel c g H.toLinearMap) p g Δ s) :
    c - quadraticModel c g H.toLinearMap s ≥
      (1 / 2) * ‖g‖ * min (‖g‖ / quadraticCurvatureBound H) (cauchyNormRatio p g * Δ) := by
  by_cases hg : g = 0
  · obtain ⟨t, _, rfl, _⟩ := hs.2
    simp [hg, quadraticModel]
  have hpg : 0 < p g := lt_of_le_of_ne (apply_nonneg p g) (fun h ↦ hg (hp g h.symm))
  let β := quadraticCurvatureBound H
  have hβ : 0 < β := by dsimp [β, quadraticCurvatureBound]; positivity
  let t := min (1 / β) (Δ / p g)
  have ht : 0 ≤ t := le_min (div_nonneg zero_le_one hβ.le) (div_nonneg hΔ hpg.le)
  have htΔ : t * p g ≤ Δ := (le_div_iff₀ hpg).1 (min_le_right _ _)
  have htβ : t * β ≤ 1 := (le_div_iff₀ hβ).1 (min_le_left _ _)
  have htrial : (-t) • g ∈ cauchyArc p g Δ := by
    refine ⟨t, ht, rfl, ?_⟩
    simpa only [map_smul_eq_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht] using htΔ
  have hmin := isMinOn_iff.1 hs.1 _ htrial
  rw [quadraticModel_cauchy] at hmin
  have hcurv : inner ℝ g (H g) ≤ β * ‖g‖ ^ 2 := calc
    inner ℝ g (H g) ≤ |inner ℝ g (H g)| := le_abs_self _
    _ ≤ ‖g‖ * ‖H g‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖g‖ * (‖H‖ * ‖g‖) := mul_le_mul_of_nonneg_left (H.le_opNorm g) (norm_nonneg g)
    _ = ‖H‖ * ‖g‖ ^ 2 := by ring
    _ ≤ β * ‖g‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [β, quadraticCurvatureBound]
      linarith
  have hquad : t ^ 2 * inner ℝ g (H g) ≤ t * ‖g‖ ^ 2 := calc
    _ ≤ t ^ 2 * (β * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    _ = (t * β) * (t * ‖g‖ ^ 2) := by ring
    _ ≤ 1 * (t * ‖g‖ ^ 2) := mul_le_mul_of_nonneg_right htβ (mul_nonneg ht (sq_nonneg _))
    _ = _ := one_mul _
  have hlength : ‖g‖ * t = min (‖g‖ / β) (cauchyNormRatio p g * Δ) := by
    dsimp only [t]
    rw [mul_min_of_nonneg _ _ (norm_nonneg g)]
    simp only [cauchyNormRatio]
    congr 1 <;> ring
  change (1 / 2) * ‖g‖ * min (‖g‖ / β) (cauchyNormRatio p g * Δ) ≤
    c - quadraticModel c g H.toLinearMap s
  rw [← hlength]
  nlinarith only [hmin, hquad]

/-- AA.1. The decrease of the model is at least a prescribed positive fraction
of the Cauchy decrease benchmark (6.3.27). -/
def HasSufficientModelDecrease (m : E → ℝ) (x s g : E) (β Δ κ : ℝ) : Prop :=
  κ ∈ Set.Ioo (0 : ℝ) 1 ∧ κ * ‖g‖ * min (‖g‖ / β) Δ ≤ m x - m (x + s)

variable [CompleteSpace E]

/-- Theorem 6.3.4. A step satisfying AA.1 strictly reduces the model and is nonzero
at a noncritical point when the model and objective gradients agree (AM.3). -/
theorem theorem_6_3_4 {f m : E → ℝ} {x s : E} {β Δ κ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hmatch : gradient m x = gradient f x) (hg : gradient f x ≠ 0)
    (hdec : HasSufficientModelDecrease m x s (gradient m x) β Δ κ) :
    m (x + s) < m x ∧ s ≠ 0 := by
  have hgn : 0 < ‖gradient m x‖ := by
    rw [hmatch]
    exact norm_pos_iff.mpr hg
  have hpos : 0 < κ * ‖gradient m x‖ * min (‖gradient m x‖ / β) Δ :=
    mul_pos (mul_pos hdec.1.1 hgn) (lt_min (div_pos hgn hβ) hΔ)
  have hlt := sub_pos.mp (hpos.trans_le hdec.2)
  exact ⟨hlt, fun hz ↦ by simp [hz] at hlt⟩

end ConnGouldToint.Chapter06
