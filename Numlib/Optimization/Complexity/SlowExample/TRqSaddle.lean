import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.MultivariateTaylor.Coord
import Numlib.Optimization.Complexity.SlowExample.TRq
import Numlib.Optimization.ModelBased.HighOrder.TRqCall
import Numlib.Optimization.Optimality.TaylorStability

/-!
# A slow TRq decrease when the radius is shared across the orders

The trust-region method TRq ([cartis2022evaluation], Algorithm 12.2.1) uses one radius `Δ_k` for
the approximate optimality tests of all orders `j ≤ q`. First-order failures can therefore drive
the radius down to the scale of `ε_1`, and a following second-order step of that length decreases
the objective by much less than `ε_2^3`. This file builds such a run for `q = 2` on the box
`X = [-1, 1]²` for the saddle quadratic `f_a(x) = x_1²/2 - a x_2²/2`, whose derivatives of orders
`1` and `2` have Lipschitz constants and bounds independent of `a ∈ [0, 1]`. The decrease at a
successful iteration is thus not bounded below by `κ min_j ε_j^{j+1}` with `κ` depending only on
the parameters and these constants; the decrease that holds is `κ ε_min^{q+1}`
(`Optimization.IsTRqRun.taylorDecrement_ge_of_anchored`).

## Main definitions

* `Optimization.halfSq`: `t ↦ t²/2`;
* `Optimization.saddleQuad a`: `f_a(x) = x_1²/2 - a x_2²/2` on `ℝ²`;
* `Optimization.saddleBox`: the box `[-1, 1]²`;
* `Optimization.saddleTRqParams`: the TRq parameters of the example.

## Main results

* `Optimization.iteratedFDerivLipschitzOn_saddleQuad`,
  `Optimization.norm_iteratedFDeriv_saddleQuad_le_four`: uniform constants on the ball of
  radius `2`;
* `Optimization.exists_isTRqRun_saddleQuad_decrease_lt`: for every `κ > 0`, a TRq run on the box
  with a successful iteration decreasing `f_a` by less than `κ min_j ε_j^{j+1}`.
-/

open Set Metric
open scoped Nat ContDiff

set_option hygiene false in
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The first coordinate direction of `ℝ²`. -/
local notation "e₁" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The second coordinate direction of `ℝ²`. -/
local notation "e₂" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

namespace Optimization

open EuclideanSpace (norm_smul_single)

/-- `t ↦ t²/2`. -/
noncomputable def halfSq : ℝ → ℝ := fun t => t ^ 2 / 2

/-- Unfolding `halfSq`. -/
@[simp]
theorem halfSq_apply (t : ℝ) : halfSq t = t ^ 2 / 2 := rfl

/-- `(t²/2)' = t`. -/
theorem deriv_halfSq : deriv halfSq = fun t => t := by
  funext t
  unfold halfSq
  have := ((hasDerivAt_pow 2 t).div_const 2)
  rw [this.deriv]; ring

/-- `(t²/2)^{(1)} = t`. -/
theorem iteratedDeriv_halfSq_one (t : ℝ) : iteratedDeriv 1 halfSq t = t := by
  rw [iteratedDeriv_one, deriv_halfSq]

/-- `(t²/2)'' = 1`. -/
theorem iteratedDeriv_halfSq_two (t : ℝ) : iteratedDeriv 2 halfSq t = 1 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_halfSq, deriv_id'']

/-- `(t²/2)''' = 0`. -/
theorem iteratedDeriv_halfSq_three (t : ℝ) : iteratedDeriv 3 halfSq t = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, deriv_halfSq, deriv_id'']
  simp

/-- `t ↦ t²/2` is smooth. -/
theorem contDiff_halfSq : ContDiff ℝ ∞ halfSq := by
  unfold halfSq; fun_prop

/-- `‖∇ⁿ (w ↦ w_i²/2)(v)‖ ≤ |(t²/2)^{(n)}(v_i)|`. -/
private theorem norm_iteratedFDeriv_halfSq_comp_le (i : Fin 2) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (fun w : ℝ² => halfSq (w i)) v‖ ≤ |iteratedDeriv n halfSq (v i)| :=
  ContDiffAt.norm_iteratedFDeriv_comp_coord_le i
    (contDiff_halfSq.contDiffAt.of_le (by exact_mod_cast le_top))

/-- `w ↦ w_i²/2` is smooth. -/
theorem contDiff_halfSq_comp_apply (i : Fin 2) : ContDiff ℝ ∞ (fun w : ℝ² => halfSq (w i)) :=
  contDiff_halfSq.comp (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).contDiff

/-- The saddle quadratic `f_a(x) = x_1²/2 - a x_2²/2` on `ℝ²` (`x_1 = v 0`, `x_2 = v 1`). -/
noncomputable def saddleQuad (a : ℝ) : ℝ² → ℝ := fun v => halfSq (v 0) - a * halfSq (v 1)

/-- `f_a` as a difference of coordinate squares. -/
private theorem saddleQuad_eq_sub (a : ℝ) :
    saddleQuad a = (fun w : ℝ² => halfSq (w 0)) - a • (fun w : ℝ² => halfSq (w 1)) := by
  funext v; simp [saddleQuad]

/-- `f_a` is smooth. -/
theorem contDiff_saddleQuad (a : ℝ) : ContDiff ℝ ∞ (saddleQuad a) := by
  rw [saddleQuad_eq_sub]
  exact (contDiff_halfSq_comp_apply 0).sub ((contDiff_halfSq_comp_apply 1).const_smul a)

/-- `f_a` is `C^n` everywhere. -/
theorem contDiffAt_saddleQuad (a : ℝ) (n : ℕ) (y : ℝ²) : ContDiffAt ℝ n (saddleQuad a) y :=
  ((contDiff_saddleQuad a).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)).contDiffAt

/-- `‖∇ⁿ f_a(v)‖ ≤ |(t²/2)^{(n)}(v_1)| + a |(t²/2)^{(n)}(v_2)|` for `a ≥ 0`. -/
theorem norm_iteratedFDeriv_saddleQuad_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (v : ℝ²) :
    ‖iteratedFDeriv ℝ n (saddleQuad a) v‖ ≤
      |iteratedDeriv n halfSq (v 0)| + a * |iteratedDeriv n halfSq (v 1)| := by
  have h0 := ((contDiff_halfSq_comp_apply 0).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1 := ((contDiff_halfSq_comp_apply 1).of_le (by exact_mod_cast le_top : (n : ℕ∞ω) ≤
      ∞)).contDiffAt
    (x := v)
  have h1' : ContDiffAt ℝ n (a • fun w : ℝ² => halfSq (w 1)) v := h1.const_smul a
  rw [saddleQuad_eq_sub, iteratedFDeriv_sub_apply h0 h1', iteratedFDeriv_const_smul_apply h1]
  refine (norm_sub_le _ _).trans (add_le_add (norm_iteratedFDeriv_halfSq_comp_le 0 n v) ?_)
  rw [norm_smul, Real.norm_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_halfSq_comp_le 1 n v) ha

/-- `∇² f_a` is constant (`0`-Lipschitz) for `a ≥ 0`. -/
theorem iteratedFDerivLipschitzOn_saddleQuad_two {a : ℝ} (ha : 0 ≤ a) (C : Set ℝ²)
    (hC : Convex ℝ C) : IteratedFDerivLipschitzOn (saddleQuad a) 2 0 C :=
  iteratedFDerivLipschitzOn_of_norm_le hC
    (fun y _ => contDiffAt_saddleQuad a _ y)
    fun x _ => (norm_iteratedFDeriv_saddleQuad_le ha 3 x).trans (by
      rw [iteratedDeriv_halfSq_three, iteratedDeriv_halfSq_three]; simp)

/-- `f_a` is quadratic: `ΔT_2(x, s) = f_a(x) - f_a(x + s)`. -/
theorem taylorDecrement_two_saddleQuad {a : ℝ} (ha : 0 ≤ a) (x s : ℝ²) :
    (ftaylorSeries ℝ (saddleQuad a) x).taylorDecrement 2 s =
      saddleQuad a x - saddleQuad a (x + s) := by
  rw [ftaylorSeries_taylorDecrement_eq]
  have := norm_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => contDiffAt_saddleQuad a _ y)
    (iteratedFDerivLipschitzOn_saddleQuad_two ha univ convex_univ) (mem_univ x) (mem_univ (x + s))
  simp only [zero_div, zero_mul] at this
  have h := norm_le_zero_iff.1 this
  rw [sub_eq_zero] at h
  rw [h]

/-- The derivative of `f_a`: `s ↦ x_1 s_1 - a x_2 s_2`. -/
theorem hasFDerivAt_saddleQuad (a : ℝ) (v : ℝ²) :
    HasFDerivAt (saddleQuad a)
      ((v 0) • (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) - (a * v 1) • EuclideanSpace.proj 1) v := by
  have h1 : HasFDerivAt (fun w : ℝ² => w 1) (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 1 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun w : ℝ² => w 0) (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ) v :=
    (EuclideanSpace.proj 0 : ℝ² →L[ℝ] ℝ).hasFDerivAt
  have := ((h0.pow 2).mul_const (1 / 2 : ℝ)).sub (((h1.pow 2).mul_const (1 / 2 : ℝ)).const_mul a)
  convert this using 1
  · funext w; simp only [saddleQuad, halfSq, Pi.sub_apply]; ring
  · ext s; simp; ring

/-- `ΔT_1(x, s) = -(x_1 s_1 - a x_2 s_2)`. -/
theorem taylorDecrement_one_saddleQuad (a : ℝ) (x s : ℝ²) :
    (ftaylorSeries ℝ (saddleQuad a) x).taylorDecrement 1 s = -(x 0 * s 0 - a * x 1 * s 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  change -(iteratedFDeriv ℝ 1 _ x (fun _ => s)) = _
  rw [iteratedFDeriv_one_apply, (hasFDerivAt_saddleQuad a x).fderiv]
  simp

/-- The box `[-1, 1]²`. -/
def saddleBox : Set ℝ² := {v | -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1}

/-- Membership in the box. -/
theorem mem_saddleBox {v : ℝ²} : v ∈ saddleBox ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 ∧ -1 ≤ v 1 ∧ v 1 ≤ 1 := Iff.rfl

/-- The box is closed. -/
theorem isClosed_saddleBox : IsClosed saddleBox := by
  have hc : ∀ a : ℝ, Continuous fun _ : ℝ² => a := fun a => continuous_const
  have h := ((isClosed_le (hc (-1)) (PiLp.continuous_apply 2 _ 0)).inter
    (isClosed_le (PiLp.continuous_apply 2 _ 0) (hc 1))).inter
    ((isClosed_le (hc (-1)) (PiLp.continuous_apply 2 _ 1)).inter
    (isClosed_le (PiLp.continuous_apply 2 _ 1) (hc 1)))
  convert h using 1
  ext v
  simp only [saddleBox, Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- The box lies in the ball of radius `2`. -/
theorem saddleBox_subset_ball : saddleBox ⊆ ball (0 : ℝ²) 2 := by
  intro v hv
  obtain ⟨h0, h2, h3, h4⟩ := hv
  rw [mem_ball_zero_iff]
  have hs := EuclideanSpace.norm_sq_eq_fin_two v
  have : ‖v‖ ^ 2 < 2 ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this

/-- For `a ∈ [0, 1]`, the derivatives of orders `1` and `2` of `f_a` are `4`-Lipschitz on the
ball of radius `2`. -/
theorem iteratedFDerivLipschitzOn_saddleQuad {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 2) : IteratedFDerivLipschitzOn (saddleQuad a) j 4 (ball 0 2) := by
  have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
  refine iteratedFDerivLipschitzOn_of_norm_le (convex_ball 0 2)
    (fun y _ => contDiffAt_saddleQuad a _ y) fun x _ =>
      (norm_iteratedFDeriv_saddleQuad_le ha0 _ x).trans ?_
  rcases hj' with rfl | rfl
  · rw [iteratedDeriv_halfSq_two, iteratedDeriv_halfSq_two]; norm_num; linarith
  · rw [iteratedDeriv_halfSq_three, iteratedDeriv_halfSq_three]; norm_num

/-- For `a ∈ [0, 1]`, the derivatives of orders `1` and `2` of `f_a` are bounded by `4` on the
ball of radius `2`. -/
theorem norm_iteratedFDeriv_saddleQuad_le_four {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 2) {x : ℝ²} (hx : x ∈ ball (0 : ℝ²) 2) :
    ‖iteratedFDeriv ℝ j (saddleQuad a) x‖ ≤ 4 := by
  have hj' : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
  refine (norm_iteratedFDeriv_saddleQuad_le ha0 _ x).trans ?_
  rcases hj' with rfl | rfl
  · rw [iteratedDeriv_halfSq_one, iteratedDeriv_halfSq_one]
    have hx' : ‖x‖ < 2 := mem_ball_zero_iff.1 hx
    have h0 := (EuclideanSpace.abs_apply_le_norm x 0).trans hx'.le
    have h1 := (EuclideanSpace.abs_apply_le_norm x 1).trans hx'.le
    nlinarith [abs_nonneg (x 1)]
  · rw [iteratedDeriv_halfSq_two, iteratedDeriv_halfSq_two]; norm_num; linarith

/-- The TRq parameters of the example: `Δ₀ = Δ_max = 1`, `η₁ = 1/4`, `η₂ = 3/4`,
`γ₁ = 1/4`, `γ₂ = 1/2`, `γ₃ = 2`, `ς = 1/2`. -/
noncomputable def saddleTRqParams : TRqParams where
  Δ₀ := 1
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 4
  γ₂ := 1 / 2
  γ₃ := 2
  Δ₀_pos := one_pos
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_le_γ₂ := by norm_num
  γ₂_lt_one := by norm_num
  one_le_γ₃ := by norm_num
  Δmax := 1
  ς := 1 / 2
  Δ₀_le_Δmax := le_rfl
  ς_pos := by norm_num
  ς_le_one := by norm_num

/-- Unfolding `f_a`. -/
theorem saddleQuad_apply (a : ℝ) (v : ℝ²) :
    saddleQuad a v = (v 0) ^ 2 / 2 - a * ((v 1) ^ 2 / 2) := rfl

/-- At `p = b e_0`, `ΔT_1(d) = -b d_0`. -/
private theorem saddle_taylorDecrement_one_smul_e0 (a b : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1 d = -(b * d 0) := by
  rw [taylorDecrement_one_saddleQuad]; simp

/-- At `0`, `ΔT_1 = 0`. -/
private theorem saddle_taylorDecrement_one_zero (a : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 1 d = 0 := by
  rw [taylorDecrement_one_saddleQuad]; simp

/-- At `0`, `ΔT_2(d) = -d_0²/2 + a d_1²/2`. -/
private theorem saddle_taylorDecrement_two_zero {a : ℝ} (ha : 0 ≤ a) (d : ℝ²) :
    (ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2 d = -((d 0) ^ 2 / 2) + a * ((d 1) ^ 2 / 2)
        := by
  rw [taylorDecrement_two_saddleQuad ha, zero_add, saddleQuad_apply, saddleQuad_apply]; simp; ring

section Prefix

variable {a b Δ : ℝ} {ε : ℕ → ℝ}

/-- `b e_1 ∈ X` for `b ∈ [0, 1]` . -/
private theorem saddle_smul_e0_mem {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b • e₁ ∈ saddleBox := by
  simp only [mem_saddleBox, PiLp.smul_apply, PiLp.single_apply]
  norm_num
  exact ⟨by linarith, hb1⟩

/-- `b e_1 - Δ e_1 ∈ X` for `b, Δ ∈ [0, 1]`. -/
private theorem saddle_neg_smul_e0_mem {b Δ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hΔ1 : Δ ≤ 1) :
    (-Δ) • e₁ ∈ {e | b • e₁ + e ∈ saddleBox} := by
  simp only [Set.mem_ofPred_eq, mem_saddleBox, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]
  norm_num
  refine ⟨by linarith, by linarith⟩

/-- The first-order Step 1 at `p = b e_0` with radius `Δ ≤ 1`: the displacement `-Δ e_0`
achieves the first-order measure `b Δ`. -/
private theorem saddle_isApproxMeasureStep_smul_e0 (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hΔ0 : 0 ≤ Δ)
    (hΔ1 : Δ ≤ 1) :
    IsApproxMeasureStep ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1)
      (min Δ 1) {e | b • e₁ + e ∈ saddleBox} saddleTRqParams.ς ((-Δ) • e₁) := by
  rw [min_eq_left hΔ1]
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_single, abs_neg, abs_of_nonneg hΔ0]),
    saddle_neg_smul_e0_mem hb0 hb1 hΔ0 hΔ1⟩, ?_⟩
  have hm : decrementMeasure
      ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1) Δ
      {e | b • e₁ + e ∈ saddleBox} ≤ b * Δ := by
    refine decrementMeasure_le ⟨0, mem_closedBall_self hΔ0, by
      change b • e₁ + 0 ∈ saddleBox
      rw [add_zero]; exact saddle_smul_e0_mem hb0 hb1⟩ fun d hd => ?_
    rw [saddle_taylorDecrement_one_smul_e0]
    have h1 := EuclideanSpace.abs_apply_le_norm d 0
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 := mul_le_mul_of_nonneg_left (neg_le_abs (d 0)) hb0
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) hb0
    linarith
  rw [saddle_taylorDecrement_one_smul_e0]
  simp only [PiLp.smul_apply, PiLp.single_apply, ↓reduceIte, smul_eq_mul, mul_one]
  have hς : saddleTRqParams.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg hb0 hΔ0]

/-- The first-order step at `p = b e_0` with radius `Δ ≤ 1` (`ε_1 = b`): order `1` fails, the
step is the Step-1 displacement `-Δ e_0`. -/
private theorem saddle_isTRqStep_smul_e0 (hb : 0 < b) (hb1 : b ≤ 1) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hε1 : ε 1 = b) (W : ℕ → ℝ²) :
    IsTRqStep (ftaylorSeries ℝ (saddleQuad a) (b • e₁)) {e | b • e₁ + e ∈
        saddleBox}
      saddleTRqParams.ς 2 ε (min Δ 1) Δ (fun j => if j = 1 then (-Δ) • e₁ else W j) 1
      ((-Δ) • e₁) where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, saddle_taylorDecrement_one_smul_e0, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul, mul_one, min_eq_left hΔ1, pow_one, Nat.factorial_one, Nat.cast_one, div_one, hε1]
    have hς : saddleTRqParams.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos hb hΔ0]
  taylorDecrement_le_of_lt := fun i hi hlt => absurd hlt (by have := (Finset.mem_Icc.1 hi).1; omega)
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_single, abs_neg, abs_of_pos hΔ0]),
    saddle_neg_smul_e0_mem hb.le hb1 hΔ0.le hΔ1⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- `f_a(b e_1) = b²/2`. -/
private theorem saddleQuad_smul_e0 (a b : ℝ) : saddleQuad a (b • e₁) = b ^ 2 / 2 := by
  rw [saddleQuad_apply]; simp

/-- `f_a(b e_1 - Δ e_1) = (b - Δ)²/2`. -/
private theorem saddleQuad_smul_e0_add (a b Δ : ℝ) :
    saddleQuad a (b • e₁ + (-Δ) • e₁) = (b - Δ) ^ 2 / 2 := by
  rw [saddleQuad_apply]; simp; ring

/-- An unsuccessful first-order iteration at `p` with radius `Δ ≥ 4b`: the ratio is
`1 - Δ/(2b) ≤ -1`, the iterate stays and the radius is divided by `4`. -/
private theorem saddle_trAcceptance_unsucc (hb : 0 < b) (h4 : 4 * b ≤ Δ) :
    TRAcceptance saddleTRqParams.toTRParams
      (reductionRatio (saddleQuad a) (b • e₁) ((-Δ) • e₁)
        ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1 ((-Δ) • e₁)))
      (b • e₁) ((-Δ) • e₁) (b • e₁) Δ (Δ / 4) := by
  have hΔ : 0 < Δ := by linarith
  have hρ : reductionRatio (saddleQuad a) (b • e₁) ((-Δ) • e₁)
      ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1 ((-Δ) • e₁)) < 1 /
          4 := by
    rw [reductionRatio_def, saddleQuad_smul_e0, saddleQuad_smul_e0_add,
      saddle_taylorDecrement_one_smul_e0]
    simp only [PiLp.smul_apply, PiLp.single_apply, ↓reduceIte, smul_eq_mul, mul_one]
    rw [div_lt_iff₀ (by nlinarith)]
    nlinarith
  refine ⟨?_, ⟨fun h => absurd h (not_le.2 (hρ.trans (by norm_num : (1 : ℝ) / 4 < 3 / 4))),
    fun h => absurd h (not_le.2 hρ), fun _ => ⟨by change 1 / 4 * Δ ≤ Δ / 4; linarith,
      by change Δ / 4 ≤ 1 / 2 * Δ; linarith⟩⟩⟩
  exact (ite_eq_right (not_le.2 hρ)).symm

/-- The successful first-order iteration at `p` with radius `b`: the ratio is `1/2`, the step
lands at `0` and the radius stays `b`. -/
private theorem saddle_trAcceptance_succ (hb : 0 < b) :
    TRAcceptance saddleTRqParams.toTRParams
      (reductionRatio (saddleQuad a) (b • e₁) ((-b) • e₁)
        ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1 ((-b) • e₁)))
      (b • e₁) ((-b) • e₁) 0 b b := by
  have hρ : reductionRatio (saddleQuad a) (b • e₁) ((-b) • e₁)
      ((ftaylorSeries ℝ (saddleQuad a) (b • e₁)).taylorDecrement 1 ((-b) • e₁)) = 1 /
          2 := by
    rw [reductionRatio_def, saddleQuad_smul_e0, saddleQuad_smul_e0_add,
      saddle_taylorDecrement_one_smul_e0]
    simp only [PiLp.smul_apply, PiLp.single_apply, ↓reduceIte, smul_eq_mul, mul_one]
    field_simp; ring
  rw [hρ]
  refine ⟨?_, ⟨fun h => absurd h (by change ¬ (3 / 4 : ℝ) ≤ 1 / 2; norm_num),
    fun _ _ => ⟨by change 1 / 2 * b ≤ b; linarith, le_rfl⟩,
    fun h => absurd h (by change ¬ (1 / 2 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show saddleTRqParams.η₁ ≤ (1 / 2 : ℝ) by change (1 / 4 : ℝ) ≤ 1 / 2; norm_num),
    ← add_smul, add_neg_cancel, zero_smul]

/-- The second-order Step 1 at `0` with radius `b ≤ 1`: `b e_2` achieves the measure
`a b²/2`. -/
private theorem saddle_isApproxMeasureStep_zero (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    IsApproxMeasureStep ((ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2)
      (min b 1) {e | (0 : ℝ²) + e ∈ saddleBox} saddleTRqParams.ς (b • e₂) := by
  rw [min_eq_left hb1]
  have hmem : b • e₂ ∈ {e | (0 : ℝ²) + e ∈ saddleBox} := by
    simp only [Set.mem_ofPred_eq, zero_add, mem_saddleBox, PiLp.smul_apply, PiLp.single_apply]
    norm_num; exact ⟨by linarith, hb1⟩
  refine ⟨⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_single, abs_of_nonneg hb0]), hmem⟩, ?_⟩
  have hm : decrementMeasure ((ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2) b
      {e | (0 : ℝ²) + e ∈ saddleBox} ≤ a * (b ^ 2 / 2) := by
    refine decrementMeasure_le ⟨0, mem_closedBall_self hb0, by
      change (0 : ℝ²) + 0 ∈ saddleBox
      simp only [add_zero, mem_saddleBox, PiLp.zero_apply]; norm_num⟩ fun d hd => ?_
    rw [saddle_taylorDecrement_two_zero ha]
    have h1 := EuclideanSpace.abs_apply_le_norm d 1
    have h2 := mem_closedBall_zero_iff.1 hd.1
    have h3 : (d 1) ^ 2 ≤ b ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
    nlinarith [sq_nonneg (d 0)]
  have hval : (ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2 (b • e₂) = a * (b ^ 2 / 2)
      := by
    rw [saddle_taylorDecrement_two_zero ha]; simp
  rw [hval]
  have hς : saddleTRqParams.ς = 1 / 2 := rfl
  rw [hς]
  linarith [mul_nonneg ha (sq_nonneg b)]

/-- The second-order step at `0` with radius `b ≤ 1` (`ε_2 = a`): order `1` passes
(`∇f(0) = 0`), order `2` fails, the step is the Step-1 displacement `b e_2`. -/
private theorem saddle_isTRqStep_zero (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) (hε1 : 0 ≤ ε 1)
    (hε2 : ε 2 = a) (W : ℕ → ℝ²) :
    IsTRqStep (ftaylorSeries ℝ (saddleQuad a) 0) {e | (0 : ℝ²) + e ∈ saddleBox}
      saddleTRqParams.ς 2 ε (min b 1) b (fun j => if j = 2 then b • e₂ else W j) 2
      (b • e₂) where
  order_mem := by simp
  lt_taylorDecrement := by
    simp only [↓reduceIte, saddle_taylorDecrement_two_zero ha.le, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, min_eq_left hb1, hε2]
    norm_num
    have hς : saddleTRqParams.ς = 1 / 2 := rfl
    rw [hς]; nlinarith [mul_pos ha (pow_pos hb 2)]
  taylorDecrement_le_of_lt := fun i hi hlt => by
    have hi1 : i = 1 := by have := (Finset.mem_Icc.1 hi).1; omega
    subst hi1
    simp only [saddle_taylorDecrement_one_zero, show ¬ ((1 : ℕ) = 2) by decide, ↓reduceIte]
    have := saddleTRqParams.ς_pos
    have : 0 ≤ min b 1 := le_min hb.le zero_le_one
    positivity
  mem := ⟨mem_closedBall_zero_iff.2 (by rw [norm_smul_single, abs_of_pos hb]), by
    simp only [Set.mem_ofPred_eq, zero_add, mem_saddleBox, PiLp.smul_apply, PiLp.single_apply]
    norm_num; exact ⟨by linarith, hb1⟩⟩
  taylorDecrement_le := le_of_eq (by simp)

/-- The very successful second-order iteration at `0` with radius `b`: the ratio is `1`, the
step lands at `b e_2` and the radius stays `b`. -/
private theorem saddle_reductionRatio_zero (ha : 0 < a) (hb : 0 < b) :
    reductionRatio (saddleQuad a) 0 (b • e₂)
      ((ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2 (b • e₂)) = 1 := by
  have h : saddleQuad a 0 - saddleQuad a (0 + b • e₂) = a * (b ^ 2 / 2) := by
    rw [zero_add, saddleQuad_apply, saddleQuad_apply]; simp
  rw [reductionRatio_def, taylorDecrement_two_saddleQuad ha.le, h, div_self]
  positivity

/-- The very successful second-order iteration at `0` with radius `b`: the step lands at
`b e_2` and the radius stays `b`. -/
private theorem saddle_trAcceptance_zero (ha : 0 < a) (hb : 0 < b) :
    TRAcceptance saddleTRqParams.toTRParams
      (reductionRatio (saddleQuad a) 0 (b • e₂)
        ((ftaylorSeries ℝ (saddleQuad a) 0).taylorDecrement 2 (b • e₂)))
      0 (b • e₂) (b • e₂) b b := by
  rw [saddle_reductionRatio_zero ha hb]
  refine ⟨?_, ⟨fun _ => ⟨le_rfl, by change b ≤ 2 * b; linarith⟩,
    fun _ h => absurd h (by change ¬ (1 : ℝ) < 3 / 4; norm_num),
    fun h => absurd h (by change ¬ (1 : ℝ) < 1 / 4; norm_num)⟩⟩
  rw [ite_eq_left (show saddleTRqParams.η₁ ≤ (1 : ℝ) by change (1 / 4 : ℝ) ≤ 1; norm_num), zero_add]

end Prefix

/-- **A successful TRq iteration with a small decrease** when the radius is shared across the
orders. For the parameters `saddleTRqParams`, the threshold `ϑ = 1`, the box `X = [-1, 1]²` and
every `κ > 0` there are `a ∈ (0, 1]`, tolerances `ε ∈ (0, 1]²` and a run of TRq
([cartis2022evaluation], Algorithm 12.2.1) on `X` for `f_a(x) = x_1²/2 - a x_2²/2` with a
successful iteration `k` before termination that decreases `f_a` by less than
`κ min_j ε_j^{j+1}`. The derivatives of `f_a` of orders `1, 2` are `4`-Lipschitz and bounded by `4`
on the ball of radius `2 ⊇ X`, uniformly in `a` (`iteratedFDerivLipschitzOn_saddleQuad`,
`norm_iteratedFDeriv_saddleQuad_le_four`), so no decrease `κ min_j ε_j^{j+1}` with `κ` depending
only on these constants holds at every successful iteration.

With `r = 2^{-N}`, `ε_1 = r²` and `ε_2 = a = r`: `N` unsuccessful first-order iterations at
`(r², 0)` shrink the radius from `1` to `r²`, a successful step reaches `0`, where the gradient
vanishes and the second-order test fails, and the second-order step `r² e_2` decreases `f_a` by
`r⁵/2`, against `κ min(ε_1², ε_2³) = κ r⁴`. The run continues as any run from `r² e_2`
(`Optimization.exists_isTRqRun_append`). -/
theorem exists_isTRqRun_saddleQuad_decrease_lt {κ : ℝ} (hκ : 0 < κ) :
    ∃ (a : ℝ) (ε : ℕ → ℝ) (x s : ℕ → ℝ²) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝ²) (k : ℕ),
      0 < a ∧ a ≤ 1 ∧ (∀ j ∈ Finset.Icc 1 2, ε j ∈ Ioc 0 1) ∧ x 0 ∈ saddleBox ∧
      IsTRqRun (saddleQuad a) (fun k => ftaylorSeries ℝ (saddleQuad a) (x k))
        (fun k => {e | x k + e ∈ saddleBox}) saddleTRqParams 2 ε 1 x s Δ jk d ∧
      (∀ i ≤ k, ¬ trqTest (fun k => ftaylorSeries ℝ (saddleQuad a) (x k)) saddleTRqParams 2 ε 1
        Δ d i) ∧
      saddleTRqParams.η₁ ≤
        trqRatio (saddleQuad a) (fun k => ftaylorSeries ℝ (saddleQuad a) (x k)) x s jk k ∧
      saddleQuad a (x k) - saddleQuad a (x (k + 1)) < κ * finMin 1 (fun j => ε j ^ (j + 1)) 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos two_pos hκ) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 / 2) ^ N := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ by positivity
  have hr1 : r ≤ 1 := hr ▸ pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = r ^ 2 := ⟨_, rfl⟩
  have hb : 0 < b := hbdef ▸ by positivity
  have hb1 : b ≤ 1 := hbdef ▸ pow_le_one₀ hr0.le hr1
  have hpowN : ((1 : ℝ) / 4) ^ N = b := by
    rw [hbdef, hr, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hq0 : ∀ k : ℕ, 0 < ((1 : ℝ) / 4) ^ k := fun k => by positivity
  have hq1 : ∀ k : ℕ, ((1 : ℝ) / 4) ^ k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun j => if j = 1 then b else r := ⟨_, rfl⟩
  have hε1 : ε 1 = b := by simp [hεdef]
  have hε2 : ε 2 = r := by simp [hεdef]
  -- the Step-1 displacements of the orders not used
  have hW : ∀ (y : ℝ²) (δ : ℝ) (j : ℕ), ∃ w : ℝ², y ∈ saddleBox → 0 ≤ δ →
      IsApproxMeasureStep ((ftaylorSeries ℝ (saddleQuad r) y).taylorDecrement j) δ
        {e | y + e ∈ saddleBox} saddleTRqParams.ς w := by
    intro y δ j
    by_cases h : y ∈ saddleBox ∧ 0 ≤ δ
    · obtain ⟨w, hw⟩ := exists_isApproxMeasureStep_taylorDecrement
        (ftaylorSeries ℝ (saddleQuad r) y) j
        (isClosed_saddleBox.preimage (continuous_const.add continuous_id))
        (by change y + 0 ∈ saddleBox; rw [add_zero]; exact h.1) h.2 saddleTRqParams.ς_le_one
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose W hW using hW
  -- the continuation: any TRq run on the box from `b e_2` with initial radius `b`
  have hbmax : b ≤ saddleTRqParams.Δmax := hb1
  have hq₀ : b • e₂ ∈ saddleBox := by
    simp only [mem_saddleBox, PiLp.smul_apply, PiLp.single_apply]
    norm_num; exact ⟨by linarith, hb1⟩
  obtain ⟨y, sy, Δy, jy, dy, hy0, hyr⟩ := exists_isTRqRun_feasible isClosed_saddleBox
    (saddleQuad r) (saddleTRqParams.withΔ₀ b hb hbmax) 2 ε zero_le_one hq₀
  -- the explicit prefix: `N` unsuccessful first-order iterations at `b e_1`, a successful one to
  -- `0`, and the successful second-order iteration from `0` to `b e_2`
  obtain ⟨xp, hxp⟩ : ∃ xp : ℕ → ℝ², ∀ k, xp k =
      if k ≤ N then b • e₁ else if k = N + 1 then 0 else b • e₂ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Δp, hΔp⟩ : ∃ Δp : ℕ → ℝ, ∀ k, Δp k = if k ≤ N then ((1 : ℝ) / 4) ^ k else b :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ℕ → ℝ², ∀ k, sp k =
      if k ≤ N then (-((1 : ℝ) / 4) ^ k) • e₁ else b • e₂ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨jp, hjp⟩ : ∃ jp : ℕ → ℕ, ∀ k, jp k = if k ≤ N then 1 else 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨dp, hdp⟩ : ∃ dp : ℕ → ℕ → ℝ², ∀ k, dp k =
      if k ≤ N then (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • e₁
        else W (b • e₁) (min (((1 : ℝ) / 4) ^ k) 1) j)
      else (fun j => if j = 2 then b • e₂ else W 0 (min b 1) j) :=
    ⟨_, fun _ => rfl⟩
  have hxl : ∀ k ≤ N, xp k = b • e₁ := fun k hk => by rw [hxp, ite_eq_left hk]
  have hΔl : ∀ k ≤ N, Δp k = ((1 : ℝ) / 4) ^ k := fun k hk => by rw [hΔp, ite_eq_left hk]
  have hsl : ∀ k ≤ N, sp k = (-((1 : ℝ) / 4) ^ k) • e₁ := fun k hk => by
    rw [hsp, ite_eq_left hk]
  have hjl : ∀ k ≤ N, jp k = 1 := fun k hk => by rw [hjp, ite_eq_left hk]
  have hdl : ∀ k ≤ N, dp k = (fun j => if j = 1 then (-((1 : ℝ) / 4) ^ k) • e₁
      else W (b • e₁) (min (((1 : ℝ) / 4) ^ k) 1) j) := fun k hk => by
    rw [hdp, ite_eq_left hk]
  have hxN : xp (N + 1) = 0 := by rw [hxp, ite_eq_right (by omega), ite_eq_left rfl]
  have hxN2 : xp (N + 1 + 1) = b • e₂ := by
    rw [hxp, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hΔN : ∀ k, N < k → Δp k = b := fun k hk => by rw [hΔp, ite_eq_right (by omega)]
  have hsN : sp (N + 1) = b • e₂ := by rw [hsp, ite_eq_right (by omega)]
  have hjN : jp (N + 1) = 2 := by rw [hjp, ite_eq_right (by omega)]
  have hdN : dp (N + 1) = (fun j => if j = 2 then b • e₂ else W 0 (min b 1) j) := by
    rw [hdp, ite_eq_right (by omega)]
  have hcases : ∀ k < N + 2, k ≤ N ∨ k = N + 1 := fun k hk => by omega
  have hstep : ∀ k < N + 2, IsTRqStep (ftaylorSeries ℝ (saddleQuad r) (xp k))
      {e | xp k + e ∈ saddleBox} saddleTRqParams.ς 2 ε (min (Δp k) 1) (Δp k) (dp k) (jp k) (sp k) :=
    fun k hk => by
    rcases hcases k hk with h | rfl
    · rw [hxl k h, hΔl k h, hdl k h, hjl k h, hsl k h]
      exact saddle_isTRqStep_smul_e0 hb hb1 (hq0 k) (hq1 k) hε1 _
    · rw [hxN, hΔN _ (by omega), hdN, hjN, hsN]
      exact saddle_isTRqStep_zero hr0 hb hb1 (hε1 ▸ hb.le) hε2 _
  have hacc : ∀ k < N + 2, TRAcceptance saddleTRqParams.toTRParams
      (reductionRatio (saddleQuad r) (xp k) (sp k)
        ((ftaylorSeries ℝ (saddleQuad r) (xp k)).taylorDecrement (jp k) (sp k)))
      (xp k) (sp k) (xp (k + 1)) (Δp k) (Δp (k + 1)) := fun k hk => by
    rcases hcases k hk with h | rfl
    · rcases Nat.lt_or_ge k N with hkN | hkN
      · rw [hxl k h, hxl (k + 1) hkN, hsl k h, hΔl k h, hΔl (k + 1) hkN, hjl k h]
        have h4 : 4 * b ≤ ((1 : ℝ) / 4) ^ k := by
          rw [← hpowN]
          have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
            (show k + 1 ≤ N by omega)
          rw [pow_succ] at this
          linarith
        have e : ((1 : ℝ) / 4) ^ (k + 1) = ((1 : ℝ) / 4) ^ k / 4 := by rw [pow_succ]; ring
        rw [e]
        exact saddle_trAcceptance_unsucc hb h4
      · obtain rfl : k = N := le_antisymm h hkN
        rw [hxl k h, hxN, hsl k h, hΔl k h, hΔN _ (by omega), hjl k h, hpowN]
        exact saddle_trAcceptance_succ hb
    · rw [hxN, hxN2, hΔN _ (by omega), hΔN _ (by omega), hsN, hjN]
      exact saddle_trAcceptance_zero hr0 hb
  have hwit : ∀ k < N + 2, ∀ j ∈ Finset.Icc 1 2, IsApproxMeasureStep
      ((ftaylorSeries ℝ (saddleQuad r) (xp k)).taylorDecrement j) (min (Δp k) 1)
      {e | xp k + e ∈ saddleBox} saddleTRqParams.ς (dp k j) := fun k hk j _ => by
    rcases hcases k hk with h | rfl
    · rw [hxl k h, hΔl k h, hdl k h]
      by_cases hj1 : j = 1
      · subst hj1
        simp only [↓reduceIte]
        exact saddle_isApproxMeasureStep_smul_e0 hb.le hb1 (hq0 k).le (hq1 k)
      · simp only [hj1, ↓reduceIte]
        exact hW _ _ _ (saddle_smul_e0_mem hb.le hb1) (le_min (hq0 k).le zero_le_one)
    · rw [hxN, hΔN _ (by omega), hdN]
      by_cases hj2 : j = 2
      · subst hj2
        simp only [↓reduceIte]
        exact saddle_isApproxMeasureStep_zero hr0.le hb.le hb1
      · simp only [hj2, ↓reduceIte]
        exact hW _ _ _ (by simp [mem_saddleBox]) (le_min hb.le zero_le_one)
  have hcap : ∀ k < N + 2, Δp (k + 1) ≤ saddleTRqParams.Δmax := fun k _ => by
    change Δp (k + 1) ≤ 1
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rw [hΔl (k + 1) hkN]; exact hq1 _
    · rw [hΔN _ (by omega)]; exact hb1
  -- the run
  obtain ⟨x, s, Δ, jk, d, hx0, hrun, hns, -, hpre, hpre'⟩ := exists_isTRqRun_append
    (T := N + 2) (T' := 0) (c := 0) (f := saddleQuad r) (D := ftaylorSeries ℝ (saddleQuad r))
    (S := fun y => {e | y + e ∈ saddleBox}) (P := saddleTRqParams) (q := 2) (ε := ε) (ϑ := 1)
    (xp := xp) (sp := sp) (Δp := Δp) (jp := jp) (dp := dp)
    (by rw [hΔl 0 (Nat.zero_le _), pow_zero]; rfl)
    (hΔN _ (by omega)) hb hbmax hstep hacc hwit hcap (by rw [hy0, ← hxN2]) hyr
    (fun _ h => absurd h (Nat.not_lt_zero _)) (Nat.zero_le _)
  have hxN' : x (N + 1) = 0 := (hpre (N + 1) (by omega)).1.trans hxN
  refine ⟨r, ε, x, s, Δ, jk, d, N + 1, hr0, hr1, fun j hj => ?_, ?_,
    hrun, fun i hi => hns i (by omega), ?_, ?_⟩
  · have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
    rcases this with rfl | rfl
    · rw [hε1]; exact ⟨hb, hb1⟩
    · rw [hε2]; exact ⟨hr0, hr1⟩
  · rw [hx0, hxl 0 (Nat.zero_le _)]; exact saddle_smul_e0_mem hb.le hb1
  · obtain ⟨hsk, hjk, -⟩ := hpre' (N + 1) (by omega)
    rw [trqRatio_eq, hxN', hsk, hjk, hsN, hjN, saddle_reductionRatio_zero hr0 hb]
    change (1 / 4 : ℝ) ≤ 1; norm_num
  · -- the decrease `r⁵/2` against `κ min_j ε_j^{j+1} ≥ κ r⁴`
    rw [(hpre (N + 1 + 1) (by omega)).1, hxN2, hxN']
    have hdec : saddleQuad r 0 - saddleQuad r (b • e₂) = r * (b ^ 2 / 2) := by
      rw [saddleQuad_apply, saddleQuad_apply]; simp
    rw [hdec]
    have hmin : b ^ 2 ≤ finMin 1 (fun j => ε j ^ (j + 1)) 2 := by
      refine le_finMin (pow_le_one₀ hb.le hb1) fun j hj => ?_
      have : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
      rcases this with rfl | rfl
      · rw [hε1]
      · rw [hε2, hbdef]
        have : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
        calc (r ^ 2) ^ 2 = r ^ 4 := by ring
          _ ≤ r ^ 3 := this
    have hrN : r < 2 * κ := hr ▸ hN
    have hb2 : 0 < b ^ 2 := by positivity
    calc r * (b ^ 2 / 2) < κ * b ^ 2 := by nlinarith
      _ ≤ κ * finMin 1 (fun j => ε j ^ (j + 1)) 2 :=
          mul_le_mul_of_nonneg_left hmin hκ.le

end Optimization
