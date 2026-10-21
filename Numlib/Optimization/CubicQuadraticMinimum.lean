import Numlib.Optimization.QuadraticSubproblem

/-!
# Quadratic minima implied by cubic minima

A cubic polynomial with zero constant term that is nonnegative on a ball has vanishing linear
part. Adding its values at opposite displacements shows its quadratic part is nonnegative.
-/

noncomputable section
open scoped Topology
open Metric Set Filter
namespace Optimization

/-- Nonnegativity of a cubic polynomial near zero forces its linear coefficient to vanish. -/
theorem linear_coefficient_eq_zero_of_cubic_nonneg {a b c r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, |t| < r → 0 ≤ a * t + b * t ^ 2 + c * t ^ 3) : a = 0 := by
  have hm : IsLocalMin (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) 0 := by
    apply Filter.mem_of_superset (ball_mem_nhds (0 : ℝ) hr)
    intro t ht
    change a * 0 + b * 0 ^ 2 + c * 0 ^ 3 ≤ _
    simpa using h t (by simpa [Real.dist_eq] using ht)
  have hd : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) a 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul b)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul c) using 1 <;> first | rfl | norm_num
  exact hd.deriv.symm.trans hm.deriv_eq_zero

/-- A cubic perturbation of a linear-plus-quadratic form cannot hide a negative quadratic
model on a ball. No symmetry assumptions are needed for the stronger diagonal statement. -/
theorem quadratic_nonneg_of_cubic_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h : ∀ s : E, ‖s‖ ≤ Δ → 0 ≤ g s + H s s / 2 + T (fun _ => s) / 6) :
    ∀ s : E, ‖s‖ ≤ Δ → 0 ≤ g s + H s s / 2 := by
  intro s hs
  by_cases he : Δ = 0
  · have hs0 : s = 0 := norm_eq_zero.mp (le_antisymm (he ▸ hs) (norm_nonneg s))
    simp [hs0]
  have hp : 0 < Δ := lt_of_le_of_ne hΔ (Ne.symm he)
  have hg : g s = 0 := by
    apply linear_coefficient_eq_zero_of_cubic_nonneg
      (r := Δ / (‖s‖ + 1)) (b := H s s / 2) (c := T (fun _ => s) / 6) (by positivity)
    intro t ht
    have hn : ‖t • s‖ ≤ Δ := by
      rw [norm_smul, Real.norm_eq_abs]
      have ht' := (lt_div_iff₀ (show 0 < ‖s‖ + 1 by positivity)).mp ht
      nlinarith [abs_nonneg t, norm_nonneg s]
    have hh := h (t • s) hn
    simp only [map_smul, smul_apply, smul_eq_mul,
      ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hh
    convert hh using 1
    ring
  have hpos := h s hs
  have hneg := h (-s) (by simpa using hs)
  have hT : T (fun _ => -s) = -T (fun _ => s) := by
    calc
      _ = T (fun _ => (-1 : ℝ) • s) := by simp
      _ = _ := by rw [ContinuousMultilinearMap.map_smul_univ]; norm_num
  simp only [map_neg, neg_apply, neg_neg, hT] at hneg
  rw [hg] at *
  linarith

/-- A zero minimum of a cubic model on a ball gives a zero minimum of its quadratic model.
The origin has value zero for both models, including at radius zero. -/
theorem isMinOn_quadratic_of_cubic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : E) (H : E →L[ℝ] E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h : IsMinOn (fun s => QuadraticSubproblem.quadratic g H s + T (fun _ => s) / 6)
      (closedBall 0 Δ) 0) :
    IsMinOn (QuadraticSubproblem.quadratic g H) (closedBall 0 Δ) 0 := by
  intro s hs
  change QuadraticSubproblem.quadratic g H 0 ≤ QuadraticSubproblem.quadratic g H s
  rw [QuadraticSubproblem.quadratic_zero]
  have hb := quadratic_nonneg_of_cubic_nonneg (innerSL ℝ g) ((innerSL ℝ).comp H) T hΔ
    (fun d hd => ?_) s (mem_closedBall_zero_iff.mp hs)
  · simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hb
    rw [real_inner_comm s (H s)] at hb
    simpa only [QuadraticSubproblem.quadratic, div_eq_mul_inv, one_mul, mul_comm] using hb
  · have hm := h (mem_closedBall_zero_iff.mpr hd)
    change QuadraticSubproblem.quadratic g H 0 + T (fun _ => 0) / 6 ≤
      QuadraticSubproblem.quadratic g H d + T (fun _ => d) / 6 at hm
    have hz : T (fun _ => 0) = 0 := T.map_coord_zero (0 : Fin 3) rfl
    simp only [QuadraticSubproblem.quadratic_zero, hz, zero_div, add_zero] at hm
    change 0 ≤ inner ℝ g d + inner ℝ (H d) d / 2 + T (fun _ => d) / 6
    rw [real_inner_comm d (H d)]
    simpa only [QuadraticSubproblem.quadratic, div_eq_mul_inv, one_mul, mul_comm] using hm

end Optimization
