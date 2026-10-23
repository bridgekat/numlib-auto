/-
Upstreaming candidate: Peano's finite Taylor remainder, derived from exactly C^k regularity.
Natural home: Mathlib.Analysis.Calculus.Taylor, alongside the one-dimensional Peano theorem.
-/
import Numlib.Analysis.Calculus.Taylor.ScalarRemainder
import Numlib.Analysis.Calculus.TaylorModel
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-!
# Peano remainder for genuine multivariate Taylor polynomials

A scalar Lagrange remainder along each affine line, with its highest Taylor term
subtracted, is bounded by variation of the actual highest derivative. Continuity of that
derivative yields a uniform small-ball remainder estimate and the Peano little-o
statement. The regularity assumption is exactly `C^k`, with no extra derivative.
-/

open Set
open scoped BigOperators

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Derivatives of an affine-line restriction are diagonal Fréchet derivatives. -/
theorem iteratedDeriv_affineLine {f : E → ℝ} {k : ℕ} (hf : ContDiff ℝ k f)
    (x s : E) (t : ℝ) {i : ℕ} (hi : i ≤ k) :
    iteratedDeriv i (fun t : ℝ => f (x + t • s)) t =
      iteratedFDeriv ℝ i f (x + t • s) (fun _ => s) := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ s
  have hg : ContDiff ℝ k (fun y : E => f (x + y)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ i ((fun y : E => f (x + y)) ∘ L) t (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_right hg t (by exact_mod_cast hi)]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, iteratedFDeriv_comp_add_left]
/-- The Taylor remainder is controlled by variation of the highest derivative along a segment. -/
theorem abs_sub_eval_le_of_derivative_variation {f : E → ℝ} {p : ℕ}
    (hf : ContDiff ℝ (p + 1) f) (x s : E) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (p + 1) f (x + t • s) - iteratedFDeriv ℝ (p + 1) f x‖ ≤ M) :
    |f (x + s) - eval f (p + 1) x s| ≤ M * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  have hg : ContDiff ℝ (p + 1) (fun t : ℝ => f (x + t • s)) := by fun_prop
  obtain ⟨ξ,hξ,heq⟩ := exists_sub_sum_eq_iteratedDeriv_mul
    (a := 0) (b := 1) (hg.contDiffAt.of_le (by exact_mod_cast Nat.le_succ p)) hg.contDiffOn
  have hξ' : ξ ∈ Icc (0 : ℝ) 1 := by simpa using hξ
  have hsum : (∑ i ∈ Finset.range (p + 1), (1 - 0 : ℝ)^i / i.factorial *
      iteratedDeriv i (fun t : ℝ => f (x + t • s)) 0) = eval f p x s := by
    rw [eval_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_affineLine hf x s 0 (Nat.le_of_lt (Finset.mem_range.mp hi))]
    simp [smul_eq_mul, div_eq_mul_inv]
  rw [hsum, iteratedDeriv_affineLine hf x s ξ le_rfl] at heq
  simp only [one_smul, sub_zero, one_pow, mul_one] at heq
  have hexp : eval f (p + 1) x s = eval f p x s +
      iteratedFDeriv ℝ (p + 1) f x (fun _ => s) / (p + 1).factorial := by
    rw [eval_eq_sum, eval_eq_sum, Finset.sum_range_succ]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hdiff : f (x + s) - eval f (p + 1) x s =
      (iteratedFDeriv ℝ (p + 1) f (x + ξ • s) - iteratedFDeriv ℝ (p + 1) f x)
        (fun _ => s) / (p + 1).factorial := by
    rw [hexp]
    change f (x + s) - (eval f p x s +
      iteratedFDeriv ℝ (p + 1) f x (fun _ => s) / (p + 1).factorial) =
      (iteratedFDeriv ℝ (p + 1) f (x + ξ • s) (fun _ => s) -
        iteratedFDeriv ℝ (p + 1) f x (fun _ => s)) / (p + 1).factorial
    rw [sub_div]
    linarith
  rw [hdiff, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p + 1).factorial)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmap : |(iteratedFDeriv ℝ (p + 1) f (x + ξ • s) - iteratedFDeriv ℝ (p + 1) f x)
      (fun _ => s)| ≤
      ‖iteratedFDeriv ℝ (p + 1) f (x + ξ • s) - iteratedFDeriv ℝ (p + 1) f x‖ *
        ‖s‖ ^ (p + 1) := by
    simpa [Real.norm_eq_abs] using
      (iteratedFDeriv ℝ (p + 1) f (x + ξ • s) - iteratedFDeriv ℝ (p + 1) f x).le_opNorm (fun _ => s)
  exact hmap.trans (mul_le_mul_of_nonneg_right (hM ξ hξ') (by positivity))
end TaylorModel
namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A `C^k` function has a uniform degree-`k` Taylor remainder bound on a sufficiently
small ball. Only continuity of the actual `k`-th derivative is needed beyond `C^k`. -/
theorem exists_pos_abs_sub_eval_le {f : E → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : ContDiff ℝ k f) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ s : E, ‖s‖ < r → |f (x + s) - eval f k x s| ≤ ε * ‖s‖ ^ k := by
  cases k with
  | zero => omega
  | succ p =>
    have hc : ContinuousAt (iteratedFDeriv ℝ (p + 1) f) x :=
      (hf.continuous_iteratedFDeriv le_rfl).continuousAt
    obtain ⟨r,hr,hclose⟩ := Metric.continuousAt_iff.1 hc
      (ε * ((p + 1).factorial : ℝ)) (by positivity)
    refine ⟨r,hr,?_⟩
    intro s hs
    have hM : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (p + 1) f (x + t • s) - iteratedFDeriv ℝ (p + 1) f x‖ ≤
          ε * ((p + 1).factorial : ℝ) := by
      intro t ht
      have hdist : dist (x + t • s) x < r := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact (mul_le_of_le_one_left (norm_nonneg s) ht.2).trans_lt hs
      simpa [dist_eq_norm] using (hclose hdist).le
    have hb := abs_sub_eval_le_of_derivative_variation hf x s hM
    convert hb using 1
    field_simp
/-- Peano's Taylor remainder with the actual derivative tensors, requiring exactly `C^k`. -/
theorem isLittleO_sub_eval {f : E → ℝ} {k : ℕ} (hk : 0 < k)
    (hf : ContDiff ℝ k f) (x : E) :
    (fun s => f (x + s) - eval f k x s) =o[nhds 0] (fun s : E => ‖s‖ ^ k) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r,hr,hbound⟩ := exists_pos_abs_sub_eval_le hk hf x hε
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with s hs
  have hs' : ‖s‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hs
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg s) k)] using hbound s hs'
end TaylorModel
