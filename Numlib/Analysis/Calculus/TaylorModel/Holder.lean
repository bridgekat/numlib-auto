/-
Upstreaming candidate: sharp Holder bounds for finite Taylor remainders on convex sets.
Natural home: Mathlib.Analysis.Calculus.Taylor.
-/
import Numlib.Analysis.Calculus.TaylorSegment
import Numlib.Analysis.Calculus.Taylor.ScalarRemainder
import Numlib.Analysis.Calculus.TaylorModel
import Numlib.Analysis.SpecialFunctions.Integrals.BetaReal

/-!
# Sharp Hölder bounds for Taylor value remainders

The genuine Fréchet Taylor polynomial has a sharp remainder estimate when its highest
derivative is Hölder continuous on a convex set. Smoothness is required only on an open
neighborhood of that set. The proof restricts to the affine segment, applies the exact
integral variation formula, and evaluates the real beta kernel. Zero increments and zero
Hölder exponent are included. No derivative of order higher than the Taylor degree is used.
-/

open Set intervalIntegral
open scoped BigOperators

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- Ordinary derivatives on an affine line agree with diagonal Fréchet derivatives when
the original function is smooth on an open neighborhood. -/
theorem iteratedDeriv_affineLine_of_contDiffOn {f : E → F} {k i : ℕ} {D : Set E}
    (hD : IsOpen D) (hf : ContDiffOn ℝ k f D) (hi : i ≤ k)
    (x s : E) (t : ℝ) (ht : x + t • s ∈ D) :
    iteratedDeriv i (fun t : ℝ => f (x + t • s)) t =
      iteratedFDeriv ℝ i f (x + t • s) (fun _ => s) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    have hU : IsOpen {u : ℝ | x + u • s ∈ D} :=
      hD.preimage (show Continuous (fun u : ℝ => x + u • s) by fun_prop)
    have heq : iteratedDeriv i (fun u : ℝ => f (x + u • s)) =ᶠ[nhds t]
        (fun u => iteratedFDeriv ℝ i f (x + u • s) (fun _ => s)) := by
      filter_upwards [hU.mem_nhds ht] with u hu
      exact ih (by omega) u hu
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (hasDerivAt_iteratedFDeriv_segment
      ((hf.contDiffAt (hD.mem_nhds ht)).of_le (by exact_mod_cast hi))).deriv
/-- The degree-`p + 1` Taylor value error is an integral of variation of the actual
`(p + 1)`-st derivative along the segment. -/
theorem sub_eval_eq_integral_variation {f : E → ℝ} {p : ℕ} {D : Set E}
    (hD : IsOpen D) (hf : ContDiffOn ℝ (p + 1) f D) (x s : E)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ D) :
    f (x + s) - eval f (p + 1) x s =
      1 / (p.factorial : ℝ) * ∫ t in (0 : ℝ)..1, (1 - t) ^ p *
        (iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
          iteratedFDeriv ℝ (p + 1) f x (fun _ => s)) := by
  have hg : ∀ t ∈ uIcc (0 : ℝ) 1,
      ContDiffAt ℝ (p + 1) (fun u : ℝ => f (x + u • s)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    exact (hf.contDiffAt (hD.mem_nhds (hpath t ht'))).comp t
      (contDiff_const.add (contDiff_id.smul_const s)).contDiffAt
  have hrem := sub_sum_eq_integral_iteratedDeriv_sub hg
  have hsum : (∑ i ∈ Finset.range (p + 2), (1 : ℝ) ^ i / i.factorial *
      iteratedDeriv i (fun u : ℝ => f (x + u • s)) 0) = eval f (p + 1) x s := by
    rw [eval_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_affineLine_of_contDiffOn hD hf
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) x s 0 (hpath 0 (by simp))]
    simp [smul_eq_mul, div_eq_mul_inv]
  simp only [one_smul] at hrem
  rw [hsum] at hrem
  rw [hrem]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  dsimp only
  rw [iteratedDeriv_affineLine_of_contDiffOn hD hf le_rfl x s t (hpath t ht'),
    iteratedDeriv_affineLine_of_contDiffOn hD hf le_rfl x s 0 (hpath 0 (by simp))]
  simp
end TaylorModel

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Sharp Hölder estimate for the value error of the degree-`p + 1` Taylor polynomial.
The exponent may be any nonnegative real number. -/
theorem abs_sub_eval_le_holder {f : E → ℝ} {p : ℕ} {C D : Set E}
    (hD : IsOpen D) (hCD : C ⊆ D) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ (p + 1) f D) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β)
    (hholder : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ (p + 1) f u - iteratedFDeriv ℝ (p + 1) f v‖ ≤ H * ‖u - v‖ ^ β)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - eval f (p + 1) x s| ≤
      H / Real.shiftedFactorial (p + 1) β * ‖s‖ ^ ((p + 1 : ℕ) + β) := by
  by_cases hs : s = 0
  · subst s
    simp only [add_zero, eval_zero, sub_self, abs_zero]
    exact mul_nonneg (div_nonneg hH (Real.shiftedFactorial_pos _ hβ).le)
      (Real.rpow_nonneg (by positivity) _)
  have hsnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ C := by
    intro t ht
    simpa using hC.add_smul_sub_mem hx hxs ht
  have hrem := sub_eval_eq_integral_variation hD hf x s (fun t ht => hCD (hpath t ht))
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(1 - t) ^ p * (iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
        iteratedFDeriv ℝ (p + 1) f x (fun _ => s))‖ ≤
      H * ‖s‖ ^ ((p + 1 : ℕ) + β) * (t ^ β * (1 - t) ^ p) := by
    intro t ht
    have happ : ‖iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
        iteratedFDeriv ℝ (p + 1) f x (fun _ => s)‖ ≤
        ‖iteratedFDeriv ℝ (p + 1) f (x + t • s) - iteratedFDeriv ℝ (p + 1) f x‖ *
          ‖s‖ ^ (p + 1) := by
      change ‖(iteratedFDeriv ℝ (p + 1) f (x + t • s) - iteratedFDeriv ℝ (p + 1) f x)
        (fun _ => s)‖ ≤ _
      simpa using (iteratedFDeriv ℝ (p + 1) f (x + t • s) -
        iteratedFDeriv ℝ (p + 1) f x).le_opNorm (fun _ => s)
    have hh := hholder (x + t • s) (hpath t ht) x hx
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
      Real.mul_rpow ht.1 (norm_nonneg s)] at hh
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) p), Real.rpow_add hsnorm,
      Real.rpow_natCast]
    calc (1 - t) ^ p * ‖iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
          iteratedFDeriv ℝ (p + 1) f x (fun _ => s)‖ ≤
        (1 - t) ^ p *
          (‖iteratedFDeriv ℝ (p + 1) f (x + t • s) - iteratedFDeriv ℝ (p + 1) f x‖ *
            ‖s‖ ^ (p + 1)) := by
          exact mul_le_mul_of_nonneg_left happ (pow_nonneg (sub_nonneg.mpr ht.2) p)
      _ ≤ (1 - t) ^ p * ((H * (t ^ β * ‖s‖ ^ β)) * ‖s‖ ^ (p + 1)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
            (pow_nonneg (norm_nonneg s) _)) (pow_nonneg (sub_nonneg.mpr ht.2) p)
      _ = _ := by ring
  have hcont : Continuous (fun t : ℝ =>
      H * ‖s‖ ^ ((p + 1 : ℕ) + β) * (t ^ β * (1 - t) ^ p)) :=
    continuous_const.mul ((Real.continuous_rpow_const hβ).mul (by fun_prop))
  have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
    (MeasureTheory.ae_of_all _ (fun t ht => hpoint t ⟨ht.1.le, ht.2⟩)) (hcont.intervalIntegrable 0 1)
  rw [hrem, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p.factorial : ℝ))]
  have hint' : |∫ t in (0 : ℝ)..1, (1 - t) ^ p *
      (iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
        iteratedFDeriv ℝ (p + 1) f x (fun _ => s))| ≤
      ∫ t in (0 : ℝ)..1, H * ‖s‖ ^ ((p + 1 : ℕ) + β) * (t ^ β * (1 - t) ^ p) := by
    simpa [Real.norm_eq_abs] using hint
  calc 1 / (p.factorial : ℝ) * |∫ t in (0 : ℝ)..1, (1 - t) ^ p *
        (iteratedFDeriv ℝ (p + 1) f (x + t • s) (fun _ => s) -
          iteratedFDeriv ℝ (p + 1) f x (fun _ => s))| ≤
      1 / (p.factorial : ℝ) *
        ∫ t in (0 : ℝ)..1, H * ‖s‖ ^ ((p + 1 : ℕ) + β) * (t ^ β * (1 - t) ^ p) := by
        gcongr
    _ = H / Real.shiftedFactorial (p + 1) β * ‖s‖ ^ ((p + 1 : ℕ) + β) := by
      rw [intervalIntegral.integral_const_mul, Real.integral_rpow_mul_one_sub_pow p hβ]
      field_simp
end TaylorModel

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Sharp Lipschitz estimate for the value error, with denominator `(p + 2)!`. -/
theorem abs_sub_eval_le_lipschitz {f : E → ℝ} {p : ℕ} {C D : Set E}
    (hD : IsOpen D) (hCD : C ⊆ D) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ (p + 1) f D) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u ∈ C, ∀ v ∈ C,
      ‖iteratedFDeriv ℝ (p + 1) f u - iteratedFDeriv ℝ (p + 1) f v‖ ≤ L * ‖u - v‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - eval f (p + 1) x s| ≤ L * ‖s‖ ^ (p + 2) / (p + 2).factorial := by
  have h := abs_sub_eval_le_holder hD hCD hC hf hL (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using hlip) hx hxs
  simpa only [Real.shiftedFactorial_one, show (p + 1 : ℕ) + (1 : ℝ) = ((p + 2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, div_mul_eq_mul_div] using h
end TaylorModel
