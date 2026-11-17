/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Mathlib.Order.Interval.Set.Monotone

/-!
# Error and direction identities for conjugate gradients

The one-step energy identity telescopes on any interval of conjugate-gradient steps.
Before the residual vanishes, the directions have explicit expansions in the orthogonal
residuals and their Euclidean inner products can be recovered from the residual norms.

## Main results

* `CG.energyNorm_error_sq_sub_eq_sum_Ico`: the energy decrement from step $k$ to
  step $n$ sums the individual decrements.
* `CG.direction_eq_sum_residual`: a direction is a linear combination of the residuals
  through its own step, with coefficients given by squared residual norm ratios.
* `CG.norm_direction_sq_eq_sum` and `CG.inner_direction_eq_scale`: direction
  norms and inner products follow from residual orthogonality.
-/

open Finset Krylov

namespace CG

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} (b x₀ : E)

local notation "r[" j "]" => State.r (iterate A b x₀ j)
local notation "p[" j "]" => State.p (iterate A b x₀ j)
local notation "x[" j "]" => State.x (iterate A b x₀ j)
local notation "a[" j "]" => alpha A (iterate A b x₀ j)

/-- For symmetric coercive $A$ with $Ax^*=b$ and $k \le n$, the conjugate-gradient iterates
satisfy
$$\|x^* - x_k\|_A^2 = \sum_{j=k}^{n-1} \operatorname{Re}(\alpha_j)\|r_j\|^2
  + \|x^* - x_n\|_A^2.$$ -/
theorem energyNorm_error_sq_sub_eq_sum_Ico (hA : A.IsSymmetricCoercive) {xstar : E}
    (hstar : A xstar = b) {k n : ℕ} (hkn : k ≤ n) :
    energyNorm A (xstar - x[k]) ^ 2 =
      (∑ j ∈ Ico k n, RCLike.re a[j] * ‖r[j]‖ ^ 2) + energyNorm A (xstar - x[n]) ^ 2 := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_Ico_succ_top hkn]
    linarith [energyNorm_error_sq_sub b x₀ hA hstar n]

private theorem beta_eq_ofReal_ratio (k : ℕ) :
    beta A (iterate A b x₀ k) = ((‖r[k + 1]‖ ^ 2 / ‖r[k]‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [beta_iterate, RCLike.ofReal_div, RCLike.ofReal_pow, inner_self_eq_norm_sq_to_K]

private theorem residual_ne_zero_of_le {i j : ℕ} (hij : i ≤ j) (hr : r[j] ≠ 0) :
    r[i] ≠ 0 := by
  intro hi
  exact hr ((congrArg State.r (iterate_eq_of_residual_eq_zero' A b x₀ hi j hij)).trans hi)

/-- For a conjugate-gradient run whose residual at step $n$ is nonzero, its direction is
$$p_n=\sum_{j=0}^n\frac{\|r_n\|^2}{\|r_j\|^2}r_j.$$ -/
theorem direction_eq_sum_residual {n : ℕ} (hr : r[n] ≠ 0) :
    p[n] = ∑ j ∈ range (n + 1), ((‖r[n]‖ ^ 2 / ‖r[j]‖ ^ 2 : ℝ) : 𝕜) • r[j] := by
  induction n with
  | zero =>
    rw [direction_zero, sum_range_one, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hr))]
    simp
  | succ n ih =>
    have hn := residual_ne_zero_of_le b x₀ (Nat.le_succ n) hr
    rw [iterate_succ_p, beta_eq_ofReal_ratio, ih hn, smul_sum]
    conv_rhs => rw [sum_range_succ]
    have hself : ((‖r[n + 1]‖ ^ 2 / ‖r[n + 1]‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      simp [hr]
    rw [hself, one_smul, add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← RCLike.ofReal_mul,
      div_mul_div_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))]

/-- If $A$ is symmetric coercive and $r_n \ne 0$, the Euclidean norm of the conjugate-gradient
direction satisfies
$$\|p_n\|^2 = \|r_n\|^4 \sum_{j=0}^n \|r_j\|^{-2}.$$ -/
theorem norm_direction_sq_eq_sum (hA : A.IsSymmetricCoercive) {n : ℕ} (hr : r[n] ≠ 0) :
    ‖p[n]‖ ^ 2 = ‖r[n]‖ ^ 4 * ∑ j ∈ range (n + 1), (‖r[j]‖ ^ 2)⁻¹ := by
  calc
    ‖p[n]‖ ^ 2 = RCLike.re (inner 𝕜 p[n] p[n]) := (inner_self_eq_norm_sq _).symm
    _ = RCLike.re (inner 𝕜
        (∑ j ∈ range (n + 1), ((‖r[n]‖ ^ 2 / ‖r[j]‖ ^ 2 : ℝ) : 𝕜) • r[j]) p[n]) :=
      congrArg (fun u => RCLike.re (inner 𝕜 u p[n])) (direction_eq_sum_residual b x₀ hr)
    _ = ‖r[n]‖ ^ 4 * ∑ j ∈ range (n + 1), (‖r[j]‖ ^ 2)⁻¹ := by
      rw [sum_inner, map_sum, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [inner_smul_left, RCLike.conj_ofReal,
        inner_residual_direction_eq b x₀ hA (Nat.le_of_lt_succ (mem_range.mp hj)),
        ← RCLike.ofReal_mul, RCLike.ofReal_re]
      ring

/-- If $A$ is symmetric coercive, $r_n \ne 0$ and $n \le \ell$, then the conjugate-gradient
directions satisfy
$$\langle p_n,p_\ell\rangle
  =\|p_n\|^2\frac{\|r_\ell\|^2}{\|r_n\|^2}.$$ -/
theorem inner_direction_eq_scale (hA : A.IsSymmetricCoercive) {n ℓ : ℕ} (hnℓ : n ≤ ℓ)
    (hr : r[n] ≠ 0) :
    inner 𝕜 p[n] p[ℓ] = ((‖p[n]‖ ^ 2 * (‖r[ℓ]‖ ^ 2 / ‖r[n]‖ ^ 2) : ℝ) : 𝕜) := by
  conv_lhs => rw [direction_eq_sum_residual b x₀ hr]
  rw [sum_inner, norm_direction_sq_eq_sum b x₀ hA hr, mul_right_comm, mul_sum,
    RCLike.ofReal_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [inner_smul_left, RCLike.conj_ofReal,
    inner_residual_direction_eq b x₀ hA ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hnℓ),
    ← RCLike.ofReal_mul]
  have hne : ‖r[n]‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  congr 1
  field_simp


private theorem iterate_sub_eq_sum_steps {k n : ℕ} (hkn : k ≤ n) :
    x[n] - x[k] = ∑ j ∈ Ico k n, a[j] • p[j] := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [iterate_succ_x, sum_Ico_succ_top hkn, ← ih]
    abel

private theorem alpha_eq_ofReal_energy (hA : A.IsSymmetricCoercive) (n : ℕ) :
    a[n] = ((‖r[n]‖ ^ 2 / energyNorm A p[n] ^ 2 : ℝ) : 𝕜) := by
  rw [hA.energyNorm_sq, RCLike.ofReal_div, RCLike.ofReal_pow,
    ← inner_self_eq_norm_sq_to_K, hA.isSymmetric.coe_re_inner_apply_self, alpha]

private theorem re_inner_error_direction (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {xstar : E} (hstar : A xstar = b)
    {n : ℕ} (hn : n < grade A (b - A x₀)) :
    RCLike.re (inner 𝕜 (xstar - x[n + 1]) p[n]) =
      (‖p[n]‖ ^ 2 / ‖r[n]‖ ^ 2) * energyNorm A (xstar - x[n + 1]) ^ 2 := by
  let d := grade A (b - A x₀)
  have hrn := residual_ne_zero_of_lt_grade b x₀ hn
  have hdeq : xstar = x[d] := by
    have hh := residual_eq_zero_of_grade_le b x₀ hA (show grade A (b - A x₀) ≤ d from le_rfl)
    rw [residual_eq, sub_eq_zero] at hh
    exact hA.isCoercive.injective (hstar.trans hh)
  have hx : xstar - x[n + 1] = ∑ j ∈ Ico (n + 1) d, a[j] • p[j] := by
    rw [hdeq, iterate_sub_eq_sum_steps b x₀ (show n + 1 ≤ d from Nat.succ_le_of_lt hn)]
  conv_lhs => rw [hx, sum_inner, map_sum]
  rw [energyNorm_error_sq_eq_sum b x₀ hA hstar, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hnj : n ≤ j := (Nat.le_succ n).trans (mem_Ico.mp hj).1
  rw [inner_smul_left, ← inner_conj_symm p[j] p[n], inner_direction_eq_scale b x₀ hA hnj hrn,
    alpha_eq_ofReal_energy b x₀ hA j, RCLike.conj_ofReal, RCLike.conj_ofReal,
    ← RCLike.ofReal_mul, RCLike.ofReal_re, RCLike.ofReal_re]
  ring

/-- For symmetric coercive $A$, $Ax^*=b$, and finite Krylov grade $d$, the CG errors
$e_j=x^*-x_j$ satisfy, for $n<d$,
$$\frac{\|e_n\|^2-\|e_{n+1}\|^2}{\|p_n\|^2}
  =\frac{\|e_n\|_A^2+\|e_{n+1}\|_A^2}{\|p_n\|_A^2}.$$ -/
theorem norm_error_sq_sub_div_eq (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {xstar : E} (hstar : A xstar = b)
    {n : ℕ} (hn : n < grade A (b - A x₀)) :
    (‖xstar - x[n]‖ ^ 2 - ‖xstar - x[n + 1]‖ ^ 2) / ‖p[n]‖ ^ 2 =
      (energyNorm A (xstar - x[n]) ^ 2 + energyNorm A (xstar - x[n + 1]) ^ 2) /
        energyNorm A p[n] ^ 2 := by
  have hr := residual_ne_zero_of_lt_grade b x₀ hn
  have hApos : 0 < energyNorm A p[n] ^ 2 := by
    rw [hA.energyNorm_sq]
    exact re_inner_apply_direction_pos b x₀ hA hr
  have hp : p[n] ≠ 0 := by
    intro hp
    simp [hp, energyNorm] at hApos
  have hp' : ‖p[n]‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
  have hr' : ‖r[n]‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hr)
  let q := ‖r[n]‖ ^ 2 / energyNorm A p[n] ^ 2
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hApos.le
  have hα : a[n] = (q : 𝕜) := alpha_eq_ofReal_energy b x₀ hA n
  have hexp : xstar - x[n] = (xstar - x[n + 1]) + a[n] • p[n] := by
    rw [iterate_succ_x]
    abel
  have hdiff :
      ‖xstar - x[n]‖ ^ 2 - ‖xstar - x[n + 1]‖ ^ 2 =
        2 * (q * ((‖p[n]‖ ^ 2 / ‖r[n]‖ ^ 2) * energyNorm A (xstar - x[n + 1]) ^ 2)) +
          (q * ‖p[n]‖) ^ 2 := by
    conv_lhs =>
      lhs
      rw [hexp, norm_add_sq (𝕜 := 𝕜), inner_smul_right, norm_smul, hα, RCLike.norm_ofReal,
        abs_of_nonneg hq, RCLike.re_ofReal_mul,
        re_inner_error_direction b x₀ hA hstar hn]
    ring
  have hstep := energyNorm_error_sq_sub b x₀ hA hstar n
  rw [hα, RCLike.ofReal_re] at hstep
  rw [hdiff, show energyNorm A (xstar - x[n]) ^ 2 =
    q * ‖r[n]‖ ^ 2 + energyNorm A (xstar - x[n + 1]) ^ 2 by linarith]
  dsimp only [q]
  have hAne : energyNorm A p[n] ≠ 0 := fun h => hApos.ne' (by simp [h])
  field_simp [hp', hr', hAne, hApos.ne']
  ring

/-- For symmetric coercive $A$, $Ax^*=b$ and finite Krylov grade $d$, the Euclidean norms of the
CG errors are strictly decreasing over steps $0,\dots,d$. -/
theorem norm_error_strictAntiOn (hA : A.IsSymmetricCoercive)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {xstar : E} (hstar : A xstar = b) :
    StrictAntiOn (fun n => ‖xstar - x[n]‖) (Set.Iic (grade A (b - A x₀))) := by
  refine strictAntiOn_Iic_of_succ_lt fun n hn => ?_
  change ‖xstar - x[n + 1]‖ < ‖xstar - x[n]‖
  have hr := residual_ne_zero_of_lt_grade b x₀ hn
  have he : xstar - x[n] ≠ 0 := by
    intro he
    rw [sub_eq_zero] at he
    apply hr
    rw [residual_eq, ← he, hstar, sub_self]
  have hxpos : 0 < energyNorm A (xstar - x[n]) ^ 2 := by
    rw [hA.energyNorm_sq]
    exact hA.isCoercive.inner_self_pos he
  have hApos : 0 < energyNorm A p[n] ^ 2 := by
    rw [hA.energyNorm_sq]
    exact re_inner_apply_direction_pos b x₀ hA hr
  have h := norm_error_sq_sub_div_eq b x₀ hA hstar hn
  have hpos : 0 < (‖xstar - x[n]‖ ^ 2 - ‖xstar - x[n + 1]‖ ^ 2) / ‖p[n]‖ ^ 2 := by
    rw [h]
    exact div_pos (add_pos_of_pos_of_nonneg hxpos (sq_nonneg _)) hApos
  have hp0 : 0 < ‖p[n]‖ ^ 2 := by
    by_contra! hn0
    rw [le_antisymm hn0 (sq_nonneg _), div_zero] at hpos
    exact (lt_irrefl _ hpos)
  have hnum := (div_pos_iff_of_pos_right hp0).1 hpos
  nlinarith [norm_nonneg (xstar - x[n]), norm_nonneg (xstar - x[n + 1])]

end CG
