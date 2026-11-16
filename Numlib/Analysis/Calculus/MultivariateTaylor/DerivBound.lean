/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# Norm bounds for the derivatives of a Taylor sum

Let $E$ and $F$ be real normed spaces, and let $D = (D_0, D_1, \dots)$ be a sequence of continuous
multilinear maps, where $D_i$ is $i$-linear from $E$ to $F$. The maps $D_i$ need not be symmetric.
Write $[s]^i$ for the tuple $(s, \dots, s)$ with $i$ entries. The **Taylor sum** of degree $p$ is
$T_p(s) = \sum_{i=0}^{p} \frac{1}{i!} D_i [s]^i$. This module proves that its $\ell$-th derivative
satisfies
$$\|\nabla^\ell T_p(s)\| \le \sum_{i=\ell}^{p} \frac{\|D_i\| \, \|s\|^{i-\ell}}{(i-\ell)!}.$$
For symmetric data this follows from the exact formula (A.11) of [cartis2022evaluation], but the
bound needs no symmetry.

The derivative of $T_p$ is linear in the data $D$. Hence the bound also applies to the difference of
two Taylor sums, as in the estimates (13.1.48)–(13.1.50) for inexact models and in the proof of
Lemma 12.2.7 of [cartis2022evaluation].

## Main results

* `ContinuousMultilinearMap.norm_iteratedFDeriv_comp_diagonal_le`: for an $n$-linear map $A$,
  $\|\nabla^\ell (y \mapsto A[y]^n)(s)\| \le n(n-1)\cdots(n-\ell+1) \, \|A\| \, \|s\|^{n-\ell}$.
* `FormalMultilinearSeries.iteratedFDeriv_taylorSum_sub`: the derivatives of the Taylor sum are
  linear in the data.
* `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le`: the bound above.
* `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_two_le`: for $p = 2$,
  $\|\nabla^m T_2(s)\| \le 3\kappa(1 + \rho)^2$ when $\|D_i\| \le \kappa$ and $\|s\| \le \rho$.
* `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le_three_mul`:
  $\|\nabla^\ell T_p(s)\| \le 3L$ for $\|s\| \le 1$ when $\|D_i\| \le L$ for $\ell \le i \le p$.
* `FormalMultilinearSeries.taylorSum_add_eq_taylorPolynomial`: a Taylor sum is its own Taylor
  polynomial at every point.

## Implementation notes

* The data $D$ is a `FormalMultilinearSeries ℝ E F`, and $T_p$ is
  `FormalMultilinearSeries.taylorSum`. Derivatives are `iteratedFDeriv`, with Mathlib's operator
  norm on continuous multilinear maps.
-/

open Finset
open scoped Nat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The diagonal embedding $y \mapsto (y, \dots, y)$ of $E$ into $E^n$ has operator norm at most
$1$. -/
theorem ContinuousLinearMap.norm_pi_id_le_one (n : ℕ) :
    ‖ContinuousLinearMap.pi (fun _ : Fin n => ContinuousLinearMap.id ℝ E)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun _ => le_rfl

/-- **Derivatives of a multilinear map on the diagonal.** Let $A \colon E^n \to F$ be a continuous
$n$-linear map, let $\ell \in \mathbb{N}$ and let $s \in E$. Then the $\ell$-th derivative of
$y \mapsto A(y, \dots, y)$ at $s$ satisfies
$$\|\nabla^\ell (y \mapsto A[y]^n)(s)\| \le n(n-1)\cdots(n-\ell+1) \, \|A\| \, \|s\|^{n-\ell}.$$

The map $A$ need not be symmetric. The factor $n(n-1)\cdots(n-\ell+1)$ is
`Nat.descFactorial n ℓ`, which is $0$ for $\ell > n$; then the derivative vanishes. The exponent
$n - \ell$ is truncated subtraction of natural numbers. -/
theorem ContinuousMultilinearMap.norm_iteratedFDeriv_comp_diagonal_le {n : ℕ}
    (A : E [×n]→L[ℝ] F) (ℓ : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ ℓ (fun y => A (fun _ => y)) s‖ ≤
      (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖s‖ ^ (n - ℓ) := by
  let g : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E
  have hg : ‖g‖ ≤ 1 := ContinuousLinearMap.norm_pi_id_le_one n
  have hgs : ‖g s‖ ≤ ‖s‖ := by simpa using g.le_of_opNorm_le hg s
  change ‖iteratedFDeriv ℝ ℓ (A ∘ g) s‖ ≤ _
  rw [g.iteratedFDeriv_comp_right A.contDiff s (i := ℓ) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin ℓ, ‖g‖ ≤ 1 := by
    simpa using pow_le_one₀ (norm_nonneg g) hg
  calc ‖iteratedFDeriv ℝ ℓ A (g s)‖ * ∏ _i : Fin ℓ, ‖g‖
      ≤ ‖iteratedFDeriv ℝ ℓ A (g s)‖ * 1 := by gcongr
    _ ≤ (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖g s‖ ^ (n - ℓ) := by
      simpa using A.norm_iteratedFDeriv_le ℓ (g s)
    _ ≤ (n.descFactorial ℓ : ℝ) * ‖A‖ * ‖s‖ ^ (n - ℓ) := by gcongr

namespace FormalMultilinearSeries

variable (D D' : FormalMultilinearSeries ℝ E F) (p : ℕ)

/-- The derivatives of a Taylor sum are linear in the data: for two data sequences $D$ and $D'$,
every $\ell$ and every $s \in E$,
$$\nabla^\ell T_p^{D - D'}(s) = \nabla^\ell T_p^{D}(s) - \nabla^\ell T_p^{D'}(s),$$
where $T_p^D$ is the Taylor sum of degree $p$ of $D$.

This lets the bound `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le` estimate the
difference of two Taylor models. -/
theorem iteratedFDeriv_taylorSum_sub (ℓ : ℕ) (s : E) :
    iteratedFDeriv ℝ ℓ ((D - D').taylorSum p) s =
      iteratedFDeriv ℝ ℓ (D.taylorSum p) s - iteratedFDeriv ℝ ℓ (D'.taylorSum p) s := by
  have h : (D - D').taylorSum p = D.taylorSum p - D'.taylorSum p :=
    funext fun s => taylorSum_sub D D' p s
  rw [h, iteratedFDeriv_sub_apply (D.contDiff_taylorSum p).contDiffAt
    (D'.contDiff_taylorSum p).contDiffAt]

/-- **Derivative bound for Taylor sums.** Let $D$ be any data sequence, not necessarily symmetric,
and let $p, \ell \in \mathbb{N}$ and $s \in E$. Then
$$\|\nabla^\ell T_p(s)\| \le \sum_{i=\ell}^{p} \frac{\|D_i\| \, \|s\|^{i-\ell}}{(i-\ell)!}.$$

For symmetric data the bound follows from formula (A.11) of [cartis2022evaluation]. It is used
in the proof of Lemma 12.2.7 and in (13.1.48) of [cartis2022evaluation]. The sum is empty, so
the bound is $0$, when $\ell > p$. -/
theorem norm_iteratedFDeriv_taylorSum_le (ℓ : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖ ≤
      ∑ i ∈ Icc ℓ p, ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
  have hfun : D.taylorSum p = fun y => ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • D i (fun _ => y) := rfl
  rw [hfun, iteratedFDeriv_fun_sum_apply fun i _ =>
    ((D.contDiff_apply_diagonal i).const_smul _).contDiffAt]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ range (p + 1),
      ‖iteratedFDeriv ℝ ℓ (fun y => (i ! : ℝ)⁻¹ • D i (fun _ => y)) s‖ ≤
        if ℓ ≤ i then ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) else 0 := by
    intro i _
    rw [iteratedFDeriv_const_smul_apply' (D.contDiff_apply_diagonal i).contDiffAt, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left ((D i).norm_iteratedFDeriv_comp_diagonal_le ℓ s)
      (by positivity)).trans (le_of_eq ?_)
    split_ifs with h
    · have hf := Nat.factorial_mul_descFactorial h
      have : ((i - ℓ)! : ℝ) ≠ 0 := by positivity
      rw [← hf, Nat.cast_mul]
      have : (i.descFactorial ℓ : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.descFactorial_pos.2 h).ne'
      field_simp
    · simp [Nat.descFactorial_eq_zero_iff_lt.2 (not_le.1 h)]
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_range, mem_Icc]
  omega


/-- **Quadratic Taylor sums on a ball.** Let $\kappa, \rho \ge 0$, and suppose that
$\|D_i\| \le \kappa$ for $i \le 2$. Then for every $m \in \mathbb{N}$ and every $s$ with
$\|s\| \le \rho$,
$$\|\nabla^m T_2(s)\| \le 3\kappa(1 + \rho)^2.$$
-/
theorem norm_iteratedFDeriv_taylorSum_two_le {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ)
    (hD : ∀ i ≤ 2, ‖D i‖ ≤ κ) (m : ℕ) {s : E} (hs : ‖s‖ ≤ ρ) :
    ‖iteratedFDeriv ℝ m (D.taylorSum 2) s‖ ≤ 3 * κ * (1 + ρ) ^ 2 := by
  refine (D.norm_iteratedFDeriv_taylorSum_le 2 m s).trans ?_
  have hterm : ∀ i ∈ Icc m 2, ‖D i‖ * ‖s‖ ^ (i - m) / ((i - m)! : ℝ) ≤ κ * (1 + ρ) ^ 2 := by
    intro i hi
    obtain ⟨hmi, hi2⟩ := mem_Icc.1 hi
    have h1 : ‖s‖ ^ (i - m) ≤ (1 + ρ) ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg s) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    have h2 : (1 : ℝ) ≤ ((i - m)! : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
    calc ‖D i‖ * ‖s‖ ^ (i - m) / ((i - m)! : ℝ) ≤ ‖D i‖ * ‖s‖ ^ (i - m) :=
          div_le_self (by positivity) h2
      _ ≤ κ * (1 + ρ) ^ 2 := mul_le_mul (hD i hi2) h1 (by positivity) hκ
  refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul, Nat.card_Icc]
  have : ((2 + 1 - m : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : 2 + 1 - m ≤ 3)
  have : 0 ≤ κ * (1 + ρ) ^ 2 := by positivity
  nlinarith

/-- The $p$-th derivative of a Taylor sum of degree $p$ is constant on $E$, so it is Lipschitz
continuous on $E$ with constant $0$ (`IteratedFDerivLipschitzOn`). -/
theorem iteratedFDerivLipschitzOn_taylorSum (p : ℕ) :
    IteratedFDerivLipschitzOn (D.taylorSum p) p 0 Set.univ :=
  iteratedFDerivLipschitzOn_of_norm_le convex_univ
    (fun _ _ => (D.contDiff_taylorSum p).contDiffAt) fun x _ => by
      refine (D.norm_iteratedFDeriv_taylorSum_le p (p + 1) x).trans_eq ?_
      rw [Icc_eq_empty (by omega), sum_empty]

/-- **A Taylor sum is its own Taylor polynomial.** For all $s, d \in E$,
$$T_p(s + d) = T_{T_p, p}(s, d),$$
where $T_{T_p,p}(s, \cdot)$ is the Taylor polynomial (`taylorPolynomial`) of degree $p$ of the
function $T_p$ at $s$. The data $D$ need not be symmetric. -/
theorem taylorSum_add_eq_taylorPolynomial (p : ℕ) (s d : E) :
    D.taylorSum p (s + d) = taylorPolynomial (D.taylorSum p) p s d := by
  have h := norm_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => (D.contDiff_taylorSum p).contDiffAt) (D.iteratedFDerivLipschitzOn_taylorSum p)
    (Set.mem_univ s) (Set.mem_univ (s + d))
  rw [zero_div, zero_mul] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- **Derivatives of a Taylor sum on the unit ball.** Let $\ell, p \in \mathbb{N}$ and $L \ge 0$,
and suppose that $\|D_i\| \le L$ for $\ell \le i \le p$. Then for every $s$ with $\|s\| \le 1$,
$$\|\nabla^\ell T_p(s)\| \le 3L.$$

This is the estimate in the proof of Lemma 12.2.7 of [cartis2022evaluation], together with
(A.33). It follows from `FormalMultilinearSeries.norm_iteratedFDeriv_taylorSum_le` and the bound
$\sum_{k=0}^{N} \|s\|^k / k! \le 1 + 2\|s\|$ for $\|s\| \le 1$. -/
theorem norm_iteratedFDeriv_taylorSum_le_three_mul {ℓ p : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ i ∈ Icc ℓ p, ‖D i‖ ≤ L) {s : E} (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖ ≤ 3 * L := by
  calc ‖iteratedFDeriv ℝ ℓ (D.taylorSum p) s‖
      ≤ ∑ i ∈ Icc ℓ p, ‖D i‖ * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) :=
        D.norm_iteratedFDeriv_taylorSum_le p ℓ s
    _ ≤ ∑ i ∈ Icc ℓ p, L * (‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)) :=
        sum_le_sum fun i hi => by rw [mul_div_assoc]; gcongr; exact hD i hi
    _ = L * ∑ i ∈ Icc ℓ p, ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := (mul_sum _ _ _).symm
    _ ≤ L * (1 + 2 * ‖s‖) := by
        gcongr; exact sum_pow_div_factorial_le_one_add_two_mul (norm_nonneg _) hs ℓ p
    _ ≤ 3 * L := by nlinarith


end FormalMultilinearSeries
