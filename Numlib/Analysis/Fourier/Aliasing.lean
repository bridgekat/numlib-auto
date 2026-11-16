/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Sobolev.Periodic
import Numlib.Topology.Algebra.InfiniteSum.Group

/-!
# Aliasing: the error of the discrete Fourier coefficients

Let $\varphi = \sum_m a_m e^{imx}$ be a $2\pi$-periodic function. Its discrete Fourier coefficient
on $N$ equispaced nodes at a frequency $k$ is the sum of its exact coefficients at all frequencies
congruent to $k$ modulo $N$ (`DFT.coeff_eq_tsum_fourierCoeff`). So the discrete coefficient is the
exact one plus the **aliasing tail** $\sum_{j \ne 0} a_{k + jN}$. This file bounds the aliasing tail
for $\varphi$ in the periodic Sobolev space $H^s$ with $s > 1/2$, and derives from the bound the
error estimates for trigonometric interpolation at equispaced nodes. Here $H^s$ is
`PeriodicSobolev s`, the space of coefficient sequences $(a_m)_{m \in \mathbb{Z}}$ with
$$\|\varphi\|_s^2 = \sum_{m \in \mathbb{Z}} \bigl(w_s(m) |a_m|\bigr)^2 < \infty, \qquad w_s(0) = 1,
  \quad w_s(m) = |m|^s \ (m \ne 0).$$

The frequencies are grouped by the centred window $W_N = \{k \in \mathbb{Z} : -\lfloor N/2 \rfloor
\le k < -\lfloor N/2 \rfloor + N\}$ of $N$ consecutive frequencies. For $k \in W_N$, the
Cauchy–Schwarz inequality against $\sum_{j \ne 0} |k + jN|^{-2s} \le (N/2)^{-2s} \cdot 2\zeta(2s)$
gives
$$\Bigl|\sum_{j \ne 0} a_{k + jN}\Bigr| \le (N/2)^{-s} \sqrt{2\zeta(2s)} \Bigl(\sum_{j \ne 0}
  \bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2\Bigr)^{1/2}.$$
Because $W_N$ tiles $\mathbb{Z}$ under the shifts by multiples of $N$, the sum over $W_N$ of the
right-hand sides is controlled by the weighted energy of $\varphi$ outside $W_N$, which is at most
$\|\varphi\|_s^2$. This gives the $\ell^2$ and $\ell^1$ aliasing bounds, and three error estimates
for the interpolant $\Pi_N f$ of $f = \sum_m a_m e^{imx}$: in $L^2(0, 2\pi)$, in the maximum norm,
and for the discrete scalar product. The last part reads the interpolant $\mathcal{I}_n \varphi$ on
$2n + 1$ nodes in the Sobolev scale, and proves $\|\varphi - \mathcal{I}_n \varphi\|_r \le \sqrt{1 +
2\zeta(2s)} \, n^{r-s} \|\varphi\|_s$ for $0 \le r \le s$, which is Theorem 7.5.7 of
[han2009theoretical].

## Main definitions

* `DFT.window`: the centred window $W_N$ of $N$ consecutive frequencies.
* `PeriodicSobolev.aliasTail`: the aliasing tail $\sum_{j \ne 0} a_{k + jN}$.
* `PeriodicSobolev.windowTailNormSq`: the weighted energy $\sum_{m \notin W_N} (w_s(m) |a_m|)^2$
  outside the window.
* `PeriodicSobolev.interpErrorCoeff`: the coefficients of the interpolation error $f - \Pi_N f$.
* `DFT.windowTrigPoly`: the trigonometric polynomial $\sum_{q \in W_N} c_q e^{iqx}$.
* `PeriodicSobolev.trigInterp`: the trigonometric interpolant $\mathcal{I}_n \varphi$ of
  [han2009theoretical], §3.7, as an element of $H^r$.

## Main results

* `DFT.sum_window_tsum_add_mul`: the window tiles $\mathbb{Z}$, $\sum_{k \in W_N} \sum_j g(k + jN) =
  \sum_m g(m)$.
* `PeriodicSobolev.norm_aliasTail_le`: the bound on one aliasing tail.
* `PeriodicSobolev.sum_window_norm_aliasTail_sq_le`: the $\ell^2$ aliasing bound.
* `PeriodicSobolev.sum_window_norm_aliasTail_le`: the $\ell^1$ aliasing bound.
* `PeriodicSobolev.dftCoeff_eval_window`: on the window, the discrete coefficient is $a_q$ plus the
  aliasing tail.
* `PeriodicSobolev.sqrt_intervalIntegral_norm_eval_sub_interp_sq_le`: $\|f - \Pi_N f\|_{L^2(0,
  2\pi)} \le \sqrt{2\pi(1 + 2\zeta(2s))} \, 2^s N^{-s} \|\varphi\|_s$.
* `PeriodicSobolev.norm_eval_sub_interp_le`: $\max |f - \Pi_N f| \le 2 \sqrt{2\zeta(2s)} \, 2^s
  N^{1/2 - s} \|\varphi\|_s$.
* `PeriodicSobolev.norm_intervalIntegral_sub_discreteInner_le`: $|(f, v_N) - (f, v_N)_N| \le
  \sqrt{2\pi} \sqrt{2\zeta(2s)} \, 2^s N^{-s} \|\varphi\|_s \|v_N\|_{L^2}$ for every trigonometric
  polynomial $v_N$ over the window.
* `PeriodicSobolev.eval_trigInterp_angleNode`: $\mathcal{I}_n \varphi$ interpolates $\varphi$ at the
  $2n + 1$ nodes.
* `PeriodicSobolev.norm_incl_sub_trigInterp_le`: Theorem 7.5.7 of [han2009theoretical], $\|\varphi -
  \mathcal{I}_n \varphi\|_r \le \sqrt{1 + 2\zeta(2s)} \, n^{r-s} \|\varphi\|_s$.

## Proof outline

Three facts about the window carry everything. First, $2|k| \le N$ on the window and $N \le 2|k|$
off it. Second, $N|j| \le 2|k + jN|$ for $k$ in the window and $j \ne 0$, so the aliased frequencies
are far from $0$. Third, the window tiles $\mathbb{Z}$: $(k, j) \mapsto k + jN$ is a bijection
$W_N \times \mathbb{Z} \to \mathbb{Z}$.

For $f = \sum_m a_m e^{imx}$, the discrete coefficients over the centred window are
$\tilde f_q = a_q + \sum_{j \ne 0} a_{q + jN}$. So the interpolation error $f - \Pi_N f$ is the
trigonometric series with the coefficient $-\sum_{j \ne 0} a_{m + jN}$ on the window and $a_m$
outside it. Parseval's identity and the aliasing bounds give the three estimates of
[quarteroni2000numerical], §10.9.

## Notation

* $a_m$: the coefficient `PeriodicSobolev.coeff φ m` of $\varphi \in H^s$.
* $w_s(m)$: the weight `periodicSobolevWeight s m`.
* $\zeta(r)$: the value `zetaReal r` $= \sum_{n \ge 1} n^{-r}$ of the Riemann zeta function.
* $f$: the sum `PeriodicSobolev.eval (2 * π) φ` of the series $\sum_m a_m e^{imx}$.
* $\Pi_N f$: the discrete Fourier series `DFT.interp N (-(N / 2)) f` over the centred window.

## Implementation notes

* The window $W_N$ is the window $m = -N/2$ of [quarteroni2000numerical], §10.9, for even $N$, and
  it is $\{-n, \dots, n\}$ for $N = 2n + 1$. The bound $\lfloor N/2 \rfloor$ is natural-number
  division.
* The three estimates of [quarteroni2000numerical], §10.9, are unnumbered in the source. They are
  stated here in coefficient form, with the norm $\|\varphi\|_s$ of the coefficient sequence. The
  norm of the source for a smooth function is reached through `PeriodicSobolev.ofSmooth` of
  `Numlib.Analysis.Sobolev.Periodic.Smooth`.
* The constants are explicit but not sharp. The source leaves them unspecified.
* The interpolant `PeriodicSobolev.trigInterp r n φ` has finitely many nonzero coefficients, so it
  lies in $H^r$ for every $r$.
-/

open scoped Real

/-! ### The centred window -/


namespace DFT

/-- The **centred window** of $N$ consecutive frequencies:
$$W_N = \{k \in \mathbb{Z} : -\lfloor N/2 \rfloor \le k < -\lfloor N/2 \rfloor + N\}.$$
For even $N$ it is the window $m = -N/2$ of (10.50) of [quarteroni2000numerical], and for
$N = 2n + 1$ it is $\{-n, \dots, n\}$. -/
def window (N : ℕ) : Finset ℤ := Finset.Ico (-((N / 2 : ℕ) : ℤ)) (-((N / 2 : ℕ) : ℤ) + N)

/-- Membership in the centred window: $k \in W_N$ if and only if $-\lfloor N/2 \rfloor \le k <
-\lfloor N/2 \rfloor + N$. -/
theorem mem_window {N : ℕ} {k : ℤ} :
    k ∈ window N ↔ -((N / 2 : ℕ) : ℤ) ≤ k ∧ k < -((N / 2 : ℕ) : ℤ) + N := by
  rw [window, Finset.mem_Ico]

/-- The centred window $W_N$ has $N$ elements. -/
theorem card_window (N : ℕ) : (window N).card = N := by
  rw [window, Int.card_Ico]
  omega

/-- On the window, $|k| \le N/2$: if $k \in W_N$, then $2|k| \le N$. -/
theorem two_mul_abs_le_of_mem_window {N : ℕ} {k : ℤ} (hk : k ∈ window N) : 2 * |k| ≤ N := by
  rw [mem_window] at hk
  rcases le_or_gt 0 k with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

/-- Off the window, $|k| \ge N/2$: if $k \notin W_N$, then $N \le 2|k|$. -/
theorem le_two_mul_abs_of_not_mem_window {N : ℕ} {k : ℤ} (hk : k ∉ window N) :
    (N : ℤ) ≤ 2 * |k| := by
  rw [mem_window, not_and_or, not_le, not_lt] at hk
  rcases le_or_gt 0 k with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

/-- The aliased frequencies are far from $0$: for $k \in W_N$ and an integer $j \ne 0$,
$$N |j| \le 2 |k + jN|.$$
-/
theorem mul_abs_le_two_mul_abs_add_mul {N : ℕ} {k j : ℤ} (hk : k ∈ window N) (hj : j ≠ 0) :
    (N : ℤ) * |j| ≤ 2 * |k + j * N| := by
  have h1 := two_mul_abs_le_of_mem_window hk
  have h2 := le_abs_self (k + j * N)
  have h3 := neg_le_abs (k + j * N)
  have h4 := le_abs_self k
  have h5 := neg_le_abs k
  rcases le_or_gt 0 j with hj0 | hj0
  · have hj1 : 1 ≤ j := by omega
    rw [abs_of_nonneg hj0]
    nlinarith
  · rw [abs_of_neg hj0]
    nlinarith

/-- For $N \ge 1$, $k \in W_N$ and $j \ne 0$, the aliased frequency $k + jN$ is nonzero. -/
theorem add_mul_ne_zero_of_mem_window {N : ℕ} (hN : 0 < N) {k j : ℤ} (hk : k ∈ window N)
    (hj : j ≠ 0) :
    k + j * N ≠ 0 := by
  intro h
  have := mul_abs_le_two_mul_abs_add_mul hk hj
  rw [h, abs_zero, mul_zero] at this
  have : (0 : ℤ) < N * |j| := mul_pos (by exact_mod_cast hN) (abs_pos.mpr hj)
  omega

/-- Each residue class modulo $N$ has exactly one representative in the window: for $N \ge 1$ and
$m \in \mathbb{Z}$ there is a unique $k \in W_N$ with $N \mid m - k$. -/
theorem existsUnique_mem_window_dvd {N : ℕ} (hN : 0 < N) (m : ℤ) :
    ∃! k, k ∈ window N ∧ (N : ℤ) ∣ m - k := by
  set m₀ : ℤ := -((N / 2 : ℕ) : ℤ)
  refine ⟨m₀ + (m - m₀) % N, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_window]
    have h1 := Int.emod_nonneg (m - m₀) (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos (m - m₀) (by exact_mod_cast hN : (0 : ℤ) < N)
    constructor <;> omega
  · exact ⟨(m - m₀) / N, by have := Int.emod_def (m - m₀) N; linarith⟩
  · rintro k ⟨hk, hdvd⟩
    rw [mem_window] at hk
    obtain ⟨c, hc⟩ := hdvd
    have : (m - m₀) % N = k - m₀ := by
      rw [show m - m₀ = (k - m₀) + N * c by linarith, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt] <;> omega
    omega

end DFT

namespace DFT

/-- **The window tiles $\mathbb{Z}$.** Every integer is $k + jN$ for exactly one $k \in W_N$ and one
$j \in \mathbb{Z}$. So, for $N \ge 1$, a complete normed group $E$ and a summable family
$g : \mathbb{Z} \to E$,
$$\sum_{k \in W_N} \sum_{j \in \mathbb{Z}} g(k + jN) = \sum_{m \in \mathbb{Z}} g(m).$$
-/
theorem sum_window_tsum_add_mul {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {N : ℕ}
    (hN : 0 < N) {g : ℤ → E} (hg : Summable g) :
    ∑ k ∈ window N, ∑' j : ℤ, g (k + j * N) = ∑' m : ℤ, g m := by
  have hinj : ∀ k : ℤ, Function.Injective fun j : ℤ => k + j * N := by
    intro k a b hab
    have : a * (N : ℤ) = b * N := by simpa using hab
    exact mul_right_cancel₀ (by exact_mod_cast hN.ne') this
  have hterm : ∀ k : ℤ, ∑' j : ℤ, g (k + j * N)
      = ∑' m : ℤ, Set.indicator {m | (N : ℤ) ∣ m - k} g m := by
    intro k
    rw [← (hinj k).tsum_eq (f := Set.indicator {m | (N : ℤ) ∣ m - k} g)]
    · exact tsum_congr fun j => (Set.indicator_of_mem (show k + j * N ∈ {m | (N : ℤ) ∣ m - k} from
        ⟨j, by ring⟩) g).symm
    · intro m hm
      have hdvd : (N : ℤ) ∣ m - k := by
        by_contra h
        exact hm (Set.indicator_of_notMem (s := {m : ℤ | (N : ℤ) ∣ m - k}) (a := m) h g)
      obtain ⟨j, hj⟩ := hdvd
      exact ⟨j, by simp only; linear_combination -hj⟩
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum fun k _ => hg.indicator _]
  refine tsum_congr fun m => ?_
  obtain ⟨k₀, ⟨hk₀, hdvd⟩, huniq⟩ := existsUnique_mem_window_dvd hN m
  rw [Finset.sum_eq_single_of_mem k₀ hk₀ fun k hk hne =>
    Set.indicator_of_notMem (s := {m : ℤ | (N : ℤ) ∣ m - k}) (a := m)
      (fun h => hne (huniq k ⟨hk, h⟩)) g,
    Set.indicator_of_mem (s := {m : ℤ | (N : ℤ) ∣ m - k₀}) (a := m) hdvd]

end DFT


namespace PeriodicSobolev

open DFT

variable {s : ℝ}

/-- The **aliasing tail** of $\varphi \in H^s$ at the frequency $k$ for the modulus $N$:
$$\sum_{j \ne 0} a_{k + jN}.$$
It is the amount by which the discrete Fourier coefficient on $N$ nodes at $k$ differs from the
exact coefficient $a_k$.

The sum is a `tsum` over $j \in \mathbb{Z}$ with the term $j = 0$ replaced by $0$. It is $0$ if
the family is not summable; for $s > 1/2$ and $N \ge 1$ the family is summable. -/
noncomputable def aliasTail (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : ℂ :=
  ∑' j : ℤ, if j = 0 then 0 else coeff φ (k + j * N)

/-- The weighted energy of $\varphi \in H^s$ aliased onto the frequency $k$: $\sum_{j \ne 0}
\bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2$. -/
noncomputable def aliasNormSq (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : ℝ :=
  ∑' j : ℤ, if j = 0 then 0
    else (periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖) ^ 2

/-- The weighted energy of $\varphi \in H^s$ outside the window:
$$\sum_{m \notin W_N} \bigl(w_s(m) |a_m|\bigr)^2.$$
It is at most $\|\varphi\|_s^2$ (`PeriodicSobolev.windowTailNormSq_le`). -/
noncomputable def windowTailNormSq (N : ℕ) (φ : PeriodicSobolev s) : ℝ :=
  ∑' m : ℤ, if m ∈ window N then 0 else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2

/-- The weighted energy outside the window is nonnegative. -/
theorem windowTailNormSq_nonneg (N : ℕ) (φ : PeriodicSobolev s) : 0 ≤ windowTailNormSq N φ :=
  tsum_nonneg fun m => by split_ifs <;> positivity

private theorem summable_ite_window (N : ℕ) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => if m ∈ window N then (0 : ℝ)
      else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
    (fun m => by split_ifs <;> [positivity; exact le_rfl]) (hasSum_norm_sq φ).summable

/-- The weighted energy outside the window is at most the whole energy: $\sum_{m \notin W_N} (w_s(m)
|a_m|)^2 \le \|\varphi\|_s^2$.
-/
theorem windowTailNormSq_le (N : ℕ) (φ : PeriodicSobolev s) : windowTailNormSq N φ ≤ ‖φ‖ ^ 2 :=
  hasSum_le (fun m => by split_ifs <;> [positivity; exact le_rfl])
    (summable_ite_window N φ).hasSum (hasSum_norm_sq φ)

private theorem summable_aliasNormSq_term {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s) (k : ℤ) :
    Summable fun j : ℤ => if j = 0 then (0 : ℝ)
      else (periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖) ^ 2 :=
  Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
    (fun j => by
      simp only [Function.comp_apply]
      split_ifs <;> [positivity; exact le_rfl])
    ((hasSum_norm_sq φ).summable.comp_injective
      ((add_right_injective k).comp (mul_left_injective₀ (by exact_mod_cast hN.ne'))))

/-- The weighted energy aliased onto a frequency is nonnegative. -/
theorem aliasNormSq_nonneg (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : 0 ≤ aliasNormSq N φ k :=
  tsum_nonneg fun j => by split_ifs <;> positivity

/-- The partner sequence of the Cauchy–Schwarz inequality: $j \mapsto w_s(k + jN)^{-1}$ for
$j \ne 0$, and $0$ for $j = 0$. -/
private noncomputable def invWeight (s : ℝ) (N : ℕ) (k : ℤ) (j : ℤ) : ℝ :=
  if j = 0 then 0 else (periodicSobolevWeight s (k + j * N))⁻¹

private theorem invWeight_nonneg (s : ℝ) (N : ℕ) (k j : ℤ) : 0 ≤ invWeight s N k j := by
  rw [invWeight]
  split_ifs
  · exact le_rfl
  · exact (inv_pos.mpr (periodicSobolevWeight_pos _ _)).le

/-- For $s > 0$, $N \ge 1$, $k \in W_N$ and $j \ne 0$, $w_s(k + jN)^{-2} \le (N/2)^{-2s} |j|^{-2s}$;
the bound also holds at $j = 0$, where the left side is $0$. -/
private theorem invWeight_sq_le (hs : 0 < s) {N : ℕ} (hN : 0 < N) {k : ℤ} (hk : k ∈ window N)
    (j : ℤ) :
    invWeight s N k j ^ 2 ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (|(j : ℝ)| ^ (2 * s))⁻¹ := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp only [invWeight, ite_true, zero_pow two_ne_zero]
    positivity
  · have hne : k + j * N ≠ 0 := add_mul_ne_zero_of_mem_window hN hk hj
    rw [invWeight, ite_eq_right hj, inv_pow, periodicSobolevWeight_sq s hne, ← mul_inv,
      ← Real.mul_rpow (by positivity) (abs_nonneg _)]
    refine inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
    have h := mul_abs_le_two_mul_abs_add_mul hk hj
    have hR : (N : ℝ) * |(j : ℝ)| ≤ 2 * |((k + j * N : ℤ) : ℝ)| := by exact_mod_cast h
    linarith

private theorem summable_invWeight_sq (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) {k : ℤ}
    (hk : k ∈ window N) : Summable fun j : ℤ => invWeight s N k j ^ 2 :=
  Summable.of_nonneg_of_le (fun j => by positivity) (invWeight_sq_le (by linarith) hN hk)
    ((hasSum_int_inv_abs_rpow (by linarith : (1 : ℝ) < 2 * s)).mul_left _).summable

private theorem tsum_invWeight_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) {k : ℤ}
    (hk : k ∈ window N) :
    ∑' j : ℤ, invWeight s N k j ^ 2 ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)) := by
  have h := (hasSum_int_inv_abs_rpow (by linarith : (1 : ℝ) < 2 * s)).mul_left
    (((N : ℝ) / 2) ^ (2 * s))⁻¹
  exact hasSum_le (invWeight_sq_le (by linarith) hN hk)
    (summable_invWeight_sq hs hN hk).hasSum h

/-- For real $s$ and $a$, $\sqrt{(N/2)^{-2s} a} = (N/2)^{-s} \sqrt{a}$. -/
private theorem sqrt_bound (s : ℝ) (N : ℕ) (a : ℝ) :
    √((((N : ℝ) / 2) ^ (2 * s))⁻¹ * a) = ((N : ℝ) / 2) ^ (-s) * √a := by
  have hpos : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  rw [Real.sqrt_mul (by positivity), ← Real.rpow_neg hpos, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hpos]
  congr 2
  ring

/-- **The Cauchy–Schwarz inequality on the aliasing tail.** Let $s > 1/2$, $N \ge 1$,
$\varphi \in H^s$ and $k \in W_N$. Then the family $(|a_{k + jN}|)_{j \ne 0}$ is summable, and
$$\sum_{j \ne 0} |a_{k + jN}| \le (N/2)^{-s} \sqrt{2\zeta(2s)} \Bigl(\sum_{j \ne 0}
  \bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2\Bigr)^{1/2}.$$
-/
theorem summable_norm_coeff_add_mul_and_tsum_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) {k : ℤ} (hk : k ∈ window N) :
    (Summable fun j : ℤ => if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖) ∧
      ∑' j : ℤ, (if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖)
        ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(aliasNormSq N φ k) := by
  set y : ℤ → ℝ := fun j => if j = 0 then 0
    else periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖ with hy
  have hy0 : ∀ j, 0 ≤ y j := fun j => by
    simp only [hy]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (periodicSobolevWeight_pos _ _).le (norm_nonneg _)
  have hprod : ∀ j, invWeight s N k j * y j
      = if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖ := by
    intro j
    simp only [hy, invWeight]
    split_ifs with h
    · rw [mul_zero]
    · rw [← mul_assoc, inv_mul_cancel₀ (periodicSobolevWeight_ne_zero _ _), one_mul]
  have hysq : (fun j => y j ^ 2) = fun j : ℤ => if j = 0 then (0 : ℝ)
      else (periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖) ^ 2 := by
    funext j
    simp only [hy]
    split_ifs <;> simp
  have hsy : Summable fun j => y j ^ 2 := by
    rw [hysq]
    exact summable_aliasNormSq_term hN φ k
  obtain ⟨hsum, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two (invWeight_nonneg s N k) hy0
    (by simpa only [Real.rpow_two] using summable_invWeight_sq hs hN hk)
    (by simpa only [Real.rpow_two] using hsy)
  simp only [Real.rpow_two, hprod] at hsum hle
  refine ⟨hsum, hle.trans ?_⟩
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hysq, ← sqrt_bound s N]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (tsum_invWeight_sq_le hs hN hk))
    (Real.sqrt_nonneg _)

/-- **The aliasing tail is small.** Let $s > 1/2$, $N \ge 1$, $\varphi \in H^s$ and $k \in W_N$.
Then
$$\Bigl|\sum_{j \ne 0} a_{k + jN}\Bigr| \le (N/2)^{-s} \sqrt{2\zeta(2s)} \Bigl(\sum_{j \ne 0}
  \bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2\Bigr)^{1/2}.$$

The last factor is the square root of `PeriodicSobolev.aliasNormSq N φ k`. -/
theorem norm_aliasTail_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s) {k : ℤ}
    (hk : k ∈ window N) :
    ‖aliasTail N φ k‖ ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(aliasNormSq N φ k) := by
  obtain ⟨hsum, hle⟩ := summable_norm_coeff_add_mul_and_tsum_le hs hN φ hk
  have hnorm : ∀ j : ℤ, ‖(if j = 0 then (0 : ℂ) else coeff φ (k + j * N))‖
      = if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖ := by
    intro j
    split_ifs <;> simp
  refine le_trans ?_ hle
  rw [aliasTail]
  refine (norm_tsum_le_tsum_norm (hsum.congr fun j => (hnorm j).symm)).trans (le_of_eq ?_)
  exact tsum_congr hnorm

/-- The squared form of `PeriodicSobolev.norm_aliasTail_le`: for $s > 1/2$, $N \ge 1$ and
$k \in W_N$,
$$\Bigl|\sum_{j \ne 0} a_{k + jN}\Bigr|^2 \le (N/2)^{-2s} \cdot 2\zeta(2s) \sum_{j \ne 0}
  \bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2.$$
-/
theorem norm_aliasTail_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s)
    {k : ℤ} (hk : k ∈ window N) :
    ‖aliasTail N φ k‖ ^ 2
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)) * aliasNormSq N φ k := by
  have h := norm_aliasTail_le hs hN φ hk
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg two_pos.le (zetaReal_nonneg _)),
    Real.sq_sqrt (aliasNormSq_nonneg N φ k),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show -s * ((2 : ℕ) : ℝ) = -(2 * s) by push_cast; ring, Real.rpow_neg (by positivity)]

/-- **The window tiles the frequencies.** For $N \ge 1$ and $\varphi \in H^s$, the weighted energies
aliased onto the frequencies of the window add up to the weighted energy outside the window:
$$\sum_{k \in W_N} \sum_{j \ne 0} \bigl(w_s(k + jN) |a_{k + jN}|\bigr)^2 = \sum_{m \notin W_N}
  \bigl(w_s(m) |a_m|\bigr)^2.$$
-/
theorem sum_window_aliasNormSq {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, aliasNormSq N φ k = windowTailNormSq N φ := by
  rw [windowTailNormSq, ← sum_window_tsum_add_mul hN (summable_ite_window N φ)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [aliasNormSq]
  refine tsum_congr fun j => ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [hk]
  · have : k + j * N ∉ window N := by
      intro h
      rw [mem_window] at h hk
      rcases lt_or_gt_of_ne hj with hj' | hj'
      · have := mul_le_mul_of_nonneg_right (show j ≤ -1 by omega) (Int.natCast_nonneg N)
        omega
      · have := mul_le_mul_of_nonneg_right (show 1 ≤ j by omega) (Int.natCast_nonneg N)
        omega
    simp [hj, this]

end PeriodicSobolev

namespace PeriodicSobolev

open DFT

variable {s : ℝ}

/-- **The $\ell^2$ aliasing bound.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$. Then
$$\sum_{k \in W_N} \Bigl|\sum_{j \ne 0} a_{k + jN}\Bigr|^2 \le (N/2)^{-2s} \cdot 2\zeta(2s)
  \sum_{m \notin W_N} \bigl(w_s(m) |a_m|\bigr)^2.$$
So the discrete coefficients over the window differ from the exact ones, in the sum of squares,
by at most $(N/2)^{-2s} \cdot 2\zeta(2s)$ times the weighted energy outside the window. -/
theorem sum_window_norm_aliasTail_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, ‖aliasTail N φ k‖ ^ 2
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)) * windowTailNormSq N φ := by
  calc ∑ k ∈ window N, ‖aliasTail N φ k‖ ^ 2
      ≤ ∑ k ∈ window N, (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))
          * aliasNormSq N φ k := Finset.sum_le_sum fun k hk => norm_aliasTail_sq_le hs hN φ hk
    _ = _ := by rw [← Finset.mul_sum, sum_window_aliasNormSq hN φ]

/-- The Cauchy–Schwarz inequality over the window: for $t \ge 0$, $\sum_{k \in W_N} \sqrt{t_k} \le
\sqrt{N} \bigl(\sum_{k \in W_N} t_k\bigr)^{1/2}$. -/
private theorem sum_window_sqrt_le (N : ℕ) {t : ℤ → ℝ} (ht : ∀ k, 0 ≤ t k) :
    ∑ k ∈ window N, √(t k) ≤ √(N : ℝ) * √(∑ k ∈ window N, t k) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (window N) (fun _ => (1 : ℝ)) fun k => √(t k)
  simp only [one_mul, one_pow, Finset.sum_const, card_window, nsmul_eq_mul, mul_one,
    Real.sq_sqrt (ht _)] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg N), ← Real.sqrt_sq (Finset.sum_nonneg fun k _ =>
    Real.sqrt_nonneg (t k))]
  exact Real.sqrt_le_sqrt h

/-- The bounds of `PeriodicSobolev.summable_norm_coeff_add_mul_and_tsum_le`, summed over the window,
are at most $(N/2)^{-s} \sqrt{2\zeta(2s)} \sqrt{N}$ times the square root of the weighted energy
outside the window. -/
private theorem sum_window_mul_sqrt_aliasNormSq_le {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(aliasNormSq N φ k)
      ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ) * √(windowTailNormSq N φ)) := by
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← sum_window_aliasNormSq hN φ]
  exact sum_window_sqrt_le N (aliasNormSq_nonneg N φ)

/-- **The $\ell^1$ aliasing bound.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$. Then
$$\sum_{k \in W_N} \Bigl|\sum_{j \ne 0} a_{k + jN}\Bigr| \le (N/2)^{-s} \sqrt{2\zeta(2s)}
  \sqrt{N} \Bigl(\sum_{m \notin W_N} \bigl(w_s(m) |a_m|\bigr)^2\Bigr)^{1/2}.$$
The factor $\sqrt{N}$ comes from the Cauchy–Schwarz inequality over the $N$ frequencies of the
window. -/
theorem sum_window_norm_aliasTail_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, ‖aliasTail N φ k‖
      ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ) * √(windowTailNormSq N φ)) := by
  exact (Finset.sum_le_sum fun k hk => norm_aliasTail_le hs hN φ hk).trans
    (sum_window_mul_sqrt_aliasNormSq_le hN φ)

/-- **The $\ell^1$ tail outside the window.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$. Then
$$\sum_{m \notin W_N} |a_m| \le (N/2)^{-s} \sqrt{2\zeta(2s)} \sqrt{N} \Bigl(\sum_{m \notin W_N}
  \bigl(w_s(m) |a_m|\bigr)^2\Bigr)^{1/2}.$$
The proof tiles the complement of the window with the aliasing tails. -/
theorem tsum_norm_coeff_notMem_window_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖)
      ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ) * √(windowTailNormSq N φ)) := by
  have hg : Summable fun m : ℤ => if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => by split_ifs <;> [positivity; exact le_rfl]) (summable_norm_coeff hs φ)
  rw [← sum_window_tsum_add_mul hN hg]
  have hterm : ∀ k ∈ window N, ∑' j : ℤ, (if k + j * N ∈ window N then (0 : ℝ)
      else ‖coeff φ (k + j * N)‖)
      = ∑' j : ℤ, (if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖) := by
    intro k hk
    refine tsum_congr fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp [hk]
    · have : k + j * N ∉ window N := by
        intro h
        rw [mem_window] at h hk
        rcases lt_or_gt_of_ne hj with hj' | hj'
        · have := mul_le_mul_of_nonneg_right (show j ≤ -1 by omega) (Int.natCast_nonneg N)
          omega
        · have := mul_le_mul_of_nonneg_right (show 1 ≤ j by omega) (Int.natCast_nonneg N)
          omega
      simp [hj, this]
  calc ∑ k ∈ window N, ∑' j : ℤ, (if k + j * N ∈ window N then (0 : ℝ) else ‖coeff φ (k + j * N)‖)
      = ∑ k ∈ window N, ∑' j : ℤ, (if j = 0 then (0 : ℝ) else ‖coeff φ (k + j * N)‖) :=
        Finset.sum_congr rfl hterm
    _ ≤ ∑ k ∈ window N, ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(aliasNormSq N φ k) :=
        Finset.sum_le_sum fun k hk => (summable_norm_coeff_add_mul_and_tsum_le hs hN φ hk).2
    _ ≤ _ := sum_window_mul_sqrt_aliasNormSq_le hN φ

/-- For $s \ge 0$, $N \ge 1$ and $m \notin W_N$, $|a_m|^2 \le (N/2)^{-2s} (w_s(m) |a_m|)^2$, because
$|m| \ge N/2$ outside the window. -/
private theorem norm_coeff_sq_le_of_not_mem_window (hs : 0 ≤ s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) {m : ℤ} (hm : m ∉ window N) :
    ‖coeff φ m‖ ^ 2
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := le_two_mul_abs_of_not_mem_window hm
    simp at this
    omega
  have habs : (N : ℝ) / 2 ≤ |(m : ℝ)| := by
    have h := le_two_mul_abs_of_not_mem_window hm
    have hR : (N : ℝ) ≤ 2 * |(m : ℝ)| := by exact_mod_cast h
    linarith
  have hpow : ((N : ℝ) / 2) ^ (2 * s) ≤ |(m : ℝ)| ^ (2 * s) :=
    Real.rpow_le_rpow (by positivity) habs (by positivity)
  have hpos : (0 : ℝ) < ((N : ℝ) / 2) ^ (2 * s) := Real.rpow_pos_of_pos (by positivity) _
  rw [mul_pow, periodicSobolevWeight_sq s hm0]
  calc ‖coeff φ m‖ ^ 2
      = (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (((N : ℝ) / 2) ^ (2 * s) * ‖coeff φ m‖ ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity))
        (by positivity)

/-- A nonnegative family $g$ with $g(m) \le C (w_s(m) |a_m|)^2$ for all $m \notin W_N$ has $\sum_{m
\notin W_N} g(m) \le C \sum_{m \notin W_N} (w_s(m) |a_m|)^2$. -/
private theorem tsum_ite_window_le_mul_windowTailNormSq {N : ℕ} (φ : PeriodicSobolev s) {C : ℝ}
    {g : ℤ → ℝ} (hg : ∀ m, 0 ≤ g m)
    (hle : ∀ m ∉ window N, g m ≤ C * (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) :
    ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else g m) ≤ C * windowTailNormSq N φ := by
  rw [windowTailNormSq, ← tsum_mul_left]
  have hle' : ∀ m : ℤ, (if m ∈ window N then (0 : ℝ) else g m)
      ≤ C * (if m ∈ window N then (0 : ℝ)
        else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) := by
    intro m
    split_ifs with hm
    · simp
    · exact hle m hm
  exact hasSum_le hle'
    (Summable.of_nonneg_of_le (fun m => by split_ifs <;> [exact le_rfl; exact hg m]) hle'
      ((summable_ite_window N φ).mul_left _)).hasSum ((summable_ite_window N φ).mul_left _).hasSum

/-- **The $\ell^2$ tail outside the window.** Let $s \ge 0$, $N \ge 1$ and $\varphi \in H^s$. Then
$$\sum_{m \notin W_N} |a_m|^2 \le (N/2)^{-2s} \sum_{m \notin W_N} \bigl(w_s(m) |a_m|\bigr)^2.$$
-/
theorem tsum_norm_coeff_sq_notMem_window_le (hs : 0 ≤ s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ ^ 2)
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * windowTailNormSq N φ :=
  tsum_ite_window_le_mul_windowTailNormSq φ (fun m => by positivity)
    fun m hm => norm_coeff_sq_le_of_not_mem_window hs hN φ hm

end PeriodicSobolev

/-! ### The discrete Fourier coefficients of the sum of the series -/

namespace DFT

open Complex

/-- A sum over the shifted frequencies $k - \lfloor N/2 \rfloor$, $k = 0, \dots, N - 1$, is a sum
over the centred window: for every $F : \mathbb{Z} \to \mathbb{C}$,
$$\sum_{k=0}^{N-1} F(k - \lfloor N/2 \rfloor) = \sum_{q \in W_N} F(q).$$
-/
theorem sum_range_eq_sum_window (N : ℕ) (F : ℤ → ℂ) :
    ∑ k ∈ Finset.range N, F ((k : ℤ) + -((N / 2 : ℕ) : ℤ)) = ∑ q ∈ window N, F q := by
  refine Finset.sum_nbij' (fun k => (k : ℤ) + -((N / 2 : ℕ) : ℤ))
    (fun q => (q + ((N / 2 : ℕ) : ℤ)).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [mem_window]
    omega
  · intro q hq
    rw [mem_window] at hq
    rw [Finset.mem_range]
    omega
  · intro k _
    omega
  · intro q hq
    rw [mem_window] at hq
    omega
  · intro k _
    rfl

end DFT

namespace PeriodicSobolev

open Complex DFT Quadrature

variable {s : ℝ}

/-- **The discrete Fourier coefficients of the sum of the series are the aliasing sums.** Let
$s > 1/2$, $N \ge 1$, $m \in \mathbb{Z}$ and $\varphi \in H^s$, and let $f$ be the sum of the
series $\sum_p a_p e^{ipx}$. Then for every natural number $k$, the discrete Fourier coefficient
of $f$ on $N$ nodes over the window that starts at $m$ is
$$\sum_{j \in \mathbb{Z}} a_{k + m + jN}.$$

The function $f$ is `PeriodicSobolev.eval (2 * π) φ`. The proof is the aliasing identity
`DFT.coeff_eq_tsum_fourierCoeff`, with the Fourier coefficients of $f$ read off by
`PeriodicSobolev.fourierCoeff_lift_eval`. -/
theorem dftCoeff_eval (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (m : ℤ) (φ : PeriodicSobolev s)
    (k : ℕ) :
    DFT.coeff N m (eval (2 * π) φ) k = ∑' j : ℤ, coeff φ ((k : ℤ) + m + j * N) := by
  have hper := eval_periodic (T := 2 * π) (Fact.out : (0 : ℝ) < 2 * π).ne' φ
  have hcont : Continuous (eval (2 * π) φ) := continuous_eval hs _ φ
  have h := DFT.coeff_eq_tsum_fourierCoeff hN m
    (f := ⟨hper.lift, hper.continuous_lift hcont⟩) (summable_fourierCoeff_lift_eval hs φ) k
  simp only [ContinuousMap.coe_mk, Function.Periodic.lift_coe, fourierCoeff_lift_eval hs] at h
  exact h

/-- Over the centred window, the discrete coefficient is the exact one plus the aliasing tail. Let
$s > 1/2$, $N \ge 1$, $\varphi \in H^s$ and $q \in W_N$, and let $\tilde f_q$ be the discrete
Fourier coefficient of $f = \sum_p a_p e^{ipx}$ at the frequency $q$ over the window $W_N$. Then
$$\tilde f_q = a_q + \sum_{j \ne 0} a_{q + jN}.$$

The coefficient $\tilde f_q$ is `DFT.coeff N (-(N / 2)) f (q + N / 2).toNat`, the coefficient
over the window that starts at $-\lfloor N/2 \rfloor$, at the index $q + \lfloor N/2 \rfloor \in
\{0, \dots, N - 1\}$. -/
theorem dftCoeff_eval_window (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s)
    {q : ℤ} (hq : q ∈ window N) :
    DFT.coeff N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) (q + ((N / 2 : ℕ) : ℤ)).toNat
      = coeff φ q + aliasTail N φ q := by
  rw [dftCoeff_eval hs hN]
  have hq' : (((q + ((N / 2 : ℕ) : ℤ)).toNat : ℕ) : ℤ) + -((N / 2 : ℕ) : ℤ) = q := by
    rw [mem_window] at hq
    omega
  simp_rw [hq']
  have hsum : Summable fun j : ℤ => coeff φ (q + j * N) :=
    (summable_coeff hs φ).comp_injective fun a b hab => by
      have : a * (N : ℤ) = b * N := by simpa using hab
      exact mul_right_cancel₀ (by exact_mod_cast hN.ne') this
  rw [hsum.tsum_eq_add_tsum_ite 0, aliasTail]
  simp

/-- The coefficients $d_m$ of the interpolation error $f - \Pi_N f$: the negative aliasing tail
$-\sum_{j \ne 0} a_{m + jN}$ for $m \in W_N$, and the exact coefficient $a_m$ for
$m \notin W_N$. -/
noncomputable def interpErrorCoeff (N : ℕ) (φ : PeriodicSobolev s) (m : ℤ) : ℂ :=
  if m ∈ window N then -aliasTail N φ m else coeff φ m

/-- The moduli of the error coefficients: $|d_m| = |\sum_{j \ne 0} a_{m + jN}|$ for $m \in W_N$, and
$|d_m| = |a_m|$ otherwise. -/
theorem norm_interpErrorCoeff (N : ℕ) (φ : PeriodicSobolev s) (m : ℤ) :
    ‖interpErrorCoeff N φ m‖ = if m ∈ window N then ‖aliasTail N φ m‖ else ‖coeff φ m‖ := by
  rw [interpErrorCoeff]
  split_ifs <;> simp

/-- For $s > 1/2$, the error coefficients $d_m$ are absolutely summable, so the series of the
interpolation error converges uniformly. -/
theorem summable_norm_interpErrorCoeff (hs : 1 / 2 < s) (N : ℕ) (φ : PeriodicSobolev s) :
    Summable fun m => ‖interpErrorCoeff N φ m‖ := by
  have h1 : Summable fun m : ℤ => if m ∈ window N then ‖aliasTail N φ m‖ else 0 :=
    summable_of_ne_finset_zero (s := window N) fun m hm => by simp [hm]
  refine ((summable_norm_coeff hs φ).add h1).of_nonneg_of_le (fun m => norm_nonneg _)
    fun m => ?_
  rw [norm_interpErrorCoeff]
  split_ifs <;> simp

/-- **The interpolation error is a trigonometric series.** Let $s > 1/2$, $N \ge 1$ and
$\varphi \in H^s$, and let $f = \sum_m a_m e^{imx}$. Then for every $x \in \mathbb{R}$,
$$f(x) - \Pi_N f(x) = \sum_{m \in \mathbb{Z}} d_m e^{imx},$$
where $d_m$ are the coefficients `PeriodicSobolev.interpErrorCoeff N φ m`.

The character $e^{imx}$ is `fourier m` at the class of $x$ in `AddCircle (2 * π)`, and the
interpolant $\Pi_N f$ is `DFT.interp N (-(N / 2)) f`. -/
theorem eval_sub_interp_eq_tsum (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s)
    (x : ℝ) :
    eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x
      = ∑' m : ℤ, interpErrorCoeff N φ m • fourier m (x : AddCircle (2 * π)) := by
  set m₀ : ℤ := -((N / 2 : ℕ) : ℤ) with hm₀
  -- the interpolant as a sum over the window
  have hinterp : DFT.interp N m₀ (eval (2 * π) φ) x
      = ∑ q ∈ window N, (coeff φ q + aliasTail N φ q) • fourier q (x : AddCircle (2 * π)) := by
    rw [DFT.interp_def, ← sum_range_eq_sum_window N
      (fun q => (coeff φ q + aliasTail N φ q) • fourier q (x : AddCircle (2 * π)))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hq : (k : ℤ) + m₀ ∈ window N := by rw [mem_window]; omega
    have hk' : ((k : ℤ) + m₀ + ((N / 2 : ℕ) : ℤ)).toNat = k := by omega
    rw [← dftCoeff_eval_window hs hN φ hq, hk', fourier_coe_two_pi, smul_eq_mul]
  -- as a `tsum` supported on the window
  have hinterp' : DFT.interp N m₀ (eval (2 * π) φ) x
      = ∑' q : ℤ, (if q ∈ window N then coeff φ q + aliasTail N φ q else 0)
          • fourier q (x : AddCircle (2 * π)) := by
    rw [hinterp, tsum_eq_sum (s := window N) fun q hq => by simp [hq]]
    exact Finset.sum_congr rfl fun q hq => by simp [hq]
  have hs1 : Summable fun m : ℤ => coeff φ m • fourier m (x : AddCircle (2 * π)) := by
    refine Summable.of_norm ((summable_norm_coeff hs φ).congr fun m => ?_)
    rw [norm_smul, norm_fourier_apply, mul_one]
  have hs2 : Summable fun q : ℤ => (if q ∈ window N then coeff φ q + aliasTail N φ q else 0)
      • fourier q (x : AddCircle (2 * π)) :=
    summable_of_ne_finset_zero (s := window N) fun q hq => by simp [hq]
  rw [eval_eq_tsum_smul_fourier, hinterp', ← hs1.tsum_sub hs2]
  refine tsum_congr fun m => ?_
  rw [← sub_smul, interpErrorCoeff]
  split_ifs <;> simp

end PeriodicSobolev

/-! ### The interpolation error in $L^2$ and in the maximum norm -/

namespace PeriodicSobolev

open Complex DFT

variable {s : ℝ}

/-- For $s > 1/2$, the sum of squares of the error coefficients splits into the aliasing errors over
the window and the tail outside it:
$$\sum_m |d_m|^2 = \sum_{m \in W_N} \Bigl|\sum_{j \ne 0} a_{m + jN}\Bigr|^2 + \sum_{m \notin
  W_N} |a_m|^2.$$
-/
theorem tsum_norm_interpErrorCoeff_sq (hs : 1 / 2 < s) (N : ℕ) (φ : PeriodicSobolev s) :
    ∑' m : ℤ, ‖interpErrorCoeff N φ m‖ ^ 2
      = ∑ m ∈ window N, ‖aliasTail N φ m‖ ^ 2
        + ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ ^ 2) := by
  have hle : ∀ m : ℤ, ‖coeff φ m‖ ^ 2 ≤ (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 := by
    intro m
    have h1 : (1 : ℝ) ≤ periodicSobolevWeight s m := by
      have := periodicSobolevWeight_le (by linarith : (0 : ℝ) ≤ s) m
      rwa [periodicSobolevWeight_zero_exponent] at this
    have h2 : ‖coeff φ m‖ ≤ periodicSobolevWeight s m * ‖coeff φ m‖ := by
      nlinarith [norm_nonneg (coeff φ m)]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hsum : Summable fun m : ℤ => ‖interpErrorCoeff N φ m‖ ^ 2 := by
    have h1 : Summable fun m : ℤ => if m ∈ window N then ‖aliasTail N φ m‖ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := window N) fun m hm => by simp [hm]
    refine (((hasSum_norm_sq φ).summable.of_nonneg_of_le (fun m => by positivity) hle).add
      h1).of_nonneg_of_le (fun m => by positivity) fun m => ?_
    rw [norm_interpErrorCoeff]
    split_ifs <;> simp
  rw [hsum.tsum_eq_sum_add_tsum_ite (window N)]
  congr 1
  · exact Finset.sum_congr rfl fun m hm => by rw [norm_interpErrorCoeff, ite_eq_left hm]
  · refine tsum_congr fun m => ?_
    split_ifs with hm
    · rfl
    · rw [norm_interpErrorCoeff, ite_eq_right hm]

/-- **Parseval's identity for the interpolation error.** For $s > 1/2$, $N \ge 1$ and
$\varphi \in H^s$,
$$\int_0^{2\pi} |f(x) - \Pi_N f(x)|^2 \, dx = 2\pi \sum_{m \in \mathbb{Z}} |d_m|^2.$$
-/
theorem intervalIntegral_norm_eval_sub_interp_sq (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∫ x in (0 : ℝ)..2 * π,
        ‖eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x‖ ^ 2
      = 2 * π * ∑' m : ℤ, ‖interpErrorCoeff N φ m‖ ^ 2 := by
  simp_rw [eval_sub_interp_eq_tsum hs hN φ]
  exact intervalIntegral_norm_tsum_smul_fourier_sq (summable_norm_interpErrorCoeff hs N φ)

/-- **The $L^2$ interpolation error** in terms of the weighted energy outside the window. For
$s > 1/2$, $N \ge 1$ and $\varphi \in H^s$,
$$\int_0^{2\pi} |f(x) - \Pi_N f(x)|^2 \, dx \le 2\pi (N/2)^{-2s} \bigl(1 + 2\zeta(2s)\bigr)
  \sum_{m \notin W_N} \bigl(w_s(m) |a_m|\bigr)^2.$$
-/
theorem intervalIntegral_norm_eval_sub_interp_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∫ x in (0 : ℝ)..2 * π,
        ‖eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x‖ ^ 2
      ≤ 2 * π * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (1 + 2 * zetaReal (2 * s)))
        * windowTailNormSq N φ := by
  rw [intervalIntegral_norm_eval_sub_interp_sq hs hN φ, tsum_norm_interpErrorCoeff_sq hs N φ]
  have h1 := sum_window_norm_aliasTail_sq_le hs hN φ
  have h2 := tsum_norm_coeff_sq_notMem_window_le (by linarith : (0 : ℝ) ≤ s) hN φ
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  calc 2 * π * (∑ m ∈ window N, ‖aliasTail N φ m‖ ^ 2
        + ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ ^ 2))
      ≤ 2 * π * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)) * windowTailNormSq N φ
          + (((N : ℝ) / 2) ^ (2 * s))⁻¹ * windowTailNormSq N φ) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hpi
    _ = _ := by ring

/-- For real $s$ and $N \ge 1$, $(N/2)^{-s} = 2^s N^{-s}$. -/
theorem div_two_rpow_neg (s : ℝ) {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) / 2) ^ (-s) = (2 : ℝ) ^ s * (N : ℝ) ^ (-s) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
    Real.div_rpow (by positivity) (by positivity)]
  field_simp

/-- **The $L^2$ interpolation error.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$, and let
$f = \sum_m a_m e^{imx}$. Then
$$\|f - \Pi_N f\|_{L^2(0, 2\pi)} \le \sqrt{2\pi(1 + 2\zeta(2s))} \, 2^s N^{-s} \|\varphi\|_s,$$
where $\Pi_N f$ is the discrete Fourier series of $f$ over the centred window. This is the first
unnumbered interpolation estimate of [quarteroni2000numerical], §10.9, in coefficient form.

The interpolant $\Pi_N f$ is `DFT.interp N (-(N / 2)) f`, the window $m = -\lfloor N/2 \rfloor$.
The error splits into the aliasing error over the window and the truncation error outside it.
Both are $O(N^{-s})$, by the bound on the weighted energy outside the window. -/
theorem sqrt_intervalIntegral_norm_eval_sub_interp_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    √(∫ x in (0 : ℝ)..2 * π,
        ‖eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x‖ ^ 2)
      ≤ √(2 * π * (1 + 2 * zetaReal (2 * s))) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖ := by
  have hz := zetaReal_nonneg (2 * s)
  have hbound := (intervalIntegral_norm_eval_sub_interp_sq_le hs hN φ).trans
    (mul_le_mul_of_nonneg_left (windowTailNormSq_le N φ) (by positivity))
  have hsqrt : √(2 * π * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (1 + 2 * zetaReal (2 * s))) * ‖φ‖ ^ 2)
      = √(2 * π * (1 + 2 * zetaReal (2 * s))) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖ := by
    rw [show 2 * π * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (1 + 2 * zetaReal (2 * s))) * ‖φ‖ ^ 2
        = (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * π * (1 + 2 * zetaReal (2 * s)) * ‖φ‖ ^ 2) by ring,
      sqrt_bound, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π * (1 + 2 * zetaReal (2 * s))),
      Real.sqrt_sq (norm_nonneg _), div_two_rpow_neg s hN]
    ring
  rw [← hsqrt]
  exact Real.sqrt_le_sqrt hbound

/-- **The interpolation error in the maximum norm.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$,
and let $f = \sum_m a_m e^{imx}$. Then for every $x \in \mathbb{R}$,
$$|f(x) - \Pi_N f(x)| \le 2 \sqrt{2\zeta(2s)} \, 2^s N^{1/2 - s} \|\varphi\|_s.$$
This is the second unnumbered interpolation estimate of [quarteroni2000numerical], §10.9, in
coefficient form.

The error is a trigonometric series with the coefficients `PeriodicSobolev.interpErrorCoeff`, so
it is bounded by the sum of their moduli. This sum is the $\ell^1$ aliasing bound over the
window plus the $\ell^1$ tail outside it, and each is at most
$(N/2)^{-s} \sqrt{2\zeta(2s)} \sqrt{N}$ times the square root of the weighted energy outside the
window. -/
theorem norm_eval_sub_interp_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s)
    (x : ℝ) :
    ‖eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x‖
      ≤ 2 * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ s * (N : ℝ) ^ (1 / 2 - s) * ‖φ‖ := by
  rw [eval_sub_interp_eq_tsum hs hN φ x]
  have hsum := summable_norm_interpErrorCoeff hs N φ
  have h1 : ‖∑' m : ℤ, interpErrorCoeff N φ m • fourier m (x : AddCircle (2 * π))‖
      ≤ ∑' m : ℤ, ‖interpErrorCoeff N φ m‖ := by
    refine (norm_tsum_le_tsum_norm (hsum.congr fun m => ?_)).trans (le_of_eq (tsum_congr fun m =>
      ?_)) <;> rw [norm_smul, norm_fourier_apply, mul_one]
  have h2 : ∑' m : ℤ, ‖interpErrorCoeff N φ m‖
      = ∑ m ∈ window N, ‖aliasTail N φ m‖
        + ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖) := by
    rw [hsum.tsum_eq_sum_add_tsum_ite (window N)]
    congr 1
    · exact Finset.sum_congr rfl fun m hm => by rw [norm_interpErrorCoeff, ite_eq_left hm]
    · refine tsum_congr fun m => ?_
      split_ifs with hm
      · rfl
      · rw [norm_interpErrorCoeff, ite_eq_right hm]
  have h3 := sum_window_norm_aliasTail_le hs hN φ
  have h4 := tsum_norm_coeff_notMem_window_le hs hN φ
  have htail : √(windowTailNormSq N φ) ≤ ‖φ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg φ)]
    exact Real.sqrt_le_sqrt (windowTailNormSq_le N φ)
  have hrate : ((N : ℝ) / 2) ^ (-s) * √(N : ℝ) = (2 : ℝ) ^ s * (N : ℝ) ^ (1 / 2 - s) := by
    rw [div_two_rpow_neg s hN, Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add (by positivity)]
    congr 2
    ring
  calc ‖∑' m : ℤ, interpErrorCoeff N φ m • fourier m (x : AddCircle (2 * π))‖
      ≤ ∑' m : ℤ, ‖interpErrorCoeff N φ m‖ := h1
    _ = _ := h2
    _ ≤ 2 * (((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ)
          * √(windowTailNormSq N φ))) := by linarith
    _ ≤ 2 * (((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ) * ‖φ‖)) := by
        gcongr
    _ = 2 * √(2 * zetaReal (2 * s)) * (((N : ℝ) / 2) ^ (-s) * √(N : ℝ)) * ‖φ‖ := by ring
    _ = _ := by rw [hrate]; ring

end PeriodicSobolev

/-! ### The discrete scalar product -/

namespace DFT

open Complex

/-- The trigonometric polynomial with frequencies in the centred window and coefficients $c$:
$$v(x) = \sum_{q \in W_N} c_q e^{iqx}.$$
It is the general element of the space $S_N$ of [quarteroni2000numerical], §10.9. -/
noncomputable def windowTrigPoly (N : ℕ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ q ∈ window N, c q * Complex.exp ((q : ℂ) * x * I)

/-- A trigonometric polynomial over the window is the trigonometric series whose coefficients are
$c_q$ for $q \in W_N$ and $0$ otherwise. -/
theorem windowTrigPoly_eq_tsum (N : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    windowTrigPoly N c x
      = ∑' q : ℤ, (if q ∈ window N then c q else 0) • fourier q (x : AddCircle (2 * π)) := by
  rw [windowTrigPoly, tsum_eq_sum (s := window N) fun q hq => by simp [hq]]
  exact Finset.sum_congr rfl fun q hq => by rw [ite_eq_left hq, fourier_coe_two_pi, smul_eq_mul]

/-- **Parseval's identity for a trigonometric polynomial over the window**: for
$c : \mathbb{Z} \to \mathbb{C}$,
$$\int_0^{2\pi} \Bigl|\sum_{q \in W_N} c_q e^{iqx}\Bigr|^2 \, dx = 2\pi \sum_{q \in W_N}
  |c_q|^2.$$
-/
theorem intervalIntegral_norm_windowTrigPoly_sq (N : ℕ) (c : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..2 * π, ‖windowTrigPoly N c x‖ ^ 2 = 2 * π * ∑ q ∈ window N, ‖c q‖ ^ 2 := by
  simp_rw [windowTrigPoly_eq_tsum]
  rw [intervalIntegral_norm_tsum_smul_fourier_sq
    (summable_of_ne_finset_zero (s := window N) fun q hq => by simp [hq]),
    tsum_eq_sum (s := window N) fun q hq => by simp [hq]]
  congr 1
  exact Finset.sum_congr rfl fun q hq => by rw [ite_eq_left hq]

end DFT

namespace PeriodicSobolev

open Complex DFT Quadrature
open scoped ComplexConjugate

variable {s : ℝ}

/-- The scalar product of the sum of the series with a character gives the coefficient: for
$s > 1/2$, $\varphi \in H^s$ and $q \in \mathbb{Z}$,
$$\int_0^{2\pi} f(x) \, \overline{e^{iqx}} \, dx = 2\pi a_q.$$
-/
theorem intervalIntegral_eval_mul_conj_exp (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (q : ℤ) :
    ∫ x in (0 : ℝ)..2 * π, eval (2 * π) φ x * conj (Complex.exp ((q : ℂ) * x * I))
      = 2 * π * coeff φ q := by
  have h := fourierCoeff_lift_eval (T := 2 * π) hs φ q
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add] at h
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_one_div_cancel hπ, one_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.Periodic.lift_coe, smul_eq_mul, fourier_neg, fourier_coe_two_pi]
  ring

/-- The $L^2$ scalar product of $f$ with a trigonometric polynomial
$v = \sum_{q \in W_N} c_q e^{iqx}$ over the window: for $s > 1/2$ and $\varphi \in H^s$,
$$(f, v) = \int_0^{2\pi} f(x) \overline{v(x)} \, dx = 2\pi \sum_{q \in W_N} a_q
  \overline{c_q}.$$
-/
theorem intervalIntegral_eval_mul_conj_windowTrigPoly (hs : 1 / 2 < s) (N : ℕ)
    (φ : PeriodicSobolev s) (c : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..2 * π, eval (2 * π) φ x * conj (windowTrigPoly N c x)
      = 2 * π * ∑ q ∈ window N, coeff φ q * conj (c q) := by
  have hcont : Continuous (eval (2 * π) φ) := continuous_eval hs _ φ
  simp_rw [windowTrigPoly, map_sum, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun q _ => Continuous.intervalIntegrable (by fun_prop)
    _ _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← intervalIntegral_eval_mul_conj_exp hs φ q,
    ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [map_mul]
  ring

/-- The discrete scalar product of $f$ with a trigonometric polynomial
$v = \sum_{q \in W_N} c_q e^{iqx}$ over the window: for $N \ge 1$ and $\varphi \in H^s$,
$$(f, v)_N = \frac{2\pi}{N} \sum_{j=0}^{N-1} f(x_j) \overline{v(x_j)} = 2\pi \sum_{q \in W_N}
  \tilde f_q \overline{c_q},$$
where $x_j = 2\pi j/N$ and $\tilde f_q$ are the discrete Fourier coefficients of $f$ over the
window, as in `PeriodicSobolev.dftCoeff_eval_window`. -/
theorem discreteInner_eval_windowTrigPoly {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s)
    (c : ℤ → ℂ) :
    ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ Finset.range N,
        eval (2 * π) φ (angleNode N j) * conj (windowTrigPoly N c (angleNode N j))
      = 2 * π * ∑ q ∈ window N,
          DFT.coeff N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) (q + ((N / 2 : ℕ) : ℤ)).toNat
            * conj (c q) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp_rw [windowTrigPoly, map_sum, Finset.mul_sum, DFT.coeff_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : (((q + ((N / 2 : ℕ) : ℤ)).toNat : ℕ) : ℤ) + -((N / 2 : ℕ) : ℤ) = q := by
    rw [mem_window] at hq
    omega
  simp_rw [hq']
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconj : conj (Complex.exp ((q : ℂ) * (angleNode N j : ℝ) * I))
      = Complex.exp (-((q : ℂ) * (angleNode N j : ℝ) * I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
    ring
  rw [map_mul, hconj]
  push_cast
  field_simp

/-- **The estimate of the discrete scalar product.** Let $s > 1/2$, $N \ge 1$ and $\varphi \in H^s$,
let $f = \sum_m a_m e^{imx}$, and let $v = \sum_{q \in W_N} c_q e^{iqx}$ be a trigonometric
polynomial over the window. Then
$$|(f, v) - (f, v)_N| \le \sqrt{2\pi} \sqrt{2\zeta(2s)} \, 2^s N^{-s} \|\varphi\|_s
  \|v\|_{L^2(0, 2\pi)},$$
where $(f, g) = \int_0^{2\pi} f \bar g$ and $(f, g)_N = (2\pi/N) \sum_{j<N} f(x_j)
\overline{g(x_j)}$ with $x_j = 2\pi j/N$. This is the third unnumbered estimate of
[quarteroni2000numerical], §10.9, in coefficient form.

The idea of the proof: the difference is $2\pi \sum_{q \in W_N} (a_q - \tilde f_q)
\overline{c_q} = -2\pi \sum_{q \in W_N} \bigl(\sum_{j \ne 0} a_{q + jN}\bigr) \overline{c_q}$.
The Cauchy–Schwarz inequality over the window, the $\ell^2$ aliasing bound and Parseval's
identity for $v$ finish the proof. -/
theorem norm_intervalIntegral_sub_discreteInner_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) (c : ℤ → ℂ) :
    ‖(∫ x in (0 : ℝ)..2 * π, eval (2 * π) φ x * conj (windowTrigPoly N c x))
        - ((2 * π / N : ℝ) : ℂ) * ∑ j ∈ Finset.range N,
            eval (2 * π) φ (angleNode N j) * conj (windowTrigPoly N c (angleNode N j))‖
      ≤ √(2 * π) * √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖
        * √(∫ x in (0 : ℝ)..2 * π, ‖windowTrigPoly N c x‖ ^ 2) := by
  rw [intervalIntegral_eval_mul_conj_windowTrigPoly hs N φ c,
    discreteInner_eval_windowTrigPoly hN φ c, ← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ q ∈ window N, coeff φ q * conj (c q)
      - DFT.coeff N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) (q + ((N / 2 : ℕ) : ℤ)).toNat
        * conj (c q) = -(aliasTail N φ q * conj (c q)) := by
    intro q hq
    rw [dftCoeff_eval_window hs hN φ hq]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, mul_neg, norm_neg, norm_mul]
  have hπ : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hπ]
  -- Cauchy–Schwarz over the window
  have hcs : ‖∑ q ∈ window N, aliasTail N φ q * conj (c q)‖
      ≤ √(∑ q ∈ window N, ‖aliasTail N φ q‖ ^ 2) * √(∑ q ∈ window N, ‖c q‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul, RCLike.norm_conj]
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun q _ => by positivity),
      ← Real.sqrt_sq (Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  -- the aliasing bound and Parseval
  have halias : √(∑ q ∈ window N, ‖aliasTail N φ q‖ ^ 2)
      ≤ √(2 * zetaReal (2 * s)) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖ := by
    have h := (sum_window_norm_aliasTail_sq_le hs hN φ).trans
      (mul_le_mul_of_nonneg_left (windowTailNormSq_le N φ)
        (mul_nonneg (by positivity) (mul_nonneg two_pos.le (zetaReal_nonneg _))))
    refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
    rw [mul_assoc, sqrt_bound, Real.sqrt_mul (mul_nonneg two_pos.le (zetaReal_nonneg _)),
      Real.sqrt_sq (norm_nonneg _), div_two_rpow_neg s hN]
    ring
  have hpar : √(∑ q ∈ window N, ‖c q‖ ^ 2)
      = (√(2 * π))⁻¹ * √(∫ x in (0 : ℝ)..2 * π, ‖windowTrigPoly N c x‖ ^ 2) := by
    rw [intervalIntegral_norm_windowTrigPoly_sq,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π) (∑ q ∈ window N, ‖c q‖ ^ 2), ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne', one_mul]
  have h2 : 2 * π * (√(2 * π))⁻¹ = √(2 * π) := by
    rw [mul_inv_eq_iff_eq_mul₀ (Real.sqrt_pos.mpr (by positivity)).ne',
      Real.mul_self_sqrt (by positivity)]
  calc 2 * π * ‖∑ q ∈ window N, aliasTail N φ q * conj (c q)‖
      ≤ 2 * π * (√(∑ q ∈ window N, ‖aliasTail N φ q‖ ^ 2) * √(∑ q ∈ window N, ‖c q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ 2 * π * ((√(2 * zetaReal (2 * s)) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖)
          * √(∑ q ∈ window N, ‖c q‖ ^ 2)) := by gcongr
    _ = (2 * π * (√(2 * π))⁻¹) * ((√(2 * zetaReal (2 * s)) * (2 : ℝ) ^ s * (N : ℝ) ^ (-s) * ‖φ‖)
          * √(∫ x in (0 : ℝ)..2 * π, ‖windowTrigPoly N c x‖ ^ 2)) := by rw [hpar]; ring
    _ = _ := by rw [h2]; ring

end PeriodicSobolev

/-! ### The trigonometric interpolant in the Sobolev scale -/

namespace PeriodicSobolev

open Complex DFT Quadrature

variable {s : ℝ}

/-- The **trigonometric interpolant** $\mathcal{I}_n \varphi$ of [han2009theoretical], §3.7 and
Theorem 7.5.7: the trigonometric polynomial of degree at most $n$ that agrees with the sum $f$
of the series of $\varphi \in H^s$ at the $2n + 1$ equispaced nodes $2\pi j/(2n + 1)$. Its
coefficients on the window $\{-n, \dots, n\}$ are the discrete Fourier coefficients of $f$ over
that window, and its other coefficients are $0$.

It is an element of $H^r$ for any $r$, because only finitely many of its coefficients are
nonzero. -/
noncomputable def trigInterp (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) : PeriodicSobolev r :=
  ofCoeff r (fun q => if q ∈ window (2 * n + 1)
      then DFT.coeff (2 * n + 1) (-(n : ℤ)) (eval (2 * π) φ) (q + n).toNat else 0)
    (memℓp_two_iff.2 (summable_of_ne_finset_zero (s := window (2 * n + 1)) fun q hq => by
      simp [hq]))

/-- The coefficients of the interpolant $\mathcal{I}_n \varphi$: on the window $\{-n, \dots, n\}$,
the discrete Fourier coefficients of $f$ on $2n + 1$ nodes; outside the window, $0$. -/
theorem coeff_trigInterp (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) (q : ℤ) :
    coeff (trigInterp r n φ) q = if q ∈ window (2 * n + 1)
      then DFT.coeff (2 * n + 1) (-(n : ℤ)) (eval (2 * π) φ) (q + n).toNat else 0 := by
  rw [trigInterp, coeff_ofCoeff]

/-- On the window, the coefficient of the interpolant is the exact one plus the aliasing tail: for
$s > 1/2$ and $q \in \{-n, \dots, n\}$,
$$(\mathcal{I}_n \varphi)_q = a_q + \sum_{j \ne 0} a_{q + j(2n+1)}.$$
-/
theorem coeff_trigInterp_of_mem (hs : 1 / 2 < s) (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s)
    {q : ℤ} (hq : q ∈ window (2 * n + 1)) :
    coeff (trigInterp r n φ) q = coeff φ q + aliasTail (2 * n + 1) φ q := by
  rw [coeff_trigInterp, ite_eq_left hq]
  have h := dftCoeff_eval_window hs (by omega : 0 < 2 * n + 1) φ hq
  have hn : ((2 * n + 1) / 2 : ℕ) = n := by omega
  simp only [hn] at h
  exact h

/-- The sum of the series of the interpolant $\mathcal{I}_n \varphi$ is the discrete Fourier series
of $f$ on $2n + 1$ nodes over the window $\{-n, \dots, n\}$.

No hypothesis on $s$ is needed: the interpolant is built from the values of the function
`PeriodicSobolev.eval (2 * π) φ`. -/
theorem eval_trigInterp (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) :
    eval (2 * π) (trigInterp r n φ)
      = DFT.interp (2 * n + 1) (-(n : ℤ)) (eval (2 * π) φ) := by
  funext x
  rw [eval, tsum_eq_sum (s := window (2 * n + 1)) fun q hq => by simp [coeff_trigInterp, hq],
    DFT.interp_def]
  have hn : ((2 * n + 1) / 2 : ℕ) = n := by omega
  rw [← sum_range_eq_sum_window (2 * n + 1)
    (fun q => coeff (trigInterp r n φ) q * periodicChar (2 * π) q x), hn]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hq : (k : ℤ) + -(n : ℤ) ∈ window (2 * n + 1) := by rw [mem_window, hn]; omega
  have hk' : ((k : ℤ) + -(n : ℤ) + n).toNat = k := by omega
  rw [coeff_trigInterp, ite_eq_left hq, hk', periodicChar_eq_fourier, fourier_coe_two_pi]

/-- **The interpolation property.** For every $\varphi \in H^s$, the interpolant
$\mathcal{I}_n \varphi$ agrees with the sum $f$ of the series of $\varphi$ at the $2n + 1$
equispaced nodes:
$$\mathcal{I}_n \varphi(x_j) = f(x_j), \qquad x_j = \frac{2\pi j}{2n + 1}, \quad j < 2n + 1.$$
-/
theorem eval_trigInterp_angleNode (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) {j : ℕ}
    (hj : j < 2 * n + 1) :
    eval (2 * π) (trigInterp r n φ) (angleNode (2 * n + 1) j)
      = eval (2 * π) φ (angleNode (2 * n + 1) j) := by
  rw [eval_trigInterp]
  exact DFT.interp_angleNode (by omega) _ _ hj

/-- For $s > 1/2$ and $r \le s$, the coefficients of $\varphi - \mathcal{I}_n \varphi$ in $H^r$ are
the coefficients $d_m$ of the interpolation error on $2n + 1$ nodes.

Here $\varphi$ is read in $H^r$ through the inclusion `PeriodicSobolev.incl`. -/
theorem coeff_incl_sub_trigInterp (hs : 1 / 2 < s) {r : ℝ} (hrs : r ≤ s) (n : ℕ)
    (φ : PeriodicSobolev s) :
    coeff (incl hrs φ - trigInterp r n φ) = interpErrorCoeff (2 * n + 1) φ := by
  funext q
  rw [coeff_sub, Pi.sub_apply, coeff_incl, interpErrorCoeff]
  split_ifs with hq
  · rw [coeff_trigInterp_of_mem hs r n φ hq]
    ring
  · rw [coeff_trigInterp, ite_eq_right hq, sub_zero]

/-- On the window $\{-n, \dots, n\}$ the weight is at most $n^r$: for $r \ge 0$, $n \ge 1$ and
$q \in W_{2n+1}$, $w_r(q) \le n^r$. -/
theorem weight_le_of_mem_window {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 0 < n) {q : ℤ}
    (hq : q ∈ window (2 * n + 1)) : periodicSobolevWeight r q ≤ (n : ℝ) ^ r := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [periodicSobolevWeight_zero]
    exact Real.one_le_rpow hn1 hr
  · rw [periodicSobolevWeight_of_ne_zero r hq0]
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hr
    have h3 : |q| ≤ (n : ℤ) := by
      have := two_mul_abs_le_of_mem_window hq
      omega
    have h4 := (Int.cast_le (R := ℝ)).mpr h3
    rwa [Int.cast_abs, Int.cast_natCast] at h4

/-- For $r \le s$ and $m \notin \{-n, \dots, n\}$, $w_r(m)^2 \le (n + 1)^{2(r - s)} w_s(m)^2$,
because $|m| \ge n + 1$. -/
private theorem weight_sq_le_of_not_mem_window {r : ℝ} (hrs : r ≤ s) {n : ℕ} {m : ℤ}
    (hm : m ∉ window (2 * n + 1)) :
    periodicSobolevWeight r m ^ 2
      ≤ ((n : ℝ) + 1) ^ (2 * (r - s)) * periodicSobolevWeight s m ^ 2 := by
  have h := le_two_mul_abs_of_not_mem_window hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  have habs : (n : ℝ) + 1 ≤ |(m : ℝ)| := by
    have h3 : (n : ℤ) + 1 ≤ |m| := by omega
    have h4 := (Int.cast_le (R := ℝ)).mpr h3
    rwa [Int.cast_abs, Int.cast_add, Int.cast_natCast, Int.cast_one] at h4
  have hpos : (0 : ℝ) < |(m : ℝ)| := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [periodicSobolevWeight_sq r hm0, periodicSobolevWeight_sq s hm0,
    show (2 : ℝ) * r = 2 * (r - s) + 2 * s by ring, Real.rpow_add hpos]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) habs (by linarith)

/-- **Theorem 7.5.7** of [han2009theoretical]. Let $s > 1/2$, $0 \le r \le s$, $n \ge 1$ and
$\varphi \in H^s$. Then the trigonometric interpolant $\mathcal{I}_n \varphi$ satisfies
$$\|\varphi - \mathcal{I}_n \varphi\|_r \le c \, n^{r - s} \|\varphi\|_s, \qquad c = \sqrt{1 +
  2\zeta(2s)}.$$

Here $\varphi$ is read in $H^r$ through `PeriodicSobolev.incl`. The idea of the proof: the
coefficients of $\varphi - \mathcal{I}_n \varphi$ are the aliasing tails on the window
$\{-n, \dots, n\}$ and the exact coefficients outside it. The $r$-weight is at most $n^r$ on the
window, and at most $(n + 1)^{r - s}$ times the $s$-weight outside it. So the $\ell^2$ aliasing
bound and the energy outside the window give the rate $n^{r - s}$. -/
theorem norm_incl_sub_trigInterp_le (hs : 1 / 2 < s) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    {n : ℕ} (hn : 0 < n) (φ : PeriodicSobolev s) :
    ‖incl hrs φ - trigInterp r n φ‖ ≤ √(1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (r - s) * ‖φ‖ := by
  have hN : 0 < 2 * n + 1 := by omega
  have hz := zetaReal_nonneg (2 * s)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set ψ := incl hrs φ - trigInterp r n φ with hψ
  have hsum := hasSum_norm_sq ψ
  rw [coeff_incl_sub_trigInterp hs hrs n φ] at hsum
  have hsplit := hsum.summable.tsum_eq_sum_add_tsum_ite (window (2 * n + 1))
  -- the window part
  have hwin : ∑ m ∈ window (2 * n + 1),
      (periodicSobolevWeight r m * ‖interpErrorCoeff (2 * n + 1) φ m‖) ^ 2
      ≤ ((n : ℝ) ^ r) ^ 2 * ∑ m ∈ window (2 * n + 1), ‖aliasTail (2 * n + 1) φ m‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [norm_interpErrorCoeff, ite_eq_left hm, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (periodicSobolevWeight_pos r m).le (weight_le_of_mem_window hr hn hm) 2)
      (by positivity)
  have hwin2 := sum_window_norm_aliasTail_sq_le hs hN φ
  have hN2 : ((((2 * n + 1 : ℕ) : ℝ) / 2) ^ (2 * s))⁻¹ ≤ ((n : ℝ) ^ (2 * s))⁻¹ := by
    refine inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
    push_cast
    linarith
  -- the part outside the window
  have hout : ∑' m : ℤ, (if m ∈ window (2 * n + 1) then (0 : ℝ)
      else (periodicSobolevWeight r m * ‖interpErrorCoeff (2 * n + 1) φ m‖) ^ 2)
      ≤ ((n : ℝ) + 1) ^ (2 * (r - s)) * windowTailNormSq (2 * n + 1) φ := by
    refine tsum_ite_window_le_mul_windowTailNormSq φ (fun m => by positivity) fun m hm => ?_
    rw [norm_interpErrorCoeff, ite_eq_right hm, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_sq_le_of_not_mem_window hrs hm) (by positivity)
  have hout2 : ((n : ℝ) + 1) ^ (2 * (r - s)) ≤ (n : ℝ) ^ (2 * (r - s)) :=
    Real.rpow_le_rpow_of_nonpos hnpos (by linarith) (by linarith)
  -- the rates
  have hrate : ((n : ℝ) ^ r) ^ 2 * ((n : ℝ) ^ (2 * s))⁻¹ = (n : ℝ) ^ (2 * (r - s)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_neg hnpos.le,
      ← Real.rpow_add hnpos]
    congr 1
    push_cast
    ring
  have htail := windowTailNormSq_le (2 * n + 1) φ
  have htail0 := windowTailNormSq_nonneg (2 * n + 1) φ
  -- assemble the squared bound
  have hsq : ‖ψ‖ ^ 2 ≤ (1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (2 * (r - s)) * ‖φ‖ ^ 2 := by
    rw [← hsum.tsum_eq, hsplit]
    have hA : ∑ m ∈ window (2 * n + 1),
        (periodicSobolevWeight r m * ‖interpErrorCoeff (2 * n + 1) φ m‖) ^ 2
        ≤ (n : ℝ) ^ (2 * (r - s)) * (2 * zetaReal (2 * s)) * windowTailNormSq (2 * n + 1) φ := by
      refine hwin.trans ?_
      calc ((n : ℝ) ^ r) ^ 2 * ∑ m ∈ window (2 * n + 1), ‖aliasTail (2 * n + 1) φ m‖ ^ 2
          ≤ ((n : ℝ) ^ r) ^ 2 * (((((2 * n + 1 : ℕ) : ℝ) / 2) ^ (2 * s))⁻¹
              * (2 * zetaReal (2 * s)) * windowTailNormSq (2 * n + 1) φ) :=
            mul_le_mul_of_nonneg_left hwin2 (by positivity)
        _ ≤ ((n : ℝ) ^ r) ^ 2 * (((n : ℝ) ^ (2 * s))⁻¹
              * (2 * zetaReal (2 * s)) * windowTailNormSq (2 * n + 1) φ) := by gcongr
        _ = _ := by rw [← hrate]; ring
    have hB : ∑' m : ℤ, (if m ∈ window (2 * n + 1) then (0 : ℝ)
        else (periodicSobolevWeight r m * ‖interpErrorCoeff (2 * n + 1) φ m‖) ^ 2)
        ≤ (n : ℝ) ^ (2 * (r - s)) * windowTailNormSq (2 * n + 1) φ :=
      hout.trans (mul_le_mul_of_nonneg_right hout2 htail0)
    calc _ ≤ (n : ℝ) ^ (2 * (r - s)) * (2 * zetaReal (2 * s)) * windowTailNormSq (2 * n + 1) φ
          + (n : ℝ) ^ (2 * (r - s)) * windowTailNormSq (2 * n + 1) φ := add_le_add hA hB
      _ = (1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (2 * (r - s))
          * windowTailNormSq (2 * n + 1) φ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)
  have hsqrt : √((1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (2 * (r - s)) * ‖φ‖ ^ 2)
      = √(1 + 2 * zetaReal (2 * s)) * (n : ℝ) ^ (r - s) * ‖φ‖ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_eq_rpow ((n : ℝ) ^ (2 * (r - s))), ← Real.rpow_mul hnpos.le]
    congr 3
    ring
  rw [← Real.sqrt_sq (norm_nonneg ψ), ← hsqrt]
  exact Real.sqrt_le_sqrt hsq

end PeriodicSobolev
