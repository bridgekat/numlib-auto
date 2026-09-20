import Numlib.Analysis.Fourier.DFT
import Numlib.Analysis.Sobolev.Periodic

/-!
# Aliasing: the error of the discrete Fourier coefficients

The `N`-point discrete Fourier coefficient of a periodic function at a frequency `k` is the sum of
its exact coefficients at all frequencies congruent to `k` modulo `N`
(`DFT.coeff_eq_tsum_fourierCoeff`): the discrete coefficient is the exact one plus the **aliasing
tail** `∑_{j ≠ 0} a_{k + jN}`. This file bounds that tail for a function with coefficients in the
periodic Sobolev space `PeriodicSobolev s`, `s > 1/2`, and derives from it the error estimates for
trigonometric interpolation at equispaced nodes.

## The window and the tiling

`DFT.window N` is the centred window `-(N/2) ≤ k < -(N/2) + N` (integer division) of `N`
consecutive frequencies — the window `m = −N/2` of [quarteroni2000numerical] §10.9 for even `N`,
and `-n, …, n` for `N = 2n + 1`. Three facts about it carry everything:

* `2 |k| ≤ N` on the window and `N ≤ 2 |k|` off it;
* `N |j| ≤ 2 |k + jN|` for `k` in the window and `j ≠ 0`, so the aliased frequencies are far
  from `0`;
* the window tiles `ℤ`: `(k, j) ↦ k + jN` is a bijection `W × ℤ → ℤ`, and for a summable family
  `∑_{k ∈ W} ∑_j g (k + jN) = ∑_m g m` (`DFT.sum_window_tsum_add_mul`).

## The bounds

For `φ ∈ PeriodicSobolev s` with `s > 1/2` and `k` in the window, Cauchy–Schwarz against
`∑_{j ≠ 0} |k + jN|^{-2s} ≤ (N/2)^{-2s} · 2 ζ(2s)` gives

`‖∑_{j ≠ 0} a_{k + jN}‖ ≤ (N/2)^{-s} √(2 ζ(2s)) √(∑_{j ≠ 0} (w(k + jN) ‖a_{k + jN}‖)²)`

(`PeriodicSobolev.norm_aliasTail_le`), and the tiling turns the sum over the window of the
right-hand sides into the weighted energy outside the window, `windowTailNormSq N φ ≤ ‖φ‖²`.
The results are the **`ℓ²` aliasing bound** `PeriodicSobolev.sum_window_norm_aliasTail_sq_le`,
the **`ℓ¹` aliasing bound** `sum_window_norm_aliasTail_le` (with the extra `√N` of Cauchy–Schwarz
over the `N` frequencies of the window), and the `ℓ¹` and `ℓ²` tails outside the window,
`tsum_norm_coeff_notMem_window_le` and `tsum_norm_coeff_sq_notMem_window_le`.

## The interpolation estimates

For `f = eval (2π) φ` the discrete coefficients over the centred window are
`f̃_q = a_q + aliasTail N φ q` (`PeriodicSobolev.dftCoeff_eval_window`), and the interpolation
error `f − Π_N f` is the trigonometric series with coefficients `interpErrorCoeff`: `−aliasTail`
on the window, `a_m` outside. Parseval and the bounds above give the three unnumbered estimates of
[quarteroni2000numerical] §10.9 in coefficient form:

* `PeriodicSobolev.sqrt_intervalIntegral_norm_eval_sub_interp_sq_le`:
  `‖f − Π_N f‖_{L²(0,2π)} ≤ √(2π (1 + 2 ζ(2s))) 2^s N^{-s} ‖φ‖`;
* `PeriodicSobolev.norm_eval_sub_interp_le`:
  `max |f − Π_N f| ≤ 2 √(2 ζ(2s)) 2^s N^{1/2 − s} ‖φ‖`;
* `PeriodicSobolev.norm_intervalIntegral_sub_discreteInner_le`:
  `|(f, v_N) − (f, v_N)_N| ≤ √(2π) √(2 ζ(2s)) 2^s N^{-s} ‖φ‖ ‖v_N‖_{L²}` for every trigonometric
  polynomial `v_N = DFT.windowTrigPoly N c` over the window.

The book's norm `‖f‖_s` is reached through `PeriodicSobolev.ofSmooth` of
`Numlib/Analysis/Sobolev/Periodic/Smooth`, which the surface does. The constants are explicit
but not sharp; the book leaves them unspecified.

## The interpolant in the Sobolev scale

`PeriodicSobolev.trigInterp r n φ` is the trigonometric interpolant `𝓘_n φ` of
[han2009theoretical] §3.7 — degree at most `n`, the `2n + 1` equispaced nodes — read as an
element of `PeriodicSobolev r` for any `r`; `eval_trigInterp_angleNode` is the interpolation
property and `norm_incl_sub_trigInterp_le` is [han2009theoretical] Theorem 7.5.7,
`‖φ − 𝓘_n φ‖_r ≤ √(1 + 2 ζ(2s)) n^{r − s} ‖φ‖_s` for `0 ≤ r ≤ s`, `s > 1/2`: the same aliasing
bound read in the `H^r` norm.
-/

open scoped Real

/-! ### The centred window -/


namespace DFT

/-- The centred window of `N` consecutive frequencies, `-(N/2) ≤ k < -(N/2) + N` (integer
division): the window `m = −N/2` of [quarteroni2000numerical] (10.50) for even `N`, and
`-n, …, n` for `N = 2n + 1`. -/
def window (N : ℕ) : Finset ℤ := Finset.Ico (-((N / 2 : ℕ) : ℤ)) (-((N / 2 : ℕ) : ℤ) + N)

/-- Membership in the centred window. -/
theorem mem_window {N : ℕ} {k : ℤ} :
    k ∈ window N ↔ -((N / 2 : ℕ) : ℤ) ≤ k ∧ k < -((N / 2 : ℕ) : ℤ) + N := by
  rw [window, Finset.mem_Ico]

/-- The window has `N` elements. -/
theorem card_window (N : ℕ) : (window N).card = N := by
  rw [window, Int.card_Ico]
  omega

/-- On the window, `|k| ≤ N/2`. -/
theorem two_mul_abs_le_of_mem_window {N : ℕ} {k : ℤ} (hk : k ∈ window N) : 2 * |k| ≤ N := by
  rw [mem_window] at hk
  rcases le_or_gt 0 k with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

/-- Off the window, `|k| ≥ N/2`. -/
theorem le_two_mul_abs_of_not_mem_window {N : ℕ} {k : ℤ} (hk : k ∉ window N) :
    (N : ℤ) ≤ 2 * |k| := by
  rw [mem_window, not_and_or, not_le, not_lt] at hk
  rcases le_or_gt 0 k with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_neg h]; omega

/-- The aliased frequencies are far from `0`: for `k` on the window and `j ≠ 0`,
`|k + jN| ≥ N |j| / 2`. -/
theorem mul_abs_le_two_mul_abs_add_mul {N : ℕ} {k j : ℤ} (hk : k ∈ window N) (hj : j ≠ 0) :
    (N : ℤ) * |j| ≤ 2 * |k + j * N| := by
  have h1 := two_mul_abs_le_of_mem_window hk
  have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have h2 := le_abs_self (k + j * N)
  have h3 := neg_le_abs (k + j * N)
  have h4 := le_abs_self k
  have h5 := neg_le_abs k
  rcases le_or_gt 0 j with hj0 | hj0
  · have hj1 : 1 ≤ j := by omega
    rw [abs_of_nonneg hj0]
    nlinarith
  · have hj1 : j ≤ -1 := by omega
    rw [abs_of_neg hj0]
    nlinarith

/-- The aliased frequencies are nonzero. -/
theorem add_mul_ne_zero_of_mem_window {N : ℕ} (hN : 0 < N) {k j : ℤ} (hk : k ∈ window N)
    (hj : j ≠ 0) :
    k + j * N ≠ 0 := by
  intro h
  have := mul_abs_le_two_mul_abs_add_mul hk hj
  rw [h, abs_zero, mul_zero] at this
  have : (0 : ℤ) < N * |j| := mul_pos (by exact_mod_cast hN) (abs_pos.mpr hj)
  omega

/-- The unique representative in the window of a residue class modulo `N`. -/
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
    have hk' : k - m₀ = (m - m₀) - N * c := by linarith
    have : (m - m₀) % N = k - m₀ := by
      rw [show m - m₀ = (k - m₀) + N * c by linarith, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt] <;> omega
    omega

end DFT

namespace DFT

/-- **The window tiles `ℤ`**: every integer is `k + j N` for exactly one `k` in the window and one
`j`, so for a summable family `∑_{k ∈ W} ∑_j g (k + j N) = ∑_m g m`. -/
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

/-- **The aliasing tail** at frequency `k` with modulus `N`: `∑_{j ≠ 0} a_{k + j N}`, the amount by
which the `N`-point discrete Fourier coefficient at `k` differs from the exact one. -/
noncomputable def aliasTail (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : ℂ :=
  ∑' j : ℤ, if j = 0 then 0 else coeff φ (k + j * N)

/-- The weighted energy aliased onto `k`: `∑_{j ≠ 0} (w(k + j N) ‖a_{k + j N}‖)²`. -/
noncomputable def aliasNormSq (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : ℝ :=
  ∑' j : ℤ, if j = 0 then 0
    else (periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖) ^ 2

/-- The weighted energy outside the window: `∑_{m ∉ W} (w(m) ‖a_m‖)²`, at most `‖φ‖²`. -/
noncomputable def windowTailNormSq (N : ℕ) (φ : PeriodicSobolev s) : ℝ :=
  ∑' m : ℤ, if m ∈ window N then 0 else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2

/-- The energy outside the window is nonnegative. -/
theorem windowTailNormSq_nonneg (N : ℕ) (φ : PeriodicSobolev s) : 0 ≤ windowTailNormSq N φ :=
  tsum_nonneg fun m => by split_ifs <;> positivity

private theorem summable_ite_window (N : ℕ) (φ : PeriodicSobolev s) :
    Summable fun m : ℤ => if m ∈ window N then (0 : ℝ)
      else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2 :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
    (fun m => by split_ifs <;> [positivity; exact le_rfl]) (hasSum_norm_sq φ).summable

/-- The energy outside the window is at most the whole energy `‖φ‖²`. -/
theorem windowTailNormSq_le (N : ℕ) (φ : PeriodicSobolev s) : windowTailNormSq N φ ≤ ‖φ‖ ^ 2 :=
  hasSum_le (fun m => by split_ifs <;> [positivity; exact le_rfl])
    (summable_ite_window N φ).hasSum (hasSum_norm_sq φ)

private theorem injective_add_mul {N : ℕ} (hN : 0 < N) (k : ℤ) :
    Function.Injective fun j : ℤ => k + j * N := by
  intro a b hab
  have : a * (N : ℤ) = b * N := by simpa using hab
  exact mul_right_cancel₀ (by exact_mod_cast hN.ne') this

private theorem summable_aliasNormSq_term {N : ℕ} (hN : 0 < N) (φ : PeriodicSobolev s) (k : ℤ) :
    Summable fun j : ℤ => if j = 0 then (0 : ℝ)
      else (periodicSobolevWeight s (k + j * N) * ‖coeff φ (k + j * N)‖) ^ 2 :=
  Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity)
    (fun j => by
      simp only [Function.comp_apply]
      split_ifs <;> [positivity; exact le_rfl])
    ((hasSum_norm_sq φ).summable.comp_injective (injective_add_mul hN k))

/-- The aliased energy is nonnegative. -/
theorem aliasNormSq_nonneg (N : ℕ) (φ : PeriodicSobolev s) (k : ℤ) : 0 ≤ aliasNormSq N φ k :=
  tsum_nonneg fun j => by split_ifs <;> positivity

/-- The Cauchy–Schwarz partner: `j ↦ w(k + j N)⁻¹` off `j = 0`. -/
private noncomputable def invWeight (s : ℝ) (N : ℕ) (k : ℤ) (j : ℤ) : ℝ :=
  if j = 0 then 0 else (periodicSobolevWeight s (k + j * N))⁻¹

private theorem invWeight_nonneg (s : ℝ) (N : ℕ) (k j : ℤ) : 0 ≤ invWeight s N k j := by
  rw [invWeight]
  split_ifs
  · exact le_rfl
  · exact (inv_pos.mpr (periodicSobolevWeight_pos _ _)).le

/-- Off `j = 0` and for `k` in the window, `w(k + j N)⁻² ≤ (N/2)^{-2s} |j|^{-2s}`. -/
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

private theorem sqrt_bound (s : ℝ) {N : ℕ} (hN : 0 < N) :
    √((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)))
      = ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) := by
  have hpos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
  rw [Real.sqrt_mul (by positivity), ← Real.rpow_neg hpos.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hpos.le]
  congr 2
  ring

/-- **Cauchy–Schwarz on the aliasing tail**: for `k` in the window,
`∑_{j ≠ 0} ‖a_{k + j N}‖ ≤ (N/2)^{-s} √(2 ζ(2 s)) √(aliasNormSq N φ k)`, and the family is
summable. -/
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
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hysq, ← sqrt_bound s hN]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (tsum_invWeight_sq_le hs hN hk))
    (Real.sqrt_nonneg _)

/-- **The aliasing tail is small**: for `k` on the window,
`‖∑_{j ≠ 0} a_{k + jN}‖ ≤ (N/2)^{-s} √(2 ζ(2s)) √(aliasNormSq N φ k)`. -/
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

/-- The squared form: `‖∑_{j ≠ 0} a_{k + j N}‖² ≤ (N/2)^{-2s} · 2 ζ(2 s) · aliasNormSq N φ k`. -/
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

/-- **The window tiles the frequencies**: the aliased energies over the window add up to the
energy outside it. -/
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

/-- **The `ℓ²` aliasing bound**: the discrete coefficients over the window differ from the exact
ones by at most `(N/2)^{-2s} · 2 ζ(2s)` times the weighted energy outside the window, in the sum
of squares. -/
theorem sum_window_norm_aliasTail_sq_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, ‖aliasTail N φ k‖ ^ 2
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s)) * windowTailNormSq N φ := by
  calc ∑ k ∈ window N, ‖aliasTail N φ k‖ ^ 2
      ≤ ∑ k ∈ window N, (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (2 * zetaReal (2 * s))
          * aliasNormSq N φ k := Finset.sum_le_sum fun k hk => norm_aliasTail_sq_le hs hN φ hk
    _ = _ := by rw [← Finset.mul_sum, sum_window_aliasNormSq hN φ]

/-- Cauchy–Schwarz over the window: `∑_{k ∈ W} √(t k) ≤ √N √(∑_{k ∈ W} t k)`. -/
private theorem sum_window_sqrt_le (N : ℕ) {t : ℤ → ℝ} (ht : ∀ k, 0 ≤ t k) :
    ∑ k ∈ window N, √(t k) ≤ √(N : ℝ) * √(∑ k ∈ window N, t k) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (window N) (fun _ => (1 : ℝ)) fun k => √(t k)
  simp only [one_mul, one_pow, Finset.sum_const, card_window, nsmul_eq_mul, mul_one,
    Real.sq_sqrt (ht _)] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg N), ← Real.sqrt_sq (Finset.sum_nonneg fun k _ =>
    Real.sqrt_nonneg (t k))]
  exact Real.sqrt_le_sqrt h

/-- **The `ℓ¹` aliasing bound**: `∑_{k ∈ W} ‖∑_{j ≠ 0} a_{k + jN}‖ ≤ (N/2)^{-s} √(2 ζ(2s)) √N
√(windowTailNormSq N φ)`. -/
theorem sum_window_norm_aliasTail_le (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑ k ∈ window N, ‖aliasTail N φ k‖
      ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * (√(N : ℝ) * √(windowTailNormSq N φ)) := by
  calc ∑ k ∈ window N, ‖aliasTail N φ k‖
      ≤ ∑ k ∈ window N, ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(aliasNormSq N φ k) :=
        Finset.sum_le_sum fun k hk => norm_aliasTail_le hs hN φ hk
    _ = ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * ∑ k ∈ window N, √(aliasNormSq N φ k) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← sum_window_aliasNormSq hN φ]
        exact sum_window_sqrt_le N (aliasNormSq_nonneg N φ)

/-- **The `ℓ¹` tail outside the window**: `∑_{m ∉ W} ‖a_m‖ ≤ (N/2)^{-s} √(2 ζ(2s)) √N
√(windowTailNormSq N φ)`, by tiling the complement of the window with the aliasing tails. -/
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
    _ = ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * ∑ k ∈ window N, √(aliasNormSq N φ k) := by
        rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← sum_window_aliasNormSq hN φ]
        exact sum_window_sqrt_le N (aliasNormSq_nonneg N φ)

/-- Outside the window `|m| ≥ N/2`, so `‖a_m‖² ≤ (N/2)^{-2s} (w(m) ‖a_m‖)²`. -/
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

/-- **The `ℓ²` tail outside the window**: `∑_{m ∉ W} ‖a_m‖² ≤ (N/2)^{-2s} windowTailNormSq N φ`. -/
theorem tsum_norm_coeff_sq_notMem_window_le (hs : 0 ≤ s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∑' m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ ^ 2)
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * windowTailNormSq N φ := by
  rw [windowTailNormSq, ← tsum_mul_left]
  have hle : ∀ m : ℤ, (if m ∈ window N then (0 : ℝ) else ‖coeff φ m‖ ^ 2)
      ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹ * (if m ∈ window N then (0 : ℝ)
        else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) := by
    intro m
    split_ifs with hm
    · simp
    · exact norm_coeff_sq_le_of_not_mem_window hs hN φ hm
  exact hasSum_le hle (Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) hle
    ((summable_ite_window N φ).mul_left _)).hasSum ((summable_ite_window N φ).mul_left _).hasSum

end PeriodicSobolev

/-! ### The discrete Fourier coefficients of the sum of the series -/

namespace DFT

open Complex

/-- The character `exp (i p x)` is the Fourier monomial `fourier p` of the circle of circumference
`2 π`, evaluated at the class of `x`. -/
theorem fourier_coe_two_pi (p : ℤ) (x : ℝ) :
    (fourier p (x : AddCircle (2 * π)) : ℂ) = Complex.exp ((p : ℂ) * x * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  field_simp

/-- A sum over `k < N` of the frequencies `k − N/2` is a sum over the centred window. -/
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

/-- **The discrete Fourier coefficients of the sum of the series are the aliasing sums**: for
`s > 1/2`, `DFT.coeff N m (eval (2π) φ) k = ∑_j a_{k + m + j N}`. Mathlib's aliasing identity
`DFT.coeff_eq_tsum_fourierCoeff`, with the Fourier coefficients of `eval` read off by
`fourierCoeff_lift_eval`. -/
theorem dftCoeff_eval (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N) (m : ℤ) (φ : PeriodicSobolev s)
    (k : ℕ) :
    DFT.coeff N m (eval (2 * π) φ) k = ∑' j : ℤ, coeff φ ((k : ℤ) + m + j * N) := by
  have hper := eval_periodic (T := 2 * π) (Fact.out : (0 : ℝ) < 2 * π).ne' φ
  have hcont : Continuous (eval (2 * π) φ) := continuous_eval hs _ φ
  have h := DFT.coeff_eq_tsum_fourierCoeff hN m
    (f := ⟨hper.lift, hper.continuous_lift hcont⟩) (summable_fourierCoeff_lift_eval hs φ) k
  simp only [ContinuousMap.coe_mk, Function.Periodic.lift_coe, fourierCoeff_lift_eval hs] at h
  exact h

/-- Over the centred window, the discrete coefficient at the frequency `q` is the exact one plus
the aliasing tail: `f̃_q = a_q + ∑_{j ≠ 0} a_{q + j N}`. -/
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

/-- The coefficients of the interpolation error `eval φ − Π_N (eval φ)`: minus the aliasing tail
on the window, the exact coefficient outside it. -/
noncomputable def interpErrorCoeff (N : ℕ) (φ : PeriodicSobolev s) (m : ℤ) : ℂ :=
  if m ∈ window N then -aliasTail N φ m else coeff φ m

/-- The moduli of the error coefficients. -/
theorem norm_interpErrorCoeff (N : ℕ) (φ : PeriodicSobolev s) (m : ℤ) :
    ‖interpErrorCoeff N φ m‖ = if m ∈ window N then ‖aliasTail N φ m‖ else ‖coeff φ m‖ := by
  rw [interpErrorCoeff]
  split_ifs <;> simp

/-- The error coefficients are absolutely summable: the series of the error converges
uniformly. -/
theorem summable_norm_interpErrorCoeff (hs : 1 / 2 < s) (N : ℕ) (φ : PeriodicSobolev s) :
    Summable fun m => ‖interpErrorCoeff N φ m‖ := by
  have h1 : Summable fun m : ℤ => if m ∈ window N then ‖aliasTail N φ m‖ else 0 :=
    summable_of_ne_finset_zero (s := window N) fun m hm => by simp [hm]
  refine ((summable_norm_coeff hs φ).add h1).of_nonneg_of_le (fun m => norm_nonneg _)
    fun m => ?_
  rw [norm_interpErrorCoeff]
  split_ifs <;> simp

/-- **The interpolation error is a trigonometric series** with coefficients
`interpErrorCoeff`: `eval φ x − Π_N (eval φ) x = ∑_m d_m e^{i m x}`. -/
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

/-! ### The interpolation error in `L²` and in the sup norm -/

namespace PeriodicSobolev

open Complex DFT

variable {s : ℝ}

/-- A summable real family, split into a finite set of indices and the rest. -/
private theorem tsum_eq_sum_add_tsum_ite {g : ℤ → ℝ} (hg : Summable g) (F : Finset ℤ) :
    ∑' m, g m = ∑ m ∈ F, g m + ∑' m, (if m ∈ F then (0 : ℝ) else g m) := by
  have h1 : Summable fun m => if m ∈ F then g m else 0 :=
    summable_of_ne_finset_zero (s := F) fun m hm => by simp [hm]
  have h2 : Summable fun m => if m ∈ F then (0 : ℝ) else g m := by
    refine (hg.indicator (↑F)ᶜ).congr fun m => ?_
    by_cases hm : m ∈ F <;> simp [hm]
  calc ∑' m, g m
      = ∑' m, ((if m ∈ F then g m else 0) + (if m ∈ F then (0 : ℝ) else g m)) :=
        tsum_congr fun m => by split_ifs <;> simp
    _ = (∑' m, if m ∈ F then g m else 0) + ∑' m, (if m ∈ F then (0 : ℝ) else g m) :=
        h1.tsum_add h2
    _ = _ := by
        rw [tsum_eq_sum (s := F) fun m hm => by simp [hm]]
        congr 1
        exact Finset.sum_congr rfl fun m hm => by simp [hm]

/-- The `ℓ²` norm of the interpolation-error coefficients splits into the aliasing errors over the
window and the tail outside it. -/
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
  rw [tsum_eq_sum_add_tsum_ite hsum (window N)]
  congr 1
  · exact Finset.sum_congr rfl fun m hm => by rw [norm_interpErrorCoeff, ite_eq_left hm]
  · refine tsum_congr fun m => ?_
    split_ifs with hm
    · rfl
    · rw [norm_interpErrorCoeff, ite_eq_right hm]

/-- **Parseval for the interpolation error**:
`∫_0^{2π} ‖eval φ − Π_N (eval φ)‖² = 2π ∑_m ‖d_m‖²`. -/
theorem intervalIntegral_norm_eval_sub_interp_sq (hs : 1 / 2 < s) {N : ℕ} (hN : 0 < N)
    (φ : PeriodicSobolev s) :
    ∫ x in (0 : ℝ)..2 * π,
        ‖eval (2 * π) φ x - DFT.interp N (-((N / 2 : ℕ) : ℤ)) (eval (2 * π) φ) x‖ ^ 2
      = 2 * π * ∑' m : ℤ, ‖interpErrorCoeff N φ m‖ ^ 2 := by
  simp_rw [eval_sub_interp_eq_tsum hs hN φ]
  exact intervalIntegral_norm_tsum_smul_fourier_sq (summable_norm_interpErrorCoeff hs N φ)

/-- **The `L²` interpolation error** in terms of the energy outside the window:
`∫_0^{2π} ‖eval φ − Π_N (eval φ)‖² ≤ 2π (N/2)^{-2s} (1 + 2 ζ(2s)) · windowTailNormSq N φ`. -/
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

/-- `(N/2)^{-s} = 2^s N^{-s}`. -/
theorem div_two_rpow_neg (s : ℝ) {N : ℕ} (hN : 0 < N) :
    ((N : ℝ) / 2) ^ (-s) = (2 : ℝ) ^ s * (N : ℝ) ^ (-s) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
    Real.div_rpow (by positivity) (by positivity)]
  field_simp

/-- **The `L²` interpolation error** (the first interpolation estimate of
[quarteroni2000numerical] §10.9, in coefficient form): for `s > 1/2` and `φ ∈ H^s`,

`‖eval φ − Π_N (eval φ)‖_{L²(0,2π)} ≤ √(2π (1 + 2 ζ(2s))) · 2^s · N^{-s} ‖φ‖`,

where `Π_N` is the discrete Fourier series over the centred window (`DFT.interp` at
`m = −N/2`). The error splits into the aliasing error over the window and the truncation error
outside it; both are `O(N^{-s})` by the weighted energy outside the window. -/
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
    have hpos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    have hinv : √((((N : ℝ) / 2) ^ (2 * s))⁻¹) = ((N : ℝ) / 2) ^ (-s) := by
      rw [← Real.rpow_neg hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]
      congr 1
      ring
    rw [show 2 * π * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * (1 + 2 * zetaReal (2 * s))) * ‖φ‖ ^ 2
        = (2 * π * (1 + 2 * zetaReal (2 * s))) * ((((N : ℝ) / 2) ^ (2 * s))⁻¹ * ‖φ‖ ^ 2) by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π * (1 + 2 * zetaReal (2 * s))),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹), hinv,
      Real.sqrt_sq (norm_nonneg _), div_two_rpow_neg s hN]
    ring
  rw [← hsqrt]
  exact Real.sqrt_le_sqrt hbound

/-- **The sup-norm interpolation error** (the second interpolation estimate of
[quarteroni2000numerical] §10.9, in coefficient form): for `s > 1/2`, `φ ∈ H^s` and every `x`,

`|eval φ x − Π_N (eval φ) x| ≤ 2 √(2 ζ(2s)) · 2^s · N^{1/2 − s} ‖φ‖`.

The error is a trigonometric series with coefficients `interpErrorCoeff`, bounded by the sum of
their moduli: the `ℓ¹` aliasing bound over the window and the `ℓ¹` tail outside it, each
`(N/2)^{-s} √(2 ζ(2s)) √N √(windowTailNormSq)`. -/
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
    rw [tsum_eq_sum_add_tsum_ite hsum (window N)]
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
  have hC : (0 : ℝ) ≤ ((N : ℝ) / 2) ^ (-s) * √(2 * zetaReal (2 * s)) * √(N : ℝ) := by positivity
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

/-- The trigonometric polynomial `x ↦ ∑_{q ∈ W} c_q e^{i q x}` with frequencies in the centred
window: the general element of the space `S_N` of [quarteroni2000numerical] §10.9. -/
noncomputable def windowTrigPoly (N : ℕ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ q ∈ window N, c q * Complex.exp ((q : ℂ) * x * I)

/-- A trigonometric polynomial over the window as a trigonometric series with finitely supported
coefficients. -/
theorem windowTrigPoly_eq_tsum (N : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    windowTrigPoly N c x
      = ∑' q : ℤ, (if q ∈ window N then c q else 0) • fourier q (x : AddCircle (2 * π)) := by
  rw [windowTrigPoly, tsum_eq_sum (s := window N) fun q hq => by simp [hq]]
  exact Finset.sum_congr rfl fun q hq => by rw [ite_eq_left hq, fourier_coe_two_pi, smul_eq_mul]

/-- Parseval for a trigonometric polynomial over the window:
`∫_0^{2π} ‖∑_{q ∈ W} c_q e^{iqx}‖² = 2π ∑_{q ∈ W} ‖c_q‖²`. -/
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

/-- The scalar product of the sum of the series against a character picks out the coefficient:
`∫_0^{2π} eval φ · conj (e^{iqx}) = 2π a_q`. -/
theorem intervalIntegral_eval_mul_conj_exp (hs : 1 / 2 < s) (φ : PeriodicSobolev s) (q : ℤ) :
    ∫ x in (0 : ℝ)..2 * π, eval (2 * π) φ x * conj (Complex.exp ((q : ℂ) * x * I))
      = 2 * π * coeff φ q := by
  have hper := eval_periodic (T := 2 * π) (Fact.out : (0 : ℝ) < 2 * π).ne' φ
  have h := fourierCoeff_lift_eval (T := 2 * π) hs φ q
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add] at h
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  rw [← h, Complex.real_smul]
  push_cast
  rw [← mul_assoc, mul_one_div_cancel hπ, one_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.Periodic.lift_coe, smul_eq_mul, fourier_neg, fourier_coe_two_pi]
  ring

/-- `(eval φ, v)_{L²} = 2π ∑_{q ∈ W} a_q conj (c_q)` for `v = ∑_{q ∈ W} c_q e^{iqx}`. -/
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

/-- `(eval φ, v)_N = 2π ∑_{q ∈ W} f̃_q conj (c_q)` with `f̃_q` the discrete coefficients. -/
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

/-- **The discrete scalar product estimate** (the third unnumbered estimate of
[quarteroni2000numerical] §10.9, in coefficient form): for `s > 1/2`, `φ ∈ H^s` and every
trigonometric polynomial `v = ∑_{q ∈ W} c_q e^{iqx}` over the window,

`|(eval φ, v) − (eval φ, v)_N| ≤ √(2π) √(2 ζ(2s)) · 2^s · N^{-s} ‖φ‖ ‖v‖_{L²(0,2π)}`,

where `(f, g) = ∫_0^{2π} f conj g` and `(f, g)_N = (2π/N) ∑_{j<N} f(x_j) conj g(x_j)`. The
difference is `2π ∑_{q ∈ W} (a_q − f̃_q) conj (c_q) = −2π ∑_{q ∈ W} aliasTail_q conj (c_q)`, and
Cauchy–Schwarz over the window with the `ℓ²` aliasing bound and Parseval for `v` finish. -/
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
    have hpos : (0 : ℝ) < (N : ℝ) / 2 := by positivity
    have hinv : √((((N : ℝ) / 2) ^ (2 * s))⁻¹) = ((N : ℝ) / 2) ^ (-s) := by
      rw [← Real.rpow_neg hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]
      congr 1
      ring
    rw [Real.sqrt_mul (mul_nonneg (by positivity) (mul_nonneg two_pos.le (zetaReal_nonneg _))),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (((N : ℝ) / 2) ^ (2 * s))⁻¹), hinv,
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

/-- **The trigonometric interpolant** `𝓘_n φ` of [han2009theoretical] §3.7 and Theorem 7.5.7: the
trigonometric polynomial of degree at most `n` that agrees with the sum of the series of `φ` at
the `2n + 1` equispaced nodes `2πj/(2n+1)`, read as an element of `PeriodicSobolev r` for any
`r` (its coefficients are finitely supported). Its coefficients on the window `-n, …, n` are
the discrete Fourier coefficients of `eval (2π) φ`, and `0` outside. -/
noncomputable def trigInterp (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) : PeriodicSobolev r :=
  ofCoeff r (fun q => if q ∈ window (2 * n + 1)
      then DFT.coeff (2 * n + 1) (-(n : ℤ)) (eval (2 * π) φ) (q + n).toNat else 0)
    (memℓp_two_iff.2 (summable_of_ne_finset_zero (s := window (2 * n + 1)) fun q hq => by
      simp [hq]))

/-- The coefficients of the interpolant: the discrete Fourier coefficients on the window, `0`
outside. -/
theorem coeff_trigInterp (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) (q : ℤ) :
    coeff (trigInterp r n φ) q = if q ∈ window (2 * n + 1)
      then DFT.coeff (2 * n + 1) (-(n : ℤ)) (eval (2 * π) φ) (q + n).toNat else 0 := by
  rw [trigInterp, coeff_ofCoeff]

/-- On the window, the interpolant's coefficient is the exact one plus the aliasing tail. -/
theorem coeff_trigInterp_of_mem (hs : 1 / 2 < s) (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s)
    {q : ℤ} (hq : q ∈ window (2 * n + 1)) :
    coeff (trigInterp r n φ) q = coeff φ q + aliasTail (2 * n + 1) φ q := by
  rw [coeff_trigInterp, ite_eq_left hq]
  have h := dftCoeff_eval_window hs (by omega : 0 < 2 * n + 1) φ hq
  have hn : ((2 * n + 1) / 2 : ℕ) = n := by omega
  simp only [hn] at h
  exact h

/-- The sum of the series of the interpolant is the discrete Fourier series of `eval φ`. -/
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

/-- **The interpolation property**: `𝓘_n φ` agrees with `φ` at the `2n + 1` equispaced nodes
`2πj/(2n+1)`, `j < 2n + 1`. -/
theorem eval_trigInterp_angleNode (r : ℝ) (n : ℕ) (φ : PeriodicSobolev s) {j : ℕ}
    (hj : j < 2 * n + 1) :
    eval (2 * π) (trigInterp r n φ) (angleNode (2 * n + 1) j)
      = eval (2 * π) φ (angleNode (2 * n + 1) j) := by
  rw [eval_trigInterp]
  exact DFT.interp_angleNode (by omega) _ _ hj

/-- The coefficients of `φ − 𝓘_n φ` are the interpolation-error coefficients. -/
theorem coeff_incl_sub_trigInterp (hs : 1 / 2 < s) {r : ℝ} (hrs : r ≤ s) (n : ℕ)
    (φ : PeriodicSobolev s) :
    coeff (incl hrs φ - trigInterp r n φ) = interpErrorCoeff (2 * n + 1) φ := by
  funext q
  rw [coeff_sub, Pi.sub_apply, coeff_incl, interpErrorCoeff]
  split_ifs with hq
  · rw [coeff_trigInterp_of_mem hs r n φ hq]
    ring
  · rw [coeff_trigInterp, ite_eq_right hq, sub_zero]

/-- On the window `-n, …, n` the `r`-weight is at most `n^r`, for `n ≥ 1` and `r ≥ 0`. -/
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

/-- Off the window `-n, …, n`, `|m| ≥ n + 1`, so `w_r(m)² ≤ (n+1)^{2(r−s)} w_s(m)²` for
`0 ≤ r ≤ s`. -/
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

/-- **[han2009theoretical] Theorem 7.5.7**: for `s > 1/2`, `φ ∈ H^s(2π)`, `0 ≤ r ≤ s` and
`n ≥ 1`, the trigonometric interpolant satisfies

`‖φ − 𝓘_n φ‖_r ≤ c n^{r − s} ‖φ‖_s`, `c = √(1 + 2 ζ(2s))`.

The coefficients of `φ − 𝓘_n φ` are the aliasing tails on the window `-n, …, n` and the exact
coefficients outside it; the `r`-weight is at most `n^r` on the window and at most
`(n+1)^{r−s}` times the `s`-weight outside, so the `ℓ²` aliasing bound and the energy outside
the window give the rate `n^{r−s}`. -/
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
  have hsplit := tsum_eq_sum_add_tsum_ite hsum.summable (window (2 * n + 1))
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
    rw [windowTailNormSq, ← tsum_mul_left]
    have hle : ∀ m : ℤ, (if m ∈ window (2 * n + 1) then (0 : ℝ)
        else (periodicSobolevWeight r m * ‖interpErrorCoeff (2 * n + 1) φ m‖) ^ 2)
        ≤ ((n : ℝ) + 1) ^ (2 * (r - s)) * (if m ∈ window (2 * n + 1) then (0 : ℝ)
          else (periodicSobolevWeight s m * ‖coeff φ m‖) ^ 2) := by
      intro m
      split_ifs with hm
      · simp
      · rw [norm_interpErrorCoeff, ite_eq_right hm, mul_pow, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (weight_sq_le_of_not_mem_window hrs hm)
          (by positivity)
    exact hasSum_le hle (Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) hle
      ((summable_ite_window _ φ).mul_left _)).hasSum ((summable_ite_window _ φ).mul_left _).hasSum
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
