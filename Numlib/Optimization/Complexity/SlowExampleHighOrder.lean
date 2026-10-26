import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Approximation.HermiteSpline
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Optimization.Optimality.Approximate
import Numlib.Optimization.ModelBased.TaylorModel

/-!
# Slow-convergence examples of arbitrary order

One-dimensional data for the sharpness ("slow convergence") results of [cartis2022evaluation]
Chapter 12 (and Theorems 3.3.6, 3.3.10, 4.1.6), generalizing the data families of
`Numlib/Optimization/Complexity/SlowExample` to arbitrary orders. In each family the jets at the
iterates have a single nonzero derivative of positive order (`Optimization.spikeJet`); the Hermite
consistency condition (A.32) then reduces to three scalar inequalities
(`Optimization.hermite_consistency_spike`), and Theorem A.9.2
(`Hermite.exists_contDiff_interpolating_jets_bounded`) gives an interpolant whose derivatives are
bounded and whose top derivative is Lipschitz, with constants independent of `ε`.

## Main results

* `Optimization.exists_slowTaylorOrder_interpolant` — the data of Theorem 12.2.15 with a free
  scale `c > 0` (steps `s_k = (c (ε + ω_k))^{1/(p-q+1)}`), also used for Theorems 3.3.6, 3.3.10 and
  4.1.6.
* `Optimization.exists_slowTRq_interpolant` — the data of the trust-region example of
  Theorem 12.2.6 (Appendix B), corrected.
* `Optimization.exists_slowARqpSmooth_interpolant` — the data of Theorem 12.2.17, for any
  regularization weight `σ > 0`.
* `Optimization.taylorMeasure_linearRegModel_eq_zero` — Example 12.1.3 in one variable: the
  Taylor measures of `-β t + σ |t|^{p+1}/(p+1)!` vanish at its minimizer for radii up to
  `3 t*/(p-1)`.

## Implementation notes

The function values are not prescribed: the statements give the decrease
`G (x (k+1)) = G (x k) - …` between consecutive iterates, which is all the algorithms see (the
initial value is `0` in the construction). Corrections to the source:

* (12.2.78): the book claims `|f^{(q)}_{k+1} - T^{(q)}_{f,p}(x_k, s_k)| = 0`; it equals
  `ω_k - ω_{k+1} = ε / k_ε`, which still satisfies (A.32).
* (B.12.5)–(B.12.8): the printed decrease `f_{k+1} = f_k - ½ ε^{q+1} c_k` contradicts
  `f_{k+1} = T_{f,q}(x_k, s_k)` (B.12.8); the Taylor decrease is `ε^{q+1} c_k`, which is used here.
  The printed (B.12.7) `x_k = (k-1) ε` is a typo for `x_k = k ε`, and the claimed
  `ε^{q+1} k_ε ≤ 1` is false (only `ε^{q+1} k_ε ≤ 2` holds). The residuals at orders `1 ≤ j < q`
  are `2 q!/(q-j)! s_k^{q-j+1}` (the book omits the factor `q!/(q-j)!`).
-/

open Set
open scoped Polynomial

namespace Optimization

/-! ### Jets with one nonzero derivative -/

/-- The jet at the `k`-th node with value `f k`, `m`-th derivative `d k` and all other
derivatives `0`. -/
def spikeJet (f d : ℕ → ℝ) (m k j : ℕ) : ℝ :=
  if j = 0 then f k else if j = m then d k else 0

theorem spikeJet_zero (f d : ℕ → ℝ) (m k : ℕ) : spikeJet f d m k 0 = f k := by
  simp [spikeJet]

theorem spikeJet_self (f d : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) (k : ℕ) : spikeJet f d m k m = d k := by
  simp [spikeJet, hm]

theorem spikeJet_of_ne (f d : ℕ → ℝ) {m j : ℕ} (hj : j ≠ 0) (hjm : j ≠ m) (k : ℕ) :
    spikeJet f d m k j = 0 := by
  simp [spikeJet, hj, hjm]

/-- The Taylor sum of a spike jet. -/
theorem sum_Icc_spikeJet (f d : ℕ → ℝ) {m n j : ℕ} (hm : m ≠ 0) (hmn : m ≤ n) (k : ℕ) (s : ℝ) :
    ∑ i ∈ Finset.Icc j n, spikeJet f d m k i * s ^ (i - j) / (i - j).factorial =
      (if j = 0 then f k else 0) +
        if j ≤ m then d k * s ^ (m - j) / (m - j).factorial else 0 := by
  have hsplit : ∀ i, spikeJet f d m k i * s ^ (i - j) / (i - j).factorial =
      (if i = 0 then f k * s ^ (i - j) / (i - j).factorial else 0) +
        (if i = m then d k * s ^ (i - j) / (i - j).factorial else 0) := fun i => by
    unfold spikeJet
    by_cases h0 : i = 0
    · subst h0
      simp [Ne.symm hm]
    · by_cases h1 : i = m
      · subst h1
        simp [hm]
      · simp [h0, h1]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  congr 1
  · by_cases hj : j = 0
    · simp [hj]
    · simp [hj, Finset.mem_Icc]
  · by_cases hj : j ≤ m
    · simp [hj, Finset.mem_Icc, hmn]
    · simp [hj, Finset.mem_Icc]

/-- **Hermite consistency for spike jets.** For jets with value `f k` and a single nonzero
derivative `d k` of order `1 ≤ m ≤ n`, the consistency condition (A.32) of order `n` with constant
`κ ≥ 0` at a step `s ≥ 0` follows from: the value residual
`|f (k+1) - f k - d k s^m/m!| ≤ κ s^{n+1}`, the bound `|d k| ≤ κ s^{n-m+1}` (needed only if
`m > 1`), and `|d (k+1) - d k| ≤ κ s^{n-m+1}`. -/
theorem hermite_consistency_spike {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) {f d : ℕ → ℝ} {k : ℕ}
    {s κ : ℝ} (hs : 0 ≤ s) (hκ : 0 ≤ κ)
    (h0 : |f (k + 1) - (f k + d k * s ^ m / m.factorial)| ≤ κ * s ^ (n + 1))
    (h1 : 1 < m → |d k| ≤ κ * s ^ (n - m + 1))
    (h2 : |d (k + 1) - d k| ≤ κ * s ^ (n - m + 1)) :
    ∀ j ≤ n, |spikeJet f d m (k + 1) j -
      ∑ i ∈ Finset.Icc j n, spikeJet f d m k i * s ^ (i - j) / (i - j).factorial| ≤
        κ * s ^ (n - j + 1) := by
  intro j hj
  have hm0 : m ≠ 0 := by omega
  rw [sum_Icc_spikeJet f d hm0 hmn]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simpa [spikeJet_zero, Nat.zero_le] using h0
  have hj0' : j ≠ 0 := by omega
  simp only [hj0', ↓reduceIte, zero_add]
  rcases lt_trichotomy j m with hjm | rfl | hjm
  · rw [spikeJet_of_ne f d hj0' hjm.ne, ite_eq_left hjm.le, zero_sub, abs_neg, abs_div, abs_mul,
      abs_pow, abs_of_nonneg hs, Nat.abs_cast]
    have hf : (1 : ℝ) ≤ (m - j).factorial := by exact_mod_cast Nat.factorial_pos _
    calc |d k| * s ^ (m - j) / (m - j).factorial ≤ |d k| * s ^ (m - j) :=
          div_le_self (by positivity) hf
      _ ≤ κ * s ^ (n - m + 1) * s ^ (m - j) :=
          mul_le_mul_of_nonneg_right (h1 (by omega)) (by positivity)
      _ = κ * s ^ (n - j + 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
  · rw [spikeJet_self f d hm0, ite_eq_left le_rfl, Nat.sub_self, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, div_one]
    exact h2
  · rw [spikeJet_of_ne f d hj0' hjm.ne', ite_eq_right (by omega), sub_zero, abs_zero]
    positivity

/-! ### Counting facts -/

/-- With `k_ε = ⌈ε^{-e}⌉₊`, `0 < ε ≤ 1`, `e ≥ 0`: `k_ε ≥ 1` and `k_ε ε^e ≤ 2`. -/
theorem one_le_ceil_rpow_neg_and_mul_le {ε e : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (he : 0 ≤ e) :
    1 ≤ ⌈ε ^ (-e)⌉₊ ∧ (⌈ε ^ (-e)⌉₊ : ℝ) * ε ^ e ≤ 2 := by
  have hpos : 0 < ε ^ (-e) := Real.rpow_pos_of_pos hε _
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne', ?_⟩
  have h := Nat.ceil_lt_add_one hpos.le
  have he1 : ε ^ e ≤ 1 := Real.rpow_le_one hε.le hε1 he
  have hepos : 0 < ε ^ e := Real.rpow_pos_of_pos hε _
  have : (⌈ε ^ (-e)⌉₊ : ℝ) * ε ^ e < (ε ^ (-e) + 1) * ε ^ e :=
    mul_lt_mul_of_pos_right h hepos
  have hinv : ε ^ (-e) * ε ^ e = 1 := by rw [Real.rpow_neg hε.le, inv_mul_cancel₀ hepos.ne']
  rw [add_mul, hinv, one_mul] at this
  linarith

/-- Partial sums of a nonnegative sequence bounded termwise by `M` over `K` terms. -/
theorem abs_sum_range_le_of_le {u : ℕ → ℝ} {M T : ℝ} {K : ℕ} (hu : ∀ i < K, 0 ≤ u i ∧ u i ≤ M)
    (hKM : (K : ℝ) * M ≤ T) {k : ℕ} (hk : k ≤ K) : |∑ i ∈ Finset.range k, u i| ≤ T := by
  have h0 : 0 ≤ ∑ i ∈ Finset.range k, u i :=
    Finset.sum_nonneg fun i hi => (hu i (by have := Finset.mem_range.1 hi; omega)).1
  rw [abs_of_nonneg h0]
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · obtain rfl : k = 0 := by omega
    simpa using hKM
  have hM : 0 ≤ M := (hu 0 hK).1.trans (hu 0 hK).2
  calc ∑ i ∈ Finset.range k, u i ≤ ∑ _i ∈ Finset.range k, M :=
        Finset.sum_le_sum fun i hi => (hu i (by have := Finset.mem_range.1 hi; omega)).2
    _ = k * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ K * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hM
    _ ≤ T := hKM

/-- Reading off the interpolation conditions for spike jets. -/
theorem iteratedDeriv_eq_of_spikeJet {G : ℝ → ℝ} {f d : ℕ → ℝ} {m n : ℕ} {x : ℕ → ℝ} {K : ℕ}
    (hm : m ≠ 0) (hmn : m ≤ n)
    (hG : ∀ k ≤ K, ∀ j ≤ n, iteratedDeriv j G (x k) = spikeJet f d m k j) {k : ℕ} (hk : k ≤ K) :
    G (x k) = f k ∧ iteratedDeriv m G (x k) = d k ∧
      ∀ j, 1 ≤ j → j ≤ n → j ≠ m → iteratedDeriv j G (x k) = 0 := by
  refine ⟨?_, ?_, fun j hj1 hjn hjm => ?_⟩
  · simpa [spikeJet_zero] using hG k hk 0 (Nat.zero_le n)
  · rw [hG k hk m hmn, spikeJet_self f d hm]
  · rw [hG k hk j hjn, spikeJet_of_ne f d (by omega) hjm]

/-! ### The trust-region example of order `q` (Theorem 12.2.6) -/

/-- **TRq slow example** ([cartis2022evaluation], Appendix B, proof of Theorem 12.2.6,
(B.12.4)–(B.12.9), corrected). For `q ≥ 1` there are `L, B ≥ 0` depending only on `q` such that:
for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-(q+1)}⌉₊`, `c_k = 2 - k/k_ε` and `x_{k+1} = x_k + ε`, there
is a `C^q` function `G : ℝ → ℝ` with `L`-Lipschitz `q`-th derivative, `|G^{(j)}| ≤ B` (`j ≤ q`),
`G^{(j)}(x_k) = 0` for `1 ≤ j < q` and `G^{(q)}(x_k) = -ε c_k q!` (`k ≤ k_ε`), and
`G (x_{k+1}) = G (x_k) - ε^{q+1} c_k` (`k < k_ε`): the decrease equals the decrease
`T_{G,q}(x_k, 0) - T_{G,q}(x_k, ε)` of the Taylor model. -/
theorem exists_slowTRq_interpolant {q : ℕ} (hq : 1 ≤ q) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, x (k + 1) = x k + ε) →
      ∃ G : ℝ → ℝ, ContDiff ℝ q G ∧
        (∀ s t, |iteratedDeriv q G s - iteratedDeriv q G t| ≤ L * |s - t|) ∧
        (∀ j ≤ q, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        (∀ k ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊, (∀ j, 1 ≤ j → j < q → iteratedDeriv j G (x k) = 0) ∧
          iteratedDeriv q G (x k) = -ε * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) * q.factorial) ∧
        ∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊,
          G (x (k + 1)) = G (x k) - ε ^ (q + 1) * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) := by
  have hq0 : q ≠ 0 := by omega
  set κ : ℝ := max 4 (2 * q.factorial) with hκ
  have hκ4 : 4 ≤ κ := le_max_left _ _
  have hκq : 2 * (q.factorial : ℝ) ≤ κ := le_max_right _ _
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le q hκ0
  refine ⟨L, B, hL, hB, fun ε x hε hε1 hx => ?_⟩
  set kε : ℕ := ⌈(ε ^ (q + 1))⁻¹⌉₊ with hkεdef
  have hpow : (ε ^ (q + 1))⁻¹ = ε ^ (-((q + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
  obtain ⟨hkε1, hkε2⟩ := one_le_ceil_rpow_neg_and_mul_le hε hε1 (Nat.cast_nonneg (q + 1))
  rw [← hpow, ← hkεdef] at hkε1 hkε2
  rw [Real.rpow_natCast] at hkε2
  have hkε : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set c : ℕ → ℝ := fun k => 2 - k / kε with hc
  have hc12 : ∀ k ≤ kε, 1 ≤ c k ∧ c k ≤ 2 := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    simp only [c]
    constructor
    · rw [le_sub_comm, div_le_iff₀ hkε]
      linarith
    · have : 0 ≤ (k : ℝ) / kε := by positivity
      linarith
  have hcs : ∀ k, c k - c (k + 1) = 1 / kε := fun k => by
    simp only [c]
    push_cast
    ring
  clear_value c
  have hqf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  set f : ℕ → ℝ := fun k => -∑ i ∈ Finset.range k, ε ^ (q + 1) * c i with hf
  set d : ℕ → ℝ := fun k => -ε * c k * q.factorial with hd
  have hfs : ∀ k, f (k + 1) = f k - ε ^ (q + 1) * c k := fun k => by
    simp only [f, Finset.sum_range_succ]
    ring
  have hfb : ∀ k ≤ kε, |f k| ≤ 4 := fun k hk => by
    simp only [f, abs_neg]
    refine abs_sum_range_le_of_le (K := kε) (M := 2 * ε ^ (q + 1)) (fun i hi => ?_) ?_ hk
    · obtain ⟨h1, h2⟩ := hc12 i hi.le
      constructor
      · positivity
      · nlinarith [pow_pos hε (q + 1)]
    · nlinarith
  have hdabs : ∀ k ≤ kε, |d k| = ε * c k * q.factorial := fun k hk => by
    obtain ⟨h1, -⟩ := hc12 k hk
    have : 0 ≤ ε * c k * q.factorial := mul_nonneg (mul_nonneg hε.le (by linarith)) hqf.le
    simp only [d]
    rw [neg_mul, neg_mul, abs_neg, abs_of_nonneg this]
  have hdb : ∀ k ≤ kε, |d k| ≤ 2 * q.factorial * ε := fun k hk => by
    obtain ⟨h1, h2⟩ := hc12 k hk
    rw [hdabs k hk]
    have : ε * c k ≤ ε * 2 := mul_le_mul_of_nonneg_left h2 hε.le
    nlinarith
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x (spikeJet f d q)
    (fun k hk => by rw [hx k hk]; linarith)
    (fun k hk => by rw [hx k hk]; linarith)
    (fun k hk j _ => by
      unfold spikeJet
      split_ifs
      · exact (hfb k hk).trans hκ4
      · refine (hdb k hk).trans ?_
        calc 2 * (q.factorial : ℝ) * ε ≤ 2 * q.factorial * 1 :=
              mul_le_mul_of_nonneg_left hε1 (by positivity)
          _ ≤ κ := by linarith
      · simpa using hκ0)
    (fun k hk => by
      have hgap : x (k + 1) - x k = ε := by rw [hx k hk]; ring
      rw [hgap]
      obtain ⟨h1, h2⟩ := hc12 k hk.le
      refine hermite_consistency_spike hq le_rfl hε.le hκ0 ?_ (fun _ => ?_) ?_
      · rw [hfs]
        simp only [d]
        have : f k - ε ^ (q + 1) * c k - (f k + -ε * c k * q.factorial * ε ^ q / q.factorial)
            = 0 := by
          field_simp
          ring
        rw [this, abs_zero]
        positivity
      · rw [Nat.sub_self, zero_add, pow_one]
        calc |d k| ≤ 2 * q.factorial * ε := hdb k hk.le
          _ ≤ κ * ε := mul_le_mul_of_nonneg_right hκq hε.le
      · rw [Nat.sub_self, zero_add, pow_one]
        have e : d (k + 1) - d k = ε * q.factorial * (1 / kε) := by
          simp only [d]
          rw [← hcs k]
          ring
        rw [e, abs_of_nonneg (by positivity)]
        have h1k : 1 / (kε : ℝ) ≤ 1 := by
          rw [div_le_one hkε]
          exact_mod_cast hkε1
        calc ε * q.factorial * (1 / kε) ≤ ε * q.factorial * 1 :=
              mul_le_mul_of_nonneg_left h1k (by positivity)
          _ ≤ κ * ε := by nlinarith)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨-, hq', hj⟩ := iteratedDeriv_eq_of_spikeJet hq0 le_rfl hGj hk
    refine ⟨fun j hj1 hjq => hj j hj1 hjq.le hjq.ne, ?_⟩
    rw [hq', hd, hc]
  · obtain ⟨h0, -, -⟩ := iteratedDeriv_eq_of_spikeJet hq0 le_rfl hGj (k := k) hk.le
    obtain ⟨h0', -, -⟩ := iteratedDeriv_eq_of_spikeJet hq0 le_rfl hGj (k := k + 1) hk
    rw [h0, h0', hfs, hc]

/-! ### The data of Theorem 12.2.15 (Taylor models of order `p`, criticality order `q`) -/

/-- **Slow example for `q`-th order criticality with `p`-th order models**
([cartis2022evaluation], proof of Theorem 12.2.15, (12.2.67)–(12.2.79); with a scale `c > 0` also
the data of Theorems 3.3.6, 3.3.10 and 4.1.6). Let `1 ≤ q ≤ p`, `c > 0` and `R = p - q + 1`. There
are `L, B ≥ 0` depending only on `p, q, c` such that: for every `ε ∈ (0, 1]`, with
`k_ε = ⌈ε^{-(p+1)/R}⌉₊`, `ω_k = ε (k_ε - k)/k_ε` and steps `x_{k+1} - x_k = (c (ε + ω_k))^{1/R}`,
there is a `C^p` function `G : ℝ → ℝ` with `L`-Lipschitz `p`-th derivative, `|G^{(j)}| ≤ B`
(`j ≤ p`), `G^{(q)}(x_k) = -(ε + ω_k)` and `G^{(j)}(x_k) = 0` for `j ∈ [1, p]`, `j ≠ q`
(`k ≤ k_ε`), and `G (x_{k+1}) = G (x_k) - (ε + ω_k) s_k^q / q!` (`k < k_ε`), i.e. the value at
`x_{k+1}` is the value of the Taylor polynomial of order `p` at `x_k`. -/
theorem exists_slowTaylorOrder_interpolant {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {c : ℝ}
    (hc : 0 < c) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (kε : ℕ) (x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      kε = ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊ →
      (∀ k < kε, x (k + 1) =
        x k + (c * (ε + ε * ((kε : ℝ) - k) / kε)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) →
      ∃ G : ℝ → ℝ, ContDiff ℝ p G ∧
        (∀ s t, |iteratedDeriv p G s - iteratedDeriv p G t| ≤ L * |s - t|) ∧
        (∀ j ≤ p, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        (∀ k ≤ kε, iteratedDeriv q G (x k) = -(ε + ε * ((kε : ℝ) - k) / kε) ∧
          ∀ j, 1 ≤ j → j ≤ p → j ≠ q → iteratedDeriv j G (x k) = 0) ∧
        ∀ k < kε, G (x (k + 1)) =
          G (x k) - (ε + ε * ((kε : ℝ) - k) / kε) * (x (k + 1) - x k) ^ q / q.factorial := by
  have hq0 : q ≠ 0 := by omega
  set R : ℕ := p - q + 1 with hR
  have hR0 : R ≠ 0 := by omega
  have hRpos : (0 : ℝ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR0
  have hRcast : (R : ℝ) = p - q + 1 := by
    rw [hR]
    push_cast [Nat.cast_sub hqp]
    ring
  have hqf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  set M : ℝ := 2 * (2 * c) ^ ((q : ℝ) / R) / q.factorial with hM
  have hM0 : 0 ≤ M := by positivity
  set κ : ℝ := max (1 / c) (max (2 * M) (max 2 ((2 * c) ^ (1 / (R : ℝ))))) with hκ
  have hκc : 1 / c ≤ κ := le_max_left _ _
  have hκM : 2 * M ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ2 : 2 ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκs : (2 * c) ^ (1 / (R : ℝ)) ≤ κ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ0 : 0 ≤ κ := by linarith
  have hκc1 : 1 ≤ κ * c := by
    have := mul_le_mul_of_nonneg_right hκc hc.le
    rwa [one_div_mul_cancel hc.ne'] at this
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le p hκ0
  refine ⟨L, B, hL, hB, fun ε kε x hε hε1 hkεdef hx => ?_⟩
  set e : ℝ := (p + 1 : ℝ) / R with he
  have he0 : 0 ≤ e := by positivity
  have he1 : 1 + (q : ℝ) / R = e := by
    rw [he]
    field_simp
    rw [hRcast]
    ring
  obtain ⟨hkε1, hkε2⟩ := one_le_ceil_rpow_neg_and_mul_le hε hε1 he0
  rw [← hkεdef] at hkε1 hkε2
  have hkε : (0 : ℝ) < kε := by exact_mod_cast hkε1
  set ω : ℕ → ℝ := fun k => ε * ((kε : ℝ) - k) / kε with hω
  have hx' : ∀ k < kε, x (k + 1) = x k + (c * (ε + ω k)) ^ (1 / (R : ℝ)) := hx
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k ∧ ω k ≤ ε := fun k hk' => by
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    simp only [ω]
    refine ⟨div_nonneg (mul_nonneg hε.le (by linarith)) hkε.le, ?_⟩
    rw [div_le_iff₀ hkε]
    nlinarith
  have hωs : ∀ k, ω k - ω (k + 1) = ε / kε := fun k => by
    simp only [ω]
    push_cast
    ring
  clear_value ω
  clear hx
  -- the steps
  set s : ℕ → ℝ := fun k => (c * (ε + ω k)) ^ (1 / (R : ℝ)) with hs
  have hgap : ∀ k < kε, x (k + 1) - x k = s k := fun k hk => by rw [hx' k hk]; ring
  have hbase : ∀ k ≤ kε, 0 < c * (ε + ω k) := fun k hk => by
    have := (hω0 k hk).1
    positivity
  have hsR : ∀ k ≤ kε, s k ^ R = c * (ε + ω k) := fun k hk => by
    simp only [s]
    rw [one_div, Real.rpow_inv_natCast_pow (hbase k hk).le hR0]
  have hspos : ∀ k ≤ kε, 0 < s k := fun k hk => Real.rpow_pos_of_pos (hbase k hk) _
  have hsq : ∀ k ≤ kε, s k ^ q = (c * (ε + ω k)) ^ ((q : ℝ) / R) := fun k hk => by
    simp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hbase k hk).le]
    ring_nf
  have hsle : ∀ k ≤ kε, s k ≤ (2 * c) ^ (1 / (R : ℝ)) := fun k hk => by
    obtain ⟨h0, h1⟩ := hω0 k hk
    simp only [s]
    refine Real.rpow_le_rpow (hbase k hk).le ?_ (by positivity)
    nlinarith
  -- the decrease and the function values
  set f : ℕ → ℝ := fun k => -∑ i ∈ Finset.range k, (ε + ω i) * s i ^ q / q.factorial with hf
  set d : ℕ → ℝ := fun k => -(ε + ω k) with hd
  have hfs : ∀ k, f (k + 1) = f k - (ε + ω k) * s k ^ q / q.factorial := fun k => by
    simp only [f, Finset.sum_range_succ]
    ring
  have hdec : ∀ i < kε, 0 ≤ (ε + ω i) * s i ^ q / q.factorial ∧
      (ε + ω i) * s i ^ q / q.factorial ≤ M * ε ^ e := fun i hi => by
    obtain ⟨h0, h1⟩ := hω0 i hi.le
    have hs0 := (hspos i hi.le).le
    refine ⟨by positivity, ?_⟩
    rw [hsq i hi.le]
    have hb : (c * (ε + ω i)) ^ ((q : ℝ) / R) ≤ (2 * c) ^ ((q : ℝ) / R) * ε ^ ((q : ℝ) / R) := by
      rw [← Real.mul_rpow (by positivity) hε.le]
      exact Real.rpow_le_rpow (hbase i hi.le).le (by nlinarith) (by positivity)
    have hεe : ε * ε ^ ((q : ℝ) / R) = ε ^ e := by
      rw [← he1, Real.rpow_add hε, Real.rpow_one]
    calc (ε + ω i) * (c * (ε + ω i)) ^ ((q : ℝ) / R) / q.factorial
        ≤ (2 * ε) * ((2 * c) ^ ((q : ℝ) / R) * ε ^ ((q : ℝ) / R)) / q.factorial := by
          gcongr
          linarith
      _ = M * (ε * ε ^ ((q : ℝ) / R)) := by rw [hM]; ring
      _ = M * ε ^ e := by rw [hεe]
  have hfb : ∀ k ≤ kε, |f k| ≤ 2 * M := fun k hk => by
    simp only [f, abs_neg]
    refine abs_sum_range_le_of_le hdec ?_ hk
    calc (kε : ℝ) * (M * ε ^ e) = M * (kε * ε ^ e) := by ring
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left hkε2 hM0
      _ = 2 * M := by ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x (spikeJet f d q)
    (fun k hk => by rw [← sub_pos, hgap k hk]; exact hspos k hk.le)
    (fun k hk => by rw [hgap k hk]; exact (hsle k hk.le).trans hκs)
    (fun k hk j _ => by
      obtain ⟨h0, h1⟩ := hω0 k hk
      unfold spikeJet
      split_ifs
      · exact (hfb k hk).trans hκM
      · simp only [d, abs_neg]
        rw [abs_of_nonneg (by linarith)]
        linarith
      · simpa using hκ0)
    (fun k hk => by
      rw [hgap k hk]
      obtain ⟨h0, h1⟩ := hω0 k hk.le
      have hsR' := hsR k hk.le
      refine hermite_consistency_spike hq hqp (hspos k hk.le).le hκ0 ?_ (fun _ => ?_) ?_
      · rw [hfs]
        simp only [d]
        have : f k - (ε + ω k) * s k ^ q / q.factorial -
            (f k + -(ε + ω k) * s k ^ q / q.factorial) = 0 := by ring
        rw [this, abs_zero]
        have := (hspos k hk.le).le
        positivity
      · rw [← hR, hsR']
        simp only [d, abs_neg]
        rw [abs_of_nonneg (by linarith)]
        calc ε + ω k = 1 * (ε + ω k) := by ring
          _ ≤ κ * c * (ε + ω k) := mul_le_mul_of_nonneg_right hκc1 (by linarith)
          _ = κ * (c * (ε + ω k)) := by ring
      · rw [← hR, hsR']
        simp only [d]
        rw [show -(ε + ω (k + 1)) - -(ε + ω k) = ε / kε by linarith [hωs k],
          abs_of_nonneg (by positivity)]
        have h1k : ε / (kε : ℝ) ≤ ε := div_le_self hε.le (by exact_mod_cast hkε1)
        calc ε / (kε : ℝ) ≤ 1 * (ε + ω k) := by linarith
          _ ≤ κ * c * (ε + ω k) := mul_le_mul_of_nonneg_right hκc1 (by linarith)
          _ = κ * (c * (ε + ω k)) := by ring)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨-, hq', hj⟩ := iteratedDeriv_eq_of_spikeJet hq0 hqp hGj hk
    refine ⟨?_, hj⟩
    rw [hq', hd, hω]
  · obtain ⟨h0, -, -⟩ := iteratedDeriv_eq_of_spikeJet hq0 hqp hGj (k := k) hk.le
    obtain ⟨h0', -, -⟩ := iteratedDeriv_eq_of_spikeJet hq0 hqp hGj (k := k + 1) hk
    rw [h0, h0', hfs, hgap k hk, hω]

/-! ### The data of Theorem 12.2.17 (smoother functions do not help) -/

/-- **Slow example for regularization methods on smoother functions** ([cartis2022evaluation],
proof of Theorem 12.2.17, (12.2.80)–(12.2.96)). Let `1 ≤ q ≤ p ≤ r` and `σ > 0` (the book takes
the weight (12.2.85)). There are `L, B ≥ 0` depending only on `p, q, r, σ` such that: for every
`ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-q(p+1)/p}⌉₊`, `ω_k = ε^{qr/p} (k_ε - k)/k_ε` (the book's
`ε^{q+γ}`, `γ = q(r/p - 1)`), `β_k = (ε^q + ω_k)/q!` and steps
`x_{k+1} - x_k = s_k = (p! β_k/σ)^{1/p}` (12.2.88), there is a `C^r` function `G : ℝ → ℝ` with
`L`-Lipschitz `r`-th derivative, `|G^{(j)}| ≤ B` (`j ≤ r`), `G'(x_k) = -β_k` and `G^{(j)}(x_k) = 0`
for `2 ≤ j ≤ r` (`k ≤ k_ε`), and `G (x_{k+1}) = G (x_k) - β_k s_k` (`k < k_ε`), the value of the
Taylor polynomial at `x_{k+1}` ((12.2.90)–(12.2.91)). -/
theorem exists_slowARqpSmooth_interpolant {p q r : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) (hpr : p ≤ r)
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (kε : ℕ) (x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      kε = ⌈ε ^ (-((q : ℝ) * (p + 1) / p))⌉₊ →
      (∀ k < kε, x (k + 1) = x k + (p.factorial *
        ((ε ^ q + ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε) / q.factorial) / σ) ^
          (1 / (p : ℝ))) →
      ∃ G : ℝ → ℝ, ContDiff ℝ r G ∧
        (∀ s t, |iteratedDeriv r G s - iteratedDeriv r G t| ≤ L * |s - t|) ∧
        (∀ j ≤ r, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        (∀ k ≤ kε, deriv G (x k) =
            -((ε ^ q + ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε) / q.factorial) ∧
          ∀ j, 2 ≤ j → j ≤ r → iteratedDeriv j G (x k) = 0) ∧
        ∀ k < kε, G (x (k + 1)) = G (x k) -
          (ε ^ q + ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε) / q.factorial *
            (x (k + 1) - x k) := by
  have hp1 : 1 ≤ p := hq.trans hqp
  have hp0 : p ≠ 0 := by omega
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp1
  have hqf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hqf1 : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hpf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  set C : ℝ := (p.factorial / (q.factorial * σ)) ^ ((r : ℝ) / p) with hC
  have hCpos : 0 < C := by positivity
  set M : ℝ := 2 / q.factorial * (2 * p.factorial / (q.factorial * σ)) ^ (1 / (p : ℝ)) with hM
  have hM0 : 0 ≤ M := by positivity
  set κ : ℝ := max (1 / (q.factorial * C)) (max (2 * M)
    (max 2 ((2 * p.factorial / σ) ^ (1 / (p : ℝ))))) with hκ
  have hκC : 1 / (q.factorial * C) ≤ κ := le_max_left _ _
  have hκM : 2 * M ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ2 : 2 ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκs : (2 * p.factorial / σ) ^ (1 / (p : ℝ)) ≤ κ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le r hκ0
  refine ⟨L, B, hL, hB, fun ε kε x hε hε1 hkεdef hx => ?_⟩
  set e : ℝ := (q : ℝ) * (p + 1) / p with he
  have he0 : 0 ≤ e := by positivity
  obtain ⟨hkε1, hkε2⟩ := one_le_ceil_rpow_neg_and_mul_le hε hε1 he0
  rw [← hkεdef] at hkε1 hkε2
  have hkε : (0 : ℝ) < kε := by exact_mod_cast hkε1
  -- powers of `ε`
  have hεq : 0 < ε ^ q := pow_pos hε q
  have hεq1 : ε ^ q ≤ 1 := pow_le_one₀ hε.le hε1
  have hA : ε ^ ((q : ℝ) * r / p) ≤ ε ^ q := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_ge hε hε1 ?_
    rw [le_div_iff₀ hppos]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpr) (Nat.cast_nonneg q)
  have hApos : 0 < ε ^ ((q : ℝ) * r / p) := Real.rpow_pos_of_pos hε _
  have hqrp : (ε ^ q) ^ ((r : ℝ) / p) = ε ^ ((q : ℝ) * r / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    ring_nf
  have hqe : ε ^ q * (ε ^ q) ^ (1 / (p : ℝ)) = ε ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_add hε, he]
    congr 1
    field_simp
  set ω : ℕ → ℝ := fun k => ε ^ ((q : ℝ) * r / p) * ((kε : ℝ) - k) / kε with hω
  set β : ℕ → ℝ := fun k => (ε ^ q + ω k) / q.factorial with hβ
  have hx' : ∀ k < kε, x (k + 1) = x k + (p.factorial * β k / σ) ^ (1 / (p : ℝ)) := hx
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k ∧ ω k ≤ ε ^ ((q : ℝ) * r / p) := fun k hk' => by
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    simp only [ω]
    refine ⟨div_nonneg (mul_nonneg hApos.le (by linarith)) hkε.le, ?_⟩
    rw [div_le_iff₀ hkε]
    nlinarith
  have hωs : ∀ k, ω k - ω (k + 1) = ε ^ ((q : ℝ) * r / p) / kε := fun k => by
    simp only [ω]
    push_cast
    ring
  have hβb : ∀ k ≤ kε, ε ^ q / q.factorial ≤ β k ∧ β k ≤ 2 * ε ^ q / q.factorial :=
    fun k hk => by
      obtain ⟨h0, h1⟩ := hω0 k hk
      simp only [β]
      constructor <;> gcongr <;> linarith
  have hβs : ∀ k, β k - β (k + 1) = ε ^ ((q : ℝ) * r / p) / kε / q.factorial := fun k => by
    simp only [β]
    rw [← hωs k]
    ring
  clear_value β ω
  clear hx
  -- the steps
  set s : ℕ → ℝ := fun k => (p.factorial * β k / σ) ^ (1 / (p : ℝ)) with hs
  have hgap : ∀ k < kε, x (k + 1) - x k = s k := fun k hk => by rw [hx' k hk]; ring
  have hβpos : ∀ k ≤ kε, 0 < β k := fun k hk =>
    lt_of_lt_of_le (by positivity) (hβb k hk).1
  have hspos : ∀ k ≤ kε, 0 < s k := fun k hk => by
    have := hβpos k hk
    exact Real.rpow_pos_of_pos (by positivity) _
  have hsr : ∀ k ≤ kε, C * ε ^ ((q : ℝ) * r / p) ≤ s k ^ r := fun k hk => by
    have hb := (hβb k hk).1
    have hX : 0 ≤ p.factorial * β k / σ := by have := hβpos k hk; positivity
    simp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX, ← hqrp, hC,
      ← Real.mul_rpow (by positivity) hεq.le, show 1 / (p : ℝ) * r = r / p by ring]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    calc p.factorial / (q.factorial * σ) * ε ^ q = p.factorial * (ε ^ q / q.factorial) / σ := by
          field_simp
      _ ≤ p.factorial * β k / σ := by gcongr
  have hsle : ∀ k ≤ kε, s k ≤ (2 * p.factorial / σ) ^ (1 / (p : ℝ)) := fun k hk => by
    have hb := (hβb k hk).2
    have hX : 0 ≤ p.factorial * β k / σ := by have := hβpos k hk; positivity
    refine Real.rpow_le_rpow hX ?_ (by positivity)
    have : β k ≤ 2 := hb.trans (by
      rw [div_le_iff₀ hqf]
      nlinarith)
    have h2 : p.factorial * β k ≤ 2 * p.factorial := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left this hpf.le
    exact div_le_div_of_nonneg_right h2 hσ.le
  -- function values
  set f : ℕ → ℝ := fun k => -∑ i ∈ Finset.range k, β i * s i with hf
  set d : ℕ → ℝ := fun k => -β k with hd
  have hfs : ∀ k, f (k + 1) = f k - β k * s k := fun k => by
    simp only [f, Finset.sum_range_succ]
    ring
  have hdec : ∀ i < kε, 0 ≤ β i * s i ∧ β i * s i ≤ M * ε ^ e := fun i hi => by
    obtain ⟨hb1, hb2⟩ := hβb i hi.le
    have hβ0 := hβpos i hi.le
    have hs0 := (hspos i hi.le).le
    refine ⟨by positivity, ?_⟩
    have hsb : s i ≤ (2 * p.factorial / (q.factorial * σ)) ^ (1 / (p : ℝ)) *
        (ε ^ q) ^ (1 / (p : ℝ)) := by
      rw [← Real.mul_rpow (by positivity) hεq.le]
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc p.factorial * β i / σ ≤ p.factorial * (2 * ε ^ q / q.factorial) / σ := by gcongr
        _ = 2 * p.factorial / (q.factorial * σ) * ε ^ q := by field_simp
    calc β i * s i ≤ 2 * ε ^ q / q.factorial *
          ((2 * p.factorial / (q.factorial * σ)) ^ (1 / (p : ℝ)) * (ε ^ q) ^ (1 / (p : ℝ))) :=
          mul_le_mul hb2 hsb hs0 (by positivity)
      _ = M * (ε ^ q * (ε ^ q) ^ (1 / (p : ℝ))) := by rw [hM]; ring
      _ = M * ε ^ e := by rw [hqe]
  have hfb : ∀ k ≤ kε, |f k| ≤ 2 * M := fun k hk => by
    simp only [f, abs_neg]
    refine abs_sum_range_le_of_le hdec ?_ hk
    calc (kε : ℝ) * (M * ε ^ e) = M * (kε * ε ^ e) := by ring
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left hkε2 hM0
      _ = 2 * M := by ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x (spikeJet f d 1)
    (fun k hk => by rw [← sub_pos, hgap k hk]; exact hspos k hk.le)
    (fun k hk => by rw [hgap k hk]; exact (hsle k hk.le).trans hκs)
    (fun k hk j _ => by
      have hb := (hβb k hk).2
      have hβ0 := hβpos k hk
      unfold spikeJet
      split_ifs
      · exact (hfb k hk).trans hκM
      · simp only [d, abs_neg]
        rw [abs_of_pos hβ0]
        have : 2 * ε ^ q / q.factorial ≤ 2 := by
          rw [div_le_iff₀ hqf]
          nlinarith
        linarith
      · simpa using hκ0)
    (fun k hk => by
      rw [hgap k hk]
      have hs0 := (hspos k hk.le).le
      refine hermite_consistency_spike le_rfl (hq.trans (hqp.trans hpr)) hs0 hκ0 ?_
        (fun h => absurd h (lt_irrefl 1)) ?_
      · rw [hfs]
        simp only [d]
        have : f k - β k * s k - (f k + -β k * s k ^ 1 / (Nat.factorial 1 : ℝ)) = 0 := by
          simp
          ring
        rw [this, abs_zero]
        positivity
      · rw [Nat.sub_add_cancel (hq.trans (hqp.trans hpr))]
        simp only [d]
        rw [show -β (k + 1) - -β k = β k - β (k + 1) by ring, hβs,
          abs_of_nonneg (by positivity)]
        have h1 : ε ^ ((q : ℝ) * r / p) / kε / q.factorial ≤
            ε ^ ((q : ℝ) * r / p) / q.factorial := by
          gcongr
          exact div_le_self hApos.le (by exact_mod_cast hkε1)
        have h2 : ε ^ ((q : ℝ) * r / p) / q.factorial =
            1 / (q.factorial * C) * (C * ε ^ ((q : ℝ) * r / p)) := by
          field_simp
        rw [h2] at h1
        exact h1.trans (mul_le_mul hκC (hsr k hk.le) (by positivity) hκ0))
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, fun j hj2 hjr => ?_⟩, fun k hk => ?_⟩
  · obtain ⟨-, h1, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero (hq.trans (hqp.trans hpr))
      hGj hk
    rw [iteratedDeriv_one] at h1
    rw [h1, hd, hβ, hω]
  · obtain ⟨-, -, hj⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero (hq.trans (hqp.trans hpr))
      hGj hk
    exact hj j (by omega) hjr (by omega)
  · have h1r := hq.trans (hqp.trans hpr)
    obtain ⟨h0, -, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero h1r hGj (k := k) hk.le
    obtain ⟨h0', -, -⟩ := iteratedDeriv_eq_of_spikeJet one_ne_zero h1r hGj (k := k + 1) hk
    rw [h0, h0', hfs, hgap k hk, hβ, hω]

/-! ### The monomial model (12.2.69)–(12.2.70) -/

/-- The regularized monomial model of [cartis2022evaluation] (12.2.69)–(12.2.70) in one variable:
`m t = -a t^q/q! + σ |t|^{p+1}/(p+1)!` (the book's weight is `σ = p!/(q-1)!`). -/
noncomputable def negMonomialRegModel (p q : ℕ) (σ a t : ℝ) : ℝ :=
  -a * t ^ q / q.factorial + σ * |t| ^ (p + 1) / (p + 1).factorial

/-- The polynomial that agrees with `negMonomialRegModel` for `t ≥ 0`. -/
private noncomputable def negMonomialPoly (p q : ℕ) (σ a : ℝ) : ℝ[X] :=
  Polynomial.C (-a / q.factorial) * Polynomial.X ^ q +
    Polynomial.C (σ / (p + 1).factorial) * Polynomial.X ^ (p + 1)

private theorem eval_negMonomialPoly (p q : ℕ) (σ a t : ℝ) :
    (negMonomialPoly p q σ a).eval t = -a * t ^ q / q.factorial +
      σ * t ^ (p + 1) / (p + 1).factorial := by
  simp [negMonomialPoly]
  ring

/-- `(n.descFactorial j : ℝ) / n! = 1/(n-j)!` if `j ≤ n` and `0` otherwise. -/
private theorem descFactorial_div_factorial (n j : ℕ) :
    (n.descFactorial j : ℝ) / n.factorial = if j ≤ n then (1 : ℝ) / (n - j).factorial else 0 := by
  split_ifs with h
  · have e : ((n - j).factorial : ℝ) * n.descFactorial j = n.factorial := by
      exact_mod_cast Nat.factorial_mul_descFactorial h
    have h1 : ((n - j).factorial : ℝ) ≠ 0 := by positivity
    have h2 : (n.factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n.descFactorial j : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (by rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega)
    rw [← e]
    field_simp
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
    simp

/-- **The monomial model** ([cartis2022evaluation] (12.2.69)–(12.2.70) and the display after it),
for any weight `σ > 0`. For `1 ≤ q ≤ p`, `a > 0`, `R = p - q + 1` and `λ = σ (q-1)!/p!`, the
model `m t = -a t^q/q! + σ |t|^{p+1}/(p+1)!` attains its global minimum at
`t* = (a/λ)^{1/R}`, with value `m t* = -R/((p+1) q!) a t*^q`, and its derivatives at `t*` are
`m^{(j)}(t*) = -a t*^{q-j}/(q-j)! [j ≤ q] + σ t*^{p+1-j}/(p+1-j)! [j ≤ p+1]`. -/
theorem isMinOn_neg_monomial_add_regularization {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {σ a : ℝ}
    (hσ : 0 < σ) (ha : 0 < a) :
    IsMinOn (negMonomialRegModel p q σ a) univ
        ((a / (σ * (q - 1).factorial / p.factorial)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) ∧
      negMonomialRegModel p q σ a
          ((a / (σ * (q - 1).factorial / p.factorial)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) =
        -(((p - q + 1 : ℕ) : ℝ) / ((p + 1) * q.factorial)) * a *
          ((a / (σ * (q - 1).factorial / p.factorial)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) ^ q ∧
      ∀ j, iteratedDeriv j (negMonomialRegModel p q σ a)
          ((a / (σ * (q - 1).factorial / p.factorial)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))) =
        (if j ≤ q then -a * ((a / (σ * (q - 1).factorial / p.factorial)) ^
            (1 / ((p - q + 1 : ℕ) : ℝ))) ^ (q - j) / (q - j).factorial else 0) +
        if j ≤ p + 1 then σ * ((a / (σ * (q - 1).factorial / p.factorial)) ^
            (1 / ((p - q + 1 : ℕ) : ℝ))) ^ (p + 1 - j) / (p + 1 - j).factorial else 0 := by
  set R : ℕ := p - q + 1 with hR
  have hR0 : R ≠ 0 := by omega
  have hqf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  have hq1f : (0 : ℝ) < (q - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos _
  have hp1f : (0 : ℝ) < (p + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  set lam : ℝ := σ * (q - 1).factorial / p.factorial with hlam
  have hlam0 : 0 < lam := by positivity
  set t₀ : ℝ := (a / lam) ^ (1 / (R : ℝ)) with ht₀
  have ht₀pos : 0 < t₀ := Real.rpow_pos_of_pos (by positivity) _
  have ht₀R : t₀ ^ R = a / lam := by
    rw [ht₀, one_div, Real.rpow_inv_natCast_pow (by positivity) hR0]
  have hlt₀ : lam * t₀ ^ R = a := by rw [ht₀R]; field_simp
  -- `σ (p+1)/(p+1)! = λ/(q-1)!`
  have hσp : σ * (p + 1) / (p + 1).factorial = lam / (q - 1).factorial := by
    rw [hlam, Nat.factorial_succ]
    push_cast
    field_simp
  set φ : ℝ → ℝ := fun t => -a * t ^ q / q.factorial + σ * t ^ (p + 1) / (p + 1).factorial
    with hφ
  have hφd : ∀ t, HasDerivAt φ (t ^ (q - 1) / (q - 1).factorial * (lam * t ^ R - a)) t :=
    fun t => by
    have h := ((((hasDerivAt_pow q t).const_mul (-a)).div_const (q.factorial : ℝ)).add
      (((hasDerivAt_pow (p + 1) t).const_mul σ).div_const ((p + 1).factorial : ℝ)))
    convert h using 1
    have htp : t ^ p = t ^ (q - 1) * t ^ R := by
      rw [← pow_add]
      congr 1
      omega
    have hqfac : (q.factorial : ℝ) = q * (q - 1).factorial := by
      have : q = q - 1 + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ]
      push_cast [Nat.cast_sub hq]
      ring
    have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have key : σ * (((p + 1 : ℕ) : ℝ) * (t ^ (q - 1) * t ^ R)) / (p + 1).factorial =
        lam * (t ^ (q - 1) * t ^ R) / (q - 1).factorial := by
      calc σ * (((p + 1 : ℕ) : ℝ) * (t ^ (q - 1) * t ^ R)) / (p + 1).factorial
          = σ * (p + 1) / (p + 1).factorial * (t ^ (q - 1) * t ^ R) := by push_cast; ring
        _ = _ := by rw [hσp]; ring
    have key2 : -a * ((q : ℝ) * t ^ (q - 1)) / q.factorial =
        -a * t ^ (q - 1) / (q - 1).factorial := by
      rw [hqfac]
      field_simp
    rw [Nat.add_sub_cancel, htp, key, key2]
    ring
  have hanti : AntitoneOn φ (Icc 0 t₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t₀) (fun t _ => (hφd t).continuousAt
      |>.continuousWithinAt) (fun t _ => (hφd t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hφd t).deriv]
    have h1 : lam * t ^ R ≤ a := by
      rw [← hlt₀]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1.le ht.2.le R) hlam0.le
    have h2 : 0 ≤ t ^ (q - 1) / (q - 1).factorial := by
      have := ht.1.le
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos h2 (by linarith)
  have hmono : MonotoneOn φ (Ici t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici t₀) (fun t _ => (hφd t).continuousAt
      |>.continuousWithinAt) (fun t _ => (hφd t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hφd t).deriv]
    have ht0 : 0 ≤ t := ht₀pos.le.trans (le_of_lt ht)
    have h1 : a ≤ lam * t ^ R := by
      rw [← hlt₀]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀pos.le (le_of_lt ht) R) hlam0.le
    have h2 : 0 ≤ t ^ (q - 1) / (q - 1).factorial := by positivity
    exact mul_nonneg h2 (by linarith)
  have hφmin : ∀ t, 0 ≤ t → φ t₀ ≤ φ t := fun t ht => by
    rcases le_total t t₀ with h | h
    · exact hanti ⟨ht, h⟩ ⟨ht₀pos.le, le_rfl⟩ h
    · exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
  have hmφ : ∀ t, 0 ≤ t → negMonomialRegModel p q σ a t = φ t := fun t ht => by
    simp only [negMonomialRegModel, φ, abs_of_nonneg ht]
  have hmge : ∀ t, φ |t| ≤ negMonomialRegModel p q σ a t := fun t => by
    simp only [negMonomialRegModel, φ]
    have h : t ^ q ≤ |t| ^ q := by
      rw [← abs_pow]
      exact le_abs_self _
    have : -a * |t| ^ q / q.factorial ≤ -a * t ^ q / q.factorial := by
      apply div_le_div_of_nonneg_right _ hqf.le
      nlinarith
    linarith
  refine ⟨fun t _ => ?_, ?_, fun j => ?_⟩
  · rw [Set.mem_ofPred_eq, hmφ t₀ ht₀pos.le]
    exact (hφmin |t| (abs_nonneg t)).trans (hmge t)
  · rw [hmφ t₀ ht₀pos.le]
    simp only [φ]
    have hpow : σ * t₀ ^ (p + 1) = σ / lam * a * t₀ ^ q := by
      rw [show p + 1 = q + R by omega, pow_add, ht₀R]
      field_simp
    have hR' : (R : ℝ) = p - q + 1 := by rw [hR]; push_cast [Nat.cast_sub hqp]; ring
    have hq' : (q.factorial : ℝ) = q * (q - 1).factorial := by
      have : q = q - 1 + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ]
      push_cast [Nat.cast_sub hq]
      ring
    have hp' : ((p + 1).factorial : ℝ) = (p + 1) * p.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hpow, hR', hq', hp', hlam]
    field_simp
    ring
  · -- near `t₀ > 0` the model is the polynomial `φ`
    have hev : negMonomialRegModel p q σ a =ᶠ[nhds t₀]
        fun t => (negMonomialPoly p q σ a).eval t := by
      filter_upwards [Ioi_mem_nhds ht₀pos] with t ht
      rw [hmφ t (le_of_lt ht), eval_negMonomialPoly]
    rw [hev.iteratedDeriv_eq, Polynomial.iteratedDeriv_eval]
    simp only [negMonomialPoly, Polynomial.iterate_derivative_add,
      Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    have e1 : -a / q.factorial * ((q.descFactorial j : ℝ) * t₀ ^ (q - j)) =
        -a * t₀ ^ (q - j) * ((q.descFactorial j : ℝ) / q.factorial) := by ring
    have e2 : σ / (p + 1).factorial * (((p + 1).descFactorial j : ℝ) * t₀ ^ (p + 1 - j)) =
        σ * t₀ ^ (p + 1 - j) * (((p + 1).descFactorial j : ℝ) / (p + 1).factorial) := by ring
    rw [e1, e2, descFactorial_div_factorial, descFactorial_div_factorial]
    congr 1
    · split_ifs <;> ring
    · split_ifs <;> ring

/-- The monomial model with the book's weight `σ = p!/(q-1)!` ((12.2.69)–(12.2.70)): the global
minimizer is `t* = a^{1/(p-q+1)}` and the minimum value is
`-(p-q+1)/((p+1) q!) a^{(p+1)/(p-q+1)}`. -/
theorem isMinOn_neg_monomial_add_regularization_book {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p)
    {a : ℝ} (ha : 0 < a) :
    IsMinOn (negMonomialRegModel p q (p.factorial / (q - 1).factorial) a) univ
        (a ^ (1 / ((p - q + 1 : ℕ) : ℝ))) ∧
      negMonomialRegModel p q (p.factorial / (q - 1).factorial) a
          (a ^ (1 / ((p - q + 1 : ℕ) : ℝ))) =
        -(((p - q + 1 : ℕ) : ℝ) / ((p + 1) * q.factorial)) *
          a ^ ((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)) := by
  have hq1f : (0 : ℝ) < (q - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos _
  have hlam : ((p.factorial / (q - 1).factorial : ℝ) * (q - 1).factorial / p.factorial) = 1 := by
    field_simp
  obtain ⟨h1, h2, -⟩ := isMinOn_neg_monomial_add_regularization hq hqp
    (σ := p.factorial / (q - 1).factorial) (by positivity) ha
  rw [hlam, div_one] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  rw [mul_assoc]
  congr 1
  have hR0 : ((p - q + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_one_add' ha.le]
  · congr 1
    push_cast [Nat.cast_sub hqp]
    have : (q : ℝ) ≤ p := by exact_mod_cast hqp
    have hne : (p : ℝ) - q + 1 ≠ 0 := by linarith
    field_simp
    ring
  · push_cast [Nat.cast_sub hqp]
    have : (q : ℝ) ≤ p := by exact_mod_cast hqp
    have : (0 : ℝ) < p - q + 1 := by linarith
    positivity

/-! ### The linear regularized model of Example 12.1.3 -/

/-- A sum `∑_{i=1}^j u_i` is nonnegative if `u_1 = 0`, the even terms are nonnegative and the
consecutive pairs `u_{2k} + u_{2k+1}` (`k ≥ 1`) are nonnegative. -/
private theorem sum_Icc_one_nonneg_of_pairs {u : ℕ → ℝ} (h1 : u 1 = 0) :
    ∀ j : ℕ, (∀ i ≤ j, 2 ≤ i → Even i → 0 ≤ u i) →
      (∀ k, 1 ≤ k → 2 * k + 1 ≤ j → 0 ≤ u (2 * k) + u (2 * k + 1)) →
      0 ≤ ∑ i ∈ Finset.Icc 1 j, u i
  | 0, _, _ => by simp
  | 1, _, _ => by simp [h1]
  | j + 2, he, hp => by
    have ih := sum_Icc_one_nonneg_of_pairs h1 (j + 1) (fun i hi => he i (by omega))
      (fun k hk1 hk => hp k hk1 (by omega))
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have := he (j + 2) le_rfl (by omega) ⟨k + 1, by omega⟩
      linarith
    · have ih' := sum_Icc_one_nonneg_of_pairs h1 j (fun i hi => he i (by omega))
        (fun k hk1 hk => hp k hk1 (by omega))
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have := hp (k + 1) (by omega) (by omega)
      rw [show 2 * (k + 1) = j + 1 by omega] at this
      linarith

/-- **Example 12.1.3 in one variable** ([cartis2022evaluation], (12.1.18)–(12.1.21)). Let
`p ≥ 1`, `β, σ > 0` and `m t = -β t + σ |t|^{p+1}/(p+1)!` on `ℝ`, with global minimizer
`t* = (β p!/σ)^{1/p}`. For `j ∈ [1, p]` and every radius `δ` with `(p - 1) δ ≤ 3 t*` (no restriction
when `j ≤ 2`), the `j`-th order Taylor measure of `m` at `t*` vanishes: `φ^δ_{m,j}(t*) = 0`.
Along `d = α t*` the Taylor decrease is `-σ t*^{p+1} ∑_{ℓ=2}^{j} α^ℓ/(ℓ!(p+1-ℓ)!)`, and the terms
of orders `2k, 2k+1` have a nonnegative sum when `|α| ≤ 3/(p-1)`. -/
theorem taylorMeasure_linearRegModel_eq_zero {p j : ℕ} (hj : j ∈ Icc 1 p) {β σ δ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ)
    (hδ : j ≤ 2 ∨ ((p : ℝ) - 1) * δ ≤ 3 * (β * p.factorial / σ) ^ (1 / (p : ℝ))) :
    taylorMeasure (ftaylorSeries ℝ (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1).factorial)
      ((β * p.factorial / σ) ^ (1 / (p : ℝ)))) j δ univ = 0 := by
  obtain ⟨hj1, hjp⟩ := hj
  have hp : 1 ≤ p := hj1.trans hjp
  set ts := (β * p.factorial / σ) ^ (1 / (p : ℝ)) with hts
  have hm : (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1).factorial) =
      negMonomialRegModel p 1 σ β := by
    funext t; simp [negMonomialRegModel]
  have hts' : (β / (σ * (1 - 1).factorial / p.factorial)) ^ (1 / ((p - 1 + 1 : ℕ) : ℝ)) = ts := by
    rw [hts, Nat.sub_add_cancel hp]
    congr 1
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
    field_simp
  obtain ⟨hmin, -, hder⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp hσ hβ
  rw [hts'] at hmin hder
  rw [hm]
  set m := negMonomialRegModel p 1 σ β
  have ht0 : 0 < ts := by rw [hts]; positivity
  have hd1 : iteratedDeriv 1 m ts = 0 := by
    rw [iteratedDeriv_one]
    exact (hmin.isLocalMin Filter.univ_mem).deriv_eq_zero
  have hdi : ∀ i, 2 ≤ i → i ≤ p + 1 →
      iteratedDeriv i m ts = σ * ts ^ (p + 1 - i) / (p + 1 - i).factorial := fun i hi2 hip => by
    rw [hder, ite_eq_right (by omega), ite_eq_left hip, zero_add]
  rcases lt_or_ge δ 0 with hneg | hδ0
  · rw [taylorMeasure_eq_sSup, Metric.closedBall_eq_empty.2 hneg, empty_inter, image_empty,
      Real.sSup_empty]
  refine le_antisymm (decrementMeasure_le ⟨0, Metric.mem_closedBall_self hδ0, mem_univ _⟩
    fun d hd => ?_) (taylorMeasure_nonneg _ _ (mem_univ _) hδ0)
  have hdδ : |d| ≤ δ := by simpa [Real.norm_eq_abs] using hd.1
  rw [FormalMultilinearSeries.taylorDecrement_eq, neg_nonpos]
  set u : ℕ → ℝ := fun i => (i.factorial : ℝ)⁻¹ * (d ^ i * iteratedDeriv i m ts) with hu
  have hsum : ∀ i, (i.factorial : ℝ)⁻¹ * ftaylorSeries ℝ m ts i (fun _ => d) = u i := fun i => by
    simp only [hu, ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  refine sum_Icc_one_nonneg_of_pairs (by simp [hu, hd1]) j (fun i hi hi2 hev => ?_)
    (fun k hk1 hk => ?_)
  · simp only [hu, hdi i hi2 (by omega)]
    have := hev.pow_nonneg d
    positivity
  · have hj2 : ¬ j ≤ 2 := by omega
    have hδ' := hδ.resolve_left hj2
    obtain ⟨N, hN⟩ : ∃ N, p = N + 2 * k + 1 := ⟨p - 2 * k - 1, by omega⟩
    subst hN
    simp only [hu, hdi (2 * k) (by omega) (by omega), hdi (2 * k + 1) (by omega) (by omega),
      show N + 2 * k + 1 + 1 - 2 * k = N + 1 + 1 by omega,
      show N + 2 * k + 1 + 1 - (2 * k + 1) = N + 1 by omega, Nat.factorial_succ (2 * k),
      Nat.factorial_succ (N + 1)]
    push_cast at hδ' ⊢
    have hdδ' : -δ ≤ d := (abs_le.1 hdδ).1
    have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have hkey : 0 ≤ (2 * k + 1 : ℝ) * ts + (N + 1 + 1) * d := by
      nlinarith [mul_le_mul_of_nonneg_left hδ' (by positivity : (0 : ℝ) ≤ 2 * k + 1),
        mul_nonneg (mul_nonneg (sub_nonneg.2 hK) hN0) hδ0, mul_nonneg (sub_nonneg.2 hK) hδ0,
        mul_nonneg (mul_nonneg (sub_nonneg.2 hK) (by positivity : (0 : ℝ) ≤ k + 1)) hδ0]
    have hA : 0 ≤ σ * ts ^ (N + 1) * d ^ (2 * k) /
        (((2 * k).factorial : ℝ) * (N + 1).factorial * (2 * k + 1) * (N + 1 + 1)) := by
      have := (even_two_mul k).pow_nonneg d
      positivity
    have e : ((2 * k).factorial : ℝ)⁻¹ * (d ^ (2 * k) * (σ * ts ^ (N + 1 + 1) /
          ((N + 1 + 1) * (N + 1).factorial))) +
        (((2 * k + 1) * (2 * k).factorial : ℝ))⁻¹ * (d ^ (2 * k + 1) * (σ * ts ^ (N + 1) /
          (N + 1).factorial)) =
        σ * ts ^ (N + 1) * d ^ (2 * k) /
          (((2 * k).factorial : ℝ) * (N + 1).factorial * (2 * k + 1) * (N + 1 + 1)) *
          ((2 * k + 1 : ℝ) * ts + (N + 1 + 1) * d) := by
      field_simp
      ring
    rw [e]
    exact mul_nonneg hA hkey


/-- **The top-order monomial model is approximately critical at its minimizer**
([cartis2022evaluation], (12.2.69)–(12.2.70) with `q = p`). For `p ≥ 1`, `a > 0` and
`m t = -a t^p/p! + p |t|^{p+1}/(p+1)!` (weight `σ = p!/(p-1)! = p`), whose global minimizer is
`t* = a`, the Taylor measures of `m` at `a` of every order `j ∈ [1, p]` vanish for radii `δ` with
`(p - 1) δ ≤ a`: the derivatives are `m^{(i)}(a) = (i-1) a^{p+1-i}/(p+1-i)!`, and the terms of
orders `2k, 2k+1` of the decrease have a nonnegative sum on `[-δ, δ]`. -/
theorem taylorMeasure_topMonomialRegModel_eq_zero {p j : ℕ} (hj : j ∈ Icc 1 p) {a δ : ℝ}
    (ha : 0 < a) (hδ : ((p : ℝ) - 1) * δ ≤ a) :
    taylorMeasure (ftaylorSeries ℝ (negMonomialRegModel p p p a) a) j δ univ = 0 := by
  obtain ⟨hj1, hjp⟩ := hj
  have hp : 1 ≤ p := hj1.trans hjp
  have hpσ : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨hmin, -, hder⟩ :=
    isMinOn_neg_monomial_add_regularization (p := p) (q := p) hp le_rfl hpσ ha
  have hts : (a / ((p : ℝ) * (p - 1).factorial / p.factorial)) ^ (1 / ((p - p + 1 : ℕ) : ℝ)) =
      a := by
    have hf : (p : ℝ) * (p - 1).factorial = p.factorial := by
      obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      push_cast [Nat.factorial_succ]; simp
    rw [Nat.sub_self, zero_add, Nat.cast_one, div_one, Real.rpow_one, hf,
      div_self (by positivity), div_one]
  rw [hts] at hmin hder
  set m := negMonomialRegModel p p p a
  have hd1 : iteratedDeriv 1 m a = 0 := by
    rw [iteratedDeriv_one]
    exact (hmin.isLocalMin Filter.univ_mem).deriv_eq_zero
  have hdi : ∀ N i, 2 ≤ i → p = N + i →
      iteratedDeriv i m a = (i - 1 : ℝ) * a ^ (N + 1) / (N + 1).factorial := fun N i hi2 hpi => by
    rw [hder, ite_eq_left (by omega), ite_eq_left (by omega),
      show p - i = N by omega, show p + 1 - i = N + 1 by omega, hpi, Nat.factorial_succ N]
    push_cast
    have hN : (0 : ℝ) < N.factorial := by positivity
    rw [pow_succ]
    field_simp
    ring
  rcases lt_or_ge δ 0 with hneg | hδ0
  · rw [taylorMeasure_eq_sSup, Metric.closedBall_eq_empty.2 hneg, empty_inter, image_empty,
      Real.sSup_empty]
  refine le_antisymm (decrementMeasure_le ⟨0, Metric.mem_closedBall_self hδ0, mem_univ _⟩
    fun d hd => ?_) (taylorMeasure_nonneg _ _ (mem_univ _) hδ0)
  have hdδ : |d| ≤ δ := by simpa [Real.norm_eq_abs] using hd.1
  rw [FormalMultilinearSeries.taylorDecrement_eq, neg_nonpos]
  set u : ℕ → ℝ := fun i => (i.factorial : ℝ)⁻¹ * (d ^ i * iteratedDeriv i m a) with hu
  have hsum : ∀ i, (i.factorial : ℝ)⁻¹ * ftaylorSeries ℝ m a i (fun _ => d) = u i := fun i => by
    simp only [hu, ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp only [hsum]
  refine sum_Icc_one_nonneg_of_pairs (by simp [hu, hd1]) j (fun i hi hi2 hev => ?_)
    (fun k hk1 hk => ?_)
  · obtain ⟨N, hN⟩ : ∃ N, p = N + i := ⟨p - i, by omega⟩
    simp only [hu, hdi N i hi2 hN]
    have := hev.pow_nonneg d
    have : (0 : ℝ) ≤ (i : ℝ) - 1 := by
      have : (2 : ℝ) ≤ i := by exact_mod_cast hi2
      linarith
    positivity
  · obtain ⟨N, hN⟩ : ∃ N, p = N + 2 * k + 1 := ⟨p - 2 * k - 1, by omega⟩
    simp only [hu, hdi (N + 1) (2 * k) (by omega) (by omega),
      hdi N (2 * k + 1) (by omega) (by omega), Nat.factorial_succ (2 * k),
      Nat.factorial_succ (N + 1)]
    have hdδ' : -δ ≤ d := (abs_le.1 hdδ).1
    have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have hpN : ((p : ℝ) - 1) = N + 2 * k := by rw [hN]; push_cast; ring
    rw [hpN] at hδ
    have hkey : 0 ≤ a * ((2 * k - 1) * (2 * k + 1)) + 2 * k * (N + 2) * d := by
      have h1 : -(2 * k * (N + 2) * δ) ≤ 2 * k * (N + 2) * d := by
        have := mul_le_mul_of_nonneg_left hdδ' (by positivity : (0 : ℝ) ≤ 2 * k * (N + 2))
        linarith
      have h2 : 2 * k * (N + 2) * δ ≤ 2 * k * a := by
        have h3 : (N + 2) * δ ≤ a := by nlinarith
        nlinarith
      have h5 : (0 : ℝ) ≤ (2 * k - 1) * (2 * k + 1) - 2 * k := by nlinarith
      have h4 := mul_nonneg ha.le h5
      nlinarith
    have hA : 0 ≤ d ^ (2 * k) * a ^ (N + 1) /
        (((2 * k).factorial : ℝ) * (N + 1).factorial * (2 * k + 1) * (N + 1 + 1)) := by
      have := (even_two_mul k).pow_nonneg d
      positivity
    push_cast
    have e : ((2 * k).factorial : ℝ)⁻¹ * (d ^ (2 * k) * ((2 * k - 1) * a ^ (N + 1 + 1) /
          ((N + 1 + 1) * (N + 1).factorial))) +
        (((2 * k + 1) * (2 * k).factorial : ℝ))⁻¹ * (d ^ (2 * k + 1) *
          ((2 * k + 1 - 1) * a ^ (N + 1) / (N + 1).factorial)) =
        d ^ (2 * k) * a ^ (N + 1) /
          (((2 * k).factorial : ℝ) * (N + 1).factorial * (2 * k + 1) * (N + 1 + 1)) *
          (a * ((2 * k - 1) * (2 * k + 1)) + 2 * k * (N + 2) * d) := by
      field_simp
      ring
    rw [e]
    exact mul_nonneg hA hkey

/-! ### Taylor data of functions of one variable -/

section OneDim

open Metric
open scoped Nat

/-- The derivative tensors of a function of one variable along `d`:
`∇^i G(y)[d]^i = G^{(i)}(y) d^i`. -/
theorem ftaylorSeries_real_apply (G : ℝ → ℝ) (y : ℝ) (i : ℕ) (d : ℝ) :
    ftaylorSeries ℝ G y i (fun _ => d) = iteratedDeriv i G y * d ^ i := by
  simp [ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, mul_comm]

/-- The Taylor decrement of a function of one variable:
`ΔT_{G,j}(y, d) = -∑_{i=1}^j G^{(i)}(y) d^i/i!`. -/
theorem taylorDecrement_real (G : ℝ → ℝ) (y : ℝ) (j : ℕ) (d : ℝ) :
    (ftaylorSeries ℝ G y).taylorDecrement j d =
      -∑ i ∈ Finset.Icc 1 j, iteratedDeriv i G y * d ^ i / i ! := by
  rw [FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ftaylorSeries_real_apply]
  ring

/-- If the derivatives of orders `1, …, j` vanish at `y`, the Taylor decrement of order `j`
vanishes. -/
theorem taylorDecrement_real_eq_zero {G : ℝ → ℝ} {y : ℝ} {j : ℕ}
    (h0 : ∀ i ∈ Finset.Icc 1 j, iteratedDeriv i G y = 0) (d : ℝ) :
    (ftaylorSeries ℝ G y).taylorDecrement j d = 0 := by
  rw [taylorDecrement_real, Finset.sum_eq_zero fun i hi => by rw [h0 i hi, zero_mul, zero_div],
    neg_zero]

/-- If, among the orders `1, …, j`, only the derivative of order `m` may be nonzero at `y`, then
`ΔT_{G,j}(y, d) = -G^{(m)}(y) d^m/m!`. -/
theorem taylorDecrement_real_spike {G : ℝ → ℝ} {y : ℝ} {j m : ℕ} (hm : m ∈ Finset.Icc 1 j)
    (h0 : ∀ i ∈ Finset.Icc 1 j, i ≠ m → iteratedDeriv i G y = 0) (d : ℝ) :
    (ftaylorSeries ℝ G y).taylorDecrement j d = -(iteratedDeriv m G y * d ^ m / m !) := by
  rw [taylorDecrement_real, Finset.sum_eq_single_of_mem m hm fun i hi him => by
    rw [h0 i hi him, zero_mul, zero_div]]

/-- The measure of a decrement of the form `a d^m` (`a ≥ 0`) over `[-δ, δ]` is `a δ^m`. -/
theorem taylorMeasure_real_monomial {D : FormalMultilinearSeries ℝ ℝ ℝ} {j m : ℕ} {a δ : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hD : ∀ d, D.taylorDecrement j d = a * d ^ m) :
    taylorMeasure D j δ univ = a * δ ^ m := by
  refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ, mem_univ _⟩
    fun d hd => ?_) ?_
  · have hdδ : |d| ≤ δ := by simpa [Real.norm_eq_abs] using hd.1
    rw [hD]
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) ha
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg d) hdδ m
  · have := taylorDecrement_le_taylorMeasure D j (S := univ) (d := δ)
      ⟨mem_closedBall_zero_iff.2 (by rw [Real.norm_eq_abs, abs_of_nonneg hδ]), mem_univ _⟩
    rwa [hD] at this

/-- The derivative tensors of a function of one variable have the norms of the derivatives:
`‖∇^i G(s) - ∇^i G(t)‖ = |G^{(i)}(s) - G^{(i)}(t)|`. -/
theorem norm_iteratedFDeriv_sub_real (G : ℝ → ℝ) (i : ℕ) (s t : ℝ) :
    ‖iteratedFDeriv ℝ i G s - iteratedFDeriv ℝ i G t‖ =
      |iteratedDeriv i G s - iteratedDeriv i G t| := by
  rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map, Real.norm_eq_abs]

/-- A derivative of order `j < q` of a `C^q` function of one variable whose next derivative is
bounded by `B` is `B`-Lipschitz (the mean value inequality
`Convex.norm_image_sub_le_of_norm_deriv_le` for `iteratedDeriv j g`). -/
theorem abs_iteratedDeriv_sub_le {g : ℝ → ℝ} {q j : ℕ} (hg : ContDiff ℝ q g)
    (hjq : j < q) {B : ℝ} (hB : ∀ t, |iteratedDeriv (j + 1) g t| ≤ B) (s t : ℝ) :
    |iteratedDeriv j g s - iteratedDeriv j g t| ≤ B * |s - t| := by
  have hd : Differentiable ℝ (iteratedDeriv j g) :=
    hg.differentiable_iteratedDeriv j (by exact_mod_cast hjq)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => hd y) (fun y _ => by
      rw [← iteratedDeriv_succ, Real.norm_eq_abs]; exact hB y) convex_univ (mem_univ t)
    (mem_univ s)
  simpa only [Real.norm_eq_abs] using this

/-- A function of one variable with `|G| ≤ B` is bounded below by `-B`. -/
theorem neg_le_of_abs_iteratedDeriv_zero_le {G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ t, |iteratedDeriv 0 G t| ≤ B) (t : ℝ) : -B ≤ G t := by
  have := hB t
  rw [iteratedDeriv_zero] at this
  exact (abs_le.1 this).1

/-- The ARqp model of one-variable data whose only nonzero derivative of order `1, …, p` at `y`
is the one of order `m`: `m(t) = G(y) + G^{(m)}(y) t^m/m! + σ |t|^{p+1}/(p+1)!`. -/
theorem regularizedModel_real_spike {G : ℝ → ℝ} {y : ℝ} {p m : ℕ} (hm : m ∈ Finset.Icc 1 p)
    (h0 : ∀ i ∈ Finset.Icc 1 p, i ≠ m → iteratedDeriv i G y = 0) (σ t : ℝ) :
    regularizedModel (ftaylorSeries ℝ G y) p σ t =
      G y + iteratedDeriv m G y * t ^ m / m ! + σ * |t| ^ (p + 1) / (p + 1)! := by
  have h1 : (ftaylorSeries ℝ G y).taylorSum p t = (ftaylorSeries ℝ G y).taylorSum p 0 -
      (ftaylorSeries ℝ G y).taylorDecrement p t := by
    rw [FormalMultilinearSeries.taylorDecrement]; ring
  have h00 : ftaylorSeries ℝ G y 0 0 = G y := by simp [ftaylorSeries]
  rw [regularizedModel_def, h1, taylorDecrement_real_spike hm h0,
    FormalMultilinearSeries.taylorSum_zero_right, h00, Real.norm_eq_abs]
  ring

/-- Adding a constant does not change the Taylor measures (of positive order). -/
theorem taylorMeasure_real_const_add (c : ℝ) (g : ℝ → ℝ) (y : ℝ) (j : ℕ) (δ : ℝ) (S : Set ℝ) :
    taylorMeasure (ftaylorSeries ℝ (fun t => c + g t) y) j δ S =
      taylorMeasure (ftaylorSeries ℝ g y) j δ S := by
  unfold taylorMeasure
  congr 1
  funext d
  rw [taylorDecrement_real, taylorDecrement_real]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iteratedDeriv_const_add (Finset.mem_Icc.1 hi).1 c]

/-- The global minimizer of the linear regularized model of Example 12.1.3 in one variable:
for `p ≥ 1`, `β, σ > 0`, `t ↦ -β t + σ |t|^{p+1}/(p+1)!` is globally minimized at
`t* = (β p!/σ)^{1/p} > 0`, with a negative minimal value. -/
theorem isMinOn_linearRegModel {p : ℕ} (hp : 1 ≤ p) {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) :
    IsMinOn (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1)!) univ
        ((β * p ! / σ) ^ (1 / (p : ℝ))) ∧
      -β * (β * p ! / σ) ^ (1 / (p : ℝ)) +
        σ * |(β * p ! / σ) ^ (1 / (p : ℝ))| ^ (p + 1) / (p + 1)! < 0 := by
  have hm : (fun t : ℝ => -β * t + σ * |t| ^ (p + 1) / (p + 1)!) =
      negMonomialRegModel p 1 σ β := by
    funext t; simp [negMonomialRegModel]
  have hts : (β / (σ * (1 - 1)! / p !)) ^ (1 / ((p - 1 + 1 : ℕ) : ℝ)) =
      (β * p ! / σ) ^ (1 / (p : ℝ)) := by
    rw [Nat.sub_add_cancel hp]
    congr 1
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
    field_simp
  obtain ⟨hmin, hval, -⟩ := isMinOn_neg_monomial_add_regularization le_rfl hp hσ hβ
  rw [hts] at hmin hval
  rw [hm]
  refine ⟨hmin, ?_⟩
  have ht : 0 < (β * p ! / σ) ^ (1 / (p : ℝ)) := by positivity
  have e : -β * (β * p ! / σ) ^ (1 / (p : ℝ)) +
      σ * |(β * p ! / σ) ^ (1 / (p : ℝ))| ^ (p + 1) / (p + 1)! =
      negMonomialRegModel p 1 σ β ((β * p ! / σ) ^ (1 / (p : ℝ))) := by
    simp [negMonomialRegModel]
  rw [e, hval]
  have hp' : (0 : ℝ) < ((p - 1 + 1 : ℕ) : ℝ) := by
    rw [Nat.sub_add_cancel hp]; exact_mod_cast hp
  have : 0 < ((p - 1 + 1 : ℕ) : ℝ) / ((p + 1) * (1 ! : ℕ)) * β *
      ((β * p ! / σ) ^ (1 / (p : ℝ))) ^ 1 := by positivity
  linarith

end OneDim

end Optimization
