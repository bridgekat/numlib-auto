import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Approximation.HermiteSpline

/-!
# Slow-convergence examples of first and second order

The sharpness ("slow convergence") constructions of [cartis2022evaluation] Chapters 2 and 3:
values and derivatives prescribed at an increasing sequence of points on the line are interpolated
by a function whose derivatives are bounded and Lipschitz with constants **independent of the
tolerance `ε`** (Hermite interpolation, `Hermite.exists_contDiff_interpolating_jets_bounded`), and
then lifted to any real inner product space as a ridge function `x ↦ g ⟪e, x⟫`
(`Numlib.Optimization.Complexity.SlowExample.Ridge`).

Each data family is parametrized by a sequence of step factors `θ k ∈ [a, b]`, and its constants
depend only on `a` and `b`. Thus a single lemma serves every method whose steps on the data are
`θ_k` times a reference step, whatever factors the method picks.

## The slow-example hierarchy

The modules `Numlib.Optimization.Complexity.SlowExample.*` are organized by the
structure they need:
* `Ridge` — ridge functions `g ⟪e, ·⟫` and their derivatives, Hessians and Taylor data;
* `Basic` (this file) — first- and second-order one-dimensional data (Chapters 2–3);
* `SeparatedJets` — gluing quadratic jets at separated points of a finite-dimensional space
  (Theorem 3.1.1);
* `HighOrder` — data of arbitrary order with jets having one nonzero derivative (Chapter 12);
* `ARp` — Taylor models of ridge functions at such jets and runs of the ARp method on them;
* `Slit` — the constrained example on a hyperplane with a parallel half-space (§14.2);
* `TRq` — explicit prefixes of runs of the trust-region method TRq continued by arbitrary runs,
  and transfer of runs between objectives (§14.2–§14.3);
* `ZigZag` — the two-dimensional zig-zag example of Theorem 2.2.5.

Each file states interpolation data as properties of a function of one variable (values,
derivatives, Lipschitz constants independent of `ε`) together with the abscissae and steps of
the run; the run predicates of the individual methods are checked against these data where the
methods are defined.

## Main definitions and results

* `Optimization.exists_slowFirstOrder_interpolant` — the data of Theorem 2.2.3 (steepest descent,
  and the first-order trust-region and regularization methods).
* `Optimization.exists_slowNegCurvature_interpolant` — the data (3.2.24) of Theorem 3.2.7: slow
  convergence to second-order criticality.
* `Optimization.secondOrderK`, `secondOrderF`, `secondOrderG`, `secondOrderH` — the data
  (3.5.11)–(3.5.12) with their elementary bounds, and `Optimization.ceil_rpow_facts`.
* `Optimization.exists_slowSecondOrder_interpolant` — the data (3.5.12) of Theorem 3.5.4: slow
  convergence to first-order criticality for second-order methods.
* `Optimization.secondOrderX`, `Optimization.exists_slowSecondOrder_run_data` — the same data at
  the abscissae of given step factors, with the termination test `|G'(x_k)| ≤ ε` first holding at
  `k_ε` (Corollary 3.5.5); `Optimization.contDiff_two_rescale_bounds` — rescaling `c G(u/c)`.

## Implementation notes

The integrality assumption of Theorem 2.2.3 (`ε⁻²` is an integer) is a hypothesis
`k_ε ε² = 1`. In the negative-curvature example (3.2.23)–(3.2.27) the abscissae are
`x_k = k ε` (with `θ ≡ 1`); only boundedness of `f` is used, which avoids requiring `ε⁻³` to be an
integer.
-/

open Set
open scoped RealInnerProductSpace

namespace Optimization

/-! ### Small sums of the Hermite consistency condition -/

theorem sum_Icc_zero_one (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 0 1, φ i = φ 0 + φ 1 := by
  rw [show Finset.Icc 0 1 = {0, 1} by decide, Finset.sum_pair (by norm_num)]

theorem sum_Icc_zero_two (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 0 2, φ i = φ 0 + φ 1 + φ 2 := by
  rw [show Finset.Icc 0 2 = {0, 1, 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num), add_assoc]

theorem sum_Icc_one_two (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 1 2, φ i = φ 1 + φ 2 := by
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]

/-- The Hermite consistency condition (A.32) for `p = 1`, in expanded form. -/
theorem hermite_consistency_one {a b : ℕ → ℝ} {s κ : ℝ}
    (h0 : |b 0 - (a 0 + a 1 * s)| ≤ κ * s ^ 2) (h1 : |b 1 - a 1| ≤ κ * s) :
    ∀ j ≤ 1, |b j - ∑ i ∈ Finset.Icc j 1, a i * s ^ (i - j) / (i - j).factorial| ≤
      κ * s ^ (1 - j + 1) := by
  intro j hj
  interval_cases j
  · simpa [sum_Icc_zero_one] using h0
  · simpa using h1

/-- The Hermite consistency condition (A.32) for `p = 2`, in expanded form. -/
theorem hermite_consistency_two {a b : ℕ → ℝ} {s κ : ℝ}
    (h0 : |b 0 - (a 0 + a 1 * s + a 2 * s ^ 2 / 2)| ≤ κ * s ^ 3)
    (h1 : |b 1 - (a 1 + a 2 * s)| ≤ κ * s ^ 2) (h2 : |b 2 - a 2| ≤ κ * s) :
    ∀ j ≤ 2, |b j - ∑ i ∈ Finset.Icc j 2, a i * s ^ (i - j) / (i - j).factorial| ≤
      κ * s ^ (2 - j + 1) := by
  intro j hj
  interval_cases j
  · simpa [sum_Icc_zero_two, Nat.factorial] using h0
  · simpa [sum_Icc_one_two] using h1
  · simpa using h2

/-! ### First-order data (Theorem 2.2.3) -/

/-- **First-order slow example** ([cartis2022evaluation], proof of Theorem 2.2.3,
(2.2.14)–(2.2.22)).
For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0` depending only on `a, b` such that:
for every `ε ∈ (0, 1]` with `k_ε = ε⁻²` an integer, every `θ` with `θ k ∈ [a, b]`, and with
`ω_k = ε (k_ε - k)/k_ε`, `g_k = -(ε + ω_k)`, `x_0 = 0`, `x_{k+1} = x_k - θ_k g_k`, `f_0 = 4 b`,
`f_{k+1} = f_k - θ_k g_k²`, there is a `C¹` function `G : ℝ → ℝ` with `L`-Lipschitz derivative,
`|G|, |G'| ≤ B`, `G (x k) = f_k` and `G' (x k) = g_k` for `k ≤ k_ε`. The book's case is
`θ ≡ t_ini`. The recurrences and the bounds on `θ` are only required for `k < k_ε`, and `x 0` is
arbitrary. -/
theorem exists_slowFirstOrder_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (kε : ℕ) (θ x f : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (kε : ℝ) * ε ^ 2 = 1 → (∀ k < kε, θ k ∈ Icc a b) →
      (∀ k < kε, x (k + 1) = x k + θ k * (ε + ε * ((kε : ℝ) - k) / kε)) → f 0 = 4 * b →
      (∀ k < kε, f (k + 1) = f k - θ k * (ε + ε * ((kε : ℝ) - k) / kε) ^ 2) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∀ s t, |deriv G s - deriv G t| ≤ L * |s - t|) ∧
        (∀ t, |G t| ≤ B) ∧ (∀ t, |deriv G t| ≤ B) ∧
        ∀ k ≤ kε, G (x k) = f k ∧ deriv G (x k) = -(ε + ε * ((kε : ℝ) - k) / kε) := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (1 / a) (max (4 * b) 2) with hκ
  have hκa : 1 / a ≤ κ := le_max_left _ _
  have hκb : 4 * b ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ2 : 2 ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 1 hκ0
  refine ⟨L, B, hL, hB, fun ε kε θ x f hε hε1 hk hθ hx hf0 hf => ?_⟩
  set ω : ℕ → ℝ := fun k => ε * ((kε : ℝ) - k) / kε with hω
  have hx' : ∀ k < kε, x (k + 1) = x k + θ k * (ε + ω k) := hx
  have hf' : ∀ k < kε, f (k + 1) = f k - θ k * (ε + ω k) ^ 2 := hf
  have hkε : (0 : ℝ) < kε := by
    rcases Nat.eq_zero_or_pos kε with h | h
    · rw [h] at hk
      norm_num at hk
    · exact_mod_cast h
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k ∧ ω k ≤ ε := fun k hk' => by
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    simp only [ω]
    refine ⟨div_nonneg (mul_nonneg hε.le (by linarith)) hkε.le, ?_⟩
    rw [div_le_iff₀ hkε]
    nlinarith
  have hωs : ∀ k, ω k - ω (k + 1) = ε ^ 3 := fun k => by
    simp only [ω]
    push_cast
    field_simp
    nlinarith
  clear_value ω
  clear hx hf
  -- steps
  have hstep : ∀ k < kε, a * ε ≤ θ k * (ε + ω k) ∧ θ k * (ε + ω k) ≤ 2 * b * ε :=
    fun k hk' => by
      obtain ⟨h0, h1⟩ := hω0 k hk'.le
      obtain ⟨ha', hb'⟩ := hθ k hk'
      constructor <;> nlinarith
  -- function values
  have hfsum : ∀ k ≤ kε, f k = 4 * b - ∑ i ∈ Finset.range k, θ i * (ε + ω i) ^ 2 := by
    intro k
    induction k with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      rw [hf' k (by omega), ih (by omega), Finset.sum_range_succ]
      ring
  have hfb : ∀ k ≤ kε, 0 ≤ f k ∧ f k ≤ 4 * b := fun k hk' => by
    rw [hfsum k hk']
    have hterm : ∀ i ∈ Finset.range k, 0 ≤ θ i * (ε + ω i) ^ 2 ∧
        θ i * (ε + ω i) ^ 2 ≤ b * (2 * ε) ^ 2 := fun i hi => by
      have hi' : i ≤ kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨h0, h1⟩ := hω0 i hi'
      obtain ⟨ha', hb'⟩ := hθ i (by have := Finset.mem_range.1 hi; omega)
      have hθ0 : 0 ≤ θ i := by linarith
      constructor
      · positivity
      · have h2 : (ε + ω i) ^ 2 ≤ (2 * ε) ^ 2 := by nlinarith
        nlinarith
    have hs0 := Finset.sum_nonneg fun i hi => (hterm i hi).1
    have hs1 : ∑ i ∈ Finset.range k, θ i * (ε + ω i) ^ 2 ≤ k * (b * (2 * ε) ^ 2) := by
      have := Finset.sum_le_sum fun i hi => (hterm i hi).2
      simpa using this
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    have hs2 : (k : ℝ) * (b * (2 * ε) ^ 2) ≤ 4 * b :=
      calc (k : ℝ) * (b * (2 * ε) ^ 2) ≤ kε * (b * (2 * ε) ^ 2) :=
            mul_le_mul_of_nonneg_right hk'' (by positivity)
        _ = 4 * b * (kε * ε ^ 2) := by ring
        _ = 4 * b := by rw [hk, mul_one]
    constructor <;> linarith
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j => if j = 0 then f k else -(ε + ω k) with hF
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * (ε + ω k) := fun k hk => by
    rw [hx' k hk]; ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk' => by
      have := (hstep k hk').1
      rw [← sub_pos, hgap k hk']
      exact lt_of_lt_of_le (by positivity) this)
    (fun k hk' => by rw [hgap k hk']; nlinarith [(hstep k hk').2])
    (fun k hk' j hj => by
      obtain ⟨h0, h1⟩ := hω0 k hk'
      interval_cases j
      · simp only [F, ↓reduceIte]
        rw [abs_le]
        constructor <;> linarith [hfb k hk']
      · simp only [F, one_ne_zero, ↓reduceIte]
        rw [abs_neg, abs_of_nonneg (by linarith)]
        linarith)
    (fun k hk' => by
      refine hermite_consistency_one ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, hgap k hk', hf' k hk']
        have : f k - θ k * (ε + ω k) ^ 2 - (f k + -(ε + ω k) * (θ k * (ε + ω k))) = 0 := by
          ring
        rw [this, abs_zero]
        positivity
      · simp only [F, one_ne_zero, ↓reduceIte, hgap k hk']
        have hs := (hstep k hk').1
        rw [show -(ε + ω (k + 1)) - -(ε + ω k) = ε ^ 3 by linarith [hωs k],
          abs_of_nonneg (by positivity)]
        have h1 : ε ^ 3 ≤ ε := by
          have : ε ^ 2 ≤ 1 := by nlinarith
          nlinarith
        calc ε ^ 3 ≤ ε := h1
          _ = 1 / a * (a * ε) := by field_simp
          _ ≤ κ * (θ k * (ε + ω k)) := mul_le_mul hκa hs (by positivity) hκ0)
  refine ⟨G, hGc, fun s t => ?_, fun t => ?_, fun t => ?_, fun k hk' => ⟨?_, ?_⟩⟩
  · simpa [iteratedDeriv_one] using hGL s t
  · simpa using hGB 0 (Nat.zero_le 1) t
  · simpa [iteratedDeriv_one] using hGB 1 le_rfl t
  · simpa [F] using hGj k hk' 0 (Nat.zero_le 1)
  · have := hGj k hk' 1 le_rfl
    simp only [iteratedDeriv_one, F, one_ne_zero, ↓reduceIte] at this
    rw [this, hω]

/-! ### Second-order data, slow to second-order criticality (Theorem 3.2.7) -/

/-- **Negative-curvature slow example** ([cartis2022evaluation], proof of Theorem 3.2.7, (3.2.23)–
(3.2.27)). For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0` depending only on
`a, b` such that: for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε⁻³⌉₊`, `c_k = 2 - k/k_ε`,
`H_k = -ε c_k`, steps `s_k = θ_k ε` (`θ k ∈ [a, b]`), `x_{k+1} = x_k + s_k`, `f_0 = 1`,
`f_{k+1} = f_k + H_k s_k²/2`, there is a `C²` function `G : ℝ → ℝ` with `L`-Lipschitz second
derivative, `|G^{(j)}| ≤ B` (`j ≤ 2`), and `G (x k) = f_k`, `G' (x k) = 0`, `G'' (x k) = H_k` for
`k ≤ k_ε`. TR2 uses `θ ≡ 1`, so that `x_k = k ε` in (3.2.25). The recurrences and the bounds on `θ`
are only required for `k < k_ε`, and `x 0` is arbitrary. -/
theorem exists_slowNegCurvature_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x f : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, θ k ∈ Icc a b) →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, x (k + 1) = x k + θ k * ε) → f 0 = 1 →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, f (k + 1) =
        f k + -ε * (2 - k / ⌈(ε ^ 3)⁻¹⌉₊) * (θ k * ε) ^ 2 / 2) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        (∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        ∀ k ≤ ⌈(ε ^ 3)⁻¹⌉₊, G (x k) = f k ∧ deriv G (x k) = 0 ∧
          iteratedDeriv 2 G (x k) = -ε * (2 - k / ⌈(ε ^ 3)⁻¹⌉₊) := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (2 * b / a ^ 2) (max (1 / a) (max (1 + 2 * b ^ 2) (max 2 b))) with hκ
  have hκ1 : 2 * b / a ^ 2 ≤ κ := le_max_left _ _
  have hκ2 : 1 / a ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ3 : 1 + 2 * b ^ 2 ≤ κ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ4 : 2 ≤ κ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ5 : b ≤ κ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 2 hκ0
  refine ⟨L, B, hL, hB, fun ε θ x f hε hε1 hθ hx hf0 hf => ?_⟩
  set kε : ℕ := ⌈(ε ^ 3)⁻¹⌉₊ with hkεdef
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hkε : (0 : ℝ) < kε := by exact_mod_cast hkε1
  have hkε3 : (kε : ℝ) * ε ^ 3 ≤ 2 := by
    have h := Nat.ceil_lt_add_one (inv_nonneg.2 (pow_nonneg hε.le 3))
    rw [← hkεdef] at h
    have hε3 : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hε1
    have : (kε : ℝ) * ε ^ 3 < ((ε ^ 3)⁻¹ + 1) * ε ^ 3 :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [add_mul, inv_mul_cancel₀ (by positivity), one_mul] at this
    linarith
  set c : ℕ → ℝ := fun k => 2 - k / kε with hc
  have hf' : ∀ k < kε, f (k + 1) = f k + -ε * c k * (θ k * ε) ^ 2 / 2 := hf
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
  clear hf
  have hθ0 : ∀ k < kε, 0 < θ k := fun k hk => ha.trans_le (hθ k hk).1
  -- function values
  have hfsum : ∀ k ≤ kε, f k = 1 - ∑ i ∈ Finset.range k, ε * c i * (θ i * ε) ^ 2 / 2 := by
    intro k
    induction k with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      rw [hf' k (by omega), ih (by omega), Finset.sum_range_succ]
      ring
  have hfb : ∀ k ≤ kε, |f k| ≤ 1 + 2 * b ^ 2 := fun k hk => by
    rw [hfsum k hk]
    have hterm : ∀ i ∈ Finset.range k, 0 ≤ ε * c i * (θ i * ε) ^ 2 / 2 ∧
        ε * c i * (θ i * ε) ^ 2 / 2 ≤ b ^ 2 * ε ^ 3 := fun i hi => by
      have hi' : i ≤ kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨h1, h2⟩ := hc12 i hi'
      have hik : i < kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨ha', hb'⟩ := hθ i hik
      have hθ0 := hθ0 i hik
      constructor
      · have : 0 ≤ c i := by linarith
        positivity
      · have h3 : (θ i * ε) ^ 2 ≤ (b * ε) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_right hb' hε.le
        have h4 : ε * c i ≤ ε * 2 := mul_le_mul_of_nonneg_left h2 hε.le
        calc ε * c i * (θ i * ε) ^ 2 / 2 ≤ ε * 2 * (b * ε) ^ 2 / 2 := by gcongr
          _ = b ^ 2 * ε ^ 3 := by ring
    have hs0 := Finset.sum_nonneg fun i hi => (hterm i hi).1
    have hs1 : ∑ i ∈ Finset.range k, ε * c i * (θ i * ε) ^ 2 / 2 ≤ k * (b ^ 2 * ε ^ 3) := by
      have := Finset.sum_le_sum fun i hi => (hterm i hi).2
      simpa using this
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have hs2 : (k : ℝ) * (b ^ 2 * ε ^ 3) ≤ 2 * b ^ 2 := by
      calc (k : ℝ) * (b ^ 2 * ε ^ 3) ≤ kε * (b ^ 2 * ε ^ 3) :=
            mul_le_mul_of_nonneg_right hk' (by positivity)
        _ = b ^ 2 * (kε * ε ^ 3) := by ring
        _ ≤ b ^ 2 * 2 := mul_le_mul_of_nonneg_left hkε3 (by positivity)
        _ = 2 * b ^ 2 := by ring
    rw [abs_le]
    constructor <;> nlinarith
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j => if j = 0 then f k else if j = 1 then 0 else -ε * c k with hF
  have h21 : (2 : ℕ) ≠ 1 := by norm_num
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * ε := fun k hk => by rw [hx k hk]; ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk => by rw [← sub_pos, hgap k hk]; exact mul_pos (hθ0 k hk) hε)
    (fun k hk => by
      rw [hgap k hk]
      calc θ k * ε ≤ b * 1 := mul_le_mul (hθ k hk).2 hε1 hε.le hb.le
        _ ≤ κ := by linarith)
    (fun k hk j hj => by
      obtain ⟨h1, h2⟩ := hc12 k hk
      interval_cases j
      · simpa [F] using (hfb k hk).trans hκ3
      · simpa [F] using hκ0
      · simp only [F, ↓reduceIte, OfNat.ofNat_ne_zero, h21]
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith)
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hc12 k hk.le
      obtain ⟨ha', hb'⟩ := hθ k hk
      have hθk := hθ0 k hk
      refine hermite_consistency_two ?_ ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk, hf' k hk]
        have : f k + -ε * c k * (θ k * ε) ^ 2 / 2 -
            (f k + 0 * (θ k * ε) + -ε * c k * (θ k * ε) ^ 2 / 2) = 0 := by ring
        rw [this, abs_zero]
        positivity
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        have e : (0 : ℝ) - (0 + -ε * c k * (θ k * ε)) = c k * θ k * ε ^ 2 := by ring
        rw [e, abs_of_nonneg (by positivity)]
        have h3 : c k * θ k ≤ 2 * b := by nlinarith
        have h4 : 2 * b ≤ κ * θ k ^ 2 := by
          have : 2 * b / a ^ 2 * a ^ 2 ≤ κ * θ k ^ 2 :=
            mul_le_mul hκ1 (pow_le_pow_left₀ ha.le ha' 2) (by positivity) hκ0
          rwa [div_mul_cancel₀ _ (by positivity)] at this
        calc c k * θ k * ε ^ 2 ≤ 2 * b * ε ^ 2 := by gcongr
          _ ≤ κ * θ k ^ 2 * ε ^ 2 := by gcongr
          _ = κ * (θ k * ε) ^ 2 := by ring
      · simp only [F, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        have e : -ε * c (k + 1) - -ε * c k = ε / kε := by
          rw [show -ε * c (k + 1) - -ε * c k = ε * (c k - c (k + 1)) by ring, hcs]
          ring
        rw [e, abs_of_nonneg (by positivity)]
        have h3 : ε / kε ≤ ε := div_le_self hε.le (by exact_mod_cast hkε1)
        have h4 : 1 ≤ κ * θ k := by
          have : 1 / a * a ≤ κ * θ k := mul_le_mul hκ2 ha' ha.le hκ0
          rwa [one_div_mul_cancel ha.ne'] at this
        nlinarith)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · simpa [F] using hGj k hk 0 (Nat.zero_le 2)
  · simpa [F, iteratedDeriv_one] using hGj k hk 1 (by norm_num)
  · have := hGj k hk 2 le_rfl
    simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte] at this
    rw [this, hc]

/-! ### The data (3.5.12) -/

/-- `k_ε = ⌈ε^{-3/2}⌉` (3.5.11). -/
noncomputable def secondOrderK (ε : ℝ) : ℕ := ⌈ε ^ (-(3 / 2 : ℝ))⌉₊

/-- The function values `f_k = 1 - k ε^{3/2}/2` of (3.5.12). -/
noncomputable def secondOrderF (ε : ℝ) (k : ℕ) : ℝ := 1 - k * ε ^ (3 / 2 : ℝ) / 2

/-- The derivatives `g_k = -2 ε f_k` of (3.5.12). -/
noncomputable def secondOrderG (ε : ℝ) (k : ℕ) : ℝ := -2 * ε * secondOrderF ε k

/-- The second derivatives `H_k = 4 ε^{1/2} f_k²` of (3.5.12). -/
noncomputable def secondOrderH (ε : ℝ) (k : ℕ) : ℝ := 4 * ε ^ (1 / 2 : ℝ) * secondOrderF ε k ^ 2

theorem secondOrderH_def (ε : ℝ) (k : ℕ) :
    secondOrderH ε k = 4 * ε ^ (1 / 2 : ℝ) * secondOrderF ε k ^ 2 :=
  rfl

section Data

variable {ε : ℝ}

private theorem rpow_three_halves_mul (hε : 0 < ε) :
    ε ^ (-(3 / 2 : ℝ)) * ε ^ (3 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add hε]; simp

theorem secondOrderF_gt_half (hε : 0 < ε) {k : ℕ} (hk : k < secondOrderK ε) :
    1 / 2 < secondOrderF ε k := by
  have hp : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have h1 : (k : ℝ) < ε ^ (-(3 / 2 : ℝ)) := Nat.lt_ceil.1 hk
  have h2 : (k : ℝ) * ε ^ (3 / 2 : ℝ) < 1 := by
    have := mul_lt_mul_of_pos_right h1 hp
    rwa [rpow_three_halves_mul hε] at this
  unfold secondOrderF; linarith

theorem secondOrderF_le_one (hε : 0 < ε) (k : ℕ) : secondOrderF ε k ≤ 1 := by
  have : 0 ≤ (k : ℝ) * ε ^ (3 / 2 : ℝ) / 2 := by
    have := Real.rpow_pos_of_pos hε (3 / 2 : ℝ); positivity
  unfold secondOrderF; linarith

theorem secondOrderF_K_le_half (hε : 0 < ε) : secondOrderF ε (secondOrderK ε) ≤ 1 / 2 := by
  have hp : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have h1 : ε ^ (-(3 / 2 : ℝ)) ≤ (secondOrderK ε : ℝ) := Nat.le_ceil _
  have h2 : 1 ≤ (secondOrderK ε : ℝ) * ε ^ (3 / 2 : ℝ) := by
    have := mul_le_mul_of_nonneg_right h1 hp.le
    rwa [rpow_three_halves_mul hε] at this
  unfold secondOrderF; linarith

theorem secondOrderF_pos (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ} (hk : k ≤ secondOrderK ε) :
    0 < secondOrderF ε k := by
  have hp : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hp1 : ε ^ (3 / 2 : ℝ) < 1 := Real.rpow_lt_one hε.le hε1 (by norm_num)
  have h1 : (secondOrderK ε : ℝ) < ε ^ (-(3 / 2 : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hε _).le
  have h2 : (k : ℝ) * ε ^ (3 / 2 : ℝ) < 2 := by
    have hk' : (k : ℝ) ≤ secondOrderK ε := by exact_mod_cast hk
    have := mul_lt_mul_of_pos_right (hk'.trans_lt h1) hp
    rw [add_mul, rpow_three_halves_mul hε, one_mul] at this
    linarith
  unfold secondOrderF; linarith

end Data

/-- Facts on `k_ε = ⌈ε^{-3/2}⌉`: `k ε^{3/2} < 1` for `k < k_ε`, and `1 ≤ k_ε ε^{3/2} ≤ 2`. -/
theorem ceil_rpow_facts {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, (k : ℝ) * ε ^ (3 / 2 : ℝ) < 1) ∧
      1 ≤ (⌈ε ^ (-(3 / 2 : ℝ))⌉₊ : ℝ) * ε ^ (3 / 2 : ℝ) ∧
      (⌈ε ^ (-(3 / 2 : ℝ))⌉₊ : ℝ) * ε ^ (3 / 2 : ℝ) ≤ 2 := by
  have he : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have he1 : ε ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hε.le hε1 (by norm_num)
  have hneg : ε ^ (-(3 / 2 : ℝ)) = (ε ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg hε.le _
  rw [hneg]
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · have h2 := mul_lt_mul_of_pos_right (Nat.lt_ceil.1 hk) he
    rwa [inv_mul_cancel₀ he.ne'] at h2
  · have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (ε ^ (3 / 2 : ℝ))⁻¹) he.le
    rwa [inv_mul_cancel₀ he.ne'] at h2
  · have := Nat.ceil_lt_add_one (inv_nonneg.2 he.le)
    have h2 := mul_lt_mul_of_pos_right this he
    rw [add_mul, inv_mul_cancel₀ he.ne'] at h2
    linarith

/-! ### Second-order data, slow to first-order criticality (Theorem 3.5.4) -/

/-- **Second-order slow example** ([cartis2022evaluation], (3.5.11)–(3.5.19) and the proof of
Theorem 3.5.4 in Appendix B). For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0`
depending only on `a, b` such that: for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-3/2}⌉₊`,
`f_k = 1 - k ε^{3/2}/2`, `g_k = -2 ε f_k`, `H_k = 4 ε^{1/2} f_k²` (3.5.12) and
`x_{k+1} = x_k + θ_k ε^{1/2}/(2 f_k)` (3.5.19) (`θ k ∈ [a, b]`), there is a `C²` function
`G : ℝ → ℝ` with `L`-Lipschitz second derivative, `|G^{(j)}| ≤ B` (`j ≤ 2`), interpolating
`(f_k, g_k, H_k)` at `x_k` for `k ≤ k_ε`. The recurrence and the bounds on `θ` are only required
for `k < k_ε`, and `x 0` is arbitrary. -/
theorem exists_slowSecondOrder_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, θ k ∈ Icc a b) →
      (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊,
        x (k + 1) = x k + θ k * ε ^ (1 / 2 : ℝ) / (2 * (1 - k * ε ^ (3 / 2 : ℝ) / 2))) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        (∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        ∀ k ≤ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, G (x k) = 1 - k * ε ^ (3 / 2 : ℝ) / 2 ∧
          deriv G (x k) = -2 * ε * (1 - k * ε ^ (3 / 2 : ℝ) / 2) ∧
          iteratedDeriv 2 G (x k) = 4 * ε ^ (1 / 2 : ℝ) * (1 - k * ε ^ (3 / 2 : ℝ) / 2) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (4 * (1 + b) ^ 2 / a ^ 3) (max (4 * (1 + 2 * b) / a ^ 2) (max (8 / a)
    (max 4 b))) with hκ
  have hκ1 : 4 * (1 + b) ^ 2 / a ^ 3 ≤ κ := le_max_left _ _
  have hκ2 : 4 * (1 + 2 * b) / a ^ 2 ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ3 : 8 / a ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ4 : 4 ≤ κ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ5 : b ≤ κ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 2 hκ0
  refine ⟨L, B, hL, hB, fun ε θ x hε hε1 hθ hx => ?_⟩
  -- pass to `r = ε^{1/2}`
  set r : ℝ := √ε with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.2 hε1
  have hεr : ε = r ^ 2 := (Real.sq_sqrt hε.le).symm
  have h12 : ε ^ (1 / 2 : ℝ) = r := (Real.sqrt_eq_rpow ε).symm
  have h32 : ε ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 * (3 : ℕ) by norm_num, Real.rpow_mul_natCast hε.le, h12]
  have hm32 : ε ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by rw [Real.rpow_neg hε.le, h32]
  rw [h12, h32, hm32]
  simp only [h12, h32, hm32] at hx hθ
  clear_value r
  subst hεr
  clear h12 h32 hm32 hrdef
  set kε : ℕ := ⌈(r ^ 3)⁻¹⌉₊ with hkεdef
  have hkε2 : (kε : ℝ) * r ^ 3 ≤ 2 := by
    have h := Nat.ceil_lt_add_one (inv_nonneg.2 (pow_nonneg hr.le 3))
    rw [← hkεdef] at h
    have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr.le hr1
    have : (kε : ℝ) * r ^ 3 < ((r ^ 3)⁻¹ + 1) * r ^ 3 :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [add_mul, inv_mul_cancel₀ (by positivity), one_mul] at this
    linarith
  set f : ℕ → ℝ := fun k => 1 - k * r ^ 3 / 2 with hfdef
  have hx' : ∀ k < kε, x (k + 1) = x k + θ k * r / (2 * f k) := hx
  have hfs : ∀ k, f (k + 1) = f k - r ^ 3 / 2 := fun k => by
    simp only [f]
    push_cast
    ring
  have hf1 : ∀ k, f k ≤ 1 := fun k => by
    simp only [f]
    have : 0 ≤ (k : ℝ) * r ^ 3 / 2 := by positivity
    linarith
  have hf0 : ∀ k ≤ kε, 0 ≤ f k := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    simp only [f]
    nlinarith [pow_pos hr 3]
  have hfh : ∀ k < kε, 1 / 2 < f k := fun k hk => by
    have h := (Nat.lt_ceil).1 (hkεdef ▸ hk : k < ⌈(r ^ 3)⁻¹⌉₊)
    have : (k : ℝ) * r ^ 3 < 1 := by
      have := mul_lt_mul_of_pos_right h (pow_pos hr 3)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    simp only [f]
    linarith
  clear_value f
  clear hx
  have hθ0 : ∀ k < kε, 0 < θ k := fun k hk => ha.trans_le (hθ k hk).1
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j =>
    if j = 0 then f k else if j = 1 then -2 * r ^ 2 * f k else 4 * r * f k ^ 2 with hF
  have h21 : (2 : ℕ) ≠ 1 := by norm_num
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * r / (2 * f k) := fun k hk => by
    rw [hx' k hk]; ring
  -- the step is at least `θ r / 2 ≥ a r / 2` and at most `b`
  have hstep : ∀ k < kε, a * r / 2 ≤ θ k * r / (2 * f k) ∧ θ k * r / (2 * f k) ≤ b := by
    intro k hk
    have hfk := hfh k hk
    have hf1k := hf1 k
    obtain ⟨ha', hb'⟩ := hθ k hk
    have har : a * r ≤ θ k * r := mul_le_mul_of_nonneg_right ha' hr.le
    have hbr : θ k * r ≤ b * 1 := mul_le_mul hb' hr1 hr.le hb.le
    constructor
    · rw [le_div_iff₀ (by linarith)]
      have : a * r * f k ≤ a * r := mul_le_of_le_one_right (by positivity) hf1k
      calc a * r / 2 * (2 * f k) = a * r * f k := by ring
        _ ≤ θ k * r := this.trans har
    · rw [div_le_iff₀ (by linarith)]
      have : b * 1 ≤ b * (2 * f k) := mul_le_mul_of_nonneg_left (by linarith) hb.le
      linarith
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk => by
      rw [← sub_pos, hgap k hk]
      have := hfh k hk
      have := hθ0 k hk
      positivity)
    (fun k hk => by rw [hgap k hk]; linarith [(hstep k hk).2])
    (fun k hk j hj => by
      have h0 := hf0 k hk
      have h1 := hf1 k
      have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
      interval_cases j
      · simp only [F, ↓reduceIte]
        rw [abs_of_nonneg h0]
        linarith
      · simp only [F, one_ne_zero, ↓reduceIte]
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith [mul_le_mul hr2 h1 h0 zero_le_one]
      · simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte]
        rw [abs_of_nonneg (by positivity)]
        have : f k ^ 2 ≤ 1 := pow_le_one₀ h0 h1
        nlinarith [mul_le_mul hr1 this (by positivity) zero_le_one])
    (fun k hk => by
      have hfk := hfh k hk
      have hf1k := hf1 k
      have hf0' := hf0 (k + 1) hk
      have hf1' := hf1 (k + 1)
      have hθk := hθ0 k hk
      obtain ⟨ha', hb'⟩ := hθ k hk
      obtain ⟨hs1, -⟩ := hstep k hk
      set s := θ k * r / (2 * f k) with hsdef
      have hs0 : 0 ≤ a * r / 2 := by positivity
      have hfne : f k ≠ 0 := by linarith
      refine hermite_consistency_two ?_ ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        rw [← hsdef]
        have e : f (k + 1) - (f k + -2 * r ^ 2 * f k * s + 4 * r * f k ^ 2 * s ^ 2 / 2) =
            -(r ^ 3 * (1 - θ k) ^ 2 / 2) := by
          rw [hfs, hsdef]
          field_simp
          ring
        rw [e, abs_neg, abs_of_nonneg (by positivity)]
        have h1 : (1 - θ k) ^ 2 ≤ (1 + b) ^ 2 := by nlinarith
        have h2 : (a * r / 2) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs0 hs1 3
        have h3 : 4 * (1 + b) ^ 2 / a ^ 3 * (a * r / 2) ^ 3 = (1 + b) ^ 2 * r ^ 3 / 2 := by
          field_simp
          ring
        calc r ^ 3 * (1 - θ k) ^ 2 / 2 ≤ (1 + b) ^ 2 * r ^ 3 / 2 := by nlinarith [pow_pos hr 3]
          _ = 4 * (1 + b) ^ 2 / a ^ 3 * (a * r / 2) ^ 3 := h3.symm
          _ ≤ κ * s ^ 3 := mul_le_mul hκ1 h2 (by positivity) hκ0
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        rw [← hsdef]
        have e : -2 * r ^ 2 * f (k + 1) - (-2 * r ^ 2 * f k + 4 * r * f k ^ 2 * s) =
            r ^ 5 - 2 * r ^ 2 * θ k * f k := by
          rw [hfs, hsdef]
          field_simp
          ring
        rw [e]
        have hr5 : r ^ 5 ≤ r ^ 2 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
        have h1 : |r ^ 5 - 2 * r ^ 2 * θ k * f k| ≤ (1 + 2 * b) * r ^ 2 := by
          rw [abs_le]
          have h0 : 0 ≤ r ^ 2 * θ k * f k := by positivity
          have hθf : θ k * f k ≤ b * 1 := mul_le_mul hb' hf1k (by linarith) hb.le
          have h1 : r ^ 2 * θ k * f k ≤ r ^ 2 * b :=
            calc r ^ 2 * θ k * f k = r ^ 2 * (θ k * f k) := by ring
              _ ≤ r ^ 2 * (b * 1) := mul_le_mul_of_nonneg_left hθf (by positivity)
              _ = r ^ 2 * b := by ring
          have h5 : 0 ≤ r ^ 5 := by positivity
          have h2 : 0 ≤ r ^ 2 := by positivity
          constructor <;> linarith
        have h2 : (a * r / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs0 hs1 2
        have h3 : 4 * (1 + 2 * b) / a ^ 2 * (a * r / 2) ^ 2 = (1 + 2 * b) * r ^ 2 := by
          field_simp
          ring
        calc |r ^ 5 - 2 * r ^ 2 * θ k * f k| ≤ (1 + 2 * b) * r ^ 2 := h1
          _ = 4 * (1 + 2 * b) / a ^ 2 * (a * r / 2) ^ 2 := h3.symm
          _ ≤ κ * s ^ 2 := mul_le_mul hκ2 h2 (by positivity) hκ0
      · simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte, hgap k hk]
        rw [← hsdef]
        have e : 4 * r * f (k + 1) ^ 2 - 4 * r * f k ^ 2 = -(2 * r ^ 4 * (f (k + 1) + f k)) := by
          rw [hfs]
          ring
        rw [e, abs_neg, abs_of_nonneg (by positivity)]
        have hr4 : r ^ 4 ≤ r := by
          calc r ^ 4 ≤ r ^ 1 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
            _ = r := pow_one r
        have h3 : 8 / a * (a * r / 2) = 4 * r := by
          field_simp
          ring
        have hsum : f (k + 1) + f k ≤ 2 := by linarith
        calc 2 * r ^ 4 * (f (k + 1) + f k) ≤ 2 * r * 2 :=
              mul_le_mul (by linarith) hsum (by linarith) (by positivity)
          _ = 8 / a * (a * r / 2) := by rw [h3]; ring
          _ ≤ κ * s := mul_le_mul hκ3 hs1 hs0 hκ0)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · have := hGj k hk 0 (Nat.zero_le 2)
    simp only [F, ↓reduceIte, iteratedDeriv_zero] at this
    rw [this, hfdef]
  · have := hGj k hk 1 (by norm_num)
    simp only [F, one_ne_zero, ↓reduceIte, iteratedDeriv_one] at this
    rw [this, hfdef]
  · have := hGj k hk 2 le_rfl
    simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte] at this
    rw [this, hfdef]

/-! ### Runs along the data (3.5.12) -/

/-- The abscissae `x_0 = 0`, `x_{k+1} = x_k + θ_k ε^{1/2}/(2 f_k)` (3.5.19) of the data (3.5.12)
for step factors `θ`. -/
noncomputable def secondOrderX (θ : ℕ → ℝ) (ε : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, θ j * ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε j)

@[simp]
theorem secondOrderX_zero (θ : ℕ → ℝ) (ε : ℝ) : secondOrderX θ ε 0 = 0 := by
  simp [secondOrderX]

theorem secondOrderX_succ (θ : ℕ → ℝ) (ε : ℝ) (k : ℕ) :
    secondOrderX θ ε (k + 1) =
      secondOrderX θ ε k + θ k * ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε k) :=
  Finset.sum_range_succ _ _

theorem secondOrderF_succ (ε : ℝ) (k : ℕ) :
    secondOrderF ε (k + 1) = secondOrderF ε k - ε ^ (3 / 2 : ℝ) / 2 := by
  simp only [secondOrderF]; push_cast; ring

/-- The termination test along the data (3.5.12): `|g_k| ≤ ε` holds (for `k ≤ k_ε`) exactly at
`k = k_ε`. -/
theorem abs_secondOrderG_le_iff {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {k : ℕ}
    (hk : k ≤ secondOrderK ε) : |secondOrderG ε k| ≤ ε ↔ secondOrderK ε ≤ k := by
  have hF0 := (secondOrderF_pos hε hε1 hk).le
  rw [secondOrderG, show -2 * ε * secondOrderF ε k = -(2 * ε * secondOrderF ε k) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  constructor
  · intro h
    by_contra hlt
    nlinarith [secondOrderF_gt_half hε (not_le.1 hlt)]
  · intro h
    rw [le_antisymm hk h]
    nlinarith [secondOrderF_K_le_half hε]

/-- **Second-order slow runs** ([cartis2022evaluation], (3.5.12), (3.5.19)): the interpolant of
`Optimization.exists_slowSecondOrder_interpolant` at the abscissae `Optimization.secondOrderX`
of the step factors `θ`, for `ε ∈ (0, 1)`, with the termination test `|G'(x_k)| ≤ ε` holding
exactly at `k = k_ε`. A method whose step at `x_k` is `θ_k ε^{1/2}/(2 f_k)` runs along these
points, whatever the factors `θ_k ∈ [a, b]` it picks. -/
theorem exists_slowSecondOrder_run_data {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ : ℕ → ℝ), 0 < ε → ε < 1 →
      (∀ k < secondOrderK ε, θ k ∈ Icc a b) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        (∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        ∀ k ≤ secondOrderK ε, G (secondOrderX θ ε k) = secondOrderF ε k ∧
          deriv G (secondOrderX θ ε k) = secondOrderG ε k ∧
          iteratedDeriv 2 G (secondOrderX θ ε k) = secondOrderH ε k ∧
          (|deriv G (secondOrderX θ ε k)| ≤ ε ↔ secondOrderK ε ≤ k) := by
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_interpolant ha hab
  refine ⟨L, B, hL, hB, fun ε θ hε hε1 hθ => ?_⟩
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε θ (secondOrderX θ ε) hε hε1.le hθ
    (fun k _ => secondOrderX_succ θ ε k)
  refine ⟨G, hG, hGL, hGB, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hGk k hk
  have h2' : deriv G (secondOrderX θ ε k) = secondOrderG ε k := h2
  exact ⟨h1, h2', h3, by rw [h2']; exact abs_secondOrderG_le_iff hε hε1 hk⟩

/-- **Rescaling a second-order interpolant**: for `0 < c ≤ 1`, the function `c G₀(u/c)` of a
`C²` function `G₀` with `L`-Lipschitz second derivative and `|G₀^{(j)}| ≤ B` (`j ≤ 2`) is `C²`
with `j`-th derivative `c c^{-j} G₀^{(j)}(u/c)`, `L/c²`-Lipschitz second derivative and
derivatives bounded by `B/c²`. -/
theorem contDiff_two_rescale_bounds {G₀ : ℝ → ℝ} {c L B : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hG₀ : ContDiff ℝ 2 G₀)
    (hGL : ∀ s t, |iteratedDeriv 2 G₀ s - iteratedDeriv 2 G₀ t| ≤ L * |s - t|)
    (hGB : ∀ j ≤ 2, ∀ t, |iteratedDeriv j G₀ t| ≤ B) :
    ContDiff ℝ 2 (fun u => c * G₀ (c⁻¹ * u)) ∧
      (∀ j ≤ 2, ∀ u, iteratedDeriv j (fun u => c * G₀ (c⁻¹ * u)) u =
        c * c⁻¹ ^ j * iteratedDeriv j G₀ (c⁻¹ * u)) ∧
      (∀ u v, |iteratedDeriv 2 (fun u => c * G₀ (c⁻¹ * u)) u -
        iteratedDeriv 2 (fun u => c * G₀ (c⁻¹ * u)) v| ≤ L / c ^ 2 * |u - v|) ∧
      ∀ j ≤ 2, ∀ u, |iteratedDeriv j (fun u => c * G₀ (c⁻¹ * u)) u| ≤ B / c ^ 2 := by
  set G : ℝ → ℝ := fun u => c * G₀ (c⁻¹ * u)
  have hG : ContDiff ℝ 2 G := contDiff_const.mul (hG₀.comp (contDiff_const.mul contDiff_id))
  have hid : ∀ j ≤ 2, ∀ u, iteratedDeriv j G u = c * c⁻¹ ^ j * iteratedDeriv j G₀ (c⁻¹ * u) := by
    intro j hj u
    have h1 : iteratedDeriv j G u = c * iteratedDeriv j (fun v => G₀ (c⁻¹ * v)) u :=
      iteratedDeriv_const_mul_field c _
    rw [h1, iteratedDeriv_comp_const_mul (hG₀.of_le (by exact_mod_cast hj)) c⁻¹]
    ring
  have hc2 : c * c⁻¹ ^ 2 = c⁻¹ := by field_simp
  have hc1' : c * c⁻¹ ^ 1 = 1 := by field_simp
  refine ⟨hG, hid, fun u v => ?_, fun j hj u => ?_⟩
  · rw [hid 2 le_rfl, hid 2 le_rfl, hc2, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hc0)]
    have := hGL (c⁻¹ * u) (c⁻¹ * v)
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hc0)] at this
    calc c⁻¹ * |iteratedDeriv 2 G₀ (c⁻¹ * u) - iteratedDeriv 2 G₀ (c⁻¹ * v)|
        ≤ c⁻¹ * (L * (c⁻¹ * |u - v|)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = L / c ^ 2 * |u - v| := by field_simp
  · rw [hid j hj, abs_mul, abs_of_pos (by positivity)]
    have hpow : c * c⁻¹ ^ j ≤ 1 / c ^ 2 := by
      interval_cases j
      · rw [pow_zero, mul_one, le_div_iff₀ (by positivity)]
        nlinarith [pow_le_one₀ hc0.le hc1 (n := 3)]
      · rw [hc1', le_div_iff₀ (by positivity), one_mul]; exact pow_le_one₀ hc0.le hc1
      · rw [hc2, one_div, inv_le_inv₀ hc0 (by positivity)]; nlinarith
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hGB 0 (by norm_num) 0)
    calc c * c⁻¹ ^ j * |iteratedDeriv j G₀ (c⁻¹ * u)| ≤ 1 / c ^ 2 * B :=
          mul_le_mul hpow (hGB j hj _) (abs_nonneg _) (by positivity)
      _ = B / c ^ 2 := by ring

/-! ### The linearly decreasing excess of the slow examples

The levels of the slow examples exceed their final value by `c (κ - k)/κ`, which decreases
linearly from `c` at `k = 0` to `0` at `k = κ`. -/

/-- The excess `c (κ - k)/κ` is nonnegative up to `κ`. -/
theorem slowGap_nonneg {c : ℝ} (hc : 0 ≤ c) {κ k : ℕ} (hk : k ≤ κ) :
    0 ≤ c * ((κ : ℝ) - k) / κ := by
  have : (k : ℝ) ≤ κ := by exact_mod_cast hk
  have : 0 ≤ (κ : ℝ) - k := by linarith
  positivity

/-- The excess `c (κ - k)/κ` is positive before `κ`. -/
theorem slowGap_pos {c : ℝ} (hc : 0 < c) {κ k : ℕ} (hk : k < κ) : 0 < c * ((κ : ℝ) - k) / κ := by
  have : (k : ℝ) < κ := by exact_mod_cast hk
  have : 0 < (κ : ℝ) - k := by linarith
  have : (0 : ℝ) < κ := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  positivity

/-- The excess `c (κ - k)/κ` is at most `c`. -/
theorem slowGap_le {c : ℝ} (hc : 0 ≤ c) (κ k : ℕ) : c * ((κ : ℝ) - k) / κ ≤ c := by
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · simpa using hc
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  rw [div_le_iff₀ hκ']
  nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

end Optimization
