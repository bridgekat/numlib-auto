import Numlib.Analysis.SpecialFunctions.EulerMaclaurin

/-!
# Richardson extrapolation and Romberg integration

A quantity `𝒜(h)` with an asymptotic expansion `α₀ + α₁ h + ⋯ + α_k h^k + R(h)`,
`|R(h)| ≤ C h^{k+1}`, is sampled at the geometric sequence `h_m = δ^m h`, `0 < δ < 1`. The
combination `(𝒜(δ h) - δ^p 𝒜(h))/(1 - δ^p)` kills the `h^p` term and keeps an expansion of the
same shape;
iterating gives the triangular *extrapolation table* whose `q`-th column converges at order
`q + 1` ([quarteroni2000numerical] §9.6, Property 9.2). *Romberg integration* is the table built
on the composite trapezoidal sums with `2^m` panels, whose expansion in `h²` is the
Euler–Maclaurin formula of `Numlib/Analysis/SpecialFunctions/EulerMaclaurin`; its first column
is the composite Simpson rule.

Everything is stated for the *sampled* sequence `A : ℕ → ℝ`, `A m = 𝒜(δ^m h)`, which is what the
algorithm consumes and which lets Romberg's parameter `η = h_m² = (1/4)^m (b - a)²` be an instance
without a square root: `Richardson.HasExpansion A δ h α k C` says
`|A m - ∑_{i ≤ k} α i (δ^m h)^i| ≤ C (δ^m h)^{k+1}` for every `m`. The constants are explicit
and independent of `m`, so the `O(·)` of the book is a genuine bound.

## Main definitions

* `Richardson.HasExpansion`, `Richardson.step`, `Richardson.table` — the expansion, one
  extrapolation step of order `p`, and the table (9.34).
* `Romberg.table` — the Romberg table, `Richardson.table` at `δ = 1/4` on the trapezoidal sums.

## Main results

* `Richardson.hasExpansion_step` — one step kills the `h^p` term and keeps an expansion with the
  coefficients `α_i (δ^i - δ^p)/(1 - δ^p)`.
* `Richardson.hasExpansion_table`, `Richardson.exists_abs_table_sub_le` — the `q`-th column has
  an expansion with `α₀` unchanged and `α_1, …, α_q` zero, hence
  `|A_{m,q} - α₀| ≤ C_q (δ^m h)^{q+1}` for `q ≤ m` (Property 9.2).
* `Richardson.abs_sub_sub_estimate_le` — the two-term a posteriori estimator behind (9.40).
* `Romberg.table_succ`, `Romberg.table_one_eq_simpsonSum` — the `4^{q+1}` recursion (9.37) and
  the identification of the first column with composite Simpson.
* `Romberg.hasExpansion_trapezoidSum`, `Romberg.exists_abs_table_sub_integral_le` — the
  Euler–Maclaurin expansion as a `HasExpansion`, and the convergence of Romberg's table at order
  `2(q + 1)` in the mesh.

## References

[quarteroni2000numerical] §9.6–9.7; [kress1998numerical] §9.5.
-/

open Filter Set Topology intervalIntegral
open scoped Nat

namespace Richardson

/-- **An asymptotic expansion, sampled geometrically**: `A m = 𝒜(δ^m h)` satisfies
`|A m - ∑_{i ≤ k} α i (δ^m h)^i| ≤ C (δ^m h)^{k+1}` for every `m`.

Reference: [quarteroni2000numerical], (9.33). -/
def HasExpansion (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ∀ m, |A m - ∑ i ∈ Finset.range (k + 1), α i * (δ ^ m * h) ^ i| ≤ C * (δ ^ m * h) ^ (k + 1)

/-- **One extrapolation step of order `p`**, `(A (m + 1) - δ^p A m)/(1 - δ^p)`: the book's
`ℬ(h) = (𝒜(δ h) - δ^p 𝒜(h))/(1 - δ^p)` at `h = δ^m h`.

Reference: [quarteroni2000numerical], §9.6. -/
noncomputable def step (A : ℕ → ℝ) (δ : ℝ) (p : ℕ) (m : ℕ) : ℝ :=
  (A (m + 1) - δ ^ p * A m) / (1 - δ ^ p)

/-- **The extrapolation table**: `table A δ m 0 = A m` and
`table A δ m (q + 1) = (table A δ m q - δ^{q+1} table A δ (m - 1) q)/(1 - δ^{q+1})`. Entries with
`m < q` are junk, as `m - 1` truncates.

Reference: [quarteroni2000numerical], (9.34). -/
noncomputable def table (A : ℕ → ℝ) (δ : ℝ) : ℕ → ℕ → ℝ
  | m, 0 => A m
  | m, q + 1 => (table A δ m q - δ ^ (q + 1) * table A δ (m - 1) q) / (1 - δ ^ (q + 1))

/-- The first column of the table is the sampled sequence. -/
@[simp]
theorem table_zero (A : ℕ → ℝ) (δ : ℝ) (m : ℕ) : table A δ m 0 = A m := rfl

/-- **The next column is one step applied to the previous one**:
`table A δ (m + 1) (q + 1) = step (fun m => table A δ m q) δ (q + 1) m`. -/
theorem table_succ (A : ℕ → ℝ) (δ : ℝ) (m q : ℕ) :
    table A δ (m + 1) (q + 1) = step (fun m => table A δ m q) δ (q + 1) m := by
  simp [table, step]

/-- **One step kills the `h^p` term and keeps the expansion.** If `HasExpansion A δ h α k C` with
`0 < δ < 1`, `0 < h` and `0 < p` (in use, `p ≤ k`), then the stepped sequence has the expansion
with coefficients `α̃_i = α_i (δ^i - δ^p)/(1 - δ^p)` — so `α̃_0 = α_0`, `α̃_p = 0` — and the
constant `C (δ^{k+1} + δ^p)/(1 - δ^p)`.

Reference: [quarteroni2000numerical], §9.6, the display after (9.33). -/
theorem hasExpansion_step {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : HasExpansion A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {p : ℕ}
    (hp : 0 < p) :
    HasExpansion (step A δ p) δ h (fun i => α i * (δ ^ i - δ ^ p) / (1 - δ ^ p)) k
      (C * (δ ^ (k + 1) + δ ^ p) / (1 - δ ^ p)) := by
  intro m
  have hδp : 0 < 1 - δ ^ p := by
    have : δ ^ p < 1 := pow_lt_one₀ hδ0.le hδ1 hp.ne'
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = δ ^ m * h := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu1 : δ ^ (m + 1) * h = δ * u := by rw [hu, pow_succ]; ring
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = A m - ∑ i ∈ Finset.range (k + 1), α i * u ^ i := ⟨_, rfl⟩
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = A (m + 1) - ∑ i ∈ Finset.range (k + 1), α i * (δ * u) ^ i :=
    ⟨_, rfl⟩
  have hR1 : |R₁| ≤ C * δ ^ (k + 1) * u ^ (k + 1) := by
    have := hA (m + 1)
    rw [hu1, mul_pow δ u (k + 1)] at this
    rw [hR₁]
    linarith [this]
  have hR0 : |R₀| ≤ C * u ^ (k + 1) := by
    rw [hR₀, hu]
    exact hA m
  -- the stepped remainder
  have hstep : step A δ p m - ∑ i ∈ Finset.range (k + 1),
      α i * (δ ^ i - δ ^ p) / (1 - δ ^ p) * u ^ i = (R₁ - δ ^ p * R₀) / (1 - δ ^ p) := by
    have e1 : ∑ i ∈ Finset.range (k + 1), α i * (δ * u) ^ i
        = ∑ i ∈ Finset.range (k + 1), α i * δ ^ i * u ^ i :=
      Finset.sum_congr rfl fun i _ => by rw [mul_pow]; ring
    have e2 : ∑ i ∈ Finset.range (k + 1), α i * (δ ^ i - δ ^ p) / (1 - δ ^ p) * u ^ i
        = (∑ i ∈ Finset.range (k + 1), α i * δ ^ i * u ^ i
          - δ ^ p * ∑ i ∈ Finset.range (k + 1), α i * u ^ i) / (1 - δ ^ p) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [step, hR₁, hR₀, e1, e2]
    field_simp
    ring
  rw [← hu, hstep, abs_div, abs_of_pos hδp, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hδp]
  calc |R₁ - δ ^ p * R₀| ≤ |R₁| + |δ ^ p * R₀| := abs_sub _ _
    _ = |R₁| + δ ^ p * |R₀| := by rw [abs_mul, abs_of_pos (pow_pos hδ0 p)]
    _ ≤ C * δ ^ (k + 1) * u ^ (k + 1) + δ ^ p * (C * u ^ (k + 1)) := by gcongr
    _ = C * (δ ^ (k + 1) + δ ^ p) * u ^ (k + 1) := by ring

/-- **The `q`-th column has an expansion with `α₀` unchanged and `α_1, …, α_q` zero**, in the
parameter `δ^m h` of its first ingredient: for `q ≤ k` there are `α'` and `C'` with `α' 0 = α 0`,
`α' i = 0` for `1 ≤ i ≤ q`, and `HasExpansion (fun m => table A δ (m + q) q) δ h α' k C'`.
Induction on `q` through `table_succ` and `hasExpansion_step`. -/
theorem hasExpansion_table {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : HasExpansion A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {q : ℕ}
    (hqk : q ≤ k) :
    ∃ (α' : ℕ → ℝ) (C' : ℝ), α' 0 = α 0 ∧ (∀ i, 1 ≤ i → i ≤ q → α' i = 0) ∧
      HasExpansion (fun m => table A δ (m + q) q) δ h α' k C' := by
  induction q with
  | zero => exact ⟨α, C, rfl, fun i h1 h0 => absurd (h1.trans h0) (by norm_num), by simpa using hA⟩
  | succ q ih =>
    obtain ⟨α', C', h0, hzero, hexp⟩ := ih (by omega)
    have hδp : 1 - δ ^ (q + 1) ≠ 0 := by
      have : δ ^ (q + 1) < 1 := pow_lt_one₀ hδ0.le hδ1 (Nat.succ_ne_zero q)
      linarith
    refine ⟨fun i => α' i * (δ ^ i - δ ^ (q + 1)) / (1 - δ ^ (q + 1)),
      C' * (δ ^ (k + 1) + δ ^ (q + 1)) / (1 - δ ^ (q + 1)), ?_, ?_, ?_⟩
    · simp only [pow_zero, h0]
      field_simp
    · intro i hi1 hiq
      rcases Nat.lt_or_ge i (q + 1) with hlt | hge
      · change α' i * (δ ^ i - δ ^ (q + 1)) / (1 - δ ^ (q + 1)) = 0
        rw [hzero i hi1 (by omega), zero_mul, zero_div]
      · obtain rfl : i = q + 1 := le_antisymm hiq hge
        change α' (q + 1) * (δ ^ (q + 1) - δ ^ (q + 1)) / (1 - δ ^ (q + 1)) = 0
        rw [sub_self, mul_zero, zero_div]
    · have := hasExpansion_step hexp hδ0 hδ1 hh (Nat.succ_pos q)
      refine fun m => ?_
      have e : table A δ (m + (q + 1)) (q + 1)
          = step (fun m => table A δ (m + q) q) δ (q + 1) m := by
        change (table A δ (m + (q + 1)) q - δ ^ (q + 1) * table A δ (m + (q + 1) - 1) q)
            / (1 - δ ^ (q + 1))
          = (table A δ (m + 1 + q) q - δ ^ (q + 1) * table A δ (m + q) q) / (1 - δ ^ (q + 1))
        rw [show m + (q + 1) - 1 = m + q by omega, show m + (q + 1) = m + 1 + q by ring]
      dsimp only
      rw [e]
      exact this m

/-- The powers of `u ∈ [0, 1 + h]` beyond `q + 1` are bounded by `(1 + h)^{k+1} u^{q+1}`, for
`j ≤ k + 1`. -/
private theorem pow_le_of_le {u h : ℝ} (hu : 0 ≤ u) (huh : u ≤ 1 + h) (hh : 0 < h) {q j k : ℕ}
    (hqj : q + 1 ≤ j) (hjk : j ≤ k + 1) : u ^ j ≤ (1 + h) ^ (k + 1) * u ^ (q + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = q + 1 + d := ⟨j - (q + 1), by omega⟩
  rw [pow_add, mul_comm]
  gcongr
  calc u ^ d ≤ (1 + h) ^ d := pow_le_pow_left₀ hu huh _
    _ ≤ (1 + h) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)

/-- An expansion whose coefficients `α 1, …, α q` vanish converges to `α 0` at order `q + 1`,
with an explicit constant. -/
theorem abs_sub_le_of_hasExpansion {B : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hB : HasExpansion B δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 < h) {q : ℕ}
    (hqk : q ≤ k) (hzero : ∀ i, 1 ≤ i → i ≤ q → α i = 0) (m : ℕ) :
    |B m - α 0| ≤ ((∑ i ∈ Finset.range (k + 1), |α i|) + |C|) * (1 + h) ^ (k + 1)
      * (δ ^ m * h) ^ (q + 1) := by
  set u : ℝ := δ ^ m * h with hu
  have hu0 : 0 ≤ u := by positivity
  have huh : u ≤ 1 + h := by
    have : δ ^ m ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have : u ≤ h := by rw [hu]; nlinarith
    linarith
  have hM : (0 : ℝ) ≤ (1 + h) ^ (k + 1) * u ^ (q + 1) := by positivity
  have hsum : ∑ i ∈ Finset.range (k + 1), α i * u ^ i
      = α 0 + ∑ i ∈ Finset.range k, α (i + 1) * u ^ (i + 1) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    ring
  have hterm : ∀ i ∈ Finset.range k, |α (i + 1) * u ^ (i + 1)|
      ≤ |α (i + 1)| * ((1 + h) ^ (k + 1) * u ^ (q + 1)) := by
    intro i hi
    have hik : i < k := Finset.mem_range.1 hi
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 _)]
    rcases Nat.lt_or_ge (i + 1) (q + 1) with hlt | hge
    · rw [hzero (i + 1) (by omega) (by omega)]
      simp
    · exact mul_le_mul_of_nonneg_left (pow_le_of_le hu0 huh hh hge (by omega)) (abs_nonneg _)
  have hrem : |B m - ∑ i ∈ Finset.range (k + 1), α i * u ^ i|
      ≤ |C| * ((1 + h) ^ (k + 1) * u ^ (q + 1)) := by
    refine (hB m).trans ?_
    calc C * u ^ (k + 1) ≤ |C| * u ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hu0 _)
      _ ≤ |C| * ((1 + h) ^ (k + 1) * u ^ (q + 1)) :=
          mul_le_mul_of_nonneg_left (pow_le_of_le hu0 huh hh (by omega) le_rfl) (abs_nonneg _)
  have h3 : B m - α 0 = (B m - ∑ i ∈ Finset.range (k + 1), α i * u ^ i)
      + ∑ i ∈ Finset.range k, α (i + 1) * u ^ (i + 1) := by
    rw [hsum]; ring
  calc |B m - α 0|
      ≤ |B m - ∑ i ∈ Finset.range (k + 1), α i * u ^ i|
          + |∑ i ∈ Finset.range k, α (i + 1) * u ^ (i + 1)| := by
        rw [h3]
        exact abs_add_le _ _
    _ ≤ |C| * ((1 + h) ^ (k + 1) * u ^ (q + 1))
        + ∑ i ∈ Finset.range k, |α (i + 1)| * ((1 + h) ^ (k + 1) * u ^ (q + 1)) := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ |C| * ((1 + h) ^ (k + 1) * u ^ (q + 1))
        + (∑ i ∈ Finset.range (k + 1), |α i|) * ((1 + h) ^ (k + 1) * u ^ (q + 1)) := by
        gcongr
        rw [← Finset.sum_mul, Finset.sum_range_succ']
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hM
    _ = _ := by ring

/-- **Property 9.2** ([quarteroni2000numerical] (9.35)), in the reading
`A_{m,q} = α₀ + O((δ^m h)^{q+1})` for `q ≤ m`: if `HasExpansion A δ h α k C` with `0 < δ < 1`,
`0 < h` and `q ≤ k`, there is `C'` with `|table A δ m q - α 0| ≤ C' (δ^m h)^{q+1}` for all
`m ≥ q`, `C'` independent of `m`. The book indexes (9.35) as `A_{m,n}` for `m = 0, …, n`, which
(9.34) does not define; this is the intended statement. -/
theorem exists_abs_table_sub_le {A : ℕ → ℝ} {δ h : ℝ} {α : ℕ → ℝ} {k : ℕ} {C : ℝ}
    (hA : HasExpansion A δ h α k C) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hh : 0 < h) {q : ℕ}
    (hqk : q ≤ k) :
    ∃ C' : ℝ, ∀ m, q ≤ m → |table A δ m q - α 0| ≤ C' * (δ ^ m * h) ^ (q + 1) := by
  obtain ⟨α', C', h0, hzero, hexp⟩ := hasExpansion_table hA hδ0 hδ1 hh hqk
  refine ⟨((∑ i ∈ Finset.range (k + 1), |α' i|) + |C'|) * (1 + h) ^ (k + 1) / δ ^ (q * (q + 1)),
    fun m hm => ?_⟩
  have hb := abs_sub_le_of_hasExpansion hexp hδ0 hδ1.le hh hqk hzero (m - q)
  simp only [Nat.sub_add_cancel hm, h0] at hb
  refine hb.trans (le_of_eq ?_)
  have hδq : (δ ^ (q * (q + 1)) : ℝ) ≠ 0 := by positivity
  have e : (δ ^ m * h) ^ (q + 1) = δ ^ (q * (q + 1)) * (δ ^ (m - q) * h) ^ (q + 1) := by
    rw [show m = (m - q) + q by omega, pow_add, Nat.add_sub_cancel]
    ring
  rw [e]
  field_simp

/-- **The a posteriori estimator** behind [quarteroni2000numerical] (9.40): if
`|A m - α₀ - c (δ^m h)^p| ≤ C (δ^m h)^q` for all `m`, with `0 < p` and `0 < δ < 1` (in use,
`p < q`), then
`|α₀ - A (m + 1) - δ^p/(1 - δ^p) (A (m + 1) - A m)| ≤ C (δ^q + δ^p)/(1 - δ^p) (δ^m h)^q`
for every `m`: with `δ = 1/2` this is `α₀ - A(2m) ≈ (A(2m) - A(m))/(2^p - 1)`, and the neglected
term is of the next order. -/
theorem abs_sub_sub_estimate_le {A : ℕ → ℝ} {δ h α₀ c C : ℝ} {p q : ℕ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hp : 0 < p)
    (hA : ∀ m, |A m - α₀ - c * (δ ^ m * h) ^ p| ≤ C * (δ ^ m * h) ^ q) (m : ℕ) :
    |α₀ - A (m + 1) - δ ^ p / (1 - δ ^ p) * (A (m + 1) - A m)|
      ≤ C * (δ ^ q + δ ^ p) / (1 - δ ^ p) * (δ ^ m * h) ^ q := by
  have hδp : 0 < 1 - δ ^ p := by
    have : δ ^ p < 1 := pow_lt_one₀ hδ0.le hδ1 (by omega)
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = δ ^ m * h := ⟨_, rfl⟩
  have hu1 : δ ^ (m + 1) * h = δ * u := by rw [hu, pow_succ]; ring
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = A m - α₀ - c * u ^ p := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : ℝ, E₁ = A (m + 1) - α₀ - c * (δ * u) ^ p := ⟨_, rfl⟩
  have hE1 : |E₁| ≤ C * δ ^ q * u ^ q := by
    have := hA (m + 1)
    rw [hu1, mul_pow δ u q] at this
    rw [hE₁]
    linarith [this]
  have hE0 : |E₀| ≤ C * u ^ q := by
    rw [hE₀, hu]
    exact hA m
  have hid : α₀ - A (m + 1) - δ ^ p / (1 - δ ^ p) * (A (m + 1) - A m)
      = -(E₁ - δ ^ p * E₀) / (1 - δ ^ p) := by
    rw [hE₁, hE₀, mul_pow]
    field_simp
    ring
  rw [← hu, hid, abs_div, abs_of_pos hδp, abs_neg, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hδp]
  calc |E₁ - δ ^ p * E₀| ≤ |E₁| + |δ ^ p * E₀| := abs_sub _ _
    _ = |E₁| + δ ^ p * |E₀| := by rw [abs_mul, abs_of_pos (pow_pos hδ0 p)]
    _ ≤ C * δ ^ q * u ^ q + δ ^ p * (C * u ^ q) := by gcongr
    _ = C * (δ ^ q + δ ^ p) * u ^ q := by ring

end Richardson

namespace Romberg

open Quadrature

/-- **The Romberg table**: Richardson extrapolation with `δ = 1/4` of the composite trapezoidal
sums on `2^m` panels, that is, `𝒜(η) = T(√η)` sampled at `η = (b - a)²/4^m`.

Reference: [quarteroni2000numerical], §9.6.1. -/
noncomputable def table (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℕ → ℝ :=
  Richardson.table (fun m => trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m)) (1 / 4)

/-- The first column of the Romberg table is the composite trapezoidal rule. -/
@[simp]
theorem table_zero (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    table f a b m 0 = trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m) := rfl

/-- **The Romberg recursion** ([quarteroni2000numerical], the display after (9.37)):
`A_{m,q+1} = (4^{q+1} A_{m,q} - A_{m-1,q})/(4^{q+1} - 1)`. -/
theorem table_succ (f : ℝ → ℝ) (a b : ℝ) (m q : ℕ) :
    table f a b m (q + 1)
      = (4 ^ (q + 1) * table f a b m q - table f a b (m - 1) q) / (4 ^ (q + 1) - 1) := by
  have h4 : (4 : ℝ) ^ (q + 1) ≠ 0 := by positivity
  have h4' : (4 : ℝ) ^ (q + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < 4 ^ (q + 1) := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero q)
    linarith
  simp only [table, Richardson.table, one_div_pow]
  field_simp

/-- Splitting a sum over `2N` terms into its even and odd terms. -/
private theorem sum_range_two_mul (g : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (2 * N), g j = ∑ i ∈ Finset.range N, (g (2 * i) + g (2 * i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

/-- **The first extrapolated column is composite Simpson**:
`A_{m+1,1} = S_{2^m}`, i.e. `(4 T_{2N} - T_N)/3 = S_N`, by reindexing the `2N`-panel trapezoidal
sum by parity.

Reference: [quarteroni2000numerical], §9.6.1 ("`T_1` is Simpson"). -/
theorem table_one_eq_simpsonSum (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    table f a b (m + 1) 1 = simpsonSum f a ((b - a) / 2 ^ m) (2 ^ m) := by
  rw [table_succ, Nat.add_sub_cancel, table_zero, table_zero, zero_add, pow_one]
  set h : ℝ := (b - a) / 2 ^ m with hh
  have h2 : (b - a) / (2 : ℝ) ^ (m + 1) = h / 2 := by rw [hh, pow_succ]; ring
  rw [h2, show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by ring, trapezoidSum, trapezoidSum, simpsonSum,
    sum_range_two_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  have e1 : a + (2 * (i : ℝ) + 1) * (h / 2) = a + i * h + h / 2 := by ring
  have e2 : a + (2 * (i : ℝ) + 1 + 1) * (h / 2) = a + (i + 1) * h := by ring
  have e3 : a + 2 * (i : ℝ) * (h / 2) = a + i * h := by ring
  rw [e1, e2, e3]
  ring

/-- The Euler–Maclaurin coefficients of the trapezoidal rule as a Richardson expansion in `h²`:
`α 0 = ∫_a^b f` and `α i = B_{2i}/(2i)! (f^{(2i-1)}(b) - f^{(2i-1)}(a))` for `i ≥ 1`. -/
noncomputable def eulerMaclaurinCoeff (f : ℝ → ℝ) (a b : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then ∫ t in a..b, f t
  else ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * (iteratedDeriv (2 * i - 1) f b
    - iteratedDeriv (2 * i - 1) f a)

/-- **Euler–Maclaurin as a Richardson expansion.** For `a < b` and `f` of class `C^{2k+2}` on an
open set containing `[a, b]`, the trapezoidal sums on `2^m` panels have the expansion
`HasExpansion (fun m => T_{2^m}) (1/4) ((b - a)²) (eulerMaclaurinCoeff f a b) k C` with
`C = |B_{2k+2}|/(2k+2)! (b - a) sup|f^{(2k+2)}|`: the parameter is `h_m² = (1/4)^m (b - a)²`.

Reference: [quarteroni2000numerical], §9.6.1. -/
theorem hasExpansion_trapezoidSum {a b : ℝ} (hab : a < b) {k : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C : ℝ, Richardson.HasExpansion (fun m => trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m)) (1 / 4)
      ((b - a) ^ 2) (eulerMaclaurinCoeff f a b) k C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab)
  refine ⟨|((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (2 * k + 2)! * (b - a) * M, fun m => ?_⟩
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  set h : ℝ := (b - a) / 2 ^ m with hh
  have h4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hh2 : (1 / 4 : ℝ) ^ m * (b - a) ^ 2 = h ^ 2 := by
    rw [hh, div_pow, div_pow, one_pow, h4]
    ring
  obtain ⟨η, hη, heq⟩ := EulerMaclaurin.trapezoidSum_eq_integral_add_sum_add_mul hab hU hUab hf
    (m := 2 ^ m) (by positivity)
  have hcast : ((2 ^ m : ℕ) : ℝ) = 2 ^ m := by push_cast; rfl
  rw [hcast] at heq
  -- the expansion sum is the Euler–Maclaurin sum
  have hsum : ∑ i ∈ Finset.range (k + 1), eulerMaclaurinCoeff f a b i * (h ^ 2) ^ i
      = (∫ t in a..b, f t) + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
          * h ^ (2 * i) * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a) := by
    rw [Finset.sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    simp only [eulerMaclaurinCoeff, ↓reduceIte, pow_zero, mul_one, Nat.succ_ne_zero,
      add_comm 1]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul]
    ring
  dsimp only
  rw [hh2, hsum, heq]
  have hMη : |iteratedDeriv (2 * k + 2) f η| ≤ M := hM η (Ioo_subset_Icc_self hη)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hMη
  rw [show (∫ t in a..b, f t) + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
      * h ^ (2 * i) * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a)
      + ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * h ^ (2 * k + 2) * (b - a)
        * iteratedDeriv (2 * k + 2) f η
      - ((∫ t in a..b, f t) + ∑ i ∈ Finset.Icc 1 k, ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)!
        * h ^ (2 * i) * (iteratedDeriv (2 * i - 1) f b - iteratedDeriv (2 * i - 1) f a))
      = ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (2 * k + 2)! * (b - a) * (h ^ 2) ^ (k + 1)
        * iteratedDeriv (2 * k + 2) f η by rw [← pow_mul]; ring]
  rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * k + 2)!),
    abs_of_pos (by linarith : (0 : ℝ) < b - a),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (h ^ 2) ^ (k + 1))]
  calc |((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (2 * k + 2)! * (b - a) * (h ^ 2) ^ (k + 1)
        * |iteratedDeriv (2 * k + 2) f η|
      ≤ |((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (2 * k + 2)! * (b - a) * (h ^ 2) ^ (k + 1) * M := by
        gcongr
    _ = _ := by ring

/-- **Convergence of Romberg integration** ([quarteroni2000numerical] §9.6.1): for `a < b` and
`f` of class `C^{2q+2}` on an open set containing `[a, b]`, there is `C` with
`|A_{m,q} - ∫_a^b f| ≤ C ((b - a)/2^m)^{2(q+1)}` for all `m ≥ q`. -/
theorem exists_abs_table_sub_integral_le {a b : ℝ} (hab : a < b) {q : ℕ} {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * q + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C : ℝ, ∀ m, q ≤ m →
      |table f a b m q - ∫ t in a..b, f t| ≤ C * ((b - a) / 2 ^ m) ^ (2 * (q + 1)) := by
  obtain ⟨C, hC⟩ := hasExpansion_trapezoidSum hab hU hUab hf (k := q)
  obtain ⟨C', hC'⟩ := Richardson.exists_abs_table_sub_le hC (by norm_num) (by norm_num)
    (by nlinarith) le_rfl
  refine ⟨C', fun m hm => ?_⟩
  have h := hC' m hm
  simp only [eulerMaclaurinCoeff, ↓reduceIte] at h
  refine h.trans (le_of_eq ?_)
  have h4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  congr 1
  rw [pow_mul]
  congr 1
  rw [div_pow, div_pow, one_pow, h4]
  ring

end Romberg
