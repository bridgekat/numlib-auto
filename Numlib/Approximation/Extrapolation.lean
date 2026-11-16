/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.EulerMaclaurin

/-!
# Richardson extrapolation and Romberg integration

Let a quantity $\mathcal{A}(h)$ have an asymptotic expansion $\mathcal{A}(h) = \alpha_0 + \alpha_1
h + \dots + \alpha_k h^k + R(h)$ with $|R(h)| \le C h^{k+1}$, and sample it on the geometric
sequence $h_m = \delta^m h$, $0 < \delta < 1$. The combination
$$\frac{\mathcal{A}(\delta h) - \delta^p \mathcal{A}(h)}{1 - \delta^p}$$
removes the term in $h^p$ and keeps an expansion of the same form. **Richardson extrapolation**
iterates this step. It gives a triangular extrapolation table whose $q$-th column converges to
$\alpha_0$ at the order $q + 1$ (Property 9.2 of [quarteroni2000numerical]). **Romberg integration**
is the table built on the composite trapezoidal sums with $2^m$ panels. Their expansion in $h^2$ is
the Euler–Maclaurin formula of `Numlib.Analysis.SpecialFunctions.EulerMaclaurin`, and the first
extrapolated column is the composite Simpson rule. The presentation follows §9.6 and §9.7 of
[quarteroni2000numerical] and §9.5 of [kress1998numerical].

## Main definitions

* `Richardson.HasExpansion`: a sampled sequence $A_m = \mathcal{A}(\delta^m h)$ has an expansion of
  order $k$ with an explicit constant.
* `Richardson.step`: one extrapolation step of order $p$.
* `Richardson.table`: the extrapolation table (9.34) of [quarteroni2000numerical].
* `Romberg.table`: the Romberg table, which is `Richardson.table` with $\delta = 1/4$ on the
  composite trapezoidal sums.
* `Romberg.eulerMaclaurinCoeff`: the coefficients of the Euler–Maclaurin expansion of the
  trapezoidal rule in $h^2$.

## Main results

* `Richardson.hasExpansion_step`: one step removes the term in $h^p$ and keeps an expansion, with
  the coefficients $\alpha_i (\delta^i - \delta^p)/(1 - \delta^p)$.
* `Richardson.hasExpansion_table`: the $q$-th column has an expansion with the same $\alpha_0$ and
  with $\alpha_1 = \dots = \alpha_q = 0$.
* `Richardson.exists_abs_table_sub_le`: $|A_{m,q} - \alpha_0| \le C_q (\delta^m h)^{q+1}$ for
  $q \le m$.
* `Richardson.abs_sub_sub_estimate_le`: the a posteriori error estimate behind (9.40) of
  [quarteroni2000numerical].
* `Romberg.table_succ`: the Romberg recursion $A_{m,q+1} = (4^{q+1} A_{m,q} - A_{m-1,q})/(4^{q+1} -
  1)$.
* `Romberg.table_one_eq_simpsonSum`: the first extrapolated column is the composite Simpson rule.
* `Romberg.hasExpansion_trapezoidSum`: the Euler–Maclaurin formula as an expansion in the sense of
  `Richardson.HasExpansion`.
* `Romberg.exists_abs_table_sub_integral_le`: the $q$-th Romberg column converges to the integral at
  the order $2(q + 1)$ in the mesh.

## Implementation notes

* All results are about the sampled sequence $A_m = \mathcal{A}(\delta^m h)$, given as `A : ℕ → ℝ`,
  which is what the algorithm uses. Then Romberg's parameter $\eta_m = h_m^2 = (1/4)^m (b - a)^2$ is
  a case of the general theory without a square root.
* The constants in the expansions are explicit and independent of $m$. So the $O(\cdot)$ of
  [quarteroni2000numerical] is a bound with a constant.
-/

open Filter Set Topology intervalIntegral
open scoped Nat

namespace Richardson

/-- **An asymptotic expansion, sampled on a geometric sequence.** Let $A_0, A_1, \dots$ be real
numbers, let $\delta, h, C \in \mathbb{R}$, let $\alpha_0, \alpha_1, \dots$ be real coefficients
and let $k \in \mathbb{N}$. The sequence $A$ has the **expansion** $(\alpha, k, C)$ in the
parameter $\delta^m h$ if for every $m$,
$$\Bigl| A_m - \sum_{i=0}^{k} \alpha_i (\delta^m h)^i \Bigr| \le C (\delta^m h)^{k+1}.$$
This is (9.33) of [quarteroni2000numerical], with $A_m = \mathcal{A}(\delta^m h)$. -/
def HasExpansion (A : ℕ → ℝ) (δ h : ℝ) (α : ℕ → ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ∀ m, |A m - ∑ i ∈ Finset.range (k + 1), α i * (δ ^ m * h) ^ i| ≤ C * (δ ^ m * h) ^ (k + 1)

/-- **One extrapolation step of order $p$:**
$$B_m = \frac{A_{m+1} - \delta^p A_m}{1 - \delta^p}.$$
This is $\mathcal{B}(h) = (\mathcal{A}(\delta h) - \delta^p \mathcal{A}(h))/(1 - \delta^p)$ of
§9.6 of [quarteroni2000numerical], at the parameter $\delta^m h$. -/
noncomputable def step (A : ℕ → ℝ) (δ : ℝ) (p : ℕ) (m : ℕ) : ℝ :=
  (A (m + 1) - δ ^ p * A m) / (1 - δ ^ p)

/-- **The extrapolation table** (9.34) of [quarteroni2000numerical]: $A_{m,0} = A_m$ and
$$A_{m,q+1} = \frac{A_{m,q} - \delta^{q+1} A_{m-1,q}}{1 - \delta^{q+1}}.$$

The entries with $m < q$ have no meaning, because $m - 1$ is truncated at $0$ in `ℕ`. -/
noncomputable def table (A : ℕ → ℝ) (δ : ℝ) : ℕ → ℕ → ℝ
  | m, 0 => A m
  | m, q + 1 => (table A δ m q - δ ^ (q + 1) * table A δ (m - 1) q) / (1 - δ ^ (q + 1))

/-- The column $0$ of the extrapolation table is the sampled sequence: $A_{m,0} = A_m$. -/
@[simp]
theorem table_zero (A : ℕ → ℝ) (δ : ℝ) (m : ℕ) : table A δ m 0 = A m := rfl

/-- **The next column is one step applied to the previous column.** The entry $A_{m+1,q+1}$ is the
extrapolation step of order $q + 1$, at index $m$, applied to the column $m \mapsto A_{m,q}$. -/
theorem table_succ (A : ℕ → ℝ) (δ : ℝ) (m q : ℕ) :
    table A δ (m + 1) (q + 1) = step (fun m => table A δ m q) δ (q + 1) m := by
  simp [table, step]

/-- **One step removes the term in $h^p$ and keeps the expansion.** Let $0 < \delta < 1$, $h > 0$
and $p > 0$, and let $A$ have the expansion $(\alpha, k, C)$ in the parameter $\delta^m h$. Then
the sequence of one extrapolation step of order $p$ has the expansion with the coefficients
$$\tilde\alpha_i = \alpha_i \frac{\delta^i - \delta^p}{1 - \delta^p},$$
the same order $k$ and the constant $C (\delta^{k+1} + \delta^p)/(1 - \delta^p)$. In particular
$\tilde\alpha_0 = \alpha_0$ and $\tilde\alpha_p = 0$. This is the display after (9.33) in §9.6
of [quarteroni2000numerical].

In applications $p \le k$, but the result does not need it. -/
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

/-- **The $q$-th column has an expansion with the same $\alpha_0$ and with
$\alpha_1, \dots, \alpha_q$ zero.** Let $0 < \delta < 1$, $h > 0$ and $q \le k$, and let $A$
have the expansion $(\alpha, k, C)$ in the parameter $\delta^m h$. Then there are coefficients
$\alpha'$ and a constant $C'$ with $\alpha'_0 = \alpha_0$ and $\alpha'_i = 0$ for
$1 \le i \le q$, such that the sequence $m \mapsto A_{m+q,q}$ has the expansion
$(\alpha', k, C')$ in the parameter $\delta^m h$.

The proof is an induction on $q$ with `Richardson.table_succ` and
`Richardson.hasExpansion_step`. -/
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

/-- For $0 \le u \le 1 + h$, $h > 0$ and $q + 1 \le j \le k + 1$, we have
$u^j \le (1 + h)^{k+1} u^{q+1}$. -/
private theorem pow_le_of_le {u h : ℝ} (hu : 0 ≤ u) (huh : u ≤ 1 + h) (hh : 0 < h) {q j k : ℕ}
    (hqj : q + 1 ≤ j) (hjk : j ≤ k + 1) : u ^ j ≤ (1 + h) ^ (k + 1) * u ^ (q + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = q + 1 + d := ⟨j - (q + 1), by omega⟩
  rw [pow_add, mul_comm]
  gcongr
  calc u ^ d ≤ (1 + h) ^ d := pow_le_pow_left₀ hu huh _
    _ ≤ (1 + h) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (by omega)

/-- Let $0 < \delta \le 1$, $h > 0$ and $q \le k$, and let $B$ have the expansion $(\alpha, k, C)$
in the parameter $\delta^m h$, with $\alpha_i = 0$ for $1 \le i \le q$. Then for every $m$,
$$|B_m - \alpha_0| \le \Bigl( \sum_{i=0}^{k} |\alpha_i| + |C| \Bigr) (1 + h)^{k+1} (\delta^m
  h)^{q+1}.$$
-/
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

/-- **Property 9.2** of [quarteroni2000numerical], (9.35). Let $0 < \delta < 1$, $h > 0$ and
$q \le k$, and let $A$ have the expansion $(\alpha, k, C)$ in the parameter $\delta^m h$. Then
there is a constant $C'$, independent of $m$, with
$$|A_{m,q} - \alpha_0| \le C' (\delta^m h)^{q+1} \qquad \text{for all } m \ge q.$$

The source writes (9.35) for $A_{m,n}$ with $m = 0, \dots, n$, which (9.34) does not define. The
statement here is the reading $A_{m,q} = \alpha_0 + O((\delta^m h)^{q+1})$ for $q \le m$. -/
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

/-- **The a posteriori error estimate** behind (9.40) of [quarteroni2000numerical]. Let
$0 < \delta < 1$ and $p > 0$, and let $A$ satisfy $|A_m - \alpha_0 - c (\delta^m h)^p| \le C
(\delta^m h)^q$ for all $m$. Then for every $m$,
$$\Bigl| \alpha_0 - A_{m+1} - \frac{\delta^p}{1 - \delta^p} (A_{m+1} - A_m) \Bigr| \le C
  \frac{\delta^q + \delta^p}{1 - \delta^p} (\delta^m h)^q.$$

In applications $p < q$. With $\delta = 1/2$ the estimate is $\alpha_0 - A(2m) \approx (A(2m) -
A(m))/(2^p - 1)$, and the neglected term is of the next order. -/
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

/-- **The Romberg table** of $f$ on $[a, b]$: Richardson extrapolation with $\delta = 1/4$ of the
composite trapezoidal sums $T_{2^m}$ with $2^m$ panels of length $(b - a)/2^m$. This is
$\mathcal{A}(\eta) = T(\sqrt{\eta})$ sampled at $\eta = (b - a)^2/4^m$, as in §9.6.1 of
[quarteroni2000numerical]. -/
noncomputable def table (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℕ → ℝ :=
  Richardson.table (fun m => trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m)) (1 / 4)

/-- The column $0$ of the Romberg table is the composite trapezoidal rule: $A_{m,0} = T_{2^m}$, with
$2^m$ panels of length $(b - a)/2^m$. -/
@[simp]
theorem table_zero (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    table f a b m 0 = trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m) := rfl

/-- **The Romberg recursion**, the display after (9.37) of [quarteroni2000numerical]: for all $m$
and $q$,
$$A_{m,q+1} = \frac{4^{q+1} A_{m,q} - A_{m-1,q}}{4^{q+1} - 1}.$$
-/
theorem table_succ (f : ℝ → ℝ) (a b : ℝ) (m q : ℕ) :
    table f a b m (q + 1)
      = (4 ^ (q + 1) * table f a b m q - table f a b (m - 1) q) / (4 ^ (q + 1) - 1) := by
  have h4 : (4 : ℝ) ^ (q + 1) ≠ 0 := by positivity
  have h4' : (4 : ℝ) ^ (q + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < 4 ^ (q + 1) := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero q)
    linarith
  simp only [table, Richardson.table, one_div_pow]
  field_simp

/-- **The first extrapolated column is the composite Simpson rule.** For every $m$,
$A_{m+1,1} = S_{2^m}$, the composite Simpson sum with $2^m$ panels of length $(b - a)/2^m$. This
is stated in §9.6.1 of [quarteroni2000numerical].

The identity is $(4 T_{2N} - T_N)/3 = S_N$, which follows by writing the trapezoidal sum with
$2N$ panels as a sum over even and odd indices. -/
theorem table_one_eq_simpsonSum (f : ℝ → ℝ) (a b : ℝ) (m : ℕ) :
    table f a b (m + 1) 1 = simpsonSum f a ((b - a) / 2 ^ m) (2 ^ m) := by
  rw [table_succ, Nat.add_sub_cancel, table_zero, table_zero, zero_add, pow_one,
    simpsonSum_eq_trapezoidSum]
  have h2 : (b - a) / (2 : ℝ) ^ (m + 1) = (b - a) / 2 ^ m / 2 := by rw [pow_succ]; ring
  rw [h2, show (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m by ring]
  norm_num

/-- The coefficients of the Euler–Maclaurin expansion of the trapezoidal rule, as an expansion in
$h^2$: $\alpha_0 = \int_a^b f$ and, for $i \ge 1$,
$$\alpha_i = \frac{B_{2i}}{(2i)!} \bigl(f^{(2i-1)}(b) - f^{(2i-1)}(a)\bigr),$$
where $B_{2i}$ is a Bernoulli number. -/
noncomputable def eulerMaclaurinCoeff (f : ℝ → ℝ) (a b : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then ∫ t in a..b, f t
  else ((bernoulli (2 * i) : ℚ) : ℝ) / (2 * i)! * (iteratedDeriv (2 * i - 1) f b
    - iteratedDeriv (2 * i - 1) f a)

/-- **The Euler–Maclaurin formula as a Richardson expansion.** Let $a < b$, let $U$ be an open set
that contains $[a, b]$, and let $f$ be of class $C^{2k+2}$ on $U$. Then the composite
trapezoidal sums $T_{2^m}$ with $2^m$ panels have the expansion $(\alpha, k, C)$ in the
parameter $(1/4)^m (b - a)^2 = h_m^2$, for some constant $C$, where $\alpha$ is
`Romberg.eulerMaclaurinCoeff f a b`. This is in §9.6.1 of [quarteroni2000numerical].

The proof takes $C = |B_{2k+2}| (b - a) M / (2k + 2)!$, where $M$ bounds $|f^{(2k+2)}|$ on
$[a, b]$. -/
theorem hasExpansion_trapezoidSum {a b : ℝ} (hab : a < b) {k : ℕ} {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hUab : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ ((2 * k + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ C : ℝ, Richardson.HasExpansion (fun m => trapezoidSum f a ((b - a) / 2 ^ m) (2 ^ m)) (1 / 4)
      ((b - a) ^ 2) (eulerMaclaurinCoeff f a b) k C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedDeriv_of_isOpen hU le_rfl).mono hUab)
  refine ⟨|((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (2 * k + 2)! * (b - a) * M, fun m => ?_⟩
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

/-- **Convergence of Romberg integration**, §9.6.1 of [quarteroni2000numerical]. Let $a < b$, let
$U$ be an open set that contains $[a, b]$, and let $f$ be of class $C^{2q+2}$ on $U$. Then there
is a constant $C$ with
$$\Bigl| A_{m,q} - \int_a^b f \Bigr| \le C \Bigl(\frac{b - a}{2^m}\Bigr)^{2(q+1)} \qquad
  \text{for all } m \ge q.$$
-/
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
