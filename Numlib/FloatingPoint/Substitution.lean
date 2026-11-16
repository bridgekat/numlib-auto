/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Substitution
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.Program

/-!
# Rounding errors of forward and backward substitution

This module gives the backward error analysis of forward and backward substitution for a triangular
system $Tx = b$ of order $n$, over an ordered field $K$, in the relational rounding model of
`Numlib.FloatingPoint.Model`. The model has a unit roundoff $u$, and every rounded value $\hat y$ of
an exact value $y$ satisfies $|\hat y - y| \le u |y|$. The constants are $\gamma_k = ku / (1 - ku)$.
The main result is Theorem 8.5 of [higham2002accuracy], which is (3.24) of
[quarteroni2000numerical], §3.2.2: the computed solution $\hat x$ solves exactly a perturbed system
$$(T + \Delta T) \hat x = b, \qquad |\Delta T| \le \gamma_n |T| \text{ entrywise}.$$

A substitution is described by what is rounded, for an explicit order of the operations. In the
running-difference form (Program 2 of [quarteroni2000numerical], and the evaluation of Lemma 8.4 of
[higham2002accuracy]), row $i$ rounds the products $t_{ij} \hat x_j$ for $j < i$, subtracts them one
after the other from $b_i$ with one rounding per subtraction, and divides the result by $t_{ii}$
with one more rounding. The order of the subtractions is existentially quantified, so every theorem
holds for every order that an implementation may use. In the inner-product form (Algorithms 3.1.1
and 3.1.2 of [golub2013matrix], Program 1 of [quarteroni2000numerical]), row $i$ accumulates $s =
\mathrm{fl}(s + \mathrm{fl}(t_{ij} \hat x_j))$ from $s = 0$, then computes $\mathrm{fl}(b_i - s)$
and divides; the first row only divides. Both forms have the backward error bound $\gamma_n$.

## Main definitions

* `FloatingPoint.RoundsForwardSubst`: forward substitution in the running-difference form, as a
  relation between $T$, $b$ and the computed solution $\hat x$.
* `FloatingPoint.RoundsBackSubst`: backward substitution in the running-difference form.
* `FloatingPoint.RoundsForwardSubstDot`, `FloatingPoint.RoundsBackSubstDot`: forward and backward
  substitution in the inner-product form.
* `FloatingPoint.RoundsUnitForwardSubst`: forward substitution for a unit lower triangular matrix,
  without the division by the diagonal.

## Main results

* `FloatingPoint.exists_rounds_sub_dot_div_eq`: Lemma 8.4 of [higham2002accuracy]. If $\hat y$ is
  computed from $(c - \sum_{j=1}^{k} a_j b_j) / d$ as a running difference and a division, then $d
  \hat y (1 + \theta_0) = c - \sum_j a_j b_j (1 + \theta_j)$ with all $|\theta| \le \gamma_{k+1}$.
* `FloatingPoint.exists_roundsForwardSubst_eq`, `FloatingPoint.exists_roundsBackSubst_eq`: Theorem
  8.5 of [higham2002accuracy]. The computed solution satisfies $(T + \Delta T) \hat x = b$ with
  $|\Delta T| \le \gamma_n |T|$.
* `FloatingPoint.exists_roundsForwardSubstDot_eq`, `FloatingPoint.exists_roundsBackSubstDot_eq`: the
  same bound for the inner-product form, a rigorous form of (3.1.1) and (3.1.2) of
  [golub2013matrix].
* `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_abs_le_diag`: Theorem 8.7 of [higham2002accuracy].
  If $|u_{ii}| \ge |u_{ij}|$ for $j > i$, then $|x_i - \hat x_i| \le 2^{n-i+1} \gamma_n \max_{j \ge
  i} |\hat x_j|$.
* `FloatingPoint.abs_sub_le_of_roundsBackSubst_of_isDiagDominant`: for a row diagonally dominant
  upper triangular $U$, $|x_i - \hat x_i| \le (2n - 1) \gamma_n \|\hat x\|_\infty$.
* `FloatingPoint.roundsForwardSubst_exact_iff`, `FloatingPoint.roundsBackSubst_exact_iff`,
  `FloatingPoint.roundsForwardSubstDot_exact_iff`, `FloatingPoint.roundsBackSubstDot_exact_iff`: in
  the exact model, each relation holds exactly for the result of `Matrix.forwardSubst` or
  `Matrix.backSubst`, with no hypothesis on the matrix.
* `FloatingPoint.roundsForwardSubst_of_mem_run_colSubst`: every run of the column-oriented loop of
  Algorithm 3.1.3 of [golub2013matrix] satisfies `FloatingPoint.RoundsForwardSubst`.
* `FloatingPoint.roundsUnitForwardSubst_of_mem_run_unitColSubst`: every run of the same loop without
  the division satisfies `FloatingPoint.RoundsUnitForwardSubst`.

## Proof outline

The scalar core is Lemma 8.4 of [higham2002accuracy]. A running sum of $k$ terms with one rounding
per addition satisfies $t (1 + \theta_0) = c + \sum_j f_j (1 + \theta_j)$ with all
$|\theta| \le \gamma_k$. The final division adds one more rounding to each factor, through
$(1 + \theta_k)(1 + \delta) = 1 + \theta_{k+1}$ and $(1 + \theta_k) / (1 + \delta) = 1 +
\theta_{k+1}$ (`FloatingPoint.abs_one_add_div_one_add_sub_one_le_gamma`). The second identity is the
reason why a division counts as one rounding, not two. Row $i$ has at most $n - 1$ terms, so its
factors are bounded by $\gamma_n$. One lemma, `FloatingPoint.exists_add_mulVec_eq_of_forall_row_eq`,
assembles the rows into the perturbed system. Backward substitution is forward substitution for the
reversed order of the indices (`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`), as in
`Numlib.Direct.Substitution`. The forward error bounds follow from
$x - \hat x = U^{-1} \Delta U \hat x$ and the bounds on $|U^{-1}| |U|$ of Lemmas 8.6 and 8.8 of
[higham2002accuracy] (`Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`,
`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`).

## Implementation notes

* All results are entrywise and hold over any ordered field $K$. The index type of the matrix is any
  finite linear order; the source's index $i$ corresponds to the position of $i$ in this order.
* The entry relation of every row is the running difference `FloatingPoint.RoundsRunningDiff` of
  `Numlib.FloatingPoint.InnerProduct`, whose program is `FloatingPoint.runningDiff`. The number of
  its terms is bounded once, by `FloatingPoint.length_add_one_le_card_of_forall_mem_iff`.
* The diagonal entries must be nonzero, because the model divides by zero with the value
  $t / 0 = 0$.
* The Doolittle recurrence `FloatingPoint.RoundsLU` of `Numlib.FloatingPoint.LU` uses the same
  running differences, and therefore it has the same constant $\gamma_n$.
* The inner-product form rounds $0 + p$ and $b_i - s$, which the relational model does not know to
  be exact. The bound is still $\gamma_n$: these roundings put the order $2 \le n$ on the diagonal
  factor (`FloatingPoint.exists_rounds_sub_dotFrom_div_eq`) and the order $\#\{j \le i\} \le n$ on
  the factor of each term. The first row must only divide: if it also rounded $b_1 - 0$, its
  diagonal factor would have the order $2$, and the bound $\gamma_n$ would fail for $n = 1$.
* At `FloatingPoint.RoundingModel.exact` the relations give the exact specification of a
  substitution program from its rounding analysis.
* The normwise bound (3.25) of [quarteroni2000numerical] needs a norm. It is a surface statement
  over $\mathbb{R}$, through `relative_error_le_condNumber`.
-/

open Finset

open scoped Matrix

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Running differences: the scalar core -/

variable {ι : Type*} [DecidableEq ι]

/-- Let $c \in K$, let $f_j \in K$ for $j$ in a list $o$ of $k$ distinct indices, and let the unit
roundoff satisfy $u < 1$ and $ku < 1$. If $t$ is computed from $c$ by adding the terms $f_j$,
$j \in o$, in the order of $o$ with one rounding per addition, then there are $\theta_0$ and
$\theta_j$, $j \in o$, with $|\theta_0| \le \gamma_k$ and $|\theta_j| \le \gamma_k$, such that
$$t (1 + \theta_0) = c + \sum_{j \in o} f_j (1 + \theta_j).$$

This is the computation inside the proof of Lemma 8.4 of [higham2002accuracy]. The term $c$ is
not perturbed: each rounding is charged to $t$ and to the terms added after it. The running sum
is `FloatingPoint.RoundsSumFrom` of the list `o.map f`. -/
theorem exists_roundsSumFrom_map_eq {m : RoundingModel K} (hu : m.u < 1) {c t : K} {f : ι → K}
    {o : List ι} (hnd : o.Nodup) (h : RoundsSumFrom m c (o.map f) t)
    (hlu : ((o.length : ℕ) : K) * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u o.length ∧ (∀ j ∈ o, |θ j| ≤ gamma m.u o.length) ∧
      t * (1 + θ₀) = c + ∑ j ∈ o.toFinset, f j * (1 + θ j) := by
  classical
  induction o generalizing c t with
  | nil =>
    simp only [List.map_nil] at h
    cases h
    exact ⟨0, fun _ => 0, by simp, by simp, by simp⟩
  | cons j o ih =>
    simp only [List.map_cons] at h
    rcases h with _ | ⟨ht', hr⟩
    rename_i t'
    rw [List.length_cons] at hlu
    have hcast : ((o.length + 1 : ℕ) : K) * m.u = (o.length : K) * m.u + m.u := by
      push_cast; ring
    have hl : (o.length : K) * m.u < 1 := by
      rw [hcast] at hlu
      linarith [m.u_nonneg]
    obtain ⟨θ₀', θ', hθ₀', hθ', heq⟩ := ih (List.nodup_cons.1 hnd).2 hr hl
    obtain ⟨δ, hδ, rfl⟩ := ht'.exists_delta
    have hd : (1 : K) + δ ≠ 0 := by
      have := neg_le_of_abs_le hδ
      linarith
    have hj : j ∉ o.toFinset := fun hj => (List.nodup_cons.1 hnd).1 (List.mem_toFinset.1 hj)
    refine ⟨(1 + θ₀') / (1 + δ) - 1,
      fun i => if i = j then 0 else (1 + θ' i) / (1 + δ) - 1, ?_, ?_, ?_⟩
    · exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu hθ₀' hδ
    · intro i hi
      rw [List.mem_cons] at hi
      dsimp only
      by_cases hij : i = j
      · simp [hij, gamma_nonneg m.u_nonneg hlu]
      · rw [ite_eq_right hij]
        exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu (hθ' i (hi.resolve_left hij))
          hδ
    · rw [List.toFinset_cons, Finset.sum_insert hj]
      dsimp only
      rw [ite_eq_left rfl, add_zero, mul_one]
      have hsum : ∑ i ∈ o.toFinset, f i * (1 + if i = j then 0 else (1 + θ' i) / (1 + δ) - 1) =
          (∑ i ∈ o.toFinset, f i * (1 + θ' i)) / (1 + δ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := fun e => hj (e ▸ hi)
        rw [ite_eq_right hij]
        field_simp
        ring
      have h1 : t * (1 + ((1 + θ₀') / (1 + δ) - 1)) = t * (1 + θ₀') / (1 + δ) := by
        field_simp
        ring
      rw [hsum, h1, heq]
      field_simp
      ring

/-- Let $a_j, b_j \in K$ for $j$ in a list $o$ of $k$ distinct indices, let $c, d \in K$ with
$d \neq 0$, and let the unit roundoff satisfy $u < 1$ and $(k + 1) u < 1$. Suppose that $t$ is
computed from $c - \sum_{j \in o} a_j b_j$ as a running difference in the order $o$, and that
$\hat y$ is an admissible rounding of $t / d$. Then there are $\theta_0$ and $\theta_j$,
$j \in o$, with $|\theta_0| \le \gamma_{k+1}$ and $|\theta_j| \le \gamma_{k+1}$, such that
$$d \hat y (1 + \theta_0) = c - \sum_{j \in o} a_j b_j (1 + \theta_j).$$
This is Lemma 8.4 of [higham2002accuracy], and it holds for every order $o$.

The running difference is `FloatingPoint.RoundsRunningDiff`. The divisor must be nonzero,
because the model divides by zero with the value $t / 0 = 0$. -/
theorem exists_rounds_sub_dot_div_eq {m : RoundingModel K} (hu : m.u < 1) {a b : ι → K}
    {o : List ι} (hnd : o.Nodup) {c d t y : K} (hd : d ≠ 0) (ht : RoundsRunningDiff m o a b c t)
    (hy : m.Rounds (t / d) y) (hlu : ((o.length + 1 : ℕ) : K) * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u (o.length + 1) ∧
      (∀ j ∈ o, |θ j| ≤ gamma m.u (o.length + 1)) ∧
      d * y * (1 + θ₀) = c - ∑ j ∈ o.toFinset, a j * b j * (1 + θ j) := by
  classical
  obtain ⟨p, hp, ht⟩ := ht
  have hcast : ((o.length + 1 : ℕ) : K) * m.u = (o.length : K) * m.u + m.u := by push_cast; ring
  have hl : (o.length : K) * m.u < 1 := by
    rw [hcast] at hlu
    linarith [m.u_nonneg]
  obtain ⟨θ₀', θ', hθ₀', hθ', heq⟩ := exists_roundsSumFrom_map_eq hu hnd ht hl
  obtain ⟨δ, hδ, rfl⟩ := hy.exists_delta
  -- the rounded products, as relative perturbations
  have hprod : ∀ j ∈ o, ∃ ε : K, |ε| ≤ m.u ∧ p j = a j * b j * (1 + ε) := fun j hj =>
    (hp j hj).exists_delta
  choose! ε hε hpε using hprod
  have hd1 : (1 : K) + δ ≠ 0 := by
    have := neg_le_of_abs_le hδ
    linarith
  refine ⟨(1 + θ₀') / (1 + δ) - 1, fun j => (1 + θ' j) * (1 + ε j) - 1, ?_, ?_, ?_⟩
  · exact abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu hθ₀' hδ
  · intro j hj
    exact abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu (hθ' j hj) (hε j hj)
  · have hsum : ∑ j ∈ o.toFinset, a j * b j * (1 + ((1 + θ' j) * (1 + ε j) - 1)) =
        -∑ j ∈ o.toFinset, (-p j) * (1 + θ' j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpε j (List.mem_toFinset.1 hj)]
      ring
    have heq' : t * (1 + θ₀') = c + ∑ j ∈ o.toFinset, -p j * (1 + θ' j) := heq
    dsimp only
    rw [hsum, sub_neg_eq_add, ← heq']
    field_simp
    ring

/-- Let $a_j, b_j \in K$ for $j$ in a list $o$ of $k$ distinct indices, let $c, d \in K$ with
$d \neq 0$, and let the unit roundoff satisfy $u < 1$, $(k + 1) u < 1$ and $2u < 1$. Suppose
that $p_j$ is an admissible rounding of $a_j b_j$ for each $j \in o$, that $s$ is computed from
$0$ by adding the $p_j$ in the order $o$ with one rounding per addition (the first addition
$\mathrm{fl}(0 + p)$ included), that $t$ is an admissible rounding of $c - s$, and that $\hat y$
is an admissible rounding of $t / d$. Then there are $\theta_0$ and $\theta_j$, $j \in o$, with
$|\theta_0| \le \gamma_2$ and $|\theta_j| \le \gamma_{k+1}$, such that
$$d \hat y (1 + \theta_0) = c - \sum_{j \in o} a_j b_j (1 + \theta_j).$$

This is the analogue of Lemma 8.4 of [higham2002accuracy] for the order "inner product, then
subtraction, then division" of Algorithm 3.1.1 of [golub2013matrix]. The divisor must be
nonzero, because the model divides by zero with the value $t / 0 = 0$. -/
theorem exists_rounds_sub_dotFrom_div_eq {m : RoundingModel K} (hu : m.u < 1) {a b p : ι → K}
    {o : List ι} (hnd : o.Nodup) (hp : ∀ j ∈ o, m.Rounds (a j * b j) (p j)) {c d s t y : K}
    (hd : d ≠ 0) (hs : RoundsSumFrom m 0 (o.map p) s) (ht : m.Rounds (c - s) t)
    (hy : m.Rounds (t / d) y) (hlu : ((o.length + 1 : ℕ) : K) * m.u < 1) (h2 : 2 * m.u < 1) :
    ∃ (θ₀ : K) (θ : ι → K), |θ₀| ≤ gamma m.u 2 ∧
      (∀ j ∈ o, |θ j| ≤ gamma m.u (o.length + 1)) ∧
      d * y * (1 + θ₀) = c - ∑ j ∈ o.toFinset, a j * b j * (1 + θ j) := by
  classical
  have hl : (o.length : K) * m.u < 1 := by
    have : (o.length : K) * m.u ≤ ((o.length + 1 : ℕ) : K) * m.u := by
      push_cast; nlinarith [m.u_nonneg]
    linarith
  obtain ⟨φ, θ', -, hθ', hseq⟩ := exists_roundsSumFrom_map_eq_add_sum hnd hs hl
  choose! ε hε hpε using fun j hj => (hp j hj).exists_delta
  obtain ⟨δ₁, hδ₁, rfl⟩ := ht.exists_delta
  obtain ⟨δ₂, hδ₂, rfl⟩ := hy.exists_delta
  have hd₁ : (1 : K) + δ₁ ≠ 0 := by linarith [neg_le_of_abs_le hδ₁]
  have hd₂ : (1 : K) + δ₂ ≠ 0 := by linarith [neg_le_of_abs_le hδ₂]
  refine ⟨(1 + 0) / (1 + δ₁) / (1 + δ₂) - 1, fun j => (1 + θ' j) * (1 + ε j) - 1, ?_,
    fun j hj => abs_one_add_mul_one_add_sub_one_le_gamma m.u_nonneg hu hlu (hθ' j hj) (hε j hj),
    ?_⟩
  · have hA := abs_one_add_div_one_add_sub_one_le_gamma (k := 0) (θ := 0) m.u_nonneg
      (by simpa using hu) (by simp) hδ₁
    have hB := abs_one_add_div_one_add_sub_one_le_gamma (k := 1) m.u_nonneg
      (by norm_num; exact h2) hA hδ₂
    rwa [add_sub_cancel] at hB
  · have hsum : s = ∑ j ∈ o.toFinset, a j * b j * (1 + ((1 + θ' j) * (1 + ε j) - 1)) := by
      rw [hseq, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hpε j (List.mem_toFinset.1 hj)]
      ring
    rw [← hsum]
    field_simp
    ring

/-! ### Forward substitution -/

section Forward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Forward substitution in floating-point arithmetic.** Let $T \in K^{n \times n}$ and
$b, \hat x \in K^n$. The relation `FloatingPoint.RoundsForwardSubst m T b xhat` holds if, for
every index $i$, there are a list $o$ of distinct indices whose members are exactly the indices
$j < i$, and a value $t$, such that $t$ is computed from $b_i - \sum_{j < i} t_{ij} \hat x_j$ as
a running difference in the order $o$ and $\hat x_i$ is an admissible rounding of $t / t_{ii}$.

This is the recurrence $x_i = (b_i - \sum_{j < i} t_{ij} x_j) / t_{ii}$ of (3.22) of
[quarteroni2000numerical], evaluated as in Lemma 8.4 of [higham2002accuracy]: the products
$t_{ij} \hat x_j$ are rounded and subtracted one after the other from $b_i$, with one rounding
per subtraction. The running difference is `FloatingPoint.RoundsRunningDiff`. The order $o$ is
existentially quantified, so a theorem about this relation holds for every order that an
implementation may use. -/
def RoundsForwardSubst (m : RoundingModel K) (T : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
    RoundsRunningDiff m o (T i) xhat (b i) t ∧ m.Rounds (t / T i i) (xhat i)

/-- If a list $o$ has as members exactly the indices $j < i$, then the finite set of its members is
the set of the indices below $i$. -/
theorem toFinset_eq_filter_lt_of_forall_mem_iff {o : List n} {i : n} (ho : ∀ j, j ∈ o ↔ j < i) :
    o.toFinset = univ.filter (· < i) := by
  ext j
  simp [ho]

/-- If a list $o$ of distinct indices has as members exactly the indices $j < i$ of a finite linear
order with $n$ elements, then $o$ has at most $n - 1$ entries.

So a row of a substitution or of a factorization, which has the terms and one more operation,
carries at most $n$ roundings. -/
theorem length_add_one_le_card_of_forall_mem_iff {o : List n} {i : n} (hnd : o.Nodup)
    (ho : ∀ j, j ∈ o ↔ j < i) : o.length + 1 ≤ Fintype.card n := by
  have hlen : o.length + 1 = #{j | j ≤ i} := by
    rw [← List.toFinset_card_of_nodup hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho,
      Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Matrix.sum_filter_le_eq_add]
  exact hlen ▸ Finset.card_le_univ _

/-- **One row of forward substitution.** Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where
$n$ is the order of the system, let $T \in K^{n \times n}$, and let $\hat x$ be computed by
forward substitution from $T$ and $b$ (`FloatingPoint.RoundsForwardSubst`). If $t_{ii} \neq 0$,
then there are $\theta_0$ and $\theta_j$, $j < i$, with $|\theta_0| \le \gamma_n$ and
$|\theta_j| \le \gamma_n$, such that
$$t_{ii} \hat x_i (1 + \theta_0) = b_i - \sum_{j < i} t_{ij} \hat x_j (1 + \theta_j).$$

This is row $i$ of Theorem 8.5 of [higham2002accuracy]. It follows from Lemma 8.4
(`FloatingPoint.exists_rounds_sub_dot_div_eq`), with $\#\{j \le i\} \le n$ roundings. -/
theorem exists_roundsForwardSubst_row_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} {b xhat : n → K}
    (h : RoundsForwardSubst m T b xhat) (i : n) (hd : T i i ≠ 0) :
    ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ gamma m.u (Fintype.card n) ∧
      (∀ j, j < i → |θ j| ≤ gamma m.u (Fintype.card n)) ∧
      T i i * xhat i * (1 + θ₀) =
        b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j) := by
  obtain ⟨o, t, hnd, ho, ht, hx⟩ := h i
  have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
  have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
  have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
  obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dot_div_eq hu hnd hd ht hx hlu
  have hmono := gamma_mono m.u_nonneg hle hcard
  refine ⟨θ₀, θ, hθ₀.trans hmono, fun j hj => (hθ j ((ho j).2 hj)).trans hmono, ?_⟩
  rw [← hset]
  exact heq

/-- Let $T \in K^{n \times n}$ be lower triangular, let $\gamma \ge 0$, and let $b, \hat x \in K^n$.
Suppose that for every row $i$ there are $\theta_0$ and $\theta_j$, $j < i$, with
$|\theta_0| \le \gamma$ and $|\theta_j| \le \gamma$, such that
$$t_{ii} \hat x_i (1 + \theta_0) = b_i - \sum_{j < i} t_{ij} \hat x_j (1 + \theta_j).$$
Then there is a matrix $\Delta T$ with $|\Delta T_{ij}| \le \gamma |T_{ij}|$ for all $i, j$ and
$(T + \Delta T) \hat x = b$.

This is the step of the proof of Theorem 8.5 of [higham2002accuracy] that assembles the rows
into a perturbed system. All evaluation orders of this module share it. -/
theorem exists_add_mulVec_eq_of_forall_row_eq {γ : K} (hγ : 0 ≤ γ) {T : Matrix n n K}
    (hT : T.IsLowerTriangular) {b xhat : n → K}
    (h : ∀ i, ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ γ ∧ (∀ j, j < i → |θ j| ≤ γ) ∧
      T i i * xhat i * (1 + θ₀) = b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j)) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ γ * |T i j|) ∧ (T + ΔT) *ᵥ xhat = b := by
  choose θ₀ θ hθ₀ hθ heq using h
  refine ⟨Matrix.of fun i j => if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0,
    fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply]
    split_ifs with hji hji'
    · rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hθ i j hji) (abs_nonneg _)
    · subst hji'
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hθ₀ j) (abs_nonneg _)
    · rw [abs_zero]
      exact mul_nonneg hγ (abs_nonneg _)
  · have hT' : (T + Matrix.of fun i j =>
        if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0).IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      rw [Matrix.add_apply, hT hij, Matrix.of_apply, ite_eq_right hij'.not_gt,
        ite_eq_right hij'.ne', add_zero]
    ext i
    rw [Matrix.mulVec_apply_of_isLowerTriangular hT', Matrix.add_apply, Matrix.of_apply,
      ite_eq_right (lt_irrefl i), ite_eq_left rfl]
    have hrow : ∑ j ∈ univ.filter (· < i), (T + Matrix.of fun i j =>
        if j < i then T i j * θ i j else if j = i then T i i * θ₀ i else 0) i j * xhat j =
        ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ i j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Matrix.add_apply, Matrix.of_apply, ite_eq_left (mem_filter.1 hj).2]
      ring
    rw [hrow]
    linear_combination heq i

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$T \in K^{n \times n}$ be lower triangular with nonzero diagonal entries, and let $\hat x$ be
computed by forward substitution from $T$ and $b$ (`FloatingPoint.RoundsForwardSubst`), in any
order of the operations. Then there is a matrix $\Delta T$ such that
$$(T + \Delta T) \hat x = b, \qquad |\Delta T_{ij}| \le \gamma_n |T_{ij}| \text{ for all } i,
  j.$$
This is Theorem 8.5 of [higham2002accuracy] and (3.24) of [quarteroni2000numerical].

Row $i$ of the conclusion is Lemma 8.4 of [higham2002accuracy]
(`FloatingPoint.exists_roundsForwardSubst_row_eq`), and the perturbation of row $i$ lies in the
entries $j \le i$. The diagonal must be nonzero, because the model divides by zero with the
value $t / 0 = 0$. -/
theorem exists_roundsForwardSubst_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) {b xhat : n → K} (h : RoundsForwardSubst m T b xhat) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ gamma m.u (Fintype.card n) * |T i j|) ∧
      (T + ΔT) *ᵥ xhat = b :=
  exists_add_mulVec_eq_of_forall_row_eq (gamma_nonneg m.u_nonneg hcard) hT fun i =>
    exists_roundsForwardSubst_row_eq hu hcard h i (hd i)

/-! ### Forward substitution in the inner-product order -/

/-- **Forward substitution in the inner-product order.** Let $T \in K^{n \times n}$ and
$b, \hat x \in K^n$. The relation `FloatingPoint.RoundsForwardSubstDot m T b xhat` holds if, for
every index $i$, the following is true. If $i$ is the least index, then $\hat x_i$ is an
admissible rounding of $b_i / t_{ii}$. Otherwise there are a list $o$ of distinct indices whose
members are exactly the indices $j < i$, values $p_j$, $s$ and $t$, such that $p_j$ is an
admissible rounding of $t_{ij} \hat x_j$ for each $j < i$, $s$ is computed from $0$ by adding
the $p_j$ in the order $o$ with one rounding per addition (the first addition
$\mathrm{fl}(0 + p)$ included), $t$ is an admissible rounding of $b_i - s$, and $\hat x_i$ is an
admissible rounding of $t / t_{ii}$.

This is Algorithm 3.1.1 of [golub2013matrix], the "inner product form" of §8.1 of
[higham2002accuracy]. As in `FloatingPoint.RoundsForwardSubst`, the order $o$ is existentially
quantified. -/
def RoundsForwardSubstDot (m : RoundingModel K) (T : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, (IsMin i → m.Rounds (b i / T i i) (xhat i)) ∧
    (¬ IsMin i → ∃ (o : List n) (p : n → K) (s t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
      (∀ j ∈ o, m.Rounds (T i j * xhat j) (p j)) ∧ RoundsSumFrom m 0 (o.map p) s ∧
      m.Rounds (b i - s) t ∧ m.Rounds (t / T i i) (xhat i))

/-- **One row of forward substitution in the inner-product order.** Let the unit roundoff satisfy
$u < 1$ and $nu < 1$, where $n$ is the order of the system, let $T \in K^{n \times n}$, and let
$\hat x$ be computed from $T$ and $b$ by `FloatingPoint.RoundsForwardSubstDot`. If
$t_{ii} \neq 0$, then there are $\theta_0$ and $\theta_j$, $j < i$, with
$|\theta_0| \le \gamma_n$ and $|\theta_j| \le \gamma_n$, such that
$$t_{ii} \hat x_i (1 + \theta_0) = b_i - \sum_{j < i} t_{ij} \hat x_j (1 + \theta_j).$$

The first row has one rounded division, so its diagonal factor has the order $1$. Every other
row has the order $2$ of the subtraction and the division on the diagonal factor, which needs
$n \ge 2$, and the order $\#\{j \le i\} \le n$ on the factor of each term
(`FloatingPoint.exists_rounds_sub_dotFrom_div_eq`). -/
theorem exists_roundsForwardSubstDot_row_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} {b xhat : n → K}
    (h : RoundsForwardSubstDot m T b xhat) (i : n) (hd : T i i ≠ 0) :
    ∃ (θ₀ : K) (θ : n → K), |θ₀| ≤ gamma m.u (Fintype.card n) ∧
      (∀ j, j < i → |θ j| ≤ gamma m.u (Fintype.card n)) ∧
      T i i * xhat i * (1 + θ₀) =
        b i - ∑ j ∈ univ.filter (· < i), T i j * xhat j * (1 + θ j) := by
  by_cases hi : IsMin i
  · obtain ⟨δ, hδ, hxδ⟩ := ((h i).1 hi).exists_delta
    have h1 : 1 ≤ Fintype.card n := Fintype.card_pos_iff.2 ⟨i⟩
    have hlu1 : ((0 + 1 : ℕ) : K) * m.u < 1 := by simpa using hu
    have hempty : univ.filter (· < i) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt
    have hd₁ : (1 : K) + δ ≠ 0 := by linarith [neg_le_of_abs_le hδ]
    refine ⟨(1 + 0) / (1 + δ) - 1, fun _ => 0,
      (abs_one_add_div_one_add_sub_one_le_gamma m.u_nonneg hlu1 (by simp) hδ).trans
        (gamma_mono m.u_nonneg h1 hcard), fun j hj => absurd hj hi.not_lt, ?_⟩
    rw [hempty, Finset.sum_empty, sub_zero, hxδ]
    field_simp
    ring
  · obtain ⟨o, p, s, t, hnd, ho, hp, hs, ht, hx⟩ := (h i).2 hi
    obtain ⟨j₀, hj₀⟩ := not_isMin_iff.1 hi
    have hset := toFinset_eq_filter_lt_of_forall_mem_iff ho
    have hle := length_add_one_le_card_of_forall_mem_iff hnd ho
    have hlu : ((o.length + 1 : ℕ) : K) * m.u < 1 :=
      (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) m.u_nonneg).trans_lt hcard
    have h2n : 2 ≤ Fintype.card n := Fintype.one_lt_card_iff.2 ⟨j₀, i, hj₀.ne⟩
    have h2 : 2 * m.u < 1 := by
      have : (2 : K) * m.u ≤ (Fintype.card n : K) * m.u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h2n) m.u_nonneg
      linarith
    obtain ⟨θ₀, θ, hθ₀, hθ, heq⟩ := exists_rounds_sub_dotFrom_div_eq hu hnd hp hd hs ht hx hlu h2
    refine ⟨θ₀, θ, hθ₀.trans (gamma_mono m.u_nonneg h2n hcard),
      fun j hj => (hθ j ((ho j).2 hj)).trans (gamma_mono m.u_nonneg hle hcard), ?_⟩
    rw [← hset]
    exact heq

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$T \in K^{n \times n}$ be lower triangular with nonzero diagonal entries, and let $\hat x$ be
computed from $T$ and $b$ by forward substitution in the inner-product order
(`FloatingPoint.RoundsForwardSubstDot`). Then there is a matrix $\Delta T$ such that
$$(T + \Delta T) \hat x = b, \qquad |\Delta T_{ij}| \le \gamma_n |T_{ij}| \text{ for all } i,
  j.$$
This is the rigorous form of (3.1.1) of [golub2013matrix] for Algorithm 3.1.1.

The constant is the same as in `FloatingPoint.exists_roundsForwardSubst_eq`. -/
theorem exists_roundsForwardSubstDot_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {T : Matrix n n K} (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) {b xhat : n → K} (h : RoundsForwardSubstDot m T b xhat) :
    ∃ ΔT : Matrix n n K, (∀ i j, |ΔT i j| ≤ gamma m.u (Fintype.card n) * |T i j|) ∧
      (T + ΔT) *ᵥ xhat = b :=
  exists_add_mulVec_eq_of_forall_row_eq (gamma_nonneg m.u_nonneg hcard) hT fun i =>
    exists_roundsForwardSubstDot_row_eq hu hcard h i (hd i)

end Forward

/-! ### Backward substitution -/

section Backward

variable {n : Type*} [Fintype n] [LinearOrder n]

/-- **Backward substitution in floating-point arithmetic.** Let $U \in K^{n \times n}$ and
$b, \hat x \in K^n$. The relation `FloatingPoint.RoundsBackSubst m U b xhat` holds if, for every
index $i$, there are a list $o$ of distinct indices whose members are exactly the indices
$j > i$, and a value $t$, such that $t$ is computed from $b_i - \sum_{j > i} u_{ij} \hat x_j$ as
a running difference in the order $o$ and $\hat x_i$ is an admissible rounding of $t / u_{ii}$.

This is the recurrence (3.23) of [quarteroni2000numerical], evaluated as in
`FloatingPoint.RoundsForwardSubst`. It is forward substitution for the reversed order of the
indices (`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`). -/
def RoundsBackSubst (m : RoundingModel K) (U : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, ∃ (o : List n) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ i < j) ∧
    RoundsRunningDiff m o (U i) xhat (b i) t ∧ m.Rounds (t / U i i) (xhat i)

omit [Fintype n] in
/-- Backward substitution is forward substitution for the reversed order:
`FloatingPoint.RoundsBackSubst m U b xhat` holds if and only if
`FloatingPoint.RoundsForwardSubst m U b xhat` holds for the order dual `nᵒᵈ` of the index type. -/
theorem roundsBackSubst_iff_roundsForwardSubst_toDual {m : RoundingModel K} {U : Matrix n n K}
    {b xhat : n → K} :
    RoundsBackSubst m U b xhat ↔ RoundsForwardSubst (n := nᵒᵈ) m U b xhat :=
  Iff.rfl

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$U \in K^{n \times n}$ be upper triangular with nonzero diagonal entries, and let $\hat x$ be
computed by backward substitution from $U$ and $b$ (`FloatingPoint.RoundsBackSubst`). Then there
is a matrix $\Delta U$ such that
$$(U + \Delta U) \hat x = b, \qquad |\Delta U_{ij}| \le \gamma_n |U_{ij}| \text{ for all } i,
  j.$$
This is Theorem 8.5 of [higham2002accuracy] for backward substitution, and (3.24) of
[quarteroni2000numerical].

The proof applies `FloatingPoint.exists_roundsForwardSubst_eq` to the reversed order of the
indices. -/
theorem exists_roundsBackSubst_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {b xhat : n → K} (h : RoundsBackSubst m U b xhat) :
    ∃ ΔU : Matrix n n K, (∀ i j, |ΔU i j| ≤ gamma m.u (Fintype.card n) * |U i j|) ∧
      (U + ΔU) *ᵥ xhat = b :=
  exists_roundsForwardSubst_eq (n := nᵒᵈ) hu hcard hU.isLowerTriangular_orderDual hd
    (roundsBackSubst_iff_roundsForwardSubst_toDual.1 h)

/-- **Backward substitution in the inner-product order.** Let $U \in K^{n \times n}$ and
$b, \hat x \in K^n$. The relation `FloatingPoint.RoundsBackSubstDot m U b xhat` is
`FloatingPoint.RoundsForwardSubstDot` with the products over the indices $j > i$: if $i$ is the
greatest index, then $\hat x_i$ is an admissible rounding of $b_i / u_{ii}$; otherwise the
rounded products $\mathrm{fl}(u_{ij} \hat x_j)$, $j > i$, are summed from $0$ in some order with
one rounding per addition, the sum $s$ is subtracted from $b_i$ with one rounding, and the
result is divided by $u_{ii}$ with one more rounding.

This is Algorithm 3.1.2 of [golub2013matrix]. It is `FloatingPoint.RoundsForwardSubstDot` for
the reversed order of the indices
(`FloatingPoint.roundsBackSubstDot_iff_roundsForwardSubstDot_toDual`). -/
def RoundsBackSubstDot (m : RoundingModel K) (U : Matrix n n K) (b xhat : n → K) : Prop :=
  ∀ i, (IsMax i → m.Rounds (b i / U i i) (xhat i)) ∧
    (¬ IsMax i → ∃ (o : List n) (p : n → K) (s t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ i < j) ∧
      (∀ j ∈ o, m.Rounds (U i j * xhat j) (p j)) ∧ RoundsSumFrom m 0 (o.map p) s ∧
      m.Rounds (b i - s) t ∧ m.Rounds (t / U i i) (xhat i))

omit [Fintype n] in
/-- Backward substitution in the inner-product order is forward substitution in the inner-product
order for the reversed order: `FloatingPoint.RoundsBackSubstDot m U b xhat` holds if and only if
`FloatingPoint.RoundsForwardSubstDot m U b xhat` holds for the order dual `nᵒᵈ` of the index
type. -/
theorem roundsBackSubstDot_iff_roundsForwardSubstDot_toDual {m : RoundingModel K}
    {U : Matrix n n K} {b xhat : n → K} :
    RoundsBackSubstDot m U b xhat ↔ RoundsForwardSubstDot (n := nᵒᵈ) m U b xhat :=
  Iff.rfl

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$U \in K^{n \times n}$ be upper triangular with nonzero diagonal entries, and let $\hat x$ be
computed from $U$ and $b$ by backward substitution in the inner-product order
(`FloatingPoint.RoundsBackSubstDot`). Then there is a matrix $\Delta U$ such that
$$(U + \Delta U) \hat x = b, \qquad |\Delta U_{ij}| \le \gamma_n |U_{ij}| \text{ for all } i,
  j.$$
This is the rigorous form of (3.1.2) of [golub2013matrix] for Algorithm 3.1.2.

The proof applies `FloatingPoint.exists_roundsForwardSubstDot_eq` to the reversed order of the
indices. -/
theorem exists_roundsBackSubstDot_eq {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {b xhat : n → K} (h : RoundsBackSubstDot m U b xhat) :
    ∃ ΔU : Matrix n n K, (∀ i j, |ΔU i j| ≤ gamma m.u (Fintype.card n) * |U i j|) ∧
      (U + ΔU) *ᵥ xhat = b :=
  exists_roundsForwardSubstDot_eq (n := nᵒᵈ) hu hcard hU.isLowerTriangular_orderDual hd
    (roundsBackSubstDot_iff_roundsForwardSubstDot_toDual.1 h)

/-- Let $U \in K^{n \times n}$ be invertible, let $\gamma \in K$, and let $x, \hat x, b \in K^n$ and
$\Delta U \in K^{n \times n}$ satisfy $Ux = b$, $(U + \Delta U) \hat x = b$ and
$|\Delta U_{ij}| \le \gamma |U_{ij}|$ for all $i, j$. Then, entrywise,
$$|x - \hat x| \le \gamma \, |U^{-1}| \, |U| \, |\hat x|.$$

This is the first line of the proof of Theorem 8.7 of [higham2002accuracy], and it follows from
$x - \hat x = U^{-1} \Delta U \hat x$. The matrices $|U^{-1}|$ and $|U|$ are `Matrix.abs`, and
the order on vectors is entrywise. -/
theorem abs_sub_le_of_mulVec_eq_of_abs_le {U ΔU : Matrix n n K} (hU : IsUnit U) {x xhat b : n → K}
    (hx : U *ᵥ x = b) (hxhat : (U + ΔU) *ᵥ xhat = b) {γ : K}
    (hΔ : ∀ i j, |ΔU i j| ≤ γ * |U i j|) :
    |x - xhat| ≤ γ • ((U⁻¹.abs * U.abs) *ᵥ |xhat|) := by
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hdiff : x - xhat = U⁻¹ *ᵥ (ΔU *ᵥ xhat) := by
    have h1 : U *ᵥ (x - xhat) = ΔU *ᵥ xhat := by
      rw [Matrix.add_mulVec] at hxhat
      rw [Matrix.mulVec_sub, hx, ← hxhat]
      abel
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hUd, Matrix.one_mulVec]
  have h2 : |ΔU *ᵥ xhat| ≤ (γ • U.abs) *ᵥ |xhat| := by
    refine (Matrix.abs_mulVec_le ΔU xhat).trans (Pi.le_def.2 fun i => ?_)
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.abs_apply, smul_eq_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)
  calc |x - xhat| = |U⁻¹ *ᵥ (ΔU *ᵥ xhat)| := by rw [hdiff]
    _ ≤ U⁻¹.abs *ᵥ |ΔU *ᵥ xhat| := Matrix.abs_mulVec_le _ _
    _ ≤ U⁻¹.abs *ᵥ ((γ • U.abs) *ᵥ |xhat|) :=
        (Matrix.entrywiseNonneg_abs U⁻¹).mulVec_mono h2
    _ = γ • ((U⁻¹.abs * U.abs) *ᵥ |xhat|) := by
        rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

/-- Let $U \in K^{n \times n}$ be upper triangular with nonzero diagonal entries, let
$\gamma \ge 0$, and let $x, \hat x, b \in K^n$ and $\Delta U \in K^{n \times n}$ satisfy
$Ux = b$, $(U + \Delta U) \hat x = b$ and $|\Delta U_{ij}| \le \gamma |U_{ij}|$ for all $i, j$.
If $c \in K$ bounds $|\hat x_j|$ for every $j \ge i$, then
$$|x_i - \hat x_i| \le \gamma c \sum_j (|U^{-1}| \, |U|)_{ij}.$$
This is row $i$ of `FloatingPoint.abs_sub_le_of_mulVec_eq_of_abs_le` for an upper triangular
$U$. -/
theorem abs_sub_apply_le_of_mulVec_eq_of_abs_le {U ΔU : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) {x xhat b : n → K} (hx : U *ᵥ x = b) (hxhat : (U + ΔU) *ᵥ xhat = b)
    {γ : K} (hγ : 0 ≤ γ) (hΔ : ∀ i j, |ΔU i j| ≤ γ * |U i j|) {i : n} {c : K}
    (hc : ∀ j, i ≤ j → |xhat j| ≤ c) :
    |x i - xhat i| ≤ γ * c * ∑ j, (U⁻¹.abs * U.abs) i j := by
  have hUu : IsUnit U := hU.isUnit_iff.2 hd
  have h := abs_sub_le_of_mulVec_eq_of_abs_le hUu hx hxhat hΔ i
  simp only [Pi.abs_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct] at h
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt i j with hij | hji
  · rw [mul_comm c]
    refine mul_le_mul_of_nonneg_left (hc j hij) ?_
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · rw [Matrix.abs_inv_mul_abs_apply_of_lt hU hji, zero_mul, mul_zero]

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$U \in K^{n \times n}$ be upper triangular with nonzero diagonal entries and with
$|u_{ij}| \le |u_{ii}|$ for all $j > i$. Let $Ux = b$, and let $\hat x$ be computed by backward
substitution from $U$ and $b$ (`FloatingPoint.RoundsBackSubst`). If $c \in K$ bounds
$|\hat x_j|$ for every $j \ge i$, then
$$|x_i - \hat x_i| \le 2^{\#\{j \,:\, j \ge i\}} \gamma_n c.$$
This is Theorem 8.7 of [higham2002accuracy], and the improved bound of §3.2.2 of
[quarteroni2000numerical].

The triangular factors of Gaussian elimination with partial pivoting satisfy the hypothesis on
$U$. The exponent $\#\{j : j \ge i\}$ is the source's $n - i + 1$, and $c$ stands for the
source's $\max_{j \ge i} |\hat x_j|$. The proof combines Theorem 8.5
(`FloatingPoint.exists_roundsBackSubst_eq`) with Lemma 8.6 of [higham2002accuracy]
(`Matrix.sum_abs_inv_mul_abs_apply_le_two_pow`). -/
theorem abs_sub_le_of_roundsBackSubst_of_abs_le_diag {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hrow : ∀ i j, i < j → |U i j| ≤ |U i i|) {x b xhat : n → K}
    (hx : U *ᵥ x = b) (h : RoundsBackSubst m U b xhat) {i : n} {c : K}
    (hc : ∀ j, i ≤ j → |xhat j| ≤ c) :
    |x i - xhat i| ≤ 2 ^ #{j | i ≤ j} * gamma m.u (Fintype.card n) * c := by
  obtain ⟨ΔU, hΔ, hxhat⟩ := exists_roundsBackSubst_eq hu hcard hU hd h
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc i le_rfl)
  refine (abs_sub_apply_le_of_mulVec_eq_of_abs_le hU hd hx hxhat hγ hΔ hc).trans ?_
  calc gamma m.u (Fintype.card n) * c * ∑ j, (U⁻¹.abs * U.abs) i j
      ≤ gamma m.u (Fintype.card n) * c * (2 ^ #{j | i ≤ j} - 1) :=
        mul_le_mul_of_nonneg_left (Matrix.sum_abs_inv_mul_abs_apply_le_two_pow hU hd hrow i)
          (mul_nonneg hγ hc0)
    _ ≤ gamma m.u (Fintype.card n) * c * 2 ^ #{j | i ≤ j} :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hγ hc0)
    _ = 2 ^ #{j | i ≤ j} * gamma m.u (Fintype.card n) * c := by ring

/-- Let the unit roundoff satisfy $u < 1$ and $nu < 1$, where $n$ is the order of the system. Let
$U \in K^{n \times n}$ be upper triangular with nonzero diagonal entries, and row diagonally
dominant: $\sum_{j \neq i} |u_{ij}| \le |u_{ii}|$ for every $i$. Let $Ux = b$, and let $\hat x$
be computed by backward substitution from $U$ and $b$ (`FloatingPoint.RoundsBackSubst`). If
$c \in K$ bounds $|\hat x_j|$ for every $j$, then for every $i$
$$|x_i - \hat x_i| \le (2n - 1) \gamma_n c.$$

This is the diagonally dominant case of §3.2.2 of [quarteroni2000numerical] ("the same result
holds … if $L$ and $U$ are diagonally dominant"), with $c$ in the place of $\|\hat x\|_\infty$.
The bound is linear in $n$, which is better than the bound $2^{n-i+1}$ that the sentence of the
source suggests. The proof combines Theorem 8.5 of [higham2002accuracy] with Lemma 8.8
(`Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant'`). Row diagonal dominance is
`Matrix.IsAbsDiagDominant`. -/
theorem abs_sub_le_of_roundsBackSubst_of_isDiagDominant {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card n : K) * m.u < 1) {U : Matrix n n K} (hU : U.IsUpperTriangular)
    (hd : ∀ i, U i i ≠ 0) (hdom : U.IsAbsDiagDominant) {x b xhat : n → K}
    (hx : U *ᵥ x = b) (h : RoundsBackSubst m U b xhat) {c : K} (hc : ∀ j, |xhat j| ≤ c) (i : n) :
    |x i - xhat i| ≤ (2 * Fintype.card n - 1) * gamma m.u (Fintype.card n) * c := by
  obtain ⟨ΔU, hΔ, hxhat⟩ := exists_roundsBackSubst_eq hu hcard hU hd h
  have hγ := gamma_nonneg m.u_nonneg hcard
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc i)
  refine (abs_sub_apply_le_of_mulVec_eq_of_abs_le hU hd hx hxhat hγ hΔ
    fun j _ => hc j).trans ?_
  calc gamma m.u (Fintype.card n) * c * ∑ j, (U⁻¹.abs * U.abs) i j
      ≤ gamma m.u (Fintype.card n) * c * (2 * Fintype.card n - 1) :=
        mul_le_mul_of_nonneg_left
          (Matrix.sum_abs_inv_mul_abs_apply_le_of_isDiagDominant' hU hd hdom i)
          (mul_nonneg hγ hc0)
    _ = (2 * Fintype.card n - 1) * gamma m.u (Fintype.card n) * c := by ring

end Backward

/-!
### The exact model

In `FloatingPoint.RoundingModel.exact` every rounding is the identity. There the substitution
relations hold exactly for the results of the recurrences `Matrix.forwardSubst` and
`Matrix.backSubst`, with no hypothesis on the matrix: both sides divide by a zero diagonal entry
with the same value $0$. This is how the exact specification of a substitution program follows from
its rounding analysis.
-/

section Exact

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Let $T \in K^{n \times n}$ and $b, x \in K^n$, over any field $K$. If
$$x_i = \Big(b_i - \sum_{j < i} t_{ij} x_j\Big) / t_{ii}$$
for every index $i$, then $x$ is `Matrix.forwardSubst T b`. This includes the case of a zero
diagonal entry, where both sides divide by zero with the value $0$. -/
theorem _root_.Matrix.eq_forwardSubst_of_forall_apply_eq {T : Matrix n n K} {b x : n → K}
    (h : ∀ i, x i = (b i - ∑ j ∈ univ.filter (· < i), T i j * x j) / T i i) :
    x = T.forwardSubst b := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
  rw [h i, Matrix.forwardSubst_apply]
  congr 2
  exact Finset.sum_congr rfl fun j hj => by rw [ih j (mem_filter.1 hj).2]

/-- In the exact model, $t$ is the running sum of $c$ and the terms $-p_j$, $j \in o$, for a list
$o$ of distinct indices, if and only if $t = c - \sum_{j \in o} p_j$. -/
theorem roundsSumFrom_exact_map_neg_iff {o : List ι} (hnd : o.Nodup) {p : ι → K} {c t : K} :
    RoundsSumFrom (RoundingModel.exact K) c (o.map fun j => -p j) t ↔
      t = c - ∑ j ∈ o.toFinset, p j := by
  rw [roundsSumFrom_exact_iff, ← List.sum_toFinset _ hnd, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- In the exact model, `FloatingPoint.RoundsForwardSubst` holds for $T$, $b$ and $x$ if and only if
$x$ is `Matrix.forwardSubst T b`. There is no hypothesis on $T$. -/
theorem roundsForwardSubst_exact_iff {T : Matrix n n K} {b x : n → K} :
    RoundsForwardSubst (RoundingModel.exact K) T b x ↔ x = T.forwardSubst b := by
  constructor
  · intro h
    refine Matrix.eq_forwardSubst_of_forall_apply_eq fun i => ?_
    obtain ⟨o, t, hnd, ho, ht, hx⟩ := h i
    rw [RoundingModel.exact_rounds_iff] at hx
    rw [hx, ht.eq_of_exact hnd, toFinset_eq_filter_lt_of_forall_mem_iff ho]
  · rintro rfl i
    refine ⟨(univ.filter (· < i)).toList,
      b i - ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      Finset.nodup_toList _, fun j => by simp, ?_, ?_⟩
    · rw [roundsRunningDiff_exact_iff, List.sum_toFinset _ (Finset.nodup_toList _)]
    · rw [RoundingModel.exact_rounds_iff, Finset.toList_toFinset]
      exact Matrix.forwardSubst_apply T b i

/-- In the exact model, `FloatingPoint.RoundsBackSubst` holds for $U$, $b$ and $x$ if and only if
$x$ is `Matrix.backSubst U b`. There is no hypothesis on $U$. This is the dual of
`FloatingPoint.roundsForwardSubst_exact_iff`. -/
theorem roundsBackSubst_exact_iff {U : Matrix n n K} {b x : n → K} :
    RoundsBackSubst (RoundingModel.exact K) U b x ↔ x = U.backSubst b := by
  rw [roundsBackSubst_iff_roundsForwardSubst_toDual, Matrix.backSubst_eq_forwardSubst_toDual]
  exact roundsForwardSubst_exact_iff (n := nᵒᵈ)

/-- In the exact model, `FloatingPoint.RoundsForwardSubstDot` holds for $T$, $b$ and $x$ if and only
if $x$ is `Matrix.forwardSubst T b`. There is no hypothesis on $T$.

The additions $0 + p$ and $b_i - s$ are exact when $u = 0$. -/
theorem roundsForwardSubstDot_exact_iff {T : Matrix n n K} {b x : n → K} :
    RoundsForwardSubstDot (RoundingModel.exact K) T b x ↔ x = T.forwardSubst b := by
  constructor
  · intro h
    refine Matrix.eq_forwardSubst_of_forall_apply_eq fun i => ?_
    by_cases hi : IsMin i
    · rw [Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt, Finset.sum_empty, sub_zero]
      exact (h i).1 hi
    · obtain ⟨o, p, s, t, hnd, ho, hp, hs, ht, hx⟩ := (h i).2 hi
      rw [roundsSumFrom_exact_iff, zero_add, ← List.sum_toFinset _ hnd,
        toFinset_eq_filter_lt_of_forall_mem_iff ho] at hs
      rw [RoundingModel.exact_rounds_iff] at ht hx
      rw [hx, ht, hs]
      congr 2
      exact Finset.sum_congr rfl fun j hj => hp j ((ho j).2 (mem_filter.1 hj).2)
  · rintro rfl i
    refine ⟨fun hi => ?_, fun _ => ⟨(univ.filter (· < i)).toList,
      fun j => T i j * T.forwardSubst b j,
      ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      b i - ∑ j ∈ (univ.filter (· < i)).toList.toFinset, T i j * T.forwardSubst b j,
      Finset.nodup_toList _, fun j => by simp, fun _ _ => rfl, ?_, rfl, ?_⟩⟩
    · rw [RoundingModel.exact_rounds_iff, Matrix.forwardSubst_apply,
        Finset.filter_eq_empty_iff.2 fun j _ => hi.not_lt, Finset.sum_empty, sub_zero]
    · rw [roundsSumFrom_exact_iff, zero_add, List.sum_toFinset _ (Finset.nodup_toList _)]
    · rw [RoundingModel.exact_rounds_iff, Finset.toList_toFinset]
      exact Matrix.forwardSubst_apply T b i

/-- In the exact model, `FloatingPoint.RoundsBackSubstDot` holds for $U$, $b$ and $x$ if and only if
$x$ is `Matrix.backSubst U b`. There is no hypothesis on $U$. The proof uses the reversed order
of the indices. -/
theorem roundsBackSubstDot_exact_iff {U : Matrix n n K} {b x : n → K} :
    RoundsBackSubstDot (RoundingModel.exact K) U b x ↔ x = U.backSubst b := by
  rw [roundsBackSubstDot_iff_roundsForwardSubstDot_toDual, Matrix.backSubst_eq_forwardSubst_toDual]
  exact roundsForwardSubstDot_exact_iff (n := nᵒᵈ)

end Exact

end FloatingPoint

/-!
### Column-oriented forward substitution as a program

The loop "for $j$ in increasing order, $b_j := b_j / \ell_{jj}$, then $b_i := b_i - b_j \ell_{ij}$
for every $i > j$" is Algorithm 3.1.3 of [golub2013matrix]. Here it runs over any linear order, so
Algorithm 3.1.4 is its instance for the reversed order. In every run of the relational model the
loop computes a `FloatingPoint.RoundsForwardSubst`: row $i$ receives its subtractions over $j < i$
one at a time, each from the finished $\hat x_j$, and this is a running difference in the order of
the outer loop. The same loop without the division, for a unit lower triangular $L$, computes a
`FloatingPoint.RoundsUnitForwardSubst`
(`FloatingPoint.roundsUnitForwardSubst_of_mem_run_unitColSubst`).
-/

namespace FloatingPoint

universe u

section ColSubst

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι : Type u} [LinearOrder ι] [DecidableEq ι]

/-- The loop invariant of column-oriented forward substitution: an index outside the remaining list
$l$ is a finished row of `FloatingPoint.RoundsForwardSubst`, and an index $i$ in $l$ holds the
running difference of $b_i$ over the finished indices. -/
private def ColInv (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (l : List ι)
    (s : ι → K) : Prop :=
  (∀ i, i ∉ l → ∃ (o : List ι) (t : K), o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
      RoundsRunningDiff fp o (L i) s (b i) t ∧ fp.Rounds (t / L i i) (s i)) ∧
  (∀ i, i ∈ l → ∃ o : List ι, o.Nodup ∧ (∀ j, j ∈ o ↔ j ∉ l) ∧
      RoundsRunningDiff fp o (L i) s (b i) (s i))

/-- One step of the outer loop keeps the loop invariant. -/
private theorem colInv_step (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (j : ι)
    (c : List ι) (hcm : ∀ i, i ∈ c ↔ j < i) (l : List ι)
    (hsort : (j :: l).Pairwise (· < ·)) (hup : ∀ i ∈ j :: l, ∀ k, i ≤ k → k ∈ j :: l)
    (s : ι → K) (hs : ColInv fp L b (j :: l) s) (y : K) (hy : fp.Rounds (s j / L j j) y)
    (s₂ : ι → K)
    (h₂ : (∀ i, i ∉ c → s₂ i = Function.update s j y i) ∧
      ∀ i ∈ c, ∃ p, fp.Rounds (Function.update s j y j * L i j) p ∧
        fp.Rounds (Function.update s j y i - p) (s₂ i)) :
    ColInv fp L b l s₂ := by
  have hlt : ∀ k, k ∉ j :: l ↔ k < j := by
    intro k
    constructor
    · intro hk
      by_contra h
      exact hk (hup j List.mem_cons_self k (not_lt.1 h))
    · intro hk hmem
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact lt_irrefl _ hk
      · exact lt_asymm hk (List.rel_of_pairwise_cons hsort hmem)
  have hjl : j ∉ l := fun h => lt_irrefl _ (List.rel_of_pairwise_cons hsort h)
  have hbelow : ∀ k, k < j → s₂ k = s k := by
    intro k hk
    rw [h₂.1 k (by rw [hcm]; exact lt_asymm hk), Function.update_of_ne (ne_of_lt hk)]
  have hj₂ : s₂ j = y := by
    rw [h₂.1 j (by rw [hcm]; exact lt_irrefl _), Function.update_self]
  obtain ⟨hfin, hrun⟩ := hs
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hij : i = j
    · subst hij
      obtain ⟨o, hnd, ho, hrd⟩ := hrun i List.mem_cons_self
      refine ⟨o, s i, hnd, fun k => (ho k).trans (hlt k),
        hrd.congr (fun _ _ => rfl) fun k hk => hbelow k ((hlt k).1 ((ho k).1 hk)), ?_⟩
      rw [hj₂]
      exact hy
    · have hi' : i ∉ j :: l := by
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact hij h
        · exact hi h
      have hij' : i < j := (hlt i).1 hi'
      obtain ⟨o, t, hnd, ho, hrd, hr⟩ := hfin i hi'
      refine ⟨o, t, hnd, ho,
        hrd.congr (fun _ _ => rfl) fun k hk => hbelow k (lt_trans ((ho k).1 hk) hij'), ?_⟩
      rw [hbelow i hij']
      exact hr
  · have hji : j < i := List.rel_of_pairwise_cons hsort hi
    obtain ⟨o, hnd, ho, hrd⟩ := hrun i (List.mem_cons_of_mem _ hi)
    obtain ⟨q, hq, hq'⟩ := h₂.2 i ((hcm i).2 hji)
    rw [Function.update_of_ne (ne_of_gt hji)] at hq'
    rw [Function.update_self] at hq
    have hjo : j ∉ o := fun h => (ho j).1 h List.mem_cons_self
    refine ⟨o ++ [j], hnd.append (List.nodup_singleton _) (List.disjoint_singleton.2 hjo),
      fun k => ?_, ?_⟩
    · rw [List.mem_append, ho k, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact fun h' => h (List.mem_cons_of_mem _ h')
        · exact hjl
      · intro h
        by_cases hkj : k = j
        · exact Or.inr hkj
        · exact Or.inl fun h' => by
            rcases List.mem_cons.1 h' with h' | h'
            · exact hkj h'
            · exact h h'
    · refine (hrd.congr (b' := s₂) (fun _ _ => rfl) fun k hk =>
        hbelow k ((hlt k).1 ((ho k).1 hk))).append_singleton hjo ?_ hq'
      rw [hj₂, mul_comm]
      exact hq

/-- The outer loop keeps the loop invariant, by induction on the remaining list. -/
private theorem colInv_foldlM (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K)
    (c : ι → List ι) (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) :
    ∀ (l : List ι) (s s' : ι → K), l.Pairwise (· < ·) →
    (∀ i ∈ l, ∀ k, i ≤ k → k ∈ l) → ColInv fp L b l s →
    s' ∈ (l.foldlM (fun (b : ι → K) j => do
      let bj ← fp.round (b j / L j j)
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj)) s).run →
    ColInv fp L b [] s' := by
  intro l
  induction l with
  | nil =>
    intro s s' _ _ hs h
    rw [List.foldlM_nil, SetM.mem_run_pure] at h
    exact h ▸ hs
  | cons j l ih =>
    intro s s' hsort hup hs h
    simp only [List.foldlM_cons, bind_assoc] at h
    rw [SetM.mem_run_bind] at h
    obtain ⟨y, hy, h⟩ := h
    rw [SetM.mem_run_bind] at h
    obtain ⟨s₂, h₂, h⟩ := h
    have key := SetM.mem_run_foldlM_update_of_nodup
      (fun a v (z : ι → K) => fp.round (z j * L a j) >>= fun p => fp.round (v - p)) (c j) (hc j)
      (fun a _ v z z' hz => by rw [hz j fun h => lt_irrefl j ((hcm j j).1 h)])
      (Function.update s j y) s₂
    simp only [bind_assoc] at key
    obtain ⟨hout, hin⟩ := key.1 h₂
    have hin' : ∀ i ∈ c j, ∃ p, fp.Rounds (Function.update s j y j * L i j) p ∧
        fp.Rounds (Function.update s j y i - p) (s₂ i) := fun i hi => by
      obtain ⟨p, hp, hq⟩ := SetM.mem_run_bind.1 (hin i hi)
      exact ⟨p, hp, hq⟩
    refine ih s₂ s' (List.pairwise_cons.1 hsort).2 (fun i hi k hik => ?_)
      (colInv_step fp L b j (c j) (hcm j) l hsort hup s hs y hy s₂ ⟨hout, hin'⟩) h
    rcases List.mem_cons.1 (hup i (List.mem_cons_of_mem _ hi) k hik) with rfl | hk
    · exact absurd (lt_of_lt_of_le (List.rel_of_pairwise_cons hsort hi) hik) (lt_irrefl _)
    · exact hk

/-- **Column-oriented forward substitution.** Let $L \in K^{n \times n}$, $b \in K^n$, let $l$ be
the list of all indices in increasing order, and for each index $j$ let $c_j$ be a list of
distinct indices whose members are exactly the indices $i > j$. Consider the loop that, for $j$
in the order of $l$, sets $b_j := \mathrm{fl}(b_j / \ell_{jj})$ and then, for $i$ in the order
of $c_j$, sets $b_i := \mathrm{fl}(b_i - \mathrm{fl}(b_j \ell_{ij}))$. Every result $x$ of a run
of this loop in the rounding model satisfies `FloatingPoint.RoundsForwardSubst` for $L$, $b$ and
$x$.

This is Algorithm 3.1.3 of [golub2013matrix], over any linear order of the indices. Algorithm
3.1.4 is its instance for the reversed order, through
`FloatingPoint.roundsBackSubst_iff_roundsForwardSubst_toDual`. In the proof, row $i$ receives
its subtractions over $j < i$ one at a time, each from the finished $\hat x_j$. There is no
hypothesis on $L$. The set of results of a run is the `run` of the program in the set monad of
`Numlib.FloatingPoint.Program`. -/
theorem roundsForwardSubst_of_mem_run_colSubst (fp : RoundingModel K) (L : Matrix ι ι K)
    {l : List ι} (hl : l.Pairwise (· < ·)) (hall : ∀ i, i ∈ l) (c : ι → List ι)
    (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) (b x : ι → K)
    (hx : x ∈ (l.foldlM (fun (b : ι → K) j => do
      let bj ← fp.round (b j / L j j)
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi))
        (Function.update b j bj)) b).run) :
    RoundsForwardSubst fp L b x := by
  have h0 : ColInv fp L b l b := by
    refine ⟨fun i hi => absurd (hall i) hi, fun i _ => ?_⟩
    exact ⟨[], List.nodup_nil, fun j => by simp [hall j], fun _ => 0, by simp, .nil _⟩
  have := colInv_foldlM fp L b c hc hcm l b x hl (fun _ _ k _ => hall k) h0 hx
  exact fun i => this.1 i (by simp)

/-- **Unit lower triangular forward substitution in floating-point arithmetic.** Let
$L \in K^{n \times n}$ and $b, \hat x \in K^n$. The relation
`FloatingPoint.RoundsUnitForwardSubst fp L b xhat` holds if, for every index $i$, there is a
list $o$ of distinct indices whose members are exactly the indices $j < i$, such that $\hat x_i$
is computed from $b_i - \sum_{j < i} \ell_{ij} \hat x_j$ as a running difference in the order
$o$.

This is `FloatingPoint.RoundsForwardSubst` without the division by the unit diagonal, which a
unit triangular solve inside a factorization does not perform (§3.1.7 of [golub2013matrix]). The
diagonal of $L$ is not read. -/
def RoundsUnitForwardSubst (fp : RoundingModel K) (L : Matrix ι ι K) (b xhat : ι → K) : Prop :=
  ∀ i, ∃ o : List ι, o.Nodup ∧ (∀ j, j ∈ o ↔ j < i) ∧
    RoundsRunningDiff fp o (L i) xhat (b i) (xhat i)

/-- The loop invariant of unit column-oriented forward substitution: every row $i$ holds the running
difference of $b_i$ over the finished indices below $i$, which are the indices not in the
remaining list $l$. -/
private def UnitColInv (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (l : List ι)
    (s : ι → K) : Prop :=
  ∀ i, ∃ o : List ι, o.Nodup ∧ (∀ k, k ∈ o ↔ k < i ∧ k ∉ l) ∧
    RoundsRunningDiff fp o (L i) s (b i) (s i)

omit [DecidableEq ι] in
/-- One step of the outer loop of the unit solve keeps the loop invariant. -/
private theorem unitColInv_step (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K) (j : ι)
    (c : List ι) (hcm : ∀ i, i ∈ c ↔ j < i) (l : List ι)
    (hsort : (j :: l).Pairwise (· < ·)) (hup : ∀ i ∈ j :: l, ∀ k, i ≤ k → k ∈ j :: l)
    (s : ι → K) (hs : UnitColInv fp L b (j :: l) s) (s₂ : ι → K)
    (h₂ : (∀ i, i ∉ c → s₂ i = s i) ∧
      ∀ i ∈ c, ∃ p, fp.Rounds (s j * L i j) p ∧ fp.Rounds (s i - p) (s₂ i)) :
    UnitColInv fp L b l s₂ := by
  have hlt : ∀ k, k ∉ j :: l ↔ k < j := by
    intro k
    constructor
    · intro hk
      by_contra h
      exact hk (hup j List.mem_cons_self k (not_lt.1 h))
    · intro hk hmem
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact lt_irrefl _ hk
      · exact lt_asymm hk (List.rel_of_pairwise_cons hsort hmem)
  have hjl : j ∉ l := fun h => lt_irrefl _ (List.rel_of_pairwise_cons hsort h)
  have hle : ∀ k, k ≤ j → s₂ k = s k := fun k hk => h₂.1 k (by rw [hcm]; exact not_lt.2 hk)
  intro i
  obtain ⟨o, hnd, ho, hrd⟩ := hs i
  by_cases hij : i ≤ j
  · refine ⟨o, hnd, fun k => ?_, ?_⟩
    · rw [ho k]
      constructor
      · rintro ⟨hki, hk⟩
        exact ⟨hki, fun h => hk (List.mem_cons_of_mem _ h)⟩
      · rintro ⟨hki, hk⟩
        refine ⟨hki, fun h => ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact lt_irrefl _ (lt_of_lt_of_le hki hij)
        · exact hk h
    · rw [hle i hij]
      exact hrd.congr (fun _ _ => rfl) fun k hk =>
        hle k (le_of_lt (lt_of_lt_of_le ((ho k).1 hk).1 hij))
  · have hji : j < i := lt_of_not_ge hij
    obtain ⟨q, hq, hq'⟩ := h₂.2 i ((hcm i).2 hji)
    have hjo : j ∉ o := fun h => ((ho j).1 h).2 List.mem_cons_self
    refine ⟨o ++ [j], hnd.append (List.nodup_singleton _) (List.disjoint_singleton.2 hjo),
      fun k => ?_, ?_⟩
    · rw [List.mem_append, ho k, List.mem_singleton]
      constructor
      · rintro (⟨hki, hk⟩ | rfl)
        · exact ⟨hki, fun h => hk (List.mem_cons_of_mem _ h)⟩
        · exact ⟨hji, hjl⟩
      · rintro ⟨hki, hk⟩
        by_cases hkj : k = j
        · exact Or.inr hkj
        · exact Or.inl ⟨hki, fun h => by
            rcases List.mem_cons.1 h with h | h
            · exact hkj h
            · exact hk h⟩
    · refine (hrd.congr (b' := s₂) (fun _ _ => rfl) fun k hk =>
        hle k (le_of_lt ((hlt k).1 ((ho k).1 hk).2))).append_singleton hjo ?_ hq'
      rw [hle j le_rfl, mul_comm]
      exact hq

/-- The outer loop of the unit solve keeps the loop invariant, by induction on the remaining list.
-/
private theorem unitColInv_foldlM (fp : RoundingModel K) (L : Matrix ι ι K) (b : ι → K)
    (c : ι → List ι) (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) :
    ∀ (l : List ι) (s s' : ι → K), l.Pairwise (· < ·) →
    (∀ i ∈ l, ∀ k, i ≤ k → k ∈ l) → UnitColInv fp L b l s →
    s' ∈ (l.foldlM (fun (b : ι → K) j =>
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi)) b) s).run →
    UnitColInv fp L b [] s' := by
  intro l
  induction l with
  | nil =>
    intro s s' _ _ hs h
    rw [List.foldlM_nil, SetM.mem_run_pure] at h
    exact h ▸ hs
  | cons j l ih =>
    intro s s' hsort hup hs h
    simp only [List.foldlM_cons] at h
    rw [SetM.mem_run_bind] at h
    obtain ⟨s₂, h₂, h⟩ := h
    have key := SetM.mem_run_foldlM_update_of_nodup
      (fun a v (z : ι → K) => fp.round (z j * L a j) >>= fun p => fp.round (v - p)) (c j) (hc j)
      (fun a _ v z z' hz => by rw [hz j fun h => lt_irrefl j ((hcm j j).1 h)]) s s₂
    simp only [bind_assoc] at key
    obtain ⟨hout, hin⟩ := key.1 h₂
    have hin' : ∀ i ∈ c j, ∃ p, fp.Rounds (s j * L i j) p ∧ fp.Rounds (s i - p) (s₂ i) :=
      fun i hi => by
        obtain ⟨p, hp, hq⟩ := SetM.mem_run_bind.1 (hin i hi)
        exact ⟨p, hp, hq⟩
    refine ih s₂ s' (List.pairwise_cons.1 hsort).2 (fun i hi k hik => ?_)
      (unitColInv_step fp L b j (c j) (hcm j) l hsort hup s hs s₂ ⟨hout, hin'⟩) h
    rcases List.mem_cons.1 (hup i (List.mem_cons_of_mem _ hi) k hik) with rfl | hk
    · exact absurd (lt_of_lt_of_le (List.rel_of_pairwise_cons hsort hi) hik) (lt_irrefl _)
    · exact hk

/-- **Unit column-oriented forward substitution.** Let $L \in K^{n \times n}$, $b \in K^n$, let $l$
be the list of all indices in increasing order, and for each index $j$ let $c_j$ be a list of
distinct indices whose members are exactly the indices $i > j$. Consider the loop that, for $j$
in the order of $l$ and then for $i$ in the order of $c_j$, sets $b_i := \mathrm{fl}(b_i -
\mathrm{fl}(b_j \ell_{ij}))$. Every result $x$ of a run of this loop in the rounding model
satisfies `FloatingPoint.RoundsUnitForwardSubst` for $L$, $b$ and $x$.

This is the loop of `FloatingPoint.roundsForwardSubst_of_mem_run_colSubst` without the division
by the unit diagonal. It is used for the solves with $L_{11}$ in the block LU Algorithms 3.2.3
and 3.2.4 of [golub2013matrix] (§3.1.7). -/
theorem roundsUnitForwardSubst_of_mem_run_unitColSubst (fp : RoundingModel K)
    (L : Matrix ι ι K) {l : List ι} (hl : l.Pairwise (· < ·)) (hall : ∀ i, i ∈ l)
    (c : ι → List ι) (hc : ∀ j, (c j).Nodup) (hcm : ∀ j i, i ∈ c j ↔ j < i) (b x : ι → K)
    (hx : x ∈ (l.foldlM (fun (b : ι → K) j =>
      (c j).foldlM (fun (b : ι → K) i => do
          let p ← fp.round (b j * L i j)
          let bi ← fp.round (b i - p)
          pure (Function.update b i bi)) b) b).run) :
    RoundsUnitForwardSubst fp L b x := by
  have h0 : UnitColInv fp L b l b := fun i =>
    ⟨[], List.nodup_nil, fun k => by simp [hall k], fun _ => 0, by simp, .nil _⟩
  intro i
  obtain ⟨o, hnd, ho, hrd⟩ :=
    unitColInv_foldlM fp L b c hc hcm l b x hl (fun _ _ k _ => hall k) h0 hx i
  exact ⟨o, hnd, fun k => by simp [ho k], hrd⟩

end ColSubst

end FloatingPoint
