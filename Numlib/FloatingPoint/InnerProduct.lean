/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Numlib.FloatingPoint.Model
import Numlib.LinearAlgebra.Matrix.Order

/-!
# Rounding errors of inner products and matrix products

This module proves the componentwise error bounds of [higham2002accuracy], §3.1–§3.5, for recursive
summation, inner products, matrix–vector products and matrix products, in the rounding model of
`Numlib.FloatingPoint.Model`. In that model, a rounding model on an ordered field $K$ has a unit
roundoff $u \ge 0$, an admissible rounding $\mathrm{fl}(x)$ of $x$ satisfies
$|\mathrm{fl}(x) - x| \le u |x|$, and the error constants are $\gamma_n = nu / (1 - nu)$. The main
bounds are $|\hat s - \sum_i x_i| \le \gamma_{n-1} \sum_i |x_i|$ for a computed recursive sum of $n$
numbers, $|\mathrm{fl}(x^T y) - x^T y| \le \gamma_n |x|^T |y|$ for a computed inner product of
length $n$, with the backward form $\mathrm{fl}(x^T y) = (x + \Delta x)^T y$,
$|\Delta x| \le \gamma_n |x|$, and the entrywise bounds $|\hat y - Ax| \le \gamma_n |A| |x|$ and
$|\hat C - AB| \le \gamma_n |A| |B|$, where $n$ is the inner dimension.

Each statement is about an explicit order of evaluation. A recursive sum adds the terms from left to
right and rounds after each addition. A computed inner product is a recursive sum, in some order of
the indices, of the rounded products $\mathrm{fl}(x_i y_i)$, and the results hold for every order.
The sharp product form $\mathrm{fl}(x^T y) = \sum_i x_i y_i (1 + \theta_i)$ with
$|\theta_i| \le (1 + u)^n - 1$ of [golub2013matrix] (2.7.10) needs no hypothesis on $nu$, and it
gives the classical constant $1.01\, nu$ of [golub2013matrix] (2.7.11). The module also treats the
running difference $c - \sum_{r} a_r b_r$ of [higham2002accuracy], Lemma 8.4, which computes the
entries in the substitutions of `Numlib.FloatingPoint.Substitution` and in the factorizations of
`Numlib.FloatingPoint.LU`.

## Main definitions

* `FloatingPoint.RoundsSumFrom`: $t$ results from a partial sum $s$ when the terms of a list are
  added from left to right, with one rounding per addition.
* `FloatingPoint.RoundsSum`: $s$ is a computed recursive sum of a list.
* `FloatingPoint.RoundsDot`: $s$ is a computed inner product $x^T y$, in some order of summation.
* `FloatingPoint.RoundsRunningDiff`: $t$ is a computed running difference
  $c - \sum_{r \in o} a_r b_r$.
* `FloatingPoint.RoundsMulVec` and `FloatingPoint.RoundsMul`: each entry of the result is a computed
  inner product of a row of $A$ with $x$, or with a column of $B$.

## Main results

* `FloatingPoint.abs_sub_le_of_roundsSum`: $|\hat s - \sum_i x_i| \le \gamma_{n-1} \sum_i |x_i|$.
* `FloatingPoint.abs_sub_le_of_roundsDot`: $|\mathrm{fl}(x^T y) - x^T y| \le \gamma_n |x|^T |y|$.
* `FloatingPoint.exists_roundsDot_eq_dotProduct_add`: $\mathrm{fl}(x^T y) = (x + \Delta x)^T y$ with
  $|\Delta x| \le \gamma_n |x|$.
* `FloatingPoint.exists_eq_sum_mul_one_add_of_roundsDot`: $\mathrm{fl}(x^T y) = \sum_i x_i y_i (1 +
  \theta_i)$ with $|\theta_i| \le (1 + u)^n - 1$.
* `FloatingPoint.abs_sub_le_of_roundsMulVec`: $|\hat y - Ax| \le \gamma_n |A| |x|$ entrywise.
* `FloatingPoint.abs_sub_entrywiseLE_of_roundsMul`: $|\hat C - AB| \le \gamma_n |A| |B|$ entrywise.
* `FloatingPoint.exists_roundsSumFrom_map_eq_add_sum`: a running sum is
  $c (1 + \varphi) + \sum_j f_j (1 + \theta_j)$ with $|\varphi|, |\theta_j| \le \gamma_k$.
* `FloatingPoint.roundsRunningDiff_exact_iff`: in the exact model, a computed running difference is
  the difference $c - \sum_r a_r b_r$.

## Proof outline

Every bound follows from one scalar step, `FloatingPoint.gamma_mul_one_add_add_le`:
$\gamma_k (1 + u) + u \le \gamma_{k+1}$. That is, one more rounding raises the order of a relative
perturbation by one.

## Implementation notes

* The rounding relation is not a function. Therefore every statement holds for all admissible
  roundings at once.
* The first term of a recursive sum enters unrounded, so a list of length $n$ costs $n - 1$
  roundings.
* The uniform bound $\|\hat y - Ax\|_\infty \le \gamma_n \|A\|_\infty \|x\|_\infty$ is
  `FloatingPoint.abs_sub_le_of_roundsMulVec_of_abs_le`. It is stated with row sums and an entrywise
  bound on $x$, because the scalar field has an order but no norm.
* The entrywise order and the entrywise absolute value of matrices are those of
  `Numlib.LinearAlgebra.Matrix.Order`: `A ≤ₑ B` is `Matrix.EntrywiseLE A B`, and `A.abs` is
  `Matrix.abs A`.
* Over a list of distinct indices, the results of the program `FloatingPoint.runningDiff` of
  `Numlib.FloatingPoint.Program` are exactly the computed running differences
  (`FloatingPoint.mem_run_runningDiff_iff`).
-/

open Finset

open scoped Matrix

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Recursive summation -/

/-- Let $K$ be an ordered field with a rounding model of unit roundoff $u$. For $s, t \in K$ and a
list $l = (x_1, \dots, x_k)$, the relation holds when $t$ is a possible computed value of the
addition of the terms of $l$ to the partial sum $s$, from left to right, with one rounding per
addition: $t_0 = s$, $t_i$ is an admissible rounding of $t_{i-1} + x_i$ for $i = 1, \dots, k$,
and $t = t_k$.

The relation is defined inductively. It is not a function, so a theorem about it holds for every
admissible sequence of roundings. -/
inductive RoundsSumFrom (m : RoundingModel K) : K → List K → K → Prop
  /-- The addition of no terms leaves the partial sum unchanged. -/
  | nil (s : K) : RoundsSumFrom m s [] s
  /-- If $t$ is an admissible rounding of $s + x$, and the addition of the terms of $l$ to $t$ gives
  $r$, then the addition of the terms of $x :: l$ to $s$ gives $r$. -/
  | cons {s x t r : K} {l : List K} (ht : m.Rounds (s + x) t) (hr : RoundsSumFrom m t l r) :
      RoundsSumFrom m s (x :: l) r

/-- The **recursive summation** of a list ([higham2002accuracy], §3.1). A value $s$ is a computed
recursive sum of $(x_1, \dots, x_n)$ if $s_1 = x_1$, $s_i$ is an admissible rounding of
$s_{i-1} + x_i$ for $i = 2, \dots, n$, and $s = s_n$. The recursive sum of the empty list is
exactly $0$.

The first term enters unrounded, so a list of length $n$ costs $n - 1$ roundings. For a nonempty
list, the relation is `FloatingPoint.RoundsSumFrom` started at the first term. -/
def RoundsSum (m : RoundingModel K) : List K → K → Prop
  | [], s => s = 0
  | x :: l, s => RoundsSumFrom m x l s

/-- A value $s$ is a computed recursive sum of the empty list if and only if $s = 0$. -/
@[simp]
theorem roundsSum_nil {m : RoundingModel K} {s : K} : RoundsSum m [] s ↔ s = 0 := Iff.rfl

/-- A value $s$ is a computed recursive sum of $x :: l$ if and only if it results from the addition
of the terms of $l$ to the unrounded first term $x$, with one rounding per addition. Therefore a
list of length $n$ costs only $n - 1$ roundings. -/
@[simp]
theorem roundsSum_cons {m : RoundingModel K} {x : K} {l : List K} {s : K} :
    RoundsSum m (x :: l) s ↔ RoundsSumFrom m x l s := Iff.rfl

/-- The sum of the absolute values of a list is nonnegative. -/
private theorem sum_map_abs_nonneg (l : List K) : 0 ≤ (l.map (|·|)).sum :=
  List.sum_nonneg fun _ hy => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
    exact abs_nonneg z

/-- Let $u < 1$, and let $l = (x_1, \dots, x_k)$ be a list with $ku < 1$. If $t$ results from the
addition of the terms of $l$ to $s$, from left to right with one rounding per addition, then
$$\Bigl|t - \Bigl(s + \sum_i x_i\Bigr)\Bigr| \le \gamma_k \Bigl(|s| + \sum_i |x_i|\Bigr).$$
This is the bound (3.2)–(3.3) of [higham2002accuracy] for a recursive sum that starts from a
partial sum. -/
theorem abs_sub_le_of_roundsSumFrom {m : RoundingModel K} (hu : m.u < 1) {s : K} {l : List K}
    {t : K} (h : RoundsSumFrom m s l t) (hlu : ((l.length : ℕ) : K) * m.u < 1) :
    |t - (s + l.sum)| ≤ gamma m.u l.length * (|s| + (l.map (|·|)).sum) := by
  induction h with
  | nil s => simp
  | @cons s x t r l ht hr ih =>
    rw [List.length_cons] at hlu
    have hcast : ((l.length + 1 : ℕ) : K) * m.u = (l.length : K) * m.u + m.u := by push_cast; ring
    have hl : (l.length : K) * m.u < 1 := by
      rw [hcast] at hlu; linarith [m.u_nonneg]
    have ihl := ih hl
    have hS : 0 ≤ (l.map (|·|)).sum := sum_map_abs_nonneg l
    have hA : 0 ≤ |s| + |x| := by positivity
    have hgl : 0 ≤ gamma m.u l.length := gamma_nonneg m.u_nonneg hl
    have hround : |t - (s + x)| ≤ m.u * (|s| + |x|) :=
      (m.abs_sub_le ht).trans (mul_le_mul_of_nonneg_left (abs_add_le s x) m.u_nonneg)
    have habs : |t| ≤ (1 + m.u) * (|s| + |x|) := by
      have h1 : |t| ≤ |t - (s + x)| + |s + x| := by
        simpa using abs_add_le (t - (s + x)) (s + x)
      have h2 : |s + x| ≤ |s| + |x| := abs_add_le s x
      nlinarith
    have htail : |r - (t + l.sum)|
        ≤ gamma m.u l.length * ((1 + m.u) * (|s| + |x|) + (l.map (|·|)).sum) :=
      ihl.trans (mul_le_mul_of_nonneg_left (by linarith) hgl)
    have hstep : gamma m.u l.length * (1 + m.u) + m.u ≤ gamma m.u (l.length + 1) :=
      gamma_mul_one_add_add_le m.u_nonneg hu hlu
    have hmono : gamma m.u l.length ≤ gamma m.u (l.length + 1) :=
      gamma_mono m.u_nonneg (Nat.le_succ _) hlu
    have hsplit : |r - (s + (x :: l).sum)| ≤ |r - (t + l.sum)| + |t - (s + x)| := by
      have harg : r - (s + (x :: l).sum) = r - (t + l.sum) + (t - (s + x)) := by
        simp only [List.sum_cons]; ring
      rw [harg]
      exact abs_add_le _ _
    refine hsplit.trans ?_
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    calc |r - (t + l.sum)| + |t - (s + x)|
        ≤ gamma m.u l.length * ((1 + m.u) * (|s| + |x|) + (l.map (|·|)).sum)
            + m.u * (|s| + |x|) := add_le_add htail hround
      _ = (gamma m.u l.length * (1 + m.u) + m.u) * (|s| + |x|)
            + gamma m.u l.length * (l.map (|·|)).sum := by ring
      _ ≤ gamma m.u (l.length + 1) * (|s| + |x|)
            + gamma m.u (l.length + 1) * (l.map (|·|)).sum :=
          add_le_add (mul_le_mul_of_nonneg_right hstep hA)
            (mul_le_mul_of_nonneg_right hmono hS)
      _ = gamma m.u (l.length + 1) * (|s| + (|x| + (l.map (|·|)).sum)) := by ring

/-- Let $u < 1$, and let $l = (x_1, \dots, x_n)$ be a list with $(n - 1) u < 1$. A computed
recursive sum $\hat s$ of $l$ satisfies
$$\Bigl|\hat s - \sum_i x_i\Bigr| \le \gamma_{n-1} \sum_i |x_i|.$$
This is the bound (3.2)–(3.3) of [higham2002accuracy].

The index $n - 1$ is subtraction of natural numbers, so it is $0$ for the empty list. -/
theorem abs_sub_le_of_roundsSum {m : RoundingModel K} (hu : m.u < 1) {l : List K} {s : K}
    (h : RoundsSum m l s) (hlu : ((l.length - 1 : ℕ) : K) * m.u < 1) :
    |s - l.sum| ≤ gamma m.u (l.length - 1) * (l.map (|·|)).sum := by
  cases l with
  | nil => simp only [roundsSum_nil] at h; simp [h]
  | cons x l =>
    simp only [List.length_cons, Nat.add_sub_cancel] at hlu ⊢
    simpa using abs_sub_le_of_roundsSumFrom hu (roundsSum_cons.1 h) hlu

/-- **Appending one term to a running sum.** The addition of the terms of $l$ followed by $x$ to $s$
gives $r$ if and only if there is a $t$ such that the addition of the terms of $l$ to $s$ gives
$t$ and $r$ is an admissible rounding of $t + x$.

This is the step of every loop invariant that grows a running sum one term at a time. -/
theorem roundsSumFrom_append_singleton {m : RoundingModel K} {s x r : K} {l : List K} :
    RoundsSumFrom m s (l ++ [x]) r ↔ ∃ t, RoundsSumFrom m s l t ∧ m.Rounds (t + x) r := by
  induction l generalizing s with
  | nil =>
    constructor
    · rintro (_ | ⟨ht, hr⟩)
      cases hr
      exact ⟨s, .nil s, ht⟩
    · rintro ⟨t, ht, hr⟩
      cases ht
      exact .cons hr (.nil _)
  | cons y l ih =>
    constructor
    · rintro (_ | ⟨ht, hr⟩)
      obtain ⟨t', h1, h2⟩ := ih.1 hr
      exact ⟨t', .cons ht h1, h2⟩
    · rintro ⟨t, (_ | ⟨ht, hr⟩), h2⟩
      exact .cons ht (ih.2 ⟨t, hr, h2⟩)

/-- In the exact model `FloatingPoint.RoundingModel.exact`, the addition of the terms of $l$ to $c$
gives $t$ if and only if $t = c + \sum_i l_i$. -/
theorem roundsSumFrom_exact_iff {c t : K} {l : List K} :
    RoundsSumFrom (RoundingModel.exact K) c l t ↔ t = c + l.sum := by
  induction l generalizing c with
  | nil =>
    refine ⟨fun h => by cases h; simp, fun h => ?_⟩
    rw [h, List.sum_nil, add_zero]
    exact .nil c
  | cons x l ih =>
    constructor
    · rintro (_ | ⟨ht, hr⟩)
      rw [RoundingModel.exact_rounds_iff] at ht
      subst ht
      rw [ih.1 hr, List.sum_cons, add_assoc]
    · intro h
      exact .cons (RoundingModel.exact_rounds_iff.2 rfl)
        (ih.2 (by rw [h, List.sum_cons, add_assoc]))

/-! ### One rounded update -/

/-- Let $a, x, y \in K$. If $p$ is an admissible rounding of $ax$ and $s$ is an admissible rounding
of $y + p$, so that $s = \mathrm{fl}(y + \mathrm{fl}(ax))$, then
$$|s - (y + ax)| \le u |y| + (2u + u^2) |ax|.$$
This is (2.7.17)–(2.7.18) of [golub2013matrix], with the second-order term written out. -/
theorem abs_sub_le_of_rounds_add_mul {m : RoundingModel K} {a x y p s : K}
    (hp : m.Rounds (a * x) p) (hs : m.Rounds (y + p) s) :
    |s - (y + a * x)| ≤ m.u * |y| + (2 * m.u + m.u ^ 2) * |a * x| := by
  obtain ⟨δ, hδ, rfl⟩ := hp.exists_delta
  obtain ⟨ε, hε, rfl⟩ := hs.exists_delta
  have hu := m.u_nonneg
  have heq : (y + a * x * (1 + δ)) * (1 + ε) - (y + a * x)
      = ε * y + a * x * (δ + ε + δ * ε) := by ring
  rw [heq]
  calc |ε * y + a * x * (δ + ε + δ * ε)|
      ≤ |ε| * |y| + |a * x| * (|δ| + |ε| + |δ| * |ε|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul (a * x)]
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        gcongr
        exact abs_add_le _ _
    _ ≤ m.u * |y| + |a * x| * (m.u + m.u + m.u * m.u) := by gcongr
    _ = m.u * |y| + (2 * m.u + m.u ^ 2) * |a * x| := by ring

/-! ### Inner products -/

variable {ι : Type*}

/-- Let $x, y \colon \iota \to K$. A value $s$ is a **computed inner product** of $x$ and $y$ if
there are a list $o$ that contains every index exactly once and admissible roundings $p_i$ of
the products $x_i y_i$ such that $s$ is a computed recursive sum of the values $p_i$ in the
order of $o$. This is the evaluation of $x^T y$ in [higham2002accuracy], §3.1.

The order $o$ is existentially quantified. Therefore a theorem about `FloatingPoint.RoundsDot`
holds for every order in which an implementation accumulates the products. -/
def RoundsDot (m : RoundingModel K) (x y : ι → K) (s : K) : Prop :=
  ∃ (o : List ι) (p : ι → K), o.Nodup ∧ (∀ i, i ∈ o) ∧ (∀ i, m.Rounds (x i * y i) (p i)) ∧
    RoundsSum m (o.map p) s

/-- One direction of `FloatingPoint.roundsDot_comp_equiv_iff`: the order and the rounded products
are carried along the bijection. -/
private theorem roundsDot_of_comp_equiv {κ : Type*} {m : RoundingModel K} (e : κ ≃ ι)
    {x y : ι → K} {s : K} (h : RoundsDot m (x ∘ e) (y ∘ e) s) : RoundsDot m x y s := by
  obtain ⟨o, p, ho, hfull, hp, hsum⟩ := h
  refine ⟨o.map e, p ∘ e.symm, ho.map e.injective, fun i => ?_, fun i => ?_, ?_⟩
  · exact List.mem_map.2 ⟨e.symm i, hfull _, e.apply_symm_apply i⟩
  · simpa using hp (e.symm i)
  · rwa [List.map_map, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- Let $e \colon \kappa \to \iota$ be a bijection. A value $s$ is a computed inner product of
$x \circ e$ and $y \circ e$ if and only if it is a computed inner product of $x$ and $y$. The
order of summation is carried along $e$. -/
theorem roundsDot_comp_equiv_iff {κ : Type*} {m : RoundingModel K} (e : κ ≃ ι) {x y : ι → K}
    {s : K} : RoundsDot m (x ∘ e) (y ∘ e) s ↔ RoundsDot m x y s := by
  refine ⟨roundsDot_of_comp_equiv e, fun h => roundsDot_of_comp_equiv e.symm ?_⟩
  have hx : (x ∘ e) ∘ e.symm = x := by ext; simp
  have hy : (y ∘ e) ∘ e.symm = y := by ext; simp
  rwa [hx, hy]

/-- The product form of a running sum over a list of $k$ distinct indices: the start and every term
carry a factor $1 + \theta$ with $|\theta| \le (1 + u)^k - 1$. -/
private theorem exists_eq_of_roundsSumFrom_map {m : RoundingModel K} {l : List ι} (hl : l.Nodup)
    {v : ι → K} {a t : K} (h : RoundsSumFrom m a (l.map v) t) :
    ∃ (φ : K) (θ : ι → K), t = a * (1 + φ) + (l.map fun i => v i * (1 + θ i)).sum ∧
      |φ| ≤ (1 + m.u) ^ l.length - 1 ∧ ∀ i ∈ l, |θ i| ≤ (1 + m.u) ^ l.length - 1 := by
  classical
  induction l generalizing a with
  | nil =>
    cases h
    exact ⟨0, 0, by simp, by simp, by simp⟩
  | cons i l ih =>
    rcases List.nodup_cons.1 hl with ⟨hi, hl'⟩
    rcases h with _ | ⟨ht, hr⟩
    obtain ⟨φ, θ, rfl, hφ, hθ⟩ := ih hl' hr
    obtain ⟨δ, hδ, hδt⟩ := ht.exists_delta
    have hψ := abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one hφ hδ
    have hmono : (1 + m.u) ^ l.length - 1 ≤ (1 + m.u) ^ (l.length + 1) - 1 := by
      have := pow_le_pow_right₀ (by linarith [m.u_nonneg] : (1 : K) ≤ 1 + m.u)
        (by omega : l.length ≤ l.length + 1)
      linarith
    refine ⟨(1 + φ) * (1 + δ) - 1, Function.update θ i ((1 + φ) * (1 + δ) - 1), ?_, hψ,
      fun j hj => ?_⟩
    · rw [List.map_cons, List.sum_cons, Function.update_self]
      have hmap : (l.map fun j => v j * (1 + Function.update θ i ((1 + φ) * (1 + δ) - 1) j))
          = l.map fun j => v j * (1 + θ j) :=
        List.map_congr_left fun j hj => by
          rw [Function.update_of_ne fun (e : j = i) => hi (e ▸ hj)]
      rw [hmap, hδt]
      ring
    · rcases List.mem_cons.1 hj with rfl | hj
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : j = i) => hi (e ▸ hj)]
        exact (hθ j hj).trans hmono

/-- Let $o$ be a list of $k$ distinct indices, and let $f \colon \iota \to K$ and $c \in K$. If $t$
results from the addition of the terms $f_j$, $j \in o$, to $c$ in the order of $o$, with one
rounding per addition, then there are $\varphi \in K$ and $\theta \colon \iota \to K$ with
$$t = c (1 + \varphi) + \sum_{j \in o} f_j (1 + \theta_j), \qquad |\varphi| \le (1 + u)^k - 1,
  \quad |\theta_j| \le (1 + u)^k - 1 \ (j \in o).$$
No hypothesis on $ku$ is needed. This is the product form (3.2) of [higham2002accuracy] for a
running sum that starts from a partial sum, with the sharp constant $(1 + u)^k - 1$.

`FloatingPoint.exists_roundsSumFrom_map_eq_add_sum` is the form with the constant $\gamma_k$. -/
theorem exists_roundsSumFrom_map_eq_add_sum_one_add_pow [DecidableEq ι] {m : RoundingModel K}
    {o : List ι} (hnd : o.Nodup) {f : ι → K} {c t : K} (h : RoundsSumFrom m c (o.map f) t) :
    ∃ (φ : K) (θ : ι → K), |φ| ≤ (1 + m.u) ^ o.length - 1 ∧
      (∀ j ∈ o, |θ j| ≤ (1 + m.u) ^ o.length - 1) ∧
      t = c * (1 + φ) + ∑ j ∈ o.toFinset, f j * (1 + θ j) := by
  obtain ⟨φ, θ, rfl, hφ, hθ⟩ := exists_eq_of_roundsSumFrom_map hnd h
  exact ⟨φ, θ, hφ, hθ, by rw [List.sum_toFinset _ hnd]⟩

/-- Let $o$ be a list of $k$ distinct indices with $ku < 1$, and let $f \colon \iota \to K$ and
$c \in K$. If $t$ results from the addition of the terms $f_j$, $j \in o$, to $c$ in the order
of $o$, with one rounding per addition, then there are $\varphi \in K$ and
$\theta \colon \iota \to K$ with
$$t = c (1 + \varphi) + \sum_{j \in o} f_j (1 + \theta_j), \qquad |\varphi| \le \gamma_k, \quad
  |\theta_j| \le \gamma_k \ (j \in o).$$

The computed result $t$ itself is not perturbed. A later operation on the sum, such as a
subtraction or a division, needs this form. -/
theorem exists_roundsSumFrom_map_eq_add_sum [DecidableEq ι] {m : RoundingModel K} {c t : K}
    {f : ι → K} {o : List ι} (hnd : o.Nodup) (h : RoundsSumFrom m c (o.map f) t)
    (hlu : ((o.length : ℕ) : K) * m.u < 1) :
    ∃ (φ : K) (θ : ι → K), |φ| ≤ gamma m.u o.length ∧ (∀ j ∈ o, |θ j| ≤ gamma m.u o.length) ∧
      t = c * (1 + φ) + ∑ j ∈ o.toFinset, f j * (1 + θ j) := by
  obtain ⟨φ, θ, hφ, hθ, heq⟩ := exists_roundsSumFrom_map_eq_add_sum_one_add_pow hnd h
  have hγ := one_add_pow_sub_one_le_gamma m.u_nonneg hlu
  exact ⟨φ, θ, hφ.trans hγ, fun j hj => (hθ j hj).trans hγ, heq⟩

/-! ### Running differences -/

/-- Let $o$ be a list of indices, let $a, b \colon \iota \to K$ and let $c \in K$. A value $t$ is a
computed **running difference** $c - \sum_{r \in o} a_r b_r$ if there are admissible roundings
$p_r$ of the products $a_r b_r$, $r \in o$, such that $t$ results from the addition of the terms
$-p_r$ to $c$ in the order of $o$, with one rounding per addition. This is the evaluation in
[higham2002accuracy], Lemma 8.4.

This relation computes the entries in the substitutions and factorizations
`FloatingPoint.RoundsForwardSubst`, `FloatingPoint.RoundsLU`, `FloatingPoint.RoundsCholesky`,
`FloatingPoint.RoundsLDL` and `FloatingPoint.RoundsCholeskyDiv`. Over a list of distinct
indices, the results of the program `FloatingPoint.runningDiff` are exactly the values that
satisfy it (`FloatingPoint.mem_run_runningDiff_iff`). -/
def RoundsRunningDiff (m : RoundingModel K) (o : List ι) (a b : ι → K) (c t : K) : Prop :=
  ∃ p : ι → K, (∀ r ∈ o, m.Rounds (a r * b r) (p r)) ∧ RoundsSumFrom m c (o.map fun r => -p r) t

/-- A running difference over $o$ depends on $a_r$ and $b_r$ only for $r \in o$: if $a'_r = a_r$ and
$b'_r = b_r$ for every $r \in o$, then a computed running difference for $a, b$ is one for
$a', b'$. -/
theorem RoundsRunningDiff.congr {m : RoundingModel K} {o : List ι} {a a' b b' : ι → K} {c t : K}
    (h : RoundsRunningDiff m o a b c t) (ha : ∀ r ∈ o, a' r = a r) (hb : ∀ r ∈ o, b' r = b r) :
    RoundsRunningDiff m o a' b' c t := by
  obtain ⟨p, hp, hs⟩ := h
  exact ⟨p, fun r hr => by rw [ha r hr, hb r hr]; exact hp r hr, hs⟩

/-- **One more term of a running difference.** Let $t$ be a computed running difference
$c - \sum_{r \in o} a_r b_r$, and let $x$ be an index that is not in $o$. If $q$ is an
admissible rounding of $a_x b_x$ and $s$ is an admissible rounding of $t - q$, then $s$ is a
computed running difference over the list $o$ followed by $x$. -/
theorem RoundsRunningDiff.append_singleton {m : RoundingModel K} {o : List ι}
    {a b : ι → K} {c t : K} (h : RoundsRunningDiff m o a b c t) {x : ι} (hx : x ∉ o) {q s : K}
    (hq : m.Rounds (a x * b x) q) (hs : m.Rounds (t - q) s) :
    RoundsRunningDiff m (o ++ [x]) a b c s := by
  classical
  obtain ⟨p, hp, ht⟩ := h
  refine ⟨Function.update p x q, fun r hr => ?_, ?_⟩
  · rcases List.mem_append.1 hr with hr | hr
    · rw [Function.update_of_ne fun (e : r = x) => hx (e ▸ hr)]
      exact hp r hr
    · rw [List.mem_singleton.1 hr, Function.update_self]
      exact hq
  · rw [List.map_append, List.map_singleton, Function.update_self]
    have hmap : (o.map fun r => -Function.update p x q r) = o.map fun r => -p r :=
      List.map_congr_left fun r hr => by
        rw [Function.update_of_ne fun (e : r = x) => hx (e ▸ hr)]
    rw [hmap, roundsSumFrom_append_singleton]
    exact ⟨t, ht, by rw [← sub_eq_add_neg]; exact hs⟩

/-- In the exact model `FloatingPoint.RoundingModel.exact`, $t$ is a computed running difference
over $o$ if and only if $t = c - \sum_{r \in o} a_r b_r$, with the sum taken along the list $o$. -/
theorem roundsRunningDiff_exact_iff {o : List ι} {a b : ι → K} {c t : K} :
    RoundsRunningDiff (RoundingModel.exact K) o a b c t ↔
      t = c - (o.map fun r => a r * b r).sum := by
  have hneg : ∀ q : ι → K, (o.map fun r => -q r).sum = -(o.map q).sum := fun q => by
    rw [List.sum_neg, List.map_map]
    rfl
  constructor
  · rintro ⟨p, hp, hs⟩
    rw [roundsSumFrom_exact_iff.1 hs, hneg, ← sub_eq_add_neg]
    exact congrArg _ (congrArg _
      (List.map_congr_left fun r hr => RoundingModel.exact_rounds_iff.1 (hp r hr)))
  · intro h
    refine ⟨fun r => a r * b r, fun _ _ => RoundingModel.exact_rounds_iff.2 rfl,
      roundsSumFrom_exact_iff.2 ?_⟩
    rw [h, hneg, ← sub_eq_add_neg]

/-- In the exact model, a computed running difference over a list $o$ of distinct indices is
$c - \sum_{r} a_r b_r$, with the sum over the finite set of the entries of $o$. -/
theorem RoundsRunningDiff.eq_of_exact [DecidableEq ι] {o : List ι} (hnd : o.Nodup) {a b : ι → K}
    {c t : K} (h : RoundsRunningDiff (RoundingModel.exact K) o a b c t) :
    t = c - ∑ r ∈ o.toFinset, a r * b r := by
  rw [roundsRunningDiff_exact_iff.1 h, List.sum_toFinset _ hnd]

variable [Fintype ι]

/-- Let $\iota$ be a finite index set with $n$ elements, and let $u < 1$ and $nu < 1$. A computed
inner product $s$ of $x, y \colon \iota \to K$ satisfies
$$|s - x^T y| \le \gamma_n |x|^T |y|,$$
whatever the order of summation. This is (3.4) of [higham2002accuracy]. -/
theorem abs_sub_le_of_roundsDot {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ι : K) * m.u < 1) {x y : ι → K} {s : K} (h : RoundsDot m x y s) :
    |s - x ⬝ᵥ y| ≤ gamma m.u (Fintype.card ι) * (|x| ⬝ᵥ |y|) := by
  classical
  obtain ⟨o, p, hnodup, hfull, hp, hsum⟩ := h
  have hdotxy : x ⬝ᵥ y = ∑ i, x i * y i := rfl
  have hdotabs : |x| ⬝ᵥ |y| = ∑ i, |x i| * |y i| := rfl
  have huniv : o.toFinset = (univ : Finset ι) :=
    Finset.eq_univ_iff_forall.2 fun i => List.mem_toFinset.2 (hfull i)
  have hlen : o.length = Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hnodup, huniv, Finset.card_univ]
  have hD0 : (0 : K) ≤ ∑ i, |x i| * |y i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpi : ∀ i, |p i - x i * y i| ≤ m.u * (|x i| * |y i|) := fun i => by
    have h := m.abs_sub_le (hp i)
    rwa [abs_mul] at h
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hzero | hpos
  · have hempty : IsEmpty ι := Fintype.card_eq_zero_iff.1 hzero
    rcases o with _ | ⟨i₀, o'⟩
    · simp only [List.map_nil, roundsSum_nil] at hsum
      simp [hsum, hdotxy, hdotabs]
    · exact (hempty.false i₀).elim
  · obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
    have hcast : ((n + 1 : ℕ) : K) * m.u = (n : K) * m.u + m.u := by push_cast; ring
    have hnu : ((n : ℕ) : K) * m.u < 1 := by
      rw [hn, hcast] at hcard; linarith [m.u_nonneg]
    have hgn : 0 ≤ gamma m.u n := gamma_nonneg m.u_nonneg hnu
    -- the sums over the order `o` are the sums over the index type
    have hmapabs : (o.map p).map (|·|) = o.map fun i => |p i| := by
      simp [List.map_map, Function.comp_def]
    have hsumeq : (o.map p).sum = ∑ i, p i := by rw [← List.sum_toFinset p hnodup, huniv]
    have habs : ((o.map p).map (|·|)).sum = ∑ i, |p i| := by
      rw [hmapabs, ← List.sum_toFinset (fun i => |p i|) hnodup, huniv]
    -- the error of the recursive summation of the rounded products
    have hbound := abs_sub_le_of_roundsSum hu hsum
      (by rw [List.length_map, hlen, hn, Nat.add_sub_cancel]; exact hnu)
    rw [List.length_map, hlen, hn, Nat.add_sub_cancel, hsumeq, habs] at hbound
    -- the error of the rounded products themselves
    have hprod : |∑ i, p i - x ⬝ᵥ y| ≤ m.u * ∑ i, |x i| * |y i| := by
      have hsplit : ∑ i, p i - x ⬝ᵥ y = ∑ i, (p i - x i * y i) := by
        rw [hdotxy, ← Finset.sum_sub_distrib]
      calc |∑ i, p i - x ⬝ᵥ y| = |∑ i, (p i - x i * y i)| := by rw [hsplit]
        _ ≤ ∑ i, |p i - x i * y i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, m.u * (|x i| * |y i|) := Finset.sum_le_sum fun i _ => hpi i
        _ = m.u * ∑ i, |x i| * |y i| := by rw [← Finset.mul_sum]
    have hsize : ∑ i, |p i| ≤ (1 + m.u) * ∑ i, |x i| * |y i| := by
      have hbd : ∀ i ∈ (univ : Finset ι), |p i| ≤ (1 + m.u) * (|x i| * |y i|) := fun i _ => by
        have h1 : |p i| ≤ |p i - x i * y i| + |x i * y i| := by
          simpa using abs_add_le (p i - x i * y i) (x i * y i)
        rw [abs_mul] at h1
        nlinarith [hpi i]
      calc ∑ i, |p i| ≤ ∑ i, (1 + m.u) * (|x i| * |y i|) := Finset.sum_le_sum hbd
        _ = (1 + m.u) * ∑ i, |x i| * |y i| := by rw [← Finset.mul_sum]
    have hstep : gamma m.u n * (1 + m.u) + m.u ≤ gamma m.u (n + 1) :=
      gamma_mul_one_add_add_le m.u_nonneg hu (by rw [← hn]; exact hcard)
    have hsplit : |s - x ⬝ᵥ y| ≤ |s - ∑ i, p i| + |∑ i, p i - x ⬝ᵥ y| := by
      have harg : s - x ⬝ᵥ y = s - ∑ i, p i + (∑ i, p i - x ⬝ᵥ y) := by ring
      rw [harg]
      exact abs_add_le _ _
    rw [hn, hdotabs]
    refine hsplit.trans ?_
    calc |s - ∑ i, p i| + |∑ i, p i - x ⬝ᵥ y|
        ≤ gamma m.u n * ((1 + m.u) * ∑ i, |x i| * |y i|) + m.u * ∑ i, |x i| * |y i| :=
          add_le_add (hbound.trans (mul_le_mul_of_nonneg_left hsize hgn)) hprod
      _ = (gamma m.u n * (1 + m.u) + m.u) * ∑ i, |x i| * |y i| := by ring
      _ ≤ gamma m.u (n + 1) * ∑ i, |x i| * |y i| := mul_le_mul_of_nonneg_right hstep hD0

/-- Let $\iota$ be finite, let $c \ge 0$, let $a, b \colon \iota \to K$, and let $r \in K$ with
$|r| \le c \sum_i |a_i| |b_i|$. Then there is $d \colon \iota \to K$ with $|d_i| \le c |a_i|$
for every $i$ and
$$\sum_i d_i b_i = r.$$
This turns a forward error bound into a backward one: the residual $r$ is the effect of a
componentwise relative perturbation of $a$ of size $c$. -/
theorem _root_.Fintype.exists_sum_mul_eq_of_abs_le {c r : K} (hc : 0 ≤ c) {a b : ι → K}
    (h : |r| ≤ c * ∑ i, |a i| * |b i|) :
    ∃ d : ι → K, (∀ i, |d i| ≤ c * |a i|) ∧ ∑ i, d i * b i = r := by
  have hS0 : (0 : K) ≤ ∑ i, |a i| * |b i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsign : ∀ i, |b i| / b i * b i = |b i| := fun i => by
    rcases eq_or_ne (b i) 0 with hb | hb
    · simp [hb]
    · rw [div_mul_cancel₀ _ hb]
  rcases eq_or_lt_of_le (mul_nonneg hc hS0) with hcz | hcpos
  · refine ⟨0, fun i => by simpa using mul_nonneg hc (abs_nonneg (a i)), ?_⟩
    have hr : |r| ≤ 0 := by rw [← hcz] at h; exact h
    simp [abs_nonpos_iff.1 hr]
  · obtain ⟨θ, hθ, hθr⟩ : ∃ θ : K, |θ| ≤ 1 ∧ c * θ * ∑ i, |a i| * |b i| = r := by
      refine ⟨r / (c * ∑ i, |a i| * |b i|), ?_, ?_⟩
      · rw [abs_div, abs_of_pos hcpos, div_le_one hcpos]
        exact h
      · have hne : c * (∑ i, |a i| * |b i|) ≠ 0 := ne_of_gt hcpos
        have hrw : c * (r / (c * ∑ i, |a i| * |b i|)) * ∑ i, |a i| * |b i|
            = c * (∑ i, |a i| * |b i|) * (r / (c * ∑ i, |a i| * |b i|)) := by ring
        rw [hrw, mul_div_cancel₀ _ hne]
    refine ⟨fun i => c * θ * |a i| * (|b i| / b i), fun i => ?_, ?_⟩
    · have hq : |(|b i| / b i)| ≤ 1 := by
        rcases eq_or_ne (b i) 0 with hb | hb
        · simp [hb]
        · rw [abs_div, abs_abs, div_self (abs_ne_zero.2 hb)]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_abs]
      calc c * |θ| * |a i| * |(|b i| / b i)|
          ≤ c * 1 * |a i| * 1 := by gcongr
        _ = c * |a i| := by ring
    · have hterm : ∀ i : ι, c * θ * |a i| * (|b i| / b i) * b i = c * θ * (|a i| * |b i|) :=
        fun i => by rw [mul_assoc (c * θ * |a i|), hsign i]; ring
      calc ∑ i, c * θ * |a i| * (|b i| / b i) * b i
          = ∑ i, c * θ * (|a i| * |b i|) := Finset.sum_congr rfl fun i _ => hterm i
        _ = c * θ * ∑ i, |a i| * |b i| := by rw [Finset.mul_sum]
        _ = r := hθr

/-- Let $\iota$ be a finite index set with $n$ elements, and let $u < 1$ and $nu < 1$. If $s$ is a
computed inner product of $x, y \colon \iota \to K$, then there is $\Delta x \colon \iota \to K$
with $|\Delta x_i| \le \gamma_n |x_i|$ for every $i$ and
$$s = (x + \Delta x)^T y.$$
This is the backward form (3.5) of [higham2002accuracy] of the inner-product bound. -/
theorem exists_roundsDot_eq_dotProduct_add {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ι : K) * m.u < 1) {x y : ι → K} {s : K} (h : RoundsDot m x y s) :
    ∃ dx : ι → K, (∀ i, |dx i| ≤ gamma m.u (Fintype.card ι) * |x i|) ∧ s = (x + dx) ⬝ᵥ y := by
  have hbound := abs_sub_le_of_roundsDot hu hcard h
  obtain ⟨d, hd, hsum⟩ :=
    Fintype.exists_sum_mul_eq_of_abs_le (c := gamma m.u (Fintype.card ι)) (r := s - x ⬝ᵥ y) (a := x)
      (b := y) (gamma_nonneg m.u_nonneg hcard) hbound
  refine ⟨d, hd, ?_⟩
  have hexp : (x + d) ⬝ᵥ y = x ⬝ᵥ y + ∑ i, d i * y i := by
    rw [add_dotProduct]
    rfl
  rw [hexp, hsum]
  ring

/-- Let $\iota$ be a finite index set with $n$ elements, let $u < 1$, and let $k$ be a natural
number with $(2k + n) u < 1$. If $\hat v_i$ is a relative perturbation of order $k$ of $v_i$ for
every $i$ (that is, $\hat v_i = v_i (1 + \theta_i)$ with $|\theta_i| \le \gamma_k$), then a
computed inner product $s$ of $\hat v$ with itself is a relative perturbation of order $2k + n$
of $v^T v$: $s = v^T v (1 + \theta)$ with $|\theta| \le \gamma_{2k + n}$. -/
theorem isRelPert_of_roundsDot_self {m : RoundingModel K} (hu : m.u < 1) {k : ℕ}
    (hk : ((2 * k + Fintype.card ι : ℕ) : K) * m.u < 1) {v vhat : ι → K}
    (hv : ∀ i, IsRelPert m.u k (v i) (vhat i)) {s : K} (hs : RoundsDot m vhat vhat s) :
    IsRelPert m.u (2 * k + Fintype.card ι) (v ⬝ᵥ v) s := by
  have hu0 := m.u_nonneg
  have hlt : ∀ j, j ≤ 2 * k + Fintype.card ι → ((j : ℕ) : K) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hk
  obtain ⟨dx, hdx, rfl⟩ := exists_roundsDot_eq_dotProduct_add hu (hlt _ (by omega)) hs
  have hterm : ∀ i, IsRelPert m.u (2 * k + Fintype.card ι) (v i * v i)
      ((vhat i + dx i) * vhat i) := by
    intro i
    have h1 : IsRelPert m.u (k + k) (v i * v i) (vhat i * vhat i) :=
      (hv i).mul hu0 (hlt _ (by omega)) (hv i)
    have h2 : IsRelPert m.u (Fintype.card ι) (vhat i * vhat i) ((vhat i + dx i) * vhat i) := by
      refine isRelPert_of_abs_sub_le (gamma_nonneg hu0 (hlt _ (by omega))) ?_
      rw [show (vhat i + dx i) * vhat i - vhat i * vhat i = dx i * vhat i by ring, abs_mul,
        abs_mul]
      exact (mul_le_mul_of_nonneg_right (hdx i) (abs_nonneg _)).trans_eq (by ring)
    have := h1.trans hu0 (hlt _ (by omega)) h2
    rwa [show k + k + Fintype.card ι = 2 * k + Fintype.card ι by ring] at this
  exact IsRelPert.sum_of_nonneg Finset.univ (gamma_nonneg hu0 (hlt _ le_rfl))
    (fun i _ => mul_self_nonneg _) fun i _ => hterm i

/-- Let $\iota$ be a finite index set with $n$ elements. If $s$ is a computed inner product of
$x, y \colon \iota \to K$, then there is $\theta \colon \iota \to K$ with
$$s = \sum_i x_i y_i (1 + \theta_i), \qquad |\theta_i| \le (1 + u)^n - 1 \text{ for every } i,$$
whatever the order of summation. No hypothesis on $nu$ is needed. This is (2.7.10) of
[golub2013matrix] and (3.2) of [higham2002accuracy]. -/
theorem exists_eq_sum_mul_one_add_of_roundsDot {m : RoundingModel K} {x y : ι → K} {s : K}
    (h : RoundsDot m x y s) :
    ∃ θ : ι → K, s = ∑ i, x i * y i * (1 + θ i) ∧
      ∀ i, |θ i| ≤ (1 + m.u) ^ Fintype.card ι - 1 := by
  classical
  obtain ⟨o, p, hnodup, hfull, hp, hsum⟩ := h
  have huniv : o.toFinset = (univ : Finset ι) :=
    Finset.eq_univ_iff_forall.2 fun i => List.mem_toFinset.2 (hfull i)
  have hlen : o.length = Fintype.card ι := by
    rw [← List.toFinset_card_of_nodup hnodup, huniv, Finset.card_univ]
  choose δ hδ hpδ using fun i => (hp i).exists_delta
  have hsumo : ∀ f : ι → K, ∑ i, f i = (o.map f).sum := fun f => by
    rw [← List.sum_toFinset f hnodup, huniv]
  cases o with
  | nil =>
    cases hsum
    exact ⟨0, by rw [hsumo]; simp, fun i => absurd (hfull i) List.not_mem_nil⟩
  | cons k o =>
    rcases List.nodup_cons.1 hnodup with ⟨hk, ho⟩
    obtain ⟨φ, θ, hs, hφ, hθ⟩ := exists_eq_of_roundsSumFrom_map ho hsum
    rw [List.length_cons] at hlen
    refine ⟨Function.update (fun j => (1 + θ j) * (1 + δ j) - 1) k ((1 + φ) * (1 + δ k) - 1),
      ?_, fun i => ?_⟩
    · rw [hsumo, List.map_cons, List.sum_cons, Function.update_self, hs]
      have hmap : (o.map fun j => x j * y j *
            (1 + Function.update (fun j => (1 + θ j) * (1 + δ j) - 1) k
              ((1 + φ) * (1 + δ k) - 1) j))
          = o.map fun j => p j * (1 + θ j) :=
        List.map_congr_left fun j hj => by
          rw [Function.update_of_ne fun (e : j = k) => hk (e ▸ hj), hpδ j]
          ring
      rw [hmap, hpδ k]
      ring
    · rw [← hlen]
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self]
        exact abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one hφ (hδ i)
      · rw [Function.update_of_ne hik]
        have hi : i ∈ o := (List.mem_cons.1 (hfull i)).resolve_left hik
        exact abs_one_add_mul_one_add_sub_one_le_one_add_pow_sub_one (hθ i hi) (hδ i)

/-- Let $\iota$ be a finite index set with $n$ elements. A computed inner product $s$ of
$x, y \colon \iota \to K$ satisfies
$$|s - x^T y| \le \bigl((1 + u)^n - 1\bigr) |x|^T |y|.$$
No hypothesis on $nu$ is needed.

This is the sharp bound behind (2.7.11) of [golub2013matrix]. With
`FloatingPoint.abs_prod_one_add_sub_one_le_of_mul_le`, it gives the bound
$1.01\, nu\, |x|^T |y|$ of the source when $nu \le 0.01$. -/
theorem abs_sub_le_one_add_pow_sub_one_of_roundsDot {m : RoundingModel K} {x y : ι → K} {s : K}
    (h : RoundsDot m x y s) :
    |s - x ⬝ᵥ y| ≤ ((1 + m.u) ^ Fintype.card ι - 1) * (|x| ⬝ᵥ |y|) := by
  obtain ⟨θ, rfl, hθ⟩ := exists_eq_sum_mul_one_add_of_roundsDot h
  set c := (1 + m.u) ^ Fintype.card ι - 1
  have hsub : ∑ i, x i * y i * (1 + θ i) - x ⬝ᵥ y = ∑ i, x i * y i * θ i := by
    rw [dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdot : |x| ⬝ᵥ |y| = ∑ i, |x i| * |y i| := rfl
  rw [hsub, hdot, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, mul_comm c]
  exact mul_le_mul_of_nonneg_left (hθ i) (by positivity)

/-! ### Matrix–vector and matrix–matrix products -/

variable {μ ν ρ : Type*}

/-- Let $A \in K^{\mu \times \nu}$ and $x \in K^\nu$. A vector $\hat y \in K^\mu$ is a **computed
matrix–vector product** $Ax$ if, for every $i$, $\hat y_i$ is a computed inner product of row
$i$ of $A$ with $x$. This is the evaluation in [higham2002accuracy], §3.5.

The order of summation can be different in each row. -/
def RoundsMulVec (m : RoundingModel K) (A : Matrix μ ν K) (x : ν → K) (yhat : μ → K) : Prop :=
  ∀ i, RoundsDot m (A i) x (yhat i)

/-- Let $A \in K^{\mu \times \nu}$ and $B \in K^{\nu \times \rho}$. A matrix
$C \in K^{\mu \times \rho}$ is a **computed matrix product** $AB$ if, for every $i$ and $j$,
$C_{ij}$ is a computed inner product of row $i$ of $A$ with column $j$ of $B$. -/
def RoundsMul (m : RoundingModel K) (A : Matrix μ ν K) (B : Matrix ν ρ K) (C : Matrix μ ρ K) :
    Prop :=
  ∀ i j, RoundsDot m (A i) (fun k => B k j) (C i j)

variable [Fintype ν]

/-- Let $\nu$ be a finite index set with $n$ elements, and let $u < 1$ and $nu < 1$. If $\hat y$ is
a computed matrix–vector product of $A \in K^{\mu \times \nu}$ and $x \in K^\nu$, then,
entrywise,
$$|\hat y - Ax| \le \gamma_n |A| |x|.$$
This is (3.12) of [higham2002accuracy].

The matrix $|A|$ is `Matrix.abs A`, and the order on vectors is the pointwise order. -/
theorem abs_sub_le_of_roundsMulVec {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {x : ν → K} {yhat : μ → K}
    (h : RoundsMulVec m A x yhat) :
    |yhat - A *ᵥ x| ≤ gamma m.u (Fintype.card ν) • (A.abs *ᵥ |x|) := by
  refine Pi.le_def.2 fun i => ?_
  have hi := abs_sub_le_of_roundsDot hu hcard (h i)
  have hlhs : |yhat - A *ᵥ x| i = |yhat i - A i ⬝ᵥ x| := rfl
  have hrhs : (gamma m.u (Fintype.card ν) • (A.abs *ᵥ |x|)) i
      = gamma m.u (Fintype.card ν) * (|A i| ⬝ᵥ |x|) := rfl
  rw [hlhs, hrhs]
  exact hi

/-- Let $\nu$ be a finite index set with $n$ elements, and let $u < 1$ and $nu < 1$. If $C$ is a
computed matrix product of $A \in K^{\mu \times \nu}$ and $B \in K^{\nu \times \rho}$, then,
entrywise,
$$|C - AB| \le \gamma_n |A| |B|.$$
This is (3.13) of [higham2002accuracy].

The inequality is `Matrix.EntrywiseLE`, and $|A|$ is `Matrix.abs A`. -/
theorem abs_sub_entrywiseLE_of_roundsMul {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {B : Matrix ν ρ K}
    {C : Matrix μ ρ K} (h : RoundsMul m A B C) :
    (C - A * B).abs ≤ₑ gamma m.u (Fintype.card ν) • (A.abs * B.abs) := by
  intro i j
  have hij := abs_sub_le_of_roundsDot hu hcard (h i j)
  have hlhs : (C - A * B).abs i j = |C i j - A i ⬝ᵥ fun k => B k j| := rfl
  have hrhs : (gamma m.u (Fintype.card ν) • (A.abs * B.abs)) i j
      = gamma m.u (Fintype.card ν) * (|A i| ⬝ᵥ fun k => |B k j|) := rfl
  rw [hlhs, hrhs]
  exact hij

/-- Let $\nu$ be a finite index set with $n$ elements, let $u < 1$ and $nu < 1$, and let $\hat y$ be
a computed matrix–vector product of $A$ and $x$. If $|x_j| \le c$ for every $j$, then for every
row $i$,
$$|\hat y_i - (Ax)_i| \le \gamma_n \Bigl(\sum_j |a_{ij}|\Bigr) c.$$
This is the bound $\|\hat y - Ax\|_\infty \le \gamma_n \|A\|_\infty \|x\|_\infty$, written
without norms, because the scalar field has an order but no norm. -/
theorem abs_sub_le_of_roundsMulVec_of_abs_le {m : RoundingModel K} (hu : m.u < 1)
    (hcard : (Fintype.card ν : K) * m.u < 1) {A : Matrix μ ν K} {x : ν → K} {yhat : μ → K}
    (h : RoundsMulVec m A x yhat) {c : K} (hx : ∀ j, |x j| ≤ c) (i : μ) :
    |yhat i - (A *ᵥ x) i| ≤ gamma m.u (Fintype.card ν) * ((∑ j, |A i j|) * c) := by
  have hrow : ∑ j, |A i j| * |x j| ≤ (∑ j, |A i j|) * c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg (A i j))
  have hi := abs_sub_le_of_roundsDot hu hcard (h i)
  have hlhs : |yhat i - (A *ᵥ x) i| = |yhat i - A i ⬝ᵥ x| := rfl
  have hdot : (|A i| : ν → K) ⬝ᵥ |x| = ∑ j, |A i j| * |x j| := rfl
  rw [hlhs]
  refine hi.trans ?_
  rw [hdot]
  exact mul_le_mul_of_nonneg_left hrow (gamma_nonneg m.u_nonneg hcard)

end FloatingPoint
