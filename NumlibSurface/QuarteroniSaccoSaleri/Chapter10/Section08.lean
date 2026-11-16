/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Interpolation

/-!
# Quarteroni, Sacco and Saleri, Section 10.8: The polynomial of best approximation

This module formalizes Section 10.8 of [quarteroni2000numerical]. For $f \in C^0([a, b])$, the
**polynomial of best approximation** $p_n^* \in \mathbb{P}_n$ is the polynomial that realizes $\|f -
p_n^*\|_\infty = \min_{p \in \mathbb{P}_n} \|f - p\|_\infty$ (10.47), also called the minimax
approximation, and $E_n^*(f) = \|f - p_n^*\|_\infty$ is its error. The section quotes three results
without proof. The Chebyshev equioscillation theorem (Property 10.1) says that $p_n^*$ exists and is
unique, and that $f - p_n^*$ takes the values $\pm E_n^*(f)$ with alternating signs at $n + 2$
points; as a consequence, $p_n^*$ interpolates $f$ at $n + 1$ points that interlace the alternation
points. The de la Vallée Poussin theorem (Property 10.2) says that an alternation of any competitor
bounds $E_n^*(f)$ from below. Finally, the interpolation error is compared with the best
approximation error through the Lebesgue constant: $\|f - \Pi_n f\|_\infty \le (1 + \Lambda_n)
E_n^*(f)$.

The proofs specialize `Numlib.Approximation.Chebyshev` on $X = [a, b]$, and the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem` of `Numlib.Analysis.Normed.Module.BestApprox` for the
interpolation projection `Lagrange.interpolateCLM`.

## Main definitions

* Equation (10.47), `QuarteroniSaccoSaleri.Chapter10.equation_10_47`: $p$ is a polynomial of best
  approximation of $f$ in $\mathbb{P}_n$ on $[a, b]$.
* Property 10.1, `QuarteroniSaccoSaleri.Chapter10.bestApproximationError`: the error of best
  approximation $E_n^*(f)$, the distance from $f$ to $\mathbb{P}_n$.

## Main results

* Equation (10.47), `QuarteroniSaccoSaleri.Chapter10.equation_10_47_iff`: $p$ is a polynomial of
  best approximation if and only if $p \in \mathbb{P}_n$ and $\|f - p\|_\infty$ is the minimum of
  $\|f - q\|_\infty$ over $q \in \mathbb{P}_n$.
* Property 10.1, `QuarteroniSaccoSaleri.Chapter10.bestApproximationError_eq`:
  $E_n^*(f) = \|f - p_n^*\|_\infty$.
* Property 10.1, `QuarteroniSaccoSaleri.Chapter10.property_10_1_existsUnique`: the polynomial of
  best approximation exists and is unique.
* Property 10.1, `QuarteroniSaccoSaleri.Chapter10.property_10_1_equioscillates`: $f - p_n^*$
  equioscillates at $n + 2$ points.
* Section 10.8, `QuarteroniSaccoSaleri.Chapter10.property_10_1_interpolates`: $p_n^*$ interpolates
  $f$ at $n + 1$ points $\tilde x_0 < \dots < \tilde x_n$ with $x_k < \tilde x_k < x_{k+1}$.
* Property 10.2, `QuarteroniSaccoSaleri.Chapter10.property_10_2`: the de la Vallée Poussin theorem.
* Section 10.8, `QuarteroniSaccoSaleri.Chapter10.interpolation_error_le_lebesgue`: $\|f - \Pi_n
  f\|_\infty \le (1 + \Lambda_n) E_n^*(f)$, where $\Lambda_n$ is the Lebesgue constant (8.11) of the
  nodes.

## Conventions

* Functions are elements of `C(Icc a b, ℝ)` with the maximum norm, the norm $\|\cdot\|_\infty$ of
  the book. The space $\mathbb{P}_n$ on $[a, b]$ is `polyLE (Icc a b) n`.
* Points $x_0 < \dots < x_{n+1}$ of $[a, b]$ are a strictly monotone family
  `x : Fin (n + 2) → Icc a b`.
* The interpolation operator $\Pi_n$ at nodes `x : Fin (n + 1) → Icc a b` is
  `Lagrange.interpolateCLM x`, and the Lagrange basis functions are $l_i$ = `Lagrange.basisCM x i`.
  The Lebesgue constant $\Lambda_n$ is the supremum over $[a, b]$ of the Lebesgue function
  $\sum_i |l_i|$.

## Implementation notes

* The polynomial of best approximation is the backbone predicate `IsBestApprox` for the subspace
  `polyLE (Icc a b) n`, and $E_n^*(f)$ is the distance `Metric.infDist f (polyLE (Icc a b) n)`.
* Property 10.1 is `existsUnique_isBestApprox_polyLE` with `IsBestApprox.equioscillates_of_polyLE`,
  and Property 10.2 is `le_infDist_of_alternates`. The norm of the interpolation operator is
  $\Lambda_n$ by `Lagrange.norm_interpolateCLM`.
* The interpolation property after Property 10.1 follows from the intermediate value theorem between
  consecutive alternation points. The backbone does not state it separately.
* Property 10.1 needs $a < b$: on an interval of one point the best approximation is not unique.
-/

open Set

namespace QuarteroniSaccoSaleri.Chapter10

variable {a b : ℝ} {n : ℕ}

/-! ### Equation (10.47): The polynomial of best approximation and its error -/

/-- **Equation (10.47)** of [quarteroni2000numerical]. Let $f \in C^0([a, b])$. A polynomial
$p_n^* \in \mathbb{P}_n$ is **the polynomial of best approximation** of $f$, or the minimax
approximation of $f$, if
$$\|f - p_n^*\|_\infty = \min_{p_n \in \mathbb{P}_n} \|f - p_n\|_\infty.$$

The definition is the backbone's `IsBestApprox` for the subspace `polyLE (Icc a b) n` of
`C(Icc a b, ℝ)`. The lemma `QuarteroniSaccoSaleri.Chapter10.equation_10_47_iff` writes out the
minimum. -/
def equation_10_47 (a b : ℝ) (n : ℕ) (f p : C(Icc a b, ℝ)) : Prop :=
  IsBestApprox (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) f p

/-- Supports equation (10.47). The polynomial $p$ is a polynomial of best approximation of $f$ if
and only if $p \in \mathbb{P}_n$ and $\|f - p\|_\infty$ is the least of the numbers
$\|f - q\|_\infty$ for $q \in \mathbb{P}_n$. -/
theorem equation_10_47_iff (f p : C(Icc a b, ℝ)) :
    equation_10_47 a b n f p ↔ p ∈ polyLE (Icc a b) n ∧
      IsLeast (Set.range fun q : polyLE (Icc a b) n => ‖f - (q : C(Icc a b, ℝ))‖) ‖f - p‖ := by
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨hp, ⟨⟨p, hp⟩, rfl⟩, by rintro _ ⟨q, rfl⟩; exact hmin q q.2⟩
  · rintro ⟨hp, -, hmin⟩
    exact ⟨hp, fun q hq => hmin ⟨⟨q, hq⟩, rfl⟩⟩

/-- **Property 10.1** of [quarteroni2000numerical], the error $E_n^*(f)$. For $f \in C^0([a, b])$,
the **error of best approximation** of $f$ from $\mathbb{P}_n$ is the distance
$$E_n^*(f) = \inf_{p \in \mathbb{P}_n} \|f - p\|_\infty.$$

The lemma `QuarteroniSaccoSaleri.Chapter10.bestApproximationError_eq` identifies it with
$\|f - p_n^*\|_\infty$, the form of the book, for the polynomial of best approximation $p_n^*$. -/
noncomputable def bestApproximationError (a b : ℝ) (n : ℕ) (f : C(Icc a b, ℝ)) : ℝ :=
  Metric.infDist f (polyLE (Icc a b) n : Set C(Icc a b, ℝ))

/-- **Property 10.1** of [quarteroni2000numerical], the error $E_n^*(f)$. If $p_n^*$ is a polynomial
of best approximation of $f \in C^0([a, b])$, then $E_n^*(f) = \|f - p_n^*\|_\infty$. -/
theorem bestApproximationError_eq {f p : C(Icc a b, ℝ)} (hp : equation_10_47 a b n f p) :
    bestApproximationError a b n f = ‖f - p‖ :=
  hp.norm_sub_eq_infDist.symm

/-! ### Property 10.1: The Chebyshev equioscillation theorem -/

/-- **Property 10.1** of [quarteroni2000numerical] (Chebyshev equioscillation theorem), existence
and uniqueness. Let $a < b$, $f \in C^0([a, b])$ and $n \ge 0$. Then the polynomial of best
approximation $p_n^*$ of $f$ exists and is unique.

The proof specializes the backbone's `existsUnique_isBestApprox_polyLE`. -/
theorem property_10_1_existsUnique (hab : a < b) (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃! p, equation_10_47 a b n f p :=
  have : Infinite (Icc a b) := Set.Icc.infinite hab
  existsUnique_isBestApprox_polyLE n f

/-- **Property 10.1** of [quarteroni2000numerical] (Chebyshev equioscillation theorem),
equioscillation. Let $a < b$, and let $p_n^*$ be the polynomial of best approximation of
$f \in C^0([a, b])$. Then there are $n + 2$ points $x_0 < x_1 < \dots < x_{n+1}$ in $[a, b]$ and
a sign $\sigma \in \{1, -1\}$ such that
$$f(x_j) - p_n^*(x_j) = \sigma (-1)^j E_n^*(f), \qquad j = 0, \dots, n + 1.$$
The sign $\sigma$ depends on $f$ and $n$.

The proof specializes the backbone's `IsBestApprox.equioscillates_of_polyLE`. The backbone also
proves the converse, `isBestApprox_of_equioscillates`, which the book does not state. -/
theorem property_10_1_equioscillates (hab : a < b) {f p : C(Icc a b, ℝ)}
    (hp : equation_10_47 a b n f p) :
    ∃ (σ : ℝ) (x : Fin (n + 2) → Icc a b), (σ = 1 ∨ σ = -1) ∧
      StrictMono (fun i => (x i : ℝ)) ∧
      ∀ j : Fin (n + 2),
        f (x j) - p (x j) = σ * (-1) ^ (j : ℕ) * bestApproximationError a b n f := by
  have : Infinite (Icc a b) := Set.Icc.infinite hab
  obtain ⟨σ, x, hσ, hmono, hval⟩ := hp.equioscillates_of_polyLE
  refine ⟨σ, x, hσ, hmono, fun j => ?_⟩
  rw [bestApproximationError_eq hp]
  simpa using hval j

/-- **Section 10.8** of [quarteroni2000numerical], the consequence of Property 10.1. Let $p_n^*$ be
the polynomial of best approximation of $f \in C^0([a, b])$, and let $x_0 < \dots < x_{n+1}$ be
points of $[a, b]$ and $\sigma \in \{1, -1\}$ with
$f(x_j) - p_n^*(x_j) = \sigma (-1)^j E_n^*(f)$ for all $j$, as in Property 10.1. Then there are
$n + 1$ points $\tilde x_0 < \tilde x_1 < \dots < \tilde x_n$ in $[a, b]$, with
$x_k < \tilde x_k < x_{k+1}$ for $k = 0, \dots, n$, such that
$$p_n^*(\tilde x_j) = f(\tilde x_j), \qquad j = 0, 1, \dots, n.$$
So the polynomial of best approximation is a polynomial of degree $n$ that interpolates $f$ at
$n + 1$ unknown nodes.

The proof applies the intermediate value theorem to $f - p_n^*$ between two consecutive
alternation points, where it takes the values $\pm E_n^*(f)$. When $E_n^*(f) = 0$, $f$ is the
polynomial $p_n^*$ and any point between two alternation points serves. Unlike Property 10.1,
the statement needs no hypothesis $a < b$, because the alternation points are already $n + 2$
distinct points of $[a, b]$. -/
theorem property_10_1_interpolates {f p : C(Icc a b, ℝ)}
    (hp : equation_10_47 a b n f p) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : Fin (n + 2) → Icc a b}
    (hmono : StrictMono fun i => (x i : ℝ))
    (hval : ∀ j : Fin (n + 2),
      f (x j) - p (x j) = σ * (-1) ^ (j : ℕ) * bestApproximationError a b n f) :
    ∃ y : Fin (n + 1) → Icc a b, StrictMono (fun i => (y i : ℝ)) ∧
      (∀ k : Fin (n + 1), (x k.castSucc : ℝ) < y k ∧ (y k : ℝ) < x k.succ) ∧
      ∀ j : Fin (n + 1), p (y j) = f (y j) := by
  have hlt : ∀ k : Fin (n + 1), (x k.castSucc : ℝ) < x k.succ := fun k =>
    hmono Fin.castSucc_lt_succ
  have hE : bestApproximationError a b n f = ‖f - p‖ := bestApproximationError_eq hp
  -- a root of `f - p` strictly between two consecutive alternation points
  have hroot : ∀ k : Fin (n + 1), ∃ z : Icc a b,
      (x k.castSucc : ℝ) < z ∧ (z : ℝ) < x k.succ ∧ (f - p) z = 0 := by
    intro k
    rcases eq_or_lt_of_le (norm_nonneg (f - p)) with h0 | hpos
    · -- `f = p`: the midpoint serves
      have hfp : f - p = 0 := norm_eq_zero.mp h0.symm
      have hmem : ((x k.castSucc : ℝ) + x k.succ) / 2 ∈ Icc a b :=
        ⟨by linarith [(x k.castSucc).2.1, (x k.succ).2.1],
          by linarith [(x k.castSucc).2.2, (x k.succ).2.2]⟩
      refine ⟨⟨((x k.castSucc : ℝ) + x k.succ) / 2, hmem⟩, ?_, ?_, ?_⟩
      · dsimp only
        linarith [hlt k]
      · dsimp only
        linarith [hlt k]
      · rw [hfp]
        rfl
    · refine ContinuousMap.exists_mem_Ioo_eq_zero_of_mul_neg (hlt k) ?_
      have hsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have hpow : ((-1 : ℝ) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by
        rw [← mul_pow]
        norm_num
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hval k.castSucc, hval k.succ, hE,
        Fin.val_castSucc, Fin.val_succ, pow_succ]
      have hprod : σ * (-1) ^ (k : ℕ) * ‖f - p‖ * (σ * ((-1) ^ (k : ℕ) * -1) * ‖f - p‖)
          = -((σ * σ) * ((-1) ^ (k : ℕ) * (-1) ^ (k : ℕ)) * (‖f - p‖ * ‖f - p‖)) := by ring
      rw [hprod, hsq, hpow, one_mul, one_mul, neg_lt_zero]
      exact mul_pos hpos hpos
  choose y hy₁ hy₂ hy₃ using hroot
  refine ⟨y, ?_, fun k => ⟨hy₁ k, hy₂ k⟩, fun j => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    calc (y i.castSucc : ℝ) < x i.castSucc.succ := hy₂ i.castSucc
      _ = x i.succ.castSucc := by rw [Fin.succ_castSucc]
      _ < y i.succ := hy₁ i.succ
  · have h := hy₃ j
    rw [ContinuousMap.sub_apply, sub_eq_zero] at h
    exact h.symm

/-! ### Property 10.2: The de la Vallée Poussin theorem -/

/-- **Property 10.2** of [quarteroni2000numerical] (de la Vallée Poussin theorem). Let $n \ge 0$,
let $f \in C^0([a, b])$, and let $x_0 < x_1 < \dots < x_{n+1}$ be $n + 2$ points in $[a, b]$. If
there is a polynomial $q_n$ of degree at most $n$ such that
$$f(x_j) - q_n(x_j) = (-1)^j e_j, \qquad j = 0, 1, \dots, n + 1,$$
where all the $e_j$ are nonzero and have the same sign, then
$$\min_{0 \le j \le n+1} |e_j| \le E_n^*(f).$$

The proof specializes the backbone's `le_infDist_of_alternates` with
$\varepsilon = \min_j |e_j|$ and $\sigma$ the common sign. -/
theorem property_10_2 {f q : C(Icc a b, ℝ)} (hq : q ∈ polyLE (Icc a b) n)
    {x : Fin (n + 2) → Icc a b} (hmono : StrictMono fun i => (x i : ℝ)) {e : Fin (n + 2) → ℝ}
    (hval : ∀ j : Fin (n + 2), f (x j) - q (x j) = (-1) ^ (j : ℕ) * e j)
    (hsign : (∀ j, 0 < e j) ∨ ∀ j, e j < 0) :
    ⨅ j, |e j| ≤ bestApproximationError a b n f := by
  have hbdd : BddBelow (Set.range fun j => |e j|) := (Set.finite_range _).bddBelow
  have hpow : ∀ j : Fin (n + 2), ((-1 : ℝ) ^ (j : ℕ)) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  rcases hsign with hpos | hneg
  · refine le_infDist_of_alternates hq (Or.inl rfl) hmono fun j => ?_
    calc ⨅ j, |e j| ≤ |e j| := ciInf_le hbdd j
      _ = 1 * (-1) ^ (j : ℕ) * (f (x j) - q (x j)) := by
          rw [hval j, abs_of_pos (hpos j), one_mul, ← mul_assoc, hpow j, one_mul]
  · refine le_infDist_of_alternates hq (Or.inr rfl) hmono fun j => ?_
    calc ⨅ j, |e j| ≤ |e j| := ciInf_le hbdd j
      _ = -1 * (-1) ^ (j : ℕ) * (f (x j) - q (x j)) := by
          rw [hval j, abs_of_neg (hneg j), mul_assoc, ← mul_assoc ((-1 : ℝ) ^ (j : ℕ)), hpow j,
            one_mul, neg_one_mul]

/-! ### The interpolation error and the Lebesgue constant -/

/-- **Section 10.8** of [quarteroni2000numerical], the bound $\|f - \Pi_n f\|_\infty \le (1 +
\Lambda_n) E_n^*(f)$. Let $x_0, \dots, x_n$ be distinct nodes in $[a, b]$, and let $\Pi_n$ be
the Lagrange interpolation operator at these nodes. Then for every $f \in C^0([a, b])$,
$$\|f - \Pi_n f\|_\infty \le (1 + \Lambda_n) E_n^*(f),$$
where $\Lambda_n = \sup_{t \in [a, b]} \sum_i |l_i(t)|$ is the Lebesgue constant (8.11) of the
nodes.

The argument of the book is the triangle inequality through $p_n^*$ together with the Lagrange
representation of $p_n^* - \Pi_n f = \Pi_n (p_n^* - f)$. Here it is the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem` for the projection `Lagrange.interpolateCLM x`, whose
range is $\mathbb{P}_n$ (`Lagrange.range_interpolateCLM`) and whose norm is $\Lambda_n$
(`Lagrange.norm_interpolateCLM`). -/
theorem interpolation_error_le_lebesgue {x : Fin (n + 1) → Icc a b} (hx : Function.Injective x)
    (f : C(Icc a b, ℝ)) :
    ‖f - Lagrange.interpolateCLM x f‖
      ≤ (1 + sSup (Set.range fun t : Icc a b => ∑ i, |Lagrange.basisCM x i t|))
        * bestApproximationError a b n f := by
  have : Nonempty (Icc a b) := ⟨x 0⟩
  have h := norm_sub_apply_le_of_isIdempotentElem (Lagrange.interpolateCLM x)
    (Lagrange.isIdempotentElem_interpolateCLM hx) f
  rw [Lagrange.range_interpolateCLM hx, Lagrange.norm_interpolateCLM hx] at h
  exact h

end QuarteroniSaccoSaleri.Chapter10
