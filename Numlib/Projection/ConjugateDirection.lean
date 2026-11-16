/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Projection.OneDimensional

/-!
# Conjugate-direction methods

Let $A$ be a linear operator on an inner product space $E$ and let $b \in E$. A conjugate-direction
method for $Ax = b$ along directions $d_0, d_1, \dots \in E$ starts from $x_0$ and takes exact
line-search steps
$$x_{k+1} = x_k + \alpha_k d_k, \qquad \alpha_k = \frac{\langle d_k, r_k \rangle}{\langle d_k, A d_k
  \rangle}, \qquad r_k = b - A x_k,$$
along directions that are mutually $A$-conjugate: $\langle A d_k, d_m \rangle = 0$ for $k \neq m$
([quarteroni2000numerical] §4.3.4 and §7.2.4, [hestenes1952methods] §3–4, [nocedal2006numerical]
§5.1). The step is `Projection.step1 A b (d k) (d k)` of `Numlib.Projection.OneDimensional`.

For coercive $A$ and conjugate directions, the file proves the *expanding subspace theorem*
([quarteroni2000numerical] Theorem 4.11 and Property 7.6, [nocedal2006numerical] Theorem 5.2). The
residual $r_{k+1}$ is orthogonal to $d_0, \dots, d_k$, and $x_k$ is the Galerkin iterate over $x_0 +
\operatorname{span}\{d_0, \dots, d_{k-1}\}$. For symmetric $A$ it follows, by
`IsGalerkin.quadratic_le` and `IsGalerkin.iff_energyNorm_min`, that $x_k$ minimizes the energy
functional $\tfrac12 \operatorname{Re}\langle Ax, x \rangle - \operatorname{Re}\langle b, x \rangle$
over this affine space, equivalently the energy norm of the error. The method terminates: once the
directions span $E$ the iterate is exact, and $n$ nonzero conjugate directions span a space of
dimension $n$.

## Main definitions

* `ConjugateDirection.IsConjugateFamily`: the directions are pairwise $A$-conjugate.
* `ConjugateDirection.iterate`: the $k$-th iterate $x_k$ from $x_0$.

## Main results

* `ConjugateDirection.inner_residual_direction_eq_zero`: $\langle r_{k+1}, d_m \rangle = 0$ for
  every $m \le k$.
* `ConjugateDirection.isGalerkin_iterate`: $x_k$ is the Galerkin iterate over $x_0 +
  \operatorname{span}\{d_0, \dots, d_{k-1}\}$.
* `ConjugateDirection.IsConjugateFamily.linearIndependent`: nonzero conjugate directions of a
  coercive operator are linearly independent.
* `ConjugateDirection.apply_iterate_eq_of_span_eq_top`: once the directions used span $E$, the
  iterate solves $Ax = b$.
* `ConjugateDirection.iterate_eq_of_finrank_le`: in dimension $n$, with $d_0, \dots, d_{n-1}$
  nonzero, every iterate from $x_n$ on is the solution.

## Implementation notes

* The directions need not be nonzero. The conjugate gradient directions vanish after the grade of
  the residual and are still conjugate (`CG.isConjugateFamily_direction`). A zero direction gives a
  zero step. Only finite termination needs $d_k \neq 0$, and its statements say so.
* Nothing here is specific to Krylov methods: the directions are arbitrary. The conjugate gradient
  recurrence of `Numlib.Krylov.CG` is the instance in which the directions are generated from the
  residuals (`CG.iterate_x_eq_conjugateDirection_iterate`). The nonlinear conjugate gradient methods
  of `Numlib.Optimization.ConjugateGradient` reduce to it on a quadratic function.
* The results need only coercivity of $A$. Symmetry enters only through the optimality
  characterizations of `Numlib.Projection.Optimality`. The space $E$ is any inner product space, not
  necessarily complete; the finite-termination results in terms of $\dim E$ need $E$
  finite-dimensional.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ConjugateDirection

/-- A family $(d_k)_{k \in \mathbb{N}}$ of directions is **$A$-conjugate** (or $A$-orthogonal) if
$$\langle A d_k, d_m \rangle = 0 \quad\text{for all } k \neq m$$
([quarteroni2000numerical] §4.3.4 and §7.2.4).

The condition is required for both orders of $k$ and $m$, so no symmetry of $A$ is assumed. The
directions may be zero. -/
def IsConjugateFamily (A : E →ₗ[𝕜] E) (d : ℕ → E) : Prop :=
  ∀ k m, k ≠ m → inner 𝕜 (A (d k)) (d m) = 0

/-- The **conjugate-direction iterates** along $(d_k)$ from $x_0$: $x_0$ is the starting point, and
$$x_{k+1} = x_k + \frac{\langle d_k, r_k \rangle}{\langle d_k, A d_k \rangle}\, d_k, \qquad
  r_k = b - A x_k.$$
This is the descent method ([quarteroni2000numerical] (7.25)) along the directions $d_k$ with
the exact step ([quarteroni2000numerical] (4.39), (7.36)).

The step is `Projection.step1 A b (d k) (d k)`. If $\langle d_k, A d_k \rangle = 0$, the
quotient is $0$ by the convention of division by zero, and $x_{k+1} = x_k$. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b : E) (d : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => Projection.step1 A b (d k) (d k) (iterate A b d x₀ k)

variable (A : E →ₗ[𝕜] E) (b : E) (d : ℕ → E) (x₀ : E)

/-- The iterate with index $0$ is the starting point $x_0$. -/
@[simp] theorem iterate_zero : iterate A b d x₀ 0 = x₀ := rfl

/-- The recurrence: $x_{k+1}$ is the one-dimensional step `Projection.step1 A b (d k) (d k)` from
$x_k$, the exact line-search step along $d_k$. -/
theorem iterate_succ (k : ℕ) :
    iterate A b d x₀ (k + 1) = Projection.step1 A b (d k) (d k) (iterate A b d x₀ k) := rfl

/-- The recurrence with the step written out:
$$x_{k+1} = x_k + \alpha_k d_k, \qquad \alpha_k = \frac{\langle d_k, b - A x_k \rangle}{\langle
  d_k, A d_k \rangle}.$$
-/
theorem iterate_succ_eq (k : ℕ) :
    iterate A b d x₀ (k + 1) = iterate A b d x₀ k +
      (inner 𝕜 (d k) (b - A (iterate A b d x₀ k)) / inner 𝕜 (d k) (A (d k))) • d k := rfl

/-- The residual recurrence: with $r_k = b - A x_k$ and $\alpha_k = \langle d_k, r_k \rangle /
\langle d_k, A d_k \rangle$,
$$r_{k+1} = r_k - \alpha_k A d_k.$$
-/
theorem residual_succ (k : ℕ) :
    b - A (iterate A b d x₀ (k + 1)) = (b - A (iterate A b d x₀ k)) -
      (inner 𝕜 (d k) (b - A (iterate A b d x₀ k)) / inner 𝕜 (d k) (A (d k))) • A (d k) := by
  rw [iterate_succ_eq, map_add, map_smul]
  abel

/-- The iterates stay in the affine space spanned by the directions used so far: $x_k - x_0 \in
\operatorname{span}\{d_0, \dots, d_{k-1}\}$ for every $k$. -/
theorem iterate_sub_mem_span (k : ℕ) :
    iterate A b d x₀ k - x₀ ∈ Submodule.span 𝕜 (Set.range fun i : Fin k => d i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : Submodule.span 𝕜 (Set.range fun i : Fin k => d i) ≤
        Submodule.span 𝕜 (Set.range fun i : Fin (k + 1) => d i) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castSucc i, rfl⟩
    rw [iterate_succ_eq, add_sub_right_comm]
    exact Submodule.add_mem _ (hmono ih)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last k, rfl⟩))

/-- Once an iterate is exact the iteration is stationary: if $A x_k = b$, then $x_{k+j} = x_k$ for
every $j$.

The residual vanishes, so every later step has coefficient $0$. -/
theorem iterate_add_eq_of_apply_eq {k : ℕ} (hk : A (iterate A b d x₀ k) = b) (j : ℕ) :
    iterate A b d x₀ (k + j) = iterate A b d x₀ k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, iterate_succ_eq, ih, hk, sub_self, inner_zero_right, zero_div, zero_smul,
      add_zero]

variable {A d}

/-- Let $A$ be coercive. For every $k$, the new residual is orthogonal to the current direction:
$\langle r_{k+1}, d_k \rangle = 0$.

This is the exactness of the line search, `Projection.step1_isGalerkin`. Coercivity gives
$\langle d_k, A d_k \rangle \neq 0$ for $d_k \neq 0$, and a zero direction gives a zero step. -/
theorem inner_residual_succ_direction_self_eq_zero (hA : A.IsCoercive) (k : ℕ) :
    inner 𝕜 (b - A (iterate A b d x₀ (k + 1))) (d k) = 0 := by
  rw [iterate_succ, inner_eq_zero_symm]
  exact (Projection.step1_isGalerkin hA (d k) _).inner_residual_eq_zero
    (Submodule.mem_span_singleton_self _)

/-- **Orthogonality of the residuals** ([quarteroni2000numerical] Property 7.6, third clause, and
(4.44)). Let $A$ be coercive and let $(d_k)$ be $A$-conjugate. Then for all $m \le k$,
$$\langle r_{k+1}, d_m \rangle = 0.$$

The step along $d_k$ gives $r_{k+1} \perp d_k$. Since $\langle A d_k, d_m \rangle = 0$ for
$m < k$, the step does not change $\langle r, d_m \rangle$, which is zero by induction. -/
theorem inner_residual_direction_eq_zero (hA : A.IsCoercive) (hd : IsConjugateFamily A d) :
    ∀ k m, m ≤ k → inner 𝕜 (b - A (iterate A b d x₀ (k + 1))) (d m) = 0 := by
  intro k
  induction k with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := Nat.le_zero.1 hm
    exact inner_residual_succ_direction_self_eq_zero b x₀ hA 0
  | succ k ih =>
    intro m hm
    rcases hm.lt_or_eq with hlt | rfl
    · rw [residual_succ, inner_sub_left, inner_smul_left, ih m (Nat.lt_succ_iff.1 hlt),
        hd (k + 1) m hlt.ne', mul_zero, sub_zero]
    · exact inner_residual_succ_direction_self_eq_zero b x₀ hA (k + 1)

/-- Let $A$ be coercive and let $(d_k)$ be $A$-conjugate. Then $\langle d_m, r_{k+1} \rangle = 0$
for all $m \le k$. This is `ConjugateDirection.inner_residual_direction_eq_zero` with the
arguments of the inner product exchanged. -/
theorem inner_direction_residual_eq_zero (hA : A.IsCoercive) (hd : IsConjugateFamily A d)
    {k m : ℕ} (h : m ≤ k) : inner 𝕜 (d m) (b - A (iterate A b d x₀ (k + 1))) = 0 :=
  inner_eq_zero_symm.1 (inner_residual_direction_eq_zero b x₀ hA hd k m h)

/-- The **expanding subspace theorem** ([quarteroni2000numerical] Theorem 4.11 and Property 7.6,
second clause; [nocedal2006numerical] Theorem 5.2). Let $A$ be coercive and let $(d_k)$ be
$A$-conjugate. Then for every $k$ the iterate $x_k$ satisfies the Galerkin condition for
$A x = b$ over
$$x_0 + \operatorname{span}\{d_0, \dots, d_{k-1}\}.$$

For symmetric $A$ it follows, by `IsGalerkin.quadratic_le` and `IsGalerkin.iff_energyNorm_min`,
that $x_k$ minimizes over this affine space the energy functional $\tfrac12
\operatorname{Re}\langle Ax, x \rangle - \operatorname{Re}\langle b, x \rangle$, equivalently
the energy norm of the error. -/
theorem isGalerkin_iterate (hA : A.IsCoercive) (hd : IsConjugateFamily A d) (k : ℕ) :
    IsGalerkin A b x₀ (Submodule.span 𝕜 (Set.range fun i : Fin k => d i))
      (iterate A b d x₀ k) := by
  refine ⟨iterate_sub_mem_span A b d x₀ k, Submodule.mem_orthogonal_span.2 ?_⟩
  rintro _ ⟨i, rfl⟩
  cases k with
  | zero => exact i.elim0
  | succ k => exact inner_direction_residual_eq_zero b x₀ hA hd (Nat.lt_succ_iff.1 i.2)

/-- Let $A$ be coercive, let $(d_k)$ be $A$-conjugate, and let $d_i \neq 0$ for every $i < k$. Then
$d_0, \dots, d_{k-1}$ are linearly independent.

A vanishing linear combination, tested against $A d_j$, gives the $j$-th coefficient times
$\langle A d_j, d_j \rangle \neq 0$. The statement is about the first $k$ directions, because in
finite dimension an infinite sequence of nonzero conjugate directions does not exist. -/
theorem IsConjugateFamily.linearIndependent (hA : A.IsCoercive) (hd : IsConjugateFamily A d)
    {k : ℕ} (h0 : ∀ i < k, d i ≠ 0) : LinearIndependent 𝕜 (fun i : Fin k => d i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg j => ?_
  have hsum : inner 𝕜 (A (∑ i, g i • d i)) (d j) = 0 := by rw [hg, map_zero, inner_zero_left]
  rw [map_sum, sum_inner, Finset.sum_eq_single j (fun i _ hij => ?_)
    (fun h => (h (Finset.mem_univ j)).elim)] at hsum
  · rw [map_smul, inner_smul_left, mul_eq_zero] at hsum
    rcases hsum with h | h
    · simpa using h
    · exact absurd h fun h' => by
        have := hA.inner_self_pos (h0 j j.2)
        rw [h', map_zero] at this
        exact lt_irrefl 0 this
  · rw [map_smul, inner_smul_left, hd i j (fun h => hij (Fin.ext h)), mul_zero]

/-- **Finite termination**, intrinsic form. Let $A$ be coercive and let $(d_k)$ be $A$-conjugate. If
$\operatorname{span}\{d_0, \dots, d_{k-1}\} = E$, then $A x_k = b$.

The residual $r_k$ is orthogonal to $d_0, \dots, d_{k-1}$, hence to all of $E$. -/
theorem apply_iterate_eq_of_span_eq_top (hA : A.IsCoercive) (hd : IsConjugateFamily A d) {k : ℕ}
    (hk : Submodule.span 𝕜 (Set.range fun i : Fin k => d i) = ⊤) :
    A (iterate A b d x₀ k) = b := by
  have h := (isGalerkin_iterate b x₀ hA hd k).orth
  rw [hk, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-- **Finite termination** ([quarteroni2000numerical] Theorem 4.11 and Property 7.6, first clause).
Let $E$ have finite dimension $n$, let $A$ be coercive, let $(d_k)$ be $A$-conjugate, and let
$d_0, \dots, d_{n-1}$ be nonzero. Then $A x_n = b$.

The $n$ nonzero conjugate directions are linearly independent, so they span $E$. -/
theorem apply_iterate_finrank_eq [FiniteDimensional 𝕜 E] (hA : A.IsCoercive)
    (hd : IsConjugateFamily A d) (h0 : ∀ i < Module.finrank 𝕜 E, d i ≠ 0) :
    A (iterate A b d x₀ (Module.finrank 𝕜 E)) = b := by
  refine apply_iterate_eq_of_span_eq_top b x₀ hA hd (Submodule.eq_top_of_finrank_eq ?_)
  rw [finrank_span_eq_card (hd.linearIndependent hA h0), Fintype.card_fin]

/-- **Finite termination**, as a statement about the solution. Let $E$ have finite dimension $n$,
let $A$ be coercive, let $(d_k)$ be $A$-conjugate, and let $d_0, \dots, d_{n-1}$ be nonzero. If
$A x^* = b$, then $x_k = x^*$ for every $k \ge n$. -/
theorem iterate_eq_of_finrank_le [FiniteDimensional 𝕜 E] (hA : A.IsCoercive)
    (hd : IsConjugateFamily A d) (h0 : ∀ i < Module.finrank 𝕜 E, d i ≠ 0) {xstar : E}
    (hstar : A xstar = b) {k : ℕ} (hk : Module.finrank 𝕜 E ≤ k) :
    iterate A b d x₀ k = xstar := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [iterate_add_eq_of_apply_eq A b d x₀ (apply_iterate_finrank_eq b x₀ hA hd h0)]
  exact hA.injective (by rw [apply_iterate_finrank_eq b x₀ hA hd h0, hstar])

end ConjugateDirection
