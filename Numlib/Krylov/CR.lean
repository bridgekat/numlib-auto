/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Iterate

/-!
# The conjugate residual recurrence (Stiefel)

The conjugate residual (CR) method of Stiefel solves $Ax = b$ for a symmetric operator $A$ on an
inner product space. From $x_0$ it starts with $r_0 = p_0 = b - A x_0$ and $q_0 = A p_0$, and one
step computes
$$\alpha_k = \frac{\langle r_k, A r_k \rangle}{\langle q_k, q_k \rangle}, \quad x_{k+1} = x_k +
  \alpha_k p_k, \quad r_{k+1} = r_k - \alpha_k q_k,$$
$$\beta_k = \frac{\langle r_{k+1}, A r_{k+1} \rangle}{\langle r_k, A r_k \rangle}, \quad p_{k+1} =
  r_{k+1} + \beta_k p_k, \quad q_{k+1} = A r_{k+1} + \beta_k q_k.$$
This is Algorithm 6.20 of [saad2003iterative], Table 2.1 of [fong2012cg] and Table 2.12 of
[choi2006iterative]. The vector $q_k = A p_k$ is carried in the state, so that each step applies $A$
only once.

For a symmetric coercive $A$, the module proves that the iterate $x_k$ minimizes the residual
$\|b - Ax\|$ over $x_0 + \mathcal{K}_k(A, r_0)$, the orthogonality relations of Theorem 2.1 of
[fong2012cg], the sign properties of Theorem 2.2 of [fong2012cg], and the monotonicity results of
its Theorems 2.3–2.5. For a symmetric, possibly indefinite or singular $A$, it proves the
minimal-residual property as long as no breakdown occurs, and the strict increase of $\|x_k\|$ that
[fong2012cg], §4.2, proves after [steihaug1983conjugate]. It also proves the general lemma of the
GCR method, Lemma 6.21 of [saad2003iterative].

## Main definitions

* `CR.State`: the state of the iteration, with $x_k$, $r_k$, $p_k$ and $q_k = A p_k$.
* `CR.alpha`, `CR.step`, `CR.init`, `CR.iterate`: the step length, one step, the initial state, and
  the $k$-th state of the recurrence.

## Main results

* `CR.isMinResidualIterate`: for symmetric coercive $A$, the CR iterate is the minimal-residual
  iterate of `Numlib.Krylov.Iterate`.
* `CR.isMinResidualIterate_of_no_breakdown`: the same for a symmetric, possibly indefinite or
  singular $A$, as long as no breakdown occurs.
* `CR.inner_apply_direction_eq_zero`, `CR.inner_residual_apply_direction_eq_zero`,
  `CR.inner_residual_apply_residual_eq_zero`: the orthogonality relations
  $\langle A p_i, A p_j \rangle = 0$, $\langle r_i, A p_j \rangle = 0$ and
  $\langle r_i, A r_j \rangle = 0$ (Theorem 2.1 of [fong2012cg], after Luenberger).
* `CR.span_direction_eq`: the first $k$ directions span $\mathcal{K}_k(A, r_0)$.
* `CR.residual_eq_zero_of_grade_le`: finite termination at the grade of $r_0$.
* `CR.re_alpha_nonneg`, `CR.re_inner_direction_apply_direction_nonneg`,
  `CR.re_inner_direction_nonneg`, `CR.re_inner_iterate_direction_nonneg`,
  `CR.re_inner_residual_direction_nonneg`: the sign properties for symmetric positive definite $A$
  (Theorem 2.2 of [fong2012cg]).
* `CR.norm_iterate_monotone`, `CR.norm_error_antitone`, `CR.energyNorm_error_antitone`: $\|x_k\|$ is
  nondecreasing, and $\|x^* - x_k\|$ and $\|x^* - x_k\|_A$ are nonincreasing (Theorems 2.3–2.5 of
  [fong2012cg]).
* `CR.norm_iterate_lt_of_pos`: the strict increase of $\|x_k\|$ for a symmetric, possibly indefinite
  $A$, the analogue of the theorem of [steihaug1983conjugate].
* `Krylov.isMinResidualIterate_of_orthogonal_directions`: any $A^H A$-orthogonal sequence of
  directions that spans the Krylov spaces gives minimal-residual iterates (Lemma 6.21 of
  [saad2003iterative]).

## Implementation notes

* The inner product $\langle x, y \rangle$ is `inner 𝕜 x y`, which is conjugate-linear in $x$ (the
  Mathlib convention).
* The definitions are total: by the Lean convention $x / 0 = 0$, a degenerate step has a value, and
  once the residual is $0$ the state does not change.
* Theorems about the sign properties use the hypothesis `LinearMap.IsSymmetricCoercive`, a symmetric
  coercive operator, which is the setting "symmetric positive definite" of [fong2012cg].
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CR

/-- The **state of the conjugate residual iteration**: an iterate $x$, a residual $r$, a search
direction $p$, and the vector $q = Ap$. -/
structure State (E : Type*) where
  /-- The iterate $x_k$. -/
  x : E
  /-- The residual $r_k = b - A x_k$ (see `CR.residual_eq`). -/
  r : E
  /-- The search direction $p_k$. -/
  p : E
  /-- The image $q_k = A p_k$ of the search direction (see `CR.q_eq`). It is carried so that a step
  applies $A$ only to the new residual. -/
  q : E

/-- The **step length** of the conjugate residual iteration at a state $(x, r, p, q)$:
$$\alpha = \frac{\langle r, A r \rangle}{\langle q, q \rangle}.$$

Along the iteration $q = Ap$ (`CR.q_eq`), so $\alpha = \langle r, Ar \rangle / \langle Ap, Ap
\rangle$. By the Lean convention, $\alpha = 0$ when $q = 0$. -/
noncomputable def alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r (A s.r) / inner 𝕜 s.q s.q

/-- One **step of the conjugate residual iteration**. From a state $(x, r, p, q)$ with step length
$\alpha$ (`CR.alpha`), it computes $r' = r - \alpha q$ and $\beta = \langle r', A r' \rangle /
\langle r, A r \rangle$, and returns the state
$$(x + \alpha p, \; r', \; r' + \beta p, \; A r' + \beta q).$$
-/
noncomputable def step (A : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α := alpha A s
  let r' := s.r - α • s.q
  let β : 𝕜 := inner 𝕜 r' (A r') / inner 𝕜 s.r (A s.r)
  { x := s.x + α • s.p, r := r', p := r' + β • s.p, q := A r' + β • s.q }

/-- The **initial state** of the conjugate residual iteration at $x_0$: the residual and the first
search direction are both $r_0 = b - A x_0$, and $q_0 = A r_0$. Storing $q_0$ lets each later
step apply $A$ only once, to the new residual. -/
def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := b - A x₀, q := A (b - A x₀) }

/-- The **$k$-th state of the conjugate residual iteration** for $Ax = b$ from $x_0$: $k$
applications of `CR.step` to `CR.init`. The approximate solution is $x_k$, the field
`(CR.iterate A b x₀ k).x`.

For a symmetric coercive $A$, the iterate satisfies the minimal-residual specification over
$x_0 + \mathcal{K}_k(A, r_0)$ (`CR.isMinResidualIterate`). The specification, not this
recurrence, is the canonical object: everything proved of it holds for any method that meets it.
For an indefinite $A$, the recurrence can break down while the minimal-residual iterate still
exists; `CR.isMinResidualIterate_of_no_breakdown` is the result that holds there. The definition
is total in either case, because the Lean convention $x / 0 = 0$ gives a degenerate step a
value. Once the residual is $0$, the state does not change. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

/-- The recurrence: state $k + 1$ is `CR.step` applied to state $k$.

This is the order in which the algorithm is read. `Function.iterate` reduces in the other order,
so unfolding `(step A)^[k+1]` directly applies the extra step to the initial state. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The coefficient $\beta = \langle r', A r' \rangle / \langle r, A r \rangle$ of the direction
update, where $r'$ is the residual of the next state. -/
private noncomputable def beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A s).r (A (step A s).r) / inner 𝕜 s.r (A s.r)

private theorem step_x (s : State E) : (step A s).x = s.x + alpha A s • s.p := rfl

private theorem step_r (s : State E) : (step A s).r = s.r - alpha A s • s.q := rfl

private theorem step_p (s : State E) : (step A s).p = (step A s).r + beta A s • s.p := rfl

private theorem step_q (s : State E) : (step A s).q = A (step A s).r + beta A s • s.q := rfl

/-- Along the iteration, the stored vector is the image of the direction: $q_k = A p_k$ for every
$k$. -/
theorem q_eq (k : ℕ) : (iterate A b x₀ k).q = A (iterate A b x₀ k).p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_q, step_p, map_add, map_smul, ih]

private theorem iterate_succ_x (k : ℕ) : (iterate A b x₀ (k + 1)).x =
    (iterate A b x₀ k).x + alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ, step_x]

private theorem iterate_succ_r (k : ℕ) : (iterate A b x₀ (k + 1)).r =
    (iterate A b x₀ k).r - alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p := by
  rw [iterate_succ, step_r, q_eq]

private theorem iterate_succ_p (k : ℕ) : (iterate A b x₀ (k + 1)).p =
    (iterate A b x₀ (k + 1)).r + beta A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ]; exact step_p A _

private theorem beta_iterate (k : ℕ) : beta A (iterate A b x₀ k) =
    inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r) /
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) := by
  rw [beta, iterate_succ]

/-- The first direction is the first residual: $p_0 = r_0$. -/
private theorem direction_zero : (iterate A b x₀ 0).p = (iterate A b x₀ 0).r := rfl

/-- The residual field of the state is the true residual: $r_k = b - A x_k$ for every $k$. -/
theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_r, iterate_succ_x, ih, map_add, map_smul, sub_sub]

/-- The residual update: $\alpha_k A p_k = r_k - r_{k+1}$. -/
private theorem alpha_smul_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p =
      (iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r := by
  rw [iterate_succ_r]; abel

/-- If the residual $r_k$ is $0$, then the direction $p_k$ is $0$. -/
private theorem direction_eq_zero_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ k).p = 0 := by
  cases k with
  | zero => rw [direction_zero]; exact hr
  | succ k =>
    rw [iterate_succ_p, hr, beta_iterate, hr, inner_zero_left, zero_div, zero_smul, add_zero]

private theorem step_eq_self (s : State E) (hr : s.r = 0) (hp : s.p = 0) (hq : s.q = 0) :
    step A s = s := by
  obtain ⟨x, r, p, q⟩ := s
  simp_all [step]

private theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hk : (iterate A b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate A b x₀ l = iterate A b x₀ k := by
  have hp : (iterate A b x₀ k).p = 0 := direction_eq_zero_of_residual_eq_zero A b x₀ hk
  have hq : (iterate A b x₀ k).q = 0 := by rw [q_eq, hp, map_zero]
  induction l with
  | zero => obtain rfl : k = 0 := Nat.le_zero.1 hl; rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · rw [iterate_succ, ih (Nat.lt_succ_iff.1 h), step_eq_self A _ hk hp hq]
    · obtain rfl : k = l + 1 := le_antisymm hl h
      rfl

private theorem residual_succ_eq_zero_of_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ (k + 1)).r = 0 := by
  rw [iterate_eq_of_residual_eq_zero A b x₀ hr (k + 1) (Nat.le_succ k), hr]

/-! ### Elementary consequences of the recurrence -/

/-- If $\langle v, A p_l \rangle = 0$ for all $l \le j$, then $\langle v, A r_j \rangle = 0$,
because each residual is a combination of two consecutive directions. -/
private theorem inner_eq_zero_of_inner_direction {j : ℕ} {v : E}
    (h : ∀ l ≤ j, inner 𝕜 v (A (iterate A b x₀ l).p) = 0) :
    inner 𝕜 v (A (iterate A b x₀ j).r) = 0 := by
  cases j with
  | zero => rw [← direction_zero]; exact h 0 le_rfl
  | succ i =>
    have hi : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [hi, map_sub, map_smul, inner_sub_right, inner_smul_right, h _ le_rfl,
      h i (Nat.le_succ i), mul_zero, sub_zero]

/-- Both $r_k$ and $p_k$ lie in $\mathcal{K}_{k+1}(A, r_0)$. -/
private theorem residual_direction_mem_subspace (k : ℕ) :
    (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) ∧
      (iterate A b x₀ k).p ∈ subspace A (b - A x₀) (k + 1) := by
  induction k with
  | zero =>
    have h : b - A x₀ ∈ subspace A (b - A x₀) 1 := self_mem_subspace A (b - A x₀) one_pos
    exact ⟨h, h⟩
  | succ k ih =>
    have hmono := subspace_mono A (b - A x₀) (Nat.le_succ (k + 1))
    have hr : (iterate A b x₀ (k + 1)).r ∈ subspace A (b - A x₀) (k + 1 + 1) := by
      rw [iterate_succ_r]
      exact Submodule.sub_mem _ (hmono ih.1) (Submodule.smul_mem _ _
        (map_subspace_le A (b - A x₀) (k + 1) ⟨_, ih.2, rfl⟩))
    exact ⟨hr, by
      rw [iterate_succ_p]
      exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ih.2))⟩

/-- The span of the first $k$ search directions $p_0, \dots, p_{k-1}$. -/
private noncomputable def dirSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p)

private theorem direction_mem_dirSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).p ∈ dirSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem dirSpan_mono {k l : ℕ} (h : k ≤ l) : dirSpan A b x₀ k ≤ dirSpan A b x₀ l := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact direction_mem_dirSpan A b x₀ (lt_of_lt_of_le i.2 h)

private theorem residual_mem_dirSpan (i : ℕ) : (iterate A b x₀ i).r ∈ dirSpan A b x₀ (i + 1) := by
  cases i with
  | zero => rw [← direction_zero]; exact direction_mem_dirSpan A b x₀ Nat.zero_lt_one
  | succ i =>
    have h : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [h]
    exact Submodule.sub_mem _ (direction_mem_dirSpan A b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (direction_mem_dirSpan A b x₀ (by omega)))

private theorem dirSpan_le_subspace (k : ℕ) : dirSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (residual_direction_mem_subspace A b x₀ i).2

private theorem iterate_sub_mem (k : ℕ) :
    (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k := by
  induction k with
  | zero => simp [iterate, init]
  | succ k ih =>
    have h : (iterate A b x₀ (k + 1)).x - x₀ = ((iterate A b x₀ k).x - x₀) +
        alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
      rw [iterate_succ_x]; abel
    rw [h]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ (residual_direction_mem_subspace A b x₀ k).2)

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-! ### The joint induction of Theorem 2.1 of [fong2012cg] -/

private theorem re_inner_self_nonneg (x : E) : 0 ≤ RCLike.re (inner 𝕜 x (A x)) := by
  obtain ⟨c, hc, h⟩ := hA.isCoercive
  rw [← hA.isSymmetric]
  exact le_trans (by positivity) (h x)

private theorem eq_zero_of_inner_self_eq_zero {x : E} (h : inner 𝕜 x (A x) = 0) : x = 0 := by
  by_contra hx
  have hpos := hA.isCoercive.inner_self_pos hx
  rw [hA.isSymmetric, h, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-- For a symmetric coercive $A$, $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every
$j$. This is the first fact that the sign properties below take from coercivity. -/
private theorem re_inner_residual_self_nonneg :
    ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)) :=
  fun _ => re_inner_self_nonneg hA _

/-- For a symmetric coercive $A$, $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$. This is the
second fact that the sign properties below take from coercivity. -/
private theorem residual_eq_zero_of_inner_self :
    ∀ j, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 →
      (iterate A b x₀ j).r = 0 :=
  fun _ h => eq_zero_of_inner_self_eq_zero hA h

omit hA in
private theorem conj_alpha (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (alpha A s) = alpha A s := by
  rw [alpha, map_div₀, inner_conj_symm, hAs, inner_self_conj]

omit hA in
private theorem conj_beta (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (beta A s) = beta A s := by
  rw [beta, map_div₀, inner_conj_symm, hAs, inner_conj_symm, hAs]

omit hA in
/-- If $\langle r_k, A p_k \rangle = \langle r_k, A r_k \rangle$, then $\alpha_k \langle A p_k, A
p_k \rangle = \langle r_k, A r_k \rangle$. This holds also at a breakdown. -/
private theorem alpha_mul_inner_apply_direction' (k : ℕ)
    (hdiag : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).p) =
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) :
    alpha A (iterate A b x₀ k) *
        inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ k).p) =
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) := by
  by_cases h : inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ k).p) = 0
  · rw [h, mul_zero, ← hdiag, inner_self_eq_zero.1 h, inner_zero_right]
  · rw [alpha, q_eq, div_mul_cancel₀ _ h]

omit hA in
/-- If $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$ for every $j$, then $\beta_k \langle r_k,
A r_k \rangle = \langle r_{k+1}, A r_{k+1} \rangle$. This holds also at a breakdown. -/
private theorem beta_mul_inner_self
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (k : ℕ) :
    beta A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) =
      inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r) := by
  by_cases h : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) = 0
  · rw [h, mul_zero, residual_succ_eq_zero_of_eq_zero A b x₀ (hz k h), inner_zero_left]
  · rw [beta_iterate, div_mul_cancel₀ _ h]

omit hA in
/-- If $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$ for every $j$, and the step length
$\alpha_k$ is $0$, then $A p_k = 0$. -/
private theorem apply_direction_eq_zero_of_alpha_eq_zero
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0) {k : ℕ}
    (h : alpha A (iterate A b x₀ k) = 0) : A (iterate A b x₀ k).p = 0 := by
  rcases div_eq_zero_iff.1 h with h' | h'
  · rw [direction_eq_zero_of_residual_eq_zero A b x₀ (hz k h'), map_zero]
  · rw [← q_eq]
    exact inner_self_eq_zero.1 h'

omit hA in
/-- If $\alpha_j = 0$ implies $A p_j = 0$, then $\langle v, A(A p_j) \rangle = 0$ for every $v$ with
$\langle v, A r_j \rangle = 0$ and $\langle v, A r_{j+1} \rangle = 0$. -/
private theorem inner_apply_apply_direction_eq_zero_of {j : ℕ} {v : E}
    (hdeg : alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0)
    (h1 : inner 𝕜 v (A (iterate A b x₀ j).r) = 0)
    (h2 : inner 𝕜 v (A (iterate A b x₀ (j + 1)).r) = 0) :
    inner 𝕜 v (A (A (iterate A b x₀ j).p)) = 0 := by
  by_cases hα : alpha A (iterate A b x₀ j) = 0
  · rw [hdeg hα, map_zero, inner_zero_right]
  · have h : alpha A (iterate A b x₀ j) * inner 𝕜 v (A (A (iterate A b x₀ j).p)) = 0 := by
      rw [← inner_smul_right, ← map_smul, alpha_smul_apply_direction, map_sub, inner_sub_right,
        h1, h2, sub_zero]
    exact (mul_eq_zero.1 h).resolve_left hα

/-- The joint invariant of the conjugate residual iteration at step $k$, from Theorem 2.1 of
[fong2012cg]. -/
private structure Invariant (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Prop where
  /-- $\langle r_k, A p_j \rangle = 0$ for $j < k$. -/
  rq : ∀ j < k, inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ j).p) = 0
  /-- $\langle A p_k, A p_j \rangle = 0$ for $j < k$. -/
  qq : ∀ j < k, inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ j).p) = 0
  /-- $\langle r_k, A p_k \rangle = \langle r_k, A r_k \rangle$. -/
  diag : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).p) =
    inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)

omit hA in
/-- For a symmetric $A$, the invariant holds at step $k$ under the two facts for which coercivity is
used: at a degenerate step before $k$ the image $A p_j$ is $0$, and the recurrence for $\beta$
transports $\langle r_j, A r_j \rangle$ to $\langle r_{j+1}, A r_{j+1} \rangle$. -/
private theorem invariant_of (hAs : A.IsSymmetric) (k : ℕ) :
    (∀ j < k, alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0) →
      (∀ j < k, beta A (iterate A b x₀ j) *
          inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) =
        inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ (j + 1)).r)) →
      Invariant A b x₀ k := by
  induction k with
  | zero =>
    exact fun _ _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j), by rw [direction_zero]⟩
  | succ k ihk =>
    intro hdeg hbeta
    have ih := ihk (fun j hj => hdeg j (by omega)) (fun j hj => hbeta j (by omega))
    have rq : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ j).p) = 0 := by
      intro j hj
      rw [iterate_succ_r, inner_sub_left, inner_smul_left, conj_alpha hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.rq j h, ih.qq j h, mul_zero, sub_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        rw [ih.diag, alpha_mul_inner_apply_direction' b x₀ j ih.diag, sub_self]
    have rr : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ j).r) = 0 :=
      fun j hj => inner_eq_zero_of_inner_direction A b x₀ fun l hl => rq l (by omega)
    refine ⟨rq, fun j hj => ?_, ?_⟩
    · rw [iterate_succ_p, map_add, map_smul, inner_add_left, inner_smul_left, conj_beta hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.qq j h, mul_zero, add_zero, hAs,
          inner_apply_apply_direction_eq_zero_of b x₀ (hdeg j (by omega)) (rr j (by omega))
            (rr (j + 1) (by omega))]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        by_cases hα : alpha A (iterate A b x₀ j) = 0
        · rw [hdeg j (by omega) hα]
          simp
        · have key : alpha A (iterate A b x₀ j) *
              (inner 𝕜 (A (iterate A b x₀ (j + 1)).r) (A (iterate A b x₀ j).p) +
                beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) = 0 := by
            rw [mul_add, ← inner_smul_right, alpha_smul_apply_direction, hAs,
              map_sub, inner_sub_right, rr j (by omega), zero_sub,
              show alpha A (iterate A b x₀ j) * (beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) =
                beta A (iterate A b x₀ j) * (alpha A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) by ring,
              alpha_mul_inner_apply_direction' b x₀ j ih.diag, hbeta j (by omega)]
            ring
          exact (mul_eq_zero.1 key).resolve_left hα
    · rw [iterate_succ_p, map_add, map_smul, inner_add_right, inner_smul_right,
        rq k (Nat.lt_succ_self k), mul_zero, add_zero]

omit hA in
/-- For a symmetric $A$ such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$ for every $j$,
the invariant holds at every step. -/
private theorem invariant' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (k : ℕ) : Invariant A b x₀ k :=
  invariant_of b x₀ hAs k
    (fun _ _ h => apply_direction_eq_zero_of_alpha_eq_zero b x₀ hz h)
    (fun j _ => beta_mul_inner_self b x₀ hz j)

private theorem invariant (k : ℕ) : Invariant A b x₀ k :=
  invariant' b x₀ hA.isSymmetric (residual_eq_zero_of_inner_self b x₀ hA) k

/-! ### The named orthogonality relations -/

/-- **Theorem 2.1(a)** of [fong2012cg], after Luenberger. Let $A$ be a symmetric coercive operator,
and let $p_i$ be the directions of the conjugate residual iteration for $Ax = b$ from $x_0$. The
images of distinct directions are orthogonal: for $i \neq j$,
$$\langle A p_i, A p_j \rangle = 0.$$
-/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (A (iterate A b x₀ j).p) = 0 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, (invariant b x₀ hA j).qq i h', map_zero]
  · exact (invariant b x₀ hA i).qq j h'

/-- **Theorem 2.1(b)** of [fong2012cg]. Let $A$ be a symmetric coercive operator, and let $r_i$,
$p_j$ be the residuals and directions of the conjugate residual iteration for $Ax = b$ from
$x_0$. Each residual is orthogonal to the images of the earlier directions: for $j < i$,
$$\langle r_i, A p_j \rangle = 0.$$
-/
theorem inner_residual_apply_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) = 0 :=
  (invariant b x₀ hA i).rq j h

omit hA in
/-- For a symmetric $A$ such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$ for every $j$,
the residuals are $A$-orthogonal: $\langle r_i, A r_j \rangle = 0$ for $i \neq j$. -/
private theorem inner_residual_apply_residual_eq_zero' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0 := by
  have key : ∀ m n : ℕ, n < m →
      inner 𝕜 (iterate A b x₀ m).r (A (iterate A b x₀ n).r) = 0 :=
    fun m n hmn => inner_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant' b x₀ hAs hz m).rq l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← hAs, ← inner_conj_symm, key j i h', map_zero]
  · exact key i j h'

/-- The residuals of the conjugate residual iteration are $A$-orthogonal. Let $A$ be a symmetric
coercive operator, and let $r_i$ be the residuals of the iteration for $Ax = b$ from $x_0$. For
$i \neq j$,
$$\langle r_i, A r_j \rangle = 0.$$
-/
theorem inner_residual_apply_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0 :=
  inner_residual_apply_residual_eq_zero' b x₀ hA.isSymmetric
    (residual_eq_zero_of_inner_self b x₀ hA) h

omit hA in
/-- For a symmetric $A$ such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$ for every $j$:
$\langle r_i, A p_j \rangle = \langle r_j, A r_j \rangle$ for $i \le j$. -/
private theorem inner_residual_apply_direction_eq' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) =
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) := by
  induction j, h using Nat.le_induction with
  | base => exact (invariant' b x₀ hAs hz i).diag
  | succ j hij ih =>
    rw [iterate_succ_p, map_add, map_smul, inner_add_right, inner_smul_right, ih,
      inner_residual_apply_residual_eq_zero' b x₀ hAs hz (show i ≠ j + 1 by omega), zero_add,
      beta_mul_inner_self b x₀ hz j]

/-- For a symmetric coercive $A$ and $i \le j$, the residuals and directions of the conjugate
residual iteration satisfy $\langle r_i, A p_j \rangle = \langle r_j, A r_j \rangle$. This is
the analogue for CR of the identity $\langle r_i, p_j \rangle = \|r_j\|^2$ of conjugate
gradients. -/
theorem inner_residual_apply_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) =
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) :=
  inner_residual_apply_direction_eq' b x₀ hA.isSymmetric
    (residual_eq_zero_of_inner_self b x₀ hA) h

/-! ### Spans and the minimal-residual property -/

omit hA in
private theorem apply_direction_mem_dirSpan (i : ℕ)
    (hdeg : alpha A (iterate A b x₀ i) = 0 → A (iterate A b x₀ i).p = 0) :
    A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2) := by
  by_cases hα : alpha A (iterate A b x₀ i) = 0
  · rw [hdeg hα]
    exact Submodule.zero_mem _
  · have h : A (iterate A b x₀ i).p = (alpha A (iterate A b x₀ i))⁻¹ •
        ((iterate A b x₀ i).r - (iterate A b x₀ (i + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ i))
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ (i + 1))))

omit hA in
private theorem pow_apply_mem_dirSpan (k : ℕ)
    (hmem : ∀ i < k, A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2))
    (ih : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k) :
    (A ^ k) (b - A x₀) ∈ dirSpan A b x₀ (k + 1) := by
  cases k with
  | zero =>
    have h : (iterate A b x₀ 0).p ∈ dirSpan A b x₀ 1 :=
      direction_mem_dirSpan A b x₀ Nat.zero_lt_one
    simpa [iterate, init] using h
  | succ j =>
    have hmemj : (A ^ j) (b - A x₀) ∈ dirSpan A b x₀ (j + 1) :=
      ih (pow_apply_mem_subspace A _ (Nat.lt_succ_self j))
    have hpow : (A ^ (j + 1)) (b - A x₀) = A ((A ^ j) (b - A x₀)) := by rw [pow_succ']; rfl
    have hcomap : dirSpan A b x₀ (j + 1) ≤ Submodule.comap A (dirSpan A b x₀ (j + 1 + 1)) := by
      rw [dirSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact dirSpan_mono A b x₀ (by omega) (hmem l (by omega))
    rw [hpow]
    exact hcomap hmemj

omit hA in
private theorem subspace_le_dirSpan (k : ℕ)
    (hmem : ∀ i < k, A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2)) :
    subspace A (b - A x₀) k ≤ dirSpan A b x₀ k := by
  induction k with
  | zero => rw [subspace_zero]; exact bot_le
  | succ k ihk =>
    have ih := ihk fun i hi => hmem i (by omega)
    rw [subspace, Submodule.span_le, Set.range_subset_iff]
    intro i
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · exact dirSpan_mono A b x₀ (Nat.le_succ k) (ih (pow_apply_mem_subspace A _ h))
    · have h' : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) h
      rw [h']
      exact pow_apply_mem_dirSpan b x₀ k (fun i hi => hmem i (by omega)) ih

/-- The first $k$ directions of the conjugate residual iteration span the Krylov space. Let $A$ be a
symmetric coercive operator, and let $p_i$ be the directions of the iteration for $Ax = b$ from
$x_0$. For every $k$,
$$\operatorname{span}\{p_0, \dots, p_{k-1}\} = \mathcal{K}_k(A, r_0).$$

This turns the orthogonality relations, which say only that $r_k$ is orthogonal to the images of
the earlier directions, into the minimal-residual property `CR.isMinResidualIterate`, since
orthogonality to the span is what the specification asks for. Degenerate steps cost nothing: a
direction whose image under $A$ is $0$ adds no dimension, and the residuals, which lie in the
same span, still fill the Krylov space. -/
theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
  le_antisymm (dirSpan_le_subspace A b x₀ k) (subspace_le_dirSpan b x₀ k
    fun i _ => apply_direction_mem_dirSpan b x₀ i
      fun h => apply_direction_eq_zero_of_alpha_eq_zero b x₀
        (residual_eq_zero_of_inner_self b x₀ hA) h)

/-- The **conjugate residual iterate is the minimal-residual iterate**. Let $A$ be a symmetric
coercive operator. For every $k$, the iterate $x_k$ of the conjugate residual iteration for
$Ax = b$ from $x_0$ satisfies $x_k - x_0 \in \mathcal{K}_k(A, r_0)$ and
$$\|b - A x_k\| \le \|b - A y\| \quad \text{for all } y \in x_0 + \mathcal{K}_k(A, r_0).$$
On symmetric systems, CR, MINRES and GMRES therefore have the same iterates. -/
theorem isMinResidualIterate (k : ℕ) : IsMinResidualIterate A b x₀ k (iterate A b x₀ k).x := by
  refine IsMinResidual.iff_isPetrovGalerkin.2 ⟨iterate_sub_mem A b x₀ k, ?_⟩
  rw [← residual_eq, ← span_direction_eq b x₀ hA k, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [← inner_conj_symm, inner_residual_apply_direction_eq_zero b x₀ hA i.2, map_zero]

/-- **Finite termination** of the conjugate residual iteration. Let $A$ be a symmetric coercive
operator, and suppose that the Krylov space of $A$ and $r_0 = b - A x_0$ is finite-dimensional.
If $k \ge \operatorname{grade}(A, r_0)$, then $r_k = 0$. Thus the iteration is a direct method
that ends in at most $\operatorname{grade}(A, r_0)$ steps.

The iterate minimizes the residual over $x_0 + \mathcal{K}_k(A, r_0)$, and at the grade this
space already contains the exact solution. -/
theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  rw [residual_eq, sub_eq_zero]
  exact ((isMinResidualIterate b x₀ hA k).apply_eq_of_grade_le hk
    hA.isCoercive.injective.injOn).symm

/-- For a symmetric coercive $A$ with a finite-dimensional Krylov space of $r_0$, for every $n$
there is an $m \ge n$ with $r_m = 0$. This is the third fact that the sign properties take from
coercivity. -/
private theorem exists_residual_eq_zero [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] :
    ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0 :=
  fun n => ⟨max n (grade A (b - A x₀)), le_max_left _ _,
    residual_eq_zero_of_grade_le b x₀ hA (le_max_right _ _)⟩

/-- Let $A$ be symmetric coercive and $b \neq 0$. Then the first iterate $x_1 = \alpha_0 b$ of the
conjugate residual iteration from $x_0 = 0$ is nonzero, so the backward-error ratio
$\|r_k\| / \|x_k\|$ is defined from step $1$ on. -/
theorem iterate_one_x_ne_zero (hb : b ≠ 0) : (iterate A b 0 1).x ≠ 0 := by
  have h0 : (iterate A b 0 0).x = 0 := rfl
  have hp : (iterate A b 0 0).p = b := by simp [iterate, init]
  have hr : (iterate A b 0 0).r = b := by simp [iterate, init]
  rw [iterate_succ_x, h0, hp, zero_add, smul_ne_zero_iff]
  refine ⟨?_, hb⟩
  rw [alpha, hr, q_eq, hp]
  refine div_ne_zero (fun h => hb (eq_zero_of_inner_self_eq_zero hA h)) fun h => hb ?_
  exact hA.isCoercive.injective (by rw [inner_self_eq_zero.1 h, map_zero])

/-! ### Signs: Theorem 2.2 of [fong2012cg] -/

omit hA in
private theorem alpha_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : alpha A (iterate A b x₀ k) =
    ((RCLike.re (inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) /
      ‖(iterate A b x₀ k).q‖ ^ 2 : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, hAs.coe_re_inner_self_apply, RCLike.ofReal_pow,
    ← inner_self_eq_norm_sq_to_K, alpha]

omit hA in
private theorem re_alpha_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r))) (k : ℕ) :
    0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (hnn k) (sq_nonneg _)

/-- **Theorem 2.2(a)** of [fong2012cg]. Let $A$ be a symmetric coercive operator. For every $k$, the
step length $\alpha_k$ of the conjugate residual iteration for $Ax = b$ from $x_0$ satisfies
$$\operatorname{Re} \alpha_k \ge 0.$$

The step length is real for a symmetric $A$. Clause (b) of the theorem, the same property for
the coefficients $\beta_k$, is proved only for internal use in this module. -/
theorem re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) :=
  re_alpha_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA) k

omit hA in
private theorem beta_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : beta A (iterate A b x₀ k) =
    ((RCLike.re (inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r)) /
      RCLike.re (inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, hAs.coe_re_inner_self_apply, hAs.coe_re_inner_self_apply, beta_iterate]

omit hA in
private theorem re_beta_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r))) (k : ℕ) :
    0 ≤ RCLike.re (beta A (iterate A b x₀ k)) := by
  rw [beta_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (hnn (k + 1)) (hnn k)

omit hA in
private theorem re_alpha_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (alpha A (iterate A b x₀ k) * z) =
      RCLike.re (alpha A (iterate A b x₀ k)) * RCLike.re z := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
private theorem re_beta_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (beta A (iterate A b x₀ k) * z) =
      RCLike.re (beta A (iterate A b x₀ k)) * RCLike.re z := by
  rw [beta_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$, and
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$: $\operatorname{Re} \langle p_i, A
p_j \rangle \ge 0$ for all $i$ and $j$. This is Theorem 2.2(c) of [fong2012cg] under these
hypotheses. -/
private theorem re_inner_direction_apply_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p)) := by
  have key : ∀ m n : ℕ, m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (A (iterate A b x₀ n).p)) := by
    intro m
    induction m with
    | zero =>
      intro n _
      rw [direction_zero, inner_residual_apply_direction_eq' b x₀ hAs hz (Nat.zero_le n)]
      exact hnn n
    | succ m ih =>
      intro n hn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta hAs, map_add,
        inner_residual_apply_direction_eq' b x₀ hAs hz (show m + 1 ≤ n by omega),
        re_beta_mul b x₀ hAs]
      exact add_nonneg (hnn n)
        (mul_nonneg (re_beta_nonneg b x₀ hAs hnn m) (ih n (by omega)))
  rcases le_total i j with h | h
  · exact key i j h
  · rw [← hAs, ← inner_conj_symm, RCLike.conj_re]
    exact key j i h

/-- **Theorem 2.2(c)** of [fong2012cg]. Let $A$ be a symmetric coercive operator, and let $p_i$ be
the directions of the conjugate residual iteration for $Ax = b$ from $x_0$. For all $i$ and $j$,
$$\operatorname{Re} \langle p_i, A p_j \rangle \ge 0.$$
-/
theorem re_inner_direction_apply_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p)) :=
  re_inner_direction_apply_direction_nonneg' b x₀ hA.isSymmetric
    (re_inner_residual_self_nonneg b x₀ hA) (residual_eq_zero_of_inner_self b x₀ hA) i j

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$, and
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$: $\operatorname{Re} \langle A(x_m -
x_i), p_j \rangle \ge 0$ for $i \le m$ and every $j$. The proof writes $A(x_m - x_i)$ as the
telescoping sum $\sum_{i \le l < m} \alpha_l A p_l$. -/
private theorem re_inner_apply_sub_direction_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i m : ℕ} (him : i ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (A ((iterate A b x₀ m).x - (iterate A b x₀ i).x))
      (iterate A b x₀ j).p) := by
  induction m, him using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ i).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ i).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    have h2 : inner 𝕜 (A (iterate A b x₀ m).p) (iterate A b x₀ j).p =
        inner 𝕜 (iterate A b x₀ m).p (A (iterate A b x₀ j).p) := hAs _ _
    rw [h, map_add, map_smul, inner_add_left, inner_smul_left, conj_alpha hAs, map_add,
      re_alpha_mul b x₀ hAs, h2]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg' b x₀ hAs hnn m)
      (re_inner_direction_apply_direction_nonneg' b x₀ hAs hnn hz m j))

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$,
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$, and such that the iteration
terminates: $\operatorname{Re} \langle r_i, p_j \rangle \ge 0$ for all $i$ and $j$. This is
Theorem 2.2(f) of [fong2012cg] under these hypotheses. -/
private theorem re_inner_residual_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p) := by
  obtain ⟨m, him, hr⟩ := hterm i
  rw [residual_eq, sub_eq_zero] at hr
  have hri : (iterate A b x₀ i).r = A ((iterate A b x₀ m).x - (iterate A b x₀ i).x) := by
    rw [map_sub, ← hr, ← residual_eq]
  rw [hri]
  exact re_inner_apply_sub_direction_nonneg b x₀ hAs hnn hz him j

/-- **Theorem 2.2(f)** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space, and let $r_i$, $p_j$ be the residuals and directions of
the conjugate residual iteration for $Ax = b$ from $x_0$. For all $i$ and $j$,
$$\operatorname{Re} \langle r_i, p_j \rangle \ge 0.$$

Finite dimension gives finite termination, which the proof uses. -/
theorem re_inner_residual_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p) :=
  re_inner_residual_direction_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA)
    (residual_eq_zero_of_inner_self b x₀ hA) (exists_residual_eq_zero b x₀ hA) i j

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$,
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$, and such that the iteration
terminates: $\operatorname{Re} \langle p_i, p_j \rangle \ge 0$ for all $i$ and $j$. This is
Theorem 2.2(d) of [fong2012cg] under these hypotheses. -/
private theorem re_inner_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  induction i with
  | zero =>
    rw [direction_zero]
    exact re_inner_residual_direction_nonneg' b x₀ hAs hnn hz hterm 0 j
  | succ i ih =>
    rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta hAs, map_add,
      re_beta_mul b x₀ hAs]
    exact add_nonneg (re_inner_residual_direction_nonneg' b x₀ hAs hnn hz hterm (i + 1) j)
      (mul_nonneg (re_beta_nonneg b x₀ hAs hnn i) ih)

/-- **Theorem 2.2(d)** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space, and let $p_i$ be the directions of the conjugate
residual iteration for $Ax = b$ from $x_0$. For all $i$ and $j$,
$$\operatorname{Re} \langle p_i, p_j \rangle \ge 0.$$

The proof uses finite termination. -/
theorem re_inner_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) :=
  re_inner_direction_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA)
    (residual_eq_zero_of_inner_self b x₀ hA) (exists_residual_eq_zero b x₀ hA) i j

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$,
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$, and such that the iteration
terminates: $\operatorname{Re} \langle x_m - x_i, p_j \rangle \ge 0$ for $i \le m$ and every
$j$. -/
private theorem re_inner_sub_direction_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) {i m : ℕ} (him : i ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ i).x)
      (iterate A b x₀ j).p) := by
  induction m, him using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ i).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ i).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hAs, map_add, re_alpha_mul b x₀ hAs]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg' b x₀ hAs hnn m)
      (re_inner_direction_nonneg' b x₀ hAs hnn hz hterm m j))

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle r_j, A r_j \rangle \ge 0$ for every $j$,
such that $\langle r_j, A r_j \rangle = 0$ implies $r_j = 0$, and such that the iteration
terminates, for the iteration from $x_0 = 0$: $\operatorname{Re} \langle x_i, p_j \rangle \ge 0$
for all $i$ and $j$. This is Theorem 2.2(e) of [fong2012cg] under these hypotheses. -/
private theorem re_inner_iterate_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)))
    (hz : ∀ j, inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r) = 0 →
      (iterate A b 0 j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b 0 m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p) := by
  have h := re_inner_sub_direction_nonneg b 0 hAs hnn hz hterm (Nat.zero_le i) j
  rwa [show (iterate A b 0 0).x = 0 from rfl, sub_zero] at h

/-- **Theorem 2.2(e)** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space, and let $x_i$, $p_j$ be the iterates and directions of
the conjugate residual iteration for $Ax = b$ from $x_0 = 0$. For all $i$ and $j$,
$$\operatorname{Re} \langle x_i, p_j \rangle \ge 0.$$
-/
theorem re_inner_iterate_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p) :=
  re_inner_iterate_direction_nonneg' b hA.isSymmetric (re_inner_residual_self_nonneg b 0 hA)
    (residual_eq_zero_of_inner_self b 0 hA) (exists_residual_eq_zero b 0 hA) i j

/-- **Theorem 2.3** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space. The norms $\|x_k\|$ of the iterates of the conjugate
residual iteration for $Ax = b$ from $x_0 = 0$ are nondecreasing in $k$. -/
theorem norm_iterate_monotone [FiniteDimensional 𝕜 E] :
    Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  refine monotone_nat_of_le_succ fun k => ?_
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 k).x
      (alpha A (iterate A b 0 k) • (iterate A b 0 k).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hA.isSymmetric]
    exact mul_nonneg (re_alpha_nonneg b 0 hA k) (re_inner_iterate_direction_nonneg b hA k k)
  have hsq : ‖(iterate A b 0 k).x‖ ^ 2 ≤ ‖(iterate A b 0 (k + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b 0 k) • (iterate A b 0 k).p‖]
  nlinarith [norm_nonneg (iterate A b 0 k).x, norm_nonneg (iterate A b 0 (k + 1)).x]

/-- **Theorem 2.4** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space, and let $A x^* = b$. The errors $\|x^* - x_k\|$ of the
iterates of the conjugate residual iteration for $Ax = b$ from $x_0$ are nonincreasing in $k$. -/
theorem norm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hr : (iterate A b x₀ (max (k + 1) (grade A (b - A x₀)))).r = 0 :=
    residual_eq_zero_of_grade_le b x₀ hA (le_max_right (k + 1) _)
  rw [residual_eq, sub_eq_zero] at hr
  have hxm : xstar = (iterate A b x₀ (max (k + 1) (grade A (b - A x₀)))).x :=
    hA.isCoercive.injective (hstar.trans hr)
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (xstar - (iterate A b x₀ (k + 1)).x)
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    refine mul_nonneg (re_alpha_nonneg b x₀ hA k) ?_
    rw [hxm]
    exact re_inner_sub_direction_nonneg b x₀ hA.isSymmetric
      (re_inner_residual_self_nonneg b x₀ hA) (residual_eq_zero_of_inner_self b x₀ hA)
      (exists_residual_eq_zero b x₀ hA) (le_max_left (k + 1) _) k
  have hsq : ‖xstar - (iterate A b x₀ (k + 1)).x‖ ^ 2 ≤ ‖xstar - (iterate A b x₀ k).x‖ ^ 2 := by
    rw [hexp, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p‖]
  nlinarith [norm_nonneg (xstar - (iterate A b x₀ (k + 1)).x),
    norm_nonneg (xstar - (iterate A b x₀ k).x)]

/-- The expansion of the quadratic form: $\operatorname{Re} \langle A(u + w), u + w \rangle =
\operatorname{Re} \langle Au, u \rangle + 2 \operatorname{Re} \langle Au, w \rangle +
\operatorname{Re} \langle Aw, w \rangle$ for a symmetric $A$. -/
private theorem re_inner_apply_add (u w : E) :
    RCLike.re (inner 𝕜 (A (u + w)) (u + w)) =
      RCLike.re (inner 𝕜 (A u) u) + 2 * RCLike.re (inner 𝕜 (A u) w) +
        RCLike.re (inner 𝕜 (A w) w) := by
  have h : inner 𝕜 (A w) u = (starRingEnd 𝕜) (inner 𝕜 (A u) w) := by
    rw [inner_conj_symm, hA.isSymmetric]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, h]
  simp only [map_add, RCLike.conj_re]
  ring

/-- **Theorem 2.5** of [fong2012cg]. Let $A$ be a symmetric coercive operator on a
finite-dimensional inner product space, and let $A x^* = b$. The errors $\|x^* - x_k\|_A$ in the
energy norm of the iterates of the conjugate residual iteration for $Ax = b$ from $x_0$ are
nonincreasing in $k$.

The paper states a strict decrease, which holds while the iteration still moves. The statement
here is the nonstrict form, which holds at every step, because the iterate does not change after
termination. -/
theorem energyNorm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hAe : A (xstar - (iterate A b x₀ (k + 1)).x) = (iterate A b x₀ (k + 1)).r := by
    rw [map_sub, hstar, ← residual_eq]
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ (k + 1)).x))
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [hAe, inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    exact mul_nonneg (re_alpha_nonneg b x₀ hA k)
      (re_inner_residual_direction_nonneg b x₀ hA (k + 1) k)
  have hself : 0 ≤ RCLike.re (inner 𝕜 (A (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p))
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [hA.isSymmetric]
    exact re_inner_self_nonneg hA _
  have hsq : energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 ≤
      energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 := by
    rw [hA.energyNorm_sq, hA.energyNorm_sq, hexp, re_inner_apply_add hA]
    linarith
  nlinarith [energyNorm_nonneg A (xstar - (iterate A b x₀ k).x),
    energyNorm_nonneg A (xstar - (iterate A b x₀ (k + 1)).x)]

omit hA in
/-- The **strict increase of $\|x_k\|$ for an indefinite system**, the analogue for CR and MINRES of
the theorem of [steihaug1983conjugate] ([fong2012cg], §4.2). Let $A$ be symmetric, possibly
indefinite, and let $x_k$, $r_k$ be the iterates and residuals of the conjugate residual
iteration for $Ax = b$ from $x_0 = 0$. If $r_\ell = 0$ and $\operatorname{Re} \langle r_j, A r_j
\rangle > 0$ for every $j < \ell$, then for every $i < \ell$
$$\|x_i\| < \|x_{i+1}\|.$$

Positivity is assumed for all $j$ up to the termination index $\ell$, not only up to $i$, and
nonvanishing is not enough. The proof of Theorem 2.2(d) in the paper expands $r_i = A(x_\ell -
x_i) = \sum_{m \ge i} \alpha_m A p_m$, so a single $\operatorname{Re} \langle r_m, A r_m \rangle
< 0$ with $m > i$ can make $\operatorname{Re} \langle r_i, p_j \rangle$ negative and break the
chain from (f) to (d) to (e). A separate hypothesis $\operatorname{Re} \langle A p_j, p_j
\rangle > 0$ would be redundant, since $\langle r_j, A p_j \rangle = \langle r_j, A r_j \rangle
\neq 0$ already forces $A p_j \neq 0$.

The result transfers to MINRES through `CR.isMinResidualIterate_of_no_breakdown`. -/
theorem norm_iterate_lt_of_pos (hAs : A.IsSymmetric) {ℓ : ℕ}
    (hstop : (iterate A b 0 ℓ).r = 0)
    (hpos : ∀ j < ℓ, 0 < RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)))
    {i : ℕ} (hi : i < ℓ) :
    ‖(iterate A b 0 i).x‖ < ‖(iterate A b 0 (i + 1)).x‖ := by
  have hzero : ∀ j, ℓ ≤ j → (iterate A b 0 j).r = 0 := fun j hj => by
    rw [iterate_eq_of_residual_eq_zero A b 0 hstop j hj]; exact hstop
  have hnn : ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)) := by
    intro j
    rcases lt_or_ge j ℓ with h | h
    · exact le_of_lt (hpos j h)
    · rw [hzero j h, inner_zero_left, map_zero]
  have hz : ∀ j, inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r) = 0 →
      (iterate A b 0 j).r = 0 := by
    intro j h
    rcases lt_or_ge j ℓ with hj | hj
    · exact absurd (hpos j hj) (by rw [h, map_zero]; exact lt_irrefl 0)
    · exact hzero j hj
  have hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b 0 m).r = 0 :=
    fun n => ⟨max n ℓ, le_max_left _ _, hzero _ (le_max_right _ _)⟩
  have hri := hpos i hi
  -- `⟪r_i, A p_i⟫ = ⟪r_i, A r_i⟫ ≠ 0`, so neither `A p_i` nor `p_i` can vanish
  have hqne : (iterate A b 0 i).q ≠ 0 := by
    intro h
    have hd := (invariant' b 0 hAs hz i).diag
    rw [q_eq] at h
    rw [h, inner_zero_right] at hd
    rw [← hd, map_zero] at hri
    exact lt_irrefl 0 hri
  have hpne : (iterate A b 0 i).p ≠ 0 := fun h => hqne (by rw [q_eq, h, map_zero])
  have hαpos : 0 < RCLike.re (alpha A (iterate A b 0 i)) := by
    rw [alpha_eq_ofReal b 0 hAs i, RCLike.ofReal_re]
    exact div_pos hri (pow_pos (norm_pos_iff.2 hqne) 2)
  have hαne : alpha A (iterate A b 0 i) ≠ 0 := fun h => by
    rw [h, map_zero] at hαpos; exact lt_irrefl 0 hαpos
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x
      (alpha A (iterate A b 0 i) • (iterate A b 0 i).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hAs]
    exact mul_nonneg (le_of_lt hαpos)
      (re_inner_iterate_direction_nonneg' b hAs hnn hz hterm i i)
  have hnz : 0 < ‖alpha A (iterate A b 0 i) • (iterate A b 0 i).p‖ := by
    rw [norm_smul]
    exact mul_pos (norm_pos_iff.2 hαne) (norm_pos_iff.2 hpne)
  have hsq : ‖(iterate A b 0 i).x‖ ^ 2 < ‖(iterate A b 0 (i + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [hnz]
  nlinarith [norm_nonneg (iterate A b 0 i).x, norm_nonneg (iterate A b 0 (i + 1)).x]

omit hA in
/-- **CR on a symmetric, possibly indefinite or singular, operator** ([fong2012cg], §2;
[choi2006iterative]). Let $A$ be symmetric, and suppose that no breakdown occurs before step
$k$: $\langle r_j, A r_j \rangle \neq 0$ and $A p_j \neq 0$ for every $j < k$. Then the iterate
$x_k$ of the conjugate residual iteration for $Ax = b$ from $x_0$ is the minimal-residual
iterate over $x_0 + \mathcal{K}_k(A, r_0)$.

Coercivity is not assumed: with it, this would be a special case of `CR.isMinResidualIterate`,
not the result for indefinite or singular operators. The hypothesis $A p_j \neq 0$ is stated for
the stored vector $q_j$, which equals $A p_j$ by `CR.q_eq`. -/
theorem isMinResidualIterate_of_no_breakdown (hA : A.IsSymmetric) (k : ℕ)
    (h1 : ∀ j < k, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) ≠ 0)
    (h2 : ∀ j < k, (iterate A b x₀ j).q ≠ 0) :
    IsMinResidualIterate A b x₀ k (iterate A b x₀ k).x := by
  have halpha : ∀ j < k, alpha A (iterate A b x₀ j) ≠ 0 := by
    intro j hj
    rw [alpha]
    exact div_ne_zero (h1 j hj) fun hq => h2 j hj (inner_self_eq_zero.1 hq)
  have hdeg : ∀ j < k, alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0 :=
    fun j hj h => absurd h (halpha j hj)
  have hbeta : ∀ j < k, beta A (iterate A b x₀ j) *
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) =
        inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ (j + 1)).r) := by
    intro j hj
    rw [beta_iterate, div_mul_cancel₀ _ (h1 j hj)]
  have hinv := invariant_of b x₀ hA k hdeg hbeta
  have hspan : Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
    le_antisymm (dirSpan_le_subspace A b x₀ k)
      (subspace_le_dirSpan b x₀ k fun i hi => apply_direction_mem_dirSpan b x₀ i (hdeg i hi))
  refine IsMinResidual.iff_isPetrovGalerkin.2 ⟨iterate_sub_mem A b x₀ k, ?_⟩
  rw [← residual_eq, ← hspan, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [← inner_conj_symm, hinv.rq i i.2, map_zero]

end CR

namespace Krylov

/-- **Lemma 6.21** of [saad2003iterative], the common lemma of GCR, ORTHOMIN and ORTHODIR. Let $A$
be a linear operator, and let $p_0, \dots, p_{m-1}$ be directions with $A p_i \neq 0$, with
$\langle A p_i, A p_j \rangle = 0$ for $i \neq j$, and with $\operatorname{span}\{p_0, \dots,
p_{m-1}\} = \mathcal{K}_m(A, r_0)$, where $r_0 = b - A x_0$. Define
$x_{j+1} = x_j + \gamma_j p_j$ with
$$\gamma_j = \frac{\langle A p_j, b - A x_j \rangle}{\langle A p_j, A p_j \rangle}.$$
Then $x_m$ is the minimal-residual iterate for $Ax = b$ over $x_0 + \mathcal{K}_m(A, r_0)$.

The inner product is conjugate-linear in its first argument, so over $\mathbb{C}$ the numerator
of $\gamma_j$ must be $\langle A p_j, r_j \rangle$, not $\langle r_j, A p_j \rangle$. The
iterates are a sequence `x : ℕ → E` with `x 0 = x₀`, and the hypotheses on the directions
concern only indices below $m$. -/
theorem isMinResidualIterate_of_orthogonal_directions {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ}
    (p : ℕ → E) (horth : ∀ i < m, ∀ j < m, i ≠ j → inner 𝕜 (A (p i)) (A (p j)) = 0)
    (hne : ∀ i < m, A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p i) = subspace A (b - A x₀) m)
    (x : ℕ → E) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j) :
    IsMinResidualIterate A b x₀ m (x m) := by
  -- the residual recurrence `r_{j+1} = r_j - c_j A p_j`
  have hres : ∀ j, b - A (x (j + 1)) = (b - A (x j)) -
      (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • A (p j) := by
    intro j
    rw [hstep j, map_add, map_smul]
    abel
  -- `x_j - x₀` lies in the span of the directions
  have hmem : ∀ j ≤ m, x j - x₀ ∈ Submodule.span 𝕜 (Set.range fun i : Fin m => p i) := by
    intro j hj
    induction j with
    | zero => rw [hx0, sub_self]; exact Submodule.zero_mem _
    | succ j ih =>
      have h : x (j + 1) - x₀ = (x j - x₀) +
          (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j := by
        rw [hstep j]; abel
      rw [h]
      exact Submodule.add_mem _ (ih (by omega)) (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩))
  -- the residual becomes orthogonal to `A p_i` at step `i + 1` and stays so
  have hkill : ∀ i < m, inner 𝕜 (A (p i)) (b - A (x (i + 1))) = 0 := by
    intro i hi
    rw [hres i, inner_sub_right, inner_smul_right,
      div_mul_cancel₀ _ (fun h => hne i hi (inner_self_eq_zero.1 h)), sub_self]
  have hstay : ∀ i < m, ∀ l, i + 1 ≤ l → l ≤ m → inner 𝕜 (A (p i)) (b - A (x l)) = 0 := by
    intro i hi l hl
    induction l, hl using Nat.le_induction with
    | base => exact fun _ => hkill i hi
    | succ l hl ih =>
      intro hlm
      rw [hres l, inner_sub_right, inner_smul_right, ih (by omega),
        horth i hi l (by omega) (by omega), mul_zero, sub_zero]
  refine IsMinResidual.iff_isPetrovGalerkin.2 ⟨hspan ▸ hmem m le_rfl, ?_⟩
  rw [← hspan, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hstay i i.2 m (by omega) le_rfl

end Krylov
