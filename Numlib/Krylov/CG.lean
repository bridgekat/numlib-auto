/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Projection.ConjugateDirection

/-!
# The conjugate gradient method

Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $b, x_0 \in E$. The conjugate gradient (CG) method of [hestenes1952methods]
starts from $r_0 = p_0 = b - A x_0$ and runs the two-term recurrence
$$\alpha_k = \frac{\langle r_k, r_k \rangle}{\langle A p_k, p_k \rangle}, \quad x_{k+1} = x_k +
  \alpha_k p_k, \quad r_{k+1} = r_k - \alpha_k A p_k, \quad \beta_k = \frac{\langle r_{k+1}, r_{k+1}
  \rangle}{\langle r_k, r_k \rangle}, \quad p_{k+1} = r_{k+1} + \beta_k p_k.$$
This is Algorithm 6.18 of [saad2003iterative]; see also [han2009theoretical], (5.6.2) and §9.4,
[fong2012cg], Table 2.1, [meurant2006lanczos], (3.2), and [choi2006iterative], Table 2.7. Here
$r_k = b - A x_k$ is the residual and $p_k$ is the search direction.

For a symmetric coercive $A$, the residuals are mutually orthogonal and the directions are mutually
$A$-conjugate ([saad2003iterative], Proposition 6.20). The directions and the residuals each span
the Krylov subspaces $\mathcal{K}_k(A, r_0)$, so $x_k$ is the Galerkin iterate of
$\mathcal{K}_k(A, r_0)$ and minimizes the energy norm of the error. CG is also the
conjugate-direction method along its own directions. The normalized residuals are the Lanczos
vectors up to sign, the Lanczos coefficients of $r_0$ are quotients of the CG coefficients, and the
Lanczos matrix factors as $T_m = L D L^T$ with $D = \operatorname{diag}(1/\alpha_j)$. The module
also proves the error identities of [hestenes1952methods], the theorem of [steihaug1983conjugate]
that the norms $\|x_k\|$ are nondecreasing when $x_0 = 0$, and the three-term form of CG
([saad2003iterative], §6.7.2).

## Main definitions

* `CG.State`: the state of the iteration, with the iterate $x_k$, the residual $r_k$ and the search
  direction $p_k$.
* `CG.alpha`, `CG.beta`, `CG.step`, `CG.init`, `CG.iterate`: the coefficients $\alpha_k$ and
  $\beta_k$, one step of the two-term recurrence, the initial state, and the state after $k$ steps.
* `CG.gamma`, `CG.rho`: the coefficients $\gamma_m$ and $\rho_m$ of the three-term form
  ([saad2003iterative], §6.7.2 and (6.97)).

## Main results

* `CG.inner_residual_eq_zero`, `CG.inner_apply_direction_eq_zero`: the residuals are mutually
  orthogonal and the directions are mutually $A$-conjugate ([saad2003iterative], Proposition 6.20).
* `CG.span_direction_eq`, `CG.span_residual_eq`: the first $k$ directions and the first $k$
  residuals each span $\mathcal{K}_k(A, r_0)$.
* `CG.isGalerkinIterate`: $x_k$ is the Galerkin iterate of $\mathcal{K}_k(A, r_0)$, so it minimizes
  the energy norm of the error.
* `CG.isConjugateFamily_direction`, `CG.iterate_x_eq_conjugateDirection_iterate`: CG is the
  conjugate-direction method along its own directions ([quarteroni2000numerical], §4.3.4).
* `CG.residual_eq_zero_of_grade_le`, `CG.residual_ne_zero_of_lt_grade`: CG terminates exactly at the
  grade of $r_0$.
* `CG.arnoldi_vec_eq`: the Lanczos vectors are $(-1)^k r_k / \|r_k\|$ ([saad2003iterative], (6.87)
  and (6.99); [meurant2006lanczos], (3.4)).
* `CG.lanczos_alpha_zero_eq`, `CG.lanczos_alpha_succ_eq`, `CG.lanczos_beta_eq`: the Lanczos
  coefficients of $r_0$ are $1/\alpha_0$, $1/\alpha_{k+1} + \beta_k/\alpha_k$ and
  $\sqrt{\beta_k}/\alpha_k$ ([saad2003iterative], (6.101)–(6.103); [golub2013matrix],
  §11.3.5–11.3.6).
* `CG.lanczos_tridiag_eq_ldl`: $T_m = L D L^T$ with $D = \operatorname{diag}(1/\alpha_j)$ and $L$
  unit lower bidiagonal with subdiagonal entries $\|r_{j+1}\| / \|r_j\|$ ([golub2013matrix],
  (11.3.15)).
* `CG.energyNorm_error_sq_sub`, `CG.energyNorm_error_sq_eq_sum`, `CG.norm_error_antitone`,
  `CG.energyNorm_error_antitone`: the error identities of [hestenes1952methods] (Theorems 6:1 and
  6:3), and the monotonicity of the error in the energy norm and in the Euclidean norm.
* `CG.norm_iterate_monotone`, `CG.norm_iterate_lt_of_re_inner_apply_direction_pos`: the theorem of
  [steihaug1983conjugate], the second form for a symmetric, possibly indefinite $A$.
* `CG.iterate_succ_eq_three_term`, `CG.residual_succ_eq_three_term`: the three-term form
  ([saad2003iterative], §6.7.2, Algorithm 6.19).

## Implementation notes

* The recurrence is a function on states, `CG.step`, iterated from `CG.init`. The residual is a
  field of the state, and `CG.residual_eq` proves that it equals $b - A x_k$.
* Divisions follow the Lean convention $x / 0 = 0$. So the iteration stops moving once $r_k = 0$:
  then $p_k = 0$, $\alpha_k = 0$ and every later state equals the state at step $k$. No hypothesis
  is needed to make the recurrence total.
* Most results assume `LinearMap.IsSymmetricCoercive A`. In the orthogonality relations and the span
  identities, coercivity is used only through the fact that a direction with
  $\langle A p_j, p_j \rangle = 0$ is $0$. The sign results behind the theorem of Steihaug also use
  $\operatorname{Re} \langle A p_j, p_j \rangle \ge 0$. The results with the suffix `_of_pos_prefix`
  replace coercivity by the hypothesis that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
  the steps $j < k$ taken so far, which is what a trust-region method checks; all of them except
  `CG.span_direction_eq_of_pos_prefix` also assume that $A$ is symmetric.
* In the three-term update of the iterates, the sign in front of $\gamma_m r_m$ is $+$.
  [saad2003iterative] prints $-$ in (6.98) and in Algorithm 6.19, but its own residual form (6.96)
  forces $+$; see `CG.iterate_succ_eq_three_term`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CG

/-- A **state of the CG iteration**: an iterate $x$, a residual $r$ and a search direction $p$, all
in $E$. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate $x_k$. -/
  x : E
  /-- The residual $r_k$, which equals $b - A x_k$ along the iteration (`CG.residual_eq`). -/
  r : E
  /-- The search direction $p_k$. -/
  p : E

/-- The **CG step length** of a state $(x, r, p)$:
$$\alpha = \frac{\langle r, r \rangle}{\langle A p, p \rangle}.$$
By the Lean convention, $\alpha = 0$ when $\langle A p, p \rangle = 0$. -/
noncomputable def alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r s.r / inner 𝕜 (A s.p) s.p

/-- **One CG step** from a state $(x, r, p)$. With the step length $\alpha = \langle r, r \rangle /
\langle A p, p \rangle$, the new state $(x', r', p')$ is
$$x' = x + \alpha p, \qquad r' = r - \alpha A p, \qquad p' = r' + \beta p, \qquad \beta =
  \frac{\langle r', r' \rangle}{\langle r, r \rangle}.$$
By the Lean convention, $\alpha = 0$ when $\langle A p, p \rangle = 0$, and $\beta = 0$ when
$r = 0$. -/
noncomputable def step (A : E →ₗ[𝕜] E) (s : State E) : State E :=
  let q := A s.p
  let α := alpha A s
  let r' := s.r - α • q
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.r s.r
  { x := s.x + α • s.p, r := r', p := r' + β • s.p }

/-- The **CG direction coefficient** of a state $(x, r, p)$:
$$\beta = \frac{\langle r', r' \rangle}{\langle r, r \rangle},$$
where $r'$ is the residual after one CG step. By the Lean convention, $\beta = 0$ when $r = 0$. -/
noncomputable def beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A s).r (step A s).r / inner 𝕜 s.r s.r

/-- The **initial CG state** $(x_0, r_0, p_0)$ with $r_0 = p_0 = b - A x_0$. -/
def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E := { x := x₀, r := b - A x₀, p := b - A x₀ }

/-- The **CG state after $k$ steps** from $x_0$, the $k$-fold application of `CG.step` to
`CG.init A b x₀`. Its components are written $x_k$, $r_k$ and $p_k$. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

/-- The iterate of the initial state is $x_0$. -/
@[simp] theorem init_x : (init A b x₀).x = x₀ := rfl

/-- The residual of the initial state is $b - A x_0$. -/
@[simp] theorem init_r : (init A b x₀).r = b - A x₀ := rfl

/-- The search direction of the initial state is $b - A x_0$. -/
@[simp] theorem init_p : (init A b x₀).p = b - A x₀ := rfl

/-- The CG state after zero steps is the initial state. -/
@[simp] theorem iterate_zero : iterate A b x₀ 0 = init A b x₀ := rfl

/-- The CG recurrence: the state after $k + 1$ steps is one `CG.step` applied to the state after $k$
steps.

This is the order in which the algorithm is read. Unfolding `(CG.step A)^[k + 1]` directly
applies the extra step to the initial state instead, because `Function.iterate` peels a step off
the front. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update of one CG step: $x' = x + \alpha p$. -/
theorem step_x (s : State E) : (step A s).x = s.x + alpha A s • s.p := rfl

/-- The residual update of one CG step: $r' = r - \alpha A p$. -/
theorem step_r (s : State E) : (step A s).r = s.r - alpha A s • A s.p := rfl

/-- The direction update of one CG step: $p' = r' + \beta p$. -/
theorem step_p (s : State E) : (step A s).p = (step A s).r + beta A s • s.p := rfl

/-- The residual of the CG state is the true residual: for every $k$,
$$r_k = b - A x_k.$$
This holds for every operator $A$. -/
theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_r, step_x, ih, map_add, map_smul, sub_sub]

/-! ### Unfolding the recurrence -/

/-- The iterate update along the iteration: $x_{k+1} = x_k + \alpha_k p_k$. -/
theorem iterate_succ_x (k : ℕ) : (iterate A b x₀ (k + 1)).x =
    (iterate A b x₀ k).x + alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ, step_x]

/-- The residual update along the iteration: $r_{k+1} = r_k - \alpha_k A p_k$. -/
theorem iterate_succ_r (k : ℕ) : (iterate A b x₀ (k + 1)).r =
    (iterate A b x₀ k).r - alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p := by
  rw [iterate_succ, step_r]

/-- The direction update along the iteration: $p_{k+1} = r_{k+1} + \beta_k p_k$. -/
theorem iterate_succ_p (k : ℕ) : (iterate A b x₀ (k + 1)).p =
    (iterate A b x₀ (k + 1)).r + beta A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ]; exact step_p A _

/-- The direction coefficient along the iteration is a quotient of inner products: $\beta_k =
\langle r_{k+1}, r_{k+1} \rangle / \langle r_k, r_k \rangle$, that is
$\|r_{k+1}\|^2 / \|r_k\|^2$. -/
theorem beta_iterate (k : ℕ) : beta A (iterate A b x₀ k) =
    inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r /
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
  rw [beta, iterate_succ]

/-- The first search direction is the first residual: $p_0 = r_0$. -/
theorem direction_zero : (iterate A b x₀ 0).p = (iterate A b x₀ 0).r := rfl

/-- The step along $A p_k$ is the change of the residual: $\alpha_k A p_k = r_k - r_{k+1}$. This is
the only way in which $A$ enters the residual recurrence. -/
theorem alpha_smul_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p =
      (iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r := by
  rw [iterate_succ_r]; abel

/-- If the residual vanishes, so does the search direction: $r_k = 0$ implies $p_k = 0$, because
then $\beta_{k-1} = 0$. -/
theorem direction_eq_zero_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ k).p = 0 := by
  cases k with
  | zero => rw [direction_zero]; exact hr
  | succ k =>
    rw [iterate_succ_p, hr, beta_iterate, hr, inner_zero_left, zero_div, zero_smul, add_zero]

/-- A state with $r = 0$ and $p = 0$ is fixed by a CG step. This uses the Lean convention
$x / 0 = 0$. -/
theorem step_eq_self_of_residual_eq_zero (s : State E) (hr : s.r = 0) (hp : s.p = 0) :
    step A s = s := by
  obtain ⟨x, r, p⟩ := s
  simp_all [step]

/-- Once the residual vanishes, the iteration is stationary: if $r_k = 0$, then the state after $l$
steps equals the state after $k$ steps for every $l \ge k$.

The form with the later index written as $k + j$ is `CG.iterate_eq_of_residual_eq_zero`. -/
theorem iterate_eq_of_residual_eq_zero' {k : ℕ} (hk : (iterate A b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate A b x₀ l = iterate A b x₀ k := by
  induction l with
  | zero => obtain rfl : k = 0 := Nat.le_zero.1 hl; rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · rw [iterate_succ, ih (Nat.lt_succ_iff.1 h), step_eq_self_of_residual_eq_zero A _ hk
        (direction_eq_zero_of_residual_eq_zero A b x₀ hk)]
    · obtain rfl : k = l + 1 := le_antisymm hl h
      rfl

/-- If $r_k = 0$, then $r_{k+1} = 0$. -/
theorem residual_succ_eq_zero_of_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ (k + 1)).r = 0 := by
  rw [iterate_eq_of_residual_eq_zero' A b x₀ hr (k + 1) (Nat.le_succ k), hr]

/-! ### Elementary consequences of the recurrence, before any orthogonality -/

private theorem inner_self_eq_ofReal_norm_sq (x : E) : inner 𝕜 x x = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  ring

private theorem conj_beta (s : State E) : (starRingEnd 𝕜) (beta A s) = beta A s := by
  rw [beta, map_div₀, inner_self_conj, inner_self_conj]

/-- The identity $\beta_k \langle r_k, r_k \rangle = \langle r_{k+1}, r_{k+1} \rangle$, which holds
also when $r_k = 0$. -/
private theorem beta_mul_inner_self (k : ℕ) :
    beta A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r =
      inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r := by
  by_cases h : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r = 0
  · rw [h, mul_zero, residual_succ_eq_zero_of_eq_zero A b x₀ (inner_self_eq_zero.1 h),
      inner_zero_left]
  · rw [beta_iterate, div_mul_cancel₀ _ h]

/-- If $v$ is orthogonal to $p_0, \dots, p_j$, then $v$ is orthogonal to $r_j$, because each
residual is a combination of two consecutive directions. -/
private theorem inner_residual_eq_zero_of_inner_direction {j : ℕ} {v : E}
    (h : ∀ l ≤ j, inner 𝕜 v (iterate A b x₀ l).p = 0) :
    inner 𝕜 v (iterate A b x₀ j).r = 0 := by
  cases j with
  | zero => rw [← direction_zero]; exact h 0 le_rfl
  | succ i =>
    have hi : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [hi, inner_sub_right, inner_smul_right, h _ le_rfl, h i (Nat.le_succ i), mul_zero,
      sub_zero]

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

/-- The residual lies in a Krylov subspace: $r_k \in \mathcal{K}_{k+1}(A, r_0)$ with
$r_0 = b - A x_0$. This holds for every operator $A$. -/
theorem residual_mem_subspace (k : ℕ) : (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) :=
  (residual_direction_mem_subspace A b x₀ k).1

/-- The search direction lies in a Krylov subspace: $p_k \in \mathcal{K}_{k+1}(A, r_0)$ with
$r_0 = b - A x_0$. This holds for every operator $A$. -/
theorem direction_mem_subspace (k : ℕ) : (iterate A b x₀ k).p ∈ subspace A (b - A x₀) (k + 1) :=
  (residual_direction_mem_subspace A b x₀ k).2

/-- The span of the first $k$ search directions. -/
private noncomputable def dirSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p)

/-- The span of the first $k$ residuals. -/
private noncomputable def resSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).r)

private theorem direction_mem_dirSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).p ∈ dirSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem residual_mem_resSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).r ∈ resSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem dirSpan_mono {k l : ℕ} (h : k ≤ l) : dirSpan A b x₀ k ≤ dirSpan A b x₀ l := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact direction_mem_dirSpan A b x₀ (lt_of_lt_of_le i.2 h)

private theorem resSpan_mono {k l : ℕ} (h : k ≤ l) : resSpan A b x₀ k ≤ resSpan A b x₀ l := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact residual_mem_resSpan A b x₀ (lt_of_lt_of_le i.2 h)

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

private theorem direction_mem_resSpan (i : ℕ) : (iterate A b x₀ i).p ∈ resSpan A b x₀ (i + 1) := by
  induction i with
  | zero => rw [direction_zero]; exact residual_mem_resSpan A b x₀ Nat.zero_lt_one
  | succ i ih =>
    rw [iterate_succ_p]
    exact Submodule.add_mem _ (residual_mem_resSpan A b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (resSpan_mono A b x₀ (by omega) ih))

private theorem dirSpan_le_subspace (k : ℕ) : dirSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (direction_mem_subspace A b x₀ i)

private theorem resSpan_le_subspace (k : ℕ) : resSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (residual_mem_subspace A b x₀ i)

private theorem dirSpan_le_resSpan (k : ℕ) : dirSpan A b x₀ k ≤ resSpan A b x₀ k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact resSpan_mono A b x₀ i.2 (direction_mem_resSpan A b x₀ i)

private theorem resSpan_le_dirSpan (k : ℕ) : resSpan A b x₀ k ≤ dirSpan A b x₀ k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact dirSpan_mono A b x₀ i.2 (residual_mem_dirSpan A b x₀ i)

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-! ### The joint induction ([saad2003iterative], Proposition 6.20) -/

private theorem re_inner_apply_self_nonneg (x : E) : 0 ≤ RCLike.re (inner 𝕜 (A x) x) := by
  obtain ⟨c, hc, h⟩ := hA.isCoercive
  exact le_trans (by positivity) (h x)

private theorem eq_zero_of_inner_apply_self_eq_zero {x : E} (h : inner 𝕜 (A x) x = 0) : x = 0 := by
  by_contra hx
  have := hA.isCoercive.inner_self_pos hx
  rw [h, map_zero] at this
  exact lt_irrefl 0 this

omit hA in
private theorem conj_alpha (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (alpha A s) = alpha A s := by
  rw [alpha, map_div₀, inner_self_conj, inner_conj_symm, ← hAs]

omit hA in
/-- The identity $\alpha_k \langle A p_k, p_k \rangle = \langle r_k, r_k \rangle$, which holds also
at a breakdown, under any hypothesis that makes a direction with
$\langle A p_k, p_k \rangle = 0$ vanish and with $\langle r_k, p_k \rangle = \langle r_k, r_k
\rangle$. -/
private theorem alpha_mul_inner_apply_direction' (k : ℕ)
    (hdeg : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0 →
      (iterate A b x₀ k).p = 0)
    (hdiag : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r) :
    alpha A (iterate A b x₀ k) * inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
  by_cases h : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0
  · rw [h, mul_zero, ← hdiag, hdeg h, inner_zero_right]
  · rw [alpha, div_mul_cancel₀ _ h]

omit hA in
/-- If a direction with $\langle A p_k, p_k \rangle = 0$ vanishes, then $\alpha_k = 0$ implies
$A p_k = 0$. -/
private theorem apply_direction_eq_zero_of_alpha_eq_zero {k : ℕ}
    (hdeg : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0 →
      (iterate A b x₀ k).p = 0)
    (h : alpha A (iterate A b x₀ k) = 0) : A (iterate A b x₀ k).p = 0 := by
  rcases div_eq_zero_iff.1 h with h' | h'
  · rw [direction_eq_zero_of_residual_eq_zero A b x₀ (inner_self_eq_zero.1 h'), map_zero]
  · rw [hdeg h', map_zero]

omit hA in
/-- If a direction with $\langle A p_j, p_j \rangle = 0$ vanishes, then
$\langle v, A p_j \rangle = 0$ for every $v$ orthogonal to both $r_j$ and $r_{j+1}$. -/
private theorem inner_apply_direction_eq_zero_of {j : ℕ} {v : E}
    (hdeg : inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p = 0 →
      (iterate A b x₀ j).p = 0)
    (h1 : inner 𝕜 v (iterate A b x₀ j).r = 0)
    (h2 : inner 𝕜 v (iterate A b x₀ (j + 1)).r = 0) :
    inner 𝕜 v (A (iterate A b x₀ j).p) = 0 := by
  by_cases hα : alpha A (iterate A b x₀ j) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀ hdeg hα, inner_zero_right]
  · have h : alpha A (iterate A b x₀ j) * inner 𝕜 v (A (iterate A b x₀ j).p) = 0 := by
      rw [← inner_smul_right, alpha_smul_apply_direction, inner_sub_right, h1, h2, sub_zero]
    exact (mul_eq_zero.1 h).resolve_left hα

/-- The joint CG invariant at step $k$ ([saad2003iterative], Proposition 6.20): $r_k$ is orthogonal
to all earlier directions, $p_k$ is $A$-conjugate to all earlier directions, and $\langle r_k,
p_k \rangle = \langle r_k, r_k \rangle$. -/
private structure Invariant (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Prop where
  /-- The residual is orthogonal to the earlier directions: $\langle r_k, p_j \rangle = 0$ for
  $j < k$. -/
  rp : ∀ j < k, inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ j).p = 0
  /-- The direction is $A$-conjugate to the earlier directions: $\langle A p_k, p_j \rangle = 0$ for
  $j < k$. -/
  pp : ∀ j < k, inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ j).p = 0
  /-- The diagonal identity $\langle r_k, p_k \rangle = \langle r_k, r_k \rangle$. -/
  diag : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).p =
    inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r

omit hA in
/-- For a symmetric $A$, the joint invariant holds at step $k$ as soon as every direction $p_j$,
$j < k$, with $\langle A p_j, p_j \rangle = 0$ is $0$, so that the theorem of
[steihaug1983conjugate] for indefinite $A$ can reuse the induction. -/
private theorem invariant_of (hAs : A.IsSymmetric) (k : ℕ) :
    (∀ j < k, inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p = 0 →
      (iterate A b x₀ j).p = 0) → Invariant A b x₀ k := by
  induction k with
  | zero =>
    exact fun _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j), by rw [direction_zero]⟩
  | succ k ihk =>
    intro hdeg
    have ih := ihk fun j hj => hdeg j (by omega)
    -- Step 1: `r_{k+1} ⟂ p_j` for `j ≤ k`.
    have rp : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ j).p = 0 := by
      intro j hj
      rw [iterate_succ_r, inner_sub_left, inner_smul_left, conj_alpha hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.rp j h, ih.pp j h, mul_zero, sub_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        rw [ih.diag, alpha_mul_inner_apply_direction' b x₀ j (hdeg j (by omega)) ih.diag, sub_self]
    -- Step 2: `r_{k+1} ⟂ r_j` for `j ≤ k`.
    have rr : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ j).r = 0 :=
      fun j hj => inner_residual_eq_zero_of_inner_direction A b x₀ fun l hl => rp l (by omega)
    refine ⟨rp, fun j hj => ?_, ?_⟩
    · -- Step 3: `p_{k+1}` is `A`-conjugate to `p_j` for `j ≤ k`.
      rw [iterate_succ_p, map_add, map_smul, inner_add_left, inner_smul_left, conj_beta, hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.pp j h, mul_zero, add_zero,
          inner_apply_direction_eq_zero_of b x₀ (hdeg j (by omega)) (rr j (by omega))
            (rr (j + 1) (by omega))]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        by_cases hα : alpha A (iterate A b x₀ j) = 0
        · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀ (hdeg j (by omega)) hα,
            inner_zero_right, inner_zero_left, mul_zero, add_zero]
        · have key : alpha A (iterate A b x₀ j) *
              (inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ j).p) +
                beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) = 0 := by
            rw [mul_add, ← inner_smul_right, alpha_smul_apply_direction, inner_sub_right,
              rr j (by omega), zero_sub, inner_self_eq_ofReal_norm_sq]
            rw [show alpha A (iterate A b x₀ j) * (beta A (iterate A b x₀ j) *
                inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) =
                beta A (iterate A b x₀ j) * (alpha A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) by ring,
              alpha_mul_inner_apply_direction' b x₀ j (hdeg j (by omega)) ih.diag,
              beta_mul_inner_self A b x₀ j, inner_self_eq_ofReal_norm_sq]
            ring
          exact (mul_eq_zero.1 key).resolve_left hα
    · -- Step 4: `⟪r_{k+1}, p_{k+1}⟫ = ⟪r_{k+1}, r_{k+1}⟫`.
      rw [iterate_succ_p, inner_add_right, inner_smul_right, rp k (Nat.lt_succ_self k), mul_zero,
        add_zero]

private theorem invariant (k : ℕ) : Invariant A b x₀ k :=
  invariant_of b x₀ hA.isSymmetric k fun _ _ h => eq_zero_of_inner_apply_self_eq_zero hA h

/-! ### The named orthogonality relations -/

/-- Let $A$ be symmetric and coercive. Then for every $k$,
$$\alpha_k \langle A p_k, p_k \rangle = \langle r_k, r_k \rangle.$$
So the step length solves the one-dimensional Galerkin condition along $p_k$. The identity holds
also after the iteration has converged, when both sides are $0$. -/
theorem alpha_mul_inner_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) * inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r :=
  alpha_mul_inner_apply_direction' b x₀ k
    (fun h => eq_zero_of_inner_apply_self_eq_zero hA h) (invariant b x₀ hA k).diag

/-- **Well-definedness of the step length.** Let $A$ be symmetric and coercive. If $r_k \neq 0$,
then
$$\operatorname{Re} \langle A p_k, p_k \rangle > 0.$$
-/
theorem re_inner_apply_direction_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p) := by
  refine hA.isCoercive.inner_self_pos fun hp => hr ?_
  have h := (invariant b x₀ hA k).diag
  rw [hp, inner_zero_right] at h
  exact inner_self_eq_zero.1 h.symm

omit hA in
/-- Once the residual vanishes, the iteration is stationary: if $r_k = 0$, then the state after
$k + j$ steps equals the state after $k$ steps for every $j$. This holds for every operator $A$.

This is `CG.iterate_eq_of_residual_eq_zero'` with the later index written as $k + j$. -/
theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) (j : ℕ) :
    iterate A b x₀ (k + j) = iterate A b x₀ k :=
  iterate_eq_of_residual_eq_zero' A b x₀ hr (k + j) (Nat.le_add_right k j)

/-- **Orthogonality of the residuals** ([saad2003iterative], Proposition 6.20(i)). Let $A$ be
symmetric and coercive. Then for all $i \neq j$,
$$\langle r_i, r_j \rangle = 0.$$
-/
theorem inner_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0 := by
  have key : ∀ m n : ℕ, n < m → inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ n).r = 0 :=
    fun m n hmn => inner_residual_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant b x₀ hA m).rp l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, key j i h', map_zero]
  · exact key i j h'

/-- **Conjugacy of the directions** ([saad2003iterative], Proposition 6.20(ii)). Let $A$ be
symmetric and coercive. Then for all $i \neq j$,
$$\langle A p_i, p_j \rangle = 0.$$
-/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (iterate A b x₀ j).p = 0 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [hA.isSymmetric, ← inner_conj_symm, (invariant b x₀ hA j).pp i h', map_zero]
  · exact (invariant b x₀ hA i).pp j h'

/-- Let $A$ be symmetric and coercive. Then the residual is orthogonal to the earlier directions:
for $j < i$,
$$\langle r_i, p_j \rangle = 0.$$
-/
theorem inner_residual_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p = 0 :=
  (invariant b x₀ hA i).rp j h

/-- Let $A$ be symmetric and coercive. Then for $i \le j$,
$$\langle r_i, p_j \rangle = \|r_j\|^2.$$

The right-hand side is $\|r_j\|^2$, not $\|r_i\|^2$. Expand $p_j = \sum_{l \le j}
\bigl(\prod_{m=l}^{j-1} \beta_m\bigr) r_l$ and use $\prod_{m=i}^{j-1} \beta_m = \|r_j\|^2 /
\|r_i\|^2$; already $\langle r_0, p_1 \rangle = \beta_0 \|r_0\|^2 = \|r_1\|^2$. The two values
agree at $i = j$, which is the only case that `CG.inner_residual_direction_eq_zero` leaves open. -/
theorem inner_residual_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p =
      (‖(iterate A b x₀ j).r‖ ^ 2 : ℝ) := by
  induction j, h using Nat.le_induction with
  | base => rw [(invariant b x₀ hA i).diag, inner_self_eq_ofReal_norm_sq]
  | succ j hij ih =>
    rw [iterate_succ_p, inner_add_right, inner_smul_right, ih,
      inner_residual_eq_zero b x₀ hA (show i ≠ j + 1 by omega), zero_add,
      ← inner_self_eq_ofReal_norm_sq, ← inner_self_eq_ofReal_norm_sq, beta_mul_inner_self A b x₀ j]

/-! ### Spans and the Galerkin property -/

omit hA in
private theorem apply_direction_mem_dirSpan_of_alpha_ne_zero (i : ℕ)
    (hα : alpha A (iterate A b x₀ i) ≠ 0) :
    A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2) := by
  have h : A (iterate A b x₀ i).p = (alpha A (iterate A b x₀ i))⁻¹ •
      ((iterate A b x₀ i).r - (iterate A b x₀ (i + 1)).r) := by
    rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ i))
    (residual_mem_dirSpan A b x₀ (i + 1)))

private theorem apply_direction_mem_dirSpan (i : ℕ) :
    A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2) := by
  by_cases hα : alpha A (iterate A b x₀ i) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀
      (fun h => eq_zero_of_inner_apply_self_eq_zero hA h) hα]
    exact Submodule.zero_mem _
  · exact apply_direction_mem_dirSpan_of_alpha_ne_zero b x₀ i hα

omit hA in
private theorem pow_apply_mem_dirSpan (k : ℕ)
    (hstep : ∀ j < k, A (iterate A b x₀ j).p ∈ dirSpan A b x₀ (j + 2))
    (ih : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k) :
    (A ^ k) (b - A x₀) ∈ dirSpan A b x₀ (k + 1) := by
  cases k with
  | zero =>
    have h : (iterate A b x₀ 0).p ∈ dirSpan A b x₀ 1 :=
      direction_mem_dirSpan A b x₀ Nat.zero_lt_one
    simpa [init] using h
  | succ j =>
    have hmem : (A ^ j) (b - A x₀) ∈ dirSpan A b x₀ (j + 1) :=
      ih (pow_apply_mem_subspace A _ (Nat.lt_succ_self j))
    have hpow : (A ^ (j + 1)) (b - A x₀) = A ((A ^ j) (b - A x₀)) := by rw [pow_succ']; rfl
    have hcomap : dirSpan A b x₀ (j + 1) ≤ Submodule.comap A (dirSpan A b x₀ (j + 1 + 1)) := by
      rw [dirSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact dirSpan_mono A b x₀ (by omega) (hstep l l.isLt)
    rw [hpow]
    exact hcomap hmem

omit hA in
private theorem subspace_le_dirSpan_of_apply (k : ℕ)
    (hstep : ∀ j : ℕ, j + 1 < k → A (iterate A b x₀ j).p ∈ dirSpan A b x₀ (j + 2)) :
    subspace A (b - A x₀) k ≤ dirSpan A b x₀ k := by
  induction k with
  | zero => rw [subspace_zero]; exact bot_le
  | succ k ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    rw [subspace, Submodule.span_le, Set.range_subset_iff]
    intro i
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · exact dirSpan_mono A b x₀ (Nat.le_succ k) (hprev (pow_apply_mem_subspace A _ h))
    · have h' : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) h
      rw [h']
      exact pow_apply_mem_dirSpan b x₀ k (fun j hj => hstep j (by omega)) hprev

private theorem subspace_le_dirSpan (k : ℕ) : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k :=
  subspace_le_dirSpan_of_apply b x₀ k fun j _ => apply_direction_mem_dirSpan b x₀ hA j

/-- Let $A$ be symmetric and coercive. Then for every $k$, the first $k$ search directions span the
Krylov subspace:
$$\operatorname{span}\{p_0, \dots, p_{k-1}\} = \mathcal{K}_k(A, r_0), \qquad r_0 = b - A x_0.$$
-/
theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
  le_antisymm (dirSpan_le_subspace A b x₀ k) (subspace_le_dirSpan b x₀ hA k)

/-- Let $A$ be symmetric and coercive. Then for every $k$, the first $k$ residuals span the Krylov
subspace:
$$\operatorname{span}\{r_0, \dots, r_{k-1}\} = \mathcal{K}_k(A, r_0), \qquad r_0 = b - A x_0.$$
-/
theorem span_residual_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).r) =
      subspace A (b - A x₀) k :=
  le_antisymm (resSpan_le_subspace A b x₀ k)
    ((subspace_le_dirSpan b x₀ hA k).trans (dirSpan_le_resSpan A b x₀ k))

omit hA in
/-- CG stays in the affine Krylov space: for every $k$,
$$x_k - x_0 \in \mathcal{K}_k(A, r_0), \qquad r_0 = b - A x_0.$$
This holds for every operator $A$.

This is the membership half of the Galerkin property `CG.isGalerkinIterate`. It follows from the
recurrence alone, since each correction is a multiple of a direction
$p_j \in \mathcal{K}_{j+1}(A, r_0)$. -/
theorem iterate_sub_mem (k : ℕ) : (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k := by
  induction k with
  | zero => simp [init]
  | succ k ih =>
    have h : (iterate A b x₀ (k + 1)).x - x₀ = ((iterate A b x₀ k).x - x₀) +
        alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
      rw [iterate_succ_x]; abel
    rw [h]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ (direction_mem_subspace A b x₀ k))

/-- **CG is a Galerkin method.** Let $A$ be symmetric and coercive. Then for every $k$, the iterate
$x_k$ is the Galerkin iterate of $\mathcal{K}_k(A, r_0)$ with $r_0 = b - A x_0$:
$$x_k \in x_0 + \mathcal{K}_k(A, r_0), \qquad b - A x_k \perp \mathcal{K}_k(A, r_0).$$

The specification is `Krylov.IsGalerkinIterate`. By
`Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf`, $x_k$ therefore minimizes the energy norm
of the error over $x_0 + \mathcal{K}_k(A, r_0)$. -/
theorem isGalerkinIterate (k : ℕ) : IsGalerkinIterate A b x₀ k (iterate A b x₀ k).x := by
  refine ⟨iterate_sub_mem b x₀ k, ?_⟩
  rw [← residual_eq, ← span_direction_eq b x₀ hA k]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [← inner_conj_symm, inner_residual_direction_eq_zero b x₀ hA i.2, map_zero]

/-! ### CG as a conjugate-direction method -/

/-- Let $A$ be symmetric and coercive. Then the CG directions form an $A$-conjugate family:
$\langle A p_k, p_m \rangle = 0$ for all $k \neq m$.

The family is `ConjugateDirection.IsConjugateFamily`. This is `CG.inner_apply_direction_eq_zero`
in that form, and it holds also past the grade, where the directions are $0$. -/
theorem isConjugateFamily_direction :
    ConjugateDirection.IsConjugateFamily A fun k => (iterate A b x₀ k).p :=
  fun _ _ h => inner_apply_direction_eq_zero b x₀ hA h

/-- **CG is the conjugate-direction method along its own directions** ([quarteroni2000numerical],
§4.3.4 and §7.2.4). Let $A$ be symmetric and coercive. Then for every $k$, the CG iterate $x_k$
equals the iterate of the conjugate-direction method with exact line search along the directions
$p_0, p_1, \dots$ from $x_0$:
$$x_{j+1} = x_j + \frac{\langle p_j, b - A x_j \rangle}{\langle p_j, A p_j \rangle} \, p_j.$$

The CG step length $\langle r_k, r_k \rangle / \langle A p_k, p_k \rangle$ equals the exact
line-search value because $\langle p_k, r_k \rangle = \|r_k\|^2$
(`CG.inner_residual_direction_eq`). With `ConjugateDirection.iterate_eq_of_finrank_le`, this is
how [quarteroni2000numerical] derive the finite termination of Theorem 4.12 from Theorem 4.11.
This library proves termination instead by `CG.residual_eq_zero_of_grade_le` with
`Krylov.grade_le_finrank`. -/
theorem iterate_x_eq_conjugateDirection_iterate (k : ℕ) :
    (iterate A b x₀ k).x = ConjugateDirection.iterate A b (fun k => (iterate A b x₀ k).p) x₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ConjugateDirection.iterate_succ_eq, ← ih, ← residual_eq, iterate_succ_x, alpha,
      ← hA.isSymmetric, ← inner_conj_symm (iterate A b x₀ k).p (iterate A b x₀ k).r,
      inner_residual_direction_eq b x₀ hA le_rfl, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_pow]

/-! ### Identification with the Lanczos vectors -/

omit hA in
/-- If $r_k \neq 0$, then $r_j \neq 0$ for every $j \le k$. -/
private theorem residual_ne_zero_of_le {k j : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) (hj : j ≤ k) :
    (iterate A b x₀ j).r ≠ 0 := fun h =>
  hr (by rw [iterate_eq_of_residual_eq_zero' A b x₀ h k hj]; exact h)

/-- If $r_k \neq 0$, then the step length $\alpha_k$ is a positive real number. -/
private theorem alpha_eq_ofReal_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ alpha A (iterate A b x₀ k) = (s : 𝕜) := by
  refine ⟨‖(iterate A b x₀ k).r‖ ^ 2 /
      RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p),
    div_pos (pow_pos (norm_pos_iff.2 hr) 2) (re_inner_apply_direction_pos b x₀ hA hr), ?_⟩
  rw [RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq,
    hA.isSymmetric.coe_re_inner_apply_self, alpha]

/-- If $r_k \neq 0$, then $\prod_{j < k} (-\alpha_j) = (-1)^k c$ for a real $c > 0$. -/
private theorem prod_neg_alpha (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) = (-1 : 𝕜) ^ k * (c : 𝕜) := by
  induction k with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ k ih =>
    have hk := residual_ne_zero_of_le b x₀ hr (Nat.le_succ k)
    obtain ⟨c, hcpos, hc⟩ := ih hk
    obtain ⟨s, hspos, hs⟩ := alpha_eq_ofReal_pos b x₀ hA hk
    refine ⟨c * s, mul_pos hcpos hspos, ?_⟩
    rw [Finset.prod_range_succ, hc, hs]
    push_cast
    ring

omit hA in
/-- Both $r_k$ and $p_k$ lie in $\bigl(\prod_{j<k} (-\alpha_j)\bigr) A^k r_0 + \mathcal{K}_k(A,
r_0)$. -/
private theorem leading (k : ℕ) :
    (iterate A b x₀ k).r -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) ∈
      subspace A (b - A x₀) k ∧
    (iterate A b x₀ k).p -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) ∈
      subspace A (b - A x₀) k := by
  induction k with
  | zero => constructor <;> · simp [iterate, init]
  | succ k ih =>
    obtain ⟨ihr, ihp⟩ := ih
    have hpow : (A ^ (k + 1)) (b - A x₀) = A ((A ^ k) (b - A x₀)) := by rw [pow_succ']; rfl
    have hmono := subspace_mono A (b - A x₀) (Nat.le_succ k)
    have hmem : (A ^ k) (b - A x₀) ∈ subspace A (b - A x₀) (k + 1) :=
      pow_apply_mem_subspace A _ (Nat.lt_succ_self k)
    have hAp : A (iterate A b x₀ k).p -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) ∈
          subspace A (b - A x₀) (k + 1) := by
      have h := map_subspace_le A (b - A x₀) k ⟨_, ihp, rfl⟩
      rwa [map_sub, map_smul, ← hpow] at h
    have hr : (iterate A b x₀ (k + 1)).r -
        (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) ∈
          subspace A (b - A x₀) (k + 1) := by
      have key : (iterate A b x₀ (k + 1)).r -
          (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) =
        ((iterate A b x₀ k).r -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) +
          (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) -
          alpha A (iterate A b x₀ k) • (A (iterate A b x₀ k).p -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀)) := by
        rw [iterate_succ_r, Finset.prod_range_succ]
        module
      rw [key]
      exact Submodule.sub_mem _
        (Submodule.add_mem _ (hmono ihr) (Submodule.smul_mem _ _ hmem))
        (Submodule.smul_mem _ _ hAp)
    refine ⟨hr, ?_⟩
    have key : (iterate A b x₀ (k + 1)).p -
        (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) =
      ((iterate A b x₀ (k + 1)).r -
          (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀)) +
        beta A (iterate A b x₀ k) • ((iterate A b x₀ k).p -
          (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) +
        beta A (iterate A b x₀ k) •
          ((∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) := by
      rw [iterate_succ_p]
      module
    rw [key]
    exact Submodule.add_mem _ (Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ihp)))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hmem))

/-- **The CG residuals are the Lanczos vectors up to sign.** Let $A$ be symmetric and coercive, let
$r_0 = b - A x_0$, and let $v_k$ be the Lanczos vector of step $k$ of $A$ from $r_0$. If
$r_k \neq 0$, then
$$v_k = (-1)^k \frac{r_k}{\|r_k\|}.$$
This is (6.87) and (6.99) of [saad2003iterative], and (3.4) of [meurant2006lanczos].

[saad2003iterative], (6.99), records only that $r_k$ is some multiple of the Lanczos vector,
which is all that §6.7.3 there needs, because it reads the tridiagonal entries off quotients and
absolute values. Here the scalar is fixed; its sign comes from the leading coefficient
$\prod_{j<k} (-\alpha_j)$ of $r_k$. The Lanczos vector is `Arnoldi.vec A (b - A x₀) k`. -/
theorem arnoldi_vec_eq (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    Arnoldi.vec A (b - A x₀) k =
      ((-1 : 𝕜) ^ k * (‖(iterate A b x₀ k).r‖⁻¹ : ℝ)) • (iterate A b x₀ k).r := by
  have hveq : Arnoldi.vec A (b - A x₀) k =
      InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) (b - A x₀)) k := rfl
  -- `v_k` and `r_k` are orthogonal to `𝒦_k`, and both lie in `𝒦_{k+1}`
  have hvperp : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 u (Arnoldi.vec A (b - A x₀) k) = 0 :=
    (Submodule.mem_orthogonal _ _).1 (Arnoldi.vec_mem_orthogonal A (b - A x₀) k)
  have hvperp' : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) u = 0 := fun u hu => by
    rw [← inner_conj_symm, hvperp u hu, map_zero]
  have hrperp : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 u (iterate A b x₀ k).r = 0 := by
    have h := (isGalerkinIterate b x₀ hA k).orth
    rw [← residual_eq A b x₀ k] at h
    exact (Submodule.mem_orthogonal _ _).1 h
  have hrmem : (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) :=
    residual_mem_subspace A b x₀ k
  -- `v_k ≠ 0`: otherwise `𝒦_{k+1} = 𝒦_k` and `r_k ⟂ r_k`
  have hvne : Arnoldi.vec A (b - A x₀) k ≠ 0 := by
    intro h0
    refine hr (inner_self_eq_zero.1 (hrperp _ ?_))
    have hle : subspace A (b - A x₀) (k + 1) ≤ subspace A (b - A x₀) k := by
      rw [← Arnoldi.span_vec A (b - A x₀) (k + 1), Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i k with h | h
      · rw [← Arnoldi.span_vec A (b - A x₀) k]
        exact Submodule.subset_span ⟨i, h, rfl⟩
      · obtain rfl : i = k := le_antisymm (Nat.lt_succ_iff.1 hi) h
        rw [h0]
        exact Submodule.zero_mem _
    exact hle hrmem
  have hnorm : ‖Arnoldi.vec A (b - A x₀) k‖ = 1 := by
    rw [hveq]
    exact InnerProductSpace.gramSchmidtNormed_unit_length' (by rwa [hveq] at hvne)
  -- `r_k` is a multiple of `v_k`, the coefficient being `⟪v_k, r_k⟫`
  have hrep : (iterate A b x₀ k).r =
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
        Arnoldi.vec A (b - A x₀) k := by
    have hzmem : (iterate A b x₀ k).r -
        inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
          Arnoldi.vec A (b - A x₀) k ∈ subspace A (b - A x₀) (k + 1) :=
      Submodule.sub_mem _ hrmem
        (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace A (b - A x₀) k))
    have hzperp : (iterate A b x₀ k).r -
        inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
          Arnoldi.vec A (b - A x₀) k ∈ (subspace A (b - A x₀) (k + 1))ᗮ := by
      rw [← Arnoldi.span_vec A (b - A x₀) (k + 1)]
      refine Submodule.mem_orthogonal_span.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i k with h | h
      · have hmem : Arnoldi.vec A (b - A x₀) i ∈ subspace A (b - A x₀) k :=
          subspace_mono A (b - A x₀) h (Arnoldi.vec_mem_subspace A (b - A x₀) i)
        rw [inner_sub_right, hrperp _ hmem, inner_smul_right,
          Arnoldi.inner_vec_eq_zero A (b - A x₀) (by omega : i ≠ k), mul_zero, sub_zero]
      · obtain rfl : i = k := le_antisymm (Nat.lt_succ_iff.1 hi) h
        rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
        simp
    have hzero := inner_self_eq_zero (𝕜 := 𝕜).1
      ((Submodule.mem_orthogonal _ _).1 hzperp _ hzmem)
    exact sub_eq_zero.1 hzero
  -- the coefficient is `(-1)^k` times a positive real
  obtain ⟨c, hcpos, hc⟩ := prod_neg_alpha b x₀ hA k hr
  obtain ⟨g, hgpos, hg⟩ : ∃ g : ℝ, 0 < g ∧
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) ((A ^ k) (b - A x₀)) = (g : 𝕜) := by
    refine ⟨‖InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) (b - A x₀)) k‖, ?_,
      hveq ▸ InnerProductSpace.inner_gramSchmidtNormed_self (fun i : ℕ => (A ^ i) (b - A x₀)) k⟩
    rw [norm_pos_iff]
    intro h0
    exact hvne (by rw [hveq, InnerProductSpace.gramSchmidtNormed, h0, smul_zero])
  have ht : inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r =
      (-1 : 𝕜) ^ k * ((c * g : ℝ) : 𝕜) := by
    have hsplit : (iterate A b x₀ k).r =
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) +
          ((iterate A b x₀ k).r -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) := by
      abel
    rw [hsplit, inner_add_right, hvperp' _ (leading b x₀ k).1, add_zero, inner_smul_right,
      hc, hg]
    push_cast
    ring
  have hnr : ‖(iterate A b x₀ k).r‖ = c * g := by
    rw [hrep, norm_smul, hnorm, mul_one, ht, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, RCLike.norm_ofReal, abs_of_pos (mul_pos hcpos hgpos)]
  have hsq : (-1 : 𝕜) ^ k * (-1 : 𝕜) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have h0 : ((c * g : ℝ) : 𝕜) ≠ 0 := by
    simpa using (mul_pos hcpos hgpos).ne'
  rw [hnr, hrep, smul_smul, ht, mul_mul_mul_comm, hsq, one_mul, RCLike.ofReal_inv,
    inv_mul_cancel₀ h0, one_smul]

/-- **Finite termination.** Let $A$ be symmetric and coercive, and suppose that the full Krylov
space $\mathcal{K}_\infty(A, r_0)$ of $r_0 = b - A x_0$ is finite-dimensional. If
$k \ge \operatorname{grade}(A, r_0)$, then
$$r_k = 0.$$
So CG is a direct method that takes at most $n$ steps in dimension $n$. -/
theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  rw [residual_eq, sub_eq_zero]
  exact ((isGalerkinIterate b x₀ hA k).apply_eq_of_grade_le hk).symm

omit hA in
/-- **Sharpness of finite termination.** Suppose that the full Krylov space
$\mathcal{K}_\infty(A, r_0)$ of $r_0 = b - A x_0$ is finite-dimensional. If
$k < \operatorname{grade}(A, r_0)$, then
$$r_k \neq 0.$$
This holds for every operator $A$. Together with `CG.residual_eq_zero_of_grade_le`, CG takes
exactly $\operatorname{grade}(A, r_0)$ steps.

A vanishing $r_k$ would make $x_k$ an exact solution in $x_0 + \mathcal{K}_k(A, r_0)$, and an
exact Krylov solution at step $k$ forces the grade down to $k$ (`Krylov.grade_le_of_apply_eq`). -/
theorem residual_ne_zero_of_lt_grade [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : k < grade A (b - A x₀)) : (iterate A b x₀ k).r ≠ 0 := by
  intro h
  rw [residual_eq, sub_eq_zero] at h
  exact absurd (grade_le_of_apply_eq (iterate_sub_mem b x₀ k) h.symm) (by omega)

/-! ### Real coefficients and their signs -/

omit hA in
private theorem alpha_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : alpha A (iterate A b x₀ k) =
    ((‖(iterate A b x₀ k).r‖ ^ 2 /
      RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p) : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq, hAs.coe_re_inner_apply_self, alpha]

omit hA in
/-- For a symmetric $A$, the step length satisfies $\operatorname{Re} \alpha_k \ge 0$ as soon as
$\operatorname{Re} \langle A p_k, p_k \rangle \ge 0$; for a coercive $A$ this is automatic
(`CG.re_alpha_nonneg`). -/
private theorem re_alpha_nonneg' (hAs : A.IsSymmetric) {k : ℕ}
    (h : 0 ≤ RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p)) :
    0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (sq_nonneg _) h

/-- Let $A$ be symmetric and coercive. Then the CG step lengths have nonnegative real part:
$\operatorname{Re} \alpha_k \ge 0$ for every $k$. (They are real, so $\alpha_k \ge 0$.) -/
theorem re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) :=
  re_alpha_nonneg' b x₀ hA.isSymmetric (re_inner_apply_self_nonneg hA _)

omit hA in
private theorem beta_eq_ofReal (k : ℕ) : beta A (iterate A b x₀ k) =
    ((‖(iterate A b x₀ (k + 1)).r‖ ^ 2 / ‖(iterate A b x₀ k).r‖ ^ 2 : ℝ) : 𝕜) := by
  rw [beta_iterate, RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq,
    ← inner_self_eq_ofReal_norm_sq]

omit hA in
private theorem re_beta_nonneg (k : ℕ) : 0 ≤ RCLike.re (beta A (iterate A b x₀ k)) := by
  rw [beta_eq_ofReal b x₀ k, RCLike.ofReal_re]
  positivity

omit hA in
/-- For a symmetric $A$, the step length is real: $\operatorname{Re}(\alpha_k z) = \operatorname{Re}
\alpha_k \operatorname{Re} z$ for every scalar $z$. -/
private theorem re_alpha_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (alpha A (iterate A b x₀ k) * z) =
      RCLike.re (alpha A (iterate A b x₀ k)) * RCLike.re z := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
private theorem re_beta_mul (k : ℕ) (z : 𝕜) :
    RCLike.re (beta A (iterate A b x₀ k) * z) =
      RCLike.re (beta A (iterate A b x₀ k)) * RCLike.re z := by
  rw [beta_eq_ofReal b x₀ k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- Let $A$ be symmetric and coercive. Then for all $i$ and $j$,
$$\operatorname{Re} \langle p_i, p_j \rangle \ge 0.$$
This is an ingredient of the theorem of [steihaug1983conjugate]. -/
theorem re_inner_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  have key : ∀ m n : ℕ, m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (iterate A b x₀ n).p) := by
    intro m
    induction m with
    | zero =>
      intro n _
      rw [direction_zero, inner_residual_direction_eq b x₀ hA (Nat.zero_le n), RCLike.ofReal_re]
      positivity
    | succ m ih =>
      intro n hn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta, map_add,
        inner_residual_direction_eq b x₀ hA (show m + 1 ≤ n by omega), RCLike.ofReal_re,
        re_beta_mul b x₀]
      exact add_nonneg (by positivity)
        (mul_nonneg (re_beta_nonneg b x₀ m) (ih n (by omega)))
  rcases le_total i j with h | h
  · exact key i j h
  · rw [← inner_conj_symm, RCLike.conj_re]
    exact key j i h

/-- For a symmetric coercive $A$, $k \le m$ and every $j$, $\operatorname{Re} \langle x_m - x_k, p_j
\rangle \ge 0$: the partial sums of the steps $\alpha_i p_i$ have nonnegative inner products
with the directions. -/
private theorem re_inner_sub_iterate_direction_nonneg {k m : ℕ} (hkm : k ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ k).x)
      (iterate A b x₀ j).p) := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ k).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ k).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hA.isSymmetric, map_add,
      re_alpha_mul b x₀ hA.isSymmetric]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg b x₀ hA m)
      (re_inner_direction_nonneg b x₀ hA m j))

/-! ### Error identities and monotonicity -/

section Errors

variable {xstar : E} (hstar : A xstar = b)
include hstar

/-- **The one-step error identity** ([hestenes1952methods], Theorem 6:1; [meurant2006lanczos],
Theorem 11). Let $A$ be symmetric and coercive, and let $x^* \in E$ satisfy $A x^* = b$. Write
$\|x\|_A = \sqrt{\operatorname{Re} \langle A x, x \rangle}$ for the energy norm. Then for every
$k$,
$$\|x^* - x_k\|_A^2 - \|x^* - x_{k+1}\|_A^2 = \operatorname{Re}(\alpha_k) \, \|r_k\|^2.$$

The energy norm is `energyNorm A`. -/
theorem energyNorm_error_sq_sub (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 -
        energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 =
      RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 := by
  have alg : ∀ (u q : E) (a R : 𝕜), inner 𝕜 (A u) q = R → inner 𝕜 (A q) u = R →
      (starRingEnd 𝕜) a = a → a * inner 𝕜 (A q) q = R →
      inner 𝕜 (A (u - a • q)) (u - a • q) = inner 𝕜 (A u) u - a * R := by
    intro u q a R h1 h2 h3 h4
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, h1, h2, h3]
    linear_combination a * h4
  have hAe : A (xstar - (iterate A b x₀ k).x) = (iterate A b x₀ k).r := by
    rw [map_sub, hstar, ← residual_eq]
  have hsub : xstar - (iterate A b x₀ (k + 1)).x =
      (xstar - (iterate A b x₀ k).x) - alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hup : inner 𝕜 (A (xstar - (iterate A b x₀ k).x)) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
    rw [hAe, (invariant b x₀ hA k).diag]
  have hpu : inner 𝕜 (A (iterate A b x₀ k).p) (xstar - (iterate A b x₀ k).x) =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
    rw [hA.isSymmetric, hAe, ← inner_conj_symm, (invariant b x₀ hA k).diag, inner_self_conj]
  have hre : RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ k).x))
        (xstar - (iterate A b x₀ k).x) -
      alpha A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r) =
      RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ k).x)) (xstar - (iterate A b x₀ k).x)) -
        RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 := by
    rw [map_sub, re_alpha_mul b x₀ hA.isSymmetric, inner_self_eq_norm_sq]
  rw [hA.energyNorm_sq, hA.energyNorm_sq, hsub,
    alg _ _ _ _ hup hpu (conj_alpha hA.isSymmetric _)
      (alpha_mul_inner_apply_direction b x₀ hA k), hre]
  ring

/-- **The error as a sum over the remaining steps.** Let $A$ be symmetric and coercive, let
$x^* \in E$ satisfy $A x^* = b$, and suppose that the full Krylov space
$\mathcal{K}_\infty(A, r_0)$ of $r_0 = b - A x_0$ is finite-dimensional, with grade $d$. Then
for every $k$,
$$\|x^* - x_k\|_A^2 = \sum_{j=k}^{d-1} \operatorname{Re}(\alpha_j) \, \|r_j\|^2.$$
For $k \ge d$ the sum is empty and the error is $0$. -/
theorem energyNorm_error_sq_eq_sum [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 =
      ∑ j ∈ Finset.Ico k (grade A (b - A x₀)),
        RCLike.re (alpha A (iterate A b x₀ j)) * ‖(iterate A b x₀ j).r‖ ^ 2 := by
  have hzero : ∀ m, grade A (b - A x₀) ≤ m →
      energyNorm A (xstar - (iterate A b x₀ m).x) ^ 2 = 0 := by
    intro m hm
    have hr := residual_eq_zero_of_grade_le b x₀ hA hm
    rw [residual_eq, sub_eq_zero] at hr
    have hx : xstar = (iterate A b x₀ m).x := hA.isCoercive.injective (hstar.trans hr)
    rw [hx, sub_self]
    simp [energyNorm]
  have tel : ∀ n : ℕ, energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 =
      (∑ j ∈ Finset.Ico k (k + n), RCLike.re (alpha A (iterate A b x₀ j)) *
        ‖(iterate A b x₀ j).r‖ ^ 2) +
      energyNorm A (xstar - (iterate A b x₀ (k + n)).x) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := energyNorm_error_sq_sub b x₀ hA hstar (k + n)
      rw [show k + (n + 1) = k + n + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
      linarith [ih]
  rcases Nat.lt_or_ge (grade A (b - A x₀)) k with h | h
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, hzero k (le_of_lt h)]
  · have hn := tel (grade A (b - A x₀) - k)
    rw [show k + (grade A (b - A x₀) - k) = grade A (b - A x₀) by omega] at hn
    rw [hn, hzero _ le_rfl, add_zero]

/-- **The Euclidean error decreases** ([hestenes1952methods], Theorem 6:3; [meurant2006lanczos],
Theorem 12). Let $A$ be symmetric and coercive, let $x^* \in E$ satisfy $A x^* = b$, and suppose
that the full Krylov space $\mathcal{K}_\infty(A, r_0)$ of $r_0 = b - A x_0$ is
finite-dimensional. Then $k \mapsto \|x^* - x_k\|$ is nonincreasing.

The hypothesis of finite dimension is needed by the proof. Both this proof and the argument of
[hestenes1952methods] use the expansion $x^* - x_k = \sum_{j \ge k} \alpha_j p_j$, that is,
finite termination of the recurrence, which `CG.energyNorm_error_sq_eq_sum` also needs. Without
it the statement becomes a convergence result in infinite dimension, which is not proved here.
In contrast, `CG.energyNorm_error_antitone` rests on a one-step identity and needs no such
hypothesis. -/
theorem norm_error_antitone [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  refine antitone_nat_of_succ_le fun k => ?_
  set m := max (k + 1) (grade A (b - A x₀)) with hm
  have hxm : xstar = (iterate A b x₀ m).x := by
    have hr := residual_eq_zero_of_grade_le b x₀ hA (le_max_right (k + 1) (grade A (b - A x₀)))
    rw [residual_eq, sub_eq_zero] at hr
    exact hA.isCoercive.injective (hstar.trans hr)
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (xstar - (iterate A b x₀ (k + 1)).x)
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    refine mul_nonneg (re_alpha_nonneg b x₀ hA k) ?_
    rw [hxm]
    exact re_inner_sub_iterate_direction_nonneg b x₀ hA (le_max_left (k + 1) _) k
  have hsq : ‖xstar - (iterate A b x₀ (k + 1)).x‖ ^ 2 ≤ ‖xstar - (iterate A b x₀ k).x‖ ^ 2 := by
    rw [hexp, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p‖]
  nlinarith [norm_nonneg (xstar - (iterate A b x₀ (k + 1)).x),
    norm_nonneg (xstar - (iterate A b x₀ k).x)]

/-- **The energy error decreases.** Let $A$ be symmetric and coercive, and let $x^* \in E$ satisfy
$A x^* = b$. Then $k \mapsto \|x^* - x_k\|_A$ is nonincreasing.

One step subtracts the nonnegative amount $\alpha_k \|r_k\|^2$ from the square of the error
(`CG.energyNorm_error_sq_sub`). Unlike the Euclidean statement `CG.norm_error_antitone`, this
needs no finite dimension, because the identity behind it concerns a single step and not an
expansion of the whole remaining error. -/
theorem energyNorm_error_antitone :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h := energyNorm_error_sq_sub b x₀ hA hstar k
  have hnn : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 :=
    mul_nonneg (re_alpha_nonneg b x₀ hA k) (sq_nonneg _)
  nlinarith [energyNorm_nonneg A (xstar - (iterate A b x₀ k).x),
    energyNorm_nonneg A (xstar - (iterate A b x₀ (k + 1)).x)]

end Errors

/-!
### The theorem of Steihaug, for a symmetric but possibly indefinite operator

Coercivity enters the sign lemmas above only through $0 \le \operatorname{Re} \langle A p_j, p_j
\rangle$ and the nondegeneracy that it gives. Assume instead that this quantity is positive at the
steps taken so far, which is what a trust-region method monitors. Then the same chain of lemmas runs
for a symmetric, possibly indefinite $A$ ([steihaug1983conjugate]), and the conclusion becomes
strict.
-/

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for all $j < k$, the
joint invariant holds at every step $m \le k$. -/
private theorem invariant_le (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {m : ℕ} (hm : m ≤ k) : Invariant A b x₀ m := by
  refine invariant_of b x₀ hAs m fun j hj h => ?_
  have hj' := hpos j (lt_of_lt_of_le hj hm)
  rw [h, map_zero] at hj'
  exact absurd hj' (lt_irrefl 0)

omit hA in
/-- Suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for all $j < k$. Then the first
$k + 1$ directions span the Krylov subspace:
$$\operatorname{span}\{p_0, \dots, p_k\} = \mathcal{K}_{k+1}(A, r_0), \qquad r_0 = b - A x_0.$$
This holds for every operator $A$ that satisfies the positivity hypothesis. -/
theorem span_direction_eq_of_pos_prefix {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p)) :
    Submodule.span 𝕜 (Set.range fun i : Fin (k + 1) => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) (k + 1) := by
  refine le_antisymm (dirSpan_le_subspace A b x₀ _) (subspace_le_dirSpan_of_apply b x₀ _ ?_)
  intro j hj
  have hjk : j < k := by omega
  have hp : (iterate A b x₀ j).p ≠ 0 := by
    intro hz
    simpa [hz] using hpos j hjk
  have hden : inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p ≠ 0 := by
    intro hz
    simpa [hz] using hpos j hjk
  have hα : alpha A (iterate A b x₀ j) ≠ 0 :=
    div_ne_zero (inner_self_ne_zero.mpr
      (fun hr => hp (direction_eq_zero_of_residual_eq_zero A b x₀ hr))) hden
  exact apply_direction_mem_dirSpan_of_alpha_ne_zero b x₀ j hα

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
all $j < k$. Then $x_k$ is the Galerkin iterate of $\mathcal{K}_k(A, r_0)$ with
$r_0 = b - A x_0$:
$$x_k \in x_0 + \mathcal{K}_k(A, r_0), \qquad b - A x_k \perp \mathcal{K}_k(A, r_0).$$
-/
theorem isGalerkinIterate_of_pos_prefix (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p)) :
    IsGalerkinIterate A b x₀ k (iterate A b x₀ k).x := by
  refine ⟨iterate_sub_mem b x₀ k, ?_⟩
  rcases k with _ | k
  · simp
  rw [← residual_eq, ← span_direction_eq_of_pos_prefix b x₀ (k := k) (fun j hj =>
    hpos j (by omega))]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [← inner_conj_symm, (invariant_le b x₀ hAs hpos le_rfl).rp i i.isLt, map_zero]

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
all $j < k$. Then $A$ is injective on the Krylov subspace traversed so far: if
$x \in \mathcal{K}_k(A, r_0)$ and $A x = 0$, then $x = 0$. -/
theorem eq_zero_of_apply_eq_zero_of_mem_subspace_of_pos_prefix
    (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {x : E} (hx : x ∈ subspace A (b - A x₀) k) (hAx : A x = 0) : x = 0 := by
  rcases k with _ | k
  · simpa using hx
  rw [← span_direction_eq_of_pos_prefix b x₀ (k := k) (fun j hj => hpos j (by omega))] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hx
  let p (i : Fin (k + 1)) := (iterate A b x₀ i).p
  change (∑ j, c j • p j) = x at hc
  have hconj (i j : Fin (k + 1)) (hij : i ≠ j) : inner 𝕜 (A (p i)) (p j) = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hh := (invariant_le b x₀ hAs hpos (show (j : ℕ) ≤ k + 1 by omega)).pp i h
      change inner 𝕜 (A (p j)) (p i) = 0 at hh
      rw [← inner_conj_symm, ← hAs, hh, map_zero]
    · exact (invariant_le b x₀ hAs hpos (show (i : ℕ) ≤ k + 1 by omega)).pp j h
  have hz (i : Fin (k + 1)) : c i = 0 := by
    have hh : inner 𝕜 (A x) (p i) = 0 := by rw [hAx, inner_zero_left]
    rw [← hc, map_sum, sum_inner, Finset.sum_eq_single i] at hh
    · rw [map_smul, inner_smul_left] at hh
      have hn : inner 𝕜 (A (p i)) (p i) ≠ 0 := by
        intro he
        have hp := hpos i i.isLt
        change 0 < RCLike.re (inner 𝕜 (A (p i)) (p i)) at hp
        simp [he] at hp
      have hc0 := (mul_eq_zero.mp hh).resolve_right hn
      exact (map_eq_zero_iff _ (starRingEnd 𝕜).injective).mp hc0
    · intro j _ hji
      rw [map_smul, inner_smul_left, hconj j i hji, mul_zero]
    · simp
  rw [← hc]
  simp [hz]

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
all $j < k$. Then
$$\langle r_k, p_k \rangle = \langle r_k, r_k \rangle.$$
-/
theorem inner_residual_direction_self_of_pos_prefix (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p)) :
    inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r :=
  (invariant_le b x₀ hAs hpos le_rfl).diag

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
all $j < k$. Then the residuals up to step $k$ are mutually orthogonal: for $i, j \le k$ with
$i \neq j$,
$$\langle r_i, r_j \rangle = 0.$$
This is `CG.inner_residual_eq_zero` up to step $k$. -/
theorem inner_residual_eq_zero_of_pos_prefix (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0 := by
  have key : ∀ m, m ≤ k → ∀ n, n < m →
      inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ n).r = 0 := by
    intro m hm n hnm
    exact inner_residual_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant_le b x₀ hAs hpos hm).rp l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, key j hj i h', map_zero]
  · exact key i hi j h'

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for
all $j < k$. Then for $i \le j \le k$,
$$\langle r_i, p_j \rangle = \|r_j\|^2.$$
This is `CG.inner_residual_direction_eq` up to step $k$. -/
theorem inner_residual_direction_eq_of_pos_prefix (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p =
      ((‖(iterate A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) := by
  revert hjk
  induction j, hij using Nat.le_induction with
  | base =>
    intro hjk
    rw [(invariant_le b x₀ hAs hpos hjk).diag, inner_self_eq_ofReal_norm_sq]
  | succ j hij ih =>
    intro hjk
    rw [iterate_succ_p, inner_add_right, inner_smul_right, ih (by omega),
      inner_residual_eq_zero_of_pos_prefix b x₀ hAs hpos (by omega) hjk (show i ≠ j + 1 by omega),
      zero_add,
      ← inner_self_eq_ofReal_norm_sq, ← inner_self_eq_ofReal_norm_sq, beta_mul_inner_self A b x₀ j]

omit hA in
/-- For a symmetric $A$ with $\operatorname{Re} \langle A p_l, p_l \rangle > 0$ for all $l < k$, and
$i, j \le k$, $\operatorname{Re} \langle p_i, p_j \rangle \ge 0$. -/
private theorem re_inner_direction_nonneg' (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  have key : ∀ m, m ≤ k → ∀ n, n ≤ k → m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (iterate A b x₀ n).p) := by
    intro m
    induction m with
    | zero =>
      intro _ n hn _
      rw [direction_zero,
        inner_residual_direction_eq_of_pos_prefix b x₀ hAs hpos (Nat.zero_le n) hn,
        RCLike.ofReal_re]
      positivity
    | succ m ih =>
      intro hm n hn hmn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta, map_add,
        inner_residual_direction_eq_of_pos_prefix b x₀ hAs hpos (show m + 1 ≤ n by omega) hn,
        RCLike.ofReal_re, re_beta_mul b x₀]
      exact add_nonneg (by positivity)
        (mul_nonneg (re_beta_nonneg b x₀ m) (ih (by omega) n hn (by omega)))
  rcases le_total i j with h | h
  · exact key i hi j hj h
  · rw [← inner_conj_symm, RCLike.conj_re]
    exact key j hj i hi h

omit hA in
/-- Let $A$ be symmetric, and suppose that $\operatorname{Re} \langle A p_i, p_i \rangle > 0$ for
all $i < k$. Then for $l \le m \le k$ and $j \le k$,
$$\operatorname{Re} \langle x_m - x_l, p_j \rangle \ge 0.$$
This is the nonnegativity of $\operatorname{Re} \langle x_m - x_l, p_j \rangle$ for symmetric
coercive $A$, up to step $k$. -/
theorem re_inner_sub_iterate_direction_nonneg_of_pos_prefix (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {l m : ℕ} (hlm : l ≤ m) (hm : m ≤ k) {j : ℕ} (hj : j ≤ k) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ l).x)
      (iterate A b x₀ j).p) := by
  revert hm
  induction m, hlm using Nat.le_induction with
  | base => intro _; simp
  | succ m hlm ih =>
    intro hm
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ l).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ l).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hAs, map_add, re_alpha_mul b x₀ hAs]
    exact add_nonneg (ih (by omega))
      (mul_nonneg (re_alpha_nonneg' b x₀ hAs (le_of_lt (hpos m (by omega))))
        (re_inner_direction_nonneg' b x₀ hAs hpos (by omega) hj))

omit hA in
/-- **The theorem of Steihaug for a symmetric, possibly indefinite operator**
([steihaug1983conjugate]). Let $A$ be symmetric, start CG at $x_0 = 0$, and suppose that
$\operatorname{Re} \langle A p_j, p_j \rangle > 0$ for all $j < k$. Then for every $i < k$,
$$\|x_i\| < \|x_{i+1}\|.$$

A trust-region method can check the hypothesis as it goes, and the conclusion makes the CG path
leave the trust region monotonically. The coercive form `CG.norm_iterate_monotone` is the
corollary in which the hypothesis holds at every step where the iteration moves. -/
theorem norm_iterate_lt_of_re_inner_apply_direction_pos (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b 0 j).p) (iterate A b 0 j).p))
    {i : ℕ} (hi : i < k) : ‖(iterate A b 0 i).x‖ < ‖(iterate A b 0 (i + 1)).x‖ := by
  have hp := hpos i hi
  have hpne : (iterate A b 0 i).p ≠ 0 := by
    intro h
    rw [h, map_zero, inner_zero_left, map_zero] at hp
    exact lt_irrefl 0 hp
  have hrne : (iterate A b 0 i).r ≠ 0 := fun h =>
    hpne (direction_eq_zero_of_residual_eq_zero A b 0 h)
  have hαpos : 0 < RCLike.re (alpha A (iterate A b 0 i)) := by
    rw [alpha_eq_ofReal b 0 hAs i, RCLike.ofReal_re]
    exact div_pos (pow_pos (norm_pos_iff.2 hrne) 2) hp
  have hαne : alpha A (iterate A b 0 i) ≠ 0 := fun h => by
    rw [h, map_zero] at hαpos; exact lt_irrefl 0 hαpos
  have hxp : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 i).p) := by
    have h := re_inner_sub_iterate_direction_nonneg_of_pos_prefix b 0 hAs hpos (Nat.zero_le i)
      (le_of_lt hi) (le_of_lt hi)
    rwa [show (iterate A b 0 0).x = 0 from rfl, sub_zero] at h
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x
      (alpha A (iterate A b 0 i) • (iterate A b 0 i).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hAs]
    exact mul_nonneg (le_of_lt hαpos) hxp
  have hnz : 0 < ‖alpha A (iterate A b 0 i) • (iterate A b 0 i).p‖ := by
    rw [norm_smul]
    exact mul_pos (norm_pos_iff.2 hαne) (norm_pos_iff.2 hpne)
  have hsq : ‖(iterate A b 0 i).x‖ ^ 2 < ‖(iterate A b 0 (i + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [hnz]
  nlinarith [norm_nonneg (iterate A b 0 i).x, norm_nonneg (iterate A b 0 (i + 1)).x]

/-- **The theorem of Steihaug** ([steihaug1983conjugate]). Let $A$ be symmetric and coercive, and
start CG at $x_0 = 0$. Then $k \mapsto \|x_k\|$ is nondecreasing.

A coercive $A$ gives $\operatorname{Re} \langle A p_j, p_j \rangle > 0$ at every step before the
residual vanishes (`CG.re_inner_apply_direction_pos`), and after that the iterate stops moving. -/
theorem norm_iterate_monotone : Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  refine monotone_nat_of_le_succ fun k => ?_
  by_cases hr : (iterate A b 0 k).r = 0
  · have h : (iterate A b 0 (k + 1)).x = (iterate A b 0 k).x := by
      rw [iterate_succ_x, direction_eq_zero_of_residual_eq_zero A b 0 hr, smul_zero, add_zero]
    exact le_of_eq (congrArg norm h.symm)
  · exact le_of_lt (norm_iterate_lt_of_re_inner_apply_direction_pos b hA.isSymmetric
      (k := k + 1) (fun j hj => re_inner_apply_direction_pos b 0 hA
        (residual_ne_zero_of_le b 0 hr (by omega))) (Nat.lt_succ_self k))

section ThreeTerm

omit hA
variable (A)

/-!
### The three-term form ([saad2003iterative], §6.7.2, Algorithm 6.19)

Let $\gamma_m = \langle r_m, r_m \rangle / \langle A r_m, r_m \rangle$, $\rho_0 = 1$ and
$$\rho_m = \Bigl(1 - \frac{\gamma_m}{\gamma_{m-1}} \frac{\|r_m\|^2}{\|r_{m-1}\|^2}
  \frac{1}{\rho_{m-1}}\Bigr)^{-1}$$
([saad2003iterative], (6.97)). Then $r_{m+1} = \rho_m (r_m - \gamma_m A r_m) + (1 - \rho_m) r_{m-1}$
([saad2003iterative], (6.96)) and $x_{m+1} = \rho_m (x_m + \gamma_m r_m) + (1 - \rho_m) x_{m-1}$
([saad2003iterative], (6.98)).

The sign in the last relation is $+$, where the book prints $-$ in (6.98) and in Algorithm 6.19. The
book's own (6.96) forces $+$: apply $b - A(\cdot)$ to the recurrence for $x$ and use
$\rho_m + (1 - \rho_m) = 1$; this turns $x_m \pm \gamma_m r_m$ into $r_m \mp \gamma_m A r_m$. The
sign $+$ also makes the first step $x_1 = x_0 + \gamma_0 r_0$ give $\langle r_1, r_0 \rangle = 0$,
which is the property that the book asks of that step.
-/

/-- The coefficient of the three-term form of CG:
$$\gamma_m = \frac{\langle r_m, r_m \rangle}{\langle A r_m, r_m \rangle},$$
with $\gamma_m = 0$ when $\langle A r_m, r_m \rangle = 0$.

This is the scalar of line 3 of Algorithm 6.19 of [saad2003iterative], §6.7.2. The book states
it between (6.96) and (6.97), without a number. -/
noncomputable def gamma (m : ℕ) : 𝕜 :=
  inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ m).r /
    inner 𝕜 (A (iterate A b x₀ m).r) (iterate A b x₀ m).r

/-- The coefficient $\rho_m$ of the three-term form of CG, (6.97) of [saad2003iterative]:
$\rho_0 = 1$ and
$$\rho_{m+1} = \Bigl(1 - \frac{\gamma_{m+1}}{\gamma_m} \frac{\|r_{m+1}\|^2}{\|r_m\|^2}
  \frac{1}{\rho_m}\Bigr)^{-1}.$$

Divisions and inverses follow the Lean convention $x / 0 = 0$ and $0^{-1} = 0$. -/
noncomputable def rho : ℕ → 𝕜
  | 0 => 1
  | m + 1 => (1 - gamma A b x₀ (m + 1) / gamma A b x₀ m *
      ((‖(iterate A b x₀ (m + 1)).r‖ ^ 2 / ‖(iterate A b x₀ m).r‖ ^ 2 : ℝ) : 𝕜) / rho m)⁻¹

variable {A}

/-! #### Scalar identities behind the three-term form -/

private theorem rho_succ (m : ℕ) : rho A b x₀ (m + 1) =
    (1 - gamma A b x₀ (m + 1) / gamma A b x₀ m * beta A (iterate A b x₀ m) /
      rho A b x₀ m)⁻¹ := by
  rw [beta_eq_ofReal b x₀ m, rho]

private theorem inner_apply_residual_self_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) :
    inner 𝕜 (A (iterate A b x₀ k).r) (iterate A b x₀ k).r ≠ 0 :=
  fun h => hk (eq_zero_of_inner_apply_self_eq_zero hA h)

private theorem inner_apply_direction_self_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) :
    inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p ≠ 0 := by
  intro h
  exact absurd (h ▸ re_inner_apply_direction_pos b x₀ hA hk) (by simp)

private theorem gamma_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) : gamma A b x₀ k ≠ 0 :=
  div_ne_zero (fun h => hk (inner_self_eq_zero.1 h))
    (inner_apply_residual_self_ne_zero b x₀ hA hk)

/-- Let $A$ be symmetric and coercive. If $r_k \neq 0$, then the step length $\alpha_k = \langle
r_k, r_k \rangle / \langle A p_k, p_k \rangle$ is nonzero. -/
theorem alpha_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) : alpha A (iterate A b x₀ k) ≠ 0 :=
  div_ne_zero (fun h => hk (inner_self_eq_zero.1 h))
    (inner_apply_direction_self_ne_zero b x₀ hA hk)

/-- For a symmetric coercive $A$, the identity of [hestenes1952methods] $\alpha_m \langle A p_{m+1},
p_{m+1} \rangle = \alpha_m \langle A r_{m+1}, r_{m+1} \rangle - \beta_m \langle r_{m+1}, r_{m+1}
\rangle$, which links the two-term and the three-term recurrences and needs no hypothesis of
nondegeneracy. -/
private theorem alpha_mul_inner_apply_direction_succ (hA : A.IsSymmetricCoercive) (m : ℕ) :
    alpha A (iterate A b x₀ m) *
        inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p =
      alpha A (iterate A b x₀ m) *
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r -
        beta A (iterate A b x₀ m) *
          inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
  have alg : ∀ (u q : E) (c : 𝕜), (starRingEnd 𝕜) c = c →
      inner 𝕜 (A (u + c • q)) (u + c • q) = inner 𝕜 (A u) u + c * inner 𝕜 (A u) q +
        c * inner 𝕜 (A q) u + c * c * inner 𝕜 (A q) q := by
    intro u q c hc
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hc]
    ring
  have hT : alpha A (iterate A b x₀ m) *
      inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ m).p =
        -inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
    rw [hA.isSymmetric, ← inner_smul_right, alpha_smul_apply_direction, inner_sub_right,
      inner_residual_eq_zero b x₀ hA (show m + 1 ≠ m by omega), zero_sub]
  have hT' : alpha A (iterate A b x₀ m) *
      inner 𝕜 (A (iterate A b x₀ m).p) (iterate A b x₀ (m + 1)).r =
        -inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
    rw [← conj_alpha hA.isSymmetric (iterate A b x₀ m), ← inner_smul_left,
      alpha_smul_apply_direction,
      inner_sub_left, inner_residual_eq_zero b x₀ hA (show m ≠ m + 1 by omega), zero_sub]
  have hQ := alpha_mul_inner_apply_direction b x₀ hA m
  have hB := beta_mul_inner_self A b x₀ m
  rw [iterate_succ_p, alg _ _ _ (conj_beta A (iterate A b x₀ m))]
  linear_combination beta A (iterate A b x₀ m) * hT + beta A (iterate A b x₀ m) * hT' +
    beta A (iterate A b x₀ m) * beta A (iterate A b x₀ m) * hQ + beta A (iterate A b x₀ m) * hB

/-- For a symmetric coercive $A$ with $r_m, r_{m+1} \neq 0$ and $\alpha_m = \rho_m \gamma_m$, the
identity $\rho_{m+1} = \langle A r_{m+1}, r_{m+1} \rangle / \langle A p_{m+1}, p_{m+1} \rangle$. -/
private theorem rho_succ_eq_div (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hm : (iterate A b x₀ m).r ≠ 0) (hm1 : (iterate A b x₀ (m + 1)).r ≠ 0)
    (ih : alpha A (iterate A b x₀ m) = rho A b x₀ m * gamma A b x₀ m) :
    rho A b x₀ (m + 1) =
      inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r /
        inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p := by
  have hS := inner_apply_residual_self_ne_zero b x₀ hA hm1
  have hg := gamma_ne_zero b x₀ hA hm
  have ha := alpha_ne_zero b x₀ hA hm
  have hK := alpha_mul_inner_apply_direction_succ b x₀ hA m
  have hrhon : rho A b x₀ m = alpha A (iterate A b x₀ m) / gamma A b x₀ m := by
    rw [ih]; field_simp
  have hX : (1 : 𝕜) - gamma A b x₀ (m + 1) / gamma A b x₀ m * beta A (iterate A b x₀ m) /
      rho A b x₀ m = inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p /
        inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r := by
    rw [hrhon, show gamma A b x₀ (m + 1) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r from rfl]
    field_simp
    linear_combination -hK
  rw [rho_succ b x₀ m, hX, inv_div]

/-- For a symmetric coercive $A$ with $r_j \neq 0$ for $j \le m$, the identity
$\alpha_m = \rho_m \gamma_m$ of [saad2003iterative], §6.7.2, which links the step length of the
two-term recurrence with the coefficients of the three-term one. -/
private theorem alpha_eq_rho_mul_gamma (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    alpha A (iterate A b x₀ m) = rho A b x₀ m * gamma A b x₀ m := by
  induction m with
  | zero => rw [rho, one_mul, alpha, gamma, direction_zero]
  | succ m ih =>
    have hm := hr m (by omega)
    have hm1 := hr (m + 1) le_rfl
    have hS := inner_apply_residual_self_ne_zero b x₀ hA hm1
    have hQ := inner_apply_direction_self_ne_zero b x₀ hA hm1
    rw [rho_succ_eq_div b x₀ hA m hm hm1 (ih fun j hj => hr j (by omega)),
      show gamma A b x₀ (m + 1) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r from rfl,
      show alpha A (iterate A b x₀ (m + 1)) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p from rfl]
    field_simp

/-- For a symmetric coercive $A$ with $r_j \neq 0$ for $j \le m + 1$, the identity $\alpha_m
(\rho_{m+1} - 1) = \alpha_{m+1} \beta_m$. -/
private theorem alpha_mul_rho_succ_sub_one (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m + 1, (iterate A b x₀ j).r ≠ 0) :
    alpha A (iterate A b x₀ m) * (rho A b x₀ (m + 1) - 1) =
      alpha A (iterate A b x₀ (m + 1)) * beta A (iterate A b x₀ m) := by
  have hm := hr m (by omega)
  have hm1 := hr (m + 1) le_rfl
  have hQ := inner_apply_direction_self_ne_zero b x₀ hA hm1
  have hK := alpha_mul_inner_apply_direction_succ b x₀ hA m
  have ha' := alpha_mul_inner_apply_direction b x₀ hA (m + 1)
  rw [rho_succ_eq_div b x₀ hA m hm hm1
    (alpha_eq_rho_mul_gamma b x₀ hA m fun j hj => hr j (by omega))]
  field_simp
  linear_combination -hK - beta A (iterate A b x₀ m) * ha'

/-- **The three-term recurrence of the iterates**, [saad2003iterative], (6.98). Let $A$ be symmetric
and coercive, and suppose that $r_j \neq 0$ for all $j \le m$. Then
$$x_{m+1} = \rho_m (x_m + \gamma_m r_m) + (1 - \rho_m) x_{m-1},$$
where $x_{-1}$ is read as $x_0$; this is harmless because $1 - \rho_0 = 0$.

The sign in front of $\gamma_m r_m$ is $+$, and not the $-$ that the book prints in (6.98) and
in Algorithm 6.19; the book's own residual form (6.96) forces $+$, see
`CG.residual_succ_eq_three_term`. The index $m - 1$ is the truncated subtraction of natural
numbers, so it is $0$ at $m = 0$. -/
theorem iterate_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).x =
      rho A b x₀ m • ((iterate A b x₀ m).x + gamma A b x₀ m • (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).x := by
  cases m with
  | zero =>
    have h0 : alpha A (iterate A b x₀ 0) = gamma A b x₀ 0 := by
      rw [alpha, gamma, direction_zero]
    rw [iterate_succ_x, h0, rho]
    simp [init]
  | succ n =>
    have hn := hr n (by omega)
    have ha := alpha_ne_zero b x₀ hA hn
    have hrho := alpha_mul_rho_succ_sub_one b x₀ hA n hr
    have hag := alpha_eq_rho_mul_gamma b x₀ hA (n + 1) hr
    have hpn : (iterate A b x₀ n).p = (alpha A (iterate A b x₀ n))⁻¹ •
        ((iterate A b x₀ (n + 1)).x - (iterate A b x₀ n).x) := by
      rw [iterate_succ_x, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [Nat.add_sub_cancel, iterate_succ_x, iterate_succ_p, hpn]
    match_scalars
    · field_simp
      linear_combination -hrho
    · field_simp
      linear_combination hag
    · field_simp
      linear_combination hrho

/-- **The three-term recurrence of the residuals**, [saad2003iterative], (6.96). Let $A$ be
symmetric and coercive, and suppose that $r_j \neq 0$ for all $j \le m$. Then
$$r_{m+1} = \rho_m (r_m - \gamma_m A r_m) + (1 - \rho_m) r_{m-1},$$
where $r_{-1}$ is read as $r_0$; this is harmless because $1 - \rho_0 = 0$. -/
theorem residual_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).r =
      rho A b x₀ m • ((iterate A b x₀ m).r - gamma A b x₀ m • A (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).r := by
  cases m with
  | zero =>
    have h0 : alpha A (iterate A b x₀ 0) = gamma A b x₀ 0 := by
      rw [alpha, gamma, direction_zero]
    rw [iterate_succ_r, h0, rho, direction_zero]
    simp
  | succ n =>
    have hn := hr n (by omega)
    have ha := alpha_ne_zero b x₀ hA hn
    have hrho := alpha_mul_rho_succ_sub_one b x₀ hA n hr
    have hag := alpha_eq_rho_mul_gamma b x₀ hA (n + 1) hr
    have hpn : A (iterate A b x₀ n).p = (alpha A (iterate A b x₀ n))⁻¹ •
        ((iterate A b x₀ n).r - (iterate A b x₀ (n + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [Nat.add_sub_cancel, iterate_succ_r, iterate_succ_p, map_add, map_smul, hpn]
    match_scalars
    · field_simp
      linear_combination -hrho
    · field_simp
      linear_combination -hag
    · field_simp
      linear_combination hrho

end ThreeTerm

/-!
### The Lanczos coefficients of $r_0$ from the CG coefficients

The Lanczos vectors are the normalized CG residuals up to sign (`CG.arnoldi_vec_eq`), so the Lanczos
coefficients of $r_0 = b - A x_0$ are quotients of CG quantities ([saad2003iterative],
(6.101)–(6.103); [golub2013matrix], §11.3.5–11.3.6): the diagonal coefficients are $1/\alpha_0$ and
$1/\alpha_{k+1} + \beta_k/\alpha_k$, and the off-diagonal coefficients are
$\|r_{k+1}\| / (\|r_k\| \alpha_k)$. Together they give $T_m = L D L^T$ with
$D = \operatorname{diag}(1/\alpha_j)$ (`CG.lanczos_tridiag_eq_ldl`).
-/

section LanczosCoefficients

/-- If $r_k \neq 0$, then $A p_k = \alpha_k^{-1} (r_k - r_{k+1})$. -/
private theorem apply_direction_eq_inv_smul {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    A (iterate A b x₀ k).p =
      (alpha A (iterate A b x₀ k))⁻¹ • ((iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r) := by
  rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ (alpha_ne_zero b x₀ hA hr),
    one_smul]

/-- If $r_{k+1} \neq 0$, then $A r_{k+1} = \alpha_{k+1}^{-1} (r_{k+1} - r_{k+2}) - \beta_k
\alpha_k^{-1} (r_k - r_{k+1})$, from $r_{k+1} = p_{k+1} - \beta_k p_k$ ([saad2003iterative],
(6.100)). -/
private theorem apply_residual_succ {k : ℕ} (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    A (iterate A b x₀ (k + 1)).r =
      (alpha A (iterate A b x₀ (k + 1)))⁻¹ •
          ((iterate A b x₀ (k + 1)).r - (iterate A b x₀ (k + 1 + 1)).r) -
        (beta A (iterate A b x₀ k) * (alpha A (iterate A b x₀ k))⁻¹) •
          ((iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r) := by
  have hrk := residual_ne_zero_of_le b x₀ hr (Nat.le_succ k)
  have hsplit : (iterate A b x₀ (k + 1)).r =
      (iterate A b x₀ (k + 1)).p - beta A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_p]; abel
  calc A (iterate A b x₀ (k + 1)).r
      = A ((iterate A b x₀ (k + 1)).p - beta A (iterate A b x₀ k) • (iterate A b x₀ k).p) := by
        rw [← hsplit]
    _ = _ := by
        rw [map_sub, map_smul, apply_direction_eq_inv_smul b x₀ hA hr,
          apply_direction_eq_inv_smul b x₀ hA hrk, smul_smul]

/-- If $r_0 \neq 0$, then $\langle r_0, A r_0 \rangle = \alpha_0^{-1} \langle r_0, r_0 \rangle$. -/
private theorem inner_residual_apply_residual_zero (hr : (iterate A b x₀ 0).r ≠ 0) :
    inner 𝕜 (iterate A b x₀ 0).r (A (iterate A b x₀ 0).r) =
      (alpha A (iterate A b x₀ 0))⁻¹ * inner 𝕜 (iterate A b x₀ 0).r (iterate A b x₀ 0).r := by
  rw [← direction_zero A b x₀, apply_direction_eq_inv_smul b x₀ hA hr, direction_zero,
    inner_smul_right, inner_sub_right, inner_residual_eq_zero b x₀ hA (show 0 ≠ 0 + 1 by omega),
    sub_zero]

/-- If $r_{k+1} \neq 0$, then $\langle r_{k+1}, A r_{k+1} \rangle = (\alpha_{k+1}^{-1} + \beta_k
\alpha_k^{-1}) \langle r_{k+1}, r_{k+1} \rangle$. -/
private theorem inner_residual_apply_residual_succ {k : ℕ}
    (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r) =
      ((alpha A (iterate A b x₀ (k + 1)))⁻¹ +
          beta A (iterate A b x₀ k) * (alpha A (iterate A b x₀ k))⁻¹) *
        inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r := by
  rw [apply_residual_succ b x₀ hA hr, inner_sub_right, inner_smul_right, inner_smul_right,
    inner_sub_right, inner_sub_right,
    inner_residual_eq_zero b x₀ hA (show k + 1 ≠ k + 1 + 1 by omega),
    inner_residual_eq_zero b x₀ hA (show k + 1 ≠ k by omega)]
  ring

/-- If $r_{k+1} \neq 0$, then $\langle r_{k+1}, A r_k \rangle = -\alpha_k^{-1} \langle r_{k+1},
r_{k+1} \rangle$. -/
private theorem inner_residual_succ_apply_residual {k : ℕ}
    (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ k).r) =
      -((alpha A (iterate A b x₀ k))⁻¹ *
        inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r) := by
  have hrk := residual_ne_zero_of_le b x₀ hr (Nat.le_succ k)
  cases k with
  | zero =>
    rw [← direction_zero A b x₀, apply_direction_eq_inv_smul b x₀ hA hrk,
      inner_smul_right, inner_sub_right, inner_residual_eq_zero b x₀ hA (show 0 + 1 ≠ 0 by omega)]
    ring
  | succ k =>
    rw [apply_residual_succ b x₀ hA hrk, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_sub_right, inner_sub_right,
      inner_residual_eq_zero b x₀ hA (show k + 1 + 1 ≠ k + 1 by omega),
      inner_residual_eq_zero b x₀ hA (show k + 1 + 1 ≠ k by omega)]
    ring

omit hA in
/-- For real $t$ and $s$, $\overline{(-1)^k t} \, (-1)^k s = t s$. -/
private theorem conj_sign_mul_sign (k : ℕ) (t s : ℝ) :
    starRingEnd 𝕜 ((-1 : 𝕜) ^ k * (t : 𝕜)) * ((-1 : 𝕜) ^ k * (s : 𝕜)) = ((t * s : ℝ) : 𝕜) := by
  have h : ((-1 : 𝕜) ^ k) * (-1 : 𝕜) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [map_mul, map_pow, map_neg, map_one, RCLike.conj_ofReal]
  push_cast
  linear_combination (t : 𝕜) * s * h

omit hA in
/-- For real $t$ and $s$, $\overline{(-1)^{k+1} t} \, (-1)^k s = -t s$. -/
private theorem conj_sign_succ_mul_sign (k : ℕ) (t s : ℝ) :
    starRingEnd 𝕜 ((-1 : 𝕜) ^ (k + 1) * (t : 𝕜)) * ((-1 : 𝕜) ^ k * (s : 𝕜)) =
      -((t * s : ℝ) : 𝕜) := by
  have h : ((-1 : 𝕜) ^ k) * (-1 : 𝕜) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [map_mul, map_pow, map_neg, map_one, RCLike.conj_ofReal]
  push_cast
  linear_combination -(t : 𝕜) * s * h

/-- For a symmetric coercive $A$, the step length is real: $\alpha_k = \operatorname{Re} \alpha_k$.
-/
private theorem ofReal_re_alpha (k : ℕ) :
    ((RCLike.re (alpha A (iterate A b x₀ k)) : ℝ) : 𝕜) = alpha A (iterate A b x₀ k) :=
  RCLike.conj_eq_iff_re.1 (conj_alpha hA.isSymmetric _)

/-- **The first Lanczos coefficient from CG** ([saad2003iterative], (6.102)). Let $A$ be symmetric
and coercive, and let $r_0 = b - A x_0 \neq 0$. Then the first diagonal coefficient of the
Lanczos process of $A$ from $r_0$ is the reciprocal of the first CG step length:
$$\alpha^L_0 = \frac{1}{\alpha_0}.$$

The Lanczos coefficient is `Lanczos.alpha A (b - A x₀) 0`, a real number embedded in
$\mathbb{K}$. -/
theorem lanczos_alpha_zero_eq (hr : (iterate A b x₀ 0).r ≠ 0) :
    (Lanczos.alpha A (b - A x₀) 0 : 𝕜) = (alpha A (iterate A b x₀ 0))⁻¹ := by
  have hn : ((‖(iterate A b x₀ 0).r‖ : ℝ) : 𝕜) ≠ 0 := by simpa using hr
  have hα := alpha_ne_zero b x₀ hA hr
  rw [Lanczos.coe_alpha _ hA.isSymmetric, Arnoldi.coeff, arnoldi_vec_eq b x₀ hA 0 hr, map_smul,
    inner_smul_left, inner_smul_right, inner_residual_apply_residual_zero b x₀ hA hr,
    ← mul_assoc, conj_sign_mul_sign, inner_self_eq_norm_sq_to_K]
  push_cast
  field_simp

/-- **The diagonal Lanczos coefficients from CG** ([saad2003iterative], (6.101)). Let $A$ be
symmetric and coercive, let $r_0 = b - A x_0$, and suppose that $r_{k+1} \neq 0$. Then the
diagonal coefficient of step $k + 1$ of the Lanczos process of $A$ from $r_0$ is
$$\alpha^L_{k+1} = \frac{1}{\alpha_{k+1}} + \frac{\beta_k}{\alpha_k}.$$

The Lanczos coefficient is `Lanczos.alpha A (b - A x₀) (k + 1)`, a real number embedded in
$\mathbb{K}$. -/
theorem lanczos_alpha_succ_eq {k : ℕ} (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    (Lanczos.alpha A (b - A x₀) (k + 1) : 𝕜) =
      (alpha A (iterate A b x₀ (k + 1)))⁻¹ +
        beta A (iterate A b x₀ k) / alpha A (iterate A b x₀ k) := by
  have hn : ((‖(iterate A b x₀ (k + 1)).r‖ : ℝ) : 𝕜) ≠ 0 := by simpa using hr
  have hα := alpha_ne_zero b x₀ hA hr
  have hαk := alpha_ne_zero b x₀ hA (residual_ne_zero_of_le b x₀ hr (Nat.le_succ k))
  rw [Lanczos.coe_alpha _ hA.isSymmetric, Arnoldi.coeff, arnoldi_vec_eq b x₀ hA (k + 1) hr,
    map_smul, inner_smul_left, inner_smul_right, inner_residual_apply_residual_succ b x₀ hA hr,
    ← mul_assoc, conj_sign_mul_sign, inner_self_eq_norm_sq_to_K]
  push_cast
  field_simp

/-- **The off-diagonal Lanczos coefficients from CG** ([saad2003iterative], (6.103)). Let $A$ be
symmetric and coercive, let $r_0 = b - A x_0$, and suppose that $r_{k+1} \neq 0$. Then the
off-diagonal coefficient of step $k$ of the Lanczos process of $A$ from $r_0$ is
$$\beta^L_k = \frac{\|r_{k+1}\|}{\|r_k\| \operatorname{Re} \alpha_k}.$$
Since $\beta_k = \|r_{k+1}\|^2 / \|r_k\|^2$ and $\alpha_k$ is real, this is
$\sqrt{\beta_k} / \alpha_k$. -/
theorem lanczos_beta_eq {k : ℕ} (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    Lanczos.beta A (b - A x₀) k =
      ‖(iterate A b x₀ (k + 1)).r‖ /
        (‖(iterate A b x₀ k).r‖ * RCLike.re (alpha A (iterate A b x₀ k))) := by
  have hrk := residual_ne_zero_of_le b x₀ hr (Nat.le_succ k)
  have hn : ((‖(iterate A b x₀ (k + 1)).r‖ : ℝ) : 𝕜) ≠ 0 := by simpa using hr
  have hnk : ((‖(iterate A b x₀ k).r‖ : ℝ) : 𝕜) ≠ 0 := by simpa using hrk
  have hα := alpha_ne_zero b x₀ hA hrk
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  rw [RCLike.ofReal_div, RCLike.ofReal_mul, ofReal_re_alpha b x₀ hA k]
  rw [Lanczos.coe_beta, Arnoldi.coeff, arnoldi_vec_eq b x₀ hA (k + 1) hr,
    arnoldi_vec_eq b x₀ hA k hrk, map_smul, inner_smul_left, inner_smul_right,
    inner_residual_succ_apply_residual b x₀ hA hr, ← mul_assoc, conj_sign_succ_mul_sign,
    inner_self_eq_norm_sq_to_K]
  push_cast
  field_simp

/-- For a symmetric coercive $A$ with $r_0 \neq 0$, the first Lanczos coefficient as a real number:
$\alpha^L_0 = (\operatorname{Re} \alpha_0)^{-1}$. -/
private theorem lanczos_alpha_zero_eq_re (hr : (iterate A b x₀ 0).r ≠ 0) :
    Lanczos.alpha A (b - A x₀) 0 = (RCLike.re (alpha A (iterate A b x₀ 0)))⁻¹ := by
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  rw [RCLike.ofReal_inv, ofReal_re_alpha b x₀ hA 0]
  exact lanczos_alpha_zero_eq b x₀ hA hr

/-- For a symmetric coercive $A$ with $r_{k+1} \neq 0$, the diagonal Lanczos coefficient as a real
number: $\alpha^L_{k+1} = (\operatorname{Re} \alpha_{k+1})^{-1} + (\|r_{k+1}\| / \|r_k\|)^2
(\operatorname{Re} \alpha_k)^{-1}$. -/
private theorem lanczos_alpha_succ_eq_re {k : ℕ} (hr : (iterate A b x₀ (k + 1)).r ≠ 0) :
    Lanczos.alpha A (b - A x₀) (k + 1) =
      (RCLike.re (alpha A (iterate A b x₀ (k + 1))))⁻¹ +
        (‖(iterate A b x₀ (k + 1)).r‖ / ‖(iterate A b x₀ k).r‖) ^ 2 *
          (RCLike.re (alpha A (iterate A b x₀ k)))⁻¹ := by
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  have hβ := beta_eq_ofReal (A := A) b x₀ k
  rw [RCLike.ofReal_add, RCLike.ofReal_mul, RCLike.ofReal_inv, RCLike.ofReal_inv,
    RCLike.ofReal_pow, RCLike.ofReal_div, ofReal_re_alpha b x₀ hA (k + 1),
    ofReal_re_alpha b x₀ hA k, lanczos_alpha_succ_eq b x₀ hA hr, hβ]
  push_cast
  ring

/-- **The Lanczos matrix is the $LDL^T$ factorization of CG** ([golub2013matrix], (11.3.15);
[saad2003iterative], §6.7.3). Let $A$ be symmetric and coercive, let $r_0 = b - A x_0$, and
suppose that the full Krylov space $\mathcal{K}_\infty(A, r_0)$ is finite-dimensional. If
$m \le \operatorname{grade}(A, r_0)$, then the $m \times m$ Lanczos matrix of $A$ from $r_0$ is
$$T_m = L D L^T, \qquad D = \operatorname{diag}\Bigl(\frac{1}{\alpha_0}, \dots,
  \frac{1}{\alpha_{m-1}}\Bigr),$$
where $L$ is unit lower bidiagonal with subdiagonal entries
$L_{j+1, j} = \|r_{j+1}\| / \|r_j\|$.

The pivots $d_k = 1/\alpha_{k-1}$ are those of Algorithm 11.3.2 of [golub2013matrix]. Entrywise
the identity is `CG.lanczos_alpha_zero_eq`, `CG.lanczos_alpha_succ_eq` and `CG.lanczos_beta_eq`.
The Lanczos matrix is `Lanczos.tridiag A (b - A x₀) m`, and $D$ uses
$\operatorname{Re} \alpha_j$. -/
theorem lanczos_tridiag_eq_ldl [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {m : ℕ}
    (hm : m ≤ grade A (b - A x₀)) :
    Lanczos.tridiag A (b - A x₀) m =
      Matrix.of (fun i j : Fin m => if (i : ℕ) = j then 1 else if (j : ℕ) + 1 = i then
          ‖(iterate A b x₀ i).r‖ / ‖(iterate A b x₀ j).r‖ else 0) *
        Matrix.diagonal (fun j : Fin m => (RCLike.re (alpha A (iterate A b x₀ j)))⁻¹) *
        (Matrix.of (fun i j : Fin m => if (i : ℕ) = j then 1 else if (j : ℕ) + 1 = i then
          ‖(iterate A b x₀ i).r‖ / ‖(iterate A b x₀ j).r‖ else 0)).transpose := by
  have hne : ∀ k : ℕ, k < m → (iterate A b x₀ k).r ≠ 0 := fun k hk =>
    residual_ne_zero_of_lt_grade b x₀ (hk.trans_le hm)
  ext i j
  rw [Lanczos.tridiag_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
  by_cases hij : (i : ℕ) = j
  · obtain rfl : i = j := Fin.ext hij
    rw [ite_eq_left rfl]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [Fintype.sum_eq_single i fun k hk => ?_]
      · rw [ite_eq_left rfl, one_mul, mul_one, h0]
        exact lanczos_alpha_zero_eq_re b x₀ hA (hne 0 (by omega))
      · have hk' : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
        rw [ite_eq_right hk', ite_eq_right (by omega)]
        simp
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀, (i : ℕ) = k₀ + 1 := ⟨(i : ℕ) - 1, by omega⟩
      let i' : Fin m := ⟨k₀, by omega⟩
      have hii' : i ≠ i' := fun h => by
        have := congrArg Fin.val h
        simp only [i'] at this
        omega
      rw [Fintype.sum_eq_add i i' hii' fun k ⟨hk, hk'⟩ => ?_]
      · have hne' : (i : ℕ) ≠ k₀ := by omega
        have hsucc : k₀ + 1 = (i : ℕ) := hk₀.symm
        simp only [i', ite_true, ite_eq_right hne', ite_eq_left hsucc]
        rw [hk₀, lanczos_alpha_succ_eq_re b x₀ hA (hne (k₀ + 1) (by omega))]
        ring
      · have h1 : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
        have h2 : (k : ℕ) + 1 ≠ i := fun h => hk' (Fin.ext (by simp only [i']; omega))
        rw [ite_eq_right h1, ite_eq_right h2]
        simp
  · rw [ite_eq_right hij]
    by_cases hij1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left hij1, Fintype.sum_eq_single i fun k hk => ?_]
      · have hne' : (j : ℕ) ≠ i := by omega
        rw [ite_eq_left rfl, ite_eq_right hne', ite_eq_left hij1, one_mul,
          lanczos_beta_eq b x₀ hA (k := i) (by rw [hij1]; exact hne j j.2), hij1]
        ring
      · have hk' : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
        rw [ite_eq_right hk']
        by_cases hki : (k : ℕ) + 1 = i
        · rw [ite_eq_left hki, ite_eq_right (by omega), ite_eq_right (by omega)]
          simp
        · rw [ite_eq_right hki]
          simp
    · rw [ite_eq_right hij1]
      by_cases hji : (j : ℕ) + 1 = i
      · rw [ite_eq_left hji, Fintype.sum_eq_single j fun k hk => ?_]
        · rw [ite_eq_right hij, ite_eq_left hji, ite_eq_left rfl, mul_one,
            lanczos_beta_eq b x₀ hA (k := j) (by rw [hji]; exact hne i i.2), hji]
          ring
        · have hk' : (j : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
          rw [ite_eq_right hk']
          by_cases hkj : (k : ℕ) + 1 = j
          · rw [ite_eq_left hkj, ite_eq_right (by omega), ite_eq_right (by omega)]
            simp
          · rw [ite_eq_right hkj]
            simp
      · rw [ite_eq_right hji]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        by_cases h1 : (i : ℕ) = k
        · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
          simp
        · rw [ite_eq_right h1]
          by_cases h2 : (k : ℕ) + 1 = i
          · rw [ite_eq_left h2, ite_eq_right (by omega), ite_eq_right (by omega)]
            simp
          · rw [ite_eq_right h2]
            simp

end LanczosCoefficients

end CG
