/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Hessenberg
import Numlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The two-sided Lanczos process

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A : E \to E$
be linear, and let $B$ be its adjoint, $\langle A x, y \rangle = \langle x, B y \rangle$. The
**Lanczos biorthogonalization** of [saad2003iterative], Algorithm 7.1, starts from a pair
$(v_0, w_0)$ with $\langle w_0, v_0 \rangle = 1$ and builds two sequences $v_j$ and $w_j$ by the
coupled three-term recurrences
$$\delta_{j+1} v_{j+1} = A v_j - \alpha_j v_j - \beta_j v_{j-1}, \qquad \bar\beta_{j+1} w_{j+1} = B
  w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1},$$
with $\alpha_j = \langle w_j, A v_j \rangle$, $\delta_{j+1} = |\langle \hat w_{j+1}, \hat v_{j+1}
\rangle|^{1/2}$ and $\beta_{j+1} = \langle \hat w_{j+1}, \hat v_{j+1} \rangle / \delta_{j+1}$, where
$\hat v_{j+1}$ and $\hat w_{j+1}$ are the right-hand sides. This normalization keeps
$\langle w_j, v_j \rangle = 1$. The main results are Proposition 7.1 of [saad2003iterative]: while
the process does not break down, the two families are biorthogonal,
$\langle w_i, v_j \rangle = \delta_{ij}$, they span the Krylov subspaces $\mathcal{K}_m(A, v_0)$ and
$\mathcal{K}_m(B, w_0)$, and $W_m^H A V_m = T_m$ for the tridiagonal matrix $T_m$ of the
coefficients. The biorthogonality holds for any pair of coupled three-term recurrences normalized by
$\langle w_j, v_j \rangle = 1$, which also covers the normalization $\beta_{j+1} = \|\hat v_{j+1}\|$
of [golub2013matrix], §10.5.5. The relation $A V_m = V_{m+1} \bar T_m$ is a Hessenberg relation with
a basis that is not orthonormal, so the residual formulas for such relations apply.

Breakdown comes in two kinds. A *lucky* breakdown $\hat v_{j+1} = 0$ is benign: the span built so
far is $\mathcal{K}_{j+1}(A, v_0)$, and it is invariant under $A$. A *serious* breakdown,
$\langle \hat w_{j+1}, \hat v_{j+1} \rangle = 0$ with $\hat v_{j+1} \neq 0$, is what the theory has
to exclude. In the polynomial picture of [saad2003iterative], §7.1.2, every vector of the process is
a polynomial in $A$ applied to $v_0$, the dual vectors are the conjugate polynomials in $B$ applied
to $w_0$ up to a scalar, and these polynomials are orthogonal for the indefinite bilinear form
$\langle p, q \rangle = \langle \bar q(B) w_0, p(A) v_0 \rangle$. This form is a moment functional,
so its moment matrix is a Hankel matrix, and a serious breakdown is the vanishing of
$\langle p, p \rangle$ on the current polynomial. The file ends with two methods built on the
process: the biconjugate gradient method (BCG, Algorithm 7.3), whose residuals are biorthogonal and
whose directions are $A$-biconjugate (Proposition 7.2), and the quasi-minimal residual method (QMR,
§7.3), whose residual is within the factor $\kappa_2(V_{m+1})$ of the GMRES residual (Theorem 7.4).

## Main definitions

* `BiLanczos.vec`, `BiLanczos.dualVec`: the primal vectors $v_j$ and the dual vectors $w_j$.
* `BiLanczos.alpha`, `BiLanczos.beta`, `BiLanczos.delta`: the coefficients $\alpha_j$, $\beta_j$ and
  $\delta_j$.
* `BiLanczos.coeff`: the tridiagonal coefficient array $T$, with $\alpha$ on the diagonal, $\delta$
  below it and $\beta$ above it.
* `BiLanczos.NoBreakdown`: $B$ is the adjoint of $A$, $\langle w_0, v_0 \rangle = 1$, and
  $\delta_{j+1} \neq 0$ for $j < m$.
* `BiLanczos.NoSeriousBreakdown`: whenever $\delta_{j+1} = 0$, also $\hat v_{j+1} = 0$.
* `BiLanczos.polyForm`, `BiLanczos.moment`, `BiLanczos.momentMatrix`: the bilinear form
  $\langle p, q \rangle$, the moment functional $L(p) = \langle w_0, p(A) v_0 \rangle$, and the
  moment matrix.
* `BiLanczos.poly`, `BiLanczos.vhatPoly`: the polynomials $p_j$ and $\hat p_j$ with
  $p_j(A) v_0 = v_j$ and $\hat p_j(A) v_0 = \hat v_{j+1}$.
* `BCG.iterate`: the iterates of the biconjugate gradient method.
* `QMR.quasiResidual`, `QMR.IsQuasiMinResidual`: the quasi-residual $\beta e_1 - \bar T_m y$ and the
  specification of the QMR iterate.

## Main results

* `BiLanczos.inner_eq_ite_of_threeTerm`: biorthogonality of any pair of coupled three-term
  recurrences normalized by $\langle w_j, v_j \rangle = 1$.
* `BiLanczos.inner_dualVec_vec`: $\langle w_i, v_j \rangle = \delta_{ij}$ without breakdown.
* `BiLanczos.span_vec`, `BiLanczos.span_dualVec`: the two families span $\mathcal{K}_m(A, v_0)$ and
  $\mathcal{K}_m(B, w_0)$.
* `BiLanczos.inner_dualVec_apply_vec`: $\langle w_i, A v_j \rangle = T_{ij}$, that is,
  $W^H A V = T$.
* `BiLanczos.hessenbergRelation`: without serious breakdown, $A V = V \bar T$ is a Hessenberg
  relation.
* `BiLanczos.NoSeriousBreakdown.of_vhat_eq_zero`,
  `BiLanczos.subspace_succ_mem_invtSubmodule_of_vhat_eq_zero`: a lucky breakdown is not serious, and
  it leaves the Krylov subspace invariant.
* `BiLanczos.polyForm_eq_moment`, `BiLanczos.momentMatrix_apply_eq_of_add_eq`:
  $\langle p, q \rangle = L(pq)$, and the moment matrix is a Hankel matrix.
* `BiLanczos.dualVhat_eq_smul`: $\hat w_{j+1}$ is a multiple of $\bar{\hat p}_j(B) w_0$.
* `BiLanczos.delta_succ_eq_zero_iff_polyForm_eq_zero`: the process breaks down at step $j$ exactly
  when $\langle \hat p_j, \hat p_j \rangle = 0$.
* `BiLanczos.polyForm_vhatPoly_eq_zero`: the polynomials $\hat p_j$ are pairwise orthogonal for the
  form.
* `BCG.inner_residual_dualResidual_eq_zero`, `BCG.inner_dualDirection_apply_direction_eq_zero`: the
  BCG residuals are biorthogonal and its directions are $A$-biconjugate.
* `BCG.isPetrovGalerkin`: the BCG iterate is the Petrov–Galerkin iterate with
  $K = \mathcal{K}_m(A, r_0)$ and $L = \mathcal{K}_m(B, r_0^*)$.
* `QMR.norm_residual_le_norm_quasiResidual`: the residual is at most $C$ times the quasi-residual.
* `QMR.norm_residual_le`: the QMR residual is at most $C / c$ times the GMRES residual.

## Implementation notes

* Indices start at $0$, as in the rest of the Krylov modules. The starting pair, named `(v₁, w₁)` in
  Lean, is $(v_0, w_0)$, and the vector $v_j$ and the coefficients $\alpha_j$, $\beta_j$, $\delta_j$
  here are $v_{j+1}$, $\alpha_{j+1}$, $\beta_{j+1}$, $\delta_{j+1}$ of [saad2003iterative]. The
  initial coefficients are $\beta_0 = \delta_0 = 0$, and $v_{-1} = w_{-1} = 0$.
* The adjoint $B$ of $A$ is taken as data, with the hypothesis `LinearMap.IsAdjointPair` for the
  inner products (see `LinearMap.isAdjointPair_inner_iff'`), because the space is assumed neither
  complete nor finite-dimensional.
* The inner product is conjugate-linear in its first argument. Over $\mathbb{C}$ the dual recurrence
  and the form $\langle p, q \rangle$ therefore carry complex conjugates that [saad2003iterative]
  does not print; over $\mathbb{R}$ the statements are those of the book.
* Breakdown is uniform: since $0^{-1} = 0$ in Lean, the recurrence returns $0$ from the first
  vanishing $\delta$ on.
* An abstract inner product space has no matrix $V_{m+1}$. The two singular-value bounds
  $c \|z\| \le \|\sum_i z_i v_i\| \le C \|z\|$ on the coordinate map are therefore hypotheses of the
  QMR results, and $\kappa_2(V_{m+1})$ is $C / c$.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace BiLanczos

/-- The state of the two-sided Lanczos recurrence at step $j$: the current pair $(v_j, w_j)$, the
previous pair $(v_{j-1}, w_{j-1})$, and the two coefficients $\beta_j$ and $\delta_j$ that the
next step uses. -/
structure State (𝕜 E : Type*) where
  /-- The primal vector $v_j$. -/
  v : E
  /-- The dual vector $w_j$. -/
  w : E
  /-- The previous primal vector $v_{j-1}$, which is $0$ at $j = 0$. -/
  vPrev : E
  /-- The previous dual vector $w_{j-1}$, which is $0$ at $j = 0$. -/
  wPrev : E
  /-- The coefficient $\beta_j$, which is $0$ at $j = 0$. -/
  beta : 𝕜
  /-- The coefficient $\delta_j$, which is $0$ at $j = 0$. -/
  delta : 𝕜

/-- The diagonal coefficient $\alpha_j = \langle w_j, A v_j \rangle$, computed from a state. -/
noncomputable def stepAlpha (A : E →ₗ[𝕜] E) (s : State 𝕜 E) : 𝕜 := inner 𝕜 s.w (A s.v)

/-- The unnormalized primal vector $\hat v_{j+1} = A v_j - \alpha_j v_j - \beta_j v_{j-1}$ of one
step, computed from a state. -/
noncomputable def stepVhat (A : E →ₗ[𝕜] E) (s : State 𝕜 E) : E :=
  A s.v - stepAlpha A s • s.v - s.beta • s.vPrev

/-- The unnormalized dual vector $\hat w_{j+1} = B w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1}$ of
one step, computed from a state. -/
noncomputable def stepWhat (A B : E →ₗ[𝕜] E) (s : State 𝕜 E) : E :=
  B s.w - starRingEnd 𝕜 (stepAlpha A s) • s.w - starRingEnd 𝕜 s.delta • s.wPrev

/-- One step of the two-sided Lanczos process, [saad2003iterative], Algorithm 7.1. From the state at
step $j$ it computes $\alpha_j$, $\hat v_{j+1}$, $\hat w_{j+1}$ and $\zeta = \langle \hat
w_{j+1}, \hat v_{j+1} \rangle$, and sets
$$\delta_{j+1} = |\zeta|^{1/2}, \quad \beta_{j+1} = \zeta / \delta_{j+1}, \quad v_{j+1} =
  \delta_{j+1}^{-1} \hat v_{j+1}, \quad w_{j+1} = \bar\beta_{j+1}^{-1} \hat w_{j+1}.$$
The new state holds $(v_{j+1}, w_{j+1})$, the previous pair $(v_j, w_j)$, $\beta_{j+1}$ and
$\delta_{j+1}$.

If $\zeta = 0$, then $\delta_{j+1} = \beta_{j+1} = 0$ and the new vectors are $0$, by the
convention $0^{-1} = 0$. -/
noncomputable def step (A B : E →ₗ[𝕜] E) (s : State 𝕜 E) : State 𝕜 E :=
  let vh := stepVhat A s
  let wh := stepWhat A B s
  let z : 𝕜 := inner 𝕜 wh vh
  let d : 𝕜 := ((Real.sqrt ‖z‖ : ℝ) : 𝕜)
  { v := d⁻¹ • vh
    w := (starRingEnd 𝕜 (z / d))⁻¹ • wh
    vPrev := s.v
    wPrev := s.w
    beta := z / d
    delta := d }

/-- The state of the two-sided Lanczos process after $j$ steps of `BiLanczos.step`, started from the
pair $(v_0, w_0)$ with $v_{-1} = w_{-1} = 0$ and $\beta_0 = \delta_0 = 0$. -/
noncomputable def state (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : State 𝕜 E :=
  (step A B)^[j] { v := v₁, w := w₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

section Recurrence

variable (A B : E →ₗ[𝕜] E) (v₁ w₁ : E)

/-- The **primal two-sided Lanczos vectors** $v_j$ of $A$ from the starting pair $(v_0, w_0)$.

Without breakdown, $v_0, \dots, v_{m-1}$ is a basis of $\mathcal{K}_m(A, v_0)$
(`BiLanczos.span_vec`). Indices start at $0$, so $v_0$ is the starting vector `v₁`. -/
noncomputable def vec (j : ℕ) : E := (state A B v₁ w₁ j).v

/-- The **dual two-sided Lanczos vectors** $w_j$, built with $B$ from the starting pair
$(v_0, w_0)$.

Without breakdown, $w_0, \dots, w_{m-1}$ is a basis of $\mathcal{K}_m(B, w_0)$
(`BiLanczos.span_dualVec`). Indices start at $0$, so $w_0$ is the starting vector `w₁`. -/
noncomputable def dualVec (j : ℕ) : E := (state A B v₁ w₁ j).w

/-- The previous primal vector $v_{j-1}$, with the convention $v_{-1} = 0$. -/
noncomputable def vecPrev (j : ℕ) : E := (state A B v₁ w₁ j).vPrev

/-- The previous dual vector $w_{j-1}$, with the convention $w_{-1} = 0$. -/
noncomputable def dualVecPrev (j : ℕ) : E := (state A B v₁ w₁ j).wPrev

/-- The **superdiagonal coefficient** $\beta_j$ of the two-sided Lanczos process, with
$\beta_0 = 0$. For $j \ge 0$, $\beta_{j+1} = \langle \hat w_{j+1}, \hat v_{j+1} \rangle /
\delta_{j+1}$.

With 0-based indices, $\beta_j$ here is $\beta_{j+1}$ of [saad2003iterative]. -/
noncomputable def beta (j : ℕ) : 𝕜 := (state A B v₁ w₁ j).beta

/-- The **subdiagonal coefficient** $\delta_j$ of the two-sided Lanczos process, with
$\delta_0 = 0$. For $j \ge 0$, $\delta_{j+1} = |\langle \hat w_{j+1}, \hat v_{j+1}
\rangle|^{1/2}$.

With 0-based indices, $\delta_j$ here is $\delta_{j+1}$ of [saad2003iterative]. -/
noncomputable def delta (j : ℕ) : 𝕜 := (state A B v₁ w₁ j).delta

/-- The **diagonal coefficient** $\alpha_j = \langle w_j, A v_j \rangle$ of the two-sided Lanczos
process. -/
noncomputable def alpha (j : ℕ) : 𝕜 := stepAlpha A (state A B v₁ w₁ j)

/-- The unnormalized primal vector $\hat v_{j+1} = A v_j - \alpha_j v_j - \beta_j v_{j-1}$. -/
noncomputable def vhat (j : ℕ) : E := stepVhat A (state A B v₁ w₁ j)

/-- The unnormalized dual vector $\hat w_{j+1} = B w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1}$.
-/
noncomputable def dualVhat (j : ℕ) : E := stepWhat A B (state A B v₁ w₁ j)

/-- The **biorthogonality scalar** $\zeta_j = \langle \hat w_{j+1}, \hat v_{j+1} \rangle$. The
process breaks down at step $j + 1$ exactly when $\zeta_j = 0$
(`BiLanczos.delta_succ_eq_zero_iff`). -/
noncomputable def zeta (j : ℕ) : 𝕜 := inner 𝕜 (dualVhat A B v₁ w₁ j) (vhat A B v₁ w₁ j)

/-! ### Unfolding the recurrence -/

/-- The first primal vector is the starting vector: $v_0 = $ `v₁`. -/
@[simp] theorem vec_zero : vec A B v₁ w₁ 0 = v₁ := rfl

/-- The first dual vector is the starting vector: $w_0 = $ `w₁`. -/
@[simp] theorem dualVec_zero : dualVec A B v₁ w₁ 0 = w₁ := rfl

/-- The previous primal vector at step $0$ is $v_{-1} = 0$. -/
@[simp] theorem vecPrev_zero : vecPrev A B v₁ w₁ 0 = 0 := rfl

/-- The previous dual vector at step $0$ is $w_{-1} = 0$. -/
@[simp] theorem dualVecPrev_zero : dualVecPrev A B v₁ w₁ 0 = 0 := rfl

/-- The initial superdiagonal coefficient is $\beta_0 = 0$. -/
@[simp] theorem beta_zero : beta A B v₁ w₁ 0 = 0 := rfl

/-- The initial subdiagonal coefficient is $\delta_0 = 0$. -/
@[simp] theorem delta_zero : delta A B v₁ w₁ 0 = 0 := rfl

/-- For every $j$, the state at step $j + 1$ is one `BiLanczos.step` applied to the state at step
$j$. -/
theorem state_succ (j : ℕ) : state A B v₁ w₁ (j + 1) = step A B (state A B v₁ w₁ j) :=
  Function.iterate_succ_apply' _ _ _

/-- For every $j$, the unnormalized next primal vector is
$$\hat v_{j+1} = A v_j - \alpha_j v_j - \beta_j v_{j-1},$$
as in line 5 of Algorithm 7.1 of [saad2003iterative]. -/
theorem vhat_eq (j : ℕ) : vhat A B v₁ w₁ j =
    A (vec A B v₁ w₁ j) - alpha A B v₁ w₁ j • vec A B v₁ w₁ j -
      beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j := rfl

/-- For every $j$, the unnormalized next dual vector is
$$\hat w_{j+1} = B w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1},$$
as in line 6 of Algorithm 7.1 of [saad2003iterative], where $B$ plays the role of $A^H$. -/
theorem dualVhat_eq (j : ℕ) : dualVhat A B v₁ w₁ j =
    B (dualVec A B v₁ w₁ j) - starRingEnd 𝕜 (alpha A B v₁ w₁ j) • dualVec A B v₁ w₁ j -
      starRingEnd 𝕜 (delta A B v₁ w₁ j) • dualVecPrev A B v₁ w₁ j := rfl

/-- For every $j$, $\alpha_j = \langle w_j, A v_j \rangle$, as in line 4 of Algorithm 7.1 of
[saad2003iterative]. -/
theorem alpha_eq (j : ℕ) :
    alpha A B v₁ w₁ j = inner 𝕜 (dualVec A B v₁ w₁ j) (A (vec A B v₁ w₁ j)) := rfl

/-- For every $j$, the previous primal vector at step $j + 1$ is $v_j$. -/
@[simp] theorem vecPrev_succ (j : ℕ) : vecPrev A B v₁ w₁ (j + 1) = vec A B v₁ w₁ j := by
  rw [vecPrev, state_succ]; rfl

/-- For every $j$, the previous dual vector at step $j + 1$ is $w_j$. -/
@[simp] theorem dualVecPrev_succ (j : ℕ) :
    dualVecPrev A B v₁ w₁ (j + 1) = dualVec A B v₁ w₁ j := by
  rw [dualVecPrev, state_succ]; rfl

/-- For every $j$, the next subdiagonal coefficient is
$$\delta_{j+1} = |\langle \hat w_{j+1}, \hat v_{j+1} \rangle|^{1/2},$$
as in line 7 of Algorithm 7.1 of [saad2003iterative]. -/
theorem delta_succ (j : ℕ) :
    delta A B v₁ w₁ (j + 1) = ((Real.sqrt ‖zeta A B v₁ w₁ j‖ : ℝ) : 𝕜) := by
  rw [delta, state_succ]; rfl

/-- For every $j$, the next superdiagonal coefficient is
$$\beta_{j+1} = \frac{\langle \hat w_{j+1}, \hat v_{j+1} \rangle}{\delta_{j+1}},$$
as in line 8 of Algorithm 7.1 of [saad2003iterative]. If $\delta_{j+1} = 0$, then
$\beta_{j+1} = 0$. -/
theorem beta_succ (j : ℕ) :
    beta A B v₁ w₁ (j + 1) = zeta A B v₁ w₁ j / delta A B v₁ w₁ (j + 1) := by
  rw [delta_succ, beta, state_succ]; rfl

/-- For every $j$, the next primal vector is
$$v_{j+1} = \frac{\hat v_{j+1}}{\delta_{j+1}},$$
as in line 10 of Algorithm 7.1 of [saad2003iterative]. On breakdown, $\delta_{j+1} = 0$ and
$v_{j+1} = 0$. -/
theorem vec_succ (j : ℕ) :
    vec A B v₁ w₁ (j + 1) = (delta A B v₁ w₁ (j + 1))⁻¹ • vhat A B v₁ w₁ j := by
  rw [delta_succ, vec, state_succ]; rfl

/-- For every $j$, the next dual vector is
$$w_{j+1} = \frac{\hat w_{j+1}}{\bar\beta_{j+1}},$$
as in line 9 of Algorithm 7.1 of [saad2003iterative]. On breakdown, $\beta_{j+1} = 0$ and
$w_{j+1} = 0$. -/
theorem dualVec_succ (j : ℕ) : dualVec A B v₁ w₁ (j + 1) =
    (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ • dualVhat A B v₁ w₁ j := by
  rw [beta_succ, delta_succ, dualVec, state_succ]; rfl

/-! ### The coefficients -/

/-- The subdiagonal coefficients are real: $\bar\delta_j = \delta_j$ for every $j$.

By definition they are also nonnegative, as square roots. -/
theorem conj_delta (j : ℕ) :
    starRingEnd 𝕜 (delta A B v₁ w₁ j) = delta A B v₁ w₁ j := by
  cases j with
  | zero => rw [delta_zero, map_zero]
  | succ j => rw [delta_succ, RCLike.conj_ofReal]

/-- Breakdown is exactly the vanishing of the biorthogonality scalar: for every $j$,
$$\delta_{j+1} = 0 \iff \langle \hat w_{j+1}, \hat v_{j+1} \rangle = 0.$$
-/
theorem delta_succ_eq_zero_iff (j : ℕ) :
    delta A B v₁ w₁ (j + 1) = 0 ↔ zeta A B v₁ w₁ j = 0 := by
  rw [delta_succ, RCLike.ofReal_eq_zero, Real.sqrt_eq_zero', ← not_lt]
  simp [norm_pos_iff]

/-- The superdiagonal coefficient vanishes at the same scalar as the subdiagonal one:
$\beta_{j+1} = 0$ if and only if $\langle \hat w_{j+1}, \hat v_{j+1} \rangle = 0$. -/
theorem beta_succ_eq_zero_iff (j : ℕ) :
    beta A B v₁ w₁ (j + 1) = 0 ↔ zeta A B v₁ w₁ j = 0 := by
  rw [beta_succ, div_eq_zero_iff, delta_succ_eq_zero_iff, or_self]

/-- The two coefficients of a step vanish together: $\beta_{j+1} \neq 0$ if and only if
$\delta_{j+1} \neq 0$. Either can therefore serve as the breakdown test. -/
theorem beta_succ_ne_zero_iff (j : ℕ) :
    beta A B v₁ w₁ (j + 1) ≠ 0 ↔ delta A B v₁ w₁ (j + 1) ≠ 0 := by
  rw [ne_eq, ne_eq, beta_succ_eq_zero_iff, delta_succ_eq_zero_iff]

/-- For every $j$, the two scaling coefficients multiply to the biorthogonality scalar:
$$\delta_{j+1} \beta_{j+1} = \langle \hat w_{j+1}, \hat v_{j+1} \rangle.$$
This is equation (7.1) of [saad2003iterative].

Lines 9 and 10 of Algorithm 7.1 divide the two unnormalized vectors by these coefficients, so
this product is the only constraint that the normalization
$\langle w_{j+1}, v_{j+1} \rangle = 1$ puts on the pair; see
`BiLanczos.inner_smul_smul_eq_one_of_mul_eq`. No hypothesis is needed, because on breakdown both
sides are $0$. -/
theorem delta_mul_beta_succ (j : ℕ) :
    delta A B v₁ w₁ (j + 1) * beta A B v₁ w₁ (j + 1) = zeta A B v₁ w₁ j := by
  rcases eq_or_ne (delta A B v₁ w₁ (j + 1)) 0 with hd | hd
  · rw [hd, zero_mul, (delta_succ_eq_zero_iff A B v₁ w₁ j).1 hd]
  · rw [beta_succ]
    field_simp

/-- The scaling freedom behind equation (7.1) of [saad2003iterative]. Let $\hat v, \hat w \in E$
with $\langle \hat w, \hat v \rangle \neq 0$, and let $\delta, \beta \in \mathbb{K}$ satisfy
$\delta \beta = \langle \hat w, \hat v \rangle$. Then
$$\Big\langle \frac{\hat w}{\bar\beta}, \frac{\hat v}{\delta} \Big\rangle = 1.$$

So any such pair $(\delta, \beta)$ normalizes a step of the two-sided Lanczos process. The
choice of lines 7 and 8 of Algorithm 7.1 is one such pair (`BiLanczos.delta_mul_beta_succ`); so
is the scaling $\delta = \|\hat v\|_2$ to which the book switches at (7.18). -/
theorem inner_smul_smul_eq_one_of_mul_eq {vh wh : E} {δ β : 𝕜} (hne : inner 𝕜 wh vh ≠ 0)
    (h : δ * β = inner 𝕜 wh vh) :
    inner 𝕜 ((starRingEnd 𝕜 β)⁻¹ • wh) (δ⁻¹ • vh) = 1 := by
  have hd : δ ≠ 0 := by rintro rfl; exact hne (by rw [← h, zero_mul])
  have hb : β ≠ 0 := by rintro rfl; exact hne (by rw [← h, mul_zero])
  rw [inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_conj, ← h]
  field_simp

/-- With the choice of lines 7 and 8 of Algorithm 7.1 of [saad2003iterative], the two coefficients
of a step have the same modulus: for every $j$,
$$|\beta_{j+1}| = |\delta_{j+1}|.$$

Over $\mathbb{R}$ this is the remark of the book that the $\delta_j$ are positive and
$\beta_j = \pm \delta_j$. -/
theorem norm_beta_succ (j : ℕ) :
    ‖beta A B v₁ w₁ (j + 1)‖ = ‖delta A B v₁ w₁ (j + 1)‖ := by
  rw [beta_succ, norm_div, delta_succ, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.div_sqrt]

/-- If $\delta_{j+1} \neq 0$, then $\hat v_{j+1} = \delta_{j+1} v_{j+1}$. -/
theorem smul_vec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) = vhat A B v₁ w₁ j := by
  rw [vec_succ, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- If $\delta_{j+1} \neq 0$, then $\hat w_{j+1} = \bar\beta_{j+1} w_{j+1}$. -/
theorem smul_dualVec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) • dualVec A B v₁ w₁ (j + 1) =
      dualVhat A B v₁ w₁ j := by
  have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
    simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 h
  rw [dualVec_succ, smul_smul, mul_inv_cancel₀ hb, one_smul]

/-- The normalization of Algorithm 7.1 of [saad2003iterative]: if $\delta_{j+1} \neq 0$, then
$$\langle w_{j+1}, v_{j+1} \rangle = 1.$$
-/
theorem inner_dualVec_vec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    inner 𝕜 (dualVec A B v₁ w₁ (j + 1)) (vec A B v₁ w₁ (j + 1)) = 1 := by
  have hz : zeta A B v₁ w₁ j ≠ 0 := fun hc =>
    h ((delta_succ_eq_zero_iff A B v₁ w₁ j).2 hc)
  rw [dualVec_succ, vec_succ, inner_smul_left, inner_smul_right, ← zeta, beta_succ]
  rw [map_inv₀, RCLike.conj_conj]
  field_simp

/-! ### The three-term recurrences -/

/-- The **three-term recurrence of the primal vectors**: if $\delta_{j+1} \neq 0$, then
$$A v_j = \beta_j v_{j-1} + \alpha_j v_j + \delta_{j+1} v_{j+1},$$
with $v_{-1} = 0$. This is equation (7.3) of [saad2003iterative]. -/
theorem apply_vec {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    A (vec A B v₁ w₁ j) = beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j +
      alpha A B v₁ w₁ j • vec A B v₁ w₁ j + delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  rw [smul_vec_succ A B v₁ w₁ h, vhat_eq]
  abel

/-- The **three-term recurrence of the dual vectors**: if $\delta_{j+1} \neq 0$, then
$$B w_j = \bar\delta_j w_{j-1} + \bar\alpha_j w_j + \bar\beta_{j+1} w_{j+1},$$
with $w_{-1} = 0$. This is equation (7.4) of [saad2003iterative], with $B$ in place of $A^H$. -/
theorem apply_dualVec {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    B (dualVec A B v₁ w₁ j) =
      starRingEnd 𝕜 (delta A B v₁ w₁ j) • dualVecPrev A B v₁ w₁ j +
        starRingEnd 𝕜 (alpha A B v₁ w₁ j) • dualVec A B v₁ w₁ j +
        starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) • dualVec A B v₁ w₁ (j + 1) := by
  rw [smul_dualVec_succ A B v₁ w₁ h, dualVhat_eq]
  abel

/-- The **tridiagonal coefficient array** $T$ of the two-sided Lanczos process, as in equation (7.5)
of [saad2003iterative]:
$$T_{jj} = \alpha_j, \qquad T_{j+1,j} = \delta_{j+1}, \qquad T_{j,j+1} = \beta_{j+1},$$
and $T_{ij} = 0$ for $|i - j| > 1$.

The array is indexed by $\mathbb{N} \times \mathbb{N}$, from $0$. -/
noncomputable def coeff (i j : ℕ) : 𝕜 :=
  if i = j then alpha A B v₁ w₁ i
  else if i = j + 1 then delta A B v₁ w₁ i
  else if j = i + 1 then beta A B v₁ w₁ j
  else 0

/-- The diagonal entries of the coefficient array are $T_{jj} = \alpha_j$. -/
@[simp] theorem coeff_self (j : ℕ) : coeff A B v₁ w₁ j j = alpha A B v₁ w₁ j := by
  rw [coeff, ite_eq_left rfl]

/-- The subdiagonal entries of the coefficient array are $T_{j+1,j} = \delta_{j+1}$. -/
@[simp] theorem coeff_succ_self (j : ℕ) :
    coeff A B v₁ w₁ (j + 1) j = delta A B v₁ w₁ (j + 1) := by
  rw [coeff, ite_eq_right (by omega), ite_eq_left rfl]

/-- The superdiagonal entries of the coefficient array are $T_{j,j+1} = \beta_{j+1}$. -/
@[simp] theorem coeff_self_succ (j : ℕ) :
    coeff A B v₁ w₁ j (j + 1) = beta A B v₁ w₁ (j + 1) := by
  rw [coeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

/-- The coefficient array is tridiagonal: if $i \ne j$, $i \ne j + 1$ and $j \ne i + 1$, then
$T_{ij} = 0$. -/
theorem coeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) (h₃ : j ≠ i + 1) :
    coeff A B v₁ w₁ i j = 0 := by
  rw [coeff, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]

/-- The coefficient array is upper Hessenberg: if $i > j + 1$, then $T_{ij} = 0$. This is the
condition that `Krylov.HessenbergRelation` asks for. -/
theorem coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A B v₁ w₁ i j = 0 :=
  coeff_eq_zero A B v₁ w₁ (by omega) (by omega) (by omega)

/-- For every $j$, $\sum_{i < j} T_{ij} v_i = \beta_j v_{j-1}$. -/
private theorem sum_coeff_lt (j : ℕ) :
    ∑ i ∈ Finset.range j, coeff A B v₁ w₁ i j • vec A B v₁ w₁ i =
      beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ n =>
    have hz : ∑ i ∈ Finset.range n, coeff A B v₁ w₁ i (n + 1) • vec A B v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hin : i < n := Finset.mem_range.1 hi
        rw [coeff_eq_zero A B v₁ w₁ (by omega) (by omega) (by omega), zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, coeff_self_succ, vecPrev_succ]

/-! ### The Krylov subspaces -/

private theorem mem_subspace_aux (j : ℕ) :
    vec A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) ∧
      vecPrev A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) := by
  induction j with
  | zero =>
    exact ⟨Krylov.self_mem_subspace A v₁ Nat.one_pos, Submodule.zero_mem _⟩
  | succ j ih =>
    have hmono := Krylov.subspace_mono A v₁ (Nat.le_succ (j + 1))
    refine ⟨?_, by rw [vecPrev_succ]; exact hmono ih.1⟩
    rw [vec_succ]
    refine Submodule.smul_mem _ _ ?_
    rw [vhat_eq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (Krylov.map_subspace_le A v₁ (j + 1) ⟨_, ih.1, rfl⟩)
      (Submodule.smul_mem _ _ (hmono ih.1))) (Submodule.smul_mem _ _ (hmono ih.2))

/-- For every $j$, the primal vector $v_j$ lies in $\mathcal{K}_{j+1}(A, v_0)$: the process only
combines $v_0, A v_0, \dots, A^j v_0$. -/
theorem vec_mem_subspace (j : ℕ) : vec A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) :=
  (mem_subspace_aux A B v₁ w₁ j).1

/-- For every $j$, the previous primal vector $v_{j-1}$ lies in $\mathcal{K}_{j+1}(A, v_0)$. -/
theorem vecPrev_mem_subspace (j : ℕ) : vecPrev A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) :=
  (mem_subspace_aux A B v₁ w₁ j).2

private theorem dualMem_subspace_aux (j : ℕ) :
    dualVec A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) ∧
      dualVecPrev A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) := by
  induction j with
  | zero =>
    exact ⟨Krylov.self_mem_subspace B w₁ Nat.one_pos, Submodule.zero_mem _⟩
  | succ j ih =>
    have hmono := Krylov.subspace_mono B w₁ (Nat.le_succ (j + 1))
    refine ⟨?_, by rw [dualVecPrev_succ]; exact hmono ih.1⟩
    rw [dualVec_succ]
    refine Submodule.smul_mem _ _ ?_
    rw [dualVhat_eq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (Krylov.map_subspace_le B w₁ (j + 1) ⟨_, ih.1, rfl⟩)
      (Submodule.smul_mem _ _ (hmono ih.1))) (Submodule.smul_mem _ _ (hmono ih.2))

/-- For every $j$, the dual vector $w_j$ lies in $\mathcal{K}_{j+1}(B, w_0)$.

No hypothesis on $B$ is needed; in the process, $B$ is the adjoint of $A$. -/
theorem dualVec_mem_subspace (j : ℕ) : dualVec A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) :=
  (dualMem_subspace_aux A B v₁ w₁ j).1

/-- For every $j$, the previous dual vector $w_{j-1}$ lies in $\mathcal{K}_{j+1}(B, w_0)$. -/
theorem dualVecPrev_mem_subspace (j : ℕ) :
    dualVecPrev A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) :=
  (dualMem_subspace_aux A B v₁ w₁ j).2

end Recurrence

/-!
### Biorthogonality

This section proves Proposition 7.1 of [saad2003iterative]. The hypotheses of the section are
collected in `BiLanczos.NoBreakdown`: $B$ is the adjoint of $A$, the starting pair is normalized,
and no $\delta$ vanishes before step $m$.
-/

section Biorthogonality

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The two-sided Lanczos process of $A$ from the pair $(v_0, w_0)$ **runs without breakdown through
step $m$**: $B$ is the adjoint of $A$, $\langle w_0, v_0 \rangle = 1$, and $\delta_{j+1} \neq 0$
for every $j < m$. -/
structure NoBreakdown (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (m : ℕ) : Prop where
  /-- $B$ is the adjoint of $A$: $\langle A x, y \rangle = \langle x, B y \rangle$ for all
  $x, y \in E$. It is taken as data because the space is assumed neither complete nor
  finite-dimensional. -/
  adjoint : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B
  /-- The starting pair is normalized: $\langle w_0, v_0 \rangle = 1$. -/
  inner_start : inner 𝕜 w₁ v₁ = 1
  /-- No breakdown occurs before step $m$: $\delta_{j+1} \neq 0$ for every $j < m$. -/
  delta_ne_zero : ∀ j < m, delta A B v₁ w₁ (j + 1) ≠ 0

/-- If the process runs without breakdown through step $m$ and $n \le m$, then it runs without
breakdown through step $n$. -/
theorem NoBreakdown.mono {m n : ℕ} (h : NoBreakdown A B v₁ w₁ m) (hnm : n ≤ m) :
    NoBreakdown A B v₁ w₁ n :=
  ⟨h.adjoint, h.inner_start, fun j hj => h.delta_ne_zero j (hj.trans_le hnm)⟩

/-- Let $B$ be the adjoint of $A$. Then for all $x, y \in E$,
$$\langle x, A y \rangle = \langle B x, y \rangle.$$
-/
theorem inner_apply_eq
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (x y : E) :
    inner 𝕜 x (A y) = inner 𝕜 (B x) y :=
  (hB.inner_apply_eq x y).symm

/-- Let $B$ be the adjoint of $A$. Then $B^k$ is the adjoint of $A^k$: for every $k \in \mathbb{N}$
and all $x, y \in E$,
$$\langle B^k x, y \rangle = \langle x, A^k y \rangle.$$
-/
theorem inner_pow_apply_eq
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (k : ℕ) (x y : E) :
    inner 𝕜 ((B ^ k) x) y = inner 𝕜 x ((A ^ k) y) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hB' : (B ^ (k + 1)) x = (B ^ k) (B x) := by rw [pow_succ]; rfl
    have hA' : (A ^ (k + 1)) y = A ((A ^ k) y) := by rw [pow_succ']; rfl
    rw [hB', ih (B x), ← inner_apply_eq hB, hA']

/-- Let $B$ be the adjoint of $A$, and let $p$ be a polynomial over $\mathbb{K}$. Then the adjoint
of $p(A)$ is $\bar p(B)$, where $\bar p$ is $p$ with conjugated coefficients: for all
$x, y \in E$,
$$\langle \bar p(B) x, y \rangle = \langle x, p(A) y \rangle.$$

Over $\mathbb{R}$ this says that the transpose of $p(A)$ is $p(A^T)$. It turns the inner product
$\langle q(B) w, p(A) v \rangle$ into $\langle w, (\bar q p)(A) v \rangle$, in which $B$ no
longer appears. The polynomial $\bar p$ is `p.map (starRingEnd 𝕜)`. -/
theorem inner_aeval_map_eq
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (p : Polynomial 𝕜)
    (x y : E) :
    inner 𝕜 (Polynomial.aeval B (p.map (starRingEnd 𝕜)) x)
        y = inner 𝕜 x (Polynomial.aeval A p y) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro q r hq hr
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
      hq, hr]
  · intro k a
    have hB' : Polynomial.aeval B (Polynomial.monomial k (starRingEnd 𝕜 a)) x
        = starRingEnd 𝕜 a • (B ^ k) x := by
      rw [Polynomial.aeval_monomial]
      simp [Module.algebraMap_end_apply]
    have hA' : Polynomial.aeval A (Polynomial.monomial k a) y = a • (A ^ k) y := by
      rw [Polynomial.aeval_monomial]
      simp [Module.algebraMap_end_apply]
    rw [Polynomial.map_monomial, hB', hA', inner_smul_left, inner_smul_right, RCLike.conj_conj,
      inner_pow_apply_eq hB]

/-- **Removing the adjoint.** Let $B$ be the adjoint of $A$, and let $p$ and $q$ be polynomials over
$\mathbb{K}$. Then for all $v, w \in E$,
$$\langle \bar q(B) w, p(A) v \rangle = \langle w, (q p)(A) v \rangle,$$
where $\bar q$ is $q$ with conjugated coefficients. -/
theorem inner_aeval_map_aeval (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
    (p q : Polynomial 𝕜) (v w : E) :
    inner 𝕜 (Polynomial.aeval B (q.map (starRingEnd 𝕜)) w) (Polynomial.aeval A p v) =
      inner 𝕜 w (Polynomial.aeval A (q * p) v) := by
  rw [inner_aeval_map_eq hB q, Module.End.aeval_mul_apply]

/-- **Biorthogonality of coupled three-term recurrences**, the core of Proposition 7.1 of
[saad2003iterative] and of [golub2013matrix], §10.5.5, for any normalization of the two-sided
Lanczos process. Let $B$ be the adjoint of $A$, let $m \in \mathbb{N}$, and let $(v_j)$, $(w_j)$
in $E$ and $(\alpha_j)$, $(\beta_j)$, $(\gamma_j)$ in $\mathbb{K}$ satisfy, for every $j < m$,
$$A v_j = \gamma_j v_{j-1} + \alpha_j v_j + \beta_{j+1} v_{j+1}, \qquad B w_j = \bar\beta_j
  w_{j-1} + \bar\alpha_j w_j + \bar\gamma_{j+1} w_{j+1},$$
with $v_{-1} = w_{-1} = 0$, together with $\alpha_j = \langle w_j, A v_j \rangle$,
$\langle w_j, v_j \rangle = 1$, $\beta_{j+1} \neq 0$ and $\gamma_{j+1} \neq 0$. Then
$$\langle w_i, v_j \rangle = \delta_{ij} \quad \text{for } i, j < m,$$
and the vectors of index $m$ are orthogonal to the other family: $\langle w_i, v_m \rangle = 0$
and $\langle w_m, v_i \rangle = 0$ for $i < m$.

The normalization $\langle w_{j+1}, v_{j+1} \rangle = 1$ fixes only the product
$\beta_{j+1} \gamma_{j+1}$. The choice $|\beta_{j+1}| = |\gamma_{j+1}|$ of [saad2003iterative]
and the choice $\beta_{j+1} = \|\hat v_{j+1}\|$ of [golub2013matrix] both fit. In a run that
stops at step $m$, the vectors of index $m$ are the residuals. The proof is by induction on $m$
and moves $A$ across the inner product. -/
theorem inner_eq_ite_of_threeTerm
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
    {v w : ℕ → E} {α β γ : ℕ → 𝕜} {m : ℕ}
    (hv : ∀ j < m, A (v j) = γ j • (if j = 0 then 0 else v (j - 1)) + α j • v j +
      β (j + 1) • v (j + 1))
    (hw : ∀ j < m, B (w j) = starRingEnd 𝕜 (β j) • (if j = 0 then 0 else w (j - 1)) +
      starRingEnd 𝕜 (α j) • w j + starRingEnd 𝕜 (γ (j + 1)) • w (j + 1))
    (hα : ∀ j < m, inner 𝕜 (w j) (A (v j)) = α j) (hone : ∀ j < m, inner 𝕜 (w j) (v j) = 1)
    (hβ : ∀ j < m, β (j + 1) ≠ 0) (hγ : ∀ j < m, γ (j + 1) ≠ 0) :
    (∀ i < m, ∀ j < m, inner 𝕜 (w i) (v j) = if i = j then 1 else 0) ∧
      (∀ i < m, inner 𝕜 (w i) (v m) = 0) ∧ ∀ j < m, inner 𝕜 (w m) (v j) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨I1, I2, I3⟩ := ih (fun j hj => hv j (by omega)) (fun j hj => hw j (by omega))
      (fun j hj => hα j (by omega)) (fun j hj => hone j (by omega))
      (fun j hj => hβ j (by omega)) (fun j hj => hγ j (by omega))
    -- biorthogonality through `m`
    have J : ∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (w i) (v j) = if i = j then 1 else 0 := by
      intro i hi j hj
      rcases hi.lt_or_eq with hi | hi <;> rcases hj.lt_or_eq with hj | hj
      · exact I1 i hi j hj
      · rw [hj, I2 i hi, ite_eq_right hi.ne]
      · rw [hi, I3 j hj, ite_eq_right hj.ne']
      · rw [hi, hj, hone m (by omega), ite_eq_left rfl]
    have Jv : ∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (w i) (if j = 0 then 0 else v (j - 1)) =
        if i + 1 = j then 1 else 0 := by
      intro i hi j hj
      split_ifs with h0 h1 h1
      · omega
      · exact inner_zero_right _
      · rw [J i hi (j - 1) (by omega), ite_eq_left (by omega)]
      · rw [J i hi (j - 1) (by omega), ite_eq_right (by omega)]
    have Jw : ∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (if i = 0 then 0 else w (i - 1)) (v j) =
        if i = j + 1 then 1 else 0 := by
      intro i hi j hj
      split_ifs with h0 h1 h1
      · omega
      · exact inner_zero_left _
      · rw [J (i - 1) (by omega) j hj, ite_eq_left (by omega)]
      · rw [J (i - 1) (by omega) j hj, ite_eq_right (by omega)]
    refine ⟨fun i hi j hj => J i (by omega) j (by omega), fun i hi => ?_, fun j hj => ?_⟩
    · -- the new primal vector is orthogonal to the dual vectors built so far
      have e : β (m + 1) • v (m + 1) =
          A (v m) - γ m • (if m = 0 then 0 else v (m - 1)) - α m • v m := by
        rw [hv m (by omega)]; abel
      have key : β (m + 1) * inner 𝕜 (w i) (v (m + 1)) = 0 := by
        rw [← inner_smul_right, e, inner_sub_right, inner_sub_right, inner_smul_right,
          inner_smul_right, Jv i (by omega) m le_rfl, J i (by omega) m le_rfl]
        rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | rfl
        · rw [inner_apply_eq hB, hw i (by omega), inner_add_left, inner_add_left,
            inner_smul_left, inner_smul_left, inner_smul_left, RCLike.conj_conj,
            RCLike.conj_conj, RCLike.conj_conj, Jw i hi.le m le_rfl, J i hi.le m le_rfl,
            J (i + 1) hi m le_rfl]
          by_cases h : i + 1 = m <;> simp [h, hi.ne, show i ≠ m + 1 by omega]
        · rw [hα i (by omega)]
          simp
      exact (mul_eq_zero.1 key).resolve_left (hβ m (by omega))
    · -- the new dual vector is orthogonal to the primal vectors built so far
      have e : starRingEnd 𝕜 (γ (m + 1)) • w (m + 1) =
          B (w m) - starRingEnd 𝕜 (β m) • (if m = 0 then 0 else w (m - 1)) -
            starRingEnd 𝕜 (α m) • w m := by
        rw [hw m (by omega)]; abel
      have key : γ (m + 1) * inner 𝕜 (w (m + 1)) (v j) = 0 := by
        rw [← RCLike.conj_conj (γ (m + 1)), ← inner_smul_left, e, inner_sub_left, inner_sub_left,
          inner_smul_left, inner_smul_left, RCLike.conj_conj, RCLike.conj_conj,
          Jw m le_rfl j (by omega), J m le_rfl j (by omega), ← inner_apply_eq hB]
        rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | rfl
        · rw [hv j (by omega), inner_add_right, inner_add_right, inner_smul_right,
            inner_smul_right, inner_smul_right, Jv m le_rfl j hj.le, J m le_rfl j hj.le,
            J m le_rfl (j + 1) hj]
          by_cases h : j + 1 = m
          · simp [h, hj.ne', show m + 1 ≠ j by omega]
          · simp [Ne.symm h, hj.ne', show m + 1 ≠ j by omega]
        · rw [hα j (by omega)]
          simp
      exact (mul_eq_zero.1 key).resolve_left (hγ m (by omega))

/-- The biorthogonality relation $\langle w_i, v_j \rangle = \delta_{ij}$ for all $i, j \le m$. -/
private def Biorth (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (m : ℕ) : Prop :=
  ∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (dualVec A B v₁ w₁ i) (vec A B v₁ w₁ j) = if i = j then 1 else 0

private theorem inner_dualVec_vecPrev {n : ℕ} (hP : Biorth A B v₁ w₁ n) {i j : ℕ} (hi : i ≤ n)
    (hj : j ≤ n) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (vecPrev A B v₁ w₁ j) = if i + 1 = j then 1 else 0 := by
  cases j with
  | zero => simp
  | succ j => rw [vecPrev_succ, hP i hi j (by omega)]; simp

/-- Without breakdown through step $m$, the process is biorthogonal up to step $m$; it satisfies the
recurrences of `BiLanczos.inner_eq_ite_of_threeTerm` with $\gamma = \beta$ and $\beta = \delta$
there. -/
private theorem biorth {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) : Biorth A B v₁ w₁ m := by
  have hprev : ∀ j, vecPrev A B v₁ w₁ j = if j = 0 then 0 else vec A B v₁ w₁ (j - 1) :=
    fun j => by cases j <;> simp
  have hdprev : ∀ j, dualVecPrev A B v₁ w₁ j = if j = 0 then 0 else dualVec A B v₁ w₁ (j - 1) :=
    fun j => by cases j <;> simp
  have hone : ∀ j ≤ m, inner 𝕜 (dualVec A B v₁ w₁ j) (vec A B v₁ w₁ j) = 1 := fun j hj => by
    cases j with
    | zero => exact h.inner_start
    | succ j => exact inner_dualVec_vec_succ A B v₁ w₁ (h.delta_ne_zero j (by omega))
  obtain ⟨I1, I2, I3⟩ := inner_eq_ite_of_threeTerm h.adjoint (v := vec A B v₁ w₁)
    (w := dualVec A B v₁ w₁) (α := alpha A B v₁ w₁) (β := delta A B v₁ w₁)
    (γ := beta A B v₁ w₁) (m := m)
    (fun j hj => by rw [← hprev]; exact apply_vec A B v₁ w₁ (h.delta_ne_zero j hj))
    (fun j hj => by rw [← hdprev]; exact apply_dualVec A B v₁ w₁ (h.delta_ne_zero j hj))
    (fun j _ => (alpha_eq A B v₁ w₁ j).symm) (fun j hj => hone j hj.le)
    (fun j hj => h.delta_ne_zero j hj)
    (fun j hj => (beta_succ_ne_zero_iff A B v₁ w₁ j).2 (h.delta_ne_zero j hj))
  intro i hi j hj
  rcases hi.lt_or_eq with hi | hi <;> rcases hj.lt_or_eq with hj | hj
  · exact I1 i hi j hj
  · rw [hj, I2 i hi, ite_eq_right hi.ne]
  · rw [hi, I3 j hj, ite_eq_right hj.ne']
  · rw [hi, hj, hone m le_rfl, ite_eq_left rfl]

/-- **Biorthogonality** (part of Proposition 7.1 of [saad2003iterative]). If the two-sided Lanczos
process runs without breakdown through step $m$, then for all $i, j \le m$,
$$\langle w_i, v_j \rangle = \delta_{ij}.$$
-/
theorem inner_dualVec_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (vec A B v₁ w₁ j) = if i = j then 1 else 0 :=
  biorth h i hi j hj

/-- Biorthogonality in the other order (part of Proposition 7.1 of [saad2003iterative]). If the
two-sided Lanczos process runs without breakdown through step $m$, then for all $i, j \le m$,
$$\langle v_i, w_j \rangle = \delta_{ij}.$$
-/
theorem inner_vec_dualVec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) :
    inner 𝕜 (vec A B v₁ w₁ i) (dualVec A B v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [← inner_conj_symm, inner_dualVec_vec h hj hi]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- The coefficient array is the oblique compression of $A$ (part of Proposition 7.1 of
[saad2003iterative]). If the two-sided Lanczos process runs without breakdown through step
$m + 1$, then for all $i \le m + 1$ and $j \le m$,
$$\langle w_i, A v_j \rangle = T_{ij}.$$
In matrix form, $W_{m+2}^H A V_{m+1} = \bar T_{m+1}$, and in particular
$W_{m+1}^H A V_{m+1} = T_{m+1}$: the matrix $T_{m+1}$ represents the oblique compression of $A$
to $\mathcal{K}_{m+1}(A, v_0)$ along $\mathcal{K}_{m+1}(B, w_0)$. -/
theorem inner_dualVec_apply_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1)) {i j : ℕ}
    (hi : i ≤ m + 1) (hj : j ≤ m) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (A (vec A B v₁ w₁ j)) = coeff A B v₁ w₁ i j := by
  have hd : delta A B v₁ w₁ (j + 1) ≠ 0 := h.delta_ne_zero j (by omega)
  rw [apply_vec _ _ _ _ hd, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_dualVec_vecPrev (biorth h) hi (by omega),
    inner_dualVec_vec h hi (by omega), inner_dualVec_vec h hi (by omega), coeff]
  by_cases h1 : i = j
  · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_left h1,
      ite_eq_right (by omega : i ≠ j + 1), ite_eq_left h1, h1]
    ring
  · by_cases h2 : i = j + 1
    · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_right h1, ite_eq_left h2,
        ite_eq_right h1, ite_eq_left h2, h2]
      ring
    · by_cases h3 : j = i + 1
      · rw [ite_eq_left (by omega : i + 1 = j), ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        ring
      · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        ring


open Matrix in
/-- **The Petrov–Galerkin condition** ([golub2013matrix], §11.4.5; [saad2003iterative], §7.1).
Suppose that the two-sided Lanczos process runs without breakdown through step $m + 1$. Let
$r \in E$, and let $y \in \mathbb{K}^{m+1}$ solve the tridiagonal system
$$T_{m+1} y = \big( \langle w_i, r \rangle \big)_{i=0}^{m}.$$
Then for every $i \le m$,
$$\Big\langle w_i, r - A \sum_{j=0}^{m} y_j v_j \Big\rangle = 0.$$

The proof uses $W_{m+1}^H A V_{m+1} = T_{m+1}$ (`BiLanczos.inner_dualVec_apply_vec`). For
$r = b - A x_0$ this is the condition that defines the iterate of the biconjugate gradient
method. The matrix $T_{m+1}$ is `Krylov.hessenbergSqOf (BiLanczos.coeff A B v₁ w₁) (m + 1)`. -/
theorem inner_dualVec_sub_apply_sum_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1)) {r : E}
    {y : Fin (m + 1) → 𝕜}
    (hy : hessenbergSqOf (coeff A B v₁ w₁) (m + 1) *ᵥ y =
      fun i : Fin (m + 1) => inner 𝕜 (dualVec A B v₁ w₁ i) r)
    (i : Fin (m + 1)) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (r - A (∑ j, y j • vec A B v₁ w₁ j)) = 0 := by
  have hsum : inner 𝕜 (dualVec A B v₁ w₁ i) (A (∑ j, y j • vec A B v₁ w₁ j)) =
      (hessenbergSqOf (coeff A B v₁ w₁) (m + 1) *ᵥ y) i := by
    rw [map_sum, inner_sum]
    simp only [map_smul, inner_smul_right, Matrix.mulVec, dotProduct, hessenbergSqOf,
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_dualVec_apply_vec h (by omega) (by omega), mul_comm]
  rw [inner_sub_right, hsum, hy, sub_self]

end Biorthogonality

/-! ### The Hessenberg relation and the Krylov bases -/

section Relation

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The two-sided Lanczos process **has no serious breakdown**: for every $j$, if
$\delta_{j+1} = 0$, then $\hat v_{j+1} = 0$, so the primal recurrence has already terminated.

This holds generically and at a regular termination $\hat v_{j+1} = 0$, and it is what the
Hessenberg relation needs. A serious breakdown, $\langle \hat w_{j+1}, \hat v_{j+1} \rangle = 0$
with $\hat v_{j+1} \neq 0$, destroys the relation, because there is then no vector along which
to expand $A v_j$. -/
structure NoSeriousBreakdown (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : Prop where
  /-- At a breakdown the primal recurrence has already terminated: $\delta_{j+1} = 0$ implies
  $\hat v_{j+1} = 0$. -/
  vhat_eq_zero : ∀ j, delta A B v₁ w₁ (j + 1) = 0 → vhat A B v₁ w₁ j = 0

/-- Without serious breakdown, $\hat v_{j+1} = \delta_{j+1} v_{j+1}$ for every $j$, including the
degenerate steps. -/
theorem NoSeriousBreakdown.vhat_eq_smul (h : NoSeriousBreakdown A B v₁ w₁) (j : ℕ) :
    vhat A B v₁ w₁ j = delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  by_cases hd : delta A B v₁ w₁ (j + 1) = 0
  · rw [h.vhat_eq_zero j hd, hd, zero_smul]
  · rw [smul_vec_succ _ _ _ _ hd]

/-- Once the primal recurrence has terminated, it stays terminated: if $\hat v_{m+1} = 0$, then
$\hat v_{j+1} = 0$ for every $j \ge m$.

The vector $v_{m+1}$ and every later vector are $0$. -/
theorem vhat_eq_zero_of_le {m : ℕ} (hv : vhat A B v₁ w₁ m = 0) {j : ℕ} (hj : m ≤ j) :
    vhat A B v₁ w₁ j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    change vhat A B v₁ w₁ (m + k + 1) = 0
    have hz : zeta A B v₁ w₁ (m + k) = 0 := by rw [zeta, ih, inner_zero_right]
    have hvec : vec A B v₁ w₁ (m + k + 1) = 0 := by rw [vec_succ, ih, smul_zero]
    have hb : beta A B v₁ w₁ (m + k + 1) = 0 := by rw [beta_succ, hz, zero_div]
    simp [vhat_eq, hvec, hb]

/-- **A lucky breakdown is not a serious one** ([saad2003iterative], §7.1.2). If the process runs
without breakdown through step $m$ and then the primal recurrence terminates,
$\hat v_{m+1} = 0$, then the process has no serious breakdown at any step.

Before step $m$ no $\delta$ vanishes, and from step $m$ on every $\hat v$ vanishes
(`BiLanczos.vhat_eq_zero_of_le`). So the Hessenberg relation and the results built on it survive
a lucky breakdown. -/
theorem NoSeriousBreakdown.of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) : NoSeriousBreakdown A B v₁ w₁ where
  vhat_eq_zero j hj := by
    rcases lt_or_ge j m with hjm | hjm
    · exact absurd hj (h.delta_ne_zero j hjm)
    · exact vhat_eq_zero_of_le hv hjm

/-- Without serious breakdown, the three-term recurrence
$$A v_j = \beta_j v_{j-1} + \alpha_j v_j + \delta_{j+1} v_{j+1}$$
holds at every step $j$. -/
theorem NoSeriousBreakdown.apply_vec (h : NoSeriousBreakdown A B v₁ w₁) (j : ℕ) :
    A (vec A B v₁ w₁ j) = beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j +
      alpha A B v₁ w₁ j • vec A B v₁ w₁ j +
      delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  rw [← h.vhat_eq_smul j, vhat_eq]
  abel

/-- **The Hessenberg relation** $A V = V \bar T$, equation (7.3) of [saad2003iterative]. If the
process has no serious breakdown, then for every $j$
$$A v_j = \sum_{i=0}^{j+1} T_{ij} v_i,$$
and $T$ is upper Hessenberg.

This is a `Krylov.HessenbergRelation` whose basis is biorthogonal rather than orthonormal, so
the residual formula `Krylov.HessenbergRelation₂.residual_eq` applies to it unchanged. -/
theorem hessenbergRelation (h : NoSeriousBreakdown A B v₁ w₁) :
    Krylov.HessenbergRelation A (vec A B v₁ w₁) (coeff A B v₁ w₁) where
  apply_eq j := by
    have hr : j + 2 = j + 1 + 1 := rfl
    rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, sum_coeff_lt, coeff_self,
      coeff_succ_self]
    exact h.apply_vec j
  eq_zero_of_lt _ _ hij := coeff_eq_zero_of_lt _ _ _ _ hij

/-- **The Hessenberg relation for a run of $m$ steps**, equation (7.3) of [saad2003iterative].
Suppose that the process runs without breakdown through step $m$. Let $z_j = v_j$ for $j < m$
and $z_j = 0$ for $j \ge m$, and let $h_{ij} = T_{ij}$ for $j < m$ and $h_{ij} = 0$ for
$j \ge m$. Then for every $j$
$$A z_j = \sum_{i=0}^{j+1} h_{ij} v_i,$$
and $h$ is upper Hessenberg.

This is a `Krylov.HessenbergRelation₂`, so the residual formulas
`Krylov.HessenbergRelation₂.residual_eq` and
`Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq` apply. Unlike
`BiLanczos.hessenbergRelation`, it needs nothing of the process after step $m$. -/
theorem NoBreakdown.hessenbergRelation₂ {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Krylov.HessenbergRelation₂ A (fun j => if j < m then vec A B v₁ w₁ j else 0)
      (vec A B v₁ w₁) (fun i j => if j < m then coeff A B v₁ w₁ i j else 0) where
  apply_eq j := by
    by_cases hj : j < m
    · simp only [hj, ite_true]
      rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
        sum_coeff_lt, coeff_self, coeff_succ_self]
      exact apply_vec _ _ _ _ (h.delta_ne_zero j hj)
    · simp only [hj, ite_false, map_zero, zero_smul, Finset.sum_const_zero]
  eq_zero_of_lt i j hij := by
    by_cases hj : j < m
    · simp only [hj, ite_true]
      exact coeff_eq_zero_of_lt _ _ _ _ hij
    · simp only [hj, ite_false]

private theorem map_span_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    Submodule.map A (Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio k)) ≤
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < k := hi
  have hd : delta A B v₁ w₁ (i + 1) ≠ 0 := h.delta_ne_zero i (lt_of_lt_of_le hi' hk)
  have hmem : ∀ l < k + 1, vec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, apply_vec _ _ _ _ hd]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · cases i with
    | zero => rw [vecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [vecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem (i + 1) (by omega))

private theorem pow_apply_mem_span {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    (A ^ k) v₁ ∈ Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  induction k with
  | zero =>
    have h0 : (A ^ 0) v₁ = vec A B v₁ w₁ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ k ih =>
    have hpow : (A ^ (k + 1)) v₁ = A ((A ^ k) v₁) := by rw [pow_succ']; rfl
    rw [hpow]
    exact map_span_le h hk ⟨_, ih (by omega), rfl⟩

/-- If the process runs without breakdown through step $m$, then
$$\operatorname{span}\{v_0, \dots, v_m\} = \mathcal{K}_{m+1}(A, v_0).$$

These are $m + 1$ vectors, one more than `BiLanczos.span_vec` accounts for. This is the form
that the lucky breakdown of [saad2003iterative], §7.1.2, needs: at a breakdown after step $m$
the process does not run without breakdown through step $m + 1$, but $v_m$ exists and the span
has already closed up. -/
theorem span_vec_succ {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) = Krylov.subspace A v₁ (m + 1) := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact Krylov.subspace_mono A v₁ (Nat.succ_le_of_lt hi) (vec_mem_subspace A B v₁ w₁ i)
  · rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m + 1 := hk
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (pow_apply_mem_span h (by omega))

/-- The primal vectors span the Krylov subspace (part of Proposition 7.1 of [saad2003iterative]). If
the process runs without breakdown through step $m$, then
$$\operatorname{span}\{v_0, \dots, v_{m-1}\} = \mathcal{K}_m(A, v_0).$$
-/
theorem span_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio m) = Krylov.subspace A v₁ m := by
  rcases m with _ | m
  · simp
  · exact span_vec_succ (h.mono m.le_succ)

/-- **Lucky breakdown** ([saad2003iterative], §7.1.2). If the process runs without breakdown through
step $m$ and $\hat v_{m+1} = 0$, then $A$ maps $\operatorname{span}\{v_0, \dots, v_m\}$ into
itself.

The last three-term relation loses its term in $v_{m+1}$, and the span closes up. -/
theorem map_span_vec_succ_le_of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) :
    Submodule.map A (Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1))) ≤
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < m + 1 := hi
  have hmem : ∀ l < m + 1, vec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with him | him
  · exact map_span_le h (le_refl m) ⟨_, Submodule.subset_span ⟨i, him, rfl⟩, rfl⟩
  · subst him
    have happ : A (vec A B v₁ w₁ i) =
        alpha A B v₁ w₁ i • vec A B v₁ w₁ i + beta A B v₁ w₁ i • vecPrev A B v₁ w₁ i := by
      have h0 : A (vec A B v₁ w₁ i) - alpha A B v₁ w₁ i • vec A B v₁ w₁ i -
          beta A B v₁ w₁ i • vecPrev A B v₁ w₁ i = 0 := by
        rw [← vhat_eq]; exact hv
      rw [sub_sub, sub_eq_zero] at h0
      exact h0
    rw [SetLike.mem_coe, happ]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem i hi')) ?_
    cases i with
    | zero => rw [vecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [vecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))

/-- **Lucky breakdown** ([saad2003iterative], §7.1.2), for the Krylov subspace. If the process runs
without breakdown through step $m$ and $\hat v_{m+1} = 0$, then $\mathcal{K}_{m+1}(A, v_0)$ is
invariant under $A$. -/
theorem subspace_succ_mem_invtSubmodule_of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) :
    Krylov.subspace A v₁ (m + 1) ∈ Module.End.invtSubmodule A := by
  rw [← span_vec_succ h]
  exact (Module.End.mem_invtSubmodule_iff_map_le A).2 (map_span_vec_succ_le_of_vhat_eq_zero h hv)

private theorem map_dualSpan_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    Submodule.map B (Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio k)) ≤
      Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < k := hi
  have hd : delta A B v₁ w₁ (i + 1) ≠ 0 := h.delta_ne_zero i (lt_of_lt_of_le hi' hk)
  have hmem : ∀ l < k + 1, dualVec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, apply_dualVec _ _ _ _ hd]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · cases i with
    | zero => rw [dualVecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [dualVecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem (i + 1) (by omega))

private theorem pow_apply_mem_dualSpan {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ}
    (hk : k < m) : (B ^ k) w₁ ∈ Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  induction k with
  | zero =>
    have h0 : (B ^ 0) w₁ = dualVec A B v₁ w₁ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ k ih =>
    have hpow : (B ^ (k + 1)) w₁ = B ((B ^ k) w₁) := by rw [pow_succ']; rfl
    rw [hpow]
    exact map_dualSpan_le h (le_of_lt hk) ⟨_, ih (by omega), rfl⟩

/-- The dual vectors span the Krylov subspace of $B$ (part of Proposition 7.1 of
[saad2003iterative]). If the process runs without breakdown through step $m$, then
$$\operatorname{span}\{w_0, \dots, w_{m-1}\} = \mathcal{K}_m(B, w_0).$$
-/
theorem span_dualVec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio m) = Krylov.subspace B w₁ m := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact Krylov.subspace_mono B w₁ (Nat.succ_le_of_lt hi) (dualVec_mem_subspace A B v₁ w₁ i)
  · rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m := hk
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (pow_apply_mem_dualSpan h hk')

end Relation

/-!
### Formal orthogonal polynomials and the moment matrix

This section follows [saad2003iterative], §7.1.2. Every vector of the process is a polynomial in $A$
applied to $v_0$: `BiLanczos.poly` is the sequence with $p_j(A) v_0 = v_j$, and `BiLanczos.vhatPoly`
is the sequence with $\hat p_j(A) v_0 = \hat v_{j+1}$. Both are defined by the divided recurrence,
so that the identities hold also after breakdown. The process orthogonalizes them for the bilinear
form `BiLanczos.polyForm`, $\langle p, q \rangle = \langle \bar q(B) w_0, p(A) v_0 \rangle$. This
form is indefinite: $\langle p, p \rangle$ can vanish for a polynomial $p \neq 0$, and that is what
a serious breakdown is.

The one structural fact about the form is `BiLanczos.polyForm_eq_moment`: it is a moment functional,
$\langle p, q \rangle = L(pq)$ with $L(r) = \langle w_0, r(A) v_0 \rangle$. The symmetry of the form
(`BiLanczos.polyForm_comm`) and the Hankel structure of the moment matrix
(`BiLanczos.momentMatrix_apply_eq_of_add_eq`) follow from it.
-/

section FormalOrthogonalPolynomials

open Polynomial

variable (A B : E →ₗ[𝕜] E) (v₁ w₁ : E)

/-- The **moment functional** of the pair $(v_0, w_0)$: for a polynomial $p$ over $\mathbb{K}$,
$$L(p) = \langle w_0, p(A) v_0 \rangle.$$
Its values on the monomials are the moments $L(x^k) = \langle w_0, A^k v_0 \rangle$ of
[saad2003iterative], §7.1.2. -/
noncomputable def moment (p : 𝕜[X]) : 𝕜 := inner 𝕜 w₁ (Polynomial.aeval A p v₁)

/-- The **bilinear form** of equation (7.7) of [saad2003iterative] on polynomials over $\mathbb{K}$:
$$\langle p, q \rangle = \langle \bar q(B) w_0, p(A) v_0 \rangle,$$
where $\bar q$ is $q$ with conjugated coefficients.

The conjugation of $q$ makes the form bilinear rather than sesquilinear over $\mathbb{C}$; over
$\mathbb{R}$ it is the form of the book. The form is indefinite: $\langle p, p \rangle$ can
vanish for $p \neq 0$, and this is exactly a serious breakdown of the process. -/
noncomputable def polyForm (p q : 𝕜[X]) : 𝕜 :=
  inner 𝕜 (Polynomial.aeval B (q.map (starRingEnd 𝕜)) w₁) (Polynomial.aeval A p v₁)

/-- The **moment matrix** $M_k$ of [saad2003iterative], §7.1.2: the $k \times k$ matrix with entries
$$(M_k)_{ij} = \langle x^i, x^j \rangle, \qquad 0 \le i, j < k,$$
for the bilinear form of (7.7).

Indices start at $0$; the book writes $M_k = \{\langle x^{i-1}, x^{j-1}
\rangle\}_{i,j=1,\dots,k}$. -/
noncomputable def momentMatrix (k : ℕ) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun i j => polyForm A B v₁ w₁ (X ^ (i : ℕ)) (X ^ (j : ℕ))

variable {A B v₁ w₁}

/-- The bilinear form of equation (7.7) of [saad2003iterative] is a **moment functional**. Let $B$
be the adjoint of $A$. Then for all polynomials $p$ and $q$,
$$\langle p, q \rangle = L(pq).$$

All other properties of the form below follow from this identity. -/
theorem polyForm_eq_moment
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (p q : 𝕜[X]) :
    polyForm A B v₁ w₁ p q = moment A v₁ w₁ (p * q) := by
  rw [polyForm, inner_aeval_map_eq hB, moment, mul_comm, map_mul, Module.End.mul_apply]

/-- The bilinear form of equation (7.7) of [saad2003iterative] is symmetric. Let $B$ be the adjoint
of $A$. Then for all polynomials $p$ and $q$,
$$\langle p, q \rangle = \langle q, p \rangle.$$

The form depends only on the product $pq$ (`BiLanczos.polyForm_eq_moment`). -/
theorem polyForm_comm
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (p q : 𝕜[X]) :
    polyForm A B v₁ w₁ p q = polyForm A B v₁ w₁ q p := by
  rw [polyForm_eq_moment hB, polyForm_eq_moment hB, mul_comm]

/-- Let $B$ be the adjoint of $A$. The entries of the moment matrix are the moments:
$(M_k)_{ij} = L(x^{i+j})$ for all $i, j < k$. -/
theorem momentMatrix_apply
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (k : ℕ) (i j : Fin k) :
    momentMatrix A B v₁ w₁ k i j = moment A v₁ w₁ (X ^ ((i : ℕ) + (j : ℕ))) := by
  rw [momentMatrix, Matrix.of_apply, polyForm_eq_moment hB, ← pow_add]

/-- The moment matrix is a **Hankel matrix** ([saad2003iterative], §7.1.2). Let $B$ be the adjoint
of $A$. If $i + j = i' + j'$ for indices below $k$, then
$$(M_k)_{ij} = (M_k)_{i'j'}.$$

The entry $\langle x^i, x^j \rangle = L(x^{i+j})$ depends on $i$ and $j$ only through $i + j$. -/
theorem momentMatrix_apply_eq_of_add_eq
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) {k : ℕ}
    {i j i' j' : Fin k} (h : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ)) :
    momentMatrix A B v₁ w₁ k i j = momentMatrix A B v₁ w₁ k i' j' := by
  rw [momentMatrix_apply hB, momentMatrix_apply hB, h]

/-! ### The polynomials the process computes -/

variable (A B v₁ w₁)

/-- The pair $(p_j, p_{j+1})$ of consecutive primal polynomials, defined by a one-step recursion. -/
private noncomputable def polyPair (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 =>
    (1, C (delta A B v₁ w₁ 1)⁻¹ *
      ((X - C (alpha A B v₁ w₁ 0)) * 1 - C (beta A B v₁ w₁ 0) * 0))
  | j + 1 =>
    ((polyPair A B v₁ w₁ j).2,
      C (delta A B v₁ w₁ (j + 2))⁻¹ *
        ((X - C (alpha A B v₁ w₁ (j + 1))) * (polyPair A B v₁ w₁ j).2 -
          C (beta A B v₁ w₁ (j + 1)) * (polyPair A B v₁ w₁ j).1))

/-- The **polynomials of the two-sided Lanczos process**: $p_0 = 1$ and
$$p_{j+1} = \delta_{j+1}^{-1} \big( (x - \alpha_j) p_j - \beta_j p_{j-1} \big),$$
with $p_{-1} = 0$, so that $p_j(A) v_0 = v_j$ (`BiLanczos.aeval_poly`).

The recurrence is divided by $\delta_{j+1}$ rather than multiplied out. It therefore holds at
every index: after a breakdown the vanishing $\delta$ inverts to $0$, and both $p_j$ and $v_j$
are $0$. -/
noncomputable def poly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] := (polyPair A B v₁ w₁ j).1

/-- The previous polynomial $p_{j-1}$, with the convention $p_{-1} = 0$ that matches
`BiLanczos.vecPrev`. -/
noncomputable def polyPrev (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X]
  | 0 => 0
  | j + 1 => poly A B v₁ w₁ j

/-- The polynomial
$$\hat p_j = (x - \alpha_j) p_j - \beta_j p_{j-1},$$
which satisfies $\hat p_j(A) v_0 = \hat v_{j+1}$ (`BiLanczos.aeval_vhatPoly`).

In the notation of [saad2003iterative], §7.1.2, this is the polynomial $p_j$ with
$\hat v_{j+1} = p_j(A) v_1$. Its indefinite norm $\langle \hat p_j, \hat p_j \rangle$ decides
whether the process breaks down. -/
noncomputable def vhatPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (X - C (alpha A B v₁ w₁ j)) * poly A B v₁ w₁ j - C (beta A B v₁ w₁ j) * polyPrev A B v₁ w₁ j

/-- The first polynomial of the process is $p_0 = 1$. -/
@[simp] theorem poly_zero : poly A B v₁ w₁ 0 = 1 := rfl

/-- The previous polynomial at step $0$ is $p_{-1} = 0$. -/
@[simp] theorem polyPrev_zero : polyPrev A B v₁ w₁ 0 = 0 := rfl

/-- For every $j$, the previous polynomial at step $j + 1$ is $p_j$. -/
@[simp] theorem polyPrev_succ (j : ℕ) : polyPrev A B v₁ w₁ (j + 1) = poly A B v₁ w₁ j := rfl

/-- The normalization step for the polynomials: for every $j$,
$p_{j+1} = \delta_{j+1}^{-1} \hat p_j$. -/
theorem poly_succ (j : ℕ) :
    poly A B v₁ w₁ (j + 1) = C (delta A B v₁ w₁ (j + 1))⁻¹ * vhatPoly A B v₁ w₁ j := by
  cases j with
  | zero => rfl
  | succ j => rfl

private theorem aeval_step (T : E →ₗ[𝕜] E) (a b : 𝕜) (p q : 𝕜[X]) (x : E) :
    Polynomial.aeval T ((X - C a) * p - C b * q) x =
      T (Polynomial.aeval T p x) - a • Polynomial.aeval T p x - b • Polynomial.aeval T q x := by
  rw [map_sub, LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    aeval_X, aeval_C, Module.algebraMap_end_apply, Module.End.aeval_apply_C_mul]

private theorem aeval_poly_aux (j : ℕ) :
    Polynomial.aeval A (poly A B v₁ w₁ j) v₁ = vec A B v₁ w₁ j ∧
      Polynomial.aeval A (polyPrev A B v₁ w₁ j) v₁ = vecPrev A B v₁ w₁ j := by
  induction j with
  | zero => exact ⟨by simp, by simp⟩
  | succ j ih =>
    have hv : Polynomial.aeval A (vhatPoly A B v₁ w₁ j) v₁ = vhat A B v₁ w₁ j := by
      rw [vhatPoly, aeval_step, ih.1, ih.2, vhat_eq]
    exact ⟨by rw [poly_succ, Module.End.aeval_apply_C_mul, hv, vec_succ],
      by rw [polyPrev_succ, ih.1, vecPrev_succ]⟩

/-- The primal vectors are polynomials in $A$ applied to the starting vector ([saad2003iterative],
§7.1.2): for every $j$,
$$p_j(A) v_0 = v_j.$$

No hypothesis is needed: after a breakdown both sides are $0$. -/
theorem aeval_poly (j : ℕ) : Polynomial.aeval A (poly A B v₁ w₁ j) v₁ = vec A B v₁ w₁ j :=
  (aeval_poly_aux A B v₁ w₁ j).1

/-- The unnormalized primal vectors are polynomials in $A$ applied to the starting vector: for every
$j$,
$$\hat p_j(A) v_0 = \hat v_{j+1}.$$
This is the statement of [saad2003iterative], §7.1.2, that there is a polynomial $p_j$ of degree
$j$ with $\hat v_{j+1} = p_j(A) v_1$, in the book's indices.

The degree is given by `BiLanczos.vhatPoly_natDegree`. -/
theorem aeval_vhatPoly (j : ℕ) :
    Polynomial.aeval A (vhatPoly A B v₁ w₁ j) v₁ = vhat A B v₁ w₁ j := by
  rw [vhatPoly, aeval_step, aeval_poly, (aeval_poly_aux A B v₁ w₁ j).2, vhat_eq]

/-! ### Degrees -/

private theorem natDegree_step (a b : 𝕜) {p q : 𝕜[X]} {k : ℕ} (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k + 1) : ((X - C a) * p - C b * q).natDegree ≤ k + 1 := by
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans natDegree_mul_le ?_)
    (le_trans natDegree_mul_le ?_))
  · rw [natDegree_X_sub_C]; omega
  · rw [natDegree_C]; omega

private theorem coeff_step (a b : 𝕜) {p q : 𝕜[X]} {k : ℕ} (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k) : ((X - C a) * p - C b * q).coeff (k + 1) = p.coeff k := by
  rw [sub_mul, coeff_sub, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (n := k + 1) (by omega),
    coeff_eq_zero_of_natDegree_lt (n := k + 1) (by omega), mul_zero, mul_zero, sub_zero, sub_zero]

private theorem natDegree_aux (j : ℕ) :
    (poly A B v₁ w₁ j).natDegree ≤ j ∧ (polyPrev A B v₁ w₁ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hv : (vhatPoly A B v₁ w₁ j).natDegree ≤ j + 1 :=
      natDegree_step _ _ ih.1 (le_trans ih.2 (by omega))
    refine ⟨?_, by rw [polyPrev_succ]; exact le_trans ih.1 (by omega)⟩
    rw [poly_succ]
    exact le_trans natDegree_mul_le (by rw [natDegree_C]; simpa using hv)

/-- For every $j$, the polynomial $p_j$ has degree at most $j$. Without breakdown the degree is
exactly $j$ (`BiLanczos.poly_natDegree`). -/
theorem poly_natDegree_le (j : ℕ) : (poly A B v₁ w₁ j).natDegree ≤ j :=
  (natDegree_aux A B v₁ w₁ j).1

/-- For every $j$, the previous polynomial $p_{j-1}$ has degree at most $j$. -/
theorem polyPrev_natDegree_le (j : ℕ) : (polyPrev A B v₁ w₁ j).natDegree ≤ j :=
  (natDegree_aux A B v₁ w₁ j).2

/-- For every $j$, the polynomial $\hat p_j$ has degree at most $j + 1$. -/
theorem vhatPoly_natDegree_le (j : ℕ) : (vhatPoly A B v₁ w₁ j).natDegree ≤ j + 1 :=
  natDegree_step _ _ (poly_natDegree_le A B v₁ w₁ j)
    (le_trans (polyPrev_natDegree_le A B v₁ w₁ j) (Nat.le_succ j))

/-- For every $j$, the coefficient of $x^{j+1}$ in $\hat p_j$ equals the coefficient of $x^j$ in
$p_j$: multiplication by $x - \alpha_j$ shifts the leading coefficient up. -/
theorem vhatPoly_coeff_succ (j : ℕ) :
    (vhatPoly A B v₁ w₁ j).coeff (j + 1) = (poly A B v₁ w₁ j).coeff j :=
  coeff_step _ _ (poly_natDegree_le A B v₁ w₁ j) (polyPrev_natDegree_le A B v₁ w₁ j)

/-- For every $j$, the coefficient of $x^j$ in $p_j$ is the product of the inverted subdiagonal
coefficients:
$$[x^j] \, p_j = \prod_{i=0}^{j-1} \delta_{i+1}^{-1}.$$
-/
theorem poly_coeff_self (j : ℕ) :
    (poly A B v₁ w₁ j).coeff j = ∏ i ∈ range j, (delta A B v₁ w₁ (i + 1))⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [poly_succ, coeff_C_mul, vhatPoly_coeff_succ, ih, Finset.prod_range_succ]
    ring

variable {A B v₁ w₁}

/-- If the process runs without breakdown through step $m$ and $j \le m$, then the coefficient of
$x^j$ in $p_j$ is not $0$. -/
theorem poly_coeff_self_ne_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (poly A B v₁ w₁ j).coeff j ≠ 0 := by
  rw [poly_coeff_self]
  exact Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero (h.delta_ne_zero i (lt_of_lt_of_le (Finset.mem_range.1 hi) hj))

/-- If the process runs without breakdown through step $m$ and $j \le m$, then $p_j$ has degree
exactly $j$. -/
theorem poly_natDegree {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (poly A B v₁ w₁ j).natDegree = j :=
  le_antisymm (poly_natDegree_le A B v₁ w₁ j)
    (le_natDegree_of_ne_zero (poly_coeff_self_ne_zero h hj))

/-- If the process runs without breakdown through step $m$ and $j \le m$, then $\hat p_j$ has degree
exactly $j + 1$. This is the degree statement of [saad2003iterative], §7.1.2, for the polynomial
with $\hat v_{j+1} = \hat p_j(A) v_0$. -/
theorem vhatPoly_natDegree {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (vhatPoly A B v₁ w₁ j).natDegree = j + 1 :=
  le_antisymm (vhatPoly_natDegree_le A B v₁ w₁ j)
    (le_natDegree_of_ne_zero (by rw [vhatPoly_coeff_succ]; exact poly_coeff_self_ne_zero h hj))

/-! ### The dual polynomials, and the breakdown criterion -/

variable (A B v₁ w₁)

/-- The pair $(p^*_j, p^*_{j+1})$ of consecutive dual polynomials, defined by a one-step recursion.
-/
private noncomputable def dualPolyPair (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 =>
    (1, C (starRingEnd 𝕜 (beta A B v₁ w₁ 1))⁻¹ *
      ((X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ 0))) * 1 -
        C (starRingEnd 𝕜 (delta A B v₁ w₁ 0)) * 0))
  | j + 1 =>
    ((dualPolyPair A B v₁ w₁ j).2,
      C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 2)))⁻¹ *
        ((X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ (j + 1)))) * (dualPolyPair A B v₁ w₁ j).2 -
          C (starRingEnd 𝕜 (delta A B v₁ w₁ (j + 1))) * (dualPolyPair A B v₁ w₁ j).1))

/-- The **dual polynomials** of the two-sided Lanczos process: $p^*_0 = 1$ and
$$p^*_{j+1} = \bar\beta_{j+1}^{-1} \big( (x - \bar\alpha_j) p^*_j - \bar\delta_j p^*_{j-1}
  \big),$$
with $p^*_{-1} = 0$, so that $p^*_j(B) w_0 = w_j$ (`BiLanczos.aeval_dualPoly`). -/
noncomputable def dualPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (dualPolyPair A B v₁ w₁ j).1

/-- The previous dual polynomial $p^*_{j-1}$, with the convention $p^*_{-1} = 0$. -/
noncomputable def dualPolyPrev (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X]
  | 0 => 0
  | j + 1 => dualPoly A B v₁ w₁ j

/-- The dual counterpart of `BiLanczos.vhatPoly`: the polynomial
$$\hat p^*_j = (x - \bar\alpha_j) p^*_j - \bar\delta_j p^*_{j-1},$$
which satisfies $\hat p^*_j(B) w_0 = \hat w_{j+1}$ (`BiLanczos.aeval_dualVhatPoly`). -/
noncomputable def dualVhatPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ j))) * dualPoly A B v₁ w₁ j -
    C (starRingEnd 𝕜 (delta A B v₁ w₁ j)) * dualPolyPrev A B v₁ w₁ j

/-- The scalars $\gamma_j$ of [saad2003iterative], §7.1.2, which relate the dual polynomials to the
primal ones (`BiLanczos.dualVhat_eq_smul`): $\gamma_0 = 1$ and
$$\gamma_{j+1} = \gamma_j \frac{\delta_{j+1}}{\bar\beta_{j+1}}.$$

If $\beta_{j+1} = 0$, then $\gamma_{j+1} = 0$, by the convention of division by $0$ in Lean. -/
noncomputable def dualPolyScalar (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜
  | 0 => 1
  | j + 1 => dualPolyScalar A B v₁ w₁ j *
      (delta A B v₁ w₁ (j + 1) / starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))

/-- The first dual polynomial is $p^*_0 = 1$. -/
@[simp] theorem dualPoly_zero : dualPoly A B v₁ w₁ 0 = 1 := rfl

/-- The previous dual polynomial at step $0$ is $p^*_{-1} = 0$. -/
@[simp] theorem dualPolyPrev_zero : dualPolyPrev A B v₁ w₁ 0 = 0 := rfl

/-- For every $j$, the previous dual polynomial at step $j + 1$ is $p^*_j$. -/
@[simp] theorem dualPolyPrev_succ (j : ℕ) :
    dualPolyPrev A B v₁ w₁ (j + 1) = dualPoly A B v₁ w₁ j := rfl

/-- The first scalar relating dual and primal polynomials is $\gamma_0 = 1$. -/
@[simp] theorem dualPolyScalar_zero : dualPolyScalar A B v₁ w₁ 0 = 1 := rfl

/-- For every $j$, $\gamma_{j+1} = \gamma_j \, \delta_{j+1} / \bar\beta_{j+1}$. -/
theorem dualPolyScalar_succ (j : ℕ) : dualPolyScalar A B v₁ w₁ (j + 1) =
    dualPolyScalar A B v₁ w₁ j *
      (delta A B v₁ w₁ (j + 1) / starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1))) := rfl

/-- The normalization step for the dual polynomials: for every $j$,
$p^*_{j+1} = \bar\beta_{j+1}^{-1} \hat p^*_j$. -/
theorem dualPoly_succ (j : ℕ) : dualPoly A B v₁ w₁ (j + 1) =
    C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ * dualVhatPoly A B v₁ w₁ j := by
  cases j with
  | zero => rfl
  | succ j => rfl

private theorem aeval_dualPoly_aux (j : ℕ) :
    Polynomial.aeval B (dualPoly A B v₁ w₁ j) w₁ = dualVec A B v₁ w₁ j ∧
      Polynomial.aeval B (dualPolyPrev A B v₁ w₁ j) w₁ = dualVecPrev A B v₁ w₁ j := by
  induction j with
  | zero => exact ⟨by simp, by simp⟩
  | succ j ih =>
    have hv : Polynomial.aeval B (dualVhatPoly A B v₁ w₁ j) w₁ = dualVhat A B v₁ w₁ j := by
      rw [dualVhatPoly, aeval_step, ih.1, ih.2, dualVhat_eq]
    exact ⟨by rw [dualPoly_succ, Module.End.aeval_apply_C_mul, hv, dualVec_succ],
      by rw [dualPolyPrev_succ, ih.1, dualVecPrev_succ]⟩

/-- The dual vectors are polynomials in $B$ applied to the starting vector: for every $j$,
$$p^*_j(B) w_0 = w_j.$$
-/
theorem aeval_dualPoly (j : ℕ) :
    Polynomial.aeval B (dualPoly A B v₁ w₁ j) w₁ = dualVec A B v₁ w₁ j :=
  (aeval_dualPoly_aux A B v₁ w₁ j).1

/-- For every $j$, $\hat p^*_j(B) w_0 = \hat w_{j+1}$. -/
theorem aeval_dualVhatPoly (j : ℕ) :
    Polynomial.aeval B (dualVhatPoly A B v₁ w₁ j) w₁ = dualVhat A B v₁ w₁ j := by
  rw [dualVhatPoly, aeval_step, aeval_dualPoly, (aeval_dualPoly_aux A B v₁ w₁ j).2, dualVhat_eq]

private theorem dualPolyScalar_step (j : ℕ) :
    (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ * dualPolyScalar A B v₁ w₁ j =
        dualPolyScalar A B v₁ w₁ (j + 1) * (delta A B v₁ w₁ (j + 1))⁻¹ ∧
      delta A B v₁ w₁ (j + 1) * dualPolyScalar A B v₁ w₁ j =
        dualPolyScalar A B v₁ w₁ (j + 1) * starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) := by
  rcases eq_or_ne (delta A B v₁ w₁ (j + 1)) 0 with hd | hd
  · have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) = 0 := by
      rw [(beta_succ_eq_zero_iff A B v₁ w₁ j).2 ((delta_succ_eq_zero_iff A B v₁ w₁ j).1 hd),
        map_zero]
    rw [dualPolyScalar_succ, hd, hb]
    simp
  · have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
      simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 hd
    rw [dualPolyScalar_succ]
    constructor <;> field_simp

private theorem dualPoly_eq_aux (j : ℕ) :
    dualPoly A B v₁ w₁ j =
        C (dualPolyScalar A B v₁ w₁ j) * (poly A B v₁ w₁ j).map (starRingEnd 𝕜) ∧
      dualVhatPoly A B v₁ w₁ j =
        C (dualPolyScalar A B v₁ w₁ j) * (vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜) := by
  induction j with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [dualVhatPoly, vhatPoly, dualPoly_zero, dualPolyPrev_zero, poly_zero, polyPrev_zero,
      dualPolyScalar_zero, delta_zero, beta_zero]
    simp
  | succ j ih =>
    obtain ⟨hs1, hs2⟩ := dualPolyScalar_step A B v₁ w₁ j
    have hpoly : (poly A B v₁ w₁ (j + 1)).map (starRingEnd 𝕜) =
        C (delta A B v₁ w₁ (j + 1))⁻¹ * (vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜) := by
      rw [poly_succ, Polynomial.map_mul, Polynomial.map_C, map_inv₀, conj_delta]
    have h1 : dualPoly A B v₁ w₁ (j + 1) =
        C (dualPolyScalar A B v₁ w₁ (j + 1)) * (poly A B v₁ w₁ (j + 1)).map (starRingEnd 𝕜) := by
      rw [dualPoly_succ, ih.2, hpoly, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs1]
    refine ⟨h1, ?_⟩
    rw [dualVhatPoly, h1, dualPolyPrev_succ, ih.1, vhatPoly, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_C, polyPrev_succ, conj_delta, mul_sub]
    rw [show C (delta A B v₁ w₁ (j + 1)) *
          (C (dualPolyScalar A B v₁ w₁ j) * (poly A B v₁ w₁ j).map (starRingEnd 𝕜))
        = C (dualPolyScalar A B v₁ w₁ (j + 1)) *
            (C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1))) *
              (poly A B v₁ w₁ j).map (starRingEnd 𝕜)) by
      rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs2]]
    ring

/-- **The dual vectors come from the conjugate polynomials** ([saad2003iterative], §7.1.2: "the same
polynomial intervenes in the equivalent expression of $\hat w_{j+1}$"). For every $j$,
$$\hat w_{j+1} = \gamma_j \, \bar{\hat p}_j(B) \, w_0,$$
where $\bar{\hat p}_j$ is the polynomial $\hat p_j$ with conjugated coefficients and $\gamma_j$
is `BiLanczos.dualPolyScalar`.

Over $\mathbb{R}$ the conjugation has no effect, and this is the statement of the book. -/
theorem dualVhat_eq_smul (j : ℕ) :
    dualVhat A B v₁ w₁ j = dualPolyScalar A B v₁ w₁ j •
      Polynomial.aeval B ((vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜)) w₁ := by
  rw [← aeval_dualVhatPoly, (dualPoly_eq_aux A B v₁ w₁ j).2, Module.End.aeval_apply_C_mul]

/-- The breakdown scalar is the indefinite norm of $\hat p_j$ up to a factor ([saad2003iterative],
§7.1.2): for every $j$,
$$\langle \hat w_{j+1}, \hat v_{j+1} \rangle = \bar\gamma_j \, \langle \hat p_j, \hat p_j
  \rangle.$$
-/
theorem zeta_eq_polyForm (j : ℕ) :
    zeta A B v₁ w₁ j = starRingEnd 𝕜 (dualPolyScalar A B v₁ w₁ j) *
      polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) (vhatPoly A B v₁ w₁ j) := by
  rw [zeta, dualVhat_eq_smul, inner_smul_left, polyForm, ← aeval_vhatPoly]

variable {A B v₁ w₁}

/-- If the process runs without breakdown through step $m$ and $j \le m$, then $\gamma_j \neq 0$. -/
theorem dualPolyScalar_ne_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    dualPolyScalar A B v₁ w₁ j ≠ 0 := by
  induction j with
  | zero => rw [dualPolyScalar_zero]; exact one_ne_zero
  | succ j ih =>
    have hd : delta A B v₁ w₁ (j + 1) ≠ 0 := h.delta_ne_zero j (by omega)
    have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
      simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 hd
    rw [dualPolyScalar_succ]
    exact mul_ne_zero (ih (by omega)) (div_ne_zero hd hb)

/-- **The breakdown criterion** ([saad2003iterative], §7.1.2). If the process runs without breakdown
through step $m$ and $j \le m$, then the process breaks down at step $j + 1$ exactly when the
indefinite norm of $\hat p_j$ vanishes:
$$\delta_{j+1} = 0 \iff \langle \hat p_j, \hat p_j \rangle = 0.$$

The criterion separates a serious breakdown from a lucky one only through the form: the form is
indefinite, so $\langle p, p \rangle = 0$ does not force $p(A) v_0 = 0$. -/
theorem delta_succ_eq_zero_iff_polyForm_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j ≤ m) :
    delta A B v₁ w₁ (j + 1) = 0 ↔
      polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) (vhatPoly A B v₁ w₁ j) = 0 := by
  rw [delta_succ_eq_zero_iff, zeta_eq_polyForm]
  refine ⟨fun hc => ?_, fun hc => by rw [hc, mul_zero]⟩
  rcases mul_eq_zero.1 hc with h1 | h2
  · exact absurd (by simpa using h1) (dualPolyScalar_ne_zero h hj)
  · exact h2

/-! ### Orthogonality -/

private theorem inner_dualVec_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ}
    (hi : i ≤ j) (hj : j < m) : inner 𝕜 (dualVec A B v₁ w₁ i) (vhat A B v₁ w₁ j) = 0 := by
  rw [← smul_vec_succ A B v₁ w₁ (h.delta_ne_zero j hj), inner_smul_right,
    inner_dualVec_vec h (by omega) (by omega), ite_eq_right (by omega), mul_zero]

private theorem inner_eq_zero_of_mem_dualSpan {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j < m) {x : E} (hx : x ∈ Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (j + 1))) :
    inner 𝕜 x (vhat A B v₁ w₁ j) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i < j + 1 := hi
    exact inner_dualVec_vhat_eq_zero h (by omega) hj
  | zero => rw [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **The process computes formal orthogonal polynomials** ([saad2003iterative], §7.1.2). If the
process runs without breakdown through step $m$ and $j < m$, then $\hat p_j$ is orthogonal, for
the form (7.7), to every polynomial $r$ of degree at most $j$:
$$\langle \hat p_j, r \rangle = 0.$$
-/
theorem polyForm_vhatPoly_eq_zero_of_natDegree_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j < m) {r : 𝕜[X]} (hr : r.natDegree ≤ j) :
    polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) r = 0 := by
  have hle : (r.map (starRingEnd 𝕜)).natDegree ≤ j :=
    le_trans (Polynomial.natDegree_map_le) hr
  have hdeg : (r.map (starRingEnd 𝕜)).degree < ((j + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_of_le hle
  rw [polyForm, aeval_vhatPoly]
  refine inner_eq_zero_of_mem_dualSpan h hj ?_
  rw [span_dualVec (h.mono (by omega))]
  exact Krylov.aeval_apply_mem_subspace B w₁ hdeg

/-- The polynomials $\hat p_j$ are pairwise orthogonal for the form (7.7) ([saad2003iterative],
§7.1.2). If the process runs without breakdown through step $m$, then for all $i, j < m$ with
$i \neq j$,
$$\langle \hat p_i, \hat p_j \rangle = 0.$$
-/
theorem polyForm_vhatPoly_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i < m)
    (hj : j < m) (hij : i ≠ j) :
    polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ i) (vhatPoly A B v₁ w₁ j) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [polyForm_comm h.adjoint]
    exact polyForm_vhatPoly_eq_zero_of_natDegree_le h hj
      (le_trans (vhatPoly_natDegree_le A B v₁ w₁ i) (by omega))
  · exact polyForm_vhatPoly_eq_zero_of_natDegree_le h hi
      (le_trans (vhatPoly_natDegree_le A B v₁ w₁ j) (by omega))

end FormalOrthogonalPolynomials

end BiLanczos

/-! ### The biconjugate gradient algorithm -/

namespace BCG

/-- The state of the biconjugate gradient iteration ([saad2003iterative], Algorithm 7.3) at step
$k$: the iterate, the residual, the shadow residual, the search direction and the shadow
direction. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate $x_k$. -/
  x : E
  /-- The residual $r_k = b - A x_k$. -/
  r : E
  /-- The shadow residual $r^*_k$. -/
  rs : E
  /-- The search direction $p_k$. -/
  p : E
  /-- The shadow direction $p^*_k$. -/
  ps : E

/-- The BCG step length $\langle r^*, r \rangle / \langle p^*, A p \rangle$, computed from a state.

This is $(r_j, r^*_j) / (A p_j, p^*_j)$ of [saad2003iterative], written with the inner product
of Mathlib, which is conjugate-linear in its first argument. -/
noncomputable def stepAlpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.rs s.r / inner 𝕜 s.ps (A s.p)

/-- One step of the **biconjugate gradient method**, [saad2003iterative], Algorithm 7.3, with $B$ in
place of $A^H$. From $(x, r, r^*, p, p^*)$ it computes $\alpha = \langle r^*, r \rangle /
\langle p^*, A p \rangle$ and
$$x' = x + \alpha p, \quad r' = r - \alpha A p, \quad r^{*\prime} = r^* - \bar\alpha B p^*,$$
then $\beta = \langle r^{*\prime}, r' \rangle / \langle r^*, r \rangle$ and
$$p' = r' + \beta p, \qquad p^{*\prime} = r^{*\prime} + \bar\beta p^*.$$

A division by $0$ gives $0$, by the convention of Lean. -/
noncomputable def step (A B : E →ₗ[𝕜] E) (s : State E) : State E :=
  let a := stepAlpha A s
  let r' := s.r - a • A s.p
  let rs' := s.rs - starRingEnd 𝕜 a • B s.ps
  let c : 𝕜 := inner 𝕜 rs' r' / inner 𝕜 s.rs s.r
  { x := s.x + a • s.p
    r := r'
    rs := rs'
    p := r' + c • s.p
    ps := rs' + starRingEnd 𝕜 c • s.ps }

/-- The state of the biconjugate gradient method after $k$ steps, started from $x_0$ with
$r_0 = p_0 = b - A x_0$ and $r^*_0 = p^*_0$ equal to the given shadow residual `rs₀`. -/
noncomputable def iterate (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A B)^[k] { x := x₀, r := b - A x₀, rs := rs₀, p := b - A x₀, ps := rs₀ }

section Recurrence

variable (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The **BCG residual** $r_k$. -/
noncomputable def residual (k : ℕ) : E := (iterate A B b x₀ rs₀ k).r

/-- The **BCG shadow residual** $r^*_k$, the residual of the dual system with $B$. -/
noncomputable def dualResidual (k : ℕ) : E := (iterate A B b x₀ rs₀ k).rs

/-- The **BCG search direction** $p_k$. -/
noncomputable def direction (k : ℕ) : E := (iterate A B b x₀ rs₀ k).p

/-- The **BCG shadow direction** $p^*_k$. -/
noncomputable def dualDirection (k : ℕ) : E := (iterate A B b x₀ rs₀ k).ps

/-- The **BCG step length** $\alpha_k = \langle r^*_k, r_k \rangle / \langle p^*_k, A p_k \rangle$,
which is $0$ if the denominator is $0$. -/
noncomputable def alpha (k : ℕ) : 𝕜 :=
  inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) /
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k))

/-- The **BCG direction update coefficient** $\beta_k = \langle r^*_{k+1}, r_{k+1} \rangle / \langle
r^*_k, r_k \rangle$, which is $0$ if the denominator is $0$. -/
noncomputable def beta (k : ℕ) : 𝕜 :=
  inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ (k + 1)) /
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k)

/-- For every $k$, the state at step $k + 1$ is one `BCG.step` applied to the state at step $k$. -/
theorem iterate_succ (k : ℕ) :
    iterate A B b x₀ rs₀ (k + 1) = step A B (iterate A B b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The initial iterate of BCG is $x_0$. -/
@[simp] theorem iterate_zero_x : (iterate A B b x₀ rs₀ 0).x = x₀ := rfl

/-- The initial residual of BCG is $r_0 = b - A x_0$. -/
@[simp] theorem residual_zero : residual A B b x₀ rs₀ 0 = b - A x₀ := rfl

/-- The initial shadow residual of BCG is the given vector $r^*_0$. -/
@[simp] theorem dualResidual_zero : dualResidual A B b x₀ rs₀ 0 = rs₀ := rfl

/-- The initial search direction of BCG is $p_0 = b - A x_0$. -/
@[simp] theorem direction_zero : direction A B b x₀ rs₀ 0 = b - A x₀ := rfl

/-- The initial shadow direction of BCG is $p^*_0 = r^*_0$. -/
@[simp] theorem dualDirection_zero : dualDirection A B b x₀ rs₀ 0 = rs₀ := rfl

/-- For every $k$, $x_{k+1} = x_k + \alpha_k p_k$, as in line 5 of Algorithm 7.3 of
[saad2003iterative]. -/
theorem iterate_succ_x (k : ℕ) : (iterate A B b x₀ rs₀ (k + 1)).x =
    (iterate A B b x₀ rs₀ k).x + alpha A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- For every $k$, $r_{k+1} = r_k - \alpha_k A p_k$, as in line 6 of Algorithm 7.3 of
[saad2003iterative]. -/
theorem residual_succ (k : ℕ) : residual A B b x₀ rs₀ (k + 1) =
    residual A B b x₀ rs₀ k - alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k) := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- For every $k$, $r^*_{k+1} = r^*_k - \bar\alpha_k B p^*_k$, as in line 7 of Algorithm 7.3 of
[saad2003iterative], with $B$ in place of $A^H$. -/
theorem dualResidual_succ (k : ℕ) : dualResidual A B b x₀ rs₀ (k + 1) =
    dualResidual A B b x₀ rs₀ k -
      starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) • B (dualDirection A B b x₀ rs₀ k) := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- For every $k$, $p_{k+1} = r_{k+1} + \beta_k p_k$, as in line 9 of Algorithm 7.3 of
[saad2003iterative]. -/
theorem direction_succ (k : ℕ) : direction A B b x₀ rs₀ (k + 1) =
    residual A B b x₀ rs₀ (k + 1) + beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  simp only [beta, residual, dualResidual, direction, iterate_succ]
  rfl

/-- For every $k$, $p^*_{k+1} = r^*_{k+1} + \bar\beta_k p^*_k$, as in line 10 of Algorithm 7.3 of
[saad2003iterative]. -/
theorem dualDirection_succ (k : ℕ) : dualDirection A B b x₀ rs₀ (k + 1) =
    dualResidual A B b x₀ rs₀ (k + 1) +
      starRingEnd 𝕜 (beta A B b x₀ rs₀ k) • dualDirection A B b x₀ rs₀ k := by
  simp only [beta, residual, dualResidual, dualDirection, iterate_succ]
  rfl

/-!
### Three-term recurrences

This part follows problem P-7.7 of [saad2003iterative]. Eliminating the directions from the coupled
two-term recurrences leaves a three-term recurrence for the residuals alone, and eliminating the
residuals leaves one for the directions. The recurrence for the directions holds without hypothesis.
The recurrence for the residuals divides by $\alpha_k$, so its closed form assumes
$\alpha_k \neq 0$; `BCG.alpha_smul_residual_add_two` is the identity without division behind it.
-/

/-- The residual three-term recurrence of problem P-7.7 of [saad2003iterative], without division:
for every $k$,
$$\alpha_k r_{k+2} = (\alpha_k + \alpha_{k+1} \beta_k) r_{k+1} - \alpha_k \alpha_{k+1} A
  r_{k+1} - \alpha_{k+1} \beta_k r_k.$$
It holds at every step, breakdown included. -/
theorem alpha_smul_residual_add_two (k : ℕ) :
    alpha A B b x₀ rs₀ k • residual A B b x₀ rs₀ (k + 2) =
      (alpha A B b x₀ rs₀ k + alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ (k + 1) -
        (alpha A B b x₀ rs₀ k * alpha A B b x₀ rs₀ (k + 1)) •
          A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) • residual A B b x₀ rs₀ k := by
  have h2 : residual A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 1) -
      alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) :=
    residual_succ A B b x₀ rs₀ (k + 1)
  have h3 : direction A B b x₀ rs₀ (k + 1) =
      residual A B b x₀ rs₀ (k + 1) + beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k :=
    direction_succ A B b x₀ rs₀ k
  have hX : alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k) =
      residual A B b x₀ rs₀ k - residual A B b x₀ rs₀ (k + 1) := by
    rw [residual_succ A B b x₀ rs₀ k]; abel
  have expand : alpha A B b x₀ rs₀ k • (residual A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • (A (residual A B b x₀ rs₀ (k + 1)) +
          beta A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k))) =
      alpha A B b x₀ rs₀ k • residual A B b x₀ rs₀ (k + 1) -
        (alpha A B b x₀ rs₀ k * alpha A B b x₀ rs₀ (k + 1)) •
          A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) •
          (alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k)) := by
    module
  rw [h2, h3, map_add, map_smul, expand, hX]
  module

/-- The **residual three-term recurrence** of problem P-7.7 of [saad2003iterative]. If
$\alpha_k \neq 0$, then
$$r_{k+2} = \Big(1 + \frac{\alpha_{k+1} \beta_k}{\alpha_k}\Big) r_{k+1} - \alpha_{k+1} A
  r_{k+1} - \frac{\alpha_{k+1} \beta_k}{\alpha_k} r_k.$$

The recurrence starts from $r_0 = b - A x_0$ and $r_1 = r_0 - \alpha_0 A r_0$
(`BCG.residual_zero`, `BCG.residual_one`). -/
theorem residual_add_two {k : ℕ} (hk : alpha A B b x₀ rs₀ k ≠ 0) :
    residual A B b x₀ rs₀ (k + 2) =
      (1 + alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k / alpha A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k / alpha A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ k := by
  refine smul_right_injective E hk ?_
  dsimp only
  rw [alpha_smul_residual_add_two]
  match_scalars <;> field_simp

/-- The second BCG residual is $r_1 = r_0 - \alpha_0 A r_0$. It starts the three-term recurrence
`BCG.residual_add_two`. -/
theorem residual_one : residual A B b x₀ rs₀ 1 =
    residual A B b x₀ rs₀ 0 - alpha A B b x₀ rs₀ 0 • A (residual A B b x₀ rs₀ 0) := by
  rw [residual_succ, direction_zero, residual_zero]

/-- The **direction three-term recurrence** of problem P-7.7 of [saad2003iterative]: for every $k$,
$$p_{k+2} = (1 + \beta_{k+1}) p_{k+1} - \alpha_{k+1} A p_{k+1} - \beta_k p_k.$$

The recurrence starts from $p_0 = b - A x_0$ and $p_1 = (1 + \beta_0) p_0 - \alpha_0 A p_0$
(`BCG.direction_zero`, `BCG.direction_one`). Unlike the residual recurrence, it needs no
hypothesis. -/
theorem direction_add_two (k : ℕ) :
    direction A B b x₀ rs₀ (k + 2) =
      (1 + beta A B b x₀ rs₀ (k + 1)) • direction A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) -
        beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  have h1 : direction A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 2) +
      beta A B b x₀ rs₀ (k + 1) • direction A B b x₀ rs₀ (k + 1) :=
    direction_succ A B b x₀ rs₀ (k + 1)
  have h2 : residual A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 1) -
      alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) :=
    residual_succ A B b x₀ rs₀ (k + 1)
  have h3 : residual A B b x₀ rs₀ (k + 1) = direction A B b x₀ rs₀ (k + 1) -
      beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
    rw [direction_succ A B b x₀ rs₀ k]; abel
  rw [h1, h2, h3]
  module

/-- The second BCG direction is $p_1 = (1 + \beta_0) p_0 - \alpha_0 A p_0$. It starts the three-term
recurrence `BCG.direction_add_two`. -/
theorem direction_one : direction A B b x₀ rs₀ 1 =
    (1 + beta A B b x₀ rs₀ 0) • direction A B b x₀ rs₀ 0 -
      alpha A B b x₀ rs₀ 0 • A (direction A B b x₀ rs₀ 0) := by
  rw [direction_succ, residual_succ, direction_zero, residual_zero]
  module

/-- The residual of the BCG state is the true residual: for every $k$, $r_k = b - A x_k$. -/
theorem residual_eq (k : ℕ) :
    residual A B b x₀ rs₀ k = b - A (iterate A B b x₀ rs₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [residual_succ, iterate_succ_x, ih, map_add, map_smul, sub_sub, direction]

/-- Let $B$ be the adjoint of $A$. Then for every $k$ and every $y \in E$,
$$\alpha_k \langle p^*_k, A y \rangle = \langle r^*_k, y \rangle - \langle r^*_{k+1}, y
  \rangle.$$
This telescoping identity is the only way in which $B$ enters the shadow residuals. -/
theorem mul_inner_dualDirection_apply
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B) (k : ℕ)
    (y : E) :
    alpha A B b x₀ rs₀ k * inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A y) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ k) y -
        inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) y := by
  rw [dualResidual_succ, inner_sub_left, inner_smul_left, RCLike.conj_conj,
    BiLanczos.inner_apply_eq hB]
  ring

/-- For every $k$ and every $y \in E$,
$$\alpha_k \langle y, A p_k \rangle = \langle y, r_k \rangle - \langle y, r_{k+1} \rangle.$$
-/
theorem mul_inner_apply_direction (k : ℕ) (y : E) :
    alpha A B b x₀ rs₀ k * inner 𝕜 y (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 y (residual A B b x₀ rs₀ k) - inner 𝕜 y (residual A B b x₀ rs₀ (k + 1)) := by
  rw [residual_succ, inner_sub_right, inner_smul_right]
  ring

private theorem mem_subspace_aux (k : ℕ) :
    residual A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) ∧
      direction A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) := by
  induction k with
  | zero =>
    exact ⟨Krylov.self_mem_subspace _ _ Nat.one_pos, Krylov.self_mem_subspace _ _ Nat.one_pos⟩
  | succ k ih =>
    have hmono := Krylov.subspace_mono A (b - A x₀) (Nat.le_succ (k + 1))
    have hr : residual A B b x₀ rs₀ (k + 1) ∈ Krylov.subspace A (b - A x₀) (k + 1 + 1) := by
      rw [residual_succ]
      exact Submodule.sub_mem _ (hmono ih.1) (Submodule.smul_mem _ _
        (Krylov.map_subspace_le A (b - A x₀) (k + 1) ⟨_, ih.2, rfl⟩))
    refine ⟨hr, ?_⟩
    rw [direction_succ]
    exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ih.2))

/-- For every $k$, the BCG residual $r_k$ lies in $\mathcal{K}_{k+1}(A, r_0)$, where
$r_0 = b - A x_0$. -/
theorem residual_mem_subspace (k : ℕ) :
    residual A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) :=
  (mem_subspace_aux A B b x₀ rs₀ k).1

/-- For every $k$, the BCG direction $p_k$ lies in $\mathcal{K}_{k+1}(A, r_0)$, where
$r_0 = b - A x_0$. -/
theorem direction_mem_subspace (k : ℕ) :
    direction A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) :=
  (mem_subspace_aux A B b x₀ rs₀ k).2

/-- For every $m$, the BCG iterate lies in the affine Krylov space:
$x_m - x_0 \in \mathcal{K}_m(A, r_0)$, where $r_0 = b - A x_0$. -/
theorem iterate_x_sub_mem (m : ℕ) :
    (iterate A B b x₀ rs₀ m).x - x₀ ∈ Krylov.subspace A (b - A x₀) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (iterate A B b x₀ rs₀ (m + 1)).x - x₀ =
        ((iterate A B b x₀ rs₀ m).x - x₀) +
          alpha A B b x₀ rs₀ m • direction A B b x₀ rs₀ m := by
      rw [iterate_succ_x]; abel
    rw [hsplit]
    exact Submodule.add_mem _ (Krylov.subspace_mono A (b - A x₀) (Nat.le_succ m) ih)
      (Submodule.smul_mem _ _ (direction_mem_subspace A B b x₀ rs₀ m))

end Recurrence

/-! ### Biorthogonality of the biconjugate gradient sequences -/

section Biorthogonality

variable {A B : E →ₗ[𝕜] E} {b x₀ rs₀ : E}

/-- The biconjugate gradient method **runs without breakdown through step $m$**: $B$ is the adjoint
of $A$, and for every $k < m$ neither the numerator $\langle r^*_k, r_k \rangle$ nor the
denominator $\langle p^*_k, A p_k \rangle$ of $\alpha_k$ in Algorithm 7.3 of [saad2003iterative]
vanishes. -/
structure NoBreakdown (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (m : ℕ) : Prop where
  /-- $B$ is the adjoint of $A$: $\langle A x, y \rangle = \langle x, B y \rangle$ for all
  $x, y \in E$. -/
  adjoint : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B
  /-- The numerator of $\alpha_k$ does not vanish: $\langle r^*_k, r_k \rangle \neq 0$ for every
  $k < m$. -/
  inner_residual_ne_zero : ∀ k < m,
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) ≠ 0
  /-- The denominator of $\alpha_k$ does not vanish: $\langle p^*_k, A p_k \rangle \neq 0$ for every
  $k < m$. -/
  inner_apply_direction_ne_zero : ∀ k < m,
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) ≠ 0

/-- If BCG runs without breakdown through step $m$ and $n \le m$, then it runs without breakdown
through step $n$. -/
theorem NoBreakdown.mono {m n : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) (hnm : n ≤ m) :
    NoBreakdown A B b x₀ rs₀ n :=
  ⟨h.adjoint, fun k hk => h.inner_residual_ne_zero k (hk.trans_le hnm),
    fun k hk => h.inner_apply_direction_ne_zero k (hk.trans_le hnm)⟩

/-- If BCG runs without breakdown through step $m$, then $\alpha_k \neq 0$ for every $k < m$,
because numerator and denominator are both nonzero. -/
theorem NoBreakdown.alpha_ne_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ} (hk : k < m) :
    alpha A B b x₀ rs₀ k ≠ 0 :=
  div_ne_zero (h.inner_residual_ne_zero k hk) (h.inner_apply_direction_ne_zero k hk)

/-- The invariant of Proposition 7.2 of [saad2003iterative] up to step $m$: the residuals are
biorthogonal and the directions are $A$-biconjugate. -/
private def Biorth (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (m : ℕ) : Prop :=
  (∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ i) = 0) ∧
    ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ i)) = 0

private theorem inner_dualResidual_apply_direction_of_lt {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {j l : ℕ} (hj : j ≤ m) (hl : l ≤ m) (hjl : j < l) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ l)) = 0 := by
  cases j with
  | zero => exact hP.2 l hl 0 hj (by omega)
  | succ n =>
    have hrs : dualResidual A B b x₀ rs₀ (n + 1) =
        dualDirection A B b x₀ rs₀ (n + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ n) • dualDirection A B b x₀ rs₀ n := by
      rw [dualDirection_succ]; abel
    rw [hrs, inner_sub_left, inner_smul_left, RCLike.conj_conj,
      hP.2 l hl (n + 1) hj (by omega), hP.2 l hl n (by omega) (by omega)]
    ring

private theorem inner_dualDirection_apply_residual_of_lt {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {j l : ℕ} (hj : j ≤ m) (hl : l ≤ m) (hjl : j < l) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ l) (A (residual A B b x₀ rs₀ j)) = 0 := by
  cases j with
  | zero => exact hP.2 0 hj l hl (by omega)
  | succ n =>
    have hr : residual A B b x₀ rs₀ (n + 1) =
        direction A B b x₀ rs₀ (n + 1) - beta A B b x₀ rs₀ n • direction A B b x₀ rs₀ n := by
      rw [direction_succ]; abel
    rw [hr, map_sub, map_smul, inner_sub_right, inner_smul_right,
      hP.2 (n + 1) hj l hl (by omega), hP.2 n (by omega) l hl (by omega)]
    ring

private theorem inner_dualResidual_apply_direction_self {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {k : ℕ} (hk : k ≤ m) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) := by
  cases k with
  | zero => rfl
  | succ n =>
    rw [dualDirection_succ, inner_add_left, inner_smul_left, RCLike.conj_conj,
      hP.2 (n + 1) hk n (by omega) (by omega)]
    ring

private theorem inner_dualDirection_apply_residual_self {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {k : ℕ} (hk : k ≤ m) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (residual A B b x₀ rs₀ k)) =
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) := by
  cases k with
  | zero => rfl
  | succ n =>
    rw [direction_succ, map_add, map_smul, inner_add_right, inner_smul_right,
      hP.2 n (by omega) (n + 1) hk (by omega)]
    ring

private theorem biorth_succ {k : ℕ} (h : NoBreakdown A B b x₀ rs₀ (k + 1))
    (hP : Biorth A B b x₀ rs₀ k) : Biorth A B b x₀ rs₀ (k + 1) := by
  have hn : inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) ≠ 0 :=
    h.inner_residual_ne_zero k (Nat.lt_succ_self k)
  have hd : inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) ≠ 0 :=
    h.inner_apply_direction_ne_zero k (Nat.lt_succ_self k)
  have hαk : alpha A B b x₀ rs₀ k *
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) := div_mul_cancel₀ _ hd
  have hX : alpha A B b x₀ rs₀ k * (beta A B b x₀ rs₀ k *
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k))) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ (k + 1)) := by
    rw [alpha, beta]
    field_simp
  have step1 : ∀ j ≤ k,
      inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ (k + 1)) = 0 := by
    intro j hj
    rw [residual_succ, inner_sub_right, inner_smul_right]
    rcases eq_or_lt_of_le hj with rfl | hjk
    · rw [inner_dualResidual_apply_direction_self hP le_rfl, hαk, sub_self]
    · rw [hP.1 k le_rfl j hj (by omega),
        inner_dualResidual_apply_direction_of_lt hP hj le_rfl hjk]
      ring
  have step2 : ∀ i ≤ k,
      inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ i) = 0 := by
    intro i hi
    have hmul := mul_inner_dualDirection_apply A B b x₀ rs₀ h.adjoint k
      (residual A B b x₀ rs₀ i)
    rcases eq_or_lt_of_le hi with rfl | hik
    · rw [inner_dualDirection_apply_residual_self hP le_rfl, hαk] at hmul
      linear_combination hmul
    · rw [hP.1 i hi k le_rfl (by omega),
        inner_dualDirection_apply_residual_of_lt hP hi le_rfl hik] at hmul
      linear_combination hmul
  have step3 : ∀ j ≤ k,
      inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ (k + 1))) = 0 := by
    intro j hj
    have hαj : alpha A B b x₀ rs₀ j ≠ 0 := h.alpha_ne_zero (by omega)
    have hmul := mul_inner_dualDirection_apply A B b x₀ rs₀ h.adjoint j
      (residual A B b x₀ rs₀ (k + 1))
    rw [direction_succ, map_add, map_smul, inner_add_right, inner_smul_right]
    rcases eq_or_lt_of_le hj with rfl | hjk
    · rw [step1 j le_rfl] at hmul
      refine mul_left_cancel₀ hαj ?_
      linear_combination hmul + hX
    · rw [step1 j hj, step1 (j + 1) (by omega)] at hmul
      rw [hP.2 k le_rfl j hj (by omega)]
      refine mul_left_cancel₀ hαj ?_
      linear_combination hmul
  have step4 : ∀ i ≤ k,
      inner 𝕜 (dualDirection A B b x₀ rs₀ (k + 1)) (A (direction A B b x₀ rs₀ i)) = 0 := by
    intro i hi
    have hαi : alpha A B b x₀ rs₀ i ≠ 0 := h.alpha_ne_zero (by omega)
    have hmul := mul_inner_apply_direction A B b x₀ rs₀ i (dualResidual A B b x₀ rs₀ (k + 1))
    rw [dualDirection_succ, inner_add_left, inner_smul_left, RCLike.conj_conj]
    rcases eq_or_lt_of_le hi with rfl | hik
    · rw [step2 i le_rfl] at hmul
      refine mul_left_cancel₀ hαi ?_
      linear_combination hmul + hX
    · rw [step2 i hi, step2 (i + 1) (by omega)] at hmul
      rw [hP.2 i hi k le_rfl (by omega)]
      refine mul_left_cancel₀ hαi ?_
      linear_combination hmul
  refine ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩
  · by_cases hi' : i = k + 1
    · subst hi'
      exact step1 j (by omega)
    · by_cases hj' : j = k + 1
      · subst hj'
        exact step2 i (by omega)
      · exact hP.1 i (by omega) j (by omega) hij
  · by_cases hi' : i = k + 1
    · subst hi'
      exact step3 j (by omega)
    · by_cases hj' : j = k + 1
      · subst hj'
        exact step4 i (by omega)
      · exact hP.2 i (by omega) j (by omega) hij

private theorem biorth {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) : Biorth A B b x₀ rs₀ m := by
  induction m with
  | zero =>
    refine ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩ <;>
      · obtain rfl : i = 0 := Nat.le_zero.1 hi
        obtain rfl : j = 0 := Nat.le_zero.1 hj
        exact absurd rfl hij
  | succ m ih => exact biorth_succ h (ih (h.mono (Nat.le_succ m)))

/-- **Biorthogonality of the BCG residuals** (Proposition 7.2 of [saad2003iterative]). If BCG runs
without breakdown through step $m$, then for all $i, j \le m$ with $i \neq j$,
$$\langle r^*_j, r_i \rangle = 0.$$
-/
theorem inner_residual_dualResidual_eq_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {i j : ℕ}
    (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ i) = 0 :=
  (biorth h).1 i hi j hj hij

/-- **$A$-biconjugacy of the BCG directions** (Proposition 7.2 of [saad2003iterative]). If BCG runs
without breakdown through step $m$, then for all $i, j \le m$ with $i \neq j$,
$$\langle p^*_j, A p_i \rangle = 0.$$
-/
theorem inner_dualDirection_apply_direction_eq_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m)
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ i)) = 0 :=
  (biorth h).2 i hi j hj hij

/-! ### BCG as a Petrov–Galerkin method -/

private theorem apply_dualDirection_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ}
    (hk : k < m) : B (dualDirection A B b x₀ rs₀ k) ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (k + 2)) := by
  have hα : starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) ≠ 0 := by
    simpa using h.alpha_ne_zero hk
  have hsub : dualResidual A B b x₀ rs₀ k - dualResidual A B b x₀ rs₀ (k + 1) =
      starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) • B (dualDirection A B b x₀ rs₀ k) := by
    rw [dualResidual_succ]; abel
  have key : B (dualDirection A B b x₀ rs₀ k) =
      (starRingEnd 𝕜 (alpha A B b x₀ rs₀ k))⁻¹ •
        (dualResidual A B b x₀ rs₀ k - dualResidual A B b x₀ rs₀ (k + 1)) := by
    rw [hsub, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.subset_span ⟨k, by simp, rfl⟩) (Submodule.subset_span ⟨k + 1, by simp, rfl⟩))

private theorem apply_dualResidual_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ}
    (hk : k < m) : B (dualResidual A B b x₀ rs₀ k) ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (k + 2)) := by
  cases k with
  | zero => exact apply_dualDirection_mem_span h hk
  | succ n =>
    have hrs : dualResidual A B b x₀ rs₀ (n + 1) =
        dualDirection A B b x₀ rs₀ (n + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ n) • dualDirection A B b x₀ rs₀ n := by
      rw [dualDirection_succ]; abel
    rw [hrs, map_sub, map_smul]
    refine Submodule.sub_mem _ (apply_dualDirection_mem_span h hk) (Submodule.smul_mem _ _ ?_)
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (apply_dualDirection_mem_span h (by omega))

private theorem pow_apply_mem_dualSpan {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {i : ℕ}
    (hi : i < m) : (B ^ i) rs₀ ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 1)) := by
  induction i with
  | zero =>
    have h0 : (B ^ 0) rs₀ = dualResidual A B b x₀ rs₀ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ i ih =>
    have hpow : (B ^ (i + 1)) rs₀ = B ((B ^ i) rs₀) := by rw [pow_succ']; rfl
    have hmap : Submodule.map B
        (Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 1))) ≤
          Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 2)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : j < i + 1 := hj
      exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
        (apply_dualResidual_mem_span h (by omega))
    rw [hpow]
    exact hmap ⟨_, ih (by omega), rfl⟩

/-- If BCG runs without breakdown through step $m$, then the shadow Krylov space lies in the span of
the shadow residuals:
$$\mathcal{K}_m(B, r^*_0) \subseteq \operatorname{span}\{r^*_0, \dots, r^*_{m-1}\}.$$
This is what makes the BCG residual orthogonal to all of $\mathcal{K}_m(B, r^*_0)$. -/
theorem subspace_le_span_dualResidual {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    Krylov.subspace B rs₀ m ≤ Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio m) := by
  rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < m := hi
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
    (pow_apply_mem_dualSpan h hi')

private theorem inner_eq_zero_of_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio m)) :
    inner 𝕜 u (residual A B b x₀ rs₀ m) = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j < m := hj
    exact inner_residual_dualResidual_eq_zero h le_rfl (le_of_lt hj') (by omega)
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- If BCG runs without breakdown through step $m$, then the residual $r_m$ is orthogonal to the
shadow Krylov space: $\langle u, r_m \rangle = 0$ for every $u \in \mathcal{K}_m(B, r^*_0)$.

This is the biorthogonality of Proposition 7.2 of [saad2003iterative] in the form that the
polynomial arguments of the transpose-free variants use. The shadow residuals span the subspace,
so only $\langle r^*_i, r_m \rangle = 0$ for $i < m$ is involved. -/
theorem inner_residual_eq_zero_of_mem_subspace {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Krylov.subspace B rs₀ m) : inner 𝕜 u (residual A B b x₀ rs₀ m) = 0 :=
  inner_eq_zero_of_mem_span h (subspace_le_span_dualResidual h hu)

/-- For every $k$, the shadow residual $r^*_k$ lies in $\operatorname{span}\{p^*_0, \dots, p^*_k\}$,
because $r^*_0 = p^*_0$ and $r^*_{k+1} = p^*_{k+1} - \bar\beta_k p^*_k$. -/
private theorem dualResidual_mem_span_dualDirection (k : ℕ) :
    dualResidual A B b x₀ rs₀ k ∈
      Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio (k + 1)) := by
  cases k with
  | zero => exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ j =>
    have hrs : dualResidual A B b x₀ rs₀ (j + 1) =
        dualDirection A B b x₀ rs₀ (j + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ j) • dualDirection A B b x₀ rs₀ j := by
      rw [dualDirection_succ]; abel
    rw [hrs]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨j + 1, by simp, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simp, rfl⟩))

/-- If BCG runs without breakdown through step $m$, then the shadow Krylov space also lies in the
span of the shadow directions:
$$\mathcal{K}_m(B, r^*_0) \subseteq \operatorname{span}\{p^*_0, \dots, p^*_{m-1}\}.$$

The shadow residuals and the shadow directions are related by a triangular change of basis. -/
theorem subspace_le_span_dualDirection {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    Krylov.subspace B rs₀ m ≤ Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio m) := by
  refine (subspace_le_span_dualResidual h).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < m := hj
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
    (dualResidual_mem_span_dualDirection j)

private theorem inner_apply_direction_eq_zero_of_mem_span {m : ℕ}
    (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio m)) :
    inner 𝕜 u (A (direction A B b x₀ rs₀ m)) = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j < m := hj
    exact inner_dualDirection_apply_direction_eq_zero h le_rfl (le_of_lt hj') (by omega)
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- If BCG runs without breakdown through step $m$, then $A p_m$ is orthogonal to the shadow Krylov
space: $\langle u, A p_m \rangle = 0$ for every $u \in \mathcal{K}_m(B, r^*_0)$.

This is the $A$-biconjugacy of Proposition 7.2 of [saad2003iterative] against the subspace
rather than against the individual shadow directions. -/
theorem inner_apply_direction_eq_zero_of_mem_subspace {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m)
    {u : E} (hu : u ∈ Krylov.subspace B rs₀ m) :
    inner 𝕜 u (A (direction A B b x₀ rs₀ m)) = 0 :=
  inner_apply_direction_eq_zero_of_mem_span h (subspace_le_span_dualDirection h hu)

/-- **BCG is a Petrov–Galerkin method.** If BCG runs without breakdown through step $m$, then the
iterate $x_m$ is a Petrov–Galerkin iterate with $K = \mathcal{K}_m(A, r_0)$ and
$L = \mathcal{K}_m(B, r^*_0)$, where $r_0 = b - A x_0$:
$$x_m - x_0 \in \mathcal{K}_m(A, r_0), \qquad b - A x_m \perp \mathcal{K}_m(B, r^*_0).$$
This follows from Proposition 7.2 of [saad2003iterative].

The specification is `IsPetrovGalerkin`, and $B$ plays the role of $A^H$. -/
theorem isPetrovGalerkin {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    IsPetrovGalerkin A b x₀ (Krylov.subspace A (b - A x₀) m) (Krylov.subspace B rs₀ m)
      (iterate A B b x₀ rs₀ m).x where
  mem := iterate_x_sub_mem A B b x₀ rs₀ m
  orth := (Submodule.mem_orthogonal _ _).2 fun u hu => by
    rw [← residual_eq]
    exact inner_eq_zero_of_mem_span h (subspace_le_span_dualResidual h hu)

end Biorthogonality

end BCG

/-!
### The quasi-minimal residual method

QMR minimizes the *quasi-residual*, the coordinate vector of the residual in the basis of the
two-sided Lanczos vectors, rather than the residual itself. Because this basis is not orthonormal,
the two differ, and the price is the conditioning of $V_{m+1}$ ([saad2003iterative], §7.3).
-/

open BiLanczos

namespace QMR

/-- The **quasi-residual** of the two-sided Lanczos relation, equation (7.13) of
[saad2003iterative]: for $\beta \in \mathbb{K}$ and $y \in \mathbb{K}^m$, the vector
$$\beta e_1 - \bar T_m y \in \mathbb{K}^{m+1},$$
with the Euclidean norm. Here $\bar T_m$ is the $(m+1) \times m$ matrix
$(T_{ij})_{i \le m, \, j < m}$ of `BiLanczos.coeff`.

When $b - A x_0 = \beta v_0$, it is the coordinate vector, in the basis $v_0, \dots, v_m$, of
the residual of $x_0 + \sum_{j<m} y_j v_j$. In Lean, the matrix is `Krylov.hessenbergOf`
applied to `BiLanczos.coeff`, and the first term is `Krylov.firstVec`. -/
noncomputable def quasiResidual (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    EuclideanSpace 𝕜 (Fin (m + 1)) :=
  WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
    (Krylov.hessenbergOf (BiLanczos.coeff A B v₁ w₁) m).mulVec y)

/-- The quasi-residual, unfolded: it is the vector $\beta e_1 - \bar T_m y$, read in the Euclidean
space $\mathbb{K}^{m+1}$. -/
theorem quasiResidual_def (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    quasiResidual A B v₁ w₁ β m y = WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
      (Krylov.hessenbergOf (BiLanczos.coeff A B v₁ w₁) m).mulVec y) := rfl

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The **quasi-minimal residual specification** of equations (7.15)–(7.17) of [saad2003iterative]:
$x$ is a QMR iterate at step $m$ if
$$x = x_0 + \sum_{j=0}^{m-1} y_j v_j$$
for a vector $y \in \mathbb{K}^m$ that minimizes the norm of the quasi-residual
$\|\beta e_1 - \bar T_m y\|$ over $\mathbb{K}^m$.

The intended use has $b - A x_0 = \beta v_0$. Replacing the true residual
$\|V_{m+1} (\beta e_1 - \bar T_m y)\|$ by the norm of its coordinate vector turns the step into
a small least-squares problem; the price is the factor $\kappa_2(V_{m+1})$ of
`QMR.norm_residual_le`. -/
def IsQuasiMinResidual (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (x₀ : E) (m : ℕ) (x : E) : Prop :=
  ∃ y : Fin m → 𝕜, x = x₀ + ∑ j, y j • BiLanczos.vec A B v₁ w₁ (j : ℕ) ∧
    IsMinOn (fun z => ‖quasiResidual A B v₁ w₁ β m z‖) Set.univ y

/-- **Proposition 7.3** of [saad2003iterative]: the residual is bounded by the quasi-residual.
Suppose that the two-sided Lanczos process has no serious breakdown, that
$b - A x_0 = \beta v_0$, and that $C \in \mathbb{R}$ satisfies
$$\Big\| \sum_{i=0}^{m} z_i v_i \Big\| \le C \|z\| \quad \text{for all } z \in
  \mathbb{K}^{m+1}.$$
Then for every $y \in \mathbb{K}^m$,
$$\Big\| b - A \Big( x_0 + \sum_{j=0}^{m-1} y_j v_j \Big) \Big\| \le C \, \|\beta e_1 - \bar T_m
  y\|.$$

The bound $C$ on the coordinate map is a hypothesis because an abstract inner product space has
no matrix $V_{m+1}$ to take a norm of. For $E = \mathbb{K}^n$, the best $C$ is the largest
singular value of $V_{m+1}$, that is, $\|V_{m+1}\|_2$. -/
theorem norm_residual_le_norm_quasiResidual (h : NoSeriousBreakdown A B v₁ w₁) {b x₀ : E}
    {β : 𝕜} (hr : b - A x₀ = β • v₁) {m : ℕ} {C : ℝ}
    (hC : ∀ z : Fin (m + 1) → 𝕜, ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖ ≤
      C * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • vec A B v₁ w₁ (j : ℕ))‖ ≤
      C * ‖quasiResidual A B v₁ w₁ β m y‖ := by
  rw [(hessenbergRelation h).residual_eq hr m y, quasiResidual_def]
  exact hC _

/-- The minimal quasi-residual in Givens form (Proposition 7.3 of [saad2003iterative]). Reduce
$\bar T_m$ to upper triangular form by the progressive Givens rotations, and suppose that no
rotation degenerates: $\rho_k \neq 0$ for every $k < m$. If $y$ minimizes
$\|\beta e_1 - \bar T_m y\|$ over $\mathbb{K}^m$, then
$$\|\beta e_1 - \bar T_m y\| = |\gamma_m|,$$
where $\gamma_m$ is the last entry of the rotated right-hand side.

The quantities $\rho_k$ and $\gamma_m$ are `Krylov.givensRho` and `Krylov.gamma` for
`BiLanczos.coeff`. By `Krylov.norm_gamma_eq_prod`,
$|\gamma_m| = |s_0| \cdots |s_{m-1}| \, |\beta|$, with the sines $s_k$ of the rotations. -/
theorem norm_quasiResidual_eq_norm_gamma {m : ℕ} {β : 𝕜}
    (hρ : ∀ k < m, givensRho (BiLanczos.coeff A B v₁ w₁) k ≠ 0) {y : Fin m → 𝕜}
    (hy : IsMinOn (fun z => ‖quasiResidual A B v₁ w₁ β m z‖) Set.univ y) :
    ‖quasiResidual A B v₁ w₁ β m y‖ = ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ := by
  have hh : Matrix.IsUpperHessenberg (n := ℕ) (BiLanczos.coeff A B v₁ w₁) :=
    Matrix.isUpperHessenberg_iff_nat.2 fun _ _ hij => BiLanczos.coeff_eq_zero_of_lt A B v₁ w₁ hij
  have hsplit : ∀ z : Fin m → 𝕜, ‖quasiResidual A B v₁ w₁ β m z‖ ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin m => gvec (BiLanczos.coeff A B v₁ w₁) β (i : ℕ)) -
          (hessenbergSqOf (rotated (BiLanczos.coeff A B v₁ w₁) m) m).mulVec z) :
        EuclideanSpace 𝕜 (Fin m))‖ ^ 2 + ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ ^ 2 := by
    intro z
    rw [quasiResidual_def]
    exact norm_sq_firstVec_sub_mulVec_eq _ hh hρ β z
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin m → 𝕜,
      (hessenbergSqOf (rotated (BiLanczos.coeff A B v₁ w₁) m) m).mulVec z₀ =
        fun i : Fin m => gvec (BiLanczos.coeff A B v₁ w₁) β (i : ℕ) := by
    exact ⟨_, Matrix.mulVec_nonsing_inv_mulVec
      (isUnit_hessenbergSqOf_rotated_self (BiLanczos.coeff A B v₁ w₁) hh hρ) _⟩
  have h0 : ‖quasiResidual A B v₁ w₁ β m z₀‖ = ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ := by
    have hsq := hsplit z₀
    rw [hz₀, sub_self] at hsq
    simp only [WithLp.toLp_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add] at hsq
    have h1 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
  refine le_antisymm (h0 ▸ isMinOn_iff.1 hy z₀ (Set.mem_univ z₀)) ?_
  have hsq : ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ ^ 2 ≤
      ‖quasiResidual A B v₁ w₁ β m y‖ ^ 2 := by
    rw [hsplit y]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- **Theorem 7.4** of [saad2003iterative]: the QMR residual is within the factor
$\kappa_2(V_{m+1})$ of the GMRES residual. Suppose that the two-sided Lanczos process has no
serious breakdown and runs without breakdown through step $m$, and that $b - A x_0 = \beta v_0$.
Let $0 < c$ and $0 \le C$ satisfy
$$c \|z\| \le \Big\| \sum_{i=0}^{m} z_i v_i \Big\| \le C \|z\| \quad \text{for all } z \in
  \mathbb{K}^{m+1}.$$
If $x$ is a QMR iterate at step $m$ and $x_G$ is a GMRES iterate at step $m$, that is, $x_G$
minimizes $\|b - A x\|$ over $x_0 + \mathcal{K}_m(A, b - A x_0)$, then
$$\|b - A x\| \le \frac{C}{c} \, \|b - A x_G\|.$$

The numbers $c$ and $C$ stand for the extreme singular values of $V_{m+1}$, so $C / c$ stands
for $\kappa_2(V_{m+1})$. The GMRES iterate lies in the same affine space, so its coordinate
vector competes in the minimization of the quasi-residual: $c$ converts its quasi-residual back
into a true residual, and $C$ converts the QMR quasi-residual into a true residual. The GMRES
specification is `Krylov.IsMinResidualIterate`. -/
theorem norm_residual_le (hs : NoSeriousBreakdown A B v₁ w₁) {m : ℕ}
    (hnb : NoBreakdown A B v₁ w₁ m) {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v₁)
    {c C : ℝ} (hc0 : 0 < c) (hC0 : 0 ≤ C)
    (hc : ∀ z : Fin (m + 1) → 𝕜, c * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤
      ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖)
    (hC : ∀ z : Fin (m + 1) → 𝕜, ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖ ≤
      C * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    {x xG : E} (hx : IsQuasiMinResidual A B v₁ w₁ β x₀ m x)
    (hG : Krylov.IsMinResidualIterate A b x₀ m xG) :
    ‖b - A x‖ ≤ C / c * ‖b - A xG‖ := by
  obtain ⟨y, rfl, hy⟩ := hx
  have hmem0 : xG - x₀ ∈ Krylov.subspace A v₁ m := by
    have hmem := hG.mem
    rw [hr] at hmem
    exact Krylov.subspace_smul A v₁ β m hmem
  have hmem : xG - x₀ ∈ Submodule.span 𝕜 (Set.range fun j : Fin m => vec A B v₁ w₁ (j : ℕ)) := by
    rw [Set.range_comp', Fin.range_val, span_vec hnb]
    exact hmem0
  obtain ⟨zG, hzG⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem
  have hxGeq : xG = x₀ + ∑ j, zG j • vec A B v₁ w₁ (j : ℕ) := by rw [hzG]; abel
  have hlow : c * ‖quasiResidual A B v₁ w₁ β m zG‖ ≤ ‖b - A xG‖ := by
    rw [hxGeq, (hessenbergRelation hs).residual_eq hr m zG, quasiResidual_def]
    exact hc _
  have hmin : ‖quasiResidual A B v₁ w₁ β m y‖ ≤ ‖quasiResidual A B v₁ w₁ β m zG‖ :=
    isMinOn_iff.1 hy zG (Set.mem_univ zG)
  have h1 : ‖quasiResidual A B v₁ w₁ β m zG‖ ≤ ‖b - A xG‖ / c := by
    rw [le_div_iff₀ hc0]
    linarith
  calc ‖b - A (x₀ + ∑ j, y j • vec A B v₁ w₁ (j : ℕ))‖
      ≤ C * ‖quasiResidual A B v₁ w₁ β m y‖ :=
        norm_residual_le_norm_quasiResidual hs hr hC y
    _ ≤ C * (‖b - A xG‖ / c) := mul_le_mul_of_nonneg_left (hmin.trans h1) hC0
    _ = C / c * ‖b - A xG‖ := by ring

end QMR
