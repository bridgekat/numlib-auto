/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.BiLanczos
import Numlib.Krylov.CG
import Numlib.Projection.OneDimensional

/-!
# Transpose-free variants of the biconjugate gradient method

This file defines the conjugate gradient squared method (CGS, due to Sonneveld) and BiCGSTAB (due to
van der Vorst), and proves the polynomial identities that explain them. Let $A$ be a linear operator
on an inner product space $E$, let $B$ be its adjoint, and let $r_0 = b - A x_0$ and a shadow
residual $r^*_0$ be given. A run of the biconjugate gradient method (BCG) has residuals
$r_j = \varphi_j(A) r_0$ and directions $p_j = \pi_j(A) r_0$ for polynomials $\varphi_j$ and $\pi_j$
of degree at most $j$. CGS computes $\varphi_j(A)^2 r_0$ and $\pi_j(A)^2 r_0$, and BiCGSTAB computes
$\psi_j(A) \varphi_j(A) r_0$ and $\psi_j(A) \pi_j(A) r_0$ with
$\psi_{j+1} = (1 - \omega_j X) \psi_j$, where each $\omega_j$ is a one-dimensional minimal-residual
step. Both methods apply $A$ only, and never $B$. The presentation follows [saad2003iterative],
§7.4, Algorithms 7.6 and 7.7 and equations (7.32) to (7.54), and [golub2013matrix], §11.4.5 and
Figure 11.4.1, whose recurrences are the same line by line.

## Main definitions

* `BCG.residualPoly`, `BCG.directionPoly`: the polynomials $\varphi_j$ and $\pi_j$ of a BCG run,
  with $\varphi_0 = \pi_0 = 1$, $\varphi_{j+1} = \varphi_j - \alpha_j X \pi_j$ and
  $\pi_{j+1} = \varphi_{j+1} + \beta_j \pi_j$ for the coefficients `BCG.alpha` and `BCG.beta` of the
  run.
* `CGS.iterate`: Algorithm 7.6 of [saad2003iterative], with the coefficients `CGS.alpha`, `CGS.beta`
  and the auxiliary vector `CGS.q` read off the states.
* `BiCGSTAB.iterate`: Algorithm 7.7 of [saad2003iterative], with `BiCGSTAB.alpha`, `BiCGSTAB.s`,
  `BiCGSTAB.omega` and `BiCGSTAB.beta` read off the states.
* `BiCGSTAB.stabPoly`: the stabilizing polynomial $\psi_j$, with $\psi_0 = 1$ and
  $\psi_{j+1} = (1 - \omega_j X) \psi_j$.

## Main results

* `BCG.residual_eq_aeval`: the four BCG sequences are $\varphi_j(A) r_0$, $\pi_j(A) r_0$,
  $\bar\varphi_j(B) r^*_0$ and $\bar\pi_j(B) r^*_0$. Every scalar of the transpose-free methods then
  follows by moving a polynomial across the inner product (`BiLanczos.inner_aeval_map_eq`).
* `CGS.residual_eq_aeval_sq`: the CGS vectors are $\varphi_j^2(A) r_0$, $\pi_j^2(A) r_0$,
  $\varphi_j(A) \pi_j(A) r_0$ and $\varphi_{j+1}(A) \pi_j(A) r_0$, and the CGS coefficients are the
  BCG coefficients, with no hypothesis against breakdown.
* `BiCGSTAB.residual_eq`: if BCG does not break down and no $\omega_i$ vanishes, then
  $r_j = \psi_j(A) \varphi_j(A) r_0$ and $p_j = \psi_j(A) \pi_j(A) r_0$.
* `BiCGSTAB.alpha_eq`, `BiCGSTAB.beta_eq`: under the same hypotheses, the BiCGSTAB coefficients are
  the BCG coefficients ([saad2003iterative], (7.53) and (7.54)).
* `BiCGSTAB.iterate_succ_x_eq_minResStep`: the second half of a BiCGSTAB step is the one-dimensional
  minimal-residual step along $s_j$ ([saad2003iterative], (7.55)).
* `CGS.r_eq_sub_apply_x`, `BiCGSTAB.r_eq_sub_apply_x`: the residuals that the methods update are the
  true residuals $b - A x_j$.

## Implementation notes

* As for `BCG` in `Numlib.Krylov.BiLanczos`, the adjoint of $A$ is a second operator $B$ with
  $\langle Ax, y \rangle = \langle x, By \rangle$, taken as data (`LinearMap.IsAdjointPair`,
  `LinearMap.isAdjointPair_inner_iff'`).
* Each method is a structure `State`, a function `step` and its iterate `iterate`, as in the other
  Krylov modules. The coefficients are defined from the states.
* Indices start at $0$: `CGS.iterate A b x₀ rs₀ j` is the state after $j$ steps, and
  `BCG.residualPoly A B b x₀ rs₀ j` is $\varphi_j$.
* The inner product is conjugate-linear in its first argument, as in Mathlib. A quotient with
  denominator $0$ is $0$.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Module.End (aeval_mul_apply aeval_apply_apply aeval_apply_add aeval_apply_sub
  aeval_apply_C_mul aeval_apply_X_mul aeval_sub_C_mul_X_mul aeval_add_C_mul)

open BiLanczos (inner_aeval_map_aeval)

/-! ### The BCG residual and direction polynomials -/

namespace BCG

/-- The pair $(\varphi_j, \pi_j)$ of BCG polynomials, defined together because each recurrence uses
the other. -/
private noncomputable def polyPair (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 => (1, 1)
  | j + 1 =>
      let φ : 𝕜[X] :=
        (polyPair A B b x₀ rs₀ j).1 - C (alpha A B b x₀ rs₀ j) * (X * (polyPair A B b x₀ rs₀ j).2)
      (φ, φ + C (beta A B b x₀ rs₀ j) * (polyPair A B b x₀ rs₀ j).2)

variable (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The **BCG residual polynomial** $\varphi_j$ ([saad2003iterative], (7.32) and (7.35);
[golub2013matrix], (11.4.14)). Let $\alpha_j$ and $\beta_j$ be the coefficients of the BCG run
of $A$ and $B$ from $x_0$ with shadow residual $r^*_0$. Then $\varphi_0 = 1$, $\pi_0 = 1$ and
$$\varphi_{j+1} = \varphi_j - \alpha_j X \pi_j, \qquad \pi_{j+1} = \varphi_{j+1} + \beta_j
  \pi_j.$$

The polynomial $\varphi_j$ has degree at most $j$ and satisfies $\varphi_j(0) = 1$, and
$r_j = \varphi_j(A) r_0$ (`BCG.residual_eq_aeval`). -/
noncomputable def residualPoly (j : ℕ) : 𝕜[X] := (polyPair A B b x₀ rs₀ j).1

/-- The **BCG direction polynomial** $\pi_j$ ([saad2003iterative], (7.33) and (7.36);
[golub2013matrix], (11.4.14)): $\pi_0 = 1$ and $\pi_{j+1} = \varphi_{j+1} + \beta_j \pi_j$, with
$\varphi_j$ and $\beta_j$ as in `BCG.residualPoly`.

Then $p_j = \pi_j(A) r_0$ (`BCG.residual_eq_aeval`). In general $\pi_j(0) \neq 1$. -/
noncomputable def directionPoly (j : ℕ) : 𝕜[X] := (polyPair A B b x₀ rs₀ j).2

/-- The residual polynomial of step $0$ is $\varphi_0 = 1$. -/
@[simp] theorem residualPoly_zero : residualPoly A B b x₀ rs₀ 0 = 1 := rfl

/-- The direction polynomial of step $0$ is $\pi_0 = 1$. -/
@[simp] theorem directionPoly_zero : directionPoly A B b x₀ rs₀ 0 = 1 := rfl

/-- The recurrence $\varphi_{j+1} = \varphi_j - \alpha_j X \pi_j$. -/
theorem residualPoly_succ (j : ℕ) : residualPoly A B b x₀ rs₀ (j + 1) =
    residualPoly A B b x₀ rs₀ j
      - C (alpha A B b x₀ rs₀ j) * (X * directionPoly A B b x₀ rs₀ j) := rfl

/-- The recurrence $\pi_{j+1} = \varphi_{j+1} + \beta_j \pi_j$. -/
theorem directionPoly_succ (j : ℕ) : directionPoly A B b x₀ rs₀ (j + 1) =
    residualPoly A B b x₀ rs₀ (j + 1)
      + C (beta A B b x₀ rs₀ j) * directionPoly A B b x₀ rs₀ j := rfl

/-- The residual polynomials are consistent: $\varphi_j(0) = 1$ for every $j$. -/
@[simp] theorem residualPoly_eval_zero (j : ℕ) : (residualPoly A B b x₀ rs₀ j).eval 0 = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [residualPoly_succ]; simp [ih]

private theorem natDegree_polyPair_le (j : ℕ) :
    (residualPoly A B b x₀ rs₀ j).natDegree ≤ j ∧ (directionPoly A B b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hφ : (residualPoly A B b x₀ rs₀ (j + 1)).natDegree ≤ j + 1 := by
      rw [residualPoly_succ]
      refine (natDegree_sub_le _ _).trans (max_le (ih.1.trans (Nat.le_succ j)) ?_)
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      simp only [natDegree_X]
      omega
    refine ⟨hφ, ?_⟩
    rw [directionPoly_succ]
    exact (natDegree_add_le _ _).trans
      (max_le hφ ((natDegree_C_mul_le _ _).trans (ih.2.trans (Nat.le_succ j))))

/-- The residual polynomial $\varphi_j$ has degree at most $j$. -/
theorem residualPoly_natDegree_le (j : ℕ) : (residualPoly A B b x₀ rs₀ j).natDegree ≤ j :=
  (natDegree_polyPair_le A B b x₀ rs₀ j).1

/-- The direction polynomial $\pi_j$ has degree at most $j$. -/
theorem directionPoly_natDegree_le (j : ℕ) : (directionPoly A B b x₀ rs₀ j).natDegree ≤ j :=
  (natDegree_polyPair_le A B b x₀ rs₀ j).2

/-- The polynomials $\varphi_j$ and $\pi_j$ have the same coefficient of $X^j$. The reason is that
$\pi_{j+1}$ differs from $\varphi_{j+1}$ by a multiple of $\pi_j$, which has lower degree. -/
theorem directionPoly_coeff_self (j : ℕ) :
    (directionPoly A B b x₀ rs₀ j).coeff j = (residualPoly A B b x₀ rs₀ j).coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [directionPoly_succ, coeff_add, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (directionPoly_natDegree_le A B b x₀ rs₀ j) (Nat.lt_succ_self j)),
      mul_zero, add_zero]

/-- Let $\gamma^{(j)}$ be the coefficient of $X^j$ in $\varphi_j$. Then
$\gamma^{(j+1)} = -\alpha_j \gamma^{(j)}$. -/
theorem residualPoly_coeff_succ (j : ℕ) :
    (residualPoly A B b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -alpha A B b x₀ rs₀ j * (residualPoly A B b x₀ rs₀ j).coeff j := by
  rw [residualPoly_succ, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (residualPoly_natDegree_le A B b x₀ rs₀ j) (Nat.lt_succ_self j)),
    ← mul_assoc, mul_comm (C (alpha A B b x₀ rs₀ j)) X, mul_assoc, coeff_X_mul, coeff_C_mul,
    directionPoly_coeff_self]
  ring

/-- **The BCG sequences are polynomials in the operators** ([saad2003iterative], (7.32) and (7.33);
[golub2013matrix], (11.4.14)). Let $r_0 = b - A x_0$. For every $j$,
$$r_j = \varphi_j(A) r_0, \qquad p_j = \pi_j(A) r_0, \qquad r^*_j = \bar\varphi_j(B) r^*_0,
  \qquad p^*_j = \bar\pi_j(B) r^*_0,$$
where $\bar\varphi_j$ and $\bar\pi_j$ are the polynomials with the complex conjugate
coefficients.

No hypothesis is needed; in particular $B$ need not be the adjoint of $A$. The conjugate
polynomials are `Polynomial.map (starRingEnd 𝕜)` of $\varphi_j$ and $\pi_j$. -/
theorem residual_eq_aeval (j : ℕ) :
    residual A B b x₀ rs₀ j = aeval A (residualPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      direction A B b x₀ rs₀ j = aeval A (directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      dualResidual A B b x₀ rs₀ j =
        aeval B ((residualPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ ∧
      dualDirection A B b x₀ rs₀ j =
        aeval B ((directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hrs, hps⟩ := ih
    have hrmap : (residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
        = (residualPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)
          - C (starRingEnd 𝕜 (alpha A B b x₀ rs₀ j))
            * (X * (directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) := by
      rw [residualPoly_succ]
      simp [Polynomial.map_sub, Polynomial.map_mul]
    have hpmap : (directionPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
        = (residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
          + C (starRingEnd 𝕜 (beta A B b x₀ rs₀ j))
            * (directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜) := by
      rw [directionPoly_succ]
      simp [Polynomial.map_add, Polynomial.map_mul]
    have h1 : residual A B b x₀ rs₀ (j + 1)
        = aeval A (residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      rw [residual_succ, residualPoly_succ, aeval_sub_C_mul_X_mul, hr, hp]
    have h3 : dualResidual A B b x₀ rs₀ (j + 1)
        = aeval B ((residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)) rs₀ := by
      rw [dualResidual_succ, hrmap, aeval_sub_C_mul_X_mul, hrs, hps]
    exact ⟨h1, by rw [direction_succ, directionPoly_succ, aeval_add_C_mul, h1, hp], h3,
      by rw [dualDirection_succ, hpmap, aeval_add_C_mul, h3, hps]⟩

/-- **BCG with $B = A$ and $r^*_0 = r_0$ is CG** ([golub2013matrix], §11.4.5: "BiCG collapses to CG
if $A$ is symmetric positive definite and $\tilde r_0 = r_0$"). Let $F$ be a real inner product
space, $T$ a linear operator on $F$, and $b, x_0 \in F$. Then for every $k$, the biconjugate
gradient iteration with second operator $T$ and shadow residual $r^*_0 = r_0 = b - T x_0$ is the
conjugate gradient iteration: the state after $k$ steps is $(x_k, r_k, r_k, p_k, p_k)$ for the
iterate $x_k$, residual $r_k$ and direction $p_k$ of `CG.iterate`.

No hypothesis on $T$ is needed for the identity of the two recurrences: over $\mathbb{R}$ the
BCG step length $\langle r, r \rangle / \langle p, Tp \rangle$ is the CG step length
$\langle r, r \rangle / \langle Tp, p \rangle$. -/
theorem iterate_self_eq_cg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : F →ₗ[ℝ] F) (b x₀ : F) (k : ℕ) :
    iterate T T b x₀ (b - T x₀) k =
      ⟨(CG.iterate T b x₀ k).x, (CG.iterate T b x₀ k).r, (CG.iterate T b x₀ k).r,
        (CG.iterate T b x₀ k).p, (CG.iterate T b x₀ k).p⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ, ih, CG.iterate_succ]
    set c := CG.iterate T b x₀ k
    have hα : stepAlpha T ⟨c.x, c.r, c.r, c.p, c.p⟩ = CG.alpha T c := by
      simp only [stepAlpha, CG.alpha]
      rw [real_inner_comm (T c.p) c.p]
    simp only [step, CG.step, hα, conj_trivial]

end BCG

/-! ### Conjugate gradient squared -/

namespace CGS

/-- The state $(x_j, r_j, u_j, p_j)$ of the conjugate gradient squared method. The auxiliary vector
$q_j$ is computed from it by `CGS.q`. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate $x_j$. -/
  x : E
  /-- The residual $r_j$, which is $\varphi_j(A)^2 r_0$. -/
  r : E
  /-- The auxiliary vector $u_j = r_j + \beta_{j-1} q_{j-1}$, which is $\varphi_j(A) \pi_j(A) r_0$.
  -/
  u : E
  /-- The direction $p_j$, which is $\pi_j(A)^2 r_0$. -/
  p : E

/-- One step of the **conjugate gradient squared** method ([saad2003iterative], Algorithm 7.6, lines
4 to 10; [golub2013matrix], Figure 11.4.1). From the state $(x, r, u, p)$ and the shadow
residual $r^*_0$, it computes
$$\alpha = \frac{\langle r^*_0, r \rangle}{\langle r^*_0, Ap \rangle}, \quad q = u - \alpha A p,
  \quad x' = x + \alpha (u + q), \quad r' = r - \alpha A (u + q),$$
$$\beta = \frac{\langle r^*_0, r' \rangle}{\langle r^*_0, r \rangle}, \quad u' = r' + \beta q,
  \quad p' = u' + \beta (q + \beta p),$$
and returns $(x', r', u', p')$. -/
noncomputable def step (A : E →ₗ[𝕜] E) (rs₀ : E) (s : State E) : State E :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (A s.p)
  let q : E := s.u - α • A s.p
  let r : E := s.r - α • A (s.u + q)
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r
  let u : E := r + β • q
  { x := s.x + α • (s.u + q), r := r, u := u, p := u + β • (q + β • s.p) }

/-- The **conjugate gradient squared** method ([saad2003iterative], Algorithm 7.6;
[golub2013matrix], Figure 11.4.1). For $b, x_0 \in E$, a shadow residual $r^*_0 \in E$ and
$k \in \mathbb{N}$, it is the state after $k$ applications of `CGS.step` to the initial state
with $x = x_0$ and $r = u = p = b - A x_0$.

Only $A$ is applied, and never its adjoint. The shadow residual $r^*_0$ is arbitrary. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A rs₀)^[k] { x := x₀, r := b - A x₀, u := b - A x₀, p := b - A x₀ }

variable (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The CGS step length $\alpha_j = \langle r^*_0, r_j \rangle / \langle r^*_0, A p_j \rangle$. -/
noncomputable def alpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r / inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)

/-- The CGS coefficient $\beta_j = \langle r^*_0, r_{j+1} \rangle / \langle r^*_0, r_j \rangle$. -/
noncomputable def beta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r

/-- The auxiliary CGS vector $q_j = u_j - \alpha_j A p_j$. -/
noncomputable def q (j : ℕ) : E :=
  (iterate A b x₀ rs₀ j).u - alpha A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p

/-- The initial CGS state is $x = x_0$ and $r = u = p = b - A x_0$. -/
@[simp] theorem iterate_zero :
    iterate A b x₀ rs₀ 0 = { x := x₀, r := b - A x₀, u := b - A x₀, p := b - A x₀ } := rfl

/-- The state after $k + 1$ steps is `CGS.step` applied to the state after $k$ steps. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ rs₀ (k + 1) = step A rs₀ (iterate A b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The recurrence $x_{j+1} = x_j + \alpha_j (u_j + q_j)$. -/
theorem iterate_succ_x (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).x =
    (iterate A b x₀ rs₀ j).x
      + alpha A b x₀ rs₀ j • ((iterate A b x₀ rs₀ j).u + q A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- The recurrence $r_{j+1} = r_j - \alpha_j A (u_j + q_j)$. -/
theorem iterate_succ_r (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).r =
    (iterate A b x₀ rs₀ j).r
      - alpha A b x₀ rs₀ j • A ((iterate A b x₀ rs₀ j).u + q A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- The recurrence $u_{j+1} = r_{j+1} + \beta_j q_j$. -/
theorem iterate_succ_u (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).u =
    (iterate A b x₀ rs₀ (j + 1)).r + beta A b x₀ rs₀ j • q A b x₀ rs₀ j := by
  simp only [beta, iterate_succ]; rfl

/-- The recurrence $p_{j+1} = u_{j+1} + \beta_j (q_j + \beta_j p_j)$. -/
theorem iterate_succ_p (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).p =
    (iterate A b x₀ rs₀ (j + 1)).u
      + beta A b x₀ rs₀ j • (q A b x₀ rs₀ j + beta A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p) := by
  simp only [beta, iterate_succ]; rfl

/-- The CGS residual is the true residual of the CGS iterate: $r_j = b - A x_j$ for every $j$. -/
theorem r_eq_sub_apply_x (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = b - A (iterate A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [iterate_succ_r, iterate_succ_x, ih, map_add, map_smul]
    abel

variable {A b x₀ rs₀}

section Polynomial

variable {B : E →ₗ[𝕜] E} (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
include hB

/-- If $r_j = \varphi_j(A)^2 r_0$, then the numerator of the BCG coefficient $\alpha_j$ is $\langle
r^*_j, r_j^{\mathrm{BCG}} \rangle = \langle r^*_0, r_j \rangle$. -/
private theorem inner_dualResidual_residual_eq {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    inner 𝕜 (BCG.dualResidual A B b x₀ rs₀ j) (BCG.residual A B b x₀ rs₀ j)
      = inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r := by
  obtain ⟨hbr, -, hbrs, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbr, hbrs, inner_aeval_map_aeval hB, hr, ← sq]

/-- If $p_j = \pi_j(A)^2 r_0$, then the denominator of the BCG coefficient $\alpha_j$ is $\langle
p^*_j, A p_j^{\mathrm{BCG}} \rangle = \langle r^*_0, A p_j \rangle$. -/
private theorem inner_dualDirection_apply_direction_eq {j : ℕ}
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    inner 𝕜 (BCG.dualDirection A B b x₀ rs₀ j) (A (BCG.direction A B b x₀ rs₀ j))
      = inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p) := by
  obtain ⟨-, hbp, -, hbps⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  have hpoly : BCG.directionPoly A B b x₀ rs₀ j * (X * BCG.directionPoly A B b x₀ rs₀ j)
      = X * BCG.directionPoly A B b x₀ rs₀ j ^ 2 := by ring
  rw [hbp, hbps, ← aeval_apply_X_mul, inner_aeval_map_aeval hB, hpoly, hp, aeval_apply_X_mul]

private theorem alpha_eq_aux {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  rw [alpha, BCG.alpha, inner_dualResidual_residual_eq hB hr,
    inner_dualDirection_apply_direction_eq hB hp]

private theorem beta_eq_aux {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hr' : (iterate A b x₀ rs₀ (j + 1)).r
      = aeval A (BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2) (b - A x₀)) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  rw [beta, BCG.beta, inner_dualResidual_residual_eq hB hr, inner_dualResidual_residual_eq hB hr']

omit hB in
private theorem q_eq_aux {j : ℕ}
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hu : (iterate A b x₀ rs₀ j).u = aeval A
      (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀))
    (hα : alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j) :
    q A b x₀ rs₀ j = aeval A
      (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j
      = BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
        - C (BCG.alpha A B b x₀ rs₀ j) * (X * BCG.directionPoly A B b x₀ rs₀ j ^ 2) := by
    rw [BCG.residualPoly_succ]; ring
  rw [q, hu, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- The CGS vectors $r_j$, $p_j$ and $u_j$ are $\varphi_j(A)^2 r_0$, $\pi_j(A)^2 r_0$ and
$\varphi_j(A) \pi_j(A) r_0$. This is the induction behind `CGS.residual_eq_aeval_sq`. -/
private theorem vec_eq (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hu⟩ := ih
    have hα := alpha_eq_aux hB hr hp
    have hq := q_eq_aux hp hu hα
    have hr' : (iterate A b x₀ rs₀ (j + 1)).r
        = aeval A (BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2) (b - A x₀) := by
      have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2
          = BCG.residualPoly A B b x₀ rs₀ j ^ 2
            - C (BCG.alpha A B b x₀ rs₀ j)
              * (X * (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
                  + BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j)) := by
        rw [BCG.residualPoly_succ]; ring
      rw [iterate_succ_r, hu, hq, hr, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul,
        aeval_apply_X_mul, aeval_apply_add]
    have hβ := beta_eq_aux hB hr hr'
    have hu' : (iterate A b x₀ rs₀ (j + 1)).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1))
          (b - A x₀) := by
      have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
          = BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2
            + C (BCG.beta A B b x₀ rs₀ j)
              * (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) := by
        rw [BCG.directionPoly_succ A B b x₀ rs₀ j]; ring
      rw [iterate_succ_u, hq, hr', hβ, hpoly, aeval_apply_add, aeval_apply_C_mul]
    refine ⟨hr', ?_, hu'⟩
    have hpoly : BCG.directionPoly A B b x₀ rs₀ (j + 1) ^ 2
        = BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
          + C (BCG.beta A B b x₀ rs₀ j)
            * (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j
              + C (BCG.beta A B b x₀ rs₀ j) * BCG.directionPoly A B b x₀ rs₀ j ^ 2) := by
      rw [BCG.directionPoly_succ A B b x₀ rs₀ j]; ring
    rw [iterate_succ_p, hu', hq, hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul,
      aeval_apply_add, aeval_apply_C_mul]

/-- **CGS computes the squared BCG polynomials** ([saad2003iterative], (7.40) to (7.45), due to
Sonneveld; [golub2013matrix], §11.4.5). Let $B$ be the adjoint of $A$, let $r_0 = b - A x_0$,
and let $\varphi_j$ and $\pi_j$ be the polynomials of the BCG run with the same $x_0$ and
$r^*_0$. Then for every $j$,
$$r_j = \varphi_j(A)^2 r_0, \quad p_j = \pi_j(A)^2 r_0, \quad u_j = \varphi_j(A) \pi_j(A) r_0,
  \quad q_j = \varphi_{j+1}(A) \pi_j(A) r_0,$$
and the CGS coefficients $\alpha_j$ and $\beta_j$ are the BCG coefficients.

No hypothesis against breakdown is needed: the coefficients agree also where both are $0/0$,
which is $0$ in Lean. -/
theorem residual_eq_aeval_sq (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      q A b x₀ rs₀ j = aeval A
        (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j ∧
      beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hr, hp, hu⟩ := vec_eq hB j
  have hα := alpha_eq_aux hB hr hp
  exact ⟨hr, hp, hu, q_eq_aux hp hu hα, hα, beta_eq_aux hB hr (vec_eq hB (j + 1)).1⟩

end Polynomial

end CGS

/-! ### BiCGSTAB -/

namespace BiCGSTAB

/-- The state $(x_j, r_j, p_j)$ of BiCGSTAB. The half-step residual $s_j$ is computed from it by
`BiCGSTAB.s`. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate $x_j$. -/
  x : E
  /-- The residual $r_j$, which is $\psi_j(A) \varphi_j(A) r_0$. -/
  r : E
  /-- The direction $p_j$, which is $\psi_j(A) \pi_j(A) r_0$. -/
  p : E

/-- One step of **BiCGSTAB** ([saad2003iterative], Algorithm 7.7, lines 4 to 10; [golub2013matrix],
Figure 11.4.1). From the state $(x, r, p)$ and the shadow residual $r^*_0$, it computes
$$\alpha = \frac{\langle r^*_0, r \rangle}{\langle r^*_0, Ap \rangle}, \quad s = r - \alpha A p,
  \quad \omega = \frac{\langle As, s \rangle}{\langle As, As \rangle}, \quad x' = x + \alpha p +
  \omega s,$$
$$r' = s - \omega A s, \quad \beta = \frac{\langle r^*_0, r' \rangle}{\langle r^*_0, r \rangle}
  \cdot \frac{\alpha}{\omega}, \quad p' = r' + \beta (p - \omega A p),$$
and returns $(x', r', p')$. -/
noncomputable def step (A : E →ₗ[𝕜] E) (rs₀ : E) (st : State E) : State E :=
  let α : 𝕜 := inner 𝕜 rs₀ st.r / inner 𝕜 rs₀ (A st.p)
  let s : E := st.r - α • A st.p
  let ω : 𝕜 := inner 𝕜 (A s) s / inner 𝕜 (A s) (A s)
  let r : E := s - ω • A s
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ st.r * (α / ω)
  { x := st.x + α • st.p + ω • s, r := r, p := r + β • (st.p - ω • A st.p) }

/-- **BiCGSTAB** ([saad2003iterative], Algorithm 7.7; [golub2013matrix], Figure 11.4.1). For
$b, x_0 \in E$, a shadow residual $r^*_0 \in E$ and $k \in \mathbb{N}$, it is the state after
$k$ applications of `BiCGSTAB.step` to the initial state with $x = x_0$ and $r = p = b - A x_0$.

Only $A$ is applied, and never its adjoint. The shadow residual $r^*_0$ is arbitrary. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A rs₀)^[k] { x := x₀, r := b - A x₀, p := b - A x₀ }

variable (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The BiCGSTAB step length $\alpha_j = \langle r^*_0, r_j \rangle / \langle r^*_0, A p_j \rangle$.
-/
noncomputable def alpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r / inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)

/-- The half-step residual $s_j = r_j - \alpha_j A p_j$. -/
noncomputable def s (j : ℕ) : E :=
  (iterate A b x₀ rs₀ j).r - alpha A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p

/-- The stabilizing step $\omega_j = \langle A s_j, s_j \rangle / \langle A s_j, A s_j \rangle$,
which minimizes $\|s_j - \omega A s_j\|$ over $\omega$. -/
noncomputable def omega (j : ℕ) : 𝕜 :=
  inner 𝕜 (A (s A b x₀ rs₀ j)) (s A b x₀ rs₀ j) /
    inner 𝕜 (A (s A b x₀ rs₀ j)) (A (s A b x₀ rs₀ j))

/-- The BiCGSTAB coefficient $\beta_j = (\langle r^*_0, r_{j+1} \rangle / \langle r^*_0, r_j
\rangle) (\alpha_j / \omega_j)$. -/
noncomputable def beta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r
    * (alpha A b x₀ rs₀ j / omega A b x₀ rs₀ j)

/-- The initial BiCGSTAB state is $x = x_0$ and $r = p = b - A x_0$. -/
@[simp] theorem iterate_zero :
    iterate A b x₀ rs₀ 0 = { x := x₀, r := b - A x₀, p := b - A x₀ } := rfl

/-- The state after $k + 1$ steps is `BiCGSTAB.step` applied to the state after $k$ steps. -/
theorem iterate_succ (k : ℕ) :
    iterate A b x₀ rs₀ (k + 1) = step A rs₀ (iterate A b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The recurrence $x_{j+1} = x_j + \alpha_j p_j + \omega_j s_j$. -/
theorem iterate_succ_x (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).x =
    (iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p
      + omega A b x₀ rs₀ j • s A b x₀ rs₀ j := by
  rw [iterate_succ]; rfl

/-- The recurrence $r_{j+1} = s_j - \omega_j A s_j$. -/
theorem iterate_succ_r (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).r =
    s A b x₀ rs₀ j - omega A b x₀ rs₀ j • A (s A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- The recurrence $p_{j+1} = r_{j+1} + \beta_j (p_j - \omega_j A p_j)$. -/
theorem iterate_succ_p (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).p =
    (iterate A b x₀ rs₀ (j + 1)).r + beta A b x₀ rs₀ j •
      ((iterate A b x₀ rs₀ j).p - omega A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p) := by
  simp only [beta, iterate_succ]; rfl

/-- The BiCGSTAB residual is the true residual of the BiCGSTAB iterate: $r_j = b - A x_j$ for every
$j$. -/
theorem r_eq_sub_apply_x (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = b - A (iterate A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iterate_succ_r, iterate_succ_x, s, ih, map_add, map_add, map_smul, map_smul]
    abel

/-- **The stabilizing half-step is a minimal-residual step** ([saad2003iterative], (7.55)). For
every $j$, the residual of the half-step iterate $y_j = x_j + \alpha_j p_j$ is $s_j$, and
$$x_{j+1} = y_j + \omega_j s_j$$
is the one-dimensional minimal-residual step `Projection.minResStep` from $y_j$, which minimizes
$\|s_j - \omega A s_j\|$ over $\omega$. -/
theorem iterate_succ_x_eq_minResStep (j : ℕ) :
    (iterate A b x₀ rs₀ (j + 1)).x = Projection.minResStep A b
      ((iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p) := by
  have hres : b - A ((iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p)
      = s A b x₀ rs₀ j := by
    rw [s, r_eq_sub_apply_x, map_add, map_smul]
    abel
  rw [Projection.minResStep, Projection.step1, hres, iterate_succ_x]
  rfl

/-- The **stabilizing polynomial** $\psi_j$ of BiCGSTAB ([saad2003iterative], (7.47)): $\psi_0 = 1$
and
$$\psi_{j+1} = (1 - \omega_j X) \psi_j,$$
where $\omega_j$ is the stabilizing step `BiCGSTAB.omega` that the method computes. -/
noncomputable def stabPoly : ℕ → 𝕜[X]
  | 0 => 1
  | j + 1 => (1 - C (omega A b x₀ rs₀ j) * X) * stabPoly j

/-- The stabilizing polynomial of step $0$ is $\psi_0 = 1$. -/
@[simp] theorem stabPoly_zero : stabPoly A b x₀ rs₀ 0 = 1 := rfl

/-- The recurrence $\psi_{j+1} = (1 - \omega_j X) \psi_j$. -/
theorem stabPoly_succ (j : ℕ) : stabPoly A b x₀ rs₀ (j + 1) =
    (1 - C (omega A b x₀ rs₀ j) * X) * stabPoly A b x₀ rs₀ j := rfl

private theorem stabPoly_succ_eq_sub (j : ℕ) : stabPoly A b x₀ rs₀ (j + 1) =
    stabPoly A b x₀ rs₀ j - C (omega A b x₀ rs₀ j) * (X * stabPoly A b x₀ rs₀ j) := by
  rw [stabPoly_succ]; ring

/-- The stabilizing polynomial $\psi_j$ has degree at most $j$. -/
theorem stabPoly_natDegree_le (j : ℕ) : (stabPoly A b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [stabPoly_succ_eq_sub]
    refine (natDegree_sub_le _ _).trans (max_le (ih.trans (Nat.le_succ j)) ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    simp only [natDegree_X]
    omega

/-- Let $\eta^{(j)}$ be the coefficient of $X^j$ in $\psi_j$. Then
$\eta^{(j+1)} = -\omega_j \eta^{(j)}$. -/
theorem stabPoly_coeff_succ (j : ℕ) :
    (stabPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -omega A b x₀ rs₀ j * (stabPoly A b x₀ rs₀ j).coeff j := by
  rw [stabPoly_succ_eq_sub, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (stabPoly_natDegree_le A b x₀ rs₀ j) (Nat.lt_succ_self j)),
    coeff_C_mul, coeff_X_mul]
  ring

/-- If $\omega_i \neq 0$ for every $i < j$, then the coefficient of $X^j$ in $\psi_j$ is nonzero.
This coefficient is $\prod_{i<j} (-\omega_i)$. -/
theorem stabPoly_coeff_ne_zero {j : ℕ} (hω : ∀ i < j, omega A b x₀ rs₀ i ≠ 0) :
    (stabPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [stabPoly_coeff_succ]
    exact mul_ne_zero (neg_ne_zero.2 (hω j (Nat.lt_succ_self j)))
      (ih fun i hi => hω i (by omega))

variable {A b x₀ rs₀}

section Polynomial

variable {B : E →ₗ[𝕜] E}

/-- **Only the leading coefficient survives.** Let $B$ be the adjoint of $A$, let $q$ be a
polynomial of degree at most $j$, and let $v$ be orthogonal to $\mathcal{K}_j(B, r^*_0)$. Then
$\langle r^*_0, q(A) v \rangle = q_j \langle B^j r^*_0, v \rangle$, where $q_j$ is the
coefficient of $X^j$ in $q$. -/
private theorem inner_aeval_eq_coeff_mul
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
    {j : ℕ} {p : 𝕜[X]} (hp : p.natDegree ≤ j) {v : E}
    (hv : ∀ u ∈ Krylov.subspace B rs₀ j, inner 𝕜 u v = 0) :
    inner 𝕜 rs₀ (aeval A p v) = p.coeff j * inner 𝕜 ((B ^ j) rs₀) v := by
  have hz : ∀ i < j, inner 𝕜 rs₀ ((A ^ i) v) = 0 := by
    intro i hi
    rw [← BiLanczos.inner_pow_apply_eq hB i rs₀ v]
    exact hv _ (Krylov.pow_apply_mem_subspace B rs₀ hi)
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hp) A, LinearMap.sum_apply, inner_sum,
    Finset.sum_eq_single j]
  · rw [LinearMap.smul_apply, inner_smul_right, BiLanczos.inner_pow_apply_eq hB j rs₀ v]
  · intro i hi hij
    rw [Finset.mem_range] at hi
    rw [LinearMap.smul_apply, inner_smul_right, hz i (by omega), mul_zero]
  · intro hc
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hc

variable {m : ℕ} (h : BCG.NoBreakdown A B b x₀ rs₀ m)
include h

/-- For $j \le m$, $\langle r^*_j, r_j \rangle = \gamma^{(j)} \langle B^j r^*_0, r_j \rangle$ for
the BCG sequences, where $\gamma^{(j)}$ is the coefficient of $X^j$ in $\varphi_j$. -/
private theorem inner_dualResidual_residual {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (BCG.dualResidual A B b x₀ rs₀ j) (BCG.residual A B b x₀ rs₀ j)
      = (BCG.residualPoly A B b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) := by
  obtain ⟨-, -, hbrs, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbrs, BiLanczos.inner_aeval_map_eq h.adjoint]
  exact inner_aeval_eq_coeff_mul h.adjoint (BCG.residualPoly_natDegree_le A B b x₀ rs₀ j)
    fun u hu => BCG.inner_residual_eq_zero_of_mem_subspace (h.mono hj) hu

/-- For $j \le m$, $\langle p^*_j, A p_j \rangle = \gamma^{(j)} \langle B^j r^*_0, A p_j \rangle$
for the BCG sequences, because $\pi_j$ and $\varphi_j$ have the same leading coefficient
$\gamma^{(j)}$. -/
private theorem inner_dualDirection_apply_direction {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (BCG.dualDirection A B b x₀ rs₀ j) (A (BCG.direction A B b x₀ rs₀ j))
      = (BCG.residualPoly A B b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (A (BCG.direction A B b x₀ rs₀ j)) := by
  obtain ⟨-, -, -, hbps⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbps, BiLanczos.inner_aeval_map_eq h.adjoint, ← BCG.directionPoly_coeff_self A B b x₀ rs₀ j]
  exact inner_aeval_eq_coeff_mul h.adjoint (BCG.directionPoly_natDegree_le A B b x₀ rs₀ j)
    fun u hu => BCG.inner_apply_direction_eq_zero_of_mem_subspace (h.mono hj) hu

/-- If the BiCGSTAB residual is $r_j = \psi_j(A) \varphi_j(A) r_0$, then $\langle r^*_0, r_j
\rangle = \eta^{(j)} \langle B^j r^*_0, r^{\mathrm{BCG}}_j \rangle$. -/
private theorem inner_residual {j : ℕ} (hj : j ≤ m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀)) :
    inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r
      = (stabPoly A b x₀ rs₀ j).coeff j * inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) := by
  obtain ⟨hbr, -, -, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hr, aeval_mul_apply, ← hbr]
  exact inner_aeval_eq_coeff_mul h.adjoint (stabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => BCG.inner_residual_eq_zero_of_mem_subspace (h.mono hj) hu

/-- If the BiCGSTAB direction is $p_j = \psi_j(A) \pi_j(A) r_0$, then $\langle r^*_0, A p_j
\rangle = \eta^{(j)} \langle B^j r^*_0, A p^{\mathrm{BCG}}_j \rangle$. -/
private theorem inner_apply_direction {j : ℕ} (hj : j ≤ m)
    (hp : (iterate A b x₀ rs₀ j).p
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀)) :
    inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)
      = (stabPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (A (BCG.direction A B b x₀ rs₀ j)) := by
  obtain ⟨-, hbp, -, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hp, aeval_mul_apply, ← aeval_apply_apply, ← hbp]
  exact inner_aeval_eq_coeff_mul h.adjoint (stabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => BCG.inner_apply_direction_eq_zero_of_mem_subspace (h.mono hj) hu

/-- For $j < m$ without breakdown, the leading coefficient $\gamma^{(j)}$ of $\varphi_j$ and the
pairing $\langle B^j r^*_0, r_j \rangle$ are both nonzero. -/
private theorem coeff_ne_zero_and {j : ℕ} (hj : j < m) :
    (BCG.residualPoly A B b x₀ rs₀ j).coeff j ≠ 0 ∧
      inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) ≠ 0 := by
  have h0 := h.inner_residual_ne_zero j hj
  rw [inner_dualResidual_residual h hj.le] at h0
  exact ⟨left_ne_zero_of_mul h0, right_ne_zero_of_mul h0⟩

private theorem alpha_eq_aux (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀))
    (hp : (iterate A b x₀ rs₀ j).p
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀)) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  have he := stabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  rw [alpha, BCG.alpha, inner_residual h hj.le hr, inner_apply_direction h hj.le hp,
    inner_dualResidual_residual h hj.le, inner_dualDirection_apply_direction h hj.le,
    mul_div_mul_left _ _ he, mul_div_mul_left _ _ (coeff_ne_zero_and h hj).1]

private theorem beta_eq_aux (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀))
    (hr' : (iterate A b x₀ rs₀ (j + 1)).r
      = aeval A (stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀))
    (hα : alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hg, hL⟩ := coeff_ne_zero_and h hj
  have he := stabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  have hωj := hω j hj
  rw [beta, BCG.beta, inner_residual h hj.le hr, inner_residual h hj hr',
    inner_dualResidual_residual h hj.le, inner_dualResidual_residual h hj,
    BCG.residualPoly_coeff_succ, stabPoly_coeff_succ, hα]
  field_simp

/-- **BiCGSTAB computes the stabilized BCG polynomials** ([saad2003iterative], (7.46) and (7.52),
due to van der Vorst; [golub2013matrix], §11.4.5). Let $r_0 = b - A x_0$. Assume that the BCG
run of $A$ and $B$ from $x_0$ with shadow residual $r^*_0$ does not break down through step $m$
(`BCG.NoBreakdown`, which includes that $B$ is the adjoint of $A$), and that $\omega_i \neq 0$
for every $i < m$. Then for every $j \le m$,
$$r_j = \psi_j(A) \varphi_j(A) r_0, \qquad p_j = \psi_j(A) \pi_j(A) r_0.$$

The two hypotheses are what the leading-coefficient argument behind `BiCGSTAB.alpha_eq` and
`BiCGSTAB.beta_eq` needs. -/
theorem residual_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j ≤ m) :
    (iterate A b x₀ rs₀ j).r
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hjm : j < m := by omega
    have hα := alpha_eq_aux h hω hjm hr hp
    have hs : s A b x₀ rs₀ j
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      have hpoly : stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          = stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j
            - C (BCG.alpha A B b x₀ rs₀ j)
              * (X * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j)) := by
        rw [BCG.residualPoly_succ]; ring
      rw [s, hr, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    have hr' : (iterate A b x₀ rs₀ (j + 1)).r = aeval A
        (stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      have hpoly : stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          = stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)
            - C (omega A b x₀ rs₀ j)
              * (X * (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1))) := by
        rw [stabPoly_succ]; ring
      rw [iterate_succ_r, hs, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    refine ⟨hr', ?_⟩
    have hβ := beta_eq_aux h hω hjm hr hr' hα
    have hpoly : stabPoly A b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
        = stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          + C (BCG.beta A B b x₀ rs₀ j)
            * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
              - C (omega A b x₀ rs₀ j)
                * (X * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j))) := by
      rw [BCG.directionPoly_succ A B b x₀ rs₀ j, stabPoly_succ]
      ring
    rw [iterate_succ_p, hr', hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul, aeval_apply_sub,
      aeval_apply_C_mul, aeval_apply_X_mul]

/-- **The BCG step length from the BiCGSTAB vectors** ([saad2003iterative], (7.53)). Under the
hypotheses of `BiCGSTAB.residual_eq` (no BCG breakdown through step $m$, and $\omega_i \neq 0$
for $i < m$), for every $j < m$ the BiCGSTAB step length $\alpha_j = \langle r^*_0, r_j \rangle
/ \langle r^*_0, A p_j \rangle$ is the BCG step length $\alpha_j$. -/
theorem alpha_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  obtain ⟨hr, hp⟩ := residual_eq h hω hj.le
  exact alpha_eq_aux h hω hj hr hp

/-- **The BCG direction coefficient from the BiCGSTAB vectors** ([saad2003iterative], (7.54)). Under
the hypotheses of `BiCGSTAB.residual_eq` (no BCG breakdown through step $m$, and
$\omega_i \neq 0$ for $i < m$), for every $j < m$ the BiCGSTAB coefficient $\beta_j = (\langle
r^*_0, r_{j+1} \rangle / \langle r^*_0, r_j \rangle) (\alpha_j / \omega_j)$ is the BCG
coefficient $\beta_j$. -/
theorem beta_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hr, hp⟩ := residual_eq h hω hj.le
  exact beta_eq_aux h hω hj hr (residual_eq h hω hj).1 (alpha_eq_aux h hω hj hr hp)

end Polynomial

end BiCGSTAB
