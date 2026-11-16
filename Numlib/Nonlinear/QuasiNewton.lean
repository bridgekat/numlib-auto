/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# Broyden's method for nonlinear systems

Let $E$ be a real inner product space and $F \colon E \to E$. Broyden's method solves $F(x) = 0$
with the Newton-like iteration $Q_k \delta_k = -F(x_k)$, $x_{k+1} = x_k + \delta_k$, in which the
approximation $Q_k$ of the Jacobian is corrected after each step by a rank-one update
([quarteroni2000numerical], §7.1.4, (7.11)–(7.14); [dennis1996numerical], Chapter 8). For a step $s$
and the corresponding change $y$ of $F$, the update is
$$Q_+ = Q + \frac{(y - Q s) \otimes s}{\langle s, s \rangle}, \qquad (u \otimes s) v = \langle s, v
  \rangle u.$$
It has three defining properties: the secant condition $Q_+ s = y$; $Q_+ - Q$ vanishes on every
vector orthogonal to $s$, which is the least-change reading of the derivation in
[quarteroni2000numerical]; and $Q_+$ is closest to $Q$ in the operator norm among all operators that
satisfy the secant condition, with $\|Q_+ - Q\| = \|y - Q s\| / \|s\|$.

For matrices $Q \in \mathbb{R}^{n \times n}$ the update is the case $c = s$ of the rank-one secant
update $B_+ = B + (y - B s) c^T / (c^T s)$ of (7.42) of [quarteroni2000numerical]. Its error against
any matrix $J$ splits as $(Q - J)(I - P) + (y - J s) s^T / (s^T s)$ with $P = s s^T / (s^T s)$. This
gives the least-change property in the Frobenius norm and the **bounded deterioration** estimate
$$\|Q_+ - J(z)\|_F \le \|Q - J(z)\|_F + \frac{L}{2} \bigl(\|x_+ - z\| + \|x - z\|\bigr),$$
which is the first step of every proof of superlinear convergence of Broyden's method
([dennis1996numerical], Lemmas 8.1.1 and 8.2.1). The superlinear convergence theorem itself,
Property 7.2 of [quarteroni2000numerical] and the Dennis–Moré theory, is
`Broyden.exists_superlinear` in `Numlib.Nonlinear.DennisMore`.

## Main definitions

* `Broyden.update`: Broyden's update $Q_+$ of an operator $Q$ for the secant pair $(s, y)$.
* `Broyden.State`: the state $(x, Q)$ of the iteration.
* `Broyden.step`: one step of Broyden's method.
* `Broyden.iterate`: the states of Broyden's method from $(x_0, Q_0)$.
* `Matrix.rankOneSecantUpdate`: the rank-one secant update $B + (y - B s) c^T / (c^T s)$.
* `Matrix.broydenUpdate`: Broyden's update of a matrix.

## Main results

* `Broyden.update_apply_self`: the secant condition $Q_+ s = y$ for $s \neq 0$.
* `Broyden.update_sub_apply_of_inner_eq_zero`: $(Q_+ - Q) v = 0$ for every $v$ orthogonal to $s$.
* `Broyden.norm_update_sub`: $\|Q_+ - Q\| = \|y - Q s\| / \|s\|$.
* `Broyden.norm_update_sub_le`: least change in the operator norm.
* `Broyden.step_Q_apply_sub`: the secant condition along the iteration.
* `Matrix.broydenUpdate_sub_eq`: the error of Broyden's update against any matrix $J$.
* `Matrix.toEuclideanCLM_broydenUpdate`: the matrix update is the operator update.
* `Matrix.frobenius_norm_broydenUpdate_sub_le`: least change in the Frobenius norm.
* `Matrix.frobenius_norm_broydenUpdate_sub_le_add`: bounded deterioration.

## Implementation notes

* The rank-one operator $u \otimes s$ is Mathlib's `InnerProductSpace.rankOne ℝ u s`.
* For $s = 0$ the coefficient $1 / \langle s, s \rangle$ is the value $0$ of $1/0$, and the update
  leaves $Q$ unchanged.
* The step solves $Q \delta = -F(x)$ with `ContinuousLinearMap.inverse`, as `Newton.step` does. For
  a singular $Q$ this gives $\delta = 0$, so the point does not move and the definition needs no
  hypothesis.
* Matrices act on `EuclideanSpace ℝ n` through `Matrix.toEuclideanCLM`, and the Frobenius norm is
  the one of `Matrix.Norms.Frobenius`.
* The estimates rest on two auxiliary facts. The first is the mean value inequality with the
  derivative frozen at a third point, $\|F(y) - F(x) - F'(z)(y - x)\| \le (L/2)(\|x - z\| + \|y -
  z\|) \|y - x\|$ (Lemma 4.1.15 of [dennis1996numerical]), which is
  `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add` of
  `Numlib.Analysis.Calculus.MeanValue`. The second is the Frobenius-norm contraction
  $\|A (I - s s^T / (s^T s))\|_F \le \|A\|_F$ of the projection off a line, which is
  `Matrix.frobenius_norm_mul_one_sub_le` of `Numlib.Analysis.Matrix.OperatorNorm` and follows from
  Pythagoras in the form $\|A\|_F^2 = \operatorname{tr}(A^T A)$.
-/

open scoped InnerProductSpace

namespace Broyden

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Broyden's update.** Let $E$ be a real inner product space, let $Q \colon E \to E$ be a
continuous linear map, and let $s, y \in E$. Broyden's update of $Q$ is
$$Q_+ = Q + \frac{1}{\langle s, s \rangle} (y - Q s) \otimes s,$$
where $(u \otimes s) v = \langle s, v \rangle u$. For $s = 0$ the coefficient
$1 / \langle s, s \rangle$ is $0$ and $Q_+ = Q$.

This is (7.14) of [quarteroni2000numerical]. In the notation of the source, $s = \delta x_k$ is
the last step and $y = b_k = F(x_k) - F(x_{k-1})$ is the corresponding change of $F$. The update
is the rank-one correction of $Q$ that enforces the secant condition $Q_+ s = y$ and leaves $Q$
unchanged on the orthogonal complement of $s$. The rank-one operator is
`InnerProductSpace.rankOne ℝ (y - Q s) s`. -/
noncomputable def update (Q : E →L[ℝ] E) (s y : E) : E →L[ℝ] E :=
  Q + (1 / ⟪s, s⟫_ℝ) • InnerProductSpace.rankOne ℝ (y - Q s) s

/-- For every $v \in E$, Broyden's update satisfies
$$Q_+ v = Q v + \frac{\langle s, v \rangle}{\langle s, s \rangle} (y - Q s).$$
-/
theorem update_apply (Q : E →L[ℝ] E) (s y v : E) :
    update Q s y v = Q v + (⟪s, v⟫_ℝ / ⟪s, s⟫_ℝ) • (y - Q s) := by
  simp only [update, add_apply, smul_apply, InnerProductSpace.rankOne_apply, smul_smul, one_div,
    inv_mul_eq_div]

/-- The correction made by Broyden's update is the scaled rank-one operator $Q_+ - Q = (y - Q s)
\otimes s / \langle s, s \rangle$. -/
theorem update_sub (Q : E →L[ℝ] E) (s y : E) :
    update Q s y - Q = (1 / ⟪s, s⟫_ℝ) • InnerProductSpace.rankOne ℝ (y - Q s) s :=
  sub_eq_of_eq_add' rfl

/-- **The secant condition.** If $s \neq 0$, then Broyden's update satisfies $Q_+ s = y$.

This is (7.12) of [quarteroni2000numerical] with $j = 1$. -/
theorem update_apply_self (Q : E →L[ℝ] E) {s : E} (hs : s ≠ 0) (y : E) : update Q s y s = y := by
  rw [update_apply, div_self (inner_self_ne_zero.2 hs), one_smul]
  abel

/-- **Broyden's update changes $Q$ only along $s$.** If $v \in E$ satisfies
$\langle s, v \rangle = 0$, then $(Q_+ - Q) v = 0$.

Together with the secant condition this characterizes (7.14) in §7.1.4 of
[quarteroni2000numerical]: $(Q_k - Q_{k-1}) v$ vanishes for every $v$ orthogonal to
$\delta x_k$. -/
theorem update_sub_apply_of_inner_eq_zero (Q : E →L[ℝ] E) (s y : E) {v : E}
    (hv : ⟪s, v⟫_ℝ = 0) : (update Q s y - Q) v = 0 := by
  simp [update_sub, InnerProductSpace.rankOne_apply, hv]

/-- The size of the correction: $\|Q_+ - Q\| = \|y - Q s\| / \|s\|$ in the operator norm. Both sides
are $0$ when $s = 0$. -/
theorem norm_update_sub (Q : E →L[ℝ] E) (s y : E) : ‖update Q s y - Q‖ = ‖y - Q s‖ / ‖s‖ := by
  rw [update_sub, norm_smul, InnerProductSpace.norm_rankOne, Real.norm_eq_abs,
    real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)]
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · field_simp

/-- **Least change in the operator norm.** Let $Q, Q' \colon E \to E$ be continuous linear maps and
$s \neq 0$, and suppose that $Q' s = y$. Then Broyden's update satisfies
$$\|Q_+ - Q\| \le \|Q' - Q\|.$$

So among all operators that satisfy the secant condition, Broyden's update is the closest to $Q$
([dennis1996numerical], §8.1). The proof is $\|Q_+ - Q\| = \|(Q' - Q) s\| / \|s\| \le \|Q' -
Q\|$. -/
theorem norm_update_sub_le (Q Q' : E →L[ℝ] E) {s : E} (hs : s ≠ 0) {y : E} (hQ' : Q' s = y) :
    ‖update Q s y - Q‖ ≤ ‖Q' - Q‖ := by
  rw [norm_update_sub, div_le_iff₀ (norm_pos_iff.2 hs), ← hQ', ← sub_apply]
  exact (Q' - Q).le_opNorm s

/-! ### The iteration -/

/-- A **state of Broyden's iteration** consists of the current point $x \in E$ and the current
approximation $Q \colon E \to E$ of the Jacobian, a continuous linear map. -/
structure State (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The current iterate $x$. -/
  x : E
  /-- The current approximation $Q$ of the Jacobian. -/
  Q : E →L[ℝ] E

/-- **One step of Broyden's method** for $F \colon E \to E$ from the state $(x, Q)$. Solve
$Q \delta = -F(x)$, move to $x_+ = x + \delta$, and replace $Q$ by Broyden's update for the
secant pair $(\delta, F(x_+) - F(x))$.

This is (7.11)–(7.14) of [quarteroni2000numerical]. The solution is $\delta = -Q^{-1} F(x)$ with
`ContinuousLinearMap.inverse`, so $\delta = 0$ when $Q$ is not invertible. -/
noncomputable def step (Fn : E → E) (σ : State E) : State E where
  x := σ.x - σ.Q.inverse (Fn σ.x)
  Q := update σ.Q (-(σ.Q.inverse (Fn σ.x))) (Fn (σ.x - σ.Q.inverse (Fn σ.x)) - Fn σ.x)

/-- The point of a Broyden step is $x_+ = x - Q^{-1} F(x)$. -/
theorem step_x (Fn : E → E) (σ : State E) : (step Fn σ).x = σ.x - σ.Q.inverse (Fn σ.x) :=
  rfl

/-- The operator of a Broyden step is Broyden's update of $Q$ with $s = x_+ - x$ and
$y = F(x_+) - F(x)$. -/
theorem step_Q (Fn : E → E) (σ : State E) :
    (step Fn σ).Q = update σ.Q ((step Fn σ).x - σ.x) (Fn (step Fn σ).x - Fn σ.x) := by
  simp only [step, sub_sub_cancel_left]

/-- **The secant condition along the iteration.** If the step moves the point, $x_+ \neq x$, then
the new operator satisfies $Q_+ (x_+ - x) = F(x_+) - F(x)$.

This is (7.12) of [quarteroni2000numerical] with $j = 1$. -/
theorem step_Q_apply_sub (Fn : E → E) (σ : State E) (h : (step Fn σ).x ≠ σ.x) :
    (step Fn σ).Q ((step Fn σ).x - σ.x) = Fn (step Fn σ).x - Fn σ.x := by
  rw [step_Q]
  exact update_apply_self _ (sub_ne_zero.2 h) _

/-- **The linear system of a step.** If $Q$ is invertible, then the step satisfies
$Q (x_+ - x) = -F(x)$.

This is (7.11) of [quarteroni2000numerical]. The invertible $Q$ is given as an equivalence `e`
with `(e : E →L[ℝ] E) = σ.Q`. -/
theorem apply_step_x_sub (Fn : E → E) (σ : State E) (e : E ≃L[ℝ] E)
    (he : (e : E →L[ℝ] E) = σ.Q) : σ.Q ((step Fn σ).x - σ.x) = -Fn σ.x := by
  rw [step_x, sub_sub_cancel_left, map_neg, ← he, ContinuousLinearMap.inverse_equiv]
  simp

/-- If $F(x) = 0$, then the point of a Broyden step from $(x, Q)$ is $x$ itself. -/
theorem step_x_eq_self_of_eq_zero (Fn : E → E) (σ : State E) (hx : Fn σ.x = 0) :
    (step Fn σ).x = σ.x := by
  simp [step_x, hx]

/-- The **states of Broyden's method** from the initial point $x_0$ and the initial approximation
$Q_0$: the $k$-fold application of `Broyden.step` to $(x_0, Q_0)$. -/
noncomputable def iterate (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) : State E :=
  (step Fn)^[k] ⟨x₀, Q₀⟩

/-- The state after $0$ steps is $(x_0, Q_0)$. -/
@[simp] theorem iterate_zero (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) :
    iterate Fn x₀ Q₀ 0 = ⟨x₀, Q₀⟩ :=
  rfl

/-- The recurrence of Broyden's method: the state after $k + 1$ steps is one step from the state
after $k$ steps. -/
theorem iterate_succ (Fn : E → E) (x₀ : E) (Q₀ : E →L[ℝ] E) (k : ℕ) :
    iterate Fn x₀ Q₀ (k + 1) = step Fn (iterate Fn x₀ Q₀ k) :=
  Function.iterate_succ_apply' _ _ _

end Broyden

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open WithLp

/-! ### Rank-one secant updates of matrices -/

/-- **The rank-one secant update.** Let $B \in \mathbb{R}^{n \times n}$ and
$s, y, c \in \mathbb{R}^n$. The update is
$$B_+ = B + \frac{1}{c^T s} (y - B s) c^T.$$
For $c^T s = 0$ the coefficient is $0$ and $B_+ = B$.

This is (7.42) of [quarteroni2000numerical], with an arbitrary scaling vector $c$. For $c = s$
it is Broyden's update `Matrix.broydenUpdate`. For $c = y - B s$ it is the symmetric rank-one
update `Matrix.sr1Update` of `Numlib.Optimization.QuasiNewton`. -/
noncomputable def rankOneSecantUpdate (B : Matrix n n ℝ) (s y c : n → ℝ) : Matrix n n ℝ :=
  B + (1 / (c ⬝ᵥ s)) • vecMulVec (y - B *ᵥ s) c

omit [DecidableEq n] in
/-- **The secant equation.** If $c^T s \neq 0$, then the rank-one secant update satisfies
$B_+ s = y$. -/
theorem rankOneSecantUpdate_mulVec (B : Matrix n n ℝ) {s c : n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : n → ℝ) : rankOneSecantUpdate B s y c *ᵥ s = y := by
  simp only [rankOneSecantUpdate, add_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, one_div, inv_mul_cancel₀ hcs, one_smul]
  abel

/-- **Broyden's update of a matrix.** For $Q \in \mathbb{R}^{n \times n}$ and
$s, y \in \mathbb{R}^n$,
$$Q_+ = Q + \frac{1}{s^T s} (y - Q s) s^T,$$
the rank-one secant update with $c = s$. For $s = 0$, $Q_+ = Q$.

This is (7.14) of [quarteroni2000numerical] in matrix form. -/
noncomputable def broydenUpdate (Q : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  rankOneSecantUpdate Q s y s

omit [DecidableEq n] in
/-- Broyden's update of a matrix is the rank-one secant update with $c = s$. -/
theorem broydenUpdate_eq_rankOneSecantUpdate (B : Matrix n n ℝ) (s y : n → ℝ) :
    broydenUpdate B s y = rankOneSecantUpdate B s y s :=
  rfl

omit [DecidableEq n] in
/-- Broyden's update of a matrix is $Q_+ = Q + (y - Q s) s^T / (s^T s)$. -/
theorem broydenUpdate_eq (Q : Matrix n n ℝ) (s y : n → ℝ) :
    broydenUpdate Q s y = Q + (1 / (s ⬝ᵥ s)) • vecMulVec (y - Q *ᵥ s) s :=
  rfl

/-- **The error of Broyden's update against any matrix.** Let $Q, J \in \mathbb{R}^{n \times n}$ and
$s, y \in \mathbb{R}^n$, and let $P = s s^T / (s^T s)$. Then
$$Q_+ - J = (Q - J)(I - P) + \frac{1}{s^T s} (y - J s) s^T.$$

The first term is the old error with its component along the step removed, and the second is the
secant residual of $J$. Both the bounded deterioration estimate and the Dennis–Moré inequality
start from this decomposition. For $s = 0$ both $P$ and the second term are $0$. -/
theorem broydenUpdate_sub_eq (Q J : Matrix n n ℝ) (s y : n → ℝ) :
    broydenUpdate Q s y - J
      = (Q - J) * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s)
        + (1 / (s ⬝ᵥ s)) • vecMulVec (y - J *ᵥ s) s := by
  rw [broydenUpdate_eq, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec,
    sub_mulVec, show y - Q *ᵥ s = (y - J *ᵥ s) - (Q *ᵥ s - J *ᵥ s) by abel, sub_vecMulVec,
    smul_sub]
  abel

omit [DecidableEq n] in
/-- Broyden's update with the step $s = 0$ leaves the matrix unchanged: $Q_+ = Q$. -/
theorem broydenUpdate_zero_left (Q : Matrix n n ℝ) (y : n → ℝ) :
    broydenUpdate Q 0 y = Q := by
  simp [broydenUpdate_eq]

/-- **The matrix update is the operator update.** For $Q \in \mathbb{R}^{n \times n}$ and
$s, y \in \mathbb{R}^n$, the operator on the Euclidean space $\mathbb{R}^n$ of Broyden's matrix
update of $Q$ is `Broyden.update` of the operator of $Q$, with $s$ and $y$ read as vectors of
the Euclidean space.

The operator of a matrix is `Matrix.toEuclideanCLM`, and a vector is read in
`EuclideanSpace ℝ n` by `WithLp.toLp 2`. -/
theorem toEuclideanCLM_broydenUpdate (Q : Matrix n n ℝ) (s y : n → ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (broydenUpdate Q s y)
      = Broyden.update (toEuclideanCLM (𝕜 := ℝ) Q) (toLp 2 s) (toLp 2 y) := by
  rw [broydenUpdate_eq, Broyden.update, map_add, map_smul, toEuclideanCLM_vecMulVec,
    EuclideanSpace.inner_toLp_toLp, star_trivial, toEuclideanCLM_toLp, ← toLp_sub]

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- For $w, s \in \mathbb{R}^n$, the rank-one matrix $w s^T / (s^T s)$ has Frobenius norm at most
$\|w\| / \|s\|$, with Euclidean norms on the right. Both sides are $0$ for $s = 0$, and in fact
equality holds. -/
theorem frobenius_norm_smul_vecMulVec_le (w s : n → ℝ) :
    ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖ ≤ ‖toLp 2 w‖ / ‖toLp 2 s‖ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
  calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec w s‖
      ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 w‖ * ‖toLp 2 s‖) := by
        gcongr
        exact frobenius_norm_vecMulVec_le _ _
    _ = ‖toLp 2 w‖ / ‖toLp 2 s‖ := by field_simp

/-- **Least change in the Frobenius norm.** Let $Q, Q' \in \mathbb{R}^{n \times n}$ and
$s, y \in \mathbb{R}^n$ with $s \neq 0$ and $Q' s = y$. Then Broyden's update satisfies
$$\|Q_+ - Q\|_F \le \|Q' - Q\|_F.$$

This is Lemma 8.1.1 of [dennis1996numerical]: among all matrices that satisfy the secant
condition, Broyden's update is the closest to $Q$. The proof is that
$Q_+ - Q = (Q' - Q) s s^T / (s^T s)$ has Frobenius norm
$\|(Q' - Q) s\| / \|s\| \le \|Q' - Q\|_F$. -/
theorem frobenius_norm_broydenUpdate_sub_le (Q Q' : Matrix n n ℝ) {s y : n → ℝ} (hs : s ≠ 0)
    (hQ's : Q' *ᵥ s = y) : ‖broydenUpdate Q s y - Q‖ ≤ ‖Q' - Q‖ := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  rw [broydenUpdate_eq, add_sub_cancel_left, ← hQ's, ← sub_mulVec]
  calc ‖(1 / (s ⬝ᵥ s)) • vecMulVec ((Q' - Q) *ᵥ s) s‖
      ≤ ‖toLp 2 ((Q' - Q) *ᵥ s)‖ / ‖toLp 2 s‖ := frobenius_norm_smul_vecMulVec_le _ _
    _ ≤ ‖Q' - Q‖ * ‖toLp 2 s‖ / ‖toLp 2 s‖ := by
        gcongr
        exact frobenius_norm_mulVec_le _ _
    _ = ‖Q' - Q‖ := by field_simp

/-- **Bounded deterioration of Broyden's update.** Let $F \colon \mathbb{R}^n \to \mathbb{R}^n$, let
$D \subseteq \mathbb{R}^n$ be convex, and let $F$ have Jacobian
$J(w) \in \mathbb{R}^{n \times n}$ at every $w \in D$. Let $z \in \mathbb{R}^n$ and
$L \in \mathbb{R}$ with $\|J(w) - J(z)\| \le L \|w - z\|$ for all $w \in D$, in the operator
norm of the Euclidean space. Let $x \in D$ and $s \neq 0$ with $x + s \in D$, let
$y = F(x + s) - F(x)$, and let $Q \in \mathbb{R}^{n \times n}$. Then, with $x_+ = x + s$ and
$Q_+$ Broyden's update of $Q$ for $(s, y)$,
$$\|Q_+ - J(z)\|_F \le \|Q - J(z)\|_F + \frac{L}{2} \bigl(\|x_+ - z\| + \|x - z\|\bigr).$$

This is Lemma 8.2.1 of [dennis1996numerical], the estimate from which every proof of superlinear
convergence of Broyden's method starts (the Dennis–Moré theory, Property 7.2 of
[quarteroni2000numerical]). The proof uses the decomposition `Matrix.broydenUpdate_sub_eq` with
$J = J(z)$. The first term is bounded by `Matrix.frobenius_norm_mul_one_sub_le`, and the second
by $\|y - J(z) s\| / \|s\|$ and the mean value inequality with the derivative frozen at a third
point, `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add`. -/
theorem frobenius_norm_broydenUpdate_sub_le_add {F : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {J : EuclideanSpace ℝ n → Matrix n n ℝ} {D : Set (EuclideanSpace ℝ n)} (hD : Convex ℝ D)
    (hF : ∀ w ∈ D, HasFDerivAt F (toEuclideanCLM (𝕜 := ℝ) (J w)) w) {z : EuclideanSpace ℝ n}
    {L : ℝ}
    (hL : ∀ w ∈ D, ‖toEuclideanCLM (𝕜 := ℝ) (J w) - toEuclideanCLM (𝕜 := ℝ) (J z)‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ n} (hx : x ∈ D) {s : n → ℝ} (hs : s ≠ 0) (hxs : x + toLp 2 s ∈ D)
    (Q : Matrix n n ℝ) :
    ‖broydenUpdate Q s (ofLp (F (x + toLp 2 s) - F x)) - J z‖
      ≤ ‖Q - J z‖ + L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
  set y : n → ℝ := ofLp (F (x + toLp 2 s) - F x) with hy
  set w : n → ℝ := y - J z *ᵥ s with hw
  set P : Matrix n n ℝ := (1 / (s ⬝ᵥ s)) • vecMulVec s s with hPdef
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  -- the decomposition
  have hdecomp : broydenUpdate Q s y - J z
      = (Q - J z) * (1 - P) + (1 / (s ⬝ᵥ s)) • vecMulVec w s :=
    broydenUpdate_sub_eq Q (J z) s y
  -- the mean value estimate for the secant residual
  have hmv : ‖toLp 2 w‖ ≤ L / 2 * (‖x - z‖ + ‖x + toLp 2 s - z‖) * ‖toLp 2 s‖ := by
    have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le_add hD hF
      (y := x + toLp 2 s) hx hxs hL
    rw [add_sub_cancel_left] at h
    refine le_of_eq_of_le ?_ h
    rw [hw, hy, toLp_sub, toLp_ofLp, toEuclideanCLM_toLp]
  have hsecond : ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖
      ≤ L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
    calc ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖ ≤ ‖toLp 2 w‖ / ‖toLp 2 s‖ :=
          frobenius_norm_smul_vecMulVec_le _ _
      _ ≤ L / 2 * (‖x - z‖ + ‖x + toLp 2 s - z‖) * ‖toLp 2 s‖ / ‖toLp 2 s‖ := by gcongr
      _ = L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) := by
          field_simp
          ring
  calc ‖broydenUpdate Q s y - J z‖
      = ‖(Q - J z) * (1 - P) + (1 / (s ⬝ᵥ s)) • vecMulVec w s‖ := by rw [hdecomp]
    _ ≤ ‖(Q - J z) * (1 - P)‖ + ‖(1 / (s ⬝ᵥ s)) • vecMulVec w s‖ := norm_add_le _ _
    _ ≤ ‖Q - J z‖ + L / 2 * (‖x + toLp 2 s - z‖ + ‖x - z‖) :=
        add_le_add (frobenius_norm_mul_one_sub_le _ hs) hsecond

end Frobenius

end Matrix
