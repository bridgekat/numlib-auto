/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.ZeroChain
import Numlib.Optimization.ModelBased.TaylorModel
import NumlibSurface.CartisGouldToint.Chapter02.Section02
import NumlibSurface.CartisGouldToint.Chapter03.Section03
import NumlibSurface.CartisGouldToint.Chapter03.Section04

/-!
# Cartis, Gould and Toint, Section 3.5: Optimal complexity for methods using second derivatives

This module formalizes Sections 3.5.1–3.5.2 of [cartis2022evaluation], with the corresponding proofs
of Appendix B, on $\mathbb{R}^n$. Section 3.5.1 defines the class $\mathcal{M}$ of second-order
methods. These are deterministic methods whose iterates depend only on the values $f(x_i)$,
$\nabla f(x_i)$ and $\nabla^2 f(x_i)$ at the earlier iterates, and whose steps $s_k = x_{k+1} - x_k$
(3.5.1) solve the regularized Newton system
$$(\nabla^2 f(x_k) + \lambda_k I) s_k = -\nabla f(x_k) + r_k \qquad (3.5.2)$$
with a small residual $r_k$, a multiplier $\lambda_k \ge 0$ that makes
$\nabla^2 f(x_k) + \lambda_k I$ positive semidefinite (3.5.3), and the bound (3.5.4) on $\lambda_k$.
Lemmas 3.5.1–3.5.3 relate the multiplier and the step length to the gradient. Theorem 3.5.4 shows
that every method in $\mathcal{M}$ can need $\lceil \epsilon_1^{-3/2} \rceil$ iterations to reach
$\|\nabla f(x_k)\| \le \epsilon_1$, on a one-dimensional function whose smoothness constants do not
depend on $\epsilon_1$. Corollary 3.5.5 shows that AR2, TRε and iRN attain this bound, so that their
complexity $O(\epsilon_1^{-3/2})$ is optimal in $\mathcal{M}$.

The methods are the oracle methods `Optimization.OracleMethod` of
`Numlib.Optimization.Complexity.OracleMethod`. The one-dimensional function interpolates the data
(3.5.11)–(3.5.12) of `Numlib.Optimization.Complexity.SlowExample.Basic`.

## Main definitions

* Equations (3.5.1)–(3.5.4), `CartisGouldToint.Chapter03.IsMClassEquation`,
  `CartisGouldToint.Chapter03.IsMClassStepWith`, `CartisGouldToint.Chapter03.IsMClassStep`: the
  system (3.5.2) and the conditions (3.5.2)–(3.5.4) on one step.
* Section 3.5.1, `CartisGouldToint.Chapter03.IsMClassMethod`: a second-order oracle method is in the
  class $\mathcal{M}$ on $f$.

## Main results

* Lemma 3.5.1, `CartisGouldToint.Chapter03.lemma_3_5_1`: a multiplier
  $\lambda \le \bar\kappa_\lambda \|s\|$ satisfies (3.5.4) with $\kappa_\lambda = 2
  \sqrt{\bar\kappa_\lambda (1 + \kappa_{rg})}$.
* Lemma 3.5.2, `CartisGouldToint.Chapter03.lemma_3_5_2` and
  `CartisGouldToint.Chapter03.lemma_3_5_2_sqrt`: under Assumption f.HL, $\|s\| \ge \bar\kappa_s
  \|\nabla f(x + s)\|^{1/2}$.
* Lemma 3.5.3, `CartisGouldToint.Chapter03.lemma_3_5_3`: if the gradients converge quadratically,
  then $\|s_k\| \ge \bar\kappa_s \|\nabla f(x_{k+1})\|^{1/2}$.
* Theorem 3.5.4, `CartisGouldToint.Chapter03.theorem_3_5_4`: for every method in $\mathcal{M}$ there
  is a function that satisfies Assumptions f.Bb, f.gL and f.HL, with constants independent of
  $\epsilon_1$, on which the method first reaches $\|\nabla f(x_k)\| \le \epsilon_1$ at
  $k = \lceil \epsilon_1^{-3/2} \rceil$. The one-dimensional function is
  `CartisGouldToint.Chapter03.exists_slowSecondOrder_ridge`.
* Corollary 3.5.5, `CartisGouldToint.Chapter03.corollary_3_5_5_i`,
  `CartisGouldToint.Chapter03.corollary_3_5_5_ii`, `CartisGouldToint.Chapter03.corollary_3_5_5_iii`:
  AR2, TRε and iRN have runs with steps of class $\mathcal{M}$ that terminate exactly at
  $\lceil \epsilon_1^{-3/2} \rceil$, which matches the upper bounds of Theorems 3.3.5, 3.4.5 and
  3.4.11. The one-dimensional criterion for steps of class $\mathcal{M}$ is
  `CartisGouldToint.Chapter03.isMClassStepWith_ridge`.

## Proof outline

In Theorem 3.5.4 the function must depend on the method. The proof therefore first computes the
iterates of the method on the data (3.5.12); they depend only on the oracle answers. On these data,
a step of class $\mathcal{M}$ has the form $s_k = \theta_k \epsilon_1^{1/2} / (2 f_k)$ with a step
factor $\theta_k \in [(1 - \kappa_{rg}) / \kappa_\lambda, 1 + \kappa_{rg}]$ (3.5.19), and this
follows directly from the part $\|r_k\| \le \kappa_{rg} \|\nabla f(x_k)\|$ of (3.5.2). The step
factors of the method are clipped to this interval, and a $C^2$ function interpolates the data at
the points that the clipped factors give. For a method in $\mathcal{M}$ the clipping is inactive, so
the method follows these points and first reaches $\|\nabla f(x_k)\| \le \epsilon_1$ at
$k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$. The detour of the source through the quadratic
inequalities after (3.5.16), and the constant $\kappa_r$ of (3.5.18), are not needed.

## Conventions

* The tolerance $\epsilon_1$ is `ε`.
* The power $\|\nabla f(x)\|^{1/2}$ is `√‖gradient f x‖`.
* The positive semidefiniteness in (3.5.3) is $\nabla^2 f(x)[d, d] + \lambda \|d\|^2 \ge 0$ for all
  $d$.
* The one-dimensional examples live on $\mathbb{R}^1$, which is `EuclideanSpace ℝ (Fin 1)`, and are
  ridge functions $x \mapsto G(\langle e_0, x \rangle)$ along the unit vector
  `CartisGouldToint.Chapter02.e₀`.

## Implementation notes

* The class $\mathcal{M}$ is a property of a method on one function $f$ and one tolerance
  $\epsilon_1$: the conditions (3.5.2)–(3.5.4) are required only for the steps before the first
  iterate with $\|\nabla f(x_k)\| \le \epsilon_1$.
* The oracle answers on a ridge function are ridge jets, `CartisGouldToint.Chapter03.ridgeJet`.
* The AR2 example of Corollary 3.5.5 is that of Theorem 3.3.6 (the data of Theorem 12.2.15 with zero
  Hessians), not the data (3.5.12).

## Deviations from the source

* **Lemma 3.5.1** (typo). The printed constant $\kappa_\lambda = 2 \sqrt{\kappa_\lambda (1 +
  \kappa_{rg})}$ is self-referential; the proof gives $\kappa_\lambda = 2 \sqrt{\bar\kappa_\lambda
  (1 + \kappa_{rg})}$. See `CartisGouldToint.Chapter03.lemma_3_5_1`.
* **Lemma 3.5.1** (generalization). The lemma holds without (3.5.3), without $\kappa_{rg} < 1$ and
  without $s \ne 0$. See `CartisGouldToint.Chapter03.lemma_3_5_1`.
* **Lemma 3.5.2** (generalization). Assumptions f.Bb and f.gL are not needed, and the bound holds
  with the constant $C^{-1/2}$, which is at least $\bar\kappa_s = C^{-1}$ when
  $\bar\kappa_\lambda > 1$. See `CartisGouldToint.Chapter03.lemma_3_5_2_sqrt`.
* **Lemma 3.5.3** (generalization). Assumptions f.Bb and f.HL and the step relation (3.5.1) are not
  needed. See `CartisGouldToint.Chapter03.lemma_3_5_3`.
* **Theorem 3.5.4** (generalization). The bound $|f| \le B$ holds on all of $\mathbb{R}$, not only
  $f(x) \in [a, b]$ for $x \ge 0$. See `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **Equation (3.5.13)** (correction). The claim $f_k \in [1/2, 1]$ holds only for $k < k_\epsilon$;
  $f_{k_\epsilon} \in (0, 1/2]$. See `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **Equation (3.5.17)** (typo). The sign of the step is wrong; the step is
  $s_k = +\theta_k \epsilon_1^{1/2} / (2 f_k)$. See `CartisGouldToint.Chapter03.theorem_3_5_4`.
* **Corollary 3.5.5**, iRN (correction). The proof sketch of the source uses the data (3.5.12), on
  which the ratio (3.4.35) of iRN, which is not scale invariant, can be below $\eta$ when
  $\eta > 1/2$. The example is rescaled to $c G(x / c)$ with $c = \min(1, (2 \eta)^{-1/2})$, which
  keeps the gradients at the iterates and the termination index. See
  `CartisGouldToint.Chapter03.corollary_3_5_5_iii`.
-/

open Set Finset Optimization
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-! ### The class $\mathcal{M}$ -/

/-- **Equation (3.5.2)** of [cartis2022evaluation], the linear system. A step $s$ from $x$ with
multiplier $\lambda$ and residual $r$ satisfies $(\nabla^2 f(x) + \lambda I) s = -\nabla f(x) +
r$, that is,
$$\nabla^2 f(x)[s, v] + \lambda \langle s, v \rangle = -\langle \nabla f(x), v \rangle + \langle
  r, v \rangle \quad \text{for all } v.$$
-/
def IsMClassEquation (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : EuclideanSpace ℝ (Fin n))
    (lam : ℝ) (r : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ v, iteratedFDeriv ℝ 2 f x ![s, v] + lam * ⟪s, v⟫ = -⟪gradient f x, v⟫ + ⟪r, v⟫

/-- **Equations (3.5.2)–(3.5.4)** of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$,
let $x, s, r \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$, and let
$\kappa_{rg}, \kappa_{rs}, \kappa_\lambda$ be constants. The step $s$ from $x$ with multiplier
$\lambda$ and residual $r$ is **of class $\mathcal{M}$** if $s \ne 0$, the system (3.5.2) holds
with
$$\|r\| \le \min(\kappa_{rg} \|\nabla f(x)\|, \kappa_{rs} \|s\|^2),$$
$\lambda \ge 0$ and $\nabla^2 f(x) + \lambda I$ is positive semidefinite (3.5.3), and
$$\lambda_{\min}[\nabla^2 f(x)] + \lambda \le \kappa_\lambda \max\left(|\lambda_{\min}[\nabla^2
  f(x)]|, \|\nabla f(x)\|^{1/2}\right). \qquad (3.5.4)$$

Positive semidefiniteness is $\nabla^2 f(x)[d, d] + \lambda \|d\|^2 \ge 0$ for all $d$, and
$\lambda_{\min}[\nabla^2 f(x)]$ is `CartisGouldToint.Chapter01.hessianMinEig f x`. -/
structure IsMClassStepWith (f : EuclideanSpace ℝ (Fin n) → ℝ) (κrg κrs κlam : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (r : EuclideanSpace ℝ (Fin n)) : Prop where
  /-- The step is nonzero: $s \ne 0$. -/
  ne_zero : s ≠ 0
  /-- The system (3.5.2) holds. -/
  equation : IsMClassEquation f x s lam r
  /-- The residual bound of (3.5.2): $\|r\| \le \min(\kappa_{rg} \|\nabla f(x)\|, \kappa_{rs}
  \|s\|^2)$. -/
  residual : ‖r‖ ≤ min (κrg * ‖gradient f x‖) (κrs * ‖s‖ ^ 2)
  /-- The multiplier is nonnegative: $\lambda \ge 0$ (3.5.3). -/
  nonneg : 0 ≤ lam
  /-- The matrix $\nabla^2 f(x) + \lambda I$ is positive semidefinite (3.5.3):
  $\nabla^2 f(x)[d, d] + \lambda \|d\|^2 \ge 0$ for all $d$. -/
  psd : ∀ d, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => d) + lam * ‖d‖ ^ 2
  /-- The bound (3.5.4): $\lambda_{\min}[\nabla^2 f(x)] + \lambda \le \kappa_\lambda
  \max(|\lambda_{\min}[\nabla^2 f(x)]|, \|\nabla f(x)\|^{1/2})$. -/
  bound : Chapter01.hessianMinEig f x + lam ≤
    κlam * max |Chapter01.hessianMinEig f x| √‖gradient f x‖

/-- **Equations (3.5.1)–(3.5.4)** of [cartis2022evaluation]. A step $s$ from $x$ is **admissible for
the class $\mathcal{M}$** with constants $\kappa_{rg}, \kappa_{rs}, \kappa_\lambda$ if there are
a multiplier $\lambda$ and a residual $r$ such that $s$, $\lambda$ and $r$ satisfy
(3.5.2)–(3.5.4), as in `CartisGouldToint.Chapter03.IsMClassStepWith`. -/
def IsMClassStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (κrg κrs κlam : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam r, IsMClassStepWith f κrg κrs κlam x s lam r

/-- **Section 3.5.1** of [cartis2022evaluation], the class $\mathcal{M}$. Let $M$ be a deterministic
second-order oracle method on $\mathbb{R}^n$: its iterate $x_{k+1}$ is a function of the values
$f(x_i)$, $\nabla f(x_i)$ and $\nabla^2 f(x_i)$ at $x_0, \dots, x_k$. The method $M$ is **in the
class $\mathcal{M}$** on $f$ with constants $\kappa_{rg}, \kappa_{rs}, \kappa_\lambda$ and
tolerance $\epsilon$ if every step $s_k = x_{k+1} - x_k$ (3.5.1) taken at an iteration $k$ with
$\|\nabla f(x_j)\| > \epsilon$ for all $j \le k$ is admissible for the class $\mathcal{M}$, that
is, satisfies (3.5.2)–(3.5.4).

The iterates are `M.iterate (jetOracle f 2) k`, for the method `M : Optimization.OracleMethod ℝⁿ
(Optimization.Jet ℝⁿ 2)` and the oracle `Optimization.jetOracle`. The class is a property of the
method on one function and one tolerance. -/
def IsMClassMethod (κrg κrs κlam : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin n)) (Jet (EuclideanSpace ℝ (Fin n)) 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) : Prop :=
  UntilHit (fun k => ‖gradient f (M.iterate (jetOracle f 2) k)‖ ≤ ε) fun k =>
    IsMClassStep f κrg κrs κlam (M.iterate (jetOracle f 2) k)
      (M.iterate (jetOracle f 2) (k + 1) - M.iterate (jetOracle f 2) k)

/-! ### Lemmas 3.5.1–3.5.3 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s r : EuclideanSpace ℝ (Fin n)} {lam : ℝ}

/-- A bilinear form satisfies $|A[v, w]| \le \|A\| \|v\| \|w\|$. -/
private theorem abs_apply_vec_le
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) : |A ![v, w]| ≤ ‖A‖ * ‖v‖ * ‖w‖ := by
  have := A.le_opNorm ![v, w]
  simpa [Fin.prod_univ_two, mul_assoc] using this

/-- The system (3.5.2) tested against $s$ gives $\nabla^2 f(x)[s, s] + \lambda \|s\|^2 = \langle
-\nabla f(x) + r, s \rangle$. -/
private theorem IsMClassEquation.apply_self (h : IsMClassEquation f x s lam r) :
    iteratedFDeriv ℝ 2 f x (fun _ => s) + lam * ‖s‖ ^ 2 = -⟪gradient f x, s⟫ + ⟪r, s⟫ := by
  rw [apply_diag_eq_vec, ← real_inner_self_eq_norm_sq]
  exact h s

/-- **Lemma 3.5.1** of [cartis2022evaluation] (bounded multiplier). Let
$f : \mathbb{R}^n \to \mathbb{R}$, let $x, s, r \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$,
and let $\kappa_{rg} \ge 0$ and $\bar\kappa_\lambda \ge 1$. If $s$, $\lambda$ and $r$ satisfy
the system (3.5.2) with $\|r\| \le \kappa_{rg} \|\nabla f(x)\|$, and
$\lambda \le \bar\kappa_\lambda \|s\|$ (3.5.6), then (3.5.4) holds with $\kappa_\lambda = 2
\sqrt{\bar\kappa_\lambda (1 + \kappa_{rg})}$:
$$\lambda_{\min}[\nabla^2 f(x)] + \lambda \le 2 \sqrt{\bar\kappa_\lambda (1 + \kappa_{rg})}
  \max\left(|\lambda_{\min}[\nabla^2 f(x)]|, \|\nabla f(x)\|^{1/2}\right).$$

**Typo.** The source prints the self-referential constant $\kappa_\lambda = 2
\sqrt{\kappa_\lambda (1 + \kappa_{rg})}$; the proof in Appendix B gives
$2 \sqrt{\bar\kappa_\lambda (1 + \kappa_{rg})}$, which is used here. **Generalization.** The
lemma holds without (3.5.3), without $\kappa_{rg} < 1$ and without $s \ne 0$; only
$\kappa_{rg} \ge 0$ and $\bar\kappa_\lambda \ge 1$ are used.

No differentiability of $f$ is assumed: the proof uses (3.5.2) only as a relation between the
values $\nabla f(x)$ and $\nabla^2 f(x)$. -/
theorem lemma_3_5_1 {κrg κbar : ℝ} (hrg : 0 ≤ κrg) (hκ : 1 ≤ κbar)
    (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrg * ‖gradient f x‖)
    (hlam : lam ≤ κbar * ‖s‖) :
    Chapter01.hessianMinEig f x + lam ≤
      2 * √(κbar * (1 + κrg)) * max |Chapter01.hessianMinEig f x| √‖gradient f x‖ := by
  set m := Chapter01.hessianMinEig f x
  set g := ‖gradient f x‖
  set c := κbar * (1 + κrg)
  have hc1 : 1 ≤ c := by nlinarith
  have hsc : 1 ≤ √c := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hc1
  set M := max |m| (√c * √g)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hMsq : c * g ≤ M ^ 2 := by
    have h1 : √c * √g ≤ M := le_max_right _ _
    have h2 : (√c * √g) ^ 2 = c * g := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (norm_nonneg _)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg g)]
  have hMle : M ≤ √c * max |m| √g := by
    refine max_le ?_ ?_
    · calc |m| = 1 * |m| := (one_mul _).symm
        _ ≤ √c * max |m| √g := mul_le_mul hsc (le_max_left _ _) (abs_nonneg _) (by linarith)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  -- `(λ_min + λ) ‖s‖² ≤ (1 + κ_rg) ‖∇f(x)‖ ‖s‖`
  have hkey : (m + lam) * ‖s‖ ^ 2 ≤ (1 + κrg) * g * ‖s‖ := by
    have h1 := heq.apply_self
    have h2 := minCurvature_mul_norm_sq_le (iteratedFDeriv ℝ 2 f x) s
    have h3 : -⟪gradient f x, s⟫ + ⟪r, s⟫ ≤ g * ‖s‖ + ‖r‖ * ‖s‖ := by
      have := real_inner_le_norm r s
      have := neg_le_of_abs_le (abs_real_inner_le_norm (gradient f x) s)
      linarith
    have h4 : ‖r‖ * ‖s‖ ≤ κrg * g * ‖s‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    change m * ‖s‖ ^ 2 ≤ _ at h2
    nlinarith
  have hmain : m + lam ≤ 2 * M := by
    by_contra hcon
    push Not at hcon
    have hlamM : M < lam := by
      have := le_abs_self m
      have := le_max_left |m| (√c * √g)
      linarith
    have hs : 0 < ‖s‖ := by
      have : 0 < κbar * ‖s‖ := by linarith
      exact pos_of_mul_pos_right this (by linarith)
    have h1 : (m + lam) * ‖s‖ ≤ (1 + κrg) * g := by
      have := hkey
      rw [sq, ← mul_assoc] at this
      exact le_of_mul_le_mul_right this hs
    have h2 : (m + lam) * lam ≤ c * g := by
      have hpos : 0 ≤ m + lam := by linarith
      calc (m + lam) * lam ≤ (m + lam) * (κbar * ‖s‖) := mul_le_mul_of_nonneg_left hlam hpos
        _ = κbar * ((m + lam) * ‖s‖) := by ring
        _ ≤ κbar * ((1 + κrg) * g) := mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = c * g := by ring
    nlinarith
  calc m + lam ≤ 2 * M := hmain
    _ ≤ 2 * (√c * max |m| √g) := by linarith
    _ = _ := by ring

/-- Under Assumption f.HL with constant $L$, a step that solves (3.5.2) satisfies $\|\nabla f(x +
s)\| \le \tfrac{L}{2} \|s\|^2 + \|r - \lambda s\|$. -/
private theorem norm_gradient_add_le_of_equation {L : ℝ} (hf : AssumptionHL f L)
    (heq : IsMClassEquation f x s lam r) :
    ‖gradient f (x + s)‖ ≤ L / 2 * ‖s‖ ^ 2 + ‖r - lam • s‖ := by
  have hfx := hf.contDiffAt x
  have hvec : gradient f x + hessianOperator f x s = r - lam • s := by
    refine ext_inner_right ℝ fun v => ?_
    have hsym := hessianOperator_isSymmetric hfx s v
    change ⟪hessianOperator f x s, v⟫ = ⟪s, hessianOperator f x v⟫ at hsym
    have h1 := heq v
    rw [← inner_hessianOperator_apply hfx] at h1
    rw [inner_add_left, hsym, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
    linarith
  rw [← hvec]
  exact norm_gradient_add_le hf

/-- **Lemma 3.5.2** of [cartis2022evaluation], sharp form. Let $f$ satisfy Assumption f.HL with
constant $L_{f,2}$, and let $\kappa_{rs} \ge 0$ and $\bar\kappa_\lambda \ge 0$. If $s$,
$\lambda$ and $r$ satisfy (3.5.2) at $x$ with $\|r\| \le \kappa_{rs} \|s\|^2$ and
$0 \le \lambda \le \bar\kappa_\lambda \|s\|$ (3.5.6), then, with $C = L_{f,2}/2 + \kappa_{rs} +
\bar\kappa_\lambda$,
$$\|\nabla f(x + s)\| \le C \|s\|^2 \quad\text{and}\quad \|s\| \ge C^{-1/2} \|\nabla f(x +
  s)\|^{1/2}.$$

**Generalization.** The source also assumes Assumptions f.Bb and f.gL; they are not needed. The
source gives the constant $\bar\kappa_s = C^{-1}$ in (3.5.7). When $C \ge 1$, which holds under
the hypothesis $\bar\kappa_\lambda > 1$ of the source, $C^{-1/2} \ge C^{-1}$, so the bound here
is stronger. -/
theorem lemma_3_5_2_sqrt {L κrs κbar : ℝ} (hf : AssumptionHL f L) (hrs : 0 ≤ κrs)
    (hκ : 0 ≤ κbar) (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrs * ‖s‖ ^ 2)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ κbar * ‖s‖) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + κrs + κbar) * ‖s‖ ^ 2 ∧
      (√(L / 2 + κrs + κbar))⁻¹ * √‖gradient f (x + s)‖ ≤ ‖s‖ := by
  have h1 := norm_gradient_add_le_of_equation hf heq
  have h2 : ‖r - lam • s‖ ≤ (κrs + κbar) * ‖s‖ ^ 2 := by
    calc ‖r - lam • s‖ ≤ ‖r‖ + ‖lam • s‖ := norm_sub_le _ _
      _ = ‖r‖ + lam * ‖s‖ := by rw [norm_smul, Real.norm_of_nonneg hlam0]
      _ ≤ κrs * ‖s‖ ^ 2 + κbar * ‖s‖ * ‖s‖ := by gcongr
      _ = (κrs + κbar) * ‖s‖ ^ 2 := by ring
  have hgrad : ‖gradient f (x + s)‖ ≤ (L / 2 + κrs + κbar) * ‖s‖ ^ 2 := by nlinarith
  refine ⟨hgrad, ?_⟩
  have hC : 0 < L / 2 + κrs + κbar := by linarith [hf.one_le]
  rw [inv_mul_le_iff₀ (Real.sqrt_pos.2 hC)]
  calc √‖gradient f (x + s)‖ ≤ √((L / 2 + κrs + κbar) * ‖s‖ ^ 2) := Real.sqrt_le_sqrt hgrad
    _ = √(L / 2 + κrs + κbar) * ‖s‖ := by
      rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)]

/-- **Lemma 3.5.2** of [cartis2022evaluation] (lower bound on the step). Let $f$ satisfy Assumption
f.HL with constant $L_{f,2}$, and let $\kappa_{rs} \ge 0$ and $\bar\kappa_\lambda > 1$. If $s$,
$\lambda$ and $r$ satisfy (3.5.2) at $x$ with $\|r\| \le \kappa_{rs} \|s\|^2$ and
$0 \le \lambda \le \bar\kappa_\lambda \|s\|$ (3.5.6), then
$$\|s\| \ge \bar\kappa_s \|\nabla f(x + s)\|^{1/2}, \qquad \bar\kappa_s =
  \left(\frac{L_{f,2}}{2} + \kappa_{rs} + \bar\kappa_\lambda\right)^{-1}. \qquad (3.5.7)$$

**Generalization.** The source also assumes Assumptions f.Bb and f.gL; they are not needed.

The bound follows from `CartisGouldToint.Chapter03.lemma_3_5_2_sqrt`, because $C = L_{f,2}/2 +
\kappa_{rs} + \bar\kappa_\lambda \ge 1$ gives $C^{-1} \le C^{-1/2}$. -/
theorem lemma_3_5_2 {L κrs κbar : ℝ} (hf : AssumptionHL f L) (hrs : 0 ≤ κrs)
    (hκ : 1 < κbar) (heq : IsMClassEquation f x s lam r) (hr : ‖r‖ ≤ κrs * ‖s‖ ^ 2)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ κbar * ‖s‖) :
    (L / 2 + κrs + κbar)⁻¹ * √‖gradient f (x + s)‖ ≤ ‖s‖ := by
  have h := (lemma_3_5_2_sqrt hf hrs (by linarith) heq hr hlam0 hlam).2
  set C := L / 2 + κrs + κbar
  have hC : 1 ≤ C := by have := hf.one_le; simp only [C]; linarith
  have hsC : √C ≤ C := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  refine le_trans ?_ h
  gcongr

/-- **Lemma 3.5.3** of [cartis2022evaluation] (a necessary condition for fast rates). Let $f$
satisfy Assumption f.gL with constant $L_1$, and let $\kappa_{rg} < 1$, $\bar\kappa_\lambda$ and
$\kappa_c > 0$ be constants. Let sequences $x_k, s_k, r_k \in \mathbb{R}^n$ and
$\lambda_k \in \mathbb{R}$ satisfy, for every $k$, the system (3.5.2) at $x_k$ with
$\|r_k\| \le \kappa_{rg} \|\nabla f(x_k)\|$, the bounds $0 \le \lambda_k \le \bar\kappa_\lambda$
(3.5.8), and the quadratic convergence
$$\|\nabla f(x_{k+1})\| \le \kappa_c \|\nabla f(x_k)\|^2. \qquad (3.5.9)$$
Then (3.5.7) holds for every $k$:
$$\|s_k\| \ge \frac{1 - \kappa_{rg}}{(L_1 + \bar\kappa_\lambda) \sqrt{\kappa_c}} \|\nabla
  f(x_{k+1})\|^{1/2}.$$

**Generalization.** The source also assumes Assumptions f.Bb and f.HL and the step relation
$s_k = x_{k+1} - x_k$ (3.5.1); they are not needed, because the hypotheses are stated about
$x_k$ and $x_{k+1}$ directly. -/
theorem lemma_3_5_3 {L₁ κrg κbar κc : ℝ} (hf : Chapter02.AssumptionGL f L₁) (hrg : κrg < 1)
    (hκc : 0 < κc) {x s r : ℕ → EuclideanSpace ℝ (Fin n)} {lam : ℕ → ℝ}
    (heq : ∀ k, IsMClassEquation f (x k) (s k) (lam k) (r k))
    (hr : ∀ k, ‖r k‖ ≤ κrg * ‖gradient f (x k)‖) (hlam : ∀ k, 0 ≤ lam k ∧ lam k ≤ κbar)
    (hquad : ∀ k, ‖gradient f (x (k + 1))‖ ≤ κc * ‖gradient f (x k)‖ ^ 2) (k : ℕ) :
    (1 - κrg) / ((L₁ + κbar) * √κc) * √‖gradient f (x (k + 1))‖ ≤ ‖s k‖ := by
  set g := ‖gradient f (x k)‖
  set w := -gradient f (x k) + r k
  have hκ : 0 ≤ κbar := (hlam 0).1.trans (hlam 0).2
  have hLκ : 0 < L₁ + κbar := by linarith [hf.one_le]
  have hHn := hf.norm_iteratedFDeriv_two_le (x k)
  -- `‖w‖ ≤ (L₁ + κ̄_λ) ‖s_k‖`
  have hw : ‖w‖ ≤ (L₁ + κbar) * ‖s k‖ := by
    have h1 := heq k w
    have h2 : ‖w‖ ^ 2 = iteratedFDeriv ℝ 2 f (x k) ![s k, w] + lam k * ⟪s k, w⟫ := by
      rw [h1, ← inner_neg_left, ← inner_add_left, real_inner_self_eq_norm_sq]
    have h3 := abs_apply_vec_le (iteratedFDeriv ℝ 2 f (x k)) (s k) w
    have h4 := abs_real_inner_le_norm (s k) w
    have h5 : lam k * ⟪s k, w⟫ ≤ κbar * (‖s k‖ * ‖w‖) := by
      calc lam k * ⟪s k, w⟫ ≤ lam k * (‖s k‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans h4) (hlam k).1
        _ ≤ κbar * (‖s k‖ * ‖w‖) := mul_le_mul_of_nonneg_right (hlam k).2 (by positivity)
    have h6 : iteratedFDeriv ℝ 2 f (x k) ![s k, w] ≤ L₁ * ‖s k‖ * ‖w‖ :=
      (le_abs_self _).trans (h3.trans (by gcongr))
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · have : ‖w‖ * ‖w‖ ≤ ((L₁ + κbar) * ‖s k‖) * ‖w‖ := by nlinarith
      exact le_of_mul_le_mul_right this h0
  -- `(1 - κ_rg) ‖∇f(x_k)‖ ≤ ‖w‖`
  have hgw : (1 - κrg) * g ≤ ‖w‖ := by
    have : g - ‖r k‖ ≤ ‖w‖ := by
      have := norm_sub_norm_le (-gradient f (x k)) (-(r k))
      rw [norm_neg, norm_neg, sub_neg_eq_add] at this
      exact this
    linarith [hr k]
  have hsq : √‖gradient f (x (k + 1))‖ ≤ √κc * g := by
    calc √‖gradient f (x (k + 1))‖ ≤ √(κc * g ^ 2) := Real.sqrt_le_sqrt (hquad k)
      _ = √κc * g := by rw [Real.sqrt_mul hκc.le, Real.sqrt_sq (norm_nonneg _)]
  have hsκ : 0 < √κc := Real.sqrt_pos.2 hκc
  calc (1 - κrg) / ((L₁ + κbar) * √κc) * √‖gradient f (x (k + 1))‖
      ≤ (1 - κrg) / ((L₁ + κbar) * √κc) * (√κc * g) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg (by linarith) (by positivity))
    _ = (1 - κrg) * g / (L₁ + κbar) := by field_simp
    _ ≤ ‖s k‖ := by
        rw [div_le_iff₀ hLκ]; linarith

end Lemmas

/-! ### The data (3.5.12) and the one-dimensional example -/


/-- The second-order jet along $e$ with coefficients $c_0, c_1, c_2$: the constant $c_0$, the linear
form $c_1 \langle e, \cdot \rangle$ and the bilinear form $c_2 \langle e, \cdot \rangle \langle
e, \cdot \rangle$. These are the jets of a ridge function $x \mapsto G(\langle e, x \rangle)$;
see `CartisGouldToint.Chapter03.jetOracle_ridge`. -/
noncomputable def ridgeJet (e : EuclideanSpace ℝ (Fin n)) (c : Fin 3 → ℝ) :
    Jet (EuclideanSpace ℝ (Fin n)) 2 := fun j =>
  c j • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
    fun _ => innerSL ℝ e

/-- For a $C^2$ function $G : \mathbb{R} \to \mathbb{R}$, the second-order oracle of the ridge
function $x \mapsto G(\langle e, x \rangle)$ at $x$ is the ridge jet along $e$ with the
coefficients $G^{(j)}(\langle e, x \rangle)$, $j = 0, 1, 2$. -/
theorem jetOracle_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (e x : EuclideanSpace ℝ (Fin n)) :
    jetOracle (ridge G e) 2 x = ridgeJet e fun j => iteratedDeriv j G ⟪e, x⟫ := by
  funext j
  ext m
  have hj : ((j : ℕ) : WithTop ℕ∞) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  rw [jetOracle_apply, iteratedFDeriv_ridge_apply hG hj]
  simp [ridgeJet, mul_comm]

/-- **Equations (3.5.11)–(3.5.21)** of [cartis2022evaluation], the one-dimensional example of
Theorem 3.5.4. Let $0 < a \le b$. There are $L_1 \ge 1$, $L_2 \ge 1$ and $B \ge 0$, which depend
only on $a$ and $b$, with the following property. Let $\epsilon \in (0, 1]$, let
$k_\epsilon = \lceil \epsilon^{-3/2} \rceil$, and let the data (3.5.12) be
$$f_k = 1 - \tfrac12 k \epsilon^{3/2}, \qquad g_k = -2 \epsilon f_k, \qquad H_k = 4
  \epsilon^{1/2} f_k^2.$$
For all step factors $\theta_k \in [a, b]$ and all abscissae $x_k$ with $x_{k+1} = x_k +
\theta_k \epsilon^{1/2} / (2 f_k)$ for $k < k_\epsilon$, there is a $C^2$ function
$G : \mathbb{R} \to \mathbb{R}$ such that the ridge function $f(x) = G(\langle e_0, x \rangle)$
on $\mathbb{R}^1$ satisfies Assumption f.Bb with $f_{\mathrm{low}} = -B$, Assumption f.gL with
$L_1$, Assumption f.HL with $L_2$ and $|f| \le B$, and $G$ interpolates the data:
$G(x_k) = f_k$, $G'(x_k) = g_k$ and $G''(x_k) = H_k$ for $k \le k_\epsilon$.

The construction follows the proof in Appendix B. The data are `Optimization.secondOrderK`,
`Optimization.secondOrderF`, `Optimization.secondOrderG` and `Optimization.secondOrderH`. The
example is also used for Corollary 3.5.5. -/
theorem exists_slowSecondOrder_ridge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < secondOrderK ε, θ k ∈ Icc a b) →
      (∀ k < secondOrderK ε,
        x (k + 1) = x k + θ k * ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε k)) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G Chapter02.e₀) (-B) ∧
        Chapter02.AssumptionGL (ridge G Chapter02.e₀) L₁ ∧
        AssumptionHL (ridge G Chapter02.e₀) L₂ ∧ (∀ y, |ridge G Chapter02.e₀ y| ≤ B) ∧
        ∀ k ≤ secondOrderK ε, G (x k) = secondOrderF ε k ∧
          deriv G (x k) = secondOrderG ε k ∧ iteratedDeriv 2 G (x k) = secondOrderH ε k := by
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowSecondOrder_interpolant ha hab
  refine ⟨max B 1, max L 1, B, le_max_right _ _, le_max_right _ _, hB,
    fun ε θ x hε hε1 hθ hx => ?_⟩
  obtain ⟨G, hG, hGL, hGB, hGk⟩ := H ε θ x hε hε1 hθ (fun k hk => by
    rw [hx k hk]; rfl)
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG hGL hGB
  refine ⟨G, hG, hb, hgl, hhl, fun y => by simpa [ridge_apply] using hGB 0 (by norm_num) _,
    fun k hk => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hGk k hk
  exact ⟨h0, by rw [h1]; rfl, by rw [h2]; rfl⟩

/-! ### Theorem 3.5.4 -/

section Theorem354

variable {ε : ℝ}

/-- The data jet $(f_k, g_k e_0, H_k e_0 e_0^T)$ of (3.5.12) at the $k$-th iterate. -/
private noncomputable def dataJet (ε : ℝ) (k : ℕ) : Jet (EuclideanSpace ℝ (Fin 1)) 2 :=
  ridgeJet Chapter02.e₀ ![secondOrderF ε k, secondOrderG ε k, secondOrderH ε k]

/-- The abscissae of the iterates that the method produces on the data (3.5.12). -/
private noncomputable def dataIter
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ) :
    ℕ → EuclideanSpace ℝ (Fin 1)
  | 0 => M.x₀
  | k + 1 => M.next k fun i => dataJet ε i

/-- The reference step $c_k = \epsilon^{1/2} / (2 f_k)$ at the $k$-th iterate. -/
private noncomputable def refStep (ε : ℝ) (k : ℕ) : ℝ := ε ^ (1 / 2 : ℝ) / (2 * secondOrderF ε k)

/-- The step factors of the method on the data (3.5.12), clipped to $[a, b]$. -/
private noncomputable def clipFactor (a b : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ)
    (k : ℕ) : ℝ :=
  max a (min b (⟪Chapter02.e₀, dataIter M ε (k + 1) - dataIter M ε k⟫ / refStep ε k))

/-- The interpolation abscissae: the first is $\langle e_0, x_0 \rangle$ for the starting point
$x_0$ of the method, and the next ones follow $x_{k+1} = x_k + \theta_k c_k$ with the clipped
step factors $\theta_k$. -/
private noncomputable def nodes (a b : ℝ)
    (M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2)) (ε : ℝ)
    (k : ℕ) : ℝ :=
  ⟪Chapter02.e₀, M.x₀⟫ + ∑ j ∈ range k, clipFactor a b M ε j * refStep ε j

/-- The step-factor bounds (3.5.19): if $g < 0$, $H > 0$, $\lambda \ge 0$, $\kappa_{rg} \le 1$,
$(H + \lambda) t = -g + \rho$ with $|\rho| \le \kappa_{rg} |g|$, and
$H + \lambda \le \kappa_\lambda H$, then $t = \theta (-g / H)$ with $\theta \in [(1 -
\kappa_{rg}) / \kappa_\lambda, 1 + \kappa_{rg}]$. -/
private theorem factor_mem {g H lam t ρ κrg κlam : ℝ} (hrg : κrg ≤ 1) (hg : g < 0) (hH : 0 < H)
    (hlam : 0 ≤ lam) (heq : (H + lam) * t = -g + ρ) (hρ : |ρ| ≤ κrg * |g|)
    (hb : H + lam ≤ κlam * H) :
    t / (-g / H) ∈ Icc ((1 - κrg) / κlam) (1 + κrg) := by
  have hκlam : 0 < κlam := by
    by_contra h; push Not at h; nlinarith
  have hHl : 0 < H + lam := by linarith
  have hg' : |g| = -g := abs_of_neg hg
  rw [hg'] at hρ
  have ht0 : t = (-g + ρ) / (H + lam) := by
    rw [eq_div_iff hHl.ne', mul_comm]; exact heq
  have ht : t / (-g / H) = (-g + ρ) * H / ((H + lam) * -g) := by
    rw [ht0]
    field_simp
  have hρ' := abs_le.1 hρ
  rw [ht]
  constructor
  · rw [div_le_div_iff₀ hκlam (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left hb (by nlinarith : (0 : ℝ) ≤ (1 - κrg) * -g),
      mul_le_mul_of_nonneg_right (by linarith : (1 - κrg) * -g ≤ -g + ρ) hH.le]
  · rw [div_le_iff₀ (by nlinarith)]
    have h1 : (-g + ρ) * H ≤ (1 + κrg) * -g * H :=
      mul_le_mul_of_nonneg_right (by linarith) hH.le
    have h2 : (1 + κrg) * -g * H ≤ (1 + κrg) * ((H + lam) * -g) := by
      have : 0 ≤ (1 + κrg) * -g := by nlinarith [abs_nonneg ρ]
      nlinarith
    linarith

/-- **Theorem 3.5.4** of [cartis2022evaluation] (a complexity lower bound for methods in
$\mathcal{M}$). Let $0 \le \kappa_{rg} < 1$, $\kappa_{rs} > 0$ and $\kappa_\lambda > 1$. There
are $f_{\mathrm{low}}$, $L_1 \ge 1$, $L_2 \ge 1$ and $B$ with the following property. For every
$\epsilon_1 \in (0, 1)$ and every deterministic second-order oracle method $M$ on
$\mathbb{R}^1$, with any starting point $x_0$, there is $f : \mathbb{R}^1 \to \mathbb{R}$ that
satisfies Assumption f.Bb with $f_{\mathrm{low}}$, Assumption f.gL with $L_1$, Assumption f.HL
with $L_2$, $|f| \le B$ and $f(x_0) = 1$, such that: if $M$ is in the class $\mathcal{M}$ on $f$
with tolerance $\epsilon_1$, then the first iterate with $\|\nabla f(x_k)\| \le \epsilon_1$ is
$x_{k_\epsilon}$, where $k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$. So the method needs
$k_\epsilon + 1$ evaluations of $f$, $\nabla f$ and $\nabla^2 f$.

**Generalization.** The bound $|f| \le B$ holds on all of $\mathbb{R}$; the source states
$f(x) \in [a, b]$ for $x \ge 0$. **Correction.** The claim (3.5.13) that $f_k \in [1/2, 1]$
holds only for $k < k_\epsilon$; at $k_\epsilon$ the value is $f_{k_\epsilon} \in (0, 1/2]$, and
this makes $k_\epsilon$ the first termination index. **Typo.** In (3.5.17) the sign of the step
is wrong: the step is $s_k = +\theta_k \epsilon_1^{1/2} / (2 f_k)$.

The hypothesis $\kappa_{rs} > 0$ is not used in the proof. The proof uses only the part
$\|r_k\| \le \kappa_{rg} \|\nabla f(x_k)\|$ of (3.5.2), which gives the step factors (3.5.19)
directly. The function is the ridge function of
`CartisGouldToint.Chapter03.exists_slowSecondOrder_ridge` for the clipped step factors of the
method. -/
theorem theorem_3_5_4 {κrg κrs κlam : ℝ} (hrg0 : 0 ≤ κrg) (hrg1 : κrg < 1) (_hrs : 0 < κrs)
    (hlam1 : 1 < κlam) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ M : OracleMethod (EuclideanSpace ℝ (Fin 1)) (Jet (EuclideanSpace ℝ (Fin 1)) 2),
        ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
          Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧ f M.x₀ = 1 ∧
          (IsMClassMethod κrg κrs κlam M f ε →
            IsFirstHit (fun k => ‖gradient f (M.iterate (jetOracle f 2) k)‖ ≤ ε)
              ⌈ε ^ (-(3 / 2 : ℝ))⌉₊) := by
  set a := (1 - κrg) / κlam
  set b := 1 + κrg
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hab : a ≤ b := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_slowSecondOrder_ridge ha hab
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 M => ?_⟩
  set K := secondOrderK ε
  set xs := nodes a b M ε
  have hθ : ∀ k, clipFactor a b M ε k ∈ Icc a b := fun k =>
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  obtain ⟨G, hG, hb, hgl, hhl, hB, hGk⟩ := H ε (clipFactor a b M ε) xs hε hε1.le
    (fun k _ => hθ k) (fun k _ => by
      simp only [xs, nodes, sum_range_succ, refStep, mul_div_assoc]; ring)
  set f := ridge G Chapter02.e₀
  have hxs0 : xs 0 = ⟪Chapter02.e₀, M.x₀⟫ := by simp [xs, nodes]
  have hx0' : M.x₀ = xs 0 • Chapter02.e₀ := by rw [hxs0]; exact eq_inner_e₀_smul _
  have hf0 : f M.x₀ = 1 := by
    have := (hGk 0 (Nat.zero_le _)).1
    simp only [f, ridge_apply]
    rw [← hxs0, this]; simp [secondOrderF]
  refine ⟨f, hb, hgl, hhl, hB, hf0, fun hM => ?_⟩
  -- facts on the data
  have hr : 0 < ε ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hfpos : ∀ k ≤ K, 0 < secondOrderF ε k := fun k hk => secondOrderF_pos hε hε1 hk
  have hgrad : ∀ y, gradient f y = deriv G ⟪Chapter02.e₀, y⟫ • Chapter02.e₀ :=
    gradient_ridge (hG.differentiable (by norm_num))
  have hnorm : ∀ k ≤ K, ‖gradient f (xs k • Chapter02.e₀)‖ = 2 * ε * secondOrderF ε k :=
    fun k hk => by
      rw [hgrad, Chapter02.inner_e₀_smul, (hGk k hk).2.1, norm_smul, Chapter02.norm_e₀,
        mul_one, secondOrderG, Real.norm_eq_abs, abs_of_neg]
      · ring
      · have := hfpos k hk; nlinarith
  have htest : ∀ k ≤ K, (‖gradient f (xs k • Chapter02.e₀)‖ ≤ ε ↔ K ≤ k) := fun k hk => by
    rw [hnorm k hk]
    constructor
    · intro h
      by_contra hlt
      have := secondOrderF_gt_half hε (not_le.1 hlt)
      nlinarith
    · intro h
      have hkK : k = K := le_antisymm hk h
      rw [hkK]
      have := secondOrderF_K_le_half hε
      nlinarith
  have hjet : ∀ k ≤ K, jetOracle f 2 (xs k • Chapter02.e₀) = dataJet ε k := fun k hk => by
    rw [jetOracle_ridge hG, Chapter02.inner_e₀_smul, dataJet]
    congr 1
    funext j
    obtain ⟨h0, h1, h2⟩ := hGk k hk
    fin_cases j
    · simpa using h0
    · simpa using h1
    · simpa using h2
  -- the iterates follow the nodes
  have hiter : ∀ k ≤ K, ∀ i ≤ k, M.iterate (jetOracle f 2) i = xs i • Chapter02.e₀ := by
    intro k
    induction k with
    | zero => intro _ i hi; rw [Nat.le_zero.1 hi, M.iterate_zero, hx0']
    | succ k ih =>
      intro hk i hi
      have hx := ih (Nat.le_of_succ_le hk)
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · exact hx i (Nat.lt_succ_iff.1 hi)
      have hkK : k < K := hk
      -- the next iterate is the data iterate
      have hnext : M.iterate (jetOracle f 2) (k + 1) = dataIter M ε (k + 1) := by
        rw [M.iterate_succ]
        simp only [dataIter]
        congr 1
        funext i
        rw [hx i (Nat.lt_succ_iff.1 i.isLt), hjet i (by omega)]
      have hprev : dataIter M ε k = xs k • Chapter02.e₀ := by
        cases k with
        | zero => simp [dataIter, hx0']
        | succ m =>
          rw [← hx (m + 1) le_rfl, M.iterate_succ]
          simp only [dataIter]
          congr 1
          funext i
          rw [hx i (by omega), hjet i (by omega)]
      -- the class condition at iteration `k`
      have hstop : ∀ j ≤ k, ¬ ‖gradient f (M.iterate (jetOracle f 2) j)‖ ≤ ε := fun j hj => by
        rw [hx j hj, htest j (by omega)]; omega
      obtain ⟨lam, r, hstep⟩ := hM k hstop
      rw [hnext, hx k le_rfl] at hstep
      set p := xs k • Chapter02.e₀
      set s := dataIter M ε (k + 1) - p
      set t := ⟪Chapter02.e₀, s⟫
      have hG2 : ContDiff ℝ 2 G := hG
      obtain ⟨hf0k, hf1k, hf2k⟩ := hGk k hkK.le
      have hinner : ⟪Chapter02.e₀, p⟫ = xs k := Chapter02.inner_e₀_smul _
      -- the equation tested against `e₀`
      have heq := hstep.equation Chapter02.e₀
      rw [iteratedFDeriv_ridge_apply hG2 (by norm_num), hgrad, hinner, hf2k, hf1k,
        real_inner_smul_left, real_inner_self_eq_norm_sq, Chapter02.norm_e₀] at heq
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        real_inner_self_eq_norm_sq, Chapter02.norm_e₀] at heq
      -- the curvature and the gradient norm at `x_k`
      have hmin : Chapter01.hessianMinEig f p = secondOrderH ε k := by
        rw [Chapter01.hessianMinEig_def, minCurvature_iteratedFDeriv_ridge_of_forall hG2
          Chapter02.norm_e₀ (fun d => ?_), hinner, hf2k]
        conv_rhs => rw [eq_inner_e₀_smul d]
        rw [norm_smul, Chapter02.norm_e₀, mul_one, Real.norm_eq_abs, sq_abs]
      have hgn : ‖gradient f p‖ = 2 * ε * secondOrderF ε k := hnorm k hkK.le
      have hfk := secondOrderF_gt_half hε hkK
      have hfk1 := secondOrderF_le_one hε k
      have hHpos : 0 < secondOrderH ε k := by unfold secondOrderH; positivity
      have hr2 : (ε ^ (1 / 2 : ℝ)) ^ 2 = ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
      have hsqrt : √‖gradient f p‖ ≤ secondOrderH ε k := by
        have h8 : 1 ≤ 8 * secondOrderF ε k ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num) hfk.le 3
          norm_num at this; linarith
        have hle : 2 * ε * secondOrderF ε k ≤ secondOrderH ε k ^ 2 := by
          rw [secondOrderH, mul_pow, mul_pow, hr2]
          have := mul_le_mul_of_nonneg_left h8
            (by positivity : (0 : ℝ) ≤ 2 * ε * secondOrderF ε k)
          nlinarith
        rw [hgn]
        exact (Real.sqrt_le_sqrt hle).trans (Real.sqrt_sq hHpos.le).le
      have hbound := hstep.bound
      rw [hmin, abs_of_pos hHpos, max_eq_left hsqrt] at hbound
      have hρ : |⟪r, Chapter02.e₀⟫| ≤ κrg * |secondOrderG ε k| := by
        have h1 := abs_real_inner_le_norm r Chapter02.e₀
        rw [Chapter02.norm_e₀, mul_one] at h1
        have h2 := hstep.residual.trans (min_le_left _ _)
        rw [hgn] at h2
        refine h1.trans (h2.trans (le_of_eq ?_))
        rw [secondOrderG, abs_of_neg (by nlinarith)]
        ring
      have hg : secondOrderG ε k < 0 := by unfold secondOrderG; nlinarith
      have hmem := factor_mem hrg1.le hg hHpos hstep.nonneg
        (t := t) (ρ := ⟪r, Chapter02.e₀⟫) (by
          simp only [one_pow, mul_one] at heq
          rw [real_inner_comm s Chapter02.e₀] at heq
          rw [show t = ⟪s, Chapter02.e₀⟫ from real_inner_comm _ _]
          linarith) hρ hbound
      -- the clipping is inactive and the node is the iterate
      have hc : -secondOrderG ε k / secondOrderH ε k = refStep ε k := by
        unfold secondOrderG secondOrderH refStep
        have hf0 := hfpos k hkK.le
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-4 * secondOrderF ε k ^ 2) * hr2
      have hclip : clipFactor a b M ε k = t / refStep ε k := by
        rw [clipFactor, hprev, ← hc, min_eq_right hmem.2, max_eq_right hmem.1]
      have hrefpos : 0 < refStep ε k := by unfold refStep; have := hfpos k hkK.le; positivity
      have hxs : xs (k + 1) = xs k + t := by
        simp only [xs, nodes, sum_range_succ]
        rw [hclip, div_mul_cancel₀ _ hrefpos.ne']
        ring
      have hs' : t • Chapter02.e₀ = s := (eq_inner_e₀_smul s).symm
      rw [hxs, add_smul, hnext, hs']
      exact (add_sub_cancel p _).symm
  have hK := hiter K le_rfl
  rw [show ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ = K from rfl]
  refine ⟨by simp only; rw [hK K le_rfl]; exact (htest K le_rfl).2 le_rfl, fun j hj => ?_⟩
  simp only
  rw [hK j hj.le, htest j hj.le]
  exact not_le.2 hj

end Theorem354

/-! ### Corollary 3.5.5 -/

section RidgeClass

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-- **Steps of class $\mathcal{M}$ on a ridge function**, for Corollary 3.5.5 of
[cartis2022evaluation]. Let $G : \mathbb{R} \to \mathbb{R}$ be $C^2$, let $x \in \mathbb{R}^1$
and $a = \langle e_0, x \rangle$, and let $t \ne 0$, $\lambda \ge 0$ and $\rho \in \mathbb{R}$.
Assume that
$$(G''(a) + \lambda) t = -G'(a) + \rho, \qquad |\rho| \le \min(\kappa_{rg} |G'(a)|, \kappa_{rs}
  t^2),$$
$G''(a) + \lambda \ge 0$ and $G''(a) + \lambda \le \kappa_\lambda \max(|G''(a)|,
|G'(a)|^{1/2})$. Then the step $t e_0$ with multiplier $\lambda$ and residual $\rho e_0$
satisfies (3.5.2)–(3.5.4) for the ridge function $f(x) = G(\langle e_0, x \rangle)$. -/
theorem isMClassStepWith_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (x : EuclideanSpace ℝ (Fin 1))
    {t lam ρ κrg κrs κlam : ℝ} (ht : t ≠ 0) (hlam : 0 ≤ lam)
    (heq : (iteratedDeriv 2 G ⟪e₀, x⟫ + lam) * t = -deriv G ⟪e₀, x⟫ + ρ)
    (hres : |ρ| ≤ min (κrg * |deriv G ⟪e₀, x⟫|) (κrs * t ^ 2))
    (hpsd : 0 ≤ iteratedDeriv 2 G ⟪e₀, x⟫ + lam)
    (hbd : iteratedDeriv 2 G ⟪e₀, x⟫ + lam ≤
      κlam * max |iteratedDeriv 2 G ⟪e₀, x⟫| √|deriv G ⟪e₀, x⟫|) :
    IsMClassStepWith (ridge G e₀) κrg κrs κlam x (t • e₀) lam (ρ • e₀) := by
  have hgrad : gradient (ridge G e₀) x = deriv G ⟪e₀, x⟫ • e₀ :=
    gradient_ridge (hG.differentiable (by norm_num)) x
  have hng : ‖gradient (ridge G e₀) x‖ = |deriv G ⟪e₀, x⟫| := by
    rw [hgrad, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]
  refine ⟨smul_ne_zero ht (by intro h; simpa [h] using norm_e₀), fun v => ?_, ?_, hlam,
    fun d => ?_, ?_⟩
  · rw [iteratedFDeriv_ridge_apply hG (by norm_num), hgrad]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inner_e₀_smul,
      real_inner_smul_left]
    linear_combination ⟪e₀, v⟫ * heq
  · rw [hng, norm_smul, norm_smul, norm_e₀, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs]
    exact hres
  · rw [iteratedFDeriv_ridge_apply_diag hG (by norm_num), ← inner_e₀_sq d]
    nlinarith [sq_nonneg ⟪e₀, d⟫]
  · rw [hessianMinEig_ridge hG, hng]
    exact hbd

end RidgeClass

/-- **Corollary 3.5.5** of [cartis2022evaluation], for AR2 (optimal complexity in $\mathcal{M}$).
For all constants of AR2 there are $f_{\mathrm{low}}$, $L_{f,1} \ge 1$, $L_{f,2} \ge 1$, $B$ and
$\kappa_\lambda > 1$ with the following property. For every $\epsilon_1 \in (0, 1]$, let
$k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$. There are $f : \mathbb{R}^1 \to \mathbb{R}$ that
satisfies Assumption f.Bb with $f_{\mathrm{low}}$, Assumption f.gL with $L_{f,1}$, Assumption
f.HL with $L_{f,2}$ and $|f| \le B$, and an AR2 run with $\epsilon_2 = +\infty$ from $x_0 = 0$,
such that:

* $k_\epsilon$ is the first iteration with $\|\nabla f(x_k)\| \le \epsilon_1$;
* every step $x_{k+1} - x_k$ with $k < k_\epsilon$ is admissible for the class $\mathcal{M}$
  with $\kappa_{rg} = 0$, $\kappa_{rs} = 1$ and $\kappa_\lambda$;
* $f(x_0) - f_{\mathrm{low}} \le 2B$, and
$$k_\epsilon + 1 \le \kappa^S_{\mathrm{AR2}} \left(1 + \frac{|\log \gamma_1|}{\log
  \gamma_2}\right) \frac{2B}{\epsilon_1^{3/2}} + \kappa^C_{\mathrm{AR2}}.$$

So AR2 attains the lower bound of Theorem 3.5.4, and the upper bound of Theorem 3.3.5 for this
run is of the same order $\epsilon_1^{-3/2}$, with constants independent of $\epsilon_1$.

The example is that of Theorem 3.3.6, not the data (3.5.12): the data of Theorem 12.2.15 with
$p = 2$ and $q = 1$, which have zero Hessians at the iterates, and steps that are exact global
minimizers of the model with $\sigma_k = \sigma_0$. In the proof,
$\kappa_\lambda = 1 + \sqrt{\sigma_0 / 2}$ and the multiplier is
$\lambda_k = \sigma_0 \|s_k\| / 2$. The constants are `CartisGouldToint.Chapter03.kappaSAR2` and
`CartisGouldToint.Chapter03.kappaCAR2`. -/
theorem corollary_3_5_5_i (P : AR2Params) :
    ∃ flow L₁ L₂ B κlam : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 1 < κlam ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε none x s σ ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMClassStep f 0 1 κlam (x k) (x (k + 1) - x k)) ∧
          f (x 0) - flow ≤ 2 * B ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (2 * B) /
              ε ^ (3 / 2 : ℝ) + kappaCAR2 P L₂ := by
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  have hσ₀ := P.σ₀_pos
  set κlam := 1 + √(P.σ₀ / 2)
  refine ⟨-B, L₁, L₂, B, κlam, hL₁, hL₂, by
    have := Real.sqrt_pos.2 (half_pos hσ₀); simp only [κlam]; linarith, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hgl, hhl, hB, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := ar2SlowK_pos (q := 1) hε
  set K := ar2SlowK 1 ε
  have htest : ∀ k ≤ K, (stopTest (ridge G Chapter02.e₀) ε none (xr k • Chapter02.e₀) ↔
      K ≤ k) := fun k hk => by
    rw [stopTest_none, gradient_ridge (hG.differentiable (by norm_num)),
      Chapter02.inner_e₀_smul, ← iteratedDeriv_one, (hd k hk).1, norm_smul, Chapter02.norm_e₀,
      mul_one, norm_neg, Real.norm_of_nonneg (ar2SlowAlpha_pos hε hK hk).le]
    exact ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨x, s, σ, hx0', hrun, -, -, hhit, hxk⟩ := exists_ar2_ridge_run P hε hε1
    (ε₂ := none) (fun _ h => absurd h (by simp)) le_rfl (by norm_num) hG
    (fun k hk => ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  have hhit' : IsFirstHit (fun k => ‖gradient (ridge G Chapter02.e₀) (x k)‖ ≤ ε) K := by
    simpa only [stopTest_none] using hhit
  have hf0 : ridge G Chapter02.e₀ (x 0) - -B ≤ 2 * B := by
    linarith [le_abs_self (ridge G Chapter02.e₀ (x 0)), hB (x 0)]
  rw [← ar2SlowK_one]
  refine ⟨ridge G Chapter02.e₀, hb, hgl, hhl, hB, x, s, σ, by rw [hx0', hx0, zero_smul], hrun,
    hhit', fun k hk => ?_, hf0, ?_⟩
  · -- the step is of class `𝓜` with `λ = σ₀ t/2`, `r = 0`
    set α := ar2SlowAlpha ε K k
    have hα : 0 < α := ar2SlowAlpha_pos hε hK hk.le
    set y := α / (P.σ₀ * ((1 - 1).factorial : ℝ) / ((2 : ℕ).factorial : ℝ))
    have hy : y = 2 * α / P.σ₀ := by
      simp only [y]; norm_num [Nat.factorial]; rw [div_div_eq_mul_div, mul_comm]
    set t := xr (k + 1) - xr k
    have ht : t = √y := by
      simp only [t]; rw [hx k hk, Real.sqrt_eq_rpow]; simp only [y, α]; norm_num
    have hy0 : 0 < y := by rw [hy]; positivity
    have ht0 : 0 < t := by rw [ht]; exact Real.sqrt_pos.2 hy0
    have ht2 : t ^ 2 = 2 * α / P.σ₀ := by rw [ht, Real.sq_sqrt hy0.le, hy]
    have hstep : x (k + 1) - x k = t • Chapter02.e₀ := by rw [hxk, hxk, ← sub_smul]
    have hxe : ⟪Chapter02.e₀, x k⟫ = xr k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    obtain ⟨h1, h2⟩ := hd k hk.le
    have hg : deriv G (xr k) = -α := by rw [← iteratedDeriv_one]; exact h1
    have hH : iteratedDeriv 2 G (xr k) = 0 := h2 2 (by norm_num) le_rfl (by norm_num)
    rw [hstep]
    refine ⟨P.σ₀ * t / 2, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht0.ne'
      (lam := P.σ₀ * t / 2) (ρ := 0) (by positivity) ?_ ?_ ?_ ?_⟩
    · rw [hxe, hH, hg]
      have : P.σ₀ * t / 2 * t = α := by
        rw [show P.σ₀ * t / 2 * t = P.σ₀ / 2 * t ^ 2 by ring, ht2]; field_simp
      linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe, hH]; positivity
    · rw [hxe, hH, hg, abs_zero, abs_neg, abs_of_pos hα, zero_add,
        max_eq_right (Real.sqrt_nonneg _)]
      have hsq : P.σ₀ * t / 2 = √(P.σ₀ / 2) * √α := by
        rw [← Real.sqrt_mul (by positivity)]
        refine (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2 ?_ |>.symm
        rw [show P.σ₀ * t / 2 * (P.σ₀ * t / 2) = P.σ₀ ^ 2 / 4 * t ^ 2 by ring, ht2]
        field_simp
        ring
      rw [hsq]
      have := Real.sqrt_nonneg α
      simp only [κlam]
      nlinarith
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_3_5 hb hhl hrun
    rw [hk.unique hhit', funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by
      have := kappaSAR2_pos (P := P) hhl.nonneg
      have := P.ar.log_γ₂_pos
      positivity
    gcongr

/-- **Corollary 3.5.5** of [cartis2022evaluation], for TRε (optimal complexity in $\mathcal{M}$).
There are $f_{\mathrm{low}}$, $L_{f,1} \ge 1$, $L_{f,2} \ge 1$ and $B$ with the following
property. For all TRε constants and every $\epsilon_1 \in (0, 1)$ with
$\sqrt{\epsilon_1} < \Delta_0$, let $k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$. There are
$f : \mathbb{R}^1 \to \mathbb{R}$ that satisfies Assumption f.Bb with $f_{\mathrm{low}}$,
Assumption f.gL with $L_{f,1}$, Assumption f.HL with $L_{f,2}$ and $|f| \le B$, and a TRε run
with $\epsilon_* = \sqrt{\epsilon_1}$ and $\epsilon_2 = +\infty$ from $x_0 = 0$, such that:

* $k_\epsilon$ is the first iteration with $\|\nabla f(x_k)\| \le \epsilon_1$;
* every step $x_{k+1} - x_k$ with $k < k_\epsilon$ is admissible for the class $\mathcal{M}$
  with $\kappa_{rg} = 0$, $\kappa_{rs} = 1$ and $\kappa_\lambda = 2$;
* the upper bound of Theorem 3.4.5 for this run holds in the form
$$k_\epsilon + 1 \le \kappa^A_{\mathrm{TR}\epsilon} \frac{2B}{\epsilon_1^{3/2}} + \frac{|\log
  \epsilon_1|}{2 |\log \gamma_2|} + \kappa^C_{\mathrm{TR}\epsilon}.$$

So the upper bound of Theorem 3.4.5 has the order of the lower bound of Theorem 3.5.4, up to the
logarithmic term.

The condition $\sqrt{\epsilon_1} < \Delta_0$ is the condition $\Delta_0 > \epsilon_*$ of TRε.
The constants $f_{\mathrm{low}}$, $L_{f,1}$, $L_{f,2}$ and $B$ do not depend on the TRε
constants. In the run the steps are interior, the radius is constant, and the multiplier is
$\lambda_k = \epsilon_*$. The run is `CartisGouldToint.Chapter03.tre_slow_example`. -/
theorem corollary_3_5_5_ii :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ (P : TREpsParams) (ε : ℝ), 0 < ε → ε < 1 →
      √ε < P.Δ₀ → ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_1 f P ε none (√ε) x s Δ ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMClassStep f 0 1 2 (x k) (x (k + 1) - x k)) ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaATREps P L₂ * (2 * B) / ε ^ (3 / 2 : ℝ) +
              1 / (2 * |Real.log P.γ₂|) * |Real.log ε| + kappaCTREps P L₂ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := tre_slow_example
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun P ε hε hε1 hΔ => ?_⟩
  obtain ⟨G, X, t, hG, -, hgl, hhl, hB, hdata, x, s, Δ, hx0, hxk, hrun, hhit⟩ :=
    H P ε hε hε1 hΔ
  set f := ridge G Chapter02.e₀
  have hb : Chapter02.AssumptionBb f (-B) := fun y => by linarith [neg_abs_le (f y), hB y]
  refine ⟨f, hb, hgl, hhl, hB, x, s, Δ, hx0, hrun, hhit, fun k hk => ?_, ?_⟩
  · obtain ⟨hXs, ht, hH, hstat⟩ := hdata k hk
    have hxe : ⟪Chapter02.e₀, x k⟫ = X k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    have hr := Real.sqrt_pos.2 hε
    rw [show x (k + 1) - x k = t k • Chapter02.e₀ by
      rw [hxk, hxk, hXs, add_smul, add_sub_cancel_left]]
    refine ⟨√ε, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht.ne' (lam := √ε)
      (ρ := 0) hr.le ?_ ?_ ?_ ?_⟩
    · rw [hxe]; linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe]; linarith
    · rw [hxe, abs_of_pos (hr.trans_le hH)]
      have := le_max_left (iteratedDeriv 2 G (X k)) √|deriv G (X k)|
      linarith
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_4_5 hb hhl hrun
    rw [hk.unique hhit, funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaATREps P L₂ := by
      have := kappaDeltaF_pos P hhl.pos
      have := Real.log_nonneg P.one_le_γ₃
      unfold kappaATREps kappaSTREps
      positivity
    have hf0 : f (x 0) - -B ≤ 2 * B := by linarith [le_abs_self (f (x 0)), hB (x 0)]
    gcongr

/-- **Corollary 3.5.5** of [cartis2022evaluation], for iRN (optimal complexity in $\mathcal{M}$).
For all iRN constants there are $f_{\mathrm{low}}$, $L_{f,1} \ge 1$, $L_{f,2} \ge 1$ and $B$
with the following property. For every $\epsilon_1 \in (0, 1)$, let
$k_\epsilon = \lceil \epsilon_1^{-3/2} \rceil$. There are $f : \mathbb{R}^1 \to \mathbb{R}$ that
satisfies Assumption f.Bb with $f_{\mathrm{low}}$, Assumption f.gL with $L_{f,1}$, Assumption
f.HL with $L_{f,2}$ and $|f| \le B$, and an iRN run with $\epsilon_2 = +\infty$ and $Q_k = I$
from $x_0 = 0$, such that:

* $k_\epsilon$ is the first iteration with $\|\nabla f(x_k)\| \le \epsilon_1$;
* every step $x_{k+1} - x_k$ with $k < k_\epsilon$ is admissible for the class $\mathcal{M}$
  with $\kappa_{rg} = 0$, $\kappa_{rs} = 1$ and $\kappa_\lambda = 2 + \sigma^U_0$;
* the upper bound of Theorem 3.4.11 for this run holds in the form
$$k_\epsilon + 1 \le \kappa^A_{\mathrm{iRN}} \frac{2B}{\epsilon_1^{3/2}} +
  \kappa^B_{\mathrm{iRN}}.$$

**Correction.** The proof sketch of the source applies iRN to the data (3.5.12). The ratio
(3.4.35) of iRN is not scale invariant. On the data (3.5.12) it is
$4 f_k^3 / \theta_k^3 \ge 1/2$, which can be below $\eta$ when $\eta > 1/2$. The example is
therefore $c G(x / c)$ with $c = \min(1, (2 \eta)^{-1/2})$. This leaves the gradients at the
iterates, and hence the termination index, unchanged, and it makes the ratio at least
$1 / (2 c^2) \ge \eta$. The proof sketch of the source omits this rescaling.

In the run the multiplier is $\lambda_k = \sigma^U_0 \|s_k\|$. The run is
`CartisGouldToint.Chapter03.irn_slow_example`, and the constants are the corrected constants
`CartisGouldToint.Chapter03.kappaAIRN` and `CartisGouldToint.Chapter03.kappaBIRN`. -/
theorem corollary_3_5_5_iii (P : IRNParams) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (lam σL σU : ℕ → ℝ), x 0 = 0 ∧
          algorithm_3_4_2 f P ε none x s lam σL σU (fun _ => ⊤) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊,
            IsMClassStep f 0 1 (2 + P.σU₀) (x k) (x (k + 1) - x k)) ∧
          ((⌈ε ^ (-(3 / 2 : ℝ))⌉₊ + 1 : ℕ) : ℝ) ≤
            kappaAIRN P L₂ * (2 * B) / ε ^ (3 / 2 : ℝ) + kappaBIRN P L₂ := by
  obtain ⟨flow, L₁, L₂, B, hL₁, hL₂, H⟩ := irn_slow_example P
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 => ?_⟩
  obtain ⟨G, X, t, hG, -, hgl, hhl, hB, hdata, x, s, lam, σL, σU, hx0, hxk, -, hrun, hhit⟩ :=
    H ε hε hε1
  set f := ridge G Chapter02.e₀
  have hσ : 0 < P.σU₀ := P.σmin_pos.trans_le P.σmin_le_σU₀
  have hb : Chapter02.AssumptionBb f (-B) := fun y => by linarith [neg_abs_le (f y), hB y]
  refine ⟨f, hb, hgl, hhl, hB, x, s, lam, σL, σU, hx0, hrun, hhit, fun k hk => ?_, ?_⟩
  · obtain ⟨hXs, ht, hH, hstat⟩ := hdata k hk
    have hxe : ⟪Chapter02.e₀, x k⟫ = X k := by rw [hxk]; exact Chapter02.inner_e₀_smul _
    rw [show x (k + 1) - x k = t k • Chapter02.e₀ by
      rw [hxk, hxk, hXs, add_smul, add_sub_cancel_left]]
    refine ⟨P.σU₀ * t k, (0 : ℝ) • Chapter02.e₀, isMClassStepWith_ridge hG (x k) ht.ne'
      (lam := P.σU₀ * t k) (ρ := 0) (by positivity) ?_ ?_ ?_ ?_⟩
    · rw [hxe]; linarith
    · rw [abs_zero]; exact le_min (by simp) (by positivity)
    · rw [hxe]; nlinarith
    · rw [hxe, abs_of_pos (ht.trans_le hH)]
      have := le_max_left (iteratedDeriv 2 G (X k)) √|deriv G (X k)|
      nlinarith [mul_le_mul_of_nonneg_left hH hσ.le]
  · obtain ⟨kε, hk, hF, -⟩ := theorem_3_4_11 hb hhl hrun
    rw [hk.unique hhit, funEvalCount_eq] at hF
    refine hF.trans ?_
    have hA : 0 ≤ kappaAIRN P L₂ := by
      have hC : 0 < L₂ + 4 * sigmaUMax P L₂ + 2 * P.κ₃ := by
        linarith [hhl.nonneg, sigmaUMax_pos P L₂, P.κ₃_pos]
      have := Real.rpow_pos_of_pos hC (3 / 2 : ℝ)
      have := P.η_pos
      have := one_le_irnUnsuccBound P L₂
      unfold kappaAIRN kappaSIRN
      have : 0 ≤ irnUnsuccBound P L₂ + 1 := by linarith
      positivity
    have hf0 : f (x 0) - -B ≤ 2 * B := by linarith [le_abs_self (f (x 0)), hB (x 0)]
    gcongr

end CartisGouldToint.Chapter03
