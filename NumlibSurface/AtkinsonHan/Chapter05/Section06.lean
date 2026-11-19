/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.PSeries
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Subspace
import Numlib.Projection.Optimality

/-!
# Atkinson and Han, Section 5.6: Conjugate Gradient Method for Operator Equations

This module formalizes Section 5.6 of [han2009theoretical]: the conjugate gradient method for an
equation $Au = f$ in a real Hilbert space $V$, its linear convergence rate (5.6.4), the Chebyshev
rate (5.6.5), and the superlinear convergence of Theorem 5.6.2 for an equation of the second kind,
due to [winther1980some]. Throughout, $A \in \mathcal{L}(V)$ is self-adjoint and positive definite
in the sense of (5.6.3):
$$\sqrt{m}\, \|v\| \le \|v\|_A \le \sqrt{M}\, \|v\| \quad \text{for all } v \in V, \qquad m > 0,$$
where $(v, u)_A = (Av, u)$ and $\|v\|_A = \sqrt{(v, v)_A}$. The proofs specialize the backbone
modules `Numlib.Krylov.CG`, `Numlib.Krylov.Convergence.CG`, `Numlib.Krylov.Convergence.Superlinear`,
`Numlib.Analysis.InnerProductSpace.Energy` and `Numlib.Analysis.InnerProductSpace.Coercive`.

## Main definitions

* Section 5.6, `AtkinsonHan.Chapter05.innerA` and `AtkinsonHan.Chapter05.normA`: the $A$-inner
  product $(v, u)_A = (Av, u)$ and the $A$-norm $\|v\|_A$.
* Equation (5.6.2), `AtkinsonHan.Chapter05.CGState`, `AtkinsonHan.Chapter05.cgStep` and
  `AtkinsonHan.Chapter05.cg`: the conjugate gradient iteration, with the residual
  $r_{k+1} = f - Au_{k+1}$.
* Theorem 5.6.3, `AtkinsonHan.Chapter05.tau`: the average $\tau_\ell = \ell^{-1} \sum_{j < \ell}
  |\lambda_j| / (1 - \lambda_j)$.

## Main results

* Equation (5.6.3), `AtkinsonHan.Chapter05.isSymmetricBoundedBy_of_bound`: the condition (5.6.3)
  gives the bounds $m \|v\|^2 \le (Av, v) \le M \|v\|^2$.
* Section 5.6, `AtkinsonHan.Chapter05.existsUnique_solution`: $Au = f$ has a unique solution, and
  $\|A^{-1}\| \le 1/m$.
* Equation (5.6.4), `AtkinsonHan.Chapter05.equation_5_6_4`: each step contracts the $A$-norm of the
  error by the factor $(M - m)/(M + m)$.
* Theorem 5.6.1, `AtkinsonHan.Chapter05.theorem_5_6_1`: the iterates converge to the solution at the
  linear rate (5.6.4).
* Equation (5.6.5), `AtkinsonHan.Chapter05.equation_5_6_5`: the Chebyshev bound with the rate
  $(\sqrt M - \sqrt m)/(\sqrt M + \sqrt m)$.
* Equation (5.6.6) (Exercise 5.6.1), `AtkinsonHan.Chapter05.equation_5_6_6`: the rate of (5.6.5) is
  at least as good as the rate of (5.6.4).
* Equations (5.6.7)–(5.6.9), `AtkinsonHan.Chapter05.isSymmetricBoundedBy_of_one_sub`: for
  $A = I - K$ with $\delta \le 1 - \lambda_j \le \Delta$, the condition (5.6.3) holds with
  $m = \delta$ and $M = \Delta$.
* Equation (5.6.8), `AtkinsonHan.Chapter05.equation_5_6_8`: $A = I - K$ is positive definite if and
  only if $\delta > 0$.
* Equation (5.6.9), `AtkinsonHan.Chapter05.equation_5_6_9`: $\|A\| = \Delta$ and
  $\|A^{-1}\| = 1/\delta$.
* Equation (5.6.10), `AtkinsonHan.Chapter05.equation_5_6_10`: the linear rate for $A = I - K$ is
  $(\Delta - \delta)/(\Delta + \delta)$.
* Theorem 5.6.2, `AtkinsonHan.Chapter05.theorem_5_6_2`: superlinear convergence of the conjugate
  gradient method for $A = I - K$.
* Theorem 5.6.3(a), `AtkinsonHan.Chapter05.theorem_5_6_3_a`: $\tau_\ell = O(\ell^{-1/2})$ for a
  Hilbert–Schmidt operator $K$.
* Theorem 5.6.3(b), `AtkinsonHan.Chapter05.theorem_5_6_3_b`: $\tau_\ell = O(\ell^{-1})$ when the
  eigenvalues decay like $j^{-(p + 1/2)}$.
* Section 5.6, closing remark, `AtkinsonHan.Chapter05.normA_error_min`: $u_k$ minimizes the $A$-norm
  of the error over $u_0 + \mathcal{K}_k$.

## Implementation notes

* `AtkinsonHan.Chapter05.innerA` and `AtkinsonHan.Chapter05.normA` are the backbone's `energyInner`
  and `energyNorm`, by `AtkinsonHan.Chapter05.innerA_eq` and `AtkinsonHan.Chapter05.normA_eq`. The
  condition (5.6.3) is the backbone's `LinearMap.IsSymmetricBoundedBy`, which every Chebyshev-type
  estimate takes as its hypothesis.
* The book's iteration `AtkinsonHan.Chapter05.cg` is the backbone's `CG.iterate`, by
  `AtkinsonHan.Chapter05.cg_eq_CG_iterate`. The backbone computes the residual by the recurrence
  $r_{k+1} = r_k - \alpha_k A s_k$ instead.
* `AtkinsonHan.Chapter05.cg_energyNorm_error_step_le` is not a statement of the book. It is the
  contraction of one step by the Kantorovich factor, in the backbone's terms, which this section and
  Section 9.4 both specialize.
* In Theorem 5.6.2 the compact self-adjoint operator $K$ is given by its eigen-decomposition: a
  Hilbert basis $\{\varphi_j\}$ of eigenvectors with eigenvalues $\lambda_j$, such that
  $|\lambda_j|$ decreases and $\lambda_j \to 0$.
* The rate in Theorem 5.6.2 is the backbone's `Krylov.wintherRate`, which
  `AtkinsonHan.Chapter05.wintherRate_eq_tau` writes with `AtkinsonHan.Chapter05.tau`.
* The eigenvalues are indexed from $0$, and the book indexes them from $1$: the book's $\lambda_j$
  is `lam (j - 1)`.

## Deviations from the source

* **Solvability of (5.6.1)** (scope). The theorem uses a uniform positive lower bound for
  the energy norm and gives a corresponding inverse norm bound. Pointwise positive
  definiteness alone does not imply bounded invertibility in infinite dimensions.
* **Equation (5.6.2)** (scope). The quotients are totalized with zero inverses, so after
  an exact zero residual the iterate stays fixed. The basic convergence results use
  arbitrary real Hilbert spaces, without the source's standing separability assumption.
* **Equations (5.6.8)–(5.6.10)** (scope). An explicit eigenbasis and bounds or defining
  inequalities for the spectral endpoints replace the derivation from compactness.
  The lower endpoint test uses uniform coercivity. The norm identity takes a supplied
  inverse, and the one-step estimate uses any valid positive lower and upper bounds.
* **Theorem 5.6.2** (generalization). The book's rate has the factor $(\Delta/\delta)^{3/(2k)}$; the
  statement proves the rate with the smaller factor $(\Delta/\delta)^{1/(2k)}$, which has the same
  limit $0$. See `AtkinsonHan.Chapter05.theorem_5_6_2`.
* **Theorem 5.6.3** (scope). The integral kernel assumptions are represented by a sum of
  squared eigenvalues in part (a) and an explicit eigenvalue decay bound in part (b).
  Part (b) allows real $p \ge 1$.

## Not formalized

* **Equations (5.6.7)–(5.6.9), the eigen-decomposition of $K$.** The Hilbert basis of eigenvectors
  is a hypothesis and is not derived from the compactness of $K$. Mathlib has the spectral theorem
  for compact self-adjoint operators, but no enumeration of their eigenvalues as a decreasing
  sequence indexed by $\mathbb{N}$, which (5.6.8) needs.
* **Theorem 5.6.3(a), the identity $\sum_j \lambda_j^2 = \|K\|_{HS}^2$.** It is a hypothesis. The
  identity is Theorem 2.8.15 of the book, and Mathlib has no Hilbert–Schmidt norm for the integral
  operators on $C([a, b] \times [a, b])$.
* **Theorem 5.6.3(b), the eigenvalue decay $|\lambda_j| \le M j^{-(p + 1/2)}$ for a symmetric kernel
  of class $C^p$.** It is a hypothesis. The book quotes it from Fenyő and Stolle, and Mathlib has no
  eigenvalue asymptotics for smooth kernels.
-/

open Filter Topology

namespace AtkinsonHan.Chapter05

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Energy

/-- The $A$-inner product of Section 5.6 of [han2009theoretical]: for $A \in \mathcal{L}(V)$,
$(v, u)_A = (Av, u)$.

**Reading.** Same bilinear form is defined for arbitrary bounded linear operator.
-/
noncomputable def innerA (A : V →L[ℝ] V) (v u : V) : ℝ := inner ℝ (A v) u

/-- The $A$-norm of Section 5.6 of [han2009theoretical]: $\|v\|_A = \sqrt{(v, v)_A}$.

**Reading.** Same square-root formula is defined for arbitrary bounded linear operator.
-/
noncomputable def normA (A : V →L[ℝ] V) (v : V) : ℝ := Real.sqrt (innerA A v v)

/-- The $A$-inner product is the backbone's energy inner product: $(v, u)_A$ is `energyInner A v u`.
-/
theorem innerA_eq (A : V →L[ℝ] V) (v u : V) :
    innerA A v u = energyInner (A : V →ₗ[ℝ] V) v u := rfl

/-- The $A$-norm is the backbone's energy norm: $\|v\|_A$ is `energyNorm A v`. -/
theorem normA_eq (A : V →L[ℝ] V) (v : V) : normA A v = energyNorm (A : V →ₗ[ℝ] V) v := rfl

/-- The $A$-norm is nonnegative: $\|v\|_A \ge 0$. -/
theorem normA_nonneg (A : V →L[ℝ] V) (v : V) : 0 ≤ normA A v := Real.sqrt_nonneg _

end Energy

section PositiveDefinite

variable [CompleteSpace V]

/-- **Equation (5.6.3)** of [han2009theoretical] as bounds on the quadratic form. Let $V$ be a real
Hilbert space and $A \in \mathcal{L}(V)$ self-adjoint, and let $m > 0$ and $\sqrt{m}\, \|v\| \le
\|v\|_A \le \sqrt{M}\, \|v\|$ for all $v$. Then $A$ is symmetric and
$$m \|v\|^2 \le (Av, v) \le M \|v\|^2 \quad \text{for all } v \in V.$$

The conclusion is the backbone's `LinearMap.IsSymmetricBoundedBy A m M`, the hypothesis of every
Chebyshev-type estimate. -/
theorem isSymmetricBoundedBy_of_bound {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ}
    (hm : 0 < m) (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖) :
    (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M := by
  have hsym : (A : V →ₗ[ℝ] V).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hinner : ∀ x : V, 0 ≤ inner ℝ (A x) x := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    by_contra hneg
    push Not at hneg
    have hzero : normA A x = 0 := Real.sqrt_eq_zero_of_nonpos hneg.le
    have h1 := (hbound x).1
    rw [hzero] at h1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    nlinarith
  have hsq : ∀ x : V, normA A x ^ 2 = inner ℝ (A x) x := fun x => Real.sq_sqrt (hinner x)
  refine ⟨hsym, fun x => ?_, fun x => ?_⟩
  · have h1 := (hbound x).1
    have h2 : (Real.sqrt m * ‖x‖) ^ 2 ≤ normA A x ^ 2 := by
      have hnn : 0 ≤ Real.sqrt m * ‖x‖ := by positivity
      nlinarith [normA_nonneg A x]
    rw [mul_pow, Real.sq_sqrt hm.le, hsq] at h2
    simpa [RCLike.re_to_real] using h2
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hlow := (hbound x).1
    have h1 := (hbound x).2
    have hMpos : 0 < Real.sqrt M := by nlinarith
    have hM : 0 ≤ M := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at hMpos
      exact lt_irrefl 0 hMpos
    have h2 : normA A x ^ 2 ≤ (Real.sqrt M * ‖x‖) ^ 2 := by
      nlinarith [normA_nonneg A x]
    rw [hsq, mul_pow, Real.sq_sqrt hM] at h2
    simpa [RCLike.re_to_real] using h2

/-- **Section 5.6** of [han2009theoretical], the setting. Let $V$ be a real Hilbert space,
$A \in \mathcal{L}(V)$ self-adjoint, $m > 0$, and $\sqrt{m}\, \|v\| \le \|v\|_A \le \sqrt{M}\,
\|v\|$ for all $v$. Then for every $f \in V$ the equation $Au = f$ has exactly one solution
$u \in V$, and $A$ is invertible with $\|A^{-1}\| \le 1/m$.

The book derives this from Theorem 5.1.4. Here it is the backbone's
`ContinuousLinearMap.exists_equiv_of_isCoerciveWith`.

**Reading.** Uses uniform positive lower bound and adds quantitative inverse bound.
-/
theorem existsUnique_solution {A : V →L[ℝ] V} (hA : IsSelfAdjoint A) {m M : ℝ} (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖) :
    (∀ f : V, ∃! u, A u = f) ∧
      ∃ e : V ≃L[ℝ] V, (e : V →L[ℝ] V) = A ∧ ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 / m := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  obtain ⟨e, he, hnorm⟩ :=
    ContinuousLinearMap.exists_equiv_of_isCoerciveWith hm hA'.isCoerciveWith
  refine ⟨fun f => ⟨e.symm f, ?_, fun u hu => ?_⟩, ⟨e, he, hnorm⟩⟩
  · rw [← he]
    exact e.apply_symm_apply f
  · rw [← hu, ← he]
    exact (e.symm_apply_apply u).symm

end PositiveDefinite

section Iteration

/-- **Equation (5.6.2)** of [han2009theoretical], the state of the iteration. A state is a triple
$(u_k, r_k, s_k)$ of elements of $V$: the iterate, the residual and the search direction. -/
@[ext]
structure CGState (V : Type*) where
  /-- The iterate $u_k$. -/
  u : V
  /-- The residual $r_k = f - Au_k$. -/
  r : V
  /-- The search direction $s_k$. -/
  s : V

/-- **Equation (5.6.2)** of [han2009theoretical], one step of the conjugate gradient method. From
the state $(u_k, r_k, s_k)$ the step computes
$$\alpha_k = \frac{\|r_k\|^2}{(As_k, s_k)}, \quad u_{k+1} = u_k + \alpha_k s_k, \quad r_{k+1} =
  f - Au_{k+1}, \quad \beta_k = \frac{\|r_{k+1}\|^2}{\|r_k\|^2}, \quad s_{k+1} = r_{k+1} +
  \beta_k s_k.$$

Division by $0$ gives $0$ in Lean, so the step is defined for every state. After breakdown, when
$r_k = 0$, both $\alpha_k$ and $\beta_k$ are $0$ and the iterate does not change. The backbone
uses the same convention.

**Reading.** The same recurrence uses totalized denominators and is defined for arbitrary states.
-/
noncomputable def cgStep (A : V →L[ℝ] V) (f : V) (st : CGState V) : CGState V :=
  let α := ‖st.r‖ ^ 2 / inner ℝ (A st.s) st.s
  let u' := st.u + α • st.s
  let r' := f - A u'
  let β := ‖r'‖ ^ 2 / ‖st.r‖ ^ 2
  ⟨u', r', r' + β • st.s⟩

/-- **Equation (5.6.2)** of [han2009theoretical], the iteration. The $k$-th state of the conjugate
gradient method for $Au = f$ is obtained by $k$ steps from $(u_0, r_0, s_0)$ with
$r_0 = s_0 = f - Au_0$.

**Reading.** Repeats the totalized recurrence from the source initialization.
-/
noncomputable def cg (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) : CGState V :=
  (cgStep A f)^[k] ⟨u₀, f - A u₀, f - A u₀⟩

/-- The conjugate gradient iteration starts at $u_0$ with $r_0 = s_0 = f - Au_0$. -/
theorem cg_zero (A : V →L[ℝ] V) (f u₀ : V) :
    cg A f u₀ 0 = ⟨u₀, f - A u₀, f - A u₀⟩ := rfl

/-- Each state of the conjugate gradient iteration is one step after the previous state.

**Reading.** Recurrence identity includes states after a zero denominator.
-/
theorem cg_succ (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    cg A f u₀ (k + 1) = cgStep A f (cg A f u₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The state $(u_k, r_k, s_k)$ of the book that corresponds to a state $(x, r, p)$ of the
backbone's iteration `CG.State`. -/
def ofCGState (s : CG.State V) : CGState V := ⟨s.x, s.r, s.p⟩

/-- One step of the book's iteration agrees with one step of the backbone's, when the incoming state
has the residual $r = f - Ax$. -/
private theorem cgStep_ofCGState (A : V →L[ℝ] V) (f : V) {s : CG.State V}
    (hres : s.r = f - A s.x) :
    cgStep A f (ofCGState s) = ofCGState (CG.step (A : V →ₗ[ℝ] V) s) := by
  have hcoe : (A : V →ₗ[ℝ] V) s.p = A s.p := rfl
  have hα : ‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p = CG.alpha (A : V →ₗ[ℝ] V) s := by
    rw [CG.alpha, real_inner_self_eq_norm_sq, hcoe]
  have hu : (cgStep A f (ofCGState s)).u = (ofCGState (CG.step (A : V →ₗ[ℝ] V) s)).u := by
    change s.x + (‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).x
    rw [CG.step_x, hα]
  have hr : (cgStep A f (ofCGState s)).r = (ofCGState (CG.step (A : V →ₗ[ℝ] V) s)).r := by
    change f - A (s.x + (‖s.r‖ ^ 2 / inner ℝ (A s.p) s.p) • s.p)
      = (CG.step (A : V →ₗ[ℝ] V) s).r
    rw [CG.step_r, hα, hres, map_add, map_smul, hcoe]
    abel
  refine CGState.ext hu hr ?_
  change (cgStep A f (ofCGState s)).r
      + (‖(cgStep A f (ofCGState s)).r‖ ^ 2 / ‖s.r‖ ^ 2) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).p
  rw [hr]
  change (CG.step (A : V →ₗ[ℝ] V) s).r
      + (‖(CG.step (A : V →ₗ[ℝ] V) s).r‖ ^ 2 / ‖s.r‖ ^ 2) • s.p = (CG.step (A : V →ₗ[ℝ] V) s).p
  rw [CG.step_p, CG.beta, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The book's iteration (5.6.2) is the backbone's `CG.iterate`: for every $k$, the $k$-th state of
`AtkinsonHan.Chapter05.cg` corresponds to the $k$-th state of `CG.iterate`.

The backbone computes the residual by the recurrence $r_{k+1} = r_k - \alpha_k A s_k$, and the
book by $r_{k+1} = f - Au_{k+1}$. -/
theorem cg_eq_CG_iterate (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    cg A f u₀ k = ofCGState (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cg_succ, ih, CG.iterate_succ,
      cgStep_ofCGState A f (CG.residual_eq (A : V →ₗ[ℝ] V) f u₀ k)]

/-- The book's iterate $u_k$ is the iterate $x_k$ of the backbone's `CG.iterate`. -/
theorem cg_u (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).u = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).x := by
  rw [cg_eq_CG_iterate]
  rfl

/-- The book's residual $r_k$ is the residual of the backbone's `CG.iterate`. -/
theorem cg_r (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).r = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).r := by
  rw [cg_eq_CG_iterate]
  rfl

/-- The book's search direction $s_k$ is the search direction $p_k$ of the backbone's `CG.iterate`.
-/
theorem cg_s (A : V →L[ℝ] V) (f u₀ : V) (k : ℕ) :
    (cg A f u₀ k).s = (CG.iterate (A : V →ₗ[ℝ] V) f u₀ k).p := by
  rw [cg_eq_CG_iterate]
  rfl

end Iteration

section KantorovichStep

/-- One conjugate gradient step contracts the energy norm of the error by the Kantorovich factor.
Let $A$ be symmetric with $\lambda_{\min} \|x\|^2 \le (Ax, x) \le \lambda_{\max} \|x\|^2$ for
all $x$ and $\lambda_{\min} > 0$, and let $Ax^* = b$. Then the iterates $x_k$ of the backbone's
`CG.iterate` satisfy
$$\|x^* - x_{k+1}\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} +
  \lambda_{\min}} \|x^* - x_k\|_A.$$

This is stated in the backbone's terms because both `AtkinsonHan.Chapter05.equation_5_6_4` and
`AtkinsonHan.Chapter09.cg_energy_rate` specialize it. One conjugate gradient step is at least as
good as one steepest descent step: the proof combines `IsGalerkin.energyNorm_le` (the conjugate
gradient iterate is optimal in the energy norm over $x_0 + \mathcal{K}_{k+1}$) with the
Kantorovich bound `Krylov.IsGalerkinIterate.energyNorm_error_succ_le` for one steepest descent
step.

**Reading.** Uses quadratic form hypotheses and does not require separability.
-/
theorem cg_energyNorm_error_step_le {A : V →ₗ[ℝ] V} {b x₀ xstar : V} {lmin lmax : ℝ}
    (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax) (hstar : A xstar = b) (k : ℕ) :
    energyNorm A (xstar - (CG.iterate A b x₀ (k + 1)).x)
      ≤ (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - (CG.iterate A b x₀ k).x) :=
  have hAc := hA.isSymmetricCoercive hl
  Krylov.IsGalerkinIterate.energyNorm_error_succ_le hl hA (CG.isGalerkinIterate b x₀ hAc k)
    (CG.isGalerkinIterate b x₀ hAc (k + 1)) hstar

end KantorovichStep

section Convergence

variable [CompleteSpace V] {A : V →L[ℝ] V} {m M : ℝ} {f u₀ ustar : V}

set_option linter.unusedSectionVars false in
/-- **Equation (5.6.6)** of [han2009theoretical] (Exercise 5.6.1). For $0 < m \le M$, the rate of
(5.6.5) is at least as good as the rate of (5.6.4):
$$\frac{\sqrt M - \sqrt m}{\sqrt M + \sqrt m} \le \frac{M - m}{M + m}.$$
-/
theorem equation_5_6_6 (hm : 0 < m) (hmM : m ≤ M) :
    (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) ≤ (M - m) / (M + m) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ m = s ^ 2 :=
    ⟨Real.sqrt m, Real.sqrt_pos.2 hm, (Real.sq_sqrt hm.le).symm⟩
  obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 < t ∧ M = t ^ 2 :=
    ⟨Real.sqrt M, Real.sqrt_pos.2 hM, (Real.sq_sqrt hM.le).symm⟩
  rw [Real.sqrt_sq hs0.le, Real.sqrt_sq ht0.le,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hst : s ≤ t := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hst) (mul_pos hs0 ht0).le]

/-- **Section 5.6** of [han2009theoretical], closing remark. Let $V$ be a real Hilbert space,
$A \in \mathcal{L}(V)$ self-adjoint, $m > 0$, $\sqrt{m}\, \|v\| \le \|v\|_A \le \sqrt{M}\,
\|v\|$ for all $v$, and $Au^* = f$. Then the conjugate gradient iterate $u_k$ minimizes the
$A$-norm of the error over the affine Krylov space $u_0 + \mathcal{K}_k(A, r_0)$: for every $y$
with $y - u_0 \in \mathcal{K}_k(A, r_0)$,
$$\|u^* - u_k\|_A \le \|u^* - y\|_A.$$

The Krylov space is `Krylov.subspace A (f - A u₀) k`. The proof is the backbone's
`IsGalerkin.energyNorm_le` with `CG.isGalerkinIterate`. -/
theorem normA_error_min (hA : IsSelfAdjoint A) (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) {y : V}
    (hy : y - u₀ ∈ Krylov.subspace (A : V →ₗ[ℝ] V) (f - A u₀) k) :
    normA A (ustar - (cg A f u₀ k).u) ≤ normA A (ustar - y) := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  have hAc := hA'.isSymmetricCoercive hm
  rw [cg_u, normA_eq, normA_eq]
  exact (CG.isGalerkinIterate f u₀ hAc k).energyNorm_le hAc hstar hy

/-- **Equation (5.6.4)** of [han2009theoretical]. Let $V$ be a real Hilbert space,
$A \in \mathcal{L}(V)$ self-adjoint, $m > 0$, $\sqrt{m}\, \|v\| \le \|v\|_A \le \sqrt{M}\,
\|v\|$ for all $v$, and $Au^* = f$. Then for every $k$ the conjugate gradient iterates satisfy
$$\|u^* - u_{k+1}\|_A \le \frac{M - m}{M + m} \|u^* - u_k\|_A.$$

This is `AtkinsonHan.Chapter05.cg_energyNorm_error_step_le`, read through the identification
`AtkinsonHan.Chapter05.cg_u` of the book's iteration with the backbone's.

**Reading.** Same one-step bound on arbitrary real Hilbert spaces.
-/
theorem equation_5_6_4 (hA : IsSelfAdjoint A) (hm : 0 < m)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ (k + 1)).u)
      ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u) := by
  rw [cg_u, cg_u, normA_eq, normA_eq]
  exact cg_energyNorm_error_step_le hm (isSymmetricBoundedBy_of_bound hA hm hbound) hstar k

/-- **Theorem 5.6.1** of [han2009theoretical]. Let $V$ be a real Hilbert space,
$A \in \mathcal{L}(V)$ self-adjoint, $m > 0$, $M > 0$, $\sqrt{m}\, \|v\| \le \|v\|_A \le
\sqrt{M}\, \|v\|$ for all $v$, and $Au^* = f$. Then the conjugate gradient iterates $u_k$
converge to $u^*$, and for every $k$
$$\|u^* - u_{k+1}\|_A \le \frac{M - m}{M + m} \|u^* - u_k\|_A.$$

**Reading.** Same convergence and rate without separability, given a solution.
-/
theorem theorem_5_6_1 (hA : IsSelfAdjoint A) (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) :
    Tendsto (fun k => (cg A f u₀ k).u) atTop (𝓝 ustar) ∧
      ∀ k, normA A (ustar - (cg A f u₀ (k + 1)).u)
        ≤ (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u) := by
  refine ⟨?_, fun k => equation_5_6_4 hA hm hbound hstar k⟩
  obtain ⟨ρ, hρ0, hρ1, hρle⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (M - m) / (M + m) ≤ ρ := by
    refine ⟨max ((M - m) / (M + m)) 0, le_max_right _ _, max_lt ?_ one_pos, le_max_left _ _⟩
    rw [div_lt_one (by linarith)]
    linarith
  have hgeom : ∀ k, normA A (ustar - (cg A f u₀ k).u) ≤ ρ ^ k * normA A (ustar - u₀) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_mul]
      exact le_of_eq rfl
    | succ k ih =>
      have h1 := equation_5_6_4 (u₀ := u₀) hA hm hbound hstar k
      have h2 : (M - m) / (M + m) * normA A (ustar - (cg A f u₀ k).u)
          ≤ ρ * normA A (ustar - (cg A f u₀ k).u) :=
        mul_le_mul_of_nonneg_right hρle (normA_nonneg _ _)
      calc normA A (ustar - (cg A f u₀ (k + 1)).u)
          ≤ ρ * normA A (ustar - (cg A f u₀ k).u) := h1.trans h2
        _ ≤ ρ * (ρ ^ k * normA A (ustar - u₀)) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * normA A (ustar - u₀) := by ring
  have hmpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hbnd : ∀ k, ‖(cg A f u₀ k).u - ustar‖ ≤ ρ ^ k * normA A (ustar - u₀) / Real.sqrt m := by
    intro k
    rw [le_div_iff₀ hmpos, ← norm_neg, neg_sub]
    calc ‖ustar - (cg A f u₀ k).u‖ * Real.sqrt m
        = Real.sqrt m * ‖ustar - (cg A f u₀ k).u‖ := mul_comm _ _
      _ ≤ normA A (ustar - (cg A f u₀ k).u) := (hbound _).1
      _ ≤ ρ ^ k * normA A (ustar - u₀) := hgeom k
  have hlim : Tendsto (fun k : ℕ => ρ ^ k * normA A (ustar - u₀) / Real.sqrt m) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const
      (normA A (ustar - u₀) / Real.sqrt m)
    simpa [mul_div_assoc] using h
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun k => norm_nonneg _) hbnd hlim)

/-- **Equation (5.6.5)** of [han2009theoretical] (Chebyshev bound). Let $V$ be a real Hilbert space,
$A \in \mathcal{L}(V)$ self-adjoint, $0 < m \le M$, $\sqrt{m}\, \|v\| \le \|v\|_A \le \sqrt{M}\,
\|v\|$ for all $v$, and $Au^* = f$. Then for every $k$
$$\|u^* - u_k\|_A \le 2 \left( \frac{\sqrt M - \sqrt m}{\sqrt M + \sqrt m} \right)^k \|u^* -
  u_0\|_A.$$

The book quotes this bound from Patterson, *Iterative Methods for the Solution of a Linear
Operator Equation in Hilbert Space — A Survey*, without proof. Here it is the backbone's
`Krylov.IsGalerkinIterate.energyNorm_error_le`, whose rate is written with the condition number
$\kappa = M/m$.

**Reading.** Same Chebyshev bound on arbitrary real Hilbert spaces with explicit endpoint ordering.
-/
theorem equation_5_6_5 (hA : IsSelfAdjoint A) (hm : 0 < m) (hmM : m ≤ M)
    (hbound : ∀ v, Real.sqrt m * ‖v‖ ≤ normA A v ∧ normA A v ≤ Real.sqrt M * ‖v‖)
    (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ k).u)
      ≤ 2 * ((Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m)) ^ k *
        normA A (ustar - u₀) := by
  have hA' := isSymmetricBoundedBy_of_bound hA hm hbound
  have hAc := hA'.isSymmetricCoercive hm
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have ht : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hid : (Real.sqrt (M / m) - 1) / (Real.sqrt (M / m) + 1)
      = (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) := by
    have hd1 : Real.sqrt M / Real.sqrt m + 1 ≠ 0 := by positivity
    have hd2 : Real.sqrt M + Real.sqrt m ≠ 0 := by positivity
    rw [Real.sqrt_div hM.le m, div_eq_div_iff hd1 hd2]
    field_simp
  have hmain := (CG.isGalerkinIterate f u₀ hAc k).energyNorm_error_le hm hmM hA' hstar
  rw [cg_u, normA_eq, normA_eq, ← hid]
  exact hmain

end Convergence

section Superlinear

variable [CompleteSpace V] {A K : V →L[ℝ] V} {lam : ℕ → ℝ} {δ Δ : ℝ} {f u₀ ustar : V}

/-- **Equations (5.6.7)–(5.6.9)** of [han2009theoretical], the setting of Theorem 5.6.2. Let $V$ be
a real Hilbert space, let $K \in \mathcal{L}(V)$ be self-adjoint with a Hilbert basis
$\{\varphi_j\}$ of eigenvectors, $K \varphi_j = \lambda_j \varphi_j$, and let $A = I - K$. If
$\delta \le 1 - \lambda_j \le \Delta$ for every $j$, then $A$ is symmetric and
$$\delta \|v\|^2 \le (Av, v) \le \Delta \|v\|^2 \quad \text{for all } v \in V.$$
So $A$ satisfies (5.6.3) with $m = \delta$ and $M = \Delta$ when $\delta > 0$.

The conclusion is the backbone's `LinearMap.IsSymmetricBoundedBy A δ Δ`. The proof is Parseval's
identity in the eigenbasis, `Krylov.isSymmetricBoundedBy_of_eq_one_sub`.

**Reading.** Quadratic form spectral endpoint bounds given an explicit eigenbasis.
-/
theorem isSymmetricBoundedBy_of_one_sub (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V))
    (hK : IsSelfAdjoint K) (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) :
    (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy δ Δ :=
  Krylov.isSymmetricBoundedBy_of_eq_one_sub hAK
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK) φ
    (fun j => by simpa using hlam j) hlow hupp

omit [CompleteSpace V] in
/-- The eigenvalue relation behind (5.6.8) and (5.6.9): if $A = I - K$ and
$K \varphi_j = \lambda_j \varphi_j$, then $A \varphi_j = (1 - \lambda_j) \varphi_j$. -/
theorem apply_eigenvector (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (j : ℕ) : A (φ j) = (1 - lam j) • φ j := by
  have h' : (A : V →ₗ[ℝ] V) (φ j) = ((1 : V →ₗ[ℝ] V) - (K : V →ₗ[ℝ] V)) (φ j) := by rw [hAK]
  have h : A (φ j) = φ j - K (φ j) := by simpa using h'
  rw [h, hlam j, sub_smul, one_smul]

omit [CompleteSpace V] in
/-- Let $A = I - K$, where $K$ has the orthonormal eigenvectors $\varphi_j$ with
$K \varphi_j = \lambda_j \varphi_j$, and let $0 < \delta \le 1 - \lambda_j$ for every $j$. Then
$1 - \lambda_j \le \|A\|$ for every $j$, because $1 - \lambda_j$ is the eigenvalue of $A$ at the
unit vector $\varphi_j$. -/
theorem one_sub_le_norm (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (j : ℕ) :
    1 - lam j ≤ ‖A‖ := by
  have hpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
  have hnorm : ‖φ j‖ = 1 := φ.orthonormal.1 j
  have hle := A.le_opNorm (φ j)
  rw [apply_eigenvector hAK φ hlam j, norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos hpos] at hle
  linarith [hle]

omit [CompleteSpace V] in
/-- Let $A = I - K$ be invertible, where $K$ has the orthonormal eigenvectors $\varphi_j$ with
$K \varphi_j = \lambda_j \varphi_j$, and let $0 < \delta \le 1 - \lambda_j$ for every $j$. Then
$1/(1 - \lambda_j) \le \|A^{-1}\|$ for every $j$. So every term of $\tau_\ell$ is at most
$\|(I - K)^{-1}\|$ times $|\lambda_j|$.

The numbers $1/(1 - \lambda_j)$ are eigenvalues of $A^{-1}$, and an eigenvalue of a bounded
operator at a unit vector is at most its norm. -/
theorem one_div_one_sub_le_norm_symm (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V))
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V) (he : (e : V →L[ℝ] V) = A) (j : ℕ) :
    1 / (1 - lam j) ≤ ‖(e.symm : V →L[ℝ] V)‖ := by
  have hpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
  have hnorm : ‖φ j‖ = 1 := φ.orthonormal.1 j
  have hA : A (φ j) = (1 - lam j) • φ j := apply_eigenvector hAK φ hlam j
  have he' : ∀ x : V, e x = A x := fun x => by rw [← he]; rfl
  have hsymm : (e.symm : V →L[ℝ] V) (φ j) = (1 - lam j)⁻¹ • φ j := by
    have hfwd : e ((1 - lam j)⁻¹ • φ j) = φ j := by
      rw [he', map_smul, hA, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    calc (e.symm : V →L[ℝ] V) (φ j) = e.symm (φ j) := rfl
      _ = e.symm (e ((1 - lam j)⁻¹ • φ j)) := by rw [hfwd]
      _ = (1 - lam j)⁻¹ • φ j := e.symm_apply_apply _
  have hle := ContinuousLinearMap.le_opNorm (e.symm : V →L[ℝ] V) (φ j)
  rw [hsymm, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hpos)] at hle
  rw [one_div]
  linarith [hle]

omit [CompleteSpace V] in
/-- Bounds on the quadratic form give a bound on the operator norm. Let $A \in \mathcal{L}(V)$ be
symmetric with $m \|x\|^2 \le (Ax, x) \le M \|x\|^2$ for all $x$, where $m > 0$ and $M \ge 0$.
Then $\|A\| \le M$.

The proof applies the Cauchy–Schwarz inequality for the energy inner product,
`LinearMap.IsSymmetricCoercive.abs_energyInner_le`, to $x$ and $Ax$. This gives the bound
$\|A\| \le \Delta$ in (5.6.9). -/
theorem norm_le_of_isSymmetricBoundedBy {A : V →L[ℝ] V} {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hA : (A : V →ₗ[ℝ] V).IsSymmetricBoundedBy m M) : ‖A‖ ≤ M := by
  have hcoer := hA.isSymmetricCoercive hm
  have hen : ∀ y : V, energyNorm (A : V →ₗ[ℝ] V) y ≤ Real.sqrt M * ‖y‖ := by
    intro y
    have hsq : energyNorm (A : V →ₗ[ℝ] V) y ^ 2 ≤ (Real.sqrt M * ‖y‖) ^ 2 := by
      rw [hcoer.energyNorm_sq, mul_pow, Real.sq_sqrt hM]
      exact hA.re_inner_le y
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (energyNorm_nonneg _ y), Real.sqrt_sq (by positivity)] at h1
  refine ContinuousLinearMap.opNorm_le_bound A hM fun x => ?_
  rcases eq_or_ne (A x) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  have hAxpos : 0 < ‖A x‖ := norm_pos_iff.2 h0
  have hcs := hcoer.abs_energyInner_le x (A x)
  have hval : ‖energyInner (A : V →ₗ[ℝ] V) x (A x)‖ = ‖A x‖ ^ 2 := by
    rw [energyInner]
    simp
  rw [hval] at hcs
  have hbound : ‖A x‖ ^ 2 ≤ (Real.sqrt M * ‖x‖) * (Real.sqrt M * ‖A x‖) :=
    hcs.trans (mul_le_mul (hen x) (hen (A x)) (energyNorm_nonneg _ _) (by positivity))
  have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
  have heq : Real.sqrt M * ‖x‖ * (Real.sqrt M * ‖A x‖) = M * ‖x‖ * ‖A x‖ := by
    have hre : Real.sqrt M * ‖x‖ * (Real.sqrt M * ‖A x‖)
        = Real.sqrt M * Real.sqrt M * (‖x‖ * ‖A x‖) := by ring
    rw [hre, hMM]; ring
  rw [heq, pow_two] at hbound
  exact le_of_mul_le_mul_right hbound hAxpos

/-- **Equation (5.6.8)** of [han2009theoretical]. In the setting of Theorem 5.6.2, let
$K \in \mathcal{L}(V)$ be self-adjoint with $K \varphi_j = \lambda_j \varphi_j$ for a Hilbert
basis $\{\varphi_j\}$, let $A = I - K$, and let $\delta = \inf_j (1 - \lambda_j)$ and
$1 - \lambda_j \le \Delta$ for every $j$. Then $A$ is positive definite, that is
$c \|v\|^2 \le (Av, v)$ for all $v$ and some $c > 0$, if and only if
$$\delta = 1 - \sup_j \lambda_j > 0.$$

The infimum is given by the two hypotheses $\delta \le 1 - \lambda_j$ for every $j$ and, for
every $\varepsilon > 0$, $1 - \lambda_j < \delta + \varepsilon$ for some $j$. Positive
definiteness is the backbone's `LinearMap.IsCoerciveWith`. A coercivity constant is at most
$1 - \lambda_j$ for every $j$, by the value at $\varphi_j$, so it is at most $\delta$.
Conversely, $\delta > 0$ is a coercivity constant, by
`AtkinsonHan.Chapter05.isSymmetricBoundedBy_of_one_sub`.

**Reading.** Explicit eigenbasis with lower-endpoint approximation and equivalence with uniform
coercivity.
-/
theorem equation_5_6_8 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hlow : ∀ j, δ ≤ 1 - lam j)
    (hinf : ∀ ε > 0, ∃ j, 1 - lam j < δ + ε) (hupp : ∀ j, 1 - lam j ≤ Δ) :
    (∃ m > 0, (A : V →ₗ[ℝ] V).IsCoerciveWith m) ↔ 0 < δ := by
  constructor
  · rintro ⟨m, hm, hcoer⟩
    have hj : ∀ j, m ≤ 1 - lam j := by
      intro j
      have h := hcoer (φ j)
      have hval : (A : V →ₗ[ℝ] V) (φ j) = (1 - lam j) • φ j := apply_eigenvector hAK φ hlam j
      simpa [hval, real_inner_smul_left, real_inner_self_eq_norm_sq, φ.orthonormal.1 j] using h
    refine lt_of_lt_of_le hm (le_of_forall_pos_le_add fun ε hε => ?_)
    obtain ⟨j, hjlt⟩ := hinf ε hε
    exact le_of_lt (lt_of_le_of_lt (hj j) hjlt)
  · intro hδ
    exact ⟨δ, hδ, (isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp).isCoerciveWith⟩

/-- **Equation (5.6.9)** of [han2009theoretical]. In the setting of Theorem 5.6.2, let
$K \in \mathcal{L}(V)$ be self-adjoint with $K \varphi_j = \lambda_j \varphi_j$ for a Hilbert
basis $\{\varphi_j\}$, and let $A = I - K$ be invertible. Let $\Delta = \sup_j (1 - \lambda_j)$
and $\delta = \inf_j (1 - \lambda_j) > 0$. Then
$$\|A\| = \Delta, \qquad \|A^{-1}\| = \frac{1}{\delta}.$$

The supremum and the infimum are each given by a bound and an approximation property, as in
`AtkinsonHan.Chapter05.equation_5_6_8`. The inequalities $\|A\| \le \Delta$ and
$\|A^{-1}\| \le 1/\delta$ follow from the bounds on the quadratic form in
`AtkinsonHan.Chapter05.isSymmetricBoundedBy_of_one_sub`. The reverse inequalities follow from
the values of $A$ and $A^{-1}$ at the unit eigenvectors $\varphi_j$, which come arbitrarily
close to $\Delta$ and to $1/\delta$.

**Reading.** Norm formulas assume a supplied diagonalization, spectral extremes and inverse
equivalence.
-/
theorem equation_5_6_9 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ)
    (hsup : ∀ ε > 0, ∃ j, Δ - ε < 1 - lam j) (hinf : ∀ ε > 0, ∃ j, 1 - lam j < δ + ε)
    (e : V ≃L[ℝ] V) (he : (e : V →L[ℝ] V) = A) :
    ‖A‖ = Δ ∧ ‖(e.symm : V →L[ℝ] V)‖ = 1 / δ := by
  have hbdd := isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp
  have hΔ : 0 < Δ := lt_of_lt_of_le hδ ((hlow 0).trans (hupp 0))
  constructor
  · refine le_antisymm (norm_le_of_isSymmetricBoundedBy hδ hΔ.le hbdd) ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨j, hj⟩ := hsup ε hε
    have := one_sub_le_norm hAK φ hlam hδ hlow j
    linarith
  · -- `‖A⁻¹‖ ≤ 1/δ` from coercivity, `≥` from the eigenvector nearest the infimum
    have hle : ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 / δ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      have hAx : A ((e.symm : V →L[ℝ] V) y) = y := by
        rw [← he]
        exact e.apply_symm_apply y
      have hco : δ * ‖(e.symm : V →L[ℝ] V) y‖ ^ 2
          ≤ inner ℝ (A ((e.symm : V →L[ℝ] V) y)) ((e.symm : V →L[ℝ] V) y) := by
        simpa using hbdd.le_re_inner ((e.symm : V →L[ℝ] V) y)
      rw [hAx] at hco
      have hcs : inner ℝ y ((e.symm : V →L[ℝ] V) y) ≤ ‖y‖ * ‖(e.symm : V →L[ℝ] V) y‖ :=
        real_inner_le_norm _ _
      rcases eq_or_lt_of_le (norm_nonneg ((e.symm : V →L[ℝ] V) y)) with hx0 | hx0
      · rw [← hx0]
        positivity
      · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ]
        nlinarith [hco, hcs, hx0]
    refine le_antisymm hle ?_
    have hpos : 0 < ‖(e.symm : V →L[ℝ] V)‖ := by
      have h0 := one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he 0
      have hjpos : 0 < 1 - lam 0 := lt_of_lt_of_le hδ (hlow 0)
      have hd : 0 < 1 / (1 - lam 0) := by positivity
      linarith
    -- `1/‖A⁻¹‖` is a lower bound for the `1 - λ_j`, hence at most their infimum `δ`
    have hlb : 1 / ‖(e.symm : V →L[ℝ] V)‖ ≤ δ := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨j, hj⟩ := hinf ε hε
      have hjpos : 0 < 1 - lam j := lt_of_lt_of_le hδ (hlow j)
      have h2 := one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j
      rw [div_le_iff₀ hjpos] at h2
      have h1 : 1 / ‖(e.symm : V →L[ℝ] V)‖ ≤ 1 - lam j := by
        rw [div_le_iff₀ hpos]
        linarith [mul_comm ‖(e.symm : V →L[ℝ] V)‖ (1 - lam j)]
      linarith
    rw [div_le_iff₀ hpos] at hlb
    rw [div_le_iff₀ hδ]
    linarith [mul_comm δ ‖(e.symm : V →L[ℝ] V)‖]

/-- **Equation (5.6.10)** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $K$ be
self-adjoint with $K \varphi_j = \lambda_j \varphi_j$ for a Hilbert basis $\{\varphi_j\}$, let
$A = I - K$, let $0 < \delta \le 1 - \lambda_j \le \Delta$ for every $j$, and let $Au^* = f$.
Then for every $k$ the conjugate gradient iterates satisfy
$$\|u^* - u_{k+1}\|_A \le \frac{\Delta - \delta}{\Delta + \delta} \|u^* - u_k\|_A.$$

This is (5.6.4) with $m = \delta$ and $M = \Delta$.

**Reading.** Uses supplied spectral bounds and an explicit eigenbasis.
-/
theorem equation_5_6_10 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) (hstar : A ustar = f) (k : ℕ) :
    normA A (ustar - (cg A f u₀ (k + 1)).u)
      ≤ (Δ - δ) / (Δ + δ) * normA A (ustar - (cg A f u₀ k).u) := by
  rw [cg_u, cg_u, normA_eq, normA_eq]
  exact cg_energyNorm_error_step_le hδ
    (isSymmetricBoundedBy_of_one_sub hAK hK φ hlam hlow hupp) hstar k

/-- **Theorem 5.6.2** of [han2009theoretical] (Winther [winther1980some]). Let $V$ be a real Hilbert
space, let $K \in \mathcal{L}(V)$ be self-adjoint with a Hilbert basis $\{\varphi_j\}$ of
eigenvectors, $K \varphi_j = \lambda_j \varphi_j$, where $|\lambda_j|$ is decreasing and
$\lambda_j \to 0$. Let $A = I - K$, let $0 < \delta \le 1 - \lambda_j \le \Delta$ for every $j$,
and let $Au^* = f$. Then the conjugate gradient iterates satisfy (5.6.11),
$$\|u^* - u_k\| \le c_k^k \|u^* - u_0\| \quad \text{for every } k,$$
where
$$c_k = \left( \frac{\Delta}{\delta} \right)^{1/(2k)} \frac{2}{k} \sum_{j < k}
  \frac{|\lambda_j|}{1 - \lambda_j},$$
and $c_k \to 0$ as $k \to \infty$.

**Generalization.** The book's rate (5.6.21) has the factor $(\Delta/\delta)^{3/(2k)}$ in place
of $(\Delta/\delta)^{1/(2k)}$. Since $\Delta/\delta \ge 1$, the rate here is smaller, and it has
the same limit $0$.

The compact operator $K$ is given by its eigen-decomposition, which is what its compactness
supplies: the eigenvalues are enumerated so that $|\lambda_j|$ decreases to $0$. This
enumeration is not derived from the compactness of $K$, because Mathlib has no decreasing
enumeration of the eigenvalues of a compact operator as a sequence indexed by $\mathbb{N}$. The
rate $c_k$ is the backbone's `Krylov.wintherRate lam δ Δ k`, and the eigenvalues are indexed
from $0$. -/
theorem theorem_5_6_2 (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (hK : IsSelfAdjoint K)
    (φ : HilbertBasis ℕ ℝ V) (hlam : ∀ j, K (φ j) = lam j • φ j)
    (hanti : Antitone fun j => |lam j|) (hlim : Tendsto lam atTop (𝓝 0)) (hδ : 0 < δ)
    (hlow : ∀ j, δ ≤ 1 - lam j) (hupp : ∀ j, 1 - lam j ≤ Δ) (hstar : A ustar = f) :
    (∀ k, ‖ustar - (cg A f u₀ k).u‖ ≤ Krylov.wintherRate lam δ Δ k ^ k * ‖ustar - u₀‖) ∧
      Tendsto (Krylov.wintherRate lam δ Δ) atTop (𝓝 0) := by
  have hΔ : 0 < Δ := hδ.trans_le ((hlow 0).trans (hupp 0))
  refine ⟨fun k => ?_, Krylov.winther_rate_tendsto_zero hδ hΔ hlim⟩
  rw [cg_u]
  exact Krylov.winther hAK (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK) φ
    (fun j => by simpa using hlam j) hanti hδ hlow hupp hstar k

/-- **Theorem 5.6.3** of [han2009theoretical], the average $\tau_\ell$. For a sequence $(\lambda_j)$
and $\ell \in \mathbb{N}$,
$$\tau_\ell = \frac{1}{\ell} \sum_{j < \ell} \frac{|\lambda_j|}{1 - \lambda_j}.$$
For the eigenvalues of $K$, this average makes the superlinear rate of Theorem 5.6.2 tend to
$0$.

The book indexes the eigenvalues from $1$. Here they are indexed from $0$, so the book's
$\lambda_j$ is `lam (j - 1)`. For $\ell = 0$ the value is $0$.

**Reading.** Same mean with zero-based indices and totalization at zero length.
-/
noncomputable def tau (lam : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)

/-- The rate of Theorem 5.6.2 written with $\tau_k$: the backbone's rate `Krylov.wintherRate` is
$$c_k = \left( \frac{\Delta}{\delta} \right)^{1/(2k)} \cdot 2 \tau_k.$$

The book's rate (5.6.21) is $(\Delta/\delta)^{3/(2k)} \cdot 2 \tau_k$. The backbone proves the
smaller rate with the exponent $1/(2k)$.

**Reading.** Uses smaller condition-factor exponent.
-/
theorem wintherRate_eq_tau (lam : ℕ → ℝ) (δ Δ : ℝ) (k : ℕ) :
    Krylov.wintherRate lam δ Δ k = (Δ / δ) ^ (1 / (2 * k : ℝ)) * (2 * tau lam k) := by
  simp only [Krylov.wintherRate, tau]
  ring


omit [CompleteSpace V] in
/-- **Theorem 5.6.3(a)** of [han2009theoretical]. Let $K$ have a Hilbert basis
$\{\varphi_j\}_{j \ge 0}$ of eigenvectors, $K \varphi_j = \lambda_j \varphi_j$, let $A = I - K$
be invertible, and let $0 < \delta \le 1 - \lambda_j$ for every $j$. Let $S \ge 0$ with
$\sum_j \lambda_j^2 = S^2$, that is $S = \|K\|_{HS}$. Then for every $\ell \ge 1$
$$\frac{1}{\ell} \frac{|\lambda_0|}{1 - \lambda_0} \le \tau_\ell \le \frac{S \, \|(I -
  K)^{-1}\|}{\sqrt{\ell}}.$$
So $\tau_\ell \to 0$ at the rate $\ell^{-1/2}$, which makes the conjugate gradient method
superlinearly convergent for an equation of the second kind with a Hilbert–Schmidt kernel. The
lower bound shows that the rate cannot be read off the leading eigenvalue alone.

The Hilbert–Schmidt norm enters only through the identity $\sum_j \lambda_j^2 = \|K\|_{HS}^2$,
which is the hypothesis `hHS`. This identity is Theorem 2.8.15 of the book, and Mathlib has no
Hilbert–Schmidt norm for the integral operators on $C([a, b] \times [a, b])$ from which to
derive it. No self-adjointness hypothesis on $K$ is needed. The upper bound is the
Cauchy–Schwarz inequality for $\sum_{j < \ell} |\lambda_j|$, which is why the exponent is
$-1/2$. The eigenvalues are indexed from $0$: the first eigenvalue $\lambda_0$, which is
`lam 0`, is the book's $\lambda_1$.

**Reading.** Abstract eigenvalue sum replaces integral Hilbert–Schmidt hypothesis.
-/
theorem theorem_5_6_3_a (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V)
    (he : (e : V →L[ℝ] V) = A) {S : ℝ} (hS : 0 ≤ S) (hHS : HasSum (fun j => lam j ^ 2) (S ^ 2))
    {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (ℓ : ℝ)⁻¹ * (|lam 0| / (1 - lam 0)) ≤ tau lam ℓ ∧
      tau lam ℓ ≤ S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hterm : ∀ j, 0 ≤ |lam j| / (1 - lam j) := fun j =>
    div_nonneg (abs_nonneg _) (le_of_lt (lt_of_lt_of_le hδ (hlow j)))
  have hC : 0 ≤ ‖(e.symm : V →L[ℝ] V)‖ := norm_nonneg _
  refine ⟨mul_le_mul_of_nonneg_left ?_ (by positivity), ?_⟩
  · exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_range.2 hℓ)
  -- the upper bound: bound each ratio by `|λ_j| ‖(I − K)⁻¹‖`, then Cauchy–Schwarz
  have hsum1 : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (∑ j ∈ Finset.range ℓ, |lam j|) * ‖(e.symm : V →L[ℝ] V)‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left
      (one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j) (abs_nonneg _)
  have hpartial : ∑ j ∈ Finset.range ℓ, lam j ^ 2 ≤ S ^ 2 :=
    sum_le_hasSum (Finset.range ℓ) (fun j _ => sq_nonneg _) hHS
  have hcs : (∑ j ∈ Finset.range ℓ, |lam j|) ^ 2
      ≤ (ℓ : ℝ) * ∑ j ∈ Finset.range ℓ, lam j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range ℓ) (f := fun j => |lam j|)
    simpa [sq_abs] using h
  have hnn : 0 ≤ ∑ j ∈ Finset.range ℓ, |lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsqrt : Real.sqrt ℓ * Real.sqrt ℓ = (ℓ : ℝ) := Real.mul_self_sqrt hℓ0.le
  have hsqrtpos : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
  have habs : ∑ j ∈ Finset.range ℓ, |lam j| ≤ Real.sqrt ℓ * S := by
    have hy : 0 ≤ Real.sqrt ℓ * S := mul_nonneg hsqrtpos.le hS
    have hsq2 : (Real.sqrt ℓ * S) ^ 2 = (ℓ : ℝ) * S ^ 2 := by
      rw [mul_pow, pow_two (Real.sqrt ℓ), hsqrt]
    have h1 : (∑ j ∈ Finset.range ℓ, |lam j|) ^ 2 ≤ (Real.sqrt ℓ * S) ^ 2 := by
      rw [hsq2]
      exact hcs.trans (mul_le_mul_of_nonneg_left hpartial hℓ0.le)
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq hy] at h2
  have hmain : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖ :=
    hsum1.trans (mul_le_mul_of_nonneg_right habs hC)
  have hfin : (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖)
      = S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := by
    rw [eq_div_iff hsqrtpos.ne']
    have hre : (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖) * Real.sqrt ℓ
        = (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * Real.sqrt ℓ) * (S * ‖(e.symm : V →L[ℝ] V)‖) := by ring
    rw [hre, hsqrt, inv_mul_cancel₀ hℓ0.ne', one_mul]
  rw [tau]
  calc (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (ℓ : ℝ)⁻¹ * (Real.sqrt ℓ * S * ‖(e.symm : V →L[ℝ] V)‖) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = S * ‖(e.symm : V →L[ℝ] V)‖ / Real.sqrt ℓ := hfin

omit [CompleteSpace V] in
/-- **Theorem 5.6.3(b)** of [han2009theoretical]. Let $K$ have a Hilbert basis $\{\varphi_j\}$ of
eigenvectors, $K \varphi_j = \lambda_j \varphi_j$, let $A = I - K$ be invertible, and let
$0 < \delta \le 1 - \lambda_j$ for every $j$. Let $p \ge 1$ and $M \ge 0$, and assume that the
eigenvalues decay like
$$|\lambda_j| \le M j^{-(p + 1/2)} \quad \text{for } j \ge 1,$$
in the book's indexing. Then for every $\ell \ge 1$
$$\tau_\ell \le \frac{M}{\ell} \, \zeta(p + 1/2) \, \|(I - K)^{-1}\|.$$
This is one full order faster than the rate $\ell^{-1/2}$ of part (a).

The book quotes the decay from Fenyő and Stolle for a symmetric kernel with continuous partial
derivatives up to the order $p$. Here it is the hypothesis `hdecay`, because Mathlib has no
eigenvalue asymptotics for smooth kernels. In the indexing from $0$, the hypothesis reads
$|\lambda_j| \le M (j + 1)^{-(p + 1/2)}$. The value $\zeta(p + 1/2)$ is written as the sum
`∑' n, 1 / n ^ (p + 1 / 2)`, whose term at $n = 0$ is $0$.

**Reading.** Abstract decay bound replaces smooth integral kernel and allows real order.
-/
theorem theorem_5_6_3_b (hAK : (A : V →ₗ[ℝ] V) = 1 - (K : V →ₗ[ℝ] V)) (φ : HilbertBasis ℕ ℝ V)
    (hlam : ∀ j, K (φ j) = lam j • φ j) (hδ : 0 < δ) (hlow : ∀ j, δ ≤ 1 - lam j) (e : V ≃L[ℝ] V)
    (he : (e : V →L[ℝ] V) = A) {p M : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M)
    (hdecay : ∀ j : ℕ, |lam j| ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2))) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    tau lam ℓ ≤ M / ℓ * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hq : (1 : ℝ) < p + 1 / 2 := by linarith
  have hq0 : (0 : ℝ) < p + 1 / 2 := by linarith
  have hsummable : Summable fun n : ℕ => 1 / (n : ℝ) ^ (p + 1 / 2) :=
    Real.summable_one_div_nat_rpow.2 hq
  have hC : 0 ≤ ‖(e.symm : V →L[ℝ] V)‖ := norm_nonneg _
  have hstep : ∀ j : ℕ, |lam j| / (1 - lam j)
      ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
    intro j
    calc |lam j| / (1 - lam j) = |lam j| * (1 / (1 - lam j)) := div_eq_mul_one_div _ _
      _ ≤ |lam j| * ‖(e.symm : V →L[ℝ] V)‖ :=
          mul_le_mul_of_nonneg_left
            (one_div_one_sub_le_norm_symm hAK φ hlam hδ hlow e he j) (abs_nonneg _)
      _ ≤ M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ :=
          mul_le_mul_of_nonneg_right (hdecay j) hC
  have hshift : ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2)
      = ∑ n ∈ Finset.range (ℓ + 1), 1 / (n : ℝ) ^ (p + 1 / 2) := by
    rw [Finset.sum_range_succ' (fun n => 1 / (n : ℝ) ^ (p + 1 / 2)) ℓ]
    simp only [Nat.cast_zero, Real.zero_rpow (ne_of_gt hq0), div_zero, add_zero, Nat.cast_add,
      Nat.cast_one]
  have hzeta : ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2)
      ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2) := by
    rw [hshift]
    refine hsummable.sum_le_tsum _ fun n _ => ?_
    positivity
  have hsum : ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by
    calc ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
        ≤ ∑ j ∈ Finset.range ℓ, M * (1 / ((j : ℝ) + 1) ^ (p + 1 / 2))
            * ‖(e.symm : V →L[ℝ] V)‖ := Finset.sum_le_sum fun j _ => hstep j
      _ = M * ‖(e.symm : V →L[ℝ] V)‖
            * ∑ j ∈ Finset.range ℓ, 1 / ((j : ℝ) + 1) ^ (p + 1 / 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ M * ‖(e.symm : V →L[ℝ] V)‖ * ∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2) :=
          mul_le_mul_of_nonneg_left hzeta (by positivity)
      _ = M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by ring
  rw [tau]
  calc (ℓ : ℝ)⁻¹ * ∑ j ∈ Finset.range ℓ, |lam j| / (1 - lam j)
      ≤ (ℓ : ℝ)⁻¹ * (M * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2))
          * ‖(e.symm : V →L[ℝ] V)‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M / ℓ * (∑' n : ℕ, 1 / (n : ℝ) ^ (p + 1 / 2)) * ‖(e.symm : V →L[ℝ] V)‖ := by ring

end Superlinear

end AtkinsonHan.Chapter05
