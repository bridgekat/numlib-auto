/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Iterate
import Numlib.Variational.Forms
import NumlibSurface.AtkinsonHan.Chapter05.Section06
import NumlibSurface.AtkinsonHan.Chapter09.Section01

/-!
# Atkinson and Han, Section 9.4: The conjugate gradient method in variational form

This module formalizes Section 9.4 of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$
be a symmetric bilinear form on $V$ that is bounded with constant $M$ and $V$-elliptic with constant
$\alpha > 0$, and let $\ell \in V'$. Through the Riesz representation (9.4.5)–(9.4.6), the
variational problem (9.4.1), find $u \in V$ with $a(u, v) = \ell(v)$ for all $v \in V$, becomes the
operator equation (9.4.7) $Au = f$, where $(Au, v) = a(u, v)$ and $(f, v) = \ell(v)$. Algorithm 1 of
the section is the conjugate gradient method for this equation, written with the residual $r_k$,
defined by $(r_k, v) = \ell(v) - a(u_k, v)$, and the search directions $s_k$: $$u_{k+1} = u_k +
\alpha_k s_k, \quad \alpha_k = \frac{\|r_k\|^2}{a(s_k, s_k)}, \quad s_{k+1} = r_{k+1} + \beta_k s_k,
\quad \beta_k = \frac{\|r_{k+1}\|^2}{\|r_k\|^2}.$$ The module proves that Algorithm 1 is the
conjugate gradient iteration `CG.iterate` of `Numlib.Krylov.CG` for $A$ and $f$. The properties of
that iteration then hold for Algorithm 1: the orthogonality of the residuals, the $a$-conjugacy of
the search directions, the Galerkin property on Krylov subspaces, and the convergence rates (5.6.4)
and (5.6.5) of Theorem 5.6.1 in the energy norm $\|v\|_a = \sqrt{a(v, v)}$.

## Main definitions

* Section 9.4, `AtkinsonHan.Chapter09.residual`: the residual $r \in V$ with
  $(r, v) = \ell(v) - a(u, v)$ for all $v$.
* Algorithm 1, `AtkinsonHan.Chapter09.cgStep`: one step of the conjugate gradient method.
* Algorithm 1, `AtkinsonHan.Chapter09.cgIterate`: the iterates $(u_k, r_k, s_k)$ started at $u_0$
  with $s_0 = r_0$.

## Main results

* Section 9.4, `AtkinsonHan.Chapter09.inner_residual`: $(r, v) = \ell(v) - a(u, v)$ for all
  $v \in V$.
* Algorithm 1, `AtkinsonHan.Chapter09.cg_energy_rate`: $\|u - u_{k+1}\|_a \le \frac{M - \alpha}{M +
  \alpha} \|u - u_k\|_a$.
* Algorithm 1, `AtkinsonHan.Chapter09.cg_energy_bound`: $\|u - u_k\|_a \le 2
  \big(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\big)^k \|u - u_0\|_a$ with $\kappa = M / \alpha$.
* Algorithm 1, `AtkinsonHan.Chapter09.cg_converges`: $u_k \to u$ for $\alpha < M$.

## Implementation notes

* The state of Algorithm 1 is the backbone structure `CG.State`, whose fields `x`, `r` and `p` are
  $u_k$, $r_k$ and $s_k$. The residual $r_{k+1}$ is computed from its definition at $u_{k+1}$.
* The operator $A$ is `AtkinsonHan.BilinForm.toOperator`, and $f$ is `SesqForm.rieszRep` of $\ell$.
* Divisions are those of Lean: $\alpha_k = 0$ if $a(s_k, s_k) = 0$, and $\beta_k = 0$ if $r_k = 0$.

## Not formalized

* **Algorithm 2** (nonlinear conjugate gradient method for a strictly convex functional $J$). The
  source quotes its convergence without proof, and its line search is a minimization whose minimizer
  need not exist in general.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Chapter09

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- **Section 9.4** of [han2009theoretical], the residual. Let $V$ be a real Hilbert space, let $a$
be a bilinear form on $V$ that is bounded with constant $M$, and let $\ell \in V'$. The
**residual** at $u \in V$ is the element $r \in V$ with $$(r, v) = \ell(v) - a(u, v) \quad
\text{for all } v \in V.$$

It is the Riesz representative `SesqForm.rieszRep` of the functional $\ell - a(u, \cdot)$, so
its defining property is `AtkinsonHan.Chapter09.inner_residual`. -/
noncomputable def residual (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (u : V) : V :=
  SesqForm.rieszRep (ℓ - a.toCLM hM u)

/-- The step length $\alpha_k = \|r_k\|^2 / a(s_k, s_k)$ of Algorithm 1, for a state with residual
$r_k$ and search direction $s_k$. It is $0$ when $a(s_k, s_k) = 0$. -/
noncomputable def cgAlpha (a : BilinForm V) (st : CG.State V) : ℝ :=
  ‖st.r‖ ^ 2 / a st.p st.p

/-- **Algorithm 1** of [han2009theoretical], Section 9.4, one step. From a state $(u_k, r_k, s_k)$,
the step computes $$u_{k+1} = u_k + \alpha_k s_k, \qquad r_{k+1} = \text{the residual at }
u_{k+1}, \qquad s_{k+1} = r_{k+1} + \beta_k s_k,$$ with $\alpha_k = \|r_k\|^2 / a(s_k, s_k)$ and
$\beta_k = \|r_{k+1}\|^2 / \|r_k\|^2$.

The state is the backbone structure `CG.State`, whose fields `x`, `r` and `p` are $u_k$, $r_k$
and $s_k$. The residual $r_{k+1}$ is `AtkinsonHan.Chapter09.residual` at $u_{k+1}$. With the
division of Lean, $\alpha_k = 0$ if $a(s_k, s_k) = 0$, and $\beta_k = 0$ if $r_k = 0$. -/
noncomputable def cgStep (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (st : CG.State V) : CG.State V :=
  { x := st.x + cgAlpha a st • st.p
    r := residual a hM ℓ (st.x + cgAlpha a st • st.p)
    p := residual a hM ℓ (st.x + cgAlpha a st • st.p)
          + (‖residual a hM ℓ (st.x + cgAlpha a st • st.p)‖ ^ 2 / ‖st.r‖ ^ 2) • st.p }

/-- **Algorithm 1** of [han2009theoretical], Section 9.4. The $k$-th state $(u_k, r_k, s_k)$ of the
conjugate gradient method started at $u_0 \in V$, with $r_0$ the residual at $u_0$ and
$s_0 = r_0$. It is the $k$-th iterate of `AtkinsonHan.Chapter09.cgStep`. -/
noncomputable def cgIterate (a : BilinForm V) (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V)
    (u₀ : V) (k : ℕ) : CG.State V :=
  (cgStep a hM ℓ)^[k] ⟨u₀, residual a hM ℓ u₀, residual a hM ℓ u₀⟩

/-! ### The residual -/

/-- **Section 9.4** of [han2009theoretical], the defining property of the residual. Let $V$ be a
real Hilbert space, let $a$ be bounded with constant $M$, and let $\ell \in V'$. For all
$u, v \in V$, the residual $r$ at $u$ satisfies $$(r, v) = \ell(v) - a(u, v).$$

So $r = 0$ exactly when $u$ solves the variational problem (9.4.1). This makes $r_k$ the
stopping criterion of Algorithm 1. -/
theorem inner_residual (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u v : V) :
    ⟪residual a hM ℓ u, v⟫_ℝ = ℓ v - a u v := by
  rw [residual, SesqForm.inner_rieszRep]
  rfl

/-- The residual at $u$ is $f - Au$, for the operator $A$ of (9.4.5) and the right-hand side $f$ of
(9.4.6). -/
theorem residual_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    residual a hM ℓ u = SesqForm.rieszRep ℓ - BilinForm.toOperator a hM u := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_residual, inner_sub_left, SesqForm.inner_rieszRep, BilinForm.inner_toOperator]

/-- The residual at $u$ is minus the Riesz representative of the functional $a(u, \cdot) - \ell$.
This functional is the derivative of the energy at $u$
(`AtkinsonHan.Chapter09.hasFDerivAt_energy`), so $r_k = 0$ exactly at the solution. -/
theorem residual_eq_neg_rieszRep (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    residual a hM ℓ u = -SesqForm.rieszRep (a.toCLM hM u - ℓ) := by
  rw [residual, show (ℓ - a.toCLM hM u) = -(a.toCLM hM u - ℓ) from by abel, SesqForm.rieszRep,
    SesqForm.rieszRep, map_neg]

/-! ### Algorithm 1 is the conjugate gradient iteration of the backbone -/

private theorem cgAlpha_eq (hM : a.IsBoundedWith M) (st : CG.State V) :
    cgAlpha a st = CG.alpha (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st := by
  rw [cgAlpha, CG.alpha, real_inner_self_eq_norm_sq]
  congr 1
  exact (BilinForm.inner_toOperator hM st.p st.p).symm

private theorem cgStep_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (st : CG.State V)
    (hst : st.r = SesqForm.rieszRep ℓ - BilinForm.toOperator a hM st.x) :
    cgStep a hM ℓ st = CG.step (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st := by
  have hα := cgAlpha_eq hM st
  have hr : residual a hM ℓ (st.x + cgAlpha a st • st.p)
      = st.r - CG.alpha (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st •
        (BilinForm.toOperator a hM : V →ₗ[ℝ] V) st.p := by
    rw [residual_eq hM, hst, hα, map_add, map_smul]
    abel
  have hβ : ∀ w : V, ‖w‖ ^ 2 / ‖st.r‖ ^ 2 = (inner ℝ w w : ℝ) / inner ℝ st.r st.r := by
    intro w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [cgStep, CG.step, CG.State.mk.injEq]
  refine ⟨by rw [hα], hr, ?_⟩
  rw [hr, hβ]

/-- Algorithm 1 of Section 9.4, started at $u_0$, is the conjugate gradient iteration `CG.iterate`
of the backbone for the operator $A$ of (9.4.5) and the right-hand side $f$ of (9.4.6): the two
sequences of states are equal. -/
theorem cgIterate_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u₀ : V) (k : ℕ) :
    cgIterate a hM ℓ u₀ k
      = CG.iterate (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k := by
  induction k with
  | zero =>
    rw [cgIterate, Function.iterate_zero_apply, CG.iterate_zero, CG.init, residual_eq hM]
    rfl
  | succ k ih =>
    have hstep : cgIterate a hM ℓ u₀ (k + 1) = cgStep a hM ℓ (cgIterate a hM ℓ u₀ k) := by
      rw [cgIterate, cgIterate, Function.iterate_succ_apply']
    rw [hstep, ih, CG.iterate_succ]
    exact cgStep_eq hM ℓ _
      (CG.residual_eq (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k)

/-! ### Properties of $A$ and $f$, and the operator form of the problem -/

/-- The quadratic form of the operator $A$ of (9.4.5) is the bilinear form: $(Ax, x) = a(x, x)$. -/
private theorem re_inner_toOperator_self (hM : a.IsBoundedWith M) (x : V) :
    RCLike.re (inner ℝ ((BilinForm.toOperator a hM : V →ₗ[ℝ] V) x) x) = a x x := by
  rw [show ((BilinForm.toOperator a hM : V →ₗ[ℝ] V)) x = BilinForm.toOperator a hM x from rfl,
    BilinForm.inner_toOperator hM x x]
  simp

/-- Equations (9.4.2)–(9.4.3). Let $a$ be bounded with constant $M$, symmetric, and $V$-elliptic
with constant $\alpha$. Then the operator $A$ of (9.4.5) is symmetric and satisfies $$\alpha
\|v\|^2 \le (Av, v) \le M \|v\|^2 \quad \text{for all } v \in V.$$
-/
theorem isSymmetricBoundedBy_toOperator (hM : a.IsBoundedWith M)
    (hs : LinearMap.BilinForm.IsSymm a) (ha : a.IsEllipticWith α) :
    (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricBoundedBy α M where
  isSymmetric := (SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp
    ((BilinForm.isSymm_iff_isHermitian hM).mp hs)
  le_re_inner := fun x => by
    rw [re_inner_toOperator_self hM]
    exact ha x
  re_inner_le := fun x => by
    rw [re_inner_toOperator_self hM]
    calc a x x ≤ |a x x| := le_abs_self _
      _ ≤ M * ‖x‖ * ‖x‖ := hM x x
      _ = M * ‖x‖ ^ 2 := by ring

/-- The operator form (9.4.7) of the problem. Let $a$ be bounded with constant $M$, and let $u$
satisfy $a(u, v) = \ell(v)$ for all $v \in V$ (9.4.4). Then $Au = f$. -/
theorem toOperator_eq_rieszRep (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, a u v = ℓ v) :
    (BilinForm.toOperator a hM : V →ₗ[ℝ] V) u = SesqForm.rieszRep ℓ :=
  (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mpr hu

/-! ### Properties of Algorithm 1 from the backbone -/

variable {ℓ : StrongDual ℝ V} {u₀ : V}

/-- Let $a$ be bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$.
Then the $k$-th iterate $u_k$ of Algorithm 1 solves the Galerkin problem on the affine Krylov
space $u_0 + \mathcal{K}_k(A, r_0)$: it lies in this space, and its residual is orthogonal to
$\mathcal{K}_k(A, r_0)$.

Equivalently, $u_k$ minimizes the energy on $u_0 + \mathcal{K}_k(A, r_0)$. The statement is
`Krylov.IsGalerkinIterate`. -/
theorem cg_isGalerkinIterate (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) (k : ℕ) :
    Krylov.IsGalerkinIterate (BilinForm.toOperator a hM : V →ₗ[ℝ] V) (SesqForm.rieszRep ℓ) u₀ k
      (cgIterate a hM ℓ u₀ k).x := by
  rw [cgIterate_eq hM ℓ u₀ k]
  exact CG.isGalerkinIterate _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) k

/-- Let $a$ be bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$.
Then the residuals of Algorithm 1 are orthogonal: $(r_i, r_j) = 0$ for $i \ne j$. -/
theorem cg_inner_residual_eq_zero (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) {i j : ℕ} (h : i ≠ j) :
    ⟪(cgIterate a hM ℓ u₀ i).r, (cgIterate a hM ℓ u₀ j).r⟫_ℝ = 0 := by
  rw [cgIterate_eq hM ℓ u₀ i, cgIterate_eq hM ℓ u₀ j]
  exact CG.inner_residual_eq_zero _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) h

/-- Let $a$ be bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$.
Then the search directions of Algorithm 1 are $a$-conjugate: $a(s_i, s_j) = 0$ for $i \ne j$. -/
theorem cg_apply_direction_eq_zero (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) (u₀ : V) {i j : ℕ} (h : i ≠ j) :
    a (cgIterate a hM ℓ u₀ i).p (cgIterate a hM ℓ u₀ j).p = 0 := by
  rw [← BilinForm.inner_toOperator hM, cgIterate_eq hM ℓ u₀ i, cgIterate_eq hM ℓ u₀ j]
  exact CG.inner_apply_direction_eq_zero _ _
    ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) h

/-- Let $a$ be bounded with constant $M$, symmetric, and $V$-elliptic with constant $\alpha > 0$,
and let $u$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$. Then the energy norm $\|u - u_k\|_a$
of the error of Algorithm 1 is a decreasing function of $k$. -/
theorem cg_energyNorm_error_antitone (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a)
    (hα : 0 < α) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) : Antitone fun k => a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) := by
  have h := CG.energyNorm_error_antitone (A := (BilinForm.toOperator a hM : V →ₗ[ℝ] V))
    (SesqForm.rieszRep ℓ) u₀ ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα)
    (toOperator_eq_rieszRep hM ℓ hu)
  intro i j hij
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact h hij

/-! ### Convergence: Theorem 5.6.1 for Algorithm 1 -/

/-- **Algorithm 1** of [han2009theoretical], Section 9.4, with the rate (5.6.4) of Theorem 5.6.1.
Let $V$ be a real Hilbert space, let $a$ be a symmetric bilinear form on $V$ that is bounded
with constant $M$ and $V$-elliptic with constant $\alpha > 0$, and let $u$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$. Then for all $k$, the iterates $u_k$ of Algorithm 1 from
any $u_0 \in V$ satisfy $$\|u - u_{k+1}\|_a \le \frac{M - \alpha}{M + \alpha} \|u - u_k\|_a.$$

The energy norm is `AtkinsonHan.BilinForm.energyNorm`. The proof transfers
`Krylov.IsGalerkinIterate.energyNorm_error_succ_le` through
`AtkinsonHan.Chapter09.cgIterate_eq`. -/
theorem cg_energy_rate (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v) (u₀ : V)
    (k : ℕ) :
    a.energyNorm (u - (cgIterate a hM ℓ u₀ (k + 1)).x)
      ≤ (M - α) / (M + α) * a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) := by
  have hAc := (isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact Krylov.IsGalerkinIterate.energyNorm_error_succ_le hα
    (isSymmetricBoundedBy_toOperator hM hs ha) (CG.isGalerkinIterate _ _ hAc k)
    (CG.isGalerkinIterate _ _ hAc (k + 1)) (toOperator_eq_rieszRep hM ℓ hu)

/-- **Algorithm 1** of [han2009theoretical], Section 9.4, with the bound (5.6.5) of Theorem 5.6.1.
Let $V$ be a real Hilbert space, let $a$ be a symmetric bilinear form on $V$ that is bounded
with constant $M$ and $V$-elliptic with constant $\alpha$, with $0 < \alpha \le M$, and let $u$
satisfy $a(u, v) = \ell(v)$ for all $v \in V$. Then for all $k$, the iterates $u_k$ of Algorithm
1 from any $u_0 \in V$ satisfy, with $\kappa = M / \alpha$, $$\|u - u_k\|_a \le 2
\Big(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\Big)^k \|u - u_0\|_a.$$

The hypothesis $\alpha \le M$ is that of the backbone. The strict inequality $\alpha < M$ is
needed only in `AtkinsonHan.Chapter09.cg_converges`. -/
theorem cg_energy_bound (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (hαM : α ≤ M) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) (k : ℕ) :
    a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x)
      ≤ 2 * ((Real.sqrt (M / α) - 1) / (Real.sqrt (M / α) + 1)) ^ k *
          a.energyNorm (u - u₀) := by
  simp only [BilinForm.energyNorm_eq_energyNorm_toOperator hM, cgIterate_eq hM ℓ u₀]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le hα hαM
    (isSymmetricBoundedBy_toOperator hM hs ha)
    (CG.isGalerkinIterate _ _ ((isSymmetricBoundedBy_toOperator hM hs ha).isSymmetricCoercive hα) k)
    (toOperator_eq_rieszRep hM ℓ hu)

/-- **Algorithm 1** of [han2009theoretical], Section 9.4, convergence. Let $V$ be a real Hilbert
space, let $a$ be a symmetric bilinear form on $V$ that is bounded with constant $M$ and
$V$-elliptic with constant $\alpha$, with $0 < \alpha < M$, and let $u$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$. Then the iterates $u_k$ of Algorithm 1 from any
$u_0 \in V$ converge to $u$ in $V$.

The proof combines the bound (5.6.5) of `AtkinsonHan.Chapter09.cg_energy_bound` with
$\sqrt{\alpha} \|v\| \le \|v\|_a$. -/
theorem cg_converges (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) (hα : 0 < α)
    (hαM : α < M) (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v)
    (u₀ : V) : Tendsto (fun k => (cgIterate a hM ℓ u₀ k).x) atTop (𝓝 u) := by
  set ρ : ℝ := (Real.sqrt (M / α) - 1) / (Real.sqrt (M / α) + 1) with hρdef
  have hsa : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hone : (1 : ℝ) < Real.sqrt (M / α) := by
    have h1 : (1 : ℝ) < M / α := (one_lt_div hα).mpr hαM
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (M / α) := Real.sqrt_lt_sqrt (by norm_num) h1
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one (by linarith)]
    linarith
  have hmaj : Tendsto (fun k => 2 * a.energyNorm (u - u₀) / Real.sqrt α * ρ ^ k) atTop (𝓝 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
      (2 * a.energyNorm (u - u₀) / Real.sqrt α)
    simpa using hpow
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hmaj
  have h1 : Real.sqrt α * ‖u - (cgIterate a hM ℓ u₀ k).x‖
      ≤ a.energyNorm (u - (cgIterate a hM ℓ u₀ k).x) :=
    BilinForm.sqrt_mul_norm_le_energyNorm hM hα.le ha _
  have h2 := cg_energy_bound hM hs hα hαM.le ha ℓ hu u₀ k
  have hrw : 2 * a.energyNorm (u - u₀) / Real.sqrt α * ρ ^ k
      = 2 * a.energyNorm (u - u₀) * ρ ^ k / Real.sqrt α := by ring
  rw [norm_sub_rev, hrw, le_div_iff₀ hsa]
  calc ‖u - (cgIterate a hM ℓ u₀ k).x‖ * Real.sqrt α
      = Real.sqrt α * ‖u - (cgIterate a hM ℓ u₀ k).x‖ := mul_comm _ _
    _ ≤ 2 * ρ ^ k * a.energyNorm (u - u₀) := h1.trans h2
    _ = 2 * a.energyNorm (u - u₀) * ρ ^ k := by ring

/-! ### The energy functional and its derivative -/

omit [CompleteSpace V] in
/-- Let $V$ be a real inner product space, and let $a$ be symmetric and bounded with constant
$M \ge 0$. Then the energy $E(v) = \frac12 a(v, v) - \ell(v)$ has at each $u \in V$ the Fréchet
derivative $$\langle E'(u), v \rangle = a(u, v) - \ell(v).$$ In particular $E$ is Gâteaux
differentiable. -/
theorem hasFDerivAt_energy (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    HasFDerivAt (a.energy ℓ) (a.toCLM hM u - ℓ) u := by
  have hkey : ∀ y : V, a.energy ℓ y - a.energy ℓ u - (a.toCLM hM u - ℓ) (y - u)
      = (1 / 2 : ℝ) * a (y - u) (y - u) := by
    intro y
    have hsym : a y u = a u y := BilinForm.isSymm_iff.mp hs y u
    have h1 : (a.toCLM hM u - ℓ) (y - u) = a u y - a u u - (ℓ y - ℓ u) := by simp
    have h2 : a (y - u) (y - u) = a y y - a u y - (a y u - a u u) := by simp [map_sub]
    simp only [BilinForm.energy]
    rw [h1, h2, hsym]
    ring
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds u (show (0 : ℝ) < 2 * c / (M + 1) by positivity)] with y hy
  have hd : ‖y - u‖ < 2 * c / (M + 1) := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hy
  have hd' : M * ‖y - u‖ ≤ 2 * c := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)] at hd
    nlinarith [norm_nonneg (y - u)]
  rw [hkey y, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hb : |a (y - u) (y - u)| ≤ M * ‖y - u‖ * ‖y - u‖ := hM _ _
  have hnn : (0 : ℝ) ≤ ‖y - u‖ := norm_nonneg _
  calc (1 / 2 : ℝ) * |a (y - u) (y - u)| ≤ (1 / 2 : ℝ) * (M * ‖y - u‖ * ‖y - u‖) := by linarith
    _ ≤ c * ‖y - u‖ := by nlinarith

/-- The residual is minus the Riesz representative of the derivative of the energy: $(r, v) =
-\langle E'(u), v \rangle = -(a(u, v) - \ell(v))$ for all $u, v \in V$. -/
theorem inner_residual_eq_neg_fderiv (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u v : V) :
    ⟪residual a hM ℓ u, v⟫_ℝ = -((a.toCLM hM u - ℓ) v) := by
  rw [inner_residual]
  have h1 : (a.toCLM hM u - ℓ) v = a u v - ℓ v := rfl
  rw [h1]
  ring

/-- Let $a$ be symmetric, bounded with constant $M$ and $V$-elliptic with constant $\alpha > 0$.
Then $u$ minimizes the energy $E(v) = \frac12 a(v, v) - \ell(v)$ over $V$ if and only if
$a(u, v) = \ell(v)$ for all $v \in V$, which is (9.4.4). This is the case $V_N = V$ of (9.1.6). -/
theorem energy_isMinOn_iff (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) (u : V) :
    IsMinOn (a.energy ℓ) Set.univ u ↔ ∀ v, a u v = ℓ v := by
  simpa using Chapter08.theorem_8_3_3_subspace hM hα ha hs ℓ ⊤ Submodule.mem_top

end AtkinsonHan.Chapter09
