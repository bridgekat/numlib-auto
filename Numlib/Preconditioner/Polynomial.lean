/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Ring.GeomSum
import Numlib.Krylov.Convergence.Polynomial

/-!
# Polynomial preconditioning

A polynomial preconditioner for an operator $A$ is $M^{-1} = s(A)$ for a real polynomial $s$ of low
degree. The preconditioned operator is then $s(A) A$, and an application of $M^{-1}$ costs only
products with $A$ ([saad2003iterative], §12.3). This module gives three algebraic facts about such
preconditioners. First, the Neumann polynomial $\sum_{i \le s} (1 - \omega t)^i$ satisfies
$\bigl(\sum_{i \le s} N^i\bigr)(m a) = 1 - N^{s+1}$ for $N = 1 - m a$ in any ring, so a Neumann
preconditioner is $s + 1$ steps of the stationary iteration of the splitting with iteration operator
$N$ (`Numlib.Stationary.Basic`). Second, if $B$ is $D$-self-adjoint, that is $\langle D(Bx), y
\rangle = \langle Dx, By \rangle$ for all $x, y$, and $D$ is symmetric and coercive, then $s(B) B$
is symmetric for the inner product $\langle Dx, y \rangle$, so the conjugate gradient method applies
to it. Third, for a symmetric $A$ with $\alpha \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle
\le \beta \|x\|^2$,
$$\|x - s(A) A x\| \le \sup_{t \in [\alpha, \beta]} |1 - t s(t)| \, \|x\|,$$
so the quantity that a polynomial preconditioner must make small is
$\sup_{[\alpha, \beta]} |1 - t s(t)|$.

The two ways to choose $s$ optimally are in other modules: minimization of the uniform norm on an
enclosing interval in `Numlib.Preconditioner.Chebyshev`, and weighted least squares in
`Numlib.RingTheory.Polynomial.KernelPolynomial`.

## Main definitions

* `Preconditioner.neumannPolyOf`: the truncated Neumann series $\sum_{i \le s} n^i$ of a ring
  element $n$.
* `Preconditioner.neumannPoly`: the Neumann polynomial $\sum_{i \le s} (1 - \omega X)^i$.

## Main results

* `Preconditioner.neumannPoly_mul_eq`: $\bigl(\sum_{i \le s} (1 - m a)^i\bigr)(m a) = 1 - (1 - m
  a)^{s+1}$ in any ring.
* `Preconditioner.isSymmetric_withEnergy_aeval_mul`: for a $D$-self-adjoint $B$ and a real
  polynomial $s$, the operator $s(B) B$ is symmetric for the $D$-inner product.
* `Preconditioner.norm_sub_aeval_mul_apply_le`: the bound $\|x - s(A) A x\| \le \sup_{[\alpha,
  \beta]} |1 - t s(t)| \, \|x\|$.
* `Preconditioner.energyNorm_sub_aeval_mul_apply_le`: the same bound in the energy norm of $A$.

## Implementation notes

* The Neumann identity is stated for $1 - m a$ with an arbitrary ring element $m$. The general form
  $M^{-1} = \bigl(\sum_{i \le s} N^i\bigr) D^{-1}$ with $N = 1 - \omega D^{-1} A$ of
  [saad2003iterative], with a block-diagonal $D$, is then the case $m = \omega D^{-1}$, and needs no
  separate statement.
* The self-adjointness result is stated for any $B$ that is already $D$-self-adjoint. This covers
  $B = D^{-1} A$ for symmetric $A$ and $D$ without an inverse in the statement: the hypothesis
  $D B = A$ suffices (`Preconditioner.energyInner_comm_of_comp_eq`).
* The $D$-inner product is the inner product of the type synonym `WithEnergy D hD`, and $s(B) B$ is
  transported to it by `WithEnergy.equiv`.
* The norm bound holds in any inner product space and uses no functional calculus. It is the bound
  of `Numlib.Krylov.Convergence.Polynomial` applied to the residual polynomial $1 - X s$.
-/

open Polynomial

namespace Preconditioner

/-! ### Neumann polynomials -/

/-- The truncated Neumann series $\sum_{i=0}^{s} n^i$ of an element $n$ of a ring. Every Neumann
preconditioner has this form once the scaling is included in $n$. -/
def neumannPolyOf {R : Type*} [Ring R] (n : R) (s : ℕ) : R := ∑ i ∈ Finset.range (s + 1), n ^ i

/-- The **Neumann polynomial** $\sum_{i=0}^{s} (1 - \omega X)^i$ of [saad2003iterative], §12.3.1,
for $\omega$ in a commutative ring $R$.

For an operator $A$, the value $p(A)$ of this polynomial is the truncation after the power $s$
of the Neumann series $\sum_{i \ge 0} (1 - \omega A)^i$ of $(\omega A)^{-1}$. The definition is
`Preconditioner.neumannPolyOf` applied to the polynomial $1 - \omega X$. -/
noncomputable def neumannPoly {R : Type*} [CommRing R] (ω : R) (s : ℕ) : R[X] :=
  neumannPolyOf (1 - C ω * X) s

/-- For an $R$-algebra $A$ and $a \in A$, the value of the Neumann polynomial
$\sum_{i \le s} (1 - \omega X)^i$ at $a$ is the truncated Neumann series
$\sum_{i \le s} (1 - \omega a)^i$. -/
theorem aeval_neumannPoly {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (ω : R) (s : ℕ)
    (a : A) :
    aeval a (neumannPoly ω s) = neumannPolyOf (1 - algebraMap R A ω * a) s := by
  simp [neumannPoly, neumannPolyOf, map_sum]

/-- Let $m$ and $a$ be elements of a ring, and let $n = 1 - m a$. Then
$$\Bigl(\sum_{i=0}^{s} n^i\Bigr)(m a) = 1 - n^{s+1}.$$
This is equation (12.3) of [saad2003iterative].

For a Neumann preconditioner $M^{-1} = \bigl(\sum_{i \le s} n^i\bigr) m$, the preconditioned
operator $M^{-1} a$ therefore differs from the identity by exactly the power $s + 1$ of the
iteration operator $n$ of the underlying splitting. -/
theorem neumannPoly_mul_eq {R : Type*} [Ring R] (m a : R) (s : ℕ) :
    neumannPolyOf (1 - m * a) s * (m * a) = 1 - (1 - m * a) ^ (s + 1) := by
  have h : m * a = 1 - (1 - m * a) := (sub_sub_cancel 1 (m * a)).symm
  rw [neumannPolyOf]
  nth_rewrite 2 [h]
  exact geom_sum_mul_neg (1 - m * a) (s + 1)

/-! ### Self-adjointness for the inner product of the preconditioner -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $D$ be a symmetric coercive operator on an inner product space $E$, and let $T$ satisfy
$\langle D(Tx), y \rangle = \langle Dx, Ty \rangle$ for all $x, y \in E$. Then $T$, transported
to the space `WithEnergy D hD` with the inner product $\langle Dx, y \rangle$, is a symmetric
operator.

The preconditioned operator is in general not symmetric for the inner product of $E$. The
conjugate gradient method needs symmetry only for the inner product that it uses, and this
result gives that symmetry. -/
theorem isSymmetric_conj_of_energyInner {D : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    {T : E →ₗ[𝕜] E} (hT : ∀ x y, inner 𝕜 (D (T x)) y = inner 𝕜 (D x) (T y)) :
    ((WithEnergy.equiv D hD).conj T).IsSymmetric := by
  intro x y
  obtain ⟨u, rfl⟩ := (WithEnergy.equiv D hD).surjective x
  obtain ⟨v, rfl⟩ := (WithEnergy.equiv D hD).surjective y
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, WithEnergy.inner_equiv, WithEnergy.inner_equiv]
  exact hT u v

/-- Let $A$, $B$ and $D$ be operators on an inner product space, with $A$ and $D$ symmetric and
$D B = A$. Then $\langle D(Bx), y \rangle = \langle Dx, By \rangle$ for all $x$ and $y$, so $B$
is self-adjoint for the $D$-inner product. The hypothesis $D B = A$ describes $B = D^{-1} A$
without an inverse. -/
theorem energyInner_comm_of_comp_eq {D A B : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (hA : A.IsSymmetric)
    (hDB : D ∘ₗ B = A) (x y : E) : inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y) := by
  have h : ∀ z, D (B z) = A z := fun z => congrArg (fun f : E →ₗ[𝕜] E => f z) hDB
  rw [h x, hA x y, ← h y, ← hD x (B y)]

section EnergySelfAdjoint

variable {D B : E →ₗ[𝕜] E}

/-- If $B$ is self-adjoint for the $D$-inner product, then so is every power $B^n$. -/
private theorem energyInner_pow_comm
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (n : ℕ) (x y : E) :
    inner 𝕜 (D ((B ^ n) x)) y = inner 𝕜 (D x) ((B ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      calc inner 𝕜 (D ((B ^ (n + 1)) x)) y
          = inner 𝕜 (D ((B ^ n) (B x))) y := by rw [pow_succ, Module.End.mul_apply]
        _ = inner 𝕜 (D (B x)) ((B ^ n) y) := ih (B x) y
        _ = inner 𝕜 (D x) (B ((B ^ n) y)) := hB x ((B ^ n) y)
        _ = inner 𝕜 (D x) ((B ^ (n + 1)) y) := by rw [pow_succ', Module.End.mul_apply]

/-- If $B$ is self-adjoint for the $D$-inner product, then so is $p(B)$ for every real polynomial
$p$. -/
private theorem energyInner_aeval_comm
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (p : ℝ[X]) (x y : E) :
    inner 𝕜 (D (aeval B (p.map (algebraMap ℝ 𝕜)) x)) y =
      inner 𝕜 (D x) (aeval B (p.map (algebraMap ℝ 𝕜)) y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
        hp, hq]
  | monomial n c =>
      have hmon : ∀ z : E, aeval B ((monomial n c : ℝ[X]).map (algebraMap ℝ 𝕜)) z =
          (algebraMap ℝ 𝕜 c) • (B ^ n) z := by
        intro z
        simp [Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply]
      rw [hmon x, hmon y, map_smul, inner_smul_left, inner_smul_right,
        RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, energyInner_pow_comm hB n x y]

end EnergySelfAdjoint

/-- Let $D$ be a symmetric coercive operator on an inner product space $E$ over $\mathbb{R}$ or
$\mathbb{C}$, and let $B$ satisfy $\langle D(Bx), y \rangle = \langle Dx, By \rangle$ for all
$x, y \in E$. Then for every real polynomial $s$, the operator $s(B) B$ is symmetric for the
inner product $\langle Dx, y \rangle$. This is Exercise 12.1 of [saad2003iterative].

This is the reason why polynomial preconditioning is compatible with the conjugate gradient
method. The case $B = D^{-1} A$ with $A$ symmetric is covered by
`Preconditioner.energyInner_comm_of_comp_eq`. With $D = 1$, the statement is that $s(A) A$ is
symmetric for a symmetric $A$.

The operator $s(B) B$ is transported to `WithEnergy D hD` by `WithEnergy.equiv`. The real
polynomial $s$ acts through its image under `algebraMap ℝ 𝕜`. -/
theorem isSymmetric_withEnergy_aeval_mul {D B : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (s : ℝ[X]) :
    ((WithEnergy.equiv D hD).conj (aeval B (s.map (algebraMap ℝ 𝕜)) * B)).IsSymmetric := by
  refine isSymmetric_conj_of_energyInner hD fun x y => ?_
  have h : aeval B (s.map (algebraMap ℝ 𝕜)) * B = aeval B ((s * X).map (algebraMap ℝ 𝕜)) := by
    rw [Polynomial.map_mul, Polynomial.map_X, map_mul, aeval_X]
  rw [h]
  exact energyInner_aeval_comm hB (s * X) x y

/-! ### The optimality criterion -/

/-- The residual polynomial $1 - X s$ of a polynomial preconditioner, applied to a vector:
$(1 - X s)(A) x = x - s(A)(Ax)$. -/
private theorem aeval_one_sub_X_mul_apply (A : E →ₗ[𝕜] E) (s : ℝ[X]) (x : E) :
    aeval A (((1 : ℝ[X]) - X * s).map (algebraMap ℝ 𝕜)) x =
      x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x) := by
  have hcomm : ((1 : ℝ[X]) - X * s) = 1 - s * X := by ring
  rw [hcomm]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Module.End.mul_apply]

/-- The absolute value of the residual polynomial $1 - X s$ at $t$ is $|1 - t s(t)|$. -/
private theorem eval_one_sub_X_mul (s : ℝ[X]) :
    (fun t => |Polynomial.eval t ((1 : ℝ[X]) - X * s)|) = fun t => |1 - t * s.eval t| := by
  funext t
  simp

/-- Let $E$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be a symmetric
operator on $E$ with $\alpha \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le \beta
\|x\|^2$ for all $x$. Then for every real polynomial $s$ and every $x \in E$,
$$\|x - s(A)(Ax)\| \le \Bigl(\sup_{t \in [\alpha, \beta]} |1 - t s(t)|\Bigr) \|x\|.$$
This is the optimality criterion (12.4)–(12.5) of [saad2003iterative], written as a bound.

A choice of $s$ that makes $\sup_{[\alpha, \beta]} |1 - t s(t)|$ small therefore makes the
preconditioned operator $s(A) A$ close to the identity. The bounds on $A$ are
`LinearMap.IsSymmetricBoundedBy`. The version with the supremum over the spectrum instead of an
enclosing interval is `LinearMap.IsSymmetric.norm_aeval_apply_le`. -/
theorem norm_sub_aeval_mul_apply_le {A : E →ₗ[𝕜] E} {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β)
    (s : ℝ[X]) (x : E) :
    ‖x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x)‖ ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * ‖x‖ := by
  have h := hA.norm_aeval_map_apply_le ((1 : ℝ[X]) - X * s) x
  rwa [aeval_one_sub_X_mul_apply, eval_one_sub_X_mul] at h

/-- Let $A$ be a symmetric operator with $\alpha \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle
\le \beta \|x\|^2$ for all $x$, and $\alpha > 0$. Then for every real polynomial $s$ and every
$x$,
$$\|x - s(A)(Ax)\|_A \le \Bigl(\sup_{t \in [\alpha, \beta]} |1 - t s(t)|\Bigr) \|x\|_A,$$
where $\|v\|_A = \sqrt{\operatorname{Re} \langle Av, v \rangle}$ is the energy norm. This is the
form of `Preconditioner.norm_sub_aeval_mul_apply_le` that the preconditioned conjugate gradient
method uses. -/
theorem energyNorm_sub_aeval_mul_apply_le {A : E →ₗ[𝕜] E} {α β : ℝ}
    (hA : A.IsSymmetricBoundedBy α β) (hα : 0 < α) (s : ℝ[X]) (x : E) :
    energyNorm A (x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x)) ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * energyNorm A x := by
  have h := hA.energyNorm_aeval_map_apply_le hα ((1 : ℝ[X]) - X * s) x
  rwa [aeval_one_sub_X_mul_apply, eval_one_sub_X_mul] at h

end Preconditioner
