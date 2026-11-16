/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# Energy inner product and energy norm

Let $A$ be an operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$.
The **energy inner product** and the **energy norm** of $A$ are
$$\langle x, y \rangle_A = \langle Ax, y \rangle, \qquad \|x\|_A = \sqrt{\operatorname{Re} \langle
  Ax, x \rangle}.$$
When $A$ is symmetric coercive, they are an inner product and its norm on $E$, also called the
$A$-inner product and the $A$-norm. The **energy functional** of the system $Ax = b$ is
$\varphi(x) = \frac{1}{2} \operatorname{Re} \langle Ax, x \rangle - \operatorname{Re} \langle b, x
\rangle$ (§4.3.3 and (7.35) of [quarteroni2000numerical]). This module proves the norm equivalence
$\sqrt{c} \|x\| \le \|x\|_A \le \sqrt{\|A\|} \|x\|$, the identity $\varphi(y) - \varphi(x^*) =
\frac{1}{2} \|y - x^*\|_A^2$ for the solution $x^*$ of $Ax^* = b$, and, over $\mathbb{R}$, the
formula $\nabla \varphi(x) = Ax - b$ for the gradient. It also defines a copy of $E$ that carries
the energy inner product, so that the orthogonal projection theory of Mathlib applies to
$A$-orthogonal projections.

## Main definitions

* `energyInner` and `energyNorm`: the energy inner product and the energy norm on $E$ itself. They
  are defined for every $A$ and are useful without any hypothesis on it.
* `energyFunctional`: the energy $\varphi(x) = \frac{1}{2} \operatorname{Re} \langle Ax, x \rangle -
  \operatorname{Re} \langle b, x \rangle$ of the system $Ax = b$.
* `WithEnergy`: the type synonym of $E$ that carries the energy inner product of a symmetric
  coercive $A$.
* `WithEnergy.equiv`: the identity map from $E$ to the energy space `WithEnergy A hA`, as a linear
  equivalence along which the inner product theory of Mathlib is transported.

## Main results

* `LinearMap.IsSymmetricCoercive.energyNorm_sq` and
  `LinearMap.IsSymmetricCoercive.energyNorm_eq_zero_iff`: $\|x\|_A^2 = \operatorname{Re} \langle Ax,
  x \rangle$, and $\|x\|_A = 0$ only for $x = 0$.
* `LinearMap.IsCoerciveWith.norm_le_energyNorm` and
  `LinearMap.IsSymmetricCoercive.energyNorm_le_norm`: $\sqrt{c} \|x\| \le \|x\|_A \le \sqrt{\|A\|}
  \|x\|$.
* `LinearMap.IsSymmetricCoercive.abs_energyInner_le`: the Cauchy–Schwarz inequality for the energy
  inner product.
* `LinearMap.IsSymmetricCoercive.energyFunctional_sub_eq`: $\varphi(y) - \varphi(x^*) = \frac{1}{2}
  \|y - x^*\|_A^2$ when $Ax^* = b$.
* `WithEnergy.inner_equiv` and `WithEnergy.norm_equiv`: the inner product and the norm of the energy
  space are the energy inner product and the energy norm.
* `WithEnergy.instCompleteSpace_of_continuousLinearMap`: for a bounded $A$ on a Hilbert space, the
  energy space is complete.
* `hasGradientAt_energyFunctional`: over $\mathbb{R}$, for a bounded symmetric $A$ on a Hilbert
  space, $\nabla \varphi(x) = Ax - b$.

## Notation

These notations are scoped in `Energy`.

* `⟪x, y⟫_[A]`: the energy inner product `energyInner A x y`.
* `‖x‖_[A]`: the energy norm `energyNorm A x`.

## Implementation notes

* The plain algebraic instances on `WithEnergy A hA` are local. Only the instances derived from
  `WithEnergy.core` are global, following Mathlib's `Matrix.toInnerProductSpace`. This avoids a
  diamond of `AddCommMonoid` instances between the two routes.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The **energy inner product** of an operator $A$ on $E$:
$\langle x, y \rangle_A = \langle Ax, y \rangle$. -/
noncomputable def energyInner (A : E →ₗ[𝕜] E) (x y : E) : 𝕜 := inner 𝕜 (A x) y

/-- The **energy norm** of an operator $A$ on $E$: $\|x\|_A = \sqrt{\operatorname{Re} \langle Ax, x
\rangle}$.

The square root is `Real.sqrt`, which is $0$ at negative arguments, so the definition makes
sense for every $A$. -/
noncomputable def energyNorm (A : E →ₗ[𝕜] E) (x : E) : ℝ :=
  Real.sqrt (RCLike.re (inner 𝕜 (A x) x))

scoped[Energy] notation "⟪" x ", " y "⟫_[" A "]" => energyInner A x y
scoped[Energy] notation "‖" x "‖_[" A "]" => energyNorm A x

/-- The energy norm is nonnegative, $\|x\|_A \ge 0$, for every operator $A$ and every $x \in E$.

It is a square root. The tactic `positivity` does not see through `energyNorm`, so this lemma
has to be applied by hand. -/
theorem energyNorm_nonneg (A : E →ₗ[𝕜] E) (x : E) : 0 ≤ energyNorm A x := Real.sqrt_nonneg _

/-- The energy norm is even: $\|-x\|_A = \|x\|_A$ for every operator $A$ and every $x \in E$. -/
@[simp]
theorem energyNorm_neg (A : E →ₗ[𝕜] E) (x : E) : energyNorm A (-x) = energyNorm A x := by
  simp [energyNorm]

/-- The energy norm of a difference is symmetric: $\|x - y\|_A = \|y - x\|_A$ for every operator $A$
and all $x, y \in E$. -/
theorem energyNorm_sub_comm (A : E →ₗ[𝕜] E) (x y : E) :
    energyNorm A (x - y) = energyNorm A (y - x) := by
  rw [← neg_sub, energyNorm_neg]

/-- The **energy functional** of the system $Ax = b$, for an operator $A$ on $E$ and $b \in E$:
$$\varphi(x) = \tfrac{1}{2} \operatorname{Re} \langle Ax, x \rangle - \operatorname{Re} \langle
  b, x \rangle.$$
This is the functional of §4.3.3 and (7.35) of [quarteroni2000numerical] and of (2.1) of
[fong2012cg].

For symmetric coercive $A$ its unique minimizer is the solution of $Ax = b$, and Galerkin
iterates minimize it over affine subspaces (`IsGalerkin.quadratic_le` in
`Numlib.Projection.Optimality`). It is defined for every $A$; the hypotheses enter only in the
statements about it. -/
noncomputable def energyFunctional (A : E →ₗ[𝕜] E) (b x : E) : ℝ :=
  RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x)

namespace LinearMap

variable {A : E →ₗ[𝕜] E}

/-- The energy form $(x, y) \mapsto \langle Ax, y \rangle$ of a symmetric coercive $A$, as a
pre-inner-product core on $E$ itself, used to get the Cauchy–Schwarz inequality before the type
synonym `WithEnergy` is available. -/
@[instance_reducible]
private noncomputable def energyPreCore (hA : A.IsSymmetricCoercive) :
    PreInnerProductSpace.Core 𝕜 E where
  inner x y := inner 𝕜 (A x) y
  conj_inner_symm x y := by
    show starRingEnd 𝕜 (inner 𝕜 (A y) x) = inner 𝕜 (A x) y
    rw [inner_conj_symm, hA.isSymmetric x y]
  re_inner_nonneg x := hA.isPositive.re_inner_nonneg_left x
  add_left x y z := by show inner 𝕜 (A (x + y)) z = _; simp [inner_add_left]
  smul_left x y r := by show inner 𝕜 (A (r • x)) y = _; simp [inner_smul_left]

/-- Let $A$ be symmetric coercive on $E$. Then $\|x\|_A^2 = \operatorname{Re} \langle Ax, x \rangle$
for every $x \in E$.

This is the form to rewrite with, since the quadratic form is what the estimates use. -/
theorem IsSymmetricCoercive.energyNorm_sq (hA : A.IsSymmetricCoercive) (x : E) :
    energyNorm A x ^ 2 = RCLike.re (inner 𝕜 (A x) x) :=
  Real.sq_sqrt (hA.isPositive.re_inner_nonneg_left x)

/-- Let $A$ be symmetric coercive on $E$. Then $\|x\|_A = 0$ if and only if $x = 0$.

This is where coercivity is used; positivity alone would give a seminorm. -/
theorem IsSymmetricCoercive.energyNorm_eq_zero_iff (hA : A.IsSymmetricCoercive) {x : E} :
    energyNorm A x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, energyNorm]⟩
  by_contra hx
  have hpos := hA.isCoercive.inner_self_pos hx
  rw [← hA.energyNorm_sq, h] at hpos
  simp at hpos

/-- Let $A$ be symmetric coercive on $E$ and let $x \neq 0$. Then $\|x\|_A > 0$. -/
theorem IsSymmetricCoercive.energyNorm_pos (hA : A.IsSymmetricCoercive) {x : E} (hx : x ≠ 0) :
    0 < energyNorm A x :=
  (energyNorm_nonneg A x).lt_of_ne fun h => hx (hA.energyNorm_eq_zero_iff.1 h.symm)

/-- Let $A$ be an operator on $E$ that is coercive with constant $c \ge 0$. Then
$\sqrt{c} \|x\| \le \|x\|_A$ for every $x \in E$. No symmetry is needed. -/
theorem IsCoerciveWith.norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (hA : A.IsCoerciveWith c) (x : E) :
    Real.sqrt c * ‖x‖ ≤ energyNorm A x := by
  have h1 : Real.sqrt c * ‖x‖ = Real.sqrt (c * ‖x‖ ^ 2) := by
    rw [Real.sqrt_mul hc, Real.sqrt_sq (norm_nonneg x)]
  rw [h1, energyNorm]
  exact Real.sqrt_le_sqrt (hA x)

/-- Let $A$ be a bounded symmetric coercive operator on $E$. Then $\|x\|_A \le \sqrt{\|A\|} \|x\|$
for every $x \in E$. -/
theorem IsSymmetricCoercive.energyNorm_le_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) (x : E) :
    energyNorm (A : E →ₗ[𝕜] E) x ≤ Real.sqrt ‖A‖ * ‖x‖ := by
  have hsq : energyNorm (A : E →ₗ[𝕜] E) x ^ 2 ≤ (Real.sqrt ‖A‖ * ‖x‖) ^ 2 := by
    rw [hA.energyNorm_sq, mul_pow, Real.sq_sqrt (norm_nonneg A)]
    calc RCLike.re (inner 𝕜 (A x) x) ≤ ‖inner 𝕜 (A x) x‖ := RCLike.re_le_norm _
      _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖x‖ * ‖x‖ := by gcongr; exact A.le_opNorm x
      _ = ‖A‖ * ‖x‖ ^ 2 := by ring
  have h2 : (0 : ℝ) ≤ Real.sqrt ‖A‖ * ‖x‖ := by positivity
  nlinarith

/-- Let $A$ be symmetric coercive on $E$, let $b, x^*, x \in E$, and let $Ax^* = b$. Then the energy
norm of the error is given by the residual $r = b - Ax$:
$$\|x^* - x\|_A^2 = \operatorname{Re} \langle x^* - x, b - Ax \rangle.$$
-/
theorem IsSymmetricCoercive.energyNorm_error_sq_eq (hA : A.IsSymmetricCoercive) {b xstar x : E}
    (hstar : A xstar = b) :
    energyNorm A (xstar - x) ^ 2 = RCLike.re (inner 𝕜 (xstar - x) (b - A x)) := by
  rw [hA.energyNorm_sq, map_sub, hstar, ← inner_conj_symm (b - A x) (xstar - x), RCLike.conj_re]

/-- Let $A$ be a symmetric operator on $E$ and let $b, x, v \in E$. The energy functional has the
exact second-order expansion
$$\varphi(x + v) = \varphi(x) + \operatorname{Re} \langle Ax - b, v \rangle + \tfrac{1}{2}
  \operatorname{Re} \langle Av, v \rangle.$$

The linear term pairs the gradient $Ax - b = -r$ with $v$, and the quadratic term is half the
energy quadratic form. Only symmetry of $A$ is used. -/
theorem IsSymmetric.energyFunctional_add (hA : A.IsSymmetric) (b x v : E) :
    energyFunctional A b (x + v)
      = energyFunctional A b x + RCLike.re (inner 𝕜 (A x - b) v)
        + RCLike.re (inner 𝕜 (A v) v) / 2 := by
  have h : RCLike.re (inner 𝕜 (A v) x) = RCLike.re (inner 𝕜 (A x) v) := by
    rw [hA v x, ← inner_conj_symm]
    exact RCLike.conj_re _
  simp only [energyFunctional, map_add, inner_add_left, inner_add_right, inner_sub_left, map_sub]
  rw [h]
  ring

/-- Let $A$ be symmetric coercive on $E$, let $b, x^* \in E$ with $Ax^* = b$, and let $y \in E$.
Then the energy functional exceeds its value at $x^*$ by half the squared energy norm of the
error:
$$\varphi(y) - \varphi(x^*) = \tfrac{1}{2} \|y - x^*\|_A^2.$$
This is (4.35) of [quarteroni2000numerical].

So $x^*$ is the strict global minimizer of $\varphi$, and to minimize $\varphi$ over a set is to
minimize the energy-norm error over it. -/
theorem IsSymmetricCoercive.energyFunctional_sub_eq (hA : A.IsSymmetricCoercive) {b xstar : E}
    (hstar : A xstar = b) (y : E) :
    energyFunctional A b y - energyFunctional A b xstar = energyNorm A (y - xstar) ^ 2 / 2 := by
  have h := hA.isSymmetric.energyFunctional_add b xstar (y - xstar)
  rw [add_sub_cancel, hstar, sub_self, inner_zero_left, map_zero, add_zero] at h
  rw [h, hA.energyNorm_sq]
  ring

/-- The **Cauchy–Schwarz inequality for the energy inner product**. Let $A$ be symmetric coercive on
$E$. Then $|\langle x, y \rangle_A| \le \|x\|_A \|y\|_A$ for all $x, y \in E$. -/
theorem IsSymmetricCoercive.abs_energyInner_le (hA : A.IsSymmetricCoercive) (x y : E) :
    ‖energyInner A x y‖ ≤ energyNorm A x * energyNorm A y := by
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 E _ _ _ (energyPreCore hA) x y
  have hsym : ‖inner 𝕜 (A y) x‖ = ‖inner 𝕜 (A x) y‖ := by
    rw [hA.isSymmetric y x, ← inner_conj_symm (A x) y, RCLike.norm_conj]
  refine nonneg_le_nonneg_of_sq_le_sq
    (mul_nonneg (energyNorm_nonneg A x) (energyNorm_nonneg A y)) ?_
  calc ‖energyInner A x y‖ * ‖energyInner A x y‖
      = ‖inner 𝕜 (A x) y‖ * ‖inner 𝕜 (A y) x‖ := by rw [hsym]; rfl
    _ ≤ RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 (A y) y) := hcs
    _ = energyNorm A x * energyNorm A y * (energyNorm A x * energyNorm A y) := by
        rw [← hA.energyNorm_sq x, ← hA.energyNorm_sq y]; ring

end LinearMap

/-- The **energy space** of a symmetric coercive operator $A$ on $E$: a type synonym of $E$ that
carries the energy inner product $\langle x, y \rangle_A = \langle Ax, y \rangle$. -/
def WithEnergy (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetricCoercive) : Type _ := E

namespace WithEnergy

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)

/-- The identity map from $E$ to the energy space `WithEnergy A hA`, defined before any instance
exists. -/
def toEnergy : E → WithEnergy A hA := id

/-- The identity map from the energy space `WithEnergy A hA` to $E$. -/
def ofEnergy : WithEnergy A hA → E := id

section Build

-- These are *local*: they only serve to state the core.  See the implementation note above.
local instance addCommGroup : AddCommGroup (WithEnergy A hA) := inferInstanceAs (AddCommGroup E)
local instance module : Module 𝕜 (WithEnergy A hA) := inferInstanceAs (Module 𝕜 E)

/-- The energy inner product $\langle x, y \rangle_A = \langle Ax, y \rangle$ as an inner product
core on the energy space. Definiteness comes from coercivity of $A$. -/
@[instance_reducible]
noncomputable def core : InnerProductSpace.Core 𝕜 (WithEnergy A hA) where
  inner x y := inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA y)
  conj_inner_symm := by
    intro x y
    show starRingEnd 𝕜 (inner 𝕜 (A (ofEnergy A hA y)) (ofEnergy A hA x)) = _
    rw [inner_conj_symm, hA.isSymmetric (ofEnergy A hA x) (ofEnergy A hA y)]
  re_inner_nonneg := by
    intro x
    exact hA.isPositive.re_inner_nonneg_left (ofEnergy A hA x)
  add_left := by
    intro x y z
    change inner 𝕜 (A (ofEnergy A hA x + ofEnergy A hA y)) (ofEnergy A hA z) = _
    simp [inner_add_left]
  smul_left := by
    intro x y r
    change inner 𝕜 (A (r • ofEnergy A hA x)) (ofEnergy A hA y) = _
    simp [inner_smul_left]
  definite := by
    intro x hx
    change ofEnergy A hA x = (0 : E)
    by_contra hx0
    have := hA.isCoercive.inner_self_pos hx0
    rw [show inner 𝕜 (A (ofEnergy A hA x)) (ofEnergy A hA x) = 0 from hx] at this
    simp at this

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (WithEnergy A hA) :=
  (core A hA).toNormedAddCommGroup

noncomputable instance instInnerProductSpace : InnerProductSpace 𝕜 (WithEnergy A hA) :=
  InnerProductSpace.ofCore (core A hA).toCore

end Build

/-- The identity map from $E$ to the energy space `WithEnergy A hA`, as a linear equivalence.

It is defined after the global instances so that it refers to them. -/
def equiv : E ≃ₗ[𝕜] WithEnergy A hA where
  toFun := toEnergy A hA
  invFun := ofEnergy A hA
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inner product of the energy space is the energy inner product of $E$: $\langle \Phi x, \Phi
y \rangle = \langle x, y \rangle_A$, where $\Phi$ is `WithEnergy.equiv`.

This makes $\Phi$ the bridge along which the inner product theory of Mathlib is transported. -/
@[simp]
theorem inner_equiv (x y : E) : inner 𝕜 (equiv A hA x) (equiv A hA y) = energyInner A x y := rfl

/-- The norm of the energy space is the energy norm of $E$: $\|\Phi x\| = \|x\|_A$, where $\Phi$ is
`WithEnergy.equiv`. So distances in the energy space are energy distances. -/
@[simp]
theorem norm_equiv (x : E) : ‖equiv A hA x‖ = energyNorm A x := rfl

/-- Orthogonality in the energy space is $A$-conjugacy: $\langle \Phi x, \Phi y \rangle = 0$ if and
only if $\langle Ax, y \rangle = 0$, where $\Phi$ is `WithEnergy.equiv`. -/
theorem inner_equiv_eq_zero_iff (x y : E) :
    inner 𝕜 (equiv A hA x) (equiv A hA y) = 0 ↔ inner 𝕜 (A x) y = 0 := Iff.rfl

/-- The image of a subspace $K$ of $E$ in the energy space under `WithEnergy.equiv`. -/
noncomputable def submoduleMap (K : Submodule 𝕜 E) : Submodule 𝕜 (WithEnergy A hA) :=
  K.map (equiv A hA).toLinearMap

instance (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] :
    FiniteDimensional 𝕜 (submoduleMap A hA K) := by
  unfold submoduleMap; infer_instance

/-- A vector $x \in E$ lies in a subspace $K$ if and only if its image in the energy space lies in
the image of $K$. -/
theorem equiv_mem_submoduleMap_iff {K : Submodule 𝕜 E} {x : E} :
    equiv A hA x ∈ submoduleMap A hA K ↔ x ∈ K := by
  rw [submoduleMap, Submodule.mem_map]
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hy, hxy⟩
  rwa [(equiv A hA).injective hxy] at hy

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- The energy space of a finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional : FiniteDimensional 𝕜 (WithEnergy A hA) :=
  (equiv A hA).finiteDimensional

/-- The energy space of a finite-dimensional space is complete. -/
instance instCompleteSpace : CompleteSpace (WithEnergy A hA) :=
  FiniteDimensional.complete 𝕜 _

end FiniteDimensional

/-- Let $A$ be a bounded symmetric coercive operator on $E$. Then the identity map
`WithEnergy.equiv` from $E$ to the energy space and its inverse are continuous.

The energy norm is equivalent to the norm of $E$ by
`LinearMap.IsCoerciveWith.norm_le_energyNorm` and
`LinearMap.IsSymmetricCoercive.energyNorm_le_norm`. -/
theorem continuous_equiv {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) :
    Continuous (equiv (A : E →ₗ[𝕜] E) hA) ∧ Continuous (equiv (A : E →ₗ[𝕜] E) hA).symm := by
  obtain ⟨c, hc, hco⟩ := hA.isCoercive
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨AddMonoidHomClass.continuous_of_bound (equiv (A : E →ₗ[𝕜] E) hA)
      (Real.sqrt ‖A‖) fun x => ?_,
    AddMonoidHomClass.continuous_of_bound (equiv (A : E →ₗ[𝕜] E) hA).symm
      (Real.sqrt c)⁻¹ fun x => ?_⟩
  · exact hA.energyNorm_le_norm x
  · change ‖ofEnergy (A : E →ₗ[𝕜] E) hA x‖ ≤ (Real.sqrt c)⁻¹ * ‖x‖
    have h := hco.norm_le_energyNorm hc.le (ofEnergy (A : E →ₗ[𝕜] E) hA x)
    have hx : energyNorm (A : E →ₗ[𝕜] E) (ofEnergy (A : E →ₗ[𝕜] E) hA x) = ‖x‖ := rfl
    rw [hx] at h
    rw [inv_mul_eq_div, le_div_iff₀ hsc, mul_comm]
    exact h

/-- Let $E$ be a Hilbert space and let $A$ be a bounded symmetric coercive operator on $E$. Then the
energy space of $A$ is complete.

The identity map from $E$ to the energy space is a continuous linear equivalence
(`WithEnergy.continuous_equiv`), hence a uniform embedding, and completeness transfers along it.
The finite-dimensional case is `WithEnergy.instCompleteSpace`. This form is needed for a Hilbert
basis of the energy space indexed by $\mathbb{N}$ and for the phase spaces of evolution
problems. It cannot be an instance, because instance search does not find the hypothesis `hA`. -/
theorem instCompleteSpace_of_continuousLinearMap [CompleteSpace E] {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) :
    CompleteSpace (WithEnergy (A : E →ₗ[𝕜] E) hA) :=
  (completeSpace_congr (e := (equiv (A : E →ₗ[𝕜] E) hA).toEquiv)
    ((equiv (A : E →ₗ[𝕜] E) hA).isUniformEmbedding (continuous_equiv hA).1
      (continuous_equiv hA).2)).1 inferInstance

end WithEnergy

/-!
### The gradient of the energy functional

Over $\mathbb{R}$ the energy functional of a bounded symmetric $A$ is differentiable everywhere,
with gradient $\nabla \varphi(x) = Ax - b$, the negative of the residual ((4.34) and §7.2.4 of
[quarteroni2000numerical]). So the projection methods of `Numlib.Projection` and the conjugate
gradient method are descent methods for $\varphi$, and the linear system $Ax = b$ is the
stationarity condition $\nabla \varphi = 0$.
-/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Let $F$ be a real inner product space, let $A$ be a bounded symmetric operator on $F$, and let
$b, x \in F$. Then the Fréchet derivative of the energy functional $\varphi$ at $x$ is the
functional
$$v \mapsto \langle Ax - b, v \rangle.$$
No completeness is needed for this form. -/
theorem hasFDerivAt_energyFunctional {A : F →L[ℝ] F} (hA : (A : F →ₗ[ℝ] F).IsSymmetric)
    (b x : F) :
    HasFDerivAt (energyFunctional (A : F →ₗ[ℝ] F) b) (innerSL ℝ (A x - b)) x := by
  have hfun : energyFunctional (A : F →ₗ[ℝ] F) b
      = fun y => 2⁻¹ * inner ℝ (A y) y - inner ℝ b y := by
    funext y; simp [energyFunctional, div_eq_inv_mul]
  have h1 : HasFDerivAt (fun y => inner ℝ (A y) y) (2 • innerSL ℝ (A x)) x := by
    refine ((A.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.coe_id', id_eq, smul_apply,
      innerSL_apply_apply, nsmul_eq_mul]
    have hs : inner ℝ (A v) x = inner ℝ v (A x) := by simpa using hA v x
    rw [hs, real_inner_comm (A x) v]
    ring
  have h2 : HasFDerivAt (fun y => inner ℝ b y) (innerSL ℝ b) x := (innerSL ℝ b).hasFDerivAt
  rw [hfun]
  refine ((HasFDerivAt.const_mul h1 (2⁻¹ : ℝ)).sub h2).congr_fderiv ?_
  ext v
  simp only [FunLike.coe_sub, Pi.sub_apply, smul_apply, innerSL_apply_apply,
    nsmul_eq_mul, smul_eq_mul, inner_sub_left]
  ring

/-- Let $F$ be a real Hilbert space, let $A$ be a bounded symmetric operator on $F$, and let
$b, x \in F$. Then the gradient of the energy functional at $x$ is
$$\nabla \varphi(x) = Ax - b,$$
the negative of the residual. This is (4.34) of [quarteroni2000numerical].

In particular the derivative of the gradient map is $A$ itself, the Hessian of $\varphi$.
Completeness is needed because Mathlib's `HasGradientAt` is defined through the Riesz
isomorphism; the derivative form `hasFDerivAt_energyFunctional` needs none. -/
theorem hasGradientAt_energyFunctional [CompleteSpace F] {A : F →L[ℝ] F}
    (hA : (A : F →ₗ[ℝ] F).IsSymmetric) (b x : F) :
    HasGradientAt (energyFunctional (A : F →ₗ[ℝ] F) b) (A x - b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : (InnerProductSpace.toDual ℝ F (A x - b) : F →L[ℝ] ℝ) = innerSL ℝ (A x - b) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  rw [h]
  exact hasFDerivAt_energyFunctional hA b x

/-- Let $F$ be a finite-dimensional real inner product space, let $A$ be a symmetric linear map on
$F$, and let $b, x \in F$. Then the gradient of the energy functional at $x$ is
$\nabla \varphi(x) = Ax - b$.

This is `hasGradientAt_energyFunctional` in finite dimension, where every linear map is bounded
and the space is complete. -/
theorem hasGradientAt_energyFunctional_of_finiteDimensional [FiniteDimensional ℝ F]
    {A : F →ₗ[ℝ] F} (hA : A.IsSymmetric) (b x : F) :
    HasGradientAt (energyFunctional A b) (A x - b) x := by
  have h := hasGradientAt_energyFunctional (A := LinearMap.toContinuousLinearMap A)
    (by simpa using hA) b x
  simpa using h

end Gradient
