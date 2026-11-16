/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Projection.Additive
import NumlibSurface.SaadSparse.Chapter05.Section01

/-!
# Saad, Section 5.4: Additive and multiplicative projection processes

This module formalizes Section 5.4 of [saad2003iterative], on projection processes that combine
several subspaces $K_1, \dots, K_p$ of $\mathbb{R}^n$. Each $K_i = \operatorname{span}(V_i)$ is the
column space of a matrix $V_i$. The additive procedure (Algorithm 5.5) corrects the current iterate
$x$ by all subspaces at once,
$$x_{\mathrm{new}} = x + \sum_{i=1}^{p} \omega_i V_i (V_i^T A V_i)^{-1} V_i^T (b - Ax),$$
and its residual satisfies (5.23), $r_{\mathrm{new}} = (I - \sum_i \omega_i P_i) r$ with
$P_i = A V_i (V_i^T A V_i)^{-1} V_i^T$. The multiplicative procedure (Algorithm 5.6) applies the
orthogonal projection step (5.7) over $K_1, \dots, K_p$ one after the other.

If every $V_i^T A V_i$ is nonsingular, then each pair $(K_i, K_i)$ is nondegenerate, and the two
algorithms are the additive and multiplicative processes of the backbone module
`Numlib.Projection.Additive`, which supplies their residual identities. The module also proves that
$P_i$ is the projector onto $A K_i$ orthogonally to $K_i$, treats the least-squares option
$L_i = A K_i$ with its exactness criterion, and proves the remark that each inner step of the block
relaxations of Section 4.1.1, formula (4.17), is the projection step (5.7) with $W = V = V_i$.

## Main definitions

* Section 5.4, `SaadSparse.Chapter05.ProjFamily`: a family of $p$ subspaces of $\mathbb{R}^n$, each
  given by a matrix of basis columns.
* Section 5.4, `SaadSparse.Chapter05.ProjFamily.subspace`: the subspace
  $K_i = \operatorname{span}(V_i)$.
* Section 5.4, `SaadSparse.Chapter05.P_i`: the projector $P_i = A V_i (V_i^T A V_i)^{-1} V_i^T$.
* Algorithm 5.5, `SaadSparse.Chapter05.additiveStep`: one step of the additive procedure with
  relaxation parameters $\omega_i$.
* Algorithm 5.6, `SaadSparse.Chapter05.multiplicativeSweep`: one sweep of the multiplicative
  procedure.

## Main results

* Equation (5.23), `SaadSparse.Chapter05.residual_additiveStep`: the residual of the additive step
  is $(I - \sum_i \omega_i P_i) r$.
* Section 5.4, `SaadSparse.Chapter05.P_i_isProjOnto`: $P_i$ is the projector onto $A K_i$
  orthogonally to $K_i$.
* Algorithm 5.5, `SaadSparse.Chapter05.additiveStep_eq`: the additive step is the backbone additive
  projection step.
* Algorithm 5.6, `SaadSparse.Chapter05.multiplicativeSweep_eq`: the multiplicative sweep is the
  backbone multiplicative projection sweep.
* Section 5.4, `SaadSparse.Chapter05.leastSquares_P_i_eq_starProjection`: with $L_i = A K_i$, the
  projector $P_i$ is the orthogonal projector onto $A K_i$.
* Section 5.4, `SaadSparse.Chapter05.sum_P_i_eq_one`: if the $A V_i$ are mutually orthogonal and the
  dimensions of the $A K_i$ add up to $n$, the least-squares projectors sum to $I$.
* Section 5.4, `SaadSparse.Chapter05.blockCorrection_eq_projStep`: the block-relaxation correction
  (4.17) is the projection step (5.7) with $W = V$.

## Implementation notes

* The subspaces of a family are indexed by `Fin p`, from $0$ to $p - 1$; the book numbers them from
  $1$ to $p$.
* The definitions use Lean's matrix inverse, which is $0$ at a singular matrix, so they are total.
  The theorems assume the nonsingularity of $V_i^T A V_i$ (or of $(A V_i)^T A V_i$) where they need
  it.
* The columns of a matrix $V$ are `Matrix.cols V`, and a projection approximation in the sense of
  (5.5)–(5.6) is `SaadSparse.Chapter05.IsProjectionApprox`.
-/

open Matrix Module Finset
open scoped SaadSparse

namespace SaadSparse.Chapter05

variable {n : ℕ}

/-- The Euclidean space $\mathbb{R}^n$, in which Chapter 5 of [saad2003iterative] works. -/
local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- **Section 5.4** of [saad2003iterative], the family of subspaces. An element consists of a number
$p$ of subspaces, their dimensions $n_1, \dots, n_p$, and for each $i$ a matrix
$V_i \in \mathbb{R}^{n \times n_i}$ whose columns span the subspace $K_i$.

The structure does not require the columns of $V_i$ to be linearly independent. They are
independent as soon as $V_i^T A V_i$ is nonsingular for some $A$
(`SaadSparse.Chapter05.linearIndependent_cols_of_isUnit`). -/
structure ProjFamily (n : ℕ) where
  /-- The number $p$ of subspaces. -/
  p : ℕ
  /-- The dimension $n_i$ of the $i$-th subspace, that is, the number of columns of $V_i$. -/
  size : Fin p → ℕ
  /-- The matrix $V_i \in \mathbb{R}^{n \times n_i}$ whose columns span the $i$-th subspace. -/
  V : ∀ i, Matrix (Fin n) (Fin (size i)) ℝ

/-- **Section 5.4** of [saad2003iterative]. The **subspace** $K_i = \operatorname{span}(V_i)
\subseteq \mathbb{R}^n$ spanned by the columns of the $i$-th matrix of the family. -/
def ProjFamily.subspace (𝒱 : ProjFamily n) (i : Fin 𝒱.p) : Submodule ℝ (E n) :=
  Submodule.span ℝ (Set.range (𝒱.V i).cols)

variable (𝒱 : ProjFamily n) (A : Matrix (Fin n) (Fin n) ℝ)

/-- The local correction matrix $V_i (V_i^T A V_i)^{-1} V_i^T$ of the $i$-th subspace, which maps
the residual to the correction of Algorithm 5.5 of [saad2003iterative]. It is $0$ when
$V_i^T A V_i$ is singular. -/
noncomputable def corrector (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- **Section 5.4** of [saad2003iterative], the display between (5.22) and (5.23). The **projector**
of the $i$-th subspace is
$$P_i = A V_i (V_i^T A V_i)^{-1} V_i^T.$$

It is the projector onto $A K_i$ orthogonally to $K_i$ when $V_i^T A V_i$ is nonsingular
(`SaadSparse.Chapter05.P_i_isProjOnto`). The matrix is $0$ when $V_i^T A V_i$ is singular. -/
noncomputable def P_i (i : Fin 𝒱.p) : Matrix (Fin n) (Fin n) ℝ :=
  A * 𝒱.V i * ((𝒱.V i)ᵀ * A * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ

/-- **Algorithm 5.5** of [saad2003iterative] (additive projection procedure). Given relaxation
parameters $\omega_1, \dots, \omega_p$, one step maps the iterate $x$ to
$$x + \sum_{i=1}^{p} \omega_i V_i (V_i^T A V_i)^{-1} V_i^T (b - Ax).$$

If $V_i^T A V_i$ is singular, Lean's matrix inverse is $0$ and the $i$-th correction vanishes. -/
noncomputable def additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) : E n :=
  x + ∑ i, ω i • ((corrector 𝒱 A i) ⬝ (b - (A ⬝ x)))

/-- **Algorithm 5.6** of [saad2003iterative] (multiplicative projection procedure). One sweep
applies, to the iterate $x$, the projection step (5.7) with $W = V = V_i$ for $i = 1, \dots, p$
in this order. Each step maps $y$ to $y + V_i (V_i^T A V_i)^{-1} V_i^T (b - Ay)$.

The step (5.7) is `SaadSparse.Chapter05.projStep`, and the sweep is a left fold over
`List.finRange p`. -/
noncomputable def multiplicativeSweep (b : E n) (x : E n) : E n :=
  (List.finRange 𝒱.p).foldl (fun y i => projStep A b (𝒱.V i) (𝒱.V i) y) x

variable {𝒱 A}

/-- The projector $P_i$ is the matrix (1.66) of [saad2003iterative] for the bases $A V_i$ and $V_i$:
$P_i = (A V_i) (V_i^T A V_i)^{-1} V_i^T$, which is `Matrix.obliqueProj (A * V i) (V i)`. -/
theorem P_i_eq_obliqueProj (i : Fin 𝒱.p) :
    P_i 𝒱 A i = Matrix.obliqueProj (A * 𝒱.V i) (𝒱.V i) := by
  rw [P_i, Matrix.obliqueProj, conjTranspose_eq_transpose, Matrix.mul_assoc (𝒱.V i)ᵀ A]

/-- The matrix $A$ times the local correction matrix of the $i$-th subspace is the projector:
$A \, V_i (V_i^T A V_i)^{-1} V_i^T = P_i$. -/
theorem mul_corrector (i : Fin 𝒱.p) : A * corrector 𝒱 A i = P_i 𝒱 A i := by
  rw [corrector, P_i, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- **Equation (5.23)** of [saad2003iterative]. For any relaxation parameters $\omega_i$, the
residual of one additive step from $x$ is
$$b - A x_{\mathrm{new}} = (b - Ax) - \sum_{i=1}^{p} \omega_i P_i (b - Ax).$$

No nonsingularity is needed: the identity follows from $A V_i (V_i^T A V_i)^{-1} V_i^T = P_i$,
which holds for Lean's total inverse. -/
theorem residual_additiveStep (ω : Fin 𝒱.p → ℝ) (b x : E n) :
    b - (A ⬝ additiveStep 𝒱 A ω b x) =
      (b - (A ⬝ x)) - ∑ i, ω i • ((P_i 𝒱 A i) ⬝ (b - (A ⬝ x))) := by
  rw [additiveStep, map_add, map_sum]
  simp only [map_smul, ← Matrix.toEuclideanLin_mul_apply, mul_corrector]
  abel

/-- **Section 5.4** of [saad2003iterative], the remark on block relaxation. For every matrix
$V \in \mathbb{R}^{n \times m}$, the block-relaxation correction (4.17),
$x + V (V^T A V)^{-1} V^T (b - Ax)$, is the projection step (5.7) with $W = V$. -/
theorem blockCorrection_eq_projStep {m : ℕ} (V : Matrix (Fin n) (Fin m) ℝ) (b x : E n) :
    x + ((V * (Vᵀ * A * V)⁻¹ * Vᵀ) ⬝ (b - (A ⬝ x))) = projStep A b V V x := rfl

/-! ### Identification with the backbone projection processes -/

section Backbone

variable {m : ℕ}

/-- The columns of $AV$ are the images under $A$ of the columns of $V$: the $j$-th column of $AV$ is
$A v_j$. -/
theorem cols_mul (A : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    (A * V).cols j = (A ⬝ V.cols j) :=
  congrArg (WithLp.toLp 2) (funext fun i => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply])

/-- The column space of $AV$ is the image under $A$ of the column space of $V$:
$\operatorname{span}(AV) = A \operatorname{span}(V)$. This is the test space of the
least-squares option. -/
theorem span_cols_mul (A : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ) :
    Submodule.span ℝ (Set.range (A * V).cols) =
      (Submodule.span ℝ (Set.range V.cols)).map (toEuclideanLin A) := by
  rw [Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℝ) (congrArg Set.range (funext (cols_mul A V)))

/-- The inner product of the $k$-th column of $X$ and the $l$-th column of $Y$ is the $(k, l)$ entry
of the cross Gram matrix $X^T Y$. -/
theorem inner_cols {m' : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (Y : Matrix (Fin n) (Fin m') ℝ)
    (k : Fin m) (l : Fin m') : inner ℝ (X.cols k) (Y.cols l) = (Xᵀ * Y) k l := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply]
  simp [dotProduct, Matrix.transpose_apply, mul_comm]

variable {A : Matrix (Fin n) (Fin n) ℝ} {V : Matrix (Fin n) (Fin m) ℝ}

/-- If $V^T A V$ is nonsingular, then the columns of $V$ are linearly independent: a relation
$Vc = 0$ gives $(V^T A V) c = 0$. -/
theorem linearIndependent_cols_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    LinearIndependent ℝ V.cols := by
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hV : V *ᵥ c = 0 := by
    have h0 : (V ⬝ (WithLp.toLp 2 c : E m)) = 0 := by
      rw [toEuclideanLin_apply_eq_sum]; exact hc
    exact congrArg WithLp.ofLp h0
  have hz : (Vᵀ * A * V) *ᵥ c = 0 := by
    rw [← mulVec_mulVec, hV, mulVec_zero]
  exact congrFun (mulVec_injective_iff_isUnit.mpr h (a₁ := c) (a₂ := 0)
    (by rw [hz, mulVec_zero]))

/-- If $V^T A V$ is nonsingular, then the columns of $AV$ are linearly independent. -/
theorem linearIndependent_cols_mul_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    LinearIndependent ℝ (A * V).cols := by
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hAV : (A * V) *ᵥ c = 0 := by
    have h0 : ((A * V) ⬝ (WithLp.toLp 2 c : E m)) = 0 := by
      rw [toEuclideanLin_apply_eq_sum]; exact hc
    exact congrArg WithLp.ofLp h0
  have hz : (Vᵀ * A * V) *ᵥ c = 0 := by
    rw [Matrix.mul_assoc, ← mulVec_mulVec, hAV, mulVec_zero]
  exact congrFun (mulVec_injective_iff_isUnit.mpr h (a₁ := c) (a₂ := 0)
    (by rw [hz, mulVec_zero]))

/-- If $V^T A V$ is nonsingular, then the columns of $V$ form a basis of their span. -/
theorem isBasisOf_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    V.IsBasisOf (Submodule.span ℝ (Set.range V.cols)) :=
  ⟨linearIndependent_cols_of_isUnit h, rfl⟩

/-- If $V^T A V$ is nonsingular, then the columns of $AV$ form a basis of
$A \operatorname{span}(V)$. -/
theorem isBasisOf_mul_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    (A * V).IsBasisOf ((Submodule.span ℝ (Set.range V.cols)).map (toEuclideanLin A)) :=
  ⟨linearIndependent_cols_mul_of_isUnit h, span_cols_mul A V⟩

/-- If $V^T A V$ is nonsingular, then $(\operatorname{span} V, \operatorname{span} V)$ is a
nondegenerate pair for $A$ in the sense of `Projection.IsNondegeneratePair`: the two spaces have
the same dimension, and no nonzero $z \in \operatorname{span} V$ has
$Az \perp \operatorname{span} V$.

This is the condition of Proposition 5.1 of [saad2003iterative] in the form that the backbone
uses. Only this direction is proved. -/
theorem isNondegeneratePair_of_isUnit (h : IsUnit (Vᵀ * A * V)) :
    Projection.IsNondegeneratePair (toEuclideanLin A) (Submodule.span ℝ (Set.range V.cols))
      (Submodule.span ℝ (Set.range V.cols)) :=
  ⟨rfl, (isUnit_transpose_mul_mul_iff (isBasisOf_of_isUnit h) (isBasisOf_of_isUnit h)).mp h⟩

/-- **Equation (5.7)** of [saad2003iterative]. Let the columns of $V$ be a basis of $K$, let the
columns of $W$ be a basis of $L$, and let $W^T A V$ be nonsingular. Then the step
$x' = x + V (W^T A V)^{-1} W^T (b - Ax)$ is a projection approximation onto $K$ orthogonally to
$L$, started from $x$: $x' - x \in K$ and $b - Ax' \perp L$. -/
theorem projStep_isProjectionApprox {W : Matrix (Fin n) (Fin m) ℝ} {K L : Submodule ℝ (E n)}
    (hV : V.IsBasisOf K) (hW : W.IsBasisOf L) (h : IsUnit (Wᵀ * A * V)) (b x : E n) :
    IsProjectionApprox A b x K L (projStep A b V W x) := by
  have hstep : projStep A b V W x = x +
      (V ⬝ (WithLp.toLp 2 ((Wᵀ * A * V)⁻¹ *ᵥ (Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x)))) : E m)) := by
    have hmul : (V * (Wᵀ * A * V)⁻¹ * Wᵀ) *ᵥ WithLp.ofLp (b - (A ⬝ x))
        = V *ᵥ ((Wᵀ * A * V)⁻¹ *ᵥ (Wᵀ *ᵥ WithLp.ofLp (b - (A ⬝ x)))) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec]
    exact congrArg (fun z : E n => x + z) (congrArg (WithLp.toLp 2) hmul)
  rw [hstep, isProjectionApprox_add_iff hV hW, mulVec_nonsing_inv_mulVec h]

/-- **Equation (5.7)** of [saad2003iterative] with $W = V$. If $V^T A V$ is nonsingular, then the
projection step $x + V (V^T A V)^{-1} V^T (b - Ax)$ is the backbone Petrov–Galerkin step
`Projection.pairStep` of the pair $(\operatorname{span} V, \operatorname{span} V)$. -/
theorem projStep_eq_pairStep (h : IsUnit (Vᵀ * A * V)) (b x : E n) :
    projStep A b V V x =
      Projection.pairStep (toEuclideanLin A) b (Submodule.span ℝ (Set.range V.cols))
        (Submodule.span ℝ (Set.range V.cols)) (isNondegeneratePair_of_isUnit h) x :=
  (isProjectionApprox_iff.mp
      (projStep_isProjectionApprox (isBasisOf_of_isUnit h) (isBasisOf_of_isUnit h) h b
        x)).eq_of_forall
    (Projection.pairStep_isPetrovGalerkin (isNondegeneratePair_of_isUnit h) x)
    (isNondegeneratePair_of_isUnit h).eq_zero_of_mem_orthogonal

end Backbone

section Family

variable {𝒲 : ProjFamily n} {A : Matrix (Fin n) (Fin n) ℝ}

/-- If $V_i^T A V_i$ is nonsingular for every $i$, then each pair $(K_i, K_i)$ is nondegenerate for
$A$ in the sense of `Projection.IsNondegeneratePair`. This is the hypothesis of the backbone
additive and multiplicative processes. -/
theorem isNondegeneratePair_subspace (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (i : Fin 𝒲.p) :
    Projection.IsNondegeneratePair (toEuclideanLin A) (𝒲.subspace i) (𝒲.subspace i) :=
  isNondegeneratePair_of_isUnit (h i)

/-- If $V_i^T A V_i$ is nonsingular for every $i$, then the projection step (5.7) of
[saad2003iterative] with $W = V = V_i$ is the backbone Petrov–Galerkin step
`Projection.pairStep` of the pair $(K_i, K_i)$. -/
theorem projStep_eq_pairStep_subspace (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (i : Fin 𝒲.p)
    (b x : E n) :
    projStep A b (𝒲.V i) (𝒲.V i) x =
      Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i) (𝒲.subspace i)
        (isNondegeneratePair_subspace h i) x :=
  projStep_eq_pairStep (h i) b x

/-- **Section 5.4** of [saad2003iterative], the sentence after the display of $P_i$. Let
$V_i^T A V_i$ be nonsingular. Then for every $z \in \mathbb{R}^n$ the vector $P_i z$ is the
projection of $z$ onto $A K_i$ orthogonally to $K_i$:
$$P_i z \in A K_i \quad \text{and} \quad z - P_i z \perp K_i.$$

The projection is `SaadSparse.IsProjOnto`, the definition (1.59)–(1.60). -/
theorem P_i_isProjOnto {i : Fin 𝒲.p} (h : IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (z : E n) :
    SaadSparse.IsProjOnto ((𝒲.subspace i).map (toEuclideanLin A)) (𝒲.subspace i) z
      ((P_i 𝒲 A i) ⬝ z) := by
  have hunit : IsUnit ((𝒲.V i)ᴴ * (A * 𝒲.V i)) := by
    rwa [conjTranspose_eq_transpose, ← Matrix.mul_assoc]
  rw [P_i_eq_obliqueProj]
  exact SaadSparse.Chapter01.obliqueProj_isProjOnto (isBasisOf_mul_of_isUnit h)
    (isBasisOf_of_isUnit h) hunit z

/-- **Algorithm 5.5** of [saad2003iterative], identification with the backbone. Let $V_i^T A V_i$ be
nonsingular for every $i$. Then for all relaxation parameters $\omega_i$ and all $b$, $x$, the
additive step is the backbone step `Projection.additiveStep`,
$$x + \sum_{i=1}^{p} \omega_i (\tilde x_i - x),$$
where $\tilde x_i$ is the Petrov–Galerkin step from $x$ for the pair $(K_i, K_i)$.

The residual identity (5.23) is therefore also `Projection.residual_additiveStep`. -/
theorem additiveStep_eq (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (ω : Fin 𝒲.p → ℝ) (b x : E n) :
    additiveStep 𝒲 A ω b x =
      Projection.additiveStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) ω x := by
  have hlhs : additiveStep 𝒲 A ω b x
      = x + ∑ i, ω i • ((corrector 𝒲 A i) ⬝ (b - (A ⬝ x))) := rfl
  have hrhs : Projection.additiveStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) ω x
      = x + ∑ i, ω i • (Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i) (𝒲.subspace i)
          (isNondegeneratePair_subspace h i) x - x) := rfl
  rw [hlhs, hrhs]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  refine congrArg (fun z : E n => ω i • z) ?_
  have hstep : projStep A b (𝒲.V i) (𝒲.V i) x = x + ((corrector 𝒲 A i) ⬝ (b - (A ⬝ x))) := rfl
  rw [← projStep_eq_pairStep_subspace h i b x, hstep]
  abel

/-- **Algorithm 5.6** of [saad2003iterative], identification with the backbone. Let $V_i^T A V_i$ be
nonsingular for every $i$. Then the multiplicative sweep is the backbone sweep
`Projection.multiplicativeStep` over the subspaces $K_1, \dots, K_p$ in this order.

By `Projection.residual_multiplicativeStep`, the residual after the sweep is
$(I - P_p) \cdots (I - P_1) (b - Ax)$. -/
theorem multiplicativeSweep_eq (h : ∀ i, IsUnit ((𝒲.V i)ᵀ * A * 𝒲.V i)) (b x : E n) :
    multiplicativeSweep 𝒲 A b x =
      Projection.multiplicativeStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) (List.finRange 𝒲.p) x := by
  have hfun : (fun (y : E n) (i : Fin 𝒲.p) => projStep A b (𝒲.V i) (𝒲.V i) y) =
      fun (y : E n) (i : Fin 𝒲.p) => Projection.pairStep (toEuclideanLin A) b (𝒲.subspace i)
        (𝒲.subspace i) (isNondegeneratePair_subspace h i) y :=
    funext fun y => funext fun i => projStep_eq_pairStep_subspace h i b y
  have hlhs : multiplicativeSweep 𝒲 A b x
      = (List.finRange 𝒲.p).foldl (fun y i => projStep A b (𝒲.V i) (𝒲.V i) y) x := rfl
  have hrhs : Projection.multiplicativeStep (toEuclideanLin A) b 𝒲.subspace 𝒲.subspace
        (isNondegeneratePair_subspace h) (List.finRange 𝒲.p) x
      = (List.finRange 𝒲.p).foldl (fun y i => Projection.pairStep (toEuclideanLin A) b
          (𝒲.subspace i) (𝒲.subspace i) (isNondegeneratePair_subspace h i) y) x := rfl
  rw [hlhs, hrhs, hfun]

/-! ### The least-squares option -/

/-- **Section 5.4** of [saad2003iterative], the remark after (5.23) on the choice $L_i = A K_i$. Let
$(A V_i)^T (A V_i)$ be nonsingular. Then the matrix
$$A V_i \big((A V_i)^T A V_i\big)^{-1} (A V_i)^T$$
is the orthogonal projector onto $A K_i$.

The matrix is `Matrix.obliqueProj (A * V i) (A * V i)`, and the orthogonal projector is
`Submodule.starProjection`. -/
theorem leastSquares_P_i_eq_starProjection {i : Fin 𝒲.p}
    (h : IsUnit ((A * 𝒲.V i)ᵀ * (A * 𝒲.V i))) :
    toEuclideanLin (Matrix.obliqueProj (A * 𝒲.V i) (A * 𝒲.V i)) =
      (((𝒲.subspace i).map (toEuclideanLin A)).starProjection : (E n) →ₗ[ℝ] (E n)) := by
  have hg : IsUnit (LinearMap.crossGram ℝ (A * 𝒲.V i).cols (A * 𝒲.V i).cols) := by
    rw [Matrix.crossGram_cols, conjTranspose_eq_transpose]
    exact h
  have hmap : ((𝒲.subspace i).map (toEuclideanLin A))
      = Submodule.span ℝ (Set.range (A * 𝒲.V i).cols) := (span_cols_mul A (𝒲.V i)).symm
  rw [Matrix.toEuclideanLin_obliqueProj]
  refine LinearMap.ext fun z => (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [hmap, ← LinearMap.range_obliqueProjectionOfBases _ _ hg]
    exact LinearMap.mem_range_self _ z
  · rw [hmap]
    exact LinearMap.sub_obliqueProjectionOfBases_apply_mem_orthogonal _ _ hg z

/-- **Section 5.4** of [saad2003iterative], the exactness remark after (5.23). Suppose that
$(A V_i)^T (A V_j) = 0$ for $i \neq j$, that every $(A V_i)^T (A V_i)$ is nonsingular, and that
$\sum_i \dim (A K_i) = n$. Then the least-squares projectors sum to the identity:
$$\sum_{i=1}^{p} A V_i \big((A V_i)^T A V_i\big)^{-1} (A V_i)^T = I.$$

By (5.23) with $\omega_i = 1$, one step of the least-squares additive process then gives the
exact solution. This consequence is not stated as a separate declaration. -/
theorem sum_P_i_eq_one (horth : ∀ i j, i ≠ j → (A * 𝒲.V i)ᵀ * (A * 𝒲.V j) = 0)
    (h : ∀ i, IsUnit ((A * 𝒲.V i)ᵀ * (A * 𝒲.V i)))
    (hdim : ∑ i, finrank ℝ ((𝒲.subspace i).map (toEuclideanLin A)) = n) :
    ∑ i, Matrix.obliqueProj (A * 𝒲.V i) (A * 𝒲.V i) = 1 := by
  have hspan : ∀ i, ((𝒲.subspace i).map (toEuclideanLin A))
      = Submodule.span ℝ (Set.range (A * 𝒲.V i).cols) :=
    fun i => (span_cols_mul A (𝒲.V i)).symm
  have horth' : ∀ i j, i ≠ j → Submodule.IsOrtho ((𝒲.subspace i).map (toEuclideanLin A))
      ((𝒲.subspace j).map (toEuclideanLin A)) := by
    intro i j hij
    rw [hspan i, hspan j, Submodule.isOrtho_span]
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    rw [inner_cols, horth i j hij, Matrix.zero_apply]
  have hkey := Projection.sum_starProjection_eq_one_of_orthogonal
    (fun i => (𝒲.subspace i).map (toEuclideanLin A)) horth'
    (by rw [hdim, finrank_euclideanSpace_fin])
  refine toEuclideanLin.injective ?_
  rw [map_sum, toEuclideanLin_one]
  simp only [fun i => leastSquares_P_i_eq_starProjection (𝒲 := 𝒲) (A := A) (i := i) (h i)]
  rw [← ContinuousLinearMap.toLinearMap_sum, hkey]
  rfl

end Family

end SaadSparse.Chapter05
