/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.DomainDecomposition.Schwarz
import Numlib.Multigrid.Basic
import Numlib.Projection.Additive
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 12.2: Overlapping block-Jacobi preconditioners

This module formalizes Section 12.2 of [saad2003iterative]. The section takes index sets
$S_1, \dots, S_p$ that may overlap and runs block Jacobi on them. With $V_i = [e_j : j \in S_i]$ and
$A_i = V_i^T A V_i$, one step with relaxation weights $\omega_i$ is
$$x_{k+1} = x_k + \sum_i \omega_i V_i A_i^{-1} V_i^T r_k, \qquad r_k = b - A x_k,$$
and its residual is $r_{k+1} = [I - \sum_i \omega_i A V_i A_i^{-1} V_i^T] r_k$. The local problems
are well posed because $A$ is assumed positive definite, so that each $A_i$ is positive definite.

The matrix $V_i A_i^{-1} V_i^T$ is the subdomain solve $T_i$ of (14.31), and $V_i A_i^{-1} V_i^T A$
is the $A$-orthogonal projector onto $K_i = \operatorname{span}\{e_j : j \in S_i\}$: Section 12.2
and Section 14.3.3 describe the same operator, as the book says in Section 14.3.3. So the step is
the additive projection process of Section 5.4 on the coordinate subspaces $K_i$, and the residual
identity specializes `Projection.residual_additiveStep` of `Numlib.Projection.Additive`. The
projector is identified with `Schwarz.energyProjection` of `Numlib.DomainDecomposition.Schwarz`.
This module names the shared vocabulary, and the modules of Section 14.3 use it; the weights
$\omega_i$ are what Section 12.2 adds to Section 14.3.3.

## Main definitions

* Section 12.2, `SaadSparse.Chapter12.restrictSubset`: the boolean restriction matrix $R_S = V_S^T$.
* Section 12.2, `SaadSparse.Chapter12.subdomainSpace`: the subspace
  $K_S = \operatorname{span}\{e_j : j \in S\}$.
* Section 12.2, `SaadSparse.Chapter12.localMatrix`: the local matrix $A_S = V_S^T A V_S$.
* Section 12.2, `SaadSparse.Chapter12.subdomainInverse`: the block correction $V_S A_S^{-1} V_S^T$.
* Section 12.2, `SaadSparse.Chapter12.subdomainProjector`: the subdomain projector
  $P_S = V_S A_S^{-1} V_S^T A$.
* Section 12.2, `SaadSparse.Chapter12.blockJacobiStep`: one weighted step of the overlapping
  block-Jacobi iteration.

## Main results

* Section 12.2, `SaadSparse.Chapter12.range_restrictSubset_transpose`: the range of $V_S$ is $K_S$.
* Section 12.2, `SaadSparse.Chapter12.subdomainProjector_eq_energyProjection`: $P_S$ is the
  $A$-orthogonal projector onto $K_S$.
* Section 12.2, `SaadSparse.Chapter12.isNondegeneratePair_subdomainSpace`: $(K_S, K_S)$ is a
  nondegenerate pair for a positive definite $A$.
* Section 12.2, `SaadSparse.Chapter12.pairStep_eq`: one block correction is one Galerkin projection
  step on $(K_S, K_S)$.
* Section 12.2, `SaadSparse.Chapter12.blockJacobiStep_eq_additiveStep`: the block-Jacobi step is the
  additive projection step on the subspaces $K_i$.
* Section 12.2, `SaadSparse.Chapter12.additiveProjector_eq`: the projector of the pair $(K_i, K_i)$
  is $A V_i A_i^{-1} V_i^T$.
* Section 12.2, closing residual display, `SaadSparse.Chapter12.equation_12_1`: the residual of one
  weighted block-Jacobi step.

## Conventions

* The scalar field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`[RCLike 𝕜]`), and
  $A \in \mathbb{K}^{n \times n}$. "Positive definite" is `Matrix.PosDef`, which includes that $A$
  is Hermitian.
* An index set $S$ is a `Finset (Fin n)`, with indices from $0$. The boolean matrix is named $R_S$,
  the notation of Section 14.3.1, in which the convergence theory of Section 14.3 is written; the
  book's $V_S$ of this section is $R_S^T$.
* The weights $\omega_i$ are scalars in $\mathbb{K}$, and the index sets are indexed by a finite
  type $\iota$.

## Deviations from the source

* **§12.2, overlapping blocks** (generalization). The coordinate sets are arbitrary finite
  subsets. The source constructs overlapping intervals. `SaadSparse.Chapter12.blockJacobiStep`
  uses scalar weights over the real or complex field. Its Galerkin and residual theorems take
  $A$ positive definite to ensure well-posed local solves.
* **(12.1)** (source location). `SaadSparse.Chapter12.equation_12_1` states the unnumbered
  weighted residual identity at the end of §12.2. The printed number labels the local unweighted
  correction, whose zero-extended version is `SaadSparse.Chapter12.pairStep_eq`.

## Not formalized

* **Weighting by a nonnegative diagonal matrix $D_i$** in place of the scalar $\omega_i$, which the
  book mentions. The identity that the book states is the scalar one.
-/

open Matrix

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter12

section Subdomains

variable {n : ℕ}

/-!
### Section 12.2: the restriction matrices and the subdomain spaces

The book writes $V_i = [e_{l_i}, \dots, e_{r_i}]$ here and $R_i = V_i^T$ in Section 14.3.1. The
boolean matrix is named for the later notation, in which the convergence theory of Section 14.3 is
written, but it is defined here, where the book introduces it.
-/

/-- **Section 12.2** of [saad2003iterative], the restriction matrix. For an index set
$S \subseteq \{0, \dots, n-1\}$, the **boolean restriction matrix**
$R_S \in \mathbb{K}^{S \times n}$ has the entries $(R_S)_{ij} = 1$ if $i = j$ and $0$ otherwise.
Its rows are the vectors $e_j^T$ for $j \in S$, so $R_S$ is the transpose of the book's
$V_S = [e_j : j \in S]$.

The product $R_S x$ is the subvector of $x$ indexed by $S$, and $R_S^T y = V_S y$ extends a
vector on $S$ by zero. Section 14.3.1 calls the matrix $R_i$.

**Reading.** Transposes the coordinate embedding and allows arbitrary finite subsets over R or C.
-/
def restrictSubset (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) : Matrix ↥S (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : Fin n) = j then 1 else 0

/-- **Section 12.2** of [saad2003iterative], the subdomain space. For an index set $S$, the subspace
$$K_S = \operatorname{span}\{V_S\} = \operatorname{Ran}(R_S^T) = \operatorname{span}\{e_j : j
  \in S\} \subseteq \mathbb{K}^n$$
consists of the vectors supported on $S$. The additive projection process projects onto it, and
the subdomain problem of the Schwarz procedure of Section 14.3 is solved on it.

**Reading.** Spans an arbitrary finite subset, beyond the source's overlapping intervals.
-/
def subdomainSpace (𝕜 : Type*) [RCLike 𝕜] (S : Finset (Fin n)) :
    Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single (j : Fin n) (1 : 𝕜))

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The entries of $R_S$ are $(R_S)_{ij} = 1$ if $i = j$ and $0$ otherwise. -/
theorem restrictSubset_apply (S : Finset (Fin n)) (i : ↥S) (j : Fin n) :
    restrictSubset 𝕜 S i j = if (i : Fin n) = j then 1 else 0 := rfl

/-- The rows of $R_S$ are orthonormal: $R_S R_S^T = I$. In particular $R_S^T$ has full column rank,
which makes the local matrix $A_S$ nonsingular for a positive definite $A$. -/
theorem restrictSubset_mul_transpose (S : Finset (Fin n)) :
    restrictSubset 𝕜 S * (restrictSubset 𝕜 S)ᵀ = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [restrictSubset_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (i : Fin n)]
  · have h : ((k : Fin n) = (i : Fin n)) ↔ i = k := by
      rw [Subtype.ext_iff]; exact eq_comm
    simp [h]
  · exact fun j _ hj => by rw [ite_eq_right (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ (i : Fin n)) h

/-- The entries of $R_S$ are $0$ and $1$, so the conjugate transpose of $R_S^T$ is $R_S$: the
adjoint of the extension $R_S^T$ is the restriction $R_S$. -/
theorem conjTranspose_transpose_restrictSubset (S : Finset (Fin n)) :
    ((restrictSubset 𝕜 S)ᵀ)ᴴ = restrictSubset 𝕜 S := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [restrictSubset_apply]
  split_ifs <;> simp

/-- **Section 12.2** of [saad2003iterative]. For an index set $S$, the range of the extension
$V_S = R_S^T$ is
$$\operatorname{Ran}(R_S^T) = K_S = \operatorname{span}\{e_j : j \in S\}.$$
The block correction lands in this subspace, and Section 14.3.1 poses the local problem on it. -/
theorem range_restrictSubset_transpose (S : Finset (Fin n)) :
    LinearMap.range (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) = subdomainSpace 𝕜 S := by
  have hbasis : (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 ↥S))
      = Submodule.span 𝕜 (Set.range fun j : ↥S => EuclideanSpace.single j (1 : 𝕜)) := by
    have h := (EuclideanSpace.basisFun (ι := ↥S) (𝕜 := 𝕜)).toBasis.span_eq
    rw [← h]
    congr 1
    exact congrArg Set.range (funext fun j => by
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply])
  have happ : ∀ j : ↥S, Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ
      (EuclideanSpace.single j (1 : 𝕜)) = EuclideanSpace.single (j : Fin n) (1 : 𝕜) := by
    intro j
    have hcol : (restrictSubset 𝕜 S)ᵀ *ᵥ Pi.single j (1 : 𝕜)
        = Pi.single (j : Fin n) (1 : 𝕜) := by
      rw [Matrix.mulVec_single_one]
      funext k
      rw [Matrix.col_apply, Matrix.transpose_apply, restrictSubset_apply, Pi.single_apply]
      by_cases h : (j : Fin n) = k
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Matrix.toLpLin_apply, PiLp.ofLp_single, hcol, PiLp.toLp_single]
  rw [LinearMap.range_eq_map, hbasis, Submodule.map_span, ← Set.range_comp, subdomainSpace]
  exact congrArg _ (congrArg Set.range (funext happ))

/-! ### §12.2: the local matrices and the subdomain projectors -/

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Section 12.2** of [saad2003iterative], the local matrix. For $A \in \mathbb{K}^{n \times n}$
and an index set $S$, the **local matrix** is
$$A_S = V_S^T A V_S = R_S A R_S^T \in \mathbb{K}^{S \times S},$$
the submatrix of $A$ on the rows and columns in $S$. Section 14.3.1 calls it $A_i$ too.

**Reading.** Principal matrix VᵀAV on any finite subset over R or C.
-/
def localMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) : Matrix ↥S ↥S 𝕜 :=
  restrictSubset 𝕜 S * A * (restrictSubset 𝕜 S)ᵀ

/-- **Section 12.2** of [saad2003iterative], the block correction. For
$A \in \mathbb{K}^{n \times n}$ and an index set $S$, the matrix
$$T_S = V_S A_S^{-1} V_S^T = R_S^T A_S^{-1} R_S$$
restricts a residual to $S$, solves the local system there, and extends the correction by zero.
It is the subdomain solve $T_i$ of (14.31).

The inverse $A_S^{-1}$ is Mathlib's matrix inverse, which is $0$ for a singular matrix; the
results below assume that $A$ is positive definite, so that $A_S$ is nonsingular.

**Reading.** Uses inverse of arbitrary local matrix with total inverse outside invertible domain.
-/
noncomputable def subdomainInverse (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  (restrictSubset 𝕜 S)ᵀ * (localMatrix A S)⁻¹ * restrictSubset 𝕜 S

/-- **Section 12.2** of [saad2003iterative], the subdomain projector. For
$A \in \mathbb{K}^{n \times n}$ and an index set $S$, the **subdomain projector** is
$$P_S = R_S^T A_S^{-1} R_S A = T_S A.$$
It is $P_i$ of (14.24).

**Reading.** Uses total matrix inverse and permits arbitrary finite subset over R or C.
-/
noncomputable def subdomainProjector (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  subdomainInverse A S * A

/-- $P_S = T_S A$, that is, (14.24) written through (14.31). -/
theorem subdomainProjector_eq_mul (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    subdomainProjector A S = subdomainInverse A S * A := rfl

/-- For $M \in \mathbb{K}^{n \times n}$ and $z \in \mathbb{K}^n$, $(I - M) z = z - Mz$. -/
theorem toEuclideanLin_one_sub_apply (M : Matrix (Fin n) (Fin n) 𝕜)
    (z : EuclideanSpace 𝕜 (Fin n)) : ((1 - M) ⬝ z) = z - (M ⬝ z) := by
  have hmat : Matrix.toEuclideanLin (1 - M)
      = (LinearMap.id : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        - Matrix.toEuclideanLin M := by
    rw [map_sub, Matrix.toLpLin_one]
  rw [hmat, LinearMap.sub_apply, LinearMap.id_apply]

/-- If $A$ is positive definite, then the map $x \mapsto Ax$ is a symmetric coercive operator. This
is the hypothesis under which the $A$-orthogonal projector below and the energy inner product
$(x, y)_A$ of Section 14.3.4 exist. -/
theorem isSymmetricCoercive_toEuclideanLin (hA : A.PosDef) :
    (Matrix.toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

/-- The adjoint of the extension $x \mapsto R_S^T x$ is the restriction $y \mapsto R_S y$. -/
theorem adjoint_toEuclideanLin_transpose (S : Finset (Fin n)) :
    LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (restrictSubset 𝕜 S) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_transpose_restrictSubset]

/-- The extension $x \mapsto R_S^T x$ is injective, since $R_S R_S^T = I$. -/
theorem injective_toEuclideanLin_transpose (S : Finset (Fin n)) :
    Function.Injective (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) := by
  have h : Matrix.toEuclideanLin (restrictSubset 𝕜 S) ∘ₗ
      Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ = LinearMap.id := by
    rw [← Matrix.toLpLin_mul_same, restrictSubset_mul_transpose, Matrix.toLpLin_one]
  exact Function.LeftInverse.injective (g := Matrix.toEuclideanLin (restrictSubset 𝕜 S))
    fun x => DFunLike.congr_fun h x

/-- The local matrix $A_S = R_S A R_S^T$ is the Galerkin coarse operator `Multigrid.galerkinCoarse`
of the extension $R_S^T$. This identification makes the whole section a specialization of the
abstract theory. -/
theorem galerkinCoarse_eq (A : Matrix (Fin n) (Fin n) 𝕜) (S : Finset (Fin n)) :
    Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
        (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      = Matrix.toEuclideanLin (localMatrix A S) := by
  have hdef : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) ∘ₗ
            Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ := rfl
  rw [hdef, adjoint_toEuclideanLin_transpose, localMatrix, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- If $A$ is positive definite, then the local matrix $A_S$ is positive definite for every index
set $S$. So the local problem is well posed, and $A_S^{-1}$ in the block correction is a true
inverse. -/
theorem posDef_localMatrix (hA : A.PosDef) (S : Finset (Fin n)) : (localMatrix A S).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive, ← galerkinCoarse_eq]
  exact Multigrid.galerkinCoarse_isSymmetricCoercive (isSymmetricCoercive_toEuclideanLin hA)
    (injective_toEuclideanLin_transpose S)

/-- Equal subspaces give equal energy projections `Schwarz.energyProjection`. -/
private theorem energyProjection_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetricCoercive)
    {K L : Submodule 𝕜 E} [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L] (h : K = L) :
    Schwarz.energyProjection T hT K = Schwarz.energyProjection T hT L := by
  subst h; rfl

/-- **Section 12.2** of [saad2003iterative], the subdomain projector as an $A$-orthogonal projector.
Let $A \in \mathbb{K}^{n \times n}$ be positive definite and let $S$ be an index set. Then the
subdomain projector $P_S = R_S^T A_S^{-1} R_S A$ is the $A$-orthogonal projector onto the
subdomain space $K_S = \operatorname{span}\{e_j : j \in S\}$.

All results of Sections 12.2 and 14.3 follow from this identification and the abstract Schwarz
theory; read in Section 14.3, it is (14.24). The $A$-orthogonal projector is
`Schwarz.energyProjection`.

**Reading.** Identifies each error projector with the backbone Hermitian energy projection over R or
C.
-/
theorem subdomainProjector_eq_energyProjection (hA : A.PosDef) (S : Finset (Fin n)) :
    Matrix.toEuclideanLin (subdomainProjector A S)
      = Schwarz.energyProjection (Matrix.toEuclideanLin A)
          (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) := by
  have hinv : localMatrix A S * (localMatrix A S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (posDef_localMatrix hA S).isUnit)
  refine LinearMap.ext fun x => ?_
  have hy : Multigrid.galerkinCoarse (Matrix.toEuclideanLin A)
      (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
      (Matrix.toEuclideanLin ((localMatrix A S)⁻¹ * restrictSubset 𝕜 S * A) x)
        = LinearMap.adjoint (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ)
            (Matrix.toEuclideanLin A x) := by
    rw [galerkinCoarse_eq, adjoint_toEuclideanLin_transpose, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
      Matrix.toLpLin_mul_same]
    rfl
  have hproj := Schwarz.energyProjection_eq_of_galerkinCoarse (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (Matrix.toEuclideanLin (restrictSubset 𝕜 S)ᵀ) hy
  rw [energyProjection_congr (isSymmetricCoercive_toEuclideanLin hA)
    (range_restrictSubset_transpose (𝕜 := 𝕜) S).symm, hproj, ← LinearMap.comp_apply,
    ← Matrix.toLpLin_mul_same]
  rw [subdomainProjector, subdomainInverse, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- If $A$ is positive definite, then the subdomain projector is idempotent: $P_S^2 = P_S$.

**Reading.** Idempotence stated under positive definiteness, stronger than invertibility of local
matrix.
-/
theorem subdomainProjector_mul_self (hA : A.PosDef) (S : Finset (Fin n)) :
    subdomainProjector A S * subdomainProjector A S = subdomainProjector A S := by
  refine (Matrix.toEuclideanLin (𝕜 := 𝕜)).injective ?_
  rw [Matrix.toLpLin_mul_same, subdomainProjector_eq_energyProjection hA S]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply]
  exact Schwarz.energyProjection_apply_of_mem (Matrix.toEuclideanLin A)
    (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S)
    (Schwarz.energyProjection_apply_mem (Matrix.toEuclideanLin A)
      (isSymmetricCoercive_toEuclideanLin hA) (subdomainSpace 𝕜 S) x)

end Subdomains

section BlockJacobi

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Section 12.2** of [saad2003iterative], one weighted step of the overlapping block-Jacobi
iteration. For $A \in \mathbb{K}^{n \times n}$, index sets $S_i$ and weights
$\omega_i \in \mathbb{K}$, $i \in \iota$, and vectors $b, x \in \mathbb{K}^n$, the step is
$$x' = x + \sum_i \omega_i V_i A_i^{-1} V_i^T (b - Ax).$$
All the corrections are computed from the same iterate and added at once. With $\omega_i = 1$
this is the additive Schwarz procedure of Section 14.3.3.

**Reading.** Arbitrary finite subsets and complex weights, with total matrix inverse.
-/
noncomputable def blockJacobiStep (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n))
    (ω : ι → 𝕜) (b x : EuclideanSpace 𝕜 (Fin n)) : EuclideanSpace 𝕜 (Fin n) :=
  x + ∑ i, ω i • (subdomainInverse A (S i) ⬝ (b - (A ⬝ x)))

/-- The block-Jacobi step, unfolded: $x' = x + \sum_i \omega_i T_{S_i} (b - Ax)$.

**Reading.** Same relaxed update beyond covering families of overlapping real intervals.
-/
theorem blockJacobiStep_def (A : Matrix (Fin n) (Fin n) 𝕜) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    blockJacobiStep A S ω b x
      = x + ∑ i, ω i • (subdomainInverse A (S i) ⬝ (b - (A ⬝ x))) := rfl

/-- **Section 12.2** of [saad2003iterative], the Galerkin pairs. Let $A \in \mathbb{K}^{n \times n}$
be positive definite and let $S$ be an index set. Then the subspace
$K_S = \operatorname{span}\{e_j : j \in S\}$ forms with itself a nondegenerate pair $(K_S, K_S)$
for $A$ in the sense of `Projection.IsNondegeneratePair`, so the projection processes of the
backbone apply.

**Reading.** Explicit positive-definiteness condition establishing the Galerkin pairing for
arbitrary subsets.
-/
theorem isNondegeneratePair_subdomainSpace (hA : A.PosDef) (S : Finset (Fin n)) :
    Projection.IsNondegeneratePair (Matrix.toEuclideanLin A) (subdomainSpace 𝕜 S)
      (subdomainSpace 𝕜 S) :=
  Schwarz.isNondegeneratePair_self (isSymmetricCoercive_toEuclideanLin hA) _

/-- **Section 12.2** of [saad2003iterative], one block correction is one Galerkin step. Let
$A \in \mathbb{K}^{n \times n}$ be positive definite, let $S$ be an index set, and let
$b, x \in \mathbb{K}^n$. Then the Petrov–Galerkin step from $x$ on the pair $(K_S, K_S)$,
$K_S = \operatorname{span}\{e_j : j \in S\}$, is
$$x + V_S A_S^{-1} V_S^T (b - Ax).$$
So the correction lands in $K_S$ and leaves a residual orthogonal to $K_S$, and Section 12.2 is
an instance of the additive projection process of Section 5.4.

The Petrov–Galerkin step is `Projection.pairStep`.

**Correction.** Global zero-extended single block correction under positive definiteness.
-/
theorem pairStep_eq (hA : A.PosDef) (S : Finset (Fin n)) (b x : EuclideanSpace 𝕜 (Fin n)) :
    Projection.pairStep (Matrix.toEuclideanLin A) b (subdomainSpace 𝕜 S)
        (subdomainSpace 𝕜 S) (isNondegeneratePair_subdomainSpace hA S) x
      = x + (subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hstar : Matrix.toEuclideanLin A (A⁻¹ ⬝ b) = b := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, Matrix.mul_nonsing_inv A hAdet,
      Matrix.toLpLin_one, LinearMap.id_apply]
  have hcorr : (subdomainProjector A S ⬝ ((A⁻¹ ⬝ b) - x))
      = (subdomainInverse A S ⬝ (b - (A ⬝ x))) := by
    rw [subdomainProjector, Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_sub,
      hstar]
  have hgal : IsGalerkin (Matrix.toEuclideanLin A) b x (subdomainSpace 𝕜 S)
      (x + (subdomainInverse A S ⬝ (b - (A ⬝ x)))) := by
    rw [← hcorr, subdomainProjector_eq_energyProjection hA S]
    exact Schwarz.energyProjection_isGalerkin _ _ _ hstar
  exact (Projection.pairStep_isPetrovGalerkin (isNondegeneratePair_subdomainSpace hA S)
    x).eq_of_forall hgal (isNondegeneratePair_subdomainSpace hA S).eq_zero_of_mem_orthogonal

/-- **Section 12.2** of [saad2003iterative], the block-Jacobi step as an additive projection step.
Let $A \in \mathbb{K}^{n \times n}$ be positive definite, let $S_i$, $i \in \iota$, be index
sets, let $\omega_i \in \mathbb{K}$, and let $b, x \in \mathbb{K}^n$. Then the weighted
overlapping block-Jacobi step from $x$ is the step of the additive projection process of Section
5.4 with the weights $\omega_i$ on the pairs $(K_i, K_i)$,
$K_i = \operatorname{span}\{e_j : j \in S_i\}$.

The additive projection step is `Projection.additiveStep`.

**Reading.** Weighted additive-step equality for arbitrary subsets under positive definiteness and
over R or C.
-/
theorem blockJacobiStep_eq_additiveStep (hA : A.PosDef) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    blockJacobiStep A S ω b x
      = Projection.additiveStep (Matrix.toEuclideanLin A) b
          (fun i => subdomainSpace 𝕜 (S i))
          (fun i => subdomainSpace 𝕜 (S i))
          (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x := by
  have hdef : Projection.additiveStep (Matrix.toEuclideanLin A) b
      (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) ω x
        = x + ∑ i, ω i • (Projection.pairStep (Matrix.toEuclideanLin A) b
            (subdomainSpace 𝕜 (S i)) (subdomainSpace 𝕜 (S i))
            (isNondegeneratePair_subdomainSpace hA (S i)) x - x) := rfl
  rw [hdef, blockJacobiStep_def]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => by
    rw [pairStep_eq hA (S i) b x, add_sub_cancel_left])

omit [Fintype ι] in
/-- **Section 12.2** of [saad2003iterative], the projectors of the pairs. Let
$A \in \mathbb{K}^{n \times n}$ be positive definite and let $S_i$, $i \in \iota$, be index
sets. Then the projector $P_i$ of the pair $(K_i, K_i)$,
$K_i = \operatorname{span}\{e_j : j \in S_i\}$, in the additive projection process is
$$P_i = A V_i A_i^{-1} V_i^T = A T_i.$$

The projector is `Projection.additiveProjector`. -/
theorem additiveProjector_eq (hA : A.PosDef) (S : ι → Finset (Fin n)) (i : ι) :
    Projection.additiveProjector (Matrix.toEuclideanLin A)
        (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
        (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
      = Matrix.toEuclideanLin (A * subdomainInverse A (S i)) := by
  refine LinearMap.ext fun r => ?_
  have hstep := Projection.apply_pairStep_sub (A := Matrix.toEuclideanLin A) (b := r)
    (K := subdomainSpace 𝕜 (S i)) (L := subdomainSpace 𝕜 (S i))
    (isNondegeneratePair_subdomainSpace hA (S i)) 0
  rw [pairStep_eq hA (S i) r 0] at hstep
  simp only [map_zero, sub_zero, zero_add] at hstep
  rw [show Projection.additiveProjector (Matrix.toEuclideanLin A)
      (fun i => subdomainSpace 𝕜 (S i)) (fun i => subdomainSpace 𝕜 (S i))
      (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i
        = Projection.pairProjector (Matrix.toEuclideanLin A) (subdomainSpace 𝕜 (S i))
            (subdomainSpace 𝕜 (S i)) (isNondegeneratePair_subdomainSpace hA (S i)) from
      rfl, ← hstep, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]

/-- **Section 12.2** of [saad2003iterative], the residual of an overlapping block-Jacobi step.
Let $A \in \mathbb{K}^{n \times n}$ be positive definite, let $S_i$, $i \in \iota$, be index
sets, let $\omega_i \in \mathbb{K}$, and let $b, x \in \mathbb{K}^n$. If $x'$ is the weighted
block-Jacobi step from $x$, then
$$b - Ax' = \Bigl[I - \sum_i \omega_i A V_i (V_i^T A V_i)^{-1} V_i^T\Bigr] (b - Ax).$$

Here $V_i = R_i^T$, and $V_i (V_i^T A V_i)^{-1} V_i^T = T_i$ is the subdomain solve of (14.31).
The identity is `Projection.residual_additiveStep`, equations (5.22)–(5.23) of the book, with
$K_i = L_i$ the coordinate subspace of $S_i$.

**Source location.** Numbered (12.1) is the unweighted correction to the local coordinates.
This theorem states the unnumbered residual identity at the end of §12.2 using the weighted
global update.

**Reading.** Name (12.1) instead points to a local unweighted coordinate update. Lean states global
residual with full SPD assumption, arbitrary subsets and scalar weights.
-/
theorem equation_12_1 (hA : A.PosDef) (S : ι → Finset (Fin n)) (ω : ι → 𝕜)
    (b x : EuclideanSpace 𝕜 (Fin n)) :
    b - (A ⬝ blockJacobiStep A S ω b x)
      = ((1 - ∑ i, ω i • (A * subdomainInverse A (S i))) ⬝ (b - (A ⬝ x))) := by
  have hmat : Matrix.toEuclideanLin
      (1 - ∑ i, ω i • (A * subdomainInverse A (S i)))
        = 1 - ∑ i, ω i • Projection.additiveProjector (Matrix.toEuclideanLin A)
            (fun i => subdomainSpace 𝕜 (S i))
            (fun i => subdomainSpace 𝕜 (S i))
            (fun i => isNondegeneratePair_subdomainSpace hA (S i)) i := by
    simp only [additiveProjector_eq hA S, map_sub, map_sum, map_smul, Matrix.toLpLin_one]
    rfl
  rw [blockJacobiStep_eq_additiveStep hA S ω b x, Projection.residual_additiveStep, hmat]

end BlockJacobi

end SaadSparse.Chapter12
