/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Iterate
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Projection.Basic

/-!
# The interface reduction of a two-block linear system

Let the unknowns of a linear system split into an *interior* block $x$, indexed by a finite type
$m$, and an *interface* block $y$, indexed by a finite type $n$:
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}
  = \begin{bmatrix} f \\ g \end{bmatrix}.$$
If $B$ is invertible, elimination of $x$ gives the reduced interface system $S y = g'$, with the
Schur complement $S = C - F B^{-1} E$ and $g' = g - F B^{-1} f$. This module shows that a Krylov
method applied to the full system with block triangular preconditioners is the same Krylov method
applied to the reduced system, and it computes the preconditioner that a block factorization of the
full matrix induces on the interface. The presentation follows [saad2003iterative]: §14.2.1 for the
reduction, §14.4.1 for the induced preconditioner (Proposition 14.10), and §14.5 for the equivalence
of the full and the reduced iterations (Propositions 14.11 and 14.12). The algebra of $S$ itself is
in `Numlib.LinearAlgebra.Matrix.SchurComplement`.

The interface restriction $R_y = \begin{bmatrix} 0 & I \end{bmatrix}$ reads off the second block of
a vector, and its transpose $R_y^T$, the interface prolongation, extends an interface vector by
zero. The main tool is a transfer principle. Let a linear map $P$ preserve inner products and
intertwine two operators, $T P = P S$, and let the initial residual of the big system be the image
under $P$ of the initial residual of the small system. Then the Krylov subspaces, the
minimal-residual iterates and the Galerkin iterates of the two systems correspond under $P$. For the
block preconditioners $L_A = \begin{bmatrix} I & 0 \\ F B^{-1} & L_S \end{bmatrix}$ and $U_A =
\begin{bmatrix} B & E \\ 0 & U_S \end{bmatrix}$, the split-preconditioned matrix
$L_A^{-1} A U_A^{-1}$ is block diagonal with $L_S^{-1} S U_S^{-1}$ in its interface block, so the
transfer principle applies with $P = R_y^T$.

## Main definitions

* `DomainDecomposition.restrictMatrix`: the interface restriction
  $R_y = \begin{bmatrix} 0 & I \end{bmatrix}$.
* `DomainDecomposition.prolongMatrix`: the interface prolongation $R_y^T$.
* `DomainDecomposition.restrict` and `DomainDecomposition.prolong`: $R_y$ and $R_y^T$ as linear maps
  between Euclidean spaces.
* `DomainDecomposition.blockLower` and `DomainDecomposition.blockUpper`: the block triangular
  preconditioners $L_A$ and $U_A$ of (14.49) and (14.55) of [saad2003iterative].
* `DomainDecomposition.reducedRhs`: the right-hand side $g' = g - F B^{-1} f$ of the reduced system.
* `DomainDecomposition.consistentGuess`: the consistent initial guess $(B^{-1}(f - E y); y)$.
* `DomainDecomposition.precondSchurComplement`: the preconditioned Schur complement
  $L_S^{-1} S U_S^{-1}$.
* `DomainDecomposition.precondMatrix`: the split-preconditioned matrix $L_A^{-1} A U_A^{-1}$.
* `DomainDecomposition.inducedPreconditioner`: the preconditioner $M_S = (R_y M_A^{-1} R_y^T)^{-1}$
  that a preconditioner $M_A$ of the full matrix induces on the interface.

## Main results

* `DomainDecomposition.adjoint_restrict`: the adjoint of $R_y$ is $R_y^T$.
* `DomainDecomposition.krylov_subspace_map_of_comp_eq`: if $T P = P S$, then
  $\mathcal{K}_k(T, P v) = P \mathcal{K}_k(S, v)$.
* `DomainDecomposition.isMinResidual_map_iff` and `DomainDecomposition.isGalerkin_map_iff`: under an
  intertwining map that preserves inner products, the minimal-residual (respectively Galerkin)
  iterates of the two systems correspond.
* `DomainDecomposition.precondMatrix_eq`: $L_A^{-1} A U_A^{-1} = \operatorname{diag}(I, L_S^{-1} S
  U_S^{-1})$.
* `DomainDecomposition.isMinResidual_iff_isMinResidual_schurComplement` and
  `DomainDecomposition.isGalerkin_iff_isGalerkin_schurComplement`: Propositions 14.11 and 14.12 of
  [saad2003iterative]; from a consistent initial guess, the Krylov iterates of the
  block-preconditioned full system correspond to those of the same method on the preconditioned
  reduced system.
* `DomainDecomposition.exists_isMinResidual_schurComplement`: every minimal-residual iterate of the
  block-preconditioned full system arises in this way.
* `DomainDecomposition.inducedPreconditioner_eq`: Proposition 14.10 of [saad2003iterative]; for a
  block triangular factorization $M_A = L_A U_A$, the induced preconditioner is the product
  $L_S U_S$ of the trailing diagonal blocks of the two factors.

## Proof outline

The split-preconditioned matrix maps the range of $R_y^T$, the vectors with zero interior block, to
itself, and it acts there as the preconditioned Schur complement. At a consistent initial guess the
initial residual lies in this range. Hence every Krylov vector of the full system has a zero
interior block, and the minimization (or the orthogonality condition) over the full Krylov subspace
is the one over the reduced Krylov subspace, because $R_y^T$ preserves inner products.

## Implementation notes

* A vector of the full system is indexed by `m ⊕ n`, and the block matrices are `Matrix.fromBlocks`.
* Matrices act on `EuclideanSpace 𝕜 _` through `Matrix.toEuclideanLin`, so the minimal-residual
  iterates minimize the Euclidean norm of the residual.
* The inverse $B^{-1}$ is `Matrix.inv`, which is $0$ for a singular matrix. The definitions are
  therefore total, and the theorems assume invertibility, in the form `IsUnit`, where they need it.
* The equivalence theorems are stated in the variables that a split-preconditioned method iterates
  on: $u = U_A x$ for the full system and $w = U_S y$ for the reduced system.
  `DomainDecomposition.blockUpper_inv_mulVec` recovers $x$ from $u$.
* The transfer theorems hold for any linear map that preserves inner products between two inner
  product spaces. The interface prolongation is one instance.
* The identities for the restriction matrix, the block preconditioners and the induced
  preconditioner hold over any commutative ring, and
  `DomainDecomposition.krylov_subspace_map_of_comp_eq` holds for modules over any commutative ring.
-/

namespace DomainDecomposition

open Matrix

/-! ### The interface restriction as a matrix -/

section RestrictMatrix

variable (R : Type*) [CommRing R] (m n : Type*) [DecidableEq n]

/-- The **interface restriction** $R_y = \begin{bmatrix} 0 & I \end{bmatrix}$: the
$n \times (m + n)$ matrix over a commutative ring $R$ that maps a vector indexed by $m \oplus n$
to its second block. It is the restriction $R_y$ of Proposition 14.1 and §14.4.1 of
[saad2003iterative].

The matrix is `Matrix.fromCols 0 1`. -/
def restrictMatrix : Matrix n (m ⊕ n) R := Matrix.fromCols 0 1

/-- The **interface prolongation** $R_y^T = \begin{bmatrix} 0 \\ I \end{bmatrix}$: the
$(m + n) \times n$ matrix that extends a vector indexed by $n$ by zero to a vector indexed by
$m \oplus n$.

The matrix is `Matrix.fromRows 0 1`. It is the transpose of `DomainDecomposition.restrictMatrix`
by `DomainDecomposition.transpose_restrictMatrix`. -/
def prolongMatrix : Matrix (m ⊕ n) n R := Matrix.fromRows 0 1

variable {R m n}

/-- The transpose of the restriction $R_y$ is the prolongation $R_y^T$. -/
@[simp]
theorem transpose_restrictMatrix : (restrictMatrix R m n)ᵀ = prolongMatrix R m n := by
  ext (i | i) j <;> simp [restrictMatrix, prolongMatrix, Matrix.one_apply, eq_comm]

/-- Over a ring with an involution, the conjugate transpose of $R_y$ is $R_y^T$, because the entries
of $R_y$ are $0$ and $1$. -/
@[simp]
theorem conjTranspose_restrictMatrix [StarRing R] :
    (restrictMatrix R m n)ᴴ = prolongMatrix R m n := by
  ext (i | i) j <;>
    simp [restrictMatrix, prolongMatrix, Matrix.one_apply, eq_comm, apply_ite star]

variable [Fintype n]

/-- The prolongation extends a vector by zero: $R_y^T y = (0; y)$. -/
@[simp]
theorem prolongMatrix_mulVec (y : n → R) :
    prolongMatrix R m n *ᵥ y = Sum.elim (0 : m → R) y := by
  simp [prolongMatrix]

variable [Fintype m]

/-- The restriction of a vector $v$ indexed by $m \oplus n$ is its second block:
$R_y v = (v_i)_{i \in n}$. -/
@[simp]
theorem restrictMatrix_mulVec (v : m ⊕ n → R) : restrictMatrix R m n *ᵥ v = v ∘ Sum.inr := by
  funext i
  simp [restrictMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

/-- The rows of $R_y$ are orthonormal: $R_y R_y^T = I$. -/
@[simp]
theorem restrictMatrix_mul_prolongMatrix : restrictMatrix R m n * prolongMatrix R m n = 1 := by
  simp [restrictMatrix, prolongMatrix, Matrix.fromCols_mul_fromRows]

/-- Let $M$ be a square matrix indexed by $m \oplus n$, with trailing diagonal block $M_{22}$. Then
$$R_y M R_y^T = M_{22}.$$

This identity is behind Proposition 14.10 of [saad2003iterative]: the compression of a matrix to
the interface variables is its $(2,2)$ block. The block $M_{22}$ is `M.toBlocks₂₂`. -/
theorem restrictMatrix_mul_mul_prolongMatrix (M : Matrix (m ⊕ n) (m ⊕ n) R) :
    restrictMatrix R m n * M * prolongMatrix R m n = M.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [restrictMatrix, prolongMatrix, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp

end RestrictMatrix

/-! ### The interface restriction as an operator

The binders are staged: the prolongation needs nothing about the interior index type `m`, its
isometry statements need `Fintype m` for the norm of the big space, and the restriction needs
`DecidableEq m` as well, for the identity matrix indexed by `m ⊕ n`. -/

section Restrict

variable (𝕜 : Type*) [RCLike 𝕜] (m n : Type*) [Fintype n] [DecidableEq n]

/-- Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The **interface prolongation operator**
$R_y^T$ is the linear map from the Euclidean space $\mathbb{K}^n$ to the Euclidean space
$\mathbb{K}^{m \oplus n}$ that extends a vector by zero. It is the adjoint of the interface
restriction operator.

The operator is `Matrix.toEuclideanLin` of `DomainDecomposition.prolongMatrix`. The adjoint
statement is `DomainDecomposition.adjoint_restrict`. -/
noncomputable def prolong : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) :=
  Matrix.toEuclideanLin (prolongMatrix 𝕜 m n)

variable {𝕜 m n}

/-- The prolongation maps $y$ to $(0; y)$. -/
theorem prolong_apply (y : EuclideanSpace 𝕜 n) :
    prolong 𝕜 m n y = WithLp.toLp 2 (Sum.elim (0 : m → 𝕜) (WithLp.ofLp y)) := by
  simp [prolong, Matrix.toLpLin_apply]

/-- The prolongation maps $y$ to $(0; y)$, for $y$ given as a function on $n$. -/
theorem prolong_toLp (y : n → 𝕜) :
    prolong 𝕜 m n (WithLp.toLp 2 y) = WithLp.toLp 2 (Sum.elim (0 : m → 𝕜) y) :=
  prolong_apply _

/-- The prolongation $R_y^T$ is injective. -/
theorem prolong_injective : Function.Injective (prolong 𝕜 m n) := by
  intro a b hab
  rw [prolong_apply, prolong_apply] at hab
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  exact congrFun (congrArg WithLp.ofLp hab) (Sum.inr j)

/-- A vector $v \in \mathbb{K}^{m \oplus n}$ lies in the range of the prolongation $R_y^T$ if and
only if its interior block vanishes: $v_i = 0$ for every $i \in m$. -/
theorem mem_range_prolong_iff (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    v ∈ LinearMap.range (prolong 𝕜 m n) ↔ ∀ i : m, WithLp.ofLp v (Sum.inl i) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i
    simp [prolong_apply]
  · intro h
    refine ⟨WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr), ?_⟩
    rw [prolong_toLp]
    refine WithLp.ofLp_injective 2 (funext fun j => ?_)
    cases j with
    | inl i => exact (h i).symm
    | inr j => rfl

section Isometry

variable (𝕜 m n)
variable [Fintype m]

/-- If $m$ is finite, the prolongation preserves inner products: $\langle R_y^T a, R_y^T b \rangle =
\langle a, b \rangle$ for all $a, b \in \mathbb{K}^n$. -/
theorem inner_prolong_prolong (a b : EuclideanSpace 𝕜 n) :
    inner 𝕜 (prolong 𝕜 m n a) (prolong 𝕜 m n b) = (inner 𝕜 a b : 𝕜) := by
  rw [prolong_apply, prolong_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type]

/-- The prolongation $R_y^T$ as a linear isometry from $\mathbb{K}^n$ to $\mathbb{K}^{m \oplus n}$.
-/
noncomputable def prolongIsometry : EuclideanSpace 𝕜 n →ₗᵢ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) :=
  (prolong 𝕜 m n).isometryOfInner (inner_prolong_prolong 𝕜 m n)

/-- The linear isometry `DomainDecomposition.prolongIsometry` is the map
`DomainDecomposition.prolong`. -/
@[simp]
theorem coe_prolongIsometry : ⇑(prolongIsometry 𝕜 m n) = prolong 𝕜 m n := rfl

variable {𝕜 m n}

/-- The prolongation preserves norms: $\|R_y^T a\| = \|a\|$. -/
@[simp]
theorem norm_prolong (a : EuclideanSpace 𝕜 n) : ‖prolong 𝕜 m n a‖ = ‖a‖ :=
  (prolongIsometry 𝕜 m n).norm_map a

end Isometry

section RestrictOp

variable (𝕜 m n)
variable [Fintype m] [DecidableEq m]

/-- Let $m$ and $n$ be finite. The **interface restriction operator** $R_y$ of Proposition 14.1 of
[saad2003iterative] is the linear map from the Euclidean space $\mathbb{K}^{m \oplus n}$ to the
Euclidean space $\mathbb{K}^n$ that maps a vector to its interface block.

The operator is `Matrix.toEuclideanLin` of `DomainDecomposition.restrictMatrix`. -/
noncomputable def restrict : EuclideanSpace 𝕜 (m ⊕ n) →ₗ[𝕜] EuclideanSpace 𝕜 n :=
  Matrix.toEuclideanLin (restrictMatrix 𝕜 m n)

variable {𝕜 m n}

/-- The restriction maps a vector $v$ to its second block $(v_i)_{i \in n}$. -/
theorem restrict_apply (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    restrict 𝕜 m n v = WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) := by
  simp [restrict, Matrix.toLpLin_apply]

/-- Restriction of a prolonged vector returns it: $R_y R_y^T y = y$. -/
@[simp]
theorem restrict_prolong (y : EuclideanSpace 𝕜 n) : restrict 𝕜 m n (prolong 𝕜 m n y) = y := by
  rw [restrict_apply, prolong_apply]
  simp

/-- $R_y R_y^T = I$, as an identity of linear maps. -/
theorem restrict_comp_prolong : restrict 𝕜 m n ∘ₗ prolong 𝕜 m n = LinearMap.id :=
  LinearMap.ext fun y => restrict_prolong y

/-- For finite $m$ and $n$, the adjoint of the interface restriction $R_y$ is the interface
prolongation $R_y^T$:
$$\langle R_y v, y \rangle = \langle v, R_y^T y \rangle \quad \text{for all } v \in
  \mathbb{K}^{m \oplus n},\ y \in \mathbb{K}^n.$$

These are the operators $R_y$ and $R_y^T$ of Proposition 14.1 of [saad2003iterative]. The
adjoint is `LinearMap.adjoint`. -/
theorem adjoint_restrict : LinearMap.adjoint (restrict 𝕜 m n) = prolong 𝕜 m n :=
  ((LinearMap.eq_adjoint_iff (prolong 𝕜 m n) (restrict 𝕜 m n)).2 fun x y => by
    rw [prolong_apply, EuclideanSpace.inner_eq_star_dotProduct, restrict_apply,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, Fintype.sum_sum_type]).symm

end RestrictOp

end Restrict

/-! ### Krylov subspaces under an intertwiner -/

section Intertwine

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {P : N →ₗ[R] M} {T : Module.End R M} {S : Module.End R N}

/-- Let $P : N \to M$ be a linear map and $T$, $S$ endomorphisms of $M$ and $N$ with $T P = P S$.
Then $T^i P v = P S^i v$ for every $i \in \mathbb{N}$ and $v \in N$. -/
theorem pow_apply_of_comp_eq (h : T ∘ₗ P = P ∘ₗ S) (i : ℕ) (v : N) :
    (T ^ i) (P v) = P ((S ^ i) v) := by
  have hTP : ∀ w : N, T (P w) = P (S w) := fun w => LinearMap.congr_fun h w
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, hTP, pow_succ', Module.End.mul_apply]

/-- Let $R$ be a commutative ring, let $M$ and $N$ be $R$-modules, let $P : N \to M$ be linear, and
let $T$ and $S$ be endomorphisms of $M$ and $N$ with $T P = P S$. Then for every $v \in N$ and
$k \in \mathbb{N}$,
$$\mathcal{K}_k(T, P v) = P \, \mathcal{K}_k(S, v),$$
where $\mathcal{K}_k(A, v) = \operatorname{span}\{v, A v, \dots, A^{k-1} v\}$.

This is the invariance statement behind every theorem of the form "the method on the reduced
system is the method on the full system". The Krylov subspace is `Krylov.subspace`, and the
image is `Submodule.map`. -/
theorem krylov_subspace_map_of_comp_eq (h : T ∘ₗ P = P ∘ₗ S) (v : N) (k : ℕ) :
    Krylov.subspace T (P v) k = (Krylov.subspace S v k).map P := by
  rw [Krylov.subspace, Krylov.subspace, Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(S ^ (i : ℕ)) v, ⟨i, rfl⟩, (pow_apply_of_comp_eq h i v).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, pow_apply_of_comp_eq h i v⟩

end Intertwine

/-! ### Projection specifications under an intertwining isometry -/

section Transfer

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
variable {P : Y →ₗ[𝕜] X} {T : X →ₗ[𝕜] X} {S : Y →ₗ[𝕜] Y} {b u₀ : X} {g y₀ : Y}

/-- If $u - u_0$ lies in the image $P K$ of a subspace $K$, then $u = u_0 + P w$ for some $w \in K$.
-/
theorem exists_mem_of_sub_mem_map {K : Submodule 𝕜 Y} {u : X} (hu : u - u₀ ∈ K.map P) :
    ∃ w ∈ K, u = u₀ + P w := by
  obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.1 hu
  exact ⟨w, hw, by rw [hwu]; abel⟩

/-- Let $P : Y \to X$ preserve inner products. For a subspace $K$ of $Y$ and $z \in Y$, the vector
$P z$ is orthogonal to $P K$ if and only if $z$ is orthogonal to $K$. -/
theorem mem_orthogonal_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (K : Submodule 𝕜 Y) (z : Y) : P z ∈ (K.map P)ᗮ ↔ z ∈ Kᗮ := by
  constructor
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
    rw [← hP u z]
    exact (Submodule.mem_orthogonal _ _).1 h _ (Submodule.mem_map_of_mem hu)
  · intro h
    refine (Submodule.mem_orthogonal _ _).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [hP u z]
    exact (Submodule.mem_orthogonal _ _).1 h _ hu

/-- If $T P = P S$ and $b - T u_0 = P (g - S y_0)$, then $b - T (u_0 + P w) = P (g - S (y_0 + w))$
for every $w \in Y$: the residual of the big system at $u_0 + P w$ is the image of the residual
of the small system at $y_0 + w$. -/
theorem residual_map (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (w : Y) :
    b - T (u₀ + P w) = P (g - S (y₀ + w)) := by
  have hTP : T (P w) = P (S w) := LinearMap.congr_fun h w
  calc b - T (u₀ + P w) = b - T u₀ - T (P w) := by rw [map_add]; abel
    _ = P (g - S y₀) - P (S w) := by rw [hres, hTP]
    _ = P (g - S (y₀ + w)) := by rw [map_add, ← map_sub]; congr 1; abel

/-- Let $X$ and $Y$ be inner product spaces over $\mathbb{K}$, let $P : Y \to X$ be a linear map
that preserves inner products, and let $T : X \to X$ and $S : Y \to Y$ be linear with
$T P = P S$. Let $b, u_0 \in X$ and $g, y_0 \in Y$ satisfy $b - T u_0 = P (g - S y_0)$. Then for
every subspace $K$ of $Y$ and every $y \in Y$, the vector $u_0 + P (y - y_0)$ is a
minimal-residual iterate of $T u = b$ over $u_0 + P K$ if and only if $y$ is a minimal-residual
iterate of $S y = g$ over $y_0 + K$. Here a minimal-residual iterate of $T u = b$ over $u_0 + L$
is a point $u \in u_0 + L$ that minimizes $\|b - T u\|$ on $u_0 + L$.

The two minimizations are the same minimization, because $P$ maps the residuals of the small
system isometrically to the residuals of the big system. The specification is `IsMinResidual`. -/
theorem isMinResidual_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (K : Submodule 𝕜 Y) (y : Y) :
    IsMinResidual T b u₀ (K.map P) (u₀ + P (y - y₀)) ↔ IsMinResidual S g y₀ K y := by
  have hinj : Function.Injective P := (LinearMap.isometryOfInner P hP).injective
  have hnorm : ∀ w : Y, ‖b - T (u₀ + P w)‖ = ‖g - S (y₀ + w)‖ := fun w => by
    rw [residual_map h hres w]
    exact (LinearMap.isometryOfInner P hP).norm_map _
  constructor
  · intro hx
    refine ⟨?_, fun y' hy' => ?_⟩
    · have hmem := hx.mem
      rw [add_sub_cancel_left] at hmem
      obtain ⟨w, hw, hwP⟩ := Submodule.mem_map.1 hmem
      rwa [hinj hwP] at hw
    · have hle := hx.min (u₀ + P (y' - y₀))
        (by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy')
      rwa [hnorm (y - y₀), hnorm (y' - y₀), add_sub_cancel, add_sub_cancel] at hle
  · intro hy
    refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy.mem, fun u hu => ?_⟩
    obtain ⟨w, hw, rfl⟩ := exists_mem_of_sub_mem_map hu
    rw [hnorm (y - y₀), hnorm w, add_sub_cancel]
    exact hy.min (y₀ + w) (by rw [add_sub_cancel_left]; exact hw)

/-- Let $X$, $Y$, $P$, $T$, $S$, $b$, $u_0$, $g$ and $y_0$ be as in
`DomainDecomposition.isMinResidual_map_iff`: $P$ preserves inner products, $T P = P S$, and
$b - T u_0 = P (g - S y_0)$. Then for every subspace $K$ of $Y$ and every $y \in Y$, the vector
$u_0 + P (y - y_0)$ is a Galerkin iterate of $T u = b$ over $u_0 + P K$ if and only if $y$ is a
Galerkin iterate of $S y = g$ over $y_0 + K$. Here a Galerkin iterate of $T u = b$ over
$u_0 + L$ is a point $u \in u_0 + L$ with $b - T u \perp L$.

The specification is `IsGalerkin`. -/
theorem isGalerkin_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (K : Submodule 𝕜 Y) (y : Y) :
    IsGalerkin T b u₀ (K.map P) (u₀ + P (y - y₀)) ↔ IsGalerkin S g y₀ K y := by
  have hinj : Function.Injective P := (LinearMap.isometryOfInner P hP).injective
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hmem := hx.mem
      rw [add_sub_cancel_left] at hmem
      obtain ⟨w, hw, hwP⟩ := Submodule.mem_map.1 hmem
      rwa [hinj hwP] at hw
    · have horth := hx.orth
      rw [residual_map h hres (y - y₀), add_sub_cancel] at horth
      exact (mem_orthogonal_map_iff hP K _).1 horth
  · intro hy
    refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hy.mem, ?_⟩
    rw [residual_map h hres (y - y₀), add_sub_cancel]
    exact (mem_orthogonal_map_iff hP K _).2 hy.orth

/-- Under the hypotheses of `DomainDecomposition.isMinResidual_map_iff`, every minimal-residual
iterate $u$ of $T u = b$ over $u_0 + P K$ is $u = u_0 + P (y - y_0)$ for a minimal-residual
iterate $y$ of $S y = g$ over $y_0 + K$. -/
theorem exists_isMinResidual_of_isMinResidual_map
    (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜)) (h : T ∘ₗ P = P ∘ₗ S)
    (hres : b - T u₀ = P (g - S y₀)) {K : Submodule 𝕜 Y} {u : X}
    (hu : IsMinResidual T b u₀ (K.map P) u) :
    ∃ y, IsMinResidual S g y₀ K y ∧ u = u₀ + P (y - y₀) := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_sub_mem_map hu.mem
  refine ⟨y₀ + w, ?_, by rw [add_sub_cancel_left]⟩
  rw [← isMinResidual_map_iff hP h hres K (y₀ + w), add_sub_cancel_left]
  exact hu

/-- If $T P = P S$ and $b - T u_0 = P (g - S y_0)$, then for every $k \in \mathbb{N}$ the Krylov
subspace of the big system at its initial residual is the image of the Krylov subspace of the
small system at its initial residual:
$$\mathcal{K}_k(T, b - T u_0) = P \, \mathcal{K}_k(S, g - S y_0).$$
-/
theorem krylov_subspace_residual_eq_map (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀))
    (k : ℕ) :
    Krylov.subspace T (b - T u₀) k = (Krylov.subspace S (g - S y₀) k).map P := by
  rw [hres]
  exact krylov_subspace_map_of_comp_eq h _ k

/-- Let $P : Y \to X$ preserve inner products, let $T P = P S$, and let $b - T u_0 = P (g - S y_0)$,
as in `DomainDecomposition.isMinResidual_map_iff`. Then for every $k \in \mathbb{N}$ and
$y \in Y$, the vector $u_0 + P (y - y_0)$ is a minimal-residual Krylov iterate at step $k$ of
$T u = b$ from $u_0$ if and only if $y$ is a minimal-residual Krylov iterate at step $k$ of
$S y = g$ from $y_0$. A minimal-residual Krylov iterate at step $k$ of $T u = b$ from $u_0$ is a
minimal-residual iterate over $u_0 + \mathcal{K}_k(T, b - T u_0)$.

This is `DomainDecomposition.isMinResidual_map_iff` for the Krylov subspaces of the initial
residuals, which correspond by `DomainDecomposition.krylov_subspace_residual_eq_map`. It is the
form in which a Krylov method such as GMRES or MINRES is specified. The specification is
`Krylov.IsMinResidualIterate`. -/
theorem isMinResidualIterate_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) (y : Y) :
    Krylov.IsMinResidualIterate T b u₀ k (u₀ + P (y - y₀)) ↔
      Krylov.IsMinResidualIterate S g y₀ k y := by
  have hK := krylov_subspace_residual_eq_map h hres k
  constructor
  · intro hx
    have hx' : IsMinResidual T b u₀ (Krylov.subspace T (b - T u₀) k) (u₀ + P (y - y₀)) := hx
    rw [hK] at hx'
    exact (isMinResidual_map_iff hP h hres _ y).1 hx'
  · intro hy
    have hy' : IsMinResidual S g y₀ (Krylov.subspace S (g - S y₀) k) y := hy
    have hx' := (isMinResidual_map_iff hP h hres _ y).2 hy'
    rw [← hK] at hx'
    exact hx'

/-- Let $P : Y \to X$ preserve inner products, let $T P = P S$, and let $b - T u_0 = P (g - S y_0)$.
Then for every $k \in \mathbb{N}$ and $y \in Y$, the vector $u_0 + P (y - y_0)$ is a Galerkin
Krylov iterate at step $k$ of $T u = b$ from $u_0$ if and only if $y$ is a Galerkin Krylov
iterate at step $k$ of $S y = g$ from $y_0$. A Galerkin Krylov iterate at step $k$ of $T u = b$
from $u_0$ is a Galerkin iterate over $u_0 + \mathcal{K}_k(T, b - T u_0)$.

This is the Galerkin counterpart of `DomainDecomposition.isMinResidualIterate_map_iff`, and the
specification of FOM, CG and the Lanczos method. The specification is
`Krylov.IsGalerkinIterate`. -/
theorem isGalerkinIterate_map_iff (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜))
    (h : T ∘ₗ P = P ∘ₗ S) (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) (y : Y) :
    Krylov.IsGalerkinIterate T b u₀ k (u₀ + P (y - y₀)) ↔ Krylov.IsGalerkinIterate S g y₀ k y := by
  have hK := krylov_subspace_residual_eq_map h hres k
  constructor
  · intro hx
    have hx' : IsGalerkin T b u₀ (Krylov.subspace T (b - T u₀) k) (u₀ + P (y - y₀)) := hx
    rw [hK] at hx'
    exact (isGalerkin_map_iff hP h hres _ y).1 hx'
  · intro hy
    have hy' : IsGalerkin S g y₀ (Krylov.subspace S (g - S y₀) k) y := hy
    have hx' := (isGalerkin_map_iff hP h hres _ y).2 hy'
    rw [← hK] at hx'
    exact hx'

/-- Let $P : Y \to X$ preserve inner products, let $T P = P S$, and let $b - T u_0 = P (g - S y_0)$.
Then every minimal-residual Krylov iterate $u$ at step $k$ of $T u = b$ from $u_0$ has the form
$$u = u_0 + P (y - y_0),$$
where $y$ is a minimal-residual Krylov iterate at step $k$ of $S y = g$ from $y_0$.

This is `DomainDecomposition.isMinResidualIterate_map_iff` read in the other direction. -/
theorem exists_isMinResidualIterate_of_isMinResidualIterate_map
    (hP : ∀ a b : Y, inner 𝕜 (P a) (P b) = (inner 𝕜 a b : 𝕜)) (h : T ∘ₗ P = P ∘ₗ S)
    (hres : b - T u₀ = P (g - S y₀)) (k : ℕ) {u : X} (hu : Krylov.IsMinResidualIterate T b u₀ k u) :
    ∃ y, Krylov.IsMinResidualIterate S g y₀ k y ∧ u = u₀ + P (y - y₀) := by
  have hu' : IsMinResidual T b u₀ (Krylov.subspace T (b - T u₀) k) u := hu
  rw [krylov_subspace_residual_eq_map h hres k] at hu'
  obtain ⟨y, hy, hyu⟩ := exists_isMinResidual_of_isMinResidual_map hP h hres hu'
  exact ⟨y, hy, hyu⟩

end Transfer

/-! ### The block preconditioners of a two-block system -/

section Block

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]
variable {B : Matrix m m R} {E : Matrix m n R} {F : Matrix n m R} {C : Matrix n n R}
  {LS US : Matrix n n R}

/-- Let $B \in R^{m \times m}$, $F \in R^{n \times m}$ and $L_S \in R^{n \times n}$. The **block
lower triangular left preconditioner** is
$$L_A = \begin{bmatrix} I & 0 \\ F B^{-1} & L_S \end{bmatrix}.$$
With $L_S = I$ it is the preconditioner of (14.49) of [saad2003iterative]. With $L_S$ the lower
factor of an approximate factorization $S \approx L_S U_S$ of the Schur complement, it is the
preconditioner of (14.55).

The inverse $B^{-1}$ is `Matrix.inv`, which is $0$ for singular $B$. -/
noncomputable def blockLower (B : Matrix m m R) (F : Matrix n m R) (LS : Matrix n n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks 1 0 (F * B⁻¹) LS

/-- Let $B \in R^{m \times m}$, $E \in R^{m \times n}$ and $U_S \in R^{n \times n}$. The **block
upper triangular right preconditioner** of (14.49) and (14.55) of [saad2003iterative] is
$$U_A = \begin{bmatrix} B & E \\ 0 & U_S \end{bmatrix}.$$
-/
def blockUpper (B : Matrix m m R) (E : Matrix m n R) (US : Matrix n n R) :
    Matrix (m ⊕ n) (m ⊕ n) R :=
  Matrix.fromBlocks B E 0 US

/-- The **right-hand side of the reduced interface system**, $g' = g - F B^{-1} f$, as in (14.4) of
[saad2003iterative].

The inverse $B^{-1}$ is `Matrix.inv`, which is $0$ for singular $B$. -/
noncomputable def reducedRhs (B : Matrix m m R) (F : Matrix n m R) (f : m → R) (g : n → R) :
    n → R :=
  g - F *ᵥ (B⁻¹ *ᵥ f)

/-- A **consistent initial guess** for $y \in R^n$ is the vector
$$\begin{bmatrix} B^{-1} (f - E y) \\ y \end{bmatrix},$$
as in (14.50) and (14.56) of [saad2003iterative]. For invertible $B$, these are the vectors
$(x; y)$ whose interior residual $f - B x - E y$ vanishes.

Every iterate of the block-preconditioned method that starts at such a guess is again of this
form, which is (14.51) of [saad2003iterative]; see `DomainDecomposition.blockUpper_inv_mulVec`.
The inverse $B^{-1}$ is `Matrix.inv`, which is $0$ for singular $B$. -/
noncomputable def consistentGuess (B : Matrix m m R) (E : Matrix m n R) (f : m → R) (y : n → R) :
    m ⊕ n → R :=
  Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y

/-- The **preconditioned Schur complement** $L_S^{-1} S U_S^{-1}$, where $S = C - F B^{-1} E$ is the
Schur complement of the $(1,1)$ block of $A = \begin{bmatrix} B & E \\ F & C \end{bmatrix}$. It
is the interface block of the split-preconditioned matrix, as in (14.53) and (14.58) of
[saad2003iterative].

The Schur complement is `Matrix.schurComplement`. All inverses are `Matrix.inv`, which is $0$
for a singular matrix. -/
noncomputable def precondSchurComplement (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) (LS US : Matrix n n R) : Matrix n n R :=
  LS⁻¹ * (Matrix.fromBlocks B E F C).schurComplement * US⁻¹

/-- The **split-preconditioned system matrix** $L_A^{-1} A U_A^{-1}$ of (14.53) of
[saad2003iterative], with $A = \begin{bmatrix} B & E \\ F & C \end{bmatrix}$ and the block
preconditioners $L_A$ and $U_A$.

The inverses are `Matrix.inv`, which is $0$ for a singular matrix. -/
noncomputable def precondMatrix (B : Matrix m m R) (E : Matrix m n R) (F : Matrix n m R)
    (C : Matrix n n R) (LS US : Matrix n n R) : Matrix (m ⊕ n) (m ⊕ n) R :=
  (blockLower B F LS)⁻¹ * Matrix.fromBlocks B E F C * (blockUpper B E US)⁻¹

/-- If $L_S$ is invertible, then the left preconditioner $L_A$ is invertible. -/
theorem isUnit_blockLower (hLS : IsUnit LS) : IsUnit (blockLower B F LS) := by
  rw [blockLower, Matrix.isUnit_fromBlocks_zero₁₂]
  exact ⟨isUnit_one, hLS⟩

/-- If $B$ and $U_S$ are invertible, then the right preconditioner $U_A$ is invertible. -/
theorem isUnit_blockUpper (hB : IsUnit B) (hUS : IsUnit US) : IsUnit (blockUpper B E US) := by
  rw [blockUpper, Matrix.isUnit_fromBlocks_zero₂₁]
  exact ⟨hB, hUS⟩

/-- If $L_S$ is invertible, then the inverse of the left preconditioner is
$$L_A^{-1} = \begin{bmatrix} I & 0 \\ -L_S^{-1} F B^{-1} & L_S^{-1} \end{bmatrix}.$$
-/
theorem inv_blockLower (hLS : IsUnit LS) :
    (blockLower B F LS)⁻¹ = Matrix.fromBlocks 1 0 (-(LS⁻¹ * (F * B⁻¹))) LS⁻¹ := by
  rw [blockLower, Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (iff_of_true isUnit_one hLS)]
  simp

/-- If $B$ and $U_S$ are invertible, then the inverse of the right preconditioner is
$$U_A^{-1} = \begin{bmatrix} B^{-1} & -B^{-1} E U_S^{-1} \\ 0 & U_S^{-1} \end{bmatrix}.$$
-/
theorem inv_blockUpper (hB : IsUnit B) (hUS : IsUnit US) :
    (blockUpper B E US)⁻¹ = Matrix.fromBlocks B⁻¹ (-(B⁻¹ * E * US⁻¹)) 0 US⁻¹ := by
  rw [blockUpper, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hB hUS)]

/-- Let $B$, $L_S$ and $U_S$ be invertible, and let $S = C - F B^{-1} E$. Then the system matrix
factors as
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix}
  = L_A \begin{bmatrix} I & 0 \\ 0 & L_S^{-1} S U_S^{-1} \end{bmatrix} U_A.$$
This is the block factorization (14.52) and (14.58) of [saad2003iterative]. -/
theorem fromBlocks_eq_blockLower_mul (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    Matrix.fromBlocks B E F C
      = blockLower B F LS * Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US)
        * blockUpper B E US := by
  have hBB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  have hLL : LS * LS⁻¹ = 1 := Matrix.mul_nonsing_inv LS ((Matrix.isUnit_iff_isUnit_det LS).1 hLS)
  have hUU : US⁻¹ * US = 1 := Matrix.nonsing_inv_mul US ((Matrix.isUnit_iff_isUnit_det US).1 hUS)
  have h1 : F * B⁻¹ * B = F := by rw [Matrix.mul_assoc, hBB, Matrix.mul_one]
  have h2 : LS * (LS⁻¹ * (C - F * B⁻¹ * E) * US⁻¹) * US = C - F * B⁻¹ * E := by
    rw [← mul_assoc LS _ US⁻¹, ← mul_assoc LS LS⁻¹, hLL, one_mul, mul_assoc, hUU, mul_one]
  rw [blockLower, blockUpper, precondSchurComplement, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add,
    Matrix.schurComplement_fromBlocks]
  rw [h1, h2]
  congr 1
  abel

/-- Let $B$, $L_S$ and $U_S$ be invertible. Then the split-preconditioned system matrix is block
diagonal:
$$L_A^{-1} A U_A^{-1} = \begin{bmatrix} I & 0 \\ 0 & L_S^{-1} S U_S^{-1} \end{bmatrix},$$
as in (14.53) of [saad2003iterative].

This is the whole content of the block preconditioning: the interface block of the
preconditioned operator is the preconditioned Schur complement, and the interior block is the
identity. -/
theorem precondMatrix_eq (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    precondMatrix B E F C LS US
      = Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US) := by
  have hL : (blockLower B F LS)⁻¹ * blockLower B F LS = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_blockLower hLS))
  have hU : blockUpper B E US * (blockUpper B E US)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_blockUpper hB hUS))
  rw [precondMatrix, fromBlocks_eq_blockLower_mul hB hLS hUS, ← mul_assoc, ← mul_assoc, hL, one_mul,
    mul_assoc, hU, mul_one]

omit [DecidableEq n] in
/-- If $B$ is invertible, the right preconditioner maps the consistent guess at $y$ to $(f; U_S y)$:
$$U_A \begin{bmatrix} B^{-1} (f - E y) \\ y \end{bmatrix} = \begin{bmatrix} f \\ U_S y
  \end{bmatrix}.$$
-/
theorem blockUpper_mulVec_consistentGuess (hB : IsUnit B) (f : m → R) (y : n → R) :
    blockUpper B E US *ᵥ consistentGuess B E f y = Sum.elim f (US *ᵥ y) := by
  rw [blockUpper, consistentGuess, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add]
  refine congrArg₂ Sum.elim ?_ rfl
  rw [Matrix.mulVec_nonsing_inv_mulVec hB]
  abel

/-- If $B$ and $U_S$ are invertible, the inverse of the right preconditioner maps $(f; U_S y)$ to
the consistent guess at $y$:
$$U_A^{-1} \begin{bmatrix} f \\ U_S y \end{bmatrix} = \begin{bmatrix} B^{-1} (f - E y) \\ y
  \end{bmatrix}.$$
This is (14.51) of [saad2003iterative].

With `DomainDecomposition.blockUpper_mulVec_consistentGuess`, this says that $U_A$ is a
bijection between the consistent guesses and the vectors with first block $f$. This is why every
iterate of the preconditioned method has the form $x_k = (B^{-1}(f - E y_k); y_k)$. -/
theorem blockUpper_inv_mulVec (hB : IsUnit B) (hUS : IsUnit US) (f : m → R) (y : n → R) :
    (blockUpper B E US)⁻¹ *ᵥ Sum.elim f (US *ᵥ y) = consistentGuess B E f y := by
  rw [inv_blockUpper hB hUS, consistentGuess, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add,
    Matrix.nonsing_inv_mulVec_mulVec hUS]
  refine congrArg₂ Sum.elim ?_ rfl
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, Matrix.nonsing_inv_mulVec_mulVec hUS,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

/-- If $L_S$ is invertible, the inverse of the left preconditioner maps the right-hand side $(f; g)$
to $(f; L_S^{-1} g')$, with $g' = g - F B^{-1} f$. -/
theorem blockLower_inv_mulVec (hLS : IsUnit LS) (f : m → R) (g : n → R) :
    (blockLower B F LS)⁻¹ *ᵥ Sum.elim f g = Sum.elim f (LS⁻¹ *ᵥ reducedRhs B F f g) := by
  rw [inv_blockLower hLS, reducedRhs, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec, add_zero]
  refine congrArg₂ Sum.elim rfl ?_
  rw [Matrix.mulVec_sub, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  abel

end Block

/-! ### The interface reduction of a block-preconditioned Krylov method -/

section Reduction

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]
variable {B : Matrix m m 𝕜} {E : Matrix m n 𝕜} {F : Matrix n m 𝕜} {C : Matrix n n 𝕜}
  {LS US : Matrix n n 𝕜}

/-- A block lower triangular matrix maps the vectors with zero interior block to themselves, and
acts on them as its trailing diagonal block: for $D \in \mathbb{K}^{m \times m}$,
$Z \in \mathbb{K}^{n \times m}$ and $S \in \mathbb{K}^{n \times n}$,
$$\begin{bmatrix} D & 0 \\ Z & S \end{bmatrix} R_y^T = R_y^T S.$$
-/
theorem toEuclideanLin_fromBlocks_comp_prolong (D : Matrix m m 𝕜) (Z : Matrix n m 𝕜)
    (S : Matrix n n 𝕜) :
    Matrix.toEuclideanLin (Matrix.fromBlocks D 0 Z S) ∘ₗ prolong 𝕜 m n
      = prolong 𝕜 m n ∘ₗ Matrix.toEuclideanLin S :=
  LinearMap.ext fun y => by
    have h : Matrix.toEuclideanLin (Matrix.fromBlocks D 0 Z S) (prolong 𝕜 m n y)
        = WithLp.toLp 2 (Matrix.fromBlocks D 0 Z S *ᵥ Sum.elim (0 : m → 𝕜) (WithLp.ofLp y)) := by
      rw [prolong_apply]; rfl
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h, Matrix.fromBlocks_mulVec]
    simp [prolong_toLp, Matrix.toLpLin_apply]

omit [Fintype m] [DecidableEq m] in
/-- For $f \in \mathbb{K}^m$ and $w, w_0 \in \mathbb{K}^n$, $(f; w) = (f; w_0) + R_y^T (w - w_0)$.
Applied to $w = U_S y$, this splits the transformed iterate $U_A x$ of a consistent $x$ into the
initial one and a prolonged correction. -/
theorem toLp_sumElim_eq_add_prolong (f : m → 𝕜) (w w₀ : n → 𝕜) :
    (WithLp.toLp 2 (Sum.elim f w) : EuclideanSpace 𝕜 (m ⊕ n))
      = WithLp.toLp 2 (Sum.elim f w₀)
        + prolong 𝕜 m n (WithLp.toLp 2 w - WithLp.toLp 2 w₀) := by
  rw [show (WithLp.toLp 2 w - WithLp.toLp 2 w₀ : EuclideanSpace 𝕜 n) = WithLp.toLp 2 (w - w₀) from
    rfl, prolong_toLp]
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  cases j with
  | inl i => simp
  | inr j => simp

/-- Let $B$, $L_S$ and $U_S$ be invertible, and let $x_0 = (B^{-1}(f - E y_0); y_0)$ be a consistent
initial guess. Then the initial residual of the split-preconditioned system at $u_0 = U_A x_0$
lies in the interface block:
$$L_A^{-1} \begin{bmatrix} f \\ g \end{bmatrix} - L_A^{-1} A U_A^{-1} u_0
  = R_y^T \left( L_S^{-1} g' - L_S^{-1} S U_S^{-1} U_S y_0 \right),$$
with $g' = g - F B^{-1} f$. This is the residual computation of (14.53) of [saad2003iterative]. -/
theorem residual_consistentGuess (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : m → 𝕜)
    (g y₀ : n → 𝕜) :
    (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g) : EuclideanSpace 𝕜 (m ⊕ n))
        - Matrix.toEuclideanLin (precondMatrix B E F C LS US)
          (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀))
      = prolong 𝕜 m n (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
          - Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
            (WithLp.toLp 2 (US *ᵥ y₀))) := by
  rw [blockLower_inv_mulVec hLS, blockUpper_mulVec_consistentGuess hB,
    precondMatrix_eq hB hLS hUS]
  have hT : Matrix.toEuclideanLin (Matrix.fromBlocks 1 0 0
        (precondSchurComplement B E F C LS US)) (WithLp.toLp 2 (Sum.elim f (US *ᵥ y₀)))
      = WithLp.toLp 2 (Sum.elim f (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀))) := by
    change WithLp.toLp 2 (Matrix.fromBlocks 1 0 0 (precondSchurComplement B E F C LS US) *ᵥ
      Sum.elim f (US *ᵥ y₀)) = _
    rw [Matrix.fromBlocks_mulVec]
    simp
  rw [hT]
  have hS : Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
      (WithLp.toLp 2 (US *ᵥ y₀))
      = WithLp.toLp 2 (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) := rfl
  rw [hS, show (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
      - WithLp.toLp 2 (precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) :
        EuclideanSpace 𝕜 n)
    = WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g
      - precondSchurComplement B E F C LS US *ᵥ (US *ᵥ y₀)) from rfl, prolong_toLp]
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  cases j with
  | inl i => simp
  | inr j => simp

/-- Let $B$, $L_S$ and $U_S$ be invertible. Then the split-preconditioned operator maps the vectors
with zero interior block to themselves, and acts on them as the preconditioned Schur complement:
$$L_A^{-1} A U_A^{-1} R_y^T = R_y^T L_S^{-1} S U_S^{-1}.$$

This is the intertwining hypothesis of the transfer theorems, such as
`DomainDecomposition.isMinResidualIterate_map_iff`. -/
theorem precondMatrix_comp_prolong (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    Matrix.toEuclideanLin (precondMatrix B E F C LS US) ∘ₗ prolong 𝕜 m n
      = prolong 𝕜 m n ∘ₗ Matrix.toEuclideanLin (precondSchurComplement B E F C LS US) := by
  rw [precondMatrix_eq hB hLS hUS]
  exact toEuclideanLin_fromBlocks_comp_prolong 1 0 _

/-- Let $B$, $L_S$ and $U_S$ be invertible, let $x_0 = (B^{-1}(f - E y_0); y_0)$ be a consistent
initial guess, and let $r_0$ and $s_0$ be the initial residuals of the split-preconditioned full
and reduced systems at $U_A x_0$ and $U_S y_0$. Then for every $k \in \mathbb{N}$,
$$\mathcal{K}_k(L_A^{-1} A U_A^{-1}, r_0) = R_y^T \, \mathcal{K}_k(L_S^{-1} S U_S^{-1}, s_0).$$
This is (14.54) of [saad2003iterative].

Every Krylov vector of the full system has a zero interior block; this is the whole argument.
The residuals are $r_0 = L_A^{-1}(f; g) - L_A^{-1} A U_A^{-1} U_A x_0$ and $s_0 = L_S^{-1} g' -
L_S^{-1} S U_S^{-1} U_S y_0$. -/
theorem krylov_subspace_eq_map_of_consistent (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : m → 𝕜) (g y₀ : n → 𝕜) (k : ℕ) :
    Krylov.subspace (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        ((WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g) : EuclideanSpace 𝕜 (m ⊕ n))
          - Matrix.toEuclideanLin (precondMatrix B E F C LS US)
            (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀))) k
      = (Krylov.subspace (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)
            - Matrix.toEuclideanLin (precondSchurComplement B E F C LS US)
              (WithLp.toLp 2 (US *ᵥ y₀))) k).map (prolong 𝕜 m n) := by
  exact krylov_subspace_residual_eq_map (precondMatrix_comp_prolong hB hLS hUS)
    (residual_consistentGuess hB hLS hUS f g y₀) k

/-- Let $B$, $L_S$ and $U_S$ be invertible, let $f \in \mathbb{K}^m$, $g, y_0, y \in \mathbb{K}^n$
and $k \in \mathbb{N}$, and let $x_0 = (B^{-1}(f - E y_0); y_0)$ and $x = (B^{-1}(f - E y); y)$
be the consistent guesses at $y_0$ and $y$. Then $U_A x$ is a minimal-residual Krylov iterate at
step $k$ of
$$L_A^{-1} A U_A^{-1} u = L_A^{-1} \begin{bmatrix} f \\ g \end{bmatrix}$$
from $U_A x_0$ if and only if $U_S y$ is a minimal-residual Krylov iterate at step $k$ of
$$L_S^{-1} S U_S^{-1} w = L_S^{-1} g'$$
from $U_S y_0$, where $g' = g - F B^{-1} f$. In words: a minimal-residual Krylov method on the
full system, preconditioned on the left by $L_A$ and on the right by $U_A$ and started from a
consistent initial guess, is the same method on the reduced system $S y = g'$, preconditioned on
the left by $L_S$ and on the right by $U_S$ and started from $y_0$. This is Propositions 14.11
and 14.12 of [saad2003iterative]: the case $L_S = U_S = I$ is Proposition 14.11, and the general
case is Proposition 14.12.

Both sides are written in the variables that the split-preconditioned method iterates on,
$u = U_A x$ for the full system and $w = U_S y$ for the reduced system. The specification is
`Krylov.IsMinResidualIterate`. The proof applies
`DomainDecomposition.isMinResidualIterate_map_iff` with $P = R_y^T$. -/
theorem isMinResidual_iff_isMinResidual_schurComplement (hB : IsUnit B) (hLS : IsUnit LS)
    (hUS : IsUnit US) (f : m → 𝕜) (g y₀ y : n → 𝕜) (k : ℕ) :
    Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResidualIterate
        (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  rw [blockUpper_mulVec_consistentGuess hB, blockUpper_mulVec_consistentGuess hB,
    toLp_sumElim_eq_add_prolong f (US *ᵥ y) (US *ᵥ y₀),
    ← blockUpper_mulVec_consistentGuess (E := E) (US := US) hB f y₀]
  exact isMinResidualIterate_map_iff (inner_prolong_prolong 𝕜 m n) hcomm
    (residual_consistentGuess hB hLS hUS f g y₀) k _

/-- Let $B$, $L_S$ and $U_S$ be invertible, and let $x_0 = (B^{-1}(f - E y_0); y_0)$ be a consistent
initial guess. Then every minimal-residual Krylov iterate $u$ at step $k$ of
$$L_A^{-1} A U_A^{-1} u = L_A^{-1} \begin{bmatrix} f \\ g \end{bmatrix}$$
from $U_A x_0$ is $u = U_A x$ for a consistent $x = (B^{-1}(f - E y); y)$, where $U_S y$ is a
minimal-residual Krylov iterate at step $k$ of $L_S^{-1} S U_S^{-1} w = L_S^{-1} g'$ from
$U_S y_0$. This is Proposition 14.11 and (14.51) of [saad2003iterative], in the direction in
which the source states them.

With `DomainDecomposition.blockUpper_inv_mulVec`, which recovers $x$ from $U_A x$, this is the
statement of the source that the method "produces iterates of the form (14.51)". -/
theorem exists_isMinResidual_schurComplement (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : m → 𝕜) (g y₀ : n → 𝕜) (k : ℕ) {u : EuclideanSpace 𝕜 (m ⊕ n)}
    (hu : Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
      (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : n → 𝕜,
      Krylov.IsMinResidualIterate (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
          (WithLp.toLp 2 (US *ᵥ y))
        ∧ u = WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  obtain ⟨w, hw, hwu⟩ := exists_isMinResidualIterate_of_isMinResidualIterate_map
    (inner_prolong_prolong 𝕜 m n) hcomm (residual_consistentGuess hB hLS hUS f g y₀) k hu
  have hUS' : US *ᵥ (US⁻¹ *ᵥ WithLp.ofLp w) = WithLp.ofLp w :=
    Matrix.mulVec_nonsing_inv_mulVec hUS _
  refine ⟨US⁻¹ *ᵥ WithLp.ofLp w, by rwa [hUS'], ?_⟩
  rw [blockUpper_mulVec_consistentGuess hB, hUS', hwu,
    blockUpper_mulVec_consistentGuess (E := E) (US := US) hB,
    toLp_sumElim_eq_add_prolong f (WithLp.ofLp w) (US *ᵥ y₀)]

/-- Let $B$, $L_S$ and $U_S$ be invertible, and let $x_0$ and $x$ be the consistent guesses at $y_0$
and $y$. Then $U_A x$ is a Galerkin Krylov iterate at step $k$ of
$L_A^{-1} A U_A^{-1} u = L_A^{-1}(f; g)$ from $U_A x_0$ if and only if $U_S y$ is a Galerkin
Krylov iterate at step $k$ of $L_S^{-1} S U_S^{-1} w = L_S^{-1} g'$ from $U_S y_0$, where
$g' = g - F B^{-1} f$.

This is the Galerkin counterpart of
`DomainDecomposition.isMinResidual_iff_isMinResidual_schurComplement`. With it, Propositions
14.11 and 14.12 of [saad2003iterative] apply to FOM, CG and the Lanczos method as well as to
GMRES and MINRES. The specification is `Krylov.IsGalerkinIterate`. -/
theorem isGalerkin_iff_isGalerkin_schurComplement (hB : IsUnit B) (hLS : IsUnit LS)
    (hUS : IsUnit US) (f : m → 𝕜) (g y₀ y : n → 𝕜) (k : ℕ) :
    Krylov.IsGalerkinIterate (Matrix.toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate
        (Matrix.toEuclideanLin (precondSchurComplement B E F C LS US))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) := by
  have hcomm := precondMatrix_comp_prolong (E := E) (F := F) (C := C) hB hLS hUS
  rw [blockUpper_mulVec_consistentGuess hB, blockUpper_mulVec_consistentGuess hB,
    toLp_sumElim_eq_add_prolong f (US *ᵥ y) (US *ᵥ y₀),
    ← blockUpper_mulVec_consistentGuess (E := E) (US := US) hB f y₀]
  exact isGalerkinIterate_map_iff (inner_prolong_prolong 𝕜 m n) hcomm
    (residual_consistentGuess hB hLS hUS f g y₀) k _

end Reduction

/-! ### The preconditioner induced on the interface -/

section Induced

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Let $M_A$ be a square matrix indexed by $m \oplus n$. The **induced preconditioner** of $M_A$ on
the interface is
$$M_S = \left( (M_A^{-1})_{22} \right)^{-1} = (R_y M_A^{-1} R_y^T)^{-1},$$
the inverse of the trailing diagonal block of $M_A^{-1}$, as in (14.46) of [saad2003iterative].
To apply $M_S^{-1}$ to a vector $v$, one solves $M_A (x; y) = (0; v)$ and keeps $y$.

The inverses are `Matrix.inv`, which is $0$ for a singular matrix. The second form is
`DomainDecomposition.inducedPreconditioner_eq_inv_restrict_mul`. -/
noncomputable def inducedPreconditioner (MA : Matrix (m ⊕ n) (m ⊕ n) R) : Matrix n n R :=
  ((MA⁻¹).toBlocks₂₂)⁻¹

/-- The induced preconditioner in the form of (14.46) of [saad2003iterative]:
$M_S = (R_y M_A^{-1} R_y^T)^{-1}$. -/
theorem inducedPreconditioner_eq_inv_restrict_mul (MA : Matrix (m ⊕ n) (m ⊕ n) R) :
    inducedPreconditioner MA = (restrictMatrix R m n * MA⁻¹ * prolongMatrix R m n)⁻¹ := by
  rw [inducedPreconditioner, restrictMatrix_mul_mul_prolongMatrix]

variable {LB UB : Matrix m m R} {X : Matrix n m R} {Y : Matrix m n R} {LS US : Matrix n n R}

/-- Let $L_B, U_B \in R^{m \times m}$ and $L_S, U_S \in R^{n \times n}$ be invertible, and let
$X \in R^{n \times m}$ and $Y \in R^{m \times n}$. Then the trailing diagonal block of the
inverse of the product of block triangular matrices is
$$\left( \left( \begin{bmatrix} L_B & 0 \\ X & L_S \end{bmatrix} \begin{bmatrix} U_B & Y \\ 0 &
  U_S \end{bmatrix} \right)^{-1} \right)_{22} = U_S^{-1} L_S^{-1}.$$
This is the computation in §14.4.1 of [saad2003iterative], where the other blocks are not
written out. -/
theorem toBlocks₂₂_inv_fromBlocks_mul (hLB : IsUnit LB) (hLS : IsUnit LS) (hUB : IsUnit UB)
    (hUS : IsUnit US) :
    (((Matrix.fromBlocks LB 0 X LS * Matrix.fromBlocks UB Y 0 US)⁻¹).toBlocks₂₂)
      = US⁻¹ * LS⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff _ _ _ (iff_of_true hUB hUS),
    Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (iff_of_true hLB hLS),
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
  simp

/-- Let $L_B, U_B \in R^{m \times m}$ and $L_S, U_S \in R^{n \times n}$ be invertible, let
$X \in R^{n \times m}$ and $Y \in R^{m \times n}$, and let $M_A = L_A U_A$ with
$$L_A = \begin{bmatrix} L_B & 0 \\ X & L_S \end{bmatrix}, \qquad
  U_A = \begin{bmatrix} U_B & Y \\ 0 & U_S \end{bmatrix}.$$
Then the preconditioner that $M_A$ induces on the interface is $M_S = L_S U_S$. This is
Proposition 14.10 of [saad2003iterative].

By `DomainDecomposition.restrictMatrix_mul_mul_prolongMatrix`, $L_S = R_y L_A R_y^T$ and
$U_S = R_y U_A R_y^T$: the $L$ and $U$ factors of $M_S$ are the $(2,2)$ blocks of the $L$ and
$U$ factors of $M_A$. -/
theorem inducedPreconditioner_eq (hLB : IsUnit LB) (hLS : IsUnit LS) (hUB : IsUnit UB)
    (hUS : IsUnit US) :
    inducedPreconditioner (Matrix.fromBlocks LB 0 X LS * Matrix.fromBlocks UB Y 0 US)
      = LS * US := by
  rw [inducedPreconditioner, toBlocks₂₂_inv_fromBlocks_mul hLB hLS hUB hUS, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hLS),
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hUS)]

end Induced

end DomainDecomposition
