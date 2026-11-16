/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Compression of an operator to a subspace

Let $A$ be a linear operator on an inner product space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $K$ be a subspace with an orthogonal projection $P_K$. The **compression** of
$A$ to $K$ is the operator $A_K = P_K A|_K$ on $K$, also called the section of $A$ on $K$. More
generally, a linear map $Q \colon E \to K$ that fixes $K$ gives the oblique compression $Q A|_K$.
The Rayleigh–Ritz method for eigenvalue problems and the Arnoldi and Lanczos matrices $H_m$ and
$T_m$ for linear systems are compressions to a Krylov subspace. The two error constants of these
methods are the Céa constant $\|A\| / c$ and the Rayleigh–Ritz constant
$\gamma = \|P_K A (1 - P_K)\|$.

The module proves that a polynomial in the compression agrees with the same polynomial in $A$ on a
vector whose orbit $x, Ax, A^2 x, \dots$ stays in $K$; this makes a Krylov subspace the natural
choice of $K$. It also proves the Galerkin characterization $\langle A_K x, y \rangle = \langle A x,
y \rangle$ for $x, y \in K$, and the residual identity behind the Rayleigh–Ritz eigenvalue error
bounds of Theorem 4.3 of [saad2011numerical].

## Main definitions

* `compressionBy`: the compression $Q A|_K$ through a linear map $Q \colon E \to K$.
* `compression`: the compression $P_K A|_K$ through the orthogonal projection.

## Main results

* `compressionBy.aeval_apply_of_forall_pow_mem`: if $Q$ fixes $K$ and $A^i x \in K$ for all
  $i \le \deg p$, then $p(Q A|_K) x = p(A) x$.
* `compressionBy.apply_aeval_of_forall_pow_lt_mem`: if $Q$ fixes $K$ and $A^i x \in K$ for all
  $i < \deg p$, then $Q \, p(A) x = p(Q A|_K) x$.
* `compression.eq_compressionBy`: the compression is the oblique compression through $P_K$.
* `compression.inner_apply`: the Galerkin characterization $\langle A_K x, y \rangle = \langle A x,
  y \rangle$ for $x, y \in K$.
* `compression.isSymmetric`: the compression of a symmetric operator is symmetric.
* `compression.apply_sub_smul_orthogonalProjection`: if $A u = \mu u$, then
  $A_K P_K u - \mu P_K u = -P_K A (u - P_K u)$.

## Implementation notes

* The degree $\deg p$ is `Polynomial.natDegree`, so the zero polynomial has degree $0$.
* The compression `compression A K` is defined through `Submodule.orthogonalProjectionOnto`, and
  `compression.eq_compressionBy` transfers every result about `compressionBy` to it.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $K$ be a subspace of an inner product space $E$, let $Q \colon E \to K$ be a linear map, and
let $A$ be a linear operator on $E$. The **compression of $A$ through $Q$** is the linear map
$$Q A|_K \colon K \to K, \qquad x \mapsto Q(Ax).$$

The definition takes any linear map $Q$. The results about it assume that $Q$ is a projector
onto $K$, that is, $Q x = x$ for $x \in K$; then this is the oblique Rayleigh–Ritz compression.
The orthogonal case is `compression`, by `compression.eq_compressionBy`. -/
def compressionBy {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (A : E →ₗ[𝕜] E) : K →ₗ[𝕜] K :=
  Q.comp (A.comp K.subtype)

namespace compressionBy

variable {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (hQ : ∀ x : K, Q x = x) (A : E →ₗ[𝕜] E)
include hQ

/-- A linear map $Q \colon E \to K$ that fixes $K$ satisfies $Q z = z$ for every $z \in K$. -/
private theorem coe_apply_of_mem {z : E} (hz : z ∈ K) : (Q z : E) = z :=
  congrArg Subtype.val (hQ ⟨z, hz⟩)

/-- If $Q$ fixes $K$ and $A^j x \in K$ for all $j \le i$, then $(Q A|_K)^i x = A^i x$. -/
private theorem coe_pow_apply {x : K} (i : ℕ) (hx : ∀ j ≤ i, (A ^ j) (x : E) ∈ K) :
    (((compressionBy Q A) ^ i) x : E) = (A ^ i) (x : E) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := ih fun j hj => hx j (hj.trans (Nat.le_succ i))
    have hstep : A ((A ^ i) (x : E)) = (A ^ (i + 1)) (x : E) := by rw [pow_succ' A i]; rfl
    rw [pow_succ' (compressionBy Q A) i]
    change (Q (A ((((compressionBy Q A) ^ i) x : K) : E)) : E) = _
    rw [hi, hstep]
    exact coe_apply_of_mem Q hQ (hx (i + 1) le_rfl)

/-- If $Q$ fixes $K$ and $A^j x \in K$ for all $j < i$, then $Q(A^i x) = (Q A|_K)^i x$. -/
private theorem apply_pow (i : ℕ) {x : K} (hx : ∀ j < i, (A ^ j) (x : E) ∈ K) :
    Q ((A ^ i) (x : E)) = ((compressionBy Q A) ^ i) x := by
  cases i with
  | zero => simpa using hQ x
  | succ i =>
    have hi := coe_pow_apply Q hQ A i fun j hj => hx j (Nat.lt_succ_of_le hj)
    have hstep : A ((A ^ i) (x : E)) = (A ^ (i + 1)) (x : E) := by rw [pow_succ' A i]; rfl
    rw [pow_succ' (compressionBy Q A) i]
    change _ = Q (A ((((compressionBy Q A) ^ i) x : K) : E))
    rw [hi, hstep]

/-- Let $K$ be a subspace of an inner product space $E$, let $Q \colon E \to K$ be a linear map with
$Q x = x$ for every $x \in K$, let $A$ be a linear operator on $E$, and let $p$ be a polynomial.
If $x \in K$ and $A^i x \in K$ for all $i \le \deg p$, then
$$p(Q A|_K) \, x = p(A) \, x.$$
-/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compressionBy Q A) p x : E) = aeval A p (x : E) := by
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    SetLike.val_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coe_pow_apply Q hQ A i fun j hj =>
    hx j (hj.trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]

/-- Let $K$ be a subspace of an inner product space $E$, let $Q \colon E \to K$ be a linear map with
$Q x = x$ for every $x \in K$, let $A$ be a linear operator on $E$, and let $p$ be a polynomial.
If $x \in K$ and $A^i x \in K$ for all $i < \deg p$, then
$$Q \, p(A) \, x = p(Q A|_K) \, x.$$
Compared with `compressionBy.aeval_apply_of_forall_pow_mem`, the condition on the orbit needs
one degree less, because $Q$ is applied at the end. -/
theorem apply_aeval_of_forall_pow_lt_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i < p.natDegree, (A ^ i) (x : E) ∈ K) :
    Q (aeval A p (x : E)) = aeval (compressionBy Q A) p x := by
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [apply_pow Q hQ A i fun j hj =>
    hx j (hj.trans_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]

end compressionBy

/-- Let $A$ be a linear operator on an inner product space $E$, and let $K$ be a subspace with an
orthogonal projection $P_K$. The **compression** of $A$ to $K$ is the linear map
$$A_K = P_K A|_K \colon K \to K, \qquad x \mapsto P_K (A x).$$
-/
noncomputable def compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K →ₗ[𝕜] K :=
  (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- The compression $P_K A|_K$ is the oblique compression `compressionBy` through the orthogonal
projection $P_K \colon E \to K$. So every result about `compressionBy` applies to it. -/
theorem eq_compressionBy :
    compression A K = compressionBy (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) A := rfl

/-- Let $A$ be a linear operator on an inner product space $E$, let $K$ be a subspace with an
orthogonal projection, and let $p$ be a polynomial. If $x \in K$ and $A^i x \in K$ for all
$i \le \deg p$, then
$$p(A_K) \, x = p(A) \, x.$$

A typical case is the Krylov subspace $K = \mathcal{K}_{m+1}(A, x)$ and $\deg p \le m$. -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compression A K) p x : E) = aeval A p (x : E) :=
  compressionBy.aeval_apply_of_forall_pow_mem _ K.orthogonalProjectionOnto_mem_subspace_eq_self A p
    hx

/-- Let $A$ be a linear operator on an inner product space $E$, and let $K$ be a subspace with an
orthogonal projection. Then for all $x, y \in K$,
$$\langle A_K x, y \rangle = \langle A x, y \rangle.$$
This is the Galerkin (Rayleigh–Ritz) characterization of the compression: the projection is
invisible against a test vector from $K$. It gives the symmetry and the bounds of the
compression. -/
theorem inner_apply (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) (y : E) := by
  have h := K.starProjection_inner_eq_zero (A (x : E)) (y : E) y.2
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

/-- Let $A$ be a linear operator on an inner product space $E$, and let $K$ be a subspace with an
orthogonal projection. Then $\langle x, A_K y \rangle = \langle x, A y \rangle$ for all
$x, y \in K$. This is `compression.inner_apply` with the compression in the second argument. -/
theorem inner_apply' (x y : K) : inner 𝕜 x (compression A K y) = inner 𝕜 (x : E) (A y) := by
  rw [← inner_conj_symm x (compression A K y), inner_apply, inner_conj_symm]

/-- Let $A$ be a symmetric linear operator on an inner product space $E$, and let $K$ be a subspace
with an orthogonal projection. Then the compression $A_K$ is symmetric. In matrix terms, the
Rayleigh–Ritz matrix of a Hermitian operator is Hermitian. -/
theorem isSymmetric (hA : A.IsSymmetric) : (compression A K).IsSymmetric := fun x y => by
  rw [inner_apply, inner_apply', hA]

/-- **Compression commutes with negation.** Let $A$ be a linear operator on an inner product space
$E$, and let $K$ be a subspace with an orthogonal projection. Then
$$(-A)_K = -A_K.$$

This turns a statement about the largest Ritz value of $A$ into the matching statement about the
smallest one. -/
theorem neg : compression (-A) K = -compression A K :=
  LinearMap.ext fun x => by simp [compression]

/-- Let $A$ be a linear operator on an inner product space $E$, let $K$ be a subspace with an
orthogonal projection, and let $(b_i)_{i \in \iota}$ be an orthonormal basis of $K$ indexed by a
finite type. Then the matrix of the compression $A_K$ in this basis has the entries
$$(A_K)_{ij} = \langle b_i, A b_j \rangle.$$
-/
theorem toMatrix_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 K) :
    LinearMap.toMatrix b.toBasis b.toBasis (compression A K) =
      Matrix.of fun i j => inner 𝕜 (b i : E) (A (b j)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply]
  exact inner_apply' A K (b i) (b j)

/-- Let $A$ be a linear operator on an inner product space $E$, and let $K$ be a subspace with an
orthogonal projection. If $K$ is invariant under $A$, then the compression is the restriction:
$A_K x = A x$ for every $x \in K$. -/
theorem apply_of_invt (hK : K ∈ Module.End.invtSubmodule A) (x : K) :
    (compression A K x : E) = A x :=
  congrArg Subtype.val (K.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨A (x : E), (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ x.2⟩)

/-- Let $A$ be a linear operator on an inner product space $E$, and let $K$ be a subspace with an
orthogonal projection $P_K$. If $u \in E$ and $\mu \in \mathbb{K}$ satisfy $A u = \mu u$, then
$$A_K P_K u - \mu P_K u = -P_K A (u - P_K u).$$
Since $P_K (1 - P_K) = 0$, the right-hand side is also $-P_K (A - \mu)(1 - P_K) u$. The identity
bounds the residual of the Ritz pair $(\mu, P_K u)$ by the part of the exact eigenvector $u$
that $K$ does not capture. It is the identity behind the Rayleigh–Ritz eigenvalue error bounds
of Theorem 4.3 of [saad2011numerical].

The sign follows from $P_K A P_K u - \mu P_K u = P_K A (P_K - 1) u$. So the right-hand side of
the display in Theorem 4.3 of [saad2011numerical] carries a minus sign. The sign does not matter
for the norm estimates that use this identity. -/
theorem apply_sub_smul_orthogonalProjection {u : E} {μ : 𝕜} (hu : A u = μ • u) :
    (compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E) =
      -K.starProjection (A (u - K.starProjection u)) := by
  have hp : A (K.starProjection u) = μ • u - A (u - K.starProjection u) := by
    rw [map_sub, ← hu]; abel
  change K.starProjection (A (K.starProjection u)) - μ • K.starProjection u = _
  rw [hp, map_sub, map_smul]
  abel

end compression
