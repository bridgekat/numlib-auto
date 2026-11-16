/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 1.12: Projection operators

This module formalizes §1.12 of [saad2003iterative]: projectors (1.58), the projector onto a
subspace $M$ orthogonally to a subspace $L$ (1.59)–(1.62), its matrix representations (1.63)–(1.66),
and orthogonal projectors (1.67)–(1.72), with Lemma 1.36, Proposition 1.37, Theorem 1.38 and
Corollary 1.39. A projector is a matrix $P \in \mathbb{K}^{n \times n}$ with $P^2 = P$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$. For subspaces $M$ and $L$ of $\mathbb{K}^n$ of the
same dimension, the projection of $x$ onto $M$ orthogonally to $L$ is the vector $u$ with
$$u \in M, \qquad x - u \perp L.$$

The module proves that this $u$ exists and is unique exactly when no nonzero vector of $M$ is
orthogonal to $L$ (Lemma 1.36). For bases $V$ of $M$ and $W$ of $L$, the projector is
$P = V(W^H V)^{-1} W^H$, and $P = V W^H$ when $W^H V = I$. A projector is orthogonal exactly when it
is Hermitian (Proposition 1.37), and the orthogonal projector onto $M$ gives the best approximation
of $x$ from $M$ (Theorem 1.38 and Corollary 1.39). The proofs specialize the backbone modules
`Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection` and `Numlib.Projection.Basic`.

## Main definitions

* §1.12.1, `Matrix.IsProjector`: a projector is an idempotent matrix, $P^2 = P$.
* Equation (1.67), `Matrix.IsOrthogonalProjector`: a projector whose null space is the orthogonal
  complement of its range.
* §1.12.3, `Matrix.cols`: the columns of a matrix as vectors of $\mathbb{K}^n$.
* §1.12.3, `Matrix.IsBasisOf`: the columns of $V$ form a basis of the subspace $M$.
* Equation (1.63), `Matrix.IsBiorthogonal`: $W^H V = I$.
* Equation (1.66), `Matrix.obliqueProj`: the matrix $V(W^H V)^{-1} W^H$.
* Equations (1.59)–(1.60), `SaadSparse.IsProjOnto`: $u \in M$ and $x - u \perp L$.
* §1.12.2, `SaadSparse.obliqueProjection`: the projector onto $M$ orthogonally to $L$.

## Main results

* Lemma 1.36, `SaadSparse.Chapter01.lemma_1_36`: for $\dim M = \dim L$, no nonzero vector of $M$ is
  orthogonal to $L$ if and only if every $x$ has a unique projection onto $M$ orthogonally to $L$.
* Equation (1.65), `SaadSparse.Chapter01.obliqueProj_of_biorthogonal`: for biorthogonal bases,
  $P = V W^H$.
* Equation (1.66), `SaadSparse.Chapter01.obliqueProj_isProjOnto`: $V(W^H V)^{-1} W^H$ is the
  projector onto $M$ orthogonally to $L$.
* Equations (1.68)–(1.70), `SaadSparse.Chapter01.isProjector_conjTranspose`,
  `SaadSparse.Chapter01.ker_conjTranspose_eq_orthogonal_range` and
  `SaadSparse.Chapter01.ker_eq_orthogonal_range_conjTranspose`: $P^H$ is a projector,
  $\operatorname{Null}(P^H) = \operatorname{Ran}(P)^\perp$ and $\operatorname{Null}(P) =
  \operatorname{Ran}(P^H)^\perp$.
* Proposition 1.37, `SaadSparse.Chapter01.proposition_1_37`: a projector is orthogonal if and only
  if it is Hermitian.
* Equation (1.71), `SaadSparse.Chapter01.toEuclideanLin_mul_conjTranspose`: for $V$ with orthonormal
  columns spanning $M$, $V V^H$ is the orthogonal projector onto $M$.
* Theorem 1.38, `SaadSparse.Chapter01.theorem_1_38`: $\min_{y \in M} \|x - y\|_2 = \|x - Px\|_2$ for
  the orthogonal projector $P$ onto $M$.
* Corollary 1.39, `SaadSparse.Chapter01.corollary_1_39`: for $y \in M$, $\|x - y\|_2$ is minimal
  over $M$ if and only if $x - y \perp M$.

## Implementation notes

* The backbone counterparts of the projectors of the book are `IsIdempotentElem` on the linear maps
  of `EuclideanSpace 𝕜 (Fin n)`, `LinearMap.obliqueProjectionOfBases` and
  `Submodule.starProjection`.

## Deviations from the source

* **§1.12.4, $\|P\|_2 = 1$ for an orthogonal projector** (reading). The claim needs $P \neq 0$,
  because the zero matrix is the orthogonal projector onto $\{0\}$. The module states the bound
  $\|Px\|_2 \le \|x\|_2$, which holds for every orthogonal projector. See
  `SaadSparse.Chapter01.norm_apply_le`.
* **Corollary 1.39** (reading). The book's "$\min_{y \in M}$" is read with $y$ ranging over $M$, so
  $y \in M$ is a hypothesis and the statement is about the least element of the set of distances.
  See `SaadSparse.Chapter01.corollary_1_39`.
-/

open Module Submodule

open scoped SaadSparse

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### Projectors (1.58) and orthogonal projectors (1.67) -/

/-- **Section 1.12.1** of [saad2003iterative], projectors. A matrix $P \in \mathbb{K}^{n \times n}$
is a **projector** if it is idempotent, $P^2 = P$. -/
abbrev IsProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop := IsIdempotentElem P

/-- A matrix $P$ is a projector if and only if the operator $x \mapsto Px$ on $\mathbb{K}^n$ is
idempotent. -/
theorem isProjector_iff_isIdempotentElem_toEuclideanLin (P : Matrix (Fin n) (Fin n) 𝕜) :
    P.IsProjector ↔ IsIdempotentElem (toEuclideanLin P) := by
  constructor
  · intro h
    change toEuclideanLin P ∘ₗ toEuclideanLin P = toEuclideanLin P
    rw [← toEuclideanLin_mul, h]
  · intro h
    refine toEuclideanLin.injective ?_
    rw [toEuclideanLin_mul]
    exact h

/-- **Equation (1.67)** of [saad2003iterative]. A matrix $P \in \mathbb{K}^{n \times n}$ is an
**orthogonal projector** if it is a projector and its null space is the orthogonal complement of
its range:
$$P^2 = P, \qquad \operatorname{Null}(P) = \operatorname{Ran}(P)^\perp.$$
-/
def IsOrthogonalProjector (P : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  IsIdempotentElem P ∧
    LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin P))ᗮ

/-! ### Bases and matrix representations (1.63)–(1.66) -/

/-- The columns $v_1, \dots, v_m$ of a matrix $V \in \mathbb{K}^{n \times m}$, as a family of
vectors of $\mathbb{K}^n$. -/
def cols (V : Matrix (Fin n) (Fin m) 𝕜) : Fin m → EuclideanSpace 𝕜 (Fin n) :=
  fun j => WithLp.toLp 2 (Vᵀ j)

omit [RCLike 𝕜] in
/-- Entry $i$ of column $j$ of $V$ is $v_{ij}$. -/
@[simp]
theorem ofLp_cols_apply (V : Matrix (Fin n) (Fin m) 𝕜) (j : Fin m) (i : Fin n) :
    WithLp.ofLp (V.cols j) i = V i j := rfl

/-- **Section 1.12.3** of [saad2003iterative], bases of a subspace. The matrix $V = [v_1, \dots,
v_m] \in \mathbb{K}^{n \times m}$ is a **basis** of the subspace $M$ of $\mathbb{K}^n$ if its
columns are linearly independent and span $M$. -/
structure IsBasisOf (V : Matrix (Fin n) (Fin m) 𝕜) (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    Prop where
  /-- The columns of `V` are linearly independent. -/
  linearIndependent : LinearIndependent 𝕜 V.cols
  /-- The columns of `V` span `M`. -/
  span_eq : Submodule.span 𝕜 (Set.range V.cols) = M

/-- The basis of the subspace $M$ given by the columns of $V$, as a `Module.Basis`, for use with the
backbone statements that are phrased with `Module.Basis`. -/
noncomputable def IsBasisOf.toBasis {V : Matrix (Fin n) (Fin m) 𝕜}
    {M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hV : V.IsBasisOf M) :
    Module.Basis (Fin m) 𝕜 M :=
  (Module.Basis.span hV.linearIndependent).map (LinearEquiv.ofEq _ _ hV.span_eq)

/-- The vectors of the basis `Matrix.IsBasisOf.toBasis` are the columns of $V$. -/
@[simp]
theorem IsBasisOf.coe_toBasis_apply {V : Matrix (Fin n) (Fin m) 𝕜}
    {M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hV : V.IsBasisOf M) (j : Fin m) :
    (hV.toBasis j : EuclideanSpace 𝕜 (Fin n)) = V.cols j := by
  simp [IsBasisOf.toBasis]

/-- **Equation (1.63)** of [saad2003iterative]. Two matrices $V, W \in \mathbb{K}^{n \times m}$ are
**biorthogonal** if $W^H V = I$. -/
def IsBiorthogonal (V W : Matrix (Fin n) (Fin m) 𝕜) : Prop := Wᴴ * V = 1

/-- **Equation (1.66)** of [saad2003iterative]. For $V, W \in \mathbb{K}^{n \times m}$, the matrix
$$P = V (W^H V)^{-1} W^H.$$
When the columns of $V$ and $W$ are bases of $M$ and $L$ and $W^H V$ is nonsingular, $P$ is the
projector onto $M$ orthogonally to $L$ (`SaadSparse.Chapter01.obliqueProj_isProjOnto`).

If $W^H V$ is singular, the inverse is Mathlib's `Matrix.inv`, which is $0$. -/
noncomputable def obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  V * (Wᴴ * V)⁻¹ * Wᴴ

/-- The backbone's cross-Gram matrix of the columns of $V$ and $W$ is $W^H V$. -/
theorem crossGram_cols (V W : Matrix (Fin n) (Fin m) 𝕜) :
    LinearMap.crossGram 𝕜 V.cols W.cols = Wᴴ * V := by
  ext i j
  simp [LinearMap.crossGram, EuclideanSpace.inner_eq_star_dotProduct, Matrix.mul_apply, dotProduct,
    mul_comm]

/-- For $W \in \mathbb{K}^{n \times m}$ and $x \in \mathbb{K}^n$, the vector $W^H x$ has entries
$(x, w_i)$, the inner products that the backbone uses. -/
theorem conjTranspose_mulVec_eq_inner (W : Matrix (Fin n) (Fin m) 𝕜)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    (Wᴴ *ᵥ WithLp.ofLp x) = fun i => inner 𝕜 (W.cols i) x := by
  funext i
  simp [EuclideanSpace.inner_eq_star_dotProduct, mulVec, dotProduct, mul_comm]

/-- The operator of the matrix $V(W^H V)^{-1} W^H$ of (1.66) is the backbone's
`LinearMap.obliqueProjectionOfBases` for the columns of $V$ and $W$. -/
theorem toEuclideanLin_obliqueProj (V W : Matrix (Fin n) (Fin m) 𝕜) :
    toEuclideanLin (obliqueProj V W) = LinearMap.obliqueProjectionOfBases 𝕜 V.cols W.cols := by
  refine LinearMap.ext fun x => ?_
  have hrhs : LinearMap.obliqueProjectionOfBases 𝕜 V.cols W.cols x
      = ∑ j, ((Wᴴ * V)⁻¹ *ᵥ (Wᴴ *ᵥ WithLp.ofLp x)) j • V.cols j := by
    change ∑ j, (LinearMap.crossGram 𝕜 V.cols W.cols)⁻¹.mulVec
      (fun i => inner 𝕜 (W.cols i) x) j • V.cols j = _
    rw [crossGram_cols, ← conjTranspose_mulVec_eq_inner]
  have hlhs : toEuclideanLin (obliqueProj V W) x
      = toEuclideanLin V (WithLp.toLp 2 ((Wᴴ * V)⁻¹ *ᵥ (Wᴴ *ᵥ WithLp.ofLp x))) := by
    change WithLp.toLp 2 ((V * (Wᴴ * V)⁻¹ * Wᴴ) *ᵥ WithLp.ofLp x) = _
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    rfl
  rw [hlhs, hrhs, toEuclideanLin_apply_eq_sum]
  rfl

end Matrix

namespace SaadSparse

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}

/-! ### The projector onto $M$ orthogonally to $L$ (1.59)–(1.62) -/

/-- **Equations (1.59)–(1.60)** of [saad2003iterative]. For subspaces $M$ and $L$ of $\mathbb{K}^n$
and $x, u \in \mathbb{K}^n$, the vector $u$ is a **projection of $x$ onto $M$ orthogonally to
$L$** if
$$u \in M, \qquad x - u \perp L.$$
-/
def IsProjOnto (M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) (x u : EuclideanSpace 𝕜 (Fin n)) :
    Prop := u ∈ M ∧ x - u ∈ Lᗮ

/-- **Section 1.12.2** of [saad2003iterative], the projector onto $M$ orthogonally to $L$. Let $M$
and $L$ be subspaces of $\mathbb{K}^n$ with $\dim M = \dim L$ and $M \cap L^\perp = \{0\}$, that
is no nonzero vector of $M$ is orthogonal to $L$. Then there is a unique idempotent linear map
$P$ on $\mathbb{K}^n$ with range $M$ and null space $L^\perp$, and this definition is that map. -/
noncomputable def obliqueProjection (M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot hd h).exists.choose

variable {M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))}

/-- The projector onto $M$ orthogonally to $L$ is idempotent, its range is $M$, and its null space
is $L^\perp$. -/
theorem obliqueProjection_spec (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    IsIdempotentElem (obliqueProjection M L hd h) ∧
      LinearMap.range (obliqueProjection M L hd h) = M ∧
      LinearMap.ker (obliqueProjection M L hd h) = Lᗮ :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot hd h).exists.choose_spec

/-- **Equation (1.62)** of [saad2003iterative], range. The range of the projector onto $M$
orthogonally to $L$ is $M$. -/
theorem range_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    LinearMap.range (obliqueProjection M L hd h) = M := (obliqueProjection_spec hd h).2.1

/-- **Equation (1.62)** of [saad2003iterative], null space. The null space of the projector onto $M$
orthogonally to $L$ is $L^\perp$. -/
theorem ker_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥) :
    LinearMap.ker (obliqueProjection M L hd h) = Lᗮ := (obliqueProjection_spec hd h).2.2

/-- **Equations (1.59)–(1.60)** of [saad2003iterative], the defining property. Let $P$ be the
projector onto $M$ orthogonally to $L$. Then for $x, u \in \mathbb{K}^n$, $Px = u$ if and only
if $u \in M$ and $x - u \perp L$. -/
theorem isProjOnto_iff_eq_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x u : EuclideanSpace 𝕜 (Fin n)) :
    IsProjOnto M L x u ↔ obliqueProjection M L hd h x = u :=
  (LinearMap.IsIdempotentElem.apply_eq_iff (obliqueProjection_spec hd h).1
    (range_obliqueProjection hd h) (ker_obliqueProjection hd h) x u).symm

/-- For the projector $P$ onto $M$ orthogonally to $L$ and every $x$, the vector $Px$ is a
projection of $x$ onto $M$ orthogonally to $L$: $Px \in M$ and $x - Px \perp L$. -/
theorem isProjOnto_obliqueProjection (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x : EuclideanSpace 𝕜 (Fin n)) : IsProjOnto M L x (obliqueProjection M L hd h x) :=
  (isProjOnto_iff_eq_obliqueProjection hd h x _).mpr rfl

/-- **Equation (1.62)** of [saad2003iterative]. For the projector $P$ onto $M$ orthogonally to $L$,
$Px = 0$ if and only if $x \perp L$. -/
theorem obliqueProjection_eq_zero_iff (hd : finrank 𝕜 M = finrank 𝕜 L) (h : M ⊓ Lᗮ = ⊥)
    (x : EuclideanSpace 𝕜 (Fin n)) : obliqueProjection M L hd h x = 0 ↔ x ∈ Lᗮ := by
  rw [← LinearMap.mem_ker, ker_obliqueProjection]

/-- The orthogonal case $L = M$ of (1.59)–(1.60): $u \in M$ and $x - u \perp M$ if and only if $u$
is the orthogonal projection of $x$ onto $M$, Mathlib's `Submodule.starProjection`. -/
theorem isProjOnto_self_iff_eq_starProjection (x u : EuclideanSpace 𝕜 (Fin n)) :
    IsProjOnto M M x u ↔ u = M.starProjection x := by
  refine ⟨fun h => (Submodule.eq_starProjection_of_mem_orthogonal h.1 h.2).symm, ?_⟩
  rintro rfl
  exact ⟨M.starProjection_apply_mem x, M.sub_starProjection_mem_orthogonal x⟩

end SaadSparse

namespace SaadSparse.Chapter01

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ}
variable {M L : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))}

/-! ### Basic properties of projectors (1.58) -/

/-- **Section 1.12.1** of [saad2003iterative]. If $P$ is a projector, then $I - P$ is a projector.
-/
theorem isProjector_one_sub {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    (1 - P).IsProjector := hP.one_sub

/-- **Section 1.12.1** of [saad2003iterative]. If $P$ is a projector, then $\operatorname{Null}(P) =
\operatorname{Ran}(I - P)$. -/
theorem ker_eq_range_one_sub {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    LinearMap.ker (toEuclideanLin P) = LinearMap.range (toEuclideanLin (1 - P)) := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  have h1 : toEuclideanLin (1 - P) = 1 - toEuclideanLin P := by
    rw [map_sub, toEuclideanLin_one]; rfl
  rw [h1]
  exact LinearMap.IsIdempotentElem.ker_eq_range_one_sub hidem

/-- **Section 1.12.1** of [saad2003iterative]. If $P$ is a projector, then $\mathbb{K}^n =
\operatorname{Ran}(P) \oplus \operatorname{Null}(P)$; in particular $\operatorname{Null}(P) \cap
\operatorname{Ran}(P) = \{0\}$. -/
theorem isCompl_range_ker {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    IsCompl (LinearMap.range (toEuclideanLin P)) (LinearMap.ker (toEuclideanLin P)) :=
  LinearMap.IsIdempotentElem.isCompl
    ((isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP)

/-- **Section 1.12.1** of [saad2003iterative]. If $M$ and $L$ are complementary subspaces of
$\mathbb{K}^n$, there is a unique projector with range $M$ and null space $L$. -/
theorem existsUnique_projector (h : IsCompl M L) :
    ∃! P : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n),
      IsIdempotentElem P ∧ LinearMap.range P = M ∧ LinearMap.ker P = L := by
  refine ⟨M.projection L h, ⟨Submodule.isIdempotentElem_projection h,
    Submodule.range_projection h, Submodule.ker_projection h⟩, ?_⟩
  rintro Q ⟨hQ, hQr, hQk⟩
  exact LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq hQ
    (Submodule.isIdempotentElem_projection h)
    (hQr.trans (Submodule.range_projection h).symm)
    (hQk.trans (Submodule.ker_projection h).symm)

/-- **Section 1.12.1** of [saad2003iterative]. If $P$ is a projector, then $\dim
\operatorname{Ran}(I - P) + \dim \operatorname{Ran}(P) = n$. So if $P$ has rank $m$, then
$\operatorname{Ran}(I - P)$ has dimension $n - m$. -/
theorem finrank_range_one_sub_add {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    finrank 𝕜 (LinearMap.range (toEuclideanLin (1 - P)))
      + finrank 𝕜 (LinearMap.range (toEuclideanLin P)) = n := by
  rw [← ker_eq_range_one_sub hP, add_comm,
    LinearMap.finrank_range_add_finrank_ker (toEuclideanLin P)]
  simp

/-! ### Lemma 1.36 -/

/-- **Lemma 1.36** of [saad2003iterative]. Let $M$ and $L$ be subspaces of $\mathbb{K}^n$ of the
same dimension. Then no nonzero vector of $M$ is orthogonal to $L$ if and only if for every
$x \in \mathbb{K}^n$ there is a unique $u$ with
$$u \in M, \qquad x - u \perp L.$$
-/
theorem lemma_1_36 (hd : finrank 𝕜 M = finrank 𝕜 L) :
    (∀ v ∈ M, v ∈ Lᗮ → v = 0) ↔ ∀ x, ∃! u, IsProjOnto M L x u := by
  constructor
  · intro hv x
    have hbot : M ⊓ Lᗮ = ⊥ := by
      refine le_antisymm (fun z hz => ?_) bot_le
      exact (Submodule.mem_bot 𝕜).mpr (hv z hz.1 hz.2)
    exact ⟨obliqueProjection M L hd hbot x, isProjOnto_obliqueProjection hd hbot x,
      fun y hy => ((isProjOnto_iff_eq_obliqueProjection hd hbot x y).mp hy).symm⟩
  · intro h v hvM hvL
    obtain ⟨u, -, hu⟩ := h v
    have h0 : (0 : EuclideanSpace 𝕜 (Fin n)) = u := hu 0 ⟨M.zero_mem, by simpa using hvL⟩
    have hv0 : v = u := hu v ⟨hvM, by simp⟩
    rw [hv0, ← h0]

/-! ### Matrix representations (1.63)–(1.66) -/

section Bases

variable {V W : Matrix (Fin n) (Fin m) 𝕜}

/-- **Equation (1.65)** of [saad2003iterative]. Let $V, W \in \mathbb{K}^{n \times m}$ be
biorthogonal, $W^H V = I$. Then $V(W^H V)^{-1} W^H = V W^H$. -/
theorem obliqueProj_of_biorthogonal (h : IsBiorthogonal V W) : obliqueProj V W = V * Wᴴ := by
  rw [obliqueProj, show Wᴴ * V = 1 from h, inv_one]
  simp

/-- **Section 1.12.3** of [saad2003iterative]. Let $W \in \mathbb{K}^{n \times m}$ be a basis of
$L$. Then for $z \in \mathbb{K}^n$, $W^H z = 0$ if and only if $z \perp L$. -/
theorem conjTranspose_mulVec_eq_zero_iff (hW : W.IsBasisOf L) (z : EuclideanSpace 𝕜 (Fin n)) :
    Wᴴ *ᵥ WithLp.ofLp z = 0 ↔ z ∈ Lᗮ := by
  rw [Matrix.conjTranspose_mulVec_eq_zero_iff, ← hW.span_eq, Submodule.mem_orthogonal_span,
    Set.forall_mem_range]
  rfl

/-- For $V \in \mathbb{K}^{n \times m}$ and $y \in \mathbb{K}^m$, the vector $Vy$ lies in the span
of the columns of $V$. -/
theorem toEuclideanLin_mem_span (V : Matrix (Fin n) (Fin m) 𝕜)
    (y : EuclideanSpace 𝕜 (Fin m)) : (V ⬝ y) ∈ Submodule.span 𝕜 (Set.range V.cols) := by
  rw [show (V ⬝ y) = toEuclideanLin V (WithLp.toLp 2 (WithLp.ofLp y)) from rfl,
    toEuclideanLin_apply_eq_sum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- **Equation (1.64)** of [saad2003iterative]. Let $V$ be a basis of $M$ and $W$ a basis of $L$,
both in $\mathbb{K}^{n \times m}$. Then for $x \in \mathbb{K}^n$ and $y \in \mathbb{K}^m$, the
vector $Vy$ is the projection of $x$ onto $M$ orthogonally to $L$ if and only if
$$W^H (x - Vy) = 0.$$
-/
theorem isProjOnto_iff_conjTranspose_mulVec_eq_zero (hV : V.IsBasisOf M) (hW : W.IsBasisOf L)
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) :
    IsProjOnto M L x (V ⬝ y) ↔ Wᴴ *ᵥ (WithLp.ofLp x - V *ᵥ WithLp.ofLp y) = 0 := by
  have hmem : (V ⬝ y) ∈ M := hV.span_eq ▸ toEuclideanLin_mem_span V y
  have hsub : WithLp.ofLp (x - (V ⬝ y)) = WithLp.ofLp x - V *ᵥ WithLp.ofLp y := rfl
  rw [IsProjOnto, ← conjTranspose_mulVec_eq_zero_iff hW (x - (V ⬝ y)), hsub]
  simp [hmem]

/-- **Section 1.12.3** of [saad2003iterative]. Let $V$ be a basis of $M$ and $W$ a basis of $L$,
both in $\mathbb{K}^{n \times m}$. Then $W^H V$ is nonsingular if and only if no nonzero vector
of $M$ is orthogonal to $L$, which is the hypothesis of Lemma 1.36. -/
theorem isUnit_conjTranspose_mul_iff (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) :
    IsUnit (Wᴴ * V) ↔ ∀ v ∈ M, v ∈ Lᗮ → v = 0 := by
  have hzero : ∀ y : Fin m → 𝕜, (Wᴴ * V) *ᵥ y = 0 ↔
      (V ⬝ (WithLp.toLp 2 y : EuclideanSpace 𝕜 (Fin m))) ∈ Lᗮ := by
    intro y
    rw [← conjTranspose_mulVec_eq_zero_iff hW, ← mulVec_mulVec]
    rfl
  constructor
  · intro h v hvM hvL
    rw [← hV.span_eq] at hvM
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hvM
    have hVc : (V ⬝ (WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin m))) = ∑ k, c k • V.cols k :=
      toEuclideanLin_apply_eq_sum V c
    have h0 : (Wᴴ * V) *ᵥ c = 0 := (hzero c).mpr (by rw [hVc]; exact hvL)
    have hc : c = 0 :=
      mulVec_injective_iff_isUnit.mpr h (a₁ := c) (a₂ := 0) (by rw [h0, mulVec_zero])
    rw [hc]
    simp
  · intro hcond
    refine mulVec_injective_iff_isUnit.mp fun u v huv => ?_
    have hsub : (Wᴴ * V) *ᵥ (u - v) = 0 := by
      rw [mulVec_sub, huv, sub_self]
    have hmemM : (V ⬝ (WithLp.toLp 2 (u - v) : EuclideanSpace 𝕜 (Fin m))) ∈ M :=
      hV.span_eq ▸ toEuclideanLin_mem_span V _
    have hzeroV := hcond _ hmemM ((hzero (u - v)).mp hsub)
    rw [toEuclideanLin_apply_eq_sum] at hzeroV
    have hli := Fintype.linearIndependent_iff.mp hV.linearIndependent (u - v) hzeroV
    funext i
    have hi := hli i
    rwa [Pi.sub_apply, sub_eq_zero] at hi

/-- **Equation (1.66)** of [saad2003iterative]. Let $V$ be a basis of $M$ and $W$ a basis of $L$,
both in $\mathbb{K}^{n \times m}$, with $W^H V$ nonsingular. Then for every
$x \in \mathbb{K}^n$, the vector $Px$ with $P = V(W^H V)^{-1} W^H$ is the projection of $x$ onto
$M$ orthogonally to $L$. -/
theorem obliqueProj_isProjOnto (hV : V.IsBasisOf M) (hW : W.IsBasisOf L) (h : IsUnit (Wᴴ * V))
    (x : EuclideanSpace 𝕜 (Fin n)) : IsProjOnto M L x (obliqueProj V W ⬝ x) := by
  have h' : IsUnit (LinearMap.crossGram 𝕜 V.cols W.cols) := by rw [crossGram_cols]; exact h
  refine ⟨?_, ?_⟩
  · rw [toEuclideanLin_obliqueProj, ← hV.span_eq,
      ← LinearMap.range_obliqueProjectionOfBases V.cols W.cols h']
    exact LinearMap.mem_range_self _ x
  · rw [toEuclideanLin_obliqueProj, ← hW.span_eq]
    exact LinearMap.sub_obliqueProjectionOfBases_apply_mem_orthogonal V.cols W.cols h' x

end Bases

/-! ### The adjoint projector (1.68)–(1.70) -/

/-- **Equation (1.68)** of [saad2003iterative]. If $P$ is a projector, then $P^H$ is a projector. -/
theorem isProjector_conjTranspose {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    Pᴴ.IsProjector := by
  change Pᴴ * Pᴴ = Pᴴ
  rw [← conjTranspose_mul, show P * P = P from hP]

/-- **Equation (1.69)** of [saad2003iterative]. For every $P \in \mathbb{K}^{n \times n}$,
$\operatorname{Null}(P^H) = \operatorname{Ran}(P)^\perp$. -/
theorem ker_conjTranspose_eq_orthogonal_range (P : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.ker (toEuclideanLin Pᴴ) = (LinearMap.range (toEuclideanLin P))ᗮ := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.orthogonal_range]

/-- **Equation (1.70)** of [saad2003iterative]. For every $P \in \mathbb{K}^{n \times n}$,
$\operatorname{Null}(P) = \operatorname{Ran}(P^H)^\perp$. -/
theorem ker_eq_orthogonal_range_conjTranspose (P : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.ker (toEuclideanLin P) = (LinearMap.range (toEuclideanLin Pᴴ))ᗮ := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.orthogonal_range,
    LinearMap.adjoint_adjoint]

/-! ### Proposition 1.37 -/

/-- **Proposition 1.37** of [saad2003iterative]. Let $P \in \mathbb{K}^{n \times n}$ be a projector.
Then $P$ is an orthogonal projector if and only if $P$ is Hermitian, $P^H = P$. -/
theorem proposition_1_37 {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector) :
    P.IsOrthogonalProjector ↔ P.IsHermitian := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  rw [← isSymmetric_toEuclideanLin_iff,
    LinearMap.IsIdempotentElem.isSymmetric_iff_orthogonal_range hidem]
  exact ⟨fun h => h.2.symm, fun h => ⟨hP, h.symm⟩⟩

/-- An orthogonal projector $P$ acts as the orthogonal projection onto its range, Mathlib's
`Submodule.starProjection`. -/
theorem toEuclideanLin_eq_starProjection {P : Matrix (Fin n) (Fin n) 𝕜}
    (hP : P.IsOrthogonalProjector) :
    toEuclideanLin P = ((LinearMap.range (toEuclideanLin P)).starProjection :
      EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) := by
  have hidem : IsIdempotentElem (toEuclideanLin P) :=
    (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP.1
  refine LinearMap.ext fun x => (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · exact LinearMap.mem_range_self _ x
  · rw [← hP.2, LinearMap.mem_ker, map_sub,
      (LinearMap.IsIdempotentElem.mem_range_iff hidem).mp (LinearMap.mem_range_self _ x), sub_self]

/-! ### The representation $P = V V^H$ (1.71)–(1.72) -/

section Orthonormal

variable {V : Matrix (Fin n) (Fin m) 𝕜}

/-- For $V \in \mathbb{K}^{n \times m}$, $V^H V = I$ if and only if the columns of $V$ are
orthonormal. -/
theorem conjTranspose_mul_self_eq_one_iff (V : Matrix (Fin n) (Fin m) 𝕜) :
    Vᴴ * V = 1 ↔ Orthonormal 𝕜 V.cols := by
  rw [orthonormal_iff_ite, ← crossGram_cols V V]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.one_apply] at hij
    simpa [LinearMap.crossGram] using hij
  · intro h
    ext i j
    rw [Matrix.one_apply]
    simpa [LinearMap.crossGram] using h i j

/-- **Equation (1.71)** of [saad2003iterative]. Let $V \in \mathbb{K}^{n \times m}$ have orthonormal
columns, $V^H V = I$, that form a basis of $M$. Then $P = V V^H$ is the orthogonal projector
onto $M$. -/
theorem toEuclideanLin_mul_conjTranspose (hV : Vᴴ * V = 1) (hVM : V.IsBasisOf M) :
    toEuclideanLin (V * Vᴴ) = (M.starProjection : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] _) := by
  obtain ⟨hli, rfl⟩ := hVM
  have horth : Orthonormal 𝕜 V.cols := (conjTranspose_mul_self_eq_one_iff V).mp hV
  have hproj : obliqueProj V V = V * Vᴴ := by
    rw [obliqueProj, hV, inv_one]
    simp
  rw [← hproj, toEuclideanLin_obliqueProj,
    LinearMap.obliqueProjectionOfBases_self_eq_starProjection V.cols horth]

/-- **Section 1.12.3** of [saad2003iterative] (Problem P-1.30). Let
$V_1, V_2 \in \mathbb{K}^{n \times m}$ both have orthonormal columns that form a basis of the
same subspace $M$. Then $V_1 V_1^H = V_2 V_2^H$. -/
theorem mul_conjTranspose_eq_of_isBasisOf {V₁ V₂ : Matrix (Fin n) (Fin m) 𝕜}
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (h₁ : V₁.IsBasisOf M) (h₂ : V₂.IsBasisOf M) :
    V₁ * V₁ᴴ = V₂ * V₂ᴴ :=
  toEuclideanLin.injective
    ((toEuclideanLin_mul_conjTranspose hV₁ h₁).trans (toEuclideanLin_mul_conjTranspose hV₂ h₂).symm)

end Orthonormal

/-! ### Properties of orthogonal projectors (§1.12.4) -/

/-- **Section 1.12.4** of [saad2003iterative]. Let $P$ be an orthogonal projector. Then for every
$x \in \mathbb{K}^n$,
$$\|x\|_2^2 = \|Px\|_2^2 + \|(I - P)x\|_2^2.$$
-/
theorem norm_sq_eq_add {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsOrthogonalProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) : ‖x‖ ^ 2 = ‖P ⬝ x‖ ^ 2 + ‖(1 - P) ⬝ x‖ ^ 2 := by
  have hPx : (P ⬝ x) = (LinearMap.range (toEuclideanLin P)).starProjection x :=
    LinearMap.congr_fun (toEuclideanLin_eq_starProjection hP) x
  have hQx : ((1 - P) ⬝ x) = (LinearMap.range (toEuclideanLin P))ᗮ.starProjection x := by
    have hadd := Submodule.starProjection_add_starProjection_orthogonal
      (K := LinearMap.range (toEuclideanLin P)) x
    have h1 : toEuclideanLin (1 - P) = 1 - toEuclideanLin P := by
      rw [map_sub, toEuclideanLin_one]; rfl
    have h2 := eq_sub_of_add_eq' hadd
    rw [h2, ← hPx]
    change toEuclideanLin (1 - P) x = _
    rw [h1, LinearMap.sub_apply, Module.End.one_apply]
  rw [hPx, hQx]
  exact (LinearMap.range (toEuclideanLin P)).norm_sq_eq_add_norm_sq_starProjection x

/-- **Section 1.12.4** of [saad2003iterative]. An orthogonal projector $P$ is a contraction:
$\|Px\|_2 \le \|x\|_2$ for every $x$.

**Reading.** The book states $\|P\|_2 = 1$ for every orthogonal projector $P$. This needs
$P \neq 0$: the zero matrix is the orthogonal projector onto $\{0\}$, and its norm is $0$. The
statement here is the bound $\|P\|_2 \le 1$, in the form $\|Px\|_2 \le \|x\|_2$, which holds
with no condition on $P$. -/
theorem norm_apply_le {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsOrthogonalProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) : ‖P ⬝ x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_add hP x
  nlinarith [norm_nonneg ((1 - P) ⬝ x), norm_nonneg (P ⬝ x), norm_nonneg x]

/-- **Section 1.12.4** of [saad2003iterative]. The eigenvalues of a projector
$P \in \mathbb{C}^{n \times n}$ are in $\{0, 1\}$. -/
theorem spectrum_subset_pair {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsProjector) :
    spectrum ℂ P ⊆ {0, 1} := by
  intro μ hμ
  obtain ⟨v, hv, hv0⟩ :=
    ((hasEigenvalue_toEuclideanLin_iff P μ).mpr hμ).exists_hasEigenvector
  have hPv : toEuclideanLin P v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hidem := (isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP
  have h2 : μ • v = (μ * μ) • v := by
    conv_lhs => rw [← hPv, ← DFunLike.congr_fun hidem v]
    change toEuclideanLin P (toEuclideanLin P v) = _
    rw [hPv, map_smul, hPv, smul_smul]
  have hμ2 : μ * μ = μ := by
    by_contra hne
    refine hv0 ?_
    have hs : (μ - μ * μ) • v = 0 := by rw [sub_smul, ← h2, sub_self]
    rcases smul_eq_zero.mp hs with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rcases eq_or_ne μ 0 with rfl | h0
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (by
      have : μ * μ = μ * 1 := by rw [mul_one]; exact hμ2
      simpa using mul_left_cancel₀ h0 this)

/-- **Section 1.12.4** of [saad2003iterative]. Let $P$ be a projector. Then $x$ is in the range of
$P$ if and only if $Px = x$, that is $x$ is fixed by $P$. -/
theorem mem_range_iff_eigen_one {P : Matrix (Fin n) (Fin n) 𝕜} (hP : P.IsProjector)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    x ∈ LinearMap.range (toEuclideanLin P) ↔ (P ⬝ x) = x :=
  LinearMap.IsIdempotentElem.mem_range_iff
    (p := toEuclideanLin P) ((isProjector_iff_isIdempotentElem_toEuclideanLin P).mp hP)

/-! ### Theorem 1.38 and Corollary 1.39 -/

/-- **Theorem 1.38** of [saad2003iterative]. Let $M$ be a subspace of $\mathbb{K}^n$, let $P$ be the
orthogonal projector onto $M$, and let $x \in \mathbb{K}^n$. Then
$$\min_{y \in M} \|x - y\|_2 = \|x - Px\|_2.$$

The minimum is the least element of the set $\{\|x - y\|_2 : y \in M\}$, and $P$ is Mathlib's
`Submodule.starProjection`. -/
theorem theorem_1_38 (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))) (x : EuclideanSpace 𝕜 (Fin n)) :
    IsLeast ((fun y => ‖x - y‖) '' (M : Set (EuclideanSpace 𝕜 (Fin n))))
      ‖x - M.starProjection x‖ := by
  refine ⟨⟨M.starProjection x, M.starProjection_apply_mem x, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.norm_sub_le_of_forall_inner_eq_zero (M.starProjection_apply_mem x)
    (fun w hw => M.starProjection_inner_eq_zero x w hw) hy

/-- **Corollary 1.39** of [saad2003iterative]. Let $M$ be a subspace of $\mathbb{K}^n$, let
$x \in \mathbb{K}^n$, and let $y \in M$. Then $\|x - y\|_2$ is the least element of
$\{\|x - z\|_2 : z \in M\}$ if and only if $x - y \perp M$.

**Reading.** The book's "$\min_{y \in M}$" is read with $y$ ranging over $M$, so membership
$y \in M$ is a hypothesis and not part of the conclusion. A vector $y \notin M$ at the same
distance from $x$ would break the literal equivalence. -/
theorem corollary_1_39 (M : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    {x y : EuclideanSpace 𝕜 (Fin n)} (hy : y ∈ M) :
    IsLeast ((fun z => ‖x - z‖) '' (M : Set (EuclideanSpace 𝕜 (Fin n)))) ‖x - y‖ ↔
      x - y ∈ Mᗮ := by
  constructor
  · intro hmin
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact Submodule.inner_eq_zero_of_forall_norm_sub_le hy
      (fun w hw => hmin.2 ⟨w, hw, rfl⟩) hu
  · intro h
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero hy
      (fun u hu => (Submodule.mem_orthogonal' _ _).1 h u hu) hw

end SaadSparse.Chapter01
