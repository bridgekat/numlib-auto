/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.GramMatrix`, beside `Matrix.gram`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Numlib.Data.Fin.Sum

/-!
# Gram determinants and the distance to the span of a finite family

Let $v = (v_i)_{i \in \iota}$ be a finite family in an inner product space $E$ over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $f \in E$. Write $G(v)$ for the Gram matrix
$(\langle v_i, v_j \rangle)_{i, j}$, $G(v, f)$ for the Gram matrix of the family $v$ enlarged by
$f$, and $P$ for the orthogonal projection onto $\operatorname{span}\{v_i\}$. The Gram determinants
determine the distance from $f$ to the span of $v$:
$$\det G(v, f) = \det G(v) \, \|f - Pf\|^2, \qquad \|f - Pf\|^2 = \frac{\det G(v, f)}{\det G(v)}
  \text{ if } v \text{ is linearly independent}.$$
This classical formula reads the error of a best approximation off two determinants. In
[gantmacher1959theory], Chapter IX §5, it is the recursion satisfied by the Gram determinants of a
nested family; in [han2009theoretical], §3.1, it drives the proof of the Müntz–Szász theorem.
Mathlib has `Matrix.gram` and its positive semidefiniteness, but no determinant formula of this
kind.

## Main results

* `Matrix.gram_sum_smul`: the Gram matrix of the family $w_j = \sum_i T_{ij} v_i$ is $T^H G(v) T$.
* `Matrix.det_gram_sumElim`: the product form $\det G(v, f) = \det G(v) \|f - Pf\|^2$, with no
  hypothesis on $v$.
* `Matrix.det_gram_cons` and `Matrix.det_gram_sumElim_eq_det_gram_cons`: the same for a family
  indexed by `Fin n` and enlarged at the front by `Fin.cons`, the form that a concrete family takes,
  and the reindexing between the two forms.
* `Submodule.norm_sub_starProjection_sq_eq_det_gram_div` and
  `Submodule.iInf_norm_sub_sq_eq_det_gram_div`: the quotient form, for a linearly independent
  family, where the denominator is nonzero, with the distance written through the projection or as
  an infimum. `Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real` and
  `Submodule.iInf_norm_sub_sq_eq_det_gram_div_real` restate them for real scalars.

## Proof outline

Let $g = f - Pf$. Replacing $f$ by $g$ changes the enlarged family by a unitriangular change of
basis $T$, which adds a combination of the $v_i$ to the last vector, and so leaves the Gram
determinant fixed by `Matrix.gram_sum_smul`. Since $g$ is orthogonal to every $v_i$, the Gram matrix
of the new family is block diagonal, with determinant $\det G(v) \|g\|^2$. The quotient
$\det G(v, f) / \det G(v)$ is the Schur complement of the block $G(v)$ in $G(v, f)$, a $1 \times 1$
matrix, but the proof does not use Schur complements. The argument above is shorter than inverting
$G(v)$ and identifying the Schur complement with the squared error through the normal equations, and
it needs no hypothesis on $v$.

## Implementation notes

* The enlarged family is `Sum.elim v (fun _ : Unit ↦ f) : ι ⊕ Unit → E`, so that its Gram matrix is
  literally a `Matrix.fromBlocks` and no reindexing equivalence appears. This is the convention of
  `Mathlib.LinearAlgebra.Matrix.SchurComplement`.
* The orthogonal projection is `Submodule.starProjection`, and the Gram matrix is `Matrix.gram 𝕜 v`,
  with entries $\langle v_i, v_j \rangle$.
-/

open scoped InnerProductSpace

variable {ι κ E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $v$ be a family indexed by a finite type in an inner product space $E$. Then the span of $v$
is finite-dimensional, so it has an orthogonal projection.

Mathlib has this instance for the span of a `Finset` (`FiniteDimensional.span_finset`) and for a
single vector, but not for the range of a family indexed by a finite type. -/
instance Submodule.hasOrthogonalProjection_span_range [Finite ι] (v : ι → E) :
    (Submodule.span 𝕜 (Set.range v)).HasOrthogonalProjection :=
  haveI := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  inferInstance

namespace Matrix

/-- Let $v = (v_i)_{i \in \iota}$ be a finite family in $E$ and let
$T \in \mathbb{K}^{\iota \times \kappa}$. The Gram matrix of the family of linear combinations
$w_j = \sum_i T_{ij} v_i$, $j \in \kappa$, is
$$G(w) = T^H G(v) T.$$
-/
theorem gram_sum_smul [Fintype ι] (v : ι → E) (T : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j ↦ ∑ i, T i j • v i) = Tᴴ * gram 𝕜 v * T := by
  ext j k
  rw [gram_apply, ← star_dotProduct_gram_mulVec v (fun i ↦ T i j) (fun i ↦ T i k),
    Matrix.mul_assoc]
  simp [dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum]

/-- Let $v = (v_i)_{i \in \iota}$ be a family in $E$ and let $g \in E$ satisfy
$\langle v_i, g \rangle = 0$ for all $i$. Then the Gram matrix of $v$ enlarged by $g$ is block
diagonal:
$$G(v, g) = \begin{bmatrix} G(v) & 0 \\ 0 & \langle g, g \rangle \end{bmatrix}.$$
-/
theorem gram_sumElim_of_inner_eq_zero (v : ι → E) {g : E} (hg : ∀ i, ⟪v i, g⟫_𝕜 = 0) :
    gram 𝕜 (Sum.elim v fun _ : Unit ↦ g)
      = fromBlocks (gram 𝕜 v) 0 0 (of fun _ _ ↦ ⟪g, g⟫_𝕜) := by
  ext i j
  cases i <;> cases j <;> simp [gram_apply, hg, inner_eq_zero_symm.2 (hg _)]

section Adjoin

variable [Fintype ι] [DecidableEq ι]

/-- Let $v = (v_i)_{i \in \iota}$ be a finite family in $E$ and let $g \in E$ satisfy
$\langle v_i, g \rangle = 0$ for all $i$. Then
$$\det G(v, g) = \det G(v) \, \langle g, g \rangle.$$
-/
theorem det_gram_sumElim_of_inner_eq_zero (v : ι → E) {g : E} (hg : ∀ i, ⟪v i, g⟫_𝕜 = 0) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ g)).det = (gram 𝕜 v).det * ⟪g, g⟫_𝕜 := by
  rw [gram_sumElim_of_inner_eq_zero v hg, det_fromBlocks_zero₂₁,
    det_unique (of fun _ _ ↦ ⟪g, g⟫_𝕜 : Matrix Unit Unit 𝕜), of_apply]

/-- **Gram's determinant formula for the distance to a span**, product form. Let
$v = (v_i)_{i \in \iota}$ be a finite family in $E$, let $f \in E$, and let $P$ be the
orthogonal projection onto $\operatorname{span}\{v_i\}$. Then
$$\det G(v, f) = \det G(v) \, \|f - Pf\|^2.$$

No hypothesis on $v$ is needed: if $v$ is linearly dependent, both sides vanish. The norm
$\|f - Pf\|$ is the distance from $f$ to the span of $v$, and it is cast to $\mathbb{K}$. -/
theorem det_gram_sumElim (v : ι → E) (f : E) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det
      = (gram 𝕜 v).det * (‖f - (Submodule.span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2 := by
  set K := Submodule.span 𝕜 (Set.range v) with hK
  set g := f - K.starProjection f with hgdef
  have hg : ∀ i, ⟪v i, g⟫_𝕜 = 0 := fun i ↦
    (Submodule.mem_orthogonal K g).1 (K.sub_starProjection_mem_orthogonal f) (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨a, ha⟩ : ∃ a : ι → 𝕜, ∑ i, a i • v i = K.starProjection f :=
    (Submodule.mem_span_range_iff_exists_fun 𝕜).1 (K.starProjection_apply_mem f)
  set T : Matrix (ι ⊕ Unit) (ι ⊕ Unit) 𝕜 := fromBlocks 1 (of fun i (_ : Unit) ↦ a i) 0 1 with hT
  have key : (Sum.elim v fun _ : Unit ↦ f)
      = fun j ↦ ∑ i, T i j • (Sum.elim v fun _ : Unit ↦ g) i := by
    funext j
    rw [Fintype.sum_sum_type]
    cases j with
    | inl i₀ => simp [hT, Matrix.one_apply]
    | inr u => simp [hT, ha, hgdef]
  have hdetT : T.det = 1 := by rw [hT, det_fromBlocks_zero₂₁, det_one, det_one, one_mul]
  rw [key, gram_sum_smul, det_mul, det_mul, det_conjTranspose, hdetT, star_one, one_mul, mul_one,
    det_gram_sumElim_of_inner_eq_zero v hg, inner_self_eq_norm_sq_to_K]

end Adjoin

section Cons

/-- Let $v = (v_0, \dots, v_{n-1})$ be a family in $E$ and let $f \in E$. Enlarging $v$ by $f$ at
the end, indexed by `Fin n ⊕ Unit`, or at the front, $(f, v_0, \dots, v_{n-1})$ indexed by
`Fin (n + 1)` through `Fin.cons`, gives the same Gram determinant. -/
theorem det_gram_sumElim_eq_det_gram_cons {n : ℕ} (v : Fin n → E) (f : E) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det
      = (gram 𝕜 (Fin.cons f v : Fin (n + 1) → E)).det := by
  rw [← det_submatrix_equiv_self (finSuccEquivSumUnit n)
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f))]
  congr 1
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp [finSuccEquivSumUnit]

/-- **Gram's determinant formula for the distance to a span**, product form, for a family indexed by
`Fin n` enlarged at the front. Let $v = (v_0, \dots, v_{n-1})$ be a family in $E$, let
$f \in E$, and let $P$ be the orthogonal projection onto $\operatorname{span}\{v_i\}$. Then
$$\det G(f, v_0, \dots, v_{n-1}) = \det G(v) \, \|f - Pf\|^2.$$
-/
theorem det_gram_cons {n : ℕ} (v : Fin n → E) (f : E) :
    (gram 𝕜 (Fin.cons f v : Fin (n + 1) → E)).det
      = (gram 𝕜 v).det * (‖f - (Submodule.span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2 := by
  rw [← det_gram_sumElim_eq_det_gram_cons, det_gram_sumElim]

end Cons

end Matrix

namespace Submodule

variable [Fintype ι] [DecidableEq ι]

/-- **Gram's determinant formula for the distance to a span**, quotient form. Let
$v = (v_i)_{i \in \iota}$ be a finite linearly independent family in $E$, let $f \in E$, and let
$P$ be the orthogonal projection onto $\operatorname{span}\{v_i\}$. Then
$$\|f - Pf\|^2 = \frac{\det G(v, f)}{\det G(v)}.$$

The norm is cast to $\mathbb{K}$. Linear independence makes the denominator nonzero. -/
theorem norm_sub_starProjection_sq_eq_det_gram_div {v : ι → E} (hv : LinearIndependent 𝕜 v)
    (f : E) :
    (‖f - (span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2
      = (Matrix.gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram 𝕜 v).det :=
  (eq_div_iff (Matrix.det_gram_ne_zero_iff_linearIndependent.2 hv)).2
    (by rw [Matrix.det_gram_sumElim, mul_comm])

/-- **Gram's determinant formula for the distance to a span**, quotient form, in a real inner
product space. Let $v = (v_i)_{i \in \iota}$ be a finite linearly independent family in a real
inner product space $E$, let $f \in E$, and let $P$ be the orthogonal projection onto
$\operatorname{span}\{v_i\}$. Then
$$\|f - Pf\|^2 = \frac{\det G(v, f)}{\det G(v)}.$$
-/
theorem norm_sub_starProjection_sq_eq_det_gram_div_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : ι → E} (hv : LinearIndependent ℝ v) (f : E) :
    ‖f - (span ℝ (Set.range v)).starProjection f‖ ^ 2
      = (Matrix.gram ℝ (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram ℝ v).det :=
  norm_sub_starProjection_sq_eq_det_gram_div hv f

/-- **Gram's determinant formula for the distance to a span**, quotient form, with the distance
written as an infimum. Let $v = (v_i)_{i \in \iota}$ be a finite linearly independent family in
$E$ and let $f \in E$. Then
$$\Bigl(\inf_{x \in \operatorname{span}\{v_i\}} \|f - x\|\Bigr)^2 = \frac{\det G(v, f)}{\det
  G(v)}.$$

The infimum is cast to $\mathbb{K}$. -/
theorem iInf_norm_sub_sq_eq_det_gram_div {v : ι → E} (hv : LinearIndependent 𝕜 v) (f : E) :
    ((⨅ x : span 𝕜 (Set.range v), ‖f - (x : E)‖ : ℝ) : 𝕜) ^ 2
      = (Matrix.gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram 𝕜 v).det := by
  rw [← starProjection_minimal, norm_sub_starProjection_sq_eq_det_gram_div hv]

/-- **Gram's determinant formula for the distance to a span**, infimum form, in a real inner product
space. Let $v = (v_i)_{i \in \iota}$ be a finite linearly independent family in a real inner
product space $E$ and let $f \in E$. Then the squared distance from $f$ to the span of $v$ is
the quotient of Gram determinants:
$$\Bigl(\inf_{x \in \operatorname{span}\{v_i\}} \|f - x\|\Bigr)^2 = \frac{\det G(v, f)}{\det
  G(v)}.$$
-/
theorem iInf_norm_sub_sq_eq_det_gram_div_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : ι → E} (hv : LinearIndependent ℝ v) (f : E) :
    (⨅ x : span ℝ (Set.range v), ‖f - (x : E)‖) ^ 2
      = (Matrix.gram ℝ (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram ℝ v).det :=
  iInf_norm_sub_sq_eq_det_gram_div hv f

end Submodule
