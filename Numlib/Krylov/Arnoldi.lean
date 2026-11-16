/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.GramSchmidt
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Projection.Basic

/-!
# The Arnoldi process

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $A : E \to E$
be linear, and let $b \in E$. The Krylov subspaces are $\mathcal{K}_m = \mathcal{K}_m(A, b) =
\operatorname{span}\{b, Ab, \dots, A^{m-1} b\}$. The **Arnoldi vectors** $v_0, v_1, \dots$ are the
normalized Gram–Schmidt orthogonalization of the Krylov sequence $b, Ab, A^2 b, \dots$; a vector is
$0$ once the sequence has become linearly dependent (breakdown). The **Arnoldi coefficients** are
$h_{ij} = \langle v_i, A v_j \rangle$. This file proves the basic facts of [saad2003iterative]: the
vectors are orthonormal and $\operatorname{span}\{v_0, \dots, v_{m-1}\} = \mathcal{K}_m$
(Proposition 6.4), breakdown happens exactly at the grade of $b$ (Proposition 6.6), the matrix
$(h_{ij})$ is upper Hessenberg, and the **Arnoldi relation**
$$A v_j = \sum_{i=0}^{j+1} h_{ij} v_i$$
holds (Proposition 6.5 and (6.9)). It also identifies the vectors with the classical recurrence
$w_j = A v_j - \sum_{i \le j} h_{ij} v_i$, $v_{j+1} = w_j / \|w_j\|$ of Algorithm 6.1, and gives the
basis-free form $(I - P_{m+1}) A v_m = h_{m+1,m} v_{m+1}$, where $P_{m+1}$ is the orthogonal
projection onto $\mathcal{K}_{m+1}$; this measures how far $\mathcal{K}_{m+1}$ is from being
invariant under $A$ ([saad2011numerical], problem P-6.1).

Three further facts close the file. If a linear map $N$ intertwines two operators, $N B = C N$, then
$N$ carries an Arnoldi vector of $B$ to a vector whose component along the Arnoldi vector of $C$ of
the same step is a nonnegative real; this makes the two families of the Golub–Kahan process line up.
The process is natural under linear isometries, which carries it between an operator and its matrix,
and between isometric models of one space. Finally, the modified Gram–Schmidt form of the process
([saad2003iterative], Algorithm 6.2; [golub2013matrix], Algorithm 10.5.1), which removes the
components along $v_0, \dots, v_j$ one at a time, computes the same vectors in exact arithmetic, and
any sequence that satisfies this recurrence is the sequence of Arnoldi vectors.

## Main definitions

* `Arnoldi.vec`: the Arnoldi vectors $v_j$, the normalized Gram–Schmidt vectors of the Krylov
  sequence, with $v_j = 0$ after breakdown.
* `Arnoldi.coeff`: the Arnoldi coefficients $h_{ij} = \langle v_i, A v_j \rangle$.
* `Arnoldi.w`: the unnormalized next vector $w_j = A v_j - \sum_{i \le j} h_{ij} v_i$.
* `Arnoldi.orthonormalBasis`: the orthonormal basis $v_0, \dots, v_{m-1}$ of $\mathcal{K}_m$ for $m$
  at most the grade.
* `Arnoldi.hessenberg`, `Arnoldi.hessenbergSq`: the $(m+1) \times m$ Hessenberg matrix $\bar H_m$
  and its leading $m \times m$ block $H_m$.
* `Arnoldi.mgsVec`: the Arnoldi vectors computed with modified Gram–Schmidt.

## Main results

* `Arnoldi.span_vec`: $\operatorname{span}\{v_0, \dots, v_{m-1}\} = \mathcal{K}_m$.
* `Arnoldi.inner_vec_eq_zero`, `Arnoldi.orthonormal`: distinct Arnoldi vectors are orthogonal, and
  the vectors below the grade are orthonormal.
* `Arnoldi.vec_eq_zero_iff`: $v_j = 0$ if and only if $j$ is at least the grade of $b$.
* `Arnoldi.apply_vec`: the Arnoldi relation $A v_j = \sum_{i \le j+1} h_{ij} v_i$.
* `Arnoldi.isUpperHessenberg_coeff`: $h_{ij} = 0$ for $i > j + 1$.
* `Arnoldi.vec_succ_eq`, `Arnoldi.coeff_succ_self`: $v_{j+1} = w_j / \|w_j\|$ and
  $h_{j+1,j} = \|w_j\|$.
* `Arnoldi.apply_sum`: the matrix form $A V_m = V_{m+1} \bar H_m$.
* `Arnoldi.hessenbergSq_eq_toMatrix_compression`: $H_m$ is the matrix of the compression of $A$ to
  $\mathcal{K}_m$.
* `Arnoldi.coeff_eq_zero_of_adjoint_mem`: if $A^*$ maps each $v$ into $\mathcal{K}_s(A, v)$, then
  $h_{ij} = 0$ for $i + s \le j$.
* `Arnoldi.inner_vec_apply_vec_of_semiconj`: an intertwining map carries Arnoldi vectors to vectors
  with a nonnegative leading coefficient.
* `Arnoldi.vec_conj_linearIsometryEquiv`, `Arnoldi.coeff_conj_linearIsometryEquiv`: naturality under
  linear isometries.
* `Arnoldi.eq_vec_of_modifiedGramSchmidt`, `Arnoldi.mgsVec_eq_vec`: the modified Gram–Schmidt
  recurrence determines the Arnoldi vectors.

## Implementation notes

* Indices start at $0$: $v_0 = b / \|b\|$, and $v_0, \dots, v_{m-1}$ span $\mathcal{K}_m$, which is
  `Krylov.subspace A b m`.
* The inner product $\langle x, y \rangle$ of Mathlib is conjugate-linear in $x$, so
  $h_{ij} = v_i^H A v_j$ for matrices.
* No hypothesis on the dimension is needed to define the vectors. The results that mention the grade
  assume that the full Krylov space `Krylov.fullSubspace A b` is finite-dimensional.
* After breakdown the vectors are $0$, so most identities hold for all indices without a hypothesis
  on the grade.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

/-- The **Arnoldi vectors** $v_0, v_1, \dots$ of $A$ and $b$: the normalized Gram–Schmidt
orthogonalization of the Krylov sequence $b, Ab, A^2 b, \dots$. Thus $v_j = u_j / \|u_j\|$,
where $u_j$ is the component of $A^j b$ orthogonal to $\mathcal{K}_j$, and $v_j = 0$ if
$u_j = 0$.

The definition is `InnerProductSpace.gramSchmidtNormed` applied to the sequence
$i \mapsto A^i b$. Indices start at $0$. -/
noncomputable def vec (A : E →ₗ[𝕜] E) (b : E) : ℕ → E :=
  InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) b)

/-- The **Arnoldi coefficients** $h_{ij} = \langle v_i, A v_j \rangle$ of $A$ and $b$, the entries
of the Hessenberg matrix of the Arnoldi process.

The inner product is conjugate-linear in its first argument, so for matrices
$h_{ij} = v_i^H A v_j$. Indices start at $0$. -/
noncomputable def coeff (A : E →ₗ[𝕜] E) (b : E) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (vec A b i) (A (vec A b j))

variable (A : E →ₗ[𝕜] E) (b : E)

/-!
### The unnormalized Gram–Schmidt vectors

Let $u_j$ be the unnormalized Gram–Schmidt vectors of the Krylov sequence, so that
$v_j = u_j / \|u_j\|$. The statements about $v_j$ and $w_j$ are proved by first writing both as
nonnegative real multiples of these vectors.
-/

/-- The unnormalized Gram–Schmidt vectors $u_j$ of the Krylov sequence $b, Ab, A^2 b, \dots$. -/
private noncomputable def gs : ℕ → E :=
  InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b)

private theorem gs_def (j : ℕ) :
    gs A b j = InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j := rfl

private theorem vec_eq_smul_gs (j : ℕ) : vec A b j = (‖gs A b j‖ : 𝕜)⁻¹ • gs A b j := rfl

private theorem gs_orthogonal {i j : ℕ} (h : i ≠ j) : inner 𝕜 (gs A b i) (gs A b j) = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal 𝕜 _ h

/-- For real $x$ and $y$, $x^{-1} (y^{-1} x^2) = y^{-1} x$ in $\mathbb{K}$, also when $x = 0$. -/
private theorem inv_mul_inv_mul_sq (x y : ℝ) :
    ((x : 𝕜))⁻¹ * ((y : 𝕜)⁻¹ * (x : 𝕜) ^ 2) = ((y⁻¹ * x : ℝ) : 𝕜) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : ((x : ℝ) : 𝕜) ≠ 0 := by simpa using hx
    push_cast
    field_simp

/-- For real $x$ and $y \neq 0$, $(y^{-1} x)^{-1} y^{-1} = x^{-1}$ in $\mathbb{K}$, also when
$x = 0$. -/
private theorem inv_mul_inv_cancel (x y : ℝ) (hy : y ≠ 0) :
    (((y⁻¹ * x : ℝ)) : 𝕜)⁻¹ * ((y : ℝ) : 𝕜)⁻¹ = ((x : ℝ) : 𝕜)⁻¹ := by
  have hy' : ((y : ℝ) : 𝕜) ≠ 0 := by simpa using hy
  push_cast
  rw [mul_inv, inv_inv, mul_right_comm, mul_inv_cancel₀ hy', one_mul]

private theorem subspace_eq_span_gs_image (m : ℕ) :
    subspace A b m = Submodule.span 𝕜 (gs A b '' Set.Iio m) := by
  rw [subspace_eq_span_image_Iio]
  exact (InnerProductSpace.span_gramSchmidt_Iio 𝕜 (fun i : ℕ => (A ^ i) b) m).symm

private theorem gs_mem_subspace {i j : ℕ} (h : i < j) : gs A b i ∈ subspace A b j := by
  rw [subspace_eq_span_gs_image]
  exact Submodule.subset_span ⟨i, h, rfl⟩

private theorem gs_mem_orthogonal (j : ℕ) : gs A b j ∈ (subspace A b j)ᗮ := by
  rw [subspace_eq_span_gs_image]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact gs_orthogonal A b hi.ne

/-- The vector $u_j$ is the component of $A^j b$ orthogonal to $\mathcal{K}_j$:
$u_j = A^j b - P_{\mathcal{K}_j} A^j b$. -/
private theorem gs_eq_sub_starProjection (j : ℕ) :
    gs A b j = (A ^ j) b - (subspace A b j).starProjection ((A ^ j) b) := by
  have hd := InnerProductSpace.gramSchmidt_def' 𝕜 (fun i : ℕ => (A ^ i) b) j
  have hsum : (A ^ j) b - gs A b j =
      ∑ i ∈ Finset.Iio j,
        (𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) i).starProjection
          ((A ^ j) b) := sub_eq_of_eq_add' hd
  have hP : (subspace A b j).starProjection ((A ^ j) b) = (A ^ j) b - gs A b j := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hsum]
      refine Submodule.sum_mem _ fun i hi => ?_
      refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_ (Submodule.starProjection_apply_mem _ _)
      exact gs_mem_subspace A b (Finset.mem_Iio.1 hi)
    · intro y hy
      rw [sub_sub_cancel]
      exact Submodule.inner_left_of_mem_orthogonal hy (gs_mem_orthogonal A b j)
  rw [hP, sub_sub_cancel]

private theorem gs_eq_zero_iff (j : ℕ) : gs A b j = 0 ↔ (A ^ j) b ∈ subspace A b j := by
  rw [gs_eq_sub_starProjection, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-! ### Basic properties of the Arnoldi vectors -/

-- `hb` is not needed: for `b = 0` both sides are `0`.
set_option linter.unusedVariables false in
/-- Let $b \neq 0$. The first Arnoldi vector is the normalized starting vector,
$$v_0 = \frac{b}{\|b\|}.$$

The hypothesis $b \neq 0$ is not used: for $b = 0$ both sides are $0$. -/
theorem vec_zero (hb : b ≠ 0) : vec A b 0 = (‖b‖⁻¹ : 𝕜) • b := by
  have h0 : gs A b 0 = b := by
    rw [gs_def, show (0 : ℕ) = ⊥ from rfl, InnerProductSpace.gramSchmidt_bot]
    simp
  rw [vec_eq_smul_gs, h0]

/-- Breakdown at step $j$ means that the Krylov sequence closes up there: $v_j = 0$ if and only if
$A^j b \in \mathcal{K}_j$. This form of `Arnoldi.vec_eq_zero_iff` needs no
finite-dimensionality. -/
theorem vec_eq_zero_iff_pow_apply_mem (j : ℕ) :
    vec A b j = 0 ↔ (A ^ j) b ∈ subspace A b j := by
  rw [← gs_eq_zero_iff, vec_eq_smul_gs, smul_eq_zero]
  refine ⟨fun h => h.elim (fun hc => ?_) id, fun h => Or.inr h⟩
  rw [inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero] at hc
  exact hc

/-- An Arnoldi vector $v_j \neq 0$ is a unit vector: $\|v_j\| = 1$. -/
theorem norm_vec_eq_one_of_ne_zero {j : ℕ} (h : vec A b j ≠ 0) : ‖vec A b j‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length' h

/-- For every $j$, the Arnoldi vector $v_j$ lies in $\mathcal{K}_{j+1}$.

The orthogonalization of $A^j b$ combines only $b, Ab, \dots, A^j b$. -/
theorem vec_mem_subspace (j : ℕ) : vec A b j ∈ subspace A b (j + 1) := by
  rw [vec_eq_smul_gs]
  exact Submodule.smul_mem _ _ (gs_mem_subspace A b j.lt_succ_self)

/-- If $i < m$, then the Arnoldi vector $v_i$ lies in $\mathcal{K}_m$. -/
theorem vec_mem_subspace_of_lt {i m : ℕ} (h : i < m) : vec A b i ∈ subspace A b m :=
  subspace_mono A b h (vec_mem_subspace A b i)

/-- For every $j$, the Arnoldi vector $v_j$ is orthogonal to $\mathcal{K}_j$, that is,
$v_j \in \mathcal{K}_j^\perp$.

Since $\mathcal{K}_j$ is spanned by $v_0, \dots, v_{j-1}$, this says that $v_j$ is orthogonal to
all earlier Arnoldi vectors at once. -/
theorem vec_mem_orthogonal (j : ℕ) : vec A b j ∈ (subspace A b j)ᗮ := by
  rw [vec_eq_smul_gs]
  exact Submodule.smul_mem _ _ (gs_mem_orthogonal A b j)

/-- Distinct Arnoldi vectors are orthogonal: for all $i \neq j$,
$$\langle v_i, v_j \rangle = 0.$$

No hypothesis on the grade is needed: after breakdown the vectors are $0$, and the inner product
vanishes for that reason. -/
theorem inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A b i) (vec A b j) = 0 := by
  rw [vec_eq_smul_gs, vec_eq_smul_gs, inner_smul_left, inner_smul_right, gs_orthogonal A b h]
  simp

/-- For every $m$, the first $m$ Arnoldi vectors span the $m$-th Krylov subspace:
$$\operatorname{span}\{v_0, \dots, v_{m-1}\} = \mathcal{K}_m.$$
This is part of Proposition 6.4 of [saad2003iterative].

No hypothesis on the grade is needed: after breakdown $\mathcal{K}_m$ stops growing and the
added vectors are $0$. -/
theorem span_vec (m : ℕ) : Submodule.span 𝕜 (vec A b '' Set.Iio m) = subspace A b m := by
  rw [subspace_eq_span_gs_image]
  exact InnerProductSpace.span_gramSchmidtNormed (fun i : ℕ => (A ^ i) b) (Set.Iio m)

section FiniteDimensional

variable [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Suppose that the full Krylov space $\operatorname{span}\{A^i b : i \ge 0\}$ is
finite-dimensional, and let $d$ be its dimension, the grade of $b$ with respect to $A$. Then for
every $j$,
$$v_j = 0 \iff d \le j.$$
This is Proposition 6.6 of [saad2003iterative]: the process breaks down exactly at the grade.

The grade is `Krylov.grade A b`. -/
theorem vec_eq_zero_iff (j : ℕ) : vec A b j = 0 ↔ grade A b ≤ j := by
  rw [vec_eq_zero_iff_pow_apply_mem, grade_le_iff]

/-- Suppose that the full Krylov space of $A$ and $b$ is finite-dimensional. If $j$ is less than the
grade of $b$, then $\|v_j\| = 1$.

From the grade on, the vectors are $0$ by `Arnoldi.vec_eq_zero_iff`. -/
theorem norm_vec_eq_one_of_lt_grade {j : ℕ} (h : j < grade A b) : ‖vec A b j‖ = 1 :=
  norm_vec_eq_one_of_ne_zero A b (fun hz => absurd ((vec_eq_zero_iff A b j).1 hz) (not_le.2 h))

/-- Suppose that the full Krylov space of $A$ and $b$ is finite-dimensional, and let $d$ be the
grade of $b$. Then $v_0, \dots, v_{d-1}$ is an orthonormal family. This is part of Proposition
6.4 of [saad2003iterative].

These are exactly the Arnoldi vectors that are not $0$. The family is indexed by
`Fin (Krylov.grade A b)`. -/
theorem orthonormal : Orthonormal 𝕜 (fun i : Fin (grade A b) => vec A b i) :=
  ⟨fun i => norm_vec_eq_one_of_lt_grade A b i.2,
    fun _ _ hij => inner_vec_eq_zero A b fun h => hij (Fin.val_injective h)⟩

end FiniteDimensional

/-! ### Expansion in the Arnoldi vectors -/

private theorem sub_sum_inner_smul_vec_mem_orthogonal (x : E) (m : ℕ) :
    x - ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i ∈ (subspace A b m)ᗮ := by
  rw [← span_vec]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [inner_sub_right, inner_sum, Finset.sum_eq_single k]
  · rcases eq_or_ne (vec A b k) 0 with h0 | h0
    · simp [h0]
    · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_vec_eq_one_of_ne_zero A b h0]
      simp
  · intro i _ hik
    rw [inner_smul_right, inner_vec_eq_zero A b (Ne.symm hik), mul_zero]
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

/-- Every $x \in \mathcal{K}_m$ is its own orthonormal expansion in the first $m$ Arnoldi vectors:
$$x = \sum_{i=0}^{m-1} \langle v_i, x \rangle v_i.$$

No hypothesis on the grade is needed: the vectors that are $0$ after breakdown contribute
nothing. -/
theorem eq_sum_inner_smul_vec {x : E} {m : ℕ} (hx : x ∈ subspace A b m) :
    x = ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i := by
  have hy : x - ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i ∈ subspace A b m :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b (Finset.mem_range.1 hi)))
  have h0 := Submodule.inner_right_of_mem_orthogonal hy
    (sub_sum_inner_smul_vec_mem_orthogonal A b x m)
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

/-- If $x \in \mathcal{K}_{m+1}$ is orthogonal to $\mathcal{K}_m$, then
$x = \langle v_m, x \rangle v_m$.

In the expansion of `Arnoldi.eq_sum_inner_smul_vec` only the last coefficient survives. This is
the step that turns the new direction of a Krylov subspace into a scalar. -/
theorem eq_inner_smul_vec {x : E} {m : ℕ} (hx : x ∈ subspace A b (m + 1))
    (hxo : x ∈ (subspace A b m)ᗮ) :
    x = inner 𝕜 (vec A b m) x • vec A b m := by
  have hzero : ∀ i ∈ Finset.range m,
      inner 𝕜 (vec A b i) x • vec A b i = (0 : E) := fun i hi => by
    rw [(Submodule.mem_orthogonal _ _).1 hxo _
      (vec_mem_subspace_of_lt A b (Finset.mem_range.1 hi)), zero_smul]
  conv_lhs => rw [eq_sum_inner_smul_vec A b hx]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero hzero, zero_add]

section OrthonormalBasis

/-- The Arnoldi vectors $v_0, \dots, v_{m-1}$ as elements of $\mathcal{K}_m$. -/
private noncomputable def vecIn {m : ℕ} (i : Fin m) : subspace A b m :=
  ⟨vec A b i, vec_mem_subspace_of_lt A b i.2⟩

private theorem orthonormal_vecIn [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) : Orthonormal 𝕜 (vecIn A b (m := m)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact norm_vec_eq_one_of_lt_grade A b (i.2.trans_le hm)
  · exact inner_vec_eq_zero A b fun h => hij (Fin.val_injective h)

private theorem span_vecIn {m : ℕ} :
    ⊤ ≤ Submodule.span 𝕜 (Set.range (vecIn A b (m := m))) := by
  intro x _
  have hxe : x = ∑ i : Fin m, inner 𝕜 (vec A b i) (x : E) • vecIn A b i := by
    apply Subtype.ext
    push_cast [vecIn]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => inner 𝕜 (vec A b i) (x : E) • vec A b i) m]
    exact eq_sum_inner_smul_vec A b x.2
  rw [hxe]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Suppose that the full Krylov space of $A$ and $b$ is finite-dimensional, and let $m$ be at most
the grade of $b$. The Arnoldi vectors $v_0, \dots, v_{m-1}$ form an **orthonormal basis** of
$\mathcal{K}_m$.

The basis is indexed by `Fin m`. Its vectors are elements of the subspace
`Krylov.subspace A b m`; `Arnoldi.coe_orthonormalBasis_apply` identifies them with
`Arnoldi.vec`. -/
noncomputable def orthonormalBasis [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) : OrthonormalBasis (Fin m) 𝕜 (subspace A b m) :=
  OrthonormalBasis.mk (orthonormal_vecIn A b hm) (span_vecIn A b)

/-- The $i$-th vector of `Arnoldi.orthonormalBasis`, as an element of $E$, is the Arnoldi vector
$v_i$.

Any statement about the basis can therefore be read back in terms of `Arnoldi.vec`. -/
@[simp]
theorem coe_orthonormalBasis_apply [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) (i : Fin m) : (orthonormalBasis A b hm i : E) = vec A b i :=
  congrArg Subtype.val
    (congrFun (OrthonormalBasis.coe_mk (orthonormal_vecIn A b hm) (span_vecIn A b)) i)

end OrthonormalBasis

/-! ### The Hessenberg structure -/

/-- The Arnoldi coefficients vanish below the first subdiagonal: if $i > j + 1$, then $h_{ij} = 0$.
-/
theorem coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A b i j = 0 := by
  refine Submodule.inner_left_of_mem_orthogonal (K := subspace A b (j + 2))
    (map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩) ?_
  exact Submodule.orthogonal_le (subspace_mono A b (by omega)) (vec_mem_orthogonal A b i)

/-- The infinite array $(h_{ij})_{i, j \ge 0}$ of Arnoldi coefficients is upper Hessenberg:
$h_{ij} = 0$ whenever some index $k$ satisfies $j < k < i$.

This is `Matrix.IsUpperHessenberg` for a matrix indexed by $\mathbb{N}$, and it is the matrix
form of `Arnoldi.coeff_eq_zero_of_lt`. -/
theorem isUpperHessenberg_coeff : Matrix.IsUpperHessenberg (n := ℕ) (coeff A b) :=
  Matrix.isUpperHessenberg_iff_nat.2 fun _ _ hij => coeff_eq_zero_of_lt A b hij

/-- The **Arnoldi relation**: for every $j$,
$$A v_j = \sum_{i=0}^{j+1} h_{ij} v_i.$$
This is equation (6.9) of [saad2003iterative].

No hypothesis on the grade is needed: after breakdown the vectors are $0$. -/
theorem apply_vec (j : ℕ) :
    A (vec A b j) = ∑ i ∈ Finset.range (j + 2), coeff A b i j • vec A b i := by
  have hx : A (vec A b j) ∈ subspace A b (j + 1 + 1) :=
    map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩
  simpa [coeff] using eq_sum_inner_smul_vec A b hx

/-- The Arnoldi relation with a longer sum: if $j + 2 \le n$, then
$$A v_j = \sum_{i=0}^{n-1} h_{ij} v_i.$$

The extra terms have coefficients $h_{ij} = 0$ with $i > j + 1$, by the Hessenberg structure. -/
theorem apply_vec_of_le {j n : ℕ} (h : j + 2 ≤ n) :
    A (vec A b j) = ∑ i ∈ Finset.range n, coeff A b i j • vec A b i := by
  rw [apply_vec]
  refine Finset.sum_subset (fun i hi => Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le h))
    fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  rw [coeff_eq_zero_of_lt A b (by omega), zero_smul]

/-- The **unnormalized next Arnoldi vector**
$$w_j = A v_j - \sum_{i=0}^{j} h_{ij} v_i,$$
computed in line 4 of Algorithm 6.1 of [saad2003iterative]. -/
noncomputable def w (j : ℕ) : E :=
  A (vec A b j) - ∑ i ∈ Finset.range (j + 1), coeff A b i j • vec A b i

/-- The vector $w_j$ is the component of $A v_j$ orthogonal to $\mathcal{K}_{j+1}$:
$$w_j = A v_j - P_{\mathcal{K}_{j+1}} A v_j,$$
where $P_{\mathcal{K}_{j+1}}$ is the orthogonal projection onto $\mathcal{K}_{j+1}$.

So subtracting the coefficients as in Algorithm 6.1 of [saad2003iterative] is the same as
removing the orthogonal projection onto the space built so far. The projection is
`Submodule.starProjection`. -/
theorem w_eq_sub_starProjection (j : ℕ) :
    w A b j = A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j)) := by
  rw [w]
  congr 1
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b (Finset.mem_range.1 hi))
  · intro y hy
    exact Submodule.inner_left_of_mem_orthogonal hy
      (sub_sum_inner_smul_vec_mem_orthogonal A b (A (vec A b j)) (j + 1))

/-- Let $B : E \to E$ be an adjoint of $A$, that is, $\langle A x, y \rangle = \langle x, B y
\rangle$ for all $x, y \in E$, and let $s \in \mathbb{N}$ be such that
$B v \in \mathcal{K}_s(A, v)$ for every $v \in E$. Then for all $i$ and $j$ with $i + s \le j$,
$$h_{ij} = 0.$$
This is the band structure (6.108) of [saad2003iterative], established in the proof of
Proposition 6.22. It generalizes the tridiagonal structure of the Lanczos process.

Proposition 6.22 itself uses this band structure to show that DIOM($s$) is equivalent to FOM.
The adjoint condition is `LinearMap.IsAdjointPair` for the flipped inner product, which states
$\langle B y, x \rangle = \langle y, A x \rangle$. -/
theorem coeff_eq_zero_of_adjoint_mem {B : E →ₗ[𝕜] E}
    (hB : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A B)
    {s : ℕ} (hs : ∀ v, B v ∈ subspace A v s) {i j : ℕ} (h : i + s ≤ j) : coeff A b i j = 0 := by
  have hle : subspace A (vec A b i) s ≤ subspace A b j := by
    rw [subspace, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < s := k.2
    exact subspace_mono A b (by omega)
      (pow_apply_mem_subspace_of_mem A b (vec_mem_subspace A b i) k)
  have hconj : coeff A b i j = starRingEnd 𝕜 (inner 𝕜 (vec A b j) (B (vec A b i))) := by
    rw [coeff, ← LinearMap.inner_apply_eq_inner_apply_of_adjoint hB, inner_conj_symm]
  rw [hconj, Submodule.inner_left_of_mem_orthogonal (hle (hs (vec A b i)))
    (vec_mem_orthogonal A b j), map_zero]

/-! ### The classical recurrence -/

private theorem w_eq_smul_gs (j : ℕ) : w A b j = (‖gs A b j‖ : 𝕜)⁻¹ • gs A b (j + 1) := by
  have hz : A ((subspace A b j).starProjection ((A ^ j) b)) ∈ subspace A b (j + 1) :=
    map_subspace_le A b j ⟨_, Submodule.starProjection_apply_mem _ _, rfl⟩
  have hpow : (A ^ (j + 1)) b = A ((A ^ j) b) := by rw [pow_succ']; rfl
  have hkey : A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b ∈ subspace A b (j + 1) := by
    have hrw : A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b =
        -((‖gs A b j‖ : 𝕜)⁻¹ • A ((subspace A b j).starProjection ((A ^ j) b))) := by
      rw [vec_eq_smul_gs, gs_eq_sub_starProjection, map_smul, map_sub, hpow]
      module
    rw [hrw]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hz)
  have hcongr : A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j)) =
      (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b -
        (subspace A b (j + 1)).starProjection ((‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b) := by
    have hself : (subspace A b (j + 1)).starProjection
        (A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b) =
        A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b :=
      Submodule.starProjection_eq_self_iff.2 hkey
    rw [map_sub] at hself
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hself.symm
  rw [w_eq_sub_starProjection, hcongr, map_smul, ← smul_sub, ← gs_eq_sub_starProjection]

private theorem norm_w (j : ℕ) : ‖w A b j‖ = ‖gs A b j‖⁻¹ * ‖gs A b (j + 1)‖ := by
  rw [w_eq_smul_gs, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

private theorem inner_vec_succ_w (j : ℕ) :
    inner 𝕜 (vec A b (j + 1)) (w A b j) = (‖w A b j‖ : 𝕜) := by
  rw [norm_w, w_eq_smul_gs, vec_eq_smul_gs, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal]
  exact inv_mul_inv_mul_sq _ _

/-- The subdiagonal Arnoldi coefficient is the norm of the unnormalized next vector: for every $j$,
$$h_{j+1,j} = \|w_j\|.$$
In particular it is real and nonnegative. -/
theorem coeff_succ_self (j : ℕ) : coeff A b (j + 1) j = (‖w A b j‖ : 𝕜) := by
  have hsplit : A (vec A b j) =
      w A b j + (subspace A b (j + 1)).starProjection (A (vec A b j)) := by
    rw [w_eq_sub_starProjection]; abel
  rw [coeff, hsplit, inner_add_right, inner_vec_succ_w,
    Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
      (vec_mem_orthogonal A b (j + 1)), add_zero]

/-- The classical Arnoldi recurrence: for every $j$,
$$v_{j+1} = \frac{w_j}{\|w_j\|},$$
as in line 7 of Algorithm 6.1 of [saad2003iterative]. If $w_j = 0$, then $v_{j+1} = 0$.

The case $w_j = 0$ follows the convention $0^{-1} = 0$ of Lean. -/
theorem vec_succ_eq (j : ℕ) : vec A b (j + 1) = (‖w A b j‖⁻¹ : 𝕜) • w A b j := by
  rcases eq_or_ne (gs A b j) 0 with h0 | h0
  · have h1 : gs A b (j + 1) = 0 := by
      rw [gs_eq_zero_iff]
      exact pow_apply_mem_subspace_of_le A b ((gs_eq_zero_iff A b j).1 h0) j.le_succ
    rw [vec_eq_smul_gs, h1, w_eq_smul_gs, h1, smul_zero, smul_zero, smul_zero]
  · have ha : ((‖gs A b j‖ : ℝ) : 𝕜) ≠ 0 := by simpa using norm_ne_zero_iff.2 h0
    rw [vec_eq_smul_gs, norm_w, w_eq_smul_gs, smul_smul]
    exact congrArg (· • gs A b (j + 1))
      (inv_mul_inv_cancel (𝕜 := 𝕜) _ _ (norm_ne_zero_iff.2 h0)).symm

/-- For every $j$, $w_j = \|w_j\| \, v_{j+1}$. This is line 7 of Algorithm 6.1 of
[saad2003iterative] read backwards; it also holds on breakdown, where both sides are $0$. -/
theorem w_eq_norm_smul_vec (j : ℕ) : w A b j = (‖w A b j‖ : 𝕜) • vec A b (j + 1) := by
  rw [vec_succ_eq, smul_smul]
  rcases eq_or_ne (w A b j) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h)), one_smul]

private theorem w_eq_zero_iff (j : ℕ) : w A b j = 0 ↔ vec A b (j + 1) = 0 := by
  rw [vec_succ_eq]
  refine ⟨fun h => by rw [h, smul_zero], fun h => ?_⟩
  by_contra h0
  exact smul_ne_zero (inv_ne_zero (by simpa using norm_ne_zero_iff.2 h0)) h0 h

/-- Breakdown read off the Hessenberg matrix. Suppose that the full Krylov space of $A$ and $b$ is
finite-dimensional, and let $d$ be the grade of $b$. Then for every $j$,
$$h_{j+1,j} = 0 \iff d \le j + 1.$$
This is Proposition 6.6 of [saad2003iterative] in terms of the subdiagonal coefficient. -/
theorem coeff_succ_self_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    coeff A b (j + 1) j = 0 ↔ grade A b ≤ j + 1 := by
  rw [coeff_succ_self, RCLike.ofReal_eq_zero, norm_eq_zero, w_eq_zero_iff, vec_eq_zero_iff]

/-! ### The Hessenberg matrices -/

/-- The $(m+1) \times m$ **Hessenberg matrix** $\bar H_m$ of the Arnoldi process, with entries
$(\bar H_m)_{ij} = h_{ij}$ for $0 \le i \le m$ and $0 \le j \le m - 1$. This is the matrix
$\bar H_m$ of Proposition 6.5 of [saad2003iterative].

Rows and columns are indexed by `Fin (m + 1)` and `Fin m`, from $0$. -/
noncomputable def hessenberg (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

/-- The $m \times m$ **Hessenberg matrix** $H_m$ of the Arnoldi process, with entries
$(H_m)_{ij} = h_{ij}$ for $0 \le i, j \le m - 1$. It is $\bar H_m$ with its last row deleted, as
in Proposition 6.5 of [saad2003iterative]. -/
noncomputable def hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

/-- For every $m$, the matrix $\bar H_m$ is upper Hessenberg: $(\bar H_m)_{ij} = 0$ whenever
$i > j + 1$.

This is `Matrix.IsUpperHessenbergRect`, the matrix form of `Arnoldi.coeff_eq_zero_of_lt`. -/
theorem hessenberg_isUpperHessenbergRect (m : ℕ) :
    (hessenberg A b m).IsUpperHessenbergRect := fun _ _ h => coeff_eq_zero_of_lt A b h

/-- For every $m$, the matrix $H_m$ is upper Hessenberg: $(H_m)_{ij} = 0$ whenever $i > j + 1$. This
is the square form of `Arnoldi.coeff_eq_zero_of_lt`. -/
theorem hessenbergSq_isUpperHessenberg (m : ℕ) : (hessenbergSq A b m).IsUpperHessenberg := by
  rintro i j ⟨k, hjk, hki⟩
  rw [Fin.lt_def] at hjk hki
  exact coeff_eq_zero_of_lt A b (by omega)

/-- The matrix form $A V_m = V_{m+1} \bar H_m$ of the Arnoldi relation, equation (6.7) of
[saad2003iterative], applied to a coordinate vector: for every $y \in \mathbb{K}^m$,
$$A \Big( \sum_{j=0}^{m-1} y_j v_j \Big) = \sum_{i=0}^{m} (\bar H_m y)_i \, v_i.$$

Here $V_m$ is the map $y \mapsto \sum_j y_j v_j$, and $y$ is a function `Fin m → 𝕜`. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • vec A b j) = ∑ i : Fin (m + 1), (hessenberg A b m).mulVec y i • vec A b i := by
  rw [map_sum]
  have hAv : ∀ j : Fin m, y j • A (vec A b j) =
      ∑ i : Fin (m + 1), (y j * coeff A b i j) • vec A b i := by
    intro j
    rw [apply_vec_of_le A b (n := m + 1) (by omega),
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ => coeff A b i j • vec A b i) (m + 1),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  simp only [map_smul, hAv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmv : (hessenberg A b m).mulVec y i = ∑ j : Fin m, y j * coeff A b i j := by
    simp [Matrix.mulVec, dotProduct, hessenberg, mul_comm]
  rw [hmv, Finset.sum_smul]

/-- Suppose that the full Krylov space of $A$ and $b$ is finite-dimensional, and let $m$ be at most
the grade of $b$. Then $H_m$ is the matrix, in the orthonormal basis $v_0, \dots, v_{m-1}$ of
$\mathcal{K}_m$, of the compression $P_{\mathcal{K}_m} A|_{\mathcal{K}_m}$ of $A$ to
$\mathcal{K}_m$. This is the identity $H_m = V_m^H A V_m$ of equation (6.8) and Proposition 6.5
of [saad2003iterative].

The basis is `Arnoldi.orthonormalBasis`, and the compression is
`compression A (Krylov.subspace A b m)`. -/
theorem hessenbergSq_eq_toMatrix_compression [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) :
    hessenbergSq A b m =
      LinearMap.toMatrix (orthonormalBasis A b hm).toBasis (orthonormalBasis A b hm).toBasis
        (compression A (subspace A b m)) := by
  rw [compression.toMatrix_orthonormalBasis]
  ext i j
  simp [hessenbergSq, coeff]

/-- The part of $A v_m$ outside $\mathcal{K}_{m+1}$ is a multiple of the next Arnoldi vector: for
every $m$,
$$A v_m - P_{\mathcal{K}_{m+1}} A v_m = h_{m+1,m} v_{m+1},$$
where $P_{\mathcal{K}_{m+1}}$ is the orthogonal projection onto $\mathcal{K}_{m+1}$.

Together with $A v_j \in \mathcal{K}_{m+1}$ for $j < m$, this gives the basis-free form $(I -
P_{\mathcal{K}_{m+1}}) A P_{\mathcal{K}_{m+1}} = h_{m+1,m} v_{m+1} v_m^H$ of the Arnoldi
relation, which measures the invariance defect of the Krylov subspace ([saad2011numerical],
Proposition 6.6 and problem P-6.1). The declaration states only the identity on $v_m$. -/
theorem starProjection_apply_vec (m : ℕ) :
    A (vec A b m) - (subspace A b (m + 1)).starProjection (A (vec A b m)) =
      coeff A b (m + 1) m • vec A b (m + 1) := by
  rw [← w_eq_sub_starProjection, coeff_succ_self, vec_succ_eq, smul_smul]
  rcases eq_or_ne (w A b m) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-! ### Arnoldi vectors under an intertwining map -/

/-- For every $j$ there is a real number $r \ge 0$ such that
$$v_j - r A^j b \in \mathcal{K}_j.$$
That is, the leading coefficient of an Arnoldi vector in the Krylov sequence is a nonnegative
real. -/
theorem exists_vec_sub_smul_pow_apply_mem (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ vec A b j - (r : 𝕜) • (A ^ j) b ∈ subspace A b j := by
  set g := InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j
  refine ⟨‖g‖⁻¹, inv_nonneg.2 (norm_nonneg _), ?_⟩
  have hmem : (A ^ j) b - g ∈ subspace A b j := by
    rw [subspace_eq_span_image_Iio]
    exact InnerProductSpace.sub_gramSchmidt_mem_span (fun i : ℕ => (A ^ i) b) j
  have hrw : vec A b j - ((‖g‖⁻¹ : ℝ) : 𝕜) • (A ^ j) b =
      -(((‖g‖⁻¹ : ℝ) : 𝕜) • ((A ^ j) b - g)) := by
    change (‖g‖ : 𝕜)⁻¹ • g - _ = _
    push_cast
    module
  rw [hrw]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)

/-- For every $j$, $\langle v_j, A^j b \rangle = \|u_j\|$, where $u_j$ is the $j$-th unnormalized
Gram–Schmidt vector (`InnerProductSpace.gramSchmidt`) of the Krylov sequence
$b, Ab, A^2 b, \dots$. In particular this inner product is real and nonnegative. -/
theorem inner_vec_pow_apply_eq_norm_gramSchmidt (j : ℕ) :
    inner 𝕜 (vec A b j) ((A ^ j) b) =
      (‖InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j‖ : 𝕜) :=
  InnerProductSpace.inner_gramSchmidtNormed_self (fun i : ℕ => (A ^ i) b) j

/-- If $\langle v_j, A^j b \rangle = 0$, then $v_j = 0$: an Arnoldi vector orthogonal to its own
Krylov vector means that the process has broken down. -/
theorem vec_eq_zero_of_inner_pow_apply_eq_zero {j : ℕ}
    (h : inner 𝕜 (vec A b j) ((A ^ j) b) = 0) : vec A b j = 0 := by
  rw [inner_vec_pow_apply_eq_norm_gramSchmidt, RCLike.ofReal_eq_zero, norm_eq_zero] at h
  change (‖InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j‖ : 𝕜)⁻¹ •
    InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j = 0
  rw [h, smul_zero]

section Semiconj

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {B : E →ₗ[𝕜] E}
  {C : F →ₗ[𝕜] F} {N : E →ₗ[𝕜] F}

/-- Let $B : E \to E$, $C : F \to F$ and $N : E \to F$ be linear with $N B = C N$, and let $b \in E$
and $c \in F$ satisfy $N b = C^s c$. Then for every $j$, $N$ maps the $j$-th Arnoldi vector of
$(B, b)$ into $\mathcal{K}_{j+1+s}(C, c)$. -/
theorem apply_vec_mem_subspace_of_semiconj (h : Function.Semiconj N B C) {b : E} {c : F} {s : ℕ}
    (hs : N b = (C ^ s) c) (j : ℕ) : N (vec B b j) ∈ subspace C c (j + 1 + s) := by
  have hmem := apply_mem_subspace_of_semiconj h (vec_mem_subspace B b j)
  rw [hs] at hmem
  exact subspace_pow_apply_le C c s (j + 1) hmem

/-- Let $B : E \to E$, $C : F \to F$ and $N : E \to F$ be linear with $N B = C N$, and let $b \in E$
and $c \in F$ satisfy $N b = C^s c$. Write $v_j(B, b)$ and $v_j(C, c)$ for the Arnoldi vectors
of the two processes. Then for every $j$ there is a real number $r \ge 0$ with
$$\langle v_{j+s}(C, c), N v_j(B, b) \rangle = r,$$
and $r = 0$ only if $v_{j+s}(C, c) = 0$, that is, only on breakdown of the second process.

This positivity of the leading coefficients makes the two families of vectors of the Golub–Kahan
process line up. The hypothesis $N B = C N$ is `Function.Semiconj N B C`. -/
theorem inner_vec_apply_vec_of_semiconj (h : Function.Semiconj N B C) {b : E} {c : F} {s : ℕ}
    (hs : N b = (C ^ s) c) (j : ℕ) :
    ∃ r : ℝ, 0 ≤ r ∧ inner 𝕜 (vec C c (j + s)) (N (vec B b j)) = (r : 𝕜) ∧
      (r = 0 → vec C c (j + s) = 0) := by
  obtain ⟨ρ, hρ, hp⟩ := exists_vec_sub_smul_pow_apply_mem B b j
  have hpow : N ((B ^ j) b) = (C ^ (j + s)) c := by
    rw [pow_apply_of_semiconj h, hs, ← Module.End.mul_apply, ← pow_add]
  have hNp : N (vec B b j - (ρ : 𝕜) • (B ^ j) b) ∈ subspace C c (j + s) := by
    have hmem := apply_mem_subspace_of_semiconj h hp
    rw [hs] at hmem
    exact subspace_pow_apply_le C c s j hmem
  have hsplit : N (vec B b j) =
      (ρ : 𝕜) • (C ^ (j + s)) c + N (vec B b j - (ρ : 𝕜) • (B ^ j) b) := by
    rw [map_sub, map_smul, hpow]
    abel
  refine ⟨ρ * ‖InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (C ^ i) c) (j + s)‖,
    mul_nonneg hρ (norm_nonneg _), ?_, fun hr => ?_⟩
  · rw [hsplit, inner_add_right, inner_smul_right, inner_vec_pow_apply_eq_norm_gramSchmidt,
      Submodule.inner_left_of_mem_orthogonal hNp (vec_mem_orthogonal C c (j + s)), add_zero]
    push_cast
    ring
  · rcases mul_eq_zero.1 hr with h0 | h0
    · rw [h0, RCLike.ofReal_zero, zero_smul, sub_zero] at hp
      have hv : vec B b j = 0 :=
        inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hp (vec_mem_orthogonal B b j))
      rw [vec_eq_zero_iff_pow_apply_mem] at hv ⊢
      have hmem := apply_mem_subspace_of_semiconj h hv
      rw [hpow, hs] at hmem
      exact subspace_pow_apply_le C c s j hmem
    · refine vec_eq_zero_of_inner_pow_apply_eq_zero C c ?_
      rw [inner_vec_pow_apply_eq_norm_gramSchmidt, h0, RCLike.ofReal_zero]

end Semiconj

/-! ### Naturality under linear isometries -/

section LinearIsometryEquiv

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (e : E ≃ₗᵢ[𝕜] E')

/-- For a linear isometry equivalence $e$, $(e A e^{-1})^i (e x) = e (A^i x)$ for all $i$ and $x$.
-/
private theorem pow_conj_apply (i : ℕ) (x : E) :
    ((e.toLinearEquiv.conj A) ^ i) (e x) = e ((A ^ i) x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearEquiv.conj_apply_apply, pow_succ',
      Module.End.mul_apply]
    simp

/-- **Naturality of the Arnoldi vectors under isometries.** Let $e : E \to E'$ be a linear isometry
equivalence. Then for every $j$ the Arnoldi vectors of $e A e^{-1}$ from $e b$ are the images of
those of $A$ from $b$:
$$v_j(e A e^{-1}, e b) = e \, v_j(A, b).$$

The operator $e A e^{-1}$ is `e.toLinearEquiv.conj A`. The proof uses that Gram–Schmidt commutes
with isometries (`InnerProductSpace.gramSchmidtNormed_comp_linearIsometry`) and that
$(e A e^{-1})^i (e b) = e (A^i b)$. -/
theorem vec_conj_linearIsometryEquiv (j : ℕ) :
    vec (e.toLinearEquiv.conj A) (e b) j = e (vec A b j) := by
  have hseq : (fun i : ℕ => ((e.toLinearEquiv.conj A) ^ i) (e b)) =
      e.toLinearIsometry ∘ fun i : ℕ => (A ^ i) b :=
    funext fun i => pow_conj_apply A e i b
  rw [vec, hseq, InnerProductSpace.gramSchmidtNormed_comp_linearIsometry]
  rfl

/-- **Naturality of the Arnoldi coefficients under isometries.** Let $e : E \to E'$ be a linear
isometry equivalence. Then $e A e^{-1}$ from $e b$ has the same Arnoldi coefficients as $A$ from
$b$: $h_{ij}(e A e^{-1}, e b) = h_{ij}(A, b)$ for all $i$ and $j$.

The operator $e A e^{-1}$ is `e.toLinearEquiv.conj A`. -/
theorem coeff_conj_linearIsometryEquiv :
    coeff (e.toLinearEquiv.conj A) (e b) = coeff A b := by
  ext i j
  rw [coeff, coeff, vec_conj_linearIsometryEquiv, vec_conj_linearIsometryEquiv,
    LinearEquiv.conj_apply_apply]
  simp

end LinearIsometryEquiv

/-! ### The modified Gram–Schmidt recurrence -/

/-- The **Arnoldi vectors computed with modified Gram–Schmidt** ([saad2003iterative], Algorithm 6.2;
[golub2013matrix], Algorithm 10.5.1). Set $q_0 = b / \|b\|$. For $j \ge 0$, start from
$w^{(0)} = A q_j$, remove the components along $q_0, \dots, q_j$ one at a time, each computed
against the current vector,
$$w^{(k+1)} = w^{(k)} - \langle q_k, w^{(k)} \rangle q_k, \qquad k = 0, \dots, j,$$
and set $q_{j+1} = w^{(j+1)} / \|w^{(j+1)}\|$. A vector of norm $0$ gives $0$.

The loop is `InnerProductSpace.modifiedGramSchmidtSweep`. In the definition the sweep reads the
earlier vectors through the clamped index $\min(i, j)$, which is needed for termination; the
clamp has no effect, because the sweep reads only $q_0, \dots, q_j$ (`Arnoldi.mgsVec_succ`). In
exact arithmetic the vectors are the Arnoldi vectors (`Arnoldi.mgsVec_eq_vec`). -/
noncomputable def mgsVec (A : E →ₗ[𝕜] E) (b : E) : ℕ → E
  | 0 => (‖b‖⁻¹ : 𝕜) • b
  | j + 1 =>
    let q : ℕ → E := fun i => mgsVec A b (min i j)
    let w := InnerProductSpace.modifiedGramSchmidtSweep 𝕜 q (A (q j)) (j + 1)
    (‖w‖⁻¹ : 𝕜) • w
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- Modified Gram–Schmidt Arnoldi starts from the normalized vector: $q_0 = b / \|b\|$. -/
@[simp]
theorem mgsVec_zero : mgsVec A b 0 = (‖b‖⁻¹ : 𝕜) • b := by
  rw [mgsVec]

/-- The step of `Arnoldi.mgsVec`: for every $j$, the vector $q_{j+1}$ is $w / \|w\|$, where $w$ is
the result of the modified Gram–Schmidt sweep of $A q_j$ against $q_0, \dots, q_j$.

The statement uses the sequence `Arnoldi.mgsVec A b` itself in the sweep, without the clamped
index of the definition. -/
theorem mgsVec_succ (j : ℕ) :
    mgsVec A b (j + 1) =
      (‖InnerProductSpace.modifiedGramSchmidtSweep 𝕜 (mgsVec A b) (A (mgsVec A b j)) (j + 1)‖⁻¹ :
        𝕜) •
        InnerProductSpace.modifiedGramSchmidtSweep 𝕜 (mgsVec A b) (A (mgsVec A b j)) (j + 1) := by
  rw [mgsVec]
  simp only [Nat.min_self]
  rw [InnerProductSpace.modifiedGramSchmidtSweep_congr 𝕜 _
    fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- **The modified Gram–Schmidt recurrence characterizes the Arnoldi vectors.** Let
$(q_j)_{j \ge 0}$ be a sequence in $E$ with $q_0 = b / \|b\|$ and, for every $j$,
$q_{j+1} = w / \|w\|$, where $w$ is the result of the modified Gram–Schmidt sweep of $A q_j$
against $q_0, \dots, q_j$. Then $q_j = v_j$ for every $j$.

The proof is by induction: once $q$ agrees with the orthonormal Arnoldi vectors up to $j$, the
sweep equals the classical $w_j$ (`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`), and
`Arnoldi.vec_succ_eq` applies. -/
theorem eq_vec_of_modifiedGramSchmidt {q : ℕ → E} (h0 : q 0 = (‖b‖⁻¹ : 𝕜) • b)
    (hsucc : ∀ j, q (j + 1) =
      (‖InnerProductSpace.modifiedGramSchmidtSweep 𝕜 q (A (q j)) (j + 1)‖⁻¹ : 𝕜) •
        InnerProductSpace.modifiedGramSchmidtSweep 𝕜 q (A (q j)) (j + 1)) :
    q = vec A b := by
  funext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | k
    · rw [h0]
      rcases eq_or_ne b 0 with rfl | hb
      · rw [smul_zero, eq_comm, vec_eq_zero_iff_pow_apply_mem, map_zero]
        exact Submodule.zero_mem _
      · exact (vec_zero A b hb).symm
    · have hq : ∀ i < k + 1, q i = vec A b i := ih
      rw [hsucc, InnerProductSpace.modifiedGramSchmidtSweep_congr 𝕜 _ hq, hq k k.lt_succ_self,
        InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum 𝕜
          (fun _ _ h => inner_vec_eq_zero A b h),
        vec_succ_eq]
      rfl

/-- **Modified Gram–Schmidt Arnoldi computes the Arnoldi vectors** in exact arithmetic: $q_j = v_j$
for every $j$ ([saad2003iterative], §6.3.2; [golub2013matrix], §10.5.1). -/
theorem mgsVec_eq_vec : mgsVec A b = vec A b :=
  eq_vec_of_modifiedGramSchmidt A b (mgsVec_zero A b) (mgsVec_succ A b)

/-- **Rescaling the starting vector by a positive number does not change the Arnoldi vectors**: if
$c > 0$, then $v_j(A, cb) = v_j(A, b)$ for every $j$.

Both sequences satisfy the modified Gram–Schmidt recurrence from $b / \|b\|$
(`Arnoldi.eq_vec_of_modifiedGramSchmidt`). -/
theorem vec_smul_of_pos {c : ℝ} (hc : 0 < c) : vec A ((c : 𝕜) • b) = vec A b := by
  refine eq_vec_of_modifiedGramSchmidt A b ?_ fun j => ?_
  · rw [← mgsVec_eq_vec, mgsVec_zero, smul_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hc]
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    · have hb' : (‖b‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hb)
      have hc' : (c : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hc.ne'
      congr 1
      push_cast
      field_simp
  · rw [← mgsVec_eq_vec]
    exact mgsVec_succ A ((c : 𝕜) • b) j

/-- The Arnoldi coefficients are the coefficients of the modified Gram–Schmidt loop: for all $i$ and
$j$,
$$h_{ij} = \langle v_i, w^{(i)} \rangle,$$
where $w^{(i)}$ is $A v_j$ after the components along $v_0, \dots, v_{i-1}$ have been removed
one at a time by the modified Gram–Schmidt sweep. -/
theorem coeff_eq_inner_modifiedGramSchmidtSweep (i j : ℕ) :
    coeff A b i j = inner 𝕜 (vec A b i)
      (InnerProductSpace.modifiedGramSchmidtSweep 𝕜 (vec A b) (A (vec A b j)) i) :=
  (InnerProductSpace.inner_modifiedGramSchmidtSweep_self 𝕜
    (fun _ _ h => inner_vec_eq_zero A b h) _ i).symm

end Arnoldi
