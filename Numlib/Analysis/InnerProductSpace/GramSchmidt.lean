/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Gram–Schmidt orthogonalization: uniqueness, naturality and the modified process

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$(f_j)_{j \in \iota}$ be a family of vectors, indexed by a well-ordered set in which every index has
finitely many predecessors (for instance $\mathbb{N}$). Mathlib's Gram–Schmidt vectors
`InnerProductSpace.gramSchmidt` are $g_j = f_j - \sum_{i < j} \frac{\langle g_i, f_j
\rangle}{\|g_i\|^2} g_i$, and the normalized vectors `InnerProductSpace.gramSchmidtNormed` are
$e_j = g_j / \|g_j\|$, with $e_j = 0$ when $g_j = 0$. This file proves that an orthonormal family
$(u_j)$ with $\operatorname{span}\{u_i : i \le j\} = \operatorname{span}\{f_i : i \le j\}$ for every
$j$ satisfies $u_j = \varepsilon_j e_j$ with $|\varepsilon_j| = 1$, and $u_j = e_j$ when
$\langle u_j, f_j \rangle > 0$. This uniqueness principle identifies the vectors that different
algorithms compute: the classical and the modified Gram–Schmidt Arnoldi processes, the Householder
Arnoldi process (up to signs), and the Lanczos vectors with the normalized conjugate-gradient
residuals.

Gram–Schmidt commutes with linear isometries, so every process built on it (Arnoldi, Lanczos)
carries over between isometric spaces, for instance from an operator to its matrix. The modified
Gram–Schmidt sweep subtracts the components of a vector along $q_0, q_1, \dots$ one at a time, each
against the current vector. Against an orthogonal family it gives the classical vector
$a - \sum_j \langle q_j, a \rangle q_j$, so in exact arithmetic the modified process computes the
Gram–Schmidt vectors.

## Main definitions

* `InnerProductSpace.modifiedGramSchmidtSweep`: one sweep $v_0 = a$,
  $v_{j+1} = v_j - \langle q_j, v_j \rangle q_j$ of the modified Gram–Schmidt process.

## Main results

* `InnerProductSpace.span_gramSchmidt_of_isLowerSet`: the vectors $g_i$ and $f_i$ with $i$ in a
  lower set $J$ span the same subspace.
* `InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed`: an orthonormal family with the same
  spans as $(f_j)$ is $(\varepsilon_j e_j)$ with $|\varepsilon_j| = 1$.
* `InnerProductSpace.eq_gramSchmidtNormed_of_re_inner_pos`: if moreover
  $\langle u_j, f_j \rangle > 0$, then $u_j = e_j$.
* `InnerProductSpace.inner_gramSchmidtNormed_eq_zero`,
  `InnerProductSpace.sub_sum_inner_smul_gramSchmidtNormed_mem_orthogonal`,
  `InnerProductSpace.eq_sum_inner_smul_gramSchmidtNormed`: orthogonality and orthonormal expansions
  in the vectors $e_i$, without linear independence of $(f_j)$.
* `InnerProductSpace.gramSchmidt_comp_linearIsometry`,
  `InnerProductSpace.gramSchmidtNormed_comp_linearIsometry`: Gram–Schmidt commutes with linear
  isometries.
* `InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`: against a pairwise orthogonal family, the
  modified sweep gives $a - \sum_{j < k} \langle q_j, a \rangle q_j$.
* `InnerProductSpace.modifiedGramSchmidt_eq_gramSchmidt`: the modified sweep of $f_n$ against
  $e_0, \dots, e_{n-1}$ is $g_n$.

## Implementation notes

* The inner product $\langle x, y \rangle$ is `inner 𝕜 x y`. It is conjugate-linear in $x$, so
  $\langle q, v \rangle q$ is the component of $v$ along a unit vector $q$.
* The vector $g_j$ is $0$ exactly when $f_j$ lies in the span of the vectors $f_i$ with $i < j$. The
  results on breakdown hold for every family $(f_j)$, because the vectors that vanish contribute
  nothing.
* The modified sweep takes an infinite sequence $(q_j)_{j \in \mathbb{N}}$. A finite family
  $q_0, \dots, q_{k-1}$ is used through its extension by zero, and the sweep is constant after step
  $k$.
-/

namespace InnerProductSpace

open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

omit [WellFoundedLT ι] in
/-- Let $(f_i)_{i \in \iota}$ be a family in $E$ and let $J \subseteq \iota$ be a lower set: if
$j \in J$ and $i \le j$, then $i \in J$. Then the Gram–Schmidt vectors with indices in $J$ span
the same subspace as the vectors $f_i$ with indices in $J$:
$$\operatorname{span}\{g_i : i \in J\} = \operatorname{span}\{f_i : i \in J\}.$$

Mathlib's `InnerProductSpace.span_gramSchmidt_Iic` is the case $J = \{i : i \le j\}$. A lower
set is the union of these sets for its members, and the general case follows. -/
theorem span_gramSchmidt_of_isLowerSet (f : ι → E) {J : Set ι} (hJ : IsLowerSet J) :
    Submodule.span 𝕜 (gramSchmidt 𝕜 f '' J) = Submodule.span 𝕜 (f '' J) := by
  have hcover : J = ⋃ i ∈ J, Set.Iic i := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Iic, exists_prop]
    exact ⟨fun hy => ⟨y, hy, le_rfl⟩, fun ⟨_, hi, hyi⟩ => hJ hyi hi⟩
  rw [hcover, Set.image_iUnion₂, Set.image_iUnion₂, Submodule.span_iUnion₂,
    Submodule.span_iUnion₂]
  exact iSup_congr fun i => iSup_congr fun _ => span_gramSchmidt_Iic 𝕜 f i

omit [WellFoundedLT ι] in
/-- For every index $j$, the difference $f_j - g_j$ lies in $\operatorname{span}\{f_i : i < j\}$:
the Gram–Schmidt vector $g_j$ is $f_j$ minus a vector in the span of the earlier vectors. -/
theorem sub_gramSchmidt_mem_span (f : ι → E) (j : ι) :
    f j - gramSchmidt 𝕜 f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
  rw [gramSchmidt_def, sub_sub_cancel, ← span_gramSchmidt_Iio 𝕜 f j]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hle : (𝕜 ∙ gramSchmidt 𝕜 f i) ≤ Submodule.span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio j) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩
  exact hle (Submodule.starProjection_apply_mem _ (f j))

omit [WellFoundedLT ι] in
/-- For every index $j$, the Gram–Schmidt vector $g_j$ is orthogonal to
$\operatorname{span}\{f_i : i < j\}$. -/
theorem gramSchmidt_mem_orthogonal (f : ι → E) (j : ι) :
    gramSchmidt 𝕜 f j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  have hle : Submodule.span 𝕜 (f '' Set.Iio j) ≤
      LinearMap.ker ((innerSL 𝕜 (gramSchmidt 𝕜 f j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular 𝕜 f hi
  exact hle hu

omit [WellFoundedLT ι] in
/-- For every index $j$, $\langle g_j, f_j \rangle = \|g_j\|^2$, because $g_j$ is the component of
$f_j$ orthogonal to the earlier vectors. -/
theorem inner_gramSchmidt_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidt 𝕜 f j) (f j) = ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' 𝕜 f j]
  rw [inner_add_right, inner_sum, inner_self_eq_norm_sq_to_K]
  convert add_zero _
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [inner_smul_right, gramSchmidt_orthogonal 𝕜 f (Finset.mem_Iio.1 hi).ne', mul_zero]

omit [WellFoundedLT ι] in
/-- For every index $j$, $\langle e_j, f_j \rangle = \|g_j\|$. In particular this inner product is a
nonnegative real number. -/
theorem inner_gramSchmidtNormed_self (f : ι → E) (j : ι) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f j) (f j) = (‖gramSchmidt 𝕜 f j‖ : 𝕜) := by
  rw [gramSchmidtNormed, inner_smul_left, inner_gramSchmidt_self, RCLike.conj_inv,
    RCLike.conj_ofReal]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) 0 with h | h
  · simp [h]
  · rw [sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

omit [WellFoundedLT ι] in
/-- Let $(f_j)_{j \in \iota}$ and $(u_j)_{j \in \iota}$ be families in $E$. Suppose that $(u_j)$ is
orthonormal and that
$$\operatorname{span}\{u_i : i \le j\} = \operatorname{span}\{f_i : i \le j\} \quad \text{for
  every } j.$$
Then for every index $j$ there is a scalar $\varepsilon \in \mathbb{K}$ with $|\varepsilon| = 1$
and $u_j = \varepsilon e_j$, where $e_j$ is the normalized Gram–Schmidt vector
`InnerProductSpace.gramSchmidtNormed`.

So an orthonormal basis of the flag of subspaces spanned by $(f_j)$ is unique up to unimodular
scalars. -/
theorem exists_norm_eq_one_smul_gramSchmidtNormed {f u : ι → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ι) : ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u j = ε • gramSchmidtNormed 𝕜 f j := by
  have hIio : Submodule.span 𝕜 (u '' Set.Iio j) = Submodule.span 𝕜 (f '' Set.Iio j) := by
    have hcover : Set.Iio j = ⋃ i ∈ Set.Iio j, Set.Iic i := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_Iic, exists_prop]
      exact ⟨fun hx => ⟨x, hx, le_rfl⟩, fun ⟨_, hi, hxi⟩ => lt_of_le_of_lt hxi hi⟩
    rw [hcover, Set.image_iUnion₂, Set.image_iUnion₂, Submodule.span_iUnion₂,
      Submodule.span_iUnion₂]
    exact iSup_congr fun i => iSup_congr fun _ => hspan i
  have huperp : u j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ := by
    rw [← hIio, Submodule.mem_orthogonal']
    intro w hw
    have hle : Submodule.span 𝕜 (u '' Set.Iio j) ≤
        LinearMap.ker ((innerSL 𝕜 (u j) : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hu.2 hi.ne'
    exact hle hw
  have hmem : u j ∈ Submodule.span 𝕜 (f '' Set.Iic j) := by
    rw [← hspan j]
    exact Submodule.subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩
  rw [show Set.Iic j = insert j (Set.Iio j) from (Set.Iio_insert (a := j)).symm,
    Set.image_insert_eq,
    Submodule.span_insert] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hs : u j - c • gramSchmidt 𝕜 f j ∈ Submodule.span 𝕜 (f '' Set.Iio j) := by
    have hrw : u j - c • gramSchmidt 𝕜 f j = c • (f j - gramSchmidt 𝕜 f j) + z := by
      rw [← hyz]; module
    rw [hrw]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sub_gramSchmidt_mem_span f j)) hz
  have hsperp : u j - c • gramSchmidt 𝕜 f j ∈ (Submodule.span 𝕜 (f '' Set.Iio j))ᗮ :=
    Submodule.sub_mem _ huperp (Submodule.smul_mem _ _ (gramSchmidt_mem_orthogonal f j))
  have huj : u j = c • gramSchmidt 𝕜 f j := by
    rw [← sub_eq_zero]
    exact inner_self_eq_zero.1
      ((Submodule.mem_orthogonal' _ _).1 hsperp _ hs)
  have hnorm : ‖u j‖ = 1 := hu.1 j
  have hg : gramSchmidt 𝕜 f j ≠ 0 := by
    intro h
    rw [huj, h, smul_zero, norm_zero] at hnorm
    norm_num at hnorm
  have hgn : ((‖gramSchmidt 𝕜 f j‖ : 𝕜)) ≠ 0 := by
    simpa using norm_ne_zero_iff.2 hg
  refine ⟨c * (‖gramSchmidt 𝕜 f j‖ : 𝕜), ?_, ?_⟩
  · rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [huj, norm_smul] at hnorm
    exact hnorm
  · rw [huj, gramSchmidtNormed, smul_smul, mul_assoc, mul_inv_cancel₀ hgn, mul_one]

/-- A scalar $w$ with $|w| = 1$ such that $w r > 0$ for a real number $r \ge 0$ is equal to $1$. -/
private theorem eq_one_of_norm_eq_one_of_mul_ofReal_pos {w : 𝕜} (hw : ‖w‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hpos : 0 < w * (r : 𝕜)) : w = 1 := by
  rw [mul_comm, RCLike.pos_iff, RCLike.re_ofReal_mul, RCLike.im_ofReal_mul] at hpos
  obtain ⟨h1, h2⟩ := hpos
  have hr0 : r ≠ 0 := by rintro rfl; simp at h1
  have him : RCLike.im w = 0 := (mul_eq_zero.1 h2).resolve_left hr0
  have hsq : RCLike.re w * RCLike.re w + RCLike.im w * RCLike.im w = 1 := by
    rw [← RCLike.norm_sq_eq_def, hw]; norm_num
  refine RCLike.ext ?_ ?_
  · rw [RCLike.one_re]; nlinarith
  · rw [RCLike.one_im, him]

omit [WellFoundedLT ι] in
/-- Let $(f_j)$ and $(u_j)$ be families in $E$ indexed by $\iota$. Suppose that $(u_j)$ is
orthonormal and that $\operatorname{span}\{u_i : i \le j\} = \operatorname{span}\{f_i : i \le
j\}$ for every $j$. If $\langle u_j, f_j \rangle > 0$ for an index $j$, then $u_j = e_j$, the
normalized Gram–Schmidt vector `InnerProductSpace.gramSchmidtNormed`.

The hypothesis $\langle u_j, f_j \rangle > 0$ uses the order of `RCLike` on $\mathbb{K}$: the
inner product is a positive real number. A positive real part is not enough over $\mathbb{C}$,
because a unimodular factor $\varepsilon$ with $\operatorname{Re} \varepsilon > 0$ need not be
$1$. So the statement with the hypothesis $\operatorname{Re} \langle u_j, f_j \rangle > 0$ is
false. Over $\mathbb{R}$ the two hypotheses agree. -/
theorem eq_gramSchmidtNormed_of_re_inner_pos {f u : ι → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j))
    (j : ι) (hpos : 0 < inner 𝕜 (u j) (f j)) : u j = gramSchmidtNormed 𝕜 f j := by
  obtain ⟨ε, hε, hue⟩ := exists_norm_eq_one_smul_gramSchmidtNormed hu hspan j
  rw [hue, inner_smul_left, inner_gramSchmidtNormed_self] at hpos
  have hconj : (starRingEnd 𝕜) ε = 1 :=
    eq_one_of_norm_eq_one_of_mul_ofReal_pos (by rwa [RCLike.norm_conj]) (norm_nonneg _) hpos
  have hε1 : ε = 1 := by
    have := congrArg (starRingEnd 𝕜) hconj
    rwa [RCLike.conj_conj, map_one] at this
  rw [hue, hε1, one_smul]

/-!
### Gram–Schmidt with breakdown

The vector $g_j$ is $0$ exactly when $f_j$ lies in the span of the vectors $f_i$ with $i < j$, and
then $e_j = 0$. The following facts hold with no linear independence hypothesis, because the vectors
that vanish contribute nothing.
-/

section Breakdown

omit [WellFoundedLT ι] in
/-- For all indices $i \ne j$, the normalized Gram–Schmidt vectors satisfy
$\langle e_i, e_j \rangle = 0$. No hypothesis on $(f_j)$ is needed: a vector $e_i$ that vanishes
is orthogonal to every vector. -/
theorem inner_gramSchmidtNormed_eq_zero (f : ι → E) {i j : ι} (h : i ≠ j) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f h]

/-- Let $(f_i)_{i \in \mathbb{N}}$ be a family in $E$, let $x \in E$ and let $n \in \mathbb{N}$.
Then the vector
$$x - \sum_{i < n} \langle e_i, x \rangle e_i$$
is orthogonal to $\operatorname{span}\{e_i : i < n\}$. No linear independence of $(f_i)$ is
needed. -/
theorem sub_sum_inner_smul_gramSchmidtNormed_mem_orthogonal (f : ℕ → E) (x : E) (n : ℕ) :
    x - ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x • gramSchmidtNormed 𝕜 f i ∈
      (Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n))ᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, hk, rfl⟩ := hz
    rw [inner_sub_right, inner_sum, Finset.sum_eq_single k]
    · rcases eq_or_ne (gramSchmidtNormed 𝕜 f k) 0 with h0 | h0
      · simp [h0]
      · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, gramSchmidtNormed_unit_length' h0]
        simp
    · intro i _ hik
      rw [inner_smul_right, inner_gramSchmidtNormed_eq_zero f (Ne.symm hik), mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.2 hk) hk'
  | zero => simp
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul c z _ hz => rw [inner_smul_left, hz, mul_zero]

/-- Let $(f_i)_{i \in \mathbb{N}}$ be a family in $E$ and let $n \in \mathbb{N}$. Every
$x \in \operatorname{span}\{e_i : i < n\}$ is its own orthonormal expansion:
$$x = \sum_{i < n} \langle e_i, x \rangle e_i.$$
No linear independence of $(f_i)$ is needed, because the vectors $e_i$ that vanish contribute
nothing. -/
theorem eq_sum_inner_smul_gramSchmidtNormed (f : ℕ → E) {x : E} {n : ℕ}
    (hx : x ∈ Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n)) :
    x = ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x • gramSchmidtNormed 𝕜 f i := by
  have hy : x - ∑ i ∈ Finset.range n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) x •
      gramSchmidtNormed 𝕜 f i ∈ Submodule.span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iio n) :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_range.1 hi, rfl⟩))
  have h0 := Submodule.inner_right_of_mem_orthogonal hy
    (sub_sum_inner_smul_gramSchmidtNormed_mem_orthogonal f x n)
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

end Breakdown

section LinearIsometry

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

/-- Let $E'$ be another inner product space over $\mathbb{K}$, let $T : E \to E'$ be a linear
isometry and let $(f_i)$ be a family in $E$. Then for every index $n$, the $n$-th Gram–Schmidt
vector of the family $(T f_i)$ is $T g_n$.

The process uses only inner products and norms, which $T$ preserves. -/
theorem gramSchmidt_comp_linearIsometry (e : E →ₗᵢ[𝕜] E') (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 (e ∘ f) n = e (gramSchmidt 𝕜 f n) := by
  induction n using WellFoundedLT.induction with
  | _ n ih =>
    rw [eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 (e ∘ f) n).symm,
      eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 f n).symm, map_sub, map_sum, Function.comp_apply]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ih i (Finset.mem_Iio.1 hi), LinearIsometry.inner_map_map,
      LinearIsometry.norm_map, map_smul]

/-- Let $E'$ be another inner product space over $\mathbb{K}$, let $T : E \to E'$ be a linear
isometry and let $(f_i)$ be a family in $E$. Then for every index $n$, the $n$-th normalized
Gram–Schmidt vector of the family $(T f_i)$ is $T e_n$.

This is the normalized form of `InnerProductSpace.gramSchmidt_comp_linearIsometry`. -/
theorem gramSchmidtNormed_comp_linearIsometry (e : E →ₗᵢ[𝕜] E') (f : ι → E) (n : ι) :
    gramSchmidtNormed 𝕜 (e ∘ f) n = e (gramSchmidtNormed 𝕜 f n) := by
  rw [gramSchmidtNormed, gramSchmidtNormed, gramSchmidt_comp_linearIsometry,
    LinearIsometry.norm_map, map_smul]

end LinearIsometry

section ModifiedGramSchmidt

variable (𝕜)

/-- Let $(q_j)_{j \in \mathbb{N}}$ be vectors in $E$ and let $a \in E$. **One sweep of the modified
Gram–Schmidt process** against $(q_j)$, starting from $a$, is the sequence
$$v_0 = a, \qquad v_{j+1} = v_j - \langle q_j, v_j \rangle q_j.$$
Each step removes from the current vector its component along the next vector $q_j$, when
$\|q_j\| = 1$. The term `modifiedGramSchmidtSweep 𝕜 q a j` is $v_j$.

The classical process takes all inner products against the original vector $a$. The modified
process takes each one against the current vector; this order of operations is the numerically
stable one. In exact arithmetic the two agree for an orthogonal family
(`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`). A finite family $q_0, \dots, q_{k-1}$
is used through its extension by zero, and then the sweep is constant after step $k$. -/
noncomputable def modifiedGramSchmidtSweep (q : ℕ → E) (a : E) : ℕ → E
  | 0 => a
  | j + 1 =>
    modifiedGramSchmidtSweep q a j - inner 𝕜 (q j) (modifiedGramSchmidtSweep q a j) • q j

/-- The modified Gram–Schmidt sweep starts at $a$: $v_0 = a$. -/
@[simp]
theorem modifiedGramSchmidtSweep_zero (q : ℕ → E) (a : E) :
    modifiedGramSchmidtSweep 𝕜 q a 0 = a :=
  rfl

/-- One step of the modified Gram–Schmidt sweep: $v_{j+1} = v_j - \langle q_j, v_j \rangle q_j$. -/
theorem modifiedGramSchmidtSweep_succ (q : ℕ → E) (a : E) (j : ℕ) :
    modifiedGramSchmidtSweep 𝕜 q a (j + 1) = modifiedGramSchmidtSweep 𝕜 q a j -
      inner 𝕜 (q j) (modifiedGramSchmidtSweep 𝕜 q a j) • q j :=
  rfl

/-- Let $(q_j)$ and $(q'_j)$ be sequences in $E$ with $q_i = q'_i$ for all $i < k$. Then the
modified Gram–Schmidt sweeps against $(q_j)$ and against $(q'_j)$, starting from the same vector
$a$, agree at step $k$.

So the vector $v_k$ depends only on $q_0, \dots, q_{k-1}$. -/
theorem modifiedGramSchmidtSweep_congr {q q' : ℕ → E} (a : E) {k : ℕ}
    (h : ∀ i < k, q i = q' i) :
    modifiedGramSchmidtSweep 𝕜 q a k = modifiedGramSchmidtSweep 𝕜 q' a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [modifiedGramSchmidtSweep_succ, modifiedGramSchmidtSweep_succ,
      ih fun i hi => h i (hi.trans k.lt_succ_self), h k k.lt_succ_self]

/-- Let $(q_j)_{j \in \mathbb{N}}$ be pairwise orthogonal vectors in $E$:
$\langle q_i, q_j \rangle = 0$ for $i \ne j$. Then for every $a \in E$ and $k \in \mathbb{N}$,
the modified Gram–Schmidt sweep gives the classical Gram–Schmidt vector:
$$v_k = a - \sum_{j < k} \langle q_j, a \rangle q_j.$$

The vector subtracted at step $i$ is a multiple of $q_i$, which is orthogonal to every later
$q_j$. So each subtraction leaves the inner products with the later vectors unchanged. Only
orthogonality is used, not normalization. For an orthonormal family `hq : Orthonormal 𝕜 q`, the
hypothesis is `fun _ _ h => hq.2 h`. -/
theorem modifiedGramSchmidtSweep_eq_sub_sum {q : ℕ → E}
    (hq : Pairwise fun i j => inner 𝕜 (q i) (q j) = 0) (a : E) (k : ℕ) :
    modifiedGramSchmidtSweep 𝕜 q a k = a - ∑ j ∈ Finset.range k, inner 𝕜 (q j) a • q j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hinner : inner 𝕜 (q k) (modifiedGramSchmidtSweep 𝕜 q a k) = inner 𝕜 (q k) a := by
      rw [ih, inner_sub_right, inner_sum]
      refine sub_eq_self.2 (Finset.sum_eq_zero fun j hj => ?_)
      rw [inner_smul_right, hq (Finset.mem_range.1 hj).ne', mul_zero]
    rw [modifiedGramSchmidtSweep_succ, hinner, ih, Finset.sum_range_succ, sub_sub]

/-- Let $(q_j)_{j \in \mathbb{N}}$ be pairwise orthogonal vectors in $E$. Then for every $a \in E$
and $k \in \mathbb{N}$, the sweep does not change the coefficient that it is about to compute:
$$\langle q_k, v_k \rangle = \langle q_k, a \rangle.$$

So the coefficients of the modified process, taken against the current vector, are those of the
classical process, taken against $a$. -/
theorem inner_modifiedGramSchmidtSweep_self {q : ℕ → E}
    (hq : Pairwise fun i j => inner 𝕜 (q i) (q j) = 0) (a : E) (k : ℕ) :
    inner 𝕜 (q k) (modifiedGramSchmidtSweep 𝕜 q a k) = inner 𝕜 (q k) a := by
  rw [modifiedGramSchmidtSweep_eq_sub_sum 𝕜 hq, inner_sub_right, inner_sum]
  refine sub_eq_self.2 (Finset.sum_eq_zero fun j hj => ?_)
  rw [inner_smul_right, hq (Finset.mem_range.1 hj).ne', mul_zero]

omit [WellFoundedLT ι] in
/-- For every index $i$ and every $x \in E$,
$$\langle e_i, x \rangle e_i = \frac{\langle g_i, x \rangle}{\|g_i\|^2} g_i,$$
the orthogonal projection of $x$ onto the line spanned by $g_i$. If $g_i = 0$, both sides are
$0$. -/
theorem inner_gramSchmidtNormed_smul_self (f : ι → E) (i : ι) (x : E) :
    inner 𝕜 (gramSchmidtNormed 𝕜 f i) x • gramSchmidtNormed 𝕜 f i =
      (inner 𝕜 (gramSchmidt 𝕜 f i) x / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  rw [gramSchmidtNormed, inner_smul_left, smul_smul, RCLike.conj_inv, RCLike.conj_ofReal]
  rcases eq_or_ne ((‖gramSchmidt 𝕜 f i‖ : 𝕜)) 0 with h | h
  · rw [h]; simp
  · congr 1
    field_simp

/-- Let $(f_i)_{i \in \mathbb{N}}$ be a family in $E$ and let $n \in \mathbb{N}$. The modified
Gram–Schmidt sweep of $f_n$ against the normalized vectors $e_0, e_1, \dots$ gives the
Gram–Schmidt vector $g_n$ after $n$ steps: if $v_0 = f_n$ and
$v_{j+1} = v_j - \langle e_j, v_j \rangle e_j$, then $v_n = g_n$.

So the modified Gram–Schmidt method computes the Gram–Schmidt vectors in exact arithmetic. No
linear independence of $(f_i)$ is needed. -/
theorem modifiedGramSchmidt_eq_gramSchmidt (f : ℕ → E) (n : ℕ) :
    modifiedGramSchmidtSweep 𝕜 (gramSchmidtNormed 𝕜 f) (f n) n = gramSchmidt 𝕜 f n := by
  have hq : Pairwise fun i j =>
      inner 𝕜 (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) = 0 := by
    intro i j hij
    rw [gramSchmidtNormed, gramSchmidtNormed, inner_smul_left, inner_smul_right,
      gramSchmidt_orthogonal 𝕜 f hij, mul_zero, mul_zero]
  rw [modifiedGramSchmidtSweep_eq_sub_sum 𝕜 hq, eq_comm, eq_sub_iff_add_eq, ← Nat.Iio_eq_range]
  have hsum : ∑ i ∈ Finset.Iio n, inner 𝕜 (gramSchmidtNormed 𝕜 f i) (f n) •
        gramSchmidtNormed 𝕜 f i = ∑ i ∈ Finset.Iio n,
        (inner 𝕜 (gramSchmidt 𝕜 f i) (f n) / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i :=
    Finset.sum_congr rfl fun i _ => inner_gramSchmidtNormed_smul_self 𝕜 f i (f n)
  rw [hsum]
  exact (gramSchmidt_def'' 𝕜 f n).symm

end ModifiedGramSchmidt

end InnerProductSpace
