/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Orthonormal
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Operator.LinearIsometry
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Principal angles between subspaces

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $F$ and
$G$ be finite-dimensional subspaces of $E$ with orthogonal projections $P_F$ and $P_G$. Let
$q = \dim G$. The **principal angles** $0 \le \theta_0 \le \theta_1 \le \dots \le \theta_{q-1} \le
\pi/2$ between $F$ and $G$ are defined by their cosines, which are the singular values of the
restricted projection $P_F|_G \colon G \to F$, $x \mapsto P_F x$. The **principal vectors** are the
corresponding singular vectors: an orthonormal basis $(g_j)$ of $G$ and an orthonormal family
$(f_j)$ in $F$ with $P_F g_j = \cos \theta_j \, f_j$. The presentation follows [golub2013matrix],
§6.4.3–6.4.4, after Björck and Golub (1973) and Jordan (1875).

The source defines the principal vectors recursively: $(f_k, g_k)$ maximizes
$\operatorname{Re} \langle u, v \rangle$ over unit vectors $u \in F$ and $v \in G$ orthogonal to the
earlier $f_i$ and $g_i$. Here this recursive definition is a theorem: every such greedy choice of
maximizers gives the principal angles. The module also proves that the intersection $F \cap G$ is
spanned by the principal vectors of angle $0$, that for subspaces of equal dimension the gap
$\|P_F - P_G\|$ is the sine of the largest angle, and that for matrices $Q_A$ and $Q_B$ with
orthonormal columns the cosines are the singular values of $Q_A^H Q_B$.

## Main definitions

* `Submodule.cosPrincipalAngle`: the cosines $\cos \theta_i$, the singular values of $P_F|_G$.
* `Submodule.principalAngle`: the principal angles $\theta_i = \arccos(\cos \theta_i)$.
* `Submodule.IsPrincipalVectors`: $(g_j)$ is an orthonormal basis of $G$, $(f_j)$ is orthonormal in
  $F$, and $P_F g_j = \cos \theta_j \, f_j$.
* `Submodule.IsRecursivePrincipalVectors`: the recursive definition of the source, a greedy sequence
  of maximizers of $\operatorname{Re} \langle u, v \rangle$ over unit vectors orthogonal to the
  earlier ones.

## Main results

* `Submodule.cosPrincipalAngle_nonneg`, `Submodule.cosPrincipalAngle_le_one`,
  `Submodule.antitone_cosPrincipalAngle`, `Submodule.monotone_principalAngle`,
  `Submodule.principalAngle_mem_Icc`: $0 \le \theta_0 \le \theta_1 \le \dots \le \pi/2$.
* `Submodule.cosPrincipalAngle_comm`: the principal angles between $F$ and $G$ are those between $G$
  and $F$.
* `Submodule.exists_isPrincipalVectors`: principal vectors exist when $\dim G \le \dim F$.
* `Submodule.IsPrincipalVectors.isGreatest_re_inner`: the max–max characterization of
  $\cos \theta_k$.
* `Submodule.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors`: every greedy choice of maximizers
  gives the principal angles, so the recursive definition of the source is well posed.
* `Submodule.IsPrincipalVectors.inf_eq_span`, `Submodule.finrank_inf_eq_card`: $F \cap G$ is spanned
  by the principal vectors of angle $0$, and its dimension is the number of these angles (Theorem
  6.4.2 of [golub2013matrix]).
* `Submodule.cosPrincipalAngle_eq_singularValues`: for matrices $Q_A$ and $Q_B$ with orthonormal
  columns, the cosines are the singular values of $Q_A^H Q_B$.
* `Submodule.cosPrincipalAngle_eq_of_isSVD`, `Submodule.isPrincipalVectors_of_isSVD`: from any SVD
  $Q_A^H Q_B = Y \Sigma Z^H$, the diagonal of $\Sigma$ lists the cosines, and the columns of
  $Q_A Y(:, 1{:}q)$ and $Q_B Z$ are principal vectors. This is the SVD step of Algorithm 6.4.3 of
  [golub2013matrix].
* `Submodule.gap_eq_sin_principalAngle`: $\operatorname{dist}(F, G) = \sin \theta_{\max}$ for
  subspaces of equal dimension.
* `Submodule.cosPrincipalAngle_span_singleton_zero`: the cosine of the first principal angle between
  $F$ and a line is `Submodule.cosAngle`, the cosine of the angle between $F$ and a nonzero vector
  of the line.

## Implementation notes

* Indices start at $0$: the angle $\theta_i$ here, `Submodule.principalAngle F G i`, is the angle
  $\theta_{i+1}$ of [golub2013matrix]. A principal vector $f_j$ or $g_j$ is indexed by `j : Fin q`.
* The cosines are Mathlib's `LinearMap.singularValues` of
  `Submodule.orthogonalProjectionRestrict F G`. These are sorted in decreasing order and padded with
  zeros. So `Submodule.cosPrincipalAngle F G i` is $0$ and the angle is $\pi/2$ for $i \ge \dim G$.
* The definition uses singular values, not recursion. The recursion is then a characterization,
  proved by deflation (`LinearMap.singularValues_comp_linearIsometry_eq_succ`).
* No result needs completeness or finite dimension of $E$, only finite dimension of $F$ and $G$.
* The distance between subspaces of [golub2013matrix], §2.5.3, is `Submodule.gap` of
  `Numlib.Analysis.InnerProductSpace.Projection.Gap`. Its theory for equal dimensions gives
  `Submodule.gap_eq_sin_principalAngle` without coordinates.
-/

open Module

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (F G : Submodule 𝕜 E) [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. The **cosines of the
principal angles** between $F$ and $G$ are the singular values of the restricted projection
$P_F|_G \colon G \to F$, in decreasing order:
$$\cos \theta_i = \sigma_i(P_F|_G), \qquad i = 0, 1, 2, \dots$$
This is $\cos \theta_{i+1}$ in (6.4.3) of [golub2013matrix].

The singular values are Mathlib's `LinearMap.singularValues`, indexed from $0$ and equal to $0$
for $i \ge \dim G$. -/
noncomputable def cosPrincipalAngle (i : ℕ) : ℝ :=
  (F.orthogonalProjectionRestrict G).singularValues i

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. The **principal
angles** between $F$ and $G$ are
$$\theta_i = \arccos(\cos \theta_i), \qquad i = 0, 1, 2, \dots,$$
where $\cos \theta_i$ is `Submodule.cosPrincipalAngle F G i`. This is $\theta_{i+1}$ in (6.4.3)
of [golub2013matrix]. For $i \ge \dim G$ the value is $\pi/2$. -/
noncomputable def principalAngle (i : ℕ) : ℝ :=
  Real.arccos (F.cosPrincipalAngle G i)

/-- The cosines of the principal angles are nonnegative: $\cos \theta_i \ge 0$ for every $i$. -/
theorem cosPrincipalAngle_nonneg (i : ℕ) : 0 ≤ F.cosPrincipalAngle G i :=
  LinearMap.singularValues_nonneg _ i

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. Then
$\cos \theta_i \le 1$ for every $i$. The reason is that an orthogonal projection does not
lengthen vectors. In [golub2013matrix], §6.4.3, this is the statement that the singular values
of $Q_A^T Q_B$ lie in $[0, 1]$. -/
theorem cosPrincipalAngle_le_one (i : ℕ) : F.cosPrincipalAngle G i ≤ 1 :=
  LinearMap.singularValues_le_of_forall_norm_apply_le _ zero_le_one (fun x => by
    rw [← Submodule.norm_coe, coe_orthogonalProjectionRestrict_apply, one_mul,
      ← Submodule.norm_coe x]
    exact F.norm_starProjection_apply_le x) i

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. Then the cosines of
the principal angles decrease: $\cos \theta_i \ge \cos \theta_j$ for $i \le j$. -/
theorem antitone_cosPrincipalAngle : Antitone (F.cosPrincipalAngle G) :=
  LinearMap.singularValues_antitone _

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. Then the principal
angles increase:
$$\theta_0 \le \theta_1 \le \theta_2 \le \cdots.$$
This is stated in §6.4.3 of [golub2013matrix]. -/
theorem monotone_principalAngle : Monotone (F.principalAngle G) :=
  fun _ _ hij => Real.antitone_arccos (F.antitone_cosPrincipalAngle G hij)

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. Then every principal
angle satisfies
$$0 \le \theta_i \le \pi/2.$$
This is stated in §6.4.3 of [golub2013matrix]. -/
theorem principalAngle_mem_Icc (i : ℕ) : F.principalAngle G i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (F.cosPrincipalAngle_nonneg G i)⟩

/-- **Principal angles are symmetric.** Let $F$ and $G$ be finite-dimensional subspaces of an inner
product space. Then the cosines of the principal angles between $F$ and $G$ equal those between
$G$ and $F$:
$$\cos \theta_i(F, G) = \cos \theta_i(G, F) \quad \text{for every } i.$$

The map $P_G|_F$ is the adjoint of $P_F|_G$, and a map and its adjoint have the same singular
values. -/
theorem cosPrincipalAngle_comm : F.cosPrincipalAngle G = G.cosPrincipalAngle F := by
  funext i
  rw [cosPrincipalAngle, cosPrincipalAngle, ← orthogonalProjectionRestrict_adjoint,
    LinearMap.singularValues_adjoint]

/-! ### Principal vectors -/

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space $E$, and let
$f, g \colon \{0, \dots, q-1\} \to E$. The pair $(f, g)$ is a family of **principal vectors** of
$F$ and $G$ if $\dim G = q$, $f$ and $g$ are orthonormal, $f_j \in F$ and $g_j \in G$ for every
$j$, and
$$P_F g_j = \cos \theta_j \, f_j \quad \text{for every } j.$$
These are the vectors $\{f_i, g_i\}$ of (6.4.3)–(6.4.5) of [golub2013matrix].

So $g$ is an orthonormal basis of $G$ of right singular vectors of $P_F|_G$, and $f$ is a family
of left singular vectors, completed arbitrarily where the cosine vanishes. -/
structure IsPrincipalVectors {q : ℕ} (f g : Fin q → E) : Prop where
  /-- The number $q$ of principal vectors is the dimension of $G$. -/
  finrank_eq : finrank 𝕜 G = q
  /-- The left vectors $f_j$ are orthonormal. -/
  orthonormal_left : Orthonormal 𝕜 f
  /-- The right vectors $g_j$ are orthonormal. -/
  orthonormal_right : Orthonormal 𝕜 g
  /-- Every left vector $f_j$ lies in $F$. -/
  mem_left : ∀ i, f i ∈ F
  /-- Every right vector $g_j$ lies in $G$. -/
  mem_right : ∀ i, g i ∈ G
  /-- The projection onto $F$ maps each right vector to a multiple of the left vector:
  $P_F g_j = \cos \theta_j \, f_j$. -/
  starProjection_right : ∀ j, F.starProjection (g j) = (F.cosPrincipalAngle G j : 𝕜) • f j

/-- **Principal vectors exist.** Let $F$ and $G$ be finite-dimensional subspaces of an inner product
space with $\dim G \le \dim F$. Then there exist $f, g \colon \{0, \dots, \dim G - 1\} \to E$
that form a family of principal vectors of $F$ and $G$. In [golub2013matrix], §6.4.3, this is
the case $p \ge q$.

The vectors come from the singular value decomposition
`LinearMap.exists_orthonormal_singularVectors` of $P_F|_G$. -/
theorem exists_isPrincipalVectors (h : finrank 𝕜 G ≤ finrank 𝕜 F) :
    ∃ f g : Fin (finrank 𝕜 G) → E, F.IsPrincipalVectors G f g := by
  obtain ⟨v, u, hu, hvu⟩ :=
    (F.orthogonalProjectionRestrict G).exists_orthonormal_singularVectors rfl h
  refine ⟨fun i => u i, fun i => v i, ⟨rfl, hu.comp_linearIsometry F.subtypeₗᵢ,
    v.orthonormal.comp_linearIsometry G.subtypeₗᵢ, fun i => (u i).2, fun i => (v i).2,
    fun j => ?_⟩⟩
  have h := congrArg Subtype.val (hvu j)
  rwa [coe_orthogonalProjectionRestrict_apply, Submodule.coe_smul] at h

namespace IsPrincipalVectors

variable {F G} {q : ℕ} {f g : Fin q → E}

/-- Let $(f, g)$ be a family of principal vectors of $F$ and $G$, indexed by $\{0, \dots, q-1\}$.
Then for all $i$ and $j$,
$$\langle f_i, g_j \rangle = \begin{cases} \cos \theta_j & \text{if } i = j, \\ 0 &
  \text{otherwise.} \end{cases}$$
In particular $\cos \theta_k = f_k^T g_k$, as in (6.4.3) of [golub2013matrix].

The proof is $\langle f_i, g_j \rangle = \langle f_i, P_F g_j \rangle = \cos \theta_j \langle
f_i, f_j \rangle$. -/
theorem inner_eq (h : F.IsPrincipalVectors G f g) (i j : Fin q) :
    inner 𝕜 (f i) (g j) = if i = j then (F.cosPrincipalAngle G j : 𝕜) else 0 := by
  rw [← starProjection_eq_self_iff.2 (h.mem_left i), inner_starProjection_left_eq_right,
    h.starProjection_right, inner_smul_right, orthonormal_iff_ite.1 h.orthonormal_left i j]
  split_ifs <;> simp

/-- If $(f, g)$ is a family of principal vectors of $F$ and $G$, then every $v \in G$ satisfies
$v = \sum_j \langle g_j, v \rangle g_j$. -/
theorem sum_inner_smul_right (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ∑ j, inner 𝕜 (g j) v • g j = v := by
  have hon : Orthonormal 𝕜 (fun j => (⟨g j, h.mem_right j⟩ : G)) :=
    (h.orthonormal_right.codRestrict G h.mem_right)
  have hsp : ⊤ ≤ span 𝕜 (Set.range fun j => (⟨g j, h.mem_right j⟩ : G)) :=
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [h.finrank_eq])).ge
  have := congrArg Subtype.val ((OrthonormalBasis.mk hon hsp).sum_repr' ⟨v, hv⟩)
  simpa [OrthonormalBasis.coe_mk, Submodule.coe_inner] using this

/-- If $(f, g)$ is a family of principal vectors of $F$ and $G$, then every $v \in G$ satisfies $P_F
v = \sum_j \langle g_j, v \rangle \cos \theta_j \, f_j$. -/
theorem starProjection_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    F.starProjection v = ∑ j, (inner 𝕜 (g j) v * F.cosPrincipalAngle G j) • f j := by
  conv_lhs => rw [← h.sum_inner_smul_right hv]
  simp_rw [map_sum, map_smul, h.starProjection_right, smul_smul]

/-- If $(f, g)$ is a family of principal vectors of $F$ and $G$, then every $v \in G$ satisfies
Parseval's identity $\|v\|^2 = \sum_j |\langle g_j, v \rangle|^2$. -/
theorem norm_sq_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ‖v‖ ^ 2 = ∑ j, ‖inner 𝕜 (g j) v‖ ^ 2 := by
  conv_lhs => rw [← h.sum_inner_smul_right hv]
  exact h.orthonormal_right.norm_sum_smul_sq _

/-- If $(f, g)$ is a family of principal vectors of $F$ and $G$, then every $v \in G$ satisfies
$\|P_F v\|^2 = \sum_j |\langle g_j, v \rangle|^2 \cos^2 \theta_j$. -/
theorem norm_starProjection_sq_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ‖F.starProjection v‖ ^ 2 = ∑ j, ‖inner 𝕜 (g j) v‖ ^ 2 * F.cosPrincipalAngle G j ^ 2 := by
  rw [h.starProjection_eq_sum hv, h.orthonormal_left.norm_sum_smul_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (F.cosPrincipalAngle_nonneg G j), mul_pow]

/-- If $(f, g)$ is a family of principal vectors of $F$ and $G$, and $v \in G$ satisfies
$\langle g_i, v \rangle = 0$ for all $i < k$, then $\|P_F v\| \le \cos \theta_k \, \|v\|$. -/
theorem norm_starProjection_le (h : F.IsPrincipalVectors G f g) (k : Fin q) {v : E} (hv : v ∈ G)
    (hvk : ∀ i < k, inner 𝕜 (g i) v = 0) :
    ‖F.starProjection v‖ ≤ F.cosPrincipalAngle G k * ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (F.cosPrincipalAngle_nonneg G k) (norm_nonneg _)) two_ne_zero).1 ?_
  rw [h.norm_starProjection_sq_eq_sum hv, mul_pow, h.norm_sq_eq_sum hv, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge j k with hjk | hjk
  · simp [hvk j hjk]
  · rw [mul_comm]
    gcongr
    · exact F.cosPrincipalAngle_nonneg G j
    · exact F.antitone_cosPrincipalAngle G hjk

/-- **The max–max characterization.** Let $(f, g)$ be a family of principal vectors of $F$ and $G$,
indexed by $\{0, \dots, q-1\}$, and let $k < q$. Then $\cos \theta_k$ is the greatest element of
the set of the numbers $\operatorname{Re} \langle u, v \rangle$, where $u \in F$ and $v \in G$
are unit vectors with $\langle f_i, u \rangle = 0$ and $\langle g_i, v \rangle = 0$ for all
$i < k$:
$$\cos \theta_k = \max \{\operatorname{Re} \langle u, v \rangle : u \in F, \ v \in G, \ \|u\| =
  \|v\| = 1, \ u \perp f_i, \ v \perp g_i \ (i < k)\}.$$
The maximum is attained at $(f_k, g_k)$. This is (6.4.3) of [golub2013matrix] and the argument
(6.4.6) after it.

Only the constraint on $v$ matters, because $\operatorname{Re} \langle u, v \rangle \le \|P_F
v\| \le \cos \theta_k$. -/
theorem isGreatest_re_inner (h : F.IsPrincipalVectors G f g) (k : Fin q) :
    IsGreatest {r : ℝ | ∃ u ∈ F, ∃ v ∈ G, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      (∀ i < k, inner 𝕜 (f i) u = 0) ∧ (∀ i < k, inner 𝕜 (g i) v = 0) ∧
        RCLike.re (inner 𝕜 u v) = r} (F.cosPrincipalAngle G k) := by
  refine ⟨⟨f k, h.mem_left k, g k, h.mem_right k, h.orthonormal_left.1 k,
    h.orthonormal_right.1 k, fun i hi => ?_, fun i hi => ?_, ?_⟩, ?_⟩
  · rw [orthonormal_iff_ite.1 h.orthonormal_left, ite_eq_right hi.ne]
  · rw [orthonormal_iff_ite.1 h.orthonormal_right, ite_eq_right hi.ne]
  · rw [h.inner_eq, ite_eq_left rfl, RCLike.ofReal_re]
  · rintro r ⟨u, hu, v, hv, hu1, hv1, -, hvk, rfl⟩
    rw [← starProjection_eq_self_iff.2 hu, inner_starProjection_left_eq_right]
    calc RCLike.re (inner 𝕜 u (F.starProjection v)) ≤ ‖u‖ * ‖F.starProjection v‖ :=
          re_inner_le_norm _ _
      _ ≤ F.cosPrincipalAngle G k := by
          rw [hu1, one_mul]
          simpa [hv1] using h.norm_starProjection_le k hv hvk

/-- Let $(f, g)$ be a family of principal vectors of $F$ and $G$, and let $i$ be an index with
$\cos \theta_i = 1$. Then $f_i = g_i$. This step is in the proof of Theorem 6.4.2 of
[golub2013matrix]: unit vectors with inner product $1$ coincide. -/
theorem eq_of_cosPrincipalAngle_eq_one (h : F.IsPrincipalVectors G f g) {i : Fin q}
    (hi : F.cosPrincipalAngle G i = 1) : f i = g i := by
  rw [← inner_eq_one_iff_of_norm_eq_one (𝕜 := 𝕜) (h.orthonormal_left.1 i)
    (h.orthonormal_right.1 i), h.inner_eq, ite_eq_left rfl, hi, RCLike.ofReal_one]

/-- **The intersection of two subspaces.** Let $(f, g)$ be a family of principal vectors of $F$ and
$G$. Then the intersection $F \cap G$ is spanned by the principal vectors of angle $0$:
$$F \cap G = \operatorname{span} \{f_i : \cos \theta_i = 1\}.$$
This is Theorem 6.4.2 of [golub2013matrix].

The proof in the source gives the inclusion $\supseteq$. For $\subseteq$, a vector
$v \in F \cap G$ has $\|P_F v\| = \|v\|$, and in principal coordinates this forces every
coordinate with $\cos \theta_j < 1$ to vanish. -/
theorem inf_eq_span (h : F.IsPrincipalVectors G f g) :
    F ⊓ G = span 𝕜 (f '' {i | F.cosPrincipalAngle G i = 1}) := by
  apply le_antisymm
  · intro v ⟨hvF, hvG⟩
    have hsq := h.norm_starProjection_sq_eq_sum hvG
    rw [starProjection_eq_self_iff.2 hvF, h.norm_sq_eq_sum hvG, ← sub_eq_zero,
      ← Finset.sum_sub_distrib] at hsq
    have hterm : ∀ j, ‖inner 𝕜 (g j) v‖ ^ 2 * (1 - F.cosPrincipalAngle G j ^ 2) = 0 := by
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ ‖inner 𝕜 (g j) v‖ ^ 2 -
          ‖inner 𝕜 (g j) v‖ ^ 2 * F.cosPrincipalAngle G j ^ 2 := fun j _ => by
        have h1 := F.cosPrincipalAngle_le_one G j
        have h0 := F.cosPrincipalAngle_nonneg G j
        have h2 : F.cosPrincipalAngle G j ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖inner 𝕜 (g j) v‖)]
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsq j (Finset.mem_univ j)
      linarith
    rw [← h.sum_inner_smul_right hvG]
    refine Submodule.sum_mem _ fun j _ => ?_
    rcases mul_eq_zero.1 (hterm j) with h0 | h1
    · rw [norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), zero_smul]
      exact Submodule.zero_mem _
    · have hc : F.cosPrincipalAngle G j = 1 := by
        have h0 := F.cosPrincipalAngle_nonneg G j
        nlinarith
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hc, ?_⟩)
      exact h.eq_of_cosPrincipalAngle_eq_one hc
  · rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨h.mem_left i, h.eq_of_cosPrincipalAngle_eq_one hi ▸ h.mem_right i⟩

end IsPrincipalVectors

/-- **The dimension of the intersection.** Let $F$ and $G$ be finite-dimensional subspaces of an
inner product space with $\dim G \le \dim F$. Then
$$\dim(F \cap G) = \#\{i < \dim G : \cos \theta_i = 1\},$$
the number of principal angles equal to $0$. This is stated in §6.4.4 of [golub2013matrix]. -/
theorem finrank_inf_eq_card (h : finrank 𝕜 G ≤ finrank 𝕜 F) :
    finrank 𝕜 (F ⊓ G : Submodule 𝕜 E) =
      (Finset.univ.filter fun i : Fin (finrank 𝕜 G) => F.cosPrincipalAngle G i = 1).card := by
  obtain ⟨f, g, hfg⟩ := F.exists_isPrincipalVectors G h
  set s := Finset.univ.filter fun i : Fin (finrank 𝕜 G) => F.cosPrincipalAngle G i = 1
  have hrange : f '' {i | F.cosPrincipalAngle G i = 1} =
      Set.range (fun i : s => f i) := by
    ext x
    simp [s]
  rw [hfg.inf_eq_span, hrange]
  exact (finrank_span_eq_card (hfg.orthonormal_left.linearIndependent.comp _
    Subtype.val_injective)).trans (Fintype.card_coe s)

/-! ### The recursive definition -/

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space $E$, and let
$f, g \colon \{0, \dots, q-1\} \to E$. The pair $(f, g)$ satisfies the **recursive definition of
principal vectors** of (6.4.3) of [golub2013matrix] if $\dim G = q$, and for every $k$:
$f_k \in F$ and $g_k \in G$ are unit vectors, $f_k$ is orthogonal to $f_i$ and $g_k$ to $g_i$
for all $i < k$, and
$$\operatorname{Re} \langle u, v \rangle \le \operatorname{Re} \langle f_k, g_k \rangle$$
for all unit vectors $u \in F$ and $v \in G$ with $u \perp f_i$ and $v \perp g_i$ for all
$i < k$.

Any greedy choice of maximizers satisfies this definition. Whatever the choices, the values
$\operatorname{Re} \langle f_k, g_k \rangle$ are the cosines of the principal angles
(`Submodule.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors`). -/
structure IsRecursivePrincipalVectors {q : ℕ} (f g : Fin q → E) : Prop where
  /-- The number $q$ of vectors is the dimension of $G$. -/
  finrank_eq : finrank 𝕜 G = q
  /-- Every left vector $f_k$ lies in $F$. -/
  mem_left : ∀ k, f k ∈ F
  /-- Every right vector $g_k$ lies in $G$. -/
  mem_right : ∀ k, g k ∈ G
  /-- Every left vector is a unit vector: $\|f_k\| = 1$. -/
  norm_left : ∀ k, ‖f k‖ = 1
  /-- Every right vector is a unit vector: $\|g_k\| = 1$. -/
  norm_right : ∀ k, ‖g k‖ = 1
  /-- Each left vector is orthogonal to the earlier ones: $\langle f_i, f_k \rangle = 0$ for
  $i < k$. -/
  inner_left : ∀ k, ∀ i < k, inner 𝕜 (f i) (f k) = 0
  /-- Each right vector is orthogonal to the earlier ones: $\langle g_i, g_k \rangle = 0$ for
  $i < k$. -/
  inner_right : ∀ k, ∀ i < k, inner 𝕜 (g i) (g k) = 0
  /-- The pair $(f_k, g_k)$ is a maximizer: every pair of unit vectors $u \in F$ and $v \in G$ with
  $u \perp f_i$ and $v \perp g_i$ for all $i < k$ satisfies $\operatorname{Re} \langle u, v
  \rangle \le \operatorname{Re} \langle f_k, g_k \rangle$. -/
  re_inner_le : ∀ k, ∀ u ∈ F, ∀ v ∈ G, ‖u‖ = 1 → ‖v‖ = 1 → (∀ i < k, inner 𝕜 (f i) u = 0) →
    (∀ i < k, inner 𝕜 (g i) v = 0) → RCLike.re (inner 𝕜 u v) ≤ RCLike.re (inner 𝕜 (f k) (g k))

/-- The projection onto $F$ shrinks every vector of $G$ by at least the largest cosine:
$\|P_F v\| \le \cos \theta_0 \, \|v\|$ for every $v \in G$. -/
theorem norm_starProjection_le_cosPrincipalAngle_zero_mul {v : E} (hv : v ∈ G) :
    ‖F.starProjection v‖ ≤ F.cosPrincipalAngle G 0 * ‖v‖ := by
  have h := (F.orthogonalProjectionRestrict G).norm_apply_le_singularValues_zero_mul ⟨v, hv⟩
  rw [← Submodule.norm_coe, coe_orthogonalProjectionRestrict_apply] at h
  exact h

/-- **A maximizing pair is a singular pair.** Let $F$ and $G$ be finite-dimensional subspaces of an
inner product space, and let $u \in F$ and $v \in G$ be unit vectors with $\operatorname{Re}
\langle u, v \rangle = \cos \theta_0$. Then
$$P_F v = \cos \theta_0 \, u.$$

The proof is $\operatorname{Re} \langle u, v \rangle = \operatorname{Re} \langle u, P_F v
\rangle \le \|P_F v\| \le \cos \theta_0$, with the equality case of the Cauchy–Schwarz
inequality. -/
theorem starProjection_eq_of_re_inner_eq {u v : E} (hu : u ∈ F) (hv : v ∈ G) (hu1 : ‖u‖ = 1)
    (hv1 : ‖v‖ = 1) (h : RCLike.re (inner 𝕜 u v) = F.cosPrincipalAngle G 0) :
    F.starProjection v = (F.cosPrincipalAngle G 0 : 𝕜) • u := by
  set c := F.cosPrincipalAngle G 0
  have h1 : RCLike.re (inner 𝕜 u (F.starProjection v)) = c := by
    rw [← inner_starProjection_left_eq_right, starProjection_eq_self_iff.2 hu, h]
  have h2 : ‖F.starProjection v‖ ≤ c := by
    simpa [hv1] using F.norm_starProjection_le_cosPrincipalAngle_zero_mul G hv
  have h3 : c ≤ ‖F.starProjection v‖ := by
    have := re_inner_le_norm (𝕜 := 𝕜) u (F.starProjection v)
    rwa [hu1, one_mul, h1] at this
  have h4 : ‖F.starProjection v - (c : 𝕜) • u‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, inner_re_symm, h1, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg (F.cosPrincipalAngle_nonneg G 0), hu1,
      le_antisymm h2 h3]
    ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4))

namespace IsRecursivePrincipalVectors

variable {F G} {q : ℕ} {f g : Fin q → E}

omit [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] in
/-- The left vectors of a family that satisfies the recursive definition are nonzero. -/
theorem ne_zero_left (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) : f k ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [hfg.norm_left k]; exact one_ne_zero)

omit [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] in
/-- The right vectors of a family that satisfies the recursive definition are nonzero. -/
theorem ne_zero_right (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) : g k ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [hfg.norm_right k]; exact one_ne_zero)

/-- If $(f, g)$ satisfies the recursive definition, $\dim G \le \dim F$ and $q > 0$, then the first
stage of the recursion gives the unconstrained maximum: $\operatorname{Re} \langle f_0, g_0
\rangle = \cos \theta_0$. -/
theorem re_inner_zero (hfg : F.IsRecursivePrincipalVectors G f g)
    (h : finrank 𝕜 G ≤ finrank 𝕜 F) (hq : 0 < q) :
    RCLike.re (inner 𝕜 (f ⟨0, hq⟩) (g ⟨0, hq⟩)) = F.cosPrincipalAngle G 0 := by
  obtain ⟨f', g', hfg'⟩ := F.exists_isPrincipalVectors G h
  have hq' : 0 < finrank 𝕜 G := hfg.finrank_eq ▸ hq
  have hG := (hfg'.isGreatest_re_inner ⟨0, hq'⟩)
  refine le_antisymm (hG.2 ⟨_, hfg.mem_left _, _, hfg.mem_right _, hfg.norm_left _,
    hfg.norm_right _, fun i hi => absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _),
    fun i hi => absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _), rfl⟩) ?_
  obtain ⟨u, hu, v, hv, hu1, hv1, -, -, hr⟩ := hG.1
  rw [← hr]
  exact hfg.re_inner_le _ u hu v hv hu1 hv1
    (fun i hi => absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _))
    (fun i hi => absurd (show (i : ℕ) < 0 from hi) (Nat.not_lt_zero _))

end IsRecursivePrincipalVectors

/-- Let $K$ be a finite-dimensional subspace of an inner product space over $\mathbb{K}$, and let
$w \in K$ with $w \neq 0$. Then
$$\dim(K \cap (\mathbb{K} w)^\perp) + 1 = \dim K.$$
This is the case $K_1 = \mathbb{K} w$ of Mathlib's
`Submodule.finrank_add_inf_finrank_orthogonal`. -/
theorem finrank_inf_orthogonal_singleton_add_one (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
    {w : E} (hw : w ∈ K) (hw0 : w ≠ 0) :
    finrank 𝕜 (K ⊓ (𝕜 ∙ w)ᗮ : Submodule 𝕜 E) + 1 = finrank 𝕜 K := by
  have h := finrank_add_inf_finrank_orthogonal ((span_singleton_le_iff_mem w K).2 hw)
  rw [finrank_span_singleton hw0, inf_comm] at h
  omega

namespace IsRecursivePrincipalVectors

variable {F G} {q : ℕ} {f g : Fin (q + 1) → E}

omit [FiniteDimensional 𝕜 F] in
/-- If $(f, g)$, indexed by $\{0, \dots, q\}$, satisfies the recursive definition for $F$ and $G$,
then the shifted family $(f_{k+1}, g_{k+1})_{k < q}$ satisfies the recursive definition for the
subspaces $F \cap f_0^\perp$ and $G \cap g_0^\perp$. -/
theorem tail (hfg : F.IsRecursivePrincipalVectors G f g) :
    (F ⊓ (𝕜 ∙ f 0)ᗮ).IsRecursivePrincipalVectors (G ⊓ (𝕜 ∙ g 0)ᗮ) (f ∘ Fin.succ)
      (g ∘ Fin.succ) where
  finrank_eq := by
    have := finrank_inf_orthogonal_singleton_add_one G (hfg.mem_right 0) (hfg.ne_zero_right 0)
    rw [hfg.finrank_eq] at this
    omega
  mem_left k := ⟨hfg.mem_left _, (mem_orthogonal_singleton_iff_inner_right).2
    (hfg.inner_left _ 0 (Fin.succ_pos k))⟩
  mem_right k := ⟨hfg.mem_right _, (mem_orthogonal_singleton_iff_inner_right).2
    (hfg.inner_right _ 0 (Fin.succ_pos k))⟩
  norm_left k := hfg.norm_left _
  norm_right k := hfg.norm_right _
  inner_left k i hi := hfg.inner_left _ _ (Fin.succ_lt_succ_iff.2 hi)
  inner_right k i hi := hfg.inner_right _ _ (Fin.succ_lt_succ_iff.2 hi)
  re_inner_le k u hu v hv hu1 hv1 hfu hgv := by
    refine hfg.re_inner_le k.succ u hu.1 v hv.1 hu1 hv1 (fun i hi => ?_) (fun i hi => ?_)
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact (mem_orthogonal_singleton_iff_inner_right).1 hu.2
      · exact hfu j (Fin.succ_lt_succ_iff.1 hi)
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact (mem_orthogonal_singleton_iff_inner_right).1 hv.2
      · exact hgv j (Fin.succ_lt_succ_iff.1 hi)

/-- Let $(f, g)$, indexed by $\{0, \dots, q\}$, satisfy the recursive definition for $F$ and $G$,
and let $\dim G \le \dim F$. Let $F' = F \cap f_0^\perp$ and $G' = G \cap g_0^\perp$. Then for
every $k$,
$$\cos \theta_k(F', G') = \cos \theta_{k+1}(F, G).$$

On $G'$ the projection onto $F'$ is the projection onto $F$, and $P_F|_G$ restricted to $G'$ is
the deflation of $P_F|_G$ by its top singular pair $(g_0, f_0)$. -/
theorem cosPrincipalAngle_tail (hfg : F.IsRecursivePrincipalVectors G f g)
    (h : finrank 𝕜 G ≤ finrank 𝕜 F) (k : ℕ) :
    (F ⊓ (𝕜 ∙ f 0)ᗮ).cosPrincipalAngle (G ⊓ (𝕜 ∙ g 0)ᗮ) k = F.cosPrincipalAngle G (k + 1) := by
  set c := F.cosPrincipalAngle G 0 with hc
  have h0 := hfg.re_inner_zero h (Nat.succ_pos q)
  have hFg : F.starProjection (g 0) = (c : 𝕜) • f 0 :=
    F.starProjection_eq_of_re_inner_eq G (hfg.mem_left 0) (hfg.mem_right 0) (hfg.norm_left 0)
      (hfg.norm_right 0) h0
  have hGf : G.starProjection (f 0) = (c : 𝕜) • g 0 := by
    rw [hc, cosPrincipalAngle_comm]
    refine G.starProjection_eq_of_re_inner_eq F (hfg.mem_right 0) (hfg.mem_left 0)
      (hfg.norm_right 0) (hfg.norm_left 0) ?_
    rw [inner_re_symm, ← cosPrincipalAngle_comm]
    exact h0
  set F' := F ⊓ (𝕜 ∙ f 0)ᗮ
  set G' := G ⊓ (𝕜 ∙ g 0)ᗮ
  set T := F.orthogonalProjectionRestrict G
  let e : G' →ₗᵢ[𝕜] G := inclusionₗᵢ inf_le_left
  let ι : F' →ₗᵢ[𝕜] F := inclusionₗᵢ inf_le_left
  -- on `G'`, the projections onto `F'` and `F` agree
  have hproj : ∀ x ∈ G', F'.starProjection x = F.starProjection x := by
    intro x hx
    refine eq_starProjection_of_mem_of_inner_eq_zero ⟨F.starProjection_apply_mem x, ?_⟩
      fun w hw => (F.mem_orthogonal _).1 (F.sub_starProjection_mem_orthogonal x) w hw.1 |>
        fun h' => by rw [← inner_conj_symm, h', map_zero]
    refine (mem_orthogonal_singleton_iff_inner_right).2 ?_
    rw [← inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.2 (hfg.mem_left 0), ← starProjection_eq_self_iff.2 hx.1,
      ← inner_starProjection_left_eq_right, hGf, inner_smul_left,
      (mem_orthogonal_singleton_iff_inner_right).1 hx.2, mul_zero]
  have hcomp : ι.toLinearMap ∘ₗ F'.orthogonalProjectionRestrict G' = T ∘ₗ e.toLinearMap := by
    ext x
    simp only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
    change (F'.orthogonalProjectionRestrict G' x : E) = (T (e x) : E)
    rw [coe_orthogonalProjectionRestrict_apply, coe_orthogonalProjectionRestrict_apply]
    exact hproj x x.2
  have hr : finrank 𝕜 G' + 1 = finrank 𝕜 G :=
    finrank_inf_orthogonal_singleton_add_one G (hfg.mem_right 0) (hfg.ne_zero_right 0)
  have hTv : T ⟨g 0, hfg.mem_right 0⟩ = (T.singularValues 0 : 𝕜) • ⟨f 0, hfg.mem_left 0⟩ :=
    Subtype.ext (by rw [coe_orthogonalProjectionRestrict_apply, Submodule.coe_smul]; exact hFg)
  have hTu : LinearMap.adjoint T ⟨f 0, hfg.mem_left 0⟩ =
      (T.singularValues 0 : 𝕜) • ⟨g 0, hfg.mem_right 0⟩ := by
    rw [orthogonalProjectionRestrict_adjoint]
    exact Subtype.ext (by
      rw [coe_orthogonalProjectionRestrict_apply, Submodule.coe_smul]; exact hGf)
  have hdefl := T.singularValues_comp_linearIsometry_eq_succ e hr
    (by simpa using hfg.norm_left 0) (by simpa using hfg.norm_right 0) hTv hTu
    (fun x => by
      change inner 𝕜 (g 0) (x : E) = 0
      exact (mem_orthogonal_singleton_iff_inner_right).1 x.2.2) k
  rw [← hcomp, LinearMap.singularValues_linearIsometry_comp] at hdefl
  exact hdefl

end IsRecursivePrincipalVectors

/-- The recursive definition gives $\operatorname{Re} \langle f_k, g_k \rangle = \cos \theta_k$ at
every stage $k$, by induction on $k$. -/
private theorem re_inner_eq_cosPrincipalAngle_aux (k : ℕ) :
    ∀ (F G : Submodule 𝕜 E) [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] (q : ℕ)
      (f g : Fin q → E), finrank 𝕜 G ≤ finrank 𝕜 F → F.IsRecursivePrincipalVectors G f g →
      ∀ hk : k < q, RCLike.re (inner 𝕜 (f ⟨k, hk⟩) (g ⟨k, hk⟩)) = F.cosPrincipalAngle G k := by
  induction k with
  | zero => exact fun F G _ _ q f g h hfg hk => hfg.re_inner_zero h hk
  | succ k ih =>
    intro F G _ _ q f g h hfg hk
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hF := finrank_inf_orthogonal_singleton_add_one F (hfg.mem_left 0) (hfg.ne_zero_left 0)
    have hG := finrank_inf_orthogonal_singleton_add_one G (hfg.mem_right 0) (hfg.ne_zero_right 0)
    have := ih (F ⊓ (𝕜 ∙ f 0)ᗮ) (G ⊓ (𝕜 ∙ g 0)ᗮ) q (f ∘ Fin.succ) (g ∘ Fin.succ) (by omega)
      hfg.tail (by omega)
    rw [hfg.cosPrincipalAngle_tail h] at this
    exact this

/-- **The recursive definition of the principal angles is well posed.** Let $F$ and $G$ be
finite-dimensional subspaces of an inner product space with $\dim G \le \dim F$, and let
$(f, g)$, indexed by $\{0, \dots, q-1\}$, satisfy the recursive definition of principal vectors.
Then for every $k < q$,
$$\operatorname{Re} \langle f_k, g_k \rangle = \cos \theta_k,$$
whichever maximizers were chosen. In (6.4.3) of [golub2013matrix] the angles "are defined
recursively".

The proof is by induction on $k$. A maximizing first pair is a top singular pair of $P_F|_G$.
The problem on the orthogonal complements of the first pair is the same problem for the deflated
map, whose singular values are the later ones
(`LinearMap.singularValues_comp_linearIsometry_eq_succ`). -/
theorem cosPrincipalAngle_eq_of_isRecursivePrincipalVectors (h : finrank 𝕜 G ≤ finrank 𝕜 F)
    {q : ℕ} {f g : Fin q → E} (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) :
    RCLike.re (inner 𝕜 (f k) (g k)) = F.cosPrincipalAngle G k :=
  re_inner_eq_cosPrincipalAngle_aux k F G q f g h hfg k.2

/-! ### The gap, lines, and matrices -/

/-- **The distance between subspaces of equal dimension is the sine of the largest principal
angle.** Let $F$ and $G$ be finite-dimensional subspaces of an inner product space with
$\dim F = \dim G = q + 1$. Then
$$\operatorname{gap}(F, G) = \sin \theta_q.$$
In [golub2013matrix], §6.4.3, this is the statement that for $p = q$, $\operatorname{dist}(F,
G) = \sqrt{1 - \cos^2 \theta_p} = \sin \theta_p$, with indices from $1$.

The gap is `Submodule.gap`, $\|P_F - P_G\|$. For equal dimensions it is the one-sided gap
$\|P_{F^\perp} P_G\|$, whose square is $1 - \sigma_q(P_F|_G)^2$. -/
theorem gap_eq_sin_principalAngle {q : ℕ} (hF : finrank 𝕜 F = q + 1)
    (hG : finrank 𝕜 G = q + 1) : F.gap G = Real.sin (F.principalAngle G q) := by
  have h := G.norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues F (by omega)
  rw [← G.gap_eq_norm_orthogonal_mul_of_finrank_eq F (hG.trans hF.symm), gap_comm, hG,
    Nat.add_sub_cancel] at h
  rw [principalAngle, Real.sin_arccos, cosPrincipalAngle, ← h,
    Real.sqrt_sq (F.gap_nonneg G)]

/-- **A principal angle with a line is the angle with a vector.** Let $F$ be a finite-dimensional
subspace of an inner product space over $\mathbb{K}$, and let $u \neq 0$. Then
$$\cos \theta_0(F, \mathbb{K} u) = \frac{\|P_F u\|}{\|u\|},$$
which is `Submodule.cosAngle`. This is the case $q = 1$ of §6.4.3 of [golub2013matrix].

On a line, $P_F$ stretches every vector by the same factor. -/
theorem cosPrincipalAngle_span_singleton_zero {u : E} (hu : u ≠ 0) :
    F.cosPrincipalAngle (𝕜 ∙ u) 0 = F.cosAngle u := by
  have hr : finrank 𝕜 (𝕜 ∙ u) = 1 := finrank_span_singleton hu
  have hstretch : ∀ x ∈ (⊤ : Submodule 𝕜 (𝕜 ∙ u)),
      ‖F.orthogonalProjectionRestrict (𝕜 ∙ u) x‖ = F.cosAngle u * ‖x‖ := by
    rintro ⟨x, hx⟩ -
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hx
    rw [← Submodule.norm_coe, coe_orthogonalProjectionRestrict_apply, ← Submodule.norm_coe,
      map_smul, norm_smul, norm_smul, cosAngle, div_mul_eq_mul_div,
      eq_div_iff (norm_ne_zero_iff.2 hu)]
    ring
  apply le_antisymm
  · exact LinearMap.singularValues_le_of_norm_le_mul _ (by omega) (S := ⊤) (by simp [hr])
      fun x hx => (hstretch x hx).le
  · exact LinearMap.le_singularValues_of_mul_norm_le _ (S := ⊤) (by simp [hr])
      fun x hx => (hstretch x hx).ge

/-- Let $F$ be a finite-dimensional subspace of an inner product space over $\mathbb{K}$, and let
$u \neq 0$. Then the first principal angle $\theta_0(F, \mathbb{K} u)$ is the angle
`Submodule.angle` between $u$ and $F$. -/
theorem principalAngle_span_singleton_zero {u : E} (hu : u ≠ 0) :
    F.principalAngle (𝕜 ∙ u) 0 = F.angle u := by
  rw [principalAngle, cosPrincipalAngle_span_singleton_zero F hu, angle]

open Matrix in
/-- **The matrix form of the cosines.** Let $Q_A \in \mathbb{K}^{m \times p}$ and
$Q_B \in \mathbb{K}^{m \times q}$ have orthonormal columns, $Q_A^H Q_A = I$ and $Q_B^H Q_B = I$.
Then the cosines of the principal angles between their ranges are the singular values of
$Q_A^H Q_B$:
$$\cos \theta_i(\operatorname{ran} Q_A, \operatorname{ran} Q_B) = \sigma_i(Q_A^H Q_B) \quad
  \text{for every } i.$$
In [golub2013matrix], §6.4.3, this is the statement $\sigma_i = \cos \theta_i$ for the SVD of
$Q_A^H Q_B$.

The ranges are those of `Matrix.toEuclideanLin`, and the singular values are those of
`Matrix.toEuclideanLin (QAᴴ * QB)`, indexed from $0$. The two matrices are isometries onto their
ranges, and $Q_A (Q_A^H Q_B) y = P_F (Q_B y)$, so $Q_A^H Q_B$ is $P_F|_G$ up to isometries on
both sides. -/
theorem cosPrincipalAngle_eq_singularValues {m p q : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] {QA : Matrix m p 𝕜}
    {QB : Matrix m q 𝕜} (hA : QAᴴ * QA = 1) (hB : QBᴴ * QB = 1) (i : ℕ) :
    (LinearMap.range (toEuclideanLin QA)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin QB)) i = (toEuclideanLin (QAᴴ * QB)).singularValues i := by
  classical
  set F := LinearMap.range (toEuclideanLin QA)
  set G := LinearMap.range (toEuclideanLin QB)
  let eA : EuclideanSpace 𝕜 p ≃ₗᵢ[𝕜] F := (toEuclideanLinearIsometry hA).equivRange
  let eB : EuclideanSpace 𝕜 q ≃ₗᵢ[𝕜] G := (toEuclideanLinearIsometry hB).equivRange
  have hAA : ∀ z, toEuclideanLin QAᴴ (toEuclideanLin QA z) = z := fun z => by
    rw [← toEuclideanLin_mul_apply, hA, toEuclideanLin_one, LinearMap.id_apply]
  have key : eA.toLinearIsometry.toLinearMap ∘ₗ toEuclideanLin (QAᴴ * QB) =
      F.orthogonalProjectionRestrict G ∘ₗ eB.toLinearIsometry.toLinearMap := by
    ext y : 1
    refine Subtype.ext ?_
    change toEuclideanLin QA (toEuclideanLin (QAᴴ * QB) y) = F.starProjection (toEuclideanLin QB y)
    rw [toEuclideanLin_mul_apply]
    symm
    refine eq_starProjection_of_mem_of_inner_eq_zero ⟨_, rfl⟩ ?_
    rintro _ ⟨w, rfl⟩
    rw [← toEuclideanLin_conjTranspose_inner_left, map_sub, hAA, sub_self, inner_zero_left]
  have h1 := LinearMap.singularValues_linearIsometry_comp (toEuclideanLin (QAᴴ * QB))
    eA.toLinearIsometry
  have h2 := (F.orthogonalProjectionRestrict G).singularValues_comp_linearIsometryEquiv eB
    (LinearIsometry.id)
  rw [key] at h1
  rw [cosPrincipalAngle, ← h1, ← h2]
  rfl

open Matrix in
/-- **The cosines from any SVD.** Let $Q_A \in \mathbb{K}^{m \times p}$ and
$Q_B \in \mathbb{K}^{m \times q}$ have orthonormal columns, and let $Q_A^H Q_B = Y \Sigma Z^H$
be a singular value decomposition with $\Sigma = \operatorname{diag}(\sigma_0, \sigma_1,
\dots)$. Then for every $k < \min\{p, q\}$,
$$\cos \theta_k(\operatorname{ran} Q_A, \operatorname{ran} Q_B) = \sigma_k.$$
This is part of §6.4.3 and Algorithm 6.4.3 of [golub2013matrix].

The SVD is `Matrix.IsSVD`. The diagonal of every SVD lists the sorted singular values
(`Matrix.IsSVD.singularValues_eq`), which are the cosines
(`Submodule.cosPrincipalAngle_eq_singularValues`). -/
theorem cosPrincipalAngle_eq_of_isSVD {m : Type*} [Fintype m] {p q : ℕ}
    {QA : Matrix m (Fin p) 𝕜} {QB : Matrix m (Fin q) 𝕜} (hA : QAᴴ * QA = 1) (hB : QBᴴ * QB = 1)
    {Y : Matrix (Fin p) (Fin p) 𝕜} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) 𝕜}
    (h : IsSVD (QAᴴ * QB) Y σ Z) {k : ℕ} (hkp : k < p) (hkq : k < q) :
    (LinearMap.range (toEuclideanLin QA)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin QB)) k = σ k := by
  rw [cosPrincipalAngle_eq_singularValues hA hB, h.singularValues_eq hkp hkq]

open Matrix in
/-- **Principal vectors from any SVD.** Let $Q_A \in \mathbb{K}^{m \times p}$ and
$Q_B \in \mathbb{K}^{m \times q}$ have orthonormal columns with $q \le p$, and let
$Q_A^H Q_B = Y \Sigma Z^H$ be a singular value decomposition. Then the columns of
$Q_A Y(:, 1{:}q)$ and the columns of $Q_B Z$ form a family of principal vectors of
$\operatorname{ran} Q_A$ and $\operatorname{ran} Q_B$. This is part of §6.4.3 and Algorithm
6.4.3 of [golub2013matrix].

The first $q$ columns of $Y$ are `Matrix.firstColumns Y hqp`, and the columns are read as
vectors of `EuclideanSpace` with `WithLp.toLp 2`. The projection onto $\operatorname{ran} Q_A$
is $Q_A Q_A^H$, so $P (Q_B z_j) = Q_A Y \Sigma Z^H z_j = \sigma_j Q_A y_j$, and
$\sigma_j = \cos \theta_j$ (`Submodule.cosPrincipalAngle_eq_of_isSVD`). -/
theorem isPrincipalVectors_of_isSVD {m : Type*} [Fintype m] {p q : ℕ}
    {QA : Matrix m (Fin p) 𝕜} {QB : Matrix m (Fin q) 𝕜} (hA : QAᴴ * QA = 1) (hB : QBᴴ * QB = 1)
    (hqp : q ≤ p) {Y : Matrix (Fin p) (Fin p) 𝕜} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) 𝕜}
    (h : IsSVD (QAᴴ * QB) Y σ Z) :
    (LinearMap.range (toEuclideanLin QA)).IsPrincipalVectors (LinearMap.range (toEuclideanLin QB))
      (fun k => WithLp.toLp 2 ((QA * firstColumns Y hqp).col k))
      (fun k => WithLp.toLp 2 ((QB * Z).col k)) := by
  classical
  have hYY : Yᴴ * Y = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
  have hZZ : Zᴴ * Z = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  have hcol : ∀ {k l : ℕ} (N : Matrix m (Fin k) 𝕜) (N' : Matrix (Fin k) (Fin l) 𝕜) (j : Fin l),
      (WithLp.toLp 2 ((N * N').col j) : EuclideanSpace 𝕜 m) =
        toEuclideanLin N (WithLp.toLp 2 (N'.col j)) := fun N N' j => by
    rw [toEuclideanLin_toLp]
    congr 1
  refine ⟨?_, ?_, ?_, fun k => ?_, fun k => ?_, fun j => ?_⟩
  · rw [finrank_range_of_conjTranspose_mul_self_eq_one hB, Fintype.card_fin]
  · refine conjTranspose_mul_self_eq_one_iff_orthonormal.1 ?_
    have hY₁ : (firstColumns Y hqp)ᴴ * firstColumns Y hqp = 1 := by
      rw [firstColumns, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        hYY]
      exact submatrix_one _ (Fin.castLE_injective hqp)
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc QAᴴ, hA, Matrix.one_mul, hY₁]
  · refine conjTranspose_mul_self_eq_one_iff_orthonormal.1 ?_
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc QBᴴ, hB, Matrix.one_mul, hZZ]
  · rw [hcol]
    exact ⟨_, rfl⟩
  · rw [hcol]
    exact ⟨_, rfl⟩
  have hP : ∀ x, (LinearMap.range (toEuclideanLin QA)).starProjection x =
      toEuclideanLin (QA * QAᴴ) x := fun x => by
    rw [toEuclideanLin_mul_conjTranspose_eq_starProjection hA]
    rfl
  rw [cosPrincipalAngle_eq_of_isSVD hA hB h (j.2.trans_le hqp) j.2, hP, hcol, hcol,
    ← toEuclideanLin_mul_apply, toEuclideanLin_toLp, toEuclideanLin_toLp]
  have hZj : Zᴴ *ᵥ Z.col j = Pi.single j 1 := by
    funext i
    have := congrFun (congrFun hZZ i) j
    rw [Matrix.mul_apply] at this
    rw [Pi.single_apply, ← Matrix.one_apply, ← this]
    rfl
  have hSig : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin p) (Fin q) 𝕜) *ᵥ
      Pi.single j 1 = (σ j : 𝕜) • Pi.single (Fin.castLE hqp j) 1 := by
    rw [mulVec_single_one]
    funext i
    simp only [col_apply, rectDiagonal_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hij : (i : ℕ) = j
    · have : i = Fin.castLE hqp j := Fin.ext hij
      rw [ite_eq_left hij, ite_eq_left this, hij, mul_one]
    · have : i ≠ Fin.castLE hqp j := fun e => hij (by rw [e]; rfl)
      rw [ite_eq_right hij, ite_eq_right this, mul_zero]
  have e : (QA * QAᴴ * QB) *ᵥ Z.col j = (σ j : 𝕜) • (QA *ᵥ (firstColumns Y hqp).col j) := by
    rw [Matrix.mul_assoc, h.eq_mul_mul_star, star_eq_conjTranspose]
    simp only [← mulVec_mulVec]
    rw [hZj, hSig, mulVec_smul, mulVec_smul, mulVec_single_one]
    rfl
  rw [e, WithLp.toLp_smul]

end Submodule
