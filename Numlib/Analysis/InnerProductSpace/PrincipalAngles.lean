import Numlib.Analysis.InnerProductSpace.Orthonormal
import Numlib.Analysis.InnerProductSpace.Projection.Gap
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Principal angles between subspaces

Principal angles and principal vectors between two finite-dimensional subspaces `F`, `G` of an
inner product space ([golub2013matrix] §6.4.3–6.4.4, after Björck–Golub 1973; Jordan 1875). The
cosines of the angles are the singular values of the restricted projection
`Submodule.orthogonalProjectionRestrict F G : G →ₗ[𝕜] F`, `x ↦ P_F x`, and the principal vectors
are its singular vectors. The book's recursive max–max definition is a theorem here, the
intersection `F ⊓ G` is spanned by the principal vectors of angle `0`, and for subspaces of equal
dimension the gap `‖P_F - P_G‖` is the sine of the largest angle.

## Main definitions

* `Submodule.cosPrincipalAngle F G i`: the `i`-th cosine, `σ_i(P_F|_G)` (Mathlib's sorted and
  zero-padded `LinearMap.singularValues`), and `Submodule.principalAngle F G i`, its `arccos`. Index
  `i` is the book's `θ_{i+1}`; for `i ≥ finrank G` the cosine is `0` and the angle `π / 2`.
* `Submodule.IsPrincipalVectors F G f g`: `g` an orthonormal basis of `G`, `f` orthonormal in `F`,
  and `P_F (g j) = cos θ_j • f j`.
* `Submodule.IsRecursivePrincipalVectors F G f g`: the book's recursive definition, a greedy
  sequence of maximizers of `re ⟪u, v⟫` over unit vectors orthogonal to the earlier ones.

## Main results

* `Submodule.cosPrincipalAngle_nonneg`, `Submodule.cosPrincipalAngle_le_one`,
  `Submodule.antitone_cosPrincipalAngle`, `Submodule.monotone_principalAngle`,
  `Submodule.principalAngle_mem_Icc`: `0 ≤ θ₁ ≤ ⋯ ≤ θ_q ≤ π / 2`.
* `Submodule.cosPrincipalAngle_comm`: principal angles are symmetric.
* `Submodule.exists_isPrincipalVectors`: principal vectors exist when `finrank G ≤ finrank F`.
* `Submodule.IsPrincipalVectors.isGreatest_re_inner`: the max–max characterization.
* `Submodule.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors`: every greedy choice of
  maximizers produces the principal angles, so the book's recursive definition is well posed.
* `Submodule.IsPrincipalVectors.inf_eq_span`, `Submodule.finrank_inf_eq_card`: the intersection
  ([golub2013matrix] Theorem 6.4.2).
* `Submodule.cosPrincipalAngle_eq_singularValues`: the matrix bridge — for matrices `Q_A`, `Q_B`
  with orthonormal columns, the cosines are the singular values of `Q_Aᴴ Q_B`.
* `Submodule.cosPrincipalAngle_eq_of_isSVD`, `Submodule.isPrincipalVectors_of_isSVD`: from any SVD
  `Q_Aᴴ Q_B = Y Σ Zᴴ`, the diagonal of `Σ` lists the cosines and the columns of `Q_A Y(:, 1:q)`,
  `Q_B Z` are principal vectors (the SVD step of [golub2013matrix] Algorithm 6.4.3).
* `Submodule.gap_eq_sin_principalAngle`: `dist(F, G) = sin θ_max` for equal dimensions.
* `Submodule.cosPrincipalAngle_span_singleton_zero`: the angle with a line is the angle of
  `Submodule.cosAngle`.

## Implementation notes

The definition is by singular values, not by recursion: the recursion is then a characterization,
proved by deflation (`LinearMap.singularValues_comp_linearIsometry_eq_succ`). Nothing needs
completeness or finite dimension of the ambient space, only of `F` and `G`. The distance of
[golub2013matrix] §2.5.3 is `Submodule.gap` of `Numlib.Analysis.InnerProductSpace.Projection.Gap`,
whose equal-dimension theory gives `gap_eq_sin_principalAngle` without coordinates.
-/

open Module

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (F G : Submodule 𝕜 E) [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]

/-- **The cosines of the principal angles** between `F` and `G` ([golub2013matrix] (6.4.3),
`cos θ_{i+1}`): the singular values of the restricted projection `P_F|_G : G → F`, sorted
decreasingly and `0` from `finrank G` on. -/
noncomputable def cosPrincipalAngle (i : ℕ) : ℝ :=
  (F.orthogonalProjectionRestrict G).singularValues i

/-- **The principal angles** between `F` and `G` ([golub2013matrix] (6.4.3), `θ_{i+1}`):
`arccos` of the cosines. -/
noncomputable def principalAngle (i : ℕ) : ℝ :=
  Real.arccos (F.cosPrincipalAngle G i)

/-- The cosines of the principal angles are nonnegative. -/
theorem cosPrincipalAngle_nonneg (i : ℕ) : 0 ≤ F.cosPrincipalAngle G i :=
  LinearMap.singularValues_nonneg _ i

/-- The cosines of the principal angles are at most `1` ([golub2013matrix] §6.4.3: the singular
values of `Q_Aᵀ Q_B` lie in `[0, 1]`): an orthogonal projection does not lengthen vectors. -/
theorem cosPrincipalAngle_le_one (i : ℕ) : F.cosPrincipalAngle G i ≤ 1 :=
  LinearMap.singularValues_le_of_forall_norm_apply_le _ zero_le_one (fun x => by
    rw [← Submodule.norm_coe, coe_orthogonalProjectionRestrict_apply, one_mul,
      ← Submodule.norm_coe x]
    exact F.norm_starProjection_apply_le x) i

/-- The cosines decrease. -/
theorem antitone_cosPrincipalAngle : Antitone (F.cosPrincipalAngle G) :=
  LinearMap.singularValues_antitone _

/-- **`θ₁ ≤ ⋯ ≤ θ_q`** ([golub2013matrix] §6.4.3): the principal angles increase. -/
theorem monotone_principalAngle : Monotone (F.principalAngle G) :=
  fun _ _ hij => Real.antitone_arccos (F.antitone_cosPrincipalAngle G hij)

/-- **`0 ≤ θ_i ≤ π / 2`** ([golub2013matrix] §6.4.3). -/
theorem principalAngle_mem_Icc (i : ℕ) : F.principalAngle G i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.2 (F.cosPrincipalAngle_nonneg G i)⟩

/-- **Principal angles are symmetric**: `P_G|_F` is the adjoint of `P_F|_G`, and a map and its
adjoint have the same singular values. -/
theorem cosPrincipalAngle_comm : F.cosPrincipalAngle G = G.cosPrincipalAngle F := by
  funext i
  rw [cosPrincipalAngle, cosPrincipalAngle, ← orthogonalProjectionRestrict_adjoint,
    LinearMap.singularValues_adjoint]

/-! ### Principal vectors -/

/-- **Principal vectors** ([golub2013matrix] (6.4.3)–(6.4.5), `{f_i, g_i}`): `g` is an orthonormal
basis of `G` (of dimension `q`), `f` is an orthonormal family in `F`, and
`P_F (g j) = cos θ_j • f j`. So `g` consists of right and `f` of left singular vectors of
`P_F|_G`, the latter completed arbitrarily where the cosine vanishes. -/
structure IsPrincipalVectors {q : ℕ} (f g : Fin q → E) : Prop where
  finrank_eq : finrank 𝕜 G = q
  orthonormal_left : Orthonormal 𝕜 f
  orthonormal_right : Orthonormal 𝕜 g
  mem_left : ∀ i, f i ∈ F
  mem_right : ∀ i, g i ∈ G
  starProjection_right : ∀ j, F.starProjection (g j) = (F.cosPrincipalAngle G j : 𝕜) • f j

/-- **Principal vectors exist** when `finrank G ≤ finrank F` ([golub2013matrix] §6.4.3, `p ≥ q`):
the singular value decomposition `LinearMap.exists_orthonormal_singularVectors` of `P_F|_G`. -/
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

/-- `⟪f i, g j⟫ = cos θ_j` if `i = j` and `0` otherwise ([golub2013matrix] (6.4.3),
`cos θ_k = f_kᵀ g_k`): `⟪f i, g j⟫ = ⟪f i, P_F g j⟫ = cos θ_j ⟪f i, f j⟫`. -/
theorem inner_eq (h : F.IsPrincipalVectors G f g) (i j : Fin q) :
    inner 𝕜 (f i) (g j) = if i = j then (F.cosPrincipalAngle G j : 𝕜) else 0 := by
  rw [← starProjection_eq_self_iff.2 (h.mem_left i), inner_starProjection_left_eq_right,
    h.starProjection_right, inner_smul_right, orthonormal_iff_ite.1 h.orthonormal_left i j]
  split_ifs <;> simp

/-- The principal vectors `g` expand every vector of `G`. -/
theorem sum_inner_smul_right (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ∑ j, inner 𝕜 (g j) v • g j = v := by
  have hon : Orthonormal 𝕜 (fun j => (⟨g j, h.mem_right j⟩ : G)) :=
    (h.orthonormal_right.codRestrict G h.mem_right)
  have hsp : ⊤ ≤ span 𝕜 (Set.range fun j => (⟨g j, h.mem_right j⟩ : G)) :=
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [h.finrank_eq])).ge
  have := congrArg Subtype.val ((OrthonormalBasis.mk hon hsp).sum_repr' ⟨v, hv⟩)
  simpa [OrthonormalBasis.coe_mk, Submodule.coe_inner] using this

/-- The projection onto `F` of a vector of `G`, in principal coordinates. -/
theorem starProjection_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    F.starProjection v = ∑ j, (inner 𝕜 (g j) v * F.cosPrincipalAngle G j) • f j := by
  conv_lhs => rw [← h.sum_inner_smul_right hv]
  simp_rw [map_sum, map_smul, h.starProjection_right, smul_smul]

/-- Parseval in `G`. -/
theorem norm_sq_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ‖v‖ ^ 2 = ∑ j, ‖inner 𝕜 (g j) v‖ ^ 2 := by
  conv_lhs => rw [← h.sum_inner_smul_right hv]
  exact h.orthonormal_right.norm_sum_smul_sq _

/-- The squared norm of the projection onto `F` of a vector of `G`, in principal coordinates. -/
theorem norm_starProjection_sq_eq_sum (h : F.IsPrincipalVectors G f g) {v : E} (hv : v ∈ G) :
    ‖F.starProjection v‖ ^ 2 = ∑ j, ‖inner 𝕜 (g j) v‖ ^ 2 * F.cosPrincipalAngle G j ^ 2 := by
  rw [h.starProjection_eq_sum hv, h.orthonormal_left.norm_sum_smul_sq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (F.cosPrincipalAngle_nonneg G j), mul_pow]

/-- On the vectors of `G` orthogonal to `g i` for `i < k`, the projection onto `F` shrinks by at
least `cos θ_k`. -/
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

/-- **The max–max characterization** ([golub2013matrix] (6.4.3), and the argument (6.4.6) after
it): `cos θ_k` is the largest value of `re ⟪u, v⟫` over unit vectors `u ∈ F`, `v ∈ G` orthogonal to
`f i`, resp. `g i`, for `i < k`, attained at `(f k, g k)`. Only the constraint on `v` matters:
`re ⟪u, v⟫ ≤ ‖P_F v‖ ≤ cos θ_k`. -/
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

/-- If `cos θ_i = 1` then `f i = g i` ([golub2013matrix] Theorem 6.4.2, proof): unit vectors with
inner product `1` coincide. -/
theorem eq_of_cosPrincipalAngle_eq_one (h : F.IsPrincipalVectors G f g) {i : Fin q}
    (hi : F.cosPrincipalAngle G i = 1) : f i = g i := by
  rw [← inner_eq_one_iff_of_norm_eq_one (𝕜 := 𝕜) (h.orthonormal_left.1 i)
    (h.orthonormal_right.1 i), h.inner_eq, ite_eq_left rfl, hi, RCLike.ofReal_one]

/-- **The intersection of two subspaces** ([golub2013matrix] Theorem 6.4.2): `F ⊓ G` is spanned by
the principal vectors of angle `0`. The book's proof gives `⊇`; for `⊆`, a vector of `F ⊓ G` has
`‖P_F v‖ = ‖v‖`, which in principal coordinates forces every coordinate with `cos θ_j < 1` to
vanish. -/
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

/-- **The dimension of the intersection** ([golub2013matrix] §6.4.4): when
`finrank G ≤ finrank F`, `finrank (F ⊓ G)` is the number of principal angles equal to `0`. -/
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

/-- **The book's recursive definition of principal vectors** ([golub2013matrix] (6.4.3)): unit
vectors `f k ∈ F`, `g k ∈ G`, orthogonal to the earlier `f i`, resp. `g i`, such that
`re ⟪f k, g k⟫` is the largest value of `re ⟪u, v⟫` over unit `u ∈ F`, `v ∈ G` orthogonal to the
earlier ones. Any greedy choice of maximizers satisfies it; the values `re ⟪f k, g k⟫` are the
cosines of the principal angles whatever the choices
(`Submodule.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors`). -/
structure IsRecursivePrincipalVectors {q : ℕ} (f g : Fin q → E) : Prop where
  finrank_eq : finrank 𝕜 G = q
  mem_left : ∀ k, f k ∈ F
  mem_right : ∀ k, g k ∈ G
  norm_left : ∀ k, ‖f k‖ = 1
  norm_right : ∀ k, ‖g k‖ = 1
  inner_left : ∀ k, ∀ i < k, inner 𝕜 (f i) (f k) = 0
  inner_right : ∀ k, ∀ i < k, inner 𝕜 (g i) (g k) = 0
  re_inner_le : ∀ k, ∀ u ∈ F, ∀ v ∈ G, ‖u‖ = 1 → ‖v‖ = 1 → (∀ i < k, inner 𝕜 (f i) u = 0) →
    (∀ i < k, inner 𝕜 (g i) v = 0) → RCLike.re (inner 𝕜 u v) ≤ RCLike.re (inner 𝕜 (f k) (g k))

/-- `P_F` shrinks by at least `cos θ₁`, the largest cosine. -/
theorem norm_starProjection_le_cosPrincipalAngle_zero_mul {v : E} (hv : v ∈ G) :
    ‖F.starProjection v‖ ≤ F.cosPrincipalAngle G 0 * ‖v‖ := by
  have h := (F.orthogonalProjectionRestrict G).norm_apply_le_singularValues_zero_mul ⟨v, hv⟩
  rw [← Submodule.norm_coe, coe_orthogonalProjectionRestrict_apply] at h
  exact h

/-- **A maximizing pair is a singular pair**: if unit vectors `u ∈ F`, `v ∈ G` have
`re ⟪u, v⟫ = cos θ₁`, then `P_F v = cos θ₁ • u`: `re ⟪u, v⟫ = re ⟪u, P_F v⟫ ≤ ‖P_F v‖ ≤ cos θ₁`, and
equality in Cauchy–Schwarz. -/
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
/-- The left vectors are nonzero. -/
theorem ne_zero_left (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) : f k ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [hfg.norm_left k]; exact one_ne_zero)

omit [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] in
/-- The right vectors are nonzero. -/
theorem ne_zero_right (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) : g k ≠ 0 :=
  norm_ne_zero_iff.1 (by rw [hfg.norm_right k]; exact one_ne_zero)

/-- The first stage of the recursion: `re ⟪f 0, g 0⟫ = cos θ₁`, the unconstrained maximum. -/
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

/-- Removing a nonzero vector of a finite-dimensional subspace lowers its dimension by one: the
case `K₁ = 𝕜 ∙ w` of Mathlib's `Submodule.finrank_add_inf_finrank_orthogonal`. -/
theorem finrank_inf_orthogonal_singleton_add_one (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
    {w : E} (hw : w ∈ K) (hw0 : w ≠ 0) :
    finrank 𝕜 (K ⊓ (𝕜 ∙ w)ᗮ : Submodule 𝕜 E) + 1 = finrank 𝕜 K := by
  have h := finrank_add_inf_finrank_orthogonal ((span_singleton_le_iff_mem w K).2 hw)
  rw [finrank_span_singleton hw0, inf_comm] at h
  omega

/-- The subspace inclusion `K ≤ L` as a linear isometry. -/
def inclusionₗᵢ {K L : Submodule 𝕜 E} (h : K ≤ L) : K →ₗᵢ[𝕜] L where
  toLinearMap := Submodule.inclusion h
  norm_map' _ := rfl

namespace IsRecursivePrincipalVectors

variable {F G} {q : ℕ} {f g : Fin (q + 1) → E}

omit [FiniteDimensional 𝕜 F] in
/-- The recursion shifted by one: the later vectors are recursive principal vectors of the
subspaces orthogonal to the first pair. -/
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

/-- The cosines of the subspaces orthogonal to a maximizing first pair are the later cosines:
`cos θ_{k+1}(F', G') = cos θ_{k+2}(F, G)`. On `G' = G ⊓ (g 0)ᗮ` the projection onto
`F' = F ⊓ (f 0)ᗮ` is the projection onto `F`, and `P_F|_G` restricted to `G'` is the deflation of
`P_F|_G` by its top singular pair `(g 0, f 0)`. -/
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

/-- The recursion, by induction on the stage. -/
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

/-- **The recursive definition of the principal angles is well posed** ([golub2013matrix] (6.4.3):
the angles "are defined recursively"): if `finrank G ≤ finrank F`, every greedy sequence of
maximizers `(f k, g k)` has `re ⟪f k, g k⟫ = cos θ_{k+1}`, whichever maximizers were chosen. By
induction on `k`: a maximizing first pair is a top singular pair of `P_F|_G`, and the problem on
the orthogonal complements of the first pair is the same problem for the deflated map, whose
singular values are the later ones (`LinearMap.singularValues_comp_linearIsometry_eq_succ`). -/
theorem cosPrincipalAngle_eq_of_isRecursivePrincipalVectors (h : finrank 𝕜 G ≤ finrank 𝕜 F)
    {q : ℕ} {f g : Fin q → E} (hfg : F.IsRecursivePrincipalVectors G f g) (k : Fin q) :
    RCLike.re (inner 𝕜 (f k) (g k)) = F.cosPrincipalAngle G k :=
  re_inner_eq_cosPrincipalAngle_aux k F G q f g h hfg k.2

/-! ### The gap, lines, and matrices -/

/-- **The distance of equal-dimensional subspaces is the sine of the largest principal angle**
([golub2013matrix] §6.4.3: if `p = q`, `dist(F, G) = √(1 - cos(θ_p)²) = sin θ_p`): if
`finrank F = finrank G = q + 1`, then `gap F G = sin θ_{q+1}`. The gap is the one-sided gap
`‖P_{F⊥} P_G‖`, whose square is `1 - σ_q(P_F|_G)²`. -/
theorem gap_eq_sin_principalAngle {q : ℕ} (hF : finrank 𝕜 F = q + 1)
    (hG : finrank 𝕜 G = q + 1) : F.gap G = Real.sin (F.principalAngle G q) := by
  have h := G.norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues F (by omega)
  rw [← G.gap_eq_norm_orthogonal_mul_of_finrank_eq F (hG.trans hF.symm), gap_comm, hG,
    Nat.add_sub_cancel] at h
  rw [principalAngle, Real.sin_arccos, cosPrincipalAngle, ← h,
    Real.sqrt_sq (F.gap_nonneg G)]

/-- **One principal angle with a line is the angle with a vector** ([golub2013matrix] §6.4.3 for
`q = 1`): for `u ≠ 0`, `cos θ₁(F, 𝕜 u) = ‖P_F u‖ / ‖u‖` is `Submodule.cosAngle`. On a line,
`P_F` stretches every vector by the same factor. -/
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

/-- The principal angle with a line is the angle of `Submodule.angle`. -/
theorem principalAngle_span_singleton_zero {u : E} (hu : u ≠ 0) :
    F.principalAngle (𝕜 ∙ u) 0 = F.angle u := by
  rw [principalAngle, cosPrincipalAngle_span_singleton_zero F hu, angle]

open Matrix in
/-- **The matrix bridge** ([golub2013matrix] §6.4.3: `σ_i = cos θ_i` for the SVD of `Q_Aᴴ Q_B`):
if the columns of `Q_A` and `Q_B` are orthonormal (`Q_Aᴴ Q_A = 1`, `Q_Bᴴ Q_B = 1`), the cosines of
the principal angles between their ranges are the singular values of `Q_Aᴴ Q_B`. The two matrices
are isometries onto the ranges, and `Q_A (Q_Aᴴ Q_B) y = P_F (Q_B y)`, so `Q_Aᴴ Q_B` is `P_F|_G` up
to isometries on both sides. -/
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
/-- **The cosines from any SVD** ([golub2013matrix] §6.4.3, Algorithm 6.4.3): if the columns of
`Q_A` and `Q_B` are orthonormal and `Q_Aᴴ Q_B = Y Σ Zᴴ` is an SVD, then `σ_k = cos θ_{k+1}` for
`k < min p q`: the diagonal of every SVD is the sorted singular values
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
/-- **Principal vectors from any SVD** ([golub2013matrix] §6.4.3, Algorithm 6.4.3): if the columns
of `Q_A` and `Q_B` are orthonormal, `q ≤ p`, and `Q_Aᴴ Q_B = Y Σ Zᴴ` is an SVD, then the columns of
`Q_A Y(:, 1:q)` and `Q_B Z` are principal vectors of `(ran Q_A, ran Q_B)`. The projection onto
`ran Q_A` is `Q_A Q_Aᴴ`, so `P (Q_B z_j) = Q_A Y Σ Zᴴ z_j = σ_j Q_A y_j`, and
`σ_j = cos θ_{j+1}` (`Submodule.cosPrincipalAngle_eq_of_isSVD`). -/
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
    rw [mul_apply] at this
    rw [Pi.single_apply, ← one_apply, ← this]
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
