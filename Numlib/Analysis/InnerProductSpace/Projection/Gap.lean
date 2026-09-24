import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.SingularValues

/-!
# The gap between two subspaces

For two subspaces `K`, `L` of an inner product space admitting orthogonal projections `P_K`, `P_L`,
the *gap* `K.gap L = ‖P_K - P_L‖` is the distance between them in the metric the subspace-iteration
bounds are measured in, and the subspace distance `dist(S₁, S₂) = ‖P₁ - P₂‖₂` of
[golub2013matrix] §2.5.3. Mathlib has no such notion. Everything is stated over `RCLike` and needs
neither completeness nor finite dimension of the ambient space, only
`Submodule.HasOrthogonalProjection` (and finite dimension of the two subspaces where singular values
enter).

The definition follows [saad2011numerical], §3.1, the source of the bounds that use it, which
writes `ω(K, L) = max {‖(1 - P_K) P_L‖, ‖(1 - P_L) P_K‖}` and states that it equals `‖P_K - P_L‖`;
the latter is the definition taken here, and it is the *symmetric* gap. That the two agree is
`gap_eq_max_norm_orthogonal_mul`; each one-sided gap `‖P_{L⊥} P_K‖` is also
`sup {sin θ(x, L) | x ∈ K, ‖x‖ = 1}`, and `sinAngle_le_gap` is the bridge to the angles of
`Numlib.Analysis.InnerProductSpace.Projection.Angle` that the subspace-iteration bounds consume.

## Main results

* `Submodule.gap_comm`, `Submodule.gap_eq_zero_iff`, `Submodule.gap_le_one`: the gap is a metric on
  the subspaces admitting an orthogonal projection, bounded by `1`. `gap_le_one` comes from the
  pointwise bound `norm_starProjection_sub_apply_le`, `‖(P_K - P_L) x‖ ≤ ‖x‖`, proved by splitting
  `P_K - P_L = P_K (1 - P_L) - P_Kᗮ P_L` into two orthogonal pieces.
* `Submodule.finrank_eq_of_gap_lt_one`: the rank-constancy fact behind subspace iteration
  ([saad2011numerical], Thm 3.2): a gap below `1` makes `P_K` injective on `L`, and symmetry does
  the rest.
* `Submodule.gap_le_add` and `Submodule.gap_le_of_forall_norm_sub_le`: the gap is bounded from
  above in two steps. `gap_le_add` bounds it by the sum of the two one-sided relative distances, and
  `gap_le_of_forall_norm_sub_le` bounds those when the two subspaces are given by spanning families
  that are close vector by vector: `gap K L ≤ 3 κ δ` when `‖w j - x j‖ ≤ δ` and `κ` is the ℓ¹
  conditioning constant of the family `x`, which is `LinearIndependent.exists_forall_sum_norm_le`.
  That is the quantitative continuity of a projector in a spanning family, and it is what turns the
  per-vector estimates of subspace iteration into a gap bound (`Krylov.gap_subspaceIterate_le`).
* `Submodule.gap_eq_max_norm_orthogonal_mul`: the gap is the larger of the two one-sided gaps.
* `Submodule.norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues`: the one-sided gap is
  `√(1 - σ_min(P_L|_K)²)`, through the restricted projection
  `Submodule.orthogonalProjectionRestrict L K : K →ₗ[𝕜] L` and the stacked-isometry identity of
  `Numlib.Analysis.InnerProductSpace.SingularValues`.
* `Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq` and `Submodule.gap_eq_one_iff_of_finrank_eq`:
  for subspaces of equal finite dimension the gap is either one-sided gap (the restricted projection
  and its adjoint `P_K|_L` have the same singular values), and it is `1` exactly when `K` meets `Lᗮ`
  ([golub2013matrix] §2.5.3).
* `Submodule.graph` and `Submodule.gap_graph`: the gap between `K` and the graph
  `{x + X x | x ∈ K}` of `X : K →L[𝕜] Kᗮ` is `‖X‖ / √(1 + ‖X‖²)`, the computation behind the
  invariant-subspace and subspace-iteration theorems of [golub2013matrix] §7.3 and §8.2.

## Implementation notes

The equal-dimension theory is proved without coordinates, orthonormal bases or a CS decomposition:
the engine is the restricted projection `P_L|_K`, whose least singular value measures how far `K`
is from `L`. The matrix forms ([golub2013matrix] Theorem 2.5.1 and (7.3.19)) are corollaries in
`Numlib/Analysis/Matrix/SingularValues`, and the principal angles of
`Numlib/Analysis/InnerProductSpace/PrincipalAngles` are the singular values of the same map.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The gap between two subspaces, `‖P_K - P_L‖`: the distance between them in the metric the
subspace-iteration bounds are measured in. It is symmetric (`gap_comm`), vanishes exactly on equal
subspaces (`gap_eq_zero_iff`) and never exceeds `1` (`gap_le_one`). -/
noncomputable def gap (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : ℝ :=
  ‖K.starProjection - L.starProjection‖

section Gap

variable (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- The gap is a norm, hence nonnegative. -/
theorem gap_nonneg : 0 ≤ K.gap L := norm_nonneg _

/-- The gap is symmetric. -/
theorem gap_comm : K.gap L = L.gap K := norm_sub_rev _ _

/-- A subspace is at gap zero from itself. -/
@[simp]
theorem gap_self : K.gap K = 0 := by rw [gap, sub_self, norm_zero]

/-- The defining bound of the gap, in the pointwise form its consumers use. -/
theorem norm_starProjection_sub_le_gap_mul (x : E) :
    ‖K.starProjection x - L.starProjection x‖ ≤ K.gap L * ‖x‖ := by
  simpa [gap] using (K.starProjection - L.starProjection).le_opNorm x

/-- The two orthogonal pieces of `P_K x - P_L x = P_K (x - P_L x) - P_{Kᗮ} (P_L x)`, a vector of `K`
and a vector of `Kᗮ`. -/
theorem norm_starProjection_sub_apply_sq_eq_add (x : E) :
    ‖K.starProjection x - L.starProjection x‖ ^ 2 =
      ‖K.starProjection (x - L.starProjection x)‖ ^ 2
        + ‖Kᗮ.starProjection (L.starProjection x)‖ ^ 2 := by
  have hinner : inner 𝕜 (K.starProjection (x - L.starProjection x))
      (Kᗮ.starProjection (L.starProjection x)) = 0 :=
    (K.mem_orthogonal _).1 (Kᗮ.starProjection_apply_mem _) _ (K.starProjection_apply_mem _)
  have hsplit : K.starProjection x - L.starProjection x =
      K.starProjection (x - L.starProjection x) + -Kᗮ.starProjection (L.starProjection x) := by
    rw [map_sub, starProjection_orthogonal_val]
    abel
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)
    (K.starProjection (x - L.starProjection x)) (-Kᗮ.starProjection (L.starProjection x))
    (by rw [inner_neg_right, hinner, neg_zero])
  rw [hsplit, pow_two, pow_two, pow_two, h, norm_neg]

/-- Two orthogonal projections never move a vector by more than its own length. Split `P_K x - P_L x
= P_K (x - P_L x) - P_{Kᗮ} (P_L x)` into a piece of `K` and a piece of `Kᗮ`: the two are orthogonal,
each is shorter than the corresponding piece of the splitting of `x` along `L`, and Pythagoras over
`L` closes the estimate. -/
theorem norm_starProjection_sub_apply_le (x : E) :
    ‖K.starProjection x - L.starProjection x‖ ≤ ‖x‖ := by
  have hpyth := K.norm_starProjection_sub_apply_sq_eq_add L x
  have hA : ‖K.starProjection (x - L.starProjection x)‖ ≤ ‖Lᗮ.starProjection x‖ := by
    rw [← starProjection_orthogonal_val (K := L) x]
    exact K.norm_starProjection_apply_le _
  have hB : ‖Kᗮ.starProjection (L.starProjection x)‖ ≤ ‖L.starProjection x‖ :=
    Kᗮ.norm_starProjection_apply_le _
  have hx : ‖Lᗮ.starProjection x‖ ^ 2 + ‖L.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [add_comm]
    exact (norm_sq_eq_add_norm_sq_starProjection x L).symm
  nlinarith [norm_nonneg (K.starProjection x - L.starProjection x), norm_nonneg x,
    norm_nonneg (K.starProjection (x - L.starProjection x)),
    norm_nonneg (Kᗮ.starProjection (L.starProjection x)),
    norm_nonneg (Lᗮ.starProjection x), norm_nonneg (L.starProjection x)]

/-- The gap between two subspaces is at most `1`. -/
theorem gap_le_one : K.gap L ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using K.norm_starProjection_sub_apply_le L x

/-- The bridge between the gap and the angles of `Submodule.sinAngle`, and the one-sided reading of
the gap: every vector of `L` is at relative distance at most `gap K L` from `K`. The one-sided
quantity `sup {sin θ(x, K) | x ∈ L, ‖x‖ = 1}` this bounds is in general strictly smaller than the
gap. -/
theorem sinAngle_le_gap {x : E} (hx : x ∈ L) : K.sinAngle x ≤ K.gap L := by
  rcases eq_or_ne x 0 with rfl | hne
  · simpa using K.gap_nonneg L
  · rw [sinAngle, div_le_iff₀ (norm_pos_iff.2 hne)]
    have h : ‖x - K.starProjection x‖ = ‖K.starProjection x - L.starProjection x‖ := by
      rw [starProjection_eq_self_iff.2 hx, norm_sub_rev]
    rw [h]
    exact K.norm_starProjection_sub_le_gap_mul L x

/-- The gap from the zero subspace is the norm of the projector. -/
theorem gap_bot : (⊥ : Submodule 𝕜 E).gap K = ‖K.starProjection‖ := by
  rw [gap, starProjection_bot, zero_sub, norm_neg]

/-- The zero subspace is at the largest possible gap from every other subspace. -/
theorem gap_bot_eq_one (hK : K ≠ ⊥) : (⊥ : Submodule 𝕜 E).gap K = 1 := by
  rw [gap_bot, K.norm_starProjection hK]

/-- The gap separates points: it is a metric on the subspaces admitting an orthogonal projection,
not a pseudometric. -/
theorem gap_eq_zero_iff : K.gap L = 0 ↔ K = L := by
  rw [gap, norm_eq_zero, sub_eq_zero]
  refine ⟨fun h => ?_, ?_⟩
  · ext v
    rw [← starProjection_eq_self_iff (K := K), ← starProjection_eq_self_iff (K := L), h]
  · rintro rfl
    rfl

/-- Below gap `1` the projection onto `K` is injective on `L`: a nonzero `x ∈ L` killed by `P_K`
would be moved by its full length, `‖(P_L - P_K) x‖ = ‖x‖`. -/
theorem eq_zero_of_starProjection_eq_zero_of_gap_lt_one (h : K.gap L < 1) {x : E} (hx : x ∈ L)
    (hx0 : K.starProjection x = 0) : x = 0 := by
  have h1 : ‖K.starProjection x - L.starProjection x‖ = ‖x‖ := by
    rw [hx0, zero_sub, norm_neg, starProjection_eq_self_iff.2 hx]
  have h2 := K.norm_starProjection_sub_le_gap_mul L x
  rw [h1] at h2
  by_contra hne
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hne
  nlinarith

/-- One half of `finrank_eq_of_gap_lt_one`. -/
theorem finrank_le_of_gap_lt_one [FiniteDimensional 𝕜 K] (h : K.gap L < 1) :
    Module.finrank 𝕜 L ≤ Module.finrank 𝕜 K := by
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp L.subtype)
    (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun x hx => ?_))
  refine Subtype.ext (K.eq_zero_of_starProjection_eq_zero_of_gap_lt_one L h x.2 ?_)
  rw [starProjection_apply]
  simpa using congrArg Subtype.val hx

/-- Two subspaces at gap less than `1` have the same dimension, so a continuously varying family of
orthogonal projectors has constant rank ([saad2011numerical], Thm 3.2). -/
theorem finrank_eq_of_gap_lt_one [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (h : K.gap L < 1) : Module.finrank 𝕜 K = Module.finrank 𝕜 L :=
  le_antisymm (L.finrank_le_of_gap_lt_one K (by rwa [gap_comm]))
    (K.finrank_le_of_gap_lt_one L h)

/-- Two names for the same subspace give the same gap.  The instance argument of `gap` depends on
the subspace, so `rw` on the second argument needs this. -/
theorem gap_congr {L' : Submodule 𝕜 E} [L'.HasOrthogonalProjection] (h : L = L') :
    K.gap L = K.gap L' := by subst h; rfl

/-- **The projection onto `K` is small on `Lᗮ` as soon as `K` is close to `L`.** If every vector of
`K` is within a relative distance `a` of `L`, then `P_K` shrinks every vector orthogonal to `L` by
the same factor.

This is the half of `gap_le_add` that is not immediate: the hypothesis is about vectors *of* `K`
while the conclusion is about vectors of `Lᗮ`, and the passage is the quadratic step `‖P_K w‖ ^ 2 =
⟪P_K w - P_L (P_K w), w⟫`, in which the `P_L` term is free because `w ⊥ L`. -/
theorem norm_starProjection_le_of_mem_orthogonal {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ u ∈ K, ‖u - L.starProjection u‖ ≤ a * ‖u‖) {w : E} (hw : w ∈ Lᗮ) :
    ‖K.starProjection w‖ ≤ a * ‖w‖ := by
  set v := K.starProjection w with hv
  have hvK : v ∈ K := K.starProjection_apply_mem w
  have h1 : (inner 𝕜 v (w - v) : 𝕜) = 0 :=
    (K.mem_orthogonal (w - v)).1 (K.sub_starProjection_mem_orthogonal w) v hvK
  have h2 : (inner 𝕜 v w : 𝕜) = ((‖v‖ : 𝕜)) ^ 2 := by
    have h := inner_sub_right (𝕜 := 𝕜) v w v
    rw [h1, inner_self_eq_norm_sq_to_K] at h
    linear_combination -h
  have h3 : (inner 𝕜 (L.starProjection v) w : 𝕜) = 0 :=
    (L.mem_orthogonal w).1 hw _ (L.starProjection_apply_mem v)
  have h4 : (inner 𝕜 (v - L.starProjection v) w : 𝕜) = ((‖v‖ : 𝕜)) ^ 2 := by
    rw [inner_sub_left, h2, h3, sub_zero]
  have h5 : ‖v‖ ^ 2 ≤ ‖v - L.starProjection v‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := 𝕜) (v - L.starProjection v) w
    rw [h4] at h
    simpa using h
  have h6 : ‖v - L.starProjection v‖ ≤ a * ‖v‖ := h v hvK
  rcases eq_or_lt_of_le (norm_nonneg v) with hz | hz
  · rw [← hz]
    positivity
  · nlinarith [norm_nonneg w]

/-- **The gap is bounded by the two one-sided distances.** If every vector of `K` is within relative
distance `a` of `L` and every vector of `L` within relative distance `b` of `K`, then `‖P_K - P_L‖ ≤
a + b`.

[saad2011numerical]'s (3.8) says more, that the gap is the *maximum* of the two one-sided suprema;
the sum is what the splitting `P_K - P_L = -(1 - P_K) P_L + P_K (1 - P_L)` gives directly, and it is
enough wherever both sides are estimated by the same quantity. -/
theorem gap_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hKL : ∀ u ∈ K, ‖u - L.starProjection u‖ ≤ a * ‖u‖)
    (hLK : ∀ y ∈ L, ‖y - K.starProjection y‖ ≤ b * ‖y‖) :
    K.gap L ≤ a + b := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hsplit : K.starProjection v - L.starProjection v =
      -(L.starProjection v - K.starProjection (L.starProjection v))
        + K.starProjection (v - L.starProjection v) := by
    rw [map_sub]
    abel
  have hb1 : ‖L.starProjection v - K.starProjection (L.starProjection v)‖
      ≤ b * ‖L.starProjection v‖ := hLK _ (L.starProjection_apply_mem v)
  have ha1 : ‖K.starProjection (v - L.starProjection v)‖ ≤ a * ‖v - L.starProjection v‖ :=
    norm_starProjection_le_of_mem_orthogonal K L ha hKL (L.sub_starProjection_mem_orthogonal v)
  have hn1 : ‖L.starProjection v‖ ≤ ‖v‖ := L.norm_starProjection_apply_le v
  have hn2 : ‖v - L.starProjection v‖ ≤ ‖v‖ := L.norm_sub_starProjection_le v
  calc ‖K.starProjection v - L.starProjection v‖
      ≤ ‖L.starProjection v - K.starProjection (L.starProjection v)‖
        + ‖K.starProjection (v - L.starProjection v)‖ := by
        rw [hsplit]
        simpa only [norm_neg] using
          norm_add_le (-(L.starProjection v - K.starProjection (L.starProjection v)))
            (K.starProjection (v - L.starProjection v))
    _ ≤ b * ‖v‖ + a * ‖v‖ :=
        add_le_add (hb1.trans (by gcongr)) (ha1.trans (by gcongr))
    _ = (a + b) * ‖v‖ := by ring

/-- **The gap is Lipschitz in a spanning family.** If `K` is spanned by `x` and `L` by a family `w`
with `‖w j - x j‖ ≤ δ` for every `j`, then `gap K L ≤ 3 κ δ`, where `κ` is the ℓ¹ conditioning
of the family `x` — the constant of `LinearIndependent.exists_forall_sum_norm_le`.

The smallness hypothesis `κ δ ≤ 1 / 2` is needed and cannot be dropped: without it the perturbed
family may be degenerate, `L` may have a smaller dimension than `K`, and the gap is then `1`
however small the individual `‖w j - x j‖` are relative to a *badly conditioned* `x`. It is used
only for the direction from `L` to `K`; the direction from `K` to `L` holds unconditionally, since
`∑ c j • w j` is a competitor for the projection of `∑ c j • x j` whatever `w` is.

This is the quantitative continuity of `family ↦ starProjection (span family)` that turns the
per-vector decay estimates of subspace iteration into the gap bound
`Krylov.gap_subspaceIterate_le`. -/
theorem gap_le_of_forall_norm_sub_le {ι : Type*} [Fintype ι] {x w : ι → E} {κ δ : ℝ}
    (hK : K = span 𝕜 (Set.range x)) (hL : L = span 𝕜 (Set.range w)) (hκ0 : 0 ≤ κ) (hδ0 : 0 ≤ δ)
    (hκ : ∀ c : ι → 𝕜, ∑ j, ‖c j‖ ≤ κ * ‖∑ j, c j • x j‖)
    (hδ : ∀ j, ‖w j - x j‖ ≤ δ) (hκδ : κ * δ ≤ 1 / 2) :
    K.gap L ≤ 3 * (κ * δ) := by
  have hsum : ∀ c : ι → 𝕜, ‖(∑ j, c j • w j) - ∑ j, c j • x j‖ ≤ (∑ j, ‖c j‖) * δ := by
    intro c
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_left (hδ j) (norm_nonneg _)
  have ha : ∀ u ∈ K, ‖u - L.starProjection u‖ ≤ κ * δ * ‖u‖ := by
    intro u hu
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 (hK ▸ hu)
    have hy : (∑ j, c j • w j) ∈ L := by
      rw [hL]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    refine ((isBestApprox_starProjection L _).2 _ hy).trans ?_
    rw [norm_sub_rev]
    refine (hsum c).trans ?_
    calc (∑ j, ‖c j‖) * δ ≤ κ * ‖∑ j, c j • x j‖ * δ :=
          mul_le_mul_of_nonneg_right (hκ c) hδ0
      _ = κ * δ * ‖∑ j, c j • x j‖ := by ring
  have hb : ∀ y ∈ L, ‖y - K.starProjection y‖ ≤ 2 * (κ * δ) * ‖y‖ := by
    intro y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 (hL ▸ hy)
    have hz : (∑ j, c j • x j) ∈ K := by
      rw [hK]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hT0 : 0 ≤ ∑ j, ‖c j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    have hd := hsum c
    have hzy : ‖∑ j, c j • x j‖ ≤ ‖∑ j, c j • w j‖ + (∑ j, ‖c j‖) * δ := by
      have h := norm_sub_norm_le (∑ j, c j • x j) (∑ j, c j • w j)
      rw [norm_sub_rev] at h
      linarith
    have hTle : (∑ j, ‖c j‖) ≤ 2 * (κ * ‖∑ j, c j • w j‖) := by
      have h1 := hκ c
      nlinarith [norm_nonneg (∑ j, c j • w j)]
    refine ((isBestApprox_starProjection K _).2 _ hz).trans ?_
    calc ‖(∑ j, c j • w j) - ∑ j, c j • x j‖ ≤ (∑ j, ‖c j‖) * δ := hd
      _ ≤ 2 * (κ * ‖∑ j, c j • w j‖) * δ := by gcongr
      _ = 2 * (κ * δ) * ‖∑ j, c j • w j‖ := by ring
  have hfin := gap_le_add K L (by positivity) (by positivity) ha hb
  linarith

end Gap

/-! ### The one-sided gaps -/

section OneSided

variable (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- ([golub2013matrix] §2.5.1, the display behind the uniqueness of the orthogonal projection) For
any `z`, `‖P_K z - P_L z‖² = re ⟪P_K z, z - P_L z⟫ + re ⟪P_L z, z - P_K z⟫`. -/
theorem norm_starProjection_sub_apply_sq (z : E) :
    ‖K.starProjection z - L.starProjection z‖ ^ 2 =
      RCLike.re (inner 𝕜 (K.starProjection z) (z - L.starProjection z)) +
        RCLike.re (inner 𝕜 (L.starProjection z) (z - K.starProjection z)) := by
  have h1 : inner 𝕜 (K.starProjection z) (z - K.starProjection z) = 0 :=
    (K.mem_orthogonal _).1 (K.sub_starProjection_mem_orthogonal z) _ (K.starProjection_apply_mem z)
  have h2 : inner 𝕜 (L.starProjection z) (z - L.starProjection z) = 0 :=
    (L.mem_orthogonal _).1 (L.sub_starProjection_mem_orthogonal z) _ (L.starProjection_apply_mem z)
  have h : inner 𝕜 (K.starProjection z - L.starProjection z)
      (K.starProjection z - L.starProjection z) =
      inner 𝕜 (K.starProjection z) (z - L.starProjection z) +
        inner 𝕜 (L.starProjection z) (z - K.starProjection z) := by
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    linear_combination -h1 - h2
  rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), h, map_add]

/-- Each one-sided gap `‖P_{L⊥} P_K‖` is at most the gap: `(P_K - P_L) P_K = P_{L⊥} P_K`. -/
theorem norm_orthogonal_mul_le_gap : ‖Lᗮ.starProjection * K.starProjection‖ ≤ K.gap L := by
  refine ContinuousLinearMap.opNorm_le_bound _ (K.gap_nonneg L) fun x => ?_
  have h : (Lᗮ.starProjection * K.starProjection) x =
      K.starProjection (K.starProjection x) - L.starProjection (K.starProjection x) := by
    rw [mul_apply_eq_comp, starProjection_orthogonal_val,
      starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]
  rw [h]
  exact (K.norm_starProjection_sub_le_gap_mul L _).trans
    (mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le x) (K.gap_nonneg L))

/-- **The gap is the larger of the two one-sided gaps**, in any inner product space:
`gap K L = max ‖P_{L⊥} P_K‖ ‖P_{K⊥} P_L‖`. The bound `≥` is `norm_orthogonal_mul_le_gap` twice;
for `≤`, the two orthogonal pieces of `P_K x - P_L x = P_K (x - P_L x) - P_{K⊥} (P_L x)` are
bounded by the one-sided gaps times the two orthogonal pieces of `x` along `L`. This is the
equality that [saad2011numerical] (3.8) states. -/
theorem gap_eq_max_norm_orthogonal_mul :
    K.gap L =
      max ‖Lᗮ.starProjection * K.starProjection‖ ‖Kᗮ.starProjection * L.starProjection‖ := by
  refine le_antisymm ?_ (max_le (K.norm_orthogonal_mul_le_gap L)
    (by rw [gap_comm]; exact L.norm_orthogonal_mul_le_gap K))
  set a := ‖Lᗮ.starProjection * K.starProjection‖
  set b := ‖Kᗮ.starProjection * L.starProjection‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ (ha.trans (le_max_left a b)) fun x => ?_
  have hA : ‖K.starProjection (x - L.starProjection x)‖ ≤ a * ‖x - L.starProjection x‖ := by
    refine K.norm_starProjection_le_of_mem_orthogonal L ha (fun u hu => ?_)
      (L.sub_starProjection_mem_orthogonal x)
    have h := (Lᗮ.starProjection * K.starProjection).le_opNorm u
    rwa [mul_apply_eq_comp, starProjection_eq_self_iff.2 hu,
      starProjection_orthogonal_val] at h
  have hB : ‖Kᗮ.starProjection (L.starProjection x)‖ ≤ b * ‖L.starProjection x‖ := by
    have h := (Kᗮ.starProjection * L.starProjection).le_opNorm (L.starProjection x)
    rwa [mul_apply_eq_comp,
      starProjection_eq_self_iff.2 (L.starProjection_apply_mem x)] at h
  have hx : ‖x - L.starProjection x‖ ^ 2 + ‖L.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← starProjection_orthogonal_val, add_comm]
    exact (norm_sq_eq_add_norm_sq_starProjection x L).symm
  have hsq := K.norm_starProjection_sub_apply_sq_eq_add L x
  set m := max a b
  have ham : a ≤ m := le_max_left a b
  have hbm : b ≤ m := le_max_right a b
  have h1 : ‖K.starProjection x - L.starProjection x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
    rw [hsq, mul_pow, ← hx]
    have hA' := mul_le_mul_of_nonneg_right ham (norm_nonneg (x - L.starProjection x))
    have hB' := mul_le_mul_of_nonneg_right hbm (norm_nonneg (L.starProjection x))
    nlinarith [norm_nonneg (K.starProjection (x - L.starProjection x)),
      norm_nonneg (Kᗮ.starProjection (L.starProjection x)),
      mul_le_mul (hA.trans hA') (hA.trans hA') (norm_nonneg _) (by positivity),
      mul_le_mul (hB.trans hB') (hB.trans hB') (norm_nonneg _) (by positivity)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- If `K` meets `Lᗮ`, the gap is `1`: a unit vector of `K ⊓ Lᗮ` is moved by its full length. No
dimension hypothesis. -/
theorem gap_eq_one_of_inf_orthogonal_ne_bot (h : K ⊓ Lᗮ ≠ ⊥) : K.gap L = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine le_antisymm (K.gap_le_one L) ?_
  have h1 := K.norm_starProjection_sub_le_gap_mul L x
  rw [starProjection_eq_self_iff.2 hx.1, (starProjection_apply_eq_zero_iff L).2 hx.2,
    sub_zero] at h1
  exact le_of_mul_le_mul_right (by simpa using h1) (norm_pos_iff.2 hx0)

end OneSided

/-! ### The restricted projection and the equal-dimension theory -/

section Restrict

/-- **The orthogonal projection onto `F` restricted to `G`**, `P_F|_G : G →ₗ[𝕜] F`. Its matrix in
orthonormal bases of `G` and `F` is `Q_Fᴴ Q_G`; its singular values are the cosines of the
principal angles between `F` and `G` (`Submodule.cosPrincipalAngle`), and its adjoint is `P_G|_F`
(`Submodule.orthogonalProjectionRestrict_adjoint`). -/
noncomputable def orthogonalProjectionRestrict (F G : Submodule 𝕜 E) [F.HasOrthogonalProjection] :
    G →ₗ[𝕜] F :=
  (F.orthogonalProjectionOnto : E →ₗ[𝕜] F) ∘ₗ G.subtype

@[simp]
theorem coe_orthogonalProjectionRestrict_apply (F G : Submodule 𝕜 E) [F.HasOrthogonalProjection]
    (x : G) : (F.orthogonalProjectionRestrict G x : E) = F.starProjection x :=
  rfl

/-- The adjoint of `P_F|_G` is `P_G|_F`: `⟪P_G f, g⟫ = ⟪f, g⟫ = ⟪f, P_F g⟫` for `f ∈ F`, `g ∈ G`. -/
theorem orthogonalProjectionRestrict_adjoint (F G : Submodule 𝕜 E) [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] :
    LinearMap.adjoint (F.orthogonalProjectionRestrict G) = G.orthogonalProjectionRestrict F := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, coe_orthogonalProjectionRestrict_apply]
  rw [inner_starProjection_left_eq_right, starProjection_eq_self_iff.2 y.2,
    ← starProjection_eq_self_iff.2 x.2, inner_starProjection_left_eq_right,
    starProjection_eq_self_iff.2 x.2]

variable (K L : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]

/-- **The one-sided gap through the restricted projection**: for finite-dimensional `K ≠ ⊥` and
`L`, `‖P_{L⊥} P_K‖² = 1 - σ_min(P_L|_K)²`, the least singular value being
`σ_{finrank K - 1}`. For `x ∈ K`, `‖P_L x‖² + ‖P_{L⊥} x‖² = ‖x‖²`, so this is the stacked-isometry
identity `LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues`. If
`finrank K > finrank L` both sides are `1`. -/
theorem norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues (hK : 0 < Module.finrank 𝕜 K) :
    ‖Lᗮ.starProjection * K.starProjection‖ ^ 2 =
      1 - (L.orthogonalProjectionRestrict K).singularValues (Module.finrank 𝕜 K - 1) ^ 2 := by
  let Q₂ : K →ₗ[𝕜] E := (Lᗮ.starProjection : E →ₗ[𝕜] E) ∘ₗ K.subtype
  have hQ₂ : ∀ x : K, Q₂ x = Lᗮ.starProjection x := fun _ => rfl
  have hQ : ∀ x : K, ‖L.orthogonalProjectionRestrict K x‖ ^ 2 + ‖Q₂ x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← Submodule.norm_coe (L.orthogonalProjectionRestrict K x),
      coe_orthogonalProjectionRestrict_apply, hQ₂, ← Submodule.norm_coe x]
    exact (norm_sq_eq_add_norm_sq_starProjection (x : E) L).symm
  rw [← LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues _ Q₂ hK hQ]
  congr 1
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h := (LinearMap.toContinuousLinearMap Q₂).le_opNorm (K.orthogonalProjectionOnto z)
    rw [LinearMap.coe_toContinuousLinearMap', hQ₂, ← starProjection_apply] at h
    rw [mul_apply_eq_comp]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← Submodule.norm_coe, ← starProjection_apply]
    exact K.norm_starProjection_apply_le z
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [LinearMap.coe_toContinuousLinearMap', hQ₂, ← Submodule.norm_coe x,
      ← starProjection_eq_self_iff.2 x.2, ← mul_apply_eq_comp,
      starProjection_eq_self_iff.2 x.2]
    exact (Lᗮ.starProjection * K.starProjection).le_opNorm _

/-- The zero subspace is the only one of dimension zero, as far as its projection goes. -/
private theorem starProjection_eq_zero_of_finrank_eq_zero (h : Module.finrank 𝕜 K = 0) :
    K.starProjection = 0 := by
  ext x
  exact (Submodule.eq_bot_iff K).1 (Submodule.finrank_eq_zero.1 h) _ (K.starProjection_apply_mem x)

/-- **For subspaces of equal dimension the gap is the one-sided gap**: if `finrank K = finrank L`,
then `gap K L = ‖P_{L⊥} P_K‖` (and, by `gap_comm`, `= ‖P_{K⊥} P_L‖`). The two one-sided gaps are
`√(1 - σ_min(P_L|_K)²)` and `√(1 - σ_min(P_K|_L)²)`, and `P_K|_L` is the adjoint of `P_L|_K`, with
the same singular values. No finite dimension of the ambient space is needed. -/
theorem gap_eq_norm_orthogonal_mul_of_finrank_eq
    (h : Module.finrank 𝕜 K = Module.finrank 𝕜 L) :
    K.gap L = ‖Lᗮ.starProjection * K.starProjection‖ := by
  rw [gap_eq_max_norm_orthogonal_mul]
  suffices ‖Kᗮ.starProjection * L.starProjection‖ = ‖Lᗮ.starProjection * K.starProjection‖ by
    rw [this, max_self]
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 K) with h0 | hpos
  · rw [starProjection_eq_zero_of_finrank_eq_zero K h0,
      starProjection_eq_zero_of_finrank_eq_zero L (h ▸ h0), mul_zero, mul_zero]
  · refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues L K (h ▸ hpos),
      norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues K L hpos,
      ← orthogonalProjectionRestrict_adjoint L K, LinearMap.singularValues_adjoint, h]

/-- **Equal-dimensional subspaces are at gap `1` exactly when one meets the orthogonal complement
of the other** ([golub2013matrix] §2.5.3): `gap K L = 1 ↔ K ⊓ Lᗮ ≠ ⊥` when
`finrank K = finrank L`. Gap `1` forces `σ_min(P_L|_K) = 0`, so `P_L|_K` has a kernel. Without
equal dimensions `→` fails (a line inside a plane). -/
theorem gap_eq_one_iff_of_finrank_eq (h : Module.finrank 𝕜 K = Module.finrank 𝕜 L) :
    K.gap L = 1 ↔ K ⊓ Lᗮ ≠ ⊥ := by
  refine ⟨fun h1 hbot => ?_, K.gap_eq_one_of_inf_orthogonal_ne_bot L⟩
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 K) with h0 | hpos
  · have hKL : K = L :=
      (Submodule.finrank_eq_zero.1 h0).trans (Submodule.finrank_eq_zero.1 (h ▸ h0)).symm
    rw [(K.gap_eq_zero_iff L).2 hKL] at h1
    exact zero_ne_one h1
  have h2 := K.norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues L hpos
  rw [← K.gap_eq_norm_orthogonal_mul_of_finrank_eq L h, h1] at h2
  have hσ : (L.orthogonalProjectionRestrict K).singularValues (Module.finrank 𝕜 K - 1) = 0 := by
    nlinarith [(L.orthogonalProjectionRestrict K).singularValues_nonneg
      (Module.finrank 𝕜 K - 1)]
  have hni : ¬ Function.Injective (L.orthogonalProjectionRestrict K) := by
    rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
    intro hpos'
    exact (hpos' _ (by omega)).ne' hσ
  rw [← LinearMap.ker_eq_bot] at hni
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hni
  refine hx0 (Subtype.ext ?_)
  have hxL : (x : E) ∈ Lᗮ := by
    rw [← starProjection_apply_eq_zero_iff, ← coe_orthogonalProjectionRestrict_apply,
      LinearMap.mem_ker.1 hx, Submodule.coe_zero]
  have : (x : E) ∈ K ⊓ Lᗮ := ⟨x.2, hxL⟩
  rw [hbot, Submodule.mem_bot] at this
  exact this

end Restrict

/-! ### The graph of a map over a subspace -/

section Graph

variable (K : Submodule 𝕜 E)

/-- **The graph of a map over a subspace**: for `X : K →L[𝕜] Kᗮ`, the subspace
`{x + X x | x ∈ K}` of `E` — in coordinates adapted to `K ⊕ Kᗮ`, the range of `[I; X]`
([golub2013matrix] §7.2.4, §7.3.1, §8.2.2: the subspaces `ran [I; X]` of the invariant-subspace and
subspace-iteration theorems). Mathlib's `LinearMap.graph` lives in `E × F` and is a different
object. -/
def graph (X : K →L[𝕜] Kᗮ) : Submodule 𝕜 E :=
  LinearMap.range (K.subtype + Kᗮ.subtype ∘ₗ (X : K →ₗ[𝕜] Kᗮ))

variable {K} in
theorem mem_graph_iff {X : K →L[𝕜] Kᗮ} {y : E} : y ∈ K.graph X ↔ ∃ x : K, (x : E) + X x = y :=
  Iff.rfl

instance [FiniteDimensional 𝕜 K] (X : K →L[𝕜] Kᗮ) : FiniteDimensional 𝕜 (K.graph X) :=
  LinearMap.finiteDimensional_range _

/-- A graph over `K` has the dimension of `K`: `x ↦ x + X x` is injective, `K` meeting `Kᗮ` only
in `0`. -/
theorem finrank_graph (X : K →L[𝕜] Kᗮ) :
    Module.finrank 𝕜 (K.graph X) = Module.finrank 𝕜 K := by
  refine LinearMap.finrank_range_of_inj fun x y hxy => ?_
  have h : (x : E) - y = (X y : E) - X x := by
    simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe] at hxy
    exact sub_eq_sub_iff_add_eq_add.2 (hxy.trans (add_comm _ _))
  have hK : (x : E) - y ∈ K := K.sub_mem x.2 y.2
  have hKo : (x : E) - y ∈ Kᗮ := h ▸ Kᗮ.sub_mem (X y).2 (X x).2
  have : (x : E) - y ∈ K ⊓ Kᗮ := ⟨hK, hKo⟩
  rw [K.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
  exact Subtype.ext this

/-- **The gap between a subspace and a graph over it** (Stewart–Sun Theorem I.5.5; the computation
behind [golub2013matrix] Theorems 7.3.1 and 8.2.2): for finite-dimensional `K` and
`X : K →L[𝕜] Kᗮ`, `gap K (graph X) = ‖X‖ / √(1 + ‖X‖²)`. The two subspaces have equal dimension, so
the gap is the one-sided `‖P_{K⊥} P_G‖`; on `g = x + X x ∈ G`, `P_{K⊥} g = X x` and
`‖g‖² = ‖x‖² + ‖X x‖²`, and `t ↦ t / √(1 + t²)` is increasing. -/
theorem gap_graph [FiniteDimensional 𝕜 K] (X : K →L[𝕜] Kᗮ) :
    K.gap (K.graph X) = ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) := by
  set G := K.graph X
  rw [gap_comm, gap_eq_norm_orthogonal_mul_of_finrank_eq G K (K.finrank_graph X)]
  set t := ‖X‖ with ht
  set γ := ‖Kᗮ.starProjection * G.starProjection‖ with hγ
  have ht0 : 0 ≤ t := norm_nonneg _
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  -- the two facts about `g = x + X x`
  have hproj : ∀ x : K, Kᗮ.starProjection ((x : E) + X x) = X x := fun x => by
    rw [map_add, (starProjection_apply_eq_zero_iff Kᗮ).2 (K.le_orthogonal_orthogonal x.2), zero_add,
      starProjection_eq_self_iff.2 (X x).2]
  have hnorm : ∀ x : K, ‖(x : E) + X x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖(X x : E)‖ ^ 2 := fun x => by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (x : E) (X x : E)
      ((K.mem_orthogonal _).1 (X x).2 x x.2)
    rw [pow_two, pow_two, pow_two, h]
  have hmem : ∀ x : K, (x : E) + X x ∈ G := fun x => ⟨x, rfl⟩
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    obtain ⟨x, hx⟩ := G.starProjection_apply_mem z
    rw [mul_apply_eq_comp, ← hx]
    change ‖Kᗮ.starProjection ((x : E) + X x)‖ ≤ _
    rw [hproj]
    have hle : ‖(X x : E)‖ * Real.sqrt (1 + t ^ 2) ≤ t * ‖(x : E) + X x‖ := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, mul_pow, hs2, hnorm]
      have h1 : ‖(X x : E)‖ ≤ t * ‖(x : E)‖ := by
        rw [Submodule.norm_coe, Submodule.norm_coe]
        exact X.le_opNorm x
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith
    calc ‖(X x : E)‖ ≤ t / Real.sqrt (1 + t ^ 2) * ‖(x : E) + X x‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hs]
          exact hle
      _ ≤ t / Real.sqrt (1 + t ^ 2) * ‖z‖ := by
          gcongr
          rw [show (x : E) + X x = G.starProjection z from hx]
          exact G.norm_starProjection_apply_le z
  · -- `‖X x‖² ≤ γ² (‖x‖² + ‖X x‖²)` for every `x`
    have hγ0 : 0 ≤ γ := norm_nonneg _
    have hbound : ∀ x : K, ‖(X x : E)‖ ^ 2 ≤ γ ^ 2 * (‖(x : E)‖ ^ 2 + ‖(X x : E)‖ ^ 2) := by
      intro x
      have h := (Kᗮ.starProjection * G.starProjection).le_opNorm ((x : E) + X x)
      rw [mul_apply_eq_comp, starProjection_eq_self_iff.2 (hmem x), hproj] at h
      rw [← hnorm, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_le_iff₀ hs]
    refine (pow_le_pow_iff_left₀ ht0 (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hs2]
    rcases le_or_gt 1 γ with hγ1 | hγ1
    · have h1 : 1 ≤ γ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)]
    · -- `‖X‖ ≤ γ / √(1 - γ²)`
      have hd : 0 < Real.sqrt (1 - γ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      have hd2 : Real.sqrt (1 - γ ^ 2) ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt (by nlinarith)
      have hX : t ≤ γ / Real.sqrt (1 - γ ^ 2) := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
        rw [div_mul_eq_mul_div, le_div_iff₀ hd]
        refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
        rw [mul_pow, mul_pow, hd2, ← Submodule.norm_coe, ← Submodule.norm_coe x]
        nlinarith [hbound x]
      have hX2 : t ^ 2 * (1 - γ ^ 2) ≤ γ ^ 2 := by
        rw [le_div_iff₀ hd] at hX
        have := pow_le_pow_left₀ (by positivity) hX 2
        rwa [mul_pow, hd2] at this
      nlinarith

end Graph

end Submodule

/-- **The ℓ¹ conditioning constant of a finite linearly independent family**: the coordinates of a
vector in the span are bounded by a fixed multiple of its norm.

The constant depends on the family and not only on its cardinality, and it is what measures how far
from orthonormal the family is. It comes from `LinearMap.exists_antilipschitzWith`, the injective
linear map here being `c ↦ ∑ c j • x j` on the finite-dimensional space `ι → 𝕜`; no finite
dimensionality of the ambient space is needed. -/
theorem LinearIndependent.exists_forall_sum_norm_le {𝕜 F ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] {x : ι → F}
    (hx : LinearIndependent 𝕜 x) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : ι → 𝕜, ∑ j, ‖c j‖ ≤ κ * ‖∑ j, c j • x j‖ := by
  have hker : LinearMap.ker (Fintype.linearCombination 𝕜 x) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    funext j
    exact Fintype.linearIndependent_iff.1 hx c
      (by simpa [Fintype.linearCombination_apply] using hc) j
  obtain ⟨K, hK, hanti⟩ := (Fintype.linearCombination 𝕜 x).exists_antilipschitzWith hker
  refine ⟨Fintype.card ι * K + 1, by positivity, fun c => ?_⟩
  have hc : ‖c‖ ≤ K * ‖∑ j, c j • x j‖ := by
    simpa [Fintype.linearCombination_apply] using ZeroHomClass.bound_of_antilipschitz _ hanti c
  calc ∑ j, ‖c j‖ ≤ ∑ _j : ι, ‖c‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm c j
    _ = Fintype.card ι * ‖c‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * (K * ‖∑ j, c j • x j‖) := by gcongr
    _ ≤ (Fintype.card ι * K + 1) * ‖∑ j, c j • x j‖ := by
        rw [← mul_assoc]
        nlinarith [norm_nonneg (∑ j, c j • x j)]
