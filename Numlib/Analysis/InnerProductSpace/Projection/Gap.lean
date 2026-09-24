import Numlib.Analysis.InnerProductSpace.Projection.Angle

/-!
# The gap between two subspaces

For two subspaces `K`, `L` of an inner product space admitting orthogonal projections `P_K`, `P_L`,
the *gap* `K.gap L = ‖P_K - P_L‖` is the distance between them in the metric the subspace-iteration
bounds are measured in. Mathlib has no such notion. Everything is stated over `RCLike` and needs
neither completeness nor finite dimension, only `Submodule.HasOrthogonalProjection`.

The definition follows [saad2011numerical], §3.1, the source of the bounds that use it, which
writes `ω(K, L) = max {‖(1 - P_K) P_L‖, ‖(1 - P_L) P_K‖}` and states that it equals `‖P_K - P_L‖`;
the latter is the definition taken here, and it is the *symmetric* gap. Either one-sided half of
it — `sup {sin θ(x, K) | x ∈ L, ‖x‖ = 1}`, which is `‖(1 - P_K) P_L‖` — is a different and
generally smaller number; the two are not proved equal here, only the inequality `sinAngle_le_gap`
(the bridge to the angles of `Numlib.Analysis.InnerProductSpace.Projection.Angle`) that the
subspace-iteration bounds consume.

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

/-- Two orthogonal projections never move a vector by more than its own length. Split `P_K x - P_L x
= P_K (x - P_L x) - P_{Kᗮ} (P_L x)` into a piece of `K` and a piece of `Kᗮ`: the two are orthogonal,
each is shorter than the corresponding piece of the splitting of `x` along `L`, and Pythagoras over
`L` closes the estimate. -/
theorem norm_starProjection_sub_apply_le (x : E) :
    ‖K.starProjection x - L.starProjection x‖ ≤ ‖x‖ := by
  have hinner : inner 𝕜 (K.starProjection (x - L.starProjection x))
      (Kᗮ.starProjection (L.starProjection x)) = 0 :=
    (K.mem_orthogonal _).1 (Kᗮ.starProjection_apply_mem _) _ (K.starProjection_apply_mem _)
  have hsplit : K.starProjection x - L.starProjection x =
      K.starProjection (x - L.starProjection x) + -Kᗮ.starProjection (L.starProjection x) := by
    rw [map_sub, starProjection_orthogonal_val]
    abel
  have hpyth : ‖K.starProjection x - L.starProjection x‖ ^ 2 =
      ‖K.starProjection (x - L.starProjection x)‖ ^ 2
        + ‖Kᗮ.starProjection (L.starProjection x)‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)
      (K.starProjection (x - L.starProjection x)) (-Kᗮ.starProjection (L.starProjection x))
      (by rw [inner_neg_right, hinner, neg_zero])
    rw [hsplit, pow_two, pow_two, pow_two, h, norm_neg]
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
