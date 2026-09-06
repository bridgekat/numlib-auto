import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Numlib.Approximation.BestApprox

/-!
# The angle between a vector and a subspace, and the gap between subspaces

For a subspace `K` admitting an orthogonal projection `P_K` and a vector `u`, this file defines

* `K.cosAngle u = ‖P_K u‖ / ‖u‖`, the fraction of `u` that `K` captures;
* `K.sinAngle u = ‖u - P_K u‖ / ‖u‖`, the relative distance from `u` to `K`;
* `K.tanAngle u = ‖u - P_K u‖ / ‖P_K u‖`;
* `K.angle u = arccos (K.cosAngle u)`, a number in `[0, π / 2]`;

and, for two such subspaces, `K.gap L = ‖P_K - P_L‖`. Sharp eigenvalue bounds are inequalities about
the angle between an eigenvector and the subspace it is approximated from, and subspace-iteration
bounds are inequalities about the gap; neither notion exists in Mathlib, whose
`InnerProductGeometry.angle` is an angle between two vectors of a *real* inner product space.
Everything here is stated over `RCLike` and needs neither completeness nor finite dimension, only
`Submodule.HasOrthogonalProjection`.

Both notions follow [saad2011numerical], §3.1, the source of the bounds that use them.
[saad2011numerical] takes the acute angle between a vector and a subspace to be the smallest angle
`u` makes with any vector of `K`, and shows it is attained at `P_K u`; since `⟪u, P_K u⟫ = ‖P_K u‖ ^
2`, its cosine is `‖P_K u‖ / ‖u‖`, which is `cosAngle`. `angle_eq_angle_starProjection` records that
agreement against Mathlib's real-space `InnerProductGeometry.angle`, the only notion of angle the
library already had.

For the gap [saad2011numerical] writes `ω(K, L) = max {‖(1 - P_K) P_L‖, ‖(1 - P_L) P_K‖}` and states
that it equals `‖P_K - P_L‖`; that is the definition taken here, and it is the *symmetric* gap.
Either one-sided half of it — `sup {sin θ(x, K) | x ∈ L, ‖x‖ = 1}`, which is `‖(1 - P_K) P_L‖` — is
a different and generally smaller number; the two are not proved equal here, only the inequality
`sinAngle_le_gap` that the subspace-iteration bounds consume.

The names are earned rather than assumed: `Real.cos (K.angle u) = K.cosAngle u` holds outright, and
`Real.sin (K.angle u) = K.sinAngle u`, `Real.tan (K.angle u) = K.tanAngle u` hold for `u ≠ 0`
(`cos_angle`, `sin_angle`, `tan_angle`). They come from the Pythagorean identity `‖P_K u‖ ^ 2 + ‖u -
P_K u‖ ^ 2 = ‖u‖ ^ 2`, which is `norm_starProjection_sq_add_norm_sub_sq` here.

Each of the four is a quotient, so each has a value where its denominator vanishes, and a lemma
about it can be true for the wrong reason. At `u = 0` the three ratios are `0` and `K.angle u` is `π
/ 2`; `K.tanAngle u` is `0` again at `P_K u = 0`, where the honest value is infinite. So the
hypotheses below are exactly the ones the proofs need: `cosAngle_mul_norm`, `sinAngle_mul_norm`,
`sinAngle_of_mem` and `cosAngle_le_of_le` are true at the degenerate points too and carry none,
whereas `cosAngle_of_mem`, `sin_angle` and `sinAngle_eq_zero_iff` need `u ≠ 0` and
`tanAngle_mul_norm` needs `P_K u ≠ 0`.

The three `*_mul_norm` lemmas are the working form: a bound stated with an angle turns into a bound
on a norm and back. `sinAngle_eq_inv_norm_mul_infDist` is the metric reading, `K.sinAngle u` being
the distance from `u` to `K` relative to `‖u‖`, and it connects the angle to the best-approximation
vocabulary of `Numlib.Approximation.BestApprox`.

For the gap, `gap_le_one` comes from the pointwise bound `norm_starProjection_sub_apply_le`, `‖(P_K
- P_L) x‖ ≤ ‖x‖`, proved by splitting `P_K - P_L = P_K (1 - P_L) - P_Kᗮ P_L` into two orthogonal
pieces, and `finrank_eq_of_gap_lt_one` is the rank-constancy fact behind subspace iteration
([saad2011numerical], Thm 3.2): a gap below `1` makes `P_K` injective on `L`, and symmetry does the
rest.

The gap is then bounded from above in two steps. `gap_le_add` bounds it by the sum of the two
one-sided relative distances, and `gap_le_of_forall_norm_sub_le` bounds those when the two
subspaces are given by spanning families that are close vector by vector: `gap K L ≤ 3 κ δ` when
`‖w j - x j‖ ≤ δ` and `κ` is the ℓ¹ conditioning constant of the family `x`, which is
`LinearIndependent.exists_forall_sum_norm_le`. That is the quantitative continuity of a projector
in a spanning family, and it is what turns the per-vector estimates of subspace iteration into a
gap bound (`Krylov.gap_subspaceIterate_le`).
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `cos θ(u, K) = ‖P_K u‖ / ‖u‖`, the cosine of the angle between the vector `u` and the subspace
`K`: the fraction of the length of `u` that `K` captures. Junk (`0`) at `u = 0`. -/
noncomputable def cosAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖K.starProjection u‖ / ‖u‖

/-- `sin θ(u, K) = ‖u - P_K u‖ / ‖u‖`, the distance from `u` to the subspace `K` relative to `‖u‖`
(`sinAngle_eq_inv_norm_mul_infDist`). Junk (`0`) at `u = 0`. -/
noncomputable def sinAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖u - K.starProjection u‖ / ‖u‖

/-- `tan θ(u, K) = ‖u - P_K u‖ / ‖P_K u‖`, the form the Ritz-value and Lanczos bounds are stated in.
Junk (`0`) at `u = 0` and, less harmlessly, at `P_K u = 0`, where the angle is a right angle and the
honest value is infinite. -/
noncomputable def tanAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖u - K.starProjection u‖ / ‖K.starProjection u‖

/-- The angle `θ(u, K) = arccos (cos θ(u, K))` between a vector and a subspace, a number in `[0, π /
2]` (`angle_mem_Icc`). Junk (`π / 2`) at `u = 0`. -/
noncomputable def angle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  Real.arccos (K.cosAngle u)

section Vector

variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- Pythagoras for the orthogonal splitting `u = P_K u + (u - P_K u)`, in the orientation the
trigonometric identities of this file use. -/
theorem norm_starProjection_sq_add_norm_sub_sq (u : E) :
    ‖K.starProjection u‖ ^ 2 + ‖u - K.starProjection u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [← starProjection_orthogonal_val (K := K) u]
  exact (norm_sq_eq_add_norm_sq_starProjection u K).symm

/-- The part of `u` that `K` misses is no longer than `u`. -/
theorem norm_sub_starProjection_le (u : E) : ‖u - K.starProjection u‖ ≤ ‖u‖ := by
  rw [← starProjection_orthogonal_val (K := K) u]
  exact Kᗮ.norm_starProjection_apply_le u

/-- Testing against a vector of `K` only sees the `K`-component of the other argument. -/
theorem inner_starProjection_left_eq_of_mem (y : E) {z : E} (hz : z ∈ K) :
    (inner 𝕜 (K.starProjection y) z : 𝕜) = inner 𝕜 y z := by
  rw [inner_starProjection_left_eq_right, starProjection_eq_self_iff.2 hz]

/-- Cosines are nonnegative: the angle never exceeds a right angle. -/
theorem cosAngle_nonneg (u : E) : 0 ≤ K.cosAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Sines are nonnegative. -/
theorem sinAngle_nonneg (u : E) : 0 ≤ K.sinAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Tangents are nonnegative on `[0, pi / 2]`, junk value included. -/
theorem tanAngle_nonneg (u : E) : 0 ≤ K.tanAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The projection cannot lengthen `u`, so the cosine is at most `1`. -/
theorem cosAngle_le_one (u : E) : K.cosAngle u ≤ 1 :=
  div_le_one_of_le₀ (K.norm_starProjection_apply_le u) (norm_nonneg _)

/-- The distance from `u` to `K` is at most `‖u‖`, so the sine is at most `1`. -/
theorem sinAngle_le_one (u : E) : K.sinAngle u ≤ 1 :=
  div_le_one_of_le₀ (K.norm_sub_starProjection_le u) (norm_nonneg _)

/-- Pythagoras in trigonometric form. It fails at `u = 0`, where both sides of the definition
degenerate to `0`. -/
theorem cosAngle_sq_add_sinAngle_sq {u : E} (hu : u ≠ 0) :
    K.cosAngle u ^ 2 + K.sinAngle u ^ 2 = 1 := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  rw [cosAngle, sinAngle, div_pow, div_pow, ← add_div,
    K.norm_starProjection_sq_add_norm_sub_sq u, div_self (pow_ne_zero 2 hn)]

/-- Turning `cos θ(u, K)` back into a norm. True at `u = 0` as well, where both sides are `0`. -/
theorem cosAngle_mul_norm (u : E) : K.cosAngle u * ‖u‖ = ‖K.starProjection u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [cosAngle]
  · rw [cosAngle, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)]

/-- Turning `sin θ(u, K)` back into a norm: this is the form the eigenvalue bounds use, an angle
bound and a bound on `‖u - P_K u‖` being the same statement. True at `u = 0` as well. -/
theorem sinAngle_mul_norm (u : E) : K.sinAngle u * ‖u‖ = ‖u - K.starProjection u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [sinAngle]
  · rw [sinAngle, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)]

/-- Turning `tan θ(u, K)` back into a norm. Unlike its two companions this one really does need its
hypothesis: at `P_K u = 0` the left-hand side is `0` and the right-hand side is `‖u‖`. -/
theorem tanAngle_mul_norm {u : E} (hu : K.starProjection u ≠ 0) :
    K.tanAngle u * ‖K.starProjection u‖ = ‖u - K.starProjection u‖ :=
  div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)

/-- `tan = sin / cos`, at the level of the three ratios. At `P_K u = 0` both sides are `0`, so only
`u ≠ 0` is needed. -/
theorem tanAngle_eq_sinAngle_div_cosAngle {u : E} (hu : u ≠ 0) :
    K.tanAngle u = K.sinAngle u / K.cosAngle u := by
  rw [tanAngle, sinAngle, cosAngle, div_div_div_cancel_right₀ (norm_ne_zero_iff.2 hu)]

/-- Junk value at the origin: `‖0‖⁻¹ = 0`. -/
@[simp]
theorem cosAngle_zero : K.cosAngle 0 = 0 := by simp [cosAngle]

/-- Junk value at the origin, and *not* `1`: an angle bound proved only for `u = 0` says nothing. -/
@[simp]
theorem sinAngle_zero : K.sinAngle 0 = 0 := by simp [sinAngle]

/-- Junk value at the origin. -/
@[simp]
theorem tanAngle_zero : K.tanAngle 0 = 0 := by simp [tanAngle]

/-- The angle of the zero vector is the junk value `π / 2`, not `0`: `cosAngle` is `0 / 0` there.
Angle statements about a vector that may vanish must say so. -/
@[simp]
theorem angle_zero : K.angle 0 = Real.pi / 2 := by simp [angle]

/-- A vector of `K` makes a zero angle with `K`, so its cosine is `1` — except at `u = 0`. -/
theorem cosAngle_of_mem {u : E} (hu : u ≠ 0) (h : u ∈ K) : K.cosAngle u = 1 := by
  rw [cosAngle, K.norm_starProjection_apply h, div_self (norm_ne_zero_iff.2 hu)]

/-- A vector of `K` is at zero relative distance from `K`, at `u = 0` as well. -/
theorem sinAngle_of_mem {u : E} (h : u ∈ K) : K.sinAngle u = 0 := by
  rw [sinAngle, starProjection_eq_self_iff.2 h, sub_self, norm_zero, zero_div]

/-- A vector of `K` has zero tangent, at `u = 0` as well. -/
theorem tanAngle_of_mem {u : E} (h : u ∈ K) : K.tanAngle u = 0 := by
  rw [tanAngle, starProjection_eq_self_iff.2 h, sub_self, norm_zero, zero_div]

/-- A nonzero vector of `K` makes a zero angle with `K`. -/
theorem angle_of_mem {u : E} (hu : u ≠ 0) (h : u ∈ K) : K.angle u = 0 := by
  rw [angle, K.cosAngle_of_mem hu h, Real.arccos_one]

/-- A nonzero vector is at relative distance `0` from `K` exactly when it lies in `K`. The
hypothesis is needed: `K.sinAngle 0 = 0` whether or not `K` is trivial. -/
theorem sinAngle_eq_zero_iff {u : E} (hu : u ≠ 0) : K.sinAngle u = 0 ↔ u ∈ K := by
  refine ⟨fun h => ?_, K.sinAngle_of_mem⟩
  rw [sinAngle, div_eq_zero_iff] at h
  simp only [norm_eq_zero, sub_eq_zero] at h
  rcases h with h | h
  · exact starProjection_eq_self_iff.1 h.symm
  · exact absurd h hu

/-- The zero subspace captures nothing. -/
@[simp]
theorem cosAngle_bot (u : E) : (⊥ : Submodule 𝕜 E).cosAngle u = 0 := by simp [cosAngle]

/-- Junk value: the true tangent of a right angle is infinite, and `Real.tan (pi / 2) = 0` is the
matching junk on the other side. -/
@[simp]
theorem tanAngle_bot (u : E) : (⊥ : Submodule 𝕜 E).tanAngle u = 0 := by simp [tanAngle]

/-- Every vector, the origin included, makes a right angle with the zero subspace. -/
@[simp]
theorem angle_bot (u : E) : (⊥ : Submodule 𝕜 E).angle u = Real.pi / 2 := by simp [angle]

/-- Away from the origin every vector is at full relative distance from the zero subspace. -/
theorem sinAngle_bot {u : E} (hu : u ≠ 0) : (⊥ : Submodule 𝕜 E).sinAngle u = 1 := by
  rw [sinAngle, starProjection_bot, zero_apply, sub_zero, div_self (norm_ne_zero_iff.2 hu)]

/-- The whole space captures every nonzero vector entirely. -/
@[simp]
theorem cosAngle_top {u : E} (hu : u ≠ 0) : (⊤ : Submodule 𝕜 E).cosAngle u = 1 :=
  cosAngle_of_mem _ hu trivial

/-- Nothing is at a positive distance from the whole space. -/
@[simp]
theorem sinAngle_top (u : E) : (⊤ : Submodule 𝕜 E).sinAngle u = 0 :=
  sinAngle_of_mem _ trivial

/-- Nothing is at a positive distance from the whole space. -/
@[simp]
theorem tanAngle_top (u : E) : (⊤ : Submodule 𝕜 E).tanAngle u = 0 :=
  tanAngle_of_mem _ trivial

/-- A nonzero vector makes a zero angle with the whole space. -/
theorem angle_top {u : E} (hu : u ≠ 0) : (⊤ : Submodule 𝕜 E).angle u = 0 :=
  angle_of_mem _ hu trivial

/-- The cosine of the angle is the cosine of an angle: no hypothesis, because both sides are `0` at
`u = 0`. -/
@[simp]
theorem cos_angle (u : E) : Real.cos (K.angle u) = K.cosAngle u :=
  Real.cos_arccos (by linarith [K.cosAngle_nonneg u]) (K.cosAngle_le_one u)

/-- The sine of the angle is the sine of an angle. Here the hypothesis is real: at `u = 0` the
left-hand side is `Real.sin (π / 2) = 1` and the right-hand side is `0`. -/
theorem sin_angle {u : E} (hu : u ≠ 0) : Real.sin (K.angle u) = K.sinAngle u := by
  have h := K.cosAngle_sq_add_sinAngle_sq hu
  rw [angle, Real.sin_arccos, show (1 : ℝ) - K.cosAngle u ^ 2 = K.sinAngle u ^ 2 by linarith,
    Real.sqrt_sq (K.sinAngle_nonneg u)]

/-- The tangent of the angle is the tangent of an angle. At `P_K u = 0` both sides are `0`, the junk
value of `Real.tan (π / 2)` matching the junk value of `tanAngle`, so `u ≠ 0` suffices. -/
theorem tan_angle {u : E} (hu : u ≠ 0) : Real.tan (K.angle u) = K.tanAngle u := by
  rw [Real.tan_eq_sin_div_cos, K.sin_angle hu, K.cos_angle u,
    ← K.tanAngle_eq_sinAngle_div_cosAngle hu]

/-- The angle is nonnegative. -/
theorem angle_nonneg (u : E) : 0 ≤ K.angle u := Real.arccos_nonneg _

/-- The angle is at most a right angle, because the cosine is a quotient of norms and so is
nonnegative: an angle with a subspace is unsigned. -/
theorem angle_le_pi_div_two (u : E) : K.angle u ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.2 (K.cosAngle_nonneg u)

/-- The angle between a vector and a subspace is a right angle at most. -/
theorem angle_mem_Icc (u : E) : K.angle u ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨K.angle_nonneg u, K.angle_le_pi_div_two u⟩

/-- The projection realizes the distance to `K`, so `‖u - P_K u‖` *is* `dist(u, K)`. -/
theorem norm_sub_starProjection_eq_infDist (u : E) :
    ‖u - K.starProjection u‖ = Metric.infDist u (K : Set E) :=
  (isBestApprox_starProjection K u).norm_sub_eq_infDist

/-- `sin θ(u, K)` is the distance from `u` to `K`, relative to `‖u‖`. Both sides are `0` at `u = 0`,
where `Metric.infDist 0 K = 0` and `‖u‖⁻¹ = 0`. -/
theorem sinAngle_eq_inv_norm_mul_infDist (u : E) :
    K.sinAngle u = ‖u‖⁻¹ * Metric.infDist u (K : Set E) := by
  rw [sinAngle, K.norm_sub_starProjection_eq_infDist u, div_eq_inv_mul]

/-- The distance from `u` to `K`, read off an angle. -/
theorem infDist_eq_sinAngle_mul_norm (u : E) :
    Metric.infDist u (K : Set E) = K.sinAngle u * ‖u‖ := by
  rw [K.sinAngle_mul_norm u, K.norm_sub_starProjection_eq_infDist u]

end Vector

section RealAngle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `⟪u, P_K u⟫ = ‖P_K u‖ ^ 2`: the projection is orthogonal, so testing `u` against `P_K u` sees
only the part of `u` inside `K`. The real case of Mathlib's
`Submodule.re_inner_starProjection_eq_normSq`, in the argument order the angle uses. -/
theorem real_inner_starProjection_self (K : Submodule ℝ F) [K.HasOrthogonalProjection] (u : F) :
    inner ℝ u (K.starProjection u) = ‖K.starProjection u‖ ^ 2 := by
  rw [real_inner_comm]
  simpa using K.re_inner_starProjection_eq_normSq u

/-- Over `ℝ` the angle with a subspace is Mathlib's angle between `u` and its projection, which is
what makes `angle` the angle a reader of the eigenvalue literature expects: the acute angle between
`u` and the subspace is the smallest angle `u` makes with a vector of `K`, and it is attained at
`P_K u`. No hypothesis is needed — at `P_K u = 0` both sides are the junk `π / 2`, and at `u = 0`
both are `π / 2` as well. -/
theorem angle_eq_angle_starProjection (K : Submodule ℝ F) [K.HasOrthogonalProjection] (u : F) :
    K.angle u = InnerProductGeometry.angle u (K.starProjection u) := by
  rw [angle, InnerProductGeometry.angle, cosAngle, K.real_inner_starProjection_self u]
  rcases eq_or_ne (K.starProjection u) 0 with h | h
  · rw [h]
    simp
  · have hp : ‖K.starProjection u‖ ≠ 0 := norm_ne_zero_iff.2 h
    have hu : ‖u‖ ≠ 0 := by
      refine norm_ne_zero_iff.2 fun hu0 => h ?_
      rw [hu0, map_zero]
    congr 1
    field_simp

end RealAngle

section Mono

variable {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- A larger subspace captures more of `u`. -/
theorem norm_starProjection_le_of_le (h : K ≤ L) (u : E) :
    ‖K.starProjection u‖ ≤ ‖L.starProjection u‖ := by
  have h' : K.starProjection (L.starProjection u) = K.starProjection u := by
    simpa using DFunLike.congr_fun (starProjection_comp_starProjection_of_le h) u
  rw [← h']
  exact K.norm_starProjection_apply_le _

/-- A larger subspace misses less of `u`: `P_L u` is the best approximation of `u` from `L`, and
`P_K u` is a competitor. -/
theorem norm_sub_starProjection_le_of_le (h : K ≤ L) (u : E) :
    ‖u - L.starProjection u‖ ≤ ‖u - K.starProjection u‖ :=
  (isBestApprox_starProjection L u).2 _ (h (K.starProjection_apply_mem u))

/-- A larger subspace has a larger cosine. True at `u = 0`, where both sides are `0`. -/
theorem cosAngle_le_of_le (h : K ≤ L) (u : E) : K.cosAngle u ≤ L.cosAngle u := by
  rw [cosAngle, cosAngle]
  gcongr
  exact norm_starProjection_le_of_le h u

/-- A larger subspace has a smaller sine, that is, a smaller relative distance. True at `u = 0`,
where both sides are `0`. -/
theorem sinAngle_le_of_le (h : K ≤ L) (u : E) : L.sinAngle u ≤ K.sinAngle u := by
  rw [sinAngle, sinAngle]
  gcongr
  exact norm_sub_starProjection_le_of_le h u

/-- A larger subspace makes the angle no larger. -/
theorem angle_le_of_le (h : K ≤ L) (u : E) : L.angle u ≤ K.angle u :=
  Real.arccos_le_arccos (cosAngle_le_of_le h u)

/-- Monotonicity for the tangent. Here the hypothesis is needed, and it is the one on the *smaller*
subspace: for `K = ⊥` the left-hand side is a genuine ratio and the right-hand side is the junk
value `0`. -/
theorem tanAngle_le_of_le (h : K ≤ L) {u : E} (hu : K.starProjection u ≠ 0) :
    L.tanAngle u ≤ K.tanAngle u := by
  have hK : (0 : ℝ) < ‖K.starProjection u‖ := norm_pos_iff.2 hu
  have hL : ‖K.starProjection u‖ ≤ ‖L.starProjection u‖ := norm_starProjection_le_of_le h u
  rw [tanAngle, tanAngle, div_le_div_iff₀ (hK.trans_le hL) hK]
  exact mul_le_mul (norm_sub_starProjection_le_of_le h u) hL (norm_nonneg _) (norm_nonneg _)

end Mono

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

/-- The bridge between the two halves of this file, and the one-sided reading of the gap: every
vector of `L` is at relative distance at most `gap K L` from `K`. The one-sided quantity `sup {sin
θ(x, K) | x ∈ L, ‖x‖ = 1}` this bounds is in general strictly smaller than the gap. -/
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
