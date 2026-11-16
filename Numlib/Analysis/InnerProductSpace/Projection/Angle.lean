/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The angle between a vector and a subspace

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K$ be a
subspace of $E$ with an orthogonal projection $P_K$, and let $u \in E$. The angle $\theta(u, K)$
between $u$ and $K$ is described by the three ratios
$$\cos \theta(u, K) = \frac{\|P_K u\|}{\|u\|}, \qquad \sin \theta(u, K) = \frac{\|u - P_K
  u\|}{\|u\|}, \qquad \tan \theta(u, K) = \frac{\|u - P_K u\|}{\|P_K u\|},$$
and the angle itself is $\theta(u, K) = \arccos(\cos \theta(u, K)) \in [0, \pi/2]$. The cosine is
the fraction of the length of $u$ that $K$ captures, and the sine is the distance from $u$ to $K$
relative to $\|u\|$. The notion follows [saad2011numerical], §3.1, the source of the eigenvalue
bounds that use it. There the acute angle between a vector and a subspace is the smallest angle that
$u$ makes with a vector of $K$, and it is attained at $P_K u$. Since
$\langle u, P_K u \rangle = \|P_K u\|^2$, its cosine is $\|P_K u\| / \|u\|$.

The names of the ratios are justified by theorems: $\cos \theta(u, K)$ is the cosine of the angle
for every $u$, and the sine and the tangent are the sine and the tangent of the angle for
$u \neq 0$. These identities come from the Pythagorean identity
$\|P_K u\|^2 + \|u - P_K u\|^2 = \|u\|^2$. The module also proves the bounds
$0 \le \cos, \sin \le 1$, the values for $u \in K$, $K = 0$ and $K = E$, and the monotonicity of the
ratios in $K$.

## Main definitions

* `Submodule.cosAngle`: $\cos \theta(u, K) = \|P_K u\| / \|u\|$.
* `Submodule.sinAngle`: $\sin \theta(u, K) = \|u - P_K u\| / \|u\|$.
* `Submodule.tanAngle`: $\tan \theta(u, K) = \|u - P_K u\| / \|P_K u\|$.
* `Submodule.angle`: $\theta(u, K) = \arccos(\cos \theta(u, K))$.

## Main results

* `Submodule.norm_starProjection_sq_add_norm_sub_sq`: $\|P_K u\|^2 + \|u - P_K u\|^2 = \|u\|^2$.
* `Submodule.cosAngle_sq_add_sinAngle_sq`: $\cos^2 \theta(u, K) + \sin^2 \theta(u, K) = 1$ for
  $u \neq 0$.
* `Submodule.cosAngle_mul_norm`, `Submodule.sinAngle_mul_norm`, `Submodule.tanAngle_mul_norm`: the
  three ratios turned back into norms.
* `Submodule.cos_angle`, `Submodule.sin_angle`, `Submodule.tan_angle`: the three ratios are the
  cosine, the sine and the tangent of $\theta(u, K)$.
* `Submodule.angle_mem_Icc`: $0 \le \theta(u, K) \le \pi/2$.
* `Submodule.sinAngle_eq_zero_iff`: for $u \neq 0$, $\sin \theta(u, K) = 0$ if and only if
  $u \in K$.
* `Submodule.sinAngle_eq_inv_norm_mul_infDist`: $\sin \theta(u, K) = \operatorname{dist}(u, K) /
  \|u\|$.
* `Submodule.angle_eq_angle_starProjection`: over $\mathbb{R}$, $\theta(u, K)$ is the angle between
  the vectors $u$ and $P_K u$.
* `Submodule.cosAngle_le_of_le`, `Submodule.sinAngle_le_of_le`, `Submodule.angle_le_of_le`,
  `Submodule.tanAngle_le_of_le`: a larger subspace gives a larger cosine and a smaller sine, angle
  and tangent.

## Implementation notes

* Mathlib has no angle between a vector and a subspace. Its `InnerProductGeometry.angle` is the
  angle between two vectors of a real inner product space. `Submodule.angle_eq_angle_starProjection`
  relates the two notions.
* All results hold over `RCLike` and need neither completeness nor finite dimension of $E$, only
  `Submodule.HasOrthogonalProjection` for $K$.
* The projection $P_K u$ is `K.starProjection u`.
* Each ratio has a value where its denominator vanishes, because Lean sets $x / 0 = 0$. At $u = 0$
  the three ratios are $0$, and the angle is $\pi/2$. The tangent is also $0$ where $P_K u = 0$,
  although the true tangent of a right angle is infinite.
* So a result about the ratios can hold at a degenerate point for the wrong reason, and each result
  carries exactly the hypotheses that its proof needs. `Submodule.cosAngle_mul_norm`,
  `Submodule.sinAngle_mul_norm`, `Submodule.sinAngle_of_mem` and `Submodule.cosAngle_le_of_le` hold
  also at the degenerate points and have no nondegeneracy hypothesis. `Submodule.cosAngle_of_mem`
  and `Submodule.sin_angle` need a nonzero $u$, and `Submodule.tanAngle_mul_norm` needs a nonzero
  $P_K u$. `Submodule.sinAngle_eq_zero_iff` also assumes that $u$ is nonzero, although its
  equivalence holds at $u = 0$ too.
* The three results `Submodule.cosAngle_mul_norm`, `Submodule.sinAngle_mul_norm` and
  `Submodule.tanAngle_mul_norm` are the working form: they turn a bound on an angle into a bound on
  a norm, and back. `Submodule.sinAngle_eq_inv_norm_mul_infDist` connects the angle to the best
  approximation results of `Numlib.Analysis.Normed.Module.BestApprox`.
* The distance between two subspaces, `Submodule.gap`, is built on this module in
  `Numlib.Analysis.InnerProductSpace.Projection.Gap`.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$, and let
$u \in E$. The **cosine of the angle** between $u$ and $K$ is
$$\cos \theta(u, K) = \frac{\|P_K u\|}{\|u\|},$$
the fraction of the length of $u$ that $K$ captures.

At $u = 0$ the value is $0$, because Lean sets $x / 0 = 0$. -/
noncomputable def cosAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖K.starProjection u‖ / ‖u‖

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$, and let
$u \in E$. The **sine of the angle** between $u$ and $K$ is
$$\sin \theta(u, K) = \frac{\|u - P_K u\|}{\|u\|},$$
the distance from $u$ to $K$ relative to $\|u\|$ (`Submodule.sinAngle_eq_inv_norm_mul_infDist`).

At $u = 0$ the value is $0$, because Lean sets $x / 0 = 0$. -/
noncomputable def sinAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖u - K.starProjection u‖ / ‖u‖

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$, and let
$u \in E$. The **tangent of the angle** between $u$ and $K$ is
$$\tan \theta(u, K) = \frac{\|u - P_K u\|}{\|P_K u\|}.$$
The bounds on Ritz values and the Lanczos bounds are stated with this ratio.

The value is $0$ at $u = 0$ and also wherever $P_K u = 0$, because Lean sets $x / 0 = 0$. In the
second case the angle is a right angle and the true tangent is infinite. -/
noncomputable def tanAngle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  ‖u - K.starProjection u‖ / ‖K.starProjection u‖

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection, and let
$u \in E$. The **angle** between $u$ and $K$ is
$$\theta(u, K) = \arccos(\cos \theta(u, K)),$$
a number in $[0, \pi/2]$ (`Submodule.angle_mem_Icc`).

At $u = 0$ the value is $\pi/2$, because the cosine is $0$ there. -/
noncomputable def angle (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) : ℝ :=
  Real.arccos (K.cosAngle u)

section Vector

variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$. Then
for every $u \in E$,
$$\|P_K u\|^2 + \|u - P_K u\|^2 = \|u\|^2.$$
This is the theorem of Pythagoras for the orthogonal splitting $u = P_K u + (u - P_K u)$, in the
order that the trigonometric identities of this module use. -/
theorem norm_starProjection_sq_add_norm_sub_sq (u : E) :
    ‖K.starProjection u‖ ^ 2 + ‖u - K.starProjection u‖ ^ 2 = ‖u‖ ^ 2 := by
  rw [← starProjection_orthogonal_val (K := K) u]
  exact (norm_sq_eq_add_norm_sq_starProjection u K).symm

/-- For every $u \in E$, the part of $u$ that $K$ misses is no longer than $u$:
$\|u - P_K u\| \le \|u\|$. -/
theorem norm_sub_starProjection_le (u : E) : ‖u - K.starProjection u‖ ≤ ‖u‖ := by
  rw [← starProjection_orthogonal_val (K := K) u]
  exact Kᗮ.norm_starProjection_apply_le u

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$. Then
for every $y \in E$ and every $z \in K$,
$$\langle P_K y, z \rangle = \langle y, z \rangle.$$
So a test against a vector of $K$ sees only the component of the other argument in $K$. -/
theorem inner_starProjection_left_eq_of_mem (y : E) {z : E} (hz : z ∈ K) :
    (inner 𝕜 (K.starProjection y) z : 𝕜) = inner 𝕜 y z := by
  rw [inner_starProjection_left_eq_right, starProjection_eq_self_iff.2 hz]

/-- The cosine is nonnegative: $\cos \theta(u, K) \ge 0$ for every $u$. -/
theorem cosAngle_nonneg (u : E) : 0 ≤ K.cosAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The sine is nonnegative: $\sin \theta(u, K) \ge 0$ for every $u$. -/
theorem sinAngle_nonneg (u : E) : 0 ≤ K.sinAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The tangent is nonnegative: $\tan \theta(u, K) \ge 0$ for every $u$, including the points where
its value is the default $0$. -/
theorem tanAngle_nonneg (u : E) : 0 ≤ K.tanAngle u := div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The cosine is at most $1$: $\cos \theta(u, K) \le 1$ for every $u$, because the projection does
not lengthen $u$. -/
theorem cosAngle_le_one (u : E) : K.cosAngle u ≤ 1 :=
  div_le_one_of_le₀ (K.norm_starProjection_apply_le u) (norm_nonneg _)

/-- The sine is at most $1$: $\sin \theta(u, K) \le 1$ for every $u$, because the distance from $u$
to $K$ is at most $\|u\|$. -/
theorem sinAngle_le_one (u : E) : K.sinAngle u ≤ 1 :=
  div_le_one_of_le₀ (K.norm_sub_starProjection_le u) (norm_nonneg _)

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection, and let
$u \in E$ with $u \neq 0$. Then
$$\cos^2 \theta(u, K) + \sin^2 \theta(u, K) = 1.$$

The identity fails at $u = 0$, where both ratios are $0$. -/
theorem cosAngle_sq_add_sinAngle_sq {u : E} (hu : u ≠ 0) :
    K.cosAngle u ^ 2 + K.sinAngle u ^ 2 = 1 := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  rw [cosAngle, sinAngle, div_pow, div_pow, ← add_div,
    K.norm_starProjection_sq_add_norm_sub_sq u, div_self (pow_ne_zero 2 hn)]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$. Then
for every $u \in E$,
$$\cos \theta(u, K) \, \|u\| = \|P_K u\|.$$

The identity holds also at $u = 0$, where both sides are $0$. -/
theorem cosAngle_mul_norm (u : E) : K.cosAngle u * ‖u‖ = ‖K.starProjection u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [cosAngle]
  · rw [cosAngle, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$. Then
for every $u \in E$,
$$\sin \theta(u, K) \, \|u\| = \|u - P_K u\|.$$
The eigenvalue bounds use this form: a bound on the angle and a bound on $\|u - P_K u\|$ are the
same statement.

The identity holds also at $u = 0$, where both sides are $0$. -/
theorem sinAngle_mul_norm (u : E) : K.sinAngle u * ‖u‖ = ‖u - K.starProjection u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [sinAngle]
  · rw [sinAngle, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection $P_K$, and let
$u \in E$ with $P_K u \neq 0$. Then
$$\tan \theta(u, K) \, \|P_K u\| = \|u - P_K u\|.$$

Unlike `Submodule.cosAngle_mul_norm` and `Submodule.sinAngle_mul_norm`, this identity needs its
hypothesis: at $P_K u = 0$ the left-hand side is $0$ and the right-hand side is $\|u\|$. -/
theorem tanAngle_mul_norm {u : E} (hu : K.starProjection u ≠ 0) :
    K.tanAngle u * ‖K.starProjection u‖ = ‖u - K.starProjection u‖ :=
  div_mul_cancel₀ _ (norm_ne_zero_iff.2 hu)

/-- For $u \neq 0$, $\tan \theta(u, K) = \sin \theta(u, K) / \cos \theta(u, K)$. Where $P_K u = 0$
both sides are $0$, so the hypothesis $u \neq 0$ is enough. -/
theorem tanAngle_eq_sinAngle_div_cosAngle {u : E} (hu : u ≠ 0) :
    K.tanAngle u = K.sinAngle u / K.cosAngle u := by
  rw [tanAngle, sinAngle, cosAngle, div_div_div_cancel_right₀ (norm_ne_zero_iff.2 hu)]

/-- At the origin the cosine has the value $\cos \theta(0, K) = 0$, because Lean sets
$\|0\|^{-1} = 0$. -/
@[simp]
theorem cosAngle_zero : K.cosAngle 0 = 0 := by simp [cosAngle]

/-- At the origin the sine has the value $\sin \theta(0, K) = 0$, not $1$. So an angle bound that is
proved only for $u = 0$ says nothing. -/
@[simp]
theorem sinAngle_zero : K.sinAngle 0 = 0 := by simp [sinAngle]

/-- At the origin the tangent has the value $\tan \theta(0, K) = 0$. -/
@[simp]
theorem tanAngle_zero : K.tanAngle 0 = 0 := by simp [tanAngle]

/-- At the origin the angle has the value $\theta(0, K) = \pi/2$, not $0$, because the cosine is
$0 / 0 = 0$ there. A statement about the angle of a vector that can vanish must say so. -/
@[simp]
theorem angle_zero : K.angle 0 = Real.pi / 2 := by simp [angle]

/-- If $u \in K$ and $u \neq 0$, then $\cos \theta(u, K) = 1$. At $u = 0$ the cosine is $0$ instead.
-/
theorem cosAngle_of_mem {u : E} (hu : u ≠ 0) (h : u ∈ K) : K.cosAngle u = 1 := by
  rw [cosAngle, K.norm_starProjection_apply h, div_self (norm_ne_zero_iff.2 hu)]

/-- If $u \in K$, then $\sin \theta(u, K) = 0$. This holds also at $u = 0$. -/
theorem sinAngle_of_mem {u : E} (h : u ∈ K) : K.sinAngle u = 0 := by
  rw [sinAngle, starProjection_eq_self_iff.2 h, sub_self, norm_zero, zero_div]

/-- If $u \in K$, then $\tan \theta(u, K) = 0$. This holds also at $u = 0$. -/
theorem tanAngle_of_mem {u : E} (h : u ∈ K) : K.tanAngle u = 0 := by
  rw [tanAngle, starProjection_eq_self_iff.2 h, sub_self, norm_zero, zero_div]

/-- **Rescaling a vector does not change its angle with a subspace.** Let $K$ be a subspace of an
inner product space $E$ over $\mathbb{K}$ with an orthogonal projection, let $c \in \mathbb{K}$
with $c \neq 0$, and let $u \in E$. Then
$$\tan \theta(c u, K) = \tan \theta(u, K).$$
The numerator and the denominator of the tangent are both multiplied by $|c|$. This lets an
angle bound be stated at a normalized eigenvector and used at any multiple of it. -/
theorem tanAngle_smul {c : 𝕜} (hc : c ≠ 0) (u : E) : K.tanAngle (c • u) = K.tanAngle u := by
  rw [tanAngle, tanAngle, map_smul, ← smul_sub, norm_smul, norm_smul,
    mul_div_mul_left _ _ (norm_ne_zero_iff.2 hc)]

/-- If $u \in K$ and $u \neq 0$, then $\theta(u, K) = 0$. -/
theorem angle_of_mem {u : E} (hu : u ≠ 0) (h : u ∈ K) : K.angle u = 0 := by
  rw [angle, K.cosAngle_of_mem hu h, Real.arccos_one]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection, and let
$u \in E$ with $u \neq 0$. Then
$$\sin \theta(u, K) = 0 \iff u \in K.$$

The equivalence also holds at $u = 0$, because $\sin \theta(0, K) = 0$ and $0 \in K$, so the
hypothesis $u \neq 0$ is not needed for the statement to be true. -/
theorem sinAngle_eq_zero_iff {u : E} (hu : u ≠ 0) : K.sinAngle u = 0 ↔ u ∈ K := by
  refine ⟨fun h => ?_, K.sinAngle_of_mem⟩
  rw [sinAngle, div_eq_zero_iff] at h
  simp only [norm_eq_zero, sub_eq_zero] at h
  rcases h with h | h
  · exact starProjection_eq_self_iff.1 h.symm
  · exact absurd h hu

/-- The zero subspace captures nothing: $\cos \theta(u, \{0\}) = 0$ for every $u$. -/
@[simp]
theorem cosAngle_bot (u : E) : (⊥ : Submodule 𝕜 E).cosAngle u = 0 := by simp [cosAngle]

/-- The tangent of the angle with the zero subspace has the value $\tan \theta(u, \{0\}) = 0$ for
every $u$. The true tangent of a right angle is infinite, and Mathlib's value $\tan(\pi/2) = 0$
is the matching default value of `Real.tan`. -/
@[simp]
theorem tanAngle_bot (u : E) : (⊥ : Submodule 𝕜 E).tanAngle u = 0 := by simp [tanAngle]

/-- Every vector, the origin included, makes the angle $\theta(u, \{0\}) = \pi/2$ with the zero
subspace. -/
@[simp]
theorem angle_bot (u : E) : (⊥ : Submodule 𝕜 E).angle u = Real.pi / 2 := by simp [angle]

/-- Every vector $u \neq 0$ has $\sin \theta(u, \{0\}) = 1$: it is at full relative distance from
the zero subspace. -/
theorem sinAngle_bot {u : E} (hu : u ≠ 0) : (⊥ : Submodule 𝕜 E).sinAngle u = 1 := by
  rw [sinAngle, starProjection_bot, zero_apply, sub_zero, div_self (norm_ne_zero_iff.2 hu)]

/-- Every vector $u \neq 0$ has $\cos \theta(u, E) = 1$: the whole space captures it entirely. -/
@[simp]
theorem cosAngle_top {u : E} (hu : u ≠ 0) : (⊤ : Submodule 𝕜 E).cosAngle u = 1 :=
  cosAngle_of_mem _ hu trivial

/-- Every vector $u$ has $\sin \theta(u, E) = 0$: nothing is at a positive distance from the whole
space. -/
@[simp]
theorem sinAngle_top (u : E) : (⊤ : Submodule 𝕜 E).sinAngle u = 0 :=
  sinAngle_of_mem _ trivial

/-- Every vector $u$ has $\tan \theta(u, E) = 0$. -/
@[simp]
theorem tanAngle_top (u : E) : (⊤ : Submodule 𝕜 E).tanAngle u = 0 :=
  tanAngle_of_mem _ trivial

/-- Every vector $u \neq 0$ makes the angle $\theta(u, E) = 0$ with the whole space. -/
theorem angle_top {u : E} (hu : u ≠ 0) : (⊤ : Submodule 𝕜 E).angle u = 0 :=
  angle_of_mem _ hu trivial

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection. Then for
every $u \in E$,
$$\cos(\theta(u, K)) = \frac{\|P_K u\|}{\|u\|},$$
that is, the ratio `Submodule.cosAngle` is the cosine of the angle `Submodule.angle`.

No hypothesis is needed: at $u = 0$ both sides are $0$. -/
@[simp]
theorem cos_angle (u : E) : Real.cos (K.angle u) = K.cosAngle u :=
  Real.cos_arccos (by linarith [K.cosAngle_nonneg u]) (K.cosAngle_le_one u)

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection, and let
$u \in E$ with $u \neq 0$. Then the ratio `Submodule.sinAngle` is the sine of the angle
`Submodule.angle`:
$$\sin(\theta(u, K)) = \frac{\|u - P_K u\|}{\|u\|}.$$

The hypothesis is needed: at $u = 0$ the left-hand side is $\sin(\pi/2) = 1$ and the right-hand
side is $0$. -/
theorem sin_angle {u : E} (hu : u ≠ 0) : Real.sin (K.angle u) = K.sinAngle u := by
  have h := K.cosAngle_sq_add_sinAngle_sq hu
  rw [angle, Real.sin_arccos, show (1 : ℝ) - K.cosAngle u ^ 2 = K.sinAngle u ^ 2 by linarith,
    Real.sqrt_sq (K.sinAngle_nonneg u)]

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection, and let
$u \in E$ with $u \neq 0$. Then the ratio `Submodule.tanAngle` is the tangent of the angle
`Submodule.angle`:
$$\tan(\theta(u, K)) = \frac{\|u - P_K u\|}{\|P_K u\|}.$$

Where $P_K u = 0$ both sides are $0$: Mathlib sets $\tan(\pi/2) = 0$, which matches the default
value of the ratio. So the hypothesis $u \neq 0$ is enough. -/
theorem tan_angle {u : E} (hu : u ≠ 0) : Real.tan (K.angle u) = K.tanAngle u := by
  rw [Real.tan_eq_sin_div_cos, K.sin_angle hu, K.cos_angle u,
    ← K.tanAngle_eq_sinAngle_div_cosAngle hu]

/-- The angle is nonnegative: $\theta(u, K) \ge 0$ for every $u$. -/
theorem angle_nonneg (u : E) : 0 ≤ K.angle u := Real.arccos_nonneg _

/-- The angle is at most a right angle: $\theta(u, K) \le \pi/2$ for every $u$. The reason is that
the cosine is a quotient of norms and so is nonnegative; an angle with a subspace has no sign. -/
theorem angle_le_pi_div_two (u : E) : K.angle u ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.2 (K.cosAngle_nonneg u)

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection. Then for
every $u \in E$,
$$0 \le \theta(u, K) \le \pi/2.$$
-/
theorem angle_mem_Icc (u : E) : K.angle u ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨K.angle_nonneg u, K.angle_le_pi_div_two u⟩

/-- The projection realizes the distance to $K$: $\|u - P_K u\| = \operatorname{dist}(u, K)$ for
every $u \in E$, where the distance is `Metric.infDist`. -/
theorem norm_sub_starProjection_eq_infDist (u : E) :
    ‖u - K.starProjection u‖ = Metric.infDist u (K : Set E) :=
  (isBestApprox_starProjection K u).norm_sub_eq_infDist

/-- Let $K$ be a subspace of an inner product space $E$ with an orthogonal projection. Then for
every $u \in E$,
$$\sin \theta(u, K) = \|u\|^{-1} \operatorname{dist}(u, K),$$
the distance from $u$ to $K$ relative to $\|u\|$.

The distance is `Metric.infDist`. The identity holds also at $u = 0$, where
$\operatorname{dist}(0, K) = 0$ and Lean sets $\|0\|^{-1} = 0$. -/
theorem sinAngle_eq_inv_norm_mul_infDist (u : E) :
    K.sinAngle u = ‖u‖⁻¹ * Metric.infDist u (K : Set E) := by
  rw [sinAngle, K.norm_sub_starProjection_eq_infDist u, div_eq_inv_mul]

/-- The distance from $u$ to $K$ is $\operatorname{dist}(u, K) = \sin \theta(u, K) \, \|u\|$ for
every $u \in E$. -/
theorem infDist_eq_sinAngle_mul_norm (u : E) :
    Metric.infDist u (K : Set E) = K.sinAngle u * ‖u‖ := by
  rw [K.sinAngle_mul_norm u, K.norm_sub_starProjection_eq_infDist u]

end Vector

section RealAngle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Let $K$ be a subspace of a real inner product space $F$ with an orthogonal projection $P_K$.
Then $\langle u, P_K u \rangle = \|P_K u\|^2$ for every $u \in F$: the projection is orthogonal,
so a test of $u$ against $P_K u$ sees only the part of $u$ in $K$. This is the real case of
Mathlib's `Submodule.re_inner_starProjection_eq_normSq`, in the order of arguments that the
angle uses. -/
theorem real_inner_starProjection_self (K : Submodule ℝ F) [K.HasOrthogonalProjection] (u : F) :
    inner ℝ u (K.starProjection u) = ‖K.starProjection u‖ ^ 2 := by
  rw [real_inner_comm]
  simpa using K.re_inner_starProjection_eq_normSq u

/-- Let $K$ be a subspace of a real inner product space $F$ with an orthogonal projection $P_K$.
Then for every $u \in F$, the angle between $u$ and $K$ is the angle between the vectors $u$ and
$P_K u$:
$$\theta(u, K) = \angle(u, P_K u).$$
So `Submodule.angle` is the angle that the eigenvalue literature uses: the acute angle between
$u$ and the subspace is the smallest angle that $u$ makes with a vector of $K$, and it is
attained at $P_K u$.

The angle between two vectors is Mathlib's `InnerProductGeometry.angle`. No hypothesis is
needed: at $P_K u = 0$, and in particular at $u = 0$, both sides are $\pi/2$. -/
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

/-- If $K \le L$, then $\|P_K u\| \le \|P_L u\|$ for every $u$: a larger subspace captures more of
$u$. -/
theorem norm_starProjection_le_of_le (h : K ≤ L) (u : E) :
    ‖K.starProjection u‖ ≤ ‖L.starProjection u‖ := by
  have h' : K.starProjection (L.starProjection u) = K.starProjection u := by
    simpa using DFunLike.congr_fun (starProjection_comp_starProjection_of_le h) u
  rw [← h']
  exact K.norm_starProjection_apply_le _

/-- If $K \le L$, then $\|u - P_L u\| \le \|u - P_K u\|$ for every $u$: a larger subspace misses
less of $u$. The reason is that $P_L u$ is the best approximation of $u$ from $L$, and $P_K u$
is a competitor. -/
theorem norm_sub_starProjection_le_of_le (h : K ≤ L) (u : E) :
    ‖u - L.starProjection u‖ ≤ ‖u - K.starProjection u‖ :=
  (isBestApprox_starProjection L u).2 _ (h (K.starProjection_apply_mem u))

/-- Let $K \le L$ be subspaces of an inner product space $E$, both with orthogonal projections. Then
for every $u \in E$,
$$\cos \theta(u, K) \le \cos \theta(u, L).$$

The inequality holds also at $u = 0$, where both sides are $0$. -/
theorem cosAngle_le_of_le (h : K ≤ L) (u : E) : K.cosAngle u ≤ L.cosAngle u := by
  rw [cosAngle, cosAngle]
  gcongr
  exact norm_starProjection_le_of_le h u

/-- Let $K \le L$ be subspaces of an inner product space $E$, both with orthogonal projections. Then
for every $u \in E$,
$$\sin \theta(u, L) \le \sin \theta(u, K),$$
so the larger subspace has the smaller relative distance from $u$.

The inequality holds also at $u = 0$, where both sides are $0$. -/
theorem sinAngle_le_of_le (h : K ≤ L) (u : E) : L.sinAngle u ≤ K.sinAngle u := by
  rw [sinAngle, sinAngle]
  gcongr
  exact norm_sub_starProjection_le_of_le h u

/-- Let $K \le L$ be subspaces of an inner product space $E$, both with orthogonal projections. Then
for every $u \in E$,
$$\theta(u, L) \le \theta(u, K).$$
-/
theorem angle_le_of_le (h : K ≤ L) (u : E) : L.angle u ≤ K.angle u :=
  Real.arccos_le_arccos (cosAngle_le_of_le h u)

/-- Let $K \le L$ be subspaces of an inner product space $E$, both with orthogonal projections, and
let $u \in E$ with $P_K u \neq 0$. Then
$$\tan \theta(u, L) \le \tan \theta(u, K).$$

The hypothesis is needed, and it is on the smaller subspace: for $K = \{0\}$ the left-hand side
is a true ratio, and the right-hand side is the default value $0$. -/
theorem tanAngle_le_of_le (h : K ≤ L) {u : E} (hu : K.starProjection u ≠ 0) :
    L.tanAngle u ≤ K.tanAngle u := by
  have hK : (0 : ℝ) < ‖K.starProjection u‖ := norm_pos_iff.2 hu
  have hL : ‖K.starProjection u‖ ≤ ‖L.starProjection u‖ := norm_starProjection_le_of_le h u
  rw [tanAngle, tanAngle, div_le_div_iff₀ (hK.trans_le hL) hK]
  exact mul_le_mul (norm_sub_starProjection_le_of_le h u) hL (norm_nonneg _) (norm_nonneg _)

end Mono

end Submodule
