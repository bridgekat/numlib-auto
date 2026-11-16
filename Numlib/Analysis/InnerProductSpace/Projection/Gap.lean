/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.SingularValues

/-!
# The gap between two subspaces

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $K$ and
$L$ be subspaces of $E$ with orthogonal projections $P_K$ and $P_L$. The **gap** between $K$ and $L$
is the operator norm
$$\operatorname{gap}(K, L) = \|P_K - P_L\|.$$
It is the distance between subspaces in which the bounds for subspace iteration are measured, and it
is the subspace distance $\operatorname{dist}(S_1, S_2) = \|P_1 - P_2\|_2$ of [golub2013matrix],
§2.5.3. The definition follows [saad2011numerical], §3.1, the source of the bounds that use it. That
source writes $\omega(K, L) = \max\{\|(1 - P_K) P_L\|, \|(1 - P_L) P_K\|\}$ and states that it
equals $\|P_K - P_L\|$. This module takes the second expression, the symmetric gap, as the
definition, and proves that the two agree. The quantities $\|P_{L^\perp} P_K\|$ and
$\|P_{K^\perp} P_L\|$ are the two **one-sided gaps**.

The gap is a metric on the subspaces with an orthogonal projection, and it is at most $1$. Two
finite-dimensional subspaces at gap less than $1$ have the same dimension. For subspaces of equal
finite dimension, the gap equals either one-sided gap, and it is $1$ exactly when one subspace meets
the orthogonal complement of the other. The one-sided gap is $\sqrt{1 - \sigma_{\min}^2}$, where
$\sigma_{\min}$ is the least singular value of the restricted projection $P_L|_K \colon K \to L$.
Finally, the gap between $K$ and the graph $\{x + Xx : x \in K\}$ of a map $X \colon K \to K^\perp$
is $\|X\| / \sqrt{1 + \|X\|^2}$.

## Main definitions

* `Submodule.gap`: the gap $\|P_K - P_L\|$.
* `Submodule.orthogonalProjectionRestrict`: the restricted projection $P_F|_G \colon G \to F$.
* `Submodule.graph`: the graph $\{x + Xx : x \in K\}$ of a map $X \colon K \to K^\perp$.

## Main results

* `Submodule.gap_comm`, `Submodule.gap_eq_zero_iff`, `Submodule.gap_le_one`: the gap is symmetric,
  vanishes exactly when $K = L$, and is at most $1$.
* `Submodule.norm_starProjection_sub_apply_le`: $\|(P_K - P_L) x\| \le \|x\|$ for every $x$.
* `Submodule.sinAngle_le_gap`: every $x \in L$ satisfies
  $\sin \theta(x, K) \le \operatorname{gap}(K, L)$.
* `Submodule.finrank_eq_of_gap_lt_one`: finite-dimensional subspaces at gap less than $1$ have the
  same dimension.
* `Submodule.gap_eq_max_norm_orthogonal_mul`: the gap is the larger of the two one-sided gaps.
* `Submodule.gap_le_max`: if every vector of $K$ is within relative distance $a$ of $L$ and every
  vector of $L$ is within relative distance $b$ of $K$, then
  $\operatorname{gap}(K, L) \le \max\{a, b\}$.
* `Submodule.gap_le_of_forall_norm_sub_le`: if $K$ and $L$ are spanned by families $x$ and $w$ with
  $\|w_j - x_j\| \le \delta$, then $\operatorname{gap}(K, L) \le 2 \kappa \delta$, where $\kappa$ is
  a conditioning constant of $x$.
* `Submodule.norm_orthogonal_mul_sq_eq_one_sub_sq_singularValues`: $\|P_{L^\perp} P_K\|^2 = 1 -
  \sigma_{\min}(P_L|_K)^2$.
* `Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`: for $\dim K = \dim L$, the gap is the
  one-sided gap $\|P_{L^\perp} P_K\|$.
* `Submodule.gap_eq_one_iff_of_finrank_eq`: for $\dim K = \dim L$, the gap is $1$ if and only if
  $K \cap L^\perp \neq 0$ ([golub2013matrix], §2.5.3).
* `Submodule.gap_span_singleton_eq_sinAngle`: the gap between two lines is the sine of their angle.
* `Submodule.gap_graph`: $\operatorname{gap}(K, \operatorname{graph} X) = \|X\| / \sqrt{1 +
  \|X\|^2}$.

## Implementation notes

* All results hold over `RCLike`. They need neither completeness nor finite dimension of $E$, only
  `Submodule.HasOrthogonalProjection` for the subspaces, and finite dimension of the two subspaces
  where singular values appear.
* The projection $P_K$ is `K.starProjection`, a continuous linear map on $E$, and the one-sided gap
  $\|P_{L^\perp} P_K\|$ is `‖Lᗮ.starProjection * K.starProjection‖`.
* The theory for equal dimensions uses no coordinates, no orthonormal bases and no CS decomposition.
  Its main tool is the restricted projection $P_L|_K$, whose least singular value measures how far
  $K$ is from $L$, together with the identity for stacked isometries of
  `Numlib.Analysis.InnerProductSpace.SingularValues`.
* The matrix forms, Theorem 2.5.1 and (7.3.19) of [golub2013matrix], are corollaries in
  `Numlib.Analysis.Matrix.SingularValues`. The principal angles of
  `Numlib.Analysis.InnerProductSpace.PrincipalAngles` are the singular values of the same restricted
  projection.
* Mathlib has no notion of a gap between subspaces. Mathlib's `LinearMap.graph` is a subspace of a
  product $E \times F$ and differs from `Submodule.graph`.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $K$ and $L$ be subspaces of an inner product space $E$ with orthogonal projections $P_K$ and
$P_L$. The **gap** between $K$ and $L$ is the operator norm
$$\operatorname{gap}(K, L) = \|P_K - P_L\|.$$
It is the distance between subspaces in which the bounds for subspace iteration are measured. It
is symmetric (`Submodule.gap_comm`), vanishes exactly when $K = L$
(`Submodule.gap_eq_zero_iff`), and is at most $1$ (`Submodule.gap_le_one`). -/
noncomputable def gap (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : ℝ :=
  ‖K.starProjection - L.starProjection‖

section Gap

variable (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- The gap is nonnegative: $\operatorname{gap}(K, L) \ge 0$, because it is a norm. -/
theorem gap_nonneg : 0 ≤ K.gap L := norm_nonneg _

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. Then the gap
is symmetric:
$$\operatorname{gap}(K, L) = \operatorname{gap}(L, K).$$
-/
theorem gap_comm : K.gap L = L.gap K := norm_sub_rev _ _

/-- Let $K$ be a subspace of an inner product space with an orthogonal projection. Then
$\operatorname{gap}(K, K) = 0$. -/
@[simp]
theorem gap_self : K.gap K = 0 := by rw [gap, sub_self, norm_zero]

/-- The gap bounds the difference of the projections pointwise: $\|P_K x - P_L x\| \le
\operatorname{gap}(K, L) \, \|x\|$ for every $x \in E$. -/
theorem norm_starProjection_sub_le_gap_mul (x : E) :
    ‖K.starProjection x - L.starProjection x‖ ≤ K.gap L * ‖x‖ := by
  simpa [gap] using (K.starProjection - L.starProjection).le_opNorm x

/-- Let $K$ and $L$ be subspaces of an inner product space $E$ with orthogonal projections $P_K$ and
$P_L$. Then for every $x \in E$,
$$\|P_K x - P_L x\|^2 = \|P_K (x - P_L x)\|^2 + \|P_{K^\perp} (P_L x)\|^2.$$
The identity comes from the splitting $P_K x - P_L x = P_K (x - P_L x) - P_{K^\perp} (P_L x)$
into a vector of $K$ and a vector of $K^\perp$. -/
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

/-- Let $K$ and $L$ be subspaces of an inner product space $E$ with orthogonal projections $P_K$ and
$P_L$. Then for every $x \in E$,
$$\|P_K x - P_L x\| \le \|x\|.$$

The proof splits $P_K x - P_L x = P_K (x - P_L x) - P_{K^\perp} (P_L x)$ into a vector of $K$
and a vector of $K^\perp$. Each piece is no longer than the corresponding piece of the splitting
of $x$ along $L$, and the theorem of Pythagoras for this splitting gives the bound. -/
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

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. Then
$$\operatorname{gap}(K, L) \le 1.$$
-/
theorem gap_le_one : K.gap L ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using K.norm_starProjection_sub_apply_le L x

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. Then every
$x \in L$ satisfies
$$\sin \theta(x, K) \le \operatorname{gap}(K, L).$$
So every vector of $L$ is within relative distance $\operatorname{gap}(K, L)$ of $K$. This
connects the gap with the angles of `Submodule.sinAngle`.

The bounded quantity $\sup \{\sin \theta(x, K) : x \in L, \|x\| = 1\}$ is a one-sided reading of
the gap. It equals the gap when the dimensions are equal
(`Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`), but it can be strictly smaller when they
differ. -/
theorem sinAngle_le_gap {x : E} (hx : x ∈ L) : K.sinAngle x ≤ K.gap L := by
  rcases eq_or_ne x 0 with rfl | hne
  · simpa using K.gap_nonneg L
  · rw [sinAngle, div_le_iff₀ (norm_pos_iff.2 hne)]
    have h : ‖x - K.starProjection x‖ = ‖K.starProjection x - L.starProjection x‖ := by
      rw [starProjection_eq_self_iff.2 hx, norm_sub_rev]
    rw [h]
    exact K.norm_starProjection_sub_le_gap_mul L x

/-- The gap from the zero subspace is the norm of the projection:
$\operatorname{gap}(\{0\}, K) = \|P_K\|$. -/
theorem gap_bot : (⊥ : Submodule 𝕜 E).gap K = ‖K.starProjection‖ := by
  rw [gap, starProjection_bot, zero_sub, norm_neg]

/-- Let $K$ be a subspace of an inner product space with an orthogonal projection, with
$K \neq \{0\}$. Then
$$\operatorname{gap}(\{0\}, K) = 1,$$
the largest possible value of the gap. -/
theorem gap_bot_eq_one (hK : K ≠ ⊥) : (⊥ : Submodule 𝕜 E).gap K = 1 := by
  rw [gap_bot, K.norm_starProjection hK]

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. Then
$$\operatorname{gap}(K, L) = 0 \iff K = L.$$
So the gap is a metric on the subspaces with an orthogonal projection, not only a pseudometric. -/
theorem gap_eq_zero_iff : K.gap L = 0 ↔ K = L := by
  rw [gap, norm_eq_zero, sub_eq_zero]
  refine ⟨fun h => ?_, ?_⟩
  · ext v
    rw [← starProjection_eq_self_iff (K := K), ← starProjection_eq_self_iff (K := L), h]
  · rintro rfl
    rfl

/-- If $\operatorname{gap}(K, L) < 1$, then $P_K$ is injective on $L$: every $x \in L$ with
$P_K x = 0$ is $0$. A nonzero $x \in L$ with $P_K x = 0$ would satisfy
$\|(P_L - P_K) x\| = \|x\|$. -/
theorem eq_zero_of_starProjection_eq_zero_of_gap_lt_one (h : K.gap L < 1) {x : E} (hx : x ∈ L)
    (hx0 : K.starProjection x = 0) : x = 0 := by
  have h1 : ‖K.starProjection x - L.starProjection x‖ = ‖x‖ := by
    rw [hx0, zero_sub, norm_neg, starProjection_eq_self_iff.2 hx]
  have h2 := K.norm_starProjection_sub_le_gap_mul L x
  rw [h1] at h2
  by_contra hne
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hne
  nlinarith

/-- If $K$ is finite-dimensional and $\operatorname{gap}(K, L) < 1$, then $\dim L \le \dim K$. This
is one half of `Submodule.finrank_eq_of_gap_lt_one`. -/
theorem finrank_le_of_gap_lt_one [FiniteDimensional 𝕜 K] (h : K.gap L < 1) :
    Module.finrank 𝕜 L ≤ Module.finrank 𝕜 K := by
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp L.subtype)
    (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun x hx => ?_))
  refine Subtype.ext (K.eq_zero_of_starProjection_eq_zero_of_gap_lt_one L h x.2 ?_)
  rw [starProjection_apply]
  simpa using congrArg Subtype.val hx

/-- Let $K$ and $L$ be finite-dimensional subspaces of an inner product space. If
$\operatorname{gap}(K, L) < 1$, then
$$\dim K = \dim L.$$
So a continuous family of orthogonal projections has constant rank. This is Theorem 3.2 of
[saad2011numerical]. -/
theorem finrank_eq_of_gap_lt_one [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (h : K.gap L < 1) : Module.finrank 𝕜 K = Module.finrank 𝕜 L :=
  le_antisymm (L.finrank_le_of_gap_lt_one K (by rwa [gap_comm]))
    (K.finrank_le_of_gap_lt_one L h)

/-- Let $K$, $L$ and $L'$ be subspaces of an inner product space with orthogonal projections. If
$L = L'$, then $\operatorname{gap}(K, L) = \operatorname{gap}(K, L')$.

The instance argument of `Submodule.gap` depends on the subspace, so a rewrite in the second
argument needs this lemma. -/
theorem gap_congr {L' : Submodule 𝕜 E} [L'.HasOrthogonalProjection] (h : L = L') :
    K.gap L = K.gap L' := by subst h; rfl

variable {K L} in
/-- Let $K$, $K'$, $L$ and $L'$ be subspaces of an inner product space with orthogonal projections.
If $K = K'$ and $L = L'$, then $\operatorname{gap}(K, L) = \operatorname{gap}(K', L')$. This is
`Submodule.gap_congr` in both arguments, across the instances of
`Submodule.HasOrthogonalProjection`. -/
theorem gap_congr₂ {K' L' : Submodule 𝕜 E} [K'.HasOrthogonalProjection]
    [L'.HasOrthogonalProjection] (hK : K = K') (hL : L = L') : K.gap L = K'.gap L' := by
  subst hK hL; rfl

/-- **The projection onto $K$ is small on $L^\perp$ when $K$ is close to $L$.** Let $K$ and $L$ be
subspaces of an inner product space with orthogonal projections $P_K$ and $P_L$, and let
$a \ge 0$. If $\|u - P_L u\| \le a \|u\|$ for every $u \in K$, then
$$\|P_K w\| \le a \|w\| \quad \text{for every } w \in L^\perp.$$

The hypothesis is about vectors of $K$ and the conclusion is about vectors of $L^\perp$. The
passage between them is the identity $\|P_K w\|^2 = \langle P_K w - P_L (P_K w), w \rangle$, in
which the term with $P_L$ costs nothing because $w \perp L$. This is the step of
`Submodule.gap_eq_max_norm_orthogonal_mul` that is not immediate. -/
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

end Gap

/-! ### The one-sided gaps -/

section OneSided

variable (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- Let $K$ and $L$ be subspaces of an inner product space $E$ with orthogonal projections $P_K$ and
$P_L$. Then for every $z \in E$,
$$\|P_K z - P_L z\|^2 = \operatorname{Re} \langle P_K z, z - P_L z \rangle + \operatorname{Re}
  \langle P_L z, z - P_K z \rangle.$$
This is the display in §2.5.1 of [golub2013matrix] behind the uniqueness of the orthogonal
projection. -/
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

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. Then the
one-sided gap is at most the gap:
$$\|P_{L^\perp} P_K\| \le \operatorname{gap}(K, L).$$
The reason is that $(P_K - P_L) P_K = P_{L^\perp} P_K$. -/
theorem norm_orthogonal_mul_le_gap : ‖Lᗮ.starProjection * K.starProjection‖ ≤ K.gap L := by
  refine ContinuousLinearMap.opNorm_le_bound _ (K.gap_nonneg L) fun x => ?_
  have h : (Lᗮ.starProjection * K.starProjection) x =
      K.starProjection (K.starProjection x) - L.starProjection (K.starProjection x) := by
    rw [mul_apply_eq_comp, starProjection_orthogonal_val,
      starProjection_eq_self_iff.2 (K.starProjection_apply_mem x)]
  rw [h]
  exact (K.norm_starProjection_sub_le_gap_mul L _).trans
    (mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le x) (K.gap_nonneg L))

/-- **The gap is the larger of the two one-sided gaps.** Let $K$ and $L$ be subspaces of an inner
product space with orthogonal projections. Then
$$\operatorname{gap}(K, L) = \max\{\|P_{L^\perp} P_K\|, \|P_{K^\perp} P_L\|\}.$$
This is the equality that (3.8) of [saad2011numerical] states.

The bound $\ge$ is `Submodule.norm_orthogonal_mul_le_gap`, applied twice. For $\le$, the two
orthogonal pieces of $P_K x - P_L x = P_K (x - P_L x) - P_{K^\perp} (P_L x)$ are bounded by the
one-sided gaps times the two orthogonal pieces of $x$ along $L$. -/
theorem gap_eq_max_norm_orthogonal_mul :
    K.gap L =
      max ‖Lᗮ.starProjection * K.starProjection‖ ‖Kᗮ.starProjection * L.starProjection‖ := by
  refine le_antisymm ?_ (max_le (K.norm_orthogonal_mul_le_gap L)
    (by rw [gap_comm]; exact L.norm_orthogonal_mul_le_gap K))
  set a := ‖Lᗮ.starProjection * K.starProjection‖
  set b := ‖Kᗮ.starProjection * L.starProjection‖
  have ha : 0 ≤ a := norm_nonneg _
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

/-- Let $a \ge 0$. If $\|u - P_L u\| \le a \|u\|$ for every $u \in K$, then the one-sided gap
satisfies $\|P_{L^\perp} P_K\| \le a$. The reason is that
$P_{L^\perp} P_K x = P_K x - P_L (P_K x)$. -/
theorem norm_orthogonal_mul_le {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ u ∈ K, ‖u - L.starProjection u‖ ≤ a * ‖u‖) :
    ‖Lᗮ.starProjection * K.starProjection‖ ≤ a := by
  refine ContinuousLinearMap.opNorm_le_bound _ ha fun x => ?_
  rw [mul_apply_eq_comp, starProjection_orthogonal_val]
  exact (h _ (K.starProjection_apply_mem x)).trans
    (mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le x) ha)

/-- **The gap is bounded by the two one-sided distances.** Let $K$ and $L$ be subspaces of an inner
product space with orthogonal projections $P_K$ and $P_L$, and let $a, b \ge 0$. Assume that
$\|u - P_L u\| \le a \|u\|$ for every $u \in K$, and that $\|y - P_K y\| \le b \|y\|$ for every
$y \in L$. Then
$$\operatorname{gap}(K, L) \le \max\{a, b\}.$$

The gap is the larger one-sided gap (`Submodule.gap_eq_max_norm_orthogonal_mul`, (3.8) of
[saad2011numerical]), and each one-sided gap is bounded by its distance
(`Submodule.norm_orthogonal_mul_le`). -/
theorem gap_le_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hKL : ∀ u ∈ K, ‖u - L.starProjection u‖ ≤ a * ‖u‖)
    (hLK : ∀ y ∈ L, ‖y - K.starProjection y‖ ≤ b * ‖y‖) :
    K.gap L ≤ max a b := by
  rw [gap_eq_max_norm_orthogonal_mul]
  exact max_le_max (K.norm_orthogonal_mul_le L ha hKL) (L.norm_orthogonal_mul_le K hb hLK)

/-- **The gap is Lipschitz in a spanning family.** Let $K$ and $L$ be subspaces of an inner product
space $E$ over $\mathbb{K}$ with orthogonal projections. Let $(x_j)_{j \in \iota}$ and
$(w_j)_{j \in \iota}$ be families in $E$ indexed by a finite type, with
$K = \operatorname{span}\{x_j\}$ and $L = \operatorname{span}\{w_j\}$. Let $\kappa \ge 0$ and
$\delta \ge 0$ satisfy
$$\sum_j |c_j| \le \kappa \Big\| \sum_j c_j x_j \Big\| \quad \text{for every } c \colon \iota
  \to \mathbb{K},$$
$\|w_j - x_j\| \le \delta$ for every $j$, and $\kappa \delta \le 1/2$. Then
$$\operatorname{gap}(K, L) \le 2 \kappa \delta.$$

The constant $\kappa$ is the $\ell^1$ conditioning constant of the family $x$, which
`LinearIndependent.exists_forall_sum_norm_le` provides. The smallness hypothesis
$\kappa \delta \le 1/2$ cannot be dropped. Without it the perturbed family can be degenerate,
$L$ can have a smaller dimension than $K$, and then the gap is $1$, however small the
differences $\|w_j - x_j\|$ are relative to a badly conditioned $x$. The hypothesis is used only
for the direction from $L$ to $K$. The direction from $K$ to $L$ holds without it, because
$\sum_j c_j w_j$ is a competitor for the projection of $\sum_j c_j x_j$ for any $w$. The two
directions give the relative distances $\kappa \delta$ and $2 \kappa \delta$, and the gap is the
larger one (`Submodule.gap_le_max`).

This is the quantitative continuity of the map from a spanning family to the projection onto its
span. It turns the estimates for each vector in subspace iteration into the gap bound
`Krylov.gap_subspaceIterate_le`. -/
theorem gap_le_of_forall_norm_sub_le {ι : Type*} [Fintype ι] {x w : ι → E} {κ δ : ℝ}
    (hK : K = span 𝕜 (Set.range x)) (hL : L = span 𝕜 (Set.range w)) (hκ0 : 0 ≤ κ) (hδ0 : 0 ≤ δ)
    (hκ : ∀ c : ι → 𝕜, ∑ j, ‖c j‖ ≤ κ * ‖∑ j, c j • x j‖)
    (hδ : ∀ j, ‖w j - x j‖ ≤ δ) (hκδ : κ * δ ≤ 1 / 2) :
    K.gap L ≤ 2 * (κ * δ) := by
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
  have hκδ0 : 0 ≤ κ * δ := mul_nonneg hκ0 hδ0
  exact (gap_le_max K L hκδ0 (by positivity) ha hb).trans (max_le (by linarith) le_rfl)

/-- Let $K$ and $L$ be subspaces of an inner product space with orthogonal projections. If
$K \cap L^\perp \neq \{0\}$, then
$$\operatorname{gap}(K, L) = 1.$$
A unit vector of $K \cap L^\perp$ is moved by its full length. The result needs no hypothesis on
the dimensions. -/
theorem gap_eq_one_of_inf_orthogonal_ne_bot (h : K ⊓ Lᗮ ≠ ⊥) : K.gap L = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine le_antisymm (K.gap_le_one L) ?_
  have h1 := K.norm_starProjection_sub_le_gap_mul L x
  rw [starProjection_eq_self_iff.2 hx.1, (starProjection_apply_eq_zero_iff L).2 hx.2,
    sub_zero] at h1
  exact le_of_mul_le_mul_right (by simpa using h1) (norm_pos_iff.2 hx0)

end OneSided

/-! ### The restricted projection and the theory for equal dimensions -/

section Restrict

/-- Let $F$ and $G$ be subspaces of an inner product space $E$, where $F$ has an orthogonal
projection $P_F$. The **restricted projection** is the linear map
$$P_F|_G \colon G \to F, \qquad x \mapsto P_F x.$$
In orthonormal bases of $G$ and $F$ its matrix is $Q_F^H Q_G$. Its singular values are the
cosines of the principal angles between $F$ and $G$ (`Submodule.cosPrincipalAngle`), and its
adjoint is $P_G|_F$ (`Submodule.orthogonalProjectionRestrict_adjoint`). -/
noncomputable def orthogonalProjectionRestrict (F G : Submodule 𝕜 E) [F.HasOrthogonalProjection] :
    G →ₗ[𝕜] F :=
  (F.orthogonalProjectionOnto : E →ₗ[𝕜] F) ∘ₗ G.subtype

/-- The restricted projection acts as the projection: $P_F|_G \, x = P_F x$ in $E$ for every
$x \in G$. -/
@[simp]
theorem coe_orthogonalProjectionRestrict_apply (F G : Submodule 𝕜 E) [F.HasOrthogonalProjection]
    (x : G) : (F.orthogonalProjectionRestrict G x : E) = F.starProjection x :=
  rfl

/-- Let $F$ and $G$ be finite-dimensional subspaces of an inner product space. Then the adjoint of
the restricted projection $P_F|_G$ is $P_G|_F$:
$$(P_F|_G)^* = P_G|_F.$$
The reason is that $\langle P_G f, g \rangle = \langle f, g \rangle = \langle f, P_F g \rangle$
for $f \in F$ and $g \in G$. -/
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

/-- **The one-sided gap through the restricted projection.** Let $K$ and $L$ be finite-dimensional
subspaces of an inner product space, with $k = \dim K \ge 1$. Then
$$\|P_{L^\perp} P_K\|^2 = 1 - \sigma_{k-1}(P_L|_K)^2,$$
where $\sigma_0 \ge \sigma_1 \ge \dots$ are the singular values of $P_L|_K$, so that
$\sigma_{k-1}$ is the least one.

For $x \in K$, $\|P_L x\|^2 + \|P_{L^\perp} x\|^2 = \|x\|^2$, so this is the identity for
stacked isometries `LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues`. If
$\dim K > \dim L$, both sides are $1$. The singular values are Mathlib's
`LinearMap.singularValues`, indexed from $0$. -/
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

/-- A finite-dimensional subspace of dimension $0$ has the projection $0$. -/
private theorem starProjection_eq_zero_of_finrank_eq_zero (h : Module.finrank 𝕜 K = 0) :
    K.starProjection = 0 := by
  ext x
  exact (Submodule.eq_bot_iff K).1 (Submodule.finrank_eq_zero.1 h) _ (K.starProjection_apply_mem x)

/-- **For subspaces of equal dimension, the gap is the one-sided gap.** Let $K$ and $L$ be
finite-dimensional subspaces of an inner product space with $\dim K = \dim L$. Then
$$\operatorname{gap}(K, L) = \|P_{L^\perp} P_K\|,$$
and by `Submodule.gap_comm` it is also $\|P_{K^\perp} P_L\|$.

The two one-sided gaps are $\sqrt{1 - \sigma_{\min}(P_L|_K)^2}$ and
$\sqrt{1 - \sigma_{\min}(P_K|_L)^2}$, and $P_K|_L$ is the adjoint of $P_L|_K$, with the same
singular values. The ambient space need not be finite-dimensional. -/
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

/-- **Subspaces of equal dimension are at gap $1$ exactly when one meets the orthogonal complement
of the other.** Let $K$ and $L$ be finite-dimensional subspaces of an inner product space with
$\dim K = \dim L$. Then
$$\operatorname{gap}(K, L) = 1 \iff K \cap L^\perp \neq \{0\}.$$
This is stated in §2.5.3 of [golub2013matrix].

Gap $1$ forces $\sigma_{\min}(P_L|_K) = 0$, so $P_L|_K$ has a nonzero kernel. Without equal
dimensions the implication from left to right fails, for example for a line inside a plane. -/
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

/-- **The gap between two lines is the sine of their angle.** Let $q$ and $u$ be unit vectors of an
inner product space $E$ over $\mathbb{K}$. Then
$$\operatorname{gap}(\mathbb{K} q, \mathbb{K} u) = \sin \theta(q, \mathbb{K} u),$$
which is $\|q - \langle u, q \rangle u\|$.

The two lines have the same dimension, so the gap is the one-sided gap $\|P_{u^\perp} P_q\|$
(`Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`), and $P_{u^\perp} P_q w = \langle q, w
\rangle P_{u^\perp} q$. -/
theorem gap_span_singleton_eq_sinAngle {q u : E} (hq : ‖q‖ = 1) (hu : ‖u‖ = 1) :
    (𝕜 ∙ q).gap (𝕜 ∙ u) = (𝕜 ∙ u).sinAngle q := by
  have hq0 : q ≠ 0 := norm_ne_zero_iff.1 (by rw [hq]; exact one_ne_zero)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  rw [gap_eq_norm_orthogonal_mul_of_finrank_eq _ _
    ((finrank_span_singleton hq0).trans (finrank_span_singleton hu0).symm), sinAngle, hq, div_one]
  have hT : ∀ w, ((𝕜 ∙ u)ᗮ.starProjection * (𝕜 ∙ q).starProjection) w =
      (inner 𝕜 q w : 𝕜) • (q - (𝕜 ∙ u).starProjection q) := by
    intro w
    change (𝕜 ∙ u)ᗮ.starProjection ((𝕜 ∙ q).starProjection w) = _
    rw [starProjection_singleton, hq, one_pow, RCLike.ofReal_one, div_one, map_smul,
      starProjection_orthogonal_val]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_) ?_
  · rw [hT, norm_smul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa [hq] using norm_inner_le_norm (𝕜 := 𝕜) q w
  · have h := ((𝕜 ∙ u)ᗮ.starProjection * (𝕜 ∙ q).starProjection).le_opNorm q
    rwa [hT, inner_self_eq_norm_sq_to_K, hq, RCLike.ofReal_one, one_pow, one_smul,
      mul_one] at h

end Restrict

/-! ### The graph of a map over a subspace -/

section Graph

variable (K : Submodule 𝕜 E)

/-- Let $K$ be a subspace of an inner product space $E$, and let $X \colon K \to K^\perp$ be a
continuous linear map. The **graph** of $X$ over $K$ is the subspace
$$\operatorname{graph} X = \{x + Xx : x \in K\}$$
of $E$. In coordinates adapted to the splitting $E = K \oplus K^\perp$, it is the range of
$\begin{bmatrix} I \\ X \end{bmatrix}$. These are the subspaces $\operatorname{ran}
\begin{bmatrix} I \\ X \end{bmatrix}$ of the theorems on invariant subspaces and subspace
iteration in §7.2.4, §7.3.1 and §8.2.2 of [golub2013matrix].

Mathlib's `LinearMap.graph` is a subspace of a product $E \times F$ and is a different object. -/
def graph (X : K →L[𝕜] Kᗮ) : Submodule 𝕜 E :=
  LinearMap.range (K.subtype + Kᗮ.subtype ∘ₗ (X : K →ₗ[𝕜] Kᗮ))

variable {K} in
/-- A vector $y$ lies in the graph of $X$ over $K$ if and only if $y = x + Xx$ for some $x \in K$.
-/
theorem mem_graph_iff {X : K →L[𝕜] Kᗮ} {y : E} : y ∈ K.graph X ↔ ∃ x : K, (x : E) + X x = y :=
  Iff.rfl

instance [FiniteDimensional 𝕜 K] (X : K →L[𝕜] Kᗮ) : FiniteDimensional 𝕜 (K.graph X) :=
  LinearMap.finiteDimensional_range _

/-- Let $K$ be a subspace of an inner product space, and let $X \colon K \to K^\perp$ be a
continuous linear map. Then the graph of $X$ has the dimension of $K$:
$$\dim(\operatorname{graph} X) = \dim K.$$
The map $x \mapsto x + Xx$ is injective, because $K$ meets $K^\perp$ only in $0$.

The dimension is `Module.finrank`, which is $0$ for an infinite-dimensional space; the equality
holds in that case too. -/
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

/-- **The gap between a subspace and a graph over it.** Let $K$ be a finite-dimensional subspace of
an inner product space, and let $X \colon K \to K^\perp$ be a continuous linear map. Then
$$\operatorname{gap}(K, \operatorname{graph} X) = \frac{\|X\|}{\sqrt{1 + \|X\|^2}}.$$
This is Theorem I.5.5 of Stewart and Sun, and it is the computation behind Theorems 7.3.1 and
8.2.2 of [golub2013matrix].

The two subspaces have the same dimension, so the gap is the one-sided gap $\|P_{K^\perp} P_G\|$
with $G = \operatorname{graph} X$. For $g = x + Xx \in G$, $P_{K^\perp} g = Xx$ and
$\|g\|^2 = \|x\|^2 + \|Xx\|^2$, and the function $t \mapsto t / \sqrt{1 + t^2}$ is increasing. -/
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
