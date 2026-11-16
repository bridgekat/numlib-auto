/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection.Minimal`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Numlib.Analysis.Normed.Module.BestApprox

/-!
# The projection onto a closed convex set of a Hilbert space

Let $K$ be a nonempty closed convex subset of a real Hilbert space $V$. Every $u \in V$ has a unique
best approximation $P_K u \in K$, that is, $\|u - P_K u\| \le \|u - v\|$ for all $v \in K$. This
module proves this projection theorem, the variational characterization of $P_K u$ as the point
$w \in K$ with
$$\langle u - w, v - w \rangle \le 0 \quad \text{for all } v \in K,$$
the monotonicity and nonexpansiveness of $P_K$, the explicit projection onto a closed ball, and the
agreement of $P_K$ with the orthogonal projection when $K$ is a closed subspace. This is §5.1 of
[brezis2011functional] (Theorem 5.2, Proposition 5.3, Corollary 5.4) and §3.4 of
[han2009theoretical] (Theorem 3.4.3, Proposition 3.4.4, Theorem 3.4.6).

## Main results

* `exists_isBestApprox_of_isClosed` and `existsUnique_isBestApprox`: the **projection theorem**,
  existence and uniqueness of the best approximation from $K$ (Theorem 5.2 of
  [brezis2011functional]).
* `isBestApprox_bestApprox_of_isClosed` and `bestApprox_mem`: the map `bestApprox K` gives the best
  approximation, which lies in $K$.
* `inner_sub_bestApprox_le_zero` and `bestApprox_eq_iff`: the variational inequality
  $\langle u - P_K u, v - P_K u \rangle \le 0$ for $v \in K$, which determines $P_K u$.
* `inner_bestApprox_sub_nonneg`, `norm_bestApprox_sub_bestApprox_le` and `lipschitzWith_bestApprox`:
  $P_K$ is monotone and does not increase distances (Proposition 5.3 of [brezis2011functional]).
* `bestApprox_closedBall_eq_radial`: the projection onto a closed ball is the identity inside the
  ball and the radial projection outside it.
* `bestApprox_eq_starProjection`: on a closed subspace the metric projection is the orthogonal
  projection (Corollary 5.4 of [brezis2011functional]), over $\mathbb{R}$ or $\mathbb{C}$.

## Implementation notes

* Mathlib proves the projection theorem as an existence statement
  (`exists_norm_eq_iInf_of_complete_convex`) and characterizes the minimizer
  (`norm_eq_iInf_iff_real_inner_le_zero`), but it has the projection as a map only for subspaces
  (`Submodule.starProjection`). The map onto a convex set is `bestApprox K` of
  `Numlib.Analysis.Normed.Module.BestApprox`. It is defined by choice in any seminormed space, and
  the hypotheses of the projection theorem are on the theorems.
* The scalars are real for the theory of convex sets, as in Mathlib's
  `norm_eq_iInf_iff_real_inner_le_zero`. Over an `RCLike` field the map is still the metric
  projection, since it is defined from the norm alone, and the result on subspaces is stated there.
-/

open scoped InnerProductSpace

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The **projection theorem**, existence. Let $V$ be a real Hilbert space and let $K \subseteq V$
be nonempty, closed and convex. Then every $u \in V$ has a best approximation from $K$: there is
$v \in K$ with $\|u - v\| \le \|u - w\|$ for all $w \in K$. This is part of Theorem 5.2 of
[brezis2011functional].

This is Mathlib's `exists_norm_eq_iInf_of_complete_convex`, read through the metric description
of `IsBestApprox`. The theorem `exists_isBestApprox_of_convex` of
`Numlib.Variational.WeakMinimization` is the same statement, proved by the direct method of the
calculus of variations. -/
theorem exists_isBestApprox_of_isClosed {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : V) : ∃ v, IsBestApprox K u v := by
  obtain ⟨v, hv, hnorm⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hK u
  refine ⟨v, (isBestApprox_iff_norm_sub_eq_infDist hv).2 ?_⟩
  rw [hnorm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]

/-- The **projection theorem**. Let $V$ be a real Hilbert space and let $K \subseteq V$ be nonempty,
closed and convex. Then every $u \in V$ has exactly one best approximation from $K$. This is
Theorem 5.2 of [brezis2011functional].

Existence is `exists_isBestApprox_of_isClosed`; uniqueness follows from strict convexity of the
norm (`IsBestApprox.unique`). -/
theorem existsUnique_isBestApprox {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (u : V) : ∃! v, IsBestApprox K u v := by
  obtain ⟨v, hv⟩ := exists_isBestApprox_of_isClosed hne hcl hK u
  exact ⟨v, hv, fun w hw => hw.unique hK hv⟩

variable {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K)
include hne hcl hK

/-- Let $V$ be a real Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Then for
every $u \in V$, `bestApprox K u` is a best approximation of $u$ from $K$. So `bestApprox K u`
is the projection $P_K u$ of §5.1 of [brezis2011functional], with no further condition. -/
theorem isBestApprox_bestApprox_of_isClosed (u : V) : IsBestApprox K u (bestApprox K u) :=
  isBestApprox_bestApprox (exists_isBestApprox_of_isClosed hne hcl hK u)

/-- Let $V$ be a real Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Then
$P_K u \in K$ for every $u \in V$. -/
theorem bestApprox_mem (u : V) : bestApprox K u ∈ K :=
  (isBestApprox_bestApprox_of_isClosed hne hcl hK u).1

/-- The **variational inequality of the projection**. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Then for every $u \in V$
$$\langle u - P_K u, v - P_K u \rangle \le 0 \quad \text{for all } v \in K.$$
This is formula (3) of Theorem 5.2 of [brezis2011functional]. -/
theorem inner_sub_bestApprox_le_zero (u : V) :
    ∀ v ∈ K, ⟪u - bestApprox K u, v - bestApprox K u⟫_ℝ ≤ 0 :=
  (isBestApprox_iff_inner_le_zero hK (bestApprox_mem hne hcl hK u)).1
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u)

/-- The **variational characterization of the projection**. Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Then for $u, w \in V$, $P_K u = w$ if and only
if $w \in K$ and
$$\langle u - w, v - w \rangle \le 0 \quad \text{for all } v \in K.$$
This is part of Theorem 5.2 of [brezis2011functional]. -/
theorem bestApprox_eq_iff {u w : V} :
    bestApprox K u = w ↔ w ∈ K ∧ ∀ v ∈ K, ⟪u - w, v - w⟫_ℝ ≤ 0 := by
  constructor
  · rintro rfl
    exact ⟨bestApprox_mem hne hcl hK u, inner_sub_bestApprox_le_zero hne hcl hK u⟩
  · rintro ⟨hw, h⟩
    exact IsBestApprox.bestApprox_eq hK ((isBestApprox_iff_inner_le_zero hK hw).2 h)

/-- **The projection is monotone.** Let $V$ be a real Hilbert space and let $K \subseteq V$ be
nonempty, closed and convex. Then for all $u_1, u_2 \in V$
$$0 \le \langle P_K u_1 - P_K u_2, u_1 - u_2 \rangle.$$
This is part of Proposition 3.4.4 of [han2009theoretical].

This is the first part of `IsBestApprox.dist_le_dist`. -/
theorem inner_bestApprox_sub_nonneg (u₁ u₂ : V) :
    0 ≤ ⟪bestApprox K u₁ - bestApprox K u₂, u₁ - u₂⟫_ℝ :=
  ((isBestApprox_bestApprox_of_isClosed hne hcl hK u₁).dist_le_dist hK
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u₂)).1

/-- **The projection does not increase distances.** Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Then for all $u_1, u_2 \in V$
$$\|P_K u_1 - P_K u_2\| \le \|u_1 - u_2\|.$$
This is Proposition 5.3 of [brezis2011functional]. -/
theorem norm_bestApprox_sub_bestApprox_le (u₁ u₂ : V) :
    ‖bestApprox K u₁ - bestApprox K u₂‖ ≤ ‖u₁ - u₂‖ :=
  ((isBestApprox_bestApprox_of_isClosed hne hcl hK u₁).dist_le_dist hK
    (isBestApprox_bestApprox_of_isClosed hne hcl hK u₂)).2

/-- Let $V$ be a real Hilbert space and let $K \subseteq V$ be nonempty, closed and convex. Then
$P_K$ is Lipschitz with constant $1$. This is Proposition 5.3 of [brezis2011functional]. -/
theorem lipschitzWith_bestApprox : LipschitzWith 1 (bestApprox K) :=
  LipschitzWith.of_dist_le_mul fun u₁ u₂ => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_bestApprox_sub_bestApprox_le hne hcl hK u₁ u₂

end Hilbert

section ClosedBall

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℝ}

/-- Let $V$ be a real inner product space, let $x, y \in V$, and let $r \ge 0$. The projection of
$y$ onto the closed ball $\bar B(x, r)$ is
$$P_{\bar B(x, r)} y = \begin{cases} y & \text{if } \|y - x\| \le r, \\ x + \dfrac{r}{\|y - x\|}
  (y - x) & \text{otherwise.} \end{cases}$$
So it is the identity inside the ball and the radial projection outside it. Completeness of $V$
is not needed. -/
theorem bestApprox_closedBall_eq_radial (x y : V) (hr : 0 ≤ r) :
    bestApprox (Metric.closedBall x r) y =
      if ‖y - x‖ ≤ r then y else x + (r / ‖y - x‖) • (y - x) := by
  let C := Metric.closedBall x r
  have hconv : Convex ℝ C := convex_closedBall x r
  by_cases hy : ‖y - x‖ ≤ r
  · rw [ite_eq_left hy]
    apply IsBestApprox.bestApprox_eq hconv
    refine ⟨Metric.mem_closedBall.mpr (by rwa [dist_eq_norm]), ?_⟩
    intro w _
    simp
  rw [ite_eq_right hy]
  let a := ‖y - x‖
  have ha : 0 < a := hr.trans_lt (lt_of_not_ge hy)
  have hs : 0 ≤ r / a := div_nonneg hr ha.le
  have hs' : r / a ≤ 1 := (div_le_one ha).2 (le_of_not_ge hy)
  let z := x + (r / a) • (y - x)
  have hz : z ∈ C := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm, show z - x = (r / a) • (y - x) by simp [z], norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs]
    exact (div_mul_cancel₀ r ha.ne').le
  have hd : ‖y - z‖ = a - r := by
    rw [show y - z = (1 - r / a) • (y - x) by
      rw [sub_smul, one_smul]
      simp only [z]
      abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs')]
    change (1 - r / a) * a = a - r
    rw [sub_mul, one_mul, div_mul_cancel₀ r ha.ne']
  apply IsBestApprox.bestApprox_eq hconv
  refine ⟨hz, fun w hw ↦ ?_⟩
  have hw' : ‖w - x‖ ≤ r := by simpa [C, Metric.mem_closedBall, dist_eq_norm] using hw
  have htri : a ≤ ‖y - w‖ + ‖w - x‖ := by
    rw [show a = ‖(y - w) + (w - x)‖ by rw [sub_add_sub_cancel]]
    exact norm_add_le _ _
  rw [hd]
  exact sub_le_iff_le_add.mpr (htri.trans (add_le_add_right hw' _))

end ClosedBall

section Subspace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **On a subspace the metric projection is the orthogonal projection.** Let $V$ be an inner
product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $K$ be a subspace of $V$
that has an orthogonal projection. Then `bestApprox K u` is the orthogonal projection of $u$
onto $K$ for every $u \in V$. This is Corollary 5.4 of [brezis2011functional].

Since `Submodule.starProjection` is a bounded linear map, this gives the statement of the
corollary that $P_M$ is a linear operator. Its characterization "$u \in M$ and
$\langle f - u, v \rangle = 0$ for all $v \in M$" is `isBestApprox_iff_mem_orthogonal`. -/
theorem bestApprox_eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    bestApprox (K : Set V) u = K.starProjection u :=
  (isBestApprox_bestApprox ⟨_, isBestApprox_starProjection K u⟩).eq_starProjection K

end Subspace
