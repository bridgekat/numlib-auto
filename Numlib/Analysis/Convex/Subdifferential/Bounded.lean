/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# Local boundedness of the subdifferential

Let $E$ be a finite-dimensional real normed space, and let $f : E \to [-\infty, +\infty]$ be proper
and convex. Then $f$ is Lipschitz on every compact subset $S$ of
$\operatorname{int}(\operatorname{dom} f)$, and one constant bounds its subgradients and its
directional derivatives on $S$: there is $K \ge 0$ such that $f$ is Lipschitz on $S$ with constant
$K$,
$$\langle z, y \rangle \le K \|z\| \quad \text{and} \quad f'(x; z) \le K \|z\|$$
for every $x \in S$, every $y \in \partial f(x)$ and every $z \in E$. When $E$ is an inner product
space paired with itself and $f$ is also closed, the image $\partial f(S) = \bigcup_{x \in S}
\partial f(x)$ is compact, and it is nonempty when $S$ is nonempty. The presentation follows
[rockafellar1970convex], §24.

## Main results

* `ConvexAnalysis.exists_lipschitz_forall_pairing_le_of_isCompact`: the three bounds with one
  constant, for any pairing. This is Theorem 24.7 of [rockafellar1970convex].
* `ConvexAnalysis.exists_forall_norm_le_of_isCompact`: in an inner product space, $\|y\| \le K$ for
  all subgradients $y$ at points of $S$.
* `ConvexAnalysis.isCompact_subdifferential`, `ConvexAnalysis.isCompact_image_subgradientRel`:
  $\partial f(x)$ is compact for $x \in \operatorname{int}(\operatorname{dom} f)$, and
  $\partial f(S)$ is compact for closed $f$.

## Implementation notes

* The bound on subgradients is stated as $\langle z, y \rangle \le K \|z\|$ for all $z$, which needs
  no norm on the dual space $F$. When $F = E$ is an inner product space, the bound at $z = y$ gives
  $\|y\| \le K$.
* The compactness statements are for a real inner product space paired with itself by `innerₗ E`.
  Closedness of $f$ is used only for the compactness of $\partial f(S)$.
* The function $f$ is Lipschitz in the sense of its real values `(f x).toReal`, which agree with $f$
  on $\operatorname{int}(\operatorname{dom} f)$.
-/

open Set Filter Topology
open scoped NNReal RealInnerProductSpace

namespace ConvexAnalysis

/-! ### Bounds with one constant -/

section Bound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Let $S \subseteq E$, $x \in S$, $\delta > 0$ and $z \ne 0$. Then $x + (\delta / \|z\|) z$ lies
in the closed $\delta$-neighbourhood `Metric.cthickening δ S` of $S$. -/
theorem mem_cthickening_add_smul {S : Set E} {x : E} (hx : x ∈ S) {δ : ℝ} (hδ : 0 < δ) {z : E}
    (hz : z ≠ 0) : x + (δ / ‖z‖) • z ∈ Metric.cthickening δ S := by
  have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine Metric.mem_cthickening_of_dist_le _ _ _ _ hx (le_of_eq ?_)
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hδ hznorm)]
  field_simp

/-- **Local boundedness with one constant.** Let $E$ be a finite-dimensional real normed space
paired with a real vector space $F$, let $f : E \to [-\infty, +\infty]$ be proper and convex,
and let $S \subseteq \operatorname{int}(\operatorname{dom} f)$ be compact. Then there is a
constant $K \ge 0$ such that

* $f$ is Lipschitz on $S$ with constant $K$;
* $\langle z, y \rangle \le K \|z\|$ for every $x \in S$, every $y \in \partial f(x)$ and every
  $z \in E$;
* $f'(x; z) \le K \|z\|$ for every $x \in S$ and every $z \in E$.

This is Theorem 24.7 of [rockafellar1970convex]. No continuity of the pairing is assumed. The
Lipschitz condition is for the real values `(f x).toReal`. The constant $K$ is a Lipschitz
constant on a compact neighbourhood `Metric.cthickening δ S` of $S$ in
$\operatorname{int}(\operatorname{dom} f)$, and the other two bounds follow from the values of
$f$ at $x + (\delta / \|z\|) z$, which lies in that neighbourhood. -/
theorem exists_lipschitz_forall_pairing_le_of_isCompact (hf : ConvexFn f) (hp : ProperConvex f)
    {S : Set E} (hS : IsCompact S) (hSD : S ⊆ interior (convexDom f)) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ y ∈ subdifferential B f x, ∀ z : E, B z y ≤ (K : ℝ) * ‖z‖) ∧
      ∀ x ∈ S, ∀ z : E, dirDeriv f x z ≤ (((K : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨δ, hδ, hδsub⟩ := hS.exists_cthickening_subset_open isOpen_interior hSD
  have hTc : IsCompact (Metric.cthickening δ S) := hS.cthickening
  have hTdom : Metric.cthickening δ S ⊆ convexDom f := hδsub.trans interior_subset
  have hTri : Metric.cthickening δ S ⊆ ri (convexDom f) := fun w hw =>
    Convex.interior_subset_relint (hδsub hw)
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_isCompact hp hTc hTri
  -- The single estimate both halves consume.
  have hkey : ∀ x ∈ S, ∀ z : E, z ≠ 0 → ∀ a b : ℝ, f x = (a : EReal) →
      f (x + (δ / ‖z‖) • z) = (b : EReal) → b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := by
    intro x hx z hz a b ha hb
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    have hwT := mem_cthickening_add_smul hx hδ hz
    have hnorm : dist (x + (δ / ‖z‖) • z) x = (δ / ‖z‖) * ‖z‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hδ hznorm)]
    have hlip := hK.dist_le_mul _ hwT _ hxT
    simp only [ha, hb, EReal.toReal_coe, Real.dist_eq, hnorm] at hlip
    exact (le_abs_self _).trans hlip
  refine ⟨K, hK.mono (Metric.self_subset_cthickening S), ?_, ?_⟩
  · intro x hx y hy z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x)
      (hTdom (Metric.self_subset_cthickening S hx))
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    have hsg := hy (x + (δ / ‖z‖) • z)
    rw [add_sub_cancel_left, map_smul, LinearMap.smul_apply, smul_eq_mul, ha, hb,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hsg
    refine le_of_mul_le_mul_left ?_ ht
    calc (δ / ‖z‖) * B z y
        ≤ b - a := by linarith
      _ ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (δ / ‖z‖) * ((K : ℝ) * ‖z‖) := by ring
  · intro x hx z
    have hxT : x ∈ Metric.cthickening δ S := Metric.self_subset_cthickening S hx
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (hTdom hxT)
    rcases eq_or_ne z 0 with rfl | hz
    · rw [dirDeriv_zero (by rw [ha]; exact EReal.coe_ne_top a) (hp.ne_bot x)]
      simp
    have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz
    have ht : (0 : ℝ) < δ / ‖z‖ := div_pos hδ hznorm
    obtain ⟨b, hb⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot _)
      (hTdom (mem_cthickening_add_smul hx hδ hz))
    refine le_trans (dirDeriv_le f x z ht) ?_
    rw [ha, hb, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff,
      div_le_iff₀ ht]
    calc b - a ≤ (K : ℝ) * ((δ / ‖z‖) * ‖z‖) := hkey x hx z hz a b ha hb
      _ = (K : ℝ) * ‖z‖ * (δ / ‖z‖) := by ring

end Bound

/-! ### Compactness of the subdifferential -/

section Image

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex, and let $S \subseteq \operatorname{int}(\operatorname{dom} f)$ be compact.
Then there is $K \ge 0$ with
$$\|y\| \le K \quad \text{for every } x \in S \text{ and every } y \in \partial f(x).$$

The subdifferential is taken for the inner product `innerₗ E`. -/
theorem exists_forall_norm_le_of_isCompact (hf : ConvexFn f) (hp : ProperConvex f) {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ interior (convexDom f)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ S, ∀ y ∈ subdifferential (innerₗ E) f x, ‖y‖ ≤ K := by
  obtain ⟨K, -, hpair, -⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := innerₗ E) hf hp hS hSD
  refine ⟨K, K.coe_nonneg, fun x hx y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have h := hpair x hx y hy y
  rw [innerₗ_apply_apply, real_inner_self_eq_norm_mul_norm] at h
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hy0)

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
proper and convex, and let $x \in \operatorname{int}(\operatorname{dom} f)$. Then
$\partial f(x)$ is compact.

It is closed because it is an intersection of closed half-spaces, and bounded by
`ConvexAnalysis.exists_forall_norm_le_of_isCompact` for $S = \{x\}$. -/
theorem isCompact_subdifferential (hf : ConvexFn f) (hp : ProperConvex f) {x : E}
    (hx : x ∈ interior (convexDom f)) : IsCompact (subdifferential (innerₗ E) f x) := by
  have : IsContinuousPairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  obtain ⟨K, -, hK⟩ := exists_forall_norm_le_of_isCompact hf hp isCompact_singleton
    (by simpa using hx)
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) K)
    (isClosed_subdifferential _ _) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hK x rfl y hy

/-- Let $f$ be proper and convex, and let $S \subseteq \operatorname{int}(\operatorname{dom} f)$ be
nonempty. Then $\partial f(S) = \bigcup_{x \in S} \partial f(x)$ is nonempty. -/
theorem image_subgradientRel_nonempty (hf : ConvexFn f) (hp : ProperConvex f) {S : Set E}
    (hne : S.Nonempty) (hSD : S ⊆ interior (convexDom f)) :
    ((subgradientRel (innerₗ E) f).image S).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := innerₗ E) hf hp
    (Convex.interior_subset_relint (hSD hx))
  exact ⟨y, x, hx, hy⟩

/-- Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
closed, proper and convex, and let $S \subseteq \operatorname{int}(\operatorname{dom} f)$ be
compact. Then
$$\partial f(S) = \bigcup_{x \in S} \partial f(x)$$
is compact.

The set $\partial f(S)$ is the image of $S$ under the relation `ConvexAnalysis.subgradientRel`.
The graph of $\partial f$ is closed, so its intersection with the compact set
$S \times \{y \mid \|y\| \le K\}$ is compact, and $\partial f(S)$ is the projection of that
intersection. -/
theorem isCompact_image_subgradientRel (hf : ClosedProperConvexFn f) {S : Set E}
    (hS : IsCompact S) (hSD : S ⊆ interior (convexDom f)) :
    IsCompact ((subgradientRel (innerₗ E) f).image S) := by
  obtain ⟨K, -, hnorm⟩ := exists_forall_norm_le_of_isCompact hf.convex hf.proper hS hSD
  have hbox : IsCompact (S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    IsCompact.prod hS (isCompact_closedBall 0 (K : ℝ))
  have hclosed : IsClosed (subgradientRel (innerₗ E) f) := by
    refine isClosed_subgradientRel ?_ hf.proper hf.lowerSemicontinuous
    exact continuous_inner
  have hcap : IsCompact (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) :=
    hbox.inter_left hclosed
  have himg : (subgradientRel (innerₗ E) f).image S
      = Prod.snd '' (subgradientRel (innerₗ E) f ∩ S ×ˢ Metric.closedBall (0 : E) (K : ℝ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, by simpa using hnorm x hx y hxy⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hpS, -⟩, rfl⟩
      exact ⟨p.1, hpS, hp⟩
  rw [himg]
  exact hcap.image continuous_snd

end Image

end ConvexAnalysis
