import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Compact and completely continuous nonlinear operators

A map `T` defined on a subset `K` of a normed space is a **compact map** when it carries every
bounded subset of `K` to a relatively compact set, and **completely continuous** when it is in
addition continuous. For a *linear* map on the whole space compactness already forces continuity
and the notion is Mathlib's `IsCompactOperator`; for a nonlinear map continuity is an independent
hypothesis, which is why the two words are needed.

* `IsCompactMap T K` is the predicate, and `isCompactMap_univ_iff_isCompactOperator` identifies
  it with `IsCompactOperator` for a linear map on the whole space.
* `IsCompactMap.isCompactOperator_hasFDerivAt`: the Fréchet derivative of a compact map at an
  interior point is a **compact linear operator**. This is what licenses the Fredholm alternative
  for `1 - T'(v₀)`, and so it is the bridge from a nonlinear fixed point problem `u = T u` to the
  linear theory of second-kind equations.

The proof of the derivative theorem is the classical one: for a scalar `a` of small norm the
difference quotients `v ↦ a⁻¹ • (T (v₀ + a • v) - T v₀)` run over a totally bounded set as `v` runs
over the closed unit ball, and they approximate `A` uniformly there, so `A` maps the unit ball into
a totally bounded set. Continuity of `T` is not used: differentiability at the one point `v₀`
together with compactness on bounded sets is enough, so the hypothesis is weaker than the
"completely continuous" of the source.

These are Atkinson–Han[^atkinson-han] Definition 5.5.3 and Proposition 5.5.5. Brouwer's and
Schauder's fixed point theorems, and the rotation of a completely continuous vector field, are not
here: Mathlib has neither a Brouwer theorem nor degree theory.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Metric Set Bornology

/-- A map `T` is a **compact map on `K`** when the image of every bounded subset of `K` is
relatively compact: `closure (T '' B)` is compact for every bounded `B ⊆ K`.

A *completely continuous* map is a continuous compact map; continuity is a separate hypothesis
because, unlike for linear maps, it does not follow. -/
def IsCompactMap {V W : Type*} [SeminormedAddCommGroup V] [TopologicalSpace W]
    (T : V → W) (K : Set V) : Prop :=
  ∀ B ⊆ K, IsBounded B → IsCompact (closure (T '' B))

namespace IsCompactMap

variable {V W : Type*} [SeminormedAddCommGroup V] [TopologicalSpace W] {T : V → W} {K L : Set V}

/-- A compact map on `K` is a compact map on every subset of `K`. -/
theorem mono (hT : IsCompactMap T K) (h : L ⊆ K) : IsCompactMap T L :=
  fun _ hB hb => hT _ (hB.trans h) hb

end IsCompactMap

section Linear

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- For a linear map on the whole space, being a compact map is Mathlib's `IsCompactOperator`. -/
theorem isCompactMap_univ_iff_isCompactOperator {f : V →ₗ[𝕜] W} :
    IsCompactMap f univ ↔ IsCompactOperator f := by
  constructor
  · intro h
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall f one_pos]
    exact h _ (subset_univ _) isBounded_closedBall
  · intro h B _ hB
    exact h.isCompact_closure_image_of_isVonNBounded ((NormedSpace.isVonNBounded_iff 𝕜).2 hB)

end Linear

section FDeriv

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [CompleteSpace W]

/-- **The Fréchet derivative of a compact map is a compact operator** (Atkinson–Han, *Theoretical
Numerical Analysis*, Proposition 5.5.5). If `T` is a compact map on a neighbourhood `K` of `v₀` and
is Fréchet differentiable at `v₀` with derivative `A`, then `A` is a compact operator.

Note that `T` is not assumed continuous: differentiability at `v₀` is all the smoothness the proof
uses, so the statement applies to a completely continuous operator in particular. -/
theorem IsCompactMap.isCompactOperator_hasFDerivAt {T : V → W} {K : Set V} {v₀ : V} {A : V →L[𝕜] W}
    (hT : IsCompactMap T K) (hK : K ∈ nhds v₀) (hA : HasFDerivAt T A v₀) :
    IsCompactOperator A := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (A : V →ₗ[𝕜] W) one_pos).2 ?_
  refine TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure ?_) isClosed_closure
  rw [Metric.totallyBounded_iff]
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.1 hK
  intro ε hε
  -- A scalar `a` small enough that the whole shifted ball `v₀ + a • closedBall 0 1` sits in `K`
  -- and that the difference quotient at `a` is within `ε / 2` of `A` on the unit ball.
  obtain ⟨δ, hδ, hdiff⟩ : ∃ δ > 0, ∀ h : V, ‖h‖ ≤ δ → ‖T (v₀ + h) - T v₀ - A h‖ ≤ ε / 2 * ‖h‖ := by
    have hlo := hA.isLittleO.def (c := ε / 2) (by positivity)
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨δ, hδ, hd⟩ := hlo
    refine ⟨δ / 2, by positivity, fun h hh => ?_⟩
    have hdist : dist (v₀ + h) v₀ < δ := by
      rw [dist_eq_norm]; simpa using lt_of_le_of_lt hh (by linarith)
    simpa using hd hdist
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt 𝕜 (lt_min hδ hr)
  have haδ : ‖a‖ ≤ δ := (ha.trans_le (min_le_left _ _)).le
  have har : ‖a‖ < r := ha.trans_le (min_le_right _ _)
  have hane : a ≠ 0 := by simpa using ha0.ne'
  -- The difference quotients over the unit ball form a totally bounded set.
  set B : Set V := (fun v => v₀ + a • v) '' closedBall 0 1 with hB
  have hBK : B ⊆ K := by
    rintro _ ⟨v, hv, rfl⟩
    refine hrK ?_
    rw [mem_ball, dist_eq_norm]
    simpa [norm_smul] using
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) (mem_closedBall_zero_iff.1 hv)) har
  have hBb : IsBounded B := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖v₀‖ + ‖a‖, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    refine (norm_add_le _ _).trans ?_
    gcongr
    simpa [norm_smul] using
      mul_le_of_le_one_right (norm_nonneg a) (mem_closedBall_zero_iff.1 hv)
  have htb : TotallyBounded ((fun w => a⁻¹ • (w - T v₀)) '' (T '' B)) := by
    refine TotallyBounded.image ?_ ?_
    · exact (hT B hBK hBb).totallyBounded.subset subset_closure
    · exact ((uniformContinuous_id.sub uniformContinuous_const).const_smul a⁻¹)
  obtain ⟨t, htf, hts⟩ := Metric.totallyBounded_iff.1 htb (ε / 2) (by positivity)
  refine ⟨t, htf, fun w hw => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hw
  -- `A v` is within `ε / 2` of the difference quotient at `v`.
  have hclose : ‖A v - a⁻¹ • (T (v₀ + a • v) - T v₀)‖ ≤ ε / 2 := by
    have hnv : ‖a • v‖ ≤ ‖a‖ := by
      simpa [norm_smul] using
        mul_le_of_le_one_right (norm_nonneg a) (mem_closedBall_zero_iff.1 hv)
    have hAa : A (a • v) = a • A v := by simp
    have hsm : a • (A v - a⁻¹ • (T (v₀ + a • v) - T v₀))
        = -(T (v₀ + a • v) - T v₀ - A (a • v)) := by
      rw [hAa, smul_sub, smul_inv_smul₀ hane]
      abel
    have hkey := hdiff (a • v) (hnv.trans haδ)
    rw [← norm_neg, ← hsm, norm_smul] at hkey
    have hle : ‖a‖ * ‖A v - a⁻¹ • (T (v₀ + a • v) - T v₀)‖ ≤ ‖a‖ * (ε / 2) := by
      nlinarith [hkey, hnv, hε.le, norm_nonneg (a • v)]
    exact le_of_mul_le_mul_left hle ha0
  -- and the difference quotient is within `ε / 2` of the net.
  have hmem : a⁻¹ • (T (v₀ + a • v) - T v₀) ∈ (fun w => a⁻¹ • (w - T v₀)) '' (T '' B) :=
    ⟨T (v₀ + a • v), ⟨v₀ + a • v, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨y, hy, hdy⟩ := mem_iUnion₂.1 (hts hmem)
  refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
  rw [mem_ball] at hdy ⊢
  calc dist (A v) y ≤ dist (A v) (a⁻¹ • (T (v₀ + a • v) - T v₀)) + dist _ y :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_le_of_lt ?_ hdy
        rwa [dist_eq_norm]
    _ = ε := by ring

end FDeriv
