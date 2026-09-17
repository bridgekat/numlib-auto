import Numlib.Analysis.Normed.Operator.Compact.Banach
import NumlibSurface.Brezis.Chapter03.Section05

/-!
# Brezis §6.1: compact operators — definitions, elementary properties, adjoint

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §6.1, over real Banach spaces `E`, `F`
(`[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`, the completeness carried only where
the book's statement uses it). The book's `K(E, F)` is Mathlib's predicate `IsCompactOperator` on
`T : E →L[ℝ] F` and its submodule `compactOperator (RingHom.id ℝ) E F`; the Banach adjoint
`T* : F* → E*` is chapter 2's `ContinuousLinearMap.strongDualMap T`
(`Numlib/Analysis/Normed/Operator/Unbounded/Adjoint`); weak convergence `uₙ ⇀ u` is chapter 3's
`Brezis.Chapter03.WeakTendsto`. Theorem 6.1 and Proposition 6.3 are Mathlib's; Corollary 6.2,
Remark 1 and Theorem 6.4 (Schauder) delegate to the backbone
`Numlib/Analysis/Normed/Operator/Compact` and `…/Compact/Banach`, Remark 2 to the same.

## Main results

* `compactOperator_iff`, `theorem_6_1`, `theorem_6_1_submodule` — the Definition, and `K(E, F)`
  is a closed linear subspace of `L(E, F)`.
* `IsFiniteRank`, `IsFiniteRank.isCompactOperator`, `corollary_6_2` — finite-rank operators are
  compact, and so are norm limits of finite-rank operators.
* `remark_6_1`, `remark_6_1_nonlinear` — the approximation property of Hilbert spaces: a compact
  operator into a Hilbert space is a norm limit of finite-rank operators; and the nonlinear
  finite-rank approximation of a continuous map with relatively compact range.
* `proposition_6_3_left`, `proposition_6_3_right` — compositions with a compact operator.
* `theorem_6_4`, `theorem_6_4_mpr` — Schauder's theorem: `T` is compact iff `T*` is.
* `remark_6_2`, `remark_6_2_mpr` — a compact operator maps weakly convergent sequences to
  strongly convergent ones, and conversely on a reflexive space (Exercise 6.7).
-/

open Filter Topology

noncomputable section

namespace Brezis.Chapter06

open Brezis.Chapter03 (WeakTendsto)

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Compact operators -/

/-- **The Definition of §6.1.** A bounded operator `T ∈ L(E, F)` is compact if `T(B_E)` has
compact closure in `F` (in the strong topology); Mathlib's primitive definition
`IsCompactOperator` is the neighbourhood form, and this is its closed-ball reading at radius
`1`. -/
theorem compactOperator_iff (T : E →L[ℝ] F) :
    IsCompactOperator T ↔ IsCompact (closure (T '' Metric.closedBall 0 1)) := by
  have key := isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℝ] F) one_pos
  rwa [ContinuousLinearMap.coe_coe] at key

/-- **Theorem 6.1, closedness.** The set `K(E, F)` of compact operators is closed in `L(E, F)`
for the operator norm (`F` complete). -/
theorem theorem_6_1 [CompleteSpace F] : IsClosed {T : E →L[ℝ] F | IsCompactOperator T} :=
  isClosed_setOfPred_isCompactOperator

/-- **Theorem 6.1, the linear-subspace clause.** `K(E, F)` is a linear subspace of `L(E, F)` —
Mathlib's submodule `compactOperator (RingHom.id ℝ) E F`, whose carrier is the set of compact
operators — and it is closed: it equals its own topological closure. -/
theorem theorem_6_1_submodule [CompleteSpace F] :
    ((compactOperator (RingHom.id ℝ) E F : Submodule ℝ (E →L[ℝ] F)) : Set (E →L[ℝ] F)) =
        {T : E →L[ℝ] F | IsCompactOperator T} ∧
      (compactOperator (RingHom.id ℝ) E F).topologicalClosure =
        compactOperator (RingHom.id ℝ) E F :=
  ⟨rfl, compactOperator_topologicalClosure⟩

/-- **The Definition of §6.1, finite rank.** An operator `T ∈ L(E, F)` is of finite rank if its
range `R(T)` is finite dimensional. -/
def IsFiniteRank (T : E →L[ℝ] F) : Prop :=
  FiniteDimensional ℝ (LinearMap.range (T : E →ₗ[ℝ] F))

/-- "Clearly, any finite-rank operator is compact." -/
theorem IsFiniteRank.isCompactOperator {T : E →L[ℝ] F} (hT : IsFiniteRank T) :
    IsCompactOperator T :=
  haveI : FiniteDimensional ℝ (LinearMap.range (T : E →ₗ[ℝ] F)) := hT
  IsCompactOperator.of_finiteDimensional_range T

/-- **Corollary 6.2.** Let `(Tₙ)` be a sequence of finite-rank operators and `T ∈ L(E, F)` with
`‖Tₙ - T‖ → 0` (`F` complete). Then `T ∈ K(E, F)`. -/
theorem corollary_6_2 [CompleteSpace F] {T : ℕ → E →L[ℝ] F} (hT : ∀ n, IsFiniteRank (T n))
    {S : E →L[ℝ] F} (h : Tendsto (fun n => ‖T n - S‖) atTop (𝓝 0)) : IsCompactOperator S :=
  IsCompactOperator.of_tendsto (fun n => (hT n).isCompactOperator) h

/-- **Remark 1, the positive answer to the approximation problem in a Hilbert space.** For `F` a
Hilbert space, `T ∈ K(E, F)` and `ε > 0`, there is a finite-rank operator `Tε` with
`‖Tε - T‖ < ε` (the book's `2ε` with `ε` halved: `Tε = P_G T` for `G` the span of a finite
`ε/2`-net of `T(B_E)`). The rest of Remark 1 (Enflo's counterexample, Schauder bases) is
bibliographical. -/
theorem remark_6_1 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {T : E →L[ℝ] F} (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : E →L[ℝ] F, IsFiniteRank S ∧ ‖S - T‖ < ε :=
  hT.exists_finiteDimensional_range_norm_sub_lt hε

/-- **Remark 1, the nonlinear finite-rank approximation (3).** Let `X` be a topological space,
`F` a Banach space and `T : X → F` continuous with `T(X)` of compact closure. Then for every
`ε > 0` there is a continuous map `Tε : X → F` of finite rank (its range lies in a
finite-dimensional subspace) with `‖Tε x - T x‖ < ε` for all `x`. The book's construction: cover
`K = closure T(X)` by finitely many balls `B(fᵢ, ε/2)`, put `qᵢ(x) = max (ε - ‖T x - fᵢ‖, 0)`
and `Tε x = ∑ qᵢ(x) fᵢ / ∑ qᵢ(x)`, a convex combination of points within `ε` of `T x`. This is
the step from Brouwer's to Schauder's fixed point theorem (Exercise 6.26). -/
theorem remark_6_1_nonlinear {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {T : X → F} (hT : Continuous T)
    (hK : IsCompact (closure (Set.range T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ Tε : X → F, Continuous Tε ∧
      (∃ G : Submodule ℝ F, FiniteDimensional ℝ G ∧ ∀ x, Tε x ∈ G) ∧ ∀ x, ‖Tε x - T x‖ < ε := by
  classical
  obtain ⟨t, -, htfin, hcover⟩ := finite_cover_balls_of_compact hK (half_pos hε)
  obtain ⟨q, hq⟩ : ∃ q : F → X → ℝ, ∀ f x, q f x = max (ε - ‖T x - f‖) 0 := ⟨_, fun _ _ => rfl⟩
  have hq_cont : ∀ f, Continuous (q f) := fun f => by
    have : q f = fun x => max (ε - ‖T x - f‖) 0 := funext (hq f)
    rw [this]
    exact (continuous_const.sub (hT.sub continuous_const).norm).max continuous_const
  have hq_nonneg : ∀ f x, 0 ≤ q f x := fun f x => by rw [hq]; exact le_max_right _ _
  -- every `T x` is within `ε / 2` of some `f₀ ∈ t`, so `∑ qᵢ x > 0`
  have hnear : ∀ x, ∃ f ∈ htfin.toFinset, ‖T x - f‖ < ε / 2 := fun x => by
    obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (hcover (subset_closure ⟨x, rfl⟩))
    exact ⟨f, htfin.mem_toFinset.2 hf, by rwa [Metric.mem_ball, dist_eq_norm] at hxf⟩
  have hQ_pos : ∀ x, 0 < ∑ f ∈ htfin.toFinset, q f x := fun x => by
    obtain ⟨f, hf, hxf⟩ := hnear x
    have h1 : ε / 2 ≤ q f x := by
      rw [hq]
      exact le_max_of_le_left (by linarith)
    exact lt_of_lt_of_le (half_pos hε)
      (h1.trans (Finset.single_le_sum (fun g _ => hq_nonneg g x) hf))
  refine ⟨fun x => (∑ f ∈ htfin.toFinset, q f x)⁻¹ • ∑ f ∈ htfin.toFinset, q f x • f, ?_,
    ⟨Submodule.span ℝ (htfin.toFinset : Set F), inferInstance, fun x => ?_⟩, fun x => ?_⟩
  · -- continuity
    exact ((continuous_finsetSum _ fun f _ => hq_cont f).inv₀ fun x => (hQ_pos x).ne').smul
      (continuous_finsetSum _ fun f _ => (hq_cont f).smul continuous_const)
  · -- range in the span of the `fᵢ`
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun f hf =>
      Submodule.smul_mem _ _ (Submodule.subset_span hf))
  · -- the error bound
    have hrw : (∑ f ∈ htfin.toFinset, q f x)⁻¹ • ∑ f ∈ htfin.toFinset, q f x • f - T x =
        (∑ f ∈ htfin.toFinset, q f x)⁻¹ • ∑ f ∈ htfin.toFinset, q f x • (f - T x) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, smul_smul,
        inv_mul_cancel₀ (hQ_pos x).ne', one_smul]
    rw [hrw, norm_smul, norm_inv, Real.norm_of_nonneg (hQ_pos x).le]
    have hlt : ‖∑ f ∈ htfin.toFinset, q f x • (f - T x)‖ < (∑ f ∈ htfin.toFinset, q f x) * ε := by
      calc ‖∑ f ∈ htfin.toFinset, q f x • (f - T x)‖
          ≤ ∑ f ∈ htfin.toFinset, ‖q f x • (f - T x)‖ := norm_sum_le _ _
        _ = ∑ f ∈ htfin.toFinset, q f x * ‖f - T x‖ := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (hq_nonneg f x)]
        _ < ∑ f ∈ htfin.toFinset, q f x * ε := by
            obtain ⟨f₀, hf₀, hxf₀⟩ := hnear x
            refine Finset.sum_lt_sum (fun f _ => ?_) ⟨f₀, hf₀, ?_⟩
            · rcases (hq_nonneg f x).eq_or_lt with h | h
              · rw [← h, zero_mul, zero_mul]
              · have hlt' : ‖f - T x‖ < ε := by
                  rw [norm_sub_rev]
                  by_contra hge
                  have : q f x = 0 := by
                    rw [hq]
                    exact max_eq_right (by linarith [not_lt.1 hge])
                  linarith
                exact mul_le_mul_of_nonneg_left hlt'.le (hq_nonneg f x)
            · have hpos : 0 < q f₀ x := by
                rw [hq]
                exact lt_of_lt_of_le (half_pos hε) (le_max_of_le_left (by linarith))
              have : ‖f₀ - T x‖ < ε := by
                rw [norm_sub_rev]
                linarith
              exact mul_lt_mul_of_pos_left this hpos
        _ = (∑ f ∈ htfin.toFinset, q f x) * ε := (Finset.sum_mul _ _ _).symm
    calc (∑ f ∈ htfin.toFinset, q f x)⁻¹ * ‖∑ f ∈ htfin.toFinset, q f x • (f - T x)‖
        < (∑ f ∈ htfin.toFinset, q f x)⁻¹ * ((∑ f ∈ htfin.toFinset, q f x) * ε) :=
          mul_lt_mul_of_pos_left hlt (inv_pos.2 (hQ_pos x))
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ (hQ_pos x).ne', one_mul]

/-- **Proposition 6.3, first case.** For `T ∈ L(E, F)` and `S ∈ K(F, G)`, `S ∘ T ∈ K(E, G)`. -/
theorem proposition_6_3_left (T : E →L[ℝ] F) {S : F →L[ℝ] G} (hS : IsCompactOperator S) :
    IsCompactOperator (S ∘L T) :=
  hS.comp_clm T

/-- **Proposition 6.3, second case.** For `T ∈ K(E, F)` and `S ∈ L(F, G)`, `S ∘ T ∈ K(E, G)`. -/
theorem proposition_6_3_right {T : E →L[ℝ] F} (hT : IsCompactOperator T) (S : F →L[ℝ] G) :
    IsCompactOperator (S ∘L T) :=
  hT.clm_comp S

/-! ### Schauder's theorem and weak-to-strong continuity -/

/-- **Theorem 6.4 (Schauder).** If `T ∈ K(E, F)` then `T* ∈ K(F*, E*)`, the Banach adjoint
`T* = ContinuousLinearMap.strongDualMap T`. -/
theorem theorem_6_4 [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T) : IsCompactOperator T.strongDualMap :=
  hT.strongDualMap

/-- **Theorem 6.4, "and conversely".** If `T* ∈ K(F*, E*)` then `T ∈ K(E, F)`: only the
completeness of `F` is used. -/
theorem theorem_6_4_mpr [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T.strongDualMap) : IsCompactOperator T :=
  IsCompactOperator.of_strongDualMap hT

/-- **Remark 2, first sentence.** Let `T ∈ K(E, F)`. If `uₙ ⇀ u` weakly in `E` then
`T uₙ → T u` strongly in `F` (also Exercise 6.7, question 2). -/
theorem remark_6_2 [CompleteSpace E] [CompleteSpace F] {T : E →L[ℝ] F}
    (hT : IsCompactOperator T) {u : ℕ → E} {x : E} (hu : WeakTendsto u x) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T x)) :=
  hT.tendsto_of_tendsto_toWeakSpace hu

/-- **Remark 2, second sentence**, "the converse is also true if `E` is reflexive (see
Exercise 6.7)": if `T ∈ L(E, F)` maps every weakly convergent sequence `uₙ ⇀ u` to a strongly
convergent one `T uₙ → T u`, and `E` is reflexive (chapter 3's `IsReflexive`), then
`T ∈ K(E, F)` (Exercise 6.7, question 4). -/
theorem remark_6_2_mpr [CompleteSpace E] [CompleteSpace F] (hE : Brezis.Chapter03.IsReflexive E)
    (T : E →L[ℝ] F)
    (h : ∀ (u : ℕ → E) (x : E), WeakTendsto u x → Tendsto (fun n => T (u n)) atTop (𝓝 (T x))) :
    IsCompactOperator T :=
  haveI := Brezis.Chapter03.isReflexive_iff.1 hE
  IsCompactOperator.of_forall_tendsto_of_tendsto_toWeakSpace T h

end Brezis.Chapter06

end
