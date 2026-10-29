import Numlib.Optimization.Optimality.Unconstrained
import Numlib.Optimization.Subproblem.MinCurvature
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Basic.Real.Pointwise

/-!
# Approximate optimality and criticality measures

Approximate optimality notions and criticality measures shared by the evaluation-complexity
results of [cartis2022evaluation] ((1.1.5), (2.1.2), (3.2.6), (12.1.10), (12.1.25), (13.1.5)).

## Main definitions

* `Optimization.IsApproxFirstOrder f x ε`: `‖∇f(x)‖ ≤ ε` ((2.1.2));
* `Optimization.IsApproxSecondOrder f x ε₁ ε₂`: `‖∇f(x)‖ ≤ ε₁` and `λ_min[∇²f(x)] ≥ -ε₂`
  ((3.2.6));
* `Optimization.criticality₂ f x = max(0, -λ_min[∇²f(x)])`, the second-order criticality measure
  `ω₂` of Section 1.1.2.6 (the first-order one is `‖fderiv ℝ f x‖`);
* `Optimization.decrementMeasure Δ δ S = sup {Δ d | ‖d‖ ≤ δ, d ∈ S}`: the largest decrease of a
  model decrement `Δ` over feasible displacements of length at most `δ`;
* `Optimization.taylorMeasure D j δ S`: the decrement measure of the Taylor decrement of order `j`
  of derivative data `D`, the book's `φ^δ_{f,j}(x)` ((12.1.10)) for `D = ftaylorSeries ℝ f x`,
  `S = univ`;
* `Optimization.IsEpsDeltaApprox D S q ε δ`, `Optimization.IsEpsApprox D S q ε`: condition
  (12.1.25) for given radii `δ`, and the `(ε, δ)`-approximate `q`-th order minimizer;
* `Optimization.hessianMatrix f x`: on `EuclideanSpace ℝ ι`, the Hessian matrix
  `[∇²f(x)]ᵢⱼ = ∇²f(x)[eᵢ, eⱼ]`, which represents `hessianOperator f x` for `f` `C²` at `x`;
* `Optimization.hessianOperator f x`: the Hessian `∇²f(x)` as an operator, the derivative of the
  gradient.

## Design

The first- and second-order notions are stated with `fderiv` and `minCurvature`, so they make
sense on any real normed space; on a complete inner product space `‖fderiv ℝ f x‖ = ‖∇f(x)‖`
(`Optimization.isApproxFirstOrder_iff_norm_gradient`). The book's tolerance `ε₂ = +∞` (second-order
test switched off) is not a real number; algorithm statements represent it separately.

The Taylor-decrement measure is defined from derivative *data*
`D : FormalMultilinearSeries ℝ E ℝ` and a set `S` of feasible displacements, so that the same
definition serves exact derivatives (`D = ftaylorSeries ℝ f x`), inexact ones (the `φ̄` of
(13.1.5)) and constraints (`S = {d | x + d ∈ C}`). All the measures of the book are instances of
`decrementMeasure`, whose API (`le_decrementMeasure`, `decrementMeasure_le`, monotonicity,
`abs_decrementMeasure_sub_le`, attainment `exists_decrementMeasure_eq`) is stated for an
arbitrary decrement function. The Taylor measure is finite without any compactness, since the
Taylor decrement is bounded on balls (`bddAbove_taylorDecrement`).
-/

open Filter Set Topology Metric Finset
open scoped Nat RealInnerProductSpace

namespace Optimization

/-! ### The decrement measure -/

section Decrement

variable {E : Type*} [NormedAddCommGroup E]


/-- The decrement measure `sup {Δ d | ‖d‖ ≤ δ, d ∈ S}`: the largest decrease `Δ d` of a model
over feasible displacements of length at most `δ` ([cartis2022evaluation], (12.1.10), (13.1.5),
(14.1.6), (14.1.14), (14.2.2), (14.2.4) for the respective decrements `Δ`). -/
noncomputable def decrementMeasure (Δ : E → ℝ) (δ : ℝ) (S : Set E) : ℝ :=
  sSup (Δ '' (closedBall 0 δ ∩ S))

variable {Δ Δ' : E → ℝ} {δ δ' : ℝ} {S S' : Set E} {d : E}

/-- Unfolding lemma for `decrementMeasure`. -/
theorem decrementMeasure_def :
    decrementMeasure Δ δ S = sSup (Δ '' (closedBall 0 δ ∩ S)) := rfl

/-- Every feasible decrease is at most the measure (when the decreases are bounded above). -/
theorem le_decrementMeasure (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S)))
    (hd : d ∈ closedBall 0 δ ∩ S) : Δ d ≤ decrementMeasure Δ δ S :=
  le_csSup hbdd (mem_image_of_mem Δ hd)

/-- If `0` is feasible and `Δ 0 = 0`, the measure is nonnegative. -/
theorem decrementMeasure_nonneg (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ0 : Δ 0 = 0) : 0 ≤ decrementMeasure Δ δ S :=
  hΔ0 ▸ le_decrementMeasure hbdd ⟨mem_closedBall_self hδ, h0⟩

/-- An upper bound on all feasible decreases bounds the measure. -/
theorem decrementMeasure_le {B : ℝ} (hne : (closedBall 0 δ ∩ S).Nonempty)
    (h : ∀ d ∈ closedBall 0 δ ∩ S, Δ d ≤ B) : decrementMeasure Δ δ S ≤ B :=
  csSup_le (hne.image Δ) (forall_mem_image.2 h)

/-- The measure is monotone in the radius. -/
theorem decrementMeasure_mono_radius (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ' ∩ S))) (hδ : δ ≤ δ') :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ δ' S :=
  csSup_le_csSup hbdd (hne.image Δ)
    (image_mono (inter_subset_inter_left _ (closedBall_subset_closedBall hδ)))

/-- The measure is monotone in the feasible set. -/
theorem decrementMeasure_mono_set (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S'))) (hS : S ⊆ S') :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ δ S' :=
  csSup_le_csSup hbdd (hne.image Δ) (image_mono (inter_subset_inter_right _ hS))

/-- The measure is monotone in the decrement. -/
theorem decrementMeasure_mono_fun (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ' '' (closedBall 0 δ ∩ S))) (h : ∀ d ∈ closedBall 0 δ ∩ S, Δ d ≤ Δ' d) :
    decrementMeasure Δ δ S ≤ decrementMeasure Δ' δ S :=
  decrementMeasure_le hne fun d hd => (h d hd).trans (le_decrementMeasure hbdd hd)

/-- Perturbation of the decrement: if `|Δ d - Δ' d| ≤ e` on the feasible ball, the measures
differ by at most `e`. -/
theorem abs_decrementMeasure_sub_le {e : ℝ} (hne : (closedBall 0 δ ∩ S).Nonempty)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) (hbdd' : BddAbove (Δ' '' (closedBall 0 δ ∩ S)))
    (h : ∀ d ∈ closedBall 0 δ ∩ S, |Δ d - Δ' d| ≤ e) :
    |decrementMeasure Δ δ S - decrementMeasure Δ' δ S| ≤ e := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine decrementMeasure_le hne fun d hd => ?_
    have := le_decrementMeasure hbdd' hd
    linarith [(abs_sub_le_iff.1 (h d hd)).1]
  · rw [sub_le_iff_le_add]
    refine decrementMeasure_le hne fun d hd => ?_
    have := le_decrementMeasure hbdd hd
    linarith [(abs_sub_le_iff.1 (h d hd)).2]

/-- The decrement measure is positively homogeneous in the decrement:
`sup (a Δ) = a sup Δ` for `a ≥ 0`. -/
theorem decrementMeasure_const_mul {Δ : E → ℝ} {δ a : ℝ} {S : Set E} (ha : 0 ≤ a) :
    decrementMeasure (fun d => a * Δ d) δ S = a * decrementMeasure Δ δ S := by
  rw [decrementMeasure_def, decrementMeasure_def, ← smul_eq_mul (a := a),
    ← Real.sSup_smul_of_nonneg ha, ← Set.image_smul, Set.image_image]
  rfl

variable [NormedSpace ℝ E]

/-- In finite dimension, with `S` closed and `Δ` continuous on the feasible ball, the measure is
attained. -/
theorem exists_decrementMeasure_eq [FiniteDimensional ℝ E] (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) :
    ∃ d ∈ closedBall 0 δ ∩ S, Δ d = decrementMeasure Δ δ S := by
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn ⟨0, mem_closedBall_self hδ, h0⟩ hΔ
  refine ⟨d, hd, ?_⟩
  exact (IsGreatest.csSup_eq ⟨mem_image_of_mem Δ hd, forall_mem_image.2 hmax⟩).symm

/-- A continuous decrement on a closed feasible set that is star-shaped about `0` takes every
fraction `ς ∈ [0, 1]` of its measure (intermediate value theorem along the segment to a
maximizer). -/
theorem exists_decrementMeasure_mul_eq [FiniteDimensional ℝ E] (hS : IsClosed S)
    (h0 : (0 : E) ∈ S) (hstar : StarConvex ℝ 0 S) (hδ : 0 ≤ δ)
    (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) {ς : ℝ} (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d ∈ closedBall 0 δ ∩ S, Δ d = ς * decrementMeasure Δ δ S := by
  obtain ⟨d, hd, hdM⟩ := exists_decrementMeasure_eq hS h0 hδ hΔ
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • d ∈ closedBall (0 : E) δ ∩ S := by
    intro t ht
    refine ⟨?_, hstar.smul_mem hd.2 ht.1 ht.2⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (mem_closedBall_zero_iff.1 hd.1)
  have hg : ContinuousOn (fun t : ℝ => Δ (t • d)) (Icc 0 1) :=
    hΔ.comp (continuous_id.smul continuous_const).continuousOn hseg
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  have hM : 0 ≤ decrementMeasure Δ δ S :=
    decrementMeasure_nonneg (hK.bddAbove_image hΔ) h0 hδ hΔ0
  have hmem : ς * decrementMeasure Δ δ S ∈ Icc (Δ ((0 : ℝ) • d)) (Δ ((1 : ℝ) • d)) := by
    rw [zero_smul, one_smul, hΔ0, hdM]
    exact ⟨mul_nonneg hς.1 hM, mul_le_of_le_one_left hM hς.2⟩
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc zero_le_one hg hmem
  exact ⟨t • d, hseg t ht, hteq⟩

end Decrement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### First- and second-order approximate minimizers -/

/-- `x` is an `ε`-approximate first-order minimizer of `f`: `‖∇f(x)‖ ≤ ε`
([cartis2022evaluation], (2.1.2)). -/
def IsApproxFirstOrder (f : E → ℝ) (x : E) (ε : ℝ) : Prop := ‖fderiv ℝ f x‖ ≤ ε

/-- Unfolding lemma for `IsApproxFirstOrder`. -/
theorem isApproxFirstOrder_iff {f : E → ℝ} {x : E} {ε : ℝ} :
    IsApproxFirstOrder f x ε ↔ ‖fderiv ℝ f x‖ ≤ ε := Iff.rfl

/-- `x` is an `(ε₁, ε₂)`-approximate second-order minimizer of `f`: `‖∇f(x)‖ ≤ ε₁` and
`λ_min[∇²f(x)] ≥ -ε₂` ([cartis2022evaluation], (3.2.6)). -/
def IsApproxSecondOrder (f : E → ℝ) (x : E) (ε₁ ε₂ : ℝ) : Prop :=
  ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ minCurvature (iteratedFDeriv ℝ 2 f x)

/-- Unfolding lemma for `IsApproxSecondOrder`. -/
theorem isApproxSecondOrder_iff {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ} :
    IsApproxSecondOrder f x ε₁ ε₂ ↔
      ‖fderiv ℝ f x‖ ≤ ε₁ ∧ -ε₂ ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := Iff.rfl

/-- An approximate second-order minimizer is an approximate first-order minimizer. -/
theorem IsApproxSecondOrder.isApproxFirstOrder {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ}
    (h : IsApproxSecondOrder f x ε₁ ε₂) : IsApproxFirstOrder f x ε₁ := h.1

/-- The second-order criticality measure `ω₂(x) = max(0, -λ_min[∇²f(x)])`
([cartis2022evaluation], (1.1.5) and Section 1.1.2.6). -/
noncomputable def criticality₂ (f : E → ℝ) (x : E) : ℝ :=
  max 0 (-minCurvature (iteratedFDeriv ℝ 2 f x))

/-- The second-order criticality measure is nonnegative. -/
theorem criticality₂_nonneg (f : E → ℝ) (x : E) : 0 ≤ criticality₂ f x := le_max_left _ _

/-- `ω₂(x) ≤ ε ↔ λ_min[∇²f(x)] ≥ -ε` for `ε ≥ 0`. -/
theorem criticality₂_le_iff {f : E → ℝ} {x : E} {ε : ℝ} (hε : 0 ≤ ε) :
    criticality₂ f x ≤ ε ↔ -ε ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := by
  rw [criticality₂, max_le_iff, neg_le]
  exact and_iff_right hε

/-- `ω₂(x) = 0 ↔ λ_min[∇²f(x)] ≥ 0`. -/
theorem criticality₂_eq_zero_iff {f : E → ℝ} {x : E} :
    criticality₂ f x = 0 ↔ 0 ≤ minCurvature (iteratedFDeriv ℝ 2 f x) := by
  rw [← (criticality₂_nonneg f x).ge_iff_eq', criticality₂_le_iff le_rfl, neg_zero]

/-- The approximate second-order condition in terms of the two criticality measures. -/
theorem isApproxSecondOrder_iff_criticality₂_le {f : E → ℝ} {x : E} {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) :
    IsApproxSecondOrder f x ε₁ ε₂ ↔ ‖fderiv ℝ f x‖ ≤ ε₁ ∧ criticality₂ f x ≤ ε₂ := by
  rw [isApproxSecondOrder_iff, criticality₂_le_iff hε₂]

/-- At a local minimizer of a function `C²` at `x` both criticality measures vanish
((1.1.5)). -/
theorem IsLocalMin.criticality_eq_zero {f : E → ℝ} {x : E} (hmin : IsLocalMin f x)
    (hf : ContDiffAt ℝ 2 f x) : ‖fderiv ℝ f x‖ = 0 ∧ criticality₂ f x = 0 :=
  ⟨by rw [hmin.fderiv_eq_zero, norm_zero],
    criticality₂_eq_zero_iff.2 (IsLocalMin.minCurvature_iteratedFDeriv_two_nonneg hmin hf)⟩

variable {δ : ℝ} {S : Set E} {d : E}

/-! ### The Taylor-decrement measure -/

/-- The Taylor decreases over a feasible ball are bounded above, so the Taylor measure is a
supremum of a bounded set. -/
theorem bddAbove_taylorDecrement (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (S : Set E) :
    BddAbove (D.taylorDecrement j '' (closedBall 0 δ ∩ S)) := by
  refine ⟨∑ i ∈ Icc 1 j, ‖D i‖ * δ ^ i / i !, forall_mem_image.2 fun d hd => ?_⟩
  exact (le_abs_self _).trans
    (D.abs_taylorDecrement_le_of_norm_le j (mem_closedBall_zero_iff.1 hd.1))

/-- The Taylor-decrement measure `φ^δ_j = sup {ΔT_j(d) | ‖d‖ ≤ δ, d ∈ S}`
([cartis2022evaluation], (12.1.10)): for `D = ftaylorSeries ℝ f x` and `S = univ` it is
`f(x) - min_{‖d‖ ≤ δ} T_{f,j}(x, d)`; with `S = {d | x + d ∈ C}` it is the constrained measure of
Chapters 6 and 14; with inexact data `D` it is the `φ̄` of (13.1.5). -/
noncomputable def taylorMeasure (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ)
    (S : Set E) : ℝ :=
  decrementMeasure (D.taylorDecrement j) δ S

/-- Unfolding lemma for `taylorMeasure`. -/
theorem taylorMeasure_eq_sSup (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (S : Set E) :
    taylorMeasure D j δ S = sSup (D.taylorDecrement j '' (closedBall 0 δ ∩ S)) := rfl

/-- Every feasible Taylor decrease is at most the measure. -/
theorem taylorDecrement_le_taylorMeasure (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ)
    (hd : d ∈ closedBall 0 δ ∩ S) : D.taylorDecrement j d ≤ taylorMeasure D j δ S :=
  le_decrementMeasure (bddAbove_taylorDecrement D j δ S) hd

/-- The Taylor measure is nonnegative when `0` is feasible. -/
theorem taylorMeasure_nonneg (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) : 0 ≤ taylorMeasure D j δ S :=
  decrementMeasure_nonneg (bddAbove_taylorDecrement D j δ S) h0 hδ
    (D.taylorDecrement_zero_right j)

/-- The supremum of `-ℓ` over the closed ball of radius `δ ≥ 0` is `δ ‖ℓ‖`. -/
theorem sSup_neg_apply_closedBall (ℓ : E →L[ℝ] ℝ) (hδ : 0 ≤ δ) :
    sSup ((fun s => -ℓ s) '' closedBall 0 δ) = δ * ‖ℓ‖ := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ((nonempty_closedBall.2 hδ.le).image _) (forall_mem_image.2 fun s hs => ?_) fun b hb => ?_
  · calc -ℓ s ≤ ‖ℓ s‖ := (neg_le_abs _).trans (Real.norm_eq_abs _).ge
      _ ≤ ‖ℓ‖ * ‖s‖ := ℓ.le_opNorm s
      _ ≤ δ * ‖ℓ‖ := by rw [mul_comm]; gcongr; exact mem_closedBall_zero_iff.1 hs
  · obtain ⟨u, hu, hbu⟩ := ℓ.exists_lt_apply_of_lt_opNorm (r := b / δ)
      (by rwa [div_lt_iff₀ hδ, mul_comm])
    rw [div_lt_iff₀ hδ, Real.norm_eq_abs] at hbu
    have hmem : ∀ c : ℝ, |c| ≤ 1 → c • δ • u ∈ closedBall (0 : E) δ := fun c hc => by
      rw [mem_closedBall_zero_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hδ]
      calc |c| * (δ * ‖u‖) ≤ 1 * (δ * 1) := by gcongr
        _ = δ := by ring
    rcases le_total 0 (ℓ u) with h | h
    · refine ⟨_, ⟨(-1 : ℝ) • δ • u, hmem (-1) (by simp), rfl⟩, ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [abs_of_nonneg h] at hbu
      linarith
    · refine ⟨_, ⟨(1 : ℝ) • δ • u, hmem 1 (by simp), rfl⟩, ?_⟩
      simp only [map_smul, smul_eq_mul]
      rw [abs_of_nonpos h] at hbu
      linarith

/-- **The first-order measure** ([cartis2022evaluation], (12.1.12)): for `δ ≥ 0`,
`φ^δ_1 = δ ‖D₁‖`, the supremum of the linear functional `-D₁` over the ball. -/
theorem taylorMeasure_one_eq (D : FormalMultilinearSeries ℝ E ℝ) (hδ : 0 ≤ δ) :
    taylorMeasure D 1 δ univ = δ * ‖D 1‖ := by
  set ℓ : E →L[ℝ] ℝ := continuousMultilinearCurryFin1 ℝ E ℝ (D 1)
  have hℓ : ∀ s, ℓ s = D 1 (fun _ => s) := fun s => by
    simp only [ℓ, continuousMultilinearCurryFin1_apply]
    congr 1
  have hnorm : ‖ℓ‖ = ‖D 1‖ := LinearIsometryEquiv.norm_map _ _
  rw [taylorMeasure_eq_sSup, Set.inter_univ, ← hnorm, ← sSup_neg_apply_closedBall ℓ hδ]
  congr 1
  refine image_congr fun s _ => ?_
  rw [D.taylorDecrement_one_apply, hℓ]

/-- Perturbation of the Taylor measure by inexact data ([cartis2022evaluation], (13.1.6)):
`|φ^δ_j(D) - φ^δ_j(D')| ≤ ∑_{i=1}^j ‖D_i - D'_i‖ δ^i / i!`. -/
theorem abs_taylorMeasure_sub_le (D D' : FormalMultilinearSeries ℝ E ℝ) (j : ℕ)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    |taylorMeasure D j δ S - taylorMeasure D' j δ S| ≤
      ∑ i ∈ Icc 1 j, ‖D i - D' i‖ * δ ^ i / i ! := by
  refine abs_decrementMeasure_sub_le ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_taylorDecrement D j δ S) (bddAbove_taylorDecrement D' j δ S) fun d hd => ?_
  refine (D.abs_taylorDecrement_sub_le D' j d).trans (sum_le_sum fun i _ => ?_)
  gcongr
  exact mem_closedBall_zero_iff.1 hd.1

/-- In finite dimension, with `S` closed and `0 ∈ S`, the Taylor measure is attained (at an
"optimality displacement" of the book). -/
theorem exists_taylorMeasure_eq [FiniteDimensional ℝ E] (D : FormalMultilinearSeries ℝ E ℝ)
    (j : ℕ) (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ S, D.taylorDecrement j d = taylorMeasure D j δ S :=
  exists_decrementMeasure_eq hS h0 hδ (D.continuous_taylorDecrement j).continuousOn

/-- Condition (12.1.25) of [cartis2022evaluation] for given optimality radii `δ`:
`φ^{δ_j}_j ≤ ε_j δ_j^j / j!` for `1 ≤ j ≤ q`, for the data `D` and the feasible displacements
`S`. Here `δ` is a fixed parameter; the book's `(ε, δ)`-approximate `q`-th order minimizer asks
for *some* radii `δ ∈ (0, 1]^q`, which is `IsEpsApprox`. For `D = ftaylorSeries ℝ f x` and
`S = univ` this is the unconstrained notion; constrained variants use `S = {d | x + d ∈ C}`. -/
def IsEpsDeltaApprox (D : FormalMultilinearSeries ℝ E ℝ) (S : Set E) (q : ℕ) (ε δ : ℕ → ℝ) :
    Prop :=
  ∀ j ∈ Finset.Icc 1 q, taylorMeasure D j (δ j) S ≤ ε j * δ j ^ j / j !

/-- Unfolding lemma for `IsEpsDeltaApprox`. -/
theorem isEpsDeltaApprox_iff {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ} {ε δ : ℕ → ℝ} :
    IsEpsDeltaApprox D S q ε δ ↔
      ∀ j ∈ Finset.Icc 1 q, taylorMeasure D j (δ j) S ≤ ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- The `(ε, δ)`-approximate `q`-th order minimizer of [cartis2022evaluation], Key Definition
with (12.1.25): condition (12.1.25) holds for some optimality radii `δ ∈ (0, 1]^q`. -/
def IsEpsApprox (D : FormalMultilinearSeries ℝ E ℝ) (S : Set E) (q : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∃ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δ j ∈ Ioc (0 : ℝ) 1) ∧ IsEpsDeltaApprox D S q ε δ

/-- Unfolding lemma for `IsEpsApprox`. -/
theorem isEpsApprox_iff {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ} {ε : ℕ → ℝ} :
    IsEpsApprox D S q ε ↔
      ∃ δ : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, δ j ∈ Ioc (0 : ℝ) 1) ∧ IsEpsDeltaApprox D S q ε δ :=
  Iff.rfl

/-- The first-order Taylor decrement is `-D₁[s]` (now
`FormalMultilinearSeries.taylorDecrement_one_apply`). -/
@[deprecated FormalMultilinearSeries.taylorDecrement_one_apply (since := "2026-10-26")]
theorem taylorDecrement_one_apply (D : FormalMultilinearSeries ℝ E ℝ) (s : E) :
    D.taylorDecrement 1 s = -D 1 (fun _ => s) :=
  D.taylorDecrement_one_apply s

/-! ### Gradient and Hessian on inner product spaces -/

/-! ### Monotonicity of the low-order measures in the radius -/

section Scale

/-- Scaling a step scales the `i`-th term of a jet by `c^i`. -/
theorem formalMultilinearSeries_apply_smul (D : FormalMultilinearSeries ℝ E ℝ) (i : ℕ) (c : ℝ)
    (d : E) : D i (fun _ => c • d) = c ^ i * D i (fun _ => d) := by
  have := (D i).map_smul_univ (fun _ => c) (fun _ => d)
  simpa [Finset.prod_const] using this

/-- **Scaling of decrements of order `≤ 2`**: for `t ∈ [0, 1]` and any `d` there is `d'` with
`‖d'‖ ≤ t ‖d‖` and `t^j ΔT_j(d) ≤ ΔT_j(d')` (`d' ∈ {0, t d, -t d}`). -/
theorem exists_taylorDecrement_scale_ge (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ}
    (hj : j ≤ 2) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (d : E) :
    ∃ d', ‖d'‖ ≤ t * ‖d‖ ∧ t ^ j * D.taylorDecrement j d ≤ D.taylorDecrement j d' := by
  interval_cases j
  · refine ⟨0, by rw [norm_zero]; positivity, ?_⟩
    simp [FormalMultilinearSeries.taylorDecrement_eq]
  · refine ⟨t • d, by rw [norm_smul, Real.norm_of_nonneg ht0], ?_⟩
    rw [FormalMultilinearSeries.taylorDecrement_one_apply,
      FormalMultilinearSeries.taylorDecrement_one_apply, formalMultilinearSeries_apply_smul]
    ring_nf; rfl
  · set a := -(D 1 fun _ => d)
    set b := -2⁻¹ * D 2 fun _ => d
    have hT : ∀ c : ℝ, D.taylorDecrement 2 (c • d) = c * a + c ^ 2 * b := fun c => by
      rw [FormalMultilinearSeries.taylorDecrement_two, formalMultilinearSeries_apply_smul,
        formalMultilinearSeries_apply_smul]
      simp only [a, b]; ring
    have h1 : D.taylorDecrement 2 d = a + b := by
      have := hT 1; simpa using this
    rcases le_or_gt 0 a with ha | ha
    · refine ⟨t • d, by rw [norm_smul, Real.norm_of_nonneg ht0], ?_⟩
      rw [hT, h1]; nlinarith [mul_nonneg ht0 ha, mul_nonneg (mul_nonneg ht0 ht0) ha]
    · refine ⟨(-t) • d, by rw [norm_smul, norm_neg, Real.norm_of_nonneg ht0], ?_⟩
      rw [hT, h1]; nlinarith [mul_nonneg ht0 (le_of_lt (neg_pos.2 ha)),
        mul_nonneg (mul_nonneg ht0 ht0) (le_of_lt (neg_pos.2 ha))]

/-- **The measures of orders `≤ 2` decrease slowly in the radius** (unconstrained case): for
`0 < δ' ≤ δ` and `j ≤ 2`, `(δ'/δ)^j φ^δ_j ≤ φ^{δ'}_j`, i.e. `δ ↦ φ^δ_j/δ^j` is non-increasing. -/
theorem pow_div_mul_taylorMeasure_le (D : FormalMultilinearSeries ℝ E ℝ) {j : ℕ} (hj : j ≤ 2)
    {δ δ' : ℝ} (hδ' : 0 < δ') (hδδ' : δ' ≤ δ) :
    (δ' / δ) ^ j * taylorMeasure D j δ univ ≤ taylorMeasure D j δ' univ := by
  have hδ : 0 < δ := hδ'.trans_le hδδ'
  set t := δ' / δ
  have ht0 : 0 < t := div_pos hδ' hδ
  have ht1 : t ≤ 1 := (div_le_one hδ).2 hδδ'
  have htj : 0 < t ^ j := pow_pos ht0 j
  rw [← le_div_iff₀' htj]
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ.le, mem_univ _⟩ fun d hd => ?_
  obtain ⟨d', hd'n, hd'⟩ := exists_taylorDecrement_scale_ge D hj ht0.le ht1 d
  have hd'm : d' ∈ closedBall 0 δ' ∩ univ := by
    refine ⟨mem_closedBall_zero_iff.2 (hd'n.trans ?_), mem_univ _⟩
    calc t * ‖d‖ ≤ t * δ := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hd.1) ht0.le
      _ = δ' := by simp only [t]; field_simp
  rw [le_div_iff₀' htj]
  exact hd'.trans (taylorDecrement_le_taylorMeasure D j hd'm)

end Scale

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f : F → ℝ} {x : F}

/-- On a complete real inner product space `‖∇f(x)‖ = ‖fderiv ℝ f x‖`. -/
theorem norm_gradient_eq (f : F → ℝ) (x : F) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ F).symm.norm_map _

/-- On a complete inner product space the first-order test reads `‖∇f(x)‖ ≤ ε`. -/
theorem isApproxFirstOrder_iff_norm_gradient {ε : ℝ} :
    IsApproxFirstOrder f x ε ↔ ‖gradient f x‖ ≤ ε := by
  rw [isApproxFirstOrder_iff, norm_gradient_eq]

/-- The first-order measure of a function ([cartis2022evaluation], (12.1.12)):
`φ^δ_{f,1}(x) = δ ‖∇f(x)‖` for `δ ≥ 0`. -/
theorem taylorMeasure_one_ftaylorSeries (f : F → ℝ) (x : F) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f x) 1 δ univ = δ * ‖gradient f x‖ := by
  rw [taylorMeasure_one_eq _ hδ, norm_gradient_eq, ← norm_iteratedFDeriv_one]
  rfl

/-- The Riesz map `F* → F` as a real continuous linear map. -/
private noncomputable def rieszL : StrongDual ℝ F →L[ℝ] F :=
  ((InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv :
    StrongDual ℝ F →SL[starRingEnd ℝ] F)

private theorem rieszL_apply (ℓ : StrongDual ℝ F) :
    (rieszL ℓ : F) = (InnerProductSpace.toDual ℝ F).symm ℓ := rfl

/-- The Hessian `∇²f(x)` as an operator on `F`: the derivative of the gradient. -/
noncomputable def hessianOperator (f : F → ℝ) (x : F) : F →L[ℝ] F := fderiv ℝ (gradient f) x

/-- For `f` twice differentiable at `x`, the gradient has derivative
`v ↦ (∇²f(x)[v, ·])^♯`. -/
private theorem hasFDerivAt_gradient_riesz (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (rieszL.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact rieszL.hasFDerivAt.comp x hd.hasFDerivAt

/-- For `f` `C²` at `x`, the gradient is differentiable at `x` with derivative the Hessian
operator. -/
theorem hasFDerivAt_gradient_hessianOperator (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (hessianOperator f x) x :=
  (hasFDerivAt_gradient_riesz hf).differentiableAt.hasFDerivAt

/-- `⟪u, ∇²f(x) v⟫ = ∇²f(x)[u, v]` for `f` `C²` at `x`. -/
theorem inner_hessianOperator_apply (hf : ContDiffAt ℝ 2 f x) (u v : F) :
    ⟪u, hessianOperator f x v⟫ = iteratedFDeriv ℝ 2 f x ![u, v] := by
  rw [hessianOperator, (hasFDerivAt_gradient_riesz hf).fderiv,
    ContinuousLinearMap.comp_apply, rieszL_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) v u

/-- The Hessian operator of a `C²` function is symmetric. -/
theorem hessianOperator_isSymmetric (hf : ContDiffAt ℝ 2 f x) :
    (hessianOperator f x : F →ₗ[ℝ] F).IsSymmetric := by
  intro u v
  change ⟪hessianOperator f x u, v⟫ = ⟪u, hessianOperator f x v⟫
  rw [real_inner_comm, inner_hessianOperator_apply hf, inner_hessianOperator_apply hf,
    iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact hf.isSymmSndFDerivAt (by simp) _ _

/-- `λ_min[∇²f(x)]` is the leftmost eigenvalue of the Hessian operator ([cartis2022evaluation],
Section A.5). -/
theorem minCurvature_iteratedFDeriv_two_eq_leftmost [FiniteDimensional ℝ F]
    (hf : ContDiffAt ℝ 2 f x) :
    minCurvature (iteratedFDeriv ℝ 2 f x) =
      Subproblem.leftmost (hessianOperator_isSymmetric hf) :=
  minCurvature_eq_leftmost _ fun v w => (inner_hessianOperator_apply hf v w).symm

/-- The Hessian form of a function `C²` at `x` is symmetric. -/
theorem iteratedFDeriv_two_symm (hf : ContDiffAt ℝ 2 f x) (v w : F) :
    iteratedFDeriv ℝ 2 f x ![v, w] = iteratedFDeriv ℝ 2 f x ![w, v] := by
  rw [← inner_hessianOperator_apply hf, ← inner_hessianOperator_apply hf, real_inner_comm]
  exact (hessianOperator_isSymmetric hf w v)

/-- The Hessian operator is bounded by the Hessian form: `‖∇²f(x)‖_op ≤ ‖∇²f(x)‖`. -/
theorem norm_hessianOperator_le (hf : ContDiffAt ℝ 2 f x) :
    ‖hessianOperator f x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  set w := hessianOperator f x v
  have h : ‖w‖ ^ 2 ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖v‖ * ‖w‖ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪w, hessianOperator f x v⟫ ≤ _
    rw [inner_hessianOperator_apply hf]
    have := (iteratedFDeriv ℝ 2 f x).le_opNorm ![w, v]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    refine (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ this).trans_eq ?_)
    ring
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **Eigenvectors of the leftmost eigenvalue** ([cartis2022evaluation], (3.2.3)): in finite
dimension, for `f` `C²` at `x` with `λ_min[∇²f(x)] < 0` there is a unit `u` with
`∇²f(x) u = λ_min u` and `⟪u, ∇f(x)⟫ ≤ 0`. -/
theorem exists_eigenvector_hessianOperator [FiniteDimensional ℝ F] (hf : ContDiffAt ℝ 2 f x)
    (hlam : minCurvature (iteratedFDeriv ℝ 2 f x) < 0) :
    ∃ u, ‖u‖ = 1 ∧ hessianOperator f x u = minCurvature (iteratedFDeriv ℝ 2 f x) • u ∧
      ⟪u, gradient f x⟫ ≤ 0 := by
  rcases subsingleton_or_nontrivial F with hE | hE
  · rw [minCurvature_of_subsingleton] at hlam
    exact absurd hlam (lt_irrefl _)
  obtain ⟨u, hu, -, hev, hgu⟩ := exists_eigenvector_minCurvature (A := iteratedFDeriv ℝ 2 f x)
    (iteratedFDeriv_two_symm hf) (gradient f x)
  refine ⟨u, hu, ext_inner_left ℝ fun w => ?_, hgu⟩
  rw [inner_hessianOperator_apply hf, iteratedFDeriv_two_symm hf, hev, inner_smul_right,
    real_inner_comm]

end Inner

section InnerMonomial

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cauchy–Schwarz for the decrement measure**: the measure of the linear decrement
`d ↦ ⟪v, d⟫` over the feasible displacements of length at most `δ` is at most `δ ‖v‖`. -/
theorem decrementMeasure_inner_le {v : F} {δ : ℝ} {S : Set F}
    (hne : (closedBall 0 δ ∩ S).Nonempty) : decrementMeasure (fun d => ⟪v, d⟫) δ S ≤ δ * ‖v‖ :=
  decrementMeasure_le hne fun d hd => (real_inner_le_norm v d).trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg v))

/-- The measure of the decrement `d ↦ a ⟪e, d⟫^m` (`a ≥ 0`, `‖e‖ = 1`) over the ball of radius
`δ ≥ 0` is `a δ^m` (attained at `d = δ e`). -/
theorem decrementMeasure_mul_inner_pow {e : F} (he : ‖e‖ = 1) {a δ : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    decrementMeasure (fun d => a * ⟪e, d⟫ ^ m) δ univ = a * δ ^ m := by
  have hle : ∀ d ∈ closedBall (0 : F) δ ∩ univ, a * ⟪e, d⟫ ^ m ≤ a * δ ^ m := fun d hd => by
    have h1 : |⟪e, d⟫| ≤ δ := (abs_real_inner_le_norm e d).trans (by
      rw [he, one_mul]; simpa using hd.1)
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) ha
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 m
  refine le_antisymm (decrementMeasure_le ⟨0, mem_closedBall_self hδ, mem_univ _⟩ hle) ?_
  have hmem : δ • e ∈ closedBall (0 : F) δ ∩ univ :=
    ⟨by rw [mem_closedBall_zero_iff, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hδ],
      mem_univ _⟩
  have := le_decrementMeasure (Δ := fun d => a * ⟪e, d⟫ ^ m) ⟨a * δ ^ m, forall_mem_image.2 hle⟩
    hmem
  simpa only [inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one] using this

end InnerMonomial

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : EuclideanSpace ℝ ι → ℝ}
  {x : EuclideanSpace ℝ ι}

/-- The Hessian matrix `[∇²f(x)]ᵢⱼ = ∇²f(x)[eᵢ, eⱼ]` (`= ∂²f(x)/∂xᵢ∂xⱼ`) of a function on
`EuclideanSpace ℝ ι`, in the standard basis `eᵢ`. -/
noncomputable def hessianMatrix (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

theorem hessianMatrix_apply (i j : ι) :
    hessianMatrix f x i j =
      iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := rfl

/-- For `f` `C²` at `x`, the Hessian matrix represents the Hessian operator. -/
theorem toEuclideanLin_hessianMatrix (hf : ContDiffAt ℝ 2 f x) :
    Matrix.toEuclideanLin (hessianMatrix f x) =
      (hessianOperator f x : EuclideanSpace ℝ ι →ₗ[ℝ] _) := by
  have e : hessianMatrix f x = LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis
      (hessianOperator f x : EuclideanSpace ℝ ι →ₗ[ℝ] _) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h := EuclideanSpace.inner_single_left i (1 : ℝ)
      (hessianOperator f x (EuclideanSpace.single j 1))
    simp only [map_one, one_mul] at h
    simp [hessianMatrix, ← h, inner_hessianOperator_apply hf]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, e, Matrix.toLin_toMatrix]

/-- For `f` `C²` at `x`, `∇²f(x)[v, w] = ⟪v, H w⟫` with the Hessian matrix `H`. -/
theorem iteratedFDeriv_two_eq_inner_hessianMatrix (hf : ContDiffAt ℝ 2 f x)
    (v w : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ 2 f x ![v, w] = ⟪v, Matrix.toEuclideanLin (hessianMatrix f x) w⟫ := by
  rw [toEuclideanLin_hessianMatrix hf, ContinuousLinearMap.coe_coe,
    inner_hessianOperator_apply hf]

/-- The Hessian matrix of a function `C²` at `x` is symmetric. -/
theorem hessianMatrix_isHermitian (hf : ContDiffAt ℝ 2 f x) : (hessianMatrix f x).IsHermitian :=
  Matrix.isSymmetric_toEuclideanLin_iff.mp
    (toEuclideanLin_hessianMatrix hf ▸ hessianOperator_isSymmetric hf)

/-- `λ_min[∇²f(x)]` is the least eigenvalue of the Hessian matrix ([cartis2022evaluation],
(1.1.5) and Section A.5); both sides are `0` when `ι` is empty. -/
theorem minCurvature_iteratedFDeriv_two_eq_iInf_eigenvalues (hf : ContDiffAt ℝ 2 f x) :
    minCurvature (iteratedFDeriv ℝ 2 f x) = ⨅ i, (hessianMatrix_isHermitian hf).eigenvalues i :=
  minCurvature_eq_iInf_isHermitian_eigenvalues _ (iteratedFDeriv_two_eq_inner_hessianMatrix hf)

end Matrix

end Optimization
