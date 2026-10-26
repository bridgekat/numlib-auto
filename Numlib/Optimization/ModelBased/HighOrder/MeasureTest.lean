import Numlib.Optimization.Optimality.Approximate

/-!
# Approximate evaluation of criticality measures and the termination test

High-order methods ([cartis2022evaluation], §12.1.6, Step 1 of Algorithms 12.2.1 and 12.2.2,
Step 1 of Algorithm 14.1.1 and of the Chapter 13 methods) never compute the measure
`φ = decrementMeasure Δ δ S` (a global optimization problem). They compute a displacement
`d ∈ B_δ ∩ S` with `ς φ ≤ Δ d` for a fixed `ς ∈ (0, 1]` (an *approximate optimality
displacement*, (12.1.32)) and compare `Δ d` with `ς ε_j δ_j^j / j!`. Passing the comparison at all
orders `j ≤ q` certifies the `(ε, δ)`-approximate optimality (12.1.25) / (14.1.9); failing it at
some order certifies a large measure there.

Everything is stated for an arbitrary decrement `Δ : E → ℝ`, so that exact Taylor data
(`Δ = D.taylorDecrement j`), inexact data (Chapter 13), model data at a trial step and the
composite decrements of Chapter 14 share one interface.

## Main definitions

* `Optimization.IsApproxMeasureStep Δ δ S ς d`: `d ∈ B_δ ∩ S` and `ς φ ≤ Δ d`;
* `Optimization.MeasureTestPasses Δ q ς ε δ d`: `Δ_j(d_j) ≤ ς ε_j δ_j^j / j!` for `1 ≤ j ≤ q`.

## Main results

* `Optimization.exists_isApproxMeasureStep`: existence in finite dimension (with refinements);
* `Optimization.isEpsDeltaApprox_of_measureTestPasses`: passing the test certifies the bounds on
  the measures, `Optimization.MeasureTestPasses.isEpsDeltaApprox` for Taylor data;
* `Optimization.exists_lt_of_not_measureTestPasses`: failing the test gives a
  (least) order with a large decrement.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E]

section ApproxStep

variable {Δ : E → ℝ} {δ ς : ℝ} {S : Set E} {d : E}

/-- An *approximate optimality displacement* ([cartis2022evaluation], (12.1.32); the `d_{k,j}` of
(12.2.1), (12.2.26), (13.1.13), (13.1.52), (14.1.10)): a feasible displacement `d ∈ B_δ ∩ S` whose
decrease is at least the fraction `ς` of the measure `decrementMeasure Δ δ S`. -/
def IsApproxMeasureStep (Δ : E → ℝ) (δ : ℝ) (S : Set E) (ς : ℝ) (d : E) : Prop :=
  d ∈ closedBall 0 δ ∩ S ∧ ς * decrementMeasure Δ δ S ≤ Δ d

/-- Unfolding lemma for `IsApproxMeasureStep`. -/
theorem isApproxMeasureStep_iff :
    IsApproxMeasureStep Δ δ S ς d ↔ d ∈ closedBall 0 δ ∩ S ∧ ς * decrementMeasure Δ δ S ≤ Δ d :=
  Iff.rfl

/-- An approximate optimality displacement has length at most `δ`. -/
theorem IsApproxMeasureStep.norm_le (h : IsApproxMeasureStep Δ δ S ς d) : ‖d‖ ≤ δ :=
  mem_closedBall_zero_iff.1 h.1.1

/-- An approximate optimality displacement is feasible. -/
theorem IsApproxMeasureStep.mem (h : IsApproxMeasureStep Δ δ S ς d) : d ∈ S := h.1.2

/-- The decrease along an approximate optimality displacement is at most the measure. -/
theorem IsApproxMeasureStep.le_decrementMeasure (h : IsApproxMeasureStep Δ δ S ς d)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) : Δ d ≤ decrementMeasure Δ δ S :=
  Optimization.le_decrementMeasure hbdd h.1

/-- Without compactness: an approximate optimality displacement exists for `ς < 1` as soon as the
decreases are bounded above, `0` is feasible and `Δ 0 = 0` (an approximate supremum, or `d = 0`
when the measure vanishes). -/
theorem exists_isApproxMeasureStep_of_lt_one (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S)))
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hΔ0 : Δ 0 = 0) (hς : ς < 1) :
    ∃ d, IsApproxMeasureStep Δ δ S ς d := by
  have h0m : (0 : E) ∈ closedBall 0 δ ∩ S := ⟨mem_closedBall_self hδ, h0⟩
  have hM := decrementMeasure_nonneg hbdd h0 hδ hΔ0
  rcases hM.eq_or_lt with hM0 | hMpos
  · exact ⟨0, h0m, by rw [← hM0, mul_zero, hΔ0]⟩
  · obtain ⟨_, ⟨d, hd, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (Set.Nonempty.image Δ ⟨0, h0m⟩)
      (show ς * decrementMeasure Δ δ S < sSup (Δ '' (closedBall 0 δ ∩ S)) by
        rw [← decrementMeasure_def]; nlinarith)
    exact ⟨d, hd, hlt.le⟩

variable [NormedSpace ℝ E]

/-- **Existence of approximate optimality displacements** ([cartis2022evaluation], §12.1.6). In
finite dimension, with `S` closed, `0 ∈ S`, `δ ≥ 0`, `ς ≤ 1` and `Δ` continuous on the feasible
ball with `Δ 0 = 0`, an exact maximizer is such a displacement. -/
theorem exists_isApproxMeasureStep [FiniteDimensional ℝ E] (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) (hς : ς ≤ 1) :
    ∃ d, IsApproxMeasureStep Δ δ S ς d := by
  obtain ⟨d, hd, hdM⟩ := exists_decrementMeasure_eq hS h0 hδ hΔ
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  have hM := decrementMeasure_nonneg (hK.bddAbove_image hΔ) h0 hδ hΔ0
  exact ⟨d, hd, by rw [hdM]; exact mul_le_of_le_one_left hM hς⟩

/-- Refinement of `exists_isApproxMeasureStep` for feasible sets star-shaped about `0`: for
`ς ∈ [0, 1]` there is a displacement with `Δ d = ς φ` exactly (used by the sharpness
examples). -/
theorem exists_isApproxMeasureStep_eq [FiniteDimensional ℝ E] (hS : IsClosed S)
    (h0 : (0 : E) ∈ S) (hstar : StarConvex ℝ 0 S) (hδ : 0 ≤ δ)
    (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d, IsApproxMeasureStep Δ δ S ς d ∧ Δ d = ς * decrementMeasure Δ δ S := by
  obtain ⟨d, hd, hdeq⟩ := exists_decrementMeasure_mul_eq hS h0 hstar hδ hΔ hΔ0 hς
  exact ⟨d, ⟨hd, hdeq.ge⟩, hdeq⟩

/-- Existence of approximate optimality displacements for Taylor decrements (finite dimension,
`S` closed, `0 ∈ S`). -/
theorem exists_isApproxMeasureStep_taylorDecrement [FiniteDimensional ℝ E]
    (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hς : ς ≤ 1) : ∃ d, IsApproxMeasureStep (D.taylorDecrement j) δ S ς d :=
  exists_isApproxMeasureStep hS h0 hδ (D.continuous_taylorDecrement j).continuousOn
    (D.taylorDecrement_zero_right j) hς

end ApproxStep

section Test

variable {Δ : ℕ → E → ℝ} {q : ℕ} {ς : ℝ} {ε δ : ℕ → ℝ} {d : ℕ → E} {S : Set E}

/-- The Step-1 termination test of the high-order methods ([cartis2022evaluation], Algorithms
12.2.1 and 12.2.2, Step 1; (14.1.10)): at every order `1 ≤ j ≤ q`, the decrease along the
displacement `d j` is at most `ς ε_j δ_j^j / j!`. Here `Δ j` is the order-`j` decrement, e.g.
`fun j => D.taylorDecrement j`. (The Chapter 13 tests use `ς / 2` in place of `ς`.) -/
def MeasureTestPasses (Δ : ℕ → E → ℝ) (q : ℕ) (ς : ℝ) (ε δ : ℕ → ℝ) (d : ℕ → E) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, Δ j (d j) ≤ ς * ε j * δ j ^ j / j !

omit [NormedAddCommGroup E] in
/-- Unfolding lemma for `MeasureTestPasses`. -/
theorem measureTestPasses_iff :
    MeasureTestPasses Δ q ς ε δ d ↔ ∀ j ∈ Finset.Icc 1 q, Δ j (d j) ≤ ς * ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- **Certification** ([cartis2022evaluation], §12.1.6, the inequalities after (12.1.32)). If
`0 < ς`, every `d j` is an approximate optimality displacement for `Δ j` and the test passes, then
`decrementMeasure (Δ j) (δ j) S ≤ ε_j δ_j^j / j!` for `1 ≤ j ≤ q`: divide
`ς φ_j ≤ Δ_j(d_j) ≤ ς ε_j δ_j^j / j!` by `ς`. -/
theorem isEpsDeltaApprox_of_measureTestPasses (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep (Δ j) (δ j) S ς (d j))
    (htest : MeasureTestPasses Δ q ς ε δ d) :
    ∀ j ∈ Finset.Icc 1 q, decrementMeasure (Δ j) (δ j) S ≤ ε j * δ j ^ j / j ! := by
  intro j hj
  have h := (hd j hj).2.trans (htest j hj)
  rw [mul_assoc, mul_div_assoc] at h
  exact le_of_mul_le_mul_left h hς

variable [NormedSpace ℝ E]

/-- Certification for Taylor data: passing the test with approximate optimality displacements
certifies `IsEpsDeltaApprox D S q ε δ` ((12.1.25)). -/
theorem MeasureTestPasses.isEpsDeltaApprox {D : FormalMultilinearSeries ℝ E ℝ} (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep (D.taylorDecrement j) (δ j) S ς (d j))
    (htest : MeasureTestPasses (fun j => D.taylorDecrement j) q ς ε δ d) :
    IsEpsDeltaApprox D S q ε δ :=
  isEpsDeltaApprox_of_measureTestPasses (Δ := fun j => D.taylorDecrement j) hς hd htest

end Test

section Failure

variable {Δ : ℕ → E → ℝ} {q : ℕ} {ς : ℝ} {ε δ : ℕ → ℝ} {d : ℕ → E} {S : Set E}

omit [NormedAddCommGroup E] in
/-- **Failure of the test** ([cartis2022evaluation], Algorithm 12.2.1 Step 1.2). If the test fails,
there is a *least* order `j ∈ [1, q]` at which `ς ε_j δ_j^j / j! < Δ_j(d_j)`; all lower orders
pass. (This least order is the book's `j_k`.) -/
theorem exists_lt_of_not_measureTestPasses
    (h : ¬ MeasureTestPasses Δ q ς ε δ d) :
    ∃ j ∈ Finset.Icc 1 q, ς * ε j * δ j ^ j / j ! < Δ j (d j) ∧
      ∀ i ∈ Finset.Icc 1 q, i < j → Δ i (d i) ≤ ς * ε i * δ i ^ i / i ! := by
  classical
  have hex : ∃ j, j ∈ Finset.Icc 1 q ∧ ς * ε j * δ j ^ j / j ! < Δ j (d j) := by
    simpa [MeasureTestPasses, not_le, and_assoc] using h
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun i hi hlt => ?_⟩
  by_contra hc
  exact Nat.find_min hex hlt ⟨hi, not_le.1 hc⟩

/-- A large decrease at a feasible displacement is a large measure: if
`ς ε_j δ_j^j / j! < Δ_j(d_j)` and `d_j ∈ B_{δ_j} ∩ S` (decreases bounded above) then
`ς ε_j δ_j^j / j! < decrementMeasure (Δ j) (δ j) S`. -/
theorem lt_decrementMeasure_of_lt {j : ℕ} (hbdd : BddAbove (Δ j '' (closedBall 0 (δ j) ∩ S)))
    (hd : d j ∈ closedBall 0 (δ j) ∩ S) (hlt : ς * ε j * δ j ^ j / j ! < Δ j (d j)) :
    ς * ε j * δ j ^ j / j ! < decrementMeasure (Δ j) (δ j) S :=
  hlt.trans_le (le_decrementMeasure hbdd hd)

/-- Failure of the test with feasible displacements: some order `j ∈ [1, q]` has a large measure,
`ς ε_j δ_j^j / j! < decrementMeasure (Δ j) (δ j) S`. -/
theorem exists_lt_decrementMeasure_of_not_measureTestPasses
    (h : ¬ MeasureTestPasses Δ q ς ε δ d)
    (hbdd : ∀ j ∈ Finset.Icc 1 q, BddAbove (Δ j '' (closedBall 0 (δ j) ∩ S)))
    (hd : ∀ j ∈ Finset.Icc 1 q, d j ∈ closedBall 0 (δ j) ∩ S) :
    ∃ j ∈ Finset.Icc 1 q, ς * ε j * δ j ^ j / j ! < decrementMeasure (Δ j) (δ j) S := by
  obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses h
  exact ⟨j, hj, lt_decrementMeasure_of_lt (hbdd j hj) (hd j hj) hlt⟩

end Failure

end Optimization
