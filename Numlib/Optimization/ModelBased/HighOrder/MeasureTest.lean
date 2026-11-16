/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Optimality.Approximate

/-!
# Approximate evaluation of criticality measures and the termination test

Let $\Delta : E \to \mathbb{R}$ be a decrement, let $\delta \ge 0$ be a radius and let
$S \subseteq E$ be a set of feasible displacements. The criticality measure is $\phi = \sup
\{\Delta(d) : \|d\| \le \delta,\ d \in S\}$, which is `Optimization.decrementMeasure Δ δ S`.
Computing $\phi$ is a global optimization problem, so the high-order methods of
[cartis2022evaluation] (§12.1.6, Step 1 of Algorithms 12.2.1, 12.2.2 and 14.1.1, and the methods of
Chapter 13) never compute it. Instead they compute an **approximate optimality displacement**
(12.1.32): a feasible $d$ with $\|d\| \le \delta$ and $\varsigma \phi \le \Delta(d)$, for a fixed
$\varsigma \in (0, 1]$. At each order $j \le q$ they compare $\Delta_j(d_j)$ with
$\varsigma \varepsilon_j \delta_j^j / j!$. If the comparison passes at all orders, the point is
$(\varepsilon, \delta)$-approximately optimal in the sense of (12.1.25) and (14.1.9). If it fails at
some order, the measure at that order is large.

All results hold for an arbitrary decrement $\Delta$. Exact Taylor data ($\Delta = \Delta T_j$, the
decrement `D.taylorDecrement j`), the inexact data of Chapter 13, model data at a trial step, and
the composite decrements of Chapter 14 therefore use the same definitions.

## Main definitions

* `Optimization.IsApproxMeasureStep`: $d$ is feasible, $\|d\| \le \delta$, and
  $\varsigma \phi \le \Delta(d)$.
* `Optimization.MeasureTestPasses`: $\Delta_j(d_j) \le \varsigma \varepsilon_j \delta_j^j / j!$ for
  $1 \le j \le q$.

## Main results

* `Optimization.exists_isApproxMeasureStep`: in finite dimension, approximate optimality
  displacements exist.
* `Optimization.IsApproxMeasureStep.mono_set`: an approximate optimality displacement over a set of
  displacements is one over every smaller set that contains it.
* `Optimization.isEpsDeltaApprox_of_measureTestPasses`: passing the test bounds the measures by
  $\varepsilon_j \delta_j^j / j!$.
* `Optimization.MeasureTestPasses.isEpsDeltaApprox`: for Taylor data, passing the test gives
  $(\varepsilon, \delta)$-approximate optimality.
* `Optimization.exists_lt_of_not_measureTestPasses`: if the test fails, there is a least order at
  which it fails.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Approximate optimality displacements -/

section ApproxStep

variable {Δ : E → ℝ} {δ ς : ℝ} {S : Set E} {d : E}

/-- An **approximate optimality displacement** of (12.1.32) of [cartis2022evaluation]. Let
$\Delta : E \to \mathbb{R}$, $\delta, \varsigma \in \mathbb{R}$ and $S \subseteq E$. A
displacement $d \in E$ is an approximate optimality displacement if
$$\|d\| \le \delta, \qquad d \in S, \qquad \varsigma \phi \le \Delta(d),$$
where $\phi = \sup \{\Delta(e) : \|e\| \le \delta,\ e \in S\}$ is the criticality measure.

These displacements are the $d_{k,j}$ of (12.2.1), (12.2.26), (13.1.13), (13.1.52) and (14.1.10)
of the source. The measure is `Optimization.decrementMeasure Δ δ S`, a supremum `sSup` in
$\mathbb{R}$, which has the value $0$ when the set of decreases is empty or not bounded above. -/
def IsApproxMeasureStep (Δ : E → ℝ) (δ : ℝ) (S : Set E) (ς : ℝ) (d : E) : Prop :=
  d ∈ closedBall 0 δ ∩ S ∧ ς * decrementMeasure Δ δ S ≤ Δ d

/-- The displacement $d$ is an approximate optimality displacement if and only if
$\|d\| \le \delta$, $d \in S$ and $\varsigma \phi \le \Delta(d)$. -/
theorem isApproxMeasureStep_iff :
    IsApproxMeasureStep Δ δ S ς d ↔ d ∈ closedBall 0 δ ∩ S ∧ ς * decrementMeasure Δ δ S ≤ Δ d :=
  Iff.rfl

/-- An approximate optimality displacement $d$ for the radius $\delta$ satisfies $\|d\| \le \delta$.
-/
theorem IsApproxMeasureStep.norm_le (h : IsApproxMeasureStep Δ δ S ς d) : ‖d‖ ≤ δ :=
  mem_closedBall_zero_iff.1 h.1.1

/-- An approximate optimality displacement for the set $S$ lies in $S$. -/
theorem IsApproxMeasureStep.mem (h : IsApproxMeasureStep Δ δ S ς d) : d ∈ S := h.1.2

/-- Let $S \subseteq S' \subseteq E$, let $\varsigma \ge 0$, and assume that the decreases
$\Delta(e)$ over $\|e\| \le \delta$, $e \in S'$ are bounded above. If $d$ is an approximate
optimality displacement for $\Delta$, $\delta$, $S'$ and $\varsigma$, and $d \in S$, then $d$ is
an approximate optimality displacement for $\Delta$, $\delta$, $S$ and $\varsigma$.

The measure over $S$ is at most the measure over $S'$, because the decreases are bounded above
on the larger set. -/
theorem IsApproxMeasureStep.mono_set {S' : Set E} (h : IsApproxMeasureStep Δ δ S' ς d)
    (hς : 0 ≤ ς) (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S'))) (hSS' : S ⊆ S') (hd : d ∈ S) :
    IsApproxMeasureStep Δ δ S ς d :=
  ⟨⟨h.1.1, hd⟩, (mul_le_mul_of_nonneg_left (decrementMeasure_mono_set ⟨d, h.1.1, hd⟩ hbdd hSS')
    hς).trans h.2⟩

/-- If the decreases $\Delta(e)$ over $\|e\| \le \delta$, $e \in S$ are bounded above, then an
approximate optimality displacement $d$ satisfies $\Delta(d) \le \phi$. -/
theorem IsApproxMeasureStep.le_decrementMeasure (h : IsApproxMeasureStep Δ δ S ς d)
    (hbdd : BddAbove (Δ '' (closedBall 0 δ ∩ S))) : Δ d ≤ decrementMeasure Δ δ S :=
  Optimization.le_decrementMeasure hbdd h.1

/-- Existence without compactness. Assume that the decreases $\Delta(e)$ over $\|e\| \le \delta$,
$e \in S$ are bounded above, that $0 \in S$, $\delta \ge 0$, $\Delta(0) = 0$ and
$\varsigma < 1$. Then an approximate optimality displacement exists.

The displacement is a near-maximizer of $\Delta$, or $d = 0$ when $\phi = 0$. -/
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

/-! ### Existence in finite dimension -/

variable [NormedSpace ℝ E]

/-- **Existence of approximate optimality displacements**, as in §12.1.6 of [cartis2022evaluation].
Let $E$ be a finite-dimensional real normed space, let $S \subseteq E$ be closed with $0 \in S$,
let $\delta \ge 0$ and $\varsigma \le 1$, and let $\Delta$ be continuous on
$\{e \in S : \|e\| \le \delta\}$ with $\Delta(0) = 0$. Then there is an approximate optimality
displacement for $\Delta$, $\delta$, $S$ and $\varsigma$.

The displacement is an exact maximizer of $\Delta$ on the compact set
$\{e \in S : \|e\| \le \delta\}$. -/
theorem exists_isApproxMeasureStep [FiniteDimensional ℝ E] (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) (hς : ς ≤ 1) :
    ∃ d, IsApproxMeasureStep Δ δ S ς d := by
  obtain ⟨d, hd, hdM⟩ := exists_decrementMeasure_eq hS h0 hδ hΔ
  have := FiniteDimensional.proper_real E
  have hK : IsCompact (closedBall (0 : E) δ ∩ S) := (isCompact_closedBall 0 δ).inter_right hS
  have hM := decrementMeasure_nonneg (hK.bddAbove_image hΔ) h0 hδ hΔ0
  exact ⟨d, hd, by rw [hdM]; exact mul_le_of_le_one_left hM hς⟩

/-- A refinement of `Optimization.exists_isApproxMeasureStep` for a set $S$ that is star-shaped
about $0$. Let $E$ be finite-dimensional, let $S$ be closed and star-shaped about $0$ with
$0 \in S$, let $\delta \ge 0$ and $\varsigma \in [0, 1]$, and let $\Delta$ be continuous on
$\{e \in S : \|e\| \le \delta\}$ with $\Delta(0) = 0$. Then there is an approximate optimality
displacement $d$ with $\Delta(d) = \varsigma \phi$ exactly.

The sharpness examples use this form. -/
theorem exists_isApproxMeasureStep_eq [FiniteDimensional ℝ E] (hS : IsClosed S)
    (h0 : (0 : E) ∈ S) (hstar : StarConvex ℝ 0 S) (hδ : 0 ≤ δ)
    (hΔ : ContinuousOn Δ (closedBall 0 δ ∩ S)) (hΔ0 : Δ 0 = 0) (hς : ς ∈ Icc (0 : ℝ) 1) :
    ∃ d, IsApproxMeasureStep Δ δ S ς d ∧ Δ d = ς * decrementMeasure Δ δ S := by
  obtain ⟨d, hd, hdeq⟩ := exists_decrementMeasure_mul_eq hS h0 hstar hδ hΔ hΔ0 hς
  exact ⟨d, ⟨hd, hdeq.ge⟩, hdeq⟩

/-- Let $E$ be finite-dimensional, let $D$ be a formal multilinear series on $E$, let
$j \in \mathbb{N}$, let $S$ be closed with $0 \in S$, and let $\delta \ge 0$ and
$\varsigma \le 1$. Then there is an approximate optimality displacement for the Taylor decrement
$\Delta T_j$ of $D$, the radius $\delta$, the set $S$ and the fraction $\varsigma$. -/
theorem exists_isApproxMeasureStep_taylorDecrement [FiniteDimensional ℝ E]
    (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (hS : IsClosed S) (h0 : (0 : E) ∈ S)
    (hδ : 0 ≤ δ) (hς : ς ≤ 1) : ∃ d, IsApproxMeasureStep (D.taylorDecrement j) δ S ς d :=
  exists_isApproxMeasureStep hS h0 hδ (D.continuous_taylorDecrement j).continuousOn
    (D.taylorDecrement_zero_right j) hς

end ApproxStep

/-! ### The termination test -/

section Test

variable {Δ : ℕ → E → ℝ} {q : ℕ} {ς : ℝ} {ε δ : ℕ → ℝ} {d : ℕ → E} {S : Set E}

/-- The **termination test** of Step 1 of the high-order methods of [cartis2022evaluation]
(Algorithms 12.2.1 and 12.2.2, Step 1, and (14.1.10)). Let $\Delta_j : E \to \mathbb{R}$ be the
decrement of order $j$, let $d_j \in E$ be displacements, and let $\varsigma \in \mathbb{R}$ and
$\varepsilon_j, \delta_j \in \mathbb{R}$. The test **passes** if
$$\Delta_j(d_j) \le \frac{\varsigma \varepsilon_j \delta_j^j}{j!} \qquad \text{for } 1 \le j \le
  q.$$

For exact Taylor data, $\Delta_j$ is `fun j => D.taylorDecrement j`. The tests of Chapter 13 use
$\varsigma / 2$ in place of $\varsigma$. -/
def MeasureTestPasses (Δ : ℕ → E → ℝ) (q : ℕ) (ς : ℝ) (ε δ : ℕ → ℝ) (d : ℕ → E) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, Δ j (d j) ≤ ς * ε j * δ j ^ j / j !

omit [NormedAddCommGroup E] in
/-- The test passes if and only if $\Delta_j(d_j) \le \varsigma \varepsilon_j \delta_j^j / j!$ for
$1 \le j \le q$. -/
theorem measureTestPasses_iff :
    MeasureTestPasses Δ q ς ε δ d ↔ ∀ j ∈ Finset.Icc 1 q, Δ j (d j) ≤ ς * ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- **Certification** by the test, as in the inequalities after (12.1.32) of [cartis2022evaluation].
Let $\varsigma > 0$. Assume that for $1 \le j \le q$ the displacement $d_j$ is an approximate
optimality displacement for $\Delta_j$, the radius $\delta_j$, the set $S$ and the fraction
$\varsigma$, and that the termination test passes. Then for $1 \le j \le q$ the measure
$\phi_j = \sup \{\Delta_j(e) : \|e\| \le \delta_j,\ e \in S\}$ satisfies
$$\phi_j \le \frac{\varepsilon_j \delta_j^j}{j!}.$$

The proof divides $\varsigma \phi_j \le \Delta_j(d_j) \le \varsigma \varepsilon_j \delta_j^j /
j!$ by $\varsigma$. -/
theorem isEpsDeltaApprox_of_measureTestPasses (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep (Δ j) (δ j) S ς (d j))
    (htest : MeasureTestPasses Δ q ς ε δ d) :
    ∀ j ∈ Finset.Icc 1 q, decrementMeasure (Δ j) (δ j) S ≤ ε j * δ j ^ j / j ! := by
  intro j hj
  have h := (hd j hj).2.trans (htest j hj)
  rw [mul_assoc, mul_div_assoc] at h
  exact le_of_mul_le_mul_left h hς

variable [NormedSpace ℝ E]

/-- Certification for Taylor data. Let $D$ be a formal multilinear series and let $\varsigma > 0$.
Assume that for $1 \le j \le q$ the displacement $d_j$ is an approximate optimality displacement
for the Taylor decrement $\Delta T_j$ of $D$, the radius $\delta_j$, the set $S$ and the
fraction $\varsigma$, and that the termination test passes for these decrements. Then $D$ is
$(\varepsilon, \delta)$-approximately optimal on $S$ in the sense of (12.1.25) of
[cartis2022evaluation], that is, `Optimization.IsEpsDeltaApprox D S q ε δ` holds. -/
theorem MeasureTestPasses.isEpsDeltaApprox {D : FormalMultilinearSeries ℝ E ℝ} (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q, IsApproxMeasureStep (D.taylorDecrement j) (δ j) S ς (d j))
    (htest : MeasureTestPasses (fun j => D.taylorDecrement j) q ς ε δ d) :
    IsEpsDeltaApprox D S q ε δ :=
  isEpsDeltaApprox_of_measureTestPasses (Δ := fun j => D.taylorDecrement j) hς hd htest

end Test

/-! ### Failure of the test -/

section Failure

variable {Δ : ℕ → E → ℝ} {q : ℕ} {ς : ℝ} {ε δ : ℕ → ℝ} {d : ℕ → E} {S : Set E}

omit [NormedAddCommGroup E] in
/-- **Failure of the test**, as in Step 1.2 of Algorithm 12.2.1 of [cartis2022evaluation]. If the
termination test does not pass, then there is a least order $j$ with $1 \le j \le q$ at which it
fails:
$$\frac{\varsigma \varepsilon_j \delta_j^j}{j!} < \Delta_j(d_j), \qquad \Delta_i(d_i) \le
  \frac{\varsigma \varepsilon_i \delta_i^i}{i!} \quad \text{for } 1 \le i < j.$$

This least order is the $j_k$ of the source. -/
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

/-- A large decrease at a feasible displacement gives a large measure. Assume that the decreases
$\Delta_j(e)$ over $\|e\| \le \delta_j$, $e \in S$ are bounded above, that
$\|d_j\| \le \delta_j$ and $d_j \in S$, and that $\varsigma \varepsilon_j \delta_j^j / j! <
\Delta_j(d_j)$. Then $\varsigma \varepsilon_j \delta_j^j / j! < \phi_j$. -/
theorem lt_decrementMeasure_of_lt {j : ℕ} (hbdd : BddAbove (Δ j '' (closedBall 0 (δ j) ∩ S)))
    (hd : d j ∈ closedBall 0 (δ j) ∩ S) (hlt : ς * ε j * δ j ^ j / j ! < Δ j (d j)) :
    ς * ε j * δ j ^ j / j ! < decrementMeasure (Δ j) (δ j) S :=
  hlt.trans_le (le_decrementMeasure hbdd hd)

/-- Assume that the termination test does not pass, and that for $1 \le j \le q$ the decreases
$\Delta_j(e)$ over $\|e\| \le \delta_j$, $e \in S$ are bounded above, $\|d_j\| \le \delta_j$ and
$d_j \in S$. Then some order $j$ with $1 \le j \le q$ has a large measure: $\varsigma
\varepsilon_j \delta_j^j / j! < \phi_j$. -/
theorem exists_lt_decrementMeasure_of_not_measureTestPasses
    (h : ¬ MeasureTestPasses Δ q ς ε δ d)
    (hbdd : ∀ j ∈ Finset.Icc 1 q, BddAbove (Δ j '' (closedBall 0 (δ j) ∩ S)))
    (hd : ∀ j ∈ Finset.Icc 1 q, d j ∈ closedBall 0 (δ j) ∩ S) :
    ∃ j ∈ Finset.Icc 1 q, ς * ε j * δ j ^ j / j ! < decrementMeasure (Δ j) (δ j) S := by
  obtain ⟨j, hj, hlt, -⟩ := exists_lt_of_not_measureTestPasses h
  exact ⟨j, hj, lt_decrementMeasure_of_lt (hbdd j hj) (hd j hj) hlt⟩

end Failure

end Optimization
