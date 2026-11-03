import Numlib.Optimization.ModelBased.SupportDescent
import Numlib.Optimization.Optimality.Clarke

/-!
# Steepest descent for a nonsmooth objective

[conn2000trust], Section 11.1. The steepest-descent calculation follows from the
Clarke support representation (3.1.4) and metric projection.
-/

open Filter Metric ConvexAnalysis Optimization
open scoped Topology RealInnerProductSpace

namespace ConnGouldToint.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The model-value agreement condition (11.1.1). -/
def modelValueMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p, m x p 0 = f x

/-- The model-directional derivative agreement condition (11.1.2). -/
def modelDerivativeMatches {P : Type*} (f : E → ℝ) (m : E → P → E → ℝ) : Prop :=
  ∀ x p d, d ≠ 0 → clarkeDerivative (m x p) 0 d = clarkeDerivative f x d

/-- The minimizing property in (11.1.3) of a steepest-descent direction. -/
def IsSteepestDirection (f : E → ℝ) (x d : E) : Prop :=
  ‖d‖ ≤ 1 ∧ IsMinOn (clarkeDerivative f x) (closedBall 0 1) d

/-- The least slope over the closed unit ball. -/
noncomputable def steepestSlope (f : E → ℝ) (x : E) : ℝ :=
  sInf (clarkeDerivative f x '' closedBall 0 1)

/-- The minimum-norm subgradient (11.1.4), as the projection of zero. -/
noncomputable def minimumNormSubgradient (f : E → ℝ) (x : E) : E :=
  bestApprox (clarkeSubgradient f x) 0

/-- The selected steepest-descent direction (11.1.6). It is zero when the minimum-norm
subgradient is zero. -/
noncomputable def steepestDirection (f : E → ℝ) (x : E) : E :=
  negativeUnit (minimumNormSubgradient f x)

variable [CompleteSpace E]

/-- Lemma 11.1.1 and formula (11.1.6), using the support representation (3.1.4).
The selected direction attains the least slope, equal to minus the norm of the
minimum-norm Clarke subgradient. -/
theorem lemma_11_1_1 {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    (minimumNormSubgradient f x ∈ clarkeSubgradient f x ∧
      ∀ z ∈ clarkeSubgradient f x, ‖minimumNormSubgradient f x‖ ≤ ‖z‖) ∧
    IsSteepestDirection f x (steepestDirection f x) ∧
    clarkeDerivative f x (steepestDirection f x) = steepestSlope f x ∧
    steepestSlope f x = -‖minimumNormSubgradient f x‖ := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  let K := clarkeSubgradient f x
  have hcl := isClosed_clarkeSubgradient f x
  have hco := convex_clarkeSubgradient f x
  have hg := isBestApprox_bestApprox_of_isClosed h.nonempty hcl hco (0 : E)
  have hval := supportFn_negativeUnit_bestApprox h.nonempty hcl hco
  change supportFn (innerₗ E) K (steepestDirection f x) =
    ((-‖minimumNormSubgradient f x‖ : ℝ) : EReal) at hval
  rw [h] at hval
  have hval' := EReal.coe_eq_coe_iff.mp hval
  have hlo (d : E) (hd : ‖d‖ ≤ 1) :
      -‖minimumNormSubgradient f x‖ ≤ clarkeDerivative f x d := by
    have hh := neg_norm_bestApprox_le_supportFn h.nonempty hcl hco hd
    rw [h] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hdir : ‖steepestDirection f x‖ ≤ 1 := norm_negativeUnit_le_one _
  have hleast : IsLeast (clarkeDerivative f x '' closedBall 0 1)
      (-‖minimumNormSubgradient f x‖) := by
    refine ⟨⟨steepestDirection f x, mem_closedBall_zero_iff.mpr hdir, hval'⟩, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hlo d (mem_closedBall_zero_iff.mp hd)
  have hslope : steepestSlope f x = -‖minimumNormSubgradient f x‖ := hleast.csInf_eq
  refine ⟨⟨hg.1, fun z hz ↦ ?_⟩, ⟨hdir, isMinOn_iff.mpr fun d hd ↦ ?_⟩,
    hval'.trans hslope.symm, hslope⟩
  · simpa [minimumNormSubgradient] using hg.2 z hz
  · exact hval'.le.trans (hlo d (mem_closedBall_zero_iff.mp hd))

/-- The least slope vanishes exactly at Clarke stationary points. -/
theorem steepestSlope_eq_zero_iff {f : E → ℝ} {x : E} {U : Set E} {L : NNReal}
    (hU : U ∈ 𝓝 x) (hL : LipschitzOnWith L f U) :
    steepestSlope f x = 0 ↔ (0 : E) ∈ clarkeSubgradient f x := by
  have h := hasClarkeSupport_of_lipschitzOnWith hU hL
  rw [(lemma_11_1_1 hU hL).2.2.2, neg_eq_zero, norm_eq_zero]
  constructor
  · intro hg
    exact hg ▸ (lemma_11_1_1 hU hL).1.1
  · intro hzero
    apply (bestApprox_eq_iff h.nonempty (isClosed_clarkeSubgradient f x)
      (convex_clarkeSubgradient f x)).mpr
    exact ⟨hzero, by simp⟩

/-- The minimizing property of a model step for (11.1.7). -/
def IsModelMinimizer (m : E → ℝ) (Δ : ℝ) (s : E) : Prop :=
  ‖s‖ ≤ Δ ∧ IsMinOn m (closedBall 0 Δ) s

omit [CompleteSpace E] in
/-- The minimizing property of a Cauchy step length along the selected direction
in (11.1.8). -/
def IsCauchyLength (m : E → ℝ) (d : E) (Δ t : ℝ) : Prop :=
  t ∈ Set.Ioc 0 Δ ∧ IsMinOn (fun u : ℝ ↦ m (u • d)) (Set.Ioc 0 Δ) t

/-- The Cauchy step in (11.1.8) given its length and direction. -/
def cauchyStep (t : ℝ) (d : E) : E := t • d

/-- Sufficient model decrease relative to a Cauchy step, as in (11.1.9). -/
def HasSufficientCauchyDecrease (m : E → ℝ) (s sC : E) (Δ κ : ℝ) : Prop :=
  ‖s‖ ≤ Δ ∧ κ * (m 0 - m sC) ≤ m 0 - m s

end ConnGouldToint.Chapter11
