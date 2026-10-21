import Numlib.Optimization.TrustRegionSecondOrder

/-!
# Shifted inexact Newton steps

A residual equation with relative and quadratic error bounds gives bounds on shifts and step
lengths. The algebraic step interface is independent of any objective or global run assumptions.
The objective-specific specialization uses the actual gradient and represented Hessian.
-/
noncomputable section
namespace Optimization.InexactNewton
open InnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A shifted Newton equation, with both relative-gradient and quadratic-step residual bounds. -/
structure IsStep (H : E →L[ℝ] E) (g s r : E) (lambda rg rs : ℝ) : Prop where
  equation : H s + lambda • s = -g + r
  relative : ‖r‖ ≤ rg * ‖g‖
  quadratic : ‖r‖ ≤ rs * ‖s‖ ^ 2
  shift_nonneg : 0 ≤ lambda

/-- Relative residual control bounds the right side of the Newton equation. -/
theorem IsStep.norm_equation_le {H : E →L[ℝ] E} {g s r : E} {lambda rg rs : ℝ}
    (h : IsStep H g s r lambda rg rs) :
    ‖H s + lambda • s‖ ≤ (1 + rg) * ‖g‖ := by
  rw [h.equation]
  calc
    ‖-g + r‖ ≤ ‖g‖ + ‖r‖ := by simpa using norm_add_le (-g) r
    _ ≤ (1 + rg) * ‖g‖ := by linarith [h.relative]

/-- Coercivity and a step-proportional shift imply a scalar quadratic inequality. -/
theorem IsStep.shift_quadratic_le {H : E →L[ℝ] E} {g s r : E}
    {lambda rg rs mu b : ℝ} (h : IsStep H g s r lambda rg rs)
    (hs : s ≠ 0) (hmu : ∀ u, mu * ‖u‖ ^ 2 ≤ inner ℝ (H u) u)
    (hpsd : 0 ≤ mu + lambda) (hb : 0 ≤ b) (hl : lambda ≤ b * ‖s‖) :
    lambda * (mu + lambda) ≤ b * (1 + rg) * ‖g‖ := by
  have hinner : (mu + lambda) * ‖s‖ ^ 2 ≤ inner ℝ (H s + lambda • s) s := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [hmu s]
  have hn := real_inner_le_norm (H s + lambda • s) s
  have hnorm : (mu + lambda) * ‖s‖ ≤ (1 + rg) * ‖g‖ := by
    have hn' := mul_le_mul_of_nonneg_right h.norm_equation_le (norm_nonneg s)
    have hp := norm_pos_iff.mpr hs
    nlinarith
  calc
    lambda * (mu + lambda) ≤ b * ‖s‖ * (mu + lambda) :=
      mul_le_mul_of_nonneg_right hl hpsd
    _ ≤ b * ((1 + rg) * ‖g‖) := by nlinarith [mul_le_mul_of_nonneg_left hnorm hb]
    _ = _ := by ring

/-- A scalar quadratic inequality yields the standard curvature/gradient shift estimate. -/
theorem shift_bound_of_quadratic {mu lambda a G : ℝ} (ha : 1 ≤ a) (hG : 0 ≤ G)
    (hquad : lambda * (mu + lambda) ≤ a * G) :
    mu + lambda ≤ 2 * Real.sqrt a * max |mu| (Real.sqrt G) := by
  let M := max |mu| (Real.sqrt G)
  have hM : 0 ≤ M := (abs_nonneg mu).trans (le_max_left _ _)
  have hm : |mu| ≤ M := le_max_left _ _
  have hg : Real.sqrt G ≤ M := le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have hsq := Real.sq_sqrt ha0
  have hsqG := Real.sq_sqrt hG
  have ha1 : 1 ≤ Real.sqrt a := (Real.one_le_sqrt).mpr ha
  have hma : M ≤ Real.sqrt a * M := by nlinarith
  have hGG : G ≤ M ^ 2 := by nlinarith [Real.sqrt_nonneg G]
  have hmu : mu ≤ Real.sqrt a * M := (le_abs_self mu).trans (hm.trans hma)
  have hq : lambda * (mu + lambda) ≤ (Real.sqrt a * M) ^ 2 := by
    calc
      _ ≤ a * G := hquad
      _ ≤ a * M ^ 2 := mul_le_mul_of_nonneg_left hGG ha0
      _ = _ := by nlinarith
  by_contra hc
  have hd : 2 * Real.sqrt a * M < mu + lambda := lt_of_not_ge hc
  have hp : 0 ≤ Real.sqrt a * M := mul_nonneg (Real.sqrt_nonneg _) hM
  nlinarith

/-- A relative residual bound controls the current gradient by the step. -/
theorem IsStep.gradient_le {H : E →L[ℝ] E} {g s r : E} {lambda rg rs B b : ℝ}
    (h : IsStep H g s r lambda rg rs) (hrg : rg < 1)
    (hH : ‖H‖ ≤ B) (hl : lambda ≤ b) :
    ‖g‖ ≤ ((B + b) / (1 - rg)) * ‖s‖ := by
  have heq : g = -(H s + lambda • s) + r := by rw [h.equation]; abel
  have hnorm : ‖g‖ ≤ (B + b) * ‖s‖ + rg * ‖g‖ := by
    calc
      ‖g‖ = ‖-(H s + lambda • s) + r‖ := congrArg norm heq
      _ ≤ ‖H s‖ + ‖lambda • s‖ + ‖r‖ := by
        grw [norm_add_le, norm_neg, norm_add_le]
      _ ≤ (B + b) * ‖s‖ + rg * ‖g‖ := by
        rw [norm_smul, Real.norm_of_nonneg h.shift_nonneg]
        have hHs := (H.le_opNorm s).trans
          (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
        have hls := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
        linarith [h.relative]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hrg)).mpr
  nlinarith

/-- A quadratic upper bound implies the sharp square-root step lower bound. -/
theorem sqrt_gradient_le_step {G C t : ℝ} (hC : 0 < C)
    (ht : 0 ≤ t) (h : G ≤ C * t ^ 2) :
    (Real.sqrt C)⁻¹ * Real.sqrt G ≤ t := by
  have hc := Real.sqrt_pos.mpr hC
  have hs : Real.sqrt G ≤ Real.sqrt C * t := by
    have hh := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul hC.le, Real.sqrt_sq ht] at hh
  calc
    _ ≤ (Real.sqrt C)⁻¹ * (Real.sqrt C * t) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le)
    _ = t := by field_simp

variable [CompleteSpace E]

/-- A globally Lipschitz gradient bounds the represented Hessian operator. -/
theorem norm_hessianOperator_le {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖TrustRegionSecondOrder.hessianOperator f x‖ ≤ L := by
  have hdual : ∀ u v, ‖fderiv ℝ f u - fderiv ℝ f v‖ ≤ L * ‖u - v‖ := by
    intro u v
    rw [← toDual_gradient, ← toDual_gradient, ← map_sub, (toDual ℝ E).norm_map]
    exact hg u v
  have hB : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ L :=
    norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall (fun u => hdual u x))
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro u
  change ‖(toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) x u)‖ ≤ L * ‖u‖
  rw [(toDual ℝ E).symm.norm_map]
  exact ((fderiv ℝ (fderiv ℝ f) x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg u))

/-- The genuine gradient Taylor remainder in the represented Hessian convention. -/
theorem gradient_remainder {f : E → ℝ} {L : ℝ}
    (hf : CubicRegularization.HessianLipschitz f L) (x s : E) :
    ‖gradient f (x + s) - (gradient f x + TrustRegionSecondOrder.hessianOperator f x s)‖ ≤
      L / 2 * ‖s‖ ^ 2 := by
  have ht := hf.derivative_remainder x s
  rw [RegularizedTaylorModel.fderiv_taylorModel_eq_taylorModel_fderiv
    (p := 1) (hf.smooth.contDiffAt), RegularizedTaylorModel.taylorModel_one] at ht
  convert ht using 1
  rw [← (toDual ℝ E).norm_map]
  congr 1
  ext u
  simp [TrustRegionSecondOrder.hessianOperator, toDual_apply_apply,
    continuousLinearMapOfBilin_apply]

/-- An actual inexact Newton step has a quadratic next-gradient estimate. -/
theorem IsStep.next_gradient_le {f : E → ℝ} {L lambda rg rs b : ℝ} {x s r : E}
    (h : IsStep (TrustRegionSecondOrder.hessianOperator f x) (gradient f x)
      s r lambda rg rs) (hf : CubicRegularization.HessianLipschitz f L)
    (hl : lambda ≤ b * ‖s‖) :
    ‖gradient f (x + s)‖ ≤ (L / 2 + rs + b) * ‖s‖ ^ 2 := by
  have heq : gradient f x + TrustRegionSecondOrder.hessianOperator f x s =
      r - lambda • s := by
    have hh := eq_sub_of_add_eq h.equation
    rw [hh]
    abel
  have hb := gradient_remainder hf x s
  have hn := norm_le_norm_sub_add (gradient f (x + s))
    (gradient f x + TrustRegionSecondOrder.hessianOperator f x s)
  rw [heq] at hn hb
  have hr := norm_sub_le r (lambda • s)
  rw [norm_smul, Real.norm_of_nonneg h.shift_nonneg] at hr
  have hl' := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
  nlinarith [h.quadratic]

/-- A second-order oracle response at a queried point. -/
structure Jet where
  point : E
  value : ℝ
  gradient : E
  hessian : E →L[ℝ] E

/-- The exact second-order oracle of a scalar objective. -/
def oracle (f : E → ℝ) (x : E) : Jet (E := E) :=
  ⟨x, f x, gradient f x, TrustRegionSecondOrder.hessianOperator f x⟩

/-- A deterministic accepted-step decision, including its shift and residual. -/
structure Decision where
  step : E
  residual : E
  shift : ℝ

/-- An internal oracle action: query an arbitrary point, or accept a shifted Newton decision. -/
inductive Action (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  | query (point : E)
  | accept (decision : Decision (E := E))

/-- A deterministic oracle policy, allowed to refine its model through arbitrarily many
internal queries. Halting is required on actual active executions separately. -/
abbrev Method (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ → List (Jet (E := E)) → Action E

/-- Embed a decision rule requiring no internal queries into the general oracle policy. -/
def Method.ofDecisions
    (A : ℝ → List (Jet (E := E)) → Decision (E := E)) : Method E :=
  fun epsilon history => .accept (A epsilon history)

/-- Run an oracle policy for the given fuel. Queries append the actual response in order;
an accepted state absorbs every subsequent fuel step. -/
def internalState (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) : ℕ → Option (Decision (E := E)) × List (Jet (E := E))
  | 0 => (none, history)
  | fuel + 1 =>
    let z := internalState A f epsilon history fuel
    match z.1 with
    | some _ => z
    | none => match A epsilon z.2 with
      | .query point => (none, z.2 ++ [oracle f point])
      | .accept decision => (some decision, z.2)

/-- Internal execution starts with the supplied transcript and no accepted decision. -/
@[simp] theorem internalState_zero (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) :
    internalState A f epsilon history 0 = (none, history) := rfl

/-- Once accepted, an internal execution preserves its decision and complete transcript. -/
theorem internalState_succ_of_accepted (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) (fuel : ℕ) (d : Decision (E := E))
    (hd : (internalState A f epsilon history fuel).1 = some d) :
    internalState A f epsilon history (fuel + 1) = internalState A f epsilon history fuel := by
  simp [internalState, hd]

/-- Actual-objective halting: some finite fuel reaches an accepted decision. The same policy
may diverge on arbitrary or inconsistent hypothetical oracle responses. -/
def Halts (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) : Prop :=
  ∃ fuel, (internalState A f epsilon history fuel).1 ≠ none

/-- A direct decision policy halts after one internal action. -/
theorem Method.ofDecisions_halts
    (A : ℝ → List (Jet (E := E)) → Decision (E := E)) (f : E → ℝ)
    (epsilon : ℝ) (history : List (Jet (E := E))) :
    Halts (Method.ofDecisions A) f epsilon history := by
  refine ⟨1, ?_⟩
  simp [internalState, Method.ofDecisions]

open Classical in
/-- Execute to the first accepted decision when the actual policy halts. On a divergent
execution this total interface returns a junk zero decision and the initial history; lawful
active runs explicitly require `Halts`, so the fallback cannot certify an accepted step. -/
def execute (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) : Decision (E := E) × List (Jet (E := E)) :=
  if h : Halts A f epsilon history then
    let z := internalState A f epsilon history (Nat.find h)
    (z.1.getD ⟨0, 0, 0⟩, z.2)
  else (⟨0, 0, 0⟩, history)

/-- A halting execution returns exactly the accepted decision and transcript of the first
fuel index reaching acceptance. No hypothetical oracle response is used. -/
theorem execute_of_halts (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) (h : Halts A f epsilon history) :
    internalState A f epsilon history (Nat.find h) =
      (some (execute A f epsilon history).1, (execute A f epsilon history).2) := by
  have hh := Nat.find_spec h
  unfold execute
  rw [dite_eq_left h]
  cases hz : internalState A f epsilon history (Nat.find h) with
  | mk d history' =>
    cases d with
    | none => simp [hz] at hh
    | some decision => rfl

/-- Divergent policies use the explicitly documented junk fallback. -/
theorem execute_fallback_of_not_halts (A : Method E) (f : E → ℝ) (epsilon : ℝ)
    (history : List (Jet (E := E))) (h : ¬Halts A f epsilon history) :
    execute A f epsilon history = (⟨0, 0, 0⟩, history) := by
  simp [execute, h]

/-- Recursive execution state: current accepted point and the complete oracle transcript.
Each iteration first queries its accepted point, then executes all internal queries and
accepts the final decision. Lawful active executions require actual-objective halting. -/
def state (A : Method E) (f : E → ℝ) (epsilon : ℝ) (x0 : E) :
    ℕ → E × List (Jet (E := E))
  | 0 => (x0, [])
  | k + 1 =>
    let z := state A f epsilon x0 k
    let history := z.2 ++ [oracle f z.1]
    let result := execute A f epsilon history
    (z.1 + result.1.step, result.2)

/-- The final decision after all internal queries at the current recursively generated point. -/
def decisionAt (A : Method E) (f : E → ℝ) (epsilon : ℝ) (x0 : E) (k : ℕ) :
    Decision (E := E) :=
  let z := state A f epsilon x0 k
  let history := z.2 ++ [oracle f z.1]
  (execute A f epsilon history).1

/-- Execution accepts the decision's full step. -/
@[simp] theorem state_succ_point (A : Method E) (f : E → ℝ) (epsilon : ℝ) (x0 : E)
    (k : ℕ) :
    (state A f epsilon x0 (k + 1)).1 =
      (state A f epsilon x0 k).1 + (decisionAt A f epsilon x0 k).step := rfl

end Optimization.InexactNewton
