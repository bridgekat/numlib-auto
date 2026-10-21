import Numlib.Optimization.InexactRegularization
import Numlib.Optimization.InexactTaylorModelBounds
import Numlib.Optimization.TaylorCriticalityFirstOrder
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Short first-order inner regularization returns

Explicit two-transition executions return a prescribed short step after its first-order
model test. A global model minimizer satisfies the decrease, retained comparison and
first-order test automatically. The initialization fraction can be chosen afresh at each
call. Exact derivative coefficients agree with the actual Taylor model up to the independent
scalar constant.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.HigherOrderApproximateRegularization
open TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scaling an attained first-order maximizer gives an exact fractional witness. -/
theorem exists_firstOrder_fractionWitness [ProperSpace E] (m : E → ℝ) (s : E)
    {fraction : ℝ} (hf : 0 ≤ fraction) (hf1 : fraction ≤ 1) :
    ∃ d : E, GapWitness m 1 s 1 fraction d ∧
      taylorDecrement m 1 s d = fraction * ‖fderiv ℝ m s‖ := by
  obtain ⟨v, hv, heq⟩ := exists_eq_gapOn (isCompact_closedBall (0 : E) 1)
    ⟨0, by simp⟩ (continuous_taylorDecrement m 1 s).continuousOn
  have hnorm : ‖v‖ ≤ 1 := by simpa using hv
  have hgap := gapOn_taylorDecrement_one m s (by norm_num : (0 : ℝ) ≤ 1)
  simp only [one_mul] at hgap
  have hdec : taylorDecrement m 1 s (fraction • v) =
      fraction * ‖fderiv ℝ m s‖ := by
    calc
      _ = fraction * taylorDecrement m 1 s v := by
        simp only [taylorDecrement_one, map_smul, smul_eq_mul]
        ring
      _ = _ := by rw [heq, hgap]
  refine ⟨fraction • v, ⟨?_, ?_⟩, hdec⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
    exact (mul_le_mul_of_nonneg_left hnorm hf).trans (by simpa using hf1)
  · rw [hgap, hdec]

private def firstOrderReturnExecution (P : Parameters) (hq : P.q = 1)
    (m : E → ℝ) (z s : E) (μ : ℝ) (hmin : ∀ t, m z ≤ m t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (m 0 - m z) ≤ m 0 - m s) (d : E)
    (hw : GapWitness m 1 s 1 P.fraction d)
    (htest : taylorDecrement m 1 s d ≤ P.fraction * P.theta * P.epsilon 1) :
    InnerExecution P m z 2 where
  state k := if k = 0 then ⟨μ, fun _ => 1, 0, .minimize⟩
    else if k = 1 then ⟨μ, fun _ => 1, s, .inspect 1⟩
    else ⟨μ, fun _ => 1, s, .returned⟩
  is_minimizer := hmin
  initial := by exact ⟨hμ, hμ1, rfl, rfl⟩
  transition k hk := by
    have hshort : ¬1 ≤ ‖s‖ := not_le_of_gt hs
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · simpa only [ite_true, zero_add, Nat.one_ne_zero, ite_false, hshort] using
        InnerTransition.minimize (P := P) (m := m) (minimizer := z)
          (⟨μ, fun _ => 1, 0, .minimize⟩ : InnerState E) rfl s hfrac
    · have ht : taylorDecrement m 1 s d ≤
          P.fraction * P.theta * P.epsilon 1 * (1 : ℝ) ^ 1 / (1 ! : ℝ) := by
        simpa only [pow_one, mul_one, Nat.factorial_one, Nat.cast_one, div_one] using htest
      simpa only [Nat.one_ne_zero, ite_false, ite_true, show 1 + 1 = 2 from rfl,
        show ¬(2 : ℕ) = 0 from by decide, show ¬(2 : ℕ) = 1 from by decide, hq] using
        InnerTransition.pass (P := P) (m := m) (minimizer := z)
          (⟨μ, fun _ => 1, s, .inspect 1⟩ : InnerState E) 1 rfl
          (by omega) (by omega) d hw ht

/-- A short step meeting the model decrease and derivative tests has the literal
minimize, inspect-order-one, returned execution with unit radii. -/
def shortFirstOrderExecution [ProperSpace E] (P : Parameters) (hq : P.q = 1)
    (m : E → ℝ) (z s : E) (μ : ℝ) (hmin : ∀ t, m z ≤ m t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (m 0 - m z) ≤ m 0 - m s)
    (hgrad : ‖fderiv ℝ m s‖ ≤ P.theta * P.epsilon 1) :
    InnerExecution P m z 2 :=
  let hw := exists_firstOrder_fractionWitness m s P.fraction_pos.le P.fraction_le_one
  firstOrderReturnExecution P hq m z s μ hmin hμ hμ1 hs hfrac (Classical.choose hw)
    (Classical.choose_spec hw).1 (by
      rw [(Classical.choose_spec hw).2]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgrad P.fraction_pos.le)

/-- The explicit execution's final state records the requested fraction, step and unit radii. -/
@[simp] theorem shortFirstOrderExecution_final [ProperSpace E]
    (P : Parameters) (hq : P.q = 1) (m : E → ℝ) (z s : E) (μ : ℝ)
    (hmin : ∀ t, m z ≤ m t) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (m 0 - m z) ≤ m 0 - m s)
    (hgrad : ‖fderiv ℝ m s‖ ≤ P.theta * P.epsilon 1) :
    (shortFirstOrderExecution P hq m z s μ hmin hμ hμ1 hs hfrac hgrad).state 2 =
      ⟨μ, fun _ => 1, s, .returned⟩ := rfl

/-- A global minimizer meets the minimizing-fraction and first-order derivative tests for
any legal initialization fraction. -/
def shortGlobalMinExecution (P : Parameters) (hq : P.q = 1)
    (m : E → ℝ) (z : E) (μ : ℝ) (hmin : ∀ t, m z ≤ m t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) : InnerExecution P m z 2 := by
  have hl : IsLocalMin m z := Filter.Eventually.of_forall hmin
  have hd := hl.fderiv_eq_zero
  refine firstOrderReturnExecution P hq m z z μ hmin hμ hμ1 hz
    (mul_le_of_le_one_left (sub_nonneg.mpr (hmin 0)) hμ1) 0 ⟨by simp, ?_⟩ ?_
  · simp [gapOn_taylorDecrement_one m z (by norm_num : (0 : ℝ) ≤ 1), hd]
  · simpa using mul_nonneg (mul_nonneg P.fraction_pos.le P.theta_pos.le)
      (P.epsilon_pos 1 le_rfl (by omega)).le

/-- A short global minimizer returns after exactly the minimization and first-order pass. -/
@[simp] theorem shortGlobalMinExecution_final
    (P : Parameters) (hq : P.q = 1) (m : E → ℝ) (z : E) (μ : ℝ)
    (hmin : ∀ t, m z ≤ m t) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    (shortGlobalMinExecution P hq m z μ hmin hμ hμ1 hz).state 2 =
      ⟨μ, fun _ => 1, z, .returned⟩ := rfl

/-- A global minimizer on the weak long-step branch returns directly from minimization. -/
def longGlobalMinExecution (P : Parameters) (m : E → ℝ) (z : E) (μ : ℝ)
    (hmin : ∀ t, m z ≤ m t) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : 1 ≤ ‖z‖) :
    InnerExecution P m z 1 where
  state k := if k = 0 then ⟨μ, fun _ => 1, 0, .minimize⟩
    else ⟨μ, fun _ => 1, z, .returned⟩
  is_minimizer := hmin
  initial := by exact ⟨hμ, hμ1, rfl, rfl⟩
  transition k hk := by
    have hk0 : k = 0 := by omega
    subst k
    simpa only [ite_true, zero_add, Nat.one_ne_zero, ite_false, hz] using
      InnerTransition.minimize (P := P) (m := m) (minimizer := z)
        (⟨μ, fun _ => 1, 0, .minimize⟩ : InnerState E) rfl z
        (mul_le_of_le_one_left (sub_nonneg.mpr (hmin 0)) hμ1)

/-- The long-step execution's final state contains the same minimizer and initialization
fraction. -/
@[simp] theorem longGlobalMinExecution_final (P : Parameters) (m : E → ℝ) (z : E) (μ : ℝ)
    (hmin : ∀ t, m z ≤ m t) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : 1 ≤ ‖z‖) :
    (longGlobalMinExecution P m z μ hmin hμ hμ1 hz).state 1 =
      ⟨μ, fun _ => 1, z, .returned⟩ := rfl

end Optimization.HigherOrderApproximateRegularization

namespace Optimization.InexactTaylorModels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact positive-order coefficients give the actual regularized Taylor model, with the
independently supplied scalar constant added in place of the objective value. -/
theorem regularizedPolynomial_iteratedFDeriv (f : E → ℝ) (x : E)
    (c : ℝ) (p : ℕ) (σ : ℝ) (s : E) :
    regularizedPolynomial c (fun i => iteratedFDeriv ℝ i f x) p σ s =
      HigherOrderApproximateRegularization.model f p x σ s + c - f x := by
  have hp := polynomial_iteratedFDeriv f x p s
  unfold polynomial at hp
  unfold regularizedPolynomial polynomial HigherOrderApproximateRegularization.model
    HigherOrderRegularization.model
  rw [← hp]
  ring

/-- Adding an independent scalar constant preserves the global model minimizers. -/
theorem regularizedPolynomial_iteratedFDeriv_minimizer_iff (f : E → ℝ) (x : E)
    (c : ℝ) (p : ℕ) (σ : ℝ) (z : E) :
    (∀ t, regularizedPolynomial c (fun i => iteratedFDeriv ℝ i f x) p σ z ≤
      regularizedPolynomial c (fun i => iteratedFDeriv ℝ i f x) p σ t) ↔
    ∀ t, HigherOrderApproximateRegularization.model f p x σ z ≤
      HigherOrderApproximateRegularization.model f p x σ t := by
  simp only [regularizedPolynomial_iteratedFDeriv, sub_le_sub_iff_right,
    add_le_add_iff_right]

end Optimization.InexactTaylorModels

namespace Optimization.InexactRegularization
open InexactTaylorModels HigherOrderApproximateRegularization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A prescribed short step with the analytic model inequalities gives an actual returned
inner result, including the comparison with the selected Step 1 direction. -/
def shortFirstOrderInnerResult [ProperSpace E] (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ z) ≤
      regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ s)
    (hgrad : ‖fderiv ℝ (regularizedPolynomial c A P.p σ) s‖ ≤ P.theta * P.epsilon 1)
    (hretained : regularizedPolynomial c A P.p σ s ≤ regularizedPolynomial c A P.p σ d) :
    InnerResult P c A σ δ d where
  minimizer := z
  length := 2
  execution := shortFirstOrderExecution P.toParameters hq _ z s μ hmin hμ hμ1 hs hfrac hgrad
  returned := rfl
  retained := hretained

/-- The returned result uses the prescribed candidate step. -/
@[simp] theorem shortFirstOrderInnerResult_step [ProperSpace E] (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ z) ≤
      regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ s)
    (hgrad : ‖fderiv ℝ (regularizedPolynomial c A P.p σ) s‖ ≤ P.theta * P.epsilon 1)
    (hretained : regularizedPolynomial c A P.p σ s ≤ regularizedPolynomial c A P.p σ d) :
    (shortFirstOrderInnerResult P hq c A σ δ d z s μ hmin hμ hμ1 hs hfrac hgrad hretained).step =
      s := rfl

/-- Every radius in this strictly short returned result is the actual initialized unit radius. -/
@[simp] theorem shortFirstOrderInnerResult_radii [ProperSpace E] (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ z) ≤
      regularizedPolynomial c A P.p σ 0 - regularizedPolynomial c A P.p σ s)
    (hgrad : ‖fderiv ℝ (regularizedPolynomial c A P.p σ) s‖ ≤ P.theta * P.epsilon 1)
    (hretained : regularizedPolynomial c A P.p σ s ≤ regularizedPolynomial c A P.p σ d) :
    (shortFirstOrderInnerResult P hq c A σ δ d z s μ hmin hμ hμ1 hs hfrac hgrad hretained).radii =
      fun _ => 1 := by
  exact ite_eq_right (not_le_of_gt hs)

/-- A short global minimizer retains every inspected direction and gives the literal
length-two returned inner result for every legal initialization fraction. -/
def shortGlobalMinInnerResult (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) : InnerResult P c A σ δ d where
  minimizer := z
  length := 2
  execution := shortGlobalMinExecution P.toParameters hq _ z μ hmin hμ hμ1 hz
  returned := rfl
  retained := hmin d

/-- The exact global-minimum result returns that same minimizer. -/
@[simp] theorem shortGlobalMinInnerResult_step (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    (shortGlobalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1 hz).step = z := rfl

/-- Strictly short global-minimum returns have unit radii at every order. -/
@[simp] theorem shortGlobalMinInnerResult_radii (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    (shortGlobalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1 hz).radii = fun _ => 1 := by
  exact ite_eq_right (not_le_of_gt hz)

/-- A weakly long global minimizer returns in one transition and retains every comparison
step. The outer result inherits the radii supplied by the completed inspection. -/
def longGlobalMinInnerResult (P : Parameters) (c : ℝ) (A : Coefficients E)
    (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : 1 ≤ ‖z‖) : InnerResult P c A σ δ d where
  minimizer := z
  length := 1
  execution := longGlobalMinExecution P.toParameters _ z μ hmin hμ hμ1 hz
  returned := rfl
  retained := hmin d

/-- The actual selected long step is the prescribed global minimizer. -/
@[simp] theorem longGlobalMinInnerResult_step (P : Parameters) (c : ℝ) (A : Coefficients E)
    (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : 1 ≤ ‖z‖) :
    (longGlobalMinInnerResult P c A σ δ d z μ hmin hμ hμ1 hz).step = z := rfl

/-- The weak long-step branch inherits the actual completed inspection's radii. -/
@[simp] theorem longGlobalMinInnerResult_radii (P : Parameters) (c : ℝ) (A : Coefficients E)
    (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : 1 ≤ ‖z‖) :
    (longGlobalMinInnerResult P c A σ δ d z μ hmin hμ hμ1 hz).radii = δ := by
  exact ite_eq_left hz

/-- A first-order inner call returns any prescribed global minimizer in at most two
transitions, following the actual weak long-step branch or the short first-order pass. -/
def globalMinInnerResult (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) : InnerResult P c A σ δ d :=
  if hz : 1 ≤ ‖z‖ then longGlobalMinInnerResult P c A σ δ d z μ hmin hμ hμ1 hz
  else shortGlobalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1 (lt_of_not_ge hz)

/-- The general global-minimum return selects the given minimizer in either branch. -/
@[simp] theorem globalMinInnerResult_step (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (globalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1).step = z := by
  unfold globalMinInnerResult
  split <;> rfl

/-- The returned radius vector follows the genuine weak long-step boundary. -/
@[simp] theorem globalMinInnerResult_radii (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (globalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1).radii =
      if 1 ≤ ‖z‖ then δ else fun _ => 1 := by
  unfold globalMinInnerResult
  split_ifs with hz
  · exact longGlobalMinInnerResult_radii P c A σ δ d z μ hmin hμ hμ1 hz
  · exact shortGlobalMinInnerResult_radii P hq c A σ δ d z μ hmin hμ hμ1 (lt_of_not_ge hz)

/-- Exactly one transition is taken for a weakly long minimum and two for a strictly short one. -/
@[simp] theorem globalMinInnerResult_length (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, regularizedPolynomial c A P.p σ z ≤ regularizedPolynomial c A P.p σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (globalMinInnerResult P hq c A σ δ d z μ hmin hμ hμ1).length =
      if 1 ≤ ‖z‖ then 1 else 2 := by
  unfold globalMinInnerResult
  split_ifs <;> rfl

/-- Every positively regularized supplied model has an actual first-order inner return in
at most two transitions, selecting a global minimum and retaining every inspected direction. -/
theorem exists_globalMinInnerResult {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients F) {σ : ℝ} (hσ : 0 < σ) (δ : ℕ → ℝ) (d : F)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ R : InnerResult P c A σ δ d,
      (∀ t, regularizedPolynomial c A P.p σ R.step ≤ regularizedPolynomial c A P.p σ t) ∧
      R.length ≤ 2 ∧ R.radii = if 1 ≤ ‖R.step‖ then δ else fun _ => 1 := by
  obtain ⟨z, hz⟩ := exists_regularizedPolynomial_minimizer c A P.p hσ
  refine ⟨globalMinInnerResult P hq c A σ δ d z μ hz hμ hμ1, ?_, ?_, ?_⟩
  · simpa only [globalMinInnerResult_step] using hz
  · rw [globalMinInnerResult_length]
    split_ifs <;> omega
  · rw [globalMinInnerResult_radii, globalMinInnerResult_step]

/-- An actual Taylor-model global minimizer supplies an exact-coefficient inner return;
the supplied scalar constant may differ from the true objective value. -/
def exactShortGlobalMinInnerResult (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    InnerResult P c (fun i => iteratedFDeriv ℝ i f x) σ δ d :=
  shortGlobalMinInnerResult P hq c _ σ δ d z μ
    ((regularizedPolynomial_iteratedFDeriv_minimizer_iff f x c P.p σ z).mpr hmin)
    hμ hμ1 hz

/-- The exact-coefficient result returns the global minimizer of the actual Taylor model. -/
@[simp] theorem exactShortGlobalMinInnerResult_step (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    (exactShortGlobalMinInnerResult P hq f x c σ δ d z μ hmin hμ hμ1 hz).step = z := rfl

/-- The actual exact-coefficient short return retains unit radii. -/
@[simp] theorem exactShortGlobalMinInnerResult_radii (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hz : ‖z‖ < 1) :
    (exactShortGlobalMinInnerResult P hq f x c σ δ d z μ hmin hμ hμ1 hz).radii =
      fun _ => 1 := by
  exact ite_eq_right (not_le_of_gt hz)

/-- The fixed squared-gradient initialization rule is legal whenever the supplied exact
gradient is nonzero and has norm at most one. -/
theorem squaredGradientFraction_bounds (f : E → ℝ) (x : E)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) :
    0 < ‖fderiv ℝ f x‖ ^ 2 / 100 ∧ ‖fderiv ℝ f x‖ ^ 2 / 100 ≤ 1 := by
  have hp : 0 < ‖fderiv ℝ f x‖ := norm_pos_iff.mpr hg
  constructor
  · positivity
  · nlinarith [norm_nonneg (fderiv ℝ f x)]

/-- The fixed squared-gradient policy and an actual short Taylor-model minimizer produce
a complete inner return, with no common positive lower bound imposed on the fractions. -/
def squaredGradientGlobalMinInnerResult (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    InnerResult P c (fun i => iteratedFDeriv ℝ i f x) σ δ d :=
  exactShortGlobalMinInnerResult P hq f x c σ δ d z (‖fderiv ℝ f x‖ ^ 2 / 100) hmin
    (squaredGradientFraction_bounds f x hg hg1).1
    (squaredGradientFraction_bounds f x hg hg1).2 hz

/-- The squared-gradient policy is the actual inner execution's initial fraction. -/
@[simp] theorem squaredGradientGlobalMinInnerResult_initial (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    (squaredGradientGlobalMinInnerResult P hq f x c σ δ d z hmin hg hg1 hz).execution.state 0 =
      ⟨‖fderiv ℝ f x‖ ^ 2 / 100, fun _ => 1, 0, .minimize⟩ := rfl

/-- The policy's final state returns the actual minimizer with the same fraction and unit radii. -/
@[simp] theorem squaredGradientGlobalMinInnerResult_final (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    let R := squaredGradientGlobalMinInnerResult P hq f x c σ δ d z hmin hg hg1 hz
    R.execution.state R.length =
      ⟨‖fderiv ℝ f x‖ ^ 2 / 100, fun _ => 1, z, .returned⟩ := rfl

/-- The squared-gradient short return has exactly two transitions. -/
@[simp] theorem squaredGradientGlobalMinInnerResult_length (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    (squaredGradientGlobalMinInnerResult P hq f x c σ δ d z hmin hg hg1 hz).length = 2 := rfl

/-- The squared-gradient short return selects the actual global model minimizer. -/
@[simp] theorem squaredGradientGlobalMinInnerResult_step (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    (squaredGradientGlobalMinInnerResult P hq f x c σ δ d z hmin hg hg1 hz).step = z := rfl

/-- The actual returned radii of the squared-gradient policy are all one. -/
@[simp] theorem squaredGradientGlobalMinInnerResult_radii (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z : E)
    (hmin : ∀ t, HigherOrderApproximateRegularization.model f P.p x σ z ≤
      HigherOrderApproximateRegularization.model f P.p x σ t)
    (hg : fderiv ℝ f x ≠ 0) (hg1 : ‖fderiv ℝ f x‖ ≤ 1) (hz : ‖z‖ < 1) :
    (squaredGradientGlobalMinInnerResult P hq f x c σ δ d z hmin hg hg1 hz).radii =
      fun _ => 1 := by
  exact ite_eq_right (not_le_of_gt hz)

end Optimization.InexactRegularization
