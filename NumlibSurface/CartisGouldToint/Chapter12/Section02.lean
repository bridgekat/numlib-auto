import Numlib.Optimization.HigherOrderDerivativeFamily
import Numlib.Optimization.HigherOrderApproximateRegularization
import Numlib.Analysis.Normed.Multilinear.Diagonal
import NumlibSurface.CartisGouldToint.Chapter12.Section01

/-!
# Chapter 12, Section 2: high-order Taylor model algorithms

The common interfaces keep all positive derivative Lipschitz bounds, actual factorial Taylor
models, and source scaling conventions. The algorithm modules specialize these data to legal
trust-region and regularization runs with their own stopping and oracle laws.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter12.Section02
open Optimization
variable {n : ℕ}

/-- Assumptions f.D1qL and f.D1pL: all active positive-order derivatives are Lipschitz.
The source normalizes every Lipschitz constant to be at least one. -/
structure LipschitzDerivativeFamily (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (L : ℕ → ℝ) : Prop extends HigherOrderDerivativeFamily f p L where
  one_le : ∀ j, 1 ≤ j → j ≤ p → 1 ≤ L j

/-- The common source Lipschitz constant (12.2.6) and (12.2.25). -/
abbrev derivativeFamilyConstant (p : ℕ) (L : ℕ → ℝ) : ℝ :=
  HigherOrderDerivativeFamily.maxConstant p L

/-- The source family specializes to the canonical single-order Taylor remainder interface. -/
theorem LipschitzDerivativeFamily.at_order {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℕ} {L : ℕ → ℝ} (hf : LipschitzDerivativeFamily f p L)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    HigherOrderRegularization.DiagonalLipschitz f j (L j) :=
  hf.toHigherOrderDerivativeFamily.at_order hj hjp

/-- Every active order also uses the common source maximum constant. -/
theorem LipschitzDerivativeFamily.at_order_max {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℕ} {L : ℕ → ℝ} (hf : LipschitzDerivativeFamily f p L)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    HigherOrderRegularization.DiagonalLipschitz f j (derivativeFamilyConstant p L) :=
  hf.toHigherOrderDerivativeFamily.at_order_max hj hjp

/-- The source common constant is at least one whenever an order is requested. -/
theorem LipschitzDerivativeFamily.one_le_constant {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℕ} {L : ℕ → ℝ} (hf : LipschitzDerivativeFamily f p L) (hp : 1 ≤ p) :
    1 ≤ derivativeFamilyConstant p L :=
  (hf.one_le 1 le_rfl hp).trans (HigherOrderDerivativeFamily.le_maxConstant L le_rfl hp)

/-- The family's repeated-direction interface is precisely the source diagonal tensor norm. -/
theorem LipschitzDerivativeFamily.diagonalNorm_bound {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℕ} {L : ℕ → ℝ} (hf : LipschitzDerivativeFamily f p L)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) (x y : EuclideanSpace ℝ (Fin n)) :
    (iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y).diagonalNorm ≤ L j * ‖x - y‖ := by
  apply (ContinuousMultilinearMap.diagonalNorm_le_iff _ (by omega)
    (mul_nonneg (hf.nonneg j hj hjp) (norm_nonneg _))).mpr
  intro d
  exact hf.bound j hj hjp x y d

/-- The source's diagonal tensor-norm assumptions construct the family without replacing
any of its derivative orders by an assumed bound. -/
theorem LipschitzDerivativeFamily.of_diagonalNorm {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : ℕ} {L : ℕ → ℝ} (hf : ContDiff ℝ p f)
    (hL : ∀ j, 1 ≤ j → j ≤ p → 1 ≤ L j)
    (hb : ∀ j, 1 ≤ j → j ≤ p → ∀ x y : EuclideanSpace ℝ (Fin n),
      (iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y).diagonalNorm ≤ L j * ‖x - y‖) :
    LipschitzDerivativeFamily f p L := by
  refine ⟨⟨hf, fun j hj hjp => (by norm_num : (0 : ℝ) ≤ 1).trans (hL j hj hjp), ?_⟩, hL⟩
  intro j hj hjp x y d
  exact (ContinuousMultilinearMap.diagonalNorm_le_iff _ (by omega)
    (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (hL j hj hjp))
      (norm_nonneg _))).mp (hb j hj hjp x y) d

/-- The actual regularized Taylor model (12.2.23); its value at zero is the objective value. -/
abbrev regularizedTaylorModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  RegularizedTaylorModel.regularizedModel f p x sigma ((p + 1)! : ℝ) (p + 1)

/-- The source real-power model agrees with the canonical natural-power model. -/
theorem regularizedTaylorModel_eq_model (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    regularizedTaylorModel f p x sigma =
      HigherOrderApproximateRegularization.model f p x sigma := by
  funext s
  simp only [HigherOrderApproximateRegularization.model, HigherOrderRegularization.model,
    regularizedTaylorModel, RegularizedTaylorModel.regularizedModel]
  rw [show (p : ℝ) + 1 = ((p + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]

/-- The actual model includes the objective value as its constant coefficient. -/
@[simp] theorem regularizedTaylorModel_zero (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    regularizedTaylorModel f p x sigma 0 = f x := by
  rw [regularizedTaylorModel_eq_model]
  exact HigherOrderApproximateRegularization.model_zero f p x sigma

/-- The source model decrement subtracts the actual radial regularizer from the Taylor
prediction; no shift of the objective's constant term is needed. -/
theorem regularizedTaylorModel_decrement (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x s : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    regularizedTaylorModel f p x sigma 0 - regularizedTaylorModel f p x sigma s =
      Section01.taylorDecrement f p x s - sigma / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  rw [regularizedTaylorModel_zero, regularizedTaylorModel_eq_model]
  unfold HigherOrderApproximateRegularization.model HigherOrderRegularization.model
  rw [Section01.taylorDecrement, TaylorCriticality.taylorDecrement_eq]
  ring

/-- Positive regularization makes the actual source model exceed every prescribed level
outside a sufficiently large ball. -/
theorem regularizedTaylorModel_eventually_ge (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x : EuclideanSpace ℝ (Fin n)) {sigma : ℝ} (hs : 0 < sigma) (b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s, R ≤ ‖s‖ → b ≤ regularizedTaylorModel f p x sigma s := by
  simpa only [regularizedTaylorModel_eq_model] using
    HigherOrderApproximateRegularization.model_eventually_ge f p x hs b

/-- All sublevels of the positively regularized source model are bounded. -/
theorem regularizedTaylorModel_sublevel_isBounded (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x : EuclideanSpace ℝ (Fin n)) {sigma : ℝ} (hs : 0 < sigma) (b : ℝ) :
    Bornology.IsBounded {s | regularizedTaylorModel f p x sigma s ≤ b} := by
  simpa only [regularizedTaylorModel_eq_model] using
    HigherOrderApproximateRegularization.model_sublevel_isBounded f p x hs b

/-- A positive source regularization parameter gives an attained global model minimum. -/
theorem exists_regularizedTaylorModel_minimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (x : EuclideanSpace ℝ (Fin n)) {sigma : ℝ} (hs : 0 < sigma) :
    ∃ s, ∀ t, regularizedTaylorModel f p x sigma s ≤ regularizedTaylorModel f p x sigma t := by
  simpa only [regularizedTaylorModel_eq_model] using
    HigherOrderApproximateRegularization.exists_model_minimizer f p x hs

/-- The actual selected Taylor decrement rescaled as in (12.2.8). -/
def trqScaledGap (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ) (delta : ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (j ! : ℝ) * Section01.taylorDecrement f j x d / delta ^ j

/-- The two ARqp exponent regimes (12.2.61)–(12.2.66). -/
def arqpComplexityExponent (p q j : ℕ) : ℝ :=
  if q ≤ 2 then ((p + 1 : ℕ) : ℝ) / ((p - j + 1 : ℕ) : ℝ)
  else (j : ℝ) * ((p + 1 : ℕ) : ℝ) / (p : ℝ)

end CartisGouldToint.Chapter12.Section02
