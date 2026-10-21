import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpC
import Numlib.Optimization.CompositeModelDecrease

/-!
# Chapter 14, Section 1: small-radius composite model decrease

The smooth regularized component and each scalar component of the vector polynomial have
bounded omitted Taylor coefficients. Combining their actual value errors retains the
nonsmooth composition exactly and gives the factorial decrease in Lemma 14.1.2.
-/

noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter14.Section01
open Optimization CompositeTaylorModels CompositeRegularization RegularizedTaylorModel

/-- All source scalar derivative Lipschitz bounds, as a reusable derivative family. -/
theorem CompositeProblem.scalarFamily {n m p : ℕ} (C : CompositeProblem n m p) :
    HigherOrderDerivativeFamily C.f p (fun j => C.Lf j) := by
  refine ⟨C.f_contDiff, fun j _ _ => (C.Lf j).coe_nonneg, ?_⟩
  intro j hj hjp x y d
  have hl := (C.f_deriv_lipschitz j (Finset.mem_Icc.mpr ⟨hj, hjp⟩)).dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at hl
  exact ((iteratedFDeriv ℝ j C.f x - iteratedFDeriv ℝ j C.f y).le_opNorm
    (fun _ => d)).trans (by simpa using (mul_le_mul_of_nonneg_right hl
      (pow_nonneg (norm_nonneg d) j)))

/-- Each source scalar component carries the same vector derivative Lipschitz family. -/
theorem CompositeProblem.componentFamily {n m p : ℕ} (C : CompositeProblem n m p) (i : Fin m) :
    HigherOrderDerivativeFamily (fun y => C.c y i) p (fun j => C.Lc j) := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) i
  refine ⟨L.contDiff.comp C.c_contDiff, fun j _ _ => (C.Lc j).coe_nonneg, ?_⟩
  intro j hj hjp x y d
  have hl := (C.c_deriv_lipschitz j (Finset.mem_Icc.mpr ⟨hj, hjp⟩) i).dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at hl
  exact ((iteratedFDeriv ℝ j (fun y => C.c y i) x -
    iteratedFDeriv ℝ j (fun y => C.c y i) y).le_opNorm
    (fun _ => d)).trans (by simpa using (mul_le_mul_of_nonneg_right hl
      (pow_nonneg (norm_nonneg d) j)))

/-- The common scalar derivative constant appearing in the inner model estimates. -/
def CompositeProblem.scalarConstant {n m p : ℕ} (C : CompositeProblem n m p) : ℝ :=
  HigherOrderDerivativeFamily.maxConstant p (fun j => C.Lf j)

/-- The common component derivative constant appearing in the inner model estimates. -/
def CompositeProblem.componentConstant {n m p : ℕ} (C : CompositeProblem n m p) : ℝ :=
  HigherOrderDerivativeFamily.maxConstant p (fun j => C.Lc j)

/-- The common composite derivative constant for all requested Taylor orders. -/
def CompositeProblem.derivativeConstant {n m p : ℕ} (C : CompositeProblem n m p) : ℝ :=
  C.scalarConstant + Real.sqrt m * C.h.constant * C.componentConstant

/-- The source vector-model remainder specializes the common componentwise bound. -/
theorem CompositeProblem.vectorModel_error {n m p j : ℕ} (C : CompositeProblem n m p)
    (hp : 1 ≤ p) (hj : 1 ≤ j) (hjp : j ≤ p) (x s d : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ 1) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hd : ‖d‖ ≤ δ) :
    ‖vectorModel C.c p x (s + d) - taylorModel (vectorModel C.c p x) j s d‖ ≤
      2 * (3 * Real.sqrt m * C.componentConstant) * δ ^ (j + 1) / (j ! : ℝ) :=
  CompositeRegularization.vectorModel_error C.componentFamily
    (fun k _ _ => (C.Lc k).coe_nonneg) hp hj hjp x s d hs hδ hd C.c_contDiff.contDiffAt

/-- The source smooth-model remainder specializes the common derivative-family bound. -/
theorem CompositeProblem.smoothModel_error {n m p j : ℕ} (C : CompositeProblem n m p)
    (hp : 1 ≤ p) (hj : 1 ≤ j) (hjp : j ≤ p) (x s d : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ 1) {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hd : ‖d‖ ≤ δ) :
    |smoothModel C.f p x σ (s + d) - taylorModel (smoothModel C.f p x σ) j s d| ≤
      2 * (3 * C.scalarConstant + σ) * δ ^ (j + 1) / (j ! : ℝ) :=
  CompositeRegularization.smoothModel_error C.scalarFamily hp hj hjp x s d hs hσ hδ hd

/-- Lemma 14.1.2: the actual generalized model decrement at a sufficiently small radius
produces at least half its factorially normalized target as actual composite model decrease.
The nonsmooth composition is retained exactly. -/
theorem lemma_14_1_2 {n m p q j : ℕ} (C : CompositeProblem n m p)
    (hj : 1 ≤ j) (hjq : j ≤ q) (hqp : q ≤ p) (x s d : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ 1) {σ α δ : ℝ} (hσ : 0 < σ) (_hα : 0 < α)
    (hδ : 0 < δ) (hδmax : δ ≤ min 1 (α / (4 * (3 * C.derivativeConstant + σ))))
    (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤ modelDecrement C.f C.c C.h p j x σ s d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤
      compositeRegularizedModel C.f C.c C.h p x σ s -
        compositeRegularizedModel C.f C.c C.h p x σ (s + d) := by
  have hp := hj.trans (hjq.trans hqp)
  have hf : 0 ≤ C.scalarConstant := C.scalarFamily.maxConstant_nonneg
  have hc : 0 ≤ C.componentConstant := (C.Lc 1).coe_nonneg.trans
    (HigherOrderDerivativeFamily.le_maxConstant (fun k => (C.Lc k : ℝ)) le_rfl hp)
  have hL : 0 ≤ C.derivativeConstant := by
    dsimp [CompositeProblem.derivativeConstant]
    positivity
  have hden : 0 < 4 * (3 * C.derivativeConstant + σ) := by positivity
  have hsmall := (le_div_iff₀ hden).mp (le_min_iff.mp hδmax).2
  have he := half_decrease_of_errors C.h.lipschitz hδ.le
    (C.smoothModel_error hp hj (hjq.trans hqp) x s d hs hσ.le
      ⟨hδ.le, (le_min_iff.mp hδmax).1⟩ hd)
    (C.vectorModel_error hp hj (hjq.trans hqp) x s d hs
      ⟨hδ.le, (le_min_iff.mp hδmax).1⟩ hd)
    (by dsimp [CompositeProblem.derivativeConstant] at hsmall; nlinarith only [hsmall]) hdec
  have hobj : ∀ t, smoothModel C.f p x σ t + C.h (vectorModel C.c p x t) =
      compositeRegularizedModel C.f C.c C.h p x σ t := by
    intro t
    dsimp [smoothModel, vectorModel, compositeRegularizedModel,
      CompositeTaylorModels.regularizedModel, CompositeTaylorModels.model]
    ring
  simpa only [hobj] using he

end CartisGouldToint.Chapter14.Section01
