import Numlib.Optimization.HigherOrderRegularizationBounds
import Numlib.Optimization.HigherOrderRegularizationRun
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Normed.Multilinear.Diagonal
import NumlibSurface.CartisGouldToint.Chapter01.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section04

/-!
# Chapter 4, Section 1: higher-order regularization models and value estimates

The model uses the actual Taylor polynomial with factorial normalization. Assumption f.DpL
uses the diagonal tensor norm of Appendix A.6. The value and parameter estimates need only
model decrease and actual acceptance/update laws, so they are stated for that trace interface;
the full finite ARp specification separately records actual derivative residuals, the source's
three stopping branches, and the first stopping index.
-/

noncomputable section
open scoped Nat
open CartisGouldToint.Chapter01.Section03
open CartisGouldToint.Chapter02.Section04
open Optimization.ParameterUpdates

namespace CartisGouldToint.Chapter04.Section01

variable {n : ℕ}

/-- Assumption f.DpL: actual continuous derivatives and the source's diagonal tensor norm. -/
structure higherOrderLipschitz (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (L : ℝ) : Prop where
  smooth : ContDiff ℝ p f
  constant_ge_one : 1 ≤ L
  bound : ∀ x y, (iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y).diagonalNorm ≤ L * ‖x - y‖

/-- The source assumption is the homogeneous diagonal control needed by the value remainder. -/
theorem higherOrderLipschitz.toDiagonalLipschitz
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {L : ℝ}
    (hf : higherOrderLipschitz f p L) (hp : 1 ≤ p) :
    Optimization.HigherOrderRegularization.DiagonalLipschitz f p L := by
  have hL : 0 ≤ L := zero_le_one.trans hf.constant_ge_one
  refine ⟨hf.smooth, hL, fun x y d => ?_⟩
  exact ((iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y).diagonalNorm_le_iff
    (by omega) (mul_nonneg hL (norm_nonneg _))).mp (hf.bound x y) d

/-- The regularized Taylor model (4.1.2). -/
def higherOrderModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  taylorModel f p x s + sigma / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)

/-- The surface model agrees with the reusable model, including its normalization. -/
theorem higherOrderModel_eq_model (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ) :
    higherOrderModel f p x sigma = Optimization.HigherOrderRegularization.model f p x sigma := rfl

/-- The small-curvature model directions in (4.1.14), for the actual regularized model. -/
def modelFlatDirections (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma theta2 : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ‖d‖ = 1 ∧ |iteratedFDeriv ℝ 2 (higherOrderModel f p x sigma) s (fun _ => d)| ≤
    theta2 * ‖s‖ ^ (p - 1)}

/-- The objective's small-curvature directions in (4.1.4). -/
def objectiveFlatDirections (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (epsilon2 : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ‖d‖ = 1 ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ epsilon2}

/-- Membership in the model direction set is exactly the source's unit-curvature test. -/
@[simp] theorem mem_modelFlatDirections (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma theta2 : ℝ)
    (s d : EuclideanSpace ℝ (Fin n)) :
    d ∈ modelFlatDirections f p x sigma theta2 s ↔ ‖d‖ = 1 ∧
      |iteratedFDeriv ℝ 2 (higherOrderModel f p x sigma) s (fun _ => d)| ≤
        theta2 * ‖s‖ ^ (p - 1) := Iff.rfl

/-- Membership in the objective direction set is exactly the source's unit-curvature test. -/
@[simp] theorem mem_objectiveFlatDirections (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (epsilon2 : ℝ) :
    d ∈ objectiveFlatDirections f x epsilon2 ↔ ‖d‖ = 1 ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ epsilon2 := Iff.rfl

/-- The actual model-decrease, ratio, iterate and parameter-update clauses used by the first
two value lemmas. Derivative residual tests are additional ARp requirements. -/
abbrev higherOrderTrialTrace (params : regularizationParameters) (p : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) : Prop :=
  Optimization.HigherOrderRegularization.TrialTrace params p f x s sigma

/-- Lemma 4.1.1: every nonincreasing regularized model pays its regularization in the
Taylor decrease. -/
theorem lemma_4_1_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}
    {x s : EuclideanSpace ℝ (Fin n)} {sigma : ℝ}
    (h : higherOrderModel f p x sigma s ≤ higherOrderModel f p x sigma 0) :
    sigma / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ taylorModel f p x 0 - taylorModel f p x s :=
  Optimization.HigherOrderRegularization.predicted_decrease_of_model_le h

/-- Lemma 4.1.2: the source's diagonal f.DpL assumption and actual trial laws give a uniform
upper bound on every regularization parameter. -/
theorem lemma_4_1_2 {params : regularizationParameters} {p : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (hp : 1 ≤ p) (hf : higherOrderLipschitz f p L)
    (h : higherOrderTrialTrace params p f x s sigma) (k : ℕ) :
    sigma k ≤ max (sigma 0) (params.gamma3 * L / (1 - params.eta2)) := by
  simpa only [mul_div_assoc] using h.sigma_upper (hf.toDiagonalLipschitz hp) hp k

/-- The source's model directions agree with the canonical actual-curvature set. -/
theorem modelFlatDirections_eq_smallCurvatureDirections
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma theta2 : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) :
    modelFlatDirections f p x sigma theta2 s =
      Optimization.HigherOrderRegularization.smallCurvatureDirections
        (Optimization.HigherOrderRegularization.model f p x sigma) s
        (theta2 * ‖s‖ ^ (p - 1)) := rfl

/-- The initial objective direction set agrees with the canonical actual-curvature set. -/
theorem objectiveFlatDirections_eq_smallCurvatureDirections
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (epsilon2 : ℝ) :
    objectiveFlatDirections f x epsilon2 =
      Optimization.HigherOrderRegularization.smallCurvatureDirections f x epsilon2 := rfl

/-- The source's stopping test. `q = 1, 2, 3` activates the corresponding finite thresholds;
unused thresholds stand for the source's infinity sentinels. The third-order branch tests only
`M`, requires it to be nonempty, and retains the strict positive-curvature alternative. -/
abbrev arpStationary (q : ℕ) (epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Optimization.HigherOrderRegularization.Stationary q epsilon f x M

/-- The source first-order branch is precisely its gradient-norm test (4.1.5). -/
@[simp] theorem arpStationary_one_iff (epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) :
    arpStationary 1 epsilon f x M ↔ ‖gradient f x‖ ≤ epsilon 0 := by
  rw [EuclideanSpace.norm_gradient_eq]
  exact Optimization.HigherOrderRegularization.stationary_one_iff _ _ _ _

/-- For second-order stopping the strict and nonstrict curvature branches combine into
(4.1.5) and (4.1.7). -/
@[simp] theorem arpStationary_two_iff (epsilon : Fin 3 → ℝ) (he : 0 ≤ epsilon 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) :
    arpStationary 2 epsilon f x M ↔
      ‖gradient f x‖ ≤ epsilon 0 ∧ -epsilon 1 ≤ leastHessianEigenvalue f x := by
  rw [EuclideanSpace.norm_gradient_eq]
  constructor
  · intro h
    exact ⟨h.first, h.second (by decide) he⟩
  · rintro ⟨hg, hH⟩
    exact ⟨hg, fun _ => Or.inr ⟨hH, by simp⟩⟩

/-- The exact third-order termination alternatives (4.1.5)–(4.1.9), on the algorithm's
current model directions rather than all flat directions of the objective. -/
theorem arpStationary_three_iff (epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) :
    arpStationary 3 epsilon f x M ↔ ‖gradient f x‖ ≤ epsilon 0 ∧
      (epsilon 1 < leastHessianEigenvalue f x ∨
        (-epsilon 1 ≤ leastHessianEigenvalue f x ∧ M.Nonempty ∧ ∀ d ∈ M,
          |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ epsilon 2 ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ epsilon 1)) := by
  simp [arpStationary, Optimization.HigherOrderRegularization.Stationary,
    EuclideanSpace.norm_gradient_eq, leastHessianEigenvalue]

/-- Finite local laws of Algorithm 4.1.1, without assuming that the algorithm terminates. -/
abbrev arpPrefix (params : regularizationParameters) (q p : ℕ) (theta epsilon : Fin 3 → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N : ℕ) : Prop :=
  Optimization.HigherOrderRegularization.RunPrefix params q p theta epsilon f x s sigma N

/-- Algorithm 4.1.1: actual factorial-normalized model, strict decrease, activated residuals,
source interval updates, cached derivatives, and the first stopping index. The order `q` lies
between one and three and `p ≥ q`; inactive thresholds encode infinity. The model direction
set is updated after every computed trial, including rejected ones. -/
abbrev algorithm_4_1_1 (params : regularizationParameters) (q p : ℕ)
    (theta epsilon : Fin 3 → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ) (N : ℕ) : Prop :=
  Optimization.HigherOrderRegularization.IsRun params q p theta epsilon f x s sigma N

/-- At a third-order stop outside the strict-positive-curvature alternative, the tested
model directions are nonempty and belong to the objective's small-curvature directions. -/
theorem arpStationary.model_directions_subset_objectiveFlatDirections
    {epsilon : Fin 3 → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {M : Set (EuclideanSpace ℝ (Fin n))}
    (h : arpStationary 3 epsilon f x M) (hunit : ∀ d ∈ M, ‖d‖ = 1)
    (hstrict : ¬epsilon 1 < leastHessianEigenvalue f x) :
    M.Nonempty ∧ M ⊆ objectiveFlatDirections f x (epsilon 1) := by
  have ht := h.third (by decide) hstrict
  exact ⟨ht.1, fun d hd => ⟨hunit d hd, (ht.2 d hd).2⟩⟩

/-- The source parameter estimate also holds on a finite executed prefix, including its
final index; no continuation or terminal certificate is an assumption. -/
theorem arpPrefix.sigma_upper {params : regularizationParameters} {q p N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : arpPrefix params q p theta epsilon f x s sigma N)
    (hf : higherOrderLipschitz f p L) {k : ℕ} (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (params.gamma3 * L / (1 - params.eta2)) := by
  have hp : 1 ≤ p := h.order_pos.trans h.degree_ge_order
  simpa only [mul_div_assoc] using h.toTrialPrefix.sigma_upper
    (hf.toDiagonalLipschitz hp) hp hk

open Optimization.HigherOrderRegularization

/-- Lemma 4.1.3, (4.1.20)–(4.1.23): every activated criticality measure at the accepted
successor is bounded by its sharp factorial coefficient times the corresponding step power.
The reciprocal of `criticalityConstant` is exactly the factorial fraction printed in the
source. Both third-order tests remain restricted to the computed model direction set. -/
theorem lemma_4_1_3 [NeZero n] {params : regularizationParameters} {q p N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : arpPrefix params q p theta epsilon f x s sigma N)
    (hf : higherOrderLipschitz f p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) :
    let S := max (sigma 0) (params.gamma3 * L / (1 - params.eta2))
    ‖gradient f (x (k + 1))‖ ≤ criticalityConstant p 1 L S (theta 0) * ‖s k‖ ^ p ∧
    (2 ≤ q → max 0 (-leastHessianEigenvalue f (x (k + 1))) ≤
      criticalityConstant p 2 L S (theta 1) * ‖s k‖ ^ (p - 1)) ∧
    (3 ≤ q → ∀ d ∈ modelFlatDirections f p (x k) (sigma k) (theta 1) (s k),
      |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ ↦ d)| ≤
        criticalityConstant p 3 L S (theta 2) * ‖s k‖ ^ (p - 2) ∧
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ ↦ d)| ≤
        criticalityConstant p 2 L S (theta 1) * ‖s k‖ ^ (p - 1)) := by
  dsimp only
  have hp : 1 ≤ p := h.order_pos.trans h.degree_ge_order
  have hS := h.sigma_upper hf (by omega : k ≤ N)
  have hL := hf.toDiagonalLipschitz hp
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.norm_gradient_eq] using h.gradient_bound hL hk hs hS
  · intro hq
    exact h.curvature_bound hL hq hk hs hS
  · intro hq d hd
    exact h.flat_direction_bounds hL hq hk hs hS hd

/-- Lemma 4.1.4, (4.1.31)–(4.1.36): every accepted trial gives the gradient, activated
negative-curvature and model-direction cubic real-power decreases. The constants are exactly
(4.1.32), (4.1.34), and (4.1.36), as `decreaseConstant_eq_factorial` shows. -/
theorem lemma_4_1_4 [NeZero n] {params : regularizationParameters} {q p N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : arpPrefix params q p theta epsilon f x s sigma N)
    (hf : higherOrderLipschitz f p L) {k : ℕ} (hk : k < N)
    (hs : params.eta1 ≤ ratio f p (x k) (s k)) :
    let S := max (sigma 0) (params.gamma3 * L / (1 - params.eta2))
    decreaseConstant params p 1 L S (theta 0) * ‖gradient f (x (k + 1))‖ ^
      (((p + 1 : ℕ) : ℝ) / p) ≤ f (x k) - f (x (k + 1)) ∧
    (2 ≤ q → decreaseConstant params p 2 L S (theta 1) *
      (max 0 (-leastHessianEigenvalue f (x (k + 1)))) ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤ f (x k) - f (x (k + 1))) ∧
    (3 ≤ q → ∀ d ∈ modelFlatDirections f p (x k) (sigma k) (theta 1) (s k),
      decreaseConstant params p 3 L S (theta 2) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ ↦ d)| ^
          (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤ f (x k) - f (x (k + 1))) := by
  dsimp only
  have hp : 1 ≤ p := h.order_pos.trans h.degree_ge_order
  have hS := h.sigma_upper hf (by omega : k ≤ N)
  have hL := hf.toDiagonalLipschitz hp
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EuclideanSpace.norm_gradient_eq] using h.gradient_decrease hL hk hs hS
  · intro hq
    exact h.curvature_decrease hL hq hk hs hS
  · intro hq d hd
    exact h.cubic_decrease hL hq hk hs hS hd

end CartisGouldToint.Chapter04.Section01
