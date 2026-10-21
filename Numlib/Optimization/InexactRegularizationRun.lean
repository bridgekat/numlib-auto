import Numlib.Optimization.InexactRegularizationAccuracy

/-!
# Complete implicit-accuracy regularization runs

A complete run contains genuine initialization and every actual transition. Its finite
prefixes share the same point, request, trial and acceptance arrays. No stopping-quality,
convergence, radius-floor or evaluation-count certificate is part of the interface.
Tolerance replacement keeps the objective-independent control data fixed.
-/

noncomputable section
namespace Optimization.InexactRegularization
open InexactTaylorModels
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Replace only requested tolerances and their admissibility proofs. Every other field,
including update constants, model orders and accuracy controls, remains fixed. -/
def Parameters.withTolerances (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) : Parameters :=
  { P with epsilon := ε, epsilon_pos := hpos, epsilon_lt_one := hlt }

/-- Tolerance replacement supplies exactly the requested tolerance vector. -/
@[simp] theorem Parameters.withTolerances_epsilon (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).epsilon = ε := rfl

/-- The underlying update parameters do not change when tolerances vary. -/
@[simp] theorem Parameters.withTolerances_updates (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).toParameters.toRegularizationParameters =
      P.toParameters.toRegularizationParameters := rfl

/-- The fixed model degree is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_p (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).p = P.p := rfl

/-- The fixed tested order is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_q (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).q = P.q := rfl

/-- The fixed model accuracy factor is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_theta (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).theta = P.theta := rfl

/-- The fixed fractional witness factor is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_fraction (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).fraction = P.fraction := rfl

/-- The fixed initial request cap is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_kappaInitial (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).kappaInitial = P.kappaInitial := rfl

/-- The fixed step accuracy coefficient is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_kappaStep (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).kappaStep = P.kappaStep := rfl

/-- The fixed geometric accuracy contraction is preserved under tolerance replacement. -/
@[simp] theorem Parameters.withTolerances_gammaAccuracy (P : Parameters) (ε : ℕ → ℝ)
    (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
    (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) :
    (P.withTolerances ε hpos hlt).gammaAccuracy = P.gammaAccuracy := rfl

/-- A complete run has the actual initialized data of a zero-length execution, together
with an actual legal transition at every index. There is no desired stopping test in these
data; availability of every finite operational prefix follows directly. -/
structure Run (P : Parameters) (checked : ℕ) (f : E → ℝ)
    (oracle : E → (ℕ → ℝ) → Coefficients E) extends Execution P checked f oracle 0 where
  transition_all : ∀ k, Transition P checked f oracle (state k) (state (k + 1))
    (trial k) (accepted k)

/-- Restrict a complete actual run to any finite prefix, retaining its actual arrays. -/
def Run.prefix {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} (r : Run P checked f oracle) (N : ℕ) :
    Execution P checked f oracle N where
  state := r.state
  trial := r.trial
  accepted := r.accepted
  initial_fresh := r.initial_fresh
  initial_sigma := r.initial_sigma
  initial_radii := r.initial_radii
  initial_tolerance := r.initial_tolerance
  initial_request := r.initial_request
  initial_request_le := r.initial_request_le
  transition := fun k _ => r.transition_all k

/-- Every prefix uses the complete run's actual states at all array indices. -/
@[simp] theorem Run.prefix_state {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} (r : Run P checked f oracle) (N : ℕ) :
    (r.prefix N).state = r.state := rfl

/-- Every prefix uses the complete run's actual trial-event array. -/
@[simp] theorem Run.prefix_trial {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} (r : Run P checked f oracle) (N : ℕ) :
    (r.prefix N).trial = r.trial := rfl

/-- Every prefix uses the complete run's actual accepted-event array. -/
@[simp] theorem Run.prefix_accepted {P : Parameters} {checked : ℕ} {f : E → ℝ}
    {oracle : E → (ℕ → ℝ) → Coefficients E} (r : Run P checked f oracle) (N : ℕ) :
    (r.prefix N).accepted = r.accepted := rfl

end Optimization.InexactRegularization
