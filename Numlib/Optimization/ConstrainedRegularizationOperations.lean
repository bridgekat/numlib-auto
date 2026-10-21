import Numlib.Optimization.ExplicitRegularization
import Numlib.Optimization.ConstrainedTaylorGaps

/-!
# Constrained polynomial searches and detailed model executions

Every coefficient witness uses the translated feasible ball. Model witnesses use the
translated feasible set at the actual trial endpoint. All-space embeddings preserve the
original selected directions, halving counts, attained minimizer and entire inner state
sequence, including calls subsequently discarded by outer accuracy refinement.
-/

noncomputable section
open Set Metric
open scoped Nat
namespace Optimization.ConstrainedRegularizationOperations
open InexactTaylorModels TaylorCriticality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The supplied polynomial gap on the actual feasible displacement ball. -/
def coefficientGap (X : Set E) (x : E) (A : InexactRegularization.Coefficients E) (j : ℕ) (δ : ℝ)
  : ℝ :=
  gapOn (decrement A j)
    (ConstrainedTaylorCriticality.feasibleDisplacements X x ∩ closedBall 0 δ)

/-- With no constraints, the supplied polynomial gap is the original full-ball gap. -/
@[simp] theorem coefficientGap_univ (x : E) (A : InexactRegularization.Coefficients E) (j : ℕ) (δ
  : ℝ) :
    coefficientGap univ x A j δ = gapOn (decrement A j) (closedBall 0 δ) := by
  simp [coefficientGap, ConstrainedTaylorCriticality.feasibleDisplacements]

/-- A direction is feasible for the actual constraints and captures a fraction of their gap. -/
structure CoefficientWitness (X : Set E) (x : E) (A : InexactRegularization.Coefficients E)
    (j : ℕ) (δ v : ℝ) (d : E) : Prop where
  feasible : x + d ∈ X
  norm_le : ‖d‖ ≤ δ
  fraction_le : v * coefficientGap X x A j δ ≤ decrement A j d

/-- The all-space coefficient witness is exactly the original witness, with no new query. -/
theorem coefficientWitness_univ_iff (x : E) (A : InexactRegularization.Coefficients E)
    (j : ℕ) (δ v : ℝ) (d : E) :
    CoefficientWitness univ x A j δ v d ↔ InexactRegularization.CoefficientWitness A j δ v d := by
  constructor
  · intro h
    exact ⟨h.norm_le, by simpa using h.fraction_le⟩
  · intro h
    exact ⟨mem_univ _, h.feasible, by simpa using h.fraction_le⟩

/-- A literal halving search retains every actual feasible direction and both failed tests. -/
structure RadiusSearch (X : Set E) (x : E) (c : ℝ) (A : InexactRegularization.Coefficients E) (p
  j : ℕ)
    (σ δ v ε : ℝ) (N : ℕ) where
  direction : ℕ → E
  witness : ∀ k, k ≤ N →
    CoefficientWitness X x A j (InexactRegularization.halvedRadius δ k) v (direction k)
  failed : ∀ k, k < N →
    v * ε * InexactRegularization.halvedRadius δ k ^ j / (2 * (j ! : ℝ)) < decrement A j
      (direction k) ∧
    c - regularizedPolynomial c A p σ (direction k) <
      v * ε * InexactRegularization.halvedRadius δ k ^ j / (4 * (j ! : ℝ))

/-- Every original radius search is literally a constrained search on all space. -/
def RadiusSearch.ofUnconstrained {c : ℝ} {A : InexactRegularization.Coefficients E} {p j : ℕ}
    {σ δ v ε : ℝ} {N : ℕ} (x : E) (s : InexactRegularization.RadiusSearch c A p j σ δ v ε N) :
    RadiusSearch univ x c A p j σ δ v ε N where
  direction := s.direction
  witness k hk := (coefficientWitness_univ_iff ..).mpr (s.witness k hk)
  failed := s.failed

/-- A completed constrained inspection retains every visited order and actual halving. -/
structure Inspection (X : Set E) (x : E) (P : InexactRegularization.Parameters) (c : ℝ)
    (A : InexactRegularization.Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) where
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ P.q + 1
  halvings : ℕ → ℕ
  search : ∀ j, 1 ≤ j → j ≤ P.q → j ≤ order →
    RadiusSearch X x c A P.p j σ (δ j) P.fraction (P.epsilon j) (halvings j)
  earlier : ∀ j (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j < order),
    decrement A j ((search j hj hjq hjo.le).direction (halvings j)) ≤
      P.fraction * P.epsilon j * InexactRegularization.halvedRadius (δ j) (halvings j) ^ j /
        (2 * (j ! : ℝ))
  failed : ∀ hq : order ≤ P.q,
    P.fraction * P.epsilon order * InexactRegularization.halvedRadius (δ order) (halvings order)
      ^ order /
        (2 * (order ! : ℝ)) <
      decrement A order ((search order order_pos hq le_rfl).direction (halvings order))
  retained : ∀ hq : order ≤ P.q,
    P.fraction * P.epsilon order * InexactRegularization.halvedRadius (δ order) (halvings order)
      ^ order /
        (4 * (order ! : ℝ)) ≤
      c - regularizedPolynomial c A P.p σ
        ((search order order_pos hq le_rfl).direction (halvings order))

/-- The all-space completed inspection preserves its exact order, halvings and directions. -/
def Inspection.ofUnconstrained {P : InexactRegularization.Parameters} {c : ℝ} {A :
  InexactRegularization.Coefficients E}
    {σ : ℝ} {δ : ℕ → ℝ} (x : E) (I : InexactRegularization.Inspection P c A σ δ) :
    Inspection univ x P c A σ δ where
  order := I.order
  order_pos := I.order_pos
  order_le := I.order_le
  halvings := I.halvings
  search j hj hjq hjo := RadiusSearch.ofUnconstrained x (I.search j hj hjq hjo)
  earlier := I.earlier
  failed := I.failed
  retained := I.retained

/-- The post-inspection radii keep all unvisited components unchanged. -/
def Inspection.radii {X : Set E} {x : E} {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ}
    (I : Inspection X x P c A σ δ) (j : ℕ) : ℝ :=
  if j ≤ I.order then InexactRegularization.halvedRadius (δ j) (I.halvings j) else δ j

/-- The actual failed direction passed to constrained model minimization. -/
def Inspection.direction {X : Set E} {x : E} {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ}
    (I : Inspection X x P c A σ δ) (hq : I.order ≤ P.q) : E :=
  (I.search I.order I.order_pos hq le_rfl).direction (I.halvings I.order)

/-- All-space embedding keeps the exact inspected radius vector, including every halving. -/
@[simp] theorem Inspection.ofUnconstrained_radii {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} (x : E)
    (I : InexactRegularization.Inspection P c A σ δ) : (Inspection.ofUnconstrained x I).radii =
      I.radii := rfl

/-- All-space embedding keeps the exact selected failed displacement. -/
@[simp] theorem Inspection.ofUnconstrained_direction {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} (x : E)
    (I : InexactRegularization.Inspection P c A σ δ) (hq : I.order ≤ P.q) :
    (Inspection.ofUnconstrained x I).direction hq = I.direction hq := rfl

/-- A model Taylor-gap witness is feasible at the actual translated model endpoint. -/
structure GapWitness (X : Set E) (x : E) (m : E → ℝ) (j : ℕ)
    (s : E) (δ v : ℝ) (d : E) : Prop where
  feasible : x + (s + d) ∈ X
  norm_le : ‖d‖ ≤ δ
  fraction_le : v * gapOn (taylorDecrement m j s)
    (ConstrainedTaylorCriticality.feasibleDisplacements X (x + s) ∩ closedBall 0 δ) ≤
      taylorDecrement m j s d

/-- For all space the translated model-gap witness is exactly the original one. -/
theorem gapWitness_univ_iff (x : E) (m : E → ℝ) (j : ℕ)
    (s : E) (δ v : ℝ) (d : E) :
    GapWitness univ x m j s δ v d ↔ HigherOrderApproximateRegularization.GapWitness m j s δ v d
      := by
  constructor
  · intro h
    exact ⟨h.norm_le, by
      simpa [ConstrainedTaylorCriticality.feasibleDisplacements] using h.fraction_le⟩
  · intro h
    exact ⟨mem_univ _, h.feasible, by
      simpa [ConstrainedTaylorCriticality.feasibleDisplacements] using h.fraction_le⟩

/-- Detailed model transitions use feasible model steps and actual constrained Taylor gaps. -/
inductive InnerTransition (X : Set E) (x : E) (P :
  HigherOrderApproximateRegularization.Parameters) (m : E → ℝ)
    (minimizer : E) : HigherOrderApproximateRegularization.InnerState E →
      HigherOrderApproximateRegularization.InnerState E → Prop where
  | minimize (a : HigherOrderApproximateRegularization.InnerState E) (hphase : a.phase = .minimize)
      (s : E) (hfeas : x + s ∈ X)
      (hfrac : a.mu * (m 0 - m minimizer) ≤ m 0 - m s) :
      InnerTransition X x P m minimizer a
        ⟨a.mu, a.radii, s, if 1 ≤ ‖s‖ then .returned else .inspect 1⟩
  | pass (a : HigherOrderApproximateRegularization.InnerState E) (j : ℕ) (hphase : a.phase =
    .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness X x m j a.step (a.radii j) P.fraction d)
      (htest : taylorDecrement m j a.step d ≤
        P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition X x P m minimizer a
        ⟨a.mu, a.radii, a.step, if j = P.q then .returned else .inspect (j + 1)⟩
  | halve (a : HigherOrderApproximateRegularization.InnerState E) (j : ℕ) (hphase : a.phase =
    .inspect j)
      (hj : 3 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness X x m j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        taylorDecrement m j a.step d)
      (hsmall : m a.step - m (a.step + d) <
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition X x P m minimizer a
        ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩
  | improve (a : HigherOrderApproximateRegularization.InnerState E) (j : ℕ) (hphase : a.phase =
    .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness X x m j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        taylorDecrement m j a.step d)
      (hother : j ≤ 2 ∨
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) ≤
          m a.step - m (a.step + d)) :
      InnerTransition X x P m minimizer a
        ⟨(1 + a.mu) / 2, a.radii, a.step, .minimize⟩

/-- Every actual original detailed branch is a constrained branch on all space. -/
theorem InnerTransition.ofUnconstrained {P : HigherOrderApproximateRegularization.Parameters} {m
  : E → ℝ} {z : E}
    {a b : HigherOrderApproximateRegularization.InnerState E} (x : E) (h :
      HigherOrderApproximateRegularization.InnerTransition P m z a b) :
    InnerTransition univ x P m z a b := by
  cases h with
  | minimize hp s hf => exact .minimize _ hp s (mem_univ _) hf
  | pass j hp hj hjq d hw ht =>
    exact .pass _ j hp hj hjq d ((gapWitness_univ_iff ..).mpr hw) ht
  | halve j hp hj hjq d hw hf hs =>
    exact .halve _ j hp hj hjq d ((gapWitness_univ_iff ..).mpr hw) hf hs
  | improve j hp hj hjq d hw hf ho =>
    exact .improve _ j hp hj hjq d ((gapWitness_univ_iff ..).mpr hw) hf ho

/-- Every non-minimizing successor has a feasible selected model step. -/
theorem InnerTransition.feasible {X : Set E} {x : E}
    {P : HigherOrderApproximateRegularization.Parameters} {m : E → ℝ} {z : E}
    {a b : HigherOrderApproximateRegularization.InnerState E}
    (h : InnerTransition X x P m z a b)
    (ha : a.phase ≠ .minimize → x + a.step ∈ X) (hb : b.phase ≠ .minimize) :
    x + b.step ∈ X := by
  cases h <;> simp_all

/-- Actual finite constrained inner traces use an attained minimum over feasible moves. -/
structure InnerExecution (X : Set E) (x : E) (P :
  HigherOrderApproximateRegularization.Parameters) (m : E → ℝ)
    (minimizer : E) (N : ℕ) where
  state : ℕ → HigherOrderApproximateRegularization.InnerState E
  minimizer_feasible : x + minimizer ∈ X
  is_minimizer : ∀ t, x + t ∈ X → m minimizer ≤ m t
  initial : HigherOrderApproximateRegularization.InnerInitial (state 0)
  transition : ∀ k, k < N → InnerTransition X x P m minimizer (state k) (state (k + 1))

/-- Every original actual inner execution embeds with the identical state function. -/
def InnerExecution.ofUnconstrained {P : HigherOrderApproximateRegularization.Parameters} {m : E →
  ℝ} {z : E} {N : ℕ}
    (x : E) (r : HigherOrderApproximateRegularization.InnerExecution P m z N) : InnerExecution
      univ x P m z N where
  state := r.state
  minimizer_feasible := mem_univ _
  is_minimizer t _ := r.is_minimizer t
  initial := r.initial
  transition k hk := InnerTransition.ofUnconstrained x (r.transition k hk)

/-- Every inspected or returned actual inner state is feasible. -/
theorem InnerExecution.feasible {X : Set E} {x : E}
    {P : HigherOrderApproximateRegularization.Parameters} {m : E → ℝ} {z : E} {N : ℕ}
    (r : InnerExecution X x P m z N) {k : ℕ} (hk : k ≤ N)
    (hp : (r.state k).phase ≠ .minimize) : x + (r.state k).step ∈ X := by
  induction k with
  | zero => exact (hp r.initial.2.2.2).elim
  | succ k ih =>
    exact (r.transition k (by omega)).feasible (fun hn => ih (by omega) hn) hp

/-- A returned constrained model execution retains the actual selected outer witness. -/
structure InnerResult (X : Set E) (x : E) (P : InexactRegularization.Parameters) (c : ℝ)
    (A : InexactRegularization.Coefficients E) (σ : ℝ) (δ : ℕ → ℝ) (d : E) where
  minimizer : E
  length : ℕ
  execution : InnerExecution X x P.toParameters (regularizedPolynomial c A P.p σ)
    minimizer length
  returned : (execution.state length).phase = .returned
  retained : regularizedPolynomial c A P.p σ (execution.state length).step ≤
    regularizedPolynomial c A P.p σ d

/-- A returned constrained call selects its actual terminal step. -/
def InnerResult.step {X : Set E} {x : E} {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} {d : E}
    (s : InnerResult X x P c A σ δ d) : E := (s.execution.state s.length).step

/-- Every returned actual model step is feasible by its executed inner transitions. -/
theorem InnerResult.feasible {X : Set E} {x : E} {P : InexactRegularization.Parameters}
    {c : ℝ} {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} {d : E}
    (s : InnerResult X x P c A σ δ d) : x + s.step ∈ X :=
  s.execution.feasible le_rfl (by rw [s.returned]; decide)

/-- The weak long-step boundary inherits the actual inspected outer radii. -/
def InnerResult.radii {X : Set E} {x : E} {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} {d : E}
    (s : InnerResult X x P c A σ δ d) : ℕ → ℝ :=
  if 1 ≤ ‖s.step‖ then δ else (s.execution.state s.length).radii

/-- Every original actual returned call embeds without changing any execution data. -/
def InnerResult.ofUnconstrained {P : InexactRegularization.Parameters} {c : ℝ} {A :
  InexactRegularization.Coefficients E}
    {σ : ℝ} {δ : ℕ → ℝ} {d : E} (x : E) (s : InexactRegularization.InnerResult P c A σ δ d) :
    InnerResult univ x P c A σ δ d where
  minimizer := s.minimizer
  length := s.length
  execution := InnerExecution.ofUnconstrained x s.execution
  returned := s.returned
  retained := s.retained

/-- Embedding preserves the actual returned step. -/
@[simp] theorem InnerResult.ofUnconstrained_step {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} {d : E} (x : E)
    (s : InexactRegularization.InnerResult P c A σ δ d) : (InnerResult.ofUnconstrained x s).step
      = s.step := rfl

/-- Embedding preserves the actual returned radii, including discarded refinement calls. -/
@[simp] theorem InnerResult.ofUnconstrained_radii {P : InexactRegularization.Parameters} {c : ℝ}
    {A : InexactRegularization.Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} {d : E} (x : E)
    (s : InexactRegularization.InnerResult P c A σ δ d) : (InnerResult.ofUnconstrained x s).radii
      = s.radii := rfl

end Optimization.ConstrainedRegularizationOperations
