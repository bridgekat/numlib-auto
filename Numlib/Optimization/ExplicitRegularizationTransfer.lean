import Numlib.Optimization.ExplicitRegularizationBounds
import Numlib.Optimization.InexactRegularizationTransfer
import Numlib.Optimization.InexactRegularizationRequestRatios

/-!
# Initial-radius tests and endpoint transfer for explicit regularization

An uncertified inspection need not fail a true objective criterion. Its actual radius
searches instead give a dichotomy at the incoming radii: a computed initial witness fails,
or an observable error sum fails with no halving. The initial witness of a search, rather
than its retained witness at a possibly smaller radius, is essential to this statement.

At an accepted short step, the unchanged request vector controls errors in both endpoint
jets. The resulting transfer estimate retains the literal outer half threshold and the
actual inner tolerance factor. Their difference need not be positive under the source
parameter restrictions; no certified-complexity conclusion is asserted here.
-/

noncomputable section
open scoped Nat
namespace Optimization.ExplicitRegularization
open InexactTaylorModels TaylorCriticality

section Normed
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Parameters} {f : E → ℝ} {O : Oracle f P.p} {a b : State E}

/-- An incoming-radius approximate failure, exhibited by a genuine compact-gap fraction
witness. A recorded failing initial inspection direction supplies such a witness. -/
def InitialFailure (P : Parameters)
    (oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E) (a : State E) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ P.q ∧ ∃ d : E,
    InexactRegularization.CoefficientWitness (oracle a.point a.request) j
      (a.radii j) P.fraction d ∧
    P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) <
      decrement (oracle a.point a.request) j d

/-- The incoming-radius error check uses exactly the request vector stored at the state,
independently of which radii a later inspection retains. -/
def IncomingErrorCheck (P : Parameters) (a : State E) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q →
    ∑ i ∈ Finset.Icc 1 j, a.request i * a.radii j ^ i / (i ! : ℝ) ≤
      P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ))

/-- Incoming-radius approximate failure is characterized by a genuine fraction witness. -/
theorem initialFailure_iff (P : Parameters)
    (oracle : E → (ℕ → ℝ) → InexactRegularization.Coefficients E) (a : State E) :
    InitialFailure P oracle a ↔
      ∃ j, 1 ≤ j ∧ j ≤ P.q ∧ ∃ d : E,
        InexactRegularization.CoefficientWitness (oracle a.point a.request) j
          (a.radii j) P.fraction d ∧
        P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) <
          decrement (oracle a.point a.request) j d := Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Failure of the incoming error check exhibits an actual offending active sum. -/
theorem not_incomingErrorCheck_iff (P : Parameters) (a : State E) :
    ¬IncomingErrorCheck P a ↔ ∃ j, 1 ≤ j ∧ j ≤ P.q ∧
      P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) <
        ∑ i ∈ Finset.Icc 1 j, a.request i * a.radii j ^ i / (i ! : ℝ) := by
  simp only [IncomingErrorCheck, not_forall, not_le, exists_prop]

/-- A visited order's actual recorded index-zero direction fails its computed test at the
incoming radius. This concerns this inspection's choices, rather than other possible witnesses. -/
def Inspection.InitialFailure (I : Inspection P O.derivative a) : Prop :=
  ∃ j, ∃ (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j ≤ I.order),
    P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) <
      decrement (O.derivative a.point a.request) j
        ((I.search j hj hjq hjo).direction 0)

/-- The initial-failure predicate exposes the actual recorded initial direction and order. -/
theorem Inspection.initialFailure_iff (I : Inspection P O.derivative a) :
    I.InitialFailure ↔ ∃ j, ∃ (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j ≤ I.order),
      P.fraction * P.epsilon j * a.radii j ^ j / (2 * (j ! : ℝ)) <
        decrement (O.derivative a.point a.request) j
          ((I.search j hj hjq hjo).direction 0) := Iff.rfl

/-- A recorded initial failure supplies its actual fraction witness at the incoming radius. -/
theorem Inspection.initialFailure_imp (I : Inspection P O.derivative a)
    (hn : I.InitialFailure) :
    Optimization.ExplicitRegularization.InitialFailure P O.derivative a := by
  obtain ⟨j, hj, hjq, hjo, hh⟩ := hn
  refine ⟨j, hj, hjq, (I.search j hj hjq hjo).direction 0, ?_, hh⟩
  simpa only [InexactRegularization.halvedRadius_zero] using
    (I.search j hj hjq hjo).witness 0 (Nat.zero_le _)

/-- Any actual positive halving count exhibits a failing witness at the original incoming
radius. The selected witness is the search's index-zero witness. -/
theorem Inspection.initialFailure_of_halving (I : Inspection P O.derivative a)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j ≤ I.order)
    (hh : 0 < I.halvings j) : I.InitialFailure := by
  refine ⟨j, hj, hjq, hjo, ?_⟩
  simpa only [InexactRegularization.halvedRadius_zero] using
    ((I.search j hj hjq hjo).failed 0 hh).1

/-- If no incoming initial witness fails, every visited search has zero halvings. -/
theorem Inspection.halvings_eq_zero_of_not_initialFailure (I : Inspection P O.derivative a)
    (hn : ¬I.InitialFailure) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ P.q) (hjo : j ≤ I.order) : I.halvings j = 0 := by
  by_contra hh
  exact hn (I.initialFailure_of_halving hj hjq hjo (Nat.pos_of_ne_zero hh))

/-- Absence of every initial witness failure forces the actual inspection to pass all
orders. A retained failing order would itself give an initial failure when no halving occurs. -/
theorem Inspection.all_pass_of_not_initialFailure (I : Inspection P O.derivative a)
    (hn : ¬I.InitialFailure) : I.order = P.q + 1 := by
  by_contra hh
  have hq : I.order ≤ P.q := by have := I.order_le; omega
  have hz := I.halvings_eq_zero_of_not_initialFailure hn I.order_pos hq le_rfl
  apply hn
  refine ⟨I.order, I.order_pos, hq, le_rfl, ?_⟩
  simpa only [hz, InexactRegularization.halvedRadius_zero] using I.failed hq

/-- Without an initial computed failure, all active inspection radii equal their incoming
values. This is derived from the searches, not assumed for a general completed inspection. -/
theorem Inspection.radii_eq_of_not_initialFailure (I : Inspection P O.derivative a)
    (hn : ¬I.InitialFailure) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ P.q) : I.radii j = a.radii j := by
  have ho := I.all_pass_of_not_initialFailure hn
  have hjo : j ≤ I.order := by omega
  simp only [InexactRegularization.Inspection.radii, ite_eq_left hjo,
    I.halvings_eq_zero_of_not_initialFailure hn hj hjq hjo,
    InexactRegularization.halvedRadius_zero]

/-- When no initial computed failure occurs, the post-inspection error check is exactly
its incoming-radius counterpart. -/
theorem Inspection.errorCheck_iff_incoming_of_not_initialFailure
    (I : Inspection P O.derivative a) (hn : ¬I.InitialFailure) :
    ErrorCheck P a I ↔ IncomingErrorCheck P a := by
  unfold ErrorCheck IncomingErrorCheck
  constructor <;> intro h j hj hjq
  · simpa only [I.radii_eq_of_not_initialFailure hn hj hjq] using h j hj hjq
  · simpa only [I.radii_eq_of_not_initialFailure hn hj hjq] using h j hj hjq

/-- Every actual uncertified inspection gives an initial incoming-radius computed failure,
or an incoming-radius error-sum failure. In the second case all active search counts are
zero and all active radii are unchanged. This avoids identifying arbitrary retained and
incoming radii. -/
theorem Inspection.not_certified_initial_cases (I : Inspection P O.derivative a)
    (hnc : ¬Certified P a I) : I.InitialFailure ∨
      (¬IncomingErrorCheck P a ∧ I.order = P.q + 1 ∧
        ∀ j, 1 ≤ j → j ≤ P.q → I.halvings j = 0 ∧ I.radii j = a.radii j) := by
  by_cases hn : I.InitialFailure
  · exact Or.inl hn
  · refine Or.inr ⟨?_, I.all_pass_of_not_initialFailure hn, ?_⟩
    · intro he
      exact hnc ⟨I.all_pass_of_not_initialFailure hn,
        (I.errorCheck_iff_incoming_of_not_initialFailure hn).mpr he⟩
    · intro j hj hjq
      have hjo : j ≤ I.order := by have := I.all_pass_of_not_initialFailure hn; omega
      exact ⟨I.halvings_eq_zero_of_not_initialFailure hn hj hjq hjo,
        I.radii_eq_of_not_initialFailure hn hj hjq⟩

end Normed
end Optimization.ExplicitRegularization

namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Errors in both endpoint jets transfer an actual short returned model test to the next
supplied objective gap. The old shifted model costs three error factors and the new supplied
jet costs one; the polynomial constant is arbitrary and cancels from every decrement. -/
theorem InnerResult.endpoint_gap_le {P : Parameters} {c : ℝ} {f : E → ℝ} {x : E}
    {A B : Coefficients E} {σ S L K : ℝ} {δ : ℕ → ℝ} {d : E}
    (s : InnerResult P c A σ δ d)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ) (hS : σ ≤ S) (hne : s.step ≠ 0)
    (hs : ‖s.step‖ < 1)
    (hA : ∀ i ∈ Finset.Icc 1 P.p,
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * P.kappaStep * ‖s.step‖ ^ (P.p - i + 1))
    (hB : ∀ i ∈ Finset.Icc 1 P.p,
      ‖B i - iteratedFDeriv ℝ i f (x + s.step)‖ ≤
        K * P.kappaStep * ‖s.step‖ ^ (P.p - i + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ P.q) (hδ : 0 ≤ s.radii j) :
    gapOn (decrement B j) (Metric.closedBall 0 (s.radii j)) ≤
      P.theta * P.epsilon j * s.radii j ^ j / (j ! : ℝ) +
        (L + S + 4 * K * P.kappaStep) * ∑ l ∈ Finset.Icc 1 j,
          s.radii j ^ l * ‖s.step‖ ^ (P.p - l + 1) / (l ! : ℝ) := by
  have hnext := gap_error_le B (fun i => iteratedFDeriv ℝ i f (x + s.step))
    (fun i => K * P.kappaStep * ‖s.step‖ ^ (P.p - i + 1))
    (q := j) (isCompact_closedBall (0 : E) (s.radii j)) ⟨0, by simpa using hδ⟩ hδ
    (Set.Subset.refl _) (fun i hi => hB i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hjq.trans P.order_le)⟩))
  have hsum : (∑ i ∈ Finset.Icc 1 j,
      K * P.kappaStep * ‖s.step‖ ^ (P.p - i + 1) * s.radii j ^ i / (i ! : ℝ)) =
      K * P.kappaStep * ∑ i ∈ Finset.Icc 1 j,
        s.radii j ^ i * ‖s.step‖ ^ (P.p - i + 1) / (i ! : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he : decrement (fun i => iteratedFDeriv ℝ i f (x + s.step)) j =
      taylorDecrement f j (x + s.step) := funext (decrement_iteratedFDeriv f _ j)
  rw [he, hsum] at hnext
  have hgap := gapOn_le_gapOn_add (Δ := taylorDecrement f j (x + s.step))
    (η := (L + S) * ∑ l ∈ Finset.Icc 1 j,
      s.radii j ^ l * ‖s.step‖ ^ (P.p - l + 1) / (l ! : ℝ))
    (isCompact_closedBall (0 : E) (s.radii j)) ⟨0, by simpa using hδ⟩
    (continuous_taylorDecrement (HigherOrderRegularization.model f P.p x σ) j
      s.step).continuousOn (fun z hz => by
      have hb := HigherOrderApproximateRegularization.taylorDecrement_sub_model_le
        (x := x) hf (P.order_pos.trans P.order_le) (hjq.trans P.order_le)
        hne hσ hS z (by simpa using hz)
      linarith only [(abs_le.mp hb).2])
  have hpert := regularizedPolynomial_gap_error_le_step_power (hjq.trans P.order_le)
    c (f x) A (fun i => iteratedFDeriv ℝ i f x) σ s.step hK P.kappaStep_pos.le hδ hA
  have hm : regularizedPolynomial (f x) (fun i => iteratedFDeriv ℝ i f x) P.p σ =
      HigherOrderRegularization.model f P.p x σ := by
    funext z
    rw [regularizedPolynomial, polynomial_iteratedFDeriv]
    unfold HigherOrderRegularization.model
    ring
  rw [hm] at hpert
  nlinarith only [(abs_le.mp hnext).2, hgap, (abs_le.mp hpert).1, s.gap_le hs hj hjq]

end Optimization.InexactRegularization
