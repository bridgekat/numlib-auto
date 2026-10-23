import Numlib.Optimization.Constrained.FirstOrderCriticality

/-!
# Actual derivative criticality on restricted feasible directions

Each measure is minus the minimum of a genuine derivative diagonal on the
restricted unit ball. Operator-norm bounds make the supremum finite even
without compactness. Closedness and properness additionally give attainment.
The first and second restrictions use the actual lower-order derivatives.
-/

namespace TaylorModel
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Minus the infimum of a tensor diagonal on restricted unit directions. -/
noncomputable def tensorCriticality {j : ℕ} (T : E [×j]→L[ℝ] ℝ) (A : Set E) : ℝ :=
  sSup ((fun d => -T (fun _ => d)) '' (A ∩ closedBall 0 1))

/-- Every tensor diagonal on the unit ball has absolute value at most its operator norm. -/
theorem abs_diagonal_le_norm {j : ℕ} (T : E [×j]→L[ℝ] ℝ) {d : E} (hd : ‖d‖ ≤ 1) :
    |T (fun _ => d)| ≤ ‖T‖ := by
  have hh := T.le_opNorm (fun _ => d)
  simp only [Fin.prod_const,Real.norm_eq_abs] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := j) (norm_nonneg d) hd) (norm_nonneg T)).trans_eq (mul_one _))

/-- Actual restricted tensor diagonals always form a bounded-above set. -/
theorem tensorCriticality_bddAbove {j : ℕ} (T : E [×j]→L[ℝ] ℝ) (A : Set E) :
    BddAbove ((fun d => -T (fun _ => d)) '' (A ∩ closedBall 0 1)) := by
  refine ⟨‖T‖,?_⟩
  rintro y ⟨d,hd,rfl⟩
  exact (neg_le_abs _).trans (abs_diagonal_le_norm T (by simpa using hd.2))

/-- Every actual feasible derivative diagonal is bounded by its criticality. -/
theorem neg_diagonal_le_tensorCriticality {j : ℕ} (T : E [×j]→L[ℝ] ℝ) {A : Set E}
    {d : E} (hd : d ∈ A) (hn : ‖d‖ ≤ 1) : -T (fun _ => d) ≤ tensorCriticality T A :=
  le_csSup (tensorCriticality_bddAbove T A) ⟨d,⟨hd,by simpa using hn⟩,rfl⟩

/-- Bounding the genuine measure is equivalent to bounding all its actual tensor diagonals. -/
theorem tensorCriticality_le_iff {j : ℕ} (T : E [×j]→L[ℝ] ℝ) {A : Set E}
    (hA : (0 : E) ∈ A) {b : ℝ} : tensorCriticality T A ≤ b ↔
      ∀ d ∈ A, ‖d‖ ≤ 1 → -T (fun _ => d) ≤ b := by
  constructor
  · exact fun h d hd hn => (neg_diagonal_le_tensorCriticality T hd hn).trans h
  · intro h
    unfold tensorCriticality
    have hne : ((fun d => -T (fun _ => d)) '' (A ∩ closedBall 0 1)).Nonempty :=
      ⟨-T (fun _ => 0),0,⟨hA,by simp⟩,rfl⟩
    apply csSup_le hne
    rintro y ⟨d,hd,rfl⟩
    exact h d hd.1 (by simpa using hd.2)

/-- A positive-order tensor has nonnegative restricted criticality whenever zero is feasible. -/
theorem tensorCriticality_nonneg {j : ℕ} (hj : 0 < j) (T : E [×j]→L[ℝ] ℝ)
    {A : Set E} (hA : (0 : E) ∈ A) : 0 ≤ tensorCriticality T A := by
  have hh := neg_diagonal_le_tensorCriticality T hA (by simp : ‖(0 : E)‖ ≤ 1)
  have hz := T.map_coord_zero (m := fun _ => (0 : E)) (⟨0,hj⟩ : Fin j) rfl
  simpa only [hz,neg_zero] using hh

/-- Enlarging actual feasible directions cannot decrease derivative criticality. -/
theorem tensorCriticality_mono {j : ℕ} (T : E [×j]→L[ℝ] ℝ) {A B : Set E}
    (hA : (0 : E) ∈ A) (hAB : A ⊆ B) : tensorCriticality T A ≤ tensorCriticality T B :=
  (tensorCriticality_le_iff T hA).mpr
    (fun _ hd hn => neg_diagonal_le_tensorCriticality T (hAB hd) hn)

/-- The actual tensor norm error bounds the change of the restricted derivative measure. -/
theorem tensorCriticality_le_of_error {j : ℕ} (T U : E [×j]→L[ℝ] ℝ)
    {A : Set E} (hA : (0 : E) ∈ A) {b : ℝ} (he : ‖T-U‖ ≤ b) :
    tensorCriticality T A ≤ tensorCriticality U A + b := by
  apply (tensorCriticality_le_iff T hA).mpr
  intro d hd hn
  have hh := (abs_diagonal_le_norm (T-U) hn).trans he
  simp only [sub_apply] at hh
  have hu := neg_diagonal_le_tensorCriticality U hd hn
  have := (abs_le.mp hh).1
  linarith

/-- Closed restricted unit balls attain the actual tensor criticality supremum. -/
theorem exists_diagonal_eq_tensorCriticality [ProperSpace E] {j : ℕ}
    (T : E [×j]→L[ℝ] ℝ) {A : Set E} (hclosed : IsClosed A) (hA : (0 : E) ∈ A) :
    ∃ d ∈ A, ‖d‖ ≤ 1 ∧ -T (fun _ => d) = tensorCriticality T A := by
  have hc : Continuous (fun d : E => -T (fun _ => d)) := by fun_prop
  obtain ⟨d,hd,he⟩ := ((isCompact_closedBall (0 : E) 1).inter_left hclosed).exists_sSup_image_eq
    ⟨0,hA,by simp⟩ hc.continuousOn
  exact ⟨d,hd.1,by simpa using hd.2,he.symm⟩

/-- Actual first-order derivative restrictions on a base direction set. -/
def firstRestrictedDirections (f : E → ℝ) (A : Set E) (x : E) (a : ℝ) : Set E :=
  {d ∈ A | |fderiv ℝ f x d| ≤ a}

/-- Actual second-order restrictions refine the first-order direction set. -/
def secondRestrictedDirections (f : E → ℝ) (A : Set E) (x : E) (a b : ℝ) : Set E :=
  {d ∈ firstRestrictedDirections f A x a | |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ b}

/-- First-restriction membership uses the genuine derivative applied to the direction. -/
@[simp] theorem mem_firstRestrictedDirections {f : E → ℝ} {A : Set E} {x d : E} {a : ℝ} :
    d ∈ firstRestrictedDirections f A x a ↔ d ∈ A ∧ |fderiv ℝ f x d| ≤ a := Iff.rfl

/-- Second-restriction membership retains both genuine lower derivative bounds. -/
@[simp] theorem mem_secondRestrictedDirections {f : E → ℝ} {A : Set E} {x d : E}
    {a b : ℝ} : d ∈ secondRestrictedDirections f A x a b ↔
      d ∈ firstRestrictedDirections f A x a ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ b :=
  Iff.rfl

/-- Nonnegative tolerances retain zero in the actual first restricted set. -/
theorem zero_mem_firstRestrictedDirections {f : E → ℝ} {A : Set E} {x : E} {a : ℝ}
    (hA : (0 : E) ∈ A) (ha : 0 ≤ a) : 0 ∈ firstRestrictedDirections f A x a := by
  exact ⟨hA,by simpa using ha⟩

/-- Nonnegative tolerances retain zero through both actual derivative restrictions. -/
theorem zero_mem_secondRestrictedDirections {f : E → ℝ} {A : Set E} {x : E} {a b : ℝ}
    (hA : (0 : E) ∈ A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ∈ secondRestrictedDirections f A x a b := by
  refine ⟨zero_mem_firstRestrictedDirections hA ha,?_⟩
  rw [(iteratedFDeriv ℝ 2 f x).map_coord_zero (m := fun _ => (0 : E)) (0 : Fin 2) rfl]
  simpa using hb

/-- First derivative restrictions preserve closedness without any extra objective smoothness. -/
theorem isClosed_firstRestrictedDirections {f : E → ℝ} {A : Set E} {x : E} {a : ℝ}
    (hA : IsClosed A) : IsClosed (firstRestrictedDirections f A x a) :=
  hA.inter (isClosed_le (fderiv ℝ f x).continuous.abs continuous_const)

/-- Second derivative restrictions preserve closedness of the actual direction set. -/
theorem isClosed_secondRestrictedDirections {f : E → ℝ} {A : Set E} {x : E} {a b : ℝ}
    (hA : IsClosed A) : IsClosed (secondRestrictedDirections f A x a b) := by
  have hc : Continuous (fun d : E => |iteratedFDeriv ℝ 2 f x (fun _ => d)|) := by fun_prop
  exact (isClosed_firstRestrictedDirections hA).inter (isClosed_le hc continuous_const)

/-- The derivative-component measure at order one is exactly the source
first-order constrained Taylor criticality on the actual feasible displacement set. -/
theorem tensorCriticality_one (f : E → ℝ) (C : Set E) (x : E) :
    tensorCriticality (iteratedFDeriv ℝ 1 f x) (feasibleDisplacements C x) =
      constrainedCriticality f 1 C x 1 := by
  have he : (fun d => -(iteratedFDeriv ℝ 1 f x) (fun _ => d)) = decrement f 1 x := by
    funext d
    simp [decrement,eval_eq_sum,Finset.sum_range_succ,iteratedFDeriv_one_apply,smul_eq_mul]
  rw [tensorCriticality,he]
  rfl

end TaylorModel
