import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# Signed diagonal coordinates

A Boolean partition specifies the positive and negative eigenspaces of an actual diagonal
matrix. Coordinate masking gives the two orthogonal components and the explicit shifted solve.
The algebraic identities do not require either sign space to be nonempty.
-/

open scoped ComplexOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal matrix with entry `1` on the positive part and `-1` on its complement. -/
def signedDiagonal (p : ι → Bool) : Matrix ι ι ℝ :=
  diagonal (fun i => if p i then 1 else -1)

/-- The component of a Euclidean vector supported on one part of a Boolean partition. -/
noncomputable def signComponent (p : ι → Bool) (b : Bool) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => if p i = b then x i else 0)

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinate formula for either sign component. -/
@[simp] theorem signComponent_apply (p : ι → Bool) (b : Bool)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    signComponent p b x i = if p i = b then x i else 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The positive and negative components sum to the original vector. -/
@[simp] theorem signComponent_add (p : ι → Bool) (x : EuclideanSpace ℝ ι) :
    signComponent p true x + signComponent p false x = x := by
  ext i
  cases h : p i <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
/-- Masking a vector twice either preserves the component or annihilates it. -/
@[simp] theorem signComponent_component (p : ι → Bool) (a b : Bool)
    (x : EuclideanSpace ℝ ι) :
    signComponent p a (signComponent p b x) = if a = b then signComponent p a x else 0 := by
  ext i
  cases a <;> cases b <;> cases h : p i <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
/-- Components commute with scalar multiplication. -/
@[simp] theorem signComponent_smul (p : ι → Bool) (b : Bool) (c : ℝ)
    (x : EuclideanSpace ℝ ι) : signComponent p b (c • x) = c • signComponent p b x := by
  ext i
  simp only [signComponent_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
/-- Components commute with addition. -/
@[simp] theorem signComponent_add_map (p : ι → Bool) (b : Bool)
    (x y : EuclideanSpace ℝ ι) :
    signComponent p b (x + y) = signComponent p b x + signComponent p b y := by
  ext i
  simp only [signComponent_apply, PiLp.add_apply]
  split_ifs <;> simp

omit [Fintype ι] in
/-- A signed diagonal matrix is symmetric. -/
theorem signedDiagonal_isSymm (p : ι → Bool) : (signedDiagonal p).IsSymm :=
  isSymm_diagonal _

omit [Fintype ι] in
/-- The actual diagonal shift is another explicitly given diagonal matrix. -/
theorem signedDiagonal_shift (p : ι → Bool) (lambda : ℝ) :
    signedDiagonal p + lambda • (1 : Matrix ι ι ℝ) =
      diagonal (fun i => lambda + if p i then 1 else -1) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [signedDiagonal, add_comm]
  · simp [signedDiagonal, h]

/-- The shifted matrix acts coordinatewise. -/
@[simp] theorem signedDiagonal_shift_apply (p : ι → Bool) (lambda : ℝ)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    toEuclideanLin (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ)) x i =
      (lambda + if p i then 1 else -1) * x i := by
  rw [signedDiagonal_shift]
  change (diagonal _ *ᵥ (WithLp.ofLp x)) i = _
  simp [mulVec, dotProduct, diagonal_apply]

/-- Coordinate characterization of stationarity for the actual shifted diagonal matrix. -/
theorem signedDiagonal_stationary_coordinates (p : ι → Bool) (g s : EuclideanSpace ℝ ι)
    (lambda : ℝ) :
    toEuclideanLin (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ)) s = -g ↔
      ∀ i, (lambda + if p i then 1 else -1) * s i = -g i := by
  constructor
  · intro h i
    simpa only [signedDiagonal_shift_apply, PiLp.neg_apply] using
      congrArg (fun x : EuclideanSpace ℝ ι => x i) h
  · intro h
    ext i
    simpa only [signedDiagonal_shift_apply, PiLp.neg_apply] using h i

omit [Fintype ι] in
/-- Positivity of a shifted signed matrix is exactly positivity of its diagonal entries. -/
theorem signedDiagonal_shift_posSemidef_iff (p : ι → Bool) (lambda : ℝ) :
    (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ)).PosSemidef ↔
      ∀ i, 0 ≤ lambda + if p i then 1 else -1 := by
  rw [signedDiagonal_shift, posSemidef_diagonal_iff]

omit [Fintype ι] in
/-- Above `1`, every shifted diagonal entry is strictly positive. -/
theorem signedDiagonal_shift_posDef (p : ι → Bool) {lambda : ℝ} (hlambda : 1 < lambda) :
    (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ)).PosDef := by
  rw [signedDiagonal_shift, posDef_diagonal_iff]
  intro i
  cases p i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

omit [Fintype ι] in
/-- At the singular shift `1`, the shifted matrix remains positive semidefinite. -/
theorem signedDiagonal_shift_one_posSemidef (p : ι → Bool) :
    (signedDiagonal p + (1 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  rw [signedDiagonal_shift_posSemidef_iff]
  intro i
  cases p i <;> norm_num

/-- Explicit nonsingular shifted step. The denominators are retained at singular shifts. -/
noncomputable def signedDiagonalStep (p : ι → Bool) (g : EuclideanSpace ℝ ι) (lambda : ℝ) :
    EuclideanSpace ℝ ι :=
  (-(lambda + 1)⁻¹) • signComponent p true g + (-(lambda - 1)⁻¹) • signComponent p false g

omit [Fintype ι] [DecidableEq ι] in
/-- Each coordinate of the explicit step is the scalar shifted solution. -/
@[simp] theorem signedDiagonalStep_apply (p : ι → Bool) (g : EuclideanSpace ℝ ι)
    (lambda : ℝ) (i : ι) :
    signedDiagonalStep p g lambda i = -g i / (lambda + if p i then 1 else -1) := by
  cases h : p i <;> simp [signedDiagonalStep, h, div_eq_mul_inv, sub_eq_add_neg,
    mul_comm]

/-- Away from both possible eigenvalue poles, the explicit step solves the actual system. -/
theorem signedDiagonalStep_stationary (p : ι → Bool) (g : EuclideanSpace ℝ ι)
    {lambda : ℝ} (hplus : lambda + 1 ≠ 0) (hminus : lambda - 1 ≠ 0) :
    toEuclideanLin (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ))
      (signedDiagonalStep p g lambda) = -g := by
  ext i
  rw [signedDiagonal_shift_apply, signedDiagonalStep_apply]
  cases p i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have : lambda + -1 ≠ 0 := by simpa [sub_eq_add_neg] using hminus
    field_simp
    rfl
  · field_simp
    rfl

/-- Nonsingular stationarity determines the step uniquely. -/
theorem signedDiagonal_stationary_iff (p : ι → Bool) (g s : EuclideanSpace ℝ ι)
    {lambda : ℝ} (hplus : lambda + 1 ≠ 0) (hminus : lambda - 1 ≠ 0) :
    toEuclideanLin (signedDiagonal p + lambda • (1 : Matrix ι ι ℝ)) s = -g ↔
      s = signedDiagonalStep p g lambda := by
  constructor
  · intro hs
    ext i
    have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) hs
    rw [signedDiagonal_shift_apply] at hi
    rw [signedDiagonalStep_apply]
    cases h : p i <;> simp only [h, Bool.false_eq_true, ↓reduceIte, PiLp.neg_apply] at *
    · apply (eq_div_iff (show lambda + -1 ≠ 0 by simpa [sub_eq_add_neg] using hminus)).mpr
      simpa only [mul_comm] using hi
    · apply (eq_div_iff hplus).mpr
      simpa only [mul_comm] using hi
  · rintro rfl
    exact signedDiagonalStep_stationary p g hplus hminus

omit [DecidableEq ι] in
/-- Squared norms split over the two orthogonal coordinate components. -/
theorem norm_sq_signComponent (p : ι → Bool) (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ‖signComponent p true x‖ ^ 2 + ‖signComponent p false x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i <;> simp [h]

omit [DecidableEq ι] in
/-- The explicit step has the signed secular norm formula, even with an empty sign space. -/
theorem norm_sq_signedDiagonalStep (p : ι → Bool) (g : EuclideanSpace ℝ ι) (lambda : ℝ) :
    ‖signedDiagonalStep p g lambda‖ ^ 2 =
      ‖signComponent p true g‖ ^ 2 / (lambda + 1) ^ 2 +
        ‖signComponent p false g‖ ^ 2 / (lambda - 1) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i <;> simp [h, div_pow, sub_eq_add_neg]

/-- All singular-shift solutions consist of the fixed positive component and a free negative one. -/
theorem signedDiagonal_stationary_one_iff (p : ι → Bool) (g s : EuclideanSpace ℝ ι) :
    toEuclideanLin (signedDiagonal p + (1 : ℝ) • (1 : Matrix ι ι ℝ)) s = -g ↔
      signComponent p false g = 0 ∧ signComponent p true s = (- (2 : ℝ)⁻¹) •
        signComponent p true g := by
  constructor
  · intro hs
    constructor
    · ext i
      have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) hs
      rw [signedDiagonal_shift_apply] at hi
      cases h : p i <;> simp [h] at *
      linarith
    · ext i
      have hi := congrArg (fun x : EuclideanSpace ℝ ι => x i) hs
      rw [signedDiagonal_shift_apply] at hi
      cases h : p i <;> simp [h] at *
      linarith
  · rintro ⟨hg, hs⟩
    ext i
    rw [signedDiagonal_shift_apply]
    have hgi := congrArg (fun x : EuclideanSpace ℝ ι => x i) hg
    have hsi := congrArg (fun x : EuclideanSpace ℝ ι => x i) hs
    cases h : p i <;> simp [h] at * <;> linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The zero vector has zero component on either sign space. -/
@[simp] theorem signComponent_zero (p : ι → Bool) (b : Bool) :
    signComponent p b (0 : EuclideanSpace ℝ ι) = 0 := by
  ext i
  simp

/-- A singular-shift step has a fixed positive component and an arbitrary negative component. -/
noncomputable def signedDiagonalHardStep (p : ι → Bool) (g z : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := (-(2 : ℝ)⁻¹) • signComponent p true g + signComponent p false z

omit [Fintype ι] [DecidableEq ι] in
/-- The fixed positive component of a hard step. -/
@[simp] theorem signComponent_true_hardStep (p : ι → Bool) (g z : EuclideanSpace ℝ ι) :
    signComponent p true (signedDiagonalHardStep p g z) =
      (-(2 : ℝ)⁻¹) • signComponent p true g := by
  simp only [signedDiagonalHardStep, signComponent_add_map, signComponent_smul,
    signComponent_component, Bool.true_eq_false, ite_false, ite_true, add_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- The free negative component of a hard step. -/
@[simp] theorem signComponent_false_hardStep (p : ι → Bool) (g z : EuclideanSpace ℝ ι) :
    signComponent p false (signedDiagonalHardStep p g z) = signComponent p false z := by
  simp only [signedDiagonalHardStep, signComponent_add_map, signComponent_smul,
    signComponent_component, Bool.false_eq_true, ite_false, ite_true, smul_zero, zero_add]

omit [DecidableEq ι] in
/-- The squared norm formula at the singular shift includes the subtracted positive contribution. -/
theorem norm_sq_signedDiagonalHardStep (p : ι → Bool) (g z : EuclideanSpace ℝ ι) :
    ‖signedDiagonalHardStep p g z‖ ^ 2 =
      ‖signComponent p true g‖ ^ 2 / 4 + ‖signComponent p false z‖ ^ 2 := by
  rw [norm_sq_signComponent p, signComponent_true_hardStep, signComponent_false_hardStep,
    norm_smul, Real.norm_eq_abs]
  norm_num
  ring

/-- The hard step solves the actual shifted system precisely when the negative gradient is zero. -/
theorem signedDiagonalHardStep_stationary_iff (p : ι → Bool) (g z : EuclideanSpace ℝ ι) :
    toEuclideanLin (signedDiagonal p + (1 : ℝ) • (1 : Matrix ι ι ℝ))
      (signedDiagonalHardStep p g z) = -g ↔ signComponent p false g = 0 := by
  rw [signedDiagonal_stationary_one_iff, signComponent_true_hardStep]
  simp

end Matrix
