import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.SaadSparse.Common

/-!
# Saad §4.1: Jacobi, Gauss–Seidel and SOR

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §4.1: the splitting `A = D - E - F` (4.2), the Jacobi (4.3)–(4.5), Gauss–Seidel (4.6)–(4.9),
SOR (4.11)–(4.12) and SSOR (4.13)–(4.14) iterations, the general splitting form (4.18)–(4.23) and
the preconditioners (4.24)–(4.27).

Every iteration is a `Stationary.Splitting` of the backbone
(`Numlib/LinearSolve/Stationary/Splitting.lean`): the equivalence lemmas `jacobiStep_eq`,
`gsStep_eq`, `backwardGsStep_eq`, `sorStep_eq` and `ssorStep_eq` identify the book's
componentwise or matrix recurrences with `Splitting.step` of the corresponding splitting.

Block relaxation (§4.1.1, Algorithms 4.1–4.2) is deferred: the plan assigns the block
splittings and their identification with the additive projection process to phase 2 of the
backbone (`plans/backbone.md` §2.4.4).
-/

open Matrix Finset Stationary

namespace SaadSparse.Chapter04

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x : Fin n → ℝ} {ω : ℝ}

/-! ### The splitting `A = D - E - F` (4.2) -/

/-- Saad (4.2): the diagonal part `D` of `A`. -/
def D (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := diagPart A

/-- Saad (4.2): `-E` is the strict lower triangular part of `A`. -/
def E (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictLower A

/-- Saad (4.2): `-F` is the strict upper triangular part of `A`. -/
def F (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := -strictUpper A

/-- Saad (4.2): `A = D - E - F`. -/
theorem decomp (A : Matrix (Fin n) (Fin n) ℝ) : A = D A - E A - F A :=
  (diagPart_sub_neg_strictLower_sub_neg_strictUpper A).symm

theorem D_sub_E (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = diagPart A + strictLower A := by
  rw [D, E, sub_neg_eq_add]

theorem D_sub_F (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = diagPart A + strictUpper A := by
  rw [D, F, sub_neg_eq_add]

theorem isUnit_D_sub_E (h : IsUnit (diagPart A)) : IsUnit (D A - E A) := by
  rw [D_sub_E]; exact isUnit_diagPart_add_strictLower h

theorem isUnit_D_sub_F (h : IsUnit (diagPart A)) : IsUnit (D A - F A) := by
  rw [D_sub_F]; exact isUnit_diagPart_add_strictUpper h

/-- `E + F = D - A`. -/
theorem E_add_F (A : Matrix (Fin n) (Fin n) ℝ) : E A + F A = D A - A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-- `D - E = A + F`. -/
theorem D_sub_E_eq (A : Matrix (Fin n) (Fin n) ℝ) : D A - E A = A + F A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-- `D - F = A + E`. -/
theorem D_sub_F_eq (A : Matrix (Fin n) (Fin n) ℝ) : D A - F A = A + E A := by
  ext i j
  rcases lt_trichotomy i j with hlt | rfl | hlt
  · simp [E, F, D, hlt, hlt.ne, asymm hlt]
  · simp [E, F, D]
  · simp [E, F, D, hlt, hlt.ne', asymm hlt]

/-! ### Componentwise formulas for the matrix-vector products -/

@[simp]
theorem D_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (D A *ᵥ y) i = A i i * y i := by
  simp [D, mulVec, dotProduct, ite_mul]

theorem E_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (E A *ᵥ y) i = -∑ j ∈ univ.filter (· < i), A i j * y j := by
  simp [E, mulVec, dotProduct, ite_mul, Finset.sum_filter]

theorem F_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (F A *ᵥ y) i = -∑ j ∈ univ.filter (i < ·), A i j * y j := by
  simp [F, mulVec, dotProduct, ite_mul, Finset.sum_filter]

theorem mulVec_eq_sum_erase (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ y) i = A i i * y i + ∑ j ∈ univ.erase i, A i j * y j := by
  rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (mem_univ i)]

/-! ### Elementary facts about matrix inverses used throughout -/

private theorem isUnit_smul_of_isUnit {c : ℝ} (hc : c ≠ 0) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUnit M) : IsUnit (c • M) := by
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hc) (isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp hM))

/-- `M⁻¹ (M u) = u` for an invertible `M`. -/
theorem inv_mulVec_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M) (u : Fin n → ℝ) :
    M⁻¹ *ᵥ (M *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

/-- `M (M⁻¹ u) = u` for an invertible `M`. -/
theorem mulVec_inv_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M) (u : Fin n → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M).mp hM), one_mulVec]

/-- Solving `M v = u` for an invertible `M`. -/
theorem inv_mulVec_eq {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M) {u v : Fin n → ℝ}
    (h : M *ᵥ v = u) : M⁻¹ *ᵥ u = v := by rw [← h, inv_mulVec_mulVec hM]

/-! ### General splittings and the affine iteration (4.10)–(4.11), (4.18)–(4.23) -/

/-- Saad §4.2: a splitting `A = M - N` of `A`, given by the nonsingular `M`. -/
abbrev Splitting (A : Matrix (Fin n) (Fin n) ℝ) := Stationary.Splitting A

/-- Saad (4.18)/(4.28): the affine step `x ↦ G x + f`. -/
def affineStep (G : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) : Fin n → ℝ := G *ᵥ x + f

/-- Saad (4.22): the step `x ↦ G x + M⁻¹ b` of a splitting, `G = M⁻¹ N = I - M⁻¹ A`. -/
noncomputable def Splitting.step (s : Splitting A) (b : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  affineStep s.iterationOperator (s.m⁻¹ *ᵥ b)

/-- Saad §4.2: one step of a splitting is `x ↦ x + M⁻¹ r` with `r = b - A x` the residual. -/
theorem Splitting.step_eq (s : Splitting A) (b x : Fin n → ℝ) :
    Splitting.step s b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) := by
  have hG : s.iterationOperator = 1 - s.m⁻¹ * A := by
    rw [Stationary.Splitting.iterationOperator, nonsing_inv_eq_ringInverse]
  rw [Splitting.step, affineStep, hG, sub_mulVec, one_mulVec, mulVec_sub, ← mulVec_mulVec]
  abel

/-- The step of a splitting is characterized by `M (x' - x) = b - A x`. -/
theorem Splitting.step_eq_of_mulVec (s : Splitting A) (b x y : Fin n → ℝ)
    (h : s.m *ᵥ (y - x) = b - A *ᵥ x) : Splitting.step s b x = y := by
  rw [Splitting.step_eq, inv_mulVec_eq s.isUnit h]
  abel

/-- Saad (4.20): the iteration operator of a splitting is `G = I - M⁻¹ A`. -/
theorem iterationOperator_eq_one_sub (s : Splitting A) :
    s.iterationOperator = 1 - s.m⁻¹ * A := by
  rw [Stationary.Splitting.iterationOperator, nonsing_inv_eq_ringInverse]

/-- Saad §4.2.1 (4.29): `x` is a fixed point of the iteration iff it solves `A x = b`. -/
theorem step_fixed_iff (s : Splitting A) (b x : Fin n → ℝ) :
    Splitting.step s b x = x ↔ A *ᵥ x = b := by
  rw [Splitting.step_eq]
  constructor
  · intro h
    have h0 : s.m⁻¹ *ᵥ (b - A *ᵥ x) = 0 := by
      have := congrArg (fun z => z - x) h
      simpa using this
    have := congrArg (fun z => s.m *ᵥ z) h0
    simp only [mulVec_inv_mulVec s.isUnit, mulVec_zero] at this
    have hx := sub_eq_zero.mp this
    exact hx.symm
  · intro h
    rw [h, sub_self, mulVec_zero, add_zero]

/-- Saad §4.1.2: the preconditioned system `M⁻¹ A x = M⁻¹ b` has the same solutions as
`A x = b`. -/
theorem preconditioned_iff {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M)
    (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    M⁻¹ *ᵥ (A *ᵥ x) = M⁻¹ *ᵥ b ↔ A *ᵥ x = b := by
  constructor
  · intro h
    have := congrArg (fun z => M *ᵥ z) h
    simpa only [mulVec_inv_mulVec hM] using this
  · intro h; rw [h]

/-! ### Jacobi (4.3)–(4.5) -/

/-- Saad (4.4): the Jacobi step, which annihilates the `i`-th residual component with all other
components frozen at their previous values. -/
noncomputable def jacobiStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (b i - ∑ j ∈ univ.erase i, A i j * x j) / A i i

/-- Saad (4.3): the Jacobi step is characterized by annihilating the `i`-th residual component,
the other components being frozen. -/
theorem jacobiStep_spec (hd : ∀ i, A i i ≠ 0) (b x : Fin n → ℝ) (i : Fin n) :
    A i i * jacobiStep A b x i + ∑ j ∈ univ.erase i, A i j * x j = b i := by
  rw [jacobiStep, mul_div_cancel₀ _ (hd i)]
  abel

/-- Saad §4.1: the Jacobi step in residual form, `x' = x + D⁻¹ (b - A x)` componentwise. -/
theorem jacobiStep_apply (hd : ∀ i, A i i ≠ 0) (b x : Fin n → ℝ) (i : Fin n) :
    jacobiStep A b x i = x i + (b i - (A *ᵥ x) i) / A i i := by
  have hi : A i i ≠ 0 := hd i
  have key : b i - (A i i * x i + ∑ j ∈ univ.erase i, A i j * x j)
      = (b i - ∑ j ∈ univ.erase i, A i j * x j) - A i i * x i := by ring
  rw [jacobiStep, mulVec_eq_sum_erase, eq_comm, key, sub_div, mul_div_cancel_left₀ _ hi]
  ring

/-- Saad (4.5): the Jacobi iteration is the splitting with `M = D`. -/
theorem jacobiStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    jacobiStep A b = Splitting.step (jacobiSplitting A h) b := by
  have hd := (isUnit_diagPart_iff A).mp h
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (jacobiSplitting A h).m = D A := rfl
  funext i
  have hspec := jacobiStep_spec hd b x i
  have hA := mulVec_eq_sum_erase A x i
  rw [hm]
  simp only [Pi.sub_apply, D_mulVec]
  rw [hA, mul_sub]
  linarith

/-- Saad (4.5): the Jacobi iteration in matrix form, `x' = D⁻¹ (E + F) x + D⁻¹ b`. -/
theorem jacobiStep_eq_vec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    jacobiStep A b x = (D A)⁻¹ *ᵥ ((E A + F A) *ᵥ x) + (D A)⁻¹ *ᵥ b := by
  have hD : IsUnit (D A) := h
  rw [jacobiStep_eq h, Splitting.step_eq]
  have hm : (jacobiSplitting A h).m = D A := rfl
  rw [hm, E_add_F, sub_mulVec, mulVec_sub, mulVec_sub, inv_mulVec_mulVec hD]
  abel

/-! ### Gauss–Seidel (4.6)–(4.9) -/

/-- Saad (4.8): the Gauss–Seidel step `x' = (D - E)⁻¹ (F x + b)`. -/
noncomputable def gsStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - E A)⁻¹ *ᵥ (F A *ᵥ x + b)

/-- Saad (4.9): the backward Gauss–Seidel step `x' = (D - F)⁻¹ (E x + b)`. -/
noncomputable def backwardGsStep (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - F A)⁻¹ *ᵥ (E A *ᵥ x + b)

/-- Saad §4.1: the symmetric Gauss–Seidel step, a forward sweep followed by a backward one. -/
noncomputable def symmetricGsStep (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := backwardGsStep A b ∘ gsStep A b

/-- Saad (4.6): the Gauss–Seidel step solves `(D - E) x' = F x + b`. -/
theorem gsStep_spec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (D A - E A) *ᵥ gsStep A b x = F A *ᵥ x + b :=
  mulVec_inv_mulVec (isUnit_D_sub_E h) _

/-- Saad (4.9): the backward Gauss–Seidel step solves `(D - F) x' = E x + b`. -/
theorem backwardGsStep_spec (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) :
    (D A - F A) *ᵥ backwardGsStep A b x = E A *ᵥ x + b :=
  mulVec_inv_mulVec (isUnit_D_sub_F h) _

/-- Saad (4.7): the componentwise Gauss–Seidel recursion, which uses the already updated
components `j < i`. -/
theorem gsStep_apply (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) (i : Fin n) :
    gsStep A b x i =
      (-(∑ j ∈ univ.filter (· < i), A i j * gsStep A b x j)
        - ∑ j ∈ univ.filter (i < ·), A i j * x j + b i) / A i i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hspec := congrFun (gsStep_spec h b x) i
  rw [sub_mulVec, Pi.sub_apply, D_mulVec, E_mulVec, Pi.add_apply, F_mulVec] at hspec
  rw [eq_div_iff hi]
  linarith

/-- Saad §4.1: the componentwise backward Gauss–Seidel recursion. -/
theorem backwardGsStep_apply (h : IsUnit (diagPart A)) (b x : Fin n → ℝ) (i : Fin n) :
    backwardGsStep A b x i =
      (-(∑ j ∈ univ.filter (i < ·), A i j * backwardGsStep A b x j)
        - ∑ j ∈ univ.filter (· < i), A i j * x j + b i) / A i i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hspec := congrFun (backwardGsStep_spec h b x) i
  rw [sub_mulVec, Pi.sub_apply, D_mulVec, F_mulVec, Pi.add_apply, E_mulVec] at hspec
  rw [eq_div_iff hi]
  linarith

/-- Saad (4.8): Gauss–Seidel is the splitting with `M = D - E`. -/
theorem gsStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    gsStep A b = Splitting.step (gaussSeidelSplitting A h) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (gaussSeidelSplitting A h).m = D A - E A := (D_sub_E A).symm
  rw [hm, mulVec_sub, gsStep_spec h b x, D_sub_E_eq, add_mulVec]
  abel

/-- Saad (4.9): backward Gauss–Seidel is the splitting with `M = D - F`. -/
theorem backwardGsStep_eq (h : IsUnit (diagPart A)) (b : Fin n → ℝ) :
    backwardGsStep A b = Splitting.step (backwardGaussSeidelSplitting A h) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm : (backwardGaussSeidelSplitting A h).m = D A - F A := (D_sub_F A).symm
  rw [hm, mulVec_sub, backwardGsStep_spec h b x, D_sub_F_eq, add_mulVec]
  abel

/-! ### SOR and SSOR (4.11)–(4.14) -/

/-- Saad (4.12): the SOR step with relaxation parameter `ω`. -/
noncomputable def sorStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) : Fin n → ℝ :=
  (D A - ω • E A)⁻¹ *ᵥ ((ω • F A + (1 - ω) • D A) *ᵥ x + ω • b)

/-- Saad §4.1: the backward SOR step. -/
noncomputable def backwardSorStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    Fin n → ℝ :=
  (D A - ω • F A)⁻¹ *ᵥ ((ω • E A + (1 - ω) • D A) *ᵥ x + ω • b)

/-- Saad §4.1: the SSOR step, a forward SOR sweep followed by a backward one. -/
noncomputable def ssorStep (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := backwardSorStep A ω b ∘ sorStep A ω b

/-- Saad (4.11): `ω A = (D - ω E) - (ω F + (1 - ω) D)`. -/
theorem omega_smul_decomp (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    ω • A = (D A - ω • E A) - (ω • F A + (1 - ω) • D A) := by
  conv_lhs => rw [decomp A]
  module

/-- The backward form of Saad (4.11): `ω A = (D - ω F) - (ω E + (1 - ω) D)`. -/
theorem omega_smul_decomp' (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    ω • A = (D A - ω • F A) - (ω • E A + (1 - ω) • D A) := by
  conv_lhs => rw [decomp A]
  module

theorem isUnit_D_sub_smul_E (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    IsUnit (D A - ω • E A) := by
  have hm : D A - ω • E A = ω • (ω⁻¹ • diagPart A + strictLower A) := by
    rw [D, E, smul_neg, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  rw [hm]
  exact isUnit_smul_of_isUnit hω (sorSplitting A h hω).isUnit

theorem isUnit_D_sub_smul_F (h : IsUnit (diagPart A)) (_hω : ω ≠ 0) :
    IsUnit (D A - ω • F A) := by
  have hd := (isUnit_diagPart_iff A).mp h
  have hm : D A - ω • F A = diagPart A + ω • strictUpper A := by
    rw [D, F, smul_neg, sub_neg_eq_add]
  have hut : (diagPart A + ω • strictUpper A).IsUpperTriangular := by
    intro i j hij
    have hji : j < i := hij
    simp [hji.ne', asymm hji]
  rw [hm, isUnit_iff_isUnit_det, det_of_isUpperTriangular hut, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by simpa using hd i

/-- Saad (4.12): the SOR step solves `(D - ω E) x' = [ω F + (1 - ω) D] x + ω b`. -/
theorem sorStep_spec (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • E A) *ᵥ sorStep A ω b x = (ω • F A + (1 - ω) • D A) *ᵥ x + ω • b :=
  mulVec_inv_mulVec (isUnit_D_sub_smul_E h hω) _

/-- Saad §4.1: the backward SOR step solves `(D - ω F) x' = [ω E + (1 - ω) D] x + ω b`. -/
theorem backwardSorStep_spec (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • F A) *ᵥ backwardSorStep A ω b x = (ω • E A + (1 - ω) • D A) *ᵥ x + ω • b :=
  mulVec_inv_mulVec (isUnit_D_sub_smul_F h hω) _

/-- Saad §4.1: SOR with `ω = 1` is Gauss–Seidel. -/
theorem sorStep_one (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    sorStep A 1 b = gsStep A b := by
  funext x
  simp [sorStep, gsStep]

/-- The SOR sweep in residual form: `(D - ω E) (x' - x) = ω (b - A x)`. -/
theorem sorStep_sub (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • E A) *ᵥ (sorStep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have h1 : ω • (b - A *ᵥ x) = ω • b - (ω • A) *ᵥ x := by
    rw [smul_sub, smul_mulVec]
  rw [mulVec_sub, sorStep_spec h hω b x, h1, omega_smul_decomp A ω]
  simp only [sub_mulVec, add_mulVec]
  abel

/-- The backward SOR sweep in residual form. -/
theorem backwardSorStep_sub (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b x : Fin n → ℝ) :
    (D A - ω • F A) *ᵥ (backwardSorStep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have h1 : ω • (b - A *ᵥ x) = ω • b - (ω • A) *ᵥ x := by
    rw [smul_sub, smul_mulVec]
  rw [mulVec_sub, backwardSorStep_spec h hω b x, h1, omega_smul_decomp' A ω]
  simp only [sub_mulVec, add_mulVec]
  abel

/-- Saad (4.12): SOR is the splitting with `M = ω⁻¹ (D - ω E)`. -/
theorem sorStep_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (b : Fin n → ℝ) :
    sorStep A ω b = Splitting.step (sorSplitting A h hω) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  have hm0 : (sorSplitting A h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  have hm : (sorSplitting A h hω).m = ω⁻¹ • (D A - ω • E A) := by
    rw [hm0, D, E, smul_neg, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, smul_mulVec, sorStep_sub h hω b x, smul_smul, inv_mul_cancel₀ hω, one_smul]

/-! ### Preconditioners (4.24)–(4.27) -/

/-- Saad (4.24): `M_JA = D`. -/
theorem M_JA_eq (h : IsUnit (diagPart A)) : (jacobiSplitting A h).m = D A := rfl

/-- Saad (4.25): `M_GS = D - E`. -/
theorem M_GS_eq (h : IsUnit (diagPart A)) : (gaussSeidelSplitting A h).m = D A - E A :=
  (D_sub_E A).symm

/-- Saad (4.26): the SOR preconditioner `M_SOR = ω⁻¹ (D - ω E)`. -/
noncomputable def M_sor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ω⁻¹ • (D A - ω • E A)

theorem M_sor_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    M_sor A ω = (sorSplitting A h hω).m := by
  have hm : (sorSplitting A h hω).m = ω⁻¹ • diagPart A + strictLower A := rfl
  rw [hm, M_sor, D, E, smul_neg, sub_neg_eq_add, smul_add, smul_smul, inv_mul_cancel₀ hω,
    one_smul]

/-- Saad (4.27): the SSOR preconditioner `M_SSOR = (ω(2-ω))⁻¹ (D - ω E) D⁻¹ (D - ω F)`. -/
noncomputable def M_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (ω * (2 - ω))⁻¹ • ((D A - ω • E A) * (D A)⁻¹ * (D A - ω • F A))

theorem M_ssor_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    M_ssor A ω = (ssorSplitting A h hω hω2).m := by
  have hm : (ssorSplitting A h hω hω2).m =
      (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
        (diagPart A + ω • strictUpper A)) := rfl
  rw [hm, M_ssor, D, E, F, smul_neg, smul_neg, sub_neg_eq_add, sub_neg_eq_add]

/-- The key computation behind Saad (4.27): if `y` is the forward SOR sweep from `x` and `z` the
backward SOR sweep from `y`, then `M_SSOR (z - x) = b - A x`. -/
private theorem ssor_key (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (hω2 : ω ≠ 2)
    (b x y z : Fin n → ℝ)
    (hu : (D A - ω • E A) *ᵥ (y - x) = ω • (b - A *ᵥ x))
    (hv : (D A - ω • F A) *ᵥ (z - y) = ω • (b - A *ᵥ y)) :
    M_ssor A ω *ᵥ (z - x) = b - A *ᵥ x := by
  have hD : IsUnit (D A) := h
  have hω2' : (2 : ℝ) - ω ≠ 0 := sub_ne_zero_of_ne (Ne.symm hω2)
  have hv' : (D A - ω • F A) *ᵥ (z - y) = (ω • F A + (1 - ω) • D A) *ᵥ (y - x) := by
    have h2 : ω • (b - A *ᵥ y) = ω • (b - A *ᵥ x) - (ω • A) *ᵥ (y - x) := by
      simp only [smul_mulVec, mulVec_sub, smul_sub]
      abel
    have h3 : (ω • A) *ᵥ (y - x)
        = (D A - ω • E A) *ᵥ (y - x) - (ω • F A + (1 - ω) • D A) *ᵥ (y - x) := by
      rw [omega_smul_decomp A ω]
      simp only [sub_mulVec]
    rw [hv, h2, h3, hu]
    abel
  have hsum : (D A - ω • F A) *ᵥ (z - x) = (2 - ω) • (D A *ᵥ (y - x)) := by
    have hsplit : z - x = (z - y) + (y - x) := by abel
    rw [hsplit, mulVec_add, hv', ← add_mulVec,
      show (ω • F A + (1 - ω) • D A) + (D A - ω • F A) = (2 - ω) • D A by module, smul_mulVec]
  rw [M_ssor, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hsum, mulVec_smul,
    inv_mulVec_mulVec hD, mulVec_smul, hu, smul_smul, smul_smul,
    show (ω * (2 - ω))⁻¹ * (2 - ω) * ω = 1 by field_simp, one_smul]

/-- Saad (4.13)–(4.14), (4.27): the SSOR sweep is the splitting with `M = M_SSOR`. -/
theorem ssorStep_eq (h : IsUnit (diagPart A)) (hω : ω ≠ 0) (hω2 : ω ≠ 2) (b : Fin n → ℝ) :
    ssorStep A ω b = Splitting.step (ssorSplitting A h hω hω2) b := by
  funext x
  refine (Splitting.step_eq_of_mulVec _ b x _ ?_).symm
  rw [← M_ssor_eq h hω hω2]
  exact ssor_key h hω hω2 b x (sorStep A ω b x) (ssorStep A ω b x) (sorStep_sub h hω b x)
    (backwardSorStep_sub h hω b (sorStep A ω b x))

/-! ### The closed form (4.13)–(4.14) of the SSOR iteration -/

/-- Saad (4.13): the SSOR iteration matrix `G_ω`. -/
noncomputable def G_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (D A - ω • F A)⁻¹ * (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹ *
    (ω • F A + (1 - ω) • D A)

/-- Saad (4.14): the SSOR right-hand side `f_ω`. -/
noncomputable def f_ssor (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  ω • ((D A - ω • F A)⁻¹ *ᵥ
    ((1 + (ω • E A + (1 - ω) • D A) * (D A - ω • E A)⁻¹) *ᵥ b))

/-- Saad (4.13)–(4.14): the SSOR sweep is the affine iteration `x ↦ G_ω x + f_ω`. -/
theorem ssorStep_eq_affine (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) (b x : Fin n → ℝ) :
    ssorStep A ω b x = G_ssor A ω *ᵥ x + f_ssor A ω b := by
  simp only [ssorStep, Function.comp_apply, backwardSorStep, sorStep, G_ssor, f_ssor,
    ← mulVec_mulVec, mulVec_add, add_mulVec, one_mulVec, mulVec_smul, smul_add]
  abel

end SaadSparse.Chapter04
