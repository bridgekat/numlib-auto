import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.Data.Matrix.Mul
import Numlib.Analysis.Normed.Lp.PiLp
import Numlib.Analysis.Normed.Lp.EuclideanOrder

/-!
# Principal solutions of Stieltjes systems

Extending the solution of a principal system by zero gives a subsolution of the full
system with nonnegative forcing. The discrete maximum principle then gives entrywise
and Euclidean norm comparisons. No sparsity or irreducibility assumption is needed.
-/

noncomputable section
open scoped Matrix
namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The discrete comparison principle, stated for two actual solutions. -/
theorem IsMMatrix.le_of_mulVec_le [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsMMatrix)
    {x y : n → ℝ} (hxy : A *ᵥ x ≤ A *ᵥ y) : x ≤ y := by
  classical
  have h : 0 ≤ A *ᵥ (y - x) := by
    rw [mulVec_sub]
    exact sub_nonneg.mpr hxy
  exact sub_nonneg.mp (hA.nonneg_of_mulVec_nonneg h)

omit [Fintype n] in
/-- A principal system with nonnegative forcing has a nonnegative solution. -/
theorem IsStieltjes.principal_solution_nonneg {A : Matrix n n ℝ}
    (hA : A.IsStieltjes) {e : m → n} (he : Function.Injective e)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ}
    (hx : A.submatrix e e *ᵥ x = b ∘ e) : 0 ≤ x := by
  classical
  apply (hA.submatrix he).isMMatrix.nonneg_of_mulVec_nonneg
  rw [hx]
  exact fun i => hb (e i)

/-- A nonnegative principal subsolution extended by zero is below the full solution.
Outside the principal index set, the Z-matrix sign makes its residual nonpositive. -/
theorem IsMMatrix.extend_principal_subsolution_le [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsMMatrix) {e : m → n} (he : Function.Injective e)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ} (hxnonneg : 0 ≤ x)
    (hx : A.submatrix e e *ᵥ x ≤ b ∘ e) (hy : A *ᵥ y = b) :
    Function.extend e x 0 ≤ y := by
  classical
  apply hA.le_of_mulVec_le
  rw [hy]
  intro i
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    have h := hx j
    rw [submatrix_mulVec_eq_comp_mulVec_extend A e he] at h
    exact h
  · apply le_trans ?_ (hb i)
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : ∃ k, e k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [he.extend_apply]
      exact mul_nonpos_of_nonpos_of_nonneg
        (hA.offDiag_nonpos i (e k) (fun h => hi ⟨k, h.symm⟩)) (hxnonneg k)
    · rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply, mul_zero]

/-- A nonnegative principal solution extended by zero is a subsolution of the full system.
The comparison applies to every principal submatrix, without any tridiagonal assumption. -/
theorem IsStieltjes.extend_principal_solution_le {A : Matrix n n ℝ}
    (hA : A.IsStieltjes) {e : m → n} (he : Function.Injective e)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ}
    (hx : A.submatrix e e *ᵥ x = b ∘ e) (hy : A *ᵥ y = b) :
    Function.extend e x 0 ≤ y := by
  classical
  exact hA.isMMatrix.extend_principal_subsolution_le he hb
    (hA.principal_solution_nonneg he hb hx) hx.le hy

/-- Principal-system comparison also bounds the Euclidean norm, including empty systems. -/
theorem IsStieltjes.norm_principal_solution_le {A : Matrix n n ℝ}
    (hA : A.IsStieltjes) {e : m → n} (he : Function.Injective e)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ}
    (hx : A.submatrix e e *ᵥ x = b ∘ e) (hy : A *ᵥ y = b) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ ≤
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ := by
  classical
  have hle := hA.extend_principal_solution_le he hb hx hy
  have hxnonneg := hA.principal_solution_nonneg he hb hx
  have hextnonneg : 0 ≤ Function.extend e x 0 := by
    intro i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [he.extend_apply]
      exact hxnonneg j
    · rw [Function.extend_apply' _ _ _ hi]
  rw [← PiLp.norm_toLp_extend 2 he x]
  apply PiLp.norm_le_norm_of_forall_norm_le
  intro i
  exact abs_le_abs_of_nonneg (hextnonneg i) (hle i)

/-- Increasing the diagonal shift on a principal system decreases its nonnegative solution
relative to the full system. The matrices need only be Stieltjes at their actual shifts. -/
theorem IsStieltjes.extend_principal_shift_solution_le [DecidableEq m] [DecidableEq n]
    {A : Matrix n n ℝ}
    {tau sigma : ℝ} (hA : (A + tau • 1).IsStieltjes)
    {e : m → n} (he : Function.Injective e)
    (hsmall : (A.submatrix e e + sigma • 1).IsStieltjes) (hshift : tau ≤ sigma)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ}
    (hx : (A.submatrix e e + sigma • 1) *ᵥ x = b ∘ e)
    (hy : (A + tau • 1) *ᵥ y = b) : Function.extend e x 0 ≤ y := by
  classical
  have hxnonneg : 0 ≤ x := hsmall.isMMatrix.nonneg_of_mulVec_nonneg
    (by rw [hx]; exact fun i => hb (e i))
  apply hA.isMMatrix.extend_principal_subsolution_le he hb hxnonneg ?_ hy
  change (A.submatrix e e + tau • (1 : Matrix n n ℝ).submatrix e e) *ᵥ x ≤ _
  rw [submatrix_one e he]
  simp only [add_mulVec, smul_mulVec, one_mulVec] at hx ⊢
  intro i
  have hi := congrFun hx i
  have hmul := mul_le_mul_of_nonneg_right hshift (hxnonneg i)
  change (A.submatrix e e *ᵥ x) i + tau * x i ≤ b (e i)
  change (A.submatrix e e *ᵥ x) i + sigma * x i = b (e i) at hi
  linarith

/-- Ordered principal shifts give the corresponding Euclidean norm comparison. -/
theorem IsStieltjes.norm_principal_shift_solution_le [DecidableEq m] [DecidableEq n]
    {A : Matrix n n ℝ} {tau sigma : ℝ} (hA : (A + tau • 1).IsStieltjes)
    {e : m → n} (he : Function.Injective e)
    (hsmall : (A.submatrix e e + sigma • 1).IsStieltjes) (hshift : tau ≤ sigma)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ}
    (hx : (A.submatrix e e + sigma • 1) *ᵥ x = b ∘ e)
    (hy : (A + tau • 1) *ᵥ y = b) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ ≤
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ := by
  classical
  have hle := hA.extend_principal_shift_solution_le he hsmall hshift hb hx hy
  have hxnonneg : 0 ≤ x := hsmall.isMMatrix.nonneg_of_mulVec_nonneg
    (by rw [hx]; exact fun i => hb (e i))
  apply le_trans ?_ (PiLp.norm_toLp_comp_le 2 he y)
  apply PiLp.norm_le_norm_of_forall_norm_le
  intro i
  have hi := hle (e i)
  rw [he.extend_apply] at hi
  exact abs_le_abs_of_nonneg (hxnonneg i) hi

/-- Strict shift comparison gives strict norm growth for a nonzero principal solution. -/
theorem IsStieltjes.norm_principal_shift_solution_lt [DecidableEq m] [DecidableEq n]
    {A : Matrix n n ℝ} {tau sigma : ℝ} (hA : (A + tau • 1).IsStieltjes)
    {e : m → n} (he : Function.Injective e)
    (hsmall : (A.submatrix e e + sigma • 1).IsStieltjes) (hshift : tau < sigma)
    {b : n → ℝ} (hb : 0 ≤ b) {x : m → ℝ} {y : n → ℝ} (hxne : x ≠ 0)
    (hx : (A.submatrix e e + sigma • 1) *ᵥ x = b ∘ e)
    (hy : (A + tau • 1) *ᵥ y = b) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ m)‖ <
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ := by
  classical
  have hle := hA.extend_principal_shift_solution_le he hsmall hshift.le hb hx hy
  have hxnonneg : 0 ≤ x := hsmall.isMMatrix.nonneg_of_mulVec_nonneg
    (by rw [hx]; exact fun i => hb (e i))
  have hextnonneg : ∀ i, 0 ≤ Function.extend e x 0 i := by
    intro i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [he.extend_apply]
      exact hxnonneg j
    · rw [Function.extend_apply' _ _ _ hi]
      exact le_rfl
  have hnormle := hA.norm_principal_shift_solution_le he hsmall hshift.le hb hx hy
  by_contra h
  have heqnorm := le_antisymm hnormle (not_lt.mp h)
  have hextnorm : ‖(WithLp.toLp 2 (Function.extend e x 0) : EuclideanSpace ℝ n)‖ =
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ :=
    (PiLp.norm_toLp_extend 2 he x).trans heqnorm
  have heq := EuclideanSpace.eq_of_nonneg_of_le_of_norm_eq
    (x := WithLp.toLp 2 (Function.extend e x 0))
    (y := WithLp.toLp 2 y) hextnonneg hle hextnorm
  have hxy : Function.extend e x 0 = y := congrArg WithLp.ofLp heq
  have hsub : (A + tau • 1).submatrix e e *ᵥ x = b ∘ e := by
    rw [submatrix_mulVec_eq_comp_mulVec_extend _ e he, hxy, hy]
  change (A.submatrix e e + tau • (1 : Matrix n n ℝ).submatrix e e) *ᵥ x = _ at hsub
  rw [submatrix_one e he] at hsub
  simp only [add_mulVec, smul_mulVec, one_mulVec] at hx hsub
  apply hxne
  ext i
  have hs := congrFun hx i
  have ht := congrFun hsub i
  change (A.submatrix e e *ᵥ x) i + sigma * x i = b (e i) at hs
  change (A.submatrix e e *ᵥ x) i + tau * x i = b (e i) at ht
  have hp : (sigma - tau) * x i = 0 := by linarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_pos.mpr hshift).ne'

end Matrix
