import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The sum of coefficient norms of a polynomial

Mathlib's polynomial sup norm controls the largest coefficient. Here the finite
coefficient sum controls evaluation and differentiation without a support-cardinality
loss at each derivative. The definition uses `Polynomial.sum`.
-/

noncomputable section
open Polynomial Real Finset

namespace Polynomial

variable {R : Type*} [SeminormedRing R]

/-- The sum of the norms of all coefficients of a polynomial. -/
def coeffNorm (p : R[X]) : ℝ := p.sum fun _ a ↦ ‖a‖

/-- Coefficient sums are nonnegative. -/
theorem coeffNorm_nonneg (p : R[X]) : 0 ≤ p.coeffNorm :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- The zero polynomial has coefficient sum zero. -/
@[simp] theorem coeffNorm_zero : (0 : R[X]).coeffNorm = 0 := by simp [coeffNorm]

/-- The coefficient sum of a constant is its norm. -/
@[simp] theorem coeffNorm_C (a : R) : (C a).coeffNorm = ‖a‖ := by simp [coeffNorm]

/-- A degree bound permits computing the coefficient sum over a fixed range. -/
theorem coeffNorm_eq_sum_range (p : R[X]) {n : ℕ} (hn : p.natDegree < n) :
    p.coeffNorm = ∑ i ∈ Finset.range n, ‖p.coeff i‖ :=
  p.sum_over_range' (fun _ ↦ norm_zero) n hn

/-- The unit polynomial has coefficient sum one. -/
@[simp] theorem coeffNorm_one [NormOneClass R] : (1 : R[X]).coeffNorm = 1 := by
  simpa using coeffNorm_C (1 : R)

/-- The coefficient sum satisfies the triangle inequality for subtraction. -/
theorem coeffNorm_sub_le (p q : R[X]) :
    (p - q).coeffNorm ≤ p.coeffNorm + q.coeffNorm := by
  let n := max p.natDegree q.natDegree + 1
  have hp : p.natDegree < n := lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hq : q.natDegree < n := lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  rw [coeffNorm_eq_sum_range _ (lt_of_le_of_lt (natDegree_sub_le _ _) (Nat.lt_succ_self _)),
    coeffNorm_eq_sum_range p hp, coeffNorm_eq_sum_range q hq, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ by
    simpa only [coeff_sub] using norm_sub_le (p.coeff i) (q.coeff i)

/-- Multiplication by a constant scales the coefficient sum by its norm. -/
theorem coeffNorm_C_mul [NormMulClass R] (a : R) (p : R[X]) :
    (C a * p).coeffNorm = ‖a‖ * p.coeffNorm := by
  rw [← smul_eq_C_mul, coeffNorm, sum_smul_index _ _ _ (fun _ ↦ norm_zero)]
  simp [coeffNorm, Polynomial.sum, norm_mul, Finset.mul_sum]

/-- Multiplication by the variable preserves the coefficient sum. -/
@[simp] theorem coeffNorm_X_mul (p : R[X]) : (X * p).coeffNorm = p.coeffNorm := by
  have hd : (X * p).natDegree < p.natDegree + 2 := by
    have h := (natDegree_mul_le (p := (X : R[X])) (q := p))
    have hX := natDegree_X_le (R := R)
    omega
  rw [coeffNorm_eq_sum_range _ hd,
    coeffNorm_eq_sum_range p (Nat.lt_succ_self _), Finset.sum_range_succ']
  simp only [coeff_X_mul_zero, norm_zero, add_zero, coeff_X_mul]

/-- Multiplication by any power of the variable preserves the coefficient sum. -/
@[simp] theorem coeffNorm_X_pow_mul (p : R[X]) (n : ℕ) :
    (X ^ n * p).coeffNorm = p.coeffNorm := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, coeffNorm_X_mul, ih]

/-- Differentiation multiplies the coefficient sum by at most the degree. -/
theorem coeffNorm_derivative_le [NormOneClass R] (p : R[X]) :
    p.derivative.coeffNorm ≤ (p.natDegree : ℝ) * p.coeffNorm := by
  by_cases hp : p.natDegree = 0
  · simp [hp, derivative_of_natDegree_zero hp]
  rw [coeffNorm_eq_sum_range _ (natDegree_derivative_lt hp)]
  calc
    _ ≤ ∑ i ∈ Finset.range p.natDegree, (p.natDegree : ℝ) * ‖p.coeff (i + 1)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [coeff_derivative]
      calc
        _ ≤ ‖p.coeff (i + 1)‖ * ‖(i + 1 : R)‖ := norm_mul_le _ _
        _ ≤ ‖p.coeff (i + 1)‖ * (i + 1 : ℕ) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa using (norm_nsmul_le (n := i + 1) (a := (1 : R)))
        _ ≤ (p.natDegree : ℝ) * ‖p.coeff (i + 1)‖ := by
          have h : (i + 1 : ℝ) ≤ p.natDegree := by
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
          simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
            mul_le_mul_of_nonneg_left h (norm_nonneg (p.coeff (i + 1)))
    _ = (p.natDegree : ℝ) * ∑ i ∈ Finset.range p.natDegree, ‖p.coeff (i + 1)‖ := by
      rw [Finset.mul_sum]
    _ ≤ (p.natDegree : ℝ) * p.coeffNorm := by
      gcongr
      rw [coeffNorm_eq_sum_range _ (Nat.lt_succ_self _), Finset.sum_range_succ']
      exact le_add_of_nonneg_right (norm_nonneg _)

/-- Negating a polynomial preserves the coefficient sum. -/
@[simp] theorem coeffNorm_neg (p : R[X]) : (-p).coeffNorm = p.coeffNorm := by
  rw [coeffNorm_eq_sum_range _ (n := p.natDegree + 1) (by
      simp),
    coeffNorm_eq_sum_range p (Nat.lt_succ_self _)]
  simp only [coeff_neg, norm_neg]

/-- The coefficient sum satisfies the triangle inequality. -/
theorem coeffNorm_add_le (p q : R[X]) :
    (p + q).coeffNorm ≤ p.coeffNorm + q.coeffNorm := by
  simpa using coeffNorm_sub_le p (-q)

/-- The norm of each coefficient is bounded by the coefficient sum. -/
theorem norm_coeff_le_coeffNorm (p : R[X]) (i : ℕ) : ‖p.coeff i‖ ≤ p.coeffNorm := by
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (p.coeff j)) hi
  · simp only [mem_support_iff, not_not] at hi
    rw [hi, norm_zero]
    exact coeffNorm_nonneg p

/-- Coefficient sums are subadditive over finite sums. -/
theorem coeffNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → R[X]) :
    (∑ i ∈ s, f i).coeffNorm ≤ ∑ i ∈ s, (f i).coeffNorm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (coeffNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Constant multiplication is submultiplicative for arbitrary seminormed coefficient rings. -/
theorem coeffNorm_C_mul_le (a : R) (p : R[X]) :
    (C a * p).coeffNorm ≤ ‖a‖ * p.coeffNorm := by
  rw [coeffNorm_eq_sum_range _ (natDegree_C_mul_le _ _ |>.trans_lt (Nat.lt_succ_self _)),
    coeffNorm_eq_sum_range p (Nat.lt_succ_self _), Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ by simpa only [coeff_C_mul] using norm_mul_le a (p.coeff i)

/-- The coefficient sum is submultiplicative. -/
theorem coeffNorm_mul_le (p q : R[X]) :
    (p * q).coeffNorm ≤ p.coeffNorm * q.coeffNorm := by
  calc
    _ = (∑ i ∈ p.support, (C (p.coeff i) * X ^ i) * q).coeffNorm := by
      conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
      rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ p.support, ((C (p.coeff i) * X ^ i) * q).coeffNorm := coeffNorm_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ‖p.coeff i‖ * q.coeffNorm := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc]
      exact (coeffNorm_C_mul_le (p.coeff i) (X ^ i * q)).trans_eq (by
        rw [coeffNorm_X_pow_mul])
    _ = _ := by simp only [coeffNorm, Polynomial.sum, Finset.sum_mul]

/-- The coefficient sum as a bundled ring seminorm. This does not change the polynomial
norm instance. -/
def coeffRingSeminorm (R : Type*) [SeminormedRing R] : RingSeminorm R[X] where
  toFun := coeffNorm
  map_zero' := coeffNorm_zero
  add_le' := coeffNorm_add_le
  neg' := coeffNorm_neg
  mul_le' := coeffNorm_mul_le

/-- Evaluation of the bundled coefficient seminorm is the coefficient sum. -/
@[simp] theorem coeffRingSeminorm_apply (p : R[X]) : coeffRingSeminorm R p = p.coeffNorm := rfl

/-- Over a normed coefficient ring, coefficient sum zero characterizes the zero polynomial. -/
@[simp] theorem coeffNorm_eq_zero_iff {S : Type*} [NormedRing S] (p : S[X]) :
    p.coeffNorm = 0 ↔ p = 0 := by
  refine ⟨fun hp ↦ ?_, fun hp ↦ by simp [hp]⟩
  ext i
  exact norm_eq_zero.mp (le_antisymm (hp ▸ norm_coeff_le_coeffNorm p i) (norm_nonneg _))

/-- The coefficient sum is a bundled ring norm when the coefficient norm separates points. -/
def coeffRingNorm (S : Type*) [NormedRing S] : RingNorm S[X] where
  toRingSeminorm := coeffRingSeminorm S
  eq_zero_of_map_eq_zero' p hp := (coeffNorm_eq_zero_iff p).mp hp

/-- Evaluation of the bundled coefficient norm is the coefficient sum. -/
@[simp] theorem coeffRingNorm_apply {S : Type*} [NormedRing S] (p : S[X]) :
    coeffRingNorm S p = p.coeffNorm := rfl

/-- A coefficient-norm preserving coefficient map preserves the coefficient sum. -/
theorem coeffNorm_map_of_norm_preserving {S : Type*} [SeminormedRing S]
    (f : R →+* S) (hf : ∀ a, ‖f a‖ = ‖a‖) (p : R[X]) :
    (p.map f).coeffNorm = p.coeffNorm := by
  rw [coeffNorm_eq_sum_range _ (natDegree_map_le.trans_lt (Nat.lt_succ_self _)),
    coeffNorm_eq_sum_range p (Nat.lt_succ_self _)]
  simp only [coeff_map, hf]

end Polynomial
