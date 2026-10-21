import NumlibSurface.CartisGouldToint.Chapter10.Section02
import Numlib.Direct.TridiagonalLDLSolve
import Numlib.Optimization.KrylovSecular

/-!
# Algorithms 10.2.1 and 10.2.2

The source algorithms specialize a certified scalar LDL runtime to the actual shifted
Lanczos tridiagonal. Factorization failure identifies a genuine nonpositive pivot,
and the successful three-sweep solve uses the cached reciprocal pivots. Arithmetic
counts follow the primitives executed by these runtimes.
-/

noncomputable section
open ArithmeticTrace
open scoped Matrix
open Matrix.TridiagonalLDL
open CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter10.Section02
variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

/-- The subdiagonal of the actual Lanczos matrix, indexed by its row.
The dummy zero-th value is unused by factorization and substitution. -/
def lanczosSubdiagonal (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if i = 0 then 0 else
    Lanczos.beta (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) (i - 1)

/-- The scalar runtime input is exactly the actual shifted Lanczos tridiagonal. -/
theorem shiftedLanczos_eq (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (k : ℕ) :
    matrix (fun i => Lanczos.alpha (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) i + lambda)
        (lanczosSubdiagonal H hM g) k =
      Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
          lambda • 1 := by
  ext i j
  simp only [matrix, Matrix.tridiagonalOfNat, Matrix.of_apply, Lanczos.tridiag_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, lanczosSubdiagonal]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [hij, hv, ite_false, mul_zero, add_zero]
    split_ifs <;> simp_all
    all_goals try omega
    all_goals congr 1
    all_goals omega

/-- Algorithm 10.2.1: the actual scalar shifted-Lanczos LDL recurrence, with cached
reciprocal pivots, positivity tests, first-failure index, and an explicit arithmetic trace.
The empty matrix succeeds without arithmetic. -/
def algorithm_10_2_1 (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) (k : ℕ) :
    ArithmeticTrace.Computation (Except ℕ Factors) :=
  factor (Lanczos.alpha (secularHessian H hM)
    (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
      (lanczosSubdiagonal H hM g) lambda k

/-- A successful source runtime returns an exact LDL factorization with positive
`D_ii = 1/r_i`. -/
theorem algorithm_10_2_1_success (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) {k : ℕ} {s : Factors}
    (h : (algorithm_10_2_1 H hM g lambda k).value = .ok s) :
    Matrix.IsLDM
      (Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
          lambda • 1) (s.lower k) (s.diagonal k) (s.lower k) ∧
      ∀ i, 0 < s.diagonal k i i := by
  rw [← shiftedLanczos_eq]
  exact factor_success_isLDM _ _ _ h

/-- A source runtime failure certifies that the actual shifted Lanczos matrix is not SPD. -/
theorem algorithm_10_2_1_failure (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) {k i : ℕ}
    (h : (algorithm_10_2_1 H hM g lambda k).value = .error i) :
    ¬(Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
        lambda • 1).PosDef := by
  rw [← shiftedLanczos_eq]
  exact factor_error_not_posDef _ _ _ h

/-- Algorithm 10.2.1 costs exactly `k` additions and divisions, `k-1` subtractions,
and `2(k-1)` multiplications on success. -/
theorem algorithm_10_2_1_counts (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) {k : ℕ} {s : Factors}
    (h : (algorithm_10_2_1 H hM g lambda k).value = .ok s) :
    (algorithm_10_2_1 H hM g lambda k).count .add = k ∧
      (algorithm_10_2_1 H hM g lambda k).count .div = k ∧
      (algorithm_10_2_1 H hM g lambda k).count .sub = k - 1 ∧
      (algorithm_10_2_1 H hM g lambda k).count .mul = 2 * (k - 1) :=
  factor_counts _ _ _ h

/-- Extend a finite right-hand side by zero for the scalar sweep storage. -/
def extendRHS {k : ℕ} (b : Fin k → ℝ) (i : ℕ) : ℝ :=
  if hi : i < k then b ⟨i, hi⟩ else 0

/-- Algorithm 10.2.2: forward substitution, reciprocal-pivot scaling, and backward
substitution using the actual cached factors. The result has exactly `k` coordinates. -/
def algorithm_10_2_2 (s : Factors) {k : ℕ} (b : Fin k → ℝ) :
    ArithmeticTrace.Computation (Fin k → ℝ) := do
  let x ← solve s (extendRHS b) k
  pure fun i => x i

/-- The actual source solve output solves the original shifted Lanczos system. -/
theorem algorithm_10_2_2_correct (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) {k : ℕ} {s : Factors}
    (h : (algorithm_10_2_1 H hM g lambda k).value = .ok s) (b : Fin k → ℝ) :
    (Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
        lambda • 1) *ᵥ (algorithm_10_2_2 s b).value = b := by
  rw [← shiftedLanczos_eq]
  simp only [algorithm_10_2_2, value_bind, value_pure]
  rw [matrix_mulVec_solve _ _ _ h (extendRHS b)]
  funext i
  simp only [extendRHS, i.isLt, ↓reduceDIte]

/-- Algorithm 10.2.2 uses exactly `k+2(k-1)` multiplications and `2(k-1)` subtractions,
with no additions or divisions. For `k≥1` the multiplication count is `3k-2`, hence
also bounded by the printed `3k-1`. -/
theorem algorithm_10_2_2_counts (s : Factors) {k : ℕ} (b : Fin k → ℝ) :
    (algorithm_10_2_2 s b).count .mul = k + 2 * (k - 1) ∧
      (algorithm_10_2_2 s b).count .sub = 2 * (k - 1) ∧
      (algorithm_10_2_2 s b).count .add = 0 ∧ (algorithm_10_2_2 s b).count .div = 0 := by
  simpa only [algorithm_10_2_2, ArithmeticTrace.Computation.count, trace_bind, trace_pure,
    List.append_nil] using solve_counts s (extendRHS b) k

/-- The source's printed multiplication count is a valid upper bound on the actual solve. -/
theorem algorithm_10_2_2_multiplications_le (s : Factors) {k : ℕ} (b : Fin k → ℝ) :
    (algorithm_10_2_2 s b).count .mul ≤ 3 * k - 1 := by
  rw [(algorithm_10_2_2_counts s b).1]
  omega

/-- A successful source factorization certifies positive definiteness as well as
returning the factors. -/
theorem algorithm_10_2_1_posDef (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lambda : ℝ) {k : ℕ} {s : Factors}
    (h : (algorithm_10_2_1 H hM g lambda k).value = .ok s) :
    (Lanczos.tridiag (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
        lambda • 1).PosDef := by
  obtain ⟨ht, hd⟩ := algorithm_10_2_1_success H hM g lambda h
  have ht' : Matrix.IsLDM
      (Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) k +
          lambda • 1) (s.lower k) (s.diagonal k) (s.lower k)ᴴᵀ := by simpa using ht
  exact ht'.posDef_iff.mpr hd

/-- The right-hand side of the actual reduced stationary system is the negative
initial-gradient norm in its first coordinate. -/
def lanczosRightHandSide (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  -(if i = 0 then
    ‖hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)‖ else 0)

/-- The norm of the actual source solve certifies which endpoint to update in a
regularization secular bracket. The reference is an actual reduced global minimizer,
and all exponents greater than two are allowed. -/
theorem algorithm_10_2_2_secular_bracket (H : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g ≠ 0) (lambda : ℝ) {m : ℕ} {s : Factors}
    (hm : m + 1 ≤ Krylov.grade (secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)))
    (h : (algorithm_10_2_1 H hM g lambda (m + 1)).value = .ok s)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hmin : IsMinOn (reducedLanczosModel H hM g m sigma r) Set.univ y) :
    let x : EuclideanSpace ℝ (Fin (m + 1)) :=
      WithLp.toLp 2 (algorithm_10_2_2 s (lanczosRightHandSide hM g m)).value
    (lambda < sigma * ‖x‖ ^ (r - 2) → lambda < reducedRegularizationMultiplier sigma r y) ∧
      (sigma * ‖x‖ ^ (r - 2) < lambda → reducedRegularizationMultiplier sigma r y < lambda) := by
  let x : EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 (algorithm_10_2_2 s (lanczosRightHandSide hM g m)).value
  have hx : ∀ i : Fin (m + 1),
      (Lanczos.tridiag (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
        (m + 1)).mulVec x i + lambda * x i =
          -(if i = 0 then
            ‖hM.isPreconditioner_toEuclideanLin.toEnergy
              (Matrix.toEuclideanLin M⁻¹ g)‖ else 0) := by
    intro i
    have he := congrFun (algorithm_10_2_2_correct H hM g lambda h
      (lanczosRightHandSide hM g m)) i
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, x, WithLp.ofLp_toLp, lanczosRightHandSide] using he
  have hy := reducedRegularizationMultiplier_spec hM hg hm hsigma hr hmin
  exact Optimization.KrylovSubproblem.lanczos_regularization_shift_bracket _ _
    hsigma hr hx hy.1 (algorithm_10_2_1_posDef H hM g lambda h) hy.2

end CartisGouldToint.Chapter10.Section02
