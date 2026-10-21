import Numlib.Direct.TridiagonalLDLRuntime

/-!
# Traced substitution for symmetric tridiagonal factors

The actual solver performs a forward sweep, reciprocal-pivot scaling, and a backward
sweep. Its three arithmetic phases are recorded by the same primitive-operation model
as the factorization runtime.
-/

noncomputable section
open ArithmeticTrace
namespace Matrix.TridiagonalLDL

/-- Forward substitution through a cached unit lower bidiagonal factor. The first
entry is copied, and every later row performs one multiplication and subtraction. -/
noncomputable def forwardSweep (l b : ℕ → ℝ) : ℕ → ArithmeticTrace.Computation (ℕ → ℝ)
  | 0 => pure b
  | n + 1 => do
    let x ← forwardSweep l b n
    if n = 0 then pure x else
      let t ← ArithmeticTrace.mul (l n) (x (n - 1))
      let v ← ArithmeticTrace.sub (b n) t
      pure (Function.update x n v)

/-- Scale every forward-solved coordinate by its cached reciprocal pivot. -/
noncomputable def scaleSweep (r : ℕ → ℝ) : ℕ → (ℕ → ℝ) → ArithmeticTrace.Computation (ℕ → ℝ)
  | 0, x => pure x
  | n + 1, x => do
    let y ← scaleSweep r n x
    let v ← ArithmeticTrace.mul (r n) (y n)
    pure (Function.update y n v)

/-- Descending unit upper bidiagonal substitution, updating entries `j-1,...,0`.
The entry `j` and all later entries remain unchanged. -/
noncomputable def backwardSweep (l : ℕ → ℝ) : ℕ → (ℕ → ℝ) → ArithmeticTrace.Computation (ℕ → ℝ)
  | 0, x => pure x
  | j + 1, x => do
    let t ← ArithmeticTrace.mul (l (j + 1)) (x (j + 1))
    let v ← ArithmeticTrace.sub (x j) t
    backwardSweep l j (Function.update x j v)

/-- The actual three-phase solve using the stored reciprocal pivots and multipliers. -/
def solve (s : Factors) (b : ℕ → ℝ) (n : ℕ) : ArithmeticTrace.Computation (ℕ → ℝ) := do
  let x ← forwardSweep s.subdiagonal b n
  let y ← scaleSweep s.reciprocal n x
  backwardSweep s.subdiagonal (n - 1) y

/-- The exact scalar forward recurrence. -/
noncomputable def forwardValue (l b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | i + 1 => b (i + 1) - l (i + 1) * forwardValue l b i

/-- The forward sweep computes the scalar recurrence on its processed prefix and
leaves every later entry equal to the original input. -/
theorem forwardSweep_spec (l b : ℕ → ℝ) (n : ℕ) :
    (∀ i, i < n → (forwardSweep l b n).value i = forwardValue l b i) ∧
      (∀ i, n ≤ i → (forwardSweep l b n).value i = b i) := by
  induction n with
  | zero => simp [forwardSweep]
  | succ n ih =>
    simp only [forwardSweep, value_bind]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp only [↓reduceIte, value_pure, forwardSweep, value_pure]
      constructor
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        rfl
      · intro i _
        trivial
    · simp only [show n ≠ 0 by omega, ↓reduceIte, ArithmeticTrace.mul,
        ArithmeticTrace.sub, value_bind, value_pure]
      constructor
      · intro i hi
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | he
        · rw [Function.update_of_ne (by omega : i ≠ n)]
          exact ih.1 i hi
        · subst i
          rw [Function.update_self, ih.1 (n - 1) (by omega)]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          rfl
      · intro i hi
        rw [Function.update_of_ne (by omega : i ≠ n)]
        exact ih.2 i (by omega)

/-- Scaling computes the diagonal product on the processed prefix and leaves later
entries unchanged. -/
theorem scaleSweep_spec (r x : ℕ → ℝ) (n : ℕ) :
    (∀ i, i < n → (scaleSweep r n x).value i = r i * x i) ∧
      (∀ i, n ≤ i → (scaleSweep r n x).value i = x i) := by
  induction n with
  | zero => simp [scaleSweep]
  | succ n ih =>
    simp only [scaleSweep, value_bind, ArithmeticTrace.mul, value_pure]
    constructor
    · intro i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | he
      · rw [Function.update_of_ne (by omega : i ≠ n)]
        exact ih.1 i hi
      · subst i
        rw [Function.update_self, ih.2 n le_rfl]
    · intro i hi
      rw [Function.update_of_ne (by omega : i ≠ n)]
      exact ih.2 i (by omega)

/-- The descending sweep satisfies every processed upper bidiagonal equation and
preserves all coordinates from its start index onward. -/
theorem backwardSweep_spec (l : ℕ → ℝ) (j : ℕ) (x : ℕ → ℝ) :
    (∀ i, i < j → (backwardSweep l j x).value i +
      l (i + 1) * (backwardSweep l j x).value (i + 1) = x i) ∧
    (∀ i, j ≤ i → (backwardSweep l j x).value i = x i) := by
  induction j generalizing x with
  | zero => simp [backwardSweep]
  | succ j ih =>
    simp only [backwardSweep, value_bind, ArithmeticTrace.mul, ArithmeticTrace.sub]
    let v := x j - l (j + 1) * x (j + 1)
    let z := Function.update x j v
    have hs := ih z
    constructor
    · intro i hi
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | he
      · rw [hs.1 i hi]
        exact Function.update_of_ne (by omega : i ≠ j) _ _
      · subst i
        rw [hs.2 j le_rfl, hs.2 (j + 1) (by omega)]
        simp only [z, Function.update_self, Function.update_of_ne (by omega : j + 1 ≠ j)]
        dsimp only [v]
        ring
    · intro i hi
      rw [hs.2 i (by omega)]
      exact Function.update_of_ne (by omega : i ≠ j) _ _

/-- A unit lower bidiagonal matrix acts by its two actual row entries. -/
theorem lowerBidiagonalOf_mulVec (l : ℕ → ℝ) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (lowerBidiagonalOf l n *ᵥ x) i =
      x i + if h : 0 < (i : ℕ) then l i * x ⟨i - 1, by omega⟩ else 0 := by
  have h := lowerBidiagonalOf_mul_apply l (Matrix.replicateCol (Fin n) x) i i
  simpa only [← Matrix.replicateCol_mulVec, Matrix.replicateCol_apply] using h

/-- The transpose of a unit lower bidiagonal factor is the corresponding unit
upper bidiagonal factor. -/
theorem transpose_lowerBidiagonalOf (l : ℕ → ℝ) (n : ℕ) :
    (lowerBidiagonalOf l n)ᵀ = tridiagonalOfNat (fun _ => 1) (fun _ => 0)
      (fun i => l (i + 1)) n := by
  ext i j
  simp only [lowerBidiagonalOf, tridiagonalOfNat, transpose_apply, of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | rfl | simp_all

/-- The actual forward sweep solves the cached unit lower bidiagonal system. -/
theorem lower_mulVec_forwardSweep (l b : ℕ → ℝ) (n : ℕ) :
    lowerBidiagonalOf l n *ᵥ (fun i => (forwardSweep l b n).value i) = fun i : Fin n => b i := by
  funext i
  rw [lowerBidiagonalOf_mulVec, (forwardSweep_spec l b n).1 i i.isLt]
  split_ifs with hi
  · rw [(forwardSweep_spec l b n).1 (i - 1) (by omega)]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (i : ℕ) ≠ 0)
    simp only [hj, Nat.succ_sub_one, forwardValue]
    ring
  · have hi0 : (i : ℕ) = 0 := by omega
    simp only [hi0, forwardValue, add_zero]

/-- The actual descending sweep solves the cached transposed lower system. -/
theorem transpose_lower_mulVec_backwardSweep (l z : ℕ → ℝ) (n : ℕ) :
    (lowerBidiagonalOf l n)ᵀ *ᵥ
      (fun i => (backwardSweep l (n - 1) z).value i) = fun i : Fin n => z i := by
  funext i
  rw [transpose_lowerBidiagonalOf, tridiagonalOfNat_mulVec]
  simp only [zero_mul, dite_eq_ite, ite_self, zero_add, one_mul]
  split_ifs with hi
  · exact (backwardSweep_spec l (n - 1) z).1 i (by omega)
  · simp only [add_zero]
    exact (backwardSweep_spec l (n - 1) z).2 i (by omega)

/-- The actual reciprocal scaling solves the cached diagonal system when all
reciprocals are nonzero. -/
theorem diagonal_mulVec_scaleSweep (s : Factors) (z : ℕ → ℝ) (n : ℕ)
    (hr : ∀ i, i < n → s.reciprocal i ≠ 0) :
    s.diagonal n *ᵥ (fun i => (scaleSweep s.reciprocal n z).value i) = fun i : Fin n => z i := by
  funext i
  rw [Factors.diagonal, Matrix.mulVec_diagonal]
  simp only [(scaleSweep_spec s.reciprocal z n).1 i i.isLt]
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ (hr i i.isLt), one_mul]

/-- A successful factorization followed by the actual three-phase runtime solves
the original shifted tridiagonal system. -/
theorem matrix_mulVec_solve (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ} {s : Factors}
    (h : (factor rho gamma lambda n).value = .ok s) (b : ℕ → ℝ) :
    matrix (fun i => rho i + lambda) gamma n *ᵥ (fun i => (solve s b n).value i) =
      fun i : Fin n => b i := by
  have ht := (factor_success_isLDM rho gamma lambda h).1
  have hs := factor_spec rho gamma lambda n
  rw [h] at hs
  have hr : ∀ i, i < n → s.reciprocal i ≠ 0 := by
    intro i hi
    rw [(hs i hi).2.1]
    exact inv_ne_zero (hs i hi).1.ne'
  simp only [solve, value_bind]
  rw [← ht.mul_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change s.lower n *ᵥ s.diagonal n *ᵥ (lowerBidiagonalOf s.subdiagonal n)ᵀ *ᵥ _ = _
  rw [transpose_lower_mulVec_backwardSweep, diagonal_mulVec_scaleSweep s _ n hr]
  exact lower_mulVec_forwardSweep s.subdiagonal b n

/-- The forward sweep performs one multiplication and subtraction per noninitial row. -/
theorem forwardSweep_counts (l b : ℕ → ℝ) (n : ℕ) :
    (forwardSweep l b n).count .mul = n - 1 ∧
      (forwardSweep l b n).count .sub = n - 1 ∧
      (forwardSweep l b n).count .add = 0 ∧ (forwardSweep l b n).count .div = 0 := by
  induction n with
  | zero => simp [forwardSweep, ArithmeticTrace.Computation.count]
  | succ n ih =>
    simp only [ArithmeticTrace.Computation.count, forwardSweep, trace_bind,
      ArithmeticTrace.mul, ArithmeticTrace.sub] at ih ⊢
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp [forwardSweep]
    · simp only [show n ≠ 0 by omega, ↓reduceIte, trace_bind, trace_pure,
        List.count_append, List.count_cons, List.count_nil]
      norm_num at *
      omega

/-- Reciprocal scaling performs exactly one multiplication per row. -/
theorem scaleSweep_counts (r x : ℕ → ℝ) (n : ℕ) :
    (scaleSweep r n x).count .mul = n ∧ (scaleSweep r n x).count .sub = 0 ∧
      (scaleSweep r n x).count .add = 0 ∧ (scaleSweep r n x).count .div = 0 := by
  induction n with
  | zero => simp [scaleSweep, ArithmeticTrace.Computation.count]
  | succ n ih =>
    simp only [ArithmeticTrace.Computation.count, scaleSweep, trace_bind,
      ArithmeticTrace.mul, trace_pure, List.count_append, List.count_cons, List.count_nil] at ih ⊢
    norm_num at *
    omega

/-- Descending substitution performs one multiplication and subtraction per updated row. -/
theorem backwardSweep_counts (l x : ℕ → ℝ) (j : ℕ) :
    (backwardSweep l j x).count .mul = j ∧ (backwardSweep l j x).count .sub = j ∧
      (backwardSweep l j x).count .add = 0 ∧ (backwardSweep l j x).count .div = 0 := by
  induction j generalizing x with
  | zero => simp [backwardSweep, ArithmeticTrace.Computation.count]
  | succ j ih =>
    simp only [ArithmeticTrace.Computation.count, backwardSweep, trace_bind,
      ArithmeticTrace.mul, ArithmeticTrace.sub, List.count_append, List.count_cons, List.count_nil]
    have h := ih (Function.update x j (x j - l (j + 1) * x (j + 1)))
    simp only [ArithmeticTrace.Computation.count] at h
    norm_num at *
    omega

/-- The exact three-phase solve costs `n+2(n-1)` multiplications and `2(n-1)`
subtractions, and no additions or divisions. For nonempty input the first number
is `3n-2`; the empty-input expression is zero as required. -/
theorem solve_counts (s : Factors) (b : ℕ → ℝ) (n : ℕ) :
    (solve s b n).count .mul = n + 2 * (n - 1) ∧
      (solve s b n).count .sub = 2 * (n - 1) ∧
      (solve s b n).count .add = 0 ∧ (solve s b n).count .div = 0 := by
  have hf := forwardSweep_counts s.subdiagonal b n
  have hd := scaleSweep_counts s.reciprocal (forwardSweep s.subdiagonal b n).value n
  have hb := backwardSweep_counts s.subdiagonal
    (scaleSweep s.reciprocal n (forwardSweep s.subdiagonal b n).value).value (n - 1)
  simp only [ArithmeticTrace.Computation.count, solve, trace_bind,
    List.count_append] at *
  omega

end Matrix.TridiagonalLDL
