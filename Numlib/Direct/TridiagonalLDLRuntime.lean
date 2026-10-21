import Numlib.Direct.TridiagonalLDL
import Numlib.Computation.ArithmeticTrace
import Mathlib.Tactic

/-!
# Traced scalar tridiagonal LDL recurrence

The factorization program caches reciprocal pivots and lower multipliers. It stops
at its first nonpositive pivot. Correctness and arithmetic counts are proved from
this program, using the existing Thomas recurrence for its mathematical specification.
-/

noncomputable section
open ArithmeticTrace
namespace Matrix.TridiagonalLDL

/-- The reciprocal pivots and lower multipliers cached by the scalar recurrence.
Entries at or beyond the processed prefix have no mathematical significance. -/
structure Factors where
  reciprocal : ℕ → ℝ
  subdiagonal : ℕ → ℝ

/-- Empty factor storage. -/
def Factors.empty : Factors := ⟨fun _ => 0, fun _ => 0⟩

/-- Write one newly computed reciprocal pivot and lower multiplier. -/
def Factors.write (s : Factors) (i : ℕ) (r l : ℝ) : Factors :=
  ⟨Function.update s.reciprocal i r, Function.update s.subdiagonal i l⟩

/-- Execute one factorization row using the cached preceding reciprocal pivot.
The error index is exactly the first nonpositive pivot encountered. -/
def factorRow (rho gamma : ℕ → ℝ) (lambda : ℝ) (i : ℕ) (s : Factors) :
    ArithmeticTrace.Computation (Except ℕ Factors) := do
  let d ← ArithmeticTrace.add (rho i) lambda
  if i = 0 then
    if 0 < d then
      let r ← ArithmeticTrace.div 1 d
      pure (.ok (s.write i r 0))
    else pure (.error i)
  else
    let l ← ArithmeticTrace.mul (gamma i) (s.reciprocal (i - 1))
    let t ← ArithmeticTrace.mul (gamma i) l
    let p ← ArithmeticTrace.sub d t
    if 0 < p then
      let r ← ArithmeticTrace.div 1 p
      pure (.ok (s.write i r l))
    else pure (.error i)

/-- The actual finite scalar LDL recurrence, including its empty-input case. -/
noncomputable def factor (rho gamma : ℕ → ℝ) (lambda : ℝ) :
    ℕ → ArithmeticTrace.Computation (Except ℕ Factors)
  | 0 => pure (.ok Factors.empty)
  | n + 1 => do
    match (← factor rho gamma lambda n) with
    | .error i => pure (.error i)
    | .ok s => factorRow rho gamma lambda n s

/-- The cached reciprocal pivot and multiplier agree with the canonical Thomas values. -/
def Factors.CorrectPrefix (rho gamma : ℕ → ℝ) (lambda : ℝ) (n : ℕ) (s : Factors) : Prop :=
  ∀ i, i < n →
    0 < pivot (fun j => rho j + lambda) gamma i ∧
    s.reciprocal i = (pivot (fun j => rho j + lambda) gamma i)⁻¹ ∧
    s.subdiagonal i = multiplier (fun j => rho j + lambda) gamma i

/-- One row's tested scalar is the actual next Thomas pivot. -/
theorem factorRow_value (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ} {s : Factors}
    (hs : s.CorrectPrefix rho gamma lambda n) :
    (factorRow rho gamma lambda n s).value =
      if 0 < pivot (fun j => rho j + lambda) gamma n then
        .ok (s.write n (pivot (fun j => rho j + lambda) gamma n)⁻¹
          (multiplier (fun j => rho j + lambda) gamma n))
      else .error n := by
  cases n with
  | zero =>
    by_cases hp : 0 < rho 0 + lambda
    · simp only [factorRow, value_bind, ArithmeticTrace.add, ArithmeticTrace.div,
        pivot, multiplier, thomasAlpha_zero, thomasBeta_zero, ↓reduceIte, hp, one_div]
      rfl
    · simp only [factorRow, value_bind, ArithmeticTrace.add, ArithmeticTrace.div,
        pivot, thomasAlpha_zero, ↓reduceIte, hp]
      rfl
  | succ n =>
    have hr := (hs n (by omega)).2.1
    have hp : rho (n + 1) + lambda - gamma (n + 1) * (gamma (n + 1) * s.reciprocal n) =
        pivot (fun j => rho j + lambda) gamma (n + 1) := by
      rw [hr]
      simp only [pivot, thomasAlpha_succ, thomasBeta_succ, div_eq_mul_inv]
      ring
    have hl : gamma (n + 1) * s.reciprocal n =
        multiplier (fun j => rho j + lambda) gamma (n + 1) := by
      rw [hr]
      rfl
    simp only [factorRow, value_bind, ArithmeticTrace.add, ArithmeticTrace.mul,
      ArithmeticTrace.sub, ArithmeticTrace.div, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [hp]
    simp only [hl, one_div]
    split_ifs <;> rfl

/-- Writing a positive pivot extends the proved cached prefix. -/
theorem Factors.CorrectPrefix.write {rho gamma : ℕ → ℝ} {lambda : ℝ} {n : ℕ} {s : Factors}
    (hs : s.CorrectPrefix rho gamma lambda n)
    (hp : 0 < pivot (fun j => rho j + lambda) gamma n) :
    (s.write n (pivot (fun j => rho j + lambda) gamma n)⁻¹
      (multiplier (fun j => rho j + lambda) gamma n)).CorrectPrefix rho gamma lambda (n + 1) := by
  intro i hi
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
  · simpa only [Factors.write, Function.update_of_ne (by omega : i ≠ n)] using hs i hi
  · simp only [Factors.write, Function.update_self]
    exact ⟨hp, trivial, trivial⟩

/-- The runtime result contains either the actual positive factor prefix or an actual
nonpositive pivot; neither alternative assumes output correctness. -/
theorem factor_spec (rho gamma : ℕ → ℝ) (lambda : ℝ) (n : ℕ) :
    match (factor rho gamma lambda n).value with
    | .ok s => s.CorrectPrefix rho gamma lambda n
    | .error i => i < n ∧ pivot (fun j => rho j + lambda) gamma i ≤ 0 := by
  induction n with
  | zero => simp only [factor, value_pure]; intro i hi; omega
  | succ n ih =>
    simp only [factor, value_bind]
    cases he : (factor rho gamma lambda n).value with
    | error i =>
      rw [he] at ih
      simp only [value_pure]
      exact ⟨by omega, ih.2⟩
    | ok s =>
      rw [he] at ih
      rw [factorRow_value rho gamma lambda ih]
      split_ifs with hp
      · exact ih.write hp
      · exact ⟨by omega, le_of_not_gt hp⟩

/-- A runtime failure is a sound certificate that the input is not positive definite. -/
theorem factor_error_not_posDef (rho gamma : ℕ → ℝ) (lambda : ℝ) {n i : ℕ}
    (h : (factor rho gamma lambda n).value = .error i) :
    ¬(matrix (fun j => rho j + lambda) gamma n).PosDef := by
  have hs := factor_spec rho gamma lambda n
  rw [h] at hs
  exact not_posDef_of_pivot_nonpos _ _ hs.1 hs.2

/-- A positive definite input makes the actual runtime succeed. -/
theorem factor_success_of_posDef (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ}
    (hA : (matrix (fun j => rho j + lambda) gamma n).PosDef) :
    ∃ s, (factor rho gamma lambda n).value = .ok s := by
  cases he : (factor rho gamma lambda n).value with
  | ok s => exact ⟨s, rfl⟩
  | error i => exact False.elim ((factor_error_not_posDef rho gamma lambda he) hA)

/-- The lower bidiagonal factor stored by a successful runtime. -/
def Factors.lower (s : Factors) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerBidiagonalOf s.subdiagonal n

/-- The diagonal factor stored as reciprocal pivots by the runtime. -/
def Factors.diagonal (s : Factors) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => 1 / s.reciprocal i

/-- Successful output is an exact LDL factorization with positive diagonal pivots. -/
theorem factor_success_isLDM (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ} {s : Factors}
    (h : (factor rho gamma lambda n).value = .ok s) :
    IsLDM (matrix (fun j => rho j + lambda) gamma n) (s.lower n) (s.diagonal n) (s.lower n) ∧
      ∀ i, 0 < s.diagonal n i i := by
  have hs := factor_spec rho gamma lambda n
  rw [h] at hs
  have hl : s.lower n = lower (fun j => rho j + lambda) gamma n := by
    ext i j
    simp only [Factors.lower, lowerBidiagonalOf, lower, thomasLower, of_apply]
    rw [(hs i i.isLt).2.2]
    rfl
  have hd : s.diagonal n = diagonal (fun j => rho j + lambda) gamma n := by
    apply congrArg Matrix.diagonal
    funext i
    rw [(hs i i.isLt).2.1]
    simp
  rw [hl, hd]
  exact ⟨isLDM _ _ (fun i hi => (hs i (by omega)).1.ne'),
    fun i => by simpa [diagonal] using (hs i i.isLt).1⟩

/-- The operation trace of one successful row is derived from its charged arithmetic primitives. -/
theorem factorRow_trace_of_success (rho gamma : ℕ → ℝ) (lambda : ℝ) (n : ℕ) (s t : Factors)
    (h : (factorRow rho gamma lambda n s).value = .ok t) :
    (factorRow rho gamma lambda n s).trace =
      if n = 0 then [.add, .div] else [.add, .mul, .mul, .sub, .div] := by
  simp only [factorRow, value_bind, trace_bind, ArithmeticTrace.add, ArithmeticTrace.mul,
    ArithmeticTrace.sub, ArithmeticTrace.div] at h ⊢
  split_ifs at h ⊢ <;> simp_all [value_bind, trace_bind]
  split_ifs at h ⊢
  simp_all [value_bind, trace_bind]

/-- The trace charged by a complete successful factorization. -/
def factorTrace (n : ℕ) : List Operation :=
  (List.range n).flatMap fun i =>
    if i = 0 then [.add, .div] else [.add, .mul, .mul, .sub, .div]

/-- The successful runtime trace equals the row-by-row primitive trace, including empty input. -/
theorem factor_trace_of_success (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ} {s : Factors}
    (h : (factor rho gamma lambda n).value = .ok s) :
    (factor rho gamma lambda n).trace = factorTrace n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [factor, value_bind] at h
    simp only [factor, trace_bind]
    cases he : (factor rho gamma lambda n).value with
    | error i => simp [he] at h
    | ok t =>
      simp only [he] at h ⊢
      rw [ih he, factorRow_trace_of_success rho gamma lambda n t s h]
      simp [factorTrace, List.range_succ, List.flatMap_append]

/-- The primitive trace has one addition and division per row, and exactly two
multiplications and one subtraction per row after the first. -/
theorem factorTrace_counts (n : ℕ) :
    (factorTrace n).count .add = n ∧ (factorTrace n).count .div = n ∧
      (factorTrace n).count .sub = n - 1 ∧ (factorTrace n).count .mul = 2 * (n - 1) := by
  induction n with
  | zero => simp [factorTrace]
  | succ n ih =>
    rw [factorTrace, List.range_succ, List.flatMap_append]
    simp only [List.count_append, List.flatMap_singleton]
    change (factorTrace n).count .add + _ = _ ∧ (factorTrace n).count .div + _ = _ ∧
      (factorTrace n).count .sub + _ = _ ∧ (factorTrace n).count .mul + _ = _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      simp [factorTrace] at *
    · simp only [show n ≠ 0 by omega, ↓reduceIte,
        List.count_cons, List.count_nil] at *
      norm_num at *
      omega

/-- Exact successful arithmetic counts in the explicit primitive-operation model. -/
theorem factor_counts (rho gamma : ℕ → ℝ) (lambda : ℝ) {n : ℕ} {s : Factors}
    (h : (factor rho gamma lambda n).value = .ok s) :
    (factor rho gamma lambda n).count .add = n ∧
    (factor rho gamma lambda n).count .div = n ∧
    (factor rho gamma lambda n).count .sub = n - 1 ∧
    (factor rho gamma lambda n).count .mul = 2 * (n - 1) := by
  simp only [ArithmeticTrace.Computation.count, factor_trace_of_success rho gamma lambda h]
  exact factorTrace_counts n

end Matrix.TridiagonalLDL
