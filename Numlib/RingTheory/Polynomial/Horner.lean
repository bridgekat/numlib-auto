import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots

/-!
# Horner's scheme and synthetic division

Horner's nested evaluation of a polynomial ([quarteroni2000numerical] §6.4.1, (6.25)–(6.26);
[kress1998numerical] §6.3; [higham2002accuracy] §5.1) on the path Mathlib would use: the nested
form `a₀ + x (a₁ + x (a₂ + … ))` is a left fold over Mathlib's coefficient list `coeffList p`
(leading coefficient first), `Polynomial.hornerEval`, and it evaluates the polynomial
(`hornerEval_coeffList`). The intermediate values `bₙ = aₙ`, `bₖ = aₖ + bₖ₊₁ z` of the synthetic
division algorithm are the list `hornerScan`, whose entries are, for `k ≥ 1`, the coefficients of
the quotient `p /ₘ (X - C z)` — Mathlib already has that recurrence as
`Polynomial.coeff_divByMonic_X_sub_C_rec` — and, for `k = 0`, the remainder `p.eval z`
(`hornerScan_coeffList`). Synthetic division itself is `p = (X - z) q + p(z)`
(`eq_X_sub_C_mul_divByMonic_add_C_eval`, Mathlib's `modByMonic_add_div` with
`modByMonic_X_sub_C_eq_C_eval`), and the "associated polynomial" `q(·; z)` of the book *is*
`p /ₘ (X - C z)`: no separate definition.

What Mathlib lacks and this module adds is the evaluation identity `q(z; z) = p'(z)`
(`eval_divByMonic_X_sub_C_self`), the fact that makes the Newton–Horner method
(`NewtonHorner.step`, [quarteroni2000numerical] (6.29)) compute `p'(z)` by a second synthetic
division, and the deflation identity `p.roots = (p /ₘ (X - C r)).roots + {r}` at a root `r`
(`roots_divByMonic_X_sub_C`), which is what the deflation loop of [quarteroni2000numerical] §6.4.1
relies on. Descartes' rule of signs and Cauchy's bound, the localization results quoted with these,
are Mathlib's `Polynomial.roots_countP_pos_le_signVariations` and
`Polynomial.IsRoot.norm_lt_cauchyBound`, with the parity clause of Descartes' rule in
`Numlib/RingTheory/Polynomial/RuleOfSigns`.
-/

open Polynomial

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- **Horner's nested multiplication** over a coefficient list `[aₙ, …, a₀]` (leading coefficient
first, as Mathlib's `coeffList`): `b ← aₙ; b ← aₖ + b z` ([quarteroni2000numerical] (6.25)–(6.26)).
-/
def hornerEval (l : List R) (z : R) : R := l.foldl (fun b a => a + b * z) 0

@[simp]
theorem hornerEval_nil (z : R) : hornerEval ([] : List R) z = 0 := rfl

/-- Starting the fold from `b₀` instead of `0` adds `b₀ z ^ length`. -/
theorem foldl_horner_eq (l : List R) (z b₀ : R) :
    l.foldl (fun b a => a + b * z) b₀ = b₀ * z ^ l.length + hornerEval l z := by
  induction l generalizing b₀ with
  | nil => simp [hornerEval]
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons, hornerEval] at ih ⊢
    rw [ih (a + b₀ * z), ih (a + 0 * z), pow_succ', ← mul_assoc, add_mul, zero_mul, add_zero]
    abel

/-- Horner's scheme on `a :: l`: the head contributes `a z ^ length l`. -/
theorem hornerEval_cons (a : R) (l : List R) (z : R) :
    hornerEval (a :: l) z = a * z ^ l.length + hornerEval l z := by
  rw [hornerEval, List.foldl_cons, foldl_horner_eq]
  simp

/-- Horner's scheme on `l ++ [a]`: one more step `b ← a + b z`. -/
theorem hornerEval_append_singleton (l : List R) (a z : R) :
    hornerEval (l ++ [a]) z = a + hornerEval l z * z := by
  simp [hornerEval, List.foldl_append]

/-- Horner's scheme over the reversed range of coefficients is the polynomial sum. -/
theorem hornerEval_map_reverse_range (c : ℕ → R) (z : R) (n : ℕ) :
    hornerEval (((List.range (n + 1)).reverse.map c)) z =
      ∑ i ∈ Finset.range (n + 1), c i * z ^ i := by
  induction n with
  | zero => simp [hornerEval]
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, hornerEval_cons, ih, Finset.sum_range_succ _ (n + 1), add_comm]
    simp

/-- **Horner's scheme evaluates the polynomial** ([quarteroni2000numerical] (6.25)–(6.26)):
`hornerEval p.coeffList z = p.eval z`. -/
theorem hornerEval_coeffList (p : R[X]) (z : R) : hornerEval p.coeffList z = p.eval z := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, hornerEval_map_reverse_range,
      eval_eq_sum_range]

/-- **The synthetic division scan**: the list `[bₙ, bₙ₋₁, …, b₀]` of all partial values of
Horner's scheme (the output vector `b` of [quarteroni2000numerical] Program 52), i.e. `scanl`
without its initial `0`. -/
def hornerScan (l : List R) (z : R) : List R := (l.scanl (fun b a => a + b * z) 0).tail

/-- The scan has one entry per coefficient. -/
@[simp]
theorem length_hornerScan (l : List R) (z : R) : (hornerScan l z).length = l.length := by
  simp [hornerScan, List.length_tail, List.length_scanl]

/-- The `i`-th entry of the scan is Horner's scheme on the first `i + 1` coefficients. -/
theorem getElem_hornerScan (l : List R) (z : R) {i : ℕ} (h : i < l.length) :
    (hornerScan l z)[i]'(by simpa using h) = hornerEval (l.take (i + 1)) z := by
  simp [hornerScan, List.getElem_tail, List.getElem_scanl, hornerEval]

/-- The last entry of the scan is the value `hornerEval l z` (the book's `b₀ = p(z)`). -/
theorem getLast?_hornerScan (l : List R) (z : R) (hl : l ≠ []) :
    (hornerScan l z).getLast? = some (hornerEval l z) := by
  have hlen : 0 < l.length := List.length_pos_iff.2 hl
  rw [List.getLast?_eq_getElem?, length_hornerScan, List.getElem?_eq_getElem (by simpa using hlen),
    getElem_hornerScan l z (by omega), Nat.sub_add_cancel hlen, List.take_length]

end Semiring

section CommRing

variable {R : Type*} [CommRing R]

/-- **Synthetic division** ([quarteroni2000numerical] §6.4.1, the display after (6.28)):
`p = (X - z) · q + p(z)` with `q = p /ₘ (X - C z)` the book's associated polynomial `q(·; z)`,
whose remainder `b₀` is `p(z)`. Mathlib's `modByMonic_add_div` and
`modByMonic_X_sub_C_eq_C_eval`. -/
theorem eq_X_sub_C_mul_divByMonic_add_C_eval (p : R[X]) (z : R) :
    p = (X - C z) * (p /ₘ (X - C z)) + C (p.eval z) := by
  conv_lhs => rw [← p.modByMonic_add_div (X - C z), modByMonic_X_sub_C_eq_C_eval]
  ring

/-- The constant term of synthetic division: `p(z) = a₀ + z · b₁`, the last step of the
recurrence (6.26) with `b₁ = q.coeff 0`. -/
theorem eval_eq_coeff_zero_add_mul_coeff_divByMonic (p : R[X]) (z : R) :
    p.eval z = p.coeff 0 + z * (p /ₘ (X - C z)).coeff 0 := by
  have h := congrArg (fun q => q.coeff 0) (eq_X_sub_C_mul_divByMonic_add_C_eval p z)
  simp only [coeff_add, mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub,
    neg_mul] at h
  rw [h]
  ring

/-- **`p'(z) = q(z; z)`** ([quarteroni2000numerical] §6.4.2): the derivative at `z` is the value
at `z` of the associated polynomial, because `p' = q + (X - z) q'`. It is the identity that lets
one synthetic division of the quotient deliver the derivative for Newton's method. -/
theorem eval_divByMonic_X_sub_C_self (p : R[X]) (z : R) :
    (p /ₘ (X - C z)).eval z = p.derivative.eval z := by
  have h := congrArg (fun q => q.derivative.eval z) (eq_X_sub_C_mul_divByMonic_add_C_eval p z)
  simp only [derivative_add, derivative_mul, derivative_X_sub_C, derivative_C, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, one_mul] at h
  exact h.symm

/-- The entry `i` of the coefficient list of a nonzero polynomial of degree `n` is the coefficient
of `X ^ (n - i)`. -/
theorem getElem_coeffList {p : R[X]} (hp : p ≠ 0) {i : ℕ} (hi : i < p.natDegree + 1) :
    p.coeffList[i]'(by simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, hi]) =
      p.coeff (p.natDegree - i) := by
  simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp, List.getElem_reverse]

/-- The quotient by `X - C z` of a polynomial of positive degree `n` is nonzero of degree
`n - 1`. -/
theorem natDegree_divByMonic_X_sub_C {p : R[X]} (hp : 0 < p.natDegree) (z : R) :
    p /ₘ (X - C z) ≠ 0 ∧ (p /ₘ (X - C z)).natDegree = p.natDegree - 1 := by
  have hnt : Nontrivial R := ⟨⟨p.leadingCoeff, 0,
    leadingCoeff_ne_zero.2 (ne_zero_of_natDegree_gt hp)⟩⟩
  refine ⟨fun h => ?_, by rw [natDegree_divByMonic _ (monic_X_sub_C z), natDegree_X_sub_C]⟩
  rw [divByMonic_eq_zero_iff (monic_X_sub_C z)] at h
  have := natDegree_lt_natDegree (ne_zero_of_natDegree_gt hp) h
  rw [natDegree_X_sub_C] at this
  omega

/-- The partial Horner values are the quotient's coefficients: for `i < n`,
`hornerEval (take (i + 1) p.coeffList) z = q.coeff (n - 1 - i)` with `q = p /ₘ (X - C z)`.
Induction on `i` through Mathlib's recurrence `coeff_divByMonic_X_sub_C_rec`. -/
theorem hornerEval_take_coeffList (p : R[X]) (z : R) {i : ℕ} (hi : i < p.natDegree) :
    hornerEval (p.coeffList.take (i + 1)) z = (p /ₘ (X - C z)).coeff (p.natDegree - 1 - i) := by
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hi
  obtain ⟨-, hdeg⟩ := natDegree_divByMonic_X_sub_C (Nat.zero_lt_of_lt hi) z
  have hlen : p.coeffList.length = p.natDegree + 1 := by
    simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
  induction i with
  | zero =>
    have hq0 : (p /ₘ (X - C z)).coeff p.natDegree = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      getElem_coeffList hp (by omega), Nat.sub_zero]
    simp only [Option.toList_some]
    rw [hornerEval_cons, coeff_divByMonic_X_sub_C_rec, Nat.sub_zero, Nat.sub_add_cancel hi, hq0]
    simp
  | succ i ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      hornerEval_append_singleton, ih (by omega), getElem_coeffList hp (by omega),
      coeff_divByMonic_X_sub_C_rec (n := p.natDegree - 1 - (i + 1)),
      show p.natDegree - 1 - (i + 1) + 1 = p.natDegree - (i + 1) by omega,
      show p.natDegree - 1 - i = p.natDegree - (i + 1) by omega]
    ring

/-- **The synthetic division algorithm (6.26) computes the quotient and the remainder**
([quarteroni2000numerical] §6.4.1): for `p ≠ 0`, the scan `[bₙ, …, b₀]` of Horner's scheme is the
coefficient list of `q = p /ₘ (X - C z)` followed by `b₀ = p(z)`. For a constant `p` the quotient
is `0` with empty coefficient list, and the scan is `[p(z)]`. -/
theorem hornerScan_coeffList {p : R[X]} (hp : p ≠ 0) (z : R) :
    hornerScan p.coeffList z = (p /ₘ (X - C z)).coeffList ++ [p.eval z] := by
  have hlen : p.coeffList.length = p.natDegree + 1 := by
    simp [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · -- a constant: the quotient is `0`
    have hnt : Nontrivial R := ⟨⟨p.leadingCoeff, 0, leadingCoeff_ne_zero.2 hp⟩⟩
    have hq : p /ₘ (X - C z) = 0 := by
      rw [divByMonic_eq_zero_iff (monic_X_sub_C z), degree_X_sub_C, degree_eq_natDegree hp, h0]
      exact zero_lt_one
    have hc : p.coeff 0 ≠ 0 := fun h => hp (by rw [eq_C_of_natDegree_eq_zero h0, h, C_0])
    rw [hq, coeffList_zero, List.nil_append, eq_C_of_natDegree_eq_zero h0, coeffList_C hc, eval_C]
    simp [hornerScan]
  · obtain ⟨hq0, hqdeg⟩ := natDegree_divByMonic_X_sub_C hpos z
    have hqlen : (p /ₘ (X - C z)).coeffList.length = p.natDegree := by
      rw [coeffList, List.length_map, List.length_reverse, List.length_range,
        withBotSucc_degree_eq_natDegree_add_one hq0, hqdeg]
      omega
    refine List.ext_getElem (by simp [hlen, hqlen]) fun i hi hi' => ?_
    rw [length_hornerScan, hlen] at hi
    rw [getElem_hornerScan _ _ (by omega)]
    rcases lt_or_ge i p.natDegree with hlt | hge
    · rw [List.getElem_append_left (by omega), getElem_coeffList hq0 (by omega), hqdeg,
        hornerEval_take_coeffList p z hlt]
    · obtain rfl : i = p.natDegree := by omega
      rw [List.getElem_append_right (by omega), ← hlen, List.take_length, hornerEval_coeffList]
      simp [hqlen]

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Deflation removes one copy of the root** ([quarteroni2000numerical] §6.4.1): for `p ≠ 0` and
a root `r`, `p.roots = (p /ₘ (X - C r)).roots + {r}`, so the remaining roots of `p`, with
multiplicities, are those of the deflated polynomial `q(·; r)`. -/
theorem roots_divByMonic_X_sub_C {p : R[X]} (hp : p ≠ 0) {r : R} (hr : p.IsRoot r) :
    p.roots = (p /ₘ (X - C r)).roots + {r} := by
  have h := mul_divByMonic_eq_iff_isRoot.2 hr
  conv_lhs => rw [← h]
  rw [roots_mul (h.symm ▸ hp), roots_X_sub_C, add_comm]

end Domain

end Polynomial

namespace NewtonHorner

variable {K : Type*} [Field K]

/-- **The Newton–Horner step** ([quarteroni2000numerical] (6.29)): `z ↦ z - p(z) / q(z; z)`, the
derivative `p'(z) = q(z; z)` supplied by a second synthetic division. Over `ℝ` or `ℂ`; the book
recommends complex arithmetic for complex roots. -/
noncomputable def step (p : K[X]) (z : K) : K := z - p.eval z / (p /ₘ (X - C z)).eval z

/-- The Newton–Horner step is the scalar Newton step `z - p(z) / p'(z)`
(`Polynomial.eval_divByMonic_X_sub_C_self`), so every theorem about Newton's method for the
function `p.eval` applies to it. -/
theorem step_eq (p : K[X]) (z : K) : step p z = z - p.eval z / p.derivative.eval z := by
  rw [step, Polynomial.eval_divByMonic_X_sub_C_self]

end NewtonHorner
