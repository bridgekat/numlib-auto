import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Numlib.FloatingPoint.System

/-!
# Quarteroni–Sacco–Saleri §2.5: machine representation of numbers

Surface file for [quarteroni2000numerical] §2.5: the positional system (§2.5.1), the floating-point
number system `𝔽(β, t, L, U)` (§2.5.2), its distribution (§2.5.3), the IEC 559 parameters (§2.5.4),
rounding and Property 2.1 (§2.5.5), and the machine operations (§2.5.6).

Everything specializes `Numlib/FloatingPoint/System.lean` to `ℝ` (and to `ℚ` for the two decidable
examples). The book defines `𝔽` by digit strings `(-1)^s β^e ∑_{i=1}^t a_i β^{-i}`; the surface
restates it in that form (`floatingPointNumbers`) and proves it equal to the backbone's
integer-mantissa form `FloatingPoint.System.numbers` (`floatingPointNumbers_eq`), the one
load-bearing equivalence of the file. The rounding (2.32) is restated as the book's digit rule, for
even `β` as the book assumes, and identified with `FloatingPoint.System.round` (`equation_2_32`).
Property 2.1 is stated with the book's range hypothesis, although the backbone bound needs none.
The unnumbered facts the text asserts — the cardinality of `𝔽`, the smallest de-normalized number,
the spacing, `ε_M` as the gap above `1`, the commutativity and the failure of associativity of `⊕`
— are nodes under descriptive names.

Two hypotheses the book leaves implicit are made explicit: `t ≥ 2` for the characterization of
`ε_M` as the gap above `1` (in `𝔽(2, 1, L, 1)` no number of `𝔽` exceeds `1`) and for the smallest
de-normalized number (for `t = 1` there are none), and `β` even for the digit rule (2.32) to be
rounding to nearest.

Skipped: Example 2.10 (a numeral written in two bases), Remark 2.3 (MATLAB `eps`), Remark 2.4 (the
IEC 559 closed arithmetic, NaN, Table 2.3), Tables 2.1–2.2, the flop counts and the round-digit
hardware discussion of §2.5.6.
-/

open Finset FloatingPoint

namespace QuarteroniSaccoSaleri.Chapter02

/-! ### §2.5.1 The positional system -/

/-- **§2.5.1, finite positional expansions are dense**: "any real number can be approximated by
numbers having a finite representation" — for a base `β ≥ 2`, every `x ∈ ℝ` and `ε > 0` there is
`y = m β^(-k)` with finitely many digits and `|y - x| < ε`. -/
theorem positionalDensity {β : ℕ} (hβ : 2 ≤ β) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℤ) (k : ℕ), |m * (β : ℝ) ^ (-(k : ℤ)) - x| < ε :=
  exists_int_mul_zpow_sub_abs_lt hβ x hε

/-! ### §2.5.2 The floating-point number system -/

/-- **§2.5.2, the display defining `𝔽(β, t, L, U)`**: the set `{0} ∪ {x ∈ ℝ : x = (-1)^s β^e
∑_{i=1}^t a_i β^{-i}}` of floating-point numbers with `t` significant digits `0 ≤ a_i ≤ β - 1`,
range `L ≤ e ≤ U`, and the normalization `a₁ ≠ 0`. The digits are a function `a : ℕ → ℕ` of which
only `a 1, …, a t` matter. -/
def floatingPointNumbers (β t : ℕ) (L U : ℤ) : Set ℝ :=
  {0} ∪ {x | ∃ (s : Bool) (e : ℤ) (a : ℕ → ℕ), (∀ i ∈ Icc 1 t, a i ≤ β - 1) ∧ a 1 ≠ 0 ∧
    L ≤ e ∧ e ≤ U ∧
    x = (-1) ^ s.toNat * (β : ℝ) ^ e * ∑ i ∈ Icc 1 t, (a i : ℝ) * (β : ℝ) ^ (-(i : ℤ))}

/-- A digit string of length `t` in base `β` has value below `β^t`. -/
private theorem sum_mul_pow_lt {β t : ℕ} {c : ℕ → ℕ} (hc : ∀ j < t, c j < β) :
    ∑ j ∈ range t, c j * β ^ j < β ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, pow_succ]
    have h1 := ih fun j hj => hc j (by omega)
    have h2 : c t + 1 ≤ β := hc t (by omega)
    nlinarith [Nat.zero_le (β ^ t)]

/-- The base-`β` expansion of `m < β^t`: `m = ∑_{j<t} (m / β^j % β) β^j`. -/
private theorem sum_div_pow_mod_mul_pow {β : ℕ} (hβ : 2 ≤ β) :
    ∀ (t m : ℕ), m < β ^ t → ∑ j ∈ range t, m / β ^ j % β * β ^ j = m := by
  intro t
  induction t with
  | zero => intro m hm; simp at hm; simp [hm]
  | succ t ih =>
    intro m hm
    rw [sum_range_succ']
    have hβ0 : 0 < β := by omega
    have hdiv : m / β < β ^ t := by
      rw [Nat.div_lt_iff_lt_mul hβ0, ← pow_succ]; exact hm
    have h := ih (m / β) hdiv
    have hre : ∑ j ∈ range t, m / β ^ (j + 1) % β * β ^ (j + 1) =
        β * ∑ j ∈ range t, m / β / β ^ j % β * β ^ j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_succ', Nat.div_div_eq_div_mul, mul_comm β (β ^ j)]
      ring
    rw [hre, h]
    simp only [pow_zero, Nat.div_one, mul_one]
    exact Nat.div_add_mod m β

/-- Reindexing a sum over the digit positions `1, …, t` by `i ↦ t - i`. -/
private theorem sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M] (t : ℕ) (g : ℕ → M) :
    ∑ i ∈ Icc 1 t, g i = ∑ j ∈ range t, g (t - j) := by
  refine sum_nbij' (fun i => t - i) (fun j => t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simp only [mem_Icc] at hi; simp only [mem_range]; omega
  · intro j hj; simp only [mem_range] at hj; simp only [mem_Icc]; omega
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro j hj; simp only [mem_range] at hj; omega
  · intro i hi; simp only [mem_Icc] at hi; rw [Nat.sub_sub_self hi.2]

/-- The value of a digit string, in the two forms: `β^e ∑_{i=1}^t a_i β^{-i} = (∑_{i=1}^t a_i
β^{t-i}) β^{e-t}`. -/
private theorem zpow_mul_sum_eq {β t : ℕ} (hβ : 0 < β) (e : ℤ) (a : ℕ → ℕ) :
    (β : ℝ) ^ e * ∑ i ∈ Icc 1 t, (a i : ℝ) * (β : ℝ) ^ (-(i : ℤ)) =
      ((∑ i ∈ Icc 1 t, a i * β ^ (t - i) : ℕ) : ℝ) * (β : ℝ) ^ (e - t) := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ.ne'
  rw [Nat.cast_sum, mul_sum, sum_mul]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_Icc] at hi
  rw [Nat.cast_mul, Nat.cast_pow, ← zpow_natCast, Nat.cast_sub hi.2, mul_left_comm, mul_assoc,
    ← zpow_add₀ hβ', ← zpow_add₀ hβ', show e + -(i : ℤ) = (t : ℤ) - i + (e - t) by ring]

/-- **§2.5.2**: the digit form of `𝔽(β, t, L, U)` is the integer-mantissa form `± m β^(e - t)`,
`β^(t-1) ≤ m ≤ β^t - 1`, of the backbone: `floatingPointNumbers s.β s.t s.L s.U = s.numbers ℝ`. The
mantissa is `m = a₁a₂…a_t = ∑ a_i β^(t-i)`, and every `m` in that range has exactly the base-`β`
digits `a_i = ⌊m / β^(t-i)⌋ mod β`, with `a₁ ≠ 0` because `m ≥ β^(t-1)`. -/
theorem floatingPointNumbers_eq (s : System) :
    floatingPointNumbers s.β s.t s.L s.U = s.numbers ℝ := by
  have hβ := s.β_pos
  have ht := s.one_le_t
  have hpow1 : 1 ≤ s.β ^ s.t := Nat.one_le_pow _ _ hβ
  ext x
  simp only [floatingPointNumbers, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    System.numbers]
  constructor
  · rintro (rfl | ⟨σ, e, a, ha, ha1, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · set m : ℕ := ∑ i ∈ Icc 1 s.t, a i * s.β ^ (s.t - i) with hm
      have hm1 : s.β ^ (s.t - 1) ≤ m := by
        calc s.β ^ (s.t - 1) = 1 * s.β ^ (s.t - 1) := (one_mul _).symm
          _ ≤ a 1 * s.β ^ (s.t - 1) := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.2 ha1)
          _ ≤ m := single_le_sum (f := fun i => a i * s.β ^ (s.t - i)) (fun _ _ => Nat.zero_le _)
              (mem_Icc.2 ⟨le_rfl, ht⟩)
      have hm2 : m ≤ s.β ^ s.t - 1 := by
        have : m < s.β ^ s.t := by
          rw [hm, sum_Icc_eq_sum_range]
          calc ∑ j ∈ range s.t, a (s.t - j) * s.β ^ (s.t - (s.t - j))
              = ∑ j ∈ range s.t, a (s.t - j) * s.β ^ j := by
                refine sum_congr rfl fun j hj => ?_
                rw [mem_range] at hj
                rw [Nat.sub_sub_self hj.le]
            _ < s.β ^ s.t := sum_mul_pow_lt fun j hj => by
                have := ha (s.t - j) (mem_Icc.2 ⟨by omega, by omega⟩)
                omega
        omega
      refine Or.inr ⟨if σ then -1 else 1, m, e, hm1, hm2, hL, hU, ?_⟩
      rw [mul_assoc, zpow_mul_sum_eq hβ, ← hm]
      cases σ <;> simp
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · have hmlt : m < s.β ^ s.t := by omega
      have hdigits : ∑ i ∈ Icc 1 s.t, m / s.β ^ (s.t - i) % s.β * s.β ^ (s.t - i) = m := by
        rw [sum_Icc_eq_sum_range]
        refine Eq.trans ?_ (sum_div_pow_mod_mul_pow s.two_le_β s.t m hmlt)
        refine sum_congr rfl fun j hj => ?_
        rw [mem_range] at hj
        rw [Nat.sub_sub_self hj.le]
      have hval : ((σ : ℤ) : ℝ) * m * (s.β : ℝ) ^ (e - s.t) = ((σ : ℤ) : ℝ) * ((s.β : ℝ) ^ e *
          ∑ i ∈ Icc 1 s.t, ((m / s.β ^ (s.t - i) % s.β : ℕ) : ℝ) * (s.β : ℝ) ^ (-(i : ℤ))) := by
        rw [zpow_mul_sum_eq hβ, hdigits, mul_assoc]
      have hdig : ∀ i ∈ Icc 1 s.t, m / s.β ^ (s.t - i) % s.β ≤ s.β - 1 := fun i _ => by
        have := Nat.mod_lt (m / s.β ^ (s.t - i)) hβ
        omega
      have hd1 : m / s.β ^ (s.t - 1) % s.β ≠ 0 := by
        have hq : m / s.β ^ (s.t - 1) < s.β := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos hβ), ← pow_succ']
          rwa [Nat.sub_add_cancel ht]
        have hq1 : 1 ≤ m / s.β ^ (s.t - 1) := (Nat.one_le_div_iff (Nat.pow_pos hβ)).2 hm1
        rw [Nat.mod_eq_of_lt hq]
        omega
      rcases Int.units_eq_one_or σ with rfl | rfl
      · exact Or.inr ⟨false, e, fun i => m / s.β ^ (s.t - i) % s.β, hdig, hd1, hL, hU,
          by rw [hval]; simp⟩
      · exact Or.inr ⟨true, e, fun i => m / s.β ^ (s.t - i) % s.β, hdig, hd1, hL, hU,
          by rw [hval]; simp⟩

/-- **(2.30)**: every nonzero `x ∈ 𝔽` satisfies
`x_min = β^(L-1) ≤ |x| ≤ β^U (1 - β^(-t)) = x_max`. -/
theorem equation_2_30 (s : System) {x : ℝ} (hx : x ∈ s.numbers ℝ) (h0 : x ≠ 0) :
    (s.β : ℝ) ^ (s.L - 1) ≤ |x| ∧ |x| ≤ (s.β : ℝ) ^ s.U * (1 - (s.β : ℝ) ^ (-(s.t : ℤ))) :=
  ⟨s.xmin_le_abs hx h0, s.abs_le_xmax hx⟩

/-- **§2.5.2, the cardinality of `𝔽`**: `card 𝔽 = 2 (β - 1) β^(t-1) (U - L + 1) + 1`. -/
theorem cardFloatingPoint (s : System) :
    ((s.numbers ℝ).ncard : ℤ)
      = 2 * ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) + 1 := by
  rw [← s.coe_finset, Set.ncard_coe_finset, s.card_finset]

/-- **§2.5.2, the de-normalized numbers `𝔽_D`**: they have mantissa between `1` and `β^(t-1) - 1`
at the exponent `L`, they "belong to the interval `(-β^(L-1), β^(L-1))`", and "the smallest number
in this set has absolute value equal to `β^(L-t)`". The last clause needs `t ≥ 2`: for `t = 1`
there are no de-normalized numbers. -/
theorem denormalizedMin (s : System) (ht : 2 ≤ s.t) :
    IsLeast {x : ℝ | x ∈ s.denormalized ℝ ∧ 0 < x} ((s.β : ℝ) ^ (s.L - s.t)) ∧
      ∀ x ∈ s.denormalized ℝ, x ∈ Set.Ioo (-(s.β : ℝ) ^ (s.L - 1)) ((s.β : ℝ) ^ (s.L - 1)) :=
  ⟨s.isLeast_denormalized ht, fun _ hx => by
    have := abs_lt.1 (s.abs_lt_xmin_of_mem_denormalized hx)
    exact ⟨this.1, this.2⟩⟩

/-- **Example 2.11**: the system `𝔽(2, 3, -1, 2)`. -/
def example_2_11_system : System := ⟨2, 3, -1, 2, by norm_num, by norm_num, by norm_num⟩

/-- **Example 2.11**: the positive numbers of `𝔽(2, 3, -1, 2)` are the sixteen numbers
`(0.111)₂ 2² = 7/2, (0.110)₂ 2² = 3, …, (0.100)₂ 2⁻¹ = 1/4`. -/
theorem example_2_11 :
    {x : ℚ | x ∈ example_2_11_system.numbers ℚ ∧ 0 < x} =
      {7/2, 3, 5/2, 2, 7/4, 3/2, 5/4, 1, 7/8, 3/4, 5/8, 1/2, 7/16, 3/8, 5/16, 1/4} := by
  have key : ∀ (m : ℕ) (e : ℤ), 4 ≤ m → m ≤ 7 → -1 ≤ e → e ≤ 2 → ∀ x : ℚ,
      x = m * (2 : ℚ) ^ (e - 3) → x ∈ example_2_11_system.numbers ℚ ∧ 0 < x := by
    intro m e hm1 hm2 he1 he2 x hx
    refine ⟨Or.inr ⟨1, m, e, hm1, hm2, he1, he2, ?_⟩, ?_⟩
    · simp [example_2_11_system, hx]
    · rw [hx]
      exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, hpos⟩
    rcases hx with rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩
    · exact absurd hpos (lt_irrefl 0)
    · simp only [example_2_11_system] at hm1 hm2 hL hU hpos ⊢
      norm_num at hm1 hm2
      rcases Int.units_eq_one_or σ with rfl | rfl
      · simp only [Units.val_one, Int.cast_one, one_mul, Nat.cast_ofNat] at hpos ⊢
        interval_cases m <;> interval_cases e <;> norm_num
      · exfalso
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Nat.cast_ofNat] at hpos
        have : (0 : ℚ) < m * (2 : ℚ) ^ (e - 3) :=
          mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
        linarith
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    · exact key 7 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 7 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 6 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 5 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)
    · exact key 4 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ (by norm_num)

/-- **Example 2.11, the bounds and the count**: the numbers are "included between `x_min = β^(L-1)
= 2⁻² = 1/4` and `x_max = β^U (1 - β^(-t)) = 2² (1 - 2⁻³) = 7/2`", and there are `(β - 1) β^(t-1) (U
- L + 1) = 16` strictly positive numbers, hence `2 · 16 + 1` numbers with their opposites and
zero. -/
theorem example_2_11_bounds :
    example_2_11_system.xmin ℚ = 1/4 ∧ example_2_11_system.xmax ℚ = 7/2 ∧
      ((example_2_11_system.finset ℚ).card : ℤ) = 2 * 16 + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [System.xmin, example_2_11_system]; norm_num
  · simp [System.xmax, example_2_11_system]; norm_num
  · rw [System.card_finset]; simp [example_2_11_system]

/-- **Example 2.11, the de-normalized numbers**: the positive de-normalized numbers of `𝔽(2, 3, -1,
2)` are `(.011)₂ 2⁻¹ = 3/16, (.010)₂ 2⁻¹ = 1/8, (.001)₂ 2⁻¹ = 1/16`, and "the smallest de-normalized
number is `β^(L-t) = 2^(-1-3) = 1/16`". -/
theorem example_2_11_denormalized :
    {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} = {3/16, 1/8, 1/16} ∧
      IsLeast {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} (1/16) := by
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ∀ x : ℚ, x = m * (2 : ℚ) ^ (-4 : ℤ) →
      x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x := by
    intro m hm1 hm2 x hx
    refine ⟨⟨1, m, hm1, hm2, ?_⟩, ?_⟩
    · simp [example_2_11_system, hx]
    · rw [hx]
      exact mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
  have hset : {x : ℚ | x ∈ example_2_11_system.denormalized ℚ ∧ 0 < x} = {3/16, 1/8, 1/16} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨σ, m, hm1, hm2, rfl⟩, hpos⟩
      simp only [example_2_11_system] at hm1 hm2 hpos ⊢
      norm_num at hm2
      rcases Int.units_eq_one_or σ with rfl | rfl
      · simp only [Units.val_one, Int.cast_one, one_mul, Nat.cast_ofNat] at hpos ⊢
        interval_cases m <;> norm_num
      · exfalso
        simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Nat.cast_ofNat] at hpos
        have : (0 : ℚ) < m * (2 : ℚ) ^ ((-1 : ℤ) - 3) :=
          mul_pos (by exact_mod_cast (by omega : 0 < m)) (zpow_pos (by norm_num) _)
        linarith
    · rintro (rfl | rfl | rfl)
      · exact key 3 (by norm_num) (by norm_num) _ (by norm_num)
      · exact key 2 (by norm_num) (by norm_num) _ (by norm_num)
      · exact key 1 (by norm_num) (by norm_num) _ (by norm_num)
  refine ⟨hset, ?_⟩
  have hval : ((example_2_11_system.β : ℚ) ^ (example_2_11_system.L - example_2_11_system.t))
      = 1 / 16 := by
    norm_num [example_2_11_system]
  have := example_2_11_system.isLeast_denormalized (K := ℚ) (by decide)
  rwa [hval] at this

/-! ### §2.5.3 Distribution of the floating-point numbers -/

/-- **§2.5.3, the distribution of the floating-point numbers**. First, having fixed an exponent `L
≤ e ≤ U`, the numbers of `𝔽` in the binade `[β^(e-1), β^e)` are `m β^(e-t)` for `β^(t-1) ≤ m ≤
β^t - 1`, "equally spaced and [with] distance equal to `β^(e-t)`". Second, "the spacing between a
number `x ∈ 𝔽` and its next nearest `y ∈ 𝔽` … is at least `β⁻¹ ε_M |x|` and at most `ε_M |x|`,
being `ε_M = β^(1-t)` the machine epsilon": the spacing `β^(e-t)` at `x ≠ 0` of exponent `e =
exponent x` satisfies `β⁻¹ ε_M |x| < β^(e-t) ≤ ε_M |x|`.

Both are stated in the mantissa convention (2.29), `x = ± 0.a₁…a_t × β^e`, in which the binade of
exponent `e` is `[β^(e-1), β^e)`; the book's sentence "having fixed an interval of the form `[β^e,
β^(e+1)]` … distance equal to `β^(e-t)`" uses the other convention `a₁.a₂… × β^e`. -/
theorem spacing (s : System) :
    (∀ e : ℤ, s.L ≤ e → e ≤ s.U →
      s.numbers ℝ ∩ Set.Ico ((s.β : ℝ) ^ (e - 1)) ((s.β : ℝ) ^ e) =
        (fun m : ℕ => (m : ℝ) * (s.β : ℝ) ^ (e - s.t)) ''
          Set.Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1)) ∧
    ∀ x : ℝ, x ≠ 0 →
      (s.β : ℝ)⁻¹ * (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| < (s.β : ℝ) ^ (s.exponent x - s.t) ∧
        (s.β : ℝ) ^ (s.exponent x - s.t) ≤ (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| :=
  ⟨fun _ hL hU => s.numbers_inter_Ico hL hU, fun _ hx => s.ulp_bounds hx⟩

/-- **(2.31)**: for `x = (-1)^s m(x) β^(e-t) ∈ 𝔽`, the distance `Δx = β^(e-t)` to the successive
number gives the relative distance `Δx / x = 1 / m(x)`, which depends only on the mantissa
(*wobbling precision*). -/
theorem equation_2_31 (s : System) {σ : ℤˣ} {m : ℕ} {e : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) {x : ℝ} (hx : x = ((σ : ℤ) : ℝ) * m * (s.β : ℝ) ^ (e - s.t)) :
    (s.β : ℝ) ^ (s.exponent x - s.t) / |x| = 1 / m :=
  s.ulp_div_eq_inv_mantissa hm1 hm2 hx

/-- **§2.5.3, the machine epsilon**: `ε_M = β^(1-t)` "represents the distance between the number
`1` and the nearest floating-point number, and therefore it is the smallest number of `𝔽` such
that `1 + ε_M > 1`" — read as: `ε_M` is the least positive `δ` with `1 + δ ∈ 𝔽`. This needs the
exponent `1` to be admissible and `t ≥ 2` (in `𝔽(2, 1, L, 1)` no number of `𝔽` exceeds `1`). -/
theorem machineEps_isLeast (s : System) (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ s.numbers ℝ} ((s.β : ℝ) ^ (1 - (s.t : ℤ))) :=
  s.isLeast_machineEps hL hU ht

/-! ### §2.5.4 IEC/IEEE arithmetic -/

/-- **§2.5.4, the IEC 559 basic formats**: single precision is `𝔽(2, 24, -125, 128)` and double
precision `𝔽(2, 53, -1021, 1024)`, with roundoff units `u = 2^(-24)` and `u = 2^(-53)`. -/
theorem ieeeUnitRoundoff :
    (System.ieeeSingle.β, System.ieeeSingle.t, System.ieeeSingle.L, System.ieeeSingle.U) =
        (2, 24, -125, 128) ∧
      (System.ieeeDouble.β, System.ieeeDouble.t, System.ieeeDouble.L, System.ieeeDouble.U) =
        (2, 53, -1021, 1024) ∧
      System.ieeeSingle.unitRoundoff ℝ = 2 ^ (-24 : ℤ) ∧
      System.ieeeDouble.unitRoundoff ℝ = 2 ^ (-53 : ℤ) :=
  ⟨rfl, rfl, System.ieeeSingle_unitRoundoff, System.ieeeDouble_unitRoundoff⟩

/-! ### §2.5.5 Rounding of a real number in its machine representation -/

/-- The nearest-integer rounding of `μ ≥ 0` as the book's digit rule: with `a_{t+1} = ⌊β μ⌋ mod β`
the first digit beyond the integer part, `round μ = ⌊μ⌋ + 1` when `a_{t+1} ≥ β/2` and `⌊μ⌋`
otherwise — for even `β`. -/
private theorem round_eq_floor_add_ite {β : ℕ} (hβ : Even β) (hβ2 : 2 ≤ β) (μ : ℝ) :
    round μ = ⌊μ⌋ + if (β : ℤ) / 2 ≤ ⌊μ * β⌋ % β then 1 else 0 := by
  obtain ⟨k, hk⟩ := hβ
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hβk : (β : ℝ) = 2 * k := by rw [hk]; push_cast; ring
  have hβk' : (β : ℤ) / 2 = k := by rw [hk]; omega
  -- the first digit beyond the integer part is `⌊fract μ · β⌋`
  have hfloor : ⌊μ * β⌋ % β = ⌊Int.fract μ * β⌋ := by
    have h1 : μ * β = ((⌊μ⌋ * β : ℤ) : ℝ) + Int.fract μ * β := by
      push_cast; rw [Int.fract]; ring
    rw [h1, Int.floor_intCast_add, Int.mul_add_emod_self_right]
    refine Int.emod_eq_of_lt (Int.floor_nonneg.2 (by positivity)) ?_
    rw [Int.floor_lt]
    push_cast
    exact mul_lt_of_lt_one_left (by exact_mod_cast (show 0 < β by omega)) (Int.fract_lt_one μ)
  have hround : round μ = ⌊μ⌋ + ⌊Int.fract μ + 1 / 2⌋ := by
    rw [round_eq, ← Int.floor_intCast_add]
    congr 1
    rw [Int.fract]; ring
  rw [hround, hfloor, hβk']
  congr 1
  have h0 := Int.fract_nonneg μ
  have h1 := Int.fract_lt_one μ
  split_ifs with h
  · rw [Int.le_floor, hβk] at h
    push_cast at h
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  · rw [Int.le_floor, hβk, not_le] at h
    push_cast at h
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith

/-- **(2.32), the rounding as a digit rule**: for even `β` (the book's standing assumption of
§2.5.1) and `x` with exponent `e`, digits `|x| = (0.a₁a₂…a_t a_{t+1}…) β^e`, integer part of the
shifted mantissa `a₁…a_t = ⌊μ⌋` where `μ = |x| β^(t-e)`, and next digit `a_{t+1} = ⌊β μ⌋ mod β`,

`fl(x) = (-1)^s (0.a₁a₂…ã_t) β^e` with `ã_t = a_t` if `a_{t+1} < β/2` and `a_t + 1` if `a_{t+1} ≥
β/2`,

i.e. `fl(x) = sign x · (⌊μ⌋ + [a_{t+1} ≥ β/2]) β^(e-t)`; this is the rounding to nearest
`FloatingPoint.System.round`. For odd `β` the digit rule chops some tails above one half. -/
theorem equation_2_32 (s : System) (hβ : Even s.β) (x : ℝ) :
    s.round x = (SignType.sign x : ℝ) *
      ((⌊s.mantissa x⌋ + if (s.β : ℤ) / 2 ≤ ⌊s.mantissa x * s.β⌋ % s.β then 1 else 0 : ℤ) : ℝ) *
        (s.β : ℝ) ^ (s.exponent x - s.t) := by
  rw [System.round, round_eq_floor_add_ite hβ s.two_le_β]

/-- **§2.5.5**: "`fl(x) = x` if `x ∈ 𝔽`". -/
theorem fl_eq_self_of_mem (s : System) {x : ℝ} (hx : x ∈ s.numbers ℝ) : s.round x = x :=
  s.round_eq_self hx

/-- **§2.5.5, the monotonicity property**: "`fl(x) ≤ fl(y)` if `x ≤ y`, for all `x, y ∈ ℝ`". -/
theorem fl_mono (s : System) {x y : ℝ} (hxy : x ≤ y) : s.round x ≤ s.round y :=
  s.round_mono hxy

/-- **Remark 2.2 (overflow and underflow)**. (i) *Overflow*: for `|x| ≥ β^U` the rounding leaves
`𝔽` — the book's "`fl(x)` is not defined" for `|x| > x_max`, read as "is not a number of `𝔽`";
the threshold is `β^U` rather than `x_max`, since the numbers of `(x_max, β^U - ½β^(U-t))` round
to `x_max`. (ii) *Underflow*: for `0 < |x| < x_min` "the operation of rounding is defined anyway",
and it still satisfies the bound (2.33), `|fl(x) - x| ≤ u |x|`. -/
theorem remark_2_2 (s : System) :
    (∀ x : ℝ, (s.β : ℝ) ^ s.U ≤ |x| → s.round x ∉ s.numbers ℝ) ∧
      ∀ x : ℝ, 0 < |x| → |x| < (s.β : ℝ) ^ (s.L - 1) →
        |s.round x - x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) * |x| :=
  ⟨fun _ hx => s.round_notMem_numbers hx, fun x _ _ => s.abs_round_sub_le x⟩

/-- **Property 2.1, (2.33)–(2.34)**: if `x ∈ ℝ` satisfies `x_min ≤ |x| ≤ x_max`, then
`fl(x) = x (1 + δ)` with `|δ| ≤ u`, where `u = ½ β^(1-t)` is the roundoff unit; and `fl(x) ∈ 𝔽`. -/
theorem property_2_1 (s : System) {x : ℝ} (h1 : s.xmin ℝ ≤ |x|) (h2 : |x| ≤ s.xmax ℝ) :
    (∃ δ : ℝ, |δ| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧ s.round x = x * (1 + δ)) ∧
      s.round x ∈ s.numbers ℝ :=
  ⟨s.exists_round_eq_mul_one_add x, s.round_mem_numbers h1 h2⟩

/-- **(2.34)**: the roundoff unit is `u = ½ β^(1-t) = ½ ε_M`. -/
theorem equation_2_34 (s : System) :
    s.unitRoundoff ℝ = (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧
      s.unitRoundoff ℝ = s.machineEps ℝ / 2 :=
  ⟨rfl, s.unitRoundoff_eq_machineEps_div_two⟩

/-- **Property 2.1 for chopping** (the book's parenthetical "in the chopping one would take `ã_t =
a_t`"): `chop x = x (1 + δ)` with `|δ| ≤ β^(1-t) = ε_M`, the unit roundoff of chopping
([higham2002accuracy] Theorem 2.2). -/
theorem property_2_1_chop (s : System) (x : ℝ) :
    ∃ δ : ℝ, |δ| ≤ (s.β : ℝ) ^ (1 - (s.t : ℤ)) ∧ s.chop x = x * (1 + δ) :=
  s.exists_chop_eq_mul_one_add x

/-- **(2.35), the relative error of rounding**: `E_rel(x) = |x - fl(x)| / |x| ≤ u` for `x ≠ 0`. -/
theorem equation_2_35 (s : System) {x : ℝ} (hx : x ≠ 0) :
    |x - s.round x| / |x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (1 - (s.t : ℤ)) := by
  rw [div_le_iff₀ (abs_pos.2 hx), abs_sub_comm]
  exact s.abs_round_sub_le x

/-- **§2.5.5, the absolute error of rounding** (the display `E(x) ≤ ½ β^(-t+e)` closing the
section): `E(x) = |x - fl(x)| ≤ ½ β^(e-t)` with `e` the exponent of `x`. -/
theorem roundAbsError (s : System) (x : ℝ) :
    |x - s.round x| ≤ (1 / 2 : ℝ) * (s.β : ℝ) ^ (s.exponent x - s.t) :=
  s.abs_sub_round_le x

/-! ### §2.5.6 Machine floating-point operations -/

/-- **§2.5.6, the machine operation**: given an arithmetic operation `∘ : ℝ × ℝ → ℝ`, the
corresponding machine operation is `x ∘ y = fl(fl(x) ∘ fl(y))`. -/
noncomputable def machineOp (s : System) (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  s.round (f (s.round x) (s.round y))

/-- The machine operation is the backbone's `FloatingPoint.System.op`; the sum, difference, product
and quotient are `s.add`, `s.sub`, `s.mul`, `s.div`. -/
theorem machineOp_eq (s : System) (f : ℝ → ℝ → ℝ) : machineOp s f = s.op f := rfl

/-- **(2.36)**: for all `x, y ∈ 𝔽` and each of the four operations, `x ∘ y = (x ∘ y)(1 + δ)` with
`|δ| ≤ u`. The book says this "will require an additional assumption … the round digit" for the
subtraction; in this idealized arithmetic the exact result is rounded, so the assumption is built
in. -/
theorem equation_2_36 (s : System) {x y : ℝ} (hx : x ∈ s.numbers ℝ) (hy : y ∈ s.numbers ℝ) :
    (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· + ·) x y = (x + y) * (1 + δ)) ∧
      (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· - ·) x y = (x - y) * (1 + δ)) ∧
      (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· * ·) x y = (x * y) * (1 + δ)) ∧
      ∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ machineOp s (· / ·) x y = (x / y) * (1 + δ) :=
  ⟨s.exists_op_eq_mul_one_add _ hx hy, s.exists_op_eq_mul_one_add _ hx hy,
    s.exists_op_eq_mul_one_add _ hx hy, s.exists_op_eq_mul_one_add _ hx hy⟩

/-- **§2.5.6, properties preserved**: "the commutativity of the sum of two addends, or the product
of two factors" survives in floating-point arithmetic. -/
theorem machineOp_comm (s : System) (x y : ℝ) :
    machineOp s (· + ·) x y = machineOp s (· + ·) y x ∧
      machineOp s (· * ·) x y = machineOp s (· * ·) y x :=
  ⟨s.add_comm x y, s.mul_comm x y⟩

/-- The two-digit decimal system `𝔽(10, 2, -1, 2)`, in which the failure of associativity is
exhibited (the base and precision of the round-digit example of §2.5.6). -/
def decimalSystem : System := ⟨10, 2, -1, 2, by norm_num, by norm_num, by norm_num⟩

/-- **§2.5.6, associativity is lost**: "in general `x ⊕ (y ⊕ z) ≠ (x ⊕ y) ⊕ z`". In `𝔽(10, 2, -1,
2)` with `x = 1`, `y = z = 0.04`, all three in `𝔽`: `(x ⊕ y) ⊕ z = fl(fl(1.04) + 0.04) = fl(1.0 +
0.04) = 1.0`, while `x ⊕ (y ⊕ z) = fl(1 + fl(0.08)) = fl(1.08) = 1.1`. Computed over `ℚ`. -/
theorem machineAdd_not_assoc :
    (1 : ℚ) ∈ decimalSystem.numbers ℚ ∧ (4 / 100 : ℚ) ∈ decimalSystem.numbers ℚ ∧
      decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) = 1 ∧
      decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) = 11 / 10 ∧
      decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) ≠
        decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) := by
  have h1 : (1 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 10, 1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have h2 : (4 / 100 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 40, -1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have h3 : (8 / 100 : ℚ) ∈ decimalSystem.numbers ℚ :=
    Or.inr ⟨1, 80, -1, by norm_num [decimalSystem], by norm_num [decimalSystem],
      by norm_num [decimalSystem], by norm_num [decimalSystem], by norm_num [decimalSystem]⟩
  have r1 : decimalSystem.round (1 : ℚ) = 1 := decimalSystem.round_eq_self h1
  have r2 : decimalSystem.round (4 / 100 : ℚ) = 4 / 100 := decimalSystem.round_eq_self h2
  have r6 : decimalSystem.round (8 / 100 : ℚ) = 8 / 100 := decimalSystem.round_eq_self h3
  -- `fl(1.04) = 1.0`: exponent `1`, mantissa `10.4`
  have r3 : decimalSystem.round (1 + 4 / 100 : ℚ) = 1 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := 1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  -- `fl(0.08) = 0.08`: exponent `-1`, mantissa `80`
  have r4 : decimalSystem.round (4 / 100 + 4 / 100 : ℚ) = 8 / 100 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := -1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  -- `fl(1.08) = 1.1`: exponent `1`, mantissa `10.8`
  have r5 : decimalSystem.round (1 + 8 / 100 : ℚ) = 11 / 10 := by
    rw [decimalSystem.round_eq_of_le_of_lt (e := 1) (by norm_num [decimalSystem])
      (by norm_num [decimalSystem])]
    norm_num [decimalSystem]
  have hl : decimalSystem.add (decimalSystem.add (1 : ℚ) (4 / 100)) (4 / 100) = 1 := by
    simp only [System.add, System.op, r1, r2, r3]
  have hr : decimalSystem.add (1 : ℚ) (decimalSystem.add (4 / 100) (4 / 100)) = 11 / 10 := by
    simp only [System.add, System.op, r1, r2, r4, r6]
    exact r5
  exact ⟨h1, h2, hl, hr, by rw [hl, hr]; norm_num⟩

end QuarteroniSaccoSaleri.Chapter02
