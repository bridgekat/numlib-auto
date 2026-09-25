import Mathlib.Data.Rat.Floor
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.System
import NumlibSurface.GolubVanLoan.Chapter02.Section06

/-!
# Golub–Van Loan §2.7: finite precision matrix computations

Surface file for [golub2013matrix] §2.7: the 3-digit calculator and the IEEE double format as
instances of `FloatingPoint.System` (§2.7.1–2.7.2), the model of floating point arithmetic
(2.7.4)–(2.7.6), the non-associativity of floating point addition (Maxim 1), storing a matrix
(2.7.7), Lemma 2.7.1, rounding in scaling and addition (2.7.15)–(2.7.16), the `2 × 2` backward error
example of §2.7.9, and the ideal equation solver (2.7.21)–(2.7.22).

## Conventions

`fp : FloatingPoint.RoundingModel ℝ` is the book's arithmetic and `fp.u` its unit roundoff `u`; a
stored or computed `fl(x)` is any `y` with `fp.Rounds x y`, entrywise for matrices and vectors.
Concrete arithmetic is a `FloatingPoint.System` (`𝔽(β, t, L, U)`), whose rounding is
`FloatingPoint.System.round` and whose machine operations are `FloatingPoint.System.add` etc. First
order `… + O(u²)` bounds are stated with `FloatingPoint.gamma` (`γ_n = n u / (1 - n u)`).

The run statements of the dot product (2.7.8)–(2.7.12), the saxpy and outer product updates
(2.7.17)–(2.7.18) and the matrix products (2.7.19)–(2.7.20), and the nonnegative-product remark of
§2.7.10, are about the runs of chapter 1's Algorithms 1.1.1–1.1.8 and 1.2.1
(`GolubVanLoan.Chapter01`); they are planned in this group and wait for chapter 1's programs.

## Sources

Backbone `Numlib/FloatingPoint/{Model,System,InnerProduct}`, and
`Numlib/Analysis/Matrix/OperatorNorm` for the norm forms. Not formalized: the sample roundings of
§2.7.1, `±∞`, `NaN`, exceptions and the directed rounding modes of §2.7.2 (the `lsb` tie rule is
covered by "any nearest element"), Maxims 2 and 3, the styles (2.7.13)–(2.7.14), the Wilkinson
quotation, and the Strassen claims of §2.7.10 (see the chapter's plan).
-/

open Finset Matrix FloatingPoint WithLp
open scoped ENNReal

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.7.1 A 3-digit calculator -/

/-- **§2.7.1, the 3-digit calculator** `± d₀.d₁d₂ × 10^e`, `1 ≤ d₀ ≤ 9`, `-9 ≤ e ≤ 9`: the system
`𝔽(10, 3, -8, 10)` (the backbone writes the numbers as `0.d₀d₁d₂ × 10^{e+1}`, which shifts the
exponent range by one). -/
def calculator3 : System :=
  ⟨10, 3, -8, 10, by norm_num, by norm_num, by norm_num⟩

/-- **§2.7.1**: the calculator has `2 × 9 × 10 × 10 × 19 + 1 = 34201` floating point numbers. -/
theorem calculator3_card : ((calculator3.finset ℝ).card : ℤ) = 34201 := by
  rw [System.card_finset]
  norm_num [calculator3]

/-- **§2.7.1**: the smallest and largest positive numbers of the calculator are
`N_min = 1.00 × 10⁻⁹` and `N_max = 9.99 × 10⁹`, and between `1.00 × 10^e` and `1.00 × 10^{e+1}`
(`-9 ≤ e ≤ 9`) the numbers are the `m × 10^{e-2}`, `100 ≤ m ≤ 999`: the spacing is `10^{e-2}`. -/
theorem calculator3_range :
    calculator3.xmin ℝ = 10 ^ (-9 : ℤ) ∧ calculator3.xmax ℝ = 999 / 100 * 10 ^ 9 ∧
      ∀ e : ℤ, -9 ≤ e → e ≤ 9 →
        calculator3.numbers ℝ ∩ Set.Ico ((10 : ℝ) ^ e) (10 ^ (e + 1)) =
          (fun m : ℕ => (m : ℝ) * 10 ^ (e - 2)) '' Set.Icc 100 999 := by
  refine ⟨by norm_num [System.xmin, calculator3], by norm_num [System.xmax, calculator3], ?_⟩
  intro e he1 he2
  have h := calculator3.numbers_inter_Ico (K := ℝ) (e := e + 1)
    (show (-8 : ℤ) ≤ e + 1 by omega) (show e + 1 ≤ (10 : ℤ) by omega)
  have hβ : ((calculator3.β : ℕ) : ℝ) = 10 := by norm_num [calculator3]
  have hβ' : calculator3.β = 10 := rfl
  have ht : calculator3.t = 3 := rfl
  rw [hβ, hβ', ht, add_sub_cancel_right] at h
  rw [h, show (fun m : ℕ => (m : ℝ) * 10 ^ (e - 2)) =
      fun m : ℕ => (m : ℝ) * 10 ^ (e + 1 - ((3 : ℕ) : ℤ)) from
        funext fun m => by congr 2; push_cast; ring]
  norm_num

/-! ### §2.7.2 IEEE floating point arithmetic -/

/-- The 52 mantissa bits `b₁ … b₅₂` read as the integer `∑ᵢ bᵢ 2^{52-i}` (0-based `2^{51-i}`):
`finFunctionFinEquiv` of the reversed bit string. -/
private theorem bits_eq (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) = (finFunctionFinEquiv (b ∘ Fin.rev) : ℕ) := by
  rw [finFunctionFinEquiv_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Function.comp_apply, Fin.rev_rev, Fin.val_rev]
  rw [show 52 - ((i : ℕ) + 1) = 51 - (i : ℕ) by omega]

/-- The mantissa bits encode exactly the integers below `2^52`. -/
private theorem bits_lt (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) < 2 ^ 52 := by
  rw [bits_eq]
  exact (finFunctionFinEquiv (b ∘ Fin.rev)).isLt

/-- Every integer below `2^52` is encoded by some mantissa bits. -/
private theorem exists_bits {r : ℕ} (hr : r < 2 ^ 52) :
    ∃ b : Fin 52 → Fin 2, ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) = r := by
  refine ⟨finFunctionFinEquiv.symm ⟨r, hr⟩ ∘ Fin.rev, ?_⟩
  have h : (finFunctionFinEquiv.symm ⟨r, hr⟩ ∘ Fin.rev) ∘ Fin.rev =
      (finFunctionFinEquiv.symm ⟨r, hr⟩ : Fin 52 → Fin 2) := by
    funext i
    simp
  rw [bits_eq, h, Equiv.apply_symm_apply]

/-- The binary fraction `(0.b₁…b₅₂)₂` is the integer of the bits times `2⁻⁵²`. -/
private theorem bits_real (b : Fin 52 → Fin 2) :
    ∑ i : Fin 52, ((b i : ℕ) : ℝ) * (2 : ℝ) ^ (-((i : ℤ) + 1)) =
      ((∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)) : ℕ) : ℝ) * 2 ^ (-52 : ℤ) := by
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 2
  have := i.isLt
  omega

/-- `2⁵² · 2⁻⁵² = 1`. -/
private theorem two_pow_mul_zpow_neg : (2 : ℝ) ^ (52 : ℕ) * 2 ^ (-52 : ℤ) = 1 := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
  norm_num

/-- The value of the double system's base and number of digits. -/
private theorem ieeeDouble_β_cast : ((System.ieeeDouble.β : ℕ) : ℝ) = 2 := by
  norm_num [System.ieeeDouble]

/-- **(2.7.2), the normalized doubles**: the values `± (1.b₁b₂…b₅₂)₂ × 2^{E - 1023}` with a biased
exponent `1 ≤ E ≤ 2046` (the exponent bits neither all `0` nor all `1`) are exactly the nonzero
numbers of the backbone's double system `𝔽(2, 53, -1021, 1024)` (mantissa
`m = 2⁵² + ∑ bᵢ 2^{52-i}`, exponent `e = E - 1022`). The bits `bᵢ` are digits `Fin 2`. -/
theorem equation_2_7_2 :
    {x : ℝ | ∃ (σ : ℤˣ) (b : Fin 52 → Fin 2) (E : ℕ), 1 ≤ E ∧ E ≤ 2046 ∧
        x = ((σ : ℤ) : ℝ) * (1 + ∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1))) *
          2 ^ ((E : ℤ) - 1023)} =
      System.ieeeDouble.numbers ℝ \ {0} := by
  have ht : (System.ieeeDouble.t : ℤ) = 53 := rfl
  ext x
  constructor
  · rintro ⟨σ, b, E, hE1, hE2, rfl⟩
    have hr := bits_lt b
    norm_num at hr
    have h1 : (0 : ℝ) < 1 + ∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1)) :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => by positivity)
    refine ⟨Or.inr ⟨σ, 2 ^ 52 + ∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ)), (E : ℤ) - 1022,
      ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · norm_num [System.ieeeDouble]
    · norm_num [System.ieeeDouble]
      omega
    · change (-1021 : ℤ) ≤ _
      omega
    · change _ ≤ (1024 : ℤ)
      omega
    · rw [ieeeDouble_β_cast, ht, show (2 : ℝ) ^ ((E : ℤ) - 1022 - 53) =
          2 ^ ((E : ℤ) - 1023) * 2 ^ (-52 : ℤ) by rw [← zpow_add₀ two_ne_zero]; ring_nf, bits_real]
      push_cast
      linear_combination (-(((σ : ℤ) : ℝ)) * (2 : ℝ) ^ ((E : ℤ) - 1023)) * two_pow_mul_zpow_neg
    · rw [Set.mem_singleton_iff]
      exact mul_ne_zero (mul_ne_zero (Int.cast_ne_zero.2 σ.ne_zero) h1.ne') (by positivity)
  · rintro ⟨hx | ⟨σ, m, e, hm1, hm2, he1, he2, rfl⟩, hx0⟩
    · exact absurd hx hx0
    norm_num [System.ieeeDouble] at hm1 hm2
    change (-1021 : ℤ) ≤ e at he1
    change e ≤ (1024 : ℤ) at he2
    obtain ⟨b, hb⟩ := exists_bits (r := m - 2 ^ 52) (by norm_num; omega)
    refine ⟨σ, b, (e + 1022).toNat, by omega, by omega, ?_⟩
    rw [ieeeDouble_β_cast, ht, bits_real, hb, Nat.cast_sub (by norm_num; omega),
      Int.toNat_of_nonneg (by omega), show (2 : ℝ) ^ (e - 53) =
        2 ^ (e + 1022 - 1023) * 2 ^ (-52 : ℤ) by rw [← zpow_add₀ two_ne_zero]; ring_nf]
    push_cast
    linear_combination (((σ : ℤ) : ℝ)) * (2 : ℝ) ^ (e + 1022 - 1023) * two_pow_mul_zpow_neg

/-- **(2.7.3), zero and the subnormal doubles**: the values `± (0.b₁b₂…b₅₂)₂ × 2^{-1022}` (exponent
bits all `0`) are exactly `0` and the de-normalized numbers `± m 2^{L-t} = ± m 2^{-1074}`,
`1 ≤ m < 2⁵²`, of the double system; they lie strictly between `-N_min` and `N_min`, uniformly
spaced by `2^{-1074}`. -/
theorem equation_2_7_3 :
    {x : ℝ | ∃ (σ : ℤˣ) (b : Fin 52 → Fin 2),
        x = ((σ : ℤ) : ℝ) * (∑ i : Fin 52, ((b i : ℕ) : ℝ) * 2 ^ (-((i : ℤ) + 1))) *
          2 ^ (-1022 : ℤ)} =
      System.ieeeDouble.denormalized ℝ ∪ {0} ∧
      ∀ x ∈ System.ieeeDouble.denormalized ℝ, |x| < System.ieeeDouble.xmin ℝ := by
  refine ⟨?_, fun x hx => System.ieeeDouble.abs_lt_xmin_of_mem_denormalized hx⟩
  have ht : (System.ieeeDouble.t : ℤ) = 53 := rfl
  have hL : System.ieeeDouble.L = -1021 := rfl
  have hexp : ∀ r : ℝ, r * 2 ^ (-52 : ℤ) * 2 ^ (-1022 : ℤ) = r * 2 ^ ((-1021 : ℤ) - 53) := by
    intro r
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]
    norm_num
  ext x
  constructor
  · rintro ⟨σ, b, rfl⟩
    have hr := bits_lt b
    norm_num at hr
    rw [bits_real]
    rcases Nat.eq_zero_or_pos (∑ i : Fin 52, (b i : ℕ) * 2 ^ (51 - (i : ℕ))) with h0 | hpos
    · refine Set.mem_union_right _ ?_
      rw [h0, Set.mem_singleton_iff]
      simp
    · refine Set.mem_union_left _ ⟨σ, _, hpos, ?_, ?_⟩
      · norm_num [System.ieeeDouble]
        omega
      · rw [ieeeDouble_β_cast, hL, ht, ← hexp]
        ring
  · rintro (⟨σ, m, hm1, hm2, rfl⟩ | h0)
    · norm_num [System.ieeeDouble] at hm2
      obtain ⟨b, hb⟩ := exists_bits (r := m) (by norm_num; omega)
      refine ⟨σ, b, ?_⟩
      rw [bits_real, hb, ieeeDouble_β_cast, hL, ht, ← hexp]
      ring
    · rw [Set.mem_singleton_iff] at h0
      exact ⟨1, fun _ => 0, by simp [h0]⟩

/-- **§2.7.2, the double format.** The machine epsilon, the gap between `1` and the next larger
double, is `2⁻⁵²`; the smallest and largest positive normalized doubles are `N_min = 2⁻¹⁰²²` and
`N_max = (2 - 2⁻⁵²) 2¹⁰²³`. -/
theorem ieeeDouble_constants :
    System.ieeeDouble.machineEps ℝ = 2 ^ (-52 : ℤ) ∧
      IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ System.ieeeDouble.numbers ℝ} (2 ^ (-52 : ℤ)) ∧
      System.ieeeDouble.xmin ℝ = 2 ^ (-1022 : ℤ) ∧
      System.ieeeDouble.xmax ℝ = (2 - 2 ^ (-52 : ℤ)) * 2 ^ (1023 : ℤ) := by
  refine ⟨System.ieeeDouble_machineEps, ?_, System.ieeeDouble_xmin, System.ieeeDouble_xmax⟩
  rw [← System.ieeeDouble_machineEps]
  exact System.ieeeDouble.isLeast_machineEps (by norm_num [System.ieeeDouble])
    (by norm_num [System.ieeeDouble]) (by norm_num [System.ieeeDouble])

/-- **§2.7.2, rounding to nearest.** If `N_min ≤ |x| ≤ N_max` and `y` is a double nearest to `x`,
then `|y - x| / |x| ≤ 2⁻⁵³`: the relative error is at most half the machine epsilon. The book's
round-half-to-even tie rule is one choice of such a `y`. -/
theorem ieeeDouble_round_nearest {x y : ℝ} (h1 : System.ieeeDouble.xmin ℝ ≤ |x|)
    (h2 : |x| ≤ System.ieeeDouble.xmax ℝ) (hnear : ∀ z ∈ System.ieeeDouble.numbers ℝ,
      |y - x| ≤ |z - x|) :
    |y - x| / |x| ≤ 2 ^ (-53 : ℤ) := by
  have hx : 0 < |x| := (System.ieeeDouble.xmin_pos).trans_le h1
  rw [div_le_iff₀ hx, ← System.ieeeDouble_unitRoundoff (K := ℝ)]
  exact System.ieeeDouble.abs_sub_le_of_forall_abs_sub_le h1 h2 hnear

/-! ### §2.7.3 The `fl` notation -/

/-- **(2.7.4)**: a floating point representation is `fl(x) = x (1 + δ)` with `|δ| ≤ u`: for every
admissible rounding `y` of `x` in the model, and for the rounding of a system `𝔽`. -/
theorem equation_2_7_4 (fp : RoundingModel ℝ) {x y : ℝ} (h : fp.Rounds x y) (s : System)
    (z : ℝ) :
    (∃ δ : ℝ, |δ| ≤ fp.u ∧ y = x * (1 + δ)) ∧
      ∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ s.round z = z * (1 + δ) :=
  ⟨h.exists_delta, s.exists_round_eq_mul_one_add z⟩

/-- **(2.7.5)**: `u = ½ × (gap between 1 and the next larger floating point number)`, for a system
with at least two digits whose exponent range contains `1`; for the IEEE formats `u = 2⁻²⁴`
(single, about `10⁻⁷`) and `u = 2⁻⁵³` (double, about `10⁻¹⁶`). -/
theorem equation_2_7_5 (s : System) (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    s.unitRoundoff ℝ = s.machineEps ℝ / 2 ∧
      IsLeast {δ : ℝ | 0 < δ ∧ 1 + δ ∈ s.numbers ℝ} (s.machineEps ℝ) ∧
      System.ieeeSingle.unitRoundoff ℝ = 2 ^ (-24 : ℤ) ∧
      System.ieeeDouble.unitRoundoff ℝ = 2 ^ (-53 : ℤ) :=
  ⟨s.unitRoundoff_eq_machineEps_div_two, s.isLeast_machineEps hL hU ht,
    System.ieeeSingle_unitRoundoff, System.ieeeDouble_unitRoundoff⟩

/-- **(2.7.6), the fundamental axiom of floating point arithmetic.** For floating point `x`, `y`
and an operation `op` (the book's `+`, `-`, `×`, `/`), `fl(x op y) = (x op y)(1 + δ)` with
`|δ| ≤ u`; equivalently the relative error is at most `u` when `x op y ≠ 0`. -/
theorem equation_2_7_6 (s : System) (f : ℝ → ℝ → ℝ) {x y : ℝ} (hx : x ∈ s.numbers ℝ)
    (hy : y ∈ s.numbers ℝ) :
    (∃ δ : ℝ, |δ| ≤ s.unitRoundoff ℝ ∧ s.op f x y = f x y * (1 + δ)) ∧
      (f x y ≠ 0 → |s.op f x y - f x y| / |f x y| ≤ s.unitRoundoff ℝ) := by
  obtain ⟨δ, hδ, hop⟩ := s.exists_op_eq_mul_one_add f hx hy
  refine ⟨⟨δ, hδ, hop⟩, fun h0 => ?_⟩
  rw [hop, show f x y * (1 + δ) - f x y = f x y * δ by ring, abs_mul,
    mul_div_cancel_left₀ _ (abs_ne_zero.2 h0)]
  exact hδ

/-! ### §2.7.4 Become a floating point thinker -/

/-- The rounding of the calculator at a number with known exponent. -/
private theorem calculator3_round_eq {x : ℝ} (e : ℤ) (h1 : (10 : ℝ) ^ (e - 1) ≤ |x|)
    (h2 : |x| < 10 ^ e) :
    calculator3.round x =
      (SignType.sign x : ℝ) * (_root_.round (|x| * (10 : ℝ) ^ (3 - e)) : ℝ) * 10 ^ (e - 3) := by
  have h := calculator3.round_eq_of_le_of_lt (K := ℝ) (x := x) (e := e)
    (by simpa [calculator3] using h1) (by simpa [calculator3] using h2)
  simpa [calculator3] using h

/-- **§2.7.4, Maxim 1: order is important.** Floating point addition is not associative: in the
calculator, with `x = 1.24`, `y = -1.23`, `z = 1.00 × 10⁻³`,
`fl(fl(x + y) + z) = 1.10 × 10⁻²` while `fl(x + fl(y + z)) = 1.00 × 10⁻²`. -/
theorem calculator3_add_not_assoc :
    calculator3.add (calculator3.add (124 / 100 : ℝ) (-123 / 100)) (1 / 1000) = 110 / 10000 ∧
      calculator3.add (124 / 100 : ℝ) (calculator3.add (-123 / 100) (1 / 1000)) = 100 / 10000 := by
  have hx : calculator3.round (124 / 100 : ℝ) = 124 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  have hy : calculator3.round (-123 / 100 : ℝ) = -123 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  have hz : calculator3.round (1 / 1000 : ℝ) = 1 / 1000 := by
    rw [calculator3_round_eq (-2) (by norm_num) (by norm_num)]; norm_num
  have hxy : calculator3.round (124 / 100 + -123 / 100 : ℝ) = 1 / 100 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have h01 : calculator3.round (1 / 100 : ℝ) = 1 / 100 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have hxyz : calculator3.round (1 / 100 + 1 / 1000 : ℝ) = 110 / 10000 := by
    rw [calculator3_round_eq (-1) (by norm_num) (by norm_num)]; norm_num
  have hyz : calculator3.round (-123 / 100 + 1 / 1000 : ℝ) = -123 / 100 := by
    rw [calculator3_round_eq 1 (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_⟩
  · simp only [System.add, System.op]
    rw [hx, hy, hxy, h01, hz, hxyz]
  · simp only [System.add, System.op]
    rw [hy, hz, hyz, hx, hy, hxy]
    norm_num

/-! ### §2.7.5 Storing a real matrix -/

/-- **(2.7.7), storing a matrix.** If `fl(A)` rounds each entry of `A ∈ ℝ^{m×n}`, then
`[fl(A)]ᵢⱼ = aᵢⱼ (1 + εᵢⱼ)` with `|εᵢⱼ| ≤ u`, i.e. `|fl(A) - A| ≤ u |A|`, and in the 1-norm
`‖fl(A) - A‖₁ ≤ u ‖A‖₁`. -/
theorem equation_2_7_7 (fp : RoundingModel ℝ) {A Â : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (A i j) (Â i j)) :
    (∃ ε : Matrix (Fin m) (Fin n) ℝ, (∀ i j, |ε i j| ≤ fp.u) ∧ ∀ i j, Â i j = A i j * (1 + ε i j)) ∧
      (Â - A).abs ≤ₑ fp.u • A.abs ∧ lpOpNorm 1 (Â - A) ≤ fp.u * lpOpNorm 1 A := by
  have habs : (Â - A).abs ≤ₑ fp.u • A.abs := fun i j => by
    simpa using fp.abs_sub_le (h i j)
  refine ⟨⟨fun i j => (h i j).exists_delta.choose, fun i j => (h i j).exists_delta.choose_spec.1,
    fun i j => (h i j).exists_delta.choose_spec.2⟩, habs, ?_⟩
  rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
  exact linfty_opNorm_le_mul_of_abs_entrywiseLE fp.u_nonneg fun i j => habs j i

/-! ### §2.7.6 Roundoff in dot products -/

/-- **Lemma 2.7.1.** If `1 + α = ∏_{k=1}^n (1 + αₖ)` with `|αₖ| ≤ u` and `n u ≤ .01`, then
`|α| ≤ 1.01 n u`. -/
theorem lemma_2_7_1 {u : ℝ} (hu : 0 ≤ u) (α : Fin n → ℝ) (hα : ∀ k, |α k| ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 100) {a : ℝ} (ha : 1 + a = ∏ k, (1 + α k)) :
    |a| ≤ 101 / 100 * (n * u) := by
  have h := abs_prod_one_add_sub_one_le_of_mul_le hu hα hnu
  rwa [← ha, add_sub_cancel_left] at h

/-! ### §2.7.8 Roundoff in other basic matrix computations -/

/-- **(2.7.15)**: if `fl(αA)` rounds each entry of `αA`, then `fl(αA) = αA + E` with
`|E| ≤ u |αA|`. -/
theorem equation_2_7_15 (fp : RoundingModel ℝ) (α : ℝ) {A C : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (α * A i j) (C i j)) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, C = α • A + E ∧ E.abs ≤ₑ fp.u • (α • A).abs :=
  ⟨C - α • A, by abel, fun i j => by simpa using fp.abs_sub_le (h i j)⟩

/-- **(2.7.16)**: if `fl(A + B)` rounds each entry of `A + B`, then `fl(A + B) = (A + B) + E` with
`|E| ≤ u |A + B|`. -/
theorem equation_2_7_16 (fp : RoundingModel ℝ) {A B C : Matrix (Fin m) (Fin n) ℝ}
    (h : ∀ i j, fp.Rounds (A i j + B i j) (C i j)) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, C = (A + B) + E ∧ E.abs ≤ₑ fp.u • (A + B).abs :=
  ⟨C - (A + B), by abel, fun i j => by simpa using fp.abs_sub_le (h i j)⟩

/-! ### §2.7.9 Forward and backward error analyses -/

/-- `|a c - a| ≤ g |a|` from `|c - 1| ≤ g`. -/
private theorem abs_mul_sub_self_le {a c g : ℝ} (h : |c - 1| ≤ g) : |a * c - a| ≤ g * |a| := by
  rw [show a * c - a = a * (c - 1) by ring, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg a)

/-- **§2.7.9, backward error of the `2 × 2` triangular product.** If `|εᵢ| ≤ u` (`i = 1:5`,
0-based here) and `fl(AB)` has the book's form
`[a₁₁b₁₁(1+ε₁), (a₁₁b₁₂(1+ε₂) + a₁₂b₂₂(1+ε₃))(1+ε₄); 0, a₂₂b₂₂(1+ε₅)]`, then `fl(AB) = Â B̂` with
`Â = [a₁₁, a₁₂(1+ε₃)(1+ε₄); 0, a₂₂(1+ε₅)]`, `B̂ = [b₁₁(1+ε₁), b₁₂(1+ε₂)(1+ε₄); 0, b₂₂]`, and
`|Â - A| ≤ γ₂ |A|`, `|B̂ - B| ≤ γ₂ |B|` (the book's `2u|A| + O(u²)`): the computed product is the
exact product of slightly perturbed factors. -/
theorem triangular_mul_two_backward {u : ℝ} (hu : 0 ≤ u) (h2u : 2 * u < 1)
    (a₁₁ a₁₂ a₂₂ b₁₁ b₁₂ b₂₂ : ℝ) (ε : Fin 5 → ℝ) (hε : ∀ i, |ε i| ≤ u) :
    !![a₁₁ * b₁₁ * (1 + ε 0),
        (a₁₁ * b₁₂ * (1 + ε 1) + a₁₂ * b₂₂ * (1 + ε 2)) * (1 + ε 3);
        0, a₂₂ * b₂₂ * (1 + ε 4)] =
      !![a₁₁, a₁₂ * ((1 + ε 2) * (1 + ε 3)); 0, a₂₂ * (1 + ε 4)] *
        !![b₁₁ * (1 + ε 0), b₁₂ * ((1 + ε 1) * (1 + ε 3)); 0, b₂₂] ∧
      (!![a₁₁, a₁₂ * ((1 + ε 2) * (1 + ε 3)); 0, a₂₂ * (1 + ε 4)] - !![a₁₁, a₁₂; 0, a₂₂]).abs ≤ₑ
        gamma u 2 • (!![a₁₁, a₁₂; 0, a₂₂] : Matrix (Fin 2) (Fin 2) ℝ).abs ∧
      (!![b₁₁ * (1 + ε 0), b₁₂ * ((1 + ε 1) * (1 + ε 3)); 0, b₂₂] - !![b₁₁, b₁₂; 0, b₂₂]).abs ≤ₑ
        gamma u 2 • (!![b₁₁, b₁₂; 0, b₂₂] : Matrix (Fin 2) (Fin 2) ℝ).abs := by
  have h2 : ((2 : ℕ) : ℝ) * u < 1 := by exact_mod_cast h2u
  have hγ0 : 0 ≤ gamma u 2 := gamma_nonneg hu h2
  have hγ1 : u ≤ gamma u 2 :=
    (le_gamma_one hu (by linarith)).trans (gamma_mono hu (by norm_num) h2)
  have hpair : ∀ i j : Fin 5, |(1 + ε i) * (1 + ε j) - 1| ≤ gamma u 2 := fun i j => by
    have h := abs_prod_one_add_sub_one_le_gamma hu h2 (δ := ![ε i, ε j])
      (fun k => by fin_cases k <;> simp [hε]) (ρ := fun _ => 1) (fun _ => Or.inl rfl)
    simpa [Fin.prod_univ_two] using h
  have hone : ∀ i : Fin 5, |(1 + ε i) - 1| ≤ gamma u 2 := fun i => by
    rw [add_sub_cancel_left]; exact (hε i).trans hγ1
  refine ⟨?_, fun i j => ?_, fun i j => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · fin_cases i <;> fin_cases j
    · simpa using mul_nonneg hγ0 (abs_nonneg a₁₁)
    · simpa using abs_mul_sub_self_le (a := a₁₂) (hpair 2 3)
    · simp
    · simpa using abs_mul_sub_self_le (a := a₂₂) (hone 4)
  · fin_cases i <;> fin_cases j
    · simpa using abs_mul_sub_self_le (a := b₁₁) (hone 0)
    · simpa using abs_mul_sub_self_le (a := b₁₂) (hpair 1 3)
    · simp
    · simpa using mul_nonneg hγ0 (abs_nonneg b₂₂)

/-! ### §2.7.11 Analysis of an ideal equation solver -/

/-- **(2.7.21)**: if `fl(A) = A + E` and `fl(b) = b + e` round the entries of `A` and `b`, then
`‖E‖_∞ ≤ u ‖A‖_∞` and `‖e‖_∞ ≤ u ‖b‖_∞`. -/
theorem equation_2_7_21 (fp : RoundingModel ℝ) {A Â : Matrix (Fin n) (Fin n) ℝ}
    {b bh : Fin n → ℝ} (hA : ∀ i j, fp.Rounds (A i j) (Â i j)) (hb : ∀ i, fp.Rounds (b i) (bh i)) :
    lpOpNorm ∞ (Â - A) ≤ fp.u * lpOpNorm ∞ A ∧
      ‖WithLp.toLp ∞ (bh - b)‖ ≤ fp.u * ‖WithLp.toLp ∞ b‖ := by
  refine ⟨?_, ?_⟩
  · rw [lpOpNorm_top, lpOpNorm_top]
    exact linfty_opNorm_le_mul_of_abs_entrywiseLE fp.u_nonneg (equation_2_7_7 fp hA).2.1
  · rw [PiLp.norm_toLp, PiLp.norm_toLp]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg fp.u_nonneg (norm_nonneg _))).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact (fp.abs_sub_le (hb i)).trans
      (mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.trans_le (norm_le_pi_norm b i))
        fp.u_nonneg)

/-- **(2.7.22), the ideal equation solver.** If `Ax = b` with `A` nonsingular and `b ≠ 0`, the
computed `xh` solves `(A + E) xh = b + e` with the bounds (2.7.21), and `u κ_∞(A) ≤ 1/2`, then
`‖x - xh‖_∞ / ‖x‖_∞ ≤ 4 u κ_∞(A)` (Theorem 2.6.2 at `ε = u`). -/
theorem equation_2_7_22 (fp : RoundingModel ℝ) {A E : Matrix (Fin n) (Fin n) ℝ}
    {b e x xh : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hxh : (A + E) *ᵥ xh = b + e) (hE : lpOpNorm ∞ E ≤ fp.u * lpOpNorm ∞ A)
    (he : ‖WithLp.toLp ∞ e‖ ≤ fp.u * ‖WithLp.toLp ∞ b‖)
    (hκ : fp.u * condNumberLp ∞ A ≤ 1 / 2) :
    ‖WithLp.toLp ∞ (x - xh)‖ / ‖WithLp.toLp ∞ x‖ ≤ 4 * fp.u * condNumberLp ∞ A := by
  have h := theorem_2_6_2 ∞ hA hx hb hxh hE he (by linarith)
  rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  refine h.trans ?_
  have hu := fp.u_nonneg
  have hκ0 : 0 ≤ condNumberLp ∞ A := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hu hκ0]

end GolubVanLoan.Chapter02
