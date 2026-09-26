import Mathlib.Data.Rat.Floor
import Numlib.FloatingPoint.InnerProduct
import Numlib.FloatingPoint.System
import NumlibSurface.GolubVanLoan.Chapter01.Section02
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
(2.7.17)–(2.7.18) and the matrix products (2.7.19)–(2.7.20), the nonnegative-product remark of
§2.7.10 and the `2 × 2` triangular product of §2.7.9 are about the runs `∀ s ∈ (alg fp.round …).run`
of chapter 1's Algorithms 1.1.1, 1.1.2, 1.1.6–1.1.8 and 1.2.1 (`GolubVanLoan.Chapter01`). The
book's exact `fl(0 + p) = p` at the start of an accumulation is the hypothesis `fp.IsIdempotent`;
chapter 1's bridges (`GolubVanLoan.Chapter01.algorithm_1_1_1_rounds`, `…_1_1_{6,7,8}_rounds`, the
run characterizations `…_mem_run`) turn runs into the backbone's relations `RoundsDot`,
`RoundsMul`.

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

/-- A run of the dot product (2.7.8) on `n + 1` entries is a run on the first `n` entries followed
by one rounded update `fl(s + fl(x_{n+1} y_{n+1}))`. -/
private theorem mem_run_algorithm_1_1_1_succ (fp : RoundingModel ℝ) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) (s : ℝ) :
    s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run ↔
      ∃ s' ∈ (Chapter01.algorithm_1_1_1 fp.round (fun k => x (Fin.castSucc k))
          (fun k => y (Fin.castSucc k))).run,
        ∃ p, fp.Rounds (x (Fin.last n) * y (Fin.last n)) p ∧ fp.Rounds (s' + p) s := by
  simp only [Chapter01.algorithm_1_1_1, List.finRange_succ_last, List.foldlM_append,
    List.foldlM_map, List.foldlM_cons, List.foldlM_nil, bind_pure, SetM.mem_run_bind,
    RoundingModel.mem_run_round]

/-- `∏_{j ≥ castSucc q} f j = (∏_{j ≥ q} f (castSucc j)) f(last)`. -/
private theorem prod_Ici_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) (q : Fin n) :
    ∏ j ∈ Finset.Ici (Fin.castSucc q), f j =
      (∏ j ∈ Finset.Ici q, f (Fin.castSucc j)) * f (Fin.last n) := by
  rw [← Finset.filter_le_eq_Ici, ← Finset.filter_le_eq_Ici, Finset.prod_filter,
    Finset.prod_filter, Fin.prod_univ_castSucc]
  simp [Fin.castSucc_le_castSucc_iff, Fin.le_last]

/-- `∏_{j ≥ last} f j = f(last)`. -/
private theorem prod_Ici_last {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∏ j ∈ Finset.Ici (Fin.last n), f j = f (Fin.last n) := by
  rw [← Fin.top_eq_last, Finset.Ici_top, Finset.prod_singleton]

/-- The partial sums of a run of the dot product (2.7.8) and their closed form: a run `s` has
relative errors `δ_k` (products) and `ε_k` (additions), `ε₁ = 0` because the first addition
`0 + fl(x₁ y₁)` is exact over an idempotent model, with `s_0 = 0`,
`s_p = (s_{p-1} + x_p y_p (1 + δ_p))(1 + ε_p)`, and
`s = ∑_k x_k y_k (1 + δ_k) ∏_{j ≥ k} (1 + ε_j)`. By induction on `n`, peeling off the last
update. -/
private theorem exists_partialSums_of_mem_run (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) :
    ∀ {n : ℕ} (x y : Fin n → ℝ) {s : ℝ}, s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run →
      ∃ δ ε : Fin n → ℝ, (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
        (∀ k : Fin n, (k : ℕ) = 0 → ε k = 0) ∧
        (∃ S : ℕ → ℝ, S 0 = 0 ∧
          (∀ p : Fin n, S (p + 1) = (S p + x p * y p * (1 + δ p)) * (1 + ε p)) ∧ s = S n) ∧
        s = ∑ k, x k * y k * ((1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j))
  | 0, x, y, s, hs => by
    have hs0 : s = 0 := by simpa [Chapter01.algorithm_1_1_1] using hs
    refine ⟨0, 0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      ⟨fun _ => 0, rfl, fun k => k.elim0, hs0⟩, ?_⟩
    simp [hs0]
  | n + 1, x, y, s, hs => by
    obtain ⟨s', hs', p, hp, hsp⟩ := (mem_run_algorithm_1_1_1_succ fp x y s).1 hs
    obtain ⟨δ', ε', hδ', hε', hε0', ⟨S', hS0, hSrec, hs'S⟩, hs'sum⟩ :=
      exists_partialSums_of_mem_run fp hfp (fun k => x (Fin.castSucc k))
        (fun k => y (Fin.castSucc k)) hs'
    obtain ⟨d, hd, hpd⟩ := hp.exists_delta
    obtain ⟨e, he, hse, he0⟩ : ∃ e, |e| ≤ fp.u ∧ s = (s' + p) * (1 + e) ∧ (n = 0 → e = 0) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hs'0 : s' = 0 := hs'S.trans hS0
        rw [hs'0, zero_add] at hsp
        refine ⟨0, by simp [fp.u_nonneg], ?_, fun _ => rfl⟩
        rw [hfp hp hsp, hs'0]
        ring
      · obtain ⟨e, he, hse⟩ := hsp.exists_delta
        exact ⟨e, he, hse, fun h => absurd h hn.ne'⟩
    refine ⟨Fin.snoc (α := fun _ => ℝ) δ' d, Fin.snoc (α := fun _ => ℝ) ε' e, fun k => ?_,
      fun k => ?_, fun k hk => ?_, ⟨fun k => if k ≤ n then S' k else s, by simp [hS0],
        fun q => ?_, by simp⟩, ?_⟩
    · induction k using Fin.lastCases with
      | last => simpa using hd
      | cast q => simpa using hδ' q
    · induction k using Fin.lastCases with
      | last => simpa using he
      | cast q => simpa using hε' q
    · induction k using Fin.lastCases with
      | last =>
        simp only [Fin.val_last] at hk
        simpa using he0 hk
      | cast q => simpa using hε0' q (by simpa using hk)
    · induction q using Fin.lastCases with
      | last =>
        simp only [Fin.val_last, Fin.snoc_last, le_refl, ↓reduceIte,
          show ¬ n + 1 ≤ n from Nat.not_succ_le_self n]
        rw [← hs'S, hse, hpd]
      | cast q =>
        have hq : (q : ℕ) + 1 ≤ n := q.isLt
        simp only [Fin.val_castSucc, Fin.snoc_castSucc, hq, q.isLt.le, ↓reduceIte]
        exact hSrec q
    · rw [Fin.sum_univ_castSucc, hse, hs'sum, hpd, add_mul, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun q _ => ?_
        simp only [Fin.snoc_castSucc, prod_Ici_castSucc, Fin.snoc_last]
        ring
      · simp only [Fin.snoc_last, prod_Ici_last]
        ring

/-- **(2.7.9)**: the rounding errors of the dot product (2.7.8). For every run `s` of
Algorithm 1.1.1 (the book's `fl(xᵀy)`) the partial sums `s_p = fl(∑_{k ≤ p} x_k y_k)` satisfy
`s₁ = x₁ y₁ (1 + δ₁)` and `s_p = (s_{p-1} + x_p y_p (1 + δ_p))(1 + ε_p)` for `p = 2:n`, with
`|δ_p|, |ε_p| ≤ u`, and `s = s_n` (0-based indices; `s₁` is exact up to `δ₁` because
`fl(0 + p) = p`, the hypothesis `fp.IsIdempotent`). -/
theorem equation_2_7_9 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ} (x y : Fin n → ℝ)
    {s : ℝ} (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    ∃ (δ ε : Fin n → ℝ) (S : ℕ → ℝ), (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
      (∀ p : Fin n, (p : ℕ) = 0 → S 1 = x p * y p * (1 + δ p)) ∧
      (∀ p : Fin n, (p : ℕ) ≠ 0 → S (p + 1) = (S p + x p * y p * (1 + δ p)) * (1 + ε p)) ∧
      s = S n := by
  obtain ⟨δ, ε, hδ, hε, hε0, ⟨S, hS0, hrec, hsS⟩, -⟩ := exists_partialSums_of_mem_run fp hfp x y hs
  refine ⟨δ, ε, S, hδ, hε, fun p hp => ?_, fun p _ => hrec p, hsS⟩
  simpa [hp, hS0, hε0 p hp] using hrec p

/-- **(2.7.10)**: every run `s` of Algorithm 1.1.1 is `fl(xᵀy) = ∑_k x_k y_k (1 + γ_k)` with
`1 + γ_k = (1 + δ_k) ∏_{j=k}^n (1 + ε_j)` (the convention `ε₁ = 0`), hence
`|fl(xᵀy) - xᵀy| ≤ ∑_k |x_k y_k| |γ_k|`. (The book's `γ_k` is not `FloatingPoint.gamma`.) -/
theorem equation_2_7_10 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ}
    (x y : Fin n → ℝ) {s : ℝ} (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    ∃ δ ε : Fin n → ℝ, (∀ k, |δ k| ≤ fp.u) ∧ (∀ k, |ε k| ≤ fp.u) ∧
      (∀ k : Fin n, (k : ℕ) = 0 → ε k = 0) ∧
      s = ∑ k, x k * y k * (1 + ((1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j) - 1)) ∧
      |s - x ⬝ᵥ y| ≤ ∑ k, |x k * y k| * |(1 + δ k) * ∏ j ∈ Finset.Ici k, (1 + ε j) - 1| := by
  obtain ⟨δ, ε, hδ, hε, hε0, -, hsum⟩ := exists_partialSums_of_mem_run fp hfp x y hs
  refine ⟨δ, ε, hδ, hε, hε0, by simpa using hsum, ?_⟩
  rw [hsum, dotProduct, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← abs_mul]
  exact le_of_eq (congrArg _ (by ring))

/-- **Lemma 2.7.1.** If `1 + α = ∏_{k=1}^n (1 + αₖ)` with `|αₖ| ≤ u` and `n u ≤ .01`, then
`|α| ≤ 1.01 n u`. -/
theorem lemma_2_7_1 {u : ℝ} (hu : 0 ≤ u) (α : Fin n → ℝ) (hα : ∀ k, |α k| ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 100) {a : ℝ} (ha : 1 + a = ∏ k, (1 + α k)) :
    |a| ≤ 101 / 100 * (n * u) := by
  have h := abs_prod_one_add_sub_one_le_of_mul_le hu hα hnu
  rwa [← ha, add_sub_cancel_left] at h

/-- **(2.7.11)**: under `n u ≤ .01`, every run `s` of Algorithm 1.1.1 satisfies
`|fl(xᵀy) - xᵀy| ≤ 1.01 n u |x|ᵀ|y|`: the product form bound `(1 + u)^n - 1`
(`FloatingPoint.abs_sub_le_one_add_pow_sub_one_of_roundsDot`) and Lemma 2.7.1. -/
theorem equation_2_7_11 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {n : ℕ}
    (x y : Fin n → ℝ) (hnu : (n : ℝ) * fp.u ≤ 1 / 100) {s : ℝ}
    (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    |s - x ⬝ᵥ y| ≤ 101 / 100 * (n * fp.u) * (|x| ⬝ᵥ |y|) := by
  have h := abs_sub_le_one_add_pow_sub_one_of_roundsDot
    (Chapter01.algorithm_1_1_1_rounds hfp x y s hs)
  rw [Fintype.card_fin] at h
  have hc : (1 + fp.u) ^ n - 1 ≤ 101 / 100 * (n * fp.u) := by
    have h1 := lemma_2_7_1 fp.u_nonneg (fun _ : Fin n => fp.u)
      (fun _ => (abs_of_nonneg fp.u_nonneg).le) hnu (a := (1 + fp.u) ^ n - 1) (by simp)
    exact (le_abs_self _).trans h1
  exact h.trans (mul_le_mul_of_nonneg_right hc
    (dotProduct_nonneg_of_nonneg (abs_nonneg x) (abs_nonneg y)))

/-- **(2.7.12)**, rigorous form of `|fl(xᵀy) - xᵀy| ≤ n u |x|ᵀ|y| + O(u²)`: every run `s` of
Algorithm 1.1.1 satisfies `|fl(xᵀy) - xᵀy| ≤ γ_n |x|ᵀ|y|`, `γ_n = n u / (1 - n u) = n u + O(u²)`,
when `n u < 1` and `fl(0 + p) = p` (`fp.IsIdempotent`); without the latter the first addition
costs one more rounding, `γ_{n+1}` (`FloatingPoint.abs_sub_le_of_mem_run_dotAccum`). -/
theorem equation_2_7_12 (fp : RoundingModel ℝ) {n : ℕ} (x y : Fin n → ℝ) {s : ℝ}
    (hs : s ∈ (Chapter01.algorithm_1_1_1 fp.round x y).run) :
    (fp.IsIdempotent → (n : ℝ) * fp.u < 1 → |s - x ⬝ᵥ y| ≤ gamma fp.u n * (|x| ⬝ᵥ |y|)) ∧
      (((n + 1 : ℕ) : ℝ) * fp.u < 1 →
        |s - x ⬝ᵥ y| ≤ gamma fp.u (n + 1) * (|x| ⬝ᵥ |y|)) := by
  refine ⟨fun hfp hnu => ?_, fun hnu => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hs0 : s = 0 := by simpa [Chapter01.algorithm_1_1_1] using hs
      simp [hs0, dotProduct]
    · have hu : fp.u < 1 := by
        have : fp.u ≤ n * fp.u :=
          le_mul_of_one_le_left fp.u_nonneg (by exact_mod_cast hn)
        linarith
      simpa using abs_sub_le_of_roundsDot hu (by simpa using hnu)
        (Chapter01.algorithm_1_1_1_rounds hfp x y s hs)
  · rw [Chapter01.algorithm_1_1_1_eq_dotAccum] at hs
    have h := abs_sub_le_of_mem_run_dotAccum (by simpa using hnu) hs
    simp only [List.length_finRange, zero_add, abs_zero] at h
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def] at h
    exact h

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

/-- **(2.7.17)**, rigorous form: every run `ŷ` of the saxpy, Algorithm 1.1.2, is
`fl(y + αx) = y + αx + z` with `|z| ≤ u |y| + (2u + u²) |αx|` (the book's
`u(|y| + 2|αx|) + O(u²)`): one rounded update per entry
(`FloatingPoint.abs_sub_le_of_rounds_add_mul`). -/
theorem equation_2_7_17 (fp : RoundingModel ℝ) (a : ℝ) (x y : Fin n → ℝ) {ŷ : Fin n → ℝ}
    (hŷ : ŷ ∈ (Chapter01.algorithm_1_1_2 fp.round a x y).run) :
    ∃ z : Fin n → ℝ, ŷ = y + a • x + z ∧
      |z| ≤ fp.u • |y| + (2 * fp.u + fp.u ^ 2) • |a • x| := by
  refine ⟨ŷ - (y + a • x), by abel, fun i => ?_⟩
  obtain ⟨p, hp, hs⟩ := (Chapter01.algorithm_1_1_2_mem_run fp a x y ŷ).1 hŷ i
  simpa using abs_sub_le_of_rounds_add_mul hp hs

/-- **(2.7.18)**, rigorous form: the outer product update `C + u vᵀ`, computed entrywise as
`fl(c_ij + fl(u_i v_j))` (a run of Algorithm 1.1.8 with inner dimension `1`), is
`fl(C + u vᵀ) = C + u vᵀ + E` with `|E| ≤ u |C| + (2u + u²) |u vᵀ|` (the book's
`u(|C| + 2|u vᵀ|) + O(u²)`). -/
theorem equation_2_7_18 (fp : RoundingModel ℝ) (C : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ)
    (v : Fin n → ℝ) {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_8 fp.round (replicateCol (Fin 1) u)
      (replicateRow (Fin 1) v) C).run) :
    ∃ E : Matrix (Fin m) (Fin n) ℝ, Ĉ = C + vecMulVec u v + E ∧
      E.abs ≤ₑ fp.u • C.abs + (2 * fp.u + fp.u ^ 2) • (vecMulVec u v).abs := by
  refine ⟨Ĉ - (C + vecMulVec u v), by abel, fun i j => ?_⟩
  have h := (Chapter01.algorithm_1_1_8_mem_run fp _ _ C Ĉ).1 hĈ i j
  simp only [dotAccum, List.finRange_succ, List.finRange_zero, List.map_nil, List.foldlM_cons,
    List.foldlM_nil, bind_pure, SetM.mem_run_bind, RoundingModel.mem_run_round,
    replicateCol_apply, replicateRow_apply] at h
  obtain ⟨p, hp, hs⟩ := h
  simpa [vecMulVec_apply] using abs_sub_le_of_rounds_add_mul hp hs

/-- The matrix-product bound `|Ĉ - AB| ≤ γ_r |A||B|` of a relational product, for every inner
dimension `r` with `r u < 1` (for `r = 0` both sides vanish). -/
private theorem abs_sub_entrywiseLE_of_roundsMul_fin (fp : RoundingModel ℝ) {r : ℕ}
    {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ} {Ĉ : Matrix (Fin m) (Fin n) ℝ}
    (hr : (r : ℝ) * fp.u < 1) (h : RoundsMul fp A B Ĉ) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · intro i j
    obtain ⟨o, p, -, -, -, hsum⟩ := h i j
    have ho : o = [] := List.eq_nil_iff_forall_not_mem.2 fun k => k.elim0
    subst ho
    have hC : Ĉ i j = 0 := hsum
    simp [hC]
  · have hu : fp.u < 1 := by
      have : fp.u ≤ r * fp.u := le_mul_of_one_le_left fp.u_nonneg (by exact_mod_cast hr0)
      linarith
    simpa using abs_sub_entrywiseLE_of_roundsMul hu (by simpa using hr) h

/-- **(2.7.19)**, rigorous form: every run `Ĉ` of the dot product matrix multiplication,
Algorithm 1.1.6 started at `C = 0` (inner dimension `r`, `r u < 1`, `fp.IsIdempotent`), is
`fl(AB) = AB + E` with `|E| ≤ γ_r |A||B|`, `γ_r = r u + O(u²)` (the book's `n u |A||B| + O(u²)`,
`n` the inner dimension): chapter 1's `algorithm_1_1_6_rounds` and
`FloatingPoint.abs_sub_entrywiseLE_of_roundsMul`. -/
theorem equation_2_7_19 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_6_rounds hfp A B Ĉ hĈ)

/-- **(2.7.19), "the same result applies if a gaxpy … procedure is used"**: every run of the
saxpy matrix multiplication, Algorithm 1.1.7 from `C = 0`, satisfies `|Ĉ - AB| ≤ γ_r |A||B|`
(`fp.IsIdempotent`, `r u < 1`): each entry is accumulated over `k = 1:r` in order. -/
theorem equation_2_7_19_saxpy (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_7 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_7_rounds hfp A B Ĉ hĈ)

/-- **(2.7.19), "… or outer product based procedure"**: every run of the outer product matrix
multiplication, Algorithm 1.1.8 from `C = 0`, satisfies `|Ĉ - AB| ≤ γ_r |A||B|`
(`fp.IsIdempotent`, `r u < 1`). -/
theorem equation_2_7_19_outer (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_8 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A.abs * B.abs) :=
  abs_sub_entrywiseLE_of_roundsMul_fin fp hr (Chapter01.algorithm_1_1_8_rounds hfp A B Ĉ hĈ)

/-- **(2.7.20)**, rigorous form: for the runs of (2.7.19),
`‖fl(AB) - AB‖₁ ≤ γ_r ‖A‖₁ ‖B‖₁` (the book's `n u ‖A‖₁ ‖B‖₁ + O(u²)`): the 1-norm is monotone in
`|·|`, submultiplicative, and `‖|A|‖₁ = ‖A‖₁`. -/
theorem equation_2_7_20 (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent) {r : ℕ}
    (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    lpOpNorm 1 (Ĉ - A * B) ≤ gamma fp.u r * (lpOpNorm 1 A * lpOpNorm 1 B) := by
  have h := equation_2_7_19 fp hfp A B hr hĈ
  have hγ : 0 ≤ gamma fp.u r := gamma_nonneg fp.u_nonneg hr
  have habs : ∀ {p q : ℕ} (X : Matrix (Fin p) (Fin q) ℝ), lpOpNorm 1 X.abs = lpOpNorm 1 X :=
    fun X => by
      rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
      exact linfty_opNorm_abs Xᵀ
  calc lpOpNorm 1 (Ĉ - A * B) ≤ gamma fp.u r * lpOpNorm 1 (A.abs * B.abs) := by
        rw [lpOpNorm_one_eq_linfty_opNorm_transpose, lpOpNorm_one_eq_linfty_opNorm_transpose]
        refine linfty_opNorm_le_mul_of_abs_entrywiseLE hγ fun i j => ?_
        simp only [Matrix.abs_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul]
        exact (h j i).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hγ)
    _ ≤ gamma fp.u r * (lpOpNorm 1 A.abs * lpOpNorm 1 B.abs) :=
        mul_le_mul_of_nonneg_left (lpOpNorm_mul_le 1 A.abs B.abs) hγ
    _ = gamma fp.u r * (lpOpNorm 1 A * lpOpNorm 1 B) := by rw [habs, habs]

/-- **§2.7.10**: "if `A ≥ 0` and `B ≥ 0`, then conventional matrix multiplication produces a
product `Ĉ` that has small componentwise relative error": for entrywise nonnegative `A`, `B`,
every run of (2.7.19) satisfies `|Ĉ - C| ≤ γ_r |C|`, `C = AB` (since `|A||B| = AB`). -/
theorem abs_sub_le_gamma_mul_abs_of_nonneg (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent)
    {r : ℕ} {A : Matrix (Fin m) (Fin r) ℝ} {B : Matrix (Fin r) (Fin n) ℝ}
    (hA : A.EntrywiseNonneg) (hB : B.EntrywiseNonneg) (hr : (r : ℝ) * fp.u < 1)
    {Ĉ : Matrix (Fin m) (Fin n) ℝ} (hĈ : Ĉ ∈ (Chapter01.algorithm_1_1_6 fp.round A B 0).run) :
    (Ĉ - A * B).abs ≤ₑ gamma fp.u r • (A * B).abs := by
  have h := equation_2_7_19 fp hfp A B hr hĈ
  have hAabs : A.abs = A := by
    ext i j
    exact abs_of_nonneg (hA i j)
  have hBabs : B.abs = B := by
    ext i j
    exact abs_of_nonneg (hB i j)
  rw [hAabs, hBabs] at h
  intro i j
  refine (h i j).trans ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.abs_apply]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (gamma_nonneg fp.u_nonneg hr)

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

/-- **§2.7.9, "it can be shown that"**: every run `Ĉ` of Algorithm 1.2.1 for `n = 2` (upper
triangular `A`, `B`, started at `C = 0`, `fp.IsIdempotent`) is
`fl(AB) = [a₁₁b₁₁(1+ε₁), (a₁₁b₁₂(1+ε₂) + a₁₂b₂₂(1+ε₃))(1+ε₄); 0, a₂₂b₂₂(1+ε₅)]` with `|εᵢ| ≤ u`
(0-based here); with `triangular_mul_two_backward` this is the backward error statement
`fl(AB) = Â B̂`. -/
theorem triangular_mul_two_backward_run (fp : RoundingModel ℝ) (hfp : fp.IsIdempotent)
    (a₁₁ a₁₂ a₂₂ b₁₁ b₁₂ b₂₂ : ℝ) {Ĉ : Matrix (Fin 2) (Fin 2) ℝ}
    (hĈ : Ĉ ∈ (Chapter01.algorithm_1_2_1 fp.round !![a₁₁, a₁₂; 0, a₂₂] !![b₁₁, b₁₂; 0, b₂₂]
      0).run) :
    ∃ ε : Fin 5 → ℝ, (∀ i, |ε i| ≤ fp.u) ∧
      Ĉ = !![a₁₁ * b₁₁ * (1 + ε 0),
        (a₁₁ * b₁₂ * (1 + ε 1) + a₁₂ * b₂₂ * (1 + ε 2)) * (1 + ε 3);
        0, a₂₂ * b₂₂ * (1 + ε 4)] := by
  have h' : ∃ p₁, fp.Rounds (a₁₁ * b₁₁) p₁ ∧ ∃ c₁, fp.Rounds p₁ c₁ ∧
      ∃ p₂, fp.Rounds (a₁₁ * b₁₂) p₂ ∧ ∃ c₂, fp.Rounds p₂ c₂ ∧
      ∃ p₃, fp.Rounds (a₁₂ * b₂₂) p₃ ∧ ∃ c₃, fp.Rounds (c₂ + p₃) c₃ ∧
      ∃ p₄, fp.Rounds (a₂₂ * b₂₂) p₄ ∧ ∃ c₄, fp.Rounds p₄ c₄ ∧
        ((0 : Matrix (Fin 2) (Fin 2) ℝ).updateRow 0
          (Function.update (Function.update ((0 : Matrix (Fin 2) (Fin 2) ℝ) 0) 0 c₁) 1
            c₃)).updateRow 1 (Function.update ((0 : Matrix (Fin 2) (Fin 2) ℝ) 1) 1 c₄) = Ĉ := by
    simpa (config := { decide := true }) [Chapter01.algorithm_1_2_1, List.finRange_succ,
      SetM.mem_run_bind, RoundingModel.mem_run_round] using hĈ
  obtain ⟨p₁, hp₁, c₁, hc₁, p₂, hp₂, c₂, hc₂, p₃, hp₃, c₃, hc₃, p₄, hp₄, c₄, hc₄, rfl⟩ := h'
  obtain rfl := hfp hp₁ hc₁
  obtain rfl := hfp hp₂ hc₂
  obtain rfl := hfp hp₄ hc₄
  obtain ⟨d₁, hd₁, rfl⟩ := hp₁.exists_delta
  obtain ⟨d₂, hd₂, rfl⟩ := hp₂.exists_delta
  obtain ⟨d₃, hd₃, rfl⟩ := hp₃.exists_delta
  obtain ⟨d₄, hd₄, rfl⟩ := hc₃.exists_delta
  obtain ⟨d₅, hd₅, rfl⟩ := hp₄.exists_delta
  refine ⟨![d₁, d₂, d₃, d₄, d₅], fun i => by fin_cases i <;> assumption, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [updateRow_apply]

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
