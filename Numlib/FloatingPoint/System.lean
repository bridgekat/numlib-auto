import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Log
import Mathlib.Basic.Sign.Basic
import Mathlib.Order.Interval.Finset.Nat
import Numlib.FloatingPoint.Model

/-!
# The floating-point number system `𝔽(β, t, L, U)`

The floating-point number system of [quarteroni2000numerical] §2.5.2–2.5.6, as a concrete instance
of the relational model of `Numlib/FloatingPoint/Model.lean`.

`FloatingPoint.System` bundles the parameters: base `β ≥ 2`, `t ≥ 1` significant digits, exponent
range `L ≤ U`. Everything else is stated over an ordered field `K` (`[Field K] [LinearOrder K]
[IsStrictOrderedRing K]`, with `[FloorRing K]` where the rounding functions are defined), never
over `ℝ` alone, so that the system can be instantiated on `ℚ` for decidable examples and on `ℝ`
for analysis. `System.numbers s K : Set K` is the set of *normalized* numbers `± m β^(e - t)` with
an integer mantissa `β^(t-1) ≤ m ≤ β^t - 1` and exponent `L ≤ e ≤ U`, together with `0`, in the
book's mantissa convention `x = ± 0.a₁…a_t × β^e`, so that a number of exponent `e` lies in the
binade `[β^(e-1), β^e)`; `System.denormalized s K` are the numbers `± m β^(L - t)` with `1 ≤ m <
β^(t-1)`. `xmin = β^(L-1)`, `xmax = β^U (1 - β^(-t))`, `machineEps = β^(1-t)`, `unitRoundoff = ½
β^(1-t)`, `exponent x = Int.log β |x| + 1`, `mantissa x = |x| β^(t - exponent x)` and `ulp x =
β^(exponent x - t)` are the book's quantities.

**Rounding is a total function.** `System.round s : K → K` rounds the mantissa to the nearest
integer with Mathlib's `round` (halves up, which is the book's digit rule `a_{t+1} ≥ β/2 ↦ a_t +
1` for even `β`) and restores sign and exponent; `System.chop` truncates it instead. The exponent
range is *not* consulted by the rounding function, so the relative error bound holds
unconditionally — `|round x - x| ≤ u |x|` for every `x` (`System.abs_round_sub_le`), which is
[higham2002accuracy] Theorem 2.2 "barring overflow and underflow" — and the book's range
hypothesis `x_min ≤ |x| ≤ x_max` is exactly what makes `round x ∈ 𝔽` (`System.round_mem_numbers`).
Consequently `System.roundingModel s K : RoundingModel K` (`Rounds x y := y = round x`, `u =
unitRoundoff`) is total and functional, and every theorem of `Numlib/FloatingPoint/InnerProduct`
and `Numlib/FloatingPoint/Stationary` specializes to the computed values of `𝔽` with no side
conditions; overflow is the separate statement `System.round_notMem_numbers`.
`System.choppingModel` is the same with `u = machineEps`.

**Machine operations** are `System.op s f x y = round (f (round x) (round y))` for an exact
operation `f`, with `add`, `sub`, `mul`, `div` as abbreviations. On machine numbers `op f x y =
round (f x y)`, whence the standard model `x ∘ y = (x ∘ y)(1 + δ)` for every operation at once
(`System.exists_op_eq_mul_one_add`); the error of a sum of arbitrary operands and of two chained
sums are stated with their second-order terms explicit (`System.abs_add_sub_le`,
`System.abs_add_add_sub_le`). The round-digit discussion of [quarteroni2000numerical] §2.5.6 is
about hardware and has no counterpart here: in this idealization the exact result is rounded.

Also here: the density of finite positional expansions (`exists_int_mul_zpow_sub_abs_lt`,
[quarteroni2000numerical] §2.5.1), the IEC 559 / IEEE 754 parameter sets `System.ieeeSingle`
and `System.ieeeDouble` ([quarteroni2000numerical] §2.5.4), and the monotonicity of Mathlib's
`round` (`FloatingPoint.monotone_round`), which Mathlib lacks.

Searched and not reused: Mathlib's `Mathlib/Data/FP/Basic.lean` (an `unsafe`, theorem-free
`FP.Float`); `Int.log` and `round` are reused.
-/

open Finset

namespace FloatingPoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Two facts about Mathlib's `round` and about positional expansions -/

/-- Rounding to the nearest integer is monotone (a fact Mathlib lacks; `round x = ⌊x + 1/2⌋`). -/
theorem monotone_round [FloorRing K] : Monotone (round : K → ℤ) := fun x y hxy => by
  rw [round_eq, round_eq]
  exact Int.floor_mono (by linarith)

/-- `|sign x| ≤ 1`, the sign cast into the field. -/
theorem abs_coe_sign_le_one (x : K) : |(SignType.sign x : K)| ≤ 1 := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [sign_neg h]
  · simp
  · simp [sign_pos h]

/-- **Density of finite positional expansions** ([quarteroni2000numerical] §2.5.1): in an
Archimedean ordered field, every `x` is within `ε` of a number `m β^(-k)` with finitely many
digits in base `β ≥ 2`. -/
theorem exists_int_mul_zpow_sub_abs_lt [Archimedean K] {β : ℕ} (hβ : 2 ≤ β) (x : K) {ε : K}
    (hε : 0 < ε) : ∃ (m : ℤ) (k : ℕ), |m * (β : K) ^ (-(k : ℤ)) - x| < ε := by
  have hβ1 : (1 : K) < β := by exact_mod_cast hβ
  have hβ0 : (0 : K) < β := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hβ1)
  obtain ⟨m, hm⟩ := exists_floor (x * (β : K) ^ k)
  have h1 : (m : K) ≤ x * (β : K) ^ k := (hm m).1 le_rfl
  have h2 : x * (β : K) ^ k < m + 1 := by
    have : ¬ ((m + 1 : ℤ) : K) ≤ x * (β : K) ^ k := fun h => by
      have := (hm (m + 1)).2 h
      omega
    push_cast at this
    exact lt_of_not_ge this
  refine ⟨m, k, ?_⟩
  have hpos : (0 : K) < (β : K) ^ k := pow_pos hβ0 k
  have hkey : (m : K) * (β : K) ^ (-(k : ℤ)) - x
      = ((m : K) - x * (β : K) ^ k) * ((β : K)⁻¹) ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
    field_simp
  rw [hkey, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hβ0) k)]
  calc |(m : K) - x * (β : K) ^ k| * ((β : K)⁻¹) ^ k ≤ 1 * ((β : K)⁻¹) ^ k := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
    _ < ε := by rw [one_mul]; exact hk

/-! ### The parameters -/

/-- The parameters of a floating-point number system `𝔽(β, t, L, U)` ([quarteroni2000numerical]
§2.5.2): base `β ≥ 2`, `t ≥ 1` significant digits, exponent range `L ≤ e ≤ U`. -/
structure System where
  /-- The base. -/
  β : ℕ
  /-- The number of significant digits. -/
  t : ℕ
  /-- The smallest exponent. -/
  L : ℤ
  /-- The largest exponent. -/
  U : ℤ
  /-- The base is at least `2`. -/
  two_le_β : 2 ≤ β
  /-- There is at least one significant digit. -/
  one_le_t : 1 ≤ t
  /-- The exponent range is nonempty. -/
  L_le_U : L ≤ U

namespace System

variable (s : System)

/-- `1 < β`. -/
theorem one_lt_β : 1 < s.β := s.two_le_β

/-- `0 < β`. -/
theorem β_pos : 0 < s.β := by have := s.two_le_β; omega

/-- `1 < β` in `K`. -/
theorem one_lt_β_cast : (1 : K) < s.β := by exact_mod_cast s.one_lt_β

/-- `0 < β` in `K`. -/
theorem β_cast_pos : (0 : K) < s.β := by exact_mod_cast s.β_pos

/-- `β ≠ 0` in `K`. -/
theorem β_cast_ne_zero : (s.β : K) ≠ 0 := s.β_cast_pos.ne'

/-- `1 ≤ β` in `K`. -/
theorem one_le_β_cast : (1 : K) ≤ s.β := s.one_lt_β_cast.le

/-- Every integer power of the base is positive. -/
theorem zpow_β_pos (e : ℤ) : 0 < (s.β : K) ^ e := zpow_pos s.β_cast_pos e

/-- Every integer power of the base is nonnegative. -/
theorem zpow_β_nonneg (e : ℤ) : 0 ≤ (s.β : K) ^ e := (s.zpow_β_pos e).le

/-- `0 ≤ m β^e` for a natural mantissa `m`. -/
theorem natCast_mul_zpow_nonneg (m : ℕ) (e : ℤ) : 0 ≤ (m : K) * (s.β : K) ^ e :=
  mul_nonneg (Nat.cast_nonneg _) (s.zpow_β_nonneg e)

/-- `|σ m β^e| = m β^e` for a sign `σ = ±1`. -/
theorem abs_units_mul (σ : ℤˣ) (m : ℕ) (e : ℤ) :
    |((σ : ℤ) : K) * m * (s.β : K) ^ e| = m * (s.β : K) ^ e := by
  rw [mul_assoc, abs_mul, abs_unit_intCast, one_mul, abs_of_nonneg (s.natCast_mul_zpow_nonneg m e)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `β^(t-1)`, cast, is `β ^ ((t : ℤ) - 1)`. -/
theorem natCast_pow_t_sub_one : ((s.β ^ (s.t - 1) : ℕ) : K) = (s.β : K) ^ ((s.t : ℤ) - 1) := by
  rw [Nat.cast_pow, ← zpow_natCast, Nat.cast_pred s.one_le_t]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `β^t`, cast, is `β ^ (t : ℤ)`. -/
theorem natCast_pow_t : ((s.β ^ s.t : ℕ) : K) = (s.β : K) ^ (s.t : ℤ) := by
  rw [Nat.cast_pow, zpow_natCast]

/-- A mantissa bounded by `β^t - 1` satisfies `m + 1 ≤ β^t` in `K`. -/
theorem natCast_add_one_le_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) :
    (m : K) + 1 ≤ (s.β : K) ^ (s.t : ℤ) := by
  have h : m + 1 ≤ s.β ^ s.t := by
    have := Nat.one_le_pow s.t s.β s.β_pos
    omega
  rw [← s.natCast_pow_t]
  exact_mod_cast h

/-- A mantissa bounded by `β^t - 1` is `< β^t` in `K`. -/
theorem natCast_lt_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) : (m : K) < (s.β : K) ^ (s.t : ℤ) :=
  (lt_add_one _).trans_le (s.natCast_add_one_le_zpow hm)

/-- A normalized mantissa is `≥ β^(t-1)` in `K`. -/
theorem zpow_le_natCast {m : ℕ} (hm : s.β ^ (s.t - 1) ≤ m) :
    (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m := by
  rw [← s.natCast_pow_t_sub_one]
  exact_mod_cast hm

/-- The lower bound of a binade: `β^(t-1) ≤ m` gives `β^(e-1) ≤ m β^(e-t)`. -/
theorem zpow_sub_one_le_mul_zpow {m : K} (hm : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m) (e : ℤ) :
    (s.β : K) ^ (e - 1) ≤ m * (s.β : K) ^ (e - s.t) := by
  have h : (s.β : K) ^ (e - 1) = (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ (e - s.t) := by
    rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  rw [h]
  exact mul_le_mul_of_nonneg_right hm (s.zpow_β_nonneg _)

/-- The upper bound of a binade: `m < β^t` gives `m β^(e-t) < β^e`. -/
theorem mul_zpow_lt_zpow {m : K} (hm : m < (s.β : K) ^ (s.t : ℤ)) (e : ℤ) :
    m * (s.β : K) ^ (e - s.t) < (s.β : K) ^ e := by
  have h : (s.β : K) ^ e = (s.β : K) ^ (s.t : ℤ) * (s.β : K) ^ (e - s.t) := by
    rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  rw [h]
  exact mul_lt_mul_of_pos_right hm (s.zpow_β_pos _)

/-- The binades `[β^(e-1), β^e)` are disjoint: a number lying in two of them has `e = e'`. -/
theorem eq_of_zpow_sub_one_le_of_lt {e e' : ℤ} {y : K} (h1 : (s.β : K) ^ (e - 1) ≤ y)
    (h2 : y < (s.β : K) ^ e) (h1' : (s.β : K) ^ (e' - 1) ≤ y) (h2' : y < (s.β : K) ^ e') :
    e = e' := by
  have hβ := s.one_lt_β_cast (K := K)
  have a : e - 1 < e' := (zpow_lt_zpow_iff_right₀ hβ).1 (h1.trans_lt h2')
  have b : e' - 1 < e := (zpow_lt_zpow_iff_right₀ hβ).1 (h1'.trans_lt h2)
  omega

/-! ### The numbers -/

/-- The **normalized floating-point numbers** `𝔽(β, t, L, U)` ([quarteroni2000numerical] §2.5.2):
`0` together with the numbers `± m β^(e - t)` with an integer mantissa `β^(t-1) ≤ m ≤ β^t - 1`
(the normalization `a₁ ≠ 0` of the book's digit string `m = a₁a₂…a_t`) and an exponent `L ≤ e ≤
U`. -/
def numbers (s : System) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Set K :=
  {x | x = 0 ∨ ∃ (σ : ℤˣ) (m : ℕ) (e : ℤ), s.β ^ (s.t - 1) ≤ m ∧ m ≤ s.β ^ s.t - 1 ∧
    s.L ≤ e ∧ e ≤ s.U ∧ x = ((σ : ℤ) : K) * m * (s.β : K) ^ (e - s.t)}

/-- The **de-normalized numbers** `𝔽_D` ([quarteroni2000numerical] §2.5.2): the numbers `± m
β^(L - t)` with a mantissa `1 ≤ m ≤ β^(t-1) - 1` below the normalization threshold, at the
minimum exponent `L`. -/
def denormalized (s : System) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Set K :=
  {x | ∃ (σ : ℤˣ) (m : ℕ), 1 ≤ m ∧ m ≤ s.β ^ (s.t - 1) - 1 ∧
    x = ((σ : ℤ) : K) * m * (s.β : K) ^ (s.L - s.t)}

/-- `x_min = β^(L-1)`, the smallest positive normalized number ([quarteroni2000numerical]
(2.30)). -/
noncomputable def xmin (s : System) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    K := (s.β : K) ^ (s.L - 1)

/-- `x_max = β^U (1 - β^(-t))`, the largest normalized number ([quarteroni2000numerical]
(2.30)). -/
noncomputable def xmax (s : System) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    K := (s.β : K) ^ s.U * (1 - (s.β : K) ^ (-(s.t : ℤ)))

/-- The **machine epsilon** `ε_M = β^(1-t)` ([quarteroni2000numerical] §2.5.3), the spacing of
the numbers of `𝔽` in the binade `[1, β)`. -/
noncomputable def machineEps (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : K := (s.β : K) ^ (1 - (s.t : ℤ))

/-- The **roundoff unit** `u = ½ β^(1-t) = ½ ε_M` ([quarteroni2000numerical] (2.34)), the
relative error bound of rounding to nearest. -/
noncomputable def unitRoundoff (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : K := (1 / 2 : K) * (s.β : K) ^ (1 - (s.t : ℤ))

/-- `0 < x_min`. -/
theorem xmin_pos : 0 < s.xmin K := s.zpow_β_pos _

/-- `0 < ε_M`. -/
theorem machineEps_pos : 0 < s.machineEps K := s.zpow_β_pos _

/-- `0 < u`. -/
theorem unitRoundoff_pos : 0 < s.unitRoundoff K := by
  rw [unitRoundoff]; exact mul_pos (by norm_num) (s.zpow_β_pos _)

/-- `0 ≤ u`. -/
theorem unitRoundoff_nonneg : 0 ≤ s.unitRoundoff K := s.unitRoundoff_pos.le

/-- `u = ε_M / 2`. -/
theorem unitRoundoff_eq_machineEps_div_two : s.unitRoundoff K = s.machineEps K / 2 := by
  rw [unitRoundoff, machineEps]; ring

/-- `x_max = β^U - β^(U-t)`. -/
theorem xmax_eq_sub : s.xmax K = (s.β : K) ^ s.U - (s.β : K) ^ (s.U - s.t) := by
  rw [xmax, mul_sub, mul_one, ← zpow_add₀ s.β_cast_ne_zero, ← sub_eq_add_neg]

/-- `x_max = (β^t - 1) β^(U-t)`. -/
theorem xmax_eq_mul : s.xmax K = ((s.β : K) ^ (s.t : ℤ) - 1) * (s.β : K) ^ (s.U - s.t) := by
  rw [xmax_eq_sub, sub_mul, one_mul, ← zpow_add₀ s.β_cast_ne_zero, add_sub_cancel]

/-- `x_max < β^U`. -/
theorem xmax_lt_zpow : s.xmax K < (s.β : K) ^ s.U := by
  rw [xmax_eq_sub]
  linarith [zpow_pos (s.β_cast_pos (K := K)) (s.U - s.t)]

/-- `0 < x_max`. -/
theorem xmax_pos : 0 < s.xmax K := by
  rw [xmax_eq_mul]
  refine mul_pos ?_ (s.zpow_β_pos _)
  linarith [one_lt_zpow₀ (s.one_lt_β_cast (K := K)) (by exact_mod_cast s.one_le_t : (0 : ℤ) < s.t)]

/-- Membership in `𝔽` through the absolute value: `x ∈ 𝔽` iff `x = 0` or `|x| = m β^(e-t)` for a
normalized mantissa `m` and an admissible exponent `e`. -/
theorem mem_numbers_iff_abs {x : K} :
    x ∈ s.numbers K ↔ x = 0 ∨ ∃ (m : ℕ) (e : ℤ), s.β ^ (s.t - 1) ≤ m ∧ m ≤ s.β ^ s.t - 1 ∧
      s.L ≤ e ∧ e ≤ s.U ∧ |x| = m * (s.β : K) ^ (e - s.t) := by
  constructor
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨m, e, hm1, hm2, hL, hU, s.abs_units_mul σ m _⟩
  · rintro (rfl | ⟨m, e, hm1, hm2, hL, hU, hx⟩)
    · exact Or.inl rfl
    · rcases le_or_gt 0 x with h | h
      · exact Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by rw [mul_assoc, ← hx, abs_of_nonneg h]; simp⟩
      · exact Or.inr ⟨-1, m, e, hm1, hm2, hL, hU, by rw [mul_assoc, ← hx, abs_of_neg h]; simp⟩

/-- `0 ∈ 𝔽`. -/
theorem zero_mem_numbers : (0 : K) ∈ s.numbers K := Or.inl rfl

/-- `𝔽` is closed under negation ([quarteroni2000numerical] §2.5.2). -/
theorem neg_mem_numbers {x : K} (hx : x ∈ s.numbers K) : -x ∈ s.numbers K := by
  rw [mem_numbers_iff_abs] at hx ⊢
  simpa [neg_eq_zero, abs_neg] using hx

/-- A nonzero normalized number of exponent `e` lies in the binade `[β^(e-1), β^e)`: the lower
bound. -/
theorem zpow_sub_one_le_natCast_mul_zpow {m : ℕ} (hm : s.β ^ (s.t - 1) ≤ m) (e : ℤ) :
    (s.β : K) ^ (e - 1) ≤ m * (s.β : K) ^ (e - s.t) :=
  s.zpow_sub_one_le_mul_zpow (s.zpow_le_natCast hm) e

/-- A normalized number of exponent `e` lies in the binade `[β^(e-1), β^e)`: the upper bound. -/
theorem natCast_mul_zpow_lt_zpow {m : ℕ} (hm : m ≤ s.β ^ s.t - 1) (e : ℤ) :
    m * (s.β : K) ^ (e - s.t) < (s.β : K) ^ e :=
  s.mul_zpow_lt_zpow (s.natCast_lt_zpow hm) e

/-- **[quarteroni2000numerical] (2.30), lower bound**: `x_min ≤ |x|` for nonzero `x ∈ 𝔽`. -/
theorem xmin_le_abs {x : K} (hx : x ∈ s.numbers K) (h0 : x ≠ 0) : s.xmin K ≤ |x| := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, hm1, _, hL, _, hxe⟩
  · exact absurd rfl h0
  · rw [hxe, xmin]
    exact (zpow_le_zpow_right₀ s.one_le_β_cast (by omega)).trans
      (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)

/-- **[quarteroni2000numerical] (2.30), upper bound**: `|x| ≤ x_max` for `x ∈ 𝔽`. -/
theorem abs_le_xmax {x : K} (hx : x ∈ s.numbers K) : |x| ≤ s.xmax K := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, _, hm2, _, hU, hxe⟩
  · simpa using s.xmax_pos.le
  · rw [hxe, xmax_eq_mul]
    have h1 : (m : K) ≤ (s.β : K) ^ (s.t : ℤ) - 1 := by
      linarith [s.natCast_add_one_le_zpow (K := K) hm2]
    have h2 : (s.β : K) ^ (e - s.t) ≤ (s.β : K) ^ (s.U - s.t) :=
      zpow_le_zpow_right₀ s.one_le_β_cast (by omega)
    exact mul_le_mul h1 h2 (s.zpow_β_nonneg _) (by linarith)

/-- The normalized representation is injective in `(m, e)`: two normalized mantissas with
`m β^(e-t) = m' β^(e'-t)` have `m = m'` and `e = e'`. -/
theorem natCast_mul_zpow_eq_iff {m m' : ℕ} {e e' : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) (hm1' : s.β ^ (s.t - 1) ≤ m') (hm2' : m' ≤ s.β ^ s.t - 1) :
    (m : K) * (s.β : K) ^ (e - s.t) = m' * (s.β : K) ^ (e' - s.t) ↔ m = m' ∧ e = e' := by
  constructor
  · intro h
    have he : e = e' :=
      s.eq_of_zpow_sub_one_le_of_lt (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)
        (s.natCast_mul_zpow_lt_zpow hm2 e) (h ▸ s.zpow_sub_one_le_natCast_mul_zpow hm1' e')
        (h ▸ s.natCast_mul_zpow_lt_zpow hm2' e')
    subst he
    refine ⟨?_, rfl⟩
    exact_mod_cast mul_right_cancel₀ (zpow_ne_zero _ s.β_cast_ne_zero) h
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Uniqueness of the normalized representation** ([quarteroni2000numerical] §2.5.2, "to enforce
uniqueness … `a₁ ≠ 0`"): a nonzero `x` is in `𝔽` iff it has exactly one representation `x = σ m
β^(e-t)` with `σ = ±1`, a normalized mantissa `m` and an admissible exponent `e`. -/
theorem mem_numbers_iff_exists_unique {x : K} (hx : x ≠ 0) :
    x ∈ s.numbers K ↔ ∃! p : ℤˣ × ℕ × ℤ, s.β ^ (s.t - 1) ≤ p.2.1 ∧ p.2.1 ≤ s.β ^ s.t - 1 ∧
      s.L ≤ p.2.2 ∧ p.2.2 ≤ s.U ∧ x = ((p.1 : ℤ) : K) * p.2.1 * (s.β : K) ^ (p.2.2 - s.t) := by
  constructor
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact absurd rfl hx
    · refine ⟨(σ, m, e), ⟨hm1, hm2, hL, hU, rfl⟩, ?_⟩
      rintro ⟨σ', m', e'⟩ ⟨hm1', hm2', -, -, h⟩
      dsimp only at hm1' hm2' h
      have habs : (m : K) * (s.β : K) ^ (e - s.t) = m' * (s.β : K) ^ (e' - s.t) := by
        have := congrArg abs h
        rwa [s.abs_units_mul, s.abs_units_mul] at this
      have hne : (m : K) * (s.β : K) ^ (e - s.t) ≠ 0 :=
        ((s.zpow_β_pos _).trans_le (s.zpow_sub_one_le_natCast_mul_zpow hm1 e)).ne'
      obtain ⟨hm, he⟩ := (s.natCast_mul_zpow_eq_iff hm1 hm2 hm1' hm2').1 habs
      subst hm he
      have hσ : ((σ : ℤ) : K) = ((σ' : ℤ) : K) := by
        rw [mul_assoc, mul_assoc] at h
        exact mul_right_cancel₀ hne h
      rw [Units.ext (Int.cast_injective hσ)]
  · rintro ⟨⟨σ, m, e⟩, ⟨hm1, hm2, hL, hU, h⟩, -⟩
    exact Or.inr ⟨σ, m, e, hm1, hm2, hL, hU, h⟩

/-! ### The cardinality -/

/-- `𝔽` as a finset: `{0}` together with the images of the mantissa–exponent rectangle under `(m, e)
↦ m β^(e-t)` and `(m, e) ↦ -(m β^(e-t))`. -/
def finset (s : System) (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Finset K :=
  {0} ∪ (Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U).image
      (fun p : ℕ × ℤ => (p.1 : K) * (s.β : K) ^ (p.2 - s.t)) ∪
    (Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U).image
      (fun p : ℕ × ℤ => -((p.1 : K) * (s.β : K) ^ (p.2 - s.t)))

/-- The finset `System.finset` is the set `System.numbers`. -/
theorem coe_finset : (s.finset K : Set K) = s.numbers K := by
  ext x
  simp only [finset, coe_union, coe_singleton, coe_image, coe_product, coe_Icc, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_image, Set.mem_prod, Set.mem_Icc, Prod.exists]
  constructor
  · rintro ((rfl | ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, rfl⟩) | ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by simp⟩
    · exact Or.inr ⟨-1, m, e, hm1, hm2, hL, hU, by simp⟩
  · rintro (rfl | ⟨σ, m, e, hm1, hm2, hL, hU, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · rcases Int.units_eq_one_or σ with rfl | rfl
      · exact Or.inl (Or.inr ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, by simp⟩)
      · exact Or.inr ⟨m, e, ⟨⟨hm1, hm2⟩, hL, hU⟩, by simp⟩

/-- **The cardinality of `𝔽`** ([quarteroni2000numerical] §2.5.2): `card 𝔽 = 2 (β - 1) β^(t-1) (U
- L + 1) + 1`. -/
theorem card_finset :
    ((s.finset K).card : ℤ)
      = 2 * ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) + 1 := by
  set R := Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) ×ˢ Icc s.L s.U with hR
  set f : ℕ × ℤ → K := fun p => (p.1 : K) * (s.β : K) ^ (p.2 - s.t) with hf
  have hfpos : ∀ p ∈ R, 0 < f p := by
    rintro ⟨m, e⟩ hp
    simp only [hR, mem_product, mem_Icc] at hp
    exact (s.zpow_β_pos _).trans_le (s.zpow_sub_one_le_natCast_mul_zpow hp.1.1 e)
  have hinj : Set.InjOn f R := by
    rintro ⟨m, e⟩ hp ⟨m', e'⟩ hp' h
    simp only [hR, coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc] at hp hp'
    obtain ⟨rfl, rfl⟩ := (s.natCast_mul_zpow_eq_iff hp.1.1 hp.1.2 hp'.1.1 hp'.1.2).1 h
    rfl
  have hinj' : Set.InjOn (fun p => -f p) R := fun p hp p' hp' h => hinj hp hp' (neg_injective h)
  have hd1 : Disjoint ({0} : Finset K) (R.image f) := by
    rw [disjoint_singleton_left, mem_image]
    rintro ⟨p, hp, h⟩
    exact (hfpos p hp).ne' h
  have hd2 : Disjoint ({0} ∪ R.image f) (R.image fun p => -f p) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx'
    rcases mem_union.1 hx with h | h
    · exact (hfpos p hp).ne' (by simpa using h)
    · obtain ⟨q, hq, hq'⟩ := mem_image.1 h
      linarith [hfpos p hp, hfpos q hq]
  have hcard : (s.finset K).card = 1 + R.card + R.card := by
    rw [finset, ← hR, ← hf, card_union_of_disjoint hd2, card_union_of_disjoint hd1,
      card_singleton, card_image_of_injOn hinj, card_image_of_injOn hinj']
  have hRcard : (R.card : ℤ) = ((s.β : ℤ) - 1) * (s.β : ℤ) ^ (s.t - 1) * (s.U - s.L + 1) := by
    rw [hR, card_product, Nat.card_Icc, Int.card_Icc, Nat.cast_mul,
      Int.toNat_of_nonneg (by linarith [s.L_le_U])]
    obtain ⟨t', ht'⟩ := Nat.exists_eq_add_of_le' s.one_le_t
    have h1 : 1 ≤ s.β ^ s.t := Nat.one_le_pow _ _ s.β_pos
    have h2 : s.β ^ (s.t - 1) ≤ s.β ^ s.t := Nat.pow_le_pow_right s.β_pos (by omega)
    rw [Nat.sub_add_cancel h1, Nat.cast_sub h2]
    rw [ht', Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  rw [hcard]
  push_cast
  rw [hRcard]
  ring

/-! ### The distribution of the numbers -/

/-- **The binade is an arithmetic progression** ([quarteroni2000numerical] §2.5.3): for `L ≤ e ≤
U`, the numbers of `𝔽` in `[β^(e-1), β^e)` are exactly `m β^(e-t)` for `β^(t-1) ≤ m ≤ β^t - 1`,
equally spaced at distance `β^(e-t)`. -/
theorem numbers_inter_Ico {e : ℤ} (hL : s.L ≤ e) (hU : e ≤ s.U) :
    s.numbers K ∩ Set.Ico ((s.β : K) ^ (e - 1)) ((s.β : K) ^ e) =
      (fun m : ℕ => (m : K) * (s.β : K) ^ (e - s.t)) ''
        Set.Icc (s.β ^ (s.t - 1)) (s.β ^ s.t - 1) := by
  ext x
  constructor
  · rintro ⟨hx, hx1, hx2⟩
    have hpos : 0 < x := (s.zpow_β_pos _).trans_le hx1
    rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e', hm1, hm2, _, _, hxe⟩
    · exact absurd hpos (lt_irrefl 0)
    · rw [abs_of_pos hpos] at hxe
      have he : e = e' :=
        s.eq_of_zpow_sub_one_le_of_lt hx1 hx2 (hxe ▸ s.zpow_sub_one_le_natCast_mul_zpow hm1 e')
          (hxe ▸ s.natCast_mul_zpow_lt_zpow hm2 e')
      subst he
      exact ⟨m, ⟨hm1, hm2⟩, hxe.symm⟩
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    refine ⟨Or.inr ⟨1, m, e, hm1, hm2, hL, hU, by simp⟩, s.zpow_sub_one_le_natCast_mul_zpow hm1 e,
      s.natCast_mul_zpow_lt_zpow hm2 e⟩

/-- No number of `𝔽` lies strictly between `1` and `1 + ε_M`: a positive `δ` with `1 + δ ∈ 𝔽` is
at least the machine epsilon. This half of [quarteroni2000numerical] §2.5.3's characterization
of `ε_M` needs no hypothesis on the exponent range. -/
theorem machineEps_le_of_one_add_mem {δ : K} (hδ : 0 < δ) (h : 1 + δ ∈ s.numbers K) :
    s.machineEps K ≤ δ := by
  have hβ := s.one_lt_β_cast (K := K)
  rcases s.mem_numbers_iff_abs.1 h with h0 | ⟨m, e, hm1, hm2, _, _, hxe⟩
  · linarith
  · rw [abs_of_pos (by linarith)] at hxe
    have hlow := s.zpow_sub_one_le_natCast_mul_zpow (K := K) hm1 e
    have hup := s.natCast_mul_zpow_lt_zpow (K := K) hm2 e
    rw [← hxe] at hlow hup
    have he0 : 0 < e := by
      have : (s.β : K) ^ (0 : ℤ) < (s.β : K) ^ e := by rw [zpow_zero]; linarith
      exact (zpow_lt_zpow_iff_right₀ hβ).1 this
    rcases lt_or_eq_of_le (show (1 : ℤ) ≤ e by omega) with he | he
    · -- exponent at least `2`: `1 + δ ≥ β ≥ 2`
      have : (s.β : K) ^ (1 : ℤ) ≤ (s.β : K) ^ (e - 1) := zpow_le_zpow_right₀ hβ.le (by omega)
      rw [zpow_one] at this
      have hε1 : s.machineEps K ≤ 1 :=
        zpow_le_one_of_nonpos₀ hβ.le (by linarith [(by exact_mod_cast s.one_le_t : (1 : ℤ) ≤ s.t)])
      have h2 : (2 : K) ≤ s.β := by exact_mod_cast s.two_le_β
      linarith
    · -- exponent `1`: `1 + δ = m β^(1-t)` with `m > β^(t-1)`
      subst he
      have hone : (1 : K) = (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ ((1 : ℤ) - s.t) := by
        rw [← zpow_add₀ s.β_cast_ne_zero]; simp
      have hlt : ((s.β ^ (s.t - 1) : ℕ) : K) < m := by
        rw [s.natCast_pow_t_sub_one]
        by_contra hcon
        have := mul_le_mul_of_nonneg_right (not_lt.1 hcon) (s.zpow_β_nonneg ((1 : ℤ) - s.t))
        linarith
      have hlt' : s.β ^ (s.t - 1) + 1 ≤ m := by exact_mod_cast hlt
      have hle : ((s.β ^ (s.t - 1) : ℕ) : K) + 1 ≤ m := by exact_mod_cast hlt'
      rw [s.natCast_pow_t_sub_one] at hle
      have := mul_le_mul_of_nonneg_right hle (s.zpow_β_nonneg ((1 : ℤ) - s.t))
      rw [add_mul, one_mul] at this
      rw [machineEps]
      linarith

/-- `1 + ε_M ∈ 𝔽` when the exponent `1` is admissible and `t ≥ 2`. (For `t = 1` and `β = 2` the
number `1 + ε_M = 2` has exponent `2`, so the statement needs `U ≥ 2` instead.) -/
theorem one_add_machineEps_mem (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    1 + s.machineEps K ∈ s.numbers K := by
  refine Or.inr ⟨1, s.β ^ (s.t - 1) + 1, 1, by omega, ?_, hL, hU, ?_⟩
  · obtain ⟨t', ht'⟩ := Nat.exists_eq_add_of_le' s.one_le_t
    have hβ := s.two_le_β
    have h2 : 2 ≤ s.β ^ t' := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t' := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ s.β ^ t' := Nat.pow_le_pow_left hβ t'
    rw [ht', Nat.add_sub_cancel, pow_succ]
    have : 2 * s.β ^ t' ≤ s.β ^ t' * s.β := by nlinarith
    omega
  · rw [machineEps, Nat.cast_add, Nat.cast_one, s.natCast_pow_t_sub_one, Units.val_one,
      Int.cast_one, one_mul, add_mul, one_mul, ← zpow_add₀ s.β_cast_ne_zero,
      show (s.t : ℤ) - 1 + (1 - s.t) = 0 by ring, zpow_zero]

/-- **The machine epsilon is the gap above `1`** ([quarteroni2000numerical] §2.5.3: "`ε_M`
represents the distance between the number `1` and the nearest floating-point number, and
therefore it is the smallest number of `𝔽` such that `1 + ε_M > 1`"): when the exponent `1` is
admissible and `t ≥ 2`, `ε_M` is the least positive `δ` with `1 + δ ∈ 𝔽`.

The hypothesis `t ≥ 2` is needed: in `𝔽(2, 1, L, 1)` no number of `𝔽` exceeds `1`. -/
theorem isLeast_machineEps (hL : s.L ≤ 1) (hU : 1 ≤ s.U) (ht : 2 ≤ s.t) :
    IsLeast {δ : K | 0 < δ ∧ 1 + δ ∈ s.numbers K} (s.machineEps K) :=
  ⟨⟨s.machineEps_pos, s.one_add_machineEps_mem hL hU ht⟩,
    fun _ hδ => s.machineEps_le_of_one_add_mem hδ.1 hδ.2⟩

/-! ### The de-normalized numbers -/

/-- A de-normalized number is at least `β^(L-t)` in absolute value: the smallest one is
`β^(L-t)` ([quarteroni2000numerical] §2.5.2). -/
theorem zpow_le_abs_of_mem_denormalized {x : K} (hx : x ∈ s.denormalized K) :
    (s.β : K) ^ (s.L - s.t) ≤ |x| := by
  obtain ⟨σ, m, hm1, _, rfl⟩ := hx
  rw [s.abs_units_mul]
  have : (1 : K) ≤ m := by exact_mod_cast hm1
  nlinarith [s.zpow_β_pos (K := K) (s.L - s.t)]

/-- The de-normalized numbers lie in `(-x_min, x_min)` ([quarteroni2000numerical] §2.5.2). -/
theorem abs_lt_xmin_of_mem_denormalized {x : K} (hx : x ∈ s.denormalized K) :
    |x| < s.xmin K := by
  obtain ⟨σ, m, _, hm2, rfl⟩ := hx
  rw [s.abs_units_mul, xmin]
  have h : m + 1 ≤ s.β ^ (s.t - 1) := by
    have := Nat.one_le_pow (s.t - 1) s.β s.β_pos
    omega
  have hm : (m : K) < (s.β : K) ^ ((s.t : ℤ) - 1) := by
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast h
  calc (m : K) * (s.β : K) ^ (s.L - s.t)
      < (s.β : K) ^ ((s.t : ℤ) - 1) * (s.β : K) ^ (s.L - s.t) :=
        mul_lt_mul_of_pos_right hm (s.zpow_β_pos _)
    _ = (s.β : K) ^ (s.L - 1) := by rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring

/-- `β^(L-t)` is de-normalized when `t ≥ 2` (for `t = 1` there are no de-normalized numbers). -/
theorem zpow_mem_denormalized (ht : 2 ≤ s.t) : (s.β : K) ^ (s.L - s.t) ∈ s.denormalized K := by
  refine ⟨1, 1, le_rfl, ?_, by simp⟩
  have : 2 ≤ s.β ^ (s.t - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (s.t - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ s.β ^ (s.t - 1) := Nat.pow_le_pow_left s.two_le_β _
  omega

/-- **The smallest de-normalized number** ([quarteroni2000numerical] §2.5.2): for `t ≥ 2`, the least
positive element of `𝔽_D` is `β^(L-t)`. -/
theorem isLeast_denormalized (ht : 2 ≤ s.t) :
    IsLeast {x : K | x ∈ s.denormalized K ∧ 0 < x} ((s.β : K) ^ (s.L - s.t)) :=
  ⟨⟨s.zpow_mem_denormalized ht, s.zpow_β_pos _⟩, fun _ hx =>
    (s.zpow_le_abs_of_mem_denormalized hx.1).trans (abs_of_pos hx.2).le⟩

section Rounding

variable [FloorRing K]

/-! ### The exponent, the mantissa and the spacing -/

/-- The **exponent** of the normalized representation `|x| = 0.a₁a₂… × β^e`, i.e. the unique `e`
with `β^(e-1) ≤ |x| < β^e` (`System.zpow_exponent_sub_one_le_abs`, `System.abs_lt_zpow_exponent`);
for `x = 0` it is the junk value `1`, which no lemma relies on. -/
noncomputable def exponent (s : System) (x : K) : ℤ := Int.log s.β |x| + 1

/-- The **mantissa** `|x| β^(t - e)` of `x`, which lies in `[β^(t-1), β^t)` for `x ≠ 0`: the
integer part of the number `a₁a₂…a_t.a_{t+1}…` obtained by shifting the digits of `|x|`. -/
noncomputable def mantissa (s : System) (x : K) : K := |x| * (s.β : K) ^ ((s.t : ℤ) - s.exponent x)

/-- The **unit in the last place** at `x`: the spacing `β^(e - t)` of the numbers of `𝔽` in the
binade `[β^(e-1), β^e)` containing `|x|` ([quarteroni2000numerical] §2.5.3, in the mantissa
convention `x = ± 0.a₁…a_t × β^e` of the book's (2.29)). -/
noncomputable def ulp (s : System) (x : K) : K := (s.β : K) ^ (s.exponent x - s.t)

omit [IsStrictOrderedRing K] in
/-- The exponent depends on `|x|` only. -/
@[simp] theorem exponent_neg (x : K) : s.exponent (-x) = s.exponent x := by simp [exponent]

/-- The exponent depends on `|x|` only. -/
@[simp] theorem exponent_abs (x : K) : s.exponent |x| = s.exponent x := by simp [exponent]

/-- The junk value of the exponent at `0`. -/
@[simp] theorem exponent_zero : s.exponent (0 : K) = 1 := by simp [exponent]

omit [IsStrictOrderedRing K] in
/-- The mantissa depends on `|x|` only. -/
@[simp] theorem mantissa_neg (x : K) : s.mantissa (-x) = s.mantissa x := by simp [mantissa]

/-- The mantissa of `0` is `0`. -/
@[simp] theorem mantissa_zero : s.mantissa (0 : K) = 0 := by simp [mantissa]

/-- The mantissa is nonnegative. -/
theorem mantissa_nonneg (x : K) : 0 ≤ s.mantissa x :=
  mul_nonneg (abs_nonneg _) (s.zpow_β_nonneg _)

omit [IsStrictOrderedRing K] in
/-- The spacing depends on `|x|` only. -/
@[simp] theorem ulp_neg (x : K) : s.ulp (-x) = s.ulp x := by simp [ulp]

/-- The spacing is positive. -/
theorem ulp_pos (x : K) : 0 < s.ulp x := s.zpow_β_pos _

/-- The lower bound of the binade of `x`: `β^(exponent x - 1) ≤ |x|` for `x ≠ 0`. -/
theorem zpow_exponent_sub_one_le_abs {x : K} (hx : x ≠ 0) :
    (s.β : K) ^ (s.exponent x - 1) ≤ |x| := by
  rw [exponent, add_sub_cancel_right]
  exact Int.zpow_log_le_self s.one_lt_β (abs_pos.2 hx)

/-- The upper bound of the binade of `x`: `|x| < β^(exponent x)`, for every `x`. -/
theorem abs_lt_zpow_exponent (x : K) : |x| < (s.β : K) ^ s.exponent x :=
  Int.lt_zpow_succ_log_self s.one_lt_β |x|

/-- The exponent is characterized by the binade: `β^(e-1) ≤ |x| < β^e` forces `exponent x = e`. -/
theorem exponent_eq_of_le_of_lt {x : K} {e : ℤ} (h1 : (s.β : K) ^ (e - 1) ≤ |x|)
    (h2 : |x| < (s.β : K) ^ e) : s.exponent x = e := by
  have hx : 0 < |x| := (s.zpow_β_pos _).trans_le h1
  have a := (Int.zpow_le_iff_le_log s.one_lt_β hx).1 h1
  have b := (Int.lt_zpow_iff_log_lt s.one_lt_β hx).1 h2
  rw [exponent]
  omega

/-- The exponent is monotone on the positive numbers. -/
theorem exponent_mono {x y : K} (hx : 0 < x) (hxy : x ≤ y) : s.exponent x ≤ s.exponent y := by
  rw [exponent, exponent]
  have := Int.log_mono_right (b := s.β) (abs_pos.2 hx.ne') (abs_le_abs hxy (by linarith))
  omega

/-- `|x| = mantissa x · β^(exponent x - t)`. -/
theorem abs_eq_mantissa_mul_zpow (x : K) :
    |x| = s.mantissa x * (s.β : K) ^ (s.exponent x - s.t) := by
  rw [mantissa, mul_assoc, ← zpow_add₀ s.β_cast_ne_zero]
  simp

/-- The mantissa of a nonzero number is at least `β^(t-1)`. -/
theorem zpow_le_mantissa {x : K} (hx : x ≠ 0) : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ s.mantissa x := by
  have h := s.zpow_exponent_sub_one_le_abs hx
  have := mul_le_mul_of_nonneg_right h (s.zpow_β_nonneg ((s.t : ℤ) - s.exponent x))
  rwa [← zpow_add₀ s.β_cast_ne_zero, show s.exponent x - 1 + ((s.t : ℤ) - s.exponent x)
    = (s.t : ℤ) - 1 by ring] at this

/-- The mantissa is less than `β^t`. -/
theorem mantissa_lt_zpow (x : K) : s.mantissa x < (s.β : K) ^ (s.t : ℤ) := by
  have h := s.abs_lt_zpow_exponent x
  have := mul_lt_mul_of_pos_right h (s.zpow_β_pos ((s.t : ℤ) - s.exponent x))
  rwa [← zpow_add₀ s.β_cast_ne_zero, show s.exponent x + ((s.t : ℤ) - s.exponent x)
    = (s.t : ℤ) by ring] at this

/-- A number written as `|x| = m β^(e-t)` with `β^(t-1) ≤ m < β^t` has exponent `e`. -/
theorem exponent_eq_of_abs_eq {x m : K} {e : ℤ} (hm1 : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m)
    (hm2 : m < (s.β : K) ^ (s.t : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) :
    s.exponent x = e :=
  s.exponent_eq_of_le_of_lt (hx ▸ s.zpow_sub_one_le_mul_zpow hm1 e) (hx ▸ s.mul_zpow_lt_zpow hm2 e)

/-- A number written as `|x| = m β^(e-t)` with `β^(t-1) ≤ m < β^t` has mantissa `m`. -/
theorem mantissa_eq_of_abs_eq {x m : K} {e : ℤ} (hm1 : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m)
    (hm2 : m < (s.β : K) ^ (s.t : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) :
    s.mantissa x = m := by
  rw [mantissa, s.exponent_eq_of_abs_eq hm1 hm2 hx, hx, mul_assoc, ← zpow_add₀ s.β_cast_ne_zero]
  simp

/-- **The spacing bounds** ([quarteroni2000numerical] §2.5.3): the distance between consecutive
numbers of `𝔽` near `x ≠ 0` is more than `β⁻¹ ε_M |x|` and at most `ε_M |x|`. (The book says "at
least `β⁻¹ ε_M |x|`"; the inequality is strict.) -/
theorem ulp_bounds {x : K} (hx : x ≠ 0) :
    (s.β : K)⁻¹ * s.machineEps K * |x| < s.ulp x ∧ s.ulp x ≤ s.machineEps K * |x| := by
  have h1 := s.zpow_exponent_sub_one_le_abs hx
  have h2 := s.abs_lt_zpow_exponent x
  have hε : 0 < s.machineEps K := s.machineEps_pos
  have hulp : s.ulp x = s.machineEps K * (s.β : K) ^ (s.exponent x - 1) := by
    rw [ulp, machineEps, ← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  have hβ : (s.β : K)⁻¹ * (s.β : K) ^ s.exponent x = (s.β : K) ^ (s.exponent x - 1) := by
    rw [← zpow_neg_one, ← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
  constructor
  · calc (s.β : K)⁻¹ * s.machineEps K * |x|
        < (s.β : K)⁻¹ * s.machineEps K * (s.β : K) ^ s.exponent x :=
          mul_lt_mul_of_pos_left h2 (mul_pos (inv_pos.2 s.β_cast_pos) hε)
      _ = s.ulp x := by rw [hulp, mul_right_comm, hβ, mul_comm]
  · rw [hulp]
    exact mul_le_mul_of_nonneg_left h1 hε.le

/-- **[quarteroni2000numerical] (2.31)**: for `x = σ m β^(e-t) ∈ 𝔽` with a normalized mantissa
`m`, the relative distance to the next number is `ulp x / |x| = 1 / m`; it depends only on the
mantissa (*wobbling precision*). -/
theorem ulp_div_eq_inv_mantissa {σ : ℤˣ} {m : ℕ} {e : ℤ} (hm1 : s.β ^ (s.t - 1) ≤ m)
    (hm2 : m ≤ s.β ^ s.t - 1) {x : K} (hx : x = ((σ : ℤ) : K) * m * (s.β : K) ^ (e - s.t)) :
    s.ulp x / |x| = 1 / m := by
  have habs : |x| = m * (s.β : K) ^ (e - s.t) := by rw [hx, s.abs_units_mul]
  rw [ulp, s.exponent_eq_of_abs_eq (s.zpow_le_natCast hm1) (s.natCast_lt_zpow hm2) habs, habs,
    mul_comm (m : K), ← div_div, div_self (zpow_ne_zero _ s.β_cast_ne_zero)]

/-! ### Rounding to nearest and chopping -/

/-- **Rounding to nearest** ([quarteroni2000numerical] (2.32)): the mantissa `|x| β^(t-e)` is
rounded to the nearest integer (halves up, Mathlib's `round`) and the sign and exponent are
restored. A total function on `K`; when the mantissa rounds up to `β^t` the value is `β^e`,
a normalized number of exponent `e + 1`. -/
noncomputable def round (s : System) (x : K) : K :=
  (SignType.sign x : K) * (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t)

/-- **Chopping** ([quarteroni2000numerical] §2.5.5): the mantissa is truncated to its integer
part. -/
noncomputable def chop (s : System) (x : K) : K :=
  (SignType.sign x : K) * (⌊s.mantissa x⌋ : K) * (s.β : K) ^ (s.exponent x - s.t)

/-- `fl(0) = 0`. -/
@[simp] theorem round_zero : s.round (0 : K) = 0 := by simp [round]

/-- Chopping fixes `0`. -/
@[simp] theorem chop_zero : s.chop (0 : K) = 0 := by simp [chop]

/-- Rounding is odd: `round (-x) = -round x`. -/
theorem round_neg (x : K) : s.round (-x) = -s.round x := by
  simp [round, Left.sign_neg]

/-- Chopping is odd: `chop (-x) = -chop x`. -/
theorem chop_neg (x : K) : s.chop (-x) = -s.chop x := by
  simp [chop, Left.sign_neg]

/-- Rounding through a known binade: if `β^(e-1) ≤ |x| < β^e` then
`round x = sign x · round (|x| β^(t-e)) · β^(e-t)`, the form in which concrete values are
computed. -/
theorem round_eq_of_le_of_lt {x : K} {e : ℤ} (h1 : (s.β : K) ^ (e - 1) ≤ |x|)
    (h2 : |x| < (s.β : K) ^ e) :
    s.round x = (SignType.sign x : K) * (_root_.round (|x| * (s.β : K) ^ ((s.t : ℤ) - e)) : K) *
      (s.β : K) ^ (e - s.t) := by
  rw [round, mantissa, s.exponent_eq_of_le_of_lt h1 h2]

/-- The rounded mantissa of a nonzero number is at least `β^(t-1)`. -/
theorem zpow_le_round_mantissa {x : K} (hx : x ≠ 0) :
    ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ _root_.round (s.mantissa x) := by
  have h := monotone_round (show ((s.β ^ (s.t - 1) : ℕ) : K) ≤ s.mantissa x by
    rw [s.natCast_pow_t_sub_one]; exact s.zpow_le_mantissa hx)
  rwa [round_natCast] at h

/-- The rounded mantissa is at most `β^t`. -/
theorem round_mantissa_le (x : K) : _root_.round (s.mantissa x) ≤ ((s.β ^ s.t : ℕ) : ℤ) := by
  have h := monotone_round (show s.mantissa x ≤ ((s.β ^ s.t : ℕ) : K) by
    rw [s.natCast_pow_t]; exact (s.mantissa_lt_zpow x).le)
  rwa [round_natCast] at h

/-- The rounded mantissa is nonnegative. -/
theorem round_mantissa_nonneg (x : K) : (0 : K) ≤ _root_.round (s.mantissa x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have := s.zpow_le_round_mantissa hx
    exact_mod_cast (Int.natCast_nonneg _).trans this

/-- `|round x| = round (mantissa x) · β^(exponent x - t)`. -/
theorem abs_round (x : K) :
    |s.round x| = (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [round, mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg (s.round_mantissa_nonneg x)
      (s.zpow_β_nonneg _))]
    rcases lt_or_gt_of_ne hx with h | h <;> simp [sign_pos, sign_neg, h]

/-- `round x = sign x · |round x|`. -/
theorem round_eq_sign_mul_abs (x : K) : s.round x = (SignType.sign x : K) * |s.round x| := by
  rw [abs_round, round, mul_assoc]

/-- Rounding preserves nonnegativity. -/
theorem round_nonneg {x : K} (hx : 0 ≤ x) : 0 ≤ s.round x := by
  rw [round_eq_sign_mul_abs]
  rcases hx.lt_or_eq with h | rfl
  · simp [sign_pos h, abs_nonneg]
  · simp

/-- Rounding preserves nonpositivity. -/
theorem round_nonpos {x : K} (hx : x ≤ 0) : s.round x ≤ 0 := by
  have := s.round_nonneg (neg_nonneg.2 hx)
  rwa [round_neg, neg_nonneg] at this

omit [IsStrictOrderedRing K] in
/-- For `0 < x`, `round x = round (mantissa x) · β^(exponent x - t)`. -/
theorem round_of_pos {x : K} (hx : 0 < x) :
    s.round x = (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) := by
  rw [round, sign_pos hx]; simp

/-- A number whose mantissa is already an integer in `[β^(t-1), β^t)` is fixed by rounding,
whatever its exponent. -/
theorem round_eq_self_of_abs_eq {x : K} {m e : ℤ} (hm1 : ((s.β ^ (s.t - 1) : ℕ) : ℤ) ≤ m)
    (hm2 : m < ((s.β ^ s.t : ℕ) : ℤ)) (hx : |x| = m * (s.β : K) ^ (e - s.t)) : s.round x = x := by
  have hm1' : (s.β : K) ^ ((s.t : ℤ) - 1) ≤ m := by
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast hm1
  have hm2' : (m : K) < (s.β : K) ^ (s.t : ℤ) := by
    rw [← s.natCast_pow_t]; exact_mod_cast hm2
  rw [round, s.mantissa_eq_of_abs_eq hm1' hm2' hx, s.exponent_eq_of_abs_eq hm1' hm2' hx,
    round_intCast, mul_assoc, ← hx, sign_mul_abs]

/-- `fl(x) = x` for `x ∈ 𝔽` ([quarteroni2000numerical] §2.5.5). -/
theorem round_eq_self {x : K} (hx : x ∈ s.numbers K) : s.round x = x := by
  rcases s.mem_numbers_iff_abs.1 hx with rfl | ⟨m, e, hm1, hm2, _, _, hxe⟩
  · simp
  · refine s.round_eq_self_of_abs_eq (m := m) (e := e) (by exact_mod_cast hm1) ?_
      (by rw [Int.cast_natCast]; exact hxe)
    have := Nat.one_le_pow s.t s.β s.β_pos
    exact_mod_cast (show m < s.β ^ s.t by omega)

/-- **Rounding is idempotent**, for every `x`: the rounded mantissa is an integer in `[β^(t-1),
β^t]`, and when it equals `β^t` the result `β^e` is the normalized number of exponent `e + 1`
with mantissa `β^(t-1)`. -/
theorem round_round (x : K) : s.round (s.round x) = s.round x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have habs := s.abs_round x
    have hlow := s.zpow_le_round_mantissa hx
    rcases (s.round_mantissa_le x).lt_or_eq with hlt | heq
    · exact s.round_eq_self_of_abs_eq hlow hlt habs
    · refine s.round_eq_self_of_abs_eq (m := ((s.β ^ (s.t - 1) : ℕ) : ℤ)) (e := s.exponent x + 1)
        le_rfl (by exact_mod_cast Nat.pow_lt_pow_right s.one_lt_β (by have := s.one_le_t; omega)) ?_
      rw [habs, heq, Int.cast_natCast, Int.cast_natCast, s.natCast_pow_t_sub_one, s.natCast_pow_t,
        ← zpow_add₀ s.β_cast_ne_zero, ← zpow_add₀ s.β_cast_ne_zero]
      congr 1; ring

/-- **Rounding lands in `𝔽`** on the range of `𝔽`: `x_min ≤ |x| ≤ x_max` gives `round x ∈ 𝔽`. The
mantissa rounds to an integer in `[β^(t-1), β^t]`; when it rounds up to `β^t` the exponent
increases by one, which stays admissible because `|x| ≤ x_max = β^U - β^(U-t)` rules out `e = U`
in that case. -/
theorem round_mem_numbers {x : K} (h1 : s.xmin K ≤ |x|) (h2 : |x| ≤ s.xmax K) :
    s.round x ∈ s.numbers K := by
  have hβ := s.one_lt_β_cast (K := K)
  have hx : x ≠ 0 := by
    rintro rfl
    simpa using s.xmin_pos.trans_le h1
  have habs := s.abs_round x
  have hlow := s.zpow_le_round_mantissa hx
  have hLe : s.L ≤ s.exponent x := by
    have : (s.β : K) ^ (s.L - 1) < (s.β : K) ^ s.exponent x :=
      h1.trans_lt (s.abs_lt_zpow_exponent x)
    have := (zpow_lt_zpow_iff_right₀ hβ).1 this
    omega
  have heU : s.exponent x ≤ s.U := by
    have : (s.β : K) ^ (s.exponent x - 1) < (s.β : K) ^ s.U :=
      (s.zpow_exponent_sub_one_le_abs hx).trans_lt (h2.trans_lt s.xmax_lt_zpow)
    have := (zpow_lt_zpow_iff_right₀ hβ).1 this
    omega
  rw [mem_numbers_iff_abs]
  rcases (s.round_mantissa_le x).lt_or_eq with hlt | heq
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((Int.natCast_nonneg _).trans hlow)
    rw [hm] at habs hlow hlt
    refine Or.inr ⟨m, s.exponent x, by exact_mod_cast hlow, ?_, hLe, heU, by simpa using habs⟩
    have : m < s.β ^ s.t := by exact_mod_cast hlt
    omega
  · -- the mantissa rounded up to `β^t`: the result is `β^e = β^(t-1) β^(e+1-t)`
    have hne : s.exponent x ≠ s.U := by
      intro hU
      have hround : (s.β : K) ^ (s.t : ℤ) ≤ s.mantissa x + 1 / 2 := by
        rw [← s.natCast_pow_t, ← Int.cast_natCast, ← heq]; exact round_le_add_half _
      have hxe := s.abs_eq_mantissa_mul_zpow x
      rw [hU] at hxe
      have hp : 0 < (s.β : K) ^ (s.U - s.t) := s.zpow_β_pos _
      have hkey : (s.β : K) ^ s.U - (s.β : K) ^ (s.U - s.t) / 2 ≤ |x| := by
        rw [hxe]
        have : ((s.β : K) ^ (s.t : ℤ) - 1 / 2) * (s.β : K) ^ (s.U - s.t) ≤
            s.mantissa x * (s.β : K) ^ (s.U - s.t) := by
          apply mul_le_mul_of_nonneg_right _ hp.le
          linarith
        rw [sub_mul, ← zpow_add₀ s.β_cast_ne_zero, add_sub_cancel] at this
        linarith
      rw [xmax_eq_sub] at h2
      linarith
    refine Or.inr ⟨s.β ^ (s.t - 1), s.exponent x + 1, le_rfl, ?_, by omega, by omega, ?_⟩
    · have h1 := Nat.one_le_pow s.t s.β s.β_pos
      have h2 : s.β ^ (s.t - 1) < s.β ^ s.t :=
        Nat.pow_lt_pow_right s.one_lt_β (by have := s.one_le_t; omega)
      omega
    · rw [habs, heq, Int.cast_natCast, s.natCast_pow_t, s.natCast_pow_t_sub_one,
        ← zpow_add₀ s.β_cast_ne_zero, ← zpow_add₀ s.β_cast_ne_zero]
      congr 1; ring

/-- Rounding is monotone on the positive numbers. Within a binade this is the monotonicity of
`round` on the mantissa; across binades,
`round x ≤ β^(exponent x) ≤ β^(exponent y - 1) ≤ round y`. -/
theorem round_le_round_of_pos {x y : K} (hx : 0 < x) (hxy : x ≤ y) : s.round x ≤ s.round y := by
  have hy : 0 < y := hx.trans_le hxy
  have hβ := s.one_lt_β_cast (K := K)
  rw [s.round_of_pos hx, s.round_of_pos hy]
  rcases (s.exponent_mono hx hxy).lt_or_eq with hlt | heq
  · -- across binades
    have hup : (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t) ≤
        (s.β : K) ^ s.exponent x := by
      have h : (_root_.round (s.mantissa x) : K) ≤ (s.β : K) ^ (s.t : ℤ) := by
        rw [← s.natCast_pow_t]; exact_mod_cast s.round_mantissa_le x
      calc (_root_.round (s.mantissa x) : K) * (s.β : K) ^ (s.exponent x - s.t)
          ≤ (s.β : K) ^ (s.t : ℤ) * (s.β : K) ^ (s.exponent x - s.t) :=
            mul_le_mul_of_nonneg_right h (s.zpow_β_nonneg _)
        _ = (s.β : K) ^ s.exponent x := by rw [← zpow_add₀ s.β_cast_ne_zero]; congr 1; ring
    have hlo : (s.β : K) ^ (s.exponent y - 1) ≤
        (_root_.round (s.mantissa y) : K) * (s.β : K) ^ (s.exponent y - s.t) := by
      refine s.zpow_sub_one_le_mul_zpow ?_ _
      rw [← s.natCast_pow_t_sub_one]; exact_mod_cast s.zpow_le_round_mantissa hy.ne'
    exact hup.trans ((zpow_le_zpow_right₀ hβ.le (by omega)).trans hlo)
  · -- within a binade
    have hm : s.mantissa x ≤ s.mantissa y := by
      rw [mantissa, mantissa, heq, abs_of_pos hx, abs_of_pos hy]
      exact mul_le_mul_of_nonneg_right hxy (s.zpow_β_nonneg _)
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast monotone_round hm)
      (s.zpow_β_nonneg _)

/-- **Rounding is monotone** ([quarteroni2000numerical] §2.5.5, "`fl(x) ≤ fl(y)` if `x ≤ y`"). -/
theorem round_mono : Monotone (s.round : K → K) := by
  intro x y hxy
  rcases lt_or_ge 0 x with hx | hx
  · exact s.round_le_round_of_pos hx hxy
  · rcases lt_or_ge y 0 with hy | hy
    · have := s.round_le_round_of_pos (neg_pos.2 hy) (neg_le_neg hxy)
      rwa [round_neg, round_neg, neg_le_neg_iff] at this
    · exact (s.round_nonpos hx).trans (s.round_nonneg hy)

/-- **The absolute error of rounding** ([quarteroni2000numerical] §2.5.5, the display `E(x) ≤ ½
β^(e-t)` closing the section): `|x - round x| ≤ ½ ulp x` for every `x`. -/
theorem abs_sub_round_le (x : K) : |x - s.round x| ≤ (1 / 2 : K) * s.ulp x := by
  have hp : 0 < (s.β : K) ^ (s.exponent x - s.t) := s.zpow_β_pos _
  have hx : x - s.round x = (SignType.sign x : K) *
      ((s.mantissa x - _root_.round (s.mantissa x)) * (s.β : K) ^ (s.exponent x - s.t)) := by
    have h1 : x = (SignType.sign x : K) * (s.mantissa x * (s.β : K) ^ (s.exponent x - s.t)) := by
      rw [← s.abs_eq_mantissa_mul_zpow, sign_mul_abs]
    rw [round, sub_mul, mul_sub, ← h1, mul_assoc]
  rw [hx, abs_mul, abs_mul, abs_of_pos hp, ulp]
  calc |(SignType.sign x : K)| * (|s.mantissa x - _root_.round (s.mantissa x)| *
        (s.β : K) ^ (s.exponent x - s.t))
      ≤ 1 * (1 / 2 * (s.β : K) ^ (s.exponent x - s.t)) := by
        gcongr
        · exact abs_coe_sign_le_one x
        · exact abs_sub_round _
    _ = 1 / 2 * (s.β : K) ^ (s.exponent x - s.t) := one_mul _

/-- Half a spacing is at most `u |x|`, for `x ≠ 0`: the step from the absolute to the relative
error bound of rounding. -/
theorem half_ulp_le_unitRoundoff_mul_abs {x : K} (hx : x ≠ 0) :
    (1 / 2 : K) * s.ulp x ≤ s.unitRoundoff K * |x| := by
  rw [unitRoundoff, mul_assoc, ← machineEps]
  exact mul_le_mul_of_nonneg_left (s.ulp_bounds hx).2 (by norm_num)

/-- **[quarteroni2000numerical] Property 2.1 (rounding), unconditional**: `|round x - x| ≤ u |x|`
for every `x`, with `u = ½ β^(1-t)` the roundoff unit. The book's range hypothesis `x_min ≤ |x| ≤
x_max` is not needed for the bound, only for `round x ∈ 𝔽` (`System.round_mem_numbers`); this is
[higham2002accuracy] Theorem 2.2 "barring overflow and underflow". -/
theorem abs_round_sub_le (x : K) : |s.round x - x| ≤ s.unitRoundoff K * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [abs_sub_comm]
    exact (s.abs_sub_round_le x).trans (s.half_ulp_le_unitRoundoff_mul_abs hx)

/-- **[quarteroni2000numerical] Property 2.1 (chopping)**: `|chop x - x| ≤ ε_M |x|` for every `x`;
the unit roundoff of chopping is `β^(1-t)` ([higham2002accuracy] Theorem 2.2). -/
theorem abs_chop_sub_le (x : K) : |s.chop x - x| ≤ s.machineEps K * |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hp : 0 < (s.β : K) ^ (s.exponent x - s.t) := s.zpow_β_pos _
    have hkey : s.chop x - x = -((SignType.sign x : K) *
        ((s.mantissa x - ⌊s.mantissa x⌋) * (s.β : K) ^ (s.exponent x - s.t))) := by
      have h1 : x = (SignType.sign x : K) * (s.mantissa x * (s.β : K) ^ (s.exponent x - s.t)) := by
        rw [← s.abs_eq_mantissa_mul_zpow, sign_mul_abs]
      rw [chop, sub_mul, mul_sub, ← h1, mul_assoc, neg_sub]
    rw [hkey, abs_neg, abs_mul, abs_mul, abs_of_pos hp]
    calc |(SignType.sign x : K)| * (|s.mantissa x - ⌊s.mantissa x⌋| *
          (s.β : K) ^ (s.exponent x - s.t))
        ≤ 1 * (1 * (s.β : K) ^ (s.exponent x - s.t)) := by
          gcongr
          · exact abs_coe_sign_le_one x
          · rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le
      _ = s.ulp x := by rw [one_mul, one_mul, ulp]
      _ ≤ s.machineEps K * |x| := (s.ulp_bounds hx).2

/-- **Overflow** ([quarteroni2000numerical] Remark 2.2): for `β^U ≤ |x|` the rounding leaves `𝔽`,
since `|round x| ≥ β^(exponent x - 1) ≥ β^U > x_max`. Numbers between `x_max` and `β^U - ½β^(U-t)`
still round to `x_max`, which is why the threshold is `β^U` and not the book's `x_max`; underflow
needs no statement, `round` being total and `System.abs_round_sub_le` unconditional. -/
theorem round_notMem_numbers {x : K} (hx : (s.β : K) ^ s.U ≤ |x|) : s.round x ∉ s.numbers K := by
  intro hmem
  have hβ := s.one_lt_β_cast (K := K)
  have hx0 : x ≠ 0 := by
    rintro rfl
    simpa using (s.zpow_β_pos s.U).trans_le hx
  have hU : s.U < s.exponent x :=
    (zpow_lt_zpow_iff_right₀ hβ).1 (hx.trans_lt (s.abs_lt_zpow_exponent x))
  have hlo : (s.β : K) ^ (s.exponent x - 1) ≤ |s.round x| := by
    rw [abs_round]
    refine s.zpow_sub_one_le_mul_zpow ?_ _
    rw [← s.natCast_pow_t_sub_one]; exact_mod_cast s.zpow_le_round_mantissa hx0
  have := s.abs_le_xmax hmem
  have := s.xmax_lt_zpow (K := K)
  have := zpow_le_zpow_right₀ hβ.le (show s.U ≤ s.exponent x - 1 by omega)
  linarith

/-! ### The instances of the relational model -/

/-- **`𝔽(β, t, L, U)` with rounding to nearest is an instance of the standard model** of
`Numlib/FloatingPoint/Model.lean`: the relation `Rounds x y := y = round x` with `u = ½ β^(1-t)`.
Total and functional; overflow is `System.round_notMem_numbers`, not a restriction of the
relation. -/
noncomputable def roundingModel (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] : RoundingModel K where
  u := s.unitRoundoff K
  u_nonneg := s.unitRoundoff_nonneg
  Rounds x y := y = s.round x
  abs_sub_le := by
    rintro x y rfl
    exact s.abs_round_sub_le x

/-- **`𝔽(β, t, L, U)` with chopping** is an instance of the standard model with `u = β^(1-t)`. -/
noncomputable def choppingModel (s : System) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] : RoundingModel K where
  u := s.machineEps K
  u_nonneg := s.machineEps_pos.le
  Rounds x y := y = s.chop x
  abs_sub_le := by
    rintro x y rfl
    exact s.abs_chop_sub_le x

/-- The unit roundoff of the rounding model is `u = ½ β^(1-t)`. -/
@[simp] theorem roundingModel_u : (s.roundingModel K).u = s.unitRoundoff K := rfl

/-- The rounding relation of the rounding model is the graph of `round`. -/
@[simp] theorem roundingModel_rounds_iff {x y : K} :
    (s.roundingModel K).Rounds x y ↔ y = s.round x := Iff.rfl

/-- The unit roundoff of the chopping model is `ε_M = β^(1-t)`. -/
@[simp] theorem choppingModel_u : (s.choppingModel K).u = s.machineEps K := rfl

/-- The rounding relation of the chopping model is the graph of `chop`. -/
@[simp] theorem choppingModel_rounds_iff {x y : K} :
    (s.choppingModel K).Rounds x y ↔ y = s.chop x := Iff.rfl

/-- **[quarteroni2000numerical] Property 2.1 in the book's form (2.33)**: `round x = x (1 + δ)`
with `|δ| ≤ u`, for every `x`. -/
theorem exists_round_eq_mul_one_add (x : K) :
    ∃ δ : K, |δ| ≤ s.unitRoundoff K ∧ s.round x = x * (1 + δ) :=
  RoundingModel.Rounds.exists_delta (m := s.roundingModel K) rfl

/-- Chopping in the `(1 + δ)` form: `chop x = x (1 + δ)` with `|δ| ≤ ε_M`. -/
theorem exists_chop_eq_mul_one_add (x : K) :
    ∃ δ : K, |δ| ≤ s.machineEps K ∧ s.chop x = x * (1 + δ) :=
  RoundingModel.Rounds.exists_delta (m := s.choppingModel K) rfl

/-! ### Machine operations -/

/-- The **machine operation** attached to an exact operation `f`: `x ∘ y = fl(f (fl x) (fl y))`
([quarteroni2000numerical] §2.5.6). -/
noncomputable def op (s : System) (f : K → K → K) (x y : K) : K :=
  s.round (f (s.round x) (s.round y))

/-- The machine sum `x ⊕ y = fl(fl(x) + fl(y))`. -/
noncomputable abbrev add (s : System) (x y : K) : K := s.op (· + ·) x y

/-- The machine difference `x ⊖ y = fl(fl(x) - fl(y))`. -/
noncomputable abbrev sub (s : System) (x y : K) : K := s.op (· - ·) x y

/-- The machine product `x ⊗ y = fl(fl(x) · fl(y))`. -/
noncomputable abbrev mul (s : System) (x y : K) : K := s.op (· * ·) x y

/-- The machine quotient `x ⊘ y = fl(fl(x) / fl(y))`. -/
noncomputable abbrev div (s : System) (x y : K) : K := s.op (· / ·) x y

omit [IsStrictOrderedRing K] in
/-- The machine sum is commutative ([quarteroni2000numerical] §2.5.6, a property of exact
arithmetic that survives). -/
theorem add_comm (x y : K) : s.add x y = s.add y x := by
  simp [op, _root_.add_comm]

omit [IsStrictOrderedRing K] in
/-- The machine product is commutative. -/
theorem mul_comm (x y : K) : s.mul x y = s.mul y x := by
  simp [op, _root_.mul_comm]

/-- On machine numbers the operands need no rounding: `x ∘ y = fl(f x y)`. -/
theorem op_eq_round_of_mem (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K)
    (hy : y ∈ s.numbers K) : s.op f x y = s.round (f x y) := by
  simp [op, s.round_eq_self hx, s.round_eq_self hy]

/-- **[quarteroni2000numerical] (2.36)**: on machine numbers, `x ∘ y = (x ∘ y)(1 + δ)` with `|δ| ≤
u`, for every operation at once. The book's caveat about the round digit does not arise: the
machine operation rounds the exact result. -/
theorem exists_op_eq_mul_one_add (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K)
    (hy : y ∈ s.numbers K) :
    ∃ δ : K, |δ| ≤ s.unitRoundoff K ∧ s.op f x y = f x y * (1 + δ) := by
  rw [s.op_eq_round_of_mem f hx hy]
  exact s.exists_round_eq_mul_one_add _

/-- A machine operation on machine numbers is an admissible rounding of the exact result in the
model `System.roundingModel`: the hook through which `𝔽` enters `FloatingPoint.RoundsSum`,
`FloatingPoint.RoundsDot` and `FloatingPoint.RoundsAffineStep`. -/
theorem rounds_op (f : K → K → K) {x y : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K) :
    (s.roundingModel K).Rounds (f x y) (s.op f x y) :=
  (s.op_eq_round_of_mem f hx hy).symm ▸ rfl

/-- **[quarteroni2000numerical] (2.37), Exercise 2.11**, for arbitrary operands and with no range
hypothesis: `|x ⊕ y - (x + y)| ≤ u (1 + u) (|x| + |y|) + u |x + y|`. The error splits as `(fl(fl x +
fl y) - (fl x + fl y)) + (fl x - x) + (fl y - y)`, each piece bounded by
`System.abs_round_sub_le`. -/
theorem abs_add_sub_le (x y : K) :
    |s.add x y - (x + y)| ≤
      s.unitRoundoff K * (1 + s.unitRoundoff K) * (|x| + |y|) + s.unitRoundoff K * |x + y| := by
  set u := s.unitRoundoff K with hu
  have hu0 : 0 ≤ u := s.unitRoundoff_nonneg
  have ha := s.abs_round_sub_le x
  have hb := s.abs_round_sub_le y
  have hc := s.abs_round_sub_le (s.round x + s.round y)
  have hsum : |s.round x + s.round y| ≤ |x + y| + |s.round x - x| + |s.round y - y| := by
    calc |s.round x + s.round y| = |(x + y) + (s.round x - x) + (s.round y - y)| := by ring_nf
      _ ≤ |(x + y) + (s.round x - x)| + |s.round y - y| := abs_add_le _ _
      _ ≤ |x + y| + |s.round x - x| + |s.round y - y| := by
          gcongr; exact abs_add_le _ _
  have hsplit : |s.add x y - (x + y)| ≤ |s.round (s.round x + s.round y) - (s.round x + s.round y)|
      + |s.round x - x| + |s.round y - y| := by
    calc |s.add x y - (x + y)| = |(s.round (s.round x + s.round y) - (s.round x + s.round y))
          + (s.round x - x) + (s.round y - y)| := by simp only [add, op]; ring_nf
      _ ≤ |(s.round (s.round x + s.round y) - (s.round x + s.round y)) + (s.round x - x)|
          + |s.round y - y| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  have h1 : |s.round (s.round x + s.round y) - (s.round x + s.round y)| ≤
      u * (|x + y| + u * |x| + u * |y|) := by
    calc _ ≤ u * |s.round x + s.round y| := hc
      _ ≤ u * (|x + y| + |s.round x - x| + |s.round y - y|) := by gcongr
      _ ≤ u * (|x + y| + u * |x| + u * |y|) := by gcongr
  calc |s.add x y - (x + y)| ≤ _ := hsplit
    _ ≤ u * (|x + y| + u * |x| + u * |y|) + u * |x| + u * |y| := by gcongr
    _ = u * (1 + u) * (|x| + |y|) + u * |x + y| := by ring

/-- **[quarteroni2000numerical] Exercise 2.12, first bound**, with the second-order term explicit:
for `x, y, z ∈ 𝔽`, `|(x ⊕ y) ⊕ z - (x + y + z)| ≤ (2 |x + y| + |z|) u + |x + y| u²`. The book writes
`C₁ ≃ (2|x + y| + |z|) u`, dropping the `u²` term; its hypothesis that the partial sums lie in the
range of `𝔽` is not needed, the bound of `System.abs_round_sub_le` being unconditional. -/
theorem abs_add_add_sub_le {x y z : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K)
    (hz : z ∈ s.numbers K) :
    |s.add (s.add x y) z - (x + y + z)| ≤
      (2 * |x + y| + |z|) * s.unitRoundoff K + |x + y| * s.unitRoundoff K ^ 2 := by
  set u := s.unitRoundoff K with hu
  have hu0 : 0 ≤ u := s.unitRoundoff_nonneg
  set w := s.add x y with hw
  have hw' : w = s.round (x + y) := s.op_eq_round_of_mem _ hx hy
  have hww : s.add w z = s.round (w + z) := by
    simp only [hw, add, op, round_round, s.round_eq_self hz]
  have h1 : |w - (x + y)| ≤ u * |x + y| := hw' ▸ s.abs_round_sub_le (x + y)
  have h2 : |s.round (w + z) - (w + z)| ≤ u * |w + z| := s.abs_round_sub_le (w + z)
  have h3 : |w + z| ≤ |x + y| + u * |x + y| + |z| := by
    calc |w + z| = |(x + y) + (w - (x + y)) + z| := by ring_nf
      _ ≤ |(x + y) + (w - (x + y))| + |z| := abs_add_le _ _
      _ ≤ |x + y| + |w - (x + y)| + |z| := by gcongr; exact abs_add_le _ _
      _ ≤ |x + y| + u * |x + y| + |z| := by gcongr
  calc |s.add w z - (x + y + z)|
      = |(s.round (w + z) - (w + z)) + (w - (x + y))| := by rw [hww]; ring_nf
    _ ≤ |s.round (w + z) - (w + z)| + |w - (x + y)| := abs_add_le _ _
    _ ≤ u * (|x + y| + u * |x + y| + |z|) + u * |x + y| := by
        gcongr
        exact h2.trans (by gcongr)
    _ = (2 * |x + y| + |z|) * u + |x + y| * u ^ 2 := by ring

/-- **[quarteroni2000numerical] Exercise 2.12, second bound**: for `x, y, z ∈ 𝔽`,
`|x ⊕ (y ⊕ z) - (x + y + z)| ≤ (|x| + 2 |y + z|) u + |y + z| u²`, from the first bound by
commutativity. -/
theorem abs_add_add_sub_le' {x y z : K} (hx : x ∈ s.numbers K) (hy : y ∈ s.numbers K)
    (hz : z ∈ s.numbers K) :
    |s.add x (s.add y z) - (x + y + z)| ≤
      (|x| + 2 * |y + z|) * s.unitRoundoff K + |y + z| * s.unitRoundoff K ^ 2 := by
  have := s.abs_add_add_sub_le hy hz hx
  rw [s.add_comm x, show x + y + z = y + z + x by ring]
  linarith

end Rounding

/-! ### IEEE parameters -/

/-- IEC 559 / IEEE 754 **single precision**, `𝔽(2, 24, -125, 128)` ([quarteroni2000numerical]
§2.5.4). -/
def ieeeSingle : System := ⟨2, 24, -125, 128, by norm_num, by norm_num, by norm_num⟩

/-- IEC 559 / IEEE 754 **double precision**, `𝔽(2, 53, -1021, 1024)` ([quarteroni2000numerical]
§2.5.4). -/
def ieeeDouble : System := ⟨2, 53, -1021, 1024, by norm_num, by norm_num, by norm_num⟩

/-- The unit roundoff of single precision is `2^(-24)`. -/
theorem ieeeSingle_unitRoundoff : ieeeSingle.unitRoundoff K = 2 ^ (-24 : ℤ) := by
  rw [unitRoundoff, show (-24 : ℤ) = -1 + (1 - (24 : ℕ)) by norm_num, zpow_add₀ two_ne_zero,
    zpow_neg_one]
  simp [ieeeSingle]

/-- The unit roundoff of double precision is `2^(-53)`. -/
theorem ieeeDouble_unitRoundoff : ieeeDouble.unitRoundoff K = 2 ^ (-53 : ℤ) := by
  rw [unitRoundoff, show (-53 : ℤ) = -1 + (1 - (53 : ℕ)) by norm_num, zpow_add₀ two_ne_zero,
    zpow_neg_one]
  simp [ieeeDouble]

end System

end FloatingPoint
