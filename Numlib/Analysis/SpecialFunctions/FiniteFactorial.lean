import Numlib.Analysis.SpecialFunctions.Integrals.BetaReal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
/-!
# Finite real factorials

The finite product convention for real powers agrees with natural factorials
and the shifted factorials in Hölder Taylor bounds.
-/

namespace Real
/-- The finite-product real factorial used for noninteger regularization powers. -/
noncomputable def finiteFactorial (r : ℝ) : ℝ := shiftedFactorial ⌊r⌋₊ (r-⌊r⌋₊)
/-- Every nonnegative real argument has a strictly positive finite factorial. -/
theorem finiteFactorial_pos {r : ℝ} (hr : 0 ≤ r) : 0 < finiteFactorial r :=
  shiftedFactorial_pos _ (sub_nonneg.mpr (Nat.floor_le hr))
/-- At natural arguments the finite product is the usual factorial. -/
theorem finiteFactorial_nat (n : ℕ) : finiteFactorial n = n.factorial := by
  simp [finiteFactorial]
/-- Splitting off the final factor gives the source identity for every r>=1. -/
theorem finiteFactorial_succ {r : ℝ} (hr : 1 ≤ r) :
    finiteFactorial r = r * finiteFactorial (r-1) := by
  have hn : 1 ≤ ⌊r⌋₊ := Nat.floor_pos.mpr hr
  have he : ⌊r⌋₊ = (⌊r⌋₊-1)+1 := by omega
  have hcast : ((⌊r⌋₊-1 : ℕ) : ℝ) = (⌊r⌋₊ : ℝ)-1 := by
    rw [Nat.cast_sub hn];norm_num
  unfold finiteFactorial
  rw [Nat.floor_sub_one]
  have hfrac : r-1-((⌊r⌋₊-1 : ℕ) : ℝ) = r-⌊r⌋₊ := by rw [hcast];ring
  rw [hfrac]
  conv_lhs => rw [he]
  rw [shiftedFactorial,Finset.prod_range_succ]
  rw [←shiftedFactorial]
  push_cast
  rw [hcast]
  ring_nf
/-- The book's shifted-factorial displays agree with the finite real factorial,
including the endpoint Holder exponent one. -/
theorem finiteFactorial_nat_add {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (k : ℕ) :
    finiteFactorial ((k : ℝ)+β) = shiftedFactorial k β := by
  rcases lt_or_eq_of_le hβ1 with hlt | rfl
  · have hf : ⌊β⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
    have hfloor : ⌊(k : ℝ)+β⌋₊ = k := by
      rw [add_comm,Nat.floor_add_natCast hβ,hf,zero_add]
    simp [finiteFactorial,hfloor]
  · rw [show (k : ℝ)+1 = ((k+1 : ℕ) : ℝ) by norm_num, finiteFactorial_nat,
      shiftedFactorial_one]
end Real
