import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Positivity

/-!
# Unique odd part and power of two

A nonzero natural number has a unique expression as an odd positive factor times a power of
two. Uniqueness follows by evaluating the prime factorization at two.
-/

namespace Nat

/-- The exponent of two in an odd-part decomposition is its prime multiplicity. -/
theorem two_factorization_of_eq_odd_mul_two_pow {n o i : ℕ} (ho : Odd o)
    (h : n = o * 2 ^ i) : n.factorization 2 = i := by
  rw [h, Nat.factorization_mul ho.pos.ne' (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by
      simpa [← even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr ho)),
    Nat.factorization_pow_self Nat.prime_two, zero_add]

/-- Odd-part decompositions are unique in both the odd factor and the exponent. -/
theorem odd_mul_two_pow_injective {o₁ o₂ i₁ i₂ : ℕ} (ho₁ : Odd o₁) (ho₂ : Odd o₂)
    (h : o₁ * 2 ^ i₁ = o₂ * 2 ^ i₂) : o₁ = o₂ ∧ i₁ = i₂ := by
  have hi : i₁ = i₂ :=
    (two_factorization_of_eq_odd_mul_two_pow ho₁ rfl).symm.trans
      (two_factorization_of_eq_odd_mul_two_pow ho₂ h)
  refine ⟨?_, hi⟩
  rw [hi] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

/-- A positive natural has exactly one pair consisting of its positive odd part and its
power-of-two exponent. -/
theorem existsUnique_odd_mul_two_pow {n : ℕ} (hn : 0 < n) :
    ∃! oi : ℕ × ℕ, Odd oi.1 ∧ 0 < oi.1 ∧ n = oi.1 * 2 ^ oi.2 := by
  obtain ⟨i, o, ho, h⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  refine ⟨(o, i), ⟨ho, ho.pos, by simpa [mul_comm] using h⟩, ?_⟩
  rintro ⟨o', i'⟩ ⟨ho', _, h'⟩
  exact Prod.ext (odd_mul_two_pow_injective ho' ho (h'.symm.trans
    (by simpa [mul_comm] using h))).1 (odd_mul_two_pow_injective ho' ho (h'.symm.trans
    (by simpa [mul_comm] using h))).2

end Nat
