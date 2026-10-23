import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Prime-power factorizations with nondivisible coefficients

A nonzero natural number splits uniquely into a power of a specified prime and a
coefficient not divisible by that prime. Specializing to two gives its unique odd part.
-/

namespace Nat

/-- The part of a natural number coprime to a prime and its prime-power exponent
are uniquely determined by a nondivisible factorization. -/
theorem Prime.existsUnique_not_dvd_mul_pow {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∃! z : ℕ × ℕ, ¬ p ∣ z.1 ∧ n = z.1 * p ^ z.2 := by
  obtain ⟨i, o, ho, h⟩ := exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  refine ⟨(o, i), ⟨ho, by simpa [mul_comm] using h⟩, ?_⟩
  rintro ⟨o', i'⟩ ⟨ho', h'⟩
  have ho0 : o ≠ 0 := by intro hz; simp [hz] at ho
  have ho'0 : o' ≠ 0 := by intro hz; simp [hz] at ho'
  have hf : n.factorization p = i := by
    rw [h, factorization_mul (pow_ne_zero _ hp.ne_zero) ho0]
    simp [hp.factorization_pow, factorization_eq_zero_of_not_dvd ho]
  have hf' : n.factorization p = i' := by
    rw [h', factorization_mul ho'0 (pow_ne_zero _ hp.ne_zero)]
    simp [hp.factorization_pow, factorization_eq_zero_of_not_dvd ho']
  have hii : i' = i := hf'.symm.trans hf
  apply Prod.ext
  · have he : o' * p ^ i = o * p ^ i := by
      rw [← hii, ← h', hii, mul_comm o, ← h]
    exact (mul_right_cancel₀ (pow_ne_zero i hp.ne_zero)) he
  · exact hii

/-- Every positive natural number has a unique odd part and a power of two. -/
theorem existsUnique_odd_mul_two_pow {n : ℕ} (hn : 0 < n) :
    ∃! z : ℕ × ℕ, Odd z.1 ∧ 0 < z.1 ∧ n = z.1 * 2 ^ z.2 := by
  obtain ⟨z, hz, hu⟩ := prime_two.existsUnique_not_dvd_mul_pow hn.ne'
  have hodd : Odd z.1 := not_even_iff_odd.mp (mt Even.two_dvd hz.1)
  refine ⟨z, ⟨hodd, ?_, hz.2⟩, ?_⟩
  · have hz0 : z.1 ≠ 0 := by intro h; simp [h] at hz
    exact Nat.pos_of_ne_zero hz0
  · intro y hy
    exact hu y ⟨hy.1.not_two_dvd_nat, hy.2.2⟩

end Nat
