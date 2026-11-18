/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Units.Basic

/-!
# Drazin and group inverses in monoids

A Drazin inverse at exponent $k$ is a commuting outer inverse that inverts multiplication by the
original element on its $k$-th power. These equations imply uniqueness in any monoid.
-/

variable {M : Type*} [Monoid M]

/-- The element $x$ is a Drazin inverse of $a$ at exponent $k$ if $a$ and $x$ commute,
$xax=x$, and $a^{k+1}x=a^k$. -/
structure IsDrazinInverseAt (k : ℕ) (a x : M) : Prop where
  /-- The original element and its inverse commute. -/
  commute : Commute a x
  /-- The inverse is an outer inverse. -/
  outer : x * a * x = x
  /-- Multiplication by the inverse sends the next power back to the given power. -/
  stable : a ^ (k + 1) * x = a ^ k

namespace IsDrazinInverseAt

variable {a x y : M} {k l : ℕ}

/-- The power identity propagates to higher exponents. -/
private theorem stable_of_le (h : a ^ (k + 1) * x = a ^ k) (hkl : k ≤ l) :
    a ^ (l + 1) * x = a ^ l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [show k + d + 1 = d + (k + 1) by omega, pow_add, mul_assoc, h, ← pow_add, Nat.add_comm d k]

/-- A Drazin inverse at exponent $k$ also satisfies the defining equations
at any exponent at least $k$. -/
protected theorem mono (h : IsDrazinInverseAt k a x) (hkl : k ≤ l) :
    IsDrazinInverseAt l a x :=
  ⟨h.commute, h.outer, stable_of_le h.stable hkl⟩

/-- In the power identity the inverse may multiply on either side. -/
theorem stable_left (h : IsDrazinInverseAt k a x) : x * a ^ (k + 1) = a ^ k :=
  (h.commute.pow_left (k + 1)).symm.eq.trans h.stable

/-- The outer inverse equation can be written $ax^2=x$. -/
theorem mul_sq (h : IsDrazinInverseAt k a x) : a * x ^ 2 = x := by
  rw [pow_two, ← mul_assoc, h.commute.eq, h.outer]

/-- A commuting outer inverse can be recovered as $a^j x^{j+1}$ for every $j$. -/
theorem pow_mul_pow_succ (h : IsDrazinInverseAt k a x) (j : ℕ) : a ^ j * x ^ (j + 1) = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      a ^ (j + 1) * x ^ (j + 1 + 1) = a ^ j * ((a * x ^ 2) * x ^ j) := by
        rw [pow_succ a j, show j + 1 + 1 = 2 + j by omega, pow_add]
        simp only [mul_assoc]
      _ = a ^ j * x ^ (j + 1) := by rw [h.mul_sq, pow_succ']
      _ = x := ih

/-- Drazin inverses at a fixed exponent are unique. -/
theorem unique (hx : IsDrazinInverseAt k a x) (hy : IsDrazinInverseAt k a y) : x = y := by
  have hxy : x * a * y = x := calc
    x * a * y = (x ^ (k + 1) * a ^ k) * a * y := by
      rw [(hx.commute.pow_pow k (k + 1)).symm.eq, hx.pow_mul_pow_succ]
    _ = x ^ (k + 1) * (a ^ (k + 1) * y) := by simp only [pow_succ a k, mul_assoc]
    _ = x := by rw [hy.stable, (hx.commute.pow_pow k (k + 1)).symm.eq, hx.pow_mul_pow_succ]
  calc
    x = x * a * y := hxy.symm
    _ = x * a * (a ^ k * y ^ (k + 1)) := by rw [hy.pow_mul_pow_succ]
    _ = (x * a ^ (k + 1)) * y ^ (k + 1) := by simp only [pow_succ' a k, mul_assoc]
    _ = y := by rw [hx.stable_left, hy.pow_mul_pow_succ]

/-- The power equation cancels the same number of factors from the two powers. -/
private theorem cancel_pow (h : a ^ (k + 1) * y = a ^ k) (d r : ℕ) :
    a ^ (k + d) * y ^ (d + r) = a ^ k * y ^ r := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      a ^ (k + (d + 1)) * y ^ (d + 1 + r) =
          (a ^ (k + d + 1) * y) * y ^ (d + r) := by
        rw [show k + (d + 1) = k + d + 1 by omega,
          show d + 1 + r = (d + r) + 1 by omega, pow_succ' y, mul_assoc]
      _ = a ^ (k + d) * y ^ (d + r) := by rw [stable_of_le h (Nat.le_add_right k d)]
      _ = _ := ih

/-- A commuting solution of the power equation gives a Drazin inverse
by the formula $x=a^k y^{k+1}$. -/
theorem of_commute_pow (hc : Commute a y) (h : a ^ (k + 1) * y = a ^ k) :
    IsDrazinInverseAt k a (a ^ k * y ^ (k + 1)) := by
  have hcomm : Commute a (a ^ k * y ^ (k + 1)) :=
    ((Commute.refl a).pow_right k).mul_right (hc.pow_right (k + 1))
  have hswap : Commute (y ^ (k + 1)) (a * a ^ k) := by
    rw [← pow_succ']
    exact (hc.pow_pow (k + 1) (k + 1)).symm
  refine ⟨hcomm, ?_, ?_⟩
  · calc
      (a ^ k * y ^ (k + 1)) * a * (a ^ k * y ^ (k + 1)) =
          a ^ k * (y ^ (k + 1) * (a * a ^ k)) * y ^ (k + 1) := by
        simp only [mul_assoc]
      _ = a ^ k * ((a * a ^ k) * y ^ (k + 1)) * y ^ (k + 1) := by rw [hswap.eq]
      _ = a ^ (k + (k + 1)) * y ^ (k + 1 + (k + 1)) := by
        rw [← pow_succ' a k, pow_add a k (k + 1), pow_add y (k + 1) (k + 1)]
        simp only [mul_assoc]
      _ = a ^ k * y ^ (k + 1) := cancel_pow h (k + 1) (k + 1)
  · calc
      a ^ (k + 1) * (a ^ k * y ^ (k + 1)) =
          a ^ (k + (k + 1)) * y ^ (k + 1 + 0) := by
        rw [Nat.add_zero, ← mul_assoc, ← pow_add, Nat.add_comm (k + 1) k]
      _ = a ^ k := by simpa only [pow_zero, mul_one] using cancel_pow h (k + 1) 0

/-- A monoid homomorphism maps a Drazin inverse to a Drazin inverse at the same exponent. -/
theorem map {N : Type*} [Monoid N] (h : IsDrazinInverseAt k a x) (f : M →* N) :
    IsDrazinInverseAt k (f a) (f x) := by
  refine ⟨h.commute.map f, ?_, ?_⟩
  · simpa only [map_mul] using congrArg f h.outer
  · simpa only [map_mul, map_pow] using congrArg f h.stable

/-- Conjugation by a unit carries Drazin inverses to Drazin inverses at the same exponent. -/
theorem conj (h : IsDrazinInverseAt k a x) (u : Mˣ) :
    IsDrazinInverseAt k ((u : M) * a * ↑u⁻¹) ((u : M) * x * ↑u⁻¹) := by
  let f : M →* M :=
    { toFun := fun b => (u : M) * b * ↑u⁻¹
      map_one' := by rw [mul_one, Units.mul_inv]
      map_mul' := fun b c => by
        calc
          (u : M) * (b * c) * ↑u⁻¹ = (u : M) * b * (↑u⁻¹ * u) * c * ↑u⁻¹ := by
            rw [Units.inv_mul, mul_one, mul_assoc (u : M) b c]
          _ = ((u : M) * b * ↑u⁻¹) * ((u : M) * c * ↑u⁻¹) := by simp only [mul_assoc] }
  exact h.map f

end IsDrazinInverseAt

/-- The group inverse is the Drazin inverse at exponent one. -/
abbrev IsGroupInverse (a x : M) : Prop := IsDrazinInverseAt 1 a x

/-- The group inverse relation comprises the two reflexive inverse equations and commutation. -/
theorem isGroupInverse_iff {a x : M} :
    IsGroupInverse a x ↔ Commute a x ∧ a * x * a = a ∧ x * a * x = x := by
  have shift (h : Commute a x) : a ^ (1 + 1) * x = a * x * a := by
    calc
      a ^ (1 + 1) * x = a * (a * x) := by rw [pow_two, mul_assoc]
      _ = a * (x * a) := by rw [h.eq]
      _ = a * x * a := (mul_assoc ..).symm
  constructor
  · intro h
    exact ⟨h.commute, by rw [← shift h.commute, h.stable, pow_one], h.outer⟩
  · rintro ⟨hc, hi, ho⟩
    exact ⟨hc, ho, by rw [shift hc, hi, pow_one]⟩

/-- If $x$ is a Drazin inverse of $a$, the group inverse of $x$ is $a^2x$. -/
theorem IsDrazinInverseAt.isGroupInverse_square_mul {a x : M} {k : ℕ}
    (h : IsDrazinInverseAt k a x) : IsGroupInverse x (a ^ 2 * x) := by
  have h₁ : a ^ 2 * x * x = a * x := calc
    a ^ 2 * x * x = a * (a * x ^ 2) := by simp only [pow_two, mul_assoc]
    _ = a * x := by rw [h.mul_sq]
  have hc : Commute x (a ^ 2 * x) :=
    (h.commute.symm.pow_right 2).mul_right (Commute.refl x)
  refine isGroupInverse_iff.mpr ⟨hc, ?_, ?_⟩
  · rw [hc.eq, h₁, mul_assoc, ← pow_two, h.mul_sq]
  · rw [h₁]
    calc
      a * x * (a ^ 2 * x) = a * (x * a ^ 2) * x := by simp only [mul_assoc]
      _ = a * (a ^ 2 * x) * x := by rw [(h.commute.pow_left 2).symm.eq]
      _ = a ^ 2 * (a * x ^ 2) := by simp only [pow_two, mul_assoc]
      _ = _ := by rw [h.mul_sq]
