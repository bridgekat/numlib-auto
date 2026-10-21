import Numlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Derivatives of quadratic radial powers on a line

The finite Leibniz rule for multiplication by a quadratic is the recurrence used to
differentiate odd integer powers of an inner-product norm along affine lines.
-/

open scoped Nat ContDiff

/-- Multiplication by a quadratic leaves only three terms in the finite Leibniz rule. -/
theorem iteratedDeriv_quadratic_mul {g : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hg : ContDiffAt ℝ (n + 2) g x) (c : ℝ) :
    iteratedDeriv (n + 2) (fun t => (c + t ^ 2) * g t) x =
      (c + x ^ 2) * iteratedDeriv (n + 2) g x +
      2 * (n + 2) * x * iteratedDeriv (n + 1) g x +
      (n + 2) * (n + 1) * iteratedDeriv n g x := by
  have hq : ContDiffAt ℝ (n + 2) (fun t : ℝ => c + t ^ 2) x := by fun_prop
  rw [iteratedDeriv_fun_mul hq hg]
  have hz : ∀ i ≥ 3, iteratedDeriv i (fun t : ℝ => c + t ^ 2) x = 0 := by
    intro i hi
    rw [iteratedDeriv_const_add (by omega) c, iteratedDeriv_pow,
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp
  rw [show n + 2 + 1 = 3 + n by omega, Finset.sum_range_add]
  have htail : (∑ i ∈ Finset.range n,
      ((n + 2).choose (3 + i) : ℝ) *
        iteratedDeriv (3 + i) (fun t : ℝ => c + t ^ 2) x *
        iteratedDeriv (n + 2 - (3 + i)) g x) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz _ (by omega), mul_zero, zero_mul]
  rw [htail, add_zero]
  have h1 : iteratedDeriv 1 (fun t : ℝ => c + t ^ 2) x = 2 * x := by
    rw [iteratedDeriv_const_add (by omega) c, iteratedDeriv_pow]
    norm_num [Nat.descFactorial]
  have h2 : iteratedDeriv 2 (fun t : ℝ => c + t ^ 2) x = 2 := by
    rw [iteratedDeriv_const_add (by omega) c, iteratedDeriv_pow]
    norm_num [Nat.descFactorial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iteratedDeriv_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, h1, h2]
  rw [Nat.choose_one_right, Nat.cast_choose_two]
  have he : n + 2 - 1 = n + 1 := by omega
  rw [he, Nat.add_sub_cancel]
  push_cast
  ring

/-- The derivative of a positive quadratic to a real power. -/
theorem deriv_quadratic_rpow {c : ℝ} (hc : 0 < c) (r x : ℝ) :
    deriv (fun t : ℝ => (c + t ^ 2) ^ r) x =
      2 * r * x * (c + x ^ 2) ^ (r - 1) := by
  have h := (((hasDerivAt_id x).pow 2).const_add c).rpow_const
    (p := r) (Or.inl (by positivity : c + x ^ 2 ≠ 0))
  simp only [Pi.pow_apply, id_eq] at h
  rw [h.deriv]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- The second derivative of a positive quadratic to a real power. -/
theorem iteratedDeriv_two_quadratic_rpow {c : ℝ} (hc : 0 < c) (r x : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => (c + t ^ 2) ^ r) x =
      2 * r * (c + x ^ 2) ^ (r - 1) +
      4 * r * (r - 1) * x ^ 2 * (c + x ^ 2) ^ (r - 2) := by
  have he : deriv (fun t : ℝ => (c + t ^ 2) ^ r) =
      fun t => 2 * r * t * (c + t ^ 2) ^ (r - 1) :=
    funext (deriv_quadratic_rpow hc r)
  rw [iteratedDeriv_succ', iteratedDeriv_one, he]
  have hp := (((hasDerivAt_id x).pow 2).const_add c).rpow_const
    (p := r - 1) (Or.inl (by positivity : c + x ^ 2 ≠ 0))
  have h := ((hasDerivAt_id x).const_mul (2 * r)).mul hp
  simp only [Pi.pow_apply, id_eq] at h
  change HasDerivAt (fun t : ℝ => 2 * r * t * (c + t ^ 2) ^ (r - 1)) _ x at h
  rw [h.deriv]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  rw [show r - 1 - 1 = r - 2 by ring]
  ring

/-- The first derivative beyond an odd radial power has a positive closed formula. -/
theorem iteratedDeriv_even_quadratic_half_pow {c : ℝ} (hc : 0 < c) (k : ℕ) (x : ℝ) :
    iteratedDeriv (2 * k + 2) (fun t : ℝ => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2)) x =
      (Nat.doubleFactorial (2 * k + 1) : ℝ) ^ 2 * c ^ (k + 1) *
        (c + x ^ 2) ^ (-((k : ℝ) + 3 / 2)) := by
  induction k generalizing x with
  | zero =>
    rw [show 2 * 0 + 2 = 2 from rfl, iteratedDeriv_two_quadratic_rpow hc]
    norm_num [Nat.doubleFactorial]
    have hq : c + x ^ 2 > 0 := by positivity
    have he : (c + x ^ 2) ^ (-(1 / 2 : ℝ)) =
        (c + x ^ 2) ^ (-(3 / 2 : ℝ)) * (c + x ^ 2) := by
      rw [← Real.rpow_add_one hq.ne']
      congr 1
      norm_num
    rw [he]
    ring
  | succ k ih =>
    let r : ℝ := -((k : ℝ) + 3 / 2)
    let C : ℝ := (Nat.doubleFactorial (2 * k + 1) : ℝ) ^ 2 * c ^ (k + 1)
    let g : ℝ → ℝ := fun t => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2)
    have hsm : ContDiff ℝ (⊤ : ℕ∞ω) g := by
      apply (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne
      intro t
      positivity
    have he : iteratedDeriv (2 * k + 2) g = fun t => C * (c + t ^ 2) ^ r :=
      funext ih
    have he1 (t : ℝ) : iteratedDeriv (2 * k + 2 + 1) g t =
        C * (2 * r * t * (c + t ^ 2) ^ (r - 1)) := by
      rw [iteratedDeriv_succ, he, deriv_const_mul_field, deriv_quadratic_rpow hc]
    have he2 (t : ℝ) : iteratedDeriv (2 * k + 2 + 2) g t = C *
        (2 * r * (c + t ^ 2) ^ (r - 1) +
          4 * r * (r - 1) * t ^ 2 * (c + t ^ 2) ^ (r - 2)) := by
      have hshift : iteratedDeriv (2 * k + 2 + 2) g =
          iteratedDeriv 2 (iteratedDeriv (2 * k + 2) g) := by
        rw [show 2 * k + 2 + 2 = 2 + (2 * k + 2) by omega]
        simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
      rw [hshift, he, iteratedDeriv_const_mul C (by
        apply (contDiffAt_const.add (contDiffAt_id.pow 2)).rpow_const_of_ne
        positivity),
        iteratedDeriv_two_quadratic_rpow hc]
    have hfun : (fun t : ℝ => (c + t ^ 2) ^ ((k + 1 : ℕ) + 1 / 2 : ℝ)) =
        fun t => (c + t ^ 2) * g t := by
      funext t
      dsimp [g]
      rw [mul_comm, ← Real.rpow_add_one (by positivity : c + t ^ 2 ≠ 0)]
      congr 1
      push_cast
      ring
    rw [hfun, show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega,
      iteratedDeriv_quadratic_mul (hsm.of_le le_top).contDiffAt c, he1, he2, he]
    simp only at *
    have hq : 0 < c + x ^ 2 := by positivity
    have hp0 : (c + x ^ 2) ^ r = (c + x ^ 2) ^ (r - 1) * (c + x ^ 2) := by
      rw [← Real.rpow_add_one hq.ne']
      congr 1
      ring
    have hp2 : (c + x ^ 2) ^ (r - 2) = (c + x ^ 2) ^ (r - 1) / (c + x ^ 2) := by
      rw [show r - 2 = (r - 1) - 1 by ring, Real.rpow_sub_one hq.ne']
    rw [hp0, hp2]
    have hdf : Nat.doubleFactorial (2 * (k + 1) + 1) =
        (2 * k + 3) * Nat.doubleFactorial (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        Nat.doubleFactorial_add_two]
    rw [hdf, Nat.cast_mul, pow_succ c (k + 1)]
    have hexp : -(((k + 1 : ℕ) : ℝ) + 3 / 2) = r - 1 := by dsimp [r]; push_cast; ring
    rw [hexp]
    dsimp [C, r]
    push_cast
    field_simp
    ring

/-- The derivative of highest odd order of a positive quadratic radial power is monotone. -/
theorem monotone_iteratedDeriv_odd_quadratic_half_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Monotone (iteratedDeriv (2 * k + 1)
      (fun t : ℝ => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2))) := by
  let g : ℝ → ℝ := fun t => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2)
  have hg : ContDiff ℝ (⊤ : ℕ∞ω) g := by
    apply (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne
    intro t
    positivity
  apply monotoneOn_univ.mp
  apply monotoneOn_of_deriv_nonneg convex_univ
    (hg.continuous_iteratedDeriv (2 * k + 1) le_top).continuousOn
    ((hg.of_le le_top).differentiable_iteratedDeriv' (2 * k + 1)).differentiableOn
  intro x _
  rw [← iteratedDeriv_succ]
  change 0 ≤ iteratedDeriv (2 * k + 2)
    (fun t : ℝ => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2)) x
  rw [iteratedDeriv_even_quadratic_half_pow hc]
  positivity
