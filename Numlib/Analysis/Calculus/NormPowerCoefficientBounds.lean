import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.Calculus.SymmetricDerivativeNorm

/-!
# Dimension-independent bounds for real norm powers

Directional derivatives of a real norm power satisfy a three-term recurrence obtained
from the differential equation of a quadratic power. Taking absolute values gives an
explicit coefficient bound, independent of the dimension of the real Hilbert space.
-/

open Filter Topology
open scoped RealInnerProductSpace

noncomputable section

/-- The quadratic power is smooth near the origin, regardless of its real parameters. -/
theorem contDiffAt_quadratic_rpow_zero (a b : ℝ) (n : ℕ) :
    ContDiffAt ℝ n (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 := by
  apply ContDiffAt.rpow_const_of_ne
  · fun_prop
  · norm_num

/-- Multiplication by the coordinate shifts the derivative jet at zero. -/
theorem iteratedDeriv_mul_coord_zero {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f 0) :
    iteratedDeriv (n + 1) (fun t => t * f t) 0 =
      (n + 1) * iteratedDeriv n f 0 := by
  have hid : ContDiffAt ℝ (n + 1) (fun t : ℝ => t) 0 := contDiffAt_id
  rw [iteratedDeriv_fun_mul hid hf]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, show 1 < n + 1 + 1 by omega, ite_true,
    Nat.choose_one_right, Nat.add_sub_cancel]
  push_cast
  ring

/-- Multiplication by the square of the coordinate shifts the derivative jet twice. -/
theorem iteratedDeriv_sq_mul_deriv_zero {f : ℝ → ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 2) f 0) :
    iteratedDeriv (n + 1) (fun t => t ^ 2 * deriv f t) 0 =
      (n + 1) * n * iteratedDeriv n f 0 := by
  have hd : ContDiffAt ℝ (n + 1) (deriv f) 0 :=
    hf.derivWithin (by exact_mod_cast (show (n + 1) + 1 ≤ n + 2 by omega))
  have hsq : ContDiffAt ℝ (n + 1) (fun t : ℝ => t ^ 2) 0 := by fun_prop
  rw [iteratedDeriv_fun_mul hsq hd]
  simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
  rcases n with _ | n
  · simp
  · have he : iteratedDeriv (n + 1) f 0 = iteratedDeriv n (deriv f) 0 := by
      rw [iteratedDeriv_succ']
    rw [ite_eq_left (by omega), show n + 1 + 1 - 2 = n by omega, ← he,
      Nat.cast_choose_two]
    push_cast
    rw [Nat.factorial_two]
    push_cast
    ring

/-- The actual directional coefficients of a quadratic power satisfy a three-term
recurrence. No sign or integrality assumption on the exponent is needed. -/
theorem iteratedDeriv_quadratic_rpow_succ_succ (a b : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 =
      b * (a - 2 * n - 2) *
          iteratedDeriv (n + 1) (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 +
        (n + 1) * (a - n) *
          iteratedDeriv n (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 := by
  let h : ℝ → ℝ := fun t => (1 + 2 * b * t + t ^ 2) ^ (a / 2)
  have hh : ContDiffAt ℝ (n + 2) h 0 := contDiffAt_quadratic_rpow_zero a b _
  have hh' : ContDiffAt ℝ (n + 1) (deriv h) 0 :=
    hh.derivWithin (by exact_mod_cast (show (n + 1) + 1 ≤ n + 2 by omega))
  have hh1 : ContDiffAt ℝ (n + 1) h 0 := hh.of_le (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))
  have hid : ContDiffAt ℝ (n + 1) (fun t : ℝ => t) 0 := contDiffAt_id
  have hsq : ContDiffAt ℝ (n + 1) (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hq : ContinuousAt (fun t : ℝ => 1 + 2 * b * t + t ^ 2) 0 := by fun_prop
  have hne : ∀ᶠ t : ℝ in 𝓝 0, 1 + 2 * b * t + t ^ 2 ≠ 0 :=
    hq.eventually_ne (by norm_num)
  have hode : (fun t : ℝ => deriv h t + 2 * b * (t * deriv h t) + t ^ 2 * deriv h t)
      =ᶠ[𝓝 0] fun t => a * b * h t + a * (t * h t) := by
    filter_upwards [hne] with t ht
    have hd := ((((hasDerivAt_id t).const_mul (2 * b)).const_add 1).add
      ((hasDerivAt_id t).pow 2)).rpow_const (p := a / 2) (Or.inl ht)
    change HasDerivAt h _ t at hd
    rw [hd.deriv]
    dsimp [h]
    rw [Real.rpow_sub_one ht]
    field_simp
  have key := hode.iteratedDeriv_eq (n + 1)
  rw [iteratedDeriv_fun_add (hh'.add (contDiffAt_const.mul (hid.mul hh')))
      (hsq.mul hh'), iteratedDeriv_fun_add hh' (contDiffAt_const.mul (hid.mul hh')),
    iteratedDeriv_const_mul _ (hid.mul hh'), iteratedDeriv_mul_coord_zero n hh',
    iteratedDeriv_sq_mul_deriv_zero n hh,
    iteratedDeriv_fun_add (contDiffAt_const.mul hh1) (contDiffAt_const.mul (hid.mul hh1)),
    iteratedDeriv_const_mul _ hh1, iteratedDeriv_const_mul _ (hid.mul hh1),
    iteratedDeriv_mul_coord_zero n hh1] at key
  have he1 : iteratedDeriv (n + 1) (deriv h) 0 = iteratedDeriv (n + 2) h 0 := by
    simpa only [Nat.add_assoc] using congrFun (iteratedDeriv_succ' (n := n + 1) (f := h)) 0 |>.symm
  have he0 : iteratedDeriv n (deriv h) 0 = iteratedDeriv (n + 1) h 0 := by
    rw [iteratedDeriv_succ']
  rw [he1, he0] at key
  change iteratedDeriv (n + 2) h 0 = _
  push_cast at key ⊢
  linear_combination key

/-- Explicit bounds for the derivative coefficients of a real norm power. The recurrence
is the absolute-value majorant of the actual quadratic-power recurrence. -/
noncomputable def normRpowDerivativeBound (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => |a|
  | n + 2 => |a - 2 * n - 2| * normRpowDerivativeBound a (n + 1) +
      (n + 1) * |a - n| * normRpowDerivativeBound a n

/-- The zeroth coefficient bound is one. -/
@[simp] theorem normRpowDerivativeBound_zero (a : ℝ) : normRpowDerivativeBound a 0 = 1 := rfl

/-- The first coefficient bound is the absolute value of the exponent. -/
@[simp] theorem normRpowDerivativeBound_one (a : ℝ) : normRpowDerivativeBound a 1 = |a| := rfl

/-- The coefficient bound is computed by an explicit two-step recurrence. -/
theorem normRpowDerivativeBound_succ_succ (a : ℝ) (n : ℕ) :
    normRpowDerivativeBound a (n + 2) =
      |a - 2 * n - 2| * normRpowDerivativeBound a (n + 1) +
        (n + 1) * |a - n| * normRpowDerivativeBound a n := by
  rw [normRpowDerivativeBound]

/-- Every coefficient bound is nonnegative. -/
theorem normRpowDerivativeBound_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ normRpowDerivativeBound a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => exact abs_nonneg a
  | more n hn hn1 =>
    rw [normRpowDerivativeBound_succ_succ]
    exact add_nonneg (mul_nonneg (abs_nonneg _) hn1)
      (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) hn)

/-- For a quadratic with correlation parameter of absolute value at most one, the
actual derivative coefficients are bounded by the explicit absolute-value recurrence. -/
theorem abs_iteratedDeriv_quadratic_rpow_zero_le (a : ℝ) {b : ℝ} (hb : |b| ≤ 1)
    (n : ℕ) :
    |iteratedDeriv n (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0| ≤
      normRpowDerivativeBound a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hd := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * b)).const_add 1).add
      ((hasDerivAt_id (0 : ℝ)).pow 2)).rpow_const (p := a / 2) (Or.inl (by norm_num))
    change HasDerivAt (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) _ 0 at hd
    have he : iteratedDeriv 1 (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0 =
        a * b := by
      rw [iteratedDeriv_one, hd.deriv]
      norm_num
      ring
    rw [he, normRpowDerivativeBound_one, abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  | more n hn hn1 =>
    rw [iteratedDeriv_quadratic_rpow_succ_succ, normRpowDerivativeBound_succ_succ]
    calc
      _ ≤ |b * (a - 2 * n - 2) *
            iteratedDeriv (n + 1) (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0| +
          |(n + 1) * (a - n) *
            iteratedDeriv n (fun t : ℝ => (1 + 2 * b * t + t ^ 2) ^ (a / 2)) 0| :=
        abs_add_le _ _
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)]
        calc
          _ ≤ (1 * |a - 2 * n - 2|) * normRpowDerivativeBound a (n + 1) +
              (n + 1) * |a - n| * normRpowDerivativeBound a n := by gcongr
          _ = _ := by rw [one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A norm power on a line through a unit vector, in a unit direction, is a quadratic
power whose correlation parameter is the inner product of the two unit vectors. -/
theorem normRpow_add_smul_unit_eq_quadratic (a : ℝ) {x u : E}
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    (fun t : ℝ => ‖x + t • u‖ ^ a) =
      fun t => (1 + 2 * ⟪x, u⟫ * t + t ^ 2) ^ (a / 2) := by
  funext t
  have hsq : ‖x + t • u‖ ^ 2 = 1 + 2 * ⟪x, u⟫ * t + t ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, hx, hu, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  rw [← hsq, ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- Every unit directional derivative at a unit vector obeys the explicit coefficient bound. -/
theorem abs_iteratedFDeriv_normRpow_unit_le (a : ℝ) (n : ℕ) {x u : E}
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x (fun _ => u)| ≤
      normRpowDerivativeBound a n := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  rw [iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
    (contDiffOn_normRpow a n) hx0 u, normRpow_add_smul_unit_eq_quadratic a hx hu]
  apply abs_iteratedDeriv_quadratic_rpow_zero_le
  simpa only [hx, hu, one_mul] using abs_real_inner_le_norm x u

variable [FiniteDimensional ℝ E]

/-- An explicit bound for every derivative of a real norm power at a unit vector.
The bound depends only on the exponent and order, independently of the dimension. -/
theorem norm_iteratedFDeriv_normRpow_unit_le (a : ℝ) (n : ℕ) {x : E}
    (hx : ‖x‖ = 1) :
    ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x‖ ≤ normRpowDerivativeBound a n := by
  rcases n with _ | n
  · simp [norm_iteratedFDeriv_zero, hx]
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  have hs := (contDiffOn_normRpow a (n + 1)).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx0)
  rw [← hs.diagonalNorm_iteratedFDeriv_eq_norm (by omega)]
  apply ContinuousMultilinearMap.diagonalNorm_le _ (normRpowDerivativeBound_nonneg a _)
  intro u hu
  exact abs_iteratedFDeriv_normRpow_unit_le a (n + 1) hx hu

/-- All derivatives of a real norm power have an explicit dimension-independent bound
off the origin. Homogeneity supplies the exact power of the radius. -/
theorem norm_iteratedFDeriv_normRpow_le_coefficient (a : ℝ) (n : ℕ) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ a) x‖ ≤
      normRpowDerivativeBound a n * ‖x‖ ^ (a - n) := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have he : x = ‖x‖ • u := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  rw [he, iteratedFDeriv_normRpow_smul a n hnx hu0, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hnx.le _), ← mul_comm]
  have h := norm_iteratedFDeriv_normRpow_unit_le a n hu
  have hscale : ‖‖x‖ • u‖ = ‖x‖ := by rw [norm_smul, norm_norm, hu, mul_one]
  rw [hscale]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hnx.le _)
