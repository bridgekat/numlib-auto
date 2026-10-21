import Numlib.Analysis.Calculus.NormPowerSmoothness
import Numlib.Analysis.Calculus.QuadraticRadialDerivatives
import Numlib.Analysis.Calculus.SymmetricDerivativeNorm
import Numlib.Analysis.Calculus.LipschitzOffPoint
import Mathlib.Data.Nat.Factorial.BigOperators
import Numlib.Algebra.Polynomial.Derivative
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Sharp derivatives of integer norm powers

Homogeneity identifies directional derivatives at infinity with their radial values.
-/

open Filter Topology
open scoped RealInnerProductSpace Nat ContDiff
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The top homogeneous derivative along a ray converges to the corresponding radial tensor. -/
theorem tendsto_iteratedFDeriv_norm_rpow_add_smul (m : ℕ) (x u : E) (hu : u ≠ 0)
    (v : Fin m → E) :
    Tendsto (fun t : ℝ => iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ))
      (x + t • u) v) atTop
      (𝓝 (iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ)) u v)) := by
  let g : ℝ → E := fun t => t⁻¹ • x + u
  have ht : Tendsto g atTop (𝓝 u) := by
    have h := ((tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).smul_const x).add_const u
    simpa only [zero_smul, zero_add] using h
  have hc : ContinuousAt (iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ))) u :=
    ((contDiffOn_normRpow (m : ℝ) m).contDiffAt
      (isOpen_compl_singleton.mem_nhds hu)).continuousAt_iteratedFDeriv le_rfl
  have hcv : ContinuousAt (fun z : E =>
      iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ)) z v) u :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => E) ℝ v).continuous.continuousAt.comp hc
  apply (hcv.tendsto.comp ht).congr'
  have hn : ∀ᶠ t in atTop, g t ≠ 0 := ht.eventually
    (isOpen_compl_singleton.mem_nhds hu)
  filter_upwards [hn, eventually_gt_atTop (0 : ℝ)] with t hgt ht0
  have he : x + t • u = t • g t := by
    dsimp [g]
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  rw [he, iteratedFDeriv_normRpow_smul (m : ℝ) m ht0 hgt, sub_self,
    Real.rpow_zero, one_smul]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Along a unit ray the top derivative of the corresponding norm power is the factorial. -/
theorem iteratedFDeriv_norm_rpow_apply_unit_nat (m : ℕ) {u : E} (hu : ‖u‖ = 1) :
    iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ)) u (fun _ => u) = (m ! : ℝ) := by
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have h := iteratedFDeriv_normRpow_apply_unit (m : ℝ) m hu0
  simp only [hu, inv_one, one_smul, sub_self, Real.one_rpow, mul_one] at h
  rw [h]
  have hp := Nat.descFactorial_eq_prod_range m m
  rw [Nat.descFactorial_self] at hp
  rw [hp, Nat.cast_prod, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m)]

omit [FiniteDimensional ℝ E] in
/-- The norm power restricted to a unit-speed affine line is a translated quadratic power. -/
theorem norm_rpow_add_smul_eq_quadratic (k : ℕ) (x u : E) (hu : ‖u‖ = 1) :
    (fun t : ℝ => ‖x + t • u‖ ^ ((2 * k + 1 : ℕ) : ℝ)) =
      fun t => (‖x‖ ^ 2 - ⟪x, u⟫ ^ 2 + (⟪x, u⟫ + t) ^ 2) ^
        ((k : ℝ) + 1 / 2) := by
  funext t
  have he : ‖x + t • u‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, u⟫ ^ 2 + (⟪x, u⟫ + t) ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      sq_abs]
    ring
  rw [← he, ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

omit [FiniteDimensional ℝ E] in
/-- A nonradial affine line has a monotone highest odd directional derivative. -/
theorem monotone_iteratedFDeriv_odd_norm_rpow_line (k : ℕ) (x u : E) (hu : ‖u‖ = 1)
    (hc : ⟪x, u⟫ ^ 2 < ‖x‖ ^ 2) :
    Monotone (fun t : ℝ => iteratedFDeriv ℝ (2 * k + 1)
      (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ)) (x + t • u) (fun _ => u)) := by
  let a : ℝ := ⟪x, u⟫
  let c : ℝ := ‖x‖ ^ 2 - a ^ 2
  have hc0 : 0 < c := sub_pos.mpr hc
  let g : ℝ → ℝ := fun t => (c + t ^ 2) ^ ((k : ℝ) + 1 / 2)
  have heq (t : ℝ) : iteratedFDeriv ℝ (2 * k + 1)
      (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ)) (x + t • u) (fun _ => u) =
      iteratedDeriv (2 * k + 1) g (a + t) := by
    have hn : x + t • u ≠ 0 := by
      intro he
      have hsq : ‖x + t • u‖ ^ 2 = c + (a + t) ^ 2 := by
        dsimp [c, a]
        rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hu,
          mul_one, sq_abs]
        ring
      rw [he, norm_zero, zero_pow (by omega)] at hsq
      nlinarith [sq_nonneg (a + t)]
    rw [iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
      (contDiffOn_normRpow _ _) hn u]
    have hline : (fun z : ℝ => ‖x + t • u + z • u‖ ^ ((2 * k + 1 : ℕ) : ℝ)) =
        fun z => g (a + t + z) := by
      funext z
      have hv : x + t • u + z • u = x + (t + z) • u := by module
      rw [hv]
      have h := congrFun (norm_rpow_add_smul_eq_quadratic k x u hu) (t + z)
      simpa only [g, c, a, add_assoc] using h
    rw [hline, iteratedDeriv_comp_const_add]
    simp
  simp_rw [heq]
  exact (monotone_iteratedDeriv_odd_quadratic_half_pow hc0 k).comp
    (monotone_const.add monotone_id)

/-- The highest odd directional derivative on a nonradial unit-speed line is at most
the exact factorial, obtained from its monotone radial limit. -/
theorem iteratedFDeriv_odd_norm_rpow_apply_const_le (k : ℕ) (x u : E) (hu : ‖u‖ = 1)
    (hc : ⟪x, u⟫ ^ 2 < ‖x‖ ^ 2) :
    iteratedFDeriv ℝ (2 * k + 1) (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ))
      x (fun _ => u) ≤ ((2 * k + 1)! : ℝ) := by
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hl := tendsto_iteratedFDeriv_norm_rpow_add_smul (2 * k + 1) x u hu0 (fun _ => u)
  rw [iteratedFDeriv_norm_rpow_apply_unit_nat _ hu] at hl
  simpa only [zero_smul, add_zero] using
    (monotone_iteratedFDeriv_odd_norm_rpow_line k x u hu hc).ge_of_tendsto hl 0

omit [FiniteDimensional ℝ E] in
private theorem odd_multilinear_apply_neg (k : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (2 * k + 1) => E) ℝ) (u : E) :
    T (fun _ => -u) = -T (fun _ => u) := by
  have h := T.map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => u)
  simpa only [neg_one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, neg_smul, one_smul] using h

/-- Every highest odd directional derivative in a unit direction is bounded by the
exact factorial, including the radial case. -/
theorem abs_iteratedFDeriv_odd_norm_rpow_apply_const_le (k : ℕ) {x : E} (hx : x ≠ 0)
    (u : E) (hu : ‖u‖ = 1) :
    |iteratedFDeriv ℝ (2 * k + 1) (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ))
      x (fun _ => u)| ≤ ((2 * k + 1)! : ℝ) := by
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hcs : ⟪x, u⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h := abs_real_inner_le_norm x u
    rw [hu, mul_one] at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  rcases hcs.lt_or_eq with hc | hc
  · apply abs_le.mpr
    constructor
    · have h := iteratedFDeriv_odd_norm_rpow_apply_const_le k x (-u)
        (by simpa only [norm_neg] using hu) (by simpa only [inner_neg_right, neg_sq] using hc)
      rw [odd_multilinear_apply_neg] at h
      linarith
    · exact iteratedFDeriv_odd_norm_rpow_apply_const_le k x u hu hc
  · let a : ℝ := ⟪x, u⟫
    have hrepr : x = a • u := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      have hn := norm_sub_sq_real x (a • u)
      rw [inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one, sq_abs] at hn
      have he : ‖x - a • u‖ ^ 2 = 0 := by dsimp [a] at hn ⊢; nlinarith only [hn, hc]
      nlinarith only [he, norm_nonneg (x - a • u)]
    have ha : a ≠ 0 := by intro he; rw [he, zero_smul] at hrepr; exact hx hrepr
    rcases lt_or_gt_of_ne ha with ha | ha
    · have he : x = (-a) • (-u) := by rw [hrepr]; module
      rw [he, iteratedFDeriv_normRpow_smul (2 * k + 1 : ℕ) (2 * k + 1)
        (neg_pos.mpr ha) (neg_ne_zero.mpr hu0), sub_self, Real.rpow_zero, one_smul]
      have h := odd_multilinear_apply_neg k
        (iteratedFDeriv ℝ (2 * k + 1) (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ)) (-u)) u
      rw [iteratedFDeriv_norm_rpow_apply_unit_nat _ (by simpa only [norm_neg] using hu)] at h
      rw [show iteratedFDeriv ℝ (2 * k + 1)
        (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ)) (-u) (fun _ => u) =
          -((2 * k + 1)! : ℝ) by linarith only [h]]
      simp
    · rw [hrepr, iteratedFDeriv_normRpow_smul (2 * k + 1 : ℕ) (2 * k + 1) ha hu0,
        sub_self, Real.rpow_zero, one_smul, iteratedFDeriv_norm_rpow_apply_unit_nat _ hu]
      simp

/-- The sharp top derivative bound for every odd positive integer exponent off the origin. -/
theorem norm_iteratedFDeriv_odd_norm_rpow_le (k : ℕ) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ (2 * k + 1) (fun z : E => ‖z‖ ^ ((2 * k + 1 : ℕ) : ℝ)) x‖ ≤
      ((2 * k + 1)! : ℝ) := by
  have hs := (contDiffOn_normRpow ((2 * k + 1 : ℕ) : ℝ) (2 * k + 1)).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx)
  rw [← hs.diagonalNorm_iteratedFDeriv_eq_norm (by omega)]
  apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
  intro u hu
  exact abs_iteratedFDeriv_odd_norm_rpow_apply_const_le k hx u hu

/-- The sharp top derivative bound for every even integer norm power off the origin. -/
theorem norm_iteratedFDeriv_even_norm_rpow_le (k : ℕ) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ (2 * k) (fun z : E => ‖z‖ ^ ((2 * k : ℕ) : ℝ)) x‖ ≤
      ((2 * k)! : ℝ) := by
  rcases k with _ | k
  · simp [norm_iteratedFDeriv_zero]
  have hs := (contDiffOn_normRpow ((2 * (k + 1) : ℕ) : ℝ) (2 * (k + 1))).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx)
  rw [← hs.diagonalNorm_iteratedFDeriv_eq_norm (by omega)]
  apply ContinuousMultilinearMap.diagonalNorm_le _ (by positivity)
  intro u hu
  rw [ContinuousMultilinearMap.diagonal,
    iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
      (contDiffOn_normRpow _ _) hx u]
  let P : Polynomial ℝ := (Polynomial.X ^ 2 + Polynomial.C (2 * ⟪x, u⟫) * Polynomial.X +
    Polynomial.C (‖x‖ ^ 2)) ^ (k + 1)
  have hP : Polynomial.IsMonicOfDegree P (2 * (k + 1)) :=
    (Polynomial.isMonicOfDegree_add_add_two (2 * ⟪x, u⟫) (‖x‖ ^ 2)).pow (k + 1)
  have he : (fun t : ℝ => ‖x + t • u‖ ^ ((2 * (k + 1) : ℕ) : ℝ)) =
      fun t => P.eval t := by
    funext t
    rw [Real.rpow_natCast, pow_mul]
    dsimp [P]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    congr 1
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      sq_abs]
    ring
  rw [he, Polynomial.iteratedDeriv_eval,
    Polynomial.iterate_derivative_eq_C_of_natDegree_eq hP.natDegree_eq,
    hP.leadingCoeff_eq, mul_one]
  simp

/-- Euler's identity for the actual homogeneous derivative tensor of a norm power. -/
theorem fderiv_iteratedFDeriv_norm_rpow_apply_self (r : ℝ) (j : ℕ) {x : E} (hx : x ≠ 0) :
    fderiv ℝ (iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ r)) x x =
      (r - j) • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ r) x := by
  let G := iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ r)
  have hd : DifferentiableAt ℝ G x :=
    ((contDiffOn_normRpow r (j + 1)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self j)
  have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hd' : HasFDerivAt G (fderiv ℝ G x) ((1 : ℝ) • x) := by
    simpa only [one_smul] using hd.hasFDerivAt
  have hcomp := hd'.comp_hasDerivAt (1 : ℝ) hline
  have he : (fun t : ℝ => G (t • x)) =ᶠ[𝓝 1]
      fun t => t ^ (r - j) • G x := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact iteratedFDeriv_normRpow_smul r j ht hx
  have hpow := ((hasDerivAt_id (1 : ℝ)).rpow_const (p := r - j)
    (Or.inl one_ne_zero)).smul_const (G x)
  have heq := (he.hasDerivAt_iff.mp hcomp).unique hpow
  simpa only [id_eq, Real.one_rpow, mul_one, one_mul, G] using heq

/-- The sharp highest derivative bound holds for every integer radial exponent. -/
theorem norm_iteratedFDeriv_nat_norm_rpow_le (m : ℕ) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ m (fun z : E => ‖z‖ ^ (m : ℝ)) x‖ ≤ (m ! : ℝ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exact norm_iteratedFDeriv_even_norm_rpow_le k hx
  · exact norm_iteratedFDeriv_odd_norm_rpow_le k hx

/-- Every derivative up to an integer radial exponent has the sharp falling-factorial
bound off the origin. The lower orders follow directly from Euler's homogeneous identity. -/
theorem norm_iteratedFDeriv_norm_nat_rpow_le {m j : ℕ} (hj : j ≤ m) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (m : ℝ)) x‖ ≤
      (Nat.descFactorial m j : ℝ) * ‖x‖ ^ (m - j) := by
  refine Nat.decreasingInduction'
    (P := fun i => ‖iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ (m : ℝ)) x‖ ≤
      (Nat.descFactorial m i : ℝ) * ‖x‖ ^ (m - i)) ?_ hj ?_
  · intro i him _ ih
    have hr : 0 < (m : ℝ) - i := sub_pos.mpr (by exact_mod_cast him)
    apply (mul_le_mul_iff_right₀ hr).mp
    have hnorm : ‖fderiv ℝ (iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ (m : ℝ))) x‖ =
        ‖iteratedFDeriv ℝ (i + 1) (fun z : E => ‖z‖ ^ (m : ℝ)) x‖ := by
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
    calc
      _ = ‖fderiv ℝ (iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ (m : ℝ))) x x‖ := by
        rw [fderiv_iteratedFDeriv_norm_rpow_apply_self _ _ hx, norm_smul,
          Real.norm_eq_abs, abs_of_pos hr, mul_comm]
      _ ≤ ‖iteratedFDeriv ℝ (i + 1) (fun z : E => ‖z‖ ^ (m : ℝ)) x‖ * ‖x‖ := by
        rw [← hnorm]
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((Nat.descFactorial m (i + 1) : ℝ) * ‖x‖ ^ (m - (i + 1))) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ih (norm_nonneg x)
      _ = _ := by
        rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega : i ≤ m),
          show m - i = m - (i + 1) + 1 by omega, pow_succ]
        ring
  · simpa only [Nat.sub_self, pow_zero, mul_one, Nat.descFactorial_self] using
      norm_iteratedFDeriv_nat_norm_rpow_le m hx

/-- Sharp all-order derivative bounds for a positive integer regularizing power,
including its derivatives at the origin below the radial exponent. -/
theorem norm_iteratedFDeriv_norm_pow_le_of_le {p j : ℕ} (hj : j ≤ p) (x : E) :
    ‖iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) x‖ ≤
      (Nat.descFactorial (p + 1) j : ℝ) * ‖x‖ ^ (p + 1 - j) := by
  by_cases hx : x = 0
  · subst x
    have hz := iteratedFDeriv_norm_rpow_zero_of_lt (E := E)
      (j := j) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : j < p + 1))
    simp only [Real.rpow_natCast] at hz
    rw [hz, norm_zero]
    positivity
  · simpa only [Real.rpow_natCast] using
      norm_iteratedFDeriv_norm_nat_rpow_le (by omega : j ≤ p + 1) hx

/-- The highest continuous jet of an integer norm power is globally Lipschitz with
the exact factorial constant, including pairs whose segment passes through zero. -/
theorem norm_sub_iteratedFDeriv_norm_pow_le (p : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
      iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y‖ ≤
      ((p + 1)! : ℝ) * ‖x - y‖ := by
  have hz : iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) 0 = 0 := by
    simpa only [Real.rpow_natCast] using iteratedFDeriv_norm_rpow_zero_of_lt (E := E)
      (j := p) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.lt_succ_self p)
  have hfac : Nat.descFactorial (p + 1) p = (p + 1)! := by
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left, Nat.factorial_one, one_mul] using
      Nat.factorial_mul_descFactorial (Nat.le_succ p)
  apply norm_sub_le_of_norm_fderiv_le_off_point (a := (0 : E))
  · intro z hz
    simpa only [Real.rpow_natCast] using
      ((contDiffOn_normRpow ((p + 1 : ℕ) : ℝ) (p + 1)).contDiffAt
        (isOpen_compl_singleton.mem_nhds hz)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self p)
  · intro z hz
    have h := norm_iteratedFDeriv_nat_norm_rpow_le (p + 1) hz
    simp only [Real.rpow_natCast] at h
    rw [iteratedFDeriv_succ_eq_comp_left] at h
    simpa only [Function.comp_apply, LinearIsometryEquiv.norm_map] using h
  · intro z
    rw [hz, sub_zero, sub_zero]
    simpa only [hfac, Nat.add_sub_cancel_left, pow_one] using
      norm_iteratedFDeriv_norm_pow_le_of_le (p := p) le_rfl z
