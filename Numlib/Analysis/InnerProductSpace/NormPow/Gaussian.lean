import Numlib.Analysis.Calculus.ParametricIntegral.Gaussian
import Numlib.Analysis.SpecialFunctions.Pow.Absolute

/-!
# Sharp integer norm-power bounds from Gaussian differentiation

The actual lower-order Fréchet derivatives of a norm power are normalized
Gaussian averages of genuine scalar absolute-power jets. Dominated
differentiation proves this identity one evaluated direction at a time. Sharp
Gaussian product moments give the falling-factorial operator bounds. The exact
scalar factorial Lipschitz estimate gives the global highest-jet estimate,
including segments through zero; actual off-origin smoothness then controls
the top derivative as well.

The estimates are valid on every finite-dimensional real inner product space.
Their public statements need no measurable-space structure.
-/

open MeasureTheory ProbabilityTheory
namespace NormPower
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian integral of a genuine scalar absolute-power jet equals
the corresponding actual norm-power derivative times the positive scalar moment. -/
theorem integral_projectionJet_abs_pow_eq {m j : ℕ} (hj : j < m) (x : E) (v : Fin j → E) :
    ∫ g : E, projectionJet (fun t : ℝ => |t| ^ m) j x v g ∂(stdGaussian E) =
      (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
        iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x v := by
  induction j generalizing x with
  | zero =>
    simp only [projectionJet_eq, iteratedDeriv_zero, Fin.prod_univ_zero, mul_one,
      iteratedFDeriv_zero_apply]
    have he : (fun g : E => |inner ℝ g x| ^ m) = fun g => |inner ℝ x g| ^ m :=
      funext fun g => by rw [real_inner_comm g x]
    rw [he, integral_abs_inner_pow_stdGaussian]
    ring
  | succ j ih =>
    have hj' : j < m := by omega
    have hc : ContDiff ℝ (j + 1 : ℕ) (fun t : ℝ => |t| ^ m) := Real.contDiff_abs_pow hj
    have hd := integral_projectionJet_hasFDerivAt (E := E) (m := m) (j := j)
      (Nat.le_of_lt hj) (Nat.cast_nonneg (m.descFactorial j))
      (Nat.cast_nonneg (m.descFactorial (j + 1))) hc
      (fun t => (Real.abs_iteratedDeriv_abs_pow hj' t).le)
      (fun t => (Real.abs_iteratedDeriv_abs_pow hj t).le) x (Fin.tail v)
    have heq : (fun y : E => ∫ g : E,
        projectionJet (fun t : ℝ => |t| ^ m) j y (Fin.tail v) g ∂(stdGaussian E)) =
        fun y : E => (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
          iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ m) y (Fin.tail v) := by
      funext y
      exact ih hj' y (Fin.tail v)
    have hcn : ContDiff ℝ (j + 1 : ℕ) (fun z : E => ‖z‖ ^ m) := by
      simpa only [Real.rpow_natCast] using
        contDiff_normRpow_of_nat_lt (E := E) (lam := (m : ℝ)) (n := j + 1)
          (by exact_mod_cast hj)
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ m)) x :=
      hcn.contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
    have hsc : DifferentiableAt ℝ
        (fun y : E => iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ m) y (Fin.tail v)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) ℝ
        (Fin.tail v)).differentiableAt.comp
        x hdiff
    have hleft := hd.2
    rw [heq] at hleft
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L (v 0))
      (hleft.unique (hsc.hasFDerivAt.const_mul (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1))))
    rw [ContinuousLinearMap.integral_apply hd.1] at hh
    simp only [← projectionJet_cons, Fin.cons_self_tail, smul_apply, smul_eq_mul] at hh
    rw [← hdiff.iteratedFDeriv_succ_apply_left' (m := v)] at hh
    exact hh



/-- Every actual norm-power derivative strictly below the degree has this
normalized Gaussian representation on arbitrary direction tuples. -/
theorem iteratedFDeriv_norm_pow_apply_eq_gaussian {m j : ℕ} (hj : j < m)
    (x : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x v =
      (∫ g : E, iteratedDeriv j (fun t : ℝ => |t| ^ m) (inner ℝ g x) *
        ∏ i, inner ℝ g (v i) ∂(stdGaussian E)) /
          (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) := by
  apply (eq_div_iff (integral_abs_pow_gaussianReal_pos m).ne').mpr
  rw [mul_comm, ← integral_projectionJet_abs_pow_eq hj]
  rfl

/-- The genuine Gaussian scalar-jet average satisfies the exact
falling-factorial evaluated-direction bound. -/
theorem norm_integral_projectionJet_abs_pow_le {m j : ℕ} (hj : j < m)
    (x : E) (v : Fin j → E) :
    ‖∫ g : E, projectionJet (fun t : ℝ => |t| ^ m) j x v g ∂(stdGaussian E)‖ ≤
      (m.descFactorial j : ℝ) * (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
        ‖x‖ ^ (m - j) * ∏ i, ‖v i‖ := by
  have hmoment : (∫ g : E, |inner ℝ g x| ^ (m - j) *
      ∏ i, |inner ℝ g (v i)| ∂(stdGaussian E)) ≤
      (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) * ‖x‖ ^ (m - j) * ∏ i, ‖v i‖ := by
    simpa only [real_inner_comm, Nat.sub_add_cancel hj.le] using
      integral_abs_inner_pow_mul_prod_stdGaussian_le (m - j) j x v
  calc
    _ ≤ ∫ g : E, ‖projectionJet (fun t : ℝ => |t| ^ m) j x v g‖ ∂(stdGaussian E) :=
      norm_integral_le_integral_norm _
    _ = (m.descFactorial j : ℝ) * ∫ g : E, |inner ℝ g x| ^ (m - j) *
        ∏ i, |inner ℝ g (v i)| ∂(stdGaussian E) := by
      simp only [projectionJet_eq, Real.norm_eq_abs, abs_mul,
        Real.abs_iteratedDeriv_abs_pow hj, Finset.abs_prod]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ ≤ (m.descFactorial j : ℝ) * ((∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
        ‖x‖ ^ (m - j) * ∏ i, ‖v i‖) :=
      mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg _)
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every actual norm-power derivative strictly below the degree has the
sharp falling-factorial operator bound, including at the origin. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le_of_lt_finiteDimensional
    {m j : ℕ} (hj : j < m) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (m.descFactorial j : ℝ) * ‖x‖ ^ (m - j) := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hc := integral_abs_pow_gaussianReal_pos m
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
        ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x v‖ =
        ‖∫ g : E, projectionJet (fun t : ℝ => |t| ^ m) j x v g ∂(stdGaussian E)‖ := by
      rw [integral_projectionJet_abs_pow_eq hj, norm_mul, Real.norm_of_nonneg hc.le]
    _ ≤ (m.descFactorial j : ℝ) * (∫ t : ℝ, |t| ^ m ∂(gaussianReal 0 1)) *
        ‖x‖ ^ (m - j) * ∏ i, ‖v i‖ := norm_integral_projectionJet_abs_pow_le hj x v
    _ = _ := by ring



omit [MeasurableSpace E] [BorelSpace E] in
/-- The actual derivative one order below any natural norm power is globally
Lipschitz with the exact degree-factorial constant. -/
theorem norm_sub_iteratedFDeriv_norm_pow_integer_le_finiteDimensional (p : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
      iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y‖ ≤
        ((p + 1).factorial : ℝ) * ‖x - y‖ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hc := integral_abs_pow_gaussianReal_pos (p + 1)
  have hj : p < p + 1 := Nat.lt_succ_self p
  have hcont : Continuous (iteratedDeriv p (fun t : ℝ => |t| ^ (p + 1))) :=
    (Real.contDiff_abs_pow hj).continuous_iteratedDeriv p le_rfl
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hint (z : E) : Integrable (fun g : E =>
      projectionJet (fun t : ℝ => |t| ^ (p + 1)) p z v g) (stdGaussian E) :=
    integrable_projectionJet hj.le (Nat.cast_nonneg ((p + 1).descFactorial p)) hcont
      (fun t => (Real.abs_iteratedDeriv_abs_pow hj t).le) z v
  have hprodint : Integrable (fun g : E => |inner ℝ g (x - y)| *
      ∏ i, |inner ℝ g (v i)|) (stdGaussian E) := by
    simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, real_inner_comm] using
      integrable_prod_abs_inner_stdGaussian (Fin.cons (x - y) v)
  have hpoint (g : E) : ‖projectionJet (fun t : ℝ => |t| ^ (p + 1)) p x v g -
      projectionJet (fun t : ℝ => |t| ^ (p + 1)) p y v g‖ ≤
      ((p + 1).factorial : ℝ) * (|inner ℝ g (x - y)| * ∏ i, |inner ℝ g (v i)|) := by
    rw [Real.norm_eq_abs, projectionJet_eq, projectionJet_eq, ← sub_mul, abs_mul,
      Finset.abs_prod]
    have hh := Real.abs_sub_iteratedDeriv_abs_pow_le p (inner ℝ g x) (inner ℝ g y)
    rw [← inner_sub_right] at hh
    have hnonneg : 0 ≤ ∏ i, |inner ℝ g (v i)| :=
      Finset.prod_nonneg fun i _ => abs_nonneg _
    have hh' := mul_le_mul_of_nonneg_right hh hnonneg
    exact hh'.trans_eq (by ring)
  have hmoment : (∫ g : E, |inner ℝ g (x - y)| *
      ∏ i, |inner ℝ g (v i)| ∂(stdGaussian E)) ≤
      (∫ t : ℝ, |t| ^ (p + 1) ∂(gaussianReal 0 1)) * ‖x - y‖ * ∏ i, ‖v i‖ := by
    simpa only [real_inner_comm, pow_one, Nat.add_comm 1 p] using
      integral_abs_inner_pow_mul_prod_stdGaussian_le 1 p (x - y) v
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (∫ t : ℝ, |t| ^ (p + 1) ∂(gaussianReal 0 1)) *
        ‖(iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
          iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y) v‖ =
        ‖∫ g : E, (projectionJet (fun t : ℝ => |t| ^ (p + 1)) p x v g -
          projectionJet (fun t : ℝ => |t| ^ (p + 1)) p y v g) ∂(stdGaussian E)‖ := by
      rw [integral_sub (hint x) (hint y), integral_projectionJet_abs_pow_eq hj,
        integral_projectionJet_abs_pow_eq hj, ← mul_sub, norm_mul,
        Real.norm_of_nonneg hc.le]
      rfl
    _ ≤ ∫ g : E, ‖projectionJet (fun t : ℝ => |t| ^ (p + 1)) p x v g -
        projectionJet (fun t : ℝ => |t| ^ (p + 1)) p y v g‖ ∂(stdGaussian E) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g : E, ((p + 1).factorial : ℝ) *
        (|inner ℝ g (x - y)| * ∏ i, |inner ℝ g (v i)|) ∂(stdGaussian E) :=
      integral_mono ((hint x).sub (hint y)).norm (hprodint.const_mul _) hpoint
    _ = ((p + 1).factorial : ℝ) * ∫ g : E, |inner ℝ g (x - y)| *
        ∏ i, |inner ℝ g (v i)| ∂(stdGaussian E) := integral_const_mul _ _
    _ ≤ ((p + 1).factorial : ℝ) * ((∫ t : ℝ, |t| ^ (p + 1) ∂(gaussianReal 0 1)) *
        ‖x - y‖ * ∏ i, ‖v i‖) := mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg _)
    _ = _ := by ring



omit [MeasurableSpace E] [BorelSpace E] in
/-- All derivative orders through the degree of a natural norm power have
the sharp falling-factorial operator bound at every nonzero point. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le_finiteDimensional
    {m j : ℕ} (hj : j ≤ m) {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (m.descFactorial j : ℝ) * ‖x‖ ^ (m - j) := by
  obtain hjlt | heq := lt_or_eq_of_le hj
  · exact norm_iteratedFDeriv_norm_pow_integer_le_of_lt_finiteDimensional hjlt x
  subst j
  by_cases hm : m = 0
  · subst m
    simp only [norm_iteratedFDeriv_zero, pow_zero, norm_one, Nat.descFactorial_zero,
      Nat.cast_one, Nat.sub_self, one_mul, le_refl]
  have hmp : m - 1 + 1 = m := by omega
  have hc : ContDiffAt ℝ (m : ℕ) (fun y : E => ‖y‖ ^ m) x := by
    simpa only [Real.rpow_natCast] using
      (contDiffOn_normRpow (m : ℝ) m).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
  have hd := hc.differentiableAt_iteratedFDeriv (m := m - 1)
    (by exact_mod_cast (show m - 1 < m by omega))
  have hh := hd.hasFDerivAt.le_of_lip' (Nat.cast_nonneg m.factorial)
    (Filter.Eventually.of_forall fun y : E => ?_)
  · rw [norm_fderiv_iteratedFDeriv, hmp] at hh
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] using hh
  · simpa only [hmp] using
      norm_sub_iteratedFDeriv_norm_pow_integer_le_finiteDimensional (m - 1) y x



omit [MeasurableSpace E] [BorelSpace E] in
/-- The sharp integer norm-power derivative bound in factorial-quotient form,
including the origin for every order strictly below the degree. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le_factorial_finiteDimensional
    {m j : ℕ} (hj : j ≤ m) (x : E) (hreg : j < m ∨ x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (m.factorial : ℝ) / (m - j).factorial * ‖x‖ ^ (m - j) := by
  have hdesc : (m.descFactorial j : ℝ) = (m.factorial : ℝ) / (m - j).factorial := by
    apply (eq_div_iff (by positivity : ((m - j).factorial : ℝ) ≠ 0)).mpr
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_descFactorial hj)
    push_cast at hh
    nlinarith
  rw [← hdesc]
  obtain hjlt | hx := hreg
  · exact norm_iteratedFDeriv_norm_pow_integer_le_of_lt_finiteDimensional hjlt x
  · exact norm_iteratedFDeriv_norm_pow_integer_le_finiteDimensional hj hx

end NormPower
