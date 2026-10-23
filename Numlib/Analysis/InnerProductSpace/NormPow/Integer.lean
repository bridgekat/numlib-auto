import Numlib.Analysis.InnerProductSpace.NormPow.Gaussian
import Numlib.Analysis.Calculus.FDeriv.Punctured

/-!
# Sharp integer norm-power bounds on real inner product spaces

At a nonzero point, every derivative evaluation lies in the finite span of the
point and its direction tuple. The actual derivative chain rule transfers the
finite-dimensional Gaussian bound to this subspace and back. Sharp growth then
proves the actual zero jets and global finite smoothness below the degree.
A sharp mean-value argument across the origin gives the exact factorial
Lipschitz constant for the derivative one order below the degree.

No finite-dimensional or completeness assumption is imposed on the space.
-/

namespace NormPower
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a nonzero point of a subspace, the actual norm-power derivative is
the restriction of the ambient derivative by the subspace inclusion. -/
theorem iteratedFDeriv_norm_pow_subtype (S : Submodule ℝ E) (m j : ℕ)
    {x : S} (hx : x ≠ 0) :
    iteratedFDeriv ℝ j (fun y : S => ‖y‖ ^ m) x =
      (iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) (x : E)).compContinuousLinearMap
        (fun _ => S.subtypeL) := by
  have hxE : (x : E) ≠ 0 := by simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using hx
  have hc : ContDiffOn ℝ j (fun y : E => ‖y‖ ^ m) ({0}ᶜ : Set E) := by
    simpa only [Real.rpow_natCast] using contDiffOn_normRpow (m : ℝ) j
  have hpre : IsOpen (S.subtypeL ⁻¹' ({0}ᶜ : Set E)) :=
    isOpen_compl_singleton.preimage S.subtypeL.continuous
  have hh := S.subtypeL.iteratedFDerivWithin_comp_right hc
    isOpen_compl_singleton.uniqueDiffOn hpre.uniqueDiffOn hxE le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hpre hxE,
    iteratedFDerivWithin_of_isOpen j isOpen_compl_singleton
      (show S.subtypeL x ∈ ({0}ᶜ : Set E) from hxE)] at hh
  exact hh

/-- Every derivative through the degree of a natural norm power has the
sharp falling-factorial operator bound at each nonzero point. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le {m j : ℕ} (hj : j ≤ m)
    {x : E} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (m.descFactorial j : ℝ) * ‖x‖ ^ (m - j) := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let w : Fin (j + 1) → E := Fin.cons x v
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range w)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  have hw (i : Fin (j + 1)) : w i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hxS : x ∈ S := hw 0
  let xs : S := ⟨x, hxS⟩
  let vs : Fin j → S := fun i => ⟨v i, hw i.succ⟩
  have hxs : xs ≠ 0 := by
    intro he
    exact hx (congrArg Subtype.val he)
  have hchain := congrArg (fun T : S [×j]→L[ℝ] ℝ => T vs)
    (iteratedFDeriv_norm_pow_subtype S m j hxs)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hchain
  have hb := (iteratedFDeriv ℝ j (fun y : S => ‖y‖ ^ m) xs).le_opNorm vs
  have hbound := norm_iteratedFDeriv_norm_pow_integer_le_finiteDimensional hj hxs
  have hh := hb.trans (mul_le_mul_of_nonneg_right hbound
    (Finset.prod_nonneg fun i _ => norm_nonneg (vs i)))
  rw [hchain] at hh
  exact hh



/-- Every actual norm-power derivative strictly below the natural degree
vanishes at the origin, on an arbitrary real inner product space. -/
theorem iteratedFDeriv_norm_pow_zero_of_lt {m j : ℕ} (hj : j < m) :
    iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) 0 = 0 := by
  induction j with
  | zero =>
    ext v
    simp only [iteratedFDeriv_zero_apply, norm_zero, zero_apply]
    exact zero_pow (by omega : m ≠ 0)
  | succ j ih =>
    have hj' : j < m := by omega
    have hz := ih hj'
    have hg (z : E) : ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) z‖ ≤
        (m.descFactorial j : ℝ) * ‖z‖ ^ (m - j) := by
      by_cases hzz : z = 0
      · subst z
        rw [hz, norm_zero]
        positivity
      · exact norm_iteratedFDeriv_norm_pow_integer_le hj'.le hzz
    have hd := hasFDerivAt_zero_of_norm_le_rpow (E := E)
      (a := ((m - j : ℕ) : ℝ)) (by exact_mod_cast (show 1 < m - j by omega))
      (C := (m.descFactorial j : ℝ)) (by simpa only [Real.rpow_natCast] using hg)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hd.fderiv]
    simp only [LinearIsometryEquiv.map_zero]

/-- The sharp falling-factorial derivative bound holds at every point for
each order strictly below the natural norm-power degree. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le_of_lt {m j : ℕ} (hj : j < m) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (m.descFactorial j : ℝ) * ‖x‖ ^ (m - j) := by
  by_cases hx : x = 0
  · subst x
    rw [iteratedFDeriv_norm_pow_zero_of_lt hj, norm_zero]
    positivity
  · exact norm_iteratedFDeriv_norm_pow_integer_le hj.le hx

/-- The actual derivative one order below a natural norm power is globally
Lipschitz with the exact degree-factorial constant. -/
theorem norm_sub_iteratedFDeriv_norm_pow_integer_le (p : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
      iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y‖ ≤
        ((p + 1).factorial : ℝ) * ‖x - y‖ := by
  let g := iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1))
  have hzero : g 0 = 0 := iteratedFDeriv_norm_pow_zero_of_lt (Nat.lt_succ_self p)
  have hdesc : (p + 1).descFactorial p = (p + 1).factorial := by
    have hh := Nat.factorial_mul_descFactorial (show p ≤ p + 1 by omega)
    rw [show p + 1 - p = 1 by omega] at hh
    simpa only [Nat.factorial_one, one_mul] using hh
  have hg (z : E) : ‖g z - g 0‖ ≤ ((p + 1).factorial : ℝ) * ‖z‖ := by
    rw [hzero, sub_zero]
    simpa only [g, hdesc, show p + 1 - p = 1 by omega, pow_one] using
      norm_iteratedFDeriv_norm_pow_integer_le_of_lt (Nat.lt_succ_self p) z
  have hd (z : E) (hz : z ≠ 0) : DifferentiableAt ℝ g z := by
    have hc : ContDiffAt ℝ (p + 1 : ℕ) (fun y : E => ‖y‖ ^ (p + 1)) z := by
      simpa only [Real.rpow_natCast] using
        (contDiffOn_normRpow ((p + 1 : ℕ) : ℝ) (p + 1)).contDiffAt
          (isOpen_compl_singleton.mem_nhds hz)
    exact hc.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self p)
  have hb (z : E) (hz : z ≠ 0) : ‖fderiv ℝ g z‖ ≤ ((p + 1).factorial : ℝ) := by
    rw [norm_fderiv_iteratedFDeriv]
    simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] using
      norm_iteratedFDeriv_norm_pow_integer_le (le_refl (p + 1)) hz
  exact norm_sub_le_of_punctured_fderiv_bound hg hd hb x y



/-- Every natural norm power is globally finitely smooth through each order
strictly below its degree, on any real inner product space. -/
theorem contDiff_norm_pow_integer {m n : ℕ} (hn : n < m) :
    ContDiff ℝ n (fun x : E => ‖x‖ ^ m) := by
  apply contDiff_nat_iff_continuous_differentiable.mpr
  constructor
  · intro j hj
    rw [continuous_iff_continuousAt]
    intro x
    have hjm : j < m := lt_of_le_of_lt hj hn
    by_cases hx : x = 0
    · subst x
      apply continuousAt_zero_of_norm_le_rpow (a := ((m - j : ℕ) : ℝ))
        (C := (m.descFactorial j : ℝ)) (by exact_mod_cast (show 0 < m - j by omega))
      intro z
      simpa only [Real.rpow_natCast] using
        norm_iteratedFDeriv_norm_pow_integer_le_of_lt hjm z
    · have hc : ContDiffOn ℝ j (fun y : E => ‖y‖ ^ m) ({0}ᶜ : Set E) := by
        simpa only [Real.rpow_natCast] using contDiffOn_normRpow (m : ℝ) j
      exact (ContinuousOn.continuousOn_iteratedFDeriv hc isOpen_compl_singleton le_rfl).continuousAt
        (isOpen_compl_singleton.mem_nhds hx)
  · intro j hj x
    by_cases hx : x = 0
    · subst x
      apply (hasFDerivAt_zero_of_norm_le_rpow (a := ((m - j : ℕ) : ℝ))
        (C := (m.descFactorial j : ℝ))
        (by exact_mod_cast (show 1 < m - j by omega)) ?_).differentiableAt
      intro z
      simpa only [Real.rpow_natCast] using
        norm_iteratedFDeriv_norm_pow_integer_le_of_lt (show j < m by omega) z
    · have hc : ContDiffAt ℝ (j + 1 : ℕ) (fun y : E => ‖y‖ ^ m) x := by
        simpa only [Real.rpow_natCast] using
          (contDiffOn_normRpow (m : ℝ) (j + 1)).contDiffAt
            (isOpen_compl_singleton.mem_nhds hx)
      exact hc.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)

/-- The sharp integer norm-power derivative bound in factorial-quotient form,
including the origin for every order strictly below the degree. -/
theorem norm_iteratedFDeriv_norm_pow_integer_le_factorial
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
  · exact norm_iteratedFDeriv_norm_pow_integer_le_of_lt hjlt x
  · exact norm_iteratedFDeriv_norm_pow_integer_le hj hx

end NormPower
