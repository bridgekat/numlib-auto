import Numlib.Analysis.Calculus.HermiteInterpolation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Uniform two-endpoint Hermite interpolation

The canonical Chinese-remainder interpolant has prescribed jets at both endpoints
and degree at most `2p+1`. Fixed unit-interval basis polynomials interpolate a
normalized terminal residual. Scaling them by `s^(p+1)` after the substitution
`t/s` gives the general interpolant. Compactness bounds the finitely many basis
derivatives before the interval length and interpolation data are chosen.
The resulting bounds are uniform in those data and require no coefficient-matrix
inverse estimate or additional regularity assumption.
-/

open Polynomial Set
namespace Hermite
/-- The canonical polynomial matching the two endpoint jets through order `p`.
The endpoint conclusions require distinct endpoints; the definition itself is total. -/
noncomputable def endpointPolynomial (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) : ℝ[X] :=
  interpolateJet (Multiset.replicate (p + 1) 0 + Multiset.replicate (p + 1) s)
    (fun x j => if x = 0 then a j / j.factorial else b j / j.factorial)

/-- Every prescribed initial derivative is attained at zero. -/
theorem endpointPolynomial_zero {p : ℕ} {s : ℝ} (hs : s ≠ 0) (a b : ℕ → ℝ)
    {j : ℕ} (hj : j ≤ p) :
    (derivative^[j] (endpointPolynomial p s a b)).eval 0 = a j := by
  have h := isJetInterpolant_iff_coeff_taylor.mp
    (isJetInterpolant_interpolateJet
      (Multiset.replicate (p + 1) (0 : ℝ) + Multiset.replicate (p + 1) s)
      (fun x j => if x = 0 then a j / j.factorial else b j / j.factorial))
    0 (by simp) j (by simp [Multiset.count_replicate, hs, Ne.symm hs]; omega)
  rw [coeff_taylor_eq_eval_iterate_derivative_div] at h
  simpa only [endpointPolynomial, ite_true, div_left_inj' (by positivity : (j.factorial
    : ℝ) ≠ 0)] using h

/-- Every prescribed terminal derivative is attained at the second endpoint. -/
theorem endpointPolynomial_right {p : ℕ} {s : ℝ} (hs : s ≠ 0) (a b : ℕ → ℝ)
    {j : ℕ} (hj : j ≤ p) :
    (derivative^[j] (endpointPolynomial p s a b)).eval s = b j := by
  have h := isJetInterpolant_iff_coeff_taylor.mp
    (isJetInterpolant_interpolateJet
      (Multiset.replicate (p + 1) (0 : ℝ) + Multiset.replicate (p + 1) s)
      (fun x j => if x = 0 then a j / j.factorial else b j / j.factorial))
    s (by simp) j (by simp [Multiset.count_replicate, hs]; omega)
  rw [coeff_taylor_eq_eval_iterate_derivative_div] at h
  simpa only [endpointPolynomial, ite_eq_right hs, div_left_inj' (by positivity :
    (j.factorial : ℝ) ≠ 0)] using h

/-- The canonical endpoint polynomial has degree strictly below `2p+2`. -/
theorem endpointPolynomial_degree_lt (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) :
    (endpointPolynomial p s a b).degree < ((2 * p + 2 : ℕ) : WithBot ℕ) := by
  have h := degree_interpolateJet_lt
    (Multiset.replicate (p + 1) (0 : ℝ) + Multiset.replicate (p + 1) s)
    (fun x j => if x = 0 then a j / j.factorial else b j / j.factorial)
  simpa only [endpointPolynomial, Multiset.card_add, Multiset.card_replicate,
    show p + 1 + (p + 1) = 2 * p + 2 by omega] using h
/-- The unit-interval basis polynomial with one terminal derivative equal to one
and every other endpoint derivative through order `p` equal to zero. -/
noncomputable def endpointBasis (p : ℕ) (i : Fin (p + 1)) : ℝ[X] :=
  endpointPolynomial p 1 (fun _ => 0) (fun j => if j = i.val then 1 else 0)

/-- The unit-interval correction interpolating a finite terminal residual jet
and a zero initial jet. -/
noncomputable def unitResidualPolynomial (p : ℕ) (r : Fin (p + 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (p + 1), r i • endpointBasis p i

/-- The correction has zero initial jet through order `p`. -/
theorem unitResidualPolynomial_zero (p : ℕ) (r : Fin (p + 1) → ℝ) {j : ℕ} (hj : j ≤ p) :
    (derivative^[j] (unitResidualPolynomial p r)).eval 0 = 0 := by
  simp only [unitResidualPolynomial, iterate_derivative_sum, iterate_derivative_smul,
    eval_finsetSum, eval_smul, endpointBasis,
    endpointPolynomial_zero (by norm_num : (1 : ℝ) ≠ 0) _ _ hj, smul_zero,
    Finset.sum_const_zero]

/-- The correction attains the specified terminal jet through order `p`. -/
theorem unitResidualPolynomial_one (p : ℕ) (r : Fin (p + 1) → ℝ) {j : ℕ} (hj : j ≤ p) :
    (derivative^[j] (unitResidualPolynomial p r)).eval 1 = r ⟨j, by omega⟩ := by
  simp only [unitResidualPolynomial, iterate_derivative_sum, iterate_derivative_smul,
    eval_finsetSum, eval_smul, endpointBasis,
    endpointPolynomial_right (by norm_num : (1 : ℝ) ≠ 0) _ _ hj, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (p + 1))]
  · simp
  · intro i _hi hine
    have hji : j ≠ i.val := by
      intro heq
      apply hine
      exact Fin.ext heq.symm
    simp [hji]
  · simp

/-- All derivatives through order `p+1` of the residual interpolant are uniformly
bounded on the unit interval when its data lie in a fixed cube. The bound precedes
the interpolation data and evaluation point. -/
theorem unitResidualPolynomial_uniform_bound (p : ℕ) (κ : ℝ) :
    ∃ M > 0, ∀ r : Fin (p + 1) → ℝ, (∀ i, |r i| ≤ κ) →
      ∀ j ≤ p + 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |(derivative^[j] (unitResidualPolynomial p r)).eval t| ≤ M := by
  let S : Set ((Fin (p + 1) → ℝ) × ℝ) :=
    Icc (fun _ => -κ) (fun _ => κ) ×ˢ Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let G : ((Fin (p + 1) → ℝ) × ℝ) → (Fin (p + 2) → ℝ) := fun z j =>
    (derivative^[j.val] (unitResidualPolynomial p z.1)).eval z.2
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    simp only [G, unitResidualPolynomial, iterate_derivative_sum, iterate_derivative_smul,
      eval_finsetSum, eval_smul, smul_eq_mul]
    fun_prop
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro r hr j hj t ht
  have hm : (r,t) ∈ S := ⟨⟨fun i => (abs_le.mp (hr i)).1,
    fun i => (abs_le.mp (hr i)).2⟩, ht⟩
  have hc := norm_le_pi_norm (G (r,t)) (⟨j,by omega⟩ : Fin (p + 2))
  have hc' : |(derivative^[j] (unitResidualPolynomial p r)).eval t| ≤ ‖G (r,t)‖ := by
    simpa only [G, Real.norm_eq_abs] using hc
  exact hc'.trans ((hM (r,t) hm).trans (by linarith [le_max_left M (0 : ℝ)]))

/-- The factorial-normalized initial Taylor polynomial determined by a jet. -/
noncomputable def initialPolynomial (p : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  jetPoly (fun j => a j / j.factorial) 0 (p + 1)

/-- The initial Taylor polynomial attains its prescribed jet at zero. -/
theorem initialPolynomial_zero (p : ℕ) (a : ℕ → ℝ) {j : ℕ} (hj : j ≤ p) :
    (derivative^[j] (initialPolynomial p a)).eval 0 = a j := by
  have h := coeff_taylor_jetPoly (fun j => a j / (j.factorial : ℝ)) (0 : ℝ) (p + 1) j
  rw [coeff_taylor_eq_eval_iterate_derivative_div, ite_eq_left (by omega)] at h
  simpa only [initialPolynomial, div_left_inj' (by positivity : (j.factorial : ℝ) ≠ 0)] using h

/-- The initial Taylor polynomial has degree at most `p`. -/
theorem initialPolynomial_degree_lt (p : ℕ) (a : ℕ → ℝ) :
    (initialPolynomial p a).degree < ((p + 1 : ℕ) : WithBot ℕ) :=
  degree_jetPoly_lt _ _ _

/-- Initial Taylor polynomials and all their derivatives through order `p`
are uniformly bounded on a fixed bounded interval for bounded initial jets. -/
theorem initialPolynomial_uniform_bound (p : ℕ) (κ : ℝ) :
    ∃ T > 0, ∀ a : ℕ → ℝ, (∀ j ≤ p, |a j| ≤ κ) →
      ∀ j ≤ p, ∀ t ∈ Icc (0 : ℝ) κ,
        |(derivative^[j] (initialPolynomial p a)).eval t| ≤ T := by
  let extend : (Fin (p + 1) → ℝ) → ℕ → ℝ := fun r j =>
    if hj : j < p + 1 then r ⟨j,hj⟩ else 0
  let S : Set ((Fin (p + 1) → ℝ) × ℝ) :=
    Icc (fun _ => -κ) (fun _ => κ) ×ˢ Icc (0 : ℝ) κ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let G : ((Fin (p + 1) → ℝ) × ℝ) → (Fin (p + 1) → ℝ) := fun z j =>
    (derivative^[j.val] (initialPolynomial p (extend z.1))).eval z.2
  have hG : Continuous G := by
    apply continuous_pi
    intro j
    simp only [G, initialPolynomial, jetPoly, sub_zero, C_0,
      iterate_derivative_sum, iterate_derivative_C_mul, eval_finsetSum, eval_mul, eval_C]
    apply continuous_finsetSum
    intro i hi
    have hi' : i < p + 1 := Finset.mem_range.mp hi
    simp only [extend, dite_eq_left hi']
    fun_prop
  obtain ⟨T,hT⟩ := hS.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max T 0 + 1, by positivity, ?_⟩
  intro a ha j hj t ht
  let r : Fin (p + 1) → ℝ := fun i => a i
  have hr : ∀ i, |r i| ≤ κ := fun i => ha i (by omega)
  have hm : (r,t) ∈ S := ⟨⟨fun i => (abs_le.mp (hr i)).1,
    fun i => (abs_le.mp (hr i)).2⟩, ht⟩
  have heq : initialPolynomial p (extend r) = initialPolynomial p a := by
    apply jetPoly_congr
    intro i hi
    simp only [extend, dite_eq_left hi, r]
  have hc := norm_le_pi_norm (G (r,t)) (⟨j,by omega⟩ : Fin (p + 1))
  have hc' : |(derivative^[j] (initialPolynomial p a)).eval t| ≤ ‖G (r,t)‖ := by
    simpa only [G, heq, Real.norm_eq_abs] using hc
  exact hc'.trans ((hT (r,t) hm).trans (by linarith [le_max_left T (0 : ℝ)]))

/-- Iterated polynomial differentiation under a scalar change of variable. -/
theorem iterate_derivative_comp_scale (Q : ℝ[X]) (c : ℝ) (j : ℕ) :
    derivative^[j] (Q.comp (C c * X)) =
      c ^ j • (derivative^[j] Q).comp (C c * X) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, derivative_smul, derivative_comp,
      derivative_C_mul, derivative_X, mul_one, smul_eq_C_mul,
      Function.iterate_succ_apply', smul_eq_C_mul, pow_succ, map_mul]
    ring

/-- The initial Taylor polynomial plus a rescaled unit-interval residual correction. -/
noncomputable def residualScaledPolynomial (p : ℕ) (s : ℝ) (a : ℕ → ℝ)
    (r : Fin (p + 1) → ℝ) : ℝ[X] :=
  initialPolynomial p a + s ^ (p + 1) • (unitResidualPolynomial p r).comp (C s⁻¹ * X)

private theorem iterate_derivative_add (P Q : ℝ[X]) (j : ℕ) :
    derivative^[j] (P + Q) = derivative^[j] P + derivative^[j] Q := by
  simp_rw [← Module.End.pow_apply, map_add]

/-- The exact derivative of the rescaled correction, including its scaling factor. -/
theorem residualScaledPolynomial_derivative (p j : ℕ) (s : ℝ) (a : ℕ → ℝ)
    (r : Fin (p + 1) → ℝ) (t : ℝ) :
    (derivative^[j] (residualScaledPolynomial p s a r)).eval t =
      (derivative^[j] (initialPolynomial p a)).eval t +
        (s ^ (p + 1) * s⁻¹ ^ j) *
          (derivative^[j] (unitResidualPolynomial p r)).eval (s⁻¹ * t) := by
  simp only [residualScaledPolynomial, iterate_derivative_add, iterate_derivative_smul,
    iterate_derivative_comp_scale, eval_add, eval_smul, eval_comp, eval_mul, eval_C, eval_X,
    smul_eq_mul]
  ring

private theorem scale_factor {p j : ℕ} {s : ℝ} (hs : s ≠ 0) (hj : j ≤ p + 1) :
    s ^ (p + 1) * s⁻¹ ^ j = s ^ (p + 1 - j) := by
  rw [inv_pow, ← div_eq_mul_inv]
  exact (pow_sub₀ s hs hj).symm

/-- The degree bound and both endpoint jets characterize the canonical interpolant. -/
theorem endpointPolynomial_eq_of_jets {p : ℕ} {s : ℝ} (hs : s ≠ 0)
    (a b : ℕ → ℝ) {Q : ℝ[X]} (hQ : Q.degree < ((2 * p + 2 : ℕ) : WithBot ℕ))
    (ha : ∀ j ≤ p, (derivative^[j] Q).eval 0 = a j)
    (hb : ∀ j ≤ p, (derivative^[j] Q).eval s = b j) :
    Q = endpointPolynomial p s a b := by
  apply eq_interpolateJet
  · simpa only [Multiset.card_add, Multiset.card_replicate,
      show p + 1 + (p + 1) = 2 * p + 2 by omega] using hQ
  · apply isJetInterpolant_iff_coeff_taylor.mpr
    intro y hy j hj
    have hy' : y = 0 ∨ y = s := by
      rcases Multiset.mem_add.mp hy with h | h
      · exact Or.inl (Multiset.eq_of_mem_replicate h)
      · exact Or.inr (Multiset.eq_of_mem_replicate h)
    rcases hy' with rfl | rfl
    · have hj' : j ≤ p := by
        simp [Multiset.count_replicate, hs, Ne.symm hs] at hj
        omega
      rw [coeff_taylor_eq_eval_iterate_derivative_div, ha j hj']
      simp
    · have hj' : j ≤ p := by
        simp [Multiset.count_replicate, hs, Ne.symm hs] at hj
        omega
      rw [coeff_taylor_eq_eval_iterate_derivative_div, hb j hj']
      simp [hs]

/-- The residual basis construction has degree strictly below `2p+2`. -/
theorem unitResidualPolynomial_degree_lt (p : ℕ) (r : Fin (p + 1) → ℝ) :
    (unitResidualPolynomial p r).degree < ((2 * p + 2 : ℕ) : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  simp only [unitResidualPolynomial, finsetSum_coeff, coeff_smul]
  apply Finset.sum_eq_zero
  intro i _hi
  change r i • (endpointPolynomial p 1 (fun _ => 0) (fun j => if j = i.val then 1
    else 0)).coeff n = 0
  rw [coeff_eq_zero_of_degree_lt ((endpointPolynomial_degree_lt p 1
    (fun _ => 0) (fun j => if j = i.val then 1 else 0)).trans_le (by exact_mod_cast hn))]
  simp

/-- Rescaling a residual interpolant preserves the required degree bound. -/
theorem residualScaledPolynomial_natDegree_le (p : ℕ) (s : ℝ) (a : ℕ → ℝ)
    (r : Fin (p + 1) → ℝ) : (residualScaledPolynomial p s a r).natDegree ≤ 2 * p + 1 := by
  have hinit : (initialPolynomial p a).natDegree ≤ p := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact coeff_eq_zero_of_degree_lt ((initialPolynomial_degree_lt p a).trans_le (by
      exact_mod_cast hn))
  have hunit : (unitResidualPolynomial p r).natDegree ≤ 2 * p + 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact coeff_eq_zero_of_degree_lt ((unitResidualPolynomial_degree_lt p r).trans_le
      (by exact_mod_cast hn))
  apply (natDegree_add_le _ _).trans
  apply max_le
  · omega
  · apply (natDegree_smul_le _ _).trans
    apply natDegree_comp_le.trans
    have hscale : (C s⁻¹ * X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans_eq natDegree_X
    nlinarith

/-- The terminal discrepancy from the initial Taylor polynomial, normalized
by the source scale `s^(p-j+1)` for each derivative order. -/
noncomputable def endpointResidual (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) : Fin (p + 1) → ℝ :=
  fun i => (b i - (derivative^[i.val] (initialPolynomial p a)).eval s) / s ^ (p - i.val + 1)

/-- The genuine canonical endpoint interpolant equals its rescaled residual
basis construction. Both jets and the degree bound are proved before uniqueness is used. -/
theorem endpointPolynomial_eq_residualScaled {p : ℕ} {s : ℝ} (hs : s ≠ 0)
    (a b : ℕ → ℝ) :
    endpointPolynomial p s a b = residualScaledPolynomial p s a (endpointResidual p s a b) := by
  apply Eq.symm
  apply endpointPolynomial_eq_of_jets hs a b
  · apply (natDegree_le_iff_degree_le.mp (residualScaledPolynomial_natDegree_le p s a _)).trans_lt
    exact_mod_cast (show 2 * p + 1 < 2 * p + 2 by omega)
  · intro j hj
    rw [residualScaledPolynomial_derivative, initialPolynomial_zero p a hj]
    simp only [mul_zero, unitResidualPolynomial_zero p _ hj, add_zero]
  · intro j hj
    rw [residualScaledPolynomial_derivative, inv_mul_cancel₀ hs,
      unitResidualPolynomial_one p _ hj, scale_factor hs (by omega)]
    change (derivative^[j] (initialPolynomial p a)).eval s + s ^ (p + 1 - j) *
      ((b j - (derivative^[j] (initialPolynomial p a)).eval s) / s ^ (p - j + 1)) = b j
    rw [show p + 1 - j = p - j + 1 by omega]
    field_simp
    ring

/-- The source endpoint discrepancy assumption bounds every normalized residual. -/
theorem endpointResidual_abs_le {p : ℕ} {s κ : ℝ} (hs : 0 < s) (a b : ℕ → ℝ)
    (hres : ∀ j ≤ p, |b j - (derivative^[j] (initialPolynomial p a)).eval s| ≤
      κ * s ^ (p - j + 1)) (i : Fin (p + 1)) : |endpointResidual p s a b i| ≤ κ := by
  rw [endpointResidual, abs_div, abs_of_pos (pow_pos hs _)]
  exact (div_le_iff₀ (pow_pos hs _)).mpr (hres i (by omega))

private theorem inv_mul_mem_Icc {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc 0 s) :
    s⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hs.le) ht.1
  · rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hs).mpr ht.2

/-- Uniform endpoint Hermite interpolation bounds, for arbitrary order. Both
constants are chosen before the interval and all jet data. The highest derivative
is Lipschitz under normalized residual bounds, and every derivative through order
`p` is bounded when the initial jet and interval length are also bounded. -/
theorem endpointPolynomial_uniform_bounds (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L > 0, ∃ B > 0, ∀ s : ℝ, 0 < s → ∀ a b : ℕ → ℝ,
      (∀ j ≤ p, |b j - (derivative^[j] (initialPolynomial p a)).eval s| ≤
        κ * s ^ (p - j + 1)) →
      (∀ u ∈ Icc 0 s, ∀ v ∈ Icc 0 s,
        |iteratedDeriv p (fun t => (endpointPolynomial p s a b).eval t) u -
          iteratedDeriv p (fun t => (endpointPolynomial p s a b).eval t) v| ≤ L * |u - v|) ∧
      ((∀ j ≤ p, |a j| ≤ κ) → s ≤ κ → ∀ j ≤ p, ∀ t ∈ Icc 0 s,
        |iteratedDeriv j (fun z => (endpointPolynomial p s a b).eval z) t| ≤ B) := by
  obtain ⟨M,hMpos,hM⟩ := unitResidualPolynomial_uniform_bound p κ
  obtain ⟨T,hTpos,hT⟩ := initialPolynomial_uniform_bound p κ
  refine ⟨M,hMpos,T + (1 + κ) ^ (p + 1) * M,by positivity,?_⟩
  intro s hs a b hres
  let r := endpointResidual p s a b
  have hr : ∀ i, |r i| ≤ κ := endpointResidual_abs_le hs a b hres
  have heq := endpointPolynomial_eq_residualScaled (p := p) hs.ne' a b
  have hhigh : ∀ t ∈ Icc 0 s,
      |(derivative^[p + 1] (endpointPolynomial p s a b)).eval t| ≤ M := by
    intro t ht
    rw [heq, residualScaledPolynomial_derivative,
      iterate_derivative_eq_zero_of_degree_lt (initialPolynomial_degree_lt p a),
      eval_zero, zero_add, scale_factor hs.ne' le_rfl]
    simpa only [Nat.sub_self, pow_zero, one_mul] using
      hM r hr (p + 1) le_rfl (s⁻¹ * t) (inv_mul_mem_Icc hs ht)
  constructor
  · intro u hu v hv
    rw [Polynomial.iteratedDeriv_eval]
    apply Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (derivative^[p] (endpointPolynomial p s a b)).differentiable t)
      (fun t ht => ?_) (convex_Icc 0 s) hv hu
    rw [((derivative^[p] (endpointPolynomial p s a b)).hasDerivAt t).deriv]
    simpa only [Real.norm_eq_abs, Function.iterate_succ_apply'] using hhigh t ht
  · intro ha hsk j hj t ht
    simp only [Polynomial.iteratedDeriv_eval]
    rw [heq, residualScaledPolynomial_derivative,
      scale_factor hs.ne' (by omega)]
    have hinit := hT a ha j hj t ⟨ht.1, ht.2.trans hsk⟩
    have hunit := hM r hr j (by omega) (s⁻¹ * t) (inv_mul_mem_Icc hs ht)
    have hfac : 0 ≤ s ^ (p + 1 - j) := pow_nonneg hs.le _
    have hfac_le : s ^ (p + 1 - j) ≤ (1 + κ) ^ (p + 1) :=
      (pow_le_pow_left₀ hs.le (by linarith : s ≤ 1 + κ) _).trans
        (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + κ) (by omega))
    calc
      _ ≤ |(derivative^[j] (initialPolynomial p a)).eval t| +
          |s ^ (p + 1 - j) * (derivative^[j] (unitResidualPolynomial p r)).eval (s⁻¹
            * t)| := abs_add_le _ _
      _ = |(derivative^[j] (initialPolynomial p a)).eval t| +
          s ^ (p + 1 - j) * |(derivative^[j] (unitResidualPolynomial p r)).eval (s⁻¹ * t)| := by
        rw [abs_mul, abs_of_nonneg hfac]
      _ ≤ _ := add_le_add hinit
        (mul_le_mul hfac_le hunit (abs_nonneg _) (by positivity))

/-- The initial polynomial evaluates to the factorial-normalized Taylor sum
specified by the initial endpoint jet. -/
theorem initialPolynomial_eval (p : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (initialPolynomial p a).eval t =
      ∑ j ∈ Finset.range (p + 1), a j * t ^ j / j.factorial := by
  simp only [initialPolynomial, jetPoly, C_0, sub_zero, eval_finsetSum, eval_mul,
    eval_C, eval_pow, eval_X, div_mul_eq_mul_div]

/-- Degree at most `2p+1`, including degenerate interpolation data. -/
theorem endpointPolynomial_natDegree_le (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) :
    (endpointPolynomial p s a b).natDegree ≤ 2 * p + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  exact coeff_eq_zero_of_degree_lt
    ((endpointPolynomial_degree_lt p s a b).trans_le (by exact_mod_cast hn))

end Hermite
