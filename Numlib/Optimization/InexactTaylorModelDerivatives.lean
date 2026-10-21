import Numlib.Optimization.InexactTaylorModels
import Numlib.Optimization.TaylorModelDerivatives
import Numlib.Optimization.HigherOrderRegularizationModelBounds

/-!
# Shifted derivatives of finite coefficient polynomials

The supplied tensors need not be derivatives of any function or symmetric. Their diagonal
polynomial has genuine derivatives, controlled by the original tensor norms. The bounds
retain the displacement powers needed to compare shifted approximate and exact jets.
-/

noncomputable section
open scoped Nat ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivatives of a diagonal multilinear polynomial obey the falling-factorial norm
bound without any symmetry hypothesis on its coefficient. -/
theorem ContinuousMultilinearMap.norm_iteratedFDeriv_diag_le {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (j : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ j (fun z => A (fun _ => z)) s‖ ≤
      (Nat.descFactorial k j : ℝ) * ‖A‖ * ‖s‖ ^ (k - j) := by
  let Δ : E →L[ℝ] (Fin k → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E)
  have hΔ : ‖Δ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖(fun _ : Fin k => x)‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using
      (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun _ : Fin k => le_rfl)
  change ‖iteratedFDeriv ℝ j (A ∘ Δ) s‖ ≤ _
  rw [Δ.iteratedFDeriv_comp_right A.contDiff s (le_refl (j : ℕ∞ω))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j A (Δ s)‖ * ∏ _ : Fin j, ‖Δ‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j A (Δ s)‖ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hΔ)
    _ ≤ (Nat.descFactorial k j : ℝ) * ‖A‖ * ‖Δ s‖ ^ (k - j) := by
      simpa using A.norm_iteratedFDeriv_le j (Δ s)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg s)).mpr (fun _ => le_rfl)

namespace Optimization.InexactTaylorModels

/-- A finite coefficient polynomial is smooth to every order, independently of its tensors. -/
theorem contDiff_polynomial (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (n : ℕ∞ω) : ContDiff ℝ n (polynomial c A p) := by
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  exact ((A i).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)).div_const _

/-- Positive-order derivatives ignore the independent scalar constant and distribute over
all actual coefficient polynomials. -/
theorem iteratedFDeriv_polynomial {j : ℕ} (hj : 1 ≤ j) (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (s : E) :
    iteratedFDeriv ℝ j (polynomial c A p) s =
      ∑ i ∈ Finset.Icc 1 p, ((i ! : ℝ)⁻¹) •
        iteratedFDeriv ℝ j (fun z => A i (fun _ => z)) s := by
  have hc (i : ℕ) : ContDiff ℝ j (fun z : E => A i (fun _ => z)) :=
    (A i).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)
  have he : polynomial c A p = (fun _ : E => c) +
      (fun z => ∑ i ∈ Finset.Icc 1 p, (i ! : ℝ)⁻¹ • A i (fun _ => z)) := by
    funext z
    simp [polynomial, div_eq_inv_mul, smul_eq_mul]
  rw [he, iteratedFDeriv_add_apply contDiff_const.contDiffAt
    ((ContDiff.sum fun i _ => (hc i).const_smul _).contDiffAt),
    iteratedFDeriv_const_of_ne (by omega : j ≠ 0), Pi.zero_apply, zero_add,
    iteratedFDeriv_fun_sum_apply (fun i _ => ((hc i).const_smul _).contDiffAt)]
  exact Finset.sum_congr rfl fun i _ => iteratedFDeriv_const_smul_apply' (hc i).contDiffAt

/-- Every shifted derivative of a finite polynomial is bounded by its factorial-normalized
coefficient tail. Arbitrary tensors are allowed, and no smooth surrogate is postulated. -/
theorem norm_iteratedFDeriv_polynomial_le {j : ℕ} (hj : 1 ≤ j) (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (s : E) :
    ‖iteratedFDeriv ℝ j (polynomial c A p) s‖ ≤
      ∑ i ∈ Finset.Icc 1 p,
        if j ≤ i then ‖A i‖ * ‖s‖ ^ (i - j) / ((i - j)! : ℝ) else 0 := by
  rw [iteratedFDeriv_polynomial hj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (i ! : ℝ))]
  have hb := mul_le_mul_of_nonneg_left ((A i).norm_iteratedFDeriv_diag_le j s)
    (by positivity : (0 : ℝ) ≤ (i ! : ℝ)⁻¹)
  by_cases hji : j ≤ i
  · rw [ite_eq_left hji]
    convert hb using 1
    have hf : ((i - j)! : ℝ) * (Nat.descFactorial i j : ℝ) = (i ! : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hji
    have hi : (i ! : ℝ) ≠ 0 := by positivity
    have hij : ((i - j)! : ℝ) ≠ 0 := by positivity
    field_simp
    rw [← hf]
    ring
  · rw [ite_eq_right hji]
    have hz : Nat.descFactorial i j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simpa [hz] using hb


/-- All derivatives above the degree of a supplied polynomial vanish identically. -/
theorem iteratedFDeriv_polynomial_eq_zero_of_lt {j p : ℕ} (hpj : p < j) (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (s : E) :
    iteratedFDeriv ℝ j (polynomial c A p) s = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply (norm_iteratedFDeriv_polynomial_le (by omega) c A p s).trans
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro i hi
  simp only [ite_eq_right (show ¬j ≤ i by have := Finset.mem_Icc.mp hi; omega)]

/-- The highest derivative of a supplied polynomial is constant, including for arbitrary
nonsymmetric coefficient tensors. -/
theorem iteratedFDeriv_polynomial_top_eq (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (s t : E) :
    iteratedFDeriv ℝ p (polynomial c A p) s = iteratedFDeriv ℝ p (polynomial c A p) t := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ)
  · intro z
    exact (contDiff_polynomial c A p (p + 1)).contDiffAt.differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self p)
  · intro z
    apply norm_eq_zero.mp
    have hz := congrArg norm (iteratedFDeriv_polynomial_eq_zero_of_lt
      (Nat.lt_succ_self p) c A z)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      LinearIsometryEquiv.norm_map, norm_zero] using hz

/-- Subtracting actual polynomials subtracts their independent constants and every tensor. -/
theorem polynomial_sub (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) : polynomial c A p - polynomial d B p =
      polynomial (c - d) (fun i => A i - B i) p := by
  funext s
  simp only [Pi.sub_apply, polynomial, sub_apply,
    sub_div, Finset.sum_sub_distrib]
  ring

/-- Errors in arbitrary supplied coefficients control the genuine shifted derivative
error, with all higher supplied orders contributing to each lower derivative. -/
theorem iteratedFDeriv_polynomial_error_le {j : ℕ} (hj : 1 ≤ j) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (p : ℕ) (s : E) (e : ℕ → ℝ)
    (herr : ∀ i ∈ Finset.Icc 1 p, ‖A i - B i‖ ≤ e i) :
    ‖iteratedFDeriv ℝ j (polynomial c A p) s -
        iteratedFDeriv ℝ j (polynomial d B p) s‖ ≤
      ∑ i ∈ Finset.Icc 1 p,
        if j ≤ i then e i * ‖s‖ ^ (i - j) / ((i - j)! : ℝ) else 0 := by
  rw [← iteratedFDeriv_sub_apply (contDiff_polynomial c A p j).contDiffAt
    (contDiff_polynomial d B p j).contDiffAt, polynomial_sub]
  apply (norm_iteratedFDeriv_polynomial_le hj (c - d) (fun i => A i - B i) p s).trans
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (herr i hi) (pow_nonneg (norm_nonneg s) _)) (by positivity)
  · exact le_rfl


/-- The reciprocal-factorial tail beginning at a positive derivative order has total
weight at most three, uniformly in the finite polynomial degree. -/
theorem factorial_tail_sum_le_three {j p : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {M : ℝ} (hM : 0 ≤ M) :
    (∑ i ∈ Finset.Icc 1 p, if j ≤ i then M / ((i - j)! : ℝ) else 0) ≤ 3 * M := by
  have heq : (∑ i ∈ Finset.Icc 1 p, if j ≤ i then M / ((i - j)! : ℝ) else 0) =
      ∑ i ∈ Finset.range (p + 1), if j ≤ i then M / ((i - j)! : ℝ) else 0 := by
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hi; omega)
    · intro i hi hn
      have hi0 : i = 0 := by
        have := Finset.mem_range.mp hi
        have hh : ¬(1 ≤ i ∧ i ≤ p) := by simpa only [Finset.mem_Icc] using hn
        omega
      subst i
      simp [show ¬j ≤ 0 by omega]
  rw [heq]
  have hr : p + 1 = j + (p + 1 - j) := by omega
  rw [hr, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range j, if j ≤ i then M / ((i - j)! : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [show ¬j ≤ i by have := Finset.mem_range.mp hi; omega]
  rw [hz, zero_add]
  simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
  rw [show (∑ i ∈ Finset.range (p + 1 - j), M / (i ! : ℝ)) =
    M * ∑ i ∈ Finset.range (p + 1 - j), 1 / (i ! : ℝ) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
  have hb := mul_le_mul_of_nonneg_left (Real.sum_inv_factorial_lt_three (p + 1 - j)).le hM
  nlinarith only [hb]

/-- Uniform bounds on supplied tensors control all actual positive-order derivatives of
their finite polynomial on the unit ball. -/
theorem norm_iteratedFDeriv_polynomial_le_three {j p : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    (c : ℝ) (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hA : ∀ i ∈ Finset.Icc j p, ‖A i‖ ≤ L)
    (s : E) (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (polynomial c A p) s‖ ≤ 3 * L := by
  apply (norm_iteratedFDeriv_polynomial_le hj c A p s).trans
  apply le_trans _ (factorial_tail_sum_le_three hj hjp hL)
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with hji
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact (mul_le_mul_of_nonneg_right
      (hA i (Finset.mem_Icc.mpr ⟨hji, (Finset.mem_Icc.mp hi).2⟩))
      (pow_nonneg (norm_nonneg s) _)).trans
        (mul_le_of_le_one_right hL (pow_le_one₀ (norm_nonneg s) hs))
  · exact le_rfl

/-- Step-dependent coefficient errors retain their full step power after any positive
number of genuine differentiations at that step. All supplied orders through `p` enter
the bound, even when the derivative order is smaller. Zero steps require no exception. -/
theorem iteratedFDeriv_polynomial_error_le_step_power {j p : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ)
    (s : E) {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (herr : ∀ i ∈ Finset.Icc 1 p,
      ‖A i - B i‖ ≤ K * κ * ‖s‖ ^ (p - i + 1)) :
    ‖iteratedFDeriv ℝ j (polynomial c A p) s -
        iteratedFDeriv ℝ j (polynomial d B p) s‖ ≤
      3 * K * κ * ‖s‖ ^ (p - j + 1) := by
  have hb := iteratedFDeriv_polynomial_error_le hj c d A B p s
    (fun i => K * κ * ‖s‖ ^ (p - i + 1)) herr
  have he : (∑ i ∈ Finset.Icc 1 p,
      if j ≤ i then K * κ * ‖s‖ ^ (p - i + 1) * ‖s‖ ^ (i - j) /
        ((i - j)! : ℝ) else 0) =
      ∑ i ∈ Finset.Icc 1 p,
        if j ≤ i then (K * κ * ‖s‖ ^ (p - j + 1)) / ((i - j)! : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hji
    · have hip := (Finset.mem_Icc.mp hi).2
      rw [mul_assoc, ← pow_add, show p - i + 1 + (i - j) = p - j + 1 by omega]
    · rfl
  rw [he] at hb
  have ht := factorial_tail_sum_le_three hj hjp
    (M := K * κ * ‖s‖ ^ (p - j + 1)) (by positivity)
  exact hb.trans (by nlinarith only [ht])


section Regularized
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Genuine derivatives of a regularized supplied polynomial split into its polynomial
and radial terms, through the polynomial degree. -/
theorem iteratedFDeriv_regularizedPolynomial_of_le {j p : ℕ} (hjp : j ≤ p)
    (c : ℝ) (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) :
    iteratedFDeriv ℝ j (regularizedPolynomial c A p σ) s =
      iteratedFDeriv ℝ j (polynomial c A p) s +
        (σ / ((p + 1)! : ℝ)) • iteratedFDeriv ℝ j (fun z : F => ‖z‖ ^ (p + 1)) s := by
  have hn : ContDiff ℝ j (fun z : F => ‖z‖ ^ (p + 1)) := by
    simpa only [Real.rpow_natCast] using contDiff_norm_rpow_of_lt (E := F)
      (n := j) (r := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega : j < p + 1))
  have he : regularizedPolynomial c A p σ = polynomial c A p +
      (fun z : F => (σ / ((p + 1)! : ℝ)) • ‖z‖ ^ (p + 1)) := by
    funext z
    simp only [regularizedPolynomial, Pi.add_apply, smul_eq_mul]
    ring
  rw [he, iteratedFDeriv_add_apply (contDiff_polynomial c A p j).contDiffAt
    (hn.const_smul _).contDiffAt, iteratedFDeriv_const_smul_apply' hn.contDiffAt]

/-- A common radial regularizer cancels exactly from every derivative difference through
the polynomial degree. The remaining error comes from the supplied coefficients alone. -/
theorem iteratedFDeriv_regularizedPolynomial_sub {j p : ℕ} (hjp : j ≤ p)
    (c d : ℝ) (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) :
    iteratedFDeriv ℝ j (regularizedPolynomial c A p σ) s -
        iteratedFDeriv ℝ j (regularizedPolynomial d B p σ) s =
      iteratedFDeriv ℝ j (polynomial c A p) s -
        iteratedFDeriv ℝ j (polynomial d B p) s := by
  rw [iteratedFDeriv_regularizedPolynomial_of_le hjp,
    iteratedFDeriv_regularizedPolynomial_of_le hjp, add_sub_add_right_eq_sub]

/-- All supplied tensor errors bound the genuine shifted regularized-model jets, with
the full step power. This requires errors at every order through the polynomial degree. -/
theorem iteratedFDeriv_regularizedPolynomial_error_le_step_power {j p : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) {K κ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (herr : ∀ i ∈ Finset.Icc 1 p,
      ‖A i - B i‖ ≤ K * κ * ‖s‖ ^ (p - i + 1)) :
    ‖iteratedFDeriv ℝ j (regularizedPolynomial c A p σ) s -
        iteratedFDeriv ℝ j (regularizedPolynomial d B p σ) s‖ ≤
      3 * K * κ * ‖s‖ ^ (p - j + 1) := by
  rw [iteratedFDeriv_regularizedPolynomial_sub hjp]
  exact iteratedFDeriv_polynomial_error_le_step_power hj hjp c d A B s hK hκ herr

/-- A uniform error in every supplied coefficient bounds each genuine shifted model jet
on the unit ball. The common regularizer contributes no error. -/
theorem iteratedFDeriv_regularizedPolynomial_error_le_uniform {j p : ℕ}
    (hj : 1 ≤ j) (hjp : j ≤ p) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) {L : ℝ} (hL : 0 ≤ L) (hs : ‖s‖ ≤ 1)
    (herr : ∀ i ∈ Finset.Icc 1 p, ‖A i - B i‖ ≤ L) :
    ‖iteratedFDeriv ℝ j (regularizedPolynomial c A p σ) s -
        iteratedFDeriv ℝ j (regularizedPolynomial d B p σ) s‖ ≤ 3 * L := by
  rw [iteratedFDeriv_regularizedPolynomial_sub hjp,
    ← iteratedFDeriv_sub_apply (contDiff_polynomial c A p j).contDiffAt
      (contDiff_polynomial d B p j).contDiffAt, polynomial_sub]
  exact norm_iteratedFDeriv_polynomial_le_three hj hjp (c - d) (fun i => A i - B i)
    hL (fun i hi => herr i (Finset.mem_Icc.mpr
      ⟨hj.trans (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2⟩)) s hs

/-- Step-dependent errors in every supplied coefficient control the actual compact Taylor
gaps of regularized models at a shifted point. Both gaps use their genuine derivatives. -/
theorem regularizedPolynomial_gap_error_le_step_power {j p : ℕ}
    (hjp : j ≤ p) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) {K κ δ : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (herr : ∀ i ∈ Finset.Icc 1 p,
      ‖A i - B i‖ ≤ K * κ * ‖s‖ ^ (p - i + 1)) :
    |TaylorCriticality.gapOn
        (TaylorCriticality.taylorDecrement (regularizedPolynomial c A p σ) j s)
        (Metric.closedBall 0 δ) -
      TaylorCriticality.gapOn
        (TaylorCriticality.taylorDecrement (regularizedPolynomial d B p σ) j s)
        (Metric.closedBall 0 δ)| ≤
      3 * K * κ * ∑ l ∈ Finset.Icc 1 j,
        δ ^ l * ‖s‖ ^ (p - l + 1) / (l ! : ℝ) := by
  have he (g : F → ℝ) : decrement (fun l => iteratedFDeriv ℝ l g s) j =
      TaylorCriticality.taylorDecrement g j s := funext (decrement_iteratedFDeriv g s j)
  have hb := gap_error_le
    (fun l => iteratedFDeriv ℝ l (regularizedPolynomial c A p σ) s)
    (fun l => iteratedFDeriv ℝ l (regularizedPolynomial d B p σ) s)
    (fun l => 3 * K * κ * ‖s‖ ^ (p - l + 1)) (q := j)
    (isCompact_closedBall (0 : F) δ) ⟨0, by simpa using hδ⟩ hδ (Set.Subset.refl _)
    (fun l hl => iteratedFDeriv_regularizedPolynomial_error_le_step_power
      (Finset.mem_Icc.mp hl).1 ((Finset.mem_Icc.mp hl).2.trans hjp) c d A B σ s hK hκ herr)
  rw [he, he] at hb
  convert hb using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Uniform supplied coefficient errors bound the genuine shifted compact gaps on unit
balls by six times the error, independently of the polynomial and criticality degrees. -/
theorem regularizedPolynomial_gap_error_le_uniform {j p : ℕ} (hjp : j ≤ p) (c d : ℝ)
    (A B : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => F) ℝ)
    (σ : ℝ) (s : F) {L δ : ℝ} (hL : 0 ≤ L) (hs : ‖s‖ ≤ 1)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (herr : ∀ i ∈ Finset.Icc 1 p, ‖A i - B i‖ ≤ L) :
    |TaylorCriticality.gapOn
        (TaylorCriticality.taylorDecrement (regularizedPolynomial c A p σ) j s)
        (Metric.closedBall 0 δ) -
      TaylorCriticality.gapOn
        (TaylorCriticality.taylorDecrement (regularizedPolynomial d B p σ) j s)
        (Metric.closedBall 0 δ)| ≤ 6 * L := by
  have he (g : F → ℝ) : decrement (fun l => iteratedFDeriv ℝ l g s) j =
      TaylorCriticality.taylorDecrement g j s := funext (decrement_iteratedFDeriv g s j)
  have hb := gap_error_le
    (fun l => iteratedFDeriv ℝ l (regularizedPolynomial c A p σ) s)
    (fun l => iteratedFDeriv ℝ l (regularizedPolynomial d B p σ) s)
    (fun _ => 3 * L) (q := j)
    (isCompact_closedBall (0 : F) δ) ⟨0, by simpa using hδ.1⟩ hδ.1 (Set.Subset.refl _)
    (fun l hl => iteratedFDeriv_regularizedPolynomial_error_le_uniform
      (Finset.mem_Icc.mp hl).1 ((Finset.mem_Icc.mp hl).2.trans hjp) c d A B σ s hL hs herr)
  rw [he, he] at hb
  exact hb.trans (by
    have ht := error_sum_le (q := j) hδ (by positivity : 0 ≤ 3 * L) (fun _ _ => le_rfl)
    nlinarith only [ht])

end Regularized
end Optimization.InexactTaylorModels
