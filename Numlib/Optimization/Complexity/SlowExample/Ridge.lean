import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Optimality.Approximate

/-!
# Ridge functions

A function `g : ℝ → ℝ` of one variable lifts to any real inner product space `E` as the **ridge
function** `x ↦ g ⟪e, x⟫` along a direction `e : E`. The one-dimensional slow-convergence examples
of [cartis2022evaluation] (footnote 10) are ridge functions, and every quantity their analysis
needs is a one-dimensional quantity along `e`: derivatives, gradient, Hessian, least curvature and
Taylor polynomials. This file also records the restriction of Taylor data to a line.

## Main definitions and results

* `Optimization.ridge g e x = g ⟪e, x⟫`.
* `Optimization.iteratedFDeriv_ridge_apply`, `Optimization.norm_iteratedFDeriv_ridge`,
  `Optimization.iteratedFDerivLipschitzOn_ridge`: derivatives, their norms and Lipschitz
  constants.
* `Optimization.gradient_ridge`, `Optimization.hessianOperator_ridge`,
  `Optimization.minCurvature_iteratedFDeriv_ridge`: gradient, Hessian and least curvature.
* `Optimization.taylorPolynomial_ridge`: Taylor polynomials.
* `Optimization.iteratedFDeriv_apply_const_eq_line`, `Optimization.taylorDecrement_eq_of_line`:
  iterated derivatives and Taylor decrements along a line are those of the restriction.
* `Optimization.hessianOperator_ridge_single`: the Hessian of a ridge function along the
  coordinate direction of `ℝ¹`.
-/

open Set Finset
open scoped Nat RealInnerProductSpace

namespace Optimization

/-! ### Ridge functions -/

section Ridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {g : ℝ → ℝ} {e : E}

/-- The **ridge function** `x ↦ g ⟪e, x⟫` lifting a function of one variable to an inner product
space along the direction `e`. -/
def ridge (g : ℝ → ℝ) (e : E) (x : E) : ℝ :=
  g ⟪e, x⟫

theorem ridge_apply (g : ℝ → ℝ) (e x : E) : ridge g e x = g ⟪e, x⟫ :=
  rfl

theorem ridge_eq_comp (g : ℝ → ℝ) (e : E) : ridge g e = g ∘ innerSL ℝ e :=
  rfl

theorem contDiff_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) : ContDiff ℝ n (ridge g e) :=
  hg.comp (innerSL ℝ e).contDiff

/-- The derivatives of a ridge function: `D^j (g ∘ ⟪e, ·⟫)(x)[m] = g^{(j)}(⟪e,x⟫) ∏ ⟪e, m i⟫`. -/
theorem iteratedFDeriv_ridge_apply {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (x : E) (m : Fin j → E) :
    iteratedFDeriv ℝ j (ridge g e) x m = (∏ i, ⟪e, m i⟫) * iteratedDeriv j g ⟪e, x⟫ := by
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  simp

/-- The derivatives of a ridge function along a direction `d`. -/
theorem iteratedFDeriv_ridge_apply_diag {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (x d : E) :
    iteratedFDeriv ℝ j (ridge g e) x (fun _ => d) = iteratedDeriv j g ⟪e, x⟫ * ⟪e, d⟫ ^ j := by
  rw [iteratedFDeriv_ridge_apply hg hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_comm]

theorem norm_iteratedFDeriv_ridge_le {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ ≤ 1) (x : E) :
    ‖iteratedFDeriv ℝ j (ridge g e) x‖ ≤ |iteratedDeriv j g ⟪e, x⟫| := by
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => by rwa [innerSL_apply_norm]

/-- For a unit vector `e`, the norm of `D^j (ridge g e)(x)` is `|g^{(j)}(⟪e, x⟫)|`. -/
theorem norm_iteratedFDeriv_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ = 1) (x : E) :
    ‖iteratedFDeriv ℝ j (ridge g e) x‖ = |iteratedDeriv j g ⟪e, x⟫| := by
  refine le_antisymm (norm_iteratedFDeriv_ridge_le hg hj he.le x) ?_
  have h := (iteratedFDeriv ℝ j (ridge g e) x).le_opNorm fun _ => e
  rw [iteratedFDeriv_ridge_apply_diag hg hj, real_inner_self_eq_norm_sq, he] at h
  simpa [he] using h

/-- Lipschitz constants of the derivatives transfer to ridge functions along `‖e‖ ≤ 1`. -/
theorem iteratedFDerivLipschitzOn_ridge {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) {j : ℕ}
    (hj : (j : WithTop ℕ∞) ≤ n) (he : ‖e‖ ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ s t, |iteratedDeriv j g s - iteratedDeriv j g t| ≤ L * |s - t|) :
    IteratedFDerivLipschitzOn (ridge g e) j L univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro x _ y _
  rw [ridge_eq_comp, (innerSL ℝ e).iteratedFDeriv_comp_right hg x hj,
    (innerSL ℝ e).iteratedFDeriv_comp_right hg y hj]
  have hsub : (iteratedFDeriv ℝ j g ⟪e, x⟫).compContinuousLinearMap (fun _ => innerSL ℝ e) -
      (iteratedFDeriv ℝ j g ⟪e, y⟫).compContinuousLinearMap (fun _ => innerSL ℝ e) =
      (iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫).compContinuousLinearMap
        (fun _ => innerSL ℝ e) := by
    ext m
    simp
  rw [innerSL_apply_apply, innerSL_apply_apply, hsub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin j, ‖innerSL ℝ e‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => by rwa [innerSL_apply_norm]
  have hd : ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ =
      |iteratedDeriv j g ⟪e, x⟫ - iteratedDeriv j g ⟪e, y⟫| := by
    rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
      Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
  have hxy : |⟪e, x⟫ - ⟪e, y⟫| ≤ ‖x - y‖ := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) he)
  calc ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ * ∏ _i : Fin j, ‖innerSL ℝ e‖
      ≤ ‖iteratedFDeriv ℝ j g ⟪e, x⟫ - iteratedFDeriv ℝ j g ⟪e, y⟫‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hp
    _ ≤ L * ‖x - y‖ := by
        rw [hd]
        exact (hL _ _).trans (mul_le_mul_of_nonneg_left hxy hL0)

/-- The smallest curvature of a ridge function along a unit vector `e`: it is at least
`min 0 (g''(⟪e, x⟫))`, and at most `g''(⟪e, x⟫)` (direction `e`). -/
theorem min_le_minCurvature_iteratedFDeriv_ridge (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1) (x : E) :
    min 0 (iteratedDeriv 2 g ⟪e, x⟫) ≤ minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) ∧
      minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) ≤ iteratedDeriv 2 g ⟪e, x⟫ := by
  have hdiag : ∀ d : E, iteratedFDeriv ℝ 2 (ridge g e) x (fun _ => d) =
      iteratedDeriv 2 g ⟪e, x⟫ * ⟪e, d⟫ ^ 2 := fun d =>
    iteratedFDeriv_ridge_apply_diag hg (by norm_num) x d
  have hE : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  refine ⟨le_minCurvature_iff.2 fun d => ?_, ?_⟩
  · rw [hdiag]
    have h1 : ⟪e, d⟫ ^ 2 ≤ ‖d‖ ^ 2 := by
      have := abs_real_inner_le_norm e d
      rw [he, one_mul] at this
      nlinarith [abs_nonneg ⟪e, d⟫, sq_abs ⟪e, d⟫]
    rcases le_total 0 (iteratedDeriv 2 g ⟪e, x⟫) with h | h
    · rw [min_eq_left h, zero_mul]
      positivity
    · rw [min_eq_right h]
      nlinarith [sq_nonneg ⟪e, d⟫]
  · have := minCurvature_le_apply (iteratedFDeriv ℝ 2 (ridge g e) x) he
    rwa [hdiag, real_inner_self_eq_norm_sq, he, one_pow, one_pow, mul_one] at this

/-- **Smallest curvature of a ridge function** when there is a unit direction orthogonal to `e`
(e.g. `dim E ≥ 2`): `λ_min[∇² (ridge g e)(x)] = min 0 (g''(⟪e, x⟫))`. -/
theorem minCurvature_iteratedFDeriv_ridge (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1)
    (hperp : ∃ d : E, ‖d‖ = 1 ∧ ⟪e, d⟫ = 0) (x : E) :
    minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) = min 0 (iteratedDeriv 2 g ⟪e, x⟫) := by
  obtain ⟨h1, h2⟩ := min_le_minCurvature_iteratedFDeriv_ridge hg he x
  obtain ⟨d, hd, hed⟩ := hperp
  have h3 := minCurvature_le_apply (iteratedFDeriv ℝ 2 (ridge g e) x) hd
  rw [iteratedFDeriv_ridge_apply_diag hg (by norm_num), hed] at h3
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h3
  exact le_antisymm (le_min h3 h2) h1

/-- In dimension one (every vector is a multiple of the unit vector `e`), the smallest curvature
of a ridge function is `g''(⟪e, x⟫)`. -/
theorem minCurvature_iteratedFDeriv_ridge_of_forall (hg : ContDiff ℝ 2 g) (he : ‖e‖ = 1)
    (hspan : ∀ d : E, ⟪e, d⟫ ^ 2 = ‖d‖ ^ 2) (x : E) :
    minCurvature (iteratedFDeriv ℝ 2 (ridge g e) x) = iteratedDeriv 2 g ⟪e, x⟫ := by
  have hE : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  refine le_antisymm (min_le_minCurvature_iteratedFDeriv_ridge hg he x).2
    (le_minCurvature_iff.2 fun d => ?_)
  rw [iteratedFDeriv_ridge_apply_diag hg (by norm_num), hspan]

/-- The gradient of a ridge function: `∇ (ridge g e)(x) = g'(⟪e, x⟫) e`. -/
theorem gradient_ridge [CompleteSpace E] (hg : Differentiable ℝ g) (x : E) :
    gradient (ridge g e) x = deriv g ⟪e, x⟫ • e := by
  have h : HasFDerivAt (ridge g e) (deriv g ⟪e, x⟫ • innerSL ℝ e) x := by
    have := (hg ⟪e, x⟫).hasDerivAt.comp_hasFDerivAt x (innerSL ℝ e).hasFDerivAt
    simpa [ridge_eq_comp] using this
  have h' : HasGradientAt (ridge g e) (deriv g ⟪e, x⟫ • e) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  exact h'.gradient

/-- The Hessian of a ridge function: `∇²(g ∘ ⟪e, ·⟫)(x) u = g''(⟪e, x⟫) ⟪e, u⟫ e`. -/
theorem hessianOperator_ridge [CompleteSpace E] (hg : ContDiff ℝ 2 g) (x u : E) :
    hessianOperator (ridge g e) x u = (iteratedDeriv 2 g ⟪e, x⟫ * ⟪e, u⟫) • e := by
  refine ext_inner_left ℝ fun w => ?_
  rw [inner_hessianOperator_apply (contDiff_ridge hg).contDiffAt,
    iteratedFDeriv_ridge_apply hg (by norm_num), Fin.prod_univ_two, inner_smul_right,
    real_inner_comm e w]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end Ridge

/-! ### Restriction to a line -/

section Line

/-- **Iterated derivatives along a line**: for `F` of class `C^n` and `i ≤ n`, `∇^i F(s)[d]^i` is
the `i`-th derivative of `τ ↦ F(s + τ d)` at `0`. -/
theorem iteratedFDeriv_apply_const_eq_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} {n : ℕ} (hF : ContDiff ℝ n F) {i : ℕ} (hi : i ≤ n) (s d : E) :
    iteratedFDeriv ℝ i F s (fun _ => d) = iteratedDeriv i (fun τ : ℝ => F (s + τ • d)) 0 := by
  have hcomp : (fun τ : ℝ => F (s + τ • d)) =
      (fun v => F (s + v)) ∘ ContinuousLinearMap.toSpanSingleton ℝ d := by
    funext τ; simp [ContinuousLinearMap.toSpanSingleton_apply]
  have hg : ContDiff ℝ n (fun v => F (s + v)) := hF.comp (contDiff_const.add contDiff_id)
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    (ContinuousLinearMap.toSpanSingleton ℝ d).iteratedFDeriv_comp_right hg 0
      (by exact_mod_cast hi),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- **Taylor decrements along a line**: if `F(s + τ d) = F₁(t + τ a)` for all `τ`, then the
Taylor decrements of `F` at `s` along `d` are those of `F₁` at `t` along `a`. -/
theorem taylorDecrement_eq_of_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → ℝ} {F₁ : ℝ → ℝ} {n : ℕ} (hF : ContDiff ℝ n F)
    (hF₁ : ContDiff ℝ n F₁) {s d : E} {t a : ℝ} (hline : ∀ τ : ℝ, F (s + τ • d) = F₁ (t + τ * a))
    {ℓ : ℕ} (hℓ : ℓ ≤ n) :
    (ftaylorSeries ℝ F s).taylorDecrement ℓ d = (ftaylorSeries ℝ F₁ t).taylorDecrement ℓ a := by
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := (Finset.mem_Icc.1 hi).2.trans hℓ
  change (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i F s (fun _ => d) =
    (i ! : ℝ)⁻¹ * iteratedFDeriv ℝ i F₁ t (fun _ => a)
  rw [iteratedFDeriv_apply_const_eq_line hF hin, iteratedFDeriv_apply_const_eq_line hF₁ hin]
  congr 2
  funext τ
  rw [hline, smul_eq_mul]

end Line

section RidgeTaylor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Taylor polynomial of a ridge function:
`T_p(x, s) = ∑_{i ≤ p} G^{(i)}(⟪e, x⟫) ⟪e, s⟫^i / i!`. -/
theorem taylorPolynomial_ridge {G : ℝ → ℝ} {p : ℕ} (hG : ContDiff ℝ p G) (e x s : E) :
    taylorPolynomial (ridge G e) p x s =
      ∑ i ∈ range (p + 1), (i.factorial : ℝ)⁻¹ * (iteratedDeriv i G ⟪e, x⟫ * ⟪e, s⟫ ^ i) := by
  rw [taylorPolynomial_apply]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [smul_eq_mul, iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast hi')]

end RidgeTaylor

/-- The Hessian of a ridge function along the coordinate direction of `ℝ¹` acts as multiplication
by `g''`. -/
theorem hessianOperator_ridge_single {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (x u : EuclideanSpace ℝ (Fin 1)) :
    hessianOperator (ridge g (EuclideanSpace.single 0 1)) x u =
      iteratedDeriv 2 g ⟪EuclideanSpace.single 0 1, x⟫ • u := by
  rw [hessianOperator_ridge hg, mul_smul, ← EuclideanSpace.eq_inner_single_smul]

end Optimization
