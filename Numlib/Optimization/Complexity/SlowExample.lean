import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Analysis.InnerProductSpace.MinCurvature
import Numlib.Approximation.HermiteSpline

/-!
# Slow-convergence examples

The sharpness ("slow convergence") constructions of [cartis2022evaluation] Chapters 2 and 3:
values and derivatives prescribed at an increasing sequence of points on the line are interpolated
by a function whose derivatives are bounded and Lipschitz with constants **independent of the
tolerance `ε`** (Hermite interpolation, `Hermite.exists_contDiff_interpolating_jets_bounded`), and
then lifted to any real inner product space as a ridge function `x ↦ g ⟪e, x⟫`.

Each data family is parametrized by a sequence of step factors `θ k ∈ [a, b]`, and its constants
depend only on `a` and `b`. Thus a single lemma serves every method whose steps on the data are
`θ_k` times a reference step, whatever factors the method picks.

## Main definitions and results

* `Optimization.ridge g e x = g ⟪e, x⟫`, with its smoothness, derivatives, gradient, derivative
  norms and Lipschitz constants (`Optimization.iteratedFDeriv_ridge_apply_diag`,
  `Optimization.norm_iteratedFDeriv_ridge`, `Optimization.iteratedFDerivLipschitzOn_ridge`,
  `Optimization.gradient_ridge`).
* `Optimization.exists_slowFirstOrder_interpolant` — the data of Theorem 2.2.3 (steepest descent,
  and the first-order trust-region and regularization methods).
* `Optimization.exists_slowNegCurvature_interpolant` — the data (3.2.24) of Theorem 3.2.7: slow
  convergence to second-order criticality.
* `Optimization.exists_slowSecondOrder_interpolant` — the data (3.5.12) of Theorem 3.5.4: slow
  convergence to first-order criticality for second-order methods.
* `Optimization.exists_contDiff_interpolating_separated_jets` — the multidimensional gluing behind
  Theorem 3.1.1 ((3.1.7)): quadratic jets at points `r` apart are interpolated by a smooth
  function whose derivatives of order `≤ 3` are bounded independently of the number of points
  (sum of translated bumps times the quadratic Taylor polynomials; Taylor-data form
  `Optimization.exists_contDiff_interpolating_separated_taylorData`).

## Implementation notes

The integrality assumption of Theorem 2.2.3 (`ε⁻²` is an integer) is a hypothesis
`k_ε ε² = 1`. In (3.2.25) the book prints `x_k = (k - 1) ε`, a typo for `x_k = k ε` (with
`θ ≡ 1`), and the claim `f_{k_ε} ≥ 0` needs `ε⁻³` integral; only boundedness of `f` is used here.
-/

open Set
open scoped RealInnerProductSpace

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

end Ridge

/-! ### Small sums of the Hermite consistency condition -/

theorem sum_Icc_zero_one (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 0 1, φ i = φ 0 + φ 1 := by
  rw [show Finset.Icc 0 1 = {0, 1} by decide, Finset.sum_pair (by norm_num)]

theorem sum_Icc_zero_two (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 0 2, φ i = φ 0 + φ 1 + φ 2 := by
  rw [show Finset.Icc 0 2 = {0, 1, 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num), add_assoc]

theorem sum_Icc_one_two (φ : ℕ → ℝ) : ∑ i ∈ Finset.Icc 1 2, φ i = φ 1 + φ 2 := by
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]

/-- The Hermite consistency condition (A.32) for `p = 1`, in expanded form. -/
theorem hermite_consistency_one {a b : ℕ → ℝ} {s κ : ℝ}
    (h0 : |b 0 - (a 0 + a 1 * s)| ≤ κ * s ^ 2) (h1 : |b 1 - a 1| ≤ κ * s) :
    ∀ j ≤ 1, |b j - ∑ i ∈ Finset.Icc j 1, a i * s ^ (i - j) / (i - j).factorial| ≤
      κ * s ^ (1 - j + 1) := by
  intro j hj
  interval_cases j
  · simpa [sum_Icc_zero_one] using h0
  · simpa using h1

/-- The Hermite consistency condition (A.32) for `p = 2`, in expanded form. -/
theorem hermite_consistency_two {a b : ℕ → ℝ} {s κ : ℝ}
    (h0 : |b 0 - (a 0 + a 1 * s + a 2 * s ^ 2 / 2)| ≤ κ * s ^ 3)
    (h1 : |b 1 - (a 1 + a 2 * s)| ≤ κ * s ^ 2) (h2 : |b 2 - a 2| ≤ κ * s) :
    ∀ j ≤ 2, |b j - ∑ i ∈ Finset.Icc j 2, a i * s ^ (i - j) / (i - j).factorial| ≤
      κ * s ^ (2 - j + 1) := by
  intro j hj
  interval_cases j
  · simpa [sum_Icc_zero_two, Nat.factorial] using h0
  · simpa [sum_Icc_one_two] using h1
  · simpa using h2

/-! ### First-order data (Theorem 2.2.3) -/

/-- **First-order slow example** ([cartis2022evaluation], proof of Theorem 2.2.3,
(2.2.14)–(2.2.22)).
For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0` depending only on `a, b` such that:
for every `ε ∈ (0, 1]` with `k_ε = ε⁻²` an integer, every `θ` with `θ k ∈ [a, b]`, and with
`ω_k = ε (k_ε - k)/k_ε`, `g_k = -(ε + ω_k)`, `x_0 = 0`, `x_{k+1} = x_k - θ_k g_k`, `f_0 = 4 b`,
`f_{k+1} = f_k - θ_k g_k²`, there is a `C¹` function `G : ℝ → ℝ` with `L`-Lipschitz derivative,
`|G|, |G'| ≤ B`, `G (x k) = f_k` and `G' (x k) = g_k` for `k ≤ k_ε`. The book's case is
`θ ≡ t_ini`. The recurrences and the bounds on `θ` are only required for `k < k_ε`, and `x 0` is
arbitrary. -/
theorem exists_slowFirstOrder_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (kε : ℕ) (θ x f : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (kε : ℝ) * ε ^ 2 = 1 → (∀ k < kε, θ k ∈ Icc a b) →
      (∀ k < kε, x (k + 1) = x k + θ k * (ε + ε * ((kε : ℝ) - k) / kε)) → f 0 = 4 * b →
      (∀ k < kε, f (k + 1) = f k - θ k * (ε + ε * ((kε : ℝ) - k) / kε) ^ 2) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧ (∀ s t, |deriv G s - deriv G t| ≤ L * |s - t|) ∧
        (∀ t, |G t| ≤ B) ∧ (∀ t, |deriv G t| ≤ B) ∧
        ∀ k ≤ kε, G (x k) = f k ∧ deriv G (x k) = -(ε + ε * ((kε : ℝ) - k) / kε) := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (1 / a) (max (4 * b) 2) with hκ
  have hκa : 1 / a ≤ κ := le_max_left _ _
  have hκb : 4 * b ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ2 : 2 ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 1 hκ0
  refine ⟨L, B, hL, hB, fun ε kε θ x f hε hε1 hk hθ hx hf0 hf => ?_⟩
  set ω : ℕ → ℝ := fun k => ε * ((kε : ℝ) - k) / kε with hω
  have hx' : ∀ k < kε, x (k + 1) = x k + θ k * (ε + ω k) := hx
  have hf' : ∀ k < kε, f (k + 1) = f k - θ k * (ε + ω k) ^ 2 := hf
  have hkε : (0 : ℝ) < kε := by
    rcases Nat.eq_zero_or_pos kε with h | h
    · rw [h] at hk
      norm_num at hk
    · exact_mod_cast h
  have hω0 : ∀ k ≤ kε, 0 ≤ ω k ∧ ω k ≤ ε := fun k hk' => by
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    simp only [ω]
    refine ⟨div_nonneg (mul_nonneg hε.le (by linarith)) hkε.le, ?_⟩
    rw [div_le_iff₀ hkε]
    nlinarith
  have hωs : ∀ k, ω k - ω (k + 1) = ε ^ 3 := fun k => by
    simp only [ω]
    push_cast
    field_simp
    nlinarith
  clear_value ω
  clear hx hf
  -- steps
  have hstep : ∀ k < kε, a * ε ≤ θ k * (ε + ω k) ∧ θ k * (ε + ω k) ≤ 2 * b * ε :=
    fun k hk' => by
      obtain ⟨h0, h1⟩ := hω0 k hk'.le
      obtain ⟨ha', hb'⟩ := hθ k hk'
      constructor <;> nlinarith
  -- function values
  have hfsum : ∀ k ≤ kε, f k = 4 * b - ∑ i ∈ Finset.range k, θ i * (ε + ω i) ^ 2 := by
    intro k
    induction k with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      rw [hf' k (by omega), ih (by omega), Finset.sum_range_succ]
      ring
  have hfb : ∀ k ≤ kε, 0 ≤ f k ∧ f k ≤ 4 * b := fun k hk' => by
    rw [hfsum k hk']
    have hterm : ∀ i ∈ Finset.range k, 0 ≤ θ i * (ε + ω i) ^ 2 ∧
        θ i * (ε + ω i) ^ 2 ≤ b * (2 * ε) ^ 2 := fun i hi => by
      have hi' : i ≤ kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨h0, h1⟩ := hω0 i hi'
      obtain ⟨ha', hb'⟩ := hθ i (by have := Finset.mem_range.1 hi; omega)
      have hθ0 : 0 ≤ θ i := by linarith
      constructor
      · positivity
      · have h2 : (ε + ω i) ^ 2 ≤ (2 * ε) ^ 2 := by nlinarith
        nlinarith
    have hs0 := Finset.sum_nonneg fun i hi => (hterm i hi).1
    have hs1 : ∑ i ∈ Finset.range k, θ i * (ε + ω i) ^ 2 ≤ k * (b * (2 * ε) ^ 2) := by
      have := Finset.sum_le_sum fun i hi => (hterm i hi).2
      simpa using this
    have hk'' : (k : ℝ) ≤ kε := by exact_mod_cast hk'
    have hs2 : (k : ℝ) * (b * (2 * ε) ^ 2) ≤ 4 * b :=
      calc (k : ℝ) * (b * (2 * ε) ^ 2) ≤ kε * (b * (2 * ε) ^ 2) :=
            mul_le_mul_of_nonneg_right hk'' (by positivity)
        _ = 4 * b * (kε * ε ^ 2) := by ring
        _ = 4 * b := by rw [hk, mul_one]
    constructor <;> linarith
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j => if j = 0 then f k else -(ε + ω k) with hF
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * (ε + ω k) := fun k hk => by
    rw [hx' k hk]; ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk' => by
      have := (hstep k hk').1
      rw [← sub_pos, hgap k hk']
      exact lt_of_lt_of_le (by positivity) this)
    (fun k hk' => by rw [hgap k hk']; nlinarith [(hstep k hk').2])
    (fun k hk' j hj => by
      obtain ⟨h0, h1⟩ := hω0 k hk'
      interval_cases j
      · simp only [F, ↓reduceIte]
        rw [abs_le]
        constructor <;> linarith [hfb k hk']
      · simp only [F, one_ne_zero, ↓reduceIte]
        rw [abs_neg, abs_of_nonneg (by linarith)]
        linarith)
    (fun k hk' => by
      refine hermite_consistency_one ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, hgap k hk', hf' k hk']
        have : f k - θ k * (ε + ω k) ^ 2 - (f k + -(ε + ω k) * (θ k * (ε + ω k))) = 0 := by
          ring
        rw [this, abs_zero]
        positivity
      · simp only [F, one_ne_zero, ↓reduceIte, hgap k hk']
        have hs := (hstep k hk').1
        rw [show -(ε + ω (k + 1)) - -(ε + ω k) = ε ^ 3 by linarith [hωs k],
          abs_of_nonneg (by positivity)]
        have h1 : ε ^ 3 ≤ ε := by
          have : ε ^ 2 ≤ 1 := by nlinarith
          nlinarith
        calc ε ^ 3 ≤ ε := h1
          _ = 1 / a * (a * ε) := by field_simp
          _ ≤ κ * (θ k * (ε + ω k)) := mul_le_mul hκa hs (by positivity) hκ0)
  refine ⟨G, hGc, fun s t => ?_, fun t => ?_, fun t => ?_, fun k hk' => ⟨?_, ?_⟩⟩
  · simpa [iteratedDeriv_one] using hGL s t
  · simpa using hGB 0 (Nat.zero_le 1) t
  · simpa [iteratedDeriv_one] using hGB 1 le_rfl t
  · simpa [F] using hGj k hk' 0 (Nat.zero_le 1)
  · have := hGj k hk' 1 le_rfl
    simp only [iteratedDeriv_one, F, one_ne_zero, ↓reduceIte] at this
    rw [this, hω]

/-! ### Second-order data, slow to second-order criticality (Theorem 3.2.7) -/

/-- **Negative-curvature slow example** ([cartis2022evaluation], proof of Theorem 3.2.7, (3.2.23)–
(3.2.27)). For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0` depending only on
`a, b` such that: for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε⁻³⌉₊`, `c_k = 2 - k/k_ε`,
`H_k = -ε c_k`, steps `s_k = θ_k ε` (`θ k ∈ [a, b]`), `x_{k+1} = x_k + s_k`, `f_0 = 1`,
`f_{k+1} = f_k + H_k s_k²/2`, there is a `C²` function `G : ℝ → ℝ` with `L`-Lipschitz second
derivative, `|G^{(j)}| ≤ B` (`j ≤ 2`), and `G (x k) = f_k`, `G' (x k) = 0`, `G'' (x k) = H_k` for
`k ≤ k_ε`. TR2 uses `θ ≡ 1` (the book's (3.2.25) `x_k = (k - 1) ε` is a typo for `x_k = k ε`). The
recurrences and the bounds on `θ` are only required for `k < k_ε`, and `x 0` is arbitrary. -/
theorem exists_slowNegCurvature_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x f : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, θ k ∈ Icc a b) →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, x (k + 1) = x k + θ k * ε) → f 0 = 1 →
      (∀ k < ⌈(ε ^ 3)⁻¹⌉₊, f (k + 1) =
        f k + -ε * (2 - k / ⌈(ε ^ 3)⁻¹⌉₊) * (θ k * ε) ^ 2 / 2) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        (∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        ∀ k ≤ ⌈(ε ^ 3)⁻¹⌉₊, G (x k) = f k ∧ deriv G (x k) = 0 ∧
          iteratedDeriv 2 G (x k) = -ε * (2 - k / ⌈(ε ^ 3)⁻¹⌉₊) := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (2 * b / a ^ 2) (max (1 / a) (max (1 + 2 * b ^ 2) (max 2 b))) with hκ
  have hκ1 : 2 * b / a ^ 2 ≤ κ := le_max_left _ _
  have hκ2 : 1 / a ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ3 : 1 + 2 * b ^ 2 ≤ κ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ4 : 2 ≤ κ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ5 : b ≤ κ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 2 hκ0
  refine ⟨L, B, hL, hB, fun ε θ x f hε hε1 hθ hx hf0 hf => ?_⟩
  set kε : ℕ := ⌈(ε ^ 3)⁻¹⌉₊ with hkεdef
  have hkε1 : 1 ≤ kε := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hkε : (0 : ℝ) < kε := by exact_mod_cast hkε1
  have hkε3 : (kε : ℝ) * ε ^ 3 ≤ 2 := by
    have h := Nat.ceil_lt_add_one (inv_nonneg.2 (pow_nonneg hε.le 3))
    rw [← hkεdef] at h
    have hε3 : ε ^ 3 ≤ 1 := pow_le_one₀ hε.le hε1
    have : (kε : ℝ) * ε ^ 3 < ((ε ^ 3)⁻¹ + 1) * ε ^ 3 :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [add_mul, inv_mul_cancel₀ (by positivity), one_mul] at this
    linarith
  set c : ℕ → ℝ := fun k => 2 - k / kε with hc
  have hf' : ∀ k < kε, f (k + 1) = f k + -ε * c k * (θ k * ε) ^ 2 / 2 := hf
  have hc12 : ∀ k ≤ kε, 1 ≤ c k ∧ c k ≤ 2 := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    simp only [c]
    constructor
    · rw [le_sub_comm, div_le_iff₀ hkε]
      linarith
    · have : 0 ≤ (k : ℝ) / kε := by positivity
      linarith
  have hcs : ∀ k, c k - c (k + 1) = 1 / kε := fun k => by
    simp only [c]
    push_cast
    ring
  clear_value c
  clear hf
  have hθ0 : ∀ k < kε, 0 < θ k := fun k hk => ha.trans_le (hθ k hk).1
  -- function values
  have hfsum : ∀ k ≤ kε, f k = 1 - ∑ i ∈ Finset.range k, ε * c i * (θ i * ε) ^ 2 / 2 := by
    intro k
    induction k with
    | zero => intro _; simp [hf0]
    | succ k ih =>
      intro hk
      rw [hf' k (by omega), ih (by omega), Finset.sum_range_succ]
      ring
  have hfb : ∀ k ≤ kε, |f k| ≤ 1 + 2 * b ^ 2 := fun k hk => by
    rw [hfsum k hk]
    have hterm : ∀ i ∈ Finset.range k, 0 ≤ ε * c i * (θ i * ε) ^ 2 / 2 ∧
        ε * c i * (θ i * ε) ^ 2 / 2 ≤ b ^ 2 * ε ^ 3 := fun i hi => by
      have hi' : i ≤ kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨h1, h2⟩ := hc12 i hi'
      have hik : i < kε := by have := Finset.mem_range.1 hi; omega
      obtain ⟨ha', hb'⟩ := hθ i hik
      have hθ0 := hθ0 i hik
      constructor
      · have : 0 ≤ c i := by linarith
        positivity
      · have h3 : (θ i * ε) ^ 2 ≤ (b * ε) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_right hb' hε.le
        have h4 : ε * c i ≤ ε * 2 := mul_le_mul_of_nonneg_left h2 hε.le
        calc ε * c i * (θ i * ε) ^ 2 / 2 ≤ ε * 2 * (b * ε) ^ 2 / 2 := by gcongr
          _ = b ^ 2 * ε ^ 3 := by ring
    have hs0 := Finset.sum_nonneg fun i hi => (hterm i hi).1
    have hs1 : ∑ i ∈ Finset.range k, ε * c i * (θ i * ε) ^ 2 / 2 ≤ k * (b ^ 2 * ε ^ 3) := by
      have := Finset.sum_le_sum fun i hi => (hterm i hi).2
      simpa using this
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have hs2 : (k : ℝ) * (b ^ 2 * ε ^ 3) ≤ 2 * b ^ 2 := by
      calc (k : ℝ) * (b ^ 2 * ε ^ 3) ≤ kε * (b ^ 2 * ε ^ 3) :=
            mul_le_mul_of_nonneg_right hk' (by positivity)
        _ = b ^ 2 * (kε * ε ^ 3) := by ring
        _ ≤ b ^ 2 * 2 := mul_le_mul_of_nonneg_left hkε3 (by positivity)
        _ = 2 * b ^ 2 := by ring
    rw [abs_le]
    constructor <;> nlinarith
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j => if j = 0 then f k else if j = 1 then 0 else -ε * c k with hF
  have h21 : (2 : ℕ) ≠ 1 := by norm_num
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * ε := fun k hk => by rw [hx k hk]; ring
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk => by rw [← sub_pos, hgap k hk]; exact mul_pos (hθ0 k hk) hε)
    (fun k hk => by
      rw [hgap k hk]
      calc θ k * ε ≤ b * 1 := mul_le_mul (hθ k hk).2 hε1 hε.le hb.le
        _ ≤ κ := by linarith)
    (fun k hk j hj => by
      obtain ⟨h1, h2⟩ := hc12 k hk
      interval_cases j
      · simpa [F] using (hfb k hk).trans hκ3
      · simpa [F] using hκ0
      · simp only [F, ↓reduceIte, OfNat.ofNat_ne_zero, h21]
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith)
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hc12 k hk.le
      obtain ⟨ha', hb'⟩ := hθ k hk
      have hθk := hθ0 k hk
      refine hermite_consistency_two ?_ ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk, hf' k hk]
        have : f k + -ε * c k * (θ k * ε) ^ 2 / 2 -
            (f k + 0 * (θ k * ε) + -ε * c k * (θ k * ε) ^ 2 / 2) = 0 := by ring
        rw [this, abs_zero]
        positivity
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        have e : (0 : ℝ) - (0 + -ε * c k * (θ k * ε)) = c k * θ k * ε ^ 2 := by ring
        rw [e, abs_of_nonneg (by positivity)]
        have h3 : c k * θ k ≤ 2 * b := by nlinarith
        have h4 : 2 * b ≤ κ * θ k ^ 2 := by
          have : 2 * b / a ^ 2 * a ^ 2 ≤ κ * θ k ^ 2 :=
            mul_le_mul hκ1 (pow_le_pow_left₀ ha.le ha' 2) (by positivity) hκ0
          rwa [div_mul_cancel₀ _ (by positivity)] at this
        calc c k * θ k * ε ^ 2 ≤ 2 * b * ε ^ 2 := by gcongr
          _ ≤ κ * θ k ^ 2 * ε ^ 2 := by gcongr
          _ = κ * (θ k * ε) ^ 2 := by ring
      · simp only [F, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        have e : -ε * c (k + 1) - -ε * c k = ε / kε := by
          rw [show -ε * c (k + 1) - -ε * c k = ε * (c k - c (k + 1)) by ring, hcs]
          ring
        rw [e, abs_of_nonneg (by positivity)]
        have h3 : ε / kε ≤ ε := div_le_self hε.le (by exact_mod_cast hkε1)
        have h4 : 1 ≤ κ * θ k := by
          have : 1 / a * a ≤ κ * θ k := mul_le_mul hκ2 ha' ha.le hκ0
          rwa [one_div_mul_cancel ha.ne'] at this
        nlinarith)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · simpa [F] using hGj k hk 0 (Nat.zero_le 2)
  · simpa [F, iteratedDeriv_one] using hGj k hk 1 (by norm_num)
  · have := hGj k hk 2 le_rfl
    simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte] at this
    rw [this, hc]

/-! ### Second-order data, slow to first-order criticality (Theorem 3.5.4) -/

/-- **Second-order slow example** ([cartis2022evaluation], (3.5.11)–(3.5.19) and the proof of
Theorem 3.5.4 in Appendix B). For step factors in `[a, b]`, `0 < a ≤ b`, there are `L, B ≥ 0`
depending only on `a, b` such that: for every `ε ∈ (0, 1]`, with `k_ε = ⌈ε^{-3/2}⌉₊`,
`f_k = 1 - k ε^{3/2}/2`, `g_k = -2 ε f_k`, `H_k = 4 ε^{1/2} f_k²` (3.5.12) and
`x_{k+1} = x_k + θ_k ε^{1/2}/(2 f_k)` (3.5.19) (`θ k ∈ [a, b]`), there is a `C²` function
`G : ℝ → ℝ` with `L`-Lipschitz second derivative, `|G^{(j)}| ≤ B` (`j ≤ 2`), interpolating
`(f_k, g_k, H_k)` at `x_k` for `k ≤ k_ε`. The recurrence and the bounds on `θ` are only required
for `k < k_ε`, and `x 0` is arbitrary. -/
theorem exists_slowSecondOrder_interpolant {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ (ε : ℝ) (θ x : ℕ → ℝ), 0 < ε → ε ≤ 1 →
      (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, θ k ∈ Icc a b) →
      (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊,
        x (k + 1) = x k + θ k * ε ^ (1 / 2 : ℝ) / (2 * (1 - k * ε ^ (3 / 2 : ℝ) / 2))) →
      ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧
        (∀ s t, |iteratedDeriv 2 G s - iteratedDeriv 2 G t| ≤ L * |s - t|) ∧
        (∀ j ≤ 2, ∀ t, |iteratedDeriv j G t| ≤ B) ∧
        ∀ k ≤ ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, G (x k) = 1 - k * ε ^ (3 / 2 : ℝ) / 2 ∧
          deriv G (x k) = -2 * ε * (1 - k * ε ^ (3 / 2 : ℝ) / 2) ∧
          iteratedDeriv 2 G (x k) = 4 * ε ^ (1 / 2 : ℝ) * (1 - k * ε ^ (3 / 2 : ℝ) / 2) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  set κ : ℝ := max (4 * (1 + b) ^ 2 / a ^ 3) (max (4 * (1 + 2 * b) / a ^ 2) (max (8 / a)
    (max 4 b))) with hκ
  have hκ1 : 4 * (1 + b) ^ 2 / a ^ 3 ≤ κ := le_max_left _ _
  have hκ2 : 4 * (1 + 2 * b) / a ^ 2 ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hκ3 : 8 / a ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hκ4 : 4 ≤ κ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ5 : b ≤ κ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨L, B, hL, hB, hH⟩ := Hermite.exists_contDiff_interpolating_jets_bounded_of_forall_le 2 hκ0
  refine ⟨L, B, hL, hB, fun ε θ x hε hε1 hθ hx => ?_⟩
  -- pass to `r = ε^{1/2}`
  set r : ℝ := √ε with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.2 hε1
  have hεr : ε = r ^ 2 := (Real.sq_sqrt hε.le).symm
  have h12 : ε ^ (1 / 2 : ℝ) = r := (Real.sqrt_eq_rpow ε).symm
  have h32 : ε ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 * (3 : ℕ) by norm_num, Real.rpow_mul_natCast hε.le, h12]
  have hm32 : ε ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by rw [Real.rpow_neg hε.le, h32]
  rw [h12, h32, hm32]
  simp only [h12, h32, hm32] at hx hθ
  clear_value r
  subst hεr
  clear h12 h32 hm32 hrdef
  set kε : ℕ := ⌈(r ^ 3)⁻¹⌉₊ with hkεdef
  have hkε2 : (kε : ℝ) * r ^ 3 ≤ 2 := by
    have h := Nat.ceil_lt_add_one (inv_nonneg.2 (pow_nonneg hr.le 3))
    rw [← hkεdef] at h
    have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr.le hr1
    have : (kε : ℝ) * r ^ 3 < ((r ^ 3)⁻¹ + 1) * r ^ 3 :=
      mul_lt_mul_of_pos_right h (by positivity)
    rw [add_mul, inv_mul_cancel₀ (by positivity), one_mul] at this
    linarith
  set f : ℕ → ℝ := fun k => 1 - k * r ^ 3 / 2 with hfdef
  have hx' : ∀ k < kε, x (k + 1) = x k + θ k * r / (2 * f k) := hx
  have hfs : ∀ k, f (k + 1) = f k - r ^ 3 / 2 := fun k => by
    simp only [f]
    push_cast
    ring
  have hf1 : ∀ k, f k ≤ 1 := fun k => by
    simp only [f]
    have : 0 ≤ (k : ℝ) * r ^ 3 / 2 := by positivity
    linarith
  have hf0 : ∀ k ≤ kε, 0 ≤ f k := fun k hk => by
    have hk' : (k : ℝ) ≤ kε := by exact_mod_cast hk
    simp only [f]
    nlinarith [pow_pos hr 3]
  have hfh : ∀ k < kε, 1 / 2 < f k := fun k hk => by
    have h := (Nat.lt_ceil).1 (hkεdef ▸ hk : k < ⌈(r ^ 3)⁻¹⌉₊)
    have : (k : ℝ) * r ^ 3 < 1 := by
      have := mul_lt_mul_of_pos_right h (pow_pos hr 3)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    simp only [f]
    linarith
  clear_value f
  clear hx
  have hθ0 : ∀ k < kε, 0 < θ k := fun k hk => ha.trans_le (hθ k hk).1
  -- the jets
  set F : ℕ → ℕ → ℝ := fun k j =>
    if j = 0 then f k else if j = 1 then -2 * r ^ 2 * f k else 4 * r * f k ^ 2 with hF
  have h21 : (2 : ℕ) ≠ 1 := by norm_num
  have hgap : ∀ k < kε, x (k + 1) - x k = θ k * r / (2 * f k) := fun k hk => by
    rw [hx' k hk]; ring
  -- the step is at least `θ r / 2 ≥ a r / 2` and at most `b`
  have hstep : ∀ k < kε, a * r / 2 ≤ θ k * r / (2 * f k) ∧ θ k * r / (2 * f k) ≤ b := by
    intro k hk
    have hfk := hfh k hk
    have hf1k := hf1 k
    obtain ⟨ha', hb'⟩ := hθ k hk
    have har : a * r ≤ θ k * r := mul_le_mul_of_nonneg_right ha' hr.le
    have hbr : θ k * r ≤ b * 1 := mul_le_mul hb' hr1 hr.le hb.le
    constructor
    · rw [le_div_iff₀ (by linarith)]
      have : a * r * f k ≤ a * r := mul_le_of_le_one_right (by positivity) hf1k
      calc a * r / 2 * (2 * f k) = a * r * f k := by ring
        _ ≤ θ k * r := this.trans har
    · rw [div_le_iff₀ (by linarith)]
      have : b * 1 ≤ b * (2 * f k) := mul_le_mul_of_nonneg_left (by linarith) hb.le
      linarith
  obtain ⟨G, hGc, hGL, hGB, hGj, -, -⟩ := hH kε x F
    (fun k hk => by
      rw [← sub_pos, hgap k hk]
      have := hfh k hk
      have := hθ0 k hk
      positivity)
    (fun k hk => by rw [hgap k hk]; linarith [(hstep k hk).2])
    (fun k hk j hj => by
      have h0 := hf0 k hk
      have h1 := hf1 k
      have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
      interval_cases j
      · simp only [F, ↓reduceIte]
        rw [abs_of_nonneg h0]
        linarith
      · simp only [F, one_ne_zero, ↓reduceIte]
        rw [abs_of_nonpos (by nlinarith)]
        nlinarith [mul_le_mul hr2 h1 h0 zero_le_one]
      · simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte]
        rw [abs_of_nonneg (by positivity)]
        have : f k ^ 2 ≤ 1 := pow_le_one₀ h0 h1
        nlinarith [mul_le_mul hr1 this (by positivity) zero_le_one])
    (fun k hk => by
      have hfk := hfh k hk
      have hf1k := hf1 k
      have hf0' := hf0 (k + 1) hk
      have hf1' := hf1 (k + 1)
      have hθk := hθ0 k hk
      obtain ⟨ha', hb'⟩ := hθ k hk
      obtain ⟨hs1, -⟩ := hstep k hk
      set s := θ k * r / (2 * f k) with hsdef
      have hs0 : 0 ≤ a * r / 2 := by positivity
      have hfne : f k ≠ 0 := by linarith
      refine hermite_consistency_two ?_ ?_ ?_
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        rw [← hsdef]
        have e : f (k + 1) - (f k + -2 * r ^ 2 * f k * s + 4 * r * f k ^ 2 * s ^ 2 / 2) =
            -(r ^ 3 * (1 - θ k) ^ 2 / 2) := by
          rw [hfs, hsdef]
          field_simp
          ring
        rw [e, abs_neg, abs_of_nonneg (by positivity)]
        have h1 : (1 - θ k) ^ 2 ≤ (1 + b) ^ 2 := by nlinarith
        have h2 : (a * r / 2) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs0 hs1 3
        have h3 : 4 * (1 + b) ^ 2 / a ^ 3 * (a * r / 2) ^ 3 = (1 + b) ^ 2 * r ^ 3 / 2 := by
          field_simp
          ring
        calc r ^ 3 * (1 - θ k) ^ 2 / 2 ≤ (1 + b) ^ 2 * r ^ 3 / 2 := by nlinarith [pow_pos hr 3]
          _ = 4 * (1 + b) ^ 2 / a ^ 3 * (a * r / 2) ^ 3 := h3.symm
          _ ≤ κ * s ^ 3 := mul_le_mul hκ1 h2 (by positivity) hκ0
      · simp only [F, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero, h21, hgap k hk]
        rw [← hsdef]
        have e : -2 * r ^ 2 * f (k + 1) - (-2 * r ^ 2 * f k + 4 * r * f k ^ 2 * s) =
            r ^ 5 - 2 * r ^ 2 * θ k * f k := by
          rw [hfs, hsdef]
          field_simp
          ring
        rw [e]
        have hr5 : r ^ 5 ≤ r ^ 2 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
        have h1 : |r ^ 5 - 2 * r ^ 2 * θ k * f k| ≤ (1 + 2 * b) * r ^ 2 := by
          rw [abs_le]
          have h0 : 0 ≤ r ^ 2 * θ k * f k := by positivity
          have hθf : θ k * f k ≤ b * 1 := mul_le_mul hb' hf1k (by linarith) hb.le
          have h1 : r ^ 2 * θ k * f k ≤ r ^ 2 * b :=
            calc r ^ 2 * θ k * f k = r ^ 2 * (θ k * f k) := by ring
              _ ≤ r ^ 2 * (b * 1) := mul_le_mul_of_nonneg_left hθf (by positivity)
              _ = r ^ 2 * b := by ring
          have h5 : 0 ≤ r ^ 5 := by positivity
          have h2 : 0 ≤ r ^ 2 := by positivity
          constructor <;> linarith
        have h2 : (a * r / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs0 hs1 2
        have h3 : 4 * (1 + 2 * b) / a ^ 2 * (a * r / 2) ^ 2 = (1 + 2 * b) * r ^ 2 := by
          field_simp
          ring
        calc |r ^ 5 - 2 * r ^ 2 * θ k * f k| ≤ (1 + 2 * b) * r ^ 2 := h1
          _ = 4 * (1 + 2 * b) / a ^ 2 * (a * r / 2) ^ 2 := h3.symm
          _ ≤ κ * s ^ 2 := mul_le_mul hκ2 h2 (by positivity) hκ0
      · simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte, hgap k hk]
        rw [← hsdef]
        have e : 4 * r * f (k + 1) ^ 2 - 4 * r * f k ^ 2 = -(2 * r ^ 4 * (f (k + 1) + f k)) := by
          rw [hfs]
          ring
        rw [e, abs_neg, abs_of_nonneg (by positivity)]
        have hr4 : r ^ 4 ≤ r := by
          calc r ^ 4 ≤ r ^ 1 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
            _ = r := pow_one r
        have h3 : 8 / a * (a * r / 2) = 4 * r := by
          field_simp
          ring
        have hsum : f (k + 1) + f k ≤ 2 := by linarith
        calc 2 * r ^ 4 * (f (k + 1) + f k) ≤ 2 * r * 2 :=
              mul_le_mul (by linarith) hsum (by linarith) (by positivity)
          _ = 8 / a * (a * r / 2) := by rw [h3]; ring
          _ ≤ κ * s := mul_le_mul hκ3 hs1 hs0 hκ0)
  refine ⟨G, hGc, hGL, hGB, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · have := hGj k hk 0 (Nat.zero_le 2)
    simp only [F, ↓reduceIte, iteratedDeriv_zero] at this
    rw [this, hfdef]
  · have := hGj k hk 1 (by norm_num)
    simp only [F, one_ne_zero, ↓reduceIte, iteratedDeriv_one] at this
    rw [this, hfdef]
  · have := hGj k hk 2 le_rfl
    simp only [F, OfNat.ofNat_ne_zero, h21, ↓reduceIte] at this
    rw [this, hfdef]

/-! ### Gluing separated quadratic jets -/

section SeparatedJets

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gluing with separation `2r`; see `exists_contDiff_interpolating_separated_taylorData`. -/
private theorem exists_contDiff_interpolating_separated_taylorData_aux [FiniteDimensional ℝ E]
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (D : ℕ → FormalMultilinearSeries ℝ E ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → 2 * r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, (D k).IsSymm 2) → (∀ k ≤ K, ∀ i ≤ 2, ‖D k i‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, ∀ j ≤ 2, iteratedFDeriv ℝ j F (x k) = D k j) ∧
        ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  let φ : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff
  -- a uniform bound on the derivatives of `φ`
  obtain ⟨Cφ, hCφ0, hCφ⟩ : ∃ C, 0 ≤ C ∧ ∀ j ≤ 3, ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ C := by
    have : ∀ j : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ C := fun j =>
      (hφc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
        (φ.hasCompactSupport.iteratedFDeriv j)
    choose C hC using this
    refine ⟨|C 0| + |C 1| + |C 2| + |C 3|, by positivity, fun j hj z => ?_⟩
    have h0 := le_abs_self (C 0)
    have h1 := le_abs_self (C 1)
    have h2 := le_abs_self (C 2)
    have h3 := le_abs_self (C 3)
    have a0 := abs_nonneg (C 0)
    have a1 := abs_nonneg (C 1)
    have a2 := abs_nonneg (C 2)
    have a3 := abs_nonneg (C 3)
    interval_cases j
    · linarith [hC 0 z]
    · linarith [hC 1 z]
    · linarith [hC 2 z]
    · linarith [hC 3 z]
  have hφ0 : ∀ z : E, r / 2 ≤ ‖z‖ → φ z = 0 := fun z hz => by
    have : z ∉ Function.support φ := by
      rw [φ.support_eq, Metric.mem_ball, dist_zero_right, not_lt]; exact hz
    simpa using this
  have hφD0 : ∀ j z, r / 2 < ‖z‖ → iteratedFDeriv ℝ j φ z = 0 := fun j z hz => by
    have : z ∉ tsupport φ := by
      rw [φ.tsupport_eq, Metric.mem_closedBall, dist_zero_right, not_le]; exact hz
    exact Function.notMem_support.1 fun h => this (support_iteratedFDeriv_subset j h)
  set Q := 3 * κ * (1 + r / 2) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨8 * Cφ * Q, by positivity, fun K x D hsep hsymm hD => ?_⟩
  set term : ℕ → E → ℝ := fun k y => φ (y - x k) * (D k).taylorSum 2 (y - x k) with hterm
  have hterm_c : ∀ k, ContDiff ℝ ∞ (term k) := fun k =>
    (hφc.comp (contDiff_id.sub contDiff_const)).mul
      (((D k).contDiff_taylorSum 2).comp (contDiff_id.sub contDiff_const))
  set F : E → ℝ := fun y => ∑ k ∈ Finset.range (K + 1), term k y with hF
  have hFc : ContDiff ℝ ∞ F := ContDiff.sum fun k _ => hterm_c k
  -- locality
  have hloc : ∀ y, ∀ k ≤ K, (∀ l ≤ K, l ≠ k → r ≤ ‖y - x l‖) → F =ᶠ[nhds y] term k := by
    intro y k hk hl
    filter_upwards [Metric.ball_mem_nhds y (by positivity : 0 < r / 2)] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    refine Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (by omega)) fun l hl' hlk => ?_
    have hlK : l ≤ K := by have := Finset.mem_range.1 hl'; omega
    have : r / 2 ≤ ‖z - x l‖ := by
      have h1 := hl l hlK hlk
      have h2 : ‖y - x l‖ ≤ ‖z - x l‖ + ‖z - y‖ := by
        calc ‖y - x l‖ = ‖(z - x l) - (z - y)‖ := by congr 1; abel
          _ ≤ ‖z - x l‖ + ‖z - y‖ := norm_sub_le _ _
      linarith
    simp only [hterm, hφ0 _ this, zero_mul]
  have hzero : ∀ y, (∀ l ≤ K, r ≤ ‖y - x l‖) → F =ᶠ[nhds y] fun _ => 0 := by
    intro y hl
    filter_upwards [Metric.ball_mem_nhds y (by positivity : 0 < r / 2)] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    refine Finset.sum_eq_zero fun l hl' => ?_
    have hlK : l ≤ K := by have := Finset.mem_range.1 hl'; omega
    have : r / 2 ≤ ‖z - x l‖ := by
      have h1 := hl l hlK
      have h2 : ‖y - x l‖ ≤ ‖z - x l‖ + ‖z - y‖ := by
        calc ‖y - x l‖ = ‖(z - x l) - (z - y)‖ := by congr 1; abel
          _ ≤ ‖z - x l‖ + ‖z - y‖ := norm_sub_le _ _
      linarith
    simp only [hterm, hφ0 _ this, zero_mul]
  -- the dichotomy: at most one node within distance `r`
  have hdich : ∀ y, (∃ k ≤ K, ∀ l ≤ K, l ≠ k → r ≤ ‖y - x l‖) ∨ ∀ l ≤ K, r ≤ ‖y - x l‖ := by
    intro y
    by_cases h : ∃ k ≤ K, ‖y - x k‖ < r
    · obtain ⟨k, hk, hyk⟩ := h
      refine Or.inl ⟨k, hk, fun l hl hlk => ?_⟩
      by_contra hcon
      have := hsep l hl k hk hlk
      have h2 : ‖x l - x k‖ ≤ ‖y - x l‖ + ‖y - x k‖ := by
        calc ‖x l - x k‖ = ‖(y - x k) - (y - x l)‖ := by congr 1; abel
          _ ≤ ‖y - x k‖ + ‖y - x l‖ := norm_sub_le _ _
          _ = ‖y - x l‖ + ‖y - x k‖ := add_comm _ _
      linarith
    · push Not at h
      exact Or.inr h
  -- bound on the derivatives of one term
  have hbound : ∀ k ≤ K, ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j (term k) y‖ ≤ 8 * Cφ * Q := by
    intro k hk j hj y
    have hf1 : ContDiff ℝ ∞ (fun y => φ (y - x k)) :=
      hφc.comp (contDiff_id.sub (contDiff_const (c := x k)))
    have hf2 : ContDiff ℝ ∞ (fun y => (D k).taylorSum 2 (y - x k)) :=
      ((D k).contDiff_taylorSum 2).comp (contDiff_id.sub (contDiff_const (c := x k)))
    have hmul := norm_iteratedFDeriv_mul_le hf1 hf2 y (n := j) (by exact_mod_cast le_top)
    refine hmul.trans ?_
    have hsummand : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => φ (y - x k)) y‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => (D k).taylorSum 2 (y - x k)) y‖ ≤
        (j.choose i : ℝ) * (Cφ * Q) := by
      intro i hi
      have hi3 : i ≤ 3 := by have := Finset.mem_range.1 hi; omega
      rw [iteratedFDeriv_comp_sub, iteratedFDeriv_comp_sub, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rcases le_or_gt ‖y - x k‖ (r / 2) with hy | hy
      · exact mul_le_mul (hCφ i hi3 _)
          ((D k).norm_iteratedFDeriv_taylorSum_two_le hκ (by positivity) (hD k hk) _ hy)
          (norm_nonneg _) hCφ0
      · rw [hφD0 i _ hy, norm_zero, zero_mul]
        positivity
    refine (Finset.sum_le_sum hsummand).trans ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    have : ((2 ^ j : ℕ) : ℝ) ≤ 8 := by
      have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj
      exact_mod_cast this
    nlinarith [mul_nonneg hCφ0 hQ0]
  refine ⟨F, hFc, fun k hk j hj => ?_, fun j hj y => ?_⟩
  · -- interpolation at the nodes
    have h1 : F =ᶠ[nhds (x k)] term k := hloc (x k) k hk fun l hl hlk => by
      have := hsep k hk l hl (Ne.symm hlk)
      linarith
    have h2 : term k =ᶠ[nhds (x k)] fun y => (D k).taylorSum 2 (y - x k) := by
      filter_upwards [Metric.closedBall_mem_nhds (x k) (by positivity : 0 < r / 4)] with z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have : φ (z - x k) = 1 :=
        φ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
      simp only [hterm, this, one_mul]
    rw [((h1.trans h2).iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_comp_sub, sub_self,
      FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero (hsymm k hk) hj]
  · rcases hdich y with ⟨k, hk, hl⟩ | hl
    · rw [((hloc y k hk hl).iteratedFDeriv ℝ j).eq_of_nhds]
      exact hbound k hk j hj y
    · rw [((hzero y hl).iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
        norm_zero]
      positivity

/-- **Gluing separated quadratic jets** (Taylor-data form). Let `E` be a finite-dimensional real
inner product space, `r > 0` and `κ ≥ 0`. There is `B ≥ 0` (depending only on `E`, `r` and `κ`)
such that for any points `x_0, …, x_K` with `‖x_i - x_j‖ ≥ r` (`i ≠ j`) and symmetric Taylor data
`D_k` with `‖D_{k,i}‖ ≤ κ` (`i ≤ 2`), there is a smooth `F : E → ℝ` whose derivatives of order
`j ≤ 2` at `x_k` are `D_{k,j}` and whose derivatives of order `j ≤ 3` are bounded by `B`.

The function is `F(y) = ∑_k φ(y - x_k) T_{D_k,2}(y - x_k)` with a fixed bump `φ` equal to `1` on
the ball of radius `r/8` and supported in the ball of radius `r/4`: near every point at most one
term is nonzero. -/
theorem exists_contDiff_interpolating_separated_taylorData [FiniteDimensional ℝ E] {r κ : ℝ}
    (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (D : ℕ → FormalMultilinearSeries ℝ E ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, (D k).IsSymm 2) → (∀ k ≤ K, ∀ i ≤ 2, ‖D k i‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, ∀ j ≤ 2, iteratedFDeriv ℝ j F (x k) = D k j) ∧
        ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  obtain ⟨B, hB, hmain⟩ :=
    exists_contDiff_interpolating_separated_taylorData_aux (E := E) (by positivity : 0 < r / 2) hκ
  exact ⟨B, hB, fun K x D hsep => hmain K x D fun i hi j hj hij => by
    linarith [hsep i hi j hj hij]⟩

/-- The quadratic jet `(f, g, H)` (value, gradient, Hessian) as Taylor data:
`D_0 = f`, `D_1 = ⟪g, ·⟫`, `D_2 = H`, `D_i = 0` for `i ≥ 3`. -/
noncomputable def quadJet (f : ℝ) (g : E) (H : E [×2]→L[ℝ] ℝ) : FormalMultilinearSeries ℝ E ℝ
  | 0 => ContinuousMultilinearMap.uncurry0 ℝ E f
  | 1 => (continuousMultilinearCurryFin1 ℝ E ℝ).symm (innerSL ℝ g)
  | 2 => H
  | _ + 3 => 0

theorem quadJet_isSymm {f : ℝ} {g : E} {H : E [×2]→L[ℝ] ℝ}
    (hH : ∀ v w, H ![v, w] = H ![w, v]) : (quadJet f g H).IsSymm 2 := by
  intro i hi σ v
  interval_cases i
  · exact congrArg _ (Subsingleton.elim _ _)
  · have : σ = 1 := Subsingleton.elim _ _
    subst this
    rfl
  · refine ContinuousMultilinearMap.apply_comp_perm_of_swap H (fun a b hab w => ?_) σ v
    have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    have hab' : Equiv.swap a b = Equiv.swap 0 1 := by
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · rfl
      · exact Equiv.swap_comm _ _
      · exact absurd rfl hab
    have hs : w ∘ Equiv.swap a b = ![w 1, w 0] := by
      rw [hab']; ext i; fin_cases i <;> simp
    change H (w ∘ Equiv.swap a b) = H w
    rw [hs, hw, hH]
    rfl

theorem norm_quadJet_le {f κ : ℝ} {g : E} {H : E [×2]→L[ℝ] ℝ} (hf : |f| ≤ κ) (hg : ‖g‖ ≤ κ)
    (hH : ‖H‖ ≤ κ) : ∀ i ≤ 2, ‖quadJet f g H i‖ ≤ κ := by
  intro i hi
  interval_cases i
  · simpa [quadJet, ContinuousMultilinearMap.uncurry0_norm] using hf
  · simpa [quadJet, innerSL_apply_norm] using hg
  · exact hH

/-- **Gluing separated quadratic jets** ([cartis2022evaluation], proof of Theorem 3.1.1, (3.1.7),
with a smooth bump in place of the book's piecewise-polynomial one). Let `E` be a
finite-dimensional real inner product space, `r > 0` and `κ ≥ 0`. There is `B ≥ 0` (depending
only on `E`, `r` and `κ`, not on the number of points) such that for any points
`x_0, …, x_K` with `‖x_i - x_j‖ ≥ r` (`i ≠ j`) and jets `(f_k, g_k, H_k)` with `H_k` symmetric
and `|f_k|, ‖g_k‖, ‖H_k‖ ≤ κ`, there is a smooth `F : E → ℝ` with `F(x_k) = f_k`,
`∇F(x_k) = g_k`, `∇²F(x_k) = H_k`, `|F| ≤ B` and `‖∇^j F‖ ≤ B` for `j ≤ 3`. -/
theorem exists_contDiff_interpolating_separated_jets [FiniteDimensional ℝ E] {r κ : ℝ}
    (hr : 0 < r) (hκ : 0 ≤ κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K : ℕ) (x : ℕ → E) (f : ℕ → ℝ) (g : ℕ → E) (H : ℕ → E [×2]→L[ℝ] ℝ),
      (∀ i ≤ K, ∀ j ≤ K, i ≠ j → r ≤ ‖x i - x j‖) →
      (∀ k ≤ K, ∀ v w, H k ![v, w] = H k ![w, v]) →
      (∀ k ≤ K, |f k| ≤ κ ∧ ‖g k‖ ≤ κ ∧ ‖H k‖ ≤ κ) →
      ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
        (∀ k ≤ K, F (x k) = f k ∧ gradient F (x k) = g k ∧ iteratedFDeriv ℝ 2 F (x k) = H k) ∧
        ∀ y, |F y| ≤ B ∧ ∀ j ≤ 3, ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
  obtain ⟨B, hB, hmain⟩ := exists_contDiff_interpolating_separated_taylorData (E := E) hr hκ
  refine ⟨B, hB, fun K x f g H hsep hH hbd => ?_⟩
  obtain ⟨F, hF, hjet, hFB⟩ := hmain K x (fun k => quadJet (f k) (g k) (H k)) hsep
    (fun k hk => quadJet_isSymm (hH k hk))
    (fun k hk => norm_quadJet_le (hbd k hk).1 (hbd k hk).2.1 (hbd k hk).2.2)
  refine ⟨F, hF, fun k hk => ⟨?_, ?_, hjet k hk 2 le_rfl⟩, fun y => ⟨?_, fun j hj => hFB j hj y⟩⟩
  · have := congrArg (fun A => A (fun _ => 0)) (hjet k hk 0 (Nat.zero_le _))
    simpa [quadJet, iteratedFDeriv_zero_apply] using this
  · have h1 : fderiv ℝ F (x k) = InnerProductSpace.toDual ℝ E (g k) := by
      ext v
      have := congrArg (fun A => A (fun _ => v)) (hjet k hk 1 (by norm_num))
      simpa [quadJet, iteratedFDeriv_one_apply, InnerProductSpace.toDual_apply_apply] using this
    rw [gradient, h1, LinearIsometryEquiv.symm_apply_apply]
  · have := hFB 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

end SeparatedJets

end Optimization
