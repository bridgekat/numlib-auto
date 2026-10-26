import Numlib.Optimization.Composite.RegularizedModel
import Numlib.Optimization.ModelBased.InexactTaylor
import Numlib.Optimization.Optimality.HighOrder

/-!
# The regularized model of high-order adaptive-regularization methods

The high-order adaptive-regularization methods ARqp ([cartis2022evaluation], §12.2.2) and
ARqpIDA/ARqpEDA (§13.1.4, §13.3.2) minimize the regularized `p`-th order model
`m(s) = regularizedModel D p σ s = T_p(s) + σ/(p+1)! ‖s‖^{p+1}`
built from derivative data `D` (the exact jet `ftaylorSeries ℝ f x` or an inexact jet), and measure
the approximate optimality of a trial step `s` through the model measure
`φ^δ_{m,j}(s) = taylorMeasure (ftaylorSeries ℝ m s) j δ S`. All statements here are for arbitrary
data, with an explicit error budget where the data are inexact; the exact-data lemmas of
Chapter 12 are the specializations with exact data and zero errors. The composite model of ARqpC
(§14.1) is treated in `Optimization.Composite.RegularizedModel`, whose lemmas with `h = 0` give the
model-decrease results here.

## Main results

* `Optimization.iteratedFDerivLipschitzOn_regularizedModel`,
  `Optimization.norm_iteratedFDeriv_regularizedModel_le`,
  `Optimization.abs_iteratedFDeriv_regularizedModel_apply_le`: Lemma 12.2.7;
* `Optimization.sub_regularizedModel_ge_of_taylorDecrement_ge`: Lemma 12.2.8, with the corollary
  `Optimization.taylorMeasure_regularizedModel_le_of_isMinOn` at a model minimizer;
* `Optimization.regularizedModel_decrease_ge_of_taylorDecrement_ge`: Lemma 13.1.10;
* `Optimization.exists_highOrderStep`: the existence part of Lemmas 12.2.9 and 13.1.12 (an
  admissible step with its optimality radii, from a global model minimizer; termination of the
  inner Algorithm 12.2.3 is not covered);
* `Optimization.taylorMeasure_regularizedModel_le_add`: (13.1.48)–(13.1.50) (exact versus inexact
  model measures);
* `Optimization.taylorMeasure_le_of_regularizedModel`: the measure transfer behind Lemma 12.2.11;
* `Optimization.sub_mul_lt_of_measure_comparison`: the radius inequality from an abstract one-step
  comparison, with instances `Optimization.radius_inequality_of_measure_gt` (Lemmas 12.2.11 and
  13.1.16 with an error budget) and `Optimization.radius_inequality_of_compositeTaylorMeasure_gt`
  (Lemma 14.1.7), in the corrected form with `ς - θ` (requiring `θ < ς`) instead of the printed
  `1 - θ`.

The step-length algebra that follows (Lemmas 12.2.12, 13.1.17, 14.1.8) is
`Optimization.pow_ge_of_measure_ineq` and `Optimization.norm_step_ge_of_measure_ineq`; the measure
at a local minimizer for orders `1, 2` (Theorem 12.1.4) is
`Optimization.taylorMeasure_eq_zero_of_isLocalMin`.
-/

open Set Metric Finset Filter
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Derivatives of the model (Lemma 12.2.7) -/

section Derivatives

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ L : ℝ}

/-- **Lemma 12.2.7, first part** ([cartis2022evaluation], (12.2.39)): for `σ ≥ 0` the `p`-th
derivative of the model is `σ`-Lipschitz (the `p`-th derivative of `T_p` is constant and that of
`‖s‖^{p+1}` is `(p+1)!`-Lipschitz, (B.4.3)). -/
theorem iteratedFDerivLipschitzOn_regularizedModel (hσ : 0 ≤ σ) :
    IteratedFDerivLipschitzOn (regularizedModel D p σ) p σ univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro a _ b _
  have hT := (D.iteratedFDerivLipschitzOn_taylorSum p) a (mem_univ a) b (mem_univ b)
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hT
  have hN := iteratedFDerivLipschitzOn_norm_pow (E := E) (r := p + 1) (by omega)
  rw [Nat.add_sub_cancel, iteratedFDerivLipschitzOn_iff] at hN
  rw [iteratedFDeriv_regularizedModel (Or.inl le_rfl), iteratedFDeriv_regularizedModel
    (Or.inl le_rfl), hT, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  calc σ / ((p + 1)! : ℝ) * ‖iteratedFDeriv ℝ p (fun y : E => ‖y‖ ^ (p + 1)) a -
        iteratedFDeriv ℝ p (fun y : E => ‖y‖ ^ (p + 1)) b‖
      ≤ σ / ((p + 1)! : ℝ) * (((p + 1)! : ℝ) * ‖a - b‖) :=
        mul_le_mul_of_nonneg_left (hN a (mem_univ a) b (mem_univ b)) (by positivity)
    _ = σ * ‖a - b‖ := by field_simp

/-- **Value remainder of the model** ([cartis2022evaluation], Lemma 12.2.7 with Corollary A.8.4):
for `σ ≥ 0`, `|m(s + d) - T_{m,p}(s, d)| ≤ σ/(p+1)! ‖d‖^{p+1}`. -/
theorem abs_regularizedModel_sub_taylorPolynomial_le (hσ : 0 ≤ σ) (s d : E) :
    |regularizedModel D p σ (s + d) - taylorPolynomial (regularizedModel D p σ) p s d| ≤
      σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) :=
  abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun _ _ => (contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt)
    (iteratedFDerivLipschitzOn_regularizedModel hσ) (mem_univ s) (mem_univ (s + d))

/-- **Lemma 12.2.7, (12.2.38)** ([cartis2022evaluation]): if `‖D_i‖ ≤ L` for `i = 2, …, p`
(`L ≥ 0`), `σ ≥ 0` and `‖s‖ ≤ 1`, then `‖∇^ℓ m(s)‖ ≤ 3 L + σ` for `ℓ = 2, …, p` (operator norm). -/
theorem norm_iteratedFDeriv_regularizedModel_le (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {ℓ : ℕ} (hℓ : ℓ ∈ Finset.Icc 2 p) {s : E}
    (hs : ‖s‖ ≤ 1) : ‖iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s‖ ≤ 3 * L + σ := by
  obtain ⟨hℓ2, hℓp⟩ := Finset.mem_Icc.1 hℓ
  rw [iteratedFDeriv_regularizedModel (Or.inl hℓp)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact D.norm_iteratedFDeriv_taylorSum_le_three_mul hL
      (fun i hi => hD i (Finset.mem_Icc.2 ⟨hℓ2.trans (Finset.mem_Icc.1 hi).1,
        (Finset.mem_Icc.1 hi).2⟩)) hs
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc σ / ((p + 1)! : ℝ) * ‖iteratedFDeriv ℝ ℓ (fun y : E => ‖y‖ ^ (p + 1)) s‖
        ≤ σ / ((p + 1)! : ℝ) * ((p + 1)! : ℝ) :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_norm_pow_le_factorial (by omega)
            (Or.inr (by omega)) hs) (by positivity)
      _ = σ := by field_simp

/-- **Lemma 12.2.7, diagonal form** ([cartis2022evaluation], (12.2.38)): under the hypotheses of
`norm_iteratedFDeriv_regularizedModel_le`, `|∇^ℓ m(s)[d]^ℓ| ≤ (3 L + σ) ‖d‖^ℓ` for every `d` and
`ℓ = 2, …, p`. -/
theorem abs_iteratedFDeriv_regularizedModel_apply_le (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {ℓ : ℕ} (hℓ : ℓ ∈ Finset.Icc 2 p) {s : E}
    (hs : ‖s‖ ≤ 1) (d : E) :
    |iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s (fun _ => d)| ≤ (3 * L + σ) * ‖d‖ ^ ℓ := by
  rw [← Real.norm_eq_abs]
  refine ((ftaylorSeries ℝ (regularizedModel D p σ) s).norm_apply_diagonal_le ℓ d).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_iteratedFDeriv_regularizedModel_le hL hD hσ hℓ hs)
    (by positivity)

end Derivatives

/-! ### Model decrease from a large decrement (Lemmas 12.2.8, 13.1.10) -/

section Decrease

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ L : ℝ}

/-- **Lemma 12.2.8** ([cartis2022evaluation]; the case `h = 0` of Lemma 14.1.2,
`compositeRegularizedModel_sub_ge_of_decrement_ge`). If `‖D_i‖ ≤ L` for `i = 2, …, p` (`L ≥ 0`),
`σ ≥ 0`, `‖s‖ ≤ 1`, `1 ≤ j ≤ p`, `0 ≤ δ ≤ 1` with `4 (3 L + σ) δ ≤ α` (the book's (12.2.41)), and
`‖d‖ ≤ δ` with `ΔT_{m,j}(s, d) ≥ α δ^j/j!` (12.2.42), then `m(s) - m(s + d) ≥ (α/2) δ^j/j!`
(12.2.43). -/
theorem sub_regularizedModel_ge_of_taylorDecrement_ge (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p)
    {s d : E} (hs : ‖s‖ ≤ 1) {α δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * (3 * L + σ) * δ ≤ α) (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ s - regularizedModel D p σ (s + d) := by
  have h := compositeRegularizedModel_sub_ge_of_decrement_ge
    (Dc := (0 : FormalMultilinearSeries ℝ E ℝ))
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl hD (fun _ _ => by simp) hσ hj hs
    hδ0 hδ1 (by simpa using hδα) hd (by rwa [compositeModelDecrement_zero_fun])
  simpa using h

/-- **Radii at a minimizer of the model** (the content of Lemma 12.2.9 of [cartis2022evaluation];
the case `h = 0` of `compositeTaylorMeasure_model_le_of_isMinOn`): under the hypotheses of
`sub_regularizedModel_ge_of_taylorDecrement_ge`, if `s` minimizes the model over `s + S`
(`m(s) ≤ m(s + d)` for `d ∈ S`, `0 ∈ S`), `α > 0` and `0 < δ ≤ 1` with `4 (3 L + σ) δ ≤ α`, then
`φ^δ_{m,j}(s) ≤ α δ^j/j!` (the measure over `closedBall 0 δ ∩ S`). -/
theorem taylorMeasure_regularizedModel_le_of_isMinOn (hL : 0 ≤ L)
    (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p)
    {s : E} (hs : ‖s‖ ≤ 1) {S : Set E} (hS0 : (0 : E) ∈ S)
    (hmin : ∀ d ∈ S, regularizedModel D p σ s ≤ regularizedModel D p σ (s + d)) {α δ : ℝ}
    (hα : 0 < α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδα : 4 * (3 * L + σ) * δ ≤ α) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤ α * δ ^ j / j ! := by
  have h := compositeTaylorMeasure_model_le_of_isMinOn
    (Dc := (0 : FormalMultilinearSeries ℝ E ℝ)) hasLipschitzConst_zero isSubadditive_zero rfl hL
    le_rfl hD (fun _ _ => by simp) hσ hj hs hS0 (by simpa using hmin) hα hδ0 hδ1
    (by simpa using hδα)
  simpa using h

/-- **Lemma 13.1.10** ([cartis2022evaluation]): the model decrease along a displacement with a
large Taylor decrement of the data. If `σ ≥ 0`, `j ≤ p`, `‖D_ℓ‖ ≤ L` for `ℓ = j + 1, …, p`,
`0 ≤ δ ≤ 1` with `4 max(L, σ) δ ≤ α` ((13.1.64)), `‖d‖ ≤ δ` and `ΔT_j(d) ≥ α δ^j/j!`, then
`m(0) - m(d) ≥ (α/2) δ^j/j!` ((13.1.65)). -/
theorem regularizedModel_decrease_ge_of_taylorDecrement_ge {j : ℕ} (hjp : j ≤ p) (hσ : 0 ≤ σ)
    (hD : ∀ ℓ ∈ Finset.Icc (j + 1) p, ‖D ℓ‖ ≤ L) {α δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * max L σ * δ ≤ α) {d : E} (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ D.taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ 0 - regularizedModel D p σ d := by
  set M := max L σ with hM
  have hM0 : 0 ≤ M := hσ.trans (le_max_right _ _)
  have hdiff : regularizedModel D p σ 0 - regularizedModel D p σ d =
      D.taylorDecrement j d - (D.taylorSum p d - D.taylorSum j d) -
        σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
    rw [regularizedModel_zero_right, regularizedModel_def, FormalMultilinearSeries.taylorDecrement,
      D.taylorSum_zero_right, D.taylorSum_zero_right]
    ring
  set S := ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ)
  have hhi : D.taylorSum p d - D.taylorSum j d ≤ M * S := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact D.norm_taylorSum_sub_taylorSum_le_of_norm_le hjp
      (fun ℓ hℓ => (hD ℓ hℓ).trans (le_max_left _ _)) hd
  have hreg : σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) ≤ M * (δ ^ (p + 1) / ((p + 1)! : ℝ)) := by
    rw [div_mul_eq_mul_div, mul_div_assoc']
    gcongr
    exact le_max_right _ _
  have hST : S + δ ^ (p + 1) / ((p + 1)! : ℝ) ≤ 2 * δ ^ (j + 1) / j ! := by
    have := sum_pow_div_factorial_Icc_succ_le hδ0 hδ1 j p
    rwa [Finset.sum_Icc_succ_top (by omega)] at this
  have h2 : M * (S + δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ M * (2 * δ ^ (j + 1) / j !) :=
    mul_le_mul_of_nonneg_left hST hM0
  refine half_mul_pow_div_factorial_le hδ0 hδα hdec ?_
  rw [hdiff]
  have e : 2 * M * δ ^ (j + 1) / (j ! : ℝ) = M * (2 * δ ^ (j + 1) / j !) := by ring
  linarith

end Decrease

/-! ### Existence of a step (Lemmas 12.2.9, 13.1.12) -/

section Step

variable {D : FormalMultilinearSeries ℝ E ℝ} {p q : ℕ} {σ L : ℝ}

/-- **Existence of an admissible high-order step** ([cartis2022evaluation], existence part of
Lemmas 12.2.9 and 13.1.12, for arbitrary data; termination of Algorithm 12.2.3 is not
covered). Let `E` be finite-dimensional, `1 ≤ p`, `q ≤ p`, `σ > 0`, `‖D_i‖ ≤ L` for
`i = 2, …, p` (`L ≥ 0`), `θ > 0`, `0 < ς ≤ 1` and `ε_ℓ > 0` for `ℓ = 1, …, q`.
Then there are a global minimizer `s` of the model `m = regularizedModel D p σ` (in particular
`m(s) ≤ m(0)`, (12.2.27)), radii `δs` and displacements `dm` such that `δs_ℓ ∈ (0, 1]`,
`δs_ℓ = 1` for `ℓ ≤ 2` ((12.2.44)), `δs_ℓ = min(1, ς θ ε_ℓ/(4 (3 L + σ)))` for `ℓ ≥ 3`
((12.2.45)), and either `‖s‖ ≥ 1` or, for every `ℓ = 1, …, q`, `dm_ℓ` is a `ς`-approximate
optimality displacement of the model at `s` with `ΔT_{m,ℓ}(s, dm_ℓ) ≤ ς θ ε_ℓ δs_ℓ^ℓ/ℓ!`
((12.2.29)). The step is a global minimizer, which the book notes is always acceptable; this
avoids the limiting argument of Algorithm 12.2.3. -/
theorem exists_highOrderStep [FiniteDimensional ℝ E] (hp : 1 ≤ p) (hq : q ≤ p) (hσ : 0 < σ)
    (hL : 0 ≤ L) (hD : ∀ i ∈ Finset.Icc 2 p, ‖D i‖ ≤ L) {θ ς : ℝ} (hθ : 0 < θ) (hς : 0 < ς)
    (hς1 : ς ≤ 1) {ε : ℕ → ℝ} (hε : ∀ ℓ ∈ Finset.Icc 1 q, 0 < ε ℓ) :
    ∃ s : E, ∃ δs : ℕ → ℝ, ∃ dm : ℕ → E, IsMinOn (regularizedModel D p σ) univ s ∧
      (∀ ℓ ∈ Finset.Icc 1 q, 0 < δs ℓ ∧ δs ℓ ≤ 1) ∧
      (∀ ℓ ∈ Finset.Icc 1 q, ℓ ≤ 2 → δs ℓ = 1) ∧
      (∀ ℓ ∈ Finset.Icc 3 q, δs ℓ = min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))) ∧
      (1 ≤ ‖s‖ ∨ ∀ ℓ ∈ Finset.Icc 1 q,
        IsApproxMeasureStep ((ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement ℓ)
          (δs ℓ) univ ς (dm ℓ) ∧
        (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement ℓ (dm ℓ) ≤
          ς * θ * ε ℓ * δs ℓ ^ ℓ / ℓ !) := by
  obtain ⟨s, hmin, -⟩ := exists_isMinOn_regularizedModel (D := D) (σ := σ) hσ hp
  set m := regularizedModel D p σ
  let δs : ℕ → ℝ := fun ℓ => if ℓ ≤ 2 then 1 else min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))
  -- maximizers of the model decrements
  have hdm : ∀ ℓ, ∃ d : E, 0 ≤ δs ℓ → d ∈ closedBall 0 (δs ℓ) ∩ univ ∧
      (ftaylorSeries ℝ m s).taylorDecrement ℓ d =
        taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ :=
    fun ℓ => by
      by_cases h : 0 ≤ δs ℓ
      · obtain ⟨d, hd, hdeq⟩ := exists_taylorMeasure_eq (ftaylorSeries ℝ m s) ℓ isClosed_univ
          (mem_univ 0) h
        exact ⟨d, fun _ => ⟨hd, hdeq⟩⟩
      · exact ⟨0, fun h' => absurd h' h⟩
  choose dm hdm using hdm
  have hK : 0 < 3 * L + σ := by positivity
  have hδs : ∀ ℓ ∈ Finset.Icc 1 q, 0 < δs ℓ ∧ δs ℓ ≤ 1 := fun ℓ hℓ => by
    have := hε ℓ hℓ
    by_cases h2 : ℓ ≤ 2
    · simp [δs, h2]
    · simp only [δs, h2, ite_false]
      exact ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  refine ⟨s, δs, dm, hmin, hδs, fun ℓ _ h2 => by simp [δs, h2], fun ℓ hℓ => ?_, ?_⟩
  · simp [δs, show ¬ ℓ ≤ 2 by have := (Finset.mem_Icc.1 hℓ).1; omega]
  by_cases hs : 1 ≤ ‖s‖
  · exact Or.inl hs
  refine Or.inr fun ℓ hℓ => ?_
  obtain ⟨hδ0, hδ1⟩ := hδs ℓ hℓ
  obtain ⟨hdmem, hdeq⟩ := hdm ℓ hδ0.le
  have hℓp : ℓ ≤ p := (Finset.mem_Icc.1 hℓ).2.trans hq
  have hφ0 := taylorMeasure_nonneg (ftaylorSeries ℝ m s) ℓ (mem_univ (0 : E)) hδ0.le
  -- the model measure is small
  have hφ : taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ ≤
      ς * θ * ε ℓ * δs ℓ ^ ℓ / ℓ ! := by
    have hεℓ := hε ℓ hℓ
    by_cases h2 : ℓ ≤ 2
    · have hcd : ContDiffAt ℝ ℓ m s :=
        (contDiff_regularizedModel (D := D) (σ := σ)).contDiffAt.of_le (by exact_mod_cast hℓp)
      rw [taylorMeasure_eq_zero_of_isLocalMin hcd (hmin.isLocalMin univ_mem)
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, h2⟩) hδ0.le]
      positivity
    · have hδsℓ : δs ℓ = min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ))) := by simp [δs, h2]
      have hδα : 4 * (3 * L + σ) * δs ℓ ≤ ς * θ * ε ℓ := by
        rw [hδsℓ]
        calc 4 * (3 * L + σ) * min 1 (ς * θ * ε ℓ / (4 * (3 * L + σ)))
            ≤ 4 * (3 * L + σ) * (ς * θ * ε ℓ / (4 * (3 * L + σ))) := by
              gcongr; exact min_le_right _ _
          _ = ς * θ * ε ℓ := by field_simp
      exact taylorMeasure_regularizedModel_le_of_isMinOn hL hD hσ.le
        (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hℓ).1, hℓp⟩) (not_le.1 hs).le (mem_univ 0)
        (fun d _ => hmin (mem_univ _)) (by positivity) hδ0 hδ1 hδα
  refine ⟨⟨hdmem, ?_⟩, ?_⟩
  · change ς * taylorMeasure (ftaylorSeries ℝ m s) ℓ (δs ℓ) univ ≤ _
    rw [hdeq]
    exact mul_le_of_le_one_left hφ0 hς1
  · rw [hdeq]; exact hφ

end Step

/-! ### Exact versus inexact model measures ((13.1.48)–(13.1.50)) -/

section Inexact

variable {D Dbar : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ} {err : ℕ → ℝ}

/-- The derivatives of order `ℓ ≤ p` of two regularized models with the same weight differ by
those of the Taylor sum of the difference of the data. -/
theorem iteratedFDeriv_regularizedModel_sub {ℓ : ℕ} (hℓ : ℓ ≤ p) (s : E) :
    iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s -
        iteratedFDeriv ℝ ℓ (regularizedModel Dbar p σ) s =
      iteratedFDeriv ℝ ℓ ((D - Dbar).taylorSum p) s := by
  rw [iteratedFDeriv_regularizedModel (Or.inl hℓ), iteratedFDeriv_regularizedModel (Or.inl hℓ),
    FormalMultilinearSeries.iteratedFDeriv_taylorSum_sub]
  abel

/-- **(13.1.48)–(13.1.49), first inequality** ([cartis2022evaluation]): if the data `Dbar`
approximate `D` with errors `err` up to order `p` (`JetApprox D Dbar p err`), then for `j ≤ p`,
`0 ∈ S` and `δ ≥ 0`, the model measures at any step `s` satisfy
`φ^δ_{m,j}(s) ≤ φ^δ_{m̄,j}(s) + ∑_{ℓ=1}^j δ^ℓ/ℓ! ∑_{i=ℓ}^p err_i ‖s‖^{i-ℓ}/(i-ℓ)!`, where
`m = regularizedModel D p σ` and `m̄ = regularizedModel Dbar p σ` (the regularization terms cancel).
By symmetry of `JetApprox` the same holds with `m` and `m̄` exchanged. -/
theorem taylorMeasure_regularizedModel_le_add (h : JetApprox D Dbar p err) {j : ℕ} (hjp : j ≤ p)
    (s : E) {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S +
        ∑ ℓ ∈ Finset.Icc 1 j,
          δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
  have habs := abs_taylorMeasure_sub_le (ftaylorSeries ℝ (regularizedModel D p σ) s)
    (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j hS0 hδ
  have hb : ∑ i ∈ Finset.Icc 1 j, ‖ftaylorSeries ℝ (regularizedModel D p σ) s i -
      ftaylorSeries ℝ (regularizedModel Dbar p σ) s i‖ * δ ^ i / i ! ≤
      ∑ ℓ ∈ Finset.Icc 1 j,
        δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
    refine sum_le_sum fun ℓ hℓ => ?_
    obtain ⟨hℓ1, hℓj⟩ := Finset.mem_Icc.1 hℓ
    have hn : ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
        ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ ≤
          ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by
      change ‖iteratedFDeriv ℝ ℓ (regularizedModel D p σ) s -
        iteratedFDeriv ℝ ℓ (regularizedModel Dbar p σ) s‖ ≤ _
      rw [iteratedFDeriv_regularizedModel_sub (hℓj.trans hjp)]
      refine ((D - Dbar).norm_iteratedFDeriv_taylorSum_le p ℓ s).trans
        (sum_le_sum fun i hi => ?_)
      have hi1 : i ∈ Finset.Icc 1 p :=
        Finset.mem_Icc.2 ⟨hℓ1.trans (Finset.mem_Icc.1 hi).1, (Finset.mem_Icc.1 hi).2⟩
      have : ‖(D - Dbar) i‖ ≤ err i := by
        change ‖D i - Dbar i‖ ≤ err i
        rw [norm_sub_rev]; exact h i hi1
      gcongr
    calc ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
          ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ * δ ^ ℓ / ℓ !
        = δ ^ ℓ / ℓ ! * ‖ftaylorSeries ℝ (regularizedModel D p σ) s ℓ -
          ftaylorSeries ℝ (regularizedModel Dbar p σ) s ℓ‖ := by ring
      _ ≤ _ := by gcongr
  linarith [(abs_le.1 habs).2]

/-- **(13.1.49)** ([cartis2022evaluation]): if moreover `err_i ≤ κ κs ‖s‖^{p-i+1}` for
`i = 1, …, p` (`κ, κs ≥ 0`; the accuracy requirement (13.1.46)), the excess is at most
`3 κ κs ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s‖^{p-ℓ+1}`. -/
theorem taylorMeasure_regularizedModel_le_add_of_stepAccuracy (h : JetApprox D Dbar p err)
    {κ κs : ℝ} (hκ : 0 ≤ κ) (hκs : 0 ≤ κs) {s : E}
    (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ κ * κs * ‖s‖ ^ (p - i + 1)) {j : ℕ} (hjp : j ≤ p)
    {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S +
        3 * κ * κs * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) := by
  refine (taylorMeasure_regularizedModel_le_add h hjp s hS0 hδ).trans (add_le_add le_rfl ?_)
  rw [mul_sum]
  refine sum_le_sum fun ℓ hℓ => ?_
  obtain ⟨hℓ1, hℓj⟩ := Finset.mem_Icc.1 hℓ
  have hin : ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) ≤
      3 * κ * κs * ‖s‖ ^ (p - ℓ + 1) := by
    calc ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
        ≤ ∑ i ∈ Finset.Icc ℓ p, κ * κs * ‖s‖ ^ (p - ℓ + 1) * ((1 : ℝ) ^ (i - ℓ) / (i - ℓ)!) := by
          refine sum_le_sum fun i hi => ?_
          obtain ⟨hℓi, hip⟩ := Finset.mem_Icc.1 hi
          have he := herr i (Finset.mem_Icc.2 ⟨hℓ1.trans hℓi, hip⟩)
          have hpow : ‖s‖ ^ (p - i + 1) * ‖s‖ ^ (i - ℓ) = ‖s‖ ^ (p - ℓ + 1) := by
            rw [← pow_add]; congr 1; omega
          calc err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
              ≤ κ * κs * ‖s‖ ^ (p - i + 1) * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := by gcongr
            _ = κ * κs * ‖s‖ ^ (p - ℓ + 1) * ((1 : ℝ) ^ (i - ℓ) / (i - ℓ)!) := by
              rw [one_pow, mul_assoc (κ * κs), hpow]; ring
      _ = κ * κs * ‖s‖ ^ (p - ℓ + 1) * ∑ i ∈ Finset.Icc ℓ p, (1 : ℝ) ^ (i - ℓ) / (i - ℓ)! :=
          (mul_sum _ _ _).symm
      _ ≤ κ * κs * ‖s‖ ^ (p - ℓ + 1) * (1 + 2 * 1) := by
          gcongr; exact sum_pow_div_factorial_le_one_add_two_mul zero_le_one le_rfl ℓ p
      _ = 3 * κ * κs * ‖s‖ ^ (p - ℓ + 1) := by ring
  calc δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
      ≤ δ ^ ℓ / ℓ ! * (3 * κ * κs * ‖s‖ ^ (p - ℓ + 1)) := by gcongr
    _ = 3 * κ * κs * (δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1)) := by ring

/-- **(13.1.50)** ([cartis2022evaluation]): if `‖s‖ ≤ 1`, `δ ≤ 1` and `err_i ≤ e` for
`i = 1, …, p`, the excess is at most `6 e`. -/
theorem taylorMeasure_regularizedModel_le_add_six_mul (h : JetApprox D Dbar p err) {e : ℝ}
    (he0 : 0 ≤ e) (he : ∀ i ∈ Finset.Icc 1 p, err i ≤ e) {s : E} (hs : ‖s‖ ≤ 1) {j : ℕ}
    (hjp : j ≤ p) {S : Set E} (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    taylorMeasure (ftaylorSeries ℝ (regularizedModel D p σ) s) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S + 6 * e := by
  refine (taylorMeasure_regularizedModel_le_add h hjp s hS0 hδ0).trans (add_le_add le_rfl ?_)
  calc ∑ ℓ ∈ Finset.Icc 1 j,
        δ ^ ℓ / ℓ ! * ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
      ≤ ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (3 * e) := by
        refine sum_le_sum fun ℓ hℓ => ?_
        have hℓ1 := (Finset.mem_Icc.1 hℓ).1
        have hin : ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) ≤ 3 * e := by
          calc ∑ i ∈ Finset.Icc ℓ p, err i * ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)
              ≤ ∑ i ∈ Finset.Icc ℓ p, e * (‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ)) := by
                refine sum_le_sum fun i hi => ?_
                rw [mul_div_assoc]
                gcongr
                exact he i (Finset.mem_Icc.2 ⟨hℓ1.trans (Finset.mem_Icc.1 hi).1,
                  (Finset.mem_Icc.1 hi).2⟩)
            _ = e * ∑ i ∈ Finset.Icc ℓ p, ‖s‖ ^ (i - ℓ) / ((i - ℓ)! : ℝ) := (mul_sum _ _ _).symm
            _ ≤ e * (1 + 2 * ‖s‖) := by
                gcongr; exact sum_pow_div_factorial_le_one_add_two_mul (norm_nonneg _) hs ℓ p
            _ ≤ 3 * e := by nlinarith
        gcongr
    _ = 3 * e * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ 3 * e * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ0 hδ1 j
    _ ≤ 6 * e := by nlinarith

end Inexact

/-! ### Measure transfer and the radius inequality (Lemmas 12.2.11, 13.1.16) -/

section Transfer

variable {f : E → ℝ} {p : ℕ} {σ L : ℝ} {C : Set E} {x s : E}

/-- **Measure transfer from the model to the function** ([cartis2022evaluation],
(12.2.53)–(12.2.56), exact data; the case `h = 0` of `compositeTaylorMeasure_le_of_step`). Let
`f` be `C^p` on a convex `C ∋ x, x + s` with `L`-Lipschitz `∇^p f` there (`L ≥ 0`), `σ ≥ 0`,
`m = regularizedModel (ftaylorSeries ℝ f x) p σ`, `j ≤ p`, feasible displacements `S ∋ 0` and
`δ ≥ 0`. Then
`φ^δ_{f,j}(x + s) ≤ φ^δ_{m,j}(s) + (L + σ) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s‖^{p-ℓ+1}/(p-ℓ+1)!`.
(The book's (12.2.56) writes `‖s_k‖^{p-j+1}` for `‖s_k‖^{p-ℓ+1}`.) -/
theorem taylorMeasure_le_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S ≤
      taylorMeasure (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s) j δ S +
        (L + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) := by
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  refine (taylorDecrement_le_add_of_regularizedModel hC hf hL hx hxs hσ hjp d).trans
    (add_le_add (taylorDecrement_le_taylorMeasure _ j hd) ?_)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) (by positivity)
  gcongr

/-- **The radius inequality, abstract form** (the common step of [cartis2022evaluation],
Lemmas 12.2.11, 13.1.16 and 14.1.7): if the measure `Φ` at the new iterate is not small,
`a ε δ^j/j! - e₀ < Φ`, a one-step comparison `Φ ≤ Φm + R` with a model measure `Φm` holds, and the
step approximately minimizes the model, `Φm ≤ θ ε δ^j/j!` ((12.2.29), (14.1.13)), then
`(a - θ) ε δ^j/j! < R + e₀`. The instances are `radius_inequality_of_measure_gt` (smooth, with
inexact data) and `radius_inequality_of_compositeTaylorMeasure_gt` (composite). -/
theorem sub_mul_lt_of_measure_comparison {Φ Φm R a θ ε δ e₀ : ℝ} {j : ℕ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ < Φ) (hcomp : Φ ≤ Φm + R)
    (h₂ : Φm ≤ θ * ε * δ ^ j / j !) : (a - θ) * ε * δ ^ j / j ! < R + e₀ := by
  have e : (a - θ) * ε * δ ^ j / (j ! : ℝ) =
      a * ε * δ ^ j / (j ! : ℝ) - θ * ε * δ ^ j / (j ! : ℝ) := by ring
  rw [e]
  linarith

/-- Dropping the factorials `(p - ℓ + 1)! ≥ 1` and enlarging the constant `A ≤ A'`. -/
private theorem mul_sum_le_mul_sum_of_factorial {A A' δ t : ℝ} {j p : ℕ} (hA : 0 ≤ A)
    (hAA' : A ≤ A') (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (t ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) ≤
      A' * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by
  have hT0 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by positivity
  calc A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (t ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))
      ≤ A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) hA
        gcongr
        exact div_le_self (by positivity)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
    _ ≤ A' * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1) := by gcongr

/-- **The radius inequality** ([cartis2022evaluation], Lemmas 12.2.11 and 13.1.16, with an
explicit error budget, corrected). Let `f` be `C^p` on a convex `C ∋ x, x + s` with
`Lp`-Lipschitz `∇^p f` there (`Lp ≥ 0`), `Dbar` approximate the jet of `f` at `x` with errors
`err_i ≤ κ κs ‖s‖^{p-i+1}` (`κ, κs ≥ 0`), `0 ≤ σ ≤ σmax`, `j ≤ p`, feasible displacements
`S ∋ 0` at `x + s`, and `δ ≥ 0`. Suppose
* (h₁) `a ε δ^j/j! - e₀ < φ^δ_{f,j}(x + s)` (the measure at the new iterate is not small), and
* (h₂) `φ^δ_{m̄,j}(s) ≤ θ ε δ^j/j!` for the inexact model `m̄ = regularizedModel Dbar p σ` (the
  step approximately minimizes the model at order `j`, (12.2.29)).

Then `(a - θ) ε δ^j/j! < (Lp + σmax + 3 κ κs) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s‖^{p-ℓ+1} + e₀`.

For exact ARqp (Lemma 12.2.11): `Dbar` the exact jet, `κ = 0`, `e₀ = 0` and `a = ς`: the failed
Step-1 test at `x + s` only certifies `φ > ς ε δ^j/j!`, so the printed factor `1 - θ` must read
`ς - θ` (and the analysis needs `θ < ς`). For ARqpIDA (Lemma 13.1.16) `κ = κ_{∇,max}`. -/
theorem radius_inequality_of_measure_gt (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    {Lp : ℝ} (hLp : IteratedFDerivLipschitzOn f p Lp C) (hLp0 : 0 ≤ Lp) (hx : x ∈ C)
    (hxs : x + s ∈ C) {Dbar : FormalMultilinearSeries ℝ E ℝ} {err : ℕ → ℝ}
    (happrox : JetApprox (ftaylorSeries ℝ f x) Dbar p err) {κ κs : ℝ} (hκ : 0 ≤ κ)
    (hκs : 0 ≤ κs) (herr : ∀ i ∈ Finset.Icc 1 p, err i ≤ κ * κs * ‖s‖ ^ (p - i + 1))
    {σmax : ℝ} (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ < taylorMeasure (ftaylorSeries ℝ f (x + s)) j δ S)
    (h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel Dbar p σ) s) j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lp + σmax + 3 * κ * κs) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) + e₀ := by
  have h3 := taylorMeasure_le_of_regularizedModel hC hf hLp hLp0 hx hxs hσ hjp hS0 hδ
  have h4 := taylorMeasure_regularizedModel_le_add_of_stepAccuracy (σ := σ) happrox hκ hκs herr
    hjp hS0 hδ
  have h5 := mul_sum_le_mul_sum_of_factorial (j := j) (p := p) (A' := Lp + σmax)
    (add_nonneg hLp0 hσ)
    (by linarith) hδ (norm_nonneg s)
  refine sub_mul_lt_of_measure_comparison h₁ ?_ h₂
  linarith

/-- **The radius inequality for composite problems** ([cartis2022evaluation], Lemma 14.1.7,
corrected). Under the hypotheses of `compositeTaylorMeasure_le_of_step` (with `0 ≤ σ ≤ σmax`),
suppose
* (h₁) `a ε δ^j/j! - e₀ < φ^δ_{w,j}(x + s)`, and
* (h₂) `φ^δ_{m̂,j}(s) ≤ θ ε δ^j/j!` for the composite model `m̂` built at `x` ((14.1.13)).

Then `(a - θ) ε δ^j/j! < (Lf + Lh Lc + σmax) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s‖^{p-ℓ+1} +
2 Lh Lc/(p+1)! ‖s‖^{p+1} + e₀`. For ARqpC, `a = ς` and `e₀ = 0`: this is (14.1.30) with `ς - θ`
for the printed `1 - θ` and the factor `2` on the last term (see
`compositeTaylorDecrement_le_of_step`). -/
theorem radius_inequality_of_compositeTaylorMeasure_gt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {c : E → F} {h : F → ℝ} {Lf Lc Lh σmax : ℝ} (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ} (hjp : j ≤ p) {S : Set E}
    (hS0 : (0 : E) ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) {ε a θ e₀ : ℝ}
    (h₁ : a * ε * δ ^ j / (j ! : ℝ) - e₀ <
      compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S)
    (h₂ : compositeTaylorMeasure
        (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
        (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S ≤
      θ * ε * δ ^ j / j !) :
    (a - θ) * ε * δ ^ j / j ! <
      (Lf + Lh * Lc + σmax) * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * ‖s‖ ^ (p - ℓ + 1) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + e₀ := by
  have h3 := compositeTaylorMeasure_le_of_step hC hf hc hLf hLc hLip hLf0 hLc0 hx hxs hσ hjp hS0 hδ
  have hLh := hLip.nonneg
  have h5 := mul_sum_le_mul_sum_of_factorial (j := j) (p := p) (A' := Lf + Lh * Lc + σmax)
    (by positivity : 0 ≤ Lf + Lh * Lc + σ) (by linarith) hδ (norm_nonneg s)
  refine sub_mul_lt_of_measure_comparison h₁ ?_ h₂
  linarith

end Transfer

end Optimization
