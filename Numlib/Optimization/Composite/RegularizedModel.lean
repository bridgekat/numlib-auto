import Numlib.Optimization.Composite.TaylorModel
import Numlib.Optimization.ModelBased.TaylorModel
import Numlib.Analysis.Calculus.MultivariateTaylor.DerivBound
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# The regularized composite model

For a composite objective `w = f + h ∘ c` ([cartis2022evaluation], §14.1), the ARqpC algorithm
(Algorithm 14.1.1) approximately minimizes the regularized composite model ((14.1.11))
`m̂(s) = T_{f,p}(s) + h(T_{c,p}(s)) + σ/(p+1)! ‖s‖^{p+1}`,
where `T_{f,p} = Df.taylorSum p`, `T_{c,p} = Dc.taylorSum p` are built from jets
`Df : FormalMultilinearSeries ℝ E ℝ`, `Dc : FormalMultilinearSeries ℝ E F` (exact jets of `f` and
`c` at the iterate, or any other data), and `h : F → ℝ` is Lipschitz and possibly nonsmooth. The
model's own optimality measure at a trial step `s` uses the decrement ((14.1.14))
`ΔT_{m̂,j}(s, d)`, the composite decrement of the jets of
`s ↦ T_{f,p}(s) + σ/(p+1)! ‖s‖^{p+1}` and of `T_{c,p}` at `s`.

With `h = 0` everything reduces to the regularized Taylor model `Optimization.regularizedModel` of
ARqp (§12.2.2): Lemma 12.2.8 (`Optimization.sub_regularizedModel_ge_of_taylorDecrement_ge`) is
derived from Lemma 14.1.2 here, and the smooth part of Lemma 14.1.7 below
(`Optimization.taylorDecrement_le_add_of_regularizedModel`) is the measure transfer of
Lemma 12.2.11.

## Main definitions

* `Optimization.compositeRegularizedModel Df Dc h p σ`: the model `m̂` (14.1.11);
* `Optimization.compositeModelDecrement Df Dc h p σ j s d`: the decrement `ΔT_{m̂,j}(s, d)` of
  (14.1.14).

## Main results

* `Optimization.le_compositeTaylorDecrement_of_compositeRegularizedModel_le`: Lemma 14.1.5;
* `Optimization.compositeRegularizedModel_sub_ge_of_decrement_ge`: Lemma 14.1.2 (model decrease
  from a large model decrement), with its corollary at a model minimizer
  `Optimization.compositeTaylorMeasure_model_le_of_isMinOn` (the radii of Lemma 14.1.3);
* `Optimization.exists_isMinOn_compositeRegularizedModel`: the model has global minimizers on
  closed feasible sets in finite dimension;
* `Optimization.exists_radius_of_isMinOn_compositeRegularizedModel_zero`: Lemma 14.1.4 (if `0`
  globally minimizes the model, the composite measures are small for small radii);
* `Optimization.compositeTaylorDecrement_le_of_step`,
  `Optimization.compositeTaylorMeasure_le_of_step`: the one-step comparison of measures behind
  Lemma 14.1.7, with the corrected factor `2` on the `‖s‖^{p+1}` term;
  `Optimization.taylorDecrement_le_add_of_regularizedModel` is its smooth part.

Constants: `Lf`, `Lc` bound the operator norms `‖Df_i‖`, `‖Dc_i‖` (`i = 2, …, p`), and `Lc` is the
Lipschitz constant of `∇^p c` in operator norm; the book's componentwise constants for
`c : ℝⁿ → ℝᵐ` give `Lc = √m L_{c,p}` (see
`ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`), whence its `√m` factors.
-/

open Set Metric Finset Filter Topology
open scoped Nat

namespace Optimization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The jet of the regularized model -/

section ModelJet

variable (D : FormalMultilinearSeries ℝ E ℝ) (p : ℕ) (σ : ℝ)

/-- The Taylor sum of order `j ≤ p` of the regularized model at `s` splits into those of the
Taylor sum `T_p` and of the regularization term `‖·‖^{p+1}`. -/
theorem taylorSum_ftaylorSeries_regularizedModel {j : ℕ} (hj : j ≤ p) (s d : E) :
    (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorSum j d =
      (ftaylorSeries ℝ (D.taylorSum p) s).taylorSum j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d := by
  simp only [FormalMultilinearSeries.taylorSum_def, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p := (Nat.lt_succ_iff.1 (mem_range.1 hi)).trans hj
  simp only [ftaylorSeries, iteratedFDeriv_regularizedModel (Or.inl hi'),
    add_apply, smul_apply, smul_eq_mul]
  ring

/-- The Taylor decrement of order `j ≤ p` of the regularized model at `s`. -/
theorem taylorDecrement_ftaylorSeries_regularizedModel {j : ℕ} (hj : j ≤ p) (s d : E) :
    (ftaylorSeries ℝ (regularizedModel D p σ) s).taylorDecrement j d =
      (ftaylorSeries ℝ (D.taylorSum p) s).taylorDecrement j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorDecrement j d := by
  simp only [FormalMultilinearSeries.taylorDecrement,
    taylorSum_ftaylorSeries_regularizedModel D p σ hj]
  ring

end ModelJet

/-! ### The model -/

section Model

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (p : ℕ) (σ : ℝ)

/-- The regularized composite model of ARqpC ([cartis2022evaluation], (14.1.11)):
`m̂(s) = T_{f,p}(s) + h(T_{c,p}(s)) + σ/(p+1)! ‖s‖^{p+1}`, with `T_{f,p} = Df.taylorSum p` and
`T_{c,p} = Dc.taylorSum p`. -/
noncomputable def compositeRegularizedModel (s : E) : ℝ :=
  regularizedModel Df p σ s + h (Dc.taylorSum p s)

/-- Unfolding lemma for `compositeRegularizedModel`. -/
theorem compositeRegularizedModel_def (s : E) :
    compositeRegularizedModel Df Dc h p σ s = regularizedModel Df p σ s + h (Dc.taylorSum p s) :=
  rfl

/-- The model at the zero step: `m̂(0) = T_{f,p}(0) + h(T_{c,p}(0))`, i.e. `w(x)` for exact jets. -/
@[simp]
theorem compositeRegularizedModel_zero_right :
    compositeRegularizedModel Df Dc h p σ 0 = Df.taylorSum p 0 + h (Dc.taylorSum p 0) := by
  simp [compositeRegularizedModel_def]

/-- With `h = 0` the composite model is the regularized Taylor model. -/
@[simp]
theorem compositeRegularizedModel_zero_fun :
    compositeRegularizedModel Df Dc (0 : F → ℝ) p σ = regularizedModel Df p σ := by
  funext s
  simp [compositeRegularizedModel_def]

/-- The composite model is continuous when `h` is. -/
theorem continuous_compositeRegularizedModel (hc : Continuous h) :
    Continuous (compositeRegularizedModel Df Dc h p σ) :=
  (continuous_regularizedModel Df p σ).add (hc.comp (Dc.contDiff_taylorSum p (n := 0)).continuous)

/-- The decrement `ΔT_{m̂,j}(s, d) = T_{m̂,j}(s, 0) - T_{m̂,j}(s, d)` of the composite model at a
trial step `s` ([cartis2022evaluation], (14.1.14)): the composite decrement of the jets at `s` of
the smooth part `s ↦ T_{f,p}(s) + σ/(p+1)! ‖s‖^{p+1}` and of `T_{c,p}`. Its supremum over
`d ∈ closedBall 0 δ ∩ S` is the model measure `φ^δ_{m̂,j}(s)`. -/
noncomputable def compositeModelDecrement (j : ℕ) (s d : E) : ℝ :=
  compositeTaylorDecrement (ftaylorSeries ℝ (regularizedModel Df p σ) s)
    (ftaylorSeries ℝ (Dc.taylorSum p) s) h j d

/-- Unfolding lemma for `compositeModelDecrement`. -/
theorem compositeModelDecrement_def (j : ℕ) (s d : E) :
    compositeModelDecrement Df Dc h p σ j s d =
      compositeTaylorDecrement (ftaylorSeries ℝ (regularizedModel Df p σ) s)
        (ftaylorSeries ℝ (Dc.taylorSum p) s) h j d := rfl

/-- With `h = 0` the model decrement is the Taylor decrement of the regularized model at `s`. -/
@[simp]
theorem compositeModelDecrement_zero_fun (j : ℕ) (s : E) :
    compositeModelDecrement Df Dc (0 : F → ℝ) p σ j s =
      (ftaylorSeries ℝ (regularizedModel Df p σ) s).taylorDecrement j := by
  funext d
  rw [compositeModelDecrement_def, compositeTaylorDecrement_zero_fun]

/-- **The displayed formula (14.1.14)**: for `j ≤ p`,
`ΔT_{m̂,j}(s, d) = ΔT_{T_{f,p},j}(s, d) + σ/(p+1)! ΔT_{‖·‖^{p+1},j}(s, d) + h(T_{c,p}(s)) -
h(T_{T_{c,p},j}(s, d))`, where `ΔT_{g,j}(s, d) = -∑_{ℓ=1}^j (1/ℓ!) ∇^ℓ g(s)[d]^ℓ`. -/
theorem compositeModelDecrement_eq {j : ℕ} (hj : j ≤ p) (s d : E) :
    compositeModelDecrement Df Dc h p σ j s d =
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorDecrement j d +
        σ / ((p + 1)! : ℝ) *
          (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorDecrement j d +
        (h (Dc.taylorSum p s) - h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)) := by
  rw [compositeModelDecrement_def, compositeTaylorDecrement_eq,
    taylorDecrement_ftaylorSeries_regularizedModel Df p σ hj]
  have : (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j 0 = Dc.taylorSum p s :=
    taylorPolynomial_zero_right (Dc.taylorSum p) j s
  rw [this]

variable {Df Dc h p σ}

/-- **Lemma 14.1.5** ([cartis2022evaluation], (14.1.25)): `m̂(s) ≤ m̂(0)` gives
`ΔT_{w,p}(s) ≥ σ/(p+1)! ‖s‖^{p+1}`. -/
theorem le_compositeTaylorDecrement_of_compositeRegularizedModel_le {s : E}
    (hs : compositeRegularizedModel Df Dc h p σ s ≤ compositeRegularizedModel Df Dc h p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ compositeTaylorDecrement Df Dc h p s := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def,
    regularizedModel_def] at hs
  rw [compositeTaylorDecrement]
  linarith

/-- **Lemma 14.1.5**, strict form: `m̂(s) < m̂(0)` gives `ΔT_{w,p}(s) > σ/(p+1)! ‖s‖^{p+1}`. -/
theorem lt_compositeTaylorDecrement_of_compositeRegularizedModel_lt {s : E}
    (hs : compositeRegularizedModel Df Dc h p σ s < compositeRegularizedModel Df Dc h p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) < compositeTaylorDecrement Df Dc h p s := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def,
    regularizedModel_def] at hs
  rw [compositeTaylorDecrement]
  linarith

end Model

/-! ### Model decrease from a large model decrement (Lemma 14.1.2) -/

section Decrease

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lf Lc Lh : ℝ}

/-- **Core estimate of Lemma 14.1.2** ([cartis2022evaluation], (14.1.20)–(14.1.23)). Let `h` be
subadditive with `h 0 = 0` and Lipschitz constant `Lh`, `‖Df_i‖ ≤ Lf`, `‖Dc_i‖ ≤ Lc` for
`i = 2, …, p`, `σ ≥ 0`, `1 ≤ j ≤ p`, `‖s‖ ≤ 1` and `‖d‖ ≤ δ ≤ 1`. Then the model decrease along `d`
differs from the model decrement by at most `2 (3 (Lf + Lh Lc) + σ) δ^{j+1}/j!`:
`m̂(s) - m̂(s + d) ≥ ΔT_{m̂,j}(s, d) - 2 (3 (Lf + Lh Lc) + σ) δ^{j+1}/j!`. -/
theorem sub_compositeRegularizedModel_ge (hLip : HasLipschitzConst h Lh) (hh : IsSubadditive h)
    (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E} (hs : ‖s‖ ≤ 1) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ) :
    compositeModelDecrement Df Dc h p σ j s d -
        2 * (3 * (Lf + Lh * Lc) + σ) * δ ^ (j + 1) / j ! ≤
      compositeRegularizedModel Df Dc h p σ s - compositeRegularizedModel Df Dc h p σ (s + d) := by
  obtain ⟨hj1, hjp⟩ := Finset.mem_Icc.1 hj
  have hLh := hLip.nonneg
  have hc : 0 ≤ σ / ((p + 1)! : ℝ) := by positivity
  have hcfac : σ / ((p + 1)! : ℝ) * ((p + 1)! : ℝ) = σ := by field_simp
  have hhigh : ∀ ℓ ∈ Finset.Icc (j + 1) p, ∀ i ∈ Finset.Icc ℓ p, i ∈ Finset.Icc 2 p :=
    fun ℓ hℓ i hi => by
      have := Finset.mem_Icc.1 hℓ; have := Finset.mem_Icc.1 hi
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  -- the polynomial parts are their own Taylor polynomials at `s`
  have hA := Df.taylorSum_add_eq_taylorPolynomial p s d
  have hB := Dc.taylorSum_add_eq_taylorPolynomial p s d
  -- the regularization term: Taylor remainder (B.4.3)
  have hNrem : ‖s + d‖ ^ (p + 1) -
      (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum p d ≤ δ ^ (p + 1) := by
    have := abs_norm_pow_sub_taylorPolynomial_le (E := E) (r := p + 1) (by omega) s d
    rw [Nat.add_sub_cancel] at this
    exact (le_abs_self _).trans (this.trans (pow_le_pow_left₀ (norm_nonneg _) hd _))
  -- the terms of orders `j + 1, …, p`
  have hAhi : (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum p d -
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum j d ≤
        3 * Lf * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => Df.norm_iteratedFDeriv_taylorSum_le_three_mul hLf
        (fun i hi => hDf i (hhigh ℓ hℓ i hi)) hs) hd
  have hBhi : ‖(ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d -
      (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d‖ ≤
        3 * Lc * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) :=
    FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => Dc.norm_iteratedFDeriv_taylorSum_le_three_mul hLc
        (fun i hi => hDc i (hhigh ℓ hℓ i hi)) hs) hd
  have hNhi : (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum p d -
      (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d ≤
        ((p + 1)! : ℝ) * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine FormalMultilinearSeries.norm_taylorSum_sub_taylorSum_le_of_norm_le _ hjp
      (fun ℓ hℓ => ?_) hd
    have := Finset.mem_Icc.1 hℓ
    exact norm_iteratedFDeriv_norm_pow_le_factorial (by omega) (Or.inr (by omega)) hs
  -- subadditivity of `h` separates the orders `≤ j` from the orders `> j`
  have hsub : h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d) -
      h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d) ≤
        Lh * (3 * Lc * ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ)) := by
    have := hh.sub_le_mul_norm h0 hLip ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)
      ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d -
        (ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum j d)
    rw [add_sub_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_left hBhi hLh)
  -- the model decrement and the model values
  have hdec := compositeModelDecrement_eq Df Dc h p σ hjp s d
  simp only [FormalMultilinearSeries.taylorDecrement] at hdec
  have hz : ∀ (G : Type _) [NormedAddCommGroup G] [NormedSpace ℝ G] (g : E → G),
      (ftaylorSeries ℝ g s).taylorSum j 0 = g s := fun _ _ _ g => taylorPolynomial_zero_right g j s
  rw [hz, hz] at hdec
  have hms : compositeRegularizedModel Df Dc h p σ s =
      Df.taylorSum p s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + h (Dc.taylorSum p s) := rfl
  have hmsd : compositeRegularizedModel Df Dc h p σ (s + d) =
      (ftaylorSeries ℝ (Df.taylorSum p) s).taylorSum p d +
        σ / ((p + 1)! : ℝ) * ‖s + d‖ ^ (p + 1) +
          h ((ftaylorSeries ℝ (Dc.taylorSum p) s).taylorSum p d) := by
    rw [compositeRegularizedModel_def, regularizedModel_def, hA, hB]; rfl
  -- the sum bound (A.33)
  set S := ∑ ℓ ∈ Finset.Icc (j + 1) p, δ ^ ℓ / (ℓ ! : ℝ) with hS
  set K := 3 * (Lf + Lh * Lc) + σ with hK
  have hST : S + δ ^ (p + 1) / ((p + 1)! : ℝ) ≤ 2 * δ ^ (j + 1) / j ! := by
    have := sum_pow_div_factorial_Icc_succ_le hδ0 hδ1 j p
    rwa [Finset.sum_Icc_succ_top (by omega)] at this
  have hK0 : σ ≤ K := by rw [hK]; nlinarith
  have hT0 : 0 ≤ δ ^ (p + 1) / ((p + 1)! : ℝ) := by positivity
  have h1 : σ * (δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ K * (δ ^ (p + 1) / ((p + 1)! : ℝ)) :=
    mul_le_mul_of_nonneg_right hK0 hT0
  have h2 : K * (S + δ ^ (p + 1) / ((p + 1)! : ℝ)) ≤ K * (2 * δ ^ (j + 1) / j !) :=
    mul_le_mul_of_nonneg_left hST (hσ.trans hK0)
  have h3 : σ / ((p + 1)! : ℝ) *
      (‖s + d‖ ^ (p + 1) - (ftaylorSeries ℝ (fun y : E => ‖y‖ ^ (p + 1)) s).taylorSum j d) ≤
        σ / ((p + 1)! : ℝ) * (δ ^ (p + 1) + ((p + 1)! : ℝ) * S) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have h4 : σ / ((p + 1)! : ℝ) * (δ ^ (p + 1) + ((p + 1)! : ℝ) * S) =
      σ * (δ ^ (p + 1) / ((p + 1)! : ℝ)) + σ * S := by
    rw [mul_add, ← mul_assoc, hcfac]; ring
  rw [hdec, hms, hmsd]
  have e : 2 * K * δ ^ (j + 1) / j ! = K * (2 * δ ^ (j + 1) / j !) := by ring
  rw [e]
  nlinarith

/-- **Lemma 14.1.2** ([cartis2022evaluation]; for `h = 0` Lemma 12.2.8): model decrease from a
large model decrement. Let `h` be subadditive with `h 0 = 0` and Lipschitz constant `Lh`,
`‖Df_i‖ ≤ Lf`, `‖Dc_i‖ ≤ Lc` for `i = 2, …, p` (`Lf, Lc ≥ 0`), `σ ≥ 0`, `‖s‖ ≤ 1`, `1 ≤ j ≤ p`,
`0 ≤ δ ≤ 1` with `4 (3 (Lf + Lh Lc) + σ) δ ≤ α`, and `‖d‖ ≤ δ`. If
`ΔT_{m̂,j}(s, d) ≥ α δ^j/j!` (14.1.18), then `m̂(s) - m̂(s + d) ≥ (α/2) δ^j/j!` (14.1.19).

With `L_w = Lf + Lh Lc` the radius condition is the book's (14.1.17)
`δ ≤ min(1, α/(4 (3 L_w + σ)))`. -/
theorem compositeRegularizedModel_sub_ge_of_decrement_ge (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s d : E} (hs : ‖s‖ ≤ 1) {α δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδα : 4 * (3 * (Lf + Lh * Lc) + σ) * δ ≤ α) (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ compositeModelDecrement Df Dc h p σ j s d) :
    α / 2 * δ ^ j / j ! ≤
      compositeRegularizedModel Df Dc h p σ s - compositeRegularizedModel Df Dc h p σ (s + d) := by
  exact half_mul_pow_div_factorial_le hδ0 hδα hdec
    (sub_compositeRegularizedModel_ge hLip hh h0 hLf hLc hDf hDc hσ hj hs hδ0 hδ1 hd)

/-- **Radii at a model minimizer** (the content of Lemma 14.1.3 of [cartis2022evaluation], and
of Lemma 12.2.9 for `h = 0`): under the hypotheses of
`compositeRegularizedModel_sub_ge_of_decrement_ge`, if `s` minimizes the model over the feasible
steps `s + S` (`m̂(s) ≤ m̂(s + d)` for `d ∈ S`), with `0 ∈ S`, `α > 0` and
`0 < δ ≤ 1`, `4 (3 (Lf + Lh Lc) + σ) δ ≤ α`, then the model measure at `s` is small:
`φ^δ_{m̂,j}(s) ≤ α δ^j/j!`. -/
theorem compositeTaylorMeasure_model_le_of_isMinOn (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hDf : ∀ i ∈ Finset.Icc 2 p, ‖Df i‖ ≤ Lf) (hDc : ∀ i ∈ Finset.Icc 2 p, ‖Dc i‖ ≤ Lc)
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {s : E} (hs : ‖s‖ ≤ 1) {S : Set E}
    (hS0 : (0 : E) ∈ S)
    (hmin : ∀ d ∈ S, compositeRegularizedModel Df Dc h p σ s ≤
      compositeRegularizedModel Df Dc h p σ (s + d))
    {α δ : ℝ} (hα : 0 < α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδα : 4 * (3 * (Lf + Lh * Lc) + σ) * δ ≤ α) :
    compositeTaylorMeasure (ftaylorSeries ℝ (regularizedModel Df p σ) s)
      (ftaylorSeries ℝ (Dc.taylorSum p) s) h j δ S ≤ α * δ ^ j / j ! := by
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ0.le, hS0⟩ fun d hd => ?_
  by_contra hlt
  push Not at hlt
  have hdec := compositeRegularizedModel_sub_ge_of_decrement_ge hLip hh h0 hLf hLc hDf hDc hσ hj
    hs hδ0.le hδ1 hδα (mem_closedBall_zero_iff.1 hd.1) hlt.le
  have hpos : 0 < α / 2 * δ ^ j / j ! := by positivity
  linarith [hmin d hd.2]

end Decrease

/-! ### Minimizers of the model (Lemma 14.1.4) -/

section Minimizer

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lh : ℝ}

/-- **Pointwise bound behind Lemma 14.1.4** ([cartis2022evaluation], Appendix B): if
`m̂(0) ≤ m̂(d)`, `h` is subadditive with `h 0 = 0` and Lipschitz constant `Lh`, and `j ≤ p`, then
`ΔT_{w,j}(d) ≤ ∑_{ℓ=j+1}^p (‖Df_ℓ‖ + Lh ‖Dc_ℓ‖) ‖d‖^ℓ/ℓ! + σ/(p+1)! ‖d‖^{p+1}`. -/
theorem compositeTaylorDecrement_le_of_compositeRegularizedModel_le
    (hLip : HasLipschitzConst h Lh) (hh : IsSubadditive h) (h0 : h 0 = 0) {j : ℕ} (hjp : j ≤ p)
    {d : E}
    (hd : compositeRegularizedModel Df Dc h p σ 0 ≤ compositeRegularizedModel Df Dc h p σ d) :
    compositeTaylorDecrement Df Dc h j d ≤
      ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! +
        σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
  rw [compositeRegularizedModel_zero_right, compositeRegularizedModel_def, regularizedModel_def,
    Df.taylorSum_zero_right, Dc.taylorSum_zero_right] at hd
  rw [compositeTaylorDecrement, Df.taylorSum_zero_right, Dc.taylorSum_zero_right]
  have h1 : Df.taylorSum p d - Df.taylorSum j d ≤
      ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Df ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact Df.norm_taylorSum_sub_taylorSum_le hjp d
  have h2 : h (Dc.taylorSum p d) - h (Dc.taylorSum j d) ≤
      Lh * ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Dc ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    have := hh.sub_le_mul_norm h0 hLip (Dc.taylorSum j d) (Dc.taylorSum p d - Dc.taylorSum j d)
    rw [add_sub_cancel] at this
    exact this.trans (mul_le_mul_of_nonneg_left (Dc.norm_taylorSum_sub_taylorSum_le hjp d)
      hLip.nonneg)
  have he : ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! =
      ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Df ℓ‖ * ‖d‖ ^ ℓ / ℓ ! +
        Lh * ∑ ℓ ∈ Finset.Icc (j + 1) p, ‖Dc ℓ‖ * ‖d‖ ^ ℓ / ℓ ! := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [he]
  linarith

/-- **Lemma 14.1.4** ([cartis2022evaluation]; for `h = 0` Lemma 12.2.10): if `0` globally
minimizes the composite model over the feasible displacements `T ∋ 0`, `h` is subadditive with
`h 0 = 0` and Lipschitz, `σ ≥ 0` and `j ≤ p`, then for every `ε > 0` there is `δ₀ ∈ (0, 1]` such
that `φ^δ_{w,j} ≤ ε δ^j/j!` for every `δ ∈ [0, δ₀]`: the iterate is an `(ε, δ)`-approximate
minimizer of order `j` (14.1.9) for all small radii. -/
theorem exists_radius_of_isMinOn_compositeRegularizedModel_zero (hLip : HasLipschitzConst h Lh)
    (hh : IsSubadditive h) (h0 : h 0 = 0) (hσ : 0 ≤ σ) {T : Set E} (hT0 : (0 : E) ∈ T)
    (hmin : IsMinOn (compositeRegularizedModel Df Dc h p σ) T 0) {j : ℕ} (hjp : j ≤ p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ₀, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ, 0 ≤ δ → δ ≤ δ₀ →
      compositeTaylorMeasure Df Dc h j δ T ≤ ε * δ ^ j / j ! := by
  set K := ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) +
    σ / ((p + 1)! : ℝ) with hK
  have hLh := hLip.nonneg
  have hK0 : 0 ≤ K := by positivity
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  refine ⟨min 1 (ε / ((j ! : ℝ) * (K + 1))), lt_min one_pos (by positivity), min_le_left _ _,
    fun δ hδ0 hδ => ?_⟩
  have hδ1 : δ ≤ 1 := hδ.trans (min_le_left _ _)
  have hδε : δ ≤ ε / ((j ! : ℝ) * (K + 1)) := hδ.trans (min_le_right _ _)
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ0, hT0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  have hpowle : ∀ ℓ, j + 1 ≤ ℓ → ‖d‖ ^ ℓ ≤ δ ^ (j + 1) := fun ℓ hℓ =>
    (pow_le_pow_left₀ (norm_nonneg _) hdδ ℓ).trans (pow_le_pow_of_le_one hδ0 hδ1 hℓ)
  have hb := compositeTaylorDecrement_le_of_compositeRegularizedModel_le hLip hh h0 hjp
    (isMinOn_iff.1 hmin d hd.2)
  have hsum : ∑ ℓ ∈ Finset.Icc (j + 1) p, (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / ℓ ! +
      σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) ≤ K * δ ^ (j + 1) := by
    rw [hK, add_mul, sum_mul]
    refine add_le_add (sum_le_sum fun ℓ hℓ => ?_) ?_
    · have ha : 0 ≤ (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) := by positivity
      calc (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) * ‖d‖ ^ ℓ / (ℓ ! : ℝ)
          = (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) * ‖d‖ ^ ℓ := by ring
        _ ≤ (‖Df ℓ‖ + Lh * ‖Dc ℓ‖) / (ℓ ! : ℝ) * δ ^ (j + 1) :=
          mul_le_mul_of_nonneg_left (hpowle ℓ (Finset.mem_Icc.1 hℓ).1) ha
    · gcongr
      exact hpowle (p + 1) (by omega)
  have hKδ : K * δ ≤ ε / j ! := by
    calc K * δ ≤ (K + 1) * δ := by nlinarith
      _ ≤ (K + 1) * (ε / ((j ! : ℝ) * (K + 1))) := by gcongr
      _ = ε / j ! := by field_simp
  calc compositeTaylorDecrement Df Dc h j d ≤ K * δ ^ (j + 1) := hb.trans hsum
    _ = K * δ * δ ^ j := by ring
    _ ≤ ε / j ! * δ ^ j := by gcongr
    _ = ε * δ ^ j / j ! := by ring

/-- The jet at `0` of the regularized model is `D` up to order `p` (symmetric `D`): the
regularization term `‖s‖^{p+1}` is flat to order `p` at `0`. -/
theorem ftaylorSeries_regularizedModel_zero (hD : Df.IsSymm p) {i : ℕ} (hi : i ≤ p) :
    ftaylorSeries ℝ (regularizedModel Df p σ) 0 i = Df i := by
  have hlt : ((i : ℕ) : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hi
  change iteratedFDeriv ℝ i (regularizedModel Df p σ) 0 = Df i
  rw [iteratedFDeriv_regularizedModel (Or.inl hi), NormPowIteratedFDeriv.norm_pow_eq_normRpow,
    iteratedFDeriv_normRpow_zero hlt, smul_zero, add_zero]
  exact FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero hD hi

/-- **The composite model at the zero step** ((12.2.49) for `h = 0`): for symmetric data and
`j ≤ p`, the generalized Taylor decrement of order `j` of the model at `0` is that of the data,
`ΔT_{m̂,j}(0, d) = ΔT_{w,j}(d)`. -/
theorem compositeModelDecrement_zero_left (hDf : Df.IsSymm p) (hDc : Dc.IsSymm p) {j : ℕ}
    (hjp : j ≤ p) :
    compositeModelDecrement Df Dc h p σ j 0 = compositeTaylorDecrement Df Dc h j := by
  funext d
  rw [compositeModelDecrement_def, compositeTaylorDecrement, compositeTaylorDecrement,
    FormalMultilinearSeries.taylorSum_congr (D := ftaylorSeries ℝ (regularizedModel Df p σ) 0)
      (D' := Df) fun i hi => ftaylorSeries_regularizedModel_zero hDf (hi.trans hjp),
    FormalMultilinearSeries.taylorSum_congr (D := ftaylorSeries ℝ (Dc.taylorSum p) 0)
      (D' := Dc) fun i hi =>
        FormalMultilinearSeries.iteratedFDeriv_taylorSum_zero hDc (hi.trans hjp)]

/-- **Lemma 14.1.4, first part** ([cartis2022evaluation]; with Lemma 14.1.1): if `h` is convex and
Lipschitz, the data are symmetric, `p ≥ 1`, the feasible displacements `T ∋ 0` form a convex set,
and `0` locally minimizes the composite model on `T`, then `ΔT_{w,1}(d) ≤ 0` for every `d ∈ T`;
so the first-order measure vanishes and ARqpC cannot stop in Step 2 when `q = 1`. -/
theorem compositeTaylorDecrement_one_nonpos_of_isLocalMinOn_compositeRegularizedModel
    (hLip : HasLipschitzConst h Lh) (hconv : ConvexOn ℝ univ h) (hDf : Df.IsSymm p)
    (hDc : Dc.IsSymm p) (hp : 1 ≤ p) {T : Set E} (hT : Convex ℝ T) (hT0 : (0 : E) ∈ T)
    (hmin : IsLocalMinOn (compositeRegularizedModel Df Dc h p σ) T 0) {d : E} (hd : d ∈ T) :
    compositeTaylorDecrement Df Dc h 1 d ≤ 0 := by
  have hf : DifferentiableAt ℝ (regularizedModel Df p σ) 0 :=
    ((contDiff_regularizedModel (D := Df) (σ := σ)).differentiable
      (by exact_mod_cast (show p ≠ 0 by omega))) 0
  have hc : DifferentiableAt ℝ (Dc.taylorSum p) 0 :=
    (Dc.contDiff_taylorSum p (n := 1)).differentiable one_ne_zero 0
  have := compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hT hT0 hf hc hconv hLip hmin
    (s := d) (by simpa using hd)
  rwa [← compositeModelDecrement_def, compositeModelDecrement_zero_left hDf hDc hp] at this

end Minimizer

/-! ### Existence of model minimizers -/

section Existence

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {p : ℕ} {σ Lh : ℝ}

/-- **Coercivity of the composite model** (remark after (14.1.14) of [cartis2022evaluation]): for
`σ > 0` and `h` with a Lipschitz constant, `m̂(s) → ∞` as `‖s‖ → ∞`, since `T_{f,p} + h ∘ T_{c,p}`
grows at most like `‖s‖^p`. -/
theorem tendsto_compositeRegularizedModel_cocompact [ProperSpace E]
    (hLip : HasLipschitzConst h Lh) (hσ : 0 < σ) :
    Tendsto (compositeRegularizedModel Df Dc h p σ) (cocompact E) atTop := by
  set Kc := ∑ i ∈ Finset.Icc 1 p, ‖Dc i‖ / (i ! : ℝ)
  set K := ∑ i ∈ Finset.Icc 1 p, ‖Df i‖ / (i ! : ℝ) + Lh * Kc
  set c := σ / ((p + 1)! : ℝ)
  set A := Df 0 0 + h (Dc 0 0)
  have hc : 0 < c := by positivity
  have hLh := hLip.nonneg
  have hg : Tendsto (fun t : ℝ => A + (c * t - K)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hc))
  have hev : ∀ᶠ t in atTop, 1 ≤ t ∧ K ≤ c * t :=
    (eventually_ge_atTop 1).and
      ((tendsto_id.const_mul_atTop hc).eventually (eventually_ge_atTop K))
  have hlow : ∀ᶠ s in cocompact E,
      A + (c * ‖s‖ - K) ≤ compositeRegularizedModel Df Dc h p σ s := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually hev] with s ⟨hs1, hsK⟩
    have hT := taylorSum_ge_of_one_le_norm Df p hs1
    have hC : ‖Dc.taylorSum p 0 - Dc.taylorSum p s‖ ≤ Kc * ‖s‖ ^ p := by
      refine (norm_taylorSum_zero_sub_le Dc p s).trans ?_
      rw [sum_mul]
      refine sum_le_sum fun i hi => ?_
      rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
      have : ‖s‖ ^ i ≤ ‖s‖ ^ p := pow_le_pow_right₀ hs1 (Finset.mem_Icc.1 hi).2
      gcongr
    rw [Dc.taylorSum_zero_right] at hC
    have hh : h (Dc 0 0) - Lh * (Kc * ‖s‖ ^ p) ≤ h (Dc.taylorSum p s) := by
      have := hLip.abs_sub_le (Dc 0 0) (Dc.taylorSum p s)
      have := (le_abs_self _).trans this
      nlinarith [mul_le_mul_of_nonneg_left hC hLh]
    have hsp : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
    have hpow : ‖s‖ ^ (p + 1) = ‖s‖ ^ p * ‖s‖ := pow_succ _ _
    have : c * ‖s‖ - K ≤ ‖s‖ ^ p * (c * ‖s‖ - K) := le_mul_of_one_le_left (by linarith) hsp
    rw [compositeRegularizedModel_def, regularizedModel_def, hpow]
    change A + (c * ‖s‖ - K) ≤ Df.taylorSum p s + c * (‖s‖ ^ p * ‖s‖) + h (Dc.taylorSum p s)
    nlinarith
  exact tendsto_atTop_mono' _ hlow (hg.comp tendsto_norm_cocompact_atTop)

/-- **Global minimizers of the composite model** on a closed set of feasible steps containing `0`
(finite dimension, `σ > 0`, `h` Lipschitz): the model is continuous and coercive. -/
theorem exists_isMinOn_compositeRegularizedModel [FiniteDimensional ℝ E]
    (hLip : HasLipschitzConst h Lh) (hσ : 0 < σ) {T : Set E} (hT : IsClosed T)
    (hT0 : (0 : E) ∈ T) :
    ∃ s ∈ T, IsMinOn (compositeRegularizedModel Df Dc h p σ) T s := by
  have := FiniteDimensional.proper_real E
  refine (continuous_compositeRegularizedModel Df Dc h p σ hLip.continuous).continuousOn
    |>.exists_isMinOn' hT hT0 ?_
  exact Filter.Eventually.filter_mono inf_le_left
    ((tendsto_compositeRegularizedModel_cocompact hLip hσ).eventually
      (eventually_ge_atTop (compositeRegularizedModel Df Dc h p σ 0)))

end Existence

/-! ### One-step comparison of measures (Lemma 14.1.7) -/

section Step

variable {f : E → ℝ} {c : E → F} {h : F → ℝ} {p : ℕ} {σ Lf Lc Lh : ℝ} {C : Set E} {x s : E}

/-- A sum over `range (j + 1)` is its `0`-th term plus the sum over `Icc 1 j`. -/
private theorem sum_range_succ_eq_add_sum_Icc (g : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), g i = g 0 + ∑ i ∈ Finset.Icc 1 j, g i := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos j),
    ← Finset.Ico_add_one_right_eq_Icc]
  rfl

/-- **Smooth part of the one-step comparison** ([cartis2022evaluation], (12.2.53)–(12.2.56),
(B.14.2), (B.14.6)): if `f` is `C^p` on a convex `C ∋ x, x + s` with `Lf`-Lipschitz `∇^p f`, the
order-`j` Taylor decrement of `f` at `x + s` exceeds that of the regularized model
`m = regularizedModel (ftaylorSeries ℝ f x) p σ` at `s` (`σ ≥ 0`, `j ≤ p`) by at most
`(Lf + σ) ∑_{ℓ=1}^j ‖d‖^ℓ/ℓ! ‖s‖^{p-ℓ+1}/(p-ℓ+1)!`. -/
theorem taylorDecrement_le_add_of_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hLf : IteratedFDerivLipschitzOn f p Lf C)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) (d : E) :
    (ftaylorSeries ℝ f (x + s)).taylorDecrement j d ≤
      (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s).taylorDecrement j d +
        (Lf + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) := by
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
    mul_sum]
  have key : ∑ ℓ ∈ Finset.Icc 1 j,
      ((ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s ℓ
          (fun _ => d) - (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ f (x + s) ℓ (fun _ => d)) ≤
      ∑ ℓ ∈ Finset.Icc 1 j,
        (Lf + σ) * (‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))) := by
    refine sum_le_sum fun ℓ hℓ => ?_
    have hℓp : ℓ ≤ p := (Finset.mem_Icc.1 hℓ).2.trans hjp
    have hb := abs_iteratedFDeriv_apply_le_of_regularizedModel hC hf hLf hx hxs hσ hℓp d
    rw [abs_sub_comm] at hb
    have hfac : (0 : ℝ) ≤ (ℓ ! : ℝ)⁻¹ := by positivity
    calc (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s ℓ
            (fun _ => d) - (ℓ ! : ℝ)⁻¹ * ftaylorSeries ℝ f (x + s) ℓ (fun _ => d)
        = (ℓ ! : ℝ)⁻¹ * (iteratedFDeriv ℝ ℓ (regularizedModel (ftaylorSeries ℝ f x) p σ) s
            (fun _ => d) - iteratedFDeriv ℝ ℓ f (x + s) (fun _ => d)) := by
          simp only [ftaylorSeries]; ring
      _ ≤ (ℓ ! : ℝ)⁻¹ * ((Lf + σ) / ((p - ℓ + 1)! : ℝ) * ‖s‖ ^ (p - ℓ + 1) * ‖d‖ ^ ℓ) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hfac
      _ = (Lf + σ) * (‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))) := by ring
  rw [sum_sub_distrib] at key
  linarith

/-- **One-step comparison of composite decrements** (the content of Lemma 14.1.7 of
[cartis2022evaluation], Appendix B (B.14.1)–(B.14.6), in corrected form). Let `f`, `c` be `C^p` on
a convex `C ∋ x, x + s`, with `Lf`-Lipschitz `∇^p f` and `Lc`-Lipschitz `∇^p c` on `C`, `h` with
Lipschitz constant `Lh`, `σ ≥ 0`, `j ≤ p`. Then the generalized Taylor decrement of `w = f + h ∘ c`
at `x + s` is at most the decrement of the composite model `m̂` built at `x` (evaluated at the
trial step `s`) plus
`(Lf + Lh Lc + σ) ∑_{ℓ=1}^j ‖d‖^ℓ/ℓ! ‖s‖^{p-ℓ+1}/(p-ℓ+1)! + 2 Lh Lc/(p+1)! ‖s‖^{p+1}`.

The book's (14.1.30) has the factor `1` on the last term: (B.14.3) and the `ℓ = 0` term of
(B.14.4) each contribute `Lh Lc ‖s‖^{p+1}/(p+1)!`. The book's exponent `p - j + 1` in (B.14.6)
should read `p - ℓ + 1`. -/
theorem compositeTaylorDecrement_le_of_step (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ}
    (hjp : j ≤ p) (d : E) :
    compositeTaylorDecrement (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j d ≤
      compositeModelDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h p σ j s d +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have hLh := hLip.nonneg
  have hsmooth := taylorDecrement_le_add_of_regularizedModel hC hf hLf hx hxs hσ hjp d
  set Ssum := ∑ ℓ ∈ Finset.Icc 1 j, ‖d‖ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ))
  -- (B.14.3): the values of `c` and of its Taylor polynomial at `x + s`
  have h1 : h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s) ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
    (le_abs_self _).trans ((hLip.abs_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      (norm_sub_taylorPolynomial_le_of_lipschitz hC hc hLc hx hxs) hLh))
  -- (B.14.4): the Taylor polynomials of order `j` of `c` at `x + s` and of `T_{c,p}` at `s`
  set B := ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s
  set C' := ftaylorSeries ℝ c (x + s)
  have hdiff : ∀ i ≤ p, ‖B i - C' i‖ ≤ Lc / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1) :=
    fun i hi => by
      rw [norm_sub_rev]
      exact norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz hC hc hLc hx hxs hi
  have h2 : h (B.taylorSum j d) - h (C'.taylorSum j d) ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum) := by
    have hn : ‖B.taylorSum j d - C'.taylorSum j d‖ ≤
        Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum := by
      rw [← FormalMultilinearSeries.taylorSum_sub]
      refine ((B - C').norm_taylorSum_le j d).trans ?_
      rw [sum_range_succ_eq_add_sum_Icc, mul_sum]
      refine add_le_add ?_ (sum_le_sum fun i hi => ?_)
      · simpa using hdiff 0 (Nat.zero_le _)
      · have hip : i ≤ p := (Finset.mem_Icc.1 hi).2.trans hjp
        calc ‖(B - C') i‖ * ‖d‖ ^ i / (i ! : ℝ)
            ≤ Lc / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1) * ‖d‖ ^ i / (i ! : ℝ) := by
              gcongr; exact hdiff i hip
          _ = Lc * (‖d‖ ^ i / i ! * (‖s‖ ^ (p - i + 1) / ((p - i + 1)! : ℝ))) := by ring
    exact (le_abs_self _).trans ((hLip.abs_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left hn hLh))
  have hz : C'.taylorSum j 0 = c (x + s) := taylorPolynomial_zero_right c j (x + s)
  have hz' : B.taylorSum j 0 = (ftaylorSeries ℝ c x).taylorSum p s :=
    taylorPolynomial_zero_right _ j s
  rw [compositeTaylorDecrement_eq, compositeModelDecrement_def, compositeTaylorDecrement_eq, hz,
    hz']
  have e : Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) +
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lc * Ssum) + (Lf + σ) * Ssum =
      (Lf + Lh * Lc + σ) * Ssum + 2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by ring
  linarith

/-- **One-step comparison of composite measures** (Lemma 14.1.7 of [cartis2022evaluation],
corrected, before using the Step-2 condition (14.1.13)): under the hypotheses of
`compositeTaylorDecrement_le_of_step`, with `Lf, Lc ≥ 0`, feasible displacements `S ∋ 0` and
`δ ≥ 0`,
`φ^δ_{w,j}(x + s) ≤ φ^δ_{m̂,j}(s) + (Lf + Lh Lc + σ) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s‖^{p-ℓ+1}/(p-ℓ+1)! +
2 Lh Lc/(p+1)! ‖s‖^{p+1}`, the measures being taken over `closedBall 0 δ ∩ S`. -/
theorem compositeTaylorMeasure_le_of_step (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : IteratedFDerivLipschitzOn f p Lf C) (hLc : IteratedFDerivLipschitzOn c p Lc C)
    (hLip : HasLipschitzConst h Lh) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc) (hx : x ∈ C)
    (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hjp : j ≤ p) {S : Set E} (hS0 : (0 : E) ∈ S)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorMeasure (ftaylorSeries ℝ f (x + s)) (ftaylorSeries ℝ c (x + s)) h j δ S ≤
      compositeTaylorMeasure
          (ftaylorSeries ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
          (ftaylorSeries ℝ ((ftaylorSeries ℝ c x).taylorSum p) s) h j δ S +
        (Lf + Lh * Lc + σ) *
          ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * (‖s‖ ^ (p - ℓ + 1) / ((p - ℓ + 1)! : ℝ)) +
        2 * Lh * Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have hK : 0 ≤ Lf + Lh * Lc + σ := by have := hLip.nonneg; positivity
  refine decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS0⟩ fun d hd => ?_
  have hdδ : ‖d‖ ≤ δ := mem_closedBall_zero_iff.1 hd.1
  refine (compositeTaylorDecrement_le_of_step hC hf hc hLf hLc hLip hx hxs hσ hjp d).trans ?_
  refine add_le_add (add_le_add (compositeTaylorDecrement_le_compositeTaylorMeasure hLip hd) ?_)
    le_rfl
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun ℓ _ => ?_) hK
  gcongr

end Step

end Optimization
