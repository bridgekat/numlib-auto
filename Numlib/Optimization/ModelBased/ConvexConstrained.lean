import Numlib.Optimization.ModelBased.ARpRun
import Numlib.Optimization.Optimality.ConstrainedMeasure

/-!
# Adaptive regularization over a convex set: one-iteration estimates

One-iteration estimates for adaptive regularization with `p`-th order models
`m(s) = regularizedModel (ftaylorSeries ℝ f x) p σ s` over a convex feasible set `C`
([cartis2022evaluation], §6.2; used again in §6.3 and §7.2, and with `C = univ` by the
unconstrained ARp of Chapter 4). The standing hypotheses are those of the core estimate
`Optimization.abs_iteratedFDeriv_apply_le_of_regularizedModel` (f.DpL.C): `C` convex, `f` `C^p`
at the points of `C`, `∇^p f` `L`-Lipschitz on `C`, `x, x + s ∈ C`, `σ ≥ 0`.

## Main statements

* `Optimization.abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall`: (6.2.23) on the
  unit ball, `|∇^j f(x+s)[d]^j - ∇^j m(s)[d]^j| ≤ (L + σ)/(p-j+1)! ‖s‖^{p-j+1}`;
* `Optimization.formCriticality_le_regularizedModel`,
  `Optimization.inter_closedBall_restrictedSteps_subset_regularizedModel`: its measure form and
  the transfer of restricted sets (the core of Lemma 6.2.1, (6.2.18)–(6.2.19));
* `Optimization.IsFirstOrderCCStep`: the Step-2 conditions of ARp1-CC (Algorithm 6.2.2,
  (6.2.29)); with `C = univ` these are ARp's first-order conditions
  (`Optimization.isFirstOrderCCStep_univ_iff`);
* `Optimization.IsFirstOrderCCStep.measure_le_mul_pow`, `Optimization.IsFirstOrderCCStep.sub_ge`:
  the step length bound and the decrease of Lemma 6.2.4;
* `Optimization.exists_isMinOn_regularizedModel_of_isClosed`,
  `Optimization.exists_isFirstOrderCCStep`: existence of model minimizers over closed sets and of
  admissible ARp1-CC steps.

## The unit ball

(6.2.18)–(6.2.19) transfer the restricted sets `𝒞^1(x_{k+1}, ε₁)`, `𝒞^2(…)` from `f` to the
model. The estimate (6.2.23) holds for `‖d‖ ≤ 1` (the error grows like `‖d‖^j`), so the transfer
is stated on the unit ball, which is all that the measures use.
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Estimates

variable {f : E → ℝ} {p : ℕ} {L σ : ℝ} {C : Set E} {x s : E}

/-- **(6.2.23)** ([cartis2022evaluation], proof of Lemma 6.2.1) on the unit ball: for `j ≤ p`
and `‖d‖ ≤ 1`, `|∇^j f(x+s)[d]^j - ∇^j m(s)[d]^j| ≤ (L + σ)/(p-j+1)! ‖s‖^{p-j+1}`. -/
theorem abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {d : E}
    (hd : d ∈ closedBall (0 : E) 1) :
    |iteratedFDeriv ℝ j f (x + s) (fun _ => d) -
        iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  refine (abs_iteratedFDeriv_apply_le_of_regularizedModel hC hf hL hx hxs hσ hj d).trans ?_
  have h1 : ‖d‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) (by simpa using hd)
  have h0 : 0 ≤ (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
  calc _ ≤ (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- **Measure form of (6.2.23)** ([cartis2022evaluation], proof of Lemma 6.2.1): for `j ≤ p` and
any admissible set `T ∋ 0`, the `j`-th order measure of `f` at `x + s` exceeds that of the model at
`s` by at most `(L + σ)/(p-j+1)! ‖s‖^{p-j+1}`. -/
theorem formCriticality_le_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {T : Set E}
    (hT : 0 ∈ T) :
    formCriticality (iteratedFDeriv ℝ j f (x + s)) T ≤
      formCriticality (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) T +
        (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
  formCriticality_le_add_of_abs_sub_le _ _ ⟨0, zero_mem_closedBall_inter hT⟩ fun _ hd =>
    abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf hL hL0 hx hxs hσ hj hd.1

/-- **(6.2.18)–(6.2.19)** ([cartis2022evaluation], Lemma 6.2.1): unit-ball
displacements on which `|∇^j f(x+s)[d]^j| ≤ a` satisfy `|∇^j m(s)[d]^j| ≤ b` whenever
`(L + σ)/(p-j+1)! ‖s‖^{p-j+1} + a ≤ b`. -/
theorem inter_closedBall_restrictedSteps_subset_regularizedModel (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) {j : ℕ} (hj : j ≤ p) {T : Set E} {a b : ℝ}
    (hab : (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) + a ≤ b) :
    closedBall 0 1 ∩ restrictedSteps (iteratedFDeriv ℝ j f (x + s)) a T ⊆
      restrictedSteps (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) b T :=
  inter_closedBall_restrictedSteps_subset _ (fun _ hd =>
    abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf hL hL0 hx hxs hσ hj hd.1)
    hab

end Estimates

section Step

/-- **The ARp1-CC step conditions** ([cartis2022evaluation], Algorithm 6.2.2, Step 2) at `x` with
weight `σ`, for the model `m = regularizedModel (ftaylorSeries ℝ f x) p σ`: the trial point is
feasible, the model decreases, and the model's first-order measure over `𝓜⁰(s) = 𝒞(x + s)` is
at most `θ ‖s‖^p` (6.2.29). With `C = univ` the last condition is ARp's (4.1.11),
`‖∇m(s)‖ ≤ θ ‖s‖^p` (`Optimization.isFirstOrderCCStep_univ_iff`). -/
structure IsFirstOrderCCStep (f : E → ℝ) (C : Set E) (p : ℕ) (θ : ℝ) (x : E) (σ : ℝ) (s : E) :
    Prop where
  /-- The trial point is feasible. -/
  mem : x + s ∈ C
  /-- The step decreases the model. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- (6.2.29): the model's first-order measure at the step is small. -/
  measure : formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (feasibleSteps C (x + s)) ≤ θ * ‖s‖ ^ p

variable {f : E → ℝ} {C : Set E} {p : ℕ} {θ σ L : ℝ} {x s : E}

/-- Without constraints, the ARp1-CC step conditions are the first-order ARp step conditions
(4.1.10)–(4.1.11). -/
theorem isFirstOrderCCStep_univ_iff :
    IsFirstOrderCCStep f univ p θ x σ s ↔
      regularizedModel (ftaylorSeries ℝ f x) p σ s <
          regularizedModel (ftaylorSeries ℝ f x) p σ 0 ∧
        ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤ θ * ‖s‖ ^ p := by
  have hU : feasibleSteps (univ : Set E) (x + s) = univ := by ext; simp
  constructor
  · rintro ⟨-, h1, h2⟩
    rw [hU, formCriticality_iteratedFDeriv_one_univ] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_univ _, h1, ?_⟩
    rwa [hU, formCriticality_iteratedFDeriv_one_univ]

/-- An ARp step for `q = 1` is an ARp1-CC step for `C = univ` and `θ = θ₁`. -/
theorem IsARpStep.isFirstOrderCCStep {P : ARpParams} {q : ℕ}
    (h : IsARpStep f p P q x σ s) : IsFirstOrderCCStep f univ p P.θ₁ x σ s :=
  isFirstOrderCCStep_univ_iff.2 ⟨h.decrease, h.gradient⟩

/-- **Step-length bound for ARp1-CC** ([cartis2022evaluation], proof of Lemma 6.2.4): for
`p ≥ 1`, with `ω = ω_{f,𝒞,1}(x + s)`, `ω ≤ (L + σ + θ p!)/p! ‖s‖^p`, i.e.
`‖s‖^p ≥ p!/(L + σ + θ p!) ω` (the admissible sets of the two measures coincide since
`𝓜⁰(s) = 𝒞(x + s)`). -/
theorem IsFirstOrderCCStep.measure_le_mul_pow (h : IsFirstOrderCCStep f C p θ x σ s)
    (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L) (hx : x ∈ C) (hσ : 0 ≤ σ) (hp : 1 ≤ p) :
    formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s)) ≤
      (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p := by
  have h1 := formCriticality_le_regularizedModel hC hf hL hL0 hx h.mem hσ hp
    (zero_mem_feasibleSteps.2 (by simpa using h.mem))
  rw [Nat.sub_add_cancel hp] at h1
  have h2 := h.measure
  have : (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p = (L + σ) / (p ! : ℝ) * ‖s‖ ^ p + θ * ‖s‖ ^ p := by
    field_simp
  rw [this]
  linarith

/-- **Lemma 6.2.4** ([cartis2022evaluation]; with `C = univ` the first part of Lemma 4.1.4,
(4.1.31)): on a successful ARp1-CC iteration (`η₁ ≤ ρ`, `η₁ > 0`) with
`0 ≤ σ_min ≤ σ ≤ σ_max`, `p ≥ 1`, `θ ≥ 0`,
`f(x) - f(x + s) ≥ κ₁ ω_{f,𝒞,1}(x + s)^{(p+1)/p}` with
`κ₁ = η₁ σ_min/(p+1)! (p!/(L + σ_max + θ p!))^{(p+1)/p}` (4.1.32). -/
theorem IsFirstOrderCCStep.sub_ge (h : IsFirstOrderCCStep f C p θ x σ s) (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L)
    (hx : x ∈ C) (hp : 1 ≤ p) (hθ : 0 ≤ θ) {σmin σmax η₁ : ℝ} (hσmin : 0 ≤ σmin)
    (hσ1 : σmin ≤ σ) (hσ2 : σ ≤ σmax) (hη : 0 < η₁)
    (hρ : η₁ ≤ reductionRatio f x s ((ftaylorSeries ℝ f x).taylorDecrement p s)) :
    η₁ * σmin / ((p + 1)! : ℝ) * ((p ! : ℝ) / (L + σmax + θ * p !)) ^ (((p : ℝ) + 1) / p) *
        formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s)) ^
          (((p : ℝ) + 1) / p) ≤ f x - f (x + s) := by
  set ω := formCriticality (iteratedFDeriv ℝ 1 f (x + s)) (feasibleSteps C (x + s))
  have hσ : 0 ≤ σ := hσmin.trans hσ1
  have hω : 0 ≤ ω := formCriticality_nonneg _ le_rfl (zero_mem_feasibleSteps.2 (by
    simpa using h.mem))
  -- the decrease (4.1.37)
  have hpred := lt_taylorDecrement_of_regularizedModel_lt h.decrease
  have hpred0 : 0 < (ftaylorSeries ℝ f x).taylorDecrement p s :=
    lt_of_le_of_lt (by positivity) hpred
  have hdec := sub_le_of_le_reductionRatio hpred0 hρ
  set c := η₁ * σmin / ((p + 1)! : ℝ)
  have hc : 0 ≤ c := by positivity
  have h37 : c * ‖s‖ ^ (p + 1) ≤ f x - f (x + s) := by
    refine le_trans ?_ hdec
    calc c * ‖s‖ ^ (p + 1) = η₁ * (σmin / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) := by ring
      _ ≤ η₁ * (σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hpred.le hη.le
  -- the step-length bound
  set K := L + σmax + θ * (p ! : ℝ)
  have hK : 0 ≤ K := by have := hσ.trans hσ2; positivity
  have hstep : (p ! : ℝ) / K * ω ≤ ‖s‖ ^ p := by
    rcases hK.lt_or_eq with hK | hK
    · have h1 := h.measure_le_mul_pow hC hf hL hL0 hx hσ hp
      have h2 : (L + σ + θ * p !) / (p ! : ℝ) * ‖s‖ ^ p ≤ K / (p ! : ℝ) * ‖s‖ ^ p := by
        gcongr
        simp only [K]
        linarith
      have h3 := h1.trans h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h3
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      linarith
    · rw [← hK, div_zero, zero_mul]; positivity
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hn, mul_assoc, ← Real.mul_rpow (by positivity) hω]
  exact (mul_le_mul_of_nonneg_left (Real.rpow_div_le_pow_of_le_pow (by positivity) (norm_nonneg _)
    (by omega) hstep) hc).trans h37

end Step

section Existence

variable {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ : ℝ}

/-- **Model minimizers over a closed set** ([cartis2022evaluation], §6.2.1): in finite
dimension, for `σ > 0` and a closed `S ∋ 0`, the model attains its minimum on `S`
(coercivity). -/
theorem exists_isMinOn_regularizedModel_of_isClosed [FiniteDimensional ℝ E] {S : Set E}
    (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hσ : 0 < σ) :
    ∃ s ∈ S, IsMinOn (regularizedModel D p σ) S s := by
  have := FiniteDimensional.proper_real E
  have htend : Filter.Tendsto (regularizedModel D p σ) (Filter.cocompact E) Filter.atTop := by
    rw [regularizedModel_eq_powRegularizedModel]
    exact tendsto_powRegularizedModel_cocompact hσ (by linarith)
  exact (continuous_regularizedModel D p σ).continuousOn.exists_isMinOn' hS h0
    ((htend.eventually (Filter.eventually_ge_atTop _)).filter_mono inf_le_left)

variable {f : E → ℝ} {C : Set E} {θ : ℝ} {x : E}

/-- **Well-posedness of ARp1-CC** (and of the first-order ARp-CC Step 2,
[cartis2022evaluation], Algorithms 6.2.1–6.2.2): in finite dimension, for `C` closed convex,
`x ∈ C`, `f` `C^p` at `x` (`p ≥ 1`), `σ > 0`, `θ ≥ 0` and `x` not first-order critical
(`ω_{f,𝒞,1}(x) > 0`), there is a global minimizer `s*` of the model over the feasible steps
`𝒞(x)`; it is an ARp1-CC step and its model measure vanishes (so it also satisfies ARp-CC's
(6.2.10)). -/
theorem exists_isFirstOrderCCStep [FiniteDimensional ℝ E] (hCc : IsClosed C) (hC : Convex ℝ C)
    (hx : x ∈ C) (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) (hσ : 0 < σ) (hθ : 0 ≤ θ)
    (hcrit : 0 < formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x)) :
    ∃ s, IsMinOn (regularizedModel (ftaylorSeries ℝ f x) p σ) (feasibleSteps C x) s ∧
      IsFirstOrderCCStep f C p θ x σ s ∧
      formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
        (feasibleSteps C (x + s)) = 0 := by
  set m := regularizedModel (ftaylorSeries ℝ f x) p σ
  set S := feasibleSteps C x
  have hS0 : (0 : E) ∈ S := zero_mem_feasibleSteps.2 hx
  have hSc : Convex ℝ S := convex_feasibleSteps hC x
  have hdiff : Differentiable ℝ m :=
    (contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := p) (σ := σ)).differentiable
      (by norm_cast; omega)
  obtain ⟨s, hs, hmin⟩ := exists_isMinOn_regularizedModel_of_isClosed
    (D := ftaylorSeries ℝ f x) (isClosed_feasibleSteps hCc x) hS0 hσ
  have hSS : ∀ t, feasibleSteps S t = feasibleSteps C (x + t) := fun t => by
    ext d; simp [S, add_assoc]
  have hzero : formCriticality (iteratedFDeriv ℝ 1 m s) (feasibleSteps C (x + s)) = 0 := by
    rw [← hSS]
    exact formCriticality_eq_zero_of_isLocalMinOn hSc hs hmin.isLocalMinOn
      (hdiff s)
  have hdec : m s < m 0 := by
    refine lt_of_le_of_ne (hmin hS0) fun heq => hcrit.ne' ?_
    have hmin0 : IsMinOn m S 0 := fun y hy => by rw [← heq]; exact hmin hy
    have h0 := formCriticality_eq_zero_of_isLocalMinOn hSc hS0 hmin0.isLocalMinOn
      (hdiff 0)
    rw [formCriticality_fderiv_eq_zero_iff hSc hS0,
      fderiv_regularizedModel_ftaylorSeries_zero hf hp] at h0
    rw [formCriticality_fderiv_eq_zero_iff hC hx]
    intro y hy
    have := h0 (y - x) (by simpa [S] using hy)
    simpa using this
  refine ⟨s, hmin, ⟨by simpa [S] using hs, hdec, ?_⟩, hzero⟩
  rw [hzero]
  positivity

end Existence

end Optimization
