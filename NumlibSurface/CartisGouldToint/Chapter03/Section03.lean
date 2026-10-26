import Numlib.Optimization.Complexity.SlowExampleHighOrder
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter03.Section02

/-!
# Cartis–Gould–Toint §3.3: Adaptive regularization using second derivatives

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §3.3: the second-order
adaptive-regularization algorithm AR2 on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

The model (3.3.1) is `m_k(s) = T_{f,2}(x_k, s) + σ_k/6 ‖s‖³`, the regularized Taylor model
`Optimization.regularizedModel (ftaylorSeries ℝ f x_k) 2 σ_k` (`ar2Model`); the ratio (3.3.7) is
`Optimization.taylorRatio f 2 x s`. AR2 is an instance of the generic adaptive-regularization run
`Optimization.IsARRun` (Steps 3–4 being `Optimization.ARAcceptance`, the update (3.3.8)
`Optimization.ARUpdate`).

## Main definitions

* `AR2Params` — the constants (3.3.3).
* `ar2Model f x σ`, `ar2Step` — the model (3.3.1) and the Step-2 conditions (3.3.5)–(3.3.6).
* `algorithm_3_3_1 f P ε₁ ε₂ x s σ` — Algorithm 3.3.1 (AR2); `exists_algorithm_3_3_1`.
* `IsModifiedAR2Run` — the variant with (3.3.23) in place of (3.3.5).
* `sigmaMaxAR2`, `kappaSAR2`, `kappaCAR2`, `kappaTAR2` — the constants of (3.3.14), Lemma 3.3.4,
  Theorems 3.3.5 and 3.3.9.

## Main results

Lemmas 3.3.1–3.3.4, 3.3.7, 3.3.8, Theorems 3.3.5 and 3.3.9 (complexity) and Theorems 3.3.6 and
3.3.10 (sharpness).

## Fixes with respect to the book

* The Hessian of the model displayed after (3.3.2) has a spurious factor `2`; nothing depends
  on it (the curvature bounds use `Optimization.minCurvature_ge_of_regularizedModel`).
* (3.3.30) prints `κ^T (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + 1 = O(·) + 2`; the `+ 1` is false
  (the decrease is only guaranteed at successful iterations followed by a non-terminal one) and the
  correct bound, proved here, is `κ^T (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + 2` (the `+ 2`
  accounting for the initial evaluation and the last successful iteration, as in (3.3.22)).
* Step 1 also terminates at "strict local minimizers"; these satisfy (3.3.4), so the termination
  test is (3.3.4) alone (`stopTest`).
* Theorems 3.3.6 and 3.3.10 are proved here (the book defers them to §12.2.2.4) on the
  one-dimensional data of Theorem 12.2.15 (`Optimization.exists_slowTaylorOrder_interpolant`):
  the iterations are exact global model minimizations with `σ_k = σ₀` and `ρ_k = 1`.
-/

open Set Finset Optimization Subproblem
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter03

variable {n : ℕ}

/-- The constants of Algorithm 3.3.1 ([cartis2022evaluation], (3.3.3)): those of AR1 (2.4.2) and
the step-accuracy parameters `θ₁, θ₂ > 0`. -/
structure AR2Params extends toAR1Params : Chapter02.ARParams where
  /-- The first-order step accuracy (3.3.5). -/
  θ₁ : ℝ
  /-- The second-order step accuracy (3.3.6). -/
  θ₂ : ℝ
  /-- `θ₁ > 0`. -/
  θ₁_pos : 0 < θ₁
  /-- `θ₂ > 0`. -/
  θ₂_pos : 0 < θ₂

/-- The constants as backbone `Optimization.ARParams`. -/
abbrev AR2Params.ar (P : AR2Params) : Optimization.ARParams := P.toAR1Params.toARParams

/-- The regularized model (3.3.1): `m(s) = T_{f,2}(x, s) + σ/6 ‖s‖³`. -/
noncomputable def ar2Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  regularizedModel (ftaylorSeries ℝ f x) 2 σ

theorem ar2Model_apply (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    ar2Model f x σ s = taylorPolynomial f 2 x s + σ / 6 * ‖s‖ ^ 3 := by
  rw [ar2Model, regularizedModel_def, ← taylorPolynomial_eq_taylorSum]
  norm_num [Nat.factorial]

/-- Step 2 of Algorithm 3.3.1: the step decreases the model, `m(s) < m(0)`, satisfies the
first-order accuracy (3.3.5) `‖∇m(s)‖ ≤ θ₁/2 ‖s‖²` and, if `ε₂ < ∞`, the second-order accuracy
(3.3.6) `λ_min[∇²m(s)] ≥ -θ₂ ‖s‖`. -/
def ar2Step (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ar2Model f x σ s < ar2Model f x σ 0 ∧ ‖fderiv ℝ (ar2Model f x σ) s‖ ≤ P.θ₁ / 2 * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.θ₂ * ‖s‖) ≤ minCurvature (iteratedFDeriv ℝ 2 (ar2Model f x σ) s))

/-- **Algorithm 3.3.1** (AR2) of [cartis2022evaluation], as a run predicate on iterates `x`,
steps `s` and regularization parameters `σ`: `ε₁ ∈ (0, 1]`, `ε₂ > 0` if finite, and the generic
adaptive-regularization run `Optimization.IsARRun` with the termination test `stopTest f ε₁ ε₂`
(3.3.4), Step 2 `ar2Step`, no post-step test and the ratio (3.3.7) `taylorRatio f 2`. -/
structure algorithm_3_3_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The first-order tolerance is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance is at most `1`. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- The second-order tolerance is positive. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- Steps 1–4. -/
  run : IsARRun P.ar (fun k => stopTest f ε₁ ε₂ (x k)) (fun k => ar2Step f P ε₂ (x k) (σ k) (s k))
    (fun _ => False) (taylorRatio f 2 x s) x s σ

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- A global minimizer of the AR2 model satisfies Step 2 whenever the termination test fails. -/
theorem ar2Step_of_isMinOn {x : EuclideanSpace ℝ (Fin n)} (P : AR2Params) (ε₂ : Option ℝ)
    {σ : ℝ} {s : EuclideanSpace ℝ (Fin n)} (hmin : IsMinOn (ar2Model f x σ) univ s)
    (hdec : ar2Model f x σ s < ar2Model f x σ 0) :
    ar2Step f P ε₂ x σ s := by
  have hloc : IsLocalMin (ar2Model f x σ) s := hmin.isLocalMin Filter.univ_mem
  refine ⟨hdec, by rw [hloc.fderiv_eq_zero, norm_zero]; have := P.θ₁_pos; positivity,
    fun _ => ?_⟩
  have h0 := hloc.minCurvature_iteratedFDeriv_two_nonneg
    ((contDiff_regularizedModel (D := ftaylorSeries ℝ f x) (p := 2) (σ := σ)).contDiffAt)
  have := P.θ₂_pos
  have : 0 ≤ P.θ₂ * ‖s‖ := by positivity
  linarith

/-- Where the AR2 termination test fails, a global minimizer of the model (3.3.1) exists and
decreases the model. -/
theorem exists_isMinOn_ar2Model_lt (hf : ContDiff ℝ 2 f) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) {y : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (hσ : 0 < σ) (hnot : ¬ stopTest f ε₁ ε₂ y) :
    ∃ s, IsMinOn (ar2Model f y σ) univ s ∧ ar2Model f y σ s < ar2Model f y σ 0 := by
  obtain ⟨s, hmin, -, -, hlt⟩ := exists_isMinOn_regularizedModel
    (D := ftaylorSeries ℝ f y) (p := 2) hσ (by norm_num)
  have hdec : ar2Model f y σ s < ar2Model f y σ 0 := by
    by_cases hg : gradient f y = 0
    · -- the second-order part of the test fails
      have hlam : minCurvature (iteratedFDeriv ℝ 2 (ar2Model f y σ) 0) < 0 := by
        rw [ar2Model, iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero
          hf.contDiffAt le_rfl]
        by_contra hnn
        refine hnot ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
        have := hε₂ e he
        change -e ≤ minCurvature _
        linarith [not_lt.1 hnn]
      exact regularizedModel_lt_of_isMinOn_of_minCurvature_neg le_rfl hmin hlam
    · refine regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin ?_
      rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt (by norm_num)]
      intro h0
      exact hg (by rw [← norm_eq_zero, norm_gradient_eq, h0, norm_zero])
  exact ⟨s, hmin, hdec⟩

/-- **Existence of AR2 runs** ([cartis2022evaluation], Algorithm 3.3.1 is well defined): for a
`C²` function, all constants and tolerances and every starting point there is an AR2 run (a
global minimizer of the model (3.3.1), which exists since `σ_k > 0`, satisfies Step 2 whenever
the termination test fails). -/
theorem exists_algorithm_3_3_1 (hf : ContDiff ℝ 2 f) (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_3_3_1 f P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := fun y σ s => ar2Step f P ε₂ y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hdec⟩ := exists_isMinOn_ar2Model_lt hf hε₁ hε₂ hσ hnot
      exact ⟨s, ar2Step_of_isMinOn P ε₂ hmin hdec, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hε₁, hε₁1, hε₂, hrun⟩

end Existence

/-! ### Lemmas 3.3.1–3.3.4 and Theorem 3.3.5 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L₂ flow : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

namespace algorithm_3_3_1

theorem sigma_pos (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : 0 < σ k :=
  h.run.sigma_pos (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

theorem sigmaMin_le (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : P.σmin ≤ σ k :=
  h.run.sigmaMin_le (IsARRun.forall_lt_not_stop_iff.2 hk) k le_rfl

theorem step (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) : ar2Step f P ε₂ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)

end algorithm_3_3_1

/-- **Lemma 3.3.1** of [cartis2022evaluation] ((3.3.13)). At every iteration `k` before
termination of an AR2 run, `T_{f,2}(x_k, 0) - T_{f,2}(x_k, s_k) > σ_k/6 ‖s_k‖³`. -/
theorem lemma_3_3_1 (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) :
    σ k / 6 * ‖s k‖ ^ 3 < (ftaylorSeries ℝ f (x k)).taylorDecrement 2 (s k) := by
  have := lt_taylorDecrement_of_regularizedModel_lt (h.step hk).1
  norm_num [Nat.factorial] at this
  exact this

/-- The bound `σ_max = max(σ₀, γ₃ L_{f,2}/(1 - η₂))` of (3.3.14) (`Optimization.arSigmaMax`). -/
noncomputable abbrev sigmaMaxAR2 (P : AR2Params) (L : ℝ) : ℝ := arSigmaMax P.ar L

/-- **Lemma 3.3.2** of [cartis2022evaluation] ((3.3.14)). Under f.HL, for every iteration `k` of
an AR2 run up to (and including) termination, `σ_k ≤ σ_max = max(σ₀, γ₃ L_{f,2}/(1 - η₂))`. -/
theorem lemma_3_3_2 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) : σ k ≤ sigmaMaxAR2 P L₂ :=
  (h.run.sigma_le convex_univ (fun y _ => hf.contDiffAt y) hf.iteratedFDerivLipschitzOn
    (mem_univ _) (fun _ _ hst => ⟨mem_univ _, hst.1⟩) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)).2.2

/-- **Lemma 3.3.3** of [cartis2022evaluation] ((3.3.15)). Under f.HL, if iteration `k` of an AR2
run is successful (and before termination), then
`‖s_k‖² ≥ 2/(L_{f,2} + θ₁ + σ_max) ‖∇f(x_{k+1})‖`. -/
theorem lemma_3_3_3 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    2 / (L₂ + P.θ₁ + sigmaMaxAR2 P L₂) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_3_3_2 hf h fun j hj => hk j hj.le
  have hstep := h.step hk
  have hb := norm_fderiv_le_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt y)
    (le_refl _ |>.trans (by norm_num : (1 : ℕ) ≤ 2)) hf.iteratedFDerivLipschitzOn (mem_univ (x k))
    (mem_univ (x k + s k)) hσ.le
  rw [h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs, norm_gradient_eq]
  change ‖fderiv ℝ f (x k + s k)‖ ≤ (L₂ + σ k) / (Nat.factorial 2 : ℝ) * ‖s k‖ ^ 2 +
    ‖fderiv ℝ (ar2Model f (x k) (σ k)) (s k)‖ at hb
  have hC : 0 < L₂ + P.θ₁ + sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := P.θ₁_pos; have := arSigmaMax_pos P.ar L₂; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h2 := hstep.2.1
  norm_num [Nat.factorial] at hb
  have : σ k * ‖s k‖ ^ 2 ≤ sigmaMaxAR2 P L₂ * ‖s k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hσmax (sq_nonneg _)
  nlinarith

/-- The constant `κ^S_AR2 = 6 (L_{f,2} + θ₁ + σ_max)^{3/2}/(2^{3/2} η₁ σ_min)` of
Lemma 3.3.4. -/
noncomputable def kappaSAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  6 * (L + P.θ₁ + sigmaMaxAR2 P L) ^ (3 / 2 : ℝ) / (2 ^ (3 / 2 : ℝ) * P.η₁ * P.σmin)

theorem kappaSAR2_pos {P : AR2Params} {L : ℝ} (hL : 0 ≤ L) : 0 < kappaSAR2 P L := by
  have := P.θ₁_pos; have := arSigmaMax_pos P.ar L; have := P.η₁_pos; have := P.σmin_pos
  unfold kappaSAR2
  have : 0 < L + P.θ₁ + sigmaMaxAR2 P L := by linarith
  positivity

/-- The decrease at a successful AR2 iteration `k` with `‖∇f(x_{k+1})‖ ≥ ε₁`:
`f(x_k) - f(x_{k+1}) ≥ ε₁^{3/2}/κ^S_AR2`. -/
theorem ar2_decrease_first (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k)
    (hg : ε₁ ≤ ‖gradient f (x (k + 1))‖) :
    ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂ ≤ f (x k) - f (x (k + 1)) := by
  set C := L₂ + P.θ₁ + sigmaMaxAR2 P L₂
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmin := h.sigmaMin_le fun j hj => hk j hj.le
  have hC : 0 < C := by
    have := hf.pos; have := P.θ₁_pos; have := arSigmaMax_pos P.ar L₂; simp only [C]; linarith
  have hε := h.ε₁_pos
  have hη := P.η₁_pos
  have hsmin := P.σmin_pos
  -- decrease from the model
  have hm := (h.step hk).1
  obtain ⟨-, hdec⟩ := h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk) hm hs
  norm_num [Nat.factorial] at hdec
  -- step length
  have h3 := lemma_3_3_3 hf h hk hs
  have hs2 : 2 * ε₁ / C ≤ ‖s k‖ ^ 2 :=
    le_trans (by rw [div_mul_eq_mul_div]; gcongr) h3
  have hs3 : (2 * ε₁ / C) ^ (3 / 2 : ℝ) ≤ ‖s k‖ ^ 3 := by
    have : (‖s k‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s k‖ ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow (by positivity) hs2 (by norm_num)
  have hsplit : (2 * ε₁ / C) ^ (3 / 2 : ℝ) =
      2 ^ (3 / 2 : ℝ) * ε₁ ^ (3 / 2 : ℝ) / C ^ (3 / 2 : ℝ) := by
    rw [Real.div_rpow (by positivity) hC.le, Real.mul_rpow (by norm_num) hε.le]
  have key : ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂ =
      P.η₁ * (P.σmin / 6 * (2 * ε₁ / C) ^ (3 / 2 : ℝ)) := by
    rw [hsplit, kappaSAR2, show L₂ + P.θ₁ + sigmaMaxAR2 P L₂ = C from rfl]
    have : 0 < C ^ (3 / 2 : ℝ) := by positivity
    have : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
    field_simp
  rw [key]
  calc P.η₁ * (P.σmin / 6 * (2 * ε₁ / C) ^ (3 / 2 : ℝ)) ≤ P.η₁ * (σ k / 6 * ‖s k‖ ^ 3) := by
        gcongr
    _ ≤ _ := by linarith

theorem le_norm_gradient_of_not_stopTest {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} (h : ¬ stopTest f ε₁ none y) : ε₁ ≤ ‖gradient f y‖ := by
  rw [stopTest_none, not_le] at h
  exact h.le

/-- **Lemma 3.3.4** of [cartis2022evaluation] ((3.3.19)). Under f.Bb and f.HL, for an AR2 run with
`ε₂ = +∞`, at every iteration `k` before termination the number of successful iterations
satisfies `|𝒮_k| ≤ κ^S_AR2 (f(x₀) - f_low)/ε₁^{3/2} + 1`. -/
theorem lemma_3_3_4 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ none x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ none (x j)) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) k).card : ℝ) ≤
      kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 1 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  set δ := ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  rw [← hNδ]
  cases k with
  | zero =>
    have : (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) 0).card ≤ 1 := card_successSet_le
    have : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) 0).card : ℝ) ≤ 1 := by
      exact_mod_cast this
    have : 0 ≤ (f (x 0) - flow) / δ := div_nonneg (sub_nonneg.2 (hb _)) hδ.le
    linarith
  | succ m =>
    have hm : ∀ j ≤ m, ¬ stopTest f ε₁ none (x j) := fun j hj => hk j (hj.trans m.le_succ)
    have hcard := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) (k := m) hδ
      (fun j hj hs => by
        rw [h.run.eq_of_not_succ
          (IsARRun.forall_le_not_stop_iff.2 fun i hi => hm i (hi.trans hj))
          (not_le.1 hs)])
      (fun j hj hs => ar2_decrease_first hf h (fun i hi => hm i (hi.trans hj)) hs
        (le_norm_gradient_of_not_stopTest (hk (j + 1) (Nat.succ_le_succ hj))))
      (hb _)
    have : ((successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) (m + 1)).card : ℝ) ≤
        (successSet (fun j => P.η₁ ≤ taylorRatio f 2 x s j) m).card + 1 := by
      exact_mod_cast card_successSet_add_one_le
    linarith

/-- The constant `κ^C_AR2 = (|log γ₁| + log max(1, γ₃ L_{f,2}/(σ₀ (1 - η₂))))/log γ₂ + 2` of
Theorem 3.3.5 (and `κ^F_AR2` of Theorem 3.3.9). -/
noncomputable def kappaCAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂))))) / Real.log P.γ₂ + 2

theorem sigmaMaxAR2_div_eq (P : AR2Params) (L : ℝ) :
    sigmaMaxAR2 P L / P.σ₀ = max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂))) := by
  have := P.σ₀_pos
  rw [sigmaMaxAR2, arSigmaMax_def, ← max_div_div_right this.le]
  congr 1
  · exact div_self this.ne'
  · field_simp

/-- **Theorem 3.3.5** of [cartis2022evaluation] (first-order complexity of AR2). Under f.Bb and
f.HL, for every `ε₁ ∈ (0, 1]`, every AR2 run with `ε₂ = +∞` terminates at an iteration `k_ε`
(the first with `‖∇f(x_k)‖ ≤ ε₁`) after at most `κ^A (f(x₀) - f_low)/ε₁^{3/2} + κ^C` evaluations
of `f` (3.3.21) and at most `κ^S (f(x₀) - f_low)/ε₁^{3/2} + 2` evaluations of `∇f` and `∇²f`
(3.3.22), with `κ^S = kappaSAR2`, `κ^A = κ^S (1 + |log γ₁|/log γ₂)`, `κ^C = kappaCAR2`. -/
theorem theorem_3_3_5 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ none x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaSAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
          ε₁ ^ (3 / 2 : ℝ) + kappaCAR2 P L₂ ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 2 x s k) kε : ℝ) ≤
        kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) + 2 := by
  have hκ := kappaSAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  set δ := ε₁ ^ (3 / 2 : ℝ) / kappaSAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSAR2 P L₂ * (f (x 0) - flow) / ε₁ ^ (3 / 2 : ℝ) := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := sigmaMaxAR2 P L₂)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_3_3_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      ((lt_of_le_of_lt (by
          have := h.sigma_pos (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j hj.le)
          positivity) (lemma_3_3_1 h (IsARRun.forall_le_not_stop_iff.1 hk)))))
    (fun k _ => hb (x k))
    (fun k hk hs => ar2_decrease_first hf h
      (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j
        (hj.trans k.le_succ)) hs
      (le_norm_gradient_of_not_stopTest
        ((IsARRun.forall_le_not_stop_iff.1 hk) (k + 1) le_rfl)))
  rw [hNδ] at hF hD
  refine ⟨kε, ?_, ?_, hD⟩
  · have := IsARRun.isFirstHit_stop_iff.1 hk
    simpa only [stopTest_none] using this
  · rw [kappaCAR2, ← sigmaMaxAR2_div_eq]
    calc (funEvalCount kε : ℝ) ≤ _ := hF
      _ = _ := by ring

end Lemmas

/-! ### The modified AR2 algorithm and Lemma 3.3.7 -/

/-- Step 2 of the **modified AR2 algorithm** of §3.3.2 ([cartis2022evaluation], (3.3.23)): as
`ar2Step`, with (3.3.5) replaced by `‖∇_s T_{f,2}(x, s)‖ ≤ θ₁/2 σ ‖s‖²`. -/
def ar2ModStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₂ : Option ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  ar2Model f x σ s < ar2Model f x σ 0 ∧
    ‖fderiv ℝ (taylorPolynomial f 2 x) s‖ ≤ P.θ₁ / 2 * σ * ‖s‖ ^ 2 ∧
    (ε₂ ≠ none → -(P.θ₂ * ‖s‖) ≤ minCurvature (iteratedFDeriv ℝ 2 (ar2Model f x σ) s))

/-- The **modified AR2 algorithm** of [cartis2022evaluation] (§3.3.2, notes after Theorem 3.3.6):
Algorithm 3.3.1 with (3.3.5) replaced by (3.3.23), for `θ₁ > 1`. -/
structure IsModifiedAR2Run (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : AR2Params) (ε₁ : ℝ)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- `θ₁ > 1`. -/
  one_lt_θ₁ : 1 < P.θ₁
  /-- The first-order tolerance is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The first-order tolerance is at most `1`. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- The second-order tolerance is positive. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- Steps 1–4 with the modified Step 2. -/
  run : IsARRun P.ar (fun k => stopTest f ε₁ ε₂ (x k))
    (fun k => ar2ModStep f P ε₂ (x k) (σ k) (s k)) (fun _ => False) (taylorRatio f 2 x s) x s σ

section Modified

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ L₂ : ℝ} {ε₂ : Option ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- A global minimizer of the AR2 model that decreases it satisfies the modified Step 2
(3.3.23) when `θ₁ ≥ 1`: at a stationary point `∇_s T_{f,2}(x, s) = -σ/2 ‖s‖ s`. -/
theorem ar2ModStep_of_isMinOn {x : EuclideanSpace ℝ (Fin n)} (P : AR2Params) (hθ : 1 ≤ P.θ₁)
    (ε₂ : Option ℝ) {σ : ℝ} (hσ : 0 ≤ σ) {s : EuclideanSpace ℝ (Fin n)}
    (hmin : IsMinOn (ar2Model f x σ) univ s) (hdec : ar2Model f x σ s < ar2Model f x σ 0) :
    ar2ModStep f P ε₂ x σ s := by
  obtain ⟨-, -, h3⟩ := ar2Step_of_isMinOn (f := f) P ε₂ hmin hdec
  have hloc : IsLocalMin (ar2Model f x σ) s := hmin.isLocalMin Filter.univ_mem
  have h0 := hloc.fderiv_eq_zero
  rw [ar2Model, fderiv_regularizedModel (by norm_num)] at h0
  have hT : fderiv ℝ (taylorPolynomial f 2 x) s =
      -((σ / ((2 : ℕ).factorial : ℝ) * ‖s‖ ^ (2 - 1)) • innerSL ℝ s) := by
    rw [taylorPolynomial_eq_taylorSum]; exact eq_neg_of_add_eq_zero_left h0
  refine ⟨hdec, ?_, h3⟩
  rw [hT, norm_neg, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by positivity)]
  norm_num [Nat.factorial]
  have : 0 ≤ σ * ‖s‖ ^ 2 := by positivity
  nlinarith

/-- **Existence of modified AR2 runs** (§3.3.2): for a `C²` function, all constants with
`θ₁ > 1`, tolerances and every starting point there is a run of the modified AR2 algorithm (a
global minimizer of the model satisfies (3.3.23)). -/
theorem exists_isModifiedAR2Run (hf : ContDiff ℝ 2 f) (P : AR2Params) (hθ : 1 < P.θ₁) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ IsModifiedAR2Run f P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.ar (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := fun y σ s => ar2ModStep f P ε₂ y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 2 t))
    (fun y σ _ _ hσ hnot => by
      obtain ⟨s, hmin, hdec⟩ := exists_isMinOn_ar2Model_lt hf hε₁ hε₂ hσ hnot
      exact ⟨s, ar2ModStep_of_isMinOn P hθ.le ε₂ hσ.le hmin hdec, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hθ, hε₁, hε₁1, hε₂, hrun⟩

/-- Lemma 3.3.2 for the modified AR2 algorithm: under f.HL, `σ_k ≤ σ_max` up to termination. -/
theorem IsModifiedAR2Run.sigma_le (hf : AssumptionHL f L₂)
    (h : IsModifiedAR2Run f P ε₁ ε₂ x s σ) {k : ℕ} (hk : ∀ j < k, ¬ stopTest f ε₁ ε₂ (x j)) :
    σ k ≤ sigmaMaxAR2 P L₂ :=
  (h.run.sigma_le convex_univ (fun y _ => hf.contDiffAt y) hf.iteratedFDerivLipschitzOn
    (mem_univ _) (fun _ _ hst => ⟨mem_univ _, hst.1⟩) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)).2.2

/-- **Lemma 3.3.7** of [cartis2022evaluation] ((3.3.24)). Under f.HL, if iteration `k` of the
modified AR2 algorithm is successful (and before termination), then
`‖s_k‖² ≥ 2/(L_{f,2} + θ₁ σ_max) ‖∇f(x_{k+1})‖`. -/
theorem lemma_3_3_7 (hf : AssumptionHL f L₂) (h : IsModifiedAR2Run f P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    2 / (L₂ + P.θ₁ * sigmaMaxAR2 P L₂) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ 2 := by
  have hσmax := h.sigma_le hf fun j hj => hk j hj.le
  have hstep := h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)
  have hb := norm_fderiv_le_of_taylorPolynomial convex_univ (fun y _ => hf.contDiffAt y)
    (by norm_num : 1 ≤ 2) hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k))
  rw [h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs, norm_gradient_eq]
  have hθ := P.θ₁_pos
  have hC : 0 < L₂ + P.θ₁ * sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := arSigmaMax_pos P.ar L₂; positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h2 := hstep.2.1
  norm_num [Nat.factorial] at hb
  have : P.θ₁ / 2 * σ k * ‖s k‖ ^ 2 ≤ P.θ₁ / 2 * sigmaMaxAR2 P L₂ * ‖s k‖ ^ 2 := by gcongr
  nlinarith

end Modified

/-! ### Second-order complexity: Lemma 3.3.8 and Theorem 3.3.9 -/

section SecondOrder

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : AR2Params} {ε₁ e L₂ flow : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 3.3.8** of [cartis2022evaluation] ((3.3.25)). Under f.HL, if iteration `k` of an AR2
run with `ε₂ < ∞` is successful (and before termination) and `λ_min[∇²f(x_{k+1})] < 0`, then
`‖s_k‖ ≥ |λ_min[∇²f(x_{k+1})]|/(L_{f,2} + θ₂ + σ_max)`. -/
theorem lemma_3_3_8 (hf : AssumptionHL f L₂) (h : algorithm_3_3_1 f P ε₁ ε₂ x s σ)
    (hε₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ stopTest f ε₁ ε₂ (x j))
    (hs : P.η₁ ≤ taylorRatio f 2 x s k)
    (hneg : Chapter01.hessianMinEig f (x (k + 1)) < 0) :
    |Chapter01.hessianMinEig f (x (k + 1))| / (L₂ + P.θ₂ + sigmaMaxAR2 P L₂) ≤ ‖s k‖ := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_3_3_2 hf h fun j hj => hk j hj.le
  have hcurv := (h.step hk).2.2 hε₂
  have hb := minCurvature_ge_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt y)
    le_rfl hf.iteratedFDerivLipschitzOn (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le
  have hC : 0 < L₂ + P.θ₂ + sigmaMaxAR2 P L₂ := by
    have := hf.pos; have := P.θ₂_pos; have := arSigmaMax_pos P.ar L₂; linarith
  rw [Chapter01.hessianMinEig,
    h.run.eq_add_of_succ (IsARRun.forall_le_not_stop_iff.2 hk) hs] at hneg ⊢
  rw [abs_of_neg hneg, div_le_iff₀ hC]
  norm_num [Nat.factorial] at hb
  change -(P.θ₂ * ‖s k‖) ≤ minCurvature (iteratedFDeriv ℝ 2
    (regularizedModel (ftaylorSeries ℝ f (x k)) 2 (σ k)) (s k)) at hcurv
  have : σ k * ‖s k‖ ≤ sigmaMaxAR2 P L₂ * ‖s k‖ :=
    mul_le_mul_of_nonneg_right hσmax (norm_nonneg _)
  nlinarith

/-- The constant `κ^T_AR2 = 6 (L_{f,2} + max(1, θ₁, θ₂) + σ_max)³/(η₁ σ_min)` of
Theorem 3.3.9. -/
noncomputable def kappaTAR2 (P : AR2Params) (L : ℝ) : ℝ :=
  6 * (L + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L) ^ 3 / (P.η₁ * P.σmin)

/-- The decrease at a successful AR2 iteration `k` with `ε₂ = e` such that the test fails at
`x_{k+1}`: `f(x_k) - f(x_{k+1}) ≥ min(ε₁^{3/2}, e³)/κ^T_AR2`. -/
theorem ar2_decrease_second (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ (some e) x s σ) {k : ℕ}
    (hk : ∀ j ≤ k + 1, ¬ stopTest f ε₁ (some e) (x j)) (hs : P.η₁ ≤ taylorRatio f 2 x s k) :
    min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂ ≤ f (x k) - f (x (k + 1)) := by
  have hk' : ∀ j ≤ k, ¬ stopTest f ε₁ (some e) (x j) := fun j hj => hk j (hj.trans k.le_succ)
  set C := L₂ + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L₂
  have hσ := h.sigma_pos fun j hj => hk' j hj.le
  have hσmin := h.sigmaMin_le fun j hj => hk' j hj.le
  have hε := h.ε₁_pos
  have he : 0 < e := h.ε₂_pos e rfl
  have hL := hf.pos
  have hsm := arSigmaMax_pos P.ar L₂
  have hθ1 : P.θ₁ ≤ max 1 (max P.θ₁ P.θ₂) := (le_max_left _ _).trans (le_max_right _ _)
  have hθ2 : P.θ₂ ≤ max 1 (max P.θ₁ P.θ₂) := (le_max_right _ _).trans (le_max_right _ _)
  have h1 : 1 ≤ max 1 (max P.θ₁ P.θ₂) := le_max_left _ _
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hC : 0 < C := by linarith
  -- the step is long
  have hstep : min (√ε₁) e / C ≤ ‖s k‖ := by
    rcases not_stopTest_some.1 (hk (k + 1) le_rfl) with hg | hlam
    · have h3 := lemma_3_3_3 hf h hk' hs
      have hC' : L₂ + P.θ₁ + sigmaMaxAR2 P L₂ ≤ C := by simp only [C]; linarith
      have hsm' : 0 < sigmaMaxAR2 P L₂ := hsm
      have hθ₁ := P.θ₁_pos
      have hD : 0 < L₂ + P.θ₁ + sigmaMaxAR2 P L₂ := by linarith
      have : ε₁ / C ^ 2 ≤ ‖s k‖ ^ 2 := by
        refine le_trans ?_ h3
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hD]
        have hCC : C ≤ C ^ 2 := by nlinarith
        have h4 : ε₁ * (L₂ + P.θ₁ + sigmaMaxAR2 P L₂) ≤ ε₁ * C ^ 2 :=
          mul_le_mul_of_nonneg_left (hC'.trans hCC) hε.le
        have h5 : ε₁ * C ^ 2 ≤ ‖gradient f (x (k + 1))‖ * C ^ 2 :=
          mul_le_mul_of_nonneg_right hg.le (by positivity)
        nlinarith [sq_nonneg C, norm_nonneg (gradient f (x (k + 1)))]
      have hsq : (√ε₁ / C) ^ 2 ≤ ‖s k‖ ^ 2 := by
        rw [div_pow, Real.sq_sqrt hε.le]; exact this
      exact (div_le_div_of_nonneg_right (min_le_left _ _) hC.le).trans
        ((pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq)
    · have hneg : Chapter01.hessianMinEig f (x (k + 1)) < 0 := hlam.trans (neg_neg_of_pos he)
      have h8 := lemma_3_3_8 hf h (Option.some_ne_none e) hk' hs hneg
      refine le_trans ?_ h8
      rw [abs_of_neg hneg]
      exact div_le_div₀ (by linarith) ((min_le_right _ _).trans (by linarith))
        (by linarith [P.θ₂_pos]) (by simp only [C]; linarith)
  -- the decrease
  obtain ⟨-, hdec⟩ := h.run.sub_ge_of_succ_taylor (IsARRun.forall_le_not_stop_iff.2 hk')
    (h.step hk').1 hs
  norm_num [Nat.factorial] at hdec
  have hmin3 : min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) = min (√ε₁) e ^ 3 := by
    have : ε₁ ^ (3 / 2 : ℝ) = √ε₁ ^ 3 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
    rw [this]
    rcases le_total (√ε₁) e with h' | h'
    · rw [min_eq_left h', min_eq_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) h' 3)]
    · rw [min_eq_right h', min_eq_right (pow_le_pow_left₀ he.le h' 3)]
  have hm0 : 0 ≤ min (√ε₁) e := le_min (Real.sqrt_nonneg _) he.le
  have hη := P.η₁_pos
  have hsmin := P.σmin_pos
  have key : min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂ =
      P.η₁ * (P.σmin / 6 * (min (√ε₁) e / C) ^ 3) := by
    rw [hmin3, kappaTAR2, show L₂ + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L₂ = C from rfl]
    field_simp
  rw [key]
  calc P.η₁ * (P.σmin / 6 * (min (√ε₁) e / C) ^ 3) ≤ P.η₁ * (σ k / 6 * ‖s k‖ ^ 3) := by
        gcongr
    _ ≤ _ := hdec

theorem kappaTAR2_pos {P : AR2Params} {L : ℝ} (hL : 0 ≤ L) : 0 < kappaTAR2 P L := by
  have := arSigmaMax_pos P.ar L; have := P.η₁_pos; have := P.σmin_pos
  have : 1 ≤ max 1 (max P.θ₁ P.θ₂) := le_max_left _ _
  have : 0 < L + max 1 (max P.θ₁ P.θ₂) + sigmaMaxAR2 P L := by
    have : 0 < sigmaMaxAR2 P L := arSigmaMax_pos P.ar L
    linarith
  unfold kappaTAR2
  positivity

/-- **Theorem 3.3.9** of [cartis2022evaluation] (second-order complexity of AR2). Under f.Bb and
f.HL, for `ε₁ ∈ (0, 1]` and `ε₂ = e > 0`, every AR2 run terminates at an iteration `k_ε` (an
`(ε₁, ε₂)`-approximate second-order minimizer (3.3.4)) after at most
`κ^D (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + κ^F` evaluations of `f` (3.3.29) and at most
`κ^T (f(x₀) - f_low)/min(ε₁^{3/2}, ε₂³) + 2` evaluations of `∇f` and `∇²f` (3.3.30), with
`κ^T = kappaTAR2`, `κ^D = κ^T (1 + |log γ₁|/log γ₂)` and `κ^F = kappaCAR2`. (The book's
`ε₂ ≤ 1` is not needed.) -/
theorem theorem_3_3_9 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionHL f L₂)
    (h : algorithm_3_3_1 f P ε₁ (some e) x s σ) :
    ∃ kε, IsFirstHit (fun k => stopTest f ε₁ (some e) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaTAR2 P L₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
          min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + kappaCAR2 P L₂ ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 2 x s k) kε : ℝ) ≤
        kappaTAR2 P L₂ * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) + 2 := by
  have hκ := kappaTAR2_pos (P := P) hf.nonneg
  have hε := h.ε₁_pos
  have he : 0 < e := h.ε₂_pos e rfl
  have hM : 0 < min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) := lt_min (by positivity) (by positivity)
  set δ := min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) / kappaTAR2 P L₂
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ =
      kappaTAR2 P L₂ * (f (x 0) - flow) / min (ε₁ ^ (3 / 2 : ℝ)) (e ^ 3) := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := sigmaMaxAR2 P L₂)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_3_3_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      ((lt_of_le_of_lt (by
          have := h.sigma_pos (fun j hj => (IsARRun.forall_le_not_stop_iff.1 hk) j hj.le)
          positivity) (lemma_3_3_1 h (IsARRun.forall_le_not_stop_iff.1 hk)))))
    (fun k _ => hb (x k))
    (fun k hk hs => ar2_decrease_second hf h (IsARRun.forall_le_not_stop_iff.1 hk) hs)
  rw [hNδ] at hF hD
  refine ⟨kε, IsARRun.isFirstHit_stop_iff.1 hk, ?_, hD⟩
  rw [kappaCAR2, ← sigmaMaxAR2_div_eq]
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

end SecondOrder

/-! ### Sharpness: Theorems 3.3.6 and 3.3.10 -/

section Sharpness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-- The AR2 model of a ridge function on `ℝ¹`: with `a = ⟪e₀, x⟫` and `t = ⟪e₀, s⟫`,
`m(s) = G(a) + G'(a) t + G''(a) t²/2 + σ/6 |t|³`. -/
theorem ar2Model_ridge {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (x s : EuclideanSpace ℝ (Fin 1))
    (σ : ℝ) :
    ar2Model (ridge G e₀) x σ s = G ⟪e₀, x⟫ + deriv G ⟪e₀, x⟫ * ⟪e₀, s⟫ +
      iteratedDeriv 2 G ⟪e₀, x⟫ * ⟪e₀, s⟫ ^ 2 / 2 + σ / 6 * |⟪e₀, s⟫| ^ 3 := by
  rw [ar2Model_apply, taylorPolynomial_two_ridge hG, norm_eq_abs_inner_e₀]

/-- The one-dimensional jets of the sharpness examples: the `q`-th derivative is `-α` and the
other derivatives of order `1, 2` vanish. -/
def IsSpikeJet (G : ℝ → ℝ) (q : ℕ) (a α : ℝ) : Prop :=
  iteratedDeriv q G a = -α ∧ ∀ j, 1 ≤ j → j ≤ 2 → j ≠ q → iteratedDeriv j G a = 0

section Spike

variable {G : ℝ → ℝ} {q : ℕ} {x : EuclideanSpace ℝ (Fin 1)} {α : ℝ}

/-- At a spike jet, `T_{f,2}(x, s) = G(a) - α t^q/q!`. -/
theorem taylorPolynomial_two_ridge_spike (hG : ContDiff ℝ 2 G) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : IsSpikeJet G q ⟪e₀, x⟫ α) (s : EuclideanSpace ℝ (Fin 1)) :
    taylorPolynomial (ridge G e₀) 2 x s = G ⟪e₀, x⟫ - α * ⟪e₀, s⟫ ^ q / q.factorial := by
  rw [taylorPolynomial_two_ridge hG]
  obtain ⟨h1, h2⟩ := hd
  interval_cases q
  · have hd2 := h2 2 (by norm_num) le_rfl (by norm_num)
    rw [iteratedDeriv_one] at h1
    rw [h1, hd2]; norm_num
    ring
  · have hd1 := h2 1 le_rfl (by norm_num) (by norm_num)
    rw [iteratedDeriv_one] at hd1
    rw [hd1, h1]; norm_num [Nat.factorial]
    ring

/-- At a spike jet the AR2 model is `G(a) + negMonomialRegModel 2 q σ α t`. -/
theorem ar2Model_ridge_spike (hG : ContDiff ℝ 2 G) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : IsSpikeJet G q ⟪e₀, x⟫ α) (σ : ℝ) (s : EuclideanSpace ℝ (Fin 1)) :
    ar2Model (ridge G e₀) x σ s = G ⟪e₀, x⟫ + negMonomialRegModel 2 q σ α ⟪e₀, s⟫ := by
  rw [ar2Model_apply, taylorPolynomial_two_ridge_spike hG hq hq2 hd, norm_eq_abs_inner_e₀,
    negMonomialRegModel]
  norm_num [Nat.factorial]
  ring

theorem taylorDecrement_ridge_spike (hG : ContDiff ℝ 2 G) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : IsSpikeJet G q ⟪e₀, x⟫ α) (s : EuclideanSpace ℝ (Fin 1)) :
    (ftaylorSeries ℝ (ridge G e₀) x).taylorDecrement 2 s = α * ⟪e₀, s⟫ ^ q / q.factorial := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_two_ridge_spike hG hq hq2 hd, taylorPolynomial_two_ridge_spike hG hq hq2 hd]
  simp only [inner_zero_right]
  rw [zero_pow (by omega)]
  ring

end Spike

/-- **AR2 runs on one-dimensional spike data** (the mechanism of Theorems 3.3.6 and 3.3.10). Let
`G` be `C²` with spike jets `G^{(q)}(x_k) = -α_k < 0` (other derivatives of order `1, 2` zero) at
points `x_k` (`k < K`, `q ∈ {1, 2}`), spaced by the global minimizers
`t_k = (α_k/λ)^{1/(3-q)}`, `λ = σ₀ (q-1)!/2`, of the one-dimensional models
`-α_k t^q/q! + σ₀ |t|³/6`, with `G(x_{k+1}) = G(x_k) - α_k t_k^q/q!`. If the termination test
holds at `x_k e₀` (`k ≤ K`) exactly when `k = K`, then the points `x_k e₀` form an AR2 run on
`ridge G e₀` with `σ_k = σ₀`, steps `t_k e₀` that are global minimizers of the models, and
`ρ_k = 1`, terminating exactly at iteration `K`; the iterates are `x_k e₀`. -/
theorem exists_ar2_ridge_run (P : AR2Params) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1)
    {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) {q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) {xr α : ℕ → ℝ} {K : ℕ} (hα : ∀ k < K, 0 < α k)
    (hd : ∀ k < K, IsSpikeJet G q (xr k) (α k))
    (hx : ∀ k < K, xr (k + 1) = xr k + (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
      (1 / ((2 - q + 1 : ℕ) : ℝ)))
    (hval : ∀ k < K, G (xr (k + 1)) = G (xr k) - α k * (xr (k + 1) - xr k) ^ q / q.factorial)
    (htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ ε₂ (xr k • e₀) ↔ K ≤ k)) :
    ∃ x s : ℕ → EuclideanSpace ℝ (Fin 1), ∃ σ : ℕ → ℝ, x 0 = xr 0 • e₀ ∧
      algorithm_3_3_1 (ridge G e₀) P ε₁ ε₂ x s σ ∧ (∀ k, σ k = P.σ₀) ∧
      (∀ k < K, IsMinOn (ar2Model (ridge G e₀) (x k) (σ k)) univ (s k) ∧
        taylorRatio (ridge G e₀) 2 x s k = 1) ∧
      IsFirstHit (fun k => stopTest (ridge G e₀) ε₁ ε₂ (x k)) K ∧ ∀ k, x k = xr k • e₀ := by
  set f := ridge G e₀
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => xr k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => (xr (k + 1) - xr k) • e₀
  have hσ₀ := P.σ₀_pos
  have hxs : ∀ k, x k + s k = x (k + 1) := fun k => by simp only [x, s, ← add_smul]; ring_nf
  have hdx : ∀ k < K, IsSpikeJet G q ⟪e₀, x k⟫ (α k) := fun k hk => by
    rw [inner_e₀_smul]; exact hd k hk
  -- the step is the global minimizer
  have ht : ∀ k < K, ⟪e₀, s k⟫ = (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
      (1 / ((2 - q + 1 : ℕ) : ℝ)) := fun k hk => by
    simp only [s]; rw [inner_e₀_smul, hx k hk]; ring
  have hmin : ∀ k < K, IsMinOn (ar2Model f (x k) P.σ₀) univ (s k) := fun k hk => by
    obtain ⟨hm, -, -⟩ := isMinOn_neg_monomial_add_regularization (p := 2) hq hq2 hσ₀ (hα k hk)
    intro y _
    simp only [mem_ofPred_eq]
    rw [ar2Model_ridge_spike hG hq hq2 (hdx k hk), ar2Model_ridge_spike hG hq hq2 (hdx k hk),
      ht k hk]
    exact (add_le_add_iff_left _).2 (isMinOn_iff.1 hm _ (mem_univ _))
  -- the model decreases
  have htpos : ∀ k < K, 0 < ⟪e₀, s k⟫ := fun k hk => by
    rw [ht k hk]
    have := hα k hk
    apply Real.rpow_pos_of_pos
    positivity
  have hdec : ∀ k < K, ar2Model f (x k) P.σ₀ (s k) < ar2Model f (x k) P.σ₀ 0 := fun k hk => by
    obtain ⟨-, hv, -⟩ := isMinOn_neg_monomial_add_regularization (p := 2) hq hq2 hσ₀ (hα k hk)
    rw [ar2Model_ridge_spike hG hq hq2 (hdx k hk), ar2Model_ridge_spike hG hq hq2 (hdx k hk),
      ht k hk, hv, inner_zero_right, negMonomialRegModel, zero_pow (by omega), abs_zero,
      zero_pow (by norm_num)]
    have h1 : (0 : ℝ) < ((2 - q + 1 : ℕ) : ℝ) / ((2 + 1) * q.factorial) := by positivity
    have h2 : 0 < (α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
        (1 / ((2 - q + 1 : ℕ) : ℝ)) := by rw [← ht k hk]; exact htpos k hk
    have := hα k hk
    have : 0 < ((2 - q + 1 : ℕ) : ℝ) / ((2 + 1) * q.factorial) * α k *
        ((α k / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^
          (1 / ((2 - q + 1 : ℕ) : ℝ))) ^ q := by positivity
    simp only [neg_mul, mul_zero, zero_div, add_zero]
    linarith
  -- the ratio
  have hratio : ∀ k < K, taylorRatio f 2 x s k = 1 := fun k hk => by
    have hts : ⟪e₀, s k⟫ = xr (k + 1) - xr k := by simp only [s]; rw [inner_e₀_smul]
    have hT := taylorDecrement_ridge_spike hG hq hq2 (hdx k hk) (s k)
    have hpos : 0 < α k * (xr (k + 1) - xr k) ^ q / q.factorial := by
      have := hα k hk; have := htpos k hk; rw [hts] at this; positivity
    rw [taylorRatio_def, hT, hts, reductionRatio_def, hxs]
    simp only [f, x, ridge_apply, inner_e₀_smul]
    rw [hval k hk, sub_sub_cancel, div_self hpos.ne']
  have hhit : IsFirstHit (fun k => stopTest f ε₁ ε₂ (x k)) K :=
    ⟨(htest K le_rfl).2 le_rfl, fun j hj h => absurd ((htest j hj.le).1 h) (not_le.2 hj)⟩
  have hbefore : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => stopTest f ε₁ ε₂ (x k))
      (fun _ => False) j) → k < K := fun k hk =>
    not_le.1 fun hle => (IsARRun.forall_le_not_stop_iff.1 hk) K hle hhit.test
  refine ⟨x, s, fun _ => P.σ₀, rfl, ⟨hε₁, hε₁1, hε₂, ⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩⟩,
    fun _ => rfl, fun k hk => ⟨hmin k hk, hratio k hk⟩, hhit, fun _ => rfl⟩
  · have hk' : k < K := by
      by_contra hle
      rcases (not_lt.1 hle).eq_or_lt with heq | hlt
      · exact h1 (heq ▸ hhit.test)
      · exact hk K hlt (Or.inl hhit.test)
    exact ar2Step_of_isMinOn P ε₂ (hmin k hk') (hdec k hk')
  · have hk' := hbefore k hk
    change ARAcceptance P.ar (taylorRatio f 2 x s k) (x k) (s k) (x (k + 1)) P.σ₀ P.σ₀
    rw [← hxs, hratio k hk']
    exact arAcceptance_of_one_le P.ar le_rfl _ _ P.ar.σmin_le_σ₀ hσ₀.le

/-- The termination index `⌈ε^{-3/(3-q)}⌉` of the one-dimensional AR2 examples
(`q = 1`: `⌈ε^{-3/2}⌉`; `q = 2`: `⌈ε^{-3}⌉`). -/
noncomputable def ar2SlowK (q : ℕ) (ε : ℝ) : ℕ :=
  ⌈ε ^ (-((2 + 1 : ℝ) / ((2 - q + 1 : ℕ) : ℝ)))⌉₊

/-- The magnitudes `α_k = ε + ε (k_ε - k)/k_ε` of the spike derivatives of the AR2 examples. -/
noncomputable def ar2SlowAlpha (ε : ℝ) (K k : ℕ) : ℝ := ε + ε * ((K : ℝ) - k) / K

theorem ar2SlowK_one (ε : ℝ) : ar2SlowK 1 ε = ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  rw [ar2SlowK]; norm_num

theorem ar2SlowK_two (ε : ℝ) : ar2SlowK 2 ε = ⌈ε ^ (-(3 : ℝ))⌉₊ := by
  rw [ar2SlowK]; norm_num

theorem ar2SlowK_pos {q : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < ar2SlowK q ε :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)

/-- `α_k ≥ ε`, with equality iff `k = k_ε` (for `k ≤ k_ε`). -/
theorem ar2SlowAlpha_le_iff {ε : ℝ} (hε : 0 < ε) {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    ar2SlowAlpha ε K k ≤ ε ↔ K ≤ k := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  rw [ar2SlowAlpha, add_le_iff_nonpos_right, div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hK')
    · have : (K : ℝ) - k ≤ 0 := by nlinarith
      exact_mod_cast (show (K : ℝ) ≤ k by linarith)
  · intro h
    have : (K : ℝ) ≤ k := by exact_mod_cast h
    right; exact ⟨by nlinarith, hK'.le⟩

theorem ar2SlowAlpha_pos {ε : ℝ} (hε : 0 < ε) {K k : ℕ} (hK : 0 < K) (hk : k ≤ K) :
    0 < ar2SlowAlpha ε K k := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  have : 0 ≤ ε * ((K : ℝ) - k) / K := div_nonneg (mul_nonneg hε.le (by linarith)) hK'.le
  rw [ar2SlowAlpha]; linarith

/-- **The one-dimensional AR2 examples** (the data of Theorem 12.2.15 with `p = 2`,
[cartis2022evaluation] §12.2.2.4, `Optimization.exists_slowTaylorOrder_interpolant`). For
`q ∈ {1, 2}` there are constants `L₁, L₂ ≥ 1`, `B ≥ 0` (depending on `σ₀` only) such that for every
`ε ∈ (0, 1]` there are a `C²` function `G` (whose ridge `f` on `ℝ¹` satisfies f.Bb, f.gL, f.HL and
`|f| ≤ B`) and points `x_0 = 0, …, x_{k_ε}` with spike jets `G^{(q)}(x_k) = -α_k`, spaced by the
global minimizers of the AR2 models with `σ = σ₀`, and with `G(x_{k+1}) = T_{f,2}(x_k, s_k)`. -/
theorem exists_ar2_slow_data (P : AR2Params) {q : ℕ} (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ∃ L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (G : ℝ → ℝ) (xr : ℕ → ℝ), ContDiff ℝ 2 G ∧
        Chapter02.AssumptionBb (ridge G e₀) (-B) ∧ Chapter02.AssumptionGL (ridge G e₀) L₁ ∧
        AssumptionHL (ridge G e₀) L₂ ∧ (∀ y, |ridge G e₀ y| ≤ B) ∧ xr 0 = 0 ∧
        (∀ k ≤ ar2SlowK q ε, IsSpikeJet G q (xr k) (ar2SlowAlpha ε (ar2SlowK q ε) k)) ∧
        (∀ k < ar2SlowK q ε, xr (k + 1) = xr k + (ar2SlowAlpha ε (ar2SlowK q ε) k /
          (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial)) ^ (1 / ((2 - q + 1 : ℕ) : ℝ))) ∧
        ∀ k < ar2SlowK q ε, G (xr (k + 1)) = G (xr k) -
          ar2SlowAlpha ε (ar2SlowK q ε) k * (xr (k + 1) - xr k) ^ q / q.factorial := by
  have hσ₀ := P.σ₀_pos
  set c : ℝ := ((2 : ℕ).factorial : ℝ) / (P.σ₀ * (q - 1).factorial)
  have hc : 0 < c := by positivity
  have hcα : ∀ α : ℝ, c * α = α / (P.σ₀ * (q - 1).factorial / (2 : ℕ).factorial) := fun α => by
    simp only [c]; field_simp
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowTaylorOrder_interpolant (p := 2) hq hq2 hc
  refine ⟨max B 1, max L 1, B, le_max_right _ _, le_max_right _ _, hB, fun ε hε hε1 => ?_⟩
  set K := ar2SlowK q ε
  set xr : ℕ → ℝ := fun k => ∑ j ∈ range k,
    (c * (ε + ε * ((K : ℝ) - j) / K)) ^ (1 / ((2 - q + 1 : ℕ) : ℝ))
  obtain ⟨G, hG, hGL, hGB, hGk, hGv⟩ := H ε K xr hε hε1 rfl
    (fun k _ => by simp only [xr, sum_range_succ])
  have hG2 : ContDiff ℝ 2 G := by exact_mod_cast hG
  obtain ⟨hb, hgl, -, hhl, -⟩ := ridge_assumptions_two hG2 hGL hGB
  refine ⟨G, xr, hG2, hb, hgl, hhl, fun y => ?_, by simp [xr], fun k hk => hGk k hk,
    fun k _ => ?_, fun k hk => hGv k hk⟩
  · have := hGB 0 (by norm_num) ⟪e₀, y⟫
    rwa [iteratedDeriv_zero] at this
  · simp only [xr, sum_range_succ, ar2SlowAlpha, hcα]

/-- **Theorem 3.3.6** of [cartis2022evaluation] (slow first-order convergence of AR2). For all AR2
constants there are `f_low`, `L_{f,1}, L_{f,2} ≥ 1` and `B` such that for every `ε₁ ∈ (0, 1]`
there are `f : ℝ¹ → ℝ` satisfying f.Bb, f.gL, f.HL and `|f| ≤ B`, and an AR2 run with `ε₂ = +∞`
from `x₀ = 0` with `σ_k = σ₀`, steps that are global minimizers of the cubic model and `ρ_k = 1`
(every iteration very successful), which terminates exactly at iteration `k_ε = ⌈ε₁^{-3/2}⌉`
(after `k_ε + 1` evaluations of `f`, `∇f` and `∇²f`). -/
theorem theorem_3_3_6 (P : AR2Params) :
    ∃ flow L₁ L₂ B : ℝ, 1 ≤ L₁ ∧ 1 ≤ L₂ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧
        Chapter02.AssumptionGL f L₁ ∧ AssumptionHL f L₂ ∧ (∀ y, |f y| ≤ B) ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε none x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε ^ (-(3 / 2 : ℝ))⌉₊, IsMinOn (ar2Model f (x k) (σ k)) univ (s k) ∧
            taylorRatio f 2 x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) ⌈ε ^ (-(3 / 2 : ℝ))⌉₊ := by
  obtain ⟨L₁, L₂, B, hL₁, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  refine ⟨-B, L₁, L₂, B, hL₁, hL₂, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hgl, hhl, hB, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := ar2SlowK_pos (q := 1) hε
  set K := ar2SlowK 1 ε
  have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε none (xr k • e₀) ↔ K ≤ k) := fun k hk => by
    rw [stopTest_none, gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul,
      ← iteratedDeriv_one, (hd k hk).1, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_of_nonneg
      (ar2SlowAlpha_pos hε hK hk).le]
    exact ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨x, s, σ, hx0', hrun, hσ, hmin, hhit, -⟩ := exists_ar2_ridge_run P hε hε1
    (ε₂ := none) (fun _ h => absurd h (by simp)) le_rfl (by norm_num) hG
    (fun k hk => ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  refine ⟨ridge G e₀, hb, hgl, hhl, hB, x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_, ?_⟩
  · rw [← ar2SlowK_one]; exact hmin
  · rw [← ar2SlowK_one]; simpa only [stopTest_none] using hhit

/-- **Theorem 3.3.10** of [cartis2022evaluation] (slow second-order convergence of AR2). For all
AR2 constants there are `f_low` and `L_{f,2} ≥ 1` such that for all `ε₁, ε₂ ∈ (0, 1]` there are
`f : ℝ¹ → ℝ` satisfying f.Bb and f.HL and an AR2 run from `x₀ = 0` with `σ_k = σ₀` which
terminates exactly at iteration `max(⌈ε₁^{-3/2}⌉, ⌈ε₂^{-3}⌉)`. (If `⌈ε₁^{-3/2}⌉ ≥ ⌈ε₂^{-3}⌉` the
example of Theorem 3.3.6 (zero curvature) is used; otherwise a negative-curvature example with zero
gradients.) -/
theorem theorem_3_3_10 (P : AR2Params) :
    ∃ flow L₂ : ℝ, 1 ≤ L₂ ∧ ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < ε₂ → ε₂ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionHL f L₂ ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_3_3_1 f P ε₁ (some ε₂) x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (fun k => stopTest f ε₁ (some ε₂) (x k))
            (max ⌈ε₁ ^ (-(3 / 2 : ℝ))⌉₊ ⌈ε₂ ^ (-(3 : ℝ))⌉₊) := by
  obtain ⟨L₁, L₂, B, -, hL₂, -, H⟩ := exists_ar2_slow_data P le_rfl (by norm_num : 1 ≤ 2)
  obtain ⟨L₁', L₂', B', -, -, -, H'⟩ := exists_ar2_slow_data P (q := 2) (by norm_num) le_rfl
  refine ⟨-max B B', max L₂ L₂', hL₂.trans (le_max_left _ _),
    fun ε₁ ε₂ hε₁ hε₁1 hε₂ hε₂1 => ?_⟩
  rcases le_total ⌈ε₂ ^ (-(3 : ℝ))⌉₊ ⌈ε₁ ^ (-(3 / 2 : ℝ))⌉₊ with hle | hle
  · -- the first-order example
    rw [max_eq_left hle]
    obtain ⟨G, xr, hG, hb, -, hhl, -, hx0, hd, hx, hv⟩ := H ε₁ hε₁ hε₁1
    have hK := ar2SlowK_pos (q := 1) hε₁
    set K := ar2SlowK 1 ε₁
    have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ (some ε₂) (xr k • e₀) ↔ K ≤ k) :=
      fun k hk => by
        rw [stopTest_some, IsApproxSecondOrderMinimizer, hessianMinEig_ridge hG, inner_e₀_smul,
          ((hd k hk).2 2 (by norm_num) le_rfl (by norm_num)),
          gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul, ← iteratedDeriv_one,
          (hd k hk).1, norm_smul, norm_e₀, mul_one, norm_neg,
          Real.norm_of_nonneg (ar2SlowAlpha_pos hε₁ hK hk).le, ← ar2SlowAlpha_le_iff hε₁ hK hk]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
    obtain ⟨x, s, σ, hx0', hrun, hσ, -, hhit, -⟩ := exists_ar2_ridge_run P hε₁ hε₁1
      (ε₂ := some ε₂) (by simpa using hε₂) le_rfl (by norm_num) hG
      (fun k hk => ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv htest
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B B']),
      hhl.mono (le_max_left _ _), x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_⟩
    rw [← ar2SlowK_one]; exact hhit
  · -- the negative-curvature example
    rw [max_eq_right hle]
    obtain ⟨G, xr, hG, hb, -, hhl, -, hx0, hd, hx, hv⟩ := H' ε₂ hε₂ hε₂1
    have hK := ar2SlowK_pos (q := 2) hε₂
    set K := ar2SlowK 2 ε₂
    have htest : ∀ k ≤ K, (stopTest (ridge G e₀) ε₁ (some ε₂) (xr k • e₀) ↔ K ≤ k) :=
      fun k hk => by
        have hg1 := (hd k hk).2 1 le_rfl (by norm_num) (by norm_num)
        rw [iteratedDeriv_one] at hg1
        rw [stopTest_some, IsApproxSecondOrderMinimizer, hessianMinEig_ridge hG, inner_e₀_smul,
          (hd k hk).1, gradient_ridge (hG.differentiable (by norm_num)), inner_e₀_smul, hg1,
          zero_smul, norm_zero, neg_le_neg_iff, ← ar2SlowAlpha_le_iff hε₂ hK hk]
        exact ⟨fun h => h.2, fun h => ⟨hε₁.le, h⟩⟩
    obtain ⟨x, s, σ, hx0', hrun, hσ, -, hhit, -⟩ := exists_ar2_ridge_run P hε₁ hε₁1
      (ε₂ := some ε₂) (by simpa using hε₂) (by norm_num) le_rfl hG
      (fun k hk => ar2SlowAlpha_pos hε₂ hK hk.le) (fun k hk => hd k hk.le) hx hv htest
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_right B B']),
      hhl.mono (le_max_right _ _), x, s, σ, by rw [hx0', hx0, zero_smul], hrun, hσ, ?_⟩
    rw [← ar2SlowK_two]; exact hhit

end Sharpness

/-! ### Deprecated aliases (moved to the backbone) -/

@[deprecated IsARRun.forall_lt_not_stop_iff (since := "2026-10-26")]
alias not_stop_iff := IsARRun.forall_lt_not_stop_iff

@[deprecated IsARRun.forall_le_not_stop_iff (since := "2026-10-26")]
alias not_stop_le_iff := IsARRun.forall_le_not_stop_iff

@[deprecated IsARRun.isFirstHit_stop_iff (since := "2026-10-26")]
alias isFirstHit_stop_iff := IsARRun.isFirstHit_stop_iff

@[deprecated Optimization.arAcceptance_of_one_le (since := "2026-10-26")]
alias arAcceptance_of_one_le := Optimization.arAcceptance_of_one_le

end CartisGouldToint.Chapter03
