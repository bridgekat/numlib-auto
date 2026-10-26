import Numlib.Optimization.ModelBased.ARRun
import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.CartisGouldToint.Chapter02.Section02

/-!
# Cartis–Gould–Toint §2.4: The adaptive-regularization method

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §2.4: the first-order
adaptive-regularization algorithm AR1 on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

The model (2.4.1) is `m_k(s) = T_{f,1}(x_k, s) + ½ σ_k ‖s‖²`, the regularized Taylor model
`Optimization.regularizedModel (ftaylorSeries ℝ f x_k) 1 σ_k` (`ar1Model`); the ratio (2.4.3) is
`Optimization.taylorRatio f 1 x s`. AR1 is an instance of the generic adaptive-regularization
run `Optimization.IsARRun` (Steps 3–4 being `Optimization.ARAcceptance`, the update (2.4.4)
`Optimization.ARUpdate`). Section 2.5 contains no numbered results.

## Main definitions

* `ARParams` — the constants (2.4.2) (also used by AR2 and ARp in later chapters).
* `ar1Model f x σ` — the model (2.4.1).
* `algorithm_2_4_1 f P ε x s σ` — Algorithm 2.4.1 (AR1); `exists_algorithm_2_4_1`.
* `sigmaMaxAR1`, `kappaSAR1`, `kappaAAR1`, `kappaCAR1` — the constants of (2.4.9), (2.4.11)
  and Theorem 2.4.4.

## Main results

* `ar1_step_eq` — (2.4.5)–(2.4.7): the step is `s = -∇f(x)/σ`, the Taylor decrease is
  `‖∇f(x)‖²/σ` and `ρ = σ (f(x) - f(x+s))/‖∇f(x)‖²`.
* `lemma_2_4_1`, `lemma_2_4_2`, `lemma_2_4_3` — Lemmas 2.4.1–2.4.3.
* `theorem_2_4_4` — Theorem 2.4.4, with the book's constants.
* `theorem_2_4_5` — Theorem 2.4.5, sharpness.

## Notes

* The "reasonable values" given after Algorithm 2.4.1 (`γ₁ = 2`, `γ₂ = γ₃ = 0.5`) contradict
  (2.4.2); they are not used.
* The proof of Lemma 2.4.3 assumes `‖∇f(x_j)‖ > ε` for `j ∈ [1:k]`; `j ∈ [0:k]` is meant (and
  used here).
-/

open Set Finset
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-- The constants of adaptive-regularization methods ([cartis2022evaluation], (2.4.2)):
`σ₀ > 0`, `σ_min ∈ (0, σ₀]`, `0 < η₁ ≤ η₂ < 1` and `0 < γ₁ < 1 < γ₂ < γ₃`. -/
structure ARParams extends Optimization.ARParams where
  /-- `σ_min > 0`. -/
  σmin_pos : 0 < σmin
  /-- `γ₂ < γ₃`. -/
  γ₂_lt_γ₃ : γ₂ < γ₃

/-- The regularized model (2.4.1) of AR1: `m(s) = T_{f,1}(x, s) + ½ σ ‖s‖²`. -/
noncomputable def ar1Model (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  regularizedModel (ftaylorSeries ℝ f x) 1 σ

section Model

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)} {σ : ℝ}

/-- The model (2.4.1): `m(s) = f(x) + ⟪∇f(x), s⟫ + ½ σ ‖s‖²`. -/
theorem ar1Model_apply :
    ar1Model f x σ s = f x + ⟪gradient f x, s⟫ + 1 / 2 * σ * ‖s‖ ^ 2 := by
  rw [ar1Model, regularizedModel_def, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_one_eq_inner,
    show ((Nat.factorial (1 + 1) : ℕ) : ℝ) = 2 by norm_num [Nat.factorial]]
  ring

/-- The first-order Taylor decrease: `T_{f,1}(x, 0) - T_{f,1}(x, s) = -⟪∇f(x), s⟫`. -/
theorem taylorDecrement_one :
    (ftaylorSeries ℝ f x).taylorDecrement 1 s = -⟪gradient f x, s⟫ := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_one_eq_inner, taylorPolynomial_one_eq_inner, inner_zero_right]
  ring

/-- Completing the square: `m(s) = f(x) - ‖∇f(x)‖²/(2σ) + ½ σ ‖s + σ⁻¹ ∇f(x)‖²`. -/
theorem ar1Model_eq_sq (hσ : σ ≠ 0) :
    ar1Model f x σ s = f x - ‖gradient f x‖ ^ 2 / (2 * σ) +
      1 / 2 * σ * ‖s + σ⁻¹ • gradient f x‖ ^ 2 := by
  rw [ar1Model_apply, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm]
  field_simp
  ring

/-- **(2.4.5)–(2.4.7)** of [cartis2022evaluation]. For `σ > 0`: the model (2.4.1) has the unique
global minimizer `s = -∇f(x)/σ`; the Taylor decrease at it is `‖∇f(x)‖²/σ` (2.4.6); and the ratio
(2.4.3) is `σ (f(x) - f(x+s))/‖∇f(x)‖²` (2.4.7). -/
theorem ar1_step_eq (hσ : 0 < σ) :
    (IsMinOn (ar1Model f x σ) univ s ↔ s = -(σ⁻¹ • gradient f x)) ∧
      (ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x)) =
        ‖gradient f x‖ ^ 2 / σ ∧
      reductionRatio f x (-(σ⁻¹ • gradient f x))
          ((ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x))) =
        σ * (f x - f (x + -(σ⁻¹ • gradient f x))) / ‖gradient f x‖ ^ 2 := by
  have hdec : (ftaylorSeries ℝ f x).taylorDecrement 1 (-(σ⁻¹ • gradient f x)) =
      ‖gradient f x‖ ^ 2 / σ := by
    rw [taylorDecrement_one, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  refine ⟨⟨fun hmin => ?_, fun hs => ?_⟩, hdec, ?_⟩
  · have := hmin (mem_univ (-(σ⁻¹ • gradient f x)))
    simp only [mem_ofPred_eq] at this
    rw [ar1Model_eq_sq hσ.ne', ar1Model_eq_sq hσ.ne', neg_add_cancel, norm_zero] at this
    have h0 : ‖s + σ⁻¹ • gradient f x‖ ^ 2 ≤ 0 := by nlinarith
    have : s + σ⁻¹ • gradient f x = 0 := by
      have := le_antisymm h0 (sq_nonneg _)
      exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 this)
    exact eq_neg_of_add_eq_zero_left this
  · intro y _
    simp only [mem_ofPred_eq]
    rw [ar1Model_eq_sq hσ.ne', ar1Model_eq_sq hσ.ne', hs, neg_add_cancel, norm_zero]
    have : 0 ≤ 1 / 2 * σ * ‖y + σ⁻¹ • gradient f x‖ ^ 2 := by positivity
    linarith
  · rw [hdec, reductionRatio_def]
    rcases eq_or_ne ‖gradient f x‖ 0 with h0 | h0
    · simp [h0]
    · field_simp

end Model

/-- **Algorithm 2.4.1** (AR1) of [cartis2022evaluation], as a run predicate on iterates `x`, trial
steps `s` and regularization parameters `σ`: `ε > 0`, and the generic adaptive-regularization run
`Optimization.IsARRun` with the Step-1 test `‖∇f(x_k)‖ ≤ ε`, Step 2 "`s_k` is a global minimizer
of the model (2.4.1)", no post-step test, and the ratio (2.4.3) `Optimization.taylorRatio f 1`:
`σ_0 = σ₀` and before termination `x_{k+1} = x_k + s_k` if `ρ_k ≥ η₁`, `x_k` otherwise, and the
update (2.4.4). -/
structure algorithm_2_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARParams) (ε : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The accuracy level is positive. -/
  ε_pos : 0 < ε
  /-- Steps 1–4. -/
  run : IsARRun P.toARParams (fun k => ‖gradient f (x k)‖ ≤ ε)
    (fun k => IsMinOn (ar1Model f (x k) (σ k)) univ (s k)) (fun _ => False)
    (taylorRatio f 1 x s) x s σ

/-- The termination test of AR1 (no post-step test). -/
private theorem not_stop_iff {test : ℕ → Prop} {k : ℕ} :
    (∀ j < k, ¬ IsARRun.Stop test (fun _ => False) j) ↔ ∀ j < k, ¬ test j := by
  simp [IsARRun.Stop]

private theorem not_stop_le_iff {test : ℕ → Prop} {k : ℕ} :
    (∀ j ≤ k, ¬ IsARRun.Stop test (fun _ => False) j) ↔ ∀ j ≤ k, ¬ test j := by
  simp [IsARRun.Stop]

/-- **Existence of AR1 runs** from every starting point (the step `-∇f(x_k)/σ_k`, (2.4.5), and the
left ends of the intervals of (2.4.4)). -/
theorem exists_algorithm_2_4_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARParams) {ε : ℝ}
    (hε : 0 < ε) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_2_4_1 f P ε x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := fun y => ‖gradient f y‖ ≤ ε)
    (stepOK := fun y σ s => IsMinOn (ar1Model f y σ) univ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement 1 t))
    (fun y σ _ _ hσ _ => ⟨_, (ar1_step_eq hσ).1.2 rfl, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hε, hrun⟩

namespace algorithm_2_4_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : ARParams} {ε : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

theorem sigma_pos (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : 0 < σ k :=
  h.run.sigma_pos (not_stop_iff.2 hk) k le_rfl

/-- Before termination the AR1 step is `s_k = -∇f(x_k)/σ_k` (2.4.5). -/
theorem step_eq (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) : s k = -((σ k)⁻¹ • gradient f (x k)) :=
  ((ar1_step_eq (h.sigma_pos fun j hj => hk j hj.le)).1).1
    (h.run.step_of_forall_le (not_stop_le_iff.2 hk))

/-- Before termination the Taylor decrease is `‖∇f(x_k)‖²/σ_k` (2.4.6). -/
theorem taylorDecrement_eq (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) = ‖gradient f (x k)‖ ^ 2 / σ k := by
  rw [h.step_eq hk]
  exact (ar1_step_eq (s := s k) (h.sigma_pos fun j hj => hk j hj.le)).2.1

theorem taylorDecrement_pos (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    0 < (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) := by
  rw [h.taylorDecrement_eq hk]
  have : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
  have := h.sigma_pos fun j hj => hk j hj.le
  positivity

end algorithm_2_4_1

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {P : ARParams} {ε L flow : ℝ}
  {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 2.4.1** of [cartis2022evaluation] ((2.4.8)). For an AR1 run, if the method has not
terminated before iteration `k` and `σ_k ≤ σ_max`, then
`k ≤ |𝒮_k| (1 + |log γ₁|/log γ₂) + log(σ_max/σ₀)/log γ₂`, `𝒮_k = {j ≤ k | ρ_j ≥ η₁}`. Only the
update (2.4.4) is used. -/
theorem lemma_2_4_1 (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) {σmax : ℝ} (hσ : σ k ≤ σmax) :
    (k : ℝ) ≤ (successSet (fun j => P.η₁ ≤ taylorRatio f 1 x s j) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
  h.run.le_succ_count (not_stop_iff.2 hk) hσ

/-- The bound `σ_max = max(σ₀, γ₃ L/(2(1 - η₂)))` of (2.4.9). -/
noncomputable def sigmaMaxAR1 (P : ARParams) (L : ℝ) : ℝ :=
  max P.σ₀ (P.γ₃ * L / (2 * (1 - P.η₂)))

theorem sigmaMaxAR1_pos (P : ARParams) (L : ℝ) : 0 < sigmaMaxAR1 P L :=
  P.σ₀_pos.trans_le (le_max_left _ _)

/-- **Lemma 2.4.2** of [cartis2022evaluation] ((2.4.9)). Under f.gL, for every iteration `k` of an
AR1 run up to (and including) termination, `σ_k ≤ max(σ₀, γ₃ L/(2(1 - η₂)))`. -/
theorem lemma_2_4_2 (hf : AssumptionGL f L) (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ ‖gradient f (x j)‖ ≤ ε) : σ k ≤ sigmaMaxAR1 P L := by
  have hforce : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => ‖gradient f (x k)‖ ≤ ε)
      (fun _ => False) j) → L / (2 * (1 - P.η₂)) ≤ σ k → P.η₂ ≤ taylorRatio f 1 x s k := by
    intro k hk hσk
    rw [not_stop_le_iff] at hk
    have hσ := h.sigma_pos fun j hj => hk j hj.le
    have hg : 0 < ‖gradient f (x k)‖ := h.ε_pos.trans (not_le.1 (hk k le_rfl))
    have hs : s k ≠ 0 := by
      rw [h.step_eq hk, neg_ne_zero, smul_ne_zero_iff]
      exact ⟨inv_ne_zero hσ.ne', norm_pos_iff.1 hg⟩
    have hdec : 1 * σ k * ‖s k‖ ^ (1 + 1) ≤ (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k) := by
      rw [h.taylorDecrement_eq hk, h.step_eq hk, norm_neg, norm_smul, Real.norm_of_nonneg
        (inv_nonneg.2 hσ.le)]
      apply le_of_eq
      rw [show (1 + 1 : ℕ) = 2 from rfl]
      field_simp
    refine le_reductionRatio_of_lipschitz convex_univ (fun y _ => hf.contDiff.contDiffAt)
      hf.iteratedFDerivLipschitzOn (mem_univ _) (mem_univ _) hs one_pos hσ hdec ?_
    rw [div_le_iff₀ (by linarith [P.η₂_lt_one])] at hσk
    norm_num [Nat.factorial]
    linarith
  have := (h.run.sigma_le_max hforce (not_stop_iff.2 hk) k le_rfl).2.2
  rw [sigmaMaxAR1]
  convert this using 2
  ring

/-- The constant `κ^S_AR1 = η₁⁻¹ max(σ₀, γ₃ L/(2(1 - η₂)))` of (2.4.11). -/
noncomputable def kappaSAR1 (P : ARParams) (L : ℝ) : ℝ :=
  P.η₁⁻¹ * sigmaMaxAR1 P L

/-- The decrease at a successful AR1 iteration: `f(x_k) - f(x_{k+1}) ≥ η₁ ε²/σ_max`. -/
private theorem sub_ge_of_succ (hf : AssumptionGL f L) (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) (hs : P.η₁ ≤ taylorRatio f 1 x s k) :
    P.η₁ * ε ^ 2 / sigmaMaxAR1 P L ≤ f (x k) - f (x (k + 1)) := by
  have hsub := (h.run.sub_ge_of_succ (w := f)
    (pred := fun k => (ftaylorSeries ℝ f (x k)).taylorDecrement 1 (s k))
    (not_stop_le_iff.2 hk) rfl (h.taylorDecrement_pos hk) hs).2
  rw [h.taylorDecrement_eq hk] at hsub
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hσmax := lemma_2_4_2 hf h fun j hj => hk j hj.le
  have hg : ε ≤ ‖gradient f (x k)‖ := (not_le.1 (hk k le_rfl)).le
  have h1 : ε ^ 2 / sigmaMaxAR1 P L ≤ ‖gradient f (x k)‖ ^ 2 / σ k :=
    div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ h.ε_pos.le hg 2) hσ hσmax
  have := mul_le_mul_of_nonneg_left h1 P.η₁_pos.le
  rw [mul_div_assoc]
  linarith

/-- **Lemma 2.4.3** of [cartis2022evaluation] ((2.4.11)). Under f.Bb and f.gL, at every iteration
`k` before termination of an AR1 run, `|𝒮_k| ≤ κ^S_AR1 (f(x₀) - f_low)/ε²`. -/
theorem lemma_2_4_3 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (h : algorithm_2_4_1 f P ε x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ((successSet (fun j => P.η₁ ≤ taylorRatio f 1 x s j) k).card : ℝ) ≤
      kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
  have hc : 0 < P.η₁ * ε ^ 2 / sigmaMaxAR1 P L := by
    have := P.η₁_pos; have := h.ε_pos; have := sigmaMaxAR1_pos P L; positivity
  have hcard := card_successSet_le_div_of_decrease (φ := fun j => f (x j)) hc
    (fun j hj hs => by
      rw [h.run.eq_of_not_succ (not_stop_le_iff.2 fun i hi => hk i (hi.trans hj)) (not_le.1 hs)])
    (fun j hj hs => sub_ge_of_succ hf h (fun i hi => hk i (hi.trans hj)) hs) (hb (x (k + 1)))
  refine hcard.trans_eq ?_
  have := P.η₁_pos; have := h.ε_pos; have := sigmaMaxAR1_pos P L
  rw [kappaSAR1]
  field_simp

/-- The constant `κ^A_AR1 = η₁⁻¹ max(σ₀, γ₃ L/(1 - η₂)) (1 + |log γ₁|/log γ₂)` of
Theorem 2.4.4. -/
noncomputable def kappaAAR1 (P : ARParams) (L : ℝ) : ℝ :=
  P.η₁⁻¹ * max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- The constant `κ^C_AR1 = log(max(1, γ₃ L/(σ₀(1 - η₂))))/log γ₂ + 1` of Theorem 2.4.4. -/
noncomputable def kappaCAR1 (P : ARParams) (L : ℝ) : ℝ :=
  Real.log (max 1 (P.γ₃ * L / (P.σ₀ * (1 - P.η₂)))) / Real.log P.γ₂ + 1

/-- **Theorem 2.4.4** of [cartis2022evaluation]. Under f.Bb and f.gL, every AR1 run terminates at
an iteration `k_ε` after at most `κ^A_AR1 (f(x₀) - f_low)/ε² + κ^C_AR1` evaluations of `f` and at
most `κ^S_AR1 (f(x₀) - f_low)/ε² + 1` evaluations of `∇f` (one at `x₀` and one per successful
iteration). -/
theorem theorem_2_4_4 (hb : AssumptionBb f flow) (hf : AssumptionGL f L)
    (h : algorithm_2_4_1 f P ε x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaAAR1 P L * (f (x 0) - flow) / ε ^ 2 + kappaCAR1 P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε : ℝ) ≤
        kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set σmax := sigmaMaxAR1 P L
  have hσmax := sigmaMaxAR1_pos P L
  have hε := h.ε_pos
  have hη := P.η₁_pos
  have hδ : 0 < P.η₁ * ε ^ 2 / σmax := by positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease_of_le (σmax := σmax)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_2_4_2 hf h (not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (h.taylorDecrement_pos (not_stop_le_iff.1 hk)))
    (fun k _ => hb (x k))
    (fun k hk hs => sub_ge_of_succ hf h (not_stop_le_iff.1 hk) hs)
  have hN : (f (x 0) - flow) / (P.η₁ * ε ^ 2 / σmax) =
      kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSAR1]; field_simp; rfl
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, hF.trans ?_, hD⟩
  -- comparison with the book's (larger) constants
  have hL0 := hf.nonneg
  have h1η := P.one_sub_η₂_pos
  have hlog := P.log_γ₂_pos
  have hf0 : 0 ≤ f (x 0) - flow := sub_nonneg.2 (hb (x 0))
  have hσ₁ : σmax ≤ max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) := by
    refine max_le_max le_rfl ?_
    rw [div_le_div_iff₀ (by positivity) h1η]
    nlinarith [P.γ₃_pos, mul_nonneg P.γ₃_pos.le hL0]
  have hA : kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) ≤
      kappaAAR1 P L * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSAR1, kappaAAR1]
    have : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
    have : 0 ≤ (f (x 0) - flow) / ε ^ 2 := by positivity
    have key : P.η₁⁻¹ * σmax * ((f (x 0) - flow) / ε ^ 2) *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) ≤
        P.η₁⁻¹ * max P.σ₀ (P.γ₃ * L / (1 - P.η₂)) * ((f (x 0) - flow) / ε ^ 2) *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by gcongr
    calc P.η₁⁻¹ * σmax * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂)
        = P.η₁⁻¹ * σmax * ((f (x 0) - flow) / ε ^ 2) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by ring
      _ ≤ _ := key
      _ = _ := by ring
  have hC : Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1 ≤ kappaCAR1 P L := by
    rw [kappaCAR1]
    gcongr
    · exact div_pos hσmax P.σ₀_pos
    · rw [div_le_iff₀ P.σ₀_pos, max_mul_of_nonneg _ _ P.σ₀_pos.le, one_mul]
      refine hσ₁.trans (max_le_max le_rfl (le_of_eq ?_))
      have := P.σ₀_pos
      field_simp
  calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1
      = kappaSAR1 P L * (f (x 0) - flow) / ε ^ 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        (Real.log (σmax / P.σ₀) / Real.log P.γ₂ + 1) := by ring
    _ ≤ _ := add_le_add hA hC

end Lemmas

/-! ### Theorem 2.4.5 -/

/-- **Theorem 2.4.5** of [cartis2022evaluation] (sharpness of AR1). For all AR1 constants there are
`L ≥ 1` and `f_low` such that for every `ε ∈ (0,1)` with `k_ε = ε⁻²` an integer there are
`f : ℝ¹ → ℝ` satisfying f.Bb and f.gL and an AR1 run from `x₀ = 0` with `σ_k = σ₀` for all `k`
and `ρ_k = 1` before termination, which terminates exactly at iteration `k_ε`, after `k_ε + 1`
evaluations of `f` and of `∇f`. (The data of Theorem 2.2.3 with `t_ini = σ₀⁻¹`.) -/
theorem theorem_2_4_5 (P : ARParams) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε < 1 → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∃ (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (σ : ℕ → ℝ), x 0 = 0 ∧
          algorithm_2_4_1 f P ε x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < kε, taylorRatio f 1 x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
          funEvalCount kε = kε + 1 ∧
          derivEvalCount (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε = kε + 1 := by
  set t := P.σ₀⁻¹
  have ht : 0 < t := inv_pos.2 P.σ₀_pos
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example ht
  refine ⟨L, flow, hL, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1.le hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX t ε kε k • e₀
  set s : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => -(P.σ₀⁻¹ • gradient f (x k))
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  have hbefore : ∀ k, (∀ j ≤ k, ¬ IsARRun.Stop (fun k => ‖gradient f (x k)‖ ≤ ε)
      (fun _ => False) j) → k < kε := fun k hk =>
    not_le.1 fun hle => (not_stop_le_iff.1 hk) kε hle hhit.test
  have hfx : ∀ j ≤ kε, f (x j) = slowF t ε kε j := fun j hj => (hfk j hj).1
  have hg : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    simp only [x]
    rw [(hfk k hk).2, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by unfold slowOmega; positivity
    linarith
  have hstep : ∀ k < kε, x k + s k = x (k + 1) := fun k hk => by
    simp only [x, s]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hratio : ∀ k < kε, taylorRatio f 1 x s k = 1 := fun k hk => by
    have hgk : 0 < ‖gradient f (x k)‖ := by rw [hg k hk.le]; linarith [slowOmega_pos hε hk]
    rw [taylorRatio_def, (ar1_step_eq (s := 0) P.σ₀_pos).2.2, hstep k hk, hfx k hk.le,
      hfx (k + 1) hk, slowF_succ, ← hg k hk.le]
    simp only [t]
    rw [sub_sub_cancel]
    have := P.σ₀_pos.ne'
    have := hgk.ne'
    field_simp
  have hrun : algorithm_2_4_1 f P ε x s fun _ => P.σ₀ := by
    refine ⟨hε, rfl, fun k _ _ => (ar1_step_eq P.σ₀_pos).1.2 rfl, fun k hk => ?_⟩
    have hk := hbefore k hk
    have h1 : P.η₁ ≤ taylorRatio f 1 x s k := by
      rw [hratio k hk]; linarith [P.η₁_le_η₂, P.η₂_lt_one]
    refine ⟨by rw [ite_eq_left h1, hstep k hk], fun _ => ⟨max_le P.σmin_le_σ₀
      (mul_le_of_le_one_left P.σ₀_pos.le P.γ₁_le_one), le_rfl⟩, fun _ h2 => ?_,
      fun h3 => absurd h3 (not_lt.2 h1)⟩
    rw [hratio k hk] at h2
    exact absurd h2 (not_lt.2 (by linarith [P.η₂_lt_one]))
  refine ⟨f, hb, hgl, x, s, fun _ => P.σ₀, by simp [x, slowX], hrun, fun _ => rfl, hratio, hhit,
    funEvalCount_eq kε, ?_⟩
  classical
  rw [derivEvalCount_eq_count]
  have : Nat.count (fun k => P.η₁ ≤ taylorRatio f 1 x s k) kε = kε := by
    rw [Nat.count_eq_card_filter_range, filter_true_of_mem, card_range]
    intro k hk
    rw [hratio k (mem_range.1 hk)]
    linarith [P.η₁_le_η₂, P.η₂_lt_one]
  rw [this]

end CartisGouldToint.Chapter02
