import NumlibSurface.CartisGouldToint.Chapter03.Section03
import Numlib.Optimization.ModelBased.PowRegularizedModel

/-!
# Cartis–Gould–Toint §5.5: Universal regularization methods

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §5.5: the universal
adaptive-regularization algorithm ARp-H (Algorithm 5.5.1) on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, with
the model `m_k(s) = T_p(x_k, s) + σ_k/r! ‖s‖^r` (5.5.1) for a real power `r > p`
(`Optimization.powRegularizedModel`, generalized factorial `Optimization.realFactorial`), for
objectives whose `p`-th derivative is Hölder continuous with an exponent `β_p` unknown to the
algorithm (f.DpH).

ARp-H is an instance of the generic adaptive-regularization run `Optimization.IsARRun`:
* termination is tested at `x₀` (Step-1 test `k = 0 ∧ stop(x₀)`) and at every trial point
  `x_k + s_k` (post-step test), where `stop = Chapter03.stopTest f ε₁ ε₂` (the "strict local
  minimizer" branch (5.5.8) is subsumed);
* Step 3–4 are `Optimization.ARAcceptance` with `σ_min = 0` and the *modified ratio*
  `ρ̃_k = ρ_k` if the step-length tests (5.5.10)–(5.5.11) hold and `ρ̃_k = 0` otherwise; since
  `η₁ > 0`, iteration `k` is successful (`ρ̃_k ≥ η₁`) iff `ρ_k ≥ η₁` and (5.5.10)–(5.5.11) hold,
  which encodes Steps 3–4 (with the corrected third case of Step 4, see below).

## Main definitions

* `AssumptionDpH f p H β` — f.DpH (5.5.3).
* `ARpHParams r` — the constants of Algorithm 5.5.1; `arpHStep`, `arpHLengthTest`,
  `arpHRatio`, `arpHStop`; `algorithm_5_5_1` — Algorithm 5.5.1; `exists_algorithm_5_5_1`.
* `kappaBeta`, `kappaBetaJ`, `sigmaBar`, `sigmaH`, `epsMax`, `deltaEps`, `kappaH` — the constants
  (5.5.19), (5.5.28), (5.5.30), (5.5.27)/(5.5.29), (5.5.42), (5.5.45).

## Main results

Lemmas 5.5.1–5.5.6 and Theorem 5.5.7 (complexity of ARp-H).

## Fixes with respect to the book

* **Algorithm 5.5.1, Step 4.** The third case reads "`ρ_k < η₁` and (5.5.10) or (5.5.11)
  fails"; it must be the complement of the first two cases, "`ρ_k < η₁`, or (5.5.10) fails, or
  (5.5.11) fails" (encoded through `ρ̃_k`).
* Lemma 5.5.2: the display writes `∇_s m_k(x_k + s_k)` for the model gradient `∇_s m_k(s_k)`.
* Lemma 5.5.4: in the proof of case (b), the conclusion is `σ_k < κ_{β,2} ε₂^{(p+β-r)/(p+β-2)}`
  (printed with `ε₁`), contradicting (5.5.29).
* **Theorem 5.5.7.** `f` and its first (and second) derivatives are evaluated at `x₀` and at
  every trial point, i.e. `k_ε + 2` times when the run terminates at the trial point of iteration
  `k_ε` (Lemma 2.4.1 bounds `k_ε + 1`): the constant `κ^C` needs an additional `+ 2`.
* `p + β_p > 1` is not a hypothesis: it follows from f.DpH (`β₁ > 0` when `p = 1`).
-/

open Set Finset Optimization
open Optimization hiding ARParams
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter05

open Chapter03

variable {n : ℕ}

/-! ### Assumption f.DpH and the algorithm -/

/-- **Assumption f.DpH** of [cartis2022evaluation] (§5.5.1): `f` is `p` times continuously
differentiable and its `p`-th derivative is Hölder continuous with constant `H = H_{f,p} ≥ 0` and
exponent `β = β_p ∈ [0, 1]`, `β > 0` if `p = 1`: `‖∇^p f(x) - ∇^p f(y)‖ ≤ H ‖x - y‖^β` (5.5.3). -/
structure AssumptionDpH (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (H β : ℝ) : Prop where
  /-- `f` is `p` times continuously differentiable. -/
  contDiff : ContDiff ℝ p f
  /-- `H ≥ 0`. -/
  H_nonneg : 0 ≤ H
  /-- `β ≥ 0`. -/
  β_nonneg : 0 ≤ β
  /-- `β ≤ 1`. -/
  β_le_one : β ≤ 1
  /-- `β > 0` when `p = 1`. -/
  β_pos_of_eq_one : p = 1 → 0 < β
  /-- The Hölder condition (5.5.3). -/
  holder : IteratedFDerivHolderOn f p H β univ

/-- f.DpH is the backbone predicate `IteratedFDerivHolderOn f p H β univ` for a `C^p` function,
with the ranges of the constants. -/
theorem assumptionDpH_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {H β : ℝ} :
    AssumptionDpH f p H β ↔ ContDiff ℝ p f ∧ 0 ≤ H ∧ β ∈ Set.Icc 0 1 ∧ (p = 1 → 0 < β) ∧
      IteratedFDerivHolderOn f p H β univ :=
  ⟨fun h => ⟨h.contDiff, h.H_nonneg, ⟨h.β_nonneg, h.β_le_one⟩, h.β_pos_of_eq_one, h.holder⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3.1, h3.2, h4, h5⟩⟩

/-- The constants of Algorithm 5.5.1 ([cartis2022evaluation], Step 0) for the regularization
power `r`: those of an AR method with `σ_min = 0`, the step accuracies `θ₁, θ₂ ∈ (0, 1]` and the
step-length constants `α₁ ∈ (0, min(1, (r-1)!)/3]`, `α₂ ∈ (0, min(1, (r-2)!)/3]`. -/
structure ARpHParams (r : ℝ) extends Optimization.ARParams where
  /-- No lower bound on the regularization weight. -/
  σmin_eq_zero : σmin = 0
  /-- The first-order step accuracy (5.5.5). -/
  θ₁ : ℝ
  /-- The second-order step accuracy (5.5.6). -/
  θ₂ : ℝ
  /-- The first-order step-length constant (5.5.10). -/
  α₁ : ℝ
  /-- The second-order step-length constant (5.5.11). -/
  α₂ : ℝ
  θ₁_pos : 0 < θ₁
  θ₁_le_one : θ₁ ≤ 1
  θ₂_pos : 0 < θ₂
  θ₂_le_one : θ₂ ≤ 1
  α₁_pos : 0 < α₁
  α₁_le : α₁ ≤ min 1 (realFactorial (r - 1)) / 3
  α₂_pos : 0 < α₂
  α₂_le : α₂ ≤ min 1 (realFactorial (r - 2)) / 3

variable {r : ℝ}

/-- The model (5.5.1) at the iterate `y` with weight `σ`. -/
noncomputable abbrev arpHModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (r : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  powRegularizedModel (ftaylorSeries ℝ f y) p σ r

/-- Step 1 of Algorithm 5.5.1: the step decreases the model (5.5.4), satisfies
`‖∇m(s)‖ ≤ θ₁ ‖s‖^{r-1}` (5.5.5) and, if `ε₂ < ∞`, `λ_min[∇²m(s)] ≥ -θ₂ ‖s‖^{r-2}` (5.5.6). -/
def arpHStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r) (ε₂ : Option ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  arpHModel f p r y σ s < arpHModel f p r y σ 0 ∧
    ‖fderiv ℝ (arpHModel f p r y σ) s‖ ≤ P.θ₁ * ‖s‖ ^ (r - 1) ∧
    (ε₂.isSome →
      -(P.θ₂ * ‖s‖ ^ (r - 2)) ≤ minCurvature (iteratedFDeriv ℝ 2 (arpHModel f p r y σ) s))

/-- The step-length tests of Step 3: `σ ‖s‖^{r-1} ≥ α₁ ‖∇f(y + s)‖` (5.5.10) and, if `ε₂ < ∞`,
`σ ‖s‖^{r-2} ≥ -α₂ λ_min[∇²f(y + s)]` (5.5.11). -/
def arpHLengthTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (P : ARpHParams r) (ε₂ : Option ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  P.α₁ * ‖gradient f (y + s)‖ ≤ σ * ‖s‖ ^ (r - 1) ∧
    (ε₂.isSome → -(P.α₂ * Chapter01.hessianMinEig f (y + s)) ≤ σ * ‖s‖ ^ (r - 2))

open Classical in
/-- The modified ratio of one iteration: the ratio (5.5.9) if the step-length tests hold, `0`
otherwise. -/
noncomputable def arpHRatioAt (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₂ : Option ℝ) (y : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if arpHLengthTest f P ε₂ y σ s then
    reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s)
  else 0

/-- The modified ratios `ρ̃_k` of a run. -/
noncomputable abbrev arpHRatio (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  arpHRatioAt f p P ε₂ (x k) (σ k) (s k)

/-- The termination test of ARp-H at iteration `k`: the test (5.5.7)–(5.5.8) at `x₀` (`k = 0`)
or at the trial point `x_k + s_k`. -/
abbrev arpHStop (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ : Option ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → Prop :=
  IsARRun.Stop (fun k => k = 0 ∧ stopTest f ε₁ ε₂ (x k)) (fun k => stopTest f ε₁ ε₂ (x k + s k))

/-- **Algorithm 5.5.1** (ARp-H) of [cartis2022evaluation], as a run predicate on iterates `x`,
steps `s` and weights `σ`: `p ≥ 1` (`p ≥ 2` if `ε₂ < ∞`), `r > p`, `ε₁ ∈ (0, 1]`,
`ε₂ ∈ (0, 1] ∪ {∞}`, and the generic AR run with termination test at `x₀` and at every trial
point, Step 1 `arpHStep`, and the modified ratio `arpHRatio` (Steps 3–4, corrected). -/
structure algorithm_5_5_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpHParams r)
    (ε₁ : ℝ) (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- `p ≥ 1`. -/
  one_le_p : 1 ≤ p
  /-- `p ≥ 2` when second-order points are sought. -/
  two_le_p : ε₂.isSome → 2 ≤ p
  /-- `r > p`. -/
  p_lt_r : (p : ℝ) < r
  /-- `ε₁ > 0`. -/
  ε₁_pos : 0 < ε₁
  /-- `ε₁ ≤ 1`. -/
  ε₁_le_one : ε₁ ≤ 1
  /-- `ε₂ > 0` if finite. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- `ε₂ ≤ 1` if finite. -/
  ε₂_le_one : ∀ e ∈ ε₂, e ≤ 1
  /-- Steps 1–4. -/
  run : IsARRun P.toARParams (fun k => k = 0 ∧ stopTest f ε₁ ε₂ (x k))
    (fun k => arpHStep f p P ε₂ (x k) (σ k) (s k)) (fun k => stopTest f ε₁ ε₂ (x k + s k))
    (arpHRatio f p P ε₂ x s σ) x s σ

section Basic

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₂ : Option ℝ}
  {y : EuclideanSpace ℝ (Fin n)} {σ : ℝ} {s : EuclideanSpace ℝ (Fin n)}

/-- An iteration is successful for the modified ratio iff `ρ_k ≥ η₁` and the step-length tests
hold. -/
theorem le_arpHRatioAt_iff :
    P.η₁ ≤ arpHRatioAt f p P ε₂ y σ s ↔
      P.η₁ ≤ reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s) ∧
        arpHLengthTest f P ε₂ y σ s := by
  unfold arpHRatioAt
  split_ifs with h
  · exact ⟨fun h1 => ⟨h1, h⟩, fun h1 => h1.1⟩
  · exact ⟨fun h1 => absurd h1 (not_le.2 P.η₁_pos), fun h1 => absurd h1.2 h⟩

/-- If the step-length tests hold, the modified ratio is the ratio (5.5.9). -/
theorem arpHRatioAt_of_lengthTest (h : arpHLengthTest f P ε₂ y σ s) :
    arpHRatioAt f p P ε₂ y σ s = reductionRatio f y s ((ftaylorSeries ℝ f y).taylorDecrement p s) :=
  by unfold arpHRatioAt; simp only [h, ↓reduceIte]

/-- The model derivatives at the zero step are those of `f`: `∇^j m(0) = ∇^j f(y)` for `j ≤ p`,
`j < r`. -/
theorem iteratedFDeriv_arpHModel_zero (hf : ContDiffAt ℝ p f y) {j : ℕ} (hj : j ≤ p)
    (hjr : (j : ℝ) < r) :
    iteratedFDeriv ℝ j (arpHModel f p r y σ) 0 = iteratedFDeriv ℝ j f y := by
  rw [arpHModel, iteratedFDeriv_powRegularizedModel ((contDiff_normRpow_of_lt hjr).contDiffAt),
    ← taylorPolynomial_eq_taylorSum, iteratedFDeriv_taylorPolynomial_zero hf hj,
    iteratedFDeriv_normRpow_zero hjr, smul_zero, add_zero]

end Basic

/-! ### Existence of runs -/

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}

/-- At a point where the termination test fails, the global minimizers of the model decrease it
and satisfy Step 1. -/
theorem exists_arpHStep (hf : ContDiff ℝ p f) (P : ARpHParams r) (hp : 1 ≤ p)
    (hpr : (p : ℝ) < r) {ε₁ : ℝ} (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (hp2 : ε₂.isSome → 2 ≤ p) {y : EuclideanSpace ℝ (Fin n)} {σ : ℝ} (hσ : 0 < σ)
    (hnot : ¬ stopTest f ε₁ ε₂ y) : ∃ s, arpHStep f p P ε₂ y σ s := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨s, -, hd, hc, hlt⟩ := exists_isMinOn_powRegularizedModel
    (D := ftaylorSeries ℝ f y) (p := p) hσ hpr (by linarith)
  refine ⟨s, hlt fun hmin0 => hnot ?_, ?_, fun hs => ?_⟩
  · have hloc : IsLocalMin (arpHModel f p r y σ) 0 := hmin0.isLocalMin Filter.univ_mem
    have hg : gradient f y = 0 := by
      have h1 := iteratedFDeriv_arpHModel_zero (y := y) (σ := σ) hf.contDiffAt hp
        (by push_cast; linarith : ((1 : ℕ) : ℝ) < r)
      have h2 := congrArg norm h1
      rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, hloc.fderiv_eq_zero, norm_zero]
        at h2
      rw [← norm_eq_zero, norm_gradient_eq, ← h2]
    refine ⟨by rw [hg, norm_zero]; exact hε₁.le, fun e he => ?_⟩
    have hp2' := hp2 (by rw [Option.mem_def.1 he]; rfl)
    have hp2r : (2 : ℝ) < r := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2'
      linarith
    have h0 := hloc.minCurvature_iteratedFDeriv_two_nonneg
      (contDiff_two_powRegularizedModel hp2r.le).contDiffAt
    rw [iteratedFDeriv_arpHModel_zero (y := y) hf.contDiffAt hp2' (by push_cast; linarith)] at h0
    have := hε₂ e he
    change -e ≤ minCurvature _
    linarith
  · rw [hd, norm_zero]
    have := P.θ₁_pos
    positivity
  · have hp2' := hp2 hs
    have h2r : (2 : ℝ) ≤ r := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2'
      linarith
    have := hc h2r
    have := P.θ₂_pos
    have : 0 ≤ P.θ₂ * ‖s‖ ^ (r - 2) := by positivity
    linarith

/-- In a run of the generic method with the test at the iterates, "no ARp-H termination before
`k` and no termination at `x₀`" implies that the test fails at all iterates `x_j`, `j ≤ k`. -/
theorem not_stopTest_iterate {E : Type*} [Add E] {P : Optimization.ARParams} {test : E → Prop}
    {step : ℕ → Prop} {ρ : ℕ → ℝ} {x s : ℕ → E} {σ : ℕ → ℝ}
    (h : IsARRun P (fun k => test (x k)) step (fun _ => False) ρ x s σ) (h0 : ¬ test (x 0))
    {k : ℕ} (hk : ∀ j < k, ¬ test (x j + s j)) : ∀ j ≤ k, ¬ test (x j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | j
    · exact h0
    · have hle : ∀ i ≤ j, ¬ IsARRun.Stop (fun k => test (x k)) (fun _ => False) i :=
        IsARRun.forall_le_not_stop_iff.2 fun i hi => ih i (by omega) (by omega)
      rcases (h.accept j hle).eq_add_or_eq_self with he | he
      · rw [he]; exact hk j (by omega)
      · rw [he]; exact ih j (by omega) (by omega)

/-- **Existence of ARp-H runs** ([cartis2022evaluation], Algorithm 5.5.1 is well defined): for
`f` of class `C^p`, all admissible constants and tolerances and every starting point there is an
ARp-H run (global model minimizers satisfy Step 1). -/
theorem exists_algorithm_5_5_1 (hf : ContDiff ℝ p f) (P : ARpHParams r) (hp : 1 ≤ p)
    (hpr : (p : ℝ) < r) {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) {ε₂ : Option ℝ}
    (hε₂ : ∀ e ∈ ε₂, 0 < e) (hε₂1 : ∀ e ∈ ε₂, e ≤ 1) (hp2 : ε₂.isSome → 2 ≤ p)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_5_5_1 f p P ε₁ ε₂ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := stopTest f ε₁ ε₂) (stepOK := arpHStep f p P ε₂) (arpHRatioAt f p P ε₂)
    (fun y σ _ _ hσ hnot => (exists_arpHStep hf P hp hpr hε₁ hε₂ hp2 hσ hnot).imp
      fun _ hs => ⟨hs, trivial⟩) trivial
  refine ⟨x, s, σ, hx0, hp, hp2, hpr, hε₁, hε₁1, hε₂, hε₂1, ⟨hrun.sigma_zero, ?_, ?_⟩⟩
  · intro k hk h1
    have h0 : ¬ stopTest f ε₁ ε₂ (x 0) := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact fun h => h1 ⟨rfl, h⟩
      · exact fun h => hk 0 hpos (Or.inl ⟨rfl, h⟩)
    have hnt := not_stopTest_iterate hrun h0 (k := k) fun j hj h => hk j hj (Or.inr h)
    exact hrun.step k (fun j hj => by simpa [IsARRun.Stop] using hnt j hj.le)
      (by simpa using hnt k le_rfl)
  · intro k hk
    have h0 : ¬ stopTest f ε₁ ε₂ (x 0) := fun h => hk 0 (Nat.zero_le _) (Or.inl ⟨rfl, h⟩)
    have hnt := not_stopTest_iterate hrun h0 (k := k) fun j hj h => hk j hj.le (Or.inr h)
    exact hrun.accept k fun j hj => by simpa [IsARRun.Stop] using hnt j hj

end Existence

/-! ### Basic properties of runs -/

section RunBasic

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

namespace algorithm_5_5_1

variable (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
include h

theorem one_lt_r : 1 < r := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast h.one_le_p
  linarith [h.p_lt_r]

theorem two_lt_r (hs : ε₂.isSome) : 2 < r := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast h.two_le_p hs
  linarith [h.p_lt_r]

/-- The weights are positive up to termination. -/
theorem sigma_pos {k : ℕ} (hk : ∀ j < k, ¬ arpHStop f ε₁ ε₂ x s j) : 0 < σ k :=
  h.run.sigma_pos hk k le_rfl

/-- Step 1 holds before termination. -/
theorem step {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    arpHStep f p P ε₂ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le hk

end algorithm_5_5_1

/-- The trial point of an iteration before termination fails the termination test. -/
theorem not_stopTest_trial {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    ¬ stopTest f ε₁ ε₂ (x k + s k) :=
  fun ht => hk k le_rfl (Or.inr ht)

end RunBasic

/-! ### Lemmas 5.5.1 and 5.5.2 -/

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.1** of [cartis2022evaluation] ((5.5.12), sufficient decrease): at every iteration
`k` before termination of an ARp-H run, `T_p(x_k, 0) - T_p(x_k, s_k) > σ_k/r! ‖s_k‖^r`. -/
theorem lemma_5_5_1 (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    σ k / realFactorial r * ‖s k‖ ^ r < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
  lt_taylorDecrement_of_powRegularizedModel_lt (by linarith [h.one_lt_r]) (h.step hk).1

/-- The step of an iteration before termination is nonzero. -/
theorem algorithm_5_5_1.step_ne_zero (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) : s k ≠ 0 := by
  intro h0
  have := (h.step hk).1
  rw [h0] at this
  exact lt_irrefl _ this

/-- **Lemma 5.5.2** of [cartis2022evaluation] (lower bound on the step). Under f.DpH, at every
iteration `k` before termination:
(5.5.13) `‖∇f(x_k + s_k)‖ ≤ H/(p+β-1)! ‖s_k‖^{p+β-1} + σ_k/(r-1)! ‖s_k‖^{r-1} + θ₁ ‖s_k‖^{r-1}`;
(5.5.14) if `ε₂ < ∞`, `-λ_min[∇²f(x_k + s_k)] ≤ H/(p+β-2)! ‖s_k‖^{p+β-2} + σ_k/(r-2)! ‖s_k‖^{r-2} +
θ₂ ‖s_k‖^{r-2}`,
with `(p+β-j)! = holderFactorial (p-j) β` and `(r-j)! = realFactorial (r-j)`. -/
theorem lemma_5_5_2 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) :
    ‖gradient f (x k + s k)‖ ≤ H / holderFactorial (p - 1) β * ‖s k‖ ^ ((p : ℝ) + β - 1) +
        σ k / realFactorial (r - 1) * ‖s k‖ ^ (r - 1) + P.θ₁ * ‖s k‖ ^ (r - 1) ∧
      (ε₂.isSome → -Chapter01.hessianMinEig f (x k + s k) ≤
        H / holderFactorial (p - 2) β * ‖s k‖ ^ ((p : ℝ) + β - 2) +
          σ k / realFactorial (r - 2) * ‖s k‖ ^ (r - 2) + P.θ₂ * ‖s k‖ ^ (r - 2)) := by
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hstep := h.step hk
  have hcd : ∀ y ∈ (univ : Set (EuclideanSpace ℝ (Fin n))), ContDiffAt ℝ p f y :=
    fun y _ => hf.contDiff.contDiffAt
  refine ⟨?_, fun hs => ?_⟩
  · have hb := norm_fderiv_le_of_powRegularizedModel convex_univ hcd h.one_le_p hf.β_nonneg
      hf.holder (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le h.one_lt_r
    have he : ((p - 1 : ℕ) : ℝ) + β = (p : ℝ) + β - 1 := by
      rw [Nat.cast_sub h.one_le_p]; push_cast; ring
    rw [he] at hb
    rw [norm_gradient_eq]
    linarith [hstep.2.1]
  · have hp2 := h.two_le_p hs
    have hb := minCurvature_ge_of_powRegularizedModel convex_univ hcd hp2 hf.β_nonneg
      hf.holder (mem_univ (x k)) (mem_univ (x k + s k)) hσ.le (h.two_lt_r hs).le
    have he : ((p - 2 : ℕ) : ℝ) + β = (p : ℝ) + β - 2 := by
      rw [Nat.cast_sub hp2]; push_cast; ring
    rw [he] at hb
    have := hstep.2.2 hs
    simp only [Chapter01.hessianMinEig_def]
    linarith

end Lemmas

/-! ### The constants -/

section Constants

variable (P : ARpHParams r) (p : ℕ) (H β : ℝ)

/-- `κ_β = r! H / ((p+β-1)! (1 - η₂))` ([cartis2022evaluation], (5.5.19)). -/
noncomputable def kappaBeta : ℝ :=
  realFactorial r * H / (holderFactorial (p - 1) β * (1 - P.η₂))

/-- `κ_{β,j} = ((r-j)!/3)^{(p+β-r)/(p+β-j)} κ_β^{(r-j)/(p+β-j)}` ([cartis2022evaluation],
(5.5.28) for `j = 1`, (5.5.30) for `j = 2`). -/
noncomputable def kappaBetaJ (j : ℝ) : ℝ :=
  (realFactorial (r - j) / 3) ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - j)) *
    kappaBeta P p H β ^ ((r - j) / ((p : ℝ) + β - j))

/-- The threshold `σ̄` above which iterations are very successful ([cartis2022evaluation], the
right-hand sides of (5.5.27) (`ε₂ = ∞`) and (5.5.29) (`ε₂ < ∞`)). -/
noncomputable def sigmaBar (ε₁ : ℝ) : Option ℝ → ℝ
  | none => max (P.θ₁ * realFactorial (r - 1))
      (kappaBetaJ P p H β 1 * ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
  | some e => max (max (P.θ₁ * realFactorial (r - 1)) (P.θ₂ * realFactorial (r - 2)))
      (max (kappaBetaJ P p H β 1 * ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
        (kappaBetaJ P p H β 2 * e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))))

/-- `σ_H` ([cartis2022evaluation], (5.5.42), (5.5.55)): `max[σ₀, γ₃θ₁(r-1)!, γ₃θ₂(r-2)!,
γ₃κ_{β,1}, γ₃κ_{β,2}]` if `ε₂ < ∞`, and `σ_{H,1} = max[σ₀, γ₃θ₁(r-1)!, γ₃κ_{β,1}]` of
Lemma 5.5.6 (i) if `ε₂ = ∞`. -/
noncomputable def sigmaH : Option ℝ → ℝ
  | none => max P.σ₀ (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1))) (P.γ₃ * kappaBetaJ P p H β 1))
  | some _ => max P.σ₀ (max (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * (P.θ₂ * realFactorial (r - 2))))
      (max (P.γ₃ * kappaBetaJ P p H β 1) (P.γ₃ * kappaBetaJ P p H β 2)))

/-- The tolerance factor of (5.5.41): `ε₁^{(p+β-r)/(p+β-1)}` if `ε₂ = ∞`, and
`max[ε₁^{(p+β-r)/(p+β-1)}, ε₂^{(p+β-r)/(p+β-2)}]` if `ε₂ < ∞`. -/
noncomputable def epsMax (r ε₁ : ℝ) : Option ℝ → ℝ
  | none => ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
  | some e => max (ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
      (e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2)))

/-- The order of the guaranteed decrease (Lemma 5.5.6, Theorem 5.5.7):
`ε₁^{(p+β)/(p+β-1)}` if `ε₂ = ∞`, `min[ε₁^{(p+β)/(p+β-1)}, ε₂^{(p+β)/(p+β-2)}]` if `ε₂ < ∞`. -/
noncomputable def deltaEps (ε₁ : ℝ) : Option ℝ → ℝ
  | none => ε₁ ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1))
  | some e => min (ε₁ ^ (((p : ℝ) + β) / ((p : ℝ) + β - 1)))
      (e ^ (((p : ℝ) + β) / ((p : ℝ) + β - 2)))

/-- The decrease constant `κ_{H,1} = η₁/r! (α₁^r/σ_{H,1})^{1/(r-1)}` (Lemma 5.5.6 (i)) and
`κ_{H,2} = η₁/r! min[(α₁^r/σ_H)^{1/(r-1)}, (α₂^r/σ_H²)^{1/(r-2)}]` ((5.5.45)) of
[cartis2022evaluation]. -/
noncomputable def kappaH : Option ℝ → ℝ
  | none => P.η₁ / realFactorial r * (P.α₁ ^ r / sigmaH P p H β none) ^ (1 / (r - 1))
  | some e => P.η₁ / realFactorial r * min ((P.α₁ ^ r / sigmaH P p H β (some e)) ^ (1 / (r - 1)))
      ((P.α₂ ^ r / sigmaH P p H β (some e) ^ 2) ^ (1 / (r - 2)))

variable {P p H β}

theorem kappaBeta_nonneg (hH : 0 ≤ H) (hβ : 0 ≤ β) : 0 ≤ kappaBeta P p H β := by
  have := realFactorial_pos r
  have := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
  have := P.one_sub_η₂_pos
  unfold kappaBeta; positivity

theorem kappaBetaJ_nonneg (hH : 0 ≤ H) (hβ : 0 ≤ β) (j : ℝ) : 0 ≤ kappaBetaJ P p H β j := by
  have := realFactorial_pos (r - j)
  have := kappaBeta_nonneg (P := P) (p := p) hH hβ
  unfold kappaBetaJ; positivity

/-- `H/(p+β-1)! ≤ κ_β/(r-1)!` ((5.5.24)). -/
theorem div_holderFactorial_le_kappaBeta (hH : 0 ≤ H) (hβ : 0 ≤ β) (hr : 1 ≤ r) :
    H / holderFactorial (p - 1) β ≤ kappaBeta P p H β / realFactorial (r - 1) := by
  have hD := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
  have hF := realFactorial_pos (r - 1)
  have hη := P.one_sub_η₂_pos
  have hη1 : 1 - P.η₂ ≤ 1 := by linarith [P.η₂_pos]
  have hFr := realFactorial_sub_one_le hr
  unfold kappaBeta
  rw [div_div, div_le_div_iff₀ hD (by positivity)]
  have h1 : (1 - P.η₂) * realFactorial (r - 1) ≤ realFactorial r := by
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hH hD.le)
  nlinarith

/-- `H/(p+β-2)! ≤ κ_β/(r-2)!` for `p ≥ 2`, `p + β ≤ r` ((5.5.26)). -/
theorem div_holderFactorial_le_kappaBeta_two (hH : 0 ≤ H) (hβ : 0 ≤ β) (hp : 2 ≤ p)
    (hr : (p : ℝ) + β ≤ r) :
    H / holderFactorial (p - 2) β ≤ kappaBeta P p H β / realFactorial (r - 2) := by
  have hD := holderFactorial_pos (p - 2) (by linarith : (-1 : ℝ) < β)
  have hF := realFactorial_pos (r - 2)
  have hη := P.one_sub_η₂_pos
  have hη1 : 1 - P.η₂ ≤ 1 := by linarith [P.η₂_pos]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hD1 : holderFactorial (p - 1) β = holderFactorial (p - 2) β * ((p : ℝ) - 1 + β) := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this, holderFactorial_succ, Nat.cast_sub hp]
    push_cast; ring
  have hr2 : realFactorial r = r * (r - 1) * realFactorial (r - 2) :=
    realFactorial_eq_mul_mul_sub_two (by linarith)
  unfold kappaBeta
  have hq1 : 0 < (p : ℝ) - 1 + β := by linarith
  rw [hD1, hr2, div_div, div_le_div_iff₀ hD (by positivity)]
  have h1 : ((p : ℝ) - 1 + β) * (1 - P.η₂) ≤ r * (r - 1) := by
    have : ((p : ℝ) - 1 + β) * (1 - P.η₂) ≤ (p : ℝ) - 1 + β := by
      have : 0 ≤ (p : ℝ) - 1 + β := by linarith
      nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ H * holderFactorial (p - 2) β *
    realFactorial (r - 2))
  nlinarith

end Constants

/-- The three-term bound behind (5.5.23)–(5.5.25): if `G ≤ c T + σ/F U + θ U` with
`θ F ≤ σ`, `c ≤ κ/F` and `κ T ≤ σ U`, then `G ≤ 3 σ/F U`. -/
theorem le_three_mul_of_bound {G c κ F θ σ T U : ℝ} (hG : G ≤ c * T + σ / F * U + θ * U)
    (hF : 0 < F) (hθ : θ * F ≤ σ) (hc : c ≤ κ / F) (hκ : κ * T ≤ σ * U) (hT : 0 ≤ T)
    (hU : 0 ≤ U) : G ≤ 3 * (σ / F * U) := by
  have h1 : θ * U ≤ σ / F * U :=
    mul_le_mul_of_nonneg_right ((le_div_iff₀ hF).2 hθ) hU
  have h2 : c * T ≤ σ / F * U :=
    calc c * T ≤ κ / F * T := mul_le_mul_of_nonneg_right hc hT
      _ = κ * T / F := by ring
      _ ≤ σ * U / F := by gcongr
      _ = σ / F * U := by ring
  linarith

/-- `t^{p+β-r} t^{r-j} = t^{p+β-j}` for `t > 0`. -/
theorem rpow_mul_rpow_sub {t q j : ℝ} (ht : 0 < t) (r : ℝ) :
    t ^ (q - r) * t ^ (r - j) = t ^ (q - j) := by
  rw [← Real.rpow_add ht]; ring_nf

/-! ### Lemma 5.5.3 -/

section Lemma553

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.3** of [cartis2022evaluation] (successful iterations). Assume f.DpH and
`r ≥ p + β`. At an iteration `k` before termination, if
`σ_k ≥ max[θ₁ (r-1)!, κ_β ‖s_k‖^{p+β-r}]` (5.5.18) and, when `ε₂ < ∞`, also
`σ_k ≥ θ₂ (r-2)!` ((5.5.20)), then `ρ_k ≥ η₂` and the step-length tests (5.5.10)–(5.5.11)
hold: iteration `k` is very successful. -/
theorem lemma_5_5_3 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j)
    (h1 : P.θ₁ * realFactorial (r - 1) ≤ σ k)
    (h2 : ε₂.isSome → P.θ₂ * realFactorial (r - 2) ≤ σ k)
    (hκ : kappaBeta P p H β * ‖s k‖ ^ ((p : ℝ) + β - r) ≤ σ k) :
    P.η₂ ≤ taylorRatio f p x s k ∧ arpHLengthTest f P ε₂ (x k) (σ k) (s k) := by
  set t := ‖s k‖
  have ht : 0 < t := norm_pos_iff.2 (h.step_ne_zero hk)
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hr1 := h.one_lt_r
  have hH := hf.H_nonneg
  have hβ := hf.β_nonneg
  have hF1 := realFactorial_pos (r - 1)
  have hκ0 := kappaBeta_nonneg (P := P) (p := p) hH hβ
  -- the ratio
  have hdec := lemma_5_5_1 h hk
  have hrat := abs_reductionRatio_sub_one_le_of_holder convex_univ
    (fun y _ => hf.contDiff.contDiffAt) h.one_le_p hβ hf.holder (mem_univ (x k))
    (mem_univ (x k + s k)) (by have := realFactorial_pos r; positivity) hdec.le
  have hη := P.one_sub_η₂_pos
  have hratio : P.η₂ ≤ taylorRatio f p x s k := by
    have hD := holderFactorial_pos (p - 1) (by linarith : (-1 : ℝ) < β)
    have heq : realFactorial r * H / (holderFactorial (p - 1) β * σ k) * t ^ ((p : ℝ) + β - r) =
        (1 - P.η₂) * (kappaBeta P p H β * t ^ ((p : ℝ) + β - r)) / σ k := by
      unfold kappaBeta; field_simp
    have hle : (1 - P.η₂) * (kappaBeta P p H β * t ^ ((p : ℝ) + β - r)) / σ k ≤ 1 - P.η₂ := by
      rw [div_le_iff₀ hσ]; nlinarith
    rw [taylorRatio_def]
    have := neg_abs_le (reductionRatio f (x k) (s k)
      ((ftaylorSeries ℝ f (x k)).taylorDecrement p (s k)) - 1)
    linarith
  -- the step-length tests
  obtain ⟨hg, hl⟩ := lemma_5_5_2 hf h hk
  refine ⟨hratio, ?_, fun hs => ?_⟩
  · have hκT : kappaBeta P p H β * t ^ ((p : ℝ) + β - 1) ≤ σ k * t ^ (r - 1) := by
      rw [← rpow_mul_rpow_sub ht r, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hκ (by positivity)
    have h3 := le_three_mul_of_bound hg hF1 h1
      (div_holderFactorial_le_kappaBeta hH hβ hr1.le) hκT (by positivity) (by positivity)
    have hα := P.α₁_le
    have hα' : P.α₁ * 3 ≤ realFactorial (r - 1) := by
      have := min_le_right 1 (realFactorial (r - 1)); linarith
    have hα0 := P.α₁_pos
    calc P.α₁ * ‖gradient f (x k + s k)‖ ≤ P.α₁ * (3 * (σ k / realFactorial (r - 1) *
          t ^ (r - 1))) := mul_le_mul_of_nonneg_left h3 hα0.le
      _ = (P.α₁ * 3) / realFactorial (r - 1) * (σ k * t ^ (r - 1)) := by ring
      _ ≤ 1 * (σ k * t ^ (r - 1)) := by
          gcongr
          rw [div_le_one hF1]; exact hα'
      _ = σ k * t ^ (r - 1) := one_mul _
  · have hp2 := h.two_le_p hs
    have hF2 := realFactorial_pos (r - 2)
    have hκT : kappaBeta P p H β * t ^ ((p : ℝ) + β - 2) ≤ σ k * t ^ (r - 2) := by
      rw [← rpow_mul_rpow_sub ht r, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hκ (by positivity)
    have h3 := le_three_mul_of_bound (hl hs) hF2 (h2 hs)
      (div_holderFactorial_le_kappaBeta_two hH hβ hp2 hr) hκT (by positivity) (by positivity)
    have hα' : P.α₂ * 3 ≤ realFactorial (r - 2) := by
      have := P.α₂_le; have := min_le_right 1 (realFactorial (r - 2)); linarith
    have hα0 := P.α₂_pos
    calc -(P.α₂ * Chapter01.hessianMinEig f (x k + s k)) =
          P.α₂ * -Chapter01.hessianMinEig f (x k + s k) := by ring
      _ ≤ P.α₂ * (3 * (σ k / realFactorial (r - 2) * t ^ (r - 2))) :=
          mul_le_mul_of_nonneg_left h3 hα0.le
      _ = (P.α₂ * 3) / realFactorial (r - 2) * (σ k * t ^ (r - 2)) := by ring
      _ ≤ 1 * (σ k * t ^ (r - 2)) := by
          gcongr
          rw [div_le_one hF2]; exact hα'
      _ = σ k * t ^ (r - 2) := one_mul _

end Lemma553

/-! ### Lemma 5.5.4 -/

/-- f.DpH with `p ≥ 1` gives `p + β > 1`. -/
theorem AssumptionDpH.one_lt_add {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {H β : ℝ}
    (hf : AssumptionDpH f p H β) (hp : 1 ≤ p) : 1 < (p : ℝ) + β := by
  rcases Nat.lt_or_ge p 2 with h2 | h2
  · have hp1 : p = 1 := by omega
    have := hf.β_pos_of_eq_one hp1
    rw [hp1]; push_cast; linarith
  · have : (2 : ℝ) ≤ p := by exact_mod_cast h2
    linarith [hf.β_nonneg]

/-- The real-power step of the proof of Lemma 5.5.4: if `σ t^d < K` and `ε < 3K/F t^a`
(`a, d > 0`), then `σ < (F/3)^{-d/a} K^{1+d/a} ε^{-d/a}`. -/
theorem lt_of_rpow_bounds {σ t K F ε a d : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hK : 0 < K)
    (hF : 0 < F) (hε : 0 < ε) (ha : 0 < a) (hd : 0 < d) (h1 : σ * t ^ d < K)
    (h2 : ε < 3 * K / F * t ^ a) :
    σ < (F / 3) ^ (-(d / a)) * K ^ (1 + d / a) * ε ^ (-(d / a)) := by
  set c := 3 * K / F
  have hc : 0 < c := by positivity
  have hx : 0 < d / a := div_pos hd ha
  have h2' : ε / c < t ^ a := by rw [div_lt_iff₀ hc]; linarith
  have h3 : (ε / c) ^ (d / a) < t ^ d := by
    have := Real.rpow_lt_rpow (by positivity) h2' hx
    rwa [← Real.rpow_mul ht.le, mul_div_cancel₀ _ ha.ne'] at this
  have h4 : σ * (ε / c) ^ (d / a) < K :=
    (mul_lt_mul_of_pos_left h3 hσ).trans h1
  have hpos : 0 < (ε / c) ^ (d / a) := by positivity
  have h5 : σ < K / (ε / c) ^ (d / a) := by rw [lt_div_iff₀ hpos]; exact h4
  have heq : K / (ε / c) ^ (d / a) = (F / 3) ^ (-(d / a)) * K ^ (1 + d / a) * ε ^ (-(d / a)) := by
    have hc' : c = K * (F / 3)⁻¹ := by simp only [c]; field_simp
    rw [Real.div_rpow hε.le hc.le, hc', Real.mul_rpow hK.le (by positivity),
      Real.inv_rpow (by positivity), Real.rpow_add hK, Real.rpow_one, Real.rpow_neg (by positivity),
      Real.rpow_neg hε.le]
    have : 0 < ε ^ (d / a) := by positivity
    have : 0 < (F / 3) ^ (d / a) := by positivity
    have : 0 < K ^ (d / a) := by positivity
    field_simp
  rwa [heq] at h5

section Lemma554

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.4** of [cartis2022evaluation] (a lower bound on `σ_k` ensuring success). Assume
f.DpH, `r ≥ p + β`, and `p + β > 2` if `ε₂ < ∞`. At an iteration `k` before termination (in
particular the trial point does not terminate), if `σ_k ≥ σ̄` (the right-hand side of (5.5.27),
resp. (5.5.29)), then (5.5.18) holds, `σ_k ≥ κ_β ‖s_k‖^{p+β-r}`, and iteration `k` is very
successful (`ρ_k ≥ η₂` and (5.5.10)–(5.5.11) hold). -/
theorem lemma_5_5_4 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) (hσ : sigmaBar P p H β ε₁ ε₂ ≤ σ k) :
    kappaBeta P p H β * ‖s k‖ ^ ((p : ℝ) + β - r) ≤ σ k ∧
      P.η₂ ≤ taylorRatio f p x s k ∧ arpHLengthTest f P ε₂ (x k) (σ k) (s k) := by
  set q := (p : ℝ) + β
  set t := ‖s k‖
  set κ := kappaBeta P p H β
  have ht : 0 < t := norm_pos_iff.2 (h.step_ne_zero hk)
  have hσ0 := h.sigma_pos fun j hj => hk j hj.le
  have hq1 : 1 < q := hf.one_lt_add h.one_le_p
  have hH := hf.H_nonneg
  have hβ := hf.β_nonneg
  have hκ0 : 0 ≤ κ := kappaBeta_nonneg hH hβ
  have hε₁ := h.ε₁_pos
  -- the thresholds
  have h1 : P.θ₁ * realFactorial (r - 1) ≤ σ k := by
    cases ε₂ <;> simp only [sigmaBar, max_le_iff] at hσ <;> tauto
  have h2 : ε₂.isSome → P.θ₂ * realFactorial (r - 2) ≤ σ k := by
    cases ε₂ with
    | none => simp
    | some e => intro; simp only [sigmaBar, max_le_iff] at hσ; tauto
  have hb1 : kappaBetaJ P p H β 1 * ε₁ ^ ((q - r) / (q - 1)) ≤ σ k := by
    cases ε₂ <;> simp only [sigmaBar, max_le_iff] at hσ <;> tauto
  have hb2 : ∀ e ∈ ε₂, kappaBetaJ P p H β 2 * e ^ ((q - r) / (q - 2)) ≤ σ k := by
    cases ε₂ with
    | none => simp
    | some e =>
      intro e' he'
      rw [Option.mem_def, Option.some_inj] at he'
      subst he'
      simp only [sigmaBar, max_le_iff] at hσ; tauto
  have h18 : κ * t ^ (q - r) ≤ σ k := by
    by_contra hlt
    push Not at hlt
    have hκpos : 0 < κ := by
      rcases hκ0.eq_or_lt with h0 | h0
      · rw [← h0, zero_mul] at hlt; linarith
      · exact h0
    rcases hr.eq_or_lt with heq | hqr
    · -- `r = p + β`
      have hz : q - r = 0 := by linarith
      rw [hz, Real.rpow_zero, mul_one] at hlt
      have : kappaBetaJ P p H β 1 = κ := by
        unfold kappaBetaJ
        rw [show (p : ℝ) + β - r = 0 by linarith, zero_div, Real.rpow_zero, one_mul,
          show (r - 1) / ((p : ℝ) + β - 1) = 1 by rw [div_eq_one_iff_eq (by linarith)]; linarith,
          Real.rpow_one]
      rw [hz, zero_div, Real.rpow_zero, mul_one, this] at hb1
      linarith
    · set d := r - q
      have hd : 0 < d := sub_pos.2 hqr
      have hσt : σ k * t ^ d < κ := by
        have h0 : t ^ (q - r) * t ^ d = 1 := by
          rw [rpow_mul_rpow_sub ht r, sub_self, Real.rpow_zero]
        have := mul_lt_mul_of_pos_right hlt (by positivity : 0 < t ^ d)
        rwa [mul_assoc, h0, mul_one] at this
      obtain ⟨hg, hl⟩ := lemma_5_5_2 hf h hk
      have hnot := not_stopTest_trial hk
      -- the case `‖∇f(x_k + s_k)‖ > ε₁`
      have hcase1 : ¬ ε₁ < ‖gradient f (x k + s k)‖ := by
        intro hgt
        have hF1 := realFactorial_pos (r - 1)
        have hA : H / holderFactorial (p - 1) β * t ^ (q - 1) ≤ κ / realFactorial (r - 1) *
            t ^ (q - 1) :=
          mul_le_mul_of_nonneg_right (div_holderFactorial_le_kappaBeta hH hβ h.one_lt_r.le)
            (by positivity)
        have hsplit : t ^ (r - 1) = t ^ d * t ^ (q - 1) := (rpow_mul_rpow_sub ht q).symm
        have hB : σ k / realFactorial (r - 1) * t ^ (r - 1) < κ / realFactorial (r - 1) *
            t ^ (q - 1) := by
          rw [hsplit, div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_assoc]
          gcongr
        have hθ : P.θ₁ * t ^ (r - 1) ≤ σ k / realFactorial (r - 1) * t ^ (r - 1) :=
          mul_le_mul_of_nonneg_right ((le_div_iff₀ hF1).2 h1) (by positivity)
        have h3 : ε₁ < 3 * κ / realFactorial (r - 1) * t ^ (q - 1) := by
          have : 3 * κ / realFactorial (r - 1) * t ^ (q - 1) =
              3 * (κ / realFactorial (r - 1) * t ^ (q - 1)) := by ring
          linarith
        have key := lt_of_rpow_bounds hσ0 ht hκpos hF1 hε₁ (by linarith) hd hσt h3
        have e1 : -(d / (q - 1)) = (q - r) / (q - 1) := by simp only [d]; ring
        have e2 : 1 + d / (q - 1) = (r - 1) / (q - 1) := by
          have hne : q - 1 ≠ 0 := by linarith
          rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; simp only [d]; ring
        rw [e1, e2] at key
        have : kappaBetaJ P p H β 1 * ε₁ ^ ((q - r) / (q - 1)) =
            (realFactorial (r - 1) / 3) ^ ((q - r) / (q - 1)) * κ ^ ((r - 1) / (q - 1)) *
              ε₁ ^ ((q - r) / (q - 1)) := by
          unfold kappaBetaJ; rfl
        linarith
      cases ε₂ with
      | none =>
        rw [stopTest_none, not_le] at hnot
        exact hcase1 hnot
      | some e =>
        rcases not_stopTest_some.1 hnot with hgt | hlam
        · exact hcase1 hgt
        · have he := h.ε₂_pos e rfl
          have hq2' : 2 < q := hq2 rfl
          have hp2 := h.two_le_p rfl
          have hF2 := realFactorial_pos (r - 2)
          have hA : H / holderFactorial (p - 2) β * t ^ (q - 2) ≤ κ / realFactorial (r - 2) *
              t ^ (q - 2) :=
            mul_le_mul_of_nonneg_right (div_holderFactorial_le_kappaBeta_two hH hβ hp2 hr)
              (by positivity)
          have hsplit : t ^ (r - 2) = t ^ d * t ^ (q - 2) := (rpow_mul_rpow_sub ht q).symm
          have hB : σ k / realFactorial (r - 2) * t ^ (r - 2) < κ / realFactorial (r - 2) *
              t ^ (q - 2) := by
            rw [hsplit, div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_assoc]
            gcongr
          have hθ : P.θ₂ * t ^ (r - 2) ≤ σ k / realFactorial (r - 2) * t ^ (r - 2) :=
            mul_le_mul_of_nonneg_right ((le_div_iff₀ hF2).2 (h2 rfl)) (by positivity)
          have hl' := hl rfl
          have h3 : e < 3 * κ / realFactorial (r - 2) * t ^ (q - 2) := by
            have : 3 * κ / realFactorial (r - 2) * t ^ (q - 2) =
                3 * (κ / realFactorial (r - 2) * t ^ (q - 2)) := by ring
            linarith
          have key := lt_of_rpow_bounds hσ0 ht hκpos hF2 he (by linarith) hd hσt h3
          have e1 : -(d / (q - 2)) = (q - r) / (q - 2) := by simp only [d]; ring
          have e2 : 1 + d / (q - 2) = (r - 2) / (q - 2) := by
            have hne : q - 2 ≠ 0 := by linarith
            rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]; simp only [d]; ring
          rw [e1, e2] at key
          have hb := hb2 e rfl
          have : kappaBetaJ P p H β 2 * e ^ ((q - r) / (q - 2)) =
              (realFactorial (r - 2) / 3) ^ ((q - r) / (q - 2)) * κ ^ ((r - 2) / (q - 2)) *
                e ^ ((q - r) / (q - 2)) := by
            unfold kappaBetaJ; rfl
          linarith
  exact ⟨h18, lemma_5_5_3 hf h hr hk h1 h2 h18⟩

end Lemma554

/-! ### Lemma 5.5.5 -/

section Lemma555

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- `ε^{(p+β-r)/(p+β-j)} ≥ 1` for `ε ∈ (0, 1]`, `r ≥ p + β > j`. -/
theorem one_le_rpow_exponent {ε q j : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hqj : j < q) (hr : q ≤ r) :
    1 ≤ ε ^ ((q - r) / (q - j)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- `M = epsMax ≥ 1` (the tolerances are at most `1`). -/
theorem one_le_epsMax (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) : 1 ≤ epsMax p β r ε₁ ε₂ := by
  have hq1 := hf.one_lt_add h.one_le_p
  cases ε₂ with
  | none => exact one_le_rpow_exponent h.ε₁_pos h.ε₁_le_one hq1 hr
  | some e => exact le_max_of_le_left (one_le_rpow_exponent h.ε₁_pos h.ε₁_le_one hq1 hr)

/-- **Lemma 5.5.5** of [cartis2022evaluation] (an upper bound on `σ_k`). Assume f.DpH,
`r ≥ p + β`, and `p + β > 2` if `ε₂ < ∞`. For every iteration `k` up to (and including)
termination, `σ_k ≤ max(σ₀, γ₃ σ̄)` ((5.5.39), (5.5.40), `σ̄ = sigmaBar`), and hence
`σ_k ≤ σ_H max[ε₁^{(p+β-r)/(p+β-1)}, ε₂^{(p+β-r)/(p+β-2)}]` (5.5.41) (`σ_k ≤ σ_{H,1}
ε₁^{(p+β-r)/(p+β-1)}` if `ε₂ = ∞`). -/
theorem lemma_5_5_5 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j < k, ¬ arpHStop f ε₁ ε₂ x s j) :
    σ k ≤ max P.σ₀ (P.γ₃ * sigmaBar P p H β ε₁ ε₂) ∧
      σ k ≤ sigmaH P p H β ε₂ * epsMax p β r ε₁ ε₂ := by
  have hforce : ∀ k, (∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) →
      sigmaBar P p H β ε₁ ε₂ ≤ σ k → P.η₂ ≤ arpHRatio f p P ε₂ x s σ k := by
    intro k hk hσ
    obtain ⟨-, hρ, hlen⟩ := lemma_5_5_4 hf h hr hq2 hk hσ
    rw [arpHRatio, arpHRatioAt_of_lengthTest hlen]
    exact hρ
  have h1 := (h.run.sigma_le_max hforce hk k le_rfl).2.2
  refine ⟨h1, h1.trans ?_⟩
  have hM := one_le_epsMax hf h hr hq2
  have hγ := P.γ₃_pos.le
  have hq1 := hf.one_lt_add h.one_le_p
  have hε₁ := h.ε₁_pos
  have hσ₀ := P.σ₀_pos
  cases ε₂ with
  | none =>
    simp only [sigmaH, sigmaBar, epsMax] at hM ⊢
    set M := ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
    set S := max P.σ₀ (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * kappaBetaJ P p H β 1))
    have hS : 0 ≤ S := hσ₀.le.trans (le_max_left _ _)
    have hSM : S ≤ S * M := le_mul_of_one_le_right hS hM
    refine max_le ((le_max_left _ _).trans hSM) ?_
    rw [mul_max_of_nonneg _ _ hγ]
    refine max_le (le_trans ?_ hSM) ?_
    · exact le_max_of_le_right (le_max_left _ _)
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (by positivity)
  | some e =>
    have he := h.ε₂_pos e rfl
    simp only [sigmaH, sigmaBar, epsMax] at hM ⊢
    set E₁ := ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1))
    set E₂ := e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))
    set S := max P.σ₀ (max (max (P.γ₃ * (P.θ₁ * realFactorial (r - 1)))
      (P.γ₃ * (P.θ₂ * realFactorial (r - 2))))
      (max (P.γ₃ * kappaBetaJ P p H β 1) (P.γ₃ * kappaBetaJ P p H β 2)))
    have hS : 0 ≤ S := hσ₀.le.trans (le_max_left _ _)
    have hSM : S ≤ S * max E₁ E₂ := le_mul_of_one_le_right hS hM
    refine max_le ((le_max_left _ _).trans hSM) ?_
    rw [mul_max_of_nonneg _ _ hγ, mul_max_of_nonneg _ _ hγ, mul_max_of_nonneg _ _ hγ]
    refine max_le (max_le (le_trans ?_ hSM) (le_trans ?_ hSM)) (max_le ?_ ?_)
    · exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
    · exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    · rw [← mul_assoc]
      exact mul_le_mul (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
        (le_max_left _ _) (by positivity) hS
    · rw [← mul_assoc]
      exact mul_le_mul (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
        (le_max_right _ _) (by positivity) hS

end Lemma555

/-! ### Lemma 5.5.6 -/

/-- The real-power chain of the proof of Lemma 5.5.6: if the step-length test
`α g ≤ σ t^m` holds (`0 < m ≤ r`), `σ ≤ S M` and `δ^m M^{r-m} ≤ g^r`, then
`(α^r/S^{r-m})^{1/m} δ ≤ σ t^r`. -/
theorem rpow_mul_le_mul_rpow {σ t α g m r S M δ : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (hα : 0 < α)
    (hg : 0 < g) (hm : 0 < m) (hmr : m ≤ r) (hS : 0 < S) (hM : 0 < M) (hσS : σ ≤ S * M)
    (hδ : 0 ≤ δ) (hlen : α * g ≤ σ * t ^ m) (hδM : δ ^ m * M ^ (r - m) ≤ g ^ r) :
    (α ^ r / S ^ (r - m)) ^ (1 / m) * δ ≤ σ * t ^ r := by
  have hr : 0 < r := hm.trans_le hmr
  have hrm : 0 ≤ r - m := sub_nonneg.2 hmr
  have him : 0 ≤ 1 / m := by positivity
  -- `(α^r g^r/σ^{r-m})^{1/m} ≤ σ t^r`
  have h1 : (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) ≤ σ * t ^ r := by
    have hY : 0 ≤ σ * t ^ r := by positivity
    have hX : α ^ r * g ^ r / σ ^ (r - m) ≤ (σ * t ^ r) ^ m := by
      have heq : (σ * t ^ r) ^ m * σ ^ (r - m) = (σ * t ^ m) ^ r := by
        rw [Real.mul_rpow hσ.le (by positivity), Real.mul_rpow hσ.le (by positivity),
          ← Real.rpow_mul ht, ← Real.rpow_mul ht, mul_comm r m,
          show σ ^ r = σ ^ m * σ ^ (r - m) by rw [← Real.rpow_add hσ]; ring_nf]
        ring
      rw [div_le_iff₀ (by positivity), heq, ← Real.mul_rpow hα.le hg.le]
      exact Real.rpow_le_rpow (by positivity) hlen hr.le
    calc (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) ≤ ((σ * t ^ r) ^ m) ^ (1 / m) :=
          Real.rpow_le_rpow (by positivity) hX him
      _ = σ * t ^ r := by rw [one_div, Real.rpow_rpow_inv hY hm.ne']
  -- replace `σ` by `S M`
  have h2 : (α ^ r * g ^ r / (S * M) ^ (r - m)) ^ (1 / m) ≤
      (α ^ r * g ^ r / σ ^ (r - m)) ^ (1 / m) := by
    refine Real.rpow_le_rpow (by positivity) ?_ him
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (Real.rpow_le_rpow hσ.le hσS hrm)
  have h3 : (α ^ r * g ^ r / (S * M) ^ (r - m)) ^ (1 / m) =
      (α ^ r / S ^ (r - m)) ^ (1 / m) * (g ^ r / M ^ (r - m)) ^ (1 / m) := by
    have : α ^ r * g ^ r / (S * M) ^ (r - m) = (α ^ r / S ^ (r - m)) * (g ^ r / M ^ (r - m)) := by
      rw [Real.mul_rpow hS.le hM.le]; field_simp
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
  have h4 : δ ≤ (g ^ r / M ^ (r - m)) ^ (1 / m) := by
    have : δ ^ m ≤ g ^ r / M ^ (r - m) := by rw [le_div_iff₀ (by positivity)]; exact hδM
    calc δ = (δ ^ m) ^ (1 / m) := by rw [one_div, Real.rpow_rpow_inv hδ hm.ne']
      _ ≤ _ := Real.rpow_le_rpow (by positivity) this him
  calc (α ^ r / S ^ (r - m)) ^ (1 / m) * δ ≤
        (α ^ r / S ^ (r - m)) ^ (1 / m) * (g ^ r / M ^ (r - m)) ^ (1 / m) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := h3.symm
    _ ≤ _ := h2
    _ ≤ _ := h1

/-- The tolerance algebra of (5.5.48)–(5.5.51), first-order case `ε₂ = ∞`:
`(ε^{q/(q-1)})^{r-1} ε^{(q-r)/(q-1)} = ε^r`. -/
theorem rpow_tolerance_eq {ε q r : ℝ} (hε : 0 < ε) (hq : 1 < q) :
    (ε ^ (q / (q - 1))) ^ (r - 1) * (ε ^ ((q - r) / (q - 1))) ^ (r - (r - 1)) = ε ^ r := by
  rw [← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le, ← Real.rpow_add hε]
  congr 1
  have : q - 1 ≠ 0 := by linarith
  field_simp; ring

/-- The tolerance algebra of (5.5.48)–(5.5.51) when `ε₂ < ∞`: with
`δ = min[ε₁^{q/(q-1)}, ε₂^{q/(q-2)}]` and `M = max[ε₁^{(q-r)/(q-1)}, ε₂^{(q-r)/(q-2)}]`
(`r ≥ q > 2`), `δ^{r-1} M ≤ ε₁^r` and `δ^{r-2} M² ≤ ε₂^r`. -/
theorem rpow_tolerance_le {ε₁ ε₂ q r : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hq : 2 < q)
    (hr : q ≤ r) :
    (min (ε₁ ^ (q / (q - 1))) (ε₂ ^ (q / (q - 2)))) ^ (r - 1) *
        (max (ε₁ ^ ((q - r) / (q - 1))) (ε₂ ^ ((q - r) / (q - 2)))) ^ (r - (r - 1)) ≤
        ε₁ ^ r ∧
      (min (ε₁ ^ (q / (q - 1))) (ε₂ ^ (q / (q - 2)))) ^ (r - 2) *
        (max (ε₁ ^ ((q - r) / (q - 1))) (ε₂ ^ ((q - r) / (q - 2)))) ^ (r - (r - 2)) ≤
        ε₂ ^ r := by
  set X₁ := Real.log ε₁ / (q - 1)
  set X₂ := Real.log ε₂ / (q - 2)
  have ha₁ : q - 1 ≠ 0 := by linarith
  have ha₂ : q - 2 ≠ 0 := by linarith
  have hL₁ : Real.log ε₁ = X₁ * (q - 1) := by simp only [X₁]; field_simp
  have hL₂ : Real.log ε₂ = X₂ * (q - 2) := by simp only [X₂]; field_simp
  have e1 : ε₁ ^ (q / (q - 1)) = Real.exp (q * X₁) := by
    rw [Real.rpow_def_of_pos hε₁, hL₁]; congr 1; field_simp
  have e2 : ε₂ ^ (q / (q - 2)) = Real.exp (q * X₂) := by
    rw [Real.rpow_def_of_pos hε₂, hL₂]; congr 1; field_simp
  have e3 : ε₁ ^ ((q - r) / (q - 1)) = Real.exp ((q - r) * X₁) := by
    rw [Real.rpow_def_of_pos hε₁, hL₁]; congr 1; field_simp
  have e4 : ε₂ ^ ((q - r) / (q - 2)) = Real.exp ((q - r) * X₂) := by
    rw [Real.rpow_def_of_pos hε₂, hL₂]; congr 1; field_simp
  have e5 : ε₁ ^ r = Real.exp (X₁ * (q - 1) * r) := by rw [Real.rpow_def_of_pos hε₁, hL₁]
  have e6 : ε₂ ^ r = Real.exp (X₂ * (q - 2) * r) := by rw [Real.rpow_def_of_pos hε₂, hL₂]
  rw [e1, e2, e3, e4, e5, e6]
  have hq0 : 0 ≤ q := by linarith
  have hqr : q - r ≤ 0 := by linarith
  have hr0 : 0 ≤ r := by linarith
  rcases le_total X₁ X₂ with h12 | h21
  · rw [min_eq_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h12 hq0)),
      max_eq_left (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left h12 hqr))]
    simp only [← Real.exp_mul, ← Real.exp_add]
    refine ⟨le_of_eq (by congr 1; ring), Real.exp_le_exp.2 ?_⟩
    have : X₁ * ((q - 2) * r) ≤ X₂ * ((q - 2) * r) :=
      mul_le_mul_of_nonneg_right h12 (by nlinarith)
    nlinarith
  · rw [min_eq_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h21 hq0)),
      max_eq_right (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left h21 hqr))]
    simp only [← Real.exp_mul, ← Real.exp_add]
    refine ⟨Real.exp_le_exp.2 ?_, le_of_eq (by congr 1; ring)⟩
    have : X₂ * ((q - 1) * r) ≤ X₁ * ((q - 1) * r) :=
      mul_le_mul_of_nonneg_right h21 (by nlinarith)
    nlinarith

section Lemma556

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 5.5.6** of [cartis2022evaluation] (decrease on successful iterations). Assume f.DpH,
`r ≥ p + β` (`p + β > 1` follows from f.DpH), and `p + β > 2` if `ε₂ < ∞`. On every successful
iteration `k` before termination,
(i) if `ε₂ = ∞`: `f(x_k) - f(x_{k+1}) ≥ κ_{H,1} ε₁^{(p+β)/(p+β-1)}`;
(ii) if `ε₂ < ∞`: `f(x_k) - f(x_{k+1}) ≥ κ_{H,2} min[ε₁^{(p+β)/(p+β-1)}, ε₂^{(p+β)/(p+β-2)}]`
(5.5.44), with `κ_{H,j} = kappaH` ((5.5.45)). -/
theorem lemma_5_5_6 (hf : AssumptionDpH f p H β) (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ)
    (hr : (p : ℝ) + β ≤ r) (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) (hs : P.η₁ ≤ arpHRatio f p P ε₂ x s σ k) :
    kappaH P p H β ε₂ * deltaEps p β ε₁ ε₂ ≤ f (x k) - f (x (k + 1)) := by
  set q := (p : ℝ) + β
  set t := ‖s k‖
  obtain ⟨hρ, hlen⟩ := le_arpHRatioAt_iff.1 hs
  have hx1 : x (k + 1) = x k + s k := h.run.eq_add_of_succ hk hs
  have hσ := h.sigma_pos fun j hj => hk j hj.le
  have hr1 := h.one_lt_r
  have hq1 : 1 < q := hf.one_lt_add h.one_le_p
  have hε₁ := h.ε₁_pos
  have hrf := realFactorial_pos r
  have ht : 0 ≤ t := norm_nonneg _
  have hdec := lemma_5_5_1 h hk
  have hΔ : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
    lt_of_le_of_lt (by positivity) hdec
  have hfd := sub_le_of_le_reductionRatio hΔ hρ
  rw [← hx1] at hfd
  have hD : P.η₁ / realFactorial r * (σ k * t ^ r) ≤ f (x k) - f (x (k + 1)) := by
    have := mul_le_mul_of_nonneg_left hdec.le P.η₁_pos.le
    calc P.η₁ / realFactorial r * (σ k * t ^ r) = P.η₁ * (σ k / realFactorial r * t ^ r) := by
          ring
      _ ≤ _ := this
      _ ≤ _ := hfd
  have hσmax := (lemma_5_5_5 hf h hr hq2 fun j hj => hk j hj.le).2
  have hM := one_le_epsMax hf h hr hq2
  have hSpos : 0 < sigmaH P p H β ε₂ := by
    cases ε₂ <;> exact P.σ₀_pos.trans_le (le_max_left _ _)
  have hnot := not_stopTest_trial hk
  have hη : 0 ≤ P.η₁ / realFactorial r := by have := P.η₁_pos; positivity
  have hpow : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → a ^ r ≤ b ^ r := fun ha hab =>
    Real.rpow_le_rpow ha hab (by linarith)
  refine le_trans ?_ hD
  cases ε₂ with
  | none =>
    rw [stopTest_none, not_le] at hnot
    simp only [kappaH, deltaEps, epsMax, sigmaH] at hσmax hM hSpos ⊢
    have key := rpow_mul_le_mul_rpow hσ ht P.α₁_pos (hε₁.trans hnot) (by linarith)
      (by linarith) hSpos (by linarith) hσmax (by positivity) hlen.1
      ((rpow_tolerance_eq hε₁ hq1).le.trans (hpow hε₁.le hnot.le))
    rw [show r - (r - 1) = 1 by ring, Real.rpow_one] at key
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left key hη
  | some e =>
    have he := h.ε₂_pos e rfl
    have hq2' : 2 < q := hq2 rfl
    have tol := rpow_tolerance_le hε₁ he hq2' hr
    simp only [kappaH, deltaEps, epsMax] at hσmax hM ⊢
    rcases not_stopTest_some.1 hnot with hg | hl
    · have key := rpow_mul_le_mul_rpow hσ ht P.α₁_pos (hε₁.trans hg) (by linarith)
        (by linarith) hSpos (by linarith) hσmax (by positivity) hlen.1
        (tol.1.trans (hpow hε₁.le hg.le))
      rw [show r - (r - 1) = 1 by ring, Real.rpow_one] at key
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ key) hη
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    · have hg2 : e < -Chapter01.hessianMinEig f (x k + s k) := by linarith
      have hlen2 : P.α₂ * -Chapter01.hessianMinEig f (x k + s k) ≤ σ k * t ^ (r - 2) := by
        have := hlen.2 rfl; linarith
      have key := rpow_mul_le_mul_rpow hσ ht P.α₂_pos (he.trans hg2)
        (by linarith [h.two_lt_r rfl]) (by linarith) hSpos (by linarith) hσmax
        (by positivity) hlen2 (tol.2.trans (hpow he.le hg2.le))
      rw [show r - (r - 2) = (2 : ℝ) by ring, Real.rpow_two] at key
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ key) hη
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)

end Lemma556

/-! ### Theorem 5.5.7 -/

/-- The logarithmic tolerance terms of (5.5.52), multiplied by `log γ₂`:
`(r-p-β)/(p+β-1) |log ε₁|`, plus `(r-p-β)/(p+β-2) |log ε₂|` if `ε₂ < ∞`. -/
noncomputable def epsLogTerm (p : ℕ) (β r ε₁ : ℝ) : Option ℝ → ℝ
  | none => (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁|
  | some e => (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁| +
      (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log e|

/-- `log ε^{(q-r)/(q-j)} ≤ (r-q)/(q-j) |log ε|` for `q > j`, `r ≥ q`. -/
theorem log_rpow_exponent_le {ε q j : ℝ} (hε : 0 < ε) (hqj : j < q) (hr : q ≤ r) :
    Real.log (ε ^ ((q - r) / (q - j))) ≤ (r - q) / (q - j) * |Real.log ε| := by
  rw [Real.log_rpow hε]
  have hc : 0 ≤ (r - q) / (q - j) := div_nonneg (by linarith) (by linarith)
  have : (q - r) / (q - j) * Real.log ε = (r - q) / (q - j) * -Real.log ε := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (neg_le_abs _) hc

section Theorem557

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpHParams r} {ε₁ H β flow : ℝ}
  {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

theorem kappaH_pos :
    0 < kappaH P p H β ε₂ := by
  have := P.η₁_pos; have := realFactorial_pos r; have := P.α₁_pos; have := P.α₂_pos
  cases ε₂ with
  | none =>
    have : 0 < sigmaH P p H β none := P.σ₀_pos.trans_le (le_max_left _ _)
    simp only [kappaH]; positivity
  | some e =>
    have : 0 < sigmaH P p H β (some e) := P.σ₀_pos.trans_le (le_max_left _ _)
    simp only [kappaH]
    refine mul_pos (by positivity) (lt_min (by positivity) (by positivity))

theorem deltaEps_pos (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) : 0 < deltaEps p β ε₁ ε₂ := by
  have := h.ε₁_pos
  cases ε₂ with
  | none => simp only [deltaEps]; positivity
  | some e =>
    have := h.ε₂_pos e rfl
    simp only [deltaEps]; exact lt_min (by positivity) (by positivity)

/-- **Theorem 5.5.7** of [cartis2022evaluation] (complexity of ARp-H). Assume f.Bb, f.DpH,
`r ≥ p + β`, and `p + β > 2` if `ε₂ < ∞`. Every ARp-H run terminates at some iteration `k_ε`
(first index of the test at `x₀` or at a trial point), with an output `x_ε` (`x₀` if `k_ε = 0`
and the test holds there, else the trial point `x_{k_ε} + s_{k_ε}`) satisfying the termination
test, and
* (5.5.52) `k_ε + 2` is at most the bound below; it bounds both the number of evaluations of
  the first (and second) derivatives needed by the termination test (at `x₀` and at the trial
  points of iterations `0, …, k_ε`, at most `k_ε + 2`) and the number of evaluations of `f` (at
  `x₀` and at the trial points of iterations `0, …, k_ε - 1`, at most `k_ε + 1`):
  `κ^A (f(x₀) - f_low)/δ_ε + (κ^B₁ |log ε₁| + κ^B₂ |log ε₂|) + κ^C`, with
  `δ_ε = deltaEps` (`min[ε₁^{(p+β)/(p+β-1)}, ε₂^{(p+β)/(p+β-2)}]`), `κ^S = 1/κ_H`,
  `κ^A = κ^S (1 + |log γ₁|/log γ₂)`, `κ^B_j = (r-p-β)/((p+β-j) log γ₂)` (`epsLogTerm/log γ₂`) and
  `κ^C = (|log γ₁| + log(σ_H/σ₀))/log γ₂ + 2` (the book's `κ^C` lacks the `+ 2`);
* the number of evaluations of the derivatives of orders up to `p` (at `x₀` and after each
  successful iteration) is at most `κ^S (f(x₀) - f_low)/δ_ε + 1`. -/
theorem theorem_5_5_7 (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpH f p H β)
    (h : algorithm_5_5_1 f p P ε₁ ε₂ x s σ) (hr : (p : ℝ) + β ≤ r)
    (hq2 : ε₂.isSome → 2 < (p : ℝ) + β) :
    ∃ kε, IsFirstHit (arpHStop f ε₁ ε₂ x s) kε ∧
      (∃ xε, (kε = 0 ∧ xε = x 0 ∨ xε = x kε + s kε) ∧ stopTest f ε₁ ε₂ xε) ∧
      (kε : ℝ) + 2 ≤
        1 / kappaH P p H β ε₂ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) /
            deltaEps p β ε₁ ε₂ + epsLogTerm p β r ε₁ ε₂ / Real.log P.γ₂ +
          ((|Real.log P.γ₁| + Real.log (sigmaH P p H β ε₂ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ arpHRatio f p P ε₂ x s σ k) kε : ℝ) ≤
        1 / kappaH P p H β ε₂ * (f (x 0) - flow) / deltaEps p β ε₁ ε₂ + 1 := by
  set κ := kappaH P p H β ε₂
  set δε := deltaEps p β ε₁ ε₂
  set S := sigmaH P p H β ε₂
  set M := epsMax p β r ε₁ ε₂
  have hκ : 0 < κ := kappaH_pos
  have hδε : 0 < δε := deltaEps_pos h
  have hδ : 0 < κ * δε := mul_pos hκ hδε
  have hM := one_le_epsMax hf h hr hq2
  have hS : 0 < S := by cases ε₂ <;> exact P.σ₀_pos.trans_le (le_max_left _ _)
  have hσ₀ := P.σ₀_pos
  have hlog := P.log_γ₂_pos
  have hdec : ∀ k, (∀ j ≤ k, ¬ arpHStop f ε₁ ε₂ x s j) →
      P.η₁ ≤ arpHRatio f p P ε₂ x s σ k → κ * δε ≤ f (x k) - f (x (k + 1)) :=
    fun k hk hs => lemma_5_5_6 hf h hr hq2 hk hs
  obtain ⟨kε, hK, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease_of_le (σmax := S * M)
    (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => (lemma_5_5_5 hf h hr hq2 hk).2) hδ
    (fun k hk => by
      by_cases hs : P.η₁ ≤ arpHRatio f p P ε₂ x s σ k
      · have := hdec k hk hs; linarith
      · rw [h.run.eq_of_not_succ hk (not_le.1 hs)])
    (fun k _ => hb _) hdec
  refine ⟨kε, hK, ?_, ?_, ?_⟩
  · rcases hK.test with ⟨h0, ht⟩ | ht
    · exact ⟨x 0, Or.inl ⟨h0, rfl⟩, by rwa [h0] at ht⟩
    · exact ⟨x kε + s kε, Or.inr rfl, ht⟩
  · have hX : (f (x 0) - flow) / (κ * δε) = 1 / κ * (f (x 0) - flow) / δε := by
      field_simp
    have hlogM : Real.log M ≤ epsLogTerm p β r ε₁ ε₂ := by
      have hq1 := hf.one_lt_add h.one_le_p
      cases ε₂ with
      | none => exact log_rpow_exponent_le h.ε₁_pos hq1 hr
      | some e =>
        have he := h.ε₂_pos e rfl
        have h1 := log_rpow_exponent_le (r := r) h.ε₁_pos hq1 hr
        have h2 := log_rpow_exponent_le (r := r) he (hq2 rfl) hr
        have hc1 : 0 ≤ (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 1) * |Real.log ε₁| :=
          mul_nonneg (div_nonneg (by linarith) (by linarith)) (abs_nonneg _)
        have hc2 : 0 ≤ (r - ((p : ℝ) + β)) / ((p : ℝ) + β - 2) * |Real.log e| :=
          mul_nonneg (div_nonneg (by linarith) (by linarith [hq2 rfl])) (abs_nonneg _)
        simp only [M, epsMax, epsLogTerm] at h1 h2 ⊢
        rcases max_choice (ε₁ ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 1)))
          (e ^ (((p : ℝ) + β - r) / ((p : ℝ) + β - 2))) with hm | hm <;> rw [hm] <;> linarith
    have hlogS : Real.log (S * M / P.σ₀) = Real.log (S / P.σ₀) + Real.log M := by
      rw [mul_div_right_comm, Real.log_mul (by positivity) (by positivity)]
    have hγ : 0 ≤ |Real.log P.γ₁| / Real.log P.γ₂ := by positivity
    rw [funEvalCount, hX, hlogS] at hF
    push_cast at hF
    have : (Real.log (S / P.σ₀) + Real.log M) / Real.log P.γ₂ ≤
        epsLogTerm p β r ε₁ ε₂ / Real.log P.γ₂ + Real.log (S / P.σ₀) / Real.log P.γ₂ := by
      rw [← add_div, add_comm (epsLogTerm _ _ _ _ _)]
      exact div_le_div_of_nonneg_right (by linarith) hlog.le
    have e1 : 1 / κ * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f (x 0) - flow) / δε =
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (1 / κ * (f (x 0) - flow) / δε) := by ring
    rw [e1, add_div (|Real.log P.γ₁|)]
    linarith
  · have hX : (f (x 0) - flow) / (κ * δε) = 1 / κ * (f (x 0) - flow) / δε := by
      field_simp
    rwa [hX] at hD

end Theorem557

end CartisGouldToint.Chapter05
