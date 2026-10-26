import Numlib.Optimization.ModelBased.ARRun

/-!
# The ARp method as a generic AR run

The adaptive-regularization method with `p`-th order Taylor models of [cartis2022evaluation]
(Algorithm 4.1.1, ARp) as an instance of `Optimization.IsARRun`, with the Step-1 termination test
as a parameter: Chapter 4 uses the tests (4.1.5)–(4.1.9), ARpLE (Algorithm 5.1.1) runs ARp on
`Φ_ℓ = ‖r‖^ℓ/ℓ` with residual-scaled tests, and the measure-dominated analysis of Section 5.3 uses
no test at all. The Step-2 conditions (4.1.10)–(4.1.14) and their one-iteration consequences
(Lemmas 4.1.3 and 4.1.4) do not depend on the test and are proved once here.

## Conventions

`q ∈ {1, 2, 3}` is the order of criticality sought (the book's `ε₂ = ε₃ = ∞` is `q = 1`,
`ε₂ < ∞ = ε₃` is `q = 2`, both finite is `q = 3`): the second-order step condition (4.1.12) is
imposed iff `2 ≤ q`, the third-order one (4.1.13) iff `3 ≤ q`. The model is
`m_k = regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)`, the ratio `taylorRatio f p x s` (4.1.15)
and the update (4.1.16) is `ARUpdate`.

## Main definitions

* `Optimization.ARpParams`: the AR constants plus `θ₁, θ₂, θ₃ ∈ (0, 1]`.
* `Optimization.smallCurvatureDirections A c`: unit directions of curvature at most `c` in
  absolute value (the sets `𝓜_k` of (4.1.14) and `𝒵_ε` of (4.1.4)).
* `Optimization.IsARpStep f p P q x σ s`: the step conditions (4.1.10)–(4.1.13).
* `Optimization.IsARpRun f p P q test x s σ`: an ARp run.

## Main statements

* `Optimization.IsARpRun.sigma_le`: Lemma 4.1.2;
* `Optimization.IsARpRun.step_lower_bounds`: Lemma 4.1.3;
* `Optimization.IsARpRun.decrease_ge`: Lemma 4.1.4;
* `Optimization.exists_isARpStep`, `Optimization.exists_isARpRun`,
  `Optimization.exists_isARpRun_prev`: existence of steps and runs.

## Existence for third-order steps

For `q = 3` an admissible step need not exist when the test fails. Take `n = 1`, `p = 3`,
`f(x) = a x²/2 + b x³/6 + x⁴` with `0 < a ≤ ε₂` and `|b| > ε₃`, `x₀ = 0` and `σ₀ ≥ b²/(3a)`. The
test (4.1.5)–(4.1.9) fails at `x₀` (`𝓜₀ = {±1}`, `|∇³f(0)| = |b| > ε₃`), but
`m₀(s) = s² (a/2 + b s/6 + σ₀ s²/24) ≥ 0 = m₀(0)`, so (4.1.10) has no solution. Existence is
therefore proved unconditionally for `q ≤ 2` (`Optimization.exists_isARpRun`), and for general `q`
under the explicit hypothesis that an admissible step exists whenever the test fails
(`Optimization.exists_isARpRun_prev`).
-/

open Set
open scoped Nat

namespace Optimization

/-- The constants of the ARp method ([cartis2022evaluation], Algorithm 4.1.1, Step 0): those of
an AR method and the step-termination constants `θ₁, θ₂, θ₃ ∈ (0, 1]`. The book requires
`σ_min > 0`; it is not a field here (the inherited `σ_min ≥ 0` suffices for every result), and
with `σ_min = 0` the decrease bounds of `Optimization.IsARpRun.decrease_ge` are trivial. -/
structure ARpParams extends ARParams where
  /-- The first-order step-termination constant of (4.1.11). -/
  θ₁ : ℝ
  /-- The second-order step-termination constant of (4.1.12), (4.1.14). -/
  θ₂ : ℝ
  /-- The third-order step-termination constant of (4.1.13). -/
  θ₃ : ℝ
  /-- `θ₁ > 0`. -/
  θ₁_pos : 0 < θ₁
  /-- `θ₁ ≤ 1`. -/
  θ₁_le_one : θ₁ ≤ 1
  /-- `θ₂ > 0`. -/
  θ₂_pos : 0 < θ₂
  /-- `θ₂ ≤ 1`. -/
  θ₂_le_one : θ₂ ≤ 1
  /-- `θ₃ > 0`. -/
  θ₃_pos : 0 < θ₃
  /-- `θ₃ ≤ 1`. -/
  θ₃_le_one : θ₃ ≤ 1

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit directions along which a bilinear form has curvature at most `c` in absolute value:
`{d | ‖d‖ = 1 ∧ |A[d, d]| ≤ c}`. With `A = ∇²m_k(s_k)` and `c = θ₂ ‖s_k‖^{p-1}` this is the set
`𝓜_{k+1}` of (4.1.14) of [cartis2022evaluation]; with `A = ∇²f(x_ε)`, `c = ε₂` it is `𝒵_ε` of
(4.1.4). -/
def smallCurvatureDirections (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (c : ℝ) :
    Set E :=
  {d | ‖d‖ = 1 ∧ |A (fun _ => d)| ≤ c}

@[simp]
theorem mem_smallCurvatureDirections {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    {c : ℝ} {d : E} :
    d ∈ smallCurvatureDirections A c ↔ ‖d‖ = 1 ∧ |A (fun _ => d)| ≤ c :=
  Iff.rfl

/-- The step conditions of one ARp iteration ([cartis2022evaluation], Algorithm 4.1.1, Step 2) at
the point `x` with weight `σ`, for the model `m = regularizedModel (ftaylorSeries ℝ f x) p σ`:
the model decrease (4.1.10), the first-order condition (4.1.11), and, depending on the order `q`
sought, the second-order condition (4.1.12) and the third-order condition (4.1.13) on the set
`𝓜_{k+1}` of (4.1.14) (vacuous when that set is empty). -/
structure IsARpStep (f : E → ℝ) (p : ℕ) (P : ARpParams) (q : ℕ) (x : E) (σ : ℝ) (s : E) :
    Prop where
  /-- (4.1.10): the step decreases the model. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- (4.1.11): the model gradient is small. -/
  gradient : ‖fderiv ℝ (regularizedModel (ftaylorSeries ℝ f x) p σ) s‖ ≤ P.θ₁ * ‖s‖ ^ p
  /-- (4.1.12): the model curvature is not too negative. -/
  curvature : 2 ≤ q →
    -(P.θ₂ * ‖s‖ ^ (p - 1)) ≤
      minCurvature (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
  /-- (4.1.13): the third model derivative is small along directions of small model curvature. -/
  third : 3 ≤ q → ∀ d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (P.θ₂ * ‖s‖ ^ (p - 1)),
    |iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      P.θ₃ * ‖s‖ ^ (p - 2)

/-- A run of the ARp method ([cartis2022evaluation], Algorithm 4.1.1, Steps 2–4; Algorithm 5.1.1)
with an arbitrary Step-1 termination test `test k` (which may refer to the run): the generic AR
run with the step conditions `IsARpStep`, no post-step test and the Taylor ratio (4.1.15).
Iteration `k` is successful iff `P.η₁ ≤ taylorRatio f p x s k`. -/
def IsARpRun (f : E → ℝ) (p : ℕ) (P : ARpParams) (q : ℕ) (test : ℕ → Prop) (x s : ℕ → E)
    (σ : ℕ → ℝ) : Prop :=
  IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

theorem isARpRun_iff {f : E → ℝ} {p : ℕ} {P : ARpParams} {q : ℕ} {test : ℕ → Prop}
    {x s : ℕ → E} {σ : ℕ → ℝ} :
    IsARpRun f p P q test x s σ ↔
      IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
        (taylorRatio f p x s) x s σ :=
  Iff.rfl

end Defs

namespace IsARpRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}
  {P : ARpParams} {test : ℕ → Prop} {x s : ℕ → E} {σ : ℕ → ℝ}

/-- An ARp run is a generic AR run. -/
theorem toIsARRun (h : IsARpRun f p P q test x s σ) :
    IsARRun P.toARParams test (fun k => IsARpStep f p P q (x k) (σ k) (s k)) (fun _ => False)
      (taylorRatio f p x s) x s σ :=
  h

private theorem not_stop_iff {K : ℕ} :
    (∀ j < K, ¬ (test j ∨ False)) ↔ ∀ j < K, ¬ test j := by simp

private theorem not_stop_le_iff {K : ℕ} :
    (∀ j ≤ K, ¬ (test j ∨ False)) ↔ ∀ j ≤ K, ¬ test j := by simp

/-- The step conditions hold at every iteration before termination. -/
theorem step_spec (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) :
    IsARpStep f p P q (x k) (σ k) (s k) :=
  h.toIsARRun.step_of_forall_le (not_stop_le_iff.2 hk)

/-- **Lemma 4.1.2** ([cartis2022evaluation]): under f.DpL (`f` `C^p` with `L`-Lipschitz `∇^p f`),
up to (and including) the first termination index, `σ_min ≤ σ_k ≤ σ_max = max(σ₀, γ₃ L/(1 - η₂))`
(4.1.19). -/
theorem sigma_le (h : IsARpRun f p P q test x s σ) {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    P.σmin ≤ σ k ∧ σ k ≤ arSigmaMax P.toARParams L := by
  have := h.toIsARRun.sigma_le convex_univ (fun y _ => hf.contDiffAt) hL (mem_univ _)
    (fun k _ hstep => ⟨mem_univ _, hstep.decrease⟩) k (not_stop_iff.2 hk)
  exact this.2

/-- The weights are positive before termination. -/
theorem sigma_pos (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    0 < σ k :=
  h.toIsARRun.sigma_pos (not_stop_iff.2 hk) k le_rfl

/-- An unsuccessful iteration before termination keeps the iterate. -/
theorem eq_of_not_succ (h : IsARpRun f p P q test x s σ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j)
    (hs : ¬ P.η₁ ≤ taylorRatio f p x s k) : x (k + 1) = x k :=
  h.toIsARRun.eq_of_not_succ (not_stop_le_iff.2 hk) (not_le.1 hs)

/-- **Density of the successful iterations** ([cartis2022evaluation], Lemma 2.4.1 with
`σ_k ≤ σ_max` from Lemma 4.1.2; the form (5.3.9)): if the run has not terminated before `k`, then
`k ≤ (1 + |log γ₁|/log γ₂) |𝒮_k| + log(σ_max/σ₀)/log γ₂`. -/
theorem density (h : IsARpRun f p P q test x s σ) {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j < k, ¬ test j) :
    (k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (successSet (fun j => P.η₁ ≤ taylorRatio f p x s j) k).card +
      Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂ := by
  have := h.toIsARRun.le_succ_count (k := k) (not_stop_iff.2 hk) (h.sigma_le hf hL hk).2
  linarith

variable {L : ℝ}

/-- **Lemma 4.1.3, (4.1.20)** at the trial point ([cartis2022evaluation]): before termination,
`‖∇f(x_k + s_k)‖ ≤ (L + σ_max + θ₁ p!)/p! ‖s_k‖^p`. -/
theorem norm_fderiv_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) :
    ‖fderiv ℝ f (x k + s k)‖ ≤
      (L + arSigmaMax P.toARParams L + P.θ₁ * p !) / (p ! : ℝ) * ‖s k‖ ^ p := by
  have hst := h.step_spec hk
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := norm_fderiv_le_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt) hp hL
    (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le
  have hfac : (0 : ℝ) < p ! := by positivity
  calc ‖fderiv ℝ f (x k + s k)‖ ≤ (L + σ k) / (p ! : ℝ) * ‖s k‖ ^ p + P.θ₁ * ‖s k‖ ^ p :=
        h1.trans (by gcongr; exact hst.gradient)
    _ ≤ (L + arSigmaMax P.toARParams L) / (p ! : ℝ) * ‖s k‖ ^ p + P.θ₁ * ‖s k‖ ^ p := by
        gcongr; exact hσ.2
    _ = _ := by field_simp

/-- **Lemma 4.1.3, (4.1.21)** at the trial point ([cartis2022evaluation]): for `q ≥ 2`, `p ≥ 2`,
before termination, `-λ_min[∇²f(x_k + s_k)] ≤ (L + σ_max + θ₂ (p-1)!)/(p-1)! ‖s_k‖^{p-1}`. -/
theorem neg_minCurvature_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 2 ≤ p) (hq : 2 ≤ q) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) :
    -minCurvature (iteratedFDeriv ℝ 2 f (x k + s k)) ≤
      (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
  have hst := h.step_spec hk
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := minCurvature_ge_of_regularizedModel convex_univ (fun y _ => hf.contDiffAt) hp hL
    (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le
  have h2 := hst.curvature hq
  have hfac : (0 : ℝ) < (p - 1)! := by positivity
  have h3 : (L + σ k) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) ≤
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
    gcongr; exact hσ.2
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) =
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) +
        P.θ₂ * ‖s k‖ ^ (p - 1) := by
    field_simp
  linarith

/-- **Lemma 4.1.3, (4.1.30)** at the trial point ([cartis2022evaluation]): for `j ≤ p` and every
unit `d`, `|∇^j f(x_k + s_k)[d]^j| ≤ (L + σ_max)/(p-j+1)! ‖s_k‖^{p-j+1} + |∇^j m_k(s_k)[d]^j|`. -/
theorem abs_iteratedFDeriv_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) {j : ℕ}
    (hj : j ≤ p) {d : E} (hd : ‖d‖ = 1) :
    |iteratedFDeriv ℝ j f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) +
        |iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| := by
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  have hσ0 := h.sigma_pos (k := k) fun j hj => hk j hj.le
  have h1 := abs_iteratedFDeriv_apply_le_of_regularizedModel convex_univ
    (fun y _ => hf.contDiffAt) hL (mem_univ (x k)) (mem_univ (x k + s k)) hσ0.le hj d
  rw [hd, one_pow, mul_one] at h1
  have h2 : (L + σ k) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) ≤
      (L + arSigmaMax P.toARParams L) / ((p - j + 1)! : ℝ) * ‖s k‖ ^ (p - j + 1) := by
    gcongr; exact hσ.2
  have h3 := abs_sub_abs_le_abs_sub (iteratedFDeriv ℝ j f (x k + s k) (fun _ => d))
    (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k) (fun _ => d))
  linarith

/-- **Lemma 4.1.3, (4.1.23)** at the trial point ([cartis2022evaluation]): for `p ≥ 2`, before
termination, every `d ∈ 𝓜_{k+1}` satisfies
`|∇²f(x_k + s_k)[d]²| ≤ (L + σ_max + θ₂ (p-1)!)/(p-1)! ‖s_k‖^{p-1}` (`= ‖s_k‖^{p-1} / κ_{s2}`). -/
theorem abs_second_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 2 ≤ p) {k : ℕ} (hk : ∀ j ≤ k, ¬ test j)
    {d : E} (hd : d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))) :
    |iteratedFDeriv ℝ 2 f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) := by
  have h1 := h.abs_iteratedFDeriv_le hf hL hk hp hd.1
  have hpe : p - 2 + 1 = p - 1 := by omega
  rw [hpe] at h1
  have hfac : (0 : ℝ) < (p - 1)! := by positivity
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) =
      (L + arSigmaMax P.toARParams L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) +
        P.θ₂ * ‖s k‖ ^ (p - 1) := by
    field_simp
  linarith [hd.2]

/-- **Lemma 4.1.3, (4.1.22)** at the trial point ([cartis2022evaluation]): for `q ≥ 3`, `p ≥ 3`,
before termination, every `d ∈ 𝓜_{k+1}` satisfies
`|∇³f(x_k + s_k)[d]³| ≤ (L + σ_max + θ₃ (p-2)!)/(p-2)! ‖s_k‖^{p-2}`. -/
theorem abs_third_le (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hp : 3 ≤ p) (hq : 3 ≤ q) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j)
    {d : E} (hd : d ∈ smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))) :
    |iteratedFDeriv ℝ 3 f (x k + s k) (fun _ => d)| ≤
      (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) := by
  have h1 := h.abs_iteratedFDeriv_le hf hL hk hp hd.1
  have hpe : p - 3 + 1 = p - 2 := by omega
  rw [hpe] at h1
  have h2 := (h.step_spec hk).third hq d hd
  have hfac : (0 : ℝ) < (p - 2)! := by positivity
  have h4 : (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) =
      (L + arSigmaMax P.toARParams L) / ((p - 2)! : ℝ) * ‖s k‖ ^ (p - 2) +
        P.θ₃ * ‖s k‖ ^ (p - 2) := by
    field_simp
  linarith

omit [InnerProductSpace ℝ E] in
private theorem constant_pos (hL0 : 0 ≤ L) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 < L + arSigmaMax P.toARParams L + θ * m ! := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem div_mul_le_of_le_div_mul {K m a t : ℝ} (hK : 0 < K) (hm : 0 < m)
    (h : a ≤ K / m * t) : m / K * a ≤ t := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  rw [div_mul_eq_mul_div, le_div_iff₀ hm] at h
  linarith

/-- **Lemma 4.1.3** ([cartis2022evaluation]) on a successful iteration `k` before termination,
with `σ_max = max(σ₀, γ₃ L/(1-η₂))` and `L ≥ 0`, `1 ≤ p`, `q ≤ p`:
(4.1.20) `‖s_k‖^p ≥ p!/(L + σ_max + θ₁ p!) ‖∇f(x_{k+1})‖`;
(4.1.21) if `q ≥ 2`, `‖s_k‖^{p-1} ≥ (p-1)!/(L + σ_max + θ₂ (p-1)!) max(0, -λ_min[∇²f(x_{k+1})])`;
(4.1.22) if `q ≥ 3`, `‖s_k‖^{p-2} ≥ (p-2)!/(L + σ_max + θ₃ (p-2)!) |∇³f(x_{k+1})[d]³|` for every
`d ∈ 𝓜_{k+1}`;
(4.1.23) if `q ≥ 2`, `|∇²f(x_{k+1})[d]²| ≤ (L + σ_max + θ₂ (p-1)!)/(p-1)! ‖s_k‖^{p-1}`
`= ‖s_k‖^{p-1}/κ_{s2}` for every `d ∈ 𝓜_{k+1}`. -/
theorem step_lower_bounds (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x (k + 1) = x k + s k ∧
    (p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !) * ‖fderiv ℝ f (x (k + 1))‖ ≤
      ‖s k‖ ^ p ∧
    (2 ≤ q → ((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) *
      max 0 (-minCurvature (iteratedFDeriv ℝ 2 f (x (k + 1)))) ≤ ‖s k‖ ^ (p - 1)) ∧
    (3 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      ((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 2)) ∧
    (2 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| ≤
        (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1)) := by
  have hx : x (k + 1) = x k + s k :=
    h.toIsARRun.eq_add_of_succ (not_stop_le_iff.2 hk) hs
  have hK := constant_pos (P := P) hL0
  rw [hx]
  refine ⟨rfl, ?_, fun hq => ?_, fun hq d hd => ?_, fun hq d hd => ?_⟩
  · exact div_mul_le_of_le_div_mul (hK _ P.θ₁_pos p) (by positivity)
      (h.norm_fderiv_le hf hL hp hk)
  · have h1 := h.neg_minCurvature_le hf hL (hq.trans hqp) hq hk
    refine div_mul_le_of_le_div_mul (hK _ P.θ₂_pos (p - 1)) (by positivity) ?_
    exact max_le (by have := hK _ P.θ₂_pos (p - 1); positivity) h1
  · exact div_mul_le_of_le_div_mul (hK _ P.θ₃_pos (p - 2)) (by positivity)
      (h.abs_third_le hf hL (hq.trans hqp) hq hk hd)
  · exact h.abs_second_le hf hL (hq.trans hqp) hk hd

/-- `a^{n/m} ≤ t^n` from `a ≤ t^m` (for `a, t ≥ 0`, `m > 0`). -/
private theorem rpow_div_le_pow_of_le_pow {a t : ℝ} {m n : ℕ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 0 < m)
    (h : a ≤ t ^ m) : a ^ ((n : ℝ) / m) ≤ t ^ n := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  calc a ^ ((n : ℝ) / m) ≤ (t ^ m) ^ ((n : ℝ) / m) := by gcongr
    _ = t ^ n := by
        rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht, mul_div_cancel₀ _ hm',
          Real.rpow_natCast]

/-- From a step bound `a v ≤ ‖s‖^m` and a decrease `≥ c ‖s‖^{p+1}` (`c ≥ 0`), the decrease is at
least `c a^{(p+1)/m} v^{(p+1)/m}`. -/
private theorem decrease_ge_of_step_bound {a v t c D : ℝ} {m n : ℕ} (ha : 0 ≤ a) (hv : 0 ≤ v)
    (ht : 0 ≤ t) (hm : 0 < m) (hc : 0 ≤ c) (hstep : a * v ≤ t ^ m) (hD : c * t ^ n ≤ D) :
    c * a ^ ((n : ℝ) / m) * v ^ ((n : ℝ) / m) ≤ D := by
  rw [mul_assoc, ← Real.mul_rpow ha hv]
  exact (mul_le_mul_of_nonneg_left (rpow_div_le_pow_of_le_pow (mul_nonneg ha hv) ht hm hstep)
    hc).trans hD

/-- **Lemma 4.1.4** ([cartis2022evaluation]) on a successful iteration `k` before termination
(`L ≥ 0`, `1 ≤ p`, `q ≤ p`): (4.1.37) `f(x_k) - f(x_{k+1}) ≥ η₁ σ_min/(p+1)! ‖s_k‖^{p+1}`, and
hence, with `κ_j = η₁ σ_min/(p+1)! ((p-j)!/(L + σ_max + θ_j (p-j)!))^{(p+1)/(p-j+1)}`
((4.1.32), (4.1.34), (4.1.36)):
(4.1.31) `f(x_k) - f(x_{k+1}) ≥ κ₁ ‖∇f(x_{k+1})‖^{(p+1)/p}`;
(4.1.33) if `q ≥ 2`, `f(x_k) - f(x_{k+1}) ≥ κ₂ max(0, -λ_min[∇²f(x_{k+1})])^{(p+1)/(p-1)}`;
(4.1.35) if `q ≥ 3`, `f(x_k) - f(x_{k+1}) ≥ κ₃ |∇³f(x_{k+1})[d]³|^{(p+1)/(p-2)}` for every
`d ∈ 𝓜_{k+1}`. -/
theorem decrease_ge (h : IsARpRun f p P q test x s σ) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ test j) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) ∧
    P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p) *
        ‖fderiv ℝ f (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤ f (x k) - f (x (k + 1)) ∧
    (2 ≤ q → P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        (max 0 (-minCurvature (iteratedFDeriv ℝ 2 f (x (k + 1))))) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ f (x k) - f (x (k + 1))) ∧
    (3 ≤ q → ∀ d ∈ smallCurvatureDirections
        (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
        (P.θ₂ * ‖s k‖ ^ (p - 1)),
      P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤
          f (x k) - f (x (k + 1))) := by
  have hσ := h.sigma_le hf hL (k := k) fun j hj => hk j hj.le
  obtain ⟨-, hdec⟩ := h.toIsARRun.sub_ge_of_succ_taylor (not_stop_le_iff.2 hk)
    (h.step_spec hk).decrease hs
  have h37 : P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) := by
    refine le_trans ?_ hdec
    have := P.η₁_pos
    rw [show P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) =
      P.η₁ * (P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) by ring]
    gcongr
    exact hσ.1
  obtain ⟨-, b1, b2, b3, -⟩ := h.step_lower_bounds hf hL hL0 hp hqp hk hs
  have hc : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_nonneg; positivity
  have hK := constant_pos (P := P) hL0
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨h37, ?_, fun hq => ?_, fun hq d hd => ?_⟩
  · rw [hn]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₁_pos p; positivity) (norm_nonneg _)
      (norm_nonneg _) (by omega) hc b1 h37
  · have hm : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hp)]; push_cast; ring
    rw [hn, hm]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₂_pos (p - 1); positivity) (le_max_left _ _)
      (norm_nonneg _) (by omega) hc (b2 hq) h37
  · have hm : ((p : ℝ) - 2) = ((p - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hn, hm]
    exact decrease_ge_of_step_bound (by have := hK _ P.θ₃_pos (p - 2); positivity) (abs_nonneg _)
      (norm_nonneg _) (by omega) hc (b3 hq d hd) h37

end IsARpRun

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}

/-- **Existence of ARp steps for `q ≤ 2`** ([cartis2022evaluation], Section 4.1.1): in finite
dimension, for `f` `C^p` at `x` (`p ≥ 1`, and `p ≥ 2` if `q = 2`) and `σ > 0`, if `x` is not
first-order critical, or `q = 2` and `∇²f(x)` has a negative eigenvalue, then any global
minimizer of the model is an admissible step (the model's gradient and Hessian at `0` are those
of `f` at `x`, so `0` is not a global minimizer of the model). -/
theorem exists_isARpStep [FiniteDimensional ℝ E] (P : ARpParams) {x : E} {σ : ℝ}
    (hf : ContDiffAt ℝ p f x) (hp : 1 ≤ p) (hq : q ≤ 2) (hqp : 2 ≤ q → 2 ≤ p) (hσ : 0 < σ)
    (hcrit : fderiv ℝ f x ≠ 0 ∨ (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 f x) < 0)) :
    ∃ s, IsARpStep f p P q x σ s := by
  obtain ⟨s, hmin, hd, hc, -⟩ :=
    exists_isMinOn_regularizedModel (D := ftaylorSeries ℝ f x) (σ := σ) hσ hp
  refine ⟨s, ⟨?_, ?_, fun _ => ?_, fun h3 => absurd h3 (by omega)⟩⟩
  · rcases hcrit with h1 | ⟨h2, h2'⟩
    · exact regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero hmin
        (by rwa [fderiv_regularizedModel_ftaylorSeries_zero hf hp])
    · exact regularizedModel_lt_of_isMinOn_of_minCurvature_neg (hqp h2) hmin
        (by rwa [iteratedFDeriv_two_regularizedModel_ftaylorSeries_zero hf (hqp h2)])
  · rw [hd, norm_zero]
    exact mul_nonneg P.θ₁_pos.le (by positivity)
  · exact (neg_nonpos.2 (mul_nonneg P.θ₂_pos.le (by positivity))).trans hc

/-- **Existence of ARp runs for `q ≤ 2`** ([cartis2022evaluation], Algorithm 4.1.1): in finite
dimension, for `f` `C^p` (`p ≥ 1`, and `p ≥ 2` if `q = 2`) and a state-based termination test
whose failure at `y` implies `∇f(y) ≠ 0` or (`q = 2` and `λ_min[∇²f(y)] < 0`) — such as the tests
(4.1.5)–(4.1.7) with `ε₁ > 0` — there is a run from every `x₀`. -/
theorem exists_isARpRun [FiniteDimensional ℝ E] (P : ARpParams) (hf : ContDiff ℝ p f)
    (hp : 1 ≤ p) (hq : q ≤ 2) (hqp : 2 ≤ q → 2 ≤ p) {test : E → Prop}
    (htest : ∀ y, ¬ test y →
      fderiv ℝ f y ≠ 0 ∨ (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 f y) < 0))
    (x₀ : E) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ IsARpRun f p P q (fun k => test (x k)) x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := fun _ => True)
    (test := test) (stepOK := fun y σ s => IsARpStep f p P q y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ _ _ hσ ht => by
      obtain ⟨s, hs⟩ := exists_isARpStep P hf.contDiffAt hp hq hqp hσ (htest y ht)
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hrun⟩

/-- **Existence of ARp runs for any `q`, under an explicit hypothesis** ([cartis2022evaluation],
Algorithm 4.1.1): if the termination test may read the previous iteration (as the third-order
test does through `𝓜_k`, built from the previous model by (4.1.14)) and an admissible step exists
at every state at which the test fails, there is a run from every `x₀`. For `q = 3` the
hypothesis can fail (see the module documentation). -/
theorem exists_isARpRun_prev (P : ARpParams) {test : Option (E × ℝ × E) → E → ℝ → Prop}
    (hstep : ∀ prev y σ, P.σmin ≤ σ → 0 < σ → ¬ test prev y σ → ∃ s, IsARpStep f p P q y σ s)
    (x₀ : E) :
    ∃ x s : ℕ → E, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧
      IsARpRun f p P q (fun k => test (prevIterate x s σ k) (x k) (σ k)) x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun_prev P.toARParams (Inv := fun _ => True)
    (test := test) (stepOK := fun y σ s => IsARpStep f p P q y σ s)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun prev y σ _ hσ hσ0 ht => by
      obtain ⟨s, hs⟩ := hstep prev y σ hσ hσ0 ht
      exact ⟨s, hs, trivial⟩) trivial
  exact ⟨x, s, σ, hx0, hrun⟩

end Existence

end Optimization
