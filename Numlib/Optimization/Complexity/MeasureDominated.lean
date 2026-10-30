import Numlib.Optimization.Complexity.GapRecurrence
import Numlib.Optimization.ModelBased.ARpRun

/-!
# Measure-dominated objectives and AR-like / TR-like methods

An objective `f` is *`ψ`-dominated of level `μ`* for a nonnegative optimality measure `ψ`
([cartis2022evaluation], (5.3.1)) if `f x - f_* ≤ κψ ψ(x)^μ`; for `ψ = ‖∇f‖` and `μ ∈ [1, 2]` this
is the Polyak–Łojasiewicz (gradient domination) property. Section 5.3 of the book analyses two
abstract classes of monotone methods with success set `S`:

* the class `ARψ,ν` (`Optimization.IsARLikeRun`): successful iterations decrease `f` by
  `κν ψ(x_{k+1})^ν` (5.3.5), unsuccessful ones keep the iterate, and successes are dense,
  `k ≤ κR |𝒮_k| + κA` (5.3.9);
* the class `TRψ,ν` (`Optimization.IsTRLikeRun`): the same with the decrease
  `κν (min_{i ≤ k} ψ(x_i))^ν` (5.3.28).

Runs are infinite sequences and domination is only required at the iterates (as the book remarks
after Lemma 5.3.1). The gap `Γ_k = f(x_k) - f_*` then satisfies the scalar recurrences of
`Optimization.IsImplicitGapDecrease` / `Optimization.IsExplicitGapDecrease` with
`c = κν / κψ^{ν/μ}` and `τ = ν/μ`, from which all rates and counts of §5.3 follow.

## Main statements

* `Optimization.isImplicitGapDecrease_of_isARLikeRun`: (5.3.11) (proof of Lemma 5.3.1);
* `Optimization.isExplicitGapDecrease_of_isTRLikeRun`: (5.3.33) (proof of Lemma 5.3.6);
* `Optimization.isARLikeRun_of_isARpRun`, `Optimization.isARLikeRun_of_isARpRun_curvature`: an
  ARp run (Algorithm 4.1.1) without termination test belongs to `ARψ,ν` for the first-order
  measure (5.3.6) and, if `q ≥ 2`, for the second-order measure (5.3.7);
* `Optimization.exists_isARpRun_softplus`: a complete non-vacuity example (ARp run, AR-like,
  dominated, gap recurrence) for `f(y) = log(1 + e^y)`;
* `Optimization.isTRLikeRun_halving`: a member of `TRψ,ν` for `f(y) = y²`.

## Remarks

* **Non-vacuity of the AR bridge.** The classes describe infinite runs, so the ARp run in the
  bridge has no termination test, and a run without termination exists only if an admissible step
  exists at every iterate: for `q = 1` this requires `∇f(x_k) ≠ 0` along the run
  (`Optimization.exists_isARpRun`); an iterate at an exact critical point stops the method. Hence
  the example uses a function without critical points: `softplus` (`f' > 0`, `f_* = 0` not
  attained, `f''` bounded, dominated of level `1` on its sublevel sets).
* The third-order measure (5.3.8) depends on the run through the set `𝓜_{k+1}`, so it is not a
  function of the point and is not covered.
* No bridge is given from TR1/TR2 runs: the density constant of Lemma 2.3.1 involves `log Δ_min`
  with `Δ_min` proportional to a lower bound on the gradient along the run, so it is not uniform
  unless the gradient stays bounded away from zero (in which case `f` cannot be dominated with
  `f_* = inf f` and the gap analysis is moot). `Optimization.isTRLikeRun_halving` documents a
  member of the class: the gradient method with step `1/4` on `y²`.
-/

open Finset
open scoped Nat

namespace Optimization

section Defs

variable {E : Type*}

/-- `f` is **`ψ`-dominated of level `μ`** on `A` with constant `κψ` and value `fstar`
([cartis2022evaluation], (5.3.1)): `fstar ≤ f x` and `f x - fstar ≤ κψ ψ(x)^μ` for `x ∈ A`.
The book's global notion is `A = univ` with `fstar = ⨅ x, f x`; the theorems below only use the
iterates, `A ⊇ range x`. -/
def IsMeasureDominated (f ψ : E → ℝ) (fstar μ κψ : ℝ) (A : Set E) : Prop :=
  ∀ x ∈ A, fstar ≤ f x ∧ f x - fstar ≤ κψ * ψ x ^ μ

/-- A run `x` with success predicate `S` is in the class **`ARψ,ν`** ([cartis2022evaluation],
§5.3.2): successful iterations decrease `f` by `κν ψ(x_{k+1})^ν` (5.3.5), unsuccessful iterations
keep the iterate, and the successes are dense, `k ≤ κR |𝒮_k| + κA` (5.3.9). (The standing
assumptions `κν > 0`, `ν ≥ 1`, `κR ≥ 1`, `κA ≥ 0`, `ψ ≥ 0` of §5.3 are hypotheses of the theorems
that need them; density forces `S` to be infinite.) -/
structure IsARLikeRun (f ψ : E → ℝ) (κν ν κR κA : ℝ) (x : ℕ → E) (S : ℕ → Prop) : Prop where
  /-- (5.3.5): the decrease on successful iterations. -/
  decrease : ∀ k, S k → κν * ψ (x (k + 1)) ^ ν ≤ f (x k) - f (x (k + 1))
  /-- Unsuccessful iterations keep the iterate. -/
  eq_of_not : ∀ k, ¬ S k → x (k + 1) = x k
  /-- (5.3.9): the successful iterations are dense. -/
  density : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA

/-- A run `x` with success predicate `S` is in the class **`TRψ,ν`** ([cartis2022evaluation],
§5.3.3): successful iterations decrease `f` by `κν (min_{i ≤ k} ψ(x_i))^ν` (5.3.28), unsuccessful
iterations keep the iterate, and the successes are dense (5.3.9). (No stop is needed when
`ψ(x_k) = 0`: the decrease condition then only asks for a nonnegative decrease.) -/
structure IsTRLikeRun (f ψ : E → ℝ) (κν ν κR κA : ℝ) (x : ℕ → E) (S : ℕ → Prop) : Prop where
  /-- (5.3.28): the decrease on successful iterations. -/
  decrease : ∀ k, S k → κν * ((range (k + 1)).inf' nonempty_range_add_one (ψ ∘ x)) ^ ν ≤
    f (x k) - f (x (k + 1))
  /-- Unsuccessful iterations keep the iterate. -/
  eq_of_not : ∀ k, ¬ S k → x (k + 1) = x k
  /-- (5.3.9): the successful iterations are dense. -/
  density : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA

variable {f ψ : E → ℝ} {fstar μ κψ : ℝ} {A A' : Set E}

/-- The reference value is a lower bound on `A`. -/
theorem IsMeasureDominated.le (h : IsMeasureDominated f ψ fstar μ κψ A) {x : E} (hx : x ∈ A) :
    fstar ≤ f x :=
  (h x hx).1

/-- The domination inequality (5.3.1) at a point of `A`. -/
theorem IsMeasureDominated.sub_le (h : IsMeasureDominated f ψ fstar μ κψ A) {x : E}
    (hx : x ∈ A) : f x - fstar ≤ κψ * ψ x ^ μ :=
  (h x hx).2

/-- Domination on `A` implies domination on any subset. -/
theorem IsMeasureDominated.mono (h : IsMeasureDominated f ψ fstar μ κψ A) (hA : A' ⊆ A) :
    IsMeasureDominated f ψ fstar μ κψ A' :=
  fun x hx => h x (hA hx)

/-- Global domination, the book's (5.3.1). -/
theorem isMeasureDominated_univ_iff :
    IsMeasureDominated f ψ fstar μ κψ Set.univ ↔
      ∀ x, fstar ≤ f x ∧ f x - fstar ≤ κψ * ψ x ^ μ := by
  simp [IsMeasureDominated]

/-- Global domination gives domination along any run. -/
theorem IsMeasureDominated.range (h : IsMeasureDominated f ψ fstar μ κψ Set.univ) (x : ℕ → E) :
    IsMeasureDominated f ψ fstar μ κψ (Set.range x) :=
  h.mono (Set.subset_univ _)

end Defs

section Gap

variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → E} {S : ℕ → Prop}

/-- Domination turns a power of the measure into a power of the gap:
`(f x - fstar)^{ν/μ} / κψ^{ν/μ} ≤ ψ(x)^ν`. -/
theorem div_rpow_le_rpow_of_isMeasureDominated {A : Set E}
    (hdom : IsMeasureDominated f ψ fstar μ κψ A) {y : E} (hy : y ∈ A) (hψ : 0 ≤ ψ y)
    (hκψ : 0 < κψ) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    (f y - fstar) ^ (ν / μ) / κψ ^ (ν / μ) ≤ ψ y ^ ν := by
  have hg : 0 ≤ f y - fstar := sub_nonneg.2 (hdom.le hy)
  rw [← Real.div_rpow hg hκψ.le]
  have hle : (f y - fstar) / κψ ≤ ψ y ^ μ := by
    rw [div_le_iff₀ hκψ]; linarith [hdom.sub_le hy]
  calc ((f y - fstar) / κψ) ^ (ν / μ) ≤ (ψ y ^ μ) ^ (ν / μ) :=
        Real.rpow_le_rpow (div_nonneg hg hκψ.le) hle (div_nonneg hν hμ.le)
    _ = ψ y ^ ν := by
        rw [← Real.rpow_mul hψ, mul_div_cancel₀ _ hμ.ne']

/-- The objective is nonincreasing along an `ARψ,ν` run with `κν ≥ 0` and `ψ ≥ 0`. -/
theorem IsARLikeRun.objective_succ_le (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ κν * ψ (x (k + 1)) ^ ν := mul_nonneg hκν (Real.rpow_nonneg (hψ _) _)
    linarith
  · rw [h.eq_of_not k hk]

/-- The objective values along an `ARψ,ν` run are antitone (`κν ≥ 0`, `ψ ≥ 0`). -/
theorem IsARLikeRun.objective_antitone (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) : Antitone fun k => f (x k) :=
  antitone_nat_of_succ_le (h.objective_succ_le hψ hκν)

/-- **(5.3.11)** ([cartis2022evaluation], proof of Lemma 5.3.1): for an `ARψ,ν` run of a
`ψ`-dominated objective (domination at the iterates), the gap `Γ_k = f(x_k) - f_*` satisfies the
implicit recurrence `κν/κψ^{ν/μ} Γ_{k+1}^{ν/μ} ≤ Γ_k - Γ_{k+1}` on successful iterations. (Only
`μ > 0` is used.) -/
theorem isImplicitGapDecrease_of_isARLikeRun (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκψ : 0 < κψ) (hμ : 0 < μ) (hκν : 0 ≤ κν) (hν : 0 ≤ ν)
    (hdom : IsMeasureDominated f ψ fstar μ κψ (Set.range x)) :
    IsImplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) where
  nonneg k := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
  eq_of_not k hk := by simp only [h.eq_of_not k hk]
  decrease k hk := by
    have h1 := div_rpow_le_rpow_of_isMeasureDominated hdom ⟨k + 1, rfl⟩ (hψ _) hκψ hμ hν
    have h2 := h.decrease k hk
    calc κν / κψ ^ (ν / μ) * (f (x (k + 1)) - fstar) ^ (ν / μ)
        = κν * ((f (x (k + 1)) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by ring
      _ ≤ κν * ψ (x (k + 1)) ^ ν := mul_le_mul_of_nonneg_left h1 hκν
      _ ≤ _ := by linarith

/-- The objective is nonincreasing along a `TRψ,ν` run with `κν ≥ 0` and `ψ ≥ 0`. -/
theorem IsTRLikeRun.objective_succ_le (h : IsTRLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ κν * ((range (k + 1)).inf' nonempty_range_add_one (ψ ∘ x)) ^ ν :=
      mul_nonneg hκν (Real.rpow_nonneg ((le_inf'_iff _ _).2 fun i _ => hψ _) _)
    linarith
  · rw [h.eq_of_not k hk]

/-- **(5.3.33)** ([cartis2022evaluation], proof of Lemma 5.3.6): for a `TRψ,ν` run of a
`ψ`-dominated objective (domination at the iterates), the gap `Γ_k = f(x_k) - f_*` satisfies the
explicit recurrence `κν/κψ^{ν/μ} Γ_k^{ν/μ} ≤ Γ_k - Γ_{k+1}` on successful iterations (domination
is applied at the minimizing earlier iterate, then monotonicity of `Γ`). (Only `μ > 0` is
used.) -/
theorem isExplicitGapDecrease_of_isTRLikeRun (h : IsTRLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκψ : 0 < κψ) (hμ : 0 < μ) (hκν : 0 ≤ κν) (hν : 0 ≤ ν)
    (hdom : IsMeasureDominated f ψ fstar μ κψ (Set.range x)) :
    IsExplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) where
  nonneg k := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
  eq_of_not k hk := by simp only [h.eq_of_not k hk]
  decrease k hk := by
    obtain ⟨i, hi, hieq⟩ := exists_mem_eq_inf' (nonempty_range_add_one (n := k)) (ψ ∘ x)
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hanti : Antitone (fun k => f (x k)) :=
      antitone_nat_of_succ_le (h.objective_succ_le hψ hκν)
    have h1 := div_rpow_le_rpow_of_isMeasureDominated hdom ⟨i, rfl⟩ (hψ _) hκψ hμ hν
    have h2 := h.decrease k hk
    rw [hieq] at h2
    have hgk : 0 ≤ f (x k) - fstar := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
    have h3 : (f (x k) - fstar) ^ (ν / μ) ≤ (f (x i) - fstar) ^ (ν / μ) :=
      Real.rpow_le_rpow hgk (by linarith [hanti hik]) (div_nonneg hν hμ.le)
    calc κν / κψ ^ (ν / μ) * (f (x k) - fstar) ^ (ν / μ)
        = κν * ((f (x k) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by ring
      _ ≤ κν * ((f (x i) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by
          gcongr
      _ ≤ κν * ψ (x i) ^ ν := mul_le_mul_of_nonneg_left h1 hκν
      _ ≤ _ := by simpa using h2

end Gap

section ARp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}
  {P : ARpParams} {x s : ℕ → E} {σ : ℕ → ℝ} {L : ℝ}

/-- **ARp is in `ARψ,ν` for the first-order measure** ([cartis2022evaluation], (5.3.6), (5.3.9):
"these properties are obviously satisfied by the ARp algorithm"). An ARp run without termination
test, for `f` `C^p` with `L`-Lipschitz `∇^p f` (`L ≥ 0`, `1 ≤ p`, `q ≤ p`), is AR-like for
`ψ = ‖∇f‖`, `ν = (p+1)/p`, `κν = κ₁` of (4.1.32) (with `σ_max` of (4.1.19)),
`κR = 1 + |log γ₁|/log γ₂` and `κA = log(σ_max/σ₀)/log γ₂`, with success set
`{k | η₁ ≤ ρ_k}`. (Such runs exist only if no iterate is a critical point, see the module
documentation and `Optimization.exists_isARpRun_softplus`.) -/
theorem isARLikeRun_of_isARpRun (h : IsARpRun f p P q (fun _ => False) x s σ)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L Set.univ) (hL0 : 0 ≤ L)
    (hp : 1 ≤ p) (hqp : q ≤ p) :
    IsARLikeRun f (fun y => ‖fderiv ℝ f y‖)
      (P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p))
      (((p : ℝ) + 1) / p) (1 + |Real.log P.γ₁| / Real.log P.γ₂)
      (Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂) x
      (fun k => P.η₁ ≤ taylorRatio f p x s k) where
  decrease k hk := (h.decrease_ge hf hL hL0 hp hqp (by simp) hk).2.1
  eq_of_not k hk := h.eq_of_not_succ (by simp) hk
  density k := h.density hf hL (by simp)

/-- **ARp is in `ARψ,ν` for the second-order measure** ([cartis2022evaluation], (5.3.7)): under
the hypotheses of `Optimization.isARLikeRun_of_isARpRun` and `2 ≤ q`, an ARp run without
termination test is AR-like for `ψ₂ = max(0, -λ_min(∇²f))`, `ν = (p+1)/(p-1)` and `κν = κ₂` of
(4.1.34). -/
theorem isARLikeRun_of_isARpRun_curvature (h : IsARpRun f p P q (fun _ => False) x s σ)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L Set.univ) (hL0 : 0 ≤ L)
    (hp : 1 ≤ p) (hqp : q ≤ p) (hq : 2 ≤ q) :
    IsARLikeRun f (fun y => max 0 (-minCurvature (iteratedFDeriv ℝ 2 f y)))
      (P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)))
      (((p : ℝ) + 1) / ((p : ℝ) - 1)) (1 + |Real.log P.γ₁| / Real.log P.γ₂)
      (Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂) x
      (fun k => P.η₁ ≤ taylorRatio f p x s k) where
  decrease k hk := (h.decrease_ge hf hL hL0 hp hqp (by simp) hk).2.2.1 hq
  eq_of_not k hk := h.eq_of_not_succ (by simp) hk
  density k := h.density hf hL (by simp)

end ARp

/-! ### Examples -/

section Softplus

/-- The softplus function `y ↦ log(1 + e^y)`: positive derivative everywhere, infimum `0` not
attained, bounded second derivative. -/
noncomputable def softplus (y : ℝ) : ℝ := Real.log (1 + Real.exp y)

private theorem one_add_exp_pos (y : ℝ) : 0 < 1 + Real.exp y := by positivity

/-- `softplus' = e^y/(1 + e^y)`, the logistic sigmoid. -/
theorem hasDerivAt_softplus (y : ℝ) :
    HasDerivAt softplus (Real.exp y / (1 + Real.exp y)) y :=
  ((Real.hasDerivAt_exp y).const_add 1).log (one_add_exp_pos y).ne'

/-- Softplus is smooth. -/
theorem contDiff_softplus {n : WithTop ℕ∞} : ContDiff ℝ n softplus :=
  (contDiff_const.add Real.contDiff_exp).log fun y => (one_add_exp_pos y).ne'

private theorem hasDerivAt_sigmoid (y : ℝ) :
    HasDerivAt (fun y => Real.exp y / (1 + Real.exp y))
      ((Real.exp y * (1 + Real.exp y) - Real.exp y * Real.exp y) / (1 + Real.exp y) ^ 2) y :=
  (Real.hasDerivAt_exp y).div ((Real.hasDerivAt_exp y).const_add 1) (one_add_exp_pos y).ne'

/-- The derivative of softplus as a linear map. -/
theorem fderiv_softplus (y : ℝ) :
    fderiv ℝ softplus y =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp y / (1 + Real.exp y)) :=
  (hasDerivAt_softplus y).hasFDerivAt.fderiv

/-- `‖∇ softplus(y)‖ = e^y/(1 + e^y)`. -/
theorem norm_fderiv_softplus (y : ℝ) :
    ‖fderiv ℝ softplus y‖ = Real.exp y / (1 + Real.exp y) := by
  rw [fderiv_softplus, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul,
    Real.norm_eq_abs, abs_of_pos (by have := one_add_exp_pos y; positivity)]

/-- Softplus has no critical point. -/
theorem fderiv_softplus_ne_zero (y : ℝ) : fderiv ℝ softplus y ≠ 0 := by
  intro h
  have := norm_fderiv_softplus y
  rw [h, norm_zero] at this
  have : 0 < Real.exp y / (1 + Real.exp y) := by have := one_add_exp_pos y; positivity
  linarith

/-- The gradient of softplus is `1`-Lipschitz. -/
theorem iteratedFDerivLipschitzOn_softplus :
    IteratedFDerivLipschitzOn softplus 1 1 Set.univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro a _ b _
  rw [norm_iteratedFDeriv_one_sub, fderiv_softplus, fderiv_softplus]
  have hsub : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp a / (1 + Real.exp a)) -
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp b / (1 + Real.exp b)) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (Real.exp a / (1 + Real.exp a) - Real.exp b / (1 + Real.exp b)) := by
    ext; simp
  rw [hsub, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hasDerivAt_sigmoid z).hasDerivWithinAt) (fun z _ => ?_) convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  have he := Real.exp_pos z
  rw [Real.norm_eq_abs, abs_le]
  have hd : 0 < (1 + Real.exp z) ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

/-- Softplus is dominated of level `1` (`ψ = |f'|`, `f_* = 0`) on each sublevel set
`{f ≤ c}`, with constant `e^c`: `log(1 + e^y) ≤ e^y = f'(y) (1 + e^y) ≤ e^c f'(y)`. -/
theorem isMeasureDominated_softplus (c : ℝ) :
    IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1 (Real.exp c)
      {y | softplus y ≤ c} := by
  intro y hy
  have h1 := one_add_exp_pos y
  refine ⟨Real.log_nonneg (by linarith [Real.exp_pos y]), ?_⟩
  rw [sub_zero, Real.rpow_one]
  simp only [norm_fderiv_softplus]
  have hle : softplus y ≤ Real.exp y := by
    have := Real.log_le_sub_one_of_pos h1
    simp only [softplus]; linarith
  have hc : 1 + Real.exp y ≤ Real.exp c := (Real.log_le_iff_le_exp h1).1 hy
  calc softplus y ≤ Real.exp y := hle
    _ = Real.exp y / (1 + Real.exp y) * (1 + Real.exp y) := by field_simp
    _ ≤ Real.exp y / (1 + Real.exp y) * Real.exp c := by gcongr
    _ = _ := mul_comm _ _

/-- **Non-vacuity of the AR bridge** ([cartis2022evaluation], §5.3.2): for every choice of ARp
constants with `σ_min > 0` and every `x₀`, the first-order ARp method with `p = 1` on softplus has
an infinite run from `x₀` (softplus has no critical point); it is AR-like for `ψ = |f'|`,
`ν = 2` with positive `κν`, softplus is dominated of level `1` along it (`f_* = 0`), and the gap
`Γ_k = f(x_k)` satisfies the implicit recurrence (5.3.11) with `τ = 2`. -/
theorem exists_isARpRun_softplus (P : ARpParams) (hσmin : 0 < P.σmin) (x₀ : ℝ) :
    ∃ x s σ : ℕ → ℝ, x 0 = x₀ ∧ IsARpRun softplus 1 P 1 (fun _ => False) x s σ ∧
      ∃ κν κR κA : ℝ, 0 < κν ∧
        IsARLikeRun softplus (fun y => ‖fderiv ℝ softplus y‖) κν 2 κR κA x
          (fun k => P.η₁ ≤ taylorRatio softplus 1 x s k) ∧
        IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1
          (Real.exp (softplus x₀)) (Set.range x) ∧
        IsImplicitGapDecrease (fun k => softplus (x k) - 0)
          (fun k => P.η₁ ≤ taylorRatio softplus 1 x s k) (κν / Real.exp (softplus x₀) ^ 2) 2 := by
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (f := softplus) (p := 1) (q := 1) P
    contDiff_softplus le_rfl (by omega) (by omega) (test := fun _ => False)
    (fun y _ => Or.inl (fderiv_softplus_ne_zero y)) x₀
  have hb := isARLikeRun_of_isARpRun hrun contDiff_softplus iteratedFDerivLipschitzOn_softplus
    zero_le_one le_rfl le_rfl
  have h2 : (((1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hb
  set κν := P.η₁ * P.σmin / ((1 + 1)! : ℝ) *
    (((1 : ℕ)! : ℝ) / (1 + arSigmaMax P.toARParams 1 + P.θ₁ * ((1 : ℕ)! : ℝ))) ^ (2 : ℝ)
  have hκν : 0 < κν := by
    have := P.η₁_pos; have := arSigmaMax_pos P.toARParams 1; have := P.θ₁_pos
    positivity
  have hψ : ∀ y, 0 ≤ ‖fderiv ℝ softplus y‖ := fun _ => norm_nonneg _
  have hdom : IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1
      (Real.exp (softplus x₀)) (Set.range x) := by
    refine (isMeasureDominated_softplus (softplus x₀)).mono ?_
    rintro _ ⟨k, rfl⟩
    have := hb.objective_antitone hψ hκν.le (Nat.zero_le k)
    simp only [hx0] at this
    exact this
  have hgap := isImplicitGapDecrease_of_isARLikeRun hb hψ (Real.exp_pos _) one_pos hκν.le
    (by norm_num) hdom
  rw [div_one, Real.rpow_two] at hgap
  exact ⟨x, s, σ, hx0, hrun, κν, _, _, hκν, hb, hdom, hgap⟩

end Softplus

section Halving

/-- **A member of `TRψ,ν`** ([cartis2022evaluation], §5.3.3): the gradient method with step `1/4`
on `f(y) = y²` (all iterations successful), `x_k = x₀/2^k`, is TR-like for `ψ = |f'| = |2y|`,
`ν = 2`, `κν = 3/16`, `κR = 1`, `κA = 0`; `f` is dominated of level `μ = 2` with `κψ = 1/4`
(`Optimization.isMeasureDominated_sq`), so (5.3.33) holds with `c = 3/4`, `τ = 1`. -/
theorem isTRLikeRun_halving (x₀ : ℝ) :
    IsTRLikeRun (fun y : ℝ => y ^ 2) (fun y => |2 * y|) (3 / 16) 2 1 0
      (fun k => x₀ / 2 ^ k) (fun _ => True) where
  decrease k _ := by
    set m := (range (k + 1)).inf' nonempty_range_add_one ((fun y : ℝ => |2 * y|) ∘
      fun k => x₀ / 2 ^ k)
    have hm0 : 0 ≤ m := (le_inf'_iff _ _).2 fun _ _ => abs_nonneg _
    have hmk : m ≤ |2 * (x₀ / 2 ^ k)| :=
      inf'_le _ (mem_range.2 (Nat.lt_succ_self k))
    have h2 : m ^ (2 : ℝ) ≤ |2 * (x₀ / 2 ^ k)| ^ (2 : ℝ) :=
      Real.rpow_le_rpow hm0 hmk (by norm_num)
    rw [Real.rpow_two, Real.rpow_two, sq_abs] at h2
    have e : (x₀ / 2 ^ k) ^ 2 - (x₀ / 2 ^ (k + 1)) ^ 2 = 3 / 16 * (2 * (x₀ / 2 ^ k)) ^ 2 := by
      rw [pow_succ]; ring
    rw [e, Real.rpow_two]
    gcongr
  eq_of_not _ h := absurd trivial h
  density k := by
    have : (successSet (fun _ => True) k).card = k + 1 := by simp [successSet]
    rw [this]; push_cast; linarith

/-- `y²` is dominated of level `2` by `|2y|` with constant `1/4` and `f_* = 0`. -/
theorem isMeasureDominated_sq :
    IsMeasureDominated (fun y : ℝ => y ^ 2) (fun y => |2 * y|) 0 2 (1 / 4) Set.univ :=
  fun y _ => ⟨sq_nonneg y, by rw [Real.rpow_two, sq_abs]; ring_nf; rfl⟩

end Halving

end Optimization
