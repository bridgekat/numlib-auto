import NumlibSurface.CartisGouldToint.Chapter14.Section03Genuine
import NumlibSurface.CartisGouldToint.Chapter14.Section03BadIter

/-!
# Cartis–Gould–Toint §14.3: Theorem 14.3.9 fails for genuine ARqp-SC runs, `q ∈ {1, 2}`

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9 (OCR l. 17583) with
INNER = ARqp-SC and the exponents `π_j = j(p+1)/p` of (14.2.12) (the "otherwise" ARqp-SC entry;
for `q = 1` also the "`q = 1`, `X` convex" ARqp-SC entry `(p+1)/(p-j+1)` and the convex ARqpC-SC
entry, all equal to `(p+1)/p` at `j = 1`).

`Chapter14.Section03Genuine` proves the theorem in the printed order for every run whose INNER
calls are ARqp-SC runs (`IsTPqpGCARqpSCRun`) when `q = p`, and for every `q ≤ p` with an extra term
`∑_j (ε₀ ε_j)^{-j}` (`theorem_14_3_9_arqp_corrected`), which is not within the printed order when
`q < p` (`exists_tpqpOrderF_lt_arqp`). This module shows that the extra term is attained by
genuine runs: for `q = 1`, `p ≥ 4` and for `q = 2`, `p ≥ 5` the printed theorem is false for
INNER = ARqp-SC.

## Main results

* `theorem_14_3_9_arqp_counterexample`: one problem (`n = 2`, `m = 1`, `X = [-1, 1]²`,
  `f(x) = x₁ - x₂/16`, `c(x) = x₁²/2`) satisfying the assumptions of the theorem, and ARqpC
  constants `cexP`, such that for `q ∈ {1, 2}`, `p ≥ q + 3`, and all `κ_F`, `κ_D` there are
  tolerances `ε₀, ε₁ ∈ (0, 1]` (vanishing as `κ_F` grows; `ε₂ = 1`) and a run of
  `IsTPqpGCARqpSCRun` (`θ = β = 1/2`, any `β₁`) whose numbers of evaluations of `(f, c)` and of
  their derivatives exceed `κ_F` and `κ_D` times the printed orders
  `max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `max_j ε₀^{1-π_j} ε_j^{-π_j}`; they are at least
  `(ε₀ ε₁)^{-1}/128`, so the extra term of `theorem_14_3_9_arqp_corrected` is attained in order;
* `theorem_14_3_9_arqp_printed_false`: on that problem, no constants satisfy the conclusion of
  `theorem_14_3_9_arqp` (proved there for `q = p`) with `q ∈ {1, 2}`, `p ≥ q + 3`.

The helpers are in the namespace `Theorem1439ARqpCex`:

* `callOut_one_step`: a one-step call (Step 1 fails at `x`, the detailed Step 2 returns `s`, the
  iteration is successful, Step 1 holds at `x + s`) is an ARqp-SC call (`IsARqpSCCallOut`), for
  any objective whose Taylor model at `x` is exact;
  `Optimization.IsDetailedStepOutput.of_short_step` is the execution of Algorithm 14.1.2 used;
* `taylorSum_merit`, `modelDecr`: `μ(·, t)` is a quartic polynomial, so its Taylor model of degree
  `p ≥ 4` is exact, and the first-order decrement of the regularized model is explicit;
  `decr_two_le`, `modelDecr_two_le`: the second-order decrements (`μ(·, t)` is convex) are at most
  the first-order ones (plus `σ ‖s‖³/2` for the model), and the order-`2` witnesses are maximizers
  (`exists_isApprox_max`);
* `callOut_first`, `callOut_mid`, `callOut_last`, `callOut_run`: every call of the run is an
  ARqp-SC call;
* `isTPqpGCPhase2`, `isARqpSCPhase2Calls`, `isTPqpGCARqpSCRun`, `isEnd_iff`, `funEvals_runS`.

## The run

For `u = 1/(4N⁵)` (`N ≥ 3`), `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `ε₂ = 1`, `M = N¹⁵`: Phase 1
stops at `x₀ = (0, 0)` (`c(x₀) = 0`) and Phase 2 makes `M + 1` outer iterations, each one
ARqp-SC call of one very successful iteration (ratio `1`, `σ = σ₀`, all radii `1`), ending where
INNER's own Step-1 test holds:

* the first moves from `(0, 0)` (`f - t₁ = ε₀`) to `(u, ·)` with `f - t₁ = -E₁`;
* the calls `k ∈ [2, M]` move along `x₂` from `f - t_k = E_{k-1}` to `f - t_k = -E_k`,
  `E_k = (u³/2)(1 - k/(64(M + 1))) ≈ u³/2 ≈ 2 ε₀ ε₁/3`;
* the last moves to `(-3u/4, ·)` with `f - t_{M+1} = (3u/4)³/2`, where (14.3.32) holds with
  `f > t` (case (c)).

At `(u, ·)` the gradient `∇μ(·, t_k) = (u³/2 - E_k, E_k/16)` nearly vanishes (the degenerate
constraint gives `∇ν = (u³/2, 0)`, cancelled by `(f - t_k) ∇f`), so INNER's Step-1 test and the
model criticality of the step hold; the call is a case-(b) iteration and the target drops by
`2 E_k` only, while after the reflection (14.3.35) the gradient is `≈ (u³, ·)` and (14.3.34)
fails. The second-order tests (for `q = 2`) hold everywhere with room to spare: their tolerances
are `∼ ‖r‖ ∼ u²`, while the second-order decrements are at most the first-order ones, `≲ u³`. As
`x₂ ∈ [-1, 1]`, about `1/u³ ∼ (ε₀ ε₁)^{-1} ∼ N¹⁵` such iterations fit, against the printed orders
`≤ 128 N¹⁴` (`order_le_pow`: with `B = 2N²`, `ε₀ ≥ B^{-5}`, `ε₁ ≥ B^{-3}`, every term is at most
`B⁷`; the order-`2` term `ε₀^{1-π₂}` needs `π₂ = 2(p+1)/p ≤ 12/5`, i.e. `p ≥ 5`).

## Faithfulness

The INNER calls are runs of `algorithm_14_1_1` with `c = 0`, `h = 0` (ARqp-SC with Step 2 by
Algorithm 14.1.2), stopped at their own termination and returning their own radii (the first
option of `IsARqpSCCallOut`). All constants of the algorithms (`cexP`: `σ₀ = σ_min`, `η₁`,
`η₂`, `γ₁ < 1 < γ₂ < γ₃`, `θ < ς`; TPqp-GC's `θ`, `β`, `β₁`) are fixed before the tolerances.
The only per-iteration freedom used is the one the book leaves to Step 2:

* Step 2 of Algorithm 14.1.1 (OCR l. 15730) asks only for "an approximate minimizer `s_k`" with
  (14.1.12) `m̂(s_k) ≤ m̂(0)` and either `‖s_k‖ ≥ 1` or (14.1.13); the steps here satisfy these
  conditions, so they are admissible for the algorithm as printed independently of how they are
  computed;
* the run class moreover asks that the step be an output of Algorithm 14.1.2, which it is: Step
  2.1 "Initialize `μ ∈ (0, 1]`" (OCR l. 12588, 15758) is executed afresh at every Step 2 (`μ` is
  not among the Step-0 constants of Algorithm 14.1.1, l. 15715ff.), and starting it with
  `μ = (m(0) - m(s))/(m(0) - m*)` reaches every approximately critical `s` with `m(s) < m(0)`
  (`Optimization.IsDetailedStepOutput.of_short_step`); the book remarks that "the full power of
  global minimization is not required" (l. 12760), and its analysis does not use a lower bound
  on `μ`.

The steps are thus approximate critical points of the model with a tiny model decrease (`≈ u⁹`
against `m(0) - m* ≈ u⁴/8`), not approximate global minimizers. For a restricted variant whose
Step 2.1 uses a `μ` bounded below independently of `ε` (or which minimizes the model globally)
these steps are not admissible, and whether the printed order then holds is not settled here.

## Scope

* `p ≥ 4` is used for the exactness of the Taylor models of the quartic `μ(·, t)`, so that a
  single step can raise `x₁` from `0` to `u`; for `p ≤ 3` the Taylor model is not exact and this
  construction does not apply. For `q = 2` the printed order-`2` term `ε₀^{1-π₂} ∼ u^{-2-4/p}` is
  at least of the order of the count `∼ u^{-3}` when `p ≤ 4`, and for `q ≥ 3` the term
  `ε₀^{1-π₃} ∼ u^{-4-6/p}` always is; with this degenerate constraint (`ε₁ ∼ ε₀^{1/2}`) the
  cases `q = 1 < p ≤ 3`, `q = 2 < p ≤ 4` and `3 ≤ q < p` are not settled.
* The run uses a box `X`; the unit-radius class on `ℝⁿ` (`IsTPqpGCARqpUnitRun`, where f.B.Fb
  fails for this `f`) is not treated.
-/

open Set Metric
open scoped Nat ContDiff

namespace CartisGouldToint.Chapter14

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

namespace Theorem1439ARqpCex

open Theorem1439OrderCex

/-! ### The data -/

/-- The objective `f(x) = x₁ - x₂/16`. -/
noncomputable def objG : ℝ² → ℝ := fun x => x 0 - x 1 / 16

/-- `f(a, b) = a - b/16`. -/
theorem objG_pt (a b : ℝ) : objG (pt a b) = a - b / 16 := by simp [objG]

/-- The derivative of `f`. -/
theorem hasFDerivAt_objG (y : ℝ²) :
    HasFDerivAt objG (EuclideanSpace.proj (0 : Fin 2) -
      (1 / 16 : ℝ) • EuclideanSpace.proj (1 : Fin 2) : ℝ² →L[ℝ] ℝ) y := by
  have := (hasFDerivAt_coord 0 y).sub ((hasFDerivAt_coord 1 y).const_mul (1 / 16 : ℝ))
  convert this using 1
  funext x; simp [objG]; ring

/-- The first-order Taylor decrement of `μ(·, t)` at `y`:
`-∇μ(y, t)[d] = -(y₁³/2 + (f(y) - t)) d₁ + (f(y) - t)/16 d₂`. -/
theorem decr (y : ℝ²) (t : ℝ) (d : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 1 d =
      -(y 0 ^ 3 / 2 + (objG y - t)) * d 0 + (objG y - t) / 16 * d 1 := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [(Constrained.hasFDerivAt_targetMerit (t := t) (hasFDerivAt_objG y)
    (hasFDerivAt_conC y)).fderiv]
  simp [conC, unitE]
  ring

/-- `μ(y, t) = y₁⁴/8 + (f(y) - t)²/2`. -/
theorem merit_eq (y : ℝ²) (t : ℝ) :
    Constrained.targetMerit objG conC t y = y 0 ^ 4 / 8 + (objG y - t) ^ 2 / 2 := by
  rw [Constrained.targetMerit_def, norm_conC]
  ring

/-- `μ(·, t)` is smooth. -/
theorem contDiff_merit (t : ℝ) : ContDiff ℝ ⊤ (Constrained.targetMerit objG conC t) := by
  have e : Constrained.targetMerit objG conC t =
      fun y : ℝ² => y 0 ^ 4 / 8 + (y 0 - y 1 / 16 - t) ^ 2 / 2 := by
    funext y; rw [merit_eq]; rfl
  rw [e]
  have h0 : ContDiff ℝ ⊤ (fun y : ℝ² => y 0) := contDiff_piLp_apply (p := 2)
  have h1 : ContDiff ℝ ⊤ (fun y : ℝ² => y 1) := contDiff_piLp_apply (p := 2)
  exact ((h0.pow 4).div_const 8).add
    ((((h0.sub (h1.div_const 16)).sub contDiff_const).pow 2).div_const 2)

/-- The coefficients of `τ ↦ μ(y + τ s, t)`, a quartic polynomial. -/
noncomputable def coef (y s : ℝ²) (t : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then y 0 ^ 3 * s 0 / 2 + (objG y - t) * (s 0 - s 1 / 16)
  else if i = 2 then 3 * y 0 ^ 2 * s 0 ^ 2 / 4 + (s 0 - s 1 / 16) ^ 2 / 2
  else if i = 3 then y 0 * s 0 ^ 3 / 2
  else if i = 4 then s 0 ^ 4 / 8 else 0

/-- `μ(y + τ s, t) = μ(y, t) + ∑_{i=1}^p τ^i a_i` for `p ≥ 4`. -/
theorem merit_line {p : ℕ} (hp : 4 ≤ p) (y s : ℝ²) (t τ : ℝ) :
    Constrained.targetMerit objG conC t (y + τ • s) =
      Constrained.targetMerit objG conC t y + ∑ i ∈ Finset.Icc 1 p, τ ^ i * coef y s t i := by
  have hsub : Finset.Icc 1 4 ⊆ Finset.Icc 1 p := Finset.Icc_subset_Icc le_rfl hp
  rw [← Finset.sum_subset hsub fun i hi hi' => by
    have h1 := Finset.mem_Icc.1 hi
    have h2 : ¬ (1 ≤ i ∧ i ≤ 4) := fun h => hi' (Finset.mem_Icc.2 h)
    have : i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 4 := by omega
    simp [coef, this.1, this.2.1, this.2.2.1, this.2.2.2]]
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp only [merit_eq, objG, coef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  ring

/-- **The Taylor model of `μ(·, t)` of degree `p ≥ 4` is exact**: `T_p(y, s) = μ(y + s, t)`. -/
theorem taylorSum_merit {p : ℕ} (hp : 4 ≤ p) (y : ℝ²) (t : ℝ) (s : ℝ²) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p s =
      Constrained.targetMerit objG conC t (y + s) := by
  rw [← taylorPolynomial_eq_taylorSum]
  exact Optimization.taylorPolynomial_eq_self_of_poly
    ((contDiff_merit t).contDiffAt.of_le (by exact_mod_cast le_top))
    (merit_line hp y s t)

/-- The coefficient `σ/p! ‖s‖^{p-1}` of the gradient `σ/p! ‖s‖^{p-1} s` of the regularization
term `σ/(p+1)! ‖s‖^{p+1}`. -/
noncomputable def regC (p : ℕ) (σ : ℝ) (s : ℝ²) : ℝ :=
  σ / Optimization.realFactorial ((p : ℝ) + 1 - 1) * ‖s‖ ^ ((p : ℝ) + 1 - 2)

/-- **The first-order decrement of the model** `m(s) = μ(y + s, t) + σ/(p+1)! ‖s‖^{p+1}` (`p ≥ 4`)
at the trial step `s` along `d`: the decrement of `μ(·, t)` at `y + s` minus `c ⟨s, d⟩`,
`c = regC p σ s`. -/
theorem modelDecr {p : ℕ} (hp : 4 ≤ p) (y s d : ℝ²) (t σ : ℝ) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 1 d =
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) (y + s)).taylorDecrement 1 d -
        regC p σ s * (s 0 * d 0 + s 1 * d 1) := by
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  have hr : (1 : ℝ) < (p : ℝ) + 1 := by
    have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    linarith
  rw [Optimization.regularizedModel_eq_powRegularizedModel,
    Optimization.fderiv_powRegularizedModel hr]
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p =
      fun v => Constrained.targetMerit objG conC t (y + v) :=
    funext (taylorSum_merit hp y t)
  rw [hT, fderiv_comp_add_left]
  simp only [add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [show (inner ℝ s d : ℝ) = s 0 * d 0 + s 1 * d 1 by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring]
  unfold regC
  ring

/-- The Taylor decrements of order `j ≤ 4` of `μ(·, t)` at `y`: `ΔT_j(y, d) = -∑_{i=1}^j a_i`. -/
theorem decr_eq_coef {j : ℕ} (hj : j ≤ 4) (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement j d =
      -∑ i ∈ Finset.Icc 1 j, coef y d t i := by
  rw [FormalMultilinearSeries.taylorDecrement, ← taylorPolynomial_eq_taylorSum,
    taylorPolynomial_zero_right,
    Optimization.taylorPolynomial_eq_of_poly (N := 4) (a := coef y d t)
      ((contDiff_merit t).contDiffAt.of_le (by exact_mod_cast le_top))
      (Filter.Eventually.of_forall fun τ => by simpa [one_mul] using merit_line le_rfl y d t τ) hj]
  ring

/-- **The second-order decrement of `μ(·, t)` is at most the first-order one** (`μ` is convex):
`ΔT_2(y, d) = ΔT_1(y, d) - a_2` with `a_2 = 3 y₁² d₁²/4 + (d₁ - d₂/16)²/2 ≥ 0`. -/
theorem decr_two_le (y d : ℝ²) (t : ℝ) :
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorDecrement 1 d := by
  rw [decr_eq_coef (by norm_num), decr_eq_coef (by norm_num)]
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide]
  simp [coef]
  nlinarith [sq_nonneg (d 0 - d 1 / 16), sq_nonneg (y 0 * d 0)]

/-- `∇²μ(y, t)[d]² ≥ 0`. -/
theorem iteratedFDeriv_two_merit_nonneg (y d : ℝ²) (t : ℝ) :
    0 ≤ iteratedFDeriv ℝ 2 (Constrained.targetMerit objG conC t) y (fun _ => d) := by
  have h := decr_two_le y d t
  rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide] at h
  simp only [Finset.Icc_self, Finset.sum_singleton, ftaylorSeries] at h
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h
  norm_num at h
  linarith

/-- **The second-order decrement of the model is at most the first-order one plus
`σ ‖s‖³/2`** (`p ≥ 4`, `σ ≥ 0`, `‖s‖, ‖d‖ ≤ 1`): the Hessian of `μ` is positive semidefinite and
that of the regularization term is at most `σ ‖s‖^{p-1}/(p-1)!` in norm. -/
theorem modelDecr_two_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) (y : ℝ²) (t : ℝ) {s d : ℝ²}
    (hs : ‖s‖ ≤ 1) (hd : ‖d‖ ≤ 1) :
    (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 2 d ≤
      (ftaylorSeries ℝ (Optimization.regularizedModel
        (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ) s).taylorDecrement 1 d +
        σ * ‖s‖ ^ 3 / 2 := by
  set m := Optimization.regularizedModel
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y) p σ with hm
  have e : (ftaylorSeries ℝ m s).taylorDecrement 2 d =
      (ftaylorSeries ℝ m s).taylorDecrement 1 d - 1 / 2 * iteratedFDeriv ℝ 2 m s (fun _ => d) := by
    rw [FormalMultilinearSeries.taylorDecrement_eq, FormalMultilinearSeries.taylorDecrement_eq,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.Icc_self, Finset.sum_singleton]
    simp only [ftaylorSeries]
    norm_num
    ring
  have hT : (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) y).taylorSum p =
      fun v => Constrained.targetMerit objG conC t (y + v) :=
    funext (taylorSum_merit hp y t)
  have e2 : iteratedFDeriv ℝ 2 m s (fun _ => d) =
      iteratedFDeriv ℝ 2 (Constrained.targetMerit objG conC t) (y + s) (fun _ => d) +
        σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d) := by
    rw [hm, Optimization.iteratedFDeriv_regularizedModel (Or.inl (by omega)), hT,
      iteratedFDeriv_comp_add_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
  rw [e, e2]
  have h1 := iteratedFDeriv_two_merit_nonneg (y + s) d t
  have h2 := abs_iteratedFDeriv_norm_pow_apply_le (E := ℝ²) (r := p + 1) (ℓ := 2) (by omega)
    (s := s) (Or.inr (by omega)) d
  have hf : ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) ≤ ((p + 1)! : ℝ) := by
    apply div_le_self (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hs3 : ‖s‖ ^ (p + 1 - 2) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hd2 : ‖d‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hd
  have hb : |iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d)| ≤
      ((p + 1)! : ℝ) * ‖s‖ ^ 3 := by
    refine h2.trans ?_
    calc ((p + 1)! : ℝ) / ((p + 1 - 2)! : ℝ) * ‖s‖ ^ (p + 1 - 2) * ‖d‖ ^ 2
        ≤ ((p + 1)! : ℝ) * ‖s‖ ^ 3 * 1 := by gcongr
      _ = _ := mul_one _
  have hc : σ / ((p + 1)! : ℝ) * iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s
      (fun _ => d) ≥ -(σ * ‖s‖ ^ 3) := by
    have hpf : (0 : ℝ) < ((p + 1)! : ℝ) := by positivity
    have := neg_abs_le (iteratedFDeriv ℝ 2 (fun y : ℝ² => ‖y‖ ^ (p + 1)) s (fun _ => d))
    have h3 : σ / ((p + 1)! : ℝ) * (-(((p + 1)! : ℝ) * ‖s‖ ^ 3)) = -(σ * ‖s‖ ^ 3) := by
      field_simp
    rw [ge_iff_le, ← h3]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **A witness from a maximizer**: a continuous decrement vanishing at `0` attains its supremum
over the unit ball intersected with a closed set containing `0`, and a maximizer is a
`ς`-approximate optimality displacement for every `ς ≤ 1`. -/
theorem exists_isApprox_max {Δ : ℝ² → ℝ} (hc : Continuous Δ) (hΔ0 : Δ 0 = 0) {S : Set ℝ²}
    (hS : IsClosed S) (h0 : (0 : ℝ²) ∈ S) {ς : ℝ} (hς : ς ≤ 1) :
    ∃ d, Optimization.IsApproxMeasureStep Δ 1 S ς d ∧
      Δ d = Optimization.decrementMeasure Δ 1 S := by
  have hK : IsCompact (closedBall (0 : ℝ²) 1 ∩ S) := (isCompact_closedBall 0 1).inter_right hS
  have hne : (closedBall (0 : ℝ²) 1 ∩ S).Nonempty := ⟨0, mem_closedBall_self zero_le_one, h0⟩
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  have hsup : Optimization.decrementMeasure Δ 1 S = Δ d :=
    IsGreatest.csSup_eq ⟨mem_image_of_mem Δ hd, forall_mem_image.2 fun y hy => hmax hy⟩
  have hd0 : 0 ≤ Δ d := hΔ0 ▸ hmax ⟨mem_closedBall_self zero_le_one, h0⟩
  refine ⟨d, ⟨hd, ?_⟩, hsup.symm⟩
  rw [hsup]
  nlinarith

/-- Taylor decrements of a formal multilinear series are continuous and vanish at `0`. -/
theorem continuous_taylorDecrement (D : FormalMultilinearSeries ℝ ℝ² ℝ) (j : ℕ) :
    Continuous (D.taylorDecrement j) :=
  continuous_const.sub (D.contDiff_taylorSum j (n := 0)).continuous

/-! ### Linear decrements on `ℝ²` -/

/-- `|d_i| ≤ ‖d‖`. -/
theorem abs_apply_le (d : ℝ²) (i : Fin 2) : |d i| ≤ ‖d‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le d i

/-- A linear decrement `a d₁ + b d₂` is at most `|a| + |b|` on the unit ball. -/
theorem lin_le (a b : ℝ) {d : ℝ²} (hd : ‖d‖ ≤ 1) : a * d 0 + b * d 1 ≤ |a| + |b| := by
  have h0 := (abs_apply_le d 0).trans hd
  have h1 := (abs_apply_le d 1).trans hd
  have e0 : a * d 0 ≤ |a| := by
    calc a * d 0 ≤ |a * d 0| := le_abs_self _
      _ = |a| * |d 0| := abs_mul _ _
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left h0 (abs_nonneg a)
      _ = |a| := mul_one _
  have e1 : b * d 1 ≤ |b| := by
    calc b * d 1 ≤ |b * d 1| := le_abs_self _
      _ = |b| * |d 1| := abs_mul _ _
      _ ≤ |b| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg b)
      _ = |b| := mul_one _
  linarith

/-- The measure of a linear decrement `d ↦ a d₁ + b d₂` with radius `1` is at most `|a| + |b|`. -/
theorem measure_lin_le {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1) {S : Set ℝ²}
    (h0 : (0 : ℝ²) ∈ S) : Optimization.decrementMeasure Δ 1 S ≤ |a| + |b| :=
  Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩ fun d hd => by
    rw [hΔ]; exact lin_le a b (mem_closedBall_zero_iff.1 hd.1)

/-- `‖(a, b)‖ ≤ 1` for `|a|, |b| ≤ 1/2`. -/
theorem norm_pt_le {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) : ‖pt a b‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_one]
  simp only [pt_zero, pt_one, Real.norm_eq_abs, sq_abs]
  have := abs_le.1 ha
  have := abs_le.1 hb
  nlinarith

/-- **A witness for a linear decrement with `ς = 1/2`**: a feasible displacement `w` of norm at
most `1` whose decrease is at least `(|a| + |b|)/2` is a `1/2`-approximate optimality
displacement. -/
theorem isApprox_lin {Δ : ℝ² → ℝ} {a b : ℝ} (hΔ : ∀ d, Δ d = a * d 0 + b * d 1) {S : Set ℝ²}
    (h0 : (0 : ℝ²) ∈ S) {w : ℝ²} (hw : ‖w‖ ≤ 1) (hwS : w ∈ S) (hval : (|a| + |b|) / 2 ≤ Δ w) :
    Optimization.IsApproxMeasureStep Δ 1 S (1 / 2) w :=
  ⟨⟨mem_closedBall_zero_iff.2 hw, hwS⟩, by have := measure_lin_le hΔ h0; linarith⟩

/-! ### One-step ARqp-SC calls -/

/-- The constants of ARqpC used by the counterexample: `σ₀ = σ_min = 10⁻⁶`, `η₁ = 1/4`,
`η₂ = 3/4`, `γ₁ = 1/2`, `γ₂ = 2 < γ₃ = 3`, `θ = 1/4`, `ς = 1/2` (so `θ < ς`). -/
noncomputable def cexP : ARqpCParams where
  σ₀ := 1 / 10 ^ 6
  σmin := 1 / 10 ^ 6
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 2
  γ₂ := 2
  γ₃ := 3
  σ₀_pos := by norm_num
  σmin_nonneg := by norm_num
  σmin_le_σ₀ := le_rfl
  η₁_pos := by norm_num
  η₁_le_η₂ := by norm_num
  η₂_lt_one := by norm_num
  γ₁_pos := by norm_num
  γ₁_lt_one := by norm_num
  one_lt_γ₂ := by norm_num
  γ₂_le_γ₃ := by norm_num
  θ := 1 / 4
  ς := 1 / 2
  θ_pos := by norm_num
  θ_lt_one := by norm_num
  ς_pos := by norm_num
  ς_le_one := by norm_num
  σmin_pos := by norm_num

/-- The iterates `x, x + s, x + s, …` of a one-step INNER call. -/
noncomputable def stepX {n : ℕ} (x s : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) :=
  fun i => if i = 0 then x else x + s

@[simp] theorem stepX_zero {n : ℕ} (x s : EuclideanSpace ℝ (Fin n)) : stepX x s 0 = x := rfl

theorem stepX_succ {n : ℕ} (x s : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    stepX x s (i + 1) = x + s := rfl

/-- **A one-step ARqp-SC call** (ARqpC-SC with `c = 0`, `h = 0`, `1 ≤ q ≤ p`, all radii `1`) on
an objective `F` bounded below on `X` whose Taylor model of degree `p` at `x` is exact: INNER's
Step-1 test fails at `x` (the witnesses `d₀ j`), the detailed Step 2 returns the step `s` (model
decrease, the model witnesses `dm j` at `s`), the iteration is very successful (ratio `1`), and
the Step-1 test holds at `x + s` (the witnesses `d₁ j`), where the run terminates. Its iterates
are `x, x + s`, one successful iteration, output radius `1`. -/
theorem callOut_one_step {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : Set (EuclideanSpace ℝ (Fin n))} {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) {P : ARqpCParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) {x s : EuclideanSpace ℝ (Fin n)}
    {d₀ d₁ dm : ℕ → EuclideanSpace ℝ (Fin n)} (hx : x ∈ X)
    (hxs : x + s ∈ X) (hs1 : ‖s‖ < 1)
    (hTay : ∀ v, (ftaylorSeries ℝ F x).taylorSum p v = F (x + v)) (hlow : BddBelow (F '' X))
    (hmod : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ s < F x)
    (hd₀ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F x).taylorDecrement j) 1 {e | x + e ∈ X} P.ς (d₀ j))
    (hfail : ∃ j ∈ Finset.Icc 1 q, P.ς * ε j / j ! < (ftaylorSeries ℝ F x).taylorDecrement j (d₀ j))
    (hdm : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep ((ftaylorSeries ℝ
      (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀) s).taylorDecrement j) 1
      {e | x + s + e ∈ X} P.ς (dm j) ∧
      (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀)
        s).taylorDecrement j (dm j) ≤ P.ς * P.θ * ε j / j !)
    (hd₁ : ∀ j ∈ Finset.Icc 1 q, Optimization.IsApproxMeasureStep
      ((ftaylorSeries ℝ F (x + s)).taylorDecrement j) 1 {e | x + s + e ∈ X} P.ς (d₁ j))
    (hpass : ∀ j ∈ Finset.Icc 1 q,
      (ftaylorSeries ℝ F (x + s)).taylorDecrement j (d₁ j) ≤ P.ς * ε j / j !) :
    IsARqpSCCallOut F X p q P ε (stepX x s) 1 (fun _ => True) (fun _ => 1) := by
  set xs := stepX x s with hxs_def
  set ss : ℕ → EuclideanSpace ℝ (Fin n) := fun _ => s
  set σs : ℕ → ℝ := fun _ => P.σ₀
  set δ : ℕ → ℕ → ℝ := fun _ _ => 1
  set dd : ℕ → ℕ → EuclideanSpace ℝ (Fin n) := fun i j => if i = 0 then d₀ j else d₁ j
  set dmm : ℕ → ℕ → EuclideanSpace ℝ (Fin n) := fun _ j => dm j
  have hx0 : xs 0 = x := rfl
  have hx1 : xs 1 = x + s := rfl
  have hT0 : (ftaylorSeries ℝ F x).taylorSum p 0 = F x := by rw [hTay, add_zero]
  have hm0 : Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ 0 = F x :=
    Optimization.regularizedModel_ftaylorSeries_zero_right p P.σ₀ F x
  have hreg : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
    have := P.σ₀_pos; positivity
  have hFs : F (x + s) < F x := by
    rw [Optimization.regularizedModel_def, hTay] at hmod; linarith
  have hpred : (ftaylorSeries ℝ F x).taylorDecrement p s = F x - F (x + s) := by
    rw [FormalMultilinearSeries.taylorDecrement, hTay, hTay, add_zero]
  have hρ : Chapter12.arqpRho F p xs ss σs 0 = 1 := by
    simp only [Chapter12.arqpRho, Optimization.arqpRatio, Chapter12.arqpData,
      Optimization.ARqpData.ofTaylor_pred, Optimization.reductionRatio, hx0, ss, hpred]
    exact div_self (by linarith)
  -- the Step-1 tests
  have h1stop :
      Optimization.arqpStop₁ P.toARqpParams q ε (Chapter12.arqpData F p xs σs) δ dd 1 := by
    intro j hj
    simpa [dd, δ, hx1] using hpass j hj
  have hn1 : ¬ Optimization.arqpStop₁ P.toARqpParams q ε (Chapter12.arqpData F p xs σs) δ dd 0 := by
    intro h
    obtain ⟨j, hj, hlt⟩ := hfail
    have := h j hj
    simp [dd, δ, hx0] at this
    linarith
  have hn2 : ¬ Optimization.arqpStop₂ (Chapter12.arqpData F p xs σs) ss 0 := by
    intro h
    simp only [Optimization.arqpStop₂, Chapter12.arqpData, Optimization.ARqpData.ofTaylor_model,
      hx0, ss, σs] at h
    rw [h, hm0] at hmod
    exact lt_irrefl _ hmod
  have hNot0 : ¬ Chapter12.arqpStop F P.toARqpParams p q ε xs ss σs δ dd 0 := by
    rintro (h | h)
    · exact hn1 h
    · exact hn2 h
  have hStop1 : Chapter12.arqpStop F P.toARqpParams p q ε xs ss σs δ dd 1 := Or.inl h1stop
  -- the model is bounded below on the feasible steps
  have hbdd : BddBelow (Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ ''
      {v | x + v ∈ X}) := by
    obtain ⟨b, hb⟩ := hlow
    refine ⟨b, forall_mem_image.2 fun v hv => ?_⟩
    rw [Optimization.regularizedModel_def, hTay]
    have := hb (mem_image_of_mem F hv)
    have : 0 ≤ P.σ₀ / ((p + 1)! : ℝ) * ‖v‖ ^ (p + 1) := by have := P.σ₀_pos; positivity
    linarith
  -- the ARqp run
  have hrun : Chapter12.algorithm_12_2_2_feasible F X P.toARqpParams p q ε (fun _ => 1) xs ss σs
      δ δ dd dmm := by
    refine ⟨⟨rfl, fun k hk h1 => ?_, fun k hk => ?_⟩, hx, rfl, fun k hk => ?_, fun k hk => ?_⟩
    · rcases k with _ | _ | k
      · refine ⟨by simpa [hx0, ss] using hxs, ?_, fun h => ?_, fun _ _ => one_pos,
          fun _ _ => le_rfl, Or.inr fun j hj => ?_⟩
        · simp only [Chapter12.arqpData, Optimization.ARqpData.ofTaylor_model, hx0, ss, σs, hm0]
          exact hmod.le
        · simp only [Chapter12.arqpData, Optimization.ARqpData.ofTaylor_model, hx0, ss, σs,
            hm0] at h
          exact absurd h hmod.ne
        · simp only [Chapter12.arqpData, Optimization.ARqpData.ofTaylor_modelDec, hx0, ss, σs,
            dmm, δ]
          exact ⟨(hdm j hj).1, by simpa using (hdm j hj).2⟩
      · exact absurd h1stop h1
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have := Optimization.arAcceptance_of_one_le P.toARParams (ρ := 1) le_rfl x s
          (σ := P.σ₀) P.σmin_le_σ₀ P.σ₀_pos.le
        change Optimization.ARAcceptance P.toARParams (Chapter12.arqpRho F p xs ss σs 0) (xs 0)
          (ss 0) (xs 1) (σs 0) (σs 1)
        rw [hρ, hx0, hx1]
        exact this
      · exact absurd hStop1 (hk 1 (by omega))
    · intro j hj
      rcases k with _ | _ | k
      · exact hd₀ j hj
      · exact hd₁ j hj
      · exact absurd hStop1 (hk 1 (by omega))
    · rcases k with _ | k
      · have hρ' : Optimization.arqpRatio F (Chapter12.arqpData F p xs σs) xs ss 0 = 1 := hρ
        refine ⟨fun _ => rfl, fun h => absurd ?_ h⟩
        rw [hρ']
        exact P.η₁_le_η₂.trans P.η₂_lt_one.le
      · exact absurd hStop1 (hk 1 (by omega))
  -- the ARqpC-SC run
  have h1 : (fun y => F y + zeroOuter (zeroCon n y)) = F := funext fun y => by simp
  have h2 := zero_arqpcData_eq F p xs σs
  have hr : algorithm_14_1_1 F (zeroCon n) zeroOuter X p q P ε (fun _ => 1) xs ss σs δ δ dd
      dmm := by
    refine ⟨hq, hqp, hε, fun _ _ => ⟨one_pos, le_rfl⟩, by rw [h1, h2]; exact hrun,
      fun k hk hns => ?_⟩
    rw [h2] at hns
    rcases k with _ | _ | k
    · have em : Optimization.compositeRegularizedModel (ftaylorSeries ℝ F x)
          (ftaylorSeries ℝ (zeroCon n) x) zeroOuter p P.σ₀ =
          Optimization.regularizedModel (ftaylorSeries ℝ F x) p P.σ₀ :=
        Optimization.compositeRegularizedModel_zero_fun _ _ _ _
      have eΔ : (fun j s d => Optimization.compositeModelDecrement (ftaylorSeries ℝ F x)
          (ftaylorSeries ℝ (zeroCon n) x) zeroOuter p P.σ₀ j s d) =
          fun j s d => (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ F x) p
            P.σ₀) s).taylorDecrement j d := by
        funext j s d
        exact congrFun (Optimization.compositeModelDecrement_zero_fun _ _ _ _ j s) d
      unfold algorithm_14_1_2
      simp only [hx0, ss, σs, δ]
      rw [em, eΔ]
      exact Optimization.IsDetailedStepOutput.of_short_step hq hxs hbdd (by rw [hm0]; exact hmod)
        hs1 fun j hj => ⟨(hdm j hj).1.1, (hdm j hj).1.2, (hdm j hj).2⟩
    · exact absurd h1stop hns
    · exact absurd (zero_arqpcStop_iff.2 hStop1) (hk 1 (by omega))
  refine ⟨xs, ss, σs, δ, δ, dd, dmm, 1, hr, ⟨zero_arqpcStop_iff.2 hStop1, fun j hj => ?_⟩,
    le_rfl, fun i _ => rfl, fun i hi => ?_, Or.inl fun j _ => rfl⟩
  · obtain rfl : j = 0 := by omega
    exact zero_arqpcStop_iff.not.2 hNot0
  · obtain rfl : i = 0 := by omega
    rw [zero_arqpRatio_eq, hρ]
    exact iff_of_true trivial (P.η₁_le_η₂.trans P.η₂_lt_one.le)


/-! ### One-step calls on the counterexample -/

/-- `(a, b) - (a', b') = (a - a', b - b')`. -/
theorem pt_sub (a b a' b' : ℝ) : pt a b - pt a' b' = pt (a - a') (b - b') := by
  ext i; fin_cases i <;> simp

/-- `(a, b) + d = (a + d₁, b + d₂)`. -/
theorem pt_add (a b : ℝ) (d : ℝ²) : pt a b + d = pt (a + d 0) (b + d 1) := by
  ext i; fin_cases i <;> simp

/-- `‖(a, b)‖ ≤ |a| + |b|`. -/
theorem norm_pt_le_add (a b : ℝ) : ‖pt a b‖ ≤ |a| + |b| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_left (by positivity)]
  simp only [pt_zero, pt_one, Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- `(a, b) ∈ X = [-1, 1]²` for `|a|, |b| ≤ 1`. -/
theorem pt_mem {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : pt a b ∈ boxX := by
  simp only [boxX, mem_ofPred_eq, pt_zero, pt_one]; exact ⟨ha, hb⟩

/-- `0 ≤ regC p σ s ≤ σ ‖s‖³/24` for `σ ≥ 0`, `‖s‖ ≤ 1`, `p ≥ 4`. -/
theorem regC_mem {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    0 ≤ regC p σ s ∧ regC p σ s ≤ σ * ‖s‖ ^ 3 / 24 := by
  have e1 : (p : ℝ) + 1 - 1 = (p : ℝ) := by ring
  have e2 : (p : ℝ) + 1 - 2 = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  unfold regC
  rw [e1, e2, Optimization.realFactorial_natCast, Real.rpow_natCast]
  have hf : (24 : ℝ) ≤ (p ! : ℝ) := by
    have := Nat.factorial_le hp
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p - 1) ≤ ‖s‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  have hn : 0 ≤ ‖s‖ ^ (p - 1) := by positivity
  refine ⟨by positivity, ?_⟩
  calc σ / (p ! : ℝ) * ‖s‖ ^ (p - 1) ≤ σ / 24 * ‖s‖ ^ 3 := by
        gcongr
    _ = σ * ‖s‖ ^ 3 / 24 := by ring

/-- `σ/(p+1)! ‖s‖^{p+1} ≤ σ ‖s‖⁵/120` for `σ ≥ 0`, `‖s‖ ≤ 1`, `p ≥ 4`. -/
theorem reg_le {p : ℕ} (hp : 4 ≤ p) {σ : ℝ} (hσ : 0 ≤ σ) {s : ℝ²} (hs : ‖s‖ ≤ 1) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ * ‖s‖ ^ 5 / 120 := by
  have hf : (120 : ℝ) ≤ ((p + 1)! : ℝ) := by
    have := Nat.factorial_le (show 5 ≤ p + 1 by omega)
    exact_mod_cast this
  have hpow : ‖s‖ ^ (p + 1) ≤ ‖s‖ ^ 5 := pow_le_pow_of_le_one (norm_nonneg _) hs (by omega)
  calc σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ / 120 * ‖s‖ ^ 5 := by
        gcongr
    _ = σ * ‖s‖ ^ 5 / 120 := by ring

/-- **A one-step call of the counterexample.** For the target `t`, the start `x = (xa, xb)` and
the landing point `x' = (ya, yb)` in `[-1/2, 1/2]²` with `F = f(x) - t`, `F' = f(x') - t`,
`L = |ya - xa| + |yb - xb| ≤ 1/2`, an order `q ∈ {1, 2}`, INNER tolerances `T₁ ∈ (0, 1]`
(order `1`) and `T₂ ∈ (0, 1]` (order `2`, used when `q = 2`, with `T₁/4 + σ₀ L³/2 ≤ T₂/16`), and
a sign `g = ±1`: if the linear decrease at `x` exceeds `T₁` (Step 1 fails), `μ` decreases by more
than the regularization bound `σ₀ L⁵/120`, and at `x'` the gradient has the signs of `g` and
`ℓ¹`-norm plus `σ₀ L⁴/24` at most `T₁/4` (model criticality, and Step 1 holds; at order `2` the
decrements are bounded through `decr_two_le` and `modelDecr_two_le`, and the witnesses are
maximizers), then the call from `x` to `x'` is a one-step ARqp-SC call with parameters `cexP`. -/
theorem callOut_cex {p q : ℕ} (hp : 4 ≤ p) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {t xa xb ya yb T₁ T₂ g : ℝ} {ε : ℕ → ℝ} (hT : ε 1 = T₁) (hT2 : 2 ≤ q → ε 2 = T₂)
    (hT20 : 0 < T₂) (hT21 : T₂ ≤ 1)
    (hT12 : T₁ / 4 + 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 ≤ T₂ / 16)
    (hxa : |xa| ≤ 1 / 2) (hxb : |xb| ≤ 1 / 2) (hya : |ya| ≤ 1 / 2) (hyb : |yb| ≤ 1 / 2)
    (hL : |ya - xa| + |yb - xb| ≤ 1 / 2) (hT0 : 0 < T₁) (hT1 : T₁ ≤ 1)
    (hF0 : 0 ≤ xa - xb / 16 - t) (hxa0 : 0 ≤ xa)
    (hfail : T₁ < xa ^ 3 / 2 + (xa - xb / 16 - t) + (xa - xb / 16 - t) / 16)
    (hmod : ya ^ 4 / 8 + (ya - yb / 16 - t) ^ 2 / 2 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 5 / 120 < xa ^ 4 / 8 + (xa - xb / 16 - t) ^ 2 / 2)
    (hg : g = 1 ∨ g = -1) (hgA : 0 ≤ g * (ya ^ 3 / 2 + (ya - yb / 16 - t)))
    (hgF : g * (ya - yb / 16 - t) ≤ 0) (hgs0 : 0 ≤ g * (ya - xa)) (hgs1 : 0 ≤ g * (yb - xb))
    (hcrit : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 ≤ T₁ / 4) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC t) boxX p q cexP ε
      (fun i => if i = 0 then pt xa xb else pt ya yb) 1 (fun _ => True) (fun _ => 1) := by
  have hg1 : |g| = 1 := by rcases hg with rfl | rfl <;> simp
  set s := pt ya yb - pt xa xb with hs_def
  have hs : s = pt (ya - xa) (yb - xb) := pt_sub _ _ _ _
  have hxs : pt xa xb + s = pt ya yb := by rw [hs_def]; abel
  have hsL : ‖s‖ ≤ |ya - xa| + |yb - xb| := by rw [hs]; exact norm_pt_le_add _ _
  have hs1 : ‖s‖ ≤ 1 := by linarith
  have hσ : cexP.σ₀ = 1 / 10 ^ 6 := rfl
  have hς : cexP.ς = 1 / 2 := rfl
  have hθ : cexP.θ = 1 / 4 := rfl
  have hxi : (fun i => if i = 0 then pt xa xb else pt ya yb) = stepX (pt xa xb) s := by
    funext i; rcases i with _ | i
    · rfl
    · simp [stepX, hxs]
  rw [hxi]
  have hmemx : pt xa xb ∈ boxX := pt_mem (hxa.trans (by norm_num)) (hxb.trans (by norm_num))
  have hmemy : pt ya yb ∈ boxX := pt_mem (hya.trans (by norm_num)) (hyb.trans (by norm_num))
  have hS : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → ∀ {c d : ℝ}, |c| ≤ 1 / 2 → |d| ≤ 1 / 2 →
      pt c d ∈ {e | pt a b + e ∈ boxX} := fun {a b} ha hb {c d} hc hd => by
    simp only [mem_ofPred_eq, pt_add, pt_zero, pt_one]
    exact pt_mem ((abs_add_le _ _).trans (by linarith)) ((abs_add_le _ _).trans (by linarith))
  have h0S : ∀ {a b : ℝ}, |a| ≤ 1 / 2 → |b| ≤ 1 / 2 → (0 : ℝ²) ∈ {e | pt a b + e ∈ boxX} :=
    fun {a b} ha hb => by
      simp only [mem_ofPred_eq, add_zero]
      exact pt_mem (ha.trans (by norm_num)) (hb.trans (by norm_num))
  have hhalf : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hhalf' : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hgw : |-g / 2| ≤ 1 / 2 := by rw [abs_div, abs_neg, hg1]; norm_num
  obtain ⟨hc0, hc1⟩ := regC_mem hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) hs1
  have hcL : regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|) ≤
      1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have hL0 : 0 ≤ |ya - xa| + |yb - xb| := by positivity
    calc regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|)
        ≤ cexP.σ₀ * ‖s‖ ^ 3 / 24 * (|ya - xa| + |yb - xb|) :=
          mul_le_mul_of_nonneg_right hc1 hL0
      _ ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 24 * (|ya - xa| + |yb - xb|) := by
          rw [hσ]; gcongr
      _ = _ := by ring
  have hgabs : ∀ z : ℝ, 0 ≤ -g * z → |z| = -g * z := fun z hz => by
    rcases hg with rfl | rfl
    · simp only [neg_mul, one_mul] at hz ⊢; exact abs_of_nonpos (by linarith)
    · simp only [neg_neg, one_mul] at hz ⊢; exact abs_of_nonneg hz
  have hgle : ∀ z : ℝ, g * z ≤ |z| := fun z => by
    rcases hg with rfl | rfl
    · simp only [one_mul]; exact le_abs_self z
    · simp only [neg_one_mul]; exact neg_le_abs z
  have hs0 : s 0 = ya - xa := by rw [hs, pt_zero]
  have hs1' : s 1 = yb - xb := by rw [hs, pt_one]
  have hΔm : ∀ d : ℝ², (ftaylorSeries ℝ (Optimization.regularizedModel (ftaylorSeries ℝ
      (Constrained.targetMerit objG conC t) (pt xa xb)) p cexP.σ₀) s).taylorDecrement 1 d =
      (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) * d 0 +
        ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) * d 1 := fun d => by
    rw [modelDecr hp, hxs, decr, objG_pt, hs0, hs1']
    simp only [pt_zero]
    ring
  have hΔ' : ∀ d : ℝ², (ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb + s)).taylorDecrement 1 d =
      -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * d 0 + (ya - yb / 16 - t) / 16 * d 1 := fun d => by
    rw [hxs, decr, objG_pt]; simp only [pt_zero]
  have hgs0' : 0 ≤ regC p cexP.σ₀ s * (g * (ya - xa)) := mul_nonneg hc0 hgs0
  have hgs1' : 0 ≤ regC p cexP.σ₀ s * (g * (yb - xb)) := mul_nonneg hc0 hgs1
  have hab0 : |-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)| =
      -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) :=
    hgabs _ (by
      have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) + regC p cexP.σ₀ s * (g * (ya - xa)) := by ring
      rw [e]; linarith)
  have hab1 : |(ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)| =
      -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) =
        -(g * (ya - yb / 16 - t)) / 16 + regC p cexP.σ₀ s * (g * (yb - xb)) := by ring
      rw [e]; linarith)
  have hab0' : |-(ya ^ 3 / 2 + (ya - yb / 16 - t))| = -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) :=
    hgabs _ (by rw [neg_mul_neg]; exact hgA)
  have hab1' : |(ya - yb / 16 - t) / 16| = -g * ((ya - yb / 16 - t) / 16) :=
    hgabs _ (by
      have e : -g * ((ya - yb / 16 - t) / 16) = -(g * (ya - yb / 16 - t)) / 16 := by ring
      rw [e]; linarith)
  have hsg : g * (ya - xa) + g * (yb - xb) ≤ |ya - xa| + |yb - xb| :=
    add_le_add (hgle _) (hgle _)
  have hcs : regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb)) ≤
      regC p cexP.σ₀ s * (|ya - xa| + |yb - xb|) := mul_le_mul_of_nonneg_left hsg hc0
  -- the order-`2` witnesses: maximizers
  have hSc : ∀ z : ℝ², IsClosed {e : ℝ² | z + e ∈ boxX} := fun z =>
    isClosed_boxX.preimage (continuous_const.add continuous_id)
  have hς1 : cexP.ς ≤ 1 := cexP.ς_le_one
  obtain ⟨w₀, hw₀, -⟩ := exists_isApprox_max (continuous_taylorDecrement (ftaylorSeries ℝ
    (Constrained.targetMerit objG conC t) (pt xa xb)) 2)
    (FormalMultilinearSeries.taylorDecrement_zero_right _ _) (hSc _) (h0S hxa hxb) hς1
  obtain ⟨wm, hwm, hwm'⟩ := exists_isApprox_max (continuous_taylorDecrement (ftaylorSeries ℝ
    (Optimization.regularizedModel (ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb)) p cexP.σ₀) s) 2)
    (FormalMultilinearSeries.taylorDecrement_zero_right _ _) (hSc (pt xa xb + s))
    (by rw [hxs]; exact h0S hya hyb) hς1
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_isApprox_max (continuous_taylorDecrement (ftaylorSeries ℝ
    (Constrained.targetMerit objG conC t) (pt xa xb + s)) 2)
    (FormalMultilinearSeries.taylorDecrement_zero_right _ _) (hSc (pt xa xb + s))
    (by rw [hxs]; exact h0S hya hyb) hς1
  have hj12 : ∀ j ∈ Finset.Icc 1 q, j = 1 ∨ (j = 2 ∧ 2 ≤ q) := fun j hj => by
    have := Finset.mem_Icc.1 hj; omega
  have hgsum : g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 ≤
      T₁ / 4 := by
    have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 4 / 24 := by positivity
    linarith
  -- order-2 bounds
  have hm2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Optimization.regularizedModel
      (ftaylorSeries ℝ (Constrained.targetMerit objG conC t) (pt xa xb)) p cexP.σ₀)
        s).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ boxX} ≤ T₂ / 16 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := modelDecr_two_le hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) (pt xa xb) t hs1 hd1
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa))
      ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) hd1
    rw [← hΔm, hab0, hab1] at h1
    have h3 : ‖s‖ ^ 3 ≤ (|ya - xa| + |yb - xb|) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hsL 3
    have e : -g * (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) +
        -g * ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
          regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb)) := by ring
    rw [e] at h1
    have h4 : cexP.σ₀ * ‖s‖ ^ 3 / 2 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by
      rw [hσ]; gcongr
    linarith
  have hμ2 : Optimization.decrementMeasure ((ftaylorSeries ℝ (Constrained.targetMerit objG conC t)
      (pt xa xb + s)).taylorDecrement 2) 1 {e | pt xa xb + s + e ∈ boxX} ≤ T₁ / 4 := by
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one,
      by rw [hxs]; exact h0S hya hyb⟩ fun d hd => ?_
    have hd1 : ‖d‖ ≤ 1 := mem_closedBall_zero_iff.1 hd.1
    have h2 := decr_two_le (pt xa xb + s) d t
    have h1 := lin_le (-(ya ^ 3 / 2 + (ya - yb / 16 - t))) ((ya - yb / 16 - t) / 16) hd1
    rw [← hΔ', hab0', hab1'] at h1
    have e : -g * -(ya ^ 3 / 2 + (ya - yb / 16 - t)) + -g * ((ya - yb / 16 - t) / 16) =
        g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 := by ring
    rw [e] at h1
    linarith
  refine callOut_one_step hq1 (by omega) (P := cexP) (fun j hj => ?_)
    hmemx (by rw [hxs]; exact hmemy) (by linarith) (taylorSum_merit hp _ t)
    ⟨0, forall_mem_image.2 fun _ _ => Constrained.targetMerit_nonneg⟩ ?_
    (d₀ := fun j => if j = 1 then pt (-1 / 2) (1 / 2) else w₀) ?_ ⟨1, by simp; omega, ?_⟩
    (dm := fun j => if j = 1 then pt (-g / 2) (-g / 2) else wm) ?_
    (d₁ := fun j => if j = 1 then pt (-g / 2) (-g / 2) else w₁) ?_ ?_
  · rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · rw [hT]; exact ⟨hT0, hT1⟩
    · rw [hT2 h2]; exact ⟨hT20, hT21⟩
  · -- the model decreases
    rw [Optimization.regularizedModel_def, taylorSum_merit hp, hxs, merit_eq, merit_eq]
    simp only [pt_zero, objG_pt]
    rw [hσ]
    have := reg_le hp (σ := cexP.σ₀) (by rw [hσ]; norm_num) hs1
    have h5 : ‖s‖ ^ 5 ≤ (|ya - xa| + |yb - xb|) ^ 5 := pow_le_pow_left₀ (norm_nonneg _) hsL 5
    rw [hσ] at this
    linarith
  · -- Step 1 at `x`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      refine isApprox_lin (a := -(xa ^ 3 / 2 + (xa - xb / 16 - t))) (b := (xa - xb / 16 - t) / 16)
        (fun d => by rw [decr, objG_pt]; simp only [pt_zero]) (h0S hxa hxb)
        (norm_pt_le hhalf' hhalf) (hS hxa hxb hhalf' hhalf) ?_
      rw [decr, objG_pt]
      simp only [pt_zero, pt_one]
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      linarith
    · simpa using hw₀
  · -- Step 1 fails at `x`
    simp only [↓reduceIte]
    rw [decr, objG_pt, hς, hT]
    simp only [pt_zero, pt_one]
    norm_num
    linarith
  · -- the model witnesses at `s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, hq2'⟩
    · simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [hς]
        refine isApprox_lin hΔm (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
          (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
        rw [hΔm, hab0, hab1]
        simp only [pt_zero, pt_one]
        ring_nf
        exact le_rfl
      · rw [hΔm, hς, hθ, hT]
        simp only [pt_zero, pt_one]
        have e : (-(ya ^ 3 / 2 + (ya - yb / 16 - t)) - regC p cexP.σ₀ s * (ya - xa)) * (-g / 2) +
            ((ya - yb / 16 - t) / 16 - regC p cexP.σ₀ s * (yb - xb)) * (-g / 2) =
            (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16 +
              regC p cexP.σ₀ s * (g * (ya - xa) + g * (yb - xb))) / 2 := by ring
        rw [e]
        norm_num
        linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      refine ⟨hwm, ?_⟩
      rw [hwm', hς, hθ, hT2 hq2']
      norm_num
      linarith
  · -- Step 1 at `x + s`: the witnesses
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, -⟩
    · simp only [↓reduceIte]
      rw [hς]
      refine isApprox_lin hΔ' (by rw [hxs]; exact h0S hya hyb) (norm_pt_le hgw hgw)
        (by rw [hxs]; exact hS hya hyb hgw hgw) ?_
      rw [hΔ', hab0', hab1']
      simp only [pt_zero, pt_one]
      ring_nf
      exact le_rfl
    · simpa using hw₁
  · -- Step 1 holds at `x + s`
    intro j hj
    rcases hj12 j hj with rfl | ⟨rfl, h2⟩
    · simp only [↓reduceIte]
      rw [hΔ', hς, hT]
      simp only [pt_zero, pt_one]
      have e : -(ya ^ 3 / 2 + (ya - yb / 16 - t)) * (-g / 2) + (ya - yb / 16 - t) / 16 * (-g / 2) =
          (g * (ya ^ 3 / 2 + (ya - yb / 16 - t)) - g * (ya - yb / 16 - t) / 16) / 2 := by ring
      rw [e]
      norm_num
      linarith
    · simp only [show (2 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
      rw [hw₁', hς, hT2 h2]
      norm_num
      have : 0 ≤ 1 / 10 ^ 6 * (|ya - xa| + |yb - xb|) ^ 3 / 2 := by positivity
      linarith

/-! ### The run -/

/-- The tolerances `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2`, `ε_j = 1` for `j ≥ 2`. -/
noncomputable def epsS (u : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else if j = 1 then 3 * u / 2 else 1

theorem epsS_zero {u : ℝ} : epsS u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [epsS]

theorem epsS_one {u : ℝ} : epsS u 1 = 3 * u / 2 := by simp [epsS]

theorem epsS_two {u : ℝ} : epsS u 2 = 1 := by simp [epsS]

theorem epsS_pos {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 < epsS u j := by
  unfold epsS; split_ifs <;> positivity

theorem epsS_le_one {u : ℝ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (j : ℕ) : epsS u j ≤ 1 := by
  unfold epsS; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]


section Run

variable (u : ℝ) (M : ℕ)

/-- The overshoot `E_k = (u³/2)(1 - k/(64(M + 1)))` of the `k`-th call below its target. -/
noncomputable def ovS (k : ℕ) : ℝ := u ^ 3 / 2 * (1 - k / (64 * (M + 1)))

/-- The targets `t_k = -ε₀ - u³ (k - 1) + u³ k (k - 1)/(128 (M + 1))`, so that
`t_{k+1} = t_k - 2 E_k`. -/
noncomputable def tgtS (k : ℕ) : ℝ :=
  -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) + u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1))

/-- The amount `f(x_{M+2}) - t_{M+1} = (3u/4)³/2` of the last call above its target. -/
noncomputable def finS : ℝ := 27 * u ^ 3 / 128

open Classical in
/-- The first coordinate of the point reached by the `k`-th call: `u` for `k ≤ M`, `-3u/4`
for the last call. -/
noncomputable def landA (k : ℕ) : ℝ := if k ≤ M then u else -3 * u / 4

open Classical in
/-- The value `f(x_{k+1}) - t_k`: `-E_k` for `k ≤ M`, `(3u/4)³/2` for the last call. -/
noncomputable def landF (k : ℕ) : ℝ := if k ≤ M then -ovS u M k else finS u

/-- The outer iterates: `x₁ = (0, 0)` and `x_{k+1} = (a_k, 16 (a_k - t_k - F_k))` for `k ≥ 1`,
so that `f(x_{k+1}) = t_k + F_k`. -/
noncomputable def xsS : ℕ → ℝ²
  | 0 => pt 0 0
  | k + 1 => if k = 0 then pt 0 0 else
      pt (landA u M k) (16 * (landA u M k - tgtS u M k - landF u M k))

/-- The Phase-2 sequences: iterates `xsS`, targets `tgtS`, radii `1`, and the `k`-th INNER call
makes one successful iteration from `x_k` to `x_{k+1}`. -/
noncomputable def runS : TPqpSeq 2 :=
  ⟨xsS u M, tgtS u M, fun _ _ => 1, fun k i => if i = 0 then xsS u M k else xsS u M (k + 1),
    fun _ => 1, fun _ _ => True⟩

end Run

section Facts

variable {u : ℝ} {M : ℕ}

theorem tgtS_one : tgtS u M 1 = -(u ^ 2 / 2 + u ^ 3 / 2) := by simp [tgtS]

/-- `t_{k+1} = t_k - 2 E_k`. -/
theorem tgtS_succ (k : ℕ) : tgtS u M (k + 1) = tgtS u M k - 2 * ovS u M k := by
  unfold tgtS ovS
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem xsS_one : xsS u M 1 = pt 0 0 := by simp [xsS]

theorem xsS_succ {k : ℕ} (hk : 1 ≤ k) :
    xsS u M (k + 1) = pt (landA u M k) (16 * (landA u M k - tgtS u M k - landF u M k)) := by
  simp [xsS, show k ≠ 0 by omega]

theorem objG_xsS_succ {k : ℕ} (hk : 1 ≤ k) :
    objG (xsS u M (k + 1)) = tgtS u M k + landF u M k := by
  rw [xsS_succ hk, objG_pt]; ring

theorem landA_of_le {k : ℕ} (hk : k ≤ M) : landA u M k = u := by simp [landA, hk]

theorem landF_of_le {k : ℕ} (hk : k ≤ M) : landF u M k = -ovS u M k := by simp [landF, hk]

theorem landA_last : landA u M (M + 1) = -3 * u / 4 := by simp [landA]

theorem landF_last : landF u M (M + 1) = finS u := by simp [landF]

/-- The iterates `x_{k+1}`, `1 ≤ k ≤ M`. -/
theorem xsS_mid {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    xsS u M (k + 1) = pt u (16 * (u - tgtS u M k + ovS u M k)) := by
  rw [xsS_succ hk1, landA_of_le hkM, landF_of_le hkM]; ring_nf

/-- The last iterate `x_{M+2}`. -/
theorem xsS_last : xsS u M (M + 1 + 1) =
    pt (-3 * u / 4) (16 * (-3 * u / 4 - tgtS u M (M + 1) - finS u)) := by
  rw [xsS_succ (by omega), landA_last, landF_last]

/-- `f(x_k) - t_k = E_{k-1}` at the start of the call `k ∈ [2, M + 1]`. -/
theorem objG_start {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    objG (xsS u M (k + 1)) - tgtS u M (k + 1) = ovS u M k := by
  rw [objG_xsS_succ hk1, landF_of_le hkM, tgtS_succ]; ring

variable (hu : 0 < u)
include hu

/-- `E_k ≤ u³/2`. -/
theorem ovS_le (k : ℕ) : ovS u M k ≤ u ^ 3 / 2 := by
  unfold ovS
  have : 0 ≤ (k : ℝ) / (64 * (M + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_k ≥ (63/64) u³/2` for `k ≤ M + 1`. -/
theorem le_ovS {k : ℕ} (hk : k ≤ M + 1) : 63 / 64 * (u ^ 3 / 2) ≤ ovS u M k := by
  unfold ovS
  have hN : (0 : ℝ) < 64 * (M + 1) := by positivity
  have : (k : ℝ) / (64 * (M + 1)) ≤ 1 / 64 := by
    rw [div_le_iff₀ hN]
    have : (k : ℝ) ≤ M + 1 := by exact_mod_cast hk
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- `E_{k-1} - E_k = u³/(128 (M + 1))`. -/
theorem ovS_sub (k : ℕ) : ovS u M k - ovS u M (k + 1) = u ^ 3 / (128 * (M + 1)) := by
  unfold ovS
  have : (64 * ((M : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `-ε₀ - u³ (k - 1) ≤ t_k ≤ -ε₀` for `k ∈ [1, M + 1]`. -/
theorem tgtS_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    -(u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) ≤ tgtS u M k ∧
      tgtS u M k ≤ -(u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold tgtS
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKM : (k : ℝ) ≤ M + 1 := by exact_mod_cast hkM
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k - 1)) / (128 * (M + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k - 1)) ≤ ((k : ℝ) - 1) * (128 * (M + 1)) := by nlinarith
    nlinarith
  constructor <;> linarith

end Facts

/-! ### The INNER calls of the run are ARqp-SC runs -/

/-- `‖r((a, b), t)‖² = (a²/2)² + (a - b/16 - t)²`. -/
theorem resid_sq_pt (a b t : ℝ) :
    Constrained.targetResidual objG conC t (pt a b) ^ 2 =
      (a ^ 2 / 2) ^ 2 + (a - b / 16 - t) ^ 2 := by
  rw [Constrained.targetResidual_sq, norm_conC, objG_pt, pt_zero]

/-- Bounds on a residual from its square. -/
theorem resid_bounds {R A F : ℝ} (hR : 0 ≤ R) (hsq : R ^ 2 = A ^ 2 + F ^ 2) (hA : 0 ≤ A)
    (hF : 0 ≤ F) : A ≤ R ∧ R ≤ A + F := by
  constructor <;> nlinarith [sq_nonneg (R - A), sq_nonneg (R - A - F), mul_nonneg hA hF]

/-- Step 1 fails at the start of the calls `k ≥ 2`. -/
theorem num_fail {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hE0 : 0 ≤ E)
    (hE2 : E ≤ u ^ 3 / 2) (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  nlinarith [pow_pos hu 3]

/-- The arithmetic of the middle calls. -/
theorem num_mid {u E E' R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E')
    (hE2' : E' ≤ u ^ 3 / 2) (hEE : u ^ 6 / 4 ≤ E - E') (hRlo : u ^ 2 / 2 ≤ R)
    (hRhi : R ≤ u ^ 2 / 2 + E) :
    1 / 2 * R * (3 * u / 2) < u ^ 3 / 2 + E + E / 16 ∧
    u ^ 4 / 8 + (-E') ^ 2 / 2 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    1 * (u ^ 3 / 2 + -E') - 1 * (-E') / 16 + 1 / 10 ^ 6 * (16 * (E + E')) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hS0 : 0 < E + E' := by linarith
  have hS1 : E + E' ≤ u ^ 3 := by linarith
  have hS4 : (E + E') ^ 4 ≤ (u ^ 3) ^ 4 := pow_le_pow_left₀ hS0.le hS1 4
  have hu6 : (u ^ 3) ^ 4 ≤ u ^ 6 / 1000 := by
    have : u ^ 6 ≤ 1 / 1000 := by
      have : u ^ 6 ≤ (1 / 200) ^ 6 := pow_le_pow_left₀ hu.le hu' 6
      linarith [show ((1 : ℝ) / 200) ^ 6 ≤ 1 / 1000 by norm_num]
    have e : (u ^ 3) ^ 4 = u ^ 6 * u ^ 6 := by ring
    rw [e]; nlinarith [pow_pos hu 6]
  refine ⟨?_, ?_, ?_⟩
  · have : R * u ≤ (u ^ 2 / 2 + u ^ 3 / 2) * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
    nlinarith
  · have e5 : (16 * (E + E')) ^ 5 = 1048576 * (E + E') ^ 4 * (E + E') := by ring
    have h1 : (E + E') ^ 4 * (E + E') ≤ u ^ 6 / 1000 * (E + E') :=
      mul_le_mul_of_nonneg_right (hS4.trans hu6) hS0.le
    have h2 : (u ^ 6 / 4) * (E + E') ≤ (E - E') * (E + E') :=
      mul_le_mul_of_nonneg_right hEE hS0.le
    have h3 : 0 < u ^ 6 * (E + E') := by positivity
    rw [e5]
    nlinarith
  · have e4 : (16 * (E + E')) ^ 4 = 65536 * (E + E') ^ 4 := by ring
    have h6 : u ^ 6 ≤ u ^ 3 / 1000 := by
      have : u ^ 3 ≤ 1 / 1000 := by nlinarith
      nlinarith
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    rw [e4]
    nlinarith

/-- The arithmetic of the last call. -/
theorem num_last {u E R : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200)
    (hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E) (hE2 : E ≤ u ^ 3 / 2) (hRlo : u ^ 2 / 2 ≤ R) :
    (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 5 / 120 <
      u ^ 4 / 8 + E ^ 2 / 2 ∧
    -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 +
      1 / 10 ^ 6 * (7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128)) ^ 4 / 24 ≤
      1 / 2 * R * (3 * u / 2) / 4 := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3 : u ^ 3 ≤ u / 40000 := by nlinarith
  have hL0 : 0 ≤ 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by nlinarith
  have hL1 : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by nlinarith
  have hL5 := pow_le_pow_left₀ hL0 hL1 5
  have hL4 := pow_le_pow_left₀ hL0 hL1 4
  have e5 : (30 * u) ^ 5 = 24300000 * u ^ 5 := by ring
  have e4 : (30 * u) ^ 4 = 810000 * u ^ 4 := by ring
  have hu5 : u ^ 5 ≤ u ^ 4 / 200 := by nlinarith [pow_pos hu 4]
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith [pow_pos hu 3]
  have hu6 : u ^ 6 ≤ u ^ 4 / 40000 := by nlinarith [pow_pos hu 4]
  have hE0 : 0 ≤ E := by linarith
  refine ⟨?_, ?_⟩
  · have e1 : (-3 * u / 4) ^ 4 / 8 + (27 * u ^ 3 / 128) ^ 2 / 2 =
        81 / 2048 * u ^ 4 + 729 / 32768 * u ^ 6 := by ring
    rw [e1]
    nlinarith
  · have e1 : -1 * ((-3 * u / 4) ^ 3 / 2 + 27 * u ^ 3 / 128) - -1 * (27 * u ^ 3 / 128) / 16 =
        27 / 2048 * u ^ 3 := by ring
    rw [e1]
    have : u ^ 2 / 2 * u ≤ R * u := mul_le_mul_of_nonneg_right hRlo hu.le
    nlinarith

/-- The order-`2` tolerance `T₂ = ‖r‖/2` dominates (`T₁/4 + σ₀ L³/2 ≤ T₂/16`). -/
theorem num_T2 {u R L : ℝ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hR : u ^ 2 / 2 ≤ R) (hL0 : 0 ≤ L)
    (hL : L ≤ 30 * u) :
    1 / 2 * R * (3 * u / 2) / 4 + 1 / 10 ^ 6 * L ^ 3 / 2 ≤ 1 / 2 * R * 1 / 16 := by
  have h3 : L ^ 3 ≤ (30 * u) ^ 3 := pow_le_pow_left₀ hL0 hL 3
  have e : (30 * u) ^ 3 = 27000 * u ^ 3 := by ring
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hRu : u * R ≤ R / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith [pow_pos hu 2]
  nlinarith

/-- The tolerances `(1/2) ‖r(x_k, t_k)‖ ε` of the `k`-th call (`β = 1/2`). -/
noncomputable abbrev callTol (u : ℝ) (M k : ℕ) : ℕ → ℝ := fun j =>
  1 / 2 * Constrained.targetResidual objG conC (tgtS u M k) (xsS u M k) * epsS u j

section Calls

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
include hu hu' hM hM1 hq1 hq2

omit hM in
/-- **The first call** (from `(0, 0)` with `f - t₁ = ε₀` to `(u, ·)` with `f - t₁ = -E₁`) is a
one-step ARqp-SC call. -/
theorem callOut_first {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M 1)) boxX p q cexP
      (callTol u M 1) (fun i => if i = 0 then xsS u M 1 else xsS u M (1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  set E := ovS u M 1 with hE
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu 1
  have ht : tgtS u M 1 = -e0 := tgtS_one
  have hx2 : xsS u M (1 + 1) = pt u (16 * (u + e0 + E)) := by
    rw [xsS_mid le_rfl hM1, ht, ← hE]; congr 1; ring
  have hR : Constrained.targetResidual objG conC (tgtS u M 1) (xsS u M 1) = e0 := by
    have hsq := resid_sq_pt 0 0 (tgtS u M 1)
    rw [← xsS_one (u := u) (M := M), ht] at hsq
    have h0 := Constrained.targetResidual_nonneg (f := objG) (c := conC) (t := tgtS u M 1)
      (x := xsS u M 1)
    rw [ht] at h0 ⊢
    have : 0 < e0 := by positivity
    nlinarith [sq_nonneg (Constrained.targetResidual objG conC (-e0) (xsS u M 1) - e0)]
  have hT : callTol u M 1 1 = 1 / 2 * e0 * (3 * u / 2) := by
    simp only [callTol, hR, epsS_one]
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 / 200 := by nlinarith
  have hu4 : u ^ 4 ≤ u ^ 3 / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hW0 : 0 ≤ 16 * (u + e0 + E) := by
    have : 0 ≤ E := by linarith
    positivity
  have hW1 : 16 * (u + e0 + E) ≤ 17 * u := by nlinarith
  have hL : |u - 0| + |16 * (u + e0 + E) - 0| ≤ 18 * u := by
    rw [sub_zero, sub_zero, abs_of_pos hu, abs_of_nonneg hW0]; linarith
  have hL0 : 0 ≤ |u - 0| + |16 * (u + e0 + E) - 0| := by positivity
  have hL5 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 5 ≤ (18 * u) ^ 5 :=
    pow_le_pow_left₀ hL0 hL 5
  have hL4 : (|u - 0| + |16 * (u + e0 + E) - 0|) ^ 4 ≤ (18 * u) ^ 4 :=
    pow_le_pow_left₀ hL0 hL 4
  have hFy : u - 16 * (u + e0 + E) / 16 - tgtS u M 1 = -E := by rw [ht]; ring
  have hFx : (0 : ℝ) - 0 / 16 - tgtS u M 1 = e0 := by rw [ht]; ring
  rw [xsS_one, hx2]
  have hT2 : 2 ≤ q → callTol u M 1 2 = 1 / 2 * e0 * 1 := fun _ => by
    simp only [callTol, hR, epsS_two]
  have he0lo : u ^ 2 / 2 ≤ e0 := by linarith
  refine callOut_cex hp hq1 hq2 (t := tgtS u M 1) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' he0lo hL0 (by linarith)) (by norm_num) (by norm_num)
    (by rw [abs_of_pos hu]; linarith) (by rw [abs_of_nonneg hW0]; linarith) (by linarith)
    (by positivity) (by nlinarith) (by rw [hFx]; positivity) le_rfl ?_ ?_ (Or.inl rfl) ?_ ?_
    (by linarith) (by linarith) ?_
  · rw [hFx]; nlinarith
  · rw [hFy, hFx]
    have h5 : (18 * u) ^ 5 = 1889568 * u ^ 5 := by ring
    have hE6 : E ^ 2 ≤ u ^ 6 / 4 := by nlinarith
    have he2 : e0 ^ 2 = u ^ 4 / 4 + u ^ 5 / 2 + u ^ 6 / 4 := by rw [he0]; ring
    have : (0 : ℝ) ^ 4 = 0 := by norm_num
    nlinarith
  · rw [hFy]; linarith
  · rw [hFy]; linarith
  · rw [hFy]
    have h4 : (18 * u) ^ 4 = 104976 * u ^ 4 := by ring
    nlinarith

omit hq1 hq2 in
/-- `u³ (M + 1) ≤ 1/32`, so `E_k - E_{k+1} = u³/(128 (M + 1)) ≥ u⁶/4`. -/
theorem ovS_sub_ge : u ^ 6 / 4 ≤ u ^ 3 / (128 * (M + 1)) := by
  have hN : (0 : ℝ) < 128 * (M + 1) := by positivity
  rw [le_div_iff₀ hN]
  have hu3 : u ^ 3 ≤ 1 / 64 := by nlinarith [pow_pos hu 2]
  have : u ^ 3 * ((M : ℝ) + 1) ≤ 1 / 32 := by nlinarith
  nlinarith [pow_pos hu 3]


/-- **The middle calls** `k = j + 1 ∈ [2, M]` (from `(u, ·)` with `f - t_k = E_j` to `(u, ·)`
with `f - t_k = -E_{j+1}`) are one-step ARqp-SC calls. -/
theorem callOut_mid {p : ℕ} (hp : 4 ≤ p) {j : ℕ} (hj1 : 1 ≤ j) (hjM : j + 1 ≤ M) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M (j + 1))) boxX p q cexP
      (callTol u M (j + 1)) (fun i => if i = 0 then xsS u M (j + 1) else xsS u M (j + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := ovS u M j with hE
  set E' := ovS u M (j + 1) with hE'
  set t := tgtS u M j with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu j
  have hE1' : 63 / 64 * (u ^ 3 / 2) ≤ E' := le_ovS hu (by omega)
  have hE2' : E' ≤ u ^ 3 / 2 := ovS_le hu (j + 1)
  have hEE : u ^ 6 / 4 ≤ E - E' := by rw [hE, hE', ovS_sub hu]; exact ovS_sub_ge hu hu' hM hM1
  have ht' : tgtS u M (j + 1) = t - 2 * E := tgtS_succ j
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hj1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M := by exact_mod_cast (show j ≤ M by omega)
      linarith
    nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : xsS u M (j + 1) = pt u A := by rw [xsS_mid hj1 (by omega)]
  have hx2 : xsS u M (j + 1 + 1) = pt u (A + 16 * (E + E')) := by
    rw [xsS_mid (by omega) hjM, ht', hA, ← hE']; congr 1; ring
  have hFx : u - A / 16 - tgtS u M (j + 1) = E := by rw [ht', hA]; ring
  have hFy : u - (A + 16 * (E + E')) / 16 - tgtS u M (j + 1) = -E' := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hR := resid_sq_pt u A (tgtS u M (j + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hR (by positivity)
    (by linarith)
  set R := Constrained.targetResidual objG conC (tgtS u M (j + 1)) (pt u A) with hRdef
  have hT : callTol u M (j + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, epsS_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hS0 : 0 ≤ E + E' := by linarith
  have hL : |u - u| + |A + 16 * (E + E') - A| = 16 * (E + E') := by
    rw [sub_self, abs_zero, zero_add, add_sub_cancel_left, abs_of_nonneg (by linarith)]
  obtain ⟨n1, n2, n3⟩ := num_mid hu hu' hE1 hE2 hE1' hE2' hEE hRlo hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (j + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, epsS_two, hx1]
  have hu3u : u ^ 3 ≤ u := pow_le_of_le_one hu.le (by linarith) (by norm_num)
  exact callOut_cex hp hq1 hq2 (t := tgtS u M (j + 1)) (g := 1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; linarith))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inl rfl) (by rw [hFy]; linarith) (by rw [hFy]; linarith)
    (by rw [sub_self]; linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **The last call** `k = M + 1` (from `(u, ·)` with `f - t_k = E_M` to `(-3u/4, ·)` with
`f - t_k = (3u/4)³/2`, a point where `∇μ(·, t_k)` vanishes in its first coordinate) is a
one-step ARqp-SC call. -/
theorem callOut_last {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M (M + 1))) boxX p q cexP
      (callTol u M (M + 1)) (fun i => if i = 0 then xsS u M (M + 1) else xsS u M (M + 1 + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  set E := ovS u M M with hE
  set t := tgtS u M M with ht
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ E := le_ovS hu (by omega)
  have hE2 : E ≤ u ^ 3 / 2 := ovS_le hu M
  have ht' : tgtS u M (M + 1) = t - 2 * E := tgtS_succ M
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hM1 (by omega)
  rw [← ht] at htlo hthi
  have hjM' : u ^ 3 * ((M : ℝ) - 1) ≤ 1 / 64 := by nlinarith [pow_pos hu 3]
  set A := 16 * (u - t + E) with hA
  have hx1 : xsS u M (M + 1) = pt u A := by rw [xsS_mid hM1 le_rfl]
  have hx2 : xsS u M (M + 1 + 1) =
      pt (-3 * u / 4) (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) := by
    rw [xsS_last, ht', hA, finS]; congr 1; ring
  have hFx : u - A / 16 - tgtS u M (M + 1) = E := by rw [ht', hA]; ring
  have hFy : -3 * u / 4 - (A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128)) / 16 -
      tgtS u M (M + 1) = 27 * u ^ 3 / 128 := by rw [ht', hA]; ring
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu3u : u ^ 3 ≤ u / 40000 := by nlinarith
  have hR := resid_sq_pt u A (tgtS u M (M + 1))
  rw [hFx] at hR
  obtain ⟨hRlo, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hR (by positivity)
    (by linarith)
  set R := Constrained.targetResidual objG conC (tgtS u M (M + 1)) (pt u A) with hRdef
  have hT : callTol u M (M + 1) (1 : ℕ) = 1 / 2 * R * (3 * u / 2) := by
    simp only [callTol, hx1, epsS_one, ← hRdef]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA1 : A ≤ 3 / 8 := by rw [hA]; linarith
  have hL : |-3 * u / 4 - u| + |A + 16 * (-(7 * u / 4) + E - 27 * u ^ 3 / 128) - A| =
      7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) := by
    rw [add_sub_cancel_left, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring
  obtain ⟨n2, n3⟩ := num_last hu hu' hE1 hE2 hRlo
  have n1 := num_fail hu hu' (by linarith) hE2 hRhi
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hT0 : 0 < 1 / 2 * R * (3 * u / 2) := by positivity
  have hT1 : 1 / 2 * R * (3 * u / 2) ≤ 1 := by
    have : R * u ≤ 1 * 1 := mul_le_mul (by linarith) (by linarith) hu.le zero_le_one
    linarith
  rw [hx1, hx2]
  have hT2 : 2 ≤ q → callTol u M (M + 1) 2 = 1 / 2 * R * 1 := fun _ => by
    rw [callTol, epsS_two, hx1]
  have hLb : 7 * u / 4 + 16 * (7 * u / 4 - E + 27 * u ^ 3 / 128) ≤ 30 * u := by linarith
  exact callOut_cex hp hq1 hq2 (t := tgtS u M (M + 1)) (g := -1) hT hT2 (by positivity)
    (by linarith) (num_T2 hu hu' hRlo (by rw [hL]; linarith) (by rw [hL]; exact hLb))
    (by rw [abs_of_pos hu]; linarith)
    (by rw [abs_of_nonneg hA0]; linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_le]; constructor <;> linarith) (by rw [hL]; linarith)
    hT0 hT1 (by rw [hFx]; linarith) hu.le (by rw [hFx]; exact n1)
    (by rw [hFy, hFx, hL]; exact n2) (Or.inr rfl) (by rw [hFy]; ring_nf; exact le_rfl)
    (by rw [hFy]; linarith) (by linarith) (by linarith) (by rw [hFy, hL]; exact n3)

/-- **Every INNER call `k ∈ [1, M + 1]` of the run is a one-step ARqp-SC call.** -/
theorem callOut_run {p : ℕ} (hp : 4 ≤ p) {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    IsARqpSCCallOut (Constrained.targetMerit objG conC (tgtS u M k)) boxX p q cexP
      (callTol u M k) (fun i => if i = 0 then xsS u M k else xsS u M (k + 1)) 1
      (fun _ => True) (fun _ => 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact callOut_first hu hu' hM1 hq1 hq2 hp
  rcases Nat.lt_or_ge j M with hjM | hjM
  · exact callOut_mid hu hu' hM hM1 hq1 hq2 hp hj hjM
  · obtain rfl : j = M := by omega
    exact callOut_last hu hu' hM hM1 hq1 hq2 hp

end Calls

/-! ### The outer run -/

section Outer

variable {u : ℝ} {M : ℕ} (hu : 0 < u) (hu' : u ≤ 1 / 200) (hM : u ^ 3 * M ≤ 1 / 64)
  (hM1 : 1 ≤ M) {q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)

include hu hu' hM in
/-- The iterates `x_k`, `k ∈ [1, M + 2]`, lie in `[-1/2, 1/2]²`, hence in `X`. -/
theorem xsS_mem {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 2) : xsS u M k ∈ boxX := by
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have hu3p : 0 < u ^ 3 := by positivity
  have hu3s : u ^ 3 ≤ 1 / 1000 := by nlinarith
  have hu2p : 0 ≤ u ^ 2 := by positivity
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [xsS_one]; exact pt_mem (by norm_num) (by norm_num)
  have hE1 : 63 / 64 * (u ^ 3 / 2) ≤ ovS u M j := le_ovS hu (by omega)
  have hE2 : ovS u M j ≤ u ^ 3 / 2 := ovS_le hu j
  obtain ⟨htlo, hthi⟩ := tgtS_mem hu (u := u) (M := M) hj (by omega)
  have hjM' : u ^ 3 * ((j : ℝ) - 1) ≤ 1 / 64 := by
    have : ((j : ℝ) - 1) ≤ M := by
      have : (j : ℝ) ≤ M + 1 := by exact_mod_cast (show j ≤ M + 1 by omega)
      linarith
    nlinarith
  rcases Nat.lt_or_ge j (M + 1) with hjM | hjM
  · rw [xsS_mid hj (by omega)]
    exact pt_mem (by rw [abs_of_pos hu]; linarith)
      (by rw [abs_le]; constructor <;> linarith)
  · obtain rfl : j = M + 1 := by omega
    rw [xsS_last, finS]
    exact pt_mem (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)

omit hM hM1 in
include hu hu' in
/-- `θ ε₀ ≤ u²/4 + u³/4 ≤ 9u²/32` for `θ = 1/2`. -/
theorem theta_eps_le' : 1 / 2 * epsS u 0 ≤ 9 * u ^ 2 / 32 := by
  rw [epsS_zero]; nlinarith [pow_pos hu 2]

include hu hu' in
/-- `‖r(x_{k+1}, t_k)‖ ≥ θ ε₀` for every call `k ∈ [1, M + 1]`: no call is in `𝒦_a`. -/
theorem resid_end_ge {k : ℕ} (hk1 : 1 ≤ k) :
    1 / 2 * epsS u 0 ≤ Constrained.targetResidual objG conC (tgtS u M k) (xsS u M (k + 1)) := by
  have hθ := theta_eps_le' hu hu'
  have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M k)
    (x := xsS u M (k + 1))
  have h' : ‖conC (xsS u M (k + 1))‖ = landA u M k ^ 2 / 2 := by
    rw [norm_conC, xsS_succ hk1, pt_zero]
  have hA2 : 9 * u ^ 2 / 32 ≤ landA u M k ^ 2 / 2 := by
    unfold landA; split_ifs
    · nlinarith [pow_pos hu 2]
    · nlinarith [pow_pos hu 2]
  linarith

include hu hu' in
/-- `‖r(x_k, t_k)‖ ≥ θ ε₀` at the start of every call `k ∈ [1, M + 1]`. -/
theorem resid_start_ge {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M + 1) :
    1 / 2 * epsS u 0 ≤ Constrained.targetResidual objG conC (tgtS u M k) (xsS u M k) := by
  have hθ := theta_eps_le' hu hu'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := Constrained.abs_sub_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (0 + 1))
      (x := xsS u M (0 + 1))
    have e : objG (xsS u M (0 + 1)) - tgtS u M (0 + 1) = epsS u 0 := by
      rw [zero_add, xsS_one, objG_pt, tgtS_one, epsS_zero]; ring
    rw [e, abs_of_pos (epsS_pos hu 0)] at h
    have := epsS_pos hu 0
    linarith
  · have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (j + 1))
      (x := xsS u M (j + 1))
    have h' : ‖conC (xsS u M (j + 1))‖ = u ^ 2 / 2 := by
      rw [norm_conC, xsS_mid hj (by omega), pt_zero]
    nlinarith [pow_pos hu 2]

include hu hu' in
/-- No outer iteration is in `𝒦_a`. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) : ¬ (runS u M).IsKa objG conC (1 / 2) (epsS u) k :=
  not_lt.2 (resid_end_ge hu hu' hk1)

include hu hu' in
/-- The outer iterations `k ∈ [1, M]` are in `𝒦_b`. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    (runS u M).IsKb objG conC (1 / 2) (epsS u) k := by
  refine ⟨resid_end_ge hu hu' hk1, ?_⟩
  change objG (xsS u M (k + 1)) < tgtS u M k
  rw [objG_xsS_succ hk1, landF_of_le hkM]
  have := le_ovS hu (M := M) (k := k) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

include hu in
/-- The outer iteration `M + 1` is not in `𝒦_b`: `f(x_{M+2}) > t_{M+1}`. -/
theorem not_isKb_last : ¬ (runS u M).IsKb objG conC (1 / 2) (epsS u) (M + 1) := by
  intro h
  have h2 := h.2
  change objG (xsS u M (M + 1 + 1)) < tgtS u M (M + 1) at h2
  rw [objG_xsS_succ (by omega), landF_last, finS] at h2
  have : 0 < u ^ 3 := by positivity
  linarith

include hu hu' hM hq1 in
/-- **(14.3.34) fails at `(x_{k+1}, t_{k+1})`** for `k ∈ [1, M]`: along `-e₁` the decrease is
`u³/2 + E_k > ε₁ ‖r(x_{k+1}, t_{k+1})‖`. -/
theorem not_meritCrit_new {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ meritCrit objG conC boxX q (epsS u) (tgtS u M (k + 1)) (xsS u M (k + 1)) (fun _ => 1) := by
  intro h
  have h1 := h 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := xsS_mem hu hu' hM (k := k + 1) (by omega) (by omega)
  have hx : xsS u M (k + 1) = pt u (16 * (u - tgtS u M k + ovS u M k)) := xsS_mid hk1 hkM
  have hS : pt (-1) 0 ∈ {d | xsS u M (k + 1) + d ∈ boxX} := by
    simp only [mem_ofPred_eq]
    rw [hx] at hmem ⊢
    rw [pt_add]
    simp only [pt_zero, pt_one, add_zero]
    obtain ⟨-, h2⟩ := hmem
    simp only [pt_one] at h2
    exact pt_mem (by rw [abs_le]; constructor <;> linarith) h2
  have hd : pt (-1) 0 ∈ closedBall (0 : ℝ²) 1 := by
    rw [mem_closedBall_zero_iff]
    exact (norm_pt_le_add _ _).trans (by norm_num)
  have hlow := Optimization.taylorDecrement_le_taylorMeasure
    (ftaylorSeries ℝ (Constrained.targetMerit objG conC (tgtS u M (k + 1))) (xsS u M (k + 1))) 1
    (δ := 1) (d := pt (-1) 0) ⟨hd, hS⟩
  have hx0 : xsS u M (k + 1) 0 = u := by rw [hx, pt_zero]
  rw [decr, objG_start hk1 hkM] at hlow
  simp only [pt_zero, pt_one, hx0] at hlow
  rw [epsS_one] at h1
  have hE1 := le_ovS hu (M := M) (k := k) (by omega)
  have hE2 := ovS_le hu (M := M) k
  have hsq := resid_sq_pt u (16 * (u - tgtS u M k + ovS u M k)) (tgtS u M (k + 1))
  have hF : u - 16 * (u - tgtS u M k + ovS u M k) / 16 - tgtS u M (k + 1) = ovS u M k := by
    rw [tgtS_succ]; ring
  rw [hF] at hsq
  obtain ⟨-, hRhi⟩ := resid_bounds Constrained.targetResidual_nonneg hsq (by positivity)
    (by linarith)
  rw [← hx] at hRhi
  have hu2 : u ^ 2 ≤ u / 200 := by nlinarith
  have : 3 * u / 2 * Constrained.targetResidual objG conC (tgtS u M (k + 1)) (xsS u M (k + 1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + ovS u M k) := by gcongr
  have : u * ovS u M k ≤ u * (u ^ 3 / 2) := mul_le_mul_of_nonneg_left hE2 hu.le
  nlinarith [pow_pos hu 3, pow_pos hu 4]

include hu hu' hM hq2 in
/-- The third test of (14.3.32) holds at `(x_{M+2}, t_{M+1})`: the gradient of
`μ(·, t_{M+1})` there is `(0, -(3u/4)³/32)`. -/
theorem meritCrit_last :
    meritCrit objG conC boxX q (epsS u) (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) (fun _ => 1) := by
  intro j hj
  have hj12 : j = 1 ∨ j = 2 := by have := Finset.mem_Icc.1 hj; omega
  simp only [one_pow, mul_one]
  have hx := xsS_last (u := u) (M := M)
  set B := 16 * (-3 * u / 4 - tgtS u M (M + 1) - finS u)
  have hF : -3 * u / 4 - B / 16 - tgtS u M (M + 1) = finS u := by ring
  have h0 : (0 : ℝ²) ∈ {d | xsS u M (M + 1 + 1) + d ∈ boxX} := by
    simpa using xsS_mem hu hu' hM (k := M + 1 + 1) (by omega) le_rfl
  have hup := measure_lin_le (Δ := (ftaylorSeries ℝ (Constrained.targetMerit objG conC
    (tgtS u M (M + 1))) (xsS u M (M + 1 + 1))).taylorDecrement 1)
    (a := -((-3 * u / 4) ^ 3 / 2 + finS u)) (b := finS u / 16)
    (fun d => by rw [decr, hx, objG_pt, pt_zero, hF]) h0
  have h := Constrained.norm_le_targetResidual (f := objG) (c := conC) (t := tgtS u M (M + 1))
    (x := xsS u M (M + 1 + 1))
  have h' : ‖conC (xsS u M (M + 1 + 1))‖ = 9 * u ^ 2 / 32 := by
    rw [norm_conC, hx, pt_zero]; ring
  have e : -((-3 * u / 4) ^ 3 / 2 + finS u) = 0 := by rw [finS]; ring
  rw [e, abs_zero, zero_add, abs_of_pos (by rw [finS]; positivity)] at hup
  have hR : 9 * u ^ 2 / 32 ≤
      Constrained.targetResidual objG conC (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) := by linarith
  rcases hj12 with rfl | rfl
  · refine (show Optimization.taylorMeasure _ 1 1 _ ≤ _ from hup).trans ?_
    rw [epsS_one, finS]
    have : 3 * u / 2 * (9 * u ^ 2 / 32) ≤ 3 * u / 2 *
        Constrained.targetResidual objG conC (tgtS u M (M + 1)) (xsS u M (M + 1 + 1)) := by
      gcongr
    norm_num
    nlinarith [pow_pos hu 3]
  · have h2 : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit objG conC
        (tgtS u M (M + 1))) (xsS u M (M + 1 + 1))) 2 1 {d | xsS u M (M + 1 + 1) + d ∈ boxX} ≤
        finS u / 16 := by
      refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self zero_le_one, h0⟩
        fun d hd => (decr_two_le _ d _).trans ?_
      exact (Optimization.le_decrementMeasure
        (Optimization.bddAbove_taylorDecrement _ 1 1 _) hd).trans hup
    refine h2.trans ?_
    rw [epsS_two, finS]
    norm_num
    nlinarith [pow_pos hu 3]

include hu hu' in
/-- Phase 2 stops at `M + 1` (case (c)). -/
theorem stop_last : (runS u M).Stop objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  Or.inl ⟨not_isKa hu hu' (by omega), not_isKb_last hu⟩

include hu hu' hM hq1 in
/-- Phase 2 does not stop at `k ∈ [1, M]`. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ¬ (runS u M).Stop objG conC boxX q (1 / 2) (epsS u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu' hk1 hkM)
  · exact not_meritCrit_new hu hu' hM hq1 hk1 hkM hm

include hu hu' hM hq1 in
/-- Phase 2 does not stop before `M + 1`. -/
theorem before_last : (runS u M).Before objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  fun _ hj1 hjM => not_stop hu hu' hM hq1 hj1 (by omega)

include hu hu' in
/-- Every outer iteration reached is at most `M + 1`. -/
theorem le_of_before {k : ℕ} (h : (runS u M).Before objG conC boxX q (1 / 2) (epsS u) k) :
    k ≤ M + 1 := by
  by_contra hk
  exact h (M + 1) (by omega) (by omega) (stop_last hu hu')

include hu hu' hM hq1 in
/-- Phase 2 terminates at the outer iteration `M + 1`. -/
theorem isEnd : (runS u M).IsEnd objG conC boxX q (1 / 2) (epsS u) (M + 1) :=
  ⟨by omega, stop_last hu hu', before_last hu hu' hM hq1⟩

include hu hu' hM hq1 in
/-- `M + 1` is the only termination index. -/
theorem isEnd_iff {k : ℕ} : (runS u M).IsEnd objG conC boxX q (1 / 2) (epsS u) k ↔ k = M + 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ isEnd hu hu' hM hq1⟩
  have hle := le_of_before hu hu' h.2.2
  rcases Nat.lt_or_ge k (M + 1) with hlt | hge
  · exact absurd h.2.1 (not_stop hu hu' hM hq1 h.1 (by omega))
  · omega

include hu hu' hM hM1 hq1 hq2 in
/-- **The sequences form a Phase-2 run of TPqp-GC** (`θ = β = 1/2`). -/
theorem isTPqpGCPhase2 {p : ℕ} (hp : 4 ≤ p) :
    IsTPqpGCPhase2 objG conC boxX q (1 / 2) (1 / 2) (epsS u) (pt 0 0) (runS u M) := by
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc1 : ‖conC (pt 0 0)‖ = 0 := by rw [norm_conC]; simp
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, fun j _ => epsS_pos hu j,
    fun j _ => epsS_le_one hu hu7 j, pt_mem (by norm_num) (by norm_num),
    by rw [hc1]; exact (mul_pos (by norm_num) (epsS_pos hu 0)).le, xsS_one (u := u) (M := M), ?_,
    fun k hk1 hk => xsS_mem hu hu' hM (by omega) (by have := le_of_before hu hu' hk; omega),
    fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, fun k hk1 hk => ?_, fun k _ _ => by simp [runS],
    fun k _ _ => by simp [runS], fun k hk1 hk i hi => ?_, fun k hk1 hk i hi => ?_,
    fun k hk1 _ ha => absurd ha (not_isKa hu hu' hk1), fun k hk1 hk hb => ?_⟩
  · change tgtS u M 1 = objG (pt 0 0) - √(epsS u 0 ^ 2 - ‖conC (pt 0 0)‖ ^ 2)
    rw [hc1, tgtS_one, objG_pt, epsS_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · have hkM := le_of_before hu hu' hk
    rcases Nat.lt_or_ge k (M + 1) with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu' hk1 (by omega)).2)
    · obtain rfl : k = M + 1 := by omega
      exact Or.inr (Or.inr (meritCrit_last hu hu' hM hq2))
  · change i < 1 at hi
    obtain rfl : i = 0 := by omega
    exact IsARqpSCCallOut.antitone
      (callOut_run hu hu' hM hM1 hq1 hq2 hp hk1 (le_of_before hu hu' hk)) 0 one_pos
  · change i < 1 at hi
    obtain rfl : i = 0 := by omega
    exact resid_start_ge hu hu' hk1 (le_of_before hu hu' hk)
  · have hkM := le_of_before hu hu' hk
    have hlt : k ≤ M := by
      by_contra h
      exact not_isKb_last hu ((show k = M + 1 by omega) ▸ hb)
    change tgtS u M (k + 1) = 2 * objG (xsS u M (k + 1)) - tgtS u M k
    rw [objG_xsS_succ hk1, landF_of_le hlt, tgtS_succ]
    ring

include hu hu' hM hM1 hq1 hq2 in
/-- **The Phase-2 INNER calls are ARqp-SC runs** (`IsARqpSCPhase2Calls`, `β = 1/2`). -/
theorem isARqpSCPhase2Calls {p : ℕ} (hp : 4 ≤ p) :
    IsARqpSCPhase2Calls objG conC boxX p q cexP (1 / 2) (1 / 2) (epsS u) (runS u M) :=
  fun _ hk1 hk => callOut_run hu hu' hM hM1 hq1 hq2 hp hk1 (le_of_before hu hu' hk)

include hu hu' hM hM1 hq1 hq2 in
/-- **The run is a TPqp-GC run** (`algorithm_14_3_2`, `θ = β = 1/2`, any `β₁ ∈ (0, 1)`): Phase 1
(LENq-SC on `ν`) stops at once at the feasible `x₀ = (0, 0)`. -/
theorem algorithm_14_3_2_run {p : ℕ} (hp : 4 ≤ p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁1 : β₁ < 1) :
    algorithm_14_3_2 objG conC boxX q (1 / 2) β₁ (1 / 2) (epsS u) (pt 0 0) (fun _ => pt 0 0)
      (fun _ _ => 1) 0 (runS u M) := by
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc1 : ‖conC (pt 0 0)‖ = 0 := by rw [norm_conC]; simp
  have hlen0 : lenStop conC boxX q (phase1Tol (1 / 2) (epsS u)) (fun _ => pt 0 0)
      (fun _ _ => 1) 0 := Or.inl (by
        rw [hc1, phase1Tol_zero]; exact (mul_pos (by norm_num) (epsS_pos hu 0)).le)
  refine ⟨rfl, ⟨pt_mem (by norm_num) (by norm_num), fun j _ => ?_, fun j _ => ?_, hβ₁, hβ₁1,
    by rw [hc1]; norm_num, fun k _ h => absurd hlen0 (h 0 (by omega)),
    fun k _ h => absurd hlen0 (h 0 (by omega)), fun k _ h => absurd hlen0 (h 0 (by omega))⟩,
    ⟨hlen0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
    fun _ => isTPqpGCPhase2 hu hu' hM hM1 hq1 hq2 hp⟩
  · unfold phase1Tol; split_ifs
    · exact mul_pos (by norm_num) (epsS_pos hu 0)
    · exact epsS_pos hu j
  · unfold phase1Tol; split_ifs
    · nlinarith [epsS_le_one hu hu7 0, epsS_pos hu 0]
    · exact epsS_le_one hu hu7 j

include hu hu' hM hM1 hq1 hq2 in
/-- **The run is a TPqp-GC run whose INNER calls are ARqp-SC runs** (`IsTPqpGCARqpSCRun`). -/
theorem isTPqpGCARqpSCRun {p : ℕ} (hp : 4 ≤ p) {β₁ : ℝ} (hβ₁ : 0 < β₁) (hβ₁1 : β₁ < 1)
    (nF₁ nD₁ : ℕ → ℕ) :
    IsTPqpGCARqpSCRun objG conC boxX p q cexP (1 / 2) β₁ (1 / 2) (epsS u) (pt 0 0)
      (fun _ => pt 0 0) (fun _ _ => 1) 0 (runS u M) nF₁ nD₁ :=
  ⟨algorithm_14_3_2_run hu hu' hM hM1 hq1 hq2 hp hβ₁ hβ₁1, fun k hk1 hk0 => absurd hk1 (by omega),
    fun _ => isARqpSCPhase2Calls hu hu' hM hM1 hq1 hq2 hp⟩

end Outer

/-- Every INNER call makes one successful iteration. -/
theorem succCount_runS (u : ℝ) (M j : ℕ) : (runS u M).succCount j = 1 := by
  classical
  unfold TPqpSeq.succCount
  rw [Finset.card_eq_one]
  refine ⟨0, Finset.eq_singleton_iff_unique_mem.2
    ⟨Finset.mem_filter.2 ⟨by simp [runS], trivial⟩, fun x hx => ?_⟩⟩
  have := (Finset.mem_filter.1 hx).1
  simpa [runS] using this

/-- `#F(k) = #D(k) = k + 1`. -/
theorem funEvals_runS (u : ℝ) (M k : ℕ) : (runS u M).funEvals k = k + 1 ∧
    (runS u M).derivEvals k = k + 1 := by
  have hs : ∀ j, (runS u M).succCount j = 1 := succCount_runS u M
  constructor
  · unfold TPqpSeq.funEvals
    simp [runS, add_comm]
  · unfold TPqpSeq.derivEvals
    simp [hs, add_comm]


/-! ### The data satisfy the assumptions of Theorem 14.3.9 -/

/-- `f` is smooth. -/
theorem contDiff_objG : ContDiff ℝ ⊤ objG :=
  (contDiff_piLp_apply (p := 2)).sub ((contDiff_piLp_apply (p := 2)).div_const 16)

/-- f.B.Fb on `ℱ_1`: `-2 ≤ f ≤ 2` on `X`. -/
theorem assumptionBFb_objG : Chapter07.AssumptionBFb objG conC boxX 1 (-2) 2 := by
  intro x hx
  obtain ⟨⟨h0, h1⟩, -⟩ := hx
  have := abs_le.1 h0
  have := abs_le.1 h1
  simp only [objG]
  constructor <;> linarith

/-- f.D1pLB.X and c.D1pLB.X hold on `X₀ = B(0, 2)` for every `p`. -/
theorem assumptionD1pLBX_objG (p : ℕ) :
    (∃ L B : ℕ → ℝ, AssumptionD1pLBX objG boxX (ball 0 2) p L B) ∧
      ∃ L B : ℕ → ℝ, AssumptionCD1pLBX conC boxX (ball 0 2) p L B :=
  ⟨exists_assumptionD1pLBX_ball (contDiff_objG.of_le le_top) boxX_subset_ball p,
    (assumptionD1pLBX p).2⟩

/-! ### The order -/

/-- `ε^{-c} ≤ B^{a c}` when `ε ≥ B^{-a}` (`ε, B > 0`, `c ≥ 0`). -/
theorem rpow_neg_le {ε B a c : ℝ} (hε : 0 < ε) (hB : 0 < B) (h : (B ^ a)⁻¹ ≤ ε) (hc : 0 ≤ c) :
    ε ^ (-c) ≤ B ^ (a * c) := by
  have hBa : 0 < B ^ a := Real.rpow_pos_of_pos hB a
  have hi : ε⁻¹ ≤ B ^ a := by
    have := inv_anti₀ (inv_pos.2 hBa) h
    rwa [inv_inv] at this
  rw [Real.rpow_neg hε.le, ← Real.inv_rpow hε.le, Real.rpow_mul hB.le]
  exact Real.rpow_le_rpow (inv_pos.2 hε).le hi hc

/-- **One term of the printed order**: if `ε₀ ≥ B^{-5}`, `ε_j ≥ B^{-a}` (`B ≥ 1`) and `π ≥ 1`
with `5(π - 1) + a π ≤ 7`, then `ε₀^{1-π} ε_j^{-π} ≤ B^7`. -/
theorem term_le_pow {ε₀ εj B a π : ℝ} (h0 : 0 < ε₀) (hj : 0 < εj) (hB : 1 ≤ B)
    (h0B : (B ^ (5 : ℝ))⁻¹ ≤ ε₀) (hjB : (B ^ a)⁻¹ ≤ εj) (hπ : 1 ≤ π)
    (hπ7 : 5 * (π - 1) + a * π ≤ 7) : ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (7 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have h1 : ε₀ ^ (1 - π) ≤ B ^ (5 * (π - 1)) := by
    rw [show 1 - π = -(π - 1) by ring]; exact rpow_neg_le h0 hB0 h0B (by linarith)
  have h2 : εj ^ (-π) ≤ B ^ (a * π) := rpow_neg_le hj hB0 hjB (by linarith)
  calc ε₀ ^ (1 - π) * εj ^ (-π) ≤ B ^ (5 * (π - 1)) * B ^ (a * π) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hj.le _) (Real.rpow_nonneg hB0.le _)
    _ = B ^ (5 * (π - 1) + a * π) := (Real.rpow_add hB0 _ _).symm
    _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB hπ7

/-- **The printed orders along the run's tolerances**: for `u = 1/(4N⁵)` (`N ≥ 1`), `q ∈ {1, 2}`
and `p ≥ q + 3`, both orders of Theorem 14.3.9 with the ARqp-SC exponents `j(p+1)/p` are at
most `128 N¹⁴` (`B = 2N²`, `ε₀ ≥ B^{-5}`, `ε₁ ≥ B^{-3}`, `ε₂ = 1`). -/
theorem order_le_pow {p q N : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hpq : q + 3 ≤ p) (hN : 1 ≤ N) :
    tpqpOrderF (Chapter12.arqpPiOf False p) q (epsS (1 / (4 * N ^ 5))) ≤ 128 * (N : ℝ) ^ 14 ∧
      tpqpOrderD (Chapter12.arqpPiOf False p) q (epsS (1 / (4 * N ^ 5))) ≤
        128 * (N : ℝ) ^ 14 := by
  set u : ℝ := 1 / (4 * N ^ 5) with hu_def
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set B : ℝ := 2 * (N : ℝ) ^ 2 with hB_def
  have hB1 : 1 ≤ B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hB7 : B ^ (7 : ℝ) = 128 * (N : ℝ) ^ 14 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hB_def]; ring
  have hu : 0 < u := by positivity
  have hε0 : (B ^ (5 : ℝ))⁻¹ ≤ epsS u 0 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, epsS_zero]
    have : (B ^ 5)⁻¹ = u ^ 2 / 2 := by rw [hB_def, hu_def]; field_simp; ring
    rw [this]; have := pow_pos hu 3; linarith
  have hε1 : (B ^ (3 : ℝ))⁻¹ ≤ epsS u 1 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, epsS_one, hB_def, hu_def]
    rw [inv_le_comm₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [pow_pos hNp 5, pow_pos hNp 6]
  have hπ : ∀ l ∈ Finset.Icc 1 q, 1 ≤ Chapter12.arqpPiOf False p l := fun l hl => by
    have := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast this.1
    simp only [Chapter12.arqpPiOf, ite_false]
    rw [le_div_iff₀ hp0]; nlinarith
  have hterm : ∀ l ∈ Finset.Icc 1 q, epsS u 0 ^ (1 - Chapter12.arqpPiOf False p l) *
      epsS u l ^ (-Chapter12.arqpPiOf False p l) ≤ B ^ (7 : ℝ) := fun l hl => by
    have hl := Finset.mem_Icc.1 hl
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hpq' : (q : ℝ) + 3 ≤ p := by exact_mod_cast hpq
    rcases (show l = 1 ∨ l = 2 by omega) with rfl | rfl
    · refine term_le_pow (epsS_pos hu 0) (epsS_pos hu 1) hB1 hε0 hε1
        (hπ 1 (Finset.mem_Icc.2 ⟨le_rfl, hq1⟩)) ?_
      simp only [Chapter12.arqpPiOf, ite_false, Nat.cast_one, one_mul]
      have hp4 : (4 : ℝ) ≤ p := by have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
                                   linarith
      have : ((p : ℝ) + 1) / p ≤ 5 / 4 := by rw [div_le_iff₀ hp0]; linarith
      linarith
    · have hq2' : (q : ℝ) = 2 := by exact_mod_cast (show q = 2 by omega)
      have h2 : epsS u 2 = 1 := epsS_two
      rw [h2, Real.one_rpow, mul_one]
      have hπ2 : Chapter12.arqpPiOf False p 2 ≤ 12 / 5 := by
        simp only [Chapter12.arqpPiOf, ite_false]
        rw [div_le_iff₀ hp0]; push_cast; linarith
      have hπ1 := hπ 2 (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩)
      calc epsS u 0 ^ (1 - Chapter12.arqpPiOf False p 2)
          ≤ B ^ (5 * (Chapter12.arqpPiOf False p 2 - 1)) := by
            rw [show 1 - Chapter12.arqpPiOf False p 2 =
              -(Chapter12.arqpPiOf False p 2 - 1) by ring]
            exact rpow_neg_le (epsS_pos hu 0) hB0 hε0 (by linarith)
        _ ≤ B ^ (7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have h0 : (epsS u 0)⁻¹ ≤ B ^ (7 : ℝ) := by
    have := rpow_neg_le (c := 1) (epsS_pos hu 0) hB0 hε0 zero_le_one
    rw [Real.rpow_neg_one, mul_one] at this
    exact this.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num))
  rw [← hB7]
  exact ⟨Chapter12.finMax_le h0 hterm,
    Chapter12.finMax_le (Real.rpow_nonneg hB0.le _) hterm⟩

/-- **The parameters for a constant `C`**: `N = ⌈128 |C|⌉ + 3`, so that `C · 128 N¹⁴ < N¹⁵` and
the tolerances `ε₀, ε₁ ≤ C⁻¹` vanish as `C` grows. -/
theorem exists_params (C : ℝ) : ∃ N : ℕ, 3 ≤ N ∧ C * (128 * (N : ℝ) ^ 14) < (N : ℝ) ^ 15 ∧
    (1 ≤ C → epsS (1 / (4 * N ^ 5)) 0 ≤ C⁻¹ ∧ epsS (1 / (4 * N ^ 5)) 1 ≤ C⁻¹) := by
  refine ⟨⌈128 * |C|⌉₊ + 3, by omega, ?_, fun hC => ?_⟩
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hNp : (0 : ℝ) < N := by linarith [abs_nonneg C]
    have h14 : (0 : ℝ) < (N : ℝ) ^ 14 := by positivity
    calc C * (128 * (N : ℝ) ^ 14) ≤ |C| * (128 * (N : ℝ) ^ 14) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = 128 * |C| * (N : ℝ) ^ 14 := by ring
      _ < N * (N : ℝ) ^ 14 := mul_lt_mul_of_pos_right (by linarith) h14
      _ = (N : ℝ) ^ 15 := by ring
  · set N : ℕ := ⌈128 * |C|⌉₊ + 3
    have hN : 128 * |C| + 2 < (N : ℝ) := by
      have := Nat.le_ceil (128 * |C|); push_cast [N]; linarith
    have hCN : C ≤ N := by linarith [le_abs_self C, abs_nonneg C]
    have hNp : (1 : ℝ) ≤ N := by linarith
    set u : ℝ := 1 / (4 * N ^ 5)
    have hu : 0 < u := by positivity
    have hN5 : (N : ℝ) ≤ (N : ℝ) ^ 5 := le_self_pow₀ hNp (by norm_num)
    have hu1 : u ≤ 1 := by
      apply div_le_one_of_le₀ (by nlinarith) (by positivity)
    have hNinv : 3 * u / 2 ≤ (N : ℝ)⁻¹ := by
      have : 3 * u / 2 = 3 / (8 * (N : ℝ) ^ 5) := by simp only [u]; field_simp; ring
      rw [this, div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    have hCi : (N : ℝ)⁻¹ ≤ C⁻¹ := inv_anti₀ (by linarith) hCN
    have hε1 : epsS u 1 ≤ C⁻¹ := by rw [epsS_one]; linarith
    refine ⟨?_, hε1⟩
    rw [epsS_zero]
    nlinarith [pow_pos hu 2, pow_pos hu 3]

end Theorem1439ARqpCex



open Theorem1439OrderCex Theorem1439ARqpCex in
/-- **Theorem 14.3.9 of [cartis2022evaluation] fails for genuine ARqp-SC runs when
`q ∈ {1, 2}` and `p ≥ q + 3`** (the exponents `π_j = j(p+1)/p` of (14.2.12), "otherwise" entry;
for `q = 1` the exponent `(p+1)/p` is also that of the "`q = 1`, `X` convex" ARqp-SC entry and of
the convex ARqpC-SC entry). There is one problem (`n = 2`, `m = 1`, `X = [-1, 1]²`,
`f(x) = x₁ - x₂/16`, `c(x) = x₁²/2`) satisfying the assumptions of the theorem — X.CNe
(`AssumptionXCNe`; `X` also convex), c.D1pLB.X and f.D1pLB.X on `X₀ = B(0, 2)`, f.B.Fb on `ℱ_1`
with `f_low = -2`, `f_up = 2` — and ARqpC constants `P` (`cexP`, with `θ < ς`) such that, with
`θ = β = 1/2`, `x₀ = (0, 0)` and every Phase-1 constant `β₁ ∈ (0, 1)`, for all `κ_F`, `κ_D` there
are tolerances `ε_j ∈ (0, 1]` (`ε₀ ≤ β_F = 1`, `ε₀, ε₁ ≤ κ_F⁻¹` when `κ_F ≥ 1`, `ε₂ = 1`) and a
TPqp-GC run whose INNER calls in both phases are ARqp-SC runs (`IsTPqpGCARqpSCRun`, the run class
of `theorem_14_3_9_arqp`; Phase 1 makes no call and Phase 2 is entered at `x₀`) such that at its
termination index `k_ε` the numbers of evaluations of `(f, c)` and of their derivatives exceed
`κ_F max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `κ_D max_j ε₀^{1-π_j} ε_j^{-π_j}`, the orders
printed in the theorem, and are at least `(ε₀ ε₁)^{-1}/128`.

The run (`Theorem1439ARqpCex.runS`): for `u = 1/(4N⁵)`, `ε₀ = u²/2 + u³/2`, `ε₁ = 3u/2` and
`M = N¹⁵`, Phase 2 makes `M + 1` outer iterations, each a single successful ARqp-SC iteration
(`callOut_run`): the first moves from `(0, 0)` to `(u, ·)`, the next `M - 1` move along `x₂` with
`f(x_{k+1}) = t_k - E_k`, `E_k ≈ u³/2 ≈ 2 ε₀ ε₁/3`, where `∇μ(·, t_k) = (u³/2 - E_k, E_k/16)` is
nearly zero (INNER stops; case (b), the target drops by `2E_k`; after the reflection the gradient
is `≈ (u³, ·)` and (14.3.34) fails), and the last lands at `(-3u/4, ·)` where (14.3.32) holds with
`f > t` (case (c)). Each step satisfies the Step-2 conditions (14.1.12)–(14.1.13), all the
printed Algorithm 14.1.1 asks for, and is an output of the detailed Step 2 (Algorithm 14.1.2)
initialized with `μ = Δm(s)/(m(0) - m*)` at Step 2.1 (`μ ∈ (0, 1]` is chosen afresh at every
Step 2, not fixed at Step 0, and the book notes that global minimization is not required,
OCR l. 12760): an approximate critical point of the model with tiny model decrease, not an
approximate global minimizer. The Taylor models are exact (`μ` is a quartic polynomial, `p ≥ 4`;
`taylorSum_merit`), so every ratio is `1`; the second-order tests (`q = 2`) hold with room to
spare. The number of evaluations is `M + 2 ∼ (ε₀ ε₁)^{-1}`, the extra term of
`theorem_14_3_9_arqp_corrected`, which is thus attained (for `q ∈ {1, 2}`, `p ≥ q + 3`). -/
theorem theorem_14_3_9_arqp_counterexample {p q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hpq : q + 3 ≤ p) :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (Lc Bc Lf Bf : ℕ → ℝ) (P : ARqpCParams),
      AssumptionXCNe X ∧ Convex ℝ X ∧ AssumptionCD1pLBX c X (ball 0 2) p Lc Bc ∧
      AssumptionD1pLBX f X (ball 0 2) p Lf Bf ∧ Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      P.θ < P.ς ∧
      ∀ β₁ κF κD : ℝ, 0 < β₁ → β₁ < 1 →
        ∃ (ε : ℕ → ℝ) (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (D : TPqpSeq 2),
          (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ (1 ≤ κF → ε 0 ≤ κF⁻¹ ∧ ε 1 ≤ κF⁻¹) ∧
          (∀ nF₁ nD₁ : ℕ → ℕ, IsTPqpGCARqpSCRun f c X p q P (1 / 2) β₁ (1 / 2) ε (pt 0 0) xP δP 0
            D nF₁ nD₁) ∧
          ‖c (xP 0)‖ ≤ 1 / 2 * ε 0 ∧ (∃ kε, D.IsEnd f c X q (1 / 2) ε kε) ∧
          ∀ kε, D.IsEnd f c X q (1 / 2) ε kε →
            κF * tpqpOrderF (Chapter12.arqpPiOf False p) q ε < D.funEvals kε ∧
            κD * tpqpOrderD (Chapter12.arqpPiOf False p) q ε < D.derivEvals kε ∧
            (ε 0 * ε 1)⁻¹ ≤ 128 * D.funEvals kε := by
  obtain ⟨⟨Lf, Bf, hf⟩, Lc, Bc, hc⟩ := assumptionD1pLBX_objG p
  refine ⟨objG, conC, boxX, Lc, Bc, Lf, Bf, cexP, ⟨isClosed_boxX, ⟨pt 0 0, pt_mem (by norm_num)
    (by norm_num)⟩⟩, convex_boxX, hc, hf, assumptionBFb_objG, by norm_num [cexP],
    fun β₁ κF κD hβ₁ hβ₁1 => ?_⟩
  set C := max (max κF κD) 1 with hC_def
  have hC1 : 1 ≤ C := le_max_right _ _
  obtain ⟨N, hN3, hNC, hCε⟩ := Theorem1439ARqpCex.exists_params C
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hNp : (0 : ℝ) < N := by linarith
  set u : ℝ := 1 / (4 * N ^ 5) with hu_def
  set M : ℕ := N ^ 15 with hM_def
  have hu : 0 < u := by positivity
  have hN5 : (243 : ℝ) ≤ (N : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num) hNR 5; norm_num at this; linarith
  have hu' : u ≤ 1 / 200 := by
    rw [hu_def]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hMR : ((M : ℕ) : ℝ) = (N : ℝ) ^ 15 := by rw [hM_def]; push_cast; ring
  have hMe : u ^ 3 * M = 1 / 64 := by
    rw [hMR, hu_def]; field_simp; ring
  have hM : u ^ 3 * M ≤ 1 / 64 := hMe.le
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hu7 : u ≤ 1 / 7 := by linarith
  have hc0 : ‖conC (pt 0 0)‖ = 0 := by rw [norm_conC]; simp
  refine ⟨epsS u, fun _ => pt 0 0, fun _ _ => 1, runS u M,
    fun j => ⟨epsS_pos hu j, epsS_le_one hu hu7 j⟩, fun hκ => ?_,
    fun nF₁ nD₁ => isTPqpGCARqpSCRun hu hu' hM hM1 hq1 hq2 (by omega) hβ₁ hβ₁1 nF₁ nD₁,
    by rw [hc0]; exact (mul_pos (by norm_num) (epsS_pos hu 0)).le,
    ⟨M + 1, Theorem1439ARqpCex.isEnd hu hu' hM hq1⟩,
    fun kε hend => ?_⟩
  · have hle : C⁻¹ ≤ κF⁻¹ :=
      inv_anti₀ (by linarith) ((le_max_left _ _).trans (le_max_left _ _))
    obtain ⟨h0, h1'⟩ := hCε hC1
    exact ⟨h0.trans hle, h1'.trans hle⟩
  rw [(isEnd_iff hu hu' hM hq1).1 hend, (funEvals_runS u M (M + 1)).1,
    (funEvals_runS u M (M + 1)).2]
  obtain ⟨hF, hD⟩ := order_le_pow (p := p) hq1 hq2 hpq (show 1 ≤ N by omega)
  rw [← hu_def] at hF hD
  have hF0 : 0 ≤ tpqpOrderF (Chapter12.arqpPiOf False p) q (epsS u) :=
    zero_le_one.trans (one_le_tpqpOrderF (epsS_pos hu 0) (epsS_le_one hu hu7 0))
  have hD0 : 0 ≤ tpqpOrderD (Chapter12.arqpPiOf False p) q (epsS u) := Chapter12.le_finMax_left
  have hκF : κF * tpqpOrderF (Chapter12.arqpPiOf False p) q (epsS u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hF0).trans
      (mul_le_mul_of_nonneg_left hF (by linarith))
  have hκD : κD * tpqpOrderD (Chapter12.arqpPiOf False p) q (epsS u) ≤
      C * (128 * (N : ℝ) ^ 14) :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hD0).trans
      (mul_le_mul_of_nonneg_left hD (by linarith))
  have hε01 : (epsS u 0 * epsS u 1)⁻¹ ≤ 128 * ((M + 1 + 1 : ℕ) : ℝ) := by
    rw [epsS_zero, epsS_one]
    have h3 : 3 * u ^ 3 / 4 ≤ (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) := by nlinarith [pow_pos hu 4]
    have h3' : 0 < 3 * u ^ 3 / 4 := by positivity
    calc ((u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2))⁻¹ ≤ (3 * u ^ 3 / 4)⁻¹ := inv_anti₀ h3' h3
      _ = 4 / 3 * (64 * M) := by
          have : u ^ 3 ≠ 0 := by positivity
          field_simp
          nlinarith [hMe]
      _ ≤ 128 * ((M + 1 + 1 : ℕ) : ℝ) := by push_cast; nlinarith
  push_cast at hε01 ⊢
  rw [hMR] at hε01 ⊢
  refine ⟨by linarith, by linarith, hε01⟩

open Theorem1439OrderCex Theorem1439ARqpCex in
/-- **The printed Theorem 14.3.9 for INNER = ARqp-SC is false when `q ∈ {1, 2}`, `p ≥ q + 3`**:
on the problem of `theorem_14_3_9_arqp_counterexample`, which satisfies its assumptions,
no constants `κ_F`, `κ_D` bound the evaluation counts of every TPqp-GC run with INNER = ARqp-SC
(`IsTPqpGCARqpSCRun`, `θ = β = β₁ = 1/2`, `x₀ = (0, 0)`) by
`κ_F max[ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}]` and `κ_D max_j ε₀^{1-π_j} ε_j^{-π_j}`,
`π_j = j(p+1)/p` (the conclusion of `theorem_14_3_9_arqp`, proved there for `q = p`, and of the
corrected `theorem_14_3_9_arqp_corrected` without its extra term `∑_j (ε₀ ε_j)^{-j}`). -/
theorem theorem_14_3_9_arqp_printed_false {p q : ℕ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hpq : q + 3 ≤ p) :
    ∃ (f : ℝ² → ℝ) (c : ℝ² → ℝ¹) (X : Set ℝ²) (Lc Bc Lf Bf : ℕ → ℝ) (P : ARqpCParams),
      AssumptionXCNe X ∧ Convex ℝ X ∧ AssumptionCD1pLBX c X (ball 0 2) p Lc Bc ∧
      AssumptionD1pLBX f X (ball 0 2) p Lf Bf ∧ Chapter07.AssumptionBFb f c X 1 (-2) 2 ∧
      P.θ < P.ς ∧
      ¬ ∃ κF κD : ℝ, ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ 1 →
        ∀ (xP : ℕ → ℝ²) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq 2) (nF₁ nD₁ : ℕ → ℕ),
          IsTPqpGCARqpSCRun f c X p q P (1 / 2) (1 / 2) (1 / 2) ε (pt 0 0) xP δP k₁ D nF₁ nD₁ →
          (1 / 2 * ε 0 < ‖c (xP k₁)‖ →
            ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
              κF * tpqpOrderF (Chapter12.arqpPiOf False p) q ε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤
              κD * tpqpOrderD (Chapter12.arqpPiOf False p) q ε) ∧
          (‖c (xP k₁)‖ ≤ 1 / 2 * ε 0 → ∃ kε, D.IsEnd f c X q (1 / 2) ε kε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
              κF * tpqpOrderF (Chapter12.arqpPiOf False p) q ε ∧
            ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
              κD * tpqpOrderD (Chapter12.arqpPiOf False p) q ε) := by
  obtain ⟨f, c, X, Lc, Bc, Lf, Bf, P, hX, hXc, hc, hf, hB, hθς, hrun⟩ :=
    theorem_14_3_9_arqp_counterexample hq1 hq2 hpq
  refine ⟨f, c, X, Lc, Bc, Lf, Bf, P, hX, hXc, hc, hf, hB, hθς, ?_⟩
  rintro ⟨κF, κD, hκ⟩
  obtain ⟨ε, xP, δP, D, hε, -, hR, hc0, -, hcount⟩ := hrun (1 / 2) κF κD (by norm_num) (by norm_num)
  obtain ⟨kε, hend, hF, -⟩ := (hκ ε (fun j _ => hε j) (hε 0).2 xP δP 0 D (fun _ => 0) (fun _ => 0)
    (hR _ _)).2 hc0
  have := (hcount kε hend).1
  simp only [Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty, zero_add] at hF
  linarith

end CartisGouldToint.Chapter14
