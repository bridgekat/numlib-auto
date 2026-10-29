import Numlib.Optimization.Complexity.DynamicAccuracy
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.Basic
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.ModelBased.InexactRatio

/-!
# ARqpIDA/ARqpEDA: one iteration and the step-length algebra

One iteration of the adaptive-regularization methods with inexact derivatives and dynamic
accuracy ARqpIDA and ARqpEDA ([cartis2022evaluation], Algorithms 13.1.2 and 13.3.2): Step 1 with
the halving of the optimality radii, Step 2 for the regularized inexact model
`m̄_k(v) = \overline{T}_{f,p}(x_k, v) + σ_k/(p+1)! ‖v‖^{p+1}`, the regularization update and the
accuracy-improving branch, together with the radii control (13.1.69)–(13.1.70) and the
step-length algebra used by both analyses. The iteration is stated on a feasible set `X`
(§14.2).

## Main definitions

* `ARqpIDAParams`, `ARqpStep1`, `ARqpStep2`, `ARqpDAStep`;
* `ARqpDARadiiControl u`: the radii control, with unit radii (mode `u`) or the lower bounds of the
  type (12.2.51) at every order (mode `¬ u`); `RadiiControl` is the mode `u = (q ≤ 2)`;
* `arPiOf`, `arStepConstOf`: the exponents `π_j` and the constants of the step-length bounds.

## Main results

* `arqpDA_card_trial_le` (Lemma 13.1.9), `ARqpStep1.radius_bounds` (Lemma 13.1.11),
  `ARqpDAStep.taylorDecrement_ge` (Lemma 13.1.13), `arqpDA_radius_ge` (the radius bound
  (13.1.71));
* `arqp_pow_ge_of_radius_ineq`, `arqp_pow_succ_ge`: step lengths from radius inequalities.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpIDA: constants and one iteration -/

/-- The constants of Algorithm 13.1.2 (ARqpIDA, [cartis2022evaluation], Step 0, (13.1.51)): the
ARqp constants (`σ₀ > 0`, `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂ ≤ γ₃`, `θ ∈ (0, 1)`,
`ς ∈ (0, 1]`) with `σ_min ∈ (0, σ₀]`, orders
`1 ≤ q ≤ p`, `κ_s > 0`, `κ_h ≥ 0`, `γ_h ∈ (0, 1)`, initial radii `δ₀ ∈ (0, 1]^q` and initial
accuracies `0 ≤ h_{0,i} ≤ κ_h` (`i ∈ [1, p]`). The requirement `ε_j ≤ δ_{0,j}` is part of the run
predicate. -/
structure ARqpIDAParams extends ARqpParams where
  /-- The criticality order. -/
  q : ℕ
  /-- The degree of the model. -/
  p : ℕ
  /-- The accuracy reduction factor. -/
  γh : ℝ
  /-- The constant of the accuracy test (13.1.46). -/
  κs : ℝ
  /-- The bound on the initial accuracies. -/
  κh : ℝ
  /-- The initial optimality radii. -/
  δ₀ : ℕ → ℝ
  /-- The initial requested accuracies. -/
  h₀ : ℕ → ℝ
  one_le_q : 1 ≤ q
  q_le_p : q ≤ p
  σmin_pos : 0 < σmin
  γh_pos : 0 < γh
  γh_lt_one : γh < 1
  κs_pos : 0 < κs
  κh_nonneg : 0 ≤ κh
  δ₀_mem : ∀ j ∈ Finset.Icc 1 q, δ₀ j ∈ Set.Ioc 0 1
  h₀_nonneg : ∀ i ∈ Finset.Icc 1 p, 0 ≤ h₀ i
  h₀_le : ∀ i ∈ Finset.Icc 1 p, h₀ i ≤ κh

namespace ARqpIDAParams

variable (P : ARqpIDAParams)

theorem one_le_p : 1 ≤ P.p := P.one_le_q.trans P.q_le_p

theorem one_mem_Icc : 1 ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩

theorem Icc_q_subset : Finset.Icc 1 P.q ⊆ Finset.Icc 1 P.p :=
  Finset.Icc_subset_Icc le_rfl P.q_le_p

end ARqpIDAParams

section ARStep

variable {X : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → E} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The decrease `Δm̄_k(v) = m̄_k(0) - m̄_k(v)` of the regularized inexact model
`m̄_k(v) = \overline{T}_{f,p}(x_k, v) + σ_k/(p+1)! ‖v‖^{p+1}` (13.1.45). -/
noncomputable abbrev arModelDec (P : ARqpIDAParams) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (σ : ℕ → ℝ) (k : ℕ) (v : E) : ℝ :=
  regularizedModel (D k) P.p (σ k) 0 - regularizedModel (D k) P.p (σ k) v

/-- `Δm̄_k(v) = \overline{ΔT}_{f,p}(x_k, v) - σ_k/(p+1)! ‖v‖^{p+1}`. -/
theorem arModelDec_eq (k : ℕ) (v : E) :
    arModelDec P D σ k v =
      (D k).taylorDecrement P.p v - σ k / ((P.p + 1)! : ℝ) * ‖v‖ ^ (P.p + 1) := by
  rw [arModelDec, regularizedModel_zero_right, regularizedModel_def,
    FormalMultilinearSeries.taylorDecrement]
  ring

/-- The Step-1.2 test (13.1.53) passes at order `j` with the radius `δ^{(1)}_{k,j}`:
`\overline{ΔT}_{f,j}(x_k, d_{k,j}) ≤ ½ ς ε_j (δ^{(1)}_{k,j})^j/j!`. -/
def arqpDAPass (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (k j : ℕ) : Prop :=
  (D k).taylorDecrement j (dd k j) ≤ P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- Step 2 of ARqpIDA, entered at the least order `j_k` at which (13.1.53) fails (and (13.1.54)
holds): the step `s_k` (feasible) decreases the model at least as much as `d_k` (13.1.55), and
either `‖s_k‖ ≥ 1` with `δ_{s_k} = δ^{(1)}_k` (13.1.56) or the radii `δ_{s_k} ∈ (0, 1]^q` and
displacements `d^m_{s_k,ℓ}` satisfy (13.1.57); the iteration is accuracy-improving iff
`‖s_k‖ < 1` and the accuracy test (13.1.46) fails for some `i ∈ [1, p]`. -/
structure ARqpStep2 (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop where
  /-- `j_k ∈ [1, q]`. -/
  jk_mem : jk k ∈ Finset.Icc 1 P.q
  /-- (13.1.53) fails at `j_k`. -/
  not_pass : ¬ arqpDAPass P ε D δ₁ dd k (jk k)
  /-- (13.1.53) holds below `j_k`. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < jk k → arqpDAPass P ε D δ₁ dd k j
  /-- The radii above `j_k` are not examined in Step 1. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, jk k < j → δ₁ k j = δ k j
  /-- (13.1.54) at `j_k`. -/
  model_dec : P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (dd k (jk k))
  /-- The trial point is feasible. -/
  mem : x k + s k ∈ X
  /-- (13.1.55). -/
  dec_le : arModelDec P D σ k (dd k (jk k)) ≤ arModelDec P D σ k (s k)
  /-- (13.1.56) or (13.1.57). -/
  radii : (1 ≤ ‖s k‖ ∧ δs k = δ₁ k) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
        (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ !
  /-- Branching to Step 5 iff `‖s_k‖ < 1` and (13.1.46) fails for some `i ∈ [1, p]`. -/
  acc_iff : acc k ↔ ‖s k‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s k‖ ^ (P.p - i + 1) < h k i

/-- **Step 1 of ARqpIDA / ARqpEDA** ([cartis2022evaluation], Algorithm 13.1.2, Steps 1.1–1.4) at
iteration `k` on the feasible set `X`, with radii `δ k = δ^{(0)}_k` at the start of Step 1
(13.1.60) and `δ₁ k = δ^{(1)}_k` at its end (13.1.61). The halving loop (`δ_{k,j}` is halved while
(13.1.53) and (13.1.54) both fail) is recorded by its effect:
`0 < δ^{(1)}_{k,j} = δ^{(0)}_{k,j}/2^m ≤ δ^{(0)}_{k,j}`, and after at least one halving,
`2 δ^{(1)}_{k,j} ≤ δ^{(0)}_{k,j}` with a witness of the last halving (both tests failed at
radius `2 δ^{(1)}_{k,j}`) and of the
first one ((13.1.53) failed at radius `δ^{(0)}_{k,j}`). The final displacements satisfy
(13.1.52). -/
structure ARqpStep1 (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (k : ℕ) :
    Prop where
  /-- `δ^{(1)}_{k,j} > 0`. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j
  /-- `δ^{(1)}_{k,j} ≤ δ^{(0)}_{k,j}`. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ≤ δ k j
  /-- The halving loop of Steps 1.1–1.4. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j < δ k j → 2 * δ₁ k j ≤ δ k j ∧
    (∃ d', ‖d'‖ ≤ 2 * δ₁ k j ∧ x k + d' ∈ X ∧
      P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 < (D k).taylorDecrement j d' ∧
      arModelDec P D σ k d' < P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ δ k j ∧ x k + d₀ ∈ X ∧
      P.ς * ε j * δ k j ^ j / j ! / 2 < (D k).taylorDecrement j d₀
  /-- The radii at the end of Step 1 are obtained by halving:
  `δ^{(1)}_{k,j} = δ^{(0)}_{k,j}/2^m`. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, δ₁ k j = δ k j / 2 ^ m
  /-- (13.1.52). -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((D k).taylorDecrement j) (δ₁ k j)
    {e | x k + e ∈ X} P.ς (dd k j)

/-- **One iteration of ARqpIDA / ARqpEDA** ([cartis2022evaluation], Algorithm 13.1.2, Steps 1, 2,
4, 5) on the feasible set `X`, given the ratio `ρ k`: Step 1 (`ARqpStep1`, radii `δ k`, `δ₁ k`);
if (13.1.53) holds at every order the iteration is accuracy-improving, otherwise Step 2
(`ARqpStep2`, radii `δs k = δ_{s_k}`) is performed. A trial iteration accepts or rejects the step,
updates `σ` by (13.1.59), inherits the radii `δ_{s_k}` after a successful short step and
`δ^{(1)}_k` otherwise, keeps the accuracies, and keeps the derivative estimates when the step is
rejected; an accuracy-improving iteration keeps `x_k`, `σ_k` and `δ^{(0)}_k` and multiplies the
accuracies by `γ_h`. -/
structure ARqpDAStep (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop) (ρ : ℕ → ℝ) (k : ℕ) :
    Prop extends ARqpStep1 X P ε x σ δ δ₁ D dd k where
  /-- Step 1 → Step 5 when (13.1.53) holds at every order. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j) → acc k
  /-- Step 2 otherwise. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
    ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k
  /-- Steps 3–4 on a trial iteration. -/
  accept : ¬ acc k → ARAcceptance P.toARParams (ρ k) (x k) (s k) (x (k + 1)) (σ k) (σ (k + 1))
  /-- The radii inherited by the next iteration (Step 3). -/
  radii_trial : ¬ acc k →
    δ (k + 1) = if P.η₁ ≤ ρ k ∧ ‖s k‖ < 1 then δs k else δ₁ k
  /-- The accuracies are kept on trial iterations. -/
  h_trial : ¬ acc k → h (k + 1) = h k
  /-- No new derivative estimates at an unchanged iterate. -/
  D_unsucc : ¬ acc k → ρ k < P.η₁ → D (k + 1) = D k
  /-- Step 5 keeps the iterate. -/
  x_acc : acc k → x (k + 1) = x k
  /-- Step 5 keeps the radii `δ^{(0)}_k`. -/
  δ_acc : acc k → δ (k + 1) = δ k
  /-- Step 5 keeps the regularization parameter. -/
  σ_acc : acc k → σ (k + 1) = σ k
  /-- Step 5 multiplies the accuracies by `γ_h`. -/
  h_acc : acc k → ∀ i, h (k + 1) i = P.γh * h k i

/-- The radii control of ARqpIDA / ARqpEDA in one of two modes, selected by the proposition `u`
([cartis2022evaluation], (13.1.69)–(13.1.70) and §14.2): after a trial iteration with a short
step `‖s_k‖ < 1`, if `u` holds then `δ_{s_k,j} = 1` for all `j ∈ [1, q]` (unit radii), and if `u`
fails then `δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` for all `j ∈ [1, q]` (the (12.2.51)-type lower
bound at every order). Unit radii are what Algorithm 12.2.3 delivers for `q ≤ 2` without
constraints (or for `q = 1` on a convex feasible set); the lower bound is available in every
case, in particular for `q > 2` or with a general feasible set. The complexity orders depend on
the mode (`arPiOf u`). -/
def ARqpDARadiiControl (u : Prop) (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ)
    (δs : ℕ → ℕ → ℝ) (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  ¬ acc k → ‖s k‖ < 1 → (u → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
    (¬ u → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)

/-- The radii control in the mode determined by the order: `ARqpDARadiiControl` with unit radii
exactly when `q ≤ 2`, i.e. after a trial iteration with a short step, `δ_{s_k,j} = 1` for all
`j ∈ [1, q]` if `q ≤ 2`, and `δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` for all `j ∈ [1, q]` if
`q > 2` (cf. [cartis2022evaluation], (13.1.69)–(13.1.70)). Unit radii at the orders `j ≤ 2` and
the lower bound at the orders `j ≥ 3` imply it (`RadiiControl.of_unit_le_two`). -/
def RadiiControl (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ) (δs : ℕ → ℕ → ℝ)
    (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  ARqpDARadiiControl (P.q ≤ 2) P ε Lb σ δs s acc k

omit [InnerProductSpace ℝ E] in
/-- `RadiiControl` unfolded, with the case `2 < q` for the lower bounds. -/
theorem radiiControl_iff {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ} :
    RadiiControl P ε Lb σ δs s acc k ↔
      (¬ acc k → ‖s k‖ < 1 → (P.q ≤ 2 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
        (2 < P.q → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)) := by
  simp only [RadiiControl, ARqpDARadiiControl, not_le]

omit [InnerProductSpace ℝ E] in
/-- Unit radii give the radii control in either mode: if `δ_{s_k,j} = 1` for all `j ∈ [1, q]`
after a trial iteration with a short step, `ε_j ≤ 1` and `L̄ ≥ 1`, then `ARqpDARadiiControl u` holds
for every `u` (the lower bound `ς θ ε_j/(24 max(L̄, σ_k)) ≤ 1` is automatic). -/
theorem ARqpDARadiiControl.of_unit {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ} {u : Prop} (hLb : 1 ≤ Lb)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ 1)
    (h1 : ¬ acc k → ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) :
    ARqpDARadiiControl u P ε Lb σ δs s acc k := by
  intro hk hs1
  refine ⟨fun _ => h1 hk hs1, fun _ j hj => ?_⟩
  rw [h1 hk hs1 j hj]
  have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  rw [div_le_one (by positivity)]
  have h0 : P.ς * P.θ ≤ 1 := (mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le
  rcases le_or_gt (ε j) 0 with hε0 | hε0
  · have : P.ς * P.θ * ε j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hε0
    linarith
  · have : P.ς * P.θ * ε j ≤ 1 := by nlinarith [hε j hj]
    linarith

omit [InnerProductSpace ℝ E] in
/-- Unit radii at the orders `j ≤ min(2, q)` and the lower bound
`δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` at the orders `j ∈ [3, q]` (after a trial iteration with a
short step) imply `RadiiControl` when `ε ∈ (0, 1]^q` and `L̄ ≥ 1`
([cartis2022evaluation], (13.1.69)–(13.1.70)). -/
theorem RadiiControl.of_unit_le_two {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ}
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb)
    (h : ¬ acc k → ‖s k‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), δs k j = 1) ∧
      ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j) :
    RadiiControl P ε Lb σ δs s acc k := by
  intro hk hs1
  obtain ⟨h1, h2⟩ := h hk hs1
  refine ⟨fun hq j hj => h1 j ?_, fun _ j hj => ?_⟩
  · obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    exact Finset.mem_Icc.2 ⟨hj1, le_min (hjq.trans hq) hjq⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  rcases le_or_gt j 2 with hj2 | hj2
  · rw [h1 j (Finset.mem_Icc.2 ⟨hj1, le_min hj2 hjq⟩)]
    have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
    have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
    have hεj := hε j hj
    rw [div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      (mul_le_of_le_one_left hεj.1.le
        ((mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le)).trans hεj.2
    linarith
  · exact h2 j (Finset.mem_Icc.2 ⟨hj2, hjq⟩)

namespace ARqpDAStep

variable (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k)
include hs

/-- A trial iteration went through Step 2. -/
theorem step2_of_not_acc (hk : ¬ acc k) : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k := by
  refine hs.step2 ?_
  by_contra hc
  push Not at hc
  exact hk (hs.acc_of_pass hc)

/-- The parameter update of a trial iteration. -/
theorem update (hk : ¬ acc k) :
    ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  (hs.accept hk).2

/-- The iterate is kept unless the iteration is successful. -/
theorem iterate_succ_eq (hk : ¬ (¬ acc k ∧ P.η₁ ≤ ρ k)) : x (k + 1) = x k := by
  by_cases ha : acc k
  · exact hs.x_acc ha
  · exact (hs.accept ha).eq_self (not_le.1 fun h' => hk ⟨ha, h'⟩)

/-- A successful iteration moves to the trial point. -/
theorem iterate_succ_eq_add (hk : ¬ acc k) (hρ : P.η₁ ≤ ρ k) : x (k + 1) = x k + s k :=
  (hs.accept hk).eq_add hρ

/-- The iterates stay feasible: `x_k ∈ X` implies `x_{k+1} ∈ X`. -/
theorem mem_succ (hx : x k ∈ X) : x (k + 1) ∈ X := by
  by_cases hc : ¬ acc k ∧ P.η₁ ≤ ρ k
  · rw [hs.iterate_succ_eq_add hc.1 hc.2]; exact (hs.step2_of_not_acc hc.1).mem
  · rw [hs.iterate_succ_eq hc]; exact hx

/-- One iteration only involves the data at iterations `k` and `k + 1`: the step predicate at `k`
transfers to sequences whose iterates, weights, radii `δ^{(0)}`, accuracies and estimates at `k'`
and `k' + 1`, and whose radii `δ^{(1)}`, `δ_s`, displacements, order, step, flag and ratio at
`k'`, are those of iterations `k` and `k + 1` (used to splice runs). -/
theorem congr {x' : ℕ → E} {σ' : ℕ → ℝ} {δ' δ₁' δs' : ℕ → ℕ → ℝ} {h' : ℕ → ℕ → ℝ}
    {D' : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd' : ℕ → ℕ → E} {jk' : ℕ → ℕ} {s' : ℕ → E}
    {acc' : ℕ → Prop} {ρ' : ℕ → ℝ} {k' : ℕ} (hx : x' k' = x k) (hx1 : x' (k' + 1) = x (k + 1))
    (hσ : σ' k' = σ k) (hσ1 : σ' (k' + 1) = σ (k + 1)) (hδ : δ' k' = δ k)
    (hδ1 : δ' (k' + 1) = δ (k + 1)) (hδ₁ : δ₁' k' = δ₁ k) (hδs : δs' k' = δs k)
    (hh : h' k' = h k) (hh1 : h' (k' + 1) = h (k + 1)) (hD : D' k' = D k)
    (hD1 : D' (k' + 1) = D (k + 1)) (hdd : dd' k' = dd k) (hjk : jk' k' = jk k)
    (hs' : s' k' = s k) (hacc : acc' k' ↔ acc k) (hρ : ρ' k' = ρ k) :
    ARqpDAStep X P ε x' σ' δ' δ₁' δs' h' D' dd' jk' s' acc' ρ' k' := by
  obtain ⟨⟨hpos, hle, hhalf, hdy, hw⟩, hap, hst, hac, hrt, hht, hdu, hxa, hδa, hσa, hha⟩ := hs
  have hP : ∀ j, arqpDAPass P ε D' δ₁' dd' k' j ↔ arqpDAPass P ε D δ₁ dd k j := fun j => by
    simp only [arqpDAPass, hD, hδ₁, hdd]
  have hM : ∀ v, arModelDec P D' σ' k' v = arModelDec P D σ k v := fun v => by
    simp only [arModelDec, hD, hσ]
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun hp => hacc.2 (hap fun j hj => (hP j).1 (hp j hj)), fun ⟨j, hj, hf⟩ => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha hr => ?_, fun ha => ?_, fun ha => ?_,
    fun ha => ?_, fun ha => ?_⟩
  · rw [hδ₁]; exact hpos j hj
  · rw [hδ₁, hδ]; exact hle j hj
  · rw [hδ₁, hδ] at hlt ⊢
    simp only [hx, hM, hD]
    exact hhalf j hj hlt
  · rw [hδ₁, hδ]; exact hdy j hj
  · rw [hδ₁, hD, hx, hdd]; exact hw j hj
  · obtain ⟨hjm, hnp, hpl, hrg, hmd, hmem, hdl, hrad, hai⟩ :=
      hst ⟨j, hj, fun h' => hf ((hP j).2 h')⟩
    refine ⟨hjk ▸ hjm, fun h' => hnp ((hP _).1 (hjk ▸ h')), fun i hi hlt => (hP i).2
      (hpl i hi (hjk ▸ hlt)), fun i hi hlt => by rw [hδ₁, hδ]; exact hrg i hi (hjk ▸ hlt),
      by rw [hM, hjk, hdd, hδ₁]; exact hmd, by rw [hx, hs']; exact hmem,
      by rw [hM, hM, hjk, hdd, hs']; exact hdl, ?_, by rw [hacc, hs', hh]; exact hai⟩
    rw [hs', hδs, hD, hσ, hx, hδ₁]; exact hrad
  · rw [hρ, hx, hs', hx1, hσ, hσ1]; exact hac (fun h => ha (hacc.2 h))
  · rw [hδ1, hρ, hs', hδs, hδ₁]; exact hrt (fun h => ha (hacc.2 h))
  · rw [hh1, hh]; exact hht (fun h => ha (hacc.2 h))
  · rw [hD1, hD]; exact hdu (fun h => ha (hacc.2 h)) (hρ ▸ hr)
  · rw [hx1, hx]; exact hxa (hacc.1 ha)
  · rw [hδ1, hδ]; exact hδa (hacc.1 ha)
  · rw [hσ1, hσ]; exact hσa (hacc.1 ha)
  · rw [hh1, hh]; exact hha (hacc.1 ha)

end ARqpDAStep

/-- The iterates of ARqpIDA/ARqpEDA sequences starting in `X` stay in `X`. -/
theorem arqpDA_mem (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hx0 : x 0 ∈ X) : x k ∈ X := by
  induction k with
  | zero => exact hx0
  | succ k ih => exact (hstep k k.lt_succ_self).mem_succ (ih fun i hi => hstep i (by omega))

/-- A trial step with `‖s_k‖ < 1` satisfies (13.1.57). -/
theorem ARqpStep2.radii_of_lt (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hs1 : ‖s k‖ < 1) :
    ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
      ∃ dm, IsApproxMeasureStep
          ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
          (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
          P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ ! :=
  h2.radii.resolve_left fun h' => absurd h'.1 (not_le.2 hs1)

/-- On a trial iteration with `‖s_k‖ < 1`, the accuracy test (13.1.46) holds. -/
theorem ARqpStep2.accuracy_le_of_not_acc (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hk : ¬ acc k) (hs1 : ‖s k‖ < 1) :
    ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := by
  intro i hi
  by_contra hc
  exact hk (h2.acc_iff.2 ⟨hs1, i, hi, not_le.1 hc⟩)

/-- **Invariants of ARqpIDA/ARqpEDA sequences**: if the step predicate holds at every iteration
`i < k`, `σ_0 = σ₀`, `δ_0 = δ₀` and `h_0 = h₀`, then `σ_k ≥ σ_min`, `δ_{k,j} ∈ (0, 1]` for
`j ∈ [1, q]` and `0 ≤ h_{k,i} ≤ κ_h` for `i ∈ [1, p]`. -/
theorem arqpDA_invariants (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh := by
  induction k with
  | zero =>
    rw [hσ0, hδ0, hh0]
    exact ⟨P.σmin_le_σ₀, fun j hj => P.δ₀_mem j hj, fun i hi => ⟨P.h₀_nonneg i hi, P.h₀_le i hi⟩⟩
  | succ k ih =>
    obtain ⟨hσ, hδ, hh⟩ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · refine ⟨by rw [hk.σ_acc ha]; exact hσ, by rw [hk.δ_acc ha]; exact hδ, fun i hi => ?_⟩
      rw [hk.h_acc ha i]
      obtain ⟨h1, h2⟩ := hh i hi
      exact ⟨mul_nonneg P.γh_pos.le h1, (mul_le_of_le_one_left h1 P.γh_lt_one.le).trans h2⟩
    refine ⟨(hk.update ha).sigmaMin_le P.σmin_nonneg P.one_le_γ₂ hσ, ?_,
      by rw [hk.h_trial ha]; exact hh⟩
    intro j hj
    rw [hk.radii_trial ha]
    split_ifs with hc
    · exact ((hk.step2_of_not_acc ha).radii_of_lt hc.2 j hj).1
    · exact ⟨hk.radius_pos j hj, (hk.radius_le j hj).trans (hδ j hj).2⟩

/-- The regularization parameters of ARqpIDA/ARqpEDA sequences are positive. -/
theorem arqpDA_sigma_pos (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) : 0 < σ k :=
  P.σmin_pos.trans_le (arqpDA_invariants hstep hσ0 hδ0 hh0).1

/-! ### Counting the trial iterations -/

/-- **Counting the trial iterations** (Lemma 13.1.9 of [cartis2022evaluation]): for sequences
satisfying the ARqpIDA step predicate at every iteration `i ≤ k` with `σ_0 = σ₀`, if
`σ_{k+1} ≤ σ_max`, then `|𝒯_k| ≤ |𝒮_k| (1 + |log γ₁|/log γ₂) + log(σ_max/σ₀)/log γ₂` (13.1.62). -/
theorem arqpDA_card_trial_le (hstep : ∀ i ≤ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) {σmax : ℝ}
    (hσmax : σ (k + 1) ≤ σmax) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  have hpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqpDA_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have h := card_successSet_or_le_of_lower_ratio (σ := σ) (k := k)
    (succ := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (fail := fun i => ¬ acc i ∧ ρ i < P.η₁)
    (hσ0 ▸ P.σ₀_pos) P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂
    (fun i _ hi hf => not_le.2 hf.2 hi.2)
    (fun i hi hs => ((hstep i hi).update hs.1).mul_le_of_le hs.2 P.γ₁_le_one (hpos i hi).le)
    (fun i hi hf => ((hstep i hi).update hf.1).mul_le_of_lt hf.2)
    (fun i hi hs hf => by
      have ha : acc i := by
        by_contra ha
        rcases le_or_gt P.η₁ (ρ i) with hρ | hρ
        · exact hs ⟨ha, hρ⟩
        · exact hf ⟨ha, hρ⟩
      rw [(hstep i hi).σ_acc ha])
    hσmax
  rw [hσ0] at h
  have hset : successSet (fun i => (¬ acc i ∧ P.η₁ ≤ ρ i) ∨ (¬ acc i ∧ ρ i < P.η₁)) k =
      successSet (fun i => ¬ acc i) k := by
    ext i
    simp only [mem_successSet]
    constructor
    · rintro ⟨hi, (h1 | h1)⟩ <;> exact ⟨hi, h1.1⟩
    · rintro ⟨hi, h1⟩
      exact ⟨hi, (le_or_gt P.η₁ (ρ i)).imp (fun h2 => ⟨h1, h2⟩) fun h2 => ⟨h1, h2⟩⟩
  rwa [hset] at h

/-! ### Radii, accuracy and decrease at one iteration -/

/-- **The radii after Step 1** (Lemma 13.1.11 of [cartis2022evaluation]): if Step 1 of ARqpIDA (or
ARqpEDA) is performed at iteration `k` with `‖∇̄^i f(x_k)‖ ≤ L̄` for `i ∈ [1, p]` (`L̄ > 0`;
(13.1.63) for ARqpIDA), `σ_k ≥ 0` and `δ^{(0)}_k ∈ (0, 1]^q`, then (13.1.66)
`δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ min(ς ε_j/(16 max(L̄, σ_k)), δ^{(0)}_{k,j})` for `j ∈ [1, q]`.
(That the halving loop stops is `exists_arqpDA_halving`.) -/
theorem ARqpStep1.radius_bounds (hs : ARqpStep1 X P ε x σ δ δ₁ D dd k) {Lb : ℝ}
    (hLb : 0 < Lb) (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hδ1 : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    δ₁ k j ≤ δ k j ∧ min (P.ς * ε j / (16 * max Lb (σ k))) (δ k j) ≤ δ₁ k j := by
  refine ⟨hs.radius_le j hj, ?_⟩
  rcases (hs.radius_le j hj).lt_or_eq with hlt | heq
  swap
  · rw [heq]; exact min_le_right _ _
  obtain ⟨h2δ, ⟨d', hd'n, -, hd'T, hd'm⟩, -⟩ := hs.halving j hj hlt
  refine (min_le_left _ _).trans ?_
  by_contra hcon
  push Not at hcon
  have hM : 0 < max Lb (σ k) := lt_max_of_lt_left hLb
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hpos := hs.radius_pos j hj
  have hε : 0 < ε j := by
    by_contra hε
    push Not at hε
    have : P.ς * ε j / (16 * max Lb (σ k)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos P.ς_pos.le hε) (by positivity)
    linarith
  have key := regularizedModel_decrease_ge_of_taylorDecrement_ge (D := D k) (p := P.p)
    (σ := σ k) (L := Lb) hjp hσ
    (fun ℓ hℓ => hD ℓ (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega,
      (Finset.mem_Icc.1 hℓ).2⟩))
    (α := P.ς * ε j / 2) (δ := 2 * δ₁ k j) (by positivity) (h2δ.trans (hδ1 j hj)) ?_ hd'n
    (by
      have : P.ς * ε j / 2 * (2 * δ₁ k j) ^ j / j ! = P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 := by
        ring
      linarith)
  · have : P.ς * ε j / 2 / 2 * (2 * δ₁ k j) ^ j / j ! =
        P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4 := by ring
    rw [this] at key
    exact absurd key (not_le.2 hd'm)
  · rw [lt_div_iff₀ (by positivity)] at hcon
    nlinarith

/-- The constant `κ^{(1)}_δ(σ) = ς θ/(24 max(L̄, σ))` of (13.1.72). -/
noncomputable def arKappaDelta1 (P : ARqpIDAParams) (Lb σ : ℝ) : ℝ :=
  P.ς * P.θ / (24 * max Lb σ)

theorem arKappaDelta1_pos {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 0 < Lb) :
    0 < arKappaDelta1 P Lb σ := by
  have := P.ς_pos; have := P.θ_pos
  exact div_pos (by positivity) (by have : 0 < max Lb σ := lt_max_of_lt_left hLb; positivity)

theorem arKappaDelta1_le_one {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 1 ≤ Lb) :
    arKappaDelta1 P Lb σ ≤ 1 := by
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σ := hLb.trans (le_max_left _ _)
  rw [arKappaDelta1, div_le_one (by positivity)]
  nlinarith

omit [InnerProductSpace ℝ E] in
/-- Either mode of the radii control gives the lower bound `κ^{(1)}_δ(σ̄) ε_j ≤ δ_{s_k,j}` after
a trial iteration with a short step, when `ε ∈ (0, 1]^q`, `L̄ ≥ 1` and `σ_k ≤ σ̄`. -/
theorem ARqpDARadiiControl.kappa_mul_le {u : Prop} {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ}
    {σ : ℕ → ℝ} {δs : ℕ → ℕ → ℝ} {s : ℕ → E} {acc : ℕ → Prop} {k : ℕ}
    (hrc : ARqpDARadiiControl u P ε Lb σ δs s acc k) (hk : ¬ acc k) (hs : ‖s k‖ < 1)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb) {σbar : ℝ}
    (hσ : σ k ≤ σbar) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    arKappaDelta1 P Lb σbar * ε j ≤ δs k j := by
  obtain ⟨h1, h2⟩ := hrc hk hs
  have hεj := hε j hj
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σbar := hLb.trans (le_max_left _ _)
  have hM' : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  by_cases hu : u
  · rw [h1 hu j hj, arKappaDelta1, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      (mul_le_of_le_one_left hεj.1.le
        ((mul_le_of_le_one_left P.θ_pos.le P.ς_le_one).trans P.θ_lt_one.le)).trans hεj.2
    nlinarith
  · refine le_trans ?_ (h2 hu j hj)
    rw [arKappaDelta1, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by have := hεj.1; positivity) (by positivity)
      (by have := max_le_max (le_refl Lb) hσ; linarith)

/-- **The radius bound (13.1.71) of Lemma 13.1.12** ([cartis2022evaluation]), for sequences
satisfying the ARqpIDA step predicate at every iteration `i < k` and Step 1 at `k`, with
`ε ∈ (0, 1]^q`, `ε ≤ δ₀`, `‖∇̄^ℓ f(x_i)‖ ≤ L̄` (`L̄ ≥ 1`), `σ_i ≤ σ̄` for `i ≤ k` and the radii
control (`ARqpDARadiiControl`, either mode) at every `i < k`:
`δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ κ^{(1)}_δ(σ̄) ε_j` for `j ∈ [1, q]`. -/
theorem arqpDA_radius_ge (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hstep1 : ARqpStep1 X P ε x σ δ δ₁ D dd k) (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀)
    (hh0 : h 0 = P.h₀)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    {Lb σbar : ℝ} (hLb : 1 ≤ Lb) (hD : ∀ i ≤ k, ∀ ℓ ∈ Finset.Icc 1 P.p, ‖D i ℓ‖ ≤ Lb)
    (hσ : ∀ i ≤ k, σ i ≤ σbar) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε Lb σ δs s acc i) :
    ∀ j ∈ Finset.Icc 1 P.q, arKappaDelta1 P Lb σbar * ε j ≤ δ₁ k j ∧ δ₁ k j ≤ δ k j := by
  have hLb0 : 0 < Lb := zero_lt_one.trans_le hLb
  set κ := arKappaDelta1 P Lb σbar with hκdef
  have hκ0 : 0 < κ := arKappaDelta1_pos hLb0
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hς := P.ς_pos
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one.le
  have hσpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqpDA_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have hMle : ∀ i ≤ k, max Lb (σ i) ≤ max Lb σbar := fun i hi => max_le_max le_rfl (hσ i hi)
  -- (a) the halving lower bound dominates `κ ε`
  have ha : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q,
      κ * ε j ≤ P.ς * ε j / (16 * max Lb (σ i)) := by
    intro i hi j hj
    have hεj := (hε j hj).1
    have hM : 0 < max Lb (σ i) := lt_max_of_lt_left hLb0
    rw [le_div_iff₀ (by positivity), hκdef, arKappaDelta1, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ (by have : 0 < max Lb σbar := lt_max_of_lt_left hLb0; positivity)]
    have := hMle i hi
    have h1 : P.ς * P.θ * ε j * (16 * max Lb (σ i)) ≤ P.ς * 1 * ε j * (16 * max Lb σbar) := by
      gcongr
    have : 0 ≤ P.ς * ε j * max Lb σbar := by
      have : 0 < max Lb σbar := lt_max_of_lt_left hLb0
      positivity
    linarith
  -- the radii at the start of Step 1
  have hδk : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ i j := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      rw [hδ0]
      exact (mul_le_of_le_one_left (hε j hj).1.le hκ1).trans (hεδ j hj)
    | succ i ih =>
      intro hi j hj
      have hik : i ≤ k := by omega
      have hsi := hstep i (by omega)
      have hδ1i : ∀ j ∈ Finset.Icc 1 P.q, δ i j ≤ 1 := fun j hj =>
        ((arqpDA_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
      have h11 :=
          (ARqpStep1.radius_bounds hsi.toARqpStep1 hLb0 (hD i hik) (hσpos i hik).le hδ1i hj).2
      have hδ₁ : κ * ε j ≤ δ₁ i j := (le_min (ha i hik j hj) (ih hik j hj)).trans h11
      by_cases hacc : acc i
      · rw [hsi.δ_acc hacc]; exact ih hik j hj
      rw [hsi.radii_trial hacc]
      split_ifs with hc
      · exact (hrc i (by omega)).kappa_mul_le hacc hc.2 hε hLb (hσ i hik) hj
      · exact hδ₁
  intro j hj
  have hδ1k : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1 := fun j hj =>
    ((arqpDA_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
  have h11 := ARqpStep1.radius_bounds hstep1 hLb0 (hD k le_rfl) (hσpos k le_rfl).le hδ1k hj
  exact ⟨(le_min (ha k le_rfl j hj) (hδk k le_rfl j hj)).trans h11.2, h11.1⟩

/-- **The model decrease at a trial iteration** (Lemma 13.1.13 of [cartis2022evaluation]): at a
trial iteration `k ∈ 𝒯` of ARqpIDA (or ARqpEDA) with `ε_{j_k} > 0` and `σ_k ≥ 0`,
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ σ_k/(p+1)! ‖s_k‖^{p+1}` (13.1.76) and
`\overline{ΔT}_{f,p}(x_k, s_k) > 0`, so that the ratio (13.1.58) is well defined. -/
theorem ARqpDAStep.taylorDecrement_ge (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k)
    (hk : ¬ acc k)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, 0 < ε j) (hσ : 0 ≤ σ k) :
    σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) ≤ (D k).taylorDecrement P.p (s k) ∧
      0 < (D k).taylorDecrement P.p (s k) := by
  have h2 := hs.step2_of_not_acc hk
  have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
    have := P.ς_pos; have := hε _ h2.jk_mem; have := hs.radius_pos _ h2.jk_mem; positivity
  have hm := hpos.trans_le (h2.model_dec.trans h2.dec_le)
  rw [arModelDec_eq] at hm
  have : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
  constructor <;> linarith

/-- **The accuracy bound (13.1.73) of Lemma 13.1.12** ([cartis2022evaluation]), for one
iteration of the ARqpIDA step predicate that goes through Step 2: if `‖∇̄^i f(x_k)‖ ≤ L̄` for
`i ∈ [1, p]` (`L̄ ≥ 1`), `σ_k ≥ 0`, any `σ̄`, `ε ∈ (0, 1]^q`, `0 ≤ κ ≤ 1` with
`δ^{(1)}_{k,j} ≥ κ ε_j`,
and `h_{k,i} ≤ κ_s (ς κ^q/(12 q! max(L̄, σ̄)))^p ε_min^{p(q+1)}` for `i ∈ [1, p]`, then the
iteration is not accuracy-improving. -/
theorem ARqpStep2.not_acc_of_le (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hpos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j) {Lb σbar κ : ℝ} (hLb : 1 ≤ Lb)
    (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hδ₁ : ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ₁ k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤
      P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σbar)) ^ P.p *
        epsMin P.q ε ^ (P.p * (P.q + 1))) :
    ¬ acc k := by
  have hq := P.one_le_q
  have hεmin : 0 < epsMin P.q ε := epsMin_pos hq fun j hj => (hε j hj).1
  have hεmin1 : epsMin P.q ε ≤ 1 := epsMin_le_one hq fun j hj => (hε j hj).2
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  set j := jk k
  set em := epsMin P.q ε
  set M := max Lb σbar
  have hM : 1 ≤ M := hLb.trans (le_max_left _ _)
  set c := P.ς * κ ^ P.q / (12 * P.q ! * M) * em ^ (P.q + 1) with hc
  have hfq : (1 : ℝ) ≤ P.q ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc P.ς * κ ^ P.q * em ^ (P.q + 1) ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hς1 (pow_le_one₀ hκ0 hκ1) (by positivity) zero_le_one)
            (pow_le_one₀ hεmin.le hεmin1) (by positivity) (by norm_num)
      _ ≤ 12 * P.q ! * M := by nlinarith
  rw [h2.acc_iff]
  rintro ⟨hs1, i, hi, hlt⟩
  refine absurd hlt (not_lt.2 ?_)
  -- the step is not too short
  have hsc : c ≤ ‖s k‖ := by
    have hup := taylorDecrement_le_two_mul (D := D k) (j := P.p) (zero_le_one.trans hLb) hD hs1.le
    have hm := h2.model_dec.trans h2.dec_le
    rw [arModelDec_eq] at hm
    have hσs : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
    have hlow : P.ς * ε j * δ₁ k j ^ j / j ! / 4 ≤ 2 * Lb * ‖s k‖ := by linarith
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le h2.jk_mem) hκ0).trans (hδ₁ j h2.jk_mem)) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : em ≤ ε j := epsMin_le h2.jk_mem
    have hLbM : 2 * Lb ≤ 3 * M := by have := le_max_left Lb σbar; linarith
    have hnum : P.ς * em * (κ * em) ^ P.q ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεj hς.le) hδj (by positivity)
        (mul_nonneg hς.le (hεmin.le.trans hεj))
    have hN : 0 ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_nonneg (mul_nonneg hς.le (hεmin.le.trans hεj)) (pow_nonneg (hpos j h2.jk_mem).le _)
    calc c = P.ς * em * (κ * em) ^ P.q / (12 * P.q ! * M) := by rw [hc]; ring
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * P.q ! * M) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * j ! * M) :=
          div_le_div_of_nonneg_left hN (by positivity) (by gcongr)
      _ = P.ς * ε j * δ₁ k j ^ j / j ! / 4 / (3 * M) := by field_simp; ring
      _ ≤ 2 * Lb * ‖s k‖ / (3 * M) := div_le_div_of_nonneg_right hlow (by positivity)
      _ ≤ 3 * M * ‖s k‖ / (3 * M) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLbM (norm_nonneg _))
            (by positivity)
      _ = ‖s k‖ := by field_simp
  obtain ⟨hi1, hip⟩ := Finset.mem_Icc.1 hi
  have hcp : c ^ P.p ≤ ‖s k‖ ^ (P.p - i + 1) :=
    (pow_le_pow_of_le_one hc0 hc1 (by omega)).trans (pow_le_pow_left₀ hc0 hsc _)
  calc h k i ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * M)) ^ P.p * em ^ (P.p * (P.q + 1)) :=
        hh i hi
    _ = P.κs * c ^ P.p := by rw [hc, mul_pow, ← pow_mul, mul_assoc, mul_comm (P.q + 1) P.p]
    _ ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := mul_le_mul_of_nonneg_left hcp P.κs_pos.le

end ARStep

/-! ### Step-length algebra for ARqpIDA and ARqpEDA -/

section StepLength

/-- The constant `κ̂ = min(κ, a/(2 q! A))` replacing `κ_{δ,min}` in the step-length bounds for
`q > 2` (Lemmas 13.1.17, 13.1.18). -/
noncomputable def arKappaHat (q : ℕ) (a A κ : ℝ) : ℝ := min κ (a / (2 * q ! * A))

/-- **The step-length bound of Lemma 13.1.17** ([cartis2022evaluation], via Lemma 12.2.12),
from the radius inequality (13.1.79), in the unit-radius mode (`u`, where `δ = 1`) or the
lower-bound mode (`¬ u`): let `a, A > 0`, `ε > 0`, `t ∈ (0, 1)`, `δ > 0`, `j ∈ [1, q]`, `q ≤ p`,
`κ > 0` with `κ ε ≤ δ`, and `δ = 1` if `u`. If
`a ε δ^j/j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1}`, then `a/(2 j! A) ε ≤ t^{p-j+1}` if `u`, and
`a/(2 j! A) κ̂^{j-1} ε^j ≤ t^p` with `κ̂ = min(κ, a/(2 q! A))` if `¬ u`. -/
theorem arqp_pow_ge_of_radius_ineq {a A t ε δ κ : ℝ} {j p q : ℕ} {u : Prop} (ha : 0 < a)
    (hA : 0 < A) (hε : 0 < ε) (ht : 0 < t) (ht1 : t < 1) (hδ : 0 < δ) (hj : j ∈ Finset.Icc 1 q)
    (hqp : q ≤ p) (hκ : 0 < κ) (hκε : κ * ε ≤ δ) (hu : u → δ = 1)
    (hineq : a * ε * δ ^ j / j ! ≤ A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1)) :
    (u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ p := hjq.trans hqp
  have hM : MeasureIneq A 0 a ε δ t j p := by
    rw [measureIneq_iff, zero_mul, add_zero]; exact hineq
  have hfj : (0 : ℝ) < j ! := by positivity
  refine ⟨fun hq => ?_, fun _ => ?_⟩
  · have h1 := hM.div_le_of_le hA.le le_rfl ht (by rw [hu hq]; exact ht1.le) hjp
    rw [add_zero] at h1
    calc a / (2 * j ! * A) * ε = a * ε / j ! / (2 * A) := by field_simp
      _ ≤ t ^ (p - j + 1) := by rw [div_le_iff₀ (by positivity)]; linarith
  · have h1 := pow_ge_of_measure_ineq hM hA ha hε ht ht1.le hδ hj1 hjp hκ hκε
    refine le_trans ?_ h1
    have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
    have hk1 : arKappaHat q a A κ ≤ min κ (a / (A * j !) / 2) := by
      refine min_le_min le_rfl ?_
      rw [div_div, mul_comm (A * j !) 2, ← mul_assoc, mul_right_comm 2 A]
      exact div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
    have hk0 : 0 ≤ arKappaHat q a A κ := le_min hκ.le (by positivity)
    have : a / (2 * j ! * A) = a / (A * j !) / 2 := by field_simp
    rw [this]
    gcongr

/-- The exponent `π_j` of Lemma 13.1.18 in the radii mode `u` (`ARqpDARadiiControl`):
`(p+1)/(p-j+1)` with unit radii (`u`) and `j(p+1)/p` with the lower-bound radii (`¬ u`). -/
noncomputable def arPiOf (u : Prop) [Decidable u] (p j : ℕ) : ℝ :=
  if u then ((p : ℝ) + 1) / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) * ((p : ℝ) + 1) / p

/-- The exponent `π_j` of Lemma 13.1.18: `(p+1)/(p-j+1)` if `q ≤ 2`, `j(p+1)/p` if `q > 2`. -/
noncomputable def arPi (q p j : ℕ) : ℝ := arPiOf (q ≤ 2) p j

/-- The step-length constant of Lemma 13.1.18 in the radii mode `u`:
`(a/(2 q! A))^{(p+1)/(p-q+1)}` with unit radii (`u`), and `(a κ̂^{q-1}/(2 q! A))^{q(p+1)/p}` with
`κ̂ = arKappaHat q a A κ` with the lower-bound radii (`¬ u`). -/
noncomputable def arStepConstOf (u : Prop) [Decidable u] (q p : ℕ) (a A κ : ℝ) : ℝ :=
  if u then (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ))
  else (a * arKappaHat q a A κ ^ (q - 1) / (2 * q ! * A)) ^ ((q : ℝ) * ((p : ℝ) + 1) / p)

/-- The step-length constant of Lemma 13.1.18: `(a/(2 q! A))^{(p+1)/(p-q+1)}` if `q ≤ 2`, and
`(a κ̂^{q-1}/(2 q! A))^{q(p+1)/p}` with `κ̂ = arKappaHat q a A κ` if `q > 2`. -/
noncomputable def arStepConst (q p : ℕ) (a A κ : ℝ) : ℝ := arStepConstOf (q ≤ 2) q p a A κ

theorem arStepConstOf_nonneg {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) : 0 ≤ arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 ≤ arKappaHat q a A κ := le_min hκ (by positivity)
  split_ifs <;> positivity

theorem arStepConstOf_pos {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 < a)
    (hA : 0 < A) (hκ : 0 < κ) : 0 < arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 < arKappaHat q a A κ := lt_min hκ (by positivity)
  split_ifs <;> positivity

theorem arPiOf_nonneg {u : Prop} [Decidable u] {p j : ℕ} : 0 ≤ arPiOf u p j := by
  unfold arPiOf; split_ifs <;> positivity

theorem arStepConst_nonneg {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hκ : 0 ≤ κ) :
    0 ≤ arStepConst q p a A κ :=
  arStepConstOf_nonneg ha hA hκ

theorem arStepConst_pos {q p : ℕ} {a A κ : ℝ} (ha : 0 < a) (hA : 0 < A) (hκ : 0 < κ) :
    0 < arStepConst q p a A κ :=
  arStepConstOf_pos ha hA hκ

theorem arPi_nonneg {q p j : ℕ} : 0 ≤ arPi q p j := arPiOf_nonneg

/-- **From step lengths to decrements** ([cartis2022evaluation], proof of Lemma 13.1.18): with
`0 < a ≤ 1`, `A ≥ 1`, `0 < κ ≤ 1`, `ε ∈ (0, 1]`, `j ∈ [1, q]`, `q ≤ p`, `t > 0`, if either
`t ≥ 1` or the bounds of `arqp_pow_ge_of_radius_ineq` (in the radii mode `u`) hold, then
`arStepConstOf u q p a A κ · ε^{π_j} ≤ t^{p+1}` with `π_j = arPiOf u p j`. -/
theorem arqp_pow_succ_ge {a A t ε κ : ℝ} {j p q : ℕ} {u : Prop} [Decidable u] (ha : 0 < a)
    (ha1 : a ≤ 1) (hA : 1 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hj : j ∈ Finset.Icc 1 q) (hqp : q ≤ p)
    (hb : 1 ≤ t ∨ ((u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p))) :
    arStepConstOf u q p a A κ * ε ^ arPiOf u p j ≤ t ^ (p + 1) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
  set κh := arKappaHat q a A κ
  have hκh0 : 0 < κh := lt_min hκ (by positivity)
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans hκ1
  have hbq0 : 0 < a / (2 * q ! * A) := by positivity
  have hbqj : a / (2 * q ! * A) ≤ a / (2 * j ! * A) :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
  have hbj1 : a / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hbq1 : a / (2 * q ! * A) ≤ 1 := hbqj.trans hbj1
  have hπ := arPiOf_nonneg (u := u) (p := p) (j := j)
  have hC0 := arStepConstOf_nonneg (u := u) (q := q) (p := p) ha.le hA0.le hκ.le
  have hepi : ε ^ arPiOf u p j ≤ 1 := Real.rpow_le_one hε.le hε1 hπ
  have hC1 : arStepConstOf u q p a A κ ≤ 1 := by
    unfold arStepConstOf
    split_ifs
    · exact Real.rpow_le_one hbq0.le hbq1 (by positivity)
    · refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      rw [mul_div_right_comm]
      exact (mul_le_of_le_one_left (by positivity) hbq1).trans (pow_le_one₀ hκh0.le hκh1)
  rcases hb with ht1 | ⟨hq2, hq3⟩
  · exact ((mul_le_of_le_one_left (by positivity) hC1).trans hepi).trans (one_le_pow₀ ht1)
  by_cases hq : u
  · have hX := hq2 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    set m := p - j + 1 with hm
    have hm0 : m ≠ 0 := by omega
    set π := ((p : ℝ) + 1) / (m : ℝ)
    have hππ : π ≤ ((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (by positivity) (by
        have : 0 < p - q + 1 := by omega
        exact_mod_cast this) ?_
      exact_mod_cast (show p - q + 1 ≤ m by omega)
    have hπ0 : 0 ≤ π := by positivity
    calc (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ)) * ε ^ π
        ≤ (a / (2 * q ! * A)) ^ π * ε ^ π :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hbq0 hbq1 hππ)
            (by positivity)
      _ ≤ (a / (2 * j ! * A)) ^ π * ε ^ π := by
          gcongr
      _ = (a / (2 * j ! * A) * ε) ^ π := (Real.mul_rpow (by positivity) hε.le).symm
      _ ≤ (t ^ m) ^ π := Real.rpow_le_rpow (by positivity) hX hπ0
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hm0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
  · have hX := hq3 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    have hp0 : p ≠ 0 := by omega
    have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
    set B := a / (2 * j ! * A) * κh ^ (j - 1)
    set Bq := a * κh ^ (q - 1) / (2 * q ! * A)
    have hBq0 : 0 < Bq := by positivity
    have hBqB : Bq ≤ B := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact mul_le_mul hbqj (pow_le_pow_of_le_one hκh0.le hκh1 (by omega)) (by positivity)
        (by positivity)
    have hBq1 : Bq ≤ 1 := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact (mul_le_of_le_one_left (by positivity) hbq1).trans (pow_le_one₀ hκh0.le hκh1)
    have he : ((p : ℝ) + 1) / p ≤ (q : ℝ) * ((p : ℝ) + 1) / p := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast (by omega : 1 ≤ q))
    have hεpow : (ε ^ j) ^ (((p : ℝ) + 1) / p) = ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_div_assoc]
    calc Bq ^ ((q : ℝ) * ((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p)
        ≤ Bq ^ (((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hBq0 hBq1 he)
            (by positivity)
      _ ≤ B ^ (((p : ℝ) + 1) / p) * (ε ^ j) ^ (((p : ℝ) + 1) / p) := by
          rw [hεpow]; gcongr
      _ = (B * ε ^ j) ^ (((p : ℝ) + 1) / p) :=
          (Real.mul_rpow (by positivity) (by positivity)).symm
      _ ≤ (t ^ p) ^ (((p : ℝ) + 1) / p) := Real.rpow_le_rpow (by positivity) hX (by positivity)
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hp0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf

end StepLength

end Optimization
