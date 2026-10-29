import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA

/-!
# ARqpEDA: adaptive regularization with explicit dynamic accuracy

The adaptive-regularization method ARqpEDA ([cartis2022evaluation], Algorithm 13.3.2): the
iteration `ARqpDAStep` with inexact function values (Step 3, `EDAStep3`), the inexact ratio
`edaRatio` and the certified termination test `edaStopAR`.

The analysis is stated for runs on a feasible set `X` (Step-1 displacements and trial points
in `{e | x_k + e ∈ X}`, [cartis2022evaluation] §14.2) under the smoothness hypothesis
`LipschitzDerivsAnchored f C A 0 p L` with normalized constants `L_j ≥ 1`, `X ⊆ C` and an anchor
set `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`: the objective does not increase along the runs, so the iterates
are anchors, derivative estimates are made at iterates, and trial points are related to them by
Taylor's theorem anchored at the iterate. The unconstrained methods of Chapter 13 are the case
`X = C = A = univ`.

## Main results

* `IsARqpEDARun.sigma_le` (Lemma 13.3.5), `.isEpsDeltaApprox_of_stop`, `.stop_of_pass`
  (Lemma 13.3.6), `.measure_ineq` (the radius inequality replacing Lemma 13.1.16: a successful
  iteration followed by an iteration with unchanged radii that is not accuracy-improving),
  `.step_bound`, `.decrease_ge` (Lemma 13.3.7), `.card_acc_le`, `.complexity` (the complexity
  argument of Theorem 13.3.8), `.complexity_of_radiiControl` (Theorem 14.2.4, ARqpEDA row),
  `.le_card_succ` (Lemma 14.2.3, ARqpEDA row).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpEDA -/

/-- The termination test of ARqpEDA ([cartis2022evaluation], Algorithm 13.3.2, Steps 1.5–1.5.1):
(13.3.15) holds at every order and (13.3.17)
`∑_{i=1}^j h_{k,i} (δ^{(1)}_{k,j})^i/i! ≤ ½ ς ε_j (δ^{(1)}_{k,j})^j/j!` for every `j ∈ [1, q]`. -/
def edaStopAR (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (k : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j) ∧
    ∀ j ∈ Finset.Icc 1 P.q, ∑ i ∈ Finset.Icc 1 j, h k i * δ₁ k j ^ i / i ! ≤
      P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- **ARqpEDA with a feasible set** ([cartis2022evaluation], Algorithm 13.3.2; ARqpEDA-SC of §14.2)
as a run predicate, with the ARqpIDA constants `P` satisfying (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`,
tolerances `ε ∈ (0, 1]^q` with `ε ≤ δ₀`, a feasible starting point `x₀ ∈ X`, the sequences of
ARqpIDA, inexact values `fx`, `fxs` with accuracies `h₀` and recomputation flags `R`: at every
iteration reached the derivatives satisfy (13.3.4) up to order `p` and Step 1 (13.3.14)–(13.3.16)
is performed on `X` (`ARqpStep1`); until termination (`edaStopAR`) every iteration satisfies
`ARqpDAStep` on `X` with the inexact ratio (13.3.19) and, on trial iterations, Step 3
(`EDAStep3`). The method returns `x_ε = x_k` and `δ_ε = δ^{(1)}_k`; the unconstrained method is the
case `X = univ`. -/
structure IsARqpEDARun (f : E → ℝ) (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : E) (x : ℕ → E) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E)
    (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) : Prop where
  /-- (13.3.13). -/
  κs_le : P.κs ≤ min P.η₁ (1 - P.η₂) / 4
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ε_j ≤ δ_{0,j}`. -/
  eps_le : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j
  /-- The starting point. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible. -/
  x₀_mem : x₀ ∈ X
  /-- The initial regularization parameter. -/
  σ_zero : σ 0 = P.σ₀
  /-- The initial radii. -/
  δ_zero : δ 0 = P.δ₀
  /-- The initial accuracies. -/
  h_zero : h 0 = P.h₀
  /-- (13.3.4) at every iteration reached. -/
  oracle : ∀ k, (∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) →
    JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.p (fun i => h k i)
  /-- Step 1 at every iteration reached. -/
  step1 : ∀ k, (∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) → ARqpStep1 X P ε x σ δ δ₁ D dd k
  /-- Steps 1–5 until termination. -/
  run : UntilHit (edaStopAR P ε D δ₁ h dd) fun k =>
    ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
        (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) k ∧
      (¬ acc k → EDAStep3 f P.κs ((D k).taylorDecrement P.p (s k)) x s acc fx fxs h₀ R k)

namespace IsARqpEDARun

variable {f : E → ℝ} {X : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop}
  (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
include hrun

theorem step {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) k :=
  (hrun.run k hk).1

theorem step3 {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k) :
    EDAStep3 f P.κs ((D k).taylorDecrement P.p (s k)) x s acc fx fxs h₀ R k :=
  (hrun.run k hk).2 ha

theorem steps_lt {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)) i :=
  fun _ hi => hrun.step fun j hj => hk j (hj.trans_lt hi)

theorem invariants {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh :=
  arqpDA_invariants (hrun.steps_lt hk) hrun.σ_zero hrun.δ_zero hrun.h_zero

theorem sigma_pos {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : 0 < σ k :=
  P.σmin_pos.trans_le (hrun.invariants hk).1

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaS_le_eta₁ : P.κs ≤ P.η₁ / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

theorem kappaS_le_eta₂ : P.κs ≤ (1 - P.η₂) / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- The iterates reached are feasible. -/
theorem mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : x k ∈ X :=
  arqpDA_mem (hrun.steps_lt hk) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along an ARqpEDA run with a feasible set before termination:
`f(x_k) ≤ f(x₀)`. On a successful iteration the inexact values are within `h_{k,0} ≤ κ_s
\overline{ΔT}_k ≤ η₁/4 \overline{ΔT}_k` of `f` ((13.3.13), (13.3.18)), so `f(x_k) - f(x_{k+1})
≥ η₁/2 \overline{ΔT}_k > 0` (Lemma 13.1.13). -/
theorem objective_le {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i hi => ?_
  have hki : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
  have hs := hrun.step hki
  by_cases hc : ¬ acc i ∧ P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i
  · have h3 := hrun.step3 hki hc.1
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hc.1 (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos fun j hj => hk j (hj.trans hi)).le).2
    have hdec := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
      (h3.fxs_err.trans h3.h₀_le) hc.2 hrun.kappaS_le_eta₁
    have := mul_pos (half_pos P.η₁_pos) hpos
    rw [hs.iterate_succ_eq_add hc.1 hc.2]
    linarith
  · rw [hs.iterate_succ_eq hc]

/-- The iterates reached lie in every set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : x k ∈ A :=
  hAX _ (hrun.mem hk) (hrun.objective_le hk)

/-- (13.1.63) with `κ_{∇,max} = 1`: `‖∇̄^i f(x_k)‖ ≤ L_f + κ_h` for `i ∈ [1, p]`, under the
smoothness hypothesis anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤
f(x₀)}`. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) : ‖D k i‖ ≤ lipMax L P.p + P.κh := by
  have h' : ‖D k i‖ ≤ ‖iteratedFDeriv ℝ i f (x k)‖ + h k i :=
    norm_le_of_jetApprox (hrun.oracle k hk) hi
  have := hf.norm_iteratedFDeriv_le_lipMax hL hi (hrun.mem_anchor hAX hk)
  have := ((hrun.invariants hk).2.2 i hi).2
  linarith

/-- The radii `δ^{(1)}_k` lie in `(0, 1]^q` at every iteration reached. -/
theorem stepOneRadii_mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
  ⟨(hrun.step1 k hk).radius_pos j hj,
    ((hrun.step1 k hk).radius_le j hj).trans ((hrun.invariants hk).2.1 j hj).2⟩

end IsARqpEDARun

section ARqpEDA

variable {X C A : Set E} {f : E → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **The regularization weights stay bounded** (Lemma 13.3.5 of [cartis2022evaluation]): under the
smoothness hypothesis, every iteration `k` reached by ARqpEDA has `σ_k ≤ σ_max` with
`σ_max = arqpIDASigmaMax P L_{f,p} 1` ((13.1.77) with `κ_{∇,max} = 1` and `κ_s' = max(κ_s, κ_h)`).
-/
theorem IsARqpEDARun.sigma_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arqpIDASigmaMax P (L P.p) 1 := by
  set κs' := max P.κs P.κh
  have hκs' : 0 ≤ κs' := P.κs_pos.le.trans (le_max_left _ _)
  set σbar := (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) / (1 - P.η₂)
  set ρ := edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)
  have key : ∀ i < k, ¬ acc i → σbar ≤ σ i → P.η₂ ≤ ρ i := by
    intro i hi ha hσi
    have his : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
    have hilt : ∀ j < i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => his j hj.le
    have hs := hrun.step his
    have h3 := hrun.step3 his ha
    have h2 := hs.step2_of_not_acc ha
    obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hilt).le
    set t := ‖s i‖
    have hherr : ∀ l ∈ Finset.Icc 1 P.p, h i l ≤ 1 * κs' * t ^ (P.p - l + 1) := by
      intro l hl
      rw [one_mul]
      rcases lt_or_ge t 1 with ht | ht
      · exact (h2.accuracy_le_of_not_acc ha ht l hl).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · exact (((hrun.invariants hilt).2.2 l hl).2.trans (le_max_right _ _)).trans
          (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy zero_le_one hκs' (hrun.oracle i hilt)
      hherr le_rfl
    have hR := hf.abs_sub_taylorDecrement_le_of_le le_rfl (hrun.mem_anchor hAX hilt) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) ≤ (1 - P.η₂) * σ i := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσi
      linarith
    have hval := h3.fx_err.trans h3.h₀_le
    have hval' := h3.fxs_err.trans h3.h₀_le
    have hκs4 := hrun.kappaS_le_eta₂
    refine le_div_of_inexact_error_le (fx := f (x i)) (fxs := f (x i + s i))
      (ΔT := (ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i)) hpos ?_
    have htp : 0 ≤ t ^ (P.p + 1) := by positivity
    have hmid : |f (x i + s i) - (f (x i) - (ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i))| +
        |(ftaylorSeries ℝ f (x i)).taylorDecrement P.p (s i) - (D i).taylorDecrement P.p (s i)| ≤
          (1 - P.η₂) / 2 * (D i).taylorDecrement P.p (s i) := by
      calc _ ≤ L P.p / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) + 2 * κs' * 1 * t ^ (P.p + 1) :=
            add_le_add hR (by rw [abs_sub_comm]; exact hE)
        _ = (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) / (2 * (P.p + 1)!) * t ^ (P.p + 1) := by
            field_simp; ring
        _ ≤ (1 - P.η₂) * σ i / (2 * (P.p + 1)!) * t ^ (P.p + 1) := by gcongr
        _ = (1 - P.η₂) / 2 * (σ i / ((P.p + 1)! : ℝ) * t ^ (P.p + 1)) := by ring
        _ ≤ (1 - P.η₂) / 2 * (D i).taylorDecrement P.p (s i) :=
            mul_le_mul_of_nonneg_left hlow (by linarith [P.one_sub_η₂_pos])
    nlinarith
  have h := sigma_le_max_of_arUpdate_of_neutral (σ := σ) (K := k) (σbar := σbar)
    (ρ := ρ) P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃ (hrun.σ_zero ▸ P.σ₀_pos) (fun i hi => by
      have his : ∀ j ≤ i, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (hj.trans_lt hi)
      by_cases ha : acc i
      · exact Or.inl ((hrun.step his).σ_acc ha)
      · exact Or.inr ⟨(hrun.step his).update ha, key i hi ha⟩) k le_rfl
  rw [hrun.σ_zero] at h
  exact h

/-- **Termination certifies approximate optimality** (Lemma 13.3.6 (i) of [cartis2022evaluation]):
if ARqpEDA terminates at iteration `k` (Step 1.5.1), then `x_k` is an `(ε, δ^{(1)}_k)`-approximate
`q`-th order minimizer with `δ^{(1)}_k ∈ (0, 1]^q`. -/
theorem IsARqpEDARun.isEpsDeltaApprox_of_stop
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
  have hmem := hrun.stepOneRadii_mem hk
  refine ⟨hmem, fun j hj => ?_⟩
  have hor := (hrun.oracle k hk).mono P.q_le_p
  have hw := ((hrun.step1 k hk).witness j hj).2
  have hεj := hrun.eps_mem j hj
  refine taylorMeasure_le_of_inexact_certificate hor (Finset.mem_Icc.1 hj).2
    (by simpa using hrun.mem hk)
    (hmem j hj).1.le P.ς_pos hw (hstop.1 j hj) ((hstop.2 j hj).trans ?_)
  have : P.ς * ε j ≤ ε j := mul_le_of_le_one_left hεj.1.le P.ς_le_one
  have h0 : 0 ≤ δ₁ k j ^ j / (j ! : ℝ) := by have := (hmem j hj).1; positivity
  calc P.ς * ε j * δ₁ k j ^ j / j ! / 2 = P.ς * ε j * (δ₁ k j ^ j / j !) / 2 := by ring
    _ ≤ ε j * (δ₁ k j ^ j / j !) / 2 := by gcongr
    _ = ε j * δ₁ k j ^ j / j ! / 2 := by ring

/-- **Accurate data give termination** (Lemma 13.3.6 (ii) of [cartis2022evaluation]): under the
smoothness hypothesis and the radii control at every iteration, if (13.3.15) holds at every order at
an iteration `k` reached by ARqpEDA and (13.1.78) holds with `κ_{∇,max} = 1`,
`h_{k,i} ≤ ς κ^{(1)}_δ(σ_max)^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, p]` (`σ_max` of Lemma 13.3.5,
`L̄_f = L_f + κ_h`), then (13.3.17) holds and the method terminates at `k`. -/
theorem IsARqpEDARun.stop_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.ς * arKappaDelta1 P (lipMax L P.p + P.κh)
      (arqpIDASigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k := by
  refine ⟨hpass, fun j hj => ?_⟩
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := arqpDA_radius_ge (hrun.steps_lt hk) (hrun.step1 k hk) hrun.σ_zero hrun.δ_zero
    hrun.h_zero hrun.eps_mem hrun.eps_le hLb
    (fun i hi ℓ hℓ => hrun.norm_D_le hf hL hAX (fun l hl => hk l (hl.trans_le hi)) hℓ)
    (fun i hi => IsARqpEDARun.sigma_le hf hXC hAX hrun fun l hl => hk l (hl.trans_le hi))
    (fun i _ => hrc i)
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hmem := hrun.stepOneRadii_mem hk j hj
  set δ := δ₁ k j
  set em := epsMin P.q ε
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hεj := hrun.eps_mem j hj
  set e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)
  have he0 : 0 ≤ e := by positivity
  have hm0 : 0 ≤ κ * em := by positivity
  have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
  have hδj : (κ * em) ^ P.q ≤ δ ^ j :=
    (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
      ((mul_le_mul_of_nonneg_left (epsMin_le hj) hκ0.le).trans (hrad j hj).1) j)
  have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
  calc ∑ i ∈ Finset.Icc 1 j, h k i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 j, e * (δ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right
          (hh i (Finset.Icc_subset_Icc le_rfl (hjq.trans P.q_le_p) hi)) (by
            have := hmem.1; positivity)
    _ = e * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ e * 2 := mul_le_mul_of_nonneg_left
        ((sum_pow_div_factorial_le_two_mul hmem.1.le hmem.2 _).trans (by linarith [hmem.2])) he0
    _ = P.ς * em * (κ * em) ^ P.q / (2 * P.q !) := by simp only [e]; ring
    _ ≤ P.ς * ε j * δ ^ j / (2 * P.q !) :=
        div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left (epsMin_le hj) hς.le)
          hδj (by positivity) (mul_nonneg hς.le hεj.1.le)) (by positivity)
    _ ≤ P.ς * ε j * δ ^ j / (2 * j !) := by
        gcongr
        exact mul_nonneg (mul_nonneg hς.le hεj.1.le) (pow_nonneg hmem.1.le _)
    _ = P.ς * ε j * δ ^ j / j ! / 2 := by ring

/-- **The radius inequality for ARqpEDA** (the counterpart of Lemmas 13.1.16–13.1.17 of
[cartis2022evaluation] for inexact function values). Under the smoothness hypothesis, let iteration
`k` of ARqpEDA (reached, not terminal) be successful with `‖s_k‖ < 1`, and suppose that Step 1 at
`k + 1` does not pass every test (13.3.15) with unchanged radii (i.e. it halves some radius or
branches to Step 2). Then for some `j ∈ [1, q]`, with `δ = δ_{k+1,j} = δ_{s_k,j}`,
`(ς/2 - θ) ε_j δ^j/j! ≤ (L_{f,p} + σ_max + 4 κ_s) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}` (`σ_max` of Lemma
13.3.5). Proof: Step 1 at `k + 1` provides a displacement in `B_δ` with a large inexact decrement,
whence `φ^δ_{f,j}(x_{k+1}) > ½ ς ε_j δ^j/j! - κ_s ∑_ℓ δ^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}` (the accuracies are
inherited from iteration `k`), and the model-optimality conditions (13.1.57) at `s_k`. -/
theorem IsARqpEDARun.measure_ineq (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hs1 : ‖s k‖ < 1)
    (hnot : ¬ ((∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd (k + 1) j) ∧
      ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 P.q, (P.ς / 2 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step hk
  have h2 := hs.step2_of_not_acc ha
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have hk1 : ∀ j < k + 1, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (Nat.lt_succ_iff.1 hj)
  have hS1 := hrun.step1 (k + 1) hk1
  -- a large inexact decrement at `x_{k+1}`
  obtain ⟨j, hj, d₀, hd₀n, hd₀X, hd₀⟩ : ∃ j ∈ Finset.Icc 1 P.q, ∃ d₀, ‖d₀‖ ≤ δ (k + 1) j ∧
      x (k + 1) + d₀ ∈ X ∧
      P.ς * ε j * δ (k + 1) j ^ j / j ! / 2 < (D (k + 1)).taylorDecrement j d₀ := by
    by_cases hall : ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j
    · have : ¬ ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd (k + 1) j := fun hp => hnot ⟨hp, hall⟩
      push Not at this
      obtain ⟨j, hj, hfail⟩ := this
      refine ⟨j, hj, dd (k + 1) j, ?_, (hS1.witness j hj).mem, ?_⟩
      · rw [← hall j hj]; exact (hS1.witness j hj).norm_le
      · unfold arqpDAPass at hfail; rw [← hall j hj]; exact not_le.1 hfail
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      obtain ⟨-, -, d₀, hd₀n, hd₀X, hd₀⟩ :=
        hS1.halving j hj (lt_of_le_of_ne (hS1.radius_le j hj) hne)
      exact ⟨j, hj, d₀, hd₀n, hd₀X, hd₀⟩
  refine ⟨j, hj, ?_⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ P.p := hjq.trans P.q_le_p
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add ha hρ
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial ha, ite_eq_left ⟨hρ, hs1⟩]
  have hh : h (k + 1) = h k := hs.h_trial ha
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  set δv := δ (k + 1) j with hδv
  have hδv0 : 0 ≤ δv := by rw [hδv, hδ]; exact hδmem.1.le
  -- the exact measure at `x_{k+1}`
  have hbar : P.ς * ε j * δv ^ j / j ! / 2 <
      taylorMeasure (D (k + 1)) j δv {e | x (k + 1) + e ∈ X} :=
    hd₀.trans_le (taylorDecrement_le_taylorMeasure _ j ⟨mem_closedBall_zero_iff.2 hd₀n, hd₀X⟩)
  have hor1 := hrun.oracle (k + 1) hk1
  have htrans := taylorMeasure_le_add_of_jetApprox hor1.symm hjp
    (show (0 : E) ∈ {e | x (k + 1) + e ∈ X} by simpa using hrun.mem hk1) hδv0
  rw [hh] at htrans
  set e₀ := P.κs * ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) with he₀def
  have hacc := h2.accuracy_le_of_not_acc ha hs1
  have he₀ : ∑ i ∈ Finset.Icc 1 j, h k i * δv ^ i / i ! ≤ e₀ := by
    rw [he₀def, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hacc i (Finset.Icc_subset_Icc le_rfl hjp hi)
    have h0 : 0 ≤ δv ^ i / (i ! : ℝ) := by positivity
    calc h k i * δv ^ i / i ! = h k i * (δv ^ i / i !) := by ring
      _ ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) * (δv ^ i / i !) := mul_le_mul_of_nonneg_right this h0
      _ = P.κs * (δv ^ i / i ! * ‖s k‖ ^ (P.p - i + 1)) := by ring
  have h₁ : P.ς / 2 * ε j * δv ^ j / (j ! : ℝ) - e₀ <
      taylorMeasure (ftaylorSeries ℝ f (x k + s k)) j δv {e | x k + s k + e ∈ X} := by
    rw [← hx]
    have : P.ς / 2 * ε j * δv ^ j / (j ! : ℝ) = P.ς * ε j * δv ^ j / j ! / 2 := by ring
    linarith
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j δv
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δv ^ j / j ! := by
    have hw := hdm.2
    rw [hδv, hδ]
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring]
      at this
    exact le_of_mul_le_mul_left this hς
  have hxA := hrun.mem_anchor hAX hklt
  have := radius_inequality_of_measure_gt_anchored hf.convex
    (fun y hy => hf.contDiffAt_of_le le_rfl hy) (hf.lipschitzAt_of_le le_rfl hxA)
    (zero_le_one.trans (hL _ le_rfl)) (hf.subset hxA)
    (hXC h2.mem) (hrun.oracle k hklt) zero_le_one P.κs_pos.le
    (fun i hi => by rw [one_mul]; exact hacc i hi)
    (hrun.sigma_pos hklt).le (IsARqpEDARun.sigma_le hf hXC hAX hrun hklt) hjp
    (by simpa using h2.mem)
    hδv0 h₁ h₂
  have e : (L P.p + arqpIDASigmaMax P (L P.p) 1 + 3 * 1 * P.κs) *
      ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) + e₀ =
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by ring
  rw [e] at this
  exact this.le

/-- The constant `L_{f,p} + σ_max + 4 κ_s` of the ARqpEDA radius inequality
(`σ_max = arqpIDASigmaMax P L_{f,p} 1`, Lemma 13.3.5). -/
noncomputable def arEDAConstA (P : ARqpIDAParams) (L : ℕ → ℝ) : ℝ :=
  L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs

theorem one_le_arEDAConstA {P : ARqpIDAParams} {L : ℕ → ℝ} (hL : 1 ≤ L P.p) :
    1 ≤ arEDAConstA P L := by
  have h1 : 0 ≤ arqpIDASigmaMax P (L P.p) 1 := P.σ₀_pos.le.trans (le_max_left _ _)
  have := P.κs_pos
  unfold arEDAConstA; linarith

/-- Step 1 at iteration `i` passes every test (13.3.15) with unchanged radii. -/
def edaPassUnchanged (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (i : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd i j) ∧ ∀ j ∈ Finset.Icc 1 P.q, δ₁ i j = δ i j

/-- The step-length bounds of ARqpEDA (as `IsARqpIDARun.step_bound`): at a successful iteration `k`
reached by ARqpEDA with the radii control at `k`, such that `‖s_k‖ ≥ 1` or Step 1 at `k + 1`
does not pass with unchanged radii, either `‖s_k‖ ≥ 1` or the conclusions of
`arqp_pow_ge_of_radius_ineq` hold for some order `j` with `a = ς/2 - θ` (`θ < ς/2`), `A =
L_{f,p} + σ_max + 4 κ_s` and `κ = κ_{δ,min}`. -/
theorem IsARqpEDARun.step_bound (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) *
          arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (j - 1) *
            ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  have hnot := hgood.resolve_left (not_le.2 hs1)
  obtain ⟨j, hj, hineq⟩ := IsARqpEDARun.measure_ineq hf hL hXC hAX hrun hk ha hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step hk
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have h2 := hs.step2_of_not_acc ha
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial ha, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le ha hs1 hrun.eps_mem hLb (IsARqpEDARun.sigma_le hf hXC hAX hrun hklt) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc ha hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hklt).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arEDAConstA P L := zero_lt_one.trans_le (one_le_arEDAConstA (hL _ le_rfl))
  exact arqp_pow_ge_of_radius_ineq (by linarith) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- **Sufficient decrease** (Lemma 13.3.7 of [cartis2022evaluation]): under the smoothness
hypothesis, the radii control at `k` and `θ < ς/2`, let iteration `k` of ARqpEDA (before
termination) be successful, and let `‖s_k‖ ≥ 1` or Step 1 at `k + 1` not pass with unchanged
radii. Then `\overline{ΔT}_{f,p}(x_k, s_k) ≥ κ'_{Δm} min_j ε_j^{π_j}` and `f(x_k) - f(x_{k+1})
≥ ½ η₁ κ'_{Δm} min_j ε_j^{π_j}`, where `κ'_{Δm}` is `κ_{Δm}` of Lemma 13.1.18 with `ς/2 - θ`
for `1 - θ`, `L_{f,p} + σ_max + 4 κ_s` for `L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` (`σ_max` of
Lemma 13.3.5) and `L̄_f = L_f + κ_h`. (The remaining successful iterations are followed by an
accuracy-improving iteration, Step 1 → Step 5.) -/
theorem IsARqpEDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} [Decidable u] (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨j, hj, hb⟩ := IsARqpEDARun.step_bound hf hL hXC hAX hrun hrc hθ hk ha hρ hgood
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have hs := hrun.step hk
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs ha (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos hklt).le
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hL _ le_rfl)
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have ha1 : P.ς / 2 - P.θ ≤ 1 := by linarith [P.ς_le_one, P.θ_pos]
  have hC := arqp_pow_succ_ge ha0 ha1 hA hεj.1 hεj.2 ht
    (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf u P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
    (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg ha0.le (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Optimization.epsMin_pos P.one_le_q fun j hj =>
      Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
  have hσ := (hrun.invariants hklt).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf u P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  refine ⟨h1, ?_⟩
  have h3 := hrun.step3 hk ha
  have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
    (h3.fxs_err.trans h3.h₀_le) hρ hrun.kappaS_le_eta₁
  rw [(hs.accept ha).eq_add hρ]
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ / 2 * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by ring
    _ ≤ P.η₁ / 2 * (D k).taylorDecrement P.p (s k) := by gcongr
    _ ≤ f (x k) - f (x k + s k) := h2

/-- **The accuracy-improving iterations of ARqpEDA with a feasible set** (proof of Theorem 13.3.8,
[cartis2022evaluation]): under `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`, `A ⊇ {y ∈ X |
f(y) ≤ f(x₀)}`) and the radii control at every iteration, if the run has not terminated at any
`j ≤ k`, then `|𝒜_k| ≤ p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem IsARqpEDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
          (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
          P.κh)| / |Real.log P.γh| + 1 := by
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set σmax := arqpIDASigmaMax P (L P.p) 1
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  set κacc := arKappaAcc P κ Lb σmax 1
  have hκacc : 0 < κacc := arKappaAcc_pos hκ0 (by linarith) zero_le_one
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.p * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith)
  have h := card_accuracyImproving_le_of_pow_of_nonneg (acc := acc)
    (hmax := fun j => ordMax P.p (h j))
    (N := P.p * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_nonneg hκacc hεmin
    ((ordMax_le_iff hp).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j hj => (ordMax_le_iff hp).2 fun i hi =>
      ((hrun.invariants fun l hl => hk l (by omega)).2.2 i hi).2)
    (fun j hj ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from
        funext ((hrun.step fun i hi => hk i (hi.trans hj)).h_acc ha),
        ordMax_mul hp P.γh_pos.le])
    (fun j hj ha => by rw [(hrun.step fun i hi => hk i (hi.trans hj)).h_trial ha])
    (fun j hj ha => by
      have hjs : ∀ i ≤ j, ¬ stop i := fun i hi => hk i (hi.trans hj)
      have hjlt : ∀ i < j, ¬ stop i := fun i hi => hjs i hi.le
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.p, h j i ≤ κacc * em ^ (P.p * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd j i
      · have hrad := arqpDA_radius_ge (hrun.steps_lt hjlt) (hrun.step1 j hjlt) hrun.σ_zero
          hrun.δ_zero hrun.h_zero hrun.eps_mem hrun.eps_le hLb
          (fun i hi ℓ hℓ => hrun.norm_D_le hf hL hAX (fun l hl => hjlt l (hl.trans_le hi)) hℓ)
          (fun i hi => IsARqpEDARun.sigma_le hf hXC hAX hrun fun l hl => hjlt l (hl.trans_le hi))
          (fun i _ => hrc i)
        refine (((hrun.step hjs).step2 hfail).not_acc_of_le (σbar := σmax)
          (hrun.step1 j hjlt).radius_pos hLb (fun i hi => hrun.norm_D_le hf hL hAX hjlt hi)
          (hrun.sigma_pos hjlt).le hκ0.le (arKappaDelta1_le_one hLb) hrun.eps_mem
          (fun l hl => (hrad l hl).1) fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hjs j le_rfl
            (IsARqpEDARun.stop_of_pass hf hL hXC hAX hrun hrc hjlt hfail fun i hi => ?_)
        calc h j i ≤ κacc * em ^ (P.p * (P.q + 1)) := hhi i hi
          _ = 1 * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le zero_le_one) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **The complexity argument for ARqpEDA** (proof of Theorem 13.3.8 of [cartis2022evaluation]), for
any decrease constant: under the smoothness hypothesis, f.Bb, the radii control at every iteration,
if every successful iteration `k` of an ARqpEDA run (before termination) with `‖s_k‖ ≥ 1` or Step 1
at `k + 1` not passing with unchanged radii decreases `f` by at least `c > 0`, then the run
terminates at some `k_ε`, `x_{k_ε}` is an `(ε, δ^{(1)}_{k_ε})`-approximate `q`-th order minimizer
with `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, and with `N = (f(x₀) - f_low)/c`,
`M = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` (a bound on the number of
accuracy-improving iterations) and `c_T = 1 + |log γ₁|/log γ₂`, at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates are made. (The successful iterations not covered by the decrease are followed
by an accuracy-improving iteration, hence at most `M` of them.) -/
theorem IsARqpEDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {c : ℝ}
    (hc : 0 < c)
    (hdec : ∀ k, (∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) → ¬ acc k →
      P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k →
      (1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) → c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / c + (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / c + 2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set ρ := edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  set σmax := arqpIDASigmaMax P (L P.p) 1
  have hσ₀ : P.σ₀ ≤ σmax := le_max_left _ _
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  set N := (f x₀ - flow) / c with hN_def
  have hN0 : 0 ≤ N := by positivity
  -- accuracy-improving iterations
  set κacc := arKappaAcc P κ Lb σmax 1
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hA : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsARqpEDARun.card_acc_le hf hL hXC hAX hrun hrc hk
  -- the objective does not increase before termination
  have hmono : ∀ j, (∀ i ≤ j, ¬ stop i) → f (x (j + 1)) ≤ f (x j) := by
    intro j hj
    have hs := hrun.step hj
    by_cases hsucc : ¬ acc j ∧ P.η₁ ≤ ρ j
    · have hjlt : ∀ i < j, ¬ stop i := fun i hi => hj i hi.le
      have h3 := hrun.step3 hj hsucc.1
      have hpos := (ARqpDAStep.taylorDecrement_ge hs hsucc.1 (fun l hl => (hrun.eps_mem l hl).1)
        (hrun.sigma_pos hjlt).le).2
      have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
        (h3.fxs_err.trans h3.h₀_le) hsucc.2 hrun.kappaS_le_eta₁
      rw [(hs.accept hsucc.1).eq_add hsucc.2]
      have := mul_pos (half_pos P.η₁_pos) hpos
      linarith
    · rw [hs.iterate_succ_eq hsucc]
  -- successful iterations
  set good : ℕ → Prop := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i ∧
    (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))
  set bad : ℕ → Prop := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i ∧
    ¬ (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))
  have hgood : ∀ k, (∀ j ≤ k + 1, ¬ stop j) → ((successSet good k).card : ℝ) ≤ N := by
    intro k hk
    rw [hN_def, le_div_iff₀ hc, mul_comm, ← hrun.x_zero]
    exact card_mul_le_of_decrease («φ» := fun i => f (x i)) successSet_subset_range
      (fun j hj => hmono j fun i hi => hk i (by omega))
      (fun j hj => by
        rw [mem_successSet] at hj
        exact hdec j (fun i hi => hk i (by omega)) hj.2.1 hj.2.2.1 hj.2.2.2)
      (hb _ (hrun.mem fun i hi => hk i hi.le))
  have hbad : ∀ k, (∀ j ≤ k + 1, ¬ stop j) →
      (successSet bad k).card ≤ (successSet acc (k + 1)).card := by
    intro k hk
    refine Finset.card_le_card_of_injOn (fun i => i + 1) (fun i hi => ?_)
      (fun a _ b _ hab => by simpa using hab)
    rw [Finset.mem_coe, mem_successSet] at hi ⊢
    obtain ⟨hik, -, -, hpu⟩ := hi
    push Not at hpu
    exact ⟨Nat.succ_le_succ hik,
      (hrun.step fun l hl => hk l (hl.trans (Nat.succ_le_succ hik))).acc_of_pass hpu.2.1⟩
  have hS : ∀ k, (∀ j ≤ k, ¬ stop j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card : ℝ) ≤ N + NA + 1 := by
    intro k hk
    cases k with
    | zero =>
      have : (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) 0).card ≤ 1 := card_successSet_le
      have : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) 0).card : ℝ) ≤ 1 := by
        exact_mod_cast this
      linarith
    | succ k =>
      have h1 : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (k + 1)).card : ℝ) ≤
          (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card + 1 := by
        exact_mod_cast card_successSet_add_one_le
      have hset : successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k =
          successSet (fun i => good i ∨ bad i) k := by
        ext i
        simp only [mem_successSet, good, bad]
        constructor
        · rintro ⟨hi, ha, hr⟩
          exact ⟨hi, (Classical.em (1 ≤ ‖s i‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (i + 1))).imp
            (fun h' => ⟨ha, hr, h'⟩) fun h' => ⟨ha, hr, h'⟩⟩
        · rintro ⟨hi, (⟨ha, hr, -⟩ | ⟨ha, hr, -⟩)⟩ <;> exact ⟨hi, ha, hr⟩
      have h2 := card_successSet_or (succ := good) (succ' := bad) (k := k)
        fun i _ hg hb => hb.2.2 hg.2.2
      rw [← hset] at h2
      have h3 := hgood k hk
      have h4 : ((successSet bad k).card : ℝ) ≤ (successSet acc (k + 1)).card := by
        exact_mod_cast hbad k hk
      have h5 := hA (k + 1) hk
      have : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card : ℝ) =
          (successSet good k).card + (successSet bad k).card := by exact_mod_cast h2
      linarith
  -- trial iterations
  have hlog2 : 0 < Real.log P.γ₂ := P.log_γ₂_pos
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂ with hcT
  have hcT0 : 0 ≤ cT := by positivity
  set NT := (N + NA + 1) * cT + Real.log (σmax / P.σ₀) / Real.log P.γ₂ with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ Real.log (σmax / P.σ₀) := Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)
    positivity
  have hT : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have h1 := arqpDA_card_trial_le (fun i hi => hrun.step fun j hj => hk j (hj.trans hi))
      hrun.σ_zero hrun.δ_zero hrun.h_zero
      (IsARqpEDARun.sigma_le hf hXC hAX hrun fun j hj => hk j (Nat.lt_succ_iff.1 hj))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ ρ i)) kε : ℝ) + 1 ≤
      derivEvalCount acc kε + derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hklt : ∀ j < kε, ¬ stop j := fun j hj => hkε.not_test_of_lt hj
  obtain ⟨hmem, happrox⟩ := IsARqpEDARun.isEpsDeltaApprox_of_stop hrun hklt hkε.test
  refine ⟨kε, hkε, hmem, happrox, ?_, ?_⟩
  · have := edaFunEvalCount_le acc R kε
    calc (edaFunEvalCount acc R kε : ℝ) ≤ 2 * ((derivEvalCount (fun i => ¬ acc i) kε : ℝ) - 1) :=
          this
      _ ≤ 2 * NT := by linarith
      _ = _ := by rw [hNT_def, hN_def, hNA_def]
  · calc _ ≤ (NA + 1) + (N + NA + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def, hN_def]; ring

end ARqpEDA

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}

/-- **Counting the trial iterations of a run** (Lemma 14.2.3 of [cartis2022evaluation]): for an
ARqpEDA run with a feasible set under `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`) and the radii control, every iteration `k` reached (up to and
including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with
`κ_uns = 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`,
`N_𝒜 = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control
(`ARqpDARadiiControl u`) may be in either mode (unit radii, or the (12.2.51)-type lower bounds
at every order). -/
theorem IsARqpEDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := arqpDA_card_trial_le (fun i hi => hrun.step fun j hj => hk' j (hj.trans hi))
    hrun.σ_zero hrun.δ_zero hrun.h_zero (IsARqpEDARun.sigma_le hf hXC hAX hrun hk)
  have hA := IsARqpEDARun.card_acc_le hf hL hXC hAX hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Evaluation complexity under the radii control** (Theorem 14.2.4 of [cartis2022evaluation]):
under `f ≥ f_low` on `X`, `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`), the radii control at every iteration and `θ < ς/2`, every ARqpEDA run
with a feasible set terminates at some `k_ε` with `x_{k_ε} ∈ X` an `(ε, δ^{(1)}_{k_ε})`-approximate
`q`-th order minimizer on `X`, `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, after at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates, where `N = (f(x₀) - f_low)/c` with `c = ½ η₁ κ'_{Δm} min_j ε_j^{π_j}` the
decrease of Lemma 14.2.2, `M = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` and
`c_T = 1 + |log γ₁|/log γ₂` (as in Theorem 13.3.8), with the radii control in either mode `u`
(`ARqpDARadiiControl`): unit radii `δ_{s_k} = 1` (`u`), which Step 2 guarantees for `X = E` with
`q ≤ 2` or for `q = 1` with `X` convex, with `π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type
lower bounds at every order (`¬ u`), available for every `q` and `X`, with `π_j = j(p+1)/p`
(`π_j = arPiOf u p j`; the radii control of Theorem 13.1.19, `RadiiControl`, is the mode
`u = (q ≤ 2)`). -/
theorem IsARqpEDARun.complexity_of_radiiControl (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpEDARun f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    [Decidable u] (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧ x kε ∈ X ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (((f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
              (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
              epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p
            (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := one_le_lipMax hL; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hL _ le_rfl)
  have hC := arStepConstOf_pos (u := u) (q := P.q) (p := P.p) (sub_pos.2 hθ)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + P.κh)
      (σ := arqpIDASigmaMax P (L P.p) 1) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
      (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := IsARqpEDARun.complexity hf hL hXC hAX hb hrun hrc hc
    fun k hk ha hρ hgood =>
        (IsARqpEDARun.decrease_ge hf hL hXC hAX hrun (hrc k) hθ hk ha hρ hgood).2
  exact ⟨kε, hk, hrun.mem fun j hj => hk.2 j hj, hmem, happ, h1, h2⟩

end Iterations

end Optimization
