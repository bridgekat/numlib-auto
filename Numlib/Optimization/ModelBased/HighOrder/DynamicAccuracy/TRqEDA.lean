import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA

/-!
# TRqEDA: a trust-region method with explicit dynamic accuracy

The trust-region method TRqEDA ([cartis2022evaluation], Algorithm 13.3.1): derivatives within
the requested accuracies (normalized error constants, (13.3.3)–(13.3.4)), inexact function
values with accuracy `h_{k,0} ≤ κ_s \overline{ΔT}_k` (Step 3, `EDAStep3`) and a certified
termination test (`edaStopTR`). The iterations before termination are `TRqDAStep`s with the
inexact ratio `edaRatio`.

The analysis is stated for runs on a feasible set `X` (Step-1 displacements and trial points
in `{e | x_k + e ∈ X}`, [cartis2022evaluation] §14.2) under the smoothness hypothesis
`LipschitzDerivsAnchored f C A 0 q L` with normalized constants `L_j ≥ 1`, `X ⊆ C` and an anchor
set `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`: the objective does not increase along the runs, so the iterates
are anchors, derivative estimates are made at iterates, and trial points are related to them by
Taylor's theorem anchored at the iterate. The unconstrained methods of Chapter 13 are the case
`X = C = A = univ`. (With inexact values a successful iteration still decreases `f`, since
`κ_s ≤ η₁/4`.)

## Main definitions

* `edaRatio`, `EDAStep3`, `edaFunEvalCount`: Step 3 and the function-evaluation count (shared
  with ARqpEDA);
* `edaStopTR`, `IsTRqEDARun`.

## Main results

* `IsTRqEDARun.ratio_ge`, `.delta_ge`, `.decrease_ge` (Lemmas 13.3.1–13.3.2),
  `.isEpsDeltaApprox_of_stop`, `.stop_of_pass` (Lemma 13.3.3), `.card_acc_le`,
  `.complexity` (Theorem 13.3.4), `.le_card_succ` (Lemma 14.2.3, TRqEDA row).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Step 3 with inexact function values -/

/-- The ratio (13.3.10), (13.3.19) with inexact function values:
`ρ_k = (f̄(x_k) - f̄(x_k + s_k)) / \overline{ΔT}_k`. -/
noncomputable def edaRatio (fx fxs pred : ℕ → ℝ) (k : ℕ) : ℝ := (fx k - fxs k) / pred k

/-- **Step 3 of TRqEDA and ARqpEDA** ([cartis2022evaluation], (13.3.1)–(13.3.2), (13.3.9),
(13.3.18)) at a trial iteration `k`, for the predicted decrease `ΔTb = \overline{ΔT}`: the
requested value accuracy satisfies `0 < h_{k,0} ≤ κ_s ΔTb`, the values `f̄(x_k)` and
`f̄(x_k + s_k)` are within `h_{k,0}` of `f`, and if `f̄(x_k)` is not recomputed (`¬ R k`) it is the
trial value of an earlier trial iteration at the same point. -/
structure EDAStep3 (f : E → ℝ) (κs ΔTb : ℝ) (x s : ℕ → E) (acc : ℕ → Prop)
    (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) (k : ℕ) : Prop where
  /-- `h_{k,0} > 0`. -/
  h₀_pos : 0 < h₀ k
  /-- (13.3.9), (13.3.18). -/
  h₀_le : h₀ k ≤ κs * ΔTb
  /-- (13.3.2). -/
  fxs_err : |fxs k - f (x k + s k)| ≤ h₀ k
  /-- (13.3.1). -/
  fx_err : |fx k - f (x k)| ≤ h₀ k
  /-- Reuse of `f̄(x_{k-1} + s_{k-1})`. -/
  reuse : ¬ R k → ∃ i < k, ¬ acc i ∧ x i + s i = x k ∧ fx k = fxs i

open Classical in
/-- The number of inexact function evaluations of an EDA method up to iteration `k`: one per trial
iteration `i < k`, plus one when `f̄(x_i)` is recomputed (`R i`). -/
noncomputable def edaFunEvalCount (acc R : ℕ → Prop) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => ¬ acc i).card +
    ((Finset.range k).filter fun i => ¬ acc i ∧ R i).card

/-- At most two function evaluations per trial iteration:
`edaFunEvalCount acc R k ≤ 2 (derivEvalCount (¬ acc) k - 1)`. -/
theorem edaFunEvalCount_le (acc R : ℕ → Prop) (k : ℕ) :
    (edaFunEvalCount acc R k : ℝ) ≤ 2 * ((derivEvalCount (fun i => ¬ acc i) k : ℝ) - 1) := by
  classical
  have h1 : ((Finset.range k).filter fun i => ¬ acc i ∧ R i).card ≤
      ((Finset.range k).filter fun i => ¬ acc i).card :=
    Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
  have h2 : derivEvalCount (fun i => ¬ acc i) k =
      ((Finset.range k).filter fun i => ¬ acc i).card + 1 := by
    rw [derivEvalCount]; congr 2; ext i; simp
  rw [edaFunEvalCount, h2]
  push_cast
  have : (((Finset.range k).filter fun i => ¬ acc i ∧ R i).card : ℝ) ≤
      ((Finset.range k).filter fun i => ¬ acc i).card := by exact_mod_cast h1
  linarith

/-! ### TRqEDA -/

/-- The termination test of TRqEDA ([cartis2022evaluation], Algorithm 13.3.1, Steps 1.4–1.4.1):
(13.3.7) fails at every order and (13.3.8) `∑_{i=1}^q h_{k,i} δ_k^i/i! ≤ ½ ς ε_min δ_k^q/q!`. -/
def edaStopTR (P : TRqIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (k : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j) ∧
    ∑ i ∈ Finset.Icc 1 P.q, h k i * trRadius P Δ k ^ i / i ! ≤
      P.ς * epsMin P.q ε * trRadius P Δ k ^ P.q / P.q ! / 2

/-- **TRqEDA with a feasible set** ([cartis2022evaluation], Algorithm 13.3.1; TRqEDA-SC of §14.2) as
a run predicate, with the TRqIDA constants `P` satisfying (13.3.5) `κ_s ≤ min(η₁, 1 - η₂)/4`,
tolerances `ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, a feasible starting point `x₀ ∈ X`, the sequences of
TRqIDA, inexact values `fx`, `fxs` with accuracies `h₀` and recomputation flags `R`: at every
iteration reached the derivatives satisfy (13.3.4) and the feasible Step-1 displacements (13.3.6);
until termination (`edaStopTR`) every iteration satisfies `TRqDAStep` on `X` with the inexact ratio
(13.3.10) and, on trial iterations, Step 3 (`EDAStep3`). The method returns `x_ε = x_k` and
`δ_ε = min(Δ_k, ϑ)` at termination; the unconstrained method is the case `X = univ`. -/
structure IsTRqEDARun (f : E → ℝ) (X : Set E) (P : TRqIDAParams) (ε : ℕ → ℝ)
    (x₀ : E) (x : ℕ → E) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
    (R : ℕ → Prop) : Prop where
  /-- (13.3.5). -/
  κs_le : P.κs ≤ min P.η₁ (1 - P.η₂) / 4
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ϑ ≥ ε_min`. -/
  epsMin_le_ϑ : epsMin P.q ε ≤ P.ϑ
  /-- The starting point. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible. -/
  x₀_mem : x₀ ∈ X
  /-- The initial radius. -/
  Δ_zero : Δ 0 = P.Δ₀
  /-- The initial accuracies. -/
  h_zero : h 0 = P.h₀
  /-- (13.3.4) at every iteration reached. -/
  oracle : ∀ k, (∀ j < k, ¬ edaStopTR P ε D Δ h dd j) →
    JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.q (fun i => h k i)
  /-- (13.3.6) at every iteration reached. -/
  witness : ∀ k, (∀ j < k, ¬ edaStopTR P ε D Δ h dd j) → ∀ j ∈ Finset.Icc 1 P.q,
    IsApproxMeasureStep ((D k).taylorDecrement j) (trRadius P Δ k) {e | x k + e ∈ X} P.ς (dd k j)
  /-- Steps 1–5 until termination. -/
  run : UntilHit (edaStopTR P ε D Δ h dd) fun k =>
    TRqDAStep X P ε x Δ h D dd jk s acc
        (edaRatio fx fxs fun i => (D i).taylorDecrement (jk i) (s i)) k ∧
      (¬ acc k → EDAStep3 f P.κs ((D k).taylorDecrement (jk k) (s k)) x s acc fx fxs h₀ R k)

namespace IsTRqEDARun

variable {f : E → ℝ} {X : Set E} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ}
  {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
include hrun

theorem step {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) :
    TRqDAStep X P ε x Δ h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement (jk i) (s i)) k :=
  (hrun.run k hk).1

theorem step3 {k : ℕ} (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k) :
    EDAStep3 f P.κs ((D k).taylorDecrement (jk k) (s k)) x s acc fx fxs h₀ R k :=
  (hrun.run k hk).2 ha

theorem steps_lt {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc
      (edaRatio fx fxs fun i => (D i).taylorDecrement (jk i) (s i)) i :=
  fun _ hi => hrun.step fun j hj => hk j (hj.trans_lt hi)

theorem invariants {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (0 < Δ k ∧ Δ k ≤ P.Δmax) ∧ ∀ i ∈ Finset.Icc 1 P.q, 0 < h k i ∧ h k i ≤ P.κh :=
  trqDA_invariants (hrun.steps_lt hk) hrun.Δ_zero hrun.h_zero

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaS_le_eta₁ : P.κs ≤ P.η₁ / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

theorem kappaS_le_eta₂ : P.κs ≤ (1 - P.η₂) / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- The iterates reached are feasible. -/
theorem mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) : x k ∈ X :=
  trqDA_mem (hrun.steps_lt hk) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along a TRqEDA run with a feasible set before termination:
`f(x_k) ≤ f(x₀)`. On a successful iteration the inexact values are within `h_{k,0} ≤ κ_s
\overline{ΔT}_k ≤ η₁/4 \overline{ΔT}_k` of `f` ((13.3.5), (13.3.9)), so `f(x_k) - f(x_{k+1}) ≥
η₁/2 \overline{ΔT}_k > 0`. -/
theorem objective_le {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i hi => ?_
  have hki : ∀ j ≤ i, ¬ edaStopTR P ε D Δ h dd j := fun j hj => hk j (hj.trans_lt hi)
  have hs := hrun.step hki
  by_cases hc : ¬ acc i ∧
      P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i
  · have h3 := hrun.step3 hki hc.1
    have hpos := hs.taylorDecrement_pos hc.1
      (hrun.invariants fun j hj => hk j (hj.trans hi)).1.1 hrun.epsMin_pos
    have hdec := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
      (h3.fxs_err.trans h3.h₀_le) hc.2 hrun.kappaS_le_eta₁
    have := mul_pos (half_pos P.η₁_pos) hpos
    rw [hs.iterate_succ_eq_add hc.1 hc.2]
    linarith
  · rw [hs.iterate_succ_eq hc]

/-- The iterates reached lie in every set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) : x k ∈ A :=
  hAX _ (hrun.mem hk) (hrun.objective_le hk)

/-- (13.1.24) with `κ_{∇,max} = 1`: `‖∇̄^i f(x_k)‖ ≤ L_f + κ_h`, under the smoothness hypothesis
anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) : ‖D k i‖ ≤ lipMax L P.q + P.κh := by
  have h' : ‖D k i‖ ≤ ‖iteratedFDeriv ℝ i f (x k)‖ + h k i :=
    norm_le_of_jetApprox (hrun.oracle k hk) hi
  have := hf.norm_iteratedFDeriv_le_lipMax hL hi (hrun.mem_anchor hAX hk)
  have := ((hrun.invariants hk).2 i hi).2
  linarith

end IsTRqEDARun

section TRqEDA

variable {X C A : Set E} {f : E → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ}
  {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Very successful iterations** (Lemma 13.3.1 of [cartis2022evaluation]): under the smoothness
hypothesis, at a trial iteration `k ∈ 𝒯` of TRqEDA before termination with (13.1.28) for
`κ_{∇,max} = 1`, `Δ_k ≤ min(ϑ, (1 - η₂)/(L_f + 4 (q+1)! κ_s) φ̂_{f,k})`, the iteration is very
successful (`ρ_k ≥ η₂`) and `Δ_{k+1} ≥ Δ_k`. -/
theorem IsTRqEDARun.ratio_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs) *
      trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k ∧
      Δ k ≤ Δ (k + 1) := by
  have hs := hrun.step hk
  have h3 := hrun.step3 hk ha
  have h2 := hs.step2_of_not_acc ha
  have hklt : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j := fun j hj => hk j hj.le
  have hΔpos := (hrun.invariants hklt).1.1
  obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge hs ha hΔpos
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hδeq : trRadius P Δ k = Δ k := min_eq_left (hΔ.trans (min_le_left _ _))
  set j := jk k
  set δ := trRadius P Δ k
  set ph := trPhiHat P Δ D dd jk k
  set Lf := lipMax L P.q
  set C := Lf + 4 * (P.q + 1)! * P.κs
  have hLf : 1 ≤ Lf := one_le_lipMax hL
  have hκs := P.κs_pos
  have hC : 0 < C := by positivity
  have hδ0 : 0 < δ := (trRadius_mem (P := P) hΔpos).1
  have hδ1 : δ ≤ 1 := (trRadius_mem (P := P) hΔpos).2
  have hφ0 : 0 < ph := lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) hφ
  have hfj : (0 : ℝ) < j ! := by positivity
  set ΔTb := (D k).taylorDecrement j (s k)
  have hΔTb : ph * δ ^ j / j ! ≤ ΔTb := hdec
  have hΔTb0 : 0 < ΔTb := lt_of_lt_of_le (by positivity) hΔTb
  have hsδ : ‖s k‖ ≤ δ := hδeq ▸ h2.norm_le
  have hacc : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ 1 * P.κs * ‖s k‖ ^ (P.q - i + 1) := by
    intro i hi
    rw [one_mul]
    by_contra hc
    exact ha (h2.acc_iff.2 ⟨i, hi, not_le.1 hc⟩)
  have hE := abs_taylorDecrement_sub_le_of_stepAccuracy zero_le_one hκs.le (hrun.oracle k hklt)
    hacc hjq
  have hR := hf.abs_sub_taylorDecrement_le_of_le hjq (hrun.mem_anchor hAX hklt) (hXC h2.mem)
  have hLj : L j ≤ Lf := le_lipMax hjq
  have hs0 := norm_nonneg (s k)
  have hpow1 : ‖s k‖ ^ (j + 1) ≤ δ ^ (j + 1) := pow_le_pow_left₀ hs0 hsδ _
  have hpow2 : ‖s k‖ ^ (P.q + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_of_le_one hs0 (hsδ.trans hδ1) (by omega)).trans hpow1
  have hfact1 : (2 : ℝ) * j ! ≤ (j + 1)! := by
    rw [Nat.factorial_succ]; push_cast
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith
  have hfact2 : (4 : ℝ) * j ! ≤ 4 * (P.q + 1)! := by
    have : (j ! : ℝ) ≤ (P.q + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
    linarith
  have hδC : δ * C ≤ (1 - P.η₂) * ph := by
    have := hΔ.trans (min_le_right _ _)
    rw [← hδeq] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hC] at this
    linarith
  have hκs4 := hrun.kappaS_le_eta₂
  have herr : |fx k - f (x k)| + |f (x k + s k) - (f (x k) -
      (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
      |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb| +
      |fxs k - f (x k + s k)| ≤ (1 - P.η₂) * ΔTb := by
    have hRb : L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) ≤ Lf / (2 * j !) * δ ^ (j + 1) := by
      gcongr
    have hEb : 2 * P.κs * 1 * ‖s k‖ ^ (P.q + 1) ≤
        4 * (P.q + 1)! * P.κs / (2 * j !) * δ ^ (j + 1) := by
      have : 2 * P.κs * 1 ≤ 4 * (P.q + 1)! * P.κs / (2 * j !) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      exact mul_le_mul this hpow2 (by positivity) (by positivity)
    have hval := h3.fx_err.trans h3.h₀_le
    have hval' := h3.fxs_err.trans h3.h₀_le
    have hmid : |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
        |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb| ≤
          (1 - P.η₂) / 2 * ΔTb := by
      calc _ ≤ L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) + 2 * P.κs * 1 * ‖s k‖ ^ (P.q + 1) :=
            add_le_add hR (by rw [abs_sub_comm]; exact hE)
        _ ≤ Lf / (2 * j !) * δ ^ (j + 1) + 4 * (P.q + 1)! * P.κs / (2 * j !) * δ ^ (j + 1) :=
            add_le_add hRb hEb
        _ = δ ^ j / j ! * (δ * C) / 2 := by rw [pow_succ]; field_simp; ring
        _ ≤ δ ^ j / j ! * ((1 - P.η₂) * ph) / 2 := by gcongr
        _ = (1 - P.η₂) / 2 * (ph * δ ^ j / j !) := by ring
        _ ≤ (1 - P.η₂) / 2 * ΔTb :=
            mul_le_mul_of_nonneg_left hΔTb (by linarith [P.one_sub_η₂_pos])
    nlinarith
  have hρ : P.η₂ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k := by
    rw [edaRatio]
    exact le_div_of_inexact_error_le hΔTb0 herr
  exact ⟨hρ, (hs.update ha).le_of_very_successful hρ⟩

/-- **The radius stays bounded below**: under the smoothness hypothesis, for an admissible `κ_Δ`
with `κ_{∇,max} = 1`, at every iteration `k` reached by TRqEDA, `δ_k ≥ ς κ_δ ε_min` with
`κ_δ = κ_Δ/2` (13.1.32). -/
theorem IsTRqEDARun.delta_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  rw [mul_one] at hκΔ'
  set a := (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs) with ha_def
  have hLf := one_le_lipMax hL
  have hC : 1 ≤ lipMax L P.q + 4 * (P.q + 1)! * P.κs := by
    have := P.κs_pos; nlinarith [show (0 : ℝ) ≤ 4 * (P.q + 1)! * P.κs by positivity]
  have ha0 : 0 ≤ a := div_nonneg P.one_sub_η₂_pos.le (zero_le_one.trans hC)
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (zero_lt_one.trans_le hC)]
    linarith [P.η₂_pos]
  have hεmin := hrun.epsMin_pos
  have hc := trqDA_delta_ge (hrun.steps_lt hk) hrun.Δ_zero ha0 hκΔ0.le hκΔ'
    (c := P.ς * epsMin P.q ε / 2)
    (fun i hi hai hΔ =>
      (IsTRqEDARun.ratio_ge hf hL hXC hAX hrun (fun j hj => hk j (by omega)) hai hΔ).1)
    (fun i hi hai => (TRqDAStep.trqGap_ge (hrun.steps_lt hk i hi) hai
      (hrun.invariants fun j hj => hk j (hj.trans hi)).1.1).1)
  have hκγ : κΔ ≤ P.γ₁ := hκΔ'.trans (mul_le_of_le_one_right P.γ₁_pos.le ha1)
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have h1 : P.ς * (κΔ / 2) * epsMin P.q ε ≤ epsMin P.q ε := by
    have : P.ς * (κΔ / 2) ≤ 1 := by nlinarith
    nlinarith
  refine le_min (le_trans ?_ hc) (h1.trans hrun.epsMin_le_ϑ)
  refine le_min ?_ (le_of_eq (by ring))
  calc P.ς * (κΔ / 2) * epsMin P.q ε ≤ P.γ₁ * epsMin P.q ε := by
        have : P.ς * (κΔ / 2) ≤ P.γ₁ := by nlinarith
        exact mul_le_mul_of_nonneg_right this hεmin.le
    _ ≤ P.γ₁ * P.ϑ := mul_le_mul_of_nonneg_left hrun.epsMin_le_ϑ P.γ₁_pos.le

/-- **Sufficient decrease** (Lemma 13.3.2 of [cartis2022evaluation]): under the smoothness
hypothesis, for an admissible `κ_Δ` (`κ_{∇,max} = 1`) and `κ_δ = κ_Δ/2`, every trial iteration
`k ∈ 𝒯` of TRqEDA before termination satisfies (13.1.34)
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and if moreover `k ∈ 𝒮` then
(13.1.35) `f(x_k) - f(x_{k+1}) ≥ η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. -/
theorem IsTRqEDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) := by
  have hklt : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j := fun j hj => hk j hj.le
  have hκΔ0 := hκΔ.1
  have h1 := (hrun.step hk).taylorDecrement_ge ha (hrun.invariants hklt).1.1 (by positivity)
    (by linarith [hκΔ.2.1]) hrun.epsMin_pos hrun.epsMin_le_one
    (IsTRqEDARun.delta_ge hf hL hXC hAX hrun hκΔ hklt)
  refine ⟨h1, fun hρ => ?_⟩
  have h3 := hrun.step3 hk ha
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) :=
    lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) h1
  have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
    (h3.fxs_err.trans h3.h₀_le) hρ hrun.kappaS_le_eta₁
  rw [((hrun.step hk).accept ha).eq_add hρ]
  have hη := P.η₁_pos
  calc P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1)
      = P.η₁ / 2 * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) := by
        field_simp
    _ ≤ P.η₁ / 2 * (D k).taylorDecrement (jk k) (s k) := by gcongr
    _ ≤ f (x k) - f (x k + s k) := h2

/-- **Termination certifies approximate optimality** (Lemma 13.3.3 (i) of [cartis2022evaluation]):
if TRqEDA terminates at iteration `k` (Step 1.4.1: (13.3.7) fails at every order and (13.3.8)
holds), then `x_k` is an `(ε, δ_k)`-approximate `q`-th order minimizer,
`δ_k = min(Δ_k, ϑ) ∈ (0, 1]`. -/
theorem IsTRqEDARun.isEpsDeltaApprox_of_stop
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) (hstop : edaStopTR P ε D Δ h dd k) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε
      (fun _ => trRadius P Δ k) := by
  have hΔ := (hrun.invariants hk).1.1
  obtain ⟨hδ0, hδ1⟩ := trRadius_mem (P := P) hΔ
  have hor := hrun.oracle k hk
  intro j hj
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set δ := trRadius P Δ k
  have hεmin := hrun.epsMin_pos
  have hς := P.ς_pos
  have hs : ∑ i ∈ Finset.Icc 1 j, h k i * δ ^ i / i ! ≤ ε j * δ ^ j / j ! / 2 := by
    have hsub : ∑ i ∈ Finset.Icc 1 j, h k i * δ ^ i / i ! ≤
        ∑ i ∈ Finset.Icc 1 P.q, h k i * δ ^ i / i ! :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hjq) fun i hi _ =>
        div_nonneg (mul_nonneg (hor.nonneg hi) (pow_nonneg hδ0.le _)) (by positivity)
    refine hsub.trans (hstop.2.trans ?_)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * epsMin P.q ε ≤ ε j :=
      (mul_le_of_le_one_left hεmin.le P.ς_le_one).trans (epsMin_le hj)
    have hδq : δ ^ P.q ≤ δ ^ j := pow_le_pow_of_le_one hδ0.le hδ1 hjq
    calc P.ς * epsMin P.q ε * δ ^ P.q / P.q ! / 2 ≤ ε j * δ ^ j / P.q ! / 2 := by
          gcongr
          exact (hrun.eps_mem j hj).1.le
      _ ≤ ε j * δ ^ j / j ! / 2 := by
          gcongr
          exact mul_nonneg (hrun.eps_mem j hj).1.le (pow_nonneg hδ0.le _)
  exact taylorMeasure_le_of_inexact_certificate hor hjq (by simpa using hrun.mem hk) hδ0.le hς
    (hrun.witness k hk j hj).2 (not_lt.1 (hstop.1 j hj)) hs

/-- **Accurate data give termination** (Lemma 13.3.3 (ii) of [cartis2022evaluation]): under the
smoothness hypothesis and for an admissible `κ_Δ` (`κ_{∇,max} = 1`), `κ_δ = κ_Δ/2`: if (13.3.7)
fails at every order at an iteration `k` reached by TRqEDA and (13.1.37)
`h_{k,i} ≤ ς^{q+1} κ_δ^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, q]`, then (13.3.8) holds: the method
terminates at `k` (Step 1.4.1) rather than branching to Step 5. -/
theorem IsTRqEDARun.stop_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopTR P ε D Δ h dd k := by
  refine ⟨hpass, ?_⟩
  have hΔ := (hrun.invariants hk).1.1
  obtain ⟨hδ0, hδ1⟩ := trRadius_mem (P := P) hΔ
  have hδm := IsTRqEDARun.delta_ge hf hL hXC hAX hrun hκΔ hk
  set δ := trRadius P Δ k
  set em := epsMin P.q ε
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have hκΔ0 := hκΔ.1
  have hκΔ1 := hκΔ.2.1
  set e := P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1)
  have he0 : 0 ≤ e := by positivity
  set m := P.ς * (κΔ / 2) * em
  have hm0 : 0 ≤ m := by positivity
  calc ∑ i ∈ Finset.Icc 1 P.q, h k i * δ ^ i / i ! ≤ ∑ i ∈ Finset.Icc 1 P.q, e * (δ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (hh i hi) (by positivity)
    _ = e * ∑ i ∈ Finset.Icc 1 P.q, δ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ e * 2 := mul_le_mul_of_nonneg_left
        ((sum_pow_div_factorial_le_two_mul hδ0.le hδ1 _).trans (by linarith)) he0
    _ = P.ς * em * m ^ P.q / (2 * P.q !) := by simp only [e, m]; ring
    _ ≤ P.ς * em * δ ^ P.q / (2 * P.q !) := by gcongr
    _ = P.ς * em * δ ^ P.q / P.q ! / 2 := by ring

/-- **The accuracy-improving iterations of TRqEDA with a feasible set** (proof of Theorem 13.3.4,
[cartis2022evaluation]): under `LipschitzDerivsAnchored f C A 0 q L` (`L_j ≥ 1`, `A ⊇ {y ∈ X |
f(y) ≤ f(x₀)}`) and for an admissible `κ_Δ` (`κ_{∇,max} = 1`), if the run has not terminated at
any `j ≤ k`, then `|𝒜_k| ≤ q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem IsTRqEDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) :
    ((successSet acc k).card : ℝ) ≤
      P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1 := by
  have hκΔ'' := hκΔ
  have hκΔ0 := hκΔ.1
  have hκΔ1 := hκΔ.2.1
  have hq := P.one_le_q
  set stop := edaStopTR P ε D Δ h dd
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  set Lf := lipMax L P.q
  set Lb := Lf + P.κh
  have hLb1 : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.kappaH_pos; linarith
  have hLb : 0 < Lb := by linarith
  set κacc := trKappaAcc P κΔ Lb 1
  have hκacc : 0 < κacc := trKappaAcc_pos hκΔ0 hLb zero_le_one
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.q * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith)
  have h := card_accuracyImproving_le_of_pow (acc := acc) (hmax := fun j => ordMax P.q (h j))
    (N := P.q * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.kappaH_pos hκacc hεmin
    ((ordMax_le_iff hq).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j hj ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from
        funext ((hrun.step fun i hi => hk i (hi.trans hj)).h_acc ha),
        ordMax_mul hq P.γh_pos.le])
    (fun j hj ha => by rw [(hrun.step fun i hi => hk i (hi.trans hj)).h_trial ha])
    (fun j hj ha => by
      have hjs : ∀ i ≤ j, ¬ stop i := fun i hi => hk i (hi.trans hj)
      have hjlt : ∀ i < j, ¬ stop i := fun i hi => hjs i hi.le
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.q, h j i ≤ κacc * em ^ (P.q * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd j i
      · refine (((hrun.step hjs).step2 hfail).not_acc_of_le (Lb := Lb)
          (hrun.invariants hjlt).1.1 hLb1 (fun i hi => hrun.norm_D_le hf hL hAX hjlt hi)
          (by positivity) (by linarith) hrun.eps_mem
          (IsTRqEDARun.delta_ge hf hL hXC hAX hrun hκΔ'' hjlt)
          fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right trKappaAcc_le (by positivity)
      · push Not at hfail
        refine hjs j le_rfl
          (IsTRqEDARun.stop_of_pass hf hL hXC hAX hrun hκΔ'' hjlt hfail fun i hi => ?_)
        calc h j i ≤ κacc * em ^ (P.q * (P.q + 1)) := hhi i hi
          _ = 1 * κacc * em ^ (P.q * (P.q + 1)) := by ring
          _ ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_trKappaAcc_le hκΔ0 zero_le_one) hpowq (by positivity)
                (by positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.q * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **Evaluation complexity of TRqEDA** (Theorem 13.3.4 of [cartis2022evaluation]): complexity of
TRqEDA. Let the smoothness hypothesis and f.Bb hold, `ε ∈ (0, 1]^q`, and `κ_Δ` be admissible with
`κ_{∇,max} = 1`, `κ_δ = κ_Δ/2`. Every TRqEDA run terminates at some iteration `k_ε` with `x_{k_ε}`
an `(ε, δ_ε)`-approximate `q`-th order minimizer, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, after at most
`2 κ^A (f(x₀) - f_low)/ε_min^{q+1} + 2 κ^B |log ε_min| + 2 κ^C` inexact function evaluations and
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^E |log ε_min| + κ^F + 2` derivative estimates, with the
constants of Theorem 13.1.8 for `κ_{∇,max} = 1` (`κ_acc = trKappaAcc P κ_Δ (L_f + κ_h) 1`). -/
theorem IsTRqEDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} P.q ε
        (fun _ => trRadius P Δ kε) ∧
      0 < trRadius P Δ kε ∧ trRadius P Δ kε ≤ 1 ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * (trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1)) +
          2 * (1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)|) +
          2 * (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| /
            |Real.log P.γh| + 2 := by
  have hκΔ'' := hκΔ
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hq := P.one_le_q
  set stop := edaStopTR P ε D Δ h dd
  set ρ := edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i))
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hη := P.η₁_pos
  set Lf := lipMax L P.q
  set Lb := Lf + P.κh
  have hLb1 : 1 ≤ Lb := by have := one_le_lipMax hL; have := P.kappaH_pos; linarith
  have hLb : 0 < Lb := by linarith
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  -- successful iterations
  set c := P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * em ^ (P.q + 1) with hc_def
  have hc : 0 < c := by positivity
  set NS := trKappaS P κΔ * (f x₀ - flow) / em ^ (P.q + 1) with hNS_def
  have hNS : NS = (f x₀ - flow) / c := by
    rw [hNS_def, hc_def, trKappaS, eq_div_iff (by positivity)]
    field_simp
  have hNS0 : 0 ≤ NS := by rw [hNS]; positivity
  have hSk : ∀ k, (∀ j ≤ k, ¬ stop j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card : ℝ) ≤ NS := by
    intro k hk
    rw [hNS, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j hj hs => by rw [(hrun.step fun i hi => hk i (hi.trans hj)).iterate_succ_eq hs])
      (fun j hj hs =>
        (IsTRqEDARun.decrease_ge hf hL hXC hAX hrun hκΔ'' (fun i hi => hk i (hi.trans hj))
          hs.1).2 hs.2)
      (hb _ (hrun.mem fun j hj => hk j (Nat.lt_succ_iff.1 hj)))
  -- trial iterations
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  set A' := 1 + Real.log P.γ₃ / |Real.log P.γ₂| with hA'
  have hA'1 : 1 ≤ A' := by
    have := Real.log_nonneg P.one_le_γ₃; rw [hA']; have := div_nonneg this hlog2.le; linarith
  set NT := trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) +
    1 / |Real.log P.γ₂| * |Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| /
      |Real.log P.γ₂| with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ trKappaS P κΔ := by unfold trKappaS; positivity
    positivity
  have hTk : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have hΔmin : P.ς * (κΔ / 2) * em ≤ Δ (k + 1) :=
      (IsTRqEDARun.delta_ge hf hL hXC hAX hrun hκΔ'' fun j hj => hk j (Nat.lt_succ_iff.1 hj)).trans
        (min_le_left _ _)
    have h1 := trqDA_card_trial_le (fun i hi => hrun.step fun j hj => hk j (hj.trans hi))
      hrun.Δ_zero (by positivity) hΔmin
    have hlog : |Real.log (P.ς * (κΔ / 2) * em / P.Δ₀)| ≤
        |Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| := by
      have hpos : 0 < P.ς * (κΔ / 2) / P.Δ₀ := by have := P.Δ₀_pos; positivity
      rw [show P.ς * (κΔ / 2) * em / P.Δ₀ = em * (P.ς * (κΔ / 2) / P.Δ₀) by ring,
        Real.log_mul hεmin.ne' hpos.ne']
      exact abs_add_le _ _
    have h2 := mul_le_mul_of_nonneg_right (hSk k hk) (zero_le_one.trans hA'1)
    calc ((successSet (fun i => ¬ acc i) k).card : ℝ)
        ≤ _ := h1
      _ ≤ NS * A' + (|Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)|) /
            |Real.log P.γ₂| := add_le_add h2 (div_le_div_of_nonneg_right hlog hlog2.le)
      _ = NT := by rw [hNT_def, hNS_def]; ring
  -- accuracy-improving iterations
  set κacc := trKappaAcc P κΔ Lb 1
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hAk : ∀ k, (∀ j ≤ k, ¬ stop j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsTRqEDARun.card_acc_le hf hL hXC hAX hrun hκΔ'' hk
  -- conclusion
  obtain ⟨kε, hkε, -, hT, hA⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hTk hAk
  have hS := derivEvalCount_le_of_isFirstHit hNS0 hkε hSk
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ ρ i)) kε : ℝ) + 1 ≤
      derivEvalCount acc kε + derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hNSA : NS ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) := by
    have : trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) = A' * NS := by
      rw [hNS_def]; ring
    rw [this]
    exact le_mul_of_one_le_left hNS0 hA'1
  have hklt : ∀ j < kε, ¬ stop j := fun j hj => hkε.not_test_of_lt hj
  have hΔ := (hrun.invariants hklt).1.1
  refine ⟨kε, hkε, IsTRqEDARun.isEpsDeltaApprox_of_stop hrun hklt hkε.test, (trRadius_mem hΔ).1,
    (trRadius_mem hΔ).2,
    ?_, ?_⟩
  · have := edaFunEvalCount_le acc R kε
    calc (edaFunEvalCount acc R kε : ℝ) ≤ 2 * ((derivEvalCount (fun i => ¬ acc i) kε : ℝ) - 1) :=
          this
      _ ≤ 2 * NT := by linarith
      _ ≤ _ := by rw [hNT_def]; nlinarith
  · calc _ ≤ (NA + 1) + (NS + 1) - 1 := by linarith
      _ ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) + NA + 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

end TRqEDA

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E} {x : ℕ → E}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E}
  {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  {L B : ℕ → ℝ} {κΔ : ℝ}

/-- **Counting the trial iterations of a run** (Lemma 14.2.3 of [cartis2022evaluation]): for a
TRqEDA run with a feasible set under `LipschitzDerivsAnchored f C A 0 q L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`) and an admissible `κ_Δ` (`κ_{∇,max} = 1`), every iteration `k` reached
(up to and including termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with
`κ_uns = 1 + log γ₃/|log γ₂|` and `κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`,
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem IsTRqEDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqEDARun f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + P.κh) 1 / P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hΔmin : P.ς * (κΔ / 2) * epsMin P.q ε ≤ Δ (k + 1) :=
    (IsTRqEDARun.delta_ge hf hL hXC hAX hrun hκΔ hk).trans (min_le_left _ _)
  have hT := trqDA_card_trial_le (fun i hi => hrun.step fun j hj => hk' j (hj.trans hi)) hrun.Δ_zero
    (mul_pos (mul_pos P.ς_pos (half_pos hκΔ.1)) hrun.epsMin_pos) hΔmin
  have hA := IsTRqEDARun.card_acc_le hf hL hXC hAX hrun hκΔ hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧
        P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

end Iterations

end Optimization
