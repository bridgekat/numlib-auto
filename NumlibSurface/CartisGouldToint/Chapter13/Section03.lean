import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpEDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01

/-!
# Cartis–Gould–Toint §13.3: Inexact algorithms using explicit dynamic accuracy

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §13.3: the trust-region method
TRqEDA (Algorithm 13.3.1) and the adaptive-regularization method ARqpEDA (Algorithm 13.3.2), in
which the derivative errors are enforceable and normalized (`κ_{∇,i} = 1`, (13.3.3)–(13.3.4):
`JetApprox (ftaylorSeries ℝ f (x k)) (D k) r (h k)`), function values are inexact with requested
accuracy `h_{k,0}` ((13.3.1)–(13.3.2)), and termination is certified.

## Modelling

* The runs reuse the iteration predicates `TRqDAStep` and `ARqpDAStep` of §13.1 (Steps 1, 2, 4
  and 5 are those of the IDA algorithms) until the termination test holds
  (`Optimization.UntilHit`), together with the new Step 3 (`EDAStep3`): `0 < h_{k,0} ≤ κ_s
  \overline{ΔT}` ((13.3.9), (13.3.18)), inexact values `f̄(x_k)` (`fx k`) and `f̄(x_k + s_k)`
  (`fxs k`) within `h_{k,0}` of `f`, and the ratio `ρ_k = (f̄(x_k) - f̄(x_k + s_k))/\overline{ΔT}`
  ((13.3.10), (13.3.19)). `R k` records that `f̄(x_k)` was (re)computed in Step 3; otherwise it is
  the trial value of an earlier iteration at the same point. The function-value count is
  `edaFunEvalCount acc R k = |𝒯 ∩ [0, k)| + |𝒯 ∩ R ∩ [0, k)| ≤ 2 |𝒯 ∩ [0, k)|` (no evaluation at
  Step 0).
* The Step-1 data (displacements, radii) and the oracle bounds are required at every iteration
  reached, including the terminating one, at which they certify approximate optimality.
* The algorithms and their analysis are those of the library
  (`Optimization.IsTRqEDARun`, `Optimization.IsARqpEDARun` in
  `Numlib/Optimization/ModelBased/HighOrder/DynamicAccuracy/`), stated on a feasible set `X` under
  the anchored smoothness hypothesis `LipschitzDerivsAnchored`; `algorithm_13_3_1` and
  `algorithm_13_3_2` are the case `X = univ`, and the results of this file are their instances
  under f.D0qL (f.D0pL). With inexact values the iterates reached still stay in the sublevel set
  `{y | f(y) ≤ f(x₀)}`: on a successful iteration the values are within
  `h_{k,0} ≤ κ_s \overline{ΔT}_k` of `f`, and `κ_s ≤ η₁/4` ((13.3.5), (13.3.13)) gives
  `f(x_k) - f(x_{k+1}) ≥ η₁/2 \overline{ΔT}_k > 0`.

## Deviations from the book

* **Theorem 13.3.4**: the printed constants `κ^B_{TRqEDA} = 6!/(2!2!) 2κ^B_{TRqIDA}`,
  `κ^C_{TRqEDA} = 6!/2 · 2κ^C_{TRqIDA}` are garbled; the proof gives the factor `2` only (at most
  two value evaluations per trial iteration). The derivative count includes the initial estimate
  and the last accuracy-improving iteration (`+ 2`), as in Theorem 13.1.8.
* **Lemma 13.3.5** uses `κ_s' = max(κ_s, κ_h)` (as Lemma 13.1.14).
* **Lemma 13.3.7 and Theorem 13.3.8.** The book proves them "identically" to Lemma 13.1.18 and
  Theorem 13.1.19, i.e. through Lemmas 13.1.16–13.1.17, whose hypothesis is that `x_{k+1}` is not
  approximately optimal. Non-termination of ARqpEDA at `k + 1` does not imply this. The corrected
  argument (`eda_radius_inequality`) uses what a successful iteration followed by an iteration
  that is not accuracy-improving with unchanged radii gives: a displacement at `x_{k+1}` with a
  large inexact decrement, hence a large exact measure up to the accuracy inherited from
  iteration `k`. This needs `θ < ς/2`, replaces `1 - θ` by `ς/2 - θ` and
  `3 κ_{∇,max} κ_s` by `4 κ_s` in the constants, and adds the (logarithmically many) successful
  iterations followed by an accuracy-improving one to the count; the orders in `ε` are unchanged.
  For `q ≤ 2` the printed radius-one conclusion is derived from the certified radii
  `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, as in Theorem 13.1.19.
-/

open Set Metric Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


/-! ### TRqEDA -/

section TRqEDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ}
  {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop} {L : ℕ → ℝ}
  {k : ℕ}

/-- **Algorithm 13.3.1** (TRqEDA) of [cartis2022evaluation] as a run predicate, with the TRqIDA
constants `P` satisfying (13.3.5) `κ_s ≤ min(η₁, 1 - η₂)/4`, tolerances `ε ∈ (0, 1]^q` with
`ε_min ≤ ϑ`, starting point `x₀`, the sequences of TRqIDA, inexact values `fx`, `fxs` with
accuracies `h₀` and recomputation flags `R`: at every iteration reached the derivatives satisfy
(13.3.4) and the Step-1 displacements (13.3.6); until termination (`edaStopTR`) every iteration
satisfies `TRqDAStep` with the inexact ratio (13.3.10) and, on trial iterations, Step 3. The method
returns `x_ε = x_k` and `δ_ε = min(Δ_k, ϑ)` at termination. This is
`IsTRqEDARun` with the feasible set `X = univ`. -/
abbrev algorithm_13_3_1 (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
    (R : ℕ → Prop) : Prop :=
  IsTRqEDARun f univ P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R

/-- **Lemma 13.3.1** ([cartis2022evaluation]): under f.D0qL, at a trial iteration `k ∈ 𝒯` of
TRqEDA before termination with (13.1.28) for `κ_{∇,max} = 1`,
`Δ_k ≤ min(ϑ, (1 - η₂)/(L_f + 4 (q+1)! κ_s) φ̂_{f,k})`, the iteration is very successful
(`ρ_k ≥ η₂`) and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_13_3_1 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs) *
      trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k ∧
      Δ k ≤ Δ (k + 1) :=
  IsTRqEDARun.ratio_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk ha hΔ

/-- **Lemma 13.3.2** ([cartis2022evaluation]): under f.D0qL, for an admissible `κ_Δ`
(`κ_{∇,max} = 1`) and `κ_δ = κ_Δ/2`, every trial iteration `k ∈ 𝒯` of TRqEDA before termination
satisfies (13.1.34) `\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and if
moreover `k ∈ 𝒮` then (13.1.35) `f(x_k) - f(x_{k+1}) ≥ η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. -/
theorem lemma_13_3_2 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j ≤ k, ¬ edaStopTR P ε D Δ h dd j) (ha : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) :=
  IsTRqEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk ha

/-- **Lemma 13.3.3 (i)** ([cartis2022evaluation]): if TRqEDA terminates at iteration `k`
(Step 1.4.1: (13.3.7) fails at every order and (13.3.8) holds), then `x_k` is an
`(ε, δ_k)`-approximate `q`-th order minimizer, `δ_k = min(Δ_k, ϑ) ∈ (0, 1]`. -/
theorem lemma_13_3_3_i (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) (hstop : edaStopTR P ε D Δ h dd k) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trRadius P Δ k) := by
  have := IsTRqEDARun.isEpsDeltaApprox_of_stop hrun hk hstop
  rwa [Set.setOf_add_mem_univ] at this

/-- **Lemma 13.3.3 (ii)** ([cartis2022evaluation]): under f.D0qL and for an admissible `κ_Δ`
(`κ_{∇,max} = 1`), `κ_δ = κ_Δ/2`: if (13.3.7) fails at every order at an iteration `k` reached by
TRqEDA and (13.1.37) `h_{k,i} ≤ ς^{q+1} κ_δ^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, q]`, then (13.3.8)
holds: the method terminates at `k` (Step 1.4.1) rather than branching to Step 5. -/
theorem lemma_13_3_3_ii (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopTR P ε D Δ h dd k :=
  IsTRqEDARun.stop_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk hpass hh

/-- **Theorem 13.3.4** ([cartis2022evaluation]): complexity of TRqEDA. Let f.D0qL and f.Bb hold,
`ε ∈ (0, 1]^q`, and `κ_Δ` be admissible with `κ_{∇,max} = 1`, `κ_δ = κ_Δ/2`. Every TRqEDA run
terminates at some iteration `k_ε` with `x_{k_ε}` an `(ε, δ_ε)`-approximate `q`-th order
minimizer, `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, after at most
`2 κ^A (f(x₀) - f_low)/ε_min^{q+1} + 2 κ^B |log ε_min| + 2 κ^C` inexact function evaluations and
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^E |log ε_min| + κ^F + 2` derivative estimates, with the
constants of Theorem 13.1.8 for `κ_{∇,max} = 1` (`κ_acc = trKappaAcc P κ_Δ (L_f + κ_h) 1`). -/
theorem theorem_13_3_4 (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ) :
    ∃ kε, IsFirstHit (edaStopTR P ε D Δ h dd) kε ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => trRadius P Δ kε) ∧
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
  have := IsTRqEDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hκΔ
  simpa only [Set.setOf_add_mem_univ] using this

/-- **Runs of Algorithm 13.3.1 exist** ([cartis2022evaluation]): for constants `P` with
(13.3.5), tolerances `ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, a starting point `x₀` and every
deterministic derivative oracle `O` satisfying (13.3.4) for all points and accuracies, there is a
TRqEDA run with `D_k = O(x_k, h_k)` (the oracle is only used for positive accuracies), using
exact function values (`f̄ = f`, always recomputed)
and `h_{k,0} = κ_s \overline{ΔT}_{f,j_k}(x_k, s_k)`. -/
theorem exists_algorithm_13_3_1 {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    (hκs : P.κs ≤ min P.η₁ (1 - P.η₂) / 4) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hϑ : epsMin P.q ε ≤ P.ϑ) (x₀ : ℝⁿ) (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.q, 0 < h' i) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.q (fun i => h' i)) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
      (R : ℕ → Prop), algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R ∧
        ∀ k, D k = O (x k) (h k) := by
  obtain ⟨x, Δ, h, dd, jk, s, acc, hx, hΔ, hh, hstep⟩ := exists_trqDA_run f P ε O x₀
  have hεmin : 0 < epsMin P.q ε := Optimization.epsMin_pos P.one_le_q fun j hj => (hε j hj).1
  refine ⟨x, Δ, h, _, dd, jk, s, acc, fun i => f (x i), fun i => f (x i + s i),
    fun i => P.κs * (O (x i) (h i)).taylorDecrement (jk i) (s i), fun _ => True,
    ⟨hκs, hε, hϑ, hx, mem_univ _, hΔ, hh, fun k _ => hO _ _ fun i hi =>
      ((trqDA_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, fun k _ j hj => ?_,
      UntilHit.of_forall fun k => ⟨hstep k, fun ha => ?_⟩⟩, fun _ => rfl⟩
  · exact (hstep k).witness j hj
  · have hΔk := trqDA_delta_pos (k := k) (fun i _ => hstep i) hΔ
    obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge (hstep k) ha hΔk
    have hφ0 : 0 < P.ς * epsMin P.q ε / 2 := by have := P.ς_pos; positivity
    have hδ := (trRadius_mem (P := P) hΔk).1
    have hpos : 0 < (O (x k) (h k)).taylorDecrement (jk k) (s k) :=
      lt_of_lt_of_le (by have := hφ0.trans_le hφ; positivity) hdec
    have h0 := (mul_pos P.κs_pos hpos).le
    exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
      fun hR => absurd trivial hR⟩

end TRqEDA

/-! ### ARqpEDA -/

section ARqpEDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Algorithm 13.3.2** (ARqpEDA) of [cartis2022evaluation] as a run predicate, with the ARqpIDA
constants `P` satisfying (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, tolerances `ε ∈ (0, 1]^q` with
`ε ≤ δ₀`, starting point `x₀`, the sequences of ARqpIDA, inexact values `fx`, `fxs` with
accuracies `h₀` and recomputation flags `R`: at every iteration reached the derivatives satisfy
(13.3.4) up to order `p` and Step 1 (13.3.14)–(13.3.16) is performed (`ARqpStep1`); until
termination (`edaStopAR`) every iteration satisfies `ARqpDAStep` with the inexact ratio (13.3.19)
and, on trial iterations, Step 3. The method returns `x_ε = x_k` and `δ_ε = δ^{(1)}_k`. This is
`IsARqpEDARun` with the feasible set `X = univ`. -/
abbrev algorithm_13_3_2 (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) : Prop :=
  IsARqpEDARun f univ P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R

/-- **Lemma 13.3.5** ([cartis2022evaluation], corrected constant): under f.D0pL, every iteration
`k` reached by ARqpEDA has `σ_k ≤ σ_max` with `σ_max = arqpIDASigmaMax P L_{f,p} 1`
((13.1.77) with `κ_{∇,max} = 1` and `κ_s' = max(κ_s, κ_h)`). -/
theorem lemma_13_3_5 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arqpIDASigmaMax P (L P.p) 1 :=
  IsARqpEDARun.sigma_le hf.lipschitzDerivsAnchored (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk

/-- **Lemma 13.3.6 (i)** ([cartis2022evaluation]): if ARqpEDA terminates at iteration `k`
(Step 1.5.1), then `x_k` is an `(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer with
`δ^{(1)}_k ∈ (0, 1]^q`. -/
theorem lemma_13_3_6_i (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) := by
  have := IsARqpEDARun.isEpsDeltaApprox_of_stop hrun hk hstop
  rwa [Set.setOf_add_mem_univ] at this

/-- **Lemma 13.3.6 (ii)** ([cartis2022evaluation]): under f.D0pL and the radii control at every
iteration, if (13.3.15) holds at every order at an iteration `k` reached by ARqpEDA and (13.1.78)
holds with `κ_{∇,max} = 1`, `h_{k,i} ≤ ς κ^{(1)}_δ(σ_max)^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, p]`
(`σ_max` of Lemma 13.3.5, `L̄_f = L_f + κ_h`), then (13.3.17) holds and the method terminates
at `k`. -/
theorem lemma_13_3_6_ii (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.ς * arKappaDelta1 P (lipMax L P.p + P.κh)
      (arqpIDASigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k :=
  IsARqpEDARun.stop_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hpass hh

/-- **The radius inequality for ARqpEDA** (the corrected replacement of Lemmas 13.1.16–13.1.17 in
§13.3.2 of [cartis2022evaluation]). Under f.D0pL, let iteration `k` of ARqpEDA (reached, not
terminal) be successful with `‖s_k‖ < 1`, and suppose that Step 1 at `k + 1` does not pass every
test (13.3.15) with unchanged radii (i.e. it halves some radius or branches to Step 2). Then for
some `j ∈ [1, q]`, with `δ = δ_{k+1,j} = δ_{s_k,j}`,
`(ς/2 - θ) ε_j δ^j/j! ≤ (L_{f,p} + σ_max + 4 κ_s) ∑_{ℓ=1}^j δ^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}`
(`σ_max` of Lemma 13.3.5). Proof: Step 1 at `k + 1` provides a displacement in `B_δ` with a large
inexact decrement, whence `φ^δ_{f,j}(x_{k+1}) > ½ ς ε_j δ^j/j! - κ_s ∑_ℓ δ^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}`
(the accuracies are inherited from iteration `k`), and the model-optimality conditions (13.1.57)
at `s_k`. -/
theorem eda_radius_inequality (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hs1 : ‖s k‖ < 1)
    (hnot : ¬ ((∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd (k + 1) j) ∧
      ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 P.q, (P.ς / 2 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  IsARqpEDARun.measure_ineq hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk ha hρ hs1 hnot

/-- **Lemma 13.3.7** ([cartis2022evaluation], corrected hypotheses): under f.D0pL, the radii
control at `k` and `θ < ς/2`, let iteration `k` of ARqpEDA (before termination) be successful,
and let `‖s_k‖ ≥ 1` or Step 1 at `k + 1` not pass with unchanged radii. Then
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ κ'_{Δm} min_j ε_j^{π_j}` and
`f(x_k) - f(x_{k+1}) ≥ ½ η₁ κ'_{Δm} min_j ε_j^{π_j}`, where `κ'_{Δm}` is `κ_{Δm}` of
Lemma 13.1.18 with `ς/2 - θ` for `1 - θ`, `L_{f,p} + σ_max + 4 κ_s` for
`L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` (`σ_max` of Lemma 13.3.5) and `L̄_f = L_f + κ_h`. (The
remaining successful iterations are followed by an accuracy-improving iteration, Step 1 → Step 5;
the book asserts the decrease for every trial iteration before termination.) -/
theorem lemma_13_3_7 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k) (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  IsARqpEDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hθ hk ha hρ hgood

/-- **The complexity argument of Theorem 13.3.8** ([cartis2022evaluation], corrected), for any
decrease constant: under f.D0pL, f.Bb, the radii control at every iteration, if every
successful iteration `k` of an ARqpEDA run (before termination) with `‖s_k‖ ≥ 1` or Step 1 at
`k + 1` not passing with unchanged radii decreases `f` by at least `c > 0`, then the run
terminates at some `k_ε`, `x_{k_ε}` is an `(ε, δ^{(1)}_{k_ε})`-approximate `q`-th order minimizer
with `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, and with `N = (f(x₀) - f_low)/c`,
`M = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` (a bound on the number of
accuracy-improving iterations) and `c_T = 1 + |log γ₁|/log γ₂`, at most
`2 ((N + M + 1) c_T + log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2`
derivative estimates are made. (The successful iterations not covered by the decrease are followed
by an accuracy-improving iteration, hence at most `M` of them.) -/
theorem arqpEDA_complexity (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i) {c : ℝ}
    (hc : 0 < c)
    (hdec : ∀ k, (∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) → ¬ acc k →
      P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k →
      (1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) → c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
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
  have := IsARqpEDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hrc hc hdec
  simpa only [Set.setOf_add_mem_univ] using this

/-- **Theorem 13.3.8 (1)** ([cartis2022evaluation], `q ∈ {1, 2}`, corrected): under f.D0pL,
f.Bb, the radii control (13.1.69)–(13.1.70) at every iteration and `θ < ς/2`, every
ARqpEDA run terminates at some `k_ε` with `x_{k_ε}` an `(ε, δ^{(1)}_{k_ε})`-approximate `q`-th
order minimizer, `δ^{(1)}_{k_ε} ∈ (0, 1]^q`, after at most `2 ((N + M + 1) c_T +
log(σ_max/σ₀)/log γ₂)` inexact function evaluations and `N + 2M + 2` derivative estimates, where
`N = κ'^S (f(x₀) - f_low)/min_j ε_j^{(p+1)/(p-j+1)}`, `κ'^S = 2/(η₁ κ'_{Δm})`,
`κ'_{Δm} = σ_min/(p+1)! ((ς/2 - θ)/(2 q! A'))^{(p+1)/(p-q+1)}` with
`A' = L_{f,p} + σ_max + 4 κ_s`, `M = κ^E |log ε_min| + κ^F + 1` (`κ_{∇,max} = 1`, `σ_max` of
Lemma 13.3.5) and `c_T = 1 + |log γ₁|/log γ₂`. Both bounds are
`O(max_j ε_j^{-(p+1)/(p-j+1)})`, the order claimed by the book; the book's constants rest on the
gap described in the module documentation (hence the extra hypothesis `θ < ς/2` and the term
`M` in the number of successful iterations). The printed conclusion `φ^1_{f,j}(x_ε) ≤ ε_j/j!`
follows from the certified radii (`isEpsDeltaApprox_one_of_le_two`). -/
theorem theorem_13_3_8_i (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) (hq2 : P.q ≤ 2) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => 1) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * ((2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
              epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : P.q ≤ 2 := hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ))) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := arqpEDA_complexity hf hb hrun hrc hc
    fun k hk ha hρ hgood => by
      have := (lemma_13_3_7 hf hrun (hrc k) hθ hk ha hρ hgood).2
      rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  rw [hdiv] at h1 h2
  exact ⟨kε, hk, hmem, happ, isEpsDeltaApprox_one_of_le_two hq2 hmem happ, h1, h2⟩

/-- **Theorem 13.3.8 (2)** ([cartis2022evaluation], `q > 2`, corrected): as
`theorem_13_3_8_i` with the exponents `π_j = j(p+1)/p` and
`κ'_{Δm} = σ_min/(p+1)! ((ς/2 - θ) κ̂^{q-1}/(2 q! A'))^{q(p+1)/p}`,
`κ̂ = min(κ_{δ,min}, (ς/2 - θ)/(2 q! A'))`; both bounds are `O(max_j ε_j^{-j(p+1)/p})`. -/
theorem theorem_13_3_8_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hθ : P.θ < P.ς / 2) (hq2 : 2 < P.q) :
    ∃ kε, IsFirstHit (edaStopAR P ε D δ₁ h dd) kε ∧
      (∀ j ∈ Finset.Icc 1 P.q, δ₁ kε j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (δ₁ kε) ∧
      (edaFunEvalCount acc R kε : ℝ) ≤
        2 * ((2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
              epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh)
                  (arqpIDASigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arqpIDASigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arqpIDASigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arqpIDASigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, hmem, happ, h1, h2⟩ := arqpEDA_complexity hf hb hrun hrc hc
    fun k hk ha hρ hgood => by
      have := (lemma_13_3_7 hf hrun (hrc k) hθ hk ha hρ hgood).2
      rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  rw [hdiv] at h1 h2
  exact ⟨kε, hk, hmem, happ, h1, h2⟩

/-- **Runs of Algorithm 13.3.2 exist** ([cartis2022evaluation]): under f.D0pL, for constants `P`
with (13.3.13), tolerances `ε ∈ (0, 1]^q` with `ε ≤ δ₀`, a starting point `x₀` and every
deterministic derivative oracle `O` satisfying (13.3.4) at every point for all accuracies
`h ∈ (0, κ_h]^p`, and positive initial accuracies, there is an ARqpEDA run with
`D_k = O(x_k, h_k)` and the radii control at every iteration, using exact
function values (`f̄ = f`, always recomputed) and `h_{k,0} = κ_s \overline{ΔT}_{f,p}(x_k, s_k)`. -/
theorem exists_algorithm_13_3_2 {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hκs : P.κs ≤ min P.η₁ (1 - P.η₂) / 4)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i)
    (x₀ : ℝⁿ) (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => h' i)) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop),
      algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R ∧
        (∀ k, D k = O (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k := by
  obtain ⟨x, σ, δ, δ₁, δs, h, D, dd, jk, s, acc, hrun, hD, hrc⟩ :=
    exists_algorithm_13_1_2 O (κg := fun _ => 1) hf hε hεδ (fun _ _ => zero_le_one) hh₀ x₀
      fun y h' hh => (hO y h' hh).mono_err fun i _ => by simp
  have hone : ordMax P.p (fun _ => (1 : ℝ)) = 1 := by
    obtain ⟨j, _, he⟩ := exists_ordMax_eq (ε := fun _ => (1 : ℝ)) P.one_le_p
    exact he
  rw [hone, one_mul] at hrc
  refine ⟨x, σ, δ, δ₁, δs, h, D, dd, jk, s, acc, fun i => f (x i), fun i => f (x i + s i),
    fun i => P.κs * (D i).taylorDecrement P.p (s i), fun _ => True,
    ⟨hκs, hε, hεδ, hrun.x_zero, mem_univ _, hrun.σ_zero, hrun.δ_zero, hrun.h_zero,
      fun k _ => (hrun.oracle k).mono_err fun i _ => by simp,
      fun k _ => (hrun.step k).toARqpStep1,
      UntilHit.of_forall fun k => ⟨hrun.step k, fun ha => ?_⟩⟩,
    hD, hrc⟩
  have hpos := (ARqpDAStep.taylorDecrement_ge (hrun.step k) ha (fun j hj => (hε j hj).1)
    (hrun.sigma_pos k).le).2
  have h0 := (mul_pos P.κs_pos hpos).le
  exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
    fun hR => absurd trivial hR⟩
end ARqpEDA

end CartisGouldToint.Chapter13
