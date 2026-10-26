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
* The runs carry a feasible set `X` and a feasible starting point (`algorithm_13_3_1_feasible`,
  `algorithm_13_3_2_feasible`: TRqEDA-SC and ARqpEDA-SC of §14.2); `algorithm_13_3_1` and
  `algorithm_13_3_2` are the case `X = univ`. The results are proved for the feasible runs under
  f.D0qL (f.D0pL) on an open convex `C ⊇ X` (`AssumptionD0qLOn`), with approximate optimality on
  `X`, in the `_feasible` declarations; the statements for Algorithms 13.3.1–13.3.2 are their
  `X = univ` instances. `trqEDA_card_acc_le_feasible` and `arqpEDA_card_acc_le_feasible` bound the
  accuracy-improving iterations before termination.

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

/-! ### Step 3 with inexact function values -/

/-- The ratio (13.3.10), (13.3.19) with inexact function values:
`ρ_k = (f̄(x_k) - f̄(x_k + s_k)) / \overline{ΔT}_k`. -/
noncomputable def edaRatio (fx fxs pred : ℕ → ℝ) (k : ℕ) : ℝ := (fx k - fxs k) / pred k

/-- **Step 3 of TRqEDA and ARqpEDA** ([cartis2022evaluation], (13.3.1)–(13.3.2), (13.3.9),
(13.3.18)) at a trial iteration `k`, for the predicted decrease `ΔTb = \overline{ΔT}`: the
requested value accuracy satisfies `0 < h_{k,0} ≤ κ_s ΔTb`, the values `f̄(x_k)` and
`f̄(x_k + s_k)` are within `h_{k,0}` of `f`, and if `f̄(x_k)` is not recomputed (`¬ R k`) it is the
trial value of an earlier trial iteration at the same point. -/
structure EDAStep3 (f : ℝⁿ → ℝ) (κs ΔTb : ℝ) (x s : ℕ → ℝⁿ) (acc : ℕ → Prop)
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
def edaStopTR (P : TRqIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j) ∧
    ∑ i ∈ Finset.Icc 1 P.q, h k i * trRadius P Δ k ^ i / i ! ≤
      P.ς * epsMin P.q ε * trRadius P Δ k ^ P.q / P.q ! / 2

/-- **Algorithm 13.3.1 with a feasible set** (TRqEDA-SC, [cartis2022evaluation] §14.2) as a run
predicate: as `algorithm_13_3_1`, for a feasible set `X` (closedness is not used by the analysis)
and a feasible starting point `x₀ ∈ X`, with feasible Step-1 displacements (13.3.6) and every
iteration before termination satisfying `TRqDAStep` on `X`. With `X = univ` this is
`algorithm_13_3_1`. -/
structure algorithm_13_3_1_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (P : TRqIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
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

/-- **Algorithm 13.3.1** (TRqEDA) of [cartis2022evaluation] as a run predicate, with the TRqIDA
constants `P` satisfying (13.3.5) `κ_s ≤ min(η₁, 1 - η₂)/4`, tolerances `ε ∈ (0, 1]^q` with
`ε_min ≤ ϑ`, starting point `x₀`, the sequences of TRqIDA, inexact values `fx`, `fxs` with
accuracies `h₀` and recomputation flags `R`: at every iteration reached the derivatives satisfy
(13.3.4) and the Step-1 displacements (13.3.6); until termination (`edaStopTR`) every iteration
satisfies `TRqDAStep` with the inexact ratio (13.3.10) and, on trial iterations, Step 3. The method
returns `x_ε = x_k` and `δ_ε = min(Δ_k, ϑ)` at termination. This is
`algorithm_13_3_1_feasible` with the feasible set `X = univ`. -/
abbrev algorithm_13_3_1 (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
    (R : ℕ → Prop) : Prop :=
  algorithm_13_3_1_feasible f univ P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R

namespace algorithm_13_3_1_feasible

variable {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ}
  {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop}
  (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
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
  trq_invariants (hrun.steps_lt hk) hrun.Δ_zero hrun.h_zero

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Chapter13.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Chapter13.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem κs_le_η₁ : P.κs ≤ P.η₁ / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

theorem κs_le_η₂ : P.κs ≤ (1 - P.η₂) / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- The iterates reached are feasible. -/
theorem mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) : x k ∈ X :=
  trq_mem (hrun.steps_lt hk) (hrun.x_zero ▸ hrun.x₀_mem)

/-- (13.1.24) with `κ_{∇,max} = 1`: `‖∇̄^i f(x_k)‖ ≤ L_f + κ_h`, under f.D0qL on `C ⊇ X`. -/
theorem norm_D_le {C : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    {k : ℕ} (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) :
    ‖D k i‖ ≤ lipMax L P.q + P.κh := by
  have h' : ‖D k i‖ ≤ ‖iteratedFDeriv ℝ i f (x k)‖ + h k i :=
    norm_le_of_jetApprox (hrun.oracle k hk) hi
  have := hf.norm_iteratedFDeriv_le hi (hXC (hrun.mem hk))
  have := ((hrun.invariants hk).2 i hi).2
  linarith

end algorithm_13_3_1_feasible

section TRqEDA

variable {X C : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ}
  {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ} {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Lemma 13.3.1 with a feasible set** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_3_1` for a TRqEDA-SC run (`algorithm_13_3_1_feasible`) under f.D0qL on an open
convex `C ⊇ X`. -/
theorem lemma_13_3_1_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
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
  obtain ⟨hφ, hdec⟩ := lemma_13_1_2 hs ha hΔpos
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hδeq : trRadius P Δ k = Δ k := min_eq_left (hΔ.trans (min_le_left _ _))
  set j := jk k
  set δ := trRadius P Δ k
  set ph := trPhiHat P Δ D dd jk k
  set Lf := lipMax L P.q
  set C := Lf + 4 * (P.q + 1)! * P.κs
  have hLf : 1 ≤ Lf := hf.one_le_lipMax
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
  have hR := hf.abs_sub_le hjq (hXC (hrun.mem hklt)) (hXC h2.mem)
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
  have hκs4 := hrun.κs_le_η₂
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
  lemma_13_3_1_feasible hf.on_univ (subset_univ _) hrun hk ha hΔ

/-- `trEDA_radius_ge` for a TRqEDA-SC run under f.D0qL on an open convex `C ⊇ X`. -/
theorem trEDA_radius_ge_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  rw [mul_one] at hκΔ'
  set a := (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs) with ha_def
  have hLf := hf.one_le_lipMax
  have hC : 1 ≤ lipMax L P.q + 4 * (P.q + 1)! * P.κs := by
    have := P.κs_pos; nlinarith [show (0 : ℝ) ≤ 4 * (P.q + 1)! * P.κs by positivity]
  have ha0 : 0 ≤ a := div_nonneg P.one_sub_η₂_pos.le (zero_le_one.trans hC)
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (zero_lt_one.trans_le hC)]
    linarith [P.η₂_pos]
  have hεmin := hrun.epsMin_pos
  have hc := trq_delta_ge (hrun.steps_lt hk) hrun.Δ_zero ha0 hκΔ0.le hκΔ'
    (c := P.ς * epsMin P.q ε / 2)
    (fun i hi hai hΔ => (lemma_13_3_1_feasible hf hXC hrun (fun j hj => hk j (by omega)) hai hΔ).1)
    (fun i hi hai => (lemma_13_1_2 (hrun.steps_lt hk i hi) hai
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

/-- **Lemma 13.1.4 for TRqEDA** ([cartis2022evaluation], §13.3.1: "Lemma 13.1.4 — with a
simplified value of `κ_δ` — follows"): under f.D0qL, for an admissible `κ_Δ` with
`κ_{∇,max} = 1`, at every iteration `k` reached by TRqEDA, `δ_k ≥ ς κ_δ ε_min` with
`κ_δ = κ_Δ/2` (13.1.32). -/
theorem trEDA_radius_ge (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) :
    P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k :=
  trEDA_radius_ge_feasible hf.on_univ (subset_univ _) hrun hκΔ hk

/-- **Lemma 13.3.2 with a feasible set** ([cartis2022evaluation] §14.2): for a TRqEDA-SC run under
f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`, every trial iteration before termination
satisfies (13.1.34) and every successful one (13.1.35), as in `lemma_13_3_2`. -/
theorem lemma_13_3_2_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
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
    (trEDA_radius_ge_feasible hf hXC hrun hκΔ hklt)
  refine ⟨h1, fun hρ => ?_⟩
  have h3 := hrun.step3 hk ha
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) :=
    lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) h1
  have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
    (h3.fxs_err.trans h3.h₀_le) hρ hrun.κs_le_η₁
  rw [((hrun.step hk).accept ha).eq_add hρ]
  have hη := P.η₁_pos
  calc P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1)
      = P.η₁ / 2 * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) := by
        field_simp
    _ ≤ P.η₁ / 2 * (D k).taylorDecrement (jk k) (s k) := by gcongr
    _ ≤ f (x k) - f (x k + s k) := h2

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
  lemma_13_3_2_feasible hf.on_univ (subset_univ _) hrun hκΔ hk ha

/-- **Lemma 13.3.3 (i) with a feasible set** ([cartis2022evaluation] §14.2): if TRqEDA-SC terminates
at iteration `k`, then `x_k` is an `(ε, δ_k)`-approximate `q`-th order minimizer on `X` (measures
over `{e | x_k + e ∈ X}`), `δ_k = min(Δ_k, ϑ)`. -/
theorem lemma_13_3_3_i_feasible
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
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

/-- **Lemma 13.3.3 (i)** ([cartis2022evaluation]): if TRqEDA terminates at iteration `k`
(Step 1.4.1: (13.3.7) fails at every order and (13.3.8) holds), then `x_k` is an
`(ε, δ_k)`-approximate `q`-th order minimizer, `δ_k = min(Δ_k, ϑ) ∈ (0, 1]`. -/
theorem lemma_13_3_3_i (hrun : algorithm_13_3_1 f P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j) (hstop : edaStopTR P ε D Δ h dd k) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trRadius P Δ k) := by
  have := lemma_13_3_3_i_feasible hrun hk hstop
  rwa [setOf_add_mem_univ] at this

/-- **Lemma 13.3.3 (ii) with a feasible set** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_3_3_ii` for a TRqEDA-SC run under f.D0qL on an open convex `C ⊇ X`. -/
theorem lemma_13_3_3_ii_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) 1 κΔ)
    (hk : ∀ j < k, ¬ edaStopTR P ε D Δ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopTR P ε D Δ h dd k := by
  refine ⟨hpass, ?_⟩
  have hΔ := (hrun.invariants hk).1.1
  obtain ⟨hδ0, hδ1⟩ := trRadius_mem (P := P) hΔ
  have hδm := trEDA_radius_ge_feasible hf hXC hrun hκΔ hk
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
  lemma_13_3_3_ii_feasible hf.on_univ (subset_univ _) hrun hκΔ hk hpass hh

/-- **The accuracy-improving iterations of TRqEDA-SC** (proof of Theorem 13.3.4,
[cartis2022evaluation]): under f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`
(`κ_{∇,max} = 1`), if the run has not terminated at any `j ≤ k`, then
`|𝒜_k| ≤ q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem trqEDA_card_acc_le_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
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
  have hLb1 : 1 ≤ Lb := by have := hf.one_le_lipMax; have := P.κh_pos; linarith
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
    (N := P.q * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_pos hκacc hεmin
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
          (hrun.invariants hjlt).1.1 hLb1 (fun i hi => hrun.norm_D_le hf hXC hjlt hi)
          (by positivity) (by linarith) hrun.eps_mem
          (trEDA_radius_ge_feasible hf hXC hrun hκΔ'' hjlt)
          fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right trKappaAcc_le (by positivity)
      · push Not at hfail
        refine hjs j le_rfl (lemma_13_3_3_ii_feasible hf hXC hrun hκΔ'' hjlt hfail fun i hi => ?_)
        calc h j i ≤ κacc * em ^ (P.q * (P.q + 1)) := hhi i hi
          _ = 1 * κacc * em ^ (P.q * (P.q + 1)) := by ring
          _ ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_trKappaAcc_le hκΔ0 zero_le_one) hpowq (by positivity)
                (by positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.q * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **Theorem 13.3.4 with a feasible set** ([cartis2022evaluation] §14.2): complexity of TRqEDA-SC
(the TRqEDA-SC row of Theorem 14.2.4). Under f.D0qL on an open convex `C ⊇ X` and f.bB.X
(`f ≥ f_low` on `X`), every TRqEDA-SC run terminates at some `k_ε` with `x_{k_ε}` an
`(ε, δ_ε)`-approximate minimizer on `X`, within the evaluation bounds of `theorem_13_3_4`. -/
theorem theorem_13_3_4_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_3_1_feasible f X P ε x₀ x Δ h D dd jk s acc fx fxs h₀ R) {κΔ : ℝ}
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
  have hLb1 : 1 ≤ Lb := by have := hf.one_le_lipMax; have := P.κh_pos; linarith
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
      (fun j hj hs => by rw [(hrun.step fun i hi => hk i (hi.trans hj)).x_succ_eq hs])
      (fun j hj hs =>
        (lemma_13_3_2_feasible hf hXC hrun hκΔ'' (fun i hi => hk i (hi.trans hj)) hs.1).2 hs.2)
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
      (trEDA_radius_ge_feasible hf hXC hrun hκΔ'' fun j hj => hk j (Nat.lt_succ_iff.1 hj)).trans
        (min_le_left _ _)
    have h1 := lemma_13_1_1 (fun i hi => hrun.step fun j hj => hk j (hj.trans hi))
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
    fun k hk => trqEDA_card_acc_le_feasible hf hXC hrun hκΔ'' hk
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
  refine ⟨kε, hkε, lemma_13_3_3_i_feasible hrun hklt hkε.test, (trRadius_mem hΔ).1,
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
  have := theorem_13_3_4_feasible hf.on_univ (subset_univ _) (fun y _ => hb y) hrun hκΔ
  simpa only [setOf_add_mem_univ] using this

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
  have hεmin : 0 < epsMin P.q ε := Chapter13.epsMin_pos P.one_le_q fun j hj => (hε j hj).1
  refine ⟨x, Δ, h, _, dd, jk, s, acc, fun i => f (x i), fun i => f (x i + s i),
    fun i => P.κs * (O (x i) (h i)).taylorDecrement (jk i) (s i), fun _ => True,
    ⟨hκs, hε, hϑ, hx, mem_univ _, hΔ, hh, fun k _ => hO _ _ fun i hi =>
      ((trq_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, fun k _ j hj => ?_,
      UntilHit.of_forall fun k => ⟨hstep k, fun ha => ?_⟩⟩, fun _ => rfl⟩
  · exact (hstep k).witness j hj
  · have hΔk := trq_delta_pos (k := k) (fun i _ => hstep i) hΔ
    obtain ⟨hφ, hdec⟩ := lemma_13_1_2 (hstep k) ha hΔk
    have hφ0 : 0 < P.ς * epsMin P.q ε / 2 := by have := P.ς_pos; positivity
    have hδ := (trRadius_mem (P := P) hΔk).1
    have hpos : 0 < (O (x k) (h k)).taylorDecrement (jk k) (s k) :=
      lt_of_lt_of_le (by have := hφ0.trans_le hφ; positivity) hdec
    have h0 := (mul_pos P.κs_pos hpos).le
    exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
      fun hR => absurd trivial hR⟩

end TRqEDA

/-! ### ARqpEDA -/

/-- The termination test of ARqpEDA ([cartis2022evaluation], Algorithm 13.3.2, Steps 1.5–1.5.1):
(13.3.15) holds at every order and (13.3.17)
`∑_{i=1}^j h_{k,i} (δ^{(1)}_{k,j})^i/i! ≤ ½ ς ε_j (δ^{(1)}_{k,j})^j/j!` for every `j ∈ [1, q]`. -/
def edaStopAR (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (k : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j) ∧
    ∀ j ∈ Finset.Icc 1 P.q, ∑ i ∈ Finset.Icc 1 j, h k i * δ₁ k j ^ i / i ! ≤
      P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- **Algorithm 13.3.2 with a feasible set** (ARqpEDA-SC, [cartis2022evaluation] §14.2) as a run
predicate: as `algorithm_13_3_2`, for a feasible set `X` (closedness is not used by the analysis)
and a feasible starting point `x₀ ∈ X`, Step 1 (`ARqpStep1`) and the iterations before
termination (`ARqpDAStep`) being performed on `X`. With `X = univ` this is `algorithm_13_3_2`. -/
structure algorithm_13_3_2_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
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

/-- **Algorithm 13.3.2** (ARqpEDA) of [cartis2022evaluation] as a run predicate, with the ARqpIDA
constants `P` satisfying (13.3.13) `κ_s ≤ min(η₁, 1 - η₂)/4`, tolerances `ε ∈ (0, 1]^q` with
`ε ≤ δ₀`, starting point `x₀`, the sequences of ARqpIDA, inexact values `fx`, `fxs` with
accuracies `h₀` and recomputation flags `R`: at every iteration reached the derivatives satisfy
(13.3.4) up to order `p` and Step 1 (13.3.14)–(13.3.16) is performed (`ARqpStep1`); until
termination (`edaStopAR`) every iteration satisfies `ARqpDAStep` with the inexact ratio (13.3.19)
and, on trial iterations, Step 3. The method returns `x_ε = x_k` and `δ_ε = δ^{(1)}_k`. This is
`algorithm_13_3_2_feasible` with the feasible set `X = univ`. -/
abbrev algorithm_13_3_2 (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x₀ : ℝⁿ)
    (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ) (R : ℕ → Prop) : Prop :=
  algorithm_13_3_2_feasible f univ P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R

namespace algorithm_13_3_2_feasible

variable {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop}
  (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
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
  arqp_invariants (hrun.steps_lt hk) hrun.σ_zero hrun.δ_zero hrun.h_zero

theorem sigma_pos {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : 0 < σ k :=
  P.σmin_pos.trans_le (hrun.invariants hk).1

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Chapter13.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Chapter13.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem κs_le_η₁ : P.κs ≤ P.η₁ / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))

theorem κs_le_η₂ : P.κs ≤ (1 - P.η₂) / 4 :=
  hrun.κs_le.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))

/-- The iterates reached are feasible. -/
theorem mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : x k ∈ X :=
  arqp_mem (hrun.steps_lt hk) (hrun.x_zero ▸ hrun.x₀_mem)

/-- (13.1.63) with `κ_{∇,max} = 1`: `‖∇̄^i f(x_k)‖ ≤ L_f + κ_h` for `i ∈ [1, p]`, under f.D0pL
on `C ⊇ X`. -/
theorem norm_D_le {C : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖D k i‖ ≤ lipMax L P.p + P.κh := by
  have h' : ‖D k i‖ ≤ ‖iteratedFDeriv ℝ i f (x k)‖ + h k i :=
    norm_le_of_jetApprox (hrun.oracle k hk) hi
  have := hf.norm_iteratedFDeriv_le hi (hXC (hrun.mem hk))
  have := ((hrun.invariants hk).2.2 i hi).2
  linarith

/-- The radii `δ^{(1)}_k` lie in `(0, 1]^q` at every iteration reached. -/
theorem delta₁_mem {k : ℕ} (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
  ⟨(hrun.step1 k hk).radius_pos j hj,
    ((hrun.step1 k hk).radius_le j hj).trans ((hrun.invariants hk).2.1 j hj).2⟩

end algorithm_13_3_2_feasible

section ARqpEDA

variable {X C : Set ℝⁿ} {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {x : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {fx fxs h₀ : ℕ → ℝ}
  {R : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Lemma 13.3.5 with a feasible set** ([cartis2022evaluation] §14.2): `σ_k ≤ σ_max` at every
iteration reached by an ARqpEDA-SC run (`algorithm_13_3_2_feasible`) under f.D0pL on an open convex
`C ⊇ X`. -/
theorem lemma_13_3_5_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arSigmaMax P (L P.p) 1 := by
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
    obtain ⟨hlow, hpos⟩ := lemma_13_1_13 hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hilt).le
    set t := ‖s i‖
    have hherr : ∀ l ∈ Finset.Icc 1 P.p, h i l ≤ 1 * κs' * t ^ (P.p - l + 1) := by
      intro l hl
      rw [one_mul]
      rcases lt_or_ge t 1 with ht | ht
      · exact (h2.h_le_of_not_acc ha ht l hl).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · exact (((hrun.invariants hilt).2.2 l hl).2.trans (le_max_right _ _)).trans
          (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy zero_le_one hκs' (hrun.oracle i hilt)
      hherr le_rfl
    have hR := hf.abs_sub_le le_rfl (hXC (hrun.mem hilt)) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * 1) ≤ (1 - P.η₂) * σ i := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσi
      linarith
    have hval := h3.fx_err.trans h3.h₀_le
    have hval' := h3.fxs_err.trans h3.h₀_le
    have hκs4 := hrun.κs_le_η₂
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

/-- **Lemma 13.3.5** ([cartis2022evaluation], corrected constant): under f.D0pL, every iteration
`k` reached by ARqpEDA has `σ_k ≤ σ_max` with `σ_max = arSigmaMax P L_{f,p} 1`
((13.1.77) with `κ_{∇,max} = 1` and `κ_s' = max(κ_s, κ_h)`). -/
theorem lemma_13_3_5 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) : σ k ≤ arSigmaMax P (L P.p) 1 :=
  lemma_13_3_5_feasible hf.on_univ (subset_univ _) hrun hk

/-- **Lemma 13.3.6 (i) with a feasible set** ([cartis2022evaluation] §14.2): if ARqpEDA-SC
terminates at iteration `k`, then `x_k` is an `(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer on
`X` (measures over `{e | x_k + e ∈ X}`) with `δ^{(1)}_k ∈ (0, 1]^q`. -/
theorem lemma_13_3_6_i_feasible
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
  have hmem := hrun.delta₁_mem hk
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

/-- **Lemma 13.3.6 (i)** ([cartis2022evaluation]): if ARqpEDA terminates at iteration `k`
(Step 1.5.1), then `x_k` is an `(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer with
`δ^{(1)}_k ∈ (0, 1]^q`. -/
theorem lemma_13_3_6_i (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j) (hstop : edaStopAR P ε D δ₁ h dd k) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) := by
  have := lemma_13_3_6_i_feasible hrun hk hstop
  rwa [setOf_add_mem_univ] at this

/-- **Lemma 13.3.6 (ii) with a feasible set** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_3_6_ii` for an ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X`. -/
theorem lemma_13_3_6_ii_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + P.κh) σ δs s acc i)
    (hk : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.ς * arKappaDelta1 P (lipMax L P.p + P.κh)
      (arSigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k := by
  refine ⟨hpass, fun j hj => ?_⟩
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := arqp_radius_ge (hrun.steps_lt hk) (hrun.step1 k hk) hrun.σ_zero hrun.δ_zero
    hrun.h_zero hrun.eps_mem hrun.eps_le hLb
    (fun i hi ℓ hℓ => hrun.norm_D_le hf hXC (fun l hl => hk l (hl.trans_le hi)) hℓ)
    (fun i hi => lemma_13_3_5_feasible hf hXC hrun fun l hl => hk l (hl.trans_le hi))
    (fun i _ => hrc i)
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hmem := hrun.delta₁_mem hk j hj
  set δ := δ₁ k j
  set em := epsMin P.q ε
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hεj := hrun.eps_mem j hj
  set e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)
  have he0 : 0 ≤ e := by positivity
  have hm0 : 0 ≤ κ * em := by positivity
  have hm1 : κ * em ≤ 1 := mul_le_one_of_le_one hκ1 hεmin.le hεmin1
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
      (arSigmaMax P (L P.p) 1) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    edaStopAR P ε D δ₁ h dd k :=
  lemma_13_3_6_ii_feasible hf.on_univ (subset_univ _) hrun hrc hk hpass hh

/-- `eda_radius_inequality` for an ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X`. -/
theorem eda_radius_inequality_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hs1 : ‖s k‖ < 1)
    (hnot : ¬ ((∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd (k + 1) j) ∧
      ∀ j ∈ Finset.Icc 1 P.q, δ₁ (k + 1) j = δ (k + 1) j)) :
    ∃ j ∈ Finset.Icc 1 P.q, (P.ς / 2 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arSigmaMax P (L P.p) 1 + 4 * P.κs) *
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
    · have : ¬ ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd (k + 1) j := fun hp => hnot ⟨hp, hall⟩
      push Not at this
      obtain ⟨j, hj, hfail⟩ := this
      refine ⟨j, hj, dd (k + 1) j, ?_, (hS1.witness j hj).mem, ?_⟩
      · rw [← hall j hj]; exact (hS1.witness j hj).norm_le
      · unfold arPass at hfail; rw [← hall j hj]; exact not_le.1 hfail
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      obtain ⟨-, -, d₀, hd₀n, hd₀X, hd₀⟩ :=
        hS1.halving j hj (lt_of_le_of_ne (hS1.radius_le j hj) hne)
      exact ⟨j, hj, d₀, hd₀n, hd₀X, hd₀⟩
  refine ⟨j, hj, ?_⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ P.p := hjq.trans P.q_le_p
  have hx : x (k + 1) = x k + s k := hs.x_succ_eq_add ha hρ
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
    (show (0 : ℝⁿ) ∈ {e | x (k + 1) + e ∈ X} by simpa using hrun.mem hk1) hδv0
  rw [hh] at htrans
  set e₀ := P.κs * ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) with he₀def
  have hacc := h2.h_le_of_not_acc ha hs1
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
  have := radius_inequality_of_measure_gt hf.convex (fun y hy => hf.contDiffAt le_rfl hy)
    (hf.lipschitz le_rfl) (zero_le_one.trans (hf.one_le le_rfl)) (hXC (hrun.mem hklt))
    (hXC h2.mem) (hrun.oracle k hklt) zero_le_one P.κs_pos.le
    (fun i hi => by rw [one_mul]; exact hacc i hi)
    (hrun.sigma_pos hklt).le (lemma_13_3_5_feasible hf hXC hrun hklt) hjp (by simpa using h2.mem)
    hδv0 h₁ h₂
  have e : (L P.p + arSigmaMax P (L P.p) 1 + 3 * 1 * P.κs) *
      ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) + e₀ =
      (L P.p + arSigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δv ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by ring
  rw [e] at this
  exact this.le

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
      (L P.p + arSigmaMax P (L P.p) 1 + 4 * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  eda_radius_inequality_feasible hf.on_univ (subset_univ _) hrun hk ha hρ hs1 hnot

/-- The constant `L_{f,p} + σ_max + 4 κ_s` of the ARqpEDA radius inequality
(`σ_max = arSigmaMax P L_{f,p} 1`, Lemma 13.3.5). -/
noncomputable def arEDAConstA (P : ARqpIDAParams) (L : ℕ → ℝ) : ℝ :=
  L P.p + arSigmaMax P (L P.p) 1 + 4 * P.κs

theorem one_le_arEDAConstA {P : ARqpIDAParams} {L : ℕ → ℝ} (hL : 1 ≤ L P.p) :
    1 ≤ arEDAConstA P L := by
  have h1 : 0 ≤ arSigmaMax P (L P.p) 1 := P.σ₀_pos.le.trans (le_max_left _ _)
  have := P.κs_pos
  unfold arEDAConstA; linarith

/-- Step 1 at iteration `i` passes every test (13.3.15) with unchanged radii. -/
def edaPassUnchanged (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (i : ℕ) : Prop :=
  (∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd i j) ∧ ∀ j ∈ Finset.Icc 1 P.q, δ₁ i j = δ i j

/-- `arqpEDA_step_bound` for an ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X`, for
either mode `u` of the radii control (`RadiiControlOf`; the cases `q ≤ 2` and `q > 2` of
`arqpEDA_step_bound` become `u` and `¬ u`). -/
theorem arqpEDA_step_bound_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : RadiiControlOf u P ε (lipMax L P.p + P.κh) σ δs s acc k) (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) *
          arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) ^ (j - 1) *
            ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  have hnot := hgood.resolve_left (not_le.2 hs1)
  obtain ⟨j, hj, hineq⟩ := eda_radius_inequality_feasible hf hXC hrun hk ha hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step hk
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have h2 := hs.step2_of_not_acc ha
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial ha, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  set κ := arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le ha hs1 hrun.eps_mem hLb (lemma_13_3_5_feasible hf hXC hrun hklt) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc ha hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (lemma_13_1_13 hs ha (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos hklt).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arEDAConstA P L := zero_lt_one.trans_le (one_le_arEDAConstA (hf.one_le le_rfl))
  exact arqp_pow_ge_of_radius_ineq (by linarith) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- The step-length bounds of ARqpEDA (as `arqpIDA_step_bound`): at a successful iteration `k`
reached by ARqpEDA with the radii control at `k`, such that `‖s_k‖ ≥ 1` or Step 1 at `k + 1` does
not pass with unchanged radii, either `‖s_k‖ ≥ 1` or the conclusions of
`arqp_pow_ge_of_radius_ineq` hold for some order `j` with `a = ς/2 - θ` (`θ < ς/2`),
`A = L_{f,p} + σ_max + 4 κ_s` and `κ = κ_{δ,min}`. -/
theorem arqpEDA_step_bound (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_3_2 f P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    (hrc : RadiiControl P ε (lipMax L P.p + P.κh) σ δs s acc k) (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((P.q ≤ 2 → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (2 < P.q → (P.ς / 2 - P.θ) / (2 * j ! * arEDAConstA P L) *
          arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
            (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) ^ (j - 1) *
            ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  obtain ⟨j, hj, h⟩ := arqpEDA_step_bound_feasible hf.on_univ (subset_univ _) hrun hrc hθ hk ha hρ
    hgood
  exact ⟨j, hj, h.imp_right fun h => ⟨h.1, fun hq => h.2 (not_le.2 hq)⟩⟩

/-- **Lemma 13.3.7 with a feasible set** ([cartis2022evaluation] §14.2): for an ARqpEDA-SC run under
f.D0pL on an open convex `C ⊇ X`, the decreases of `lemma_13_3_7`, for either mode `u` of the radii
control (`RadiiControlOf`), with `π_j = arPiOf u p j` and the constant `arStepConstOf u`. -/
theorem lemma_13_3_7_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} [Decidable u] (hrc : RadiiControlOf u P ε (lipMax L P.p + P.κh) σ δs s acc k)
    (hθ : P.θ < P.ς / 2)
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) (ha : ¬ acc k)
    (hρ : P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) k)
    (hgood : 1 ≤ ‖s k‖ ∨ ¬ edaPassUnchanged P ε D δ δ₁ dd (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨j, hj, hb⟩ := arqpEDA_step_bound_feasible hf hXC hrun hrc hθ hk ha hρ hgood
  have hklt : ∀ j < k, ¬ edaStopAR P ε D δ₁ h dd j := fun j hj => hk j hj.le
  have hs := hrun.step hk
  obtain ⟨hlow, hpos⟩ := lemma_13_1_13 hs ha (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos hklt).le
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
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
    (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg ha0.le (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Chapter13.epsMin_pos P.one_le_q fun j hj =>
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
    (h3.fxs_err.trans h3.h₀_le) hρ hrun.κs_le_η₁
  rw [(hs.accept ha).eq_add hρ]
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ / 2 * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by ring
    _ ≤ P.η₁ / 2 * (D k).taylorDecrement P.p (s k) := by gcongr
    _ ≤ f (x k) - f (x k + s k) := h2

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
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ)
          (arEDAConstA P L) (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1))) /
          2 * epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  lemma_13_3_7_feasible hf.on_univ (subset_univ _) hrun hrc hθ hk ha hρ hgood

/-- **The accuracy-improving iterations of ARqpEDA-SC** (proof of Theorem 13.3.8,
[cartis2022evaluation]): under f.D0pL on an open convex `C ⊇ X` and the radii control at every
iteration, if the run has not terminated at any `j ≤ k`, then
`|𝒜_k| ≤ p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem arqpEDA_card_acc_le_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ edaStopAR P ε D δ₁ h dd j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
          (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
          P.κh)| / |Real.log P.γh| + 1 := by
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  set σmax := arSigmaMax P (L P.p) 1
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
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd j i
      · have hrad := arqp_radius_ge (hrun.steps_lt hjlt) (hrun.step1 j hjlt) hrun.σ_zero
          hrun.δ_zero hrun.h_zero hrun.eps_mem hrun.eps_le hLb
          (fun i hi ℓ hℓ => hrun.norm_D_le hf hXC (fun l hl => hjlt l (hl.trans_le hi)) hℓ)
          (fun i hi => lemma_13_3_5_feasible hf hXC hrun fun l hl => hjlt l (hl.trans_le hi))
          (fun i _ => hrc i)
        refine (((hrun.step hjs).step2 hfail).not_acc_of_le (σbar := σmax)
          (hrun.step1 j hjlt).radius_pos hLb (fun i hi => hrun.norm_D_le hf hXC hjlt hi)
          (hrun.sigma_pos hjlt).le hκ0.le (arKappaDelta1_le_one hLb) hrun.eps_mem
          (fun l hl => (hrad l hl).1) fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hjs j le_rfl (lemma_13_3_6_ii_feasible hf hXC hrun hrc hjlt hfail fun i hi => ?_)
        calc h j i ≤ κacc * em ^ (P.p * (P.q + 1)) := hhi i hi
          _ = 1 * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le zero_le_one) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **The complexity argument of Theorem 13.3.8 with a feasible set** ([cartis2022evaluation]
§14.2): `arqpEDA_complexity` for an ARqpEDA-SC run under f.D0pL on an open convex `C ⊇ X` and
f.bB.X, with approximate optimality on `X` at termination. -/
theorem arqpEDA_complexity_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_3_2_feasible f X P ε x₀ x σ δ δ₁ δs h D dd jk s acc fx fxs h₀ R)
    {u : Prop} (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + P.κh) σ δs s acc i) {c : ℝ}
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
              (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / c + 2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq := P.one_le_q
  have hp := P.one_le_p
  set stop := edaStopAR P ε D δ₁ h dd
  set ρ := edaRatio fx fxs fun i => (D i).taylorDecrement P.p (s i)
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set Lb := lipMax L P.p + P.κh
  have hLb : 1 ≤ Lb := by have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  set σmax := arSigmaMax P (L P.p) 1
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
    fun k hk => arqpEDA_card_acc_le_feasible hf hXC hrun hrc hk
  -- the objective does not increase before termination
  have hmono : ∀ j, (∀ i ≤ j, ¬ stop i) → f (x (j + 1)) ≤ f (x j) := by
    intro j hj
    have hs := hrun.step hj
    by_cases hsucc : ¬ acc j ∧ P.η₁ ≤ ρ j
    · have hjlt : ∀ i < j, ¬ stop i := fun i hi => hj i hi.le
      have h3 := hrun.step3 hj hsucc.1
      have hpos := (lemma_13_1_13 hs hsucc.1 (fun l hl => (hrun.eps_mem l hl).1)
        (hrun.sigma_pos hjlt).le).2
      have h2 := sub_ge_of_inexact_ratio hpos (h3.fx_err.trans h3.h₀_le)
        (h3.fxs_err.trans h3.h₀_le) hsucc.2 hrun.κs_le_η₁
      rw [(hs.accept hsucc.1).eq_add hsucc.2]
      have := mul_pos (half_pos P.η₁_pos) hpos
      linarith
    · rw [hs.x_succ_eq hsucc]
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
    have h1 := lemma_13_1_9 (fun i hi => hrun.step fun j hj => hk j (hj.trans hi))
      hrun.σ_zero hrun.δ_zero hrun.h_zero
      (lemma_13_3_5_feasible hf hXC hrun fun j hj => hk j (Nat.lt_succ_iff.1 hj))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ ρ i)) kε : ℝ) + 1 ≤
      derivEvalCount acc kε + derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hklt : ∀ j < kε, ¬ stop j := fun j hj => hkε.not_test_of_lt hj
  obtain ⟨hmem, happrox⟩ := lemma_13_3_6_i_feasible hrun hklt hkε.test
  refine ⟨kε, hkε, hmem, happrox, ?_, ?_⟩
  · have := edaFunEvalCount_le acc R kε
    calc (edaFunEvalCount acc R kε : ℝ) ≤ 2 * ((derivEvalCount (fun i => ¬ acc i) kε : ℝ) - 1) :=
          this
      _ ≤ 2 * NT := by linarith
      _ = _ := by rw [hNT_def, hN_def, hNA_def]
  · calc _ ≤ (NA + 1) + (N + NA + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def, hN_def]; ring

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
              (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        (f x₀ - flow) / c + 2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
            (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
            P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have := arqpEDA_complexity_feasible hf.on_univ (subset_univ _) (fun y _ => hb y) hrun hrc hc hdec
  simpa only [setOf_add_mem_univ] using this

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
                (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : P.q ≤ 2 := hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) / (2 * P.q ! * arEDAConstA P L)) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ))) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Chapter13.epsMin_pos P.one_le_q fun j hj =>
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
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
              epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
            (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
              |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
                (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
                P.κh)| / |Real.log P.γh| + 1) + 1) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
          Real.log (arSigmaMax P (L P.p) 1 / P.σ₀) / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
          P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement P.p (s i)) i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
              (f x₀ - flow) /
            epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
          2 * (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
            |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + P.κh)
              (arSigmaMax P (L P.p) 1)) (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1) 1 /
              P.κh)| / |Real.log P.γh| + 1) + 2 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := (P.σmin / ((P.p + 1)! : ℝ) *
            ((P.ς / 2 - P.θ) * arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
              (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) ^ (P.q - 1) /
              (2 * P.q ! * arEDAConstA P L)) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
      (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb : 1 ≤ lipMax L P.p + P.κh := by
    have := hf.one_le_lipMax; have := P.κh_nonneg; linarith
  have hA := one_le_arEDAConstA (P := P) (hf.one_le le_rfl)
  have ha0 : 0 < P.ς / 2 - P.θ := by linarith
  have hκpos : 0 < κΔm := by
    rw [← hκ']
    have hC : 0 < arStepConst P.q P.p (P.ς / 2 - P.θ) (arEDAConstA P L)
        (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) := by
      have hk0 : 0 < arKappaHat P.q (P.ς / 2 - P.θ) (arEDAConstA P L)
          (arKappaDelta1 P (lipMax L P.p + P.κh) (arSigmaMax P (L P.p) 1)) :=
        lt_min (arKappaDelta1_pos (by linarith)) (by positivity)
      unfold arStepConst arStepConstOf
      split_ifs
      positivity
    have := P.σmin_pos
    positivity
  have hmpos : 0 < m := Chapter13.epsMin_pos P.one_le_q fun j hj =>
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
  have hpos := (lemma_13_1_13 (hrun.step k) ha (fun j hj => (hε j hj).1)
    (hrun.sigma_pos k).le).2
  have h0 := (mul_pos P.κs_pos hpos).le
  exact ⟨mul_pos P.κs_pos hpos, le_rfl, by simpa using h0, by simpa using h0,
    fun hR => absurd trivial hR⟩

end ARqpEDA

end CartisGouldToint.Chapter13
