import Numlib.Optimization.Complexity.DynamicAccuracy
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.Basic
import Numlib.Optimization.ModelBased.HighOrder.TRq
import Numlib.Optimization.ModelBased.InexactRatio

/-!
# TRqIDA: a trust-region method with inexact derivatives and implicit dynamic accuracy

The trust-region method TRqIDA ([cartis2022evaluation], Algorithm 13.1.1) looks for
`(ε, δ)`-approximate `q`-th order minimizers using exact function values and inexact derivative
jets `D_k` with `‖D_k i - ∇^i f(x_k)‖ ≤ κ_{∇,i} h_{k,i}` (13.1.2), for constants `κ_{∇,i}`
unknown to the method and accuracies `h_{k,i}` controlled by it: an iteration whose step is too
short for the current accuracies (13.1.9) only reduces them (it is *accuracy-improving*).

The analysis is stated for runs on a feasible set `X` (Step-1 displacements and trial points
in `{e | x_k + e ∈ X}`, [cartis2022evaluation] §14.2) under the smoothness hypothesis
`LipschitzDerivsAnchored f C A 0 q L` with normalized constants `L_j ≥ 1`, `X ⊆ C` and an anchor set
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`: the objective does not increase along the runs, so the iterates are
anchors, derivative estimates are made at iterates, and trial points are related to them by
Taylor's theorem anchored at the iterate. The unconstrained methods of Chapter 13 are the case
`X = C = A = univ`.

## Main definitions

* `TRqIDAParams`: the constants of Step 0;
* `TRqDAStep`: one iteration (Steps 1, 2, 4, 5) given the value of the ratio, shared with TRqEDA;
* `IsTRqIDARun`: a run on a feasible set with the exact-value ratio (13.1.16); `trqIDATest`: the
  (unobservable) approximate-optimality test.

## Main results

* `trqDA_card_trial_le` (Lemma 13.1.1), `TRqDAStep.trqGap_ge` (Lemma 13.1.2),
  `trqDA_delta_ge` (the radius bound behind Lemma 13.1.4);
* `IsTRqIDARun.ratio_ge`, `.delta_ge`, `.decrease_ge`, `.not_acc_of_le`, `.trqIDATest_of_pass`
  (Lemmas 13.1.3–13.1.7), `.card_acc_le` (the accuracy-improving iterations),
  `.complexity` (Theorem 13.1.8), `.le_card_succ` (Lemma 14.2.3, TRqIDA row);
* `exists_trqDA_run`: runs exist for every oracle (in finite dimension).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### TRqIDA: constants and one iteration -/

/-- The constants of Algorithm 13.1.1 (TRqIDA, [cartis2022evaluation], Step 0): the trust-region
constants (`0 < η₁ ≤ η₂ < 1`, `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃`, `Δ₀ > 0`), the criticality order `q ≥ 1`,
`ϑ ∈ (0, 1]` with `ϑ ≤ Δ₀ ≤ Δ_max`, `ς ∈ (0, 1]`, `γ_h ∈ (0, 1)`, `κ_s > 0`, and initial
accuracies `0 < h_{0,i} ≤ κ_h` (`i ∈ [1, q]`). The tolerance-dependent requirement
`ϑ ≥ ε_min` is part of the run predicate. -/
structure TRqIDAParams extends TRParams where
  /-- The criticality order. -/
  q : ℕ
  /-- The threshold on the optimality radius. -/
  ϑ : ℝ
  /-- The maximal trust-region radius. -/
  Δmax : ℝ
  /-- The accuracy reduction factor. -/
  γh : ℝ
  /-- The constant of the accuracy test (13.1.9). -/
  κs : ℝ
  /-- The bound on the initial accuracies. -/
  κh : ℝ
  /-- The fraction of the measure achieved by the Step-1 displacements. -/
  ς : ℝ
  /-- The initial requested accuracies. -/
  h₀ : ℕ → ℝ
  one_le_q : 1 ≤ q
  ϑ_pos : 0 < ϑ
  ϑ_le_one : ϑ ≤ 1
  ϑ_le_Δ₀ : ϑ ≤ Δ₀
  Δ₀_le_Δmax : Δ₀ ≤ Δmax
  ς_pos : 0 < ς
  ς_le_one : ς ≤ 1
  γh_pos : 0 < γh
  γh_lt_one : γh < 1
  κs_pos : 0 < κs
  h₀_pos : ∀ i ∈ Finset.Icc 1 q, 0 < h₀ i
  h₀_le : ∀ i ∈ Finset.Icc 1 q, h₀ i ≤ κh

namespace TRqIDAParams

variable (P : TRqIDAParams)

theorem kappaH_pos : 0 < P.κh :=
  (P.h₀_pos 1 (Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩)).trans_le
    (P.h₀_le 1 (Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩))

theorem one_mem_Icc : 1 ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩

end TRqIDAParams

section TRStep

variable {X : Set E} {P : TRqIDAParams} {ε : ℕ → ℝ} {x : ℕ → E} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ}
  {s : ℕ → E} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The optimality radius `δ_k = min(Δ_k, ϑ)` of TRqIDA (Step 1). -/
noncomputable abbrev trqDARadius (P : TRqIDAParams) (Δ : ℕ → ℝ) (k : ℕ) : ℝ := min (Δ k) P.ϑ

/-- The Step-1.2 test (13.1.14) at order `j` fails to certify optimality:
`\overline{ΔT}_{f,j}(x_k, d_{k,j}) > ½ ς ε_j δ_k^j / j!`. -/
def trqDAFail (P : TRqIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ)
    (Δ : ℕ → ℝ) (dd : ℕ → ℕ → E) (k j : ℕ) : Prop :=
  P.ς * ε j * trqDARadius P Δ k ^ j / j ! / 2 < (D k).taylorDecrement j (dd k j)

/-- Step 2 of TRqIDA ((13.1.15) and the accuracy test (13.1.9)), entered at the least order `j_k`
at which (13.1.14) holds: `s_k ∈ B_{Δ_k}` (feasible) does at least as well as `d_k = d_{k,j_k}`
on the order-`j_k` inexact decrement, and the iteration is accuracy-improving iff (13.1.9)
fails for some `i ∈ [1, q]`. -/
structure TRqStep2 (X : Set E) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (Δ : ℕ → ℝ)
    (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ)
    (s : ℕ → E) (acc : ℕ → Prop) (k : ℕ) : Prop where
  /-- `j_k ∈ [1, q]`. -/
  jk_mem : jk k ∈ Finset.Icc 1 P.q
  /-- (13.1.14) holds at `j_k`. -/
  fail : trqDAFail P ε D Δ dd k (jk k)
  /-- `j_k` is the least such order. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < jk k → ¬ trqDAFail P ε D Δ dd k j
  /-- The trial point is feasible. -/
  mem : x k + s k ∈ X
  /-- `s_k ∈ B_{Δ_k}`. -/
  norm_le : ‖s k‖ ≤ Δ k
  /-- (13.1.15). -/
  dec_le : (D k).taylorDecrement (jk k) (dd k (jk k)) ≤ (D k).taylorDecrement (jk k) (s k)
  /-- Branching to Step 5 iff the accuracy test (13.1.9) fails. -/
  acc_iff : acc k ↔ ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖s k‖ ^ (P.q - i + 1) < h k i

/-- **One iteration of TRqIDA / TRqEDA** ([cartis2022evaluation], Algorithm 13.1.1, Steps 1, 2,
4, 5) on the feasible set `X`, given the ratio `ρ k` of Step 3: Step-1 displacements `d_{k,j}` with
(13.1.13) for every order; if (13.1.14) fails at every order the iteration is accuracy-improving,
otherwise Step 2 (`TRqStep2`); a trial iteration (`¬ acc k`) accepts or rejects the step and updates
the radius by (13.1.17) (capped by `Δ_max`), keeps the accuracies, and keeps the derivative
estimates when the step is rejected; an accuracy-improving iteration keeps `x_k` and `Δ_k` and
multiplies the accuracies by `γ_h` (13.1.18). -/
structure TRqDAStep (X : Set E) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → E) (Δ : ℕ → ℝ)
    (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ)
    (s : ℕ → E) (acc : ℕ → Prop) (ρ : ℕ → ℝ) (k : ℕ) : Prop where
  /-- (13.1.13): `ς`-approximate optimality displacements at every order. -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((D k).taylorDecrement j)
    (trqDARadius P Δ k) {e | x k + e ∈ X} P.ς (dd k j)
  /-- Step 1 → Step 5 when (13.1.14) fails at every order. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFail P ε D Δ dd k j) → acc k
  /-- Step 2 when (13.1.14) holds at some order. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, trqDAFail P ε D Δ dd k j) →
    TRqStep2 X P ε x Δ h D dd jk s acc k
  /-- Steps 3–4 on a trial iteration. -/
  accept : ¬ acc k → TRAcceptance P.toTRParams (ρ k) (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))
  /-- The radius cap of (13.1.17). -/
  le_Δmax : ¬ acc k → Δ (k + 1) ≤ P.Δmax
  /-- The accuracies are kept on trial iterations. -/
  h_trial : ¬ acc k → h (k + 1) = h k
  /-- No new derivative estimates at an unchanged iterate. -/
  D_unsucc : ¬ acc k → ρ k < P.η₁ → D (k + 1) = D k
  /-- Step 5 keeps the iterate. -/
  x_acc : acc k → x (k + 1) = x k
  /-- Step 5 keeps the radius. -/
  Δ_acc : acc k → Δ (k + 1) = Δ k
  /-- Step 5 (13.1.18). -/
  h_acc : acc k → ∀ i, h (k + 1) i = P.γh * h k i

namespace TRqDAStep

variable (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
include hs

/-- A trial iteration went through Step 2. -/
theorem step2_of_not_acc (hk : ¬ acc k) : TRqStep2 X P ε x Δ h D dd jk s acc k := by
  refine hs.step2 ?_
  by_contra hc
  push Not at hc
  exact hk (hs.acc_of_pass hc)

/-- The radius update of a trial iteration. -/
theorem update (hk : ¬ acc k) :
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  (hs.accept hk).update

/-- The radius either is kept or follows the update. -/
theorem delta_succ_eq_or_update : Δ (k + 1) = Δ k ∨
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) := by
  by_cases hk : acc k
  · exact Or.inl (hs.Δ_acc hk)
  · exact Or.inr (hs.update hk)

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
transfers to sequences whose iterates, radii, accuracies and estimates at `k'` and `k' + 1`, and
whose displacements, order, step, flag and ratio at `k'`, are those of iterations `k` and `k + 1`
(used to splice runs). -/
theorem congr {x' : ℕ → E} {Δ' : ℕ → ℝ} {h' : ℕ → ℕ → ℝ}
    {D' : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd' : ℕ → ℕ → E} {jk' : ℕ → ℕ} {s' : ℕ → E}
    {acc' : ℕ → Prop} {ρ' : ℕ → ℝ} {k' : ℕ} (hx : x' k' = x k) (hx1 : x' (k' + 1) = x (k + 1))
    (hΔ : Δ' k' = Δ k) (hΔ1 : Δ' (k' + 1) = Δ (k + 1)) (hh : h' k' = h k)
    (hh1 : h' (k' + 1) = h (k + 1)) (hD : D' k' = D k) (hD1 : D' (k' + 1) = D (k + 1))
    (hdd : dd' k' = dd k) (hjk : jk' k' = jk k) (hs' : s' k' = s k) (hacc : acc' k' ↔ acc k)
    (hρ : ρ' k' = ρ k) :
    TRqDAStep X P ε x' Δ' h' D' dd' jk' s' acc' ρ' k' := by
  obtain ⟨hw, hap, hst, hac, hle, hht, hdu, hxa, hΔa, hha⟩ := hs
  have hF : ∀ j, trqDAFail P ε D' Δ' dd' k' j ↔ trqDAFail P ε D Δ dd k j := fun j => by
    simp only [trqDAFail, trqDARadius, hD, hΔ, hdd]
  refine ⟨fun j hj => ?_, fun hp => hacc.2 (hap fun j hj hf => hp j hj ((hF j).2 hf)),
    fun ⟨j, hj, hf⟩ => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha hr => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · simpa only [trqDARadius, hD, hΔ, hx, hdd] using hw j hj
  · obtain ⟨hjm, hfl, hpl, hmem, hnl, hdl, hai⟩ := hst ⟨j, hj, (hF j).1 hf⟩
    refine ⟨hjk ▸ hjm, (hF _).2 (hjk ▸ hfl), fun i hi hlt hfi => hpl i hi (hjk ▸ hlt)
      ((hF i).1 hfi), by rw [hx, hs']; exact hmem, by rw [hs', hΔ]; exact hnl,
      by rw [hD, hjk, hdd, hs']; exact hdl, by rw [hacc, hs', hh]; exact hai⟩
  · rw [hρ, hx, hs', hx1, hΔ, hΔ1]; exact hac (fun h => ha (hacc.2 h))
  · rw [hΔ1]; exact hle (fun h => ha (hacc.2 h))
  · rw [hh1, hh]; exact hht (fun h => ha (hacc.2 h))
  · rw [hD1, hD]; exact hdu (fun h => ha (hacc.2 h)) (hρ ▸ hr)
  · rw [hx1, hx]; exact hxa (hacc.1 ha)
  · rw [hΔ1, hΔ]; exact hΔa (hacc.1 ha)
  · rw [hh1, hh]; exact hha (hacc.1 ha)

end TRqDAStep

/-- The iterates of TRqIDA/TRqEDA sequences starting in `X` stay in `X`. -/
theorem trqDA_mem (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i) (hx0 : x 0 ∈ X) :
    x k ∈ X := by
  induction k with
  | zero => exact hx0
  | succ k ih => exact (hstep k k.lt_succ_self).mem_succ (ih fun i hi => hstep i (by omega))

/-- The radii of TRqIDA/TRqEDA sequences stay positive. -/
theorem trqDA_delta_pos (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) : 0 < Δ k := by
  induction k with
  | zero => rw [hΔ0]; exact P.Δ₀_pos
  | succ k ih =>
    have hΔ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · rw [hk.Δ_acc ha]; exact hΔ
    · exact (hk.accept ha).pos hΔ

/-- **Invariants of TRqIDA/TRqEDA sequences**: if the step predicate holds at every iteration
`i < k`, `Δ_0 = Δ₀` and `h_0 = h₀`, then `0 < Δ_k ≤ Δ_max` and `0 < h_{k,i} ≤ κ_h` for
`i ∈ [1, q]`. -/
theorem trqDA_invariants (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) (hh0 : h 0 = P.h₀) :
    (0 < Δ k ∧ Δ k ≤ P.Δmax) ∧ ∀ i ∈ Finset.Icc 1 P.q, 0 < h k i ∧ h k i ≤ P.κh := by
  induction k with
  | zero =>
    rw [hΔ0, hh0]
    exact ⟨⟨P.Δ₀_pos, P.Δ₀_le_Δmax⟩, fun i hi => ⟨P.h₀_pos i hi, P.h₀_le i hi⟩⟩
  | succ k ih =>
    obtain ⟨⟨hΔ, hΔm⟩, hh⟩ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · refine ⟨⟨by rw [hk.Δ_acc ha]; exact hΔ, by rw [hk.Δ_acc ha]; exact hΔm⟩, fun i hi => ?_⟩
      rw [hk.h_acc ha i]
      obtain ⟨h1, h2⟩ := hh i hi
      exact ⟨mul_pos P.γh_pos h1, (mul_le_of_le_one_left h1.le P.γh_lt_one.le).trans h2⟩
    · exact ⟨⟨(hk.accept ha).pos hΔ, hk.le_Δmax ha⟩, by rw [hk.h_trial ha]; exact hh⟩

/-- The optimality radius lies in `(0, 1]`. -/
theorem trqDARadius_mem (hΔ : 0 < Δ k) : 0 < trqDARadius P Δ k ∧ trqDARadius P Δ k ≤ 1 :=
  ⟨lt_min hΔ P.ϑ_pos, (min_le_right _ _).trans P.ϑ_le_one⟩

/-! ### Counting the trial iterations -/

/-- **Counting the trial iterations** (Lemma 13.1.1 of [cartis2022evaluation]): for sequences
satisfying the TRqIDA step predicate at every iteration `i ≤ k` with `Δ_0 = Δ₀`, if
`0 < Δ_min ≤ Δ_{k+1}`, then `|𝒯_k| ≤ |𝒮_k| (1 + log γ₃/|log γ₂|) + |log (Δ_min/Δ₀)|/|log γ₂|`
(13.1.22), where `𝒯_k = {i ≤ k | ¬ acc i}` and `𝒮_k = {i ≤ k | ¬ acc i, ρ_i ≥ η₁}`. -/
theorem trqDA_card_trial_le (hstep : ∀ i ≤ k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) {Δmin : ℝ} (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  have h := card_successSet_or_le_of_upper_ratio (Δ := Δ) (k := k)
    (succ := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (fail := fun i => ¬ acc i ∧ ρ i < P.η₁)
    P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃
    (fun i _ hi hf => not_le.2 hf.2 hi.2)
    (fun i hi hs => (((hstep i hi).update hs.1).le_mul_of_le hs.2 P.γ₂_lt_one P.one_le_γ₃))
    (fun i hi hf => ((hstep i hi).update hf.1).le_mul_of_lt hf.2)
    (fun i hi hs hf => by
      have ha : acc i := by
        by_contra ha
        rcases le_or_gt P.η₁ (ρ i) with hρ | hρ
        · exact hs ⟨ha, hρ⟩
        · exact hf ⟨ha, hρ⟩
      rw [(hstep i hi).Δ_acc ha])
    hmin hΔmin
  rw [hΔ0] at h
  have hset : successSet (fun i => (¬ acc i ∧ P.η₁ ≤ ρ i) ∨ (¬ acc i ∧ ρ i < P.η₁)) k =
      successSet (fun i => ¬ acc i) k := by
    ext i
    simp only [mem_successSet]
    constructor
    · rintro ⟨hi, (h1 | h1)⟩ <;> exact ⟨hi, h1.1⟩
    · rintro ⟨hi, h1⟩
      exact ⟨hi, (le_or_gt P.η₁ (ρ i)).imp (fun h2 => ⟨h1, h2⟩) fun h2 => ⟨h1, h2⟩⟩
  rwa [hset] at h

/-! ### The decrease at a trial iteration -/

/-- **The decrease at a trial iteration** (Lemma 13.1.2 of [cartis2022evaluation]): at a trial
iteration `k ∈ 𝒯` of TRqIDA (or TRqEDA) with `Δ_k > 0`, the scaled criticality `φ̂_{f,k}` of
(13.1.25) satisfies `φ̂_{f,k} ≥ ½ ς ε_min` (hence (13.1.26), `min_{i ∈ 𝒯_k} φ̂_{f,i} ≥ ½ ς ε_min`)
and (13.1.27), `\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ φ̂_{f,k} δ_k^{j_k} / j_k!`. -/
theorem TRqDAStep.trqGap_ge (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hΔ : 0 < Δ k) :
    P.ς * epsMin P.q ε / 2 ≤ trqGap (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) ∧
      trqGap (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) * trqDARadius P Δ k ^ jk k / (jk k)! ≤
        (D k).taylorDecrement (jk k) (s k) := by
  have h2 := hs.step2_of_not_acc hk
  have hδ := (trqDARadius_mem (P := P) hΔ).1
  set δ := trqDARadius P Δ k
  set j := jk k
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  have hδj : 0 < δ ^ j := pow_pos hδ j
  have heq : trqGap (D k) j δ (dd k j) * δ ^ j / j ! = (D k).taylorDecrement j (dd k j) := by
    rw [trqGap]; field_simp
  refine ⟨?_, heq ▸ h2.dec_le⟩
  have hfail := h2.fail
  unfold trqDAFail at hfail
  rw [trqGap, le_div_iff₀ hδj]
  have hεj := epsMin_le (ε := ε) h2.jk_mem
  have : P.ς * epsMin P.q ε / 2 * δ ^ j ≤ P.ς * ε j * δ ^ j / 2 := by
    have := P.ς_pos.le
    have : P.ς * epsMin P.q ε ≤ P.ς * ε j := mul_le_mul_of_nonneg_left hεj this
    nlinarith
  calc P.ς * epsMin P.q ε / 2 * δ ^ j ≤ P.ς * ε j * δ ^ j / 2 := this
    _ = j ! * (P.ς * ε j * δ ^ j / j ! / 2) := by field_simp
    _ ≤ j ! * (D k).taylorDecrement j (dd k j) := by gcongr

/-- The predicted decrease `\overline{ΔT}_{f,j_k}(x_k, s_k)` of a trial iteration of TRqIDA (or
TRqEDA) with `Δ_k > 0` and `ε_min > 0` is positive (Lemma 13.1.2). -/
theorem TRqDAStep.taylorDecrement_pos (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
    (hk : ¬ acc k) (hΔ : 0 < Δ k) (hε : 0 < epsMin P.q ε) :
    0 < (D k).taylorDecrement (jk k) (s k) := by
  obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge hs hk hΔ
  have hδ := (trqDARadius_mem (P := P) hΔ).1
  have h0 : 0 < P.ς * epsMin P.q ε / 2 := by have := P.ς_pos; positivity
  exact lt_of_lt_of_le (div_pos (mul_pos (h0.trans_le hφ) (pow_pos hδ _)) (by positivity)) hdec

/-- The scaled criticality `φ̂_{f,i}` (13.1.25) of iteration `i`. -/
noncomputable abbrev trPhiHat (P : TRqIDAParams) (Δ : ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (i : ℕ) : ℝ :=
  trqGap (D i) (jk i) (trqDARadius P Δ i) (dd i (jk i))

/-- **The radius bound behind Lemma 13.1.4** ([cartis2022evaluation], Appendix B), for sequences
satisfying the TRqIDA step predicate at every iteration `i < k` with `Δ_0 = Δ₀`. Suppose that a
trial iteration `i` with `Δ_i ≤ min(ϑ, a φ̂_{f,i})` is very successful (Lemmas 13.1.3, 13.3.1),
and let `0 ≤ κ_Δ ≤ γ₁ a`. Then for every lower bound `c` of the `φ̂_{f,i}`, `i ∈ 𝒯_{k-1}`,
`Δ_k ≥ min(γ₁ ϑ, κ_Δ c)`. -/
theorem trqDA_delta_ge (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) {a κΔ c : ℝ} (ha : 0 ≤ a) (hκΔ0 : 0 ≤ κΔ) (hκΔ : κΔ ≤ P.γ₁ * a)
    (hsucc : ∀ i < k, ¬ acc i → Δ i ≤ min P.ϑ (a * trPhiHat P Δ D dd jk i) → P.η₂ ≤ ρ i)
    (hc : ∀ i < k, ¬ acc i → c ≤ trPhiHat P Δ D dd jk i) :
    min (P.γ₁ * P.ϑ) (κΔ * c) ≤ Δ k := by
  induction k with
  | zero =>
    rw [hΔ0]
    exact (min_le_left _ _).trans ((mul_le_of_le_one_left P.ϑ_pos.le P.γ₁_le_one).trans
      P.ϑ_le_Δ₀)
  | succ k ih =>
    have hlt : ∀ i < k, i < k + 1 := fun i hi => hi.trans k.lt_succ_self
    have IH := ih (fun i hi => hstep i (hlt i hi)) (fun i hi => hsucc i (hlt i hi))
      (fun i hi => hc i (hlt i hi))
    have hk := hstep k k.lt_succ_self
    have hΔpos := trqDA_delta_pos (fun i hi => hstep i (hlt i hi)) hΔ0
    by_cases hacc : acc k
    · rw [hk.Δ_acc hacc]; exact IH
    have hu := hk.update hacc
    by_cases hsmall : Δ k ≤ min P.ϑ (a * trPhiHat P Δ D dd jk k)
    · exact IH.trans (hu.le_of_very_successful (hsucc k k.lt_succ_self hacc hsmall))
    have hγ : P.γ₁ * Δ k ≤ Δ (k + 1) := hu.mul_le P.γ₁_le_γ₂ P.γ₁_le_one hΔpos.le
    rcases le_or_gt c 0 with hc0 | hc0
    · exact (min_le_right _ _).trans ((mul_nonpos_of_nonneg_of_nonpos hκΔ0 hc0).trans
        (hu.pos P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one hΔpos).le)
    rw [not_le, min_lt_iff] at hsmall
    refine le_trans ?_ hγ
    rcases hsmall with hϑ | hφ
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hϑ.le P.γ₁_pos.le)
    · have h1 : a * c ≤ a * trPhiHat P Δ D dd jk k :=
        mul_le_mul_of_nonneg_left (hc k k.lt_succ_self hacc) ha
      calc min (P.γ₁ * P.ϑ) (κΔ * c) ≤ κΔ * c := min_le_right _ _
        _ ≤ P.γ₁ * a * c := mul_le_mul_of_nonneg_right hκΔ hc0.le
        _ = P.γ₁ * (a * c) := by ring
        _ ≤ P.γ₁ * Δ k := mul_le_mul_of_nonneg_left (h1.trans hφ.le) P.γ₁_pos.le

/-- **The decrement bound behind Lemma 13.1.5** ([cartis2022evaluation], Appendix B), for one
trial iteration of the TRqIDA step predicate: if `0 < ε_min ≤ 1`, `0 ≤ κ_δ ≤ ½` and
`δ_k ≥ ς κ_δ ε_min` ((13.1.32)), then
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}` ((13.1.34)). -/
theorem TRqDAStep.taylorDecrement_ge (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
    (hk : ¬ acc k) (hΔ : 0 < Δ k) {κδ : ℝ} (hκδ0 : 0 ≤ κδ) (hκδ : κδ ≤ 1 / 2)
    (hεmin : 0 < epsMin P.q ε) (hεmin1 : epsMin P.q ε ≤ 1)
    (hδ : P.ς * κδ * epsMin P.q ε ≤ trqDARadius P Δ k) :
    (P.ς * κδ) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
      (D k).taylorDecrement (jk k) (s k) := by
  obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge hs hk hΔ
  have h2 := hs.step2_of_not_acc hk
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  set m := P.ς * κδ * epsMin P.q ε with hm
  set ph := trPhiHat P Δ D dd jk k
  set δ := trqDARadius P Δ k
  set j := jk k
  have hm0 : 0 ≤ m := by have := P.ς_pos.le; positivity
  have hm1 : m ≤ 1 := by
    have : P.ς * κδ ≤ 1 := by
      have := P.ς_le_one; have := P.ς_pos.le; nlinarith
    calc m = P.ς * κδ * epsMin P.q ε := rfl
      _ ≤ 1 * 1 := mul_le_mul this hεmin1 hεmin.le zero_le_one
      _ = 1 := one_mul 1
  have hmφ : m ≤ ph := by
    refine le_trans ?_ hφ
    have := P.ς_pos.le
    have : P.ς * epsMin P.q ε * κδ ≤ P.ς * epsMin P.q ε * (1 / 2) :=
      mul_le_mul_of_nonneg_left hκδ (by positivity)
    rw [hm]; linarith
  have hδj : m ^ P.q ≤ δ ^ j :=
    (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδ j)
  have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
  have hjpos : (0 : ℝ) < j ! := by positivity
  calc (P.ς * κδ) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) = m * m ^ P.q / P.q ! := by
        rw [hm, mul_pow, pow_succ']; ring
    _ ≤ ph * δ ^ j / P.q ! :=
        div_le_div_of_nonneg_right (mul_le_mul hmφ hδj (by positivity) (hm0.trans hmφ))
          (by positivity)
    _ ≤ ph * δ ^ j / j ! :=
        div_le_div_of_nonneg_left (mul_nonneg (hm0.trans hmφ) (pow_nonneg (hm0.trans hδ) _))
          hjpos hfact
    _ ≤ (D k).taylorDecrement j (s k) := hdec

/-- **The accuracy bound behind Lemma 13.1.6** ([cartis2022evaluation]), for one iteration of the
TRqIDA step predicate that goes through Step 2: if `‖∇̄^i f(x_k)‖ ≤ L̄` for `i ∈ [1, q]` with
`L̄ ≥ 1`, `ε ∈ (0, 1]^q`, `0 ≤ κ_δ ≤ 1`, `δ_k ≥ ς κ_δ ε_min` and (13.1.36)
`h_{k,i} ≤ κ_s (ς^{q+1} κ_δ^q/(4 q! L̄))^q ε_min^{q(q+1)}` for `i ∈ [1, q]`, then the accuracy test
(13.1.9) holds, i.e. the iteration is not accuracy-improving. -/
theorem TRqStep2.not_acc_of_le (h2 : TRqStep2 X P ε x Δ h D dd jk s acc k) (hΔ : 0 < Δ k)
    {Lb κδ : ℝ} (hLb : 1 ≤ Lb) (hD : ∀ i ∈ Finset.Icc 1 P.q, ‖D k i‖ ≤ Lb)
    (hκδ0 : 0 ≤ κδ) (hκδ : κδ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hδ : P.ς * κδ * epsMin P.q ε ≤ trqDARadius P Δ k)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.κs * (P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb)) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k := by
  have hq := P.one_le_q
  have hεmin : 0 < epsMin P.q ε := epsMin_pos hq fun j hj => (hε j hj).1
  have hεmin1 : epsMin P.q ε ≤ 1 := epsMin_le_one hq fun j hj => (hε j hj).2
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  set j := jk k
  set em := epsMin P.q ε
  set c := P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb) * em ^ (P.q + 1) with hc
  have hfq : (0 : ℝ) < P.q ! := by positivity
  have hLb0 : 0 < Lb := zero_lt_one.trans_le hLb
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    have h1 : P.ς ^ (P.q + 1) ≤ 1 := pow_le_one₀ hς.le hς1
    have h2 : κδ ^ P.q ≤ 1 := pow_le_one₀ hκδ0 hκδ
    have h3 : em ^ (P.q + 1) ≤ 1 := pow_le_one₀ hεmin.le hεmin1
    have h4 : (1 : ℝ) ≤ 4 * P.q ! * Lb := by
      have : (1 : ℝ) ≤ P.q ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
      nlinarith
    rw [hc, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc P.ς ^ (P.q + 1) * κδ ^ P.q * em ^ (P.q + 1) ≤ 1 * 1 * 1 := by gcongr
      _ ≤ 4 * P.q ! * Lb := by linarith
  -- the step is not too short
  have hsc : c ≤ ‖s k‖ ∨ 1 ≤ ‖s k‖ := by
    rcases le_or_gt 1 ‖s k‖ with h1 | h1
    · exact Or.inr h1
    left
    have hfail := h2.fail
    unfold trqDAFail at hfail
    have hup := taylorDecrement_le_two_mul (D := D k) (j := j) hLb0.le
      (fun i hi => hD i (Finset.Icc_subset_Icc le_rfl hjq hi)) h1.le
    have hlow := hfail.trans_le (h2.dec_le.trans hup)
    have hδ0 := (trqDARadius_mem (P := P) hΔ).1
    set δ := trqDARadius P Δ k
    have hm0 : 0 ≤ P.ς * κδ * em := by positivity
    have hm1 : P.ς * κδ * em ≤ 1 := by
      calc P.ς * κδ * em ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have hδj : (P.ς * κδ * em) ^ P.q ≤ δ ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδ j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hjpos : (0 : ℝ) < j ! := by positivity
    have hεj : em ≤ ε j := epsMin_le h2.jk_mem
    have key : P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb) ≤
        P.ς * ε j * δ ^ j / j ! / 2 / (2 * Lb) := by
      have hnum : P.ς * em * (P.ς * κδ * em) ^ P.q ≤ P.ς * ε j * δ ^ j :=
        mul_le_mul (mul_le_mul_of_nonneg_left hεj hς.le) hδj (by positivity)
          (mul_nonneg hς.le (hεmin.le.trans hεj))
      have hN : 0 ≤ P.ς * ε j * δ ^ j :=
        mul_nonneg (mul_nonneg hς.le (hεmin.le.trans hεj)) (pow_nonneg hδ0.le _)
      calc P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb)
          ≤ P.ς * ε j * δ ^ j / (4 * P.q ! * Lb) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ P.ς * ε j * δ ^ j / (4 * j ! * Lb) :=
            div_le_div_of_nonneg_left hN (by positivity) (by gcongr)
        _ = P.ς * ε j * δ ^ j / j ! / 2 / (2 * Lb) := by field_simp; ring
    have : c = P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb) := by
      rw [hc]; ring
    rw [this]
    refine key.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [h2.acc_iff]
  push Not
  intro i hi
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  have hcq : c ^ P.q ≤ ‖s k‖ ^ (P.q - i + 1) := by
    rcases hsc with hsc | hsc
    · exact (pow_le_pow_of_le_one hc0 hc1 (by omega)).trans (pow_le_pow_left₀ hc0 hsc _)
    · exact (pow_le_one₀ hc0 hc1).trans (one_le_pow₀ hsc)
  calc h k i ≤ P.κs * (P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb)) ^ P.q *
        em ^ (P.q * (P.q + 1)) := hh i hi
    _ = P.κs * c ^ P.q := by rw [hc, mul_pow, ← pow_mul, mul_comm (P.q + 1) P.q, mul_assoc]
    _ ≤ P.κs * ‖s k‖ ^ (P.q - i + 1) := mul_le_mul_of_nonneg_left hcq P.κs_pos.le

end TRStep

/-! ### TRqIDA runs -/

/-- The test of approximate optimality of TRqIDA with a feasible set at iteration `k`
([cartis2022evaluation], §14.2, (14.2.2)): `x_k` is an `(ε, δ_k)`-approximate `q`-th order
minimizer of `f` on the feasible set `X` (measures over the feasible displacements `{e | x_k +
e ∈ X}`) with the radius `δ_k = min(Δ_k, ϑ)`. The unconstrained test is the case `X = univ`. -/
def trqIDATest (f : E → ℝ) (X : Set E) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → E)
    (Δ : ℕ → ℝ) (k : ℕ) : Prop :=
  IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (fun _ => trqDARadius P Δ k)

/-- **TRqIDA with a feasible set** ([cartis2022evaluation], Algorithm 13.1.1; TRqIDA-SC of
§14.2) as a run predicate, for the objective `f`, the closed feasible set `X` (closedness is
not used by the analysis), the (unknown) oracle constants `κ_{∇,i}` (`κg i ≥ 0`), constants
`P`, tolerances `ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, a feasible starting point `x₀ ∈ X`, and
sequences of iterates `x`, radii `Δ`, requested accuracies `h`, inexact jets `D` satisfying
(13.1.2), Step-1 displacements `dd`, orders `j_k`, steps `s` and accuracy-improving flags
`acc`; every iteration satisfies `TRqDAStep` on `X` (feasible Step-1 displacements and trial
points) with the exact-value ratio (13.1.16) `ρ_k = (f(x_k) - f(x_k + s_k)) /
\overline{ΔT}_{f,j_k}(x_k, s_k)` (`Optimization.trqRatio`). Algorithm 13.1.1 is the case `X =
    univ`. -/
structure IsTRqIDARun (f : E → ℝ) (X : Set E) (κg : ℕ → ℝ) (P : TRqIDAParams)
    (ε : ℕ → ℝ) (x₀ : E) (x : ℕ → E) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E)
    (acc : ℕ → Prop) : Prop where
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ϑ ≥ ε_min`. -/
  epsMin_le_ϑ : epsMin P.q ε ≤ P.ϑ
  /-- `κ_{∇,i} ≥ 0`. -/
  κg_nonneg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i
  /-- The starting point. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible. -/
  x₀_mem : x₀ ∈ X
  /-- The initial radius. -/
  Δ_zero : Δ 0 = P.Δ₀
  /-- The initial accuracies. -/
  h_zero : h 0 = P.h₀
  /-- The error model (13.1.2). -/
  oracle : ∀ k, JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.q (fun i => κg i * h k i)
  /-- Steps 1–5. -/
  step : ∀ k, TRqDAStep X P ε x Δ h D dd jk s acc (trqRatio f D x s jk) k

namespace IsTRqIDARun

variable {f : E → ℝ} {X : Set E} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop}
  (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
include hrun

theorem delta_pos (k : ℕ) : 0 < Δ k :=
  trqDA_delta_pos (fun i _ => hrun.step i) hrun.Δ_zero

theorem accuracy_mem (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) : 0 < h k i ∧ h k i ≤ P.κh :=
  (trqDA_invariants (k := k) (fun i _ => hrun.step i) hrun.Δ_zero hrun.h_zero).2 i hi

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaMax_nonneg : 0 ≤ ordMax P.q κg := ordMax_nonneg hrun.κg_nonneg

/-- The iterates are feasible. -/
theorem mem (k : ℕ) : x k ∈ X :=
  trqDA_mem (fun i _ => hrun.step i) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along a TRqIDA run with a feasible set: `f(x_k) ≤ f(x₀)` (the
ratio uses exact function values and the predicted decrease of a trial iteration is positive). -/
theorem objective_le (k : ℕ) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i _ => ?_
  by_cases ha : acc i
  · simp only [(hrun.step i).x_acc ha, le_rfl]
  · exact ((hrun.step i).accept ha).le (f := f) trqRatio_eq
      ((hrun.step i).taylorDecrement_pos ha (hrun.delta_pos i) hrun.epsMin_pos)

/-- The iterates lie in every set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) : x k ∈ A :=
  hAX _ (hrun.mem k) (hrun.objective_le k)

/-- (13.1.24): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` under the smoothness hypothesis
anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) :
    ‖D k i‖ ≤ lipMax L P.q + ordMax P.q κg * P.κh :=
  hf.norm_le_of_jetApprox hL (hrun.mem_anchor hAX k) (hrun.oracle k) hrun.κg_nonneg
    (fun _ hi => (hrun.accuracy_mem k hi).1.le) (fun _ hi => (hrun.accuracy_mem k hi).2) hi

end IsTRqIDARun

section TRqIDA

variable {X C A : Set E} {f : E → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-! ### Very successful iterations -/

/-- **Very successful iterations** (Lemma 13.1.3 of [cartis2022evaluation]): under the smoothness
hypothesis, at a trial iteration `k ∈ 𝒯` of TRqIDA with (13.1.28)
`Δ_k ≤ min(ϑ, (1 - η₂)/(L_f + 4 (q+1)! κ_s κ_{∇,max}) pĥ_{f,k})`, the iteration is very successful
(`ρ_k ≥ η₂`) and `Δ_{k+1} ≥ Δ_k`. -/
theorem IsTRqIDARun.ratio_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hΔpos := hrun.delta_pos k
  obtain ⟨hφ, hdec⟩ := TRqDAStep.trqGap_ge hs hk hΔpos
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hδeq : trqDARadius P Δ k = Δ k := min_eq_left (hΔ.trans (min_le_left _ _))
  set j := jk k
  set δ := trqDARadius P Δ k
  set ph := trPhiHat P Δ D dd jk k
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  set C := Lf + 4 * (P.q + 1)! * P.κs * κm
  have hLf : 1 ≤ Lf := one_le_lipMax hL
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  have hκs := P.κs_pos
  have hC : 0 < C := by positivity
  have hδ0 : 0 < δ := (trqDARadius_mem (P := P) hΔpos).1
  have hδ1 : δ ≤ 1 := (trqDARadius_mem (P := P) hΔpos).2
  have hφ0 : 0 < ph := lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) hφ
  have hfj : (0 : ℝ) < j ! := by positivity
  set ΔTb := (D k).taylorDecrement j (s k)
  have hΔTb : ph * δ ^ j / j ! ≤ ΔTb := hdec
  have hΔTb0 : 0 < ΔTb := lt_of_lt_of_le (by positivity) hΔTb
  have hsδ : ‖s k‖ ≤ δ := hδeq ▸ h2.norm_le
  -- the step accuracy (13.1.9) holds on a trial iteration
  have hacc : ∀ i ∈ Finset.Icc 1 P.q, κg i * h k i ≤ κm * P.κs * ‖s k‖ ^ (P.q - i + 1) := by
    intro i hi
    have hhi : h k i ≤ P.κs * ‖s k‖ ^ (P.q - i + 1) := by
      by_contra hc
      exact hk (h2.acc_iff.2 ⟨i, hi, not_le.1 hc⟩)
    rw [mul_assoc]
    exact mul_le_mul (le_ordMax hi) hhi (hrun.accuracy_mem k hi).1.le hκm
  have hE := abs_taylorDecrement_sub_le_of_stepAccuracy hκm hκs.le (hrun.oracle k) hacc hjq
  have hR := hf.abs_sub_taylorDecrement_le_of_le hjq (hrun.mem_anchor hAX k) (hXC h2.mem)
  have hLj : L j ≤ Lf := le_lipMax hjq
  -- bounds by `δ^{j+1}`
  have hs0 := norm_nonneg (s k)
  have hpow1 : ‖s k‖ ^ (j + 1) ≤ δ ^ (j + 1) := pow_le_pow_left₀ hs0 hsδ _
  have hpow2 : ‖s k‖ ^ (P.q + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_of_le_one hs0 (hsδ.trans hδ1) (by omega)).trans hpow1
  have hfact1 : ((j + 1)! : ℝ) ≥ j ! := by exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hfact2 : (2 : ℝ) * j ! ≤ 4 * (P.q + 1)! := by
    have : (j ! : ℝ) ≤ (P.q + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
    linarith
  have hδC : δ * C ≤ (1 - P.η₂) * ph := by
    have := hΔ.trans (min_le_right _ _)
    rw [← hδeq] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hC] at this
    linarith
  have herr : |f (x k) - f (x k)| + |f (x k + s k) - (f (x k) -
      (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
      |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb| +
      |f (x k + s k) - f (x k + s k)| ≤ (1 - P.η₂) * ΔTb := by
    rw [sub_self, sub_self, abs_zero, zero_add, add_zero]
    have hRb : L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) ≤ Lf / j ! * δ ^ (j + 1) := by
      gcongr
    have hEb : 2 * P.κs * κm * ‖s k‖ ^ (P.q + 1) ≤
        4 * (P.q + 1)! * P.κs * κm / j ! * δ ^ (j + 1) := by
      have : 2 * P.κs * κm ≤ 4 * (P.q + 1)! * P.κs * κm / j ! := by
        rw [le_div_iff₀ hfj]
        have := mul_le_mul_of_nonneg_right hfact2 (mul_nonneg hκs.le hκm)
        linarith
      exact mul_le_mul this hpow2 (by positivity) (by positivity)
    calc |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
          |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb|
        ≤ L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) + 2 * P.κs * κm * ‖s k‖ ^ (P.q + 1) :=
          add_le_add hR (by rw [abs_sub_comm]; exact hE)
      _ ≤ Lf / j ! * δ ^ (j + 1) + 4 * (P.q + 1)! * P.κs * κm / j ! * δ ^ (j + 1) :=
          add_le_add hRb hEb
      _ = δ ^ j / j ! * (δ * C) := by rw [pow_succ]; ring
      _ ≤ δ ^ j / j ! * ((1 - P.η₂) * ph) := by gcongr
      _ = (1 - P.η₂) * (ph * δ ^ j / j !) := by ring
      _ ≤ (1 - P.η₂) * ΔTb := mul_le_mul_of_nonneg_left hΔTb P.one_sub_η₂_pos.le
  have hρ : P.η₂ ≤ trqRatio f D x s jk k := by
    rw [trqRatio_eq, reductionRatio_def]
    exact le_div_of_inexact_error_le hΔTb0 herr
  exact ⟨hρ, (hs.update hk).le_of_very_successful hρ⟩

/-! ### The radius stays bounded below -/

/-- **The radius stays bounded below** (Lemma 13.1.4 of [cartis2022evaluation]): under the
smoothness hypothesis, along a TRqIDA run, for every `κ_Δ ∈ (0, 1]` with
`κ_Δ ≤ γ₁ (1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max})` (e.g. the value (13.1.31), `trKappaDelta`) and
every `k`: (13.1.30) `Δ_k ≥ min(γ₁ ϑ, κ_Δ min_{i ∈ 𝒯_k} φ̂_{f,i})` if `𝒯_k ≠ ∅` and `Δ_k ≥ γ₁ ϑ`
otherwise, and (13.1.32) `δ_k ≥ ς κ_δ ε_min` with `κ_δ = κ_Δ/2` (13.1.33). -/
theorem IsTRqIDARun.delta_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ} (hκΔ0 : 0 < κΔ)
    (hκΔ1 : κΔ ≤ 1)
    (hκΔ : κΔ ≤ P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
    (k : ℕ) :
    (∀ hne : (successSet (fun i => ¬ acc i) k).Nonempty, min (P.γ₁ * P.ϑ)
        (κΔ * (successSet (fun i => ¬ acc i) k).inf' hne (trPhiHat P Δ D dd jk)) ≤ Δ k) ∧
      (successSet (fun i => ¬ acc i) k = ∅ → P.γ₁ * P.ϑ ≤ Δ k) ∧
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trqDARadius P Δ k := by
  set a := (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) with ha_def
  have hLf := one_le_lipMax hL
  have hκm := hrun.kappaMax_nonneg
  have hC : 1 ≤ lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg := by
    have := P.κs_pos; nlinarith [show (0 : ℝ) ≤ 4 * (P.q + 1)! * P.κs * ordMax P.q κg by
      positivity]
  have ha0 : 0 ≤ a := div_nonneg P.one_sub_η₂_pos.le (zero_le_one.trans hC)
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (zero_lt_one.trans_le hC)]
    linarith [P.η₂_pos]
  have hsucc : ∀ i < k, ¬ acc i → Δ i ≤ min P.ϑ (a * trPhiHat P Δ D dd jk i) →
      P.η₂ ≤ trqRatio f D x s jk i :=
    fun i _ hi hΔ => (IsTRqIDARun.ratio_ge hf hL hXC hAX hrun hi hΔ).1
  have core := fun c (hc : ∀ i < k, ¬ acc i → c ≤ trPhiHat P Δ D dd jk i) =>
    trqDA_delta_ge (fun i _ => hrun.step i) hrun.Δ_zero ha0 hκΔ0.le hκΔ hsucc hc
  refine ⟨fun hne => core _ fun i hi hai => Finset.inf'_le _
      (mem_successSet.2 ⟨hi.le, hai⟩), fun hempty => ?_, ?_⟩
  · have := core (P.γ₁ * P.ϑ / κΔ) fun i hi hai => by
      have : i ∈ successSet (fun i => ¬ acc i) k := mem_successSet.2 ⟨hi.le, hai⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty i)
    rwa [mul_div_cancel₀ _ hκΔ0.ne', min_self] at this
  · have hεmin := hrun.epsMin_pos
    have hc := core (P.ς * epsMin P.q ε / 2) fun i _ hai =>
      (TRqDAStep.trqGap_ge (hrun.step i) hai (hrun.delta_pos i)).1
    have hκγ : κΔ ≤ P.γ₁ := hκΔ.trans (mul_le_of_le_one_right P.γ₁_pos.le ha1)
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

/-- The admissible values of `κ_Δ` in Lemmas 13.1.4–13.1.7 and Theorem 13.1.8:
`0 < κ_Δ ≤ 1` and `κ_Δ ≤ γ₁ (1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max})`. -/
def IsTRKappaDelta (P : TRqIDAParams) (Lf κm κΔ : ℝ) : Prop :=
  0 < κΔ ∧ κΔ ≤ 1 ∧ κΔ ≤ P.γ₁ * ((1 - P.η₂) / (Lf + 4 * (P.q + 1)! * P.κs * κm))

/-! ### Sufficient decrease -/

/-- **Sufficient decrease** (Lemma 13.1.5 of [cartis2022evaluation]): under the smoothness
hypothesis, for an admissible `κ_Δ` and `κ_δ = κ_Δ/2`, every trial iteration `k ∈ 𝒯` of a TRqIDA run
satisfies (13.1.34) `\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and if
moreover `k ∈ 𝒮` then (13.1.35) `f(x_k) - f(x_{k+1}) ≥ η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. (No
optimality hypothesis is needed.) -/
theorem IsTRqIDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) (hk : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ⟩ := hκΔ
  have h1 := (hrun.step k).taylorDecrement_ge hk (hrun.delta_pos k) (by positivity)
    (by linarith) hrun.epsMin_pos hrun.epsMin_le_one
    (IsTRqIDARun.delta_ge hf hL hXC hAX hrun hκΔ0 hκΔ1 hκΔ k).2.2
  refine ⟨h1, fun hρ => ?_⟩
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) :=
    lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) h1
  have h2 := ((hrun.step k).accept hk).sub_ge (f := f) trqRatio_eq hpos hρ
  have hη := P.η₁_pos
  have : 0 ≤ (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) := by
    have := P.ς_pos; have := hrun.epsMin_pos; positivity
  calc P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1)
      = P.η₁ * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) / 2 := by
        field_simp
    _ ≤ P.η₁ * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) := by
        have := mul_nonneg hη.le this; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement (jk k) (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

/-! ### Accuracy and certification -/

/-- **Accurate derivatives give trial iterations** (Lemma 13.1.6 of [cartis2022evaluation]): under
the smoothness hypothesis, with `L̄_f = L_f + κ_{∇,max} κ_h` ((13.1.24)) and an admissible `κ_Δ`,
`κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to Step 2 at iteration `k` and (13.1.36)
`h_{k,i} ≤ κ_s (ς^{q+1} κ_δ^q/(4 q! L̄_f))^q ε_min^{q(q+1)}` for all `i ∈ [1, q]`, then Step 2 does
not branch to Step 5 (`k ∈ 𝒯`). -/
theorem IsTRqIDARun.not_acc_of_le (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hLb : 1 ≤ lipMax L P.q + ordMax P.q κg * P.κh := by
    have := one_le_lipMax hL; have := hrun.kappaMax_nonneg; have := P.kappaH_pos; nlinarith
  exact ((hrun.step k).step2 hb).not_acc_of_le (hrun.delta_pos k) hLb
    (fun i hi => hrun.norm_D_le hf hL hAX k hi) (by positivity) (by linarith) hrun.eps_mem
    (IsTRqIDARun.delta_ge hf hL hXC hAX hrun hκΔ0 hκΔ1 hκΔ' k).2.2 hh

/-- **Certification by the Step-1 test** (Lemma 13.1.7 of [cartis2022evaluation]): under the
smoothness hypothesis and for an admissible `κ_Δ`, `κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to
Step 5 at iteration `k` ((13.1.14) fails at every order) and (13.1.37)
`κ_{∇,max} h_{k,i} ≤ ς^{q+1} κ_δ^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, q]` (written without division,
so that `κ_{∇,max} = 0` is allowed), then `φ^{δ_k}_{f,j}(x_k) ≤ ε_j δ_k^j/j!` for all `j ∈ [1, q]`.
-/
theorem IsTRqIDARun.trqIDATest_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trqIDATest f X P ε x Δ k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hδm := (IsTRqIDARun.delta_ge hf hL hXC hAX hrun hκΔ0 hκΔ1 hκΔ' k).2.2
  have hδ := trqDARadius_mem (P := P) (hrun.delta_pos k)
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  intro j hj
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set δ := trqDARadius P Δ k
  set em := epsMin P.q ε
  set m := P.ς * (κΔ / 2) * em
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := by
    have : P.ς * (κΔ / 2) ≤ 1 := by nlinarith
    calc m ≤ 1 * 1 := mul_le_mul this hεmin1 hεmin.le zero_le_one
      _ = 1 := one_mul 1
  have hw := ((hrun.step k).witness j hj).2
  refine taylorMeasure_le_of_inexact_certificate_uniform (hrun.oracle k) hj
    (by simpa using hrun.mem k) hδ.1.le
    hδ.2 hς hw (not_lt.1 (hpass j hj))
    (e := P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1))
    (fun i hi => ?_) ?_
  · have hiq : i ∈ Finset.Icc 1 P.q := Finset.Icc_subset_Icc le_rfl hjq hi
    exact (mul_le_mul_of_nonneg_right (le_ordMax hiq) (hrun.accuracy_mem k hiq).1.le).trans
      (hh i hiq)
  · have hδj : m ^ P.q ≤ δ ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδm j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * em ≤ ε j := (mul_le_of_le_one_left hεmin.le hς1).trans (epsMin_le hj)
    calc P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) =
          P.ς * em * m ^ P.q / (4 * P.q !) := by simp only [m]; ring
      _ ≤ ε j * δ ^ j / (4 * P.q !) :=
          div_le_div_of_nonneg_right (mul_le_mul hεj hδj (pow_nonneg hm0 _)
            (hrun.eps_mem j hj).1.le) (by positivity)
      _ ≤ ε j * δ ^ j / (4 * j !) := by
          gcongr
          exact mul_nonneg ((by positivity : (0 : ℝ) ≤ P.ς * em).trans hεj)
            (pow_nonneg hδ.1.le _)

/-! ### Complexity -/

/-- The constant `κ^S_{TRqIDA} = 2 q!/(η₁ (ς κ_δ)^{q+1})` (13.1.40), with `κ_δ = κ_Δ/2`. -/
noncomputable def trKappaS (P : TRqIDAParams) (κΔ : ℝ) : ℝ :=
  2 * P.q ! / (P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1))

/-- The constant `κ_acc` of the proof of Theorem 13.1.8 ([cartis2022evaluation]):
`min(ς^{q+1} κ_δ^q/(4 q! κ_{∇,max}), κ_s (ς^{q+1} κ_δ^q/(4 q! L̄_f))^q)`, the first term being
omitted when `κ_{∇,max} = 0` (exact derivatives). -/
noncomputable def trKappaAcc (P : TRqIDAParams) (κΔ Lb κm : ℝ) : ℝ :=
  if κm = 0 then P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q
  else min (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm))
    (P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q)

theorem trKappaAcc_pos {P : TRqIDAParams} {κΔ Lb κm : ℝ} (hκΔ : 0 < κΔ) (hLb : 0 < Lb)
    (hκm : 0 ≤ κm) : 0 < trKappaAcc P κΔ Lb κm := by
  have := P.ς_pos; have := P.κs_pos
  unfold trKappaAcc
  split_ifs with h0
  · positivity
  · exact lt_min (by have := lt_of_le_of_ne hκm (Ne.symm h0); positivity) (by positivity)

theorem trKappaAcc_le {P : TRqIDAParams} {κΔ Lb κm : ℝ} :
    trKappaAcc P κΔ Lb κm ≤
      P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q := by
  unfold trKappaAcc
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem mul_trKappaAcc_le {P : TRqIDAParams} {κΔ Lb κm : ℝ} (hκΔ : 0 < κΔ) (hκm : 0 ≤ κm) :
    κm * trKappaAcc P κΔ Lb κm ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) := by
  have := P.ς_pos
  unfold trKappaAcc
  split_ifs with h0
  · rw [h0, zero_mul]; positivity
  · have hκm' : 0 < κm := lt_of_le_of_ne hκm (Ne.symm h0)
    calc κm * min (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm)) _
        ≤ κm * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hκm
      _ = P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) := by field_simp

/-- **The accuracy-improving iterations of TRqIDA with a feasible set** (proof of Theorem 13.1.8,
[cartis2022evaluation]): under `LipschitzDerivsAnchored f C A 0 q L` (`L_j ≥ 1`, `A ⊇ {y ∈ X |
f(y) ≤ f(x₀)}`) and for an admissible `κ_Δ`, if no iterate `x_j`, `j ≤ k`, is approximately
optimal on `X`, then `|𝒜_k| ≤ q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem IsTRqIDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ trqIDATest f X P ε x Δ j) :
    ((successSet acc k).card : ℝ) ≤
      P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
          P.κh)| / |Real.log P.γh| + 1 := by
  have hκΔ'' := hκΔ
  have hκΔ0 := hκΔ.1
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := Lf + κm * P.κh
  have hLb : 0 < Lb := by have := one_le_lipMax hL; have := P.kappaH_pos; nlinarith
  set κacc := trKappaAcc P κΔ Lb κm
  have hκacc : 0 < κacc := trKappaAcc_pos hκΔ0 hLb hκm
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.q * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith)
  have h := card_accuracyImproving_le_of_pow (acc := acc) (hmax := fun j => ordMax P.q (h j))
    (N := P.q * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.kappaH_pos hκacc hεmin
    ((ordMax_le_iff hq).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j _ ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from funext ((hrun.step j).h_acc ha),
        ordMax_mul hq P.γh_pos.le])
    (fun j _ ha => by rw [(hrun.step j).h_trial ha])
    (fun j hj ha => by
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.q, h j i ≤ κacc * em ^ (P.q * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, trqDAFail P ε D Δ dd j i
      · refine IsTRqIDARun.not_acc_of_le hf hL hXC hAX hrun hκΔ'' hfail
          (fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right trKappaAcc_le (by positivity)
      · push Not at hfail
        refine hk j hj
            (IsTRqIDARun.trqIDATest_of_pass hf hL hXC hAX hrun hκΔ'' hfail fun i hi => ?_)
        calc κm * h j i ≤ κm * (κacc * em ^ (P.q * (P.q + 1))) :=
              mul_le_mul_of_nonneg_left (hhi i hi) hκm
          _ = κm * κacc * em ^ (P.q * (P.q + 1)) := by ring
          _ ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_trKappaAcc_le hκΔ0 hκm) hpowq (by positivity) (by positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.q * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **Evaluation complexity of TRqIDA** (Theorem 13.1.8 of [cartis2022evaluation]): complexity of
TRqIDA. Let the smoothness hypothesis and f.Bb (`f ≥ f_low`) hold, `ε ∈ (0, 1]^q`, and `κ_Δ` be
admissible (e.g. (13.1.31)), `κ_δ = κ_Δ/2`. For every TRqIDA run there is a first iteration `k_ε` at
which `x_ε = x_{k_ε}` is an `(ε, δ_ε)`-approximate `q`-th order minimizer with
`δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, and before it at most (13.1.38)
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` function evaluations and (13.1.39)
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^E |log ε_min| + κ^F + 2` derivative estimates are made, with
`κ^S = 2 q!/(η₁ (ς κ_δ)^{q+1})`, `κ^A = κ^S (1 + log γ₃/|log γ₂|)`, `κ^B = 1/|log γ₂|`,
`κ^C = |log(ς κ_δ/Δ₀)|/|log γ₂| + 1`, `κ^E = q(q+1)/|log γ_h|`, `κ^F = |log(κ_acc/κ_h)|/|log γ_h|`
(`κ_acc = trKappaAcc`). The derivative count includes the initial estimate and the last
accuracy-improving iteration. -/
theorem IsTRqIDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trqIDATest f X P ε x Δ) kε ∧ 0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  have hκΔ'' := hκΔ
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hη := P.η₁_pos
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := Lf + κm * P.κh
  have hLb : 0 < Lb := by have := one_le_lipMax hL; have := P.kappaH_pos; nlinarith
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  -- successful iterations
  set c := P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * em ^ (P.q + 1) with hc_def
  have hc : 0 < c := by positivity
  set NS := trKappaS P κΔ * (f x₀ - flow) / em ^ (P.q + 1) with hNS_def
  have hNS : NS = (f x₀ - flow) / c := by
    rw [hNS_def, hc_def, trKappaS, eq_div_iff (by positivity)]
    field_simp
  have hNS0 : 0 ≤ NS := by rw [hNS]; positivity
  have hSk : ∀ k, ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card : ℝ)
      ≤ NS := by
    intro k
    rw [hNS, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j _ hj => by rw [(hrun.step j).iterate_succ_eq hj])
      (fun j _ hj => (IsTRqIDARun.decrease_ge hf hL hXC hAX hrun hκΔ'' hj.1).2 hj.2)
          (hb _ (hrun.mem _))
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
  have hTk : ∀ k, ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k
    have hΔmin : P.ς * (κΔ / 2) * em ≤ Δ (k + 1) :=
      (IsTRqIDARun.delta_ge hf hL hXC hAX hrun hκΔ0 hκΔ1 hκΔ' (k + 1)).2.2.trans (min_le_left _ _)
    have h1 := trqDA_card_trial_le (fun i _ => hrun.step i) hrun.Δ_zero (by positivity) hΔmin
    have hlog : |Real.log (P.ς * (κΔ / 2) * em / P.Δ₀)| ≤
        |Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| := by
      have hpos : 0 < P.ς * (κΔ / 2) / P.Δ₀ := by have := P.Δ₀_pos; positivity
      rw [show P.ς * (κΔ / 2) * em / P.Δ₀ = em * (P.ς * (κΔ / 2) / P.Δ₀) by ring,
        Real.log_mul hεmin.ne' hpos.ne']
      exact abs_add_le _ _
    have h2 := mul_le_mul_of_nonneg_right (hSk k) (zero_le_one.trans hA'1)
    calc ((successSet (fun i => ¬ acc i) k).card : ℝ)
        ≤ _ := h1
      _ ≤ NS * A' + (|Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)|) /
            |Real.log P.γ₂| := add_le_add h2 (div_le_div_of_nonneg_right hlog hlog2.le)
      _ = NT := by rw [hNT_def, hNS_def]; ring
  -- accuracy-improving iterations
  set κacc := trKappaAcc P κΔ Lb κm
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hAk : ∀ k, (∀ j ≤ k, ¬ trqIDATest f X P ε x Δ j) →
      ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsTRqIDARun.card_acc_le hf hL hXC hAX hrun hκΔ'' hk
  -- conclusion
  obtain ⟨kε, hkε, -, hT, hA⟩ :=
    exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 (fun k _ => hTk k) hAk
  have hS := derivEvalCount_le_of_isFirstHit hNS0 hkε (fun k _ => hSk k)
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε :
      ℝ) + 1 ≤ derivEvalCount acc kε +
        derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hNSA : NS ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) := by
    have : trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) = A' * NS := by
      rw [hNS_def]; ring
    rw [this]
    exact le_mul_of_one_le_left hNS0 hA'1
  refine ⟨kε, hkε, (trqDARadius_mem (hrun.delta_pos kε)).1, (trqDARadius_mem (hrun.delta_pos kε)).2,
    ?_, ?_⟩
  · calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ NT + 1 := hT
      _ = _ := by rw [hNT_def]; ring
  · calc _ ≤ (NA + 1) + (NS + 1) - 1 := by linarith
      _ ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) + NA + 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

end TRqIDA

/-! ### Existence of TRqIDA runs -/

section TRExistence

variable [FiniteDimensional ℝ E]

/-- The data of one TRqIDA iteration: iterate, radius, accuracies, Step-1 displacements, order,
step and accuracy-improving flag. -/
private structure TRState (E : Type*) where
  x : E
  Δ : ℝ
  h : ℕ → ℝ
  dd : ℕ → E
  jk : ℕ
  s : E
  acc : Prop

variable (f : E → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ)
  (O : E → (ℕ → ℝ) → FormalMultilinearSeries ℝ E ℝ)

/-- The Step-1.2 test of a state. -/
private def trqDAFailS (a : TRState E) (j : ℕ) : Prop :=
  P.ς * ε j * min a.Δ P.ϑ ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j (a.dd j)

/-- Steps 1–2 of a state, and the radius invariant. -/
private def TRLocal (a : TRState E) : Prop :=
  (0 < a.Δ ∧ a.Δ ≤ P.Δmax) ∧
  (∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((O a.x a.h).taylorDecrement j) (min a.Δ P.ϑ)
    univ P.ς (a.dd j)) ∧
  ((∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFailS P ε O a j) → a.acc) ∧
  ((∃ j ∈ Finset.Icc 1 P.q, trqDAFailS P ε O a j) →
    a.jk ∈ Finset.Icc 1 P.q ∧ trqDAFailS P ε O a a.jk ∧
    (∀ j ∈ Finset.Icc 1 P.q, j < a.jk → ¬ trqDAFailS P ε O a j) ∧ ‖a.s‖ ≤ a.Δ ∧
    (O a.x a.h).taylorDecrement a.jk (a.dd a.jk) ≤ (O a.x a.h).taylorDecrement a.jk a.s ∧
    (a.acc ↔ ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖a.s‖ ^ (P.q - i + 1) < a.h i))

/-- Steps 1–2 can be performed at every iterate with a positive radius. -/
private theorem exists_trLocal (x : E) {Δ : ℝ} (hΔ : 0 < Δ) (hΔm : Δ ≤ P.Δmax) (h : ℕ → ℝ) :
    ∃ dd jk s, ∃ acc : Prop, TRLocal P ε O ⟨x, Δ, h, dd, jk, s, acc⟩ := by
  classical
  have hδ : 0 ≤ min Δ P.ϑ := le_min hΔ.le P.ϑ_pos.le
  choose dd hdd using fun j => exists_isApproxMeasureStep_taylorDecrement (O x h) j
    isClosed_univ (mem_univ 0) hδ P.ς_le_one
  by_cases hex : ∃ j, j ∈ Finset.Icc 1 P.q ∧
      P.ς * ε j * min Δ P.ϑ ^ j / j ! / 2 < (O x h).taylorDecrement j (dd j)
  · set jk := Nat.find hex
    obtain ⟨hjk, hfjk⟩ := Nat.find_spec hex
    refine ⟨dd, jk, dd jk, ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖dd jk‖ ^ (P.q - i + 1) < h i,
      ⟨hΔ, hΔm⟩, fun j _ => hdd j, fun hpass => absurd hfjk (hpass jk hjk), fun _ =>
      ⟨hjk, hfjk, fun j hj hlt hf => Nat.find_min hex hlt ⟨hj, hf⟩,
        (hdd jk).norm_le.trans (min_le_left _ _), le_rfl, Iff.rfl⟩⟩
  · push Not at hex
    exact ⟨dd, 1, 0, True, ⟨hΔ, hΔm⟩, fun j _ => hdd j, fun _ => trivial,
      fun ⟨j, hj, hf⟩ => absurd (hex j hj) (not_le.2 hf)⟩

/-- The transition of a TRqIDA run from a state satisfying Steps 1–2. -/
private theorem exists_trNext (a : TRState E) (ha : TRLocal P ε O a) :
    ∃ b : TRState E, TRLocal P ε O b ∧ ∀ (r : ℕ → TRState E) (k : ℕ), r k = a → r (k + 1) = b →
      TRqDAStep univ P ε (fun i => (r i).x) (fun i => (r i).Δ) (fun i => (r i).h)
        (fun i => O (r i).x (r i).h) (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s)
        (fun i => (r i).acc)
        (trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
          (fun i => (r i).jk)) k := by
  classical
  obtain ⟨⟨hΔ, hΔm⟩, hw, hpass, hst⟩ := ha
  set ρ := reductionRatio f a.x a.s ((O a.x a.h).taylorDecrement a.jk a.s) with hρ
  set x' := if a.acc then a.x else if P.η₁ ≤ ρ then a.x + a.s else a.x
  set Δ' := if a.acc then a.Δ else if P.η₁ ≤ ρ then a.Δ else P.γ₂ * a.Δ
  set h' : ℕ → ℝ := if a.acc then fun i => P.γh * a.h i else a.h
  have hΔ' : 0 < Δ' ∧ Δ' ≤ P.Δmax := by
    simp only [Δ']
    split_ifs
    · exact ⟨hΔ, hΔm⟩
    · exact ⟨hΔ, hΔm⟩
    · exact ⟨mul_pos P.γ₂_pos hΔ, (mul_le_of_le_one_left hΔ.le P.γ₂_lt_one.le).trans hΔm⟩
  obtain ⟨dd', jk', s', acc', hloc⟩ := exists_trLocal P ε O x' hΔ'.1 hΔ'.2 h'
  refine ⟨⟨x', Δ', h', dd', jk', s', acc'⟩, hloc, fun r k hra hrb => ?_⟩
  have hfail : ∀ j, trqDAFail P ε (fun i => O (r i).x (r i).h) (fun i => (r i).Δ)
      (fun i => (r i).dd) k j ↔ trqDAFailS P ε O a j := by
    intro j; simp only [trqDAFail, trqDARadius, trqDAFailS, hra]
  have hratio : trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
      (fun i => (r i).jk) k = ρ := by simp only [trqRatio, hra, hρ]
  refine ⟨fun j hj => ?_, fun hp => ?_, fun he => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_,
    fun hk hlt => ?_, fun hk => ?_, fun hk => ?_, fun hk i => ?_⟩
  · simp only [trqDARadius, hra, Set.setOf_add_mem_univ]; exact hw j hj
  · simp only [hra]; exact hpass fun j hj => (hfail j).not.1 (hp j hj)
  · obtain ⟨j, hj, hf⟩ := he
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst ⟨j, hj, (hfail j).1 hf⟩
    refine ⟨by simp only [hra]; exact h1, by simp only [hra] at hfail ⊢; exact (hfail _).2 h2,
      fun j hj hlt => ?_, by simp, by simp only [hra]; exact h4, by simp only [hra]; exact h5,
      by simp only [hra]; exact h6⟩
    simp only [hra] at hlt
    exact (hfail j).not.2 (h3 j hj hlt)
  · simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, x', Δ', hk, ite_false]
    refine ⟨rfl, ?_⟩
    have hu := TRUpdate.mk (η₁ := P.η₁) (η₂ := P.η₂) (γ₁ := P.γ₁) (γ₂ := P.γ₂) (γ₃ := P.γ₃)
      (ρ := ρ) (Δ := a.Δ) (Δ' := if P.η₁ ≤ ρ then a.Δ else P.γ₂ * a.Δ)
      (fun h2 => by
        rw [ite_eq_left (P.η₁_le_η₂.trans h2)]
        exact ⟨le_rfl, le_mul_of_one_le_left hΔ.le P.one_le_γ₃⟩)
      (fun h1 _ => by
        rw [ite_eq_left h1]
        exact ⟨mul_le_of_le_one_left hΔ.le P.γ₂_lt_one.le, le_rfl⟩)
      (fun h1 => by
        rw [ite_eq_right (not_le.2 h1)]
        exact ⟨mul_le_mul_of_nonneg_right P.γ₁_le_γ₂ hΔ.le, le_rfl⟩)
    exact hu
  · simp only [hrb]; exact hΔ'.2
  · simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_false]
  · simp only [hra] at hk; rw [hratio] at hlt
    simp only [hra, hrb, x', h', hk, ite_false, ite_eq_right (not_le.2 hlt)]
  · simp only [hra] at hk; simp only [hra, hrb, x', hk, ite_true]
  · simp only [hra] at hk; simp only [hra, hrb, Δ', hk, ite_true]
  · simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_true]

/-- **Existence of TRqIDA iterations** ([cartis2022evaluation], Algorithm 13.1.1): for every
objective `f`, constants `P`, tolerances `ε`, starting point `x₀` and deterministic derivative
oracle `O` (inexact jet `O y h` at `y` for accuracies `h`), there are sequences following the
iteration of TRqIDA at every step, with the exact-value ratio (13.1.16) and the derivatives
`D_k = O(x_k, h_k)`. -/
theorem exists_trqDA_run (x₀ : E) :
    ∃ (x : ℕ → E) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ)
      (s : ℕ → E) (acc : ℕ → Prop), x 0 = x₀ ∧ Δ 0 = P.Δ₀ ∧ h 0 = P.h₀ ∧
      ∀ k, TRqDAStep univ P ε x Δ h (fun i => O (x i) (h i)) dd jk s acc
        (trqRatio f (fun i => O (x i) (h i)) x s jk) k := by
  obtain ⟨dd₀, jk₀, s₀, acc₀, h₀⟩ :=
    exists_trLocal P ε O x₀ P.Δ₀_pos P.Δ₀_le_Δmax P.h₀
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant (α := TRState E)
    (init := fun a => a = ⟨x₀, P.Δ₀, P.h₀, dd₀, jk₀, s₀, acc₀⟩)
    (inv := fun _ a => TRLocal P ε O a) (stop := fun _ _ => False)
    (step := fun k a b => ∀ (r : ℕ → TRState E), r k = a → r (k + 1) = b →
      TRqDAStep univ P ε (fun i => (r i).x) (fun i => (r i).Δ) (fun i => (r i).h)
        (fun i => O (r i).x (r i).h) (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s)
        (fun i => (r i).acc)
        (trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
          (fun i => (r i).jk)) k)
    ⟨_, rfl⟩ (fun a ha => ha ▸ h₀) (fun k a ha _ => by
      obtain ⟨b, hb, hs⟩ := exists_trNext f P ε O a ha
      exact ⟨b, hb, fun r => hs r k⟩)
  refine ⟨fun i => (r i).x, fun i => (r i).Δ, fun i => (r i).h, fun i => (r i).dd,
    fun i => (r i).jk, fun i => (r i).s, fun i => (r i).acc, by simp only [hr0],
    by simp only [hr0], by simp only [hr0], fun k => (hr k fun _ _ h => h).2 r rfl rfl⟩

end TRExistence

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ}
  {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E} {acc : ℕ → Prop} {L B : ℕ → ℝ} {κΔ : ℝ}

/-- **Counting the trial iterations of a run** (Lemma 14.2.3 of [cartis2022evaluation]): for a
TRqIDA run with a feasible set under `LipschitzDerivsAnchored f C A 0 q L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`) and an admissible `κ_Δ`, every iteration `k` up to the first iterate
that is approximately optimal on `X` satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13), with `𝒮_k` the
successful iterations in `[0, k]`, `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(ς κ_δ ε_min/Δ₀)|/|log γ₂| + N_𝒜`, where
`N_𝒜 = q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` bounds the number of
accuracy-improving iterations. -/
theorem IsTRqIDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.q L)
    (hL : ∀ j ≤ P.q, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsTRqIDARun f X κg P ε x₀ x Δ h D dd jk s acc)
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j < k, ¬ trqIDATest f X P ε x Δ j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card *
        (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
      (|Real.log (P.ς * (κΔ / 2) * epsMin P.q ε / P.Δ₀)| / |Real.log P.γ₂| +
        (P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
    add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ trqIDATest f X P ε x Δ j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hΔmin : P.ς * (κΔ / 2) * epsMin P.q ε ≤ Δ (k + 1) :=
    (IsTRqIDARun.delta_ge hf hL hXC hAX hrun hκΔ.1 hκΔ.2.1 hκΔ.2.2 (k + 1)).2.2.trans
      (min_le_left _ _)
  have hT := trqDA_card_trial_le (fun i _ => hrun.step i) hrun.Δ_zero
    (mul_pos (mul_pos P.ς_pos (half_pos hκΔ.1)) hrun.epsMin_pos) hΔmin
  have hA := IsTRqIDARun.card_acc_le hf hL hXC hAX hrun hκΔ hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

end Iterations

end Optimization
