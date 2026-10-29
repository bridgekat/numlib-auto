import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpDAStep

/-!
# ARqpIDA: adaptive regularization with implicit dynamic accuracy

The analysis of the adaptive-regularization method ARqpIDA ([cartis2022evaluation],
Algorithm 13.1.2): exact function values, inexact derivatives within `κ_{∇,i} h_{k,i}` of the
exact ones, and the iteration `ARqpDAStep`.

The analysis is stated for runs on a feasible set `X` (Step-1 displacements and trial points
in `{e | x_k + e ∈ X}`, [cartis2022evaluation] §14.2) under the smoothness hypothesis
`LipschitzDerivsAnchored f C A 0 p L` with normalized constants `L_j ≥ 1`, `X ⊆ C` and an anchor
set `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`: the objective does not increase along the runs, so the iterates
are anchors, derivative estimates are made at iterates, and trial points are related to them by
Taylor's theorem anchored at the iterate. The unconstrained methods of Chapter 13 are the case
`X = C = A = univ`.

## Main definitions

* `IsARqpIDARun`: a run on a feasible set with the exact-value ratio (13.1.58) (`arqpIDARatio`);
* `arqpIDATest`: approximate optimality on `X` for some radii in `(0, 1]^q`;
* `arqpIDASigmaMax`, `arConstA`, `arKappaAcc`: the constants of Lemmas 13.1.14–13.1.18 and
  Theorem 13.1.19.

## Main results

* `IsARqpIDARun.not_acc_of_le` (Lemma 13.1.12), `.sigma_le` (Lemma 13.1.14),
  `.arqpIDATest_of_pass` (Lemma 13.1.15), `.measure_ineq` (Lemma 13.1.16), `.step_bound`,
  `.norm_step_ge` (Lemma 13.1.17), `.decrease_ge` (Lemma 13.1.18), `.card_acc_le`,
  `.complexity` (the complexity argument of Theorem 13.1.19), `.complexity_of_radiiControl`
  (Theorem 14.2.4, ARqpIDA row), `.le_card_succ` (Lemma 14.2.3, ARqpIDA row);
* `.measure_ineq_unit`, `.step_bound_unit`, `.decrease_ge_unit`: the unit-radii argument for
  `q ≤ 2` without constraints (`δ ↦ φ^δ_j/δ^j` is non-increasing for `j ≤ 2`).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### ARqpIDA runs -/

/-- The ratio (13.1.58) of ARqpIDA: `ρ_k = (f(x_k) - f(x_k + s_k)) / \overline{ΔT}_{f,p}(x_k, s_k)`
with exact function values. -/
noncomputable def arqpIDARatio (f : E → ℝ) (P : ARqpIDAParams)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (x s : ℕ → E) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((D k).taylorDecrement P.p (s k))

/-- The test of approximate optimality used for ARqpIDA with a feasible set
([cartis2022evaluation], §14.2, (14.2.2)): `x_k` is an `(ε, δ)`-approximate `q`-th order
minimizer of `f` on the feasible set `X` (measures over `{e | x_k + e ∈ X}`) for *some* radii
`δ ∈ (0, 1]^q`. The unconstrained test is the case `X = univ`. -/
def arqpIDATest (f : E → ℝ) (X : Set E) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → E)
    (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε δ'

/-- **ARqpIDA with a feasible set** ([cartis2022evaluation], Algorithm 13.1.2; ARqpIDA-SC of §14.2)
as a run predicate, for the objective `f`, a feasible set `X` (displacements `{e | x_k + e ∈ X}`,
feasible trial points and Step-2 displacements; closedness of `X` is not used), the (unknown)
oracle constants `κ_{∇,i} ≥ 0`, constants `P`, tolerances `ε ∈ (0, 1]^q` with `ε ≤ δ₀`, a feasible
starting point `x₀ ∈ X`, and sequences of iterates `x`, regularization parameters `σ`, radii
`δ, δ₁, δs` (`δ^{(0)}_k, δ^{(1)}_k, δ_{s_k}`), requested accuracies `h`, inexact jets `D`
satisfying (13.1.2) up to order `p`, Step-1 displacements `dd`, orders `j_k`, steps `s` and
accuracy-improving flags `acc`; every iteration satisfies `ARqpDAStep` on `X` with the exact-value
ratio (13.1.58). The method has no termination rule (see `arqpIDATest`); the unconstrained method
is the case `X = univ`. -/
structure IsARqpIDARun (f : E → ℝ) (X : Set E) (κg : ℕ → ℝ) (P : ARqpIDAParams)
    (ε : ℕ → ℝ) (x₀ : E) (x : ℕ → E) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (dd : ℕ → ℕ → E) (jk : ℕ → ℕ) (s : ℕ → E)
    (acc : ℕ → Prop) : Prop where
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ε_j ≤ δ_{0,j}` (13.1.51). -/
  eps_le : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j
  /-- `κ_{∇,i} ≥ 0`. -/
  κg_nonneg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i
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
  /-- The error model (13.1.2) for `i ∈ [1, p]`. -/
  oracle : ∀ k, JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.p (fun i => κg i * h k i)
  /-- Steps 1–5. -/
  step : ∀ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc (arqpIDARatio f P D x s) k

namespace IsARqpIDARun

variable {f : E → ℝ} {X : Set E} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop}
  (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
include hrun

theorem invariants (k : ℕ) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh :=
  arqpDA_invariants (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero

theorem sigma_pos (k : ℕ) : 0 < σ k := P.σmin_pos.trans_le (hrun.invariants k).1

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Optimization.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Optimization.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaMax_nonneg : 0 ≤ ordMax P.p κg := ordMax_nonneg hrun.κg_nonneg

/-- The iterates are feasible. -/
theorem mem (k : ℕ) : x k ∈ X :=
  arqpDA_mem (fun i _ => hrun.step i) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along an ARqpIDA run with a feasible set: `f(x_k) ≤ f(x₀)` (the
ratio uses exact function values and the predicted decrease of a trial iteration is positive,
Lemma 13.1.13). -/
theorem objective_le (k : ℕ) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_forall_succ_le (u := fun i => f (x i)) fun i _ => ?_
  by_cases ha : acc i
  · simp only [(hrun.step i).x_acc ha, le_rfl]
  · exact ((hrun.step i).accept ha).le (w := f) rfl (ARqpDAStep.taylorDecrement_ge (hrun.step i) ha
      (fun j hj => (hrun.eps_mem j hj).1) (hrun.sigma_pos i).le).2

/-- The iterates lie in every set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set E} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) : x k ∈ A :=
  hAX _ (hrun.mem k) (hrun.objective_le k)

/-- (13.1.63): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` for `i ∈ [1, p]`, under the smoothness
hypothesis anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem norm_D_le {C A : Set E} {L : ℕ → ℝ} (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖D k i‖ ≤ lipMax L P.p + ordMax P.p κg * P.κh :=
  hf.norm_le_of_jetApprox hL (hrun.mem_anchor hAX k) (hrun.oracle k) hrun.κg_nonneg
    (fun i hi => ((hrun.invariants k).2.2 i hi).1) (fun i hi => ((hrun.invariants k).2.2 i hi).2) hi

/-- `L̄_f = L_f + κ_{∇,max} κ_h ≥ 1` for normalized constants `L_j ≥ 1`. -/
theorem one_le_Lbar {L : ℕ → ℝ} (hL : ∀ j ≤ P.p, 1 ≤ L j) :
    1 ≤ lipMax L P.p + ordMax P.p κg * P.κh := by
  have := one_le_lipMax hL; have := hrun.kappaMax_nonneg; have := P.κh_nonneg; nlinarith

end IsARqpIDARun

section ARqpIDA

variable {X C A : Set E} {f : E → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Accurate derivatives give trial iterations** (Lemma 13.1.12 of [cartis2022evaluation]): the
outcomes of Step 2 at iteration `k` of an ARqpIDA run. Assume the smoothness hypothesis, write
`L̄_f = L_f + κ_{∇,max} κ_h`, assume the radii control (13.1.69)–(13.1.70) at the earlier iterations
`i < k` (only these enter the radius bound at `k`), and let `σ̄` be any bound with `σ_i ≤ σ̄` for
`i ≤ k`. Then:
* if Step 2 is performed at `k`, then (13.1.74)
  `Δm̄_k(s_k) ≥ ¼ ς ε_{j_k} (δ^{(1)}_{k,j_k})^{j_k}/j_k! > 0`, hence `s_k ≠ 0`;
* (13.1.71) `δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ κ^{(1)}_δ(σ̄) ε_j` for `j ∈ [1, q]`;
* if Step 2 is performed at `k` and (13.1.73)
  `h_{k,i} ≤ κ_s (ς κ^{(1)}_δ(σ̄)^q/(12 q! max(L̄_f, σ̄)))^p ε_min^{p(q+1)}` for `i ∈ [1, p]`, then
  `k ∈ 𝒯`, i.e. iteration `k` is not accuracy-improving (`¬ acc k`). -/
theorem IsARqpIDARun.not_acc_of_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  have hrad := arqpDA_radius_ge (fun i _ => hrun.step i) (hrun.step k).toARqpStep1 hrun.σ_zero
    hrun.δ_zero hrun.h_zero
    hrun.eps_mem hrun.eps_le hLb (fun i _ ℓ hℓ => hrun.norm_D_le hf hL hAX i hℓ) hσ hrc
  refine ⟨fun hb => ?_, hrad, fun hb hh => ?_⟩
  · have h2 := (hrun.step k).step2 hb
    have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
      have := P.ς_pos; have := (hrun.eps_mem _ h2.jk_mem).1
      have := (hrun.step k).radius_pos _ h2.jk_mem; positivity
    have hm := h2.model_dec.trans h2.dec_le
    refine ⟨hpos, hm, fun h0 => ?_⟩
    rw [h0, arModelDec, sub_self] at hm
    linarith
  · have h2 := (hrun.step k).step2 hb
    exact h2.not_acc_of_le ((hrun.step k).radius_pos) hLb
      (fun i hi => hrun.norm_D_le hf hL hAX k hi)
      (hrun.sigma_pos k).le (arKappaDelta1_pos (by linarith)).le
      (arKappaDelta1_le_one hLb) hrun.eps_mem (fun j hj => (hrad j hj).1) hh

/-! ### The regularization weights -/

/-- The bound `σ_max = max(σ₀, γ₃ (2 L_{f,p} + 4 (p+1)! κ_s' κ_{∇,max})/(1 - η₂))` of (13.1.77),
with `κ_s' = max(κ_s, κ_h)`. -/
noncomputable def arqpIDASigmaMax (P : ARqpIDAParams) (Lp κm : ℝ) : ℝ :=
  max P.σ₀ (P.γ₃ * ((2 * Lp + 4 * (P.p + 1)! * max P.κs P.κh * κm) / (1 - P.η₂)))

/-- **The regularization weights stay bounded** (Lemma 13.1.14 of [cartis2022evaluation]): under the
smoothness hypothesis, every ARqpIDA run satisfies `σ_k ≤ σ_max` (13.1.77) for all `k`, with
`σ_max = arqpIDASigmaMax` (the constant `κ_s' = max(κ_s, κ_h)` covers the long steps `‖s_k‖ ≥ 1`,
where the accuracy test (13.1.46) is not performed and only `h_{k,i} ≤ κ_h` is known). -/
theorem IsARqpIDARun.sigma_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := by
  set κm := ordMax P.p κg
  set κs' := max P.κs P.κh
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  have hκs' : 0 ≤ κs' := P.κs_pos.le.trans (le_max_left _ _)
  have hLp : 1 ≤ L P.p := hL _ le_rfl
  set σbar := (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) / (1 - P.η₂)
  have key : ∀ k, ¬ acc k → σbar ≤ σ k → P.η₂ ≤ arqpIDARatio f P D x s k := by
    intro k hk hσk
    have hs := hrun.step k
    have h2 := hs.step2_of_not_acc hk
    obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le
    set t := ‖s k‖
    have hherr : ∀ i ∈ Finset.Icc 1 P.p, κg i * h k i ≤ κm * κs' * t ^ (P.p - i + 1) := by
      intro i hi
      have hhi : h k i ≤ κs' * t ^ (P.p - i + 1) := by
        rcases lt_or_ge t 1 with ht | ht
        · exact (h2.accuracy_le_of_not_acc hk ht i hi).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact (((hrun.invariants k).2.2 i hi).2.trans (le_max_right _ _)).trans
            (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) hhi ((hrun.invariants k).2.2 i hi).1 hκm
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy hκm hκs' (hrun.oracle k) hherr le_rfl
    have hR := hf.abs_sub_taylorDecrement_le_of_le le_rfl (hrun.mem_anchor hAX k) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) ≤ (1 - P.η₂) * σ k := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσk
      linarith
    rw [arqpIDARatio, reductionRatio_def]
    refine le_div_of_inexact_error_le (fx := f (x k)) (fxs := f (x k + s k))
      (ΔT := (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k)) hpos ?_
    rw [sub_self, sub_self, abs_zero, zero_add, add_zero]
    have htp : 0 ≤ t ^ (P.p + 1) := by positivity
    calc |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k))| +
          |(ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k) - (D k).taylorDecrement P.p (s k)|
        ≤ L P.p / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) + 2 * κs' * κm * t ^ (P.p + 1) :=
          add_le_add hR (by rw [abs_sub_comm]; exact hE)
      _ = (L P.p + 2 * (P.p + 1)! * κs' * κm) / (P.p + 1)! * t ^ (P.p + 1) := by
          field_simp
      _ ≤ (1 - P.η₂) * σ k / (P.p + 1)! * t ^ (P.p + 1) := by
          gcongr
          have : 0 ≤ (P.p + 1)! * κs' * κm := by positivity
          linarith
      _ = (1 - P.η₂) * (σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1)) := by ring
      _ ≤ (1 - P.η₂) * (D k).taylorDecrement P.p (s k) :=
          mul_le_mul_of_nonneg_left hlow P.one_sub_η₂_pos.le
  have h := sigma_le_max_of_arUpdate_of_neutral (σ := σ) (K := k) (σbar := σbar)
    (ρ := arqpIDARatio f P D x s) P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃
    (hrun.σ_zero ▸ P.σ₀_pos) (fun i _ => by
      by_cases ha : acc i
      · exact Or.inl ((hrun.step i).σ_acc ha)
      · exact Or.inr ⟨(hrun.step i).update ha, key i ha⟩) k le_rfl
  rwa [hrun.σ_zero] at h

/-! ### Certification and the radius inequality -/

/-- **Certification at Step 5** (Lemma 13.1.15 of [cartis2022evaluation]): under the smoothness
hypothesis and the radii control at every iteration before `k`, if Step 1 of ARqpIDA branches to
Step 5 at iteration `k` ((13.1.53) at every order) and (13.1.78)
`κ_{∇,max} h_{k,i} ≤ ς κ^{(1)}_δ(σ_max)^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, p]`, then `x_k` is an
`(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer with `δ^{(1)}_k ∈ (0, 1]^q` (in particular
`arqpIDATest k`). -/
theorem IsARqpIDARun.arqpIDATest_of_pass (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) ∧
        arqpIDATest f X P ε x k := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := (IsARqpIDARun.not_acc_of_le hf hL hAX hrun hrc (k := k)
    (fun i _ => IsARqpIDARun.sigma_le hf hL hXC hAX hrun i)).2.1
  have hmem : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
    ⟨(hrun.step k).radius_pos j hj, (hrad j hj).2.trans ((hrun.invariants k).2.1 j hj).2⟩
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have happrox : IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
    intro j hj
    obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    set em := epsMin P.q ε
    have hw := ((hrun.step k).witness j hj).2
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := (mul_le_of_le_one_left hεmin.le hκ1).trans hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le hj) hκ0.le).trans (hrad j hj).1) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * em ≤ ε j := (mul_le_of_le_one_left hεmin.le hς1).trans (epsMin_le hj)
    refine taylorMeasure_le_of_inexact_certificate_uniform ((hrun.oracle k).mono P.q_le_p) hj
      (by simpa using hrun.mem k) (hmem j hj).1.le (hmem j hj).2 hς hw (hpass j hj)
      (e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)) (fun i hi => ?_) ?_
    · have hip : i ∈ Finset.Icc 1 P.p :=
        Finset.Icc_subset_Icc le_rfl (hjq.trans P.q_le_p) hi
      exact (mul_le_mul_of_nonneg_right (le_ordMax hip) ((hrun.invariants k).2.2 i hip).1).trans
        (hh i hip)
    · calc P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) =
            P.ς * em * (κ * em) ^ P.q / (4 * P.q !) := by ring
        _ ≤ ε j * δ₁ k j ^ j / (4 * P.q !) :=
            div_le_div_of_nonneg_right (mul_le_mul hεj hδj (pow_nonneg hm0 _)
              (hrun.eps_mem j hj).1.le) (by positivity)
        _ ≤ ε j * δ₁ k j ^ j / (4 * j !) := by
            gcongr
            exact mul_nonneg (hrun.eps_mem j hj).1.le (pow_nonneg (hmem j hj).1.le _)
  exact ⟨hmem, happrox, δ₁ k, hmem, happrox⟩

/-- **The radius inequality** (Lemma 13.1.16 of [cartis2022evaluation]): under the smoothness
hypothesis, let iteration `k` of ARqpIDA be successful with `‖s_k‖ < 1`, and let `x_{k+1}` not be
approximately optimal for the radii `δ_{k+1} = δ^{(0)}_{k+1}` (`= δ_{s_k}`). Then for some
`j ∈ [1, q]` (13.1.79)
`(1 - θ) ε_j δ_{k+1,j}^j/j!
≤ (L_{f,p} + σ_max + 3 κ_{∇,max} κ_s) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ! ‖s_k‖^{p-ℓ+1}`,
with `σ_max` of Lemma 13.1.14. -/
theorem IsARqpIDARun.measure_ineq (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add hk hρ
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  rw [hδ] at hlt ⊢
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring]
      at this
    exact le_of_mul_le_mul_left this hς
  have hxA := hrun.mem_anchor hAX k
  have := radius_inequality_of_measure_gt_anchored hf.convex
    (fun y hy => hf.contDiffAt_of_le le_rfl hy) (hf.lipschitzAt_of_le le_rfl hxA)
    (zero_le_one.trans (hL _ le_rfl)) (hf.subset hxA)
    (hXC h2.mem) (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.accuracy_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le (IsARqpIDARun.sigma_le hf hL hXC hAX hrun k) hjp (by simpa using h2.mem)
    hδmem.1.le
    (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-! ### Step length and decrease -/

/-- The constant `L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` of Lemmas 13.1.16–13.1.18. -/
noncomputable def arConstA (P : ARqpIDAParams) (L : ℕ → ℝ) (κm : ℝ) : ℝ :=
  L P.p + arqpIDASigmaMax P (L P.p) κm + 3 * κm * P.κs

theorem one_le_arConstA {P : ARqpIDAParams} {L : ℕ → ℝ} {κm : ℝ} (hL : 1 ≤ L P.p)
    (hκm : 0 ≤ κm) : 1 ≤ arConstA P L κm := by
  have h1 : 0 ≤ arqpIDASigmaMax P (L P.p) κm := P.σ₀_pos.le.trans (le_max_left _ _)
  have h2 : 0 ≤ 3 * κm * P.κs := by have := P.κs_pos; positivity
  unfold arConstA; linarith

/-- `κ^{(1)}_δ(σ') ε ≤ ς θ ε/(24 max(L̄, σ))` for `σ ≤ σ'`. -/
theorem arKappaDelta1_mul_le {P : ARqpIDAParams} {Lb σ σ' e : ℝ} (hLb : 0 < Lb) (hσ : σ ≤ σ')
    (he : 0 ≤ e) : arKappaDelta1 P Lb σ' * e ≤ P.ς * P.θ * e / (24 * max Lb σ) := by
  have := P.ς_pos; have := P.θ_pos
  have hM : 0 < max Lb σ := lt_max_of_lt_left hLb
  have hM' : max Lb σ ≤ max Lb σ' := max_le_max le_rfl hσ
  rw [arKappaDelta1, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- The step-length bounds behind Lemmas 13.1.17 and 13.1.18 for ARqpIDA: at a successful iteration
`k` with the radii control at `k` and `x_{k+1}` not approximately optimal for the radii
`δ_{k+1}`, either `‖s_k‖ ≥ 1` or the conclusions of `arqp_pow_ge_of_radius_ineq` hold for some
order `j` with `a = 1 - θ`, `A = L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` and `κ = κ_{δ,min}`. -/
theorem IsARqpIDARun.step_bound (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := IsARqpIDARun.measure_ineq hf hL hXC hAX hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb := hrun.one_le_Lbar hL
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le hk hs1 hrun.eps_mem hLb (IsARqpIDARun.sigma_le hf hL hXC hAX hrun k) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc hk hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hL _ le_rfl
    have : 0 ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- **The step is long** (Lemma 13.1.17 of [cartis2022evaluation]): under the smoothness hypothesis
and the radii control at iteration `k`, if iteration `k` of ARqpIDA is successful and `x_{k+1}`
is not approximately optimal for the radii `δ_{k+1}`, then for some `j ∈ [1, q]` (13.1.80):
* if `q ≤ 2`, `‖s_k‖ ≥ ((1 - θ)/(2 j! A))^{1/(p-j+1)} ε_j^{1/(p-j+1)}`;
* if `q > 2`, `‖s_k‖ ≥ ((1 - θ) κ̂^{j-1}/(2 j! A))^{1/p} ε_j^{j/p}`, where `A = L_{f,p} + σ_max
  + 3 κ_{∇,max} κ_s` and `κ̂ = min(κ_{δ,min}, (1-θ)/(2 q! A))` with `κ_{δ,min} = ς θ/(24
  max(L̄_f, σ_max))` (13.1.81). -/
theorem IsARqpIDARun.norm_step_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    (u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (¬ u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound hf hL hXC hAX hrun hrc hk hρ hnot
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set A := arConstA P L (ordMax P.p κg)
  have hLb := hrun.one_le_Lbar hL
  set κh := arKappaHat P.q (1 - P.θ) A (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one
  have hεj := hrun.eps_mem j hj
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hden : 0 < 2 * (j ! : ℝ) * A := by nlinarith
  have hb0 : 0 ≤ (1 - P.θ) / (2 * j ! * A) := div_nonneg (by linarith) hden.le
  have hb1 : (1 - P.θ) / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  have hκh0 : 0 ≤ κh := le_min (arKappaDelta1_pos (by linarith)).le
    (div_nonneg (by linarith) (by nlinarith))
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans (arKappaDelta1_le_one hLb)
  have hB0 : 0 ≤ (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) := by
    exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg hκh0 _)) hden.le
  have hB1 : (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) ≤ 1 := by
    rw [mul_div_right_comm]
    exact (mul_le_of_le_one_left (pow_nonneg hκh0 _) hb1).trans (pow_le_one₀ hκh0 hκh1)
  rcases hb with hs1 | ⟨hq2, hq3⟩
  · refine ⟨fun _ => ⟨j, hj, ?_⟩, fun _ => ⟨j, hj, ?_⟩⟩
    · exact ((mul_le_of_le_one_left (Real.rpow_nonneg hεj.1.le _)
        (Real.rpow_le_one hb0 hb1 (by positivity))).trans
        (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
    · exact ((mul_le_of_le_one_left (Real.rpow_nonneg hεj.1.le _)
        (Real.rpow_le_one hB0 hB1 (by positivity))).trans
        (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
  refine ⟨fun hq => ⟨j, hj, ?_⟩, fun hq => ⟨j, hj, ?_⟩⟩
  · rw [← Real.mul_rpow hb0 hεj.1.le]
    exact Optimization.rpow_one_div_le_of_le_pow (by omega) (mul_nonneg hb0 hεj.1.le)
      (norm_nonneg _) (hq2 hq)
  · have hp0 : P.p ≠ 0 := by have := P.one_le_p; omega
    have he : ε j ^ ((j : ℝ) / P.p) = (ε j ^ j) ^ (1 / (P.p : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεj.1.le, mul_one_div]
    rw [he, ← Real.mul_rpow hB0 (pow_nonneg hεj.1.le _)]
    refine Optimization.rpow_one_div_le_of_le_pow hp0 (mul_nonneg hB0 (pow_nonneg hεj.1.le _))
      (norm_nonneg _) ?_
    calc (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) * ε j ^ j =
          (1 - P.θ) / (2 * j ! * A) * κh ^ (j - 1) * ε j ^ j := by ring
      _ ≤ ‖s k‖ ^ P.p := hq3 hq

/-- **Sufficient decrease** (Lemma 13.1.18 of [cartis2022evaluation]): under the smoothness
hypothesis and the radii control at every iteration, if iteration `k` of ARqpIDA is successful
and `x_{k+1}` is not approximately optimal (for any radii in `(0, 1]^q`), then (13.1.82)
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ κ_{Δm} min_{j ∈ [1,q]} ε_j^{π_j}` and (13.1.83) `f(x_k) -
f(x_{k+1}) ≥ ½ η₁ κ_{Δm} min_j ε_j^{π_j}`, with `π_j = arPi q p j` and `κ_{Δm} = σ_min/(p+1)! ·
arStepConst q p (1 - θ) A κ_{δ,min}`: for `q ≤ 2`, `κ_{Δm} = σ_min/(p+1)! ((1-θ)/(2 q!
A))^{(p+1)/(p-q+1)}`, for `q > 2`, `κ_{Δm} = σ_min/(p+1)! ((1-θ) κ̂^{q-1}/(2 q! A))^{q(p+1)/p}`
(`κ̂` as in `IsARqpIDARun.norm_step_ge`). -/
theorem IsARqpIDARun.decrease_ge (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    [Decidable u]
    (hrc : ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k)
    (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arqpIDATest f X P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1)) :=
    fun hc => hnot ⟨δ (k + 1), fun j hj => (hrun.invariants (k + 1)).2.1 j hj, hc⟩
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound hf hL hXC hAX hrun hrc hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar hL
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA hεj.1 hεj.2 ht
    (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf u P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Optimization.epsMin_pos P.one_le_q fun j hj =>
      Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
  have hσ := (hrun.invariants k).1
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
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) /
          2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

/-! ### Complexity -/

/-- The constant `κ_acc` of the proof of Theorem 13.1.19 ([cartis2022evaluation]):
`min(ς κ^q/(4 q! κ_{∇,max}), κ_s (ς κ^q/(12 q! max(L̄_f, σ_max)))^p)` with `κ = κ^{(1)}_δ(σ_max)`,
the first term being omitted when `κ_{∇,max} = 0`. -/
noncomputable def arKappaAcc (P : ARqpIDAParams) (κ Lb σmax κm : ℝ) : ℝ :=
  if κm = 0 then P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p
  else min (P.ς * κ ^ P.q / (4 * P.q ! * κm))
    (P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p)

theorem arKappaAcc_pos {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 < κ) (hLb : 0 < Lb)
    (hκm : 0 ≤ κm) : 0 < arKappaAcc P κ Lb σmax κm := by
  have := P.ς_pos; have := P.κs_pos
  have hM : 0 < max Lb σmax := lt_max_of_lt_left hLb
  unfold arKappaAcc
  split_ifs with h0
  · positivity
  · exact lt_min (by have := lt_of_le_of_ne hκm (Ne.symm h0); positivity) (by positivity)

theorem arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} :
    arKappaAcc P κ Lb σmax κm ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p := by
  unfold arKappaAcc
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem mul_arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 ≤ κ) (hκm : 0 ≤ κm) :
    κm * arKappaAcc P κ Lb σmax κm ≤ P.ς * κ ^ P.q / (4 * P.q !) := by
  have := P.ς_pos
  unfold arKappaAcc
  split_ifs with h0
  · rw [h0, zero_mul]; positivity
  · have hκm' : 0 < κm := lt_of_le_of_ne hκm (Ne.symm h0)
    calc κm * min (P.ς * κ ^ P.q / (4 * P.q ! * κm)) _
        ≤ κm * (P.ς * κ ^ P.q / (4 * P.q ! * κm)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hκm
      _ = P.ς * κ ^ P.q / (4 * P.q !) := by field_simp

/-- **The accuracy-improving iterations of ARqpIDA with a feasible set** (proof of Theorem 13.1.19,
[cartis2022evaluation]): under `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`, `A ⊇ {y ∈ X |
f(y) ≤ f(x₀)}`) and the radii control at every iteration, if no iterate `x_j`, `j ≤ k`, is
approximately optimal on `X`, then `|𝒜_k| ≤ p(q+1)/|log γ_h| |log ε_min| +
|log(κ_acc/κ_h)|/|log γ_h| + 1` (either mode of the radii control, `ARqpDARadiiControl`). -/
theorem IsARqpIDARun.card_acc_le (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arqpIDATest f X P ε x j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
          |Real.log P.γh| + 1 := by
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set σmax := arqpIDASigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => IsARqpIDARun.sigma_le hf hL hXC hAX hrun k
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  set κacc := arKappaAcc P κ Lb σmax κm
  have hκacc : 0 < κacc := arKappaAcc_pos hκ0 (by linarith) hκm
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.p * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith [P.one_le_p])
  have hp := P.one_le_p
  have h := card_accuracyImproving_le_of_pow_of_nonneg (acc := acc)
    (hmax := fun j => ordMax P.p (h j))
    (N := P.p * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_nonneg hκacc hεmin
    ((ordMax_le_iff hp).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j _ => (ordMax_le_iff hp).2 fun i hi => ((hrun.invariants j).2.2 i hi).2)
    (fun j _ ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from funext ((hrun.step j).h_acc ha),
        ordMax_mul hp P.γh_pos.le])
    (fun j _ ha => by rw [(hrun.step j).h_trial ha])
    (fun j hj ha => by
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.p, h j i ≤ κacc * em ^ (P.p * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd j i
      · refine (IsARqpIDARun.not_acc_of_le hf hL hAX hrun (fun i _ => hrc i) (k := j)
          (fun i _ => hσk i)).2.2 hfail
          (fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hk j hj
          (IsARqpIDARun.arqpIDATest_of_pass hf hL hXC hAX hrun (fun i _ => hrc i) hfail fun i
            hi => ?_).2.2
        calc κm * h j i ≤ κm * (κacc * em ^ (P.p * (P.q + 1))) :=
              mul_le_mul_of_nonneg_left (hhi i hi) hκm
          _ = κm * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le hκm) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **The complexity argument of Theorem 13.1.19** ([cartis2022evaluation]), for any decrease
constant: under the smoothness hypothesis, f.Bb and the radii control at every iteration, if
every successful iteration `k` of an ARqpIDA run followed by an iterate `x_{k+1}` that is not
approximately optimal decreases `f` by at least `c > 0`, then there is a first approximately
optimal iterate `x_{k_ε}`, before which at most `(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c +
log(σ_max/σ₀)/log γ₂ + 2 + |log γ₁|/log γ₂` function evaluations and at most `(f(x₀) - f_low)/c
+ p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 3` derivative estimates are made. -/
theorem IsARqpIDARun.complexity (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arqpIDATest f X P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar hL
  set σmax := arqpIDASigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => IsARqpIDARun.sigma_le hf hL hXC hAX hrun k
  have hσ₀ : P.σ₀ ≤ σmax := le_max_left _ _
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  set N := (f x₀ - flow) / c with hN_def
  have hN0 : 0 ≤ N := by positivity
  -- successful iterations before termination
  have hS : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤ N + 1 := by
    refine card_successSet_le_add_one_of_forall hN0 fun k hk => ?_
    rw [hN_def, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j _ hj => by rw [(hrun.step j).iterate_succ_eq hj])
      (fun j hj hs => hdec j hs.1 hs.2 (hk (j + 1) (by omega))) (hb _ (hrun.mem _))
  -- trial iterations
  have hlog2 : 0 < Real.log P.γ₂ := P.log_γ₂_pos
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂ with hcT
  have hcT0 : 0 ≤ cT := by positivity
  set NT := (N + 1) * cT + Real.log (σmax / P.σ₀) / Real.log P.γ₂ with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ Real.log (σmax / P.σ₀) :=
      Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)
    positivity
  have hT : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) →
      ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have h1 := arqpDA_card_trial_le (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
      (hσk (k + 1))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- accuracy-improving iterations
  set κacc := arKappaAcc P κ Lb σmax κm
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hp := P.one_le_p
  have hA : ∀ k, (∀ j ≤ k, ¬ arqpIDATest f X P ε x j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => IsARqpIDARun.card_acc_le hf hL hXC hAX hrun hrc hk
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) + 1 ≤ derivEvalCount acc kε +
        derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  refine ⟨kε, hkε, ?_, ?_⟩
  · calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ NT + 1 := hTk
      _ = _ := by rw [hNT_def, hcT]; ring
  · calc _ ≤ (NA + 1) + (N + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

/-- **Radius one for orders `≤ 2`** (used for Theorem 13.1.19 (1)): if `q ≤ 2` and `x` is an
`(ε, δ)`-approximate `q`-th order minimizer for some radii `δ ∈ (0, 1]^q` (unconstrained), then
`φ^1_{f,j}(x) ≤ ε_j/j!` for `j ∈ [1, q]` (`δ ↦ φ^δ_j/δ^j` is non-increasing for `j ≤ 2`,
`Optimization.pow_div_mul_taylorMeasure_le`). -/
theorem isEpsDeltaApprox_one_of_le_two {D : FormalMultilinearSeries ℝ E ℝ} {q : ℕ}
    (hq : q ≤ 2) {ε δ : ℕ → ℝ} (hδ : ∀ j ∈ Finset.Icc 1 q, δ j ∈ Set.Ioc 0 1)
    (h : IsEpsDeltaApprox D univ q ε δ) : IsEpsDeltaApprox D univ q ε (fun _ => 1) := by
  intro j hj
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq
  have h1 := pow_div_mul_taylorMeasure_le D hj2 (hδ j hj).1 (hδ j hj).2
  have h2 := h j hj
  have hpos : 0 < δ j ^ j := pow_pos (hδ j hj).1 j
  have hf : (0 : ℝ) < j ! := by positivity
  rw [div_one] at h1
  simp only [one_pow, mul_one]
  have : δ j ^ j * taylorMeasure D j 1 univ ≤ δ j ^ j * (ε j / j !) := by
    calc δ j ^ j * taylorMeasure D j 1 univ ≤ ε j * δ j ^ j / j ! := h1.trans h2
      _ = δ j ^ j * (ε j / j !) := by ring
  exact le_of_mul_le_mul_left this hpos

/-- **The radius inequality at unit radii**: for an ARqpIDA run on `E`
(`IsARqpIDARun` with `X = univ`) under the smoothness hypothesis, a successful iteration `k`
with `‖s_k‖ < 1` such that `x_{k+1}` is not approximately optimal with unit radii satisfies
(13.1.79) with `δ = 1`, whatever the radii `δ_{s_k}` of Step 2: since `δ ↦ φ^δ_ℓ/δ^ℓ` is
non-increasing for `ℓ ≤ 2` (`Optimization.pow_div_mul_taylorMeasure_le`), the bound (13.1.57)
on the model at the radii `δ_{s_k}` gives the same bound at radius `1`. -/
theorem IsARqpIDARun.measure_ineq_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * 1 ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, 1 ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.iterate_succ_eq_add hk hρ
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq2
  have hfj : (0 : ℝ) < j ! := by positivity
  have h₂δ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      univ ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring,
      Set.setOf_add_mem_univ] at this
    exact le_of_mul_le_mul_left this hς
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1
      univ ≤ P.θ * ε j * 1 ^ j / j ! := by
    have hmono := pow_div_mul_taylorMeasure_le
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) hj2 hδmem.1 hδmem.2
    rw [div_one] at hmono
    have hpos : 0 < δs k j ^ j := pow_pos hδmem.1 j
    rw [one_pow, mul_one]
    have : δs k j ^ j * taylorMeasure
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1 univ ≤
        δs k j ^ j * (P.θ * ε j / j !) := by
      calc _ ≤ P.θ * ε j * δs k j ^ j / j ! := hmono.trans h₂δ
        _ = δs k j ^ j * (P.θ * ε j / j !) := by ring
    exact le_of_mul_le_mul_left this hpos
  have := radius_inequality_of_measure_gt hf.convex (fun y hy => hf.contDiffAt_of_le le_rfl hy)
    (hf.lipschitzOn_of_le le_rfl) (zero_le_one.trans (hL _ le_rfl)) (mem_univ _) (mem_univ _)
    (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.accuracy_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le
        (IsARqpIDARun.sigma_le hf hL subset_rfl (fun _ _ _ => mem_univ _) hrun k) hjp (mem_univ 0)
    zero_le_one (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-- **The step bound at unit radii** (`q ≤ 2`, no constraints): for an ARqpIDA run on `E` under the
smoothness hypothesis and any radii, a successful iteration `k` such that `x_{k+1}` is not
approximately optimal with unit radii has a long step or `(1-θ)/(2 j! A) ε_j ≤ ‖s_k‖^{p-j+1}`
for some `j ∈ [1, q]` (in the unit-radii mode). -/
theorem IsARqpIDARun.step_bound_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := IsARqpIDARun.measure_ineq_unit hf hL hq2 hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have hLb := hrun.one_le_Lbar hL
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hεj := hrun.eps_mem j hj
  have hκε : κ * ε j ≤ 1 := (mul_le_of_le_one_left hεj.1.le hκ1).trans hεj.2
  have ht : 0 < ‖s k‖ := by
    have hpos := (ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hL _ le_rfl
    have : 0 ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (u := True) (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 one_pos
    hj P.q_le_p hκ0 hκε (fun _ => rfl) hineq

/-- **Sufficient decrease at unit radii**: for an ARqpIDA run on `E` under the
smoothness hypothesis and any radii, every successful iteration `k` such that `x_{k+1}` is not
approximately optimal (`arqpIDATest`, some radii in `(0, 1]^q`) decreases `f` by at least `½ η₁
κ_{Δm} min_j ε_j^{(p+1)/(p-j+1)}`, the decrease of the unit-radii mode (the unit-radii mode `u
= True`), whatever the radii control of the run. -/
theorem IsARqpIDARun.decrease_ge_unit (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hq2 : P.q ≤ 2)
    (hrun : IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ arqpIDATest f univ P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1) :=
    fun hc => hnot ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, by rwa [Set.setOf_add_mem_univ]⟩
  obtain ⟨j, hj, hb⟩ := IsARqpIDARun.step_bound_unit hf hL hq2 hrun hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := ARqpDAStep.taylorDecrement_ge hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar hL
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (u := True) (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA
    hεj.1 hεj.2 ht (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf True P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ ε j ^ arPiOf True P.p j :=
    epsMin_le hj
  have hσ := (hrun.invariants k).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf True P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C *
      epsMin P.q (fun j => ε j ^ arPiOf True P.p j) := by
    have hm0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf True P.p j) :=
      (Optimization.epsMin_pos P.one_le_q fun j hj =>
        Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) / 2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

end ARqpIDA

section Iterations

variable {f : E → ℝ} {X C A X₀ : Set E} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : E}
  {x : ℕ → E} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {dd : ℕ → ℕ → E} {jk : ℕ → ℕ} {s : ℕ → E}
  {acc : ℕ → Prop} {L B : ℕ → ℝ} {u : Prop}

/-- **Counting the trial iterations of a run** (Lemma 14.2.3 of [cartis2022evaluation]): for an
ARqpIDA run with a feasible set under `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`) and the radii control, every iteration `k` up to the first iterate
that is approximately optimal on `X` satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13) with
`κ_uns = 1 + |log γ₁|/log γ₂` and `κ_unc = log(σ_max/σ₀)/log γ₂ + N_𝒜`,
`N_𝒜 = p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. The radii control
(`ARqpDARadiiControl u`) may be in either mode (unit radii, or the (12.2.51)-type lower bounds
at every order). -/
theorem IsARqpIDARun.le_card_succ (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j < k, ¬ arqpIDATest f X P ε x j) :
    (k : ℝ) ≤ (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
      (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ +
        (P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 1)) := by
  have hc : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ :=
    add_nonneg zero_le_one (div_nonneg (abs_nonneg _) P.log_γ₂_pos.le)
  have hσ : 0 ≤ Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (le_max_left _ _))) P.log_γ₂_pos.le
  rcases k with _ | k
  · rw [Nat.cast_zero]; positivity
  have hk' : ∀ j ≤ k, ¬ arqpIDATest f X P ε x j := fun j hj => hk j (Nat.lt_succ_of_le hj)
  have hT := arqpDA_card_trial_le (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
    (IsARqpIDARun.sigma_le hf hL hXC hAX hrun (k + 1))
  have hA := IsARqpIDARun.card_acc_le hf hL hXC hAX hrun hrc hk'
  have hsum : ((successSet (fun i => ¬ acc i) k).card : ℝ) + (successSet acc k).card = k + 1 := by
    exact_mod_cast card_trial_add_card_acc acc k
  have hmono : ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) (k + 1)).card := by
    exact_mod_cast card_successSet_mono k.le_succ
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hmono hc]

/-- **Evaluation complexity under the radii control** (Theorem 14.2.4 of [cartis2022evaluation]):
under `f ≥ f_low` on `X`, `LipschitzDerivsAnchored f C A 0 p L` (`L_j ≥ 1`,
`A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`) and the radii control at every iteration, every ARqpIDA with a
feasible set run reaches a first iterate `x_{k_ε} ∈ X` that is an `(ε, δ_ε)`-approximate `q`-th
order minimizer on `X` for some radii `δ_ε ∈ (0, 1]^q` (`arqpIDATest`), before which at most
`(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c + κ^C` function evaluations and
`(f(x₀) - f_low)/c + κ^E |log ε_min| + κ^F + 3` derivative estimates are made, where
`c = ½ η₁ κ_{Δm} min_j ε_j^{π_j}` is the decrease of Lemma 14.2.2, and the constants are those of
Theorem 13.1.19, with the radii control in either mode `u` (`ARqpDARadiiControl`): unit radii
`δ_{s_k} = 1` (`u`), which Step 2 guarantees for `X = E` with `q ≤ 2` or for `q = 1` with `X`
convex, with `π_j = (p+1)/(p-j+1)`, or the (12.2.51)-type lower bounds at every order (`¬ u`),
available for every `q` and `X`, with `π_j = j(p+1)/p` (`π_j = arPiOf u p j`; the radii control of
Theorem 13.1.19, `RadiiControl`, is the mode `u = (q ≤ 2)`). -/
theorem IsARqpIDARun.complexity_of_radiiControl (hf : LipschitzDerivsAnchored f C A 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : IsARqpIDARun f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    [Decidable u]
    (hrc : ∀ i, ARqpDARadiiControl u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) :
    ∃ kε, IsFirstHit (arqpIDATest f X P ε x) kε ∧ x kε ∈ X ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j))) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) /
          (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
            (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
            epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) +
          P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hLb := hrun.one_le_Lbar hL
  have hA := one_le_arConstA (hL _ le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hC := arStepConstOf_pos (u := u) (q := P.q) (p := P.p) (sub_pos.2 P.θ_lt_one)
    (zero_lt_one.trans_le hA) (arKappaDelta1_pos (Lb := lipMax L P.p + ordMax P.p κg * P.κh)
      (σ := arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (P := P) (by linarith))
  have hm : 0 < epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    Optimization.epsMin_pos P.one_le_q fun j hj => Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
      epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := IsARqpIDARun.complexity hf hL hXC hAX hb hrun hrc hc
    fun k hk hρ hnot => (IsARqpIDARun.decrease_ge hf hL hXC hAX hrun (hrc k) hk hρ hnot).2
  exact ⟨kε, hk, hrun.mem kε, h1, h2⟩

end Iterations

end Optimization
