/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA

/-!
# Existence of ARqpIDA runs

In finite dimension, iterations of ARqpIDA (Algorithm 13.1.2 of [cartis2022evaluation]) can be
performed from every admissible state, for every deterministic oracle that satisfies the error model
(13.1.2) $\|\overline{\nabla}^i f(x) - \nabla^i f(x)\| \le \kappa_{\nabla,i} h_i$. The halving loop
of Step 1 stops, Step 2 can use a global minimizer of the regularized model, and the resulting
sequences satisfy the radii control (13.1.69)–(13.1.70). The setting is the whole space $E$, without
constraints.

## Main results

* `Optimization.exists_arqpDA_halving`: the halving loop of Step 1 stops (the existence half of
  Lemma 13.1.11).
* `Optimization.exists_arqpDA_steps`: from every admissible state there are sequences all of whose
  iterations are ARqpIDA iterations on $E$ that satisfy the radii control.
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Existence of ARqpIDA runs -/

section ARExistence

variable [FiniteDimensional ℝ E]

open Classical in
/-- The halving loop of Step 1 of ARqpIDA stops. Let $E$ be finite-dimensional, let $D$ be
derivative data with $\|D_\ell\| \le \overline{L}$ for $\ell \in [1, p]$ and $\overline{L} > 0$,
let $\sigma \ge 0$, $j \le p$, $0 < \varsigma \le 1$, $e > 0$ and $\delta \in (0, 1]$. Write
$m(d) = T_p(d) + \sigma\|d\|^{p+1}/(p+1)!$ for the regularized model of $D$ and $\Delta T_j$ for
the order-$j$ Taylor decrement of $D$. Then there are a radius $\delta_1$ and a displacement $d$
such that:
* $0 < \delta_1 \le \delta$ and $\delta_1 = \delta/2^m$ for some $m \in \mathbb{N}$;
* $d$ is a $\varsigma$-approximate optimality displacement of $\Delta T_j$ for the radius
  $\delta_1$ (13.1.52);
* the test (13.1.53) $\Delta T_j(d) \le \varsigma e\delta_1^j/(2\,j!)$ or the condition
  (13.1.54) $m(0) - m(d) \ge \varsigma e\delta_1^j/(4\,j!)$ holds;
* if $\delta_1 < \delta$, then $2\delta_1 \le \delta$, some $d'$ with $\|d'\| \le 2\delta_1$ has
  $\Delta T_j(d') > \varsigma e(2\delta_1)^j/(2\,j!)$ and $m(0) - m(d') < \varsigma
  e(2\delta_1)^j/(4\,j!)$ (the last halving), and some $d_0$ with $\|d_0\| \le \delta$ has
  $\Delta T_j(d_0) > \varsigma e\delta^j/(2\,j!)$ (the first halving).

This is the existence half of Lemma 13.1.11 of [cartis2022evaluation]. The number $e$ stands for
the tolerance $\varepsilon_j$, and the result gives the data of `Optimization.ARqpStep1` at one
order. -/
theorem exists_arqpDA_halving {D : FormalMultilinearSeries ℝ E ℝ} {p : ℕ} {σ Lb : ℝ} (hσ : 0 ≤ σ)
    (hLb : 0 < Lb) (hD : ∀ ℓ ∈ Finset.Icc 1 p, ‖D ℓ‖ ≤ Lb) {j : ℕ} (hjp : j ≤ p)
    {ς e δ : ℝ} (hς : 0 < ς) (hς1 : ς ≤ 1) (he : 0 < e) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ δ₁ d, 0 < δ₁ ∧ δ₁ ≤ δ ∧ IsApproxMeasureStep (D.taylorDecrement j) δ₁ univ ς d ∧
      (D.taylorDecrement j d ≤ ς * e * δ₁ ^ j / j ! / 2 ∨
        ς * e * δ₁ ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ d) ∧
      (δ₁ < δ → 2 * δ₁ ≤ δ ∧
        (∃ d', ‖d'‖ ≤ 2 * δ₁ ∧ ς * e * (2 * δ₁) ^ j / j ! / 2 < D.taylorDecrement j d' ∧
          regularizedModel D p σ 0 - regularizedModel D p σ d' < ς * e * (2 * δ₁) ^ j / j ! / 4) ∧
        ∃ d₀, ‖d₀‖ ≤ δ ∧ ς * e * δ ^ j / j ! / 2 < D.taylorDecrement j d₀) ∧
      ∃ m : ℕ, δ₁ = δ / 2 ^ m := by
  set r : ℕ → ℝ := fun m => δ / 2 ^ m with hr
  have hr0 : ∀ m, 0 < r m := fun m => by positivity
  have hrle : ∀ m, r m ≤ δ := fun m => div_le_self hδ.le (one_le_pow₀ one_le_two)
  have hrsucc : ∀ m, 2 * r (m + 1) = r m := fun m => by simp only [hr, pow_succ]; field_simp
  choose d hd using fun m => exists_isApproxMeasureStep_taylorDecrement D j isClosed_univ
    (mem_univ 0) (hr0 m).le hς1
  set M := max Lb σ
  have hM : 0 < M := lt_max_of_lt_left hLb
  have hex : ∃ m, D.taylorDecrement j (d m) ≤ ς * e * r m ^ j / j ! / 2 ∨
      ς * e * r m ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ (d m) := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (δ / (ς * e / (8 * M))) one_lt_two
    refine ⟨m, ?_⟩
    by_cases hpass : D.taylorDecrement j (d m) ≤ ς * e * r m ^ j / j ! / 2
    · exact Or.inl hpass
    right
    have hrm : r m ≤ ς * e / (8 * M) := by
      rw [div_lt_iff₀ (by positivity)] at hm
      simp only [hr]
      rw [div_le_iff₀ (by positivity)]
      linarith
    have key := regularizedModel_decrease_ge_of_taylorDecrement_ge (D := D) (p := p) (σ := σ)
      (L := Lb) hjp hσ
      (fun ℓ hℓ => hD ℓ (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega,
        (Finset.mem_Icc.1 hℓ).2⟩))
      (α := ς * e / 2) (hr0 m).le ((hrle m).trans hδ1) (by
        rw [le_div_iff₀ (by positivity)] at hrm; nlinarith) (hd m).norm_le
      (by
        have : ς * e / 2 * r m ^ j / j ! = ς * e * r m ^ j / j ! / 2 := by ring
        rw [this]; exact (not_le.1 hpass).le)
    have : ς * e / 2 / 2 * r m ^ j / j ! = ς * e * r m ^ j / j ! / 4 := by ring
    rwa [this] at key
  set m := Nat.find hex
  refine ⟨r m, d m, hr0 m, hrle m, hd m, Nat.find_spec hex, fun hlt => ?_, m, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0] at hlt; simp [hr] at hlt
    · omega
  have hmin : ∀ i < m, ¬ (D.taylorDecrement j (d i) ≤ ς * e * r i ^ j / j ! / 2 ∨
      ς * e * r i ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ (d i)) :=
    fun i hi => Nat.find_min hex hi
  have h2 : 2 * r m = r m' := by rw [hm']; exact hrsucc m'
  rw [h2]
  have hm'lt : m' < m := by omega
  push Not at hmin
  obtain ⟨hp', ht'⟩ := hmin m' hm'lt
  obtain ⟨hp0, -⟩ := hmin 0 (by omega)
  exact ⟨hrle m', ⟨d m', (hd m').norm_le, hp', ht'⟩, d 0, (hd 0).norm_le.trans (by simp [hr]),
    by simpa [hr] using hp0⟩

/-- The data of one ARqpIDA iteration: the iterate, the weight, the three families of radii, the
accuracies, the Step-1 displacements, the order $j_k$, the step and the accuracy-improving flag. -/
private structure ARState (E : Type*) where
  x : E
  σ : ℝ
  δ : ℕ → ℝ
  δ₁ : ℕ → ℝ
  δs : ℕ → ℝ
  h : ℕ → ℝ
  dd : ℕ → E
  jk : ℕ
  s : E
  acc : Prop

variable (P : ARqpIDAParams) (ε : ℕ → ℝ) (O : E → (ℕ → ℝ) → FormalMultilinearSeries ℝ E ℝ)
  (Lb : ℝ)

/-- The test (13.1.53) at order $j$ for a state, with the derivative data given by the oracle. -/
private def arqpDAPassS (a : ARState E) (j : ℕ) : Prop :=
  (O a.x a.h).taylorDecrement j (a.dd j) ≤ P.ς * ε j * a.δ₁ j ^ j / j ! / 2

/-- Step 2 of ARqpIDA for a state, as in `Optimization.ARqpStep2` on $E$ with the derivative data
given by the oracle. -/
private structure ARStep2S (a : ARState E) : Prop where
  /-- The order $j_k$ lies in $[1, q]$. -/
  jk_mem : a.jk ∈ Finset.Icc 1 P.q
  /-- The test (13.1.53) fails at the order $j_k$. -/
  not_pass : ¬ arqpDAPassS P ε O a a.jk
  /-- The test (13.1.53) holds at every order $j \in [1, q]$ with $j < j_k$. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < a.jk → arqpDAPassS P ε O a j
  /-- The radii above $j_k$ are not changed in Step 1. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, a.jk < j → a.δ₁ j = a.δ j
  /-- The condition (13.1.54) holds at $j_k$. -/
  model_dec : P.ς * ε a.jk * a.δ₁ a.jk ^ a.jk / a.jk ! / 4 ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ (a.dd a.jk)
  /-- The condition (13.1.55): the step decreases the model at least as much as $d_{k,j_k}$. -/
  dec_le : regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ
      (a.dd a.jk) ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ a.s
  /-- Either (13.1.56) for a long step or (13.1.57) holds. -/
  radii : (1 ≤ ‖a.s‖ ∧ a.δs = a.δ₁) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, a.δs ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ)
        (a.δs ℓ) {e | a.x + a.s + e ∈ (univ : Set E)} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * a.δs ℓ ^ ℓ / ℓ !
  /-- The state is accuracy-improving if and only if the step is short and the accuracy test
  (13.1.46) fails for some $i \in [1, p]$. -/
  acc_iff : a.acc ↔ ‖a.s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖a.s‖ ^ (P.p - i + 1) < a.h i

/-- Steps 1 and 2 of ARqpIDA for a state, the invariants of a run, and the radii control in the form
of `Optimization.RadiiControl.of_unit_le_two`. -/
private structure ARLocal (a : ARState E) : Prop where
  /-- The weight satisfies $\sigma \ge \sigma_{\min}$. -/
  σ_ge : P.σmin ≤ a.σ
  /-- The radii $\delta^{(0)}_j$ lie in $(0, 1]$ for $j \in [1, q]$. -/
  δ_mem : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ j ∧ a.δ j ≤ 1
  /-- The accuracies lie in $(0, \kappa_h]$ for $i \in [1, p]$. -/
  accuracy_mem : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.h i ∧ a.h i ≤ P.κh
  /-- The radii $\delta^{(1)}_j$ are positive for $j \in [1, q]$. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ₁ j
  /-- The radii satisfy $\delta^{(1)}_j \le \delta^{(0)}_j$ for $j \in [1, q]$. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j ≤ a.δ j
  /-- The halving loop of Step 1, as in `Optimization.ARqpStep1`. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j < a.δ j → 2 * a.δ₁ j ≤ a.δ j ∧
    (∃ d', ‖d'‖ ≤ 2 * a.δ₁ j ∧ a.x + d' ∈ (univ : Set E) ∧
      P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d' ∧
      regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ d' <
        P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ a.δ j ∧ a.x + d₀ ∈ (univ : Set E) ∧
      P.ς * ε j * a.δ j ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d₀
  /-- The radii $\delta^{(1)}_j$ come from halving $\delta^{(0)}_j$. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, a.δ₁ j = a.δ j / 2 ^ m
  /-- The Step-1 displacements satisfy (13.1.52). -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((O a.x a.h).taylorDecrement j)
    (a.δ₁ j) {e | a.x + e ∈ (univ : Set E)} P.ς (a.dd j)
  /-- If the test (13.1.53) holds at every order, the state is accuracy-improving. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arqpDAPassS P ε O a j) → a.acc
  /-- If the test (13.1.53) fails at some order, Step 2 holds. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPassS P ε O a j) → ARStep2S P ε O a
  /-- After a trial iteration with a short step, the radii of Step 2 are $1$ at the orders
  $j \le \min\{2, q\}$ and at least $\varsigma\theta\varepsilon_j/(24\max\{\overline{L},
  \sigma\})$ at the orders $j \in [3, q]$. -/
  rc : ¬ a.acc → ‖a.s‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), a.δs j = 1) ∧
    ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb a.σ) ≤ a.δs j

/-- Steps 1 and 2 of ARqpIDA, with the radii control (13.1.69)–(13.1.70), can be performed at every
state that satisfies the invariants, when $\varepsilon \in (0, 1]^q$, $\overline{L} \ge 1$ and
the oracle data are bounded by $\overline{L}$. -/
private theorem exists_arLocal (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb1 : 1 ≤ Lb)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb)
    (x : E) {σ : ℝ} (hσ : P.σmin ≤ σ) {δ h : ℕ → ℝ}
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ j ∧ δ j ≤ 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.κh) :
    ∃ δ₁ δs dd jk s, ∃ acc : Prop, ARLocal P ε O Lb ⟨x, σ, δ, δ₁, δs, h, dd, jk, s, acc⟩ := by
  classical
  have hLb : 0 < Lb := zero_lt_one.trans_le hLb1
  set D := O x h
  have hD := hO x h hh
  have hσ0 : 0 < σ := P.σmin_pos.trans_le hσ
  have H : ∀ j ∈ Finset.Icc 1 P.q, ∃ δ₁ d, 0 < δ₁ ∧ δ₁ ≤ δ j ∧
      IsApproxMeasureStep (D.taylorDecrement j) δ₁ univ P.ς d ∧
      (D.taylorDecrement j d ≤ P.ς * ε j * δ₁ ^ j / j ! / 2 ∨
        P.ς * ε j * δ₁ ^ j / j ! / 4 ≤ regularizedModel D P.p σ 0 - regularizedModel D P.p σ d) ∧
      (δ₁ < δ j → 2 * δ₁ ≤ δ j ∧
        (∃ d', ‖d'‖ ≤ 2 * δ₁ ∧ P.ς * ε j * (2 * δ₁) ^ j / j ! / 2 < D.taylorDecrement j d' ∧
          regularizedModel D P.p σ 0 - regularizedModel D P.p σ d' <
            P.ς * ε j * (2 * δ₁) ^ j / j ! / 4) ∧
        ∃ d₀, ‖d₀‖ ≤ δ j ∧ P.ς * ε j * δ j ^ j / j ! / 2 < D.taylorDecrement j d₀) ∧
      ∃ m : ℕ, δ₁ = δ j / 2 ^ m :=
    fun j hj => exists_arqpDA_halving hσ0.le hLb hD ((Finset.mem_Icc.1 hj).2.trans P.q_le_p) P.ς_pos
      P.ς_le_one (hε j hj).1 (hδ j hj).1 (hδ j hj).2
  choose! δ₁h ddh hH using H
  have H0 : ∀ j ∈ Finset.Icc 1 P.q, ∃ d, IsApproxMeasureStep (D.taylorDecrement j) (δ j) univ
      P.ς d := fun j hj => exists_isApproxMeasureStep_taylorDecrement D j isClosed_univ
        (mem_univ 0) (hδ j hj).1.le P.ς_le_one
  choose! d0 hd0 using H0
  by_cases hex : ∃ j, j ∈ Finset.Icc 1 P.q ∧
      ¬ D.taylorDecrement j (ddh j) ≤ P.ς * ε j * δ₁h j ^ j / j ! / 2
  · set jk := Nat.find hex
    obtain ⟨hjk, hfjk⟩ := Nat.find_spec hex
    have hjkmin : ∀ j ∈ Finset.Icc 1 P.q, j < jk →
        D.taylorDecrement j (ddh j) ≤ P.ς * ε j * δ₁h j ^ j / j ! / 2 := fun j hj hlt => by
      by_contra hc; exact Nat.find_min hex hlt ⟨hj, hc⟩
    set δ₁ : ℕ → ℝ := fun j => if jk < j then δ j else δ₁h j
    set dd : ℕ → E := fun j => if jk < j then d0 j else ddh j
    have hp : 1 ≤ P.p := P.one_le_p
    obtain ⟨s, δs0, dm, hmin, hδs0, hδs2, hδs3, hbr⟩ := exists_highOrderStep (D := D)
      (p := P.p) (q := P.q) (σ := σ) (L := Lb) hp P.q_le_p hσ0 hLb.le
      (fun i hi => hD i (Finset.Icc_subset_Icc (by norm_num) le_rfl hi)) P.θ_pos P.ς_pos
      P.ς_le_one fun j hj => (hε j hj).1
    set δs : ℕ → ℝ := if 1 ≤ ‖s‖ then δ₁ else δs0
    refine ⟨δ₁, δs, dd, jk, s, ‖s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s‖ ^ (P.p - i + 1) < h i,
      ⟨hσ, hδ, hh, fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_,
        fun j hj => ?_, fun hpass => ?_, fun _ => ?_, fun _ hs1 => ?_⟩⟩
    · dsimp only; simp only [δ₁]; split_ifs
      · exact (hδ j hj).1
      · exact (hH j hj).1
    · dsimp only; simp only [δ₁]; split_ifs
      · exact le_rfl
      · exact (hH j hj).2.1
    · dsimp only at hlt ⊢
      simp only [δ₁] at hlt ⊢
      split_ifs at hlt ⊢ with hj'
      · exact absurd hlt (lt_irrefl _)
      · obtain ⟨h1, ⟨d', hd'n, hd'T, hd'm⟩, d₀, hd₀n, hd₀⟩ := (hH j hj).2.2.2.2.1 hlt
        exact ⟨h1, ⟨d', hd'n, mem_univ _, hd'T, hd'm⟩, d₀, hd₀n, mem_univ _, hd₀⟩
    · dsimp only; simp only [δ₁]; split_ifs
      · exact ⟨0, by rw [pow_zero, div_one]⟩
      · exact (hH j hj).2.2.2.2.2
    · dsimp only
      rw [Set.setOf_add_mem_univ]
      simp only [δ₁, dd]; split_ifs
      · exact hd0 j hj
      · exact (hH j hj).2.2.1
    · exfalso
      have := hpass jk hjk
      simp only [arqpDAPassS, δ₁, dd, lt_irrefl, ite_false] at this
      exact hfjk this
    · have hpass_jk : ¬ arqpDAPassS P ε O ⟨x, σ, δ, δ₁, δs, h, dd, jk, s,
          ‖s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s‖ ^ (P.p - i + 1) < h i⟩ jk := by
        simp only [arqpDAPassS, δ₁, dd, lt_irrefl, ite_false]; exact hfjk
      have hdec : P.ς * ε jk * δ₁h jk ^ jk / jk ! / 4 ≤
          regularizedModel D P.p σ 0 - regularizedModel D P.p σ (ddh jk) :=
        (hH jk hjk).2.2.2.1.resolve_left hfjk
      have hminv := isMinOn_iff.1 hmin (ddh jk) (mem_univ _)
      refine ⟨hjk, hpass_jk, fun j hj hlt => ?_, fun j hj hlt => ?_, ?_, ?_, ?_, Iff.rfl⟩
      · dsimp only at hlt
        have hlt' : ¬ jk < j := by omega
        simp only [arqpDAPassS, δ₁, dd, hlt', ite_false]; exact hjkmin j hj hlt
      · dsimp only at hlt ⊢; simp only [δ₁, hlt, ite_true]
      · dsimp only; simp only [δ₁, dd, lt_irrefl, ite_false]; exact hdec
      · dsimp only; simp only [dd, lt_irrefl, ite_false]
        linarith
      · dsimp only
        by_cases hs1 : 1 ≤ ‖s‖
        · left; exact ⟨hs1, by simp only [δs, hs1, ite_true]⟩
        · right
          intro ℓ hℓ
          have hδsℓ : δs ℓ = δs0 ℓ := by simp only [δs, hs1, ite_false]
          rw [hδsℓ]
          obtain ⟨happ, hle⟩ := (hbr.resolve_left hs1) ℓ hℓ
          refine ⟨⟨(hδs0 ℓ hℓ).1, (hδs0 ℓ hℓ).2⟩, dm ℓ, ?_, hle⟩
          have : {e | x + s + e ∈ (univ : Set E)} = univ := by ext; simp
          rw [this]; exact happ
    · dsimp only at hs1 ⊢
      have hs1' : ¬ 1 ≤ ‖s‖ := not_le.2 hs1
      have hδsℓ : ∀ ℓ, δs ℓ = δs0 ℓ := fun ℓ => by simp only [δs, hs1', ite_false]
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
        rw [hδsℓ]
        exact hδs2 j (Finset.mem_Icc.2 ⟨hj1, hj2.trans (min_le_right _ _)⟩)
          (hj2.trans (min_le_left _ _))
      · rw [hδsℓ, hδs3 j hj]
        have hεj := hε j (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
          (Finset.mem_Icc.1 hj).2⟩)
        have hM : 1 ≤ max Lb σ := hLb1.trans (le_max_left _ _)
        have hς := P.ς_pos; have hς1 := P.ς_le_one; have hθ := P.θ_pos; have hθ1 := P.θ_lt_one
        have h1 : P.ς * P.θ * ε j / (24 * max Lb σ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : P.ς * P.θ * ε j ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul hς1 hθ1.le hθ.le zero_le_one) hεj.2 hεj.1.le (by norm_num)
          linarith
        refine le_min h1 ?_
        refine div_le_div_of_nonneg_left (by have := hεj.1; positivity) (by positivity) ?_
        have := le_max_left Lb σ; have := le_max_right Lb σ
        linarith
  · push Not at hex
    refine ⟨δ₁h, fun _ => 1, ddh, 1, 0, True, ⟨hσ, hδ, hh, fun j hj => (hH j hj).1,
      fun j hj => (hH j hj).2.1, fun j hj hlt => ?_, fun j hj => (hH j hj).2.2.2.2.2,
      fun j hj => ?_, fun _ => trivial,
      fun ⟨j, hj, hf⟩ => absurd (hex j hj) hf, fun h' => absurd trivial h'⟩⟩
    · dsimp only at hlt ⊢
      obtain ⟨h1, ⟨d', hd'n, hd'T, hd'm⟩, d₀, hd₀n, hd₀⟩ := (hH j hj).2.2.2.2.1 hlt
      exact ⟨h1, ⟨d', hd'n, mem_univ _, hd'T, hd'm⟩, d₀, hd₀n, mem_univ _, hd₀⟩
    · dsimp only; rw [Set.setOf_add_mem_univ]; exact (hH j hj).2.2.1

/-- From a state that satisfies Steps 1 and 2 there is a next state that satisfies them, such that
the transition is an ARqpIDA iteration on $E$ that satisfies `Optimization.RadiiControl`. -/
private theorem exists_arNext (f : E → ℝ) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hLb1 : 1 ≤ Lb)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb)
    (a : ARState E) (ha : ARLocal P ε O Lb a) :
    ∃ b : ARState E, ARLocal P ε O Lb b ∧ ∀ (r : ℕ → ARState E) (k : ℕ), r k = a →
      r (k + 1) = b →
      ARqpDAStep univ P ε (fun i => (r i).x) (fun i => (r i).σ) (fun i => (r i).δ)
        (fun i => (r i).δ₁) (fun i => (r i).δs) (fun i => (r i).h) (fun i => O (r i).x (r i).h)
        (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s) (fun i => (r i).acc)
        (arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)) k ∧
      RadiiControl P ε Lb (fun i => (r i).σ) (fun i => (r i).δs) (fun i => (r i).s)
        (fun i => (r i).acc) k := by
  classical
  set ρ := reductionRatio f a.x a.s ((O a.x a.h).taylorDecrement P.p a.s) with hρ
  set x' := if a.acc then a.x else if P.η₁ ≤ ρ then a.x + a.s else a.x
  set σ' := if a.acc then a.σ else if P.η₁ ≤ ρ then a.σ else P.γ₂ * a.σ
  set δ' := if a.acc then a.δ else if P.η₁ ≤ ρ ∧ ‖a.s‖ < 1 then a.δs else a.δ₁
  set h' : ℕ → ℝ := if a.acc then fun i => P.γh * a.h i else a.h
  have hσpos : 0 < a.σ := P.σmin_pos.trans_le ha.σ_ge
  have hstep2 : ¬ a.acc → ARStep2S P ε O a := fun hk => ha.step2 (by
    by_contra hc; push Not at hc; exact hk (ha.acc_of_pass hc))
  have hσ' : P.σmin ≤ σ' := by
    simp only [σ']; split_ifs
    · exact ha.σ_ge
    · exact ha.σ_ge
    · exact ha.σ_ge.trans (le_mul_of_one_le_left hσpos.le P.one_le_γ₂)
  have hδ' : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ' j ∧ δ' j ≤ 1 := by
    intro j hj
    simp only [δ']; split_ifs with h1 h2
    · exact ha.δ_mem j hj
    · exact ((hstep2 h1).radii.resolve_left (fun h' => absurd h'.1 (not_le.2 h2.2)) j hj).1
    · exact ⟨ha.radius_pos j hj, (ha.radius_le j hj).trans (ha.δ_mem j hj).2⟩
  have hh' : ∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh := by
    intro i hi
    simp only [h']; split_ifs
    · obtain ⟨h1, h2⟩ := ha.accuracy_mem i hi
      exact ⟨mul_pos P.γh_pos h1, (mul_le_of_le_one_left h1.le P.γh_lt_one.le).trans h2⟩
    · exact ha.accuracy_mem i hi
  obtain ⟨δ₁', δs', dd', jk', s', acc', hloc⟩ :=
    exists_arLocal P ε O Lb hε hLb1 hO x' hσ' hδ' hh'
  refine ⟨⟨x', σ', δ', δ₁', δs', h', dd', jk', s', acc'⟩, hloc, fun r k hra hrb => ?_⟩
  have hpass : ∀ j, arqpDAPass P ε (fun i => O (r i).x (r i).h) (fun i => (r i).δ₁)
      (fun i => (r i).dd) k j ↔ arqpDAPassS P ε O a j := by
    intro j; simp only [arqpDAPass, arqpDAPassS, hra]
  have hratio : arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x)
      (fun i => (r i).s) k = ρ := by simp only [arqpIDARatio, hra, hρ]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [hra]; exact ha.radius_pos
  · simp only [hra]; exact ha.radius_le
  · simp only [arModelDec, hra]; exact ha.halving
  · simp only [hra]; exact ha.dyadic
  · simp only [hra]; exact ha.witness
  · intro hp; simp only [hra]; exact ha.acc_of_pass fun j hj => (hpass j).1 (hp j hj)
  · rintro ⟨j, hj, hf⟩
    have h2 := ha.step2 ⟨j, hj, (hpass j).not.1 hf⟩
    refine ⟨?_, ?_, fun j hj hlt => ?_, fun j hj hlt => ?_, ?_, by simp, ?_, ?_, ?_⟩
    · simp only [hra]; exact h2.jk_mem
    · simp only [hra] at hpass ⊢; exact (hpass _).not.2 h2.not_pass
    · simp only [hra] at hlt; exact (hpass j).2 (h2.pass_lt j hj hlt)
    · simp only [hra] at hlt ⊢; exact h2.radius_gt j hj hlt
    · simp only [arModelDec, hra]; exact h2.model_dec
    · simp only [arModelDec, hra]; exact h2.dec_le
    · simp only [hra]; exact h2.radii
    · simp only [hra]; exact h2.acc_iff
  · intro hk
    simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, x', σ', hk, ite_false]
    refine ⟨rfl, ⟨fun h2 => ?_, fun h1 _ => ?_, fun h1 => ?_⟩⟩
    · rw [ite_eq_left (P.η₁_le_η₂.trans h2)]
      exact ⟨max_le ha.σ_ge (mul_le_of_le_one_left hσpos.le P.γ₁_le_one), le_rfl⟩
    · rw [ite_eq_left h1]
      exact ⟨le_rfl, le_mul_of_one_le_left hσpos.le P.one_le_γ₂⟩
    · rw [ite_eq_right (not_le.2 h1)]
      exact ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσpos.le⟩
  · intro hk
    simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, δ', hk, ite_false]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_false]
  · intro hk hlt; simp only [hra] at hk; rw [hratio] at hlt
    simp only [hra, hrb, x', h', hk, ite_false, ite_eq_right (not_le.2 hlt)]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, x', hk, ite_true]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, δ', hk, ite_true]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, σ', hk, ite_true]
  · intro hk i; simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_true]
  · exact RadiiControl.of_unit_le_two hε hLb1 fun hk hs1 => by
      simp only [hra] at hk hs1 ⊢; exact ha.rc hk hs1

variable {P ε}

/-- ARqpIDA iterations exist from every admissible state. Let $E$ be finite-dimensional, and assume
the smoothness hypothesis `LipschitzDerivsAnchored f univ univ 0 p L` with $L_j \ge 1$. Let
$\varepsilon_j \in (0, 1]$ for $j \in [1, q]$ and $\kappa_{\nabla,i} \ge 0$ for $i \in [1, p]$,
and let $O$ be a deterministic oracle that satisfies the error model (13.1.2), $\|O(y, h)_i -
\nabla^i f(y)\| \le \kappa_{\nabla,i} h_i$ for $i \in [1, p]$, at every point $y$ and for all
accuracies $h \in (0, \kappa_h]^p$. Let a starting state be given: a point $x_0$, a weight
$\sigma' \ge \sigma_{\min}$, radii $\delta' \in (0, 1]^q$ and accuracies
$h' \in (0, \kappa_h]^p$. Then there are sequences, starting at this state, with
$h_k \in (0, \kappa_h]^p$ for every $k$, such that every iteration is an ARqpIDA iteration
(`Optimization.ARqpDAStep` on $E$, with the derivative data $D_k = O(x_k, h_k)$ and the ratio
(13.1.58)) and satisfies the radii control `Optimization.RadiiControl` with $\overline{L} =
L_f + \kappa_{\nabla,\max}\kappa_h$. This is the existence part of Lemmas 13.1.11 and 13.1.12 of
[cartis2022evaluation].

The initial state of $P$ gives runs of ARqpIDA. Other starting states allow a run to continue
from any of its iterates. Step 2 uses a global minimizer of the regularized model. -/
theorem exists_arqpDA_steps {f : E → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : LipschitzDerivsAnchored f univ univ 0 P.p L)
    (hL : ∀ j ≤ P.p, 1 ≤ L j) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i) (x₀ : E) {σ' : ℝ} (hσ' : P.σmin ≤ σ')
    {δ' h' : ℕ → ℝ} (hδ' : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ' j ∧ δ' j ≤ 1)
    (hh' : ∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => κg i * h' i)) :
    ∃ (x : ℕ → E) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → E)
      (jk : ℕ → ℕ) (s : ℕ → E) (acc : ℕ → Prop),
      x 0 = x₀ ∧ σ 0 = σ' ∧ δ 0 = δ' ∧ h 0 = h' ∧
        (∀ k, ∀ i ∈ Finset.Icc 1 P.p, 0 < h k i ∧ h k i ≤ P.κh) ∧
        (∀ k, ARqpDAStep univ P ε x σ δ δ₁ δs h (fun i => O (x i) (h i)) dd jk s acc
          (arqpIDARatio f P (fun i => O (x i) (h i)) x s) k) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb1 : 1 ≤ Lb := by
    have := one_le_lipMax hL; have := ordMax_nonneg hκg; have := P.κh_nonneg; nlinarith
  have hO' : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb := fun y h' hh ℓ hℓ =>
    hf.norm_le_of_jetApprox hL (mem_univ y) (hO y h' hh) hκg (fun i hi => (hh i hi).1.le)
      (fun i hi => (hh i hi).2) hℓ
  obtain ⟨δ₁₀, δs₀, dd₀, jk₀, s₀, acc₀, h₀⟩ := exists_arLocal P ε O Lb hε hLb1 hO' x₀
    hσ' hδ' hh'
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant (α := ARState E)
    (init := fun a => a = ⟨x₀, σ', δ', δ₁₀, δs₀, h', dd₀, jk₀, s₀, acc₀⟩)
    (inv := fun _ a => ARLocal P ε O Lb a) (stop := fun _ _ => False)
    (step := fun k a b => ∀ (r : ℕ → ARState E), r k = a → r (k + 1) = b →
      ARqpDAStep univ P ε (fun i => (r i).x) (fun i => (r i).σ) (fun i => (r i).δ)
        (fun i => (r i).δ₁) (fun i => (r i).δs) (fun i => (r i).h) (fun i => O (r i).x (r i).h)
        (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s) (fun i => (r i).acc)
        (arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)) k ∧
      RadiiControl P ε Lb (fun i => (r i).σ) (fun i => (r i).δs) (fun i => (r i).s)
        (fun i => (r i).acc) k)
    ⟨_, rfl⟩ (fun a ha => ha ▸ h₀) (fun k a ha _ => by
      obtain ⟨b, hb, hs⟩ := exists_arNext P ε O Lb f hε hLb1 hO' a ha
      exact ⟨b, hb, fun r => hs r k⟩)
  exact ⟨fun i => (r i).x, fun i => (r i).σ, fun i => (r i).δ, fun i => (r i).δ₁,
    fun i => (r i).δs, fun i => (r i).h, fun i => (r i).dd, fun i => (r i).jk, fun i => (r i).s,
    fun i => (r i).acc, by simp only [hr0], by simp only [hr0], by simp only [hr0],
    by simp only [hr0], fun k => (hr k fun _ _ h => h).1.accuracy_mem,
    fun k => ((hr k fun _ _ h => h).2 r rfl rfl).1, fun k => ((hr k fun _ _ h => h).2 r rfl rfl).2⟩

end ARExistence

end Optimization
