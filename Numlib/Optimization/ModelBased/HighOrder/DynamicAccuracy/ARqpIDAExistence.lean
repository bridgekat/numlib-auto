import Numlib.Optimization.Complexity.Existence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDA

/-!
# Existence of ARqpIDA runs

In finite dimension, ARqpIDA iterations ([cartis2022evaluation], Algorithm 13.1.2) exist from
every admissible state, for every deterministic oracle satisfying the error model (13.1.2):

* `exists_arqpDA_halving`: the halving loop of Step 1 terminates (existence half of
  Lemma 13.1.11);
* `exists_arqpDA_steps`: sequences all of whose iterations are ARqpIDA steps on the whole space
  satisfying the radii control (Step 2 uses a global minimizer of the regularized model).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Existence of ARqpIDA runs -/

section ARExistence

variable [FiniteDimensional ℝ E]

open Classical in
/-- **The halving loop of Step 1 of ARqpIDA terminates** ([cartis2022evaluation], Lemma 13.1.11,
existence half): for inexact derivatives with `‖D_ℓ‖ ≤ L̄` (`ℓ ∈ [1, p]`), `σ ≥ 0`, `ε_j > 0`
and a radius `δ ∈ (0, 1]`, halving `δ` while (13.1.53) and (13.1.54) both fail stops at a radius
`δ₁ ∈ (0, δ]` with a displacement `d` satisfying (13.1.52) and (13.1.53) or (13.1.54), and if
`δ₁ < δ` with the witnesses of the last and of the first halving. -/
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

/-- The data of one ARqpIDA iteration. -/
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

/-- The Step-1.2 test (13.1.53) of a state. -/
private def arPassS (a : ARState E) (j : ℕ) : Prop :=
  (O a.x a.h).taylorDecrement j (a.dd j) ≤ P.ς * ε j * a.δ₁ j ^ j / j ! / 2

/-- Step 2 of a state. -/
private structure ARStep2S (a : ARState E) : Prop where
  /-- See `ARqpStep2`. -/
  jk_mem : a.jk ∈ Finset.Icc 1 P.q
  /-- See `ARqpStep2`. -/
  not_pass : ¬ arPassS P ε O a a.jk
  /-- See `ARqpStep2`. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < a.jk → arPassS P ε O a j
  /-- See `ARqpStep2`. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, a.jk < j → a.δ₁ j = a.δ j
  /-- See `ARqpStep2`. -/
  model_dec : P.ς * ε a.jk * a.δ₁ a.jk ^ a.jk / a.jk ! / 4 ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ (a.dd a.jk)
  /-- See `ARqpStep2`. -/
  dec_le : regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ
      (a.dd a.jk) ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ a.s
  /-- See `ARqpStep2`. -/
  radii : (1 ≤ ‖a.s‖ ∧ a.δs = a.δ₁) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, a.δs ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ)
        (a.δs ℓ) {e | a.x + a.s + e ∈ (univ : Set E)} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * a.δs ℓ ^ ℓ / ℓ !
  /-- See `ARqpStep2`. -/
  acc_iff : a.acc ↔ ‖a.s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖a.s‖ ^ (P.p - i + 1) < a.h i

/-- Steps 1–2 of a state, the invariants and the radii control. -/
private structure ARLocal (a : ARState E) : Prop where
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  σ_ge : P.σmin ≤ a.σ
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  δ_mem : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ j ∧ a.δ j ≤ 1
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  accuracy_mem : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.h i ∧ a.h i ≤ P.κh
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ₁ j
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j ≤ a.δ j
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j < a.δ j → 2 * a.δ₁ j ≤ a.δ j ∧
    (∃ d', ‖d'‖ ≤ 2 * a.δ₁ j ∧ a.x + d' ∈ (univ : Set E) ∧
      P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d' ∧
      regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ d' <
        P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ a.δ j ∧ a.x + d₀ ∈ (univ : Set E) ∧
      P.ς * ε j * a.δ j ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d₀
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, a.δ₁ j = a.δ j / 2 ^ m
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((O a.x a.h).taylorDecrement j)
    (a.δ₁ j) {e | a.x + e ∈ (univ : Set E)} P.ς (a.dd j)
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arPassS P ε O a j) → a.acc
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arPassS P ε O a j) → ARStep2S P ε O a
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  rc : ¬ a.acc → ‖a.s‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), a.δs j = 1) ∧
    ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb a.σ) ≤ a.δs j

/-- Steps 1–2 of ARqpIDA can be performed at every state satisfying the invariants, with the
radii control (13.1.69)–(13.1.70). -/
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
      simp only [arPassS, δ₁, dd, lt_irrefl, ite_false] at this
      exact hfjk this
    · have hpass_jk : ¬ arPassS P ε O ⟨x, σ, δ, δ₁, δs, h, dd, jk, s,
          ‖s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s‖ ^ (P.p - i + 1) < h i⟩ jk := by
        simp only [arPassS, δ₁, dd, lt_irrefl, ite_false]; exact hfjk
      have hdec : P.ς * ε jk * δ₁h jk ^ jk / jk ! / 4 ≤
          regularizedModel D P.p σ 0 - regularizedModel D P.p σ (ddh jk) :=
        (hH jk hjk).2.2.2.1.resolve_left hfjk
      have hminv := isMinOn_iff.1 hmin (ddh jk) (mem_univ _)
      refine ⟨hjk, hpass_jk, fun j hj hlt => ?_, fun j hj hlt => ?_, ?_, ?_, ?_, Iff.rfl⟩
      · dsimp only at hlt
        have hlt' : ¬ jk < j := by omega
        simp only [arPassS, δ₁, dd, hlt', ite_false]; exact hjkmin j hj hlt
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

/-- The transition of an ARqpIDA run from a state satisfying Steps 1–2. -/
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
  have hpass : ∀ j, arPass P ε (fun i => O (r i).x (r i).h) (fun i => (r i).δ₁)
      (fun i => (r i).dd) k j ↔ arPassS P ε O a j := by
    intro j; simp only [arPass, arPassS, hra]
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

/-- **ARqpIDA iterations exist from any admissible state** ([cartis2022evaluation], existence part
of Lemmas 13.1.11 and 13.1.12): under the smoothness hypothesis, for tolerances `ε ∈ (0, 1]^q`,
oracle constants `κ_{∇,i} ≥ 0`, every deterministic oracle `O` satisfying (13.1.2) for all
accuracies `h ∈ (0, κ_h]^p`, and a starting state (`x₀`, a weight `σ' ≥ σ_min`, radii `δ' ∈ (0,
1]^q`, accuracies `h' ∈ (0, κ_h]^p`), there are sequences starting at that state all of whose
iterations are ARqpIDA steps (`ARqpDAStep` on `X = univ`, with `D_k = O(x_k, h_k)`) satisfying
the radii control (13.1.69)–(13.1.70). The initial state of `P` gives runs of ARqpIDA; other
states allow continuing a run from any of its iterates. -/
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
