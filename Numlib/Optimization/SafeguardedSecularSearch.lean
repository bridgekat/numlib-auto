import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Safeguarded interval search with geometric and affine trial points

A trichotomy classifies trials below the regular domain, on its desired lower side, or
above the root. The search retains actual bounds and nondeterministic legal safeguarded
choices. Bounds and contraction follow from its update equations, rather than being
included as conclusions in a run specification.
-/

noncomputable section
namespace Optimization.SafeguardedSecularSearch

/-- The three outcomes of a secular trial. -/
inductive Region where
  /-- The shifted problem is outside its strictly regular domain. -/
  | negative
  /-- The regular trial lies on the desired lower side. -/
  | lower
  /-- The regular trial lies above the desired root. -/
  | greater
  deriving DecidableEq

/-- Uniform affine safeguards, strictly between the interval endpoints. -/
structure Parameters where
  /-- The smallest permitted affine fraction. -/
  lower : ℝ
  /-- The largest permitted affine fraction. -/
  upper : ℝ
  /-- The affine fraction stays away from zero. -/
  lower_pos : 0 < lower
  /-- The safeguard interval is ordered. -/
  lower_le_upper : lower ≤ upper
  /-- The affine fraction stays away from one. -/
  upper_lt_one : upper < 1

/-- The retained bounds and the current trial point. -/
structure State where
  /-- The retained lower interval endpoint. -/
  lower : ℝ
  /-- The retained upper interval endpoint. -/
  upper : ℝ
  /-- The actual trial classified by the search. -/
  candidate : ℝ

/-- An actual bracketing state, with the trial inside the nonnegative interval. -/
def Brackets (root : ℝ) (s : State) : Prop :=
  0 ≤ s.lower ∧ s.lower ≤ root ∧ root ≤ s.upper ∧
    s.lower ≤ s.candidate ∧ s.candidate ≤ s.upper

/-- The bracketing interface exposes nonnegativity, root enclosure, and trial enclosure. -/
@[simp] theorem brackets_iff (root : ℝ) (s : State) :
    Brackets root s ↔ 0 ≤ s.lower ∧ s.lower ≤ root ∧ root ≤ s.upper ∧
      s.lower ≤ s.candidate ∧ s.candidate ≤ s.upper := Iff.rfl

/-- The geometric or affine safeguarded point, selected by a binary geometric flag. -/
def trial (s : State) (θ : ℝ) (geometric : Bool) : ℝ :=
  max (if geometric then Real.sqrt (s.lower * s.upper) else 0)
    (s.lower + θ * (s.upper - s.lower))

/-- A permitted optional improvement of the lower bound. -/
def improveLower (lower : ℝ) (estimate : Option ℝ) : ℝ :=
  match estimate with
  | none => lower
  | some a => max lower a

/-- Every optional estimate is a certified lower bound on the regular-domain boundary. -/
def EstimateBelow (pole : ℝ) (estimate : Option ℝ) : Prop :=
  ∀ a, estimate = some a → a ≤ pole

/-- The optional estimate cannot lower the existing bound. -/
theorem le_improveLower (lower : ℝ) (estimate : Option ℝ) :
    lower ≤ improveLower lower estimate := by
  cases estimate <;> simp [improveLower]

/-- A shared upper bound on the old lower bound and optional estimate is preserved. -/
theorem improveLower_le {lower pole bound : ℝ} {estimate : Option ℝ}
    (hl : lower ≤ bound) (hp : pole ≤ bound) (he : EstimateBelow pole estimate) :
    improveLower lower estimate ≤ bound := by
  cases estimate with
  | none => exact hl
  | some a => exact max_le hl ((he a rfl).trans hp)

/-- The retained interval after classification, before selecting a new trial. -/
def updateBounds (r : Region) (s : State) (estimate : Option ℝ) : State :=
  { lower := improveLower (if r = .negative then max s.lower s.candidate else s.lower) estimate
    upper := if r = .greater then min s.upper s.candidate else s.upper
    candidate := s.candidate }

/-- The lower endpoint update is exposed without unfolding the state implementation. -/
@[simp] theorem updateBounds_lower (r : Region) (s : State) (estimate : Option ℝ) :
    (updateBounds r s estimate).lower =
      improveLower (if r = .negative then max s.lower s.candidate else s.lower) estimate := rfl

/-- The upper endpoint update is exposed without unfolding the state implementation. -/
@[simp] theorem updateBounds_upper (r : Region) (s : State) (estimate : Option ℝ) :
    (updateBounds r s estimate).upper =
      if r = .greater then min s.upper s.candidate else s.upper := rfl

/-- No optional estimate leaves the lower endpoint unchanged. -/
@[simp] theorem improveLower_none (lower : ℝ) : improveLower lower none = lower := rfl

/-- An optional estimate is combined by taking the maximum. -/
@[simp] theorem improveLower_some (lower a : ℝ) : improveLower lower (some a) = max lower a := rfl

/-- An absent estimate needs no extra cutoff certificate. -/
@[simp] theorem estimateBelow_none (pole : ℝ) : EstimateBelow pole none := by
  intro a ha
  cases ha

/-- A present estimate is valid precisely when it lies below the cutoff. -/
@[simp] theorem estimateBelow_some_iff (pole a : ℝ) : EstimateBelow pole (some a) ↔ a ≤ pole := by
  simp [EstimateBelow]

/-- Disabling the geometric safeguard leaves the affine safeguard and nonnegativity. -/
@[simp] theorem trial_false (s : State) (θ : ℝ) :
    trial s θ false = max 0 (s.lower + θ * (s.upper - s.lower)) := rfl

/-- Enabling the geometric safeguard compares it with the affine safeguard. -/
@[simp] theorem trial_true (s : State) (θ : ℝ) :
    trial s θ true = max (Real.sqrt (s.lower * s.upper))
      (s.lower + θ * (s.upper - s.lower)) := rfl

/-- A legal selection records both affine and binary geometric safeguards. -/
structure Choice where
  /-- The lower affine fraction. -/
  thetaLower : ℝ
  /-- The upper affine fraction. -/
  thetaUpper : ℝ
  /-- Whether the lower candidate safeguard includes the geometric mean. -/
  geometricLower : Bool
  /-- Whether the upper candidate safeguard includes the geometric mean. -/
  geometricUpper : Bool
  /-- An optional new lower bound certified against the domain cutoff. -/
  estimate : Option ℝ

/-- The source safeguards are ordered, and negative-region trials use a single chosen point. -/
def Choice.Legal (p : Parameters) (r : Region) (c : Choice) : Prop :=
  p.lower ≤ c.thetaLower ∧ c.thetaLower ≤ c.thetaUpper ∧ c.thetaUpper ≤ p.upper ∧
    c.geometricLower ≤ c.geometricUpper ∧
    (r = .negative → c.thetaLower = c.thetaUpper ∧ c.geometricLower = c.geometricUpper)

/-- Legal choices are exactly the ordered safeguards and the negative-branch singleton rule. -/
@[simp] theorem Choice.legal_iff (p : Parameters) (r : Region) (c : Choice) :
    c.Legal p r ↔ p.lower ≤ c.thetaLower ∧ c.thetaLower ≤ c.thetaUpper ∧
      c.thetaUpper ≤ p.upper ∧ c.geometricLower ≤ c.geometricUpper ∧
      (r = .negative → c.thetaLower = c.thetaUpper ∧ c.geometricLower = c.geometricUpper) :=
  Iff.rfl

/-- A real classifier's local certificates, with no convergence or complexity assumption. -/
structure ClassifierSpec (classify : ℝ → Region) (pole root : ℝ) : Prop where
  /-- A negative-region trial cannot lie above the negative-region ceiling. -/
  negative_le : ∀ a, 0 ≤ a → classify a = .negative → a ≤ pole
  /-- A lower-region trial cannot lie above the root. -/
  lower_le : ∀ a, 0 ≤ a → classify a = .lower → a ≤ root
  /-- A greater-region trial cannot lie below the root. -/
  greater_ge : ∀ a, 0 ≤ a → classify a = .greater → root ≤ a

/-- Actual initialized search transitions, required only while no lower-side trial was found. -/
structure IsRun (p : Parameters) (classify : ℝ → Region) (pole root : ℝ)
    (s : ℕ → State) (c : ℕ → Choice) : Prop where
  /-- Initialization supplies actual ordered bounds and an enclosed trial. -/
  initial : Brackets root (s 0)
  /-- Every executed choice obeys the source safeguards. -/
  choice : ∀ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) →
    (c k).Legal p (classify (s k).candidate)
  /-- Every executed optional estimate is a certified cutoff lower bound. -/
  estimate : ∀ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) →
    EstimateBelow pole (c k).estimate
  /-- The lower endpoint follows the actual update formula. -/
  lower_update : ∀ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) →
    (s (k + 1)).lower = (updateBounds (classify (s k).candidate) (s k) (c k).estimate).lower
  /-- The upper endpoint follows the actual update formula. -/
  upper_update : ∀ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) →
    (s (k + 1)).upper = (updateBounds (classify (s k).candidate) (s k) (c k).estimate).upper
  /-- The actual next candidate lies in the prescribed safeguarded interval. -/
  candidate_update : ∀ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) →
    let b := updateBounds (classify (s k).candidate) (s k) (c k).estimate
    (s (k + 1)).candidate ∈ Set.Icc (trial b (c k).thetaLower (c k).geometricLower)
      (trial b (c k).thetaUpper (c k).geometricUpper)

/-- Classifiers agreeing on every executed trial define the same operational run. -/
theorem IsRun.congr_trials {p : Parameters} {classify classify' : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (he : ∀ k, classify (s k).candidate = classify' (s k).candidate) :
    IsRun p classify' pole root s c := by
  have hpre (k : ℕ) (hn : ∀ j ≤ k, classify' (s j).candidate ≠ .lower) :
      ∀ j ≤ k, classify (s j).candidate ≠ .lower := by
    intro j hj
    rw [he j]
    exact hn j hj
  refine ⟨h.initial, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hn
    rw [← he k]
    exact h.choice k (hpre k hn)
  · intro k hn
    exact h.estimate k (hpre k hn)
  · intro k hn
    rw [← he k]
    exact h.lower_update k (hpre k hn)
  · intro k hn
    rw [← he k]
    exact h.upper_update k (hpre k hn)
  · intro k hn
    rw [← he k]
    exact h.candidate_update k (hpre k hn)

/-- A safeguarded trial is at least its affine safeguard. -/
theorem affine_le_trial (s : State) (θ : ℝ) (geometric : Bool) :
    s.lower + θ * (s.upper - s.lower) ≤ trial s θ geometric := le_max_right _ _

/-- The geometric mean lies below the arithmetic midpoint for nonnegative bounds. -/
theorem sqrt_mul_le_midpoint {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    Real.sqrt (l * u) ≤ l + (1 / 2 : ℝ) * (u - l) := by
  have hp := Real.sq_sqrt (mul_nonneg hl hu)
  have hs := Real.sqrt_nonneg (l * u)
  nlinarith [sq_nonneg (u - l)]

/-- A trial never exceeds the larger of its affine fraction and one half of the width. -/
theorem trial_le_affine_max {s : State} (hl : 0 ≤ s.lower) (hlu : s.lower ≤ s.upper)
    {θ q : ℝ} (hθ : θ ≤ q) (hq : (1 / 2 : ℝ) ≤ q) (geometric : Bool) :
    trial s θ geometric ≤ s.lower + q * (s.upper - s.lower) := by
  apply max_le
  · split_ifs
    · exact (sqrt_mul_le_midpoint hl (hl.trans hlu)).trans (by nlinarith)
    · nlinarith
  · nlinarith

/-- With safeguards in the unit interval, the actual candidate remains inside its bounds. -/
theorem trial_mem_Icc {s : State} (hl : 0 ≤ s.lower) (hlu : s.lower ≤ s.upper)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (geometric : Bool) :
    trial s θ geometric ∈ Set.Icc s.lower s.upper := by
  refine ⟨(by nlinarith : s.lower ≤ s.lower + θ * (s.upper - s.lower)).trans
    (affine_le_trial _ _ _), ?_⟩
  have h := trial_le_affine_max hl hlu hθ1 (by norm_num : (1 / 2 : ℝ) ≤ 1) geometric
  nlinarith

/-- The interval update preserves its actual nonnegative bracketing bounds. -/
theorem updateBounds_bounds {classify : ℝ → Region} {pole root : ℝ}
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root) {s : State}
    (hs : Brackets root s) {estimate : Option ℝ} (he : EstimateBelow pole estimate) :
    let b := updateBounds (classify s.candidate) s estimate
    0 ≤ b.lower ∧ b.lower ≤ root ∧ root ≤ b.upper := by
  have hcn : 0 ≤ s.candidate := hs.1.trans hs.2.2.2.1
  have hbase : (if classify s.candidate = .negative then max s.lower s.candidate
      else s.lower) ≤ root := by
    split_ifs with hn
    · exact max_le hs.2.1 ((hc.negative_le _ hcn hn).trans hpr)
    · exact hs.2.1
  have hnonneg : 0 ≤ (if classify s.candidate = .negative then max s.lower s.candidate
      else s.lower) := by
    split_ifs
    · exact hs.1.trans (le_max_left _ _)
    · exact hs.1
  refine ⟨hnonneg.trans (le_improveLower _ _), improveLower_le hbase hpr he, ?_⟩
  dsimp [updateBounds]
  split_ifs with hg
  · exact le_min hs.2.2.1 (hc.greater_ge _ hcn hg)
  · exact hs.2.2.1

/-- The lower interval endpoint never decreases during an update. -/
theorem lower_le_updateBounds (r : Region) (s : State) (estimate : Option ℝ) :
    s.lower ≤ (updateBounds r s estimate).lower := by
  apply le_trans (b := if r = .negative then max s.lower s.candidate else s.lower)
  · split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  · exact le_improveLower _ _

/-- A legal search preserves the actual bracket before its first lower-side trial. -/
theorem IsRun.brackets {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root) (k : ℕ)
    (hn : ∀ j < k, classify (s j).candidate ≠ .lower) : Brackets root (s k) := by
  induction k with
  | zero => exact h.initial
  | succ k ih =>
    have hpre : ∀ j ≤ k, classify (s j).candidate ≠ .lower := fun j hj => hn j (by omega)
    have hs := ih (fun j hj => hn j (by omega))
    have hb := updateBounds_bounds hc hpr hs (h.estimate k hpre)
    have hchoice := h.choice k hpre
    have hband := h.candidate_update k hpre
    have hθl : 0 ≤ (c k).thetaLower := p.lower_pos.le.trans hchoice.1
    have hθl1 : (c k).thetaLower ≤ 1 :=
      hchoice.2.1.trans (hchoice.2.2.1.trans p.upper_lt_one.le)
    have hθu : 0 ≤ (c k).thetaUpper := hθl.trans hchoice.2.1
    have hθu1 : (c k).thetaUpper ≤ 1 := hchoice.2.2.1.trans p.upper_lt_one.le
    have hlo := trial_mem_Icc hb.1 (hb.2.1.trans hb.2.2) hθl hθl1 (c k).geometricLower
    have hup := trial_mem_Icc hb.1 (hb.2.1.trans hb.2.2) hθu hθu1 (c k).geometricUpper
    unfold Brackets
    rw [h.lower_update k hpre, h.upper_update k hpre]
    exact ⟨hb.1, hb.2.1, hb.2.2, hlo.1.trans hband.1, hband.2.trans hup.2⟩

/-- The lower bound cannot cross a fixed ceiling that bounds initialization and the pole. -/
theorem IsRun.lower_le_ceiling {p : Parameters} {classify : ℝ → Region} {pole root ceiling : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root)
    (hi : (s 0).lower ≤ ceiling) (hp : pole ≤ ceiling) (k : ℕ)
    (hn : ∀ j < k, classify (s j).candidate ≠ .lower) : (s k).lower ≤ ceiling := by
  induction k with
  | zero => exact hi
  | succ k ih =>
    have hpre : ∀ j ≤ k, classify (s j).candidate ≠ .lower := fun j hj => hn j (by omega)
    have hs := h.brackets hc hpr k (fun j hj => hn j (by omega))
    have hl := ih (fun j hj => hn j (by omega))
    rw [h.lower_update k hpre]
    apply improveLower_le (pole := pole) (bound := ceiling) ?_ hp (h.estimate k hpre)
    split_ifs with hneg
    · exact max_le hl ((hc.negative_le _ (hs.1.trans hs.2.2.2.1) hneg).trans hp)
    · exact hl

/-- Uniform width-contraction coefficient for both possible update branches. -/
def contraction (p : Parameters) : ℝ := max (1 - p.lower) (max p.upper (1 / 2))

/-- The common contraction factor is nonnegative and strictly below one. -/
theorem contraction_bounds (p : Parameters) : 0 ≤ contraction p ∧ contraction p < 1 := by
  exact ⟨(by norm_num : (0 : ℝ) ≤ 1 / 2).trans
    ((le_max_right p.upper _).trans (le_max_right _ _)),
    max_lt (by linarith [p.lower_pos]) (max_lt p.upper_lt_one (by norm_num))⟩

/-- Every newly selected trial has uniform affine margins inside the updated interval. -/
theorem IsRun.candidate_bounds {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root) (k : ℕ)
    (hn : ∀ j ≤ k, classify (s j).candidate ≠ .lower) :
    (s (k + 1)).lower + p.lower * ((s (k + 1)).upper - (s (k + 1)).lower) ≤
      (s (k + 1)).candidate ∧
    (s (k + 1)).candidate ≤ (s (k + 1)).lower + max p.upper (1 / 2) *
      ((s (k + 1)).upper - (s (k + 1)).lower) := by
  let b := updateBounds (classify (s k).candidate) (s k) (c k).estimate
  have hs := h.brackets hc hpr k (fun j hj => hn j hj.le)
  have hb := updateBounds_bounds hc hpr hs (h.estimate k hn)
  change 0 ≤ b.lower ∧ b.lower ≤ root ∧ root ≤ b.upper at hb
  have hw : 0 ≤ b.upper - b.lower := sub_nonneg.mpr (hb.2.1.trans hb.2.2)
  have hchoice := h.choice k hn
  have hband := h.candidate_update k hn
  change (s (k + 1)).candidate ∈ Set.Icc
    (trial b (c k).thetaLower (c k).geometricLower)
    (trial b (c k).thetaUpper (c k).geometricUpper) at hband
  rw [h.lower_update k hn, h.upper_update k hn]
  change b.lower + p.lower * (b.upper - b.lower) ≤ (s (k + 1)).candidate ∧
    (s (k + 1)).candidate ≤ b.lower + max p.upper (1 / 2) * (b.upper - b.lower)
  constructor
  · calc
      _ ≤ b.lower + (c k).thetaLower * (b.upper - b.lower) := by
        nlinarith [hchoice.1]
      _ ≤ trial b (c k).thetaLower (c k).geometricLower := affine_le_trial _ _ _
      _ ≤ _ := hband.1
  · exact hband.2.trans (trial_le_affine_max hb.1 (hb.2.1.trans hb.2.2)
      (hchoice.2.2.1.trans (le_max_left _ _)) (le_max_right _ _) _)

/-- Every executed update after the initial trial contracts the actual interval width. -/
theorem IsRun.width_step {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root) (k : ℕ)
    (hn : ∀ j ≤ k + 1, classify (s j).candidate ≠ .lower) :
    (s (k + 2)).upper - (s (k + 2)).lower ≤
      contraction p * ((s (k + 1)).upper - (s (k + 1)).lower) := by
  have hpre : ∀ j ≤ k, classify (s j).candidate ≠ .lower := fun j hj => hn j (by omega)
  have hs := h.brackets hc hpr (k + 1) (fun j hj => hn j (by omega))
  have hw : 0 ≤ (s (k + 1)).upper - (s (k + 1)).lower :=
    sub_nonneg.mpr (hs.2.1.trans hs.2.2.1)
  have hb := h.candidate_bounds hc hpr k hpre
  have hlow := lower_le_updateBounds (classify (s (k + 1)).candidate)
    (s (k + 1)) (c (k + 1)).estimate
  rw [← h.lower_update (k + 1) hn] at hlow
  have hL := h.lower_update (k + 1) hn
  have hU := h.upper_update (k + 1) hn
  cases hr : classify (s (k + 1)).candidate with
  | negative =>
    have hcl : (s (k + 1)).candidate ≤ (s (k + 2)).lower := by
      rw [hL]
      simp only [updateBounds, hr, ite_true]
      exact (le_max_right _ _).trans (le_improveLower _ _)
    have hu : (s (k + 2)).upper = (s (k + 1)).upper := by
      simpa [updateBounds, hr] using hU
    have hq := mul_le_mul_of_nonneg_right
      (le_max_left (1 - p.lower) (max p.upper (1 / 2))) hw
    rw [hu]
    dsimp [contraction]
    nlinarith [hb.1]
  | lower => exact (hn (k + 1) le_rfl hr).elim
  | greater =>
    have hcu : (s (k + 2)).upper ≤ (s (k + 1)).candidate := by
      rw [hU]
      simp only [updateBounds, hr, ite_true]
      exact min_le_right _ _
    have hq := mul_le_mul_of_nonneg_right
      (le_max_right (1 - p.lower) (max p.upper (1 / 2))) hw
    dsimp [contraction]
    nlinarith [hb.2]

/-- A nonterminating legal search has geometrically vanishing interval widths. -/
theorem IsRun.width_le_pow {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hpr : pole ≤ root)
    (hn : ∀ k, classify (s k).candidate ≠ .lower) (k : ℕ) :
    (s (k + 1)).upper - (s (k + 1)).lower ≤
      contraction p ^ k * ((s 1).upper - (s 1).lower) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := h.width_step hc hpr k (fun j _ => hn j)
    have hm := mul_le_mul_of_nonneg_left ih (contraction_bounds p).1
    rw [pow_succ]
    nlinarith

/-- Strict initialization below the root and a nonempty regular lower side force finite entry.
Allowing the initial lower endpoint to equal the root requires separate endpoint handling. -/
theorem IsRun.exists_lower {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hp : pole < root) (hi : (s 0).lower < root) :
    ∃ k, classify (s k).candidate = .lower := by
  by_contra! hn
  let ceiling := max (s 0).lower pole
  let δ := root - ceiling
  have hδ : 0 < δ := sub_pos.mpr (max_lt hi hp)
  have hw (k : ℕ) : δ ≤ (s (k + 1)).upper - (s (k + 1)).lower := by
    have hs := h.brackets hc hp.le (k + 1) (fun j _ => hn j)
    have hl := h.lower_le_ceiling hc hp.le (le_max_left (s 0).lower pole)
      (le_max_right (s 0).lower pole) (k + 1) (fun j _ => hn j)
    dsimp [δ, ceiling]
    linarith [hs.2.2.1]
  have hw1 : 0 < (s 1).upper - (s 1).lower := hδ.trans_le (hw 0)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδ hw1) (contraction_bounds p).2
  have hsmall := (lt_div_iff₀ hw1).mp hk
  have hgeo := h.width_le_pow hc hp.le hn k
  linarith [hw k]

/-- Finite entry has a first executed lower-side trial with the true bracketing certificates. -/
theorem IsRun.exists_first_lower {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hp : pole < root) (hi : (s 0).lower < root) :
    ∃ k, classify (s k).candidate = .lower ∧
      (∀ j < k, classify (s j).candidate ≠ .lower) ∧
      Brackets root (s k) ∧ 0 ≤ (s k).candidate ∧ (s k).candidate ≤ root := by
  have he := h.exists_lower hc hp hi
  let k := Nat.find he
  have hk : classify (s k).candidate = .lower := Nat.find_spec he
  have hfirst : ∀ j < k, classify (s j).candidate ≠ .lower := fun j hj => Nat.find_min he hj
  have hb := h.brackets hc hp.le k hfirst
  have hnonneg := hb.1.trans hb.2.2.2.1
  exact ⟨k, hk, hfirst, hb, hnonneg, hc.lower_le _ hnonneg hk⟩

/-- The two-cutoff classifier used for simple explicit search examples. -/
def cutoffClassifier (pole root a : ℝ) : Region :=
  if a ≤ pole then .negative else if a ≤ root then .lower else .greater

/-- Cutoff classification supplies the local bound certificates. -/
theorem cutoffClassifier_spec (pole root : ℝ) :
    ClassifierSpec (cutoffClassifier pole root) pole root := by
  constructor
  · intro a _ ha
    by_contra hn
    simp [cutoffClassifier, hn] at ha
    split_ifs at ha
  · intro a _ ha
    by_contra hn
    simp [cutoffClassifier, hn] at ha
    split_ifs at ha
  · intro a _ ha
    by_contra! hn
    simp [cutoffClassifier, hn.le] at ha
    split_ifs at ha

end Optimization.SafeguardedSecularSearch
