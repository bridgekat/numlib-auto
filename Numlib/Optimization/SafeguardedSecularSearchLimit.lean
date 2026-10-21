import Numlib.Optimization.SafeguardedSecularSearch

/-!
# Limits and width stopping for safeguarded interval searches

An infinite legal history contracts to its enclosed root. A positive width tolerance is
therefore reached in finite time; the retained midpoint then has the usual half-width error.
No exact root is queried by any transition or stopping test.
-/

noncomputable section
open Filter Topology
namespace Optimization.SafeguardedSecularSearch

/-- Ordering both affine and binary geometric safeguards orders their actual trial points. -/
theorem trial_mono {s : State} (hs : s.lower ≤ s.upper) {θl θu : ℝ}
    (hθ : θl ≤ θu) {gl gu : Bool} (hg : gl ≤ gu) : trial s θl gl ≤ trial s θu gu := by
  have ha : s.lower + θl * (s.upper - s.lower) ≤
      s.lower + θu * (s.upper - s.lower) := by nlinarith
  cases gl <;> cases gu
  · exact max_le_max le_rfl ha
  · exact max_le_max (Real.sqrt_nonneg _) ha
  · exact (show ¬ (true : Bool) ≤ false by decide) hg |>.elim
  · exact max_le_max le_rfl ha

/-- The ordered source safeguards always specify a nonempty interval of candidate choices. -/
theorem Choice.trial_interval_nonempty {p : Parameters} {r : Region} {c : Choice}
    (hc : c.Legal p r) {s : State} (hs : s.lower ≤ s.upper) :
    (Set.Icc (trial s c.thetaLower c.geometricLower)
      (trial s c.thetaUpper c.geometricUpper)).Nonempty :=
  Set.nonempty_Icc.mpr (trial_mono hs hc.2.1 hc.2.2.2.1)

/-- An infinite legal search has interval widths tending to zero. -/
theorem IsRun.tendsto_width {p : Parameters} {classify : ℝ → Region} {pole root : ℝ}
    {s : ℕ → State} {c : ℕ → Choice} (h : IsRun p classify pole root s c)
    (hc : ClassifierSpec classify pole root) (hp : pole ≤ root)
    (hn : ∀ k, classify (s k).candidate ≠ .lower) :
    Tendsto (fun k => (s k).upper - (s k).lower) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply squeeze_zero
  · intro k
    have hs := h.brackets hc hp (k + 1) (fun j _ => hn j)
    linarith [hs.2.1, hs.2.2.1]
  · exact h.width_le_pow hc hp hn
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (contraction_bounds p).1 (contraction_bounds p).2).mul_const
      ((s 1).upper - (s 1).lower)

/-- The distance of any enclosed point from the root is bounded by the retained width. -/
theorem Brackets.dist_le_width {root : ℝ} {s : State} (h : Brackets root s)
    {x : ℝ} (hx : x ∈ Set.Icc s.lower s.upper) :
    dist x root ≤ s.upper - s.lower := by
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h.2.1, h.2.2.1, hx.1, hx.2]

/-- Every retained lower endpoint, upper endpoint, and trial tends to the enclosed root. -/
theorem IsRun.tendsto_bounds_candidate {p : Parameters} {classify : ℝ → Region}
    {pole root : ℝ} {s : ℕ → State} {c : ℕ → Choice}
    (h : IsRun p classify pole root s c) (hc : ClassifierSpec classify pole root)
    (hp : pole ≤ root) (hn : ∀ k, classify (s k).candidate ≠ .lower) :
    Tendsto (fun k => (s k).lower) atTop (𝓝 root) ∧
      Tendsto (fun k => (s k).upper) atTop (𝓝 root) ∧
      Tendsto (fun k => (s k).candidate) atTop (𝓝 root) := by
  have hw := h.tendsto_width hc hp hn
  have aux (x : ℕ → ℝ) (hx : ∀ k, x k ∈ Set.Icc (s k).lower (s k).upper) :
      Tendsto x atTop (𝓝 root) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hw.eventually_lt_const hε)
    refine ⟨N, fun k hk => ?_⟩
    exact ((h.brackets hc hp k (fun j _ => hn j)).dist_le_width (hx k)).trans_lt (hN k hk)
  have hb (k : ℕ) := h.brackets hc hp k (fun j _ => hn j)
  exact ⟨aux _ (fun k => ⟨le_rfl, (hb k).2.1.trans (hb k).2.2.1⟩),
    aux _ (fun k => ⟨(hb k).2.1.trans (hb k).2.2.1, le_rfl⟩),
    aux _ (fun k => ⟨(hb k).2.2.2.1, (hb k).2.2.2.2⟩)⟩

/-- Either a lower-region point is returned or a positive width tolerance is attained. -/
theorem IsRun.exists_lower_or_width_lt {p : Parameters} {classify : ℝ → Region}
    {pole root : ℝ} {s : ℕ → State} {c : ℕ → Choice}
    (h : IsRun p classify pole root s c) (hc : ClassifierSpec classify pole root)
    (hp : pole ≤ root) {ε : ℝ} (hε : 0 < ε) :
    (∃ k, classify (s k).candidate = .lower) ∨
      ∃ k, (∀ j ≤ k, classify (s j).candidate ≠ .lower) ∧
        (s k).upper - (s k).lower < ε := by
  classical
  by_cases he : ∃ k, classify (s k).candidate = .lower
  · exact Or.inl he
  · push Not at he
    obtain ⟨k, hk⟩ := ((h.tendsto_width hc hp he).eventually_lt_const hε).exists
    exact Or.inr ⟨k, fun j _ => he j, hk⟩

/-- The retained midpoint is within half the width of every enclosed root. -/
theorem Brackets.midpoint_error {root : ℝ} {s : State} (h : Brackets root s) :
    |(s.lower + s.upper) / 2 - root| ≤ (s.upper - s.lower) / 2 := by
  rw [abs_le]
  constructor <;> linarith [h.2.1, h.2.2.1]

/-- The width test provides a strict half-tolerance midpoint approximation. -/
theorem Brackets.midpoint_error_lt {root ε : ℝ} {s : State} (h : Brackets root s)
    (hw : s.upper - s.lower < ε) : |(s.lower + s.upper) / 2 - root| < ε / 2 :=
  h.midpoint_error.trans_lt (by linarith)

end Optimization.SafeguardedSecularSearch
