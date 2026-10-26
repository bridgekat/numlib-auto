import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Safeguarded interval reduction for the multiplier of a subproblem

Algorithm 9.2.1 of Cartis–Gould–Toint (after Moré–Sorensen and Conn–Gould–Toint §7.3.6) looks for
a multiplier `λ` in the "good" set `𝓛 = (λₛ, λ*]` by shrinking a bracket `[λᴸ, λᵁ] ∋ λ*`: a trial
value `λ_C ≤ λₛ` (in `𝓝`) raises the lower end, a trial value `λ_C > λ*` (in `𝓖`) lowers the upper
end, and the next trial value is a safeguarded convex or geometric combination of the ends. The run
only ever *tests membership* of the trial value in the three pieces of the partition
`ℝ = Iic a ∪ Ioc a b ∪ Ioi b`, so it is formalized for an arbitrary partition (`a = λₛ`,
`b = λ*` for the subproblems).

`Subproblem.IsBracketRun a b θL θU lo hi c` says that the sequences of lower ends `lo`, upper ends
`hi` and trial values `c` are a run of the algorithm, with every nondeterministic choice of the
book (the parameters `θ ∈ [θL, θU]`, `γ ∈ {0, 1}`, the optional lower-bound improvements
`-λ_E ≤ λₛ`, and the new trial value in the interval (9.2.2)) existentially quantified. The run is
constant once a trial value lies in `Ioc a b`.

## Main statements

* `Subproblem.IsBracketRun.exists`: runs exist from any admissible initial bracket.
* `Subproblem.IsBracketRun.mem_of_le`: a run is constant after its exit.
* `Subproblem.IsBracketRun.invariant`: the bracket contains `b` and shrinks monotonically, and
  every non-final trial value lies in the bracket.
* `Subproblem.IsBracketRun.width_le`: after the first step, each step multiplies the width of the
  bracket by at most `ρ = max (1 - θL) (max θU (1/2)) < 1`.
* `Subproblem.IsBracketRun.exists_mem`: finite termination with an explicit iteration bound when
  `a < b` and the initial lower end is `< b`.

## Notes on the source

The book bounds the width ratio by `max (1 - θ, θ, γ √λᵁ/(√λᴸ + √λᵁ))`; this is valid but not
uniformly below `1`. The geometric branch in fact contracts by `√λᴸ/(√λᴸ + √λᵁ) ≤ 1/2` when it
moves the upper end, which gives the uniform factor `ρ`. Finite termination needs the initial
lower end below `b`: if `λᴸ = λ*` initially, every later trial value exceeds `λ*` and the run never
stops, a degenerate case not excluded by the book's "finite convergence if `𝓛` is nonempty".
-/

open Set

namespace Subproblem

/-- The safeguarded trial value of Algorithm 9.2.1, `max (γ √(l u)) (l + θ (u - l))`, a
geometric mean (if `γ = 1`) safeguarded by a convex combination of the bracket ends `l ≤ u`. -/
noncomputable def bracketEstimate (γ θ l u : ℝ) : ℝ := max (γ * √(l * u)) (l + θ * (u - l))

/-- An update `l ↦ l'` of a lower bracket end that is either trivial or a maximum with some
estimate `e ≤ a` (the book's `-λ_E` for an upper bound `λ_E ≥ λ₁` of the leftmost eigenvalue, so
that `-λ_E ≤ λₛ`). -/
def IsLowerUpdate (a l l' : ℝ) : Prop := l' = l ∨ ∃ e ≤ a, l' = max l e

/-- A run of Algorithm 9.2.1 of Cartis–Gould–Toint for the partition
`ℝ = Iic a ∪ Ioc a b ∪ Ioi b`, with parameters `θL ≤ θU`: lower ends `lo`, upper ends `hi`, trial
values `c`, with `0 ≤ lo 0 ≤ b ≤ hi 0` ((9.2.1) for the target `b`, the multipliers being
nonnegative) and at every step `k`:
* if `c k ∈ Ioc a b`, the run has stopped: nothing changes;
* if `c k ≤ a`, the lower end is raised to `max (lo k) (c k)` and possibly improved by an estimate
  `e ≤ a`, and the next trial value is `bracketEstimate γ θ` of the new bracket for some
  `θ ∈ [θL, θU]`, `γ ∈ {0, 1}`;
* if `b < c k`, the upper end is lowered to `min (hi k) (c k)`, the lower end possibly improved by
  an estimate `e ≤ a`, and the next trial value lies in the interval (9.2.2) between
  `bracketEstimate γ₁ θl` and `bracketEstimate γ₂ θu` of the new bracket, for some
  `θl ≤ θu` in `[θL, θU]` and `γ₁ ≤ γ₂` in `{0, 1}`. -/
structure IsBracketRun (a b θL θU : ℝ) (lo hi c : ℕ → ℝ) : Prop where
  /-- The initial lower end is nonnegative. -/
  nonneg : 0 ≤ lo 0
  /-- The initial lower end is at most the target `b` ((9.2.1)). -/
  lo_zero_le : lo 0 ≤ b
  /-- The initial upper end is at least the target `b` ((9.2.1)). -/
  le_hi_zero : b ≤ hi 0
  /-- A trial value in `Ioc a b` (in `𝓛`) stops the run. -/
  exit : ∀ k, c k ∈ Ioc a b → lo (k + 1) = lo k ∧ hi (k + 1) = hi k ∧ c (k + 1) = c k
  /-- A trial value `≤ a` (in `𝓝`) raises the lower end; the next trial value is
  `bracketEstimate γ θ` of the new bracket. -/
  left : ∀ k, c k ≤ a → hi (k + 1) = hi k ∧ IsLowerUpdate a (max (lo k) (c k)) (lo (k + 1)) ∧
    ∃ θ ∈ Icc θL θU, ∃ γ ∈ ({0, 1} : Set ℝ),
      c (k + 1) = bracketEstimate γ θ (lo (k + 1)) (hi (k + 1))
  /-- A trial value `> b` (in `𝓖`) lowers the upper end; the next trial value lies in the
  interval (9.2.2) of the new bracket. -/
  right : ∀ k, b < c k → hi (k + 1) = min (hi k) (c k) ∧ IsLowerUpdate a (lo k) (lo (k + 1)) ∧
    ∃ θl ∈ Icc θL θU, ∃ θu ∈ Icc θL θU, θl ≤ θu ∧ ∃ γ₁ ∈ ({0, 1} : Set ℝ),
      ∃ γ₂ ∈ ({0, 1} : Set ℝ), γ₁ ≤ γ₂ ∧
        c (k + 1) ∈ Icc (bracketEstimate γ₁ θl (lo (k + 1)) (hi (k + 1)))
          (bracketEstimate γ₂ θu (lo (k + 1)) (hi (k + 1)))

/-! ### The trial value -/

section Estimate

variable {γ θ l u : ℝ}

/-- The trial value is at least the convex combination `l + θ (u - l)`. -/
theorem le_bracketEstimate (γ θ l u : ℝ) : l + θ * (u - l) ≤ bracketEstimate γ θ l u :=
  le_max_right _ _

/-- For `γ ∈ {0, 1}` the trial value is at most `max (√(l u)) (l + θ (u - l))`. -/
theorem bracketEstimate_le_max_sqrt (hγ : γ ∈ ({0, 1} : Set ℝ)) :
    bracketEstimate γ θ l u ≤ max √(l * u) (l + θ * (u - l)) := by
  refine max_le_max ?_ le_rfl
  rcases hγ with rfl | rfl <;> simp [Real.sqrt_nonneg]

/-- The geometric mean of `0 ≤ l ≤ u` exceeds `l` by at most half the width. -/
theorem sqrt_mul_sub_le (hl : 0 ≤ l) (hlu : l ≤ u) : √(l * u) - l ≤ (u - l) / 2 := by
  have h : √(l * u) ≤ (l + u) / 2 :=
    (Real.sqrt_le_left (by linarith)).2 (by nlinarith [sq_nonneg (u - l)])
  linarith

/-- The geometric mean of `0 ≤ l ≤ u` is at most `u`. -/
theorem sqrt_mul_le_right (hl : 0 ≤ l) (hlu : l ≤ u) : √(l * u) ≤ u :=
  (Real.sqrt_le_left (hl.trans hlu)).2 (by nlinarith)

/-- For `0 ≤ l ≤ u`, `γ ∈ {0, 1}` and `θ ∈ [0, 1]` the trial value lies in `[l, u]`. -/
theorem bracketEstimate_mem_Icc (hl : 0 ≤ l) (hlu : l ≤ u) (hγ : γ ∈ ({0, 1} : Set ℝ))
    (hθ : θ ∈ Icc (0 : ℝ) 1) : bracketEstimate γ θ l u ∈ Icc l u := by
  have hw : 0 ≤ u - l := sub_nonneg.2 hlu
  refine ⟨le_trans (by nlinarith [hθ.1]) (le_bracketEstimate γ θ l u),
    (bracketEstimate_le_max_sqrt hγ).trans (max_le (sqrt_mul_le_right hl hlu) ?_)⟩
  nlinarith [hθ.2]

end Estimate

/-- The lower end after an update is at least the old one. -/
theorem IsLowerUpdate.le {a l l' : ℝ} (h : IsLowerUpdate a l l') : l ≤ l' := by
  rcases h with rfl | ⟨e, -, rfl⟩
  · exact le_rfl
  · exact le_max_left _ _

/-- The lower end after an update is at most `max l a`. -/
theorem IsLowerUpdate.le_max {a l l' : ℝ} (h : IsLowerUpdate a l l') : l' ≤ max l a := by
  rcases h with rfl | ⟨e, he, rfl⟩
  · exact le_max_left _ _
  · exact max_le_max le_rfl he

/-! ### Existence -/

/-- One deterministic step of Algorithm 9.2.1 with `θ = θL`, `γ = 0` and no lower-bound
estimates, on the state `(lo, hi, c)`. -/
private noncomputable def bracketStep (a b θ : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if a < s.2.2 ∧ s.2.2 ≤ b then s
  else if s.2.2 ≤ a then (max s.1 s.2.2, s.2.1, bracketEstimate 0 θ (max s.1 s.2.2) s.2.1)
  else (s.1, min s.2.1 s.2.2, bracketEstimate 0 θ s.1 (min s.2.1 s.2.2))

/-- Runs exist: from any `0 ≤ lo₀ ≤ b ≤ hi₀` and any `c₀`, the deterministic run with `θ = θL`,
`γ = 0` and no lower-bound estimates is a run, for any `a ≤ b` and `θL ≤ θU`. -/
theorem IsBracketRun.exists {a b θL θU lo₀ hi₀ c₀ : ℝ} (hab : a ≤ b) (hθ : θL ≤ θU)
    (h0 : 0 ≤ lo₀) (hlo : lo₀ ≤ b) (hhi : b ≤ hi₀) :
    ∃ lo hi c : ℕ → ℝ, IsBracketRun a b θL θU lo hi c ∧ lo 0 = lo₀ ∧ hi 0 = hi₀ ∧ c 0 = c₀ := by
  set s : ℕ → ℝ × ℝ × ℝ := fun k => (bracketStep a b θL)^[k] (lo₀, hi₀, c₀) with hs
  have hsucc : ∀ k, s (k + 1) = bracketStep a b θL (s k) := fun k => by
    simp only [hs, Function.iterate_succ_apply']
  have hθmem : θL ∈ Icc θL θU := ⟨le_rfl, hθ⟩
  have h0mem : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := Or.inl rfl
  have e1 : ∀ k, (s k).2.2 ∈ Ioc a b → s (k + 1) = s k := fun k hk => by
    rw [hsucc, bracketStep, ite_eq_left (show a < (s k).2.2 ∧ (s k).2.2 ≤ b from hk)]
  have e2 : ∀ k, (s k).2.2 ≤ a → s (k + 1) = (max (s k).1 (s k).2.2, (s k).2.1,
      bracketEstimate 0 θL (max (s k).1 (s k).2.2) (s k).2.1) := fun k hk => by
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ b) := fun h => absurd hk (not_le.2 h.1)
    rw [hsucc, bracketStep, ite_eq_right hn, ite_eq_left hk]
  have e3 : ∀ k, b < (s k).2.2 → s (k + 1) = ((s k).1, min (s k).2.1 (s k).2.2,
      bracketEstimate 0 θL (s k).1 (min (s k).2.1 (s k).2.2)) := fun k hk => by
    have hn : ¬ (a < (s k).2.2 ∧ (s k).2.2 ≤ b) := fun h => absurd hk (not_lt.2 h.2)
    have hn' : ¬ (s k).2.2 ≤ a := fun h => absurd (h.trans hab) (not_le.2 hk)
    rw [hsucc, bracketStep, ite_eq_right hn, ite_eq_right hn']
  refine ⟨fun k => (s k).1, fun k => (s k).2.1, fun k => (s k).2.2, ⟨h0, hlo, hhi, ?_, ?_, ?_⟩,
    rfl, rfl, rfl⟩
  · intro k hk
    rw [e1 k hk]
    exact ⟨rfl, rfl, rfl⟩
  · intro k hk
    rw [e2 k hk]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, 0, h0mem, rfl⟩
  · intro k hk
    rw [e3 k hk]
    exact ⟨rfl, Or.inl rfl, θL, hθmem, θL, hθmem, le_rfl, 0, h0mem, 0, h0mem, le_rfl,
      le_rfl, le_rfl⟩

/-! ### Invariants -/

namespace IsBracketRun

variable {a b θL θU : ℝ} {lo hi c : ℕ → ℝ} (h : IsBracketRun a b θL θU lo hi c)
include h

/-- **Exit is stable**: once a trial value `c k` lies in `Ioc a b`, the run is constant from then
on. -/
theorem mem_of_le {k : ℕ} (hk : c k ∈ Ioc a b) {n : ℕ} (hkn : k ≤ n) :
    c n = c k ∧ lo n = lo k ∧ hi n = hi k := by
  induction n, hkn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨h1, h2, h3⟩ := h.exit n (ih.1 ▸ hk)
    exact ⟨h3.trans ih.1, h1.trans ih.2.1, h2.trans ih.2.2⟩

/-- One step of a run: the bracket ends move monotonically, the upper end stays at least `b` and
the lower end stays at most `max (lo k) a`. -/
theorem step_bounds (k : ℕ) :
    lo k ≤ lo (k + 1) ∧ lo (k + 1) ≤ max (lo k) a ∧ hi (k + 1) ≤ hi k ∧
      (b ≤ hi k → b ≤ hi (k + 1)) := by
  rcases le_or_gt (c k) a with hca | hca
  · obtain ⟨hhi, hlo, -⟩ := h.left k hca
    refine ⟨(le_max_left _ _).trans hlo.le, hlo.le_max.trans ?_, hhi.le, fun hb => hhi ▸ hb⟩
    exact max_le (max_le (le_max_left _ _) (hca.trans (le_max_right _ _))) (le_max_right _ _)
  rcases le_or_gt (c k) b with hcb | hcb
  · obtain ⟨hlo, hhi, -⟩ := h.exit k ⟨hca, hcb⟩
    exact ⟨hlo.ge, hlo ▸ le_max_left _ _, hhi.le, fun hb => hhi ▸ hb⟩
  · obtain ⟨hhi, hlo, -⟩ := h.right k hcb
    exact ⟨hlo.le, hlo.le_max, hhi ▸ min_le_left _ _,
      fun hb => hhi ▸ le_min hb hcb.le⟩

/-- The lower ends increase. -/
theorem monotone_lo : Monotone lo :=
  monotone_nat_of_le_succ fun k => (h.step_bounds k).1

/-- The upper ends decrease. -/
theorem antitone_hi : Antitone hi :=
  antitone_nat_of_succ_le fun k => (h.step_bounds k).2.2.1

/-- The upper ends stay at least `b`. -/
theorem le_hi (k : ℕ) : b ≤ hi k := by
  induction k with
  | zero => exact h.le_hi_zero
  | succ k ih => exact (h.step_bounds k).2.2.2 ih

/-- The lower ends stay at most `max (lo 0) a`. -/
theorem lo_le_max (k : ℕ) : lo k ≤ max (lo 0) a := by
  induction k with
  | zero => exact le_max_left _ _
  | succ k ih =>
    exact (h.step_bounds k).2.1.trans (max_le ih (le_max_right _ _))

/-- The lower ends stay at most `b`. -/
theorem lo_le (hab : a ≤ b) (k : ℕ) : lo k ≤ b :=
  (h.lo_le_max k).trans (max_le h.lo_zero_le hab)

/-- The lower ends stay nonnegative. -/
theorem lo_nonneg (k : ℕ) : 0 ≤ lo k :=
  h.nonneg.trans (h.monotone_lo (Nat.zero_le k))

/-- A trial value that does not stop the run was produced by a non-final step, hence by one of
the two update formulas: it is at least `lo + θL (hi - lo)` and at most
`max (√(lo hi)) (lo + θU (hi - lo))` of the current bracket. -/
theorem estimate_bounds (hab : a ≤ b) {k : ℕ} (hk : c (k + 1) ∉ Ioc a b) :
    lo (k + 1) + θL * (hi (k + 1) - lo (k + 1)) ≤ c (k + 1) ∧
      c (k + 1) ≤ max √(lo (k + 1) * hi (k + 1)) (lo (k + 1) + θU * (hi (k + 1) - lo (k + 1))) := by
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) :=
    sub_nonneg.2 ((h.lo_le hab _).trans (h.le_hi _))
  rcases le_or_gt (c k) a with hca | hca
  · obtain ⟨-, -, θ, hθ, γ, hγ, hc⟩ := h.left k hca
    rw [hc]
    exact ⟨le_trans (by nlinarith [hθ.1]) (le_bracketEstimate _ _ _ _),
      (bracketEstimate_le_max_sqrt hγ).trans (max_le_max le_rfl (by nlinarith [hθ.2]))⟩
  rcases le_or_gt (c k) b with hcb | hcb
  · exact absurd ((h.exit k ⟨hca, hcb⟩).2.2 ▸ ⟨hca, hcb⟩) hk
  · obtain ⟨-, -, θl, hθl, θu, hθu, -, γ₁, -, γ₂, hγ₂, -, hc⟩ := h.right k hcb
    exact ⟨le_trans (by nlinarith [hθl.1]) ((le_bracketEstimate _ _ _ _).trans hc.1),
      hc.2.trans ((bracketEstimate_le_max_sqrt hγ₂).trans
        (max_le_max le_rfl (by nlinarith [hθu.2])))⟩

/-- **Invariants of a run** (for `a ≤ b`): `lo k ≤ b ≤ hi k`, the lower ends increase, the upper
ends decrease, `lo k ≤ max (lo 0) a`, and a trial value `c (k+1)` that does not stop the run lies
in the bracket `[lo (k+1), hi (k+1)]` (when `0 ≤ θL` and `θU ≤ 1`). -/
theorem invariant (hab : a ≤ b) (hθL : 0 ≤ θL) (hθU : θU ≤ 1) :
    (∀ k, lo k ≤ b ∧ b ≤ hi k) ∧ Monotone lo ∧ Antitone hi ∧ (∀ k, lo k ≤ max (lo 0) a) ∧
      ∀ k, c (k + 1) ∉ Ioc a b → c (k + 1) ∈ Icc (lo (k + 1)) (hi (k + 1)) := by
  refine ⟨fun k => ⟨h.lo_le hab k, h.le_hi k⟩, h.monotone_lo, h.antitone_hi,
    h.lo_le_max, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := h.estimate_bounds hab hk
  have hl := h.lo_nonneg (k + 1)
  have hlu := (h.lo_le hab (k + 1)).trans (h.le_hi (k + 1))
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) := sub_nonneg.2 hlu
  exact ⟨le_trans (by nlinarith) h1, h2.trans (max_le (sqrt_mul_le_right hl hlu) (by nlinarith))⟩

/-- Width contraction in the form used by `IsBracketRun.width_le`: a step from a non-final trial
value `c (k+1)` multiplies the bracket width by at most `ρ = max (1 - θL) (max θU (1/2))`. -/
theorem width_le_aux (hab : a ≤ b) {k : ℕ} (hk : c (k + 1) ∉ Ioc a b) :
    hi (k + 2) - lo (k + 2) ≤ max (1 - θL) (max θU (1 / 2)) * (hi (k + 1) - lo (k + 1)) := by
  obtain ⟨h1, h2⟩ := h.estimate_bounds hab hk
  have hl := h.lo_nonneg (k + 1)
  have hlu := (h.lo_le hab (k + 1)).trans (h.le_hi (k + 1))
  have hw : 0 ≤ hi (k + 1) - lo (k + 1) := sub_nonneg.2 hlu
  set ρ := max (1 - θL) (max θU (1 / 2))
  have hρ1 : (1 - θL) * (hi (k + 1) - lo (k + 1)) ≤ ρ * (hi (k + 1) - lo (k + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  have hρ2 : θU * (hi (k + 1) - lo (k + 1)) ≤ ρ * (hi (k + 1) - lo (k + 1)) :=
    mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hw
  have hρ3 : (hi (k + 1) - lo (k + 1)) / 2 ≤ ρ * (hi (k + 1) - lo (k + 1)) := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hw
  rcases le_or_gt (c (k + 1)) a with hca | hca
  · -- the lower end moves up to at least `c (k+1)`
    obtain ⟨hhi, hlo, -⟩ := h.left (k + 1) hca
    have : c (k + 1) ≤ lo (k + 2) := (le_max_right _ _).trans hlo.le
    rw [hhi]
    nlinarith
  · have hcb : b < c (k + 1) := by
      by_contra hcb
      exact hk ⟨hca, not_lt.1 hcb⟩
    -- the upper end moves down to at most `c (k+1)`
    obtain ⟨hhi, hlo, -⟩ := h.right (k + 1) hcb
    have hhi' : hi (k + 2) ≤ c (k + 1) := hhi ▸ min_le_right _ _
    have hlo' := hlo.le
    rcases le_max_iff.1 h2 with h2 | h2
    · have := sqrt_mul_sub_le hl hlu
      linarith
    · linarith

/-- **Width contraction**: for `k ≥ 1`, a step from a trial value `c k ∉ Ioc a b` multiplies the
width of the bracket by at most `ρ = max (1 - θL) (max θU (1/2))`. -/
theorem width_le (hab : a ≤ b) {k : ℕ} (hk1 : 1 ≤ k) (hk : c k ∉ Ioc a b) :
    hi (k + 1) - lo (k + 1) ≤ max (1 - θL) (max θU (1 / 2)) * (hi k - lo k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk1
  exact h.width_le_aux hab hk

/-- **Finite termination** (with an explicit bound): if `a < b`, `lo 0 < b` and
`0 < θL ≤ θU < 1`, then some trial value `c k` with
`k ≤ ⌈log ((hi 1 - lo 1) / (b - max (lo 0) a)) / log (1/ρ)⌉₊ + 1`,
`ρ = max (1 - θL) (max θU (1/2))`, lies in `Ioc a b`. While the run has not stopped, the bracket
keeps width at least `b - max (lo 0) a > 0` and shrinks by `ρ` per step. -/
theorem exists_mem (hab : a < b) (hlo : lo 0 < b) (hθL : 0 < θL) (hθU : θU < 1) :
    ∃ k ≤ ⌈Real.log ((hi 1 - lo 1) / (b - max (lo 0) a)) /
        Real.log (1 / max (1 - θL) (max θU (1 / 2)))⌉₊ + 1, c k ∈ Ioc a b := by
  set ρ := max (1 - θL) (max θU (1 / 2)) with hρ
  set δ := b - max (lo 0) a with hδ
  set W := hi 1 - lo 1 with hW
  set N := ⌈Real.log (W / δ) / Real.log (1 / ρ)⌉₊ with hN
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans (le_max_right _ _))
  have hρ1 : ρ < 1 := max_lt (by linarith) (max_lt hθU (by norm_num))
  have hδpos : 0 < δ := sub_pos.2 (max_lt hlo hab)
  have hwidth : ∀ k, δ ≤ hi k - lo k := fun k => by
    have := h.lo_le_max k
    have := h.le_hi k
    linarith
  have hWpos : 0 < W := hδpos.trans_le (hwidth 1)
  by_contra hcon
  push Not at hcon
  -- the widths decay geometrically while the run has not stopped
  have hdecay : ∀ n ≤ N + 1, hi (n + 1) - lo (n + 1) ≤ ρ ^ n * W := by
    intro n hn
    induction n with
    | zero => simp [hW]
    | succ n ih =>
      have := h.width_le hab.le (Nat.le_add_left 1 n) (hcon (n + 1) hn)
      calc hi (n + 1 + 1) - lo (n + 1 + 1) ≤ ρ * (hi (n + 1) - lo (n + 1)) := this
        _ ≤ ρ * (ρ ^ n * W) := mul_le_mul_of_nonneg_left (ih (by omega)) hρpos.le
        _ = ρ ^ (n + 1) * W := by ring
  -- `ρ ^ N ≤ δ / W` by the choice of `N`
  have hlogρ : 0 < Real.log (1 / ρ) := Real.log_pos ((one_lt_div hρpos).2 hρ1)
  have hpowN : ρ ^ N ≤ δ / W := by
    have hceil : Real.log (W / δ) ≤ N * Real.log (1 / ρ) :=
      (div_le_iff₀ hlogρ).1 (Nat.le_ceil _)
    rw [← Real.log_le_log_iff (pow_pos hρpos N) (div_pos hδpos hWpos), Real.log_pow,
      Real.log_div hδpos.ne' hWpos.ne']
    rw [Real.log_div hWpos.ne' hδpos.ne', one_div, Real.log_inv] at hceil
    linarith
  have h1 := hdecay (N + 1) le_rfl
  have h2 := hwidth (N + 1 + 1)
  have : ρ ^ (N + 1) * W ≤ ρ * δ := by
    rw [pow_succ, mul_comm (ρ ^ N) ρ, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hWpos).1 hpowN) hρpos.le
  nlinarith

end IsBracketRun

end Subproblem
