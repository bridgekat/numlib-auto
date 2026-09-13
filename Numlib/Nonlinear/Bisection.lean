import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The bisection method

The bisection method for a real root of a continuous function ([quarteroni2000numerical] §6.2.1;
[kress1998numerical] §6.1; [han2009theoretical] §5.2): the theorem of zeros for continuous
functions (Mathlib's intermediate value theorem in the sign-change form
`exists_eq_zero_Ioo_of_mul_neg`), the bracket iteration `Bisection.step` on pairs `(a, b)`, its
invariants — the length halves (`bracket_sub`), the sign condition persists (`bracket_mul_nonpos`),
the brackets are nested (`bracket_nested`) — and global convergence to a root with the a priori
bound `|x_k - α| ≤ (b - a) / 2 ^ (k + 1)` (`exists_tendsto_iterate`; the book prints
`(b - a) / 2 ^ k`, which the midpoint choice improves by a factor two), plus the iteration-count
bound `|x_m - α| ≤ ε` for `log₂((b - a) / ε) ≤ m + 1` (`abs_iterate_sub_le_of_le_logb`, the book's
(6.9)).

## Design

* The step follows the book's Program 46 rather than its prose: `a := m` when `f a · f m > 0`, and
  `b := m` otherwise — so an exact hit `f m = 0` closes the bracket on the right and keeps `m` as
  `b`. The prose's two strict cases leave `f m = 0` undefined.
* Only `f a * f b ≤ 0` is needed for everything, not the book's `< 0`: the invariant is stated with
  `≤ 0`, since it fails with `< 0` as soon as an iterate is an exact root.
* The root produced by `exists_tendsto_iterate` is the supremum of the left endpoints; a bracket may
  contain several roots, and the estimates hold for that root. The iteration-count bound is stated
  for it (`abs_iterate_sub_le_of_le_logb`) and, in the pure arithmetic form
  `div_two_pow_le_of_logb_le`, for any sequence obeying the a priori bound.
-/

open Filter Topology Set

section IntermediateValue

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **The theorem of zeros for continuous functions** ([quarteroni2000numerical] Property 6.1): a
continuous `f : [a, b] → ℝ` with `f a * f b < 0` has a zero in the open interval `(a, b)`.
Mathlib's `intermediate_value_Ioo` / `intermediate_value_Ioo'` after `mul_neg_iff` splits the sign
case; every rootfinding text states it in this product form. -/
theorem exists_eq_zero_Ioo_of_mul_neg (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b < 0) : ∃ α ∈ Ioo a b, f α = 0 := by
  rcases mul_neg_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨α, hα, hfα⟩ := intermediate_value_Ioo' hab hf ⟨hb, ha⟩
    exact ⟨α, hα, hfα⟩
  · obtain ⟨α, hα, hfα⟩ := intermediate_value_Ioo hab hf ⟨ha, hb⟩
    exact ⟨α, hα, hfα⟩

/-- The closed form of the theorem of zeros: for `a ≤ b`, `f` continuous on `[a, b]` and
`f a * f b ≤ 0`, there is a zero in `[a, b]` — an endpoint when the product vanishes,
`exists_eq_zero_Ioo_of_mul_neg` otherwise. -/
theorem exists_eq_zero_Icc_of_mul_nonpos (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b ≤ 0) : ∃ α ∈ Icc a b, f α = 0 := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨α, hα, hfα⟩ := exists_eq_zero_Ioo_of_mul_neg hab hf hlt
    exact ⟨α, Ioo_subset_Icc_self hα, hfα⟩
  · rcases mul_eq_zero.1 heq with ha | hb
    · exact ⟨a, left_mem_Icc.2 hab, ha⟩
    · exact ⟨b, right_mem_Icc.2 hab, hb⟩

end IntermediateValue

namespace Bisection

variable {f : ℝ → ℝ} {a b : ℝ}

/-- One bisection step on a bracket `(a, b)`: with `m = (a + b) / 2`, keep `[m, b]` when
`f a * f m > 0` and `[a, m]` otherwise — the rule of [quarteroni2000numerical] Program 46, under
which an exact hit `f m = 0` closes the bracket on the right. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  if 0 < f s.1 * f ((s.1 + s.2) / 2) then ((s.1 + s.2) / 2, s.2) else (s.1, (s.1 + s.2) / 2)

/-- The `k`-th bracket `[a^{(k)}, b^{(k)}]` of the bisection method started on `[a, b]`. -/
noncomputable def bracket (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ × ℝ := (step f)^[k] (a, b)

/-- The `k`-th bisection iterate `x^{(k)} = (a^{(k)} + b^{(k)}) / 2`, the midpoint of the `k`-th
bracket. -/
noncomputable def iterate (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  ((bracket f a b k).1 + (bracket f a b k).2) / 2

@[simp]
theorem bracket_zero (f : ℝ → ℝ) (a b : ℝ) : bracket f a b 0 = (a, b) := rfl

/-- The `(k+1)`-st bracket is one bisection step from the `k`-th. -/
theorem bracket_succ (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    bracket f a b (k + 1) = step f (bracket f a b k) :=
  Function.iterate_succ_apply' _ _ _

/-- **The length halves** ([quarteroni2000numerical] (6.8)): `b^{(k)} - a^{(k)} = (b - a) / 2 ^ k`,
with no hypothesis on `f`, `a` or `b`. -/
theorem bracket_sub (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    (bracket f a b k).2 - (bracket f a b k).1 = (b - a) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [bracket_succ]
    set s := bracket f a b k with hs
    unfold step
    have h2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    have ih' : b - a = (s.2 - s.1) * 2 ^ k := by rw [ih]; field_simp
    split_ifs <;> simp only <;> rw [pow_succ, ih'] <;> field_simp <;> ring

/-- The brackets are genuine intervals when the starting one is. -/
theorem bracket_fst_le_snd (hab : a ≤ b) (k : ℕ) : (bracket f a b k).1 ≤ (bracket f a b k).2 := by
  have := bracket_sub f a b k
  have hpos : 0 ≤ (b - a) / 2 ^ k := by
    have : 0 ≤ b - a := sub_nonneg.2 hab
    positivity
  linarith

/-- **The sign invariant**: if `f a * f b ≤ 0` then `f a^{(k)} * f b^{(k)} ≤ 0` for every `k`. The
book writes `< 0`, which fails at an exact hit; the weak inequality is what the step preserves. -/
theorem bracket_mul_nonpos (h : f a * f b ≤ 0) (k : ℕ) :
    f (bracket f a b k).1 * f (bracket f a b k).2 ≤ 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [bracket_succ]
    set s := bracket f a b k with hs
    unfold step
    split_ifs with hpos
    · simp only
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hpos hcon, sq_nonneg (f ((s.1 + s.2) / 2))]
    · simpa using hpos

/-- Each step keeps one endpoint and replaces the other by the midpoint, so the brackets are
nested: `[a^{(k+1)}, b^{(k+1)}] ⊆ [a^{(k)}, b^{(k)}]`. -/
theorem bracket_nested (hab : a ≤ b) (k : ℕ) :
    Icc (bracket f a b (k + 1)).1 (bracket f a b (k + 1)).2 ⊆
      Icc (bracket f a b k).1 (bracket f a b k).2 := by
  have hle := bracket_fst_le_snd (f := f) hab k
  rw [bracket_succ]
  set s := bracket f a b k with hs
  unfold step
  split_ifs <;> exact Icc_subset_Icc (by simp only; linarith) (by simp only; linarith)

/-- The left endpoints increase. -/
theorem monotone_bracket_fst (hab : a ≤ b) : Monotone fun k => (bracket f a b k).1 :=
  monotone_nat_of_le_succ fun k =>
    (bracket_nested hab k (left_mem_Icc.2 (bracket_fst_le_snd hab (k + 1)))).1

/-- The right endpoints decrease. -/
theorem antitone_bracket_snd (hab : a ≤ b) : Antitone fun k => (bracket f a b k).2 :=
  antitone_nat_of_succ_le fun k =>
    (bracket_nested hab k (right_mem_Icc.2 (bracket_fst_le_snd hab (k + 1)))).2

/-- Every bracket lies in the starting interval. -/
theorem bracket_subset_Icc (hab : a ≤ b) (k : ℕ) :
    Icc (bracket f a b k).1 (bracket f a b k).2 ⊆ Icc a b :=
  Icc_subset_Icc (by simpa using monotone_bracket_fst (f := f) hab (Nat.zero_le k))
    (by simpa using antitone_bracket_snd (f := f) hab (Nat.zero_le k))

/-- Every bracket contains a root: the theorem of zeros on `[a^{(k)}, b^{(k)}]`. -/
theorem exists_root_mem_bracket (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b ≤ 0)
    (k : ℕ) : ∃ α ∈ Icc (bracket f a b k).1 (bracket f a b k).2, f α = 0 :=
  exists_eq_zero_Icc_of_mul_nonpos (bracket_fst_le_snd hab k) (hf.mono (bracket_subset_Icc hab k))
    (bracket_mul_nonpos h k)

/-- A left endpoint never exceeds a right endpoint, whatever the indices. -/
theorem bracket_fst_le_bracket_snd (hab : a ≤ b) (j k : ℕ) :
    (bracket f a b j).1 ≤ (bracket f a b k).2 :=
  calc (bracket f a b j).1 ≤ (bracket f a b (max j k)).1 :=
        monotone_bracket_fst hab (le_max_left j k)
    _ ≤ (bracket f a b (max j k)).2 := bracket_fst_le_snd hab _
    _ ≤ (bracket f a b k).2 := antitone_bracket_snd hab (le_max_right j k)

/-- The midpoint of an interval is within half its length of every point of the interval. -/
theorem abs_midpoint_sub_le {u v x : ℝ} (hx : x ∈ Icc u v) : |(u + v) / 2 - x| ≤ (v - u) / 2 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- **Global convergence of bisection, with the a priori bound** ([quarteroni2000numerical]
§6.2.1, the consequence of (6.8)). For `a ≤ b`, `f` continuous on `[a, b]` and `f a * f b ≤ 0`
there is a root `α ∈ [a, b]` lying in every bracket, to which the iterates converge with
`|x^{(k)} - α| ≤ (b - a) / 2 ^ (k + 1)` for every `k` (the book states `(b - a) / 2 ^ k`).

`α` is the supremum of the increasing left endpoints; it lies below every right endpoint
(`bracket_fst_le_bracket_snd`), so in every bracket, and `f α = 0` because
`f a^{(k)} · f b^{(k)} ≤ 0` passes to the limit `f α · f α ≤ 0` along the two endpoint sequences,
which converge to `α` since the lengths `(b - a) / 2 ^ k` tend to `0`. -/
theorem exists_tendsto_iterate (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b ≤ 0) :
    ∃ α ∈ Icc a b, f α = 0 ∧ Tendsto (iterate f a b) atTop (𝓝 α) ∧
      (∀ k, α ∈ Icc (bracket f a b k).1 (bracket f a b k).2) ∧
      ∀ k, |iterate f a b k - α| ≤ (b - a) / 2 ^ (k + 1) := by
  set l : ℕ → ℝ := fun k => (bracket f a b k).1 with hl
  set r : ℕ → ℝ := fun k => (bracket f a b k).2 with hr
  have hbdd : BddAbove (range l) := ⟨b, by
    rintro _ ⟨k, rfl⟩
    simpa using bracket_fst_le_bracket_snd (f := f) hab k 0⟩
  set α : ℝ := ⨆ k, l k with hα
  have hmono : Monotone l := monotone_bracket_fst hab
  -- `α` lies in every bracket
  have hmem : ∀ k, α ∈ Icc (bracket f a b k).1 (bracket f a b k).2 := fun k =>
    ⟨le_ciSup hbdd k, ciSup_le fun j => bracket_fst_le_bracket_snd hab j k⟩
  -- the endpoints converge to `α`
  have hl_lim : Tendsto l atTop (𝓝 α) := tendsto_atTop_ciSup hmono hbdd
  have hlen : Tendsto (fun k : ℕ => (b - a) / 2 ^ k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).const_mul (b - a)
  have hr_lim : Tendsto r atTop (𝓝 α) := by
    have := hl_lim.add hlen
    rw [add_zero] at this
    refine this.congr fun k => ?_
    simp only [hl, hr]
    linarith [bracket_sub f a b k]
  -- the bound on the midpoints, and their convergence
  have hbound : ∀ k, |iterate f a b k - α| ≤ (b - a) / 2 ^ (k + 1) := fun k => by
    have := abs_midpoint_sub_le (hmem k)
    rw [bracket_sub, div_div, ← pow_succ] at this
    exact this
  have hx_lim : Tendsto (iterate f a b) atTop (𝓝 α) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => (Real.norm_eq_abs _).symm ▸ hbound k) ?_)
    exact (hlen.comp (tendsto_add_atTop_nat 1)).congr fun k => rfl
  -- `f α = 0` by passing the sign condition to the limit
  have hαab : α ∈ Icc a b := bracket_subset_Icc hab 0 (hmem 0)
  have hfα : f α = 0 := by
    have hcont : ContinuousWithinAt f (Icc a b) α := hf α hαab
    have hfl : Tendsto (fun k => f (l k)) atTop (𝓝 (f α)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hl_lim, Eventually.of_forall fun k => bracket_subset_Icc hab k
          (left_mem_Icc.2 (bracket_fst_le_snd hab k))⟩)
    have hfr : Tendsto (fun k => f (r k)) atTop (𝓝 (f α)) :=
      hcont.tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hr_lim, Eventually.of_forall fun k => bracket_subset_Icc hab k
          (right_mem_Icc.2 (bracket_fst_le_snd hab k))⟩)
    have hsq : f α * f α ≤ 0 :=
      le_of_tendsto (hfl.mul hfr) (Eventually.of_forall fun k => bracket_mul_nonpos h k)
    nlinarith [mul_self_nonneg (f α)]
  exact ⟨α, hαab, hfα, hx_lim, hmem, hbound⟩

/-- The arithmetic of the iteration count: if `0 ≤ L`, `0 < ε` and `log₂(L / ε) ≤ n` then
`L / 2 ^ n ≤ ε`. -/
theorem div_two_pow_le_of_logb_le {L ε : ℝ} {n : ℕ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hn : Real.logb 2 (L / ε) ≤ n) : L / 2 ^ n ≤ ε := by
  rcases hL.lt_or_eq with hL | rfl
  · have := (Real.logb_le_iff_le_rpow one_lt_two (div_pos hL hε)).1 hn
    rw [Real.rpow_natCast] at this
    rw [div_le_iff₀ (by positivity)]
    rwa [div_le_iff₀ hε, mul_comm] at this
  · simp [hε.le]

/-- **The iteration count** ([quarteroni2000numerical] (6.9)): for the root `α` of
`exists_tendsto_iterate` and a tolerance `ε > 0`, `|x^{(m)} - α| ≤ ε` as soon as
`log₂((b - a) / ε) ≤ m + 1` — with the sharp bound `(b - a) / 2 ^ (m + 1)`; the book's
`log₂((b - a) / ε) ≤ m` suffices for its weaker `(b - a) / 2 ^ m`. Stated for that root rather than
an arbitrary one, since a bracket may contain several roots. -/
theorem abs_iterate_sub_le_of_le_logb (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b ≤ 0) :
    ∃ α ∈ Icc a b, f α = 0 ∧ Tendsto (iterate f a b) atTop (𝓝 α) ∧
      ∀ (m : ℕ) (ε : ℝ), 0 < ε → Real.logb 2 ((b - a) / ε) ≤ m + 1 →
        |iterate f a b m - α| ≤ ε := by
  obtain ⟨α, hα, hfα, hlim, -, hbound⟩ := exists_tendsto_iterate hab hf h
  refine ⟨α, hα, hfα, hlim, fun m ε hε hm => (hbound m).trans ?_⟩
  exact div_two_pow_le_of_logb_le (sub_nonneg.2 hab) hε (by exact_mod_cast hm)

end Bisection
