import Numlib.Optimization.Complexity.Telescoping
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Recurrences for objective gaps

Let `Γ_k ≥ 0` be the gap `f(x_k) - f_*` of a monotone method whose iterate only changes at the
successful iterations `S` ([cartis2022evaluation], §5.3). For measure-dominated objectives the
guaranteed decrease on successful iterations becomes a power of the gap itself:
* adaptive-regularization-like methods (5.3.11): `c Γ_{k+1}^τ ≤ Γ_k - Γ_{k+1}`
  (`Optimization.IsImplicitGapDecrease`);
* trust-region-like methods (5.3.33): `c Γ_k^τ ≤ Γ_k - Γ_{k+1}`
  (`Optimization.IsExplicitGapDecrease`);
with `c > 0` and `τ = ν/μ > 0`. This file contains the resulting rates and success counts of §5.3
(Lemma 5.3.1, Theorems 5.3.2–5.3.9 and their proofs in Appendix B), stated as "after `N`
successful iterations the gap is at most `ε`", i.e. `Γ_{k+1} ≤ ε` whenever `N ≤ |𝒮_k|`, with
explicit `N`:
* `τ < 1`: `IsImplicitGapDecrease.superlinear`, the two-phase count
  `IsImplicitGapDecrease.le_of_superlinear_count` (`O(log |log ε|)`), and for the explicit
  recurrence finite termination `IsExplicitGapDecrease.eq_zero_of_lt_one`;
* `τ = 1`: `IsImplicitGapDecrease.linear`, `IsImplicitGapDecrease.le_of_linear_count`
  (`O(|log ε|)`);
* `τ > 1`: `IsImplicitGapDecrease.sublinear`, `IsImplicitGapDecrease.le_of_sublinear_count`
  (`O(ε^{-(τ-1)})`), and `Optimization.exists_le_of_halving` for the optimality measure.
The exact count of Theorem 5.3.2 is `Optimization.implicitGapHitIndex`, the hitting time of the
sequence `Optimization.implicitGapSeq` defined by `κ t_{n+1}^τ + t_{n+1} = t_n` (5.3.12).
Finally `Optimization.le_two_pow_two_pow_of_sq` is the doubly exponential count of Lemma 5.4.3.
Helpers for the measure-dominated complexity theorems: `Optimization.frequently_of_density`
(density forces infinitely many successes), `Optimization.exists_le_of_gap_count` and
`Optimization.exists_le_of_gap_count_nat` (measure counts from gap counts, (B.5.11)),
`Optimization.superlinearCountConst` (the additive constant of the superlinear count),
`Optimization.IsImplicitGapDecrease.mul_kappaDom`, and the first-success facts
`Optimization.IsExplicitGapDecrease.mul_rpow_le_one`,
`Optimization.IsExplicitGapDecrease.eq_zero_of_one_le_mul_rpow`.

## Corrections to the book

* (B.5.12): `(1 - t)^α ≤ 1 - α t` and `1 - t^α ≥ α (1 - t)` hold only for `α ∈ (0, 1]`; the
  valid replacement for all `α > 0` is `1 - t^α ≥ min 1 α * (1 - t)`
  (`Optimization.one_sub_rpow_ge`).
  This changes the constant of the sublinear rate (`κdom`, (B.5.14)–(B.5.15)).
* Theorem 5.3.3: the second phase must reach `ω ≤ c^{1/α} ε`, not `ω ≤ ε`.
* The halving argument of Theorem 5.3.5 yields `2 ⌊M⌋₊ + 2` successful iterations.
-/

open Finset Filter Topology

namespace Optimization

/-! ### Elementary inequalities -/

section Elementary

/-- **(B.5.12), corrected.** For `t ∈ [0, 1]` and `α > 0`: `min 1 α * (1 - t) ≤ 1 - t ^ α`.
(The book's `α (1 - t) ≤ 1 - t ^ α` holds only for `α ≤ 1`, see
`Optimization.mul_one_sub_le_one_sub_rpow`; for `α = 2`, `t = 1/2` it fails.) -/
theorem one_sub_rpow_ge {t α : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hα : 0 < α) :
    min 1 α * (1 - t) ≤ 1 - t ^ α := by
  rcases le_total α 1 with hα1 | hα1
  · rw [min_eq_right hα1]
    have := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hα.le hα1
    simp only [add_sub_cancel] at this
    linarith
  · rw [min_eq_left hα1, one_mul]
    have : t ^ α ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge' ht ht1 zero_le_one hα1
    rw [Real.rpow_one] at this
    linarith

/-- (B.5.12) in its valid range: for `t ≥ 0` and `α ∈ [0, 1]`, `α (1 - t) ≤ 1 - t ^ α`. -/
theorem mul_one_sub_le_one_sub_rpow {t α : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    α * (1 - t) ≤ 1 - t ^ α := by
  have := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hα hα1
  simp only [add_sub_cancel] at this
  linarith

/-- (B.5.12) in its valid range: for `t ≤ 1` and `α ∈ [0, 1]`, `(1 - t) ^ α ≤ 1 - α t`. -/
theorem one_sub_rpow_le {t α : ℝ} (ht1 : t ≤ 1) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (1 - t) ^ α ≤ 1 - α * t := by
  have := rpow_one_add_le_one_add_mul_self (s := -t) (by linarith) hα hα1
  rw [← sub_eq_add_neg] at this
  linarith

/-- **Mean-value form** used for the trust-region-like sublinear rate: for `0 < b ≤ a` and
`α > 0`, `α a^{-α-1} (a - b) ≤ b^{-α} - a^{-α}`. -/
theorem mul_rpow_mul_sub_le_rpow_neg_sub {a b α : ℝ} (hb : 0 < b) (hba : b ≤ a) (hα : 0 < α) :
    α * a ^ (-α - 1) * (a - b) ≤ b ^ (-α) - a ^ (-α) := by
  rcases hba.lt_or_eq with hlt | rfl
  · have hcont : ContinuousOn (fun x : ℝ => x ^ (-α)) (Set.Icc b a) := fun x hx =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (hb.trans_le hx.1).ne')).continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo b a, HasDerivAt (fun x : ℝ => x ^ (-α)) (-α * x ^ (-α - 1)) x :=
      fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hb.trans hx.1).ne')
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope _ _ hlt hcont hderiv
    have hξpos : 0 < ξ := hb.trans hξ.1
    have hmono : a ^ (-α - 1) ≤ ξ ^ (-α - 1) :=
      Real.rpow_le_rpow_of_nonpos hξpos hξ.2.le (by linarith)
    have hab : 0 < a - b := sub_pos.2 hlt
    rw [eq_div_iff hab.ne'] at hξeq
    have key : b ^ (-α) - a ^ (-α) = α * ξ ^ (-α - 1) * (a - b) := by linarith
    rw [key]
    have := mul_le_mul_of_nonneg_left hmono (mul_nonneg hα.le hab.le)
    nlinarith
  · simp

end Elementary

/-! ### The recurrences -/

/-- **Implicit gap recurrence** ([cartis2022evaluation], (5.3.11)): `Γ ≥ 0` is unchanged at the
unsuccessful iterations and decreases by at least `c Γ_{k+1}^τ` at the successful ones. -/
structure IsImplicitGapDecrease (Γ : ℕ → ℝ) (S : ℕ → Prop) (c τ : ℝ) : Prop where
  /-- The gaps are nonnegative. -/
  nonneg : ∀ k, 0 ≤ Γ k
  /-- The gap is unchanged at unsuccessful iterations. -/
  eq_of_not : ∀ k, ¬ S k → Γ (k + 1) = Γ k
  /-- The guaranteed decrease at successful iterations. -/
  decrease : ∀ k, S k → c * Γ (k + 1) ^ τ ≤ Γ k - Γ (k + 1)

/-- **Explicit gap recurrence** ([cartis2022evaluation], (5.3.33)): `Γ ≥ 0` is unchanged at the
unsuccessful iterations and decreases by at least `c Γ_k^τ` at the successful ones. -/
structure IsExplicitGapDecrease (Γ : ℕ → ℝ) (S : ℕ → Prop) (c τ : ℝ) : Prop where
  /-- The gaps are nonnegative. -/
  nonneg : ∀ k, 0 ≤ Γ k
  /-- The gap is unchanged at unsuccessful iterations. -/
  eq_of_not : ∀ k, ¬ S k → Γ (k + 1) = Γ k
  /-- The guaranteed decrease at successful iterations. -/
  decrease : ∀ k, S k → c * Γ k ^ τ ≤ Γ k - Γ (k + 1)

variable {Γ : ℕ → ℝ} {S : ℕ → Prop} {c τ : ℝ}

section Generic

/-- Iterates of a map that is monotone and nonnegative on `[0, ∞)` are monotone there. -/
theorem iterate_le_iterate_of_monotoneOn {F : ℝ → ℝ} (hF : ∀ x y, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hF0 : ∀ x, 0 ≤ x → 0 ≤ F x) (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    F^[n] x ≤ F^[n] y := by
  induction n generalizing x y with
  | zero => exact hxy
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (hF0 x hx) (hF x y hx hxy)

theorem iterate_nonneg {F : ℝ → ℝ} (hF0 : ∀ x, 0 ≤ x → 0 ≤ F x) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ F^[n] x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (hF0 x hx)


/-- Monotone bounds propagate along the successful iterations: if `F` is monotone and
nonnegative on `[0, ∞)`, `Γ ≥ 0`, `Γ_{k+1} = Γ_k` at unsuccessful and `Γ_{k+1} ≤ F Γ_k` at
successful iterations, then `Γ_{k+1} ≤ F^{|𝒮_k|} Γ_0`. -/
theorem le_iterate_of_successSet {F : ℝ → ℝ} (hF : ∀ x y, 0 ≤ x → x ≤ y → F x ≤ F y)
    (hF0 : ∀ x, 0 ≤ x → 0 ≤ F x) (hΓ : ∀ k, 0 ≤ Γ k) (heq : ∀ k, ¬ S k → Γ (k + 1) = Γ k)
    (hS : ∀ k, S k → Γ (k + 1) ≤ F (Γ k)) (k : ℕ) :
    Γ (k + 1) ≤ F^[(successSet S k).card] (Γ 0) := by
  induction k with
  | zero =>
    by_cases h0 : S 0
    · rw [successSet_zero_of_succ h0]; simpa using hS 0 h0
    · rw [successSet_zero_of_not_succ h0]; simp [heq 0 h0]
  | succ k ih =>
    by_cases hk : S (k + 1)
    · rw [card_successSet_add_one_of_succ hk, Function.iterate_succ_apply']
      exact (hS _ hk).trans (hF _ _ (hΓ _) ih)
    · rw [card_successSet_add_one_of_not_succ hk, heq _ hk]
      exact ih

/-- Iterates of `x ↦ q x`. -/
theorem iterate_mul_left_apply (q x : ℝ) (n : ℕ) : (fun x => q * x)^[n] x = q ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring

/-- If the number of successful iterations is unbounded (`S` infinite), so is `|𝒮_k|`. -/
theorem exists_le_card_successSet (hS : ∀ N, ∃ k ≥ N, S k) (n : ℕ) :
    ∃ k, n ≤ (successSet S k).card := by
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hk', hSk'⟩ := hS (k + 1)
    refine ⟨k', lt_of_le_of_lt hk (card_lt_card ?_)⟩
    refine (ssubset_iff_of_subset (successSet_mono (by omega))).2 ⟨k', ?_, ?_⟩
    · exact mem_successSet.2 ⟨le_rfl, hSk'⟩
    · intro h; have := (mem_successSet.1 h).1; omega

/-- **Density** ([cartis2022evaluation], (5.3.9), (5.3.15)): if `k ≤ κR |𝒮_k| + κA` for all `k`
(`κR > 0`), then `N ≤ |𝒮_k|` as soon as `κR N + κA ≤ k`. Hence "`Γ_{k+1} ≤ ε` after `N`
successful iterations" holds after `k + 1` iterations whenever `κR N + κA ≤ k`. -/
theorem le_card_of_density {κR κA N : ℝ} (hκR : 0 < κR)
    (h : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA) {k : ℕ}
    (hk : κR * N + κA ≤ k) : N ≤ (successSet S k).card := by
  have := h k
  have : κR * N ≤ κR * (successSet S k).card := by linarith
  exact le_of_mul_le_mul_left this hκR

end Generic

namespace IsImplicitGapDecrease

variable (h : IsImplicitGapDecrease Γ S c τ)
include h

/-- The gaps do not increase (for `c ≥ 0`). -/
theorem le_self (hc : 0 ≤ c) (k : ℕ) : Γ (k + 1) ≤ Γ k := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ c * Γ (k + 1) ^ τ := mul_nonneg hc (Real.rpow_nonneg (h.nonneg _) _)
    linarith
  · exact (h.eq_of_not k hk).le

theorem antitone (hc : 0 ≤ c) : Antitone Γ := antitone_nat_of_succ_le (h.le_self hc)

/-- Telescoping: `Γ_{k+1} = Γ_0 - ∑_{j ∈ 𝒮_k} (Γ_j - Γ_{j+1})`. -/
theorem eq_sub_sum (k : ℕ) :
    Γ (k + 1) = Γ 0 - ∑ j ∈ successSet S k, (Γ j - Γ (j + 1)) := by
  rw [sum_successSet_sub_eq fun j _ hj => h.eq_of_not j hj]; ring

/-- **(5.3.10)**: at a successful iteration, `Γ_{k+1} ≤ Γ_k / (1 + c Γ_{k+1}^{τ-1})` (for
`c ≥ 0`; with Lean's convention `0 ^ x = 0` for `x ≠ 0` this also holds when `Γ_{k+1} = 0`). -/
theorem le_div (hc : 0 ≤ c) {k : ℕ} (hk : S k) :
    Γ (k + 1) ≤ Γ k / (1 + c * Γ (k + 1) ^ (τ - 1)) := by
  have hpos : 0 < 1 + c * Γ (k + 1) ^ (τ - 1) := by
    have := mul_nonneg hc (Real.rpow_nonneg (h.nonneg (k + 1)) (τ - 1)); linarith
  rw [le_div_iff₀ hpos]
  rcases (h.nonneg (k + 1)).lt_or_eq with hΓ | hΓ
  · have hsplit : Γ (k + 1) ^ τ = Γ (k + 1) ^ (τ - 1) * Γ (k + 1) := by
      rw [← Real.rpow_add_one hΓ.ne', sub_add_cancel]
    have := h.decrease k hk
    rw [hsplit] at this
    linarith
  · rw [← hΓ, zero_mul]; exact h.nonneg k

/-- The gaps converge to zero if there are infinitely many successful iterations
([cartis2022evaluation], Lemma 5.3.1). -/
theorem tendsto_zero (hc : 0 < c) (hτ : 0 < τ) (hS : ∀ N, ∃ k ≥ N, S k) :
    Tendsto Γ atTop (𝓝 0) := by
  have hanti := h.antitone hc.le
  have hbdd : BddBelow (Set.range Γ) := ⟨0, by rintro _ ⟨k, rfl⟩; exact h.nonneg k⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ k, Γ k
  have hL0 : 0 ≤ L := le_ciInf h.nonneg
  have hLle : ∀ k, L ≤ Γ k := fun k => ciInf_le hbdd k
  suffices hL : L = 0 by rwa [hL] at hlim
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
  set d := c * L ^ τ
  have hd : 0 < d := mul_pos hc (Real.rpow_pos_of_pos hLpos τ)
  -- every successful iteration decreases `Γ` by at least `d`
  have hdec : ∀ k, S k → d ≤ Γ k - Γ (k + 1) := fun k hk =>
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL0 (hLle _) hτ.le) hc.le).trans
      (h.decrease k hk)
  obtain ⟨n, hn⟩ := exists_nat_gt (Γ 0 / d)
  obtain ⟨k, hk⟩ := exists_le_card_successSet hS n
  have := card_successSet_mul_le_of_decrease (φ := Γ) (succ := S) (k := k) (c := d)
    (fun j _ hj => h.eq_of_not j hj) (fun j _ hj => hdec j hj) (h.nonneg (k + 1))
  have hn' : Γ 0 / d < (successSet S k).card :=
    hn.trans_le (by exact_mod_cast hk)
  rw [div_lt_iff₀ hd] at hn'
  linarith

/-- **Linear rate** ([cartis2022evaluation], Lemma 5.3.1 (ii)): if `τ = 1`, every successful
iteration has `Γ_{k+1} ≤ (1 + c)⁻¹ Γ_k`. -/
theorem linear (hτ : τ = 1) (hc : 0 ≤ c) {k : ℕ} (hk : S k) :
    Γ (k + 1) ≤ (1 + c)⁻¹ * Γ k := by
  have := h.decrease k hk
  rw [hτ, Real.rpow_one] at this
  rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

/-- **Count for the linear case** ([cartis2022evaluation], proof of Theorem 5.3.4): if `τ = 1`,
`c > 0`, `0 < ε` and `0 < Γ_0`, then `Γ_{k+1} ≤ ε` as soon as
`(log Γ_0 - log ε) / log (1 + c) ≤ |𝒮_k|`. -/
theorem le_of_linear_count (hτ : τ = 1) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) (hΓ0 : 0 < Γ 0)
    {k : ℕ} (hk : (Real.log (Γ 0) - Real.log ε) / Real.log (1 + c) ≤ (successSet S k).card) :
    Γ (k + 1) ≤ ε := by
  set q := (1 + c)⁻¹
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hbound := le_iterate_of_successSet (F := fun x => q * x)
    (fun x y _ hxy => mul_le_mul_of_nonneg_left hxy hq0.le)
    (fun x hx => mul_nonneg hq0.le hx) h.nonneg h.eq_of_not
    (fun k hk => h.linear hτ hc.le hk) k
  rw [iterate_mul_left_apply] at hbound
  set n := (successSet S k).card
  refine hbound.trans ?_
  have hlog : 0 < Real.log (1 + c) := Real.log_pos (by linarith)
  rw [div_le_iff₀ hlog] at hk
  rw [← Real.log_le_log_iff (mul_pos (pow_pos hq0 n) hΓ0) hε, Real.log_mul (pow_pos hq0 n).ne'
    hΓ0.ne', Real.log_pow, Real.log_inv]
  linarith

end IsImplicitGapDecrease

namespace IsExplicitGapDecrease

variable (h : IsExplicitGapDecrease Γ S c τ)
include h

/-- The gaps do not increase (for `c ≥ 0`). -/
theorem le_self (hc : 0 ≤ c) (k : ℕ) : Γ (k + 1) ≤ Γ k := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ c * Γ k ^ τ := mul_nonneg hc (Real.rpow_nonneg (h.nonneg _) _)
    linarith
  · exact (h.eq_of_not k hk).le

/-- The explicit recurrence implies the implicit one (for `c ≥ 0`, `τ ≥ 0`). -/
theorem toImplicit (hc : 0 ≤ c) (hτ : 0 ≤ τ) : IsImplicitGapDecrease Γ S c τ where
  nonneg := h.nonneg
  eq_of_not := h.eq_of_not
  decrease k hk := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (h.nonneg _) (h.le_self hc k) hτ) hc).trans (h.decrease k hk)

/-- **(5.3.30)**: at a successful iteration, `Γ_{k+1} ≤ Γ_k (1 - c Γ_k^{τ-1})`. -/
theorem le_mul (hc : 0 ≤ c) {k : ℕ} (hk : S k) :
    Γ (k + 1) ≤ Γ k * (1 - c * Γ k ^ (τ - 1)) := by
  rcases (h.nonneg k).lt_or_eq with hΓ | hΓ
  · have hsplit : Γ k ^ τ = Γ k ^ (τ - 1) * Γ k := by
      rw [← Real.rpow_add_one hΓ.ne', sub_add_cancel]
    have := h.decrease k hk
    rw [hsplit] at this
    linarith
  · have := h.decrease k hk
    have : 0 ≤ c * Γ k ^ τ := mul_nonneg hc (Real.rpow_nonneg (h.nonneg _) _)
    rw [← hΓ, zero_mul]
    linarith

/-- **Count for the linear explicit case** ([cartis2022evaluation], Lemma 5.3.6 (i), proof of
Theorem 5.3.8): if `τ = 1`, `0 < c < 1`, `0 < ε` and `0 < Γ_0`, then `Γ_{k+1} ≤ ε` as soon as
`(log Γ_0 - log ε) / |log (1 - c)| ≤ |𝒮_k|`. -/
theorem le_of_linear_count (hτ : τ = 1) (hc : 0 < c) (hc1 : c < 1) {ε : ℝ} (hε : 0 < ε)
    (hΓ0 : 0 < Γ 0) {k : ℕ}
    (hk : (Real.log (Γ 0) - Real.log ε) / |Real.log (1 - c)| ≤ (successSet S k).card) :
    Γ (k + 1) ≤ ε := by
  set q := 1 - c
  have hq0 : 0 < q := by simp only [q]; linarith
  have hq1 : q < 1 := by simp only [q]; linarith
  have hstep : ∀ k, S k → Γ (k + 1) ≤ q * Γ k := fun k hk => by
    have := h.le_mul hc.le hk
    rw [hτ, sub_self, Real.rpow_zero, mul_one, mul_comm] at this
    exact this
  have hbound := le_iterate_of_successSet (F := fun x => q * x)
    (fun x y _ hxy => mul_le_mul_of_nonneg_left hxy hq0.le)
    (fun x hx => mul_nonneg hq0.le hx) h.nonneg h.eq_of_not hstep k
  rw [iterate_mul_left_apply] at hbound
  set n := (successSet S k).card
  refine hbound.trans ?_
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  rw [abs_of_neg hlog, div_le_iff₀ (by linarith)] at hk
  rw [← Real.log_le_log_iff (mul_pos (pow_pos hq0 n) hΓ0) hε, Real.log_mul (pow_pos hq0 n).ne'
    hΓ0.ne', Real.log_pow]
  linarith

/-- If `τ = 1` and `c ≥ 1`, the gap vanishes after every successful iteration (and `c > 1`
forces `Γ_k = 0` at every successful `k`). -/
theorem eq_zero_of_one_le (hτ : τ = 1) (hc : 1 ≤ c) {k : ℕ} (hk : S k) :
    Γ (k + 1) = 0 ∧ (1 < c → Γ k = 0) := by
  have := h.decrease k hk
  rw [hτ, Real.rpow_one] at this
  have h0 := h.nonneg k
  have h1 := h.nonneg (k + 1)
  refine ⟨by nlinarith, fun hc1 => by nlinarith⟩

end IsExplicitGapDecrease

/-! ### Superlinear and sublinear rates -/

section Iterates

variable {F G : ℝ → ℝ}

/-- If `F ≤ G` on `[0, ∞)`, `G` is monotone there and `F` preserves nonnegativity, then
`F^[n] ≤ G^[n]` on `[0, ∞)`. -/
theorem iterate_le_iterate_of_le (hFG : ∀ x, 0 ≤ x → F x ≤ G x)
    (hG : ∀ x y, 0 ≤ x → x ≤ y → G x ≤ G y) (hF0 : ∀ x, 0 ≤ x → 0 ≤ F x) (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : F^[n] x ≤ G^[n] x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (hFG _ (iterate_nonneg hF0 n hx)).trans (hG _ _ (iterate_nonneg hF0 n hx) ih)

/-- If `F x ≤ x` on `[0, ∞)`, the iterates of `F` decrease. -/
theorem iterate_le_iterate_of_le_self (hF : ∀ x, 0 ≤ x → F x ≤ x)
    (hF0 : ∀ x, 0 ≤ x → 0 ≤ F x) {m n : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    F^[n] x ≤ F^[m] x := by
  have hdec : ∀ d y, 0 ≤ y → F^[d] y ≤ y := by
    intro d
    induction d with
    | zero => intro y _; exact le_rfl
    | succ d ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      exact (hF _ (iterate_nonneg hF0 d hy)).trans (ih y hy)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, Function.iterate_add_apply]
  exact hdec d _ (iterate_nonneg hF0 m hx)

/-- Iterates of `x ↦ x ^ a` on `[0, ∞)`: `x ↦ x ^ (a ^ n)`. -/
theorem iterate_rpow_apply {a x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (fun y : ℝ => y ^ a)^[n] x = x ^ (a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, ← Real.rpow_mul hx, pow_succ]

end Iterates

/-- Lower bounds on `Γ^{-α}` accumulate along the successful iterations: if `Γ ≥ 0` is
nonincreasing, unchanged at unsuccessful iterations, and `d ≤ Γ_{k+1}^{-α} - Γ_k^{-α}` at every
successful `k` with `Γ_{k+1} > 0`, then `Γ_0^{-α} + d |𝒮_k| ≤ Γ_{k+1}^{-α}` whenever
`Γ_{k+1} > 0`. -/
theorem add_mul_card_le_rpow_neg {α d : ℝ} (hΓ : ∀ k, Γ (k + 1) ≤ Γ k)
    (heq : ∀ k, ¬ S k → Γ (k + 1) = Γ k)
    (hstep : ∀ k, S k → 0 < Γ (k + 1) → d ≤ Γ (k + 1) ^ (-α) - Γ k ^ (-α)) (k : ℕ) :
    0 < Γ (k + 1) → Γ 0 ^ (-α) + d * (successSet S k).card ≤ Γ (k + 1) ^ (-α) := by
  induction k with
  | zero =>
    intro hpos
    by_cases h0 : S 0
    · rw [successSet_zero_of_succ h0]
      have := hstep 0 h0 hpos
      simp only [card_singleton, Nat.cast_one, mul_one]
      linarith
    · rw [successSet_zero_of_not_succ h0, heq 0 h0]; simp
  | succ k ih =>
    intro hpos
    by_cases hk : S (k + 1)
    · rw [card_successSet_add_one_of_succ hk]
      have := ih (hpos.trans_le (hΓ _))
      have := hstep _ hk hpos
      push_cast
      linarith
    · rw [card_successSet_add_one_of_not_succ hk, heq _ hk]
      exact ih (by rwa [← heq _ hk])

/-- From `Γ_0^{-α} + d |𝒮_k| ≤ Γ_{k+1}^{-α}` (when `Γ_{k+1} > 0`) to a count:
`Γ_{k+1} ≤ ε` as soon as `(ε^{-α} - Γ_0^{-α}) / d ≤ |𝒮_k|`. -/
theorem le_of_add_mul_card_le_rpow_neg {α d ε : ℝ} (hα : 0 < α) (hd : 0 < d) (hε : 0 < ε)
    {k : ℕ} (hΓ : 0 ≤ Γ (k + 1))
    (hbound : 0 < Γ (k + 1) → Γ 0 ^ (-α) + d * (successSet S k).card ≤ Γ (k + 1) ^ (-α))
    (hk : (ε ^ (-α) - Γ 0 ^ (-α)) / d ≤ (successSet S k).card) : Γ (k + 1) ≤ ε := by
  rcases hΓ.lt_or_eq with hpos | hzero
  · have h1 := hbound hpos
    rw [div_le_iff₀ hd] at hk
    have h2 : ε ^ (-α) ≤ Γ (k + 1) ^ (-α) := by linarith
    exact (Real.rpow_le_rpow_iff_of_neg hε hpos (neg_lt_zero.2 hα)).1 h2
  · rw [← hzero]; exact hε.le

namespace IsImplicitGapDecrease

variable (h : IsImplicitGapDecrease Γ S c τ)
include h

/-- Rescaling: `λ Γ` satisfies the implicit recurrence with constant `c λ^{1-τ}`. -/
theorem const_mul {l : ℝ} (hl : 0 < l) :
    IsImplicitGapDecrease (fun k => l * Γ k) S (c * l ^ (1 - τ)) τ where
  nonneg k := mul_nonneg hl.le (h.nonneg k)
  eq_of_not k hk := by simp only [h.eq_of_not k hk]
  decrease k hk := by
    have := h.decrease k hk
    rw [Real.mul_rpow hl.le (h.nonneg _)]
    have hl' : c * l ^ (1 - τ) * (l ^ τ * Γ (k + 1) ^ τ) = l * (c * Γ (k + 1) ^ τ) := by
      rw [show c * l ^ (1 - τ) * (l ^ τ * Γ (k + 1) ^ τ) = c * (l ^ (1 - τ) * l ^ τ) *
        Γ (k + 1) ^ τ by ring, ← Real.rpow_add hl, sub_add_cancel, Real.rpow_one]
      ring
    rw [hl']
    have := mul_le_mul_of_nonneg_left this hl.le
    linarith

/-- **Superlinear rate** ([cartis2022evaluation], Lemma 5.3.1 (i)): if `0 < τ < 1`, `c > 0` and
there are infinitely many successful iterations, then for every `η > 0` eventually every
successful iteration has `Γ_{k+1} ≤ η Γ_k`. -/
theorem superlinear (hc : 0 < c) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hS : ∀ N, ∃ k ≥ N, S k)
    {η : ℝ} (hη : 0 < η) : ∃ K, ∀ k ≥ K, S k → Γ (k + 1) ≤ η * Γ k := by
  set δ := (c * η) ^ (1 / (1 - τ)) with hδ
  have hcη : 0 < c * η := mul_pos hc hη
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hcη _
  have hδpow : δ ^ (τ - 1) = (c * η)⁻¹ := by
    rw [hδ, ← Real.rpow_mul hcη.le, ← Real.rpow_neg_one]
    congr 1
    field_simp [show (1 : ℝ) - τ ≠ 0 by linarith]
    ring
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((h.tendsto_zero hc hτ0 hS).eventually (ge_mem_nhds hδpos))
  refine ⟨K, fun k hk hSk => ?_⟩
  have hsmall : Γ (k + 1) ≤ δ := hK (k + 1) (by omega)
  rcases (h.nonneg (k + 1)).lt_or_eq with hpos | hzero
  · have hpow : δ ^ (τ - 1) ≤ Γ (k + 1) ^ (τ - 1) :=
      Real.rpow_le_rpow_of_nonpos hpos hsmall (by linarith)
    have hden : η⁻¹ ≤ 1 + c * Γ (k + 1) ^ (τ - 1) := by
      have : c * δ ^ (τ - 1) = η⁻¹ := by rw [hδpow]; field_simp
      have := mul_le_mul_of_nonneg_left hpow hc.le
      linarith
    calc Γ (k + 1) ≤ Γ k / (1 + c * Γ (k + 1) ^ (τ - 1)) := h.le_div hc.le hSk
      _ ≤ Γ k / η⁻¹ := div_le_div_of_nonneg_left (h.nonneg k) (inv_pos.2 hη) hden
      _ = η * Γ k := by rw [div_inv_eq_mul, mul_comm]
  · rw [← hzero]; exact mul_nonneg hη.le (h.nonneg k)

/-- The constant `κdom = min (Γ_0^{-α} c⁻¹ (2^α - 1)) (min 1 α / 2)` of the sublinear rate
(corrected (B.5.14)–(B.5.15), `α = τ - 1`). -/
noncomputable def kappaDom (c α Γ0 : ℝ) : ℝ :=
  min (Γ0 ^ (-α) * c⁻¹ * (2 ^ α - 1)) (min 1 α / 2)

omit h in
theorem kappaDom_pos {α Γ0 : ℝ} (hc : 0 < c) (hα : 0 < α) (hΓ0 : 0 < Γ0) :
    0 < kappaDom c α Γ0 := by
  have h2 : 0 < (2 : ℝ) ^ α - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα; linarith
  exact lt_min (by have := Real.rpow_pos_of_pos hΓ0 (-α); positivity)
    (by have : 0 < min 1 α := lt_min one_pos hα; positivity)

/-- One step of the sublinear analysis ((B.5.13)–(B.5.15), corrected): at a successful iteration
with `Γ_{k+1} > 0` and `τ > 1`, `Γ_{k+1}^{-α} - Γ_k^{-α} ≥ c κdom`. -/
theorem kappaDom_le_sub (hc : 0 < c) (hτ : 1 < τ) {k : ℕ} (hk : S k) (hpos : 0 < Γ (k + 1)) :
    c * kappaDom c (τ - 1) (Γ 0) ≤ Γ (k + 1) ^ (-(τ - 1)) - Γ k ^ (-(τ - 1)) := by
  set α := τ - 1 with hα_def
  have hα : 0 < α := by linarith
  set y := Γ (k + 1)
  set x := Γ k
  have hyx : y ≤ x := h.le_self hc.le k
  have hx : 0 < x := hpos.trans_le hyx
  have hx0 : x ≤ Γ 0 := h.antitone hc.le (Nat.zero_le k)
  have hdec := h.decrease k hk
  rcases le_or_gt y (x / 2) with hhalf | hhalf
  · -- `Γ_{k+1} ≤ Γ_k / 2`
    have h1 : (x / 2) ^ (-α) ≤ y ^ (-α) := Real.rpow_le_rpow_of_nonpos hpos hhalf (by linarith)
    have h2 : (x / 2) ^ (-α) = 2 ^ α * x ^ (-α) := by
      rw [Real.div_rpow hx.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]
    have h3 : Γ 0 ^ (-α) ≤ x ^ (-α) := Real.rpow_le_rpow_of_nonpos hx hx0 (by linarith)
    have h2α : 0 < (2 : ℝ) ^ α - 1 := by
      have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hα; linarith
    calc c * kappaDom c α (Γ 0) ≤ c * (Γ 0 ^ (-α) * c⁻¹ * (2 ^ α - 1)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ = (2 ^ α - 1) * Γ 0 ^ (-α) := by field_simp
      _ ≤ (2 ^ α - 1) * x ^ (-α) := mul_le_mul_of_nonneg_left h3 h2α.le
      _ ≤ y ^ (-α) - x ^ (-α) := by rw [h2] at h1; linarith
  · -- `Γ_{k+1} > Γ_k / 2`: use `one_sub_rpow_ge` with `t = Γ_{k+1} / Γ_k`
    set t := y / x
    have ht0 : 0 ≤ t := div_nonneg hpos.le hx.le
    have ht1 : t ≤ 1 := (div_le_one hx).2 hyx
    have hgt : 1 / 2 < t := by rw [lt_div_iff₀ hx]; linarith
    have hm := one_sub_rpow_ge ht0 ht1 hα
    have hxy : x ^ (-α) = y ^ (-α) * t ^ α := by
      rw [Real.div_rpow hpos.le hx.le, Real.rpow_neg hx.le, Real.rpow_neg hpos.le]
      field_simp
    have hyτ : y ^ (-α) * y ^ τ = y := by
      rw [← Real.rpow_add hpos, hα_def, show -(τ - 1) + τ = 1 by ring, Real.rpow_one]
    have hmin : 0 < min 1 α := lt_min one_pos hα
    have hyα : 0 < y ^ (-α) := Real.rpow_pos_of_pos hpos _
    calc c * kappaDom c α (Γ 0) ≤ c * (min 1 α / 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
      _ ≤ min 1 α * c * t := by have := mul_pos hmin hc; nlinarith
      _ = y ^ (-α) * (min 1 α * (c * y ^ τ / x)) := by
          rw [show y ^ (-α) * (min 1 α * (c * y ^ τ / x)) =
            min 1 α * c * ((y ^ (-α) * y ^ τ) / x) by ring, hyτ]
      _ ≤ y ^ (-α) * (min 1 α * ((x - y) / x)) := by
          gcongr
      _ = y ^ (-α) * (min 1 α * (1 - t)) := by
          rw [sub_div, div_self hx.ne']
      _ ≤ y ^ (-α) * (1 - t ^ α) := mul_le_mul_of_nonneg_left hm hyα.le
      _ = y ^ (-α) - x ^ (-α) := by rw [hxy]; ring

/-- **Sublinear rate** ([cartis2022evaluation], Lemma 5.3.1 (iii), (B.5.14) corrected): if
`τ > 1`, `c > 0` and `Γ_0 > 0`, then with `α = τ - 1`,
`Γ_{k+1} ≤ (Γ_0^{-α} + c κdom |𝒮_k|)^{-1/α}` for all `k`. -/
theorem sublinear (hc : 0 < c) (hτ : 1 < τ) (hΓ0 : 0 < Γ 0) (k : ℕ) :
    Γ (k + 1) ≤
      (Γ 0 ^ (-(τ - 1)) + c * kappaDom c (τ - 1) (Γ 0) * (successSet S k).card) ^
        (-1 / (τ - 1)) := by
  have hα : 0 < τ - 1 := by linarith
  have hbound := add_mul_card_le_rpow_neg (h.le_self hc.le) h.eq_of_not
    (fun k hk hpos => h.kappaDom_le_sub hc hτ hk hpos) k
  rcases (h.nonneg (k + 1)).lt_or_eq with hpos | hzero
  · have hB : 0 < Γ 0 ^ (-(τ - 1)) + c * kappaDom c (τ - 1) (Γ 0) * (successSet S k).card := by
      have := Real.rpow_pos_of_pos hΓ0 (-(τ - 1))
      have := mul_pos hc (kappaDom_pos hc hα hΓ0)
      positivity
    calc Γ (k + 1) = (Γ (k + 1) ^ (-(τ - 1))) ^ (-1 / (τ - 1)) := by
          rw [← Real.rpow_mul hpos.le]
          rw [show -(τ - 1) * (-1 / (τ - 1)) = 1 by field_simp, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hB (hbound hpos) (by
          rw [neg_div]; exact neg_nonpos.2 (div_nonneg zero_le_one hα.le))
  · rw [← hzero]; exact Real.rpow_nonneg (by
      have := Real.rpow_nonneg hΓ0.le (-(τ - 1))
      have := (kappaDom_pos hc hα hΓ0).le
      positivity) _

/-- **Lemma 5.3.1** ([cartis2022evaluation]), the three rates as upper bounds (the recurrence
does not exclude faster or finite convergence): if `c > 0`, `τ > 0` and there are infinitely
many successful iterations, then
* (i) if `τ < 1`, for every `η > 0` eventually every successful iteration has
  `Γ_{k+1} ≤ η Γ_k` (superlinear);
* (ii) if `τ = 1`, every successful iteration has `Γ_{k+1} ≤ (1 + c)⁻¹ Γ_k` (linear);
* (iii) if `τ > 1` and `Γ_0 > 0`, `Γ_{k+1} ≤ (Γ_0^{-α} + c κdom |𝒮_k|)^{-1/α}` with `α = τ - 1`
  (sublinear). -/
theorem rates (hc : 0 < c) (hτ0 : 0 < τ) (hS : ∀ N, ∃ k ≥ N, S k) :
    (τ < 1 → ∀ η, 0 < η → ∃ K, ∀ k ≥ K, S k → Γ (k + 1) ≤ η * Γ k) ∧
      (τ = 1 → ∀ k, S k → Γ (k + 1) ≤ (1 + c)⁻¹ * Γ k) ∧
      (1 < τ → 0 < Γ 0 → ∀ k, Γ (k + 1) ≤
        (Γ 0 ^ (-(τ - 1)) + c * kappaDom c (τ - 1) (Γ 0) * (successSet S k).card) ^
          (-1 / (τ - 1))) :=
  ⟨fun hτ1 _ hη => h.superlinear hc hτ0 hτ1 hS hη, fun hτ _ hk => h.linear hτ hc.le hk,
    fun hτ hΓ0 k => h.sublinear hc hτ hΓ0 k⟩

/-- **Count for the sublinear case** ([cartis2022evaluation], proof of Theorem 5.3.5, corrected):
if `τ > 1`, `c > 0`, `Γ_0 > 0` and `ε > 0`, then with `α = τ - 1`, `Γ_{k+1} ≤ ε` as soon as
`(ε^{-α} - Γ_0^{-α}) / (c κdom) ≤ |𝒮_k|`. -/
theorem le_of_sublinear_count (hc : 0 < c) (hτ : 1 < τ) (hΓ0 : 0 < Γ 0) {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : (ε ^ (-(τ - 1)) - Γ 0 ^ (-(τ - 1))) / (c * kappaDom c (τ - 1) (Γ 0)) ≤
      (successSet S k).card) :
    Γ (k + 1) ≤ ε :=
  le_of_add_mul_card_le_rpow_neg (by linarith)
    (mul_pos hc (kappaDom_pos hc (by linarith) hΓ0)) hε (h.nonneg _)
    (add_mul_card_le_rpow_neg (h.le_self hc.le) h.eq_of_not
      (fun k hk hpos => h.kappaDom_le_sub hc hτ hk hpos) k) hk

end IsImplicitGapDecrease

namespace IsExplicitGapDecrease

variable (h : IsExplicitGapDecrease Γ S c τ)
include h

/-- One step of the trust-region-like sublinear analysis (mean-value theorem): at a successful
iteration with `Γ_{k+1} > 0` and `τ > 1`, `Γ_{k+1}^{-α} - Γ_k^{-α} ≥ α c` (`α = τ - 1`). -/
theorem mul_le_sub (hc : 0 < c) (hτ : 1 < τ) {k : ℕ} (hk : S k) (hpos : 0 < Γ (k + 1)) :
    (τ - 1) * c ≤ Γ (k + 1) ^ (-(τ - 1)) - Γ k ^ (-(τ - 1)) := by
  have hle := h.le_self hc.le k
  have hx : 0 < Γ k := hpos.trans_le hle
  have hmvt := mul_rpow_mul_sub_le_rpow_neg_sub hpos hle (show 0 < τ - 1 by linarith)
  have hdec := h.decrease k hk
  have hpow : Γ k ^ (-(τ - 1) - 1) * Γ k ^ τ = 1 := by
    rw [← Real.rpow_add hx, show -(τ - 1) - 1 + τ = 0 by ring, Real.rpow_zero]
  have hnn : 0 ≤ (τ - 1) * Γ k ^ (-(τ - 1) - 1) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hx.le _)
  calc (τ - 1) * c = (τ - 1) * Γ k ^ (-(τ - 1) - 1) * (c * Γ k ^ τ) := by
        rw [show (τ - 1) * Γ k ^ (-(τ - 1) - 1) * (c * Γ k ^ τ) =
          (τ - 1) * c * (Γ k ^ (-(τ - 1) - 1) * Γ k ^ τ) by ring, hpow, mul_one]
    _ ≤ (τ - 1) * Γ k ^ (-(τ - 1) - 1) * (Γ k - Γ (k + 1)) := mul_le_mul_of_nonneg_left hdec hnn
    _ ≤ _ := hmvt

/-- **Count for the trust-region-like sublinear case** ([cartis2022evaluation], proof of
Theorem 5.3.9): if `τ > 1`, `c > 0` and `ε > 0`, then with `α = τ - 1`, `Γ_{k+1} ≤ ε` as soon as
`(ε^{-α} - Γ_0^{-α}) / (α c) ≤ |𝒮_k|`. -/
theorem le_of_sublinear_count (hc : 0 < c) (hτ : 1 < τ) {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : (ε ^ (-(τ - 1)) - Γ 0 ^ (-(τ - 1))) / ((τ - 1) * c) ≤ (successSet S k).card) :
    Γ (k + 1) ≤ ε :=
  le_of_add_mul_card_le_rpow_neg (by linarith) (mul_pos (by linarith) hc) hε (h.nonneg _)
    (add_mul_card_le_rpow_neg (h.le_self hc.le) h.eq_of_not
      (fun k hk hpos => h.mul_le_sub hc hτ hk hpos) k) hk

end IsExplicitGapDecrease

/-! ### The two-phase count of the superlinear case -/

/-- The number of successful iterations after which the implicit gap with `τ < 1` is at most `ε`
(proof of [cartis2022evaluation], Theorem 5.3.3, corrected). With `α = τ - 1 < 0`, the scaled
gap `ω_0 = c^{1/α} Γ_0`, the scaled tolerance `ε' = c^{1/α} ε` and `q = (1 + ω_0^α)⁻¹`:
`N₁ = ⌈log ω_0 / log (1 + ω_0^α)⌉₊ + 1` successful iterations bring `ω` below `q` (linear
phase), and `N₂ = ⌈(log (log (1/ε')) - log (log (1 + ω_0^α))) / log (1/τ)⌉₊` more bring it below
`ε'` (superlinear phase, `N₂ = 0` if `ε' ≥ 1`). -/
noncomputable def superlinearGapCount (c τ Γ0 ε : ℝ) : ℕ :=
  (⌈Real.log (c ^ (1 / (τ - 1)) * Γ0) /
      Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1))⌉₊ + 1) +
    if c ^ (1 / (τ - 1)) * ε < 1 then
      ⌈(Real.log (Real.log (1 / (c ^ (1 / (τ - 1)) * ε))) -
          Real.log (Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)))) / Real.log (1 / τ)⌉₊
    else 0

namespace IsImplicitGapDecrease

variable (h : IsImplicitGapDecrease Γ S c τ)
include h

/-- **Count for the superlinear case** ([cartis2022evaluation], Theorem 5.3.3, proof in
Appendix B, corrected): if `0 < τ < 1`, `c > 0`, `Γ_0 > 0` and `ε > 0`, then `Γ_{k+1} ≤ ε` as
soon as `superlinearGapCount c τ Γ_0 ε ≤ |𝒮_k|`. -/
theorem le_of_superlinear_count (hc : 0 < c) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hΓ0 : 0 < Γ 0)
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : superlinearGapCount c τ (Γ 0) ε ≤ (successSet S k).card) :
    Γ (k + 1) ≤ ε := by
  set α := τ - 1 with hα_def
  have hα : α < 0 := by linarith
  set l := c ^ (1 / α) with hl_def
  have hl : 0 < l := Real.rpow_pos_of_pos hc _
  -- the scaled gap `ω = l Γ` satisfies the recurrence with constant `1`
  set ω : ℕ → ℝ := fun k => l * Γ k with hω_def
  have hω : IsImplicitGapDecrease ω S 1 τ := by
    have := h.const_mul hl
    have hconst : c * l ^ (1 - τ) = 1 := by
      rw [hl_def, ← Real.rpow_mul hc.le, show 1 / α * (1 - τ) = -1 by
        rw [hα_def]; field_simp [show τ - 1 ≠ 0 by linarith]; ring, Real.rpow_neg_one,
        mul_inv_cancel₀ hc.ne']
    rwa [hconst] at this
  set ω0 := ω 0
  have hω0 : 0 < ω0 := mul_pos hl hΓ0
  set B := 1 + ω0 ^ α
  have hB : 1 < B := by have := Real.rpow_pos_of_pos hω0 α; simp only [B]; linarith
  set q := B⁻¹
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hB
  -- the two one-step bounds
  have hanti := hω.antitone zero_le_one
  have hstep1 : ∀ k, S k → ω (k + 1) ≤ q * ω k := by
    intro k hk
    have hle := hω.le_div zero_le_one hk
    rw [one_mul] at hle
    rcases (hω.nonneg (k + 1)).lt_or_eq with hpos | hzero
    · have hpow : ω0 ^ α ≤ ω (k + 1) ^ α :=
        Real.rpow_le_rpow_of_nonpos hpos (hanti (Nat.zero_le _)) hα.le
      refine hle.trans ?_
      rw [show q * ω k = ω k / B by simp only [q]; ring]
      exact div_le_div_of_nonneg_left (hω.nonneg k) (by linarith) (by simp only [B]; linarith)
    · rw [← hzero]; exact mul_nonneg hq0.le (hω.nonneg k)
  have hstep2 : ∀ k, S k → ω (k + 1) ≤ ω k ^ (1 / τ) := by
    intro k hk
    have hdec := hω.decrease k hk
    have hle : ω (k + 1) ^ τ ≤ ω k := by have := hω.nonneg (k + 1); linarith
    calc ω (k + 1) = (ω (k + 1) ^ τ) ^ (1 / τ) := by
          rw [← Real.rpow_mul (hω.nonneg _), mul_one_div_cancel hτ0.ne', Real.rpow_one]
      _ ≤ ω k ^ (1 / τ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (hω.nonneg _) _) hle (by positivity)
  -- the combined map
  set F : ℝ → ℝ := fun x => min (q * x) (x ^ (1 / τ))
  have hF : ∀ x y, 0 ≤ x → x ≤ y → F x ≤ F y := fun x y hx hxy =>
    min_le_min (mul_le_mul_of_nonneg_left hxy hq0.le) (Real.rpow_le_rpow hx hxy (by positivity))
  have hF0 : ∀ x, 0 ≤ x → 0 ≤ F x := fun x hx =>
    le_min (mul_nonneg hq0.le hx) (Real.rpow_nonneg hx _)
  have hFself : ∀ x, 0 ≤ x → F x ≤ x := fun x hx =>
    (min_le_left _ _).trans (mul_le_of_le_one_left hx hq1.le)
  have hbound := le_iterate_of_successSet hF hF0 hω.nonneg hω.eq_of_not
    (fun k hk => le_min (hstep1 k hk) (hstep2 k hk)) k
  -- the two phases
  set N₁ := ⌈Real.log ω0 / Real.log B⌉₊ + 1
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hphase1 : F^[N₁] ω0 ≤ q := by
    calc F^[N₁] ω0 ≤ (fun x => q * x)^[N₁] ω0 :=
          iterate_le_iterate_of_le (fun x _ => min_le_left _ _)
            (fun x y _ hxy => mul_le_mul_of_nonneg_left hxy hq0.le) hF0 N₁ hω0.le
      _ = q ^ N₁ * ω0 := iterate_mul_left_apply q ω0 N₁
      _ ≤ q := by
          have hceil : Real.log ω0 / Real.log B ≤ ⌈Real.log ω0 / Real.log B⌉₊ := Nat.le_ceil _
          rw [div_le_iff₀ hlogB] at hceil
          have : q ^ ⌈Real.log ω0 / Real.log B⌉₊ * ω0 ≤ 1 := by
            rw [← Real.log_nonpos_iff (by positivity), Real.log_mul (by positivity) hω0.ne',
              Real.log_pow, Real.log_inv]
            linarith
          calc q ^ N₁ * ω0 = q * (q ^ ⌈Real.log ω0 / Real.log B⌉₊ * ω0) := by ring
            _ ≤ q * 1 := mul_le_mul_of_nonneg_left this hq0.le
            _ = q := mul_one q
  have hcount : superlinearGapCount c τ (Γ 0) ε = N₁ +
      if l * ε < 1 then
        ⌈(Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) / Real.log (1 / τ)⌉₊
      else 0 := rfl
  set N₂ := if l * ε < 1 then
      ⌈(Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) / Real.log (1 / τ)⌉₊ else 0
  have hfinal : F^[N₁ + N₂] ω0 ≤ l * ε := by
    rw [add_comm, Function.iterate_add_apply]
    have hy0 : 0 ≤ F^[N₁] ω0 := iterate_nonneg hF0 N₁ hω0.le
    have h2 : F^[N₂] (F^[N₁] ω0) ≤ F^[N₂] q :=
      iterate_le_iterate_of_monotoneOn hF hF0 N₂ hy0 hphase1
    by_cases hε' : l * ε < 1
    · have hN₂ : N₂ = ⌈(Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) /
          Real.log (1 / τ)⌉₊ := ite_eq_left hε'
      have h3 : F^[N₂] q ≤ (fun x : ℝ => x ^ (1 / τ))^[N₂] q :=
        iterate_le_iterate_of_le (fun x _ => min_le_right _ _)
          (fun x y hx hxy => Real.rpow_le_rpow hx hxy (by positivity)) hF0 N₂ hq0.le
      rw [iterate_rpow_apply hq0.le] at h3
      refine h2.trans (h3.trans ?_)
      -- `q ^ ((1/τ)^N₂) ≤ ε'`
      have hε'0 : 0 < l * ε := mul_pos hl hε
      have hA : 0 < Real.log (1 / (l * ε)) :=
        Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hε'0).2 hε')
      have hτlog : 0 < Real.log (1 / τ) :=
        Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hτ0).2 hτ1)
      have hceil := Nat.le_ceil ((Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) /
        Real.log (1 / τ))
      rw [← hN₂, div_le_iff₀ hτlog] at hceil
      have hpow : Real.log (1 / (l * ε)) ≤ (1 / τ) ^ N₂ * Real.log B := by
        rw [← Real.log_le_log_iff hA (by positivity), Real.log_mul (by positivity) hlogB.ne',
          Real.log_pow]
        linarith
      have hlogq : Real.log q = -Real.log B := Real.log_inv B
      rw [Real.rpow_def_of_pos hq0, hlogq, ← Real.exp_log hε'0]
      apply Real.exp_le_exp.2
      rw [one_div, Real.log_inv] at hpow
      linarith
    · have hN₂ : N₂ = 0 := ite_eq_right hε'
      rw [hN₂, Function.iterate_zero_apply]
      push Not at hε'
      linarith
  have hk' : N₁ + N₂ ≤ (successSet S k).card := hcount ▸ hk
  have hω1 : ω (k + 1) ≤ l * ε :=
    hbound.trans ((iterate_le_iterate_of_le_self hFself hF0 hk' hω0.le).trans hfinal)
  exact le_of_mul_le_mul_left hω1 hl

end IsImplicitGapDecrease

/-- **The superlinear count is `O(log |log ε|)`** ([cartis2022evaluation], (5.3.16), constants
of the corrected proof): for `c > 0`, `0 < τ < 1`, `Γ_0 > 0`, `ε > 0`, with `α = τ - 1`,
`ω_0 = c^{1/α} Γ_0`,
`superlinearGapCount c τ Γ_0 ε ≤ log (max 1 |log ε|) / log (1/τ) + κ`, where
`κ = max 0 (log ω_0) / log (1 + ω_0^α) + 2
  + (log (1 + |log c| / |α|) + |log (log (1 + ω_0^α))|) / log (1/τ) + 1`. -/
theorem superlinearGapCount_le {Γ0 ε : ℝ} (hc : 0 < c) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hΓ0 : 0 < Γ0) (hε : 0 < ε) :
    (superlinearGapCount c τ Γ0 ε : ℝ) ≤
      Real.log (max 1 |Real.log ε|) / Real.log (1 / τ) +
        (max 0 (Real.log (c ^ (1 / (τ - 1)) * Γ0)) /
            Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)) + 2 +
          (Real.log (1 + |Real.log c| / |τ - 1|) +
              |Real.log (Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)))|) /
            Real.log (1 / τ) + 1) := by
  set α := τ - 1 with hα_def
  have hα : α < 0 := by linarith
  set l := c ^ (1 / α)
  have hl : 0 < l := Real.rpow_pos_of_pos hc _
  set ω0 := l * Γ0
  have hω0 : 0 < ω0 := mul_pos hl hΓ0
  set B := 1 + ω0 ^ α
  have hB : 1 < B := by have := Real.rpow_pos_of_pos hω0 α; simp only [B]; linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hτlog : 0 < Real.log (1 / τ) := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hτ0).2 hτ1)
  set M := max 1 |Real.log ε|
  have hM1 : 1 ≤ M := le_max_left _ _
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hC : 0 ≤ Real.log (1 + |Real.log c| / |α|) :=
    Real.log_nonneg (by
      have h0 : (0 : ℝ) ≤ |Real.log c| / |α| := by positivity
      linarith)
  -- the first phase
  have hN₁ : ((⌈Real.log ω0 / Real.log B⌉₊ + 1 : ℕ) : ℝ) ≤
      max 0 (Real.log ω0) / Real.log B + 2 := by
    push_cast
    have h1 : (⌈Real.log ω0 / Real.log B⌉₊ : ℝ) < max 0 (Real.log ω0 / Real.log B) + 1 := by
      rcases le_or_gt (Real.log ω0 / Real.log B) 0 with hneg | hpos
      · rw [Nat.ceil_eq_zero.2 hneg, max_eq_left hneg]; norm_num
      · rw [max_eq_right hpos.le]; exact Nat.ceil_lt_add_one hpos.le
    have h2 : max 0 (Real.log ω0 / Real.log B) = max 0 (Real.log ω0) / Real.log B := by
      rw [← max_div_div_right hlogB.le, zero_div]
    linarith
  -- the second phase
  have hrest : (0 : ℝ) ≤ (Real.log M + (Real.log (1 + |Real.log c| / |α|) +
      |Real.log (Real.log B)|)) / Real.log (1 / τ) := by positivity
  have hN₂ : ((if l * ε < 1 then
      ⌈(Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) / Real.log (1 / τ)⌉₊
      else 0 : ℕ) : ℝ) ≤
      (Real.log M + (Real.log (1 + |Real.log c| / |α|) + |Real.log (Real.log B)|)) /
        Real.log (1 / τ) + 1 := by
    split_ifs with hε'
    · have hε'0 : 0 < l * ε := mul_pos hl hε
      set A := Real.log (1 / (l * ε))
      have hA : 0 < A := Real.log_pos (by rw [one_div]; exact (one_lt_inv₀ hε'0).2 hε')
      -- `A ≤ M (1 + |log c| / |α|)`
      have hAeq : A = -Real.log ε - Real.log c / α := by
        simp only [A, one_div, Real.log_inv]
        rw [Real.log_mul hl.ne' hε.ne', Real.log_rpow hc]
        ring
      have hAle : A ≤ M * (1 + |Real.log c| / |α|) := by
        rw [hAeq]
        have h1 : -Real.log ε ≤ M := (neg_le_abs _).trans (le_max_right _ _)
        have h2 : -(Real.log c / α) ≤ |Real.log c| / |α| := by
          rw [← abs_div]; exact neg_le_abs _
        have h3 : |Real.log c| / |α| ≤ M * (|Real.log c| / |α|) :=
          le_mul_of_one_le_left (by positivity) hM1
        nlinarith
      have hlogA : Real.log A ≤ Real.log M + Real.log (1 + |Real.log c| / |α|) := by
        rw [← Real.log_mul (by linarith) (by positivity)]
        exact Real.log_le_log hA hAle
      have hx : (Real.log A - Real.log (Real.log B)) / Real.log (1 / τ) ≤
          (Real.log M + (Real.log (1 + |Real.log c| / |α|) + |Real.log (Real.log B)|)) /
            Real.log (1 / τ) := by
        apply div_le_div_of_nonneg_right _ hτlog.le
        have := neg_le_abs (Real.log (Real.log B))
        linarith
      rcases le_or_gt ((Real.log A - Real.log (Real.log B)) / Real.log (1 / τ)) 0 with hneg | hpos
      · rw [Nat.ceil_eq_zero.2 hneg]; push_cast; linarith
      · exact (Nat.ceil_lt_add_one hpos.le).le.trans (by linarith)
    · push_cast; linarith
  have hdef : superlinearGapCount c τ Γ0 ε = (⌈Real.log ω0 / Real.log B⌉₊ + 1) +
      if l * ε < 1 then
        ⌈(Real.log (Real.log (1 / (l * ε))) - Real.log (Real.log B)) / Real.log (1 / τ)⌉₊
      else 0 := rfl
  rw [hdef, Nat.cast_add]
  have : (Real.log M + (Real.log (1 + |Real.log c| / |α|) + |Real.log (Real.log B)|)) /
      Real.log (1 / τ) = Real.log M / Real.log (1 / τ) +
        (Real.log (1 + |Real.log c| / |α|) + |Real.log (Real.log B)|) / Real.log (1 / τ) := by
    rw [add_div]
  linarith

/-! ### The explicit recurrence with `τ < 1`: finite termination -/

namespace IsExplicitGapDecrease

variable (h : IsExplicitGapDecrease Γ S c τ)
include h

/-- **Finite termination of the explicit recurrence with `τ < 1`** ([cartis2022evaluation],
Lemma 5.3.6 (ii), proof of Theorem 5.3.7). Let `c > 0`, `τ < 1`, `α = τ - 1` and
`Γ□ = c^{-1/α}`.
* Every successful iteration with `Γ_k > 0` has `Γ_k ≥ Γ□`.
* If `Γ_0 > 0` and some iteration is successful, then `Γ_0 ≥ Γ□` (5.3.29).
* With `ω_0 = Γ_0 / Γ□`: if `Γ_0 > 0`, then `Γ_{k+1} = 0` as soon as
  `⌈log ω_0 / |log (1 - ω_0^α)|⌉₊ + 1 ≤ |𝒮_k|`. This is the integer form of the book's real
  bound `log ω_0 / |log (1 - ω_0^α)| + 1` (proof of Theorem 5.3.7); no assumption that there are
  infinitely many successful iterations is needed. -/
theorem eq_zero_of_lt_one (hc : 0 < c) (hτ : τ < 1) :
    (∀ k, S k → 0 < Γ k → c ^ (-1 / (τ - 1)) ≤ Γ k) ∧
      (0 < Γ 0 → ∀ k, S k → c ^ (-1 / (τ - 1)) ≤ Γ 0) ∧
      (0 < Γ 0 → ∀ k, ⌈Real.log (Γ 0 / c ^ (-1 / (τ - 1))) /
          |Real.log (1 - (Γ 0 / c ^ (-1 / (τ - 1))) ^ (τ - 1))|⌉₊ + 1 ≤ (successSet S k).card →
        Γ (k + 1) = 0) := by
  set α := τ - 1 with hα_def
  have hα : α < 0 := by linarith
  set G := c ^ (-1 / α) with hG_def
  have hGpos : 0 < G := Real.rpow_pos_of_pos hc _
  have hGα : G ^ α = c⁻¹ := by
    rw [hG_def, ← Real.rpow_mul hc.le, show -1 / α * α = -1 by field_simp [hα.ne],
      Real.rpow_neg_one]
  -- `c Γ^α = (Γ / Γ□)^α`
  have hscale : ∀ x, 0 < x → (x / G) ^ α = c * x ^ α := fun x hx => by
    rw [Real.div_rpow hx.le hGpos.le, hGα, div_inv_eq_mul, mul_comm]
  have hanti : Antitone Γ := antitone_nat_of_succ_le (h.le_self hc.le)
  -- (a)
  have ha : ∀ k, S k → 0 < Γ k → G ≤ Γ k := by
    intro k hk hpos
    have hle := h.le_mul hc.le hk
    have h1 : c * Γ k ^ α ≤ 1 := by
      have := h.nonneg (k + 1)
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [← hscale _ hpos] at h1
    have : (Γ k / G) ^ α ≤ (1 : ℝ) ^ α := by rwa [Real.one_rpow]
    have := (Real.rpow_le_rpow_iff_of_neg (div_pos hpos hGpos) one_pos hα).1 this
    rwa [one_le_div hGpos] at this
  -- (b)
  have hb : 0 < Γ 0 → ∀ k, S k → G ≤ Γ 0 := by
    classical
    intro hΓ0 k hk
    have hex : ∃ j, S j := ⟨k, hk⟩
    set j := Nat.find hex
    have hj : S j := Nat.find_spec hex
    have hΓj : Γ j = Γ 0 := by
      have : ∀ i ≤ j, Γ i = Γ 0 := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ i ih =>
          intro hi
          rw [h.eq_of_not i (Nat.find_min hex (by omega)), ih (by omega)]
      exact this j le_rfl
    rw [← hΓj]
    exact ha j hj (hΓj ▸ hΓ0)
  refine ⟨ha, hb, fun hΓ0 k hk => ?_⟩
  -- (c)
  set ω0 := Γ 0 / G
  set r := 1 - ω0 ^ α
  have hn1 : 1 ≤ (successSet S k).card := le_add_self.trans hk
  obtain ⟨j0, hj0⟩ := card_pos.1 hn1
  have hSj0 : S j0 := (mem_successSet.1 hj0).2
  have hGΓ0 := hb hΓ0 j0 hSj0
  have hω0 : 1 ≤ ω0 := (one_le_div hGpos).2 hGΓ0
  have hω0α : 0 < ω0 ^ α := Real.rpow_pos_of_pos (by linarith) _
  have hω0α1 : ω0 ^ α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hω0 hα.le
  have hr0 : 0 ≤ r := by simp only [r]; linarith
  have hr1 : r ≤ 1 := by simp only [r]; linarith
  -- one step: `Γ_{j+1} ≤ r Γ_j`
  have hstep : ∀ j, S j → Γ (j + 1) ≤ r * Γ j := by
    intro j hj
    rcases (h.nonneg j).lt_or_eq with hpos | hzero
    · have h1 := h.le_mul hc.le hj
      have h2 : ω0 ^ α ≤ c * Γ j ^ α := by
        rw [← hscale _ hpos]
        exact Real.rpow_le_rpow_of_nonpos (div_pos hpos hGpos)
          (div_le_div_of_nonneg_right (hanti (Nat.zero_le j)) hGpos.le) hα.le
      calc Γ (j + 1) ≤ Γ j * (1 - c * Γ j ^ α) := h1
        _ ≤ Γ j * r := mul_le_mul_of_nonneg_left (by simp only [r]; linarith) hpos.le
        _ = r * Γ j := mul_comm _ _
    · have := h.le_self hc.le j
      rw [← hzero] at this ⊢
      linarith [h.nonneg (j + 1)]
  have hgeo : ∀ i, Γ (i + 1) ≤ r ^ (successSet S i).card * Γ 0 := fun i => by
    have := le_iterate_of_successSet (F := fun x => r * x)
      (fun x y _ hxy => mul_le_mul_of_nonneg_left hxy hr0) (fun x hx => mul_nonneg hr0 hx)
      h.nonneg h.eq_of_not hstep i
    rwa [iterate_mul_left_apply] at this
  -- the value at a successful iteration
  have hatS : ∀ j, S j → Γ j ≤ r ^ ((successSet S j).card - 1) * Γ 0 := by
    intro j hj
    cases j with
    | zero => rw [successSet_zero_of_succ hj]; simp
    | succ i =>
      rw [card_successSet_add_one_of_succ hj, Nat.add_sub_cancel]
      exact hgeo i
  -- `r^{⌈L⌉} Γ_0 ≤ Γ□`
  set L := Real.log ω0 / |Real.log r|
  have hkey : r ^ ⌈L⌉₊ * Γ 0 ≤ G := by
    rcases hr0.lt_or_eq with hrpos | hrzero
    · have hlogr : Real.log r < 0 := Real.log_neg hrpos (by simp only [r]; linarith)
      have hL : 0 ≤ L := div_nonneg (Real.log_nonneg hω0) (abs_nonneg _)
      have h1 : r ^ ⌈L⌉₊ ≤ r ^ L := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge' hr0 hr1 hL (Nat.le_ceil L)
      have h2 : r ^ L = ω0⁻¹ := by
        have hω0pos : 0 < ω0 := by linarith
        rw [Real.rpow_def_of_pos hrpos, ← Real.exp_log (inv_pos.2 hω0pos), Real.log_inv]
        congr 1
        simp only [L]
        rw [abs_of_neg hlogr, mul_div, div_neg, mul_div_cancel_left₀ _ hlogr.ne]
      calc r ^ ⌈L⌉₊ * Γ 0 ≤ ω0⁻¹ * Γ 0 := mul_le_mul_of_nonneg_right (h1.trans h2.le) hΓ0.le
        _ = G := by simp only [ω0]; field_simp
    · have hω01 : ω0 ^ α = 1 := by simp only [r] at hrzero; linarith
      have hω0eq : ω0 = 1 := by
        by_contra hne
        have hgt : 1 < ω0 := lt_of_le_of_ne hω0 (Ne.symm hne)
        have := Real.rpow_lt_one_of_one_lt_of_neg hgt hα
        linarith
      have hLz : L = 0 := by simp only [L, hω0eq, Real.log_one, zero_div]
      rw [hLz, Nat.ceil_zero, pow_zero, one_mul]
      have : Γ 0 = G := by
        have := hω0eq; simp only [ω0] at this; rwa [div_eq_one_iff_eq hGpos.ne'] at this
      exact this.le
  -- conclusion
  by_contra hne
  have hpos : 0 < Γ (k + 1) := lt_of_le_of_ne (h.nonneg _) (Ne.symm hne)
  have hne' : (successSet S k).Nonempty := card_pos.1 hn1
  set j := (successSet S k).max' hne'
  have hjmem := (successSet S k).max'_mem hne'
  obtain ⟨hjk, hSj⟩ := mem_successSet.1 hjmem
  have hcard : (successSet S j).card = (successSet S k).card := by
    congr 1
    refine Subset.antisymm (successSet_mono hjk) fun i hi => ?_
    exact mem_successSet.2 ⟨(successSet S k).le_max' i hi, (mem_successSet.1 hi).2⟩
  have hΓj : Γ j ≤ G := by
    calc Γ j ≤ r ^ ((successSet S j).card - 1) * Γ 0 := hatS j hSj
      _ ≤ r ^ ⌈L⌉₊ * Γ 0 := by
          apply mul_le_mul_of_nonneg_right _ hΓ0.le
          exact pow_le_pow_of_le_one hr0 hr1 (by rw [hcard]; omega)
      _ ≤ G := hkey
  have hjpos : 0 < Γ j := hpos.trans_le (hanti (by omega))
  have hΓjG : Γ j = G := le_antisymm hΓj (ha j hSj hjpos)
  have hzero : Γ (j + 1) ≤ 0 := by
    have := h.le_mul hc.le hSj
    have h1 : c * Γ j ^ α = 1 := by
      rw [← hscale _ hjpos, hΓjG, div_self hGpos.ne', Real.one_rpow]
    rw [h1, sub_self, mul_zero] at this
    exact this
  have := hanti (show j + 1 ≤ k + 1 by omega)
  linarith

end IsExplicitGapDecrease

/-! ### The halving argument for the optimality measure -/

/-- If `n ≥ 1` successful iterations occurred in `[0, k]`, some successful `a ≤ k` is the `n`-th
one: `|𝒮_a| = n`. -/
theorem exists_card_successSet_eq {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ (successSet S k).card) :
    ∃ a ≤ k, S a ∧ (successSet S a).card = n := by
  classical
  have hex : ∃ a, n ≤ (successSet S a).card := ⟨k, hk⟩
  set a := Nat.find hex
  have ha : n ≤ (successSet S a).card := Nat.find_spec hex
  have hak : a ≤ k := Nat.find_min' hex hk
  refine ⟨a, hak, ?_⟩
  cases ha' : a with
  | zero =>
    rw [ha'] at ha
    have h1 : (successSet S 0).card ≤ 1 := card_successSet_le
    have hS0 : S 0 := by
      by_contra hS0
      rw [successSet_zero_of_not_succ hS0] at ha
      simp at ha; omega
    exact ⟨hS0, by omega⟩
  | succ i =>
    rw [ha'] at ha
    have hmin : ¬ n ≤ (successSet S i).card := Nat.find_min hex (by omega)
    have hle : (successSet S (i + 1)).card ≤ (successSet S i).card + 1 :=
      card_successSet_add_one_le
    have hSi : S (i + 1) := by
      by_contra hSi
      rw [card_successSet_add_one_of_not_succ hSi] at ha
      exact hmin ha
    exact ⟨hSi, by omega⟩

/-- **Measure counts from gap rates** ([cartis2022evaluation], proof of Theorem 5.3.5, the
halving argument, corrected). Let `Γ ≥ 0` be unchanged at the unsuccessful iterations, with
`Γ_{k+1} ≤ (A |𝒮_k|)^{-1/α}` whenever `|𝒮_k| ≥ 1` (`A, α > 0`), and let
`κν φ_k^ν ≤ Γ_k - Γ_{k+1}` at the successful iterations (`κν, ν > 0`). Let `ε > 0` and
`M = A^{-1/(α+1)} κν^{-α/(α+1)} ε^{-να/(α+1)}`. If at least `2 (⌊M⌋₊ + 1)` successful iterations
occurred in `[0, k]`, one of the first `2 (⌊M⌋₊ + 1)` of them has `φ_j ≤ ε`. (With
`α = (ν - μ)/μ`, `να/(α+1) = ν - μ`.) -/
theorem exists_le_of_halving {φ : ℕ → ℝ} {A α κν ν ε : ℝ} (hA : 0 < A) (hα : 0 < α)
    (hκν : 0 < κν) (hν : 0 < ν) (hε : 0 < ε) (hΓ : ∀ k, 0 ≤ Γ k)
    (heq : ∀ k, ¬ S k → Γ (k + 1) = Γ k)
    (hrate : ∀ k, 1 ≤ (successSet S k).card →
      Γ (k + 1) ≤ (A * (successSet S k).card) ^ (-1 / α))
    (hdec : ∀ k, S k → κν * φ k ^ ν ≤ Γ k - Γ (k + 1)) {k : ℕ}
    (hk : 2 * (⌊A ^ (-1 / (α + 1)) * κν ^ (-α / (α + 1)) * ε ^ (-ν * α / (α + 1))⌋₊ + 1) ≤
      (successSet S k).card) :
    ∃ j ≤ k, S j ∧
      (successSet S j).card ≤
        2 * (⌊A ^ (-1 / (α + 1)) * κν ^ (-α / (α + 1)) * ε ^ (-ν * α / (α + 1))⌋₊ + 1) ∧
      φ j ≤ ε := by
  set M := A ^ (-1 / (α + 1)) * κν ^ (-α / (α + 1)) * ε ^ (-ν * α / (α + 1))
  set m := ⌊M⌋₊ + 1
  by_contra hcon
  push Not at hcon
  obtain ⟨a, hak, hSa, hca⟩ := exists_card_successSet_eq (S := S) (n := m) (by omega)
    ((by omega : m ≤ 2 * m).trans hk)
  obtain ⟨b, hbk, hSb, hcb⟩ := exists_card_successSet_eq (S := S) (n := 2 * m) (by omega) hk
  have hab : a ≤ b := by
    by_contra hba
    push Not at hba
    have := card_successSet_mono (succ := S) hba.le
    omega
  -- telescoping over the successful iterations in `(a, b]`
  set T := successSet S b \ successSet S a
  have hsub : successSet S a ⊆ successSet S b := successSet_mono hab
  have hT : ∑ j ∈ T, (Γ j - Γ (j + 1)) = Γ (a + 1) - Γ (b + 1) := by
    have h1 := sum_successSet_sub_eq (φ := Γ) (succ := S) (k := b) fun j _ hj => heq j hj
    have h2 := sum_successSet_sub_eq (φ := Γ) (succ := S) (k := a) fun j _ hj => heq j hj
    rw [sum_sdiff_eq_sub hsub, h1, h2]; ring
  have hTcard : T.card = m := by
    rw [card_sdiff_of_subset hsub, hcb, hca]; omega
  have hεν : 0 < ε ^ ν := Real.rpow_pos_of_pos hε ν
  have hTdec : ∀ j ∈ T, κν * ε ^ ν ≤ Γ j - Γ (j + 1) := by
    intro j hj
    obtain ⟨hjb, hja⟩ := mem_sdiff.1 hj
    obtain ⟨hjb', hSj⟩ := mem_successSet.1 hjb
    have hcj : (successSet S j).card ≤ 2 * m := hcb ▸ card_successSet_mono hjb'
    have hφ := hcon j (hjb'.trans hbk) hSj hcj
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le hφ.le hν.le) hκν.le).trans
      (hdec j hSj)
  have hsum : (m : ℝ) * (κν * ε ^ ν) ≤ Γ (a + 1) - Γ (b + 1) := by
    rw [← hT, ← hTcard, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hTdec
  have hra := hrate a (by rw [hca]; omega)
  rw [hca] at hra
  have hupper : (m : ℝ) * (κν * ε ^ ν) ≤ (A * m) ^ (-1 / α) := by
    have := hΓ (b + 1); linarith
  -- but `m > M` makes the left side larger
  set X := κν * ε ^ ν
  have hX : 0 < X := mul_pos hκν hεν
  have hm0 : (0 : ℝ) < m := by positivity
  have hM0 : 0 ≤ M := by positivity
  have hMm : M < m := by simpa [m] using Nat.lt_floor_add_one M
  set e := (α + 1) / α
  have he : 0 < e := by positivity
  have hMe : M ^ e = A ^ (-1 / α) * X⁻¹ := by
    have hα1 : α + 1 ≠ 0 := by linarith
    have e1 : -1 / (α + 1) * e = -1 / α := by simp only [e]; field_simp
    have e2 : -α / (α + 1) * e = -1 := by simp only [e]; field_simp
    have e3 : -ν * α / (α + 1) * e = -ν := by simp only [e]; field_simp
    simp only [M, X]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.rpow_mul hA.le, ← Real.rpow_mul hκν.le, ← Real.rpow_mul hε.le,
      e1, e2, e3, Real.rpow_neg_one, Real.rpow_neg hε.le, mul_inv]
    ring
  have hlt : M ^ e < (m : ℝ) ^ e := Real.rpow_lt_rpow hM0 hMm he
  have hme : (m : ℝ) ^ e = m * (m : ℝ) ^ (1 / α) := by
    rw [show e = 1 + 1 / α by simp only [e]; field_simp, Real.rpow_add hm0, Real.rpow_one]
  have hAm : (A * m) ^ (-1 / α) = A ^ (-1 / α) * (m : ℝ) ^ (-1 / α) :=
    Real.mul_rpow hA.le hm0.le
  have hinv : (m : ℝ) ^ (1 / α) * (m : ℝ) ^ (-1 / α) = 1 := by
    rw [← Real.rpow_add hm0, show 1 / α + -1 / α = 0 by ring, Real.rpow_zero]
  rw [hMe, hme] at hlt
  have : A ^ (-1 / α) * (m : ℝ) ^ (-1 / α) < m * X := by
    have h1 : A ^ (-1 / α) < m * (m : ℝ) ^ (1 / α) * X := by
      rwa [← div_eq_mul_inv, div_lt_iff₀ hX] at hlt
    have h2 := mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hm0 (-1 / α))
    calc A ^ (-1 / α) * (m : ℝ) ^ (-1 / α) < m * (m : ℝ) ^ (1 / α) * X * (m : ℝ) ^ (-1 / α) := h2
      _ = m * X * ((m : ℝ) ^ (1 / α) * (m : ℝ) ^ (-1 / α)) := by ring
      _ = m * X := by rw [hinv, mul_one]
  rw [← hAm] at this
  linarith

/-! ### The implicit gap sequence (5.3.12) -/

section ImplicitGapSeq

variable {κ : ℝ}

/-- `t ↦ κ t^τ + t` is strictly increasing on `[0, ∞)` for `κ ≥ 0`, `τ > 0`. -/
theorem add_rpow_lt_add_rpow (hκ : 0 ≤ κ) (hτ : 0 < τ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    κ * s ^ τ + s < κ * t ^ τ + t := by
  have := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs hst.le hτ.le) hκ
  linarith

/-- For `y ≥ 0` there is `t ≥ 0` with `κ t^τ + t = y` (intermediate value theorem). -/
theorem exists_add_rpow_eq (hκ : 0 ≤ κ) (hτ : 0 < τ) {y : ℝ} (hy : 0 ≤ y) :
    ∃ t, 0 ≤ t ∧ κ * t ^ τ + t = y := by
  have hcont : ContinuousOn (fun t : ℝ => κ * t ^ τ + t) (Set.Icc 0 y) :=
    ((continuous_const.mul (Real.continuous_rpow_const hτ.le)).add continuous_id).continuousOn
  have hmem : y ∈ Set.Icc ((fun t : ℝ => κ * t ^ τ + t) 0) ((fun t : ℝ => κ * t ^ τ + t) y) := by
    simp only [Real.zero_rpow hτ.ne', mul_zero, add_zero, Set.mem_Icc]
    exact ⟨hy, le_add_of_nonneg_left (mul_nonneg hκ (Real.rpow_nonneg hy τ))⟩
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hy hcont hmem
  exact ⟨t, ht.1, hteq⟩

open Classical in
/-- One step of the recurrence (5.3.12): for `y ≥ 0`, the unique `t ≥ 0` with `κ t^τ + t = y`
(`κ ≥ 0`, `τ > 0`; the value `0` is used when no such `t` exists). -/
noncomputable def implicitGapStep (κ τ y : ℝ) : ℝ :=
  if h : ∃ t, 0 ≤ t ∧ κ * t ^ τ + t = y then h.choose else 0

theorem implicitGapStep_spec (hκ : 0 ≤ κ) (hτ : 0 < τ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ implicitGapStep κ τ y ∧ κ * implicitGapStep κ τ y ^ τ + implicitGapStep κ τ y = y := by
  have hex := exists_add_rpow_eq hκ hτ hy
  rw [implicitGapStep, dite_eq_left hex]
  exact hex.choose_spec

theorem implicitGapStep_nonneg (κ τ y : ℝ) : 0 ≤ implicitGapStep κ τ y := by
  unfold implicitGapStep
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

/-- `implicitGapStep κ τ y` is the only `t ≥ 0` with `κ t^τ + t = y`. -/
theorem eq_implicitGapStep_iff (hκ : 0 ≤ κ) (hτ : 0 < τ) {y t : ℝ} (hy : 0 ≤ y) (ht : 0 ≤ t) :
    t = implicitGapStep κ τ y ↔ κ * t ^ τ + t = y := by
  obtain ⟨h0, heq⟩ := implicitGapStep_spec hκ hτ hy
  refine ⟨fun h => h ▸ heq, fun h => ?_⟩
  rcases lt_trichotomy t (implicitGapStep κ τ y) with hlt | heq' | hgt
  · have := add_rpow_lt_add_rpow hκ hτ ht hlt; linarith
  · exact heq'
  · have := add_rpow_lt_add_rpow hκ hτ h0 hgt; linarith

/-- If `t ≥ 0` and `κ t^τ + t ≤ y`, then `t ≤ implicitGapStep κ τ y`. -/
theorem le_implicitGapStep (hκ : 0 ≤ κ) (hτ : 0 < τ) {y t : ℝ} (ht : 0 ≤ t)
    (h : κ * t ^ τ + t ≤ y) : t ≤ implicitGapStep κ τ y := by
  have hy : 0 ≤ y := le_trans (by have := Real.rpow_nonneg ht τ; positivity) h
  obtain ⟨h0, heq⟩ := implicitGapStep_spec hκ hτ hy
  by_contra hlt
  push Not at hlt
  have := add_rpow_lt_add_rpow hκ hτ h0 hlt
  linarith

theorem implicitGapStep_mono (hκ : 0 ≤ κ) (hτ : 0 < τ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    implicitGapStep κ τ x ≤ implicitGapStep κ τ y :=
  le_implicitGapStep hκ hτ (implicitGapStep_nonneg κ τ x)
    ((implicitGapStep_spec hκ hτ hx).2.le.trans hxy)

/-- **The sequence (5.3.12)** ([cartis2022evaluation]): `t_0 = t₀` and `t_{n+1}` is the unique
`t ≥ 0` with `κ t^τ + t = t_n`. -/
noncomputable def implicitGapSeq (κ τ t₀ : ℝ) : ℕ → ℝ
  | 0 => t₀
  | n + 1 => implicitGapStep κ τ (implicitGapSeq κ τ t₀ n)

@[simp] theorem implicitGapSeq_zero (κ τ t₀ : ℝ) : implicitGapSeq κ τ t₀ 0 = t₀ := rfl

@[simp] theorem implicitGapSeq_succ (κ τ t₀ : ℝ) (n : ℕ) :
    implicitGapSeq κ τ t₀ (n + 1) = implicitGapStep κ τ (implicitGapSeq κ τ t₀ n) := rfl

theorem implicitGapSeq_eq_iterate (κ τ t₀ : ℝ) (n : ℕ) :
    implicitGapSeq κ τ t₀ n = (implicitGapStep κ τ)^[n] t₀ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [implicitGapSeq_succ, ih, Function.iterate_succ_apply']

theorem implicitGapSeq_nonneg {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (n : ℕ) : 0 ≤ implicitGapSeq κ τ t₀ n := by
  cases n with
  | zero => exact ht₀
  | succ n => exact implicitGapStep_nonneg _ _ _

/-- The recurrence (5.3.12): `κ t_{n+1}^τ + t_{n+1} = t_n`. -/
theorem implicitGapSeq_rec (hκ : 0 ≤ κ) (hτ : 0 < τ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (n : ℕ) :
    κ * implicitGapSeq κ τ t₀ (n + 1) ^ τ + implicitGapSeq κ τ t₀ (n + 1) =
      implicitGapSeq κ τ t₀ n :=
  (implicitGapStep_spec hκ hτ (implicitGapSeq_nonneg ht₀ n)).2

/-- The sequence (5.3.12) satisfies the implicit recurrence (with equality) at every index. -/
theorem isImplicitGapDecrease_implicitGapSeq (hκ : 0 ≤ κ) (hτ : 0 < τ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    IsImplicitGapDecrease (implicitGapSeq κ τ t₀) (fun _ => True) κ τ where
  nonneg := implicitGapSeq_nonneg ht₀
  eq_of_not _ h := absurd trivial h
  decrease n _ := by have := implicitGapSeq_rec hκ hτ ht₀ n; linarith

theorem implicitGapSeq_antitone (hκ : 0 ≤ κ) (hτ : 0 < τ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Antitone (implicitGapSeq κ τ t₀) :=
  (isImplicitGapDecrease_implicitGapSeq hκ hτ ht₀).antitone hκ

theorem implicitGapSeq_pos (hκ : 0 ≤ κ) (hτ : 0 < τ) {t₀ : ℝ} (ht₀ : 0 < t₀) (n : ℕ) :
    0 < implicitGapSeq κ τ t₀ n := by
  induction n with
  | zero => exact ht₀
  | succ n ih =>
    rcases (implicitGapSeq_nonneg ht₀.le (κ := κ) (τ := τ) (n + 1)).lt_or_eq with h | h
    · exact h
    · have := implicitGapSeq_rec hκ hτ ht₀.le n
      rw [← h, Real.zero_rpow hτ.ne'] at this
      linarith

theorem tendsto_implicitGapSeq (hκ : 0 < κ) (hτ : 0 < τ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    Tendsto (implicitGapSeq κ τ t₀) atTop (𝓝 0) :=
  (isImplicitGapDecrease_implicitGapSeq hκ.le hτ ht₀).tendsto_zero hκ hτ
    fun N => ⟨N, le_rfl, trivial⟩

open Classical in
/-- **The count `Υ_{κ,τ}(t₀, ε)` of (5.3.13)**: the smallest `n` with `t_n ≤ ε` (`0` if there
is none, which does not happen for `κ, τ, ε > 0`, `t₀ ≥ 0`). -/
noncomputable def implicitGapHitIndex (κ τ t₀ ε : ℝ) : ℕ :=
  if h : ∃ n, implicitGapSeq κ τ t₀ n ≤ ε then Nat.find h else 0

theorem exists_implicitGapSeq_le (hκ : 0 < κ) (hτ : 0 < τ) {t₀ ε : ℝ} (ht₀ : 0 ≤ t₀)
    (hε : 0 < ε) : ∃ n, implicitGapSeq κ τ t₀ n ≤ ε :=
  ((tendsto_implicitGapSeq hκ hτ ht₀).eventually (ge_mem_nhds hε)).exists

theorem implicitGapSeq_hitIndex_le (hκ : 0 < κ) (hτ : 0 < τ) {t₀ ε : ℝ} (ht₀ : 0 ≤ t₀)
    (hε : 0 < ε) : implicitGapSeq κ τ t₀ (implicitGapHitIndex κ τ t₀ ε) ≤ ε := by
  classical
  have hex := exists_implicitGapSeq_le hκ hτ ht₀ hε
  rw [implicitGapHitIndex, dite_eq_left hex]
  exact Nat.find_spec hex

theorem lt_implicitGapSeq_of_lt_hitIndex {t₀ ε : ℝ} {n : ℕ}
    (hn : n < implicitGapHitIndex κ τ t₀ ε) : ε < implicitGapSeq κ τ t₀ n := by
  classical
  unfold implicitGapHitIndex at hn
  split_ifs at hn with hex
  · exact not_le.1 (Nat.find_min hex hn)
  · omega

end ImplicitGapSeq

/-- **Comparison with the sequence (5.3.12)** ([cartis2022evaluation], proof of
Theorem 5.3.2): if `Γ` satisfies the implicit recurrence with `c > 0`, `τ > 0`, then
`Γ_{k+1} ≤ t_{|𝒮_k|}` for the sequence `t = implicitGapSeq c τ Γ_0`. Hence `Γ_{k+1} ≤ ε` as soon
as `implicitGapHitIndex c τ Γ_0 ε ≤ |𝒮_k|` (`ε > 0`), which is Theorem 5.3.2. -/
theorem IsImplicitGapDecrease.le_implicitGapSeq (h : IsImplicitGapDecrease Γ S c τ)
    (hc : 0 < c) (hτ : 0 < τ) :
    (∀ k, Γ (k + 1) ≤ implicitGapSeq c τ (Γ 0) (successSet S k).card) ∧
      ∀ ε, 0 < ε → ∀ k, implicitGapHitIndex c τ (Γ 0) ε ≤ (successSet S k).card →
        Γ (k + 1) ≤ ε := by
  have hmain : ∀ k, Γ (k + 1) ≤ implicitGapSeq c τ (Γ 0) (successSet S k).card := by
    intro k
    rw [implicitGapSeq_eq_iterate]
    refine le_iterate_of_successSet (fun x y hx hxy => implicitGapStep_mono hc.le hτ hx hxy)
      (fun x _ => implicitGapStep_nonneg _ _ x) h.nonneg h.eq_of_not (fun k hk => ?_) k
    exact le_implicitGapStep hc.le hτ (h.nonneg _) (by have := h.decrease k hk; linarith)
  refine ⟨hmain, fun ε hε k hk => (hmain k).trans ?_⟩
  exact (implicitGapSeq_antitone hc.le hτ (h.nonneg 0) hk).trans
    (implicitGapSeq_hitIndex_le hc hτ (h.nonneg 0) hε)

/-! ### The doubly exponential count -/

/-- **Lemma 5.4.3** ([cartis2022evaluation], (5.4.15)). If `0 ≤ u_{k+1} ≤ u_k^2 / ζ` and
`u_0 ≤ ζ / 2` (`ζ > 0`), then `u_n ≤ ζ / 2^{2^n}`; hence `u_n ≤ ε` for every
`n ≥ ⌈log₂ (log₂ (ζ / ε))⌉₊` when `0 < ε < ζ`, and for every `n` when `ζ / 2 ≤ ε`. -/
theorem le_two_pow_two_pow_of_sq {u : ℕ → ℝ} {ζ : ℝ} (hζ : 0 < ζ) (hu : ∀ k, 0 ≤ u k)
    (hrec : ∀ k, u (k + 1) ≤ u k ^ 2 / ζ) (h0 : u 0 ≤ ζ / 2) :
    (∀ n, u n ≤ ζ / 2 ^ 2 ^ n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, (ζ / 2 ≤ ε ∨ ⌈Real.logb 2 (Real.logb 2 (ζ / ε))⌉₊ ≤ n) →
        u n ≤ ε := by
  have hmain : ∀ n, u n ≤ ζ / 2 ^ 2 ^ n := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      calc u (n + 1) ≤ u n ^ 2 / ζ := hrec n
        _ ≤ (ζ / 2 ^ 2 ^ n) ^ 2 / ζ := by gcongr; exact hu n
        _ = ζ / 2 ^ 2 ^ (n + 1) := by
          rw [pow_succ 2 n, pow_mul]; field_simp
  refine ⟨hmain, fun ε hε n hn => (hmain n).trans ?_⟩
  rcases hn with hn | hn
  · calc ζ / 2 ^ 2 ^ n ≤ ζ / 2 := by
          gcongr
          calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ 2 ^ n := pow_le_pow_right₀ one_le_two (Nat.one_le_two_pow)
      _ ≤ ε := hn
  · rcases le_or_gt (ζ / 2) ε with hle | hlt
    · calc ζ / 2 ^ 2 ^ n ≤ ζ / 2 := by
            gcongr
            calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ 2 ^ n := pow_le_pow_right₀ one_le_two (Nat.one_le_two_pow)
        _ ≤ ε := hle
    · have hr : 2 < ζ / ε := by rw [lt_div_iff₀ hε]; linarith
      have hlog1 : 1 < Real.logb 2 (ζ / ε) := by
        rw [Real.lt_logb_iff_rpow_lt one_lt_two (by linarith)]; simpa using hr
      have h2n : Real.logb 2 (Real.logb 2 (ζ / ε)) ≤ n :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h2n' : Real.logb 2 (ζ / ε) ≤ 2 ^ n := by
        rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith)] at h2n
        exact_mod_cast h2n.trans (by rw [Real.rpow_natCast]; push_cast; rfl)
      have h3 : ζ / ε ≤ 2 ^ 2 ^ n := by
        rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith)] at h2n'
        exact_mod_cast h2n'.trans (by rw [← Real.rpow_natCast]; norm_cast)
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at h3
      linarith

/-! ### Helpers for measure-dominated complexity counts -/

/-! ### Density and measure counts -/

section Counting

variable {Γ : ℕ → ℝ} {S : ℕ → Prop}


/-- The density (5.3.9) forces infinitely many successful iterations. -/
theorem frequently_of_density {κR κA : ℝ} (hκR : 0 ≤ κR)
    (h : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA) : ∀ N, ∃ k ≥ N, S k := by
  intro N
  by_contra hcon
  push Not at hcon
  have hcard : ∀ k, (successSet S k).card ≤ N := fun k => by
    calc (successSet S k).card ≤ (Finset.range N).card := by
          refine Finset.card_le_card fun j hj => ?_
          rw [mem_successSet] at hj
          exact Finset.mem_range.2 (lt_of_not_ge fun hjN => hcon j hjN hj.2)
      _ = N := Finset.card_range N
  obtain ⟨k, hk⟩ := exists_nat_gt (κR * N + κA)
  have h1 := h k
  have h2 : κR * ((successSet S k).card : ℝ) ≤ κR * N :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard k) hκR
  linarith

/-- **Measure counts from gap counts** (the step (B.5.11) of [cartis2022evaluation], Appendix B):
let `Γ ≥ 0` with infinitely many successful iterations, `Γ_{k+1} ≤ ε` whenever `N ≤ |𝒮_k|`, and
`κν φ_k^ν ≤ Γ_k - Γ_{k+1}` at the successful `k`. Then some successful `k` has
`κν φ_k^ν ≤ ε` and `|𝒮_k| ≤ max N 0 + 2`. -/
theorem exists_le_of_gap_count {φ : ℕ → ℝ} {κν ν ε N : ℝ} (hΓ : ∀ k, 0 ≤ Γ k)
    (hS : ∀ M, ∃ k ≥ M, S k) (hcount : ∀ k, N ≤ (successSet S k).card → Γ (k + 1) ≤ ε)
    (hdec : ∀ k, S k → κν * φ k ^ ν ≤ Γ k - Γ (k + 1)) :
    ∃ k, S k ∧ κν * φ k ^ ν ≤ ε ∧ ((successSet S k).card : ℝ) ≤ max N 0 + 2 := by
  set n := max 2 (⌈N⌉₊ + 1) with hn
  obtain ⟨k₀, hk₀⟩ := exists_le_card_successSet hS n
  obtain ⟨a, -, hSa, hcard⟩ := exists_card_successSet_eq (by omega) hk₀
  have ha : a ≠ 0 := by
    rintro rfl
    have : (successSet S 0).card ≤ 1 := card_successSet_le
    omega
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  have hcb : (successSet S b).card + 1 = n := by
    rw [← card_successSet_add_one_of_succ hSa, hcard]
  have hNb : N ≤ (successSet S b).card := by
    have h1 : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
    have h2 : ⌈N⌉₊ ≤ (successSet S b).card := by omega
    exact h1.trans (by exact_mod_cast h2)
  refine ⟨b + 1, hSa, ?_, ?_⟩
  · have := hdec _ hSa
    have := hcount b hNb
    have := hΓ (b + 1 + 1)
    linarith
  · rw [hcard]
    rcases le_total 2 (⌈N⌉₊ + 1) with h | h
    · rw [hn, max_eq_right h]
      have := Nat.ceil_lt_add_one (le_max_right N 0)
      have h3 : (⌈N⌉₊ : ℝ) ≤ ⌈max N 0⌉₊ := by exact_mod_cast Nat.ceil_mono (le_max_left _ _)
      push_cast
      linarith
    · rw [hn, max_eq_left h]
      have := le_max_right N 0
      push_cast
      linarith

/-- **Measure counts from gap counts, integer form** (the step (B.5.11) of [cartis2022evaluation],
Appendix B): let `Γ ≥ 0` with infinitely many successful iterations, `Γ_{k+1} ≤ ε` whenever
`n ≤ |𝒮_k|` (`n` a natural number), and `κν φ_k^ν ≤ Γ_k - Γ_{k+1}` at the successful `k`. Then
some successful `k` has `κν φ_k^ν ≤ ε` and `|𝒮_k| ≤ max n 1 + 1` (one successful iteration
more than the gap count). -/
theorem exists_le_of_gap_count_nat {φ : ℕ → ℝ} {κν ν ε : ℝ} {n : ℕ} (hΓ : ∀ k, 0 ≤ Γ k)
    (hS : ∀ M, ∃ k ≥ M, S k) (hcount : ∀ k, n ≤ (successSet S k).card → Γ (k + 1) ≤ ε)
    (hdec : ∀ k, S k → κν * φ k ^ ν ≤ Γ k - Γ (k + 1)) :
    ∃ k, S k ∧ κν * φ k ^ ν ≤ ε ∧ (successSet S k).card ≤ max n 1 + 1 := by
  obtain ⟨k₀, hk₀⟩ := exists_le_card_successSet hS (max n 1 + 1)
  obtain ⟨a, -, hSa, hcard⟩ := exists_card_successSet_eq (by omega) hk₀
  have ha : a ≠ 0 := by
    rintro rfl
    have : (successSet S 0).card ≤ 1 := card_successSet_le
    omega
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  have hcb : (successSet S b).card + 1 = max n 1 + 1 := by
    rw [← card_successSet_add_one_of_succ hSa, hcard]
  refine ⟨b + 1, hSa, ?_, hcard.le⟩
  have := hdec _ hSa
  have := hcount b (by omega)
  have := hΓ (b + 1 + 1)
  linarith

end Counting

/-- The additive constant of the superlinear count (`superlinearGapCount_le`; `κ^F_{AR,gap,1}`
of Theorem 5.3.3 of [cartis2022evaluation], corrected): with `α = τ - 1` and `ω_0 = c^{1/α} Γ_0`,
`max(0, log ω_0)/log(1 + ω_0^α) + 2 + (log(1 + |log c|/|α|) + |log log(1 + ω_0^α)|)/log(1/τ)`
`+ 1`. -/
noncomputable def superlinearCountConst (c τ Γ0 : ℝ) : ℝ :=
  max 0 (Real.log (c ^ (1 / (τ - 1)) * Γ0)) /
      Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)) + 2 +
    (Real.log (1 + |Real.log c| / |τ - 1|) +
        |Real.log (Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)))|) /
      Real.log (1 / τ) + 1

theorem superlinearCountConst_nonneg {c τ Γ0 : ℝ} (hc : 0 ≤ c) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hΓ0 : 0 ≤ Γ0) : 0 ≤ superlinearCountConst c τ Γ0 := by
  have h1 : 0 ≤ (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1) :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hc _) hΓ0) _
  have h2 : 0 ≤ Real.log (1 + (c ^ (1 / (τ - 1)) * Γ0) ^ (τ - 1)) :=
    Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (1 + |Real.log c| / |τ - 1|) := Real.log_nonneg (by
    have : 0 ≤ |Real.log c| / |τ - 1| := by positivity
    linarith)
  have h4 : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ0]; linarith)
  unfold superlinearCountConst
  have := le_max_left 0 (Real.log (c ^ (1 / (τ - 1)) * Γ0))
  positivity

/-- `superlinearGapCount_le` with the constant `superlinearCountConst`. -/
theorem superlinearGapCount_le_const {c τ Γ0 ε : ℝ} (hc : 0 < c) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hΓ0 : 0 < Γ0) (hε : 0 < ε) :
    (superlinearGapCount c τ Γ0 ε : ℝ) ≤
      Real.log (max 1 |Real.log ε|) / Real.log (1 / τ) + superlinearCountConst c τ Γ0 := by
  have := superlinearGapCount_le (Γ0 := Γ0) hc hτ0 hτ1 hΓ0 hε
  rw [superlinearCountConst]; linarith

/-- `c κdom = min(Γ_0^{-α} (2^α - 1), min(1, α) c / 2)` for `c > 0`. -/
theorem IsImplicitGapDecrease.mul_kappaDom {c α Γ0 : ℝ} (hc : 0 < c) :
    c * IsImplicitGapDecrease.kappaDom c α Γ0 =
      min (Γ0 ^ (-α) * (2 ^ α - 1)) (min 1 α * c / 2) := by
  rw [IsImplicitGapDecrease.kappaDom, mul_min_of_nonneg _ _ hc.le]
  congr 1
  · field_simp
  · ring

section ExplicitFirst

variable {Γ : ℕ → ℝ} {S : ℕ → Prop} {c τ : ℝ}

/-- Before the first successful iteration the gap is unchanged. -/
theorem IsExplicitGapDecrease.eq_of_le_first (hg : IsExplicitGapDecrease Γ S c τ) {k₁ : ℕ}
    (hfirst : ∀ j < k₁, ¬ S j) : ∀ j ≤ k₁, Γ j = Γ 0 := by
  intro j
  induction j with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro hj
    rw [hg.eq_of_not j (hfirst j (by omega)), ih (by omega)]

/-- At the first successful iteration, `0 ≤ Γ_{k₁+1} ≤ Γ_0 (1 - c Γ_0^{τ-1})`; hence
`c Γ_0^{τ-1} ≤ 1` when `Γ_0 > 0`. -/
theorem IsExplicitGapDecrease.mul_rpow_le_one (hg : IsExplicitGapDecrease Γ S c τ) (hc : 0 ≤ c)
    (hS : ∃ k, S k) (hΓ0 : 0 < Γ 0) : c * Γ 0 ^ (τ - 1) ≤ 1 := by
  classical
  have hk := Nat.find_spec hS
  have h0 := hg.eq_of_le_first (fun j hj => Nat.find_min hS hj) _ le_rfl
  have h1 := hg.le_mul hc hk
  have h2 := hg.nonneg (Nat.find hS + 1)
  rw [h0] at h1
  by_contra hcon
  push Not at hcon
  nlinarith

/-- If `c Γ_0^{τ-1} ≥ 1` (and `Γ_0 > 0`), the gap vanishes after every successful iteration. -/
theorem IsExplicitGapDecrease.eq_zero_of_one_le_mul_rpow (hg : IsExplicitGapDecrease Γ S c τ) (hc : 0 ≤ c)
    (hΓ0 : 0 < Γ 0) (h1 : 1 ≤ c * Γ 0 ^ (τ - 1)) : ∀ k, S k → Γ (k + 1) = 0 := by
  classical
  intro k hk
  have hS : ∃ k, S k := ⟨k, hk⟩
  set k₁ := Nat.find hS
  have hk₁ : k₁ ≤ k := Nat.find_min' hS hk
  have h0 := hg.eq_of_le_first (fun j hj => Nat.find_min hS hj) _ le_rfl
  have hle := hg.le_mul hc (Nat.find_spec hS)
  rw [h0] at hle
  have hz : Γ (k₁ + 1) ≤ 0 := hle.trans (by nlinarith)
  have hanti : Antitone Γ := antitone_nat_of_succ_le (hg.le_self hc)
  exact le_antisymm ((hanti (by omega : k₁ + 1 ≤ k + 1)).trans hz) (hg.nonneg _)

end ExplicitFirst

end Optimization
