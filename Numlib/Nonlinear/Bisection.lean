/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The bisection method

Let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$ with $f(a) f(b) \le 0$. The bisection
method halves a bracket $[a^{(k)}, b^{(k)}]$ in each step and keeps the half on which $f$ changes
sign. Its iterate $x^{(k)}$ is the midpoint of the $k$-th bracket. This module follows §6.2.1 of
[quarteroni2000numerical], with §6.1 of [kress1998numerical] and §5.2 of [han2009theoretical]. It
proves the theorem of zeros for continuous functions in the sign-change form, the invariants of the
bracket iteration, and the global convergence of the iterates to a root $\alpha$ with the a priori
bound
$$|x^{(k)} - \alpha| \le \frac{b - a}{2^{k+1}}.$$
It also proves the iteration count: $|x^{(m)} - \alpha| \le \varepsilon$ when
$\log_2((b - a)/\varepsilon) \le m + 1$, which is (6.9) of [quarteroni2000numerical].

## Main definitions

* `Bisection.step`: one bisection step on a bracket $(a, b)$.
* `Bisection.bracket`: the $k$-th bracket $[a^{(k)}, b^{(k)}]$.
* `Bisection.iterate`: the $k$-th iterate $x^{(k)} = (a^{(k)} + b^{(k)})/2$.

## Main results

* `exists_eq_zero_Ioo_of_mul_neg`: a function continuous on $[a, b]$ with $f(a) f(b) < 0$ has a zero
  in $(a, b)$.
* `exists_eq_zero_Icc_of_mul_nonpos`: a function continuous on $[a, b]$ with $f(a) f(b) \le 0$ has a
  zero in $[a, b]$.
* `Bisection.bracket_sub`: the $k$-th bracket has length $(b - a)/2^k$.
* `Bisection.bracket_mul_nonpos`: the sign condition $f(a^{(k)}) f(b^{(k)}) \le 0$ holds for every
  $k$.
* `Bisection.bracket_nested`: the brackets are nested.
* `Bisection.exists_tendsto_iterate`: the iterates converge to a root $\alpha \in [a, b]$ that lies
  in every bracket, with $|x^{(k)} - \alpha| \le (b - a)/2^{k+1}$.
* `Bisection.abs_iterate_sub_le_of_le_logb`: $|x^{(m)} - \alpha| \le \varepsilon$ when
  $\log_2((b - a)/\varepsilon) \le m + 1$.

## Implementation notes

* The step follows Program 46 of [quarteroni2000numerical] and not its prose. With $m = (a + b)/2$,
  the step sets $a := m$ when $f(a) f(m) > 0$, and $b := m$ otherwise. Thus an exact hit $f(m) = 0$
  closes the bracket on the right and keeps $m$ as the right endpoint. The two strict cases of the
  prose leave the case $f(m) = 0$ undefined.
* All results need only $f(a) f(b) \le 0$, not the condition $f(a) f(b) < 0$ of the source. The
  invariant is stated with $\le 0$, because it fails with $< 0$ as soon as an iterate is an exact
  root.
* The a priori bound of [quarteroni2000numerical] is $(b - a)/2^k$. Because the iterate is the
  midpoint of the bracket, the bound here is better by a factor $2$.
* The root of `Bisection.exists_tendsto_iterate` is the supremum of the left endpoints. A bracket
  can contain several roots, and the estimates hold for this root. The iteration count is stated for
  this root (`Bisection.abs_iterate_sub_le_of_le_logb`), and in a pure arithmetic form for any
  sequence that satisfies the a priori bound (`Bisection.div_two_pow_le_of_logb_le`).
-/

open Filter Topology Set

section IntermediateValue

variable {f : ℝ → ℝ} {a b : ℝ}

/-- The **theorem of zeros for continuous functions**. Let $a \le b$, and let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$ with $f(a) f(b) < 0$. Then there is
$\alpha \in (a, b)$ with $f(\alpha) = 0$. This is Property 6.1 of [quarteroni2000numerical].

The proof splits the two sign cases with `mul_neg_iff` and applies `intermediate_value_Ioo` or
`intermediate_value_Ioo'` of Mathlib. -/
theorem exists_eq_zero_Ioo_of_mul_neg (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b < 0) : ∃ α ∈ Ioo a b, f α = 0 := by
  rcases mul_neg_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨α, hα, hfα⟩ := intermediate_value_Ioo' hab hf ⟨hb, ha⟩
    exact ⟨α, hα, hfα⟩
  · obtain ⟨α, hα, hfα⟩ := intermediate_value_Ioo hab hf ⟨ha, hb⟩
    exact ⟨α, hα, hfα⟩

/-- The theorem of zeros on a closed interval. Let $a \le b$, and let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$ with $f(a) f(b) \le 0$. Then there is
$\alpha \in [a, b]$ with $f(\alpha) = 0$.

If $f(a) f(b) = 0$, the zero is an endpoint. Otherwise the zero comes from
`exists_eq_zero_Ioo_of_mul_neg`. -/
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

/-- One **bisection step** on a bracket $(a, b)$. Let $m = (a + b)/2$. The step returns $(m, b)$ if
$f(a) f(m) > 0$, and $(a, m)$ otherwise.

This is the rule of Program 46 of [quarteroni2000numerical]. Under this rule an exact hit
$f(m) = 0$ closes the bracket on the right. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  if 0 < f s.1 * f ((s.1 + s.2) / 2) then ((s.1 + s.2) / 2, s.2) else (s.1, (s.1 + s.2) / 2)

/-- The $k$-th **bracket** $(a^{(k)}, b^{(k)})$ of the bisection method started on $(a, b)$: the
result of $k$ applications of `Bisection.step` to $(a, b)$. -/
noncomputable def bracket (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ × ℝ := (step f)^[k] (a, b)

/-- The $k$-th **bisection iterate** $x^{(k)} = (a^{(k)} + b^{(k)})/2$, the midpoint of the $k$-th
bracket. -/
noncomputable def iterate (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  ((bracket f a b k).1 + (bracket f a b k).2) / 2

/-- The bracket at step $0$ is the starting pair $(a, b)$. -/
@[simp]
theorem bracket_zero (f : ℝ → ℝ) (a b : ℝ) : bracket f a b 0 = (a, b) := rfl

/-- The bracket at step $k + 1$ is one bisection step applied to the bracket at step $k$:
$(a^{(k+1)}, b^{(k+1)}) = \operatorname{step}(a^{(k)}, b^{(k)})$. -/
theorem bracket_succ (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) :
    bracket f a b (k + 1) = step f (bracket f a b k) :=
  Function.iterate_succ_apply' _ _ _

/-- **The length halves.** For every $f$, $a$, $b$ and $k$,
$$b^{(k)} - a^{(k)} = \frac{b - a}{2^k}.$$
This is (6.8) of [quarteroni2000numerical]. No hypothesis on $f$, $a$ or $b$ is necessary. -/
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

/-- If $a \le b$, then $a^{(k)} \le b^{(k)}$ for every $k$, for every $f$. -/
theorem bracket_fst_le_snd (hab : a ≤ b) (k : ℕ) : (bracket f a b k).1 ≤ (bracket f a b k).2 := by
  have := bracket_sub f a b k
  have hpos : 0 ≤ (b - a) / 2 ^ k := by
    positivity
  linarith

/-- **The sign invariant.** If $f(a) f(b) \le 0$, then $f(a^{(k)}) f(b^{(k)}) \le 0$ for every $k$.

The source writes the condition with $< 0$. That condition fails after an exact hit $f(m) = 0$,
and the weak inequality is what the step keeps. -/
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

/-- **The brackets are nested.** If $a \le b$, then $[a^{(k+1)}, b^{(k+1)}] \subseteq [a^{(k)},
b^{(k)}]$ for every $k$, because each step keeps one endpoint and replaces the other by the
midpoint. -/
theorem bracket_nested (hab : a ≤ b) (k : ℕ) :
    Icc (bracket f a b (k + 1)).1 (bracket f a b (k + 1)).2 ⊆
      Icc (bracket f a b k).1 (bracket f a b k).2 := by
  have hle := bracket_fst_le_snd (f := f) hab k
  rw [bracket_succ]
  set s := bracket f a b k with hs
  unfold step
  split_ifs <;> exact Icc_subset_Icc (by simp only; linarith) (by simp only; linarith)

/-- If $a \le b$, the left endpoints $a^{(k)}$ increase with $k$. -/
theorem monotone_bracket_fst (hab : a ≤ b) : Monotone fun k => (bracket f a b k).1 :=
  monotone_nat_of_le_succ fun k =>
    (bracket_nested hab k (left_mem_Icc.2 (bracket_fst_le_snd hab (k + 1)))).1

/-- If $a \le b$, the right endpoints $b^{(k)}$ decrease with $k$. -/
theorem antitone_bracket_snd (hab : a ≤ b) : Antitone fun k => (bracket f a b k).2 :=
  antitone_nat_of_succ_le fun k =>
    (bracket_nested hab k (right_mem_Icc.2 (bracket_fst_le_snd hab (k + 1)))).2

/-- If $a \le b$, then every bracket $[a^{(k)}, b^{(k)}]$ lies in $[a, b]$. -/
theorem bracket_subset_Icc (hab : a ≤ b) (k : ℕ) :
    Icc (bracket f a b k).1 (bracket f a b k).2 ⊆ Icc a b :=
  Icc_subset_Icc (by simpa using monotone_bracket_fst (f := f) hab (Nat.zero_le k))
    (by simpa using antitone_bracket_snd (f := f) hab (Nat.zero_le k))

/-- Let $a \le b$, and let $f$ be continuous on $[a, b]$ with $f(a) f(b) \le 0$. Then every bracket
$[a^{(k)}, b^{(k)}]$ contains a zero of $f$. The proof applies the theorem of zeros to the
bracket. -/
theorem exists_root_mem_bracket (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (h : f a * f b ≤ 0)
    (k : ℕ) : ∃ α ∈ Icc (bracket f a b k).1 (bracket f a b k).2, f α = 0 :=
  exists_eq_zero_Icc_of_mul_nonpos (bracket_fst_le_snd hab k) (hf.mono (bracket_subset_Icc hab k))
    (bracket_mul_nonpos h k)

/-- If $a \le b$, then $a^{(j)} \le b^{(k)}$ for all $j$ and $k$: a left endpoint never exceeds a
right endpoint, at any two steps. -/
theorem bracket_fst_le_bracket_snd (hab : a ≤ b) (j k : ℕ) :
    (bracket f a b j).1 ≤ (bracket f a b k).2 :=
  calc (bracket f a b j).1 ≤ (bracket f a b (max j k)).1 :=
        monotone_bracket_fst hab (le_max_left j k)
    _ ≤ (bracket f a b (max j k)).2 := bracket_fst_le_snd hab _
    _ ≤ (bracket f a b k).2 := antitone_bracket_snd hab (le_max_right j k)

/-- Let $u, v, x \in \mathbb{R}$ with $x \in [u, v]$. Then $|(u + v)/2 - x| \le (v - u)/2$: the
midpoint of an interval is within half its length of every point of the interval. -/
theorem abs_midpoint_sub_le {u v x : ℝ} (hx : x ∈ Icc u v) : |(u + v) / 2 - x| ≤ (v - u) / 2 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- **Global convergence of bisection, with the a priori bound.** Let $a \le b$, and let $f$ be
continuous on $[a, b]$ with $f(a) f(b) \le 0$. Then there is $\alpha \in [a, b]$ with
$f(\alpha) = 0$ such that $\alpha$ lies in every bracket $[a^{(k)}, b^{(k)}]$, the iterates
$x^{(k)}$ converge to $\alpha$, and for every $k$
$$|x^{(k)} - \alpha| \le \frac{b - a}{2^{k+1}}.$$
This is the consequence of (6.8) in §6.2.1 of [quarteroni2000numerical]. The source states the
weaker bound $(b - a)/2^k$.

The root $\alpha$ is the supremum of the increasing left endpoints. It lies below every right
endpoint (`Bisection.bracket_fst_le_bracket_snd`), so it lies in every bracket. The two endpoint
sequences converge to $\alpha$, because the lengths $(b - a)/2^k$ tend to $0$. So
$f(a^{(k)}) f(b^{(k)}) \le 0$ passes to the limit $f(\alpha)^2 \le 0$, and $f(\alpha) = 0$. -/
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

/-- The arithmetic of the iteration count. Let $L \ge 0$, $\varepsilon > 0$ and $n \in \mathbb{N}$
with $\log_2(L/\varepsilon) \le n$. Then $L/2^n \le \varepsilon$. -/
theorem div_two_pow_le_of_logb_le {L ε : ℝ} {n : ℕ} (hL : 0 ≤ L) (hε : 0 < ε)
    (hn : Real.logb 2 (L / ε) ≤ n) : L / 2 ^ n ≤ ε := by
  rcases hL.lt_or_eq with hL | rfl
  · have := (Real.logb_le_iff_le_rpow one_lt_two (div_pos hL hε)).1 hn
    rw [Real.rpow_natCast] at this
    rw [div_le_iff₀ (by positivity)]
    rwa [div_le_iff₀ hε, mul_comm] at this
  · simp [hε.le]

/-- **The iteration count.** Let $a \le b$, and let $f$ be continuous on $[a, b]$ with
$f(a) f(b) \le 0$. Then there is $\alpha \in [a, b]$ with $f(\alpha) = 0$ such that the iterates
$x^{(k)}$ converge to $\alpha$, and for every $m \in \mathbb{N}$ and every $\varepsilon > 0$,
$$\log_2\frac{b - a}{\varepsilon} \le m + 1 \implies |x^{(m)} - \alpha| \le \varepsilon.$$
This is (6.9) of [quarteroni2000numerical], with the sharper bound $(b - a)/2^{m+1}$. The
condition $\log_2((b - a)/\varepsilon) \le m$ of the source suffices for its weaker bound
$(b - a)/2^m$.

The root $\alpha$ is the root of `Bisection.exists_tendsto_iterate`. The statement is for this
root and not for an arbitrary root, because a bracket can contain several roots. -/
theorem abs_iterate_sub_le_of_le_logb (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h : f a * f b ≤ 0) :
    ∃ α ∈ Icc a b, f α = 0 ∧ Tendsto (iterate f a b) atTop (𝓝 α) ∧
      ∀ (m : ℕ) (ε : ℝ), 0 < ε → Real.logb 2 ((b - a) / ε) ≤ m + 1 →
        |iterate f a b m - α| ≤ ε := by
  obtain ⟨α, hα, hfα, hlim, -, hbound⟩ := exists_tendsto_iterate hab hf h
  refine ⟨α, hα, hfα, hlim, fun m ε hε hm => (hbound m).trans ?_⟩
  exact div_two_pow_le_of_logb_le (sub_nonneg.2 hab) hε (by exact_mod_cast hm)

end Bisection
