import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Optimization.LineSearch

/-!
# Steepest descent: backtracking-Armijo and exact line searches

Step-size rules for the steepest-descent iteration `x⁺ = x - t ∇f(x)` on a real inner product
space, as analysed in [cartis2022evaluation] §2.2, for an objective whose gradient is
`L`-Lipschitz (`‖∇f(y) - ∇f(z)‖ ≤ L ‖y - z‖`).

* `LineSearch.le_add_inner_add_of_lipschitz_gradient` — the descent lemma
  `f (x + d) ≤ f x + ⟪∇f(x), d⟫ + L/2 ‖d‖²` ((A.19) with `p = 1`).
* `LineSearch.armijo_neg_gradient_of_le` — Lemma 2.2.1: the Armijo condition (2.2.1)
  `f (x - t ∇f(x)) ≤ f x - α t ‖∇f(x)‖²` holds for every `t ∈ [0, 2(1-α)/L]`.
* `LineSearch.backtrackingIndex` — the number of halvings of the backtracking-Armijo line search
  of Algorithm 2.2.1: the least `i` such that the trial step `t_ini 2^{-i}` satisfies (2.2.1).
  `LineSearch.backtrackingIndex_le` gives the book's bound (2.2.6) on it and the lower bound
  `t ≥ min t_ini ((1-α)/L)` on the accepted step; the book's (2.2.7), `t ≥ (1-α)/L`, holds only
  when `t_ini ≥ (1-α)/L`, since the first trial may already be shorter.
* `LineSearch.IsExactLineMin` (the book's exact line search (2.2.26): the first global minimizer
  of `t ↦ f (x - t ∇f(x))` on `t ≥ 0`) and `LineSearch.IsFirstLocalLineMin` (the first stationary
  point along the ray, the slope being negative before it). The second rule is the one realised by
  the book's sharpness example for the exact line search (Theorem 2.2.5, Lemma B.2.6).
  `LineSearch.IsExactLineMin.unique` and `LineSearch.exists_isExactLineMin` (continuous `f`,
  bounded sublevel set) show that the exact line search is well defined.
* `LineSearch.decrease_ge_of_exactLineMin` — the core of Theorem 2.2.4: for any global line
  minimizer (`LineSearch.IsGlobalLineMin`) and for the first-local-minimizer rule, the step
  satisfies `t ≥ 1/L` and the decrease is at least `‖∇f(x)‖² / (2L)` ((2.2.28)).
-/

open Set
open scoped RealInnerProductSpace

namespace LineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {L α : ℝ}

/-! ### The descent lemma -/

/-- The derivative of `f` at `x` applied to `d` is `⟪∇f(x), d⟫`. -/
theorem fderiv_apply_eq_inner_gradient (f : E → ℝ) (x d : E) :
    fderiv ℝ f x d = ⟪gradient f x, d⟫ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- The operator norm of a difference of derivatives is the norm of the difference of the
gradients. -/
theorem norm_fderiv_sub_fderiv_eq (f : E → ℝ) (y z : E) :
    ‖fderiv ℝ f y - fderiv ℝ f z‖ = ‖gradient f y - gradient f z‖ := by
  have h : fderiv ℝ f y - fderiv ℝ f z =
      InnerProductSpace.toDual ℝ E (gradient f y - gradient f z) := by
    simp [gradient]
  rw [h, LinearIsometryEquiv.norm_map]

/-- **Descent lemma** ([cartis2022evaluation] (A.19) with `p = 1`): if `f` is differentiable with
`L`-Lipschitz gradient, then `f (x + d) ≤ f x + ⟪∇f(x), d⟫ + L/2 ‖d‖²`. -/
theorem le_add_inner_add_of_lipschitz_gradient (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (x d : E) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L / 2 * ‖d‖ ^ 2 := by
  have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (𝕜 := ℝ) convex_univ
    (fun z _ => (hf z).hasFDerivAt) (mem_univ x) (mem_univ (x + d)) (C := L)
    (fun z _ => by rw [norm_fderiv_sub_fderiv_eq]; exact hL z x)
  simp only [add_sub_cancel_left, Real.norm_eq_abs, fderiv_apply_eq_inner_gradient] at h
  linarith [le_abs_self (f (x + d) - f x - ⟪gradient f x, d⟫)]

/-! ### Armijo condition along the steepest-descent direction -/

/-- Along `d = -∇f(x)`, the Armijo condition `LineSearch.Armijo` with derivative `fderiv ℝ f` is
the inequality (2.2.1) `f (x - t ∇f(x)) ≤ f x - α t ‖∇f(x)‖²`. -/
theorem armijo_neg_gradient_iff {x : E} {t : ℝ} :
    Armijo f (fderiv ℝ f) α x (-gradient f x) t ↔
      f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 := by
  rw [Armijo, fderiv_apply_eq_inner_gradient, inner_neg_right, real_inner_self_eq_norm_sq,
    smul_neg, ← sub_eq_add_neg]
  constructor <;> intro h <;> linarith

/-- **Lemma 2.2.1** ([cartis2022evaluation] (2.2.3)–(2.2.4)). If `f` is differentiable with
`L`-Lipschitz gradient and `L > 0`, the Armijo condition along the steepest-descent
direction holds for every step `t ∈ [0, 2(1-α)/L]`:
`f (x - t ∇f(x)) ≤ f x - α t ‖∇f(x)‖²`. -/
theorem armijo_neg_gradient_of_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (x : E) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * (1 - α) / L) :
    f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 := by
  have h := le_add_inner_add_of_lipschitz_gradient hf hL x (-(t • gradient f x))
  rw [← sub_eq_add_neg, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at h
  have hLt : L * t ≤ 2 * (1 - α) := by rwa [le_div_iff₀ hL0, mul_comm] at ht
  have hg := sq_nonneg ‖gradient f x‖
  nlinarith [mul_nonneg (mul_nonneg ht0 hg) (sub_nonneg.2 hLt)]

/-! ### The backtracking index -/

/-- The Armijo test (2.2.1) of Algorithm 2.2.1 at the `i`-th trial step `t_ini 2^{-i}`. -/
def BacktrackingTest (f : E → ℝ) (α tini : ℝ) (x : E) (i : ℕ) : Prop :=
  f (x - (tini * 2⁻¹ ^ i) • gradient f x) ≤ f x - α * (tini * 2⁻¹ ^ i) * ‖gradient f x‖ ^ 2

open Classical in
/-- The **backtracking index** of Algorithm 2.2.1 ([cartis2022evaluation] Steps 2–3): the least
`i` such that the trial step `t_ini 2^{-i}` satisfies the Armijo condition (2.2.1)
`f (x - t ∇f(x)) ≤ f x - α t ‖∇f(x)‖²` (`LineSearch.BacktrackingTest`), and `0` if there is
none. The accepted step is `t_ini 2^{-i}`; the line search evaluates `f` `i + 1` times. -/
noncomputable def backtrackingIndex (f : E → ℝ) (α tini : ℝ) (x : E) : ℕ :=
  if h : ∃ i, BacktrackingTest f α tini x i then Nat.find h else 0

theorem backtrackingIndex_eq_find {tini : ℝ} {x : E} (h : ∃ i, BacktrackingTest f α tini x i)
    [DecidablePred (BacktrackingTest f α tini x)] :
    backtrackingIndex f α tini x = Nat.find h := by
  rw [backtrackingIndex, dite_eq_left_of_eq_true (eq_true h)]
  congr

/-- The accepted step satisfies the Armijo condition, as soon as some trial step does. -/
theorem backtrackingIndex_spec {tini : ℝ} {x : E} (h : ∃ i, BacktrackingTest f α tini x i) :
    BacktrackingTest f α tini x (backtrackingIndex f α tini x) := by
  classical
  rw [backtrackingIndex_eq_find h]
  exact Nat.find_spec h

/-- Trial steps before the accepted one fail the Armijo condition. -/
theorem not_backtrackingTest_of_lt {tini : ℝ} {x : E} {i : ℕ}
    (hi : i < backtrackingIndex f α tini x) : ¬ BacktrackingTest f α tini x i := by
  classical
  by_cases h : ∃ i, BacktrackingTest f α tini x i
  · rw [backtrackingIndex_eq_find h] at hi
    exact Nat.find_min h hi
  · exact fun hi' => h ⟨i, hi'⟩

/-- The backtracking index is at most any index whose trial step satisfies the Armijo
condition. -/
theorem backtrackingIndex_le_of_test {tini : ℝ} {x : E} {i : ℕ}
    (hi : BacktrackingTest f α tini x i) : backtrackingIndex f α tini x ≤ i :=
  not_lt.1 fun h => not_backtrackingTest_of_lt h hi

/-- If the first trial step `t_ini` is accepted, no backtracking takes place. -/
theorem backtrackingIndex_eq_zero {tini : ℝ} {x : E} (h : BacktrackingTest f α tini x 0) :
    backtrackingIndex f α tini x = 0 :=
  Nat.le_zero.1 (backtrackingIndex_le_of_test h)

/-- Under the hypotheses of Lemma 2.2.1 every trial step `t_ini 2^{-i} ≤ 2(1-α)/L` is accepted. -/
theorem backtrackingTest_of_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) {tini : ℝ}
    (htini : 0 < tini) (x : E) {i : ℕ} (hi : tini * 2⁻¹ ^ i ≤ 2 * (1 - α) / L) :
    BacktrackingTest f α tini x i :=
  armijo_neg_gradient_of_le hf hL hL0 x (by positivity) hi

/-- **Bounds (2.2.6)–(2.2.7)** of [cartis2022evaluation]. Under the hypotheses of Lemma 2.2.1,
with `0 < α < 1` and `t_ini > 0`, the backtracking index satisfies
`i ≤ ⌈log₂ (L t_ini / (2(1-α)))⌉₊`, and the accepted step `t = t_ini 2^{-i}` satisfies
`t ≥ min t_ini ((1-α)/L)`. (The book's (2.2.7), `t ≥ (1-α)/L`, requires `t_ini ≥ (1-α)/L`.) -/
theorem backtrackingIndex_le (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (hα : α < 1)
    {tini : ℝ} (htini : 0 < tini) (x : E) :
    backtrackingIndex f α tini x ≤ ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ ∧
      min tini ((1 - α) / L) ≤ tini * 2⁻¹ ^ backtrackingIndex f α tini x := by
  have h1α : 0 < 1 - α := sub_pos.2 hα
  set N := ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊
  have hpos : 0 < L * tini / (2 * (1 - α)) := by positivity
  have hN : tini * 2⁻¹ ^ N ≤ 2 * (1 - α) / L := by
    have h2N : L * tini / (2 * (1 - α)) ≤ 2 ^ N := by
      rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow (by norm_num) hpos]
      exact Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at h2N
    rw [le_div_iff₀ hL0, inv_pow]
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    calc tini * (2 ^ N)⁻¹ * L = L * tini / 2 ^ N := by ring
      _ ≤ 2 * (1 - α) := by rw [div_le_iff₀ h2]; linarith
  refine ⟨backtrackingIndex_le_of_test (backtrackingTest_of_le hf hL hL0 htini x hN), ?_⟩
  rcases Nat.eq_zero_or_pos (backtrackingIndex f α tini x) with h0 | hpos'
  · rw [h0]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hpos'
    rw [zero_add] at hj
    have hfail : ¬ BacktrackingTest f α tini x j :=
      not_backtrackingTest_of_lt (by omega)
    have hlt : 2 * (1 - α) / L < tini * 2⁻¹ ^ j :=
      not_le.1 fun h => hfail (backtrackingTest_of_le hf hL hL0 htini x h)
    refine min_le_of_right_le ?_
    rw [hj, pow_succ]
    have : (1 - α) / L = 2 * (1 - α) / L * 2⁻¹ := by ring
    rw [this, ← mul_assoc]
    exact (mul_le_mul_iff_left₀ (by norm_num)).2 hlt.le

/-! ### Exact line searches -/

/-- `t ≥ 0` is a global minimizer of `τ ↦ f (x - τ ∇f(x))` on `[0, ∞)`. -/
def IsGlobalLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ τ : ℝ, 0 ≤ τ → f (x - t • gradient f x) ≤ f (x - τ • gradient f x)

/-- The **exact line search** (2.2.26) of [cartis2022evaluation]: `t ≥ 0` is the first global
minimizer of `τ ↦ f (x - τ ∇f(x))` on `[0, ∞)`. -/
def IsExactLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  IsGlobalLineMin f x t ∧ ∀ τ ∈ Ico 0 t, f (x - t • gradient f x) < f (x - τ • gradient f x)

/-- An exact line-search step is a global line minimizer. -/
theorem IsExactLineMin.isGlobalLineMin {x : E} {t : ℝ} (h : IsExactLineMin f x t) :
    IsGlobalLineMin f x t :=
  h.1

/-- The exact line-search step (2.2.26) is unique: there is only one first global minimizer on
the ray. -/
theorem IsExactLineMin.unique {x : E} {t t' : ℝ} (h : IsExactLineMin f x t)
    (h' : IsExactLineMin f x t') : t = t' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.2 t ⟨h.1.1, hlt⟩
    linarith [h.1.2 t' h'.1.1]
  · have := h.2 t' ⟨h'.1.1, hlt⟩
    linarith [h'.1.2 t h.1.1]

/-- **The exact line search (2.2.26) is well defined** when `f` is continuous and the sublevel
set `{y | f y ≤ f x}` is bounded: the first global minimizer of `t ↦ f(x - t∇f(x))` on `t ≥ 0`
exists. -/
theorem exists_isExactLineMin (hf : Continuous f) {x : E}
    (hbdd : Bornology.IsBounded {y | f y ≤ f x}) : ∃ t, IsExactLineMin f x t := by
  set g := gradient f x
  rcases eq_or_ne g 0 with hg | hg
  · refine ⟨0, ⟨⟨le_rfl, fun τ _ => by simp [g, hg]⟩, fun τ hτ => ?_⟩⟩
    exact absurd hτ.2 (not_lt.2 hτ.1)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  set φ : ℝ → ℝ := fun t => f (x - t • g)
  have hφ : Continuous φ := hf.comp (continuous_const.sub (continuous_id.smul continuous_const))
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1 hbdd
  set T : Set ℝ := {t | 0 ≤ t ∧ φ t ≤ f x}
  have hTsub : T ⊆ Icc 0 ((R + ‖x‖) / ‖g‖) := by
    intro t ⟨ht0, ht⟩
    refine ⟨ht0, ?_⟩
    have hmem := hR (show x - t • g ∈ {y | f y ≤ f x} from ht)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    rw [le_div_iff₀ hgpos]
    have : ‖t • g‖ ≤ ‖x - t • g‖ + ‖x‖ := by
      have := norm_sub_le x (x - t • g)
      rw [sub_sub_cancel] at this
      linarith
    rw [norm_smul, Real.norm_of_nonneg ht0] at this
    linarith
  have hTclosed : IsClosed T := isClosed_Ici.inter (isClosed_le hφ continuous_const)
  have hTcpt : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed hTsub
  have h0T : (0 : ℝ) ∈ T := ⟨le_rfl, by simp [φ]⟩
  obtain ⟨t₀, ht₀, hmin⟩ := hTcpt.exists_isMinOn ⟨0, h0T⟩ hφ.continuousOn
  have hm0 : φ t₀ ≤ f x := by simpa [φ] using hmin h0T
  set M : Set ℝ := {t | 0 ≤ t ∧ φ t ≤ φ t₀}
  have hMsub : M ⊆ T := fun t ht => ⟨ht.1, ht.2.trans hm0⟩
  have hMcpt : IsCompact M :=
    hTcpt.of_isClosed_subset (isClosed_Ici.inter (isClosed_le hφ continuous_const)) hMsub
  obtain ⟨t, htM, hleast⟩ := hMcpt.exists_isLeast ⟨t₀, ht₀.1, le_rfl⟩
  have hglob : ∀ τ, 0 ≤ τ → φ t ≤ φ τ := fun τ hτ => by
    by_cases hτT : τ ∈ T
    · exact htM.2.trans (hmin hτT)
    · have : f x < φ τ := not_le.1 fun h' => hτT ⟨hτ, h'⟩
      linarith [htM.2]
  refine ⟨t, ⟨htM.1, hglob⟩, fun τ hτ => lt_of_le_of_ne (hglob τ hτ.1) fun heq => ?_⟩
  have : φ τ ≤ φ t₀ := by
    have h2 : φ t = φ τ := heq
    rw [← h2]; exact htM.2
  exact absurd (hleast ⟨hτ.1, this⟩) (not_le.2 hτ.2)

/-- The **first-local-minimizer line search**: `t > 0` is the first stationary point of
`φ τ = f (x - τ ∇f(x))` on `[0, ∞)` and `φ` has negative slope `φ' τ = -⟪∇f(x - τ ∇f(x)), ∇f(x)⟫`
on `[0, t)`. This is the property of the iterates of the sharpness example of
[cartis2022evaluation] Theorem 2.2.5 (Lemma B.2.6). -/
def IsFirstLocalLineMin (f : E → ℝ) (x : E) (t : ℝ) : Prop :=
  0 < t ∧ ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0 ∧
    ∀ τ ∈ Ico 0 t, 0 < ⟪gradient f (x - τ • gradient f x), gradient f x⟫

/-- The derivative of `τ ↦ f (x - τ ∇f(x))`. -/
theorem hasDerivAt_lineFun (hf : Differentiable ℝ f) (x : E) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => f (x - τ • gradient f x))
      (-⟪gradient f (x - τ • gradient f x), gradient f x⟫) τ := by
  have hl : HasDerivAt (fun τ : ℝ => x - τ • gradient f x) (-gradient f x) τ := by
    simpa using ((hasDerivAt_id τ).smul_const (gradient f x)).const_sub x
  have h := (hf (x - τ • gradient f x)).hasFDerivAt.comp_hasDerivAt τ hl
  rwa [map_neg, fderiv_apply_eq_inner_gradient] at h

/-- A global line minimizer is positive and stationary when `∇f(x) ≠ 0`. -/
theorem IsGlobalLineMin.pos_and_inner_eq_zero (hf : Differentiable ℝ f) {x : E} {t : ℝ}
    (h : IsGlobalLineMin f x t) (hg : gradient f x ≠ 0) :
    0 < t ∧ ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0 := by
  have hpos : 0 < t := by
    rcases h.1.lt_or_eq with ht | ht
    · exact ht
    · -- at `t = 0` the slope `-‖∇f(x)‖²` is negative, so `0` is not a minimizer on `[0, ∞)`
      exfalso
      have hd := hasDerivAt_lineFun hf x 0
      simp only [zero_smul, sub_zero, real_inner_self_eq_norm_sq] at hd
      have hneg : -‖gradient f x‖ ^ 2 < 0 := by
        have := norm_pos_iff.2 hg
        nlinarith
      have hlim := hd.tendsto_slope_zero_right
      have hev : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Ioi 0),
          0 ≤ τ⁻¹ • (f (x - (0 + τ) • gradient f x) - f (x - (0 : ℝ) • gradient f x)) := by
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hmin := h.2 τ (le_of_lt hτ)
        rw [← ht] at hmin
        simp only [zero_add, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 (le_of_lt hτ)) (sub_nonneg.2 hmin)
      have := ge_of_tendsto hlim hev
      linarith
  refine ⟨hpos, ?_⟩
  have hmin : IsLocalMin (fun τ : ℝ => f (x - τ • gradient f x)) t :=
    Filter.mem_of_superset (Ioi_mem_nhds hpos) fun τ hτ => h.2 τ (le_of_lt hτ)
  have := hmin.hasDerivAt_eq_zero (hasDerivAt_lineFun hf x t)
  linarith

/-- On a line where `∇f` is `L`-Lipschitz, a stationary step satisfies `t ≥ 1/L`
(from `0 = ⟪∇f(x - t∇f(x)), ∇f(x)⟫ ≥ ‖∇f(x)‖² (1 - L t)`). -/
theorem one_div_le_of_inner_eq_zero (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (hL0 : 0 < L) {x : E} (hg : gradient f x ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (h0 : ⟪gradient f (x - t • gradient f x), gradient f x⟫ = 0) : 1 / L ≤ t := by
  set g := gradient f x
  have hng : 0 < ‖g‖ := norm_pos_iff.2 hg
  have hd := hL (x - t • g) x
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hd
  have hcs := real_inner_le_norm (g - gradient f (x - t • g)) g
  have hexp : ⟪g - gradient f (x - t • g), g⟫ = ‖g‖ ^ 2 := by
    rw [inner_sub_left, h0, real_inner_self_eq_norm_sq, sub_zero]
  rw [hexp, norm_sub_rev] at hcs
  have : 1 * ‖g‖ ^ 2 ≤ (L * t) * ‖g‖ ^ 2 := by nlinarith
  have h1 := le_of_mul_le_mul_right this (by positivity)
  rw [div_le_iff₀ hL0]
  linarith

/-- The decrease at the step `1/L`: `f (x - ∇f(x)/L) ≤ f x - ‖∇f(x)‖²/(2L)` ((2.2.28)). -/
theorem le_sub_of_step_inv (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) (x : E) :
    f (x - (1 / L) • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have h := le_add_inner_add_of_lipschitz_gradient hf hL x (-((1 / L) • gradient f x))
  rw [← sub_eq_add_neg, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  have : f x + -(1 / L * ‖gradient f x‖ ^ 2) + L / 2 * (1 / L * ‖gradient f x‖) ^ 2 =
      f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  linarith

/-- **Theorem 2.2.4, core** ([cartis2022evaluation] proof of Theorem 2.2.4). Let `f` be
differentiable with `L`-Lipschitz gradient, `L > 0`, and `∇f(x) ≠ 0`. If `t` is a global line
minimizer (`IsGlobalLineMin`, e.g. the book's exact line search (2.2.26) `IsExactLineMin`) or a
first-local-minimizer step (`IsFirstLocalLineMin`), then `t ≥ 1/L` and
`f x - f (x - t ∇f(x)) ≥ ‖∇f(x)‖²/(2L)`. -/
theorem decrease_ge_of_exactLineMin (hf : Differentiable ℝ f)
    (hL : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖) (hL0 : 0 < L) {x : E}
    (hg : gradient f x ≠ 0) {t : ℝ} (ht : IsGlobalLineMin f x t ∨ IsFirstLocalLineMin f x t) :
    1 / L ≤ t ∧ ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - f (x - t • gradient f x) := by
  have hstep := le_sub_of_step_inv hf hL hL0 x
  rcases ht with ht | ht
  · obtain ⟨hpos, h0⟩ := ht.pos_and_inner_eq_zero hf hg
    refine ⟨one_div_le_of_inner_eq_zero hL hL0 hg hpos.le h0, ?_⟩
    have := ht.2 (1 / L) (by positivity)
    linarith
  · have h1L := one_div_le_of_inner_eq_zero hL hL0 hg ht.1.le ht.2.1
    refine ⟨h1L, ?_⟩
    -- `φ` is antitone on `[0, t]`, hence `φ t ≤ φ (1/L)`
    have hanti : AntitoneOn (fun τ : ℝ => f (x - τ • gradient f x)) (Icc 0 t) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
      · exact fun τ _ => (hasDerivAt_lineFun hf x τ).continuousAt.continuousWithinAt
      · exact fun τ _ => (hasDerivAt_lineFun hf x τ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hasDerivAt_lineFun hf x τ).deriv]
        exact (neg_neg_of_pos (ht.2.2 τ ⟨hτ.1.le, hτ.2⟩)).le
    have := hanti ⟨by positivity, h1L⟩ ⟨ht.1.le, le_rfl⟩ h1L
    simp only at this
    linarith

end LineSearch
