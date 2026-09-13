import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.IntermediateValue
import Numlib.Optimization.Descent

/-!
# Inexact line searches: Armijo, Wolfe and Goldstein conditions, Zoutendijk's theorem

The step-size conditions of inexact line searches for a descent method `x_{k+1} = x_k + α_k d_k`
([quarteroni2000numerical] §7.2.3 and §7.2.6; Nocedal–Wright, *Numerical Optimization*, §3.1–3.2),
as predicates on a step `α` along a direction `d` at a point `x`: the Armijo sufficient-decrease
condition (7.31) `f (x + α d) ≤ f x + σ α f' x d` (`LineSearch.Armijo`), the weak (7.33) and strong
(7.32) Wolfe curvature conditions (`LineSearch.WolfeCurvature`, `LineSearch.StrongWolfeCurvature`),
and the Goldstein conditions (7.34) (`LineSearch.Goldstein`). Then the two existence facts and the
global convergence theorem:

* backtracking terminates — every small enough positive step satisfies the Armijo condition along a
  descent direction (`LineSearch.eventually_armijo_of_isDescentDirection`);
* [quarteroni2000numerical] Property 7.5 (Nocedal–Wright Lemma 3.1): if `f` is bounded below along
  the ray, a whole interval `[c, C]` of steps satisfies the Armijo condition together with both
  Wolfe conditions (`LineSearch.exists_Icc_armijo_wolfe`);
* **Zoutendijk's theorem** (Nocedal–Wright Theorem 3.2), the content of [quarteroni2000numerical]
  Property 7.7: for a descent sequence with Armijo–Wolfe steps, a Lipschitz derivative and `f`
  bounded below on the iterates, `∑ (f' x_k d_k / ‖d_k‖)² < ∞` (`LineSearch.zoutendijk`), whence
  either `f (x_k) → -∞` or `f' x_k d_k / ‖d_k‖ → 0` (`LineSearch.tendsto_atBot_or_tendsto_zero`).

Everything is stated on a real normed space with the derivative as data `f' : E → E →L[ℝ] ℝ` and
the descent method as `Descent.IsDescentSequence` (`Numlib/Optimization/Descent`); the book's
Lipschitz condition `‖∇f(x) − ∇f(y)‖₂ ≤ L ‖x − y‖₂` is the operator-norm Lipschitz condition on
`f'`. The book's restriction `σ ∈ (0, 1/2)` is nowhere needed: Property 7.5 holds for
`0 < σ < β < 1` and Zoutendijk's theorem for `0 < σ` and `β < 1`. The first alternative of
Property 7.7, `∇f(x_k) = 0` for some `k`, is the termination case excluded by
`IsDescentSequence.descent`; the book's (7.31) is printed with an outer `0 ≥ v_M(x_{k+1})`, which
is a consequence of the inner inequality formalized here.
-/

open Filter Topology Metric Set

namespace LineSearch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Armijo (sufficient decrease) condition** ([quarteroni2000numerical] (7.31)):
`f (x + α d) ≤ f x + σ α f' x d`; for `α > 0` it says that the average descent rate
`(f x - f (x + α d)) / α` is at least the fraction `-σ f' x d` of the initial rate. -/
def Armijo (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (σ : ℝ) (x d : E) (α : ℝ) : Prop :=
  f (x + α • d) ≤ f x + σ * α * f' x d

/-- The **(weak) Wolfe curvature condition** ([quarteroni2000numerical] (7.33)):
`β f' x d ≤ f' (x + α d) d`, the slope along `d` at the new point is not more negative than the
fraction `β` of the initial slope. -/
def WolfeCurvature (f' : E → E →L[ℝ] ℝ) (β : ℝ) (x d : E) (α : ℝ) : Prop :=
  β * f' x d ≤ f' (x + α • d) d

/-- The **strong Wolfe curvature condition** ([quarteroni2000numerical] (7.32)):
`|f' (x + α d) d| ≤ β |f' x d|`; it implies `WolfeCurvature` when `f' x d < 0`. -/
def StrongWolfeCurvature (f' : E → E →L[ℝ] ℝ) (β : ℝ) (x d : E) (α : ℝ) : Prop :=
  |f' (x + α • d) d| ≤ β * |f' x d|

/-- The **Goldstein conditions** ([quarteroni2000numerical] (7.34)):
`f x + (1 - σ) α f' x d ≤ f (x + α d) ≤ f x + σ α f' x d`, which for `f' x d < 0` and `α > 0` read
`σ ≤ (f (x + α d) - f x) / (α f' x d) ≤ 1 - σ`. The second inequality is the Armijo condition. -/
def Goldstein (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (σ : ℝ) (x d : E) (α : ℝ) : Prop :=
  f x + (1 - σ) * α * f' x d ≤ f (x + α • d) ∧ f (x + α • d) ≤ f x + σ * α * f' x d

/-- The strong Wolfe condition implies the weak one along a descent direction. -/
theorem StrongWolfeCurvature.wolfeCurvature {f' : E → E →L[ℝ] ℝ} {β : ℝ} {x d : E} {α : ℝ}
    (hd : Descent.IsDescentDirection f' x d) (h : StrongWolfeCurvature f' β x d α) :
    WolfeCurvature f' β x d α := by
  have hneg : f' x d < 0 := hd
  have h1 := (abs_le.1 h).1
  rw [abs_of_neg hneg] at h1
  change β * f' x d ≤ f' (x + α • d) d
  linarith

/-- The Goldstein conditions contain the Armijo condition. -/
theorem Goldstein.armijo {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {σ : ℝ} {x d : E} {α : ℝ}
    (h : Goldstein f f' σ x d α) : Armijo f f' σ x d α :=
  h.2

/-- **Backtracking terminates** ([quarteroni2000numerical] §7.2.3, Program 62): along a descent
direction, with `σ < 1`, every small enough positive step satisfies the Armijo condition, because
the derivative of `t ↦ f (x + t d) - f x - σ t f' x d` at `0` is `(1 - σ) f' x d < 0`. Hence the
Armijo rule `α_k = β^{m_k} ᾱ` finds an admissible `m_k` after finitely many reductions. -/
theorem eventually_armijo_of_isDescentDirection {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : E} {σ : ℝ}
    (hf : HasFDerivAt f (f' x) x) (hd : Descent.IsDescentDirection f' x d) (hσ : σ < 1) :
    ∀ᶠ α in 𝓝[>] (0 : ℝ), Armijo f f' σ x d α := by
  have hneg : f' x d < 0 := hd
  have hg : HasDerivAt (fun t : ℝ => f (x + t • d)) (f' x d) 0 := hf.hasLineDerivAt d
  have hlt : f' x d < σ * f' x d := by nlinarith
  filter_upwards [Descent.eventually_lt_add_mul_of_hasDerivAt_lt hg hlt] with t ht
  simp only [zero_smul, add_zero] at ht
  change f (x + t • d) ≤ f x + σ * t * f' x d
  linarith

/-- **Existence of an interval of admissible steps** ([quarteroni2000numerical] Property 7.5;
Nocedal–Wright Lemma 3.1): if `f` is differentiable with continuous derivative, bounded below along
the ray `x + t d`, `d` is a descent direction at `x`, and `0 < σ < β < 1`, then there is an
interval `[c, C]` with `0 < c < C` on which the Armijo condition and both the weak and the strong
Wolfe curvature conditions hold.

Proof: `φ t = f (x + t d)` and `l t = f x + σ t f' x d`; `φ - l` is negative just to the right of
`0` (`σ < 1`) and nonnegative far out (`l → -∞`, `φ ≥ M`), so it has a first zero `α' > 0`, and
the Armijo condition holds on `(0, α']`. The mean value theorem gives `α'' ∈ (0, α')` with
`φ' α'' = σ f' x d`, which is `> β f' x d` and has `|φ' α''| < β |f' x d|` because `σ < β`;
continuity of `φ'` extends both to a closed interval around `α''` inside `(0, α')`. The book's
`σ < 1/2` is not needed. -/
theorem exists_Icc_armijo_wolfe {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : E} {M σ β : ℝ}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hcont : Continuous f')
    (hM : ∀ t : ℝ, M ≤ f (x + t • d)) (hd : Descent.IsDescentDirection f' x d)
    (hσ : 0 < σ) (hσβ : σ < β) (hβ : β < 1) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ α ∈ Set.Icc c C,
      Armijo f f' σ x d α ∧ WolfeCurvature f' β x d α ∧ StrongWolfeCurvature f' β x d α := by
  have hg₀ : f' x d < 0 := hd
  set φ : ℝ → ℝ := fun t => f (x + t • d) with hφ
  set φ' : ℝ → ℝ := fun t => f' (x + t • d) d with hφ'
  set l : ℝ → ℝ := fun t => f x + σ * t * f' x d with hl
  have hφd : ∀ t, HasDerivAt φ (φ' t) t := fun t => ((hf _).hasLineDerivAt d).hasDerivAt_line
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφd t).continuousAt
  have hφ'c : Continuous φ' := by
    have h : Continuous fun t : ℝ => f' (x + t • d) := hcont.comp (by fun_prop)
    exact h.clm_apply continuous_const
  have hlc : Continuous l := by fun_prop
  have hφ0 : φ 0 = f x := by simp [hφ]
  have hM' : ∀ t, M ≤ φ t := hM
  -- `φ < l` just to the right of `0`
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t < l t := by
    have hlt : φ' 0 < σ * f' x d := by
      simp only [hφ', zero_smul, add_zero]
      nlinarith
    filter_upwards [Descent.eventually_lt_add_mul_of_hasDerivAt_lt (hφd 0) hlt] with t ht
    rw [hφ0] at ht
    simp only [hl]
    linarith
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hnear
  rw [Set.mem_Ioi] at hε
  set t₁ : ℝ := ε / 2 with ht₁def
  have ht₁ : 0 < t₁ := by positivity
  have hneg₁ : ∀ t ∈ Set.Ioc 0 t₁, φ t < l t := fun t ht =>
    hεsub ⟨ht.1, by linarith [ht.2]⟩
  have hneg₁' : φ t₁ - l t₁ < 0 := by linarith [hneg₁ t₁ ⟨ht₁, le_rfl⟩]
  -- far out, `l ≤ M ≤ φ`
  set t₂ : ℝ := max (t₁ + 1) ((f x - M) / (-(σ * f' x d))) with ht₂def
  have ht₂ : t₁ < t₂ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hσg : 0 < -(σ * f' x d) := by nlinarith
  have hpos₂ : 0 ≤ φ t₂ - l t₂ := by
    have h1 : (f x - M) / (-(σ * f' x d)) ≤ t₂ := le_max_right _ _
    rw [div_le_iff₀ hσg] at h1
    have h2 : l t₂ ≤ M := by simp only [hl]; nlinarith
    linarith [hM' t₂]
  -- the first zero of `φ - l` beyond `t₁`
  set Z : Set ℝ := Set.Icc t₁ t₂ ∩ {t | φ t - l t = 0} with hZ
  have hZc : IsClosed Z := isClosed_Icc.inter (isClosed_eq (hφc.sub hlc) continuous_const)
  have hZne : Z.Nonempty := by
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc ht₂.le (hφc.sub hlc).continuousOn
      ⟨hneg₁'.le, hpos₂⟩
    exact ⟨t, ht, ht0⟩
  have hZbdd : BddBelow Z := ⟨t₁, fun t ht => ht.1.1⟩
  set α' : ℝ := sInf Z with hα'def
  have hα'Z : α' ∈ Z := hZc.csInf_mem hZne hZbdd
  have hα'le : ∀ t ∈ Z, α' ≤ t := fun t ht => csInf_le hZbdd ht
  have hα'gt : t₁ < α' := by
    refine lt_of_le_of_ne hα'Z.1.1 fun h => ?_
    have h2 : φ α' - l α' = 0 := hα'Z.2
    rw [← h] at h2
    linarith
  have hα'pos : 0 < α' := ht₁.trans hα'gt
  have hα'eq : φ α' = l α' := sub_eq_zero.1 hα'Z.2
  -- the Armijo condition on `(0, α']`
  have harm : ∀ t ∈ Set.Ioc 0 α', φ t ≤ l t := by
    intro t ht
    rcases le_or_gt t t₁ with h | h
    · exact (hneg₁ t ⟨ht.1, h⟩).le
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · rw [h2, hα'eq]
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc h.le (hφc.sub hlc).continuousOn
      ⟨hneg₁'.le, by rw [Pi.sub_apply]; linarith⟩
    have hsZ : s ∈ Z := ⟨⟨hs.1, hs.2.trans (h2.le.trans hα'Z.1.2)⟩, hs0⟩
    linarith [hα'le s hsZ, hs.2]
  -- the mean value theorem on `[0, α']`
  obtain ⟨α'', hα'', hα''eq⟩ :=
    exists_hasDerivAt_eq_slope φ φ' hα'pos hφc.continuousOn fun s _ => hφd s
  have hφ'α'' : φ' α'' = σ * f' x d := by
    have hα'ne : α' ≠ 0 := hα'pos.ne'
    rw [hα''eq, hα'eq, hφ0]
    simp only [hl]
    field_simp
    ring
  -- a closed interval around `α''` on which both curvature conditions hold strictly
  have hU : ∀ᶠ t in 𝓝 α'', β * f' x d < φ' t ∧ |φ' t| < β * |f' x d| ∧ t ∈ Set.Ioo 0 α' := by
    have h1 : ∀ᶠ t in 𝓝 α'', β * f' x d < φ' t :=
      hφ'c.continuousAt.eventually (lt_mem_nhds (by rw [hφ'α'']; nlinarith))
    have h2 : ∀ᶠ t in 𝓝 α'', |φ' t| < β * |f' x d| := by
      refine hφ'c.abs.continuousAt.eventually (gt_mem_nhds ?_)
      change |φ' α''| < β * |f' x d|
      rw [hφ'α'', abs_mul, abs_of_pos hσ]
      exact mul_lt_mul_of_pos_right hσβ (abs_pos.2 hg₀.ne)
    exact h1.and (h2.and (Ioo_mem_nhds hα''.1 hα''.2))
  obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.1 hU
  have hmemη : ∀ t ∈ Set.Icc (α'' - η / 2) (α'' + η / 2), dist t α'' < η := by
    intro t ht
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨α'' - η / 2, α'' + η / 2, ?_, by linarith, fun t ht => ?_⟩
  · exact (hηsub (hmemη _ ⟨le_rfl, by linarith⟩)).2.2.1
  · obtain ⟨h1, h2, h3⟩ := hηsub (hmemη t ht)
    exact ⟨harm t ⟨h3.1, h3.2.le⟩, h1.le, h2.le⟩

/-- **Zoutendijk's theorem** (Nocedal–Wright Theorem 3.2; the content of
[quarteroni2000numerical] Property 7.7): for a descent sequence `x_{k+1} = x_k + α_k d_k` whose
steps satisfy the Armijo and (weak) Wolfe conditions, with `f'` Lipschitz of constant `L` and `f`
bounded below on the iterates, the series `∑ (f' x_k d_k / ‖d_k‖)²` converges.

Proof: the curvature condition and the Lipschitz bound give
`(β - 1) f' x_k d_k ≤ L α_k ‖d_k‖²`, hence a lower bound on `α_k`; the Armijo condition then gives
`f x_{k+1} ≤ f x_k - (σ (1 - β) / L) (f' x_k d_k / ‖d_k‖)²`, and the sum telescopes to
`f x_0 - M`. Differentiability of `f` is not used: only the three inequalities are. -/
theorem zoutendijk {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : ℕ → E} {α : ℕ → ℝ} {L σ β M : ℝ}
    (hL : ∀ y z, ‖f' y - f' z‖ ≤ L * ‖y - z‖) (hseq : Descent.IsDescentSequence f' x d α)
    (harmijo : ∀ k, Armijo f f' σ (x k) (d k) (α k))
    (hwolfe : ∀ k, WolfeCurvature f' β (x k) (d k) (α k))
    (hσ : 0 < σ) (hβ : β < 1) (hM : ∀ k, M ≤ f (x k)) :
    Summable fun k => (f' (x k) (d k) / ‖d k‖) ^ 2 := by
  have hgneg : ∀ k, f' (x k) (d k) < 0 := hseq.descent
  -- the curvature condition and the Lipschitz bound
  have hstep : ∀ k, (β - 1) * f' (x k) (d k) ≤ L * α k * ‖d k‖ ^ 2 := by
    intro k
    have h1 : β * f' (x k) (d k) ≤ f' (x k + α k • d k) (d k) := hwolfe k
    have h2 : f' (x k + α k • d k) (d k) - f' (x k) (d k) ≤ L * α k * ‖d k‖ ^ 2 := by
      calc f' (x k + α k • d k) (d k) - f' (x k) (d k)
          = (f' (x k + α k • d k) - f' (x k)) (d k) := by simp
        _ ≤ ‖(f' (x k + α k • d k) - f' (x k)) (d k)‖ := by
            rw [Real.norm_eq_abs]; exact le_abs_self _
        _ ≤ ‖f' (x k + α k • d k) - f' (x k)‖ * ‖d k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖x k + α k • d k - x k‖ * ‖d k‖ :=
            mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
        _ = L * α k * ‖d k‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hseq.pos k)]
            ring
    linarith
  have hpos : ∀ k, 0 < (β - 1) * f' (x k) (d k) := fun k =>
    mul_pos_of_neg_of_neg (by linarith) (hgneg k)
  have hd0 : ∀ k, 0 < ‖d k‖ := by
    intro k
    rcases (norm_nonneg (d k)).lt_or_eq with h | h
    · exact h
    · have := hstep k
      rw [← h] at this
      linarith [hpos k]
  have hL0 : 0 < L := by
    by_contra h
    rw [not_lt] at h
    have : L * α 0 * ‖d 0‖ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (hseq.pos 0).le)
        (sq_nonneg _)
    linarith [hstep 0, hpos 0]
  set c : ℝ := σ * (1 - β) / L with hc
  have hc0 : 0 < c := div_pos (mul_pos hσ (by linarith)) hL0
  -- the decrease at every step
  have hdec : ∀ k, c * (f' (x k) (d k) / ‖d k‖) ^ 2 ≤ f (x k) - f (x (k + 1)) := by
    intro k
    have h1 : f (x k + α k • d k) ≤ f (x k) + σ * α k * f' (x k) (d k) := harmijo k
    rw [← hseq.step k] at h1
    have hD : 0 < L * ‖d k‖ ^ 2 := mul_pos hL0 (pow_pos (hd0 k) 2)
    have h2 : (β - 1) * f' (x k) (d k) / (L * ‖d k‖ ^ 2) ≤ α k := by
      rw [div_le_iff₀ hD]
      linarith [hstep k]
    have h3 : σ * α k * f' (x k) (d k)
        ≤ σ * ((β - 1) * f' (x k) (d k) / (L * ‖d k‖ ^ 2)) * f' (x k) (d k) := by
      have := mul_le_mul_of_nonpos_right h2 (hgneg k).le
      nlinarith
    have h4 : σ * ((β - 1) * f' (x k) (d k) / (L * ‖d k‖ ^ 2)) * f' (x k) (d k)
        = -(c * (f' (x k) (d k) / ‖d k‖) ^ 2) := by
      rw [hc]
      field_simp
      ring
    linarith
  refine summable_of_sum_range_le (c := (f (x 0) - M) / c) (fun k => sq_nonneg _) fun n => ?_
  rw [le_div_iff₀ hc0]
  have htel : ∑ i ∈ Finset.range n, (f (x i) - f (x (i + 1))) = f (x 0) - f (x n) :=
    Finset.sum_range_sub' (fun i => f (x i)) n
  have hsum : ∑ i ∈ Finset.range n, c * (f' (x i) (d i) / ‖d i‖) ^ 2
      ≤ ∑ i ∈ Finset.range n, (f (x i) - f (x (i + 1))) :=
    Finset.sum_le_sum fun i _ => hdec i
  rw [htel, ← Finset.mul_sum] at hsum
  linarith [hM n]

/-- **Global convergence of descent methods with Armijo–Wolfe steps**
([quarteroni2000numerical] Property 7.7): under the hypotheses of `LineSearch.zoutendijk` without
the lower bound on `f`, either `f (x_k) → -∞` or `f' x_k d_k / ‖d_k‖ → 0`. Indeed `f (x_k)` is
decreasing; if it is unbounded below it tends to `-∞`, and otherwise Zoutendijk's theorem applies
and the summands tend to `0`. The book's third alternative, `∇f(x_k) = 0` for some `k`, is the
termination case excluded by `IsDescentSequence.descent`. -/
theorem tendsto_atBot_or_tendsto_zero {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : ℕ → E}
    {α : ℕ → ℝ} {L σ β : ℝ} (hL : ∀ y z, ‖f' y - f' z‖ ≤ L * ‖y - z‖)
    (hseq : Descent.IsDescentSequence f' x d α)
    (harmijo : ∀ k, Armijo f f' σ (x k) (d k) (α k))
    (hwolfe : ∀ k, WolfeCurvature f' β (x k) (d k) (α k)) (hσ : 0 < σ) (hβ : β < 1) :
    Tendsto (fun k => f (x k)) atTop atBot ∨
      Tendsto (fun k => f' (x k) (d k) / ‖d k‖) atTop (𝓝 0) := by
  have hanti : Antitone fun k => f (x k) := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h1 : f (x k + α k • d k) ≤ f (x k) + σ * α k * f' (x k) (d k) := harmijo k
    rw [← hseq.step k] at h1
    have : σ * α k * f' (x k) (d k) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hσ (hseq.pos k)) (hseq.descent k)
    linarith
  by_cases hbdd : ∃ M, ∀ k, M ≤ f (x k)
  · obtain ⟨M, hM⟩ := hbdd
    right
    have h1 := (zoutendijk hL hseq harmijo hwolfe hσ hβ hM).tendsto_atTop_zero
    have h2 : Tendsto (fun k => |f' (x k) (d k) / ‖d k‖|) atTop (𝓝 0) := by
      simpa [Real.sqrt_sq_eq_abs] using h1.sqrt
    exact (tendsto_zero_iff_abs_tendsto_zero _).2 h2
  · left
    simp only [not_exists, not_forall, not_le] at hbdd
    exact tendsto_atTop_atBot_of_antitone hanti fun b => (hbdd b).imp fun k hk => hk.le

end LineSearch
