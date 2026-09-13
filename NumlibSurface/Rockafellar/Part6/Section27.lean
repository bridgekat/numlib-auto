import Numlib.Analysis.Convex.Optimization.Minimum
import Numlib.Analysis.Convex.Optimization.Prox
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Subgradient.StrictlyConvex
import NumlibSurface.Rockafellar.Part5.Section25

/-!
# Rockafellar, §27: The Minimum of a Convex Function

The unconstrained minimum of a convex function and its duality with `f*` at the origin
(Theorem 27.1); existence, compactness and well-posedness of the minimum set under a recession
hypothesis (Theorems 27.2 and 27.3); and the optimality condition `0 ∈ ∂h(x) + N_C(x)` for
minimising over a convex set (Theorem 27.4).

All 9 numbered results of §27 are formalized: Theorems 27.1–27.4 — 27.1 with its nine clauses
(a)–(i) — and Corollaries 27.2.1, 27.2.2, 27.3.1, 27.3.2 and 27.3.3.

The book's *minimum set* of `f` is the backbone's `argmin f = {x | ∀ z, f x ≤ f z}`, whose unfolded
form is the subgradient inequality at `x* = 0`; `mem_argmin_iff_isMinOn` is the bridge to Mathlib's
`IsMinOn`. The level set `lev_α f` is written out as `{x | f x ≤ (α : EReal)}` and `inf f` is
`⨅ x, f x` in `EReal`, so "bounded below", "finite" and "attained" read as `≠ ⊥`, `≠ ⊥ ∧ ≠ ⊤` and
`(argmin f).Nonempty`. The one definition introduced here is `IsDirectionOfRecession`.

Corollaries 27.2.1 and 27.2.2 are about minimising *sequences* and are stated that way;
`corollary_27_2_1_infDist` records the backbone's arbitrary-filter form of the same fact.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §27 (pp. 263–272).
  Corollary 27.2.1 is stated there with no printed proof, and the polyhedral clause of Theorem 27.3
  is proved there from Helly's theorem.
-/

open Bornology Filter Set Topology

open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis NumlibSurface

variable {n : ℕ}

/-! ### The section's vocabulary -/

section Vocabulary

variable {f : Rn n → EReal} {y : Rn n}

/-- Rockafellar's **direction of recession of `f`**: a nonzero `y` such that `λ ↦ f (x + λ y)` is
non-increasing for every `x`. -/
def IsDirectionOfRecession (f : Rn n → EReal) (y : Rn n) : Prop :=
  y ≠ 0 ∧ ∀ x : Rn n, Antitone fun l : ℝ => f (x + l • y)

/-- A direction of recession is a nonzero element of `recessionConeFn f`. This is Theorem 8.6
(`forall_antitone_iff_recessionFn_nonpos`), which needs no hypothesis on `f` at all. -/
theorem isDirectionOfRecession_iff :
    IsDirectionOfRecession f y ↔ y ≠ 0 ∧ y ∈ recessionConeFn f :=
  and_congr_right fun _ => forall_antitone_iff_recessionFn_nonpos

/-- "`f` has no direction of recession" is `0⁺f = {0}`: the hypothesis of Theorem 27.2 and of the
non-polyhedral case of Theorem 27.3, as the backbone spells it. -/
theorem recessionConeFn_eq_zero_iff (f : Rn n → EReal) :
    recessionConeFn f = {0} ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y := by
  constructor
  · rintro h ⟨y, hy0, hy⟩
    exact hy0 (by
      rw [← Set.mem_singleton_iff, ← h]
      exact forall_antitone_iff_recessionFn_nonpos.1 hy)
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨recessionFn_apply_zero_le f, fun z hz => ?_⟩
    by_contra hz0
    exact h ⟨z, hz0, forall_antitone_iff_recessionFn_nonpos.2 hz⟩

/-- "`f` and `C` have no direction of recession in common", the hypothesis of Theorem 27.3, against
the backbone's `0⁺f ∩ 0⁺C = {0}`. -/
theorem recessionConeFn_inter_eq_zero_iff (f : Rn n → EReal) (C : Set (Rn n)) :
    recessionConeFn f ∩ recessionCone C = {0}
      ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y ∧ y ∈ recessionCone C := by
  constructor
  · rintro h ⟨y, ⟨hy0, hy⟩, hyC⟩
    exact hy0 (by
      rw [← Set.mem_singleton_iff, ← h]
      exact ⟨forall_antitone_iff_recessionFn_nonpos.1 hy, hyC⟩)
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2
      ⟨⟨recessionFn_apply_zero_le f, zero_mem_recessionCone C⟩, fun z hz => ?_⟩
    by_contra hz0
    exact h ⟨z, ⟨hz0, forall_antitone_iff_recessionFn_nonpos.2 hz.1⟩, hz.2⟩

end Vocabulary

/-! ### The section's opening remarks -/

section Opening

variable {f : Rn n → EReal} {x : Rn n}

/-- The minimum set of a convex `f` is convex: when nonempty it is a level set of `f`, which is the
book's reason. -/
theorem convex_argmin_surface (hf : ConvexFn f) : Convex ℝ (argmin f) :=
  convex_argmin hf

/-- The minimum set is closed when `f` is closed. -/
theorem isClosed_argmin (hf : ClosedProperConvexFn f) : IsClosed (argmin f) := by
  rcases Set.eq_empty_or_nonempty (argmin f) with hE | ⟨a, ha⟩
  · rw [hE]; exact isClosed_empty
  · obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
    obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_dom.1 hx₀))
    rw [argmin_eq_setOf_le ha hμ]
    exact (lowerSemicontinuous_iff_isClosed_le.1 hf.lowerSemicontinuous) μ

/-- The minimum set contains at most one point when `f` is strictly convex on `dom f`: two distinct
minimisers lie in `dom f` — a minimiser of a proper `f` has a finite value — and their midpoint
would have a strictly smaller value. -/
theorem subsingleton_argmin_of_strictConvexOnFn (hp : Proper f)
    (hs : StrictConvexOnFn f (dom f)) : (argmin f).Subsingleton := by
  intro x hx y hy
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  have hxd : x ∈ dom f := mem_dom.2 (lt_of_le_of_lt (hx x₀) (mem_dom.1 hx₀))
  have hyd : y ∈ dom f := mem_dom.2 (lt_of_le_of_lt (hy x₀) (mem_dom.1 hx₀))
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (mem_dom.1 hxd)
  have hxy : f x = f y := le_antisymm (hx y) (hy x)
  have hstrict := hs hxd hyd hne (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [← hxy, hμ] at hstrict
  have hval : ((1 / 2 : ℝ) : EReal) * (μ : EReal) + ((1 / 2 : ℝ) : EReal) * (μ : EReal)
      = (μ : EReal) := by
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  rw [hval] at hstrict
  exact absurd (hμ ▸ hx ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) (not_le.2 hstrict)

/-- `x` minimises `f` exactly when `0 ∈ ∂f(x)`: `argmin f` unfolds to the subgradient inequality at
`x* = 0`. -/
theorem mem_argmin_iff_zero_mem_subgradient_surface (f : Rn n → EReal) (x : Rn n) :
    x ∈ argmin f ↔ (0 : Rn n) ∈ subgradient (pairing n) f x :=
  mem_argmin_iff_zero_mem_subgradient (pairing n) f x

/-- By Theorem 23.2: `0 ∈ ∂f(x)` exactly when `f` is finite at `x` and `f'(x; y) ≥ 0` for every
`y`. -/
theorem mem_argmin_iff_zero_le_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    x ∈ argmin f ↔ ∀ y : Rn n, 0 ≤ dirDeriv f x y := by
  rw [mem_argmin_iff_zero_mem_subgradient_surface, mem_subgradient_iff_le_dirDeriv ht hb]
  exact forall_congr' fun y => by simp

/-- One of the most quoted sentences in the subject: a *local* minimum of a proper convex function
is a *global* minimum. Rockafellar routes it through Theorem 23.2 — the directional derivatives see
only an arbitrarily small neighbourhood — while the proof here is the underlying convexity estimate
along `[x, z]`. -/
theorem mem_argmin_of_localMin (hf : ConvexFn f) (hp : Proper f) (hx : x ∈ dom f)
    {ε : ℝ} (hε : 0 < ε) (hloc : ∀ z : Rn n, dist z x < ε → f x ≤ f z) : x ∈ argmin f := by
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) (mem_dom.1 hx)
  intro z
  rcases eq_or_ne (f z) ⊤ with hz | hz
  · rw [hz]; exact le_top
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot z)
    (lt_top_iff_ne_top.2 hz)
  have hr : (0 : ℝ) ≤ ‖z - x‖ := norm_nonneg _
  set t : ℝ := min 1 (ε / (2 * (‖z - x‖ + 1))) with htdef
  have hden : (0 : ℝ) < 2 * (‖z - x‖ + 1) := by positivity
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htr : t * ‖z - x‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
    have h2 : t * ‖z - x‖ ≤ ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ :=
      mul_le_mul_of_nonneg_right h1 hr
    have h3 : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith
  have hdist : dist (x + t • (z - x)) x < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    exact htr
  have hcombo := hf.epi_combo (x := x) (y := z) (μ := μ) (ν := ν) (le_of_eq hμ) (le_of_eq hν)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  have hpt : (1 - t) • x + t • z = x + t • (z - x) := by module
  rw [hpt] at hcombo
  have hchain : (μ : EReal) ≤ (((1 - t) * μ + t * ν : ℝ) : EReal) :=
    le_trans (hμ ▸ hloc _ hdist) hcombo
  rw [EReal.coe_le_coe_iff] at hchain
  rw [hμ, hν, EReal.coe_le_coe_iff]
  nlinarith

end Opening

/-! ### Theorem 27.1(a): the infimum is `-f*(0)` -/

section Theorem271

variable {f : Rn n → EReal}

/-- **Theorem 27.1(a)**. `inf f = -f*(0)`. Needs **no hypothesis at all**, not even convexity: the
theorem's standing "closed proper convex" is there for the other eight clauses. -/
theorem theorem_27_1_a (f : Rn n → EReal) : (⨅ x, f x) = -(conj (pairing n) f 0) :=
  iInf_eq_neg_conj_zero (pairing n) f

/-- **Theorem 27.1(a)**, second sentence: `f` is bounded below iff `0 ∈ dom f*`. Also
hypothesis-free. -/
theorem theorem_27_1_a_bddBelow (f : Rn n → EReal) :
    (⊥ : EReal) < ⨅ x, f x ↔ (0 : Rn n) ∈ dom (conj (pairing n) f) :=
  (zero_mem_dom_conj_iff (pairing n) f).symm

/-! ### Theorem 27.1(b): the minimum set is `∂f*(0)` -/

/-- **Theorem 27.1(b)**, first sentence: the minimum set of a closed convex `f` is `∂f*(0)`, by
Theorem 23.5 at the origin. Properness, which the book assumes throughout, is not needed. -/
theorem theorem_27_1_b (hf : ConvexFn f) (hc : ClosedFn f) :
    argmin f = subgradient (pairing n) (conj (pairing n) f) 0 := by
  rw [argmin_eq_subgradient_conj_zero (B := pairing n) hf hc, flip_pairing]

/-- **Theorem 27.1(b)**, second sentence: the infimum of `f` is attained exactly when `f*` is
subdifferentiable at the origin. -/
theorem theorem_27_1_b_attained (hf : ConvexFn f) (hc : ClosedFn f) :
    (argmin f).Nonempty ↔ (subgradient (pairing n) (conj (pairing n) f) 0).Nonempty := by
  rw [theorem_27_1_b hf hc]

/-- **Theorem 27.1(b)**, third sentence: `0 ∈ ri (dom f*)` is enough for the infimum to be attained.
This is Theorem 23.4 for `f*` at the origin. -/
theorem theorem_27_1_b_relint (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (h0 : (0 : Rn n) ∈ ri (dom (conj (pairing n) f))) : (argmin f).Nonempty := by
  rw [theorem_27_1_b hf hc]
  exact subgradient_nonempty_of_mem_relint_dom (B := pairing n) (convexFn_conj (pairing n) f)
    (proper_conj ⟨hf, hc, hp⟩) h0

/-- **Theorem 27.1(b)**, last sentence: `0 ∈ ri (dom f*)` exactly when every direction of recession
of `f` is a direction in which `f` is constant. Corollary 8.6.1 is what makes `constancySpace f` the
book's phrase. -/
theorem theorem_27_1_b_constancy (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (0 : Rn n) ∈ ri (dom (conj (pairing n) f)) ↔ recessionConeFn f ⊆ constancySpace f :=
  zero_mem_relint_dom_conj_iff_recessionConeFn_subset_constancySpace (B := pairing n) hf hc hp

/-! ### Theorem 27.1(c): finite but unattained -/

/-- **Theorem 27.1(c)**. The infimum of a closed proper convex `f` is finite but unattained exactly
when `f*(0)` is finite and `f*'(0; y) = -∞` for some `y`. **Only one of the book's two finiteness
bounds carries information on each side**; the two that are free are `theorem_27_1_c_free`. -/
theorem theorem_27_1_c (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((⨅ x, f x) ≠ ⊥ ∧ argmin f = ∅)
      ↔ (conj (pairing n) f 0 ≠ ⊤ ∧ ∃ y : Rn n, dirDeriv (conj (pairing n) f) 0 y = ⊥) :=
  iInf_ne_bot_and_argmin_eq_empty_iff (B := pairing n) hf hc hp

/-- The two bounds `theorem_27_1_c` leaves out, so that the reading "finite" can be checked against
the statement: for a proper `f`, `inf f ≠ ⊤` and `f*(0) ≠ ⊥` hold unconditionally. -/
theorem theorem_27_1_c_free (hp : Proper f) :
    (⨅ x, f x) ≠ ⊤ ∧ conj (pairing n) f 0 ≠ ⊥ :=
  ⟨iInf_ne_top hp, conj_ne_bot hp.dom_nonempty 0⟩

/-! ### Theorem 27.1(d): a nonempty bounded minimum set -/

/-- **Theorem 27.1(d)**, first sentence: the minimum set of a closed proper convex `f` is nonempty
and bounded exactly when `0 ∈ int (dom f*)`. -/
theorem theorem_27_1_d (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((argmin f).Nonempty ∧ IsBounded (argmin f))
      ↔ (0 : Rn n) ∈ interior (dom (conj (pairing n) f)) :=
  argmin_nonempty_and_isBounded_iff_zero_mem_interior_dom_conj (B := pairing n) hf hc hp

/-- **Theorem 27.1(d)**, second sentence: that holds exactly when `f` has no direction of
recession. -/
theorem theorem_27_1_d_recession (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (0 : Rn n) ∈ interior (dom (conj (pairing n) f)) ↔ ¬ ∃ y : Rn n, IsDirectionOfRecession f y :=
  (zero_mem_interior_dom_conj_iff_recessionConeFn_eq_zero (B := pairing n) hf hc hp).trans
    (recessionConeFn_eq_zero_iff f)

/-- **Theorem 27.1(d)** in the form Theorem 30.4(g) uses it: *some* level set of `f` is nonempty and
bounded exactly when the minimum set is. -/
theorem theorem_27_1_d_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    ((argmin f).Nonempty ∧ IsBounded (argmin f))
      ↔ ∃ α : ℝ, {x : Rn n | f x ≤ (α : EReal)}.Nonempty ∧
          IsBounded {x : Rn n | f x ≤ (α : EReal)} :=
  argmin_nonempty_and_isBounded_iff_exists_setOf_le (B := pairing n) hf hc hp

/-! ### Theorem 27.1(e): a unique minimiser is `∇f*(0)` -/

/-- **Theorem 27.1(e)**. The minimum set of a closed proper convex `f` is `{x}` exactly when `f*` is
differentiable at the origin with `∇f*(0) = x`. Nothing needs reflexivity: `∂f*(0)` is a subset of
`ℝⁿ`, because the pairing is what says what a dual variable of `f*` is. -/
theorem theorem_27_1_e (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {x : Rn n} :
    argmin f = {x} ↔ HasGradientVecAt (conj (pairing n) f) x 0 := by
  rw [theorem_27_1_b hf hc,
    theorem_25_1 (convexFn_conj (pairing n) f) (proper_conj ⟨hf, hc, hp⟩)]

/-- **Theorem 27.1(e)** as existence: the infimum is attained at a unique point iff `f*` is
differentiable at the origin. -/
theorem theorem_27_1_e_differentiable (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) :
    (∃ x : Rn n, argmin f = {x}) ↔ DifferentiableAtFn (conj (pairing n) f) 0 := by
  rw [differentiableAtFn_iff_exists_hasGradientVecAt]
  exact exists_congr fun _ => theorem_27_1_e hf hc hp

/-- **Theorem 27.1(e)**, the identification `x = ∇f*(0)`: the unique minimiser is computed by
`gradientVec` (§25). -/
theorem theorem_27_1_e_gradientVec (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {x : Rn n}
    (h : argmin f = {x}) : x = gradientVec (conj (pairing n) f) 0 :=
  ((theorem_27_1_e hf hc hp).1 h).gradientVec_eq.symm

/-! ### Theorem 27.1(f): all nonempty level sets share a recession cone -/

/-- **Theorem 27.1(f)**: every nonempty level set of a closed proper convex `f` has the recession
cone of `f`. This is Theorem 8.7, restated here because clause (f) is where §27 uses it. -/
theorem theorem_27_1_f_setOf_le (hf : ClosedProperConvexFn f) {α : ℝ}
    (hne : {x : Rn n | f x ≤ (α : EReal)}.Nonempty) :
    recessionCone {x : Rn n | f x ≤ (α : EReal)} = recessionConeFn f :=
  recessionCone_setOf_le hf.convex hf.isClosed_epi hne

/-- **Theorem 27.1(f)**, the parenthesis: the minimum set, when nonempty, is itself a level set, so
it too has the recession cone of `f`. -/
theorem theorem_27_1_f_argmin (hf : ClosedProperConvexFn f) {a : Rn n} (ha : a ∈ argmin f)
    {μ : ℝ} (hμ : f a = (μ : EReal)) : recessionCone (argmin f) = recessionConeFn f := by
  rw [argmin_eq_setOf_le ha hμ]
  exact theorem_27_1_f_setOf_le hf ⟨a, le_of_eq hμ⟩

/-- **Theorem 27.1(f)**, last sentence: that common recession cone is the polar of the convex cone
generated by `dom f*` — equivalently, since polarity does not see the cone hull, of `dom f*`. -/
theorem theorem_27_1_f_polarCone (hf : ClosedProperConvexFn f) {α : ℝ}
    (hne : {x : Rn n | f x ≤ (α : EReal)}.Nonempty) :
    recessionCone {x : Rn n | f x ≤ (α : EReal)}
      = polarCone (pairing n)
          (PointedCone.hull ℝ (dom (conj (pairing n) f)) : Set (Rn n)) := by
  rw [polarCone_hull]
  have h := recessionCone_setOf_le_eq_polarCone_dom_conj (B := pairing n) hf.convex hf.closed
    hf.proper hne
  rwa [flip_pairing] at h

/-! ### Theorem 27.1(g): support functions of the level sets -/

/-- **Theorem 27.1(g)**, first sentence: for each real `α` the support function of `lev_α f` is the
closure of the positively homogeneous convex function generated by `f* + α`. -/
theorem theorem_27_1_g_setOf_le (hf : ConvexFn f) (hc : ClosedFn f) (α : ℝ) :
    supportFn (pairing n) {x : Rn n | f x ≤ (α : EReal)}
      = clFn (posHomGen fun y => conj (pairing n) f y + (α : EReal)) :=
  supportFn_setOf_le (B := pairing n) hf hc α

/-- **Theorem 27.1(g)**, second sentence: when `f` is bounded below, the support function of the
minimum set is the closure of `f*'(0; ·)`. Clause (b) plus Theorem 23.2; "bounded below" enters as
`f*(0) ≠ ⊤`, which is clause (a). -/
theorem theorem_27_1_g_argmin (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f)
    (hbdd : (⊥ : EReal) < ⨅ x, f x) :
    supportFn (pairing n) (argmin f) = clFn (dirDeriv (conj (pairing n) f) 0) :=
  supportFn_argmin (B := pairing n) hf hc hp
    (lt_top_iff_ne_top.1 (mem_dom.1 ((theorem_27_1_a_bddBelow f).1 hbdd)))

/-! ### Theorem 27.1(h): the limit of the support functions -/

/-- **Theorem 27.1(h)**. If `inf f` is finite then `lim_{α ↓ inf f} δ*(y | lev_α f) = f*'(0; y)` for
every `y`. **The limit is stated as an infimum**: the level sets increase with `α`, so their support
functions do, and the monotone limit *is* the infimum; no filter is needed. -/
theorem theorem_27_1_h (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {μ : ℝ}
    (hμ : (⨅ x, f x) = (μ : EReal)) (y : Rn n) :
    (⨅ ε ∈ Ioi (0 : ℝ), supportFn (pairing n) {z : Rn n | f z ≤ ((μ + ε : ℝ) : EReal)} y)
      = dirDeriv (conj (pairing n) f) 0 y :=
  iInf_supportFn_setOf_le (B := pairing n) hf hc hp hμ y

/-- The identification the proof of Theorem 27.1(h) runs on, unnumbered in the book: the level sets
of `f` above its infimum are the ε-subdifferentials of `f*` at the origin. -/
theorem theorem_27_1_h_epsSubgradient (hf : ConvexFn f) (hc : ClosedFn f) (hp : Proper f) {μ : ℝ}
    (hμ : (⨅ x, f x) = (μ : EReal)) (ε : ℝ) :
    epsSubgradient (pairing n) ε (conj (pairing n) f) 0
      = {z : Rn n | f z ≤ ((μ + ε : ℝ) : EReal)} := by
  rw [← epsSubgradient_conj_zero (B := pairing n) hf hc hp hμ ε, flip_pairing]

/-! ### Theorem 27.1(i): the origin in the closure of `dom f*` -/

/-- **Theorem 27.1(i)**, first sentence: `0 ∈ cl (dom f*)` exactly when `(f0⁺)(y) ≥ 0` for every
`y`. This is the origin case of Corollary 13.3.4. -/
theorem theorem_27_1_i (hf : ClosedProperConvexFn f) :
    (0 : Rn n) ∈ closure (dom (conj (pairing n) f)) ↔ ∀ y : Rn n, 0 ≤ recessionFn f y :=
  zero_mem_closure_dom_conj_iff (B := pairing n) hf

/-- **Theorem 27.1(i)**, second sentence: `0 ∉ cl (dom f*)` exactly when `f` decreases at a uniform
positive rate along some nonzero direction. `y ≠ 0` is automatic — at `y = 0` the inequality at
`λ = 1` would read `0 ≤ -ε` on `dom f` — and restricting `x` to `dom f` costs nothing. -/
theorem theorem_27_1_i_notMem (hf : ClosedProperConvexFn f) :
    (0 : Rn n) ∉ closure (dom (conj (pairing n) f)) ↔
      ∃ y : Rn n, y ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ dom f, ∀ a : ℝ, 0 ≤ a → f (x + a • y) ≤ f x - ((a * ε : ℝ) : EReal) :=
  zero_notMem_closure_dom_conj_iff (B := pairing n) hf

/-- Clauses (a) and (i) together, an unnumbered remark of §27: `f` can recede nowhere at a negative
rate and still be unbounded below, exactly when `0 ∈ cl (dom f*)` but `0 ∉ dom f*`. -/
theorem theorem_27_1_ai (hf : ClosedProperConvexFn f) :
    ((∀ y : Rn n, 0 ≤ recessionFn f y) ∧ (⨅ x, f x) = ⊥)
      ↔ ((0 : Rn n) ∈ closure (dom (conj (pairing n) f)) ∧
          (0 : Rn n) ∉ dom (conj (pairing n) f)) := by
  rw [theorem_27_1_i hf, ← theorem_27_1_a_bddBelow f, not_lt, le_bot_iff]

end Theorem271

/-! ### Theorem 27.2: existence, compactness and well-posedness -/

section Theorem272

variable {f : Rn n → EReal}

/-- **Theorem 27.2**, first sentence: a closed proper convex function with no direction of recession
has a finite infimum. The backbone's proof is the lower-semicontinuous extreme value theorem on a
level set, which Theorems 8.7 and 8.4 make compact. -/
theorem theorem_27_2_finite (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) : ∃ μ : ℝ, (⨅ z, f z) = (μ : EReal) :=
  exists_iInf_eq_coe hf.convex hf.closed hf.proper ((recessionConeFn_eq_zero_iff f).2 hrec)

/-- **Theorem 27.2**, the attainment. -/
theorem theorem_27_2_attained (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) : (argmin f).Nonempty :=
  argmin_nonempty_of_recessionConeFn_eq_zero hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec)

/-- **Theorem 27.2**, last clause: the minimum set is nonempty, closed, bounded and convex. Closed
and bounded is stated as compact, which in `ℝⁿ` is the same thing. -/
theorem theorem_27_2_argmin (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) :
    (argmin f).Nonempty ∧ IsCompact (argmin f) ∧ Convex ℝ (argmin f) :=
  ⟨theorem_27_2_attained hf hrec,
    isCompact_argmin_of_recessionConeFn_eq_zero hf.convex hf.closed hf.proper
      ((recessionConeFn_eq_zero_iff f).2 hrec),
    convex_argmin hf.convex⟩

/-- **Theorem 27.2**, well-posedness: for every `ε > 0` there is a `δ > 0` such that every `x` with
`f x ≤ inf f + δ` lies within `ε` of the minimum set. Rockafellar's nested-compactness argument is
avoided: the extreme value theorem is applied once more, to `lev_{inf f + 1} f \ (M + ε · int
B)`. -/
theorem theorem_27_2_wellPosed (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Rn n, f x ≤ (⨅ z, f z) + (δ : EReal) →
      ∃ z ∈ argmin f, dist x z < ε :=
  exists_pos_forall_exists_mem_argmin_dist_lt hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hε

/-! ### Corollary 27.2.1 -/

/-- **Corollary 27.2.1**, first assertion: a minimising sequence of a closed proper convex function
with no direction of recession is bounded. **The book states this corollary with no proof.** The
argument is Theorem 27.2's well-posedness clause at `ε = 1`, past which the whole sequence lies
within distance `1` of the compact minimum set. -/
theorem corollary_27_2_1_isBounded (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {u : ℕ → Rn n}
    (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) : IsBounded (Set.range u) :=
  isBounded_range_of_tendsto_iInf hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu

/-- **Corollary 27.2.1**: every cluster point of a minimising sequence lies in the minimum set. -/
theorem corollary_27_2_1_clusterPt (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {u : ℕ → Rn n}
    (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) {x : Rn n}
    (hx : MapClusterPt x atTop u) : x ∈ argmin f :=
  mem_argmin_of_mapClusterPt hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu hx

/-- The substance of Corollary 27.2.1: along any minimising net the distance to the minimum set
tends to `0`. Stated for an arbitrary filter, of which the book's `atTop` is one instance. -/
theorem corollary_27_2_1_infDist (hf : ClosedProperConvexFn f)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession f y) {ι : Type*} {l : Filter ι} {u : ι → Rn n}
    (hu : Tendsto (fun i => f (u i)) l (𝓝 (⨅ z, f z))) :
    Tendsto (fun i => Metric.infDist (u i) (argmin f)) l (𝓝 0) :=
  tendsto_infDist_argmin hf.convex hf.closed hf.proper
    ((recessionConeFn_eq_zero_iff f).2 hrec) hu

/-! ### Corollary 27.2.2 -/

/-- **Corollary 27.2.2** — the label is printed in mixed case in the book. If a closed proper convex
function attains its infimum at a unique `x`, every minimising sequence converges to `x`. No
recession hypothesis: a one-point minimum set is a level set, so Theorem 8.7 forces `0⁺f = {0}`. -/
theorem corollary_27_2_2 (hf : ClosedProperConvexFn f) {a : Rn n} (hM : argmin f = {a})
    {u : ℕ → Rn n} (hu : Tendsto (fun i => f (u i)) atTop (𝓝 (⨅ z, f z))) :
    Tendsto u atTop (𝓝 a) :=
  tendsto_of_argmin_eq_singleton hf.convex hf.closed hf.proper hM hu

end Theorem272

/-! ### Theorem 27.3: minimising over a closed convex set -/

section Theorem273

variable {h : Rn n → EReal} {C : Set (Rn n)}

/-- **Theorem 27.3**, the non-polyhedral case: a closed proper convex `h` attains its infimum over a
nonempty closed convex `C` as soon as `h` and `C` have no direction of recession in common. The
degenerate case `dom h ∩ C = ∅`, where every point of `C` minimises, is dispatched separately. -/
theorem theorem_27_3 (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty)
    (hrec : ¬ ∃ y : Rn n, IsDirectionOfRecession h y ∧ y ∈ recessionCone C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_recessionConeFn_inter_eq_zero hh hC hCc hCne
    ((recessionConeFn_inter_eq_zero_iff h C).2 hrec)

/-- **Theorem 27.3**, the polyhedral refinement: for polyhedral `C` it is enough that every common
direction of recession of `h` and `C` be one in which `h` is *constant*. The book proves this from
Helly's theorem (Theorem 21.5); the proof here projects `ℝⁿ` along the constancy space of `h`. -/
theorem theorem_27_3_polyhedral (hh : ClosedProperConvexFn h) (hC : Polyhedral C)
    (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hC hCne hrec

/-- **Theorem 27.3** in a form the book does not state but its proof gives: for a general closed
convex `C` the hypothesis weakens to "every common direction of recession is one in which `h` is
constant *and* `C` is linear". This sits strictly between the book's two clauses. -/
theorem theorem_27_3_lineality (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h ∩ linealitySpace C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace hh hC hCc hCne hrec

/-! ### Corollary 27.3.1 -/

/-- **Corollary 27.3.1**. If every direction of recession of a closed proper convex `h` is one in
which `h` is *affine*, then `h` attains its infimum relative to any polyhedral convex `C` on which
it is bounded below. The lower bound cannot be dropped: `h(ξ₁, ξ₂) = ξ₁` is affine in every
direction and its infimum over `{ξ₂ = 0}` is `-∞`. -/
theorem corollary_27_3_1 (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ⊆ linealitySpaceFn h) {β : ℝ}
    (hbdd : ∀ x ∈ C, (β : EReal) ≤ h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn hh hC hCne hrec hbdd

/-- The unconstrained case of the polyhedral refinement of Theorem 27.3, which the book does not
separate out: a closed proper convex function whose recession cone consists of directions of
constancy attains its infimum. -/
theorem corollary_27_3_1_unconstrained (hh : ClosedProperConvexFn h)
    (hrec : recessionConeFn h ⊆ constancySpace h) : (argmin h).Nonempty :=
  argmin_nonempty_of_recessionConeFn_subset_constancySpace hh hrec

/-! ### Corollary 27.3.2 -/

/-- **Corollary 27.3.2**. A polyhedral convex function attains its infimum relative to any
polyhedral convex set on which it is bounded below. The book derives this from Corollary 27.3.1 and
so from Helly's theorem; the proof here needs neither. -/
theorem corollary_27_3_2 (hh : PolyhedralFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hbdd : (⊥ : EReal) < ⨅ x ∈ C, h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z :=
  exists_forall_le_of_polyhedralFn_of_polyhedral hh hC hCne hbdd

/-- Corollary 27.3.2 unconstrained. Neither closedness nor properness is assumed: boundedness below
already excludes `-∞`, and `h ≡ +∞` is minimised everywhere. -/
theorem corollary_27_3_2_unconstrained (hh : PolyhedralFn h) (hbdd : (⊥ : EReal) < ⨅ x, h x) :
    (argmin h).Nonempty :=
  argmin_nonempty_of_polyhedralFn hh hbdd

end Theorem273

/-! ### Corollary 27.3.3: an arbitrary system of convex inequalities -/

section Corollary2733

variable {ι : Type*} {f₀ : Rn n → EReal} {g : ι → Rn n → EReal}

/-- **Corollary 27.3.3**, the non-polyhedral case: a closed proper convex `f₀` attains its infimum
subject to a consistent system `fᵢ x ≤ 0`, `i ∈ I`, of closed proper convex constraints, provided
`f₀` and the `fᵢ` have no direction of recession in common. The index set is arbitrary. -/
theorem corollary_27_3_3 (hf₀ : ClosedProperConvexFn f₀) (hg : ∀ i, ClosedProperConvexFn (g i))
    (hCne : {x : Rn n | ∀ i, g i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn f₀ ∩ ⋂ i, recessionConeFn (g i) = {0}) :
    ∃ x, (∀ i, g i x ≤ 0) ∧ ∀ z, (∀ i, g i z ≤ 0) → f₀ x ≤ f₀ z :=
  exists_forall_le_of_forall_le_zero hf₀ hg hCne hrec

/-! #### The polyhedral refinement

The book splits the index set as `I = I₀ ⊔ (I ∖ I₀)` with `I₀` finite; two index *types* say the
same thing and keep every `DecidableEq` out of the statement. `ι₀` is the book's `I₀`. -/

/-- **Corollary 27.3.3**, the polyhedral refinement: the infimum is attained if the constraints
split into a *finite* polyhedral family `g₀` and an arbitrary family `g₁`, and the only common
directions of recession are ones in which `f₀` and all the `g₁` are constant. The book's own
reduction lands on the polyhedral case of Theorem 27.3, so Helly's theorem is not needed. -/
theorem corollary_27_3_3_polyhedral {ι₀ ι₁ : Type*} [Finite ι₀]
    {g₀ : ι₀ → Rn n → EReal} {g₁ : ι₁ → Rn n → EReal}
    (hf₀ : ClosedProperConvexFn f₀) (hg₀ : ∀ i, PolyhedralFn (g₀ i))
    (hg₁ : ∀ i, ClosedProperConvexFn (g₁ i))
    (hne : {x : Rn n | (∀ i, g₀ i x ≤ 0) ∧ ∀ i, g₁ i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn f₀ ∩ (⋂ i, recessionConeFn (g₀ i)) ∩ (⋂ i, recessionConeFn (g₁ i))
      ⊆ constancySpace f₀ ∩ ⋂ i, constancySpace (g₁ i)) :
    ∃ x : Rn n, ((∀ i, g₀ i x ≤ 0) ∧ ∀ i, g₁ i x ≤ 0) ∧
      ∀ z : Rn n, ((∀ i, g₀ i z ≤ 0) ∧ ∀ i, g₁ i z ≤ 0) → f₀ x ≤ f₀ z := by
  obtain ⟨C, hCdef⟩ : ∃ C : Set (Rn n), C = ⋂ i, {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Set (Rn n), D = ⋂ i, {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  have hmemC : ∀ z : Rn n, z ∈ C ↔ ∀ i, g₀ i z ≤ 0 := by
    intro z; rw [hCdef]; simp
  have hmemD : ∀ z : Rn n, z ∈ D ↔ ∀ i, g₁ i z ≤ 0 := by
    intro z; rw [hDdef]; simp
  obtain ⟨w, hwC, hwD⟩ := hne
  have hwCm : w ∈ C := (hmemC w).2 hwC
  have hwDm : w ∈ D := (hmemD w).2 hwD
  have hC0conv : ∀ i, Convex ℝ {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg₀ i).convexFn.convex_le _
  have hC0closed : ∀ i, IsClosed {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    ((hg₀ i).polyhedral_sublevel 0).isClosed
  have hD1conv : ∀ i, Convex ℝ {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg₁ i).convex.convex_le _
  have hD1closed : ∀ i, IsClosed {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    lowerSemicontinuous_iff_isClosed_le.1 (hg₁ i).lowerSemicontinuous 0
  have hCpoly : Polyhedral C := by
    rw [hCdef]; exact polyhedral_iInter fun i => (hg₀ i).polyhedral_sublevel 0
  have hDconv : Convex ℝ D := by rw [hDdef]; exact convex_iInter hD1conv
  have hDclosed : IsClosed D := by rw [hDdef]; exact isClosed_iInter hD1closed
  have hCrec : recessionCone C = ⋂ i, recessionConeFn (g₀ i) := by
    have hwCm' : w ∈ ⋂ i, {z : Rn n | g₀ i z ≤ ((0 : ℝ) : EReal)} := hCdef ▸ hwCm
    rw [hCdef, recessionCone_iInter hC0conv hC0closed ⟨w, hwCm'⟩]
    exact Set.iInter_congr fun i => recessionCone_setOf_le (hg₀ i).convexFn (hg₀ i).isClosed_epi
      ⟨w, Set.mem_iInter.1 hwCm' i⟩
  have hDrec : recessionCone D = ⋂ i, recessionConeFn (g₁ i) := by
    have hwDm' : w ∈ ⋂ i, {z : Rn n | g₁ i z ≤ ((0 : ℝ) : EReal)} := hDdef ▸ hwDm
    rw [hDdef, recessionCone_iInter hD1conv hD1closed ⟨w, hwDm'⟩]
    exact Set.iInter_congr fun i => recessionCone_setOf_le (hg₁ i).convex (hg₁ i).isClosed_epi
      ⟨w, Set.mem_iInter.1 hwDm' i⟩
  by_cases hfin : ∃ v : Rn n, ((∀ i, g₀ i v ≤ 0) ∧ ∀ i, g₁ i v ≤ 0) ∧ f₀ v ≠ ⊤
  · obtain ⟨v, ⟨hvC, hvD⟩, hvtop⟩ := hfin
    have hvCm : v ∈ C := (hmemC v).2 hvC
    have hvDm : v ∈ D := (hmemD v).2 hvD
    have hval : ∀ z : Rn n, z ∈ D → (f₀ + indicatorFn D) z = f₀ z := fun z hz => by
      rw [Pi.add_apply, indicatorFn_of_mem hz, add_zero]
    have hdom : (dom (f₀ + indicatorFn D)).Nonempty :=
      ⟨v, mem_dom.2 (by rw [hval v hvDm]; exact lt_top_iff_ne_top.2 hvtop)⟩
    have hh : ClosedProperConvexFn (f₀ + indicatorFn D) :=
      hf₀.add (closedProperConvexFn_indicatorFn hDconv hDclosed ⟨w, hwDm⟩) hdom
    have hhrec : recessionConeFn (f₀ + indicatorFn D) = recessionConeFn f₀ ∩ recessionCone D :=
      recessionConeFn_add_indicatorFn hf₀ hDconv hDclosed ⟨w, hwDm⟩ hdom
    have hkey : recessionConeFn (f₀ + indicatorFn D) ∩ recessionCone C
        ⊆ constancySpace (f₀ + indicatorFn D) := by
      rintro y ⟨hy1, hy2⟩
      rw [hhrec] at hy1
      have hy : y ∈ recessionConeFn f₀ ∩ (⋂ i, recessionConeFn (g₀ i))
          ∩ (⋂ i, recessionConeFn (g₁ i)) :=
        ⟨⟨hy1.1, hCrec ▸ hy2⟩, hDrec ▸ hy1.2⟩
      obtain ⟨hyf, hyg⟩ := hrec hy
      have hyD : ∀ b : Rn n, (b ∈ recessionConeFn f₀ ∧ ∀ i, b ∈ recessionConeFn (g₁ i)) →
          b ∈ recessionConeFn (f₀ + indicatorFn D) := by
        intro b hb
        rw [hhrec]
        exact ⟨hb.1, hDrec ▸ Set.mem_iInter.2 hb.2⟩
      refine mem_constancySpace.2 ⟨hyD y ⟨(mem_constancySpace.1 hyf).1, fun i =>
        (mem_constancySpace.1 (Set.mem_iInter.1 hyg i)).1⟩,
        hyD (-y) ⟨(mem_constancySpace.1 hyf).2, fun i =>
          (mem_constancySpace.1 (Set.mem_iInter.1 hyg i)).2⟩⟩
    obtain ⟨x, hxC, hxmin⟩ :=
      exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hCpoly ⟨w, hwCm⟩ hkey
    have hxlt : (f₀ + indicatorFn D) x < ⊤ :=
      lt_of_le_of_lt (hxmin v hvCm) (by rw [hval v hvDm]; exact lt_top_iff_ne_top.2 hvtop)
    have hxD : x ∈ D := by
      by_contra hcon
      rw [Pi.add_apply, indicatorFn_of_notMem hcon,
        EReal.add_top_of_ne_bot (hf₀.proper.ne_bot x)] at hxlt
      exact absurd hxlt (lt_irrefl ⊤)
    refine ⟨x, ⟨(hmemC x).1 hxC, (hmemD x).1 hxD⟩, fun z hz => ?_⟩
    have hstep := hxmin z ((hmemC z).2 hz.1)
    rwa [hval x hxD, hval z ((hmemD z).2 hz.2)] at hstep
  · push Not at hfin
    exact ⟨w, ⟨hwC, hwD⟩, fun z hz => by rw [hfin w ⟨hwC, hwD⟩, hfin z hz]⟩

end Corollary2733

/-! ### Theorem 27.4: the subdifferential optimality condition -/

section Theorem274

variable {h : Rn n → EReal} {C : Set (Rn n)} {x : Rn n}

/-- **Theorem 27.4**, sufficiency: if some `x* ∈ ∂h(x)` has `-x*` normal to `C` at `x`, then `h`
attains its infimum relative to `C` at `x`. Needs **no hypothesis at all** — not properness of `h`,
not convexity of `C`, not even `x ∈ C`: the two inequalities simply add. -/
theorem theorem_27_4_sufficient {y : Rn n} (hy : y ∈ subgradient (pairing n) h x)
    (hn : -y ∈ normalCone (pairing n) C x) {z : Rn n} (hz : z ∈ C) : h x ≤ h z :=
  le_of_mem_subgradient_of_neg_mem_normalCone hy hn hz

/-- **Theorem 27.4**, necessity under the book's first constraint qualification: `ri (dom h)` meets
`ri C`. The exactness of the sum `h + δ(· | C)` comes from Theorem 16.4; Rockafellar's proof cites
Theorem 23.8 for the same step. -/
theorem theorem_27_4_necessary (hh : ConvexFn h) (hp : Proper h) (hC : Convex ℝ C)
    (hCne : C.Nonempty) {x₀ : Rn n} (hx₀h : x₀ ∈ ri (dom h)) (hx₀C : x₀ ∈ ri C)
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subgradient (pairing n) h x, -y ∈ normalCone (pairing n) C x :=
  exists_mem_subgradient_neg_mem_normalCone
    (IsExactSum.of_relint (B := pairing n) hh hp (convexFn_indicatorFn.2 hC)
      (proper_indicatorFn.2 hCne) hx₀h (by rw [dom_indicatorFn]; exact hx₀C)) hx hmin

/-- **Theorem 27.4**, necessity under the book's second constraint qualification: `C` polyhedral and
`ri (dom h)` meets `C` — merely `C`, not `ri C`, since the polyhedral summand of the `IsExactSum` of
Theorem 20.1 needs only a point of its effective domain. -/
theorem theorem_27_4_necessary_polyhedral (hh : ConvexFn h) (hp : Proper h) (hC : Polyhedral C)
    {x₀ : Rn n} (hx₀h : x₀ ∈ ri (dom h)) (hx₀C : x₀ ∈ C)
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subgradient (pairing n) h x, -y ∈ normalCone (pairing n) C x :=
  exists_mem_subgradient_neg_mem_normalCone
    (IsExactSum.symm (IsExactSum.of_polyhedral (B := pairing n) (polyhedralFn_indicatorFn hC)
      (proper_indicatorFn.2 ⟨x₀, hx₀C⟩) hh hp (by rw [dom_indicatorFn]; exact hx₀C) hx₀h))
    hx hmin

private theorem quadFn_le_quadFn_iff (u v : Rn n) :
    quadFn (pairing n) u ≤ quadFn (pairing n) v ↔ ‖u‖ ≤ ‖v‖ := by
  rw [quadFn_apply, quadFn_apply, EReal.coe_le_coe_iff, pairing_apply, pairing_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, div_le_div_iff_of_pos_right two_pos]
  exact pow_le_pow_iff_left₀ (norm_nonneg u) (norm_nonneg v) two_ne_zero

/-- The headline application of Theorem 27.4, and the projection theorem: `x` is the point of a
nonempty convex `C` nearest to `a` exactly when `a - x` is normal to `C` at `x`. Closedness of `C`
is not needed for the characterisation, only for the existence of a nearest point. -/
theorem nearest_iff_sub_mem_normalCone (hC : Convex ℝ C) (hCne : C.Nonempty) {a : Rn n}
    (hx : x ∈ C) :
    (∀ z ∈ C, dist a x ≤ dist a z) ↔ a - x ∈ normalCone (pairing n) C x := by
  have hdist : ∀ u : Rn n, dist a u = ‖a - u‖ := fun u => dist_eq_norm a u
  have hdom : dom (fun u => quadFn (pairing n) (a - u)) = Set.univ :=
    Set.eq_univ_iff_forall.2 fun u => mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))
  have hmin : (∀ z ∈ C, dist a x ≤ dist a z) ↔
      ∀ z ∈ C, quadFn (pairing n) (a - x) ≤ quadFn (pairing n) (a - z) := by
    refine forall_congr' fun z => forall_congr' fun _ => ?_
    rw [quadFn_le_quadFn_iff, hdist, hdist]
  rw [hmin]
  constructor
  · intro hmin'
    obtain ⟨x₀, hx₀⟩ := Convex.relint_nonempty hC hCne
    obtain ⟨y, hy, hny⟩ := theorem_27_4_necessary (convexFn_quadFn_sub a) (proper_quadFn_sub a) hC
      hCne (x₀ := x₀) (by rw [hdom, intrinsicInterior_univ]; trivial) hx₀ hx hmin'
    rw [subgradient_quadFn_sub, Set.mem_singleton_iff] at hy
    rwa [hy, neg_sub] at hny
  · intro hn z hz
    refine theorem_27_4_sufficient (h := fun u => quadFn (pairing n) (a - u)) (y := x - a)
      ?_ ?_ hz
    · rw [subgradient_quadFn_sub]
      exact Set.mem_singleton _
    · rwa [neg_sub]

end Theorem274

end Rockafellar
