import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Order.Zorn

/-!
# Brezis §1.1: the analytic form of the Hahn–Banach theorem

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §1.1: the analytic form of the Hahn–Banach theorem
(Theorem 1.1, with Zorn's lemma, Lemma 1.1) and its corollaries on a real normed space `E` with
dual `E* = StrongDual ℝ E` — the norm-preserving extension of a functional (Corollary 1.2), the
norming functional of a vector (Corollary 1.3, with the duality map of Remark 2 and its
uniqueness clause when `E*` is strictly convex) and the dual description of the norm
(Corollary 1.4). Everything is Mathlib's, restated in the book's words: Theorem 1.1 is
`exists_extension_of_le_sublinear`, Corollary 1.2 is `exists_extension_norm_eq`, Corollary 1.3
is `exists_dual_vector` rescaled, Corollary 1.4 is the isometry `inclusionInDoubleDualLi` read
through `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`.

## Main results

* `theorem_1_1` — Hahn–Banach, analytic form: a linear functional dominated by a positively
  homogeneous subadditive `p` on a subspace extends to all of `E` with the same domination.
* `lemma_1_1` — Zorn's lemma, in the book's formulation.
* `dualNorm_eq` — the dual norm (5), `‖f‖ = sup_{‖x‖ ≤ 1} |f x| = sup_{‖x‖ ≤ 1} f x`.
* `corollary_1_2`, `corollary_1_3`, `corollary_1_4` — the three corollaries.
* `dualityMap`, `dualityMap_nonempty`, `remark_1_2` — the duality map `F x₀` of Remark 2 and its
  uniqueness clause.

Remark 1 (on Zorn's lemma) is discussion; Remark 3 (the dual norm is attained in a reflexive
space, and R. C. James' converse) is stated by the book without proof and is not formalized.
-/

open Metric NormedSpace

namespace Brezis.Chapter01

/-! ### Theorem 1.1 and Lemma 1.1 -/

/-- **Theorem 1.1 (Helly, Hahn–Banach analytic form).** Let `E` be a real vector space and
`p : E → ℝ` with `p (λ • x) = λ * p x` for `λ > 0` (1) and `p (x + y) ≤ p x + p y` (2). If `G` is
a subspace and `g : G → ℝ` a linear functional with `g x ≤ p x` on `G`, there is a linear
functional `f` on all of `E` extending `g` with `f x ≤ p x` for all `x`. -/
theorem theorem_1_1 {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ)
    (hp₁ : ∀ l : ℝ, 0 < l → ∀ x, p (l • x) = l * p x) (hp₂ : ∀ x y, p (x + y) ≤ p x + p y)
    (G : Submodule ℝ E) (g : G →ₗ[ℝ] ℝ) (hg : ∀ x : G, g x ≤ p x) :
    ∃ f : E →ₗ[ℝ] ℝ, (∀ x : G, f x = g x) ∧ ∀ x, f x ≤ p x :=
  exists_extension_of_le_sublinear ⟨G, g⟩ p hp₁ hp₂ hg

/-- **Lemma 1.1 (Zorn).** Every nonempty ordered set that is inductive — every totally ordered
subset has an upper bound — has a maximal element `m`, i.e. `m ≤ x` only for `x = m`. -/
theorem lemma_1_1 {P : Type*} [PartialOrder P] [Nonempty P]
    (h : ∀ c : Set P, IsChain (· ≤ ·) c → BddAbove c) : ∃ m : P, ∀ x, m ≤ x → x = m := by
  obtain ⟨m, hm⟩ := zorn_le h
  exact ⟨m, fun x hx => (hm hx).antisymm hx⟩

/-! ### The dual norm and the corollaries -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The dual norm, formula (5).** For `f ∈ E*`,
`‖f‖ = sup_{‖x‖ ≤ 1} |f x| = sup_{‖x‖ ≤ 1} f x`; the book's `E*` is `StrongDual ℝ E` with its
operator norm. -/
theorem dualNorm_eq (f : StrongDual ℝ E) :
    ‖f‖ = sSup ((fun x => |f x|) '' closedBall 0 1) ∧
      ‖f‖ = sSup ((fun x => f x) '' closedBall 0 1) := by
  have h₁ : ‖f‖ = sSup ((fun x => |f x|) '' closedBall 0 1) :=
    f.sSup_unitClosedBall_eq_norm.symm
  have hle : ∀ x ∈ closedBall (0 : E) 1, |f x| ≤ ‖f‖ := fun x hx =>
    f.unit_le_opNorm x (mem_closedBall_zero_iff.1 hx)
  have hne : (closedBall (0 : E) 1).Nonempty := nonempty_closedBall.2 zero_le_one
  have hbdd : BddAbove ((fun x => f x) '' closedBall 0 1) := by
    refine ⟨‖f‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hle x hx)
  refine ⟨h₁, le_antisymm ?_ ?_⟩
  · rw [h₁]
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    change |f x| ≤ _
    rcases le_total 0 (f x) with h | h
    · rw [abs_of_nonneg h]
      exact le_csSup hbdd ⟨x, hx, rfl⟩
    · rw [abs_of_nonpos h, ← map_neg]
      exact le_csSup hbdd ⟨-x, by simpa using hx, rfl⟩
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (hle x hx)

/-- **Corollary 1.2.** A continuous linear functional `g` on a subspace `G ⊆ E` extends to some
`f ∈ E*` with `‖f‖_{E*} = ‖g‖_{G*}`. -/
theorem corollary_1_2 (G : Submodule ℝ E) (g : StrongDual ℝ G) :
    ∃ f : StrongDual ℝ E, (∀ x : G, f x = g x) ∧ ‖f‖ = ‖g‖ :=
  exists_extension_norm_eq G g

/-- **Corollary 1.3.** For every `x₀ ∈ E` there is `f₀ ∈ E*` with `‖f₀‖ = ‖x₀‖` and
`⟨f₀, x₀⟩ = ‖x₀‖²`. -/
theorem corollary_1_3 (x₀ : E) :
    ∃ f₀ : StrongDual ℝ E, ‖f₀‖ = ‖x₀‖ ∧ f₀ x₀ = ‖x₀‖ ^ 2 := by
  by_cases hx : x₀ = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨g, hg₁, hgx⟩ := exists_dual_vector ℝ x₀ (norm_ne_zero_iff.2 hx)
  refine ⟨‖x₀‖ • g, ?_, ?_⟩
  · rw [norm_smul, hg₁, Real.norm_eq_abs, abs_norm, mul_one]
  · rw [smul_apply, hgx, smul_eq_mul, sq]
    rfl

/-- **The duality map of Remark 2**: `F x₀ = {f₀ ∈ E* | ‖f₀‖ = ‖x₀‖ ∧ ⟨f₀, x₀⟩ = ‖x₀‖²}`, the
set of functionals produced by Corollary 1.3. -/
def dualityMap (x₀ : E) : Set (StrongDual ℝ E) :=
  {f₀ | ‖f₀‖ = ‖x₀‖ ∧ f₀ x₀ = ‖x₀‖ ^ 2}

/-- `F x₀` is nonempty: that is Corollary 1.3. -/
theorem dualityMap_nonempty (x₀ : E) : (dualityMap x₀).Nonempty :=
  corollary_1_3 x₀

/-- **Remark 2.** If `E*` is strictly convex, the functional `f₀` of Corollary 1.3 is unique:
`F x₀` has at most one element. -/
theorem remark_1_2 [StrictConvexSpace ℝ (StrongDual ℝ E)] (x₀ : E) {f₁ f₂ : StrongDual ℝ E}
    (h₁ : f₁ ∈ dualityMap x₀) (h₂ : f₂ ∈ dualityMap x₀) : f₁ = f₂ := by
  obtain ⟨hn₁, hv₁⟩ := h₁
  obtain ⟨hn₂, hv₂⟩ := h₂
  by_cases hx : x₀ = 0
  · subst hx
    rw [norm_zero, norm_eq_zero] at hn₁ hn₂
    rw [hn₁, hn₂]
  have hx' : 0 < ‖x₀‖ := norm_pos_iff.2 hx
  have h := (f₁ + f₂).le_opNorm x₀
  rw [add_apply, hv₁, hv₂, Real.norm_of_nonneg (by positivity)] at h
  have hsum : (‖f₁‖ + ‖f₂‖) * ‖x₀‖ ≤ ‖f₁ + f₂‖ * ‖x₀‖ := by
    rw [hn₁, hn₂]
    nlinarith
  exact eq_of_norm_eq_of_norm_add_eq (hn₁.trans hn₂.symm)
    (le_antisymm (norm_add_le _ _) (le_of_mul_le_mul_right hsum hx'))

/-- **Corollary 1.4, formula (6).** For every `x ∈ E`,
`‖x‖ = sup_{‖f‖ ≤ 1} |⟨f, x⟩| = max_{‖f‖ ≤ 1} |⟨f, x⟩|`: the supremum over the closed unit ball
of `E*` equals `‖x‖`, and it is attained. -/
theorem corollary_1_4 (x : E) :
    ‖x‖ = sSup ((fun f : StrongDual ℝ E => |f x|) '' closedBall 0 1) ∧
      ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ |f x| = ‖x‖ := by
  refine ⟨?_, ?_⟩
  · rw [← (inclusionInDoubleDualLi ℝ).norm_map x,
      ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
    rfl
  · obtain ⟨f, hf, hfx⟩ := exists_dual_vector'' ℝ x
    exact ⟨f, hf, by rw [hfx, RCLike.ofReal_real_eq_id, id, abs_norm]⟩

end Brezis.Chapter01
