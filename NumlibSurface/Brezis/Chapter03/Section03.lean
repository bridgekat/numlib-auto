import Mathlib.Analysis.Convex.Combination
import Numlib.Analysis.Convex.Epigraph
import Numlib.Variational.WeakMinimization
import NumlibSurface.Brezis.Chapter03.Section02

/-!
# Brezis §3.3: weak topology, convex sets, and linear operators

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.3, over real Banach spaces `E`, `F`. Theorem 3.7
(Mazur), Corollary 3.9, Remark 6 and Theorem 3.10 with Remark 7 are the backbone
`Numlib/Analysis/Normed/Module/WeakClosed`; Corollary 3.8 (Mazur's lemma) is the backbone's
`exists_seq_convexCombination_tendsto` of `Numlib/Variational/WeakMinimization`; Remark 5 is
Mathlib's `RCLike.iInter_halfSpaces_eq'` at `𝕜 = ℝ`. Functions `φ : E → (−∞, +∞]` are
`E → EReal`, convex as `ConvexAnalysis.ConvexFn` and l.s.c. as `LowerSemicontinuous`, as in
chapter 1's §1.4.

## Main results

* `theorem_3_7` — Mazur: a convex set is weakly closed iff it is strongly closed.
* `corollary_3_8` — Mazur's lemma: if `xₙ ⇀ x` there are convex combinations of the `xₙ`
  converging strongly to `x`.
* `remark_3_5` — a closed convex set is the intersection of the closed half-spaces containing it.
* `corollary_3_9`, `remark_3_6` — a convex strongly l.s.c. function is weakly l.s.c.; in
  particular the norm, and `‖x‖ ≤ liminf ‖xₙ‖` again.
* `theorem_3_10`, `remark_3_7` — a linear operator is strongly continuous iff weak–weak
  continuous; strong–weak continuity already gives strong–strong.

Remark 7's second clause (weak–strong continuous iff finite rank, Exercise 6.7) and its last
paragraph (nonlinear maps, Exercise 4.20) are not stated.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Theorem 3.7 (Mazur).** A convex subset `C ⊆ E` is closed in the weak topology `σ(E, E*)`
iff it is closed in the strong topology. -/
theorem theorem_3_7 [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) :
    IsClosed (toWeakSpace ℝ E '' C) ↔ IsClosed C :=
  hC.isClosed_image_toWeakSpace_iff

/-- **Corollary 3.8 (Mazur's lemma).** If `xₙ ⇀ x` weakly, there is a sequence `yₙ` made up of
convex combinations of the `xₙ` that converges strongly to `x`; the combinations may be taken
from the tails `x_n, …, x_{N n}`. -/
theorem corollary_3_8 [CompleteSpace E] {x : ℕ → E} {u : E} (h : x ⇀ u) :
    (∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • x i) atTop (𝓝 u)) ∧
    ∃ y : ℕ → E, (∀ n, y n ∈ convexHull ℝ (Set.range x)) ∧ Tendsto y atTop (𝓝 u) := by
  obtain ⟨N, lam, hN, hlam0, hlam1, hlim⟩ :=
    exists_seq_convexCombination_tendsto (weakSeqTendsto_iff_tendsto_toWeakSpace.2 h)
  refine ⟨⟨N, lam, hN, hlam0, hlam1, hlim⟩, fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • x i,
    fun n => ?_, hlim⟩
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hlam0 n i) (hlam1 n)
    fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩

/-- **Remark 5.** Every closed convex set `C` coincides with the intersection of all the closed
half-spaces containing it. -/
theorem remark_3_5 [CompleteSpace E] {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) :
    ⋂ (f : StrongDual ℝ E) (c : ℝ) (_ : ∀ y ∈ C, f y ≤ c), {x | f x ≤ c} = C := by
  have := RCLike.iInter_halfSpaces_eq' (𝕜 := ℝ) hC hCc
  simpa only [RCLike.re_to_real] using this

/-- **Corollary 3.9.** A convex function `φ : E → (−∞, +∞]` that is l.s.c. in the strong
topology is l.s.c. in the weak topology `σ(E, E*)`. -/
theorem corollary_3_9 [CompleteSpace E] {φ : E → EReal} (hφ : ConvexAnalysis.ConvexFn φ)
    (hlsc : LowerSemicontinuous φ) : LowerSemicontinuous (φ ∘ (toWeakSpace ℝ E).symm) :=
  hlsc.comp_toWeakSpace_symm_of_convex_le (𝕜 := ℝ) fun b => hφ.convex_le b

/-- **Remark 6.** A convex strongly continuous function is weakly l.s.c.; for example the norm
`φ x = ‖x‖` is weakly l.s.c., and in particular `xₙ ⇀ x` implies `‖x‖ ≤ liminf ‖xₙ‖`
(Proposition 3.5 (iii) again). -/
theorem remark_3_6 [CompleteSpace E] :
    (∀ φ : E → ℝ, ConvexOn ℝ Set.univ φ → Continuous φ →
      LowerSemicontinuous (φ ∘ (toWeakSpace ℝ E).symm)) ∧
    LowerSemicontinuous (fun x : WeakSpace ℝ E => ‖(toWeakSpace ℝ E).symm x‖) ∧
    ∀ (x : ℕ → E) (u : E), x ⇀ u → ‖u‖ ≤ liminf (fun n => ‖x n‖) atTop :=
  ⟨fun _ hφ hc => hφ.lowerSemicontinuous_comp_toWeakSpace_symm (𝕜 := ℝ) hc.lowerSemicontinuous,
    lowerSemicontinuous_norm_comp_toWeakSpace_symm (𝕜 := ℝ),
    fun _ _ h => proposition_3_5_iii_liminf h⟩

/-- **Theorem 3.10.** Let `E`, `F` be Banach spaces and `T : E → F` a linear operator. Then `T`
is continuous in the strong topologies iff it is continuous from `E` weak `σ(E, E*)` into `F`
weak `σ(F, F*)`. -/
theorem theorem_3_10 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F) :
    Continuous T ↔
      Continuous (fun x : WeakSpace ℝ E => toWeakSpace ℝ F (T ((toWeakSpace ℝ E).symm x))) :=
  T.continuous_iff_continuous_weakSpace

/-- **Remark 7.** A linear operator continuous from `E` strong into `F` weak is continuous from
`E` strong into `F` strong; so for linear operators the continuity properties `S → S`, `W → W`
and `S → W` are all the same. -/
theorem remark_3_7 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F)
    (hT : Continuous (fun x => toWeakSpace ℝ F (T x))) : Continuous T :=
  T.continuous_of_continuous_toWeakSpace_comp hT

end Brezis.Chapter03
