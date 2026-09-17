import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Numlib.Analysis.Convex.Uniform
import Numlib.Analysis.Normed.Module.MilmanPettis
import NumlibSurface.Brezis.Chapter03.Section06

/-!
# Brezis §3.7: uniformly convex spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §3.7, over a real Banach space `E`. The book's
Definition is `IsUniformlyConvex E` (strict inequalities, on the closed unit ball) and
`uniformlyConvex_iff` identifies it with Mathlib's `UniformConvexSpace E` (non-strict, on the
unit sphere); every later node uses the Mathlib class. Example 1 is `EuclideanSpace ℝ (Fin 2)`
against `WithLp 1 (ℝ × ℝ)` and `ℝ × ℝ` (the sup norm); Example 2's Hilbert clause is Mathlib's
`InnerProductSpace.toUniformConvexSpace` and its `L^p` clause is Theorem 4.10 (chapter 4).
Theorem 3.31 (Milman–Pettis) is the backbone `Numlib/Analysis/Normed/Module/MilmanPettis`;
Proposition 3.32 is `Numlib/Analysis/Convex/Uniform`; Remark 21's invariance clause is the
backbone's `NormedSpace.isReflexive_congr`.

## Main results

* `IsUniformlyConvex`, `uniformlyConvex_iff` — the Definition and the bridge to Mathlib.
* `example_3_7_1_euclidean`, `example_3_7_1_l1`, `example_3_7_1_linf`, `example_3_7_2` — the
  three norms on `ℝ²` and Hilbert spaces.
* `theorem_3_31` — Milman–Pettis: uniformly convex Banach spaces are reflexive.
* `remark_3_21` — reflexivity is invariant under equivalent norms, uniform convexity is not.
* `proposition_3_32` — `xₙ ⇀ x` and `limsup ‖xₙ‖ ≤ ‖x‖` give `xₙ → x` strongly.
-/

open Filter Metric Set Topology

namespace Brezis.Chapter03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Definition of §3.7.** A Banach space is uniformly convex if for every `ε > 0` there is
`δ > 0` such that `‖x‖ ≤ 1`, `‖y‖ ≤ 1` and `‖x - y‖ > ε` imply `‖(x + y)/2‖ < 1 - δ`. -/
def IsUniformlyConvex (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε < ‖x - y‖ →
    ‖(1 / 2 : ℝ) • (x + y)‖ < 1 - δ

/-- The book's Definition is Mathlib's `UniformConvexSpace E` (which asks, for `‖x‖ = ‖y‖ = 1`
and `ε ≤ ‖x - y‖`, that `‖x + y‖ ≤ 2 - δ`). -/
theorem uniformlyConvex_iff : IsUniformlyConvex E ↔ UniformConvexSpace E := by
  have hhalf : ∀ v : E, ‖(1 / 2 : ℝ) • v‖ = ‖v‖ / 2 := fun v => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  constructor
  · intro h
    refine ⟨fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hδ'⟩ := h (ε / 2) (by positivity)
    refine ⟨2 * δ, by positivity, fun x hx y hy hxy => ?_⟩
    have := hδ' x y hx.le hy.le (by linarith)
    rw [hhalf] at this
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
    refine ⟨δ / 4, by positivity, fun x y hx hy hxy => ?_⟩
    have := hδ' hx hy hxy.le
    rw [hhalf]
    linarith

/-- **Example 1 of §3.7, first clause.** On `E = ℝ²` the Euclidean norm
`‖x‖₂ = (|x₁|² + |x₂|²)^{1/2}` is uniformly convex. -/
theorem example_3_7_1_euclidean : UniformConvexSpace (EuclideanSpace ℝ (Fin 2)) :=
  inferInstance

/-- **Example 1 of §3.7, second clause.** On `ℝ²` the norm `‖x‖₁ = |x₁| + |x₂|` is not
uniformly convex: `x = (1, 0)`, `y = (0, 1)` have `‖x‖₁ = ‖y‖₁ = 1` and
`‖x - y‖₁ = ‖x + y‖₁ = 2`. -/
theorem example_3_7_1_l1 : ¬ UniformConvexSpace (WithLp 1 (ℝ × ℝ)) := by
  intro h
  obtain ⟨δ, hδ, hs⟩ :=
    exists_forall_sphere_dist_add_le_two_sub (WithLp 1 (ℝ × ℝ)) (ε := 2) two_pos
  have hx : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ))‖ = 1 := by simp
  have hy : ‖WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 1 := by simp
  have hsub : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ)) - WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 2 := by
    rw [← WithLp.toLp_sub]
    simp [WithLp.prod_norm_eq_of_L1]
    norm_num
  have hadd : ‖WithLp.toLp 1 ((1 : ℝ), (0 : ℝ)) + WithLp.toLp 1 ((0 : ℝ), (1 : ℝ))‖ = 2 := by
    rw [← WithLp.toLp_add]
    simp [WithLp.prod_norm_eq_of_L1]
    norm_num
  have := hs hx hy hsub.ge
  linarith

/-- **Example 1 of §3.7, third clause.** On `ℝ²` the norm `‖x‖_∞ = max (|x₁|, |x₂|)` (Mathlib's
norm on `ℝ × ℝ`) is not uniformly convex: `x = (1, 1)`, `y = (1, -1)` have `‖x‖ = ‖y‖ = 1` and
`‖x - y‖ = ‖x + y‖ = 2`. -/
theorem example_3_7_1_linf : ¬ UniformConvexSpace (ℝ × ℝ) := by
  intro h
  obtain ⟨δ, hδ, hs⟩ := exists_forall_sphere_dist_add_le_two_sub (ℝ × ℝ) (ε := 2) two_pos
  have hx : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hy : ‖((1 : ℝ), (-1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hsub : ‖((1 : ℝ), (1 : ℝ)) - ((1 : ℝ), (-1 : ℝ))‖ = 2 := by
    simp [Prod.norm_def]
    norm_num
  have hadd : ‖((1 : ℝ), (1 : ℝ)) + ((1 : ℝ), (-1 : ℝ))‖ = 2 := by
    simp [Prod.norm_def]
    norm_num
  have := hs hx hy hsub.ge
  linarith

/-- **Example 2 of §3.7, Hilbert clause.** Hilbert spaces are uniformly convex (the
parallelogram law); the `L^p` clause, `1 < p < ∞`, is Theorem 4.10. -/
theorem example_3_7_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    UniformConvexSpace H :=
  inferInstance

/-- **Theorem 3.31 (Milman–Pettis).** Every uniformly convex Banach space is reflexive. -/
theorem theorem_3_31 [CompleteSpace E] (h : IsUniformlyConvex E) : IsReflexive E := by
  have := uniformlyConvex_iff.1 h
  exact isReflexive_iff.2 NormedSpace.isReflexive_of_uniformConvexSpace

/-- **Remark 21.** Reflexivity is a topological property — a reflexive space remains reflexive
for an equivalent norm, i.e. reflexivity transfers along a continuous linear equivalence —
whereas uniform convexity is a geometric property of the norm: `ℝ²` with the Euclidean norm and
with the norm `‖·‖₁` are isomorphic Banach spaces, and only the first is uniformly convex. -/
theorem remark_3_21 [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E ≃L[ℝ] F) :
    (IsReflexive E ↔ IsReflexive F) ∧
      (UniformConvexSpace (EuclideanSpace ℝ (Fin 2)) ∧ ¬ UniformConvexSpace (WithLp 1 (ℝ × ℝ)) ∧
        Nonempty (EuclideanSpace ℝ (Fin 2) ≃L[ℝ] WithLp 1 (ℝ × ℝ))) := by
  refine ⟨?_, example_3_7_1_euclidean, example_3_7_1_l1, ⟨?_⟩⟩
  · rw [isReflexive_iff, isReflexive_iff]
    exact NormedSpace.isReflexive_congr e
  · refine (ContinuousLinearEquiv.ofFinrankEq ?_).trans
      (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ ℝ).symm
    simp [Module.finrank_prod]

/-- **Proposition 3.32.** Let `E` be uniformly convex and `(xₙ)` a sequence with `xₙ ⇀ x`
weakly and `limsup ‖xₙ‖ ≤ ‖x‖`. Then `xₙ → x` strongly. -/
theorem proposition_3_32 [CompleteSpace E] (h : IsUniformlyConvex E) {x : ℕ → E} {u : E}
    (hx : x ⇀ u) (hlim : limsup (fun n => ‖x n‖) atTop ≤ ‖u‖) : Tendsto x atTop (𝓝 u) := by
  have := uniformlyConvex_iff.1 h
  exact tendsto_of_forall_dual_tendsto_of_limsup_norm_le ((proposition_3_5 _ _).1 hx) hlim

end Brezis.Chapter03
