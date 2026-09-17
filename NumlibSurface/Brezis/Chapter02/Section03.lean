import Mathlib.Analysis.Normed.Operator.Banach
import NumlibSurface.Brezis.Chapter02.Section02

/-!
# Brezis §2.3: the open mapping theorem and the closed graph theorem

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.3, for real Banach spaces `E`, `F`. All of it is
Mathlib (`Mathlib/Analysis/Normed/Operator/Banach.lean`):
`ContinuousLinearMap.exists_preimage_norm_le` is Theorem 2.6, `ContinuousLinearMap.isOpenMap` is
Remark 5, `ContinuousLinearEquiv.ofBijective` is Corollary 2.7,
`LinearMap.continuous_of_isClosed_graph` is Theorem 2.9. Corollary 2.8 is stated, as in the
book, for one vector space carrying two complete norms: the norms are two `Norm E`
structures satisfying `NormedSpace.Core` and the completeness hypotheses refer to the metrics
they induce; the proof registers each on a type synonym and applies Corollary 2.7 to the
identity.

## Main results

* `theorem_2_6` — the open mapping theorem, `T(B_E(0, 1)) ⊇ B_F(0, c)`.
* `remark_2_5` — a surjective bounded operator is an open map.
* `corollary_2_7` — a bijective bounded operator has a bounded inverse, with `‖x‖ ≤ (1/c) ‖T x‖`.
* `corollary_2_8` — two complete norms, one dominating the other, are equivalent.
* `theorem_2_9`, `remark_2_6` — the closed graph theorem and its converse.

The two steps of the proof of Theorem 2.6 are Mathlib's
`ContinuousLinearMap.exists_approx_preimage_norm_le` and, for closed operators, the backbone's
`LinearPMap.IsClosed.exists_preimage_norm_le_of_approx`.
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Theorem 2.6 (open mapping theorem).** Let `E`, `F` be Banach spaces and `T : E → F` a
surjective bounded operator. Then there is `c > 0` with `T(B_E(0, 1)) ⊇ B_F(0, c)` (7). -/
theorem theorem_2_6 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : ∃ c > 0, ball (0 : F) c ⊆ T '' ball 0 1 := by
  obtain ⟨C, hC, h⟩ := T.exists_preimage_norm_le hT
  refine ⟨1 / C, by positivity, fun y hy => ?_⟩
  obtain ⟨x, hx, hxn⟩ := h y
  refine ⟨x, ?_, hx⟩
  rw [mem_ball_zero_iff] at hy ⊢
  calc ‖x‖ ≤ C * ‖y‖ := hxn
    _ < C * (1 / C) := by gcongr
    _ = 1 := by field_simp

/-- **Remark 5.** A surjective bounded operator between Banach spaces maps open sets to open
sets. -/
theorem remark_2_5 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : IsOpenMap T :=
  T.isOpenMap hT

/-- **Corollary 2.7.** Let `E`, `F` be Banach spaces and `T : E → F` a bijective bounded
operator. Then `T⁻¹` is continuous: there is a bounded `S : F → E` inverse to `T`, and a
constant `c > 0` with `‖x‖ ≤ (1/c) ‖T x‖` for all `x`. -/
theorem corollary_2_7 [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : Function.Bijective T) :
    (∃ S : F →L[ℝ] E, Function.LeftInverse S T ∧ Function.RightInverse S T) ∧
      ∃ c > 0, ∀ x, ‖x‖ ≤ (1 / c) * ‖T x‖ := by
  let e := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.2 hT.1)
    (LinearMap.range_eq_top.2 hT.2)
  refine ⟨⟨e.symm, e.symm_apply_apply, e.apply_symm_apply⟩,
    1 / (‖(e.symm : F →L[ℝ] E)‖ + 1), by positivity, fun x => ?_⟩
  rw [one_div_one_div]
  calc ‖x‖ = ‖e.symm (T x)‖ := by rw [show T x = e x from rfl, e.symm_apply_apply]
    _ ≤ ‖(e.symm : F →L[ℝ] E)‖ * ‖T x‖ := (e.symm : F →L[ℝ] E).le_opNorm _
    _ ≤ (‖(e.symm : F →L[ℝ] E)‖ + 1) * ‖T x‖ := by gcongr; linarith

/-! ### Corollary 2.8: two complete norms on one space -/

section TwoNorms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The vector space `V` carrying the norm `n`, as a type synonym on which the normed-space
structure of `h` is registered (the way Mathlib puts two norms on one space). -/
private def WithNormCore (V : Type*) [AddCommGroup V] [Module ℝ V] {n : Norm V}
    (_h : @NormedSpace.Core ℝ V _ _ _ n) : Type _ := V

variable {n : Norm V} (h : @NormedSpace.Core ℝ V _ _ _ n)

private noncomputable instance : NormedAddCommGroup (WithNormCore V h) :=
  @NormedAddCommGroup.ofCore ℝ V _ _ _ n h

private instance : Module ℝ (WithNormCore V h) := ‹Module ℝ V›

private noncomputable instance : NormedSpace ℝ (WithNormCore V h) :=
  @NormedSpace.ofCore ℝ (WithNormCore V h) _ _ _ h

/-- **Corollary 2.8.** Let `E` be a vector space with two norms `‖·‖₁`, `‖·‖₂`, complete for
both, such that `‖x‖₂ ≤ C ‖x‖₁` for some `C ≥ 0` and all `x`. Then the two norms are
equivalent: there is `c > 0` with `‖x‖₁ ≤ c ‖x‖₂` for all `x`. The norms are given as `Norm`
structures `n₁`, `n₂` satisfying the norm axioms (`NormedSpace.Core`), and "Banach for the
norm" refers to the metric each induces. -/
theorem corollary_2_8 {n₁ n₂ : Norm V} (h₁ : @NormedSpace.Core ℝ V _ _ _ n₁)
    (h₂ : @NormedSpace.Core ℝ V _ _ _ n₂)
    (c₁ : @CompleteSpace V (@NormedAddCommGroup.ofCore ℝ V _ _ _ n₁ h₁).toUniformSpace)
    (c₂ : @CompleteSpace V (@NormedAddCommGroup.ofCore ℝ V _ _ _ n₂ h₂).toUniformSpace)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, @norm V n₂ x ≤ C * @norm V n₁ x) :
    ∃ c > 0, ∀ x, @norm V n₁ x ≤ c * @norm V n₂ x := by
  have : CompleteSpace (WithNormCore V h₁) := c₁
  have : CompleteSpace (WithNormCore V h₂) := c₂
  obtain ⟨C, -, hC⟩ := hC
  let T : WithNormCore V h₁ →L[ℝ] WithNormCore V h₂ :=
    LinearMap.mkContinuous (LinearMap.id : WithNormCore V h₁ →ₗ[ℝ] WithNormCore V h₂) C
      fun x => hC x
  obtain ⟨-, c, hc, hT⟩ := corollary_2_7 T ⟨fun x y hxy => hxy, fun y => ⟨y, rfl⟩⟩
  exact ⟨1 / c, by positivity, hT⟩

end TwoNorms

/-! ### The closed graph theorem -/

/-- **Theorem 2.9 (closed graph theorem).** Let `E`, `F` be Banach spaces and `T : E → F` a
linear operator whose graph `G(T)` is closed in `E × F`. Then `T` is continuous. -/
theorem theorem_2_9 [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[ℝ] F)
    (hT : IsClosed (T.graph : Set (E × F))) : Continuous T :=
  T.continuous_of_isClosed_graph hT

/-- **Remark 6.** The converse is obvious: the graph of a continuous (linear) map is closed. -/
theorem remark_2_6 (T : E →ₗ[ℝ] F) (hT : Continuous T) : IsClosed (T.graph : Set (E × F)) := by
  have : (T.graph : Set (E × F)) = {p | p.2 = T p.1} := Set.ext fun p => T.mem_graph_iff p
  rw [this]
  exact isClosed_eq continuous_snd (hT.comp continuous_fst)

end Brezis.Chapter02
