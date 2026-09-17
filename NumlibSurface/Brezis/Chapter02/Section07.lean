import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange
import NumlibSurface.Brezis.Chapter02.Section06

/-!
# Brezis §2.7: operators with closed range, and surjective operators

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.7: the closed range theorem and the two
characterizations of surjective operators, for a densely defined closed operator
`A : D(A) ⊆ E → F` between real Banach spaces and its adjoint `A.strongDualAdjoint`. Everything
is the backbone `Numlib/Analysis/Normed/Operator/Unbounded/ClosedRange` (Theorems 2.19–2.21,
Remark 20) and `Unbounded/Basic` (Remark 18 = Exercise 2.14), restated over `ℝ`; the book derives
Theorem 2.19 from Theorem 2.16 by the product-space device and Theorems 2.20–2.21 from 2.19, the
backbone proves them directly.

## Main results

* `theorem_2_19` — the closed range theorem: `R(A)` closed ⟺ `R(A*)` closed ⟺ `R(A) = N(A*)^⊥`
  ⟺ `R(A*) = N(A)^⊥`.
* `remark_2_18` — `R(A)` is closed iff `dist (u, N(A)) ≤ C ‖A u‖` on `D(A)`.
* `theorem_2_20` — `A` onto ⟺ `‖v‖ ≤ C ‖A* v‖` on `D(A*)` ⟺ `N(A*) = 0` and `R(A*)` closed
  (Remark 19, the method of a priori estimates, is the direction (b) ⇒ (a)).
* `theorem_2_21` — `A*` onto ⟺ `‖u‖ ≤ C ‖A u‖` on `D(A)` ⟺ `N(A) = 0` and `R(A)` closed.
* `remark_2_20`, `remark_2_20_implications`, `remark_2_20_diag` — the finite-dimensional
  equivalences, the general implications, and the `ℓ²` example (`diagOperator` of §2.6) showing
  that their converses fail.
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Theorem 2.19 (the closed range theorem).** For a densely defined closed `A`, the following
are equivalent: (i) `R(A)` is closed; (ii) `R(A*)` is closed; (iii) `R(A) = N(A*)^⊥`;
(iv) `R(A*) = N(A)^⊥`. -/
theorem theorem_2_19 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    [IsClosed (LinearMap.range A.toFun : Set F),
      IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E)),
      LinearMap.range A.toFun = A.strongDualAdjoint.ker.strongDualCoannihilator,
      LinearMap.range A.strongDualAdjoint.toFun = A.ker.strongDualAnnihilator].TFAE :=
  hc.isClosed_range_tfae hd

/-- **Remark 18.** For a closed `A`, `R(A)` is closed iff `dist (u, N(A)) ≤ C ‖A u‖` for all
`u ∈ D(A)` and some constant `C` (Exercise 2.14). -/
theorem remark_2_18 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) :
    IsClosed (LinearMap.range A.toFun : Set F) ↔
      ∃ C : ℝ, ∀ u : A.domain, infDist (u : E) (A.ker : Set E) ≤ C * ‖A u‖ :=
  hc.isClosed_range_iff_exists_infDist_ker_le

/-- **Theorem 2.20.** For a densely defined closed `A`, the following are equivalent:
(a) `A` is surjective; (b) `‖v‖ ≤ C ‖A* v‖` for all `v ∈ D(A*)` and some constant `C`;
(c) `N(A*) = {0}` and `R(A*)` is closed. Remark 19, the method of a priori estimates, is the
direction (b) ⇒ (a). -/
theorem theorem_2_20 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.toFun = ⊤ ↔ ∃ C : ℝ, ∀ v : A.strongDualAdjoint.domain,
      ‖(v : StrongDual ℝ F)‖ ≤ C * ‖A.strongDualAdjoint v‖) ∧
    (LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥ ∧
      IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E))) :=
  ⟨hc.range_eq_top_iff_exists_norm_le_norm_strongDualAdjoint hd,
    hc.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_and_isClosed_range_strongDualAdjoint hd⟩

/-- **Theorem 2.21 (the dual statement).** For a densely defined closed `A`, the following are
equivalent: (a) `A*` is surjective; (b) `‖u‖ ≤ C ‖A u‖` for all `u ∈ D(A)` and some constant
`C`; (c) `N(A) = {0}` and `R(A)` is closed. -/
theorem theorem_2_21 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      ∃ C : ℝ, ∀ u : A.domain, ‖(u : E)‖ ≤ C * ‖A u‖) ∧
    (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      A.ker = ⊥ ∧ IsClosed (LinearMap.range A.toFun : Set F)) :=
  ⟨hc.range_strongDualAdjoint_eq_top_iff_exists_norm_le_norm hd,
    hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_and_isClosed_range hd⟩

/-- **Remark 20, the finite-dimensional case.** If `dim E < ∞` or `dim F < ∞`, then `A` is
surjective iff `A*` is injective, and `A*` is surjective iff `A` is injective, because `R(A)` and
`R(A*)` are then finite-dimensional, hence closed. -/
theorem remark_2_20 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : FiniteDimensional ℝ E ∨ FiniteDimensional ℝ F) :
    (LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥) ∧
      (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔ A.ker = ⊥) :=
  ⟨hc.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_of_finiteDimensional hd h,
    hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_of_finiteDimensional hd h⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Remark 20, the general case.** `A` surjective implies `A*` injective, and `A*` surjective
implies `A` injective. -/
theorem remark_2_20_implications {A : E →ₗ.[ℝ] F} (hc : A.IsClosed)
    (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.toFun = ⊤ → A.strongDualAdjoint.ker = ⊥) ∧
      (LinearMap.range A.strongDualAdjoint.toFun = ⊤ → A.ker = ⊥) :=
  ⟨LinearPMap.ker_strongDualAdjoint_eq_bot_of_range_eq_top hd,
    hc.ker_eq_bot_of_range_strongDualAdjoint_eq_top hd⟩

/-- **Remark 20, the example.** The converses fail: on `ℓ²` the bounded operator
`A x = (xₙ / n)` is self-adjoint (`A* = A`, in the Hilbert-space sense), injective, not
surjective, and its range is dense but not closed. So `A*` injective does not give `A`
surjective, and `A` injective does not give `A*` surjective. -/
theorem remark_2_20_diag :
    IsSelfAdjoint diagOperator ∧ Function.Injective diagOperator ∧
      ¬ Function.Surjective diagOperator ∧ Dense (Set.range diagOperator) ∧
      ¬ IsClosed (Set.range diagOperator) := by
  refine ⟨?_, diagOperator_injective, not_surjective_diagOperator, dense_range_diagOperator,
    remark_2_12_range_not_closed.1⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, lp.inner_eq_tsum, diagOperator_apply]
  refine tsum_congr fun n => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end Brezis.Chapter02
