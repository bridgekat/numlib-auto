/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange
import NumlibSurface.Brezis.Chapter02.Section06

/-!
# Brezis, Section 2.7: Operators with closed range, and surjective operators

This module formalizes Section 2.7 of [brezis2011functional] for a densely defined closed unbounded
operator $A : D(A) \subseteq E \to F$ between real Banach spaces and its adjoint $A^\star$. The
closed range theorem (Theorem 2.19) states that $R(A)$ is closed if and only if $R(A^\star)$ is
closed, if and only if $R(A) = N(A^\star)^\perp$, if and only if $R(A^\star) = N(A)^\perp$. The
operator $A$ is surjective if and only if $\|v\| \le C\|A^\star v\|$ on $D(A^\star)$, if and only if
$N(A^\star) = \{0\}$ and $R(A^\star)$ is closed (Theorem 2.20). Dually, $A^\star$ is surjective if
and only if $\|u\| \le C\|Au\|$ on $D(A)$, if and only if $N(A) = \{0\}$ and $R(A)$ is closed
(Theorem 2.21). In finite dimension, $A$ is surjective if and only if $A^\star$ is injective (Remark
20); an example on $\ell^2$ shows that this fails in general.

The results specialize the backbone modules `Numlib.Analysis.Normed.Operator.Unbounded.ClosedRange`
(Theorems 2.19 to 2.21 and Remark 20) and `Numlib.Analysis.Normed.Operator.Unbounded.Basic` (Remark
18).

## Main results

* Theorem 2.19, `Brezis.Chapter02.theorem_2_19`: the four conditions of the closed range theorem are
  equivalent.
* Remark 18, `Brezis.Chapter02.remark_2_18`: $R(A)$ is closed if and only if
  $\operatorname{dist}(u, N(A)) \le C\|Au\|$ for all $u \in D(A)$.
* Theorem 2.20, `Brezis.Chapter02.theorem_2_20`: $A$ is surjective if and only if
  $\|v\| \le C\|A^\star v\|$ on $D(A^\star)$, if and only if $N(A^\star) = \{0\}$ and $R(A^\star)$
  is closed.
* Theorem 2.21, `Brezis.Chapter02.theorem_2_21`: $A^\star$ is surjective if and only if
  $\|u\| \le C\|Au\|$ on $D(A)$, if and only if $N(A) = \{0\}$ and $R(A)$ is closed.
* Remark 20, `Brezis.Chapter02.remark_2_20`: if $\dim E < \infty$ or $\dim F < \infty$, then $A$ is
  surjective if and only if $A^\star$ is injective, and $A^\star$ is surjective if and only if $A$
  is injective.
* Remark 20, `Brezis.Chapter02.remark_2_20_implications`: in general, $A$ surjective implies
  $A^\star$ injective, and $A^\star$ surjective implies $A$ injective.
* Remark 20, `Brezis.Chapter02.remark_2_20_diag`: the operator $x \mapsto (x_n/n)$ on $\ell^2$ is
  self-adjoint and injective but not surjective.

## Conventions

* The adjoint $A^\star$ is the backbone `LinearPMap.strongDualAdjoint` of Section 2.6.

## Implementation notes

* The source derives Theorem 2.19 from Theorem 2.16 by the product space device, and Theorems 2.20
  and 2.21 from Theorem 2.19. The backbone proves them directly.
* Remark 19, the method of a priori estimates, is the direction (b) $\Rightarrow$ (a) of Theorem
  2.20.
-/

open Metric

namespace Brezis.Chapter02

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Theorem 2.19** of [brezis2011functional] (closed range theorem). Let $E$ and $F$ be Banach
spaces and let $A : D(A) \subseteq E \to F$ be a densely defined closed unbounded linear
operator. The following properties are equivalent: (i) $R(A)$ is closed; (ii) $R(A^\star)$ is
closed; (iii) $R(A) = N(A^\star)^\perp$; (iv) $R(A^\star) = N(A)^\perp$.

The equivalence is stated with `List.TFAE`. -/
theorem theorem_2_19 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    [IsClosed (LinearMap.range A.toFun : Set F),
      IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E)),
      LinearMap.range A.toFun = A.strongDualAdjoint.ker.strongDualCoannihilator,
      LinearMap.range A.strongDualAdjoint.toFun = A.ker.strongDualAnnihilator].TFAE :=
  hc.isClosed_range_tfae hd

/-- **Remark 18** of [brezis2011functional]. Let $E$ and $F$ be Banach spaces and let
$A : D(A) \subseteq E \to F$ be a closed unbounded linear operator. Then $R(A)$ is closed if and
only if there is a constant $C$ such that
$$\operatorname{dist}(u, N(A)) \le C\|Au\| \quad \text{for all } u \in D(A).$$
This is Exercise 2.14 of the source.

The distance is Mathlib's `Metric.infDist`. -/
theorem remark_2_18 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) :
    IsClosed (LinearMap.range A.toFun : Set F) ↔
      ∃ C : ℝ, ∀ u : A.domain, infDist (u : E) (A.ker : Set E) ≤ C * ‖A u‖ :=
  hc.isClosed_range_iff_exists_infDist_ker_le

/-- **Theorem 2.20** of [brezis2011functional]. Let $E$ and $F$ be Banach spaces and let
$A : D(A) \subseteq E \to F$ be a densely defined closed unbounded linear operator. The
following properties are equivalent: (a) $A$ is surjective, that is, $R(A) = F$; (b) there is a
constant $C$ such that
$$\|v\| \le C\|A^\star v\| \quad \text{for all } v \in D(A^\star);$$
(c) $N(A^\star) = \{0\}$ and $R(A^\star)$ is closed.

The statement is the two equivalences (a) $\iff$ (b) and (a) $\iff$ (c). Remark 19 of the
source, the method of a priori estimates, is the direction (b) $\Rightarrow$ (a). -/
theorem theorem_2_20 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.toFun = ⊤ ↔ ∃ C : ℝ, ∀ v : A.strongDualAdjoint.domain,
      ‖(v : StrongDual ℝ F)‖ ≤ C * ‖A.strongDualAdjoint v‖) ∧
    (LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥ ∧
      IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual ℝ E))) :=
  ⟨hc.range_eq_top_iff_exists_norm_le_norm_strongDualAdjoint hd,
    hc.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_and_isClosed_range_strongDualAdjoint hd⟩

/-- **Theorem 2.21** of [brezis2011functional]. Let $E$ and $F$ be Banach spaces and let
$A : D(A) \subseteq E \to F$ be a densely defined closed unbounded linear operator. The
following properties are equivalent: (a) $A^\star$ is surjective, that is,
$R(A^\star) = E^\star$; (b) there is a constant $C$ such that
$$\|u\| \le C\|Au\| \quad \text{for all } u \in D(A);$$
(c) $N(A) = \{0\}$ and $R(A)$ is closed.

The statement is the two equivalences (a) $\iff$ (b) and (a) $\iff$ (c). -/
theorem theorem_2_21 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      ∃ C : ℝ, ∀ u : A.domain, ‖(u : E)‖ ≤ C * ‖A u‖) ∧
    (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      A.ker = ⊥ ∧ IsClosed (LinearMap.range A.toFun : Set F)) :=
  ⟨hc.range_strongDualAdjoint_eq_top_iff_exists_norm_le_norm hd,
    hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_and_isClosed_range hd⟩

/-- **Remark 20** of [brezis2011functional], the finite-dimensional case. Let $E$ and $F$ be Banach
spaces with $\dim E < \infty$ or $\dim F < \infty$, and let $A : D(A) \subseteq E \to F$ be a
densely defined closed unbounded linear operator. Then $A$ is surjective if and only if
$A^\star$ is injective, and $A^\star$ is surjective if and only if $A$ is injective.

The proof uses that $R(A)$ and $R(A^\star)$ are then finite-dimensional, hence closed. -/
theorem remark_2_20 {A : E →ₗ.[ℝ] F} (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : FiniteDimensional ℝ E ∨ FiniteDimensional ℝ F) :
    (LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥) ∧
      (LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔ A.ker = ⊥) :=
  ⟨hc.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_of_finiteDimensional hd h,
    hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_of_finiteDimensional hd h⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Remark 20** of [brezis2011functional], the general case. Let $E$ and $F$ be real normed spaces
and let $A : D(A) \subseteq E \to F$ be a densely defined closed unbounded linear operator. If
$A$ is surjective, then $A^\star$ is injective. If $A^\star$ is surjective, then $A$ is
injective. -/
theorem remark_2_20_implications {A : E →ₗ.[ℝ] F} (hc : A.IsClosed)
    (hd : Dense (A.domain : Set E)) :
    (LinearMap.range A.toFun = ⊤ → A.strongDualAdjoint.ker = ⊥) ∧
      (LinearMap.range A.strongDualAdjoint.toFun = ⊤ → A.ker = ⊥) :=
  ⟨LinearPMap.ker_strongDualAdjoint_eq_bot_of_range_eq_top hd,
    hc.ker_eq_bot_of_range_strongDualAdjoint_eq_top hd⟩

/-- **Remark 20** of [brezis2011functional], the example. The converses of
`Brezis.Chapter02.remark_2_20_implications` fail. On $\ell^2$ the bounded operator
$Ax = (x_n/n)_{n \ge 1}$ is self-adjoint, injective and not surjective, and its range is dense
but not closed. Since $A^\star = A$, the injectivity of $A^\star$ does not give the surjectivity
of $A$, and the injectivity of $A$ does not give the surjectivity of $A^\star$.

The operator is `Brezis.Chapter02.diagOperator`, indexed from $0$ as
$x \mapsto (x_n/(n+1))_{n \ge 0}$. Self-adjointness is in the Hilbert space sense of Mathlib's
`IsSelfAdjoint`, for the inner product of $\ell^2$. -/
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
