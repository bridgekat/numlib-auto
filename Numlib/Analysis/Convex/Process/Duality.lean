/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Process.Basic
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# The two inner products of a convex process

Let $A$ be a convex process from $U$ to $X$, with $U$ paired with $V$ and $X$ paired with $Y$, and
let $A^*$ be its adjoint. The process carries two inner products,
$$\langle Au, x^* \rangle = \sup \{\langle x, x^* \rangle \mid x \in Au\} \quad\text{and}\quad
  \langle u, A^* x^* \rangle = \inf \{\langle u, u^* \rangle \mid u^* \in A^* x^*\}.$$
The first is a maximization over a value of $A$, the second a minimization over a value of $A^*$.
They are the bracket of the indicator bifunction $F$ of $A$ and the concave bracket of its adjoint
$F^*$, so everything that separates them is a partial closure. The module
`Numlib.Analysis.Convex.Process.Basic` proves the results that need only the closure in $u$. This
module adds the results that need the closure in $x^*$, where closedness of $A$ enters, and the
results that need relative interiors. The presentation follows [rockafellar1970convex], §39.

## Main results

* `ConvexAnalysis.ConvexProcess.closedConvexBifun_indicatorBifun_iff`: $A$ is a closed convex
  process exactly when its indicator bifunction is closed.
* `ConvexAnalysis.ConvexProcess.concaveDomBifun_convexAdjointBifun_indicatorBifun`: the effective
  domain of $F^*$ is $\operatorname{dom} A^*$.
* `ConvexAnalysis.ConvexProcess.partialCl₂_concaveBracket_convexAdjointBifun_indicatorBifun`:
  $\langle Au, x^* \rangle = \operatorname{cl}_{x^*} \langle u, A^* x^* \rangle$ for a closed convex
  process.
* `ConvexAnalysis.ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom`,
  `ConvexAnalysis.ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint`: $\langle Au,
  x^* \rangle = \langle u, A^* x^* \rangle$ whenever
  $u \in \operatorname{ri}(\operatorname{dom} A)$, or $A$ is closed and $x^* \in
  \operatorname{ri}(\operatorname{dom} A^*)$. This is Theorem 39.3 of [rockafellar1970convex]. The
  bifunction statements that they specialize,
  `ConvexAnalysis.bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint` and
  `ConvexAnalysis.bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint_concaveDomBifun`, are
  in `Numlib.Analysis.Convex.Saddle.Kernel`.
* `ConvexAnalysis.exists_unique_convexProcess_bracket_indicatorBifun_eq`: a lower closed
  concave-convex function $K$ with $K(0, 0) = 0$ that is positively homogeneous in each variable
  separately is $\langle Au, x^* \rangle$ for exactly one closed convex process $A$. This is Theorem
  39.4 of [rockafellar1970convex]. `ConvexAnalysis.ConvexProcess.isClosed_eval` and the properties
  of `ConvexAnalysis.bracket` for the indicator bifunction proved before it are the properties that
  this correspondence inverts.
* `ConvexAnalysis.ConvexProcess.closedConvex_imageBifun_indicatorBifun` and the results after it:
  for a closed convex process $A$ and a closed proper convex function $f$, the image $Af$ is closed,
  the infimum that defines $(Af)(x)$ is attained, and $(Af)^* = \operatorname{cl}((A^*)^{-1} f^*)$.
  The statement without closures is
  `ConvexAnalysis.ConvexProcess.convexConj_imageBifun_indicatorBifun` in
  `Numlib.Analysis.Convex.Process.Basic`.

## Implementation notes

* Rockafellar puts "if $A$ is closed" before both halves of the statement $\langle Au, x^* \rangle =
  \langle u, A^* x^* \rangle$ on relative interiors. The half for
  $u \in \operatorname{ri}(\operatorname{dom} A)$ needs only that a concave function agrees with its
  concave closure on the relative interior of its effective domain, so it is stated without
  closedness. Closedness is needed only for $x^*$, where the closure in $x^*$, which rests on
  $F^{**} = \operatorname{cl} F$, identifies $\operatorname{cl}_{x^*} \langle u, A^* x^* \rangle$
  with $\langle Au, x^* \rangle$. In that half $Y$, not $U$, must be finite-dimensional.
* A process is closed exactly when its indicator bifunction is closed, because $\operatorname{cl}
  \delta(\cdot \mid S) = \delta(\cdot \mid \operatorname{cl} S)$. So the theorems about bifunctions
  apply to processes without a separate closedness argument.
* The correspondence with saddle functions is stated as a unique existence with closedness inside
  it. It is a correspondence between closed convex processes and saddle functions, so uniqueness is
  uniqueness among closed processes.
* The pairings are `Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ` and `Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ`. The Lean variables `y` and
  `v` stand for the dual vectors $x^* \in Y$ and $u^* \in V$.
-/

open Set

namespace ConvexAnalysis

/-! ### Closedness, and the effective domain of the adjoint -/

section Closedness

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [TopologicalSpace U]
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

namespace ConvexProcess

/-- Let $U$ and $X$ be topological spaces. A convex process $A$ from $U$ to $X$ has a closed graph
if and only if its indicator bifunction is a closed convex bifunction.

For an indicator bifunction, closedness of the bifunction is the equation
$\operatorname{cl}(\operatorname{graph} A) = \operatorname{graph} A$. -/
theorem closedConvexBifun_indicatorBifun_iff (A : ConvexProcess U X) :
    ClosedConvexBifun A.indicatorBifun ↔ IsClosed (A.graph : Set (U × X)) := by
  have hgr : ClosedConvexBifun A.indicatorBifun
      ↔ convexCl (indicatorFn (A.graph : Set (U × X))) = indicatorFn (A.graph : Set (U × X)) := by
    rw [ClosedConvexBifun, graphFn_indicatorBifun]
    exact Iff.rfl
  rw [hgr, convexCl_indicatorFn, ← closure_eq_iff_isClosed]
  constructor
  · intro h
    refine Subset.antisymm (fun p hp => ?_) subset_closure
    by_contra hc
    have e1 : indicatorFn (closure (A.graph : Set (U × X))) p = 0 := indicatorFn_of_mem hp
    rw [h, indicatorFn_of_notMem hc] at e1
    exact absurd e1 (by simp)
  · intro h
    rw [h]

/-- Let $U$ and $X$ be topological spaces. If the graph of $A$ is closed, then every value $Au$ is a
closed set, because $Au$ is the preimage of the graph under the continuous map
$x \mapsto (u, x)$. -/
theorem isClosed_eval {A : ConvexProcess U X} (hA : IsClosed (A.graph : Set (U × X))) (u : U) :
    IsClosed (A.eval u) :=
  hA.preimage (continuous_const.prodMk continuous_id)

end ConvexProcess

end Closedness

section DomAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The effective domain $\{x^* \mid (F^* x^*)(u^*) \neq -\infty \text{ for some } u^*\}$ of the
concave bifunction $F^*$, the adjoint of the indicator bifunction $F$ of $A$, is the effective
domain of the adjoint process $A^*$.

Equivalently, $\langle u, A^* x^* \rangle = +\infty$ exactly where $A^* x^*$ is empty. -/
@[simp] theorem concaveDomBifun_convexAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    concaveDomBifun (convexAdjointBifun Bu Bx A.indicatorBifun) = (adjointProcess Bu Bx A).dom := by
  ext y
  simp only [mem_concaveDomBifun, mem_dom, Set.Nonempty]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    by_contra hc
    exact hv (by
      simp [convexAdjointBifun_indicatorBifun, indicatorBifun_apply, indicatorFn_of_notMem hc])
  · rintro ⟨v, hv⟩
    exact ⟨v, by
      simp [convexAdjointBifun_indicatorBifun, indicatorBifun_apply, indicatorFn_of_mem hv]⟩

end ConvexProcess

end DomAdjoint

/-! ### The two inner products for a closed convex process -/

section BracketClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

namespace ConvexProcess

/-- **For a closed convex process, $\langle Au, x^* \rangle = \operatorname{cl}_{x^*} \langle u, A^*
x^* \rangle$.** Let $U$, $X$ and $Y$ be locally convex topological vector spaces, such that the
continuous linear functionals on $U$, $X$ and $Y$ are exactly the pairings with $V$, $Y$ and
$X$. Let $A$ be a convex process from $U$ to $X$ with closed graph. Then the convex closure in
the second variable of $(u, x^*) \mapsto \langle u, A^* x^* \rangle$ is
$(u, x^*) \mapsto \langle Au, x^* \rangle$.

This is the closure in $x^*$, and closedness of $A$ enters here: the proof runs through
$F^{**} = \operatorname{cl} F = F$. The closure in $u$, $\langle u, A^* x^* \rangle =
\operatorname{cl}_u \langle Au, x^* \rangle$
(`ConvexAnalysis.ConvexProcess.concaveBracket_convexAdjointBifun_indicatorBifun_eq_partialCl₁`),
holds for every convex process. -/
theorem partialCl₂_concaveBracket_convexAdjointBifun_indicatorBifun (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) :
    partialCl₂ (fun p : U × Y =>
        concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) p.1 p.2)
      = fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  partialCl₂_concaveBracket_adjoint Bu Bx A.convexBifun_indicatorBifun
    ((closedConvexBifun_indicatorBifun_iff A).2 hA)

end ConvexProcess

end BracketClosed

/-! ### Where the two inner products agree -/

section BracketAgree

variable {U V X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- **$\langle Au, x^* \rangle = \langle u, A^* x^* \rangle$ at every relative interior point of
$\operatorname{dom} A$.** Let $U$ be a finite-dimensional real normed space whose continuous
linear functionals are exactly $\langle \cdot, u^* \rangle$ for $u^* \in V$. If
$u \in \operatorname{ri}(\operatorname{dom} A)$, then $\langle Au, x^* \rangle = \langle u, A^*
x^* \rangle$ for every $x^* \in Y$. This is part of Theorem 39.3 of [rockafellar1970convex].

Rockafellar puts "if $A$ is closed" before the assertion. No closedness is needed here: the
statement is `ConvexAnalysis.bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint` for the
indicator bifunction. -/
theorem bracket_eq_concaveBracket_of_mem_relint_dom (A : ConvexProcess U X) {u : U}
    (hu : u ∈ ri A.dom) (y : Y) :
    bracket Bx A.indicatorBifun u y
      = concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) u y :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint Bu Bx A.convexBifun_indicatorBifun
    (by rw [convexDomBifun_indicatorBifun]; exact hu) y

end ConvexProcess

end BracketAgree

section BracketAgreeAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]

namespace ConvexProcess

/-- **For a closed convex process, $\langle Au, x^* \rangle = \langle u, A^* x^* \rangle$ at every
relative interior point of $\operatorname{dom} A^*$, and for every $u$.** Let $Y$ be a
finite-dimensional real normed space, and let $U$ and $X$ be locally convex topological vector
spaces, such that the continuous linear functionals on $U$, $X$ and $Y$ are exactly the pairings
with $V$, $Y$ and $X$. Let $A$ have a closed graph. If $x^* \in
\operatorname{ri}(\operatorname{dom} A^*)$, then $\langle Au, x^* \rangle = \langle u, A^* x^*
\rangle$ for every $u \in U$. This is part of Theorem 39.3 of [rockafellar1970convex].

Unlike the statement for $u \in \operatorname{ri}(\operatorname{dom} A)$, this one needs $A$
closed, because it goes through the closure in $x^*$. -/
theorem bracket_eq_concaveBracket_of_mem_relint_dom_adjoint (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) (u : U)
    {y : Y} (hy : y ∈ ri (adjointProcess Bu Bx A).dom) :
    bracket Bx A.indicatorBifun u y
      = concaveBracket Bu (convexAdjointBifun Bu Bx A.indicatorBifun) u y :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint_concaveDomBifun
    A.convexBifun_indicatorBifun ((closedConvexBifun_indicatorBifun_iff A).2 hA) u
    (by rw [concaveDomBifun_convexAdjointBifun_indicatorBifun]; exact hy)

end ConvexProcess

end BracketAgreeAdjoint

/-!
### Which saddle functions are inner products of processes

The lower closed concave-convex functions on $U \times Y$ correspond to the closed convex
bifunctions from $U$ to $X$. The functions that come from processes are exactly those that satisfy
two further conditions: they vanish at the origin, and they are positively homogeneous in each
variable separately.
-/

section SaddleCorrespondence

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {K : U × Y → EReal}

namespace ConvexProcess

omit [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]
  [LocallyConvexSpace ℝ U] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **The inner product of a convex process is concave-convex**:
$(u, x^*) \mapsto \langle Au, x^* \rangle$ is concave in $u$ and convex in $x^*$. -/
theorem concaveConvexFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConcaveConvexFn fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  concaveConvexFn_bracket A.convexBifun_indicatorBifun Bx

/-- **The inner product of a closed convex process is lower closed.** Let $U$, $X$ and $Y$ be
locally convex topological vector spaces, such that the continuous linear functionals on $U$,
$X$ and $Y$ are exactly the pairings with $V$, $Y$ and $X$. If the graph of $A$ is closed, then
$(u, x^*) \mapsto \langle Au, x^* \rangle$ is lower closed. This is the correspondence between
bifunctions and saddle functions, applied to the indicator bifunction. -/
theorem lowerClosedFn_bracket_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (A : ConvexProcess U X) (hA : IsClosed (A.graph : Set (U × X))) :
    LowerClosedFn fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2 :=
  lowerClosedFn_bracket Bu Bx A.convexBifun_indicatorBifun
    ((closedConvexBifun_indicatorBifun_iff A).2 hA)

omit [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **A closed convex process is recovered from its inner product.** Let $X$ be a locally convex
topological vector space whose continuous linear functionals are exactly
$\langle \cdot, x^* \rangle$ for $x^* \in Y$. If the graph of $A$ is closed, then for every $u$
$$Au = \{x \mid \langle x, x^* \rangle \le \langle Au, x^* \rangle \text{ for all } x^* \in
  Y\}.$$

This is the recovery of a closed convex set from its support function, applied to $Au$, whose
support function is $\langle Au, \cdot \rangle$
(`ConvexAnalysis.ConvexProcess.bracket_indicatorBifun`). -/
theorem eval_eq_supportSet_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bx] (A : ConvexProcess U X)
    (hA : IsClosed (A.graph : Set (U × X))) (u : U) :
    A.eval u = supportSet Bx.flip (bracket Bx A.indicatorBifun u) := by
  rw [bracket_indicatorBifun]
  exact (supportSet_supportFn (A.convex_eval u) (isClosed_eval hA u)).symm

end ConvexProcess

/-- **$K(u, x^*) = \langle Au, x^* \rangle$ is a one-to-one correspondence** between the closed
convex processes from $U$ to $X$ and the lower closed concave-convex functions on $U \times Y$
that vanish at the origin and are positively homogeneous in each variable separately. Precisely:
let $U$, $X$ and $Y$ be locally convex topological vector spaces, such that the continuous
linear functionals on $U$, $X$ and $Y$ are exactly the pairings with $V$, $Y$ and $X$. Let
$K : U \times Y \to [-\infty, +\infty]$ be concave-convex and lower closed, with $K(0, 0) = 0$,
and positively homogeneous in $u$ for each $x^*$ and in $x^*$ for each $u$. Then there is
exactly one convex process $A$ with closed graph such that
$$\langle Au, x^* \rangle = K(u, x^*) \quad \text{for all } u \in U,\ x^* \in Y.$$
This is Theorem 39.4 of [rockafellar1970convex]. The inverse map is $Au = \{x \mid \langle x,
x^* \rangle \le K(u, x^*) \text{ for all } x^*\}$
(`ConvexAnalysis.ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun`).

The correspondence between saddle functions and bifunctions does all the work on the side of
bifunctions. What remains is that the closed convex bifunction $F$ it produces is an indicator
bifunction. The condition $K(0, 0) = 0$ bounds $F0$ below by $0$ and makes it finite somewhere,
so the closed convex graph function of $F$ cannot take the value $-\infty$, and no slice
$K(u, \cdot)$ is identically $+\infty$. The conjugate of a positively homogeneous function that
is not identically $+\infty$ is an indicator function, so each $Fu$ is one. Positive homogeneity
in $u$ makes the resulting set a cone, and its convexity comes from the convexity of $F$. -/
theorem exists_unique_convexProcess_bracket_indicatorBifun_eq
    (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) (hK₀ : K (0, 0) = 0)
    (hhu : ∀ y : Y, PosHomogeneous fun u : U => K (u, y))
    (hhy : ∀ u : U, PosHomogeneous fun y : Y => K (u, y)) :
    ∃! A : ConvexProcess U X, IsClosed (A.graph : Set (U × X)) ∧
      (fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2) = K := by
  obtain ⟨F, ⟨hFconv, hFcl, hFbr⟩, huniq⟩ := exists_unique_convexBifun_bracket_eq Bu Bx hK hlc
  have hbr0 : ∀ (u : U) (y : Y), convexConj Bx (F u) y = K (u, y) := fun u y => congrFun hFbr (u, y)
  -- `K (0, 0) = 0` bounds `F 0` below and makes it finite somewhere.
  have hzero : ∀ x : X, (0 : EReal) ≤ F 0 x := by
    intro x
    have h1 : ((Bx x (0 : Y) : ℝ) : EReal) - F 0 x ≤ K (0, 0) := by
      rw [← hbr0 0 0]
      exact sub_le_convexConj Bx (F 0) x 0
    rw [hK₀, map_zero, EReal.coe_zero] at h1
    have hz : (0 : EReal) - F 0 x = -(F 0 x) := zero_add _
    rw [hz] at h1
    have h3 := EReal.neg_le.1 h1
    rwa [neg_zero] at h3
  have hex0 : ∃ x : X, F 0 x ≠ ⊤ := by
    by_contra hc
    push Not at hc
    have hbot : convexConj Bx (F 0) (0 : Y) = ⊥ := convexConj_eq_bot_iff.2 hc
    rw [hbr0 0 0, hK₀] at hbot
    exact absurd hbot (by simp)
  -- Hence `graphFn F` never takes `-∞`: a closed convex function that does is nowhere finite.
  have hFnb : ∀ (u : U) (x : X), F u x ≠ ⊥ := by
    intro u x hux
    obtain ⟨x₀, hx₀⟩ := hex0
    have hgc : ConvexFn (graphFn F) := hFconv
    have hcl' : ClosedConvex (graphFn F) := hFcl
    have hgbot : graphFn F (u, x) = ⊥ := hux
    rcases hgc.eq_bot_or_eq_top (ClosedConvex.lowerSemicontinuous hcl') ⟨(u, x), hgbot⟩ (0, x₀) with
      h | h
    · have h' : F 0 x₀ = ⊥ := h
      have hle := hzero x₀
      rw [h'] at hle
      exact absurd hle (by simp)
    · exact hx₀ h
  -- `F u` is the conjugate of `K (u, ·)`, because a closed bifunction is image-closed.
  have hFconj : ∀ u : U, F u = convexConj Bx.flip (fun y : Y => K (u, y)) := by
    intro u
    have hcl : convexCl (F u) = F u := ClosedConvexBifun.imageClosedBifun hFcl u
    have h1 : convexCl (F u) = convexConj Bx.flip (bracket Bx F u) :=
        convexCl_eq_convexConj_bracket hFconv u
    have h2 : bracket Bx F u = fun y : Y => K (u, y) := funext fun y => hbr0 u y
    rw [hcl, h2] at h1
    exact h1
  have hKne : ∀ u : U, ∃ y : Y, K (u, y) ≠ ⊤ := by
    intro u
    by_contra hc
    push Not at hc
    have hbot : convexConj Bx.flip (fun y : Y => K (u, y)) (0 : X) = ⊥ := convexConj_eq_bot_iff.2 hc
    rw [← hFconj u] at hbot
    exact hFnb u 0 hbot
  have hK0nb : ∀ y : Y, K (0, y) ≠ ⊥ := by
    intro y
    obtain ⟨x₀, hx₀⟩ := hex0
    rw [← hbr0 0 y]
    exact convexConj_ne_bot ⟨x₀, lt_top_iff_ne_top.2 hx₀⟩ y
  have hK0nn : ∀ y : Y, (0 : EReal) ≤ K (0, y) := by
    intro y
    have htri : K (0, y) = 0 ∨ K (0, y) = ⊤ ∨ K (0, y) = ⊥ :=
      (hhu y).map_zero_trichotomy
    rcases htri with h | h | h
    · exact le_of_eq h.symm
    · rw [h]; exact le_top
    · exact absurd h (hK0nb y)
  -- Each `F u` is an indicator function, `K (u, ·)` being positively homogeneous.
  have hFind : ∀ u : U,
      F u = indicatorFn {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (u, y)} := by
    intro u
    have hset : supportSet Bx.flip (fun y : Y => K (u, y))
        = {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (u, y)} := rfl
    rw [hFconj u, convexConj_eq_indicatorFn_of_posHomogeneous (B := Bx.flip) (hhy u) (hKne u), hset]
  -- The graph of the process to come.
  obtain ⟨G, hG⟩ : ∃ S : Set (U × X),
      S = {p : U × X | ∀ y : Y, ((Bx p.2 y : ℝ) : EReal) ≤ K (p.1, y)} := ⟨_, rfl⟩
  have hmem : ∀ p : U × X, p ∈ G ↔ ∀ y : Y, ((Bx p.2 y : ℝ) : EReal) ≤ K (p.1, y) := by
    rw [hG]; exact fun _ => Iff.rfl
  have hgraphFn : graphFn F = indicatorFn G := by
    funext p
    rw [graphFn_apply, hFind p.1]
    by_cases hp : p ∈ G
    · have h1 : p.2 ∈ {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (p.1, y)} := (hmem p).1 hp
      rw [indicatorFn_of_mem h1, indicatorFn_of_mem hp]
    · have h1 : p.2 ∉ {x : X | ∀ y : Y, ((Bx x y : ℝ) : EReal) ≤ K (p.1, y)} :=
        fun hc => hp ((hmem p).2 hc)
      rw [indicatorFn_of_notMem h1, indicatorFn_of_notMem hp]
  have hGconv : Convex ℝ G := by
    refine convexFn_indicatorFn.1 ?_
    rw [← hgraphFn]
    exact hFconv
  have hG0 : (0 : U × X) ∈ G := by
    refine (hmem 0).2 fun y => ?_
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, LinearMap.zero_apply,
      EReal.coe_zero]
    exact hK0nn y
  have hGsmul : ∀ c : ℝ, 0 ≤ c → ∀ p ∈ G, c • p ∈ G := by
    intro c hc p hp
    rcases eq_or_lt_of_le hc with rfl | hcpos
    · rw [zero_smul]
      exact hG0
    · refine (hmem _).2 fun y => ?_
      have hK' : K ((c • p).1, y) = (c : EReal) * K (p.1, y) := hhu y c hcpos p.1
      have hB : ((Bx (c • p).2 y : ℝ) : EReal) = (c : EReal) * ((Bx p.2 y : ℝ) : EReal) := by
        simp only [Prod.smul_snd, map_smul, smul_eq_mul, LinearMap.smul_apply]
        rw [EReal.coe_mul]
      rw [hK', hB]
      exact mul_le_mul_of_nonneg_left ((hmem p).1 hp y) (by exact_mod_cast hcpos.le)
  have hGadd : ∀ p ∈ G, ∀ q ∈ G, p + q ∈ G := by
    intro p hp q hq
    have hmid : (2 : ℝ)⁻¹ • p + (2 : ℝ)⁻¹ • q ∈ G :=
      hGconv hp hq (by norm_num) (by norm_num) (by norm_num)
    have h2 := hGsmul 2 (by norm_num) _ hmid
    have hval : (2 : ℝ) • ((2 : ℝ)⁻¹ • p + (2 : ℝ)⁻¹ • q) = p + q := by
      rw [smul_add, smul_smul, smul_smul]
      norm_num
    rwa [hval] at h2
  obtain ⟨A, hAgraph⟩ : ∃ A : ConvexProcess U X, (A.graph : Set (U × X)) = G :=
    ⟨⟨{ carrier := G
        zero_mem' := hG0
        add_mem' := fun {p q} hp hq => hGadd p hp q hq
        smul_mem' := fun c p hp => hGsmul (c : ℝ) c.2 p hp }⟩, rfl⟩
  have hAind : A.indicatorBifun = F := by
    funext u x
    have heval : A.eval u = {z : X | ∀ y : Y, ((Bx z y : ℝ) : EReal) ≤ K (u, y)} := by
      ext z
      rw [ConvexProcess.mem_eval, ← SetLike.mem_coe, hAgraph]
      exact hmem (u, z)
    rw [ConvexProcess.indicatorBifun_apply, heval, hFind u]
  refine ⟨A, ⟨?_, ?_⟩, ?_⟩
  · exact (ConvexProcess.closedConvexBifun_indicatorBifun_iff A).1 (by rw [hAind]; exact hFcl)
  · rw [hAind]; exact hFbr
  · rintro A' ⟨hA'cl, hA'br⟩
    refine ConvexProcess.indicatorBifun_injective ?_
    rw [hAind]
    exact huniq A'.indicatorBifun
      ⟨A'.convexBifun_indicatorBifun, (ConvexProcess.closedConvexBifun_indicatorBifun_iff
          A').2 hA'cl,
        hA'br⟩

end SaddleCorrespondence

/-! ### The image under a closed convex process -/

section ImageClosed

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}
  [IsCompatiblePairing Bx] {A : ConvexProcess U X} {f : U → EReal}

namespace ConvexProcess

/-- **For a closed convex process $A$ and a closed proper convex function $f$, the image $Af$ is
closed.** Let $U$ and $X$ be locally convex topological vector spaces whose continuous linear
functionals are exactly the pairings with $V$ and $Y$. Let $A$ have a closed graph, and let
$f : U \to [-\infty, +\infty]$ be closed, proper and convex. Suppose that for every $x \in X$
the conjugate $f^*$ and the function $u^* \mapsto -\sup \{\langle x, x^* \rangle \mid x^* \in
(A^*)^{-1} u^*\}$ add exactly (`ConvexAnalysis.IsExactSum`). Then the function
$(Af)(x) = \inf \{f(u) \mid x \in Au\}$ is a closed convex function.

This is `ConvexAnalysis.closedConvex_imageBifun` for the indicator bifunction of $A$. The
closedness hypothesis passes through
`ConvexAnalysis.ConvexProcess.closedConvexBifun_indicatorBifun_iff`, and the condition "finite
somewhere" is $0 \in A0$. Rockafellar's hypothesis $\operatorname{ri}(\operatorname{dom} f^*)
\cap \operatorname{ri}(\operatorname{dom} (A^*)^{-1}) \neq \emptyset$ is replaced by the
exactness hypothesis, one instance for each $x$. Here $\operatorname{dom} (A^*)^{-1}$ is the
range of $A^*$. -/
theorem closedConvex_imageBifun_indicatorBifun (hA : IsClosed (A.graph : Set (U × X)))
    (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (adjointProcess Bu Bx A).inv.indicatorBifun v x))) :
    ClosedConvex (imageBifun A.indicatorBifun f) := by
  refine closedConvex_imageBifun (Bu := Bu) (Bx := Bx) A.convexBifun_indicatorBifun
    ((closedConvexBifun_indicatorBifun_iff A).2 hA) A.indicatorBifun_zero_zero_ne_top hf ?_
  simpa only [lowerAdjointBifun_indicatorBifun] using hex

/-- **The infimum that defines $(Af)(x)$ is attained.** Under the hypotheses of
`ConvexAnalysis.ConvexProcess.closedConvex_imageBifun_indicatorBifun` at the point $x$, there is
a $u \in U$ with
$$f(u) + \delta(x \mid Au) = (Af)(x).$$
-/
theorem exists_imageBifun_indicatorBifun_eq (hA : IsClosed (A.graph : Set (U × X)))
    (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (adjointProcess Bu Bx A).inv.indicatorBifun v x))) :
    ∃ u : U, f u + A.indicatorBifun u x = imageBifun A.indicatorBifun f x := by
  refine exists_imageBifun_eq (Bu := Bu) (Bx := Bx) A.convexBifun_indicatorBifun
    ((closedConvexBifun_indicatorBifun_iff A).2 hA) A.indicatorBifun_zero_zero_ne_top hf ?_
  simpa only [lowerAdjointBifun_indicatorBifun] using hex

/-- **Wherever $Af$ is finite, the infimum $\inf \{f(u) \mid x \in Au\}$ is attained** at a point
$u$ with $x \in Au$. Under the hypotheses of
`ConvexAnalysis.ConvexProcess.closedConvex_imageBifun_indicatorBifun` at the point $x$, and if
$(Af)(x) \neq +\infty$, there is a $u$ with $x \in Au$ and $f(u) = (Af)(x)$.

`ConvexAnalysis.ConvexProcess.exists_imageBifun_indicatorBifun_eq` gives a $u$ with
$f(u) + \delta(x \mid Au) = (Af)(x)$. The indicator is $0$ or $+\infty$. The value $+\infty$ is
excluded, because $f(u) \neq -\infty$ would then force $(Af)(x) = +\infty$. -/
theorem exists_mem_eval_and_eq_imageBifun (hA : IsClosed (A.graph : Set (U × X)))
    (hf : ClosedProperConvexFn f) {x : X}
    (hex : IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (adjointProcess Bu Bx A).inv.indicatorBifun v x)))
    (hne : imageBifun A.indicatorBifun f x ≠ ⊤) :
    ∃ u : U, x ∈ A.eval u ∧ f u = imageBifun A.indicatorBifun f x := by
  obtain ⟨u, hu⟩ := exists_imageBifun_indicatorBifun_eq (Bu := Bu) (Bx := Bx) hA hf hex
  have hmem : x ∈ A.eval u := by
    by_contra hc
    rw [indicatorBifun_apply, indicatorFn_of_notMem hc,
      EReal.add_top_of_ne_bot (hf.proper.ne_bot u)] at hu
    exact hne hu.symm
  refine ⟨u, hmem, ?_⟩
  rwa [indicatorBifun_apply, indicatorFn_of_mem hmem, add_zero] at hu

variable [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] [IsCompatiblePairing Bx.flip]

/-- $(Af)^* = \operatorname{cl}((A^*)^{-1} f^*)$ for a closed convex process and a closed proper
convex function. Under the hypotheses of
`ConvexAnalysis.ConvexProcess.closedConvex_imageBifun_indicatorBifun`, and if in addition $Y$ is
a locally convex topological vector space whose continuous linear functionals are exactly
$\langle x, \cdot \rangle$ for $x \in X$, the conjugate of $Af$ is the closure of the convex
function $x^* \mapsto \inf \{f^*(u^*) \mid u^* \in A^* x^*\}$. -/
theorem convexConj_imageBifun_indicatorBifun_eq_convexCl (hA : IsClosed (A.graph : Set (U × X)))
    (hf : ClosedProperConvexFn f)
    (hex : ∀ x : X, IsExactSum Bu.flip (convexConj Bu f)
      (fun v => -(bracket Bx.flip (adjointProcess Bu Bx A).inv.indicatorBifun v x))) :
    convexConj Bx (imageBifun A.indicatorBifun f)
      = convexCl (imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (convexConj Bu f)) := by
  rw [← lowerAdjointBifun_indicatorBifun (Bu := Bu) (Bx := Bx)]
  refine convexConj_imageBifun_eq_convexCl A.convexBifun_indicatorBifun
    ((closedConvexBifun_indicatorBifun_iff A).2 hA) A.indicatorBifun_zero_zero_ne_top hf ?_
  simpa only [lowerAdjointBifun_indicatorBifun] using hex

end ConvexProcess

end ImageClosed


end ConvexAnalysis
