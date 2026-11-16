/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Correspondence

/-!
# Equivalence classes of saddle-functions

Let $K$ and $L$ be functions on $U \times X$ with values in $[-\infty, +\infty]$. They are
**equivalent** if $\operatorname{cl}_1 K = \operatorname{cl}_1 L$ and
$\operatorname{cl}_2 K = \operatorname{cl}_2 L$, where $\operatorname{cl}_1$ and
$\operatorname{cl}_2$ are the partial closures of `Numlib.Analysis.Convex.Saddle.Defs`. A
saddle-function $K$ is **closed** if $\operatorname{cl}_1 K$ and $\operatorname{cl}_2 K$ are both
equivalent to $K$. This is weaker than lower or upper closedness: a whole order interval can consist
of closed saddle-functions while only its two ends are lower closed and upper closed. The
presentation follows [rockafellar1970convex], §34.

The equivalence classes of closed saddle-functions are exactly the order intervals $$\Omega(F) = \{K
\mid \langle Fu, y \rangle \le K(u, y) \le \langle u, F^* y \rangle\}$$ between the two brackets of
a closed convex bifunction $F$. On such an interval both partial closures are constant and equal to
the two ends, and the class determines $F$. The interval lemmas are stated for a pair
$(\underline{K}, \overline{K})$ with $\operatorname{cl}_1 \underline{K} = \overline{K}$ and
$\operatorname{cl}_2 \overline{K} = \underline{K}$ instead of a bifunction, so they need no pairing.
These pairs are exactly the pairs of brackets of closed convex bifunctions.

## Main definitions

* `ConvexAnalysis.SaddleEquiv`: $K$ and $L$ are equivalent, that is,
  $\operatorname{cl}_1 K = \operatorname{cl}_1 L$ and
  $\operatorname{cl}_2 K = \operatorname{cl}_2 L$.
* `ConvexAnalysis.ClosedSaddleFn`: $K$ is closed, that is, $\operatorname{cl}_1 \operatorname{cl}_2
  K = \operatorname{cl}_1 K$ and $\operatorname{cl}_2 \operatorname{cl}_1 K = \operatorname{cl}_2
  K$.
* `ConvexAnalysis.saddleClass`: the order interval $\{K \mid \underline{K} \le K \le
  \overline{K}\}$, a set of functions.

## Main results

* `ConvexAnalysis.partialCl₂_eq_of_mem_saddleClass`,
  `ConvexAnalysis.partialCl₁_eq_of_mem_saddleClass`,
  `ConvexAnalysis.closedSaddleFn_of_mem_saddleClass`: on the interval of a pair
  $(\underline{K}, \overline{K})$ as above, $\operatorname{cl}_2$ is constant at $\underline{K}$,
  $\operatorname{cl}_1$ is constant at $\overline{K}$, and every member is closed.
* `ConvexAnalysis.exists_unique_bifun_of_closedSaddleFn`: conversely, a closed concave-convex
  function $K$ determines a unique closed convex bifunction whose two brackets are
  $\operatorname{cl}_2 K$ and $\operatorname{cl}_1 K$. These results are parts of Theorem 34.2 of
  [rockafellar1970convex].

## Implementation notes

* `ConvexAnalysis.saddleClass` is the plain order interval between two functions. It does not
  require its members to be concave-convex.
* Equivalence uses the single closures $\operatorname{cl}_1$ and $\operatorname{cl}_2$, not the
  composed closures $\operatorname{cl}_1 \operatorname{cl}_2$ and
  $\operatorname{cl}_2 \operatorname{cl}_1$.
-/

namespace ConvexAnalysis

/-! ### Equivalence, closedness, and the order interval -/

section Defs

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K L M : U × X → EReal}

/-- Two functions $K, L : U \times X \to [-\infty, +\infty]$ are **equivalent** if
$$\operatorname{cl}_1 K = \operatorname{cl}_1 L \quad \text{and} \quad \operatorname{cl}_2 K =
\operatorname{cl}_2 L.$$

The definition uses the single closures, not the composed ones. -/
def SaddleEquiv (K L : U × X → EReal) : Prop :=
  partialCl₁ K = partialCl₁ L ∧ partialCl₂ K = partialCl₂ L

/-- Every function is equivalent to itself. -/
theorem saddleEquiv_refl (K : U × X → EReal) : SaddleEquiv K K := ⟨rfl, rfl⟩

/-- If $K$ is equivalent to $L$, then $L$ is equivalent to $K$. -/
theorem SaddleEquiv.symm (h : SaddleEquiv K L) : SaddleEquiv L K := ⟨h.1.symm, h.2.symm⟩

/-- If $K$ is equivalent to $L$ and $L$ is equivalent to $M$, then $K$ is equivalent to $M$. -/
theorem SaddleEquiv.trans (h : SaddleEquiv K L) (h' : SaddleEquiv L M) : SaddleEquiv K M :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- A saddle-function $K$ is **closed** if $\operatorname{cl}_1 K$ and $\operatorname{cl}_2 K$ are
both equivalent to $K$. Because the partial closures are idempotent, this is the pair of
equations $$\operatorname{cl}_1 \operatorname{cl}_2 K = \operatorname{cl}_1 K \quad \text{and}
\quad \operatorname{cl}_2 \operatorname{cl}_1 K = \operatorname{cl}_2 K,$$ and the definition
states these two equations. -/
def ClosedSaddleFn (K : U × X → EReal) : Prop :=
  partialCl₁ (partialCl₂ K) = partialCl₁ K ∧ partialCl₂ (partialCl₁ K) = partialCl₂ K

/-- The **order interval** $\Omega$ between two functions $\underline{K}$ and $\overline{K}$ on
$U \times X$ is the set of functions $K$ with $\underline{K} \le K \le \overline{K}$.

It is used for a pair with $\operatorname{cl}_1 \underline{K} = \overline{K}$ and
$\operatorname{cl}_2 \overline{K} = \underline{K}$. Its members need not be concave-convex. -/
def saddleClass (Klow Kup : U × X → EReal) : Set (U × X → EReal) := {K | Klow ≤ K ∧ K ≤ Kup}

omit [TopologicalSpace U] [TopologicalSpace X] in
/-- $K$ lies in the interval between $\underline{K}$ and $\overline{K}$ if and only if
$\underline{K} \le K \le \overline{K}$. -/
theorem mem_saddleClass {Klow Kup : U × X → EReal} :
    K ∈ saddleClass Klow Kup ↔ Klow ≤ K ∧ K ≤ Kup := Iff.rfl

/-- Every function $K$ lies in the interval between $\operatorname{cl}_2 K$ and
$\operatorname{cl}_1 K$. -/
theorem mem_saddleClass_self (K : U × X → EReal) :
    K ∈ saddleClass (partialCl₂ K) (partialCl₁ K) := ⟨partialCl₂_le K, le_partialCl₁ K⟩

end Defs

section ClosedEquiv

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- If $K$ is a closed saddle-function, then $\operatorname{cl}_2 K$ is equivalent to $K$. -/
theorem ClosedSaddleFn.saddleEquiv_partialCl₂ (h : ClosedSaddleFn K) :
    SaddleEquiv (partialCl₂ K) K :=
  ⟨h.1, partialClosed₂_partialCl₂ K⟩

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- If $K$ is a closed saddle-function, then $\operatorname{cl}_1 K$ is equivalent to $K$. -/
theorem ClosedSaddleFn.saddleEquiv_partialCl₁ (h : ClosedSaddleFn K) :
    SaddleEquiv (partialCl₁ K) K :=
  ⟨partialClosed₁_partialCl₁ K, h.2⟩

end ClosedEquiv

/-! ### The closures are constant on the interval -/

section IntervalCl₂

variable {U X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
  {Klow Kup K : U × X → EReal}

/-- Let $X$ be a commutative topological group. If $\operatorname{cl}_2 \overline{K} =
\underline{K}$ and $\underline{K} \le K \le \overline{K}$, then
$\operatorname{cl}_2 K = \underline{K}$.

By monotonicity, $\operatorname{cl}_2 K$ lies between $\operatorname{cl}_2 \underline{K} =
\underline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$. -/
theorem partialCl₂_eq_of_mem_saddleClass (h2 : partialCl₂ Kup = Klow)
    (hK : K ∈ saddleClass Klow Kup) : partialCl₂ K = Klow := by
  have hcc : partialCl₂ Klow = Klow := by
    rw [← h2]
    exact partialClosed₂_partialCl₂ Kup
  exact le_antisymm ((partialCl₂_mono hK.2).trans h2.le)
    (hcc.symm.trans_le (partialCl₂_mono hK.1))

end IntervalCl₂

section IntervalCl₁

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  {Klow Kup K : U × X → EReal}

/-- Let $U$ be a commutative topological group. If $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\underline{K} \le K \le \overline{K}$, then
$\operatorname{cl}_1 K = \overline{K}$.

By monotonicity, $\operatorname{cl}_1 K$ lies between $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_1 \overline{K} = \overline{K}$. -/
theorem partialCl₁_eq_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup)
    (hK : K ∈ saddleClass Klow Kup) : partialCl₁ K = Kup := by
  have hcc : partialCl₁ Kup = Kup := by
    rw [← h1]
    exact partialClosed₁_partialCl₁ Klow
  exact le_antisymm ((partialCl₁_mono hK.2).trans hcc.le)
    (h1.symm.trans_le (partialCl₁_mono hK.1))

end IntervalCl₁

section Interval

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
  {Klow Kup K L : U × X → EReal}

/-- Let $U$ and $X$ be commutative topological groups, and let $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$. Any two members of the
interval between $\underline{K}$ and $\overline{K}$ are equivalent. -/
theorem saddleEquiv_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    (hK : K ∈ saddleClass Klow Kup) (hL : L ∈ saddleClass Klow Kup) : SaddleEquiv K L :=
  ⟨(partialCl₁_eq_of_mem_saddleClass h1 hK).trans (partialCl₁_eq_of_mem_saddleClass h1 hL).symm,
    (partialCl₂_eq_of_mem_saddleClass h2 hK).trans (partialCl₂_eq_of_mem_saddleClass h2 hL).symm⟩

/-- Let $U$ and $X$ be commutative topological groups, and let $\operatorname{cl}_1 \underline{K} =
\overline{K}$ and $\operatorname{cl}_2 \overline{K} = \underline{K}$. Every member of the
interval between $\underline{K}$ and $\overline{K}$ is a closed saddle-function. -/
theorem closedSaddleFn_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup)
    (h2 : partialCl₂ Kup = Klow) (hK : K ∈ saddleClass Klow Kup) : ClosedSaddleFn K := by
  constructor
  · rw [partialCl₂_eq_of_mem_saddleClass h2 hK, h1, partialCl₁_eq_of_mem_saddleClass h1 hK]
  · rw [partialCl₁_eq_of_mem_saddleClass h1 hK, h2, partialCl₂_eq_of_mem_saddleClass h2 hK]

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X]
  [IsTopologicalAddGroup X] in
/-- If $\operatorname{cl}_2 \overline{K} = \underline{K}$, then $\underline{K}$ lies in the interval
between $\underline{K}$ and $\overline{K}$. -/
theorem mem_saddleClass_left (h2 : partialCl₂ Kup = Klow) : Klow ∈ saddleClass Klow Kup :=
  ⟨le_refl _, le_of_partialCl₂_eq h2⟩

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X]
  [IsTopologicalAddGroup X] in
/-- If $\operatorname{cl}_2 \overline{K} = \underline{K}$, then $\overline{K}$ lies in the interval
between $\underline{K}$ and $\overline{K}$. -/
theorem mem_saddleClass_right (h2 : partialCl₂ Kup = Klow) : Kup ∈ saddleClass Klow Kup :=
  ⟨le_of_partialCl₂_eq h2, le_refl _⟩

end Interval

/-! ### The interval of a closed convex bifunction -/

section Omega

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : Bifun U X} {K : U × Y → EReal}

/-- Let $U$, $X$ and $Y$ be locally convex topological vector spaces, let the pairing of $U$ with
$V$ be compatible on $U$, and let the pairing of $X$ with $Y$ be compatible on both $X$ and $Y$.
Let $F$ be a closed convex bifunction from $U$ to $X$. If $\langle Fu, y \rangle \le K(u, y) \le
\langle u, F^* y \rangle$ for all $(u, y)$, then $\operatorname{cl}_2 K(u, y) = \langle Fu, y
\rangle$. -/
theorem partialCl₂_eq_bracket_of_mem_saddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)) :
    partialCl₂ K = fun p : U × Y => bracket Bx F p.1 p.2 :=
  partialCl₂_eq_of_mem_saddleClass (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- Let $U$ be a locally convex topological vector space with a compatible pairing with $V$, and let
$F$ be a convex bifunction from $U$ to $X$. If $\langle Fu, y \rangle \le K(u, y) \le \langle u,
F^* y \rangle$ for all $(u, y)$, then $\operatorname{cl}_1 K(u, y) = \langle u, F^* y \rangle$.

Closedness of $F$ is not needed here. -/
theorem partialCl₁_eq_concaveBracket_of_mem_saddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)) :
    partialCl₁ K = fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2 :=
  partialCl₁_eq_of_mem_saddleClass (partialCl₁_bracket Bu Bx hF) hK

/-- Let $U$, $X$ and $Y$ be locally convex topological vector spaces, let the pairing of $U$ with
$V$ be compatible on $U$, and let the pairing of $X$ with $Y$ be compatible on both $X$ and $Y$.
Let $F$ be a closed convex bifunction from $U$ to $X$. If $\langle Fu, y \rangle \le K(u, y) \le
\langle u, F^* y \rangle$ for all $(u, y)$, then $K$ is a closed saddle-function. -/
theorem closedSaddleFn_of_mem_saddleClass_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2)) :
    ClosedSaddleFn K :=
  closedSaddleFn_of_mem_saddleClass (partialCl₁_bracket Bu Bx hF)
    (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK

/-- Let $U$, $X$ and $Y$ be locally convex topological vector spaces, let the pairing of $U$ with
$V$ be compatible on $U$, and let the pairing of $X$ with $Y$ be compatible on both $X$ and $Y$.
If $K$ is a closed concave-convex function on $U \times Y$, then there is exactly one bifunction
$F$ from $U$ to $X$ that is convex and closed and satisfies $$\langle Fu, y \rangle =
\operatorname{cl}_2 K(u, y) \quad \text{and} \quad \langle u, F^* y \rangle =
\operatorname{cl}_1 K(u, y) \quad \text{for all } (u, y).$$ This is the converse part of Theorem
34.2 of [rockafellar1970convex].

Together with `ConvexAnalysis.mem_saddleClass_self`, it shows that every equivalence class of
closed saddle-functions is an interval $\Omega(F)$. -/
theorem exists_unique_bifun_of_closedSaddleFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedConvexBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = partialCl₂ K ∧
      (fun p : U × Y => concaveBracket Bu (convexAdjointBifun Bu Bx F) p.1 p.2) = partialCl₁ K :=
  exists_unique_bifun_of_closure_pair Bu Bx (concaveConvexFn_partialCl₂ Bx hK) hcl.1 hcl.2

end Omega

end ConvexAnalysis
