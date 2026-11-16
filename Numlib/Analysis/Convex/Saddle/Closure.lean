/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Defs

/-!
# The lower and upper closures of a saddle-function

Let $U$ and $X$ be topological spaces and let $K : U \times X \to [-\infty, +\infty]$. Write
$\operatorname{cl}_1 K$ for the function that closes $K(\cdot, x)$ as a concave function for each
$x$, and $\operatorname{cl}_2 K$ for the function that closes $K(u, \cdot)$ as a convex function for
each $u$. Applying the two partial closures in the two possible orders gives the **lower closure**
$\operatorname{cl}_2 \operatorname{cl}_1 K$ and the **upper closure**
$\operatorname{cl}_1 \operatorname{cl}_2 K$ of $K$. The two closures do not agree in general, and
this is the reason why saddle-functions are grouped into equivalence classes. Each of them is
idempotent. The presentation follows [rockafellar1970convex], §33–§34.

Idempotence needs no duality and no hypothesis on $K$: $\operatorname{cl}_1$ raises a function and
$\operatorname{cl}_2$ lowers it, and each is monotone and idempotent.

## Main definitions

* `ConvexAnalysis.lowerCl`, `ConvexAnalysis.upperCl`: the lower closure
  $\operatorname{cl}_2 \operatorname{cl}_1 K$ and the upper closure
  $\operatorname{cl}_1 \operatorname{cl}_2 K$.
* `ConvexAnalysis.LowerClosedFn`, `ConvexAnalysis.UpperClosedFn`, `ConvexAnalysis.FullyClosedFn`:
  $K$ equals its lower closure, $K$ equals its upper closure, and $K$ is fixed by both
  $\operatorname{cl}_1$ and $\operatorname{cl}_2$.

## Main results

* `ConvexAnalysis.fullyClosedFn_iff`: $K$ is fully closed if and only if it is lower closed and
  upper closed.
* `ConvexAnalysis.upperCl_saddleSwap`, `ConvexAnalysis.lowerCl_saddleSwap`: the involution
  $K \mapsto -K(u, x)$ read at $(x, u)$ exchanges the lower and the upper closure.
* `ConvexAnalysis.lowerCl_idem`, `ConvexAnalysis.upperCl_idem`: each closure is idempotent, for
  every $K$. This is Theorem 34.1 of [rockafellar1970convex].
-/

namespace ConvexAnalysis

/-! ### The two closures -/

section Defs

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

/-- The **lower closure** of $K : U \times X \to [-\infty, +\infty]$ is
$\operatorname{cl}_2 \operatorname{cl}_1 K$: first close $K(\cdot, x)$ concavely for each $x$,
then close the result convexly in the second variable for each $u$. -/
noncomputable def lowerCl (K : U × X → EReal) : U × X → EReal := partialCl₂ (partialCl₁ K)

/-- The **upper closure** of $K : U \times X \to [-\infty, +\infty]$ is
$\operatorname{cl}_1 \operatorname{cl}_2 K$: first close $K(u, \cdot)$ convexly for each $u$,
then close the result concavely in the first variable for each $x$. -/
noncomputable def upperCl (K : U × X → EReal) : U × X → EReal := partialCl₁ (partialCl₂ K)

/-- The lower closure of $K$ is $\operatorname{cl}_2 \operatorname{cl}_1 K$. -/
theorem lowerCl_def (K : U × X → EReal) : lowerCl K = partialCl₂ (partialCl₁ K) := rfl

/-- The upper closure of $K$ is $\operatorname{cl}_1 \operatorname{cl}_2 K$. -/
theorem upperCl_def (K : U × X → EReal) : upperCl K = partialCl₁ (partialCl₂ K) := rfl

/-- A function $K : U \times X \to [-\infty, +\infty]$ is **lower closed** if it equals its lower
closure: $\operatorname{cl}_2 \operatorname{cl}_1 K = K$. -/
def LowerClosedFn (K : U × X → EReal) : Prop := lowerCl K = K

/-- A function $K : U \times X \to [-\infty, +\infty]$ is **upper closed** if it equals its upper
closure: $\operatorname{cl}_1 \operatorname{cl}_2 K = K$. -/
def UpperClosedFn (K : U × X → EReal) : Prop := upperCl K = K

/-- A function $K : U \times X \to [-\infty, +\infty]$ is **fully closed** if it is closed in each
variable separately: $\operatorname{cl}_2 K = K$ and $\operatorname{cl}_1 K = K$. -/
def FullyClosedFn (K : U × X → EReal) : Prop := PartialClosed₂ K ∧ PartialClosed₁ K

/-- $K$ is lower closed if and only if $\operatorname{cl}_2 \operatorname{cl}_1 K = K$. -/
theorem lowerClosedFn_iff : LowerClosedFn K ↔ lowerCl K = K := Iff.rfl

/-- $K$ is upper closed if and only if $\operatorname{cl}_1 \operatorname{cl}_2 K = K$. -/
theorem upperClosedFn_iff : UpperClosedFn K ↔ upperCl K = K := Iff.rfl

/-- $K$ is fully closed if and only if $\operatorname{cl}_2 K = K$ and $\operatorname{cl}_1 K = K$.
-/
theorem fullyClosedFn_iff' : FullyClosedFn K ↔ PartialClosed₂ K ∧ PartialClosed₁ K := Iff.rfl

end Defs

section FullyClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- A lower closed function is closed in the second variable: if
$\operatorname{cl}_2 \operatorname{cl}_1 K = K$, then $\operatorname{cl}_2 K = K$. -/
theorem LowerClosedFn.partialClosed₂ (hK : LowerClosedFn K) : PartialClosed₂ K := by
  rw [← hK, lowerCl_def]
  exact partialClosed₂_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- An upper closed function is closed in the first variable: if
$\operatorname{cl}_1 \operatorname{cl}_2 K = K$, then $\operatorname{cl}_1 K = K$. -/
theorem UpperClosedFn.partialClosed₁ (hK : UpperClosedFn K) : PartialClosed₁ K := by
  rw [← hK, upperCl_def]
  exact partialClosed₁_partialCl₁ (partialCl₂ K)

/-- Let $U$ and $X$ be commutative topological groups and let
$K : U \times X \to [-\infty, +\infty]$. Then $K$ is fully closed, that is
$\operatorname{cl}_1 K = K$ and $\operatorname{cl}_2 K = K$, if and only if $K$ is both lower
closed and upper closed. -/
theorem fullyClosedFn_iff : FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K := by
  constructor
  · rintro ⟨h2, h1⟩
    exact ⟨by rw [lowerClosedFn_iff, lowerCl_def, h1, h2],
      by rw [upperClosedFn_iff, upperCl_def, h2, h1]⟩
  · rintro ⟨hl, hu⟩
    exact ⟨hl.partialClosed₂, hu.partialClosed₁⟩

end FullyClosed

/-! ### The closures under the swap involution -/

section SwapClosure

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

/-- The swap $K \mapsto \tilde K$, with $\tilde K(x, u) = -K(u, x)$, carries the lower closure to
the upper closure: the upper closure of $\tilde K$ is the swap of the lower closure of $K$. -/
theorem upperCl_saddleSwap (K : U × X → EReal) :
    upperCl (saddleSwap K) = saddleSwap (lowerCl K) := by
  rw [upperCl_def, partialCl₂_saddleSwap, partialCl₁_saddleSwap, lowerCl_def]

/-- The swap $K \mapsto \tilde K$, with $\tilde K(x, u) = -K(u, x)$, carries the upper closure to
the lower closure: the lower closure of $\tilde K$ is the swap of the upper closure of $K$. -/
theorem lowerCl_saddleSwap (K : U × X → EReal) :
    lowerCl (saddleSwap K) = saddleSwap (upperCl K) := by
  rw [lowerCl_def, partialCl₁_saddleSwap, partialCl₂_saddleSwap, upperCl_def]

/-- $K$ is lower closed if and only if its swap $\tilde K(x, u) = -K(u, x)$ is upper closed. -/
theorem lowerClosedFn_iff_upperClosedFn_saddleSwap :
    LowerClosedFn K ↔ UpperClosedFn (saddleSwap K) := by
  rw [lowerClosedFn_iff, upperClosedFn_iff, upperCl_saddleSwap]
  exact ⟨fun h => by rw [h], fun h => saddleSwap_injective h⟩

end SwapClosure

/-! ### Idempotence of the two closures -/

section Idempotence

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- Let $U$ and $X$ be commutative topological groups. For every
$K : U \times X \to [-\infty, +\infty]$, the lower closure is lower closed:
$$\operatorname{cl}_2 \operatorname{cl}_1 (\operatorname{cl}_2 \operatorname{cl}_1 K)
  = \operatorname{cl}_2 \operatorname{cl}_1 K.$$
This is Theorem 34.1 of [rockafellar1970convex] for the lower closure.

No duality is needed. The operators $\operatorname{cl}_1$ and $\operatorname{cl}_2$ are monotone
and idempotent, $\operatorname{cl}_1$ raises a function and $\operatorname{cl}_2$ lowers it.
With $M = \operatorname{cl}_1 K$ and $N = \operatorname{cl}_2 M$ the chain $\operatorname{cl}_2
\operatorname{cl}_1 N \le \operatorname{cl}_2 \operatorname{cl}_1 M = \operatorname{cl}_2 M =
N = \operatorname{cl}_2 N \le \operatorname{cl}_2 \operatorname{cl}_1 N$ gives the claim. -/
theorem lowerCl_idem (K : U × X → EReal) : lowerCl (lowerCl K) = lowerCl K := by
  have hAM : partialCl₁ (partialCl₁ K) = partialCl₁ K := partialClosed₁_partialCl₁ K
  have hBN : partialCl₂ (partialCl₂ (partialCl₁ K)) = partialCl₂ (partialCl₁ K) :=
    partialClosed₂_partialCl₂ (partialCl₁ K)
  have hNM : partialCl₂ (partialCl₁ K) ≤ partialCl₁ K := partialCl₂_le _
  simp only [lowerCl_def]
  refine le_antisymm ?_ ?_
  · calc partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K)))
        ≤ partialCl₂ (partialCl₁ (partialCl₁ K)) := partialCl₂_mono (partialCl₁_mono hNM)
      _ = partialCl₂ (partialCl₁ K) := by rw [hAM]
  · calc partialCl₂ (partialCl₁ K) = partialCl₂ (partialCl₂ (partialCl₁ K)) := hBN.symm
      _ ≤ partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K))) :=
          partialCl₂_mono (le_partialCl₁ _)

/-- Let $U$ and $X$ be commutative topological groups. For every
$K : U \times X \to [-\infty, +\infty]$, the upper closure is upper closed:
$$\operatorname{cl}_1 \operatorname{cl}_2 (\operatorname{cl}_1 \operatorname{cl}_2 K)
  = \operatorname{cl}_1 \operatorname{cl}_2 K.$$
This is Theorem 34.1 of [rockafellar1970convex] for the upper closure.

The proof applies `ConvexAnalysis.lowerCl_idem` to the swap $\tilde K(x, u) = -K(u, x)$. -/
theorem upperCl_idem (K : U × X → EReal) : upperCl (upperCl K) = upperCl K := by
  have h := lowerCl_idem (saddleSwap K)
  rw [lowerCl_saddleSwap, lowerCl_saddleSwap] at h
  exact saddleSwap_injective h

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- The lower closure is closed in the second variable, because it is of the form
$\operatorname{cl}_2 M$. -/
theorem partialClosed₂_lowerCl (K : U × X → EReal) : PartialClosed₂ (lowerCl K) :=
  partialClosed₂_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The upper closure is closed in the first variable, because it is of the form
$\operatorname{cl}_1 M$. -/
theorem partialClosed₁_upperCl (K : U × X → EReal) : PartialClosed₁ (upperCl K) :=
  partialClosed₁_partialCl₁ (partialCl₂ K)

end Idempotence

end ConvexAnalysis
