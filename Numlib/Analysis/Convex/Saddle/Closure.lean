import Numlib.Analysis.Convex.Saddle.Defs

/-!
# The lower and upper closures of a saddle-function

Applying the two partial closures of a concave-convex function in the two possible orders gives the
**lower closure** `lowerCl K = cl₂ (cl₁ K)` and the **upper closure** `upperCl K = cl₁ (cl₂ K)`.
These do *not* agree in general — the discrepancy is what forces saddle-functions to be grouped
into equivalence classes — but each is idempotent.

Idempotence needs no duality: `cl₁` raises, `cl₂` lowers, and each is monotone and idempotent.

## Main definitions

* `lowerCl`, `upperCl` — the two closures; `LowerClosedFn`, `UpperClosedFn`, `FullyClosedFn` for
  the functions they fix.

## Main results

* `fullyClosedFn_iff` — fully closed means lower closed and upper closed.
* `upperCl_saddleSwap`, `lowerCl_saddleSwap` — `saddleSwap` exchanges the two closures.
* `lowerCl_idem`, `upperCl_idem` — each closure is idempotent ([rockafellar1970convex]
  Theorem 34.1), for every `K`: `cl₁` and `cl₂` are a closure and a co-closure operator, so no
  duality and no hypothesis is needed.

## References

* [rockafellar1970convex] §33–§34.
-/

namespace ConvexAnalysis

/-! ### The two closures -/

section Defs

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K : U × X → EReal}

/-- The **lower closure** `cl₂ cl₁ K` of a concave-convex function. -/
noncomputable def lowerCl (K : U × X → EReal) : U × X → EReal := partialCl₂ (partialCl₁ K)

/-- The **upper closure** `cl₁ cl₂ K` of a concave-convex function. -/
noncomputable def upperCl (K : U × X → EReal) : U × X → EReal := partialCl₁ (partialCl₂ K)

theorem lowerCl_def (K : U × X → EReal) : lowerCl K = partialCl₂ (partialCl₁ K) := rfl

theorem upperCl_def (K : U × X → EReal) : upperCl K = partialCl₁ (partialCl₂ K) := rfl

/-- `K` is **lower closed** when it is its own lower closure. -/
def LowerClosedFn (K : U × X → EReal) : Prop := lowerCl K = K

/-- `K` is **upper closed** when it is its own upper closure. -/
def UpperClosedFn (K : U × X → EReal) : Prop := upperCl K = K

/-- `K` is **fully closed** when it is closed in each variable separately. -/
def FullyClosedFn (K : U × X → EReal) : Prop := PartialClosed₂ K ∧ PartialClosed₁ K

theorem lowerClosedFn_iff : LowerClosedFn K ↔ lowerCl K = K := Iff.rfl

theorem upperClosedFn_iff : UpperClosedFn K ↔ upperCl K = K := Iff.rfl

theorem fullyClosedFn_iff' : FullyClosedFn K ↔ PartialClosed₂ K ∧ PartialClosed₁ K := Iff.rfl

end Defs

section FullyClosed

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
theorem LowerClosedFn.partialClosed₂ (hK : LowerClosedFn K) : PartialClosed₂ K := by
  rw [← hK, lowerCl_def]
  exact partialClosed₂_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
theorem UpperClosedFn.partialClosed₁ (hK : UpperClosedFn K) : PartialClosed₁ K := by
  rw [← hK, upperCl_def]
  exact partialClosed₁_partialCl₁ (partialCl₂ K)

/-- Fully closed is exactly lower closed and upper closed. -/
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

theorem upperCl_saddleSwap (K : U × X → EReal) :
    upperCl (saddleSwap K) = saddleSwap (lowerCl K) := by
  rw [upperCl_def, partialCl₂_saddleSwap, partialCl₁_saddleSwap, lowerCl_def]

theorem lowerCl_saddleSwap (K : U × X → EReal) :
    lowerCl (saddleSwap K) = saddleSwap (upperCl K) := by
  rw [lowerCl_def, partialCl₁_saddleSwap, partialCl₂_saddleSwap, upperCl_def]

theorem lowerClosedFn_iff_upperClosedFn_saddleSwap :
    LowerClosedFn K ↔ UpperClosedFn (saddleSwap K) := by
  rw [lowerClosedFn_iff, upperClosedFn_iff, upperCl_saddleSwap]
  exact ⟨fun h => by rw [h], fun h => saddleSwap_injective h⟩

end SwapClosure

/-! ### Idempotence of the two closures -/

section Idempotence

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]

/-- The lower closure is lower closed: `lowerCl` is idempotent.

No duality is needed: `cl₁` and `cl₂` are a closure and a *co*-closure operator — monotone,
idempotent, one raising and one lowering — and with `M = cl₁ K`, `N = cl₂ M` the chain
`cl₂ (cl₁ N) ≤ cl₂ (cl₁ M) = cl₂ M = N = cl₂ N ≤ cl₂ (cl₁ N)` closes. -/
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

/-- The upper closure is upper closed, by the swap involution. -/
theorem upperCl_idem (K : U × X → EReal) : upperCl (upperCl K) = upperCl K := by
  have h := lowerCl_idem (saddleSwap K)
  rw [lowerCl_saddleSwap, lowerCl_saddleSwap] at h
  exact saddleSwap_injective h

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
/-- The lower closure is convex-closed: it *is* a `cl₂`. -/
theorem partialClosed₂_lowerCl (K : U × X → EReal) : PartialClosed₂ (lowerCl K) :=
  partialClosed₂_partialCl₂ (partialCl₁ K)

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
/-- The upper closure is concave-closed: it *is* a `cl₁`. -/
theorem partialClosed₁_upperCl (K : U × X → EReal) : PartialClosed₁ (upperCl K) :=
  partialClosed₁_partialCl₁ (partialCl₂ K)

end Idempotence

end ConvexAnalysis
