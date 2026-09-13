import Numlib.Analysis.Convex.Saddle.Correspondence

/-!
# Equivalence classes of saddle-functions

Two saddle-functions are **equivalent** when their partial closures agree, and `K` is **closed**
when `cl₁ K` and `cl₂ K` are both equivalent to `K`. This is weaker than lower or upper closedness:
a whole order interval can be closed while only its two ends are lower and upper closed.

The equivalence classes of closed saddle-functions are exactly the order intervals
`Ω(F) = {K | ⟨Fu, y⟩ ≤ K ≤ ⟨u, F* y⟩}` between the two brackets of a closed convex bifunction `F`;
on such an interval both partial closures are constant, equal to the two ends, and `F` is
determined by the class. The interval lemmas below are stated for a closure pair `(K̲, K̄)` with
`cl₁ K̲ = K̄` and `cl₂ K̄ = K̲` rather than for a bifunction, so they need no pairing; the closure
pairs are exactly the bracket pairs.

## Main definitions

* `SaddleEquiv K L` — `cl₁ K = cl₁ L` and `cl₂ K = cl₂ L`.
* `ClosedSaddleFn K` — `cl₁ cl₂ K = cl₁ K` and `cl₂ cl₁ K = cl₂ K`.
* `saddleClass Klow Kup` — the order interval `Ω`, as a set of functions.

## Main results

* `partialCl₂_eq_of_mem_saddleClass`, `closedSaddleFn_of_mem_saddleClass` — the closures are
  constant on the interval and every member of it is closed ([rockafellar1970convex] Theorem 34.2).
* `exists_unique_bifun_of_closedSaddleFn` — conversely, a closed concave-convex function determines
  a unique closed convex bifunction, with brackets `cl₂ K` and `cl₁ K`.

## References

* [rockafellar1970convex] §34.
-/

namespace ConvexAnalysis

/-! ### Equivalence, closedness, and the order interval -/

section Defs

variable {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] {K L M : U × X → EReal}

/-- Two saddle-functions are **equivalent** when their partial closures agree. Rockafellar uses the
single closures here, not the doubled ones. -/
def SaddleEquiv (K L : U × X → EReal) : Prop :=
  partialCl₁ K = partialCl₁ L ∧ partialCl₂ K = partialCl₂ L

theorem saddleEquiv_refl (K : U × X → EReal) : SaddleEquiv K K := ⟨rfl, rfl⟩

theorem SaddleEquiv.symm (h : SaddleEquiv K L) : SaddleEquiv L K := ⟨h.1.symm, h.2.symm⟩

theorem SaddleEquiv.trans (h : SaddleEquiv K L) (h' : SaddleEquiv L M) : SaddleEquiv K M :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- A saddle-function is **closed** when `cl₁ K` and `cl₂ K` are both equivalent to it; by
idempotence of the closures that amounts to these two equations. -/
def ClosedSaddleFn (K : U × X → EReal) : Prop :=
  partialCl₁ (partialCl₂ K) = partialCl₁ K ∧ partialCl₂ (partialCl₁ K) = partialCl₂ K

/-- Rockafellar's `Ω`: the saddle-functions between the two members of a closure pair. -/
def saddleClass (Klow Kup : U × X → EReal) : Set (U × X → EReal) := {K | Klow ≤ K ∧ K ≤ Kup}

omit [TopologicalSpace U] [TopologicalSpace X] in
theorem mem_saddleClass {Klow Kup : U × X → EReal} :
    K ∈ saddleClass Klow Kup ↔ Klow ≤ K ∧ K ≤ Kup := Iff.rfl

theorem mem_saddleClass_self (K : U × X → EReal) :
    K ∈ saddleClass (partialCl₂ K) (partialCl₁ K) := ⟨partialCl₂_le K, le_partialCl₁ K⟩

end Defs

section ClosedEquiv

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {K : U × X → EReal}

omit [AddCommGroup U] [IsTopologicalAddGroup U] in
theorem ClosedSaddleFn.saddleEquiv_partialCl₂ (h : ClosedSaddleFn K) :
    SaddleEquiv (partialCl₂ K) K :=
  ⟨h.1, convexClosedFn_partialCl₂ K⟩

omit [AddCommGroup X] [IsTopologicalAddGroup X] in
theorem ClosedSaddleFn.saddleEquiv_partialCl₁ (h : ClosedSaddleFn K) :
    SaddleEquiv (partialCl₁ K) K :=
  ⟨concaveClosedFn_partialCl₁ K, h.2⟩

end ClosedEquiv

/-! ### The closures are constant on the interval -/

section IntervalCl₂

variable {U X : Type*} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
  {Klow Kup K : U × X → EReal}

/-- On the interval of a closure pair, `cl₂` is constant at the lower end. Monotonicity squeezes
`cl₂ K` between `cl₂ K̲ = K̲` and `cl₂ K̄ = K̲`. -/
theorem partialCl₂_eq_of_mem_saddleClass (h2 : partialCl₂ Kup = Klow)
    (hK : K ∈ saddleClass Klow Kup) : partialCl₂ K = Klow := by
  have hcc : partialCl₂ Klow = Klow := by
    rw [← h2]
    exact convexClosedFn_partialCl₂ Kup
  exact le_antisymm ((partialCl₂_mono hK.2).trans h2.le)
    (hcc.symm.trans_le (partialCl₂_mono hK.1))

end IntervalCl₂

section IntervalCl₁

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  {Klow Kup K : U × X → EReal}

theorem partialCl₁_eq_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup)
    (hK : K ∈ saddleClass Klow Kup) : partialCl₁ K = Kup := by
  have hcc : partialCl₁ Kup = Kup := by
    rw [← h1]
    exact concaveClosedFn_partialCl₁ Klow
  exact le_antisymm ((partialCl₁_mono hK.2).trans hcc.le)
    (h1.symm.trans_le (partialCl₁_mono hK.1))

end IntervalCl₁

section Interval

variable {U X : Type*} [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U]
  [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
  {Klow Kup K L : U × X → EReal}

theorem saddleEquiv_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup) (h2 : partialCl₂ Kup = Klow)
    (hK : K ∈ saddleClass Klow Kup) (hL : L ∈ saddleClass Klow Kup) : SaddleEquiv K L :=
  ⟨(partialCl₁_eq_of_mem_saddleClass h1 hK).trans (partialCl₁_eq_of_mem_saddleClass h1 hL).symm,
    (partialCl₂_eq_of_mem_saddleClass h2 hK).trans (partialCl₂_eq_of_mem_saddleClass h2 hL).symm⟩

/-- Every member of the interval of a closure pair is a closed saddle-function. -/
theorem closedSaddleFn_of_mem_saddleClass (h1 : partialCl₁ Klow = Kup)
    (h2 : partialCl₂ Kup = Klow) (hK : K ∈ saddleClass Klow Kup) : ClosedSaddleFn K := by
  constructor
  · rw [partialCl₂_eq_of_mem_saddleClass h2 hK, h1, partialCl₁_eq_of_mem_saddleClass h1 hK]
  · rw [partialCl₁_eq_of_mem_saddleClass h1 hK, h2, partialCl₂_eq_of_mem_saddleClass h2 hK]

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X]
  [IsTopologicalAddGroup X] in
theorem mem_saddleClass_left (h2 : partialCl₂ Kup = Klow) : Klow ∈ saddleClass Klow Kup :=
  ⟨le_refl _, le_of_partialCl₂_eq h2⟩

omit [TopologicalSpace U] [AddCommGroup U] [IsTopologicalAddGroup U] [AddCommGroup X]
  [IsTopologicalAddGroup X] in
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

/-- Between the two brackets of a closed convex bifunction, `cl₂` is the lower bracket and `cl₁`
the upper. -/
theorem partialCl₂_eq_bracket_of_mem_saddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)) :
    partialCl₂ K = fun p : U × Y => bracket Bx F p.1 p.2 :=
  partialCl₂_eq_of_mem_saddleClass (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK

omit [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ X] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
theorem partialCl₁_eq_concaveBracket_of_mem_saddleClass (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hF : ConvexBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)) :
    partialCl₁ K = fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2 :=
  partialCl₁_eq_of_mem_saddleClass (partialCl₁_bracket Bu Bx hF) hK

theorem closedSaddleFn_of_mem_saddleClass_bracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bx.flip] (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ saddleClass (fun p : U × Y => bracket Bx F p.1 p.2)
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2)) :
    ClosedSaddleFn K :=
  closedSaddleFn_of_mem_saddleClass (partialCl₁_bracket Bu Bx hF)
    (partialCl₂_concaveBracket_adjoint Bu Bx hF hcl) hK

/-- Conversely, a closed concave-convex function determines a unique closed convex bifunction,
with brackets `cl₂ K` and `cl₁ K`. With `mem_saddleClass_self`, every class of closed
saddle-functions is an `Ω(F)`. -/
theorem exists_unique_bifun_of_closedSaddleFn (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu]
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx] [IsCompatiblePairing Bx.flip]
    (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K) :
    ∃! F : Bifun U X, ConvexBifun F ∧ ClosedBifun F ∧
      (fun p : U × Y => bracket Bx F p.1 p.2) = partialCl₂ K ∧
      (fun p : U × Y => concaveBracket Bu (adjointBifun Bu Bx F) p.1 p.2) = partialCl₁ K :=
  exists_unique_bifun_of_closure_pair Bu Bx (concaveConvexFn_partialCl₂ Bx hK) hcl.1 hcl.2

end Omega

end ConvexAnalysis
