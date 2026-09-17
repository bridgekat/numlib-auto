import Numlib.Analysis.Normed.Module.Annihilator
import NumlibSurface.Brezis.Chapter01.Section02

/-!
# Brezis §1.3: the bidual `E**`, orthogonality relations

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §1.3, over a real normed space `E`. The canonical
injection `J : E → E**` is Mathlib's `NormedSpace.inclusionInDoubleDual ℝ E`, with
`⟨J x, f⟩ = ⟨f, x⟩` (`NormedSpace.dual_def`) and the isometry `inclusionInDoubleDualLi`;
reflexivity (`J` onto) is the backbone's `NormedSpace.IsReflexive ℝ E`, restated in chapter 3.
The orthogonals `M^⊥ ⊆ E*` (for `M ⊆ E`) and `N^⊥ ⊆ E` (for `N ⊆ E*`) are the backbone's
`Submodule.strongDualAnnihilator` and `Submodule.strongDualCoannihilator`
(`Numlib/Analysis/Normed/Module/Annihilator`); Proposition 1.9 and Remark 6's reflexive clause
are `strongDualCoannihilator_strongDualAnnihilator`,
`topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator` and
`strongDualAnnihilator_strongDualCoannihilator` there.

## Main results

* `canonicalInjection_apply`, `norm_canonicalInjection`, `canonicalInjection_injective` — the
  canonical injection `J` and its isometry.
* `mem_orthogonal_iff`, `isClosed_orthogonal` — the two orthogonals of the Notation paragraph.
* `proposition_1_9`, `proposition_1_9_supset` — `(M^⊥)^⊥ = closure M` and `(N^⊥)^⊥ ⊇ closure N`.
* `remark_1_6` — `(N^⊥)^⊥ = closure N` when `E` is reflexive.

Remark 6's strict inclusion in `ℓ¹` (Exercise 1.16) and its last sentence, that `(N^⊥)^⊥` is
the weak-∗ closure of `N`, are not stated here (the latter is chapter 3's).
-/

open NormedSpace

namespace Brezis.Chapter01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The canonical injection -/

/-- **The canonical injection `J : E → E**`** of §1.3: `J x` is the functional `f ↦ ⟨f, x⟩` on
`E*`, so that `⟨J x, f⟩_{E**, E*} = ⟨f, x⟩_{E*, E}`. It is `NormedSpace.inclusionInDoubleDual ℝ E`,
a bounded linear map. -/
theorem canonicalInjection_apply (x : E) (f : StrongDual ℝ E) :
    inclusionInDoubleDual ℝ E x f = f x :=
  dual_def ℝ E x f

/-- **`J` is an isometry**: `‖J x‖_{E**} = ‖x‖_E` (by Corollary 1.4). -/
theorem norm_canonicalInjection (x : E) : ‖inclusionInDoubleDual ℝ E x‖ = ‖x‖ :=
  (inclusionInDoubleDualLi ℝ).norm_map x

/-- `J` is injective (it is an isometry). -/
theorem canonicalInjection_injective : Function.Injective (inclusionInDoubleDual ℝ E) :=
  (inclusionInDoubleDualLi ℝ (E := E)).injective

/-! ### The orthogonals -/

/-- **The Notation of §1.3.** For a subspace `M ⊆ E`, `M^⊥ = {f ∈ E* | ⟨f, x⟩ = 0 ∀ x ∈ M}` is
`M.strongDualAnnihilator`; for a subspace `N ⊆ E*`, `N^⊥ = {x ∈ E | ⟨f, x⟩ = 0 ∀ f ∈ N}` — a
subset of `E` rather than of `E**` — is `N.strongDualCoannihilator`. -/
theorem mem_orthogonal_iff (M : Submodule ℝ E) (N : Submodule ℝ (StrongDual ℝ E))
    (f : StrongDual ℝ E) (x : E) :
    (f ∈ M.strongDualAnnihilator ↔ ∀ y ∈ M, f y = 0) ∧
      (x ∈ N.strongDualCoannihilator ↔ ∀ g ∈ N, g x = 0) :=
  ⟨Submodule.mem_strongDualAnnihilator, Submodule.mem_strongDualCoannihilator⟩

/-- "It is clear that `M^⊥` (resp. `N^⊥`) is a closed linear subspace of `E*` (resp. `E`)." -/
theorem isClosed_orthogonal (M : Submodule ℝ E) (N : Submodule ℝ (StrongDual ℝ E)) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual ℝ E)) ∧
      IsClosed (N.strongDualCoannihilator : Set E) :=
  ⟨M.isClosed_strongDualAnnihilator, N.isClosed_strongDualCoannihilator⟩

/-- **Proposition 1.9, first clause.** For a linear subspace `M ⊆ E`, `(M^⊥)^⊥ = closure M`. -/
theorem proposition_1_9 (M : Submodule ℝ E) :
    M.strongDualAnnihilator.strongDualCoannihilator = M.topologicalClosure :=
  M.strongDualCoannihilator_strongDualAnnihilator

/-- **Proposition 1.9, second clause.** For a linear subspace `N ⊆ E*`,
`(N^⊥)^⊥ ⊇ closure N`. -/
theorem proposition_1_9_supset (N : Submodule ℝ (StrongDual ℝ E)) :
    N.topologicalClosure ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  N.topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator

/-- **Remark 6.** If `E` is reflexive then `(N^⊥)^⊥ = closure N` for every linear subspace
`N ⊆ E*`: the separating `ξ ∈ E**` of the attempted proof is then `J x₀` for some `x₀ ∈ E`. -/
theorem remark_1_6 [IsReflexive ℝ E] (N : Submodule ℝ (StrongDual ℝ E)) :
    N.strongDualCoannihilator.strongDualAnnihilator = N.topologicalClosure :=
  N.strongDualAnnihilator_strongDualCoannihilator

end Brezis.Chapter01
