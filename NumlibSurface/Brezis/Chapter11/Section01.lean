import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.RingTheory.Finiteness.Cofinite
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Numlib.Analysis.Normed.Module.FiniteCodim
import NumlibSurface.Brezis.Chapter02.Section04

/-!
# Brezis §11.1: finite-dimensional and finite-codimensional spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §11.1, over a real Banach space `E`. Almost everything
is Mathlib: Propositions 11.1, 11.2 and 11.5 and the closedness half of Proposition 11.4 are
`Submodule.closed_of_finiteDimensional`, `LinearMap.continuous_of_finiteDimensional`,
`Submodule.isClosed_mono_of_finiteDimensional_quotient` and
`Submodule.isClosed_sup_finiteDimensional`. The rest — `dim X* = dim X`, Proposition 11.3, the
complement half of Proposition 11.4, Propositions 11.6 and 11.7 — is the backbone
`Numlib/Analysis/Normed/Module/FiniteCodim`, stated there over `RCLike 𝕜` and read here at `ℝ`.

Vocabulary. "`M` admits a complement" is §2.4's `Brezis.Chapter02.IsComplement M N` for some
`N` (a closed subspace `N` with `M ∩ N = {0}` and `M + N = E`), which for a closed `M` in a
Banach space is Mathlib's `Submodule.ClosedComplemented M` (`admitsComplement_iff`); the
theorems are stated with the book's phrase and bridged to the backbone through that lemma.
"Finite codimension" is the book's Definition, `IsFiniteCodim M` (a finite-dimensional `X`
with `M + X = E`), identified with Mathlib's `Submodule.CoFG M` (`Module.Finite ℝ (E ⧸ M)`)
by `isFiniteCodim_iff_coFG`; `codim M` is `Module.finrank ℝ (E ⧸ M)`, and
`codim_eq_finrank_of_isCompl` is the book's "the dimension of such `X`, independent of the
choice". The theorems carry the book's `[CompleteSpace E]` whether or not the proof uses it.

## Main results

* `proposition_11_1`, `proposition_11_2`, `proposition_11_2_functional` — finite-dimensional
  subspaces are closed; linear operators on a finite-dimensional space are bounded.
* `finrank_dual`, `coord_basis_strongDual`, `proposition_11_3` — `dim X* = dim X`, the dual
  basis of coordinate functionals, and the converse "`X*` finite-dimensional ⇒ `X` is".
* `admitsComplement_iff`, `proposition_11_4`, `proposition_11_4_closedComplemented` — `M + X`
  is closed, and admits a complement iff `M` does.
* `IsFiniteCodim`, `isFiniteCodim_iff_coFG`, `IsFiniteCodim.exists_finiteDimensional_isCompl`,
  `codim`, `codim_eq_finrank_of_isCompl` — the Definition paragraph.
* `proposition_11_5`, `proposition_11_6`, `proposition_11_7` — subspaces containing a closed
  finite-codimensional one are closed; complements inside a dense subspace; complements from
  `G + L + X₁ = E` and `G ∩ L ⊆ X₂`.

The opening sentence's facts about `ℝ^p` (completeness, equivalence of norms, compactness of
the unit ball) are Mathlib's `FiniteDimensional.complete`, `ContinuousLinearEquiv.ofFinrankEq`
and `FiniteDimensional.proper` and are not restated; the two bracketed warnings (a sum of closed
subspaces need not be closed, a subspace of finite codimension need not be closed) are not
formalized.
-/

open Module

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Finite-dimensional spaces -/

/-- **Proposition 11.1.** Let `E` be a Banach space and let `X ⊆ E` be a finite-dimensional
subspace. Then `X` is closed. -/
theorem proposition_11_1 [CompleteSpace E] (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    IsClosed (X : Set E) :=
  X.closed_of_finiteDimensional

/-- **Proposition 11.2.** Assume that `X` is finite-dimensional and `F` is a Banach space. Then
every linear operator `T : X → F` is bounded: `T` is continuous, and `‖T x‖ ≤ C ‖x‖` for some
constant `C` (the book's `C = max ‖T eᵢ‖` times the constant of the equivalence of norms). -/
theorem proposition_11_2 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : X →ₗ[ℝ] F) : Continuous T ∧ ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖x‖ :=
  ⟨T.continuous_of_finiteDimensional,
    ⟨‖LinearMap.toContinuousLinearMap T‖, fun x =>
      (LinearMap.toContinuousLinearMap T).le_opNorm x⟩⟩

/-- **Proposition 11.2, "in particular".** All linear functionals on a finite-dimensional space
`X` are continuous. -/
theorem proposition_11_2_functional {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : X →ₗ[ℝ] ℝ) : Continuous f :=
  f.continuous_of_finiteDimensional

/-- **The paragraph after Proposition 11.2.** The dual space `X*` of a finite-dimensional space
`X` is finite-dimensional, and `dim X* = dim X`. -/
theorem finrank_dual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    FiniteDimensional ℝ (StrongDual ℝ X) ∧ finrank ℝ (StrongDual ℝ X) = finrank ℝ X :=
  ⟨(LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := X) (F' := ℝ)).finiteDimensional,
    NormedSpace.finrank_strongDual⟩

/-- **The paragraph after Proposition 11.2, "more precisely".** If `(eᵢ)` is a basis of `X`,
write `x = ∑ xᵢ eᵢ` and set `fᵢ(x) = xᵢ`; the functionals `(fᵢ)` form a basis of `X*`. -/
theorem coord_basis_strongDual {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {ι : Type*} [Finite ι] (b : Basis ι ℝ X) :
    ∃ b' : Basis ι ℝ (StrongDual ℝ X), ∀ i x, b' i x = b.repr x i := by
  classical
  exact ⟨b.dualBasis.map LinearMap.toContinuousLinearMap, fun i x => by
    rw [Basis.map_apply]
    exact b.dualBasis_apply i x⟩

/-- **Proposition 11.3.** Assume that `X` is a Banach space such that `X*` is
finite-dimensional. Then `X` is finite-dimensional and `dim X = dim X*`. -/
theorem proposition_11_3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ (StrongDual ℝ X)] :
    FiniteDimensional ℝ X ∧ finrank ℝ X = finrank ℝ (StrongDual ℝ X) :=
  have := NormedSpace.finiteDimensional_of_finiteDimensional_strongDual (𝕜 := ℝ) (E := X)
  ⟨this, NormedSpace.finrank_strongDual.symm⟩

/-! ### Complements -/

/-- **The vocabulary of §11.1.** "`M` admits a complement in `E`" — a closed subspace `N` with
`M ∩ N = {0}` and `M + N = E`, §2.4's `IsComplement M N` — is, for a subspace `M` of a Banach
space, Mathlib's `Submodule.ClosedComplemented M` together with the closedness of `M`. -/
theorem admitsComplement_iff [CompleteSpace E] (M : Submodule ℝ E) :
    M.ClosedComplemented ↔ IsClosed (M : Set E) ∧ ∃ N, Chapter02.IsComplement M N :=
  Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl

/-- **Proposition 11.4, first clause.** Let `E` be a Banach space, `M ⊆ E` a closed subspace
and `X ⊆ E` a finite-dimensional subspace. Then `M + X` is closed. -/
theorem proposition_11_4 [CompleteSpace E] {M : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    IsClosed ((M ⊔ X : Submodule ℝ E) : Set E) :=
  Submodule.isClosed_sup_finiteDimensional M X hM

/-- **Proposition 11.4, "moreover".** Under the same hypotheses, `M + X` admits a complement in
`E` if and only if `M` does. -/
theorem proposition_11_4_closedComplemented [CompleteSpace E] {M : Submodule ℝ E}
    (hM : IsClosed (M : Set E)) (X : Submodule ℝ E) [FiniteDimensional ℝ X] :
    (∃ N, Chapter02.IsComplement (M ⊔ X) N) ↔ ∃ N, Chapter02.IsComplement M N := by
  have hMX : IsClosed ((M ⊔ X : Submodule ℝ E) : Set E) := proposition_11_4 hM X
  refine ((and_iff_right hMX).symm.trans (admitsComplement_iff _).symm).trans ?_
  refine (Submodule.closedComplemented_sup_finiteDimensional_iff hM X).trans ?_
  exact (admitsComplement_iff M).trans (and_iff_right hM)

/-! ### Finite codimension -/

/-- **The Definition of §11.1.** A subspace `M` of a Banach space `E` has finite codimension
if there exists a finite-dimensional subspace `X ⊆ E` such that `M + X = E`. -/
def IsFiniteCodim (M : Submodule ℝ E) : Prop :=
  ∃ X : Submodule ℝ E, FiniteDimensional ℝ X ∧ M ⊔ X = ⊤

/-- The book's Definition is Mathlib's `Submodule.CoFG M`, i.e. `Module.Finite ℝ (E ⧸ M)`. -/
theorem isFiniteCodim_iff_coFG (M : Submodule ℝ E) : IsFiniteCodim M ↔ M.CoFG := by
  constructor
  · rintro ⟨X, hX, hsup⟩
    exact (Module.Finite.iff_fg.1 hX).cofg_of_codisjoint (codisjoint_iff.2 (by rwa [sup_comm]))
  · intro h
    obtain ⟨X, hX⟩ := M.exists_isCompl
    exact ⟨X, Module.Finite.iff_fg.2 (h.fg_of_isCompl hX), hX.sup_eq_top⟩

/-- "We may always assume that `M ∩ X = {0}`": a subspace of finite codimension has a
finite-dimensional algebraic complement. -/
theorem IsFiniteCodim.exists_finiteDimensional_isCompl {M : Submodule ℝ E}
    (h : IsFiniteCodim M) : ∃ X : Submodule ℝ E, FiniteDimensional ℝ X ∧ IsCompl M X := by
  have := (isFiniteCodim_iff_coFG M).1 h
  obtain ⟨X, hX⟩ := M.exists_isCompl
  exact ⟨X, Module.Finite.iff_fg.2 (Submodule.CoFG.fg_of_isCompl hX this), hX⟩

/-- **The codimension.** `codim M` is the dimension of a finite-dimensional complement `X` of
`M` (see `codim_eq_finrank_of_isCompl`); "it coincides with `dim (E/M)`", which is the
definition taken here (`0` when infinite, as `Module.finrank` is). -/
noncomputable def codim (M : Submodule ℝ E) : ℕ :=
  finrank ℝ (E ⧸ M)

/-- The codimension is the dimension of any algebraic complement `X` of `M`, "independent of
the special choice of `X`". -/
theorem codim_eq_finrank_of_isCompl {M X : Submodule ℝ E} (h : IsCompl M X) :
    codim M = finrank ℝ X :=
  (M.quotientEquivOfIsCompl X h).finrank_eq

/-- **Proposition 11.5.** Let `E` be a Banach space and `M` a closed subspace of finite
codimension. Then any subspace `M̃` of `E` containing `M` is closed. -/
theorem proposition_11_5 [CompleteSpace E] {M M' : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hcodim : IsFiniteCodim M) (hle : M ≤ M') : IsClosed (M' : Set E) :=
  have := (isFiniteCodim_iff_coFG M).1 hcodim
  Submodule.isClosed_mono_of_finiteDimensional_quotient hM hle

/-- **Proposition 11.6.** Let `E` be a Banach space, `M` a closed subspace of finite
codimension and `D` a dense subspace of `E`. Then there exists a complement `X` of `M` with
`X ⊆ D`. -/
theorem proposition_11_6 [CompleteSpace E] {M D : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hcodim : IsFiniteCodim M) (hD : Dense (D : Set E)) :
    ∃ X : Submodule ℝ E, X ≤ D ∧ Chapter02.IsComplement M X := by
  have := (isFiniteCodim_iff_coFG M).1 hcodim
  obtain ⟨X, hXD, hMX⟩ := Submodule.exists_isCompl_le_of_dense hM hD
  have : FiniteDimensional ℝ X := Module.Finite.iff_fg.2 (Submodule.CoFG.fg_of_isCompl hMX this)
  exact ⟨X, hXD, X.closed_of_finiteDimensional, hMX⟩

/-- **Proposition 11.7.** Let `E` be a Banach space and `G, L ⊆ E` closed subspaces. Assume
there exist finite-dimensional subspaces `X₁, X₂ ⊆ E` such that `G + L + X₁ = E` and
`G ∩ L ⊆ X₂`. Then `G` (resp. `L`) admits a complement. -/
theorem proposition_11_7 [CompleteSpace E] {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) (X₁ X₂ : Submodule ℝ E) [FiniteDimensional ℝ X₁]
    [FiniteDimensional ℝ X₂] (hsup : G ⊔ L ⊔ X₁ = ⊤) (hinf : G ⊓ L ≤ X₂) :
    (∃ N, Chapter02.IsComplement G N) ∧ ∃ N, Chapter02.IsComplement L N := by
  constructor
  · exact ((admitsComplement_iff G).1
      (Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le hG hL X₁ X₂ hsup hinf)).2
  · refine ((admitsComplement_iff L).1
      (Submodule.closedComplemented_of_sup_sup_eq_top_of_inf_le hL hG X₁ X₂ ?_ ?_)).2
    · rwa [sup_comm L G]
    · rwa [inf_comm L G]

end Brezis.Chapter11
