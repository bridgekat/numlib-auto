import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Quotient
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter03.Section07
import NumlibSurface.Brezis.Chapter11.Section01

/-!
# Brezis §11.2: quotient spaces

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §11.2, the quotient `E/M` of a real Banach space `E`
by a closed subspace `M`. The space, its norm `‖[x]‖ = inf_{m ∈ M} ‖x − m‖`, `‖π‖ ≤ 1` and
Proposition 11.8 are Mathlib's normed quotient (`Submodule.Quotient.normedAddCommGroup`, an
instance under `[IsClosed (M : Set E)]`, `Submodule.Quotient.normedSpace`, `Submodule.mkQL`,
`QuotientAddGroup.norm_mk`, `Submodule.Quotient.completeSpace`). Everything else — the
factorization `T = T̃ ∘ π`, Propositions 11.9–11.14 — is the backbone
`Numlib/Analysis/Normed/Module/Quotient`, stated there over `RCLike 𝕜` and read here at `ℝ`.

Conventions. The orthogonals `M^⊥ ⊆ E*`, `N^⊥ ⊆ E` of §1.3 are `Submodule.strongDualAnnihilator`
and `Submodule.strongDualCoannihilator` as chapter 1 reads them (`Chapter01.mem_orthogonal_iff`);
the adjoint `π*` of Proposition 11.9 and the restriction `T f = f|_M` of Proposition 11.10 are
chapter 2's Banach adjoint `ContinuousLinearMap.strongDualMap` of `π = M.mkQL` and of the
inclusion `M.subtypeL`; reflexivity and uniform convexity are chapter 3's Definitions
`Chapter03.IsReflexive`, `Chapter03.IsUniformlyConvex`; finite codimension and `codim` are
§11.1's `IsFiniteCodim` and `codim`. Every theorem takes the closedness of the subspace as the
instance argument `[IsClosed (M : Set E)]` the quotient norm needs, and the book's
`[CompleteSpace E]` where the book says "Banach", used or not.

## Main results

* `quotientNorm_eq_iInf`, `proposition_11_8` — the quotient norm, `‖π‖ ≤ 1`, completeness.
* `proposition_11_9`, `quotKerFactorization`, `proposition_11_10` — `(E/M)* ≅ M^⊥` through
  `π*`, the factorization `T = T̃ ∘ π` through `F/N(T)`, and `E*/M^⊥ ≅ M*`.
* `proposition_11_11`, `proposition_11_12` — the quotient of a reflexive (uniformly convex)
  space is reflexive (uniformly convex).
* `proposition_11_13_a`, `proposition_11_13_b`, `proposition_11_14`, `proposition_11_14_le` —
  `dim M = codim M^⊥`, `codim M = dim M^⊥`, `dim N = codim N^⊥`, `dim N^⊥ ≤ codim N`.

The book's example inside the proof of Proposition 11.14 of a strict inequality
`dim N^⊥ < codim N` (a hyperplane `N = ker ξ` with `ξ ∈ E** ∖ J(E)`) is not formalized.
-/

open Metric Module

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The quotient norm -/

/-- **The Definition paragraph of §11.2.** For a closed subspace `M` of `E`, the quotient norm
of the class `[x] = π(x)` is `‖[x]‖ = inf_{m ∈ M} ‖x − m‖`; the projection satisfies
`‖π(x)‖ ≤ ‖x‖`, so `π : E → E/M` is bounded with `‖π‖ ≤ 1`; and `‖[x]‖ = 0` forces `[x] = 0`
(this is where the closedness of `M` is used). -/
theorem quotientNorm_eq_iInf (M : Submodule ℝ E) [IsClosed (M : Set E)] (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = ⨅ m : M, ‖x - m‖ ∧ ‖M.mkQL x‖ ≤ ‖x‖ ∧ ‖M.mkQL‖ ≤ 1 ∧
      (‖(Submodule.Quotient.mk x : E ⧸ M)‖ = 0 → (Submodule.Quotient.mk x : E ⧸ M) = 0) := by
  refine ⟨?_, Submodule.Quotient.norm_mk_le M x, Submodule.opNorm_mkQL_le M,
    fun h => norm_eq_zero.1 h⟩
  have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = infDist x (M : Set E) :=
    QuotientAddGroup.norm_mk (S := M.toAddSubgroup) x
  rw [hnorm, infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

/-- **Proposition 11.8.** The quotient space `E/M` equipped with the quotient norm is a Banach
space. -/
theorem proposition_11_8 [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    CompleteSpace (E ⧸ M) :=
  inferInstance

/-! ### The dual of a quotient, and factorization through the kernel -/

/-- **Proposition 11.9.** Let `M` be a closed subspace of `E` and `π* : (E/M)* → E*` the adjoint
of `π : E → E/M` (`⟨π* ξ, x⟩ = ⟨ξ, π x⟩`). Then `R(π*) = M^⊥`; more precisely `π*` is bijective
from `(E/M)*` onto `M^⊥` with `‖π* ξ‖_{E*} = ‖ξ‖_{(E/M)*}` for all `ξ`. "In particular `(E/M)*`
is isomorphic and isometric to `M^⊥`": the backbone's isometry
`Submodule.strongDualQuotLIEAnnihilator M : (E/M)* ≃ₗᵢ[ℝ] M^⊥` is `π*` (last clause). -/
theorem proposition_11_9 (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (∀ (ξ : StrongDual ℝ (E ⧸ M)) (x : E), M.mkQL.strongDualMap ξ x = ξ (M.mkQL x)) ∧
      LinearMap.range (M.mkQL.strongDualMap : StrongDual ℝ (E ⧸ M) →ₗ[ℝ] StrongDual ℝ E) =
        M.strongDualAnnihilator ∧
      Function.Injective M.mkQL.strongDualMap ∧
      (∀ ξ : StrongDual ℝ (E ⧸ M), ‖M.mkQL.strongDualMap ξ‖ = ‖ξ‖) ∧
      ∀ ξ : StrongDual ℝ (E ⧸ M),
        (M.strongDualQuotLIEAnnihilator ξ : StrongDual ℝ E) = M.mkQL.strongDualMap ξ := by
  refine ⟨fun ξ x => rfl, ?_, fun ξ η h => M.strongDualQuotLIEAnnihilator.injective
    (Subtype.ext h), fun ξ => M.strongDualQuotLIEAnnihilator.norm_map ξ, fun ξ => rfl⟩
  ext f
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ξ, rfl⟩
    exact Submodule.comp_mkQL_mem_strongDualAnnihilator M ξ
  · intro hf
    obtain ⟨ξ, hξ⟩ := M.strongDualQuotLIEAnnihilator.surjective ⟨f, hf⟩
    exact ⟨ξ, congrArg Subtype.val hξ⟩

/-- **The factorization paragraph of §11.2.** Let `F`, `G` be Banach spaces and `T ∈ 𝓛(F, G)`.
The kernel `N(T)` is closed, and `T` factors as `T = T̃ ∘ π` through `π : F → F/N(T)`, where
`T̃ : F/N(T) → G` (`T̃ (π x) = T x`, Mathlib's `Submodule.liftQL`) is well defined, bijective
from `F/N(T)` onto `R(T)`, and `‖T̃‖ = ‖T‖` (the book prints `‖T‖ = ‖T‖`). -/
theorem quotKerFactorization {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (T : F →L[ℝ] G) :
    IsClosed (T.ker : Set F) ∧ (∀ x, T.ker.liftQL T le_rfl (T.ker.mkQL x) = T x) ∧
      Function.Injective (T.ker.liftQL T le_rfl) ∧
      Set.range (T.ker.liftQL T le_rfl) = Set.range T ∧ ‖T.ker.liftQL T le_rfl‖ = ‖T‖ := by
  refine ⟨T.isClosed_ker, fun x => rfl, Submodule.injective_liftQL_ker T, ?_,
    Submodule.opNorm_liftQL T le_rfl⟩
  have h := Submodule.range_liftQL T le_rfl
  rw [SetLike.ext'_iff] at h
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using h

/-- **Proposition 11.10.** For any Banach space `E` and closed subspace `M`, let
`T : E* → M*`, `T f = f|_M` (the adjoint of the inclusion `M ⊆ E`). Then `N(T) = M^⊥`, by
Hahn–Banach `R(T) = M*`, and the induced operator `T̃ : E*/M^⊥ → M*` (`T̃ ∘ π = T`) is a
bijective isometry from `E*/M^⊥` onto `M*`. -/
theorem proposition_11_10 [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (∀ (f : StrongDual ℝ E) (x : M), M.subtypeL.strongDualMap f x = f x) ∧
      M.subtypeL.strongDualMap.ker = M.strongDualAnnihilator ∧
      Function.Surjective M.subtypeL.strongDualMap ∧
      ∃ e : (StrongDual ℝ E ⧸ M.strongDualAnnihilator) ≃ₗᵢ[ℝ] StrongDual ℝ M,
        ∀ f : StrongDual ℝ E, e (Submodule.Quotient.mk f) = M.subtypeL.strongDualMap f := by
  refine ⟨fun f x => rfl, Submodule.ker_comp_subtypeL_eq_strongDualAnnihilator M, fun g => ?_,
    ⟨M.quotAnnihilatorLIEStrongDual, fun f => rfl⟩⟩
  obtain ⟨f, hf, -⟩ := Chapter01.corollary_1_2 M g
  exact ⟨f, ContinuousLinearMap.ext hf⟩

/-! ### Reflexivity and uniform convexity of a quotient -/

/-- **Proposition 11.11.** Assume that `E` is a reflexive Banach space and `M` is a closed
subspace. Then `E/M` is reflexive. (The backbone proves it directly through Proposition 11.9
and Hahn–Banach rather than through Corollary 3.21 and Proposition 3.20 as the book does.) -/
theorem proposition_11_11 [CompleteSpace E] (hE : Chapter03.IsReflexive E) (M : Submodule ℝ E)
    [IsClosed (M : Set E)] : Chapter03.IsReflexive (E ⧸ M) :=
  have := Chapter03.isReflexive_iff.1 hE
  Chapter03.isReflexive_iff.2 inferInstance

/-- **Proposition 11.12.** Assume that `E` is a uniformly convex Banach space and `M` is a
closed subspace. Then `E/M` is uniformly convex. (The book picks representatives in the closed
unit ball by Corollary 3.23 and Milman–Pettis; the backbone uses representatives in the ball of
radius `1 + η` and needs neither.) -/
theorem proposition_11_12 [CompleteSpace E] (hE : Chapter03.IsUniformlyConvex E)
    (M : Submodule ℝ E) [IsClosed (M : Set E)] : Chapter03.IsUniformlyConvex (E ⧸ M) :=
  have := Chapter03.uniformlyConvex_iff.1 hE
  Chapter03.uniformlyConvex_iff.2 inferInstance

/-! ### Dimension and codimension -/

/-- **Proposition 11.13 (a).** Let `E` be a Banach space and `M ⊆ E` a closed subspace. Then
`dim M < ∞` if and only if `codim M^⊥ < ∞`, and in that case `dim M = codim M^⊥`. -/
theorem proposition_11_13_a [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (FiniteDimensional ℝ M ↔ IsFiniteCodim M.strongDualAnnihilator) ∧
      (FiniteDimensional ℝ M → finrank ℝ M = codim M.strongDualAnnihilator) :=
  ⟨M.finiteDimensional_iff_coFG_strongDualAnnihilator.trans (isFiniteCodim_iff_coFG _).symm,
    fun _ => M.finrank_eq_finrank_quotient_strongDualAnnihilator⟩

/-- **Proposition 11.13 (b).** Let `E` be a Banach space and `M ⊆ E` a closed subspace. Then
`codim M < ∞` if and only if `dim M^⊥ < ∞`, and in that case `codim M = dim M^⊥`. -/
theorem proposition_11_13_b [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (IsFiniteCodim M ↔ FiniteDimensional ℝ M.strongDualAnnihilator) ∧
      (IsFiniteCodim M → codim M = finrank ℝ M.strongDualAnnihilator) :=
  ⟨(isFiniteCodim_iff_coFG M).trans M.coFG_iff_finiteDimensional_strongDualAnnihilator,
    fun _ => M.finrank_quotient_eq_finrank_strongDualAnnihilator⟩

/-- **Proposition 11.14, first sentence.** Let `N ⊆ E*` be a closed subspace. Then `dim N < ∞`
if and only if `codim N^⊥ < ∞`, and in that case `dim N = codim N^⊥`. (The claim `N^⊥⊥ = N`
for finite-dimensional `N` inside the book's proof, by Lemma 3.2, is the backbone's
`Submodule.strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional`.) -/
theorem proposition_11_14 [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [IsClosed (N : Set (StrongDual ℝ E))] :
    (FiniteDimensional ℝ N ↔ IsFiniteCodim N.strongDualCoannihilator) ∧
      (FiniteDimensional ℝ N → finrank ℝ N = codim N.strongDualCoannihilator) :=
  ⟨N.finiteDimensional_iff_coFG_strongDualCoannihilator.trans (isFiniteCodim_iff_coFG _).symm,
    fun _ => N.finrank_eq_finrank_quotient_strongDualCoannihilator⟩

/-- **Proposition 11.14, second sentence.** "It is also true that `dim N^⊥ ≤ codim N`": for a
closed subspace `N ⊆ E*` of finite codimension, `N^⊥` is finite-dimensional and
`dim N^⊥ ≤ codim N`. The book's example showing that the inequality may be strict
(`dim N^⊥ < codim N < ∞`) is not formalized. -/
theorem proposition_11_14_le [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [IsClosed (N : Set (StrongDual ℝ E))] (hN : IsFiniteCodim N) :
    FiniteDimensional ℝ N.strongDualCoannihilator ∧
      finrank ℝ N.strongDualCoannihilator ≤ codim N :=
  have := (isFiniteCodim_iff_coFG N).1 hN
  ⟨N.finiteDimensional_strongDualCoannihilator_of_coFG,
    N.finrank_strongDualCoannihilator_le_finrank_quotient⟩

end Brezis.Chapter11
