/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Quotient
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter03.Section07
import NumlibSurface.Brezis.Chapter11.Section01

/-!
# Brezis, Section 11.2: Quotient spaces

This module formalizes Section 11.2 of [brezis2011functional]: the quotient $E/M$ of a real Banach
space $E$ by a closed subspace $M$. The class of $x \in E$ is $[x] = \pi(x)$, where
$\pi : E \to E/M$ is the canonical projection, and the quotient norm is
$\|[x]\| = \inf_{m \in M} \|x - m\|$. With this norm $E/M$ is a Banach space (Proposition 11.8). The
dual of $E/M$ is isometric to the orthogonal $M^\perp \subseteq E^*$ through the adjoint $\pi^*$
(Proposition 11.9), and $E^*/M^\perp$ is isometric to $M^*$ (Proposition 11.10). An operator
$T \in \mathcal{L}(F, G)$ factors as $T = \tilde{T} \circ \pi$ through $F/N(T)$. A quotient of a
reflexive (uniformly convex) space is reflexive (uniformly convex) (Propositions 11.11 and 11.12).
Finally, the dimension and the codimension of a closed subspace and of its orthogonal are related
(Propositions 11.13 and 11.14).

The quotient space, its norm, the bound $\|\pi\| \le 1$ and Proposition 11.8 come from Mathlib's
normed quotient: `Submodule.Quotient.normedAddCommGroup`, `Submodule.Quotient.normedSpace`,
`Submodule.mkQL`, `QuotientAddGroup.norm_mk` and `Submodule.Quotient.completeSpace`. The other
results specialize the backbone module `Numlib.Analysis.Normed.Module.Quotient`, which is stated
over `RCLike 𝕜`, at $\mathbb{R}$.

## Main definitions

* Section 11.2, definition of the quotient norm, `Brezis.Chapter11.quotientNorm_eq_iInf`:
  $\|[x]\| = \inf_{m \in M} \|x - m\|$, with $\|\pi\| \le 1$ and $\|[x]\| = 0 \Rightarrow [x] = 0$.

## Main results

* Proposition 11.8, `Brezis.Chapter11.proposition_11_8`: $E/M$ with the quotient norm is a Banach
  space.
* Proposition 11.9, `Brezis.Chapter11.proposition_11_9`: the adjoint $\pi^*$ is an isometric
  bijection from $(E/M)^*$ onto $M^\perp$.
* Section 11.2, factorization through the kernel, `Brezis.Chapter11.quotKerFactorization`:
  $T = \tilde{T} \circ \pi$, where $\tilde{T}$ is a bijection from $F/N(T)$ onto $R(T)$ with
  $\|\tilde{T}\| = \|T\|$.
* Proposition 11.10, `Brezis.Chapter11.proposition_11_10`: the restriction map $E^* \to M^*$ has
  kernel $M^\perp$, is surjective, and induces an isometric isomorphism $E^*/M^\perp \cong M^*$.
* Proposition 11.11, `Brezis.Chapter11.proposition_11_11`: a quotient of a reflexive Banach space by
  a closed subspace is reflexive.
* Proposition 11.12, `Brezis.Chapter11.proposition_11_12`: a quotient of a uniformly convex Banach
  space by a closed subspace is uniformly convex.
* Proposition 11.13(a), `Brezis.Chapter11.proposition_11_13_a`: $\dim M < \infty$ if and only if
  $\operatorname{codim} M^\perp < \infty$, and then $\dim M = \operatorname{codim} M^\perp$.
* Proposition 11.13(b), `Brezis.Chapter11.proposition_11_13_b`: $\operatorname{codim} M < \infty$ if
  and only if $\dim M^\perp < \infty$, and then $\operatorname{codim} M = \dim M^\perp$.
* Proposition 11.14, `Brezis.Chapter11.proposition_11_14`: for a closed subspace $N \subseteq E^*$,
  $\dim N < \infty$ if and only if $\operatorname{codim} N^\perp < \infty$, and then
  $\dim N = \operatorname{codim} N^\perp$.
* Proposition 11.14, `Brezis.Chapter11.proposition_11_14_le`: if $N \subseteq E^*$ is closed and has
  finite codimension, then $\dim N^\perp \le \operatorname{codim} N$.

## Conventions

* The orthogonals $M^\perp \subseteq E^*$ and $N^\perp \subseteq E$ of Section 1.3 are
  `Submodule.strongDualAnnihilator` and `Submodule.strongDualCoannihilator`, as in
  `Brezis.Chapter01.mem_orthogonal_iff`.
* The adjoint $\pi^*$ of Proposition 11.9 and the restriction $Tf = f|_M$ of Proposition 11.10 are
  the Banach adjoints `ContinuousLinearMap.strongDualMap` of Chapter 2, applied to $\pi$, which is
  `M.mkQL`, and to the inclusion of $M$ in $E$, which is `M.subtypeL`.
* Reflexivity and uniform convexity are the definitions `Brezis.Chapter03.IsReflexive` and
  `Brezis.Chapter03.IsUniformlyConvex` of Chapter 3. Finite codimension and the codimension are
  `Brezis.Chapter11.IsFiniteCodim` and `Brezis.Chapter11.codim` of Section 11.1.

## Implementation notes

* Every theorem takes the closedness of the subspace as the instance argument
  `[IsClosed (M : Set E)]`, which the quotient norm needs.
* Every theorem takes `[CompleteSpace E]` where the source says "Banach space", whether or not the
  proof uses it.

## Deviations from the source

* **Quotient norm and Proposition 11.9** (generalization). The norm formula and the isometric
  identification of the quotient dual with the annihilator also apply in incomplete normed
  spaces.
* **Proposition 11.14, codimension inequality** (restriction). The source allows an infinite
  codimension on the right. Lean proves the inequality for finite codimension, since its
  natural-valued codimension is zero for infinite-dimensional quotients.

## Not formalized

* **Example in the proof of Proposition 11.14.** The example of a strict inequality
  $\dim N^\perp < \operatorname{codim} N$, with a hyperplane $N = \ker \xi$ for
  $\xi \in E^{**} \setminus J(E)$.
-/

open Metric Module

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The quotient norm -/

/-- **Section 11.2** of [brezis2011functional], definition of the quotient norm. Let $M$ be a closed
subspace of $E$, and let $\pi : E \to E/M$, $\pi(x) = [x]$, be the canonical projection. For
every $x \in E$, $$\|[x]\| = \inf_{m \in M} \|x - m\|,$$ and $\|\pi(x)\| \le \|x\|$, so that
$\pi$ is bounded with $\|\pi\| \le 1$. Moreover $\|[x]\| = 0$ implies $[x] = 0$.

The last clause is the place where the closedness of $M$ is used. The projection $\pi$ is
`M.mkQL`, and the infimum runs over the elements of the subtype `M`.

**Reading.** The source assumes a Banach space. The norm and projection statements only need a
normed space and closedness of the subspace. -/
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

/-- **Proposition 11.8** of [brezis2011functional]. Let $E$ be a Banach space and let $M$ be a
closed subspace of $E$. Then the quotient space $E/M$ with the quotient norm is a Banach space.

The proof is Mathlib's `Submodule.Quotient.completeSpace`. -/
theorem proposition_11_8 [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    CompleteSpace (E ⧸ M) :=
  inferInstance

/-! ### The dual of a quotient, and factorization through the kernel -/

/-- **Proposition 11.9** of [brezis2011functional]. Let $M$ be a closed subspace of $E$, and let
$\pi^* : (E/M)^* \to E^*$ be the adjoint of $\pi : E \to E/M$, that is, $\langle \pi^* \xi, x
\rangle = \langle \xi, \pi x \rangle$ for all $\xi \in (E/M)^*$ and $x \in E$. Then
$R(\pi^*) = M^\perp$, the map $\pi^*$ is injective, and $$\|\pi^* \xi\|_{E^*} =
\|\xi\|_{(E/M)^*} \quad \text{for all } \xi \in (E/M)^*.$$ Thus $\pi^*$ is an isometric
bijection from $(E/M)^*$ onto $M^\perp$, and "in particular $(E/M)^*$ is isomorphic and
isometric to $M^\perp$".

The last conjunct says that the backbone isometry `Submodule.strongDualQuotLIEAnnihilator M`,
from $(E/M)^*$ onto $M^\perp$, is the map $\pi^*$.

**Reading.** The standing Banach assumption of the source is relaxed to a normed space. -/
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

/-- **Section 11.2** of [brezis2011functional], factorization through the kernel. Let $F$ and $G$ be
Banach spaces and let $T \in \mathcal{L}(F, G)$. Then the kernel $N(T)$ is closed, and
$T = \tilde{T} \circ \pi$, where $\pi : F \to F/N(T)$ is the canonical projection and
$\tilde{T} : F/N(T) \to G$, $\tilde{T}(\pi x) = Tx$. The map $\tilde{T}$ is injective,
$R(\tilde{T}) = R(T)$, and $\|\tilde{T}\| = \|T\|$.

The operator $\tilde{T}$ is Mathlib's `Submodule.liftQL` for $N(T)$ = `T.ker`. -/
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

/-- **Proposition 11.10** of [brezis2011functional]. Let $E$ be a Banach space and let $M$ be a
closed subspace of $E$. Let $T : E^* \to M^*$ be the restriction $Tf = f|_M$. Then
$N(T) = M^\perp$, and $T$ is surjective, that is, $R(T) = M^*$. Moreover there is an isometric
isomorphism $\tilde{T} : E^*/M^\perp \to M^*$ with $\tilde{T}([f]) = Tf$ for all $f \in E^*$.

The restriction $T$ is the adjoint of the inclusion $M \subseteq E$, `M.subtypeL.strongDualMap`;
the first conjunct says that it is the restriction. The surjectivity is the Hahn–Banach theorem. -/
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

/-- **Proposition 11.11** of [brezis2011functional]. Let $E$ be a reflexive Banach space and let $M$
be a closed subspace of $E$. Then $E/M$ is reflexive.

The source proves this with Corollary 3.21 and Proposition 3.20. The backbone proof uses
Proposition 11.9 and the Hahn–Banach theorem instead. -/
theorem proposition_11_11 [CompleteSpace E] (hE : Chapter03.IsReflexive E) (M : Submodule ℝ E)
    [IsClosed (M : Set E)] : Chapter03.IsReflexive (E ⧸ M) :=
  have := Chapter03.isReflexive_iff.1 hE
  Chapter03.isReflexive_iff.2 inferInstance

/-- **Proposition 11.12** of [brezis2011functional]. Let $E$ be a uniformly convex Banach space and
let $M$ be a closed subspace of $E$. Then $E/M$ is uniformly convex.

The source picks representatives in the closed unit ball with Corollary 3.23 and the
Milman–Pettis theorem. The backbone proof picks representatives in the ball of radius $1 + \eta$
and needs neither result. -/
theorem proposition_11_12 [CompleteSpace E] (hE : Chapter03.IsUniformlyConvex E)
    (M : Submodule ℝ E) [IsClosed (M : Set E)] : Chapter03.IsUniformlyConvex (E ⧸ M) :=
  have := Chapter03.uniformlyConvex_iff.1 hE
  Chapter03.uniformlyConvex_iff.2 inferInstance

/-! ### Dimension and codimension -/

/-- **Proposition 11.13(a)** of [brezis2011functional]. Let $E$ be a Banach space and let
$M \subseteq E$ be a closed subspace. Then $\dim M < \infty$ if and only if
$\operatorname{codim} M^\perp < \infty$, and in that case $$\dim M = \operatorname{codim}
M^\perp.$$

Here $M^\perp \subseteq E^*$ is `M.strongDualAnnihilator`, and
"$\operatorname{codim} M^\perp < \infty$" is `Brezis.Chapter11.IsFiniteCodim`. -/
theorem proposition_11_13_a [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (FiniteDimensional ℝ M ↔ IsFiniteCodim M.strongDualAnnihilator) ∧
      (FiniteDimensional ℝ M → finrank ℝ M = codim M.strongDualAnnihilator) :=
  ⟨M.finiteDimensional_iff_coFG_strongDualAnnihilator.trans (isFiniteCodim_iff_coFG _).symm,
    fun _ => M.finrank_eq_finrank_quotient_strongDualAnnihilator⟩

/-- **Proposition 11.13(b)** of [brezis2011functional]. Let $E$ be a Banach space and let
$M \subseteq E$ be a closed subspace. Then $\operatorname{codim} M < \infty$ if and only if
$\dim M^\perp < \infty$, and in that case $$\operatorname{codim} M = \dim M^\perp.$$

Here $M^\perp \subseteq E^*$ is `M.strongDualAnnihilator`. -/
theorem proposition_11_13_b [CompleteSpace E] (M : Submodule ℝ E) [IsClosed (M : Set E)] :
    (IsFiniteCodim M ↔ FiniteDimensional ℝ M.strongDualAnnihilator) ∧
      (IsFiniteCodim M → codim M = finrank ℝ M.strongDualAnnihilator) :=
  ⟨(isFiniteCodim_iff_coFG M).trans M.coFG_iff_finiteDimensional_strongDualAnnihilator,
    fun _ => M.finrank_quotient_eq_finrank_strongDualAnnihilator⟩

/-- **Proposition 11.14** of [brezis2011functional], first sentence. Let $E$ be a Banach space and
let $N \subseteq E^*$ be a closed subspace. Then $\dim N < \infty$ if and only if
$\operatorname{codim} N^\perp < \infty$, and in that case $$\dim N = \operatorname{codim}
N^\perp.$$

Here $N^\perp \subseteq E$ is `N.strongDualCoannihilator`. The proof of the source uses
$N^{\perp\perp} = N$ for a finite-dimensional $N$, by Lemma 3.2; this is the backbone theorem
`Submodule.strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional`. -/
theorem proposition_11_14 [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [IsClosed (N : Set (StrongDual ℝ E))] :
    (FiniteDimensional ℝ N ↔ IsFiniteCodim N.strongDualCoannihilator) ∧
      (FiniteDimensional ℝ N → finrank ℝ N = codim N.strongDualCoannihilator) :=
  ⟨N.finiteDimensional_iff_coFG_strongDualCoannihilator.trans (isFiniteCodim_iff_coFG _).symm,
    fun _ => N.finrank_eq_finrank_quotient_strongDualCoannihilator⟩

/-- **Proposition 11.14** of [brezis2011functional], second sentence. Let $E$ be a Banach space and
let $N \subseteq E^*$ be a closed subspace of finite codimension. Then $N^\perp$ is
finite-dimensional and $$\dim N^\perp \le \operatorname{codim} N.$$

The example of the source that shows that the inequality can be strict,
$\dim N^\perp < \operatorname{codim} N < \infty$, is not formalized.

**Reading.** The source allows infinite codimension on the right. Lean assumes finite codimension
to express the bound with natural-valued dimensions. -/
theorem proposition_11_14_le [CompleteSpace E] (N : Submodule ℝ (StrongDual ℝ E))
    [IsClosed (N : Set (StrongDual ℝ E))] (hN : IsFiniteCodim N) :
    FiniteDimensional ℝ N.strongDualCoannihilator ∧
      finrank ℝ N.strongDualCoannihilator ≤ codim N :=
  have := (isFiniteCodim_iff_coFG N).1 hN
  ⟨N.finiteDimensional_strongDualCoannihilator_of_coFG,
    N.finrank_strongDualCoannihilator_le_finrank_quotient⟩

end Brezis.Chapter11
