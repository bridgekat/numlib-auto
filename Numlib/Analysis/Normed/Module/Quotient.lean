/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural homes: `Mathlib.Analysis.Normed.Group.Quotient` (the lift and the uniformly convex
quotient) and `Mathlib.Analysis.Normed.Module.Dual` (the duals of quotients and subspaces).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.FiniteCodim

/-!
# The normed quotient of a normed space by a subspace

Let $E$ be a normed space and $M$ a closed subspace of $E$. The quotient $E / M$ with the quotient
norm $\|[x]\| = \operatorname{dist}(x, M)$ is a normed space, and $\pi \colon E \to E/M$ denotes the
projection. For a subspace $M \subseteq E$ the **annihilator** is
$M^\perp = \{f \in E^* : f = 0 \text{ on } M\}$, and for a subspace $N \subseteq E^*$ it is
$N^\perp = \{x \in E : f(x) = 0 \text{ for all } f \in N\}$. This file adds to the Mathlib quotient
what §11.2 of [brezis2011functional] proves about it: the factorization $T = \tilde T \circ \pi$ of
an operator through a quotient, the isometric isomorphisms $(E/M)^* \cong M^\perp$ and
$E^*/M^\perp \cong M^*$, the reflexivity and uniform convexity of a quotient, and the relations
between dimension and codimension of a subspace and of its annihilator.

## Main definitions

* `Submodule.strongDualQuotLIEAnnihilator`: the isometric isomorphism $(E/M)^* \cong M^\perp$,
  $\xi \mapsto \xi \circ \pi$ (Proposition 11.9 of [brezis2011functional]).
* `Submodule.quotAnnihilatorLIEStrongDual`: the isometric isomorphism $E^*/M^\perp \cong M^*$,
  $[f] \mapsto f|_M$ (Proposition 11.10 of [brezis2011functional]).

## Main results

* `Submodule.opNorm_liftQL`: the lift $\tilde T \colon E/M \to F$ of an operator $T \colon E \to F$
  that vanishes on $M$ has $\|\tilde T\| = \|T\|$.
* `Submodule.injective_liftQL_ker` and `Submodule.range_liftQL`: the lift through $E / \ker T$ is a
  bijection onto the range of $T$.
* `Submodule.Quotient.instIsReflexive`: a quotient of a reflexive space by a closed subspace is
  reflexive (Proposition 11.11 of [brezis2011functional]).
* `Submodule.Quotient.uniformConvexSpace` and `Submodule.Quotient.instUniformConvexSpace`: a
  quotient of a uniformly convex space is uniformly convex (Proposition 11.12 of
  [brezis2011functional]).
* `Submodule.finiteDimensional_iff_coFG_strongDualAnnihilator` and
  `Submodule.finrank_eq_finrank_quotient_strongDualAnnihilator`: $\dim M < \infty$ if and only if
  $\operatorname{codim} M^\perp < \infty$, and $\dim M = \operatorname{codim} M^\perp$ (Proposition
  11.13(a)).
* `Submodule.coFG_iff_finiteDimensional_strongDualAnnihilator` and
  `Submodule.finrank_quotient_eq_finrank_strongDualAnnihilator`: for a closed $M$,
  $\operatorname{codim} M < \infty$ if and only if $\dim M^\perp < \infty$, and
  $\operatorname{codim} M = \dim M^\perp$ (Proposition 11.13(b)).
* `Submodule.strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional`:
  $(N^\perp)^\perp = N$ for a finite-dimensional subspace $N$ of $E^*$; this is the key to
  Proposition 11.14.
* `Submodule.finiteDimensional_iff_coFG_strongDualCoannihilator` and
  `Submodule.finrank_eq_finrank_quotient_strongDualCoannihilator`: for a subspace $N$ of $E^*$,
  $\dim N < \infty$ if and only if $\operatorname{codim} N^\perp < \infty$, and
  $\dim N = \operatorname{codim} N^\perp$ (Proposition 11.14).
* `Submodule.finiteDimensional_strongDualCoannihilator_of_coFG` and
  `Submodule.finrank_strongDualCoannihilator_le_finrank_quotient`: if $N \subseteq E^*$ has finite
  codimension, then $\dim N^\perp \le \operatorname{codim} N$ (Proposition 11.14).

## Proof outline

The proofs of Propositions 11.11 and 11.12 in [brezis2011functional] use Corollary 3.21 ($E$ is
reflexive if and only if $E^*$ is reflexive) and Corollary 3.23 with the Milman–Pettis theorem. Both
are avoided here. Reflexivity of the quotient is proved directly: a functional on $(E/M)^*$ is a
functional on $M^\perp$, it extends to an element of $E^{**}$ by the Hahn–Banach theorem, this
element is represented by some $x \in E$ because $E$ is reflexive, and the functional is then the
evaluation at $[x]$. Uniform convexity is proved with representatives of norm less than $1 + \eta$
in place of the representatives of norm at most $1$ of [brezis2011functional], at the price of a
slightly smaller modulus of convexity.

## Implementation notes

* The quotient is the Mathlib one: `Submodule.Quotient.normedAddCommGroup` (under the instance
  argument `[IsClosed (M : Set E)]`), `Submodule.Quotient.normedSpace` and
  `Submodule.Quotient.completeSpace`, with the projection `Submodule.mkQL`, the bounds
  `Submodule.Quotient.norm_mk_le` and `QuotientAddGroup.norm_mk`, the representatives of almost
  minimal norm `Submodule.Quotient.norm_mk_lt`, and the lift `Submodule.liftQL`.
* The annihilators are `Submodule.strongDualAnnihilator` and `Submodule.strongDualCoannihilator` of
  `Numlib.Analysis.Normed.Module.Annihilator`. The annihilator $M^\perp$ is closed, and this is the
  instance `Submodule.instIsClosedStrongDualAnnihilator`, so that $E^*/M^\perp$ is a normed space by
  instance search.
* Finite codimension is the Mathlib predicate `Submodule.CoFG`, and the codimension of $M$ is
  `Module.finrank 𝕜 (E ⧸ M)`. A `Module.finrank` is $0$ for an infinite-dimensional space.
* The scalars are `RCLike 𝕜` where the Hahn–Banach theorem is used (Propositions 11.10, 11.11, 11.13
  and 11.14), and a nontrivially normed field elsewhere (the factorization and Proposition 11.9).
  The quotient $E/M$ has the hypothesis `[IsClosed (M : Set E)]` wherever it must be a normed space
  and not only a seminormed space.
* Uniform convexity is a statement about the real structure, so the general theorem assumes
  `[NormedSpace ℝ E]`, and the instance is over `RCLike 𝕜`, where the real structure is
  `NormedSpace.restrictScalars`.
-/

open Metric Module

noncomputable section

namespace Submodule

/-! ### The factorization $T = \tilde T \circ \pi$ -/

section Lift

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Let $M$ be a subspace of a seminormed space $E$. The projection $\pi \colon E \to E/M$ has
operator norm at most $1$. -/
theorem opNorm_mkQL_le (M : Submodule 𝕜 E) : ‖M.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    simpa using Submodule.Quotient.norm_mk_le M y

/-- Let $M$ be a subspace of a seminormed space $E$, and let $f \colon E \to F$ be a bounded
operator that vanishes on $M$. Then $\|f(x)\| \le \|f\| \, \|[x]\|$ for every $x \in E$, where
$[x]$ is the class of $x$ in $E/M$.

This holds because $f(x) = f(x - m)$ for every $m \in M$. -/
theorem norm_apply_le_opNorm_mul_norm_mk {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker)
    (x : E) : ‖f x‖ ≤ ‖f‖ * ‖(Submodule.Quotient.mk x : E ⧸ M)‖ := by
  have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = infDist x (M : Set E) :=
    QuotientAddGroup.norm_mk (S := M.toAddSubgroup) x
  rw [hnorm, infDist_eq_iInf, Real.mul_iInf_of_nonneg (norm_nonneg f)]
  have : Nonempty (M : Set E) := ⟨⟨0, M.zero_mem⟩⟩
  refine le_ciInf fun z => ?_
  have hz : f z = 0 := h z.2
  rw [dist_eq_norm, ← sub_zero (f x), ← hz, ← map_sub]
  exact f.le_opNorm _

/-- Let $M$ be a subspace of a seminormed space $E$, and let $f \colon E \to F$ be a bounded
operator that vanishes on $M$. Then the lift $\tilde f \colon E/M \to F$, with
$f = \tilde f \circ \pi$, has the same operator norm: $\|\tilde f\| = \|f\|$. This is stated in
the factorization paragraph of §11.2 of [brezis2011functional].

[brezis2011functional] prints $\|T\| = \|T\|$, a misprint for $\|\tilde T\| = \|T\|$. The lift
is `M.liftQL f h`. The bound $\le$ holds because $\|f(x)\| \le \|f\| \, \|[x]\|$, and $\ge$
holds because $f = \tilde f \circ \pi$ and $\|\pi\| \le 1$. -/
theorem opNorm_liftQL {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker) :
    ‖M.liftQL f h‖ = ‖f‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun x => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    exact norm_apply_le_opNorm_mul_norm_mk f h y
  · calc ‖f‖ = ‖(M.liftQL f h).comp M.mkQL‖ := congrArg norm (by ext; rfl)
      _ ≤ ‖M.liftQL f h‖ * ‖M.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖M.liftQL f h‖ * 1 := by gcongr; exact opNorm_mkQL_le M
      _ = ‖M.liftQL f h‖ := mul_one _

/-- Let $M$ be a subspace of a seminormed space $E$, and let $f \colon E/M \to F$ be a bounded
operator. Then the lift of $f \circ \pi$ through $E/M$ is $f$. -/
theorem liftQL_comp_mkQL (M : Submodule 𝕜 E) (f : E ⧸ M →L[𝕜] F) (h : M ≤ (f.comp M.mkQL).ker) :
    M.liftQL (f.comp M.mkQL) h = f := by
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
  rfl

/-- Let $M$ be a subspace of a seminormed space $E$, and let $f \colon E \to F$ be a bounded
operator that vanishes on $M$. Then the lift $\tilde f \colon E/M \to F$ has the same range as
$f$. -/
theorem range_liftQL {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker) :
    LinearMap.range (M.liftQL f h : E ⧸ M →ₗ[𝕜] F) = LinearMap.range (f : E →ₗ[𝕜] F) :=
  range_liftQ M (f : E →ₗ[𝕜] F) h

/-- Let $f \colon E \to F$ be a bounded operator between seminormed spaces. Then the lift
$\tilde f \colon E / \ker f \to F$ of $f$ is injective. With `Submodule.range_liftQL`,
$\tilde f$ is a bijection of $E / N(f)$ onto $R(f)$, as in the factorization paragraph of §11.2
of [brezis2011functional]. -/
theorem injective_liftQL_ker (f : E →L[𝕜] F) : Function.Injective (f.ker.liftQL f le_rfl) :=
  LinearMap.ker_eq_bot.1 (ker_liftQ_eq_bot f.ker (f : E →ₗ[𝕜] F) le_rfl le_rfl)

end Lift

/-! ### The dual of a quotient -/

section DualQuotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $M$ be a subspace of a normed space $E$, and let $\xi \in (E/M)^*$. Then $\xi \circ \pi$
lies in the annihilator $M^\perp$. -/
theorem comp_mkQL_mem_strongDualAnnihilator (M : Submodule 𝕜 E) (ξ : StrongDual 𝕜 (E ⧸ M)) :
    ξ.comp M.mkQL ∈ M.strongDualAnnihilator :=
  mem_strongDualAnnihilator.2 fun x hx => by
    rw [ContinuousLinearMap.comp_apply, mkQL_apply, mkQ_apply,
      (Submodule.Quotient.mk_eq_zero M).2 hx, map_zero]

/-- Let $M$ be a closed subspace of a normed space $E$ over a nontrivially normed field. Then
$\xi \mapsto \xi \circ \pi$ is an isometric isomorphism of the dual $(E/M)^*$ onto the
annihilator $M^\perp$. This is Proposition 11.9 of [brezis2011functional].

The inverse map lifts $f \in M^\perp$ through the quotient (`Submodule.liftQL`). The norm is
preserved because $\|\xi \circ \pi\| \le \|\xi\| \, \|\pi\| \le \|\xi\|$, while $\xi$ is the
lift of $\xi \circ \pi$ (`Submodule.opNorm_liftQL`). The Hahn–Banach theorem is not needed. This
is the normed version of the Mathlib equivalence `Submodule.dualQuotEquivDualAnnihilator` for
the algebraic dual. -/
def strongDualQuotLIEAnnihilator (M : Submodule 𝕜 E) [IsClosed (M : Set E)] :
    StrongDual 𝕜 (E ⧸ M) ≃ₗᵢ[𝕜] M.strongDualAnnihilator :=
  LinearIsometryEquiv.ofSurjective
    { toFun := fun ξ => ⟨ξ.comp M.mkQL, comp_mkQL_mem_strongDualAnnihilator M ξ⟩
      map_add' := fun ξ η => Subtype.ext (ContinuousLinearMap.add_comp _ _ _)
      map_smul' := fun c ξ => Subtype.ext (ContinuousLinearMap.smul_comp _ _ _)
      norm_map' := fun ξ => by
        change ‖ξ.comp M.mkQL‖ = ‖ξ‖
        refine le_antisymm ?_ ?_
        · calc ‖ξ.comp M.mkQL‖ ≤ ‖ξ‖ * ‖M.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ ‖ξ‖ * 1 := by gcongr; exact opNorm_mkQL_le M
            _ = ‖ξ‖ := mul_one _
        · have h : M ≤ (ξ.comp M.mkQL).ker := fun x hx =>
            comp_mkQL_mem_strongDualAnnihilator M ξ |> mem_strongDualAnnihilator.1 |> (· x hx)
          rw [← opNorm_liftQL (ξ.comp M.mkQL) h, liftQL_comp_mkQL] }
    fun f => ⟨M.liftQL (f : StrongDual 𝕜 E) fun x hx => mem_strongDualAnnihilator.1 f.2 x hx,
      Subtype.ext (by ext; rfl)⟩

/-- Let $M$ be a closed subspace of a normed space $E$, and let $\xi \in (E/M)^*$. The image of
$\xi$ under `Submodule.strongDualQuotLIEAnnihilator`, as an element of $E^*$, is
$\xi \circ \pi$. So $\langle \pi^* \xi, x \rangle = \langle \xi, \pi x \rangle$, the defining
relation of the adjoint of $\pi$ in Proposition 11.9 of [brezis2011functional].

The functional `ContinuousLinearMap.strongDualMap M.mkQL ξ` is the same functional. -/
@[simp]
theorem strongDualQuotLIEAnnihilator_apply (M : Submodule 𝕜 E) [IsClosed (M : Set E)]
    (ξ : StrongDual 𝕜 (E ⧸ M)) :
    (M.strongDualQuotLIEAnnihilator ξ : StrongDual 𝕜 E) = ξ.comp M.mkQL :=
  rfl

/-- Let $M$ be a closed subspace of a normed space $E$, and let $f \in M^\perp$. The inverse of
`Submodule.strongDualQuotLIEAnnihilator` sends $f$ to the lift of $f$ through $E/M$. -/
theorem strongDualQuotLIEAnnihilator_symm_apply (M : Submodule 𝕜 E) [IsClosed (M : Set E)]
    (f : M.strongDualAnnihilator) :
    M.strongDualQuotLIEAnnihilator.symm f =
      M.liftQL (f : StrongDual 𝕜 E) fun x hx => mem_strongDualAnnihilator.1 f.2 x hx :=
  (LinearIsometryEquiv.symm_apply_eq _).mpr rfl

end DualQuotient

/-! ### The dual of a subspace -/

section DualSubspace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $M$ be a subspace of a normed space $E$. The kernel of the restriction map $E^* \to M^*$,
$f \mapsto f|_M$, is the annihilator $M^\perp$. This is stated in §11.2 of
[brezis2011functional], in the paragraph before Proposition 11.10.

The restriction map is `ContinuousLinearMap.precomp 𝕜 M.subtypeL`. -/
theorem ker_comp_subtypeL_eq_strongDualAnnihilator (M : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜 M.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 M).ker =
      M.strongDualAnnihilator := by
  ext f
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_strongDualAnnihilator,
    ContinuousLinearMap.ext_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

end DualSubspace

section DualSubspaceRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
the restriction map $E^* \to M^*$, $f \mapsto f|_M$, is onto: every continuous linear functional
on $M$ is the restriction of one on $E$. This is the statement "$R(T) = M^*$ by Hahn–Banach" of
§11.2 of [brezis2011functional].

The proof uses `exists_extension_norm_eq` and drops its norm clause. -/
theorem surjective_comp_subtypeL (M : Submodule 𝕜 E) :
    Function.Surjective fun f : StrongDual 𝕜 E => f.comp M.subtypeL := by
  intro g
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq M g
  exact ⟨f, ContinuousLinearMap.ext fun x => hf x⟩

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The
restriction of functionals to $M$ induces an isometric isomorphism $$E^* / M^\perp \cong M^*,
\qquad [f] \mapsto f|_M.$$ This is Proposition 11.10 of [brezis2011functional].

The map is onto by the Hahn–Banach theorem (`Submodule.surjective_comp_subtypeL`), and it is
isometric because $\|[f]\| = \operatorname{dist}(f, M^\perp) = \|f|_M\|$
(`Submodule.infDist_strongDualAnnihilator`). Neither closedness of $M$ nor completeness of $E$
is used. This is the normed version of the Mathlib equivalence `Subspace.quotAnnihilatorEquiv`
for the algebraic dual. -/
def quotAnnihilatorLIEStrongDual (M : Submodule 𝕜 E) :
    (StrongDual 𝕜 E ⧸ M.strongDualAnnihilator) ≃ₗᵢ[𝕜] StrongDual 𝕜 M :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (M.strongDualAnnihilator.liftQL
        (ContinuousLinearMap.precomp 𝕜 M.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 M)
        (ker_comp_subtypeL_eq_strongDualAnnihilator M).ge).toLinearMap
      norm_map' := fun x => by
        obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective M.strongDualAnnihilator x
        change ‖f.comp M.subtypeL‖ = ‖(Submodule.Quotient.mk f : _ ⧸ M.strongDualAnnihilator)‖
        have hnorm : ‖(Submodule.Quotient.mk f : _ ⧸ M.strongDualAnnihilator)‖ =
            infDist f (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) :=
          QuotientAddGroup.norm_mk (S := M.strongDualAnnihilator.toAddSubgroup) f
        rw [hnorm, infDist_strongDualAnnihilator] }
    fun g => by
      obtain ⟨f, hf⟩ := surjective_comp_subtypeL M g
      exact ⟨Submodule.Quotient.mk f, hf⟩

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and
let $f \in E^*$. The isomorphism `Submodule.quotAnnihilatorLIEStrongDual` sends the class of $f$
in $E^*/M^\perp$ to the restriction $f|_M$. -/
@[simp]
theorem quotAnnihilatorLIEStrongDual_apply_mk (M : Submodule 𝕜 E) (f : StrongDual 𝕜 E) :
    M.quotAnnihilatorLIEStrongDual (Submodule.Quotient.mk f) = f.comp M.subtypeL :=
  rfl

end DualSubspaceRCLike

/-! ### Reflexivity and uniform convexity of a quotient -/

section Reflexive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a reflexive normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $M$
be a closed subspace of $E$. Then $E/M$ is reflexive. This is Proposition 11.11 of
[brezis2011functional].

The proof is direct and avoids the use of Corollary 3.21 of [brezis2011functional]. A functional
$\Phi$ on $(E/M)^*$ is a functional on $M^\perp \subseteq E^*$ through
`Submodule.strongDualQuotLIEAnnihilator`. It extends to an element of $E^{**}$ by the
Hahn–Banach theorem, this element is represented by some $x \in E$ because $E$ is reflexive, and
$\Phi$ is then the evaluation at $[x]$. -/
instance Quotient.instIsReflexive [NormedSpace.IsReflexive 𝕜 E] (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : NormedSpace.IsReflexive 𝕜 (E ⧸ M) := by
  refine ⟨fun Φ => ?_⟩
  set e := M.strongDualQuotLIEAnnihilator
  obtain ⟨Ψ, hΨ, -⟩ := exists_extension_norm_eq M.strongDualAnnihilator
    (Φ.comp (e.symm.toContinuousLinearEquiv : M.strongDualAnnihilator →L[𝕜] StrongDual 𝕜 (E ⧸ M)))
  obtain ⟨x, hx⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E) Ψ
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  ext ξ
  have h1 := hΨ (e ξ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply] at h1
  rw [NormedSpace.dual_def, ← h1, ← hx, NormedSpace.dual_def, strongDualQuotLIEAnnihilator_apply]
  rfl

end Reflexive

section UniformConvex

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $E$ be a normed space over a nontrivially normed field $\mathbb{K}$, which is also a real
normed space and is uniformly convex, and let $M$ be a subspace of $E$ over $\mathbb{K}$. Then
the quotient $E/M$ is uniformly convex. This is Proposition 11.12 of [brezis2011functional].

The subspace $M$ need not be closed; the quotient is then a seminormed space. The real structure
is needed because uniform convexity is a statement about real scalar multiples.
[brezis2011functional] takes representatives of norm at most $1$, which needs Corollary 3.23 and
hence the reflexivity of $E$ by the Milman–Pettis theorem. Here representatives $x'$, $y'$ of
norm less than $1 + \eta$ (`Submodule.Quotient.norm_mk_lt`) are rescaled by $(1 + \eta)^{-1}$,
and uniform convexity of $E$ at $\varepsilon/2$ in its closed-ball form gives
$\|x' + y'\| \le (1 + \eta)(2 - \delta)$. With $\eta = \delta/4$ and $\delta \le 1$ this is at
most $2 - \delta/2$, which gives the modulus of convexity of the quotient. -/
theorem Quotient.uniformConvexSpace [NormedSpace ℝ E] [UniformConvexSpace E] (M : Submodule 𝕜 E) :
    UniformConvexSpace (E ⧸ M) := by
  refine ⟨fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (half_pos hε)
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  refine ⟨δ' / 2, half_pos hδ'0, fun x hx y hy hxy => ?_⟩
  have hη0 : 0 < δ' / 4 := by positivity
  obtain ⟨x', rfl, hx'⟩ := Submodule.Quotient.norm_mk_lt x hη0
  obtain ⟨y', rfl, hy'⟩ := Submodule.Quotient.norm_mk_lt y hη0
  rw [hx] at hx'
  rw [hy] at hy'
  have hpos : 0 < 1 + δ' / 4 := by linarith
  have hinv : 0 < (1 + δ' / 4)⁻¹ := inv_pos.2 hpos
  have ha : ‖(1 + δ' / 4)⁻¹ • x'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos, mul_one]
    exact hx'.le
  have hb : ‖(1 + δ' / 4)⁻¹ • y'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos, mul_one]
    exact hy'.le
  have hab : ε / 2 ≤ ‖(1 + δ' / 4)⁻¹ • x' - (1 + δ' / 4)⁻¹ • y'‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    have h1 : ε ≤ ‖x' - y'‖ := by
      refine hxy.trans ?_
      rw [← Submodule.Quotient.mk_sub]
      exact Submodule.Quotient.norm_mk_le M _
    calc ε / 2 = 2⁻¹ * ε := div_eq_inv_mul ε 2
      _ ≤ (1 + δ' / 4)⁻¹ * ε := by gcongr; linarith
      _ ≤ (1 + δ' / 4)⁻¹ * ‖x' - y'‖ := by gcongr
  have hsum := h ha hb hab
  rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos] at hsum
  calc ‖(Submodule.Quotient.mk x' : E ⧸ M) + Submodule.Quotient.mk y'‖
      = ‖(Submodule.Quotient.mk (x' + y') : E ⧸ M)‖ := by rw [Submodule.Quotient.mk_add]
    _ ≤ ‖x' + y'‖ := Submodule.Quotient.norm_mk_le M _
    _ ≤ (1 + δ' / 4) * (2 - δ) := hsum
    _ ≤ 2 - δ' / 2 := by nlinarith [mul_nonneg hδ'0.le hδ.le]

/-- Let $E$ be a uniformly convex normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and
let $M$ be a subspace of $E$. Then the quotient $E/M$ is uniformly convex. This is Proposition
11.12 of [brezis2011functional].

This is the instance form of `Submodule.Quotient.uniformConvexSpace`, with the real structure
`NormedSpace.restrictScalars`. -/
instance Quotient.instUniformConvexSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [UniformConvexSpace E] (M : Submodule 𝕜 E) :
    UniformConvexSpace (E ⧸ M) :=
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  Quotient.uniformConvexSpace M

end UniformConvex

/-! ### Dimension and codimension -/

section Dimension

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
$M$ is finite-dimensional if and only if the annihilator $M^\perp$ has finite codimension in
$E^*$. This is the first clause of Proposition 11.13(a) of [brezis2011functional].

The proof combines $E^*/M^\perp \cong M^*$ with Proposition 11.3
(`NormedSpace.finiteDimensional_of_finiteDimensional_strongDual`). -/
theorem finiteDimensional_iff_coFG_strongDualAnnihilator (M : Submodule 𝕜 E) :
    FiniteDimensional 𝕜 M ↔ M.strongDualAnnihilator.CoFG := by
  constructor
  · intro _
    exact M.quotAnnihilatorLIEStrongDual.toLinearEquiv.symm.finiteDimensional
  · intro _
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 M) :=
      M.quotAnnihilatorLIEStrongDual.toLinearEquiv.finiteDimensional
    exact NormedSpace.finiteDimensional_of_finiteDimensional_strongDual

/-- Let $M$ be a subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then
$$\dim M = \operatorname{codim} M^\perp,$$ where the codimension is the dimension of
$E^*/M^\perp$. This is the second clause of Proposition 11.13(a) of [brezis2011functional].

Both sides are `Module.finrank`, so both are $0$ when they are infinite. -/
theorem finrank_eq_finrank_quotient_strongDualAnnihilator (M : Submodule 𝕜 E) :
    finrank 𝕜 M = finrank 𝕜 (StrongDual 𝕜 E ⧸ M.strongDualAnnihilator) := by
  by_cases h : FiniteDimensional 𝕜 M
  · rw [← NormedSpace.finrank_strongDual, M.quotAnnihilatorLIEStrongDual.toLinearEquiv.finrank_eq]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (M.finiteDimensional_iff_coFG_strongDualAnnihilator.not.1 h)]

/-- Let $M$ be a closed subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. Then $M$ has finite codimension if and only if the annihilator $M^\perp$ is
finite-dimensional. This is the first clause of Proposition 11.13(b) of [brezis2011functional].

The proof combines $(E/M)^* \cong M^\perp$ with Proposition 11.3 for the normed space $E/M$. -/
theorem coFG_iff_finiteDimensional_strongDualAnnihilator (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : M.CoFG ↔ FiniteDimensional 𝕜 M.strongDualAnnihilator := by
  constructor
  · intro _
    exact M.strongDualQuotLIEAnnihilator.toLinearEquiv.finiteDimensional
  · intro _
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 (E ⧸ M)) :=
      M.strongDualQuotLIEAnnihilator.toLinearEquiv.symm.finiteDimensional
    exact NormedSpace.finiteDimensional_of_finiteDimensional_strongDual

/-- Let $M$ be a closed subspace of a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. Then $$\operatorname{codim} M = \dim M^\perp,$$ where the codimension is the
dimension of $E/M$. This is the second clause of Proposition 11.13(b) of [brezis2011functional].

Both sides are `Module.finrank`, so both are $0$ when they are infinite. -/
theorem finrank_quotient_eq_finrank_strongDualAnnihilator (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : finrank 𝕜 (E ⧸ M) = finrank 𝕜 M.strongDualAnnihilator := by
  by_cases h : FiniteDimensional 𝕜 (E ⧸ M)
  · rw [← NormedSpace.finrank_strongDual, M.strongDualQuotLIEAnnihilator.toLinearEquiv.finrank_eq]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (M.coFG_iff_finiteDimensional_strongDualAnnihilator.not.1 h)]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
finite-dimensional subspace of the dual $E^*$. Then $(N^\perp)^\perp = N$, where
$N^\perp \subseteq E$ and $(N^\perp)^\perp \subseteq E^*$. This is the claim inside the proof of
Proposition 11.14 of [brezis2011functional].

For a general subspace $N$, the subspace $(N^\perp)^\perp$ is only the weak-$*$ closure of $N$.
For a basis $f_1, \dots, f_k$ of $N$, the subspace $N^\perp$ is $\bigcap_i \ker f_i$, and a
functional that vanishes on it is a linear combination of the $f_i$
(`mem_span_of_iInf_ker_le_ker`, Lemma 3.2 of [brezis2011functional]). -/
theorem strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 N] :
    N.strongDualCoannihilator.strongDualAnnihilator = N := by
  refine le_antisymm (fun f hf => ?_) (le_strongDualCoannihilator_strongDualAnnihilator N)
  let b := Module.finBasis 𝕜 N
  -- `N` is spanned by the basis, seen in `E*`
  have hN : N = span 𝕜 (Set.range fun i => (b i : StrongDual 𝕜 E)) := by
    rw [show (fun i => (b i : StrongDual 𝕜 E)) = N.subtype ∘ b from rfl, Set.range_comp,
      ← map_span, b.span_eq, map_subtype_top]
  -- `f` vanishes on `⋂ᵢ ker (b i) = N^⊥`, hence lies in the span of the `b i` as a linear map
  have hker : ⨅ i, LinearMap.ker ((b i : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜) ≤
      LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := by
    intro x hx
    rw [mem_iInf] at hx
    refine mem_strongDualAnnihilator.1 hf x (mem_strongDualCoannihilator.2 fun g hg => ?_)
    have hg' : g ∈ span 𝕜 (Set.range fun i => (b i : StrongDual 𝕜 E)) := hN ▸ hg
    refine span_induction (fun g ⟨i, hi⟩ => ?_) (by simp) (fun g₁ g₂ _ _ h₁ h₂ => ?_)
      (fun c g _ h => ?_) hg'
    · rw [← hi]; exact hx i
    · simp [h₁, h₂]
    · simp [h]
  have hspan := mem_span_of_iInf_ker_le_ker hker
  rw [show (fun i => ((b i : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜)) =
      (ContinuousLinearMap.coeLM 𝕜) ∘ fun i => (b i : StrongDual 𝕜 E) from rfl, Set.range_comp,
    ← map_span, mem_map] at hspan
  obtain ⟨g, hg, hgf⟩ := hspan
  rw [hN]
  exact ContinuousLinearMap.coe_injective hgf ▸ hg

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
subspace of the dual $E^*$. Then $N$ is finite-dimensional if and only if $N^\perp \subseteq E$
has finite codimension. This is the first clause of Proposition 11.14 of [brezis2011functional].

[brezis2011functional] assumes that $N$ is closed and $E$ is complete; neither is used here.
With $M = N^\perp$, which is closed, $M^\perp = N$ when $N$ is finite-dimensional, and
$N \subseteq M^\perp$ always. -/
theorem finiteDimensional_iff_coFG_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    FiniteDimensional 𝕜 N ↔ N.strongDualCoannihilator.CoFG := by
  constructor
  · intro _
    rw [coFG_iff_finiteDimensional_strongDualAnnihilator,
      strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional]
    infer_instance
  · intro h
    have : FiniteDimensional 𝕜 N.strongDualCoannihilator.strongDualAnnihilator :=
      (coFG_iff_finiteDimensional_strongDualAnnihilator _).1 h
    exact finiteDimensional_of_le (le_strongDualCoannihilator_strongDualAnnihilator N)

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
subspace of the dual $E^*$. Then $$\dim N = \operatorname{codim} N^\perp,$$ where the
codimension is the dimension of $E / N^\perp$. This is the second clause of Proposition 11.14 of
[brezis2011functional].

Both sides are `Module.finrank`, so both are $0$ when they are infinite. -/
theorem finrank_eq_finrank_quotient_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    finrank 𝕜 N = finrank 𝕜 (E ⧸ N.strongDualCoannihilator) := by
  by_cases h : FiniteDimensional 𝕜 N
  · rw [finrank_quotient_eq_finrank_strongDualAnnihilator,
      strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (N.finiteDimensional_iff_coFG_strongDualCoannihilator.not.1 h)]

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
subspace of finite codimension of the dual $E^*$. Then $N^\perp \subseteq E$ is
finite-dimensional. This is the finiteness part of the third clause of Proposition 11.14 of
[brezis2011functional].

Since $N \subseteq (N^\perp)^\perp$, the subspace $(N^\perp)^\perp$ also has finite codimension,
and Proposition 11.13(a) applies to $N^\perp$. -/
theorem finiteDimensional_strongDualCoannihilator_of_coFG (N : Submodule 𝕜 (StrongDual 𝕜 E))
    [N.CoFG] : FiniteDimensional 𝕜 N.strongDualCoannihilator :=
  (finiteDimensional_iff_coFG_strongDualAnnihilator _).2
    (CoFG.of_le (le_strongDualCoannihilator_strongDualAnnihilator N) ‹N.CoFG›)

/-- Let $E$ be a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $N$ be a
subspace of finite codimension of the dual $E^*$. Then $$\dim N^\perp \le \operatorname{codim}
N,$$ where the codimension is the dimension of $E^*/N$. This is the third clause of Proposition
11.14 of [brezis2011functional].

The inequality can be strict when $E$ is not reflexive: a hyperplane $N = \ker \xi$ for
$\xi \in E^{**} \setminus J(E)$ has $N^\perp = 0$. Since $N \subseteq (N^\perp)^\perp$, the
quotient $E^*/(N^\perp)^\perp$ is a quotient of $E^*/N$, and $\dim N^\perp =
\operatorname{codim} (N^\perp)^\perp$ by Proposition 11.13(a). -/
theorem finrank_strongDualCoannihilator_le_finrank_quotient (N : Submodule 𝕜 (StrongDual 𝕜 E))
    [N.CoFG] :
    finrank 𝕜 N.strongDualCoannihilator ≤ finrank 𝕜 (StrongDual 𝕜 E ⧸ N) := by
  rw [finrank_eq_finrank_quotient_strongDualAnnihilator]
  exact LinearMap.finrank_le_finrank_of_surjective
    (factor_surjective (le_strongDualCoannihilator_strongDualAnnihilator N))

end Dimension

end Submodule

end
