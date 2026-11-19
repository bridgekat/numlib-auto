/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.Reflexive
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint

/-!
# Brezis, Section 5.2: The dual space of a Hilbert space

This module formalizes Section 5.2 of [brezis2011functional] for a real Hilbert space $H$ with
scalar product $(u, v)$ and norm $|u|$. The Riesz–Fréchet representation theorem states that every
$\varphi \in H^\star$ has the form $\langle \varphi, u \rangle = (f, u)$ for a unique $f \in H$, and
that $|f| = \|\varphi\|_{H^\star}$ (Theorem 5.5). The remarks of the section describe a Banach space
$V$ that is continuously and densely embedded in $H$, with $H$ as the pivot space of the triple
$V \subset H \subset V^\star$ (Remark 3), give a direct proof that Hilbert spaces are reflexive
(Remark 4), and identify the orthogonal complement $M^\perp$ of a closed subspace in $H$ with its
annihilator in $H^\star$ (Remark 5).

The Riesz–Fréchet theorem is Mathlib's isometry `InnerProductSpace.toDual ℝ H`. Remark 3 uses the
Banach adjoint `ContinuousLinearMap.strongDualMap` of Chapter 2, which restricts a functional along
the injection $i : V \to H$. Remark 5 uses the annihilator `Submodule.strongDualAnnihilator` of
Chapter 1 and Mathlib's orthogonal complement `Submodule.orthogonal`.

## Main results

* Theorem 5.5 (Riesz–Fréchet), `Brezis.Chapter05.theorem_5_5`: every $\varphi \in H^\star$ is
  $u \mapsto (f, u)$ for a unique $f \in H$, and $|f| = \|\varphi\|$.
* Remark 3, `Brezis.Chapter05.remark_5_3`: the restriction map $T : H^\star \to V^\star$ is bounded
  by the norm of the injection and injective, and it has dense range when $V$ is reflexive.
* Remark 3, `Brezis.Chapter05.remark_5_3_pairing`: $\langle Tf, v \rangle_{V^\star, V} = (f, v)$ for
  $f \in H$ and $v \in V$.
* Remark 4, `Brezis.Chapter05.remark_5_4`: Hilbert spaces are reflexive.
* Remark 5, `Brezis.Chapter05.remark_5_5`: for a closed subspace $M$, $M \cap M^\perp = \{0\}$,
  $M + M^\perp = H$, $f - P_M f = P_{M^\perp} f$, and $M$ is complemented.
* Remark 5, `Brezis.Chapter05.remark_5_5_annihilator`: the annihilator of $M$ in $H^\star$
  corresponds to $M^\perp \subseteq H$ under the Riesz–Fréchet isometry.

## Conventions

* Reflexivity is the backbone class `NormedSpace.IsReflexive ℝ V`.
* The orthogonal complement $M^\perp = \{u \in H : (u, v) = 0 \text{ for all } v \in M\}$ is
  Mathlib's `Mᗮ`, and the orthogonal projection $P_M$ is `Submodule.starProjection M`.

## Deviations from the source

* **Remark 3** (generalization). The dual restriction result drops completeness. The pairing
  formula holds for arbitrary continuous linear maps from normed spaces into $H$. See
  `Brezis.Chapter05.remark_5_3` and `Brezis.Chapter05.remark_5_3_pairing`.
* **Remark 5** (reading). The intersection identity is grouped with the conclusions for closed
  subspaces and shares their closedness hypothesis. See `Brezis.Chapter05.remark_5_5`.

## Not formalized

* **Remark 3, the example with a weighted space $\ell^2$.** It is not stated.
* **Remark 3, footnote.** The claim that $T$ is not surjective in general is not stated.
-/

open InnerProductSpace NormedSpace
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Theorem 5.5** of [brezis2011functional] (Riesz–Fréchet representation theorem). Let $H$ be a
real Hilbert space. For every $\varphi \in H^\star$ there is a unique $f \in H$ such that
$$\langle \varphi, u \rangle = (f, u) \quad \text{for all } u \in H.$$
Moreover $|f| = \|\varphi\|_{H^\star}$.

Uniqueness is stated for the pair of conditions. The representative is
`(InnerProductSpace.toDual ℝ H).symm φ`. -/
theorem theorem_5_5 (φ : StrongDual ℝ H) :
    ∃! f : H, (∀ u, φ u = ⟪f, u⟫_ℝ) ∧ ‖f‖ = ‖φ‖ := by
  refine ⟨(toDual ℝ H).symm φ, ⟨fun u => ?_, ?_⟩, ?_⟩
  · rw [toDual_symm_apply]
  · exact LinearIsometryEquiv.norm_map _ _
  · rintro g ⟨hg, -⟩
    apply (toDual ℝ H).injective
    ext u
    rw [toDual_apply_apply, ← hg, LinearIsometryEquiv.apply_symm_apply]

/-! ### Remark 3: the triple $V \subset H \subset V^\star$ -/

section Pivot

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace H] [CompleteSpace V] in
/-- **Remark 3** in Chapter 5 of [brezis2011functional], the triple $V \subset H \subset V^\star$
with $H$ as pivot space. Let $V$ be a real normed space and let $i : V \to H$ be a continuous,
injective linear map with dense range, so that $|i v| \le C \|v\|$ with $C = \|i\|$. Let
$T : H^\star \to V^\star$ be the restriction map, $\langle T\varphi, v \rangle = \langle
\varphi, i v \rangle$. Then:

1. $\|T\varphi\|_{V^\star} \le \|i\| \, \|\varphi\|_{H^\star}$ for every $\varphi \in H^\star$;
2. $T$ is injective;
3. if $V$ is reflexive, then the range $R(T)$ is dense in $V^\star$.

The map $T$ is the Banach adjoint `i.strongDualMap` of Chapter 2.

**Generalization.** The conclusions apply to incomplete spaces. In (3), reflexivity itself
implies completeness of $V$. -/
theorem remark_5_3 (i : V →L[ℝ] H) (hi : Function.Injective i) (hd : DenseRange i) :
    (∀ φ : StrongDual ℝ H, ‖i.strongDualMap φ‖ ≤ ‖i‖ * ‖φ‖) ∧
      Function.Injective i.strongDualMap ∧
      (IsReflexive ℝ V → DenseRange i.strongDualMap) := by
  refine ⟨fun φ => ?_, ?_, fun hV => ?_⟩
  · -- (i): `‖T‖ = ‖i‖`
    calc ‖i.strongDualMap φ‖ ≤ ‖i.strongDualMap‖ * ‖φ‖ := i.strongDualMap.le_opNorm φ
      _ = ‖i‖ * ‖φ‖ := by rw [ContinuousLinearMap.opNorm_strongDualMap]
  · -- (ii): a functional vanishing on the dense range of `i` vanishes
    refine (injective_iff_map_eq_zero _).2 fun φ hφ => ?_
    have h : (⇑φ : H → ℝ) = ⇑(0 : StrongDual ℝ H) :=
      hd.equalizer φ.continuous continuous_const (funext fun v => by
        have := congrArg (fun ψ : StrongDual ℝ V => ψ v) hφ
        simpa [ContinuousLinearMap.strongDualMap_apply] using this)
    exact DFunLike.coe_injective h
  · -- (iii): a functional on `V*` vanishing on `R(T)` is `J v` with `i v = 0`
    by_contra hnot
    rw [denseRange_iff_closure_range] at hnot
    obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ V, ψ ∉ closure (Set.range i.strongDualMap) := by
      by_contra h
      exact hnot (Set.eq_univ_of_forall fun ψ => not_not.1 fun h' => h ⟨ψ, h'⟩)
    set N : Submodule ℝ (StrongDual ℝ V) :=
      (LinearMap.range (i.strongDualMap : StrongDual ℝ H →ₗ[ℝ] StrongDual ℝ V)).topologicalClosure
      with hN
    have hNcl : IsClosed (N : Set (StrongDual ℝ V)) := Submodule.isClosed_topologicalClosure _
    have hψN : ψ ∉ N := by
      rw [hN, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]
      exact hψ
    obtain ⟨ξ, hξ1, hξN, hξψ⟩ := N.exists_dual_eq_zero_of_notMem hNcl hψN
    obtain ⟨v, rfl⟩ := hV.surjective_inclusionInDoubleDual ξ
    have hv : i v = 0 := by
      refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
      have := hξN (i.strongDualMap φ) (Submodule.le_topologicalClosure _ ⟨φ, rfl⟩)
      rwa [dual_def, ContinuousLinearMap.strongDualMap_apply] at this
    have hv0 : v = 0 := hi (by rw [hv, map_zero])
    rw [hv0, map_zero] at hξ1
    simp at hξ1

omit [CompleteSpace V] in
/-- **Remark 3** in Chapter 5 of [brezis2011functional], the identification of the pairings. Let $V$
be a real normed space and $i : V \to H$ a continuous linear map. Read $f \in H$ as an element
of $H^\star$ by the Riesz–Fréchet isometry, and then as an element of $V^\star$ by $T$. Then
$$\langle f, v \rangle_{V^\star, V} = (f, i v) \quad \text{for all } f \in H,\ v \in V.$$

**Generalization.** The pairing formula applies to any continuous linear map from a normed
space $V$. The source takes a dense embedding of a Banach space. -/
theorem remark_5_3_pairing (i : V →L[ℝ] H) (f : H) (v : V) :
    i.strongDualMap (toDual ℝ H f) v = ⟪f, i v⟫_ℝ := by
  rw [ContinuousLinearMap.strongDualMap_apply, toDual_apply_apply]

end Pivot

/-- **Remark 4** in Chapter 5 of [brezis2011functional]. Every real Hilbert space is reflexive. The
proof does not use the theory of uniformly convex spaces.

The proof is the backbone instance `NormedSpace.instIsReflexiveOfInnerProductSpace`, which uses
the Riesz–Fréchet isomorphism twice: from $H$ onto $H^\star$, and from $H^\star$ onto
$H^{\star\star}$. -/
theorem remark_5_4 : IsReflexive ℝ H := inferInstance

/-- **Remark 5** in Chapter 5 of [brezis2011functional], the orthogonal complement in $H$. Let
$M \subseteq H$ be a closed linear subspace and $f \in H$. Then $M \cap M^\perp = \{0\}$,
$M + M^\perp = H$,
$$f - P_M f = P_{M^\perp} f,$$
and $M$ has a complement in the sense of Section 2.4.

The last property is Mathlib's `Submodule.ClosedComplemented`: there is a continuous linear
projection of $H$ onto $M$.

**Reading.** The source states the intersection identity for every subspace. Here it is grouped
with the three conclusions that require closedness. -/
theorem remark_5_5 (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (f : H) :
    M ⊓ Mᗮ = ⊥ ∧ M ⊔ Mᗮ = ⊤ ∧
      (haveI := hM.completeSpace_coe; f - M.starProjection f = Mᗮ.starProjection f) ∧
      M.ClosedComplemented := by
  have := hM.completeSpace_coe
  exact ⟨M.inf_orthogonal_eq_bot, Submodule.sup_orthogonal_of_hasOrthogonalProjection,
    (M.starProjection_orthogonal_val f).symm, M.isTopCompl_orthogonal.closedComplemented⟩

/-- **Remark 5** in Chapter 5 of [brezis2011functional], first sentence. Let $M \subseteq H$ be a
linear subspace. The annihilator $M^\perp \subseteq H^\star$ of Section 1.3 "may now be
considered as a subspace of $H$": a functional $\varphi \in H^\star$ lies in the annihilator of
$M$ if and only if its Riesz–Fréchet representative lies in
$$M^\perp = \{u \in H : (u, v) = 0 \text{ for all } v \in M\}.$$

The annihilator is `Submodule.strongDualAnnihilator M`, and the representative is
`(InnerProductSpace.toDual ℝ H).symm φ`. -/
theorem remark_5_5_annihilator (M : Submodule ℝ H) (φ : StrongDual ℝ H) :
    φ ∈ M.strongDualAnnihilator ↔ (toDual ℝ H).symm φ ∈ Mᗮ := by
  rw [Submodule.mem_strongDualAnnihilator, Submodule.mem_orthogonal]
  refine forall₂_congr fun u _ => ?_
  rw [real_inner_comm, toDual_symm_apply]

end Brezis.Chapter05

end
