/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Module.Annihilator
import NumlibSurface.Brezis.Chapter01.Section02

/-!
# Brezis, Section 1.3: The bidual $E^{\star\star}$, orthogonality relations

This module formalizes Section 1.3 of [brezis2011functional] for a real normed space $E$. The
canonical injection $J : E \to E^{\star\star}$ sends $x$ to the functional
$f \mapsto \langle f, x \rangle$ on $E^\star$, so that $\langle Jx, f \rangle_{E^{\star\star},
E^\star} = \langle f, x \rangle_{E^\star, E}$. It is a linear isometry, hence injective. For a
linear subspace $M \subseteq E$ and a linear subspace $N \subseteq E^\star$, the orthogonals are
$$M^\perp = \{f \in E^\star : \langle f, x \rangle = 0 \ \forall x \in M\},
  \qquad N^\perp = \{x \in E : \langle f, x \rangle = 0 \ \forall f \in N\}.$$
Both are closed linear subspaces. Proposition 1.9 states $(M^\perp)^\perp = \overline{M}$ and
$(N^\perp)^\perp \supseteq \overline{N}$, and Remark 6 states equality in the second relation when
$E$ is reflexive.

The canonical injection is Mathlib's `NormedSpace.inclusionInDoubleDual ℝ E`, with the isometry
`NormedSpace.inclusionInDoubleDualLi`. The orthogonals and the proofs come from the backbone module
`Numlib.Analysis.Normed.Module.Annihilator`: Proposition 1.9 and Remark 6 specialize
`Submodule.strongDualCoannihilator_strongDualAnnihilator`,
`Submodule.topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator` and
`Submodule.strongDualAnnihilator_strongDualCoannihilator`.

## Main definitions

* Section 1.3, the canonical injection, `Brezis.Chapter01.canonicalInjection_apply`: $J$ is
  `NormedSpace.inclusionInDoubleDual ℝ E`, and $\langle Jx, f \rangle = \langle f, x \rangle$.
* Section 1.3, the notation for orthogonals, `Brezis.Chapter01.mem_orthogonal_iff`: the orthogonals
  $M^\perp$ and $N^\perp$ are `Submodule.strongDualAnnihilator` and
  `Submodule.strongDualCoannihilator`.

## Main results

* Section 1.3, `Brezis.Chapter01.norm_canonicalInjection`: $\|Jx\|_{E^{\star\star}} = \|x\|_E$.
* Section 1.3, `Brezis.Chapter01.canonicalInjection_injective`: $J$ is injective.
* Section 1.3, `Brezis.Chapter01.isClosed_orthogonal`: $M^\perp$ and $N^\perp$ are closed.
* Proposition 1.9, `Brezis.Chapter01.proposition_1_9`: $(M^\perp)^\perp = \overline{M}$.
* Proposition 1.9, `Brezis.Chapter01.proposition_1_9_supset`:
  $(N^\perp)^\perp \supseteq \overline{N}$.
* Remark 6, `Brezis.Chapter01.remark_1_6`: if $E$ is reflexive, then
  $(N^\perp)^\perp = \overline{N}$.

## Conventions

* Reflexivity, that is, $J$ is onto, is the backbone class `NormedSpace.IsReflexive ℝ E`. Chapter 3
  restates it.
* $N^\perp$ is a subset of $E$, not of $E^{\star\star}$.

## Not formalized

* **Remark 6, strict inclusion (Exercise 1.16).** An example in $\ell^1$ where
  $(N^\perp)^\perp \neq \overline{N}$.
* **Remark 6, last sentence.** $(N^\perp)^\perp$ is the closure of $N$ in the weak-$\star$ topology.
  The weak-$\star$ topology belongs to Chapter 3.
-/

open NormedSpace

namespace Brezis.Chapter01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The canonical injection -/

/-- **Section 1.3** of [brezis2011functional], the canonical injection $J : E \to E^{\star\star}$.
Let $E$ be a real normed space. For $x \in E$, $Jx$ is the functional
$f \mapsto \langle f, x \rangle$ on $E^\star$, that is,
$$\langle Jx, f \rangle_{E^{\star\star}, E^\star} = \langle f, x \rangle_{E^\star, E} \quad
  \text{for all } f \in E^\star.$$

The map $J$ is Mathlib's `NormedSpace.inclusionInDoubleDual ℝ E`, a bounded linear map. -/
theorem canonicalInjection_apply (x : E) (f : StrongDual ℝ E) :
    inclusionInDoubleDual ℝ E x f = f x :=
  dual_def ℝ E x f

/-- **Section 1.3** of [brezis2011functional], $J$ is an isometry. For every $x$ in a real normed
space $E$,
$$\|Jx\|_{E^{\star\star}} = \|x\|_E.$$

The source derives this from Corollary 1.4. The proof uses Mathlib's
`NormedSpace.inclusionInDoubleDualLi`. -/
theorem norm_canonicalInjection (x : E) : ‖inclusionInDoubleDual ℝ E x‖ = ‖x‖ :=
  (inclusionInDoubleDualLi ℝ).norm_map x

/-- **Section 1.3** of [brezis2011functional]. The canonical injection $J : E \to E^{\star\star}$ is
injective, because it is an isometry. -/
theorem canonicalInjection_injective : Function.Injective (inclusionInDoubleDual ℝ E) :=
  (inclusionInDoubleDualLi ℝ (E := E)).injective

/-! ### The orthogonals -/

/-- **Section 1.3** of [brezis2011functional], the notation for orthogonals. Let $E$ be a real
normed space. For a linear subspace $M \subseteq E$,
$$M^\perp = \{f \in E^\star : \langle f, x \rangle = 0 \ \forall x \in M\},$$
and for a linear subspace $N \subseteq E^\star$,
$$N^\perp = \{x \in E : \langle f, x \rangle = 0 \ \forall f \in N\}.$$

The set $M^\perp$ is `M.strongDualAnnihilator`. The set $N^\perp$, a subset of $E$ rather than
of $E^{\star\star}$, is `N.strongDualCoannihilator`. The theorem states the two membership
criteria. -/
theorem mem_orthogonal_iff (M : Submodule ℝ E) (N : Submodule ℝ (StrongDual ℝ E))
    (f : StrongDual ℝ E) (x : E) :
    (f ∈ M.strongDualAnnihilator ↔ ∀ y ∈ M, f y = 0) ∧
      (x ∈ N.strongDualCoannihilator ↔ ∀ g ∈ N, g x = 0) :=
  ⟨Submodule.mem_strongDualAnnihilator, Submodule.mem_strongDualCoannihilator⟩

/-- **Section 1.3** of [brezis2011functional]. Let $E$ be a real normed space, $M \subseteq E$ and
$N \subseteq E^\star$ linear subspaces. Then $M^\perp$ is a closed linear subspace of $E^\star$
and $N^\perp$ is a closed linear subspace of $E$. -/
theorem isClosed_orthogonal (M : Submodule ℝ E) (N : Submodule ℝ (StrongDual ℝ E)) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual ℝ E)) ∧
      IsClosed (N.strongDualCoannihilator : Set E) :=
  ⟨M.isClosed_strongDualAnnihilator, N.isClosed_strongDualCoannihilator⟩

/-- **Proposition 1.9** of [brezis2011functional], first relation. Let $E$ be a real normed space.
For every linear subspace $M \subseteq E$,
$$(M^\perp)^\perp = \overline{M}.$$

The closure $\overline{M}$ is `M.topologicalClosure`. The proof specializes the backbone theorem
`Submodule.strongDualCoannihilator_strongDualAnnihilator`. -/
theorem proposition_1_9 (M : Submodule ℝ E) :
    M.strongDualAnnihilator.strongDualCoannihilator = M.topologicalClosure :=
  M.strongDualCoannihilator_strongDualAnnihilator

/-- **Proposition 1.9** of [brezis2011functional], second relation. Let $E$ be a real normed space.
For every linear subspace $N \subseteq E^\star$,
$$(N^\perp)^\perp \supseteq \overline{N}.$$

The proof specializes the backbone theorem
`Submodule.topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator`. -/
theorem proposition_1_9_supset (N : Submodule ℝ (StrongDual ℝ E)) :
    N.topologicalClosure ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  N.topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator

/-- **Remark 6** of [brezis2011functional], the reflexive case. Let $E$ be a reflexive real normed
space. For every linear subspace $N \subseteq E^\star$,
$$(N^\perp)^\perp = \overline{N}.$$

In the proof of the source, the functional $\xi \in E^{\star\star}$ that separates a point from
$\overline{N}$ is then $Jx_0$ for some $x_0 \in E$. The proof specializes the backbone theorem
`Submodule.strongDualAnnihilator_strongDualCoannihilator`. -/
theorem remark_1_6 [IsReflexive ℝ E] (N : Submodule ℝ (StrongDual ℝ E)) :
    N.strongDualCoannihilator.strongDualAnnihilator = N.topologicalClosure :=
  N.strongDualAnnihilator_strongDualCoannihilator

end Brezis.Chapter01
