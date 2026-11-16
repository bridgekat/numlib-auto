/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Module.Annihilator.ClosedSum
import NumlibSurface.Brezis.Chapter02.Section04

/-!
# Brezis, Section 2.5: Orthogonality revisited

This module formalizes Section 2.5 of [brezis2011functional]: the orthogonals of sums and
intersections of two closed linear subspaces $G$ and $L$ of a real normed space $E$. In the notation
of Section 1.3, $M^\perp \subseteq E^\star$ is the orthogonal of $M \subseteq E$ and
$N^\perp \subseteq E$ is the orthogonal of $N \subseteq E^\star$. Proposition 2.14 gives
$G \cap L = (G^\perp + L^\perp)^\perp$ and $G^\perp \cap L^\perp = (G + L)^\perp$. Corollary 2.15
gives $(G \cap L)^\perp \supseteq \overline{G^\perp + L^\perp}$ and $(G^\perp \cap L^\perp)^\perp =
\overline{G + L}$. When $E$ is a Banach space, Theorem 2.16 shows that $G + L$ is closed if and only
if $G^\perp + L^\perp$ is closed, and gives two more equivalent conditions.

The results specialize the backbone module `Numlib.Analysis.Normed.Module.Annihilator` (Proposition
2.14 and Corollary 2.15) and the module `Numlib.Analysis.Normed.Module.Annihilator.ClosedSum`
(Theorem 2.16, from `Submodule.tfae_isClosed_sup`).

## Main results

* Proposition 2.14, `Brezis.Chapter02.proposition_2_14`: $G \cap L = (G^\perp + L^\perp)^\perp$ (16)
  and $G^\perp \cap L^\perp = (G + L)^\perp$ (17).
* Corollary 2.15, `Brezis.Chapter02.corollary_2_15`: $(G \cap L)^\perp \supseteq \overline{G^\perp +
  L^\perp}$ (18) and $(G^\perp \cap L^\perp)^\perp = \overline{G + L}$ (19).
* Theorem 2.16, `Brezis.Chapter02.theorem_2_16`: $G + L$ is closed if and only if
  $G^\perp + L^\perp$ is closed, if and only if $G + L = (G^\perp \cap L^\perp)^\perp$, if and only
  if $G^\perp + L^\perp = (G \cap L)^\perp$.

## Conventions

* $M^\perp$ for $M \subseteq E$ is `Submodule.strongDualAnnihilator`, and $N^\perp$ for
  $N \subseteq E^\star$ is `Submodule.strongDualCoannihilator`. The sum $G + L$ is `G ⊔ L` and the
  intersection $G \cap L$ is `G ⊓ L`.

## Implementation notes

* The backbone proves (17), (18) and (19) without the closedness of $G$ and $L$. The results keep
  the hypotheses of the source.
-/

namespace Brezis.Chapter02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Proposition 2.14** of [brezis2011functional]. Let $E$ be a real normed space and let $G$ and
$L$ be two closed linear subspaces of $E$. Then
$$G \cap L = (G^\perp + L^\perp)^\perp, \qquad (16)$$
$$G^\perp \cap L^\perp = (G + L)^\perp. \qquad (17)$$
-/
theorem proposition_2_14 {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    G ⊓ L = (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).strongDualCoannihilator ∧
      G.strongDualAnnihilator ⊓ L.strongDualAnnihilator = (G ⊔ L).strongDualAnnihilator :=
  ⟨(Submodule.strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed hG hL).symm,
    (Submodule.strongDualAnnihilator_sup G L).symm⟩

/-- **Corollary 2.15** of [brezis2011functional]. Let $E$ be a real normed space and let $G$ and $L$
be two closed linear subspaces of $E$. Then
$$(G \cap L)^\perp \supseteq \overline{G^\perp + L^\perp}, \qquad (18)$$
$$(G^\perp \cap L^\perp)^\perp = \overline{G + L}. \qquad (19)$$

The proof does not use the closedness of $G$ and $L$. -/
theorem corollary_2_15 {G L : Submodule ℝ E} (_hG : IsClosed (G : Set E))
    (_hL : IsClosed (L : Set E)) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).topologicalClosure ≤
        (G ⊓ L).strongDualAnnihilator ∧
      (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator =
        (G ⊔ L).topologicalClosure :=
  ⟨Submodule.topologicalClosure_sup_strongDualAnnihilator_le G L,
    Submodule.strongDualCoannihilator_inf_strongDualAnnihilator G L⟩

/-- **Theorem 2.16** of [brezis2011functional]. Let $E$ be a Banach space and let $G$ and $L$ be two
closed linear subspaces of $E$. The following properties are equivalent: (a) $G + L$ is closed
in $E$; (b) $G^\perp + L^\perp$ is closed in $E^\star$; (c)
$G + L = (G^\perp \cap L^\perp)^\perp$; (d) $G^\perp + L^\perp = (G \cap L)^\perp$.

The equivalence is stated with `List.TFAE`. The proof specializes the backbone theorem
`Submodule.tfae_isClosed_sup`. -/
theorem theorem_2_16 [CompleteSpace E] {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    [IsClosed ((G ⊔ L : Submodule ℝ E) : Set E),
      IsClosed ((G.strongDualAnnihilator ⊔ L.strongDualAnnihilator :
        Submodule ℝ (StrongDual ℝ E)) : Set (StrongDual ℝ E)),
      G ⊔ L = (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator,
      G.strongDualAnnihilator ⊔ L.strongDualAnnihilator = (G ⊓ L).strongDualAnnihilator].TFAE :=
  Submodule.tfae_isClosed_sup hG hL

end Brezis.Chapter02
