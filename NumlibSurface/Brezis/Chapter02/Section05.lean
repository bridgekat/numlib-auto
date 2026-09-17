import Numlib.Analysis.Normed.Module.Annihilator.ClosedSum
import NumlibSurface.Brezis.Chapter02.Section04

/-!
# Brezis §2.5: orthogonality revisited

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.5: the orthogonals of sums and intersections of
closed subspaces `G`, `L` of a real Banach space `E`, in the notation of §1.3
(`M^⊥ = M.strongDualAnnihilator ⊆ E*` for `M ⊆ E`, `N^⊥ = N.strongDualCoannihilator ⊆ E` for
`N ⊆ E*`). All three results are the backbone `Numlib/Analysis/Normed/Module/Annihilator`
(Proposition 2.14 and Corollary 2.15) and its child `Annihilator/ClosedSum` (Theorem 2.16,
`Submodule.tfae_isClosed_sup`), restated over `ℝ`. The backbone proves (17), (18) and (19)
without closedness of `G`, `L`; the surface keeps the book's hypotheses.

## Main results

* `proposition_2_14` — `G ∩ L = (G^⊥ + L^⊥)^⊥` (16) and `G^⊥ ∩ L^⊥ = (G + L)^⊥` (17).
* `corollary_2_15` — `(G ∩ L)^⊥ ⊇ closure (G^⊥ + L^⊥)` (18) and `(G^⊥ ∩ L^⊥)^⊥ = closure (G + L)`
  (19).
* `theorem_2_16` — `G + L` is closed iff `G^⊥ + L^⊥` is closed iff `G + L = (G^⊥ ∩ L^⊥)^⊥` iff
  `G^⊥ + L^⊥ = (G ∩ L)^⊥`.
-/

namespace Brezis.Chapter02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Proposition 2.14.** Let `G`, `L` be two closed subspaces of `E`. Then
(16) `G ∩ L = (G^⊥ + L^⊥)^⊥` and (17) `G^⊥ ∩ L^⊥ = (G + L)^⊥`. -/
theorem proposition_2_14 {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    G ⊓ L = (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).strongDualCoannihilator ∧
      G.strongDualAnnihilator ⊓ L.strongDualAnnihilator = (G ⊔ L).strongDualAnnihilator :=
  ⟨(Submodule.strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed hG hL).symm,
    (Submodule.strongDualAnnihilator_sup G L).symm⟩

/-- **Corollary 2.15.** Let `G`, `L` be two closed subspaces of `E`. Then
(18) `(G ∩ L)^⊥ ⊇ closure (G^⊥ + L^⊥)` and (19) `(G^⊥ ∩ L^⊥)^⊥ = closure (G + L)`. -/
theorem corollary_2_15 {G L : Submodule ℝ E} (_hG : IsClosed (G : Set E))
    (_hL : IsClosed (L : Set E)) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).topologicalClosure ≤
        (G ⊓ L).strongDualAnnihilator ∧
      (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator =
        (G ⊔ L).topologicalClosure :=
  ⟨Submodule.topologicalClosure_sup_strongDualAnnihilator_le G L,
    Submodule.strongDualCoannihilator_inf_strongDualAnnihilator G L⟩

/-- **Theorem 2.16.** Let `G`, `L` be two closed subspaces of a Banach space `E`. The following
are equivalent: (a) `G + L` is closed in `E`; (b) `G^⊥ + L^⊥` is closed in `E*`;
(c) `G + L = (G^⊥ ∩ L^⊥)^⊥`; (d) `G^⊥ + L^⊥ = (G ∩ L)^⊥`. -/
theorem theorem_2_16 [CompleteSpace E] {G L : Submodule ℝ E} (hG : IsClosed (G : Set E))
    (hL : IsClosed (L : Set E)) :
    [IsClosed ((G ⊔ L : Submodule ℝ E) : Set E),
      IsClosed ((G.strongDualAnnihilator ⊔ L.strongDualAnnihilator :
        Submodule ℝ (StrongDual ℝ E)) : Set (StrongDual ℝ E)),
      G ⊔ L = (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator,
      G.strongDualAnnihilator ⊔ L.strongDualAnnihilator = (G ⊓ L).strongDualAnnihilator].TFAE :=
  Submodule.tfae_isClosed_sup hG hL

end Brezis.Chapter02
