/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section02
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# Generalized inverses of Hilbert space operators

Section 9.3 of [benIsrael2003generalized] introduces Tseng inverses of
partially defined Hilbert space operators and identifies the maximal Tseng
inverse with the bounded Moore–Penrose inverse when the range is closed.

## Deviations from the source

* In **Theorem 4(c)** the range of the Erdélyi inverse is the carrier.
  Its closure can be smaller than the orthogonal complement of the kernel.
* In **Theorem 4(e)** the projection uses the image of the carrier.
* In **Theorem 4(f), (h), (j)** the iterated kernel is the perpendicular
  complement of the carrier. Equality with the original operator requires
  dense domain as well as closed kernel.
* In **Theorem 4(k)** a dense closed operator satisfies the adjoint equality.
  A dense closable operator with trivial carrier and nonzero range
  violates the printed inclusion.
* **Exercise 15** isolates the exact compatibility condition on the
  original domain and the closure of its kernel.
-/

namespace BenIsraelGreville.Chapter09

open LinearPMap
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem eq_zero_of_mem_of_mem_orthogonal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {U : Submodule 𝕜 H} {x : H} (hu : x ∈ U) (ho : x ∈ Uᗮ) : x = 0 :=
  (Submodule.disjoint_def.mp U.orthogonal_disjoint) x hu ho

/-- **Definition 1**, Equations (5)–(8) of [benIsrael2003generalized].
Two partial operators are Tseng inverses when their ranges lie in each
other's domains and the products have orthogonal projection residuals. -/
structure IsTsengInverse (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop where
  /-- The first operator's entire range belongs to the inverse's domain. -/
  range_le_domain : T.toFun.range ≤ S.domain
  /-- The inverse's entire range belongs to the first operator's domain. -/
  inverse_range_le_domain : S.toFun.range ≤ T.domain
  /-- The inverse applied after the operator has an orthogonal residual. -/
  left (x : T.domain) :
    (x : E) - S ⟨T x, range_le_domain ⟨x, rfl⟩⟩ ∈ S.toFun.rangeᗮ
  /-- The operator applied after its inverse has an orthogonal residual. -/
  right (y : S.domain) :
    (y : F) - T ⟨S y, inverse_range_le_domain ⟨y, rfl⟩⟩ ∈ T.toFun.rangeᗮ

/-- The defining equations are symmetric in the two operators. -/
theorem IsTsengInverse.symm {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) : IsTsengInverse S T :=
  ⟨h.inverse_range_le_domain, h.range_le_domain, h.right, h.left⟩

private theorem IsTsengInverse.apply_left_eq_self_of_mem_range
    {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S)
    (x : T.domain) (hx : (x : E) ∈ S.toFun.range) :
    S ⟨T x, h.range_le_domain ⟨x, rfl⟩⟩ = x := by
  have he := eq_zero_of_mem_of_mem_orthogonal
    (S.toFun.range.sub_mem hx ⟨_, rfl⟩) (h.left x)
  exact (sub_eq_zero.mp he).symm

/-- **Lemma 1** of [benIsrael2003generalized].
The domain is the orthogonal sum of the inverse range and its orthogonal
complement within the domain. -/
theorem lemma_1 {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S) :
    T.domain = S.toFun.range ⊔ (T.domain ⊓ S.toFun.rangeᗮ) := by
  refine le_antisymm (fun x hx => ?_) (sup_le h.inverse_range_le_domain inf_le_left)
  let z := S ⟨T ⟨x, hx⟩, h.range_le_domain ⟨⟨x, hx⟩, rfl⟩⟩
  have hz : z ∈ S.toFun.range := ⟨_, rfl⟩
  exact Submodule.mem_sup.mpr
    ⟨z, hz, x - z, ⟨T.domain.sub_mem hx (h.inverse_range_le_domain hz), h.left ⟨x, hx⟩⟩,
      add_sub_cancel z x⟩

/-- **Lemma 2** of [benIsrael2003generalized].
The restrictions to the two ranges are mutually inverse. -/
theorem lemma_2 {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S) :
    (∀ x : T.domain, (x : E) ∈ S.toFun.range →
      S ⟨T x, h.range_le_domain ⟨x, rfl⟩⟩ = x) ∧
    (∀ y : S.domain, (y : F) ∈ T.toFun.range →
      T ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ = y) :=
  ⟨h.apply_left_eq_self_of_mem_range, h.symm.apply_left_eq_self_of_mem_range⟩

private theorem ker_eq_domain_inf_orthogonal_range_of_isTsengInverse
    {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S) :
    T.ker = T.domain ⊓ S.toFun.rangeᗮ := by
  ext x
  constructor
  · intro hx
    let u : T.domain := ⟨x, T.ker_le_domain hx⟩
    have hTu : T u = 0 := T.coe_mem_ker_iff.mp hx
    have hleft := h.left u
    have hS : (⟨T u, h.range_le_domain ⟨u, rfl⟩⟩ : S.domain) = 0 := Subtype.ext hTu
    rw [hS, S.map_zero, sub_zero] at hleft
    exact ⟨u.2, hleft⟩
  · rintro ⟨hd, ho⟩
    let u : T.domain := ⟨x, hd⟩
    let y : S.domain := ⟨T u, h.range_le_domain ⟨u, rfl⟩⟩
    have hz : S y ∈ S.toFun.range := ⟨y, rfl⟩
    have hzo : S y ∈ S.toFun.rangeᗮ := by
      have hv := S.toFun.rangeᗮ.sub_mem ho (h.left u)
      convert hv using 1
      dsimp only [u, y]
      abel
    have hzero := eq_zero_of_mem_of_mem_orthogonal hz hzo
    have hv : (⟨S y, h.inverse_range_le_domain hz⟩ : T.domain) = 0 := Subtype.ext hzero
    have hTy : T ⟨S y, h.inverse_range_le_domain hz⟩ = T u :=
      (lemma_2 h).2 y ⟨u, rfl⟩
    rw [hv, T.map_zero] at hTy
    exact T.coe_mem_ker_iff.mpr hTy.symm

/-- **Lemma 3**, Equations (10)–(11) of [benIsrael2003generalized].
The original kernel is the domain perpendicular to the inverse range, and
the inverse range equals the original carrier. -/
theorem lemma_3 {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S) :
    T.ker = T.domain ⊓ S.toFun.rangeᗮ ∧ carrier T = S.toFun.range := by
  have hk := ker_eq_domain_inf_orthogonal_range_of_isTsengInverse h
  have hr : S.toFun.range ≤ carrier T :=
    le_inf h.inverse_range_le_domain
      ((Submodule.le_orthogonal_orthogonal S.toFun.range).trans (Submodule.orthogonal_le
        (show T.ker ≤ S.toFun.rangeᗮ from hk ▸ inf_le_right)))
  refine ⟨hk, le_antisymm (fun x hx => ?_) hr⟩
  have hxd : x ∈ S.toFun.range ⊔ T.ker := by rw [hk, ← lemma_1 h]; exact hx.1
  obtain ⟨a, ha, k, hk', hsum⟩ := Submodule.mem_sup.mp hxd
  have hko : k ∈ T.kerᗮ := by
    have he : k = x - a := eq_sub_of_add_eq' hsum
    rw [he]
    exact T.kerᗮ.sub_mem hx.2 (hr ha).2
  have hk0 := eq_zero_of_mem_of_mem_orthogonal hk' hko
  simpa [hk0, ← hsum] using ha

private theorem restrictCarrier_range_of_split (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    (restrictCarrier T).toFun.range = T.toFun.range :=
  restrictCarrier_range T ⟨T.ker_le_domain, hT⟩

private abbrev zeroOn (L : Submodule 𝕜 F) : F →ₗ.[𝕜] E :=
  (0 : F →ₗ[𝕜] E).toPMap L

private theorem disjoint_carrier_inverse_zero (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    Disjoint (restrictCarrier T).inverse.domain (zeroOn (E := E) L).domain := by
  rw [LinearPMap.inverse_domain]
  exact T.toFun.range.orthogonal_disjoint.mono (restrictCarrier_range_le T) hL

/-- The inverse on the carrier, extended by zero on a subspace perpendicular
to the operator's range. Under the domain decomposition of Theorem 1 this
is the Tseng inverse with that prescribed kernel. -/
noncomputable def tsengInverseOn (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) : F →ₗ.[𝕜] E :=
  let A := (restrictCarrier T).inverse
  let Z := zeroOn (E := E) L
  A.sup Z (LinearPMap.sup_h_of_disjoint A Z (disjoint_carrier_inverse_zero T L hL))

/-- **Equation (14)** of [benIsrael2003generalized], for the constructed inverse. -/
theorem tsengInverseOn_domain (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    (tsengInverseOn T L hL).domain = (restrictCarrier T).toFun.range ⊔ L := by
  rw [tsengInverseOn, LinearPMap.domain_sup, LinearPMap.inverse_domain]
  rfl

private theorem carrierInverse_le_tsengInverseOn (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    (restrictCarrier T).inverse ≤ tsengInverseOn T L hL :=
  LinearPMap.left_le_sup _ _ (LinearPMap.sup_h_of_disjoint _ _
    (disjoint_carrier_inverse_zero T L hL))

private theorem zeroOn_le_tsengInverseOn (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    zeroOn L ≤ tsengInverseOn T L hL :=
  LinearPMap.right_le_sup _ _ (LinearPMap.sup_h_of_disjoint _ _
    (disjoint_carrier_inverse_zero T L hL))

/-- A point on the inverse graph is obtained from a carrier vector by
adding a vector from the chosen orthogonal subspace to its image. -/
theorem mem_graph_tsengInverseOn_iff (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) {y : F} {x : E} :
    (y, x) ∈ (tsengInverseOn T L hL).graph ↔
      ∃ a : T.domain, (a : E) ∈ T.kerᗮ ∧ (a : E) = x ∧ y - T a ∈ L := by
  let A := (restrictCarrier T).inverse
  let S := tsengInverseOn T L hL
  constructor
  · rintro hy
    have hyd := LinearPMap.mem_domain_of_mem_graph hy
    have hy' : y ∈ A.domain ⊔ L := hyd
    obtain ⟨b, hb, z, hz, hsum⟩ := Submodule.mem_sup.mp hy'
    let b' : A.domain := ⟨b, hb⟩
    have hab : b ∈ (restrictCarrier T).toFun.range := by rwa [← LinearPMap.inverse_domain]
    obtain ⟨a, ha⟩ := hab
    have hA : A b' = (a : E) := LinearPMap.inverse_apply_eq (restrictCarrier_ker T) ha
    have hS : S ⟨y, hyd⟩ = x := ((LinearPMap.image_iff hyd).mpr hy).symm
    have he : S ⟨y, hyd⟩ = A b' := by
      have he' := LinearPMap.sup_apply
        (LinearPMap.sup_h_of_disjoint A (zeroOn L) (disjoint_carrier_inverse_zero T L hL))
        b' (⟨z, hz⟩ : L) (⟨y, hy'⟩ : ↥(A.domain ⊔ L)) hsum
      exact he'.trans (add_zero _)
    refine ⟨⟨a, a.2.2⟩, a.2.1, hA.symm.trans (he.symm.trans hS), ?_⟩
    have hb' : T ⟨a, a.2.2⟩ = b := ha
    rw [hb', ← hsum, add_sub_cancel_left]
    exact hz
  · rintro ⟨a, hao, rfl, hz⟩
    have hb : (T a, (a : E)) ∈ A.graph := by
      exact LinearPMap.mem_inverse_graph (restrictCarrier_ker T)
        (⟨a, hao, a.2⟩ : (restrictCarrier T).domain)
    have hS := LinearPMap.le_graph_of_le (carrierInverse_le_tsengInverseOn T L hL) hb
    have hZ : (y - T a, (0 : E)) ∈ S.graph := by
      apply LinearPMap.le_graph_of_le (zeroOn_le_tsengInverseOn T L hL)
      exact (zeroOn (E := E) L).mem_graph ⟨y - T a, hz⟩
    have he := S.graph.add_mem hS hZ
    change (T a + (y - T a), (a : E) + 0) ∈ S.graph at he
    rwa [add_sub_cancel, add_zero] at he

/-- **Equation (15)** of [benIsrael2003generalized]. -/
theorem tsengInverseOn_ker (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    (tsengInverseOn T L hL).ker = L := by
  ext y
  rw [LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨b, rfl, hb⟩
    obtain ⟨a, _, ha, h⟩ := (mem_graph_tsengInverseOn_iff T L hL).mp
      ((LinearPMap.image_iff b.2).mp hb.symm)
    have ha0 : a = 0 := Subtype.ext ha
    simpa [ha0] using h
  · intro hy
    have hg : (y, 0) ∈ (tsengInverseOn T L hL).graph :=
      (mem_graph_tsengInverseOn_iff T L hL).mpr
        ⟨0, T.kerᗮ.zero_mem, rfl, by simpa only [T.map_zero, sub_zero] using hy⟩
    obtain ⟨b, hby, hb⟩ := (LinearPMap.mem_graph_iff _).mp hg
    exact ⟨b, hby.symm, hb⟩

/-- **Equation (17)** of [benIsrael2003generalized]. -/
theorem tsengInverseOn_range (T : E →ₗ.[𝕜] F)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    (tsengInverseOn T L hL).toFun.range = carrier T := by
  ext x
  rw [LinearPMap.mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, hao, rfl, _⟩ := (mem_graph_tsengInverseOn_iff T L hL).mp hy
    exact ⟨a.2, hao⟩
  · rintro ⟨hxd, hxo⟩
    exact ⟨T ⟨x, hxd⟩, (mem_graph_tsengInverseOn_iff T L hL).mpr
      ⟨⟨x, hxd⟩, hxo, rfl, by simp⟩⟩

private theorem ker_le_orthogonal_carrier (T : E →ₗ.[𝕜] F) :
    T.ker ≤ (carrier T)ᗮ :=
  T.ker.le_orthogonal_orthogonal.trans
    (Submodule.orthogonal_le (show carrier T ≤ T.kerᗮ from inf_le_right))

private theorem domain_eq_ker_sup_carrier_of_isTsengInverse
    {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E} (h : IsTsengInverse T S) :
    T.domain = T.ker ⊔ carrier T := by
  rw [(lemma_3 h).2, (lemma_3 h).1, sup_comm, ← lemma_1 h]

/-- **Theorem 1** of [benIsrael2003generalized], constructive direction.
The inverse on the carrier extended by zero is a Tseng inverse whenever
the domain splits orthogonally over the kernel. -/
theorem isTsengInverse_tsengInverseOn (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    IsTsengInverse T (tsengInverseOn T L hL) := by
  let S := tsengInverseOn T L hL
  have hr : S.toFun.range = carrier T := tsengInverseOn_range T L hL
  have hTS : T.toFun.range ≤ S.domain := by
    rw [tsengInverseOn_domain, restrictCarrier_range_of_split T hT]
    exact le_sup_left
  have hST : S.toFun.range ≤ T.domain := by rw [hr]; exact inf_le_left
  refine ⟨hTS, hST, fun x => ?_, fun y => ?_⟩
  · let y : S.domain := ⟨T x, hTS ⟨x, rfl⟩⟩
    have hgraph : (T x, S y) ∈ S.graph := S.mem_graph y
    obtain ⟨a, _, ha, hrL⟩ := (mem_graph_tsengInverseOn_iff T L hL).mp hgraph
    have hzero := eq_zero_of_mem_of_mem_orthogonal ((T.toFun.range).sub_mem ⟨x, rfl⟩ ⟨a, rfl⟩)
      (hL hrL)
    have hxk : (x : E) - (a : E) ∈ T.ker := T.sub_mem_ker_iff.mpr (sub_eq_zero.mp hzero)
    change (x : E) - S y ∈ S.toFun.rangeᗮ
    rw [← ha, hr]
    exact ker_le_orthogonal_carrier T hxk
  · let a : T.domain := ⟨S y, hST ⟨y, rfl⟩⟩
    obtain ⟨a', _, he, hy⟩ := (mem_graph_tsengInverseOn_iff T L hL).mp (S.mem_graph y)
    have hea : a' = a := Subtype.ext he
    rw [hea] at hy
    exact hL hy

/-- **Theorem 1**, Equations (9), (14)–(17) of [benIsrael2003generalized].
An operator has a Tseng inverse exactly when its domain is the orthogonal
sum of its kernel and carrier. In that case every subspace perpendicular
to the range is the kernel of a Tseng inverse. -/
theorem theorem_1 (T : E →ₗ.[𝕜] F) :
    (∃ S, IsTsengInverse T S) ↔ IsDecomposable T.domain T.ker :=
  ⟨fun ⟨_, h⟩ => ⟨T.ker_le_domain, domain_eq_ker_sup_carrier_of_isTsengInverse h⟩,
    fun h => ⟨tsengInverseOn T ⊥ bot_le, isTsengInverse_tsengInverseOn T h.2 ⊥ bot_le⟩⟩

/-- **Theorem 1**, Equations (14)–(15) of [benIsrael2003generalized].
Each prescribed perpendicular kernel is realized by a Tseng inverse,
whose domain is the sum of that kernel and the original range. -/
theorem exists_tsengInverseOn (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T)
    (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ) :
    ∃ S, IsTsengInverse T S ∧ S.domain = T.toFun.range ⊔ L ∧ S.ker = L :=
  ⟨tsengInverseOn T L hL, isTsengInverse_tsengInverseOn T hT L hL,
    (tsengInverseOn_domain T L hL).trans (congrArg (· ⊔ L) (restrictCarrier_range_of_split T hT)),
    tsengInverseOn_ker T L hL⟩

/-- **Definition 2** of [benIsrael2003generalized].
With an orthogonally decomposable domain, the maximal Tseng inverse
extends the inverse on the carrier by zero on the range's orthogonal
complement. -/
noncomputable def maximalTsengInverse (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] E :=
  tsengInverseOn T T.toFun.rangeᗮ le_rfl

/-- The maximal inverse satisfies the defining Tseng equations. -/
theorem isTsengInverse_maximalTsengInverse (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    IsTsengInverse T (maximalTsengInverse T) :=
  isTsengInverse_tsengInverseOn T hT _ le_rfl

/-- **Equation (18)** of [benIsrael2003generalized].
The maximal inverse's domain is the orthogonal sum of the range and
its orthogonal complement. -/
theorem maximalTsengInverse_domain (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    (maximalTsengInverse T).domain = T.toFun.range ⊔ T.toFun.rangeᗮ := by
  rw [maximalTsengInverse, tsengInverseOn_domain, restrictCarrier_range_of_split T hT]

/-- **Equation (19)** of [benIsrael2003generalized]. -/
theorem maximalTsengInverse_ker (T : E →ₗ.[𝕜] F) :
    (maximalTsengInverse T).ker = T.toFun.rangeᗮ :=
  tsengInverseOn_ker T _ le_rfl

/-- The maximal inverse has range equal to the original carrier. -/
theorem maximalTsengInverse_range (T : E →ₗ.[𝕜] F) :
    (maximalTsengInverse T).toFun.range = carrier T :=
  tsengInverseOn_range T _ le_rfl

/-- Every Tseng inverse is a restriction of the maximal one. -/
theorem IsTsengInverse.le_maximalTsengInverse {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) : S ≤ maximalTsengInverse T := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨y, x⟩ hxy
  have hy := LinearPMap.mem_domain_of_mem_graph hxy
  have hx : S ⟨y, hy⟩ = x := ((LinearPMap.image_iff hy).mpr hxy).symm
  have hxR : x ∈ S.toFun.range := ⟨⟨y, hy⟩, hx⟩
  have hxc : x ∈ carrier T := (lemma_3 h).2.symm ▸ hxR
  refine (mem_graph_tsengInverseOn_iff T _ le_rfl).mpr ⟨⟨x, hxc.1⟩, hxc.2, rfl, ?_⟩
  have he : (⟨S ⟨y, hy⟩, h.inverse_range_le_domain ⟨_, rfl⟩⟩ : T.domain) =
      ⟨x, hxc.1⟩ := Subtype.ext hx
  simpa only [he] using h.right ⟨y, hy⟩

private theorem tsengInverse_domain_eq_range_sup_ker {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) : S.domain = T.toFun.range ⊔ S.ker := by
  rw [← (lemma_3 h.symm).2, sup_comm]
  exact domain_eq_ker_sup_carrier_of_isTsengInverse h.symm

/-- **Exercise 10** of [benIsrael2003generalized].
Each admissible kernel determines exactly one Tseng inverse. -/
theorem exercise_9_10 {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) (L : Submodule 𝕜 F) (hL : L ≤ T.toFun.rangeᗮ)
    (hker : S.ker = L) : S = tsengInverseOn T L hL := by
  have hT := domain_eq_ker_sup_carrier_of_isTsengInverse h
  apply LinearPMap.eq_of_le_of_domain_eq
  · apply LinearPMap.le_of_le_graph
    rintro ⟨y, x⟩ hxy
    have hGraph := LinearPMap.le_graph_of_le h.le_maximalTsengInverse hxy
    obtain ⟨a, ha, hax, hz⟩ := (mem_graph_tsengInverseOn_iff T _ le_rfl).mp hGraph
    have hy : y ∈ T.toFun.range ⊔ L := by
      rw [← hker, ← tsengInverse_domain_eq_range_sup_ker h]
      exact LinearPMap.mem_domain_of_mem_graph hxy
    obtain ⟨b, hb, w, hw, hsum⟩ := Submodule.mem_sup.mp hy
    have he : b - T a = (y - T a) - w := by rw [← hsum]; abel
    have hh := eq_zero_of_mem_of_mem_orthogonal (T.toFun.range.sub_mem hb ⟨a, rfl⟩)
      (he ▸ T.toFun.rangeᗮ.sub_mem hz (hL hw))
    refine (mem_graph_tsengInverseOn_iff T L hL).mpr ⟨a, ha, hax, ?_⟩
    have hwEq : y - T a = w := by
      rw [← hsum, show b = T a from sub_eq_zero.mp hh]
      abel
    rwa [hwEq]
  · rw [tsengInverseOn_domain, restrictCarrier_range_of_split T hT,
      tsengInverse_domain_eq_range_sup_ker h, hker]

section Hilbert

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem starProjection_closure_eq_of_mem_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U : Submodule 𝕜 H) {x z : H} (hz : z ∈ U) (ho : x - z ∈ Uᗮ) :
    z = U.topologicalClosure.starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (U.le_topologicalClosure hz)
  rwa [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.triorthogonal_eq_orthogonal]

/-- The two products are the projections onto their closed ranges. -/
theorem IsTsengInverse.projections {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) :
    (∀ x : T.domain, S ⟨T x, h.range_le_domain ⟨x, rfl⟩⟩ =
      S.toFun.range.topologicalClosure.starProjection x) ∧
    (∀ y : S.domain, T ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ =
      T.toFun.range.topologicalClosure.starProjection y) :=
  ⟨fun x => starProjection_closure_eq_of_mem_orthogonal S.toFun.range ⟨_, rfl⟩ (h.left x),
    fun y => starProjection_closure_eq_of_mem_orthogonal T.toFun.range ⟨_, rfl⟩ (h.right y)⟩

/-- The two range containments and projection identities imply the defining
conditions for a Tseng inverse. -/
theorem IsTsengInverse.of_projections {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (hTS : T.toFun.range ≤ S.domain) (hST : S.toFun.range ≤ T.domain)
    (hLeft : ∀ x : T.domain, S ⟨T x, hTS ⟨x, rfl⟩⟩ =
      S.toFun.range.topologicalClosure.starProjection x)
    (hRight : ∀ y : S.domain, T ⟨S y, hST ⟨y, rfl⟩⟩ =
      T.toFun.range.topologicalClosure.starProjection y) : IsTsengInverse T S := by
  refine ⟨hTS, hST, fun x => ?_, fun y => ?_⟩
  · rw [hLeft, ← S.toFun.range.triorthogonal_eq_orthogonal,
      S.toFun.range.orthogonal_orthogonal_eq_closure]
    exact S.toFun.range.topologicalClosure.sub_starProjection_mem_orthogonal _
  · rw [hRight, ← T.toFun.range.triorthogonal_eq_orthogonal,
      T.toFun.range.orthogonal_orthogonal_eq_closure]
    exact T.toFun.range.topologicalClosure.sub_starProjection_mem_orthogonal _

omit [CompleteSpace E] in
/-- A maximal Tseng inverse has dense domain. -/
theorem dense_domain_maximalTsengInverse (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    Dense ((maximalTsengInverse T).domain : Set F) := by
  rw [maximalTsengInverse_domain T hT, Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.inf_orthogonal,
    Submodule.inf_orthogonal_eq_bot, Submodule.bot_orthogonal_eq_top]

omit [CompleteSpace E] in
/-- **Exercise 11** of [benIsrael2003generalized].
The maximal inverse is the only densely defined Tseng inverse whose
kernel is closed. -/
theorem exercise_9_11 {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}
    (h : IsTsengInverse T S) (hDense : Dense (S.domain : Set F))
    (hClosed : IsClosed (S.ker : Set F)) : S = maximalTsengInverse T := by
  have := hClosed.completeSpace_coe
  have hout : S.ker ≤ T.toFun.rangeᗮ := by
    rw [(lemma_3 h.symm).1]
    exact inf_le_right
  apply exercise_9_10 h _ le_rfl
  refine le_antisymm hout (fun z hz => ?_)
  let p : F := S.ker.starProjection z
  have hp : p ∈ S.ker := S.ker.starProjection_apply_mem z
  have hzp : z - p ∈ S.kerᗮ := S.ker.sub_starProjection_mem_orthogonal z
  have hzt : z - p ∈ T.toFun.rangeᗮ := T.toFun.rangeᗮ.sub_mem hz (hout hp)
  have hzs : z - p ∈ S.domainᗮ := by
    rw [tsengInverse_domain_eq_range_sup_ker h, ← Submodule.inf_orthogonal]
    exact ⟨hzt, hzp⟩
  simpa only [sub_eq_zero.mp (hDense.eq_zero_of_mem_orthogonal hzs)] using hp


omit [CompleteSpace F] in
private theorem domain_eq_ker_sup_carrier_of_isClosed_ker {T : E →ₗ.[𝕜] F}
    (hT : IsClosed (T.ker : Set E)) : T.domain = T.ker ⊔ carrier T :=
  (isDecomposable_of_isClosed T.ker_le_domain hT).2

omit [CompleteSpace F] in
/-- A closed operator has a maximal Tseng inverse. -/
theorem isTsengInverse_maximalTsengInverse_of_isClosed {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    IsTsengInverse T (maximalTsengInverse T) :=
  isTsengInverse_maximalTsengInverse T
    (domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed _ hT))

omit [CompleteSpace E] in
private theorem mem_graph_maximalTsengInverse_iff (T : E →ₗ.[𝕜] F) {y : F} {x : E} :
    (y, x) ∈ (maximalTsengInverse T).graph ↔
      (x, T.toFun.range.topologicalClosure.starProjection y) ∈ T.graph ∧ x ∈ T.kerᗮ := by
  rw [maximalTsengInverse, mem_graph_tsengInverseOn_iff]
  constructor
  · rintro ⟨a, ha, rfl, hres⟩
    rw [← starProjection_closure_eq_of_mem_orthogonal T.toFun.range ⟨a, rfl⟩ hres]
    exact ⟨T.mem_graph a, ha⟩
  · rintro ⟨hgraph, hxo⟩
    obtain ⟨a, ha, hpr⟩ := (T.mem_graph_iff).mp hgraph
    refine ⟨a, ha.symm ▸ hxo, ha, ?_⟩
    rw [hpr, ← T.toFun.range.triorthogonal_eq_orthogonal,
      T.toFun.range.orthogonal_orthogonal_eq_closure]
    exact T.toFun.range.topologicalClosure.sub_starProjection_mem_orthogonal y

omit [CompleteSpace E] in
/-- **Theorem 2(a)** of [benIsrael2003generalized].
The maximal Tseng inverse of a closed operator is closed. -/
theorem isClosed_maximalTsengInverse {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    (maximalTsengInverse T).IsClosed := by
  let P := T.toFun.range.topologicalClosure.starProjection
  have hgraph : ((maximalTsengInverse T).graph : Set (F × E)) =
      (fun p : F × E => (p.2, P p.1)) ⁻¹' (T.graph : Set (E × F)) ∩
        Prod.snd ⁻¹' (T.kerᗮ : Set E) := by
    ext ⟨y, x⟩
    exact mem_graph_maximalTsengInverse_iff T
  change IsClosed ((maximalTsengInverse T).graph : Set (F × E))
  rw [hgraph]
  exact (hT.preimage (continuous_snd.prodMk (P.continuous.comp continuous_fst))).inter
    (T.ker.isClosed_orthogonal.preimage continuous_snd)

omit [CompleteSpace F] in
private theorem mem_graph_adjoint_iff {T : E →ₗ.[𝕜] F} (hD : Dense (T.domain : Set E))
    {y : F} {x : E} :
    (y, x) ∈ T.adjoint.graph ↔ ∀ a : T.domain, inner 𝕜 x a = inner 𝕜 y (T a) := by
  constructor
  · intro h a
    obtain ⟨b, hb, hbx⟩ := (T.adjoint.mem_graph_iff).mp h
    simpa only [hb, hbx] using T.adjoint_isFormalAdjoint hD b a
  · intro h
    have hyd := LinearPMap.mem_adjoint_domain_of_exists (T := T) y ⟨x, h⟩
    exact (T.adjoint.mem_graph_iff).mpr ⟨⟨y, hyd⟩, rfl,
      LinearPMap.adjoint_apply_eq hD ⟨y, hyd⟩ h⟩

/-- **Theorem 2(a)–(c)** of [benIsrael2003generalized].
The maximal Tseng inverse is closed, its kernel is the adjoint kernel,
and its range is the original carrier. -/
theorem theorem_2_closed_domain_ker {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    (maximalTsengInverse T).IsClosed ∧
    (maximalTsengInverse T).domain = T.toFun.range ⊔ T.adjoint.ker ∧
    (maximalTsengInverse T).ker = T.adjoint.ker ∧
    (maximalTsengInverse T).toFun.range = carrier T := by
  rw [ker_adjoint_eq_orthogonal_range T hD]
  exact ⟨isClosed_maximalTsengInverse hT,
    maximalTsengInverse_domain T
      (domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed _ hT)),
    maximalTsengInverse_ker T, maximalTsengInverse_range T⟩

/-- **Theorem 2(d)–(e)** of [benIsrael2003generalized].
The maximal inverse gives the two orthogonal range projections. -/
theorem theorem_2_projections (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    let S := maximalTsengInverse T
    let h := isTsengInverse_maximalTsengInverse T hT
    (∀ x : T.domain, S ⟨T x, h.range_le_domain ⟨x, rfl⟩⟩ =
      S.toFun.range.topologicalClosure.starProjection x) ∧
    (∀ y : S.domain, T ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ =
      T.toFun.range.topologicalClosure.starProjection y) :=
  (isTsengInverse_maximalTsengInverse T hT).projections

omit [CompleteSpace F] in
/-- **Theorem 2(f)** of [benIsrael2003generalized].
The maximal inverse is involutive on densely defined operators with
closed kernel, including all densely defined closed operators. -/
theorem maximalTsengInverse_involutive {T : E →ₗ.[𝕜] F}
    (hD : Dense (T.domain : Set E)) (hK : IsClosed (T.ker : Set E)) :
    maximalTsengInverse (maximalTsengInverse T) = T :=
  (exercise_9_11
    (isTsengInverse_maximalTsengInverse T (domain_eq_ker_sup_carrier_of_isClosed_ker hK)).symm
    hD hK).symm


/-- A least-squares solution minimizes the residual norm over the entire
domain of the partial operator. -/
def IsOperatorLeastSquaresSolution (T : E →ₗ.[𝕜] F) (y : F) (x : T.domain) : Prop :=
  ∀ z : T.domain, ‖y - T x‖ ≤ ‖y - T z‖

omit [CompleteSpace E] [CompleteSpace F] in
/-- The residual of a least-squares solution is perpendicular to the range. -/
theorem isOperatorLeastSquaresSolution_iff (T : E →ₗ.[𝕜] F) {y : F} {x : T.domain} :
    IsOperatorLeastSquaresSolution T y x ↔ y - T x ∈ T.toFun.rangeᗮ := by
  rw [← isBestApprox_iff_mem_orthogonal T.toFun.range (show T x ∈ T.toFun.range from ⟨x, rfl⟩)]
  constructor
  · intro h
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact h z
  · intro h z
    exact h.2 (T z) ⟨z, rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- A least-squares solution exists exactly for data in the domain of the
maximal Tseng inverse. Among all solutions, that inverse returns the
unique solution of minimum norm. -/
theorem maximalTsengInverse_leastSquares (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) (y : F) :
    (∃ x : T.domain, IsOperatorLeastSquaresSolution T y x) ↔
      ∃ b : (maximalTsengInverse T).domain, (b : F) = y ∧
        ∃ x : T.domain, (x : E) = maximalTsengInverse T b ∧
          IsOperatorLeastSquaresSolution T y x ∧
          ∀ z : T.domain, IsOperatorLeastSquaresSolution T y z →
            ‖(x : E)‖ ≤ ‖(z : E)‖ ∧ (‖(x : E)‖ = ‖(z : E)‖ → x = z) := by
  let S := maximalTsengInverse T
  let h := isTsengInverse_maximalTsengInverse T hT
  constructor
  · rintro ⟨x', hx'⟩
    have hres := (isOperatorLeastSquaresSolution_iff T).mp hx'
    have hy : y ∈ S.domain := by
      rw [maximalTsengInverse_domain T hT]
      exact Submodule.mem_sup.mpr ⟨T x', ⟨x', rfl⟩, y - T x', hres, add_sub_cancel _ _⟩
    let b : S.domain := ⟨y, hy⟩
    let x : T.domain := ⟨S b, h.inverse_range_le_domain ⟨b, rfl⟩⟩
    have hx : IsOperatorLeastSquaresSolution T y x :=
      (isOperatorLeastSquaresSolution_iff T).mpr (h.right b)
    refine ⟨b, rfl, x, rfl, hx, fun z hz => ?_⟩
    have hzres := (isOperatorLeastSquaresSolution_iff T).mp hz
    have hxres := (isOperatorLeastSquaresSolution_iff T).mp hx
    have himg : T z = T x := by
      rw [← sub_eq_zero]
      apply eq_zero_of_mem_of_mem_orthogonal (T.toFun.range.sub_mem ⟨z, rfl⟩ ⟨x, rfl⟩)
      have he : T z - T x = (y - T x) - (y - T z) := by abel
      change T z - T x ∈ T.toFun.rangeᗮ
      rw [he]
      exact T.toFun.rangeᗮ.sub_mem hxres hzres
    have hk : ((z : E) - (x : E)) ∈ T.ker := T.sub_mem_ker_iff.mpr himg
    have hxo : (x : E) ∈ T.kerᗮ := by
      have hr : (x : E) ∈ carrier T := maximalTsengInverse_range T ▸ ⟨b, rfl⟩
      exact hr.2
    have hinner : inner 𝕜 (x : E) ((z : E) - (x : E)) = 0 :=
      T.ker.inner_left_of_mem_orthogonal hk hxo
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (x : E) ((z : E) - (x : E)) hinner
    have hp' : ‖(z : E)‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖(z : E) - (x : E)‖ ^ 2 := by
      simpa only [add_sub_cancel, pow_two] using hp
    refine ⟨?_, fun he => ?_⟩
    · nlinarith [norm_nonneg (x : E), norm_nonneg (z : E), sq_nonneg ‖(z : E) - (x : E)‖]
    · apply Subtype.ext
      apply (sub_eq_zero.mp ?_).symm
      apply norm_eq_zero.mp
      rw [he] at hp'
      nlinarith [sq_nonneg ‖(z : E) - (x : E)‖]
  · rintro ⟨_, _, x, _, hx, _⟩
    exact ⟨x, hx⟩

end Hilbert

section Erdelyi

private abbrev erdelyiRestriction (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] F :=
  T.domRestrict (T.ker ⊔ carrier T)

private theorem erdelyiRestriction_domain (T : E →ₗ.[𝕜] F) :
    (erdelyiRestriction T).domain = T.ker ⊔ carrier T :=
  inf_eq_left.mpr (sup_le T.ker_le_domain inf_le_left)

private theorem erdelyiRestriction_ker (T : E →ₗ.[𝕜] F) :
    (erdelyiRestriction T).ker = T.ker := by
  ext x
  constructor
  · rw [LinearPMap.mem_ker_iff, LinearPMap.mem_ker_iff]
    rintro ⟨a, rfl, h⟩
    exact ⟨⟨a, a.2.2⟩, rfl, h⟩
  · intro hx
    have hsup : x ∈ T.ker ⊔ carrier T :=
      (le_sup_left : T.ker ≤ T.ker ⊔ carrier T) hx
    have hxd : x ∈ (erdelyiRestriction T).domain := ⟨hsup, T.ker_le_domain hx⟩
    apply (LinearPMap.coe_mem_ker_iff (f := erdelyiRestriction T) (x := ⟨x, hxd⟩)).mpr
    exact (T.coe_mem_ker_iff (x := ⟨x, T.ker_le_domain hx⟩)).mp hx

private theorem erdelyiRestriction_carrier (T : E →ₗ.[𝕜] F) :
    carrier (erdelyiRestriction T) = carrier T := by
  change (erdelyiRestriction T).domain ⊓ (erdelyiRestriction T).kerᗮ = _
  rw [erdelyiRestriction_domain, erdelyiRestriction_ker]
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right inf_le_right)
  obtain ⟨k, hk, a, ha, he⟩ := Submodule.mem_sup.mp hx.1
  have hk' : k ∈ T.kerᗮ := by
    have hka : k = x - a := eq_sub_of_add_eq he
    rw [hka]
    exact T.kerᗮ.sub_mem hx.2 ha.2
  have hk0 := eq_zero_of_mem_of_mem_orthogonal hk hk'
  simpa only [hk0, zero_add] using he ▸ (show k + a ∈ carrier T by simpa [hk0] using ha)

private theorem erdelyiRestriction_decomposable (T : E →ₗ.[𝕜] F) :
    (erdelyiRestriction T).domain =
      (erdelyiRestriction T).ker ⊔ carrier (erdelyiRestriction T) := by
  rw [erdelyiRestriction_domain, erdelyiRestriction_ker, erdelyiRestriction_carrier]

private theorem erdelyiRestriction_range (T : E →ₗ.[𝕜] F) :
    (erdelyiRestriction T).toFun.range = (restrictCarrier T).toFun.range := by
  rw [← restrictCarrier_range_of_split (erdelyiRestriction T) (erdelyiRestriction_decomposable T)]
  suffices h : restrictCarrier (erdelyiRestriction T) = restrictCarrier T by rw [h]
  have hd : (restrictCarrier (erdelyiRestriction T)).domain = (restrictCarrier T).domain := by
    rw [restrictCarrier_domain, erdelyiRestriction_carrier, restrictCarrier_domain]
  exact LinearPMap.ext hd fun {_ _ _} => rfl

/-- **Definition 3**, Equation (26) of [benIsrael2003generalized].
The Erdélyi inverse is the maximal Tseng inverse of the restriction to
the orthogonal sum of the operator's kernel and carrier. -/
noncomputable def erdelyiInverse (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] E :=
  maximalTsengInverse (erdelyiRestriction T)

/-- **Theorem 4(a)** of [benIsrael2003generalized].
The two inverse constructions agree whenever Tseng inverses exist. -/
theorem erdelyiInverse_eq_maximalTsengInverse (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    erdelyiInverse T = maximalTsengInverse T := by
  have he : erdelyiRestriction T = T :=
    LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le
      ((erdelyiRestriction_domain T).trans hT.symm)
  rw [erdelyiInverse, he]

/-- **Theorem 4(b)–(c)** of [benIsrael2003generalized].
The domain is the orthogonal sum of the image of the carrier and its
orthogonal complement, and the range is the carrier. -/
theorem theorem_4_range_domain (T : E →ₗ.[𝕜] F) :
    (erdelyiInverse T).domain = (restrictCarrier T).toFun.range ⊔
      (restrictCarrier T).toFun.rangeᗮ ∧
    (erdelyiInverse T).toFun.range = carrier T ∧
    (erdelyiInverse T).ker = (restrictCarrier T).toFun.rangeᗮ := by
  unfold erdelyiInverse
  constructor
  · rw [maximalTsengInverse_domain _ (erdelyiRestriction_decomposable T), erdelyiRestriction_range]
  · rw [maximalTsengInverse_range, maximalTsengInverse_ker, erdelyiRestriction_carrier,
      erdelyiRestriction_range]
    exact ⟨rfl, rfl⟩

/-- **Equation (27)** of [benIsrael2003generalized].
The inverse graph shifts the image of a carrier vector by a vector
orthogonal to the image of the carrier. -/
theorem mem_graph_erdelyiInverse_iff (T : E →ₗ.[𝕜] F) {y : F} {x : E} :
    (y, x) ∈ (erdelyiInverse T).graph ↔
      ∃ a : T.domain, (a : E) ∈ T.kerᗮ ∧ (a : E) = x ∧
        y - T a ∈ (restrictCarrier T).toFun.rangeᗮ := by
  rw [erdelyiInverse, maximalTsengInverse, mem_graph_tsengInverseOn_iff,
    erdelyiRestriction_ker, erdelyiRestriction_range]
  constructor
  · rintro ⟨a, ha, rfl, hy⟩
    exact ⟨⟨a, a.2.2⟩, ha, rfl, hy⟩
  · rintro ⟨a, ha, rfl, hy⟩
    have hsup : (a : E) ∈ T.ker ⊔ carrier T :=
      (le_sup_right : carrier T ≤ T.ker ⊔ carrier T) ⟨a.2, ha⟩
    exact ⟨⟨a, hsup, a.2⟩, ha, rfl, hy⟩

/-- **Theorem 4(d)–(e)** of [benIsrael2003generalized].
On its restricted domain the two compositions are orthogonal projections.
For the product in the original codomain the projected subspace is the
closure of the image of the carrier. -/
theorem theorem_4_projections [CompleteSpace E] [CompleteSpace F] (T : E →ₗ.[𝕜] F) :
    let A := erdelyiRestriction T
    let S := erdelyiInverse T
    let h := isTsengInverse_maximalTsengInverse A (erdelyiRestriction_decomposable T)
    (∀ x : A.domain, S ⟨A x, h.range_le_domain ⟨x, rfl⟩⟩ =
      (carrier T).topologicalClosure.starProjection x) ∧
    (∀ y : S.domain, A ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ =
      (restrictCarrier T).toFun.range.topologicalClosure.starProjection y) := by
  intro A S h
  have hp := h.projections
  change (∀ x : A.domain, S ⟨A x, h.range_le_domain ⟨x, rfl⟩⟩ =
      S.toFun.range.topologicalClosure.starProjection x) ∧
    (∀ y : S.domain, A ⟨S y, h.inverse_range_le_domain ⟨y, rfl⟩⟩ =
      A.toFun.range.topologicalClosure.starProjection y) at hp
  rw [(theorem_4_range_domain T).2.1, erdelyiRestriction_range T] at hp
  exact hp

private theorem tsengInverse_erdelyiRestriction (T : E →ₗ.[𝕜] F) :
    IsTsengInverse (erdelyiRestriction T) (erdelyiInverse T) :=
  isTsengInverse_maximalTsengInverse _ (erdelyiRestriction_decomposable T)

private theorem erdelyiInverse_iterated_eq (T : E →ₗ.[𝕜] F) :
    erdelyiInverse (erdelyiInverse T) = maximalTsengInverse (erdelyiInverse T) :=
  erdelyiInverse_eq_maximalTsengInverse _
    (domain_eq_ker_sup_carrier_of_isTsengInverse (tsengInverse_erdelyiRestriction T).symm)

/-- **Theorem 4(f)–(h)** of [benIsrael2003generalized], with the iterated
kernel expressed as the orthogonal complement of the original carrier. -/
theorem theorem_4_iterated (T : E →ₗ.[𝕜] F) :
    (erdelyiInverse (erdelyiInverse T)).domain = carrier T ⊔ (carrier T)ᗮ ∧
    (erdelyiInverse (erdelyiInverse T)).toFun.range = (restrictCarrier T).toFun.range ∧
    (erdelyiInverse (erdelyiInverse T)).ker = (carrier T)ᗮ := by
  rw [erdelyiInverse_iterated_eq]
  constructor
  · rw [maximalTsengInverse_domain _
      (domain_eq_ker_sup_carrier_of_isTsengInverse (tsengInverse_erdelyiRestriction T).symm),
      (theorem_4_range_domain T).2.1]
  · rw [maximalTsengInverse_range, maximalTsengInverse_ker, (theorem_4_range_domain T).2.1,
      (lemma_3 (tsengInverse_erdelyiRestriction T).symm).2, erdelyiRestriction_range]
    exact ⟨rfl, rfl⟩

/-- **Theorem 4(i)** of [benIsrael2003generalized].
The iterated Erdélyi inverse extends an operator with decomposable domain. -/
theorem le_erdelyiInverse_erdelyiInverse (T : E →ₗ.[𝕜] F)
    (hT : T.domain = T.ker ⊔ carrier T) :
    T ≤ erdelyiInverse (erdelyiInverse T) := by
  rw [erdelyiInverse_iterated_eq, erdelyiInverse_eq_maximalTsengInverse T hT]
  exact (isTsengInverse_maximalTsengInverse T hT).symm.le_maximalTsengInverse

/-- **Theorem 4(j)** of [benIsrael2003generalized], with density included.
The iterated Erdélyi inverse equals the original operator precisely when
the original domain is dense and its kernel is closed. -/
theorem erdelyiInverse_erdelyiInverse_eq_iff [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) :
    erdelyiInverse (erdelyiInverse T) = T ↔
      Dense (T.domain : Set E) ∧ IsClosed (T.ker : Set E) := by
  constructor
  · intro he
    rw [← he]
    constructor
    · rw [erdelyiInverse_iterated_eq]
      exact dense_domain_maximalTsengInverse _
        (domain_eq_ker_sup_carrier_of_isTsengInverse (tsengInverse_erdelyiRestriction T).symm)
    · rw [erdelyiInverse_iterated_eq, maximalTsengInverse_ker]
      exact Submodule.isClosed_orthogonal _
  · rintro ⟨hD, hK⟩
    rw [erdelyiInverse_iterated_eq,
      erdelyiInverse_eq_maximalTsengInverse T (domain_eq_ker_sup_carrier_of_isClosed_ker hK)]
    exact maximalTsengInverse_involutive hD hK

end Erdelyi


section Bounded

variable [CompleteSpace E] [CompleteSpace F]

private abbrev asPartial (T : E →L[𝕜] F) : E →ₗ.[𝕜] F :=
  T.toLinearMap.toPMap ⊤

omit [CompleteSpace E] [CompleteSpace F] in
private theorem range_asPartial (T : E →L[𝕜] F) :
    (asPartial T).toFun.range = T.range := by
  ext y
  change (∃ x : (⊤ : Submodule 𝕜 E), T x = y) ↔ ∃ x : E, T x = y
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, trivial⟩, hx⟩⟩

omit [CompleteSpace E] [CompleteSpace F] in
private theorem ker_asPartial (T : E →L[𝕜] F) : (asPartial T).ker = T.ker := by
  rw [LinearMap.toPMap_ker, top_inf_eq]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem asPartial_isClosed (T : E →L[𝕜] F) : (asPartial T).IsClosed := by
  have he : ((asPartial T).graph : Set (E × F)) = {p | p.2 = T p.1} := by
    ext ⟨x, y⟩
    change (x, y) ∈ (asPartial T).graph ↔ y = T x
    have hx : x ∈ (asPartial T).domain := Submodule.mem_top
    exact (LinearPMap.image_iff (f := asPartial T) hx).symm
  change IsClosed ((asPartial T).graph : Set (E × F))
  rw [he]
  exact isClosed_eq continuous_snd (T.continuous.comp continuous_fst)

omit [CompleteSpace E] [CompleteSpace F] in
private def totalLinearMap (S : F →ₗ.[𝕜] E) (hS : S.domain = ⊤) : F →ₗ[𝕜] E :=
  S.toFun.comp (LinearMap.id.codRestrict S.domain fun y => by rw [hS]; trivial)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem totalLinearMap_graph (S : F →ₗ.[𝕜] E) (hS : S.domain = ⊤) :
    (totalLinearMap S hS).graph = S.graph := by
  ext ⟨y, x⟩
  have hy : y ∈ S.domain := hS ▸ Submodule.mem_top
  rw [LinearMap.mem_graph_iff, ← LinearPMap.image_iff hy]
  rfl

private theorem domain_maximal_asPartial (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    (maximalTsengInverse (asPartial T)).domain = ⊤ := by
  have hSplit := domain_eq_ker_sup_carrier_of_isClosed_ker
    (isClosed_kernel_of_isClosed _ (asPartial_isClosed T))
  rw [maximalTsengInverse_domain _ hSplit, range_asPartial]
  have := hR.completeSpace_coe
  exact T.range.sup_orthogonal_of_hasOrthogonalProjection

/-- The bounded Moore–Penrose inverse of a bounded operator with closed
range, obtained by applying the closed graph theorem to its maximal Tseng
inverse on the full target space. -/
noncomputable def boundedMoorePenroseInverse (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    F →L[𝕜] E :=
  ContinuousLinearMap.ofIsClosedGraph
    (g := totalLinearMap _ (domain_maximal_asPartial T hR)) <| by
    rw [totalLinearMap_graph]
    exact isClosed_maximalTsengInverse (asPartial_isClosed T)

/-- The bounded Moore–Penrose inverse agrees with the maximal partial
Tseng inverse, including its full domain. -/
theorem boundedMoorePenroseInverse_asPartial (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    asPartial (boundedMoorePenroseInverse T hR) = maximalTsengInverse (asPartial T) := by
  apply LinearPMap.ext (domain_maximal_asPartial T hR).symm
  intro y _ hy
  rfl

/-- The range of the bounded inverse is the orthogonal complement of the
operator's kernel. The kernel is the orthogonal complement of its range. -/
theorem boundedMoorePenroseInverse_range_ker (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    (boundedMoorePenroseInverse T hR).range = T.kerᗮ ∧
    (boundedMoorePenroseInverse T hR).ker = T.rangeᗮ := by
  constructor
  · rw [← range_asPartial (boundedMoorePenroseInverse T hR), boundedMoorePenroseInverse_asPartial,
      maximalTsengInverse_range]
    change (⊤ : Submodule 𝕜 E) ⊓ (asPartial T).kerᗮ = _
    rw [ker_asPartial, top_inf_eq]
  · rw [← ker_asPartial (boundedMoorePenroseInverse T hR), boundedMoorePenroseInverse_asPartial,
      maximalTsengInverse_ker, range_asPartial]

/-- The products with the bounded Moore–Penrose inverse are the orthogonal
projections onto the range and the orthogonal complement of the kernel. -/
theorem boundedMoorePenroseInverse_projections (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) :
    T.comp (boundedMoorePenroseInverse T hR) = T.range.topologicalClosure.starProjection ∧
    (boundedMoorePenroseInverse T hR).comp T = T.kerᗮ.starProjection := by
  let B := boundedMoorePenroseInverse T hR
  have hTS : IsTsengInverse (asPartial T) (asPartial B) := by
    rw [boundedMoorePenroseInverse_asPartial]
    exact isTsengInverse_maximalTsengInverse_of_isClosed (asPartial_isClosed T)
  have hr := (boundedMoorePenroseInverse_range_ker T hR).1
  constructor
  · ext y
    have he := hTS.projections.2 (⟨y, trivial⟩ : (asPartial B).domain)
    rw [range_asPartial T] at he
    exact he
  · ext x
    have he := hTS.left (⟨x, trivial⟩ : (asPartial T).domain)
    rw [range_asPartial B, hr] at he
    symm
    apply Submodule.eq_starProjection_of_mem_orthogonal ?_ he
    rw [← hr]
    exact ⟨T x, rfl⟩

/-- **Theorem 3(a)** of [benIsrael2003generalized].
The bounded Moore–Penrose inverse satisfies the four Penrose equations. -/
theorem boundedMoorePenroseInverse_penrose (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    let B := boundedMoorePenroseInverse T hR
    (T.comp B).comp T = T ∧ (B.comp T).comp B = B ∧
      (T.comp B).adjoint = T.comp B ∧ (B.comp T).adjoint = B.comp T := by
  intro B
  obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hTB]
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (T.range.le_topologicalClosure ⟨x, rfl⟩)
  · rw [hBT]
    ext y
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [← (boundedMoorePenroseInverse_range_ker T hR).1]
    exact ⟨y, rfl⟩
  · rw [hTB]
    exact (isSelfAdjoint_starProjection _).star_eq
  · rw [hBT]
    exact (isSelfAdjoint_starProjection _).star_eq

private theorem eq_boundedMoorePenroseInverse_of_tseng (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E)
    (h : IsTsengInverse (asPartial T) (asPartial X)) : X = boundedMoorePenroseInverse T hR := by
  have hClosed : IsClosed ((asPartial X).ker : Set F) := by rw [ker_asPartial]; exact X.isClosed_ker
  have hDense : Dense ((asPartial X).domain : Set F) := by
    change Dense ((⊤ : Submodule 𝕜 F) : Set F)
    rw [Submodule.top_coe]
    exact dense_univ
  have ph := (exercise_9_11 h hDense hClosed).trans (boundedMoorePenroseInverse_asPartial T hR).symm
  ext y
  exact (LinearPMap.ext_iff.mp ph).2 (x := y) (hf := trivial) (hg := trivial)

/-- **Theorem 3(g)** of [benIsrael2003generalized].
Projecting the two products onto their indicated ranges determines the
bounded Moore–Penrose inverse. -/
theorem theorem_3g (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    (T.comp X = T.range.topologicalClosure.starProjection ∧
      X.comp T = X.range.topologicalClosure.starProjection) ↔
        X = boundedMoorePenroseInverse T hR := by
  constructor
  · rintro ⟨hTX, hXT⟩
    apply eq_boundedMoorePenroseInverse_of_tseng T hR X
    refine IsTsengInverse.of_projections (le_top : _ ≤ (asPartial X).domain)
      (le_top : _ ≤ (asPartial T).domain) (fun x => ?_) (fun y => ?_)
    · rw [range_asPartial X]
      exact DFunLike.congr_fun hXT (x : E)
    · rw [range_asPartial T]
      exact DFunLike.congr_fun hTX (y : F)
  · rintro rfl
    obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
    refine ⟨hTB, ?_⟩
    rw [hBT]
    apply ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection
      isStarProjection_starProjection
    rw [Submodule.range_starProjection, Submodule.range_starProjection,
      (boundedMoorePenroseInverse_range_ker T hR).1]
    exact (SetLike.coe_injective T.ker.isClosed_orthogonal.closure_eq).symm

/-- **Theorem 3(a)** of [benIsrael2003generalized].
For bounded operators with closed range the four Penrose equations
characterize the bounded Moore–Penrose inverse. -/
theorem theorem_3a (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    ((T.comp X).comp T = T ∧ (X.comp T).comp X = X ∧
      (T.comp X).adjoint = T.comp X ∧ (X.comp T).adjoint = X.comp T) ↔
      X = boundedMoorePenroseInverse T hR := by
  refine ⟨?_, fun h => h.symm ▸ boundedMoorePenroseInverse_penrose T hR⟩
  rintro ⟨hTXT, hXTX, hTXs, hXTs⟩
  have hTXr : (T.comp X).range = T.range := by
    refine le_antisymm (fun y ⟨w, hw⟩ => ⟨X w, hw⟩) ?_
    rintro y ⟨x, rfl⟩
    exact ⟨T x, DFunLike.congr_fun hTXT x⟩
  have hXTr : (X.comp T).range = X.range := by
    refine le_antisymm (fun y ⟨w, hw⟩ => ⟨T w, hw⟩) ?_
    rintro y ⟨x, rfl⟩
    exact ⟨X x, DFunLike.congr_fun hXTX x⟩
  have hTXi : IsIdempotentElem (T.comp X) := by
    change (T.comp X).comp (T.comp X) = T.comp X
    ext y
    exact DFunLike.congr_fun hTXT (X y)
  have hXTi : IsIdempotentElem (X.comp T) := by
    change (X.comp T).comp (X.comp T) = X.comp T
    ext x
    exact DFunLike.congr_fun hXTX (T x)
  have iTX : IsStarProjection (T.comp X) := ⟨hTXi, hTXs⟩
  have iXT : IsStarProjection (X.comp T) := ⟨hXTi, hXTs⟩
  have hc : (X.comp T).range.topologicalClosure = (X.comp T).range := by
    have he : ((X.comp T).range : Set E) = {x | (X.comp T) x = x} := by
      ext x
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (X.comp T) z = x := hz
        change (X.comp T) x = x
        exact hz' ▸ DFunLike.congr_fun hXTi z
      · intro hx
        exact ⟨x, hx⟩
    have hClosed : IsClosed ((X.comp T).range : Set E) := by
      rw [he]
      exact isClosed_eq (X.comp T).continuous continuous_id
    exact SetLike.coe_injective hClosed.closure_eq
  apply (theorem_3g T hR X).mp
  constructor
  · apply ContinuousLinearMap.IsStarProjection.ext iTX (isStarProjection_starProjection)
    rw [hTXr, Submodule.range_starProjection,
      (SetLike.coe_injective hR.closure_eq : T.range.topologicalClosure = T.range)]
  · apply ContinuousLinearMap.IsStarProjection.ext iXT (isStarProjection_starProjection)
    rw [Submodule.range_starProjection, ← hXTr, hc]


omit [CompleteSpace E] in
private theorem comp_rangeProjection_eq_self_of_ker_le (T : E →L[𝕜] F) (X : F →L[𝕜] E)
    (hX : T.rangeᗮ ≤ X.ker) : X.comp T.range.topologicalClosure.starProjection = X := by
  ext y
  have hr : y - T.range.topologicalClosure.starProjection y ∈ T.rangeᗮ := by
    rw [← T.range.triorthogonal_eq_orthogonal, T.range.orthogonal_orthogonal_eq_closure]
    exact T.range.topologicalClosure.sub_starProjection_mem_orthogonal y
  have hX' : X (y - T.range.topologicalClosure.starProjection y) = 0 := hX hr
  rw [_root_.map_sub, sub_eq_zero] at hX'
  exact hX'.symm

private theorem eq_boundedMoorePenroseInverse_of_comp_eq_of_range_le
    (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E)
    (hTX : T.comp X = T.range.topologicalClosure.starProjection) (hX : X.range ≤ T.kerᗮ) :
    X = boundedMoorePenroseInverse T hR := by
  let B := boundedMoorePenroseInverse T hR
  obtain ⟨hTB, _⟩ := boundedMoorePenroseInverse_projections T hR
  have hBrange := (boundedMoorePenroseInverse_range_ker T hR).1
  ext y
  have hk : X y - B y ∈ T.ker := by
    change T (X y - B y) = 0
    rw [_root_.map_sub, sub_eq_zero]
    exact (DFunLike.congr_fun hTX y).trans (DFunLike.congr_fun hTB y).symm
  have hko : X y - B y ∈ T.kerᗮ :=
    T.kerᗮ.sub_mem (hX ⟨y, rfl⟩) (hBrange ▸ ⟨y, rfl⟩)
  exact sub_eq_zero.mp (eq_zero_of_mem_of_mem_orthogonal hk hko)

/-- **Theorem 3(b)** of [benIsrael2003generalized].
The target range projection together with the adjoint kernel condition
characterizes the bounded Moore–Penrose inverse. -/
theorem theorem_3b (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    (T.comp X = T.range.topologicalClosure.starProjection ∧ X.adjoint.ker = T.ker) ↔
      X = boundedMoorePenroseInverse T hR := by
  constructor
  · rintro ⟨hTX, hX⟩
    apply eq_boundedMoorePenroseInverse_of_comp_eq_of_range_le T hR X hTX
    rw [← hX, ← X.orthogonal_range]
    exact X.range.le_orthogonal_orthogonal
  · rintro rfl
    have hX := (boundedMoorePenroseInverse_range_ker T hR).1
    refine ⟨(boundedMoorePenroseInverse_projections T hR).1, ?_⟩
    rw [← ContinuousLinearMap.orthogonal_range, hX]
    have := T.isClosed_ker.completeSpace_coe
    exact T.ker.orthogonal_orthogonal

private theorem adjointRangeProjection_eq_kerProjection (T : E →L[𝕜] F) :
    T.adjoint.range.topologicalClosure.starProjection = T.kerᗮ.starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection
    isStarProjection_starProjection
  rw [Submodule.range_starProjection, Submodule.range_starProjection, T.orthogonal_ker]

/-- **Theorem 3(c)** of [benIsrael2003generalized].
The two fixed range projections and the outer inverse equation
characterize the bounded Moore–Penrose inverse. -/
theorem theorem_3c (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    (T.comp X = T.range.topologicalClosure.starProjection ∧
      X.comp T = T.adjoint.range.topologicalClosure.starProjection ∧ (X.comp T).comp X = X) ↔
      X = boundedMoorePenroseInverse T hR := by
  rw [adjointRangeProjection_eq_kerProjection]
  constructor
  · rintro ⟨hTX, hXT, hXTX⟩
    apply eq_boundedMoorePenroseInverse_of_comp_eq_of_range_le T hR X hTX
    rintro _ ⟨y, rfl⟩
    change X y ∈ T.kerᗮ
    have hp : T.kerᗮ.starProjection (X y) = X y := by
      rw [← hXT]
      exact DFunLike.congr_fun hXTX y
    exact Submodule.starProjection_eq_self_iff.mp hp
  · rintro rfl
    obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
    exact ⟨hTB, hBT, (boundedMoorePenroseInverse_penrose T hR).2.1⟩

/-- **Theorem 3(f)** of [benIsrael2003generalized].
The source projection and the kernel of the unknown inverse determine
the bounded Moore–Penrose inverse. -/
theorem theorem_3f (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    (X.comp T = T.adjoint.range.topologicalClosure.starProjection ∧ X.ker = T.adjoint.ker) ↔
      X = boundedMoorePenroseInverse T hR := by
  rw [adjointRangeProjection_eq_kerProjection, ← T.orthogonal_range]
  constructor
  · rintro ⟨hXT, hX⟩
    let B := boundedMoorePenroseInverse T hR
    obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
    calc
      X = X.comp T.range.topologicalClosure.starProjection :=
        (comp_rangeProjection_eq_self_of_ker_le T X (le_of_eq hX.symm)).symm
      _ = (X.comp T).comp B := by rw [← hTB]; rfl
      _ = (B.comp T).comp B := by rw [hXT, hBT]
      _ = B := (boundedMoorePenroseInverse_penrose T hR).2.1
  · rintro rfl
    exact ⟨(boundedMoorePenroseInverse_projections T hR).2,
      (boundedMoorePenroseInverse_range_ker T hR).2⟩

/-- **Theorem 3(e)** of [benIsrael2003generalized].
The inverse is determined by inverting on the adjoint range and
vanishing on the adjoint kernel. -/
theorem theorem_3e (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    ((∀ x ∈ T.adjoint.range, X (T x) = x) ∧ (∀ y ∈ T.adjoint.ker, X y = 0)) ↔
      X = boundedMoorePenroseInverse T hR := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    have hQ : X.comp T = T.kerᗮ.starProjection := by
      have hfix : IsClosed {x | X (T x) = x} :=
        isClosed_eq (X.continuous.comp T.continuous) continuous_id
      have hCL : (T.kerᗮ : Set E) ⊆ {x | X (T x) = x} := by
        rw [T.orthogonal_ker]
        exact closure_minimal hLeft hfix
      ext x
      let q := T.kerᗮ.starProjection x
      have hq : q ∈ T.kerᗮ := T.kerᗮ.starProjection_apply_mem x
      have hRes : x - q ∈ T.ker := by
        have := T.isClosed_ker.completeSpace_coe
        rw [← T.ker.orthogonal_orthogonal]
        exact T.kerᗮ.sub_starProjection_mem_orthogonal x
      have hTq : T x = T q := by
        have h := (LinearMap.mem_ker.mp hRes : T (x - q) = 0)
        rwa [_root_.map_sub, sub_eq_zero] at h
      change X (T x) = q
      rw [hTq]
      exact hCL hq
    have hTX : X = boundedMoorePenroseInverse T hR := by
      let B := boundedMoorePenroseInverse T hR
      obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
      have hp := comp_rangeProjection_eq_self_of_ker_le T X
        (by rwa [T.orthogonal_range])
      calc
        X = X.comp T.range.topologicalClosure.starProjection := hp.symm
        _ = (X.comp T).comp B := by rw [← hTB]; rfl
        _ = (B.comp T).comp B := by rw [hQ, hBT]
        _ = B := (boundedMoorePenroseInverse_penrose T hR).2.1
    exact hTX
  · rintro rfl
    have pr := (boundedMoorePenroseInverse_projections T hR).2
    have hk := (boundedMoorePenroseInverse_range_ker T hR).2
    constructor
    · intro x hx
      rw [← ContinuousLinearMap.comp_apply, pr]
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [T.orthogonal_ker]
      exact T.adjoint.range.le_topologicalClosure hx
    · intro y hy
      change y ∈ (boundedMoorePenroseInverse T hR).ker
      rw [hk, T.orthogonal_range]
      exact hy

/-- **Theorem 3(d)** of [benIsrael2003generalized].
The two normal equation identities characterize the bounded
Moore–Penrose inverse. -/
theorem theorem_3d (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) (X : F →L[𝕜] E) :
    ((X.comp T).comp T.adjoint = T.adjoint ∧ (X.comp X.adjoint).comp T.adjoint = X) ↔
      X = boundedMoorePenroseInverse T hR := by
  constructor
  · rintro ⟨hXT, hXX⟩
    apply (theorem_3e T hR X).mp
    constructor
    · rintro _ ⟨x, rfl⟩
      exact DFunLike.congr_fun hXT x
    · intro y hy
      have he := DFunLike.congr_fun hXX y
      change X (X.adjoint (T.adjoint y)) = X y at he
      have hy' : T.adjoint y = 0 := hy
      rw [hy', _root_.map_zero, _root_.map_zero] at he
      exact he.symm
  · rintro rfl
    let B := boundedMoorePenroseInverse T hR
    have he := (theorem_3e T hR B).mpr rfl
    refine ⟨?_, ?_⟩
    · ext y
      exact he.1 _ ⟨y, rfl⟩
    · have hstar := (boundedMoorePenroseInverse_penrose T hR).2.2.1
      change (T.comp B).adjoint = T.comp B at hstar
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.adjoint_comp, hstar]
      exact (boundedMoorePenroseInverse_penrose T hR).2.1

end Bounded

section Adjoint

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem inner_starProjection_orthogonal_ker (T : E →ₗ.[𝕜] F)
    (x : E) (a : T.domain) (ha : (a : E) ∈ T.kerᗮ) :
    inner 𝕜 (T.kerᗮ.starProjection x) (a : E) = inner 𝕜 x (a : E) := by
  rw [T.kerᗮ.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr ha]

private theorem maximalTsengInverse_adjoint_aux {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E))
    (hKer : T.adjoint.toFun.rangeᗮ = T.ker) :
    (maximalTsengInverse T).adjoint = maximalTsengInverse T.adjoint := by
  let S := maximalTsengInverse T
  have hSplit := domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed _ hT)
  have hS := dense_domain_maximalTsengInverse T hSplit
  have hK := ker_adjoint_eq_orthogonal_range T hD
  apply LinearPMap.eq_of_eq_graph
  ext ⟨u, v⟩
  rw [mem_graph_adjoint_iff hS, show maximalTsengInverse T.adjoint =
    tsengInverseOn T.adjoint T.adjoint.toFun.rangeᗮ le_rfl from rfl,
      mem_graph_tsengInverseOn_iff, hK, hKer]
  constructor
  · intro h
    have hvo : v ∈ T.toFun.rangeᗮᗮ := by
      apply (Submodule.mem_orthogonal' _ _).mpr
      intro z hz
      have hzD : z ∈ S.domain := S.ker_le_domain (maximalTsengInverse_ker T ▸ hz)
      have hz0 : S ⟨z, hzD⟩ = 0 := S.coe_mem_ker_iff.mp (maximalTsengInverse_ker T ▸ hz)
      have hh := h ⟨z, hzD⟩
      change inner 𝕜 v z = inner 𝕜 u (S ⟨z, hzD⟩) at hh
      rwa [hz0, inner_zero_right] at hh
    let q := T.kerᗮ.starProjection u
    have hq : ∀ a : T.domain, inner 𝕜 q a = inner 𝕜 v (T a) := by
      intro a
      have ha' : (a : E) ∈ T.ker ⊔ carrier T := hSplit ▸ a.2
      obtain ⟨k, hk, x, hx, he⟩ := Submodule.mem_sup.mp ha'
      let k' : T.domain := ⟨k, T.ker_le_domain hk⟩
      let x' : T.domain := ⟨x, hx.1⟩
      have hk' : T k' = 0 := T.coe_mem_ker_iff.mp hk
      have hae : a = k' + x' := Subtype.ext he.symm
      have htx : (T x', x) ∈ S.graph :=
        (mem_graph_tsengInverseOn_iff T _ le_rfl).mpr ⟨x', hx.2, rfl, by simp⟩
      have hd := LinearPMap.mem_domain_of_mem_graph htx
      have hT0 : S ⟨T x', hd⟩ = x := ((LinearPMap.image_iff hd).mpr htx).symm
      have hInner : inner 𝕜 u x = inner 𝕜 v (T x') := by
        have hh := (h ⟨T x', hd⟩).symm
        change inner 𝕜 u (S ⟨T x', hd⟩) = inner 𝕜 v (T x') at hh
        rwa [hT0] at hh
      have hqk : inner 𝕜 q k = 0 :=
        T.ker.inner_left_of_mem_orthogonal hk (T.kerᗮ.starProjection_apply_mem u)
      calc
        inner 𝕜 q (a : E) = inner 𝕜 q k + inner 𝕜 q x := by rw [← he, inner_add_right]
        _ = inner 𝕜 v (T x') := by
          rw [hqk, zero_add]
          exact (inner_starProjection_orthogonal_ker T u x' hx.2).trans hInner
        _ = inner 𝕜 v (T a) := by rw [hae, T.map_add, hk', zero_add]
    have hvD := LinearPMap.mem_adjoint_domain_of_exists (T := T) v ⟨q, hq⟩
    let b : T.adjoint.domain := ⟨v, hvD⟩
    have hqEq : T.adjoint b = q := LinearPMap.adjoint_apply_eq hD b hq
    have hqo : u - q ∈ T.ker := by
      have hClosed := isClosed_kernel_of_isClosed _ hT
      have : CompleteSpace T.ker := hClosed.completeSpace_coe
      rw [← Submodule.orthogonal_orthogonal T.ker]
      exact T.kerᗮ.sub_starProjection_mem_orthogonal u
    exact ⟨b, hvo, rfl, hqEq.symm ▸ hqo⟩
  · rintro ⟨b, hb, rfl, hu⟩ y
    obtain ⟨a, ha, has, hy⟩ := (mem_graph_tsengInverseOn_iff T _ le_rfl).mp (S.mem_graph y)
    have hb0 : inner 𝕜 (b : F) ((y : F) - T a) = 0 :=
      T.toFun.rangeᗮ.inner_left_of_mem_orthogonal hy hb
    have hu0 : inner 𝕜 (u - T.adjoint b) (a : E) = 0 :=
      T.ker.inner_right_of_mem_orthogonal hu ha
    have eqY : inner 𝕜 (b : F) (y : F) = inner 𝕜 (b : F) (T a) := by
      rw [inner_sub_right] at hb0
      exact sub_eq_zero.mp hb0
    have eqU : inner 𝕜 u (a : E) = inner 𝕜 (T.adjoint b) (a : E) := by
      rw [inner_sub_left] at hu0
      exact sub_eq_zero.mp hu0
    rw [← has, eqU, eqY, T.adjoint_isFormalAdjoint hD b a]

omit [CompleteSpace F] in
/-- The kernel of the maximal inverse of the adjoint is the orthogonal
complement of the adjoint range. -/
theorem maximalTsengInverse_adjoint_ker (T : E →ₗ.[𝕜] F) :
    (maximalTsengInverse T.adjoint).ker = T.adjoint.toFun.rangeᗮ :=
  maximalTsengInverse_ker T.adjoint


/-- **Theorem 2(f)–(h)** of [benIsrael2003generalized].
For a densely defined closed operator the maximal inverse is involutive,
commutes with taking adjoints, and the inverse of the adjoint has the
same kernel as the original operator. -/
theorem theorem_2_involution_adjoint {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    maximalTsengInverse (maximalTsengInverse T) = T ∧
    (maximalTsengInverse T).adjoint = maximalTsengInverse T.adjoint ∧
    (maximalTsengInverse T.adjoint).ker = T.ker :=
  ⟨maximalTsengInverse_involutive hD (isClosed_kernel_of_isClosed T hT),
    maximalTsengInverse_adjoint_aux hT hD (orthogonal_range_adjoint_eq_ker T hD hT),
    (maximalTsengInverse_adjoint_ker T).trans (orthogonal_range_adjoint_eq_ker T hD hT)⟩

/-- **Theorem 4(k)** of [benIsrael2003generalized], under closedness.
For a densely defined closed operator the Erdélyi inverse commutes with
taking adjoints. -/
theorem theorem_4_adjoint {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    (erdelyiInverse T).adjoint = erdelyiInverse T.adjoint := by
  rw [erdelyiInverse_eq_maximalTsengInverse _ (domain_eq_ker_sup_carrier_of_isClosed_ker
        (isClosed_kernel_of_isClosed T hT)),
      erdelyiInverse_eq_maximalTsengInverse _ (domain_eq_ker_sup_carrier_of_isClosed_ker
        (isClosed_kernel_of_isClosed T.adjoint (LinearPMap.adjoint_isClosed hD)))]
  exact (theorem_2_involution_adjoint hT hD).2.1

end Adjoint


section Exercises

/-- **Exercise 13** of [benIsrael2003generalized].
A closed operator has closed range exactly when its maximal Tseng inverse
obeys a uniform norm bound on its domain. -/
theorem exercise_9_13 [CompleteSpace E] [CompleteSpace F] {T : E →ₗ.[𝕜] F}
    (hT : T.IsClosed) :
    IsClosed (T.toFun.range : Set F) ↔ IsBoundedOperator (maximalTsengInverse T) := by
  let S := maximalTsengInverse T
  have hSplit := domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed _ hT)
  constructor
  · intro hR
    have := hR.completeSpace_coe
    have htop : S.domain = ⊤ :=
      (maximalTsengInverse_domain T hSplit).trans
        T.toFun.range.sup_orthogonal_of_hasOrthogonalProjection
    let B := ContinuousLinearMap.ofIsClosedGraph (g := totalLinearMap S htop) (by
      rw [totalLinearMap_graph]
      exact isClosed_maximalTsengInverse hT)
    refine ⟨‖B‖, fun y => ?_⟩
    exact B.le_opNorm (y : F)
  · rintro ⟨C, hC⟩
    rw [← restrictCarrier_range_of_split T hSplit]
    apply (restrictCarrier_isClosed _ hT).isClosed_range_of_norm_le (C := C)
    intro x
    let a : T.domain := ⟨x, x.2.2⟩
    have hxGraph : (T a, (a : E)) ∈ S.graph :=
      (mem_graph_tsengInverseOn_iff T _ le_rfl).mpr ⟨a, x.2.1, rfl, by simp⟩
    have hy := LinearPMap.mem_domain_of_mem_graph hxGraph
    have he := ((LinearPMap.image_iff hy).mpr hxGraph).symm
    have hs := hC ⟨T a, hy⟩
    change ‖S ⟨T a, hy⟩‖ ≤ C * ‖T a‖ at hs
    rw [he] at hs
    exact hs

/-- **Exercise 15**, Equations (28)–(29) of [benIsrael2003generalized].
An extension with the closure of the old kernel as kernel can exist only
when the old domain meets that closure in the old kernel. -/
theorem exercise_9_15 {T U : E →ₗ.[𝕜] F} (hTU : T ≤ U)
    (hU : U.ker = T.ker.topologicalClosure) :
    T.domain ⊓ T.ker.topologicalClosure = T.ker := by
  refine le_antisymm (fun x hx => ?_) (le_inf T.ker_le_domain T.ker.le_topologicalClosure)
  let a : T.domain := ⟨x, hx.1⟩
  let b : U.domain := ⟨x, hTU.1 hx.1⟩
  have hb : U b = 0 := U.coe_mem_ker_iff.mp (hU.symm ▸ hx.2)
  exact T.coe_mem_ker_iff.mpr ((hTU.2 (x := a) (y := b) rfl).trans hb)

/-- The condition in Exercise 15 is also sufficient. The closure of the
kernel is added to the domain, and the operator vanishes on it. -/
theorem exists_extension_with_closed_kernel_iff (T : E →ₗ.[𝕜] F) :
    (∃ U : E →ₗ.[𝕜] F, T ≤ U ∧ U.domain = T.domain ⊔ T.ker.topologicalClosure ∧
      U.ker = T.ker.topologicalClosure) ↔ T.domain ⊓ T.ker.topologicalClosure = T.ker := by
  constructor
  · rintro ⟨U, hTU, _, hU⟩
    exact exercise_9_15 hTU hU
  · intro hK
    let L := T.ker.topologicalClosure
    let Z : E →ₗ.[𝕜] F := (0 : E →ₗ[𝕜] F).toPMap L
    have hAgree (a : T.domain) (b : Z.domain) (hab : (a : E) = b) : T a = Z b := by
      have ha : (a : E) ∈ T.ker := hK ▸ ⟨a.2, hab.symm ▸ b.2⟩
      exact T.coe_mem_ker_iff.mp ha
    let U := T.sup Z hAgree
    have hZU : Z ≤ U := LinearPMap.right_le_sup T Z hAgree
    have hLU : L ≤ U.ker := fun z hz => by
      let a : Z.domain := ⟨z, hz⟩
      let b : U.domain := ⟨z, hZU.1 hz⟩
      apply (U.coe_mem_ker_iff (x := b)).mpr
      exact (hZU.2 (x := a) (y := b) rfl).symm
    refine ⟨U, LinearPMap.left_le_sup T Z hAgree, rfl,
      le_antisymm (fun z hz => ?_) hLU⟩
    have hzU : z ∈ U.domain := U.ker_le_domain hz
    have hz' : z ∈ T.domain ⊔ L := hzU
    obtain ⟨x, hx, k, hk, he⟩ := Submodule.mem_sup.mp hz'
    have hUx : U ⟨z, hzU⟩ = T ⟨x, hx⟩ :=
      (LinearPMap.sup_apply hAgree ⟨x, hx⟩ ⟨k, hk⟩ ⟨z, hz'⟩ he).trans (add_zero _)
    have hTx : T ⟨x, hx⟩ = 0 := hUx.symm.trans (U.coe_mem_ker_iff.mp hz)
    rw [← he]
    exact L.add_mem (T.ker.le_topologicalClosure (T.coe_mem_ker_iff.mpr hTx)) hk

end Exercises

section GramOperators

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem mem_graph_partialComp_iff {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (S : F →ₗ.[𝕜] G) (T : E →ₗ.[𝕜] F) {x : E} {z : G} :
    (x, z) ∈ (partialComp S T).graph ↔ ∃ y : F, (x, y) ∈ T.graph ∧ (y, z) ∈ S.graph := by
  constructor
  · intro hg
    have hx := LinearPMap.mem_domain_of_mem_graph hg
    obtain ⟨hTx, hSt⟩ := (partialComp_mem_domain S T x).mp hx
    have h := ((LinearPMap.image_iff hx).mpr hg).symm
    rw [partialComp_apply S T x hTx hSt] at h
    exact ⟨T ⟨x, hTx⟩, T.mem_graph ⟨x, hTx⟩, (LinearPMap.image_iff hSt).mp h.symm⟩
  · rintro ⟨y, hTg, hSg⟩
    have hx := LinearPMap.mem_domain_of_mem_graph hTg
    have hy := LinearPMap.mem_domain_of_mem_graph hSg
    have he := ((LinearPMap.image_iff hx).mpr hTg).symm
    have hTy : T ⟨x, hx⟩ ∈ S.domain := he.symm ▸ hy
    have hz := ((LinearPMap.image_iff hy).mpr hSg).symm
    have hd := (partialComp_mem_domain S T x).mpr ⟨hx, hTy⟩
    apply (LinearPMap.image_iff hd).mp
    rw [partialComp_apply S T x hx hTy]
    exact (congrArg S (Subtype.ext he)).trans hz |>.symm

omit [CompleteSpace F] in
private theorem gramOperator_pairing (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E))
    (z : (partialComp T.adjoint T).domain) (x : T.domain) :
    ∃ a : T.domain, (a : E) = (z : E) ∧
      inner 𝕜 (partialComp T.adjoint T z) (x : E) = inner 𝕜 (T a) (T x) := by
  obtain ⟨hd, ha⟩ := (partialComp_mem_domain T.adjoint T (z : E)).mp z.2
  let a : T.domain := ⟨z, hd⟩
  refine ⟨a, rfl, ?_⟩
  rw [show partialComp T.adjoint T z = T.adjoint ⟨T a, ha⟩ from
    partialComp_apply T.adjoint T (z : E) hd ha]
  exact T.adjoint_isFormalAdjoint hD ⟨T a, ha⟩ x

omit [CompleteSpace F] in
private theorem gramOperator_ker (T : E →ₗ.[𝕜] F) (hD : Dense (T.domain : Set E)) :
    (partialComp T.adjoint T).ker = T.ker := by
  let G := partialComp T.adjoint T
  ext x
  rw [LinearPMap.mem_ker_iff, LinearPMap.mem_ker_iff]
  constructor
  · rintro ⟨z, rfl, hz⟩
    obtain ⟨hd, _⟩ := (partialComp_mem_domain T.adjoint T (z : E)).mp z.2
    let a : T.domain := ⟨z, hd⟩
    obtain ⟨b, hb, he⟩ := gramOperator_pairing T hD z a
    have hba : b = a := Subtype.ext hb
    change G z = 0 at hz
    change inner 𝕜 (G z) (a : E) = inner 𝕜 (T b) (T a) at he
    rw [hba, hz, inner_zero_left] at he
    exact ⟨a, rfl, inner_self_eq_zero.mp he.symm⟩
  · rintro ⟨a, rfl, ha⟩
    have hd : T a ∈ T.adjoint.domain := ha.symm ▸ T.adjoint.domain.zero_mem
    refine ⟨⟨a, (partialComp_mem_domain T.adjoint T (a : E)).mpr ⟨a.2, hd⟩⟩, rfl, ?_⟩
    rw [partialComp_apply T.adjoint T (a : E) a.2 hd]
    have he : (⟨T a, hd⟩ : T.adjoint.domain) = 0 := Subtype.ext ha
    rw [he, LinearPMap.map_zero]

private theorem gramOperator_orthogonal_range (T : E →ₗ.[𝕜] F)
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    (partialComp T.adjoint T).toFun.rangeᗮ = T.ker := by
  let G := partialComp T.adjoint T
  have hS : IsSelfAdjoint G := (gramOperators_nonnegative T hT hD).1.1
  have hA : G.adjoint = G := hS.star_eq
  rw [← ker_adjoint_eq_orthogonal_range G hS.dense_domain, hA]
  exact gramOperator_ker T hD

private theorem maximalTsengInverse_gramOperator (T : E →ₗ.[𝕜] F)
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    maximalTsengInverse (partialComp T.adjoint T) =
      partialComp (maximalTsengInverse T) (maximalTsengInverse T.adjoint) := by
  let G := partialComp T.adjoint T
  let S := maximalTsengInverse T
  let V := maximalTsengInverse T.adjoint
  have hGker := gramOperator_ker T hD
  have hGorth := gramOperator_orthogonal_range T hT hD
  have hTk := ker_adjoint_eq_orthogonal_range T hD
  have hTo := orthogonal_range_adjoint_eq_ker T hD hT
  apply LinearPMap.eq_of_eq_graph
  ext ⟨y, x⟩
  change (y, x) ∈ (maximalTsengInverse G).graph ↔ (y, x) ∈ (partialComp S V).graph
  rw [mem_graph_partialComp_iff,
    show maximalTsengInverse G = tsengInverseOn G G.toFun.rangeᗮ le_rfl from rfl,
    mem_graph_tsengInverseOn_iff, hGker, hGorth]
  constructor
  · rintro ⟨z, hzo, rfl, hz⟩
    obtain ⟨ha, hb⟩ := (partialComp_mem_domain T.adjoint T (z : E)).mp z.2
    let a : T.domain := ⟨z, ha⟩
    let b : T.adjoint.domain := ⟨T a, hb⟩
    have hGz : G z = T.adjoint b := partialComp_apply T.adjoint T (z : E) ha hb
    refine ⟨T a, (mem_graph_tsengInverseOn_iff T.adjoint _ le_rfl).mpr ⟨b, ?_, rfl, ?_⟩,
      (mem_graph_tsengInverseOn_iff T _ le_rfl).mpr ⟨a, hzo, rfl, by simp⟩⟩
    · rw [hTk]
      exact T.toFun.range.le_orthogonal_orthogonal ⟨a, rfl⟩
    · rw [hTo, ← hGz]
      exact hz
  · rintro ⟨v, hv, hx⟩
    obtain ⟨b, hbo, hbv, hy⟩ := (mem_graph_tsengInverseOn_iff T.adjoint _ le_rfl).mp hv
    obtain ⟨a, hao, rfl, hres⟩ := (mem_graph_tsengInverseOn_iff T _ le_rfl).mp hx
    have hv' : v = T a := by
      have hvo : v ∈ T.toFun.rangeᗮᗮ := by rwa [hTk, hbv] at hbo
      have hTo' : T a ∈ T.toFun.rangeᗮᗮ := T.toFun.range.le_orthogonal_orthogonal ⟨a, rfl⟩
      exact sub_eq_zero.mp (eq_zero_of_mem_of_mem_orthogonal hres
        (T.toFun.rangeᗮᗮ.sub_mem hvo hTo'))
    have hTa : T a ∈ T.adjoint.domain := (hbv.trans hv') ▸ b.2
    let z : G.domain := ⟨a, (partialComp_mem_domain T.adjoint T (a : E)).mpr ⟨a.2, hTa⟩⟩
    have hGe : G z = T.adjoint b := by
      rw [partialComp_apply T.adjoint T (a : E) a.2 hTa]
      exact congrArg T.adjoint (Subtype.ext (hbv.trans hv').symm)
    refine ⟨z, hao, rfl, ?_⟩
    rwa [hGe, ← hTo]

/-- **Theorem 2(i)–(j)** of [benIsrael2003generalized].
The two Gram operators and their maximal inverses are nonnegative.
The inverse identities are equalities of partial maps, including the
domains of the compositions. -/
theorem theorem_2_gramOperators (T : E →ₗ.[𝕜] F)
    (hT : T.IsClosed) (hD : Dense (T.domain : Set E)) :
    let A := partialComp T.adjoint T
    let B := partialComp T T.adjoint
    let S := maximalTsengInverse T
    let V := maximalTsengInverse T.adjoint
    IsNonnegativeOperator A ∧ IsNonnegativeOperator B ∧
    A.ker = T.ker ∧ B.ker = T.adjoint.ker ∧
    maximalTsengInverse A = partialComp S V ∧ maximalTsengInverse B = partialComp V S ∧
    IsNonnegativeOperator (partialComp S V) ∧ IsNonnegativeOperator (partialComp V S) := by
  intro A B S V
  have hTa := LinearPMap.adjoint_isClosed hD
  have hdTa := dense_adjoint_domain_of_isClosable T hD hT.isClosable
  have hTaTa : T.adjoint.adjoint = T :=
    (closure_eq_adjoint_adjoint T hD hT.isClosable).symm.trans
      (LinearPMap.eq_of_eq_graph (by rw [← hT.isClosable.graph_closure_eq_closure_graph]; exact
        hT.submodule_topologicalClosure_eq))
  have hBS : partialComp T.adjoint.adjoint T.adjoint = B := by rw [hTaTa]
  have hVA : S.adjoint = V := (theorem_2_involution_adjoint hT hD).2.1
  have hSD := dense_domain_maximalTsengInverse T
    (domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed T hT))
  have hVD := dense_domain_maximalTsengInverse T.adjoint
    (domain_eq_ker_sup_carrier_of_isClosed_ker (isClosed_kernel_of_isClosed T.adjoint hTa))
  have hVS : V.adjoint = S := by
    rw [(theorem_2_involution_adjoint hTa hdTa).2.1, hTaTa]
  have hAB := gramOperators_nonnegative T hT hD
  refine ⟨hAB.1, hAB.2.2.1, gramOperator_ker T hD, ?_,
    maximalTsengInverse_gramOperator T hT hD, ?_, ?_, ?_⟩
  · rw [← hBS]
    exact gramOperator_ker T.adjoint hdTa
  · have he := maximalTsengInverse_gramOperator T.adjoint hTa hdTa
    rw [hTaTa] at he
    exact he
  · rw [← hVS]
    exact (gramOperators_nonnegative V (isClosed_maximalTsengInverse hTa) hVD).1
  · rw [← hVA]
    exact (gramOperators_nonnegative S (isClosed_maximalTsengInverse hT) hSD).1

end GramOperators


section BoundedExercises

variable [CompleteSpace E] [CompleteSpace F]

private theorem adjoint_range_eq_orthogonal_ker_of_isClosed_range (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) : T.adjoint.range = T.kerᗮ := by
  let B := boundedMoorePenroseInverse T hR
  have hp : B.comp T = T.kerᗮ.starProjection := (boundedMoorePenroseInverse_projections T hR).2
  have ht : T.adjoint.comp B.adjoint = T.kerᗮ.starProjection := by
    rw [← ContinuousLinearMap.adjoint_comp, hp]
    exact (isSelfAdjoint_starProjection _).star_eq
  refine le_antisymm (T.adjoint.range.le_topologicalClosure.trans (le_of_eq T.orthogonal_ker.symm))
    (fun x hx => ?_)
  refine ⟨B.adjoint x, ?_⟩
  have he := DFunLike.congr_fun ht x
  exact he.trans (Submodule.starProjection_eq_self_iff.mpr hx)

private theorem range_adjoint_comp_self_of_isClosed_range (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) : (T.adjoint.comp T).range = T.adjoint.range := by
  let B := boundedMoorePenroseInverse T hR
  have hp : T.comp B = T.range.topologicalClosure.starProjection :=
    (boundedMoorePenroseInverse_projections T hR).1
  have he : (T.adjoint.comp T).comp B = T.adjoint := by
    rw [ContinuousLinearMap.comp_assoc, hp]
    exact comp_rangeProjection_eq_self_of_ker_le T T.adjoint (le_of_eq T.orthogonal_range)
  refine le_antisymm (fun y ⟨x, hx⟩ => ⟨T x, hx⟩) ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨B y, DFunLike.congr_fun he y⟩

private theorem range_self_comp_adjoint_of_isClosed_range (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) : (T.comp T.adjoint).range = T.range := by
  have hR' : IsClosed (T.adjoint.range : Set E) := by
    rw [adjoint_range_eq_orthogonal_ker_of_isClosed_range T hR]
    exact T.ker.isClosed_orthogonal
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    range_adjoint_comp_self_of_isClosed_range T.adjoint hR'

private theorem isClosed_range_adjoint_comp_self (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    IsClosed ((T.adjoint.comp T).range : Set E) := by
  rw [range_adjoint_comp_self_of_isClosed_range T hR,
    adjoint_range_eq_orthogonal_ker_of_isClosed_range T hR]
  exact T.ker.isClosed_orthogonal

private theorem isClosed_range_self_comp_adjoint (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    IsClosed ((T.comp T.adjoint).range : Set F) := by
  rwa [range_self_comp_adjoint_of_isClosed_range T hR]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem partialComp_asPartial {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) :
    partialComp (asPartial S) (asPartial T) = asPartial (S.comp T) := by
  have hd : (partialComp (asPartial S) (asPartial T)).domain = ⊤ := by
    ext x
    rw [partialComp_mem_domain]
    exact ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
  apply LinearPMap.ext hd
  intro x hx hxt
  exact partialComp_apply (asPartial S) (asPartial T) x trivial trivial

omit [CompleteSpace E] [CompleteSpace F] in
private theorem asPartial_injective :
  Function.Injective (asPartial (𝕜 := 𝕜) (E := E) (F := F)) := by
  intro A B h
  ext x
  exact (LinearPMap.ext_iff.mp h).2 (x := x) (hf := trivial) (hg := trivial)

omit [CompleteSpace E] [CompleteSpace F] in
private theorem asPartial_dense (T : E →L[𝕜] F) : Dense ((asPartial T).domain : Set E) := by
  change Dense ((⊤ : Submodule 𝕜 E) : Set E)
  rw [Submodule.top_coe]
  exact dense_univ

private theorem asPartial_adjoint (T : E →L[𝕜] F) : (asPartial T).adjoint = asPartial T.adjoint :=
  T.toPMap_adjoint_eq_adjoint_toPMap_of_dense (asPartial_dense T)

private theorem boundedMoorePenroseInverse_gram (T : E →L[𝕜] F)
    (hR : IsClosed (T.range : Set F)) :
    boundedMoorePenroseInverse (T.adjoint.comp T) (isClosed_range_adjoint_comp_self T hR) =
      (boundedMoorePenroseInverse T hR).comp (boundedMoorePenroseInverse T hR).adjoint ∧
    boundedMoorePenroseInverse (T.comp T.adjoint) (isClosed_range_self_comp_adjoint T hR) =
      (boundedMoorePenroseInverse T hR).adjoint.comp (boundedMoorePenroseInverse T hR) := by
  let T₀ := asPartial T
  let B := boundedMoorePenroseInverse T hR
  obtain ⟨_, _, _, _, hA, hF, _⟩ := theorem_2_gramOperators T₀
    (asPartial_isClosed T) (asPartial_dense T)
  have hAdj := (theorem_2_involution_adjoint (asPartial_isClosed T) (asPartial_dense T)).2.1
  have hAdjS : maximalTsengInverse T₀.adjoint = asPartial B.adjoint := by
    rw [← hAdj, ← boundedMoorePenroseInverse_asPartial T hR, asPartial_adjoint]
  have hGramA : partialComp T₀.adjoint T₀ = asPartial (T.adjoint.comp T) := by
    rw [show T₀.adjoint = asPartial T.adjoint from asPartial_adjoint T, partialComp_asPartial]
  have hGramF : partialComp T₀ T₀.adjoint = asPartial (T.comp T.adjoint) := by
    rw [show T₀.adjoint = asPartial T.adjoint from asPartial_adjoint T, partialComp_asPartial]
  constructor
  · apply asPartial_injective
    rw [boundedMoorePenroseInverse_asPartial, ← hGramA, hA, hAdjS,
      ← boundedMoorePenroseInverse_asPartial T hR, partialComp_asPartial]
  · apply asPartial_injective
    rw [boundedMoorePenroseInverse_asPartial, ← hGramF, hF, hAdjS,
      ← boundedMoorePenroseInverse_asPartial T hR, partialComp_asPartial]

/-- **Exercise 14** of [benIsrael2003generalized].
The bounded Moore–Penrose inverse has both normal-equation formulas. -/
theorem exercise_9_14 (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    boundedMoorePenroseInverse T hR =
      (boundedMoorePenroseInverse (T.adjoint.comp T) (isClosed_range_adjoint_comp_self T hR)).comp
        T.adjoint ∧
    boundedMoorePenroseInverse T hR =
      T.adjoint.comp (boundedMoorePenroseInverse (T.comp T.adjoint)
        (isClosed_range_self_comp_adjoint T hR)) := by
  let B := boundedMoorePenroseInverse T hR
  obtain ⟨ha, hb⟩ := boundedMoorePenroseInverse_gram T hR
  obtain ⟨_, hout, hright, hleft⟩ := boundedMoorePenroseInverse_penrose T hR
  constructor
  · rw [ha, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.adjoint_comp, hright,
      ← ContinuousLinearMap.comp_assoc]
    exact hout.symm
  · rw [hb, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.adjoint_comp, hleft]
    exact hout.symm

/-- **Exercise 12** of [benIsrael2003generalized].
The adjoint of the range restriction is the restricted adjoint. Its
range-space Gram operator is invertible and gives the displayed formula
for the bounded Moore–Penrose inverse. -/
theorem exercise_9_12 (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    letI : CompleteSpace T.range := hR.completeSpace_coe
    let T₁ := T.rangeRestrict
    ∃ C : T.range ≃L[𝕜] T.range,
      T₁.adjoint = T.adjoint.comp T.range.subtypeL ∧
      C.toContinuousLinearMap = T₁.comp T₁.adjoint ∧
      boundedMoorePenroseInverse T hR =
        T.kerᗮ.starProjection.comp
          (T₁.adjoint.comp (C.symm.toContinuousLinearMap.comp
            T.range.orthogonalProjectionOnto)) := by
  let : CompleteSpace T.range := hR.completeSpace_coe
  let U : E →L[𝕜] T.range := T.rangeRestrict
  let C := U.comp U.adjoint
  change ∃ e : T.range ≃L[𝕜] T.range,
    U.adjoint = T.adjoint.comp T.range.subtypeL ∧ e.toContinuousLinearMap = C ∧
    boundedMoorePenroseInverse T hR = T.kerᗮ.starProjection.comp
      (U.adjoint.comp (e.symm.toContinuousLinearMap.comp T.range.orthogonalProjectionOnto))
  have hU : U.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hUAdj : U.adjoint = T.adjoint.comp T.range.subtypeL := by
    ext z
    apply ext_inner_right 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hCker : C.ker = ⊥ := by
    rw [ContinuousLinearMap.ker_self_comp_adjoint, ← U.orthogonal_range, hU,
      Submodule.top_orthogonal_eq_bot]
  have hCR : C.range = ⊤ := by
    change (U.comp U.adjoint).range = ⊤
    rw [range_self_comp_adjoint_of_isClosed_range U
      (by rw [hU, Submodule.top_coe]; exact isClosed_univ)]
    exact hU
  let e := ContinuousLinearEquiv.ofBijective C hCker hCR
  have he : e.toContinuousLinearMap = C := ContinuousLinearEquiv.coe_ofBijective _ _ _
  refine ⟨e, hUAdj, he, ?_⟩
  let X := T.kerᗮ.starProjection.comp
      (U.adjoint.comp (e.symm.toContinuousLinearMap.comp T.range.orthogonalProjectionOnto))
  change boundedMoorePenroseInverse T hR = X
  symm
  apply eq_boundedMoorePenroseInverse_of_comp_eq_of_range_le T hR X
  · have hTQ : T.comp T.kerᗮ.starProjection = T := by
      rw [← (boundedMoorePenroseInverse_projections T hR).2, ← ContinuousLinearMap.comp_assoc]
      exact (boundedMoorePenroseInverse_penrose T hR).1
    have hProject : T.range.starProjection = T.range.topologicalClosure.starProjection := by
      apply ContinuousLinearMap.IsStarProjection.ext isStarProjection_starProjection
        isStarProjection_starProjection
      rw [Submodule.range_starProjection, Submodule.range_starProjection]
      exact (SetLike.coe_injective hR.closure_eq).symm
    ext y
    let p := T.range.orthogonalProjectionOnto y
    have hp : C (e.symm p) = p := by
      rw [← he]
      exact e.apply_symm_apply p
    change T (T.kerᗮ.starProjection (U.adjoint (e.symm p))) =
      T.range.topologicalClosure.starProjection y
    rw [← ContinuousLinearMap.comp_apply, hTQ, ← hProject]
    exact congrArg Subtype.val hp
  · rintro _ ⟨y, rfl⟩
    exact T.kerᗮ.starProjection_apply_mem (U.adjoint (e.symm (T.range.orthogonalProjectionOnto y)))


open scoped ENNReal in
/-- **Exercise 16** of [benIsrael2003generalized].
The norm of the bounded inverse is the reciprocal of the reduced minimum
modulus. For the zero operator the modulus is infinite and the norm is zero. -/
theorem exercise_9_16 (T : E →L[𝕜] F) (hR : IsClosed (T.range : Set F)) :
    ‖boundedMoorePenroseInverse T hR‖ = ((reducedMinimumModulus (asPartial T))⁻¹).toReal := by
  let B := boundedMoorePenroseInverse T hR
  let U := restrictCarrier (asPartial T)
  let γ := reducedMinimumModulus (asPartial T)
  have hU (x : E) : x ∈ U.domain ↔ x ∈ T.kerᗮ := by
    change x ∈ (restrictCarrier (asPartial T)).domain ↔ _
    rw [restrictCarrier_domain, carrier, ker_asPartial]
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have hEval (x : U.domain) : U x = T (x : E) := rfl
  obtain ⟨hTB, hBT⟩ := boundedMoorePenroseInverse_projections T hR
  have hInv (x : U.domain) : B (U x) = (x : E) := by
    rw [hEval, ← ContinuousLinearMap.comp_apply, hBT]
    exact Submodule.starProjection_eq_self_iff.mpr ((hU x).mp x.2)
  change ‖B‖ = (γ⁻¹).toReal
  by_cases hB : B = 0
  · have hzero : T = 0 := by
      have hh := (boundedMoorePenroseInverse_penrose T hR).1
      change (T.comp B).comp T = T at hh
      simpa [hB] using hh.symm
    have hEmpty : IsEmpty {x : U.domain // x ≠ 0} := by
      refine ⟨fun x => x.2 (Subtype.ext ?_)⟩
      have hx := (hU (x.val : E)).mp x.val.2
      rw [hzero] at hx
      simpa using hx
    change ‖B‖ = ((⨅ x : {x : U.domain // x ≠ 0}, ENNReal.ofReal (‖U x.val‖ / ‖x.val‖))⁻¹).toReal
    rw [hB, norm_zero, iInf_of_empty, ENNReal.inv_top, ENNReal.toReal_zero]
  have hBp : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hW : ∃ y : F, B y ≠ 0 := by
    by_contra! h
    exact hB (ContinuousLinearMap.ext fun y => h y)
  obtain ⟨y₀, hy₀⟩ := hW
  have hBrange := (boundedMoorePenroseInverse_range_ker T hR).1
  have hUby (y : F) : B y ∈ U.domain := (hU _).mpr (hBrange ▸ ⟨y, rfl⟩)
  let x₀ : U.domain := ⟨B y₀, hUby y₀⟩
  have hx₀ : x₀ ≠ 0 := fun h => hy₀ (congrArg Subtype.val h)
  let r (x : {x : U.domain // x ≠ 0}) := ENNReal.ofReal (‖U x.val‖ / ‖x.val‖)
  have hFin : γ ≠ ⊤ := ne_of_lt ((iInf_le r ⟨x₀, hx₀⟩).trans_lt ENNReal.ofReal_lt_top)
  have hLower : ENNReal.ofReal (‖B‖⁻¹) ≤ γ := by
    apply le_iInf
    intro x
    have hxNorm : 0 < ‖x.val‖ := norm_pos_iff.mpr x.2
    have h := B.le_opNorm (U x.val)
    rw [hInv] at h
    have hnorm : ‖x.val‖ ≤ ‖B‖ * ‖U x.val‖ := h
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hxNorm).mpr
    calc
      ‖B‖⁻¹ * ‖x.val‖ ≤ ‖B‖⁻¹ * (‖B‖ * ‖U x.val‖) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hBp.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hBp.ne', one_mul]
  have hPos : 0 < γ.toReal := ENNReal.toReal_pos
    (ne_of_gt ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hBp)).trans_le hLower)) hFin
  rw [ENNReal.toReal_inv]
  refine le_antisymm (B.opNorm_le_bound (inv_nonneg.mpr hPos.le) fun y => ?_) ?_
  · by_cases hy : B y = 0
    · rw [hy, norm_zero]
      positivity
    · let z : U.domain := ⟨B y, hUby y⟩
      have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
      have hratio := (ENNReal.toReal_le_toReal hFin ENNReal.ofReal_ne_top).mpr (iInf_le r ⟨z, hz⟩)
      have hRz : γ.toReal ≤ ‖T (B y)‖ / ‖B y‖ := by
        change γ.toReal ≤ (ENNReal.ofReal (‖T (B y)‖ / ‖B y‖)).toReal at hratio
        simpa only [ENNReal.toReal_ofReal (div_nonneg (norm_nonneg _) (norm_nonneg _))] using hratio
      have hBound : γ.toReal * ‖B y‖ ≤ ‖T (B y)‖ :=
        (le_div_iff₀ (norm_pos_iff.mpr hy)).mp hRz
      have hProj : ‖T (B y)‖ ≤ ‖y‖ := by
        rw [← ContinuousLinearMap.comp_apply, hTB]
        exact T.range.topologicalClosure.norm_starProjection_apply_le y
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hPos).mpr (by simpa only [mul_comm] using hBound.trans hProj)
  · have h : ‖B‖⁻¹ ≤ γ.toReal := by
      have h' := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hFin).mpr hLower
      simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hBp.le)] using h'
    calc
      γ.toReal⁻¹ ≤ (‖B‖⁻¹)⁻¹ := (inv_le_inv₀ hPos (inv_pos.mpr hBp)).mpr h
      _ = ‖B‖ := inv_inv _


private noncomputable def gramEquivOfSurjective {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (T : H →L[𝕜] K) (hT : T.range = ⊤) : K ≃L[𝕜] K :=
  ContinuousLinearEquiv.ofBijective (T.comp T.adjoint)
    (by rw [ContinuousLinearMap.ker_self_comp_adjoint, ← T.orthogonal_range, hT,
        Submodule.top_orthogonal_eq_bot])
    (by rw [range_self_comp_adjoint_of_isClosed_range T
      (by rw [hT, Submodule.top_coe]; exact isClosed_univ),
        hT])

private theorem gramEquivOfSurjective_apply {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (T : H →L[𝕜] K) (hT : T.range = ⊤) (y : K) :
    gramEquivOfSurjective T hT y = T (T.adjoint y) := rfl

/-- **Exercise 17** of [benIsrael2003generalized].
A surjective factor followed by a factor with surjective adjoint
has closed range. Its Moore–Penrose inverse is the reverse product of the
two inverses, with the stated invertible Gram factors. -/
theorem exercise_9_17 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (F₁ : H →L[𝕜] F) (G : E →L[𝕜] H) (hG : G.range = ⊤) (hF : F₁.adjoint.range = ⊤) :
    let A := F₁.comp G
    ∃ (hFR : IsClosed (F₁.range : Set F)) (hGR : IsClosed (G.range : Set H))
        (hAR : IsClosed (A.range : Set F)) (C D : H ≃L[𝕜] H),
      C.toContinuousLinearMap = G.comp G.adjoint ∧
      D.toContinuousLinearMap = F₁.adjoint.comp F₁ ∧
      boundedMoorePenroseInverse A hAR =
        (boundedMoorePenroseInverse G hGR).comp (boundedMoorePenroseInverse F₁ hFR) ∧
      boundedMoorePenroseInverse A hAR =
        (G.adjoint.comp C.symm.toContinuousLinearMap).comp
          (D.symm.toContinuousLinearMap.comp F₁.adjoint) := by
  intro A
  let C := gramEquivOfSurjective G hG
  let D := gramEquivOfSurjective F₁.adjoint hF
  have hC (z : H) : C z = G (G.adjoint z) := gramEquivOfSurjective_apply G hG z
  have hD (z : H) : D z = F₁.adjoint (F₁ z) := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      gramEquivOfSurjective_apply F₁.adjoint hF z
  let Bg := G.adjoint.comp C.symm.toContinuousLinearMap
  let Bf := D.symm.toContinuousLinearMap.comp F₁.adjoint
  have hLg (z : H) : G (Bg z) = z := by
    change G (G.adjoint (C.symm z)) = z
    rw [← hC, C.apply_symm_apply]
  have hLf (z : H) : Bf (F₁ z) = z := by
    change D.symm (F₁.adjoint (F₁ z)) = z
    rw [← hD, D.symm_apply_apply]
  have hFR : IsClosed (F₁.range : Set F) := by
    have he : (F₁.range : Set F) = {y | F₁ (Bf y) = y} := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        change F₁ (Bf (F₁ z)) = F₁ z
        rw [hLf]
      · exact fun hy => ⟨Bf y, hy⟩
    rw [he]
    exact isClosed_eq (F₁.continuous.comp Bf.continuous) continuous_id
  have hGR : IsClosed (G.range : Set H) := by rw [hG, Submodule.top_coe]; exact isClosed_univ
  have hAR : IsClosed (A.range : Set F) := by
    have hAR' : A.range = F₁.range := by
      refine le_antisymm (fun y ⟨x, hx⟩ => ⟨G x, hx⟩) ?_
      rintro _ ⟨z, rfl⟩
      exact ⟨Bg z, congrArg F₁ (hLg z)⟩
    rwa [hAR']
  have hBg : Bg = boundedMoorePenroseInverse G hGR := by
    apply eq_boundedMoorePenroseInverse_of_comp_eq_of_range_le G hGR Bg
    · have htop : G.range.topologicalClosure = ⊤ := by
        rw [hG]
        apply SetLike.coe_injective
        exact ((isClosed_univ : IsClosed (Set.univ : Set H)).closure_eq)
      have hp : G.range.topologicalClosure.starProjection = ContinuousLinearMap.id 𝕜 H := by
        ext z
        apply Submodule.starProjection_eq_self_iff.mpr
        rw [htop]
        trivial
      rw [hp]
      ext z
      exact hLg z
    · rintro _ ⟨z, rfl⟩
      have hz : Bg z ∈ G.adjoint.range := ⟨C.symm z, rfl⟩
      change Bg z ∈ G.kerᗮ
      rw [G.orthogonal_ker]
      exact G.adjoint.range.le_topologicalClosure hz
  have hBf : Bf = boundedMoorePenroseInverse F₁ hFR := by
    apply (theorem_3e F₁ hFR Bf).mp
    refine ⟨fun z _ => hLf z, fun y hy => ?_⟩
    have h : F₁.adjoint y = 0 := hy
    change D.symm (F₁.adjoint y) = 0
    rw [h, _root_.map_zero]
  let X := Bg.comp Bf
  have hAX : A.comp X = F₁.comp Bf := by
    ext y
    change F₁ (G (Bg (Bf y))) = F₁ (Bf y)
    rw [hLg]
  have hXA : X.comp A = Bg.comp G := by
    ext x
    change Bg (Bf (F₁ (G x))) = Bg (G x)
    rw [hLf]
  have hX : X = boundedMoorePenroseInverse A hAR := by
    apply (theorem_3a A hAR X).mp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hAX]
      ext x
      change F₁ (Bf (F₁ (G x))) = F₁ (G x)
      rw [hLf]
    · rw [hXA]
      ext y
      change Bg (G (Bg (Bf y))) = Bg (Bf y)
      rw [hLg]
    · rw [hAX, hBf]
      exact (boundedMoorePenroseInverse_penrose F₁ hFR).2.2.1
    · rw [hXA, hBg]
      exact (boundedMoorePenroseInverse_penrose G hGR).2.2.2
  refine ⟨hFR, hGR, hAR, C, D, ContinuousLinearMap.ext hC, ContinuousLinearMap.ext hD, ?_, hX.symm⟩
  rw [← hBg, ← hBf]
  exact hX.symm

end BoundedExercises


section InverseGraphs

/-- **Equations (25a)–(25b)** of [benIsrael2003generalized], with the
coordinate order of the inverse graph. A point of this graph is the sum
of a carrier graph point and a vertical vector in the adjoint kernel. -/
theorem theorem_2_inverseGraph [CompleteSpace E] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E)) {x : E} {y : F} :
    (y, x) ∈ (maximalTsengInverse T).graph ↔
      (x, y) ∈ (restrictCarrier T).graph ⊔ (⊥ : Submodule 𝕜 E).prod T.adjoint.ker := by
  rw [maximalTsengInverse, mem_graph_tsengInverseOn_iff, ker_adjoint_eq_orthogonal_range T hD]
  constructor
  · rintro ⟨a, ha, rfl, hy⟩
    let a' : (restrictCarrier T).domain := ⟨a, ha, a.2⟩
    refine Submodule.mem_sup.mpr ⟨((a : E), T a), (restrictCarrier T).mem_graph a',
      (0, y - T a), ⟨Submodule.zero_mem _, hy⟩, ?_⟩
    exact Prod.ext (add_zero _) (add_sub_cancel _ _)
  · intro h
    obtain ⟨⟨u, v⟩, hu, ⟨a, z⟩, ha, he⟩ := Submodule.mem_sup.mp h
    obtain ⟨u', huu, huv⟩ := (LinearPMap.mem_graph_iff _).mp hu
    have hbot : a ∈ (⊥ : Submodule 𝕜 E) := ha.1
    have ha0 : a = 0 := by simpa only [Submodule.mem_bot] using hbot
    have hx : u = x := by
      have hh : u + a = x := congrArg Prod.fst he
      rwa [ha0, add_zero] at hh
    have hy : v + z = y := congrArg Prod.snd he
    let a' : T.domain := ⟨u', u'.2.2⟩
    refine ⟨a', u'.2.1, huu.trans hx, ?_⟩
    have hv : T a' = v := huv
    rw [hv, ← hy, add_sub_cancel_left]
    exact ha.2


/-- **Equation (25a)** of [benIsrael2003generalized].
The carrier graph is perpendicular to the vertical copy of the adjoint kernel
in the Hilbert product. -/
theorem theorem_2_inverseGraph_orthogonal [CompleteSpace E] (T : E →ₗ.[𝕜] F)
    (hD : Dense (T.domain : Set E))
    (a : (restrictCarrier T).domain) {z : F} (hz : z ∈ T.adjoint.ker) :
    inner 𝕜 (WithLp.toLp 2 ((a : E), restrictCarrier T a))
      (WithLp.toLp 2 ((0 : E), z)) = 0 := by
  rw [WithLp.prod_inner_apply]
  change inner 𝕜 (a : E) (0 : E) + inner 𝕜 (restrictCarrier T a) z = 0
  rw [inner_zero_right, zero_add]
  have hi : restrictCarrier T a ∈ T.toFun.range := restrictCarrier_range_le T ⟨a, rfl⟩
  rw [ker_adjoint_eq_orthogonal_range T hD] at hz
  exact T.toFun.range.inner_right_of_mem_orthogonal hi hz

/-- **Equation (25b)** of [benIsrael2003generalized]. The signed adjoint
graph is the sum of the graph of the negative adjoint on its carrier,
written in inverse coordinates, and the horizontal original kernel. -/
theorem theorem_2_signed_adjoint_graph [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (hD : Dense (T.domain : Set E))
    (x : E) (y : F) :
    (-x, y) ∈ (maximalTsengInverse T).adjoint.graph ↔
      ∃ b : (restrictCarrier T.adjoint).domain,
        (b : F) = y ∧ x + restrictCarrier T.adjoint b ∈ T.ker := by
  rw [(theorem_2_involution_adjoint hT hD).2.1, maximalTsengInverse,
    mem_graph_tsengInverseOn_iff, orthogonal_range_adjoint_eq_ker T hD hT]
  constructor
  · rintro ⟨b, hb, rfl, hx⟩
    refine ⟨⟨b.val, hb, b.prop⟩, rfl, ?_⟩
    have h := T.ker.neg_mem hx
    convert h using 1
    change x + T.adjoint b = -(-x - T.adjoint b)
    abel
  · rintro ⟨b, rfl, hx⟩
    refine ⟨⟨b.val, b.prop.2⟩, b.prop.1, rfl, ?_⟩
    have h := T.ker.neg_mem hx
    convert h using 1
    change -x - T.adjoint ⟨b.val, b.prop.2⟩ = -(x + T.adjoint ⟨b.val, b.prop.2⟩)
    abel

private theorem carrierRestriction_range_eq_bot {T : E →ₗ.[𝕜] F} (hC : carrier T = ⊥) :
    (restrictCarrier T).toFun.range = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro y ⟨a, rfl⟩
  have ha : (a : E) ∈ carrier T := (restrictCarrier_domain T) ▸ a.2
  rw [hC] at ha
  have ha0' : (a : E) = 0 := by simpa only [Submodule.mem_bot] using ha
  have ha0 : a = 0 := Subtype.ext ha0'
  rw [ha0, LinearMap.map_zero]

/-- With trivial carrier, the Erdélyi inverse is the everywhere-zero operator. -/
theorem erdelyiInverse_eq_zero_of_carrier_eq_bot {T : E →ₗ.[𝕜] F} (hC : carrier T = ⊥) :
    erdelyiInverse T = 0 := by
  rw [← LinearPMap.ker_eq_top, (theorem_4_range_domain T).2.2,
    carrierRestriction_range_eq_bot hC, Submodule.bot_orthogonal_eq_top]

/-- The adjoint inclusion in **Theorem 4(k)** of [benIsrael2003generalized]
fails for a densely defined closable operator with trivial carrier and
nonzero range. -/
theorem erdelyiInverse_adjoint_not_le_of_carrier_eq_bot [CompleteSpace E] [CompleteSpace F]
    {T : E →ₗ.[𝕜] F} (hD : Dense (T.domain : Set E)) (hT : T.IsClosable)
    (hR : T.toFun.range ≠ ⊥) (hC : carrier T = ⊥) :
    ¬ (erdelyiInverse T).adjoint ≤ erdelyiInverse T.adjoint := by
  intro h
  have hS := erdelyiInverse_eq_zero_of_carrier_eq_bot hC
  have hZ : (0 : F →ₗ.[𝕜] E).adjoint = 0 := by
    rw [show (0 : F →ₗ.[𝕜] E) = asPartial (0 : F →L[𝕜] E) from rfl,
      asPartial_adjoint, _root_.map_zero]
    rfl
  rw [hS, hZ] at h
  have he := LinearPMap.eq_of_le_of_domain_eq h (top_unique h.1).symm
  have hcarrier : carrier T.adjoint = ⊥ := by
    rw [← (theorem_4_range_domain T.adjoint).2.1, ← he]
    exact LinearMap.range_zero
  have hSplit := domain_eq_ker_sup_carrier_of_isClosed_ker
    (isClosed_kernel_of_isClosed T.adjoint (LinearPMap.adjoint_isClosed hD))
  have hTa : T.adjoint.toFun.range = ⊥ :=
    (restrictCarrier_range_of_split T.adjoint hSplit).symm.trans
      (carrierRestriction_range_eq_bot hcarrier)
  have hd := dense_adjoint_domain_of_isClosable T hD hT
  apply hR
  rw [Submodule.eq_bot_iff]
  intro y hy
  apply hd.eq_zero_of_mem_orthogonal
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hxy : x ∈ T.toFun.rangeᗮ := by
    rw [← ker_adjoint_eq_orthogonal_range T hD]
    have hz : T.adjoint ⟨x, hx⟩ ∈ T.adjoint.toFun.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hTa] at hz
    exact T.adjoint.coe_mem_ker_iff.mpr (by simpa only [Submodule.mem_bot] using hz)
  exact T.toFun.range.inner_left_of_mem_orthogonal hy hxy


/-- The carrier closure assertion printed in **Theorem 4(c)** fails for a
closable operator with trivial carrier and nonzero range. -/
theorem theorem_4c_closure_ne_of_trivial_carrier [CompleteSpace E]
    {T : E →ₗ.[𝕜] F} (hT : T.IsClosable)
    (hR : T.toFun.range ≠ ⊥) (hC : carrier T = ⊥) :
    (erdelyiInverse T).toFun.range.topologicalClosure ≠ T.kerᗮ := by
  intro h
  have hK : T.kerᗮ = ⊥ := by
    rw [← h, (theorem_4_range_domain T).2.1, hC]
    exact isClosed_singleton.submodule_topologicalClosure_eq
  have hKcl : T.ker.topologicalClosure = ⊤ := T.ker.topologicalClosure_eq_top_iff.mpr hK
  have hle := T.le_closure
  have hKer : T.ker ≤ T.closure.ker := by
    intro x hx
    obtain ⟨a, rfl, ha⟩ := LinearPMap.mem_ker_iff.mp hx
    exact LinearPMap.mem_ker_iff.mpr
      ⟨⟨a, hle.1 a.2⟩, rfl, (hle.2 (x := a) (y := ⟨a, hle.1 a.2⟩) rfl).symm.trans ha⟩
  have hKerCl : T.ker.topologicalClosure ≤ T.closure.ker :=
    T.ker.topologicalClosure_minimal hKer
      (isClosed_kernel_of_isClosed T.closure hT.closure_isClosed)
  have hzero : T.closure = 0 :=
    LinearPMap.ker_eq_top.mp (top_unique (hKcl ▸ hKerCl))
  apply hR
  rw [Submodule.eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  have hle' : T ≤ (0 : E →ₗ.[𝕜] F) := hzero ▸ hle
  exact hle'.2 (x := a) (y := ⟨a, trivial⟩) rfl

/-- Exercise 4 supplies a single counterexample to the printed assertions
in **Theorem 4(c)** and **Theorem 4(k)** whenever the Hilbert space has a
proper dense subspace. -/
theorem theorem_4c_k_counterexample [CompleteSpace E] (D : Submodule 𝕜 E)
    (hD : Dense (D : Set E)) (v : E) (hv : v ∉ D) :
    ∃ T : E →ₗ.[𝕜] E, T.IsClosable ∧ Dense (T.domain : Set E) ∧
      (erdelyiInverse T).toFun.range.topologicalClosure ≠ T.kerᗮ ∧
      ¬ (erdelyiInverse T).adjoint ≤ erdelyiInverse T.adjoint := by
  obtain ⟨T, hdom, _, hT, hR, hC⟩ := exercise_9_4 D hD v hv
  have hd : Dense (T.domain : Set E) := hdom ▸ hD
  exact ⟨T, hT, hd, theorem_4c_closure_ne_of_trivial_carrier hT hR hC,
    erdelyiInverse_adjoint_not_le_of_carrier_eq_bot hd hT hR hC⟩


/-- **Theorem 4(b)** of [benIsrael2003generalized].
An injective bounded operator with dense nonclosed range yields a partial
operator whose range is not contained in its Erdélyi inverse domain. -/
theorem theorem_4b_range_not_le_domain_example [CompleteSpace E]
    (A : E →L[𝕜] E) (hA : Function.Injective A)
    (hD : Dense (A.range : Set E)) (hR : ¬ IsClosed (A.range : Set E)) :
    ∃ T : WithLp 2 (E × E) →ₗ.[𝕜] E, ¬ T.toFun.range ≤ (erdelyiInverse T).domain := by
  have hex : ∃ v : E, v ∉ A.range := by
    by_contra! h
    apply hR
    have htop : A.range = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, Submodule.top_coe]
    exact isClosed_univ
  obtain ⟨v, hv⟩ := hex
  obtain ⟨S, _, _, _, hSRange, hSC⟩ := exercise_9_4 A.range hD v hv
  have hSw : ∃ a : S.domain, S a ≠ 0 := by
    by_contra! h
    apply hSRange
    rw [Submodule.eq_bot_iff]
    rintro y ⟨a, rfl⟩
    exact h a
  obtain ⟨a₀, ha₀⟩ := hSw
  let f := innerSL 𝕜 (S a₀)
  have hf : f (S a₀) ≠ 0 := by
    change inner 𝕜 (S a₀) (S a₀) ≠ 0
    exact fun h => ha₀ (inner_self_eq_zero.mp h)
  let Z : E →ₗ.[𝕜] E := (((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).smulRight v).comp
    f.toLinearMap).compPMap S
  let P := (asPartial A).coprod Z
  let W := (WithLp.linearEquiv 2 𝕜 (E × E)).toLinearMap
  let D := P.domain.comap W
  let T : WithLp 2 (E × E) →ₗ.[𝕜] E :=
    ⟨D, P.toFun.comp ((W.comp D.subtype).codRestrict P.domain (fun p => p.2))⟩
  have hd (p : WithLp 2 (E × E)) :
      p ∈ T.domain ↔ (WithLp.ofLp p).2 ∈ S.domain := by
    change ((WithLp.ofLp p).1 ∈ (⊤ : Submodule 𝕜 E) ∧ (WithLp.ofLp p).2 ∈ S.domain) ↔ _
    exact ⟨And.right, fun h => ⟨trivial, h⟩⟩
  have hvT (p : T.domain) :
      T p = A (WithLp.ofLp (p : WithLp 2 (E × E))).1 +
        f (S ⟨(WithLp.ofLp (p : WithLp 2 (E × E))).2, (hd p).mp p.2⟩) • v := rfl
  have hkFirst {p : WithLp 2 (E × E)} (hp : p ∈ T.ker) : (WithLp.ofLp p).1 = 0 := by
    obtain ⟨q, rfl, hq⟩ := LinearPMap.mem_ker_iff.mp hp
    rw [hvT] at hq
    let x := (WithLp.ofLp (q : WithLp 2 (E × E))).1
    let c := f (S ⟨(WithLp.ofLp (q : WithLp 2 (E × E))).2, (hd q).mp q.2⟩)
    change A x + c • v = 0 at hq
    have hc : c = 0 := by
      by_contra h
      apply hv
      refine ⟨(-c⁻¹) • x, ?_⟩
      change A ((-c⁻¹) • x) = v
      have hAx : A x = -(c • v) := eq_neg_of_add_eq_zero_left hq
      rw [_root_.map_smul, hAx, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ h, one_smul]
    rw [hc, zero_smul, add_zero] at hq
    exact hA (hq.trans (_root_.map_zero A).symm)
  have hkVertical (y : E) (hy : y ∈ S.ker) : WithLp.toLp 2 ((0 : E), y) ∈ T.ker := by
    let p := WithLp.toLp 2 ((0 : E), y)
    let q : T.domain := ⟨p, (hd p).mpr (S.ker_le_domain hy)⟩
    apply (T.coe_mem_ker_iff (x := q)).mpr
    rw [hvT]
    change A 0 + f (S ⟨y, S.ker_le_domain hy⟩) • v = 0
    rw [S.coe_mem_ker_iff.mp hy, _root_.map_zero, _root_.map_zero, zero_smul, zero_add]
  have hc (p : WithLp 2 (E × E)) : p ∈ carrier T ↔ (WithLp.ofLp p).2 = 0 := by
    constructor
    · rintro ⟨hp, ho⟩
      let y := (WithLp.ofLp p).2
      have hy : y ∈ S.kerᗮ := by
        apply (Submodule.mem_orthogonal _ _).mpr
        intro z hz
        have hh := T.ker.inner_right_of_mem_orthogonal (hkVertical z hz) ho
        rw [WithLp.prod_inner_apply] at hh
        change inner 𝕜 (0 : E) (WithLp.ofLp p).1 + inner 𝕜 z y = 0 at hh
        rwa [inner_zero_left, zero_add] at hh
      have hyC : y ∈ carrier S := ⟨(hd p).mp hp, hy⟩
      rw [hSC] at hyC
      simpa only [Submodule.mem_bot] using hyC
    · intro hy
      refine ⟨(hd p).mpr (hy.symm ▸ S.domain.zero_mem), ?_⟩
      apply (Submodule.mem_orthogonal _ _).mpr
      intro q hq
      rw [WithLp.prod_inner_apply, hkFirst hq, hy, inner_zero_left, inner_zero_right, add_zero]
  have hCR : (restrictCarrier T).toFun.range = A.range := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      have hp : (p : WithLp 2 (E × E)) ∈ carrier T := (restrictCarrier_domain T) ▸ p.2
      let q : T.domain := ⟨p, hp.1⟩
      have hq := hvT q
      have he : (⟨(WithLp.ofLp (q : WithLp 2 (E × E))).2, (hd q).mp q.2⟩ : S.domain) = 0 :=
        Subtype.ext ((hc p).mp hp)
      rw [he, LinearPMap.map_zero, _root_.map_zero, zero_smul, add_zero] at hq
      exact ⟨(WithLp.ofLp (q : WithLp 2 (E × E))).1, hq.symm⟩
    · rintro ⟨x, rfl⟩
      let p := WithLp.toLp 2 (x, (0 : E))
      have hp : p ∈ carrier T := (hc p).mpr rfl
      let q : T.domain := ⟨p, hp.1⟩
      have he := hvT q
      change T q = A x + f (S 0) • v at he
      rw [LinearPMap.map_zero, _root_.map_zero, zero_smul, add_zero] at he
      exact ⟨⟨p, hp.2, hp.1⟩, he⟩
  have hvRange : v ∈ T.toFun.range := by
    let a := (f (S a₀))⁻¹ • a₀
    let p := WithLp.toLp 2 ((0 : E), (a : E))
    let q : T.domain := ⟨p, (hd p).mpr a.2⟩
    have he := hvT q
    change T q = A 0 + f (S a) • v at he
    have hfa : f (S a) = 1 := by
      dsimp only [a]
      rw [S.map_smul, _root_.map_smul, smul_eq_mul, inv_mul_cancel₀ hf]
    rw [_root_.map_zero, hfa, one_smul, zero_add] at he
    exact ⟨q, he⟩
  refine ⟨T, fun hle => ?_⟩
  have hOrtho : A.rangeᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    exact fun x hx => hD.eq_zero_of_mem_orthogonal hx
  have hvD := hle hvRange
  rw [(theorem_4_range_domain T).1, hCR, hOrtho, sup_bot_eq] at hvD
  exact hv hvD

end InverseGraphs

end BenIsraelGreville.Chapter09
