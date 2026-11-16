/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Closure
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv

/-!
# Polyhedral convex functions

A function $f \colon E \to [-\infty, +\infty]$ on a real normed space is a **polyhedral convex
function** if its epigraph is a polyhedral convex set. By the Minkowski–Weyl theorem, in finite
dimensions this means that $f$ is the pointwise maximum of finitely many affine functions on a
polyhedral effective domain ([rockafellar1970convex], §19). All results here are read off the
epigraph through the polyhedral calculus of `Numlib.Analysis.Convex.Polyhedral.Ops`.

A polyhedral convex function is convex and lower semicontinuous, and its effective domain and its
sublevel sets are polyhedral. Sums, infimal convolutes, inverse images and images under linear maps
of polyhedral convex functions are polyhedral. For an infimal convolute and for an image, the
infimum in the definition is attained wherever it is finite.

## Main definitions

* `ConvexAnalysis.PolyhedralFn`: the epigraph of $f$ is a polyhedral set.

## Main results

* `ConvexAnalysis.PolyhedralFn.convexFn`, `ConvexAnalysis.PolyhedralFn.lowerSemicontinuous`,
  `ConvexAnalysis.PolyhedralFn.closedConvex`: a polyhedral convex function is convex and lower
  semicontinuous, and it is closed if it never takes the value $-\infty$.
* `ConvexAnalysis.PolyhedralFn.polyhedral_convexDom`,
  `ConvexAnalysis.PolyhedralFn.polyhedral_sublevel`: the effective domain and every sublevel set are
  polyhedral.
* `ConvexAnalysis.polyhedralFn_indicatorFn`: the indicator function of a polyhedral set is
  polyhedral. This is what makes the polyhedral constraint qualifications apply to constraint sets.
* `ConvexAnalysis.PolyhedralFn.add`, `ConvexAnalysis.PolyhedralFn.finsetSum`: a sum of polyhedral
  convex functions that never take the value $-\infty$ is polyhedral.
* `ConvexAnalysis.PolyhedralFn.infConv`, `ConvexAnalysis.epi_infConv_of_polyhedralFn`: the infimal
  convolute of two polyhedral convex functions is polyhedral, and its epigraph is the sum of the
  epigraphs.
* `ConvexAnalysis.PolyhedralFn.compLin`: the inverse image $gA$ of a polyhedral $g$ under a linear
  map $A$ is polyhedral.
* `ConvexAnalysis.PolyhedralFn.mapLin`, `ConvexAnalysis.epi_mapLin_of_polyhedralFn`,
  `ConvexAnalysis.exists_mapLin_eq_of_polyhedralFn`: the image $Af$ of a polyhedral $f$ is
  polyhedral, and the infimum that defines it is attained wherever it is finite.

## Implementation notes

* `ConvexAnalysis.PolyhedralFn` does not exclude the value $-\infty$: the epigraph of
  $f \equiv -\infty$ is all of $E \times \mathbb{R}$, which is polyhedral. For this reason
  `ConvexAnalysis.PolyhedralFn.closedConvex` has the hypothesis that $f$ never takes the value
  $-\infty$, while lower semicontinuity holds without it. The classical convention makes polyhedral
  convex functions proper.
-/

open Set
open scoped Pointwise

namespace ConvexAnalysis

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- A function $f \colon E \to [-\infty, +\infty]$ is a **polyhedral convex function** if its
epigraph $\operatorname{epi} f = \{ (x, \mu) \in E \times \mathbb{R} \mid f(x) \le \mu \}$ is a
polyhedral convex set.

The definition allows the value $-\infty$: the function $f \equiv -\infty$ is polyhedral. The
classical definition makes polyhedral convex functions proper. -/
def PolyhedralFn (f : E → EReal) : Prop := Polyhedral (epi f)

omit [FiniteDimensional ℝ E] in
/-- A polyhedral convex function is convex. -/
theorem PolyhedralFn.convexFn (hf : PolyhedralFn f) : ConvexFn f :=
  convexFn_iff_convex_epi.2 (Polyhedral.convex hf)

/-- On a finite-dimensional space, the epigraph of a polyhedral convex function is closed. -/
theorem PolyhedralFn.isClosed_epi (hf : PolyhedralFn f) : IsClosed (epi f) :=
  Polyhedral.isClosed hf

/-- On a finite-dimensional space, a polyhedral convex function is lower semicontinuous. -/
theorem PolyhedralFn.lowerSemicontinuous (hf : PolyhedralFn f) : LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_epi.2 hf.isClosed_epi

/-- On a finite-dimensional space, a polyhedral convex function $f$ that never takes the value
$-\infty$ is closed, that is, it equals its closure. -/
theorem PolyhedralFn.closedConvex (hf : PolyhedralFn f) (h : ∀ x, f x ≠ ⊥) : ClosedConvex f :=
  (closedConvex_iff_lowerSemicontinuous h).2 hf.lowerSemicontinuous

/-- On a finite-dimensional space, the effective domain of a polyhedral convex function is a
polyhedral convex set. It is the projection of the epigraph on $E$. -/
theorem PolyhedralFn.polyhedral_convexDom (hf : PolyhedralFn f) : Polyhedral (convexDom f) := by
  rw [convexDom_eq_fst_image_epi]
  exact Polyhedral.image hf (LinearMap.fst ℝ E ℝ)

omit [FiniteDimensional ℝ E] in
/-- For every polyhedral convex function $f$ and every $c \in \mathbb{R}$, the sublevel set
$\{ x \in E \mid f(x) \le c \}$ is polyhedral. It is the preimage of the epigraph under the
affine map $x \mapsto (x, c)$. -/
theorem PolyhedralFn.polyhedral_sublevel (hf : PolyhedralFn f) (c : ℝ) :
    Polyhedral {x : E | f x ≤ (c : EReal)} := by
  have hpre : {x : E | f x ≤ (c : EReal)}
      = (fun x => LinearMap.inl ℝ E ℝ x + ((0 : E), c)) ⁻¹' epi f := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_epi]
    constructor
    · intro hx
      have hfst : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).1 = x := by simp
      have hsnd : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).2 = c := by simp
      rw [hfst, hsnd]
      exact hx
    · intro hx
      have hfst : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).1 = x := by simp
      have hsnd : (LinearMap.inl ℝ E ℝ x + ((0 : E), c)).2 = c := by simp
      rw [hfst, hsnd] at hx
      exact hx
  rw [hpre]
  exact Polyhedral.comap_affine hf _ _

omit [FiniteDimensional ℝ E] in
/-- **The indicator function of a polyhedral convex set is a polyhedral convex function.** Its
epigraph is the half-cylinder $C \times [0, \infty)$, the intersection of the preimage of $C$
with a half-space. -/
theorem polyhedralFn_indicatorFn {C : Set E} (hC : Polyhedral C) :
    PolyhedralFn (indicatorFn C) := by
  have hepi : epi (indicatorFn C)
      = (LinearMap.fst ℝ E ℝ) ⁻¹' C ∩ {p : E × ℝ | (-LinearMap.snd ℝ E ℝ) p ≤ 0} := by
    rw [epi_indicatorFn]
    ext p
    simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, by change -p.2 ≤ 0; linarith⟩
    · rintro ⟨h₁, h₂⟩
      have h₂' : -p.2 ≤ 0 := h₂
      exact ⟨h₁, by linarith⟩
  rw [PolyhedralFn, hepi]
  exact Polyhedral.inter (hC.comap _) (polyhedral_halfSpace _ _)

/-- The linear map $((x, \alpha), (y, \beta)) \mapsto (x, \alpha + \beta)$ from $(E \times
\mathbb{R}) \times (E \times \mathbb{R})$ to $E \times \mathbb{R}$, used to build the epigraph
of a sum. -/
def addEpiMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E × ℝ where
  toFun p := (p.1.1, p.1.2 + p.2.2)
  map_add' p q := by
    refine Prod.ext rfl ?_
    change p.1.2 + q.1.2 + (p.2.2 + q.2.2) = p.1.2 + p.2.2 + (q.1.2 + q.2.2)
    ring
  map_smul' a p := by
    refine Prod.ext rfl ?_
    change a * p.1.2 + a * p.2.2 = a * (p.1.2 + p.2.2)
    ring

/-- The linear map $((x, \alpha), (y, \beta)) \mapsto x - y$ from $(E \times \mathbb{R}) \times (E
\times \mathbb{R})$ to $E$. Its kernel is the condition that the two points have the same first
coordinate. -/
def diagMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E where
  toFun p := p.1.1 - p.2.1
  map_add' p q := by
    change p.1.1 + q.1.1 - (p.2.1 + q.2.1) = p.1.1 - p.2.1 + (q.1.1 - q.2.1)
    abel
  map_smul' a p := by
    change a • p.1.1 - a • p.2.1 = a • (p.1.1 - p.2.1)
    rw [smul_sub]

/-- Let $E$ be a finite-dimensional real normed space. If $f, g \colon E \to [-\infty, +\infty]$ are
polyhedral convex functions that never take the value $-\infty$, then $f + g$ is polyhedral.

The epigraph of $f + g$ is the image of the polyhedral set $\{ ((x, \alpha), (y, \beta)) \in
\operatorname{epi} f \times \operatorname{epi} g \mid x = y \}$ under $((x, \alpha), (y, \beta))
\mapsto (x, \alpha + \beta)$. The hypotheses make the splitting $f(x) + g(x) \le \mu \iff
\exists \alpha, \beta,\ f(x) \le \alpha,\ g(x) \le \beta,\ \alpha + \beta = \mu$ correct in
`EReal`. -/
theorem PolyhedralFn.add {g : E → EReal} (hf : PolyhedralFn f) (hg : PolyhedralFn g)
    (hf' : ∀ x, f x ≠ ⊥) (hg' : ∀ x, g x ≠ ⊥) : PolyhedralFn (f + g) := by
  have hS : Polyhedral (((epi f) ×ˢ (epi g)) ∩ (diagMap ⁻¹' ({0} : Set E))) :=
    Polyhedral.inter (Polyhedral.prod hf hg) (Polyhedral.comap polyhedral_zero _)
  have himg : epi (f + g) = (addEpiMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] E × ℝ) ''
      (((epi f) ×ˢ (epi g)) ∩ (diagMap ⁻¹' ({0} : Set E))) := by
    ext p
    constructor
    · intro hp
      have hle : f p.1 + g p.1 ≤ ((p.2 : ℝ) : EReal) := hp
      have hftop : f p.1 ≠ ⊤ := by
        intro h
        rw [h, EReal.top_add_of_ne_bot (hg' p.1)] at hle
        exact absurd hle (not_le.2 (EReal.coe_lt_top p.2))
      have hgtop : g p.1 ≠ ⊤ := by
        intro h
        rw [h, EReal.add_top_of_ne_bot (hf' p.1)] at hle
        exact absurd hle (not_le.2 (EReal.coe_lt_top p.2))
      obtain ⟨a, ha⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hf' p.1) (lt_top_iff_ne_top.2 hftop)
      obtain ⟨b, hb⟩ :=
        EReal.exists_coe_of_ne_bot_of_lt_top (hg' p.1) (lt_top_iff_ne_top.2 hgtop)
      rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
      refine ⟨((p.1, a), (p.1, p.2 - a)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · change f p.1 ≤ ((a : ℝ) : EReal)
        rw [ha]
      · change g p.1 ≤ ((p.2 - a : ℝ) : EReal)
        rw [hb, EReal.coe_le_coe_iff]
        linarith
      · change p.1 - p.1 ∈ ({0} : Set E)
        rw [sub_self]
        rfl
      · refine Prod.ext rfl ?_
        change a + (p.2 - a) = p.2
        ring
    · rintro ⟨q, ⟨⟨hq₁, hq₂⟩, hq₃⟩, rfl⟩
      have hdiag : q.1.1 = q.2.1 := by
        have : q.1.1 - q.2.1 ∈ ({0} : Set E) := hq₃
        rw [Set.mem_singleton_iff, sub_eq_zero] at this
        exact this
      have h₁ : f q.1.1 ≤ ((q.1.2 : ℝ) : EReal) := hq₁
      have h₂ : g q.2.1 ≤ ((q.2.2 : ℝ) : EReal) := hq₂
      rw [← hdiag] at h₂
      change f q.1.1 + g q.1.1 ≤ ((q.1.2 + q.2.2 : ℝ) : EReal)
      rw [EReal.coe_add]
      exact add_le_add h₁ h₂
  rw [PolyhedralFn, himg]
  exact Polyhedral.image hS _

/-- Let $E$ be a finite-dimensional real normed space and let $s$ be a nonempty finite set. If
$f_i \colon E \to [-\infty, +\infty]$ is a polyhedral convex function that never takes the value
$-\infty$ for every $i \in s$, then $\sum_{i \in s} f_i$ is polyhedral. -/
theorem PolyhedralFn.finsetSum {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hs : s.Nonempty) (hpoly : ∀ i ∈ s, PolyhedralFn (f i))
    (hbot : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) : PolyhedralFn (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons i t hi ih =>
    have hmt : ∀ j ∈ t, j ∈ Finset.cons i t hi := fun j hj => Finset.mem_cons_of_mem hj
    rcases Finset.eq_empty_or_nonempty t with rfl | htne
    · rw [Finset.cons_empty, Finset.sum_singleton]
      exact hpoly i (by simp)
    rw [Finset.sum_cons]
    exact PolyhedralFn.add (hpoly i (by simp))
      (ih htne (fun j hj => hpoly j (hmt j hj)) (fun j hj => hbot j (hmt j hj)))
      (hbot i (by simp))
      (fun x => by
        rw [Finset.sum_apply]
        exact EReal.sum_ne_bot fun j hj => hbot j (hmt j hj) x)

/-- **Attainment for the infimal convolute.** Let $E$ be a finite-dimensional real normed space. If
$f, g \colon E \to [-\infty, +\infty]$ are polyhedral convex functions, then
$$\operatorname{epi}(f \mathbin{\square} g) = \operatorname{epi} f + \operatorname{epi} g.$$ So
the infimum that defines $(f \mathbin{\square} g)(x)$ is attained wherever it is finite.

A sum of epigraphs always has vertical sections that are closed upwards, and here the sum is
also closed, because it is polyhedral. These are the two conditions for a set to be an epigraph. -/
theorem epi_infConv_of_polyhedralFn (hf : PolyhedralFn f) {g : E → EReal} (hg : PolyhedralFn g) :
    epi (infConv f g) = epi f + epi g :=
  epi_infConv (IsEpiLike.of_isClosed (fun _ _ _ h hle => mem_epi_add_epi_of_le h hle)
    (Polyhedral.isClosed (Polyhedral.add hf hg)))

/-- Let $E$ be a finite-dimensional real normed space. If $f, g \colon E \to [-\infty, +\infty]$ are
polyhedral convex functions, then their infimal convolute $f \mathbin{\square} g$ is polyhedral.
Its epigraph is the sum of the two epigraphs. -/
theorem PolyhedralFn.infConv (hf : PolyhedralFn f) {g : E → EReal} (hg : PolyhedralFn g) :
    PolyhedralFn (_root_.ConvexAnalysis.infConv f g) := by
  have h : Polyhedral (epi (_root_.ConvexAnalysis.infConv f g)) := by
    rw [epi_infConv_of_polyhedralFn hf hg]
    exact Polyhedral.add hf hg
  exact h

end Defs

/-! ### Linear images and inverse images -/

section Image

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {f : E → EReal}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- Let $E$ and $G$ be real normed spaces and let $A \colon E \to G$ be a linear map. If
$g \colon G \to [-\infty, +\infty]$ is a polyhedral convex function, then its inverse image
$gA = g \circ A$ is polyhedral.

The epigraph of $gA$ is the preimage of $\operatorname{epi} g$ under
$(x, \mu) \mapsto (Ax, \mu)$, and the preimage of a polyhedral set under a linear map is
polyhedral (`ConvexAnalysis.Polyhedral.comap`). This direction needs neither closedness nor
attainment, so no finite dimension is assumed. -/
theorem PolyhedralFn.compLin {g : G → EReal} (hg : PolyhedralFn g) (A : E →ₗ[ℝ] G) :
    PolyhedralFn (_root_.ConvexAnalysis.compLin g A) := by
  change Polyhedral (epi (_root_.ConvexAnalysis.compLin g A))
  rw [epi_compLin]
  exact Polyhedral.comap hg _

/-- Let $E$ and $G$ be finite-dimensional real normed spaces and let $A \colon E \to G$ be a linear
map. If $f \colon E \to [-\infty, +\infty]$ is a polyhedral convex function, then the epigraph
of its image $Af$ is the image of $\operatorname{epi} f$: $$\operatorname{epi}(Af) = \{ (Ax,
\mu) \mid (x, \mu) \in \operatorname{epi} f \}.$$

In general the image of $\operatorname{epi} f$ need not be an epigraph, because the infimum that
defines $Af$ need not be attained (`ConvexAnalysis.exists_epi_mapLin_ne_image`). Here the image
is polyhedral, hence closed, and a closed set whose vertical sections are closed upwards is an
epigraph. The polyhedrality of $Af$ and the attainment of the infimum both follow from this
identity. -/
theorem epi_mapLin_of_polyhedralFn (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  refine epi_mapLin (IsEpiLike.of_isClosed ?_ (Polyhedral.image hf _).isClosed)
  rintro y μ ν ⟨⟨x, ρ⟩, hx, hxy⟩ hμν
  have h1 : A x = y := congrArg Prod.fst hxy
  have h2 : ρ = μ := congrArg Prod.snd hxy
  refine ⟨(x, ν), mk_mem_epi.2 ?_, ?_⟩
  · exact le_trans (h2 ▸ mk_mem_epi.1 hx) (by exact_mod_cast hμν)
  · rw [LinearMap.prodMap_apply, h1]
    rfl

/-- Let $E$ and $G$ be finite-dimensional real normed spaces and let $A \colon E \to G$ be a linear
map. If $f \colon E \to [-\infty, +\infty]$ is a polyhedral convex function, then its image $Af$
is polyhedral.

By `ConvexAnalysis.epi_mapLin_of_polyhedralFn`, $\operatorname{epi}(Af)$ is the image of
$\operatorname{epi} f$, and a linear image of a polyhedral set is polyhedral. -/
theorem PolyhedralFn.mapLin (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) :
    PolyhedralFn (_root_.ConvexAnalysis.mapLin A f) := by
  change Polyhedral (epi (_root_.ConvexAnalysis.mapLin A f))
  rw [epi_mapLin_of_polyhedralFn hf A]
  exact Polyhedral.image hf _

/-- **Attainment for the image.** Let $E$ and $G$ be finite-dimensional real normed spaces, let
$A \colon E \to G$ be a linear map, and let $f \colon E \to [-\infty, +\infty]$ be a polyhedral
convex function. If $(Af)(y) = \mu$ for some $y \in G$ and $\mu \in \mathbb{R}$, then there is
an $x \in E$ with $Ax = y$ and $f(x) = (Af)(y)$.

By `ConvexAnalysis.epi_mapLin_of_polyhedralFn`, the point $(y, \mu)$ of $\operatorname{epi}(Af)$
is the image of a point of $\operatorname{epi} f$. -/
theorem exists_mapLin_eq_of_polyhedralFn (hf : PolyhedralFn f) (A : E →ₗ[ℝ] G) {y : G} {μ : ℝ}
    (hy : mapLin A f y = (μ : EReal)) : ∃ x : E, A x = y ∧ f x = mapLin A f y := by
  have hmem : ((y, μ) : G × ℝ) ∈ epi (mapLin A f) := mk_mem_epi.2 (le_of_eq hy)
  rw [epi_mapLin_of_polyhedralFn hf A] at hmem
  obtain ⟨⟨x, ν⟩, hx, hxy⟩ := hmem
  have h1 : A x = y := congrArg Prod.fst hxy
  have h2 : ν = μ := congrArg Prod.snd hxy
  refine ⟨x, h1, le_antisymm ?_ (mapLin_le h1)⟩
  rw [hy]
  exact h2 ▸ mk_mem_epi.1 hx

end Image

end ConvexAnalysis
