/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Perturbation
import Numlib.Analysis.Convex.HellyRefined
import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Conjugate
import Numlib.Analysis.Convex.Polyhedral.Faces
import Numlib.Analysis.Convex.Polyhedral.NormalForm
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import Numlib.Analysis.Convex.Representation
import NumlibSurface.Rockafellar.Chapter02.Section09

/-!
# Rockafellar, Section 19: Polyhedral convex sets and functions

This module formalizes §19 of [rockafellar1970convex]: the Minkowski–Weyl theorem, which says that a
convex set in $\mathbb{R}^n$ is polyhedral if and only if it is finitely generated, and the calculus
of polyhedral convex sets and functions. Polyhedrality is preserved by conjugation, support
functions and polars, by images and inverse images under linear maps, by sums and infimal
convolution, by scalar multiples and recession cones, and by closed convex hulls of unions and
closed generated cones. All seventeen numbered results are formalized: Theorems 19.1–19.7 and
Corollaries 19.1.1, 19.1.2, 19.2.1, 19.2.2, 19.3.1–19.3.4, 19.5.1 and 19.7.1, together with the
unnumbered normal form $f = h + \delta(\cdot \mid C)$ of a polyhedral convex function. The proofs
specialize the backbone modules under `Numlib.Analysis.Convex.Polyhedral`.

The printed statements of §19 are correct. Two proofs in the source are incomplete: the proof of (b)
⇒ (a) in Theorem 19.1 reduces to the $n$-dimensional case without justification, and Theorem 19.6 is
printed without a proof.

## Main definitions

* Definition of a polytope, `Rockafellar.IsPolytope`: the convex hull of a finite set of points,
  equivalently a bounded polyhedral convex set.
* Definition of a finitely generated convex function, `Rockafellar.FinitelyGeneratedFn`: a function
  whose epigraph is a finitely generated convex set.

## Main results

* Theorem 19.1 (Minkowski–Weyl), `Rockafellar.theorem_19_1`, `Rockafellar.theorem_19_1_pairing`,
  `Rockafellar.theorem_19_1_convexHullPD`, `Rockafellar.theorem_19_1_isClosed`,
  `Rockafellar.theorem_19_1_finite_faces`,
  `Rockafellar.theorem_19_1_finitelyGenerated_of_finite_faces`,
  `Rockafellar.theorem_19_1_of_finite_faces`, `Rockafellar.theorem_19_1_iff_finite_faces`: for a
  convex set, being polyhedral, being closed with finitely many faces, and being finitely generated
  are equivalent.
* The remark after Theorem 19.1, `Rockafellar.theorem_19_1_face`: a face of a polyhedral convex set
  is polyhedral.
* Corollary 19.1.1, `Rockafellar.corollary_19_1_1_extremePoints`,
  `Rockafellar.corollary_19_1_1_extremeDirections`: a polyhedral convex set has finitely many
  extreme points and extreme directions.
* Corollary 19.1.2, `Rockafellar.corollary_19_1_2`, `Rockafellar.corollary_19_1_2_closed`,
  `Rockafellar.corollary_19_1_2_attained`: a convex function is polyhedral if and only if it is
  finitely generated; a proper polyhedral convex function is closed; and the infimum that defines a
  finitely generated function is attained where it is finite.
* Theorem 19.2, `Rockafellar.theorem_19_2`: the conjugate of a polyhedral convex function is
  polyhedral.
* Corollary 19.2.1, `Rockafellar.corollary_19_2_1`: a closed convex set is polyhedral if and only if
  its support function is polyhedral.
* Corollary 19.2.2, `Rockafellar.corollary_19_2_2`: the polar of a polyhedral convex set is
  polyhedral.
* Theorem 19.3, `Rockafellar.theorem_19_3_image`, `Rockafellar.theorem_19_3_preimage`: images and
  inverse images of polyhedral convex sets under linear maps are polyhedral.
* Corollary 19.3.1, `Rockafellar.corollary_19_3_1_image`, `Rockafellar.corollary_19_3_1_attained`,
  `Rockafellar.corollary_19_3_1_preimage`: the same for polyhedral convex functions, with attainment
  of the infimum that defines $Af$.
* Corollary 19.3.2, `Rockafellar.corollary_19_3_2`: the sum of two polyhedral convex sets is
  polyhedral.
* Corollary 19.3.3, `Rockafellar.corollary_19_3_3`: two disjoint non-empty polyhedral convex sets
  can be separated strongly.
* Corollary 19.3.4, `Rockafellar.corollary_19_3_4`, `Rockafellar.corollary_19_3_4_attained`: the
  infimal convolution of two polyhedral convex functions is polyhedral, and its infimum is attained
  where it is finite.
* Theorem 19.4, `Rockafellar.theorem_19_4`: the sum of two proper polyhedral convex functions is
  polyhedral.
* The normal form, `Rockafellar.polyhedralFn_iff_normalForm`: a function with values in
  $(-\infty, +\infty]$ is polyhedral convex if and only if it is a maximum of finitely many affine
  functions plus the indicator function of a polyhedral convex set.
* Theorem 19.5, `Rockafellar.theorem_19_5_smul`, `Rockafellar.theorem_19_5_recession`,
  `Rockafellar.theorem_19_5_generators`: scalar multiples of a polyhedral convex set are polyhedral,
  and the recession cone of a non-empty one is a polyhedral convex cone generated by its directions.
* Corollary 19.5.1, `Rockafellar.corollary_19_5_1`: $f \lambda$ is polyhedral for a proper
  polyhedral convex function $f$, $\lambda \ge 0$ and $\lambda = 0^+$.
* Theorem 19.6, `Rockafellar.theorem_19_6`, `Rockafellar.theorem_19_6_iUnion`,
  `Rockafellar.theorem_19_6_biUnion`, `Rockafellar.theorem_19_6_biUnion_add`: the closed convex hull
  of a union of non-empty polyhedral convex sets is polyhedral, with formulas for it.
* Theorem 19.7, `Rockafellar.theorem_19_7`, `Rockafellar.theorem_19_7_iUnion`: the closure of the
  convex cone generated by a non-empty polyhedral convex set is a polyhedral convex cone, with a
  formula for it.
* Corollary 19.7.1, `Rockafellar.corollary_19_7_1`: if a polyhedral convex set contains the origin,
  the convex cone that it generates is polyhedral.

## Conventions

* Theorems 19.6 and 19.7 and Corollary 19.5.1 use the extended coefficient $\lambda \ge 0^+$ of the
  source, which is `Rockafellar.ExtCoeff` from §9. For the coefficient $0^+$,
  `Rockafellar.ExtCoeff.smulSet` gives the recession cone $0^+ C$ of a set, and
  `Rockafellar.ExtCoeff.smulFn` gives the recession function $f 0^+$ of a function.

## Implementation notes

* The five notions of the section are those of the backbone. A polyhedral convex set is
  `ConvexAnalysis.Polyhedral`, the solution set of finitely many weak linear inequalities. A
  polyhedral convex cone is `ConvexAnalysis.PolyhedralCone`. A finitely generated convex set is
  `ConvexAnalysis.FinitelyGenerated`, the set $\operatorname{conv} P + \operatorname{cone} D$ for
  finite sets $P$ of points and $D$ of directions. A polyhedral convex function is
  `ConvexAnalysis.PolyhedralFn`, a function whose epigraph is polyhedral.

## Deviations from the source

* **Corollary 19.3.4** (generalization). The source assumes the two functions proper; this is not
  needed. See `Rockafellar.corollary_19_3_4`.
-/

namespace Rockafellar

open ConvexAnalysis

open scoped Pointwise

variable {n m : ℕ}

/-! ### Polytopes and finitely generated functions -/

/-- **Section 19** of [rockafellar1970convex], definition of a polytope. A set
$C \subseteq \mathbb{R}^n$ is a **polytope** if it is the convex hull of a finite set of points.

The source defines a polytope as a bounded finitely generated convex set. The two definitions
agree, and `Rockafellar.isPolytope_iff` shows that a polytope is the same as a bounded
polyhedral convex set. -/
def IsPolytope (C : Set (Rn n)) : Prop := ∃ P : Finset (Rn n), C = convexHull ℝ (P : Set (Rn n))

/-- **Section 19** of [rockafellar1970convex], definition of a finitely generated convex function. A
function $f$ on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$ is **finitely generated** if
its epigraph is a finitely generated convex set in $\mathbb{R}^n \times \mathbb{R}$.

The source defines the notion by an infimum formula, and observes before Corollary 19.1.2 that
this means $f(x) = \inf \{\mu \mid (x, \mu) \in F\}$, where $F$ is the convex hull of finitely
many points $(a_i, \alpha_i)$, directions, and the direction $(0, 1)$. Here the generator
$(0, 1)$ is part of the requirement that the generated set is an epigraph. -/
def FinitelyGeneratedFn (f : Rn n → EReal) : Prop := FinitelyGenerated (epi f)

/-- A set $C \subseteq \mathbb{R}^n$ is a polytope if and only if it is polyhedral and bounded. -/
theorem isPolytope_iff {C : Set (Rn n)} :
    IsPolytope C ↔ Polyhedral C ∧ Bornology.IsBounded C := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨polyhedral_convexHull_finset P,
      (P.finite_toSet.isCompact.convexHull).isBounded⟩
  · rintro ⟨hC, hb⟩
    exact hC.exists_finset_convexHull hb

/-! ### Theorem 19.1 -/

/-- **Theorem 19.1** of [rockafellar1970convex] (Minkowski–Weyl theorem), (a) ⇔ (c). A set
$C \subseteq \mathbb{R}^n$ is polyhedral, that is, the intersection of finitely many closed
half-spaces, if and only if it is finitely generated, that is, the convex hull of a finite set
of points and directions. -/
theorem theorem_19_1 {C : Set (Rn n)} : Polyhedral C ↔ FinitelyGenerated C :=
  polyhedral_iff_finitelyGenerated

/-- **Theorem 19.1** of [rockafellar1970convex], clause (a) in the notation of the source. A set
$C \subseteq \mathbb{R}^n$ is polyhedral if and only if there are finitely many pairs $(b_i,
\beta_i) \in \mathbb{R}^n \times \mathbb{R}$ with
$$C = \{x \mid \langle x, b_i \rangle \le \beta_i \text{ for all } i\}.$$

The backbone quantifies over linear functionals; on $\mathbb{R}^n$ the pairing represents each
of them by a vector. -/
theorem theorem_19_1_pairing {C : Set (Rn n)} :
    Polyhedral C ↔ ∃ s : Finset (Rn n × ℝ), C = {x : Rn n | ∀ q ∈ s, pairing n x q.1 ≤ q.2} := by
  classical
  refine ⟨fun hC => hC.exists_finset_pairing, ?_⟩
  rintro ⟨s, rfl⟩
  refine ⟨s.image fun q => ((pairing n).flip q.1, q.2), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_image]
  constructor
  · rintro h q ⟨p, hp, rfl⟩
    exact h p hp
  · intro h q hq
    exact h ((pairing n).flip q.1, q.2) ⟨q, hq, rfl⟩

/-- **Theorem 19.1** of [rockafellar1970convex], clause (c) in the notation of the source. A set
$C \subseteq \mathbb{R}^n$ is finitely generated if and only if $C = \operatorname{conv} S$ for
a finite set $S$ of points $P$ and directions $D$. -/
theorem theorem_19_1_convexHullPD {C : Set (Rn n)} :
    FinitelyGenerated C ↔ ∃ P D : Finset (Rn n),
      C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := Iff.rfl

/-- **Theorem 19.1** of [rockafellar1970convex], (a) ⇒ (b), first half. A polyhedral convex set in
$\mathbb{R}^n$ is closed. -/
theorem theorem_19_1_isClosed {C : Set (Rn n)} (hC : Polyhedral C) : IsClosed C :=
  hC.isClosed

/-- **Theorem 19.1** of [rockafellar1970convex], (a) ⇒ (b), second half. A polyhedral convex set in
$\mathbb{R}^n$ has finitely many faces. -/
theorem theorem_19_1_finite_faces {C : Set (Rn n)} (hC : Polyhedral C) :
    {C' : Set (Rn n) | IsFace C C'}.Finite :=
  hC.finite_setOf_isFace

/-- **Theorem 19.1** of [rockafellar1970convex], (b) ⇒ (c). A closed convex set in $\mathbb{R}^n$
with finitely many faces is finitely generated. -/
theorem theorem_19_1_finitelyGenerated_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C)
    (hCcl : IsClosed C) (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) :
    FinitelyGenerated C :=
  finitelyGenerated_of_finite_setOf_isFace hC hCcl hfin

/-- **Theorem 19.1** of [rockafellar1970convex], (b) ⇒ (a). A closed convex set in $\mathbb{R}^n$
with finitely many faces is polyhedral.

The proof in the source has a gap: it says that it suffices to treat the case where $C$ is
$n$-dimensional, without justification, and then uses the tangent half-spaces of Theorem 18.8.
The proof here goes through (b) ⇒ (c) ⇒ (a) instead, and uses neither Theorem 18.8 nor a
dimension count. -/
theorem theorem_19_1_of_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hfin : {C' : Set (Rn n) | IsFace C C'}.Finite) : Polyhedral C :=
  polyhedral_of_finite_setOf_isFace hC hCcl hfin

/-- **Theorem 19.1** of [rockafellar1970convex], (a) ⇔ (b). A convex set in $\mathbb{R}^n$ is
polyhedral if and only if it is closed and has finitely many faces. With
`Rockafellar.theorem_19_1`, this gives the equivalence of the three clauses. -/
theorem theorem_19_1_iff_finite_faces {C : Set (Rn n)} (hC : Convex ℝ C) :
    Polyhedral C ↔ IsClosed C ∧ {C' : Set (Rn n) | IsFace C C'}.Finite :=
  polyhedral_iff_isClosed_finite_setOf_isFace hC

/-- **Section 19** of [rockafellar1970convex], the remark after Theorem 19.1. A face of a polyhedral
convex set in $\mathbb{R}^n$ is polyhedral. -/
theorem theorem_19_1_face {C C' : Set (Rn n)} (hC : Polyhedral C) (hface : IsFace C C') :
    Polyhedral C' :=
  hC.of_isFace hface

/-! ### Corollary 19.1.1 -/

/-- **Corollary 19.1.1** of [rockafellar1970convex], extreme points. A polyhedral convex set in
$\mathbb{R}^n$ has finitely many extreme points. -/
theorem corollary_19_1_1_extremePoints {C : Set (Rn n)} (hC : Polyhedral C) :
    (C.extremePoints ℝ).Finite :=
  hC.finitelyGenerated.finite_extremePoints

/-- **Corollary 19.1.1** of [rockafellar1970convex], extreme directions. A polyhedral convex set $C$
in $\mathbb{R}^n$ has finitely many extreme directions: there is a finite set $D$ such that
every vector $y$ that generates an extreme direction of $C$ is a positive multiple of a vector
of $D$.

A direction is represented by a vector that generates it, so
`ConvexAnalysis.extremeDirections C` is closed under multiplication by positive scalars, and it
is infinite when it is non-empty. So the finiteness is stated up to positive multiples, which is
the meaning of the source. -/
theorem corollary_19_1_1_extremeDirections {C : Set (Rn n)} (hC : Polyhedral C) :
    ∃ D : Finset (Rn n), ∀ y ∈ extremeDirections C,
      ∃ z ∈ (D : Set (Rn n)), ∃ a : ℝ, 0 < a ∧ y = a • z := by
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  have hPD' : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n)) := hPD
  refine ⟨D, fun y hy => ?_⟩
  rw [hPD'] at hy
  exact exists_mem_eq_smul_of_mem_extremeDirections_of_isBounded _ _ P.finite_toSet.isBounded hy

/-! ### Corollary 19.1.2 -/

/-- **Corollary 19.1.2** of [rockafellar1970convex], first sentence. A function on $\mathbb{R}^n$
with values in $[-\infty, +\infty]$ is polyhedral convex if and only if it is finitely
generated.

Both conditions are conditions on the epigraph, and the proof applies Theorem 19.1 to it. -/
theorem corollary_19_1_2 {f : Rn n → EReal} : PolyhedralFn f ↔ FinitelyGeneratedFn f :=
  polyhedral_iff_finitelyGenerated

/-- **Corollary 19.1.2** of [rockafellar1970convex], second sentence. A proper polyhedral convex
function on $\mathbb{R}^n$ is closed.

Properness cannot be omitted. The constant function $-\infty$ has the epigraph
$\mathbb{R}^n \times \mathbb{R}$, which is polyhedral as the solution set of the empty system,
but it is not closed in the sense of `ConvexAnalysis.ClosedConvex`. -/
theorem corollary_19_1_2_closed {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : ProperConvex f) :
    ClosedConvex f :=
  hf.closedConvex hp.ne_bot

/-- **Corollary 19.1.2** of [rockafellar1970convex], third sentence. Let the epigraph of $f$ be the
convex hull $F$ of a finite set of points and directions in $\mathbb{R}^n \times \mathbb{R}$. If
$f(x) = \mu$ is finite, then $(x, \mu) \in F$: the infimum
$f(x) = \inf \{\mu \mid (x, \mu) \in F\}$ is attained wherever it is finite. -/
theorem corollary_19_1_2_attained {f : Rn n → EReal} {P D : Finset (Rn n × ℝ)}
    (hPD : epi f = convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)))
    {x : Rn n} {μ : ℝ} (hx : f x = (μ : EReal)) :
    ((x, μ) : Rn n × ℝ) ∈ convexHullPD (P : Set (Rn n × ℝ)) (D : Set (Rn n × ℝ)) := by
  rw [← hPD]
  exact mk_mem_epi.2 (le_of_eq hx)

/-! ### Theorem 19.2 and its corollaries -/

/-- **Theorem 19.2** of [rockafellar1970convex]. The conjugate $f^*$ of a polyhedral convex function
$f$ on $\mathbb{R}^n$ is polyhedral.

The function $f$ need not be proper. -/
theorem theorem_19_2 {f : Rn n → EReal} (hf : PolyhedralFn f) :
    PolyhedralFn (convexConj (pairing n) f) :=
  hf.convexConj

/-- **Corollary 19.2.1** of [rockafellar1970convex]. A closed convex set $C \subseteq \mathbb{R}^n$
is polyhedral if and only if its support function $\delta^*(\cdot \mid C)$ is polyhedral. -/
theorem corollary_19_2_1 {C : Set (Rn n)} (hconv : Convex ℝ C) (hcl : IsClosed C) :
    Polyhedral C ↔ PolyhedralFn (supportFn (pairing n) C) := by
  constructor
  · intro hC
    rw [supportFn_eq_convexConj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).convexConj
  · intro hs
    have h := hs.convexConj (B := (pairing n).flip)
    rw [convexConj_supportFn hconv hcl] at h
    have hd := h.polyhedral_convexDom
    rwa [convexDom_indicatorFn] at hd

/-- **Corollary 19.2.2** of [rockafellar1970convex]. The polar $C^\circ$ of a polyhedral convex set
$C \subseteq \mathbb{R}^n$ is polyhedral. -/
theorem corollary_19_2_2 {C : Set (Rn n)} (hC : Polyhedral C) :
    Polyhedral (polarSet (pairing n) C) := by
  have hs : PolyhedralFn (supportFn (pairing n) C) := by
    rw [supportFn_eq_convexConj_indicatorFn]
    exact (polyhedralFn_indicatorFn hC).convexConj
  have heq : polarSet (pairing n) C
      = {y : Rn n | supportFn (pairing n) C y ≤ ((1 : ℝ) : EReal)} := by
    ext y
    rw [mem_polarSet, Set.mem_ofPred_eq, supportFn_le_coe_iff]
  rw [heq]
  exact hs.polyhedral_sublevel 1

/-! ### Theorem 19.3 and its corollaries -/

/-- **Theorem 19.3** of [rockafellar1970convex], images. Let $A$ be a linear transformation from
$\mathbb{R}^n$ to $\mathbb{R}^m$. If $C \subseteq \mathbb{R}^n$ is polyhedral convex, then $AC$
is polyhedral convex. -/
theorem theorem_19_3_image {C : Set (Rn n)} (hC : Polyhedral C) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A '' C) :=
  hC.image A

/-- **Theorem 19.3** of [rockafellar1970convex], inverse images. Let $A$ be a linear transformation
from $\mathbb{R}^n$ to $\mathbb{R}^m$. If $D \subseteq \mathbb{R}^m$ is polyhedral convex, then
$A^{-1} D$ is polyhedral convex. -/
theorem theorem_19_3_preimage {D : Set (Rn m)} (hD : Polyhedral D) (A : Rn n →ₗ[ℝ] Rn m) :
    Polyhedral (A ⁻¹' D) :=
  hD.comap A

/-- **Corollary 19.3.1** of [rockafellar1970convex], images. Let $A$ be a linear transformation from
$\mathbb{R}^n$ to $\mathbb{R}^m$. If $f$ is a polyhedral convex function on $\mathbb{R}^n$, then
$Af$, with $(Af)(y) = \inf \{f(x) \mid Ax = y\}$, is polyhedral convex. -/
theorem corollary_19_3_1_image {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m) :
    PolyhedralFn (mapLin A f) :=
  PolyhedralFn.mapLin hf A

/-- **Corollary 19.3.1** of [rockafellar1970convex], attainment. Let $A$ be a linear transformation
from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $f$ be a polyhedral convex function on
$\mathbb{R}^n$. If $(Af)(y)$ is finite, then there is $x$ with $Ax = y$ and $f(x) = (Af)(y)$:
the infimum is attained. -/
theorem corollary_19_3_1_attained {f : Rn n → EReal} (hf : PolyhedralFn f) (A : Rn n →ₗ[ℝ] Rn m)
    {y : Rn m} {μ : ℝ} (hy : mapLin A f y = (μ : EReal)) :
    ∃ x : Rn n, A x = y ∧ f x = mapLin A f y :=
  exists_mapLin_eq_of_polyhedralFn hf A hy

/-- **Corollary 19.3.1** of [rockafellar1970convex], inverse images. Let $A$ be a linear
transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$. If $g$ is a polyhedral convex function on
$\mathbb{R}^m$, then $gA$, with $(gA)(x) = g(Ax)$, is polyhedral convex. -/
theorem corollary_19_3_1_preimage {g : Rn m → EReal} (hg : PolyhedralFn g)
    (A : Rn n →ₗ[ℝ] Rn m) : PolyhedralFn (compLin g A) :=
  PolyhedralFn.compLin hg A

/-- **Corollary 19.3.2** of [rockafellar1970convex]. If $C_1, C_2 \subseteq \mathbb{R}^n$ are
polyhedral convex sets, then $C_1 + C_2$ is polyhedral. -/
theorem corollary_19_3_2 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂) :
    Polyhedral (C₁ + C₂) :=
  h₁.add h₂

/-- **Corollary 19.3.3** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be non-empty disjoint
polyhedral convex sets in $\mathbb{R}^n$. Then there is a hyperplane that separates $C_1$ and
$C_2$ strongly: a continuous linear function $\varphi$ and a number $c$ with
$$\sup_{x \in C_1} \varphi(x) < c < \inf_{x \in C_2} \varphi(x).$$

The non-emptiness hypotheses of the source are kept, but the proof does not use them. The set
$C_1 - C_2$ is polyhedral, hence closed, and Theorem 11.4 applies. Strong separation is
`ConvexAnalysis.SeparatesStrongly`. -/
theorem corollary_19_3_3 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (h₂ : Polyhedral C₂)
    (_hne₁ : C₁.Nonempty) (_hne₂ : C₂.Nonempty) (hdisj : Disjoint C₁ C₂) :
    ∃ (φ : Rn n →L[ℝ] ℝ) (c : ℝ), SeparatesStrongly φ c C₁ C₂ :=
  separatesStrongly_of_polyhedral h₁ h₂ hdisj

/-- **Corollary 19.3.4** of [rockafellar1970convex]. If $f_1$ and $f_2$ are polyhedral convex
functions on $\mathbb{R}^n$, then the infimal convolution $f_1 \mathbin{\square} f_2$ is
polyhedral convex.

**Generalization.** The source assumes $f_1$ and $f_2$ proper. This is not needed. -/
theorem corollary_19_3_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂) :
    PolyhedralFn (infConv f₁ f₂) :=
  h₁.infConv h₂

/-- **Corollary 19.3.4** of [rockafellar1970convex], attainment. Let $f_1$ and $f_2$ be polyhedral
convex functions on $\mathbb{R}^n$. If $(f_1 \mathbin{\square} f_2)(x) = \mu$ is finite, then
there are $x_1, x_2$ with $x_1 + x_2 = x$ and $f_1(x_1) + f_2(x_2) \le \mu$, so the infimum in
$$(f_1 \mathbin{\square} f_2)(x) = \inf \{f_1(x_1) + f_2(x_2) \mid x_1 + x_2 = x\}$$
is attained. -/
theorem corollary_19_3_4_attained {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁)
    (h₂ : PolyhedralFn f₂) {x : Rn n} {μ : ℝ} (hx : infConv f₁ f₂ x = (μ : EReal)) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f₁ x₁ + f₂ x₂ ≤ (μ : EReal) := by
  have hmem : ((x, μ) : Rn n × ℝ) ∈ epi (infConv f₁ f₂) := mk_mem_epi.2 (le_of_eq hx)
  rw [epi_infConv_of_polyhedralFn h₁ h₂] at hmem
  obtain ⟨⟨x₁, μ₁⟩, hp₁, ⟨x₂, μ₂⟩, hp₂, hsum⟩ := hmem
  refine ⟨x₁, x₂, congrArg Prod.fst hsum, ?_⟩
  have hμ : μ₁ + μ₂ = μ := congrArg Prod.snd hsum
  calc f₁ x₁ + f₂ x₂ ≤ (μ₁ : EReal) + (μ₂ : EReal) :=
        add_le_add (mk_mem_epi.1 hp₁) (mk_mem_epi.1 hp₂)
    _ = (μ : EReal) := by rw [← EReal.coe_add, hμ]

/-! ### Theorem 19.4 -/

/-- **Theorem 19.4** of [rockafellar1970convex]. If $f_1$ and $f_2$ are proper polyhedral convex
functions on $\mathbb{R}^n$, then $f_1 + f_2$ is polyhedral.

The proof uses properness only through $f_i(x) > -\infty$ for all $x$. This makes valid the
splitting $f_1(x) + f_2(x) \le \mu$ if and only if $f_1(x) \le \alpha$ and $f_2(x) \le \beta$
for some $\alpha + \beta = \mu$, which fails for the sum $(+\infty) + (-\infty)$. -/
theorem theorem_19_4 {f₁ f₂ : Rn n → EReal} (h₁ : PolyhedralFn f₁) (h₂ : PolyhedralFn f₂)
    (hp₁ : ProperConvex f₁) (hp₂ : ProperConvex f₂) : PolyhedralFn (f₁ + f₂) :=
  h₁.add h₂ hp₁.ne_bot hp₂.ne_bot

/-! ### The normal form $f = h + \delta(\cdot \mid C)$ -/

/-- **Section 19** of [rockafellar1970convex], the normal form of a polyhedral convex function. Let
$f$ be a function from $\mathbb{R}^n$ to $(-\infty, +\infty]$. Then $f$ is polyhedral convex if
and only if there are finitely many pairs $(b_i, \beta_i) \in \mathbb{R}^n \times \mathbb{R}$
and a polyhedral convex set $C$ with
$$f(x) = h(x) + \delta(x \mid C), \qquad h(x) = \max_i \{\langle x, b_i \rangle - \beta_i\}.$$

The source writes $C = \{x \mid \langle x, b_i \rangle \le \beta_i,\ i = k + 1, \dots, m\}$ with
a second family of pairs. The two families are the two kinds of closed half-space that can bound
the epigraph in $\mathbb{R}^{n+1}$: epigraphs of affine functions, and vertical half-spaces.

The hypothesis that $f$ never takes the value $-\infty$ cannot be omitted. In `EReal` the sum
$(-\infty) + (+\infty)$ is $-\infty$, so a function of the form $h + \delta(\cdot \mid C)$ takes
the value $-\infty$ only inside $C$, and the function that is $-\infty$ on a non-empty
polyhedral set and $+\infty$ outside it is convex with a polyhedral epigraph. -/
theorem polyhedralFn_iff_normalForm {f : Rn n → EReal} (hb : ∀ x, f x ≠ ⊥) :
    PolyhedralFn f ↔ ∃ (s : Finset (Rn n × ℝ)) (C : Set (Rn n)), Polyhedral C ∧
      ∀ x, f x = (⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal)) + indicatorFn C x := by
  classical
  have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ a : Rn n, ∀ x, φ x = pairing n x a := by
    intro φ
    obtain ⟨a, ha⟩ := exists_pairing_eq (pairing n) (LinearMap.toContinuousLinearMap φ)
    exact ⟨a, fun x => ha x⟩
  choose rep hrep using hrep
  constructor
  · intro hf
    obtain ⟨s, C, hC, hfC⟩ := (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).1 hf
    refine ⟨s.image fun q => (rep q.1, q.2), C, hC, fun x => ?_⟩
    have hval : f x = maxAffineFn s x + indicatorFn C x := congrFun hfC x
    have hunfold : maxAffineFn s x = ⨆ q ∈ s, ((q.1 x - q.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn s x
        = ⨆ q ∈ s.image fun q => (rep q.1, q.2), ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun ψ hψ => ?_)
      · refine le_iSup₂_of_le (rep ψ.1, ψ.2) (Finset.mem_image_of_mem _ hψ) (le_of_eq ?_)
        rw [hrep ψ.1 x]
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        refine le_iSup₂_of_le q hq (le_of_eq ?_)
        rw [hrep q.1 x]
    rw [hval, hmax]
  · rintro ⟨s, C, hC, hfC⟩
    refine (polyhedralFn_iff_maxAffineFn_add_indicatorFn hb).2
      ⟨s.image fun q => ((pairing n).flip q.1, q.2), C, hC, funext fun x => ?_⟩
    have hunfold : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ ψ ∈ s.image fun q => ((pairing n).flip q.1, q.2),
            ((ψ.1 x - ψ.2 : ℝ) : EReal) := rfl
    have hmax : maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x
        = ⨆ q ∈ s, ((pairing n x q.1 - q.2 : ℝ) : EReal) := by
      rw [hunfold]
      refine le_antisymm (iSup₂_le fun ψ hψ => ?_) (iSup₂_le fun q hq => ?_)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
        exact le_iSup₂_of_le q hq (le_of_eq rfl)
      · exact le_iSup₂_of_le ((pairing n).flip q.1, q.2)
          (Finset.mem_image_of_mem _ hq) (le_of_eq rfl)
    change f x = maxAffineFn (s.image fun q => ((pairing n).flip q.1, q.2)) x + indicatorFn C x
    rw [hmax]
    exact hfC x

/-! ### Theorem 19.5 and its corollary -/

/-- **Theorem 19.5** of [rockafellar1970convex], scalar multiples. If $C \subseteq \mathbb{R}^n$ is
polyhedral convex, then $\lambda C$ is polyhedral for every real $\lambda$.

One statement covers $\lambda > 0$, $\lambda = 0$ and $\lambda < 0$, so the case distinction of
the source is not reproduced. -/
theorem theorem_19_5_smul {C : Set (Rn n)} (hC : Polyhedral C) (l : ℝ) : Polyhedral (l • C) :=
  hC.smul l

/-- **Theorem 19.5** of [rockafellar1970convex], recession cone. The recession cone $0^+ C$ of a
non-empty polyhedral convex set $C \subseteq \mathbb{R}^n$ is a polyhedral convex cone. -/
theorem theorem_19_5_recession {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (recessionCone C) :=
  hC.polyhedralCone_recessionCone hne

/-- **Theorem 19.5** of [rockafellar1970convex], generators. Let $C = \operatorname{conv} S$ be
non-empty, for a finite set $S$ of points $P$ and directions $D$ in $\mathbb{R}^n$. Then
$0^+ C = \operatorname{conv} S_0$, where $S_0$ consists of the origin and the directions of $S$:
the recession cone is the convex cone generated by $D$. -/
theorem theorem_19_5_generators {C : Set (Rn n)} {P D : Finset (Rn n)}
    (hPD : C = convexHullPD (P : Set (Rn n)) (D : Set (Rn n))) (hne : C.Nonempty) :
    recessionCone C = (PointedCone.hull ℝ (D : Set (Rn n)) : Set (Rn n)) :=
  recessionCone_of_finitelyGenerated hPD hne

/-- **Corollary 19.5.1** of [rockafellar1970convex]. Let $f$ be a proper polyhedral convex function
on $\mathbb{R}^n$. Then $f \lambda$ is polyhedral for every $\lambda \ge 0$ and for
$\lambda = 0^+$.

The coefficient is `Rockafellar.ExtCoeff`. The function $f \lambda$ is
`Rockafellar.ExtCoeff.smulFn`: right scalar multiplication for real $\lambda$, and the recession
function $f 0^+$ for $\lambda = 0^+$. -/
theorem corollary_19_5_1 {f : Rn n → EReal} (hf : PolyhedralFn f) (hp : ProperConvex f)
    {l : ExtCoeff} (hl : l.Nonneg) : PolyhedralFn (l.smulFn f) := by
  cases l with
  | ofReal t =>
    rw [ExtCoeff.smulFn_ofReal]
    rcases eq_or_lt_of_le (hl : (0 : ℝ) ≤ t) with ht | ht
    · rw [← ht, smulRight_zero hp.convexDom_nonempty]
      exact polyhedralFn_indicatorFn polyhedral_zero
    · change Polyhedral (epi (smulRight f t))
      rw [epi_smulRight ht]
      exact hf.smul t
  | zeroPlus =>
    change Polyhedral (epi (recessionFn f))
    rw [epi_recessionFn]
    exact (hf.polyhedralCone_recessionCone
      ((epi_nonempty_iff f).2 hp.convexDom_nonempty)).polyhedral

/-! ### Theorems 19.6 and 19.7 -/

/-- **Theorem 19.6** of [rockafellar1970convex], for two sets. If $C_1, C_2 \subseteq \mathbb{R}^n$
are non-empty polyhedral convex sets, then $\operatorname{cl}(\operatorname{conv}(C_1 \cup
C_2))$ is polyhedral.

The source prints Theorem 19.6 without a proof. The proof formalized here is the argument in the
text around it. -/
theorem theorem_19_6 {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    Polyhedral (closure (convexHull ℝ (C₁ ∪ C₂))) :=
  polyhedral_closure_convexHull_union h₁ hne₁ h₂ hne₂

/-- **Theorem 19.6** of [rockafellar1970convex], formula for two sets. If
$C_1, C_2 \subseteq \mathbb{R}^n$ are non-empty polyhedral convex sets, then
$$\operatorname{cl}(\operatorname{conv}(C_1 \cup C_2)) = \bigcup \{\lambda_1 C_1 + \lambda_2 C_2
  \mid \lambda_i \ge 0^+,\ \lambda_1 + \lambda_2 = 1\},$$
where $0^+ C_i$ is used in place of $0 C_i$ when $\lambda_i = 0^+$.

The union is over pairs of `Rockafellar.ExtCoeff`, as in Theorem 9.8. In the sum
$\lambda_1 + \lambda_2$, the coefficient $0^+$ counts as $0$. -/
theorem theorem_19_6_iUnion {C₁ C₂ : Set (Rn n)} (h₁ : Polyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Polyhedral C₂) (hne₂ : C₂.Nonempty) :
    closure (convexHull ℝ (C₁ ∪ C₂))
      = ⋃ p : ExtCoeff × ExtCoeff,
          ⋃ _ : p.1.Nonneg ∧ p.2.Nonneg ∧ p.1.toReal + p.2.toReal = 1,
            p.1.smulSet C₁ + p.2.smulSet C₂ := by
  rw [iUnion_extCoeff_pair h₁.convex hne₁ h₂.convex hne₂]
  exact (finitelyGenerated_closure_convexHull_union h₁ hne₁ h₂ hne₂).2

/-- **Theorem 19.6** of [rockafellar1970convex], for $m$ sets. If
$C_1, \dots, C_m \subseteq \mathbb{R}^n$ are non-empty polyhedral convex sets, then
$\operatorname{cl}(\operatorname{conv}(C_1 \cup \cdots \cup C_m))$ is polyhedral.

The sets are indexed by a `Finset`. The empty family is allowed, and then the set is empty. -/
theorem theorem_19_6_biUnion {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    Polyhedral (closure (convexHull ℝ (⋃ i ∈ s, C i))) :=
  polyhedral_closure_convexHull_biUnion hC hne

/-- **Theorem 19.6** of [rockafellar1970convex], formula for $m$ sets without the convention $0^+$.
If $C_1, \dots, C_m \subseteq \mathbb{R}^n$ are non-empty polyhedral convex sets, then
$$\operatorname{cl}(\operatorname{conv}(C_1 \cup \cdots \cup C_m)) = \operatorname{conv}(C_1
  \cup \cdots \cup C_m) + (0^+ C_1 + \cdots + 0^+ C_m).$$

The sum of the recession cones expresses what the union over the coefficients
$\lambda_i \ge 0^+$ expresses in the source. -/
theorem theorem_19_6_biUnion_add {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Polyhedral (C i)) (hne : ∀ i ∈ s, (C i).Nonempty) :
    closure (convexHull ℝ (⋃ i ∈ s, C i))
      = convexHull ℝ (⋃ i ∈ s, C i) + ∑ i ∈ s, recessionCone (C i) :=
  (finitelyGenerated_closure_convexHull_biUnion hC hne).2

/-- For a convex set $C \subseteq \mathbb{R}^n$,
$$\bigcup \{\lambda C \mid \lambda > 0 \text{ or } \lambda = 0^+\} = \operatorname{cone} C + 0^+
  C,$$
where $\operatorname{cone} C$ is the convex cone generated by $C$, which contains the origin.
This is the convention $\lambda \ge 0^+$ for one set. Theorem 19.7 assumes $C$ non-empty, but
the identity does not need it: for $C = \emptyset$ both sides are
$0^+ \emptyset = \mathbb{R}^n$. -/
theorem iUnion_extCoeff_pos {C : Set (Rn n)} (hC : Convex ℝ C) :
    (⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C)
      = (PointedCone.hull ℝ C : Set (Rn n)) + recessionCone C := by
  have hzeroK : (0 : Rn n) ∈ (PointedCone.hull ℝ C : Set (Rn n)) :=
    (PointedCone.hull ℝ C).zero_mem
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨l, hl, hmem⟩ := Set.mem_iUnion₂.1 hx
    cases l with
    | ofReal t =>
      obtain ⟨y, hy, hyx⟩ := hmem
      have hyx' : t • y = x := hyx
      have hKt : x ∈ (PointedCone.hull ℝ C : Set (Rn n)) := by
        rw [← hyx']
        exact Submodule.smul_mem _ (⟨t, (hl : (0 : ℝ) < t).le⟩ : {c : ℝ // 0 ≤ c})
          (PointedCone.subset_hull hy)
      simpa using Set.add_mem_add hKt (zero_mem_recessionCone C)
    | zeroPlus => simpa using Set.add_mem_add hzeroK hmem
  · obtain ⟨u, hu, v, hv, huv⟩ := hx
    have huv' : u + v = x := huv
    rcases (mem_coe_hull_iff_of_convex hC).1 hu with rfl | ⟨t, ht, y, hy, hty⟩
    · refine Set.mem_iUnion₂.2 ⟨ExtCoeff.zeroPlus, trivial, ?_⟩
      rw [ExtCoeff.smulSet_zeroPlus, ← huv', zero_add]
      exact hv
    · have hty' : t • y = u := hty
      refine Set.mem_iUnion₂.2 ⟨ExtCoeff.ofReal t, ht, ?_⟩
      rw [ExtCoeff.smulSet_ofReal]
      have hyC : y + t⁻¹ • v ∈ C :=
        add_mem_of_mem_recessionCone (smul_mem_recessionCone (by positivity) hv) hy
      have hmem := Set.smul_mem_smul_set (a := t) hyC
      have hval : t • (y + t⁻¹ • v) = x := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul, hty', huv']
      rwa [hval] at hmem

/-- **Theorem 19.7** of [rockafellar1970convex]. If $C \subseteq \mathbb{R}^n$ is a non-empty
polyhedral convex set, then the closure of the convex cone generated by $C$ is a polyhedral
convex cone.

The closure is needed. For $C$ the horizontal line at height $1$ in $\mathbb{R}^2$, the cone
generated by $C$ is the open upper half-plane together with the origin, and the horizontal
directions that it misses are exactly $0^+ C$. -/
theorem theorem_19_7 {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    PolyhedralCone (closure (PointedCone.hull ℝ C : Set (Rn n))) :=
  polyhedralCone_closure_coe_hull hC hne

/-- **Theorem 19.7** of [rockafellar1970convex], formula. If $C \subseteq \mathbb{R}^n$ is a
non-empty polyhedral convex set, then the closure $K$ of the convex cone generated by $C$ is
$$K = \bigcup \{\lambda C \mid \lambda > 0 \text{ or } \lambda = 0^+\}.$$

The proof uses `Rockafellar.iUnion_extCoeff_pos` to identify the union with
$\operatorname{cone} C + 0^+ C$. -/
theorem theorem_19_7_iUnion {C : Set (Rn n)} (hC : Polyhedral C) (hne : C.Nonempty) :
    closure (PointedCone.hull ℝ C : Set (Rn n)) = ⋃ l : ExtCoeff, ⋃ _ : l.Pos, l.smulSet C := by
  rw [iUnion_extCoeff_pos hC.convex]
  exact (finitelyGeneratedCone_closure_coe_hull hC hne).2

/-- **Corollary 19.7.1** of [rockafellar1970convex]. If a polyhedral convex set
$C \subseteq \mathbb{R}^n$ contains the origin, then the convex cone generated by $C$ is
polyhedral, with no closure needed. -/
theorem corollary_19_7_1 {C : Set (Rn n)} (hC : Polyhedral C) (h0 : (0 : Rn n) ∈ C) :
    PolyhedralCone (PointedCone.hull ℝ C : Set (Rn n)) :=
  (finitelyGeneratedCone_hull_of_zero_mem hC h0).polyhedralCone

end Rockafellar
