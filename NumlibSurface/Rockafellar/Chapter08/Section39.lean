import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Process.Linear
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar §39: convex processes

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39
(pp. 413–424). A **convex process** from `ℝᵐ` to `ℝⁿ` is a multivalued map whose graph is a convex
cone containing the origin. It sits between a linear transformation and a convex bifunction, and it
inherits a full duality theory from §§30–38.

All nine numbered results of §39 are formalized: Theorems 39.1–39.8 and Corollary 39.7.1.

**Orientation is data, not a convention.** Rockafellar is explicit: "an oriented convex set is a
pair consisting of a convex set and one of the words *supremum* or *infimum*". Theorems 39.5 and
39.8 require two processes to carry the **same** orientation and Theorem 39.2 **flips** it, so both
orientations have to be simultaneously expressible: a global convention of the kind §36 imposes on
saddle-functions cannot even state Theorem 39.5.

## Main definitions

* `Orientation`, `OrientedProcess`, `Orientation.adjointProcess` — the book's orientation and the
  dispatch it drives; `adjoint`, `inv`, `add_process`, `smul_process`, `comp` and `bracket` are the
  oriented operations built on it.
* `Orientation.bracketSet`, `bracket` — the inner products `⟨C, x*⟩` and `⟨Au, x*⟩`, read as a
  support function under the supremum orientation and as its reflection under the infimum one.
* `imageFn` — the image `(Af)(x) = inf {f u | u ∈ A⁻¹x}` of a convex function under a process.
* `PolyhedralConvexProcess` — a surface definition; no numbered result of §39 needs it.
* `convexProcessEquivGraph`, `convexProcessCompleteLattice` — a convex process *is* its graph, and
  the processes from `ℝᵐ` to `ℝⁿ` form a complete lattice under inclusion of graphs.

## Main results

* `eval_convex`, `dom_convex`, `range_convex`, `dom_inv`, `range_inv`, `add_eval_zero_subset`,
  `comp_assoc`, `id_comp`, `comp_id`, `inv_comp`, `inv_comp_ne_id`, `comp_add_le`, `add_comp_le` —
  the elementary algebra, including that `A⁻¹A` is not the identity and that the distributive laws
  hold only as inclusions.
* `theorem_39_1`, `theorem_39_1_isBounded` — a convex process with `dom A = ℝᵐ` and `A 0 = {0}` is
  a linear transformation.
* `theorem_39_2`, `theorem_39_2_orientation`, `theorem_39_2_isClosed`,
  `theorem_39_2_eq_self_iff`, `theorem_39_2_indicatorBifun` — `A*` is a closed process of the
  opposite orientation and `A** = cl A`.
* `theorem_39_3_*` — `⟨Au, x*⟩` is positively homogeneous and convex resp. concave according to the
  orientation, `⟨u, A* x*⟩` is its closure in `u`, and the two agree over `ri (dom A)`.
* `theorem_39_4`, `theorem_39_4_eval` — the one-to-one correspondence between closed convex
  processes and the saddle-functions `K (u, x*) = ⟨Au, x*⟩`.
* `theorem_39_5`, `theorem_39_5_isClosed`, `theorem_39_5_closure`, `theorem_39_6` —
  `(A₁ + A₂)* = A₁* + A₂*` and `(λA)* = λA*`.
* `theorem_39_7`, `theorem_39_7_attained`, `theorem_39_7_closedFn`, `theorem_39_7_attained_image`,
  `theorem_39_7_closure`, `corollary_39_7_1`, `corollary_39_7_1_isBounded` — the image of a convex
  function, `(Af)* = A*⁻¹ f*`, and the closedness of `A C` for a closed convex `C`.
* `theorem_39_8`, `theorem_39_8_isClosed`, `theorem_39_8_closure` — `(BA)* = A* B*`.

## Divergences from the book

Theorem 39.1 is stated with `A 0 = {0}` where the book assumes `A 0` bounded. The first line of
Rockafellar's proof turns one into the other and nothing later uses boundedness, so `A 0 = {0}` is
the hypothesis the theorem actually has, and it needs neither a norm nor finite dimension;
`theorem_39_1_isBounded` recovers the book's literal form.

Theorems 39.5, 39.7 and 39.8 carry an `IsExactSum` where the book carries a relative-interior
condition. `IsExactSum` demands **proper** summands, and the summands here are `u ↦ -⟨Aᵢ u, x*⟩`,
which take `-∞` wherever `Aᵢ u` is unbounded in the direction `x*`; quantified over all `x*` that
forces `dom Aᵢ* = ℝⁿ`. The hypothesis is therefore strictly stronger than the book's — strong
enough to exclude §39's own running example `Au = {x | x ≤ Bu}` for `u ≥ 0` — and the gap is not
closable by `IsExactSum.of_relint`.

Theorem 39.3's last assertion is stated without closedness on the `u` side, where the book prefixes
both halves with "if `A` is closed": that half is Corollary 33.2.1.
-/

namespace Rockafellar

open Pointwise Set ConvexAnalysis

variable {m n p : ℕ}

/-! ### Convex processes: the elementary properties -/

/-- Each value `A u` of a convex process is a convex set. -/
theorem eval_convex (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) : Convex ℝ (A.eval u) :=
  A.convex_eval u

/-- `A 0` consists precisely of the vectors `y` with `A u + y ⊆ A u` for every `u`. -/
theorem add_eval_zero_subset (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    A.eval u + A.eval 0 ⊆ A.eval u :=
  A.add_eval_zero_subset u

/-- `dom A = {u | A u ≠ ∅}` is a convex cone containing the origin. -/
theorem dom_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.dom := A.convex_dom

/-- `range A = ⋃ {A u | u ∈ ℝᵐ}` is a convex cone containing the origin. -/
theorem range_convex (A : ConvexProcess (Rn m) (Rn n)) : Convex ℝ A.range := A.convex_range

/-- `dom A⁻¹ = range A`. -/
theorem dom_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.dom = A.range := A.dom_inv

/-- `range A⁻¹ = dom A`. -/
theorem range_inv (A : ConvexProcess (Rn m) (Rn n)) : A.inv.range = A.dom := A.range_inv

/-! ### Theorem 39.1 -/

/-- **Theorem 39.1.** A convex process from `ℝᵐ` to `ℝⁿ` with `dom A = ℝᵐ` and `A 0 = {0}` is a
linear transformation.

Rockafellar's hypothesis is that `A 0` be *bounded*, and the first line of his proof turns that into
`A 0 = {0}`; nothing later uses boundedness. The hypothesis here is therefore strictly weaker than
the book's, and it needs neither a norm nor finite dimension. -/
theorem theorem_39_1 (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hzero : A.eval 0 = {0}) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  A.exists_linearMap_of_isBounded hdom (by rw [hzero]; exact Bornology.isBounded_singleton)

/-- **Theorem 39.1** in the book's literal form, with `A 0` bounded. The two hypotheses coincide,
`A 0` being a convex cone containing the origin. -/
theorem theorem_39_1_isBounded (A : ConvexProcess (Rn m) (Rn n)) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : Rn m →ₗ[ℝ] Rn n, ∀ u, A.eval u = {T u} :=
  theorem_39_1 A hdom (A.eval_zero_eq_zero_of_isBounded hb)

/-! ### Polyhedral convex processes -/

/-- A convex process is **polyhedral** if its graph is a polyhedral convex cone. No numbered result
of §39 needs this — all nine are proved without it — so it is a surface definition, with
`polyhedral_graph_of_polyhedral` as the bridge to `Polyhedral`. -/
def PolyhedralConvexProcess (A : ConvexProcess (Rn m) (Rn n)) : Prop :=
  PolyhedralCone (A.graph : Set (Rn m × Rn n))

/-- The graph of a polyhedral convex process is a polyhedral convex set. -/
theorem polyhedral_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : Polyhedral (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.polyhedral hA

/-- A polyhedral convex process is closed, a polyhedral convex cone being closed. -/
theorem isClosed_graph_of_polyhedral {A : ConvexProcess (Rn m) (Rn n)}
    (hA : PolyhedralConvexProcess A) : IsClosed (A.graph : Set (Rn m × Rn n)) :=
  PolyhedralCone.isClosed hA

/-! ### The algebra of convex processes -/

/-- `dom (A₁ + A₂) = dom A₁ ∩ dom A₂`. -/
theorem dom_add (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    (A₁ + A₂).dom = A₁.dom ∩ A₂.dom :=
  ConvexProcess.dom_add A₁ A₂

/-- The image `A C` of a convex set under a convex process is convex. -/
theorem image_convex (A : ConvexProcess (Rn m) (Rn n)) {C : Set (Rn m)} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) :=
  A.convex_image hC

/-- The **image of a convex function under a convex process**, `(Af)(x) = inf {f u | u ∈ A⁻¹x}`.
This is `imageBifun` at the indicator bifunction of `A`; `imageFn_apply` turns the unrestricted
infimum of `imageBifun` into the book's restricted one. -/
noncomputable def imageFn (A : ConvexProcess (Rn m) (Rn n)) (f : Rn m → EReal) : Rn n → EReal :=
  imageBifun A.indicatorBifun f

/-- `(Af)(x) = inf {f u | u ∈ A⁻¹x}`, the book's own formula. The hypothesis `f u ≠ ⊥` is what
turns the summand `f u + δ(x | A u)` into `⊤` off the fibre; it is automatic for the proper convex
`f` of Theorem 39.7. -/
theorem imageFn_apply (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal}
    (hf : ∀ u, f u ≠ ⊥) (x : Rn n) :
    imageFn A f x = ⨅ u ∈ A.inv.eval x, f u := by
  have hunfold : imageFn A f x = ⨅ u, f u + A.indicatorBifun u x := rfl
  rw [hunfold]
  refine iInf_congr fun u => ?_
  by_cases hu : u ∈ A.inv.eval x
  · rw [ConvexProcess.indicatorBifun_apply, indicatorFn_of_mem (show x ∈ A.eval u from hu),
      add_zero, iInf_pos hu]
  · rw [ConvexProcess.indicatorBifun_apply,
      indicatorFn_of_notMem (show x ∉ A.eval u from hu), iInf_neg hu]
    exact EReal.add_top_of_ne_bot (hf u)

/-- `(BA)⁻¹ = A⁻¹B⁻¹`. -/
theorem inv_comp (B : ConvexProcess (Rn n) (Rn p)) (A : ConvexProcess (Rn m) (Rn n)) :
    (B.comp A).inv = A.inv.comp B.inv :=
  ConvexProcess.inv_comp B A

/-- Multiplication of convex processes is associative, so the convex processes from `ℝⁿ` to itself
form a semigroup under multiplication. -/
theorem comp_assoc {q : ℕ} (C : ConvexProcess (Rn p) (Rn q)) (B : ConvexProcess (Rn n) (Rn p))
    (A : ConvexProcess (Rn m) (Rn n)) : (C.comp B).comp A = C.comp (B.comp A) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  constructor
  · rintro ⟨x, hx, z, hz, hw⟩
    exact ⟨z, ⟨x, hx, hz⟩, hw⟩
  · rintro ⟨z, ⟨x, hx, hz⟩, hw⟩
    exact ⟨x, hx, z, hz, hw⟩

/-- The identity transformation is a left identity for multiplication of convex processes. -/
theorem id_comp (A : ConvexProcess (Rn m) (Rn n)) :
    (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn n))).comp A = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hz' : x = w := hz
    rwa [hz']
  · intro hr
    exact ⟨x, hr, rfl⟩

/-- And a right identity. -/
theorem comp_id (A : ConvexProcess (Rn m) (Rn n)) :
    A.comp (ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn m))) = A := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨u, x⟩ := r
  constructor
  · rintro ⟨w, hw, hz⟩
    have hw' : w = u := hw
    rwa [hw'] at hz
  · intro hr
    exact ⟨u, rfl, hr⟩

/-- `A⁻¹A` is in general multivalued and **not** the identity transformation: for the zero map on
`ℝ¹`, `A⁻¹0 = ℝ¹` and `(A⁻¹A) u = ℝ¹`, whereas `I u = {u}`. This is why the convex processes from
`ℝⁿ` to itself form a semigroup and not a group. -/
theorem inv_comp_ne_id :
    ∃ A : ConvexProcess (Rn 1) (Rn 1),
      A.inv.comp A ≠ ConvexProcess.ofLinearMap (LinearMap.id (R := ℝ) (M := Rn 1)) := by
  refine ⟨ConvexProcess.ofLinearMap 0, fun hc => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Rn 1)
  have hmem : ((0 : Rn 1), v) ∈
      ((ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1)).inv.comp
        (ConvexProcess.ofLinearMap (0 : Rn 1 →ₗ[ℝ] Rn 1))).graph := ⟨0, rfl, rfl⟩
  rw [hc] at hmem
  exact hv hmem

/-- The first distributive inequality: `A(A₁ + A₂) ⊇ AA₁ + AA₂`, inclusion in the sense of
graphs. -/
theorem comp_add_le (A : ConvexProcess (Rn n) (Rn p)) (A₁ A₂ : ConvexProcess (Rn m) (Rn n)) :
    ((A.comp A₁) + (A.comp A₂)).graph ≤ (A.comp (A₁ + A₂)).graph := by
  rintro ⟨u, z⟩ ⟨z₁, ⟨x₁, hx₁, hz₁⟩, z₂, ⟨x₂, hx₂, hz₂⟩, hz⟩
  refine ⟨x₁ + x₂, ⟨x₁, hx₁, x₂, hx₂, rfl⟩, ?_⟩
  have hz' : z = z₁ + z₂ := hz
  rw [hz']
  exact A.add_mem_graph hz₁ hz₂

/-- The second distributive inequality: `(A₁ + A₂)A ⊆ A₁A + A₂A`. -/
theorem add_comp_le (A : ConvexProcess (Rn m) (Rn n)) (A₁ A₂ : ConvexProcess (Rn n) (Rn p)) :
    ((A₁ + A₂).comp A).graph ≤ ((A₁.comp A) + (A₂.comp A)).graph := by
  rintro ⟨u, z⟩ ⟨x, hx, z₁, hz₁, z₂, hz₂, hz⟩
  exact ⟨z₁, ⟨x, hx, hz₁⟩, z₂, ⟨x, hx, hz₂⟩, hz⟩

/-! ### The complete lattice of convex processes

The lattice of pointed cones is Mathlib's `Submodule` lattice, and the structure is transported
along the graph bijection rather than rebuilt. -/

/-- A convex process **is** its graph: the bijection between convex processes and pointed convex
cones in the product, along which the lattice structure is transported. -/
def convexProcessEquivGraph (m n : ℕ) :
    ConvexProcess (Rn m) (Rn n) ≃ PointedCone ℝ (Rn m × Rn n) where
  toFun A := A.graph
  invFun K := ⟨K⟩
  left_inv A := by cases A; rfl
  right_inv _ := rfl

/-- The convex processes from `ℝᵐ` to `ℝⁿ` form a **complete lattice** under inclusion, "inasmuch
as the collection of all convex cones containing the origin in `ℝᵐ⁺ⁿ` is a complete lattice under
inclusion". -/
noncomputable instance convexProcessCompleteLattice :
    CompleteLattice (ConvexProcess (Rn m) (Rn n)) :=
  (convexProcessEquivGraph m n).completeLattice

/-- The order of the lattice is inclusion of graphs, Rockafellar's `A ⊇ B` read the other way
round. -/
theorem convexProcess_le_iff {A B : ConvexProcess (Rn m) (Rn n)} :
    A ≤ B ↔ (A.graph : Set (Rn m × Rn n)) ⊆ B.graph :=
  Iff.rfl

/-! ### Orientation -/

/-- **Rockafellar's orientation**: "an oriented convex set is a pair consisting of a convex set and
one of the words *supremum* or *infimum*". This is that word. -/
inductive Orientation where
  /-- The supremum orientation: `C` is identified with `δ(· | C)`. -/
  | sup : Orientation
  /-- The infimum orientation: `C` is identified with `-δ(· | C)`. -/
  | inf : Orientation
  deriving DecidableEq

/-- The opposite orientation. The inverse of an oriented convex process is given the opposite
orientation, and so is its adjoint (Theorem 39.2). -/
def Orientation.flip : Orientation → Orientation
  | Orientation.sup => Orientation.inf
  | Orientation.inf => Orientation.sup

@[simp] theorem Orientation.flip_sup : Orientation.sup.flip = Orientation.inf := rfl

@[simp] theorem Orientation.flip_inf : Orientation.inf.flip = Orientation.sup := rfl

@[simp] theorem Orientation.flip_flip (o : Orientation) : o.flip.flip = o := by cases o <;> rfl

/-- The inner product `⟨C, x*⟩ = ⟨x*, C⟩` of an **oriented convex set** with a vector: the supremum
of `⟨x, x*⟩` over `C` when `C` is supremum oriented, the infimum when it is infimum oriented. -/
noncomputable def Orientation.bracketSet (o : Orientation) (C : Set (Rn n)) (y : Rn n) : EReal :=
  match o with
  | Orientation.sup => ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal)
  | Orientation.inf => ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal)

@[simp] theorem Orientation.bracketSet_sup (C : Set (Rn n)) (y : Rn n) :
    Orientation.sup.bracketSet C y = ⨆ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

@[simp] theorem Orientation.bracketSet_inf (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = ⨅ x ∈ C, ((pairing n x y : ℝ) : EReal) := rfl

/-- For a supremum-oriented convex set, `⟨C, ·⟩` is the support function of `C`, the convex
conjugate of `δ(· | C)`. -/
theorem bracketSet_sup_eq_supportFn (C : Set (Rn n)) :
    Orientation.sup.bracketSet C = supportFn (pairing n) C :=
  funext fun y => (supportFn_apply (pairing n) C y).symm

/-- For an infimum-oriented convex set, `⟨C, x*⟩ = -δ*(-x* | C)`; that is, `⟨C, ·⟩` is the concave
conjugate of `-δ(· | C)`. -/
theorem bracketSet_inf_eq_neg_supportFn (C : Set (Rn n)) (y : Rn n) :
    Orientation.inf.bracketSet C y = -(supportFn (pairing n) C (-y)) := by
  rw [Orientation.bracketSet_inf, supportFn_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [← EReal.coe_neg, map_neg (pairing n x) y, _root_.neg_neg]

/-- An **oriented convex process** is a convex process together with an orientation, `A u` carrying
that orientation for every `u`. It must be a pair: Theorems 39.5 and 39.8 require two processes to
carry the *same* orientation and Theorem 39.2 flips it, so no global convention can state them. -/
@[ext] structure OrientedProcess (m n : ℕ) where
  /-- The underlying convex process. -/
  process : ConvexProcess (Rn m) (Rn n)
  /-- The orientation, one of the two words. -/
  orientation : Orientation

/-- The **adjoint of a convex process in a given orientation**: `adjointProcess` for the supremum
orientation and `coadjointProcess` for the infimum one, the two differing only in the direction of
the defining inequality. -/
noncomputable def Orientation.adjointProcess (o : Orientation)
    (A : ConvexProcess (Rn m) (Rn n)) : ConvexProcess (Rn n) (Rn m) :=
  match o with
  | Orientation.sup => ConvexProcess.adjointProcess (pairing m) (pairing n) A
  | Orientation.inf => ConvexProcess.coadjointProcess (pairing m) (pairing n) A

@[simp] theorem Orientation.adjointProcess_sup (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.sup.adjointProcess A
      = ConvexProcess.adjointProcess (pairing m) (pairing n) A := rfl

@[simp] theorem Orientation.adjointProcess_inf (A : ConvexProcess (Rn m) (Rn n)) :
    Orientation.inf.adjointProcess A
      = ConvexProcess.coadjointProcess (pairing m) (pairing n) A := rfl

namespace OrientedProcess

/-- The inverse of an oriented convex process, with the opposite orientation. -/
def inv (A : OrientedProcess m n) : OrientedProcess n m := ⟨A.process.inv, A.orientation.flip⟩

@[simp] theorem inv_process (A : OrientedProcess m n) : A.inv.process = A.process.inv := rfl

@[simp] theorem inv_orientation (A : OrientedProcess m n) :
    A.inv.orientation = A.orientation.flip := rfl

/-- The **adjoint** `A*` of an oriented convex process: an oriented convex process from `ℝⁿ` to
`ℝᵐ`, with the opposite orientation. -/
noncomputable def adjoint (A : OrientedProcess m n) : OrientedProcess n m :=
  ⟨A.orientation.adjointProcess A.process, A.orientation.flip⟩

@[simp] theorem adjoint_process (A : OrientedProcess m n) :
    A.adjoint.process = A.orientation.adjointProcess A.process := rfl

@[simp] theorem adjoint_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := rfl

/-- The sum of two convex processes with like orientation, given that same orientation. Only sums
of processes with like orientation are considered, which is why every theorem about a sum below
carries the hypothesis that the two orientations agree. -/
instance : Add (OrientedProcess m n) where
  add A₁ A₂ := ⟨A₁.process + A₂.process, A₁.orientation⟩

@[simp] theorem add_process (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).process = A₁.process + A₂.process := rfl

@[simp] theorem add_orientation (A₁ A₂ : OrientedProcess m n) :
    (A₁ + A₂).orientation = A₁.orientation := rfl

/-- The scalar multiple `λA`, with the same orientation. -/
instance : SMul ℝ (OrientedProcess m n) where
  smul a A := ⟨a • A.process, A.orientation⟩

@[simp] theorem smul_process (a : ℝ) (A : OrientedProcess m n) :
    (a • A).process = a • A.process := rfl

@[simp] theorem smul_orientation (a : ℝ) (A : OrientedProcess m n) :
    (a • A).orientation = A.orientation := rfl

/-- The product `BA` of two convex processes with like orientation, given that same
orientation. -/
def comp (B : OrientedProcess n p) (A : OrientedProcess m n) : OrientedProcess m p :=
  ⟨B.process.comp A.process, A.orientation⟩

@[simp] theorem comp_process (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).process = B.process.comp A.process := rfl

@[simp] theorem comp_orientation (B : OrientedProcess n p) (A : OrientedProcess m n) :
    (B.comp A).orientation = A.orientation := rfl

/-- The inner product `⟨Au, x*⟩` of an oriented convex process, the value `A u` being read with
`A`'s orientation. -/
noncomputable def bracket (A : OrientedProcess m n) (u : Rn m) (y : Rn n) : EReal :=
  A.orientation.bracketSet (A.process.eval u) y

/-- The supremum-oriented inner product is §33's bracket of the indicator bifunction of `A`, which
is where every clause of Theorem 39.3 about a supremum-oriented process comes from. -/
theorem bracket_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  (ConvexProcess.bracket_indicatorBifun_apply (pairing n) A u y).symm

/-- The infimum-oriented inner product is `ConvexProcess.coBracket`. -/
theorem bracket_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).bracket u y
      = ConvexProcess.coBracket (pairing n) A u y := rfl

theorem bracket_sup_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.sup).bracket u
      = ConvexAnalysis.bracket (pairing n) A.indicatorBifun u :=
  funext fun y => bracket_sup A u y

theorem bracket_inf_fn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    (OrientedProcess.mk A Orientation.inf).bracket u
      = ConvexProcess.coBracket (pairing n) A u := rfl

theorem bracket_sup_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).bracket u y)
      = fun u => ConvexAnalysis.bracket (pairing n) A.indicatorBifun u y :=
  funext fun u => bracket_sup A u y

/-- `bracket_sup` as an equation between functions on the product, the shape Theorems 39.3 and 39.4
state their closure identities in. -/
theorem bracket_sup_prod (A : ConvexProcess (Rn m) (Rn n)) :
    (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
      = fun q : Rn m × Rn n =>
          ConvexAnalysis.bracket (pairing n) A.indicatorBifun q.1 q.2 :=
  funext fun q => bracket_sup A q.1 q.2

end OrientedProcess

/-- When `A` is a linear transformation, the adjoint of `A` as a convex process — in **either**
orientation — is the adjoint linear transformation. -/
theorem adjoint_ofLinearMap (T : Rn m →ₗ[ℝ] Rn n) (o : Orientation) :
    (OrientedProcess.mk (ConvexProcess.ofLinearMap T) o).adjoint.process
      = ConvexProcess.ofLinearMap (LinearMap.adjoint T) := by
  cases o
  · exact ConvexProcess.adjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)
  · exact ConvexProcess.coadjointProcess_ofLinearMap (Bu := pairing m) (Bx := pairing n)
      (separatingRight_pairing m) (isAdjointPair_adjoint T)

/-! ### Theorem 39.2 -/

/-- **Theorem 39.2**, first assertion: `A*` has the **opposite orientation** to `A`. This holds by
construction, and it is the clause that forces the orientation to be data. -/
theorem theorem_39_2_orientation (A : OrientedProcess m n) :
    A.adjoint.orientation = A.orientation.flip := A.adjoint_orientation

/-- **Theorem 39.2**, first assertion: `A*` is a **closed** convex process from `ℝⁿ` to `ℝᵐ`, in
either orientation, being an intersection of homogeneous closed half-spaces. -/
theorem theorem_39_2_isClosed (A : OrientedProcess m n) :
    IsClosed (A.adjoint.process.graph : Set (Rn n × Rn m)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact ConvexProcess.isClosed_graph_adjointProcess (pairing m) (pairing n) A
  · exact ConvexProcess.isClosed_graph_coadjointProcess (pairing m) (pairing n) A

/-- The second adjoint of a supremum-oriented process is the bipolar of its graph. -/
private theorem graph_biadjoint_sup (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.coadjointProcess (pairing n) (pairing m)
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_coadjointProcess_adjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- The second adjoint of an infimum-oriented process is the same bipolar. -/
private theorem graph_biadjoint_inf (A : ConvexProcess (Rn m) (Rn n)) :
    ((ConvexProcess.adjointProcess (pairing n) (pairing m)
        (ConvexProcess.coadjointProcess (pairing m) (pairing n) A)).graph : Set (Rn m × Rn n))
      = closure (A.graph : Set (Rn m × Rn n)) := by
  have h := ConvexProcess.graph_adjointProcess_coadjointProcess_eq_closure (pairing m) (pairing n) A
  simp only [flip_pairing] at h
  exact h

/-- **Theorem 39.2**, second assertion: `A** = cl A`. Read through the graph this is the bipolar
theorem `K°° = cl K` of §14; the two sign flips cancel because the second adjoint is taken in the
*opposite* orientation. -/
theorem theorem_39_2 (A : OrientedProcess m n) :
    (A.adjoint.adjoint.process.graph : Set (Rn m × Rn n))
      = closure (A.process.graph : Set (Rn m × Rn n)) := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact graph_biadjoint_sup A
  · exact graph_biadjoint_inf A

/-- **Theorem 39.2**: a convex process is closed exactly when it is its own second adjoint. -/
theorem theorem_39_2_eq_self_iff (A : OrientedProcess m n) :
    A.adjoint.adjoint = A ↔ IsClosed (A.process.graph : Set (Rn m × Rn n)) := by
  rw [← closure_eq_iff_isClosed, ← theorem_39_2 A]
  constructor
  · intro h
    rw [h]
  · intro h
    refine OrientedProcess.ext ?_ (by simp)
    exact ConvexProcess.ext (SetLike.ext' h)

/-- **Theorem 39.2**, last assertion: the adjoint of the indicator bifunction of a
supremum-oriented convex process `A` is the indicator bifunction of `A*`. The indicator appears
negated because `A*` carries the opposite orientation, and an infimum-oriented set is identified
with `-δ(· | ·)`. The infimum-oriented mirror is not formalized. -/
theorem theorem_39_2_indicatorBifun (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    adjointBifun (pairing m) (pairing n) A.indicatorBifun y v
      = -((OrientedProcess.mk A Orientation.sup).adjoint.process.indicatorBifun y v) :=
  ConvexProcess.adjointBifun_indicatorBifun (pairing m) (pairing n) A y v

/-! ### Theorem 39.3 -/

/-- The second extremum problem of Theorem 39.3 for a supremum-oriented `A`:
`⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}`, the concave bracket of the adjoint bifunction. -/
private theorem bracket_adjoint_sup (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u
      = concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) u y := by
  rw [ConvexProcess.concaveBracket_adjointBifun_indicatorBifun]
  change (⨅ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iInf_congr fun v => iInf_congr fun _ => by rw [pairing_comm]

/-- The same for an infimum-oriented `A`: `⟨u, A* x*⟩ = sup {⟨u, u*⟩ | u* ∈ A* x*}`. -/
private theorem bracket_adjoint_inf (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u
      = ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) := by
  change (⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
      ((pairing m v u : ℝ) : EReal)) = _
  exact iSup_congr fun v => iSup_congr fun _ => by rw [pairing_comm]

/-- **Theorem 39.3**, first assertion: `⟨Au, x*⟩` is **positively homogeneous** in `x*` for each
`u`, in either orientation. -/
theorem theorem_39_3_posHomogeneous (A : OrientedProcess m n) (u : Rn m) :
    PosHomogeneous (A.bracket u) := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_fn]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun (pairing n) A u
  · rw [OrientedProcess.bracket_inf_fn]
    exact ConvexProcess.posHomogeneous_coBracket (pairing n) A u

/-- **Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is **convex** in
`x*`, being the support function of `A u`. -/
theorem theorem_39_3_convexFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConvexFn ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.convexFn_bracket_indicatorBifun (pairing n) A u

/-- **Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is **closed** in
`x*`. -/
theorem theorem_39_3_closedFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedFn ((OrientedProcess.mk A Orientation.sup).bracket u) := by
  rw [OrientedProcess.bracket_sup_fn]
  exact ConvexProcess.closedFn_bracket_indicatorBifun (Bx := pairing n) A u

/-- **Theorem 39.3**, "likewise when `A` is infimum oriented, except that then convexity and
concavity are reversed": `⟨Au, x*⟩` is **concave** in `x*`. -/
theorem theorem_39_3_concaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ConcaveFn ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.concaveFn_coBracket (pairing n) A u

/-- **Theorem 39.3**, infimum-oriented mirror: `⟨Au, x*⟩` is **closed concave** in `x*`. -/
theorem theorem_39_3_closedConcaveFn (A : ConvexProcess (Rn m) (Rn n)) (u : Rn m) :
    ClosedConcaveFn ((OrientedProcess.mk A Orientation.inf).bracket u) := by
  rw [OrientedProcess.bracket_inf_fn]
  exact ConvexProcess.closedConcaveFn_coBracket (Bx := pairing n) A u

/-- **Theorem 39.3**, first assertion: `⟨Au, x*⟩` is **positively homogeneous** in `u` for each
`x*`, in either orientation. This is the one clause that uses the definition of a convex process
rather than §33: it is axiom (b), `A(λu) = λ(Au)`. -/
theorem theorem_39_3_posHomogeneous_arg (A : OrientedProcess m n) (y : Rn n) :
    PosHomogeneous fun u => A.bracket u y := by
  obtain ⟨A, o⟩ := A
  cases o
  · rw [OrientedProcess.bracket_sup_arg]
    exact ConvexProcess.posHomogeneous_bracket_indicatorBifun_arg (pairing n) A y
  · exact ConvexProcess.posHomogeneous_coBracket_arg (pairing n) A y

/-- **Theorem 39.3**, first assertion: for a supremum-oriented `A`, `⟨Au, x*⟩` is **concave** in
`u` for each `x*`. -/
theorem theorem_39_3_concaveFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConcaveFn fun u => (OrientedProcess.mk A Orientation.sup).bracket u y := by
  rw [OrientedProcess.bracket_sup_arg]
  exact ConvexProcess.concaveFn_bracket_indicatorBifun (pairing n) A y

/-- **Theorem 39.3**, infimum-oriented mirror: `⟨Au, x*⟩` is **convex** in `u`. Reversing the
orientation exchanges convexity and concavity in both variables at once. -/
theorem theorem_39_3_convexFn_arg (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    ConvexFn fun u => (OrientedProcess.mk A Orientation.inf).bracket u y :=
  ConvexProcess.convexFn_coBracket_arg (pairing n) A y

/-- **Theorem 39.3**, third assertion: `⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩` for a supremum-oriented `A`,
the closure being the **concave** one because `⟨A ·, x*⟩` is concave. No closedness of `A` is
needed. -/
theorem theorem_39_3_cl (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => partialCl₁
          (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2)
          (u, y) := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u)
      = fun u => concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) u y :=
    funext fun u => bracket_adjoint_sup A u y
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁
    (Bu := pairing m) (Bx := pairing n) A y

/-- **Theorem 39.3**, third assertion, infimum-oriented mirror: the closure is now the ordinary
**convex** one, because `⟨A ·, x*⟩` is convex. -/
theorem theorem_39_3_cl_inf (A : ConvexProcess (Rn m) (Rn n)) (y : Rn n) :
    (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => clFn (fun u' => (OrientedProcess.mk A Orientation.inf).bracket u' y) u := by
  have hL : (fun u => (OrientedProcess.mk A Orientation.inf).adjoint.bracket y u)
      = fun u => ⨆ v ∈ (ConvexProcess.coadjointProcess (pairing m) (pairing n) A).eval y,
          ((pairing m u v : ℝ) : EReal) :=
    funext fun u => bracket_adjoint_inf A u y
  rw [hL]
  exact ConvexProcess.iSup_coadjointProcess_eq_clFn (Bu := pairing m) (Bx := pairing n) A y

/-- **Theorem 39.3**, fourth assertion: if `A` is closed then `⟨Au, x*⟩ = cl_{x*} ⟨u, A* x*⟩`, the
closure in the dual variable being the ordinary convex one. Closedness is genuinely needed here: it
is Theorem 33.2's *second* equation. -/
theorem theorem_39_3_cl_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) :
    partialCl₂ (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2 := by
  have hL : (fun q : Rn m × Rn n =>
        (OrientedProcess.mk A Orientation.sup).adjoint.bracket q.2 q.1)
      = fun q : Rn m × Rn n => concaveBracket (pairing m)
          (adjointBifun (pairing m) (pairing n) A.indicatorBifun) q.1 q.2 :=
    funext fun q => bracket_adjoint_sup A q.1 q.2
  rw [hL, OrientedProcess.bracket_sup_prod]
  exact ConvexProcess.partialCl₂_concaveBracket_adjointBifun_indicatorBifun
    (Bu := pairing m) (Bx := pairing n) A hA

/-- **Theorem 39.3**, last assertion: `⟨Au, x*⟩ = ⟨u, A* x*⟩` whenever `u ∈ ri (dom A)`. The book
prefixes this and its dual with "if `A` is closed"; this half is Corollary 33.2.1, whose only input
is that a concave function agrees with its closure on `ri (dom)`, so no closedness is needed. -/
theorem theorem_39_3_relint_dom (A : ConvexProcess (Rn m) (Rn n)) {u : Rn m}
    (hu : u ∈ ri A.dom) (y : Rn n) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom
    (Bu := pairing m) (Bx := pairing n) A hu y

/-- **Theorem 39.3**, last assertion, dual half: for a **closed** `A`, `⟨Au, x*⟩ = ⟨u, A* x*⟩`
whenever `x* ∈ ri (dom A*)`. -/
theorem theorem_39_3_relint_dom_adjoint (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (OrientedProcess.mk A Orientation.sup).adjoint.process.dom) :
    (OrientedProcess.mk A Orientation.sup).bracket u y
      = (OrientedProcess.mk A Orientation.sup).adjoint.bracket y u := by
  rw [OrientedProcess.bracket_sup, bracket_adjoint_sup]
  exact ConvexProcess.bracket_eq_concaveBracket_of_mem_relint_dom_adjoint
    (Bu := pairing m) (Bx := pairing n) A hA u hy

/-! ### Theorem 39.4 -/

/-- **Theorem 39.4.** The relations `K (u, x*) = ⟨Au, x*⟩` and `Au = {x | ⟨x, x*⟩ ≤ K (u, x*) ∀ x*}`
are a **one-to-one correspondence** between the lower closed concave-convex functions `K` on
`ℝᵐ × ℝⁿ` with `K (0, 0) = 0` that are positively homogeneous in each variable separately, and the
supremum-oriented **closed** convex processes from `ℝᵐ` to `ℝⁿ`. Closedness sits inside the `∃!`
because uniqueness is uniqueness among closed processes. -/
theorem theorem_39_4 {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K)
    (hK₀ : K (0, 0) = 0)
    (hhu : ∀ y : Rn n, PosHomogeneous fun u : Rn m => K (u, y))
    (hhy : ∀ u : Rn m, PosHomogeneous fun y : Rn n => K (u, y)) :
    ∃! A : ConvexProcess (Rn m) (Rn n), IsClosed (A.graph : Set (Rn m × Rn n)) ∧
      (fun q : Rn m × Rn n => (OrientedProcess.mk A Orientation.sup).bracket q.1 q.2) = K := by
  simp only [OrientedProcess.bracket_sup_prod]
  exact exists_unique_convexProcess_bracket_indicatorBifun_eq (pairing m) (pairing n)
    hK hlc hK₀ hhu hhy

/-- **Theorem 39.4**, second displayed relation: a closed convex process is recovered from its
inner product by `Au = {x | ⟨x, x*⟩ ≤ K (u, x*) for every x*}`. -/
theorem theorem_39_4_eval (A : ConvexProcess (Rn m) (Rn n))
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (u : Rn m) :
    A.eval u = {x : Rn n | ∀ y : Rn n,
      ((pairing n x y : ℝ) : EReal) ≤ (OrientedProcess.mk A Orientation.sup).bracket u y} := by
  have h := ConvexProcess.eval_eq_supportSet_bracket_indicatorBifun (Bx := pairing n) A hA u
  rw [flip_pairing] at h
  rw [h]
  ext x
  simp only [mem_supportSet, mem_ofPred_eq, OrientedProcess.bracket_sup]
  exact forall_congr' fun y => by rw [pairing_comm]

/-! ### Theorem 39.5 -/

/-- **Theorem 39.5.** For convex processes `A₁`, `A₂` from `ℝᵐ` to `ℝⁿ` with the **same
orientation**, `(A₁ + A₂)* = A₁* + A₂*`. The agreement of orientations is load-bearing and is the
reason orientation has to be data.

Where the book asks for `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`, the hypothesis here is the exactness of
the sum of the two support functions `u ↦ -⟨Aᵢ u, x*⟩`, one instance per `x*` — strictly stronger;
see the module docstring. -/
theorem theorem_39_5 (A₁ A₂ : OrientedProcess m n) (hor : A₁.orientation = A₂.orientation)
    (hex : ∀ y : Rn n, IsExactSum (pairing m)
      (fun u => -(supportFn (pairing n) (A₁.process.eval u) y))
      (fun u => -(supportFn (pairing n) (A₂.process.eval u) y))) :
    (A₁ + A₂).adjoint = A₁.adjoint + A₂.adjoint := by
  obtain ⟨A₁, o₁⟩ := A₁
  obtain ⟨A₂, o₂⟩ := A₂
  have hor' : o₁ = o₂ := hor
  subst hor'
  cases o₁
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_add (pairing m) (pairing n) A₁ A₂ hex) rfl

/-- **Theorem 39.5**, second statement, first half: for closed `A₁` and `A₂`, `A₁ + A₂` is closed.
Where the book asks that `ri (dom A₁*)` and `ri (dom A₂*)` meet, the hypothesis here is again an
`IsExactSum`. The proof does not use Corollary 38.2.1: `A₁ + A₂` *is* the infimum-oriented adjoint
of `A₁* + A₂*`. -/
theorem theorem_39_5_isClosed {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    IsClosed (((A₁ + A₂).graph : Set (Rn m × Rn n))) := by
  refine ConvexProcess.isClosed_graph_add (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-- **Theorem 39.5**, second statement, second half: `(A₁ + A₂)*` is the **closure** of
`A₁* + A₂*`. -/
theorem theorem_39_5_closure {A₁ A₂ : ConvexProcess (Rn m) (Rn n)}
    (hA₁ : IsClosed (A₁.graph : Set (Rn m × Rn n)))
    (hA₂ : IsClosed (A₂.graph : Set (Rn m × Rn n)))
    (hex : ∀ u : Rn m, IsExactSum (pairing n)
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁).eval y) u))
      (fun y => -(supportFn (pairing m)
        ((ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).eval y) u))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing n) (A₁ + A₂)).graph : Set (Rn n × Rn m))
      = closure (((ConvexProcess.adjointProcess (pairing m) (pairing n) A₁
          + ConvexProcess.adjointProcess (pairing m) (pairing n) A₂).graph
            : Set (Rn n × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_add_eq_closure (pairing m) (pairing n) hA₁ hA₂ ?_
  simpa only [flip_pairing] using hex

/-! ### Theorem 39.6 -/

/-- **Theorem 39.6.** For any oriented convex process `A` and any `λ > 0`, `(λA)* = λ(A*)`. -/
theorem theorem_39_6 (A : OrientedProcess m n) {a : ℝ} (ha : 0 < a) :
    (a • A).adjoint = a • A.adjoint := by
  obtain ⟨A, o⟩ := A
  cases o
  · exact OrientedProcess.ext (ConvexProcess.adjointProcess_smul (pairing m) (pairing n) ha A) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_smul (pairing m) (pairing n) ha A) rfl

/-! ### Theorem 39.7 -/

/-- **Theorem 39.7**, first assertion: for a supremum-oriented convex process `A` and a proper
convex `f` on `ℝᵐ`, `(Af)* = A*⁻¹ f*`. Where the book asks for `ri (dom f) ∩ ri (dom A) ≠ ∅`, the
hypothesis here is the exactness of `f + (-⟨A ·, x*⟩)`; see the module docstring. -/
theorem theorem_39_7 (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal} (hf : Proper f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    conj (pairing n) (imageFn A f) y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f) y := by
  refine ConvexProcess.conj_imageBifun_indicatorBifun (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Theorem 39.7**, second assertion: the infimum defining `(A*⁻¹ f*)(x*)` is attained. -/
theorem theorem_39_7_attained (A : ConvexProcess (Rn m) (Rn n)) {f : Rn m → EReal} (hf : Proper f)
    {y : Rn n}
    (hex : IsExactSum (pairing m) f
      (fun u => -((OrientedProcess.mk A Orientation.sup).bracket u y))) :
    ∃ v : Rn m, conj (pairing m) f v
        + (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv.indicatorBifun v y
      = imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f) y := by
  refine ConvexProcess.exists_imageBifun_indicatorBifun_adjointProcess_eq
    (pairing m) (pairing n) A hf ?_
  simpa only [OrientedProcess.bracket_sup] using hex

/-- **Theorem 39.7**, third assertion: for closed `A` and `f`, `Af` is closed. Where the book asks
that `ri (dom f*)` meet `ri (dom A*⁻¹)`, the hypothesis here is again an `IsExactSum`. -/
theorem theorem_39_7_closedFn {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    ClosedFn (imageFn A f) := by
  refine ConvexProcess.closedFn_imageBifun_indicatorBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Theorem 39.7**, fourth assertion, in the book's own form: wherever `Af` is finite there is a
`u` with `x ∈ Au` and `f u = (Af)(x)`. -/
theorem theorem_39_7_attained_image {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f) {x : Rn n}
    (hex : IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x)))
    (hne : imageFn A f x ≠ ⊤) :
    ∃ u : Rn m, x ∈ A.eval u ∧ f u = imageFn A f x := by
  refine ConvexProcess.exists_mem_eval_and_eq_imageBifun (Bu := pairing m) (Bx := pairing n)
    hA hf ?_ hne
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-- **Theorem 39.7**, last assertion: `(Af)*` is the **closure** of `A*⁻¹ f*`. -/
theorem theorem_39_7_closure {A : ConvexProcess (Rn m) (Rn n)} {f : Rn m → EReal}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hf : ClosedProperConvexFn f)
    (hex : ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
      (fun v => -((OrientedProcess.mk
        (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          Orientation.sup).bracket v x))) :
    conj (pairing n) (imageFn A f)
      = clFn (imageFn (ConvexProcess.adjointProcess (pairing m) (pairing n) A).inv
          (conj (pairing m) f)) := by
  refine ConvexProcess.conj_imageBifun_indicatorBifun_eq_clFn (Bu := pairing m) (Bx := pairing n)
    hA hf ?_
  simpa only [OrientedProcess.bracket_sup, flip_pairing] using hex

/-! ### Corollary 39.7.1 -/

/-- **Corollary 39.7.1.** For a closed convex process `A` and a nonempty closed convex `C ⊆ ℝᵐ`, if
no nonzero vector of `A⁻¹0` lies in the recession cone of `C`, then `AC` is closed.

Proved as Theorem 9.1 for the projection `(u, x) ↦ x` rather than by specialising Theorem 39.7:
`AC` is the image of `graph A ∩ (C × ℝⁿ)`, whose recession cone is `graph A ∩ (0⁺C × ℝⁿ)`. -/
theorem corollary_39_7_1 {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty)
    (h : ∀ v ∈ A.inv.eval 0, v ≠ 0 → v ∉ recessionCone C) :
    IsClosed (A.image C) := by
  refine ConvexProcess.isClosed_image hA hC hCcl hCne fun v hv hrec => ?_
  by_contra hv0
  exact h v hv hv0 hrec

/-- **Corollary 39.7.1**, the parenthesis "which is true in particular if `C` is bounded": the
image of a nonempty compact convex set under a closed convex process is closed. -/
theorem corollary_39_7_1_isBounded {A : ConvexProcess (Rn m) (Rn n)} {C : Set (Rn m)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hC : Convex ℝ C) (hCcl : IsClosed C)
    (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) :=
  ConvexProcess.isClosed_image_of_isBounded hA hC hCcl hCne hb

/-! ### Theorem 39.8 -/

/-- **Theorem 39.8.** For a convex process `A` from `ℝᵐ` to `ℝⁿ` and `B` from `ℝⁿ` to `ℝᵖ` with the
**same orientation**, `(BA)* = A* B*`. As in Theorem 39.5, the agreement of orientations is a
hypothesis only a formal orientation *pair* can express.

Where the book asks for `ri (range A) ∩ ri (dom B) ≠ ∅`, the hypothesis here is the exactness of
the corresponding sum, one instance per `(z*, u*)`. The proof does not go through Theorem 38.5: it
is a linear sandwich produced by Fenchel's duality theorem. -/
theorem theorem_39_8 (A : OrientedProcess m n) (B : OrientedProcess n p)
    (hor : B.orientation = A.orientation)
    (hex : ∀ (w : Rn p) (v : Rn m), IsExactSum (pairing n)
      (fun x => ⨅ u ∈ A.process.inv.eval x, ((pairing m u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.process.eval x, ((pairing p z w : ℝ) : EReal)))) :
    (B.comp A).adjoint = A.adjoint.comp B.adjoint := by
  obtain ⟨A, oA⟩ := A
  obtain ⟨B, oB⟩ := B
  have hor' : oB = oA := hor
  subst hor'
  cases oB
  · exact OrientedProcess.ext
      (ConvexProcess.adjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl
  · exact OrientedProcess.ext
      (ConvexProcess.coadjointProcess_comp (pairing m) (pairing n) (pairing p) A B hex) rfl

/-- **Theorem 39.8**, second statement, first half: for closed `A` and `B`, `BA` is closed. Where
the book asks that `ri (range B*)` meet `ri (dom A*)`, the hypothesis here is again an
`IsExactSum`. -/
theorem theorem_39_8_isClosed {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    IsClosed (((B.comp A).graph : Set (Rn m × Rn p))) := by
  refine ConvexProcess.isClosed_graph_comp (pairing m) (pairing n) (pairing p) hA hB ?_
  simpa only [flip_pairing] using hex

/-- **Theorem 39.8**, second statement, second half: `(BA)*` is the **closure** of `A* B*`. -/
theorem theorem_39_8_closure {A : ConvexProcess (Rn m) (Rn n)} {B : ConvexProcess (Rn n) (Rn p)}
    (hA : IsClosed (A.graph : Set (Rn m × Rn n))) (hB : IsClosed (B.graph : Set (Rn n × Rn p)))
    (hex : ∀ (u : Rn m) (z : Rn p), IsExactSum (pairing n)
      (fun y => ⨅ w ∈ (ConvexProcess.adjointProcess (pairing n) (pairing p) B).inv.eval y,
        ((pairing p z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (ConvexProcess.adjointProcess (pairing m) (pairing n) A).eval y,
        ((pairing m u v : ℝ) : EReal)))) :
    ((ConvexProcess.adjointProcess (pairing m) (pairing p) (B.comp A)).graph
        : Set (Rn p × Rn m))
      = closure ((((ConvexProcess.adjointProcess (pairing m) (pairing n) A).comp
          (ConvexProcess.adjointProcess (pairing n) (pairing p) B)).graph
            : Set (Rn p × Rn m))) := by
  refine ConvexProcess.graph_adjointProcess_comp_eq_closure (pairing m) (pairing n) (pairing p)
    hA hB ?_
  simpa only [flip_pairing] using hex

end Rockafellar
