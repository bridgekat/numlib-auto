import Numlib.Analysis.Convex.Bifunction.Algebra
import Numlib.Analysis.Convex.Recession.Closedness

/-!
# Convex processes

A **convex process** from `U` to `X` is a multivalued map `A : u ↦ A u` with
`A (u₁ + u₂) ⊇ A u₁ + A u₂`, `A (λ u) = λ (A u)` for `λ > 0`, and `0 ∈ A 0`. These conditions say
exactly that the graph `{(u, x) | x ∈ A u}` is a convex cone containing the origin, so that is what
`ConvexProcess` *is*: a bundled `PointedCone ℝ (U × X)`, with `A.eval u` the `u`-slice of the cone
and every elementary property a `Submodule` fact in disguise. Processes sit between linear
transformations and convex bifunctions — `ofLinearMap` embeds the former, `indicatorBifun` embeds a
process into the latter — and carry the adjoint, sum, product and inverse of that algebra.

The adjoint `A*` is the polar of the graph with a sign flip on one factor: `(y, v) ∈ graph A*` iff
`(-v, y) ∈ (graph A)°` (`mem_graph_adjointProcess_iff_mem_polarCone`), the sign convention
`adjointBifun` uses, so everything topological about `A*` comes from the theory of polar cones.

Rockafellar carries "supremum oriented" and "infimum oriented" as extra data on a convex set and
defines the adjoint of an infimum-oriented process by reversing the inequality. Here the two are two
definitions, `adjointProcess` and `coadjointProcess`, and `A**` uses one of each: with
`adjointProcess` twice the sign flips *add* instead of cancelling, giving
`{p | ∀ w ∈ K°, 0 ≤ ⟨p, w⟩}` in place of the bipolar `K°°`. Reflection through the origin
(`reflect`) exchanges the two adjoints and commutes with sums and products, so every
infimum-oriented statement below — they carry a `co` in their names — is the supremum-oriented one
read back through it. The inner products are the exception: reflection flips the *dual* variable
only, and `coBracket_eq_neg_bracket` records the sign.

## Main definitions

* `ConvexProcess U X` — a convex process, carried by its graph. `eval`, `dom`, `range`, `image`,
  `inv` are `A u`, `dom A`, `range A`, `A C`, `A⁻¹`; `comp` with the `Add` and `SMul` instances are
  `B A`, `A₁ + A₂` and `λ A`. `ofLinearMap` embeds a linear transformation, and `indicatorBifun` is
  the bifunction `(F u)(x) = δ(x | A u)`.
* `ConvexProcess.adjointProcess`, `coadjointProcess`, `reflect` — the two adjoints and the
  reflection exchanging them; `coBracket` is the inner product `⟨Au, x*⟩ = inf {⟨x, x*⟩ | x ∈ A u}`
  of an infimum-oriented process.

## Main results

* `exists_linearMap_of_isBounded` — a convex process with full domain and bounded `A 0` is a
  linear transformation (Theorem 39.1 in [^1]).
* `isClosed_graph_adjointProcess`, `coadjointProcess_adjointProcess_eq_self_iff` — `A*` is always
  closed, `A** = cl A`, and `A** = A` exactly for closed `A`.
* `bracket_indicatorBifun` and the results beside it — `⟨Au, x*⟩` is the support function of `A u`,
  hence closed convex in `x*` and concave in `u`, and `⟨u, A* x*⟩` is its convex closure in `u`
  (Theorem 39.3 in [^1]).
* `adjointProcess_add`, `adjointProcess_comp`, `adjointProcess_smul` — `(A₁ + A₂)* = A₁* + A₂*`,
  `(BA)* = A* B*` and `(λ A)* = λ (A*)` for `λ > 0`; `isClosed_graph_add`,
  `graph_adjointProcess_add_eq_closure` and the `comp` analogues are the closed halves.
* `conj_imageBifun_indicatorBifun` — `(Af)* = A*⁻¹ f*`, the infimum attained (Theorem 39.7 in [^1]).
* `isClosed_image` — `A C` is closed for closed `A`, nonempty closed convex `C`, and no non-zero
  vector of `A⁻¹ 0` receding `C`.
* `exists_pairing_sandwich` — Fenchel duality at a positively homogeneous pair: a concave `p` below
  a convex `q`, both straddling `0` at the origin, admit a linear `⟨·, y⟩` between them.

## Implementation notes

The adjoints of a sum and of a product take an `IsExactSum` hypothesis, one instance per dual
vector, where Rockafellar assumes `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`. `IsExactSum` also requires both
summands proper, so the hypothesis carried here is stronger than the book's.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §39.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### The definition -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- A **convex process** from `U` to `X`: a multivalued map `A : u ↦ Au` with

* `A (u₁ + u₂) ⊇ A u₁ + A u₂`,
* `A (λ u) = λ (A u)` for `λ > 0`,
* `0 ∈ A 0`,

which Rockafellar shows is the same thing as a convex cone in `U × X` containing the origin — that
is, a `PointedCone ℝ (U × X)`, read as a relation. -/
structure ConvexProcess (U X : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup X]
    [Module ℝ X] where
  /-- The graph of the process. -/
  graph : PointedCone ℝ (U × X)

namespace ConvexProcess

variable {A : ConvexProcess U X} {u u₁ u₂ : U} {x x₁ x₂ : X}

/-- The value `A u` of the process at `u`: the `u`-slice of its graph. -/
def eval (A : ConvexProcess U X) (u : U) : Set X := {x | (u, x) ∈ A.graph}

@[simp] theorem mem_eval : x ∈ A.eval u ↔ (u, x) ∈ A.graph := Iff.rfl

/-- The graph of a convex process, as a relation. -/
def toSetRel (A : ConvexProcess U X) : SetRel U X := (A.graph : Set (U × X))

@[simp] theorem mem_toSetRel {p : U × X} : p ∈ A.toSetRel ↔ p ∈ A.graph := Iff.rfl

/-- The **effective domain** of a convex process: the `u` at which `A u` is nonempty. -/
def dom (A : ConvexProcess U X) : Set U := {u | (A.eval u).Nonempty}

@[simp] theorem mem_dom : u ∈ A.dom ↔ (A.eval u).Nonempty := Iff.rfl

/-- The **range** of a convex process. -/
def range (A : ConvexProcess U X) : Set X := {x | ∃ u, (u, x) ∈ A.graph}

@[simp] theorem mem_range : x ∈ A.range ↔ ∃ u, (u, x) ∈ A.graph := Iff.rfl

/-- The **image** of a set under a convex process: `A C = ⋃ {A u | u ∈ C}`. -/
def image (A : ConvexProcess U X) (C : Set U) : Set X := {x | ∃ u ∈ C, (u, x) ∈ A.graph}

@[simp] theorem mem_image {C : Set U} : x ∈ A.image C ↔ ∃ u ∈ C, (u, x) ∈ A.graph := Iff.rfl

theorem image_univ (A : ConvexProcess U X) : A.image univ = A.range := by
  ext x; simp

/-- Two convex processes with the same graph are equal. -/
@[ext] theorem ext {A B : ConvexProcess U X} (h : A.graph = B.graph) : A = B := by
  cases A
  cases B
  simp only [ConvexProcess.mk.injEq]
  exact h

/-- A linear transformation, read as a convex process. Its graph is the graph of `T`, a linear
subspace and hence in particular a pointed convex cone. -/
def ofLinearMap (T : U →ₗ[ℝ] X) : ConvexProcess U X where
  graph :=
    { carrier := {p : U × X | p.2 = T p.1}
      zero_mem' := by simp
      add_mem' := by
        rintro ⟨u₁, x₁⟩ ⟨u₂, x₂⟩ h₁ h₂
        simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
        rw [Prod.mk_add_mk, map_add, h₁, h₂]
      smul_mem' := by
        rintro c ⟨u, x⟩ h
        simp only [Set.mem_ofPred_eq] at h ⊢
        change (c : ℝ) • x = T ((c : ℝ) • u)
        rw [map_smul, h] }

@[simp] theorem mem_graph_ofLinearMap {T : U →ₗ[ℝ] X} {p : U × X} :
    p ∈ (ofLinearMap T).graph ↔ p.2 = T p.1 := Iff.rfl

@[simp] theorem eval_ofLinearMap (T : U →ₗ[ℝ] X) (u : U) : (ofLinearMap T).eval u = {T u} := by
  ext x
  simp [eval]

@[simp] theorem dom_ofLinearMap (T : U →ₗ[ℝ] X) : (ofLinearMap T).dom = univ := by
  ext u
  simp

/-- The **inverse** of a convex process, again a convex process. -/
def inv (A : ConvexProcess U X) : ConvexProcess X U where
  graph :=
    { carrier := {p : X × U | (p.2, p.1) ∈ A.graph}
      zero_mem' := A.graph.zero_mem
      add_mem' := fun h₁ h₂ => A.graph.add_mem h₁ h₂
      smul_mem' := fun c _ h => Submodule.smul_mem A.graph c h }

@[simp] theorem mem_graph_inv {p : X × U} : p ∈ A.inv.graph ↔ (p.2, p.1) ∈ A.graph := Iff.rfl

@[simp] theorem mem_eval_inv : u ∈ A.inv.eval x ↔ (u, x) ∈ A.graph := Iff.rfl

theorem inv_inv (A : ConvexProcess U X) : A.inv.inv = A := by
  ext p
  rfl

theorem dom_inv (A : ConvexProcess U X) : A.inv.dom = A.range := by
  ext x
  simp only [mem_dom, mem_range, Set.Nonempty, mem_eval_inv]

theorem range_inv (A : ConvexProcess U X) : A.inv.range = A.dom := by
  ext u
  simp only [mem_range, mem_dom, Set.Nonempty, mem_eval, mem_graph_inv]

/-! ### Elementary structure -/

theorem convex_graph (A : ConvexProcess U X) : Convex ℝ (A.graph : Set (U × X)) :=
  ((A.graph : ConvexCone ℝ (U × X))).convex

/-- Membership of a nonnegative multiple, in the form the `PointedCone` coercion hides. -/
theorem smul_mem_graph {a : ℝ} (ha : 0 ≤ a) {p : U × X} (hp : p ∈ A.graph) : a • p ∈ A.graph := by
  have h := Submodule.smul_mem A.graph (⟨a, ha⟩ : {c : ℝ // 0 ≤ c}) hp
  exact h

theorem add_mem_graph {p q : U × X} (hp : p ∈ A.graph) (hq : q ∈ A.graph) : p + q ∈ A.graph :=
  A.graph.add_mem hp hq

theorem zero_mem_graph (A : ConvexProcess U X) : ((0 : U), (0 : X)) ∈ A.graph :=
  A.graph.zero_mem

@[simp] theorem zero_mem_eval_zero (A : ConvexProcess U X) : (0 : X) ∈ A.eval 0 :=
  A.zero_mem_graph

/-- Each value `A u` of a convex process is a convex set. -/
theorem convex_eval (A : ConvexProcess U X) (u : U) : Convex ℝ (A.eval u) := by
  intro x₁ h₁ x₂ h₂ a b ha hb hab
  have h : a • ((u, x₁) : U × X) + b • (u, x₂) ∈ A.graph :=
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)
  have hfst : (a • ((u, x₁) : U × X) + b • (u, x₂)) = (u, a • x₁ + b • x₂) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
  rwa [hfst] at h

/-- `A 0` is a cone: it is stable under multiplication by a nonnegative scalar. -/
theorem smul_mem_eval_zero (A : ConvexProcess U X) {a : ℝ} (ha : 0 ≤ a) (hx : x ∈ A.eval 0) :
    a • x ∈ A.eval 0 := by
  have h := smul_mem_graph ha hx
  rwa [Prod.smul_mk, smul_zero] at h

/-- `A u + A 0 ⊆ A u`, so `A 0` is a set of directions along which every value of the process is
invariant. -/
theorem add_eval_zero_subset (A : ConvexProcess U X) (u : U) :
    A.eval u + A.eval 0 ⊆ A.eval u := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have h : ((u, x) : U × X) + (0, y) ∈ A.graph := add_mem_graph hx hy
  rwa [Prod.mk_add_mk, add_zero] at h

/-- The effective domain of a convex process is convex. -/
theorem convex_dom (A : ConvexProcess U X) : Convex ℝ A.dom := by
  rintro u₁ ⟨x₁, h₁⟩ u₂ ⟨x₂, h₂⟩ a b ha hb hab
  exact ⟨a • x₁ + b • x₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

theorem convex_range (A : ConvexProcess U X) : Convex ℝ A.range := by
  rintro x₁ ⟨u₁, h₁⟩ x₂ ⟨u₂, h₂⟩ a b ha hb hab
  exact ⟨a • u₁ + b • u₂,
    by simpa [Prod.smul_mk, Prod.mk_add_mk] using
      add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)⟩

/-- The image of a convex set under a convex process is convex. -/
theorem convex_image (A : ConvexProcess U X) {C : Set U} (hC : Convex ℝ C) :
    Convex ℝ (A.image C) := by
  rintro x₁ ⟨u₁, hu₁, h₁⟩ x₂ ⟨u₂, hu₂, h₂⟩ a b ha hb hab
  refine ⟨a • u₁ + b • u₂, hC hu₁ hu₂ ha hb hab, ?_⟩
  simpa [Prod.smul_mk, Prod.mk_add_mk] using
    add_mem_graph (smul_mem_graph ha h₁) (smul_mem_graph hb h₂)

/-- The image `A C` is the projection of `graph A ∩ (C × X)` on the second factor. This is what
turns closedness of `A C` into a statement about the image of a convex set under a linear map. -/
theorem image_eq_image_snd (A : ConvexProcess U X) (C : Set U) :
    A.image C = (LinearMap.snd ℝ U X) '' ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) := by
  ext x
  constructor
  · rintro ⟨u, hu, hp⟩
    exact ⟨(u, x), ⟨hp, hu, mem_univ x⟩, rfl⟩
  · rintro ⟨⟨u, z⟩, ⟨hp, hu, -⟩, rfl⟩
    exact ⟨u, hu, hp⟩

end ConvexProcess

end Defs

/-! ### The indicator bifunction -/

section IndicatorInjective

variable {W : Type*}

/-- The indicator function determines its set.

Proof idea: `δ(· | S)` takes the value `0` exactly on `S` and `⊤` off it, and `0 ≠ ⊤` in
`EReal`. -/
theorem indicatorFn_injective : Function.Injective (indicatorFn : Set W → W → EReal) := by
  intro S T h
  ext w
  constructor
  · intro hw
    by_contra hc
    have h0 : indicatorFn S w = 0 := indicatorFn_of_mem hw
    rw [h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)
  · intro hw
    by_contra hc
    have h0 : indicatorFn T w = 0 := indicatorFn_of_mem hw
    rw [← h, indicatorFn_of_notMem hc] at h0
    exact absurd h0 (by simp)

end IndicatorInjective

section Indicator

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

namespace ConvexProcess

/-- The **indicator bifunction** of a supremum-oriented convex process: `(F u)(x) = δ(x | A u)`.
This is the dictionary entry making every result about processes one about bifunctions. -/
noncomputable def indicatorBifun (A : ConvexProcess U X) : Bifun U X :=
  fun u => indicatorFn (A.eval u)

theorem indicatorBifun_apply (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x = indicatorFn (A.eval u) x := rfl

/-- The graph function of the indicator bifunction of `A` is the indicator function of the graph
of `A`. -/
@[simp] theorem graphFn_indicatorBifun (A : ConvexProcess U X) :
    graphFn A.indicatorBifun = indicatorFn (A.graph : Set (U × X)) := by
  funext p
  obtain ⟨u, x⟩ := p
  rw [graphFn_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show x ∈ A.eval u from h), indicatorFn_of_mem h]
  · rw [indicatorFn_of_notMem (show x ∉ A.eval u from h), indicatorFn_of_notMem h]

theorem indicatorBifun_ne_bot (A : ConvexProcess U X) (u : U) (x : X) :
    A.indicatorBifun u x ≠ ⊥ := indicatorFn_ne_bot _ _

/-- **A convex process is determined by its indicator bifunction.** A process *is* its graph, and
the indicator function of a set determines the set, so this is `indicatorFn_injective` read through
`graphFn_indicatorBifun`. It is what makes the correspondence with bifunctions one-to-one. -/
theorem indicatorBifun_injective :
    Function.Injective (indicatorBifun : ConvexProcess U X → Bifun U X) := by
  intro A₁ A₂ h
  refine ConvexProcess.ext (SetLike.ext' (indicatorFn_injective ?_))
  rw [← graphFn_indicatorBifun, ← graphFn_indicatorBifun, h]

/-- The indicator bifunction of a convex process is a convex bifunction. -/
theorem convexBifun_indicatorBifun (A : ConvexProcess U X) : ConvexBifun A.indicatorBifun := by
  rw [convexBifun_iff, graphFn_indicatorBifun]
  exact convexFn_indicatorFn.2 A.convex_graph

/-- The effective domain of the indicator bifunction is the effective domain of the process. -/
@[simp] theorem domBifun_indicatorBifun (A : ConvexProcess U X) :
    domBifun A.indicatorBifun = A.dom := by
  ext u
  simp only [mem_domBifun, mem_dom, Set.Nonempty, indicatorBifun_apply]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    by_contra h
    exact hx (indicatorFn_of_notMem h)
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [indicatorFn_of_mem hx]; simp⟩

/-- Positive multiples do not move the graph of a convex process: it is a cone. -/
theorem smul_graph (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) :
    a • (A.graph : Set (U × X)) = (A.graph : Set (U × X)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem_graph ha.le hq
  · intro hp
    refine ⟨a⁻¹ • p, smul_mem_graph (inv_nonneg.2 ha.le) hp, ?_⟩
    change a • a⁻¹ • p = p
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- **`A (λ u) = λ (A u)` for `λ > 0`**, the positive-homogeneity axiom of a convex process.

Both inclusions are one application of `smul_mem_graph`, to `a` and to `a⁻¹`: a cone is stable
under *both* directions of a positive scaling, which is what turns the inclusion Rockafellar's
axiom would give into an equality. -/
theorem eval_smul_arg (A : ConvexProcess U X) {a : ℝ} (ha : 0 < a) (u : U) :
    A.eval (a • u) = a • A.eval u := by
  ext x
  constructor
  · intro hx
    have hmem : ((u, a⁻¹ • x) : U × X) ∈ A.graph := by
      have h := smul_mem_graph (A := A) (inv_nonneg.2 ha.le) hx
      rwa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
    have hval : a • a⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    exact ⟨a⁻¹ • x, hmem, hval⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : a • z = x := hzx
    have h := smul_mem_graph (A := A) ha.le (show ((u, z) : U × X) ∈ A.graph from hz)
    rw [Prod.smul_mk, hzx'] at h
    exact h

end ConvexProcess

end Indicator

/-! ### The algebra of convex processes, and its bifunction dictionary -/

section Algebra

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

omit [Module ℝ X] in
/-- The infimal convolute of two indicator functions is the indicator function of the sum of the
sets. `Operations/InfConv.lean` has only the special case of a singleton, so it is proved here. -/
theorem infConv_indicatorFn (S T : Set X) :
    infConv (indicatorFn S) (indicatorFn T) = indicatorFn (S + T) := by
  have hepi : epi (indicatorFn S) + epi (indicatorFn T) = epi (indicatorFn (S + T)) := by
    rw [epi_indicatorFn, epi_indicatorFn, epi_indicatorFn]
    ext p
    constructor
    · rintro ⟨q, ⟨hq, hq0⟩, r, ⟨hr, hr0⟩, rfl⟩
      exact ⟨⟨q.1, hq, r.1, hr, rfl⟩,
        Set.mem_Ici.2 (add_nonneg (Set.mem_Ici.1 hq0) (Set.mem_Ici.1 hr0))⟩
    · rintro ⟨hw, hc⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hw
      refine ⟨(a, p.2), ⟨ha, hc⟩, (b, 0), ⟨hb, Set.mem_Ici.2 (le_refl 0)⟩, ?_⟩
      have hab2 : a + b = p.1 := hab
      change ((a, p.2) : X × ℝ) + (b, 0) = p
      rw [Prod.mk_add_mk, hab2, add_zero]
  rw [infConv_def, hepi, ofEpi_epi]

namespace ConvexProcess

/-- The **sum** of two convex processes, `(A₁ + A₂) u = A₁ u + A₂ u`. -/
instance : Add (ConvexProcess U X) where
  add A₁ A₂ :=
    { graph :=
        { carrier := {p : U × X | ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y}
          zero_mem' := ⟨0, A₁.zero_mem_eval_zero, 0, A₂.zero_mem_eval_zero, (add_zero 0).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, y₁, k₁, rfl⟩ ⟨x₂, h₂, y₂, k₂, rfl⟩
            exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, y₁ + y₂, add_mem_graph k₁ k₂,
              add_add_add_comm x₁ y₁ x₂ y₂⟩
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, hx, y, hy, rfl⟩
            exact ⟨(c : ℝ) • x, smul_mem_graph c.2 hx, (c : ℝ) • y, smul_mem_graph c.2 hy,
              smul_add (c : ℝ) x y⟩ } }

@[simp] theorem mem_graph_add {A₁ A₂ : ConvexProcess U X} {p : U × X} :
    p ∈ (A₁ + A₂).graph ↔ ∃ x ∈ A₁.eval p.1, ∃ y ∈ A₂.eval p.1, p.2 = x + y := Iff.rfl

@[simp] theorem eval_add (A₁ A₂ : ConvexProcess U X) (u : U) :
    (A₁ + A₂).eval u = A₁.eval u + A₂.eval u := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- **The effective domain of a sum is the intersection**: `dom (A₁ + A₂) = dom A₁ ∩ dom A₂`. -/
@[simp] theorem dom_add (A₁ A₂ : ConvexProcess U X) : (A₁ + A₂).dom = A₁.dom ∩ A₂.dom := by
  ext u
  constructor
  · rintro ⟨_, x, hx, y, hy, -⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨x + y, x, hx, y, hy, rfl⟩

/-- The **scalar multiple** `λ A`, defined by `(λ A) u = λ (A u)`.

The graph `{(u, λ x) | (u, x) ∈ graph A}` is a pointed convex cone for *every* real `λ`, so the
definition needs no positivity; `λ > 0` is needed only from `adjointProcess_smul` on, where the
inverse scaling is used. The action is a `MulAction` — `1 • A = A` and `(ab) • A = a • (b • A)`
both hold — but it is not additive: `2 • A` and `A + A` differ. -/
instance : SMul ℝ (ConvexProcess U X) where
  smul a A :=
    { graph :=
        { carrier := {p : U × X | ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x}
          zero_mem' := ⟨0, A.zero_mem_graph, (smul_zero a).symm⟩
          add_mem' := by
            rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, hz₁⟩ ⟨x₂, h₂, hz₂⟩
            refine ⟨x₁ + x₂, add_mem_graph h₁ h₂, ?_⟩
            have hz₁' : z₁ = a • x₁ := hz₁
            have hz₂' : z₂ = a • x₂ := hz₂
            change z₁ + z₂ = a • (x₁ + x₂)
            rw [smul_add, hz₁', hz₂']
          smul_mem' := by
            rintro c ⟨u, z⟩ ⟨x, h, hz⟩
            refine ⟨(c : ℝ) • x, smul_mem_graph c.2 h, ?_⟩
            have hz' : z = a • x := hz
            change (c : ℝ) • z = a • (c : ℝ) • x
            rw [hz', smul_comm] } }

@[simp] theorem mem_graph_smul {a : ℝ} {A : ConvexProcess U X} {p : U × X} :
    p ∈ (a • A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ p.2 = a • x := Iff.rfl

/-- **`(λ A) u = λ (A u)`**, the defining equation of the scalar multiple. -/
@[simp] theorem eval_smul (a : ℝ) (A : ConvexProcess U X) (u : U) :
    (a • A).eval u = a • A.eval u := by
  ext x
  constructor
  · rintro ⟨z, hz, hx⟩
    have hx' : x = a • z := hx
    exact ⟨z, hz, hx'.symm⟩
  · rintro ⟨z, hz, hx⟩
    have hx' : a • z = x := hx
    exact ⟨z, hz, hx'.symm⟩

/-- The **product** of convex processes, `(B A) u = B (A u)`. -/
def comp (B : ConvexProcess X Z) (A : ConvexProcess U X) : ConvexProcess U Z where
  graph :=
    { carrier := {p : U × Z | ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph}
      zero_mem' := ⟨0, A.zero_mem_graph, B.zero_mem_graph⟩
      add_mem' := by
        rintro ⟨u₁, z₁⟩ ⟨u₂, z₂⟩ ⟨x₁, h₁, k₁⟩ ⟨x₂, h₂, k₂⟩
        exact ⟨x₁ + x₂, add_mem_graph h₁ h₂, add_mem_graph k₁ k₂⟩
      smul_mem' := by
        rintro c ⟨u, z⟩ ⟨x, h, k⟩
        exact ⟨(c : ℝ) • x, smul_mem_graph c.2 h, smul_mem_graph c.2 k⟩ }

@[simp] theorem mem_graph_comp {B : ConvexProcess X Z} {A : ConvexProcess U X} {p : U × Z} :
    p ∈ (B.comp A).graph ↔ ∃ x, (p.1, x) ∈ A.graph ∧ (x, p.2) ∈ B.graph := Iff.rfl

@[simp] theorem eval_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) (u : U) :
    (B.comp A).eval u = B.image (A.eval u) := by
  ext z
  exact Iff.rfl

/-- **The inverse of a product is the product of the inverses**: `(B A)⁻¹ = A⁻¹ B⁻¹`. -/
theorem inv_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).inv = A.inv.comp B.inv := by
  ext p
  constructor <;> rintro ⟨x, h, k⟩ <;> exact ⟨x, k, h⟩

/-- The indicator bifunction of `A₁ + A₂` is the infimal convolute `F₁ □ F₂`. -/
theorem indicatorBifun_add (A₁ A₂ : ConvexProcess U X) :
    (A₁ + A₂).indicatorBifun = infConvBifun A₁.indicatorBifun A₂.indicatorBifun := by
  funext u
  change indicatorFn ((A₁ + A₂).eval u)
    = infConv (indicatorFn (A₁.eval u)) (indicatorFn (A₂.eval u))
  rw [eval_add, infConv_indicatorFn]

/-- The indicator bifunction of `B A` is the product `G F` of the indicator bifunctions. -/
theorem indicatorBifun_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).indicatorBifun = compBifun B.indicatorBifun A.indicatorBifun := by
  funext u z
  rw [compBifun_apply]
  by_cases h : z ∈ (B.comp A).eval u
  · rw [indicatorBifun_apply, indicatorFn_of_mem h]
    obtain ⟨x₀, hx₀, hz₀⟩ := h
    symm
    refine le_antisymm ?_ (le_iInf fun x => ?_)
    · refine le_of_le_of_eq (iInf_le _ x₀) ?_
      rw [indicatorBifun_apply, indicatorFn_of_mem (show x₀ ∈ A.eval u from hx₀),
        indicatorBifun_apply, indicatorFn_of_mem (show z ∈ B.eval x₀ from hz₀), add_zero]
    · refine add_nonneg ?_ ?_
      · rw [indicatorBifun_apply]
        by_cases hx : x ∈ A.eval u <;> simp [hx]
      · rw [indicatorBifun_apply]
        by_cases hz : z ∈ B.eval x <;> simp [hz]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem h]
    symm
    refine le_antisymm le_top (le_iInf fun x => ?_)
    by_cases hx : x ∈ A.eval u
    · have hz : z ∉ B.eval x := fun hc => h ⟨x, hx, hc⟩
      rw [indicatorBifun_apply, indicatorFn_of_mem hx, indicatorBifun_apply,
        indicatorFn_of_notMem hz, zero_add]
    · rw [indicatorBifun_apply, indicatorFn_of_notMem hx]
      by_cases hz : z ∈ B.eval x
      · rw [indicatorBifun_apply, indicatorFn_of_mem hz, add_zero]
      · rw [indicatorBifun_apply, indicatorFn_of_notMem hz]
        simp

end ConvexProcess

end Algebra

/-! ### The adjoint of a convex process -/

section Adjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} {A : ConvexProcess U X}

namespace ConvexProcess

/-- The **adjoint** of a supremum-oriented convex process:
`A* x* = {u* | ⟨u, u*⟩ ≥ ⟨x, x*⟩ for every x ∈ A u and every u}`. It is a convex process from `Y`
to `V`, and it is infimum oriented. -/
def adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2}
      zero_mem' := by
        intro p _
        change Bx p.2 (0 : Y) ≤ Bu p.1 (0 : V)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bx p.2 (y₁ + y₂) ≤ Bu p.1 (v₁ + v₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bx p.2 ((c : ℝ) • y) ≤ Bu p.1 ((c : ℝ) • v)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

/-- The **adjoint of an infimum-oriented convex process**: the same definition with the inequality
reversed. Keeping the two apart is what makes `A** = cl A` come out right. -/
def coadjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ConvexProcess Y V where
  graph :=
    { carrier := {q : Y × V | ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1}
      zero_mem' := by
        intro p _
        change Bu p.1 (0 : V) ≤ Bx p.2 (0 : Y)
        simp
      add_mem' := by
        rintro ⟨y₁, v₁⟩ ⟨y₂, v₂⟩ h₁ h₂ p hp
        change Bu p.1 (v₁ + v₂) ≤ Bx p.2 (y₁ + y₂)
        rw [map_add, map_add]
        exact add_le_add (h₁ p hp) (h₂ p hp)
      smul_mem' := by
        rintro c ⟨y, v⟩ h p hp
        change Bu p.1 ((c : ℝ) • v) ≤ Bx p.2 ((c : ℝ) • y)
        rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (h p hp) c.2 }

@[simp] theorem mem_graph_adjointProcess {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 q.1 ≤ Bu p.1 q.2 :=
  Iff.rfl

@[simp] theorem mem_graph_coadjointProcess {q : Y × V} :
    q ∈ (coadjointProcess Bu Bx A).graph ↔ ∀ p : U × X, p ∈ A.graph → Bu p.1 q.2 ≤ Bx p.2 q.1 :=
  Iff.rfl

@[simp] theorem mem_eval_adjointProcess {y : Y} {v : V} :
    v ∈ (adjointProcess Bu Bx A).eval y ↔ ∀ p : U × X, p ∈ A.graph → Bx p.2 y ≤ Bu p.1 v :=
  Iff.rfl

/-- The graph of `A*` is the polar of the graph of `A`, up to the sign flip on the first factor
that the adjoint of a bifunction carries. -/
theorem mem_graph_adjointProcess_iff_mem_polarCone {q : Y × V} :
    q ∈ (adjointProcess Bu Bx A).graph ↔
      ((-q.2, q.1) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X)) := by
  simp only [mem_graph_adjointProcess, mem_polarCone, prodPairing_apply, map_neg,
    SetLike.mem_coe]
  constructor
  · intro h p hp
    have := h p hp
    linarith
  · intro h p hp
    have := h p hp
    linarith

/-- **The adjoint of the indicator bifunction of `A` is the indicator bifunction of `A*`.** `A*`
carries the opposite orientation, which is why the indicator appears negated: an infimum-oriented
set is identified with `-δ(· | ·)`. -/
theorem adjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) (v : V) :
    adjointBifun Bu Bx A.indicatorBifun y v = -((adjointProcess Bu Bx A).indicatorBifun y v) := by
  rw [adjointBifun_eq_neg_conj_graphFn, graphFn_indicatorBifun,
    conj_indicatorFn_eq_indicatorFn_polarCone (fun a ha => A.smul_graph ha)
      ⟨0, A.zero_mem_graph⟩]
  congr 1
  by_cases h : ((-v, y) : V × Y) ∈ polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))
  · rw [indicatorFn_of_mem h, indicatorBifun_apply,
      indicatorFn_of_mem (show v ∈ (adjointProcess Bu Bx A).eval y from
        mem_graph_adjointProcess_iff_mem_polarCone.2 h)]
  · rw [indicatorFn_of_notMem h, indicatorBifun_apply,
      indicatorFn_of_notMem (show v ∉ (adjointProcess Bu Bx A).eval y from fun hc =>
        h (mem_graph_adjointProcess_iff_mem_polarCone.1 hc))]

/-- The graph of `A**` is the bipolar of the graph of `A`. The two sign flips cancel, which is why
the second adjoint must be the *infimum-oriented* one. -/
theorem graph_coadjointProcess_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = polarCone (prodPairing Bu Bx).flip
          (polarCone (prodPairing Bu Bx) (A.graph : Set (U × X))) := by
  ext q
  simp only [SetLike.mem_coe, mem_graph_coadjointProcess, mem_polarCone, LinearMap.flip_apply,
    prodPairing_apply]
  constructor
  · rintro h ⟨a, b⟩ hab
    have hmem : ((b, -a) : Y × V) ∈ (adjointProcess Bu Bx A).graph :=
      mem_graph_adjointProcess_iff_mem_polarCone.2 (by simpa using hab)
    have hb := h (b, -a) hmem
    simp only [map_neg] at hb
    linarith
  · rintro h ⟨y, v⟩ hyv
    have hmem := mem_graph_adjointProcess_iff_mem_polarCone.1 hyv
    have hb := h (-v, y) hmem
    simp only [map_neg] at hb
    linarith

private theorem mul_le_iff_le_inv_mul {a : ℝ} (ha : 0 < a) (r s : ℝ) :
    a * r ≤ s ↔ r ≤ a⁻¹ * s := by
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha.le)
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · intro h
    have h' := mul_le_mul_of_nonneg_left h ha.le
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

private theorem le_mul_iff_inv_mul_le {a : ℝ} (ha : 0 < a) (r s : ℝ) :
    s ≤ a * r ↔ a⁻¹ * s ≤ r := by
  constructor
  · intro h
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.2 ha.le)
    rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at h'
  · intro h
    have h' := mul_le_mul_of_nonneg_left h ha.le
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at h'

/-- **The adjoint of a scalar multiple**: `(λ A)* = λ (A*)` for `λ > 0`.

Rockafellar deduces this from the adjoint formula for `Fλ`. It is cheaper here as a direct
computation on cones: `(y, v) ∈ graph (λA)*` says `λ⟨x, y⟩ ≤ ⟨u, v⟩` on `graph A`, which is
`(y, λ⁻¹ v) ∈ graph A*` after dividing by `λ`, and that is exactly `v ∈ λ (A* y)`. Positivity of
`λ` is used only to divide. -/
theorem adjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    adjointProcess Bu Bx (a • A) = a • adjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_adjointProcess, mem_graph_smul]
  constructor
  · intro h
    refine ⟨a⁻¹ • q.2, fun p hp => ?_, ?_⟩
    · have hmem : ((p.1, a • p.2) : U × X) ∈ (a • A).graph := ⟨p.2, hp, rfl⟩
      have h' := h (p.1, a • p.2) hmem
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h' ⊢
      exact (mul_le_iff_le_inv_mul ha _ _).1 h'
    · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨w, hw, hv⟩ p ⟨x, hx, hz⟩
    have hz' : p.2 = a • x := hz
    have hv' : q.2 = a • w := hv
    have hle := hw (p.1, x) hx
    rw [hz', hv']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hle ha.le

/-- **The adjoint of a scalar multiple, for an infimum-oriented process**: `(λ A)* = λ (A*)`, with
the adjoint taken in the reversed sense. The proof is `adjointProcess_smul` with both inequalities
turned round. -/
theorem coadjointProcess_smul (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) {a : ℝ}
    (ha : 0 < a) (A : ConvexProcess U X) :
    coadjointProcess Bu Bx (a • A) = a • coadjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  simp only [mem_graph_coadjointProcess, mem_graph_smul]
  constructor
  · intro h
    refine ⟨a⁻¹ • q.2, fun p hp => ?_, ?_⟩
    · have hmem : ((p.1, a • p.2) : U × X) ∈ (a • A).graph := ⟨p.2, hp, rfl⟩
      have h' := h (p.1, a • p.2) hmem
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h' ⊢
      exact (le_mul_iff_inv_mul_le ha _ _).1 h'
    · rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · rintro ⟨w, hw, hv⟩ p ⟨x, hx, hz⟩
    have hz' : p.2 = a • x := hz
    have hv' : q.2 = a • w := hv
    have hle := hw (p.1, x) hx
    rw [hz', hv']
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hle ha.le

end ConvexProcess

end Adjoint

/-! ### `A*` is closed, and `A** = cl A` -/

section AdjointTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

section Closed

variable [TopologicalSpace V] [TopologicalSpace Y]

/-- **The adjoint of a convex process is a *closed* convex process**, being an intersection of
homogeneous closed half-spaces. -/
theorem isClosed_graph_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] [IsContinuousPairing Bx.flip] (A : ConvexProcess U X) :
    IsClosed ((adjointProcess Bu Bx A).graph : Set (Y × V)) := by
  have h : ((adjointProcess Bu Bx A).graph : Set (Y × V))
      = ⋂ p ∈ (A.graph : Set (U × X)), {q : Y × V | Bx p.2 q.1 ≤ Bu p.1 q.2} := by
    ext q
    simp [mem_graph_adjointProcess]
  rw [h]
  refine isClosed_biInter fun p _ => isClosed_le ?_ ?_
  · exact (continuous_pairing Bx.flip p.2).comp continuous_fst
  · exact (continuous_pairing Bu.flip p.1).comp continuous_snd

end Closed

section Bipolar

variable [TopologicalSpace U] [TopologicalSpace X] [IsTopologicalAddGroup U]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ U] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ U]
  [LocallyConvexSpace ℝ X]

/-- **`A** = cl A`.** Read through `graph_coadjointProcess_adjointProcess`, this is exactly the
bipolar theorem `K°° = cl K` for the graph. -/
theorem graph_coadjointProcess_adjointProcess_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    ((coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A)).graph : Set (U × X))
      = closure (A.graph : Set (U × X)) := by
  rw [graph_coadjointProcess_adjointProcess]
  exact polarCone_polarCone A.convex_graph (fun a ha => A.smul_graph ha) ⟨0, A.zero_mem_graph⟩

/-- **A convex process is closed exactly when it is its own second adjoint.** -/
theorem coadjointProcess_adjointProcess_eq_self_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    coadjointProcess Bx.flip Bu.flip (adjointProcess Bu Bx A) = A ↔
      IsClosed (A.graph : Set (U × X)) := by
  constructor
  · intro h
    rw [← closure_eq_iff_isClosed,
      ← graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h]
  · intro h
    refine ConvexProcess.ext (SetLike.ext' ?_)
    rw [graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A, h.closure_eq]

end Bipolar

end ConvexProcess

end AdjointTopology

/-! ### The two inner products

`⟨Au, x*⟩` is the bracket of the indicator bifunction of `A`, and `⟨u, A* x*⟩` is the concave
bracket of its adjoint. Both are ordinary extremum problems over the values of a process: a
maximisation of `⟨·, x*⟩` over `A u`, and a minimisation of `⟨u, ·⟩` over `A* x*`. -/

section Bracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **The inner product `⟨Au, x*⟩` is the support function of the convex set `A u`.** Every clause
about the `x*` variable below is then a property of support functions; the identity itself is
`supportFn_eq_conj_indicatorFn` read backwards, since `⟨Fu, ·⟩` is by definition the conjugate of
`F u = δ(· | A u)`. -/
theorem bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    bracket Bx A.indicatorBifun u = supportFn Bx (A.eval u) :=
  (supportFn_eq_conj_indicatorFn Bx (A.eval u)).symm

/-- The first of Rockafellar's two extremum problems: `⟨Au, x*⟩ = sup {⟨x, x*⟩ | x ∈ A u}`. -/
theorem bracket_indicatorBifun_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : bracket Bx A.indicatorBifun u y = ⨆ x ∈ A.eval u, ((Bx x y : ℝ) : EReal) := by
  rw [bracket_indicatorBifun, supportFn_apply]

/-- **`⟨Au, ·⟩` is positively homogeneous**, being a support function. -/
theorem posHomogeneous_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (u : U) : PosHomogeneous (bracket Bx A.indicatorBifun u) := by
  rw [bracket_indicatorBifun]
  exact posHomogeneous_supportFn Bx _

/-- **`⟨Au, ·⟩` is convex**, being a conjugate. -/
theorem convexFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    ConvexFn (bracket Bx A.indicatorBifun u) :=
  convexFn_bracket Bx A.indicatorBifun u

/-- **`⟨A ·, x*⟩` is positively homogeneous.** This is the one clause that uses the definition of a
convex process rather than the general theory of brackets: `A (λ u) = λ (A u)` (`eval_smul_arg`),
and the support function of a positive multiple of a set is the corresponding multiple of the
support function. -/
theorem posHomogeneous_bracket_indicatorBifun_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) (y : Y) :
    PosHomogeneous fun u => bracket Bx A.indicatorBifun u y := by
  intro a ha u
  change bracket Bx A.indicatorBifun (a • u) y = (a : EReal) * bracket Bx A.indicatorBifun u y
  rw [bracket_indicatorBifun, bracket_indicatorBifun, eval_smul_arg A ha, supportFn_smul Bx ha]

/-- **`⟨A ·, x*⟩` is concave**, the bracket of a convex bifunction being concave in its first
variable. -/
theorem concaveFn_bracket_indicatorBifun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X)
    (y : Y) : ConcaveFn fun u => bracket Bx A.indicatorBifun u y :=
  concaveFn_bracket A.convexBifun_indicatorBifun Bx y

/-- **The inner product `⟨Au, x*⟩` vanishes at the origin**, because `A 0` contains `0` and the
support function of a nonempty set is `0` at `0`. -/
@[simp] theorem bracket_indicatorBifun_zero_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) : bracket Bx A.indicatorBifun 0 (0 : Y) = 0 := by
  rw [bracket_indicatorBifun]
  exact supportFn_zero ⟨0, A.zero_mem_eval_zero⟩

end ConvexProcess

end Bracket

section BracketClosed

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsContinuousPairing Bx.flip]

namespace ConvexProcess

/-- **`⟨Au, ·⟩` is closed** as well as convex and positively homogeneous. -/
theorem closedFn_bracket_indicatorBifun (A : ConvexProcess U X) (u : U) :
    ClosedFn (bracket Bx A.indicatorBifun u) :=
  closedFn_bracket (F := A.indicatorBifun) u

end ConvexProcess

end BracketClosed

section ConcaveBracket

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The second of Rockafellar's two extremum problems: `⟨u, A* x*⟩ = inf {⟨u, u*⟩ | u* ∈ A* x*}`.

Together with `bracket_indicatorBifun_apply` this is a dual pair of linear programs; the two values
differ only by a closure in `u` (`concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁`). The
proof is the definition of the concave bracket plus `adjointBifun_indicatorBifun`: the indicator of
`A* x*` turns the unrestricted infimum into a restricted one. -/
theorem concaveBracket_adjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y
      = ⨅ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal) := by
  rw [concaveBracket_apply]
  refine iInf_congr fun v => ?_
  rw [adjointBifun_indicatorBifun]
  by_cases hv : v ∈ (adjointProcess Bu Bx A).eval y
  · rw [indicatorBifun_apply, indicatorFn_of_mem hv, neg_zero, sub_zero, iInf_pos hv]
  · rw [indicatorBifun_apply, indicatorFn_of_notMem hv, iInf_neg hv]
    simp

end ConvexProcess

end ConcaveBracket

section ConcaveBracketClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- **`⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`**: the two inner products differ by a closure in `u`.

The concave closure in the first variable is the *only* difference between them, for every convex
process — closedness of `A` plays no part. This is `concaveBracket_adjointBifun_eq_partialCl₁`
applied to the indicator bifunction. -/
theorem concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁ (A : ConvexProcess U X) (y : Y) :
    (fun u => concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u y)
      = fun u => partialCl₁ (fun p : U × Y => bracket Bx A.indicatorBifun p.1 p.2) (u, y) :=
  concaveBracket_adjointBifun_eq_partialCl₁ A.convexBifun_indicatorBifun y

end ConvexProcess

end ConcaveBracketClosure

/-! ### The adjoint of a sum of processes -/

section SupConvIndicator

variable {X : Type*} [AddCommGroup X]

/-- The concave mirror of `infConv_indicatorFn`: the supremal convolute of two *negated* indicator
functions is the negated indicator function of the sum of the sets. Infimum-oriented convex sets
are carried by `-δ(· | ·)` (see `ConvexProcess.adjointBifun_indicatorBifun`), so this is the form
in which the adjoint of an infimal convolute speaks about processes.

Proof idea: `supConv` is `infConv` conjugated by negation, so the two negations inside cancel and
`infConv_indicatorFn` applies verbatim. -/
theorem supConv_neg_indicatorFn (S T : Set X) :
    supConv (fun x => -(indicatorFn S x)) (fun x => -(indicatorFn T x))
      = fun x => -(indicatorFn (S + T) x) := by
  funext x
  change -(infConv (fun w => -(-(indicatorFn S w))) (fun w => -(-(indicatorFn T w))) x) = _
  simp only [neg_neg]
  rw [infConv_indicatorFn]

end SupConvIndicator

section AdjointAdd

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **The adjoint of a sum is the sum of the adjoints**: `(A₁ + A₂)* = A₁* + A₂*`.

Where the book assumes `ri (dom A₁) ∩ ri (dom A₂) ≠ ∅`, the hypothesis here is exactness of the
sum of the two support functions `u ↦ ⟨Aᵢ u, y⟩`, one instance per `y`. Since `IsExactSum` also
requires both summands proper, this is stronger than the book's hypothesis. -/
theorem adjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A₁ A₂ : ConvexProcess U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(supportFn Bx (A₁.eval u) y))
      (fun u => -(supportFn Bx (A₂.eval u) y))) :
    adjointProcess Bu Bx (A₁ + A₂) = adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂ := by
  have hex' : ∀ y : Y, IsExactSum Bu (fun u => -(bracket Bx A₁.indicatorBifun u y))
      (fun u => -(bracket Bx A₂.indicatorBifun u y)) := by
    intro y
    have e₁ : (fun u => -(bracket Bx A₁.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₁.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₁ u) y)
    have e₂ : (fun u => -(bracket Bx A₂.indicatorBifun u y))
        = fun u => -(supportFn Bx (A₂.eval u) y) :=
      funext fun u => congrArg Neg.neg (congrFun (bracket_indicatorBifun Bx A₂ u) y)
    rw [e₁, e₂]
    exact hex y
  have key : ∀ y : Y, (adjointProcess Bu Bx (A₁ + A₂)).eval y
      = (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂).eval y := by
    intro y
    have hL : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = adjointBifun Bu Bx (A₁ + A₂).indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx (A₁ + A₂) y v).symm
    have hR₁ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y) v))
        = adjointBifun Bu Bx A₁.indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx A₁ y v).symm
    have hR₂ : (fun v => -(indicatorFn ((adjointProcess Bu Bx A₂).eval y) v))
        = adjointBifun Bu Bx A₂.indicatorBifun y :=
      funext fun v => (adjointBifun_indicatorBifun Bu Bx A₂ y v).symm
    have heq : (fun v => -(indicatorFn ((adjointProcess Bu Bx (A₁ + A₂)).eval y) v))
        = fun v => -(indicatorFn ((adjointProcess Bu Bx A₁).eval y
            + (adjointProcess Bu Bx A₂).eval y) v) := by
      rw [hL, ← supConv_neg_indicatorFn, hR₁, hR₂, indicatorBifun_add]
      exact adjointBifun_infConvBifun Bu Bx _ _ (hex' y)
    have hsets : (adjointProcess Bu Bx (A₁ + A₂)).eval y
        = (adjointProcess Bu Bx A₁).eval y + (adjointProcess Bu Bx A₂).eval y :=
      indicatorFn_injective (funext fun v => neg_injective (congrFun heq v))
    rw [hsets, eval_add]
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  obtain ⟨y, v⟩ := q
  rw [← mem_eval, ← mem_eval, key y]

end ConvexProcess

end AdjointAdd

/-! ### The adjoint of a product of processes -/

section Sandwich

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **A linear sandwich.** If a concave `p` lies below a convex `q`, the two add exactly, and each
straddles `0` at the origin from its own side, then some `⟨·, y⟩` runs between them.

This is Fenchel's duality theorem read at a *positively homogeneous* pair. The two extrema are
`p*(y) ≤ 0` and `q*(y) ≥ 0` for free, so the attained dual value `p*(y) - q*(y) ≥ 0` forces both to
vanish, and `p*(y) = 0` and `q*(y) = 0` say precisely `p ≤ ⟨·, y⟩` and `⟨·, y⟩ ≤ q`. No convexity
hypothesis appears: `IsExactSum` already carries it. -/
theorem exists_pairing_sandwich {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {p q : E → EReal}
    (hex : IsExactSum B q fun x => -(p x)) (hle : ∀ x, p x ≤ q x)
    (hp0 : (0 : EReal) ≤ p 0) (hq0 : q 0 ≤ 0) :
    ∃ y : F, (∀ x, p x ≤ ((B x y : ℝ) : EReal)) ∧ ∀ x, ((B x y : ℝ) : EReal) ≤ q x := by
  have hex' : IsExactSum B q (-p) := hex
  have hqnb : ∀ x, q x ≠ ⊥ := hex'.proper_left.ne_bot
  have hpnt : ∀ x, p x ≠ ⊤ := fun x hx => hex'.proper_right.ne_bot x (by simp [hx])
  have hinf : (0 : EReal) ≤ ⨅ x, q x - p x := by
    refine le_iInf fun x => ?_
    rw [_root_.EReal.le_sub_iff_add_le (.inr (hqnb x)) (.inl (hpnt x)), zero_add]
    exact hle x
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq (B := B) hex'
  have hcc_le : concaveConj B p y ≤ 0 := by
    have h := concaveConj_le_sub B p 0 y
    simp only [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero] at h
    refine h.trans ?_
    have hz : (0 : EReal) - p 0 = -(p 0) := zero_add _
    rw [hz]
    exact _root_.EReal.neg_le.2 (by rw [neg_zero]; exact hp0)
  have hconj_ge : (0 : EReal) ≤ conj B q y := by
    have h := sub_le_conj B q 0 y
    simp only [map_zero, LinearMap.zero_apply, _root_.EReal.coe_zero] at h
    refine le_trans ?_ h
    have hz : (0 : EReal) - q 0 = -(q 0) := zero_add _
    rw [hz]
    exact _root_.EReal.le_neg.2 (by rw [neg_zero]; exact hq0)
  have hbne : conj B q y ≠ ⊥ := by
    intro h
    rw [h] at hconj_ge
    exact absurd hconj_ge (by simp)
  have hcne : concaveConj B p y ≠ ⊤ := by
    intro h
    rw [h] at hcc_le
    exact absurd hcc_le (by simp)
  have hkey : conj B q y ≤ concaveConj B p y := by
    have h0 : (0 : EReal) ≤ concaveConj B p y - conj B q y := by rw [hy]; exact hinf
    rwa [_root_.EReal.le_sub_iff_add_le (.inl hbne) (.inr hcne), zero_add] at h0
  refine ⟨y, fun x => ?_, fun x => ?_⟩
  · have hmem : ((0 : ℝ) : EReal) ≤ concaveConj B p y := by
      rw [_root_.EReal.coe_zero]
      exact hconj_ge.trans hkey
    have h3 := coe_le_concaveConj_iff.1 hmem x
    rwa [affineFn_apply, _root_.EReal.coe_zero, sub_zero] at h3
  · have hmem : conj B q y ≤ ((0 : ℝ) : EReal) := by
      rw [_root_.EReal.coe_zero]
      exact hkey.trans hcc_le
    have h3 := conj_le_coe_iff.1 hmem x
    rwa [affineFn_apply, _root_.EReal.coe_zero, sub_zero] at h3

end Sandwich

section AdjointComp

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]

namespace ConvexProcess

/-- **The inclusion that costs nothing**: `A* B* ⊆ (BA)*`.

A pair `(z*, u*)` that factors through `B*` and then `A*` chains the two defining inequalities,
`⟨z, z*⟩ ≤ ⟨x, x*⟩ ≤ ⟨u, u*⟩`, for every factorisation `u ↦ x ↦ z` in `BA`. -/
theorem comp_adjointProcess_le (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z) :
    ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B)).graph
      ≤ (adjointProcess Bu Bz (B.comp A)).graph := by
  rintro ⟨w, v⟩ ⟨y, hwy, hyv⟩ ⟨u, z⟩ ⟨x, hux, hxz⟩
  exact le_trans (hwy (x, z) hxz) (hyv (u, x) hux)

/-- **The adjoint of a product is the product of the adjoints**: `(BA)* = A* B*`.

Read directly this is a *sandwich*: `(x*, u*) ∈ (BA)*` says the concave `x ↦ ⟨Bx, z*⟩` lies below
the convex `x ↦ ⟨u*, A⁻¹x⟩`, and a factorisation through `A*` and `B*` is exactly a linear
functional running between them, which `exists_pairing_sandwich` supplies.

Where the book assumes `ri (range A) ∩ ri (dom B) ≠ ∅`, the hypothesis here is that condition in
`IsExactSum` form, one instance per `(z*, u*)` — the two effective domains involved *are*
`range A` and `dom B`. As `IsExactSum` also requires both summands proper, it is stronger than the
book's hypothesis. -/
theorem adjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z)
    (hex : ∀ (w : W) (v : V), IsExactSum Bx
      (fun x => ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal)))) :
    adjointProcess Bu Bz (B.comp A)
      = (adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B) := by
  refine ConvexProcess.ext (SetLike.ext fun r => ?_)
  obtain ⟨w, v⟩ := r
  refine ⟨fun hr => ?_, fun hr => comp_adjointProcess_le Bu Bx Bz A B hr⟩
  have hle : ∀ x : X, (⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal))
      ≤ ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal) := by
    intro x
    refine iSup₂_le fun z hz => le_iInf₂ fun u hu => ?_
    exact_mod_cast hr (u, z) ⟨x, hu, hz⟩
  have hp0 : (0 : EReal) ≤ ⨆ z ∈ B.eval (0 : X), ((Bz z w : ℝ) : EReal) :=
    le_iSup₂_of_le (0 : Z) B.zero_mem_eval_zero (by simp)
  have hq0 : (⨅ u ∈ A.inv.eval (0 : X), ((Bu u v : ℝ) : EReal)) ≤ 0 :=
    iInf₂_le_of_le (0 : U) A.inv.zero_mem_eval_zero (by simp)
  obtain ⟨y, hpy, hqy⟩ := exists_pairing_sandwich (hex w v) hle hp0 hq0
  refine ⟨y, ?_, ?_⟩
  · rintro ⟨x, z⟩ hxz
    have h := le_trans (le_iSup₂_of_le z hxz le_rfl) (hpy x)
    exact_mod_cast h
  · rintro ⟨u, x⟩ hux
    have h := le_trans (hqy x) (iInf₂_le_of_le u hux le_rfl)
    exact_mod_cast h

end ConvexProcess

end AdjointComp



/-! ### The conjugate of an image under a convex process -/

section ImageConj

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The indicator bifunction of `A⁻¹` is the indicator bifunction of `A` read backwards: both
values are `δ(· | ·)` of the same membership `(u, x) ∈ graph A`. -/
@[simp] theorem indicatorBifun_inv (A : ConvexProcess U X) (x : X) (u : U) :
    A.inv.indicatorBifun x u = A.indicatorBifun u x := by
  rw [indicatorBifun_apply, indicatorBifun_apply]
  by_cases h : (u, x) ∈ A.graph
  · rw [indicatorFn_of_mem (show u ∈ A.inv.eval x from h),
      indicatorFn_of_mem (show x ∈ A.eval u from h)]
  · rw [indicatorFn_of_notMem (show u ∉ A.inv.eval x from h),
      indicatorFn_of_notMem (show x ∉ A.eval u from h)]

/-- **`(A⁻¹)* = A*⁻¹`.** The inverse of a supremum-oriented process is infimum oriented, so its
adjoint is the `coadjointProcess`; with that reading the identity is an unfolding, both sides
being `{(v, y) | ⟨x, y⟩ ≤ ⟨u, v⟩ for every (u, x) ∈ graph A}`. -/
theorem coadjointProcess_inv (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    coadjointProcess Bx Bu A.inv = (adjointProcess Bu Bx A).inv := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  exact ⟨fun h p hp => h (p.2, p.1) hp, fun h p hp => h (p.2, p.1) hp⟩

/-- **The `F⁎*` entry of the process/bifunction dictionary**: the lower adjoint of the indicator
bifunction of `A` is the indicator bifunction of `A*⁻¹`.

This is `adjointBifun_indicatorBifun` with the two negations of `lowerAdjointBifun` cancelling
against the negation the opposite orientation of `A*` puts on its indicator, and the reversal
`indicatorBifun_inv` absorbing the transposition. It is the last thing `(Af)* = A*⁻¹ f*` needs. -/
theorem lowerAdjointBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    lowerAdjointBifun Bu Bx A.indicatorBifun = (adjointProcess Bu Bx A).inv.indicatorBifun := by
  funext v y
  rw [lowerAdjointBifun_apply, adjointBifun_indicatorBifun, neg_neg, indicatorBifun_inv]

/-- The indicator bifunction of a convex process is finite at the origin, `0` being in `A 0`.
This is the "finite somewhere" side condition the closed-image results ask of `F`. -/
theorem indicatorBifun_zero_zero_ne_top (A : ConvexProcess U X) :
    A.indicatorBifun 0 0 ≠ ⊤ := by
  rw [indicatorBifun_apply, indicatorFn_of_mem A.zero_mem_eval_zero]
  simp

/-- **`(Af)* = A*⁻¹ f*`**, where `Af` is the image `Ff` of `f` under the indicator bifunction `F`
of `A`, i.e. `(Af)(x) = inf {f u | x ∈ A u}`.

This specialises the conjugate of an image under a bifunction; the only work is the dictionary
`lowerAdjointBifun_indicatorBifun`. Rockafellar's `ri (dom f) ∩ ri (dom A) ≠ ∅` becomes the
`IsExactSum` of `conj_imageBifun`, `dom F` being `dom A`. -/
theorem conj_imageBifun_indicatorBifun (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) {f : U → EReal} (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    conj Bx (imageBifun A.indicatorBifun f) y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (conj Bu f) y := by
  rw [← lowerAdjointBifun_indicatorBifun]
  exact conj_imageBifun_eq_imageBifun A.indicatorBifun_ne_bot hf hex

/-- **The infimum defining `(A*⁻¹ f*)(x*)` is attained.** This is `exists_conj_imageBifun_eq` read
through the same dictionary. -/
theorem exists_imageBifun_indicatorBifun_adjointProcess_eq (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) {f : U → EReal} (hf : Proper f) {y : Y}
    (hex : IsExactSum Bu f (fun u => -(bracket Bx A.indicatorBifun u y))) :
    ∃ v : V, conj Bu f v + (adjointProcess Bu Bx A).inv.indicatorBifun v y
      = imageBifun (adjointProcess Bu Bx A).inv.indicatorBifun (conj Bu f) y := by
  obtain ⟨v, hv⟩ := exists_conj_imageBifun_eq (Bu := Bu) (Bx := Bx) A.indicatorBifun_ne_bot hf hex
  refine ⟨v, ?_⟩
  rw [← conj_imageBifun_indicatorBifun Bu Bx A hf hex, ← hv, ← lowerAdjointBifun_indicatorBifun]
  rfl

end ConvexProcess

end ImageConj


/-! ### Bounded values force a linear transformation -/

section Linear

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {A : ConvexProcess U X}

namespace ConvexProcess

/-- `A 0` is a convex cone containing the origin, so if it is bounded it is `{0}`. -/
theorem eval_zero_eq_zero_of_isBounded (A : ConvexProcess U X)
    (hb : Bornology.IsBounded (A.eval 0)) : A.eval 0 = {0} := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hR0 : (0 : ℝ) ≤ R := by simpa using hR _ A.zero_mem_eval_zero
  refine Set.Subset.antisymm (fun x hx => ?_) (by simpa using A.zero_mem_eval_zero)
  by_contra hx0
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hc0 : (0 : ℝ) ≤ (R + 1) / ‖x‖ := div_nonneg (by linarith) (norm_nonneg x)
  have hmem := A.smul_mem_eval_zero hc0 hx
  have hle := hR _ hmem
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, div_mul_cancel₀ _ (ne_of_gt hxn)] at hle
  linarith

/-- If `A 0` is bounded and `A` has full domain, every value of `A` is a single point. -/
theorem exists_eval_eq_singleton (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) (u : U) : ∃ x, A.eval u = {x} := by
  obtain ⟨x, hx⟩ : (A.eval u).Nonempty := by rw [← mem_dom, hdom]; trivial
  obtain ⟨y, hy⟩ : (A.eval (-u)).Nonempty := by rw [← mem_dom, hdom]; trivial
  refine ⟨x, Set.Subset.antisymm (fun z hz => ?_) (by simpa using hx)⟩
  have hzy : z + y ∈ A.eval 0 := by
    have h := add_mem_graph hz hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  have hxy : x + y ∈ A.eval 0 := by
    have h := add_mem_graph hx hy
    rwa [Prod.mk_add_mk, add_neg_cancel] at h
  rw [A.eval_zero_eq_zero_of_isBounded hb, Set.mem_singleton_iff] at hzy hxy
  exact Set.mem_singleton_iff.2 (add_right_cancel (hzy.trans hxy.symm))

/-- **A convex process whose domain is everything and whose value at the origin is bounded is
(the graph of) a linear transformation.**

Linear transformations are exactly the convex processes all of whose values are nonempty and
bounded; the converse direction is `ConvexProcess.dom_ofLinearMap` together with
`ConvexProcess.eval_ofLinearMap`. -/
theorem exists_linearMap_of_isBounded (A : ConvexProcess U X) (hdom : A.dom = univ)
    (hb : Bornology.IsBounded (A.eval 0)) : ∃ T : U →ₗ[ℝ] X, ∀ u, A.eval u = {T u} := by
  choose T hT using A.exists_eval_eq_singleton hdom hb
  have hmem : ∀ u, (u, T u) ∈ A.graph := by
    intro u
    have h : T u ∈ A.eval u := by rw [hT u]; exact Set.mem_singleton _
    exact h
  have hadd : ∀ u₁ u₂, T (u₁ + u₂) = T u₁ + T u₂ := by
    intro u₁ u₂
    have h := add_mem_graph (hmem u₁) (hmem u₂)
    rw [Prod.mk_add_mk] at h
    have h' : T u₁ + T u₂ ∈ A.eval (u₁ + u₂) := h
    rw [hT (u₁ + u₂), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hT0 : T 0 = 0 := by
    have h0 : (0 : X) ∈ A.eval 0 := A.zero_mem_eval_zero
    rw [hT 0, Set.mem_singleton_iff] at h0
    exact h0.symm
  have hneg : ∀ u, T (-u) = -T u := by
    intro u
    have h := hadd u (-u)
    rw [add_neg_cancel, hT0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hpos : ∀ c : ℝ, 0 < c → ∀ u, T (c • u) = c • T u := by
    intro c hc u
    have h := smul_mem_graph hc.le (hmem u)
    rw [Prod.smul_mk] at h
    have h' : c • T u ∈ A.eval (c • u) := h
    rw [hT (c • u), Set.mem_singleton_iff] at h'
    exact h'.symm
  have hsmul : ∀ (c : ℝ) (u : U), T (c • u) = c • T u := by
    intro c u
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h1 : T ((-c) • u) = (-c) • T u := hpos _ (by linarith) u
      rw [neg_smul, hneg, neg_smul, neg_inj] at h1
      exact h1
    · simp [hT0]
    · exact hpos _ hc u
  exact ⟨{ toFun := T, map_add' := hadd, map_smul' := fun c u => hsmul c u }, hT⟩

end ConvexProcess

end Linear

/-! ### Closedness of the image -/

section Closedness

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {A : ConvexProcess U X} {C : Set U}

namespace ConvexProcess

/-- **If `A` is a closed convex process, `C` is a nonempty closed convex set, and no non-zero
vector of `A⁻¹ 0` recedes `C`, then `A C` is closed.** In particular this holds when `C` is
bounded, since then `0⁺C = {0}`.

This is the recession-cone criterion for a linear image, at the projection `(u, x) ↦ x`: `A C` is
the image of `graph A ∩ (C × X)`, whose recession cone is `graph A ∩ (0⁺C × X)` — the graph is its
own recession cone, being a pointed convex cone — and whose intersection with the kernel of the
projection is `{(v, 0) | v ∈ A⁻¹ 0 ∩ 0⁺C}`. No duality is needed. -/
theorem isClosed_image (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty)
    (h : ∀ v : U, (v, (0 : X)) ∈ A.graph → v ∈ recessionCone C → v = 0) :
    IsClosed (A.image C) := by
  have hSconv : Convex ℝ ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    Convex.inter (convex_graph A) (Convex.prod hC convex_univ)
  have hScl : IsClosed ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) :=
    hA.inter (hC'.prod isClosed_univ)
  rcases Set.eq_empty_or_nonempty ((A.graph : Set (U × X)) ∩ C ×ˢ (univ : Set X)) with hSe | hSne
  · have hempty : A.image C = ∅ := by rw [image_eq_image_snd, hSe, Set.image_empty]
    rw [hempty]
    exact isClosed_empty
  rw [image_eq_image_snd]
  refine isClosed_image_of_recessionCone_inter_ker _ hSconv hScl ?_
  rintro ⟨v, y⟩ ⟨hrec, hker⟩
  rw [recessionCone_inter (convex_graph A) hA (Convex.prod hC convex_univ)
    (hC'.prod isClosed_univ) hSne] at hrec
  obtain ⟨hg, hp⟩ := hrec
  rw [recessionCone_coe_pointedCone] at hg
  rw [recessionCone_prod hCne ⟨0, mem_univ 0⟩, recessionCone_univ] at hp
  have hy : y = 0 := by simpa using hker
  subst hy
  have hv : v = 0 := h v hg hp.1
  subst hv
  simp

/-- **The image of a nonempty compact convex set under a closed convex process is closed**, the
bounded case of `isClosed_image`. -/
theorem isClosed_image_of_isBounded (hA : IsClosed (A.graph : Set (U × X))) (hC : Convex ℝ C)
    (hC' : IsClosed C) (hCne : C.Nonempty) (hb : Bornology.IsBounded C) :
    IsClosed (A.image C) := by
  refine isClosed_image hA hC hC' hCne fun v _ hv => ?_
  have h0 : recessionCone C = {0} := recessionCone_eq_zero_of_isBounded hCne hb
  rw [h0] at hv
  simpa using hv

end ConvexProcess

end Closedness

/-! ### The reflected process, and the dictionary between the two orientations -/

section Reflect

variable {U X Z : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Z] [Module ℝ Z]

namespace ConvexProcess

/-- The **reflection** of a convex process: the process whose graph is the reflection of
`graph A` through the origin, so that `(A.reflect) u = -(A (-u))`.

Reflection is what exchanges the two orientations: reversing the inequality in the definition of
the adjoint is the same as reflecting the graph, so
`adjointProcess Bu Bx A.reflect = coadjointProcess Bu Bx A` (`adjointProcess_reflect`). Read the
other way round (`coadjointProcess_eq_reflect_adjointProcess`) it puts the reflection on the
*conclusion*, where `reflect_add` and `reflect_comp` cancel it, so the infimum-oriented mirrors
carry the supremum-oriented hypotheses unchanged. -/
def reflect (A : ConvexProcess U X) : ConvexProcess U X where
  graph :=
    { carrier := {p : U × X | -p ∈ A.graph}
      zero_mem' := by
        change -(0 : U × X) ∈ A.graph
        rw [_root_.neg_zero]
        exact A.graph.zero_mem
      add_mem' := by
        intro p q hp hq
        change -(p + q) ∈ A.graph
        rw [_root_.neg_add]
        exact A.graph.add_mem hp hq
      smul_mem' := by
        intro c p hp
        change -(c • p) ∈ A.graph
        rw [← smul_neg]
        exact Submodule.smul_mem A.graph c hp }

@[simp] theorem mem_graph_reflect {A : ConvexProcess U X} {p : U × X} :
    p ∈ A.reflect.graph ↔ -p ∈ A.graph := Iff.rfl

theorem reflect_involutive :
    Function.Involutive (reflect : ConvexProcess U X → ConvexProcess U X) := fun A => by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  rw [mem_graph_reflect, mem_graph_reflect, _root_.neg_neg]

@[simp] theorem reflect_reflect (A : ConvexProcess U X) : A.reflect.reflect = A :=
  reflect_involutive A

theorem reflect_injective :
    Function.Injective (reflect : ConvexProcess U X → ConvexProcess U X) :=
  reflect_involutive.injective

theorem eval_reflect (A : ConvexProcess U X) (u : U) : A.reflect.eval u = -(A.eval (-u)) := by
  ext x
  change -((u, x) : U × X) ∈ A.graph ↔ x ∈ -(A.eval (-u))
  rw [Set.mem_neg]
  exact Iff.rfl

theorem reflect_add (A₁ A₂ : ConvexProcess U X) :
    (A₁ + A₂).reflect = A₁.reflect + A₂.reflect := by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  obtain ⟨u, x⟩ := p
  rw [← mem_eval, ← mem_eval, eval_reflect, eval_add, eval_add, eval_reflect, eval_reflect,
    _root_.neg_add]

theorem reflect_comp (B : ConvexProcess X Z) (A : ConvexProcess U X) :
    (B.comp A).reflect = B.reflect.comp A.reflect := by
  refine ConvexProcess.ext (SetLike.ext fun p => ?_)
  constructor
  · rintro ⟨x, h, k⟩
    exact ⟨-x, by simpa using h, by simpa using k⟩
  · rintro ⟨x, h, k⟩
    exact ⟨-x, by simpa using h, by simpa using k⟩

/-- Reflection **bundled**: an additive automorphism of the convex processes from `U` to `X`.

It is involutive (`reflect_involutive`) and additive (`reflect_add`), so `.injective`, `.eq_iff`
and `.toPerm` come from the bundled form instead of being re-proved. -/
def reflectAut : AddAut (ConvexProcess U X) where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_involutive
  right_inv := reflect_involutive
  map_add' := reflect_add

@[simp] theorem reflectAut_apply (A : ConvexProcess U X) : reflectAut A = A.reflect := rfl

end ConvexProcess

end Reflect

section ReflectAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- **Reversing the inequality is reflecting the graph**: the supremum-oriented adjoint of the
reflected process is the infimum-oriented adjoint of the original one. -/
theorem adjointProcess_reflect (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    adjointProcess Bu Bx A.reflect = coadjointProcess Bu Bx A := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  have hx : ∀ (p : U × X), Bx (-p).2 q.1 = -(Bx p.2 q.1) := fun p => by
    rw [Prod.snd_neg, map_neg Bx p.2, LinearMap.neg_apply]
  have hu : ∀ (p : U × X), Bu (-p).1 q.2 = -(Bu p.1 q.2) := fun p => by
    rw [Prod.fst_neg, map_neg Bu p.1, LinearMap.neg_apply]
  simp only [mem_graph_adjointProcess, mem_graph_coadjointProcess, mem_graph_reflect]
  constructor
  · intro h p hp
    have hpp := h (-p) (by rw [_root_.neg_neg]; exact hp)
    rw [hx p, hu p] at hpp
    linarith
  · intro h p hp
    have hpp := h (-p) hp
    rw [hx p, hu p] at hpp
    linarith

/-- The mirror of `adjointProcess_reflect`: reflection also carries the infimum-oriented adjoint
back to the supremum-oriented one. -/
theorem coadjointProcess_reflect (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A : ConvexProcess U X) :
    coadjointProcess Bu Bx A.reflect = adjointProcess Bu Bx A := by
  rw [← adjointProcess_reflect Bu Bx A.reflect, reflect_reflect]

/-- The infimum-oriented adjoint is the reflection of the supremum-oriented one. Together with
`adjointProcess_reflect` this is the whole content of "the adjoint of an infimum-oriented process
is defined in the same way, except that the inequality is reversed". -/
theorem coadjointProcess_eq_reflect_adjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    coadjointProcess Bu Bx A = (adjointProcess Bu Bx A).reflect := by
  refine ConvexProcess.ext (SetLike.ext fun q => ?_)
  have hx : ∀ (p : U × X), Bx p.2 (-q).1 = -(Bx p.2 q.1) := fun p => by
    rw [Prod.fst_neg, map_neg (Bx p.2) q.1]
  have hu : ∀ (p : U × X), Bu p.1 (-q).2 = -(Bu p.1 q.2) := fun p => by
    rw [Prod.snd_neg, map_neg (Bu p.1) q.2]
  simp only [mem_graph_coadjointProcess, mem_graph_reflect, mem_graph_adjointProcess]
  constructor
  · intro h p hp
    rw [hx p, hu p]
    linarith [h p hp]
  · intro h p hp
    have hpp := h p hp
    rw [hx p, hu p] at hpp
    linarith

end ConvexProcess

end ReflectAdjoint

section ReflectTopology

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

section ReflectClosed

variable [TopologicalSpace U] [IsTopologicalAddGroup U] [TopologicalSpace X]
  [IsTopologicalAddGroup X]

/-- Reflection preserves closedness: it is a preimage under the homeomorphism `p ↦ -p`. -/
theorem isClosed_graph_reflect {A : ConvexProcess U X}
    (hA : IsClosed (A.graph : Set (U × X))) : IsClosed (A.reflect.graph : Set (U × X)) :=
  hA.preimage (continuous_neg (G := U × X))

end ReflectClosed

section CoadjointClosed

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y]

/-- **The adjoint of an infimum-oriented convex process is closed**, as in the supremum-oriented
case. -/
theorem isClosed_graph_coadjointProcess (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] [IsContinuousPairing Bx.flip] (A : ConvexProcess U X) :
    IsClosed ((coadjointProcess Bu Bx A).graph : Set (Y × V)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess]
  exact isClosed_graph_reflect (isClosed_graph_adjointProcess Bu Bx A)

end CoadjointClosed

section Bipolar

variable [TopologicalSpace U] [TopologicalSpace X] [IsTopologicalAddGroup U]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ U] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ U]
  [LocallyConvexSpace ℝ X]

/-- **Taking the infimum-oriented adjoint and then the supremum-oriented one also returns `cl A`.**

This is `graph_coadjointProcess_adjointProcess_eq_closure` read through
`adjointProcess_reflect`; the two sign flips still cancel, and it is what turns the closed halves
of the sum and product theorems into corollaries of their open halves. -/
theorem graph_adjointProcess_coadjointProcess_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    ((adjointProcess Bx.flip Bu.flip (coadjointProcess Bu Bx A)).graph : Set (U × X))
      = closure (A.graph : Set (U × X)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess, adjointProcess_reflect]
  exact graph_coadjointProcess_adjointProcess_eq_closure Bu Bx A

/-- **A convex process is closed exactly when the supremum-oriented adjoint of its
infimum-oriented adjoint is itself.** -/
theorem adjointProcess_coadjointProcess_eq_self_iff (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    (A : ConvexProcess U X) :
    adjointProcess Bx.flip Bu.flip (coadjointProcess Bu Bx A) = A ↔
      IsClosed (A.graph : Set (U × X)) := by
  rw [coadjointProcess_eq_reflect_adjointProcess, adjointProcess_reflect]
  exact coadjointProcess_adjointProcess_eq_self_iff Bu Bx A

end Bipolar

end ConvexProcess

end ReflectTopology

/-! ### Sums and products for infimum-oriented processes -/

section MirrorAlgebra

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]

namespace ConvexProcess

/-- **The adjoint of a sum, for two *infimum-oriented* processes**: `(A₁ + A₂)* = A₁* + A₂*`.

Rockafellar states the result for two processes "with the same orientation" and leaves the
infimum-oriented case implicit. It is the supremum-oriented theorem read through
`coadjointProcess_eq_reflect_adjointProcess`, reflection distributing over sums; the hypothesis is
`adjointProcess_add`'s own, verbatim. -/
theorem coadjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (A₁ A₂ : ConvexProcess U X)
    (hex : ∀ y : Y, IsExactSum Bu (fun u => -(supportFn Bx (A₁.eval u) y))
      (fun u => -(supportFn Bx (A₂.eval u) y))) :
    coadjointProcess Bu Bx (A₁ + A₂)
      = coadjointProcess Bu Bx A₁ + coadjointProcess Bu Bx A₂ := by
  rw [coadjointProcess_eq_reflect_adjointProcess Bu Bx (A₁ + A₂),
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A₁,
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A₂,
    adjointProcess_add Bu Bx A₁ A₂ hex, reflect_add]

/-- **The adjoint of a product, for two *infimum-oriented* processes**: `(BA)* = A* B*`.

Like `coadjointProcess_add`, this reflects the *adjoints* rather than the processes, so the
hypothesis is `adjointProcess_comp`'s own; `reflect_comp` is what makes the product come out in
the same order. -/
theorem coadjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (B : ConvexProcess X Z)
    (hex : ∀ (w : W) (v : V), IsExactSum Bx
      (fun x => ⨅ u ∈ A.inv.eval x, ((Bu u v : ℝ) : EReal))
      (fun x => -(⨆ z ∈ B.eval x, ((Bz z w : ℝ) : EReal)))) :
    coadjointProcess Bu Bz (B.comp A)
      = (coadjointProcess Bu Bx A).comp (coadjointProcess Bx Bz B) := by
  rw [coadjointProcess_eq_reflect_adjointProcess Bu Bz (B.comp A),
    coadjointProcess_eq_reflect_adjointProcess Bu Bx A,
    coadjointProcess_eq_reflect_adjointProcess Bx Bz B,
    adjointProcess_comp Bu Bx Bz A B hex, reflect_comp]

end ConvexProcess

end MirrorAlgebra

/-! ### The closed halves of the sum and product theorems -/

section ClosedHalves

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]

namespace ConvexProcess

/-- The sum of two closed convex processes is the infimum-oriented adjoint of the sum of their
adjoints, provided the two adjoints add exactly. This is the identity both closed-half results
about sums come from. -/
theorem add_eq_coadjointProcess_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    A₁ + A₂ = coadjointProcess Bx.flip Bu.flip
      (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂) := by
  rw [coadjointProcess_add Bx.flip Bu.flip _ _ hex,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A₁).2 hA₁,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A₂).2 hA₂]

/-- **The sum of two closed convex processes is closed.** It is an adjoint, and an adjoint is
always closed. -/
theorem isClosed_graph_add (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    IsClosed (((A₁ + A₂).graph : Set (U × X))) := by
  rw [add_eq_coadjointProcess_add Bu Bx hA₁ hA₂ hex]
  exact isClosed_graph_coadjointProcess Bx.flip Bu.flip _

end ConvexProcess

end ClosedHalves

section ClosedHalvesAdjoint

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

namespace ConvexProcess

/-- **`(A₁ + A₂)*` is the closure of `A₁* + A₂*`**, for closed `A₁` and `A₂`. -/
theorem graph_adjointProcess_add_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] [IsCompatiblePairing Bu.flip]
    [IsCompatiblePairing Bx.flip] {A₁ A₂ : ConvexProcess U X}
    (hA₁ : IsClosed (A₁.graph : Set (U × X))) (hA₂ : IsClosed (A₂.graph : Set (U × X)))
    (hex : ∀ u : U, IsExactSum Bx.flip
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₁).eval y) u))
      (fun y => -(supportFn Bu.flip ((adjointProcess Bu Bx A₂).eval y) u))) :
    ((adjointProcess Bu Bx (A₁ + A₂)).graph : Set (Y × V))
      = closure (((adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂).graph : Set (Y × V))) := by
  have h := graph_adjointProcess_coadjointProcess_eq_closure Bx.flip Bu.flip
    (adjointProcess Bu Bx A₁ + adjointProcess Bu Bx A₂)
  simp only [LinearMap.flip_flip] at h
  rw [add_eq_coadjointProcess_add Bu Bx hA₁ hA₂ hex, h]

end ConvexProcess

end ClosedHalvesAdjoint

section ClosedHalvesComp

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]

namespace ConvexProcess

/-- The product of two closed convex processes is the infimum-oriented adjoint of the product of
their adjoints. This is the identity both closed-half results about products come from. -/
theorem comp_eq_coadjointProcess_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    B.comp A = coadjointProcess Bz.flip Bu.flip
      ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B)) := by
  rw [coadjointProcess_comp Bz.flip Bx.flip Bu.flip _ _ hex,
    (coadjointProcess_adjointProcess_eq_self_iff Bx Bz B).2 hB,
    (coadjointProcess_adjointProcess_eq_self_iff Bu Bx A).2 hA]

/-- **The product of two closed convex processes is closed.** -/
theorem isClosed_graph_comp (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    IsClosed (((B.comp A).graph : Set (U × Z))) := by
  rw [comp_eq_coadjointProcess_comp Bu Bx Bz hA hB hex]
  exact isClosed_graph_coadjointProcess Bz.flip Bu.flip _

end ConvexProcess

end ClosedHalvesComp

section ClosedHalvesCompAdjoint

variable {U V X Y Z W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
  [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

namespace ConvexProcess

omit [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [LocallyConvexSpace ℝ Y] in
/-- **`(BA)*` is the closure of `A* B*`**, for closed `A` and `B`. -/
theorem graph_adjointProcess_comp_eq_closure (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (Bz : Z →ₗ[ℝ] W →ₗ[ℝ] ℝ) [IsCompatiblePairing Bu] [IsCompatiblePairing Bx]
    [IsCompatiblePairing Bz] [IsCompatiblePairing Bu.flip] [IsCompatiblePairing Bz.flip]
    {A : ConvexProcess U X} {B : ConvexProcess X Z}
    (hA : IsClosed (A.graph : Set (U × X))) (hB : IsClosed (B.graph : Set (X × Z)))
    (hex : ∀ (u : U) (z : Z), IsExactSum Bx.flip
      (fun y => ⨅ w ∈ (adjointProcess Bx Bz B).inv.eval y, ((Bz z w : ℝ) : EReal))
      (fun y => -(⨆ v ∈ (adjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)))) :
    ((adjointProcess Bu Bz (B.comp A)).graph : Set (W × V))
      = closure ((((adjointProcess Bu Bx A).comp
          (adjointProcess Bx Bz B)).graph : Set (W × V))) := by
  have h := graph_adjointProcess_coadjointProcess_eq_closure Bz.flip Bu.flip
    ((adjointProcess Bu Bx A).comp (adjointProcess Bx Bz B))
  simp only [LinearMap.flip_flip] at h
  rw [comp_eq_coadjointProcess_comp Bu Bx Bz hA hB hex, h]

end ConvexProcess

end ClosedHalvesCompAdjoint

/-! ### The two inner products for infimum-oriented processes

For an infimum-oriented process the indicator bifunction is the *concave* function `-δ(· | A u)`,
and the inner product `⟨Au, x*⟩` is its concave conjugate: an infimum over `A u` rather than a
supremum. As with `adjointProcess`/`coadjointProcess`, the two orientations are separate
definitions rather than two branches of one flag, and the whole mirror is driven by the single
sign dictionary `coBracket_eq_neg_bracket`. -/

section CoBracket

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

/-- The inner product `⟨Au, x*⟩` of an **infimum-oriented** convex process:
`⟨Au, x*⟩ = inf {⟨x, x*⟩ | x ∈ A u}`.

This is the concave conjugate of the concave indicator `-δ(· | A u)`, exactly as
`bracket _ A.indicatorBifun u` is the convex conjugate of `δ(· | A u)`. -/
noncomputable def coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    EReal :=
  ⨅ x ∈ A.eval u, ((Bx x y : ℝ) : EReal)

/-- The first of the two extremum problems, in infimum-oriented form:
`⟨Au, x*⟩ = inf {⟨x, x*⟩ | x ∈ A u}`. -/
theorem coBracket_apply (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    coBracket Bx A u y = ⨅ x ∈ A.eval u, ((Bx x y : ℝ) : EReal) := rfl

/-- The **sign dictionary** between the two orientations: the infimum-oriented inner product is
minus the supremum-oriented one, read at the reflected dual vector. Note that only the dual
variable is reflected — the primal variable `u` is untouched, because reversing the orientation
of a process does not reverse its argument. -/
theorem coBracket_eq_neg_bracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : coBracket Bx A u y = -(bracket Bx A.indicatorBifun u (-y)) := by
  rw [coBracket_apply, bracket_indicatorBifun_apply, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [← _root_.EReal.coe_neg, map_neg (Bx x) y, _root_.neg_neg]

theorem coBracket_eq_neg_bracket_fun (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    (fun u => coBracket Bx A u y) = fun u => -(bracket Bx A.indicatorBifun u (-y)) :=
  funext fun u => coBracket_eq_neg_bracket Bx A u y

/-- The infimum-oriented inner product is minus a support function, read at the reflected dual
vector. -/
theorem coBracket_eq_neg_supportFn (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U)
    (y : Y) : coBracket Bx A u y = -(supportFn Bx (A.eval u) (-y)) := by
  rw [coBracket_eq_neg_bracket, bracket_indicatorBifun]

/-- The negative of `⟨Au, ·⟩` is the supremum-oriented inner product composed with the linear
reflection `x* ↦ -x*`. This is the form in which the sign dictionary feeds the convexity and
closedness lemmas for a composition with a linear map. -/
theorem neg_coBracket_eq_compLin (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    (fun y => -(coBracket Bx A u y))
      = compLin (bracket Bx A.indicatorBifun u) (-LinearMap.id : Y →ₗ[ℝ] Y) := by
  funext y
  rw [coBracket_eq_neg_bracket, _root_.neg_neg]
  simp only [compLin, Function.comp_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq]

/-- **`⟨Au, ·⟩` is positively homogeneous**, in the infimum-oriented mirror. -/
theorem posHomogeneous_coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    PosHomogeneous (coBracket Bx A u) := by
  intro a ha y
  rw [coBracket_eq_neg_bracket, coBracket_eq_neg_bracket, ← smul_neg,
    posHomogeneous_bracket_indicatorBifun Bx A u a ha (-y), ← _root_.mul_neg]

/-- **`⟨Au, ·⟩` is concave** in the infimum-oriented mirror, being a concave conjugate. -/
theorem concaveFn_coBracket (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) :
    ConcaveFn (coBracket Bx A u) := by
  rw [concaveFn_iff_convexFn_neg, neg_coBracket_eq_compLin]
  exact convexFn_compLin _ (convexFn_bracket_indicatorBifun Bx A u)

/-- **`⟨A ·, x*⟩` is positively homogeneous**, in the infimum-oriented mirror. -/
theorem posHomogeneous_coBracket_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    PosHomogeneous fun u => coBracket Bx A u y := by
  intro a ha u
  change coBracket Bx A (a • u) y = (a : EReal) * coBracket Bx A u y
  rw [coBracket_eq_neg_bracket, coBracket_eq_neg_bracket, _root_.mul_neg]
  exact congrArg Neg.neg (posHomogeneous_bracket_indicatorBifun_arg Bx A (-y) a ha u)

/-- **`⟨A ·, x*⟩` is convex** in the infimum-oriented mirror, where in the supremum-oriented case
it is concave. Reversing the orientation of a process exchanges convexity and concavity in both
variables at once. -/
theorem convexFn_coBracket_arg (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (y : Y) :
    ConvexFn fun u => coBracket Bx A u y := by
  rw [coBracket_eq_neg_bracket_fun]
  exact concaveFn_iff_convexFn_neg.1 (concaveFn_bracket_indicatorBifun Bx A (-y))

/-- **The inner product vanishes at the origin**, in the infimum-oriented mirror. -/
@[simp] theorem coBracket_zero_zero (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) :
    coBracket Bx A 0 (0 : Y) = 0 := by
  rw [coBracket_eq_neg_bracket, _root_.neg_zero, bracket_indicatorBifun_zero_zero,
    _root_.neg_zero]

end ConvexProcess

end CoBracket

section CoBracketClosed

variable {U X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ} [IsContinuousPairing Bx.flip]

namespace ConvexProcess

/-- **`⟨Au, ·⟩` is a closed concave function** in the infimum-oriented mirror, the reflection
`x* ↦ -x*` being a homeomorphism. -/
theorem closedConcaveFn_coBracket (A : ConvexProcess U X) (u : U) :
    ClosedConcaveFn (coBracket Bx A u) := by
  rw [closedConcaveFn_iff, neg_coBracket_eq_compLin]
  exact closedFn_compLin (closedFn_bracket_indicatorBifun A u) (continuous_neg (G := Y))

end ConvexProcess

end CoBracketClosed

section CoBracketAdjoint

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

namespace ConvexProcess

omit [Module ℝ U] [Module ℝ V] [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
  [Module ℝ Y] in
private theorem iSup_mem_neg (s : Set V) (f : V → EReal) :
    ⨆ v ∈ -s, f v = ⨆ v ∈ s, f (-v) := by
  refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun v hv => ?_)
  · rw [Set.mem_neg] at hv
    exact le_iSup₂_of_le (-v) hv (le_of_eq (by rw [_root_.neg_neg]))
  · refine le_iSup₂_of_le (-v) ?_ le_rfl
    rw [Set.mem_neg, _root_.neg_neg]
    exact hv

/-- The second of the two extremum problems, in infimum-oriented form:
`⟨u, A* x*⟩ = sup {⟨u, u*⟩ | u* ∈ A* x*}`, where `A*` is now the infimum-oriented adjoint
`coadjointProcess`, whose values are the reflections of those of `adjointProcess`. -/
theorem iSup_coadjointProcess_eq_neg_concaveBracket (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (A : ConvexProcess U X) (u : U) (y : Y) :
    ⨆ v ∈ (coadjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal)
      = -(concaveBracket Bu (adjointBifun Bu Bx A.indicatorBifun) u (-y)) := by
  rw [concaveBracket_adjointBifun_indicatorBifun, coadjointProcess_eq_reflect_adjointProcess,
    eval_reflect, iSup_mem_neg, EReal.neg_iInf]
  refine iSup_congr fun v => ?_
  rw [EReal.neg_iInf]
  refine iSup_congr fun _ => ?_
  rw [map_neg (Bu u) v, _root_.EReal.coe_neg]

end ConvexProcess

end CoBracketAdjoint

section CoBracketClosure

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ}

namespace ConvexProcess

/-- **`⟨u, A* x*⟩ = cl_u ⟨Au, x*⟩`**, the infimum-oriented mirror.

The closure is now the ordinary convex closure `clFn`, because `⟨A ·, x*⟩` is convex rather than
concave (`convexFn_coBracket_arg`); in the supremum-oriented statement
`concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁` it is the concave closure `clConcave`
packaged as `partialCl₁`. As there, closedness of `A` plays no part. -/
theorem iSup_coadjointProcess_eq_clFn (A : ConvexProcess U X) (y : Y) :
    (fun u => ⨆ v ∈ (coadjointProcess Bu Bx A).eval y, ((Bu u v : ℝ) : EReal))
      = fun u => clFn (fun u' => coBracket Bx A u' y) u := by
  funext u
  have h := congrFun (concaveBracket_adjointBifun_indicatorBifun_eq_partialCl₁
    (Bu := Bu) (Bx := Bx) A (-y)) u
  simp only [partialCl₁_apply, clConcave_apply] at h
  rw [iSup_coadjointProcess_eq_neg_concaveBracket Bu Bx, h, coBracket_eq_neg_bracket_fun,
    _root_.neg_neg]

end ConvexProcess

end CoBracketClosure

end ConvexAnalysis
