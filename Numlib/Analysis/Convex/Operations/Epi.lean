/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Numlib.Analysis.Convex.Epigraph

/-!
# The function determined by a set in $E \times \mathbb{R}$

To build a convex function on $E$, one builds a convex set $F \subseteq E \times \mathbb{R}$ and
takes the function whose graph is the lower boundary of $F$:
$$(\operatorname{ofEpi} F)(x) = \inf\{\mu \in \mathbb{R} \mid (x, \mu) \in F\},$$
an infimum in $[-\infty, +\infty]$. It is $+\infty$ where the vertical section of $F$ is empty, and
$-\infty$ where the section is unbounded below. Infimal convolution, right scalar multiplication,
the convex hull of a family of functions, the image under a linear map and the lower semicontinuous
hull are all of the form $\operatorname{ofEpi} F$ for a set $F$ built from epigraphs. No structure
on $E$ is needed, except that convexity requires a real vector space. The presentation follows
[rockafellar1970convex], §5.

The equation $\operatorname{epi}(\operatorname{ofEpi} F) = F$ is false in general; only $F \subseteq
\operatorname{epi}(\operatorname{ofEpi} F)$ always holds. A set for which the equation holds is
called epi-like. The operations that matter most do not preserve this property. A sum of epigraphs
need not be an epigraph, since an infimal convolution need not attain its infimum, and neither need
the convex hull of a union of epigraphs. The modules on these operations therefore carry
epi-likeness as a hypothesis.

## Main definitions

* `ConvexAnalysis.ofEpi`: the function whose graph is the lower boundary of a set
  $F \subseteq E \times \mathbb{R}$.
* `ConvexAnalysis.epiClosure`: the closure operator $F \mapsto
  \operatorname{epi}(\operatorname{ofEpi} F)$ on subsets of $E \times \mathbb{R}$.
* `ConvexAnalysis.IsEpiLike`: a set $F \subseteq E \times \mathbb{R}$ is epi-like if it is the
  epigraph of a function.

## Main results

* `ConvexAnalysis.subset_epi_iff_le_ofEpi`: $F \subseteq \operatorname{epi} g$ if and only if
  $g \le \operatorname{ofEpi} F$.
* `ConvexAnalysis.gc_ofEpi_epi`: $\operatorname{epi}$ and $\operatorname{ofEpi}$ form an antitone
  Galois connection, whose closed sets are the epi-like sets.
* `ConvexAnalysis.ofEpi_epi`: $\operatorname{ofEpi}(\operatorname{epi} f) = f$ for every $f$.
* `ConvexAnalysis.epi_ofEpi`: $\operatorname{epi}(\operatorname{ofEpi} F) = F$ for every epi-like
  $F$.
* `ConvexAnalysis.convexFn_ofEpi`: $\operatorname{ofEpi} F$ is convex when $F$ is convex.
* `ConvexAnalysis.IsEpiLike.iInter`, `ConvexAnalysis.IsEpiLike.inter`,
  `ConvexAnalysis.IsEpiLike.union`, `ConvexAnalysis.IsEpiLike.of_isClosed`,
  `ConvexAnalysis.IsEpiLike.closure`: epi-likeness is preserved by intersections, by binary unions
  and by topological closure, and a closed set that is upward closed in the vertical direction is
  epi-like.

## Implementation notes

* The order facts about $\operatorname{ofEpi}$ are formal consequences of the Galois connection
  `ConvexAnalysis.gc_ofEpi_epi`.
-/

open Set

namespace ConvexAnalysis

section Basic

variable {E : Type*}

/-! ### The function determined by a set -/

/-- The function whose graph is the **lower boundary** of a set $F \subseteq E \times \mathbb{R}$:
$$(\operatorname{ofEpi} F)(x) = \inf\{\mu \in \mathbb{R} \mid (x, \mu) \in F\},$$
an infimum in $[-\infty, +\infty]$.

The infimum of the empty set is $+\infty$, and the infimum of a set that is unbounded below is
$-\infty$. -/
noncomputable def ofEpi (F : Set (E × ℝ)) : E → EReal :=
  fun x => ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)

variable {F G : Set (E × ℝ)} {f g : E → EReal} {x : E} {μ ν : ℝ} {z : EReal}

/-- If $(x, \mu) \in F$, then $(\operatorname{ofEpi} F)(x) \le \mu$. -/
theorem ofEpi_apply_le (h : (x, μ) ∈ F) : ofEpi F x ≤ (μ : EReal) :=
  iInf₂_le (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) μ h

/-- If $z \le \mu$ for every $\mu \in \mathbb{R}$ with $(x, \mu) \in F$, then
$z \le (\operatorname{ofEpi} F)(x)$. -/
theorem le_ofEpi (h : ∀ μ : ℝ, (x, μ) ∈ F → z ≤ (μ : EReal)) : z ≤ ofEpi F x :=
  le_iInf₂ (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) h

/-- For $z \in [-\infty, +\infty]$, $(\operatorname{ofEpi} F)(x) < z$ if and only if there is a real
$\mu < z$ with $(x, \mu) \in F$.

The infimum that defines $(\operatorname{ofEpi} F)(x)$ need not be attained. So arguments about
$\operatorname{ofEpi}$ go through this strict inequality, which does produce a witness. -/
theorem ofEpi_lt_iff : ofEpi F x < z ↔ ∃ μ : ℝ, (x, μ) ∈ F ∧ (μ : EReal) < z := by
  simp only [ofEpi, iInf_lt_iff, exists_prop]
  exact Iff.rfl

/-- **The universal property.** For $F \subseteq E \times \mathbb{R}$ and
$g : E \to [-\infty, +\infty]$,
$$F \subseteq \operatorname{epi} g \iff g \le \operatorname{ofEpi} F.$$
So $\operatorname{ofEpi} F$ is the greatest function whose epigraph contains $F$. -/
theorem subset_epi_iff_le_ofEpi : F ⊆ epi g ↔ g ≤ ofEpi F := by
  constructor
  · exact fun h y => le_ofEpi fun _ hμ => h hμ
  · rintro h ⟨y, ρ⟩ hp
    exact (h y).trans (ofEpi_apply_le hp)

/-- Every set $F \subseteq E \times \mathbb{R}$ satisfies $F \subseteq
\operatorname{epi}(\operatorname{ofEpi} F)$.

The reverse inclusion holds for epi-like $F$: see `ConvexAnalysis.epi_ofEpi`. -/
theorem subset_epi_ofEpi (F : Set (E × ℝ)) : F ⊆ epi (ofEpi F) :=
  subset_epi_iff_le_ofEpi.2 le_rfl

/-- $\operatorname{ofEpi}$ is antitone: $F \subseteq G$ implies $\operatorname{ofEpi} G \le
\operatorname{ofEpi} F$. -/
theorem ofEpi_mono (h : F ⊆ G) : ofEpi G ≤ ofEpi F :=
  subset_epi_iff_le_ofEpi.1 (h.trans (subset_epi_ofEpi G))

/-- $(\operatorname{ofEpi} F)(x) = +\infty$ if and only if $(x, \mu) \notin F$ for every
$\mu \in \mathbb{R}$. -/
theorem ofEpi_eq_top_iff : ofEpi F x = ⊤ ↔ ∀ μ : ℝ, (x, μ) ∉ F := by
  rw [← not_iff_not, ← Ne, ← lt_top_iff_ne_top, ofEpi_lt_iff]
  simp

/-- The function determined by the empty set is the constant $+\infty$. -/
@[simp] theorem ofEpi_empty : ofEpi (∅ : Set (E × ℝ)) = ⊤ :=
  funext fun _ => ofEpi_eq_top_iff.2 fun _ => notMem_empty _

/-- The function determined by all of $E \times \mathbb{R}$ is the constant $-\infty$. -/
@[simp] theorem ofEpi_univ : ofEpi (univ : Set (E × ℝ)) = ⊥ :=
  funext fun _ =>
    le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ofEpi_apply_le (mem_univ (_, r)))

/-- Every function $f : E \to [-\infty, +\infty]$ satisfies
$\operatorname{ofEpi}(\operatorname{epi} f) = f$.

No hypothesis is needed: a vertical section of an epigraph is empty, all of $\mathbb{R}$, or a
closed half-line $[c, \infty)$, and in each case its infimum is the value of $f$. -/
@[simp] theorem ofEpi_epi (f : E → EReal) : ofEpi (epi f) = f := by
  refine le_antisymm (fun x => ?_) (subset_epi_iff_le_ofEpi.1 subset_rfl)
  rcases eq_top_or_lt_top (f x) with h | h
  · rw [h]; exact le_top
  by_cases hb : f x = ⊥
  · rw [hb, le_bot_iff]
    exact le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ =>
      ofEpi_apply_le (mk_mem_epi.2 (hb.le.trans bot_le)))
  · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb h
    exact hr ▸ ofEpi_apply_le (mk_mem_epi.2 hr.le)

/-- If $\operatorname{epi} f = F$, then $f = \operatorname{ofEpi} F$. -/
theorem eq_ofEpi_of_epi_eq (h : epi f = F) : f = ofEpi F := by rw [← h, ofEpi_epi]

/-- If the vertical sections of $F$ and $G$ over $x$ agree, then $(\operatorname{ofEpi} F)(x) =
(\operatorname{ofEpi} G)(x)$. -/
theorem ofEpi_apply_congr (h : ∀ μ : ℝ, (x, μ) ∈ F ↔ (x, μ) ∈ G) : ofEpi F x = ofEpi G x := by
  have hs : {μ : ℝ | (x, μ) ∈ F} = {μ : ℝ | (x, μ) ∈ G} := Set.ext h
  simp only [ofEpi, hs]

/-- The effective domain of $\operatorname{ofEpi} F$ is the projection of $F$ onto $E$.

So $(\operatorname{ofEpi} F)(x) < +\infty$ if and only if the vertical section of $F$ over $x$
is nonempty. No hypothesis on $F$ is needed. -/
theorem convexDom_ofEpi (F : Set (E × ℝ)) : convexDom (ofEpi F) = Prod.fst '' F := by
  ext x
  constructor
  · intro hx
    by_contra hx'
    exact absurd (ofEpi_eq_top_iff.2 fun μ hμ => hx' ⟨(x, μ), hμ, rfl⟩) hx.ne
  · rintro ⟨⟨w, μ⟩, hw, rfl⟩
    exact lt_of_le_of_lt (ofEpi_apply_le hw) (EReal.coe_lt_top μ)

/-!
### The Galois connection between sets and functions

The map $\operatorname{ofEpi}$ and the map $\operatorname{epi}$ form an antitone adjunction. The
order dual on the side of the functions turns it into a monotone `GaloisConnection` of Mathlib.
-/

open OrderDual in
/-- The maps $F \mapsto \operatorname{ofEpi} F$, from subsets of $E \times \mathbb{R}$ to the order
dual of $E \to [-\infty, +\infty]$, and $g \mapsto \operatorname{epi} g$ in the other direction,
form a **Galois connection**. This restates `ConvexAnalysis.subset_epi_iff_le_ofEpi`. -/
theorem gc_ofEpi_epi :
    GaloisConnection (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  fun _ _ => subset_epi_iff_le_ofEpi.symm

open OrderDual in
/-- The Galois connection `ConvexAnalysis.gc_ofEpi_epi` is a **Galois insertion**, because
$\operatorname{ofEpi}(\operatorname{epi} f) = f$ for every $f$. -/
noncomputable def gi_ofEpi_epi :
    GaloisInsertion (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  gc_ofEpi_epi.toGaloisInsertion fun g => le_of_eq (by simp [ofEpi_epi])

/-- The **closure operator** $F \mapsto \operatorname{epi}(\operatorname{ofEpi} F)$ on subsets of
$E \times \mathbb{R}$, from the Galois connection `ConvexAnalysis.gc_ofEpi_epi`. Its closed sets
are the epi-like sets. -/
noncomputable def epiClosure : ClosureOperator (Set (E × ℝ)) := gc_ofEpi_epi.closureOperator

/-- The closure operator `ConvexAnalysis.epiClosure` maps $F$ to
$\operatorname{epi}(\operatorname{ofEpi} F)$. -/
@[simp] theorem epiClosure_apply (F : Set (E × ℝ)) : epiClosure F = epi (ofEpi F) := rfl

/-- The map $f \mapsto \operatorname{epi} f$ is injective on functions $E \to [-\infty, +\infty]$.
-/
theorem epi_injective : Function.Injective (epi : (E → EReal) → Set (E × ℝ)) :=
  fun _ _ h => by simpa using congrArg ofEpi h

/-! ### Sets that are epigraphs -/

/-- A set $F \subseteq E \times \mathbb{R}$ is **epi-like** if $F = \operatorname{epi} f$ for some
$f : E \to [-\infty, +\infty]$.

Equivalently (`ConvexAnalysis.isEpiLike_iff_forall`), every vertical section
$\{\mu \mid (x, \mu) \in F\}$ is upward closed and contains its infimum when it is bounded
below; that is, it is empty, all of $\mathbb{R}$, or a closed half-line $[c, \infty)$. Both
conditions are needed: $\{p \mid p_2 > 0\}$ is upward closed but does not attain its infimum,
and $\{(0, 0)\}$ attains it but is not upward closed. The function $f$ is always
$\operatorname{ofEpi} F$ (`ConvexAnalysis.isEpiLike_iff`). -/
def IsEpiLike (F : Set (E × ℝ)) : Prop := ∃ f : E → EReal, F = epi f

/-- Every epigraph is epi-like. -/
@[simp] theorem isEpiLike_epi (f : E → EReal) : IsEpiLike (epi f) := ⟨f, rfl⟩

/-- For an epi-like set $F$, $\operatorname{epi}(\operatorname{ofEpi} F) = F$.

So on epi-like sets, $\operatorname{ofEpi}$ and $\operatorname{epi}$ are inverse to each other.
This is the purpose of the notion. -/
@[simp] theorem epi_ofEpi (h : IsEpiLike F) : epi (ofEpi F) = F := by
  obtain ⟨f, rfl⟩ := h
  rw [ofEpi_epi]

/-- A set $F$ is epi-like if and only if $\operatorname{epi}(\operatorname{ofEpi} F) = F$. -/
theorem isEpiLike_iff : IsEpiLike F ↔ epi (ofEpi F) = F :=
  ⟨epi_ofEpi, fun h => ⟨ofEpi F, h.symm⟩⟩

/-- A set is epi-like if and only if it is closed for the closure operator
`ConvexAnalysis.epiClosure`. -/
theorem isEpiLike_iff_isClosed {F : Set (E × ℝ)} : IsEpiLike F ↔ epiClosure.IsClosed F :=
  isEpiLike_iff

/-- An epi-like set is upward closed in the vertical direction: if $(x, \mu) \in F$ and
$\mu \le \nu$, then $(x, \nu) \in F$. -/
theorem IsEpiLike.mem_of_le (h : IsEpiLike F) (hμ : (x, μ) ∈ F) (hμν : μ ≤ ν) : (x, ν) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  exact mk_mem_epi.2 ((mk_mem_epi.1 hμ).trans (by exact_mod_cast hμν))

/-- An epi-like set contains the infimum of a vertical section: if $(x, \nu) \in F$ for every
$\nu > \mu$, then $(x, \mu) \in F$. -/
theorem IsEpiLike.mem_of_forall_lt (h : IsEpiLike F) (hμ : ∀ ν : ℝ, μ < ν → (x, ν) ∈ F) :
    (x, μ) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  refine mk_mem_epi.2 (EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_)
  replace hq := EReal.coe_lt_coe_iff.1 hq
  obtain ⟨ρ, hμρ, hρq⟩ := exists_between hq
  exact lt_of_le_of_lt (mk_mem_epi.1 (hμ ρ hμρ)) (by exact_mod_cast hρq)

/-- **The criterion for epi-likeness that one checks in practice.** A set
$F \subseteq E \times \mathbb{R}$ is epi-like if it satisfies the following two conditions: if
$(x, \mu) \in F$ and $\mu \le \nu$, then $(x, \nu) \in F$; and if $(x, \nu) \in F$ for every
$\nu > \mu$, then $(x, \mu) \in F$. -/
theorem isEpiLike_of_forall
    (hmono : ∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F)
    (hbelow : ∀ (x : E) (μ : ℝ), (∀ ν : ℝ, μ < ν → (x, ν) ∈ F) → (x, μ) ∈ F) :
    IsEpiLike F := by
  refine isEpiLike_iff.2 (subset_antisymm ?_ (subset_epi_ofEpi F))
  rintro ⟨y, ρ⟩ hp
  refine hbelow y ρ fun σ hσ => ?_
  have hlt : ofEpi F y < (σ : EReal) :=
    lt_of_le_of_lt (mk_mem_epi.1 hp) (by exact_mod_cast hσ)
  obtain ⟨τ, hτF, hτσ⟩ := ofEpi_lt_iff.1 hlt
  exact hmono y τ σ hτF (by exact_mod_cast hτσ.le)

/-- A set $F \subseteq E \times \mathbb{R}$ is epi-like if and only if it satisfies the following
two conditions: if $(x, \mu) \in F$ and $\mu \le \nu$, then $(x, \nu) \in F$; and if
$(x, \nu) \in F$ for every $\nu > \mu$, then $(x, \mu) \in F$. -/
theorem isEpiLike_iff_forall :
    IsEpiLike F ↔ (∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F) ∧
      ∀ (x : E) (μ : ℝ), (∀ ν : ℝ, μ < ν → (x, ν) ∈ F) → (x, μ) ∈ F :=
  ⟨fun h => ⟨fun _ _ _ hμ hμν => h.mem_of_le hμ hμν, fun _ _ hμ => h.mem_of_forall_lt hμ⟩,
    fun h => isEpiLike_of_forall h.1 h.2⟩

/-- An intersection of a family of epi-like sets is epi-like. It is the epigraph of the pointwise
supremum. -/
theorem IsEpiLike.iInter {ι : Sort*} {F : ι → Set (E × ℝ)} (h : ∀ i, IsEpiLike (F i)) :
    IsEpiLike (⋂ i, F i) := by
  choose f hf using h
  refine ⟨⨆ i, f i, ?_⟩
  ext p
  simp [hf, epi, iSup_apply, iSup_le_iff]

/-- The intersection of two epi-like sets is epi-like. -/
theorem IsEpiLike.inter (hF : IsEpiLike F) (hG : IsEpiLike G) : IsEpiLike (F ∩ G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  refine ⟨f ⊔ g, ?_⟩
  ext p
  simp [epi, sup_le_iff]

/-- The union of two epi-like sets is epi-like. It is the epigraph of the pointwise minimum.

The proof uses that the order of $[-\infty, +\infty]$ is linear. The result fails for infinite
unions: the union of the epigraphs of the constant functions $1/(n + 1)$, $n \in \mathbb{N}$, is
not an epigraph. -/
theorem IsEpiLike.union (hF : IsEpiLike F) (hG : IsEpiLike G) : IsEpiLike (F ∪ G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  refine ⟨f ⊓ g, ?_⟩
  ext p
  simp [epi]

end Basic

/-! ### Convexity of the function determined by a set -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Let $E$ be a real vector space. If $F \subseteq E \times \mathbb{R}$ is convex, then the
function $\operatorname{ofEpi} F$ whose graph is the lower boundary of $F$ is convex.

The proof uses `ConvexAnalysis.convexFn_iff_forall_lt`, which asks only for strict upper bounds,
because a non-strict upper bound gives no witness in $F$. -/
theorem convexFn_ofEpi {F : Set (E × ℝ)} (hF : Convex ℝ F) : ConvexFn (ofEpi F) := by
  rw [convexFn_iff_forall_lt]
  intro x y a b ha hb hab α β hx hy
  obtain ⟨μ, hμF, hμα⟩ := ofEpi_lt_iff.1 hx
  obtain ⟨ν, hνF, hνβ⟩ := ofEpi_lt_iff.1 hy
  have hcombo : (a • x + b • y, a * μ + b * ν) ∈ F := by
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hF hμF hνF ha.le hb.le hab
  refine lt_of_le_of_lt (ofEpi_apply_le hcombo) ?_
  have h1 : a * μ < a * α := mul_lt_mul_of_pos_left (by exact_mod_cast hμα) ha
  have h2 : b * ν < b * β := mul_lt_mul_of_pos_left (by exact_mod_cast hνβ) hb
  exact_mod_cast add_lt_add h1 h2

end Module

/-! ### Epi-likeness and topology -/

section Topology

variable {E : Type*} [TopologicalSpace E] {F : Set (E × ℝ)}

/-- Let $E$ be a topological space, and let $F \subseteq E \times \mathbb{R}$ be closed and upward
closed in the vertical direction: $(x, \mu) \in F$ and $\mu \le \nu$ imply $(x, \nu) \in F$.
Then $F$ is epi-like.

Closedness gives the attainment half of epi-likeness, since a closed vertical section contains
its infimum. It does not give the other half: $\{(0, 0)\}$ is closed and is not an epigraph. -/
theorem IsEpiLike.of_isClosed
    (hmono : ∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F) (hF : IsClosed F) :
    IsEpiLike F := by
  refine isEpiLike_of_forall hmono fun x μ hμ => ?_
  have hcont : Continuous fun ν : ℝ => (x, ν) := continuous_const.prodMk continuous_id
  have hclosed : IsClosed ((fun ν : ℝ => (x, ν)) ⁻¹' F) := hF.preimage hcont
  have hsub : Ioi μ ⊆ (fun ν : ℝ => (x, ν)) ⁻¹' F := fun ν hν => hμ ν hν
  have hmem : μ ∈ closure (Ioi μ) := by rw [closure_Ioi]; exact le_refl μ
  have hmem' := closure_mono hsub hmem
  rwa [hclosed.closure_eq] at hmem'

variable [AddZeroClass E] [ContinuousAdd E]

/-- Let $E$ be a topological space with a continuous addition that has a zero element. Then the
closure of an epi-like set $F \subseteq E \times \mathbb{R}$ is epi-like.

This is what the lower semicontinuous hull `ConvexAnalysis.lscHull`, defined as
$\operatorname{ofEpi}$ of the closure of $\operatorname{epi} f$, needs to satisfy
$\operatorname{epi}(\operatorname{lscHull} f) = \operatorname{cl}(\operatorname{epi} f)$. -/
theorem IsEpiLike.closure (h : IsEpiLike F) : IsEpiLike (_root_.closure F) := by
  refine IsEpiLike.of_isClosed (fun x μ ν hμ hμν => ?_) isClosed_closure
  have hcont : Continuous fun p : E × ℝ => p + ((0 : E), ν - μ) :=
    continuous_id.add continuous_const
  have himg : (fun p : E × ℝ => p + ((0 : E), ν - μ)) '' F ⊆ F := by
    rintro _ ⟨⟨z, ρ⟩, hz, rfl⟩
    simpa using h.mem_of_le hz (by linarith : ρ ≤ ρ + (ν - μ))
  have hmem := image_closure_subset_closure_image hcont (mem_image_of_mem _ hμ)
  have hmem' := closure_mono himg hmem
  simpa using hmem'

end Topology

end ConvexAnalysis
