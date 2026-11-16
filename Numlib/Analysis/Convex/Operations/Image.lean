/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# Images and inverse images of convex functions under a linear map

Let $A \colon E \to G$ be a linear map between real vector spaces, and consider functions with
values in $[-\infty, +\infty]$. The **inverse image** of $g \colon G \to [-\infty, +\infty]$ is
$gA = g \circ A$, and its epigraph is a preimage of the epigraph of $g$. The **image** of
$f \colon E \to [-\infty, +\infty]$ is $$(Af)(y) = \inf \{ f(x) \mid Ax = y \},$$ which is $+\infty$
off the range of $A$. Both operations preserve convexity, as in [rockafellar1970convex], §5. The
infimum that defines $Af$ need not be attained. For this reason $Af$ is the function determined by
the set $\{(Ax, \mu) \mid (x, \mu) \in \operatorname{epi} f\}$, but this set need not be the
epigraph of $Af$.

The two operations form a monotone Galois connection: $g \le Af$ if and only if $gA \le f$. This
gives the monotonicity of both operations, the inequalities $(Af)A \le f$ and $g \le A(gA)$, and,
for surjective $A$, the identity $A(gA) = g$. Partial minimization $y \mapsto \inf_z h(y, z)$ is the
image under a projection, so it preserves convexity too. The module also treats the reflection
$x \mapsto f(-x)$, the most frequent inverse image.

## Main definitions

* `ConvexAnalysis.mapLin`: the image $Af$ of $f$ under $A$.
* `ConvexAnalysis.compLin`: the inverse image $gA$ of $g$ under $A$.
* `ConvexAnalysis.reflectFst`: the linear map $(x, \mu) \mapsto (-x, \mu)$ of $E \times \mathbb{R}$.

## Main results

* `ConvexAnalysis.convexFn_compLin`, `ConvexAnalysis.convexFn_mapLin`: the inverse image and the
  image of a convex function are convex.
* `ConvexAnalysis.gc_compLin_mapLin`: $g \mapsto gA$ and $f \mapsto Af$ form a Galois connection,
  that is, $gA \le f$ if and only if $g \le Af$.
* `ConvexAnalysis.mapLin_eq_ofEpi`: $Af$ is the function determined by the image of
  $\operatorname{epi} f$ under $(x, \mu) \mapsto (Ax, \mu)$.
* `ConvexAnalysis.epi_mapLin`: if that image is an epigraph, then it is the epigraph of $Af$.
* `ConvexAnalysis.exists_epi_mapLin_ne_image`: in general, that image is not the epigraph of $Af$.
* `ConvexAnalysis.convexFn_iInf_right`: if $h$ is jointly convex, then $y \mapsto \inf_z h(y, z)$ is
  convex.
* `ConvexAnalysis.ConvexFn.comp_affine`: if $g$ is convex, then $x \mapsto g(Ax + b)$ is convex.
* `ConvexAnalysis.ConvexFn.slice_left`, `ConvexAnalysis.ConvexFn.slice_right`: fixing one variable
  of a jointly convex function gives a convex function.
* `ConvexAnalysis.epi_comp_neg`, `ConvexAnalysis.convexDom_comp_neg`,
  `ConvexAnalysis.ProperConvex.comp_neg`: the epigraph, the effective domain and the properness of
  $x \mapsto f(-x)$.

## Implementation notes

* The Galois connection is monotone: it needs no `OrderDual`, unlike `ConvexAnalysis.gc_ofEpi_epi`.
  For surjective $A$ it is a `GaloisCoinsertion` (`ConvexAnalysis.gci_compLin_mapLin`).
* Convexity of $Af$ is proved through `ConvexAnalysis.mapLin_eq_ofEpi`: a linear image of a convex
  set is convex, and the function that a convex set determines is convex.
* `ConvexAnalysis.epi_mapLin` needs the hypothesis `ConvexAnalysis.IsEpiLike` on the image of the
  epigraph. This hypothesis is exactly the attainment of the infimum that defines $Af$ where it is
  finite.
-/

open Set

namespace ConvexAnalysis

section Module

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]

/-! ### The two operations -/

/-- The **image** of $f \colon E \to [-\infty, +\infty]$ under a linear map $A \colon E \to G$ is
the function $$(Af)(y) = \inf \{ f(x) \mid x \in E,\ Ax = y \}.$$ The infimum is over the fibre
of $A$ above $y$, so $(Af)(y) = +\infty$ when $y$ is not in the range of $A$.

The infimum is in general not attained. -/
noncomputable def mapLin (A : E →ₗ[ℝ] G) (f : E → EReal) : G → EReal :=
  fun y => ⨅ x ∈ {x | A x = y}, f x

/-- The **inverse image** of $g \colon G \to [-\infty, +\infty]$ under a linear map
$A \colon E \to G$ is the function $(gA)(x) = g(Ax)$. -/
def compLin (g : G → EReal) (A : E →ₗ[ℝ] G) : E → EReal := g ∘ A

/-- The linear map $(x, \mu) \mapsto (Ax, \mu)$ from $E \times \mathbb{R}$ to $G \times \mathbb{R}$.
The epigraph of $gA$ is the preimage of the epigraph of $g$ under this map. -/
abbrev prodMapId (A : E →ₗ[ℝ] G) : E × ℝ →ₗ[ℝ] G × ℝ :=
  A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

variable {A : E →ₗ[ℝ] G} {f : E → EReal} {g : G → EReal} {x : E} {y : G} {z : EReal}

/-- The inverse image $gA$ takes the value $g(Ax)$ at $x$. -/
@[simp] theorem compLin_apply (g : G → EReal) (A : E →ₗ[ℝ] G) (x : E) :
    compLin g A x = g (A x) := rfl

/-! ### The infimum that defines the image -/

/-- If $Ax = y$, then $(Af)(y) \le f(x)$. -/
theorem mapLin_le (h : A x = y) : mapLin A f y ≤ f x :=
  iInf₂_le (f := fun z (_ : z ∈ {z | A z = y}) => f z) x h

/-- If $z \le f(x)$ for every $x$ with $Ax = y$, then $z \le (Af)(y)$. -/
theorem le_mapLin (h : ∀ x : E, A x = y → z ≤ f x) : z ≤ mapLin A f y :=
  le_iInf₂ (f := fun z (_ : z ∈ {z | A z = y}) => f z) h

/-- For $z \in [-\infty, +\infty]$, $(Af)(y) < z$ if and only if there is an $x$ with $Ax = y$ and
$f(x) < z$.

This lemma extracts a witness from a strict inequality, as for `ConvexAnalysis.ofEpi`. -/
theorem mapLin_lt_iff : mapLin A f y < z ↔ ∃ x : E, A x = y ∧ f x < z := by
  simp only [mapLin, iInf_lt_iff, exists_prop]
  exact Iff.rfl

/-- If $y$ is not in the range of $A$, then $(Af)(y) = +\infty$, because the infimum is over the
empty set. -/
theorem mapLin_of_notMem_range (hy : y ∉ Set.range A) : mapLin A f y = ⊤ :=
  top_le_iff.1 (le_mapLin fun x hx => absurd ⟨x, hx⟩ hy)

/-! ### The Galois connection between the two operations -/

/-- The **universal property of the image**: for all $g \colon G \to [-\infty, +\infty]$ and
$f \colon E \to [-\infty, +\infty]$, $$gA \le f \iff g \le Af.$$ That is, $g \mapsto gA$ and
$f \mapsto Af$ form a monotone Galois connection, and $f \mapsto Af$ is the right adjoint. -/
theorem gc_compLin_mapLin (A : E →ₗ[ℝ] G) :
    GaloisConnection (fun g : G → EReal => compLin g A) (fun f : E → EReal => mapLin A f) :=
  fun _ _ =>
    ⟨fun h _ => le_mapLin fun x hx => hx ▸ h x, fun h x => (h (A x)).trans (mapLin_le rfl)⟩

/-- $g \le Af$ if and only if $gA \le f$. -/
theorem le_mapLin_iff : g ≤ mapLin A f ↔ compLin g A ≤ f :=
  (gc_compLin_mapLin A g f).symm

/-- The image is monotone: if $f_1 \le f_2$, then $Af_1 \le Af_2$. -/
theorem mapLin_mono {f₁ f₂ : E → EReal} (h : f₁ ≤ f₂) : mapLin A f₁ ≤ mapLin A f₂ :=
  (gc_compLin_mapLin A).monotone_u h

/-- The inverse image is monotone: if $g_1 \le g_2$, then $g_1 A \le g_2 A$. -/
theorem compLin_mono {g₁ g₂ : G → EReal} (h : g₁ ≤ g₂) : compLin g₁ A ≤ compLin g₂ A :=
  fun x => h (A x)

/-- The counit of the Galois connection: $(Af)A \le f$, that is, $(Af)(Ax) \le f(x)$ for every
$x \in E$. -/
theorem compLin_mapLin_le (A : E →ₗ[ℝ] G) (f : E → EReal) : compLin (mapLin A f) A ≤ f :=
  (gc_compLin_mapLin A).l_u_le f

/-- The unit of the Galois connection: $g \le A(gA)$. Equality holds at the points of the range of
$A$, and $A(gA)$ is $+\infty$ off it. -/
theorem le_mapLin_compLin (A : E →ₗ[ℝ] G) (g : G → EReal) : g ≤ mapLin A (compLin g A) :=
  (gc_compLin_mapLin A).le_u_l g

/-- If $A$ is surjective, then $A(gA) = g$. -/
theorem mapLin_compLin (hA : Function.Surjective A) (g : G → EReal) :
    mapLin A (compLin g A) = g :=
  le_antisymm (fun y => by
    obtain ⟨x, rfl⟩ := hA y
    exact mapLin_le rfl) (le_mapLin_compLin A g)

/-- If $A$ is surjective, then the Galois connection between $g \mapsto gA$ and $f \mapsto Af$ is a
Galois coinsertion. -/
noncomputable def gci_compLin_mapLin (hA : Function.Surjective A) :
    GaloisCoinsertion (fun g : G → EReal => compLin g A) (fun f : E → EReal => mapLin A f) :=
  (gc_compLin_mapLin A).toGaloisCoinsertion fun g => le_of_eq (mapLin_compLin hA g)

/-! ### Effective domains -/

/-- The effective domain of the inverse image is the preimage of the effective domain:
$\operatorname{dom}(gA) = A^{-1}(\operatorname{dom} g)$. -/
theorem convexDom_compLin (g : G → EReal)
    (A : E →ₗ[ℝ] G) : convexDom (compLin g A) = A ⁻¹' convexDom g := rfl

/-- If $A$ is surjective, then $gA$ is proper if and only if $g$ is proper.

Surjectivity is needed for both directions. Without it, $gA$ can be proper while $g$ is
$-\infty$ off the range of $A$, and $g$ can be proper while the range of $A$ misses all points
where $g$ is finite. -/
theorem properConvex_compLin_of_surjective (hA : Function.Surjective A) :
    ProperConvex (compLin g A) ↔ ProperConvex g := by
  constructor
  · rintro ⟨⟨x, hx⟩, hb⟩
    refine ⟨⟨A x, hx⟩, fun z => ?_⟩
    obtain ⟨w, rfl⟩ := hA z
    exact hb w
  · rintro ⟨⟨z, hz⟩, hb⟩
    obtain ⟨w, rfl⟩ := hA z
    exact ⟨⟨w, hz⟩, fun x => hb (A x)⟩

/-- The effective domain of the image is the image of the effective domain:
$\operatorname{dom}(Af) = A(\operatorname{dom} f)$. No convexity is needed. -/
theorem convexDom_mapLin (A : E →ₗ[ℝ] G)
    (f : E → EReal) : convexDom (mapLin A f) = A '' convexDom f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hf⟩ := mapLin_lt_iff.1 hy
    exact ⟨x, hf, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact mapLin_lt_iff.2 ⟨x, rfl, hx⟩

/-! ### Epigraphs, and convexity in both directions -/

/-- The epigraph of the inverse image is the preimage of the epigraph: $$\operatorname{epi}(gA) = \{
(x, \mu) \mid (Ax, \mu) \in \operatorname{epi} g \}.$$
-/
theorem epi_compLin (g : G → EReal) (A : E →ₗ[ℝ] G) :
    epi (compLin g A) = prodMapId A ⁻¹' epi g := rfl

/-- Let $A \colon E \to G$ be a linear map. If $g \colon G \to [-\infty, +\infty]$ is convex, then
its inverse image $gA$ is convex.

The epigraph of $gA$ is the preimage of the convex set $\operatorname{epi} g$ under a linear
map. -/
theorem convexFn_compLin (A : E →ₗ[ℝ] G) (hg : ConvexFn g) : ConvexFn (compLin g A) := by
  refine ⟨?_⟩
  rw [epi_compLin]
  exact hg.convex_epi.linear_preimage _

/-- **Precomposition with an affine map preserves convexity.** Let $A \colon E \to G$ be a linear
map and let $b \in G$. If $g \colon G \to [-\infty, +\infty]$ is convex, then
$x \mapsto g(Ax + b)$ is convex on $E$. -/
theorem ConvexFn.comp_affine (hg : ConvexFn g) (A : E →ₗ[ℝ] G) (b : G) :
    ConvexFn (fun x : E => g (A x + b)) := by
  have heq : (fun x : E => g (A x + b)) = compLin (fun y => g (b + y)) A := by
    funext x
    simp [compLin, add_comm]
  rw [heq]
  exact convexFn_compLin A (hg.comp_add_left b)

/-- Let $A \colon E \to G$ be a linear map and let $f \colon E \to [-\infty, +\infty]$. Then $Af$ is
the function determined by the set $\{ (Ax, \mu) \mid (x, \mu) \in \operatorname{epi} f \}$:
$$(Af)(y) = \inf \{ \mu \in \mathbb{R} \mid \text{there is } x \in E \text{ with } Ax = y \text{
and } f(x) \le \mu \}.$$

This is an equality of functions. The corresponding equality of sets,
`ConvexAnalysis.epi_mapLin`, needs a hypothesis. The function determined by a set is
`ConvexAnalysis.ofEpi`. -/
theorem mapLin_eq_ofEpi (A : E →ₗ[ℝ] G) (f : E → EReal) :
    mapLin A f = ofEpi (A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f) := by
  funext y
  refine le_antisymm (le_ofEpi fun μ hμ => ?_) (le_mapLin fun x hx => ?_)
  · obtain ⟨⟨x, ν⟩, hx, hxy⟩ := hμ
    have h1 : A x = y := congrArg Prod.fst hxy
    have h2 : ν = μ := congrArg Prod.snd hxy
    exact (mapLin_le h1).trans (h2 ▸ (mk_mem_epi.1 hx))
  · conv_rhs => rw [← ofEpi_epi f]
    exact le_ofEpi fun μ hμ => ofEpi_apply_le ⟨(x, μ), hμ, by rw [LinearMap.prodMap_apply, hx]; rfl⟩

/-- Let $A \colon E \to G$ be a linear map. If $f \colon E \to [-\infty, +\infty]$ is convex, then
its image $Af$ is convex.

The image of $\operatorname{epi} f$ under $(x, \mu) \mapsto (Ax, \mu)$ is convex, and the
function that a convex set determines is convex (`ConvexAnalysis.mapLin_eq_ofEpi`). -/
theorem convexFn_mapLin (A : E →ₗ[ℝ] G) (hf : ConvexFn f) : ConvexFn (mapLin A f) := by
  rw [mapLin_eq_ofEpi]
  exact convexFn_ofEpi (hf.convex_epi.linear_image _)

/-- If the image of $\operatorname{epi} f$ under $(x, \mu) \mapsto (Ax, \mu)$ is the epigraph of
some function, then it is the epigraph of $Af$: $$\operatorname{epi}(Af) = \{ (Ax, \mu) \mid (x,
\mu) \in \operatorname{epi} f \}.$$ The hypothesis says that the infimum that defines $Af$ is
attained wherever it is finite. -/
theorem epi_mapLin (h : IsEpiLike (A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f)) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  rw [mapLin_eq_ofEpi]
  exact epi_ofEpi h

/-! ### Indicator functions -/

/-- The image of the indicator function of $s \subseteq E$ is the indicator function of the image
set: $A\,\delta(\cdot \mid s) = \delta(\cdot \mid A(s))$. -/
theorem mapLin_indicatorFn (A : E →ₗ[ℝ] G) (s : Set E) :
    mapLin A (indicatorFn s) = indicatorFn (A '' s) := by
  have hnonneg : ∀ x : E, (0 : EReal) ≤ indicatorFn s x := by
    intro x; by_cases hx : x ∈ s <;> simp [hx]
  funext y
  by_cases hy : y ∈ A '' s
  · obtain ⟨x, hx, rfl⟩ := hy
    have hmem : A x ∈ A '' s := ⟨x, hx, rfl⟩
    rw [indicatorFn_of_mem hmem]
    refine le_antisymm ?_ (le_mapLin fun z _ => hnonneg z)
    calc mapLin A (indicatorFn s) (A x) ≤ indicatorFn s x := mapLin_le rfl
      _ = 0 := indicatorFn_of_mem hx
  · rw [indicatorFn_of_notMem hy]
    refine le_antisymm le_top (le_mapLin fun z hz => ?_)
    exact le_of_eq (indicatorFn_of_notMem fun hzs => hy ⟨z, hzs, hz⟩).symm

/-- The inverse image of the indicator function of $s \subseteq G$ is the indicator function of the
preimage: $\delta(\cdot \mid s) A = \delta(\cdot \mid A^{-1}(s))$. -/
theorem compLin_indicatorFn (A : E →ₗ[ℝ] G) (s : Set G) :
    compLin (indicatorFn s) A = indicatorFn (A ⁻¹' s) := by
  funext x
  by_cases hx : A x ∈ s <;> simp [hx, Set.mem_preimage]

/-! ### The hypothesis of `ConvexAnalysis.epi_mapLin` is not removable -/

/-- **The image of an epigraph need not be an epigraph.** There are a convex function
$f \colon \mathbb{R} \to [-\infty, +\infty]$ and a linear map
$A \colon \mathbb{R} \to \mathbb{R}$ such that $\operatorname{epi}(Af)$ is not the image of
$\operatorname{epi} f$ under $(x, \mu) \mapsto (Ax, \mu)$.

The example is $A = 0$ and $f(x) = x$ for $x > 0$, $f(x) = +\infty$ otherwise. Then
$(Af)(0) = \inf \{ x \mid x > 0 \} = 0$ is not attained. The point $(0, 0)$ is in
$\operatorname{epi}(Af)$, but not in the image of $\operatorname{epi} f$, which is
$\{0\} \times (0, \infty)$. -/
theorem exists_epi_mapLin_ne_image :
    ∃ (f : ℝ → EReal) (A : ℝ →ₗ[ℝ] ℝ), ConvexFn f ∧
      epi (mapLin A f) ≠ A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  refine ⟨ConvexAnalysis.convexRestrict (Ioi 0) (fun x => (x : EReal)), 0, ?_, ?_⟩
  · refine convexFn_of_epi_combo fun u v μ ν hu hv a b ha hb hab => ?_
    have hu0 : u ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [ConvexAnalysis.convexRestrict_of_notMem h] at hu
      exact absurd hu (not_le.2 (EReal.coe_lt_top μ))
    have hv0 : v ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [ConvexAnalysis.convexRestrict_of_notMem h] at hv
      exact absurd hv (not_le.2 (EReal.coe_lt_top ν))
    rw [ConvexAnalysis.convexRestrict_of_mem hu0] at hu
    rw [ConvexAnalysis.convexRestrict_of_mem hv0] at hv
    have hu0' : (0 : ℝ) < u := hu0
    have hv0' : (0 : ℝ) < v := hv0
    have huμ : u ≤ μ := by exact_mod_cast hu
    have hvν : v ≤ ν := by exact_mod_cast hv
    have hpos : a • u + b • v ∈ Ioi (0 : ℝ) := by
      change (0 : ℝ) < a • u + b • v
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · nlinarith
    rw [ConvexAnalysis.convexRestrict_of_mem hpos]
    have hle : a • u + b • v ≤ a * μ + b * ν := by
      simp only [smul_eq_mul]
      nlinarith
    exact_mod_cast hle
  · intro hcontra
    set f : ℝ → EReal := ConvexAnalysis.convexRestrict (Ioi 0) (fun x => (x : EReal)) with hf
    have hmem : ((0 : ℝ), (0 : ℝ)) ∈ epi (mapLin (0 : ℝ →ₗ[ℝ] ℝ) f) := by
      refine mk_mem_epi.2 (EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_)
      replace hq := EReal.coe_lt_coe_iff.1 hq
      refine lt_of_le_of_lt (mapLin_le (x := q / 2) (by simp)) ?_
      have hq2 : q / 2 ∈ Ioi (0 : ℝ) := by change (0 : ℝ) < q / 2; linarith
      rw [hf, ConvexAnalysis.convexRestrict_of_mem hq2]
      exact_mod_cast (by linarith : q / 2 < q)
    rw [hcontra] at hmem
    obtain ⟨⟨u, μ⟩, hu, huv⟩ := hmem
    have hu' : f u ≤ (μ : EReal) := hu
    have h2 : μ = 0 := congrArg Prod.snd huv
    rw [h2] at hu'
    have hu0 : u ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [hf, ConvexAnalysis.convexRestrict_of_notMem h] at hu'
      exact absurd hu' (not_le.2 (EReal.coe_lt_top 0))
    rw [hf, ConvexAnalysis.convexRestrict_of_mem hu0] at hu'
    exact absurd (by exact_mod_cast hu' : u ≤ (0 : ℝ)) (not_le.2 hu0)

end Module

/-!
### Reflecting the argument

The function $x \mapsto f(-x)$ is the inverse image `ConvexAnalysis.compLin f (-LinearMap.id)`. The
results below state the reflection in the forms in which it is used.
-/

section Reflection

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable (E) in
/-- The reflection $(x, \mu) \mapsto (-x, \mu)$ of $E \times \mathbb{R}$, as a linear map. It
carries $\operatorname{epi} f$ to $\operatorname{epi}(x \mapsto f(-x))$. It is the horizontal
counterpart of the vertical scaling `ConvexAnalysis.scaleSnd`. -/
noncomputable def reflectFst : (E × ℝ) →ₗ[ℝ] E × ℝ :=
  LinearMap.prodMap (-LinearMap.id) LinearMap.id

/-- The reflection maps $(x, \mu)$ to $(-x, \mu)$. -/
@[simp] theorem reflectFst_apply (p : E × ℝ) : reflectFst E p = (-p.1, p.2) := rfl

/-- The epigraph of $x \mapsto f(-x)$ is the reflection of the epigraph of $f$:
$\operatorname{epi}(x \mapsto f(-x)) = \{ (-x, \mu) \mid (x, \mu) \in \operatorname{epi} f \}$. -/
theorem epi_comp_neg (f : E → EReal) :
    epi (fun x => f (-x)) = reflectFst E '' epi f := by
  ext p
  constructor
  · intro hp
    exact ⟨(-p.1, p.2), mk_mem_epi.2 (mem_epi.1 hp), by simp⟩
  · rintro ⟨q, hq, rfl⟩
    rw [mem_epi]
    simpa using mk_mem_epi.1 hq

omit [Module ℝ E] in
open Pointwise in
/-- The effective domain of $x \mapsto f(-x)$ is $-\operatorname{dom} f$. -/
theorem convexDom_comp_neg (f : E → EReal) : convexDom (fun x => f (-x)) = -convexDom f := by
  ext x
  rw [Set.mem_neg, mem_convexDom, mem_convexDom]

omit [Module ℝ E] in
/-- If $f$ is proper, then $x \mapsto f(-x)$ is proper. -/
theorem ProperConvex.comp_neg {f : E → EReal}
    (hf : ProperConvex f) : ProperConvex (fun x => f (-x)) := by
  obtain ⟨⟨x, hx⟩, hb⟩ := hf
  exact ⟨⟨-x, by simpa using hx⟩, fun x => hb (-x)⟩

/-- If $f$ is convex, then $x \mapsto f(-x)$ is convex. -/
theorem ConvexFn.comp_neg {f : E → EReal} (hf : ConvexFn f) : ConvexFn fun x => f (-x) :=
  convexFn_compLin (-LinearMap.id) hf

end Reflection

/-! ### Partial minimization: the image under a projection -/

section Projection

variable {Y Z : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
variable {h : Y × Z → EReal}

/-- Let $h \colon Y \times Z \to [-\infty, +\infty]$ be jointly convex and let $c \in Y$. Then
$z \mapsto h(c, z)$ is convex on $Z$.

The map $z \mapsto (c, z)$ is affine, so this is `ConvexAnalysis.ConvexFn.comp_affine`. -/
theorem ConvexFn.slice_left (hh : ConvexFn h) (c : Y) : ConvexFn (fun z : Z => h (c, z)) := by
  have heq : (fun z : Z => h (c, z)) = fun z : Z => h (LinearMap.inr ℝ Y Z z + (c, 0)) := by
    funext z
    simp
  rw [heq]
  exact hh.comp_affine _ _

/-- Let $h \colon Y \times Z \to [-\infty, +\infty]$ be jointly convex and let $c \in Z$. Then
$y \mapsto h(y, c)$ is convex on $Y$.

The map $y \mapsto (y, c)$ is affine, so this is `ConvexAnalysis.ConvexFn.comp_affine`. -/
theorem ConvexFn.slice_right (hh : ConvexFn h) (c : Z) : ConvexFn (fun y : Y => h (y, c)) := by
  have heq : (fun y : Y => h (y, c)) = fun y : Y => h (LinearMap.inl ℝ Y Z y + (0, c)) := by
    funext y
    simp
  rw [heq]
  exact hh.comp_affine _ _

/-- The image of $h \colon Y \times Z \to [-\infty, +\infty]$ under the projection
$(y, z) \mapsto y$ is minimization over $z$: its value at $y$ is $\inf_{z \in Z} h(y, z)$. -/
theorem mapLin_fst_apply (h : Y × Z → EReal) (y : Y) :
    mapLin (LinearMap.fst ℝ Y Z) h y = ⨅ z, h (y, z) := by
  refine le_antisymm (le_iInf fun z => mapLin_le rfl) (le_mapLin ?_)
  rintro ⟨y', z⟩ hp
  have hp' : y' = y := hp
  subst hp'
  exact iInf_le (fun z => h (y', z)) z

/-- The image of $h \colon Y \times Z \to [-\infty, +\infty]$ under the projection
$(y, z) \mapsto y$ is the function $y \mapsto \inf_{z \in Z} h(y, z)$. -/
theorem mapLin_fst (h : Y × Z → EReal) :
    mapLin (LinearMap.fst ℝ Y Z) h = fun y => ⨅ z, h (y, z) :=
  funext (mapLin_fst_apply h)

/-- **Partial minimization preserves convexity.** If $h \colon Y \times Z \to [-\infty, +\infty]$ is
jointly convex, then $$y \mapsto \inf_{z \in Z} h(y, z)$$ is convex on $Y$.

This is the image of $h$ under the projection $(y, z) \mapsto y$. It is the form used to build
the perturbation function of a convex program. -/
theorem convexFn_iInf_right (hh : ConvexFn h) : ConvexFn (fun y => ⨅ z, h (y, z)) := by
  rw [← mapLin_fst h]
  exact convexFn_mapLin _ hh

/-- The effective domain of $y \mapsto \inf_{z} h(y, z)$ is the projection of the effective domain
of $h$ on $Y$. -/
theorem convexDom_iInf_right (h : Y × Z → EReal) :
    convexDom (fun y => ⨅ z, h (y, z)) = Prod.fst '' convexDom h := by
  rw [← mapLin_fst h, convexDom_mapLin]
  rfl

end Projection

end ConvexAnalysis
