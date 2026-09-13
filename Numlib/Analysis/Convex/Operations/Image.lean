import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# Images and inverse images of convex functions under a linear map

A linear map `A : E → G` transports convex functions in both directions. The *inverse image*
`g A = g ∘ A` is the easy one — its epigraph is a preimage — while the *image*
`(A f) y = inf {f x | A x = y}` is the interesting one: the infimum need not be attained, so `A f`
is read off `epi f` not as a set image but as the function that image determines. Accordingly
`epi (A f) = (A × id) '' epi f` is **false** in general
(`exists_epi_mapLin_ne_image`); `epi_mapLin` recovers it from `IsEpiLike`, exactly the missing
attainment.

## Main definitions

* `mapLin A f` — the image `A f` of `f` under `A`.
* `compLin g A` — the inverse image `g A` of `g` under `A`.

## Main results

* `convexFn_compLin`, `convexFn_mapLin` — both directions preserve convexity.
* `gc_compLin_mapLin` — `g ≤ A f ↔ g A ≤ f`, a *monotone* Galois connection (no `OrderDual`,
  unlike `gc_ofEpi_epi`), giving the monotonicity lemmas, the unit and counit, and — for surjective
  `A`, where it is a `GaloisCoinsertion` — the identity `A (g A) = g`.
* `mapLin_eq_ofEpi` — the image is the function determined by the image of the epigraph under
  `(x, μ) ↦ (A x, μ)`, which is how convexity of the image is proved.
* `convexFn_iInf_right` — partial minimisation `y ↦ ⨅ z, h (y, z)` of a jointly convex function is
  convex: the projection case, and the form the perturbation function of a convex program takes.
* `ConvexFn.comp_affine`, `ConvexFn.slice_left`, `ConvexFn.slice_right` — precomposition with an
  affine map, and fixing one variable of a function of two.

## References

* [rockafellar1970convex] §5.
-/

open Set

namespace ConvexAnalysis

section Module

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]

/-! ### The two operations -/

/-- The **image** of `f` under a linear map `A`: `(A f) y = inf {f x | A x = y}` over the fibre of
`A` above `y`, hence `⊤` off its range. The infimum is generally *not attained*. -/
noncomputable def mapLin (A : E →ₗ[ℝ] G) (f : E → EReal) : G → EReal :=
  fun y => ⨅ x ∈ {x | A x = y}, f x

/-- The **inverse image** of `g` under a linear map `A`: `(g A) x = g (A x)`. -/
def compLin (g : G → EReal) (A : E →ₗ[ℝ] G) : E → EReal := g ∘ A

/-- The map `(x, μ) ↦ (A x, μ)`, along which `epi (g A)` is the pullback of `epi g`. -/
abbrev prodMapId (A : E →ₗ[ℝ] G) : E × ℝ →ₗ[ℝ] G × ℝ :=
  A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

variable {A : E →ₗ[ℝ] G} {f : E → EReal} {g : G → EReal} {x : E} {y : G} {z : EReal}

@[simp] theorem compLin_apply (g : G → EReal) (A : E →ₗ[ℝ] G) (x : E) :
    compLin g A x = g (A x) := rfl

/-! ### The infimum defining the image -/

theorem mapLin_le (h : A x = y) : mapLin A f y ≤ f x :=
  iInf₂_le (f := fun z (_ : z ∈ {z | A z = y}) => f z) x h

theorem le_mapLin (h : ∀ x : E, A x = y → z ≤ f x) : z ≤ mapLin A f y :=
  le_iInf₂ (f := fun z (_ : z ∈ {z | A z = y}) => f z) h

/-- The witness extractor: as for `ofEpi`, arguments go through a strict inequality. -/
theorem mapLin_lt_iff : mapLin A f y < z ↔ ∃ x : E, A x = y ∧ f x < z := by
  simp only [mapLin, iInf_lt_iff, exists_prop]
  exact Iff.rfl

/-- Off the range of `A` the image is `⊤`: there is nothing to take an infimum over. -/
theorem mapLin_of_notMem_range (hy : y ∉ Set.range A) : mapLin A f y = ⊤ :=
  top_le_iff.1 (le_mapLin fun x hx => absurd ⟨x, hx⟩ hy)

/-! ### The adjunction `g ≤ A f ↔ g A ≤ f` -/

/-- **The universal property of the image.** `f ↦ A f` is right adjoint to `g ↦ g A`. -/
theorem gc_compLin_mapLin (A : E →ₗ[ℝ] G) :
    GaloisConnection (fun g : G → EReal => compLin g A) (fun f : E → EReal => mapLin A f) :=
  fun _ _ =>
    ⟨fun h _ => le_mapLin fun x hx => hx ▸ h x, fun h x => (h (A x)).trans (mapLin_le rfl)⟩

theorem le_mapLin_iff : g ≤ mapLin A f ↔ compLin g A ≤ f :=
  (gc_compLin_mapLin A g f).symm

theorem mapLin_mono {f₁ f₂ : E → EReal} (h : f₁ ≤ f₂) : mapLin A f₁ ≤ mapLin A f₂ :=
  (gc_compLin_mapLin A).monotone_u h

theorem compLin_mono {g₁ g₂ : G → EReal} (h : g₁ ≤ g₂) : compLin g₁ A ≤ compLin g₂ A :=
  fun x => h (A x)

/-- The counit of the adjunction: `(A f) (A x) ≤ f x`. -/
theorem compLin_mapLin_le (A : E →ₗ[ℝ] G) (f : E → EReal) : compLin (mapLin A f) A ≤ f :=
  (gc_compLin_mapLin A).l_u_le f

/-- The unit of the adjunction: `g ≤ A (g A)`, with equality exactly on the range of `A`. -/
theorem le_mapLin_compLin (A : E →ₗ[ℝ] G) (g : G → EReal) : g ≤ mapLin A (compLin g A) :=
  (gc_compLin_mapLin A).le_u_l g

theorem mapLin_compLin (hA : Function.Surjective A) (g : G → EReal) :
    mapLin A (compLin g A) = g :=
  le_antisymm (fun y => by
    obtain ⟨x, rfl⟩ := hA y
    exact mapLin_le rfl) (le_mapLin_compLin A g)

/-- For surjective `A` the adjunction is a `GaloisCoinsertion`. -/
noncomputable def gci_compLin_mapLin (hA : Function.Surjective A) :
    GaloisCoinsertion (fun g : G → EReal => compLin g A) (fun f : E → EReal => mapLin A f) :=
  (gc_compLin_mapLin A).toGaloisCoinsertion fun g => le_of_eq (mapLin_compLin hA g)

/-! ### Effective domains -/

theorem dom_compLin (g : G → EReal) (A : E →ₗ[ℝ] G) : dom (compLin g A) = A ⁻¹' dom g := rfl

/-- **Properness survives a surjective substitution, both ways.** Surjectivity is needed for both
halves: `g A` can be proper while `g` is `⊥` off the range, and `g` proper while `A` misses all of
its finite values. -/
theorem proper_compLin_of_surjective (hA : Function.Surjective A) :
    Proper (compLin g A) ↔ Proper g := by
  constructor
  · rintro ⟨⟨x, hx⟩, hb⟩
    refine ⟨⟨A x, hx⟩, fun z => ?_⟩
    obtain ⟨w, rfl⟩ := hA z
    exact hb w
  · rintro ⟨⟨z, hz⟩, hb⟩
    obtain ⟨w, rfl⟩ := hA z
    exact ⟨⟨w, hz⟩, fun x => hb (A x)⟩

/-- The effective domain of an image is the image of the effective domain; no convexity needed. -/
theorem dom_mapLin (A : E →ₗ[ℝ] G) (f : E → EReal) : dom (mapLin A f) = A '' dom f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hf⟩ := mapLin_lt_iff.1 hy
    exact ⟨x, hf, hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact mapLin_lt_iff.2 ⟨x, rfl, hx⟩

/-! ### Epigraphs, and convexity in both directions -/

/-- `epi g` pulled back along `(x, μ) ↦ (A x, μ)`: the whole proof of the inverse-image half. -/
theorem epi_compLin (g : G → EReal) (A : E →ₗ[ℝ] G) :
    epi (compLin g A) = prodMapId A ⁻¹' epi g := rfl

/-- The inverse image of a convex function under a linear map is convex. -/
theorem convexFn_compLin (A : E →ₗ[ℝ] G) (hg : ConvexFn g) : ConvexFn (compLin g A) := by
  refine ⟨?_⟩
  rw [epi_compLin]
  exact hg.convex_epi.linear_preimage _

/-- **Precomposition with an affine map preserves convexity**, in the form applications want. -/
theorem ConvexFn.comp_affine (hg : ConvexFn g) (A : E →ₗ[ℝ] G) (b : G) :
    ConvexFn (fun x : E => g (A x + b)) := by
  have heq : (fun x : E => g (A x + b)) = compLin (fun y => g (b + y)) A := by
    funext x
    simp [compLin, add_comm]
  rw [heq]
  exact convexFn_compLin A (hg.comp_add_left b)

/-- The image of `f` under `A` is the function determined by the image of `epi f` under
`(x, μ) ↦ (A x, μ)`. This is an equality of *functions*; the corresponding equality of *sets*,
`epi_mapLin`, needs a hypothesis. -/
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

/-- The image of a convex function under a linear map is convex: a linear image of a convex set is
convex, and the function it determines is then convex too. -/
theorem convexFn_mapLin (A : E →ₗ[ℝ] G) (hf : ConvexFn f) : ConvexFn (mapLin A f) := by
  rw [mapLin_eq_ofEpi]
  exact convexFn_ofEpi (hf.convex_epi.linear_image _)

/-- The epigraph of the image is the image of the epigraph, under the hypothesis that makes it
true: the infimum defining `A f` must be attained wherever it is finite. -/
theorem epi_mapLin (h : IsEpiLike (A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f)) :
    epi (mapLin A f) = A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  rw [mapLin_eq_ofEpi]
  exact epi_ofEpi h

/-! ### Indicator functions -/

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

theorem compLin_indicatorFn (A : E →ₗ[ℝ] G) (s : Set G) :
    compLin (indicatorFn s) A = indicatorFn (A ⁻¹' s) := by
  funext x
  by_cases hx : A x ∈ s <;> simp [hx, Set.mem_preimage]

/-! ### The hypothesis of `epi_mapLin` is not removable -/

/-- **The image of an epigraph need not be an epigraph.** With `A = 0` on `ℝ` and `f` the (convex)
function equal to `x` on `(0, ∞)` and `⊤` elsewhere, `(A f) 0 = inf {x | x > 0} = 0` is not
attained: `(0, 0)` belongs to `epi (A f)` but not to the image of `epi f`, which is
`{0} × (0, ∞)`. -/
theorem exists_epi_mapLin_ne_image :
    ∃ (f : ℝ → EReal) (A : ℝ →ₗ[ℝ] ℝ), ConvexFn f ∧
      epi (mapLin A f) ≠ A.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) '' epi f := by
  refine ⟨ConvexAnalysis.restrictFn (Ioi 0) (fun x => (x : EReal)), 0, ?_, ?_⟩
  · refine convexFn_of_epi_combo fun u v μ ν hu hv a b ha hb hab => ?_
    have hu0 : u ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [ConvexAnalysis.restrictFn_of_notMem h] at hu
      exact absurd hu (not_le.2 (EReal.coe_lt_top μ))
    have hv0 : v ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [ConvexAnalysis.restrictFn_of_notMem h] at hv
      exact absurd hv (not_le.2 (EReal.coe_lt_top ν))
    rw [ConvexAnalysis.restrictFn_of_mem hu0] at hu
    rw [ConvexAnalysis.restrictFn_of_mem hv0] at hv
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
    rw [ConvexAnalysis.restrictFn_of_mem hpos]
    have hle : a • u + b • v ≤ a * μ + b * ν := by
      simp only [smul_eq_mul]
      nlinarith
    exact_mod_cast hle
  · intro hcontra
    set f : ℝ → EReal := ConvexAnalysis.restrictFn (Ioi 0) (fun x => (x : EReal)) with hf
    have hmem : ((0 : ℝ), (0 : ℝ)) ∈ epi (mapLin (0 : ℝ →ₗ[ℝ] ℝ) f) := by
      refine mk_mem_epi.2 (EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_)
      replace hq := EReal.coe_lt_coe_iff.1 hq
      refine lt_of_le_of_lt (mapLin_le (x := q / 2) (by simp)) ?_
      have hq2 : q / 2 ∈ Ioi (0 : ℝ) := by change (0 : ℝ) < q / 2; linarith
      rw [hf, ConvexAnalysis.restrictFn_of_mem hq2]
      exact_mod_cast (by linarith : q / 2 < q)
    rw [hcontra] at hmem
    obtain ⟨⟨u, μ⟩, hu, huv⟩ := hmem
    have hu' : f u ≤ (μ : EReal) := hu
    have h2 : μ = 0 := congrArg Prod.snd huv
    rw [h2] at hu'
    have hu0 : u ∈ Ioi (0 : ℝ) := by
      by_contra h
      rw [hf, ConvexAnalysis.restrictFn_of_notMem h] at hu'
      exact absurd hu' (not_le.2 (EReal.coe_lt_top 0))
    rw [hf, ConvexAnalysis.restrictFn_of_mem hu0] at hu'
    exact absurd (by exact_mod_cast hu' : u ≤ (0 : ℝ)) (not_le.2 hu0)

end Module

/-! ### Partial minimisation: the projection case -/

section Projection

variable {Y Z : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
variable {h : Y × Z → EReal}

/-- Fixing one variable of a jointly convex function: the slice map `z ↦ (c, z)` is affine. -/
theorem ConvexFn.slice_left (hh : ConvexFn h) (c : Y) : ConvexFn (fun z : Z => h (c, z)) := by
  have heq : (fun z : Z => h (c, z)) = fun z : Z => h (LinearMap.inr ℝ Y Z z + (c, 0)) := by
    funext z
    simp
  rw [heq]
  exact hh.comp_affine _ _

theorem ConvexFn.slice_right (hh : ConvexFn h) (c : Z) : ConvexFn (fun y : Y => h (y, c)) := by
  have heq : (fun y : Y => h (y, c)) = fun y : Y => h (LinearMap.inl ℝ Y Z y + (0, c)) := by
    funext y
    simp
  rw [heq]
  exact hh.comp_affine _ _

/-- The image under the projection `(y, z) ↦ y` is minimisation over `z`. -/
theorem mapLin_fst_apply (h : Y × Z → EReal) (y : Y) :
    mapLin (LinearMap.fst ℝ Y Z) h y = ⨅ z, h (y, z) := by
  refine le_antisymm (le_iInf fun z => mapLin_le rfl) (le_mapLin ?_)
  rintro ⟨y', z⟩ hp
  have hp' : y' = y := hp
  subst hp'
  exact iInf_le (fun z => h (y', z)) z

theorem mapLin_fst (h : Y × Z → EReal) :
    mapLin (LinearMap.fst ℝ Y Z) h = fun y => ⨅ z, h (y, z) :=
  funext (mapLin_fst_apply h)

/-- **Partial minimisation preserves convexity**: the image case with `A` a projection. This is the
form used to build the perturbation function of a convex program. -/
theorem convexFn_iInf_right (hh : ConvexFn h) : ConvexFn (fun y => ⨅ z, h (y, z)) := by
  rw [← mapLin_fst h]
  exact convexFn_mapLin _ hh

theorem dom_iInf_right (h : Y × Z → EReal) :
    dom (fun y => ⨅ z, h (y, z)) = Prod.fst '' dom h := by
  rw [← mapLin_fst h, dom_mapLin]
  rfl

end Projection

end ConvexAnalysis
