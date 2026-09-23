import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.Closure
import Mathlib.Order.GaloisConnection.Basic
import Numlib.Analysis.Convex.Epigraph

/-!
# The function determined by a set in `E × ℝ`

To build a convex function on `E`, build a convex set `F ⊆ E × ℝ` and take `ofEpi F`, the function
whose graph is the *lower boundary* of `F`: `ofEpi F x = inf {μ : ℝ | (x, μ) ∈ F}`, an infimum in
`EReal`, hence `⊤` over an empty vertical section and `⊥` over one unbounded below. Infimal
convolution, right scalar multiplication, the convex hull of a family of functions, the image under
a linear map and the lower-semicontinuous hull are all `ofEpi` of a set built from epigraphs. No
structure on `E` is needed; only the convexity statement itself asks for a real vector space.

`epi (ofEpi F) = F` is false in general — only `F ⊆ epi (ofEpi F)` always holds — and `IsEpiLike F`
names the sets where it does. That predicate is not preserved by the operations that matter most: a
sum of epigraphs need not be an epigraph, since an infimal convolution need not attain its infimum,
and nor need the convex hull of a union. Those modules carry it as a hypothesis.

## Main results

* `subset_epi_iff_le_ofEpi` — the adjunction `F ⊆ epi g ↔ g ≤ ofEpi F`: `epi` and `ofEpi` form an
  antitone Galois connection (`gc_ofEpi_epi`, `epiClosure`) whose closed elements are the epi-like
  sets, and the order facts below are formal consequences.
* `convexFn_ofEpi` — `ofEpi F` is convex when `F` is.
* `ofEpi_epi` — `ofEpi (epi f) = f`, with no hypothesis; `epi_ofEpi` is the converse, under
  `IsEpiLike`.
* `IsEpiLike.iInter`, `.inter`, `.union`, `.of_isClosed`, `.closure` — the stability properties
  the operations of this section consume.

## References

* [rockafellar1970convex] §5.
-/

open Set

namespace ConvexAnalysis

section Basic

variable {E : Type*}

/-! ### The function determined by a set -/

/-- The function whose graph is the *lower boundary* of a set `F ⊆ E × ℝ`:
`ofEpi F x = inf {μ | (x, μ) ∈ F}`, an infimum in `EReal`. -/
noncomputable def ofEpi (F : Set (E × ℝ)) : E → EReal :=
  fun x => ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)

variable {F G : Set (E × ℝ)} {f g : E → EReal} {x : E} {μ ν : ℝ} {z : EReal}

theorem ofEpi_apply_le (h : (x, μ) ∈ F) : ofEpi F x ≤ (μ : EReal) :=
  iInf₂_le (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) μ h

theorem le_ofEpi (h : ∀ μ : ℝ, (x, μ) ∈ F → z ≤ (μ : EReal)) : z ≤ ofEpi F x :=
  le_iInf₂ (f := fun μ (_ : (x, μ) ∈ F) => (μ : EReal)) h

/-- The workhorse: the infimum defining `ofEpi F x` need not be attained, so arguments about
`ofEpi` proceed through a strict inequality, which does produce a witness. -/
theorem ofEpi_lt_iff : ofEpi F x < z ↔ ∃ μ : ℝ, (x, μ) ∈ F ∧ (μ : EReal) < z := by
  simp only [ofEpi, iInf_lt_iff, exists_prop]
  exact Iff.rfl

/-- **The universal property**: `ofEpi F` is the greatest function whose epigraph contains `F`. -/
theorem subset_epi_iff_le_ofEpi : F ⊆ epi g ↔ g ≤ ofEpi F := by
  constructor
  · exact fun h y => le_ofEpi fun _ hμ => h hμ
  · rintro h ⟨y, ρ⟩ hp
    exact (h y).trans (ofEpi_apply_le hp)

/-- The reverse inclusion is `epi_ofEpi`, and needs `IsEpiLike`. -/
theorem subset_epi_ofEpi (F : Set (E × ℝ)) : F ⊆ epi (ofEpi F) :=
  subset_epi_iff_le_ofEpi.2 le_rfl

theorem ofEpi_mono (h : F ⊆ G) : ofEpi G ≤ ofEpi F :=
  subset_epi_iff_le_ofEpi.1 (h.trans (subset_epi_ofEpi G))

theorem ofEpi_eq_top_iff : ofEpi F x = ⊤ ↔ ∀ μ : ℝ, (x, μ) ∉ F := by
  rw [← not_iff_not, ← Ne, ← lt_top_iff_ne_top, ofEpi_lt_iff]
  simp

@[simp] theorem ofEpi_empty : ofEpi (∅ : Set (E × ℝ)) = ⊤ :=
  funext fun _ => ofEpi_eq_top_iff.2 fun _ => notMem_empty _

@[simp] theorem ofEpi_univ : ofEpi (univ : Set (E × ℝ)) = ⊥ :=
  funext fun _ =>
    le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ofEpi_apply_le (mem_univ (_, r)))

/-- No hypothesis: a vertical section of an epigraph is `∅`, `ℝ` or a closed half-line, and in each
case its infimum is the value of `f`. -/
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

theorem eq_ofEpi_of_epi_eq (h : epi f = F) : f = ofEpi F := by rw [← h, ofEpi_epi]

theorem ofEpi_apply_congr (h : ∀ μ : ℝ, (x, μ) ∈ F ↔ (x, μ) ∈ G) : ofEpi F x = ofEpi G x := by
  have hs : {μ : ℝ | (x, μ) ∈ F} = {μ : ℝ | (x, μ) ∈ G} := Set.ext h
  simp only [ofEpi, hs]

/-- For any `F`: `ofEpi F x < ⊤` says exactly that the vertical section over `x` is nonempty. -/
theorem convexDom_ofEpi (F : Set (E × ℝ)) : convexDom (ofEpi F) = Prod.fst '' F := by
  ext x
  constructor
  · intro hx
    by_contra hx'
    exact absurd (ofEpi_eq_top_iff.2 fun μ hμ => hx' ⟨(x, μ), hμ, rfl⟩) hx.ne
  · rintro ⟨⟨w, μ⟩, hw, rfl⟩
    exact lt_of_le_of_lt (ofEpi_apply_le hw) (EReal.coe_lt_top μ)

/-! ### The Galois connection between sets and functions

`OrderDual` on the function side makes the antitone adjunction fit Mathlib's monotone
`GaloisConnection`. -/

open OrderDual in
theorem gc_ofEpi_epi :
    GaloisConnection (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  fun _ _ => subset_epi_iff_le_ofEpi.symm

open OrderDual in
/-- An insertion, because `ofEpi (epi f) = f` on the nose. -/
noncomputable def gi_ofEpi_epi :
    GaloisInsertion (fun F : Set (E × ℝ) => toDual (ofEpi F))
      (fun g : (E → EReal)ᵒᵈ => epi (ofDual g)) :=
  gc_ofEpi_epi.toGaloisInsertion fun g => le_of_eq (by simp [ofEpi_epi])

/-- The closure operator `F ↦ epi (ofEpi F)`; its closed elements are the epi-like sets. -/
noncomputable def epiClosure : ClosureOperator (Set (E × ℝ)) := gc_ofEpi_epi.closureOperator

@[simp] theorem epiClosure_apply (F : Set (E × ℝ)) : epiClosure F = epi (ofEpi F) := rfl

theorem epi_injective : Function.Injective (epi : (E → EReal) → Set (E × ℝ)) :=
  fun _ _ h => by simpa using congrArg ofEpi h

/-! ### Sets that are epigraphs -/

/-- `F ⊆ E × ℝ` is *epi-like* when it is the epigraph of some function `E → EReal`. Equivalently
(`isEpiLike_iff_forall`), every vertical section `{μ | (x, μ) ∈ F}` is upward closed and attains
its infimum — is `∅`, `ℝ`, or a closed half-line `Set.Ici c`.

Both halves are needed: it fails for `{p | 0 < p.2}` (upward closed, does not attain) and for
`{(0, 0)}` (attains, not upward closed). The witness is always `ofEpi F` (`isEpiLike_iff`). -/
def IsEpiLike (F : Set (E × ℝ)) : Prop := ∃ f : E → EReal, F = epi f

@[simp] theorem isEpiLike_epi (f : E → EReal) : IsEpiLike (epi f) := ⟨f, rfl⟩

/-- **The point of `IsEpiLike`.** For an epi-like set the two constructions are inverse. -/
@[simp] theorem epi_ofEpi (h : IsEpiLike F) : epi (ofEpi F) = F := by
  obtain ⟨f, rfl⟩ := h
  rw [ofEpi_epi]

theorem isEpiLike_iff : IsEpiLike F ↔ epi (ofEpi F) = F :=
  ⟨epi_ofEpi, fun h => ⟨ofEpi F, h.symm⟩⟩

theorem isEpiLike_iff_isClosed {F : Set (E × ℝ)} : IsEpiLike F ↔ epiClosure.IsClosed F :=
  isEpiLike_iff

theorem IsEpiLike.mem_of_le (h : IsEpiLike F) (hμ : (x, μ) ∈ F) (hμν : μ ≤ ν) : (x, ν) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  exact mk_mem_epi.2 ((mk_mem_epi.1 hμ).trans (by exact_mod_cast hμν))

theorem IsEpiLike.mem_of_forall_lt (h : IsEpiLike F) (hμ : ∀ ν : ℝ, μ < ν → (x, ν) ∈ F) :
    (x, μ) ∈ F := by
  obtain ⟨f, rfl⟩ := h
  refine mk_mem_epi.2 (EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_)
  replace hq := EReal.coe_lt_coe_iff.1 hq
  obtain ⟨ρ, hμρ, hρq⟩ := exists_between hq
  exact lt_of_le_of_lt (mk_mem_epi.1 (hμ ρ hμρ)) (by exact_mod_cast hρq)

/-- The criterion one checks in practice. -/
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

theorem isEpiLike_iff_forall :
    IsEpiLike F ↔ (∀ (x : E) (μ ν : ℝ), (x, μ) ∈ F → μ ≤ ν → (x, ν) ∈ F) ∧
      ∀ (x : E) (μ : ℝ), (∀ ν : ℝ, μ < ν → (x, ν) ∈ F) → (x, μ) ∈ F :=
  ⟨fun h => ⟨fun _ _ _ hμ hμν => h.mem_of_le hμ hμν, fun _ _ hμ => h.mem_of_forall_lt hμ⟩,
    fun h => isEpiLike_of_forall h.1 h.2⟩

/-- An intersection of epigraphs is an epigraph: that of the pointwise supremum. -/
theorem IsEpiLike.iInter {ι : Sort*} {F : ι → Set (E × ℝ)} (h : ∀ i, IsEpiLike (F i)) :
    IsEpiLike (⋂ i, F i) := by
  choose f hf using h
  refine ⟨⨆ i, f i, ?_⟩
  ext p
  simp [hf, epi, iSup_apply, iSup_le_iff]

theorem IsEpiLike.inter (hF : IsEpiLike F) (hG : IsEpiLike G) : IsEpiLike (F ∩ G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  refine ⟨f ⊔ g, ?_⟩
  ext p
  simp [epi, sup_le_iff]

/-- The epigraph of the pointwise minimum. This uses linearity of `EReal` and fails for infinite
unions: the union of the epigraphs of the constants `1 / (n + 1)` is not an epigraph. -/
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

/-- The function whose graph is the lower boundary of a convex set is convex. The route is
`convexFn_iff_forall_lt`, which asks only for *strict* upper bounds, a non-strict one yielding no
witness. -/
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

/-- Closedness buys the attainment half of `IsEpiLike` — a closed vertical section contains the
infimum of its points — but not the other: `{(0, 0)}` is closed and is not an epigraph. -/
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

/-- What `lscHull f := ofEpi (closure (epi f))` needs, to satisfy `epi (lscHull f) = cl (epi f)`. -/
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
