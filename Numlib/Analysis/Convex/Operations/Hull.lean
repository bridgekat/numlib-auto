import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# The convex hull of a family of functions

The pointwise infimum of convex functions is generally not convex; the convex hull is what replaces
it. The convex hull of a family `f : ι → E → EReal` is the function determined by the convex hull of
the union of the epigraphs, and it is the **greatest convex function below every `f i`**.

## Main definitions

* `convFn f` — the convex hull of a family: the infimum in the lattice of convex functions.
* `convHullFn g` — the convex hull `conv g` of a single function: the coreflector onto that
  lattice. The two determine each other (`convFn_eq_convHullFn_iInf`, `convFn_unit`) but play
  different roles — only `convHullFn` is an adjoint, only `convFn` takes a family.
* `convFn₂ f g` — the binary case, the meet of two convex functions.

## Main results

* `convFn_le`, `le_convFn`, `isGreatest_convFn` — **the universal property**: greatest convex
  minorant, from which everything else in the file follows.
* `convexFn_convFn` — the convex hull is convex.
* `convFn_le_iInf` — the convex hull is below the pointwise infimum, generally *strictly*;
  `convFn₂_indicatorFn_lt_inf` is a witness.
* `gci_val_convHullFn` — `conv` is right adjoint to the inclusion of the convex functions, as a
  `GaloisCoinsertion`. This is what makes the convex functions a complete lattice with
  `⨅ = convFn` and `⨆ = sSup`.
* `convFn_apply` — the explicit formula `(conv {f i}) x = inf {∑ λ i * f i (x i) | ∑ λ i • x i = x}`
  ([rockafellar1970convex] Theorem 5.6); `convFn₂_apply` is the two-function form later sections
  use.
* `IsEpiLike.mem_convexHull_of_le`, `isEpiLike_convexHull_epi_union`, `epi_convFn₂` — when that
  infimum is *attained*. `epi (conv {f, g})` is `conv (epi f ∪ epi g)` exactly when that hull is
  an epigraph, and the only way it can fail to be one is by failing to be closed.

## References

* [rockafellar1970convex] §5.
-/

open Set

namespace ConvexAnalysis


section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The convex hull of a family -/

section Family

variable {ι : Sort*} {f : ι → E → EReal} {g : E → EReal}

/-- The **convex hull of a family of functions**: the function determined by the convex hull of the
union of the epigraphs. Equivalently (`isGreatest_convFn`), the greatest convex `h`, proper or not,
with `h ≤ f i` for every `i`. -/
noncomputable def convFn (f : ι → E → EReal) : E → EReal :=
  ofEpi (convexHull ℝ (⋃ i, epi (f i)))

/-- The convex hull of a family is a convex function, a convex hull of sets being convex. -/
theorem convexFn_convFn (f : ι → E → EReal) : ConvexFn (convFn f) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

theorem convFn_le (f : ι → E → EReal) (i : ι) : convFn f ≤ f i := by
  have h : epi (f i) ⊆ convexHull ℝ (⋃ j, epi (f j)) :=
    (subset_iUnion (fun j => epi (f j)) i).trans (subset_convexHull ℝ _)
  have h' := ofEpi_mono h
  rwa [ofEpi_epi] at h'

/-- **The universal property.** Any convex function below every `f i` is below the convex hull;
with `convFn_le` and `convexFn_convFn`, the convex hull is the *greatest* convex minorant. -/
theorem le_convFn (hg : ConvexFn g) (h : ∀ i, g ≤ f i) : g ≤ convFn f :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (iUnion_subset fun i => epi_anti (h i)) hg.convex_epi)

theorem isGreatest_convFn (f : ι → E → EReal) :
    IsGreatest {g : E → EReal | ConvexFn g ∧ ∀ i, g ≤ f i} (convFn f) :=
  ⟨⟨convexFn_convFn f, convFn_le f⟩, fun _ hg => le_convFn hg.1 hg.2⟩

theorem convFn_mono {f₁ f₂ : ι → E → EReal} (h : ∀ i, f₁ i ≤ f₂ i) : convFn f₁ ≤ convFn f₂ :=
  le_convFn (convexFn_convFn f₁) fun i => (convFn_le f₁ i).trans (h i)

/-- The epigraph of the convex hull is the convex hull of the union of epigraphs, under the
hypothesis that the latter is an epigraph at all. It need not be: even for two functions the
infimum in the formula for `convFn` need not be attained. -/
theorem epi_convFn (h : IsEpiLike (convexHull ℝ (⋃ i, epi (f i)))) :
    epi (convFn f) = convexHull ℝ (⋃ i, epi (f i)) :=
  epi_ofEpi h

/-- The convex hull is below the pointwise infimum, strictly in general
(`convFn₂_indicatorFn_lt_inf`), which is the entire reason the convex hull exists. -/
theorem convFn_le_iInf (f : ι → E → EReal) (x : E) : convFn f x ≤ ⨅ i, f i x :=
  le_iInf fun i => convFn_le f i x

/-- When the pointwise infimum happens to be convex, it *is* the convex hull. -/
theorem convFn_eq_iInf (hc : ConvexFn fun x => ⨅ i, f i x) : convFn f = fun x => ⨅ i, f i x :=
  le_antisymm (fun x => convFn_le_iInf f x)
    (le_convFn hc fun i x => iInf_le (fun j => f j x) i)

end Family

/-! ### The convex hull of a single function -/

section Single

variable {g h : E → EReal}

/-- The **convex hull of a function**, `conv g`: the greatest convex function majorised by `g`. -/
noncomputable def convHullFn (g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi g))

theorem convexFn_convHullFn (g : E → EReal) : ConvexFn (convHullFn g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

theorem convHullFn_le (g : E → EReal) : convHullFn g ≤ g := by
  have h' := ofEpi_mono (subset_convexHull ℝ (epi g))
  rwa [ofEpi_epi] at h'

/-- **The universal property of `conv g`.** -/
theorem le_convHullFn (hh : ConvexFn h) (hg : h ≤ g) : h ≤ convHullFn g :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (epi_anti hg) hh.convex_epi)

theorem isGreatest_convHullFn (g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ g} (convHullFn g) :=
  ⟨⟨convexFn_convHullFn g, convHullFn_le g⟩, fun _ hh => le_convHullFn hh.1 hh.2⟩

theorem convHullFn_mono (hgh : g ≤ h) : convHullFn g ≤ convHullFn h :=
  le_convHullFn (convexFn_convHullFn g) ((convHullFn_le g).trans hgh)

theorem convHullFn_eq_self (hg : ConvexFn g) : convHullFn g = g :=
  le_antisymm (convHullFn_le g) (le_convHullFn hg le_rfl)

/-- Convexity is exactly closedness under `conv`. -/
theorem convexFn_iff_convHullFn_eq : ConvexFn g ↔ convHullFn g = g :=
  ⟨convHullFn_eq_self, fun h => h ▸ convexFn_convHullFn g⟩

theorem convHullFn_idem (g : E → EReal) : convHullFn (convHullFn g) = convHullFn g :=
  convHullFn_eq_self (convexFn_convHullFn g)

end Single

/-! ### The coreflection onto the convex functions -/

section Coreflection

/-- **`conv` is right adjoint to the inclusion of the convex functions.** For convex `h` and
arbitrary `g`, `h ≤ g` and `h ≤ conv g` say the same thing. -/
theorem gc_val_convHullFn :
    GaloisConnection (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  fun h g => ⟨fun hle => le_convHullFn h.2 hle,
    fun hle => (show (h : E → EReal) ≤ convHullFn g from hle).trans (convHullFn_le g)⟩

/-- A coinsertion, because `conv` fixes the convex functions. The convex functions therefore
inherit a complete lattice structure in which the infimum is `convFn`. -/
noncomputable def gci_val_convHullFn :
    GaloisCoinsertion (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  gc_val_convHullFn.toGaloisCoinsertion fun h => convHullFn_le (h : E → EReal)

end Coreflection

/-! ### The two hulls determine each other -/

section Compare

variable {ι : Sort*} {f : ι → E → EReal}

/-- Rockafellar: the convex hull of a collection "is the convex hull of the pointwise infimum of
the collection". Both sides are the greatest convex function below every `f i`. -/
theorem convFn_eq_convHullFn_iInf (f : ι → E → EReal) :
    convFn f = convHullFn fun x => ⨅ i, f i x :=
  le_antisymm (le_convHullFn (convexFn_convFn f) fun x => convFn_le_iInf f x)
    (le_convFn (convexFn_convHullFn _) fun i =>
      (convHullFn_le _).trans fun x => iInf_le (fun j => f j x) i)

/-- `convHullFn` is the one-element instance of `convFn`. -/
theorem convFn_unit (g : E → EReal) : convFn (fun _ : Unit => g) = convHullFn g := by
  rw [convFn_eq_convHullFn_iInf]
  simp

end Compare

/-! ### The binary case -/

section Binary

variable {f g h : E → EReal}

/-- The convex hull of two functions: the greatest convex function below both, i.e. the meet in the
lattice of convex functions. -/
noncomputable def convFn₂ (f g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi f ∪ epi g))

theorem convexFn_convFn₂ (f g : E → EReal) : ConvexFn (convFn₂ f g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

theorem convFn₂_le_left (f g : E → EReal) : convFn₂ f g ≤ f := by
  have h' := ofEpi_mono (subset_union_left.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

theorem convFn₂_le_right (f g : E → EReal) : convFn₂ f g ≤ g := by
  have h' := ofEpi_mono (subset_union_right.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

/-- **The universal property**, binary case. -/
theorem le_convFn₂ (hh : ConvexFn h) (h₁ : h ≤ f) (h₂ : h ≤ g) : h ≤ convFn₂ f g :=
  subset_epi_iff_le_ofEpi.1
    (convexHull_min (union_subset (epi_anti h₁) (epi_anti h₂)) hh.convex_epi)

theorem isGreatest_convFn₂ (f g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ f ∧ h ≤ g} (convFn₂ f g) :=
  ⟨⟨convexFn_convFn₂ f g, convFn₂_le_left f g, convFn₂_le_right f g⟩,
    fun _ hh => le_convFn₂ hh.1 hh.2.1 hh.2.2⟩

/-- The binary convex hull is below the pointwise minimum, generally strictly. -/
theorem convFn₂_le_inf (f g : E → EReal) : convFn₂ f g ≤ f ⊓ g :=
  le_inf (convFn₂_le_left f g) (convFn₂_le_right f g)

/-- The binary case is the two-element instance of `convFn`. -/
theorem convFn₂_eq_convFn (f g : E → EReal) :
    convFn₂ f g = convFn (fun b : Bool => cond b f g) := by
  refine le_antisymm (le_convFn (convexFn_convFn₂ f g) fun b => ?_)
    (le_convFn₂ (convexFn_convFn _) (convFn_le _ true) (convFn_le _ false))
  cases b
  · exact convFn₂_le_right f g
  · exact convFn₂_le_left f g

/-- **The inequality `convFn₂_le_inf` is strict in general.** The indicator functions of `{0}` and
`{1}` in `ℝ` are both convex; their pointwise minimum is `⊤` at `1 / 2`, while their convex hull —
the indicator function of the segment `[0, 1]` — is `0` there. -/
theorem convFn₂_indicatorFn_lt_inf :
    convFn₂ (indicatorFn ({0} : Set ℝ)) (indicatorFn ({1} : Set ℝ)) (1 / 2) <
      indicatorFn ({0} : Set ℝ) (1 / 2) ⊓ indicatorFn ({1} : Set ℝ) (1 / 2) := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({0} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({1} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have hconv := convex_convexHull ℝ
    (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ)))
  have hmid := hconv (subset_convexHull ℝ _ (Or.inl h0)) (subset_convexHull ℝ _ (Or.inr h1))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpt : ((1 / 2 : ℝ), (0 : ℝ)) ∈
      convexHull ℝ (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ))) := by
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmid
  refine lt_of_le_of_lt (ofEpi_apply_le hpt) ?_
  rw [indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({0} : Set ℝ)),
    indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({1} : Set ℝ))]
  simp

/-! #### The explicit formula for two functions -/

/-- Every convex combination `a • u + b • v = x` bounds the convex hull at `x`: the easy half of the
formula. Only `f, g ≠ ⊥` is needed, not full properness — with `⊥` allowed the right-hand side
can be `⊥` (since `⊥ + ⊤ = ⊥` in `EReal`) while the left-hand side is `⊤`. -/
theorem convFn₂_le_combo (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) {u v x : E} (hx : a • u + b • v = x) :
    convFn₂ f g x ≤ (a : EReal) * f u + (b : EReal) * g v := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    have hxv : v = x := by rw [← hx, hb1]; simp
    subst hb1
    subst hxv
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, zero_add]
    exact convFn₂_le_right f g v
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    have hxu : u = x := by rw [← hx, ha1]; simp
    subst ha1
    subst hxu
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, add_zero]
    exact convFn₂_le_left f g u
  by_cases hS : (a : EReal) * f u + (b : EReal) * g v = ⊤
  · rw [hS]; exact le_top
  have hfu : f u ≠ ⊤ := by
    intro hfu
    exact hS (by rw [hfu, EReal.coe_mul_top_of_pos ha',
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb'.le (hg v))])
  have hgv : g v ≠ ⊤ := by
    intro hgv
    exact hS (by rw [hgv, EReal.coe_mul_top_of_pos hb',
      EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha'.le (hf u))])
  obtain ⟨μ, hμ⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf u) (lt_top_iff_ne_top.2 hfu)
  obtain ⟨ν, hν⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hg v) (lt_top_iff_ne_top.2 hgv)
  have hpt : (x, a * μ + b * ν) ∈ convexHull ℝ (epi f ∪ epi g) := by
    have hmem := convex_convexHull ℝ (epi f ∪ epi g)
      (subset_convexHull ℝ _ (Or.inl (mk_mem_epi.2 hμ.le)))
      (subset_convexHull ℝ _ (Or.inr (mk_mem_epi.2 hν.le))) ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hx] using hmem
  refine (ofEpi_apply_le hpt).trans (le_of_eq ?_)
  rw [hμ, hν, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- The convex hull of two proper convex functions is given by the explicit formula

`(conv {f, g}) x = inf {a f u + b g v | a u + b v = x, a, b ≥ 0, a + b = 1}`,

the infimum over *all* representations, and genuinely an infimum — it need not be attained.

`convFn_apply` proves the same theorem for an arbitrary family and needs only the `≠ ⊥` half of
properness. Here `dom f, dom g ≠ ∅` is used as well, to make the epigraphs non-empty and so turn
the convex hull of their union into a convex join. -/
theorem convFn₂_apply (hf : ConvexFn f) (hg : ConvexFn g) (hf' : Proper f) (hg' : Proper g)
    (x : E) :
    convFn₂ f g x = sInf {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} := by
  have hfe : (epi f).Nonempty := ((dom_eq_fst_image_epi f) ▸ hf'.dom_nonempty).of_image
  have hge : (epi g).Nonempty := ((dom_eq_fst_image_epi g) ▸ hg'.dom_nonempty).of_image
  refine le_antisymm (le_sInf ?_) ?_
  · rintro z ⟨a, b, u, v, ha, hb, hab, hx, rfl⟩
    exact convFn₂_le_combo hf'.ne_bot hg'.ne_bot ha hb hab hx
  · refine le_ofEpi fun μ hμ => ?_
    rw [hf.convex_epi.convexHull_union hg.convex_epi hfe hge] at hμ
    obtain ⟨p, hp, q, hq, a, b, ha, hb, hab, hcombo⟩ := mem_convexJoin.1 hμ
    have hx : a • p.1 + b • q.1 = x := congrArg Prod.fst hcombo
    have hμ2 : a * p.2 + b * q.2 = μ := congrArg Prod.snd hcombo
    have h₁ : (a : EReal) * f p.1 ≤ (a : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hp) (by exact_mod_cast ha)
    have h₂ : (b : EReal) * g q.1 ≤ (b : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hq) (by exact_mod_cast hb)
    have hmem : (a : EReal) * f p.1 + (b : EReal) * g q.1 ∈
        {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
          a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} :=
      ⟨a, b, p.1, q.1, ha, hb, hab, hx, rfl⟩
    refine (sInf_le hmem).trans ?_
    refine (add_le_add h₁ h₂).trans (le_of_eq ?_)
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hμ2]

/-- `conv (f ⊓ g) = conv {f, g}`: both sides are the greatest convex function below `f` and `g`. -/
theorem convHullFn_inf (f g : E → EReal) : convHullFn (f ⊓ g) = convFn₂ f g :=
  le_antisymm
    (le_convFn₂ (convexFn_convHullFn _) ((convHullFn_le _).trans inf_le_left)
      ((convHullFn_le _).trans inf_le_right))
    (le_convHullFn (convexFn_convFn₂ f g) (convFn₂_le_inf f g))

/-! #### When a convex hull of epigraphs is again an epigraph

`epi (convFn₂ f g)` is `conv (epi f ∪ epi g)` only when that hull is epi-like, which is exactly the
statement that the infimum in the formula is attained. Of the two halves of `isEpiLike_iff_forall`
the upward-closure half holds unconditionally; only attainment is at issue. -/

/-- The convex hull of an epi-like set is upward closed in the vertical coordinate: `conv F`
inherits every translation `p ↦ p + (0, t)`, `t ≥ 0`, that `F` itself admits. -/
theorem IsEpiLike.mem_convexHull_of_le {F : Set (E × ℝ)} (hF : IsEpiLike F) {x : E} {μ ν : ℝ}
    (hmem : (x, μ) ∈ convexHull ℝ F) (hμν : μ ≤ ν) : (x, ν) ∈ convexHull ℝ F := by
  have hconv : Convex ℝ ((fun p : E × ℝ => p + ((0 : E), ν - μ)) ⁻¹' convexHull ℝ F) := by
    intro u hu v hv a b ha hb hab
    have hsplit : a • ((0 : E), ν - μ) + b • ((0 : E), ν - μ) = ((0 : E), ν - μ) := by
      rw [← add_smul, hab, one_smul]
    have heq : a • (u + ((0 : E), ν - μ)) + b • (v + ((0 : E), ν - μ))
        = a • u + b • v + ((0 : E), ν - μ) := by
      rw [smul_add, smul_add, add_add_add_comm, hsplit]
    change a • u + b • v + ((0 : E), ν - μ) ∈ convexHull ℝ F
    rw [← heq]
    exact convex_convexHull ℝ F hu hv ha hb hab
  have hsub : convexHull ℝ F ⊆ (fun p : E × ℝ => p + ((0 : E), ν - μ)) ⁻¹' convexHull ℝ F := by
    refine convexHull_min (fun p hp => ?_) hconv
    change p + ((0 : E), ν - μ) ∈ convexHull ℝ F
    refine subset_convexHull ℝ F ?_
    have hpair : p + ((0 : E), ν - μ) = (p.1, p.2 + (ν - μ)) := Prod.ext (by simp) (by simp)
    rw [hpair]
    exact hF.mem_of_le (x := p.1) (μ := p.2) hp (by linarith)
  have hres := hsub hmem
  change ((x, μ) : E × ℝ) + ((0 : E), ν - μ) ∈ convexHull ℝ F at hres
  have hval : μ + (ν - μ) = ν := by ring
  have hxy : ((x, μ) : E × ℝ) + ((0 : E), ν - μ) = (x, ν) := by
    rw [Prod.mk_add_mk, add_zero, hval]
  rwa [hxy] at hres

/-- The binary case of `epi_convFn`. -/
theorem epi_convFn₂ (hF : IsEpiLike (convexHull ℝ (epi f ∪ epi g))) :
    epi (convFn₂ f g) = convexHull ℝ (epi f ∪ epi g) :=
  epi_ofEpi hF

end Binary

end Module

/-! ### The explicit formula in general -/

section Formula

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- The convex hull of a family of convex functions, none of which takes the value `⊥`, is given by
the explicit formula

`(conv {f i}) x = inf {∑ λ i * f i (x i) | ∑ λ i • x i = x}`,

the infimum being over all representations of `x` as a convex combination of points `x i`, with
only finitely many non-zero coefficients.

The classical statement assumes the `f i` proper; only the `≠ ⊥` half is used, twice — it keeps
`λ i * f i (x i)` from being `−∞` where `λ i = 0`, and it turns a finite bound on the sum into a
finite bound on each term. `dom (f i) ≠ ∅` does no work, exactly as for sums.

The description of a convex hull by convex combinations presents a point of the hull as drawn from
the `epi (f i)` *with repetitions*, whereas the infimum here ranges over one point per index. The
proof of `≥` bridges the two by merging the points drawn from a single `epi (f i)` into their
center of mass, which is the only use made of convexity of the `f i`. -/
theorem convFn_apply {f : ι → E → EReal} (hf : ∀ i, ConvexFn (f i)) (hf' : ∀ i x, f i x ≠ ⊥)
    (x : E) :
    convFn f x = sInf {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
      (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
        z = ∑ i ∈ t, (w i : EReal) * f i (p i)} := by
  classical
  refine le_antisymm (le_sInf ?_) ?_
  -- **`≤`**: the convex hull is below the value of every representation of `x`.
  · rintro z ⟨t, w, p, hw₀, hw₁, hwx, rfl⟩
    by_cases htop : ∑ i ∈ t, (w i : EReal) * f i (p i) = ⊤
    · rw [htop]; exact le_top
    have hbot : ∀ i ∈ t, (w i : EReal) * f i (p i) ≠ ⊥ := fun i hi =>
      EReal.coe_mul_ne_bot (hw₀ i hi) (hf' i (p i))
    have hnetop := EReal.forall_ne_top_of_sum_ne_top t _ hbot htop
    -- discard the indices carrying zero weight, whose points need not lie in `dom (f i)`
    set t' : Finset ι := t.filter (fun i => 0 < w i) with ht'def
    have hsub : t' ⊆ t := Finset.filter_subset _ _
    have hzero : ∀ i ∈ t, i ∉ t' → w i = 0 := by
      intro i hi hi'
      rcases eq_or_lt_of_le (hw₀ i hi) with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.2 ⟨hi, h⟩) hi'
    have hw₁' : ∑ i ∈ t', w i = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
    have hwx' : ∑ i ∈ t', w i • p i = x := by
      rw [Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]]; exact hwx
    obtain ⟨μ, hμ⟩ : ∃ μ : ι → ℝ, ∀ i ∈ t', f i (p i) = (μ i : EReal) := by
      refine ⟨fun i => (f i (p i)).toReal, fun i hi => ?_⟩
      have hpos : 0 < w i := (Finset.mem_filter.1 hi).2
      have hne : f i (p i) ≠ ⊤ := fun hcon =>
        hnetop i (hsub hi) (by rw [hcon, EReal.coe_mul_top_of_pos hpos])
      exact (EReal.coe_toReal hne (hf' i (p i))).symm
    have hcm := Finset.centerMass_mem_convexHull t'
      (fun i hi => ((Finset.mem_filter.1 hi).2).le) (by rw [hw₁']; exact zero_lt_one)
      (z := fun i => ((p i, μ i) : E × ℝ))
      (fun i hi => mem_iUnion.2 ⟨i, mk_mem_epi.2 (le_of_eq (hμ i hi))⟩)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁'] at hcm
    have hsplit : ∑ i ∈ t', w i • ((p i, μ i) : E × ℝ) = (x, ∑ i ∈ t', w i * μ i) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]; simpa using hwx'
      · rw [Prod.snd_sum]; simp [smul_eq_mul]
    rw [hsplit] at hcm
    refine (ofEpi_apply_le hcm).trans (le_of_eq ?_)
    rw [EReal.coe_sum,
      ← Finset.sum_subset hsub (fun i hi hi' => by rw [hzero i hi hi']; simp)]
    exact Finset.sum_congr rfl fun i hi => by rw [hμ i hi, ← EReal.coe_mul]
  -- **`≥`**: every point of the convex hull of the union comes from a representation.
  · refine le_ofEpi fun ν hν => ?_
    rw [convexHull_eq] at hν
    obtain ⟨κ, s, w, z, hw₀, hw₁, hz, hcm⟩ := hν
    set s' : Finset κ := s.filter (fun j => 0 < w j) with hs'def
    have hsub : s' ⊆ s := Finset.filter_subset _ _
    have hwpos : ∀ j ∈ s', 0 < w j := fun j hj => (Finset.mem_filter.1 hj).2
    have hzero : ∀ j ∈ s, j ∉ s' → w j = 0 := by
      intro j hj hj'
      rcases eq_or_lt_of_le (hw₀ j hj) with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.2 ⟨hj, h⟩) hj'
    have hw₁' : ∑ j ∈ s', w j = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
    have hcm' : ∑ j ∈ s', w j • z j = (x, ν) := by
      rw [Finset.sum_subset hsub fun j hj hj' => by rw [hzero j hj hj', zero_smul],
        ← Finset.centerMass_eq_of_sum_1 _ _ hw₁]
      exact hcm
    -- choose, for each point of the combination, an index whose epigraph it belongs to
    obtain ⟨j₀, hj₀⟩ : s'.Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [hw₁']; exact one_ne_zero)
    obtain ⟨i₀, -⟩ := mem_iUnion.1 (hz j₀ (hsub hj₀))
    have hchoice : ∀ j : κ, ∃ i : ι, j ∈ s' → z j ∈ epi (f i) := by
      intro j
      by_cases hj : j ∈ s'
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (hz j (hsub hj))
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun hcon => absurd hcon hj⟩
    choose σ hσ using hchoice
    -- merge the points drawn from one and the same epigraph into their center of mass
    obtain ⟨W, hW⟩ : ∃ W : ι → ℝ, ∀ i, W i = ∑ j ∈ s' with σ j = i, w j := ⟨_, fun _ => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ι → E × ℝ,
        ∀ i, Q i = (s'.filter fun j => σ j = i).centerMass w z := ⟨_, fun _ => rfl⟩
    have hmaps : ∀ j ∈ s', σ j ∈ s'.image σ := fun j hj => Finset.mem_image_of_mem σ hj
    have hWpos : ∀ i ∈ s'.image σ, 0 < W i := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [hW]
      exact Finset.sum_pos (fun k hk => hwpos k (Finset.mem_filter.1 hk).1)
        ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩
    have hQmem : ∀ i ∈ s'.image σ, Q i ∈ epi (f i) := by
      intro i hi
      rw [hQ]
      refine (hf i).convex_epi.centerMass_mem
        (fun j hj => (hwpos j (Finset.mem_filter.1 hj).1).le) ?_ (fun j hj => ?_)
      · have := hWpos i hi; rwa [hW] at this
      · obtain ⟨hj₁, hj₂⟩ := Finset.mem_filter.1 hj
        exact hj₂ ▸ hσ j hj₁
    have hWsum : ∑ i ∈ s'.image σ, W i = 1 := by
      simp only [hW]
      rw [Finset.sum_fiberwise_of_maps_to hmaps w]
      exact hw₁'
    have hQsum : ∑ i ∈ s'.image σ, W i • Q i = (x, ν) := by
      have hstep : ∀ i ∈ s'.image σ, W i • Q i = ∑ j ∈ s' with σ j = i, w j • z j := by
        intro i hi
        have hWi : (∑ j ∈ s' with σ j = i, w j) ≠ 0 := by
          have hpos := hWpos i hi
          rw [hW] at hpos
          exact hpos.ne'
        rw [hQ, Finset.centerMass, hW, smul_inv_smul₀ hWi]
      rw [Finset.sum_congr rfl hstep,
        Finset.sum_fiberwise_of_maps_to hmaps (fun j => w j • z j)]
      exact hcm'
    have hx' : ∑ i ∈ s'.image σ, W i • (Q i).1 = x := by
      have hfst := congrArg Prod.fst hQsum
      rw [Prod.fst_sum] at hfst
      simpa using hfst
    have hν' : ∑ i ∈ s'.image σ, W i * (Q i).2 = ν := by
      have hsnd := congrArg Prod.snd hQsum
      rw [Prod.snd_sum] at hsnd
      simpa [smul_eq_mul] using hsnd
    have hval : ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1) ≤ (ν : EReal) := by
      calc ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)
          ≤ ∑ i ∈ s'.image σ, (W i : EReal) * (((Q i).2 : ℝ) : EReal) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (mem_epi.1 (hQmem i hi))
              (by exact_mod_cast (hWpos i hi).le)
        _ = ((∑ i ∈ s'.image σ, W i * (Q i).2 : ℝ) : EReal) := by
            rw [EReal.coe_sum]
            exact Finset.sum_congr rfl fun i _ => EReal.coe_mul _ _
        _ = (ν : EReal) := by rw [hν']
    have hmemS : (∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)) ∈
        {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
          (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
            z = ∑ i ∈ t, (w i : EReal) * f i (p i)} :=
      ⟨s'.image σ, W, fun i => (Q i).1, fun i hi => (hWpos i hi).le, hWsum, hx', rfl⟩
    exact (sInf_le hmemS).trans hval

end Formula

/-! ### Closedness supplies the missing half -/

section Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {f g : E → EReal}

/-- A **closed** convex hull of two epigraphs is an epigraph: `IsEpiLike.mem_convexHull_of_le`
gives upward closure unconditionally and closedness gives attainment of the vertical infima. So the
only way `conv (epi f ∪ epi g)` can fail to be an epigraph is by failing to be closed, which turns
the closedness criteria for convex hulls into attainment statements for that infimum. -/
theorem isEpiLike_convexHull_epi_union (hc : IsClosed (convexHull ℝ (epi f ∪ epi g))) :
    IsEpiLike (convexHull ℝ (epi f ∪ epi g)) :=
  IsEpiLike.of_isClosed (fun _ _ _ hmem hle =>
    ((isEpiLike_epi f).union (isEpiLike_epi g)).mem_convexHull_of_le hmem hle) hc

end Topology

end ConvexAnalysis
