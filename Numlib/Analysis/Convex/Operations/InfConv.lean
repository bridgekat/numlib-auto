import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# Infimal convolution

The functional operation `f □ g` corresponding to addition of epigraphs: the function determined by
`epi f + epi g`. It is convex whenever `f` and `g` are, and it is dual to pointwise addition of
convex functions under conjugacy.

`f □ g` is *defined* as `ofEpi (epi f + epi g)`, not by the classical formula
`(f □ g) x = ⨅ y, f (x - y) + g y`, which is ill-formed as soon as one function reaches `⊤` where
the other reaches `⊥`: for `f ≡ ⊤` and `g 0 = ⊥`, `epi f + epi g = ∅` so the left side is `⊤` and
the right side `⊤ + ⊥ = ⊥`. `infConv_apply` recovers the formula under `f, g ≠ ⊥`; since that
example uses only one `⊤` value and one `⊥` value, a single such hypothesis will not do.

## Main definitions

* `infConv f g` — the infimal convolute `f □ g`.
* `InfConvFn E` — the type synonym `E → EReal` carrying `□` as its addition, so that
  `f₁ □ ⋯ □ fₘ` is a `Finset.sum`. A synonym is forced, since `E → EReal` already carries the
  pointwise `+` that `□` is dual to; additive notation is right, `□` being addition of epigraphs.

## Main results

* `convexFn_infConv` — `□` preserves convexity; `convexFn_sum_toInfConvFn` is the m-ary form.
* `infConv_apply`, `infConv_le_add` — the classical infimum formula and its inequality half;
  `sum_toInfConvFn_apply_le`, `sum_toInfConvFn_le_sum` are the m-ary versions.
* `dom_infConv` — `dom (f □ g) = dom f + dom g`, with no hypothesis at all.
* `InfConvFn.instAddCommMonoid` — `□` is commutative and associative with identity `δ(· | 0)`;
  `infConv_indicatorFn_singleton` translates the graph of `f` by `a`.
* `subset_epi_infConv`, `epi_infConv` — `epi f + epi g ⊆ epi (f □ g)` always; equality needs
  `IsEpiLike (epi f + epi g)`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### The definition and its epigraph -/

section Basic

variable {E : Type*} [AddCommGroup E] {f g f₁ f₂ g₁ g₂ : E → EReal} {y z : E} {ν ρ : ℝ}

/-- **Infimal convolution** `f □ g`, defined by addition of epigraphs rather than by the infimum
formula `(f □ g) x = ⨅ y, f (x - y) + g y`, which is ill-formed when `f` or `g` takes the value
`⊥`. The formula is `infConv_apply`. -/
noncomputable def infConv (f g : E → EReal) : E → EReal := ofEpi (epi f + epi g)

theorem infConv_def (f g : E → EReal) : infConv f g = ofEpi (epi f + epi g) := rfl

theorem subset_epi_infConv (f g : E → EReal) : epi f + epi g ⊆ epi (infConv f g) :=
  subset_epi_ofEpi _

/-- Rockafellar's description of `epi (f □ g)`, under the hypothesis that makes it true.

The hypothesis is not removable: a sum of epigraphs need not be an epigraph. On `ℝ` take
`f x = 1/x` for `x > 0` and `⊤` otherwise, and `g ≡ 0`; both are convex, every vertical section of
`epi f + epi g` is `Ioi 0`, so the sum is `ℝ ×ˢ Ioi 0`, whereas `f □ g ≡ 0` has epigraph
`ℝ ×ˢ Ici 0`. -/
theorem epi_infConv (h : IsEpiLike (epi f + epi g)) : epi (infConv f g) = epi f + epi g :=
  epi_ofEpi h

/-- Vertical sections of a sum of epigraphs are upward closed: the half of `IsEpiLike` that holds
unconditionally, closedness having to supply the other. -/
theorem mem_epi_add_epi_of_le {x : E} {μ ν : ℝ} (h : ((x, μ) : E × ℝ) ∈ epi f + epi g)
    (hμν : μ ≤ ν) : ((x, ν) : E × ℝ) ∈ epi f + epi g := by
  obtain ⟨⟨y', a⟩, h₁, ⟨z', b⟩, h₂, heq⟩ := h
  have hy : y' + z' = x := congrArg Prod.fst heq
  have hab : a + b = μ := congrArg Prod.snd heq
  refine ⟨(y', a), h₁, (z', b + (ν - μ)), mk_mem_epi.2 ?_, ?_⟩
  · exact (mk_mem_epi.1 h₂).trans (by exact_mod_cast (by linarith : b ≤ b + (ν - μ)))
  · change ((y', a) : E × ℝ) + (z', b + (ν - μ)) = (x, ν)
    rw [Prod.mk_add_mk, hy, show a + (b + (ν - μ)) = ν by linarith]

/-- The basic upper bound, phrased inside the epigraphs so that no `∞ - ∞` can arise. -/
theorem infConv_apply_le (hy : f y ≤ (ν : EReal)) (hz : g z ≤ (ρ : EReal)) :
    infConv f g (y + z) ≤ ((ν + ρ : ℝ) : EReal) := by
  refine ofEpi_apply_le ?_
  have hmem : ((y, ν) : E × ℝ) + (z, ρ) ∈ epi f + epi g :=
    Set.add_mem_add (mk_mem_epi.2 hy) (mk_mem_epi.2 hz)
  rwa [Prod.mk_add_mk] at hmem

/-! ### The effective domain -/

/-- `dom (f □ g) = dom f + dom g`, with no hypothesis, unlike `dom_add` for pointwise addition:
`dom` is the projection of the epigraph, and projection is an additive hom. -/
theorem dom_infConv (f g : E → EReal) : dom (infConv f g) = dom f + dom g := by
  rw [infConv_def, dom_ofEpi, dom_eq_fst_image_epi f, dom_eq_fst_image_epi g]
  exact Set.image_add (AddMonoidHom.fst E ℝ)

/-! ### The infimum formula -/

/-- `(f □ g) x ≤ f (x - y) + g y`. Both `≠ ⊥` hypotheses are needed: without them the right side
can be `⊤ + ⊥ = ⊥` while the left is `⊤`. -/
theorem infConv_le_add (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x y : E) :
    infConv f g x ≤ f (x - y) + g y := by
  rcases eq_top_or_lt_top (f (x - y)) with h1 | h1
  · rw [h1, _root_.EReal.top_add_of_ne_bot (hg y)]
    exact le_top
  rcases eq_top_or_lt_top (g y) with h2 | h2
  · rw [h2, _root_.EReal.add_top_of_ne_bot (hf (x - y))]
    exact le_top
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf (x - y)) h1
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg y) h2
  rw [hp, hq, ← _root_.EReal.coe_add]
  simpa using infConv_apply_le (f := f) (g := g) hp.le hq.le

/-- **Rockafellar's formula for `□`**: `(f □ g) x = ⨅ y, f (x - y) + g y`, "analogous to the
classical formula for integral convolution". The `≠ ⊥` hypotheses make the right side meaningful. -/
theorem infConv_apply (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x : E) :
    infConv f g x = ⨅ y, f (x - y) + g y := by
  refine le_antisymm (le_iInf fun y => infConv_le_add hf hg x y) (le_ofEpi fun μ hμ => ?_)
  obtain ⟨⟨a, ν⟩, ha, ⟨b, ρ⟩, hb, hab⟩ := Set.mem_add.1 hμ
  rw [Prod.mk_add_mk, Prod.mk.injEq] at hab
  refine le_trans (iInf_le (fun y => f (x - y) + g y) b) ?_
  rw [← hab.1, add_sub_cancel_right, ← hab.2, _root_.EReal.coe_add]
  exact add_le_add (mk_mem_epi.1 ha) (mk_mem_epi.1 hb)

/-! ### Commutativity, associativity, monotonicity -/

theorem infConv_comm (f g : E → EReal) : infConv f g = infConv g f := by
  rw [infConv_def, infConv_def, add_comm]

/-- Enlarging a summand from `F` to the epigraph it determines does not move the lower boundary of
the sum: the points `epi (ofEpi F)` adds are limits from above of points of `F`. This is what makes
`□` associative. -/
theorem epi_ofEpi_add_subset (F G : Set (E × ℝ)) :
    epi (ofEpi F) + G ⊆ epi (ofEpi (F + G)) := by
  rintro p hp
  obtain ⟨⟨w, μ⟩, hwμ, ⟨u, σ⟩, huσ, rfl⟩ := Set.mem_add.1 hp
  rw [Prod.mk_add_mk]
  refine mk_mem_epi.2 (EReal.le_coe_of_forall_lt fun q hq => ?_)
  have hlt : ofEpi F w < ((μ + (q - (μ + σ)) : ℝ) : EReal) :=
    lt_of_le_of_lt (mk_mem_epi.1 hwμ)
      (by exact_mod_cast (by linarith : μ < μ + (q - (μ + σ))))
  obtain ⟨τ, hτF, hτ⟩ := ofEpi_lt_iff.1 hlt
  have hmem : ((w, τ) : E × ℝ) + (u, σ) ∈ F + G := Set.add_mem_add hτF huσ
  rw [Prod.mk_add_mk] at hmem
  refine lt_of_le_of_lt (ofEpi_apply_le hmem) ?_
  have hτ' : τ < μ + (q - (μ + σ)) := by exact_mod_cast hτ
  exact_mod_cast (by linarith : τ + σ < q)

theorem infConv_ofEpi_left (F : Set (E × ℝ)) (g : E → EReal) :
    infConv (ofEpi F) g = ofEpi (F + epi g) := by
  refine le_antisymm (ofEpi_mono (Set.add_subset_add_right (subset_epi_ofEpi F))) ?_
  exact subset_epi_iff_le_ofEpi.1 (epi_ofEpi_add_subset F (epi g))

theorem infConv_ofEpi_right (f : E → EReal) (G : Set (E × ℝ)) :
    infConv f (ofEpi G) = ofEpi (epi f + G) := by
  rw [infConv_comm, infConv_ofEpi_left, add_comm]

/-- `□` is associative. Not a direct consequence of associativity of set addition: `epi (f □ g)` is
larger than `epi f + epi g` in general, and `epi_ofEpi_add_subset` closes the gap. -/
theorem infConv_assoc (f g h : E → EReal) :
    infConv (infConv f g) h = infConv f (infConv g h) := by
  rw [infConv_def f g, infConv_def g h, infConv_ofEpi_left, infConv_ofEpi_right, add_assoc]

theorem infConv_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : infConv f₁ g₁ ≤ infConv f₂ g₂ :=
  ofEpi_mono (Set.add_subset_add (epi_anti hf) (epi_anti hg))

/-! ### Indicator functions: the identity element and translation -/

/-- Adding the epigraph of `δ(· | a)` — the half-cylinder `{a} ×ˢ Ici 0` — translates an epigraph
horizontally by `a`. Unlike a general sum of epigraphs, this one *is* an epigraph. -/
theorem epi_add_epi_indicatorFn_singleton (f : E → EReal) (a : E) :
    epi f + epi (indicatorFn ({a} : Set E)) = epi fun x => f (x - a) := by
  rw [epi_indicatorFn]
  ext p
  constructor
  · intro hp
    obtain ⟨⟨w, ν'⟩, hw, ⟨u, σ⟩, hu, rfl⟩ := Set.mem_add.1 hp
    have hu1 : u = a := hu.1
    have hu2 : (0 : ℝ) ≤ σ := hu.2
    subst hu1
    rw [Prod.mk_add_mk]
    refine mk_mem_epi.2 ?_
    rw [add_sub_cancel_right]
    exact (mk_mem_epi.1 hw).trans (by exact_mod_cast (by linarith : ν' ≤ ν' + σ))
  · intro hp
    obtain ⟨w, μ⟩ := p
    have hmem : ((w - a, μ) : E × ℝ) + (a, 0) ∈ epi f + ({a} ×ˢ Ici (0 : ℝ)) :=
      Set.add_mem_add (mk_mem_epi.2 (mk_mem_epi.1 hp)) ⟨rfl, le_refl (0 : ℝ)⟩
    simpa using hmem

/-- `f □ δ(· | a)` translates the graph of `f` horizontally by `a`. -/
theorem infConv_indicatorFn_singleton (f : E → EReal) (a : E) :
    infConv f (indicatorFn ({a} : Set E)) = fun x => f (x - a) := by
  rw [infConv_def, epi_add_epi_indicatorFn_singleton, ofEpi_epi]

/-- **`δ(· | 0)` is the identity element for `□`.** -/
@[simp] theorem infConv_indicatorFn_zero (f : E → EReal) :
    infConv f (indicatorFn ({0} : Set E)) = f := by
  simpa using infConv_indicatorFn_singleton f 0

@[simp] theorem indicatorFn_zero_infConv (f : E → EReal) :
    infConv (indicatorFn ({0} : Set E)) f = f := by
  rw [infConv_comm, infConv_indicatorFn_zero]

/-- If `g` is nonpositive at the origin then `f □ g ≤ f`, since `δ(· | 0)` dominates such a `g`. -/
theorem infConv_le_left (f : E → EReal) (hg : g 0 ≤ 0) : infConv f g ≤ f := by
  refine le_of_le_of_eq (infConv_mono (le_refl f) ?_) (infConv_indicatorFn_zero f)
  intro w
  by_cases hw : w = 0
  · subst hw
    simpa using hg
  · have hw' : w ∉ ({0} : Set E) := fun hmem => hw hmem
    simp [hw']

theorem infConv_le_right (hf : f 0 ≤ 0) (g : E → EReal) : infConv f g ≤ g := by
  rw [infConv_comm]
  exact infConv_le_left g hf

end Basic

/-! ### Convexity of an infimal convolute -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → EReal}

/-- The infimal convolute of two convex functions is convex. No properness is needed: the
classical hypothesis only makes the infimum formula meaningful, and the epigraph definition
does not use it. -/
theorem convexFn_infConv (hf : ConvexFn f) (hg : ConvexFn g) : ConvexFn (infConv f g) :=
  convexFn_ofEpi (hf.convex_epi.add hg.convex_epi)

end Module

/-! ### `□` as a commutative monoid -/

/-- `E → EReal`, carrying infimal convolution as its addition and `δ(· | 0)` as its zero;
`∑ i ∈ s, toInfConvFn (f i)` is Rockafellar's `f₁ □ ⋯ □ fₘ`. -/
def InfConvFn (E : Type*) : Type _ := E → EReal

/-- A function `E → EReal`, regarded as an element of the infimal-convolution monoid. -/
def toInfConvFn {E : Type*} (f : E → EReal) : InfConvFn E := f

/-- An element of the infimal-convolution monoid, regarded as a function `E → EReal`. -/
def ofInfConvFn {E : Type*} (F : InfConvFn E) : E → EReal := F

@[simp] theorem ofInfConvFn_toInfConvFn {E : Type*} (f : E → EReal) :
    ofInfConvFn (toInfConvFn f) = f := rfl

@[simp] theorem toInfConvFn_ofInfConvFn {E : Type*} (F : InfConvFn E) :
    toInfConvFn (ofInfConvFn F) = F := rfl

section Monoid

variable {E : Type*} [AddCommGroup E]

/-- Infimal convolution is the addition of `InfConvFn E`. -/
noncomputable instance InfConvFn.instAdd : Add (InfConvFn E) := ⟨infConv⟩

/-- `δ(· | 0)` is the zero of `InfConvFn E`. -/
noncomputable instance InfConvFn.instZero : Zero (InfConvFn E) := ⟨indicatorFn {0}⟩

@[simp] theorem toInfConvFn_add (f g : E → EReal) :
    toInfConvFn f + toInfConvFn g = toInfConvFn (infConv f g) := rfl

@[simp] theorem toInfConvFn_indicatorFn_zero :
    toInfConvFn (indicatorFn ({0} : Set E)) = 0 := rfl

@[simp] theorem ofInfConvFn_add (F G : InfConvFn E) :
    ofInfConvFn (F + G) = infConv (ofInfConvFn F) (ofInfConvFn G) := rfl

@[simp] theorem ofInfConvFn_zero :
    ofInfConvFn (0 : InfConvFn E) = indicatorFn ({0} : Set E) := rfl

/-- `E → EReal` is a commutative monoid under `□`, with identity `δ(· | 0)`. -/
noncomputable instance InfConvFn.instAddCommMonoid : AddCommMonoid (InfConvFn E) where
  add := (· + ·)
  zero := 0
  add_assoc := infConv_assoc
  zero_add := indicatorFn_zero_infConv
  add_zero := infConv_indicatorFn_zero
  add_comm := infConv_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

end Monoid

section MonoidConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Convexity in m-ary form: `f₁ □ ⋯ □ fₘ` is convex whenever `f₁, …, fₘ` are. The empty case is
`δ(· | 0)`, which is convex because `{0}` is. -/
theorem convexFn_sum_toInfConvFn {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) :
    ConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  induction s using Finset.cons_induction with
  | empty => simpa using convexFn_indicatorFn.2 (convex_singleton (0 : E))
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    simp only [ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact convexFn_infConv (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))

end MonoidConvex

section MonoidSum

variable {ι E : Type*} [AddCommGroup E] {s : Finset ι} {g : ι → E → EReal}

/-- **The `m`-ary basic upper bound**, `infConv_apply_le` iterated; no hypothesis is needed. -/
theorem sum_toInfConvFn_apply_le {y : ι → E} {c : ι → ℝ}
    (h : ∀ i ∈ s, g i (y i) ≤ (c i : EReal)) :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (g i)) (∑ i ∈ s, y i) ≤ ((∑ i ∈ s, c i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, ofInfConvFn_zero,
      indicatorFn_of_mem (s := ({0} : Set E)) (Set.mem_singleton_iff.2 rfl)]
    exact_mod_cast le_rfl
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ofInfConvFn_add,
      ofInfConvFn_toInfConvFn]
    exact infConv_apply_le (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- **The `m`-ary infimum bound**: `(g₁ □ ⋯ □ gₘ) (y₁ + ⋯ + yₘ) ≤ g₁ y₁ + ⋯ + gₘ yₘ`. The `≠ ⊥`
hypothesis sits on each `gᵢ` separately, never on a partial convolute: `□` does not preserve
`≠ ⊥`, since `g₁ x = -x` and `g₂ x = x` are everywhere finite with `g₁ □ g₂ ≡ -∞`. -/
theorem sum_toInfConvFn_le_sum (hg : ∀ i ∈ s, ∀ x, g i x ≠ ⊥) (y : ι → E) :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (g i)) (∑ i ∈ s, y i) ≤ ∑ i ∈ s, g i (y i) := by
  rcases eq_or_ne (∑ i ∈ s, g i (y i)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hfin : ∀ i ∈ s, g i (y i) ≠ ⊤ :=
    EReal.forall_ne_top_of_sum_ne_top s _ (fun i hi => hg i hi (y i)) htop
  have hci : ∀ i ∈ s, g i (y i) = (((g i (y i)).toReal : ℝ) : EReal) := fun i hi =>
    (_root_.EReal.coe_toReal (hfin i hi) (hg i hi (y i))).symm
  have hsum : ∑ i ∈ s, g i (y i) = ((∑ i ∈ s, (g i (y i)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl hci
  rw [hsum]
  exact sum_toInfConvFn_apply_le fun i hi => (hci i hi).le

/-- `dom (g₁ □ ⋯ □ gₘ) = dom g₁ + ⋯ + dom gₘ`, with no hypothesis; the empty convolute is
`δ(· | 0)`, whose domain `{0}` is the empty sum of sets. -/
theorem dom_sum_toInfConvFn (s : Finset ι) (g : ι → E → EReal) :
    dom (ofInfConvFn (∑ i ∈ s, toInfConvFn (g i))) = ∑ i ∈ s, dom (g i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ofInfConvFn_zero, dom_indicatorFn,
      Set.singleton_zero]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn, dom_infConv,
      ih]

end MonoidSum

end ConvexAnalysis
