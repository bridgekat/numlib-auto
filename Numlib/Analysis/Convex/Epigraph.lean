import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Numlib.Order.EReal

/-!
# Extended-real-valued convex and concave functions

The basic theory of convex functions `f : E → EReal` on a real vector space, and of their concave
counterparts `g : E → EReal`. Convexity is *defined* geometrically, as convexity of the epigraph,
rather than by the inequality `f (a • x + b • y) ≤ a * f x + b * f y`: the right-hand side can be
the undefined `∞ - ∞` when `f` takes both infinite values, and improper functions are admitted
throughout. The epigraph lives in `E × ℝ`, not `E × EReal` — the second coordinate ranges over the
*reals*, unlike Mathlib's `ConvexOn.convex_epigraph`, which uses the codomain of the function.
Concavity is defined in the same way, as convexity of the hypograph; `-g` appears only in the sign
dictionary. Rockafellar mixes the two theories constantly from Part VI on, so the concave notions
need first-class names rather than being spelled `ConvexFn (-g)` at every use.

**Naming.** Where mathematics has a natural dual word, the two sides use it: `epi`/`hypo`,
`ConvexFn`/`ConcaveFn`, `infConv`/`supConv`, and downstream `lscHull`/`uscHull` and
`subdifferential`/`superdifferential`. Elsewhere both sides are marked with the same pattern:
`convexDom`/`concaveDom`, `ProperConvex`/`ProperConcave`, `convexRestrict`/`concaveRestrict`, and
downstream `convexCl`/`concaveCl`, `ClosedConvex`/`ClosedConcave`, `convexConj`/`concaveConj`.
Lemma names carry these tokens (`mem_convexDom`, `closedConvex_iff`). Each concave declaration sits
right after its convex twin, and is proved from it through the sign dictionary where that is not
longer than a direct proof.

Sign transfer is not free on `EReal`, because negation does not distribute over addition:
`-(⊥ + ⊤) = ⊤` while `(-⊥) + (-⊤) = ⊥`. This is why `concaveFn_iff_le` needs `∀ x, g x ≠ ⊤`,
mirroring the `∀ x, f x ≠ ⊥` of `convexFn_iff_le`, while `concaveFn_iff_convexFn_neg`, which never
forms a sum, needs no hypothesis at all.

## Main definitions

* `epi f`, `hypo g` — the epigraph of `f` and the hypograph of `g`, subsets of `E × ℝ`.
  Rockafellar writes `epi g` for the hypograph too, overloading the notation; we do not.
* `convexDom f` — the effective domain of `f`, where `f < ⊤`; `concaveDom g`, where `g > ⊥`.
* `ProperConvex f` — `f` is finite somewhere and never `⊥`; `ProperConcave g` — finite somewhere and
  never `⊤`.
* `convexRestrict s f` — `f` restricted to `s`, extended by `⊤`; `concaveRestrict s g`, extended by
  `⊥`.
* `ConvexFn f` — `f` is convex, meaning that `epi f` is a convex set; `ConcaveFn g` — `hypo g` is
  convex.
* `scaleSnd c` — the vertical scaling `(x, μ) ↦ (x, c μ)` of `E × ℝ`, which is how a scalar
  multiple of `f` acts on epigraphs.

## Main results

* `hypo_neg`, `epi_neg`, `concaveDom_eq_convexDom_neg`, `properConcave_iff_properConvex_neg`,
  `concaveFn_iff_convexFn_neg` — the sign dictionary: "`g` is concave when `-g` is convex",
  recovered as a theorem, together with the transfer of domains and properness.
* `convexFn_iff_forall_lt`, `concaveFn_iff_forall_gt` — convexity and concavity by strict
  inequalities: the form that avoids `∞ - ∞` entirely.
* `convexFn_iff_le` — the familiar inequality, valid when `f` never takes `⊥`; `concaveFn_iff_le`,
  when `g` never takes `⊤`.
* `convexFn_add_coe`, `ConvexFn.comp_add_left` — adding a real-valued affine coordinate, and
  translating the argument, preserve convexity.
* `ConvexFn.convex_lt`, `ConvexFn.convex_le`, `ConvexFn.convex_convexDom` — sublevel sets and the
  effective domain of a convex function are convex; `ConcaveFn.convex_gt`, `ConcaveFn.convex_ge`,
  `ConcaveFn.convex_concaveDom` for superlevel sets.
* `convexFn_coe_mul`, `convexDom_coe_mul`, `properConvex_coe_mul` — a non-negative multiple `cf`.
* `convexOn_iff_convexFn`, `concaveOn_iff_concaveFn` — the bridges to Mathlib's `ConvexOn` and
  `ConcaveOn`; with them the dictionary between real-valued and `EReal`-valued functions:
  `convexDom_coe`, `properConvex_coe`, `convexDom_convexRestrict_coe`,
  `properConvex_convexRestrict_coe`, `ConvexOn.convexFn_convexRestrict_coe`,
  `ConvexOn.convexFn_coe`, and their concave twins.
* `ConvexFn.sum_le` — Jensen's inequality for a finite convex combination.

## References

* [rockafellar1970convex] §4, and §30 for the concave conventions.
-/

open Set

namespace ConvexAnalysis

/-! ### Epigraphs, hypographs, domains, properness -/

section Basic

variable {E : Type*}

/-- The epigraph of `f : E → EReal`, `{(x, μ) | μ ∈ ℝ, f x ≤ μ} ⊆ E × ℝ`. The second coordinate
ranges over the *reals*, not over `EReal`. -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

@[simp]
theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal) := Iff.rfl

theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal) := Iff.rfl

/-- The hypograph of `g : E → EReal`, `{(x, μ) | μ ∈ ℝ, μ ≤ g x} ⊆ E × ℝ`. Rockafellar writes this
`epi g`, reusing the epigraph notation; we keep the two names apart. As with `epi`, the second
coordinate ranges over the *reals*. -/
def hypo (g : E → EReal) : Set (E × ℝ) := {p | (p.2 : EReal) ≤ g p.1}

@[simp]
theorem mem_hypo {g : E → EReal} {p : E × ℝ} : p ∈ hypo g ↔ (p.2 : EReal) ≤ g p.1 := Iff.rfl

theorem mk_mem_hypo {g : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ hypo g ↔ (μ : EReal) ≤ g x := Iff.rfl

/-- `epi` is **antitone**: a larger function has a smaller epigraph. -/
theorem epi_anti {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f := fun _ hp => (h _).trans hp

/-- The epigraph determines the function: `f ≤ g` exactly when `epi g ⊆ epi f`. -/
theorem le_iff_epi_subset {f g : E → EReal} : f ≤ g ↔ epi g ⊆ epi f := by
  refine ⟨epi_anti, fun h x => ?_⟩
  by_contra hx
  obtain ⟨q, hgq, hqf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (h (show (x, q) ∈ epi g from hgq.le)) (not_le.2 hqf)

/-- The hypograph is monotone in the function, where the epigraph is antitone. -/
theorem hypo_mono {g h : E → EReal} (hgh : g ≤ h) : hypo g ⊆ hypo h := fun _ hp => hp.trans (hgh _)

/-- The hypograph determines the function: `g ≤ h` exactly when `hypo g ⊆ hypo h`. -/
theorem le_iff_hypo_subset {g h : E → EReal} : g ≤ h ↔ hypo g ⊆ hypo h := by
  refine ⟨hypo_mono, fun hs x => ?_⟩
  by_contra hx
  obtain ⟨q, hhq, hqg⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (hs (show (x, q) ∈ hypo g from hqg.le)) (not_le.2 hhq)

/-- The effective domain of `f`: the set where `f < ⊤`. Equivalently the projection of `epi f` on
`E`. -/
def convexDom (f : E → EReal) : Set E := {x | f x < ⊤}

@[simp] theorem mem_convexDom {f : E → EReal} {x : E} : x ∈ convexDom f ↔ f x < ⊤ := Iff.rfl

/-- The effective domain of a concave function: the set where `g > -∞`. It is the projection of
the hypograph, `concaveDom_eq_fst_image_hypo`. -/
def concaveDom (g : E → EReal) : Set E := {x | ⊥ < g x}

@[simp] theorem mem_concaveDom {g : E → EReal} {x : E} : x ∈ concaveDom g ↔ ⊥ < g x := Iff.rfl

/-- `f` is *proper* when it is finite somewhere and never takes the value `⊥`; equivalently, `epi f`
is nonempty and contains no vertical lines. -/
structure ProperConvex (f : E → EReal) : Prop where
  /-- `f` is not identically `⊤`. -/
  convexDom_nonempty : (convexDom f).Nonempty
  /-- `f` never takes the value `⊥`. -/
  ne_bot : ∀ x, f x ≠ ⊥

/-- `g` is a *proper* concave function when it is finite somewhere and never takes the value `⊤`;
equivalently, when `-g` is proper (`properConcave_iff_properConvex_neg`). -/
structure ProperConcave (g : E → EReal) : Prop where
  /-- `g` is not identically `⊥`. -/
  concaveDom_nonempty : (concaveDom g).Nonempty
  /-- `g` never takes the value `⊤`. -/
  ne_top : ∀ x, g x ≠ ⊤

/-- `f` restricted to `s` and extended by `⊤` off `s` — the standing encoding of "a convex function
given on a convex set". The `⨅` formulation avoids a decidability hypothesis;
`convexRestrict_of_mem` and `convexRestrict_of_notMem` are the defining equations. -/
noncomputable def convexRestrict (s : Set E) (f : E → EReal) : E → EReal :=
    fun x => ⨅ _ : x ∈ s, f x

@[simp] theorem convexRestrict_of_mem {s : Set E} {f : E → EReal} {x : E} (hx : x ∈ s) :
    convexRestrict s f x = f x := iInf_pos hx

@[simp] theorem convexRestrict_of_notMem {s : Set E} {f : E → EReal} {x : E} (hx : x ∉ s) :
    convexRestrict s f x = ⊤ := iInf_neg hx

/-- `g` restricted to `s` and extended by `⊥` off `s`: the concave counterpart of `convexRestrict`,
which extends by `⊤`. The `⨆` formulation avoids a decidability hypothesis;
`concaveRestrict_of_mem` and `concaveRestrict_of_notMem` are the defining equations. -/
noncomputable def concaveRestrict (s : Set E) (g : E → EReal) : E → EReal :=
  fun x => ⨆ _ : x ∈ s, g x

@[simp] theorem concaveRestrict_of_mem {s : Set E} {g : E → EReal} {x : E} (hx : x ∈ s) :
    concaveRestrict s g x = g x := iSup_pos hx

@[simp] theorem concaveRestrict_of_notMem {s : Set E} {g : E → EReal} {x : E} (hx : x ∉ s) :
    concaveRestrict s g x = ⊥ := iSup_neg hx

/-! #### The sign dictionary

Every concave notion above is the reflection of its convex twin under `g ↦ -g`. None of these
transfers involves a sum on `EReal`, so none needs a side condition. -/

/-- The hypograph of `g` is the vertical reflection `(x, μ) ↦ (x, -μ)` of the epigraph of `-g`. This
— not a definition — is Rockafellar's "`g` is concave when `-g` is convex", at the level of sets. -/
theorem hypo_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' epi fun x => -(g x) := by
  ext ⟨x, μ⟩
  change (μ : EReal) ≤ g x ↔ -(g x) ≤ ((-μ : ℝ) : EReal)
  rw [EReal.coe_neg, EReal.neg_le_neg_iff]

/-- The epigraph of `-g` is the vertical reflection `(x, μ) ↦ (x, -μ)` of the hypograph of `g`; the
converse direction of `hypo_neg`, the reflection being an involution. -/
theorem epi_neg (g : E → EReal) :
    epi (fun x => -(g x)) = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' hypo g := by
  rw [hypo_neg, ← Set.preimage_comp]
  ext ⟨x, μ⟩
  simp

/-- `hypo_neg` with the reflection applied as an image rather than a preimage. -/
theorem hypo_eq_image_epi_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) '' epi fun x => -(g x) := by
  have hinv : Function.LeftInverse (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ))
      (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ)) := fun p => by simp [Prod.map]
  rw [Set.image_eq_preimage_of_inverse hinv hinv, hypo_neg]

/-- The concave effective domain of `g` is the convex effective domain of `-g`. -/
theorem concaveDom_eq_convexDom_neg (g : E → EReal) : concaveDom g = convexDom fun x => -(g x) := by
  ext x
  change ⊥ < g x ↔ -(g x) < ⊤
  exact (EReal.neg_lt_comm (a := g x) (b := ⊤)).symm

/-- The concave effective domain of `-h` is the convex effective domain of `h`. -/
theorem concaveDom_neg (h : E → EReal) : concaveDom (fun z => -(h z)) = convexDom h := by
  simpa using concaveDom_eq_convexDom_neg fun z => -(h z)

/-- Rockafellar's own definition of properness for a concave function: `g` is proper exactly when
`-g` is. -/
theorem properConcave_iff_properConvex_neg {g : E → EReal} :
    ProperConcave g ↔ ProperConvex fun x => -(g x) := by
  constructor
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [← concaveDom_eq_convexDom_neg]; exact h.concaveDom_nonempty
    · simp [h.ne_top x]
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [concaveDom_eq_convexDom_neg]; exact h.convexDom_nonempty
    · simpa using h.ne_bot x

/-- The forward direction of `properConcave_iff_properConvex_neg`, as dot notation. -/
theorem ProperConcave.properConvex_neg {g : E → EReal} (hg : ProperConcave g) :
    ProperConvex fun x => -(g x) :=
  properConcave_iff_properConvex_neg.1 hg

/-- Extension by `⊥` and extension by `⊤` correspond under negation. -/
theorem neg_concaveRestrict (s : Set E) (g : E → EReal) :
    (fun x => -(concaveRestrict s g x)) = convexRestrict s fun x => -(g x) := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

/-! #### Effective domains as projections -/

/-- `dom f` is the projection of `epi f`, with no hypothesis on `f` and improper functions
included. That is why `convexDom` must not be restricted to functions avoiding `⊥`: the relative
interior `ri (dom f)` carries statements about *improper* `f` too. -/
theorem convexDom_eq_fst_image_epi (f : E → EReal) : convexDom f = Prod.fst '' epi f := by
  ext x
  constructor
  · intro hx
    rcases eq_or_lt_of_le (bot_le : (⊥ : EReal) ≤ f x) with h | h
    · exact ⟨(x, 0), by simp [epi, ← h], rfl⟩
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top h.ne' hx
      exact ⟨(x, r), by simp [epi, hr], rfl⟩
  · rintro ⟨⟨y, μ⟩, hy, rfl⟩
    exact lt_of_le_of_lt hy (EReal.coe_lt_top μ)

/-- The mirror of `convexDom_eq_fst_image_epi`: `concaveDom g` is the projection of `hypo g` on `E`,
with no hypothesis on `g`. -/
theorem concaveDom_eq_fst_image_hypo (g : E → EReal) : concaveDom g = Prod.fst '' hypo g := by
  rw [concaveDom_eq_convexDom_neg, convexDom_eq_fst_image_epi, hypo_eq_image_epi_neg,
      Set.image_image]
  rfl

/-- The epigraph is nonempty exactly when the effective domain is: both say `f ≢ +∞`. -/
theorem epi_nonempty_iff (f : E → EReal) : (epi f).Nonempty ↔ (convexDom f).Nonempty := by
  rw [convexDom_eq_fst_image_epi, Set.image_nonempty]

theorem epi_eq_empty_iff (f : E → EReal) : epi f = ∅ ↔ convexDom f = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, epi_nonempty_iff]

@[simp] theorem epi_top : epi (⊤ : E → EReal) = ∅ := by
  ext p
  simp [epi, Pi.top_apply]

/-! #### Non-negative scalar multiples

`EReal` obeys `0 · ∞ = 0`, so `0 · f` is the constant `0`, which is proper and convex; only the
*effective domain* statement needs `0 < c`, because `dom (0 · f)` is all of `E`. -/

/-- **A positive multiple of `f` has the same effective domain as `f`.** The hypothesis is
`0 < c`, not `0 ≤ c`: at `c = 0` the product is the constant `0` and its domain is everything. -/
theorem convexDom_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) :
    convexDom (fun x => (c : EReal) * f x) = convexDom f := by
  ext x
  rw [mem_convexDom, mem_convexDom]
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne le_top (EReal.coe_mul_ne_top hc h.ne)⟩
  by_contra hcon
  rw [top_le_iff.1 (not_lt.1 hcon), EReal.coe_mul_top_of_pos hc] at h
  exact lt_irrefl _ h

/-- **A non-negative multiple of a proper function is proper.** At `c = 0` the product is the
constant `0`, which is finite everywhere; at `c > 0` the domain is unchanged
(`convexDom_coe_mul`). -/
theorem properConvex_coe_mul {c : ℝ} (hc : 0 ≤ c) {f : E → EReal} (hp : ProperConvex f) :
    ProperConvex (fun x => (c : EReal) * f x) := by
  refine ⟨?_, fun x => EReal.coe_mul_ne_bot hc (hp.ne_bot x)⟩
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  refine ⟨x₀, ?_⟩
  rcases eq_or_lt_of_le hc with h | h
  · rw [mem_convexDom, ← h]; simp
  · exact mem_convexDom.2 (lt_of_le_of_ne le_top (EReal.coe_mul_ne_top h (mem_convexDom.1 hx₀).ne))

end Basic

/-! ### Convex and concave functions -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A function `f : E → EReal` is convex when its epigraph is a convex subset of `E × ℝ`.
See `convexFn_iff_forall_lt` and `convexFn_iff_le` for the analytic forms. -/
structure ConvexFn (f : E → EReal) : Prop where
  /-- The epigraph of a convex function is convex. -/
  convex_epi : Convex ℝ (epi f)

@[simp] theorem convexFn_iff_convex_epi {f : E → EReal} : ConvexFn f ↔ Convex ℝ (epi f) :=
  ⟨fun h => h.convex_epi, fun h => ⟨h⟩⟩

/-- A function `g : E → EReal` is concave when its hypograph is a convex subset of `E × ℝ`. This
mirrors `ConvexFn`, and agrees with the definition by "`-g` is convex" through
`concaveFn_iff_convexFn_neg`. -/
structure ConcaveFn (g : E → EReal) : Prop where
  /-- The hypograph of a concave function is convex. -/
  convex_hypo : Convex ℝ (hypo g)

@[simp] theorem concaveFn_iff_convex_hypo {g : E → EReal} : ConcaveFn g ↔ Convex ℝ (hypo g) :=
  ⟨fun h => h.convex_hypo, fun h => ⟨h⟩⟩

/-- A convex-combination goal reduces to the case of two positive coefficients. -/
theorem combo_of_pos {P : E → Prop} {x y : E} {a b : ℝ} (hx : P x) (hy : P y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (h : 0 < a → 0 < b → P (a • x + b • y)) :
    P (a • x + b • y) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1; simpa using hx
  exact h ha' hb'

/-- The defining property of convexity, in the form in which it is used: a convex combination of
two points of the epigraph lies in the epigraph. -/
theorem ConvexFn.epi_combo {f : E → EReal} (hf : ConvexFn f) {x y : E} {μ ν : ℝ}
    (hx : f x ≤ (μ : EReal)) (hy : f y ≤ (ν : EReal)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal) :=
  hf.convex_epi (show (x, μ) ∈ epi f from hx) (show (y, ν) ∈ epi f from hy) ha hb hab

/-- The defining property of concavity, in the form in which it is used: a convex combination of
two points of the hypograph lies in the hypograph. -/
theorem ConcaveFn.hypo_combo {g : E → EReal} (hg : ConcaveFn g) {x y : E} {μ ν : ℝ}
    (hx : (μ : EReal) ≤ g x) (hy : (ν : EReal) ≤ g y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y) :=
  hg.convex_hypo (show (x, μ) ∈ hypo g from hx) (show (y, ν) ∈ hypo g from hy) ha hb hab

/-- Conversely, the combination property characterises convexity. -/
theorem convexFn_of_epi_combo {f : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), f x ≤ (μ : EReal) → f y ≤ (ν : EReal) →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)) :
    ConvexFn f := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-- Conversely, the combination property characterises concavity. -/
theorem concaveFn_of_hypo_combo {g : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), (μ : EReal) ≤ g x → (ν : EReal) ≤ g y →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y)) :
    ConcaveFn g := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-! #### The sign dictionary for convexity -/

/-- **A function is concave exactly when its negative is convex.** Like `hypo_neg`, this needs no
side condition: the reflection `(x, μ) ↦ (x, -μ)` is linear and carries each graph to the other. -/
theorem concaveFn_iff_convexFn_neg {g : E → EReal} : ConcaveFn g ↔ ConvexFn fun x => -(g x) := by
  rw [concaveFn_iff_convex_hypo, convexFn_iff_convex_epi]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [epi_neg]; exact h.linear_preimage (LinearMap.prodMap LinearMap.id (-LinearMap.id))
  · rw [hypo_neg]; exact h.linear_preimage (LinearMap.prodMap LinearMap.id (-LinearMap.id))

/-- The forward direction of `concaveFn_iff_convexFn_neg`. -/
theorem ConcaveFn.convexFn_neg {g : E → EReal} (hg : ConcaveFn g) : ConvexFn fun x => -(g x) :=
  concaveFn_iff_convexFn_neg.1 hg

/-- The mirror of `ConcaveFn.convexFn_neg`: a convex function has a concave negative. -/
theorem ConvexFn.concaveFn_neg {f : E → EReal} (hf : ConvexFn f) : ConcaveFn fun x => -(f x) :=
  concaveFn_iff_convexFn_neg.2 (by simpa using hf)

/-! #### Affine perturbations -/

/-- **A real-valued affine coordinate added to a convex function keeps it convex.** The hypothesis
is the combination law rather than linearity, so the same lemma serves a coordinate of a pairing, a
projection of a product and an affine function alike. -/
theorem convexFn_add_coe {f : E → EReal} (hf : ConvexFn f) {l : E → ℝ}
    (hl : ∀ (x y : E) (a b : ℝ), a + b = 1 → l (a • x + b • y) = a * l x + b * l y) :
    ConvexFn (fun x => f x + ((l x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  have hcomb := hf.epi_combo (EReal.add_coe_le_coe_iff.1 hx)
    (EReal.add_coe_le_coe_iff.1 hy) ha hb hab
  refine EReal.add_coe_le_coe_iff.2 (hcomb.trans (le_of_eq ?_))
  rw [EReal.coe_eq_coe_iff, hl x y a b hab]
  ring

/-- **Translating the argument preserves convexity.** `x ↦ f (a + x)` is convex whenever `f` is,
for any `a`; the epigraph of the translate is the translate of the epigraph. -/
theorem ConvexFn.comp_add_left {f : E → EReal} (hf : ConvexFn f) (a : E) :
    ConvexFn (fun x => f (a + x)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy s t hs ht hst => ?_
  have hcombo := hf.epi_combo (x := a + x) (y := a + y) hx hy hs ht hst
  have hkey : s • (a + x) + t • (a + y) = a + (s • x + t • y) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul]
  rwa [hkey] at hcombo

/-! ### Non-negative scalar multiples -/

/-- The linear map `(x, μ) ↦ (x, c μ)` of `E × ℝ`. It is the vertical scaling that carries `epi f`
to `epi (cf)`; see `epi_coe_mul`. -/
noncomputable def scaleSnd (c : ℝ) : (E × ℝ) →ₗ[ℝ] (E × ℝ) :=
  LinearMap.prod (LinearMap.fst ℝ E ℝ) (c • LinearMap.snd ℝ E ℝ)

theorem scaleSnd_apply (c : ℝ) (p : E × ℝ) : scaleSnd c p = (p.1, c * p.2) := rfl

/-- **The epigraph of a positive multiple.** `epi (cf)` is `epi f` pulled back along the vertical
scaling `(x, μ) ↦ (x, μ / c)`, which makes convexity and closedness of `cf` preimage arguments. The
identity fails at `c = 0`, where the left side is `E × Ici 0` and the right side is everything. -/
theorem epi_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) :
    epi (fun x => (c : EReal) * f x) = scaleSnd c⁻¹ ⁻¹' epi f := by
  ext p
  rw [Set.mem_preimage, mem_epi, mem_epi, scaleSnd_apply]
  change (c : EReal) * f p.1 ≤ (p.2 : EReal) ↔ f p.1 ≤ ((c⁻¹ * p.2 : ℝ) : EReal)
  rw [show c⁻¹ * p.2 = p.2 / c from (div_eq_inv_mul p.2 c).symm]
  exact EReal.coe_mul_le_coe_iff hc

/-- **A non-negative multiple of a convex function is convex**, the `EReal`-valued form of "`λf` is
convex for `λ ≥ 0`". -/
theorem convexFn_coe_mul {c : ℝ} (hc : 0 ≤ c) {f : E → EReal} (hf : ConvexFn f) :
    ConvexFn (fun x => (c : EReal) * f x) := by
  rcases eq_or_lt_of_le hc with h | h
  · have hz : (fun x => (c : EReal) * f x) = fun _ : E => (0 : EReal) := by
      funext x; rw [← h]; simp
    rw [hz]
    refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
    have hμ : (0 : ℝ) ≤ μ := by exact_mod_cast hx
    have hν : (0 : ℝ) ≤ ν := by exact_mod_cast hy
    exact_mod_cast add_nonneg (mul_nonneg ha hμ) (mul_nonneg hb hν)
  · refine ⟨?_⟩
    rw [epi_coe_mul h f]
    exact hf.convex_epi.linear_preimage _

/-! ### Convexity as a strict inequality on values -/

/-- **Convexity in strict inequalities.** A function `f : E → EReal` is convex if and only if
`f ((1 - λ) x + λ y) < (1 - λ) α + λ β` whenever `f x < α`, `f y < β` and `0 < λ < 1`. The strict
inequalities keep `α` and `β` real, so the forbidden `∞ - ∞` never arises. -/
theorem convexFn_iff_forall_lt (f : E → EReal) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) := by
  constructor
  · intro hf x y a b ha hb hab α β hx hy
    obtain ⟨α', hxα', hα'⟩ := EReal.exists_between_coe_real hx
    obtain ⟨β', hyβ', hβ'⟩ := EReal.exists_between_coe_real hy
    rw [EReal.coe_lt_coe_iff] at hα' hβ'
    refine lt_of_le_of_lt (hf.epi_combo hxα'.le hyβ'.le ha.le hb.le hab) ?_
    exact_mod_cast add_lt_add (by nlinarith) (by nlinarith)
  · intro h
    refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      subst ha1; simpa using hx
    · refine EReal.le_of_forall_lt_iff_le.1 (fun q hq => le_of_lt ?_)
      replace hq := EReal.coe_lt_coe_iff.1 hq
      have hx' : f x < ((μ + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hx (by exact_mod_cast (by linarith : μ < μ + (q - (a * μ + b * ν))))
      have hy' : f y < ((ν + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hy (by exact_mod_cast (by linarith : ν < ν + (q - (a * μ + b * ν))))
      have key := h x y a b ha' hb' hab _ _ hx' hy'
      have harith : a * (μ + (q - (a * μ + b * ν))) + b * (ν + (q - (a * μ + b * ν))) = q := by
        linear_combination (q - (a * μ + b * ν)) * hab
      rwa [harith] at key

/-- **Concavity in strict inequalities.** A function `g : E → EReal` is concave if and only if
`g ((1 - λ) x + λ y) > (1 - λ) α + λ β` whenever `g x > α`, `g y > β` and `0 < λ < 1`. The strict
inequalities keep `α` and `β` real, so no `∞ - ∞` arises and no hypothesis on `g` is needed. -/
theorem concaveFn_iff_forall_gt (g : E → EReal) :
    ConcaveFn g ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, (α : EReal) < g x → (β : EReal) < g y →
        ((a * α + b * β : ℝ) : EReal) < g (a • x + b • y) := by
  rw [concaveFn_iff_convexFn_neg, convexFn_iff_forall_lt]
  constructor
  · intro h x y a b ha hb hab α β hx hy
    have hx' : -(g x) < ((-α : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.2 hx
    have hy' : -(g y) < ((-β : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_neg_iff.2 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, EReal.coe_neg] at key
    exact EReal.neg_lt_neg_iff.1 key
  · intro h x y a b ha hb hab α β hx hy
    have hx' : ((-α : ℝ) : EReal) < g x := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hx
    have hy' : ((-β : ℝ) : EReal) < g y := by
      rw [EReal.coe_neg]; exact EReal.neg_lt_comm.1 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, EReal.coe_neg] at key
    exact EReal.neg_lt_comm.1 key

/-! ### Convexity as an inequality on values -/

/-- For a function `f` that never takes the value `⊥` — equivalently, a function into `(-∞, +∞]` —
**convexity is the familiar inequality**. -/
theorem convexFn_iff_le {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  rw [convexFn_iff_forall_lt]
  have hacoe : ∀ {c : ℝ}, 0 < c → (0 : EReal) < (c : EReal) := fun hc => by exact_mod_cast hc
  constructor
  · intro h x y a b ha hb hab
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx, EReal.mul_top_of_pos (hacoe ha)]
      rcases eq_top_or_lt_top (f y) with hy | hy
      · rw [hy, EReal.mul_top_of_pos (hacoe hb), EReal.top_add_top]; exact le_top
      · obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf y) hy
        rw [hq, ← EReal.coe_mul, EReal.top_add_coe]; exact le_top
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf x) hx
    rcases eq_top_or_lt_top (f y) with hy | hy
    · rw [hy, EReal.mul_top_of_pos (hacoe hb), hp, ← EReal.coe_mul, EReal.coe_add_top]
      exact le_top
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf y) hy
    rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    refine EReal.le_of_forall_lt_iff_le.1 (fun r hr => le_of_lt ?_)
    replace hr := EReal.coe_lt_coe_iff.1 hr
    have hx' : f x < ((p + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hp]; exact_mod_cast (by linarith : p < p + (r - (a * p + b * q)))
    have hy' : f y < ((q + (r - (a * p + b * q)) : ℝ) : EReal) := by
      rw [hq]; exact_mod_cast (by linarith : q < q + (r - (a * p + b * q)))
    have key := h x y a b ha hb hab _ _ hx' hy'
    have harith : a * (p + (r - (a * p + b * q))) + b * (q + (r - (a * p + b * q))) = r := by
      linear_combination (r - (a * p + b * q)) * hab
    rwa [harith] at key
  · intro h x y a b ha hb hab α β hx hy
    obtain ⟨p, hp⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hf x) (hx.trans (EReal.coe_lt_top α))
    obtain ⟨q, hq⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hf y) (hy.trans (EReal.coe_lt_top β))
    refine lt_of_le_of_lt (h x y a b ha hb hab) ?_
    rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    rw [hp] at hx; rw [hq] at hy
    have hpα : p < α := by exact_mod_cast hx
    have hqβ : q < β := by exact_mod_cast hy
    exact_mod_cast (by nlinarith : a * p + b * q < a * α + b * β)

/-- For a function `g` that never takes the value `⊤` — equivalently, a function into
`[-∞, +∞)` — **concavity is the familiar reversed inequality**. The
hypothesis is what makes the right-hand side of the convex form negate to the left-hand side here:
on `EReal`, `-(u + v) = -u + -v` fails when one summand is `⊤` and the other `⊥`. -/
theorem concaveFn_iff_le {g : E → EReal} (hg : ∀ x, g x ≠ ⊤) :
    ConcaveFn g ↔ ∀ (x y : E) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      (a : EReal) * g x + (b : EReal) * g y ≤ g (a • x + b • y) := by
  have hneg : ∀ x, -(g x) ≠ ⊥ := fun x => by simp [hg x]
  rw [concaveFn_iff_convexFn_neg, convexFn_iff_le hneg]
  refine forall₂_congr fun x y => forall₂_congr fun a b => ?_
  refine forall₃_congr fun ha hb _ => ?_
  rw [EReal.neg_combo ha hb (hg x) (hg y), EReal.neg_le_neg_iff]

/-! ### Level sets and the effective domain -/

/-- **Strict sublevel sets of a convex function are convex.** -/
theorem ConvexFn.convex_lt {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x < α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x < α := hx
  have hy' : f y < α := hy
  change f (a • x + b • y) < α
  obtain ⟨p, hxp, hpα⟩ := EReal.lt_iff_exists_real_btwn.1 hx'
  obtain ⟨q, hyq, hqα⟩ := EReal.lt_iff_exists_real_btwn.1 hy'
  refine lt_of_le_of_lt (hf.epi_combo hxp.le hyq.le ha'.le hb'.le hab) ?_
  induction α with
  | bot => exact absurd hpα (by simp)
  | top => exact EReal.coe_lt_top _
  | coe r =>
    have hp : p < r := by exact_mod_cast hpα
    have hq : q < r := by exact_mod_cast hqα
    have h1 : a * p < a * r := mul_lt_mul_of_pos_left hp ha'
    have h2 : b * q < b * r := mul_lt_mul_of_pos_left hq hb'
    have h3 : a * r + b * r = r := by linear_combination r * hab
    exact_mod_cast (by linarith : a * p + b * q < r)

/-- **Strict superlevel sets of a concave function are convex.** -/
theorem ConcaveFn.convex_gt {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α < g x} := by
  have hset : {x | α < g x} = {x | -(g x) < -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_lt (-α)

/-- **Sublevel sets of a convex function are convex.** -/
theorem ConvexFn.convex_le {f : E → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x ≤ α} := by
  intro x hx y hy a b ha hb hab
  refine combo_of_pos (P := fun z => z ∈ {x | f x ≤ α}) hx hy ha hb hab (fun ha' hb' => ?_)
  have hx' : f x ≤ α := hx
  have hy' : f y ≤ α := hy
  change f (a • x + b • y) ≤ α
  induction α with
  | bot =>
    refine le_of_eq (le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ?_))
    have := hf.epi_combo (μ := r) (ν := r) (hx'.trans bot_le) (hy'.trans bot_le) ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)
  | top => exact le_top
  | coe r =>
    have := hf.epi_combo hx' hy' ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)

/-- **Superlevel sets of a concave function are convex.** These are the sets whose closedness
characterises upper semicontinuity. -/
theorem ConcaveFn.convex_ge {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α ≤ g x} := by
  have hset : {x | α ≤ g x} = {x | -(g x) ≤ -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_le (-α)

/-- The effective domain of a convex function is convex. -/
theorem ConvexFn.convex_convexDom {f : E → EReal} (hf : ConvexFn f) : Convex ℝ (convexDom f) :=
  hf.convex_lt ⊤

/-- The effective domain of a concave function is convex. -/
theorem ConcaveFn.convex_concaveDom {g : E → EReal} (hg : ConcaveFn g) : Convex ℝ (concaveDom g) :=
  hg.convex_gt ⊥

/-! ### The bridges to Mathlib's `ConvexOn` and `ConcaveOn` -/

omit [AddCommGroup E] [Module ℝ E] in
theorem epi_convexRestrict_coe (s : Set E) (g : E → ℝ) :
    epi (convexRestrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

omit [AddCommGroup E] [Module ℝ E] in
/-- The hypograph of a real-valued function extended by `⊥`, in the shape Mathlib's
`concaveOn_iff_convex_hypograph` expects. -/
theorem hypo_concaveRestrict_coe (s : Set E) (g : E → ℝ) :
    hypo (concaveRestrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [hypo, hp]

/-- Mathlib's `ConvexOn` for a real-valued function on a set agrees with `ConvexFn` for its
extension by `⊤`. This is the interface through which the surface layer reuses Mathlib. -/
theorem convexOn_iff_convexFn (s : Set E) (g : E → ℝ) :
    ConvexOn ℝ s g ↔ ConvexFn (convexRestrict s fun x => (g x : EReal)) := by
  rw [convexFn_iff_convex_epi, epi_convexRestrict_coe]
  exact ⟨fun h => h.convex_epigraph, fun h => convexOn_of_convex_epigraph h⟩

/-- Mathlib's `ConcaveOn` for a real-valued function on a set agrees with `ConcaveFn` for its
extension by `⊥`; compare `convexOn_iff_convexFn`. -/
theorem concaveOn_iff_concaveFn (s : Set E) (g : E → ℝ) :
    ConcaveOn ℝ s g ↔ ConcaveFn (concaveRestrict s fun x => (g x : EReal)) := by
  rw [concaveFn_iff_convex_hypo, hypo_concaveRestrict_coe]
  exact ⟨fun h => h.convex_hypograph, fun h => concaveOn_of_convex_hypograph h⟩

end Module

/-! ### Real-valued functions as `EReal`-valued ones

A book's convex function is real-valued on a convex set `s`, or on the whole space; the backbone's
is `EReal`-valued. The dictionary: a real-valued `g` on `s` is
`convexRestrict s fun x => (g x : EReal)`, which is proper with effective domain `s` as soon as `s`
is nonempty, and convex exactly when `g` is `ConvexOn ℝ s`; on the whole space the restriction
disappears. A concave `g` on `s` is `concaveRestrict s fun x => (g x : EReal)`, with the same
dictionary. -/

section RealValued

variable {E : Type*}

@[simp] theorem convexRestrict_univ (f : E → EReal) : convexRestrict univ f = f :=
  funext fun x => convexRestrict_of_mem (mem_univ x)

@[simp] theorem concaveRestrict_univ (g : E → EReal) : concaveRestrict univ g = g :=
  funext fun x => concaveRestrict_of_mem (mem_univ x)

/-- A real-valued function, read as `EReal`-valued, has effective domain everything. -/
@[simp] theorem convexDom_coe (g : E → ℝ) : convexDom (fun x => ((g x : ℝ) : EReal)) = univ :=
  eq_univ_of_forall fun _ => mem_convexDom.2 (EReal.coe_lt_top _)

/-- A real-valued function, read as `EReal`-valued, has concave effective domain everything. -/
@[simp] theorem concaveDom_coe (g : E → ℝ) : concaveDom (fun x => ((g x : ℝ) : EReal)) = univ :=
  eq_univ_of_forall fun _ => mem_concaveDom.2 (EReal.bot_lt_coe _)

/-- A real-valued function on a nonempty space is proper as an `EReal`-valued one. -/
theorem properConvex_coe [Nonempty E] (g : E → ℝ) : ProperConvex (fun x => ((g x : ℝ) : EReal)) :=
  ⟨by simp, fun _ => EReal.coe_ne_bot _⟩

/-- A real-valued function on a nonempty space is proper as an `EReal`-valued concave one. -/
theorem properConcave_coe [Nonempty E] (g : E → ℝ) :
    ProperConcave (fun x => ((g x : ℝ) : EReal)) :=
  ⟨by simp, fun _ => EReal.coe_ne_top _⟩

/-- The effective domain of a real-valued function extended by `⊤` is the set it was given on. -/
theorem convexDom_convexRestrict_coe (s : Set E) (g : E → ℝ) :
    convexDom (convexRestrict s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The concave effective domain of a finite function extended by `⊥` is the set it was given
on. -/
theorem concaveDom_concaveRestrict_coe (s : Set E) (g : E → ℝ) :
    concaveDom (concaveRestrict s fun x => (g x : EReal)) = s := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The restriction of a real-valued function to a nonempty set is a proper `EReal`-valued
function: its effective domain is that set, and it never takes the value `⊥`. -/
theorem properConvex_convexRestrict_coe {s : Set E} (hs : s.Nonempty) (g : E → ℝ) :
    ProperConvex (convexRestrict s fun x => (g x : EReal)) := by
  refine ⟨by rwa [convexDom_convexRestrict_coe], fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [convexRestrict_of_mem hx]; exact EReal.coe_ne_bot _
  · rw [convexRestrict_of_notMem hx]; exact top_ne_bot

/-- The restriction of a real-valued function to a nonempty set, extended by `⊥`, is a proper
concave `EReal`-valued function. -/
theorem properConcave_concaveRestrict_coe {s : Set E} (hs : s.Nonempty) (g : E → ℝ) :
    ProperConcave (concaveRestrict s fun x => (g x : EReal)) := by
  refine ⟨by rwa [concaveDom_concaveRestrict_coe], fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [concaveRestrict_of_mem hx]; exact EReal.coe_ne_top _
  · rw [concaveRestrict_of_notMem hx]; exact bot_ne_top

variable [AddCommGroup E] [Module ℝ E]

/-- `convexOn_iff_convexFn`, forwards, as dot notation on a `ConvexOn` hypothesis. -/
theorem _root_.ConvexOn.convexFn_convexRestrict_coe {s : Set E} {g : E → ℝ} (h : ConvexOn ℝ s g) :
    ConvexFn (convexRestrict s fun x => (g x : EReal)) :=
  (convexOn_iff_convexFn s g).1 h

/-- `concaveOn_iff_concaveFn`, forwards, as dot notation on a `ConcaveOn` hypothesis. -/
theorem _root_.ConcaveOn.concaveFn_concaveRestrict_coe {s : Set E} {g : E → ℝ}
    (h : ConcaveOn ℝ s g) : ConcaveFn (concaveRestrict s fun x => (g x : EReal)) :=
  (concaveOn_iff_concaveFn s g).1 h

/-- A real-valued function convex on the whole space is convex as an `EReal`-valued one. -/
theorem _root_.ConvexOn.convexFn_coe {g : E → ℝ} (h : ConvexOn ℝ univ g) :
    ConvexFn fun x => (g x : EReal) := by
  simpa using h.convexFn_convexRestrict_coe

/-- A real-valued function concave on the whole space is concave as an `EReal`-valued one. -/
theorem _root_.ConcaveOn.concaveFn_coe {g : E → ℝ} (h : ConcaveOn ℝ univ g) :
    ConcaveFn fun x => (g x : EReal) := by
  simpa using h.concaveFn_concaveRestrict_coe

end RealValued

/-! ### Jensen's inequality for finite convex combinations -/

section Jensen

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}

/-- **Jensen's inequality** for a convex `EReal`-valued function, in the form the epigraph supplies
it: a convex combination of points at which `f` is bounded above by reals `m j` is bounded above by
the same combination of the `m j`. The bound is by *reals*, not by `f (u j)` directly; the
`EReal`-valued form `f (∑ wt j • u j) ≤ ∑ wt j • f (u j)` needs the `0 · ∞ = 0` convention at
indices where `wt j = 0` and `f (u j) = ⊤`. Aliased as `jensen`. -/
theorem ConvexFn.sum_le {ι : Type*} (hf : ConvexFn f) (t : Finset ι) (u : ι → E) (m wt : ι → ℝ)
    (hm : ∀ j ∈ t, f (u j) ≤ ((m j : ℝ) : EReal)) (hw : ∀ j ∈ t, 0 ≤ wt j)
    (hw1 : ∑ j ∈ t, wt j = 1) :
    f (∑ j ∈ t, wt j • u j) ≤ ((∑ j ∈ t, wt j * m j : ℝ) : EReal) := by
  have hmem := hf.convex_epi.sum_mem hw hw1 (fun j hj => mk_mem_epi.2 (hm j hj))
  have hsum : (∑ j ∈ t, wt j • ((u j, m j) : E × ℝ))
      = ((∑ j ∈ t, wt j • u j, ∑ j ∈ t, wt j * m j) : E × ℝ) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, smul_eq_mul]
  rw [hsum] at hmem
  exact mk_mem_epi.1 hmem

end Jensen

end ConvexAnalysis
