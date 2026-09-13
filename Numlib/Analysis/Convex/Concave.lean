import Numlib.Analysis.Convex.Epigraph

/-!
# Extended-real-valued concave functions

The concave counterpart of `Numlib/Analysis/Convex/Epigraph.lean`, for `g : E → EReal`. Concavity is
*defined* geometrically, as convexity of the hypograph, exactly as convexity is defined by convexity
of the epigraph; `-g` appears only in the transfer lemmas. Rockafellar mixes the two theories
constantly from Part VI on, so the concave notions need first-class names rather than being spelled
`ConvexFn (-g)` at every use.

Sign transfer is not free on `EReal`, because negation does not distribute over addition:
`-(⊥ + ⊤) = ⊤` while `(-⊥) + (-⊤) = ⊥`. This is why `concaveFn_iff_le` needs `∀ x, g x ≠ ⊤`,
mirroring the `∀ x, f x ≠ ⊥` of `convexFn_iff_le`, while `concaveFn_iff_forall_gt`, which never
forms a sum of infinities, needs no hypothesis at all.

## Main definitions

* `hypo g` — the hypograph of `g`, a subset of `E × ℝ`. Rockafellar writes `epi g` for it,
  overloading the notation; we do not.
* `domConcave g` — the effective domain, the set where `g > -∞`. This is *not* `dom`.
* `ProperConcave g` — `g` is finite somewhere and never `⊤`.
* `restrictConcave s g` — `g` restricted to `s`, extended by `⊥`.
* `ConcaveFn g` — `g` is concave, meaning that `hypo g` is convex.

## Main results

* `hypo_neg`, `epi_neg` — hypograph and epigraph are exchanged by the reflection `(x, μ) ↦ (x, -μ)`.
* `concaveFn_iff_convexFn_neg` — "`g` is concave when `-g` is convex", recovered as a theorem. With
  `domConcave_eq_dom_neg` and `properConcave_iff_proper_neg` this is the sign dictionary through
  which the concave theory is derived from the convex one.
* `concaveFn_iff_forall_gt`, `concaveFn_iff_le` — concavity as an inequality on values, strict
  and non-strict.
* `ConcaveFn.convex_gt`, `ConcaveFn.convex_ge` — superlevel sets of a concave function are
  convex.
* `concaveOn_iff_concaveFn` — the bridge to Mathlib's `ConcaveOn`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §30 for the concave
  conventions, §4 for the convex statements being mirrored.
-/

open Set

namespace ConvexAnalysis

/-! ### Hypographs, domains, properness -/

section Basic

variable {E : Type*}

/-- The hypograph of `g : E → EReal`, `{(x, μ) | μ ∈ ℝ, μ ≤ g x} ⊆ E × ℝ`. Rockafellar writes this
`epi g`, reusing the epigraph notation; we keep the two names apart. As with `epi`, the second
coordinate ranges over the *reals*. -/
def hypo (g : E → EReal) : Set (E × ℝ) := {p | (p.2 : EReal) ≤ g p.1}

@[simp]
theorem mem_hypo {g : E → EReal} {p : E × ℝ} : p ∈ hypo g ↔ (p.2 : EReal) ≤ g p.1 := Iff.rfl

theorem mk_mem_hypo {g : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ hypo g ↔ (μ : EReal) ≤ g x := Iff.rfl

/-- The hypograph is monotone in the function, where the epigraph is antitone. -/
theorem hypo_mono {g h : E → EReal} (hgh : g ≤ h) : hypo g ⊆ hypo h := fun _ hp => hp.trans (hgh _)

/-- The hypograph determines the function: `g ≤ h` exactly when `hypo g ⊆ hypo h`. -/
theorem le_iff_hypo_subset {g h : E → EReal} : g ≤ h ↔ hypo g ⊆ hypo h := by
  refine ⟨hypo_mono, fun hs x => ?_⟩
  by_contra hx
  obtain ⟨q, hhq, hqg⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (hs (show (x, q) ∈ hypo g from hqg.le)) (not_le.2 hhq)

/-- The hypograph of `g` is the vertical reflection `(x, μ) ↦ (x, -μ)` of the epigraph of `-g`. This
— not a definition — is Rockafellar's "`g` is concave when `-g` is convex", at the level of sets. It
holds for every `g`, with no side condition, because it involves no addition on `EReal`. -/
theorem hypo_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' epi fun x => -(g x) := by
  ext ⟨x, μ⟩
  change (μ : EReal) ≤ g x ↔ -(g x) ≤ ((-μ : ℝ) : EReal)
  rw [_root_.EReal.coe_neg, _root_.EReal.neg_le_neg_iff]

/-- The epigraph of `-g` is the vertical reflection `(x, μ) ↦ (x, -μ)` of the hypograph of `g`; the
converse direction of `hypo_neg`, the reflection being an involution. -/
theorem epi_neg (g : E → EReal) :
    epi (fun x => -(g x)) = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) ⁻¹' hypo g := by
  ext ⟨x, μ⟩
  change -(g x) ≤ (μ : EReal) ↔ ((-μ : ℝ) : EReal) ≤ g x
  rw [_root_.EReal.coe_neg]
  exact _root_.EReal.neg_le

/-- `hypo_neg` with the reflection applied as an image rather than a preimage. -/
theorem hypo_eq_image_epi_neg (g : E → EReal) :
    hypo g = Prod.map (id : E → E) (Neg.neg : ℝ → ℝ) '' epi fun x => -(g x) := by
  have hinv : Function.LeftInverse (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ))
      (Prod.map (id : E → E) (Neg.neg : ℝ → ℝ)) := fun p => by simp [Prod.map]
  rw [Set.image_eq_preimage_of_inverse hinv hinv, hypo_neg]

/-- The effective domain of a concave function: the set where `g > -∞`. It is the projection of
the hypograph, `domConcave_eq_fst_image_hypo`. -/
def domConcave (g : E → EReal) : Set E := {x | ⊥ < g x}

@[simp] theorem mem_domConcave {g : E → EReal} {x : E} : x ∈ domConcave g ↔ ⊥ < g x := Iff.rfl

/-- The concave effective domain of `g` is the convex effective domain of `-g`. -/
theorem domConcave_eq_dom_neg (g : E → EReal) : domConcave g = dom fun x => -(g x) := by
  ext x
  change ⊥ < g x ↔ -(g x) < ⊤
  exact (_root_.EReal.neg_lt_comm (a := g x) (b := ⊤)).symm

/-- The mirror of `dom_eq_fst_image_epi`: `domConcave g` is the projection of `hypo g` on `E`,
with no hypothesis on `g`. -/
theorem domConcave_eq_fst_image_hypo (g : E → EReal) : domConcave g = Prod.fst '' hypo g := by
  rw [domConcave_eq_dom_neg, dom_eq_fst_image_epi, hypo_eq_image_epi_neg, Set.image_image]
  rfl

/-- `g` is a *proper* concave function when it is finite somewhere and never takes the value `⊤`;
equivalently, when `-g` is proper (`properConcave_iff_proper_neg`). -/
structure ProperConcave (g : E → EReal) : Prop where
  /-- `g` is not identically `⊥`. -/
  domConcave_nonempty : (domConcave g).Nonempty
  /-- `g` never takes the value `⊤`. -/
  ne_top : ∀ x, g x ≠ ⊤

/-- Rockafellar's own definition of properness for a concave function: `g` is proper exactly when
`-g` is. -/
theorem properConcave_iff_proper_neg {g : E → EReal} :
    ProperConcave g ↔ Proper fun x => -(g x) := by
  constructor
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [← domConcave_eq_dom_neg]; exact h.domConcave_nonempty
    · simp [h.ne_top x]
  · refine fun h => ⟨?_, fun x => ?_⟩
    · rw [domConcave_eq_dom_neg]; exact h.dom_nonempty
    · simpa using h.ne_bot x

/-- `g` restricted to `s` and extended by `⊥` off `s`: the concave counterpart of `restrict`, which
extends by `⊤`. The `⨆` formulation avoids a decidability hypothesis; `restrictConcave_of_mem` and
`restrictConcave_of_notMem` are the defining equations. -/
noncomputable def restrictConcave (s : Set E) (g : E → EReal) : E → EReal :=
  fun x => ⨆ _ : x ∈ s, g x

@[simp] theorem restrictConcave_of_mem {s : Set E} {g : E → EReal} {x : E} (hx : x ∈ s) :
    restrictConcave s g x = g x := iSup_pos hx

@[simp] theorem restrictConcave_of_notMem {s : Set E} {g : E → EReal} {x : E} (hx : x ∉ s) :
    restrictConcave s g x = ⊥ := iSup_neg hx

/-- Extension by `⊥` and extension by `⊤` correspond under negation. -/
theorem neg_restrictConcave (s : Set E) (g : E → EReal) :
    (fun x => -(restrictConcave s g x)) = restrict s fun x => -(g x) := by
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

end Basic

/-! ### Concave functions -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A function `g : E → EReal` is concave when its hypograph is a convex subset of `E × ℝ`. This
mirrors `ConvexFn`, and agrees with the definition by "`-g` is convex" through
`concaveFn_iff_convexFn_neg`. -/
structure ConcaveFn (g : E → EReal) : Prop where
  /-- The hypograph of a concave function is convex. -/
  convex_hypo : Convex ℝ (hypo g)

@[simp] theorem concaveFn_iff_convex_hypo {g : E → EReal} : ConcaveFn g ↔ Convex ℝ (hypo g) :=
  ⟨fun h => h.convex_hypo, fun h => ⟨h⟩⟩

/-- The defining property of concavity, in the form in which it is used: a convex combination of
two points of the hypograph lies in the hypograph. -/
theorem ConcaveFn.hypo_combo {g : E → EReal} (hg : ConcaveFn g) {x y : E} {μ ν : ℝ}
    (hx : (μ : EReal) ≤ g x) (hy : (ν : EReal) ≤ g y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y) :=
  hg.convex_hypo (show (x, μ) ∈ hypo g from hx) (show (y, ν) ∈ hypo g from hy) ha hb hab

/-- Conversely, the combination property characterises concavity. -/
theorem concaveFn_of_hypo_combo {g : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), (μ : EReal) ≤ g x → (ν : EReal) ≤ g y →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → ((a * μ + b * ν : ℝ) : EReal) ≤ g (a • x + b • y)) :
    ConcaveFn g := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

/-- **A function is concave exactly when its negative is convex.** Like
`hypo_neg`, this needs no side condition: negation reverses only the *order* here, never a sum. -/
theorem concaveFn_iff_convexFn_neg {g : E → EReal} : ConcaveFn g ↔ ConvexFn fun x => -(g x) := by
  constructor
  · intro hg
    refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
    have hx' : ((-μ : ℝ) : EReal) ≤ g x := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_le.1 hx
    have hy' : ((-ν : ℝ) : EReal) ≤ g y := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_le.1 hy
    have key := hg.hypo_combo hx' hy' ha hb hab
    rw [show (a * -μ + b * -ν : ℝ) = -(a * μ + b * ν) by ring, _root_.EReal.coe_neg] at key
    exact _root_.EReal.neg_le_of_neg_le key
  · intro hg
    refine concaveFn_of_hypo_combo fun x y μ ν hx hy a b ha hb hab => ?_
    have hx' : -(g x) ≤ ((-μ : ℝ) : EReal) := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_le_neg_iff.2 hx
    have hy' : -(g y) ≤ ((-ν : ℝ) : EReal) := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_le_neg_iff.2 hy
    have key := hg.epi_combo hx' hy' ha hb hab
    rw [show (a * -μ + b * -ν : ℝ) = -(a * μ + b * ν) by ring, _root_.EReal.coe_neg] at key
    exact _root_.EReal.neg_le_neg_iff.1 key

/-- The forward direction of `concaveFn_iff_convexFn_neg`. -/
theorem ConcaveFn.convexFn_neg {g : E → EReal} (hg : ConcaveFn g) : ConvexFn fun x => -(g x) :=
  concaveFn_iff_convexFn_neg.1 hg

/-- The mirror of `ConcaveFn.convexFn_neg`: a convex function has a concave negative. -/
theorem ConvexFn.concaveFn_neg {f : E → EReal} (hf : ConvexFn f) : ConcaveFn fun x => -(f x) :=
  concaveFn_iff_convexFn_neg.2 (by simpa using hf)

/-! ### Concavity as a strict inequality on values -/

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
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_lt_neg_iff.2 hx
    have hy' : -(g y) < ((-β : ℝ) : EReal) := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_lt_neg_iff.2 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, _root_.EReal.coe_neg] at key
    exact _root_.EReal.neg_lt_neg_iff.1 key
  · intro h x y a b ha hb hab α β hx hy
    have hx' : ((-α : ℝ) : EReal) < g x := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_lt_comm.1 hx
    have hy' : ((-β : ℝ) : EReal) < g y := by
      rw [_root_.EReal.coe_neg]; exact _root_.EReal.neg_lt_comm.1 hy
    have key := h x y a b ha hb hab _ _ hx' hy'
    rw [show (a * -α + b * -β : ℝ) = -(a * α + b * β) by ring, _root_.EReal.coe_neg] at key
    exact _root_.EReal.neg_lt_comm.1 key

/-! ### Concavity as an inequality on values -/

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
  rw [EReal.neg_combo ha hb (hg x) (hg y), _root_.EReal.neg_le_neg_iff]

/-! ### Level sets and the effective domain -/

/-- **Strict superlevel sets of a concave function are convex.** -/
theorem ConcaveFn.convex_gt {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α < g x} := by
  have hset : {x | α < g x} = {x | -(g x) < -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_lt (-α)

/-- **Superlevel sets of a concave function are convex.** These are the sets whose closedness
characterises upper semicontinuity. -/
theorem ConcaveFn.convex_ge {g : E → EReal} (hg : ConcaveFn g) (α : EReal) :
    Convex ℝ {x | α ≤ g x} := by
  have hset : {x | α ≤ g x} = {x | -(g x) ≤ -α} := by ext x; simp
  rw [hset]
  exact hg.convexFn_neg.convex_le (-α)

/-- The effective domain of a concave function is convex. -/
theorem ConcaveFn.convex_domConcave {g : E → EReal} (hg : ConcaveFn g) : Convex ℝ (domConcave g) :=
  hg.convex_gt ⊥

/-! ### The bridge to Mathlib's `ConcaveOn` -/

omit [AddCommGroup E] [Module ℝ E] in
/-- The hypograph of a real-valued function extended by `⊥`, in the shape Mathlib's
`concaveOn_iff_convex_hypograph` expects. -/
theorem hypo_restrictConcave_coe (s : Set E) (g : E → ℝ) :
    hypo (restrictConcave s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [hypo, hp]

/-- Mathlib's `ConcaveOn` for a real-valued function on a set agrees with `ConcaveFn` for its
extension by `⊥`; compare `convexOn_iff_convexFn`. -/
theorem concaveOn_iff_concaveFn (s : Set E) (g : E → ℝ) :
    ConcaveOn ℝ s g ↔ ConcaveFn (restrictConcave s fun x => (g x : EReal)) := by
  rw [concaveFn_iff_convex_hypo, hypo_restrictConcave_coe]
  exact ⟨fun h => h.convex_hypograph, fun h => concaveOn_of_convex_hypograph h⟩

end Module

end ConvexAnalysis
