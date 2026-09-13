import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Numlib.Order.EReal

/-!
# Extended-real-valued convex functions

The basic theory of convex functions `f : E → EReal` on a real vector space. Convexity is *defined*
geometrically, as convexity of the epigraph, rather than by the
inequality `f (a • x + b • y) ≤ a * f x + b * f y`: the right-hand side can be the undefined
`∞ - ∞` when `f` takes both infinite values, and improper functions are admitted throughout. The
epigraph lives in `E × ℝ`, not `E × EReal` — the second coordinate ranges over the *reals*, unlike
Mathlib's `ConvexOn.convex_epigraph`, which uses the codomain of the function.

## Main definitions

* `epi f` — the epigraph of `f`, a subset of `E × ℝ`.
* `dom f` — the effective domain of `f`, where `f < ⊤`.
* `Proper f` — `f` is finite somewhere and never `⊥`.
* `restrict s f` — `f` restricted to `s`, extended by `⊤`.
* `ConvexFn f` — `f` is convex, meaning that `epi f` is a convex set.
* `scaleSnd c` — the vertical scaling `(x, μ) ↦ (x, c μ)` of `E × ℝ`, which is how a scalar
  multiple of `f` acts on epigraphs.

## Main results

* `convexFn_iff_forall_lt` — convexity by strict inequalities: the form that avoids `∞ - ∞`
  entirely.
* `convexFn_iff_le` — the familiar inequality, valid when `f` never takes `⊥`.
* `convexFn_add_coe`, `ConvexFn.comp_add_left` — adding a real-valued affine coordinate, and
  translating the argument, preserve convexity.
* `ConvexFn.convex_lt`, `ConvexFn.convex_le`, `ConvexFn.convex_dom` — sublevel sets and the
  effective domain of a convex function are convex.
* `convexFn_coe_mul`, `dom_coe_mul`, `proper_coe_mul` — a non-negative multiple `cf`.
* `convexOn_iff_convexFn` — the bridge to Mathlib's `ConvexOn`.
* `ConvexFn.sum_le` — Jensen's inequality for a finite convex combination.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §4.
-/

open Set

namespace ConvexAnalysis

/-! ### Epigraphs, domains, properness -/

section Basic

variable {E : Type*}

/-- The epigraph of `f : E → EReal`, `{(x, μ) | μ ∈ ℝ, f x ≤ μ} ⊆ E × ℝ`. The second coordinate
ranges over the *reals*, not over `EReal`. -/
def epi (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

@[simp]
theorem mem_epi {f : E → EReal} {p : E × ℝ} : p ∈ epi f ↔ f p.1 ≤ (p.2 : EReal) := Iff.rfl

theorem mk_mem_epi {f : E → EReal} {x : E} {μ : ℝ} : (x, μ) ∈ epi f ↔ f x ≤ (μ : EReal) := Iff.rfl

/-- `epi` is **antitone**: a larger function has a smaller epigraph. -/
theorem epi_anti {f g : E → EReal} (h : f ≤ g) : epi g ⊆ epi f := fun _ hp => (h _).trans hp

/-- The epigraph determines the function: `f ≤ g` exactly when `epi g ⊆ epi f`. -/
theorem le_iff_epi_subset {f g : E → EReal} : f ≤ g ↔ epi g ⊆ epi f := by
  refine ⟨epi_anti, fun h x => ?_⟩
  by_contra hx
  obtain ⟨q, hgq, hqf⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  exact absurd (h (show (x, q) ∈ epi g from hgq.le)) (not_le.2 hqf)

/-- The effective domain of `f`: the set where `f < ⊤`. Equivalently the projection of `epi f` on
`E`. -/
def dom (f : E → EReal) : Set E := {x | f x < ⊤}

@[simp] theorem mem_dom {f : E → EReal} {x : E} : x ∈ dom f ↔ f x < ⊤ := Iff.rfl

/-- `dom f` is the projection of `epi f`, with no hypothesis on `f` and improper functions
included. That is why `dom` must not be restricted to functions avoiding `⊥`: the relative interior
`ri (dom f)` carries statements about *improper* `f` too. -/
theorem dom_eq_fst_image_epi (f : E → EReal) : dom f = Prod.fst '' epi f := by
  ext x
  constructor
  · intro hx
    rcases eq_or_lt_of_le (bot_le : (⊥ : EReal) ≤ f x) with h | h
    · exact ⟨(x, 0), by simp [epi, ← h], rfl⟩
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top h.ne' hx
      exact ⟨(x, r), by simp [epi, hr], rfl⟩
  · rintro ⟨⟨y, μ⟩, hy, rfl⟩
    exact lt_of_le_of_lt hy (_root_.EReal.coe_lt_top μ)

/-- The epigraph is nonempty exactly when the effective domain is: both say `f ≢ +∞`. -/
theorem epi_nonempty_iff (f : E → EReal) : (epi f).Nonempty ↔ (dom f).Nonempty := by
  rw [dom_eq_fst_image_epi, Set.image_nonempty]

theorem epi_eq_empty_iff (f : E → EReal) : epi f = ∅ ↔ dom f = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, epi_nonempty_iff]

@[simp] theorem epi_top : epi (⊤ : E → EReal) = ∅ := by
  ext p
  simp [epi, Pi.top_apply]

/-- `f` is *proper* when it is finite somewhere and never takes the value `⊥`; equivalently, `epi f`
is nonempty and contains no vertical lines. -/
structure Proper (f : E → EReal) : Prop where
  /-- `f` is not identically `⊤`. -/
  dom_nonempty : (dom f).Nonempty
  /-- `f` never takes the value `⊥`. -/
  ne_bot : ∀ x, f x ≠ ⊥

/-- `f` restricted to `s` and extended by `⊤` off `s` — the standing encoding of "a convex function
given on a convex set". The `⨅` formulation avoids a decidability hypothesis;
`restrict_of_mem` and `restrict_of_notMem` are the defining equations. -/
noncomputable def restrict (s : Set E) (f : E → EReal) : E → EReal := fun x => ⨅ _ : x ∈ s, f x

@[simp] theorem restrict_of_mem {s : Set E} {f : E → EReal} {x : E} (hx : x ∈ s) :
    restrict s f x = f x := iInf_pos hx

@[simp] theorem restrict_of_notMem {s : Set E} {f : E → EReal} {x : E} (hx : x ∉ s) :
    restrict s f x = ⊤ := iInf_neg hx

/-! #### Non-negative scalar multiples

`EReal` obeys `0 · ∞ = 0`, so `0 · f` is the constant `0`, which is proper and convex; only the
*effective domain* statement needs `0 < c`, because `dom (0 · f)` is all of `E`. -/

/-- **A positive multiple of `f` has the same effective domain as `f`.** The hypothesis is
`0 < c`, not `0 ≤ c`: at `c = 0` the product is the constant `0` and its domain is everything. -/
theorem dom_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) :
    dom (fun x => (c : EReal) * f x) = dom f := by
  ext x
  rw [mem_dom, mem_dom]
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne le_top (EReal.coe_mul_ne_top hc h.ne)⟩
  by_contra hcon
  rw [top_le_iff.1 (not_lt.1 hcon), _root_.EReal.coe_mul_top_of_pos hc] at h
  exact lt_irrefl _ h

/-- **A non-negative multiple of a proper function is proper.** At `c = 0` the product is the
constant `0`, which is finite everywhere; at `c > 0` the domain is unchanged (`dom_coe_mul`). -/
theorem proper_coe_mul {c : ℝ} (hc : 0 ≤ c) {f : E → EReal} (hp : Proper f) :
    Proper (fun x => (c : EReal) * f x) := by
  refine ⟨?_, fun x => EReal.coe_mul_ne_bot hc (hp.ne_bot x)⟩
  obtain ⟨x₀, hx₀⟩ := hp.dom_nonempty
  refine ⟨x₀, ?_⟩
  rcases eq_or_lt_of_le hc with h | h
  · rw [mem_dom, ← h]; simp
  · exact mem_dom.2 (lt_of_le_of_ne le_top (EReal.coe_mul_ne_top h (mem_dom.1 hx₀).ne))

end Basic

/-! ### Convex functions -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A function `f : E → EReal` is convex when its epigraph is a convex subset of `E × ℝ`.
See `convexFn_iff_forall_lt` and `convexFn_iff_le` for the analytic forms. -/
structure ConvexFn (f : E → EReal) : Prop where
  /-- The epigraph of a convex function is convex. -/
  convex_epi : Convex ℝ (epi f)

@[simp] theorem convexFn_iff_convex_epi {f : E → EReal} : ConvexFn f ↔ Convex ℝ (epi f) :=
  ⟨fun h => h.convex_epi, fun h => ⟨h⟩⟩

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

/-- Conversely, the combination property characterises convexity. -/
theorem convexFn_of_epi_combo {f : E → EReal}
    (h : ∀ (x y : E) (μ ν : ℝ), f x ≤ (μ : EReal) → f y ≤ (ν : EReal) →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * μ + b * ν : ℝ) : EReal)) :
    ConvexFn f := by
  refine ⟨?_⟩
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  exact h x y μ ν hx hy a b ha hb hab

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
  rw [_root_.EReal.coe_eq_coe_iff, hl x y a b hab]
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
    obtain ⟨α', hxα', hα'⟩ := EReal.exists_real_btwn_of_lt_coe hx
    obtain ⟨β', hyβ', hβ'⟩ := EReal.exists_real_btwn_of_lt_coe hy
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
    · refine EReal.le_coe_of_forall_lt (fun q hq => ?_)
      have hx' : f x < ((μ + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hx (by exact_mod_cast (by linarith : μ < μ + (q - (a * μ + b * ν))))
      have hy' : f y < ((ν + (q - (a * μ + b * ν)) : ℝ) : EReal) :=
        lt_of_le_of_lt hy (by exact_mod_cast (by linarith : ν < ν + (q - (a * μ + b * ν))))
      have key := h x y a b ha' hb' hab _ _ hx' hy'
      have harith : a * (μ + (q - (a * μ + b * ν))) + b * (ν + (q - (a * μ + b * ν))) = q := by
        linear_combination (q - (a * μ + b * ν)) * hab
      rwa [harith] at key

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
        rw [hq, EReal.coe_mul_coe, EReal.top_add_coe]; exact le_top
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf x) hx
    rcases eq_top_or_lt_top (f y) with hy | hy
    · rw [hy, EReal.mul_top_of_pos (hacoe hb), hp, EReal.coe_mul_coe, EReal.coe_add_top]
      exact le_top
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf y) hy
    rw [hp, hq, EReal.coe_mul_coe, EReal.coe_mul_coe, ← EReal.coe_add]
    refine EReal.le_coe_of_forall_lt (fun r hr => ?_)
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
    rw [hp, hq, EReal.coe_mul_coe, EReal.coe_mul_coe, ← EReal.coe_add]
    rw [hp] at hx; rw [hq] at hy
    have hpα : p < α := by exact_mod_cast hx
    have hqβ : q < β := by exact_mod_cast hy
    exact_mod_cast (by nlinarith : a * p + b * q < a * α + b * β)

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
    refine le_of_eq (EReal.eq_bot_of_forall_le_coe (fun r => ?_))
    have := hf.epi_combo (μ := r) (ν := r) (hx'.trans bot_le) (hy'.trans bot_le) ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)
  | top => exact le_top
  | coe r =>
    have := hf.epi_combo hx' hy' ha'.le hb'.le hab
    refine this.trans (le_of_eq ?_)
    exact_mod_cast (by linear_combination r * hab : a * r + b * r = r)

/-- The effective domain of a convex function is convex. -/
theorem ConvexFn.convex_dom {f : E → EReal} (hf : ConvexFn f) : Convex ℝ (dom f) :=
  hf.convex_lt ⊤

/-! ### The bridge to Mathlib's `ConvexOn` -/

omit [AddCommGroup E] [Module ℝ E] in
theorem epi_restrict_coe (s : Set E) (g : E → ℝ) :
    epi (restrict s fun x => (g x : EReal)) = {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

/-- Mathlib's `ConvexOn` for a real-valued function on a set agrees with `ConvexFn` for its
extension by `⊤`. This is the interface through which the surface layer reuses Mathlib. -/
theorem convexOn_iff_convexFn (s : Set E) (g : E → ℝ) :
    ConvexOn ℝ s g ↔ ConvexFn (restrict s fun x => (g x : EReal)) := by
  rw [convexFn_iff_convex_epi, epi_restrict_coe]
  exact ⟨fun h => h.convex_epigraph, fun h => convexOn_of_convex_epigraph h⟩

end Module

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
