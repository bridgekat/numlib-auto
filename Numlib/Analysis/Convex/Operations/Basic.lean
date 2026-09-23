import Numlib.Analysis.Convex.Indicator

/-!
# Operations that preserve convexity: the epigraph-only ones

The operations whose convexity proof needs nothing beyond the epigraph API. Those that instead read
a function off a convex set in `E × ℝ` — infimal convolution, convex hulls of families, images under
linear maps — live elsewhere.

## Main results

* `convexFn_iSup`, `ConvexFn.sup` — pointwise suprema, via `epi_iSup`.
* `ConvexFn.add`, `ConvexFn.sum`, `dom_add` — sums, and the effective domain of a sum.
* `convexFn_coe_mul` (in `Numlib/Analysis/Convex/Epigraph.lean`) — multiplication by a
  nonnegative real.
* `ConvexFn.comp`, `ConvexFn.comp_extendTop` — composition with a nondecreasing convex function of
  one real variable.
* `convexFn_const`, `concaveFn_const` — constants.
* `ConvexFn.convexRestrict`, `ConvexFn.add_indicatorFn` — restriction to a convex set, the same
  operation as adding an indicator function.

## Implementation notes

Sums carry `∀ x, f x ≠ ⊥` where Rockafellar assumes properness: that is the half which avoids
`∞ - ∞`, and it cannot be dropped. On `ℝ` let `f` be `⊥` on `Ioi 0` and `⊤` elsewhere, `g` be `⊥` on
`Iio 0` and `⊤` elsewhere; both are convex, but `f + g` is `⊥` off `0` and `⊤` at `0`, with a
nonconvex epigraph `(ℝ \ {0}) ×ˢ univ`. The other half, `dom f` nonempty, is irrelevant.

## References

* [rockafellar1970convex] §5.
-/

open Set

namespace ConvexAnalysis

/-! ### Epigraphs of suprema, sums and restrictions: no linear structure on `E` is used -/

section Basic

variable {E : Type*}

/-- The epigraph of a pointwise supremum is the intersection of the epigraphs. Support functions
are computed this way. -/
theorem epi_iSup {ι : Sort*} (f : ι → E → EReal) : epi (fun x => ⨆ i, f i x) = ⋂ i, epi (f i) := by
  ext p
  simp [epi, iSup_le_iff]

theorem epi_biSup {ι : Type*} (s : Set ι) (f : ι → E → EReal) :
    epi (fun x => ⨆ i ∈ s, f i x) = ⋂ i ∈ s, epi (f i) := by
  ext p
  simp [epi, iSup_le_iff]

theorem epi_sup (f g : E → EReal) : epi (f ⊔ g) = epi f ∩ epi g := by
  ext p
  simp [epi, sup_le_iff]

/-- The effective domain of a sum is the intersection of the effective domains. Both `≠ ⊥`
hypotheses are needed: for `f x = ⊥` and `g x = ⊤`, `x` lies in `dom (f + g)` but not in `dom g`. -/
theorem convexDom_add {f g : E → EReal} (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) :
    convexDom (f + g) = convexDom f ∩ convexDom g := by
  ext x
  simp only [mem_convexDom, Pi.add_apply, Set.mem_inter_iff, lt_top_iff_ne_top]
  exact EReal.add_ne_top_iff_ne_top₂ (hf x) (hg x)

theorem epi_convexRestrict (s : Set E)
    (f : E → EReal) : epi (convexRestrict s f) = epi f ∩ s ×ˢ univ := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp]

end Basic

/-! ### Convexity of the operations -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem convexFn_const (c : EReal) : ConvexFn (fun _ : E => c) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : c ≤ (μ : EReal) := hx
  have hy' : c ≤ (ν : EReal) := hy
  rcases eq_or_ne c ⊥ with rfl | hc
  · exact bot_le
  obtain ⟨r, rfl⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top hc (hx'.trans_lt (EReal.coe_lt_top μ))
  have h1 : r ≤ μ := by exact_mod_cast hx'
  have h2 : r ≤ ν := by exact_mod_cast hy'
  have h3 : a * r + b * r = r := by linear_combination r * hab
  have h4 : a * r ≤ a * μ := mul_le_mul_of_nonneg_left h1 ha
  have h5 : b * r ≤ b * ν := mul_le_mul_of_nonneg_left h2 hb
  exact_mod_cast (by linarith : r ≤ a * μ + b * ν)

/-- Constant functions are concave; the mirror of `convexFn_const`. -/
theorem concaveFn_const (c : EReal) : ConcaveFn (fun _ : E => c) :=
  concaveFn_iff_convexFn_neg.2 (convexFn_const (-c))

/-- Its negative is convex too, which is why the functions both convex and concave are exactly the
affine ones. The pairing-presented form is `convexFn_affineFn`. -/
theorem convexFn_coe_linearMap (l : E →ₗ[ℝ] ℝ) :
    ConvexFn (fun x : E => ((l x : ℝ) : EReal)) := by
  have h := convexFn_add_coe (f := fun _ : E => (0 : EReal)) (convexFn_const 0)
    (l := fun x => l x) (fun x y a b _ => by simp [map_add, map_smul, smul_eq_mul])
  simpa using h

/-! #### Pointwise suprema -/

/-- A pointwise supremum of convex functions is convex. The index is a `Sort*`, so the empty family
is allowed: the supremum is then `⊥`, whose epigraph is all of `E × ℝ`. -/
theorem convexFn_iSup {ι : Sort*} {f : ι → E → EReal} (h : ∀ i, ConvexFn (f i)) :
    ConvexFn (fun x => ⨆ i, f i x) := by
  refine ⟨?_⟩
  rw [epi_iSup]
  exact convex_iInter fun i => (h i).convex_epi

/-- A pointwise supremum over an index set of convex functions is convex. -/
theorem convexFn_biSup {ι : Type*} {s : Set ι} {f : ι → E → EReal}
    (h : ∀ i ∈ s, ConvexFn (f i)) : ConvexFn (fun x => ⨆ i ∈ s, f i x) := by
  refine ⟨?_⟩
  rw [epi_biSup]
  exact convex_iInter₂ fun i hi => (h i hi).convex_epi

theorem ConvexFn.sup {f g : E → EReal} (hf : ConvexFn f) (hg : ConvexFn g) : ConvexFn (f ⊔ g) := by
  refine ⟨?_⟩
  rw [epi_sup]
  exact hf.convex_epi.inter hg.convex_epi

/-! #### Sums -/

/-- A sum of two convex functions is convex. Where the classical statement assumes properness this
needs only its `≠ ⊥` half, which prevents `∞ - ∞` and cannot be dropped; the module docstring has a
counterexample. -/
theorem ConvexFn.add {f g : E → EReal} (hf : ConvexFn f) (hg : ConvexFn g)
    (hf' : ∀ x, f x ≠ ⊥) (hg' : ∀ x, g x ≠ ⊥) : ConvexFn (f + g) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : f x + g x ≤ (μ : EReal) := hx
  have hy' : f y + g y ≤ (ν : EReal) := hy
  -- neither summand can be `⊤`, so all four values are real
  have hxt : f x ≠ ⊤ ∧ g x ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ (hf' x) (hg' x)).1
      (hx'.trans_lt (EReal.coe_lt_top μ)).ne
  have hyt : f y ≠ ⊤ ∧ g y ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ (hf' y) (hg' y)).1
      (hy'.trans_lt (EReal.coe_lt_top ν)).ne
  obtain ⟨p₁, hp₁⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf' x) (lt_top_iff_ne_top.2 hxt.1)
  obtain ⟨p₂, hp₂⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hg' x) (lt_top_iff_ne_top.2 hxt.2)
  obtain ⟨q₁, hq₁⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf' y) (lt_top_iff_ne_top.2 hyt.1)
  obtain ⟨q₂, hq₂⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hg' y) (lt_top_iff_ne_top.2 hyt.2)
  rw [hp₁, hp₂, ← EReal.coe_add, EReal.coe_le_coe_iff] at hx'
  rw [hq₁, hq₂, ← EReal.coe_add, EReal.coe_le_coe_iff] at hy'
  have hfc := hf.epi_combo hp₁.le hq₁.le ha hb hab
  have hgc := hg.epi_combo hp₂.le hq₂.le ha hb hab
  have hsum := add_le_add hfc hgc
  rw [← EReal.coe_add] at hsum
  refine hsum.trans ?_
  have h1 : a * (p₁ + p₂) ≤ a * μ := mul_le_mul_of_nonneg_left hx' ha
  have h2 : b * (q₁ + q₂) ≤ b * ν := mul_le_mul_of_nonneg_left hy' hb
  have h3 : a * p₁ + b * q₁ + (a * p₂ + b * q₂) = a * (p₁ + p₂) + b * (q₁ + q₂) := by ring
  exact_mod_cast (by linarith : a * p₁ + b * q₁ + (a * p₂ + b * q₂) ≤ a * μ + b * ν)

/-- A finite sum of convex functions, none of which takes the value `⊥`, is convex. -/
theorem ConvexFn.sum {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) (hf' : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) :
    ConvexFn (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.cons_induction with
  | empty => simpa using convexFn_const (E := E) 0
  | cons i t hi ih =>
    have key : ConvexFn (f i + fun x => ∑ j ∈ t, f j x) :=
      (hf i (by simp)).add
        (ih (fun j hj => hf j (by simp [hj])) (fun j hj => hf' j (by simp [hj])))
        (hf' i (by simp))
        (fun x => EReal.sum_ne_bot fun j hj => hf' j (by simp [hj]) x)
    have hfun : (fun x => ∑ j ∈ Finset.cons i t hi, f j x) = (f i + fun x => ∑ j ∈ t, f j x) := by
      funext x; simp [Finset.sum_cons]
    rw [hfun]
    exact key

/-! #### Composition with a nondecreasing convex function -/

/-- `φ : ℝ → EReal` extended to `EReal → EReal` by `φ (+∞) = +∞` and `φ (-∞) = -∞`, the choice that
keeps the extension monotone; the composition rule never applies `φ` at `⊥`. -/
noncomputable def extendTop (φ : ℝ → EReal) : EReal → EReal :=
  EReal.rec ⊥ φ ⊤

@[simp] theorem extendTop_coe (φ : ℝ → EReal) (r : ℝ) : extendTop φ (r : EReal) = φ r := rfl

@[simp] theorem extendTop_top (φ : ℝ → EReal) : extendTop φ ⊤ = ⊤ := rfl

@[simp] theorem extendTop_bot (φ : ℝ → EReal) : extendTop φ ⊥ = ⊥ := rfl

theorem monotone_extendTop {φ : ℝ → EReal} (h : Monotone φ) : Monotone (extendTop φ) := by
  intro z w hzw
  induction z with
  | bot => simp
  | top =>
    obtain rfl := top_le_iff.1 hzw
    exact le_rfl
  | coe r =>
    induction w with
    | bot => exact absurd hzw (by simp)
    | top => simp
    | coe s => exact h (by exact_mod_cast hzw)

/-- A nondecreasing convex `φ` composed with a convex `f` is convex, stated for `φ : EReal → EReal`
rather than the classical `φ : ℝ → (-∞, +∞]`. `EReal` is not an `ℝ`-module, so convexity of `φ` is
required only where it is statable; off the reals the proof uses just monotonicity and `φ ⊤ = ⊤`.
That last is not decoration — a monotone convex `φ : ℝ → EReal` bounded above is constant, and
gluing a strictly larger finite value at `⊤` breaks convexity of `φ ∘ f` as soon as `dom f` has
nonconvex complement. -/
theorem ConvexFn.comp {f : E → EReal} {φ : EReal → EReal} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hφ : ConvexFn fun r : ℝ => φ (r : EReal)) (hmono : Monotone φ)
    (htop : φ ⊤ = ⊤) : ConvexFn (fun x => φ (f x)) := by
  refine convexFn_of_epi_combo (fun x y μ ν hx hy a b ha hb hab => ?_)
  have hx' : φ (f x) ≤ (μ : EReal) := hx
  have hy' : φ (f y) ≤ (ν : EReal) := hy
  -- `f` cannot be `⊤` where `φ ∘ f` is bounded above by a real, because `φ ⊤ = ⊤`
  have hfx : f x < ⊤ := by
    rcases eq_top_or_lt_top (f x) with h | h
    · rw [h, htop] at hx'
      exact absurd hx' (not_le.2 (EReal.coe_lt_top μ))
    · exact h
  have hfy : f y < ⊤ := by
    rcases eq_top_or_lt_top (f y) with h | h
    · rw [h, htop] at hy'
      exact absurd hy' (not_le.2 (EReal.coe_lt_top ν))
    · exact h
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf' x) hfx
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf' y) hfy
  rw [hp] at hx'
  rw [hq] at hy'
  have hcombo : f (a • x + b • y) ≤ ((a * p + b * q : ℝ) : EReal) :=
    hf.epi_combo hp.le hq.le ha hb hab
  refine (hmono hcombo).trans ?_
  simpa [smul_eq_mul] using hφ.epi_combo hx' hy' ha hb hab

/-- The same composition rule in its classical shape: `φ` is a nondecreasing convex function of one
real variable, and `x ↦ φ (f x)` is convex under the convention `φ (+∞) = +∞`. -/
theorem ConvexFn.comp_extendTop {f : E → EReal} {φ : ℝ → EReal} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hφ : ConvexFn φ) (hmono : Monotone φ) :
    ConvexFn (fun x => extendTop φ (f x)) :=
  hf.comp hf' hφ (monotone_extendTop hmono) (extendTop_top φ)

/-! #### Restriction to a convex set -/

theorem ConvexFn.convexRestrict {f : E → EReal} {s : Set E} (hf : ConvexFn f) (hs : Convex ℝ s) :
    ConvexFn (ConvexAnalysis.convexRestrict s f) := by
  refine ⟨?_⟩
  rw [epi_convexRestrict]
  exact hf.convex_epi.inter (hs.prod convex_univ)

/-- Restricting a concave function to a convex set — extending by `⊥` off it — gives a concave
function; the mirror of `ConvexFn.convexRestrict`. -/
theorem ConcaveFn.concaveRestrict {g : E → EReal} {s : Set E} (hg : ConcaveFn g)
    (hs : Convex ℝ s) : ConcaveFn (ConvexAnalysis.concaveRestrict s g) := by
  refine concaveFn_iff_convexFn_neg.2 ?_
  rw [neg_concaveRestrict]
  exact hg.convexFn_neg.convexRestrict hs

/-- Adding the indicator function of a convex set is restriction to that set, and preserves
convexity. -/
theorem ConvexFn.add_indicatorFn {f : E → EReal} {s : Set E} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hs : Convex ℝ s) : ConvexFn (f + indicatorFn s) := by
  rw [← convexRestrict_eq_add_indicatorFn hf']
  exact hf.convexRestrict hs

end Module

end ConvexAnalysis
