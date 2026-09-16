import Numlib.Analysis.Convex.Duality.Gauge
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Lattice
import Numlib.Analysis.Convex.Operations.Image
import Numlib.Analysis.Convex.Operations.InfConv
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar §5: functional operations

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5:
the operations that build new convex functions out of old — outer composition, addition, infimal
convolution `□`, pointwise suprema, the convex hull of a collection, and image and inverse image
under a linear map.

All 8 numbered results of §5 are formalized. Theorems 5.7 and 5.8 carry no letter labels in the
book, so the declaration suffixes are the book's own symbols: `gA` and `Ah` for 5.7, and the four
displayed function names `f`, `g`, `h`, `k` for 5.8. `ℝⁿ⁺¹` is `Rn n × ℝ` here, which is what "a
convex set `F` in `ℝⁿ⁺¹`" means when Theorem 5.3 goes on to write `(x, μ) ∈ F`.

## Main results

* `theorem_5_1` — `φ ∘ f` is convex for convex `f` and non-decreasing convex `φ`.
* `theorem_5_2` — the sum of two proper convex functions is convex.
* `theorem_5_3` — the lower boundary of a convex set in `ℝⁿ⁺¹` is a convex function; it is the
  construction the rest of the section is phrased through.
* `theorem_5_4`, `convexFn_infimalConvolution` — the infimal convolute of proper convex functions
  is convex, and `□` needs no properness in the epigraph form.
* `infimalConvolution_apply`, `dom_infimalConvolution`, `infimalConvolution_isCommMonoid` — the
  classical formula `(f □ g) x = infᵧ {f (x - y) + g y}`, the effective domain `dom f + dom g`,
  and commutativity and associativity with `δ(· | 0)` as identity.
* `convexFn_leftSMul`, `convexFn_rightSMul`, `rightSMul_apply_pos`, `rightSMul_zero`,
  `rightSMul_zero_of_top`, `posHomogeneous_iff_rightSMul_eq` — the two scalar multiplications of
  the section, and `f` positively homogeneous exactly when `fλ = f` for all `λ > 0`.
* `isGreatest_posHomGen`, `posHomGen_apply` — the positively homogeneous convex function generated
  by `h`, and its formula `inf {(hλ) x | λ ≥ 0}`.
* `theorem_5_5` — a pointwise supremum of convex functions is convex; `convexFn_maxCoord` and
  `convexFn_tchebycheffNorm` are the section's two illustrations of it.
* `isGreatest_conv`, `isGreatest_convCollection`, `theorem_5_6` — the convex hull of a function
  and of a collection, and its explicit formula for proper convex `fᵢ`.
* `coe_iInf_convexFns`, `coe_iSup_convexFns` — the convex functions on `ℝⁿ` form a complete
  lattice, with `conv {fᵢ}` as infimum and the pointwise supremum as supremum.
* `theorem_5_7_gA`, `theorem_5_7_Ah` — inverse image and image of a convex function under a linear
  transformation.
* `theorem_5_8_f`, `theorem_5_8_g`, `theorem_5_8_h`, `theorem_5_8_k` — the four functions of
  Theorem 5.8, obtained by adding in `x` alone, in `λ` alone, and in both.

## Two traps

**Properness is not preserved by `□`.** No declaration here concludes properness of an infimal
convolute, and `exists_not_proper_infimalConvolution` is the witness: `f x = ⟨v, x⟩` and
`g x = -⟨v, x⟩` are proper convex with `f □ g ≡ -∞`. That is also why the backbone defines `□` by
adding epigraphs rather than by the infimum formula, which would be `∞ - ∞`;
`infimalConvolution_apply` recovers the formula under properness.

**`f0` is defined by cases**, as in the book: `rightSMul_zero` gives `f0 = δ(· | 0)` when
`f ≢ +∞`, and `rightSMul_zero_of_top` gives `f0 = f` when `f ≡ +∞`. `hom_apply_smul` is where
that case split meets §4's `0 · ∞ = 0`, and the two agree.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

/-! ### Linear functionals on `ℝⁿ`

Two small pieces of `ℝⁿ` bookkeeping that the examples of this section need and that the backbone,
which is written for a general topological vector space, has no reason to carry. -/

/-- The `j`-th coordinate of `ℝⁿ`, as a linear functional. -/
noncomputable def coordFunctional (n : ℕ) (j : Fin n) : Rn n →ₗ[ℝ] ℝ where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordFunctional_apply {n : ℕ} (j : Fin n) (x : Rn n) :
    coordFunctional n j x = x j := rfl

/-! ### Theorem 5.1 -/

/-- **Theorem 5.1.** For convex `f : ℝⁿ → (-∞, +∞]` and non-decreasing convex `φ : ℝ → (-∞, +∞]`,
`φ ∘ f` is convex. `extendTop φ` is `φ` extended by the book's convention `φ (+∞) = +∞`. -/
theorem theorem_5_1 {n : ℕ} {f : Rn n → EReal} {φ : ℝ → EReal} (hf : ConvexFn f)
    (hf' : ∀ x, f x ≠ ⊥) (hφ : ConvexFn φ) (hmono : Monotone φ) :
    ConvexFn fun x => extendTop φ (f x) :=
  hf.comp_extendTop hf' hφ hmono

/-! ### Theorem 5.2 -/

/-- **Theorem 5.2.** The sum of two proper convex functions is convex. Properness is there only
to avoid `∞ - ∞`, and only its `≠ -∞` half is used. -/
theorem theorem_5_2 {n : ℕ} {f₁ f₂ : Rn n → EReal} (h₁ : ConvexFn f₁) (hp₁ : Proper f₁)
    (h₂ : ConvexFn f₂) (hp₂ : Proper f₂) : ConvexFn (f₁ + f₂) :=
  h₁.add h₂ hp₁.ne_bot hp₂.ne_bot

/-! ### Theorem 5.3 -/

/-- **Theorem 5.3.** The lower boundary `f x = inf {μ | (x, μ) ∈ F}` of a convex set `F` in
`ℝⁿ⁺¹` is a convex function. `ℝⁿ⁺¹` is read as `Rn n × ℝ`. -/
theorem theorem_5_3 {n : ℕ} {F : Set (Rn n × ℝ)} (hF : Convex ℝ F) {f : Rn n → EReal}
    (hf : ∀ x, f x = ⨅ μ ∈ {μ : ℝ | (x, μ) ∈ F}, (μ : EReal)) : ConvexFn f := by
  have hfF : f = ofEpi F := funext hf
  rw [hfF]
  exact convexFn_ofEpi hF

/-! ### Theorem 5.4 -/

/-- A convex function of a single coordinate of `(ℝⁿ)ᵐ` is convex as a function of the whole
tuple: this is the inverse image under the `i`-th projection, Theorem 5.7. -/
theorem convexFn_coord {n m : ℕ} {g : Rn n → EReal} (hg : ConvexFn g) (i : Fin m) :
    ConvexFn fun p : Fin m → Rn n => g (p i) := by
  have h := convexFn_compLin (E := Fin m → Rn n) (G := Rn n)
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Rn n) i) hg
  exact h

/-- The linear map `(x₁, …, xₘ) ↦ x₁ + ⋯ + xₘ` on `(ℝⁿ)ᵐ`. Every `m`-ary operation of this
section that "adds in `x`" is an image under this map, in the sense of Theorem 5.7. -/
noncomputable def sumLin (n m : ℕ) : (Fin m → Rn n) →ₗ[ℝ] Rn n :=
  ∑ i, LinearMap.proj i

@[simp] theorem sumLin_apply {n m : ℕ} (p : Fin m → Rn n) : sumLin n m p = ∑ i, p i := by
  simp [sumLin, LinearMap.sum_apply]

/-- **Theorem 5.4.** For proper convex `f₁, …, fₘ`, the infimal convolute
`f x = inf {f₁x₁ + ⋯ + fₘxₘ | x₁ + ⋯ + xₘ = x}` is convex. Properness is used only through its
`≠ -∞` half, which is what makes the sum unambiguous. -/
theorem theorem_5_4 {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) :
    ConvexFn fun x => ⨅ p ∈ {p : Fin m → Rn n | ∑ i, p i = x}, ∑ i, f i (p i) := by
  have hsep : ConvexFn fun p : Fin m → Rn n => ∑ i, f i (p i) :=
    ConvexFn.sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => convexFn_coord (hf i) i) (fun i _ p => (hp i).ne_bot (p i))
  have hmap := convexFn_mapLin (sumLin n m) hsep
  have hkey : mapLin (sumLin n m) (fun p : Fin m → Rn n => ∑ i, f i (p i))
      = fun x => ⨅ p ∈ {p : Fin m → Rn n | ∑ i, p i = x}, ∑ i, f i (p i) := by
    funext x
    simp only [mapLin, sumLin_apply]
  rwa [hkey] at hmap

/-! ### Infimal convolution

Rockafellar, §5, after Theorem 5.4: "The function `f` in Theorem 5.4 will be denoted by
`f₁ □ f₂ □ ⋯ □ fₘ`. The operation `□` is called infimal convolution." -/

@[inherit_doc ConvexAnalysis.infConv]
scoped infixl:65 " □ " => ConvexAnalysis.infConv

/-- **Theorem 5.4**, binary case: `f □ g` is convex whenever `f` and `g` are. No properness is
needed, the epigraph definition `f □ g = ofEpi (epi f + epi g)` being Theorem 5.3 applied to a sum
of convex sets; the book's properness is what makes the *infimum formula* meaningful. -/
theorem convexFn_infimalConvolution {n : ℕ} {f g : Rn n → EReal} (hf : ConvexFn f)
    (hg : ConvexFn g) : ConvexFn (f □ g) :=
  convexFn_infConv hf hg

/-- For two functions, `(f □ g) x = infᵧ {f (x - y) + g y}` — the analogue of the classical
formula for integral convolution. Properness is what makes the right-hand side unambiguous; `□`
is *defined* through epigraph addition, as in the book, because this infimum produces the
forbidden `∞ - ∞` when one function reaches `-∞`. -/
theorem infimalConvolution_apply {n : ℕ} {f g : Rn n → EReal} (hf : Proper f) (hg : Proper g)
    (x : Rn n) : (f □ g) x = ⨅ y, f (x - y) + g y :=
  infConv_apply hf.ne_bot hg.ne_bot x

/-- **Rockafellar, §5.** "The effective domain of `f □ g` is the sum of `dom f` and `dom g`." It
needs no hypothesis at all. -/
theorem dom_infimalConvolution {n : ℕ} (f g : Rn n → EReal) :
    dom (f □ g) = dom f + dom g :=
  dom_infConv f g

/-- **Rockafellar, §5.** "`f □ δ(· | a)` is the function whose graph is obtained by translating
the graph of `f` horizontally by `a`." -/
theorem infimalConvolution_indicatorFn_singleton {n : ℕ} (f : Rn n → EReal) (a : Rn n) :
    (f □ indicatorFn ({a} : Set (Rn n))) = fun x => f (x - a) :=
  infConv_indicatorFn_singleton f a

/-- Infimal convolution is commutative and associative on all functions `ℝⁿ → [-∞, +∞]`, with
`δ(· | 0)` as identity: the monoid structure lives on the type synonym `InfConvFn (Rn n)`. -/
theorem infimalConvolution_isCommMonoid {n : ℕ} :
    (∀ f g : Rn n → EReal, (f □ g) = g □ f) ∧
      (∀ f g h : Rn n → EReal, ((f □ g) □ h) = f □ (g □ h)) ∧
      (∀ f : Rn n → EReal, (f □ indicatorFn ({0} : Set (Rn n))) = f) :=
  ⟨infConv_comm, infConv_assoc, infConv_indicatorFn_zero⟩

/-- **Properness is not preserved by `□`.** For `v ≠ 0` the pair `f x = ⟨v, x⟩`, `g x = -⟨v, x⟩`
is finite, hence proper, and convex, while `(f □ g) x = -∞` everywhere. This is why no result of
§5 concludes properness of an infimal convolute. -/
theorem exists_not_proper_infimalConvolution {n : ℕ} {v : Rn n} (hv : v ≠ 0) :
    ∃ f g : Rn n → EReal, ConvexFn f ∧ Proper f ∧ ConvexFn g ∧ Proper g ∧ ¬ Proper (f □ g) := by
  have hsurj : Function.Surjective (pairing n v) := by
    refine LinearMap.surjective_of_ne_zero ?_
    intro hzero
    refine hv ((inner_self_eq_zero (𝕜 := ℝ)).1 ?_)
    have hvv := congrArg (fun t : Rn n →ₗ[ℝ] ℝ => t v) hzero
    simpa using hvv
  have hbot : infConv (fun x : Rn n => ((pairing n v x : ℝ) : EReal))
      (fun x : Rn n => ((-(pairing n v x) : ℝ) : EReal)) 0 = ⊥ := by
    rw [infConv_apply (fun x => by simp) (fun x => by simp) 0]
    refine le_bot_iff.1 (EReal.le_of_forall_lt_iff_le.1 fun r _ => ?_)
    obtain ⟨y, hy⟩ := hsurj (-r / 2)
    refine le_trans (iInf_le _ y) (le_of_eq ?_)
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff, map_sub, map_zero, hy]
    ring
  exact ⟨_, _, convexFn_coe_linearMap (pairing n v), ⟨⟨0, by simp⟩, fun x => by simp⟩,
    convexFn_coe_linearMap (-(pairing n v)), ⟨⟨0, by simp⟩, fun x => by simp⟩,
    fun hproper => hproper.ne_bot 0 hbot⟩

/-! ### Left and right scalar multiplication

Rockafellar, §5: `(λf) x = λ (f x)` for `λ ≥ 0`, and `fλ` is the function obtained from
Theorem 5.3 with `F = λ (epi f)`. -/

/-- Non-negative left scalar multiplication `(λ f) x = λ (f x)` preserves convexity. `EReal`
obeys the book's `0 · ∞ = 0`, so `λ = 0` is not a special case. -/
theorem convexFn_leftSMul {n : ℕ} {f : Rn n → EReal} (l : ℝ) (hl : 0 ≤ l) (hf : ConvexFn f) :
    ConvexFn fun x => (l : EReal) * f x :=
  hf.smul l hl

/-- **Rockafellar, §5.** Right scalar multiplication preserves convexity: `fλ` is Theorem 5.3
applied to the convex set `λ (epi f)`. -/
theorem convexFn_rightSMul {n : ℕ} {f : Rn n → EReal} (l : ℝ) (hf : ConvexFn f) :
    ConvexFn (smulRight f l) :=
  convexFn_smulRight l hf

/-- **Rockafellar, §5**, first branch of the definition of `fλ`:
`(fλ) x = λ f (λ⁻¹ x)` for `λ > 0`. -/
theorem rightSMul_apply_pos {n : ℕ} {l : ℝ} (hl : 0 < l) (f : Rn n → EReal) (x : Rn n) :
    smulRight f l x = (l : EReal) * f (l⁻¹ • x) :=
  smulRight_apply_pos hl f x

/-- Right scalar multiplication at zero: `(f0) x = δ(x | 0)` provided `f ≢ +∞`. The side
condition is the book's own and is not decoration; see `rightSMul_zero_of_top`. -/
theorem rightSMul_zero {n : ℕ} {f : Rn n → EReal} (hf : (dom f).Nonempty) :
    smulRight f 0 = indicatorFn ({0} : Set (Rn n)) :=
  smulRight_zero hf

/-- **Rockafellar, §5**, third branch: "trivially `f0 = f` if `f ≡ +∞`". Together with
`rightSMul_zero` this is the whole of the book's definition by cases at `λ = 0`. -/
theorem rightSMul_zero_of_top {n : ℕ} {f : Rn n → EReal} (hf : f = ⊤) :
    smulRight f 0 = f := by
  rw [smulRight_of_epi_eq_empty (by rw [hf]; exact epi_top) 0, hf]

/-- **Rockafellar, §5.** "A function `f` is positively homogeneous if and only if `fλ = f` for
every `λ > 0`." -/
theorem posHomogeneous_iff_rightSMul_eq {n : ℕ} {f : Rn n → EReal} :
    PosHomogeneous f ↔ ∀ l > (0 : ℝ), smulRight f l = f :=
  posHomogeneous_iff_smulRight_eq

/-! ### The positively homogeneous convex function generated by `h` -/

/-- The **positively homogeneous convex function generated by `h`**: the greatest positively
homogeneous convex `f` with `f 0 ≤ 0` and `f ≤ h`, obtained by applying Theorem 5.3 to the convex
cone in `ℝⁿ⁺¹` generated by `epi h`. Not the backbone's `hom`, which is the same construction
applied to the level-one lift of `h` and so lives one dimension up. -/
theorem isGreatest_posHomGen {n : ℕ} (h : Rn n → EReal) :
    IsGreatest {f : Rn n → EReal | PosHomogeneous f ∧ ConvexFn f ∧ f 0 ≤ 0 ∧ f ≤ h}
      (posHomGen h) :=
  posHomGen_isGreatest h

/-- **Rockafellar, §5.** `f x = inf {(hλ) x | λ ≥ 0}` for the positively homogeneous convex function
`f` generated by `h`; " `λ = 0` can be omitted from the infimum if `x ≠ 0` ". This is the form with
`λ = 0` omitted. -/
theorem posHomGen_apply {n : ℕ} {h : Rn n → EReal} (hh : ConvexFn h) {x : Rn n} (hx : x ≠ 0) :
    posHomGen h x = ⨅ l > (0 : ℝ), smulRight h l x := by
  rw [posHomGen_apply_of_ne_zero hh hx]
  exact iInf_congr fun l => iInf_congr fun hl => (smulRight_apply_pos hl h x).symm

/-! ### Theorem 5.5 -/

/-- **Theorem 5.5.** The pointwise supremum of an arbitrary collection of convex
functions is convex. -/
theorem theorem_5_5 {n : ℕ} {ι : Sort*} {f : ι → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    ConvexFn fun x => ⨆ i, f i x :=
  convexFn_iSup hf

/-- **Rockafellar, §5**, the illustration after Theorem 5.5: the function assigning to
`x = (ξ₁, …, ξₙ)` the greatest of its components is convex, "because it is the pointwise supremum
of the linear functions `⟨x, eⱼ⟩`". (It is also the support function of the unit simplex.) -/
theorem convexFn_maxCoord {n : ℕ} :
    ConvexFn fun x : Rn n => ⨆ j : Fin n, ((x j : ℝ) : EReal) :=
  convexFn_iSup fun j => convexFn_coe_linearMap (coordFunctional n j)

/-- **Rockafellar, §5**: the convexity of `k x = max {|ξⱼ| : j = 1, …, n}`, "which is called the
**Tchebycheff norm** on `ℝⁿ`, can be seen similarly from Theorem 5.5". It is the pointwise supremum
of the `2n` linear functions `± ξⱼ`. -/
theorem convexFn_tchebycheffNorm {n : ℕ} :
    ConvexFn fun x : Rn n => ⨆ j : Fin n, ((|x j| : ℝ) : EReal) := by
  have hrw : (fun x : Rn n => ⨆ j : Fin n, ((|x j| : ℝ) : EReal))
      = fun x : Rn n => ⨆ p : Fin n × Bool, ((cond p.2 (x p.1) (-(x p.1)) : ℝ) : EReal) := by
    funext x
    rw [iSup_prod]
    refine iSup_congr fun j => ?_
    simp only [abs_eq_max_neg, iSup_bool_eq, Bool.cond_true, Bool.cond_false]
    exact_mod_cast rfl
  rw [hrw]
  refine convexFn_iSup fun p => ?_
  obtain ⟨j, b⟩ := p
  cases b
  · exact convexFn_coe_linearMap (-coordFunctional n j)
  · exact convexFn_coe_linearMap (coordFunctional n j)

/-! ### The convex hull of a function, and of a collection

`conv g` is Theorem 5.3 applied to `F = conv (epi g)`, and `conv {fᵢ}` the same with the convex
hull of the union of the epigraphs. -/

/-- **Rockafellar, §5.** `conv g` "is the greatest convex function majorized by `g`". Restates
`isGreatest_convHullFn`. -/
theorem isGreatest_conv {n : ℕ} (g : Rn n → EReal) :
    IsGreatest {h : Rn n → EReal | ConvexFn h ∧ h ≤ g} (convHullFn g) :=
  isGreatest_convHullFn g

/-- **Rockafellar, §5.** `conv {fᵢ | i ∈ I}` "is the greatest convex function `f` (not necessarily
proper) on `ℝⁿ` such that `f x ≤ fᵢ x` for every `x ∈ ℝⁿ` and every `i ∈ I`". Restates
`isGreatest_convFn`. -/
theorem isGreatest_convCollection {n : ℕ} {ι : Sort*} (f : ι → Rn n → EReal) :
    IsGreatest {g : Rn n → EReal | ConvexFn g ∧ ∀ i, g ≤ f i} (convFn f) :=
  isGreatest_convFn f

/-! ### Theorem 5.6 -/

/-- **Theorem 5.6.** The convex hull of a collection of proper convex functions is
`f x = inf {∑ᵢ λᵢ fᵢ xᵢ | ∑ᵢ λᵢ xᵢ = x}`, over all representations of `x` as a convex combination
with finitely many non-zero coefficients (carried by the `Finset`). The function-level analogue of
Theorem 2.3. -/
theorem theorem_5_6 {n : ℕ} {ι : Type*} {f : ι → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) (x : Rn n) :
    convFn f x = sInf {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → Rn n),
      (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
        z = ∑ i ∈ t, (w i : EReal) * f i (p i)} :=
  convFn_apply hf (fun i y => (hp i).ne_bot y) x

/-- The convex functions on `ℝⁿ`, ordered pointwise, form a **complete lattice** with greatest
lower bound `conv {fᵢ}` and least upper bound `sup {fᵢ}`. The lattice is `ConvexFns (Rn n)`, and
`ConvexFns.not_coe_inf_eq_inf` is the warning behind the book's "(relative to this particular
partially ordered set!)": the meet is not the pointwise infimum. -/
theorem coe_iInf_convexFns {n : ℕ} {ι : Sort*} (f : ι → ConvexFns (Rn n)) :
    ((⨅ i, f i : ConvexFns (Rn n)) : Rn n → EReal) = convFn fun i => (f i : Rn n → EReal) :=
  ConvexFns.coe_iInf f

/-- The other half of the lattice sentence: the least upper bound is the pointwise supremum,
which is Theorem 5.5. -/
theorem coe_iSup_convexFns {n : ℕ} {ι : Sort*} (f : ι → ConvexFns (Rn n)) (x : Rn n) :
    ((⨆ i, f i : ConvexFns (Rn n)) : Rn n → EReal) x = ⨆ i, (f i : Rn n → EReal) x :=
  ConvexFns.coe_iSup_apply f x

/-! ### Theorem 5.7 -/

/-- **Theorem 5.7**, first assertion. The *inverse image* `(gA) x = g (A x)` of a convex function
under a linear transformation is convex. -/
theorem theorem_5_7_gA {n m : ℕ} (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g) :
    ConvexFn fun x => g (A x) :=
  convexFn_compLin A hg

/-- **Theorem 5.7**, second assertion. The *image* `(Ah) y = inf {h x | A x = y}` of a convex
function is convex. The infimum need not be attained, which is why `Ah` is not read off the image
of `epi h` as a set. -/
theorem theorem_5_7_Ah {n m : ℕ} (A : Rn n →ₗ[ℝ] Rn m) {h : Rn n → EReal} (hh : ConvexFn h) :
    ConvexFn fun y => ⨅ x ∈ {x | A x = y}, h x :=
  convexFn_mapLin A hh

/-! ### Theorem 5.8

The book derives the four operations below from partial additions of convex cones in `ℝⁿ⁺²`. The
statements are four explicit formulas, and each is an instance of Theorem 5.7 applied to a jointly
convex function of the auxiliary variables, so nothing here depends on that construction. -/

/-- The linear map `(λ, x) ↦ (λ₁ + ⋯ + λₘ, x)`, along which the two "adding in `λ`" operations of
Theorem 5.8 are images. -/
noncomputable def homSumLin (n m : ℕ) : ((Fin m → ℝ) × Rn n) →ₗ[ℝ] ℝ × Rn n :=
  LinearMap.prod ((∑ i, LinearMap.proj i).comp (LinearMap.fst ℝ (Fin m → ℝ) (Rn n)))
    (LinearMap.snd ℝ (Fin m → ℝ) (Rn n))

@[simp] theorem homSumLin_apply {n m : ℕ} (q : (Fin m → ℝ) × Rn n) :
    homSumLin n m q = (∑ i, q.1 i, q.2) := by
  simp [homSumLin]

/-- The linear map `(λ, x) ↦ (λᵢ, x)`, which reads off the `i`-th homogenising variable. -/
noncomputable def coordHomLin (n m : ℕ) (i : Fin m) : ((Fin m → ℝ) × Rn n) →ₗ[ℝ] ℝ × Rn n :=
  LinearMap.prod ((LinearMap.proj i).comp (LinearMap.fst ℝ (Fin m → ℝ) (Rn n)))
    (LinearMap.snd ℝ (Fin m → ℝ) (Rn n))

@[simp] theorem coordHomLin_apply {n m : ℕ} (i : Fin m) (q : (Fin m → ℝ) × Rn n) :
    coordHomLin n m i q = (q.1 i, q.2) := rfl

/-- The joint convexity behind clauses `g` and `h` of Theorem 5.8: `(λ, x) ↦ (fᵢ λᵢ) x` is convex
on `ℝᵐ × ℝⁿ`, since it is the inverse image of `hom fᵢ` under `(λ, x) ↦ (λᵢ, x)`. -/
theorem convexFn_hom_coord {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (i : Fin m) : ConvexFn fun q : (Fin m → ℝ) × Rn n => hom (f i) (q.1 i, q.2) := by
  have h := convexFn_compLin (coordHomLin n m i) (convexFn_hom (hf i))
  exact h

/-- **Theorem 5.8**, first function. `f x = inf {max {f₁x₁, …, fₘxₘ} | x₁ + ⋯ + xₘ = x}` is
convex, the book's "adding in `x` alone". Stated without the properness the book assumes: the
proof does not use it. -/
theorem theorem_5_8_f {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    ConvexFn fun x => ⨅ p ∈ {p : Fin m → Rn n | ∑ i, p i = x}, ⨆ i, f i (p i) := by
  have hsup : ConvexFn fun p : Fin m → Rn n => ⨆ i, f i (p i) :=
    convexFn_iSup fun i => convexFn_coord (hf i) i
  have hmap := convexFn_mapLin (sumLin n m) hsup
  have hkey : mapLin (sumLin n m) (fun p : Fin m → Rn n => ⨆ i, f i (p i))
      = fun x => ⨅ p ∈ {p : Fin m → Rn n | ∑ i, p i = x}, ⨆ i, f i (p i) := by
    funext x
    simp only [mapLin, sumLin_apply]
  rwa [hkey] at hmap

/-- **Theorem 5.8**, second function. For proper convex `f₁, …, fₘ`,
`g x = inf {(f₁λ₁) x + ⋯ + (fₘλₘ) x | λᵢ ≥ 0, ∑ λᵢ = 1}` is convex, the book's "adding in `λ` and
`μ`". Not the formula for `conv {f₁, …, fₘ}` after Theorem 5.6, which has `f₁λ₁ □ ⋯ □ fₘλₘ` in
place of the pointwise sum. -/
theorem theorem_5_8_g {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) :
    ConvexFn fun x => ⨅ l ∈ {l : Fin m → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1},
      ∑ i, smulRight (f i) (l i) x := by
  have hPsi : ConvexFn fun q : (Fin m → ℝ) × Rn n => ∑ i, hom (f i) (q.1 i, q.2) :=
    ConvexFn.sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => convexFn_hom_coord hf i) (fun i _ q => hom_ne_bot (hp i).ne_bot (q.1 i, q.2))
  have hslice := (convexFn_mapLin (homSumLin n m) hPsi).slice_left 1
  have hkey : (fun x : Rn n =>
        mapLin (homSumLin n m) (fun q : (Fin m → ℝ) × Rn n => ∑ i, hom (f i) (q.1 i, q.2)) (1, x))
      = fun x => ⨅ l ∈ {l : Fin m → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1},
        ∑ i, smulRight (f i) (l i) x := by
    funext x
    refine le_antisymm (le_iInf₂ fun l hl => ?_) (le_mapLin fun q hq => ?_)
    · refine (mapLin_le (x := (l, x)) ?_).trans_eq ?_
      · rw [homSumLin_apply, hl.2]
      · exact Finset.sum_congr rfl fun i _ => hom_apply_nonneg (hl.1 i) (f i) x
    · obtain ⟨l, y⟩ := q
      rw [homSumLin_apply, Prod.mk.injEq] at hq
      obtain ⟨hq₁, rfl⟩ := hq
      by_cases hpos : ∀ i, 0 ≤ l i
      · refine le_trans (iInf₂_le l ⟨hpos, hq₁⟩) (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => (hom_apply_nonneg (hpos i) (f i) y).symm
      · obtain ⟨j, hj⟩ := not_forall.1 hpos
        have hbot : ∀ i ∈ (Finset.univ : Finset (Fin m)), hom (f i) (l i, y) ≠ ⊥ :=
          fun i _ => hom_ne_bot (hp i).ne_bot (l i, y)
        have htop : (∑ i, hom (f i) (l i, y)) = ⊤ := by
          by_contra hne
          exact absurd (hom_apply_neg (not_le.1 hj) (f j) y)
            (EReal.forall_ne_top_of_sum_ne_top _ _ hbot hne j (Finset.mem_univ j))
        rw [htop]
        exact le_top
  rwa [hkey] at hslice

/-- **Theorem 5.8**, third function. `h x = inf {max {(f₁λ₁) x, …, (fₘλₘ) x} | λᵢ ≥ 0, ∑ λᵢ = 1}`
is convex, the book's "adding in `λ` alone", which "amounts to inverse addition of epigraphs".
Stated without the properness the book assumes: a supremum, unlike a sum, cannot produce
`∞ - ∞`. -/
theorem theorem_5_8_h {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    ConvexFn fun x => ⨅ l ∈ {l : Fin m → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1},
      ⨆ i, smulRight (f i) (l i) x := by
  have hPsi : ConvexFn fun q : (Fin m → ℝ) × Rn n => ⨆ i, hom (f i) (q.1 i, q.2) :=
    convexFn_iSup fun i => convexFn_hom_coord hf i
  have hslice := (convexFn_mapLin (homSumLin n m) hPsi).slice_left 1
  have hkey : (fun x : Rn n =>
        mapLin (homSumLin n m) (fun q : (Fin m → ℝ) × Rn n => ⨆ i, hom (f i) (q.1 i, q.2)) (1, x))
      = fun x => ⨅ l ∈ {l : Fin m → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1},
        ⨆ i, smulRight (f i) (l i) x := by
    funext x
    refine le_antisymm (le_iInf₂ fun l hl => ?_) (le_mapLin fun q hq => ?_)
    · refine (mapLin_le (x := (l, x)) ?_).trans_eq ?_
      · rw [homSumLin_apply, hl.2]
      · exact iSup_congr fun i => hom_apply_nonneg (hl.1 i) (f i) x
    · obtain ⟨l, y⟩ := q
      rw [homSumLin_apply, Prod.mk.injEq] at hq
      obtain ⟨hq₁, rfl⟩ := hq
      by_cases hpos : ∀ i, 0 ≤ l i
      · refine le_trans (iInf₂_le l ⟨hpos, hq₁⟩) (le_of_eq ?_)
        exact iSup_congr fun i => (hom_apply_nonneg (hpos i) (f i) y).symm
      · obtain ⟨j, hj⟩ := not_forall.1 hpos
        have htop : (⨆ i, hom (f i) (l i, y)) = ⊤ :=
          top_le_iff.1 (le_iSup_of_le j (hom_apply_neg (not_le.1 hj) (f j) y).ge)
        rw [htop]
        exact le_top
  rwa [hkey] at hslice

/-- The linear map `(λ, y) ↦ (λ₁ + ⋯ + λₘ, y₁ + ⋯ + yₘ)` on `ℝᵐ × (ℝⁿ)ᵐ`, along which the last
operation of Theorem 5.8 — "adding in `λ` and `x`" — is an image. -/
noncomputable def sumPairLin (n m : ℕ) : ((Fin m → ℝ) × (Fin m → Rn n)) →ₗ[ℝ] ℝ × Rn n :=
  LinearMap.prod ((∑ i, LinearMap.proj i).comp (LinearMap.fst ℝ (Fin m → ℝ) (Fin m → Rn n)))
    ((∑ i, LinearMap.proj i).comp (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → Rn n)))

@[simp] theorem sumPairLin_apply {n m : ℕ} (q : (Fin m → ℝ) × (Fin m → Rn n)) :
    sumPairLin n m q = (∑ i, q.1 i, ∑ i, q.2 i) := by
  simp [sumPairLin]

/-- The linear map `(λ, y) ↦ (λᵢ, yᵢ)`. -/
noncomputable def coordPairLin (n m : ℕ) (i : Fin m) :
    ((Fin m → ℝ) × (Fin m → Rn n)) →ₗ[ℝ] ℝ × Rn n :=
  LinearMap.prod ((LinearMap.proj i).comp (LinearMap.fst ℝ (Fin m → ℝ) (Fin m → Rn n)))
    ((LinearMap.proj i).comp (LinearMap.snd ℝ (Fin m → ℝ) (Fin m → Rn n)))

@[simp] theorem coordPairLin_apply {n m : ℕ} (i : Fin m) (q : (Fin m → ℝ) × (Fin m → Rn n)) :
    coordPairLin n m i q = (q.1 i, q.2 i) := rfl

/-- **Theorem 5.8**, fourth function. For proper convex `f₁, …, fₘ`,
`k x = inf {max {λ₁f₁x₁, …, λₘfₘxₘ}}` over all convex representations `x = λ₁x₁ + ⋯ + λₘxₘ` is
convex, the book's "adding in `λ` and `x`". -/
theorem theorem_5_8_k {n m : ℕ} {f : Fin m → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, Proper (f i)) :
    ConvexFn fun x => ⨅ lp ∈ {lp : (Fin m → ℝ) × (Fin m → Rn n) |
        (∀ i, 0 ≤ lp.1 i) ∧ ∑ i, lp.1 i = 1 ∧ ∑ i, lp.1 i • lp.2 i = x},
      ⨆ i, (lp.1 i : EReal) * f i (lp.2 i) := by
  have hPsi : ConvexFn fun q : (Fin m → ℝ) × (Fin m → Rn n) => ⨆ i, hom (f i) (q.1 i, q.2 i) :=
    convexFn_iSup fun i => by
      have h := convexFn_compLin (coordPairLin n m i) (convexFn_hom (hf i))
      exact h
  have hslice := (convexFn_mapLin (sumPairLin n m) hPsi).slice_left 1
  have hkey : (fun x : Rn n => mapLin (sumPairLin n m)
        (fun q : (Fin m → ℝ) × (Fin m → Rn n) => ⨆ i, hom (f i) (q.1 i, q.2 i)) (1, x))
      = fun x => ⨅ lp ∈ {lp : (Fin m → ℝ) × (Fin m → Rn n) |
          (∀ i, 0 ≤ lp.1 i) ∧ ∑ i, lp.1 i = 1 ∧ ∑ i, lp.1 i • lp.2 i = x},
        ⨆ i, (lp.1 i : EReal) * f i (lp.2 i) := by
    funext x
    refine le_antisymm (le_iInf₂ fun lp hlp => ?_) (le_mapLin fun q hq => ?_)
    · refine (mapLin_le (x := (lp.1, fun i => lp.1 i • lp.2 i)) ?_).trans_eq ?_
      · rw [sumPairLin_apply, hlp.2.1, hlp.2.2]
      · exact iSup_congr fun i => hom_apply_smul (hp i).dom_nonempty (hlp.1 i) (lp.2 i)
    · obtain ⟨l, y⟩ := q
      rw [sumPairLin_apply, Prod.mk.injEq] at hq
      obtain ⟨hq₁, hq₂⟩ := hq
      by_cases hpos : ∀ i, 0 ≤ l i
      · by_cases hzero : ∀ i, l i = 0 → y i = 0
        · have hsmul : ∀ i, l i • (l i)⁻¹ • y i = y i := by
            intro i
            rcases eq_or_lt_of_le (hpos i) with h | h
            · rw [← h, zero_smul, hzero i h.symm]
            · rw [smul_smul, mul_inv_cancel₀ h.ne', one_smul]
          refine le_trans (iInf₂_le (l, fun i => (l i)⁻¹ • y i) ⟨hpos, hq₁, ?_⟩) (le_of_eq ?_)
          · refine iSup_congr fun i => ?_
            calc (l i : EReal) * f i ((l i)⁻¹ • y i)
                = hom (f i) (l i, l i • (l i)⁻¹ • y i) :=
                  (hom_apply_smul (hp i).dom_nonempty (hpos i) ((l i)⁻¹ • y i)).symm
              _ = hom (f i) (l i, y i) := by rw [hsmul i]
          · change (∑ i, l i • (l i)⁻¹ • y i) = x
            simp_rw [hsmul]
            exact hq₂
        · obtain ⟨j, hj⟩ := not_forall.1 hzero
          have hj0 : l j = 0 := by
            by_contra hc
            exact hj fun h0 => absurd h0 hc
          have hjy : y j ≠ 0 := fun h0 => hj fun _ => h0
          have hjtop : hom (f j) (l j, y j) = ⊤ := by
            rw [hj0, hom_apply_zero, smulRight_zero (hp j).dom_nonempty,
              indicatorFn_of_notMem (by simpa using hjy)]
          have htop : (⨆ i, hom (f i) (l i, y i)) = ⊤ :=
            top_le_iff.1 (le_iSup_of_le j hjtop.ge)
          rw [htop]
          exact le_top
      · obtain ⟨j, hj⟩ := not_forall.1 hpos
        have htop : (⨆ i, hom (f i) (l i, y i)) = ⊤ :=
          top_le_iff.1 (le_iSup_of_le j (hom_apply_neg (not_le.1 hj) (f j) (y j)).ge)
        rw [htop]
        exact le_top
  rwa [hkey] at hslice

end Rockafellar
