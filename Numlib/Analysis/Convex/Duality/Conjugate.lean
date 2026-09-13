import Numlib.Analysis.Convex.Duality.Pairing
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Order.GaloisConnection

/-!
# Conjugates of convex functions

The **conjugate** of `f : E → EReal` with respect to a pairing `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ` is
`f*(y) = sup_x (⟨x, y⟩ - f x)`. Read through epigraphs, `f*` is a description of the affine
minorants of `f`: `f*(y) ≤ c` says exactly that `x ↦ ⟨x, y⟩ - c` lies below `f`. It is defined for
an arbitrary `f`, and is always a closed convex function. The theorem the rest of the library rests
on is **Fenchel–Moreau**, `f** = cl f` for convex `f`: conjugacy is an involution on the closed
convex functions, and a closed convex function is the pointwise supremum of the affine functions
below it.

## Main definitions

* `conj B f`, `biconj B f` — the conjugate `f*` and biconjugate `f**`.
* `conjClosure B` — conjugacy as a `ClosureOperator` on `(E → EReal)ᵒᵈ`, whose closed elements are
  exactly the closed convex functions.
* `conjEquiv` — conjugacy as an involution on the closed proper convex functions.

## Main results

* `sub_le_conj`, `conj_le_coe_iff`, `conj_le_iff` — the unconditional forms of Fenchel's
  inequality. The last says that `conj B` and `conj B.flip` are an antitone Galois connection.
* `le_add_conj` — **Fenchel's inequality** `⟨x, y⟩ ≤ f x + f* y`. In `EReal` this needs
  `Proper f`, and the hypothesis is not removable; see the implementation notes.
* `convexFn_conj`, `closedFn_conj` — the conjugate of an arbitrary function is closed and convex.
* `conj_clFn` — `(cl f)* = f*`: closure does not change the conjugate.
* `exists_affineFn_le_of_lt`, `eq_biSup_affineFn` — a closed convex function is the pointwise
  supremum of the affine functions below it.
* `biconj_eq_clFn` — the **Fenchel–Moreau theorem**: `f** = cl f` for convex `f`;
  `proper_conj_iff` is its properness half. `biconj_eq_clFn_topDual` and `biconj_eq_clFn_inner`
  discharge every hypothesis, for a locally convex space paired with its own continuous dual and
  for a real Hilbert space paired with itself, both in the space's *own* topology.
* `gc_conj_conj`, `conjClosure`, `conjOrderIso` — the Galois connection, the closure operator it
  induces, and the order anti-isomorphism between the biconjugation-fixed functions.
* `conj_comp_sub`, `conj_comp_add`, `conj_add_pairing`, `conj_sub_pairing`, `conj_add_const`,
  `conj_comp_linearEquiv` — the four elementary rows (translation, tilting, an added constant, an
  invertible substitution), with `conj_comp_affine` composing them
  ([rockafellar1970convex] Theorem 12.3).

## Implementation notes

Fenchel–Moreau does not care which topology `E` carries, so long as its continuous dual is the `F`
side of the pairing: that is `IsCompatiblePairing B`. Its weaker companion `IsContinuousPairing`,
asking only that every `⟨·, y⟩` be continuous, is all the closedness half of this file needs —
`closedFn_conj`, `conj_clFn`, `biconj_le_clFn` — which matters because a Banach space paired with
its norm-topology dual is continuous on both sides but compatible only if it is reflexive.

## References

* [rockafellar1970convex] §12.
-/

open Set OrderDual

namespace ConvexAnalysis

/-! ### The conjugate -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **convex conjugate** of `f` with respect to the pairing `B`:
`f*(y) = sup_x (⟨x, y⟩ - f x)`. `epi f*` is the set of pairs `(y, c)` for which the affine function
`x ↦ ⟨x, y⟩ - c` is majorized by `f`. No hypothesis is placed on `f`. -/
noncomputable def conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨆ x : E, ((B x y : ℝ) : EReal) - f x

/-- The **biconjugate**, back on `E`. Using `B.flip` rather than a second copy of `B` makes the
correspondence symmetric with no reflexivity assumption; `B.flip.flip = B` holds by `rfl`. -/
noncomputable abbrev biconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : E → EReal :=
  conj B.flip (conj B f)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F} {c : ℝ}

theorem conj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    conj B f y = ⨆ x : E, ((B x y : ℝ) : EReal) - f x := rfl

theorem biconj_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    biconj B f x = ⨆ y : F, ((B x y : ℝ) : EReal) - conj B f y := rfl

/-- **Fenchel's inequality, `∞ - ∞`-free**: it holds for every `f`, `x` and `y`, and it is the
form the proofs below use rather than the additive `le_add_conj`. -/
theorem sub_le_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) - f x ≤ conj B f y :=
  le_iSup (fun x : E => ((B x y : ℝ) : EReal) - f x) x

/-- `f*(y) ≤ c` says exactly that the affine function `x ↦ ⟨x, y⟩ - c` lies below `f`. -/
theorem conj_le_coe_iff : conj B f y ≤ (c : EReal) ↔ affineFn B y c ≤ f := by
  rw [conj_apply, iSup_le_iff, affineFn_le_iff]

theorem conj_antitone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Antitone (conj B) := fun _ _ h _ =>
  iSup_mono fun x => EReal.sub_le_sub le_rfl (h x)

/-- **The adjunction.** `f* ≤ g` and `g* ≤ f` say the same thing — that `⟨x, y⟩ ≤ f x + g y` for
all `x` and `y`, in the `∞ - ∞`-free reading. -/
theorem conj_le_iff {g : F → EReal} : conj B f ≤ g ↔ conj B.flip g ≤ f := by
  simp only [Pi.le_def, conj_apply, iSup_le_iff, LinearMap.flip_apply]
  rw [forall_comm]
  exact forall₂_congr fun _ _ => EReal.coe_sub_le_comm

theorem biconj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : biconj B f ≤ f :=
  conj_le_iff.1 le_rfl

/-! ### The improper cases -/

/-- `f*` takes the value `⊥` at a point exactly when `f ≡ ⊤` — a condition independent of the
point. So `f*` is either the constant `⊥` or never `⊥`, which is why it is always *closed*. -/
theorem conj_eq_bot_iff : conj B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  rw [conj_apply, iSup_eq_bot]
  exact forall_congr' fun _ => EReal.coe_sub_eq_bot_iff

/-- **If `f` takes the value `⊥` anywhere, its conjugate is identically `⊤`.** -/
theorem conj_of_eq_bot {x₀ : E} (h : f x₀ = ⊥) : conj B f = fun _ => ⊤ := by
  funext y
  refine top_le_iff.1 (le_trans ?_ (sub_le_conj B f x₀ y))
  rw [h, EReal.coe_sub_bot]

theorem conj_top (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : conj B (fun _ => ⊤) = fun _ => (⊥ : EReal) :=
  funext fun _ => conj_eq_bot_iff.2 fun _ => rfl

theorem conj_bot (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : conj B (fun _ => ⊥) = fun _ => (⊤ : EReal) :=
  conj_of_eq_bot (x₀ := (0 : E)) rfl

theorem conj_ne_bot (h : (dom f).Nonempty) (y : F) : conj B f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := h
  exact fun hc => absurd (conj_eq_bot_iff.1 hc x) hx.ne

/-- **Fenchel's inequality**: `⟨x, y⟩ ≤ f x + f*(y)` for a proper `f`.

Properness is not decorative: if `f ≡ +∞` then `f* ≡ -∞` and the right-hand side is `⊤ + ⊥ = ⊥`,
and if `f` takes `-∞` then it is `⊥ + ⊤ = ⊥`. Use `sub_le_conj` when properness is unavailable. -/
theorem le_add_conj (hb : f x ≠ ⊥) (hd : (dom f).Nonempty) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + conj B f y := by
  rw [add_comm]
  exact (EReal.sub_le_iff_le_add (.inl hb) (.inr (conj_ne_bot hd y))).1 (sub_le_conj B f x y)

theorem Proper.le_add_conj (hp : Proper f) (x : E) (y : F) :
    ((B x y : ℝ) : EReal) ≤ f x + conj B f y :=
  _root_.ConvexAnalysis.le_add_conj (hp.ne_bot x) hp.dom_nonempty y

/-- If the conjugate is proper then so is the original function; no hypothesis is needed for this
direction. The converse is `proper_conj`, and needs closedness. -/
theorem proper_of_proper_conj (h : Proper (conj B f)) : Proper f := by
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := h.dom_nonempty
    by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact absurd (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x))) (h.ne_bot y)
  · obtain ⟨y, hy⟩ := h.dom_nonempty
    rw [conj_of_eq_bot hx] at hy
    exact absurd hy (by simp)

/-! ### Convexity of the conjugate -/

/-- The `x`-th term of the supremum defining `f*` is, as a function of `y`, either constant or one
of the affine functions of the flipped pairing, according to the value of `f x`. -/
theorem conj_term_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊥ : EReal)) ∨
      (fun y => ((B x y : ℝ) : EReal) - f x) = (fun _ => (⊤ : EReal)) ∨
      ∃ t : ℝ, (fun y => ((B x y : ℝ) : EReal) - f x) = affineFn B.flip x t := by
  rcases eq_or_ne (f x) ⊤ with h | h
  · exact Or.inl (funext fun y => by rw [h, EReal.sub_top])
  rcases eq_or_ne (f x) ⊥ with h' | h'
  · exact Or.inr (Or.inl (funext fun y => by rw [h', EReal.coe_sub_bot]))
  · obtain ⟨t, ht⟩ := EReal.exists_coe_of_ne_bot_of_lt_top h' (lt_top_iff_ne_top.2 h)
    exact Or.inr (Or.inr ⟨t, funext fun y => by rw [ht, affineFn_apply, LinearMap.flip_apply]⟩)

/-- **The conjugate of an arbitrary function is convex**: a pointwise supremum of affine functions
and constants. -/
theorem convexFn_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : ConvexFn (conj B f) := by
  refine convexFn_iSup fun x => ?_
  rcases conj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact convexFn_const ⊥
  · exact convexFn_const ⊤
  · exact convexFn_affineFn x t

end Defs

/-! ### Why Fenchel's inequality needs properness

In `EReal` the value `⊥` is absorbing for addition, so `⊤ + ⊥ = ⊥ + ⊤ = ⊥` and the additive form of
Fenchel's inequality collapses at each of the two improper functions. -/

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊤ : EReal)) 0 + conj (innerₗ ℝ) (fun _ : ℝ => (⊤ : EReal)) 0 := by
  rw [conj_top]
  simp

example : ¬ (((innerₗ ℝ) (0 : ℝ) (0 : ℝ) : ℝ) : EReal)
    ≤ (fun _ : ℝ => (⊥ : EReal)) 0 + conj (innerₗ ℝ) (fun _ : ℝ => (⊥ : EReal)) 0 := by
  rw [conj_bot]
  simp

/-! ### Closedness of the conjugate

The conjugate is closed in *any* topology on `F` for which the pairing is continuous — in
particular in `σ(F, E)`, hence also in the norm topology of a normed space paired with its dual. -/

section ConjClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

theorem lowerSemicontinuous_conj : LowerSemicontinuous (conj B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  rcases conj_term_eq B f x with h | h | ⟨t, h⟩ <;> rw [h]
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_const
  · exact lowerSemicontinuous_affineFn (continuous_pairing B.flip x)

variable [IsTopologicalAddGroup F]

/-- **The conjugate is a closed convex function**, with no hypothesis on `f`: if `f ≡ +∞` it is
the constant `⊥`, and otherwise it is lower semicontinuous and never takes `⊥`. -/
theorem closedFn_conj : ClosedFn (conj B f) := by
  rw [closedFn_iff]
  by_cases h : ∀ x, f x = ⊤
  · exact Or.inl (funext fun _ => conj_eq_bot_iff.2 h)
  · exact Or.inr ⟨lowerSemicontinuous_conj, fun _ hy => h (conj_eq_bot_iff.1 hy)⟩

end ConjClosed

/-! ### The conjugate sees only the closure -/

section ConjClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsContinuousPairing B] {f : E → EReal}

/-- **Closure does not change the conjugate**: `(cl f)* = f*`. The affine functions below `f` and
below `cl f` are the same, because an affine function of a continuous pairing is itself closed. -/
theorem conj_clFn (f : E → EReal) : conj B (clFn f) = conj B f := by
  funext y
  refine EReal.eq_of_forall_le_coe_iff fun c => ?_
  rw [conj_le_coe_iff, conj_le_coe_iff]
  exact ⟨fun h => h.trans (clFn_le f),
    fun h => le_clFn_of_le (closedFn_affineFn (continuous_pairing B y)) h⟩

/-- The biconjugate is a closed convex minorant of `f`, hence a minorant of `cl f`: the easy half
of Fenchel–Moreau, needing no convexity. -/
theorem biconj_le_clFn (f : E → EReal) : biconj B f ≤ clFn f :=
  le_clFn_of_le (closedFn_conj (B := B.flip)) (biconj_le B f)

end ConjClosure

/-! ### Affine minorants of a closed convex function -/

section AffineMinorants

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The affine-minorant lemma**, in its working form: below any value strictly under a closed
convex function there is an affine minorant of the pairing. -/
theorem exists_affineFn_le_of_lt (hf : ConvexFn f) (hc : ClosedFn f) {x₀ : E} {α : ℝ}
    (h : (α : EReal) < f x₀) :
    ∃ (y : F) (c : ℝ), affineFn B y c ≤ f ∧ (α : EReal) < affineFn B y c x₀ := by
  by_cases hp : Proper f
  case neg =>
    -- A closed improper function is constant; `f ≡ -∞` contradicts `α < f x₀`, and every affine
    -- function lies below `f ≡ +∞`.
    rcases eq_const_of_closedFn_of_not_proper hc hp with hbot | htop
    · rw [hbot] at h; exact absurd h (by simp)
    · refine ⟨0, -(α + 1), htop ▸ fun _ => le_top, ?_⟩
      rw [affineFn_eq_coe, map_zero, EReal.coe_lt_coe_iff]
      linarith
  case pos =>
  -- A point of the epigraph over any point of the effective domain.
  have hmem : ∀ x, f x < ⊤ → ∃ μ : ℝ, (x, μ) ∈ epi f := by
    intro x hx
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hx
    exact ⟨r, by rw [mk_mem_epi, hr]⟩
  have hnot : ((x₀, α) : E × ℝ) ∉ epi f := fun hcon => absurd (mk_mem_epi.1 hcon) (not_le.2 h)
  have hclosed : IsClosed (epi f) :=
    lowerSemicontinuous_iff_isClosed_epi.1 hc.lowerSemicontinuous
  obtain ⟨L, u, hLs, hLx⟩ := geometric_hahn_banach_closed_point hf.convex_epi hclosed hnot
  set g : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hg
  set c₀ : ℝ := L (0, 1) with hc₀def
  have hL : ∀ (x : E) (μ : ℝ), L (x, μ) = g x + c₀ * μ := dual_prod_apply L
  -- The separating functional cannot be a *lower* half-space: `epi f` is unbounded above.
  obtain ⟨x₁, hx₁⟩ := hp.dom_nonempty
  obtain ⟨μ₁, hμ₁⟩ := hmem x₁ hx₁
  have hc₀ : c₀ ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set t : ℝ := max 0 ((u - g x₁ - c₀ * μ₁) / c₀) with ht
    have ht0 : 0 ≤ t := le_max_left _ _
    have htle : (u - g x₁ - c₀ * μ₁) / c₀ ≤ t := le_max_right _ _
    have hin : ((x₁, μ₁ + t) : E × ℝ) ∈ epi f :=
      mk_mem_epi.2 ((mk_mem_epi.1 hμ₁).trans
        (by exact_mod_cast (by linarith : μ₁ ≤ μ₁ + t)))
    have hbnd := hLs _ hin
    rw [hL] at hbnd
    have := (div_le_iff₀ hpos).1 htle
    nlinarith
  obtain ⟨y₁, hy₁⟩ := exists_pairing_eq B g
  rcases lt_or_eq_of_le hc₀ with hneg | hzero
  · -- Upper half-space: rescale by `-c₀ > 0`.
    have hd : 0 < -c₀ := by linarith
    have hy : ∀ x, B x ((-c₀)⁻¹ • y₁) = (-c₀)⁻¹ * g x := fun x => by
      rw [map_smul, smul_eq_mul, hy₁ x]
    refine ⟨(-c₀)⁻¹ • y₁, u / (-c₀), fun x => ?_, ?_⟩
    · rw [affineFn_eq_coe, hy]
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨μ, hfμ, hμ⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have hin : ((x, μ) : E × ℝ) ∈ epi f := mk_mem_epi.2 hfμ.le
      have hbnd := hLs _ hin
      rw [hL] at hbnd
      have hμ' : μ < (-c₀)⁻¹ * g x - u / (-c₀) := by exact_mod_cast hμ
      rw [inv_mul_eq_div, div_sub_div_same, lt_div_iff₀ hd] at hμ'
      nlinarith
    · rw [affineFn_eq_coe, hy, EReal.coe_lt_coe_iff, inv_mul_eq_div, div_sub_div_same,
        lt_div_iff₀ hd]
      rw [hL] at hLx
      nlinarith
  · -- Vertical half-space: absorb it into a known affine minorant.
    obtain ⟨w, c₂, hw⟩ := exists_affine_le_of_closed_proper ⟨hf, hc, hp⟩
    obtain ⟨y₂, hy₂⟩ := exists_pairing_eq B w
    have hdom : ∀ x, f x < ⊤ → g x < u := by
      intro x hx
      obtain ⟨μ, hμ⟩ := hmem x hx
      have hbnd := hLs _ hμ
      rw [hL, hzero] at hbnd
      simpa using hbnd
    have hgx₀ : u < g x₀ := by rw [hL, hzero] at hLx; simpa using hLx
    set d : ℝ := g x₀ - u with hdd
    have hdpos : 0 < d := by rw [hdd]; linarith
    set m : ℝ := B x₀ y₂ - c₂ with hm
    set lam : ℝ := max 0 ((α + 1 - m) / d) with hlam
    have hlam0 : 0 ≤ lam := le_max_left _ _
    have hlamle : (α + 1 - m) / d ≤ lam := le_max_right _ _
    refine ⟨lam • y₁ + y₂, lam * u + c₂, fun x => ?_, ?_⟩
    · rw [affineFn_smul_add]
      rcases lt_or_ge (f x) ⊤ with hx | hx
      · have h1 : lam * (B x y₁ - u) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hlam0 (by rw [← hy₁ x]; linarith [hdom x hx])
        refine le_trans ?_ (hy₂ x ▸ hw x)
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        linarith
      · rw [top_le_iff.1 hx]; exact le_top
    · rw [affineFn_smul_add, EReal.coe_lt_coe_iff, ← hy₁ x₀, ← hm]
      have := (div_le_iff₀ hdpos).1 hlamle
      nlinarith

/-- A closed convex function is the pointwise supremum of all the affine functions of the pairing
that lie below it. -/
theorem eq_biSup_affineFn (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : F × ℝ | affineFn B p.1 p.2 ≤ f}, affineFn B p.1 p.2 x := by
  funext x
  refine le_antisymm ?_ (iSup₂_le fun p hp => hp x)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ := exists_affineFn_le_of_lt (B := B) hf hc hα₂
  exact absurd (lt_of_lt_of_le hlt (le_iSup₂ (f := fun p (_ : p ∈ _) => affineFn B p.1 p.2 x)
    ((y, c) : F × ℝ) hle)) (not_lt.2 hα₁.le)

end AffineMinorants

/-! ### The Fenchel–Moreau theorem -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The Fenchel–Moreau theorem.** For a convex function, `f** = cl f`.

The improper cases are why `clFn` branches on `lscHull f` rather than on `f`: if `f` takes `-∞`
anywhere then `f* ≡ +∞` and `f** ≡ -∞`, which is `cl f` only under that branching. -/
theorem biconj_eq_clFn (hf : ConvexFn f) : biconj B f = clFn f := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    have hbot : lscHull f x₀ = ⊥ := le_bot_iff.1 (hx₀ ▸ lscHull_le f x₀)
    rw [clFn_of_exists_eq_bot ⟨x₀, hbot⟩]
    change conj B.flip (conj B f) = _
    rw [conj_of_eq_bot hx₀, conj_top]
  push Not at hb
  by_cases ht : ∀ x, f x = ⊤
  · have hfeq : f = fun _ => (⊤ : EReal) := funext ht
    rw [hfeq]
    change conj B.flip (conj B (fun _ => (⊤ : EReal))) = _
    rw [conj_top, conj_bot]
    exact closedFn_const_top.symm
  refine le_antisymm (biconj_le_clFn f) fun x₀ => ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨α, hα₁, hα₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  obtain ⟨y, c, hle, hlt⟩ :=
    exists_affineFn_le_of_lt (B := B) (convexFn_clFn hf) (closedFn_clFn f) hα₂
  have hcy : conj B f y ≤ (c : EReal) := conj_le_coe_iff.2 (hle.trans (clFn_le f))
  refine absurd (lt_of_lt_of_le hlt ?_) (not_lt.2 hα₁.le)
  refine le_trans ?_ (sub_le_conj B.flip (conj B f) y x₀)
  rw [affineFn_apply, LinearMap.flip_apply]
  exact EReal.sub_le_sub le_rfl hcy

/-- **The properness half**: the conjugate of a closed proper convex function is proper.
With `proper_of_proper_conj`, "`f*` is proper if and only if `f` is". -/
theorem proper_conj (hf : ClosedProperConvexFn f) : Proper (conj B f) := by
  obtain ⟨w, c, hw⟩ := exists_affine_le_of_closed_proper hf
  obtain ⟨y, hy⟩ := exists_pairing_eq B w
  refine ⟨⟨y, lt_of_le_of_lt (conj_le_coe_iff.2 fun x => ?_) (EReal.coe_lt_top c)⟩,
    conj_ne_bot hf.proper.dom_nonempty⟩
  rw [affineFn_apply, ← hy x]
  exact hw x

theorem proper_conj_iff (hf : ConvexFn f) (hc : ClosedFn f) :
    Proper (conj B f) ↔ Proper f :=
  ⟨proper_of_proper_conj, fun hp => proper_conj ⟨hf, hc, hp⟩⟩

theorem biconj_eq_self (hf : ConvexFn f) (hc : ClosedFn f) : biconj B f = f :=
  (biconj_eq_clFn hf).trans hc

end FenchelMoreau

/-! ### Conjugacy as a Galois connection

`conj_le_iff` says that `conj B` and `conj B.flip` are antitonely adjoint; Fenchel–Moreau then
identifies the closed elements of the induced closure operator with the closed convex functions.
The `OrderDual` on the domain is what makes an antitone adjunction fit Mathlib's monotone
`GaloisConnection`. -/

section Galois

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem gc_conj_conj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    GaloisConnection (fun f : (E → EReal)ᵒᵈ => conj B (ofDual f))
      (fun g : F → EReal => toDual (conj B.flip g)) := fun _ _ => conj_le_iff

/-- The closure operator `f ↦ f**` induced by the adjunction. Its closed elements are the functions
equal to their own biconjugate, which by Fenchel–Moreau are exactly the closed convex functions. -/
noncomputable def conjClosure (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : ClosureOperator (E → EReal)ᵒᵈ :=
  (gc_conj_conj B).closureOperator

@[simp] theorem conjClosure_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    conjClosure B (toDual f) = toDual (biconj B f) := rfl

theorem isClosed_conjClosure_iff {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} :
    (conjClosure B).IsClosed (toDual f) ↔ biconj B f = f :=
  ⟨fun h => congrArg ofDual h, fun h => congrArg toDual h⟩

/-- Conjugating three times is the same as conjugating once: the triangle identity, which here says
that `f*` is unchanged by closure. -/
theorem conj_biconj (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : conj B (biconj B f) = conj B f :=
  le_antisymm (conj_le_iff.2 (le_refl (biconj B f))) (conj_antitone B (biconj_le B f))

/-- **Conjugacy is an order anti-isomorphism between the biconjugation-fixed functions.**

Neither this nor `conjEquiv` below subsumes the other: this one needs no topology and carries the
order, while `conjEquiv` is about the *proper* closed convex functions, a strictly smaller class
that `f** = f` does not pin down — the improper `f ≡ +∞` and `f ≡ -∞` are fixed by biconjugation
too. -/
noncomputable def conjOrderIso (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    {f : (E → EReal)ᵒᵈ // toDual (conj B.flip (conj B (ofDual f))) = f} ≃o
      {g : F → EReal // conj B (ofDual (toDual (conj B.flip g))) = g} :=
  (gc_conj_conj B).closedsOrderIso

end Galois

/-! ### The involution on closed proper convex functions

Both spaces carry topologies compatible with the pairing, and everything is symmetric under
`B ↦ B.flip`. -/

section Involution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] [IsCompatiblePairing B.flip]

/-- Conjugacy is a symmetric one-to-one correspondence between the closed proper convex functions
on `E` and those on `F`. -/
noncomputable def conjEquiv :
    {f : E → EReal // ClosedProperConvexFn f} ≃ {g : F → EReal // ClosedProperConvexFn g} where
  toFun f := ⟨conj B f.1, convexFn_conj B f.1, closedFn_conj, proper_conj f.2⟩
  invFun g := ⟨conj B.flip g.1, convexFn_conj B.flip g.1, closedFn_conj, proper_conj g.2⟩
  left_inv f := Subtype.ext (biconj_eq_self f.2.convex f.2.closed)
  right_inv g := Subtype.ext (biconj_eq_self (B := B.flip) g.2.convex g.2.closed)

@[simp] theorem conjEquiv_apply (f : {f : E → EReal // ClosedProperConvexFn f}) :
    (conjEquiv B f : F → EReal) = conj B f := rfl

end Involution

/-! ### Translation, tilting, constants and an invertible substitution

The elementary conjugacy operations, those under which `h*` changes by a change of variable rather
than by a change of function. There are four independent rows —

| primal | dual |
|---|---|
| `h (x - a)` | `h* y + ⟨a, y⟩` |
| `h x + ⟨x, b⟩` | `h* (y - b)` |
| `h x + α` | `h* y - α` |
| `h (A x)`, `A` invertible | `h* (A'⁻¹ y)` |

— and `conj_comp_affine` composes all four into a single formula. The two *scaling* rows of the
same table are `conj_smul` and `conj_smulRight` in `Duality/Ops.lean`. Each
identity holds for an arbitrary `h : E → EReal`, improper ones included, with no topology,
properness or convexity: `⟨a, y⟩`, `⟨x, b⟩` and `α` are *real*, so sliding them across the
difference `⟨x, y⟩ - h x` never produces `∞ - ∞`.

Rockafellar writes the substitution row with `A*⁻¹`, presuming that `A` has an adjoint and that the
adjoint is invertible. Over a general pairing neither is automatic, so `conj_comp_linearEquiv`
takes the inverse pair `A`, `A'` and the adjointness datum `IsAdjointPair B B' A A'` as
hypotheses; with `B` and `B'` separating, `A'` is determined by `A`, so nothing is lost. -/

section AffineOps

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}

/-- **The translation row**: translating the argument of `h` by `a` adds the linear function
`⟨a, ·⟩` to the conjugate. -/
theorem conj_comp_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    conj B (fun x => h (x - a)) y = conj B h y + ((B a y : ℝ) : EReal) := by
  have hre := (Equiv.addRight a).iSup_comp
    (g := fun x : E => ((B x y : ℝ) : EReal) - h (x - a))
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at hre
  simp only [conj_apply]
  rw [← hre, EReal.iSup_add_coe]
  exact iSup_congr fun u => by
    rw [map_add, LinearMap.add_apply, EReal.coe_add_sub]

/-- **The translation row** with the translation on the left: `h (a + ·)` is
`h (· - (-a))`, so its conjugate is `h* - ⟨a, ·⟩`. -/
theorem conj_comp_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (a : E) (y : F) :
    conj B (fun x => h (a + x)) y = conj B h y - ((B a y : ℝ) : EReal) := by
  have hfun : (fun x : E => h (a + x)) = fun x : E => h (x - -a) := by
    funext x; rw [sub_neg_eq_add, add_comm]
  rw [hfun, conj_comp_sub, map_neg, LinearMap.neg_apply, EReal.coe_neg,
    ← sub_eq_add_neg]

/-- **The tilting row**: adding the linear function `⟨·, b⟩` to `h` translates the
conjugate by `b`. -/
theorem conj_add_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    conj B (fun x => h x + ((B x b : ℝ) : EReal)) y = conj B h (y - b) := by
  simp only [conj_apply]
  exact iSup_congr fun x => by rw [EReal.coe_sub_add_coe, map_sub]

/-- **The tilting row** with the linear term *subtracted*: `h - ⟨·, b⟩` has conjugate
`h* (· + b)`. -/
theorem conj_sub_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (b : F) (y : F) :
    conj B (fun x => h x - ((B x b : ℝ) : EReal)) y = conj B h (y + b) := by
  have hfun : (fun x : E => h x - ((B x b : ℝ) : EReal))
      = fun x : E => h x + ((B x (-b) : ℝ) : EReal) := by
    funext x
    rw [map_neg, EReal.coe_neg, ← sub_eq_add_neg]
  rw [hfun, conj_add_pairing, sub_neg_eq_add]

/-- **The constant row**: adding a constant to `h` subtracts it from the conjugate. -/
theorem conj_add_const (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (α : ℝ) (y : F) :
    conj B (fun x => h x + (α : EReal)) y = conj B h y - (α : EReal) := by
  simp only [conj_apply]
  rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.iSup_add_coe]
  exact iSup_congr fun x => by
    rw [EReal.coe_sub_add_coe, ← EReal.coe_add_sub, ← sub_eq_add_neg]

/-- **The substitution row**: precomposing `h` with a linear *isomorphism* `A` precomposes the
conjugate with the inverse of the transpose. Contrast `conj_mapLin`, which drops invertibility at
the cost of stating the dual side as an image. -/
theorem conj_comp_linearEquiv (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (h : G → EReal) (y : F) :
    conj B (fun x => h (A x)) y = conj B' h (A'.symm y) := by
  have hre := A.toEquiv.iSup_comp
    (g := fun u : G => ((B' u (A'.symm y) : ℝ) : EReal) - h u)
  simp only [LinearEquiv.coe_toEquiv] at hre
  have hAx : ∀ (x : E) (z : H), B' (A x) z = B x (A' z) := hA
  simp only [conj_apply]
  rw [← hre]
  exact iSup_congr fun x => by
    rw [hAx x (A'.symm y), LinearEquiv.apply_symm_apply]

/-- **The four rows composed.** For `f x = h (A (x - a)) + ⟨x, a*⟩ + α` with `A` an invertible
linear transformation, `f* y = h* (A*⁻¹ (y - a*)) + ⟨a, y⟩ + α*` where `α* = -α - ⟨a, a*⟩`. -/
theorem conj_comp_affine (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (h : G → EReal) (a : E) (b : F)
    (α : ℝ) (y : F) :
    conj B (fun x => h (A (x - a)) + ((B x b : ℝ) : EReal) + (α : EReal)) y
      = conj B' h (A'.symm (y - b)) + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := by
  have e1 : conj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal) + (α : EReal)) y
      = conj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) y - (α : EReal) :=
    conj_add_const B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) α y
  have e2 : conj B (fun x : E => h (A (x - a)) + ((B x b : ℝ) : EReal)) y
      = conj B (fun x : E => h (A (x - a))) (y - b) :=
    conj_add_pairing B (fun x : E => h (A (x - a))) b y
  have e3 : conj B (fun x : E => h (A (x - a))) (y - b)
      = conj B (fun x : E => h (A x)) (y - b) + ((B a (y - b) : ℝ) : EReal) :=
    conj_comp_sub B (fun x : E => h (A x)) a (y - b)
  have e4 : conj B (fun x : E => h (A x)) (y - b) = conj B' h (A'.symm (y - b)) :=
    conj_comp_linearEquiv A A' hA h (y - b)
  have harith : ((B a y - B a b : ℝ) : EReal) + -(α : EReal)
      = ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := by
    rw [← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring
  have hassoc : ∀ U : EReal, U + ((B a (y - b) : ℝ) : EReal) - (α : EReal)
      = U + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal) := fun U => by
    rw [map_sub (B a) y b]
    change U + ((B a y - B a b : ℝ) : EReal) + -(α : EReal)
      = U + ((B a y : ℝ) : EReal) + ((-α - B a b : ℝ) : EReal)
    rw [add_assoc, add_assoc, harith]
  rw [e1, e2, e3, e4, hassoc]

/-- **Translation and tilting composed**: for `f = h (z + ·) - ⟨·, z*⟩`,
`f* = h* (z* + ·) - ⟨z, ·⟩ - ⟨z, z*⟩`. The constant `⟨z, z*⟩` is what makes the two infima it is
used for add to `⟨z, z*⟩` rather than to zero. -/
theorem conj_comp_add_sub_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (h : E → EReal) (z : E) (z' : F)
    (y : F) :
    conj B (fun x => h (z + x) - ((B x z' : ℝ) : EReal)) y
      = conj B h (z' + y) - ((B z y : ℝ) : EReal) - ((B z z' : ℝ) : EReal) := by
  have hsplit : ∀ (u : EReal) (p q : ℝ),
      u - ((p + q : ℝ) : EReal) = u - (p : EReal) - (q : EReal) := fun u p q => by
    have hneg : -(((p + q : ℝ)) : EReal) = -((p : ℝ) : EReal) + -((q : ℝ) : EReal) := by
      rw [← EReal.coe_neg, neg_add, EReal.coe_add, EReal.coe_neg,
        EReal.coe_neg]
    change u + -(((p + q : ℝ)) : EReal) = u + -((p : ℝ) : EReal) + -((q : ℝ) : EReal)
    rw [hneg, ← add_assoc]
  rw [conj_sub_pairing B (fun x => h (z + x)) z' y, conj_comp_add B h z (y + z'),
    add_comm y z', map_add, add_comm ((B z) z' : ℝ) ((B z) y), hsplit]

end AffineOps


section TopDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Fenchel–Moreau for a locally convex space paired with its own topological dual**, in the
original topology of `E` and with no hypothesis beyond convexity. -/
theorem biconj_eq_clFn_topDual {f : E → EReal} (hf : ConvexFn f) :
    biconj (topDualPairing ℝ E).flip f = clFn f :=
  biconj_eq_clFn hf

theorem eq_biSup_affineFn_topDual {f : E → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : (E →L[ℝ] ℝ) × ℝ | affineFn (topDualPairing ℝ E).flip p.1 p.2 ≤ f},
      affineFn (topDualPairing ℝ E).flip p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end TopDual

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Fenchel–Moreau for a real Hilbert space paired with itself by the inner product**, in the
norm topology. Compatibility is the Fréchet–Riesz representation theorem. -/
theorem biconj_eq_clFn_inner {f : E → EReal} (hf : ConvexFn f) :
    biconj (innerₗ E) f = clFn f :=
  biconj_eq_clFn hf

theorem eq_biSup_affineFn_inner {f : E → EReal} (hf : ConvexFn f) (hc : ClosedFn f) :
    f = fun x => ⨆ p ∈ {p : E × ℝ | affineFn (innerₗ E) p.1 p.2 ≤ f},
      affineFn (innerₗ E) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

end Hilbert

end ConvexAnalysis
