import Numlib.Analysis.Convex.Bifunction.Cofinite
import NumlibSurface.Rockafellar.Part6.Section30

/-!
# Rockafellar, §38: The Algebra of Bifunctions

Addition, scalar multiplication, application and composition of convex bifunctions, and how each
behaves under taking adjoints. All twelve numbered results of §38 are formalized: Theorems
38.1–38.5 and 38.7, Lemma 38.6, and Corollaries 38.2.1, 38.4.1, 38.5.1, 38.7.1 and 38.7.2.

## Implementation notes

Theorem 38.1's inner-product identity holds "if one sets `∞ − ∞ = −∞ + ∞ = −∞`", and its
parenthetical adds "similarly for concave bifunctions, but with `∞ − ∞ = −∞ + ∞ = +∞`". Those are
two different binary operations on `EReal`, named apart here as `convexAdd` — which is `EReal`'s
own addition — and `concaveAdd`, which is not: `theorem_38_1_bracket_concave` is false with
`convexAdd` in its place.

Rockafellar's inner product `⟨f, g⟩` of a convex and a concave function is a **partial** operation;
he states the definedness condition in prose and then writes `⟨f, g⟩` freely. Here
`HasInnerProduct` is that condition, and it is an explicit hypothesis wherever an inner product is
claimed to exist.

## Divergences from the book

Every relative-interior hypothesis of §38 is carried as an `IsExactSum`. Rockafellar's conditions
are always "`ri (dom …)` and `ri (dom …)` have a point in common", the hypothesis of Theorem 16.4;
`IsExactSum` is that theorem's conclusion. Two consequences show in the statements: exactness is
demanded once per dual vector, where the book's single condition is uniform in it, and
`IsExactSum` carries properness of both summands, which is the book's main branch.

`□` is unconditionally commutative and associative here, where the book hedges "to the extent that
it is defined" — `infConv` is total on `EReal`, so improper bifunctions are included. That is
*stronger* than the book. The caveat that is real is the one about bifunction **multiplication**,
and it is not discharged.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §38, pp. 401–412.
-/

open Set

namespace Rockafellar

open ConvexAnalysis NumlibSurface

/-! ### The two `∞ − ∞` conventions of Theorem 38.1 -/

/-- Rockafellar's **convex** `∞ − ∞` convention, `∞ − ∞ = −∞ + ∞ = −∞`, under which Theorem 38.1's
inner-product identity holds for convex bifunctions. On `EReal` this is the ambient addition; the
definition exists only to give the convention a name distinct from the concave one. -/
noncomputable def convexAdd (a b : EReal) : EReal := a + b

/-- Rockafellar's **concave** `∞ − ∞` convention, `∞ − ∞ = −∞ + ∞ = +∞`. This is **not** `EReal`'s
addition: it is addition read through negation. -/
noncomputable def concaveAdd (a b : EReal) : EReal := -(-a + -b)

theorem convexAdd_apply (a b : EReal) : convexAdd a b = a + b := rfl

theorem concaveAdd_apply (a b : EReal) : concaveAdd a b = -(-a + -b) := rfl

/-- The convex convention resolves `∞ − ∞` downwards. -/
@[simp] theorem convexAdd_top_bot : convexAdd ⊤ ⊥ = ⊥ := by
  rw [convexAdd_apply, _root_.EReal.add_bot]

/-- The concave convention resolves `∞ − ∞` upwards. -/
@[simp] theorem concaveAdd_top_bot : concaveAdd ⊤ ⊥ = ⊤ := by
  rw [concaveAdd_apply, _root_.EReal.neg_top, _root_.EReal.neg_bot, _root_.EReal.bot_add,
    _root_.EReal.neg_bot]

/-- The two conventions are genuinely different operations, which is why they are named apart
where the book's `⟨·, ·⟩` carries both. -/
theorem convexAdd_ne_concaveAdd : convexAdd ⊤ ⊥ ≠ concaveAdd ⊤ ⊥ := by
  rw [convexAdd_top_bot, concaveAdd_top_bot]
  exact bot_ne_top

/-- Away from the two collisions the conventions agree. -/
theorem concaveAdd_eq_convexAdd {a b : EReal} (h₁ : a ≠ ⊤ ∨ b ≠ ⊥) (h₂ : a ≠ ⊥ ∨ b ≠ ⊤) :
    concaveAdd a b = convexAdd a b := by
  have hn₁ : -a ≠ ⊥ ∨ -b ≠ ⊤ := by
    rcases h₁ with h | h
    · exact Or.inl (by rw [Ne, _root_.EReal.neg_eq_bot_iff]; exact h)
    · exact Or.inr (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact h)
  have hn₂ : -a ≠ ⊤ ∨ -b ≠ ⊥ := by
    rcases h₂ with h | h
    · exact Or.inl (by rw [Ne, _root_.EReal.neg_eq_top_iff]; exact h)
    · exact Or.inr (by rw [Ne, _root_.EReal.neg_eq_bot_iff]; exact h)
  have hna : -(-a + -b) = - -a + - -b := _root_.EReal.neg_add hn₁ hn₂
  have hb₁ : (- -a : EReal) = a := neg_neg a
  have hb₂ : (- -b : EReal) = b := neg_neg b
  rw [concaveAdd_apply, convexAdd_apply, hna, hb₁, hb₂]

/-! ### The inner product `⟨f, g⟩` of a convex and a concave function -/

/-- Rockafellar's inner product `⟨f, g⟩` **exists**: the two extrema `sup_x {g*(x) − f(x)}` and
`inf_y {f*(y) − g(y)}` agree. He leaves `⟨f, g⟩` undefined when they do not, so this predicate is
the definedness side condition and appears in every statement below that mentions one. -/
abbrev HasInnerProduct {n : ℕ} (f g : Rn n → EReal) : Prop :=
  HasFenchelPairing (pairing n) f g

/-- The value of `⟨f, g⟩`, represented by the inf side. It is Rockafellar's inner product only
under `HasInnerProduct`. -/
noncomputable abbrev innerProduct {n : ℕ} (f g : Rn n → EReal) : EReal :=
  fenchelPairing (pairing n) f g

variable {m n k : ℕ}

theorem innerProduct_eq (f g : Rn n → EReal) :
    innerProduct f g = ⨅ y, (conj (pairing n) f y - g y) := rfl

/-- The definedness condition in the book's own two extrema. -/
theorem hasInnerProduct_iff (f g : Rn n → EReal) :
    HasInnerProduct f g ↔
      (⨆ x, (concaveConj (pairing n) g x - f x)) = ⨅ y, (conj (pairing n) f y - g y) := by
  rw [← fenchelInf_apply (pairing n) f g]
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact Iff.rfl

/-- Weak duality: the sup side never exceeds the inf side, with no hypothesis. This is what makes
every existence claim below a single inequality. -/
theorem fenchelSup_le_innerProduct (f g : Rn n → EReal) :
    (⨆ x, (concaveConj (pairing n) g x - f x)) ≤ innerProduct f g := by
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact fenchelSup_le_fenchelInf (pairing n) f g

/-! ### Theorem 38.1 -/

/-- **Theorem 38.1**, first assertion: the infimal convolution `(F₁ □ F₂)u = F₁u □ F₂u` of two
proper convex bifunctions from `ℝᵐ` to `ℝⁿ` is a convex bifunction. -/
theorem theorem_38_1_convex {F₁ F₂ : Bifun (Rn m) (Rn n)} (hp₁ : Proper (graphFn F₁))
    (hp₂ : Proper (graphFn F₂)) (hc₁ : ConvexBifun F₁) (hc₂ : ConvexBifun F₂) :
    ConvexBifun (infConvBifun F₁ F₂) :=
  convexBifun_infConvBifun (fun u x => hp₁.ne_bot (u, x)) (fun u x => hp₂.ne_bot (u, x)) hc₁ hc₂

/-- **Theorem 38.1**, second assertion: `dom (F₁ □ F₂) = dom F₁ ∩ dom F₂`. The book prints the
left-hand side as `dom (F₁ ∩ F₂)`; the operation meant is `□`, as its own proof shows. No
hypothesis is needed. -/
theorem theorem_38_1_dom (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    domBifun (infConvBifun F₁ F₂) = domBifun F₁ ∩ domBifun F₂ :=
  domBifun_infConvBifun F₁ F₂

/-- **Theorem 38.1**, the inner-product identity `⟨(F₁ □ F₂)u, x*⟩ = ⟨F₁u, x*⟩ + ⟨F₂u, x*⟩`, under
the **convex** convention `∞ − ∞ = −∞`. It needs no hypothesis: it is Theorem 16.4's unconditional
row `conj_infConv` read slice by slice. -/
theorem theorem_38_1_bracket (F₁ F₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    bracket (pairing n) (infConvBifun F₁ F₂) u y
      = convexAdd (bracket (pairing n) F₁ u y) (bracket (pairing n) F₂ u y) :=
  congrFun (bracket_infConvBifun (pairing n) F₁ F₂ u) y

/-- **Theorem 38.1**, concave orientation: for concave bifunctions `□` is *supremal* convolution
and the identity holds under the **concave** convention `∞ − ∞ = +∞`, with `⟨Gu, x*⟩` the concave
conjugate of the slice. The statement is **false** with `convexAdd` in place of `concaveAdd`. Like
its convex twin it is unconditional. -/
theorem theorem_38_1_bracket_concave (G₁ G₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    concaveConj (pairing n) (supConv (G₁ u) (G₂ u)) y
      = concaveAdd (concaveConj (pairing n) (G₁ u) y) (concaveConj (pairing n) (G₂ u) y) := by
  have hneg : (fun x => -(supConv (G₁ u) (G₂ u) x))
      = infConv (fun w => -(G₁ u w)) (fun w => -(G₂ u w)) :=
    funext fun x => neg_supConv (G₁ u) (G₂ u) x
  rw [concaveAdd_apply, neg_concaveConj, neg_concaveConj, ← Pi.add_apply, ← conj_infConv,
    concaveConj_eq_neg_conj_neg, hneg]

/-! ### The algebra of `□` -/

/-- `□` is commutative "in the class of convex bifunctions from `ℝᵐ` to `ℝⁿ` to the extent that it
is defined". The hedge is unnecessary here: `infConv` is total on `EReal`, so this holds for
arbitrary bifunctions, improper ones included — strictly stronger than the book. -/
theorem infConvBifun_comm' (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  infConvBifun_comm F₁ F₂

/-- `□` is associative, again with no hypothesis. -/
theorem infConvBifun_assoc' (F₁ F₂ F₃ : Bifun (Rn m) (Rn n)) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  infConvBifun_assoc F₁ F₂ F₃

/-! ### Theorem 38.2 -/

/-- **Theorem 38.2**: `(F₁ □ F₂)* = F₁* □ F₂*`, the bifunction generalisation of
`(A₁ + A₂)* = A₁* + A₂*`; the `□` on the right is supremal convolution. Where the book asks that
`ri (dom F₁)` and `ri (dom F₂)` meet, the hypothesis here is `IsExactSum` for the two concave
functions `u ↦ ⟨Fᵢu, x*⟩`, one instance per `x*`. -/
theorem theorem_38_2 (F₁ F₂ : Bifun (Rn m) (Rn n))
    (hex : ∀ y : Rn n, IsExactSum (pairing m) (fun u => -(bracket (pairing n) F₁ u y))
      (fun u => -(bracket (pairing n) F₂ u y))) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  adjointBifun_infConvBifun_eq_supConvBifun (pairing m) (pairing n) F₁ F₂ hex

/-! ### Corollary 38.2.1 -/

/-- The `IsExactSum` Corollary 38.2.1 consumes. The book's condition is that `ri (dom F₁*)` and
`ri (dom F₂*)` have a point in common. -/
abbrev IsExactSumCor3821 (F₁ F₂ : Bifun (Rn m) (Rn n)) : Prop :=
  ∀ u : Rn m, IsExactSum (pairing n)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)) u)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₂)) u)

/-- **Corollary 38.2.1**, first assertion: for closed proper convex `F₁` and `F₂`, `F₁ □ F₂` is
closed. The hypothesis is `IsExactSumCor3821`, where the book asks that `ri (dom F₁*)` and
`ri (dom F₂*)` meet. The proof is not Rockafellar's: `F₁ □ F₂` is exhibited as a lower adjoint,
and those are closed unconditionally. -/
theorem corollary_38_2_1_closed {F₁ F₂ : Bifun (Rn m) (Rn n)} (hc₁ : ConvexBifun F₁)
    (hcl₁ : ClosedBifun F₁) (hc₂ : ConvexBifun F₂) (hcl₂ : ClosedBifun F₂)
    (hex : IsExactSumCor3821 F₁ F₂) : ClosedBifun (infConvBifun F₁ F₂) := by
  refine closedBifun_infConvBifun (Bu := pairing m) (Bx := pairing n) hc₁ hcl₁ hc₂ hcl₂ ?_
  simpa using hex

/-- **Corollary 38.2.1**, last assertion: `(F₁ □ F₂)* = cl (F₁* □ F₂*)`. Stated in the `F⁎*`
packaging, where the right-hand `□` is convolution in the *first* variable — what the book's
concave `F₁* □ F₂*` becomes once the negations move outside, keeping everything convex. -/
theorem corollary_38_2_1_adjoint {F₁ F₂ : Bifun (Rn m) (Rn n)}
    (h₁ : ClosedProperConvexFn (graphFn F₁)) (h₂ : ClosedProperConvexFn (graphFn F₂))
    (hex : IsExactSumCor3821 F₁ F₂) :
    lowerAdjointBifun (pairing m) (pairing n) (infConvBifun F₁ F₂)
      = clBifun (infConvFstBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)
          (lowerAdjointBifun (pairing m) (pairing n) F₂)) := by
  refine lowerAdjointBifun_infConvBifun_eq_clBifun (Bu := pairing m) (Bx := pairing n) h₁ h₂ ?_
  simpa using hex

/-! ### Theorem 38.3 -/

/-- **Theorem 38.3**, first assertion: for `λ > 0` the scalar multiple `Fλ`, defined by
`((Fλ)u)(x) = λ (Fu)(λ⁻¹x)`, is convex when `F` is. -/
theorem theorem_38_3_convex {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hF : ConvexBifun F) : ConvexBifun (smulRightBifun F l) :=
  convexBifun_smulRightBifun hl hF

/-- **Theorem 38.3**, the inner-product identity: `⟨(Fλ)u, x*⟩ = λ ⟨Fu, x*⟩`. -/
theorem theorem_38_3_bracket {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) (smulRightBifun F l) u y = (l : EReal) * bracket (pairing n) F u y :=
  congrFun (bracket_smulRightBifun hl (pairing n) F u) y

/-- **Theorem 38.3**, the adjoint formula: `(Fλ)* = F*λ`, with no hypothesis beyond `0 < λ`. -/
theorem theorem_38_3_adjoint {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) :
    dualProgram (smulRightBifun F l) = smulRightBifun (dualProgram F) l :=
  funext fun y => funext fun v => adjointBifun_smulRightBifun hl (pairing m) (pairing n) F y v

/-- **Theorem 38.3**, second assertion, closedness: `Fλ` is closed when `F` is closed convex and
`λ > 0`. -/
theorem theorem_38_3_closed {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (hF : ConvexBifun F)
    (hcl : ClosedBifun F) : ClosedBifun (smulRightBifun F l) := by
  have hcont : Continuous (scaleFst (Rn n) l : Rn m × Rn n →ₗ[ℝ] Rn m × Rn n) := by
    change Continuous fun p : Rn m × Rn n => ((l • p.1, p.2) : Rn m × Rn n)
    exact (continuous_fst.const_smul l).prodMk continuous_snd
  refine closedBifun_iff.2 ?_
  rw [graphFn_smulRightBifun hl F]
  exact closedFn_smulRight (pairingProd m n) (convexFn_compLin _ hF)
    (closedFn_compLin (closedBifun_iff.1 hcl) hcont) hl

/-- **Theorem 38.3**, second assertion, properness: `Fλ` is proper when `F` is and `λ > 0`. -/
theorem theorem_38_3_proper {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hp : Proper (graphFn F)) : Proper (graphFn (smulRightBifun F l)) := by
  rw [graphFn_smulRightBifun hl F]
  refine proper_smulRight ⟨?_, fun p => hp.ne_bot _⟩ hl
  obtain ⟨p₀, hp₀⟩ := hp.dom_nonempty
  refine ⟨(l⁻¹ • p₀.1, p₀.2), ?_⟩
  have hq : ((l • (l⁻¹ • p₀.1), p₀.2) : Rn m × Rn n) = p₀ := by
    rw [smul_inv_smul₀ hl.ne']
  change compLin (graphFn F) (scaleFst (Rn n) l) (l⁻¹ • p₀.1, p₀.2) < ⊤
  rw [compLin_apply, scaleFst_apply, hq]
  exact mem_dom.1 hp₀

/-! ### Theorem 38.4 -/

/-- **Theorem 38.4**, first assertion: the image `Ff` of a proper convex `f` on `ℝᵐ` under a
proper convex bifunction `F`, `(Ff)(x) = inf_u {f(u) + (Fu)(x)}`, is convex on `ℝⁿ`. -/
theorem theorem_38_4_convex {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hfp : Proper f) (hF : ConvexBifun F) (hf : ConvexFn f) :
    ConvexFn (imageBifun F f) :=
  convexFn_imageBifun (fun u x => hFp.ne_bot (u, x)) hfp.ne_bot hF hf

/-- **Theorem 38.4**, the conjugacy formula: `(Ff)* = F⁎* f*`. Where the book asks that `ri (dom f)`
meet `ri (dom F)`, the hypothesis here is the `IsExactSum` of Theorem 16.4 for `f` and
`u ↦ ⟨Fu, x*⟩`, whose properness field is his side condition `x* ∈ dom F*`. -/
theorem theorem_38_4_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    conj (pairing n) (imageBifun F f) y
      = imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f) y :=
  conj_imageBifun_eq_imageBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Theorem 38.4**, the attainment clause: the infimum defining `(F⁎* f*)(x*)` is attained. -/
theorem theorem_38_4_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    ∃ v : Rn m, conj (pairing m) f v - dualProgram F y v
      = conj (pairing n) (imageBifun F f) y :=
  exists_conj_imageBifun_eq (fun u x => hFp.ne_bot (u, x)) hf hex

/-! ### Corollary 38.4.1 -/

/-- The `IsExactSum` Corollary 38.4.1 consumes; the book's condition is that `ri (dom f*)` meets
`ri (dom F⁎*)`. -/
abbrev IsExactSumCor3841 (F : Bifun (Rn m) (Rn n)) (f : Rn m → EReal) : Prop :=
  ∀ x : Rn n, IsExactSum (pairing m) (conj (pairing m) f)
    (fun v => -(bracket (pairing n) (lowerAdjointBifun (pairing m) (pairing n) F) v x))

/-- **Corollary 38.4.1**, first assertion: `Ff` is closed, being a conjugate. -/
theorem corollary_38_4_1_closed {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) : ClosedFn (imageBifun F f) := by
  refine closedFn_imageBifun (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-- **Corollary 38.4.1**, middle assertion: the infimum defining `(Ff)(x)` is attained. -/
theorem corollary_38_4_1_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hF : ConvexBifun F) (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) {x : Rn n} :
    ∃ u : Rn m, f u + F u x = imageBifun F f x := by
  refine exists_imageBifun_eq (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex x

/-- **Corollary 38.4.1**, last assertion: `(Ff)* = cl (F⁎* f*)`. -/
theorem corollary_38_4_1_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) :
    conj (pairing n) (imageBifun F f)
      = clFn (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f)) := by
  refine conj_imageBifun_eq_clFn (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-! ### Theorem 38.5 -/

/-- `(GF)⁎ = F⁎ G⁎`: inversion reverses the order of a product. -/
theorem inverseBifun_compBifun' (G : Bifun (Rn n) (Rn k)) (F : Bifun (Rn m) (Rn n))
    (hFp : Proper (graphFn F)) (hGp : Proper (graphFn G)) :
    inverseBifun (compBifun G F) = concaveCompBifun (inverseBifun G) (inverseBifun F) :=
  inverseBifun_compBifun G F (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y))

/-- **Theorem 38.5**, first assertion: the product `GF`, `((GF)u)(y) = inf_x {(Fu)(x) + (Gx)(y)}`,
is a convex bifunction from `ℝᵐ` to `ℝᵖ`. -/
theorem theorem_38_5_convex {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) (hGp : Proper (graphFn G)) (hF : ConvexBifun F)
    (hG : ConvexBifun G) : ConvexBifun (compBifun G F) :=
  convexBifun_compBifun (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y)) hF hG

/-- **Theorem 38.5**, the adjoint formula: `(GF)* = F* G*`, the product on the right being the
concave one. Where the book asks that `ri (dom F⁎)` meet `ri (dom G)`, the hypothesis here is
`IsExactSum` for `f(x) = ⟨u*, F⁎x⟩` and `g(x) = ⟨Gx, y*⟩`, one instance per `(y*, u*)`. -/
theorem theorem_38_5_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    dualProgram (compBifun G F) z v
      = concaveCompBifun (dualProgram G) (dualProgram F) z v := by
  refine adjointBifun_compBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-- **Theorem 38.5**, the attainment clause: the supremum defining `((F* G*)y*)(u*)` is
attained. -/
theorem theorem_38_5_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    ∃ x : Rn n, dualProgram G z x + dualProgram F x v = dualProgram (compBifun G F) z v := by
  refine exists_adjointBifun_compBifun_eq (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-! ### Corollary 38.5.1 -/

/-- The `IsExactSum` Corollary 38.5.1 consumes; the book's condition is that `ri (dom F*)` and
`ri (dom G⁎*)` have a point in common. -/
abbrev IsExactSumCor3851 (F : Bifun (Rn m) (Rn n)) (G : Bifun (Rn n) (Rn k)) : Prop :=
  ∀ (u : Rn m) (y : Rn k), IsExactSum (pairing n)
    (concaveBracket (pairing m) (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F)) u)
    (fun w => -(bracket (pairing k) (lowerAdjointBifun (pairing n) (pairing k) G) w y))

/-- **Corollary 38.5.1**, first assertion: `GF` is closed, being a lower adjoint. -/
theorem corollary_38_5_1_closed {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) : ClosedBifun (compBifun G F) := by
  refine closedBifun_compBifun (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-- **Corollary 38.5.1**, middle assertion: the infimum defining `((GF)u)(y)` is attained. -/
theorem corollary_38_5_1_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) {u : Rn m} {y : Rn k} :
    ∃ x : Rn n, F u x + G x y = compBifun G F u y := by
  refine exists_compBifun_eq (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  simpa using hex u y

/-- **Corollary 38.5.1**, last assertion: `(GF)* = cl (F* G*)`, in the `F⁎*` packaging
`(GF)⁎* = cl (G⁎* F⁎*)` — inversion reverses the order twice, so the right-hand product is taken
in the same order as `GF`. -/
theorem corollary_38_5_1_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) :
    lowerAdjointBifun (pairing m) (pairing k) (compBifun G F)
      = clBifun (compBifun (lowerAdjointBifun (pairing n) (pairing k) G)
          (lowerAdjointBifun (pairing m) (pairing n) F)) := by
  refine lowerAdjointBifun_compBifun_eq_clBifun (Bu := pairing m) (Bx := pairing n)
    (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-! ### Lemma 38.6 -/

/-- **Lemma 38.6**, first assertion: if `⟨f, g⟩` exists then so does `⟨f*, g*⟩`. The book's proof
is the chain `−⟨f, g⟩ ≤ ⟨f*, g*⟩_sup ≤ ⟨f*, g*⟩_inf ≤ −⟨f, g⟩`, whose middle link is weak
duality. -/
theorem lemma_38_6_exists {f g : Rn n → EReal} (hf : Proper f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    HasInnerProduct (conj (pairing n) f) (concaveConj (pairing n) g) := by
  simpa using hasFenchelPairing_conj (B := pairing n) hf hg h

/-- **Lemma 38.6**, the value: `⟨f*, g*⟩ = −⟨f, g⟩`. The lemma's second assertion, that
`⟨cl f, cl g⟩` then exists and equals `⟨f, g⟩`, is not formalized. -/
theorem lemma_38_6 {f g : Rn n → EReal} (hf : Proper f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    innerProduct (conj (pairing n) f) (concaveConj (pairing n) g) = -(innerProduct f g) := by
  simpa using fenchelPairing_conj (B := pairing n) hf hg h

/-! ### Theorem 38.7 and Corollary 38.7.1 -/

/-- **Corollary 38.7.1**, existence: `⟨f, F*x*⟩` exists for every `x*`. Weak duality supplies one
inequality for free and Theorem 38.4 the other. -/
theorem corollary_38_7_1_exists {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    HasInnerProduct f (dualProgram F y) :=
  hasFenchelPairing_adjointBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Corollary 38.7.1**: `⟨Ff, x*⟩ = ⟨f, F*x*⟩` — an adjoint moves across the inner product. The
left side is `(Ff)*(x*)`, the right the inner product of the convex `f` with the concave
`F*x*`. -/
theorem corollary_38_7_1 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    conj (pairing n) (imageBifun F f) y = innerProduct f (dualProgram F y) :=
  conj_imageBifun_eq_fenchelPairing (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Theorem 38.7**, first equality: `⟨Ff, g*⟩ = ⟨f, F*g*⟩`. Where the book asks that some `u` in
`ri (dom f) ∩ ri (dom F)` have `ri (dom (Fu))` meeting `ri (dom g)`, the hypothesis here is
`IsExactSum` together with a point at which `f`, `F` and `g` are all finite. The middle member
`−⟨f*, F⁎g⟩` of the book's four-term chain is not formalized. -/
theorem theorem_38_7 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    innerProduct (imageBifun F f) (concaveConj (pairing n) g)
      = innerProduct f (concaveImageBifun (dualProgram F) (concaveConj (pairing n) g)) :=
  fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (Bu := pairing m) (Bx := pairing n)
    (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hgb hgt hex

/-- **Theorem 38.7**, last equality: `⟨F⁎*f*, g⟩ = −⟨Ff, g*⟩`. The left side is the *sup* side of
`⟨F⁎*f*, g⟩`, and both sides unwind to the same double extremum. -/
theorem theorem_38_7_third {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : Proper (graphFn F)) (hf : Proper f) (hgd : (domConcave g).Nonempty) {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    fenchelSup (pairing n)
        (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (conj (pairing m) f)) g
      = -(innerProduct (imageBifun F f) (concaveConj (pairing n) g)) := by
  have h := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (Bu := pairing m) (Bx := pairing n)
    (F := F) (f := f) (g := g) (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hex
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 38.7.2 -/

/-- **Corollary 38.7.2**, the existence clause: `⟨Fu, G*y*⟩` exists. -/
theorem corollary_38_7_2_exists {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : Proper (graphFn G)) {u : Rn m} (hFu : Proper (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    HasInnerProduct (F u) (dualProgram G z) :=
  hasFenchelPairing_adjointBifun_slice (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Corollary 38.7.2**, first equality: `⟨GFu, y*⟩ = ⟨Fu, G*y*⟩`, Corollary 38.7.1 at the slice
`Fu`, since `(GF)u = G(Fu)`. It carries the `IsExactSum` its proof consumes: the book derives that
hypothesis by "a pithy exercise in the calculus of relative interiors" left to the reader. -/
theorem corollary_38_7_2_first {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : Proper (graphFn G)) {u : Rn m} (hFu : Proper (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z = innerProduct (F u) (dualProgram G z) :=
  bracket_compBifun_eq_fenchelPairing (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Corollary 38.7.2**, second equality: `⟨GFu, y*⟩ = ⟨u, F*G*y*⟩` at every `u ∈ ri (dom (GF))`.
This is Corollary 33.2.1 with Theorem 38.5, and unlike the first equality it genuinely needs the
relative interior. -/
theorem corollary_38_7_2_second {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : Proper (graphFn F)) (hGF : ConvexBifun (compBifun G F)) {u : Rn m}
    (hu : u ∈ ri (domBifun (compBifun G F))) {z : Rn k}
    (hex : ∀ v : Rn m, IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z
      = concaveBracket (pairing m) (concaveCompBifun (dualProgram G) (dualProgram F)) u z := by
  refine bracket_compBifun_eq_concaveBracket_concaveCompBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) hGF hu ?_
  intro v
  simpa using hex v

/-! ### The closing discussion: co-finite bifunctions -/

/-- For a co-finite convex bifunction `⟨Fu, x*⟩` is finite for all `u` and `x*`: Corollary 13.3.1
at the slice `Fu`. -/
theorem cofiniteBifun_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) : bracket (pairing n) F u y ≠ ⊥ ∧ bracket (pairing n) F u y ≠ ⊤ :=
  ⟨CofiniteBifun.bracket_ne_bot (Bx := pairing n) hF u y,
    (CofiniteBifun.bracket_lt_top (Bx := pairing n) hF u y).ne⟩

/-- A closed convex bifunction is co-finite **if and only if** `⟨Fu, x*⟩` is finite for all `u`
and `x*`. -/
theorem cofinite_iff_forall_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) :
    CofiniteBifun F ↔ ∀ (u : Rn m) (y : Rn n), bracket (pairing n) F u y < ⊤ :=
  ⟨fun h u y => CofiniteBifun.bracket_lt_top (Bx := pairing n) h u y,
    cofiniteBifun_of_forall_bracket_lt_top hF hcl⟩

/-- For a co-finite `F` the two inner products agree at *every* `u`: `⟨Fu, x*⟩ = ⟨u, F*x*⟩`, which
is Corollary 33.2.1 with `ri (dom F) = ℝᵐ`. -/
theorem cofiniteBifun_bracket_eq {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) F u y = concaveBracket (pairing m) (dualProgram F) u y :=
  CofiniteBifun.bracket_eq_concaveBracket_adjointBifun (pairing m) (pairing n) hF u y

/-- The infimal convolution of two co-finite convex bifunctions is co-finite. -/
theorem cofinite_infConvBifun' {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  cofiniteBifun_infConvBifun (pairing n) hF₁ hF₂

/-- `(F₁ □ F₂)* = F₁* □ F₂*` for co-finite bifunctions, with Theorem 38.2's relative-interior
hypothesis discharged: the brackets are finite everywhere. -/
theorem cofinite_adjoint_infConvBifun {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  adjointBifun_infConvBifun_of_cofinite (pairing m) (pairing n) hF₁ hF₂

/-- `F ↦ Fλ` with `λ > 0` preserves co-finiteness. -/
theorem cofinite_smulRightBifun' {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hF : CofiniteBifun F)
    (hl : 0 < l) : CofiniteBifun (smulRightBifun F l) :=
  cofiniteBifun_smulRightBifun (pairing n) hF hl

/-- A closed proper convex bifunction `F` from `ℝᵐ` to `ℝⁿ` is co-finite **if and only if**
`dom F = ℝᵐ` and `dom F* = ℝⁿ`. Rockafellar cites Theorem 34.2; the proof here does not use the
saddle-function correspondence at all, only Corollary 13.3.1 slice by slice. -/
theorem cofiniteBifun_of_domBifun_eq_univ' {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hp : Proper (graphFn F)) :
    CofiniteBifun F ↔ domBifun F = univ ∧ domConcaveBifun (dualProgram F) = univ :=
  cofiniteBifun_iff_domBifun_eq_univ (Bu := pairing m) (Bx := pairing n) hF hcl hp

end Rockafellar
