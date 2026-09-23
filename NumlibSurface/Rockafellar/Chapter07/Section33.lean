import Numlib.Analysis.Convex.Process.Duality
import Numlib.Analysis.Convex.Saddle.Conjugate
import NumlibSurface.Rockafellar.Chapter06.Section30

/-!
# Rockafellar §33: saddle-functions

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §33
(pp. 349–358): concave-convex and convex-concave functions on `ℝᵐ × ℝⁿ`, the partial closures `cl₁`
and `cl₂`, and the correspondence — "at the heart of the theory of saddle-functions" — between
saddle-functions and convex bifunctions from `ℝᵐ` to `ℝⁿ`.

All eleven numbered results of §33 are formalized: Theorems 33.1–33.3 and Corollaries 33.1.1,
33.1.2, 33.1.3, 33.2.1, 33.2.2, 33.3.1, 33.3.2, 33.3.3.

**Orientation.** A concave-convex `K (u, v)` is concave in the first argument and convex in the
second, and the two closures are named after the *argument* they close, not the sense in which
they close it: `cl₁` closes the first — concave — argument concavely, `cl₂` the second — convex —
argument convexly. So `K` is **lower closed** when `cl₂ (cl₁ K) = K` and **upper closed** when
`cl₁ (cl₂ K) = K`. Reversing any of this silently swaps every statement of §§34–37. A
*convex-concave* `K` is reached by negation; see `convexConcave_lowerClosed_iff`.

## Main definitions

* `cl₁`, `cl₂` — the two partial closures.
* `convexConjBracket`, `concaveConjBracket`, `bifunBracket`, `concaveBifunBracket`, `adjointBracket`
  — Rockafellar's overloaded `⟨·, ·⟩`, split into one name per meaning: the conjugate of a convex
  `f`, of a concave `f`, and of a slice of a convex, of a concave, and of an adjoint bifunction.
  The bifunction brackets are uncurried, as functions of the pair `(u, x*)`, the form every
  closedness predicate is stated against.
* `bifunOfSaddleFn` — the convex bifunction attached to a saddle-function, `Fu = K (u, ·)*`; the
  inverse of the bracket correspondence.

## Main results

* `theorem_33_1_concaveConvex`, `theorem_33_1_convexClosed`, `theorem_33_1_inversion`,
  `theorem_33_1_convexBifun`, `theorem_33_1_imageClosed`, `theorem_33_1_bracket_eq` — the bracket
  of a convex bifunction is a convex-closed concave-convex function, and the construction inverts.
* `corollary_33_1_1_cl₁_concaveConvex`, `corollary_33_1_1_cl₂_concaveConvex`,
  `corollary_33_1_1_cl₁_concaveClosed`, `corollary_33_1_1_cl₂_convexClosed` — the partial closures
  preserve concave-convexity and close the argument they name.
* `corollary_33_1_2` — the two relations `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K (u, ·)*` are inverse
  bijections, packaged as an `Equiv`.
* `corollary_33_1_3_convex`, `corollary_33_1_3_concave`, `corollary_33_1_3_inversion` — the
  polyhedral case.
* `theorem_33_2_first`, `theorem_33_2_second`, `corollary_33_2_1_primal`, `corollary_33_2_1_dual`,
  `corollary_33_2_2`, `corollary_33_2_2_exceptional` — `⟨u, F*x*⟩ = cl₁ ⟨Fu, x*⟩` and
  `cl₂ ⟨u, F*x*⟩ = ⟨(cl F)u, x*⟩`, with the relative-interior and polyhedral cases where the
  closures are inert.
* `theorem_33_3`, `theorem_33_3_lowerClosed`, `corollary_33_3_1`, `corollary_33_3_2`,
  `corollary_33_3_3` with its `dom` and formula clauses — the one-to-one correspondence between
  closed convex bifunctions and lower (resp. upper) closed concave-convex functions.
* `fullyClosed_iff_lowerClosed_and_upperClosed`, `convexConcave_lowerClosed_iff`,
  `convexConcave_upperClosed_iff`, `fullyClosedFn_of_finite` — the relations between the closedness
  notions, and the convex-concave convention.
-/

open Set

namespace Rockafellar

open ConvexAnalysis

/-! ### The two partial closures -/

/-- Rockafellar's `cl₂ K = cl_v K`, the **convex closure**: close `K (u, ·)` as a convex function
of the second argument, for each fixed `u`. An `abbrev` for `partialCl₂`. -/
noncomputable abbrev cl₂ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₂ K

/-- Rockafellar's `cl₁ K = cl_u K`, the **concave closure**: close `K (·, v)` as a concave
function of the first argument. An `abbrev` for `partialCl₁`; it is `cl₂` conjugated by negation,
not `cl₂` with the arguments exchanged. -/
noncomputable abbrev cl₁ {m n : ℕ} (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  partialCl₁ K

/-! ### The three brackets -/

section Brackets

variable {m n : ℕ}

/-- Rockafellar's `⟨f, x*⟩ = f*(x*)` for a **convex** `f`: the conjugate, as an inner product. -/
noncomputable abbrev convexConjBracket (f : Rn n → EReal) : Rn n → EReal := convexConj (pairing n) f

/-- Rockafellar's `⟨f, x*⟩` for a **concave** `f`: the concave conjugate. -/
noncomputable abbrev concaveConjBracket (f : Rn n → EReal) : Rn n → EReal :=
  concaveConj (pairing n) f

/-- Rockafellar's `⟨Fu, x*⟩ = (Fu)*(x*)` for a **convex** bifunction `F`, as a function of the
pair `(u, x*)`. This is the `K̲` of Corollary 33.3.1. -/
noncomputable abbrev bifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  saddleOfBifun (pairing n) F

/-- Rockafellar's `⟨u, Gx*⟩ = (Gx*)*(u)` for a **concave** bifunction `G` from `ℝⁿ` to `ℝᵐ`. -/
noncomputable abbrev concaveBifunBracket (G : Bifun (Rn n) (Rn m)) : Rn m × Rn n → EReal :=
  fun p => concaveBracket (pairing m) G p.1 p.2

/-- Rockafellar's `⟨u, F*x*⟩`, the concave bracket of the adjoint `F*` (§30, `dualProgram`); the
`K̄` of Corollary 33.3.1. -/
noncomputable abbrev adjointBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (dualProgram F)

/-- The convex bifunction attached to a saddle-function, `Fu = K (u, ·)*`: the inverse map of
Corollaries 33.1.2 and 33.3.2. -/
noncomputable abbrev bifunOfSaddleFn (K : Rn m × Rn n → EReal) : Bifun (Rn m) (Rn n) :=
  bifunOfSaddle (pairing n) K

/-- The book's defining formula: `⟨Fu, x*⟩ = sup_x {⟨x, x*⟩ - (Fu)(x)}`. -/
theorem bifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    bifunBracket F p = ⨆ x : Rn n, ((pairing n x p.2 : ℝ) : EReal) - F p.1 x := rfl

/-- The book's defining formula: `⟨u, Gx*⟩ = inf_v {⟨u, v⟩ - (Gx*)(v)}`. -/
theorem concaveBifunBracket_apply (G : Bifun (Rn n) (Rn m)) (p : Rn m × Rn n) :
    concaveBifunBracket G p = ⨅ v : Rn m, ((pairing m p.1 v : ℝ) : EReal) - G p.2 v := rfl

/-- The book's defining formula for `Fu = K (u, ·)*`. -/
theorem bifunOfSaddleFn_apply (K : Rn m × Rn n → EReal) (u : Rn m) (x : Rn n) :
    bifunOfSaddleFn K u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := rfl

/-- `⟨f, x*⟩ = ⟨x, x*⟩` when `f` is the indicator of `x`: the notation extends the ordinary inner
product along the embedding of `ℝⁿ` into the convex functions. -/
theorem convexConjBracket_indicatorFn (x y : Rn n) :
    convexConjBracket (indicatorFn ({x} : Set (Rn n))) y = ((pairing n x y : ℝ) : EReal) :=
  congrFun ((supportFn_eq_convexConj_indicatorFn (pairing n) {x}).symm.trans
    (supportFn_singleton (pairing n) x)) y

end Brackets

/-! ### Theorem 33.1 -/

section Thm331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 33.1**, first clause: for a convex bifunction `F`, `⟨Fu, x*⟩` is concave-convex in
`(u, x*)`. Concavity in `u` is Theorem 5.7 for the image of the graph function. -/
theorem theorem_33_1_concaveConvex (hF : ConvexBifun F) : ConcaveConvexFn (bifunBracket F) :=
  concaveConvexFn_bracket hF (pairing n)

/-- **Theorem 33.1**, second clause: `⟨Fu, x*⟩` is convex-closed, with no hypothesis on `F`
whatever — each slice is a conjugate. -/
theorem theorem_33_1_convexClosed (F : Bifun (Rn m) (Rn n)) : PartialClosed₂ (bifunBracket F) :=
  partialClosed₂_saddleOfBifun

/-- **Theorem 33.1**, the inversion formula: Fenchel–Moreau (Theorem 12.2) uniformly in `u`. -/
theorem theorem_33_1_inversion (hF : ConvexBifun F) (u : Rn m) (x : Rn n) :
    convexCl (F u) x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  congrFun (convexCl_eq_convexConj_bracket (Bx := pairing n) hF u) x

/-- **Theorem 33.1**, converse: for a concave-convex `K`, the bifunction `Fu = K (u, ·)*` is
convex. -/
theorem theorem_33_1_convexBifun (hK : ConcaveConvexFn K) : ConvexBifun (bifunOfSaddleFn K) :=
  convexBifun_bifunOfSaddle hK (pairing n)

/-- **Theorem 33.1**, converse: that bifunction is image-closed, each `Fu` being a conjugate. -/
theorem theorem_33_1_imageClosed (K : Rn m × Rn n → EReal) :
    ImageClosedBifun (bifunOfSaddleFn K) :=
  imageClosedBifun_bifunOfSaddle

/-- **Theorem 33.1**, converse, the identity that closes the loop: `⟨Fu, x*⟩ = (cl₂ K)(u, x*)`,
with `cl₂` the closure in the convex — second — argument. -/
theorem theorem_33_1_bracket_eq (hK : ConcaveConvexFn K) :
    bifunBracket (bifunOfSaddleFn K) = cl₂ K :=
  funext fun p => bracket_bifunOfSaddle (Bx := pairing n) hK p

end Thm331

/-! ### Corollary 33.1.1 -/

section Cor3311

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Corollary 33.1.1**: `cl₁ K` is again concave-convex. -/
theorem corollary_33_1_1_cl₁_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₁ K) :=
  concaveConvexFn_partialCl₁ (pairing m) hK

/-- **Corollary 33.1.1**: `cl₂ K` is again concave-convex. -/
theorem corollary_33_1_1_cl₂_concaveConvex (hK : ConcaveConvexFn K) :
    ConcaveConvexFn (cl₂ K) :=
  concaveConvexFn_partialCl₂ (pairing n) hK

/-- **Corollary 33.1.1**: `cl₁ K` is concave-closed; the concave closure is idempotent. -/
theorem corollary_33_1_1_cl₁_concaveClosed (K : Rn m × Rn n → EReal) :
    PartialClosed₁ (cl₁ K) :=
  partialClosed₁_partialCl₁ K

/-- **Corollary 33.1.1**: `cl₂ K` is convex-closed. -/
theorem corollary_33_1_1_cl₂_convexClosed (K : Rn m × Rn n → EReal) :
    PartialClosed₂ (cl₂ K) :=
  partialClosed₂_partialCl₂ K

end Cor3311


/-! ### Corollary 33.1.2 -/

section Cor3312

variable {m n : ℕ}

/-- A closed bifunction is image-closed: a slice of a closed function is closed. -/
theorem imageClosedBifun_of_closedConvexBifun {F : Bifun (Rn m) (Rn n)} (hF : ClosedConvexBifun F) :
    ImageClosedBifun F :=
  hF.imageClosedBifun

/-- **Corollary 33.1.2**. The relations `K (u, x*) = ⟨Fu, x*⟩` and `Fu = K (u, ·)*` are a
one-to-one correspondence between the convex-closed concave-convex functions on `ℝᵐ × ℝⁿ` and the
image-closed convex bifunctions from `ℝᵐ` to `ℝⁿ`. -/
noncomputable def corollary_33_1_2 :
    {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ PartialClosed₂ K} :=
  bifunSaddleEquiv (Bx := pairing n)

/-- The forward relation of Corollary 33.1.2 is `K (u, x*) = ⟨Fu, x*⟩`. -/
theorem corollary_33_1_2_apply
    (F : {F : Bifun (Rn m) (Rn n) // ConvexBifun F ∧ ImageClosedBifun F}) :
    (corollary_33_1_2 F).1 = bifunBracket F.1 := rfl

/-- The inverse relation of Corollary 33.1.2 is `Fu = K (u, ·)*`. -/
theorem corollary_33_1_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ PartialClosed₂ K}) :
    (corollary_33_1_2.symm K).1 = bifunOfSaddleFn K.1 := rfl

end Cor3312

/-! ### Corollary 33.1.3 -/

section Cor3313

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.1.3**: for a polyhedral convex bifunction `F`, `⟨Fu, x*⟩` is polyhedral convex
in `x*` for each `u`. -/
theorem corollary_33_1_3_convex (hF : PolyhedralBifun F) (u : Rn m) :
    PolyhedralFn fun y => bifunBracket F (u, y) :=
  polyhedralFn_bracket hF (pairing n) u

/-- **Corollary 33.1.3**: `⟨Fu, x*⟩` is polyhedral concave in `u` for each `x*`. -/
theorem corollary_33_1_3_concave (hF : PolyhedralBifun F) (y : Rn n) :
    PolyhedralFn fun u => -(bifunBracket F (u, y)) :=
  polyhedralFn_neg_bracket hF (pairing n) y

/-- **Corollary 33.1.3**: a proper polyhedral convex bifunction is recovered from its bracket with
no closure operation, being already closed. -/
theorem corollary_33_1_3_inversion (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F))
    (u : Rn m)
    (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - bifunBracket F (u, y) :=
  eq_iSup_sub_bracket_of_polyhedralBifun (pairing n) hF hp u x

end Cor3313

/-! ### The adjoint bracket -/

section AdjointBracket

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- `⟨u, F*x*⟩` is concave-convex in `(u, x*)`, with no hypothesis on `F`: the adjoint of any
bifunction is concave. -/
theorem adjointBracket_concaveConvex (F : Bifun (Rn m) (Rn n)) :
    ConcaveConvexFn (adjointBracket F) :=
  concaveConvexFn_concaveBracket (concaveBifun_convexAdjointBifun (pairing m) (pairing n) F)
      (pairing m)

/-- `⟨u, F*x*⟩` is concave-closed: it is a `cl₁` by Theorem 33.2, and every `cl₁` is
concave-closed by Corollary 33.1.1. -/
theorem adjointBracket_concaveClosed (hF : ConvexBifun F) :
    PartialClosed₁ (adjointBracket F) := by
  have h : adjointBracket F = cl₁ (bifunBracket F) :=
    (partialCl₁_bracket (pairing m) (pairing n) hF).symm
  rw [h]
  exact corollary_33_1_1_cl₁_concaveClosed _

end AdjointBracket

/-! ### Theorem 33.2 -/

section Thm332

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Theorem 33.2**, first equation: `⟨u, F*x*⟩ = cl₁ ⟨Fu, x*⟩`, the closure in the concave —
first — argument. It is concave Fenchel–Moreau in `u`. -/
theorem theorem_33_2_first (hF : ConvexBifun F) : adjointBracket F = cl₁ (bifunBracket F) :=
  (partialCl₁_bracket (pairing m) (pairing n) hF).symm

/-- **Theorem 33.2**, second equation: `cl₂ ⟨u, F*x*⟩ = ⟨(cl F)u, x*⟩`, the closure in the convex —
second — argument. It is the first equation at `F*` composed with Theorem 30.1's `F** = cl F`. -/
theorem theorem_33_2_second (hF : ConvexBifun F) :
    cl₂ (adjointBracket F) = bifunBracket (convexClBifun F) := by
  funext p
  exact congrFun
    (partialCl₂_concaveBracket_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) hF p.1) p.2

end Thm332

/-! ### Corollary 33.2.1 -/

section Cor3321

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.2.1**, first assertion: if `u ∈ ri (dom F)` then `⟨Fu, x*⟩ = ⟨u, F*x*⟩` for
every `x*`. The two differ by `cl₁`, which Theorem 7.4 removes on `ri (dom)`. -/
theorem corollary_33_2_1_primal (hF : ConvexBifun F) {u : Rn m} (hu : u ∈ ri (convexDomBifun F))
    (y : Rn n) : bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint (pairing m) (pairing n) hF hu y

/-- **Corollary 33.2.1**, second assertion: if `F` is closed and `x* ∈ ri (dom F*)` then
`⟨Fu, x*⟩ = ⟨u, F*x*⟩` for every `u`. The book's "apply the first fact to `F*`" is not literally
available, `F*` being concave; the route here spends the closedness hypothesis, and it is spent
nowhere else in the corollary. -/
theorem corollary_33_2_1_dual (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (u : Rn m) {y : Rn n}
    (hy : y ∈ ri (concaveDomBifun (dualProgram F))) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_mem_relint_concaveDomBifun
    (Bu := pairing m) (Bx := pairing n) hF hcl u hy

end Cor3321

/-! ### Corollary 33.2.2 -/

section Cor3322

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- **Corollary 33.2.2**. For a proper polyhedral convex bifunction `F`, `⟨Fu, x*⟩ = ⟨u, F*x*⟩`
except when both `u ∉ dom F` and `x* ∉ dom F*`: polyhedrality drops Corollary 33.2.1's `ri`. -/
theorem corollary_33_2_2 (hF : PolyhedralBifun F) (hp : ProperConvex (graphFn F)) (u : Rn m)
    (y : Rn n)
    (h : u ∈ convexDomBifun F ∨ y ∈ concaveDomBifun (dualProgram F)) :
    bifunBracket F (u, y) = adjointBracket F (u, y) :=
  bracket_eq_concaveBracket_convexAdjointBifun_of_polyhedral (pairing m) (pairing n) hF hp u y h

/-- **Corollary 33.2.2**, the parenthetical: in the exceptional case one quantity is `+∞`, the
other `-∞`. Neither polyhedrality nor properness is used. -/
theorem corollary_33_2_2_exceptional {u : Rn m} (hu : u ∉ convexDomBifun F) {y : Rn n}
    (hy : y ∉ concaveDomBifun (dualProgram F)) :
    bifunBracket F (u, y) = ⊥ ∧ adjointBracket F (u, y) = ⊤ :=
  bracket_eq_bot_and_concaveBracket_eq_top (pairing m) (pairing n) hu hy

end Cor3322


/-! ### Full, lower and upper closedness -/

section Closedness

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- A saddle-function finite everywhere is convex-closed: Corollary 10.1.1, slice by slice. -/
theorem partialClosed₂_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : PartialClosed₂ K := by
  refine partialClosed₂_iff.2 fun u => ?_
  refine (closedConvex_iff_lowerSemicontinuous fun x => hbot (u, x)).2 ?_
  refine Continuous.lowerSemicontinuous
    (ConvexFn.continuous_of_convexDom_eq_univ (hK.convex_snd u) ⟨⟨0, ?_⟩, fun x => hbot (u, x)⟩ ?_)
  · exact lt_top_iff_ne_top.2 (htop (u, 0))
  · exact Set.eq_univ_of_forall fun x => lt_top_iff_ne_top.2 (htop (u, x))

/-- A saddle-function finite everywhere is fully closed. -/
theorem fullyClosedFn_of_finite (hK : ConcaveConvexFn K) (hbot : ∀ p, K p ≠ ⊥)
    (htop : ∀ p, K p ≠ ⊤) : FullyClosedFn K := by
  refine ⟨partialClosed₂_of_finite hK hbot htop, ?_⟩
  have hswap : PartialClosed₂ (saddleSwap K) :=
    partialClosed₂_of_finite hK.saddleSwap
      (fun q => by simpa [saddleSwap] using htop (q.2, q.1))
      (fun q => by simpa [saddleSwap] using hbot (q.2, q.1))
  have h : saddleSwap (partialCl₁ K) = saddleSwap K := by
    rw [← partialCl₂_saddleSwap]
    exact hswap
  exact saddleSwap_injective h

/-- Fully closed is lower closed and upper closed together, by idempotence of `cl₁` and `cl₂`. -/
theorem fullyClosed_iff_lowerClosed_and_upperClosed (K : Rn m × Rn n → EReal) :
    FullyClosedFn K ↔ LowerClosedFn K ∧ UpperClosedFn K :=
  fullyClosedFn_iff

/-- The convex-concave convention. For a *convex-concave* `K` the book's `cl₁` closes convexly in
the first argument and its `cl₂` concavely in the second, so both are the operators of this module
conjugated by negation, and the book's "`K` is lower closed" says `UpperClosedFn (-K)`. -/
theorem convexConcave_lowerClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(upperCl (fun q => -(K q)) p)) = K ↔ UpperClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

/-- The other half: "`K` upper closed" for a convex-concave `K` is `LowerClosedFn (-K)`. -/
theorem convexConcave_upperClosed_iff (K : Rn m × Rn n → EReal) :
    (fun p => -(lowerCl (fun q => -(K q)) p)) = K ↔ LowerClosedFn fun p => -(K p) := by
  constructor
  · intro h
    funext p
    rw [← congrFun h p, neg_neg]
  · intro h
    funext p
    rw [congrFun h p, neg_neg]

end Closedness

/-! ### Theorem 33.3 -/

section Thm333

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 33.3**, one direction: the bracket of a *closed* convex bifunction is a lower closed
concave-convex function. Both closure steps are Theorem 33.2. -/
theorem theorem_33_3_lowerClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    LowerClosedFn (bifunBracket F) :=
  lowerClosedFn_bracket (pairing m) (pairing n) hF hcl

/-- **Theorem 33.3**. The same relations are a one-to-one correspondence between the lower closed
concave-convex functions on `ℝᵐ × ℝⁿ` and the *closed* convex bifunctions from `ℝᵐ` to `ℝⁿ`. -/
theorem theorem_33_3 (hK : ConcaveConvexFn K) (hlc : LowerClosedFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧ bifunBracket F = K :=
  exists_unique_convexBifun_bracket_eq (pairing m) (pairing n) hK hlc

end Thm333

/-! ### Corollary 33.3.1 -/

section Cor3331

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {Klow Kup : Rn m × Rn n → EReal}

/-- **Corollary 33.3.1**. For concave-convex `K̲` and `K̄`, a closed convex bifunction `F` with
`K̲ (u, x*) = ⟨Fu, x*⟩` and `K̄ (u, x*) = ⟨u, F*x*⟩` exists — and is then unique — if and only if
`cl₁ K̲ = K̄` and `cl₂ K̄ = K̲`. This is the sufficiency. -/
theorem corollary_33_3_1 (hK : ConcaveConvexFn Klow) (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧
      bifunBracket F = Klow ∧ adjointBracket F = Kup :=
  exists_unique_bifun_of_closure_pair (pairing m) (pairing n) hK h1 h2

/-- **Corollary 33.3.1**, necessity: `cl₁ ⟨Fu, x*⟩ = ⟨u, F*x*⟩`, needing no closedness. -/
theorem corollary_33_3_1_necessity_first (hF : ConvexBifun F) :
    cl₁ (bifunBracket F) = adjointBracket F :=
  partialCl₁_bracket (pairing m) (pairing n) hF

/-- **Corollary 33.3.1**, necessity: `cl₂ ⟨u, F*x*⟩ = ⟨Fu, x*⟩` for a *closed* `F`. -/
theorem corollary_33_3_1_necessity_second (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    cl₂ (adjointBracket F) = bifunBracket F :=
  partialCl₂_concaveBracket_adjoint (pairing m) (pairing n) hF hcl

/-- **Corollary 33.3.1**: the closure relations make `K̲` lower closed. -/
theorem corollary_33_3_1_lowerClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    LowerClosedFn Klow := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [lowerClosedFn_iff, lowerCl_def, e1, e2]

/-- **Corollary 33.3.1**: the closure relations make `K̄` upper closed. -/
theorem corollary_33_3_1_upperClosed (h1 : cl₁ Klow = Kup) (h2 : cl₂ Kup = Klow) :
    UpperClosedFn Kup := by
  have e1 : partialCl₁ Klow = Kup := h1
  have e2 : partialCl₂ Kup = Klow := h2
  rw [upperClosedFn_iff, upperCl_def, e2, e1]

/-- **Corollary 33.3.1**: `K̲ ≤ K̄`. Only the `cl₂` relation is used, because `cl₂` lowers. -/
theorem corollary_33_3_1_le (h2 : cl₂ Kup = Klow) : Klow ≤ Kup :=
  le_of_partialCl₂_eq h2

end Cor3331

/-! ### Corollary 33.3.2 -/

section Cor3332

variable {m n : ℕ}

/-- **Corollary 33.3.2**. `K̄ = cl₁ K̲` and `K̲ = cl₂ K̄` are a one-to-one correspondence between
the lower closed and the upper closed concave-convex functions on `ℝᵐ × ℝⁿ`. -/
noncomputable def corollary_33_3_2 :
    {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K} ≃
      {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K} :=
  lowerUpperClosedEquiv (pairing m) (pairing n)

/-- The forward relation of Corollary 33.3.2 is `K̄ = cl₁ K̲`. -/
theorem corollary_33_3_2_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ LowerClosedFn K}) :
    (corollary_33_3_2 K).1 = cl₁ K.1 := rfl

/-- The inverse relation of Corollary 33.3.2 is `K̲ = cl₂ K̄`. -/
theorem corollary_33_3_2_symm_apply
    (K : {K : Rn m × Rn n → EReal // ConcaveConvexFn K ∧ UpperClosedFn K}) :
    (corollary_33_3_2.symm K).1 = cl₂ K.1 := rfl

end Cor3332

/-! ### Corollary 33.3.3

Where the book asks for `K` "finite continuous" on `C × D`, meaning jointly, the hypotheses below
ask only for convexity, concavity and continuity of each one-variable section on its own set. -/

section Cor3333

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

private theorem dom₂_concaveBifunBracket (G : Bifun (Rn n) (Rn m)) :
    dom₂ (concaveBifunBracket G) = concaveDomBifun G := by
  ext y
  constructor
  · intro hy
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) G (0 : Rn m) w := hy 0
    rwa [convexDom_concaveBracket] at h
  · intro hy u
    have h : y ∈ convexDom fun w => concaveBracket (pairing m) G u w := by
      rw [convexDom_concaveBracket]; exact hy
    exact h

/-- **Corollary 33.3.3**: the lower simple extension `K̲` of such a `K` is lower closed. -/
theorem corollary_33_3_3_lowerClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    LowerClosedFn (lowerSimpleExt C D K) :=
  lowerClosedFn_lowerSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 33.3.3**: the upper simple extension `K̄` is upper closed. -/
theorem corollary_33_3_3_upperClosed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    UpperClosedFn (upperSimpleExt C D K) :=
  upperClosedFn_upperSimpleExt hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 33.3.3**, main clause: there is a unique closed convex bifunction `F` whose two
brackets are the lower and the upper simple extension of `K`. -/
theorem corollary_33_3_3 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧
      bifunBracket F = lowerSimpleExt C D K ∧ adjointBracket F = upperSimpleExt C D K :=
  exists_unique_bifun_of_simpleExt (pairing m) (pairing n) hC hCcl hDcl hCne hconv hconc hDne
    hcontD hcontC

/-- **Corollary 33.3.3**: that bifunction is `K̲ (u, ·)*`, and its bracket is `K̲` again. -/
theorem corollary_33_3_3_bracket (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = lowerSimpleExt C D K :=
  (theorem_33_1_bracket_eq (concaveConvexFn_lowerSimpleExt hC hconv hconc)).trans
    (partialCl₂_lowerSimpleExt hDcl hcontD)

/-- **Corollary 33.3.3**: and its adjoint bracket is `K̄`. -/
theorem corollary_33_3_3_adjointBracket (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)) = upperSimpleExt C D K := by
  rw [theorem_33_2_first
      (theorem_33_1_convexBifun (concaveConvexFn_lowerSimpleExt hC hconv hconc)),
    corollary_33_3_3_bracket hC hDcl hconv hconc hcontD]
  exact partialCl₁_lowerSimpleExt hCcl hCne hcontC

/-- **Corollary 33.3.3**: `dom F = C`. -/
theorem corollary_33_3_3_dom (hC : Convex ℝ C) (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) :
    convexDomBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) = C := by
  have h1 : dom₁ (bifunBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = convexDomBifun (bifunOfSaddleFn (lowerSimpleExt C D K)) :=
    dom₁_bracket (pairing n) _
  rw [← h1, corollary_33_3_3_bracket hC hDcl hconv hconc hcontD, dom₁_lowerSimpleExt hDne]

/-- **Corollary 33.3.3**: `dom F* = D`. -/
theorem corollary_33_3_3_domAdjoint (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D)
    (hcontC : ∀ x ∈ D, ContinuousOn (fun u => K (u, x)) C) :
    concaveDomBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) = D := by
  have h2 : dom₂ (adjointBracket (bifunOfSaddleFn (lowerSimpleExt C D K)))
      = concaveDomBifun (dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K))) :=
    dom₂_concaveBifunBracket _
  rw [← h2, corollary_33_3_3_adjointBracket hC hCcl hDcl hCne hconv hconc hcontD hcontC,
    dom₂_upperSimpleExt hCne]

/-- **Corollary 33.3.3**, the formula for `F` off `C`: `(Fu)(x) = +∞`. -/
theorem corollary_33_3_3_bifun_of_notMem {u : Rn m} (hu : u ∉ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x = ⊤ := by
  rw [bifunOfSaddleFn_apply]
  refine le_antisymm le_top (le_iSup_of_le 0 ?_)
  rw [lowerSimpleExt_of_notMem_left (p := (u, (0 : Rn n))) hu]
  simp

/-- **Corollary 33.3.3**, the formula for `F` on `C`:
`(Fu)(x) = sup {⟨x, x*⟩ - K (u, x*) | x* ∈ D}`. -/
theorem corollary_33_3_3_bifun_of_mem {u : Rn m} (hu : u ∈ C) (x : Rn n) :
    bifunOfSaddleFn (lowerSimpleExt C D K) u x
      = ⨆ y ∈ D, (((pairing n x y : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  rw [bifunOfSaddleFn_apply]
  refine iSup_congr fun y => ?_
  by_cases hy : y ∈ D
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iSup_pos hy]
  · rw [lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy, iSup_neg hy]
    simp

/-- **Corollary 33.3.3**, the formula for `F*` on `D`:
`(F*x*)(u*) = inf {⟨u, u*⟩ - K (u, x*) | u ∈ C}`. -/
theorem corollary_33_3_3_adjoint_of_mem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∈ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = ⨅ u ∈ C, (((pairing m u v : ℝ) : EReal) - ((K (u, y) : ℝ) : EReal)) := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    convexAdjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  rw [h, concaveConj_apply]
  refine iInf_congr fun u => ?_
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y)]
  by_cases hu : u ∈ C
  · rw [lowerSimpleExt_of_mem (p := (u, y)) hu hy, iInf_pos hu]
  · rw [lowerSimpleExt_of_notMem_left (p := (u, y)) hu, iInf_neg hu]
    simp

/-- **Corollary 33.3.3**, the formula for `F*` off `D`: `(F*x*)(u*) = -∞`. -/
theorem corollary_33_3_3_adjoint_of_notMem (hC : Convex ℝ C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x))
    (hconc : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun x => K (u, x)) D) {y : Rn n} (hy : y ∉ D) (v : Rn m) :
    dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v = ⊥ := by
  have hbr := congrFun (corollary_33_3_3_bracket hC hDcl hconv hconc hcontD)
  have h : dualProgram (bifunOfSaddleFn (lowerSimpleExt C D K)) y v
      = concaveConj (pairing m)
        (fun u => bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y) v :=
    convexAdjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) _ y v
  obtain ⟨u, hu⟩ := hCne
  rw [h, concaveConj_apply]
  refine le_antisymm (iInf_le_of_le u ?_) bot_le
  rw [show bracket (pairing n) (bifunOfSaddleFn (lowerSimpleExt C D K)) u y
      = lowerSimpleExt C D K (u, y) from hbr (u, y),
    lowerSimpleExt_of_notMem_right (p := (u, y)) hu hy]
  simp

end Cor3333

end Rockafellar
