import Numlib.Analysis.Convex.Saddle.Subdifferential
import NumlibSurface.Rockafellar.Chapter07.Section33

/-!
# Rockafellar, §36: Minimax Problems

The two iterated extrema `sup inf` and `inf sup`, the saddle-value and the saddle-point, the
reduction of a minimax problem on `C × D` to one on all of `ℝᵐ × ℝⁿ`, the inverse bifunction `F_*`,
and the identification of the Lagrangians of closed convex programs with the upper closed
concave-convex functions. All seven numbered results of §36 are formalized: Lemmas 36.1 and 36.2,
Theorems 36.3–36.6 and Corollary 36.3.1.

**Orientation.** From here to the end of the book, *minimization takes place in the convex argument
and maximization in the concave one*. For a concave-convex `K (u, v)` — concave in the first
argument, convex in the second — that fixes both extrema: `maximin K` is `sup_u inf_v K (u, v)` and
`minimax K` is `inf_v sup_u K (u, v)`, so Lemma 36.1 reads `maximin K ≤ minimax K`, and a
saddle-point is a `p` with `K (u, p.2) ≤ K p ≤ K (p.1, v)` — first argument maximised, second
minimised. Theorems 36.3–36.6 and every result of §37 are false verbatim under the opposite
convention.

`HasSaddleValue` is the bare equality of the two iterated extrema. Finiteness of the common value
is a separate conclusion, drawn where the book draws it, in Corollary 36.3.1.

## References

* [rockafellar1970convex] §36, pp. 379–387.
-/

namespace Rockafellar

open ConvexAnalysis

/-! ### The saddle-value and the saddle-point -/

section Defs

variable {m n : ℕ}

/-- The two iterated extrema, and the **saddle-value** of `K` — their common value, *when they are
equal*. Nothing is said about that value being finite. -/
theorem hasSaddleValue_iff_maximin_eq (K : Rn m × Rn n → EReal) :
    HasSaddleValue K ↔ (⨆ u : Rn m, ⨅ v : Rn n, K (u, v)) = ⨅ v : Rn n, ⨆ u : Rn m, K (u, v) :=
  Iff.rfl

/-- The definition of a **saddle-point**: `K (u, v̄) ≤ K (ū, v̄) ≤ K (ū, v)` for all `u` and `v`.
The first argument is the one `K` is maximised over. -/
theorem isSaddlePoint_iff_forall (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔ ∀ u : Rn m, ∀ v : Rn n, K (u, p.2) ≤ K p ∧ K p ≤ K (p.1, v) :=
  ⟨fun h u v => ⟨h.1 u, h.2 v⟩, fun h => ⟨fun u => (h u 0).1, fun v => (h 0 v).2⟩⟩

end Defs

/-! ### Lemma 36.1 -/

section Lemma361

variable {m n : ℕ}

/-- **Lemma 36.1**: `sup inf ≤ inf sup`, with no hypothesis at all — not even nonemptiness. -/
theorem lemma_36_1 (K : Rn m × Rn n → EReal) : maximin K ≤ minimax K :=
  maximin_le_minimax K

/-- **Lemma 36.1** in the book's own `C × D` form, for arbitrary subsets `C` and `D`. The `⨆ ∈`
reading makes the book's nonemptiness assumption unnecessary. -/
theorem lemma_36_1_on (C : Set (Rn m)) (D : Set (Rn n)) (K : Rn m × Rn n → EReal) :
    (⨆ u ∈ C, ⨅ v ∈ D, K (u, v)) ≤ ⨅ v ∈ D, ⨆ u ∈ C, K (u, v) :=
  iSup₂_le fun u hu => le_iInf₂ fun v hv =>
    (iInf₂_le (f := fun v (_ : v ∈ D) => K (u, v)) v hv).trans
      (le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, v)) u hu)

end Lemma361

/-! ### Lemma 36.2 -/

section Lemma362

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Lemma 36.2**: `(ū, v̄)` is a saddle-point exactly when the supremum in `sup inf` is attained
at `ū`, the infimum in `inf sup` at `v̄`, and the two extrema are equal. Stated on `ℝᵐ × ℝⁿ` rather
than the book's `C × D`; `IsSaddlePointOn` carries the relative reading where it is wanted. -/
theorem lemma_36_2 (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔
      (⨅ v : Rn n, K (p.1, v)) = maximin K ∧ (⨆ u : Rn m, K (u, p.2)) = minimax K ∧
        HasSaddleValue K :=
  isSaddlePoint_iff_attained

/-- **Lemma 36.2**, last sentence: at a saddle-point both extrema equal `K (ū, v̄)`. -/
theorem lemma_36_2_saddleValue (h : IsSaddlePoint K p) :
    maximin K = K p ∧ minimax K = K p :=
  ⟨IsSaddlePoint.maximin_eq h, IsSaddlePoint.minimax_eq h⟩

end Lemma362

/-! ### The reduction to the whole space -/

section Extension

variable {m n : ℕ}

/-- Where the book extends a finite `K` on `C × D` by `±∞`, the outer supremum in `sup inf` may
always be restricted to `C = dom₁ K`, since `inf_v K (u, v) = −∞` for `u ∉ C`. -/
theorem maximin_restricted (K : Rn m × Rn n → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v : Rn n, K (u, v) :=
  maximin_eq_biSup_dom₁ K

/-- The outer infimum in `inf sup` may always be restricted to `D = dom₂ K`. -/
theorem minimax_restricted (K : Rn m × Rn n → EReal) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u : Rn m, K (u, v) :=
  minimax_eq_biInf_dom₂ K

end Extension

/-! ### Theorem 36.3 -/

section Thm363

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Theorem 36.3**, first displayed equation: for a closed proper concave-convex `K`, with
`C = dom₁ K` and `D = dom₂ K`, `sup_{ℝᵐ} inf_{ℝⁿ} K = sup_C inf_D K`. -/
theorem theorem_36_3_maximin (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v ∈ dom₂ K, K (u, v) :=
  maximin_eq_biSup_biInf hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Theorem 36.3**, second displayed equation: `inf_{ℝⁿ} sup_{ℝᵐ} K = inf_D sup_C K`. With
`theorem_36_3_maximin` this says the two problems have the same pair of iterated extrema. -/
theorem theorem_36_3_minimax (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, v) :=
  minimax_eq_biInf_biSup hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Theorem 36.3**, last sentence: the saddle-points of `K` on `ℝᵐ × ℝⁿ` are its saddle-points
relative to `C × D = dom K`. -/
theorem theorem_36_3_saddlePoint (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p :=
  isSaddlePoint_iff_isSaddlePointOn_dom hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

end Thm363

/-! ### Corollary 36.3.1 -/

section Cor3631

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Corollary 36.3.1**, first assertion: a saddle-point of a proper saddle-function lies in
`dom K`. The book states this for a *closed* proper saddle-function; closedness is not used. -/
theorem corollary_36_3_1_mem_dom (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp h

/-- **Corollary 36.3.1**, second assertion: a proper saddle-function with a saddle-point has a
**finite** saddle-value. -/
theorem corollary_36_3_1_finite (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) :=
  IsSaddlePoint.exists_maximin_eq_coe hp h

end Cor3631

/-! ### Theorem 36.4 -/

section Thm364

variable {m n : ℕ} {K L : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Theorem 36.4**: equivalent saddle-functions have the same `sup inf`. Two concave functions
with the same closure have the same supremum, and the iterated extrema see only that. -/
theorem theorem_36_4_maximin (h : SaddleEquiv K L) : maximin K = maximin L :=
  SaddleEquiv.maximin_eq h

theorem theorem_36_4_minimax (h : SaddleEquiv K L) : minimax K = minimax L :=
  SaddleEquiv.minimax_eq h

/-- **Theorem 36.4**: one of two equivalent saddle-functions has a saddle-value exactly when the
other does. -/
theorem theorem_36_4_hasSaddleValue (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L :=
  SaddleEquiv.hasSaddleValue_iff h

/-- **Theorem 36.4**: equivalent saddle-functions have the same saddle-points. This is what makes
minimax theory a theory of equivalence classes, hence — by Theorem 36.5 — of convex programs. -/
theorem theorem_36_4_saddlePoint (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p :=
  SaddleEquiv.isSaddlePoint_iff h

end Thm364

/-! ### The inverse bifunction `F_*` -/

section Inverse

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- `F_*` is **concave** if `F` is convex: it is `flipBifun` composed with a change of sign. -/
theorem concaveBifun_inverseBifun (hF : ConvexBifun F) : ConcaveBifun (inverseBifun F) := by
  have he : (fun q : Rn n × Rn m => -(graphFn (inverseBifun F) q)) = graphFn (flipBifun F) :=
    funext fun _ => neg_neg _
  have h : ConcaveFn (graphFn (inverseBifun F)) := by
    rw [concaveFn_iff_convexFn_neg, he]
    exact convexBifun_flipBifun hF
  exact h

/-- The inverse operation is **involutory**, `(F_*)_* = F`. -/
theorem inverseBifun_involutive (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun F) = F :=
  inverseBifun_inverseBifun F

/-- The inverse operation **commutes with the adjoint**, `(F_*)^* = (F^*)_*`, so one may write
`F_*^*` for either. The left side is the concave adjoint of the concave bifunction `F_*`, the right
the inverse of `F*`; Rockafellar reads it as `(A⁻¹)^* = (A^*)⁻¹` for a non-singular `A`. -/
theorem concaveAdjointBifun_inverseBifun (F : Bifun (Rn m) (Rn n)) :
    concaveAdjointBifun (pairing m) (pairing n) (inverseBifun F)
      = inverseBifun (dualProgram F) := by
  have hlow : lowerAdjointBifun (pairing m) (pairing n) F = inverseBifun (dualProgram F) := rfl
  have h := lowerAdjointBifun_eq_concaveAdjointBifun (pairing m) (pairing n) F
  rw [hlow] at h
  simpa only [flip_pairing] using h.symm

/-- Rockafellar's `⟨u*, F_* x⟩`, the concave bracket of the inverse bifunction, as a function of
the pair `(u*, x)`. It *is* the Lagrangian of `(P)`, and by Theorem 37.1 the upper conjugate `K̄*`
of every member of `Ω (F)`. An `abbrev` for `concaveBifunBracket` at `inverseBifun F`. -/
noncomputable abbrev inverseBifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (inverseBifun F)

/-- The book's defining formula: `⟨u*, F_* x⟩ = inf_u {⟨u*, u⟩ + (Fu)(x)}`. -/
theorem inverseBifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    inverseBifunBracket F p = ⨅ u : Rn m, ((pairing m p.1 u : ℝ) : EReal) - inverseBifun F p.2 u :=
  rfl

end Inverse

/-! ### Theorem 36.5 -/

section Thm365

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {L : Rn m × Rn n → EReal}

/-- The Lagrangian `L (u*, x) = inf_u {⟨u*, u⟩ + (Fu)(x)}` of `(P)` **is** the bracket
`⟨u*, F_* x⟩`. The only step that is not definitional is symmetry of the Euclidean pairing. -/
theorem saddleLagrangian_eq_inverseBifunBracket (F : Bifun (Rn m) (Rn n)) :
    saddleLagrangian (pairing m) F = inverseBifunBracket F := by
  funext p
  rw [saddleLagrangian_apply, lagrangian_apply, inverseBifunBracket_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, pairing_comm, sub_eq_add_neg, neg_neg]

/-- The Lagrangian of a convex program is **concave-convex**: concave in the price variable `u*`,
convex in the primal variable `x`. -/
theorem saddleLagrangian_concaveConvex (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian (pairing m) F) :=
  concaveConvexFn_saddleLagrangian (pairing m) hF

/-- **Theorem 36.5.** `L` is the Lagrangian of a convex program associated with a closed convex
bifunction from `ℝᵐ` to `ℝⁿ` **if and only if** `L` is an upper closed concave-convex function on
`ℝᵐ × ℝⁿ`. So the regularized minimax problems of §36 and the closed proper convex programs of
§§29–30 are the same objects, read through the Lagrangian; with Corollary 34.2.2's unique upper
closed member per class, that names the canonical representative of a class. -/
theorem theorem_36_5 (L : Rn m × Rn n → EReal) :
    (∃ F : Bifun (Rn m) (Rn n),
        ConvexBifun F ∧ ClosedBifun F ∧ saddleLagrangian (pairing m) F = L)
      ↔ ConcaveConvexFn L ∧ UpperClosedFn L := by
  constructor
  · rintro ⟨F, hF, hcl, rfl⟩
    exact ⟨concaveConvexFn_saddleLagrangian (pairing m) hF,
      upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl⟩
  · rintro ⟨hL, huc⟩
    obtain ⟨G, hG, -⟩ :=
      exists_unique_closedBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc
    exact ⟨G, hG⟩

/-- **Theorem 36.5**, necessity alone: the Lagrangian of a closed convex bifunction is upper
closed concave-convex. -/
theorem theorem_36_5_upperClosed (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    UpperClosedFn (saddleLagrangian (pairing m) F) :=
  upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl

/-- An upper closed concave-convex `L` is the Lagrangian of **one and only one** closed convex
bifunction. The book determines it explicitly by `(Fu)(x) = sup_{u*} {L (u*, x) − ⟨u*, u⟩}`; the
statement here asserts existence and uniqueness without naming the witness. -/
theorem theorem_36_5_unique (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun (Rn m) (Rn n),
      ConvexBifun G ∧ ClosedBifun G ∧ saddleLagrangian (pairing m) G = L :=
  exists_unique_closedBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc

end Thm365

/-! ### The Kuhn–Tucker condition, and Theorem 36.6 -/

section Thm366

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- `(0, 0) ∈ ∂K (u, v)` if and only if `(u, v)` is a saddle-point of `K`: the concave slice
attains its maximum at `u` and the convex slice its minimum at `v`. No hypothesis is needed. -/
theorem zero_mem_saddleSubdifferential_iff_isSaddlePoint (K : Rn m × Rn n → EReal)
    (p : Rn m × Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n) K p ↔ IsSaddlePoint K p := by
  rw [mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]

/-- The **Kuhn–Tucker condition for `(P)`**: for a closed proper convex bifunction `F`,
`(0, 0) ∈ ∂L (ū*, x̄)` holds exactly when `ū*` is a Kuhn–Tucker vector for `(P)` and `x̄` is an
optimal solution. -/
theorem kuhnTucker_condition_iff (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (v : Rn m) (x : Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [zero_mem_saddleSubdifferential_iff_isSaddlePoint]
  exact theorem_29_3_isSaddlePoint hF hcl hpr

/-- **Theorem 36.6**, the **strongly consistent** case: for `(P)` associated with a closed proper
convex bifunction and strongly consistent, `x̄` is optimal if and only if `(0, 0) ∈ ∂L (ū*, x̄)` for
some `ū*`. The book prints no proof; this is the Kuhn–Tucker theorem, Corollary 29.3.1. -/
theorem theorem_36_6_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_stronglyConsistent hF hcl hpr hs]
  exact exists_congr fun v =>
    (zero_mem_saddleSubdifferential_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Theorem 36.6**, the **strictly consistent** case, which is strongly consistent. -/
theorem theorem_36_6_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) :=
  theorem_36_6_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Theorem 36.6**, the **polyhedral** case: plain consistency suffices, Theorem 29.2 supplying
a Kuhn–Tucker vector with no interiority hypothesis. -/
theorem theorem_36_6_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_polyhedral hF hcl hpr hc]
  exact exists_congr fun v =>
    (zero_mem_saddleSubdifferential_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Theorem 36.6**, last sentence: for a given optimal `x̄`, the `ū*` satisfying the Kuhn–Tucker
condition are precisely the Kuhn–Tucker vectors for `(P)`. No constraint qualification is used. -/
theorem theorem_36_6_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hx : IsOptimalSolution F x) (v : Rn m) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F := by
  rw [kuhnTucker_condition_iff hF hcl hpr]
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

end Thm366

end Rockafellar
