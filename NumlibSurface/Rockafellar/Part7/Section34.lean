import NumlibSurface.Common.Euclidean
import NumlibSurface.Rockafellar.Part7.Section33

/-!
# Rockafellar, §34: Closures and Equivalence Classes

The lower and upper closures `cl₂ cl₁ K` and `cl₁ cl₂ K`, the effective domain `dom K`,
equivalence and closedness of saddle-functions, the class `Ω (F)`, the kernel, and simple
saddle-functions. All ten numbered results of §34 are formalized: Theorems 34.1–34.5 (34.3 in six
clauses (a)–(f)), Corollaries 34.2.1–34.2.4 and Corollary 34.5.1.

The orientation convention for `cl₁` and `cl₂` is stated in `Part7/Section33.lean` and used here
unchanged; `lowerCl K = cl₂ (cl₁ K)` and `upperCl K = cl₁ (cl₂ K)`.

Theorem 34.2 is stated before Theorem 34.1 because it licenses the reading everything downstream
uses: the natural primitive is not a saddle-function but a closed convex bifunction `F`, whose
order interval `Ω (F) = {K | K̲ ≤ K ≤ K̄}` is exactly one equivalence class of closed
concave-convex functions. Theorem 34.1 then says the two closures always land on such a pair.

## Divergences from the book

Theorem 34.2's `dom K = dom F × dom F*` is a product identity and only that: the book argues the
two factors separately, and that step fails for improper `F` — with graph function `≡ +∞`,
`dom₁ K = ∅ = dom F` but `dom₂ K = ℝⁿ` while `dom F* = ∅`, and both products are empty. So
`theorem_34_2_dom₁` and `theorem_34_2_dom₂` carry a nonemptiness hypothesis the book suppresses.
Theorem 34.1 is proved with no hypothesis at all, stronger than the book's statement, and
Corollary 34.2.4 asks only for separate continuity of the slices where the book asks for joint.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §34, pp. 359–369.
-/

namespace Rockafellar

open ConvexAnalysis NumlibSurface

/-! ### The vocabulary of §34 -/

section Vocabulary

variable {m n : ℕ}

/-- Rockafellar's `dom₁ K = {u | K (u, v) > −∞, ∀ v}`. -/
theorem dom₁_eq (K : Rn m × Rn n → EReal) : dom₁ K = {u | ∀ v, ⊥ < K (u, v)} := rfl

/-- Rockafellar's `dom₂ K = {v | K (u, v) < +∞, ∀ u}`. -/
theorem dom₂_eq (K : Rn m × Rn n → EReal) : dom₂ K = {v | ∀ u, K (u, v) < ⊤} := rfl

/-- Rockafellar's `dom K = dom₁ K × dom₂ K`, the effective domain of a saddle-function. -/
theorem domSaddle_eq (K : Rn m × Rn n → EReal) : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl

/-- `K` is **proper** when `dom K ≠ ∅`. -/
theorem properSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ProperSaddleFn K ↔ (domSaddle K).Nonempty :=
  properSaddleFn_iff_domSaddle_nonempty

/-- On `dom K` a saddle-function is finite. -/
theorem lt_top_of_mem_domSaddle' {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}
    (hp : p ∈ domSaddle K) : ⊥ < K p ∧ K p < ⊤ :=
  ⟨bot_lt_of_mem_domSaddle hp, lt_top_of_mem_domSaddle hp⟩

variable {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- The lower simple extension of a finite saddle-function on a nonempty `C × D` has
`dom K = C × D`, and is proper. -/
theorem domSaddle_lowerSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (lowerSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (lowerSimpleExt C D K)
      = dom₁ (lowerSimpleExt C D K) ×ˢ dom₂ (lowerSimpleExt C D K) := rfl
  rw [h, dom₁_lowerSimpleExt hDne, dom₂_lowerSimpleExt hCne]

/-- The upper simple extension likewise. -/
theorem domSaddle_upperSimpleExt (hCne : C.Nonempty) (hDne : D.Nonempty) :
    domSaddle (upperSimpleExt C D K) = C ×ˢ D := by
  have h : domSaddle (upperSimpleExt C D K)
      = dom₁ (upperSimpleExt C D K) ×ˢ dom₂ (upperSimpleExt C D K) := rfl
  rw [h, dom₁_upperSimpleExt hDne, dom₂_upperSimpleExt hCne]

/-- Rockafellar's **equivalent**: `cl₁ K = cl₁ L` and `cl₂ K = cl₂ L`. -/
theorem saddleEquiv_iff (K L : Rn m × Rn n → EReal) :
    SaddleEquiv K L ↔ cl₁ K = cl₁ L ∧ cl₂ K = cl₂ L := Iff.rfl

/-- Rockafellar's **closed**: `cl₁ cl₂ K = cl₁ K` and `cl₂ cl₁ K = cl₂ K`. The book defines it as
"`cl₁ K` and `cl₂ K` are both equivalent to `K`", then reduces that to these two equations. -/
theorem closedSaddleFn_iff (K : Rn m × Rn n → EReal) :
    ClosedSaddleFn K ↔ cl₁ (cl₂ K) = cl₁ K ∧ cl₂ (cl₁ K) = cl₂ K := Iff.rfl

end Vocabulary

/-! ### Theorem 34.2 -/

section Thm342

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- Rockafellar's `Ω (F)`: for a closed convex bifunction `F`, the collection of all
**concave-convex** `K` with `⟨Fu, x*⟩ ≤ K (u, x*) ≤ ⟨u, F*x*⟩`. The concave-convexity is part of
the book's definition; the backbone's `bifunSaddleClass` is the same interval without it. -/
noncomputable def Ω (F : Bifun (Rn m) (Rn n)) : Set (Rn m × Rn n → EReal) :=
  {K | ConcaveConvexFn K} ∩ saddleClass (bifunBracket F) (adjointBracket F)

theorem mem_Ω : K ∈ Ω F ↔ ConcaveConvexFn K ∧ bifunBracket F ≤ K ∧ K ≤ adjointBracket F :=
  Iff.rfl

/-- The bridge from `Ω (F)` to the backbone's order interval, which is what §37's statements about
a class are phrased against. -/
theorem mem_bifunSaddleClass_of_mem_Ω (hK : K ∈ Ω F) :
    K ∈ bifunSaddleClass (pairing m) (pairing n) F := hK.2

/-- **Theorem 34.2**: `K̲ (u, x*) = ⟨Fu, x*⟩` belongs to `Ω (F)`. -/
theorem theorem_34_2_lower_mem (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    bifunBracket F ∈ Ω F :=
  ⟨theorem_33_1_concaveConvex hF,
    mem_saddleClass_left (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Theorem 34.2**: `K̄ (u, x*) = ⟨u, F*x*⟩` belongs to `Ω (F)`. -/
theorem theorem_34_2_upper_mem (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    adjointBracket F ∈ Ω F :=
  ⟨adjointBracket_concaveConvex F,
    mem_saddleClass_right (corollary_33_3_1_necessity_second hF hcl)⟩

/-- **Theorem 34.2**, second equation: `cl₂ K = K̲` for every `K ∈ Ω (F)`. -/
theorem theorem_34_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₂ K = bifunBracket F :=
  partialCl₂_eq_bracket_of_mem_saddleClass (pairing m) (pairing n) hF hcl hK.2

/-- **Theorem 34.2**, first equation: `cl₁ K = K̄` for every `K ∈ Ω (F)`, with no closedness of
`F` needed. -/
theorem theorem_34_2_cl₁ (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    cl₁ K = adjointBracket F :=
  partialCl₁_eq_concaveBracket_of_mem_saddleClass (pairing m) (pairing n) hF hK.2

/-- **Theorem 34.2**: every member of `Ω (F)` is a closed saddle-function. -/
theorem theorem_34_2_closed (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn K :=
  closedSaddleFn_of_mem_saddleClass_bracket (pairing m) (pairing n) hF hcl hK.2

/-- **Theorem 34.2**: any two members of `Ω (F)` are equivalent. -/
theorem theorem_34_2_equiv (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : SaddleEquiv K L :=
  saddleEquiv_of_mem_saddleClass (corollary_33_3_1_necessity_first hF)
    (corollary_33_3_1_necessity_second hF hcl) hK.2 hL.2

/-- **Theorem 34.2**: `Ω (F)` is a *whole* equivalence class — a concave-convex function
equivalent to a member is itself a member. -/
theorem theorem_34_2_maximal (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : L ∈ Ω F := by
  refine ⟨hL, ?_⟩
  have e2 : partialCl₂ L = bifunBracket F := by
    have hK2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
    rw [← h.2]; exact hK2
  have e1 : partialCl₁ L = adjointBracket F := by
    have hK1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
    rw [← h.1]; exact hK1
  have hmem := mem_saddleClass_self L
  rw [e1, e2] at hmem
  exact hmem

/-- **Theorem 34.2**, converse: a closed concave-convex function determines one and only one
closed convex bifunction whose two brackets are `cl₂ K` and `cl₁ K`. -/
theorem theorem_34_2_converse (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K) :
    ∃! F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧
      bifunBracket F = cl₂ K ∧ adjointBracket F = cl₁ K :=
  exists_unique_bifun_of_closedSaddleFn (pairing m) (pairing n) hK hcl

/-- **Theorem 34.2**, converse: and `K` lies in the class of that bifunction, so every equivalence
class of closed concave-convex functions is an `Ω (F)`. -/
theorem theorem_34_2_mem_self (hK : ConcaveConvexFn K) (hlow : bifunBracket F = cl₂ K)
    (hup : adjointBracket F = cl₁ K) : K ∈ Ω F := by
  refine ⟨hK, ?_⟩
  have e2 : partialCl₂ K = bifunBracket F := hlow.symm
  have e1 : partialCl₁ K = adjointBracket F := hup.symm
  have hmem := mem_saddleClass_self K
  rw [e1, e2] at hmem
  exact hmem

/-- **Theorem 34.2**, `dom` clause, first factor: `dom₁ K = dom F` for `K ∈ Ω (F)`. The
nonemptiness hypothesis is not in the book and cannot be dropped; see the module docstring. -/
theorem theorem_34_2_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hne : (dom₂ K).Nonempty) : dom₁ K = domBifun F :=
  dom₁_eq_domBifun_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl hK.2 hK.1 hne

private theorem dom₂_adjointBracket (F : Bifun (Rn m) (Rn n)) :
    dom₂ (adjointBracket F) = domConcaveBifun (dualProgram F) := by
  ext y
  constructor
  · intro hy
    have h : y ∈ dom fun w => concaveBracket (pairing m) (dualProgram F) (0 : Rn m) w := hy 0
    rwa [dom_concaveBracket] at h
  · intro hy u
    have h : y ∈ dom fun w => concaveBracket (pairing m) (dualProgram F) u w := by
      rw [dom_concaveBracket]; exact hy
    exact h

/-- **Theorem 34.2**, `dom` clause, second factor: `dom₂ K = dom F*` for `K ∈ Ω (F)`, again with a
nonemptiness hypothesis the book suppresses. -/
theorem theorem_34_2_dom₂ (hF : ConvexBifun F) (hK : K ∈ Ω F) (hne : (dom₁ K).Nonempty) :
    dom₂ K = domConcaveBifun (dualProgram F) := by
  have e1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  rw [← dom₂_partialCl₁ hK.1 hne, e1, dom₂_adjointBracket]

/-- **Theorem 34.2**: `dom K = dom F × dom F*`. -/
theorem theorem_34_2_dom (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) :
    domSaddle K = domBifun F ×ˢ domConcaveBifun (dualProgram F) := by
  have h : domSaddle K = dom₁ K ×ˢ dom₂ K := rfl
  rw [h, theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty,
    theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]

/-- **Theorem 34.2**: `F` is recovered from any `K ∈ Ω (F)` as `Fu = K (u, ·)*`. -/
theorem theorem_34_2_bifunOfSaddleFn (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    bifunOfSaddleFn K = F := by
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  refine eq_of_bracket_eq (Bx := pairing n) (theorem_33_1_convexBifun hK.1) hF
    (theorem_33_1_imageClosed K) (imageClosedBifun_of_closedBifun hcl) ?_
  funext u x
  calc bracket (pairing n) (bifunOfSaddleFn K) u x
      = partialCl₂ K (u, x) := bracket_bifunOfSaddle hK.1 (u, x)
    _ = bracket (pairing n) F u x := congrFun h2 (u, x)

/-- **Theorem 34.2**, third equation: `(Fu)(x) = sup_{x*} {⟨x, x*⟩ − K (u, x*)}`. -/
theorem theorem_34_2_bifun_apply (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (u : Rn m) (x : Rn n) :
    F u x = ⨆ y : Rn n, ((pairing n x y : ℝ) : EReal) - K (u, y) := by
  rw [← theorem_34_2_bifunOfSaddleFn hF hcl hK]
  exact bifunOfSaddleFn_apply K u x

private theorem concaveConj_clConcave (g : Rn m → EReal) :
    concaveConj (pairing m) (clConcave g) = concaveConj (pairing m) g := by
  funext y
  rw [concaveConj_eq_neg_conj_neg, concaveConj_eq_neg_conj_neg]
  have h : (fun x => -(clConcave g x)) = clFn fun z => -(g z) := funext (neg_clConcave g)
  rw [h, conj_clFn]

/-- **Theorem 34.2**, fourth equation: `(F*x*)(u*) = inf_u {⟨u, u*⟩ − K (u, x*)}`. The book writes
this off the third by symmetry, but it is not symmetric: `F* x*` is the *concave* conjugate of
`u ↦ (cl₂ K) (u, x*)`, and replacing `cl₂ K` by `K` under it is what closedness of `K` buys. -/
theorem theorem_34_2_adjoint (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (x : Rn n) (v : Rn m) :
    dualProgram F x v = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have hfun : (fun u => bracket (pairing n) F u x) = fun u => partialCl₂ K (u, x) := by
    funext u
    exact (congrFun h2 (u, x)).symm
  have hclc : clConcave (fun u => partialCl₂ K (u, x)) = clConcave fun u => K (u, x) := by
    rw [← partialCl₁_slice (partialCl₂ K) x, ← partialCl₁_slice K x, hcls.1]
  have hgoal : adjointBifun (pairing m) (pairing n) F x v
      = ⨅ u : Rn m, ((pairing m u v : ℝ) : EReal) - K (u, x) := by
    rw [adjointBifun_eq_concaveConj_bracket (pairing m) (pairing n) F x v, hfun,
      ← concaveConj_clConcave (fun u => partialCl₂ K (u, x)), hclc, concaveConj_clConcave,
      concaveConj_apply]
  exact hgoal

/-- **Theorem 34.2**, last clause: `K (u, x*) = ⟨Fu, x*⟩ = ⟨u, F*x*⟩` when `u ∈ ri (dom F)`. -/
theorem theorem_34_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (domBifun F)) (x : Rn n) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hu' : u ∈ ri (dom₁ K) := by
    rw [theorem_34_2_dom₁ hF hcl hK hp.dom₂_nonempty]; exact hu
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₁ hK.1 hp hu' x]
  exact congrFun h1 (u, x)

/-- **Theorem 34.2**, last clause, second half: the same when `x* ∈ ri (dom F*)`. -/
theorem theorem_34_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {x : Rn n}
    (hx : x ∈ ri (domConcaveBifun (dualProgram F))) (u : Rn m) :
    K (u, x) = bifunBracket F (u, x) ∧ K (u, x) = adjointBracket F (u, x) := by
  have hcls : ClosedSaddleFn K := theorem_34_2_closed hF hcl hK
  have h2 : partialCl₂ K = bifunBracket F := theorem_34_2_cl₂ hF hcl hK
  have h1 : partialCl₁ K = adjointBracket F := theorem_34_2_cl₁ hF hK
  have hx' : x ∈ ri (dom₂ K) := by
    rw [theorem_34_2_dom₂ hF hK hp.dom₁_nonempty]; exact hx
  have heq := hcls.eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u
  refine ⟨heq.trans (congrFun h2 (u, x)), ?_⟩
  rw [heq, ← hcls.partialCl₁_eq_partialCl₂_of_mem_relint_dom₂ hK.1 hp hx' u]
  exact congrFun h1 (u, x)

end Thm342

/-! ### Theorem 34.1

The two closure operations always land on a closure pair, hence on an `Ω (F)`. -/

section Thm341

variable {m n : ℕ}

/-- **Theorem 34.1**: the lower closure `cl₂ cl₁ K` is lower closed. Proved here from monotonicity
and idempotence of the two closures, so it needs **no hypothesis at all** — not concave-convexity,
not properness — which is strictly stronger than the book's statement. -/
theorem theorem_34_1_lower (K : Rn m × Rn n → EReal) : LowerClosedFn (lowerCl K) :=
  lowerCl_idem K

/-- **Theorem 34.1**: the upper closure `cl₁ cl₂ K` is upper closed, again with no hypothesis. -/
theorem theorem_34_1_upper (K : Rn m × Rn n → EReal) : UpperClosedFn (upperCl K) :=
  upperCl_idem K

/-- **Theorem 34.1**, first displayed equation: `cl₂ cl₁ cl₂ cl₁ K = cl₂ cl₁ K`. -/
theorem theorem_34_1_lower_eq (K : Rn m × Rn n → EReal) :
    cl₂ (cl₁ (cl₂ (cl₁ K))) = cl₂ (cl₁ K) := by
  have h : partialCl₂ (partialCl₁ (partialCl₂ (partialCl₁ K))) = partialCl₂ (partialCl₁ K) :=
    lowerCl_idem K
  exact h

/-- **Theorem 34.1**, second displayed equation: `cl₁ cl₂ cl₁ cl₂ K = cl₁ cl₂ K`. -/
theorem theorem_34_1_upper_eq (K : Rn m × Rn n → EReal) :
    cl₁ (cl₂ (cl₁ (cl₂ K))) = cl₁ (cl₂ K) := by
  have h : partialCl₁ (partialCl₂ (partialCl₁ (partialCl₂ K))) = partialCl₁ (partialCl₂ K) :=
    upperCl_idem K
  exact h

end Thm341

/-! ### Corollary 34.2.1 -/

section Cor3421

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.1**, first clause: equivalent saddle-functions have the same effective
domain. -/
theorem corollary_34_2_1_dom (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    domSaddle L = domSaddle K :=
  (h.domSaddle_eq hK hpK hL hpL).symm

/-- **Corollary 34.2.1**: the `dom L = dom K` clause needs **no closedness**, which the book's
blanket hypothesis "`K` closed" suggests it does. `dom₁` is already `dom₁ (cl₂ ·)` and `dom₂`
already `dom₂ (cl₁ ·)`, so equivalence alone settles both factors. -/
theorem corollary_34_2_1_dom_of_not_closed (h : SaddleEquiv K L) (hK : ConcaveConvexFn K)
    (hpK : ProperSaddleFn K) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    dom₁ L = dom₁ K ∧ dom₂ L = dom₂ K :=
  ⟨(h.dom₁_eq hK hpK hL hpL).symm, (h.dom₂_eq hK hpK hL hpL).symm⟩

/-- **Corollary 34.2.1**, second clause: `L (u, v) = K (u, v)` whenever `u ∈ ri (dom₁ K)`. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₁ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {u : Rn m} (hu : u ∈ ri (dom₁ K))
    (v : Rn n) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₁ hclK hK hpK hclL hL hpL hu v).symm

/-- **Corollary 34.2.1**, second clause: `L (u, v) = K (u, v)` whenever `v ∈ ri (dom₂ K)`. -/
theorem corollary_34_2_1_eq_of_mem_relint_dom₂ (h : SaddleEquiv K L) (hclK : ClosedSaddleFn K)
    (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K) (hclL : ClosedSaddleFn L)
    (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) {v : Rn n} (hv : v ∈ ri (dom₂ K))
    (u : Rn m) : L (u, v) = K (u, v) :=
  (h.eq_of_mem_relint_dom₂ hclK hK hpK hclL hL hpL hv u).symm

end Cor3421

/-! ### Corollary 34.2.2 -/

section Cor3422

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.2**: a lower closed saddle-function is closed. -/
theorem corollary_34_2_2_of_lowerClosed (h : LowerClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Corollary 34.2.2**: an upper closed saddle-function is closed. -/
theorem corollary_34_2_2_of_upperClosed (h : UpperClosedFn K) : ClosedSaddleFn K :=
  h.closedSaddleFn

/-- **Corollary 34.2.2**: a fully closed saddle-function is closed. -/
theorem corollary_34_2_2_of_fullyClosed (h : FullyClosedFn K) : ClosedSaddleFn K :=
  (fullyClosedFn_iff.1 h).1.closedSaddleFn

/-- **Corollary 34.2.2**: the class of a closed saddle-function has a lower closed member,
`cl₂ K`. -/
theorem corollary_34_2_2_lower_exists (hcl : ClosedSaddleFn K) : LowerClosedFn (cl₂ K) :=
  hcl.lowerClosedFn_partialCl₂

/-- **Corollary 34.2.2**: and an upper closed member of that class, `cl₁ K`. -/
theorem corollary_34_2_2_upper_exists (hcl : ClosedSaddleFn K) : UpperClosedFn (cl₁ K) :=
  hcl.upperClosedFn_partialCl₁

/-- **Corollary 34.2.2**: a lower closed member of the class of `K` is `cl₂ K`. -/
theorem corollary_34_2_2_lower_unique (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L = cl₂ K :=
  h.eq_partialCl₂_of_lowerClosedFn hL

/-- **Corollary 34.2.2**: an upper closed member of the class of `K` is `cl₁ K`. -/
theorem corollary_34_2_2_upper_unique (h : SaddleEquiv K L) (hL : UpperClosedFn L) : L = cl₁ K :=
  h.eq_partialCl₁_of_upperClosedFn hL

/-- **Corollary 34.2.2**: the lower closed member is the **least** member of the class. -/
theorem corollary_34_2_2_least (h : SaddleEquiv K L) (hL : LowerClosedFn L) : L ≤ K := by
  have e : L = partialCl₂ K := h.eq_partialCl₂_of_lowerClosedFn hL
  rw [e]
  exact partialCl₂_le K

/-- **Corollary 34.2.2**: the upper closed member is the **greatest** member. -/
theorem corollary_34_2_2_greatest (h : SaddleEquiv K L) (hL : UpperClosedFn L) : K ≤ L := by
  have e : L = partialCl₁ K := h.eq_partialCl₁_of_upperClosedFn hL
  rw [e]
  exact le_partialCl₁ K

end Cor3422

/-! ### Corollary 34.2.3 -/

section Cor3423

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Corollary 34.2.3**: the only improper closed saddle-functions on `ℝᵐ × ℝⁿ` are the two
constants `−∞` and `+∞`. -/
theorem corollary_34_2_3 (hcl : ClosedSaddleFn K) (hp : ¬ ProperSaddleFn K) :
    K = (fun _ => (⊥ : EReal)) ∨ K = fun _ => (⊤ : EReal) :=
  hcl.eq_const_of_not_properSaddleFn hp

/-- **Corollary 34.2.3**: and the two constants are **not** equivalent. -/
theorem corollary_34_2_3_not_equiv :
    ¬ SaddleEquiv (fun _ : Rn m × Rn n => (⊥ : EReal)) (fun _ => (⊤ : EReal)) :=
  not_saddleEquiv_const_bot_const_top

end Cor3423

/-! ### Corollary 34.2.4

The `+∞`/`−∞` pattern is orientation-sensitive: `+∞` where `u ∈ C` and `v ∉ D`, `−∞` where
`u ∉ C` and `v ∈ D`. It is the opposite of what a convex-concave convention would give. -/

section Cor3424

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
  {L : Rn m × Rn n → EReal}

/-- **Corollary 34.2.4**: the class of the corollary — the extensions of `K` by `+∞` on `C × Dᶜ`
and `−∞` on `Cᶜ × D` — is exactly the order interval between the two simple extensions. The values
on `Cᶜ × Dᶜ` are unconstrained. Stated without the concave-convexity the book's `Ω` also asks
for. -/
theorem corollary_34_2_4_mem_iff :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      (∀ u ∈ C, ∀ v ∈ D, L (u, v) = (K (u, v) : EReal)) ∧
        (∀ u ∈ C, ∀ v ∉ D, L (u, v) = ⊤) ∧ ∀ u ∉ C, ∀ v ∈ D, L (u, v) = ⊥ :=
  mem_saddleClass_simpleExt_iff

/-- **Corollary 34.2.4**: every member of the class is a closed saddle-function. -/
theorem corollary_34_2_4_closed (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_simpleExt hCcl hDcl hCne hDne hcontD hcontC hL

/-- **Corollary 34.2.4**: every member of the class is proper. -/
theorem corollary_34_2_4_proper (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hL : L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_simpleExt hCne hDne hL

/-- **Corollary 34.2.4**: the class is precisely one equivalence class. -/
theorem corollary_34_2_4_equiv (hCcl : IsClosed C) (hDcl : IsClosed D) (hCne : C.Nonempty)
    (hDne : D.Nonempty) (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C) :
    L ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) ↔
      SaddleEquiv (lowerSimpleExt C D K) L :=
  mem_saddleClass_simpleExt_iff_saddleEquiv hCcl hDcl hCne hDne hcontD hcontC

/-- **Corollary 34.2.4**: the lower simple extension is the **least** member. -/
theorem corollary_34_2_4_least (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    lowerSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_left (partialCl₂_upperSimpleExt hDcl hDne hcontD)

/-- **Corollary 34.2.4**: the upper simple extension is the **greatest** member. -/
theorem corollary_34_2_4_greatest (hDcl : IsClosed D) (hDne : D.Nonempty)
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D) :
    upperSimpleExt C D K ∈ saddleClass (lowerSimpleExt C D K) (upperSimpleExt C D K) :=
  mem_saddleClass_right (partialCl₂_upperSimpleExt hDcl hDne hcontD)

end Cor3424

/-! ### Theorem 34.3

Six clauses, one declaration each, in the necessity direction; the sufficiency direction needs all
six at once and is `theorem_34_3`. Throughout, `C = dom₁ K` and `D = dom₂ K`. -/

section Thm343

variable {m n : ℕ} {K : Rn m × Rn n → EReal}

/-- **Theorem 34.3 (a)**. For `u ∈ ri C` the convex function `K (u, ·)` is closed proper with
effective domain `D`. -/
theorem theorem_34_3_a (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ ClosedFn (fun v => K (u, v)) ∧
      Proper (fun v => K (u, v)) ∧ dom (fun v => K (u, v)) = dom₂ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.closedFn_slice u hu,
    hs.1.proper_slice u (intrinsicInterior_subset hu), hs.1.dom_slice u hu⟩

/-- **Theorem 34.3 (b)**. For `u ∈ C ∖ ri C` the convex function `K (u, ·)` is proper and its
effective domain lies between `D` and `cl D`. The lower inclusion holds for every `u` whatsoever;
only the upper one uses the structure. -/
theorem theorem_34_3_b (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∈ dom₁ K \ ri (dom₁ K)) :
    ConvexFn (fun v => K (u, v)) ∧ Proper (fun v => K (u, v)) ∧
      dom₂ K ⊆ dom (fun v => K (u, v)) ∧
      dom (fun v => K (u, v)) ⊆ closure (dom₂ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.convex_snd u, hs.1.proper_slice u hu.1, dom₂_subset_dom_slice K u,
    hs.1.dom_slice_subset_closure u hu.1⟩

/-- **Theorem 34.3 (c)**. For `u ∉ C` the convex function `K (u, ·)` is improper, with value `−∞`
throughout `ri D` — throughout `D` itself if `u ∉ cl C`. -/
theorem theorem_34_3_c (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {u : Rn m} (hu : u ∉ dom₁ K) :
    ¬ Proper (fun v => K (u, v)) ∧ (∀ v ∈ ri (dom₂ K), K (u, v) = ⊥) ∧
      (u ∉ closure (dom₁ K) → ∀ v ∈ dom₂ K, K (u, v) = ⊥) := by
  have hs := hcl.saddleStructure hK hp
  have hbot : ∀ v ∈ ri (dom₂ K), K (u, v) = ⊥ := hs.1.eq_bot_of_notMem_dom₁ u hu
  refine ⟨?_, hbot, fun hu' => hs.1.eq_bot_of_notMem_closure_dom₁ u hu'⟩
  obtain ⟨v₀, hv₀⟩ := hp.relint_dom₂_nonempty hK
  exact fun hpr => hpr.ne_bot v₀ (hbot v₀ hv₀)

/-- **Theorem 34.3 (d)**. For `v ∈ ri D` the concave function `K (·, v)` is closed proper with
effective domain `C`. -/
theorem theorem_34_3_d (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ClosedConcaveFn (fun u => K (u, v)) ∧
      ProperConcave (fun u => K (u, v)) ∧ domConcave (fun u => K (u, v)) = dom₁ K := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.closedConcaveFn_slice hv,
    hs.properConcave_slice (intrinsicInterior_subset hv), hs.domConcave_slice hv⟩

/-- **Theorem 34.3 (e)**. For `v ∈ D ∖ ri D` the concave function `K (·, v)` is proper and its
effective domain lies between `C` and `cl C`. -/
theorem theorem_34_3_e (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∈ dom₂ K \ ri (dom₂ K)) :
    ConcaveFn (fun u => K (u, v)) ∧ ProperConcave (fun u => K (u, v)) ∧
      dom₁ K ⊆ domConcave (fun u => K (u, v)) ∧
      domConcave (fun u => K (u, v)) ⊆ closure (dom₁ K) := by
  have hs := hcl.saddleStructure hK hp
  exact ⟨hK.concave_fst v, hs.properConcave_slice hv.1, dom₁_subset_domConcave_slice K v,
    hs.domConcave_slice_subset_closure hv.1⟩

/-- **Theorem 34.3 (f)**. For `v ∉ D` the concave function `K (·, v)` is improper, with value `+∞`
throughout `ri C` — throughout `C` itself if `v ∉ cl D`. -/
theorem theorem_34_3_f (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    {v : Rn n} (hv : v ∉ dom₂ K) :
    ¬ ProperConcave (fun u => K (u, v)) ∧ (∀ u ∈ ri (dom₁ K), K (u, v) = ⊤) ∧
      (v ∉ closure (dom₂ K) → ∀ u ∈ dom₁ K, K (u, v) = ⊤) := by
  have hs := hcl.saddleStructure hK hp
  have htop : ∀ u ∈ ri (dom₁ K), K (u, v) = ⊤ := fun _u hu => hs.eq_top_of_notMem_dom₂ hv hu
  refine ⟨?_, htop, fun hv' _u hu => hs.eq_top_of_notMem_closure_dom₂ hv' hu⟩
  obtain ⟨u₀, hu₀⟩ := hp.relint_dom₁_nonempty hK
  exact fun hpr => hpr.ne_top u₀ (htop u₀ hu₀)

/-- **Theorem 34.3.** A proper concave-convex function is closed **if and only if** it has the six
properties (a)–(f), bundled as `SaddleStructure`: (a)–(c) for `K` together with (a)–(c) for
`saddleSwap K`, which is what (d)–(f) are. -/
theorem theorem_34_3 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) :
    ClosedSaddleFn K ↔ SaddleStructure K :=
  closedSaddleFn_iff_saddleStructure hK hp

end Thm343

/-! ### The kernel and simple saddle-functions -/

section Kernel

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- `ri (dom K) = ri (dom₁ K) × ri (dom₂ K)`, the rectangle the kernel lives on. -/
theorem relint_domSaddle_eq_prod (K : Rn m × Rn n → EReal) :
    ri (domSaddle K) = ri (dom₁ K) ×ˢ ri (dom₂ K) :=
  relint_domSaddle K

/-- The **kernel** of `K`: its restriction to `ri (dom K)`. Rockafellar's kernel is a partial
function on a rectangle that moves with `K`; here it is extended by `+∞` off the rectangle, so that
`kernel K = kernel L` is one equation rather than a rectangle equality plus a transport. -/
theorem kernel_eq_restrictFn (K : Rn m × Rn n → EReal) :
    kernel K = ConvexAnalysis.restrictFn (ri (domSaddle K)) K := by
  have h : kernel K = ConvexAnalysis.restrictFn (kernelSet K) K := rfl
  rw [h, kernelSet_eq_relint_domSaddle]

/-- Equality of kernels unpacked into the book's two facts: the same rectangle, same values. -/
theorem kernel_eq_iff' :
    kernel K = kernel L ↔ kernelSet K = kernelSet L ∧ Set.EqOn K L (kernelSet K) :=
  kernel_eq_iff

/-- Rockafellar's **simple**: over `ri (dom₁ K)` the convex slices stay inside `cl (dom₂ K)`, and
over `ri (dom₂ K)` the concave slices stay inside `cl (dom₁ K)`. -/
theorem simpleSaddleFn_iff (K : Rn m × Rn n → EReal) :
    SimpleSaddleFn K ↔
      ((∀ u ∈ ri (dom₁ K), dom (fun v => K (u, v)) ⊆ closure (dom₂ K)) ∧
        ∀ v ∈ ri (dom₂ K), domConcave (fun u => K (u, v)) ⊆ closure (dom₁ K)) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Every closed proper saddle-function is simple: clauses (b) and (e) of Theorem 34.3. -/
theorem simpleSaddleFn_of_closed (hcl : ClosedSaddleFn K) (hK : ConcaveConvexFn K)
    (hp : ProperSaddleFn K) : SimpleSaddleFn K :=
  hcl.simpleSaddleFn hK hp

/-- The two simple extensions of a finite saddle-function on a nonempty `C × D` are simple. -/
theorem simpleSaddleFn_lowerSimpleExt' {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    SimpleSaddleFn (lowerSimpleExt C D K) ∧ SimpleSaddleFn (upperSimpleExt C D K) := by
  refine ⟨simpleSaddleFn_lowerSimpleExt hCne hDne, ?_⟩
  rw [upperSimpleExt_eq_saddleSwap]
  exact simpleSaddleFn_saddleSwap_iff.2 (simpleSaddleFn_lowerSimpleExt hDne hCne)

/-- Every saddle-function of the form `K (u, x*) = ⟨Fu, x*⟩` is simple, Rockafellar's exercise.
Stated here for `F` **closed** and `K` **proper**, where the book asks only that `F` be a convex or
concave bifunction: closedness makes `K` closed (Theorem 33.3) and properness lets Theorem 34.3
apply. Whether the unrestricted claim holds is not settled here. -/
theorem simpleSaddleFn_bifunBracket {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedBifun F) (hp : ProperSaddleFn (bifunBracket F)) :
    SimpleSaddleFn (bifunBracket F) :=
  (theorem_34_2_closed hF hcl (theorem_34_2_lower_mem hF hcl)).simpleSaddleFn
    (theorem_33_1_concaveConvex hF) hp

end Kernel

/-! ### Theorem 34.4 -/

section Thm344

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Theorem 34.4.** Two closed proper concave-convex functions on `ℝᵐ × ℝⁿ` are equivalent **if
and only if** they have the same kernel. -/
theorem theorem_34_4 (hclK : ClosedSaddleFn K) (hK : ConcaveConvexFn K) (hpK : ProperSaddleFn K)
    (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L) (hpL : ProperSaddleFn L) :
    SaddleEquiv K L ↔ kernel K = kernel L :=
  saddleEquiv_iff_kernel_eq hclK hK hpK hclL hL hpL

end Thm344

/-! ### Theorem 34.5 and Corollary 34.5.1 -/

section Thm345

variable {m n : ℕ} {K L : Rn m × Rn n → EReal}

/-- **Theorem 34.5**: `cl₂ cl₁ K ≤ cl₁ cl₂ K` for a simple proper concave-convex `K`. -/
theorem theorem_34_5_le (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : lowerCl K ≤ upperCl K :=
  lowerCl_le_upperCl hK hp hs

/-- **Theorem 34.5**: the lower and upper closures of such a `K` are **equivalent**. -/
theorem theorem_34_5_equiv (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) : SaddleEquiv (lowerCl K) (upperCl K) :=
  saddleEquiv_lowerCl_upperCl hK hp hs

/-- **Theorem 34.5**: every saddle-function between the two closures is closed. -/
theorem theorem_34_5_closed (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ClosedSaddleFn L :=
  closedSaddleFn_of_mem_saddleClass_lowerCl hK hp hs hL

/-- **Theorem 34.5**: every saddle-function between the two closures is proper. -/
theorem theorem_34_5_proper (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hL : L ∈ saddleClass (lowerCl K) (upperCl K)) : ProperSaddleFn L :=
  properSaddleFn_of_mem_saddleClass_lowerCl hK hp hL

/-- **Theorem 34.5**: every concave-convex function between the two closures has the same kernel
as `K`. -/
theorem theorem_34_5_kernel (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hL : ConcaveConvexFn L)
    (hmem : L ∈ saddleClass (lowerCl K) (upperCl K)) : kernel L = kernel K :=
  kernel_of_mem_saddleClass_lowerCl hK hp hs hL hmem

/-- **Theorem 34.5**, converse half: a closed proper concave-convex function with the same kernel
as `K` lies between the two closures, so the interval is the *whole* class. -/
theorem theorem_34_5_mem_of_kernel_eq (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hs : SimpleSaddleFn K) (hclL : ClosedSaddleFn L) (hL : ConcaveConvexFn L)
    (hpL : ProperSaddleFn L) (hker : kernel L = kernel K) :
    L ∈ saddleClass (lowerCl K) (upperCl K) :=
  mem_saddleClass_lowerCl_of_kernel_eq hK hp hs hclL hL hpL hker

/-- **Theorem 34.5**, summary: the kernel of a simple proper concave-convex function is the kernel
of exactly one equivalence class of closed proper concave-convex functions, represented by
`cl₂ cl₁ K`. -/
theorem theorem_34_5 (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K) (hs : SimpleSaddleFn K) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = kernel K) ∧ ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L →
      ProperSaddleFn L → (kernel L = kernel K ↔ SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_kernel hK hp hs

end Thm345

/-! ### Corollary 34.5.1 -/

section Cor3451

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 34.5.1.** For nonempty convex `C ⊆ ℝᵐ`, `D ⊆ ℝⁿ` and a finite concave-convex `K`
on `C × D`, there is one and only one equivalence class of closed proper concave-convex functions
on `ℝᵐ × ℝⁿ` whose kernel is the restriction of `K` to `ri (C × D)`. -/
theorem corollary_34_5_1 (hC : Convex ℝ C) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v)) :
    ∃ M : Rn m × Rn n → EReal, (ClosedSaddleFn M ∧ ConcaveConvexFn M ∧ ProperSaddleFn M ∧
      kernel M = ConvexAnalysis.restrictFn (ri (C ×ˢ D)) fun p => (K p : EReal)) ∧
      ∀ L : Rn m × Rn n → EReal, ClosedSaddleFn L → ConcaveConvexFn L → ProperSaddleFn L →
        (kernel L = ConvexAnalysis.restrictFn (ri (C ×ˢ D)) (fun p => (K p : EReal)) ↔
          SaddleEquiv M L) :=
  exists_unique_saddleEquiv_class_of_finite hC hCne hDne hconv hconc

end Cor3451

end Rockafellar
