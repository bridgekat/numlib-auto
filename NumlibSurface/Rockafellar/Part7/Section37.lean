import Numlib.Analysis.Convex.Saddle.Conjugate
import Numlib.Analysis.Convex.Saddle.Existence
import Numlib.Analysis.Convex.Saddle.Monotone
import NumlibSurface.Rockafellar.Part7.Section34
import NumlibSurface.Rockafellar.Part7.Section35
import NumlibSurface.Rockafellar.Part7.Section36

/-!
# Rockafellar, §37: Conjugate Saddle-Functions and Minimax Theorems

The lower conjugate `K̲*` and the upper conjugate `K̄*` of a saddle-function, the conjugacy
correspondence among equivalence classes of closed saddle-functions, the effective domain `C* × D*`
of the conjugate class, the existence theorems for the saddle-value and for a saddle-point, and —
as their special cases — Rockafellar's two finite-dimensional minimax theorems. Minimax theory is
the conjugacy correspondence of §§33–34 read at the origin.

All eighteen numbered results of §37 are formalized: Theorems 37.1–37.6 and Corollaries 37.1.1,
37.1.2, 37.1.3, 37.2.1, 37.3.1, 37.3.2, 37.4.1, 37.5.1, 37.5.2, 37.5.3, 37.6.1, 37.6.2.

**Orientation.** The lower conjugate is `sup_v inf_u` and the upper is `inf_u sup_v`, with
`K̲* ≤ K̄*` by Lemma 36.1; swapping the extrema swaps the two conjugates. §33's `cl₁`/`cl₂` and
§36's "minimise in the convex argument, maximise in the concave" are both in force. By Corollary
37.1.1 the conjugates depend only on the equivalence class, so results are stated for a member of
`Ω (F)` (§34) or for a closed concave-convex `K`, from which `exists_mem_Ω_of_closed` recovers `F`.

## Divergences from the book

The `C*` support-function half of Theorem 37.2 is not formalized; its `D*` half is
`theorem_37_2_dom₂`, and nothing downstream depends on the other.

Corollaries 37.3.2 and 37.6.2 are Rockafellar's finite-dimensional minimax theorems. The hypothesis
here is that `C` or `D` be closed and **bounded**, where the infinite-dimensional analogues
(Kneser–Fan, Sion) need compactness; in `ℝⁿ` the two coincide by Heine–Borel. Both also ask for
convexity, concavity and continuity **slice by slice** rather than jointly.

Corollary 37.4.1 carries a closedness hypothesis the book does not state, and Corollary 37.5.1's
homeomorphism comes out as `(u − u*, v* + v)` where the book prints `(u − u*, v + v*)`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §37, pp. 388–400.
-/

namespace Rockafellar

open ConvexAnalysis NumlibSurface

/-! ### The two conjugates of a saddle-function -/

section Defs

variable {m n : ℕ}

/-- Rockafellar's **lower conjugate** `K̲* (u*, v*) = sup_v inf_u {⟨u, u*⟩ + ⟨v, v*⟩ − K (u, v)}`;
the supremum over the **convex** variable is outermost. -/
noncomputable abbrev lowerConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  lowerConjSaddle (pairing m) (pairing n) K

/-- Rockafellar's **upper conjugate** `K̄* (u*, v*) = inf_u sup_v {⟨u, u*⟩ + ⟨v, v*⟩ − K (u, v)}`,
with the infimum over the **concave** variable outermost. -/
noncomputable abbrev upperConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  upperConjSaddle (pairing m) (pairing n) K

/-- The book's defining formula for `K̲*`. -/
theorem lowerConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    lowerConj K q
      = ⨆ v : Rn n, ⨅ u : Rn m, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- The book's defining formula for `K̄*`. -/
theorem upperConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    upperConj K q
      = ⨅ u : Rn m, ⨆ v : Rn n, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- `K̲* ≤ K̄*`, "of course, by Lemma 36.1". No hypotheses. -/
theorem lowerConj_le_upperConj (K : Rn m × Rn n → EReal) : lowerConj K ≤ upperConj K :=
  lowerConjSaddle_le_upperConjSaddle (pairing m) (pairing n) K

/-- Rockafellar's `dom ∂K = {(u, v) | ∂K (u, v) ≠ ∅}`. -/
abbrev domSubgrad (K : Rn m × Rn n → EReal) : Set (Rn m × Rn n) :=
  domSaddleSubgradient (pairing m) (pairing n) K

theorem mem_domSubgrad {K : Rn m × Rn n → EReal} {p : Rn m × Rn n} :
    p ∈ domSubgrad K ↔ (subgrad K p).Nonempty := Iff.rfl

/-- `pairing n` separates on the left; on a self-paired space this is one line from
`inner_self_eq_zero`. -/
theorem separatingLeft_pairing (n : ℕ) : (pairing n).SeparatingLeft :=
  fun _ hx => inner_self_eq_zero.1 (hx _)

/-- Theorem 34.2, packaged for §37: a closed concave-convex function on `ℝᵐ × ℝⁿ` belongs to the
class `Ω (F)` of a unique closed convex bifunction `F`. Properness of `K` is not needed, but
properness of the graph function of `F` is exactly `ProperSaddleFn K`. -/
theorem exists_mem_Ω_of_closed {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K)
    (hcl : ClosedSaddleFn K) :
    ∃ F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedBifun F ∧ K ∈ Ω F := by
  obtain ⟨F, ⟨hFconv, hFcl, hlow, hup⟩, -⟩ := theorem_34_2_converse hK hcl
  exact ⟨F, hFconv, hFcl, theorem_34_2_mem_self hK hlow hup⟩

end Defs

/-! ### Theorem 37.1 -/

section Thm371

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Theorem 37.1**, first equation: for a closed convex bifunction `F` and any `K ∈ Ω (F)`,
`inf_u sup_x* {⟨u, u*⟩ + ⟨x, x*⟩ − K (u, x*)} = ⟨u*, F_* x⟩`. The upper conjugate *is* the
Lagrangian, and the Lagrangian is the concave bracket of the inverse bifunction. -/
theorem theorem_37_1_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    upperConj K = inverseBifunBracket F :=
  (upperConjSaddle_eq_saddleLagrangian (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)).trans (saddleLagrangian_eq_inverseBifunBracket F)

/-- **Theorem 37.1**, second equation: `sup_x* inf_u {⟨u, u*⟩ + ⟨x, x*⟩ − K (u, x*)} =
⟨F_*^* u*, x⟩`, where `F_*^*` is the bifunction of the conjugate class. -/
theorem theorem_37_1_lower (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    lowerConj K = bifunBracket (inverseBifun (dualProgram F)) := by
  have h := lowerConjSaddle_eq_bracket_inverseBifun (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK)
  simp only [flip_pairing] at h
  exact h

/-- The class conjugate to `Ω (F)` is `Ω (F_*^*)`, and `F_*^*` is again a convex bifunction from
`ℝᵐ` to `ℝⁿ`. -/
theorem convexBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ConvexBifun (inverseBifun (dualProgram F)) :=
  convexBifun_inverseBifun_adjointBifun (pairing m) (pairing n) F

/-- And `F_*^*` is closed. -/
theorem closedBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ClosedBifun (inverseBifun (dualProgram F)) :=
  closedBifun_inverseBifun_adjointBifun (pairing m) (pairing n) F

/-- `(F_*^*)_* = F^*`: the inverse operation is an involution. -/
theorem inverseBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun (dualProgram F)) = dualProgram F :=
  inverseBifun_inverseBifun _

/-- The biadjoint identity `(F_*^*)^* = F_*`, for a closed convex bifunction. -/
theorem dualProgram_conjBifun (hF : ConvexBifun F) (hcl : ClosedBifun F) :
    dualProgram (inverseBifun (dualProgram F)) = inverseBifun F := by
  have h := adjointBifun_flip_inverseBifun_adjointBifun (pairing m) (pairing n) hF hcl
  simpa only [flip_pairing] using h

/-- **Theorem 37.1**, third equation: for any `K* ∈ Ω (F_*)`,
`inf_u* sup_x {⟨u, u*⟩ + ⟨x, x*⟩ − K* (u*, x)} = ⟨u, F* x*⟩`, the first equation at `F_*^*`. -/
theorem theorem_37_1_conj_upper (F : Bifun (Rn m) (Rn n))
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : upperConj L = adjointBracket F := by
  have h := theorem_37_1_upper (convexBifun_conjBifun F) (closedBifun_conjBifun F) hL
  have h2 : inverseBifunBracket (inverseBifun (dualProgram F)) = adjointBracket F := by
    change concaveBifunBracket (inverseBifun (inverseBifun (dualProgram F))) = adjointBracket F
    rw [inverseBifun_conjBifun]
  exact h.trans h2

/-- **Theorem 37.1**, fourth equation: `sup_x inf_u* {⟨u, u*⟩ + ⟨x, x*⟩ − K* (u*, x)} = ⟨Fu, x*⟩`.
The second equation at `F_*^*`, using `(F_*^*)^* = F_*`, which is where closedness of `F` is
spent. -/
theorem theorem_37_1_conj_lower (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : lowerConj L = bifunBracket F := by
  have h := theorem_37_1_lower (convexBifun_conjBifun F) hL
  rw [dualProgram_conjBifun hF hcl, inverseBifun_inverseBifun] at h
  exact h

end Thm371

/-! ### Corollary 37.1.1 -/

section Cor3711

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- The upper conjugate of a member of `Ω (F)` lies in the conjugate class `Ω (F_*^*)`. -/
theorem upperConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    upperConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (inverseBifun (adjointBifun (pairing m) (pairing n) F)) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_right (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simpa only [flip_pairing] using hmem
  exact hmem'

/-- So does the lower conjugate. -/
theorem lowerConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    lowerConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (inverseBifun (adjointBifun (pairing m) (pairing n) F)) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_left (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simpa only [flip_pairing] using hmem
  exact hmem'

/-- **Corollary 37.1.1**: `K̲*` is concave-convex. -/
theorem corollary_37_1_1_lower_concaveConvex (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    ConcaveConvexFn (lowerConj K) :=
  concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**: `K̲*` is **lower closed**, `cl₂ cl₁ K̲* = K̲*` — Theorem 33.3 at
`F_*^*`. -/
theorem corollary_37_1_1_lower_lowerClosed (hF : ConvexBifun F) (_hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : LowerClosedFn (lowerConj K) :=
  lowerClosedFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**: `K̄*` is concave-convex. -/
theorem corollary_37_1_1_upper_concaveConvex (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : ConcaveConvexFn (upperConj K) :=
  concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**: `K̄*` is **upper closed**, `cl₁ cl₂ K̄* = K̄*`. -/
theorem corollary_37_1_1_upper_upperClosed (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) : UpperClosedFn (upperConj K) :=
  upperClosedFn_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**: `K̲*` and `K̄*` are **equivalent**, so by Theorem 36.4 they have the same
iterated extrema and the same saddle-points. -/
theorem corollary_37_1_1_equiv (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj K) (upperConj K) :=
  saddleEquiv_lowerConjSaddle_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**: the lower conjugate is a closed saddle-function — the two conjugates are
the ends of the closure pair of `Ω (F_*^*)`. -/
theorem corollary_37_1_1_closed_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn (lowerConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedBifun_conjBifun F)
    (lowerConj_mem_Ω hF hcl hK)

/-- **Corollary 37.1.1**: and so is the upper conjugate. -/
theorem corollary_37_1_1_closed_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    ClosedSaddleFn (upperConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedBifun_conjBifun F)
    (upperConj_mem_Ω hF hcl hK)

/-- **Corollary 37.1.1**: the lower conjugate **depends only on the equivalence class** — two
members of `Ω (F)` have the same one, on the nose. -/
theorem corollary_37_1_1_lower_class (hF : ConvexBifun F) (hK : K ∈ Ω F) (hL : L ∈ Ω F) :
    lowerConj K = lowerConj L :=
  (theorem_37_1_lower hF hK).trans (theorem_37_1_lower hF hL).symm

/-- **Corollary 37.1.1**: and so does the upper conjugate. -/
theorem corollary_37_1_1_upper_class (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : upperConj K = upperConj L :=
  (theorem_37_1_upper hF hcl hK).trans (theorem_37_1_upper hF hcl hL).symm

/-- A saddle-function conjugate to a closed **proper** saddle-function is proper: the only
improper closed saddle-functions are the constants `±∞`, and those are conjugate to each other. -/
theorem corollary_37_1_1_proper_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (upperConj K) :=
  properSaddleFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- The same for the lower conjugate. -/
theorem corollary_37_1_1_proper_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (lowerConj K) :=
  properSaddleFn_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1**, last sentence: conjugacy is involutive up to equivalence — the lower
conjugate of a conjugate of `K` is equivalent to `K`. It is `⟨Fu, x*⟩`, the lower end of
`Ω (F)`. -/
theorem corollary_37_1_1_biconj_lower (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj (upperConj K)) K := by
  rw [theorem_37_1_conj_lower hF hcl (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_lower_mem hF hcl) hK

/-- **Corollary 37.1.1**, last sentence: and the upper conjugate of `K*` is `⟨u, F*x*⟩`, the
upper end of `Ω (F)`. -/
theorem corollary_37_1_1_biconj_upper (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (upperConj (upperConj K)) K := by
  rw [theorem_37_1_conj_upper F (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_upper_mem hF hcl) hK

end Cor3711

/-! ### Corollary 37.1.2 -/

section Cor3712

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Corollary 37.1.2**, first equation: `cl₁ K̲* = K̄*`. -/
theorem corollary_37_1_2_cl₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₁ (lowerConj K) = upperConj K :=
  partialCl₁_lowerConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2**, second equation: `cl₂ K̄* = K̲*`. -/
theorem corollary_37_1_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    cl₂ (upperConj K) = lowerConj K :=
  partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2**: `C* × D*` is the effective domain of **both** conjugates. -/
theorem corollary_37_1_2_dom (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : domSaddle (lowerConj K) = domSaddle (upperConj K) :=
  domSaddle_conjSaddle_eq (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2**, first sentence: the conjugates of a closed proper saddle-function have
the structural properties of Theorem 34.3 with respect to the nonempty convex `C* × D*`. -/
theorem corollary_37_1_2_structure (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : SaddleStructure (upperConj K) :=
  (theorem_34_3 (corollary_37_1_1_upper_concaveConvex hF hcl hK)
    (corollary_37_1_1_proper_upper hF hcl hK hp)).1 (corollary_37_1_1_closed_upper hF hcl hK)

/-- **Corollary 37.1.2**, last clause: `K̲* = K̄*` at `(u*, v*)` whenever `u* ∈ ri C*`. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (dom₁ (lowerConj K)))
    (v : Rn n) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hu v

/-- **Corollary 37.1.2**, last clause: and whenever `v* ∈ ri D*`. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {v : Rn n} (hv : v ∈ ri (dom₂ (lowerConj K)))
    (u : Rn m) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hv u

end Cor3712

/-! ### The saddle-value read at the origin, and Corollary 37.1.3 -/

section Cor3713

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- `inf_v sup_u K (u, v) = −K̲* (0, 0)`. No hypotheses. -/
theorem minimax_eq_neg_lowerConj_zero (K : Rn m × Rn n → EReal) :
    minimax K = -(lowerConj K 0) :=
  minimax_eq_neg_lowerConjSaddle_zero (pairing m) (pairing n) K

/-- `sup_u inf_v K (u, v) = −K̄* (0, 0)`. No hypotheses. -/
theorem maximin_eq_neg_upperConj_zero (K : Rn m × Rn n → EReal) :
    maximin K = -(upperConj K 0) :=
  maximin_eq_neg_upperConjSaddle_zero (pairing m) (pairing n) K

/-- **Corollary 37.1.3** (the book prints no proof): if the origin of `ℝᵐ` lies in `ri C*` then
`inf_v sup_u K = sup_u inf_v K`. The two displays above make the saddle-value exist exactly when
the conjugates agree at the origin, and Corollary 37.1.2 makes them agree on `ri C* × ℝⁿ`. -/
theorem corollary_37_1_3_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Corollary 37.1.3**: the same when the origin of `ℝⁿ` lies in `ri D*`. -/
theorem corollary_37_1_3_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Corollary 37.1.3**, last sentence: if **both** conditions hold the saddle-value is
finite. -/
theorem corollary_37_1_3_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)))
    (h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_mem_relint_domSaddle (pairing m) (pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h1 h2

end Cor3713

/-! ### Theorem 37.2 and Corollary 37.2.1 -/

section Thm372

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.2**, the `D*` formula: for a closed proper concave-convex `K` with effective
domain `C × D`, `δ*(w | D*) = sup_{u ∈ ri C} sup_{v ∈ D} {K (u, v + w) − K (u, v)}`. The `C*`
formula is not carried; see the module docstring. -/
theorem theorem_37_2_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), ⨆ v ∈ dom₂ K, (K (u, v + w) - K (u, v)) :=
  supportFn_dom₂_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Theorem 37.2**, the `D*` formula in recession-function form: `δ*(· | D*)` is the pointwise
supremum over `u ∈ ri C` of the recession functions of the slices `K (u, ·)`. -/
theorem theorem_37_2_dom₂_recessionFn (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), recessionFn (fun v => K (u, v)) w :=
  supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Corollary 37.2.1**, first half: `0 ∈ int D*` if and only if the convex functions `K (u, ·)`,
`u ∈ ri C`, have **no common direction of recession**. -/
theorem corollary_37_2_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn n) ∈ interior (dom₂ (upperConj K)) ↔
      ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w :=
  zero_mem_interior_dom₂_upperConjSaddle_iff (pairing m) (pairing n) (separatingRight_pairing n)
    hF hcl (proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
      (mem_bifunSaddleClass_of_mem_Ω hK) hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1
    hp.dom₂_nonempty ((theorem_34_3 hK.1 hp).1 hcls).1

/-- **Corollary 37.2.1**, second half: `0 ∈ int C*` if and only if the convex functions `−K (·, v)`,
`v ∈ ri D`, have no common direction of recession. -/
theorem corollary_37_2_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn m) ∈ interior (dom₁ (lowerConj K)) ↔
      ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z :=
  zero_mem_interior_dom₁_lowerConjSaddle_iff (pairing m) (pairing n) (separatingLeft_pairing m)
    hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls)

end Thm372

/-! ### Theorem 37.3 and its two corollaries -/

section Thm373

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.3 (a)**: if the convex functions `K (u, ·)`, `u ∈ ri C`, have no common direction
of recession, the saddle-value of `K` exists. It is Corollaries 37.1.3 and 37.2.1 combined. -/
theorem theorem_37_3_a (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession (pairing m) (pairing n)
    (separatingRight_pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 hrec

/-- **Theorem 37.3 (b)**: if the convex functions `−K (·, v)`, `v ∈ ri D`, have no common
direction of recession, the saddle-value of `K` exists. -/
theorem theorem_37_3_b (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_neg (pairing m) (pairing n)
    (separatingLeft_pairing m) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hrec

/-- **Theorem 37.3**, last sentence: if **both** conditions hold the saddle-value is finite.
Corollary 37.2.1 turns them into `0 ∈ int C*` and `0 ∈ int D*`. -/
theorem theorem_37_3_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  have hpr := proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
    (mem_bifunSaddleClass_of_mem_Ω hK) hp
  have h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)) :=
    interior_subset_intrinsicInterior ((corollary_37_2_1_dom₁ hF hcl hK hp hcls).2 hrec₁)
  have h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K)) := by
    rw [dom₂_conjSaddle_eq (pairing m) (pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact interior_subset_intrinsicInterior ((corollary_37_2_1_dom₂ hF hcl hK hp hcls).2 hrec₂)
  exact corollary_37_1_3_finite hF hcl hK hp h1 h2

/-- **Corollary 37.3.1**, the half where `D` is bounded: the effective domain of `K (u, ·)` is `D`
for every `u ∈ ri C` (Theorem 34.3), so a bounded `D` fulfils condition (a). -/
theorem corollary_37_3_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₂ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₂ (pairing m) (pairing n) (separatingRight_pairing n) hF hcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n) (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty hp.dom₁_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 hbd

/-- **Corollary 37.3.1**, the half where `C` is bounded: condition (b) is fulfilled. -/
theorem corollary_37_3_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₁ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁ (pairing m) (pairing n) (separatingLeft_pairing m) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hbd

end Thm373

/-! ### Corollary 37.3.2: the minimax theorem for a finite continuous saddle-function -/

section Cor3732

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 37.3.2.** For nonempty closed convex `C ⊆ ℝᵐ`, `D ⊆ ℝⁿ` and a continuous finite
concave-convex `K` on `C × D` with `D` **bounded**,
`inf_{v ∈ D} sup_{u ∈ C} K (u, v) = sup_{u ∈ C} inf_{v ∈ D} K (u, v)`. The extrema are in `EReal`:
with only `D` bounded both can be infinite (`C = {0}`, `D = ℝ`, `K (u, v) = v`). -/
theorem corollary_37_3_2_right (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_right (pairing m) (pairing n)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbd

/-- **Corollary 37.3.2**, the half where `C` is bounded. Same divergences as
`corollary_37_3_2_right`. -/
theorem corollary_37_3_2_left (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_left (pairing m) (pairing n)
    (separatingLeft_pairing m) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbd

end Cor3732

/-! ### Theorem 37.4: subgradients are saddle-points of the tilted function -/

section Thm374

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Theorem 37.4**, first sentence: `(u*, v*) ∈ ∂K (u, v)` exactly when `(u, v)` is a
saddle-point of the tilted function `K − ⟨·, u*⟩ − ⟨·, v*⟩`. The two inner products are combined
into one real coercion so that no `∞ − ∞` can arise, and there are **no hypotheses at all** — not
concavity, not convexity, not properness, where the book assumes concave-convexity. -/
theorem theorem_37_4 (K : Rn m × Rn n → EReal) (p q : Rn m × Rn n) :
    q ∈ subgrad K p ↔ IsSaddlePoint (saddleTilt (pairing m) (pairing n) K q) p :=
  mem_saddleSubgradient_iff_isSaddlePoint

/-- `∂K (u, v)` is **convex**, with no hypothesis on `K`: it is a product of two convex sets. -/
theorem theorem_37_4_convex (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    Convex ℝ (subgrad K p) := convex_subgrad

private theorem isClosed_subgrad₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subgrad₁ K p) := by
  have h : subgrad₁ K p
      = (fun y : Rn m => -y) ⁻¹' subgradient (pairing m) (fun u => -(K (u, p.2))) p.1 := by
    ext y
    exact mem_subgrad₁_iff_neg_mem_subgradient_neg
  rw [h]
  exact (isClosed_subgradient _ _).preimage continuous_neg

/-- `∂K (u, v)` is **closed**. The concave factor is assembled from §35's sign dictionary
`mem_subgrad₁_iff_neg_mem_subgradient_neg` and `isClosed_subgradient`. -/
theorem theorem_37_4_isClosed (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subgrad K p) :=
  (isClosed_subgrad₁ K p).prod (isClosed_subgradient _ _)

/-- **Theorem 37.4**, left-hand inclusion: `ri (dom K) ⊆ dom ∂K` for a closed proper concave-convex
function. Over `ri C` the slice `K (u, ·)` is proper with effective domain `D` (Theorem 34.3), so
Theorem 23.4 produces a subgradient; the concave half is the same statement for `saddleSwap K`. -/
theorem theorem_37_4_relint (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) : ri (domSaddle K) ⊆ domSubgrad K := by
  have h := kernelSet_subset_domSaddleSubgradient (Bu := pairing m) (Bx := pairing n) hK
    ((theorem_34_3 hK hp).1 hcl)
  rwa [kernelSet_eq_relint_domSaddle] at h

/-- **Theorem 37.4**, right-hand inclusion: `dom ∂K ⊆ dom K`. Only **properness** is used — a
subgradient pair makes `p` a saddle-point of the tilt, and Corollary 36.3.1 places it in
`dom K`. -/
theorem theorem_37_4_dom (hp : ProperSaddleFn K) : domSubgrad K ⊆ domSaddle K :=
  domSaddleSubgradient_subset_domSaddle hp

end Thm374

/-! ### Corollary 37.4.1 -/

section Cor3741

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Corollary 37.4.1**: equivalent saddle-functions have the same subdifferential, `∂K = ∂L`, so
one may speak of the subdifferential of an equivalence *class*.

Rockafellar tilts both functions and appeals to Theorem 36.4, which needs `cl₁ (K − ℓ) = cl₁ K − ℓ`;
the route here is Theorem 37.5's (a) ⇔ (d), and the price is a **closedness hypothesis the book's
statement does not carry**. -/
theorem corollary_37_4_1_subgrad (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : subgrad K = subgrad L := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  have hpair : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → ∀ p q : Rn m × Rn n,
      (q ∈ subgrad M p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q) := by
    intro M hM p q
    have hb := mem_saddleSubgradient_iff_isBifunSubgradientPair (pairing m) (pairing n) hFconv
      hFcl (mem_bifunSaddleClass_of_mem_Ω hM) p q
    simpa only [flip_pairing] using hb
  funext p
  ext q
  exact (hpair K hKmem p q).trans (hpair L hLmem p q).symm

/-- **Corollary 37.4.1**, second sentence: equivalent saddle-functions moreover **agree in value**
on `dom ∂K = dom ∂L`. A subgradient pair at `p` says the conjugate of the convex slice is attained,
and that conjugate is `F p.1` for every member of the class. -/
theorem corollary_37_4_1_eq (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) {p : Rn m × Rn n} (hp : p ∈ domSubgrad K) :
    K p = L p := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  obtain ⟨q, hq⟩ := hp
  have hqL : q ∈ subgrad L p := by
    rw [← corollary_37_4_1_subgrad hK hcl hL h]
    exact hq
  have key : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → q ∈ subgrad M p →
      ((pairing n p.2 q.2 : ℝ) : EReal) - F p.1 q.2 = M p := by
    intro M hM hqM
    have hA : conj (pairing n).flip (fun v => M (p.1, v)) = F p.1 :=
      congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hFconv hFcl
        (mem_bifunSaddleClass_of_mem_Ω hM)) p.1
    rw [flip_pairing] at hA
    have hsub : conj (pairing n) (fun v => M (p.1, v)) q.2
        = ((pairing n p.2 q.2 : ℝ) : EReal) - M (p.1, p.2) :=
      mem_subgradient_iff_conj_eq.1 hqM.2
    rw [hA] at hsub
    exact eq_coe_sub_iff_coe_sub_eq.1 hsub
  exact (key K hKmem hq).symm.trans (key L hLmem hqL)

end Cor3741

/-! ### Theorem 37.5 -/

section Thm375

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.5**, the function `f`: the graph function of the `F` of Theorem 34.2,
`f (u, v*) = sup_v {⟨v, v*⟩ − K (u, v)}`. It is closed proper convex on `ℝᵐ⁺ⁿ`, read here as a
function on `ℝᵐ × ℝⁿ`. -/
theorem theorem_37_5_f (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) (u : Rn m)
    (w : Rn n) : graphFn F (u, w) = ⨆ v : Rn n, (((pairing n v w : ℝ) : EReal) - K (u, v)) := by
  have hA : conj (pairing n).flip (fun v => K (u, v)) = F u :=
    congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK)) u
  rw [flip_pairing] at hA
  have hg : graphFn F (u, w) = F u w := rfl
  rw [hg, ← hA, conj_apply]

/-- **Theorem 37.5 (a)**, against condition (d): `(u*, v*) ∈ ∂K (u, v)` exactly when the pair
satisfies the class-level condition `IsBifunSubgradientPair`. Because the right-hand side mentions
only `F`, this *is* the statement that `∂K` depends only on the equivalence class. -/
theorem theorem_37_5_a (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    q ∈ subgrad K p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubgradient_iff_isBifunSubgradientPair (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Theorem 37.5 (b)**, against condition (d): `(u, v) ∈ ∂K* (u*, v*)` for the canonical upper
conjugate. With (a) this says the subdifferentials of conjugate classes are **inverse** to each
other, as `∂(f*) = (∂f)⁻¹` is for convex functions. -/
theorem theorem_37_5_b (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    p ∈ subgrad (upperConj K) q ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubgradient_upperConjSaddle_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Theorem 37.5 (c)**, against condition (d): `(−u*, v) ∈ ∂f (u, v*)`. So `∂K` is the **partial
inversion** of `∂f` — second components of point and gradient swapped, first component of the
gradient negated. That is what transfers closedness, the Minty parametrisation and maximal
monotonicity to `∂K`, and is the source of the asymmetry in Corollaries 37.5.1 and 37.5.2. -/
theorem theorem_37_5_c (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      (-q.1, p.2) ∈ subgradient (pairingProd m n) (graphFn F) (p.1, q.2) :=
  isBifunSubgradientPair_iff_mem_subgradient_graphFn (pairing m) (pairing n) F p q

/-- **Theorem 37.5 (d)**: the condition `(Fu)(v*) − ⟨v, v*⟩ = (F*v)(u*) − ⟨u, u*⟩`, the equality
case of `⟨v, v*⟩ − (Fu)(v*) ≤ ⟨Fu, v⟩ ≤ K (u, v) ≤ ⟨u, F*v⟩ ≤ ⟨u, u*⟩ − (F*v)(u*)`. It mentions no
representative of the class, which is why (a), (b) and (c) are stated against it. -/
theorem theorem_37_5_d (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      F p.1 q.2 - ((pairing n q.2 p.2 : ℝ) : EReal)
        = dualProgram F p.2 q.1 - ((pairing m p.1 q.1 : ℝ) : EReal) := Iff.rfl

end Thm375

/-! ### Corollaries 37.5.1 and 37.5.2 -/

section Cor3751

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

private theorem continuous_pairing (n : ℕ) :
    Continuous fun r : Rn n × Rn n => pairing n r.1 r.2 := continuous_inner

/-- **Corollary 37.5.1**, closedness clause: the graph of `∂K` is closed. Theorem 37.5 (c) makes it
the preimage of the graph of `∂f` under a linear homeomorphism, and Theorem 24.4 applies. -/
theorem corollary_37_5_1_isClosed (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F) :
    IsClosed {r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} := by
  have h := isClosed_setOf_mem_saddleSubgradient (pairing m) (pairing n) (continuous_pairing m)
    (continuous_pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.1**, homeomorphism clause: the graph of `∂K` is homeomorphic to `ℝᵐ × ℝⁿ`
under `(u, v, u*, v*) ↦ (u − u*, v + v*)`. The map is asymmetric, being Corollary 31.5.1's Minty
parametrisation composed with the partial inversion of Theorem 37.5 (c). `F` is an explicit
argument because a `Homeomorph` is data; `corollary_37_5_1_exists_homeomorph` is the book's
form. -/
noncomputable def corollary_37_5_1_homeomorph (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F) :
    ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} ≃ₜ (Rn m × Rn n) :=
  saddleSubgradientHomeomorph hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)

/-- The homeomorphism is the book's map, with the two summands of the second component in the
other order: `(u − u*, v* + v)` against the printed `(u − u*, v + v*)`. -/
theorem corollary_37_5_1_homeomorph_apply (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F)
    (r : ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1}) :
    corollary_37_5_1_homeomorph hF hcl hpr hK r = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) :=
  saddleSubgradientHomeomorph_apply hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) r

/-- **Corollary 37.5.1** in the book's own quantification: for a closed proper concave-convex
`K` the graph of `∂K` is homeomorphic to `ℝᵐ × ℝⁿ`. -/
theorem corollary_37_5_1_exists_homeomorph (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    Nonempty (↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subgrad K r.1} ≃ₜ (Rn m × Rn n)) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_mem_Ω_of_closed hK hcl
  exact ⟨corollary_37_5_1_homeomorph hFconv hFcl
    (proper_graphFn_of_properSaddleFn (pairing m) (pairing n)
      (mem_bifunSaddleClass_of_mem_Ω hmem) hp) hmem⟩

/-- **Corollary 37.5.2**: `ρ : (u, v) ↦ {(−u*, v*) | (u*, v*) ∈ ∂K (u, v)}` is a **maximal
monotone** mapping from `ℝᵐ × ℝⁿ` to itself. The `u* ↦ −u*` is inserted, not derived: `∂K` carries
a superdifferential in the first argument and a subdifferential in the second, so it is monotone in
one variable and antitone in the other, and negating the first dual component repairs it. -/
theorem corollary_37_5_2 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hpr : Proper (graphFn F))
    (hK : K ∈ Ω F) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subgrad K r.1} := by
  have h := isMaximalMonotoneRel_saddleMonotoneRel hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  have he : saddleMonotoneRel (pairing m) (pairing n) K
      = {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subgrad K r.1} := by
    ext r
    simp only [mem_saddleMonotoneRel, flip_pairing, Set.mem_ofPred_eq]
  rwa [he] at h

/-- **Corollary 37.5.2**, "in particular": if `K` is everywhere finite and differentiable then
`(u, v) ↦ (−∇₁K (u, v), ∇₂K (u, v))` is maximal monotone. The gradient is a **pair**, not a vector
of `ℝᵐ⁺ⁿ`, because Mathlib gives a product of inner-product spaces the supremum norm. -/
theorem corollary_37_5_2_gradient {K : Rn m × Rn n → ℝ}
    (hK : ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K)
    (hdiff : ∀ p : Rn m × Rn n, DifferentiableAt ℝ K p) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} :=
  isMaximalMonotoneRel_setOf_hasSaddleGradientAt hK hdiff

end Cor3751

/-! ### Corollary 37.5.3 -/

section Cor3753

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Corollary 37.5.3**: `∂K* (0, 0)` **is** the set of saddle-points of `K`. It is Theorem
37.5 (b) at the origin composed with Theorem 37.4, whose tilt by the origin is `K` itself. -/
theorem corollary_37_5_3 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (p : Rn m × Rn n) : p ∈ subgrad (upperConj K) 0 ↔ IsSaddlePoint K p := by
  have h := mem_saddleSubgradient_upperConjSaddle_zero_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.3**: the saddle-points form a **convex product set**, being a value of
`∂K* = ∂₁K* × ∂₂K*`. -/
theorem corollary_37_5_3_convex (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    Convex ℝ {p : Rn m × Rn n | IsSaddlePoint K p} :=
  convex_setOf_isSaddlePoint (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.5.3**: and a **closed** set. -/
theorem corollary_37_5_3_isClosed (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    IsClosed {p : Rn m × Rn n | IsSaddlePoint K p} := by
  have hset : {p : Rn m × Rn n | IsSaddlePoint K p} = subgrad (upperConj K) 0 := by
    ext p
    exact (corollary_37_5_3 hF hcl hK p).symm
  rw [hset]
  exact theorem_37_4_isClosed _ _

/-- **Corollary 37.5.3**, last sentence: a saddle-point exists **if and only if**
`(0, 0) ∈ dom ∂K*`. -/
theorem corollary_37_5_3_exists_iff (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F) :
    (∃ p, IsSaddlePoint K p) ↔ (0 : Rn m × Rn n) ∈ domSubgrad (upperConj K) := by
  have h := exists_isSaddlePoint_iff_zero_mem_domSaddleSubgradient (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.3**, "in particular": `K` has a saddle-point as soon as
`(0, 0) ∈ ri (dom K*)`, by Theorem 37.4 applied to `K*`. -/
theorem corollary_37_5_3_exists_of_relint (hF : ConvexBifun F) (hcl : ClosedBifun F)
    (hpr : Proper (graphFn F)) (hK : K ∈ Ω F)
    (h0 : (0 : Rn m × Rn n) ∈ ri (domSaddle (upperConj K))) : ∃ p, IsSaddlePoint K p := by
  refine exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle (pairing m) (pairing n) hF
    hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) ?_
  rwa [← kernelSet_eq_relint_domSaddle] at h0

end Cor3753

/-! ### Theorem 37.6 and its two corollaries -/

section Thm376

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.6**: if conditions (a) **and** (b) of Theorem 37.3 both hold, `K` has a
saddle-point. Corollary 37.2.1 turns the two recession conditions into `(0, 0) ∈ ri (dom K*)` and
Corollary 37.5.3 produces the point. -/
theorem theorem_37_6 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_no_common_direction_of_recession (pairing m) (pairing n)
    (separatingLeft_pairing m) (separatingRight_pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hrec₂ hrec₁

/-- **Theorem 37.6**, parenthesis: a saddle-point of a proper saddle-function lies in
`C × D = dom K`. -/
theorem theorem_37_6_mem_dom (hp : ProperSaddleFn K) {q : Rn m × Rn n} (hq : IsSaddlePoint K q) :
    q ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp hq

/-- **Corollary 37.6.1**: if `C` **and** `D` are bounded, `K` has a saddle-point — the slices over
the relative interiors have effective domains exactly `D` and `C` (Theorem 34.3). -/
theorem corollary_37_6_1 (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

/-- **Corollary 37.6.1**, second clause: the saddle-value is then **finite**, being a value of `K`
at a saddle-point. -/
theorem corollary_37_6_1_finite (hF : ConvexBifun F) (hcl : ClosedBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

end Thm376

/-! ### Corollary 37.6.2: the minimax theorem -/

section Cor3762

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 37.6.2**, the classical minimax theorem: for nonempty closed **bounded** convex
`C ⊆ ℝᵐ`, `D ⊆ ℝⁿ` and a continuous finite concave-convex `K` on `C × D`, there are `ū ∈ C`,
`v̄ ∈ D` with `K (u, v̄) ≤ K (ū, v̄) ≤ K (ū, v)` for all `u ∈ C`, `v ∈ D`. The lower simple
extension of `K` is closed proper with effective domain `C × D`, Corollary 37.6.1 gives it a
saddle-point, and Corollary 36.3.1 places that point in `C × D`. -/
theorem corollary_37_6_2 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : Rn m × Rn n, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ v ∈ D, K q ≤ K (q.1, v) :=
  exists_saddlePoint_of_isBounded (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne hconv hconc hcontD hcontC hbdC hbdD

end Cor3762

end Rockafellar
