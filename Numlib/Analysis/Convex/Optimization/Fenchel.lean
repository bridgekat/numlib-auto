import Numlib.Analysis.Convex.Duality.ConcaveConj
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Optimization.Minimum

/-!
# Fenchel's duality theorem

Minimising a difference `f - g`, with `f` convex and `g` concave, is dual to maximising `g* - f*`,
where `g*` is the *concave* conjugate. Weak duality `g*(y) - f*(y) ≤ f x - g x` is Fenchel's
inequality used twice and needs no hypothesis at all; equality, and attainment on one of the two
sides, needs `f` and `-g` to add exactly. A linear transformation may be interposed between the two
functions; the Kuhn–Tucker conditions `y ∈ ∂f x`, `-y ∈ ∂(-g) x` characterise a jointly optimal
pair; and the whole specialises to minimising over a convex cone `K`, where the dual problem is
minimising `f*` over `K* = -K°`.

## Main results

* `concaveConj_sub_conj_le_sub` — weak duality, pointwise.
* `fenchel_duality`, `exists_concaveConj_sub_conj_eq` — **Fenchel's duality theorem** under
  condition (a): `inf (f - g) = sup (g* - f*)`, with the supremum attained (Theorem 31.1 in [^1]).
* `fenchel_duality_of_closed`, `exists_sub_eq_iInf` — the same under condition (b): the same
  equality, with the *infimum* attained.
* `fenchel_duality_comp`, `exists_concaveConj_sub_conj_comp_eq` — the same with a linear
  transformation interposed: `inf (f - g A) = sup (g* - f* A')`, with the supremum attained.
* `sub_eq_concaveConj_sub_conj_iff`, `sub_comp_eq_concaveConj_sub_conj_iff` — the **Fenchel
  optimality conditions**, with and without the transformation, read as a criterion for minimality
  by `iInf_sub_eq_iff_exists_kuhnTucker` and `iInf_sub_comp_eq_iff_exists_kuhnTucker`.
* `iInf_mem_eq_neg_iInf_mem_neg_polarCone` — the **cone form**, with
  `exists_mem_neg_polarCone_conj_eq_iInf` and `exists_mem_eq_iInf_of_isExactSum_conj` for
  attainment under (a) and (b), `iInf_mem_submodule_eq_neg_iInf_mem_polarCone` for a subspace.

## Implementation notes

The hypothesis throughout is `IsExactSum B f (-g)`, not a constraint qualification. The book's
condition (a) `ri (dom f) ∩ ri (dom g) ≠ ∅`, its condition (b) on the conjugates, and the two
polyhedral weakenings of each are all ways of saying that `f` and `-g` add exactly, so the theorem
is proved once and every variant is an instance; condition (b) is condition (a) read on the dual
pair. The transformed statement likewise splits the book's transformed condition (a) into two
interfaces, `IsExactSum` for the sum and `IsExactImage` for the pullback along `A`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §31.
-/

namespace ConvexAnalysis

section Fenchel

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

omit [Module ℝ E] [Module ℝ F] in
/-- Reindexing an infimum over a group by negation. -/
private theorem iInf_neg_comp (ψ : F → EReal) : (⨅ y : F, ψ y) = ⨅ y : F, ψ (-y) :=
  le_antisymm (le_iInf fun y => iInf_le ψ (-y))
    (le_iInf fun y => le_trans (iInf_le (fun z => ψ (-z)) (-y)) (le_of_eq (by rw [neg_neg])))

/-- Two Fenchel inequalities sharing the same *finite* value `p` combine into a comparison of
differences; both `∞ - ∞` collisions are absorbed on the correct side. -/
private theorem sub_le_sub_of_le_sub_of_sub_le {a b c d : EReal} {p : ℝ}
    (h1 : a ≤ (p : EReal) - b) (h2 : (p : EReal) - c ≤ d) : a - d ≤ c - b := by
  have hpb : ((p : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hpt : ((p : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have h3 : -d ≤ c - ((p : ℝ) : EReal) := by
    refine le_trans (EReal.neg_le_neg_iff.2 h2) (le_of_eq ?_)
    rw [EReal.neg_sub (.inl hpb) (.inl hpt), sub_eq_add_neg, add_comm]
  have hsum : a + -d ≤ (((p : ℝ) : EReal) - b) + (c - ((p : ℝ) : EReal)) := add_le_add h1 h3
  refine le_trans (le_of_eq (sub_eq_add_neg _ _)) (le_trans hsum (le_of_eq ?_))
  rw [sub_eq_add_neg ((p : ℝ) : EReal) b, sub_eq_add_neg c ((p : ℝ) : EReal),
    add_comm c (-((p : ℝ) : EReal)),
    add_add_add_comm ((p : ℝ) : EReal) (-b) (-((p : ℝ) : EReal)) c]
  have hpp : ((p : ℝ) : EReal) + -((p : ℝ) : EReal) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  rw [hpp, zero_add, add_comm (-b) c, sub_eq_add_neg]

/-- **Weak duality**, pointwise: every dual value is below every primal value, by Fenchel's
inequality for `f` and for `g` added together. No hypothesis at all is needed — both `∞ - ∞`
collisions send the left side to `⊥`. -/
theorem concaveConj_sub_conj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) (y : F) :
    concaveConj B g y - conj B f y ≤ f x - g x :=
  sub_le_sub_of_le_sub_of_sub_le (concaveConj_le_sub B g x y) (sub_le_conj B f x y)

/-- **Fenchel's duality theorem**: `inf (f - g) = sup (g* - f*)`. This is `inf h = -h*(0)` applied
to `h = f + (-g)`, with exact addition splitting the conjugate of that sum at the origin. -/
theorem fenchel_duality (hex : IsExactSum B f (-g)) :
    (⨅ x, f x - g x) = ⨆ y, concaveConj B g y - conj B f y := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.conj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(conj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_conj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  have hdual : conj B (f + fun x => -(g x)) 0 = ⨅ y : F, conj B f y - concaveConj B g y := by
    rw [hex'.conj_add_apply 0, iInf_neg_comp]
    refine iInf_congr fun y => ?_
    rw [zero_sub, neg_neg, ← neg_concaveConj B g y, sub_eq_add_neg]
  rw [hprimal, hdual, EReal.neg_iInf]
  exact iSup_congr fun y => EReal.neg_sub_comm (.inl (hex'.conj_left_ne_bot y)) (.inr (hne y))

/-- **Attainment**: under exact addition the supremum of `g* - f*` is attained. -/
theorem exists_concaveConj_sub_conj_eq (hex : IsExactSum B f (-g)) :
    ∃ y : F, concaveConj B g y - conj B f y = ⨅ x, f x - g x := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.conj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(conj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_conj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  obtain ⟨y₁, y₂, hy, hval⟩ := hex'.exists_conj_add_eq 0
  have hy2 : y₂ = -y₁ := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hy
  subst hy2
  rw [← neg_concaveConj B g y₁, ← sub_eq_add_neg] at hval
  refine ⟨y₁, ?_⟩
  rw [hprimal, ← hval, EReal.neg_sub_comm (.inl (hex'.conj_left_ne_bot y₁)) (.inr (hne y₁))]

/-- The two clauses packaged: the common value is the *greatest* dual value. -/
theorem isGreatest_concaveConj_sub_conj (hex : IsExactSum B f (-g)) :
    IsGreatest (Set.range fun y => concaveConj B g y - conj B f y) (⨅ x, f x - g x) := by
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq hex
  refine ⟨⟨y, hy⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [fenchel_duality hex]
  exact le_iSup (fun w : F => concaveConj B g w - conj B f w) z

end Fenchel

/-! ### A linear transformation between the two functions -/

section Comp

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal}

/-- **The concave face of the image rule**: the concave conjugate of an inverse image `g A` is the
*supremum* of `g*` over the fibres of the transpose, where the convex statement has an infimum.
Both reflections are at work, so the fibre `A' z = -y` becomes `A' z = y`. -/
theorem concaveConj_compLin (hA : IsAdjointPair B B' A A')
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (y : F) :
    concaveConj B (compLin g A) y = ⨆ z : H, ⨆ _ : A' z = y, concaveConj B' g z := by
  set k : H → EReal := conj B' (fun w => -(g w)) with hk
  have hneg : ∀ z : H, -(concaveConj B' g z) = k (-z) := fun z => neg_concaveConj B' g z
  have hmain : mapLin A' k (-y) = ⨅ z : H, ⨅ _ : A' z = y, k (-z) := by
    refine le_antisymm (le_iInf fun z => le_iInf fun hz => mapLin_le ?_) (le_mapLin fun w hw => ?_)
    · rw [map_neg, hz]
    · refine le_trans (iInf₂_le (f := fun z (_ : A' z = y) => k (-z)) (-w) ?_) (le_of_eq ?_)
      · rw [map_neg, hw, neg_neg]
      · rw [neg_neg]
  have hcomp : concaveConj B (compLin g A) y = -(mapLin A' k (-y)) := by
    rw [concaveConj_eq_neg_conj_neg]
    congr 1
    exact congrFun (himg.conj_compLin) (-y)
  rw [hcomp, hmain, EReal.neg_iInf]
  refine iSup_congr fun z => ?_
  rw [EReal.neg_iInf]
  exact iSup_congr fun _ => (hneg z).symm ▸ neg_neg _

/-- **The transformed dual program lives on `H`, not on `F`.** Duality gives a supremum over `F`;
the concave image rule rewrites each value as a supremum over a fibre of `A'`, and the two suprema
collapse into one over `H`. Besides the exact-image hypothesis only `conj B f ≠ ⊥` is used, so
both conditions (a) and (b) can call it. -/
theorem iSup_concaveConj_compLin_sub_conj (hA : IsAdjointPair B B' A A')
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (hb : ∀ y : F, conj B f y ≠ ⊥) :
    (⨆ y : F, concaveConj B (compLin g A) y - conj B f y)
      = ⨆ z : H, concaveConj B' g z - conj B f (A' z) := by
  have key : ∀ y : F, concaveConj B (compLin g A) y - conj B f y
      = ⨆ z : H, ⨆ _ : A' z = y, (concaveConj B' g z - conj B f (A' z)) := by
    intro y
    rw [concaveConj_compLin hA himg y, EReal.iSup_sub_of_ne_bot _ (hb y)]
    refine iSup_congr fun z => ?_
    rw [EReal.iSup_sub_of_ne_bot _ (hb y)]
    exact iSup_congr fun hz => by rw [hz]
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun z => ?_)
  · rw [key y]
    exact iSup_le fun w => iSup_le fun _ =>
      le_iSup (fun v : H => concaveConj B' g v - conj B f (A' v)) w
  · refine le_trans ?_
      (le_iSup (fun y : F => concaveConj B (compLin g A) y - conj B f y) (A' z))
    rw [key (A' z)]
    exact le_iSup₂ (f := fun w (_ : A' w = A' z) => concaveConj B' g w - conj B f (A' w)) z rfl

/-- **Fenchel's duality theorem with a linear transformation**:
`inf (f - g A) = sup (g* - f* A')`.

The two hypotheses are the book's condition (a) split in two: `hex` makes `f` and `-(g A)` add
exactly, `himg` makes `g` pull back exactly along `A`, and
`ri (dom f) ∩ A⁻¹ (ri (dom g)) ≠ ∅` delivers both. -/
theorem fenchel_duality_comp (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    (⨅ x, f x - g (A x)) = ⨆ z : H, concaveConj B' g z - conj B f (A' z) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  have h31 : (⨅ x, f x - g (A x)) = ⨆ y : F, concaveConj B (compLin g A) y - conj B f y :=
    fenchel_duality hex'
  rw [h31]
  exact iSup_concaveConj_compLin_sub_conj hA himg hex'.conj_left_ne_bot

/-- **Attainment**: under exact addition and exact pullback the supremum of `g* - f* A'` is
attained. Two attainment statements chain — duality over `F`, then the image rule over the fibre —
with the degenerate common value `-∞` taken separately. -/
theorem exists_concaveConj_sub_conj_comp_eq (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    ∃ z : H, concaveConj B' g z - conj B f (A' z) = ⨅ x, f x - g (A x) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  rcases eq_or_ne (⨅ x, f x - g (A x)) ⊥ with hb | hb
  · have hle : concaveConj B' g 0 - conj B f (A' 0) ≤ ⨅ x, f x - g (A x) := by
      rw [fenchel_duality_comp hA hex himg]
      exact le_iSup (fun z : H => concaveConj B' g z - conj B f (A' z)) 0
    exact ⟨0, le_antisymm hle (by rw [hb]; exact bot_le)⟩
  obtain ⟨y, hy⟩ : ∃ y : F, concaveConj B (compLin g A) y - conj B f y = ⨅ x, f x - g (A x) :=
    exists_concaveConj_sub_conj_eq hex'
  have hyb : concaveConj B (compLin g A) y ≠ ⊥ := by
    intro hc
    exact hb (by rw [← hy, hc, sub_eq_add_neg, EReal.bot_add])
  have hlt : conj B (compLin (fun w => -(g w)) A) (-y) < ⊤ := by
    refine lt_of_le_of_ne le_top fun hc => hyb ?_
    rw [concaveConj_eq_neg_conj_neg]
    change -(conj B (compLin (fun w => -(g w)) A) (-y)) = ⊥
    rw [hc, EReal.neg_top]
  obtain ⟨z, hz, hzeq⟩ := himg.exists_conj_compLin_eq hlt
  refine ⟨-z, ?_⟩
  have hA'z : A' (-z) = y := by rw [map_neg, hz, neg_neg]
  have hval : concaveConj B' g (-z) = concaveConj B (compLin g A) y := by
    rw [concaveConj_eq_neg_conj_neg, neg_neg, hzeq, concaveConj_eq_neg_conj_neg]
    rfl
  rw [hA'z, hval, hy]

end Comp

/-! ### Condition (b): the closed case, with the infimum attained -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f g : E → EReal}

/-- The dual-side reading of the primal value: under condition (b), `inf (f - g)` is minus
`inf (f* - g*)`. This is `fenchel_duality` on the pair `(f*, g*)` over `B.flip`. -/
theorem iInf_sub_eq_neg_iInf_conj_sub (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = -(⨅ y : F, conj B f y - concaveConj B g y) := by
  have hgt : ∀ x, g x ≠ ⊤ := fun x hx => hg.proper.ne_bot x (by rw [hx, EReal.neg_top])
  have hbi : ∀ x, conj B.flip (conj B f) x = f x := fun x =>
    congrFun (biconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (biconcaveConj_eq_self (concaveFn_iff_convexFn_neg.2 hg.convex) hg.closed) x
  have hkey := fenchel_duality (B := B.flip) (f := conj B f) (g := concaveConj B g) hex
  rw [show (⨆ x : E, concaveConj B.flip (concaveConj B g) x - conj B.flip (conj B f) x)
        = ⨆ x : E, -(f x - g x) from
      iSup_congr fun x => by
        rw [hbi, hbc]
        exact (EReal.neg_sub_comm (.inl (hf.proper.ne_bot x)) (.inr (hgt x))).symm,
    ← EReal.neg_iInf] at hkey
  rw [hkey, neg_neg]

/-- **Duality under condition (b)**: `f` and `g` closed, with the conjugates adding exactly. The
equality is the same; what (b) buys is attainment on the *primal* side. -/
theorem fenchel_duality_of_closed (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = ⨆ y : F, concaveConj B g y - conj B f y := by
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hg.proper.dom_nonempty
  rw [iInf_sub_eq_neg_iInf_conj_sub hf hg hex, EReal.neg_iInf]
  exact iSup_congr fun y =>
    EReal.neg_sub_comm (.inl (conj_ne_bot hf.proper.dom_nonempty y))
      (.inr (concaveConj_ne_top hdc y))

/-- Under condition (b) the *infimum* of `f - g` is attained. -/
theorem exists_sub_eq_iInf (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn fun x => -(g x))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B g))) :
    ∃ x : E, f x - g x = ⨅ z, f z - g z := by
  have hgt : ∀ x, g x ≠ ⊤ := fun x hx => hg.proper.ne_bot x (by rw [hx, EReal.neg_top])
  have hbi : ∀ x, conj B.flip (conj B f) x = f x := fun x =>
    congrFun (biconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (biconcaveConj_eq_self (concaveFn_iff_convexFn_neg.2 hg.convex) hg.closed) x
  obtain ⟨x, hx⟩ := exists_concaveConj_sub_conj_eq (B := B.flip) (f := conj B f)
    (g := concaveConj B g) hex
  rw [hbi, hbc] at hx
  exact ⟨x, by rw [iInf_sub_eq_neg_iInf_conj_sub hf hg hex, ← hx,
    EReal.neg_sub_comm (.inr (hf.proper.ne_bot x)) (.inl (hgt x))]⟩

end Closed

/-! ### The transformed pair under condition (b) -/

section CompClosed

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal}

/-- **The transformed duality equality under condition (b)**: `f` and `g` closed with the
conjugates adding exactly. Where condition (a) delivers attainment on the dual side, (b) delivers
it on the *primal* side (`exists_sub_comp_eq_iInf`). -/
theorem fenchel_duality_comp_of_closed (hA : IsAdjointPair B B' A A')
    (hf : ClosedProperConvexFn f) (hgA : ClosedProperConvexFn fun x => -(g (A x)))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B (compLin g A))))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    (⨅ x, f x - g (A x)) = ⨆ z : H, concaveConj B' g z - conj B f (A' z) := by
  have h : (⨅ x, f x - g (A x)) = ⨆ y : F, concaveConj B (compLin g A) y - conj B f y :=
    fenchel_duality_of_closed hf hgA hex
  rw [h]
  exact iSup_concaveConj_compLin_sub_conj hA himg (conj_ne_bot hf.proper.dom_nonempty)

/-- Under condition (b) the *infimum* of `f - g A` is attained. -/
theorem exists_sub_comp_eq_iInf (hf : ClosedProperConvexFn f)
    (hgA : ClosedProperConvexFn fun x => -(g (A x)))
    (hex : IsExactSum B.flip (conj B f) (-(concaveConj B (compLin g A)))) :
    ∃ x : E, f x - g (A x) = ⨅ z, f z - g (A z) :=
  exists_sub_eq_iInf hf hgA hex

end CompClosed

/-! ### The Fenchel optimality conditions -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F}

/-- A difference of two `EReal`s that avoids both `∞ - ∞` collisions on the *stated* side is finite
as soon as it equals another such difference. -/
private theorem finite_of_sub_eq {a b c d : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (h : a - b = c - d) : a ≠ ⊤ ∧ b ≠ ⊥ ∧ c ≠ ⊥ ∧ d ≠ ⊤ := by
  induction a <;> induction b <;> induction c <;> induction d <;>
    simp_all [← EReal.coe_sub]

private theorem finite_of_add_eq {a d p : EReal} (ha : a ≠ ⊥) (hd : d ≠ ⊥) (hp : p ≠ ⊤)
    (h : a + d = p) : a ≠ ⊤ ∧ d ≠ ⊤ := by
  induction a <;> induction d <;> simp_all

private theorem finite_of_add_eq' {b c p : EReal} (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hp : p ≠ ⊥)
    (h : b + c = p) : b ≠ ⊥ ∧ c ≠ ⊥ := by
  induction b <;> induction c <;> simp_all

/-- Squeezed between `p ≤ a + d` and `b + c ≤ p`, the equality `a - b = c - d` says exactly that
both squeezes are tight. -/
private theorem sub_eq_sub_iff_of_le {a b c d p : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (hp1 : p ≠ ⊥) (hp2 : p ≠ ⊤) (h1 : p ≤ a + d) (h2 : b + c ≤ p) :
    a - b = c - d ↔ a + d = p ∧ b + c = p := by
  obtain ⟨π, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hp1 (lt_top_iff_ne_top.2 hp2)
  constructor
  · intro h
    obtain ⟨hat, hbb, hcb, hdt⟩ := finite_of_sub_eq ha hb hc hd h
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff,
      EReal.coe_eq_coe_iff]
    constructor <;> linarith
  · rintro ⟨e1, e2⟩
    obtain ⟨hat, hdt⟩ := finite_of_add_eq ha hd (EReal.coe_ne_top π) e1
    obtain ⟨hbb, hcb⟩ := finite_of_add_eq' hb hc (EReal.coe_ne_bot π) e2
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at e1
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at e2
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    linarith

/-- **Equality in the concave Fenchel inequality**: `g x + g*(y) = ⟨x, y⟩` says `-y ∈ ∂(-g) x`.
The book writes this as `x ∈ ∂g*(y)` with the superdifferential of a concave function,
`-∂(-g)`. -/
theorem neg_mem_subgradient_neg_iff_add_concaveConj_eq (hpg : Proper fun z => -(g z)) :
    -y ∈ subgradient B (fun z => -(g z)) x ↔ g x + concaveConj B g y = ((B x y : ℝ) : EReal) := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  have hct : concaveConj B g y ≠ ⊤ := concaveConj_ne_top hdc y
  have hpn : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, EReal.coe_neg]
  rw [hpg.mem_subgradient_iff_add_conj_eq, ← neg_concaveConj B g y, hpn, ← sub_eq_add_neg,
    ← EReal.neg_add (.inr hct) (.inl hgt), neg_inj]

/-- **The optimality conditions** at `A = id`: `x` and `y` are jointly optimal for the two problems
of Fenchel's duality theorem exactly when `y ∈ ∂f x` and `-y ∈ ∂(-g) x`. Both are Fenchel's
inequality holding with equality, and `f x - g x = g*(y) - f*(y)` squeezes the two inequalities
`⟨x, y⟩ ≤ f x + f*(y)` and `g x + g*(y) ≤ ⟨x, y⟩` together. -/
theorem sub_eq_concaveConj_sub_conj_iff (hpf : Proper f) (hpg : Proper fun z => -(g z)) :
    f x - g x = concaveConj B g y - conj B f y ↔
      y ∈ subgradient B f x ∧ -y ∈ subgradient B (fun z => -(g z)) x := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc y)
      (conj_ne_bot hpf.dom_nonempty y) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      (le_add_conj (hpf.ne_bot x) hpf.dom_nonempty y) (add_concaveConj_le B g x y),
    hpf.mem_subgradient_iff_add_conj_eq, neg_mem_subgradient_neg_iff_add_concaveConj_eq hpg]

/-- A point where the primal and dual values agree already minimises `f - g`. Only weak duality is
used. -/
theorem iInf_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - conj B f y) :
    (⨅ z, f z - g z) = f x - g x :=
  le_antisymm (iInf_le _ x) (le_iInf fun z => by
    rw [h]; exact concaveConj_sub_conj_le_sub B f g z y)

/-- The same point maximises `g* - f*`. -/
theorem iSup_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - conj B f y) :
    (⨆ w : F, concaveConj B g w - conj B f w) = concaveConj B g y - conj B f y :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_conj_le_sub B f g x w)
    (le_iSup (fun w : F => concaveConj B g w - conj B f w) y)

/-- At `A = id`: under exact addition, `x` minimises `f - g` exactly when it carries a Kuhn–Tucker
pair. -/
theorem iInf_sub_eq_iff_exists_kuhnTucker (hex : IsExactSum B f (-g)) (x : E) :
    (⨅ z, f z - g z) = f x - g x ↔
      ∃ y : F, y ∈ subgradient B f x ∧ -y ∈ subgradient B (fun z => -(g z)) x := by
  have hpf : Proper f := hex.proper_left
  have hpg : Proper fun z => -(g z) := hex.proper_right
  constructor
  · intro hmin
    obtain ⟨y, hy⟩ := exists_concaveConj_sub_conj_eq hex
    exact ⟨y, (sub_eq_concaveConj_sub_conj_iff hpf hpg).1 (hmin.symm.trans hy.symm)⟩
  · rintro ⟨y, hy⟩
    exact iInf_sub_eq_of_sub_eq ((sub_eq_concaveConj_sub_conj_iff hpf hpg).2 hy)

end Optimality

/-! ### Optimality conditions for the transformed pair of problems

A pair `(x, z)` is jointly optimal for `inf (f - g A)` and `sup (g* - f* A')` exactly when
`A' z ∈ ∂f x` and `A x` lies in the superdifferential of `g*` at `z`. The superdifferential of a
concave function is `-∂` of its negative, so the second condition reads `-z ∈ ∂(-g)(A x)` and no
new notion is needed.

These are the Kuhn–Tucker conditions for the transformed pair of programs. -/

section OptimalityComp

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal} {x : E} {z : H}

/-- **Weak duality for the transformed problem**: every value of `g* - f* A'` is below every value
of `f - g A`. Nothing is needed beyond the adjointness datum identifying `⟨A x, z⟩'` with
`⟨x, A' z⟩`. -/
theorem concaveConj_sub_conj_comp_le_sub (hA : IsAdjointPair B B' A A') (x : E) (z : H) :
    concaveConj B' g z - conj B f (A' z) ≤ f x - g (A x) := by
  refine sub_le_sub_of_le_sub_of_sub_le (p := B x (A' z)) ?_ (sub_le_conj B f x (A' z))
  rw [← hA x z]
  exact concaveConj_le_sub B' g (A x) z

/-- `x` and `z` are jointly optimal for the two transformed programs exactly when `A' z ∈ ∂f x`
and `-z ∈ ∂(-g)(A x)`. The proof is the one at `A = id`, with the shared finite value
`⟨x, A' z⟩ = ⟨A x, z⟩'`. -/
theorem sub_comp_eq_concaveConj_sub_conj_iff (hA : IsAdjointPair B B' A A') (hpf : Proper f)
    (hpg : Proper fun w => -(g w)) :
    f x - g (A x) = concaveConj B' g z - conj B f (A' z) ↔
      A' z ∈ subgradient B f x ∧ -z ∈ subgradient B' (fun w => -(g w)) (A x) := by
  have hgt : g (A x) ≠ ⊤ := fun hc => hpg.ne_bot (A x) (by rw [hc, EReal.neg_top])
  have hdc : (domConcave g).Nonempty := by
    rw [domConcave_eq_dom_neg]
    exact hpg.dom_nonempty
  have hp : ((B' (A x) z : ℝ) : EReal) = ((B x (A' z) : ℝ) : EReal) := by rw [hA x z]
  have h2 : g (A x) + concaveConj B' g z ≤ ((B x (A' z) : ℝ) : EReal) := by
    rw [← hp]
    exact add_concaveConj_le B' g (A x) z
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc z)
      (conj_ne_bot hpf.dom_nonempty (A' z)) (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)
      (le_add_conj (hpf.ne_bot x) hpf.dom_nonempty (A' z)) h2,
    hpf.mem_subgradient_iff_add_conj_eq,
    neg_mem_subgradient_neg_iff_add_concaveConj_eq (B := B') (g := g) (x := A x) (y := z) hpg, hp]

/-- A point where the primal and dual values agree already minimises `f - g A`. -/
theorem iInf_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - conj B f (A' z)) :
    (⨅ w, f w - g (A w)) = f x - g (A x) :=
  le_antisymm (iInf_le _ x) (le_iInf fun w => by
    rw [h]; exact concaveConj_sub_conj_comp_le_sub hA w z)

/-- The same pair maximises `g* - f* A'`. -/
theorem iSup_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - conj B f (A' z)) :
    (⨆ w : H, concaveConj B' g w - conj B f (A' w)) = concaveConj B' g z - conj B f (A' z) :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_conj_comp_le_sub hA x w)
    (le_iSup (fun w : H => concaveConj B' g w - conj B f (A' w)) z)

/-- Under the two exactness hypotheses, `x` minimises `f - g A` exactly when it carries a
Kuhn–Tucker pair. The forward direction needs the attainment clause to produce the multiplier; the
backward one is weak duality alone. -/
theorem iInf_sub_comp_eq_iff_exists_kuhnTucker (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun w => -(g (A w)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (x : E) :
    (⨅ w, f w - g (A w)) = f x - g (A x) ↔
      ∃ z : H, A' z ∈ subgradient B f x ∧ -z ∈ subgradient B' (fun w => -(g w)) (A x) := by
  have hpf : Proper f := hex.proper_left
  have hpg : Proper fun w => -(g w) := himg.proper
  constructor
  · intro hmin
    obtain ⟨z, hz⟩ := exists_concaveConj_sub_conj_comp_eq hA hex himg
    exact ⟨z, (sub_comp_eq_concaveConj_sub_conj_iff hA hpf hpg).1 (hmin.symm.trans hz.symm)⟩
  · rintro ⟨z, hz⟩
    exact iInf_sub_comp_eq_of_sub_eq hA ((sub_comp_eq_concaveConj_sub_conj_iff hA hpf hpg).2 hz)

end OptimalityComp

/-! ### Minimising over a convex cone -/

section Cone

open Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {K : Set E} {x : E} {y : F}

/-- The book's `K*` is the *negative* of the polar cone `K°`. `Set` negation is a preimage, so
`y ∈ -K°` unfolds to `-y ∈ K°`. -/
theorem mem_neg_polarCone : y ∈ -(polarCone B K) ↔ ∀ z ∈ K, 0 ≤ B z y := by
  simp [Set.mem_neg, mem_polarCone, map_neg]

omit [Module ℝ F] in
/-- Negating a set moves the negation onto the argument of its indicator. -/
private theorem indicatorFn_neg_set (S : Set F) (w : F) :
    indicatorFn (-S) w = indicatorFn S (-w) := by
  by_cases hw : -w ∈ S
  · rw [indicatorFn_of_mem (Set.mem_neg.2 hw), indicatorFn_of_mem hw]
  · rw [indicatorFn_of_notMem fun hc => hw (Set.mem_neg.1 hc), indicatorFn_of_notMem hw]

/-- A constrained infimum is an unconstrained infimum of the function plus an indicator, provided
the function never takes `⊥`. -/
theorem iInf_mem_eq_iInf_add_indicatorFn {α : Type*} (φ : α → EReal) (S : Set α)
    (hb : ∀ z, φ z ≠ ⊥) : (⨅ z ∈ S, φ z) = ⨅ z, (φ + indicatorFn S) z := by
  refine iInf_congr fun z => ?_
  by_cases hz : z ∈ S
  · rw [iInf_pos hz, Pi.add_apply, indicatorFn_of_mem hz, add_zero]
  · rw [iInf_neg hz, Pi.add_apply, indicatorFn_of_notMem hz]
    exact (EReal.add_top_of_ne_bot (hb z)).symm

/-- **The cone form**: minimising a convex function over a convex cone `K` is dual to minimising
its conjugate over `K* = -K°`. Rather than through duality with `g = -δ(· | K)`, this goes to the
source both proofs share: `inf h = -h*(0)` applied to `h = f + δ(· | K)`, with the sum's conjugate
split at the origin and the conjugate of an indicator evaluating the second factor. The `0 - y`
produced by the splitting is the sign flip turning `K°` into `K*`. -/
theorem iInf_add_indicatorFn_eq_neg_iInf_conj_add_indicatorFn
    (hex : IsExactSum B f (indicatorFn K)) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    (⨅ z, (f + indicatorFn K) z) = -(⨅ w, (conj B f + indicatorFn (-(polarCone B K))) w) := by
  rw [iInf_eq_neg_conj_zero B, hex.conj_add_apply 0, iInf_neg_comp]
  congr 1
  refine iInf_congr fun w => ?_
  rw [Pi.add_apply, conj_indicatorFn_eq_indicatorFn_polarCone hK hne, zero_sub, neg_neg,
    indicatorFn_neg_set]

/-- The same in constrained notation: `inf {f x | x ∈ K} = -inf {f*(y) | y ∈ K*}`. -/
theorem iInf_mem_eq_neg_iInf_mem_neg_polarCone (hex : IsExactSum B f (indicatorFn K))
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone B K), conj B f w) := by
  rw [iInf_mem_eq_iInf_add_indicatorFn f K hex.proper_left.ne_bot,
    iInf_mem_eq_iInf_add_indicatorFn (conj B f) _ (conj_ne_bot hex.proper_left.dom_nonempty)]
  exact iInf_add_indicatorFn_eq_neg_iInf_conj_add_indicatorFn hex hK hne

/-- **Weak duality for the cone program**: every dual value is below every primal value. -/
theorem neg_conj_le_of_mem_neg_polarCone (hxK : x ∈ K) {w : F} (hwK : w ∈ -(polarCone B K)) :
    -(conj B f w) ≤ f x := by
  have hle : -(f x) ≤ conj B f w := by
    refine le_trans (le_of_eq (zero_sub (f x)).symm) (le_trans ?_ (sub_le_conj B f x w))
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add (by exact_mod_cast mem_neg_polarCone.1 hwK x hxK) le_rfl
  rw [← EReal.neg_le_neg_iff, neg_neg] at hle
  exact hle

/-- `f x + f*(y) = 0` pins `f*(y)` to `-f x`; both values are then finite. -/
private theorem neg_conj_eq_of_add_eq_zero (hp : Proper f) (hz : f x + conj B f y = 0) :
    -(conj B f y) = f x := by
  have hcb : conj B f y ≠ ⊥ := conj_ne_bot hp.dom_nonempty y
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have hft : f x ≠ ⊤ := fun hc => by
    rw [hc, EReal.top_add_of_ne_bot hcb] at hz
    exact absurd hz (by simp)
  have hct : conj B f y ≠ ⊤ := fun hc => by
    rw [hc, EReal.add_top_of_ne_bot hfb] at hz
    exact absurd hz (by simp)
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hfb (lt_top_iff_ne_top.2 hft)
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hct)
  rw [hr, hs, ← EReal.coe_add] at hz
  rw [hs, hr, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
  have : r + s = 0 := by exact_mod_cast hz
  linarith

/-- **Optimality conditions for the cone program**: for `x ∈ K` and `y ∈ K*` the primal and dual
values agree exactly when `y ∈ ∂f x` and `⟨x, y⟩ = 0`. These are the Fenchel conditions for
`g = -δ(· | K)`. -/
theorem add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero (hp : Proper f) (hxK : x ∈ K)
    (hyK : y ∈ -(polarCone B K)) :
    f x + conj B f y = 0 ↔ y ∈ subgradient B f x ∧ (B x y : ℝ) = 0 := by
  have hxy : (0 : ℝ) ≤ B x y := mem_neg_polarCone.1 hyK x hxK
  rw [hp.mem_subgradient_iff_add_conj_eq]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, EReal.coe_zero]⟩
  have hle : ((B x y : ℝ) : EReal) ≤ 0 := h ▸ hp.le_add_conj x y
  have hzero : (B x y : ℝ) = 0 := le_antisymm (by exact_mod_cast hle) hxy
  exact ⟨by rw [h, hzero, EReal.coe_zero], hzero⟩

/-- The optimality conditions make `x` optimal for the primal cone program. Only `⟨x, y⟩ = 0` and
`y ∈ K*` are used. -/
theorem forall_le_of_mem_subgradient_of_pairing_eq_zero (hyK : y ∈ -(polarCone B K))
    (hy : y ∈ subgradient B f x) (hxy : (B x y : ℝ) = 0) {z : E} (hz : z ∈ K) : f x ≤ f z := by
  have hzy : (0 : ℝ) ≤ B (z - x) y := by
    rw [map_sub, LinearMap.sub_apply, hxy, sub_zero]
    exact mem_neg_polarCone.1 hyK z hz
  exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hzy)) (hy z)

/-- The optimality conditions make `y` optimal for the dual cone program. -/
theorem conj_le_conj_of_mem_subgradient_of_pairing_eq_zero (hp : Proper f) (hxK : x ∈ K)
    (hy : y ∈ subgradient B f x) (hxy : (B x y : ℝ) = 0) {w : F} (hwK : w ∈ -(polarCone B K)) :
    conj B f y ≤ conj B f w := by
  have hsum : f x + conj B f y = 0 := by
    rw [hp.mem_subgradient_iff_add_conj_eq.1 hy, hxy, EReal.coe_zero]
  have hxeq : -(conj B f y) = f x := neg_conj_eq_of_add_eq_zero hp hsum
  rw [← EReal.neg_le_neg_iff, hxeq]
  exact neg_conj_le_of_mem_neg_polarCone hxK hwK

/-! ### Attainment of the two infima -/

/-- **The dual value read at the origin**: `(f + δ(·|K))* 0` *is* the dual infimum
`inf {f*(y) | y ∈ K*}`. This is what turns exactness of the sum into attainment. -/
theorem conj_add_indicatorFn_zero_eq_iInf_mem_neg_polarCone
    (hex : IsExactSum B f (indicatorFn K)) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    conj B (f + indicatorFn K) 0 = ⨅ w ∈ -(polarCone B K), conj B f w := by
  rw [conj_zero_eq_neg_iInf, ← iInf_mem_eq_iInf_add_indicatorFn f K hex.proper_left.ne_bot,
    iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne, neg_neg]

/-- **Attainment under condition (a)**: as soon as `f` and `δ(·|K)` add exactly, the *dual*
infimum is attained. It is read straight off `IsExactSum`: the splitting `0 = y₁ + y₂` at the
origin already is a minimising `y₁ ∈ K*`, since the second conjugate factor is the indicator of
`K°`. The degenerate branch `y₂ ∉ K°` forces the dual infimum to `⊤`, attained at the origin. -/
theorem exists_mem_neg_polarCone_conj_eq_iInf (hex : IsExactSum B f (indicatorFn K))
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) :
    ∃ y ∈ -(polarCone B K), conj B f y = ⨅ w ∈ -(polarCone B K), conj B f w := by
  obtain ⟨y₁, y₂, hsum, hle⟩ := hex.exact_le 0
  rw [conj_indicatorFn_eq_indicatorFn_polarCone hK hne,
    conj_add_indicatorFn_zero_eq_iInf_mem_neg_polarCone hex hK hne] at hle
  by_cases hy₂ : y₂ ∈ polarCone B K
  · have hy₁ : y₁ ∈ -(polarCone B K) := by
      rw [Set.mem_neg, neg_eq_of_add_eq_zero_right hsum]
      exact hy₂
    rw [indicatorFn_of_mem hy₂, add_zero] at hle
    exact ⟨y₁, hy₁, le_antisymm hle (iInf₂_le y₁ hy₁)⟩
  · rw [indicatorFn_of_notMem hy₂,
      EReal.add_top_of_ne_bot (hex.conj_left_ne_bot y₁)] at hle
    have h0 : (0 : F) ∈ -(polarCone B K) := zero_mem_neg_polarCone B K
    have htop : (⨅ w ∈ -(polarCone B K), conj B f w) = ⊤ := top_le_iff.1 hle
    have hge : (⨅ w ∈ -(polarCone B K), conj B f w) ≤ conj B f 0 := iInf₂_le (0 : F) h0
    rw [htop, top_le_iff] at hge
    exact ⟨0, h0, by rw [hge, htop]⟩

/-- The two infima *added* rather than negated: when the dual infimum is finite the duality
equation says the two values sum to zero. -/
theorem iInf_mem_add_iInf_mem_neg_polarCone_eq_zero (hex : IsExactSum B f (indicatorFn K))
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (hbot : (⨅ w ∈ -(polarCone B K), conj B f w) ≠ ⊥)
    (htop : (⨅ w ∈ -(polarCone B K), conj B f w) ≠ ⊤) :
    (⨅ z ∈ K, f z) + (⨅ w ∈ -(polarCone B K), conj B f w) = 0 := by
  obtain ⟨m, hm⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 htop)
  rw [iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne, hm, ← EReal.coe_neg,
    ← EReal.coe_add, neg_add_cancel, EReal.coe_zero]

/-! ### Minimising over a subspace -/

/-- The polar cone of a **subspace** is closed under negation, so `K*` and `K°` coincide there:
both are the annihilator `L^⊥ = {y | ∀ x ∈ L, ⟨x, y⟩ = 0}`. -/
theorem neg_polarCone_coe_submodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    -(polarCone B (M : Set E)) = polarCone B (M : Set E) := by
  ext w
  rw [Set.mem_neg, polarCone_coe_submodule']
  refine ⟨fun h u hu => ?_, fun h u hu => ?_⟩
  · have hu' := h u hu
    rwa [map_neg, neg_eq_zero] at hu'
  · rw [map_neg, h u hu, neg_zero]

/-- `inf {f x | x ∈ L} = -inf {f*(y) | y ∈ L^⊥}` for a subspace `L`, where `K* = -K°` collapses to
`K°` itself. -/
theorem iInf_mem_submodule_eq_neg_iInf_mem_polarCone {M : Submodule ℝ E}
    (hex : IsExactSum B f (indicatorFn (M : Set E))) :
    (⨅ z ∈ (M : Set E), f z) = -(⨅ w ∈ polarCone B (M : Set E), conj B f w) := by
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex (fun _ ha => smul_coe_submodule M ha)
    ⟨0, M.zero_mem⟩
  rwa [neg_polarCone_coe_submodule] at h

/-- Over a subspace the orthogonality `⟨x, y⟩ = 0` is automatic, so the primal and dual values
agree exactly when `y ∈ ∂f x`. -/
theorem add_conj_eq_zero_iff_mem_subgradient_of_mem_submodule {M : Submodule ℝ E} (hp : Proper f)
    (hxM : x ∈ M) (hyM : y ∈ polarCone B (M : Set E)) :
    f x + conj B f y = 0 ↔ y ∈ subgradient B f x := by
  have hxy : (B x y : ℝ) = 0 := by
    rw [polarCone_coe_submodule'] at hyM
    exact hyM x hxM
  have hyK : y ∈ -(polarCone B (M : Set E)) := by
    rw [neg_polarCone_coe_submodule]
    exact hyM
  rw [add_conj_eq_zero_iff_mem_subgradient_and_pairing_eq_zero hp hxM hyK]
  exact ⟨And.left, fun h => ⟨h, hxy⟩⟩

end Cone

/-! ### Attainment of the primal infimum

Attainment of the *primal* infimum is Rockafellar's condition (b), which is condition (a) read on
the dual pair. It is the previous section's statement applied to `f*` and `K*`, with `K** = K`
(`neg_polarCone_neg_polarCone`) and `f** = f` (Fenchel–Moreau) closing the circle; the bipolar is
what makes this section layer C rather than layer A. -/

section ConeClosed

open Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal} {K : Set E}

/-- **Attainment under condition (b)**: when `f*` and `δ(·|K*)` add exactly, the *primal* infimum
is attained. `biconj B f = f` is taken as a hypothesis rather than derived, so that the statement
stays free of a compatibility assumption on the `F` side. -/
theorem exists_mem_eq_iInf_of_isExactSum_conj (hbi : biconj B f = f)
    (hex : IsExactSum B.flip (conj B f) (indicatorFn (-(polarCone B K))))
    (hconv : Convex ℝ K) (hK : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (hcl : IsClosed K) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z := by
  have hbi' : conj B.flip (conj B f) = f := hbi
  have h := exists_mem_neg_polarCone_conj_eq_iInf (B := B.flip) (K := -(polarCone B K)) hex
    (fun a ha => smul_neg_polarCone B K a ha) (neg_polarCone_nonempty B K)
  rwa [neg_polarCone_neg_polarCone hconv hK hne hcl, hbi'] at h

end ConeClosed

end ConvexAnalysis
