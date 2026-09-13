import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Hull

/-!
# The complete lattice of convex functions

The convex functions on `E`, pointwise ordered, form a complete lattice. The least upper bound of a
family is the pointwise supremum, since a pointwise supremum of convex functions is convex. The
greatest lower bound is *not* the pointwise infimum, which need not be convex; it is the convex hull
`conv {f i}`, the greatest convex minorant of the family. `ConvexFns.exists_coe_inf_lt_inf` makes
the difference concrete on `ℝ`: the indicators of `{0}` and `{1}` have pointwise minimum `⊤` at
`1/2`, while their meet, the indicator of `[0, 1]`, is `0` there. So the coercion to `E → EReal` is
an `sSupHom` but cannot be an `sInfHom`.

## Main definitions

* `ConvexFns E` — the convex functions on `E` as a type, with `ConvexFns.instCompleteLattice`.
* `ConvexFns.coeOrderEmbedding`, `ConvexFns.coeSSupHom` — the coercion to `E → EReal` as an order
  embedding and as an `sSupHom`.

## Main results

* `ConvexFns.coe_sSup`, `ConvexFns.coe_sup` — the join is the pointwise supremum.
* `ConvexFns.coe_iInf`, `ConvexFns.coe_inf` — the meet is `convFn`, resp. `convFn₂`.
* `ConvexFns.coe_top`, `ConvexFns.coe_bot` — the extreme elements are the constants `⊤` and `⊥`.
* `ConvexFns.not_coe_inf_eq_inf` — the meet is genuinely not the pointwise infimum.

## Implementation notes

`ConvexFns E` is a reducible abbreviation for the subtype `gci_val_convHullFn` is stated about, so
that coreflection lifts to a `CompleteLattice` directly and the order is definitionally the
pointwise one.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §5.
-/

open Set

namespace ConvexAnalysis

/-! ### The type of convex functions -/

/-- The **convex functions on `E`**, bundled as a type carrying the pointwise order. -/
abbrev ConvexFns (E : Type*) [AddCommGroup E] [Module ℝ E] := {f : E → EReal // ConvexFn f}

namespace ConvexFns

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The convex functions on `E`, pointwise ordered, form a **complete lattice**. The instance is
the coreflection `gci_val_convHullFn` transported by
`GaloisCoinsertion.liftCompleteLattice`, so every field is the corresponding operation on
`E → EReal` followed by `convHullFn`; the lemmas below evaluate that hull. -/
noncomputable instance instCompleteLattice : CompleteLattice (ConvexFns E) :=
  gci_val_convHullFn.liftCompleteLattice

/-- The coercion `ConvexFns E → (E → EReal)` is an **order embedding**: `f ≤ g` in the lattice of
convex functions means exactly `f x ≤ g x` for every `x`. -/
noncomputable def coeOrderEmbedding : ConvexFns E ↪o (E → EReal) := OrderEmbedding.subtype _

@[simp]
theorem coe_coeOrderEmbedding :
    ⇑(coeOrderEmbedding : ConvexFns E ↪o (E → EReal)) = Subtype.val := rfl

/-- A convex function is a member of the lattice, and only convex functions are. -/
@[simp]
theorem mem_range_coe {g : E → EReal} :
    g ∈ Set.range (Subtype.val : ConvexFns E → (E → EReal)) ↔ ConvexFn g :=
  ⟨fun ⟨f, hf⟩ => hf ▸ f.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

/-! ### Suprema: the join is pointwise -/

/-- **The least upper bound is the pointwise supremum** (Rockafellar's "`sup {f i}`"). -/
@[simp]
theorem coe_sSup (s : Set (ConvexFns E)) :
    ((sSup s : ConvexFns E) : E → EReal) = sSup (Subtype.val '' s) := by
  refine convHullFn_eq_self ?_
  have h : sSup (Subtype.val '' s) = fun x => ⨆ f : s, ((f : ConvexFns E) : E → EReal) x := by
    rw [sSup_image']
    exact funext fun x => iSup_apply
  rw [h]
  exact convexFn_iSup fun f : s => (f : ConvexFns E).2

theorem coe_iSup {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) = ⨆ i, (f i : E → EReal) := by
  rw [iSup, coe_sSup, ← Set.range_comp]
  rfl

@[simp]
theorem coe_iSup_apply {ι : Sort*} (f : ι → ConvexFns E) (x : E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) x = ⨆ i, (f i : E → EReal) x := by
  rw [coe_iSup, iSup_apply]

theorem coe_sSup_apply (s : Set (ConvexFns E)) (x : E) :
    ((sSup s : ConvexFns E) : E → EReal) x = ⨆ f ∈ s, (f : E → EReal) x := by
  rw [coe_sSup, sSup_image', iSup_apply, iSup_subtype]

/-- The binary case: the join of two convex functions is their pointwise maximum. -/
@[simp]
theorem coe_sup (f g : ConvexFns E) :
    ((f ⊔ g : ConvexFns E) : E → EReal) = (f : E → EReal) ⊔ (g : E → EReal) :=
  convHullFn_eq_self (f.2.sup g.2)

/-- The coercion to `E → EReal` as an **`sSupHom`**: it preserves arbitrary suprema. There is no
companion `sInfHom` — see `ConvexFns.not_coe_inf_eq_inf`. -/
noncomputable def coeSSupHom : sSupHom (ConvexFns E) (E → EReal) where
  toFun := Subtype.val
  map_sSup' := coe_sSup

@[simp]
theorem coe_coeSSupHom : ⇑(coeSSupHom : sSupHom (ConvexFns E) (E → EReal)) = Subtype.val := rfl

/-! ### Infima: the meet is a convex hull -/

/-- **The greatest lower bound is a convex hull**, `conv` of the pointwise infimum. -/
theorem coe_sInf (s : Set (ConvexFns E)) :
    ((sInf s : ConvexFns E) : E → EReal) = convHullFn (sInf (Subtype.val '' s)) := rfl

/-- **Rockafellar's `conv {f i | i ∈ I}`.** The greatest lower bound of a family of convex functions
is their convex hull `convFn`, *not* their pointwise infimum, which is generally not convex. -/
@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨅ i, f i : ConvexFns E) : E → EReal) = convFn (fun i => (f i : E → EReal)) := by
  rw [convFn_eq_convHullFn_iInf, iInf, coe_sInf, ← Set.range_comp]
  refine congrArg convHullFn (funext fun x => ?_)
  change (⨅ i, (f i : E → EReal)) x = ⨅ i, (f i : E → EReal) x
  exact iInf_apply

/-- The binary case: the meet of two convex functions is their binary convex hull `convFn₂`. -/
@[simp]
theorem coe_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) = convFn₂ (f : E → EReal) (g : E → EReal) :=
  convHullFn_inf _ _

/-- The meet lies below the pointwise infimum, and generally strictly:
`ConvexFns.exists_coe_inf_lt_inf`. -/
theorem coe_inf_le_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) ≤ (f : E → EReal) ⊓ (g : E → EReal) :=
  (coe_inf f g).trans_le (convFn₂_le_inf _ _)

/-! ### The extreme elements -/

/-- The greatest convex function is the constant `⊤`. -/
@[simp]
theorem coe_top : ((⊤ : ConvexFns E) : E → EReal) = ⊤ :=
  convHullFn_eq_self (convexFn_const ⊤)

/-- The least convex function is the constant `⊥`. -/
@[simp]
theorem coe_bot : ((⊥ : ConvexFns E) : E → EReal) = ⊥ :=
  convHullFn_eq_self (convexFn_const ⊥)

end Module

/-! ### The meet is not the pointwise infimum -/

/-- **The meet of `ConvexFns` is strictly below the pointwise infimum, in general.** -/
theorem exists_coe_inf_lt_inf :
    ∃ (f g : ConvexFns ℝ) (x : ℝ),
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) x < ((f : ℝ → EReal) ⊓ (g : ℝ → EReal)) x := by
  refine ⟨⟨indicatorFn ({0} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 0)⟩,
    ⟨indicatorFn ({1} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 1)⟩, 1 / 2, ?_⟩
  rw [coe_inf, Pi.inf_apply]
  exact convFn₂_indicatorFn_lt_inf

/-- **The coercion `ConvexFns E → (E → EReal)` is not an `sInfHom`**, not even a lattice
homomorphism: it does not commute with binary meets. Contrast `ConvexFns.coeSSupHom`. -/
theorem not_coe_inf_eq_inf :
    ¬ ∀ f g : ConvexFns ℝ,
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) = (f : ℝ → EReal) ⊓ (g : ℝ → EReal) := by
  obtain ⟨f, g, x, hx⟩ := exists_coe_inf_lt_inf
  exact fun h => absurd (congrFun (h f g) x) hx.ne

end ConvexFns

end ConvexAnalysis
