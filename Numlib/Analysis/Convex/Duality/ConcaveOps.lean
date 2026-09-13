import Numlib.Analysis.Convex.Duality.ConcaveConj
import Numlib.Analysis.Convex.Duality.Exact

/-!
# Supremal convolution and the conjugate of a concave sum

Two convex functions are combined by infimal convolution `f₁ □ f₂`, and the conjugate of a sum is
that convolution. Two concave functions are combined by **supremal** convolution
`(g □ h)(x) = sup {g x₁ + h x₂ ∣ x₁ + x₂ = x}`, and the *concave* conjugate of a sum is that: the
concave orientation of the same duality, which the adjoint of `F₁ □ F₂` needs.

## Main definitions

* `supConv g h` — supremal convolution, defined as `-((-g) □ (-h))`.

## Main results

* `infConv_neg` — infimal convolution commutes with negating the argument.
* `supConv_apply` — the supremum formula, when neither function reaches `+∞`.
* `concaveConj_add_of_isExactSum` — the concave conjugate of a sum is the supremal convolution of
  the conjugates, under the hypothesis `IsExactSum B (-g₁) (-g₂)`
  ([rockafellar1970convex] Theorem 16.4).

## Implementation notes

`supConv` negates *values*, not arguments, so it inherits commutativity, associativity and the
effective-domain formula from `infConv`. The reflection of the argument that does appear,
`infConv_neg`, comes from the sign dictionary `neg_concaveConj`, which reflects on the dual side;
the proof of the concave conjugate formula crosses it once.

The two properness fields of `IsExactSum B (-g₁) (-g₂)` say exactly that neither `gᵢ` takes the
value `+∞`, which is where the classical proof case-splits; the relative-interior condition
supplies the third field (`IsExactSum.of_relint`). No case distinction survives into the statement.

## References

* [rockafellar1970convex] §16 and §38.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### `EReal` bookkeeping -/

/-- Negation distributes over an `EReal` sum as soon as neither summand is `⊥`: the symmetric
special case of Mathlib's `EReal.neg_add`, and with it the whole sign dictionary for sums. -/
theorem neg_add_of_ne_bot {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥) : -(u + v) = -u + -v :=
  (EReal.neg_add (.inl hu) (.inr hv)).trans (sub_eq_add_neg _ _)

/-! ### Infimal convolution and reflection -/

section InfConvNeg

variable {E : Type*} [AddCommGroup E]

/-- **Infimal convolution commutes with negating the argument**: `(f ∘ -) □ (g ∘ -) = (f □ g) ∘ -`.
Negation in the first coordinate is an additive bijection of `E × ℝ`, so it carries the sum of the
epigraphs to the sum of their images. -/
theorem infConv_neg (f g : E → EReal) (x : E) :
    infConv (fun w => f (-w)) (fun w => g (-w)) x = infConv f g (-x) := by
  have key : ∀ μ : ℝ, ((x, μ) : E × ℝ) ∈ epi (fun w => f (-w)) + epi (fun w => g (-w))
      ↔ ((-x, μ) : E × ℝ) ∈ epi f + epi g := by
    intro μ
    constructor
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), mk_mem_epi.2 (mk_mem_epi.1 ha), (-b, β),
        mk_mem_epi.2 (mk_mem_epi.1 hb), ?_⟩
      change ((-a, α) : E × ℝ) + (-b, β) = (-x, μ)
      rw [Prod.mk_add_mk, ← neg_add, hab'.1, hab'.2]
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (-x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), ?_, (-b, β), ?_, ?_⟩
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 ha)
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 hb)
      · change ((-a, α) : E × ℝ) + (-b, β) = (x, μ)
        rw [Prod.mk_add_mk, ← neg_add, hab'.1, neg_neg, hab'.2]
  exact le_antisymm (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).2 hμ))
    (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).1 hμ))

end InfConvNeg

/-! ### Supremal convolution -/

section SupConv

variable {E : Type*} [AddCommGroup E]

/-- **Supremal convolution** of two concave functions, Rockafellar's `□` in its concave
orientation: `(g □ h)(x) = sup {g x₁ + h x₂ | x₁ + x₂ = x}`. Defined as `-((-g) □ (-h))`, so that
every property of `infConv` transfers by one negation; the supremum formula is `supConv_apply`. -/
noncomputable def supConv (g h : E → EReal) : E → EReal :=
  fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x)

theorem supConv_def (g h : E → EReal) :
    supConv g h = fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x) := rfl

@[simp] theorem neg_supConv (g h : E → EReal) (x : E) :
    -(supConv g h x) = infConv (fun w => -(g w)) (fun w => -(h w)) x := neg_neg _

theorem supConv_comm (g h : E → EReal) : supConv g h = supConv h g :=
  funext fun x => congrArg Neg.neg (congrFun (infConv_comm _ _) x)

/-- **The formula for the concave `□`**: `(g □ h)(x) = sup {g (x - y) + h y | y}`. The hypotheses
mirror those of `infConv_apply`: without them the summand is `∞ - ∞` where one function is `+∞` and
the other `-∞`, and `EReal` resolves it on the wrong side. -/
theorem supConv_apply {g h : E → EReal} (hg : ∀ x, g x ≠ ⊤) (hh : ∀ x, h x ≠ ⊤) (x : E) :
    supConv g h x = ⨆ y, g (x - y) + h y := by
  have h1 : infConv (fun w => -(g w)) (fun w => -(h w)) x
      = ⨅ y, -(g (x - y)) + -(h y) :=
    infConv_apply (fun z => by simpa using hg z) (fun z => by simpa using hh z) x
  change -(infConv (fun w => -(g w)) (fun w => -(h w)) x) = _
  rw [h1, EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [neg_add_of_ne_bot (by simpa using hg (x - y)) (by simpa using hh y), neg_neg, neg_neg]

end SupConv

/-! ### The concave conjugate of a sum -/

section ConcaveConjSum

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The conjugate of a concave sum**: the concave conjugate of a sum is the supremal
convolution of the concave conjugates, `(g₁ + g₂)* = g₁* □ g₂*`.

The hypothesis is the convex `IsExactSum` interface applied to `-g₁` and `-g₂`. -/
theorem concaveConj_add_of_isExactSum {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g₁ g₂ : E → EReal}
    (hex : IsExactSum B (fun x => -(g₁ x)) (fun x => -(g₂ x))) :
    concaveConj B (fun x => g₁ x + g₂ x)
      = supConv (concaveConj B g₁) (concaveConj B g₂) := by
  have hg₁ : ∀ x, g₁ x ≠ ⊤ := fun x hx => hex.proper_left.ne_bot x (by simp [hx])
  have hg₂ : ∀ x, g₂ x ≠ ⊤ := fun x hx => hex.proper_right.ne_bot x (by simp [hx])
  have hsum : (fun x => -(g₁ x + g₂ x)) = (fun x => -(g₁ x)) + (fun x => -(g₂ x)) :=
    funext fun x => (EReal.neg_add (.inr (hg₂ x)) (.inl (hg₁ x))).trans (sub_eq_add_neg _ _)
  funext v
  have step1 : concaveConj B (fun x => g₁ x + g₂ x) v
      = -(conj B ((fun x => -(g₁ x)) + (fun x => -(g₂ x))) (-v)) := by
    rw [← hsum]
    exact concaveConj_eq_neg_conj_neg B (fun x => g₁ x + g₂ x) v
  have step2 : conj B ((fun x => -(g₁ x)) + (fun x => -(g₂ x))) (-v)
      = infConv (conj B fun x => -(g₁ x)) (conj B fun x => -(g₂ x)) (-v) :=
    congrFun hex.conj_add (-v)
  have step3 : infConv (conj B fun x => -(g₁ x)) (conj B fun x => -(g₂ x)) (-v)
      = infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v := by
    have e₁ : (fun w => -(concaveConj B g₁ w)) = fun w => (conj B fun x => -(g₁ x)) (-w) :=
      funext fun w => neg_concaveConj B g₁ w
    have e₂ : (fun w => -(concaveConj B g₂ w)) = fun w => (conj B fun x => -(g₂ x)) (-w) :=
      funext fun w => neg_concaveConj B g₂ w
    rw [e₁, e₂]
    exact (infConv_neg _ _ v).symm
  change concaveConj B (fun x => g₁ x + g₂ x) v
      = -(infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v)
  rw [step1, step2, step3]

end ConcaveConjSum

end ConvexAnalysis
