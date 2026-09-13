import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Operations.Image

/-!
# Exact duality: when the closure may be omitted

Almost every "exact" duality statement has the shape

> if `ri (dom f₁) ∩ … ∩ ri (dom fₘ) ≠ ∅` then the closure operation can be dropped and the
> infimum defining the dual operation is attained

(conjugates of sums, of inverse images and of suprema; subdifferential calculus; the duality
theorems of convex programming). The relative interior condition is one sufficient condition among
several; there are polyhedral variants, a continuity variant valid in any topological vector
space, and Attouch–Brezis conditions in Banach spaces.

This file names the **conclusion**. `IsExactSum` and `IsExactImage` are hypothesis-only interfaces,
and the sufficient conditions for them are proved in the module that owns each hypothesis
(`IsExactSum.of_relint` in `Duality/Relint.lean`, `.of_polyhedral` in `Polyhedral/Duality.lean`).

## Main definitions

* `IsExactSum B f g` — `f` and `g` **add exactly**: both are proper, and the infimal convolution
  defining `(f + g)*` is attained.
* `IsExactFinsetSum B s f` — the same for a finite family, the form the `m`-ary statements need.
* `IsExactImage B B' A A' hA g` — `g` **pulls back exactly** along `A`: `g` is proper, and the
  infimum defining `(g A)*` over the fibres of the transpose `A'` is attained.

## Main results

* `conj_add_le_infConv`, `conj_compLin_le_mapLin`, `conj_finsetSum_le_sum_toInfConvFn` — the
  *unconditional* halves: `(f + g)* ≤ f* □ g*` and `(g A)* ≤ A' (g*)`, with no hypothesis at all.
* `IsExactSum.conj_add`, `IsExactSum.exists_conj_add_eq` — the exact half for a sum:
  `(f + g)* = f* □ g*` with the infimal convolution attained (Theorem 16.4 in [^1]);
  `IsExactFinsetSum.conj_finsetSum` is the `m`-ary form.
* `IsExactImage.conj_compLin`, `IsExactImage.exists_conj_compLin_eq` — the exact half for an
  inverse image: `(g A)* = A' (g*)`, the infimum over the fibre attained (Theorem 16.3 in [^1]).
* `IsExactFinsetSum.singleton`, `.cons`, `.of_split` — the family interface built out of binary
  ones, which is how every `m`-ary constraint qualification is discharged.
* `IsExactSum.proper_add`, `IsExactFinsetSum.proper_finsetSum`, `IsExactImage.proper_compLin` —
  the interfaces are unsatisfiable when the effective domains miss each other.

## Implementation notes

The equality is a theorem, not a field of the structure. `(f + g)* ≤ f* □ g*` holds for arbitrary
`f` and `g`, and an interface *stating the equality* would be unsatisfiable where it looks most
innocent: when `dom f ∩ dom g = ∅` we have `(f + g)* ≡ -∞`, while the conjugate of a proper
function is never `-∞`. What the interface carries is the *attainment*, `exact_le`.

`IsExactImage.exact_le` asks for a point of the fibre `A' ⁻¹' {y}` only where `(g A)* y` is finite.
Without that guard the interface is unsatisfiable whenever `A'` is not surjective: at a `y` outside
the range of `A'` there is no `z` to produce, while both sides of the identity are legitimately
`+∞` there.

The family interface is not an iterated binary one: `□` does not preserve `≠ ⊥`, so the binary
bound cannot be iterated, and what iterates is the *construction*, `IsExactFinsetSum.cons`. And
`exact_le` demands a splitting of every `y`, so `IsExactFinsetSum B ∅ f` forces `F` to be trivial —
the empty family is not exact, just as two functions with disjoint effective domains are not.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §16, §20, §23, §31.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Sums: the unconditional half -/

section Sum

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {y₁ y₂ : F} {c₁ c₂ : ℝ}

/-- An affine minorant of `f` and one of `g` add to an affine minorant of `f + g`. Read through
`conj_le_coe_iff` this is the whole unconditional content of the conjugate-of-a-sum identity. -/
theorem conj_add_le_coe_add (h₁ : conj B f y₁ ≤ (c₁ : EReal)) (h₂ : conj B g y₂ ≤ (c₂ : EReal)) :
    conj B (f + g) (y₁ + y₂) ≤ ((c₁ + c₂ : ℝ) : EReal) := by
  rw [conj_le_coe_iff] at h₁ h₂ ⊢
  intro x
  have hsplit : affineFn B (y₁ + y₂) (c₁ + c₂) x
      = affineFn B y₁ c₁ x + affineFn B y₂ c₂ x := by
    rw [affineFn_eq_coe, affineFn_eq_coe, affineFn_eq_coe, ← _root_.EReal.coe_add]
    congr 1
    rw [map_add]
    ring
  rw [hsplit, Pi.add_apply]
  exact add_le_add (h₁ x) (h₂ x)

theorem epi_conj_add_epi_conj_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    epi (conj B f) + epi (conj B g) ⊆ epi (conj B (f + g)) := by
  rintro _ ⟨⟨y₁, c₁⟩, h₁, ⟨y₂, c₂⟩, h₂, rfl⟩
  rw [mk_mem_epi] at h₁ h₂
  simpa using conj_add_le_coe_add h₁ h₂

/-- **Unconditionally, the conjugate of a sum is at most the infimal convolution** of the
conjugates, for *arbitrary* `f` and `g`. The reverse inequality is what `IsExactSum` asks for, and
what every constraint qualification exists to supply. -/
theorem conj_add_le_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    conj B (f + g) ≤ infConv (conj B f) (conj B g) := by
  rw [infConv_def]
  exact subset_epi_iff_le_ofEpi.1 (epi_conj_add_epi_conj_subset B f g)

/-- The pointwise form of `conj_add_le_infConv`, which is *not* unconditional: if `f ≡ +∞` and `g`
takes `-∞` somewhere then `(f + g)* ≡ +∞` while `f* y₁ + g* y₂ = ⊥ + ⊤ = ⊥`. Nonempty effective
domains rule that out. -/
theorem conj_add_le_add_conj (hf : (dom f).Nonempty) (hg : (dom g).Nonempty) (y₁ y₂ : F) :
    conj B (f + g) (y₁ + y₂) ≤ conj B f y₁ + conj B g y₂ := by
  rcases eq_or_ne (conj B f y₁) ⊤ with h₁ | h₁
  · rw [h₁, _root_.EReal.top_add_of_ne_bot (conj_ne_bot hg y₂)]
    exact le_top
  rcases eq_or_ne (conj B g y₂) ⊤ with h₂ | h₂
  · rw [h₂, _root_.EReal.add_top_of_ne_bot (conj_ne_bot hf y₁)]
    exact le_top
  obtain ⟨c₁, hc₁⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (conj_ne_bot hf y₁) (lt_top_iff_ne_top.2 h₁)
  obtain ⟨c₂, hc₂⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (conj_ne_bot hg y₂) (lt_top_iff_ne_top.2 h₂)
  rw [hc₁, hc₂, ← _root_.EReal.coe_add]
  exact conj_add_le_coe_add hc₁.le hc₂.le

end Sum

/-! ### Sums: the interface -/

section SumInterface

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- `f` and `g` **add exactly** with respect to the pairing `B`: both are proper, and the infimal
convolution `f* □ g*` is attained at every point — equivalently (`IsExactSum.conj_add`), the
conjugate of the sum *is* the infimal convolution of the conjugates. This is the conclusion the
relative-interior and polyhedral qualifications both deliver. -/
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  /-- The left summand is proper. -/
  proper_left : Proper f
  /-- The right summand is proper. -/
  proper_right : Proper g
  /-- At every `y` the infimal convolution defining `(f + g)*` is attained: some splitting
  `y = y₁ + y₂` already achieves the value. The reverse inequality is unconditional
  (`conj_add_le_infConv`), so this is the entire content. -/
  exact_le : ∀ y : F, ∃ y₁ y₂ : F, y₁ + y₂ = y ∧
    conj B f y₁ + conj B g y₂ ≤ conj B (f + g) y

namespace IsExactSum

variable (h : IsExactSum B f g)
include h

theorem conj_left_ne_bot (y : F) : conj B f y ≠ ⊥ := conj_ne_bot h.proper_left.dom_nonempty y

theorem conj_right_ne_bot (y : F) : conj B g y ≠ ⊥ := conj_ne_bot h.proper_right.dom_nonempty y

theorem symm : IsExactSum B g f where
  proper_left := h.proper_right
  proper_right := h.proper_left
  exact_le y := by
    obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
    refine ⟨y₂, y₁, by rw [add_comm]; exact hy, ?_⟩
    rw [add_comm g f, add_comm (conj B g y₂)]
    exact hle

/-- **The interface rules out disjoint effective domains**: the sum of two exactly-adding
functions is itself proper. -/
theorem proper_add : Proper (f + g) := by
  have hb : conj B (f + g) 0 ≠ ⊥ := by
    obtain ⟨y₁, y₂, -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff, _root_.EReal.add_eq_bot_iff] at hle
    exact hle.elim (h.conj_left_ne_bot y₁) (h.conj_right_ne_bot y₂)
  refine ⟨?_, fun x hx => ?_⟩
  · by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))
  · rw [Pi.add_apply, _root_.EReal.add_eq_bot_iff] at hx
    exact hx.elim (h.proper_left.ne_bot x) (h.proper_right.ne_bot x)

theorem infConv_le_conj_add : infConv (conj B f) (conj B g) ≤ conj B (f + g) := by
  intro y
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  subst hy
  simpa using infConv_le_add h.conj_left_ne_bot h.conj_right_ne_bot (y₁ + y₂) y₂

/-- **The exact half**: the conjugate of a sum is the infimal convolution of the conjugates. -/
theorem conj_add : conj B (f + g) = infConv (conj B f) (conj B g) :=
  le_antisymm (conj_add_le_infConv B f g) h.infConv_le_conj_add

theorem conj_add_apply (y : F) :
    conj B (f + g) y = ⨅ y' : F, conj B f (y - y') + conj B g y' := by
  rw [h.conj_add]
  exact infConv_apply h.conj_left_ne_bot h.conj_right_ne_bot y

/-- **The infimal convolution is attained**, which is the half the constraint qualifications are
for. -/
theorem exists_conj_add_eq (y : F) :
    ∃ y₁ y₂ : F, y₁ + y₂ = y ∧ conj B f y₁ + conj B g y₂ = conj B (f + g) y := by
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine ⟨y₁, y₂, hy, le_antisymm hle ?_⟩
  subst hy
  exact conj_add_le_add_conj h.proper_left.dom_nonempty h.proper_right.dom_nonempty y₁ y₂

end IsExactSum

end SumInterface

/-! ### Sums over a `Finset`: the unconditional half -/

section FinsetSum

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

omit [AddCommGroup E] [Module ℝ E] in
theorem dom_finsetSum (hf : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) :
    dom (∑ i ∈ s, f i) = ⋂ i ∈ s, dom (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    ext x
    simp
  | cons i t hi ih =>
    have hbot : ∀ x, (∑ j ∈ t, f j) x ≠ ⊥ := fun x => by
      rw [Finset.sum_apply]
      exact EReal.sum_ne_bot fun j hj => hf j (by simp [hj]) x
    rw [Finset.sum_cons, dom_add (hf i (by simp)) hbot, ih fun j hj => hf j (by simp [hj])]
    ext x
    simp [Finset.mem_cons]

theorem conj_finsetSum_le_coe_sum {y : ι → F} {c : ι → ℝ}
    (h : ∀ i ∈ s, conj B (f i) (y i) ≤ (c i : EReal)) :
    conj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ((∑ i ∈ s, c i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [conj_le_coe_iff]
    intro x
    rw [affineFn_eq_coe]
    simp
  | cons i t hi ih =>
    simp only [Finset.sum_cons]
    exact conj_add_le_coe_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- The pointwise `m`-ary form: `(f₁ + ⋯ + fₘ)* (y₁ + ⋯ + yₘ) ≤ f₁* y₁ + ⋯ + fₘ* yₘ`. Nonempty
effective domains keep the right-hand side from collapsing to `⊥` through a `⊤ + ⊥`. -/
theorem conj_finsetSum_le_sum_conj (hf : ∀ i ∈ s, (dom (f i)).Nonempty) (y : ι → F) :
    conj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ∑ i ∈ s, conj B (f i) (y i) := by
  rcases eq_or_ne (∑ i ∈ s, conj B (f i) (y i)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hbot : ∀ i ∈ s, conj B (f i) (y i) ≠ ⊥ := fun i hi => conj_ne_bot (hf i hi) (y i)
  have hfin : ∀ i ∈ s, conj B (f i) (y i) ≠ ⊤ :=
    EReal.forall_ne_top_of_sum_ne_top s _ hbot htop
  have hci : ∀ i ∈ s, conj B (f i) (y i) = (((conj B (f i) (y i)).toReal : ℝ) : EReal) :=
    fun i hi => (_root_.EReal.coe_toReal (hfin i hi) (hbot i hi)).symm
  have hsum : ∑ i ∈ s, conj B (f i) (y i)
      = ((∑ i ∈ s, (conj B (f i) (y i)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl hci
  rw [hsum]
  exact conj_finsetSum_le_coe_sum fun i hi => (hci i hi).le

/-- **The `m`-ary form, unconditionally**:
`(f₁ + ⋯ + fₘ)* ≤ f₁* □ ⋯ □ fₘ*`, the `□`-product being the `AddCommMonoid` sum of `InfConvFn F`.

No properness may be assumed at the intermediate stages, since `□` does not preserve it; the
induction runs on `infConv_mono` and never re-enters the infimum formula. -/
theorem conj_finsetSum_le_sum_toInfConvFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) :
    conj B (∑ i ∈ s, f i) ≤ ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty, ofInfConvFn_zero]
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [indicatorFn_of_mem (s := ({0} : Set F)) (Set.mem_singleton_iff.2 rfl), conj_apply]
      refine iSup_le fun x => ?_
      simp
    · rw [indicatorFn_of_notMem (s := ({0} : Set F)) (by simpa using hy)]
      exact le_top
  | cons i t hi ih =>
    simp only [Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact (conj_add_le_infConv B (f i) _).trans (infConv_mono le_rfl ih)

end FinsetSum

/-! ### Sums over a `Finset`: the interface -/

section FinsetSumInterface

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- A finite family `(fᵢ)_{i ∈ s}` **adds exactly** with respect to the pairing `B`: every member
is proper, and the `m`-fold infimal convolution `f₁* □ ⋯ □ fₘ*` is attained at every point —
equivalently, the conjugate of `f₁ + ⋯ + fₘ` *is* `f₁* □ ⋯ □ fₘ*`.

`IsExactSum` is the case of two. Every consequence below is proved once, for the family;
`IsExactFinsetSum.cons` and `.of_split` build a family interface out of binary ones. -/
structure IsExactFinsetSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → E → EReal) : Prop where
  /-- Every member of the family is proper. -/
  proper : ∀ i ∈ s, Proper (f i)
  /-- At every `y` the `m`-fold infimal convolution defining `(f₁ + ⋯ + fₘ)*` is attained: some
  splitting `y = y₁ + ⋯ + yₘ` already achieves the value. The reverse inequality is unconditional
  (`conj_finsetSum_le_sum_toInfConvFn`), so this is the entire content. -/
  exact_le : ∀ y : F, ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
    ∑ i ∈ s, conj B (f i) (y' i) ≤ conj B (∑ i ∈ s, f i) y

namespace IsExactFinsetSum

variable (h : IsExactFinsetSum B s f)
include h

theorem finsetSum_ne_bot (x : E) : (∑ i ∈ s, f i) x ≠ ⊥ := by
  rw [Finset.sum_apply]
  exact EReal.sum_ne_bot fun i hi => (h.proper i hi).ne_bot x

/-- **The interface rules out effective domains with empty intersection**, exactly as in the
binary case. -/
theorem proper_finsetSum : Proper (∑ i ∈ s, f i) := by
  have hb : conj B (∑ i ∈ s, f i) 0 ≠ ⊥ := by
    obtain ⟨y', -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff] at hle
    exact EReal.sum_ne_bot
      (fun i hi => conj_ne_bot (h.proper i hi).dom_nonempty (y' i)) hle
  refine ⟨?_, h.finsetSum_ne_bot⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

theorem sum_toInfConvFn_le_conj_finsetSum :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) ≤ conj B (∑ i ∈ s, f i) := by
  intro y
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  rw [← hy]
  exact sum_toInfConvFn_le_sum (fun i hi x => conj_ne_bot (h.proper i hi).dom_nonempty x) y'

/-- **The `m`-ary exact half**: the conjugate of a finite sum is the infimal convolution of the
conjugates. -/
theorem conj_finsetSum :
    conj B (∑ i ∈ s, f i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (conj B (f i))) :=
  le_antisymm (conj_finsetSum_le_sum_toInfConvFn B s f) h.sum_toInfConvFn_le_conj_finsetSum

/-- **The `m`-fold infimal convolution is attained**, which is the half the constraint
qualifications are for:
`(f₁ + ⋯ + fₘ)* y = inf {f₁* y₁ + ⋯ + fₘ* yₘ | y₁ + ⋯ + yₘ = y}`, with the infimum attained. -/
theorem exists_conj_finsetSum_eq (y : F) :
    ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, conj B (f i) (y' i) = conj B (∑ i ∈ s, f i) y := by
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine ⟨y', hy, le_antisymm hle ?_⟩
  rw [← hy]
  exact conj_finsetSum_le_sum_conj (fun i hi => (h.proper i hi).dom_nonempty) y'

end IsExactFinsetSum

/-- A one-element family adds exactly as soon as its member is proper: there is nothing to
split. This is the base case of every `m`-ary constraint qualification. -/
theorem IsExactFinsetSum.singleton {i : ι} (hf : Proper (f i)) :
    IsExactFinsetSum B ({i} : Finset ι) f where
  proper j hj := by rw [Finset.mem_singleton.1 hj]; exact hf
  exact_le y := ⟨fun _ => y, by simp, by simp⟩

/-- **Adjoining one summand.** A family adds exactly as soon as its tail does and the new summand
adds exactly to the sum of the tail: the induction step every `m`-ary constraint qualification
runs on. -/
theorem IsExactFinsetSum.cons {i : ι} {t : Finset ι} (hi : i ∉ t)
    (hbin : IsExactSum B (f i) (∑ j ∈ t, f j)) (ht : IsExactFinsetSum B t f) :
    IsExactFinsetSum B (Finset.cons i t hi) f := by
  classical
  refine ⟨fun j hj => ?_, fun y => ?_⟩
  · rcases Finset.mem_cons.1 hj with rfl | hj'
    · exact hbin.proper_left
    · exact ht.proper j hj'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨y', hy', hle'⟩ := ht.exact_le y₂
    obtain ⟨w, hwi, hwt⟩ : ∃ w : ι → F, w i = y₁ ∧ ∀ j ∈ t, w j = y' j :=
      ⟨Function.update y' i y₁, Function.update_self _ _ _,
        fun j hj => Function.update_of_ne (by rintro rfl; exact hi hj) _ _⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_cons, hwi, Finset.sum_congr rfl hwt, hy', hy]
    · rw [Finset.sum_cons, Finset.sum_cons, hwi]
      have hcongr : ∑ j ∈ t, conj B (f j) (w j) = ∑ j ∈ t, conj B (f j) (y' j) :=
        Finset.sum_congr rfl fun j hj => by rw [hwt j hj]
      rw [hcongr]
      exact le_trans (add_le_add le_rfl hle') hle

/-- **Gluing two exactly-adding subfamilies.** If `s` splits into disjoint `t` and `u`, both of
which add exactly, and the two partial sums add exactly to each other, then `s` adds exactly. This
is the form the polyhedral proof uses, with `t` the polyhedral indices and `u` the rest; the
splitting is spelled pointwise so that no `DecidableEq` instance is needed. -/
theorem IsExactFinsetSum.of_split {t u : Finset ι} (hdisj : Disjoint t u)
    (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (ht : IsExactFinsetSum B t f) (hu : IsExactFinsetSum B u f)
    (hbin : IsExactSum B (∑ i ∈ t, f i) (∑ i ∈ u, f i)) :
    IsExactFinsetSum B s f := by
  classical
  have hsu : s = t ∪ u := Finset.ext fun i => by rw [hmem i, Finset.mem_union]
  subst hsu
  refine ⟨fun i hi => ?_, fun y => ?_⟩
  · rcases Finset.mem_union.1 hi with hi' | hi'
    · exact ht.proper i hi'
    · exact hu.proper i hi'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨a, ha, hlea⟩ := ht.exact_le y₁
    obtain ⟨b, hb, hleb⟩ := hu.exact_le y₂
    obtain ⟨w, hwt, hwu⟩ : ∃ w : ι → F, (∀ i ∈ t, w i = a i) ∧ ∀ i ∈ u, w i = b i :=
      ⟨fun i => if i ∈ t then a i else b i, fun i hi => by simp [hi],
        fun i hi => by simp [Finset.disjoint_right.1 hdisj hi]⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_union hdisj, Finset.sum_congr rfl hwt, Finset.sum_congr rfl hwu, ha, hb, hy]
    · rw [Finset.sum_union hdisj, Finset.sum_union hdisj]
      have h₁ : ∑ i ∈ t, conj B (f i) (w i) = ∑ i ∈ t, conj B (f i) (a i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwt i hi]
      have h₂ : ∑ i ∈ u, conj B (f i) (w i) = ∑ i ∈ u, conj B (f i) (b i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwu i hi]
      rw [h₁, h₂]
      exact le_trans (add_le_add hlea hleb) hle

end FinsetSumInterface

/-! ### Images -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **Unconditionally, the conjugate of the inverse image `g A` is at most the image** under the
transpose of the conjugate of `g`. Only the adjointness datum is used. -/
theorem conj_compLin_le_mapLin (hA : IsAdjointPair B B' A A') (g : G → EReal) :
    conj B (compLin g A) ≤ mapLin A' (conj B' g) := by
  intro y
  refine le_mapLin fun z hz => ?_
  rw [conj_apply]
  refine iSup_le fun x => ?_
  rw [compLin_apply, ← hz, ← hA x z]
  exact sub_le_conj B' g (A x) z

/-- `g` **pulls back exactly** along `A`: `g` is proper, and the infimum over the fibres of the
transpose `A'` that defines `A' (g*)` is attained — equivalently, `(g A)* = A' (g*)`.

The transpose `A'` and the adjointness `hA` are *data*: between arbitrarily paired spaces a linear
map need not have an adjoint at all. -/
structure IsExactImage (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) (hA : IsAdjointPair B B' A A') (g : G → EReal) : Prop where
  /-- The function being pulled back is proper. -/
  proper : Proper g
  /-- Wherever `(g A)* y` is finite, the infimum defining `A' (g*) y` is attained on the fibre of
  `A'` over `y`. The reverse inequality is unconditional (`conj_compLin_le_mapLin`).

  The guard `(g A)* y < ⊤` is not a weakening of convenience: without it the field would demand a
  point of the fibre `A' ⁻¹' {y}` for *every* `y`, i.e. it would silently force `A'` to be
  surjective. -/
  exact_le : ∀ y : F, conj B (compLin g A) y < ⊤ →
    ∃ z : H, A' z = y ∧ conj B' g z ≤ conj B (compLin g A) y

namespace IsExactImage

variable {hA : IsAdjointPair B B' A A'} (h : IsExactImage B B' A A' hA g)
include h

theorem proper_compLin : Proper (compLin g A) := by
  have hb : conj B (compLin g A) 0 ≠ ⊥ := by
    intro hc
    obtain ⟨z, -, hle⟩ := h.exact_le 0 (by rw [hc]; exact bot_lt_top)
    rw [hc, le_bot_iff] at hle
    exact conj_ne_bot h.proper.dom_nonempty z hle
  refine ⟨?_, fun x => h.proper.ne_bot (A x)⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (conj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

theorem mapLin_le_conj_compLin : mapLin A' (conj B' g) ≤ conj B (compLin g A) := fun y => by
  rcases eq_top_or_lt_top (conj B (compLin g A) y) with hy | hy
  · rw [hy]; exact le_top
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact (mapLin_le hz).trans hle

/-- **The exact half**: the conjugate of an inverse image is the image of the conjugate under the
transpose. -/
theorem conj_compLin : conj B (compLin g A) = mapLin A' (conj B' g) :=
  le_antisymm (conj_compLin_le_mapLin hA g) h.mapLin_le_conj_compLin

/-- **The infimum over the fibre is attained**, which is the half the constraint qualifications
are for. -/
theorem exists_conj_compLin_eq {y : F} (hy : conj B (compLin g A) y < ⊤) :
    ∃ z : H, A' z = y ∧ conj B' g z = conj B (compLin g A) y := by
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact ⟨z, hz, le_antisymm hle (h.conj_compLin ▸ mapLin_le hz)⟩

end IsExactImage

end Image

end ConvexAnalysis
