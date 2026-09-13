import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations

/-!
# Auxiliary lemmas about `EReal`

Upstreaming candidate: nothing here is specific to numerical analysis.

Convex analysis over `EReal` needs a handful of order and arithmetic facts that Mathlib does not
provide directly (its home there would be `Mathlib/Data/EReal/Operations.lean`). They are
collected here so that they do not accumulate as ad hoc `have`s throughout the library. Anything
that Mathlib does state — `EReal.le_of_forall_lt_iff_le`, `EReal.exists_between_coe_real`,
`EReal.coe_mul`, `EReal.neg_add`, `EReal.neg_sub`, `EReal.left_distrib_of_nonneg_of_ne_top` — is
used directly and not restated.

## Rockafellar's arithmetic conventions

Rockafellar (*Convex Analysis*, §4) fixes the conventions

* `α + ∞ = ∞` for `-∞ < α ≤ ∞`,
* `α - ∞ = -∞` for `-∞ ≤ α < ∞`,
* `0 · ∞ = 0`,
* `inf ∅ = +∞`, `sup ∅ = -∞`,

and leaves `∞ - ∞` *undefined*, avoiding it by properness hypotheses. Every one of these agrees
with the corresponding fact about `EReal` in Mathlib, so no bespoke arithmetic type is needed; see
the `example`s below, which are exactly the conventions listed in the book.
-/

section Conventions

example (r : ℝ) : (r : EReal) + ⊤ = ⊤ := by simp
example (r : ℝ) : (r : EReal) - ⊤ = ⊥ := by simp
example : (0 : EReal) * ⊤ = 0 := by simp
example : -(⊥ : EReal) = ⊤ := by simp
example : (⨆ _ : (∅ : Set ℝ), (0 : EReal)) = ⊥ := by simp

end Conventions

namespace EReal

/-- An `EReal` that is neither `⊥` nor `⊤` is a real number: the existential form of
`EReal.coe_toReal`, for use with `obtain` where `lift` would substitute the value away. -/
theorem exists_coe_of_ne_bot_of_lt_top {z : EReal} (h₁ : z ≠ ⊥) (h₂ : z < ⊤) :
    ∃ r : ℝ, z = (r : EReal) :=
  ⟨z.toReal, (coe_toReal h₂.ne h₁).symm⟩

/-- A positive real multiple of an `EReal` below `⊤` stays below `⊤`. -/
theorem coe_mul_ne_top {a : ℝ} (ha : 0 < a) {u : EReal} (hu : u ≠ ⊤) : (a : EReal) * u ≠ ⊤ := by
  rw [EReal.mul_ne_top]
  exact ⟨Or.inl (EReal.coe_ne_bot a), Or.inl (by exact_mod_cast ha.le),
    Or.inl (EReal.coe_ne_top a), Or.inr hu⟩

/-- Negation turns a convex combination with positive real coefficients into the combination of the
negations — provided neither value is `⊤`, without which the identity is false on `EReal`. -/
theorem neg_combo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {u v : EReal} (hu : u ≠ ⊤) (hv : v ≠ ⊤) :
    (a : EReal) * -u + (b : EReal) * -v = -((a : EReal) * u + (b : EReal) * v) := by
  rw [EReal.neg_add (.inr (coe_mul_ne_top hb hv)) (.inl (coe_mul_ne_top ha hu)), sub_eq_add_neg,
    mul_neg, mul_neg]

/-! The hypotheses of `EReal.neg_combo` are load-bearing: at `u = ⊤`, `v = ⊥` the two sides
are `⊥` and `⊤`. -/

example : (1 : EReal) * -(⊤ : EReal) + (1 : EReal) * -(⊥ : EReal) = ⊥ := by simp

example : -((1 : EReal) * (⊤ : EReal) + (1 : EReal) * (⊥ : EReal)) = ⊤ := by simp

/-- Multiplication by a positive real scalar reflects, as well as preserves, the order on `EReal`.
The reflection direction is proved by multiplying by the inverse scalar, since `EReal` has
`PosMulMono` but not `PosMulStrictMono`. -/
theorem coe_mul_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z w : EReal} :
    (a : EReal) * z ≤ (a : EReal) * w ↔ z ≤ w := by
  refine ⟨fun h => ?_, fun h => mul_le_mul_of_nonneg_left h (by exact_mod_cast ha.le)⟩
  have ha' : (0 : EReal) ≤ ((a⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 ha).le
  have h' := mul_le_mul_of_nonneg_left h ha'
  rwa [← mul_assoc, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne',
    EReal.coe_one, one_mul, one_mul] at h'

/-- **If `z` is at most every positive real, then `z ≤ 0`.** The conclusion is genuinely weaker
than `z ≤ r` for a fixed `r`: `z` may be any non-positive extended real. It is how "the optimal
value is not positive" is extracted from feasible solutions whose values tend to `0`. -/
theorem le_zero_of_forall_le_pos {z : EReal} (h : ∀ ε : ℝ, 0 < ε → z ≤ (ε : EReal)) : z ≤ 0 := by
  by_contra hc
  obtain ⟨q, hq0, hqz⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hc)
  exact absurd (h q (by exact_mod_cast hq0)) (not_le.2 hqz)

/-- **Scaling an inequality that carries a real offset**, `cA + ct ≤ cB ↔ A + t ≤ B` for `c > 0`.

This is what a positive Lagrange multiplier does to a constraint. -/
theorem coe_mul_add_coe_le_coe_mul_iff {c : ℝ} (hc : 0 < c) (A B : EReal) (t : ℝ) :
    (c : EReal) * A + ((c * t : ℝ) : EReal) ≤ (c : EReal) * B ↔ A + (t : EReal) ≤ B := by
  rw [EReal.coe_mul, ← left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc.le) (coe_ne_top c),
    coe_mul_le_coe_mul_iff hc]

/-- An extended real is determined by the real numbers that bound it above. -/
theorem eq_of_forall_le_coe_iff {z w : EReal}
    (h : ∀ r : ℝ, z ≤ (r : EReal) ↔ w ≤ (r : EReal)) : z = w := by
  refine le_antisymm ?_ ?_
  · induction w with
    | bot => exact le_of_forall_lt_iff_le.1 fun r _ => (h r).2 bot_le
    | top => exact le_top
    | coe s => exact (h s).2 le_rfl
  · induction z with
    | bot => exact le_of_forall_lt_iff_le.1 fun r _ => (h r).1 bot_le
    | top => exact le_top
    | coe s => exact (h s).1 le_rfl

/-- The only extended reals fixed by multiplication by a positive scalar other than `1` are `0`,
`⊤` and `⊥`. This is the whole content of "positive homogeneity says nothing about `f 0`". -/
theorem eq_zero_or_eq_top_or_eq_bot {a : ℝ} (ha : a ≠ 1) {z : EReal} (h : (a : EReal) * z = z) :
    z = 0 ∨ z = ⊤ ∨ z = ⊥ := by
  induction z with
  | bot => exact Or.inr (Or.inr rfl)
  | top => exact Or.inr (Or.inl rfl)
  | coe r =>
    left
    rw [← EReal.coe_mul] at h
    have hr : a * r = r := by exact_mod_cast h
    have hz : (a - 1) * r = 0 := by rw [sub_mul, one_mul, hr, _root_.sub_self]
    rcases mul_eq_zero.1 hz with h1 | h1
    · exact absurd (by linarith : a = 1) ha
    · rw [h1, EReal.coe_zero]

/-- An extended real equal to its own negative is `0`. -/
theorem eq_zero_of_neg_eq {z : EReal} (h : -z = z) : z = 0 := by
  induction z with
  | bot => rw [EReal.neg_bot] at h; exact absurd h (by simp)
  | top => rw [EReal.neg_top] at h; exact absurd h (by simp)
  | coe r =>
    have hr : (-r : ℝ) = r := by exact_mod_cast h
    rw [(by linarith : r = (0 : ℝ)), EReal.coe_zero]

/-- Transposing a term across `0 ≤ u + v`, when `u` is not `⊥`. -/
theorem neg_le_of_zero_le_add {u v : EReal} (hu : u ≠ ⊥) (h : 0 ≤ u + v) : -u ≤ v := by
  induction u with
  | bot => exact absurd rfl hu
  | top => rw [EReal.neg_top]; exact bot_le
  | coe r =>
    induction v with
    | bot => rw [EReal.add_bot] at h; simp at h
    | top => exact le_top
    | coe s =>
      rw [← EReal.coe_add] at h
      have hrs : (0 : ℝ) ≤ r + s := by exact_mod_cast h
      rw [← EReal.coe_neg]
      exact_mod_cast (by linarith : -r ≤ s)

/-- A finite sum of `EReal`s none of which is `⊥` is not `⊥`. -/
theorem sum_ne_bot {ι : Type*} {s : Finset ι} {g : ι → EReal} (h : ∀ i ∈ s, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    exact EReal.add_ne_bot_iff.2 ⟨h i (by simp), ih fun j hj => h j (by simp [hj])⟩

/-- Dividing through by a positive real coefficient. This is the form in which a hypothesis
`(a : EReal) * z ≤ r` gets used: it turns a statement about `a • f` into one about `f`. -/
theorem coe_mul_le_coe_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (a : EReal) * z ≤ (r : EReal) ↔ z ≤ ((r / a : ℝ) : EReal) := by
  induction z with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe s =>
    rw [← coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ ha,
      mul_comm]

/-- The mirror of `EReal.coe_mul_le_coe_iff`: dividing through a *lower* bound by a positive
real. -/
theorem coe_le_coe_mul_iff {a : ℝ} (ha : 0 < a) {z : EReal} {r : ℝ} :
    (r : EReal) ≤ (a : EReal) * z ↔ ((r / a : ℝ) : EReal) ≤ z := by
  induction z with
  | bot => simp [EReal.coe_mul_bot_of_pos ha]
  | top => simp [EReal.coe_mul_top_of_pos ha]
  | coe s =>
    rw [← coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, div_le_iff₀ ha,
      mul_comm]

variable {κ : Type*}

/-- The coercion `ℝ → EReal` commutes with finite sums. -/
theorem coe_sum (t : Finset κ) (r : κ → ℝ) :
    ((∑ i ∈ t, r i : ℝ) : EReal) = ∑ i ∈ t, ((r i : ℝ) : EReal) := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, EReal.coe_add, ih]

/-- A non-negative real multiple of an `EReal` other than `⊥` is not `⊥`. The coefficient `0` is
harmless because `EReal` obeys Rockafellar's convention `0 · ∞ = 0`. -/
theorem coe_mul_ne_bot {a : ℝ} (ha : 0 ≤ a) {z : EReal} (hz : z ≠ ⊥) : (a : EReal) * z ≠ ⊥ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, EReal.coe_zero, zero_mul]; simp
  · induction z with
    | bot => exact absurd rfl hz
    | top => rw [EReal.coe_mul_top_of_pos h]; exact top_ne_bot
    | coe r => rw [← coe_mul]; exact EReal.coe_ne_bot _

/-- If a finite sum of `EReal`s none of which is `⊥` is not `⊤`, then no term is `⊤`. This is the
form in which "the sum is unambiguous" gets used: it turns a finite bound on a sum into a finite
bound on each term. -/
theorem forall_ne_top_of_sum_ne_top (t : Finset κ) (z : κ → EReal) :
    (∀ i ∈ t, z i ≠ ⊥) → (∑ i ∈ t, z i ≠ ⊤) → ∀ i ∈ t, z i ≠ ⊤ := by
  induction t using Finset.cons_induction with
  | empty => simp
  | cons j t hj ih =>
    intro hbot hsum i hi
    rw [Finset.sum_cons] at hsum
    have h₁ : z j ≠ ⊥ := hbot j (by simp)
    have h₂ : (∑ k ∈ t, z k) ≠ ⊥ := sum_ne_bot fun k hk => hbot k (by simp [hk])
    obtain ⟨hj', ht'⟩ := (EReal.add_ne_top_iff_ne_top₂ h₁ h₂).1 hsum
    rcases Finset.mem_cons.1 hi with rfl | hi'
    · exact hj'
    · exact ih (fun k hk => hbot k (by simp [hk])) ht' i hi'

/-- `a - z` is `⊥` exactly when `z` is `⊤`, for a real `a`. -/
theorem coe_sub_eq_bot_iff {a : ℝ} {z : EReal} : (a : EReal) - z = ⊥ ↔ z = ⊤ := by
  induction z with
  | bot => simp
  | top => simp
  | coe r =>
    refine ⟨fun h => absurd h ?_, fun h => absurd h (by simp)⟩
    rw [← EReal.coe_sub]
    exact EReal.coe_ne_bot _

/-- Moving a real summand across an inequality against a real coercion. -/
theorem add_coe_le_coe_iff {z : EReal} {c m : ℝ} :
    z + (c : EReal) ≤ (m : EReal) ↔ z ≤ ((m - c : ℝ) : EReal) := by
  rw [EReal.coe_sub, EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot c))
    (.inl (EReal.coe_ne_top c))]

/-- Subtracting a value below `⊤` from a real number cannot give `⊥`. -/
theorem coe_sub_ne_bot {a : ℝ} {z : EReal} (h : z ≠ ⊤) : (a : EReal) - z ≠ ⊥ := fun hc =>
  h (coe_sub_eq_bot_iff.1 hc)

/-- **The symmetry of Fenchel's inequality**, and the single `EReal` fact that carries the whole of
§12: `a - z ≤ w ↔ a - w ≤ z` whenever `a` is a real number. There is *no* side condition: all eight
degenerate combinations of `⊥` and `⊤` work out, because `a` is finite. -/
theorem coe_sub_le_comm {a : ℝ} {z w : EReal} : (a : EReal) - z ≤ w ↔ (a : EReal) - w ≤ z := by
  induction z with
  | bot => simpa using coe_sub_eq_bot_iff.symm
  | top => simp
  | coe r =>
    induction w with
    | bot => simp [coe_sub_eq_bot_iff]
    | top => simp
    | coe s =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

/-- **The mirror of `EReal.coe_sub_le_comm`**, for the concave side of the theory:
`z ≤ a - w ↔ w ≤ a - z` whenever `a` is a real number. It says that `z ↦ a - z` is an *antitone
involution* of `EReal`, and, like its convex counterpart, it carries no side condition. -/
theorem le_coe_sub_comm {a : ℝ} {z w : EReal} :
    z ≤ (a : EReal) - w ↔ w ≤ (a : EReal) - z := by
  induction z with
  | bot => simp
  | top =>
    induction w with
    | bot => simp
    | top => simp
    | coe s =>
      rw [EReal.sub_top, le_bot_iff, top_le_iff, ← EReal.coe_sub]
      exact iff_of_false (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  | coe r =>
    induction w with
    | bot => simp
    | top =>
      rw [EReal.sub_top, le_bot_iff, top_le_iff, ← EReal.coe_sub]
      exact iff_of_false (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
    | coe s =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

/-- Reflecting an `EReal` in two real numbers: `b - (a - z) = (b - a) + z`. In particular
`a - (a - z) = z`, so `z ↦ a - z` is an involution of `EReal` for every *real* `a`. -/
theorem coe_sub_coe_sub (a b : ℝ) (z : EReal) :
    (b : EReal) - ((a : EReal) - z) = ((b - a : ℝ) : EReal) + z := by
  induction z with
  | bot => rw [EReal.coe_sub_bot, EReal.sub_top, EReal.add_bot]
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring
  | top => rw [EReal.sub_top, EReal.coe_sub_bot, EReal.coe_add_top]

/-- To bound an `EReal` by another it suffices to bound it by the reals above the latter. -/
theorem le_of_forall_coe_le {u v : EReal} (h : ∀ s : ℝ, v ≤ (s : EReal) → u ≤ (s : EReal)) :
    u ≤ v := by
  induction v with
  | bot => exact le_of_forall_lt_iff_le.1 fun s _ => h s bot_le
  | coe t => exact h t le_rfl
  | top => exact le_top

/-- Multiplication by a positive real commutes with an infimum. `EReal` has `PosMulMono` but no
`PosMulStrictMono`, so the reverse inequality goes through `a⁻¹`. -/
theorem coe_mul_iInf {ι : Sort*} {a : ℝ} (ha : 0 < a) (g : ι → EReal) :
    (a : EReal) * ⨅ i, g i = ⨅ i, (a : EReal) * g i := by
  have hcancel : ∀ z : EReal, ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * z) = z := fun z => by
    rw [← mul_assoc, ← coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  refine le_antisymm (le_iInf fun i => (coe_mul_le_coe_mul_iff ha).2 (iInf_le g i)) ?_
  rw [← coe_mul_le_coe_mul_iff (a := a⁻¹) (inv_pos.2 ha), hcancel]
  exact le_iInf fun i =>
    (hcancel (g i)) ▸ (coe_mul_le_coe_mul_iff (inv_pos.2 ha)).2 (iInf_le _ i)

/-- The difference quotient `(u - r) / a` bounded above by a real, for `a > 0`. -/
theorem sub_div_le_coe_iff {r m a : ℝ} (ha : 0 < a) (u : EReal) :
    (u - (r : EReal)) / (a : EReal) ≤ (m : EReal) ↔ u ≤ ((r + m * a : ℝ) : EReal) := by
  rw [EReal.div_le_iff_le_mul (mod_cast ha) (EReal.coe_ne_top a),
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot r))
      (.inl (EReal.coe_ne_top r)), ← coe_mul, ← EReal.coe_add,
    show (a * m + r : ℝ) = r + m * a from by ring]

/-- The difference quotient `(u - r) / a` bounded below by a real, for `a > 0`. -/
theorem coe_le_sub_div_iff {r m a : ℝ} (ha : 0 < a) (u : EReal) :
    (m : EReal) ≤ (u - (r : EReal)) / (a : EReal) ↔ ((r + m * a : ℝ) : EReal) ≤ u := by
  rw [EReal.le_div_iff_mul_le (mod_cast ha) (EReal.coe_ne_top a),
    EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r))
      (.inl (EReal.coe_ne_top r)), ← coe_mul, ← EReal.coe_add,
    show (m * a + r : ℝ) = r + m * a from by ring]

/-- **Negation exchanges suprema and infima.** Unlike addition, negation *is* an order-reversing
involution of `EReal` with no exceptional values, so this needs no hypothesis. It is what turns
every statement about `conj` into one about `concaveConj`. -/
theorem neg_iSup {ι : Sort*} (u : ι → EReal) : -(⨆ i, u i) = ⨅ i, -(u i) :=
  eq_of_forall_le_iff fun z => by
    simp only [le_iInf_iff, EReal.le_neg, iSup_le_iff]

/-- The companion of `EReal.neg_iSup`. -/
theorem neg_iInf {ι : Sort*} (u : ι → EReal) : -(⨅ i, u i) = ⨆ i, -(u i) :=
  eq_of_forall_ge_iff fun z => by
    simp only [iSup_le_iff, EReal.neg_le, le_iInf_iff]

/-- **Negating a difference whose minuend is a *real* number turns it around**, with no side
condition: the finite term rules out both `∞ - ∞` collisions by itself, where the unrestricted
`EReal.neg_sub` needs two hypotheses. -/
theorem neg_coe_sub (r : ℝ) (z : EReal) : -((r : EReal) - z) = z - (r : EReal) := by
  induction z with
  | bot => simp
  | coe s => norm_cast; ring
  | top => simp

/-- **Negation turns a difference around**, provided neither of the two `∞ - ∞` collisions occurs:
Mathlib's `EReal.neg_sub`, whose right-hand side is `-a + b`, with the difference written as
`b - a`. The hypotheses are Mathlib's; `neg_coe_sub` above is the case where a finite minuend
satisfies both at once. -/
theorem neg_sub_comm {a b : EReal} (h₁ : a ≠ ⊥ ∨ b ≠ ⊥) (h₂ : a ≠ ⊤ ∨ b ≠ ⊤) :
    -(a - b) = b - a := by
  rw [EReal.neg_sub h₁ h₂, sub_eq_add_neg, add_comm]

/-- A positive real scalar commutes with a supremum. -/
theorem coe_mul_iSup {a : ℝ} (ha : 0 < a) {ι : Sort*} (u : ι → EReal) :
    (a : EReal) * ⨆ i, u i = ⨆ i, (a : EReal) * u i := by
  have key : ∀ b : ℝ, 0 < b → ∀ v : ι → EReal,
      (⨆ i, (b : EReal) * v i) ≤ (b : EReal) * ⨆ i, v i := fun b hb v =>
    iSup_le fun i => mul_le_mul_of_nonneg_left (le_iSup v i) (by exact_mod_cast hb.le)
  refine le_antisymm ?_ (key a ha u)
  have h := key a⁻¹ (inv_pos.2 ha) fun i => (a : EReal) * u i
  have hid : ∀ i, ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * u i) = u i := fun i => by
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  simp only [hid] at h
  calc (a : EReal) * ⨆ i, u i
      ≤ (a : EReal) * (((a⁻¹ : ℝ) : EReal) * ⨆ i, (a : EReal) * u i) :=
        mul_le_mul_of_nonneg_left h (by exact_mod_cast ha.le)
    _ = ⨆ i, (a : EReal) * u i := by
        rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one,
          one_mul]

/-- A *real* constant may be moved in and out of a supremum. Because it is finite no `∞ - ∞`
arises, so there is no hypothesis; the empty index set works too, since `⊥ + r = ⊥`. -/
theorem iSup_add_coe {ι : Sort*} (u : ι → EReal) (r : ℝ) :
    (⨆ i, u i) + (r : EReal) = ⨆ i, (u i + (r : EReal)) := by
  have key : ∀ (c : ℝ) (v : ι → EReal), (⨆ i, (v i + (c : EReal))) ≤ (⨆ i, v i) + (c : EReal) :=
    fun c v => iSup_le fun i => add_le_add (le_iSup v i) le_rfl
  refine le_antisymm ?_ (key r u)
  have h := key (-r) fun i => u i + (r : EReal)
  have hid : ∀ i, u i + (r : EReal) + ((-r : ℝ) : EReal) = u i := fun i => by
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  simp only [hid] at h
  calc (⨆ i, u i) + (r : EReal)
      ≤ ((⨆ i, (u i + (r : EReal))) + ((-r : ℝ) : EReal)) + (r : EReal) := add_le_add h le_rfl
    _ = ⨆ i, (u i + (r : EReal)) := by
        rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]

/-- **A constant slides out of a supremum**, with no hypothesis at all: `x ↦ x + c` preserves
arbitrary suprema on `EReal` (for `c = ⊤` it sends `⊥` to `⊥` and everything else to `⊤`; for
`c = ⊥` it is constant; for real `c` it is an order isomorphism), and the empty index set gives
`⊥ + c = ⊥` on both sides. Infima are different: see `EReal.add_iInf_of_ne_bot`. -/
theorem iSup_add {ι : Sort*} (u : ι → EReal) (c : EReal) :
    (⨆ i, u i) + c = ⨆ i, (u i + c) := by
  induction c with
  | bot => simp
  | coe r => exact iSup_add_coe u r
  | top =>
    by_cases h : ∀ i, u i = ⊥
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hne : (⨆ i, u i) ≠ ⊥ := fun hc => hi (le_bot_iff.1 (hc ▸ le_iSup u i))
      rw [add_top_of_ne_bot hne]
      exact le_antisymm (le_iSup_of_le i (add_top_of_ne_bot hi).ge) le_top

/-- The mirror of `EReal.iSup_add`, with the constant on the left. -/
theorem add_iSup {ι : Sort*} (c : EReal) (u : ι → EReal) :
    c + (⨆ i, u i) = ⨆ i, (c + u i) := by
  rw [add_comm, iSup_add]
  exact iSup_congr fun i => add_comm _ _

/-- **A constant minus an infimum is the supremum of the differences**, again with no hypothesis:
`c - x = c + -x`, and negation exchanges infima and suprema. -/
theorem sub_iInf {ι : Sort*} (c : EReal) (u : ι → EReal) :
    c - ⨅ i, u i = ⨆ i, (c - u i) := by
  rw [sub_eq_add_neg, neg_iInf, add_iSup]
  exact iSup_congr fun i => (sub_eq_add_neg _ _).symm

/-- **A constant that is not `-∞` slides out of a supremum as a subtrahend.** The hypothesis rules
out the disagreement at `c = ⊥`: there `(⨆ i, u i) - ⊥` is `⊤` as soon as the supremum is not `⊥`,
while `u i - ⊥` is `⊤` only where `u i ≠ ⊥`. Over an empty index set both sides are `⊥`. -/
theorem iSup_sub_of_ne_bot {ι : Sort*} (u : ι → EReal) {c : EReal} (hc : c ≠ ⊥) :
    (⨆ i, u i) - c = ⨆ i, (u i - c) := by
  induction c with
  | bot => exact absurd rfl hc
  | coe r =>
    rw [sub_eq_add_neg, ← EReal.coe_neg, iSup_add_coe]
    exact iSup_congr fun i => by rw [sub_eq_add_neg, ← EReal.coe_neg]
  | top =>
    have h : ∀ x : EReal, x - (⊤ : EReal) = ⊥ := fun x => by
      rw [sub_eq_add_neg, EReal.neg_top, EReal.add_bot]
    simp only [h, iSup_bot]

/-- The dual of `EReal.iSup_add_coe`, and like it hypothesis-free: the empty index set works
too, since `⊤ + r = ⊤`. -/
theorem iInf_add_coe {ι : Sort*} (u : ι → EReal) (r : ℝ) :
    (⨅ i, u i) + (r : EReal) = ⨅ i, (u i + (r : EReal)) := by
  have key : ∀ (c : ℝ) (v : ι → EReal), (⨅ i, v i) + (c : EReal) ≤ ⨅ i, (v i + (c : EReal)) :=
    fun c v => le_iInf fun i => add_le_add (iInf_le v i) le_rfl
  refine le_antisymm (key r u) ?_
  have h := key (-r) fun i => u i + (r : EReal)
  have hid : ∀ i, u i + (r : EReal) + ((-r : ℝ) : EReal) = u i := fun i => by
    rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.add_sub_cancel_right]
  simp only [hid] at h
  calc (⨅ i, (u i + (r : EReal)))
      = ((⨅ i, (u i + (r : EReal))) + ((-r : ℝ) : EReal)) + (r : EReal) := by
        rw [EReal.coe_neg, ← sub_eq_add_neg, EReal.sub_add_cancel]
    _ ≤ (⨅ i, u i) + (r : EReal) := add_le_add h le_rfl

/-- The set-indexed form of `EReal.iSup_add_coe`. -/
theorem biSup_add_coe {α : Type*} (s : Set α) (u : α → EReal) (r : ℝ) :
    (⨆ a ∈ s, u a) + (r : EReal) = ⨆ a ∈ s, (u a + (r : EReal)) := by
  rw [iSup_add_coe]
  exact iSup_congr fun a => iSup_add_coe _ r

/-- **A real summand cancels from the right**, with no hypothesis: `r` is finite, so
`u + r - r = u` for every `u : EReal`. -/
theorem add_coe_right_cancel {u v : EReal} {r : ℝ} (h : u + (r : EReal) = v + (r : EReal)) :
    u = v := by
  rw [← EReal.add_sub_cancel_right (a := u) (b := r),
    ← EReal.add_sub_cancel_right (a := v) (b := r), h]

/-- The set-indexed form of `EReal.iInf_add_coe`. -/
theorem biInf_add_coe {α : Type*} (s : Set α) (u : α → EReal) (r : ℝ) :
    (⨅ a ∈ s, u a) + (r : EReal) = ⨅ a ∈ s, (u a + (r : EReal)) := by
  rw [iInf_add_coe]
  exact iInf_congr fun a => iInf_add_coe _ r

/-- An arbitrary constant may be moved in and out of a supremum over a set on which the values are
never `⊥`. The hypothesis is what rules out `⊥ + ⊤ = ⊥` disagreeing with `⨆ (⊥ + ⊤)`. -/
theorem biSup_add_of_ne_bot {α : Type*} {s : Set α} {u : α → EReal} (hu : ∀ a ∈ s, u a ≠ ⊥)
    (M : EReal) : (⨆ a ∈ s, u a) + M = ⨆ a ∈ s, (u a + M) := by
  induction M with
  | bot => simp
  | coe r => exact biSup_add_coe s u r
  | top =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
    · simp
    · have hne : (⨆ a ∈ s, u a) ≠ ⊥ := fun hc =>
        hu a₀ ha₀ (le_bot_iff.1 (hc ▸ le_iSup₂ (f := fun a (_ : a ∈ s) => u a) a₀ ha₀))
      rw [EReal.add_top_of_ne_bot hne]
      refine (top_le_iff.1 ?_).symm
      calc (⊤ : EReal) = u a₀ + ⊤ := (EReal.add_top_of_ne_bot (hu a₀ ha₀)).symm
        _ ≤ ⨆ a ∈ s, (u a + (⊤ : EReal)) :=
          le_iSup₂ (f := fun a (_ : a ∈ s) => u a + (⊤ : EReal)) a₀ ha₀

/-- **The supremum of a sum splits**, provided neither family takes `⊥`; if either index set is
empty both sides are `⊥`. This is what turns "the epigraph of an infimal convolution is a sum of
epigraphs" into "the conjugate of an infimal convolution is a sum of conjugates" (Theorem 16.4). -/
theorem biSup_add_biSup {α β : Type*} {s : Set α} {t : Set β} {u : α → EReal} {v : β → EReal}
    (hu : ∀ a ∈ s, u a ≠ ⊥) (hv : ∀ b ∈ t, v b ≠ ⊥) :
    (⨆ a ∈ s, u a) + (⨆ b ∈ t, v b) = ⨆ a ∈ s, ⨆ b ∈ t, (u a + v b) := by
  rw [biSup_add_of_ne_bot hu]
  refine iSup_congr fun a => iSup_congr fun _ => ?_
  rw [add_comm (u a), biSup_add_of_ne_bot hv]
  exact iSup_congr fun _ => iSup_congr fun _ => add_comm _ _

/-- A *real* constant may be moved in and out of an infimum from the **left**. The mirror of
`EReal.iInf_add_coe`, which has it on the right. -/
theorem coe_add_iInf {ι : Sort*} (r : ℝ) (u : ι → EReal) :
    (r : EReal) + (⨅ i, u i) = ⨅ i, ((r : EReal) + u i) := by
  rw [add_comm, iInf_add_coe]
  exact iInf_congr fun i => add_comm _ _

/-- **A real constant subtracted from an infimum turns it into a supremum.** -/
theorem coe_sub_iInf {ι : Sort*} (r : ℝ) (u : ι → EReal) :
    (r : EReal) - ⨅ i, u i = ⨆ i, ((r : EReal) - u i) := by
  rw [sub_eq_add_neg, neg_iInf, add_comm, iSup_add_coe]
  exact iSup_congr fun i => by rw [add_comm, ← sub_eq_add_neg]

/-- An arbitrary constant may be moved in and out of an infimum **whose value is not `⊥`**. Note
where the hypothesis sits: for suprema (`EReal.biSup_add_of_ne_bot`) it is the *values* that
must avoid `⊥`; here it is the infimum itself. -/
theorem add_iInf_of_ne_bot {ι : Sort*} [Nonempty ι] (a : EReal) (u : ι → EReal)
    (hu : (⨅ i, u i) ≠ ⊥) : a + (⨅ i, u i) = ⨅ i, (a + u i) := by
  have hui : ∀ i, u i ≠ ⊥ := fun i h => hu (le_bot_iff.1 (h ▸ iInf_le u i))
  induction a with
  | bot =>
    have h : ∀ i, (⊥ : EReal) + u i = ⊥ := fun i => EReal.bot_add (u i)
    rw [EReal.bot_add]
    simp only [h, iInf_const]
  | coe r =>
    rw [add_comm, iInf_add_coe]
    exact iInf_congr fun i => add_comm _ _
  | top =>
    have h : ∀ i, (⊤ : EReal) + u i = ⊤ := fun i => by
      rw [add_comm]; exact EReal.add_top_of_ne_bot (hui i)
    rw [add_comm, EReal.add_top_of_ne_bot hu]
    simp only [h, iInf_const]

/-- The mirror of `EReal.add_iInf_of_ne_bot`, with the constant on the right. -/
theorem iInf_add_of_ne_bot {ι : Sort*} [Nonempty ι] (u : ι → EReal)
    (hu : (⨅ i, u i) ≠ ⊥) (c : EReal) : (⨅ i, u i) + c = ⨅ i, (u i + c) := by
  rw [add_comm, add_iInf_of_ne_bot c u hu]
  exact iInf_congr fun i => add_comm _ _

/-- **An infimum of `⊥` survives adding any constant but `⊤`.** -/
theorem iInf_add_eq_bot {ι : Sort*} [Nonempty ι] {u : ι → EReal} (hu : (⨅ i, u i) = ⊥)
    {c : EReal} (hc : c ≠ ⊤) : (⨅ i, (u i + c)) = ⊥ := by
  induction c with
  | bot => simp
  | coe r => rw [← iInf_add_coe, hu, EReal.bot_add]
  | top => exact absurd rfl hc

/-- **The infimum of a sum splits**, provided neither infimum is `⊥`. The infimal mirror of
`EReal.biSup_add_biSup`, but with a *different* hypothesis: for suprema it is the values that
must avoid `⊥`, here it is the two infima themselves. -/
theorem iInf_add_iInf_of_ne_bot {ι κ : Sort*} [Nonempty ι] [Nonempty κ]
    (u : ι → EReal) (v : κ → EReal) (hu : (⨅ i, u i) ≠ ⊥) (hv : (⨅ j, v j) ≠ ⊥) :
    (⨅ i, u i) + (⨅ j, v j) = ⨅ i, ⨅ j, (u i + v j) := by
  rw [iInf_add_of_ne_bot u hu]
  exact iInf_congr fun i => add_iInf_of_ne_bot (u i) v hv

/-- **An infimum over a product of a separated sum splits**, under the single hypothesis that
neither infimum is `⊤`. Unlike `EReal.iInf_add_iInf_of_ne_bot`, the `⊥` cases are handled
rather than excluded: when one infimum is `⊥` the other being below `⊤` forces both sides to `⊥`.
Some hypothesis is necessary — for `ψ i = -i` on `ℕ` and `φ ≡ ⊤` the sides are `⊤` and `⊥`. -/
theorem iInf_prod_add {α β : Type*} [Nonempty α] [Nonempty β] (ψ : α → EReal) (φ : β → EReal)
    (hψ : (⨅ a, ψ a) ≠ ⊤) (hφ : (⨅ b, φ b) ≠ ⊤) :
    (⨅ p : α × β, (ψ p.1 + φ p.2)) = (⨅ a, ψ a) + ⨅ b, φ b := by
  have hprod : (⨅ p : α × β, (ψ p.1 + φ p.2)) = ⨅ a, ⨅ b, (ψ a + φ b) := iInf_prod
  rw [hprod]
  by_cases hψb : (⨅ a, ψ a) = ⊥
  · obtain ⟨b₀, hb₀⟩ : ∃ b, φ b ≠ ⊤ := by
      by_contra hcon
      exact hφ (le_antisymm le_top (le_iInf fun b => ge_of_eq (not_not.1 (not_exists.1 hcon b))))
    rw [hψb, EReal.bot_add]
    refine le_antisymm (le_trans (iInf_mono fun a => iInf_le _ b₀) ?_) bot_le
    exact le_of_eq (iInf_add_eq_bot hψb hb₀)
  by_cases hφb : (⨅ b, φ b) = ⊥
  · obtain ⟨a₀, ha₀⟩ : ∃ a, ψ a ≠ ⊤ := by
      by_contra hcon
      exact hψ (le_antisymm le_top (le_iInf fun a => ge_of_eq (not_not.1 (not_exists.1 hcon a))))
    rw [hφb, EReal.add_bot]
    refine le_antisymm (le_trans (iInf_le _ a₀) ?_) bot_le
    refine le_of_eq ?_
    rw [← iInf_add_eq_bot (u := φ) hφb ha₀]
    exact iInf_congr fun b => add_comm _ _
  · exact (iInf_add_iInf_of_ne_bot ψ φ hψb hφb).symm

/-- **A real summand slides out of a difference.** `(p + q) - u = (p - u) + q` for real `p`, `q`
and arbitrary `u : EReal`. -/
theorem coe_add_sub (p q : ℝ) (u : EReal) :
    ((p + q : ℝ) : EReal) - u = (((p : ℝ) : EReal) - u) + ((q : ℝ) : EReal) := by
  rw [EReal.coe_add]
  change ((p : EReal) + (q : EReal)) + -u = ((p : EReal) + -u) + (q : EReal)
  rw [add_assoc, add_assoc, add_comm ((q : ℝ) : EReal) (-u)]

/-- **A real summand slides out of the subtrahend.** `p - (u + q) = (p - q) - u` for real `p`, `q`
and arbitrary `u : EReal`. Both are finite, so no `∞ - ∞` collision arises: at `u = ⊤` both sides
are `⊥` and at `u = ⊥` both sides are `⊤`. -/
theorem coe_sub_add_coe (p q : ℝ) (u : EReal) :
    ((p : ℝ) : EReal) - (u + ((q : ℝ) : EReal)) = ((p - q : ℝ) : EReal) - u := by
  induction u with
  | bot =>
    rw [EReal.bot_add, EReal.sub_bot (EReal.coe_ne_bot p),
      EReal.sub_bot (EReal.coe_ne_bot _)]
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff]
    ring
  | top => rw [EReal.top_add_coe, EReal.sub_top, EReal.sub_top]

/-- **The same difference, folded the other way**: `p - (u + q) = (p - u) + (-q)`. The unprimed
form collects both reals on the left; this one keeps `p - u` intact. Interderivable, but a `rw`
matches one and not the other. -/
theorem coe_sub_add_coe' (p q : ℝ) (u : EReal) :
    ((p : ℝ) : EReal) - (u + ((q : ℝ) : EReal)) = (((p : ℝ) : EReal) - u) + ((-q : ℝ) : EReal) := by
  induction u with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
      ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  | top => simp

/-- **The difference quotient of a sum splits.** For `c > 0`, reals `p`, `q` and `u`, `v` never
`⊥`, `c * (u - p) + c * (v - q) = c * ((u + v) - (p + q))`. This is the `EReal` arithmetic behind
the recession-function half of Rockafellar's Theorem 9.3: the difference quotients defining `f0⁺`
and `g0⁺` add up to the one defining `(f + g)0⁺`. -/
theorem coe_mul_sub_add_coe_mul_sub {c : ℝ} (hc : 0 < c) {u v : EReal} (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (p q : ℝ) :
    (c : EReal) * (u - (p : ℝ)) + (c : EReal) * (v - (q : ℝ))
      = (c : EReal) * ((u + v) - ((p + q : ℝ) : EReal)) := by
  have hsubne : ∀ {w : EReal}, w ≠ ⊥ → ∀ r : ℝ, w - (r : ℝ) ≠ ⊥ := by
    intro w hw r
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_bot_iff.2 ⟨hw, EReal.coe_ne_bot _⟩
  have hcn : ¬ ((c : EReal) < 0) := by
    simp only [not_lt]
    exact_mod_cast hc.le
  have hmulne : ∀ {w : EReal}, w ≠ ⊥ → (c : EReal) * w ≠ ⊥ := by
    intro w hw hbot
    rw [EReal.mul_eq_bot] at hbot
    rcases hbot with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
    · exact EReal.coe_ne_bot c h1
    · exact hw h2
    · exact EReal.coe_ne_top c h3
    · exact hcn h4
  rcases eq_top_or_lt_top u with hut | hut
  · have huv : u + v = ⊤ := by rw [hut]; exact EReal.top_add_of_ne_bot hv
    rw [huv, hut, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hc,
      EReal.top_add_of_ne_bot (hmulne (hsubne hv q))]
  rcases eq_top_or_lt_top v with hvt | hvt
  · have huv : u + v = ⊤ := by rw [hvt]; exact EReal.add_top_of_ne_bot hu
    rw [huv, hvt, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hc,
      EReal.add_top_of_ne_bot (hmulne (hsubne hu p))]
  obtain ⟨r, hr⟩ := exists_coe_of_ne_bot_of_lt_top hu hut
  obtain ⟨s, hs⟩ := exists_coe_of_ne_bot_of_lt_top hv hvt
  rw [hr, hs, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub,
    ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add]
  norm_cast
  ring

/-- **Two slack inequalities cannot compensate each other.** If `u` and `v` are bounded below by
reals `p` and `q`, and their sum is bounded above by `p + q`, then each is pinned to its own bound.
Stated one-sided; apply it again with `add_comm` for the other summand. Rockafellar's Theorem 23.8
is where it is needed: the exact-sum hypothesis delivers one *joint* equality in Fenchel's
inequality, and this splits it into `y₁ ∈ ∂f x` and `y₂ ∈ ∂g x`. -/
theorem le_coe_of_add_le_coe_add {p q : ℝ} {u v : EReal} (hp : (p : EReal) ≤ u)
    (hq : (q : EReal) ≤ v) (h : u + v ≤ ((p + q : ℝ) : EReal)) : u ≤ (p : EReal) := by
  have hub : u ≠ ⊥ := ((EReal.bot_lt_coe p).trans_le hp).ne'
  have hvb : v ≠ ⊥ := ((EReal.bot_lt_coe q).trans_le hq).ne'
  have hsum : u + v ≠ ⊤ := fun hc =>
    EReal.coe_ne_top _ (top_le_iff.1 (hc ▸ h))
  obtain ⟨hut, hvt⟩ := (EReal.add_ne_top_iff_ne_top₂ hub hvb).1 hsum
  obtain ⟨a, rfl⟩ := exists_coe_of_ne_bot_of_lt_top hub (lt_top_iff_ne_top.2 hut)
  obtain ⟨b, rfl⟩ := exists_coe_of_ne_bot_of_lt_top hvb (lt_top_iff_ne_top.2 hvt)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [EReal.coe_le_coe_iff] at hp hq ⊢
  linarith

/-- **The `m`-ary form of `EReal.le_coe_of_add_le_coe_add`.** If each `u i` is bounded below
by the real `c i` and the sum of the `u i` is bounded above by the sum of the `c i`, then every one
of the `m` inequalities is tight. The two-summand version does not iterate — there is no
subtraction on `EReal` to peel a summand off with — so the proof splits `s` as `{j} ∪ s.erase j`
and applies it once, with the two partial sums as the second pair. -/
theorem le_coe_of_sum_le_coe_sum {ι : Type*} {s : Finset ι} {c : ι → ℝ} {u : ι → EReal}
    (hle : ∀ i ∈ s, ((c i : ℝ) : EReal) ≤ u i)
    (hsum : ∑ i ∈ s, u i ≤ ((∑ i ∈ s, c i : ℝ) : EReal)) {j : ι} (hj : j ∈ s) :
    u j ≤ ((c j : ℝ) : EReal) := by
  classical
  have hq : ((∑ i ∈ s.erase j, c i : ℝ) : EReal) ≤ ∑ i ∈ s.erase j, u i := by
    rw [coe_sum]
    exact Finset.sum_le_sum fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have hadd : u j + ∑ i ∈ s.erase j, u i
      ≤ ((c j + ∑ i ∈ s.erase j, c i : ℝ) : EReal) := by
    rw [Finset.add_sum_erase s u hj, Finset.add_sum_erase s c hj]
    exact hsum
  exact le_coe_of_add_le_coe_add (hle j hj) hq hadd

end EReal
