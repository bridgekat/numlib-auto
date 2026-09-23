import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth
import Numlib.Analysis.Convex.Duality.InnerPairing

/-!
# Essential strict convexity

A closed proper convex function is *essentially strictly convex* — strictly convex on every convex
subset of `dom ∂f` — exactly when its conjugate is essentially smooth. Together with the matching
characterisation of essential smoothness this is the duality that makes the Legendre transformation
an involution: strict convexity on one side is smoothness on the other. Since `∂f*` is the inverse
of `∂f`, single-valuedness of `∂f*` *is* the statement that distinct points never share a
subgradient of `f`, and `essentiallyStrictlyConvex_iff_pairwise_disjoint` identifies that with
essential strict convexity.

## Main definitions

* `StrictConvexOnFn f C` — `f` satisfies the convexity inequality *strictly* between distinct
  points of `C`.
* `EssentiallyStrictlyConvex f` — `f` is strictly convex on every convex subset of `dom ∂f`.

## Main results

* `mem_subdifferential_of_combo`, `le_combo_of_mem_subdifferential` — a subgradient shared by two
  points is a subgradient at every point between them, and `f` is affine along that segment.
* `mem_subdifferential_convexConj_innerL_iff`, `pairwise_disjoint_subdifferential_convexConj_iff` —
  `∂f*` inverts `∂f` for the self-pairing, and the transfer it gives between single-valuedness and
  injectivity.
* `essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex` and
  `essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth` — the duality, both ways round
  ([rockafellar1970convex] Theorem 26.3).
* `subdifferential_injective_iff` — `∂f` is one-to-one exactly when `f` is essentially smooth and
  strictly convex on `int (dom f)`.

## Implementation notes

Every value in sight is finite, so the arithmetic is real: points of `dom ∂f` lie in `dom f` and
`f` is proper. The only `EReal` case split is on `f z` at the *test* point of the subgradient
inequality, where `f z = ⊤` makes it trivial. The definitions need only a real vector space;
The duality needs an inner-product space, because `EssentiallySmooth` does.

## References

* [rockafellar1970convex] §26.
-/

namespace ConvexAnalysis

open Filter Metric Topology

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **Strict convexity on a set.** Between two *distinct* points of `C` the convexity inequality
is strict. Nothing is asked off `C`, and nothing is asked about the finiteness of `f`. -/
def StrictConvexOnFn (f : E → EReal) (C : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < (a : EReal) * f x + (b : EReal) * f y

/-- Strict convexity is inherited by subsets. -/
theorem StrictConvexOnFn.mono {C D : Set E} (h : StrictConvexOnFn f C) (hDC : D ⊆ C) :
    StrictConvexOnFn f D := fun _ hx _ hy hne _ _ ha hb hab =>
  h (hDC hx) (hDC hy) hne ha hb hab

/-- **The bridge to Mathlib's `StrictConvexOn`.** On a convex set where `f` is finite, strict
convexity of the `EReal`-valued `f` and of its real trace are the same condition — and so the only
way in for a *concrete* function, since Mathlib's strict-convexity API and its second-derivative
criteria are stated for real-valued functions. Finiteness is needed in both directions: where
`f x = ⊤` the `EReal` inequality is vacuous and the real one is not, and where `f x = ⊥` the real
one is vacuous and the `EReal` one is not. -/
theorem strictConvexOnFn_iff_strictConvexOn {C : Set E} (hC : Convex ℝ C)
    (hbot : ∀ x ∈ C, f x ≠ ⊥) (htop : ∀ x ∈ C, f x ≠ ⊤) :
    StrictConvexOnFn f C ↔ StrictConvexOn ℝ C (fun x => (f x).toReal) := by
  have hcoe : ∀ x ∈ C, f x = (((f x).toReal : ℝ) : EReal) := fun x hx =>
    (EReal.coe_toReal (htop x hx) (hbot x hx)).symm
  constructor
  · refine fun h => ⟨hC, fun x hx y hy hne a b ha hb hab => ?_⟩
    have hlt := h hx hy hne ha hb hab
    rw [hcoe x hx, hcoe y hy, hcoe _ (hC hx hy ha.le hb.le hab), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
    simpa using hlt
  · intro h x hx y hy hne a b ha hb hab
    have hlt := h.2 hx hy hne ha hb hab
    rw [hcoe x hx, hcoe y hy, hcoe _ (hC hx hy ha.le hb.le hab), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    simpa using hlt

/-- **Essential strict convexity**: `f` is strictly convex on every convex subset of `dom ∂f`.
This is *weaker* than strict convexity on `dom f` and *stronger* than strict convexity on
`ri (dom f)`, and examples separate it from both. -/
def EssentiallyStrictlyConvex (f : E → EReal) : Prop :=
  ∀ ⦃C : Set E⦄, Convex ℝ C → C ⊆ domSubdifferential B f → StrictConvexOnFn f C

/-- **The subgradient inequality between real numbers.** Both values are finite — `f x` because a
subgradient exists there, `f z` by hypothesis — so the `EReal` inequality is a real one. -/
theorem sub_le_of_mem_subdifferential (hp : ProperConvex f) {v : F} {x z : E}
    (h : v ∈ subdifferential B f x) (hz : z ∈ convexDom f) :
    (f x).toReal + B (z - x) v ≤ (f z).toReal := by
  have hle := h z
  have hxt : f x ≠ ⊤ := (mem_convexDom.1 (mem_convexDom_of_mem_subdifferential hp h)).ne
  have hzt : f z ≠ ⊤ := (mem_convexDom.1 hz).ne
  rw [← EReal.coe_toReal hxt (hp.ne_bot x), ← EReal.coe_toReal hzt (hp.ne_bot z),
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  exact hle

/-- The subgradient inequality, in the direction that has to be *proved*: a real bound at every
point of `dom f` is the `EReal` subgradient inequality everywhere, since off `dom f` it reads
`≤ ⊤`. -/
theorem mem_subdifferential_of_forall_sub_le (hp : ProperConvex f) {v : F} {x : E}
    (hx : x ∈ convexDom f)
    (h : ∀ z ∈ convexDom f, (f x).toReal + B (z - x) v ≤ (f z).toReal) : v
        ∈ subdifferential B f x := by
  intro z
  by_cases hz : z ∈ convexDom f
  · rw [← EReal.coe_toReal (mem_convexDom.1 hx).ne (hp.ne_bot x),
      ← EReal.coe_toReal (mem_convexDom.1 hz).ne (hp.ne_bot z), ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    exact h z hz
  · rw [top_le_iff.1 (not_lt.1 fun hlt => hz (mem_convexDom.2 hlt))]
    exact le_top

end Defs

section Segment

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {v : F} {x₁ x₂ : E} {a b : ℝ}

/-- The pairing at a convex combination splits, because `z - (a x₁ + b x₂)` is the same
combination of `z - x₁` and `z - x₂`. -/
theorem pairing_sub_combo (hab : a + b = 1) (z : E) :
    B (z - (a • x₁ + b • x₂)) v = a * B (z - x₁) v + b * B (z - x₂) v := by
  have hsplit : z - (a • x₁ + b • x₂) = a • (z - x₁) + b • (z - x₂) := by
    rw [smul_sub, smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_add, LinearMap.add_apply, map_smul, map_smul,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

/-- The pairing from a convex combination back to the first endpoint. -/
theorem pairing_combo_sub_left (hab : a + b = 1) :
    B (a • x₁ + b • x₂ - x₁) v = b * B (x₂ - x₁) v := by
  have hsplit : a • x₁ + b • x₂ - x₁ = b • (x₂ - x₁) := by
    rw [smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- The pairing from a convex combination back to the second endpoint. -/
theorem pairing_combo_sub_right (hab : a + b = 1) :
    B (a • x₁ + b • x₂ - x₂) v = -(a * B (x₂ - x₁) v) := by
  have hsplit : a • x₁ + b • x₂ - x₂ = (-a) • (x₂ - x₁) := by
    rw [smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **A subgradient shared by two points is a subgradient all along the segment between them.**
The graph of `⟨·, v⟩ - f*(v)` is a supporting hyperplane touching `epi f` at both endpoints, so it
touches it along the whole segment. -/
theorem mem_subdifferential_of_combo (hf : ConvexFn f) (hp : ProperConvex f)
    (h₁ : v ∈ subdifferential B f x₁) (h₂ : v ∈ subdifferential B f x₂)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    v ∈ subdifferential B f (a • x₁ + b • x₂) := by
  have hx₁ : x₁ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₁
  have hx₂ : x₂ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₂
  have hcomb : a • x₁ + b • x₂ ∈ convexDom f := hf.convex_convexDom hx₁ hx₂ ha.le hb.le hab
  refine mem_subdifferential_of_forall_sub_le hp hcomb fun z hz => ?_
  -- The combination's value is bounded by the combination of the endpoint values.
  have hcv := (convexFn_iff_le hp.ne_bot).1 hf x₁ x₂ a b ha hb hab
  have hreal : (f (a • x₁ + b • x₂)).toReal ≤ a * (f x₁).toReal + b * (f x₂).toReal := by
    rw [← EReal.coe_toReal (mem_convexDom.1 hx₁).ne (hp.ne_bot x₁),
      ← EReal.coe_toReal (mem_convexDom.1 hx₂).ne (hp.ne_bot x₂),
      ← EReal.coe_toReal (mem_convexDom.1 hcomb).ne (hp.ne_bot _), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcv
    exact hcv
  rw [pairing_sub_combo hab z]
  have hA := mul_le_mul_of_nonneg_left (sub_le_of_mem_subdifferential hp h₁ hz) ha.le
  have hB' := mul_le_mul_of_nonneg_left (sub_le_of_mem_subdifferential hp h₂ hz) hb.le
  have hsum : a * (f z).toReal + b * (f z).toReal = (f z).toReal := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- **A shared subgradient makes `f` affine along the segment**, so the convexity inequality there
is an *equality* and strict convexity fails. -/
theorem le_combo_of_mem_subdifferential (hp : ProperConvex f) (h₁ : v ∈ subdifferential B f x₁)
    (h₂ : v ∈ subdifferential B f x₂) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hcomb : a • x₁ + b • x₂ ∈ convexDom f) :
    (a : EReal) * f x₁ + (b : EReal) * f x₂ ≤ f (a • x₁ + b • x₂) := by
  have hx₁ : x₁ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₁
  have hx₂ : x₂ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₂
  have hs₁ := sub_le_of_mem_subdifferential hp h₁ hcomb
  have hs₂ := sub_le_of_mem_subdifferential hp h₂ hcomb
  rw [pairing_combo_sub_left hab] at hs₁
  rw [pairing_combo_sub_right hab] at hs₂
  have hA := mul_le_mul_of_nonneg_left hs₁ ha.le
  have hB' := mul_le_mul_of_nonneg_left hs₂ hb.le
  have hsum : a * (f (a • x₁ + b • x₂)).toReal + b * (f (a • x₁ + b • x₂)).toReal
      = (f (a • x₁ + b • x₂)).toReal := by rw [← add_mul, hab, one_mul]
  rw [← EReal.coe_toReal (mem_convexDom.1 hx₁).ne (hp.ne_bot x₁),
    ← EReal.coe_toReal (mem_convexDom.1 hx₂).ne (hp.ne_bot x₂),
    ← EReal.coe_toReal (mem_convexDom.1 hcomb).ne (hp.ne_bot _), ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- **The converse computation**: if `f` fails to be strictly convex between `x₁` and `x₂` and has
a subgradient at the point between them, that subgradient serves at both endpoints.

The two endpoint inequalities add up to the failed strict inequality, so neither can be strict. -/
theorem mem_subdifferential_endpoints_of_le_combo (hp : ProperConvex f) (hx₁ : x₁ ∈ convexDom f)
    (hx₂ : x₂ ∈ convexDom f) (hv : v ∈ subdifferential B f (a • x₁ + b • x₂))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hle : a * (f x₁).toReal + b * (f x₂).toReal ≤ (f (a • x₁ + b • x₂)).toReal) :
    v ∈ subdifferential B f x₁ ∧ v ∈ subdifferential B f x₂ := by
  have hcomb : a • x₁ + b • x₂ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp hv
  have hs₁ := sub_le_of_mem_subdifferential hp hv hx₁
  have hs₂ := sub_le_of_mem_subdifferential hp hv hx₂
  rw [show x₁ - (a • x₁ + b • x₂) = -(a • x₁ + b • x₂ - x₁) by abel, map_neg,
    LinearMap.neg_apply, pairing_combo_sub_left hab] at hs₁
  rw [show x₂ - (a • x₁ + b • x₂) = -(a • x₁ + b • x₂ - x₂) by abel, map_neg,
    LinearMap.neg_apply, pairing_combo_sub_right hab] at hs₂
  have hsum : a * (f (a • x₁ + b • x₂)).toReal + b * (f (a • x₁ + b • x₂)).toReal
      = (f (a • x₁ + b • x₂)).toReal := by rw [← add_mul, hab, one_mul]
  -- Both endpoint inequalities are equalities.
  have he₁ : (f (a • x₁ + b • x₂)).toReal - b * B (x₂ - x₁) v = (f x₁).toReal := by
    refine le_antisymm (by linarith) (le_of_mul_le_mul_left ?_ ha)
    have hB' := mul_le_mul_of_nonneg_left hs₂ hb.le
    linarith
  have he₂ : (f (a • x₁ + b • x₂)).toReal + a * B (x₂ - x₁) v = (f x₂).toReal := by
    refine le_antisymm (by linarith) (le_of_mul_le_mul_left ?_ hb)
    have hA := mul_le_mul_of_nonneg_left hs₁ ha.le
    linarith
  constructor
  · refine mem_subdifferential_of_forall_sub_le hp hx₁ fun z hz => ?_
    have hz' := sub_le_of_mem_subdifferential hp hv hz
    have hlin : B (z - x₁) v = B (z - (a • x₁ + b • x₂)) v + b * B (x₂ - x₁) v := by
      rw [show z - x₁ = (z - (a • x₁ + b • x₂)) + (a • x₁ + b • x₂ - x₁) by abel, map_add,
        LinearMap.add_apply, pairing_combo_sub_left hab]
    rw [hlin, ← he₁]
    linarith
  · refine mem_subdifferential_of_forall_sub_le hp hx₂ fun z hz => ?_
    have hz' := sub_le_of_mem_subdifferential hp hv hz
    have hlin : B (z - x₂) v = B (z - (a • x₁ + b • x₂)) v - a * B (x₂ - x₁) v := by
      rw [show z - x₂ = (z - (a • x₁ + b • x₂)) + (a • x₁ + b • x₂ - x₂) by abel, map_add,
        LinearMap.add_apply, pairing_combo_sub_right hab]
      ring
    rw [hlin, ← he₂]
    linarith

end Segment

section Reformulation

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **The reformulation the duality runs on**: a proper convex function is essentially strictly
convex exactly when two distinct points never share a subgradient. Forwards, a shared subgradient
makes the whole segment lie in `dom ∂f` and `f` affine on it, so strict convexity fails there.
Backwards, a failure of strict convexity on a convex `C ⊆ dom ∂f` puts a subgradient at a point
between two points of `C`, and the failed inequality forces it to serve at both of them. -/
theorem essentiallyStrictlyConvex_iff_pairwise_disjoint (hf : ConvexFn f) (hp : ProperConvex f) :
    EssentiallyStrictlyConvex (B := B) f ↔
      ∀ x₁ x₂ : E, x₁ ≠ x₂ → Disjoint (subdifferential B f x₁) (subdifferential B f x₂) := by
  constructor
  · intro hes x₁ x₂ hne
    rw [Set.disjoint_left]
    intro v h₁ h₂
    -- The segment lies in `dom ∂f`.
    have hseg : segment ℝ x₁ x₂ ⊆ domSubdifferential B f := by
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1
        simpa using ⟨v, h₂⟩
      rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simpa using ⟨v, h₁⟩
      exact ⟨v, mem_subdifferential_of_combo hf hp h₁ h₂ ha' hb' hab⟩
    have hstrict := hes (convex_segment x₁ x₂) hseg (left_mem_segment ℝ x₁ x₂)
      (right_mem_segment ℝ x₁ x₂) hne (a := 1/2) (b := 1/2) (by norm_num) (by norm_num)
      (by norm_num)
    have hcomb : (1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂ ∈ convexDom f :=
      hf.convex_convexDom (mem_convexDom_of_mem_subdifferential hp h₁)
          (mem_convexDom_of_mem_subdifferential hp h₂)
        (by norm_num) (by norm_num) (by norm_num)
    exact absurd (le_combo_of_mem_subdifferential hp h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
      hcomb) (not_le.2 hstrict)
  · intro hdisj C hC hCsub x₁ hx₁ x₂ hx₂ hne a b ha hb hab
    by_contra hcon
    push Not at hcon
    have hmem : a • x₁ + b • x₂ ∈ C := hC hx₁ hx₂ ha.le hb.le hab
    obtain ⟨v, hv⟩ := hCsub hmem
    have hx₁d : x₁ ∈ convexDom f := domSubdifferential_subset_convexDom hp (hCsub hx₁)
    have hx₂d : x₂ ∈ convexDom f := domSubdifferential_subset_convexDom hp (hCsub hx₂)
    have hcombd : a • x₁ + b • x₂ ∈ convexDom f := hf.convex_convexDom hx₁d hx₂d ha.le hb.le hab
    have hle : a * (f x₁).toReal + b * (f x₂).toReal ≤ (f (a • x₁ + b • x₂)).toReal := by
      rw [← EReal.coe_toReal (mem_convexDom.1 hx₁d).ne (hp.ne_bot x₁),
        ← EReal.coe_toReal (mem_convexDom.1 hx₂d).ne (hp.ne_bot x₂),
        ← EReal.coe_toReal (mem_convexDom.1 hcombd).ne (hp.ne_bot _), ← EReal.coe_mul,
        ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcon
      exact hcon
    obtain ⟨hsub₁, hsub₂⟩ :=
      mem_subdifferential_endpoints_of_le_combo hp hx₁d hx₂d hv ha hb hab hle
    exact (Set.disjoint_left.1 (hdisj x₁ x₂ hne)) hsub₁ hsub₂

end Reformulation

section Conjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **`∂f*` is the inverse of `∂f`**, for the self-pairing of an inner-product space. The flip of
`innerₗ E` is discharged once here so that no later rewrite has to reach inside `convexConj`. -/
theorem mem_subdifferential_convexConj_innerL_iff (hf : ConvexFn f) (hcl : ClosedConvex f)
    (u w : E) :
    u ∈ subdifferential (innerₗ E) (convexConj (innerₗ E) f) w ↔ w
        ∈ subdifferential (innerₗ E) f u := by
  have h :=
    mem_subdifferential_convexConj_iff_of_closedConvex (B := innerₗ E) (f := f) (x := u)
        (y := w) hf hcl
  rwa [flip_innerₗ] at h

/-- Single-valuedness of `∂f*` is injectivity of `∂f`. -/
theorem subsingleton_subdifferential_convexConj_iff (hf : ConvexFn f) (hcl : ClosedConvex f) :
    (∀ w : E, (subdifferential (innerₗ E) (convexConj (innerₗ E) f) w).Subsingleton) ↔
      ∀ x₁ x₂ : E, x₁ ≠ x₂ →
        Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂) := by
  constructor
  · intro h x₁ x₂ hne
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    exact hne (h v ((mem_subdifferential_convexConj_innerL_iff hf hcl x₁ v).2 hv₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₂ v).2 hv₂))
  · intro h v x₁ hx₁ x₂ hx₂
    by_contra hne
    exact (Set.disjoint_left.1 (h x₁ x₂ hne))
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₁ v).1 hx₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₂ v).1 hx₂)

/-- Injectivity of `∂f*` is single-valuedness of `∂f` — the mirror of
`subsingleton_subdifferential_convexConj_iff`. -/
theorem pairwise_disjoint_subdifferential_convexConj_iff (hf : ConvexFn f) (hcl : ClosedConvex f) :
    (∀ y₁ y₂ : E, y₁ ≠ y₂ →
        Disjoint (subdifferential (innerₗ E) (convexConj (innerₗ E) f) y₁)
          (subdifferential (innerₗ E) (convexConj (innerₗ E) f) y₂)) ↔
      ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton := by
  constructor
  · intro h z y₁ hy₁ y₂ hy₂
    by_contra hne
    exact (Set.disjoint_left.1 (h y₁ y₂ hne))
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₁).2 hy₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₂).2 hy₂)
  · intro h y₁ y₂ hne
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hne (h z ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₁).1 hz₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₂).1 hz₂))

/-- A closed proper convex function is essentially strictly convex exactly when its conjugate is
essentially smooth. -/
theorem essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    EssentiallySmooth (convexConj (innerₗ E) f) ↔ EssentiallyStrictlyConvex (B := innerₗ E) f := by
  have hcp : ClosedProperConvexFn f := ⟨hf, hcl, hp⟩
  have hgc : ConvexFn (convexConj (innerₗ E) f) := convexFn_convexConj _ f
  have hgp : ProperConvex (convexConj (innerₗ E) f) := properConvex_convexConj hcp
  have hgcl : ClosedConvex (convexConj (innerₗ E) f) := closedConvex_convexConj
  rw [← subsingleton_subdifferential_iff_essentiallySmooth hgc hgp hgcl,
    essentiallyStrictlyConvex_iff_pairwise_disjoint hf hp,
    subsingleton_subdifferential_convexConj_iff hf hcl]

/-- `f** = f` for the self-pairing of an inner-product space, with the flip of `innerₗ E`
discharged so that the equation is stated in terms of `convexConj (innerₗ E)` twice. -/
theorem convexConj_convexConj_innerL (hf : ConvexFn f) (hcl : ClosedConvex f) :
    convexConj (innerₗ E) (convexConj (innerₗ E) f) = f := by
  have h : convexConj ((innerₗ E).flip) (convexConj (innerₗ E) f) = f := convexBiconj_eq_self hf hcl
  rwa [flip_innerₗ] at h

/-- The same duality read in the other direction: the conjugate of a closed proper convex function
is essentially strictly convex exactly when the function itself is essentially smooth. This is the
previous theorem applied to `f*`, together with `f** = f`. -/
theorem essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    EssentiallyStrictlyConvex (B := innerₗ E) (convexConj (innerₗ E) f) ↔ EssentiallySmooth f := by
  rw [← essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex (convexFn_convexConj _ f)
    (properConvex_convexConj ⟨hf, hcl, hp⟩) closedConvex_convexConj,
        convexConj_convexConj_innerL hf hcl]

/-- `∂f` is a one-to-one mapping — single-valued and injective — exactly when `f` is essentially
smooth and strictly convex on `int (dom f)`. Under essential smoothness `dom ∂f` *is*
`int (dom f)`, so essential strict convexity, which quantifies over all convex subsets of
`dom ∂f`, collapses to strict convexity on that one set. -/
theorem subdifferential_injective_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    ((∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ∧
        ∀ x₁ x₂ : E, x₁ ≠ x₂ →
          Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂)) ↔
      (EssentiallySmooth f ∧ StrictConvexOnFn f (interior (convexDom f))) := by
  have hdom : Convex ℝ (convexDom f) := hf.convex_convexDom
  rw [subsingleton_subdifferential_iff_essentiallySmooth hf hp hcl,
    ← essentiallyStrictlyConvex_iff_pairwise_disjoint hf hp]
  refine and_congr_right fun hes => ⟨fun h => ?_, fun h => ?_⟩
  · refine h hdom.interior fun z hz => ?_
    rw [mem_domSubdifferential, subdifferential_eq_singleton_of_essentiallySmooth hf hes hz]
    exact Set.singleton_nonempty _
  · refine fun C hC hCsub => h.mono fun z hz => ?_
    by_contra hzint
    obtain ⟨v, hv⟩ := hCsub hz
    rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hzint] at hv
    exact absurd hv (Set.notMem_empty v)

end Conjugate

end ConvexAnalysis
