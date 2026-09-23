import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Extremum.Minimum

/-!
# Moreau's decomposition

For a space paired with itself by a symmetric positive definite form `B` whose quadratic form is
continuous, the quadratic `w z = ½ B z z` is its own conjugate, and infimal convolution with it
splits `w` between a closed proper convex function and its conjugate:

`(f □ w) + (f* □ w) = w`.

This is the identity half of **Moreau's decomposition**. Attainment, uniqueness and the `prox`
operator are in `Extremum/Prox.lean`, which needs finite dimensions; the gradient formulas are
in `Extremum/MoreauGradient.lean`.

## Main definitions

* `quadFn B` — `w z = ½ B z z`, as an `EReal`-valued function.

## Main results

* `convexConj_quadFn` — the quadratic is self-conjugate under its own pairing.
* `convexConj_quadFn_sub` — `(w (z - ·))* y = B z y + w y`.
* `moreau_add` — **Moreau's decomposition**: `(f □ w) z + (f* □ w) z = w z`
  ([rockafellar1970convex] Theorem 31.5).
* `infConv_quadFn_ne_top`, `infConv_quadFn_ne_bot` — both Moreau envelopes are finite.
* `mem_subdifferential_iff_infConv_eq` — the Kuhn–Tucker conditions attached to a splitting
  `z = x + y`.

## Implementation notes

The identity is `⨅ φ = -φ* 0` applied to `φ = f + w (z - ·)`, with the conjugate of that sum split
at the origin. The constraint qualification is continuity of `w (z - ·)` rather than a
relative-interior condition, so no finite-dimensionality is needed. Everything goes through `B` and
never through the norm, so the theorem applies verbatim on a product space carrying
`prodPairing (innerₗ U) (innerₗ X)` and no `InnerProductSpace` instance; the inner-product case is
recovered by `quadFn_innerL`.

## References

* [rockafellar1970convex] §31.
-/

open RealInnerProductSpace

namespace ConvexAnalysis

/-! ### The quadratic `w z = ½ B z z` -/

section Quadratic

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- The quadratic `w z = ½ B z z`, `EReal`-valued so that it lives alongside `convexConj` and
`infConv`. -/
noncomputable def quadFn (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E → EReal :=
  fun z => ((B z z / 2 : ℝ) : EReal)

theorem quadFn_apply (z : E) : quadFn B z = ((B z z / 2 : ℝ) : EReal) := rfl

theorem quadFn_ne_bot (z : E) : quadFn B z ≠ ⊥ := EReal.coe_ne_bot _

theorem quadFn_ne_top (z : E) : quadFn B z ≠ ⊤ := EReal.coe_ne_top _

@[simp] theorem quadFn_neg (z : E) : quadFn B (-z) = quadFn B z := by
  rw [quadFn_apply, quadFn_apply, self_pairing_neg]

/-- The quadratic translated to the origin is the quadratic: `w (0 - ·) = w`. -/
theorem quadFn_zero_sub : (fun u : E => quadFn B (0 - u)) = quadFn B := by
  funext u
  rw [zero_sub, quadFn_neg]

variable [IsInnerPairing B]

/-- `x ↦ w (z - x)` is convex: the defect is `½ a b B (u - v) (u - v) ≥ 0`. -/
theorem convexFn_quadFn_sub (z : E) : ConvexFn (fun x => quadFn B (z - x)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  rw [quadFn_apply, EReal.coe_le_coe_iff] at hx hy
  have harg : z - (a • x + b • y) = a • (z - x) + b • (z - y) := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
  rw [quadFn_apply, harg, EReal.coe_le_coe_iff]
  refine le_trans (self_pairing_combo_le ha hb hab) ?_
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- `w` is a convex function. -/
theorem convexFn_quadFn : ConvexFn (quadFn B) := by
  rw [← quadFn_zero_sub]
  exact convexFn_quadFn_sub 0

omit [IsInnerPairing B] in
/-- `x ↦ w (z - x)` is proper: it is finite everywhere. -/
theorem properConvex_quadFn_sub (z : E) : ProperConvex (fun x => quadFn B (z - x)) :=
  ⟨⟨z, mem_convexDom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))⟩, fun _ => quadFn_ne_bot _⟩

/-- **The quadratic is self-conjugate** under its own pairing: `w* = w`. The supremum
`⨆ x (B x y - ½ B x x)` has defect `½ B (x - y) (x - y)` and is attained at `x = y`. -/
theorem convexConj_quadFn (y : E) : convexConj B (quadFn B) y = quadFn B y := by
  rw [convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · rw [quadFn_apply, quadFn_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith [self_pairing_sub (B := B) x y, self_pairing_nonneg B (x - y)]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun x : E => ((B x y : ℝ) : EReal) - quadFn B x) y)
    rw [quadFn_apply, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring

/-- **The conjugate of a translate of the quadratic**: `(w (z - ·))* y = B z y + w y`. The supremum
has defect `½ B ((x - z) - y) ((x - z) - y)` and is attained at `x = z + y`. -/
theorem convexConj_quadFn_sub (z y : E) :
    convexConj B (fun x => quadFn B (z - x)) y = ((B z y : ℝ) : EReal) + quadFn B y := by
  have hsub : ∀ u : E, B (u - z) y = B u y - B z y := fun u => by
    rw [map_sub, LinearMap.sub_apply]
  rw [convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · rw [quadFn_apply, quadFn_apply, ← EReal.coe_sub, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith [self_pairing_sub (B := B) (x - z) y, self_pairing_nonneg B (x - z - y), hsub x,
      self_pairing_sub_rev (B := B) z x]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun x : E => ((B x y : ℝ) : EReal) - quadFn B (z - x)) (z + y))
    have harg : z - (z + y) = -y := by abel
    have hadd : B (z + y) y = B z y + B y y := by rw [map_add, LinearMap.add_apply]
    rw [harg, quadFn_apply, quadFn_apply, ← EReal.coe_add, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff, hadd, self_pairing_neg]
    ring

end Quadratic

/-! ### The quadratic in a topological space -/

section QuadraticTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B]

/-- `x ↦ w (z - x)` is continuous: the constraint qualification the theorem uses. -/
theorem continuous_quadFn_sub (z : E) : Continuous (fun x => quadFn B (z - x)) := by
  have h : Continuous fun x : E => (B (z - x) (z - x) / 2 : ℝ) :=
    ((continuous_self_pairing' B).comp (continuous_const.sub continuous_id)).div_const 2
  exact continuous_coe_real_ereal.comp h

end QuadraticTopology

/-! ### The inner-product instance -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a real inner-product space the quadratic is `½‖z‖²`. -/
@[simp] theorem quadFn_innerL (z : E) : quadFn (innerₗ E) z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal) := by
  rw [quadFn_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq]

end Inner

/-! ### Moreau's decomposition -/

section Moreau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] [IsCompatiblePairing B] {f : E → EReal}

private theorem iInf_comp_sub {α : Type*} [AddCommGroup α] (φ : α → EReal) (z : α) :
    (⨅ x, φ (z - x)) = ⨅ y, φ y :=
  le_antisymm
    (le_iInf fun y => le_trans (iInf_le (fun x => φ (z - x)) (z - y))
      (le_of_eq (by rw [sub_sub_cancel])))
    (le_iInf fun x => iInf_le φ (z - x))

private theorem iInf_comp_neg {α : Type*} [AddCommGroup α] (φ : α → EReal) :
    (⨅ y, φ y) = ⨅ y, φ (-y) :=
  le_antisymm (le_iInf fun y => iInf_le φ (-y))
    (le_iInf fun y => le_trans (iInf_le (fun w => φ (-w)) (-y)) (le_of_eq (by rw [neg_neg])))

omit [IsContinuousInnerPairing B] [IsCompatiblePairing B] in
/-- The **Moreau envelope** written out: `(f □ w) z = inf_x {f x + w (z - x)}`. -/
theorem infConv_quadFn_apply (hb : ∀ x, f x ≠ ⊥) (z : E) :
    infConv f (quadFn B) z = ⨅ x, (f x + quadFn B (z - x)) := by
  rw [infConv_apply hb (fun x => quadFn_ne_bot x) z,
    ← iInf_comp_sub (fun y => f (z - y) + quadFn B y) z]
  exact iInf_congr fun x => by rw [sub_sub_cancel]

/-- **Moreau's decomposition**: infimal convolution with the quadratic splits the quadratic between
`f` and `f*`. The proof is `⨅ φ = -φ* 0` for `φ = f + w (z - ·)`, with the conjugate of that sum
split at the origin; the sign flip `y ↦ -y` turns `⟨z, y⟩ + w y` into `w (z - y) - w z`. -/
theorem moreau_add (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z + infConv (convexConj B f) (quadFn B) z = quadFn B z := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  obtain ⟨y₀, hy₀⟩ := (properConvex_convexConj hf (B := B)).convexDom_nonempty
  have hex : IsExactSum (B) f (fun x => quadFn B (z - x)) :=
    (IsExactSum.of_continuousAt (convexFn_quadFn_sub z) (properConvex_quadFn_sub z) hf.convex
        hf.proper
      (mem_convexDom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))) hx₀
      (continuous_quadFn_sub z).continuousAt).symm
  have hD : infConv (convexConj B f) (quadFn B) z
      = ⨅ y, (convexConj B f y + quadFn B (z - y)) :=
    infConv_quadFn_apply (convexConj_ne_bot hf.proper.convexDom_nonempty) z
  have hP : infConv f (quadFn B) z
      = -(convexConj B (f + fun x => quadFn B (z - x)) 0) := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← iInf_eq_neg_convexConj_zero (B)]
    exact iInf_congr fun x => rfl
  have hstep : ∀ y : E,
      convexConj B f (0 - -y) + convexConj B (fun x => quadFn B (z - x)) (-y)
        = (convexConj B f y + quadFn B (z - y)) + ((-(B z z / 2) : ℝ) : EReal) := by
    intro y
    have hinner : B z (-y) = -B z y := by rw [map_neg]
    have hreal : B z (-y) + B y y / 2 = B (z - y) (z - y) / 2 + -(B z z / 2) := by
      rw [hinner]
      have h := self_pairing_sub (B := B) z y
      linarith
    rw [convexConj_quadFn_sub, zero_sub, neg_neg, quadFn_neg, quadFn_apply, quadFn_apply,
      ← EReal.coe_add, hreal, EReal.coe_add, ← add_assoc]
  have hQD : convexConj B (f + fun x => quadFn B (z - x)) 0
      = infConv (convexConj B f) (quadFn B) z + ((-(B z z / 2) : ℝ) : EReal) := by
    rw [hex.convexConj_add_apply 0,
      iInf_comp_neg fun y => convexConj B f (0 - y)
        + convexConj B (fun x => quadFn B (z - x)) y,
      hD, EReal.iInf_add_coe]
    exact iInf_congr hstep
  have hDt : infConv (convexConj B f) (quadFn B) z ≠ ⊤ := by
    rw [hD]
    obtain ⟨r, hr⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (convexConj_ne_bot hf.proper.convexDom_nonempty y₀) hy₀
    have hle : (⨅ y, (convexConj B f y + quadFn B (z - y)))
        ≤ convexConj B f y₀ + quadFn B (z - y₀) := iInf_le _ y₀
    rw [hr, quadFn_apply, ← EReal.coe_add] at hle
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  have hQb : convexConj B (f + fun x => quadFn B (z - x)) 0 ≠ ⊥ := by
    intro hc
    have hle := sub_le_convexConj B (f + fun x => quadFn B (z - x)) x₀ 0
    rw [hc, le_bot_iff, EReal.coe_sub_eq_bot_iff] at hle
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
    rw [Pi.add_apply, hp, quadFn_apply, ← EReal.coe_add] at hle
    exact absurd hle (EReal.coe_ne_top _)
  have hDb : infConv (convexConj B f) (quadFn B) z ≠ ⊥ := by
    intro hc
    rw [hc] at hQD
    simp only [EReal.bot_add] at hQD
    exact hQb hQD
  obtain ⟨d, hd⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hDb (lt_top_iff_ne_top.2 hDt)
  rw [hP, hQD, hd, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_add,
    quadFn_apply, EReal.coe_eq_coe_iff]
  ring

private theorem top_add_ne_coe (u : EReal) (r : ℝ) : ⊤ + u ≠ (r : EReal) := by
  rcases eq_or_ne u ⊥ with rfl | hu
  · rw [EReal.add_bot]
    exact (EReal.coe_ne_bot r).symm
  · rw [EReal.top_add_of_ne_bot hu]
    exact (EReal.coe_ne_top r).symm

private theorem bot_add_ne_coe (u : EReal) (r : ℝ) : ⊥ + u ≠ (r : EReal) := by
  rw [EReal.bot_add]
  exact (EReal.coe_ne_bot r).symm

/-- The Moreau envelope of a closed proper convex function is never `+∞`. Both infima in the
decomposition are real, since their sum is. -/
theorem infConv_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply] at h
  exact top_add_ne_coe _ _ h

/-- The Moreau envelope never takes `-∞`. -/
theorem infConv_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply] at h
  exact bot_add_ne_coe _ _ h

/-- The dual Moreau envelope is finite too. -/
theorem infConv_convexConj_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv (convexConj B f) (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, EReal.add_top_of_ne_bot (infConv_quadFn_ne_bot (B := B) hf z), quadFn_apply] at h
  exact absurd h (EReal.coe_ne_top _).symm

/-- The dual Moreau envelope never takes `-∞`. -/
theorem infConv_convexConj_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv (convexConj B f) (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, EReal.add_bot, quadFn_apply] at h
  exact absurd h (EReal.coe_ne_bot _).symm

private theorem eq_coe_of_add_coe_eq_coe {S : EReal} {k m : ℝ}
    (h : S + (k : EReal) = (m : EReal)) : S = ((m - k : ℝ) : EReal) := by
  induction S with
  | bot =>
      rw [EReal.bot_add] at h
      exact absurd h.symm (EReal.coe_ne_bot m)
  | coe s =>
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
      rw [EReal.coe_eq_coe_iff]
      linarith
  | top =>
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot k)] at h
      exact absurd h.symm (EReal.coe_ne_top m)

private theorem finite_of_add_eq_coe {A C : EReal} (hA : A ≠ ⊥) (hC : C ≠ ⊥) {m : ℝ}
    (h : A + C = (m : EReal)) : A ≠ ⊤ ∧ C ≠ ⊤ := by
  induction A <;> induction C <;> simp_all

/-- **The Kuhn–Tucker conditions for the decomposition**: for a splitting `z = x + y`, the pair
`(x, y)` attains both infima exactly when `y ∈ ∂f x`. It follows from `moreau_add`, because
`(f x + w y) + (f* y + w x) = (f x + f* y) + (w x + w y)` while `⟨x, y⟩ + w x + w y = w z`, so
Fenchel's inequality makes the left side at least `w z`, which is the sum of the two infima.

That such a splitting exists and is unique is `Extremum/Prox.lean`. -/
theorem mem_subdifferential_iff_infConv_eq (hf : ClosedProperConvexFn f) {x y z : E}
    (hz : x + y = z) :
    y ∈ subdifferential (B) f x ↔
      f x + quadFn B y = infConv f (quadFn B) z ∧
        convexConj B f y + quadFn B x = infConv (convexConj B f) (quadFn B) z := by
  have hzx : z - x = y := by rw [← hz]; abel
  have hzy : z - y = x := by rw [← hz]; abel
  have hPle : infConv f (quadFn B) z ≤ f x + quadFn B y := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← hzx]
    exact iInf_le _ x
  have hDle : infConv (convexConj B f) (quadFn B) z ≤ convexConj B f y + quadFn B x := by
    rw [infConv_quadFn_apply (convexConj_ne_bot hf.proper.convexDom_nonempty) z, ← hzy]
    exact iInf_le _ y
  have hreal : B y y / 2 + B x x / 2 = B x x / 2 + B y y / 2 := by ring
  have hkey : (f x + quadFn B y) + (convexConj B f y + quadFn B x)
      = (f x + convexConj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) := by
    rw [add_add_add_comm, quadFn_apply, quadFn_apply, ← EReal.coe_add, hreal]
  have hwz : ((B x y : ℝ) : EReal) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) = quadFn B z := by
    rw [← EReal.coe_add, quadFn_apply, ← hz, EReal.coe_eq_coe_iff]
    have h := self_pairing_add (B := B) x y
    linarith
  constructor
  · intro hmem
    have hfen : f x + convexConj B f y = ((B x y : ℝ) : EReal) :=
      hf.proper.mem_subdifferential_iff_add_convexConj_eq.1 hmem
    have hsum : (f x + quadFn B y) + (convexConj B f y + quadFn B x)
        = infConv f (quadFn B) z + infConv (convexConj B f) (quadFn B) z := by
      rw [hkey, hfen, hwz, moreau_add (B := B) hf z]
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (infConv_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top (B := B) hf z))
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (infConv_convexConj_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_convexConj_quadFn_ne_top (B := B) hf z))
    have hAb : f x + quadFn B y ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hp] at hPle
      exact absurd hPle (EReal.coe_ne_bot p)
    have hCb : convexConj B f y + quadFn B x ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hq] at hDle
      exact absurd hDle (EReal.coe_ne_bot q)
    obtain ⟨hAt, hCt⟩ := finite_of_add_eq_coe hAb hCb
      (m := p + q) (by rw [hsum, hp, hq, ← EReal.coe_add])
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hAb (lt_top_iff_ne_top.2 hAt)
    obtain ⟨c, hcc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hCb (lt_top_iff_ne_top.2 hCt)
    rw [hp, ha, EReal.coe_le_coe_iff] at hPle
    rw [hq, hcc, EReal.coe_le_coe_iff] at hDle
    rw [ha, hcc, hp, hq, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_eq_coe_iff] at hsum
    refine ⟨?_, ?_⟩
    · rw [ha, hp, EReal.coe_eq_coe_iff]
      linarith
    · rw [hcc, hq, EReal.coe_eq_coe_iff]
      linarith
  · rintro ⟨h1, h2⟩
    have hsum : (f x + convexConj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal)
        = ((B z z / 2 : ℝ) : EReal) := by
      rw [← hkey, h1, h2, moreau_add hf z, quadFn_apply]
    rw [hf.proper.mem_subdifferential_iff_add_convexConj_eq, eq_coe_of_add_coe_eq_coe hsum,
      EReal.coe_eq_coe_iff, ← hz]
    have h := self_pairing_add (B := B) x y
    linarith

end Moreau

end ConvexAnalysis
