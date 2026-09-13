import Numlib.Analysis.Convex.Optimization.Moreau
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# Proximal mappings, and maximal monotonicity of the subdifferential

For `f` closed proper convex and `w x = ½ B x x`, the infimum defining the Moreau envelope
`(f □ w) z` is attained at exactly one point, the **proximal point** `prox (z | f)`, and the
minimiser is characterised by `z - x ∈ ∂f x`. That is the attainment and uniqueness half of
**Moreau's decomposition**; `Optimization/Moreau.lean` has the identity `(f □ w) + (f* □ w) = w`,
and `Optimization/MoreauGradient.lean` the gradient formulas.

Two corollaries follow from the same monotonicity argument. Proximation is nonexpansive, so
`(x, x*) ↦ x + x*` is a homeomorphism of the graph of `∂f` onto the space, and `∂f` is a *maximal
monotone* mapping — maximal among monotone relations, which is a different statement from the
maximal cyclic monotonicity of a subdifferential.

## Main definitions

* `moreauObj B f z` — the objective `x ↦ f x + w (z - x)`, whose infimum is `(f □ w) z`.
* `prox B f z` — the **proximal point**: the unique minimiser of `moreauObj B f z`, or `0` when
  there is none.

## Main results

* `subdifferential_quadFn_sub` — `∂(w (z - ·)) x = {x - z}`; `recessionFn_quadFn_sub` — `w (z - ·)`
  recedes in no direction but `0`.
* `argmin_moreauObj_nonempty`, `mem_argmin_moreauObj_iff`, `existsUnique_sub_mem_subdifferential`,
  `prox_eq_iff` — the minimum exists, is unique, and solves `z - x ∈ ∂f x`
  ([rockafellar1970convex] Theorem 31.5); `prox_add_prox_conj` — `z = prox (z | f) + prox (z | f*)`.
* `pairingNorm_prox_sub_le`, `dist_prox_prox_le`, `lipschitzWith_prox` — proximation is
  nonexpansive.
* `subgradientRelHomeomorph` — the graph of `∂f` is homeomorphic to `E`;
  `isMaximalMonotoneRel_subgradientRel` — `∂f` is maximal monotone.

## Implementation notes

Everything runs through the pairing `B`, never through the ambient norm, so `prox` is available on
product spaces carrying no `InnerProductSpace` instance; the norm enters only in `continuous_prox`.
`prox` is a `Classical` choice from the minimum set, with value `0` where that set is empty; the
standing hypothesis `ClosedProperConvexFn f` makes the set a singleton. Finite-dimensionality is
used only for attainment of the minimum.

## References

* [rockafellar1970convex] §31.
-/

namespace ConvexAnalysis

/-! ### The Moreau objective and the subdifferential of the quadratic -/

section Objective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] {f : E → EReal}

/-- The objective `x ↦ f x + w (z - x)`, whose infimum over `x` is the envelope `(f □ w) z`. -/
noncomputable def moreauObj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f : E → EReal) (z : E) : E → EReal :=
  f + fun x => quadFn B (z - x)

omit [IsContinuousInnerPairing B] in
theorem moreauObj_def (f : E → EReal) (z : E) :
    moreauObj B f z = f + fun x => quadFn B (z - x) := rfl

omit [IsContinuousInnerPairing B] in
@[simp] theorem moreauObj_apply (f : E → EReal) (z x : E) :
    moreauObj B f z x = f x + quadFn B (z - x) := rfl

/-- `x - z` is a subgradient of `u ↦ w (z - u)` at `x`; the defect in the inequality is
`½ B (u - x) (u - x)`. -/
theorem sub_mem_subdifferential_quadFn_sub (z x : E) :
    x - z ∈ subdifferential B (fun u => quadFn B (z - u)) x := by
  intro u
  simp only [quadFn_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hexp := self_pairing_sub (B := B) (z - x) (u - x)
  have hinner : B (u - x) (x - z) = -B (z - x) (u - x) := by
    rw [show x - z = -(z - x) by abel, map_neg, pairing_comm B (u - x) (z - x)]
  rw [show z - u = (z - x) - (u - x) by abel]
  nlinarith [self_pairing_nonneg B (u - x)]

/-- **The subdifferential of the translated quadratic is a singleton**: `∂(w (z - ·)) x = {x - z}`.
Testing at the point `y + z` forces `½ B ((z - x) + y) ((z - x) + y) ≤ 0`. -/
theorem subdifferential_quadFn_sub (z x : E) :
    subdifferential B (fun u => quadFn B (z - u)) x = {x - z} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · have h := hy (y + z)
    simp only [quadFn_apply, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    have hnorm : B (z - (y + z)) (z - (y + z)) = B y y := by
      rw [show z - (y + z) = -y by abel, self_pairing_neg]
    have hyz : B (y + z - x) y = B y y + B (z - x) y := by
      rw [show y + z - x = y + (z - x) by abel, map_add, LinearMap.add_apply]
    rw [hnorm, hyz] at h
    have hexp := self_pairing_add (B := B) (z - x) y
    have hsq : B ((z - x) + y) ((z - x) + y) ≤ 0 := by nlinarith
    have hz : (z - x) + y = 0 :=
      self_pairing_eq_zero_iff.1 (le_antisymm hsq (self_pairing_nonneg B _))
    rw [Set.mem_singleton_iff, ← sub_eq_zero, show y - (x - z) = (z - x) + y by abel]
    exact hz
  · rw [Set.singleton_subset_iff]
    exact sub_mem_subdifferential_quadFn_sub z x

/-- **The subdifferential of the quadratic is the identity**: `∂w x = {x}`. -/
theorem subdifferential_quadFn (x : E) : subdifferential B (quadFn B) x = {x} := by
  rw [← quadFn_zero_sub, subdifferential_quadFn_sub, sub_zero]

/-- `u ↦ w (z - u)` is closed proper convex: it is finite, convex and continuous. -/
theorem closedProperConvexFn_quadFn_sub (z : E) :
    ClosedProperConvexFn (fun x => quadFn B (z - x)) := by
  refine ⟨convexFn_quadFn_sub z, ?_, proper_quadFn_sub z⟩
  rw [closedFn_iff_lowerSemicontinuous fun _ => quadFn_ne_bot _]
  exact (continuous_quadFn_sub z).lowerSemicontinuous

/-- **The translated quadratic recedes in no direction**: `(w (z - ·))0⁺ y = +∞` for `y ≠ 0`.
Testing `q (x + a • y) ≤ q x + a ν` at `x = z` gives `½ a² B y y ≤ a ν` for every `a ≥ 0`, which
fails for large `a` since `B y y > 0`. -/
theorem recessionFn_quadFn_sub (z : E) {y : E} (hy : y ≠ 0) :
    recessionFn (fun x => quadFn B (z - x)) y = ⊤ := by
  by_contra hne
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (recessionFn_ne_bot (proper_quadFn_sub z) y) (lt_top_iff_ne_top.2 hne)
  have hy2 : 0 < B y y := self_pairing_pos hy
  have ha1 : (1 : ℝ) ≤ max 1 (2 * (|ν| + 1) / B y y) := le_max_left _ _
  have ha0 : (0 : ℝ) ≤ max 1 (2 * (|ν| + 1) / B y y) := le_trans zero_le_one ha1
  have ha3 : 2 * (|ν| + 1) ≤ max 1 (2 * (|ν| + 1) / B y y) * B y y := by
    rw [← div_le_iff₀ hy2]
    exact le_max_right _ _
  have hkey := recessionFn_le_coe_iff_forall.1 (le_of_eq hν) z _ ha0
  have hz : quadFn B (z - z) = ((0 : ℝ) : EReal) := by
    rw [sub_self, quadFn_apply, map_zero]
    norm_num
  have hza : ∀ a : ℝ, quadFn B (z - (z + a • y)) = ((a ^ 2 * B y y / 2 : ℝ) : EReal) := by
    intro a
    rw [show z - (z + a • y) = -(a • y) by abel, quadFn_apply, self_pairing_neg,
      self_pairing_smul]
  simp only [hz, hza, ← EReal.coe_add, EReal.coe_le_coe_iff] at hkey
  nlinarith [hkey, mul_le_mul_of_nonneg_left ha3 ha0,
    mul_le_mul_of_nonneg_left (le_abs_self ν) ha0]

/-- **Uniqueness of the proximal point**: at most one `x` satisfies `z - x ∈ ∂f x`. Monotonicity
of `∂f` gives `0 ≤ B (x₁ - x₂) (-(x₁ - x₂))`, and definiteness finishes. -/
theorem eq_of_sub_mem_subdifferential (hp : Proper f) {z x₁ x₂ : E}
    (h₁ : z - x₁ ∈ subdifferential B f x₁) (h₂ : z - x₂ ∈ subdifferential B f x₂) :
    x₁ = x₂ := by
  have hmono := isMonotoneRel_subgradientRel (B := B) hp (x₁, z - x₁) h₁ (x₂, z - x₂) h₂
  rw [show z - x₁ - (z - x₂) = -(x₁ - x₂) by abel, map_neg] at hmono
  rw [← sub_eq_zero]
  exact self_pairing_eq_zero_iff.1
    (le_antisymm (by linarith) (self_pairing_nonneg B (x₁ - x₂)))

/-- The **proximal mapping** `prox (z | f)`: the point at which `x ↦ f x + w (z - x)` attains its
minimum, and `0` where no minimum exists — which for closed proper convex `f` never happens. -/
noncomputable def prox (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f : E → EReal) (z : E) : E :=
  Classical.epsilon fun x => x ∈ argmin (moreauObj B f z)

end Objective

/-! ### Attainment, uniqueness, and `prox` -/

section Attainment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] [IsCompatiblePairing B]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- The constraint qualification: `w (z - ·)` is finite and continuous, so the conjugate of
`f + w (z - ·)` splits and the subgradient sum rule applies. -/
theorem isExactSum_quadFn_sub (hf : ClosedProperConvexFn f) (z : E) :
    IsExactSum B f (fun x => quadFn B (z - x)) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  exact (IsExactSum.of_continuousAt (convexFn_quadFn_sub z) (proper_quadFn_sub z) hf.convex
    hf.proper (mem_dom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))) hx₀
    (continuous_quadFn_sub z).continuousAt).symm

omit [FiniteDimensional ℝ E] in
/-- The same at the origin: the conjugate of `f + w` splits. -/
theorem isExactSum_quadFn (hf : ClosedProperConvexFn f) : IsExactSum B f (quadFn B) := by
  have h := isExactSum_quadFn_sub (B := B) hf 0
  rwa [quadFn_zero_sub] at h

omit [FiniteDimensional ℝ E] [IsCompatiblePairing B] in
/-- The Moreau objective of a closed proper convex function is closed proper convex. -/
theorem closedProperConvexFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    ClosedProperConvexFn (moreauObj B f z) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.dom_nonempty
  refine ClosedProperConvexFn.add hf (closedProperConvexFn_quadFn_sub z) ⟨x₀, ?_⟩
  exact mem_dom.2 (EReal.add_lt_top (mem_dom.1 hx₀).ne (quadFn_ne_top _))

omit [FiniteDimensional ℝ E] [IsCompatiblePairing B] in
/-- **The Moreau objective has no direction of recession.** Its recession function splits as
`f0⁺ + (w (z - ·))0⁺`, where the second term is `+∞` off the origin. -/
theorem recessionConeFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    recessionConeFn (moreauObj B f z) = {0} := by
  have hg := closedProperConvexFn_moreauObj (B := B) hf z
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    rw [mem_recessionConeFn, moreauObj_def,
      congrFun (recessionFn_add hf (closedProperConvexFn_quadFn_sub z) hg.proper.dom_nonempty) y,
      Pi.add_apply, recessionFn_quadFn_sub z hy0,
      EReal.add_top_of_ne_bot (recessionFn_ne_bot hf.proper y)] at hy
    exact absurd hy (by simp)
  · rw [Set.singleton_subset_iff, mem_recessionConeFn]
    exact recessionFn_apply_zero_le _

omit [IsCompatiblePairing B] in
/-- **Attainment**: the infimum defining `(f □ w) z` is attained, because `f + w (z - ·)` is
closed proper convex with recession cone `{0}`. -/
theorem argmin_moreauObj_nonempty (hf : ClosedProperConvexFn f) (z : E) :
    (argmin (moreauObj B f z)).Nonempty :=
  argmin_nonempty_of_recessionConeFn_eq_zero (closedProperConvexFn_moreauObj hf z).convex
    (closedProperConvexFn_moreauObj hf z).closed (closedProperConvexFn_moreauObj hf z).proper
    (recessionConeFn_moreauObj hf z)

omit [FiniteDimensional ℝ E] in
/-- **The characterisation of the minimiser**: `x` minimises `f + w (z - ·)` exactly when
`z - x ∈ ∂f x`. Fermat's rule, the sum rule and `subdifferential_quadFn_sub`. -/
theorem mem_argmin_moreauObj_iff (hf : ClosedProperConvexFn f) (z x : E) :
    x ∈ argmin (moreauObj B f z) ↔ z - x ∈ subdifferential B f x := by
  rw [mem_argmin_iff_zero_mem_subdifferential B, moreauObj_def,
    (isExactSum_quadFn_sub hf z).subdifferential_add x, subdifferential_quadFn_sub]
  constructor
  · rintro ⟨y, hy, w, hw, hsum⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hyz : y = z - x := by
      rw [← sub_eq_zero, show y - (z - x) = y + (x - z) by abel]
      exact hsum
    rwa [hyz] at hy
  · intro h
    exact ⟨z - x, h, x - z, rfl, by abel_nf⟩

/-- There is exactly one `x` with `z = x + x*` and `x* ∈ ∂f x`. -/
theorem existsUnique_sub_mem_subdifferential (hf : ClosedProperConvexFn f) (z : E) :
    ∃! x : E, z - x ∈ subdifferential B f x := by
  obtain ⟨x, hx⟩ := argmin_moreauObj_nonempty (B := B) hf z
  have hx' := (mem_argmin_moreauObj_iff hf z x).1 hx
  exact ⟨x, hx', fun x' hx'' => eq_of_sub_mem_subdifferential hf.proper hx'' hx'⟩

omit [IsCompatiblePairing B] in
/-- `prox B f z` minimises the Moreau objective. -/
theorem prox_mem_argmin (hf : ClosedProperConvexFn f) (z : E) :
    prox B f z ∈ argmin (moreauObj B f z) :=
  Classical.epsilon_spec (argmin_moreauObj_nonempty hf z)

/-- The splitting `z = x + x*` with `x* ∈ ∂f x` exists, at `x = prox (z | f)`. -/
theorem sub_prox_mem_subdifferential (hf : ClosedProperConvexFn f) (z : E) :
    z - prox B f z ∈ subdifferential B f (prox B f z) :=
  (mem_argmin_moreauObj_iff hf z _).1 (prox_mem_argmin hf z)

/-- That splitting determines `prox`. -/
theorem prox_eq_of_sub_mem_subdifferential (hf : ClosedProperConvexFn f) {z x : E}
    (h : z - x ∈ subdifferential B f x) : prox B f z = x :=
  eq_of_sub_mem_subdifferential hf.proper (sub_prox_mem_subdifferential hf z) h

/-- Attainment and uniqueness in one statement: `prox (z | f) = x` exactly when `z - x ∈ ∂f x`. -/
theorem prox_eq_iff (hf : ClosedProperConvexFn f) (z x : E) :
    prox B f z = x ↔ z - x ∈ subdifferential B f x :=
  ⟨fun h => h ▸ sub_prox_mem_subdifferential hf z, prox_eq_of_sub_mem_subdifferential hf⟩

/-- The minimum set of the Moreau objective is `{prox (z | f)}`. -/
theorem argmin_moreauObj_eq_singleton (hf : ClosedProperConvexFn f) (z : E) :
    argmin (moreauObj B f z) = {prox B f z} := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · rw [Set.mem_singleton_iff]
    exact (prox_eq_of_sub_mem_subdifferential hf ((mem_argmin_moreauObj_iff hf z x).1 hx)).symm
  · rw [Set.singleton_subset_iff]
    exact prox_mem_argmin hf z

omit [IsCompatiblePairing B] in
/-- The envelope is the value of the objective at the proximal point. -/
theorem infConv_quadFn_eq_moreauObj_prox (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z = f (prox B f z) + quadFn B (z - prox B f z) := by
  rw [infConv_quadFn_apply hf.proper.ne_bot z]
  exact iInf_eq_of_mem_argmin (f := moreauObj B f z) (prox_mem_argmin hf z)

omit [FiniteDimensional ℝ E] in
/-- The conjugate of a closed proper convex function is closed proper convex. -/
theorem closedProperConvexFn_conj (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (conj B f) := by
  exact ⟨convexFn_conj _ _, closedFn_conj, proper_conj hf⟩

/-- **Moreau's decomposition of a point**: `z` splits as `prox (z | f) + prox (z | f*)`. Conjugate
inversion turns `∂f` into `∂f*`, so the second half of `z = x + x*` is `prox (z | f*)`. -/
theorem prox_add_prox_conj (hf : ClosedProperConvexFn f) (z : E) :
    prox B f z + prox B (conj B f) z = z := by
  have hx : z - prox B f z ∈ subdifferential B f (prox B f z) := sub_prox_mem_subdifferential hf z
  have hstar : z - (z - prox B f z) ∈
      subdifferential B (conj B f) (z - prox B f z) := by
    rw [sub_sub_cancel]
    have h := (mem_subdifferential_conj_iff_of_closedFn (B := B) hf.convex hf.closed).2 hx
    rwa [flip_eq_self] at h
  rw [prox_eq_of_sub_mem_subdifferential (closedProperConvexFn_conj hf) hstar]
  abel

/-! ### The graph of `∂f` is homeomorphic to the space -/

/-- **Proximation is nonexpansive** in the norm the pairing induces. Monotonicity of `∂f` gives
`B (x₁ - x₂) (x₁ - x₂) ≤ B (x₁ - x₂) (z₁ - z₂)`, and Cauchy–Schwarz finishes. -/
theorem pairingNorm_prox_sub_le (hf : ClosedProperConvexFn f) (z₁ z₂ : E) :
    pairingNorm B (prox B f z₁ - prox B f z₂) ≤ pairingNorm B (z₁ - z₂) := by
  have hmono := isMonotoneRel_subgradientRel (B := B) hf.proper
    (prox B f z₁, z₁ - prox B f z₁) (sub_prox_mem_subdifferential hf z₁)
    (prox B f z₂, z₂ - prox B f z₂) (sub_prox_mem_subdifferential hf z₂)
  rw [show z₁ - prox B f z₁ - (z₂ - prox B f z₂)
      = (z₁ - z₂) - (prox B f z₁ - prox B f z₂) by abel, map_sub] at hmono
  have hcs := pairing_le_pairingNorm_mul B (prox B f z₁ - prox B f z₂) (z₁ - z₂)
  have hsq := pairingNorm_sq B (prox B f z₁ - prox B f z₂)
  rcases eq_or_lt_of_le (pairingNorm_nonneg B (prox B f z₁ - prox B f z₂)) with h0 | h0
  · rw [← h0]
    exact pairingNorm_nonneg _ _
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith

/-- `prox` is Lipschitz, hence continuous. The constant is `1` only for the pairing norm; in the
ambient norm it is the ratio of the two equivalence constants between the norms. -/
theorem continuous_prox (hf : ClosedProperConvexFn f) : Continuous (prox B f) := by
  obtain ⟨c, C, hc, hC, hlow, hhigh⟩ := exists_pairingNorm_le_and_le_pairingNorm B
  have hK : (0 : ℝ) ≤ C / c := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := (C / c).toNNReal) fun z₁ z₂ => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK, div_mul_eq_mul_div, le_div_iff₀ hc]
  have h1 := hlow (prox B f z₁ - prox B f z₂)
  have h2 := pairingNorm_prox_sub_le (B := B) hf z₁ z₂
  have h3 := hhigh (z₁ - z₂)
  linarith

/-- `(x, x*) ↦ x + x*` is a homeomorphism of the graph of `∂f` onto `E`. It is bijective because
every `z` splits uniquely, continuous because addition is, and its inverse
`z ↦ (prox (z | f), z - prox (z | f))` is continuous because `prox` is nonexpansive. -/
noncomputable def subgradientRelHomeomorph (hf : ClosedProperConvexFn f) :
    ↥(subgradientRel B f) ≃ₜ E where
  toFun p := p.1.1 + p.1.2
  invFun z := ⟨(prox B f z, z - prox B f z), sub_prox_mem_subdifferential hf z⟩
  left_inv := by
    rintro ⟨⟨x, y⟩, hp⟩
    have hpx : prox B f (x + y) = x :=
      prox_eq_of_sub_mem_subdifferential hf (by rwa [show x + y - x = y by abel])
    refine Subtype.ext ?_
    simp only [hpx, Prod.mk.injEq, true_and]
    abel
  right_inv z := by
    simp only
    abel
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuous_prox hf).prodMk (continuous_id.sub (continuous_prox hf))) _

@[simp] theorem subgradientRelHomeomorph_apply (hf : ClosedProperConvexFn f)
    (p : ↥(subgradientRel B f)) : subgradientRelHomeomorph hf p = p.1.1 + p.1.2 := rfl

@[simp] theorem subgradientRelHomeomorph_symm_apply (hf : ClosedProperConvexFn f) (z : E) :
    (subgradientRelHomeomorph hf).symm z
      = ⟨(prox B f z, z - prox B f z), sub_prox_mem_subdifferential hf z⟩ := rfl

/-! ### `∂f` is maximal monotone -/

/-- The subdifferential of a closed proper convex function is *maximal monotone*. Given `(y, y*)`
monotonically related to the whole graph, the unique splitting of `y + y*` produces `(x, x*)` in
the graph with `x + x* = y + y*`; then `y - x = -(y* - x*)`, so the monotonicity inequality reads
`0 ≤ -|y - x|²`. -/
theorem isMaximalMonotoneRel_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalMonotoneRel B (subgradientRel B f) := by
  refine ⟨isMonotoneRel_subgradientRel hf.proper, fun σ hσ hsub q hq => ?_⟩
  have hmem : (prox B f (q.1 + q.2), q.1 + q.2 - prox B f (q.1 + q.2))
      ∈ subgradientRel B f := sub_prox_mem_subdifferential hf (q.1 + q.2)
  have hmono := hσ q hq _ (hsub hmem)
  rw [show q.2 - (q.1 + q.2 - prox B f (q.1 + q.2)) = -(q.1 - prox B f (q.1 + q.2)) by abel,
    map_neg] at hmono
  have hq1 : q.1 = prox B f (q.1 + q.2) := by
    rw [← sub_eq_zero]
    exact self_pairing_eq_zero_iff.1
      (le_antisymm (by linarith) (self_pairing_nonneg B (q.1 - prox B f (q.1 + q.2))))
  have hq2 : q.2 = q.1 + q.2 - prox B f (q.1 + q.2) := by rw [← hq1]; abel
  rw [show q = (prox B f (q.1 + q.2), q.1 + q.2 - prox B f (q.1 + q.2)) from Prod.ext hq1 hq2]
  exact hmem

end Attainment

/-! ### The inner-product case

For `innerₗ E` the pairing norm is the norm itself, so proximation is nonexpansive on the nose. -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- The distance between two proximal points is at most the distance between the two points. -/
theorem dist_prox_prox_le (hf : ClosedProperConvexFn f) (z₁ z₂ : E) :
    dist (prox (innerₗ E) f z₁) (prox (innerₗ E) f z₂) ≤ dist z₁ z₂ := by
  have h := pairingNorm_prox_sub_le (B := innerₗ E) hf z₁ z₂
  rwa [pairingNorm_innerL, pairingNorm_innerL, ← dist_eq_norm, ← dist_eq_norm] at h

/-- `prox` is nonexpansive in an inner-product space. -/
theorem lipschitzWith_prox (hf : ClosedProperConvexFn f) :
    LipschitzWith 1 (prox (innerₗ E) f) :=
  LipschitzWith.of_dist_le_mul fun z₁ z₂ => by
    simpa using dist_prox_prox_le hf z₁ z₂

end Inner

end ConvexAnalysis
