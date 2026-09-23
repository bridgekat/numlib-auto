import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Recession.Cone
import NumlibSurface.Rockafellar.Chapter03.Section13

/-!
# Rockafellar §15: polars of convex functions

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §15:
gauges and their polars, norms and Minkowski metrics, the gauge-like functions, and the polar `f°`
and obverse of a nonnegative convex function vanishing at the origin.

All 11 numbered results of §15 are formalized.

The unnumbered running text is recorded too: a gauge recovered from its own unit level set and the
uniqueness of the closed convex set with a given closed gauge; the polar-pair inequality
`⟨x, x*⟩ ≤ k(x) k°(x*)` with its Schwarz instance, the Euclidean norm being self-polar; the
correspondence between norms and Minkowski metrics; the level sets of the obverse; and the closing
display `{f° ≤ α⁻¹} = α⁻¹ {f* ≤ α}`.

## The section's definitions

* **A gauge** is a nonnegative positively homogeneous convex `k` with `k 0 = 0`, the backbone's
  `IsGauge`. `gauge_iff_exists_gaugeFn` is Rockafellar's other description — the gauges are exactly
  the `γ(· | C) = inf {μ ≥ 0 | x ∈ μ C}` for non-empty convex `C` — and `gaugeFn_apply_rn` is that
  infimum written out.
* **The polar `k°` of a gauge** is `polarGauge (pairing n) k`, with `polarGauge_apply_rn` the
  book's formula `inf {μ* ≥ 0 | ⟨x, x*⟩ ≤ μ* k(x) for all x}`.
* **A norm** is a gauge that is finite, symmetric and positive off the origin: `IsNorm`, whose
  four fields are the book's conditions (a)–(d). `IsNorm.toSeminorm` says a Rockafellar norm is a
  Mathlib `Seminorm`.
* **A Minkowski metric** is `IsMinkowskiMetric`, defined here: a metric invariant under translation
  and linear along segments.
* **Gauge-like** is the backbone's `IsGaugeLike`: `f 0 = inf f`, and the sublevel sets above that
  infimum are all positive multiples of a single set.
* **Positively homogeneous of degree `p`** is `PosHomogeneousDeg`.
* **The polar `f°`** of a nonnegative convex function vanishing at the origin is
  `polarFn (pairing n) f`, with `polarFn_apply_rn` giving the book's
  `inf {μ* ≥ 0 | ⟨x, x*⟩ ≤ 1 + μ* f(x) for all x}`.
* **The obverse** is `obverse f = inf {λ > 0 | (fλ)(x) ≤ 1}`, unfolded by `obverse_apply_rn`.

## Main results

* `theorem_15_1_isGauge`, `theorem_15_1_closedFn`, `theorem_15_1_polar_polar`,
  `theorem_15_1_gaugeFn` — the polar of a gauge is a closed gauge, `k°° = cl k`, and `k°` is the
  gauge of `C°` when `k` is the gauge of `C`.
* `corollary_15_1_1`, `corollary_15_1_1_gaugeEquiv`, `corollary_15_1_1_sets`, `corollary_15_1_2`,
  `corollary_15_1_2_symm` — polarity is a symmetric one-to-one correspondence on the closed gauges,
  matching the polarity of closed convex sets containing the origin, and gauge and support function
  of such a set are polar to each other.
* `theorem_15_2_isNorm`, `theorem_15_2_setOf_le_one`, `theorem_15_2_gaugeFn`,
  `theorem_15_2_setOf_gaugeFn_le_one`, `theorem_15_2_polar` — the norms are exactly the gauges of
  the symmetric closed bounded convex sets with the origin interior, and the polar of a norm is a
  norm.
* `theorem_15_3`, `theorem_15_3_conj`, `theorem_15_3_isGaugeLike_conj`, `corollary_15_3_1`,
  `corollary_15_3_1_conj`, `corollary_15_3_2`, `corollary_15_3_2_isGauge`,
  `corollary_15_3_2_inequality`, `corollary_15_3_2_polarSet` — the gauge-like closed proper convex
  functions, their conjugates through the monotone conjugate `g⁺`, and the Hölder pair
  `[(1/p) k^p]* = (1/q) (k°)^q`.
* `theorem_15_4_nonneg`, `theorem_15_4_map_zero`, `theorem_15_4_convexFn`, `theorem_15_4_closedFn`,
  `theorem_15_4_polar_polar`, `corollary_15_4_1` — `f°` is again nonnegative closed convex and
  vanishes at the origin, `f°° = cl f`, and `f ↦ f°` is a symmetric one-to-one correspondence.
* `theorem_15_5_isPolarFn`, `theorem_15_5_obverse_obverse`, `theorem_15_5_polarFn_eq_conj_obverse`,
  `theorem_15_5_conj_eq_polarFn_obverse`, `theorem_15_5_conj_eq_obverse_polarFn`,
  `theorem_15_5_polarFn_eq_obverse_conj`, `corollary_15_5_1` — the obverse, its involutivity, and
  the four identities relating it to `*` and `°`, whence `f*° = f°*`.
-/

open Set Pointwise Bornology

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The definitions of §15 -/

/-- **Rockafellar's gauge function** (§15, p. 128): `γ(x | C) = inf {μ ≥ 0 | x ∈ μ C}`. This is the
backbone's `gaugeFn C`, and the equation is the definition unfolded. -/
theorem gaugeFn_apply_rn (C : Set (Rn n)) (x : Rn n) :
    gaugeFn C x = ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal) :=
  gaugeFn_apply C x

/-- **Rockafellar §15, p. 128**: the gauges are exactly the functions `γ(· | C)` for a non-empty
convex set `C`. -/
theorem gauge_iff_exists_gaugeFn {k : Rn n → EReal} :
    IsGauge k ↔ ∃ C : Set (Rn n), C.Nonempty ∧ Convex ℝ C ∧ k = gaugeFn C :=
  isGauge_iff

/-- **Rockafellar §15, p. 128**: "one always has `γ(· | C) = k` for `C = {x | k(x) ≤ 1}`".
Closedness of `k` is not needed. -/
theorem gaugeFn_setOf_le_one {k : Rn n → EReal} (hk : IsGauge k) :
    gaugeFn {x : Rn n | k x ≤ 1} = k :=
  gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Rockafellar's polar of a gauge** (§15, p. 128):
`k°(x*) = inf {μ* ≥ 0 | ⟨x, x*⟩ ≤ μ* k(x), ∀ x}`. This is the backbone's `polarGauge (pairing n) k`,
and the equation is the definition unfolded. -/
theorem polarGauge_apply_rn (k : Rn n → EReal) (y : Rn n) :
    polarGauge (pairing n) k y
      = ⨅ m ∈ {m : ℝ | 0 ≤ m ∧ ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ (m : EReal) * k x},
          (m : EReal) :=
  polarGauge_apply (pairing n) k y

/-- **Rockafellar's polar of a nonnegative convex function vanishing at the origin** (§15, p. 136):
`f°(x*) = inf {μ* ≥ 0 | ⟨x, x*⟩ ≤ 1 + μ* f(x), ∀ x}`.

The backbone's `polarFn` quantifies over `epi f` rather than over `x`, because Rockafellar's
admissible set is not closed at `μ* = 0`; `polarFn_apply_eq` is the identification. -/
theorem polarFn_apply_rn {f : Rn n → EReal} (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) (y : Rn n) :
    polarFn (pairing n) f y
      = ⨅ m ∈ {m : ℝ | 0 ≤ m ∧ ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ 1 + (m : EReal) * f x},
          (m : EReal) :=
  polarFn_apply_eq hnn h0.le y

/-- **Rockafellar's obverse** (§15, p. 137): `g(x) = inf {λ > 0 | (fλ)(x) ≤ 1}`, where
`(fλ)(x) = λ f(λ⁻¹x)` is the right scalar multiple of §5. -/
theorem obverse_apply_rn (f : Rn n → EReal) (x : Rn n) :
    obverse f x = ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal) :=
  obverse_apply f x

/-! ### Theorem 15.1 -/

/-- **Theorem 15.1**, third assertion: if `k = γ(· | C)` for a non-empty convex set
`C`, then `k° = γ(· | C°)`. -/
theorem theorem_15_1_gaugeFn {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) :
    polarGauge (pairing n) (gaugeFn C) = gaugeFn (polarSet (pairing n) C) :=
  polarGauge_gaugeFn hC hne

/-- **Theorem 15.1**, first assertion: the polar of a gauge is a gauge. -/
theorem theorem_15_1_isGauge {k : Rn n → EReal} (hk : IsGauge k) :
    IsGauge (polarGauge (pairing n) k) :=
  isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Theorem 15.1**, first assertion: the polar of a gauge is *closed*. -/
theorem theorem_15_1_closedFn {k : Rn n → EReal} (hk : IsGauge k) :
    ClosedConvex (polarGauge (pairing n) k) :=
  closedConvex_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero

/-- **Theorem 15.1**, second assertion: `k°° = cl k`.

The backbone derives this from Theorem 15.4 rather than by Rockafellar's route through Theorem 14.5
and the unit level set. -/
theorem theorem_15_1_polar_polar {k : Rn n → EReal} (hk : IsGauge k) :
    polarGauge (pairing n) (polarGauge (pairing n) k) = convexCl k := by
  have h := polarGauge_polarGauge (B := pairing n) hk
  rwa [flip_pairing] at h

/-! ### Corollary 15.1.1 -/

/-- **Rockafellar §15, p. 128**, the correspondence `k(x) = γ(x | C)`, `C = {x | k(x) ≤ 1}` between
the closed convex sets containing the origin and the closed gauges; Corollary 15.1.1 quantifies
over this class. -/
noncomputable def corollary_15_1_1_gaugeEquiv (n : ℕ) :
    {C : Set (Rn n) // Convex ℝ C ∧ IsClosed C ∧ (0 : Rn n) ∈ C} ≃
      {k : Rn n → EReal // IsGauge k ∧ ClosedConvex k} :=
  gaugeEquiv (Rn n)

/-- **Corollary 15.1.1**, first assertion: `k ↦ k°` induces a one-to-one symmetric
correspondence in the class of all closed gauges on `ℝⁿ`. -/
noncomputable def corollary_15_1_1 (n : ℕ) :
    {k : Rn n → EReal // IsGauge k ∧ ClosedConvex k} ≃
      {j : Rn n → EReal // IsGauge j ∧ ClosedConvex j} :=
  polarGaugeEquiv (pairing n)

/-- **Corollary 15.1.1**, second assertion: two closed convex sets containing the
origin are polar to each other if and only if their gauge functions are polar to each other. -/
theorem corollary_15_1_1_sets {C D : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hD : Convex ℝ D) (hDcl : IsClosed D) (hD0 : (0 : Rn n) ∈ D) :
    polarSet (pairing n) C = D ↔ polarGauge (pairing n) (gaugeFn C) = gaugeFn D :=
  polarSet_eq_iff_polarGauge_gaugeFn_eq (pairing n) hC h0 hD hDcl hD0

/-! ### Corollary 15.1.2 -/

/-- **Corollary 15.1.2**: if `C` is a closed convex set containing the origin, the gauge function
of `C` and the support function of `C` are gauges polar to each other. Stated without the
closedness the book assumes. -/
theorem corollary_15_1_2 {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C) :
    polarGauge (pairing n) (gaugeFn C) = supportFn (pairing n) C :=
  polarGauge_gaugeFn_eq_supportFn hC h0

/-- **Corollary 15.1.2**, the other half of "polar to each other": the polar of the
support function of a closed convex set containing the origin is its gauge function.

This is `corollary_15_1_2` fed to `theorem_15_1_polar_polar`, closedness of `γ(· | C)` removing the
closure. -/
theorem corollary_15_1_2_symm {C : Set (Rn n)} (hC : Convex ℝ C) (h0 : (0 : Rn n) ∈ C)
    (hcl : IsClosed C) :
    polarGauge (pairing n) (supportFn (pairing n) C) = gaugeFn C := by
  rw [← corollary_15_1_2 hC h0, theorem_15_1_polar_polar (isGauge_gaugeFn hC ⟨0, h0⟩)]
  exact closedConvex_gaugeFn hC h0 hcl

/-! ### The polar-pair inequality -/

/-- **Rockafellar §15, p. 129**: gauges polar to each other satisfy `⟨x, x*⟩ ≤ k(x) k°(x*)` for
every `x ∈ dom k` and `x* ∈ dom k°`. The two values are named as reals because the right-hand side
is a product of reals. -/
theorem pairing_le_mul_rn {k : Rn n → EReal} (hk : IsGauge k) (hkc : ClosedConvex k) {x y : Rn n}
    {c d : ℝ} (hx : k x = (c : EReal)) (hy : polarGauge (pairing n) k y = (d : EReal)) :
    (inner ℝ x y : ℝ) ≤ c * d :=
  pairing_le_mul_of_gauge hk hkc hx hy

/-! ### Theorem 15.2 -/

section Norms

variable {k : Rn n → EReal}

/-- **Rockafellar §15, p. 131**, the opening of the proof of Theorem 15.2: "norms, being finite
convex functions, are continuous (Theorem 10.1)".

`ConvexFn.continuous_of_convexDom_eq_univ` is the backbone's Corollary 10.1.1. -/
theorem isNorm_continuous_rn (hk : IsNorm k) : Continuous k := by
  refine hk.toIsGauge.convexFn.continuous_of_convexDom_eq_univ
    ⟨⟨0, lt_of_le_of_ne le_top (hk.ne_top 0)⟩, hk.toIsGauge.ne_bot⟩ ?_
  exact Set.eq_univ_of_forall fun x => lt_of_le_of_ne le_top (hk.ne_top x)

/-- **Rockafellar §15, p. 131**: a norm on `ℝⁿ` is a closed function. The backbone declines to
prove this in general — closedness of a norm comes from Theorem 10.1, which is
finite-dimensional. -/
theorem isNorm_closedConvex_rn (hk : IsNorm k) : ClosedConvex k :=
  (closedConvex_iff_lowerSemicontinuous hk.toIsGauge.ne_bot).2
    (isNorm_continuous_rn hk).lowerSemicontinuous

/-- The unit level set of a norm on `ℝⁿ` contains the origin in its interior — Rockafellar's
`0 ∈ int C`, obtained from continuity rather than from Corollary 6.4.1. -/
theorem isNorm_zero_mem_interior_rn (hk : IsNorm k) :
    (0 : Rn n) ∈ interior {x : Rn n | k x ≤ 1} := by
  refine mem_interior.2 ⟨{x : Rn n | k x < 1}, fun x (hx : k x < 1) => le_of_lt hx, ?_, ?_⟩
  · exact (isNorm_continuous_rn hk).isOpen_preimage _ isOpen_Iio
  · change k 0 < 1
    rw [hk.toIsGauge.map_zero]
    exact zero_lt_one

/-- The unit level set of a norm on `ℝⁿ` is bounded — Rockafellar's "`C` is bounded", obtained from
Theorem 8.4 (`isBounded_iff_recessionCone_eq_zero`) and ray-freeness. -/
theorem isNorm_isBounded_setOf_le_one_rn (hk : IsNorm k) :
    IsBounded {x : Rn n | k x ≤ 1} := by
  obtain ⟨hconv, h0, -, -, hray⟩ := hk.level_one
  refine (isBounded_iff_recessionCone_eq_zero hconv
    (isClosed_setOf_le_one (isNorm_closedConvex_rn hk)) ⟨0, h0⟩).2
    (Set.Subset.antisymm (fun y hy => ?_) ?_)
  · by_contra hy0
    obtain ⟨l, hl, hlm⟩ := hray y (by simpa using hy0)
    exact hlm (by simpa using hy 0 h0 l hl.le)
  · rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact fun x hx a _ => by simpa using hx

/-- **Theorem 15.2**, first half: the gauge of a symmetric closed bounded convex set
`C` with `0 ∈ int C` is a norm.

The book's two set conditions are translated into the backbone's `AbsorbsAll` and `RayFree` here —
Corollary 6.4.1 and Theorem 8.4, each in the easy direction. -/
theorem theorem_15_2_isNorm {C : Set (Rn n)} (hC : Convex ℝ C) (hsymm : -C = C)
    (hint : (0 : Rn n) ∈ interior C) (hbdd : IsBounded C) : IsNorm (gaugeFn C) := by
  refine isNorm_gaugeFn hC (interior_subset hint) hsymm
    (absorbsAll_of_absorbent (absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hint)))
    fun x hx => ?_
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨(|R| + 1) / ‖x‖, by positivity, fun hmem => ?_⟩
  have h := mem_closedBall_zero_iff.1 (hR hmem)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hxn.ne'] at h
  have hRa : R ≤ |R| := le_abs_self R
  linarith

/-- **Theorem 15.2**, second half: the unit level set of a norm is a symmetric closed
bounded convex set containing the origin in its interior. -/
theorem theorem_15_2_setOf_le_one (hk : IsNorm k) :
    Convex ℝ {x : Rn n | k x ≤ 1} ∧ IsClosed {x : Rn n | k x ≤ 1} ∧
      IsBounded {x : Rn n | k x ≤ 1} ∧ -{x : Rn n | k x ≤ 1} = {x : Rn n | k x ≤ 1} ∧
      (0 : Rn n) ∈ interior {x : Rn n | k x ≤ 1} :=
  ⟨hk.toIsGauge.convex_level_one, isClosed_setOf_le_one (isNorm_closedConvex_rn hk),
    isNorm_isBounded_setOf_le_one_rn hk, hk.level_one.2.2.1, isNorm_zero_mem_interior_rn hk⟩

/-- **Theorem 15.2**: the correspondence, in the direction `k ↦ C ↦ γ(· | C)`. -/
theorem theorem_15_2_gaugeFn (hk : IsNorm k) : gaugeFn {x : Rn n | k x ≤ 1} = k :=
  gaugeFn_setOf_le_one hk.toIsGauge

/-- **Theorem 15.2**: the correspondence, in the direction `C ↦ γ(· | C) ↦ C`. This is
also the uniqueness clause of §15, p. 128: a closed gauge determines the closed convex set
containing the origin. -/
theorem theorem_15_2_setOf_gaugeFn_le_one {C : Set (Rn n)} (hC : Convex ℝ C)
    (h0 : (0 : Rn n) ∈ C) (hcl : IsClosed C) : {x : Rn n | gaugeFn C x ≤ 1} = C :=
  setOf_gaugeFn_le_one hC h0 hcl

/-- **Theorem 15.2**, last assertion: the polar of a norm is a norm. The two side conditions are the
pairing readings of "`C` is bounded" and "`0 ∈ int C`". -/
theorem theorem_15_2_polar (hk : IsNorm k) : IsNorm (polarGauge (pairing n) k) := by
  obtain ⟨hconv, h0, hsymm, -, -⟩ := hk.level_one
  have hmain := isNorm_polarGauge_gaugeFn (B := pairing n) hconv h0 hsymm ?_ ?_
  · rwa [theorem_15_2_gaugeFn hk] at hmain
  · intro y
    obtain ⟨R, hR⟩ := (isNorm_isBounded_setOf_le_one_rn hk).subset_closedBall 0
    refine ⟨|R| * ‖y‖, fun x hx => ?_⟩
    have hx' : ‖x‖ ≤ |R| := le_trans (mem_closedBall_zero_iff.1 (hR hx)) (le_abs_self R)
    calc pairing n x y = (inner ℝ x y : ℝ) := rfl
      _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ |R| * ‖y‖ := mul_le_mul_of_nonneg_right hx' (norm_nonneg y)
  · intro y hy
    obtain ⟨e, he, hsub⟩ :=
      Metric.isOpen_iff.1 isOpen_interior 0 (isNorm_zero_mem_interior_rn hk)
    have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have ht0 : 0 < e / (2 * ‖y‖) := by positivity
    refine ⟨(e / (2 * ‖y‖)) • y, interior_subset (hsub ?_), ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have hval : e / (2 * ‖y‖) * ‖y‖ = e / 2 := by field_simp
      rw [hval]
      linarith
    · have hval : pairing n ((e / (2 * ‖y‖)) • y) y = e / (2 * ‖y‖) * (‖y‖ * ‖y‖) := by
        rw [pairing_apply, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      rw [hval]
      exact ne_of_gt (mul_pos ht0 (mul_pos hyn hyn))

end Norms

/-! ### The Euclidean norm, and the Schwarz inequality -/

/-- **The Euclidean norm is a norm in Rockafellar's sense** (§15, p. 130). -/
theorem isNorm_euclideanNorm (n : ℕ) : IsNorm (fun x : Rn n => ((‖x‖ : ℝ) : EReal)) := by
  have hph : PosHomogeneous fun x : Rn n => ((‖x‖ : ℝ) : EReal) := by
    intro a ha x
    change ((‖a • x‖ : ℝ) : EReal) = ((a : ℝ) : EReal) * ((‖x‖ : ℝ) : EReal)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, ← EReal.coe_mul]
  have hbot : ∀ x : Rn n, ((‖x‖ : ℝ) : EReal) ≠ ⊥ := fun x => EReal.coe_ne_bot _
  have hconv : ConvexFn fun x : Rn n => ((‖x‖ : ℝ) : EReal) := by
    refine (PosHomogeneous.convexFn_iff_subadditive hph hbot).2 fun x y => ?_
    rw [← EReal.coe_add]
    exact_mod_cast norm_add_le x y
  exact ⟨⟨fun x => by exact_mod_cast norm_nonneg x, hph, hconv, by simp⟩,
    fun _ => EReal.coe_ne_top _, fun x => by rw [norm_neg],
    fun x hx => by exact_mod_cast norm_pos_iff.2 hx⟩

/-- **Rockafellar §15, p. 130**: the Euclidean norm is its own polar, being both the gauge function
and the support function of the Euclidean unit ball. -/
theorem polarGauge_euclideanNorm (n : ℕ) :
    polarGauge (pairing n) (fun x : Rn n => ((‖x‖ : ℝ) : EReal))
      = fun y : Rn n => ((‖y‖ : ℝ) : EReal) := by
  have hk := isNorm_euclideanNorm n
  have hset : {x : Rn n | ((‖x‖ : ℝ) : EReal) ≤ 1} = Metric.closedBall (0 : Rn n) 1 := by
    ext x
    rw [mem_closedBall_zero_iff]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  rw [polarGauge_eq_supportFn hk.toIsGauge.nonneg hk.toIsGauge.posHomogeneous
    hk.toIsGauge.map_zero, hset]
  funext y
  exact supportFn_unitBall y

/-- **Rockafellar §15, p. 130**, the Schwarz inequality read as the polar-pair inequality for the
Euclidean norm: `⟨x, y⟩ ≤ |x| · |y|`. -/
theorem schwarz_rn (x y : Rn n) : (inner ℝ x y : ℝ) ≤ ‖x‖ * ‖y‖ := by
  have hk := isNorm_euclideanNorm n
  refine pairing_le_mul_rn hk.toIsGauge (isNorm_closedConvex_rn hk) rfl ?_
  rw [polarGauge_euclideanNorm n]

/-! ### Minkowski metrics -/

/-- **A Minkowski metric on `ℝⁿ`** (Rockafellar §15, p. 132): a metric `ρ` — conditions (a), (b),
(c) — that is in addition invariant under translation (d) and linear along line segments (e). -/
structure IsMinkowskiMetric (rho : Rn n → Rn n → ℝ) : Prop where
  /-- (a) `ρ(x, y) > 0` when `x ≠ y`. -/
  pos : ∀ x y, x ≠ y → 0 < rho x y
  /-- (a) `ρ(x, x) = 0`. -/
  self : ∀ x, rho x x = 0
  /-- (b) `ρ` is symmetric. -/
  comm : ∀ x y, rho x y = rho y x
  /-- (c) the triangle inequality. -/
  triangle : ∀ x y z, rho x z ≤ rho x y + rho y z
  /-- (d) distances are invariant under translation. -/
  vadd : ∀ x y z, rho (x + z) (y + z) = rho x y
  /-- (e) distances behave linearly along line segments. -/
  segment : ∀ x y, ∀ l ∈ Set.Icc (0 : ℝ) 1, rho x ((1 - l) • x + l • y) = l * rho x y

/-- **Rockafellar §15, p. 132**: a norm `k` defines a Minkowski metric `ρ(x, y) = k(x - y)`.

Rockafellar leaves the verification to the reader. Written through `IsNorm.toSeminorm`, whose
subadditivity is Theorem 4.7 and whose absolute homogeneity is `IsNorm.apply_smul`. -/
theorem isMinkowskiMetric_of_isNorm {k : Rn n → EReal} (hk : IsNorm k) :
    IsMinkowskiMetric fun x y : Rn n => hk.toSeminorm (x - y) where
  pos x y hxy := by
    have h : (0 : EReal) < k (x - y) := hk.pos _ (sub_ne_zero_of_ne hxy)
    rw [← hk.coe_toSeminorm (x - y)] at h
    exact_mod_cast h
  self x := by simp
  comm x y := by rw [← map_neg_eq_map hk.toSeminorm (x - y), neg_sub]
  triangle x y z := by
    have h : x - z = (x - y) + (y - z) := by abel
    rw [h]
    exact map_add_le_add hk.toSeminorm _ _
  vadd x y z := by rw [add_sub_add_right_eq_sub]
  segment x y l hl := by
    have h : x - ((1 - l) • x + l • y) = l • (x - y) := by module
    rw [h, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hl.1]

/-- **Rockafellar §15, p. 132**: a Minkowski metric is determined by the norm `x ↦ ρ(x, 0)`, since
translation invariance gives `ρ(x, y) = ρ(x - y, 0)`. This is the uniqueness half of the
correspondence. -/
theorem minkowskiMetric_eq_sub {rho : Rn n → Rn n → ℝ} (h : IsMinkowskiMetric rho) (x y : Rn n) :
    rho x y = rho (x - y) 0 := by
  have hv := h.vadd (x - y) 0 y
  rwa [sub_add_cancel, zero_add] at hv

/-! ### Theorem 15.3 -/

/-- **Theorem 15.3**, first assertion: a function is a gauge-like closed proper convex
function if and only if it is `g ∘ k` for a closed gauge `k` and a non-constant nondecreasing lower
semicontinuous convex function `g` on `[0, +∞]` which is finite at some `ζ > 0`. -/
theorem theorem_15_3 {f : Rn n → EReal} :
    (ClosedProperConvexFn f ∧ IsGaugeLike f) ↔
      ∃ (g : ℝ → EReal) (k : Rn n → EReal),
        (MonotoneHalfLineFn g ∧ (∃ t : ℝ, 0 < t ∧ g 0 < g t) ∧ (∃ z : ℝ, 0 < z ∧ g z ≠ ⊤)) ∧
        (IsGauge k ∧ ClosedConvex k) ∧ f = monotoneComp g k :=
  closedProperConvexFn_and_isGaugeLike_iff (pairing n)

/-- **Theorem 15.3**, second assertion: `f* (x*) = g⁺(k°(x*))`, where `g⁺` is the monotone
conjugate of `g`. -/
theorem theorem_15_3_conj {g : ℝ → EReal} {k : Rn n → EReal} (hk : IsGauge k) (hkc : ClosedConvex k)
    (hg : MonotoneHalfLineFn g) (hfin : ∃ z : ℝ, 0 < z ∧ g z ≠ ⊤) :
    convexConj (pairing n) (monotoneComp g k)
      = monotoneComp (monotoneConj g) (polarGauge (pairing n) k) :=
  convexConj_monotoneComp hk hkc hg hfin

/-- **Theorem 15.3**, second assertion: "if `f` is of this type, then `f*` is
gauge-like too". -/
theorem theorem_15_3_isGaugeLike_conj {g : ℝ → EReal} {k : Rn n → EReal} (hk : IsGauge k)
    (hkc : ClosedConvex k) (hg : MonotoneHalfLineFn g) (hfin : ∃ z : ℝ, 0 < z ∧ g z ≠ ⊤)
    (hne : ∃ t : ℝ, 0 < t ∧ g 0 < g t) :
    IsGaugeLike (convexConj (pairing n) (monotoneComp g k)) :=
  isGaugeLike_convexConj_monotoneComp (pairing n) hk hkc hg hfin hne

/-! ### Corollary 15.3.1 -/

/-- **Corollary 15.3.1**, first assertion: a closed proper convex function `f` is positively
homogeneous of degree `p`, `1 < p < ∞`, if and only if `f = (1/p) k^p` for a closed gauge `k`. The
book's `(1/p) k^p` is `monotoneComp (powHalfLine p) k`. -/
theorem corollary_15_3_1 {p : ℝ} {f : Rn n → EReal} (hp : 1 < p) (hf : ClosedProperConvexFn f) :
    PosHomogeneousDeg p f ↔
      ∃ k : Rn n → EReal, IsGauge k ∧ ClosedConvex k ∧ f = monotoneComp (powHalfLine p) k :=
  posHomogeneousDeg_iff_exists_isGauge hp hf.convex hf.closed hf.proper

/-- **Corollary 15.3.1**, second assertion: `[(1/p) k^p]* = (1/q) (k°)^q`, where
`(1/p) + (1/q) = 1`. -/
theorem corollary_15_3_1_conj {p q : ℝ} {k : Rn n → EReal} (hpq : p.HolderConjugate q)
    (hk : IsGauge k) (hkc : ClosedConvex k) :
    convexConj (pairing n) (monotoneComp (powHalfLine p) k)
      = monotoneComp (powHalfLine q) (polarGauge (pairing n) k) :=
  convexConj_monotoneComp_powHalfLine hpq hk hkc

/-! ### Corollary 15.3.2 -/

section Cor1532

variable {p q : ℝ} {f : Rn n → EReal}

/-- **Corollary 15.3.2**, first assertion: `(pf)^{1/p}` is a closed gauge. -/
theorem corollary_15_3_2_isGauge (hp : 1 < p) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) : IsGauge (degGauge p f) ∧ ClosedConvex (degGauge p f) := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have h0 : f 0 = 0 :=
    PosHomogeneousDeg.map_zero_eq_zero hp0 hf.closed hf.proper hph
  have hnn : ∀ z, 0 ≤ f z :=
    PosHomogeneousDeg.nonneg hp hf.convex hf.proper.ne_bot hph h0
  exact ⟨isGauge_degGauge hp0 hf.convex hnn hph h0,
    closedConvex_degGauge hp0 hf.convex hf.closed hnn hph h0⟩

/-- **Corollary 15.3.2**: the polar of the closed gauge `(pf)^{1/p}` is `(qf*)^{1/q}`. -/
theorem corollary_15_3_2 (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) :
    polarGauge (pairing n) (degGauge p f) = degGauge q (convexConj (pairing n) f) :=
  polarGauge_degGauge hpq hf.convex hf.closed hf.proper hph

/-- **Corollary 15.3.2**, the Hölder-type inequality
`⟨x, x*⟩ ≤ [p f(x)]^{1/p} [q f*(x*)]^{1/q}` on `dom f × dom f*`. -/
theorem corollary_15_3_2_inequality (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) {x y : Rn n} {a b : ℝ} (hx : f x = (a : EReal))
    (hy : convexConj (pairing n) f y = (b : EReal)) :
    (inner ℝ x y : ℝ) ≤ (p * a) ^ p⁻¹ * (q * b) ^ q⁻¹ :=
  pairing_le_rpow_mul_rpow hpq hf.convex hf.closed hf.proper hph hx hy

/-- **Corollary 15.3.2**, last assertion: the closed convex sets `{f ≤ 1/p}` and
`{f* ≤ 1/q}` are polar to each other. -/
theorem corollary_15_3_2_polarSet (hpq : p.HolderConjugate q) (hf : ClosedProperConvexFn f)
    (hph : PosHomogeneousDeg p f) :
    polarSet (pairing n) {x : Rn n | f x ≤ ((p⁻¹ : ℝ) : EReal)}
      = {y : Rn n | convexConj (pairing n) f y ≤ ((q⁻¹ : ℝ) : EReal)} :=
  polarSet_setOf_le_inv hpq hf.convex hf.closed hf.proper hph

end Cor1532

/-! ### Theorem 15.4 -/

section Thm154

variable {f : Rn n → EReal}

/-- **Theorem 15.4**: the polar `f°` of a nonnegative convex function vanishing at the
origin is nonnegative. -/
theorem theorem_15_4_nonneg (h0 : f 0 = 0) (y : Rn n) : 0 ≤ polarFn (pairing n) f y :=
  polarFn_nonneg h0.le y

/-- **Theorem 15.4**: `f°` vanishes at the origin. -/
theorem theorem_15_4_map_zero (h0 : f 0 = 0) : polarFn (pairing n) f 0 = 0 :=
  polarFn_zero (pairing n) f h0.le

/-- **Theorem 15.4**: `f°` is convex. -/
theorem theorem_15_4_convexFn (hnn : ∀ x, 0 ≤ f x) : ConvexFn (polarFn (pairing n) f) :=
  convexFn_polarFn hnn

/-- **Theorem 15.4**: `f°` is closed. -/
theorem theorem_15_4_closedFn (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) :
    ClosedConvex (polarFn (pairing n) f) :=
  closedConvex_polarFn hnn h0.le

/-- **Theorem 15.4**, second assertion: `f°° = cl f`.

Note that `f` is *not* assumed closed: this is the statement that makes `f ↦ f°` an involution on
the closed members of the class. -/
theorem theorem_15_4_polar_polar (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 = 0) :
    polarFn (pairing n) (polarFn (pairing n) f) = convexCl f := by
  have h := polarFn_polarFn (B := pairing n) hconv hnn h0.le
  rwa [flip_pairing] at h

end Thm154

/-- **Corollary 15.4.1**: `f ↦ f°` induces a symmetric one-to-one correspondence in
the class of all nonnegative closed convex functions vanishing at the origin.

`IsPolarFn` is that class. -/
noncomputable def corollary_15_4_1 (n : ℕ) :
    {f : Rn n → EReal // IsPolarFn f} ≃ {g : Rn n → EReal // IsPolarFn g} :=
  polarFnEquiv (pairing n)

/-! ### Theorem 15.5 -/

section Thm155

variable {f : Rn n → EReal}

/-- **Theorem 15.5**, first assertion: the obverse `g` of a nonnegative closed convex
function `f` vanishing at the origin has those same three properties. -/
theorem theorem_15_5_isPolarFn (h : IsPolarFn f) : IsPolarFn (obverse f) :=
  isPolarFn_obverse h

/-- **Theorem 15.5**, first assertion: `f` is the obverse of its obverse. -/
theorem theorem_15_5_obverse_obverse (h : IsPolarFn f) : obverse (obverse f) = f :=
  obverse_obverse h

/-- **Theorem 15.5**: `f° = g*`, where `g` is the obverse of `f`. -/
theorem theorem_15_5_polarFn_eq_conj_obverse (h : IsPolarFn f) :
    convexConj (pairing n) (obverse f) = polarFn (pairing n) f :=
  convexConj_obverse h

/-- **Theorem 15.5**: `f* = g°`, where `g` is the obverse of `f`. -/
theorem theorem_15_5_conj_eq_polarFn_obverse (h : IsPolarFn f) :
    polarFn (pairing n) (obverse f) = convexConj (pairing n) f :=
  polarFn_obverse h

/-- **Theorem 15.5**, last assertion: `f*` is the obverse of `f°`. -/
theorem theorem_15_5_conj_eq_obverse_polarFn (h : IsPolarFn f) :
    convexConj (pairing n) f = obverse (polarFn (pairing n) f) :=
  convexConj_eq_obverse_polarFn h

/-- **Theorem 15.5**, last assertion: `f°` is the obverse of `f*`. -/
theorem theorem_15_5_polarFn_eq_obverse_conj (h : IsPolarFn f) :
    polarFn (pairing n) f = obverse (convexConj (pairing n) f) :=
  polarFn_eq_obverse_convexConj h

/-- **Corollary 15.5.1**: `f*° = f°*` for a nonnegative closed convex function `f`
vanishing at the origin. -/
theorem corollary_15_5_1 (h : IsPolarFn f) :
    polarFn (pairing n) (convexConj (pairing n) f)
        = convexConj (pairing n) (polarFn (pairing n) f) := by
  have hp := polarFn_convexConj_eq_convexConj_polarFn (B := pairing n) h
  rwa [flip_pairing] at hp

/-! ### The level sets at the end of §15 -/

/-- **Rockafellar §15, p. 139**: `{g ≤ α} = α {f ≤ α⁻¹}` for `α > 0`, where `g` is the obverse
of `f`. -/
theorem setOf_obverse_le_rn (h : IsPolarFn f) {alpha : ℝ} (ha : 0 < alpha) :
    {x : Rn n | obverse f x ≤ (alpha : EReal)}
      = alpha • {x : Rn n | f x ≤ ((alpha⁻¹ : ℝ) : EReal)} :=
  setOf_obverse_le h ha

/-- **Rockafellar §15**, the last display of the section: `{f° ≤ α⁻¹} = α⁻¹ {f* ≤ α}` for `α > 0`.
This set is the middle set of the inclusions of Theorem 14.7. -/
theorem setOf_polarFn_le_rn (h : IsPolarFn f) {alpha : ℝ} (ha : 0 < alpha) :
    {y : Rn n | polarFn (pairing n) f y ≤ ((alpha⁻¹ : ℝ) : EReal)}
      = alpha⁻¹ • {y : Rn n | convexConj (pairing n) f y ≤ (alpha : EReal)} :=
  setOf_polarFn_le h ha

end Thm155

end Rockafellar
