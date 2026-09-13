import Numlib.Analysis.Convex.Polyhedral.Function

/-!
# The normal form of a polyhedral convex function

A polyhedral convex function is exactly a pointwise maximum of finitely many affine functions,
restricted to a polyhedral convex set: `f = h + δ(· | C)` with

`h x = max {⟨x, b₁⟩ - β₁, …, ⟨x, b_k⟩ - β_k}` and `C = {x | ⟨x, b_j⟩ ≤ β_j, j = k+1, …, m}`.

The two descriptions are the two kinds of closed half-space that can appear in a polyhedral
description of `epi f ⊆ E × ℝ`: those whose bounding hyperplane is *non-vertical*, which are the
epigraphs of affine functions, and those that are *vertical*, which constrain only `x`. There is
no third kind, because `epi f` is upward closed and so no constraint can bound the vertical
variable above; reading a polyhedral system for `epi f` off in the two groups is the whole proof.

## Main definitions

* `maxAffineFn s` — the pointwise maximum `x ↦ ⨆ q ∈ s, (q.1 x - q.2)` of a finite family of
  affine functions, valued in `EReal`. The empty family gives the constant `⊥`.

## Main results

* `polyhedralFn_maxAffineFn`, `polyhedralFn_maxAffineFn_add_indicatorFn` — a normal form is always
  polyhedral, with no hypothesis: the degenerate `s = ∅` gives `⊥`, whose epigraph is everything.
* `PolyhedralFn.exists_maxAffineFn_add_indicatorFn_dom` — every polyhedral convex function that
  nowhere takes `⊥` is in normal form, with `dom f` itself as the set. The vertical inequalities
  cut out a polyhedral set that may be strictly larger than `dom f`, but off `dom f` the function
  is `⊤` anyway.
* `polyhedralFn_iff_maxAffineFn_add_indicatorFn` — the two together, as an iff.

## Implementation notes

The `⊥`-freeness hypothesis is not decoration: `EReal` has `⊥ + ⊤ = ⊥`, so a normal form can take
the value `⊥` only on `C`. The function that is `⊥` on a proper nonempty polyhedral `C` and `⊤`
elsewhere is convex with polyhedral epigraph `C ×ˢ univ` and has no normal form. The classical
convention makes polyhedral convex functions proper, so `∀ x, f x ≠ ⊥` is the weaker hypothesis.
The forward direction needs no finite-dimensionality; only the converse uses Minkowski–Weyl,
through `PolyhedralFn.add`.

## References

* [rockafellar1970convex] §19.
-/

open Set

namespace ConvexAnalysis

section MaxAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The pointwise maximum of the finite family of affine functions `x ↦ q.1 x - q.2`, `q ∈ s`,
valued in `EReal`. The empty family gives the constant `⊥`, which is the value the extended
arithmetic assigns to an empty supremum. -/
noncomputable def maxAffineFn (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) : E → EReal :=
  fun x => ⨆ q ∈ s, ((q.1 x - q.2 : ℝ) : EReal)

variable {s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)} {x : E} {c : ℝ}

/-- A real number bounds a finite maximum of affine functions exactly when it bounds each of
them. -/
theorem maxAffineFn_le_coe : maxAffineFn s x ≤ (c : EReal) ↔ ∀ q ∈ s, q.1 x - q.2 ≤ c := by
  rw [maxAffineFn, iSup₂_le_iff]
  exact forall₂_congr fun _ _ => EReal.coe_le_coe_iff

/-- Every value of a finite maximum of affine functions is a lower bound for that family. -/
theorem coe_le_maxAffineFn {q : (E →ₗ[ℝ] ℝ) × ℝ} (hq : q ∈ s) :
    ((q.1 x - q.2 : ℝ) : EReal) ≤ maxAffineFn s x :=
  le_iSup₂ (f := fun q (_ : q ∈ s) => ((q.1 x - q.2 : ℝ) : EReal)) q hq

/-- A non-empty family of affine functions has a maximum that is nowhere `⊥`. -/
theorem maxAffineFn_ne_bot (hs : s.Nonempty) (x : E) : maxAffineFn s x ≠ ⊥ := by
  obtain ⟨q, hq⟩ := hs
  intro h
  have hle : ((q.1 x - q.2 : ℝ) : EReal) ≤ ⊥ := h ▸ coe_le_maxAffineFn hq
  exact absurd (le_bot_iff.1 hle) (EReal.coe_ne_bot _)

/-- An empty family of affine functions has the constant `⊥` as its maximum. -/
@[simp] theorem maxAffineFn_empty : maxAffineFn (∅ : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) = fun _ : E => ⊥ :=
  funext fun _ => by simp [maxAffineFn]

end MaxAffine

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- A finite maximum of affine functions is a polyhedral convex function: its epigraph is cut out
by the system `q.1 x - μ ≤ q.2`. -/
theorem polyhedralFn_maxAffineFn (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) :
    PolyhedralFn (maxAffineFn s) := by
  classical
  refine ⟨s.image fun q => (q.1 ∘ₗ LinearMap.fst ℝ E ℝ - LinearMap.snd ℝ E ℝ, q.2), ?_⟩
  ext p
  simp only [mem_epi, Set.mem_ofPred_eq, Finset.mem_image, maxAffineFn_le_coe]
  constructor
  · rintro h ψ ⟨q, hq, rfl⟩
    have hq' := h q hq
    change q.1 p.1 - p.2 ≤ q.2
    linarith
  · intro h q hq
    have hq' : q.1 p.1 - p.2 ≤ q.2 := h _ ⟨q, hq, rfl⟩
    linarith

omit [FiniteDimensional ℝ E] in
/-- The constant `⊥` is a polyhedral convex function: its epigraph is everything. -/
theorem polyhedralFn_bot : PolyhedralFn (fun _ : E => (⊥ : EReal)) := by
  have h : epi (fun _ : E => (⊥ : EReal)) = (Set.univ : Set (E × ℝ)) := by
    ext p; simp
  rw [PolyhedralFn, h]
  exact polyhedral_univ

/-- **The normal form is always polyhedral.** For any finite family of affine functions and any
polyhedral convex set `C`, the function `h + δ(· | C)` is a polyhedral convex function.

For a non-empty family this is `PolyhedralFn.add` applied to `polyhedralFn_maxAffineFn` and
`polyhedralFn_indicatorFn`; for the empty family `h + δ(· | C)` is the constant `⊥`, because
`⊥ + ⊤ = ⊥`. -/
theorem polyhedralFn_maxAffineFn_add_indicatorFn (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) {C : Set E}
    (hC : Polyhedral C) : PolyhedralFn (maxAffineFn s + indicatorFn C) := by
  rcases Finset.eq_empty_or_nonempty s with rfl | hs
  · have h : maxAffineFn (∅ : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) + indicatorFn C
        = fun _ : E => (⊥ : EReal) := by
      funext x
      change maxAffineFn ∅ x + indicatorFn C x = ⊥
      rw [maxAffineFn_empty]
      exact EReal.bot_add _
    rw [h]
    exact polyhedralFn_bot
  · exact PolyhedralFn.add (polyhedralFn_maxAffineFn s) (polyhedralFn_indicatorFn hC)
      (maxAffineFn_ne_bot hs) (indicatorFn_ne_bot C)

/-- A negative coefficient on the vertical variable turns an inequality `A + μ c ≤ b` into the
epigraph inequality of the affine function with slope `(-c)⁻¹ A` and constant `(-c)⁻¹ b`. -/
private theorem affine_le_iff_of_neg {A b c μ : ℝ} (hc : c < 0) :
    A + μ * c ≤ b ↔ (-c)⁻¹ * A - (-c)⁻¹ * b ≤ μ := by
  have hc' : (0 : ℝ) < -c := by linarith
  have hcne : c ≠ 0 := ne_of_lt hc
  have hne : (-c) ≠ 0 := ne_of_gt hc'
  constructor
  · intro h
    have h1 : (-c)⁻¹ * (A - b) ≤ (-c)⁻¹ * (μ * (-c)) := by
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hc').le
      have hmul : μ * (-c) = -(μ * c) := by ring
      rw [hmul]
      linarith
    have h2 : (-c)⁻¹ * (μ * (-c)) = μ := by field_simp
    rw [h2, mul_sub] at h1
    exact h1
  · intro h
    have h1 : (-c) * ((-c)⁻¹ * A - (-c)⁻¹ * b) ≤ (-c) * μ :=
      mul_le_mul_of_nonneg_left h hc'.le
    have h2 : (-c) * ((-c)⁻¹ * A - (-c)⁻¹ * b) = A - b := by
      field_simp
      ring
    have h3 : (-c) * μ = -(μ * c) := by ring
    rw [h2, h3] at h1
    linarith

omit [FiniteDimensional ℝ E] in
/-- **The normal form of a polyhedral convex function.** A polyhedral convex function that nowhere
takes the value `⊥` is a pointwise maximum of finitely many affine functions plus the indicator of
a polyhedral convex set, and the set may be taken to be `dom f`.

The affine pieces come from the *non-vertical* inequalities of a polyhedral system for `epi f`,
each rescaled by minus its (negative) coefficient on the vertical variable. The *vertical*
inequalities constrain `x` alone and hold throughout `dom f`, which is why `dom f` itself serves as
the set; it is polyhedral by `PolyhedralFn.polyhedral_dom`. No inequality can have a *positive*
vertical coefficient, since `epi f` is upward closed. -/
theorem PolyhedralFn.exists_maxAffineFn_add_indicatorFn_dom (hf : PolyhedralFn f)
    (hb : ∀ x, f x ≠ ⊥) :
    ∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ), f = maxAffineFn s + indicatorFn (dom f) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset (((E × ℝ) →ₗ[ℝ] ℝ) × ℝ),
      epi f = {p : E × ℝ | ∀ q ∈ t, q.1 p ≤ q.2} := hf
  have hsplit : ∀ (Ψ : (E × ℝ) →ₗ[ℝ] ℝ) (x : E) (μ : ℝ),
      Ψ ((x, μ) : E × ℝ) = Ψ (LinearMap.inl ℝ E ℝ x) + μ * Ψ ((0 : E), (1 : ℝ)) := by
    intro Ψ x μ
    have hp : ((x, μ) : E × ℝ) = LinearMap.inl ℝ E ℝ x + μ • ((0 : E), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hp, map_add, map_smul, smul_eq_mul]
  rcases Set.eq_empty_or_nonempty (epi f) with hemp | hne
  · -- `epi f = ∅`, so `f ≡ ⊤` and `dom f = ∅`.
    have htop : ∀ x, f x = ⊤ := by
      intro x
      refine top_le_iff.1 (not_lt.1 fun hlt => ?_)
      obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hb x) hlt
      have hmem : ((x, r) : E × ℝ) ∈ epi f := le_of_eq hr
      rw [hemp] at hmem
      exact hmem
    have hdom : dom f = (∅ : Set E) := by
      ext x
      simp [htop x]
    refine ⟨{(0, 0)}, funext fun x => ?_⟩
    have hmax : maxAffineFn ({((0 : E →ₗ[ℝ] ℝ), (0 : ℝ))} : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) x = 0 := by
      simp [maxAffineFn]
    change f x = maxAffineFn _ x + indicatorFn (dom f) x
    rw [htop x, hmax, hdom, indicatorFn_of_notMem (Set.notMem_empty x), zero_add]
  obtain ⟨⟨x₀, r₀⟩, hp₀⟩ := hne
  have hp₀' : f x₀ ≤ ((r₀ : ℝ) : EReal) := hp₀
  have ht₀ : ∀ q ∈ t, q.1 ((x₀, r₀) : E × ℝ) ≤ q.2 := by
    have h := hp₀
    rw [ht] at h
    exact h
  -- No inequality can have a positive coefficient on the vertical variable.
  have hnp : ∀ q ∈ t, q.1 ((0 : E), (1 : ℝ)) ≤ 0 := by
    intro q hq
    by_contra hpos
    rw [not_le] at hpos
    have hcne : q.1 ((0 : E), (1 : ℝ)) ≠ 0 := ne_of_gt hpos
    have hray : ∀ μ : ℝ, r₀ ≤ μ →
        q.1 (LinearMap.inl ℝ E ℝ x₀) + μ * q.1 ((0 : E), (1 : ℝ)) ≤ q.2 := by
      intro μ hμ
      have hmem : ((x₀, μ) : E × ℝ) ∈ epi f :=
        le_trans hp₀' (EReal.coe_le_coe_iff.2 hμ)
      rw [ht] at hmem
      have hq' := hmem q hq
      rwa [hsplit] at hq'
    obtain ⟨M, hM₁, hM₂⟩ : ∃ M : ℝ, r₀ ≤ M ∧
        (q.2 - q.1 (LinearMap.inl ℝ E ℝ x₀)) / q.1 ((0 : E), (1 : ℝ)) + 1 ≤ M :=
      ⟨max _ _, le_max_left _ _, le_max_right _ _⟩
    have h1 := hray M hM₁
    have h3 : ((q.2 - q.1 (LinearMap.inl ℝ E ℝ x₀)) / q.1 ((0 : E), (1 : ℝ)) + 1)
        * q.1 ((0 : E), (1 : ℝ))
        = q.2 - q.1 (LinearMap.inl ℝ E ℝ x₀) + q.1 ((0 : E), (1 : ℝ)) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_right hM₂ hpos.le
    rw [h3] at h4
    linarith
  -- Some inequality has a strictly negative one, or `f` would take the value `⊥` on `dom f`.
  have hfne : (t.filter fun q => q.1 ((0 : E), (1 : ℝ)) < 0).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (t.filter fun q => q.1 ((0 : E), (1 : ℝ)) < 0) with
      hfilt | h
    · refine absurd (le_bot_iff.1 ((EReal.le_of_forall_lt_iff_le (y := f x₀)).1 fun μ _ => ?_))
        (hb x₀)
      have hzero : ∀ q ∈ t, q.1 ((0 : E), (1 : ℝ)) = 0 := by
        intro q hq
        rcases lt_or_eq_of_le (hnp q hq) with hlt | heq
        · exact absurd (Finset.mem_filter.2 ⟨hq, hlt⟩) (by rw [hfilt]; simp)
        · exact heq
      have hmem : ((x₀, μ) : E × ℝ) ∈ epi f := by
        rw [ht]
        intro q hq
        rw [hsplit, hzero q hq, mul_zero, add_zero]
        have h0 := ht₀ q hq
        rw [hsplit q.1 x₀ r₀, hzero q hq, mul_zero, add_zero] at h0
        exact h0
      exact hmem
    · exact h
  -- The affine pieces.
  obtain ⟨s, hs⟩ : ∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ),
      s = (t.filter fun q => q.1 ((0 : E), (1 : ℝ)) < 0).image fun q =>
        ((-q.1 ((0 : E), (1 : ℝ)))⁻¹ • (q.1 ∘ₗ LinearMap.inl ℝ E ℝ),
          (-q.1 ((0 : E), (1 : ℝ)))⁻¹ * q.2) := ⟨_, rfl⟩
  have hsne : s.Nonempty := by
    obtain ⟨q, hq⟩ := hfne
    exact ⟨_, by rw [hs]; exact Finset.mem_image_of_mem _ hq⟩
  have hmaxle : ∀ (x : E) (μ : ℝ), maxAffineFn s x ≤ (μ : EReal)
      ↔ ∀ q ∈ t, q.1 ((0 : E), (1 : ℝ)) < 0 →
          q.1 (LinearMap.inl ℝ E ℝ x) + μ * q.1 ((0 : E), (1 : ℝ)) ≤ q.2 := by
    intro x μ
    rw [maxAffineFn_le_coe, hs]
    constructor
    · intro h q hq hlt
      have hmem := h _ (Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, hlt⟩, rfl⟩)
      rw [affine_le_iff_of_neg hlt]
      exact hmem
    · intro h ψ hψ
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hψ
      obtain ⟨hqt, hlt⟩ := Finset.mem_filter.1 hq
      change (-q.1 ((0 : E), (1 : ℝ)))⁻¹ * q.1 (LinearMap.inl ℝ E ℝ x)
          - (-q.1 ((0 : E), (1 : ℝ)))⁻¹ * q.2 ≤ μ
      rw [← affine_le_iff_of_neg hlt]
      exact h q hqt hlt
  refine ⟨s, funext fun x => ?_⟩
  change f x = maxAffineFn s x + indicatorFn (dom f) x
  by_cases hx : x ∈ dom f
  · rw [indicatorFn_of_mem hx, add_zero]
    refine EReal.eq_of_forall_le_coe_iff fun μ => ?_
    rw [hmaxle x μ]
    constructor
    · intro hfx q hq hlt
      have hmem : ((x, μ) : E × ℝ) ∈ epi f := hfx
      rw [ht] at hmem
      have hq' := hmem q hq
      rwa [hsplit] at hq'
    · intro hall
      obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hb x) hx
      have hmem : ((x, μ) : E × ℝ) ∈ epi f := by
        rw [ht]
        intro q hq
        rw [hsplit]
        rcases lt_or_eq_of_le (hnp q hq) with hlt | heq
        · exact hall q hq hlt
        · have hxν : ((x, ν) : E × ℝ) ∈ epi f := le_of_eq hν
          rw [ht] at hxν
          have h0 := hxν q hq
          rw [hsplit q.1 x ν, heq, mul_zero, add_zero] at h0
          rw [heq, mul_zero, add_zero]
          exact h0
      exact hmem
  · have htop : f x = ⊤ := top_le_iff.1 (not_lt.1 hx)
    rw [htop, indicatorFn_of_notMem hx]
    exact (EReal.add_top_of_ne_bot (maxAffineFn_ne_bot hsne x)).symm

/-- **The normal form characterises polyhedral convex functions.** A function that nowhere takes
the value `⊥` is polyhedral convex exactly when it is a pointwise maximum of finitely many affine
functions plus the indicator of a polyhedral convex set. -/
theorem polyhedralFn_iff_maxAffineFn_add_indicatorFn (hb : ∀ x, f x ≠ ⊥) :
    PolyhedralFn f ↔ ∃ (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) (C : Set E), Polyhedral C ∧
      f = maxAffineFn s + indicatorFn C := by
  constructor
  · intro hf
    obtain ⟨s, hs⟩ := hf.exists_maxAffineFn_add_indicatorFn_dom hb
    exact ⟨s, dom f, hf.polyhedral_dom, hs⟩
  · rintro ⟨s, C, hC, rfl⟩
    exact polyhedralFn_maxAffineFn_add_indicatorFn s hC

end Polyhedral

end ConvexAnalysis
