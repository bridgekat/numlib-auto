/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Function

/-!
# The normal form of a polyhedral convex function

A polyhedral convex function that never takes the value $-\infty$ is exactly a pointwise maximum of
finitely many affine functions, restricted to a polyhedral convex set ([rockafellar1970convex],
§19). That is, $f = h + \delta(\cdot \mid C)$ with $$h(x) = \max \{ \varphi_1(x) - \beta_1, \dots,
\varphi_k(x) - \beta_k \}, \qquad C = \{ x \mid \varphi_j(x) \le \beta_j,\ j = k + 1, \dots, m \},$$
where the $\varphi_i$ are linear functionals and the $\beta_i$ are real numbers.

The two parts come from the two kinds of closed half-space in a polyhedral description of
$\operatorname{epi} f \subseteq E \times \mathbb{R}$. A half-space with a non-vertical bounding
hyperplane is the epigraph of an affine function. A half-space with a vertical bounding hyperplane
constrains only $x$. There is no third kind, because the vertical sections of $\operatorname{epi} f$
are closed upwards, so no constraint bounds the vertical variable from above. The proof sorts a
polyhedral system for $\operatorname{epi} f$ into these two groups.

## Main definitions

* `ConvexAnalysis.maxAffineFn`: the pointwise maximum $x \mapsto \max_{(\varphi, \beta) \in s}
  (\varphi(x) - \beta)$ of a finite family of affine functions, with values in $[-\infty, +\infty]$.
  The empty family gives the constant $-\infty$.

## Main results

* `ConvexAnalysis.polyhedralFn_maxAffineFn`,
  `ConvexAnalysis.polyhedralFn_maxAffineFn_add_indicatorFn`: a function in normal form is always
  polyhedral. No hypothesis is needed: for $s = \emptyset$ the function is $-\infty$, whose epigraph
  is the whole space.
* `ConvexAnalysis.PolyhedralFn.exists_maxAffineFn_add_indicatorFn_convexDom`: every polyhedral
  convex function that never takes the value $-\infty$ is in normal form, with
  $C = \operatorname{dom} f$. The vertical inequalities cut out a polyhedral set that can be larger
  than $\operatorname{dom} f$, but $f$ is $+\infty$ off $\operatorname{dom} f$ in any case.
* `ConvexAnalysis.polyhedralFn_iff_maxAffineFn_add_indicatorFn`: the two results together, as an
  equivalence.

## Implementation notes

* The hypothesis that $f$ never takes the value $-\infty$ is necessary. A function in normal form
  never takes the value $-\infty$ if the family is nonempty, and it is the constant $-\infty$ if the
  family is empty, because $-\infty + (+\infty) = -\infty$ in `EReal`. The function that is
  $-\infty$ on a nonempty polyhedral set $C \ne E$ and $+\infty$ elsewhere is convex with the
  polyhedral epigraph $C \times \mathbb{R}$, but it has no normal form.
  The classical convention makes polyhedral convex functions proper, so this hypothesis is weaker
  than the classical one.
* The direction from polyhedral functions to the normal form needs no finite dimension. Only the
  converse uses the Minkowski–Weyl theorem, through `ConvexAnalysis.PolyhedralFn.add`.
-/

open Set

namespace ConvexAnalysis

section MaxAffine

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For a finite set $s$ of pairs $(\varphi, \beta)$ of a linear functional $\varphi$ on $E$ and a
real number $\beta$, the pointwise maximum of the affine functions
$x \mapsto \varphi(x) - \beta$: $$x \mapsto \sup_{(\varphi, \beta) \in s} \big( \varphi(x) -
\beta \big) \in [-\infty, +\infty].$$

For $s = \emptyset$ the function is the constant $-\infty$, which is the value of an empty
supremum in `EReal`. -/
noncomputable def maxAffineFn (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) : E → EReal :=
  fun x => ⨆ q ∈ s, ((q.1 x - q.2 : ℝ) : EReal)

variable {s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)} {x : E} {c : ℝ}

/-- For $c \in \mathbb{R}$, the maximum of the affine functions of $s$ at $x$ is at most $c$ if and
only if $\varphi(x) - \beta \le c$ for every $(\varphi, \beta) \in s$. -/
theorem maxAffineFn_le_coe : maxAffineFn s x ≤ (c : EReal) ↔ ∀ q ∈ s, q.1 x - q.2 ≤ c := by
  rw [maxAffineFn, iSup₂_le_iff]
  exact forall₂_congr fun _ _ => EReal.coe_le_coe_iff

/-- For every $(\varphi, \beta) \in s$ and every $x$, $\varphi(x) - \beta$ is at most the maximum of
the affine functions of $s$ at $x$. -/
theorem coe_le_maxAffineFn {q : (E →ₗ[ℝ] ℝ) × ℝ} (hq : q ∈ s) :
    ((q.1 x - q.2 : ℝ) : EReal) ≤ maxAffineFn s x :=
  le_iSup₂ (f := fun q (_ : q ∈ s) => ((q.1 x - q.2 : ℝ) : EReal)) q hq

/-- If $s$ is nonempty, then the maximum of the affine functions of $s$ never takes the value
$-\infty$. -/
theorem maxAffineFn_ne_bot (hs : s.Nonempty) (x : E) : maxAffineFn s x ≠ ⊥ := by
  obtain ⟨q, hq⟩ := hs
  intro h
  have hle : ((q.1 x - q.2 : ℝ) : EReal) ≤ ⊥ := h ▸ coe_le_maxAffineFn hq
  exact absurd (le_bot_iff.1 hle) (EReal.coe_ne_bot _)

/-- For $s = \emptyset$, the maximum of the affine functions of $s$ is the constant $-\infty$. -/
@[simp] theorem maxAffineFn_empty : maxAffineFn (∅ : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) = fun _ : E => ⊥ :=
  funext fun _ => by simp [maxAffineFn]

end MaxAffine

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- For every finite family $s$ of affine functions, the maximum of the family is a polyhedral
convex function. Its epigraph is cut out by the inequalities $\varphi(x) - \mu \le \beta$,
$(\varphi, \beta) \in s$. -/
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
/-- The constant function $-\infty$ is a polyhedral convex function, because its epigraph is all of
$E \times \mathbb{R}$. -/
theorem polyhedralFn_bot : PolyhedralFn (fun _ : E => (⊥ : EReal)) := by
  have h : epi (fun _ : E => (⊥ : EReal)) = (Set.univ : Set (E × ℝ)) := by
    ext p; simp
  rw [PolyhedralFn, h]
  exact polyhedral_univ

/-- **A function in normal form is polyhedral.** Let $E$ be a finite-dimensional real normed space,
let $s$ be a finite family of affine functions with maximum $h$, and let $C \subseteq E$ be a
polyhedral convex set. Then $h + \delta(\cdot \mid C)$ is a polyhedral convex function.

For a nonempty family this is `ConvexAnalysis.PolyhedralFn.add` applied to
`ConvexAnalysis.polyhedralFn_maxAffineFn` and `ConvexAnalysis.polyhedralFn_indicatorFn`. For the
empty family, $h + \delta(\cdot \mid C)$ is the constant $-\infty$, because
$-\infty + (+\infty) = -\infty$ in `EReal`. -/
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

/-- If $c < 0$, then $A + \mu c \le b$ if and only if $(-c)^{-1} A - (-c)^{-1} b \le \mu$: a
negative coefficient on the vertical variable turns the inequality into the epigraph inequality
of an affine function. -/
private theorem affine_le_iff_of_neg {A b c μ : ℝ} (hc : c < 0) :
    A + μ * c ≤ b ↔ (-c)⁻¹ * A - (-c)⁻¹ * b ≤ μ := by
  have hc' : (0 : ℝ) < -c := by linarith
  have hcne : c ≠ 0 := ne_of_lt hc
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
/-- **The normal form of a polyhedral convex function.** Let $E$ be a real normed space and let
$f \colon E \to [-\infty, +\infty]$ be a polyhedral convex function that never takes the value
$-\infty$. Then there is a finite family of affine functions with maximum $h$ such that $$f =
h + \delta(\cdot \mid \operatorname{dom} f).$$

The affine functions come from the non-vertical inequalities of a polyhedral system for
$\operatorname{epi} f$, each divided by minus its coefficient on the vertical variable, which is
negative. The vertical inequalities constrain only $x$ and hold on all of
$\operatorname{dom} f$, which is why $\operatorname{dom} f$ itself serves as the set. In finite
dimensions $\operatorname{dom} f$ is polyhedral by
`ConvexAnalysis.PolyhedralFn.polyhedral_convexDom`. No inequality has a positive coefficient on
the vertical variable, because the vertical sections of $\operatorname{epi} f$ are closed
upwards. -/
theorem PolyhedralFn.exists_maxAffineFn_add_indicatorFn_convexDom (hf : PolyhedralFn f)
    (hb : ∀ x, f x ≠ ⊥) :
    ∃ s : Finset ((E →ₗ[ℝ] ℝ) × ℝ), f = maxAffineFn s + indicatorFn (convexDom f) := by
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
    have hdom : convexDom f = (∅ : Set E) := by
      ext x
      simp [htop x]
    refine ⟨{(0, 0)}, funext fun x => ?_⟩
    have hmax : maxAffineFn ({((0 : E →ₗ[ℝ] ℝ), (0 : ℝ))} : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) x = 0 := by
      simp [maxAffineFn]
    change f x = maxAffineFn _ x + indicatorFn (convexDom f) x
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
  change f x = maxAffineFn s x + indicatorFn (convexDom f) x
  by_cases hx : x ∈ convexDom f
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

/-- **The normal form characterizes polyhedral convex functions.** Let $E$ be a finite-dimensional
real normed space and let $f \colon E \to [-\infty, +\infty]$ never take the value $-\infty$.
Then $f$ is a polyhedral convex function if and only if there are a finite family of affine
functions with maximum $h$ and a polyhedral convex set $C \subseteq E$ such that
$f = h + \delta(\cdot \mid C)$. -/
theorem polyhedralFn_iff_maxAffineFn_add_indicatorFn (hb : ∀ x, f x ≠ ⊥) :
    PolyhedralFn f ↔ ∃ (s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) (C : Set E), Polyhedral C ∧
      f = maxAffineFn s + indicatorFn C := by
  constructor
  · intro hf
    obtain ⟨s, hs⟩ := hf.exists_maxAffineFn_add_indicatorFn_convexDom hb
    exact ⟨s, convexDom f, hf.polyhedral_convexDom, hs⟩
  · rintro ⟨s, C, hC, rfl⟩
    exact polyhedralFn_maxAffineFn_add_indicatorFn s hC

end Polyhedral

end ConvexAnalysis
