import Mathlib.Analysis.LocallyConvex.Separation
import Numlib.Analysis.Convex.Duality.Exact

/-!
# The continuity constraint qualification

If one of two proper convex functions is continuous at a point where the other is finite, they add
exactly: `(f + g)* = f* □ g*`, with the infimal convolution attained.

The classical qualification ([rockafellar1970convex] Theorem 16.4) asks instead that `ri (dom f)`
and `ri (dom g)` meet, which is sharp in finite dimensions but is not available in general, `ri`
being empty for most infinite-dimensional convex sets. Continuity is the condition that replaces it,
and the one every application in a Banach space actually verifies — typically because one summand is
finite and continuous everywhere.

## Main results

* `IsExactSum.of_continuousAt` — the qualification, the third constructor of `IsExactSum` alongside
  `IsExactSum.of_relint` (finite dimensions) and `IsExactSum.of_polyhedral`.

## Implementation notes

The only topological input is `geometric_hahn_banach_open`, which separates a *nonempty open*
convex set from a disjoint convex set in any real topological vector space; local convexity, which
is what separating two closed sets needs, is not required. Continuity at `x₀` is what supplies the
open set: it makes `f` bounded above near `x₀`, so the strict epigraph of `f` has interior.

With `a = (f + g)* y` finite, the hypothesis to be contradicted is `f x + g x < ⟨x, y⟩ - a`, so the
two sets separated are the strict epigraph of `f` and the hypograph of the concave function
`x ↦ ⟨x, y⟩ - a - g x`. The separating functional is non-vertical, and its `ℝ`-coefficient is
negative rather than positive because the strict epigraph is unbounded upwards.

## References

* [rockafellar1970convex] §16.
-/

open Set Filter
open scoped Topology

namespace ConvexAnalysis

section ContinuousAt

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f g : E → EReal}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The strict epigraph of a convex function is convex: the strict form of the epigraph
inequality (`convexFn_iff_forall_lt`) read as a statement about a set. -/
theorem ConvexFn.convex_strictEpi (hf : ConvexFn f) :
    Convex ℝ {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)} := by
  rintro ⟨x, μ⟩ hx ⟨x', μ'⟩ hx' s t hs ht hst
  refine combo_of_pos (P := fun p : E × ℝ => f p.1 < ((p.2 : ℝ) : EReal)) hx hx' hs ht hst
    fun hs' ht' => ?_
  have hcombo := (convexFn_iff_forall_lt f).1 hf x x' s t hs' ht' hst μ μ' hx hx'
  simpa [smul_eq_mul] using hcombo

/-- **The continuity constraint qualification.** If `f` and `g` are proper convex functions and `f`
is continuous at some point where both are finite, then `f` and `g` add exactly. This is the
constructor of `IsExactSum` that survives into infinite dimensions. -/
theorem IsExactSum.of_continuousAt (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConvexFn g)
    (hpg : ProperConvex g) {x₀ : E} (hfx₀ : x₀ ∈ convexDom f) (hgx₀ : x₀ ∈ convexDom g)
    (hcont : ContinuousAt f x₀) : IsExactSum B f g := by
  refine ⟨hpf, hpg, fun y => ?_⟩
  -- the value to be attained
  rcases eq_top_or_lt_top (convexConj B (f + g) y) with htop | hlt
  · exact ⟨y, 0, add_zero y, htop ▸ le_top⟩
  have hsumdom : (convexDom (f + g)).Nonempty := by
    refine ⟨x₀, ?_⟩
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x₀) hfx₀
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x₀) hgx₀
    have hval : (f + g) x₀ = ((p + q : ℝ) : EReal) := by
      rw [Pi.add_apply, hp, hq, ← EReal.coe_add]
    rw [mem_convexDom, hval]
    exact EReal.coe_lt_top _
  obtain ⟨a, ha⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (convexConj_ne_bot hsumdom y) hlt
  have hkey : ∀ x, ((B x y : ℝ) : EReal) - (a : EReal) ≤ f x + g x :=
    convexConj_le_coe_iff.1 ha.le
  -- the two convex sets
  have hC₂ : Convex ℝ {p : E × ℝ | g p.1 ≤ ((B p.1 y - a - p.2 : ℝ) : EReal)} := by
    rintro ⟨x, μ⟩ hx ⟨x', μ'⟩ hx' s t hs ht hst
    have hcombo := hg.epi_combo hx hx' hs ht hst
    refine le_trans hcombo (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    linear_combination (-a) * hst
  have hdisj : Disjoint {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)}
      {p : E × ℝ | g p.1 ≤ ((B p.1 y - a - p.2 : ℝ) : EReal)} := by
    rw [Set.disjoint_left]
    rintro ⟨x, μ⟩ h1 h2
    have h1' : f x < ((μ : ℝ) : EReal) := h1
    have h2' : g x ≤ ((B x y - a - μ : ℝ) : EReal) := h2
    obtain ⟨p, hp⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x) (h1'.trans_le le_top)
    obtain ⟨q, hq⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x)
        (lt_of_le_of_lt h2' (EReal.coe_lt_top _))
    rw [hp] at h1'
    rw [hq] at h2'
    have hpμ : p < μ := by exact_mod_cast h1'
    have hqb : q ≤ B x y - a - μ := by exact_mod_cast h2'
    have hk := hkey x
    rw [hp, hq, ← EReal.coe_add, ← EReal.coe_sub,
      EReal.coe_le_coe_iff] at hk
    linarith
  -- continuity gives the strict epigraph an interior
  obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.1 hfx₀
  obtain ⟨V, hVf, hVopen, hx₀V⟩ := mem_nhds_iff.1 ((tendsto_order.1 hcont).2 (r : EReal) hr)
  have hVsub : V ×ˢ Set.Ioi r ⊆ {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)} := by
    rintro ⟨x, μ⟩ hmem
    have hfx : f x < ((r : ℝ) : EReal) := hVf hmem.1
    have hμ : r < μ := hmem.2
    exact lt_trans hfx (by exact_mod_cast hμ)
  have hVint : V ×ˢ Set.Ioi r ⊆ interior {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)} :=
    interior_maximal hVsub (hVopen.prod isOpen_Ioi)
  have hint : (interior {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)}).Nonempty :=
    ⟨(x₀, r + 1), hVint ⟨hx₀V, by simp⟩⟩
  -- a point of the second set above `x₀`
  obtain ⟨q₀, hq₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x₀) hgx₀
  have hC₂x₀ : ((x₀, B x₀ y - a - q₀) : E × ℝ)
      ∈ {p : E × ℝ | g p.1 ≤ ((B p.1 y - a - p.2 : ℝ) : EReal)} := by
    have hval : g x₀ ≤ ((B x₀ y - a - (B x₀ y - a - q₀) : ℝ) : EReal) := by
      rw [hq₀]
      exact EReal.coe_le_coe_iff.2 (le_of_eq (by ring))
    exact hval
  -- separate
  obtain ⟨φ, u, hφ1, hφ2⟩ := geometric_hahn_banach_open (Convex.interior hf.convex_strictEpi)
    isOpen_interior hC₂ (Set.disjoint_of_subset_left interior_subset hdisj)
  have hφ1' : ∀ p ∈ {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)}, φ p ≤ u := by
    intro p hp
    have hcl : closure (interior {p : E × ℝ | f p.1 < ((p.2 : ℝ) : EReal)}) ⊆ {q | φ q ≤ u} :=
      (isClosed_le φ.continuous continuous_const).closure_subset_iff.2 fun q hq => (hφ1 q hq).le
    refine hcl ?_
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior hf.convex_strictEpi hint]
    exact subset_closure hp
  -- split the functional and show it is not vertical
  obtain ⟨⟨ψ, c⟩, hsplit, -⟩ := exists_unique_dual_prod φ
  have hsplit' : ∀ (x : E) (μ : ℝ), φ (x, μ) = ψ x + c * μ := hsplit
  have hup : ∀ μ : ℝ, r < μ → ψ x₀ + c * μ < u := fun μ hμ => by
    have hmem : ((x₀, μ) : E × ℝ) ∈ V ×ˢ Set.Ioi r := ⟨hx₀V, hμ⟩
    have h := hφ1 _ (hVint hmem)
    rwa [hsplit'] at h
  have hcneg : c < 0 := by
    rcases lt_trichotomy c 0 with hc | hc | hc
    · exact hc
    · exfalso
      have h1 : ψ x₀ + c * (r + 1) < u := hup (r + 1) (by linarith)
      have h2 : u ≤ ψ x₀ + c * (B x₀ y - a - q₀) := by
        have h := hφ2 _ hC₂x₀
        rwa [hsplit'] at h
      rw [hc] at h1 h2
      linarith
    · exfalso
      have hcM : c * ((u - ψ x₀) / c) = u - ψ x₀ := by field_simp
      have h1 := hup (max (r + 1) ((u - ψ x₀) / c + 1))
        (lt_of_lt_of_le (by linarith) (le_max_left _ _))
      have h2 : (u - ψ x₀) / c + 1 ≤ max (r + 1) ((u - ψ x₀) / c + 1) := le_max_right _ _
      nlinarith [h1, h2, hcM, hc]
  -- normalise the vertical coefficient to `-t` with `t > 0`
  obtain ⟨t, htpos, rfl⟩ : ∃ t : ℝ, 0 < t ∧ c = -t := ⟨-c, by linarith, by ring⟩
  obtain ⟨y₁, hy₁⟩ := exists_pairing_eq B (t⁻¹ • ψ)
  have hy₁' : ∀ x, ψ x = t * B x y₁ := by
    intro x
    have h : t⁻¹ * ψ x = B x y₁ := hy₁ x
    have h2 : t * (t⁻¹ * ψ x) = t * B x y₁ := by rw [h]
    rwa [← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul] at h2
  obtain ⟨d, hd⟩ : ∃ d : ℝ, t * d = u := ⟨u / t, by field_simp⟩
  have hlow : ∀ (x : E) (μ : ℝ), f x < ((μ : ℝ) : EReal) → B x y₁ - d ≤ μ := by
    intro x μ hμ
    have h := hφ1' (x, μ) hμ
    rw [hsplit', hy₁' x] at h
    exact le_of_mul_le_mul_left (by linarith : t * (B x y₁ - d) ≤ t * μ) htpos
  have hhigh : ∀ (x : E) (μ : ℝ), g x ≤ ((B x y - a - μ : ℝ) : EReal) → μ ≤ B x y₁ - d := by
    intro x μ hμ
    have h := hφ2 (x, μ) hμ
    rw [hsplit', hy₁' x] at h
    exact le_of_mul_le_mul_left (by linarith : t * μ ≤ t * (B x y₁ - d)) htpos
  -- read off the two affine minorants
  refine ⟨y₁, y - y₁, by abel, ?_⟩
  have hA : convexConj B f y₁ ≤ (d : EReal) := by
    refine convexConj_le_coe_iff.2 fun x => ?_
    rw [affineFn_eq_coe]
    rcases eq_top_or_lt_top (f x) with hx | hx
    · rw [hx]; exact le_top
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x) hx
    rw [hp, EReal.coe_le_coe_iff]
    rcases le_or_gt (B x y₁ - d) p with hle | hgt
    · exact hle
    · exfalso
      have hmid : p < (p + (B x y₁ - d)) / 2 := by linarith
      have hstep := hlow x ((p + (B x y₁ - d)) / 2) (by rw [hp]; exact_mod_cast hmid)
      linarith
  have hBb : convexConj B g (y - y₁) ≤ ((a - d : ℝ) : EReal) := by
    refine convexConj_le_coe_iff.2 fun x => ?_
    rw [affineFn_eq_coe]
    rcases eq_top_or_lt_top (g x) with hx | hx
    · rw [hx]; exact le_top
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpg.ne_bot x) hx
    rw [hp, EReal.coe_le_coe_iff]
    have hstep := hhigh x (B x y - a - p) (by rw [hp]; exact_mod_cast le_of_eq (by ring))
    have hBsub : B x (y - y₁) = B x y - B x y₁ := map_sub (B x) y y₁
    rw [hBsub]
    linarith
  calc convexConj B f y₁ + convexConj B g (y - y₁) ≤ (d : EReal) + ((a - d : ℝ) : EReal) :=
        add_le_add hA hBb
    _ = (a : EReal) := by rw [← EReal.coe_add]; norm_num
    _ = convexConj B (f + g) y := ha.symm

end ContinuousAt

end ConvexAnalysis
