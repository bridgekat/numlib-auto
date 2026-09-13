import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Homogenize
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.LinearAlgebra.Subspace
import Mathlib.Analysis.Convex.EGauge
import Mathlib.Analysis.Convex.Gauge

/-!
# Gauges, polars of convex functions, and obverses

The **gauge** of a set `C` is `γ(x ∣ C) = inf {a ≥ 0 ∣ x ∈ a • C}`: the least dilation of `C` that
swallows `x`, and `+∞` when none does. Gauges are exactly the nonnegative positively homogeneous
convex functions vanishing at `0`, and `C ↦ γ(· ∣ C)` is a bijection from closed convex sets
containing `0` to closed gauges. Three polarity operations act here, each an involution on its
class: the polar `k°(y) = inf {μ ≥ 0 ∣ ⟨x, y⟩ ≤ μ k(x)}` of a gauge, the polar
`f°(y) = inf {μ ≥ 0 ∣ ⟨x, y⟩ ≤ 1 + μ f(x)}` of a nonnegative closed convex `f` with `f 0 = 0`, and
the obverse `fᵒ(x) = inf {λ > 0 ∣ λ f(x / λ) ≤ 1}`. On a gauge the first two agree, and the obverse
ties them to the Fenchel conjugate: `f* = (f°)ᵒ`. Two facts about polar *sets* are proved here too,
because the gauge is what makes them short: the recession cone of a closed convex set containing the
origin is the polar of its polar, and the polar of a sublevel set of a nonnegative convex function
is within a factor of two of the corresponding sublevel set of the conjugate.

## Main definitions

* `gaugeFn C`, `IsGauge k` — the gauge, `EReal`-valued, and its characterising properties.
* `polarGauge B k`, `polarFn B f`, `obverse f` — the three operations above. `polarFn` infimises
  over `epi f`; `polarFn_apply_eq` recovers the book's formula.
* `IsPolarFn f` — nonnegative, closed, convex, `f 0 = 0`: the class `polarFn` inverts.
* `IsNorm k` — a gauge that is finite, symmetric and positive off `0`; `IsNorm.toSeminorm` builds
  the Mathlib `Seminorm`. `AbsorbsAll C` and `RayFree C` make `γ(· ∣ C)` a norm.
* `epiPairing B`, `vNeg X` — the pairing of `E × ℝ` with `F × ℝ`, and vertical reflection.
* `UpClosed S` — upward closed subsets of `ℝ`, the shape of every admissible-scalar set here.

## Main results

* `gaugeEquiv`, `isGauge_iff` — the correspondence `k = γ(· ∣ C)`, `C = {k ≤ 1}`.
* `recessionCone_eq_polarCone_polarSet`, `polarCone_linealitySpace` — the recession cone of `C` is
  the polar of `C°`, and the lineality space of `C` is the annihilator of `C°`;
  `finrank_vectorSpan_polarSet_add_lineality` and its companion read these through `finrank` as
  `dim C° = n - lin C` and `lin C° = n - dim C`. `polarSet_setOf_le_subset_and_subset` traps
  `α⁻¹ {f* ≤ α}` between `{f ≤ α}°` and `2 {f ≤ α}°`.
* `polarGauge_eq_supportFn`, `polarGauge_polarGauge`, `polarGaugeEquiv` — the polar of a gauge is
  the support function of its unit level set, and `k°° = cl k` (Theorem 15.1 in [^1]). `isNorm_iff`
  identifies the norms among the gauges.
* `polarFn_polarFn`, `polarFnEquiv` — `f°° = cl f`, so `f ↦ f°` is an involution on the nonnegative
  closed convex functions vanishing at the origin (Theorem 15.4 in [^1]).
* `obverse_obverse`, `conj_eq_obverse_polarFn`, `polarFn_eq_obverse_conj` — the obverse is an
  involution, and `f°` and `f*` are obverses of each other (Theorem 15.5 in [^1]);
  `polarFn_conj_eq_conj_polarFn` is `f*° = f°*`, and `setOf_polarFn_le` is
  `{f° ≤ α⁻¹} = α⁻¹ {f* ≤ α}`.

## Implementation notes

`gaugeFn` is `EReal`-valued and infimises over `a ≥ 0`, so it is `+∞` off `⋃ a • C`; that is what
makes `{γ ≤ c}` equal `c • C`. Mathlib's `gauge` infimises over `a > 0` into `ℝ` and returns `0`
there instead — the two agree under absorbency (`gaugeFn_eq_gauge`) — while `egauge` is this same
infimum taken in `ℝ≥0∞`, whereas every function in this library is `EReal`-valued.

The book's admissible set for `f°`, `{μ ≥ 0 ∣ ⟨x, y⟩ ≤ 1 + μ f(x) ∀ x}`, is not closed: at `μ = 0`
the convention `0 · (+∞) = 0` imposes `⟨x, y⟩ ≤ 1` where `f x = +∞`, which nearby positive `μ` do
not. Quantifying over `epi f` gives a closed, upward closed set with the same infimum.

## Divergences from the reference

The sublevel-set inclusions are stated for any nonnegative convex `f` with `f 0 ≤ 0`, with no
closedness. `isNorm_iff` uses `AbsorbsAll C` and `RayFree C` where the book has `0 ∈ int C` and `C`
bounded — equivalent readings in `ℝⁿ` — and does not assert that a norm is closed, which the book
obtains from the continuity of a finite convex function on `ℝⁿ`. `gaugeFn_level_one` needs only
nonnegativity, positive homogeneity and `k 0 = 0`, and `gaugeFn_polarSet` (`γ(· ∣ C°) = δ*(· ∣ C)`)
needs only `0 ∈ C`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §14 and §15.
-/

open Set Pointwise
open scoped NNReal ENNReal

namespace ConvexAnalysis

/-! ### Infima of upward closed sets of reals

Every definition in this file is an infimum `⨅ a ∈ S, (a : EReal)` of a set `S ⊆ ℝ` of admissible
scalars, and every proof about it needs to convert `⨅ a ∈ S, a ≤ c` into a statement about
membership in `S`. The two lemmas here are that conversion: it is unconditional in the form "every
`d > c` lies in `S`" once `S` is upward closed, and becomes "`c ∈ S`" once `S` is also closed. -/

section UpClosed

variable {S : Set ℝ}

/-- `S ⊆ ℝ` is **upward closed**: the shape shared by the admissible-scalar sets of `gaugeFn`,
`polarGauge`, `polarFn` and `obverse`. -/
def UpClosed (S : Set ℝ) : Prop := ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, a ≤ b → b ∈ S

/-- The infimum of an upward closed set of reals is `≤ c` exactly when every `d > c` belongs to
it. -/
theorem biInf_coe_le_coe_iff_forall_lt (hS : UpClosed S) (c : ℝ) :
    (⨅ a ∈ S, (a : EReal)) ≤ (c : EReal) ↔ ∀ d : ℝ, c < d → d ∈ S := by
  constructor
  · intro h d hd
    have hlt : (⨅ a ∈ S, (a : EReal)) < (d : EReal) :=
      lt_of_le_of_lt h (EReal.coe_lt_coe_iff.2 hd)
    rw [iInf_lt_iff] at hlt
    obtain ⟨a, ha⟩ := hlt
    rw [iInf_lt_iff] at ha
    obtain ⟨haS, halt⟩ := ha
    exact hS haS (EReal.coe_lt_coe_iff.1 halt).le
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨d, hcd, hd⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    exact absurd (iInf₂_le d (h d (EReal.coe_lt_coe_iff.1 hcd))) (not_le.2 hd)

/-- For a closed upward closed set of reals, the infimum is `≤ c` exactly when `c` belongs to
it. -/
theorem biInf_coe_le_coe_iff (hS : UpClosed S) (hcl : IsClosed S) (c : ℝ) :
    (⨅ a ∈ S, (a : EReal)) ≤ (c : EReal) ↔ c ∈ S := by
  refine ⟨fun h => ?_, fun h => iInf₂_le c h⟩
  rw [biInf_coe_le_coe_iff_forall_lt hS] at h
  have hten : Filter.Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) Filter.atTop (nhds c) := by
    have : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add this
  refine hcl.mem_of_tendsto hten (Filter.Eventually.of_forall fun n => h _ ?_)
  have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  linarith

/-- The infimum of a nonempty upward closed set of reals bounded below by `0` is nonnegative. -/
theorem zero_le_biInf_coe (h : ∀ a ∈ S, (0 : ℝ) ≤ a) : 0 ≤ ⨅ a ∈ S, (a : EReal) :=
  le_iInf₂ fun a ha => EReal.coe_nonneg.2 (h a ha)

/-- If `z ≤ d` for every real `d` above `r`, then `z ≤ r`: Mathlib's
`EReal.le_of_forall_lt_iff_le` with the hypothesis stated in `ℝ`. -/
theorem le_coe_of_forall_gt_le {z : EReal} {r : ℝ} (h : ∀ d : ℝ, r < d → z ≤ (d : EReal)) :
    z ≤ (r : EReal) :=
  EReal.le_of_forall_lt_iff_le.1 fun d hd => h d (EReal.coe_lt_coe_iff.1 hd)

end UpClosed

/-! ### The gauge of a convex set

`γ(x | C) = inf {a ≥ 0 | x ∈ a • C}`. The scalar `0` is admitted, and
`0 • C = {0}` for nonempty `C`, so `γ(0 | C) = 0` for every nonempty `C` — that is what makes a
gauge vanish at the origin even when `C` does not contain it. -/

section GaugeFn

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C D : Set E} {x : E} {a c t : ℝ}

/-- **The gauge** of a set `C`: `γ(x | C) = inf {a ≥ 0 | x ∈ a • C}`.

Named `gaugeFn` because it is neither of Mathlib's two Minkowski functionals; `gaugeFn_eq_gauge`
and `gaugeFn_eq_egauge` are the bridges, and the module docstring says why the `EReal`-valued
version is the one this development needs. -/
noncomputable def gaugeFn (C : Set E) : E → EReal :=
  fun x => ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal)

theorem gaugeFn_apply (C : Set E) (x : E) :
    gaugeFn C x = ⨅ a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}, (a : EReal) := rfl

theorem gaugeFn_le_of_mem_smul (ha : 0 ≤ a) (h : x ∈ a • C) : gaugeFn C x ≤ (a : EReal) :=
  iInf₂_le a ⟨ha, h⟩

theorem gaugeFn_nonneg (C : Set E) (x : E) : 0 ≤ gaugeFn C x :=
  zero_le_biInf_coe fun _ ha => ha.1

theorem gaugeFn_ne_bot (C : Set E) (x : E) : gaugeFn C x ≠ ⊥ :=
  fun h => by simpa [h] using gaugeFn_nonneg C x

/-- **The witness extractor**: a strict upper bound for the gauge is witnessed by an admissible
scalar. The infimum is not attained in general, so this is the only way in. -/
theorem gaugeFn_lt_iff {z : EReal} :
    gaugeFn C x < z ↔ ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C ∧ (a : EReal) < z := by
  rw [gaugeFn_apply, iInf_lt_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [iInf_lt_iff] at ha
    obtain ⟨⟨ha0, hmem⟩, halt⟩ := ha
    exact ⟨a, ha0, hmem, halt⟩
  · rintro ⟨a, ha0, hmem, halt⟩
    exact ⟨a, by rw [iInf_lt_iff]; exact ⟨⟨ha0, hmem⟩, halt⟩⟩

theorem gaugeFn_anti (h : C ⊆ D) : gaugeFn D ≤ gaugeFn C :=
  fun _ => iInf₂_mono' fun a ha => ⟨a, ⟨ha.1, smul_set_mono h ha.2⟩, le_rfl⟩

@[simp] theorem gaugeFn_empty : gaugeFn (∅ : Set E) = fun _ => (⊤ : EReal) := by
  funext x
  simp [gaugeFn_apply]

/-- **A gauge vanishes at the origin**: `0 ∈ 0 • C` as soon as `C` is nonempty. -/
@[simp] theorem gaugeFn_zero (hne : C.Nonempty) : gaugeFn C 0 = 0 := by
  refine le_antisymm ?_ (gaugeFn_nonneg C 0)
  obtain ⟨z, hz⟩ := hne
  simpa using gaugeFn_le_of_mem_smul (C := C) le_rfl ⟨z, hz, by simp⟩

theorem gaugeFn_smul_le (ht : 0 < t) (C : Set E) (x : E) :
    gaugeFn C (t • x) ≤ (t : EReal) * gaugeFn C x := by
  rw [gaugeFn_apply C x, EReal.coe_mul_iInf ht]
  refine le_iInf fun a => ?_
  rw [EReal.coe_mul_iInf ht]
  refine le_iInf fun ha => ?_
  rw [← EReal.coe_mul]
  obtain ⟨z, hz, hzx⟩ := ha.2
  refine gaugeFn_le_of_mem_smul (mul_nonneg ht.le ha.1) ⟨z, hz, ?_⟩
  change (t * a) • z = t • x
  rw [mul_smul]
  exact congrArg (t • ·) hzx

theorem posHomogeneous_gaugeFn (C : Set E) : PosHomogeneous (gaugeFn C) := by
  intro t ht x
  refine le_antisymm (gaugeFn_smul_le ht C x) ?_
  have h := gaugeFn_smul_le (inv_pos.2 ht) C (t • x)
  rw [inv_smul_smul₀ ht.ne'] at h
  have h2 : (t : EReal) * gaugeFn C x ≤ (t : EReal) * ((t⁻¹ : ℝ) * gaugeFn C (t • x)) :=
    mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.2 ht.le)
  rwa [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul] at h2

theorem convexFn_gaugeFn (hC : Convex ℝ C) : ConvexFn (gaugeFn C) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  refine EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_
  replace hq := EReal.coe_lt_coe_iff.1 hq
  set ε : ℝ := q - (a * μ + b * ν) with hε
  have hε0 : 0 < ε := by simp only [hε]; linarith
  have hxs : gaugeFn C x < ((μ + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hx (EReal.coe_lt_coe_iff.2 (by linarith))
  have hys : gaugeFn C y < ((ν + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hy (EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨s, hs0, hsC, hslt⟩ := gaugeFn_lt_iff.1 hxs
  obtain ⟨u, hu0, huC, hult⟩ := gaugeFn_lt_iff.1 hys
  have hslt' : s < μ + ε := EReal.coe_lt_coe_iff.1 hslt
  have hult' : u < ν + ε := EReal.coe_lt_coe_iff.1 hult
  have hmem : a • x + b • y ∈ (a * s + b * u) • C := by
    rw [hC.add_smul (by positivity) (by positivity)]
    exact ⟨a • x, by rw [mul_smul]; exact smul_mem_smul_set hsC,
      b • y, by rw [mul_smul]; exact smul_mem_smul_set huC, rfl⟩
  refine lt_of_le_of_lt (gaugeFn_le_of_mem_smul (by positivity) hmem)
    (EReal.coe_lt_coe_iff.2 ?_)
  have h1 : a * s < a * (μ + ε) := mul_lt_mul_of_pos_left hslt' ha'
  have h2 : b * u < b * (ν + ε) := mul_lt_mul_of_pos_left hult' hb'
  have h3 : a * (μ + ε) + b * (ν + ε) = a * μ + b * ν + ε := by
    have : a * ε + b * ε = ε := by linear_combination ε * hab
    nlinarith [this]
  simp only [hε] at h3 ⊢
  linarith

end GaugeFn

/-! ### Gauges

A **gauge** is a nonnegative positively homogeneous convex function vanishing at the origin —
equivalently, a function whose epigraph is a convex cone containing the origin and no `(x, μ)` with
`μ < 0`. `isGauge_iff` is the other description: the gauges are exactly the `γ(· | C)` for nonempty
convex `C`. -/

section IsGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {k : E → EReal} {x : E} {a b c : ℝ}

/-- **A gauge**: a nonnegative positively homogeneous convex function that vanishes at the
origin. -/
structure IsGauge (k : E → EReal) : Prop where
  /-- A gauge is nonnegative. -/
  nonneg : ∀ x, 0 ≤ k x
  /-- A gauge is positively homogeneous. -/
  posHomogeneous : PosHomogeneous k
  /-- A gauge is convex. -/
  convexFn : ConvexFn k
  /-- A gauge vanishes at the origin. This is a genuine extra condition: it rules out `k ≡ +∞`,
  which satisfies the other three. -/
  map_zero : k 0 = 0

theorem IsGauge.ne_bot (hk : IsGauge k) (x : E) : k x ≠ ⊥ :=
  fun h => by simpa [h] using hk.nonneg x

theorem isGauge_gaugeFn (hC : Convex ℝ C) (hne : C.Nonempty) : IsGauge (gaugeFn C) where
  nonneg := gaugeFn_nonneg C
  posHomogeneous := posHomogeneous_gaugeFn C
  convexFn := convexFn_gaugeFn hC
  map_zero := gaugeFn_zero hne

theorem IsGauge.convex_level_one (hk : IsGauge k) : Convex ℝ {x : E | k x ≤ 1} :=
  hk.convexFn.convex_le 1

theorem IsGauge.zero_mem_level_one (hk : IsGauge k) : (0 : E) ∈ {x : E | k x ≤ 1} := by
  change k 0 ≤ 1
  rw [hk.map_zero]
  exact zero_le_one

/-- **A gauge is the gauge of its own unit level set**: `γ(· | {k ≤ 1}) = k`. Convexity is not
used — only nonnegativity, positive homogeneity, and `k 0 = 0`.

This is the half of the gauge/set correspondence that needs no topology; the other half,
`level_one_gaugeFn`, does. -/
theorem gaugeFn_level_one (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    gaugeFn {x : E | k x ≤ 1} = k := by
  set D : Set E := {x : E | k x ≤ 1} with hD
  have h0D : (0 : E) ∈ D := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  funext x
  refine le_antisymm ?_ ?_
  · rcases eq_or_lt_of_le (le_top (a := k x)) with htop | hlt
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    have hr0 : (0 : ℝ) ≤ r := by
      have := hnn x; rw [hr] at this; exact EReal.coe_nonneg.1 this
    rcases eq_or_lt_of_le hr0 with rfl | hrpos
    · rw [hr]
      refine le_coe_of_forall_gt_le fun d hd => ?_
      refine gaugeFn_le_of_mem_smul hd.le ⟨d⁻¹ • x, ?_, smul_inv_smul₀ hd.ne' x⟩
      change k (d⁻¹ • x) ≤ 1
      rw [hph d⁻¹ (inv_pos.2 hd) x, hr]
      simp
    · rw [hr]
      refine gaugeFn_le_of_mem_smul hr0 ⟨r⁻¹ • x, ?_, smul_inv_smul₀ hrpos.ne' x⟩
      change k (r⁻¹ • x) ≤ 1
      rw [hph r⁻¹ (inv_pos.2 hrpos) x, hr, ← EReal.coe_mul, inv_mul_cancel₀ hrpos.ne']
      exact le_rfl
  · rw [gaugeFn_apply]
    refine le_iInf₂ fun a ha => ?_
    obtain ⟨ha0, z, hz, hzx⟩ := ha
    rcases eq_or_lt_of_le ha0 with rfl | hapos
    · have : x = 0 := by rw [← hzx]; simp
      rw [this, h0]
      exact le_rfl
    · have hzx' : a • z = x := hzx
      rw [← hzx', hph a hapos z]
      have hz1 : k z ≤ 1 := hz
      calc (a : EReal) * k z ≤ (a : EReal) * 1 :=
            mul_le_mul_of_nonneg_left hz1 (EReal.coe_nonneg.2 ha0)
        _ = (a : EReal) := by rw [mul_one]

/-- **The gauges are exactly the gauge functions of the nonempty convex sets.** `{x | k x ≤ 1}` is
the canonical choice of set, and it is the only closed one containing the origin (`gaugeEquiv`). -/
theorem isGauge_iff : IsGauge k ↔ ∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ k = gaugeFn C := by
  refine ⟨fun hk => ⟨{x | k x ≤ 1}, ⟨0, hk.zero_mem_level_one⟩, hk.convex_level_one,
      (gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero).symm⟩, ?_⟩
  rintro ⟨C, hne, hC, rfl⟩
  exact isGauge_gaugeFn hC hne

end IsGauge

/-! ### Gauges of sets containing the origin

The admissible-scalar set `{a ≥ 0 | x ∈ a • C}` is upward closed exactly because `a • C ⊆ b • C`
for `0 ≤ a ≤ b` when `C` is convex and contains the origin. Everything quantitative about `gaugeFn`
goes through that. -/

section ZeroMem

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {x : E} {a b c : ℝ}

theorem smul_subset_smul_of_le (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (ha : 0 ≤ a) (hab : a ≤ b) :
    a • C ⊆ b • C := by
  rintro _ ⟨z, hz, rfl⟩
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simpa using ⟨0, h0, by simp⟩
  · have hbpos : 0 < b := lt_of_lt_of_le hapos hab
    refine ⟨(a / b) • z, hC.smul_mem_of_zero_mem h0 hz ⟨by positivity, by
      rw [div_le_one hbpos]; exact hab⟩, ?_⟩
    change b • (a / b) • z = a • z
    rw [smul_smul, mul_div_cancel₀ _ hbpos.ne']

/-- The admissible-scalar set of the gauge is upward closed, for a convex set containing the
origin. -/
theorem upClosed_gaugeSet (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (x : E) :
    UpClosed {a : ℝ | 0 ≤ a ∧ x ∈ a • C} :=
  fun _ ha _ hab => ⟨ha.1.trans hab, smul_subset_smul_of_le hC h0 ha.1 hab ha.2⟩

/-- **The level sets of a gauge, without closedness.** `γ(x | C) ≤ c` exactly when `x ∈ d • C` for
every `d > c`. -/
theorem gaugeFn_le_coe_iff_forall_lt (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hc : 0 ≤ c) :
    gaugeFn C x ≤ (c : EReal) ↔ ∀ d : ℝ, c < d → x ∈ d • C := by
  rw [gaugeFn_apply, biInf_coe_le_coe_iff_forall_lt (upClosed_gaugeSet hC h0 x)]
  exact forall₂_congr fun d hd => ⟨fun h => h.2, fun h => ⟨le_of_lt (lt_of_le_of_lt hc hd), h⟩⟩

/-- The sublevel sets of a gauge, as intersections of dilates. -/
theorem setOf_gaugeFn_le (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hc : 0 ≤ c) :
    {x : E | gaugeFn C x ≤ (c : EReal)} = ⋂ d ∈ Ioi c, d • C := by
  ext x
  rw [mem_iInter₂]
  exact gaugeFn_le_coe_iff_forall_lt hC h0 hc

end ZeroMem

/-! ### Closed gauges

For a *closed* convex set containing the origin the level sets of the gauge are the dilates
themselves, `{x | γ(x | C) ≤ c} = c • C` for `c > 0`, and the gauge is closed. `gaugeEquiv`
packages the resulting one-to-one correspondence. -/

section ClosedGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {C : Set E} {x : E} {c : ℝ}

/-- **The level sets of a closed gauge are the dilates.** `γ(x | C) ≤ c` exactly when `x ∈ c • C`,
for `c > 0` and `C` closed convex containing the origin.

The restriction to `c > 0` is essential: `{x | γ(x | C) ≤ 0}` is the recession cone of `C`, not
`0 • C = {0}`. -/
theorem gaugeFn_le_coe_iff (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) (hc : 0 < c) :
    gaugeFn C x ≤ (c : EReal) ↔ x ∈ c • C := by
  refine ⟨fun h => ?_, fun h => gaugeFn_le_of_mem_smul hc.le h⟩
  rw [gaugeFn_le_coe_iff_forall_lt hC h0 hc.le] at h
  rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne' C x]
  have hseq : Filter.Tendsto (fun n : ℕ => (c + 1 / (n + 1 : ℝ))⁻¹ • x) Filter.atTop
      (nhds (c⁻¹ • x)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) Filter.atTop (nhds c) := by
      simpa using Filter.Tendsto.const_add c tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Continuous fun r : ℝ => r • x := continuous_id.smul continuous_const
    exact (h2.tendsto (c⁻¹)).comp (h1.inv₀ hc.ne')
  refine hcl.mem_of_tendsto hseq (Filter.Eventually.of_forall fun n => ?_)
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hd : c < c + 1 / (n + 1 : ℝ) := by linarith
  exact (mem_smul_set_iff_inv_smul_mem₀ (by linarith : c + 1 / (n + 1 : ℝ) ≠ 0) C x).1 (h _ hd)

/-- The sublevel sets of a closed gauge, for a positive level. -/
theorem setOf_gaugeFn_le_pos (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) (hc : 0 < c) :
    {x : E | gaugeFn C x ≤ (c : EReal)} = c • C :=
  Set.ext fun _ => gaugeFn_le_coe_iff hC h0 hcl hc

/-- **The unit level set of the gauge recovers the set**: `{x | γ(x | C) ≤ 1} = C` for a closed
convex set containing the origin. Together with `gaugeFn_level_one` this is the one-to-one
correspondence between closed gauges and closed convex sets containing the origin. -/
theorem setOf_gaugeFn_le_one (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    {x : E | gaugeFn C x ≤ 1} = C := by
  have h := setOf_gaugeFn_le_pos hC h0 hcl one_pos
  rw [EReal.coe_one] at h
  rw [h, one_smul]

/-- The gauge of a closed convex set containing the origin is lower semicontinuous: each of its
sublevel sets is an intersection of dilates of `C`. -/
theorem lowerSemicontinuous_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    LowerSemicontinuous (gaugeFn C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro z
  have hset : gaugeFn C ⁻¹' Iic z = {x : E | gaugeFn C x ≤ z} := rfl
  rw [hset]
  induction z using EReal.rec with
  | bot =>
    have : {x : E | gaugeFn C x ≤ (⊥ : EReal)} = ∅ := by
      ext x
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, le_bot_iff]
      exact gaugeFn_ne_bot C x
    rw [this]; exact isClosed_empty
  | coe r =>
    rcases lt_or_ge r 0 with hr | hr
    · have : {x : E | gaugeFn C x ≤ (r : EReal)} = ∅ := by
        ext x
        simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false]
        exact fun hx => absurd (le_trans (gaugeFn_nonneg C x) hx)
          (not_le.2 (by exact_mod_cast hr))
      rw [this]; exact isClosed_empty
    · rw [setOf_gaugeFn_le hC h0 hr]
      exact isClosed_biInter fun d hd => hcl.smul_of_ne_zero (by
        have : (0 : ℝ) < d := lt_of_le_of_lt hr hd
        exact this.ne')
  | top =>
    have : {x : E | gaugeFn C x ≤ (⊤ : EReal)} = univ := by ext x; simp
    rw [this]; exact isClosed_univ

variable [IsTopologicalAddGroup E]

theorem closedFn_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hcl : IsClosed C) :
    ClosedFn (gaugeFn C) :=
  (closedFn_iff_lowerSemicontinuous (gaugeFn_ne_bot C)).2 (lowerSemicontinuous_gaugeFn hC h0 hcl)

omit [Module ℝ E] [ContinuousSMul ℝ E] in
theorem isClosed_setOf_le_one {k : E → EReal} (hc : ClosedFn k) :
    IsClosed {x : E | k x ≤ 1} :=
  ClosedFn.lowerSemicontinuous hc |>.isClosed_preimage 1

/-- **The gauge correspondence**: the closed gauges on `E` are in bijection with the closed convex
subsets of `E` containing the origin, by `C ↦ γ(· | C)` and `k ↦ {x | k x ≤ 1}`.

This is the gauge analogue of `supportEquiv` (`Duality/Support.lean`). -/
noncomputable def gaugeEquiv (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℝ E] [IsTopologicalAddGroup E] :
    {C : Set E // Convex ℝ C ∧ IsClosed C ∧ (0 : E) ∈ C} ≃
      {k : E → EReal // IsGauge k ∧ ClosedFn k} where
  toFun C := ⟨gaugeFn C.1, isGauge_gaugeFn C.2.1 ⟨0, C.2.2.2⟩,
    closedFn_gaugeFn C.2.1 C.2.2.2 C.2.2.1⟩
  invFun k := ⟨{x | k.1 x ≤ 1}, k.2.1.convex_level_one, isClosed_setOf_le_one k.2.2,
    k.2.1.zero_mem_level_one⟩
  left_inv C := Subtype.ext (setOf_gaugeFn_le_one C.2.1 C.2.2.2 C.2.2.1)
  right_inv k := Subtype.ext
    (gaugeFn_level_one k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero)

end ClosedGauge

/-! ### The gauge of a polar set

The gauge of `C°` is the support function of `C`. The book states this for a closed convex `C`
containing the origin, as part of the polarity theorem; only `0 ∈ C` is used. -/

section GaugePolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- **The gauge of the polar set is the support function**: `γ(· | C°) = δ*(· | C)`.

Only `0 ∈ C` is needed — neither convexity nor closedness — because `0 ∈ C` is exactly what makes
`δ*(· | C)` nonnegative, and the two infima then agree scalar by scalar. -/
theorem gaugeFn_polarSet (h0 : (0 : E) ∈ C) : gaugeFn (polarSet B C) = supportFn B C := by
  funext y
  have hsupp0 : (0 : EReal) ≤ supportFn B C y := by
    have h := le_supportFn (B := B) h0 y
    rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
  refine le_antisymm ?_ ?_
  · by_cases htop : supportFn B C y = ⊤
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simp [h] at hsupp0) (lt_top_iff_ne_top.2 htop)
    have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hsupp0; exact EReal.coe_nonneg.1 hsupp0
    have hbound : ∀ x ∈ C, B x y ≤ r := supportFn_le_coe_iff.1 (le_of_eq hr)
    rw [hr]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hr0 hd
    refine gaugeFn_le_of_mem_smul hd0.le ⟨d⁻¹ • y, fun x hx => ?_, smul_inv_smul₀ hd0.ne' y⟩
    rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hd0, mul_one]
    exact le_of_lt (lt_of_le_of_lt (hbound x hx) hd)
  · rw [gaugeFn_apply]
    refine le_iInf₂ fun a ha => ?_
    obtain ⟨ha0, w, hw, hwy⟩ := ha
    rw [supportFn_le_coe_iff]
    intro x hx
    have hy : a • w = y := hwy
    rw [← hy, map_smul, smul_eq_mul]
    calc a * B x w ≤ a * 1 := by
          exact mul_le_mul_of_nonneg_left (hw x hx) ha0
      _ = a := mul_one a

end GaugePolar

/-! ### The recession cone and the lineality space as polars

`0⁺C` and the closed convex cone generated by `C°` are polar to each other, and the lineality space
of `C` is the annihilator of `C°`. The classical proof reads the recession cone off as the largest
closed convex cone inside `C`; the argument here identifies it directly as a polar, which needs only
the bipolar theorem. -/

section RecessionLineality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] in
/-- The easy half: a recession direction of a set containing the origin is nonpositively paired
with every element of the polar. -/
theorem recessionCone_subset_polarCone_polarSet (h0 : (0 : E) ∈ C) :
    recessionCone C ⊆ polarCone B.flip (polarSet B C) := by
  intro v hv y hy
  rw [LinearMap.flip_apply]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨t, ht⟩ := exists_gt (1 / B v y)
  have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) ht.le
  have hmem : (0 : E) + t • v ∈ C := hv 0 h0 t ht0
  rw [zero_add] at hmem
  have := hy _ hmem
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [div_lt_iff₀ hcon] at ht
  nlinarith

/-- **The recession cone is the polar of the polar set**, for a closed convex set containing the
origin. -/
theorem recessionCone_eq_polarCone_polarSet [IsCompatiblePairing B] (hconv : Convex ℝ C)
    (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone C = polarCone B.flip (polarSet B C) := by
  refine subset_antisymm (recessionCone_subset_polarCone_polarSet h0) fun v hv x hx a ha => ?_
  rw [← polarSet_polarSet (B := B) hconv hcl h0]
  intro y hy
  simp only [LinearMap.flip_apply, map_add, map_smul, smul_eq_mul]
  have h1 : B x y ≤ 1 := by
    have := hx
    rw [← polarSet_polarSet (B := B) hconv hcl h0] at this
    exact this y hy
  have h2 : B v y ≤ 0 := hv y hy
  nlinarith

/-- **The recession cone of a polar set is a polar cone**: `0⁺(C°) = C°` read as a *cone* polar
rather than a *set* polar, for a closed convex `C` containing the origin.

The previous result applied to `C°`, whose bipolar is `C` (`polarSet_polarSet`). Both spaces are
topologised here, because the recession cone being computed lives in `F`. -/
theorem recessionCone_polarSet [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    recessionCone (polarSet B C) = polarCone B C := by
  have h := recessionCone_eq_polarCone_polarSet (B := B.flip) (C := polarSet B C)
    (convex_polarSet B C) isClosed_polarSet (zero_mem_polarSet B C)
  rwa [LinearMap.flip_flip, polarSet_polarSet (B := B) hconv hcl h0] at h

/-- **The recession cone of `C` and the closed convex cone generated by `C°` are polar to each
other.** -/
theorem polarCone_recessionCone [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarCone B (recessionCone C) =
      closure (PointedCone.hull ℝ (polarSet B C) : Set F) := by
  rw [recessionCone_eq_polarCone_polarSet (B := B) hconv hcl h0,
    ← polarCone_hull B.flip (polarSet B C)]
  have h := polarCone_polarCone (B := B.flip)
    (K := (PointedCone.hull ℝ (polarSet B C) : Set F))
    ((PointedCone.hull ℝ (polarSet B C) : ConvexCone ℝ F).convex)
    (smul_coe_pointedCone _) ⟨0, (PointedCone.hull ℝ (polarSet B C)).zero_mem⟩
  rwa [LinearMap.flip_flip] at h

/-- **The lineality space of a closed convex set containing the origin is the annihilator of its
polar.** -/
theorem linealitySpace_eq_setOf_pairing_eq_zero [IsCompatiblePairing B] (hconv : Convex ℝ C)
    (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    linealitySpace C = {x : E | ∀ y ∈ polarSet B C, B x y = 0} := by
  ext v
  rw [mem_linealitySpace, recessionCone_eq_polarCone_polarSet (B := B) hconv hcl h0]
  constructor
  · rintro ⟨h1, h2⟩ y hy
    have e1 : B v y ≤ 0 := h1 y hy
    have e2 : B (-v) y ≤ 0 := h2 y hy
    rw [map_neg, LinearMap.neg_apply] at e2
    linarith
  · intro h
    exact ⟨fun y hy => le_of_eq (h y hy), fun y hy => by
      rw [LinearMap.flip_apply, map_neg, LinearMap.neg_apply, h y hy, neg_zero]⟩

/-- **The polar of the lineality space of `C` is the closed subspace generated by `C°`**, the dual
form of the previous result. -/
theorem polarCone_linealitySpace [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    polarCone B (linealitySpace C) =
      closure (Submodule.span ℝ (polarSet B C) : Set F) := by
  have hlin : linealitySpace C =
      polarCone B.flip (Submodule.span ℝ (polarSet B C) : Set F) := by
    rw [linealitySpace_eq_setOf_pairing_eq_zero (B := B) hconv hcl h0,
      polarCone_coe_submodule' B.flip (Submodule.span ℝ (polarSet B C))]
    ext v
    simp only [Set.mem_ofPred, LinearMap.flip_apply]
    refine ⟨fun h y hy => ?_, fun h y hy => h y (Submodule.subset_span hy)⟩
    exact Submodule.span_induction (fun z hz => h z hz) (map_zero (B v))
      (fun z w _ _ hz hw => by rw [map_add, hz, hw, add_zero])
      (fun a z _ hz => by rw [map_smul, hz, smul_zero]) hy
  rw [hlin]
  have h := polarCone_polarCone (B := B.flip)
    (K := (Submodule.span ℝ (polarSet B C) : Set F))
    (Submodule.span ℝ (polarSet B C)).convex
    (fun a ha => by
      ext z
      exact ⟨fun ⟨w, hw, hwz⟩ => hwz ▸ Submodule.smul_mem _ a hw,
        fun hz => ⟨a⁻¹ • z, Submodule.smul_mem _ _ hz, smul_inv_smul₀ ha.ne' z⟩⟩)
    ⟨0, (Submodule.span ℝ (polarSet B C)).zero_mem⟩
  rwa [LinearMap.flip_flip] at h

end RecessionLineality

/-! ### The dimension relations for a polar set

`dim C° = n - lin C` and `lin C° = n - dim C`. They are the orthogonality above read through
`finrank`: the polar of a *subspace* is its annihilator, and the annihilator of a subspace of a
finite-dimensional space has the complementary dimension. -/

/-! `vectorSpan_eq_span_of_zero_mem` — the affine and linear hulls of a set through the origin
agree — is `vectorSpan_eq_span_of_zero_mem` in `Numlib/LinearAlgebra/Subspace.lean`. It has no
convexity in it and three unrelated developments want it. -/

section PolarDimension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

/-- **The polar of a subspace has the complementary dimension.** This is rank–nullity for the map
`F → M*` that a compatible pairing induces: it is onto because `B.flip` is onto `E*` (compatibility,
plus the automatic continuity of a functional in finite dimensions) and restriction `E* → M*` is
onto, and its kernel is the polar of `M`. -/
theorem finrank_add_finrank_polarSubmodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    (M : Submodule ℝ E) :
    Module.finrank ℝ M + Module.finrank ℝ (polarSubmodule B M) = Module.finrank ℝ F := by
  classical
  have hflip : Function.Surjective (B.flip : F →ₗ[ℝ] Module.Dual ℝ E) := by
    intro g
    obtain ⟨y, hy⟩ := exists_pairing_eq B (LinearMap.toContinuousLinearMap g)
    refine ⟨y, LinearMap.ext fun x => ?_⟩
    have h := hy x
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [LinearMap.flip_apply, ← h]
  have hsurj : Function.Surjective ((Submodule.subtype M).dualMap.comp B.flip) :=
    (LinearMap.dualMap_surjective_of_injective (Submodule.injective_subtype M)).comp hflip
  have hker : LinearMap.ker ((Submodule.subtype M).dualMap.comp B.flip) = polarSubmodule B M := by
    ext y
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, polarSubmodule, Submodule.mem_comap,
      Submodule.mem_dualAnnihilator, LinearMap.flip_apply]
    constructor
    · intro h w hw
      have hval := congrArg (fun g : Module.Dual ℝ M => g ⟨w, hw⟩) h
      simpa using hval
    · intro h
      ext m
      simpa using h (m : E) m.2
  have hrk := LinearMap.finrank_range_add_finrank_ker ((Submodule.subtype M).dualMap.comp B.flip)
  rw [LinearMap.range_eq_top.2 hsurj, hker, finrank_top, Subspace.dual_finrank_eq] at hrk
  exact hrk

/-- **`dim C° = n - lin C`** for a closed convex set containing the origin, stated without
truncated subtraction, as `dim C° + lin C = n`.

The subspace generated by `C°` is the polar of the lineality space of `C`
(`polarCone_linealitySpace`; the closure there is redundant in finite dimensions), and the affine
hull of `C°` is its linear hull because `0 ∈ C°`. -/
theorem finrank_vectorSpan_polarSet_add_lineality [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    Module.finrank ℝ (vectorSpan ℝ (polarSet B C)) + lineality C = Module.finrank ℝ F := by
  have hspan : vectorSpan ℝ (polarSet B C) = Submodule.span ℝ (polarSet B C) :=
    vectorSpan_eq_span_of_zero_mem (zero_mem_polarSet B C)
  have hpol : polarSubmodule B (linealitySubmodule C) = Submodule.span ℝ (polarSet B C) := by
    refine SetLike.coe_injective ?_
    rw [coe_polarSubmodule, coe_linealitySubmodule,
      polarCone_linealitySpace (B := B) hconv hcl h0,
      (Submodule.closed_of_finiteDimensional (Submodule.span ℝ (polarSet B C))).closure_eq]
  rw [hspan, ← hpol, lineality, add_comm]
  exact finrank_add_finrank_polarSubmodule B (linealitySubmodule C)

/-- **`lin C° = n - dim C`**, again without truncated subtraction. It is the first relation applied
to the polar pair the other way round, using `C°° = C`.

The book's third relation, `rank C° = rank C`, is the difference of the two: both `dim C° + lin C`
and `dim C + lin C°` equal `n`. -/
theorem finrank_vectorSpan_add_lineality_polarSet [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hconv : Convex ℝ C) (hcl : IsClosed C) (h0 : (0 : E) ∈ C) :
    Module.finrank ℝ (vectorSpan ℝ C) + lineality (polarSet B C) = Module.finrank ℝ E := by
  have hcvx : Convex ℝ (polarSet B C) := by
    intro y hy z hz s t hs ht hst x hx
    have h1 : B x y ≤ 1 := hy x hx
    have h2 : B x z ≤ 1 := hz x hx
    have hval : B x (s • y + t • z) = s * B x y + t * B x z := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hval]
    nlinarith
  have h := finrank_vectorSpan_polarSet_add_lineality (B := B.flip) (C := polarSet B C)
    hcvx isClosed_polarSet (zero_mem_polarSet B C)
  rwa [polarSet_polarSet (B := B) hconv hcl h0] at h

end PolarDimension

/-! ### The polar of a sublevel set

For a nonnegative convex function vanishing at the origin, the polar of a sublevel set and the
corresponding sublevel set of the conjugate are within a factor of `2` of each other. -/

section SublevelPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {α : ℝ}

/-- A convex function that is nonpositive at the origin is **subhomogeneous** for factors in
`[0, 1]`: `f (t • x) ≤ t * r` whenever `f x ≤ r`. -/
theorem ConvexFn.smul_le_coe (hconv : ConvexFn f) (h0 : f 0 ≤ 0) {t r : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {x : E} (hx : f x ≤ (r : EReal)) : f (t • x) ≤ ((t * r : ℝ) : EReal) := by
  have h0' : f 0 ≤ ((0 : ℝ) : EReal) := by rwa [EReal.coe_zero]
  have h := hconv.epi_combo hx h0' (a := t) (b := 1 - t) ht0 (by linarith) (by ring)
  simpa using h

/-- The conjugate of a function that is nonpositive at the origin is nonnegative. -/
theorem zero_le_conj (h0 : f 0 ≤ 0) (y : F) : 0 ≤ conj B f y := by
  refine le_trans ?_ (sub_le_conj B f 0 y)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub, EReal.le_neg,
    neg_zero]
  exact h0

/-- The conjugate of a nonnegative function vanishing at the origin again vanishes at the
origin. -/
theorem conj_zero_eq_zero (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) : conj B f 0 = 0 := by
  refine le_antisymm ?_ (zero_le_conj h0 0)
  rw [conj_apply]
  refine iSup_le fun x => ?_
  rw [map_zero, EReal.coe_zero, zero_sub, EReal.neg_le, neg_zero]
  exact hnn x

/-- **The first inclusion** (in scaled form): `α • {f ≤ α}° ⊆ {f* ≤ α}`.

The book proves this through the positively homogeneous function generated by `f* + α`. The direct
argument is shorter: for `f x > α` the point `(α / f x) • x` lies in the sublevel set, and rescaling
the inequality it satisfies gives `⟨x, y⟩ ≤ f x`. -/
theorem smul_polarSet_setOf_le_subset (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0)
    (hα : 0 < α) :
    α • polarSet B {x : E | f x ≤ (α : EReal)} ⊆ {y : F | conj B f y ≤ (α : EReal)} := by
  rintro _ ⟨w, hw, rfl⟩
  change conj B f (α • w) ≤ (α : EReal)
  rw [conj_apply]
  refine iSup_le fun x => ?_
  have hBx : B x (α • w) = α * B x w := by rw [map_smul, smul_eq_mul]
  by_cases hfx : f x ≤ (α : EReal)
  · have h1 : B x w ≤ 1 := hw x hfx
    have h2 : B x (α • w) ≤ α := by rw [hBx]; nlinarith
    calc ((B x (α • w) : ℝ) : EReal) - f x
        ≤ ((α : ℝ) : EReal) - 0 := EReal.sub_le_sub (EReal.coe_le_coe_iff.2 h2) (hnn x)
      _ = (α : EReal) := by rw [sub_zero]
  · rw [not_le] at hfx
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop]
      simp
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    rw [hr] at hfx
    have hαr : α < r := EReal.coe_lt_coe_iff.1 hfx
    have hr0 : (0 : ℝ) < r := lt_trans hα hαr
    have ht : f ((α / r) • x) ≤ ((α : ℝ) : EReal) := by
      have := ConvexFn.smul_le_coe hconv h0 (t := α / r) (r := r) (by positivity)
        (by rw [div_le_one hr0]; linarith) (le_of_eq hr)
      rwa [div_mul_cancel₀ _ hr0.ne'] at this
    have h1 : B ((α / r) • x) w ≤ 1 := hw _ ht
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : B x (α • w) ≤ r := by
      have hkey : α * B x w = r * (α / r * B x w) := by field_simp
      rw [hBx, hkey]
      exact mul_le_of_le_one_right hr0.le h1
    rw [hr]
    calc ((B x (α • w) : ℝ) : EReal) - (r : EReal)
        ≤ ((r : ℝ) : EReal) - (r : EReal) := EReal.sub_le_sub
          (EReal.coe_le_coe_iff.2 h2) le_rfl
      _ = 0 := by rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
      _ ≤ (α : EReal) := EReal.coe_nonneg.2 hα.le

/-- **The second inclusion** (in scaled form): `{f* ≤ α} ⊆ (2α) • {f ≤ α}°`. This half is
Fenchel's inequality and nothing else. -/
theorem setOf_conj_le_subset_smul_polarSet (hnn : ∀ x, 0 ≤ f x) (hα : 0 < α) :
    {y : F | conj B f y ≤ (α : EReal)} ⊆ (2 * α) • polarSet B {x : E | f x ≤ (α : EReal)} := by
  intro y hy
  have hy' : conj B f y ≤ (α : EReal) := hy
  have h2α : (2 * α) ≠ 0 := by positivity
  rw [mem_smul_set_iff_inv_smul_mem₀ h2α]
  intro x hx
  have hx' : f x ≤ (α : EReal) := hx
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 * α), mul_one]
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (fun h => by simpa [h] using hnn x) (lt_of_le_of_lt hx' (EReal.coe_lt_top α))
  have hr0 : (0 : ℝ) ≤ r := by
    have := hnn x; rw [hr] at this; exact EReal.coe_nonneg.1 this
  have hrα : r ≤ α := by rw [hr] at hx'; exact EReal.coe_le_coe_iff.1 hx'
  have hsub := le_trans (sub_le_conj B f x y) hy'
  rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hsub
  linarith

/-- **The two inclusions together**: `{f ≤ α}° ⊆ α⁻¹ • {f* ≤ α} ⊆ 2 • {f ≤ α}°`. -/
theorem polarSet_setOf_le_subset_and_subset (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x)
    (h0 : f 0 ≤ 0) (hα : 0 < α) :
    polarSet B {x : E | f x ≤ (α : EReal)} ⊆ α⁻¹ • {y : F | conj B f y ≤ (α : EReal)} ∧
      α⁻¹ • {y : F | conj B f y ≤ (α : EReal)} ⊆
        (2 : ℝ) • polarSet B {x : E | f x ≤ (α : EReal)} := by
  constructor
  · intro y hy
    have h : α⁻¹ • (α • polarSet B {x : E | f x ≤ (α : EReal)}) ⊆
        α⁻¹ • {y : F | conj B f y ≤ (α : EReal)} :=
      smul_set_mono (smul_polarSet_setOf_le_subset hconv hnn h0 hα)
    rw [smul_smul, inv_mul_cancel₀ hα.ne', one_smul] at h
    exact h hy
  · intro y hy
    have h : α⁻¹ • {y : F | conj B f y ≤ (α : EReal)} ⊆
        α⁻¹ • ((2 * α) • polarSet B {x : E | f x ≤ (α : EReal)}) :=
      smul_set_mono (setOf_conj_le_subset_smul_polarSet (B := B) hnn hα)
    rw [smul_smul] at h
    have hcalc : α⁻¹ * (2 * α) = 2 := by field_simp
    rw [hcalc] at h
    exact h hy

end SublevelPolar

/-! ### The polar of a gauge

`k°(y) = inf {μ ≥ 0 | ⟨x, y⟩ ≤ μ k(x) for all x}`. The content of this section is that `k°` is the
support function of `{k ≤ 1}`, hence a closed gauge, and that it is `γ(· | C°)` whenever
`k = γ(· | C)`. -/

section PolarGauge

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {k : E → EReal} {C : Set E} {y : F}

/-- **The polar of a gauge**: `k°(y) = inf {μ ≥ 0 | ⟨x, y⟩ ≤ μ k(x) for every x}`.

The product `μ * k x` is `EReal` multiplication, so `0 * (+∞) = 0`; that makes `μ = 0` admissible
only when `⟨·, y⟩ ≤ 0` everywhere, which is the classical reading of the `μ* = 0` case. The infimum
is insensitive to the convention, since the admissible set is an up-set in `[0, ∞)`. -/
noncomputable def polarGauge (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) : F → EReal :=
  fun y => ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x}, (μ : EReal)

theorem polarGauge_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) (y : F) :
    polarGauge B k y =
      ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x}, (μ : EReal) :=
  rfl

theorem polarGauge_le_of_forall {μ : ℝ} (hμ : 0 ≤ μ)
    (h : ∀ x : E, ((B x y : ℝ) : EReal) ≤ (μ : EReal) * k x) : polarGauge B k y ≤ (μ : EReal) :=
  iInf₂_le μ ⟨hμ, h⟩

theorem polarGauge_nonneg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (k : E → EReal) (y : F) :
    0 ≤ polarGauge B k y :=
  zero_le_biInf_coe fun _ hμ => hμ.1

/-- **The polar of a gauge is the support function of its unit level set.**

Convexity of `k` is not used; nonnegativity, positive homogeneity and `k 0 = 0` are. -/
theorem polarGauge_eq_supportFn (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    polarGauge B k = supportFn B {x : E | k x ≤ 1} := by
  have h0D : (0 : E) ∈ {x : E | k x ≤ 1} := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  funext y
  have hs0 : (0 : EReal) ≤ supportFn B {x : E | k x ≤ 1} y := by
    have h := le_supportFn (B := B) h0D y
    rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h
  refine le_antisymm ?_ ?_
  · by_cases htop : supportFn B {x : E | k x ≤ 1} y = ⊤
    · rw [htop]; exact le_top
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simp [h] at hs0) (lt_top_iff_ne_top.2 htop)
    have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hs0; exact EReal.coe_nonneg.1 hs0
    have hbound : ∀ x, k x ≤ 1 → B x y ≤ r := supportFn_le_coe_iff.1 (le_of_eq hr)
    rw [hr]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hr0 hd
    refine polarGauge_le_of_forall hd0.le fun x => ?_
    rcases eq_or_lt_of_le (le_top (a := k x)) with htopx | hltx
    · rw [htopx, EReal.coe_mul_top_of_pos hd0]
      exact le_top
    obtain ⟨sx, hsx⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hltx
    have hsx0 : (0 : ℝ) ≤ sx := by
      have := hnn x; rw [hsx] at this; exact EReal.coe_nonneg.1 this
    rw [hsx, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    rcases eq_or_lt_of_le hsx0 with hzero | hpos
    · have hray : ∀ t : ℝ, 0 < t → t * B x y ≤ r := by
        intro t ht
        have hkt : k (t • x) ≤ 1 := by
          rw [hph t ht x, hsx, ← hzero]
          simp
        have hb := hbound _ hkt
        rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
      have hle0 : B x y ≤ 0 := by
        by_contra hcon
        rw [not_le] at hcon
        have ht : (0 : ℝ) < (r + 1) / B x y := by positivity
        have hb := hray _ ht
        rw [div_mul_cancel₀ _ hcon.ne'] at hb
        linarith
      rw [← hzero]
      nlinarith
    · have hmem : k (sx⁻¹ • x) ≤ 1 := by
        rw [hph _ (inv_pos.2 hpos) x, hsx, ← EReal.coe_mul, inv_mul_cancel₀ hpos.ne']
        exact le_rfl
      have hb := hbound _ hmem
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hpos] at hb
      nlinarith
  · rw [polarGauge_apply]
    refine le_iInf₂ fun μ hμ => ?_
    obtain ⟨hμ0, hμk⟩ := hμ
    rw [supportFn_le_coe_iff]
    intro x hx
    have h2 : (μ : EReal) * k x ≤ (μ : EReal) * 1 :=
      mul_le_mul_of_nonneg_left hx (EReal.coe_nonneg.2 hμ0)
    rw [mul_one] at h2
    exact EReal.coe_le_coe_iff.1 (le_trans (hμk x) h2)

/-- **The polar of a gauge is a gauge.** -/
theorem isGauge_polarGauge (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    IsGauge (polarGauge B k) := by
  have h0D : (0 : E) ∈ {x : E | k x ≤ 1} := by change k 0 ≤ 1; rw [h0]; exact zero_le_one
  rw [polarGauge_eq_supportFn hnn hph h0]
  refine ⟨fun y => ?_, posHomogeneous_supportFn B _, convexFn_supportFn B _,
    supportFn_zero ⟨0, h0D⟩⟩
  have h := le_supportFn (B := B) h0D y
  rwa [map_zero, LinearMap.zero_apply, EReal.coe_zero] at h

/-- The polar of a gauge is a **closed** gauge. -/
theorem closedFn_polarGauge [TopologicalSpace F] [IsTopologicalAddGroup F]
    [IsContinuousPairing B.flip] (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    ClosedFn (polarGauge B k) := by
  rw [polarGauge_eq_supportFn hnn hph h0]
  exact closedFn_supportFn

theorem polarSet_setOf_gaugeFn_le_one (C : Set E) :
    polarSet B {x : E | gaugeFn C x ≤ 1} = polarSet B C := by
  refine subset_antisymm (polarSet_anti fun x hx => ?_) fun y hy x hx => ?_
  · exact gaugeFn_le_of_mem_smul zero_le_one ⟨x, hx, one_smul ℝ x⟩
  · have hx' : gaugeFn C x ≤ 1 := hx
    refine le_of_forall_gt_imp_ge_of_dense fun q hq => ?_
    have hlt : gaugeFn C x < ((q : ℝ) : EReal) := by
      refine lt_of_le_of_lt hx' ?_
      rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one]]
      exact EReal.coe_lt_coe_iff.2 hq
    obtain ⟨a, ha0, ⟨z, hz, hza⟩, halt⟩ := gaugeFn_lt_iff.1 hlt
    have haq : a < q := EReal.coe_lt_coe_iff.1 halt
    have hzx : a • z = x := hza
    have hzy : B z y ≤ 1 := hy z hz
    rw [← hzx, map_smul, LinearMap.smul_apply, smul_eq_mul]
    nlinarith

/-- **Polarity of gauges is polarity of sets**: if `k = γ(· | C)` for a nonempty convex set `C`,
then `k° = γ(· | C°)`.

`C` is neither required to contain the origin nor to be closed — the polar set does not
distinguish `C` from `{x | γ(x | C) ≤ 1}`, which does contain the origin. -/
theorem polarGauge_gaugeFn (hC : Convex ℝ C) (hne : C.Nonempty) :
    polarGauge B (gaugeFn C) = gaugeFn (polarSet B C) := by
  have hg := isGauge_gaugeFn hC hne
  rw [polarGauge_eq_supportFn hg.nonneg hg.posHomogeneous hg.map_zero,
    ← polarSet_setOf_gaugeFn_le_one (B := B) C,
    gaugeFn_polarSet (B := B) (C := {x : E | gaugeFn C x ≤ 1}) hg.zero_mem_level_one]

/-- For a convex set containing the origin, the gauge function and the support function of `C` are
gauges polar to each other. -/
theorem polarGauge_gaugeFn_eq_supportFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    polarGauge B (gaugeFn C) = supportFn B C := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩, gaugeFn_polarSet h0]

end PolarGauge

/-! ### The pairing of `E × ℝ` with `F × ℝ`

Polarity of a function is polarity of its epigraph, one dimension higher, so it needs a pairing of
`E × ℝ` with `F × ℝ`. `prodPairing` (`Duality/Pairing.lean`) supplies it once `ℝ` is paired with
itself, and `mulPairing` is that self-pairing. -/

section EpiPairing

/-- The self-pairing of `ℝ` by multiplication. -/
def mulPairing : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := LinearMap.mul ℝ ℝ

@[simp] theorem mulPairing_apply (a b : ℝ) : mulPairing a b = a * b := rfl

@[simp] theorem mulPairing_flip : mulPairing.flip = mulPairing :=
  LinearMap.ext fun a => LinearMap.ext fun b => mul_comm b a

instance : IsContinuousPairing mulPairing where
  continuous_left b := by simpa using continuous_mul_const b

instance : IsCompatiblePairing mulPairing where
  toIsContinuousPairing := inferInstance
  surjective_eval g := ⟨g 1, ContinuousLinearMap.ext fun a => by
    rw [evalCLM_apply, mulPairing_apply]
    have h : g (a • (1 : ℝ)) = a • g 1 := map_smul g a 1
    rw [smul_eq_mul, mul_one] at h
    rw [h, smul_eq_mul]⟩

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The pairing under which epigraphs are polarised**: `⟨(x, ν), (y, μ)⟩ = ⟨x, y⟩ + ν μ`.

An `abbrev` so that the `prodPairing` instances of `Duality/Pairing.lean` remain visible to
instance search (a `def` would hide them — `LinearMap.flip` is the same trap). -/
abbrev epiPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (E × ℝ) →ₗ[ℝ] (F × ℝ) →ₗ[ℝ] ℝ :=
  prodPairing B mulPairing

@[simp] theorem epiPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (p : E × ℝ) (q : F × ℝ) :
    epiPairing B p q = B p.1 q.1 + p.2 * q.2 := rfl

theorem epiPairing_flip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (epiPairing B).flip = epiPairing B.flip := by
  rw [epiPairing, prodPairing_flip, mulPairing_flip]

/-- **Vertical reflection**: `(x, μ) ↦ (x, -μ)`. -/
def vNeg (X : Type*) [AddCommGroup X] [Module ℝ X] : (X × ℝ) →ₗ[ℝ] X × ℝ :=
  LinearMap.prodMap LinearMap.id (-LinearMap.id)

@[simp] theorem vNeg_apply (X : Type*) [AddCommGroup X] [Module ℝ X] (p : X × ℝ) :
    vNeg X p = (p.1, -p.2) := rfl

@[simp] theorem vNeg_vNeg (X : Type*) [AddCommGroup X] [Module ℝ X] (p : X × ℝ) :
    vNeg X (vNeg X p) = p := by
  simp

theorem image_vNeg_eq_preimage (X : Type*) [AddCommGroup X] [Module ℝ X] (S : Set (X × ℝ)) :
    vNeg X '' S = vNeg X ⁻¹' S := by
  ext p
  refine ⟨?_, fun hp => ⟨vNeg X p, hp, vNeg_vNeg X p⟩⟩
  rintro ⟨q, hq, rfl⟩
  simpa using hq

@[simp] theorem image_vNeg_image_vNeg (X : Type*) [AddCommGroup X] [Module ℝ X]
    (S : Set (X × ℝ)) : vNeg X '' (vNeg X '' S) = S := by
  rw [image_vNeg_eq_preimage, image_vNeg_eq_preimage]
  ext p
  simp

/-- **Polarity commutes with vertical reflection**: `(A S)° = A (S°)`, because `A` is self-adjoint
for `epiPairing`. -/
theorem polarSet_image_vNeg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (S : Set (E × ℝ)) :
    polarSet (epiPairing B) (vNeg E '' S) = vNeg F '' polarSet (epiPairing B) S := by
  rw [image_vNeg_eq_preimage F (polarSet (epiPairing B) S)]
  ext q
  simp only [Set.mem_preimage, mem_polarSet, Set.forall_mem_image, epiPairing_apply, vNeg_apply]
  exact forall₂_congr fun z _ => ⟨fun h => by linarith, fun h => by linarith⟩

end EpiPairing

/-! ### The polar of a nonnegative convex function

`f°(y) = inf {μ ≥ 0 | ⟨x, y⟩ ≤ 1 + μ f(x) for all x}`. The definition below is the `∞`-free reading
of that formula, quantifying over the epigraph of `f` rather than over `f` itself: `μ` is admissible
when `⟨x, y⟩ - ν μ ≤ 1` for every `(x, ν) ∈ epi f`. This says exactly that `(y, -μ)` lies in the
polar of `epi f`, which is what the classical proof uses, and `polarFn_apply_eq` shows it agrees
with the original formula. -/

section PolarFn

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {y : F} {μ : ℝ}

/-- **The polar of a nonnegative convex function vanishing at the origin**:
`f°(y) = inf {μ ≥ 0 | ⟨x, y⟩ ≤ 1 + μ f(x) for all x}`, in the epigraph form. -/
noncomputable def polarFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => ⨅ μ ∈ {μ : ℝ | ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1}, (μ : EReal)

def polarFnSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) : Set ℝ :=
  {μ : ℝ | ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1}

theorem polarFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    polarFn B f y = ⨅ μ ∈ polarFnSet B f y, (μ : EReal) := rfl

/-- The admissible-multiplier set is upward closed: the vertical coordinates of `epi f` are
nonnegative because `f` is. -/
theorem upClosed_polarFnSet (hnn : ∀ x, 0 ≤ f x) (y : F) : UpClosed (polarFnSet B f y) := by
  intro a ha b hab x ν hν
  have hν0 : (0 : ℝ) ≤ ν := by
    have := le_trans (hnn x) hν
    exact EReal.coe_nonneg.1 this
  have h := ha x ν hν
  nlinarith

/-- The admissible-multiplier set is closed: it is an intersection of closed half-lines. -/
theorem isClosed_polarFnSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) :
    IsClosed (polarFnSet B f y) := by
  have hrw : polarFnSet B f y =
      ⋂ x : E, ⋂ ν : ℝ, ⋂ _ : f x ≤ (ν : EReal), {μ : ℝ | B x y - ν * μ ≤ 1} := by
    ext μ
    simp [polarFnSet]
  rw [hrw]
  exact isClosed_iInter fun x => isClosed_iInter fun ν => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const

/-- **The defining inequality of `polarFn`.** -/
theorem polarFn_le_coe_iff (hnn : ∀ x, 0 ≤ f x) :
    polarFn B f y ≤ (μ : EReal) ↔ ∀ (x : E) (ν : ℝ), f x ≤ (ν : EReal) → B x y - ν * μ ≤ 1 :=
  biInf_coe_le_coe_iff (upClosed_polarFnSet hnn y) (isClosed_polarFnSet B f y) μ

theorem polarFn_nonneg (h0 : f 0 ≤ 0) (y : F) : 0 ≤ polarFn B f y := by
  refine zero_le_biInf_coe fun a ha => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hna : (0 : ℝ) < -a := by linarith
  have hb : ∀ ν : ℝ, 0 ≤ ν → ν * -a ≤ 1 := by
    intro ν hν
    have h0' : f 0 ≤ ((ν : ℝ) : EReal) := by
      refine le_trans h0 ?_
      rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
      exact hν
    have h := ha 0 ν h0'
    rw [map_zero, LinearMap.zero_apply] at h
    rw [mul_neg]
    linarith
  have hkey := hb (2 / -a) (div_nonneg (by norm_num) hna.le)
  rw [div_mul_cancel₀ (2 : ℝ) hna.ne'] at hkey
  linarith

/-- The polar of a function vanishes at the origin. -/
@[simp] theorem polarFn_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (h0 : f 0 ≤ 0) :
    polarFn B f 0 = 0 := by
  refine le_antisymm ?_ (polarFn_nonneg h0 0)
  have h : (0 : ℝ) ∈ polarFnSet B f 0 := by
    intro x ν _
    simp
  have h2 := iInf₂_le (f := fun (μ : ℝ) (_ : μ ∈ polarFnSet B f 0) => (μ : EReal)) (0 : ℝ) h
  rw [polarFn_apply, ← EReal.coe_zero]
  exact h2

/-- **The original formula for the polar**, recovered from the epigraph form: `f°(y)` is the
infimum of the `μ ≥ 0` with `⟨x, y⟩ ≤ 1 + μ f(x)` for every `x`.

The two admissible sets differ only at `μ = 0`, where the convention `0 · (+∞) = 0` imposes a
condition off `dom f` that the epigraph form does not; since both are up-sets in `[0, ∞)`, the
infima agree. -/
theorem polarFn_apply_eq (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) (y : F) :
    polarFn B f y =
      ⨅ μ ∈ {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ 1 + (μ : EReal) * f x},
        (μ : EReal) := by
  set T : Set ℝ := {μ : ℝ | 0 ≤ μ ∧ ∀ x : E, ((B x y : ℝ) : EReal) ≤ 1 + (μ : EReal) * f x}
    with hT
  have hTS : T ⊆ polarFnSet B f y := by
    intro μ hμ x ν hν
    have hν0 : (0 : ℝ) ≤ ν := EReal.coe_nonneg.1 (le_trans (hnn x) hν)
    have hle : (μ : EReal) * f x ≤ (μ : EReal) * (ν : EReal) :=
      mul_le_mul_of_nonneg_left hν (EReal.coe_nonneg.2 hμ.1)
    have := le_trans (hμ.2 x) (add_le_add (le_refl (1 : EReal)) hle)
    rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one],
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    nlinarith
  have hpos : ∀ μ : ℝ, 0 < μ → μ ∈ polarFnSet B f y → μ ∈ T := by
    intro μ hμ0 hμ
    refine ⟨hμ0.le, fun x => ?_⟩
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop, EReal.coe_mul_top_of_pos hμ0,
        show ((1 : EReal)) = ((1 : ℝ) : EReal) by rw [EReal.coe_one],
        EReal.coe_add_top]
      exact le_top
    obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hlt
    have := hμ x s (le_of_eq hs)
    rw [hs, ← EReal.coe_mul, show ((1 : EReal)) = ((1 : ℝ) : EReal) by
      rw [EReal.coe_one], ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  refine le_antisymm (le_iInf₂ fun μ hμ => iInf₂_le μ (hTS hμ)) ?_
  refine le_iInf₂ fun μ hμ => ?_
  have hμ0 : 0 ≤ μ := by
    have := polarFn_nonneg (B := B) h0 y
    exact EReal.coe_nonneg.1 (le_trans this (iInf₂_le μ hμ))
  rcases eq_or_lt_of_le hμ0 with hzero | hlt
  · rw [← hzero]
    refine le_coe_of_forall_gt_le fun d hd => ?_
    exact iInf₂_le d (hpos d hd (upClosed_polarFnSet hnn y hμ (by linarith)))
  · exact iInf₂_le μ (hpos μ hlt hμ)

end PolarFn

/-! ### Closures of nonnegative functions

A nonnegative function has a nonnegative lower semicontinuous hull, so the exceptional `⊥` branch
of `clFn` never fires and `cl f` is computed by the closure of the epigraph. -/

section NonnegClosure

variable {E : Type*} [TopologicalSpace E] {f : E → EReal}

/-- The closure of the epigraph of a nonnegative function stays in the upper half-space. -/
theorem nonneg_of_mem_closure_epi (hnn : ∀ x, 0 ≤ f x) {p : E × ℝ} (hp : p ∈ closure (epi f)) :
    0 ≤ p.2 := by
  refine closure_minimal (fun q hq => ?_) (isClosed_le continuous_const continuous_snd) hp
  have h : (0 : EReal) ≤ (q.2 : EReal) := le_trans (hnn q.1) hq
  exact_mod_cast h

theorem lscHull_nonneg (hnn : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ lscHull f x := by
  refine le_ofEpi fun μ hμ => ?_
  have h := nonneg_of_mem_closure_epi hnn hμ
  exact_mod_cast h

/-- For a nonnegative function the closure is the lower semicontinuous hull: the exceptional
branch of `clFn` cannot fire. -/
theorem clFn_eq_lscHull_of_nonneg (hnn : ∀ x, 0 ≤ f x) : clFn f = lscHull f :=
  clFn_of_forall_ne_bot fun x h => by
    have h0 := lscHull_nonneg hnn x
    rw [h, le_bot_iff] at h0
    exact absurd h0 (by simp)

theorem clFn_nonneg (hnn : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ clFn f x := by
  rw [clFn_eq_lscHull_of_nonneg hnn]
  exact lscHull_nonneg hnn x

/-- A nonnegative function with a closed epigraph is closed. -/
theorem closedFn_of_isClosed_epi (hnn : ∀ x, 0 ≤ f x) (hcl : IsClosed (epi f)) : ClosedFn f := by
  rw [ClosedFn, clFn_eq_lscHull_of_nonneg hnn]
  exact le_antisymm (lscHull_le f)
    (le_lscHull_of_le (lowerSemicontinuous_iff_isClosed_epi.2 hcl) le_rfl)

end NonnegClosure

section NonnegClosureGroup

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  {f : E → EReal}

/-- For a nonnegative function the epigraph of the closure is the closure of the epigraph. -/
theorem epi_clFn_of_nonneg (hnn : ∀ x, 0 ≤ f x) : epi (clFn f) = closure (epi f) := by
  rw [clFn_eq_lscHull_of_nonneg hnn, epi_lscHull]

/-- A nonnegative closed function has a closed epigraph. -/
theorem isClosed_epi_of_closedFn (hnn : ∀ x, 0 ≤ f x) (hcl : ClosedFn f) : IsClosed (epi f) := by
  have h : epi f = closure (epi f) := by rw [← epi_clFn_of_nonneg hnn, hcl]
  rw [h]
  exact isClosed_closure

/-- Closedness of a nonnegative function, as a statement about its epigraph. -/
theorem closedFn_iff_isClosed_epi (hnn : ∀ x, 0 ≤ f x) : ClosedFn f ↔ IsClosed (epi f) :=
  ⟨isClosed_epi_of_closedFn hnn, closedFn_of_isClosed_epi hnn⟩

end NonnegClosureGroup

/-! ### The bipolar of a function

The epigraph of `f°` is the vertical reflection of the polar of the epigraph of `f`, so the
bipolar theorem of `Duality/Polar.lean`, applied in `E × ℝ`, gives `f°° = cl f` at once. -/

section PolarEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- **The epigraph of the polar**: `epi f° = A ((epi f)°)`, where `A` is the vertical reflection
`vNeg`. -/
theorem epi_polarFn (hnn : ∀ x, 0 ≤ f x) :
    epi (polarFn B f) = vNeg F '' polarSet (epiPairing B) (epi f) := by
  rw [image_vNeg_eq_preimage]
  ext q
  simp only [Set.mem_preimage, mem_epi, mem_polarSet, vNeg_apply, epiPairing_apply,
    polarFn_le_coe_iff hnn]
  constructor
  · rintro h ⟨x, ν⟩ hp
    have h2 := h x ν hp
    simp only
    linarith
  · intro h x ν hν
    have h2 := h (x, ν) hν
    simp only at h2
    linarith

/-- The polar of a nonnegative function is convex, being cut out by a polar set. -/
theorem convexFn_polarFn (hnn : ∀ x, 0 ≤ f x) : ConvexFn (polarFn B f) := by
  rw [convexFn_iff_convex_epi, epi_polarFn hnn, image_vNeg_eq_preimage]
  exact (convex_polarSet _ _).linear_preimage (vNeg F)

end PolarEpi

section PolarClosed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

/-- The polar of a nonnegative function vanishing at the origin is closed, because polar sets are
closed. -/
theorem closedFn_polarFn (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) : ClosedFn (polarFn B f) := by
  have : IsContinuousPairing (epiPairing B).flip := by
    rw [epiPairing_flip]
    infer_instance
  refine closedFn_of_isClosed_epi (fun y => polarFn_nonneg h0 y) ?_
  rw [epi_polarFn hnn, image_vNeg_eq_preimage]
  have hc : Continuous fun p : F × ℝ => ((p.1, -p.2) : F × ℝ) :=
    continuous_fst.prodMk continuous_snd.neg
  exact isClosed_polarSet.preimage hc

end PolarClosed

section BipolarFn

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The bipolar is the closure**: for a nonnegative convex function vanishing at the origin,
`f°° = cl f`.

The outer polar is taken with respect to `B.flip`, since `f°` lives on `F`. -/
theorem polarFn_polarFn (hconv : ConvexFn f) (hnn : ∀ x, 0 ≤ f x) (h0 : f 0 ≤ 0) :
    polarFn B.flip (polarFn B f) = clFn f := by
  have hnn' : ∀ y, 0 ≤ polarFn B f y := fun y => polarFn_nonneg h0 y
  have hmem : (0 : E × ℝ) ∈ closure (epi f) := by
    refine subset_closure ?_
    rw [mem_epi]
    simpa using h0
  have hepi : epi (polarFn B.flip (polarFn B f)) = closure (epi f) := by
    rw [epi_polarFn hnn', epi_polarFn hnn, polarSet_image_vNeg B.flip, image_vNeg_image_vNeg,
      ← epiPairing_flip B, ← polarSet_closure (B := epiPairing B) (epi f)]
    exact polarSet_polarSet hconv.convex_epi.closure isClosed_closure hmem
  have hof := congrArg ofEpi hepi
  rwa [ofEpi_epi, ← epi_clFn_of_nonneg hnn, ofEpi_epi] at hof

end BipolarFn

/-! ### The class on which the polar is an involution

The nonnegative closed convex functions that vanish at the origin. -/

section PolarClass

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {f : E → EReal}

/-- **The nonnegative closed convex functions vanishing at the origin.** These are exactly the
functions that arise as polars (`isPolarFn_polarFn` and `polarFn_polarFn`), and `f ↦ f°` is an
involution on them. -/
structure IsPolarFn (f : E → EReal) : Prop where
  /-- A polar is nonnegative. -/
  nonneg : ∀ x, 0 ≤ f x
  /-- A polar vanishes at the origin. -/
  map_zero : f 0 = 0
  /-- A polar is convex. -/
  convexFn : ConvexFn f
  /-- A polar is closed. -/
  closedFn : ClosedFn f

theorem IsPolarFn.map_zero_le (h : IsPolarFn f) : f 0 ≤ 0 := le_of_eq h.map_zero

/-- A closed gauge is an `IsPolarFn`. -/
theorem IsGauge.isPolarFn (h : IsGauge f) (hcl : ClosedFn f) : IsPolarFn f :=
  ⟨h.nonneg, h.map_zero, h.convexFn, hcl⟩

end PolarClass

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip]
  {f : E → EReal}

/-- **The polar of an `IsPolarFn` is again one**: the four conditions are inherited. -/
theorem isPolarFn_polarFn (h : IsPolarFn f) : IsPolarFn (polarFn B f) where
  nonneg y := polarFn_nonneg h.map_zero_le y
  map_zero := polarFn_zero B f h.map_zero_le
  convexFn := convexFn_polarFn h.nonneg
  closedFn := closedFn_polarFn h.nonneg h.map_zero_le

end

section PolarInvolution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- **`f ↦ f°` is a symmetric one-to-one correspondence** on the nonnegative closed convex
functions vanishing at the origin. -/
noncomputable def polarFnEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {f : E → EReal // IsPolarFn f} ≃ {g : F → EReal // IsPolarFn g} where
  toFun f := ⟨polarFn B f.1, isPolarFn_polarFn f.2⟩
  invFun g := ⟨polarFn B.flip g.1, isPolarFn_polarFn g.2⟩
  left_inv f := Subtype.ext <| by
    change polarFn B.flip (polarFn B f.1) = f.1
    rw [polarFn_polarFn f.2.convexFn f.2.nonneg f.2.map_zero_le]
    exact f.2.closedFn
  right_inv g := Subtype.ext <| by
    change polarFn B (polarFn B.flip g.1) = g.1
    have h := polarFn_polarFn (B := B.flip) g.2.convexFn g.2.nonneg g.2.map_zero_le
    rw [LinearMap.flip_flip] at h
    rw [h]
    exact g.2.closedFn

end PolarInvolution

/-! ### The involution `k°° = cl k`

The book derives this from polarity of the unit level set. Here it is a special case of
`polarFn_polarFn` instead: on a gauge the two polar operations agree (`polarFn_eq_polarGauge`),
because the `1 +` in the definition of `f°` is invisible to a positively homogeneous function. -/

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {k : E → EReal}

/-- **The two polar operations agree on gauges**: the `1 +` in the definition of `f°` is invisible
to a positively homogeneous `f`.

The admissible set of `polarGauge` is contained in that of `polarFn`, and the two differ at most
at `0`; since both are up-sets in `[0, ∞)`, the infima agree. -/
theorem polarFn_eq_polarGauge (hnn : ∀ x, 0 ≤ k x) (hph : PosHomogeneous k) (h0 : k 0 = 0) :
    polarFn B k = polarGauge B k := by
  funext y
  refine le_antisymm ?_ ?_
  · rw [polarGauge_apply]
    refine le_iInf₂ fun μ hμ => ?_
    refine (polarFn_le_coe_iff hnn).2 fun x ν hν => ?_
    have h1 : ((B x y : ℝ) : EReal) ≤ ((μ * ν : ℝ) : EReal) := by
      refine le_trans (hμ.2 x) ?_
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hν (EReal.coe_nonneg.2 hμ.1)
    rw [EReal.coe_le_coe_iff] at h1
    linarith [mul_comm μ ν]
  · rw [polarFn_apply]
    refine le_iInf₂ fun μ hμ => ?_
    have hμ0 : (0 : ℝ) ≤ μ := by
      have hle : polarFn B k y ≤ (μ : EReal) :=
        iInf₂_le (f := fun (μ : ℝ) (_ : μ ∈ polarFnSet B k y) => (μ : EReal)) μ hμ
      exact EReal.coe_nonneg.1 (le_trans (polarFn_nonneg (le_of_eq h0) y) hle)
    refine le_coe_of_forall_gt_le fun d hd => ?_
    have hd0 : (0 : ℝ) < d := lt_of_le_of_lt hμ0 hd
    have hdmem : d ∈ polarFnSet B k y := upClosed_polarFnSet hnn y hμ hd.le
    refine polarGauge_le_of_forall hd0.le fun x => ?_
    rcases eq_or_lt_of_le (le_top (a := k x)) with htopx | hltx
    · rw [htopx, EReal.coe_mul_top_of_pos hd0]
      exact le_top
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (fun h => by simpa [h] using hnn x) hltx
    rw [hc, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    by_contra hcon
    rw [not_le] at hcon
    have ha0 : (0 : ℝ) < B x y - d * c := by linarith
    have ht : (0 : ℝ) < 2 / (B x y - d * c) := by positivity
    have hkt : k ((2 / (B x y - d * c)) • x) ≤ (((2 / (B x y - d * c)) * c : ℝ) : EReal) :=
      le_of_eq (by rw [hph _ ht x, hc, ← EReal.coe_mul])
    have hb := hdmem _ _ hkt
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
    have hexp : 2 / (B x y - d * c) * B x y - 2 / (B x y - d * c) * c * d
        = 2 / (B x y - d * c) * (B x y - d * c) := by ring
    rw [hexp, div_mul_cancel₀ (2 : ℝ) ha0.ne'] at hb
    linarith

end

section GaugeInvolution

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {k : E → EReal}

/-- **`k°° = cl k`** for a gauge `k`. -/
theorem polarGauge_polarGauge (hk : IsGauge k) :
    polarGauge B.flip (polarGauge B k) = clFn k := by
  have hpk : IsGauge (polarGauge B k) := isGauge_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero
  rw [← polarFn_eq_polarGauge hpk.nonneg hpk.posHomogeneous hpk.map_zero,
    ← polarFn_eq_polarGauge hk.nonneg hk.posHomogeneous hk.map_zero]
  exact polarFn_polarFn hk.convexFn hk.nonneg (le_of_eq hk.map_zero)

end GaugeInvolution

/-! ### Polarity as a correspondence, for gauges and for sets -/

section GaugeCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- **`k ↦ k°` is a symmetric one-to-one correspondence on the closed gauges.** -/
noncomputable def polarGaugeEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {k : E → EReal // IsGauge k ∧ ClosedFn k} ≃ {j : F → EReal // IsGauge j ∧ ClosedFn j} where
  toFun k := ⟨polarGauge B k.1,
    isGauge_polarGauge k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero,
    closedFn_polarGauge k.2.1.nonneg k.2.1.posHomogeneous k.2.1.map_zero⟩
  invFun j := ⟨polarGauge B.flip j.1,
    isGauge_polarGauge j.2.1.nonneg j.2.1.posHomogeneous j.2.1.map_zero,
    closedFn_polarGauge j.2.1.nonneg j.2.1.posHomogeneous j.2.1.map_zero⟩
  left_inv k := Subtype.ext <| by
    change polarGauge B.flip (polarGauge B k.1) = k.1
    rw [polarGauge_polarGauge k.2.1]
    exact k.2.2
  right_inv j := Subtype.ext <| by
    change polarGauge B (polarGauge B.flip j.1) = j.1
    have h := polarGauge_polarGauge (B := B.flip) j.2.1
    rw [LinearMap.flip_flip] at h
    rw [h]
    exact j.2.2

end GaugeCorrespondence

section SetCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [ContinuousSMul ℝ F]

/-- **Two closed convex sets containing the origin are polar to each other exactly when their
gauges are.** -/
theorem polarSet_eq_iff_polarGauge_gaugeFn_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    [IsContinuousPairing B.flip] {C : Set E} {D : Set F}
    (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hD : Convex ℝ D) (hDcl : IsClosed D)
    (hD0 : (0 : F) ∈ D) :
    polarSet B C = D ↔ polarGauge B (gaugeFn C) = gaugeFn D := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have hpc : {y : F | gaugeFn (polarSet B C) y ≤ 1} = {y : F | gaugeFn D y ≤ 1} := by rw [h]
  rwa [setOf_gaugeFn_le_one (convex_polarSet B C) (fun x _ => by simp) isClosed_polarSet,
    setOf_gaugeFn_le_one hD hD0 hDcl] at hpc

end SetCorrespondence

/-! ### The obverse

`g(x) = inf {λ > 0 | (fλ)(x) ≤ 1}`. The observation that replaces the geometric argument of the
book is that this is a **gauge value one dimension higher**: `g(x) = γ((x, 1) | epi f)`. Everything
about the obverse then follows from the gauge API. -/

section Obverse

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {a : ℝ}

theorem mk_mem_smul_epi_iff (ha : 0 < a) (f : E → EReal) (x : E) (r : ℝ) :
    (x, r) ∈ a • epi f ↔ f (a⁻¹ • x) ≤ ((a⁻¹ * r : ℝ) : EReal) := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  exact Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
theorem mk_one_mem_epi_iff (f : E → EReal) (x : E) : (x, (1 : ℝ)) ∈ epi f ↔ f x ≤ 1 := by
  rw [mem_epi]
  exact_mod_cast Iff.rfl

/-- **The obverse of `f`**, Rockafellar's term: `g(x) = inf {λ > 0 | (fλ)(x) ≤ 1}`. -/
noncomputable def obverse (f : E → EReal) : E → EReal :=
  fun x => ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal)

theorem obverse_apply (f : E → EReal) (x : E) :
    obverse f x = ⨅ l ∈ {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1}, (l : EReal) := rfl

/-- The admissible set of the obverse is the admissible set of the gauge of `epi f` at height one:
the scalar `0` is never admissible, because `(x, 1) ∉ 0 • S`. -/
theorem obverseSet_eq (f : E → EReal) (x : E) :
    {l : ℝ | 0 < l ∧ smulRight f l x ≤ 1} = {a : ℝ | 0 ≤ a ∧ (x, (1 : ℝ)) ∈ a • epi f} := by
  ext l
  constructor
  · rintro ⟨hl, hle⟩
    exact ⟨hl.le, by rw [← epi_smulRight hl]; exact (mk_one_mem_epi_iff _ x).2 hle⟩
  · rintro ⟨hl0, hmem⟩
    rcases eq_or_lt_of_le hl0 with hzero | hl
    · exfalso
      obtain ⟨p, -, hp⟩ := hmem
      rw [← hzero] at hp
      simpa using congrArg Prod.snd hp
    · exact ⟨hl, (mk_one_mem_epi_iff _ x).1 (by rw [← epi_smulRight hl] at hmem; exact hmem)⟩

/-- **The obverse is a gauge value one dimension up**: `g(x) = γ((x, 1) | epi f)`. -/
theorem obverse_eq_gaugeFn (f : E → EReal) (x : E) :
    obverse f x = gaugeFn (epi f) (x, (1 : ℝ)) := by
  rw [obverse_apply, gaugeFn_apply, obverseSet_eq]

/-- The epigraph of the obverse is a slice of the epigraph of the gauge of `epi f`. -/
theorem epi_obverse (f : E → EReal) :
    epi (obverse f) = (fun p : E × ℝ => ((p.1, (1 : ℝ)), p.2)) ⁻¹' epi (gaugeFn (epi f)) := by
  ext p
  simp only [Set.mem_preimage, mem_epi, obverse_eq_gaugeFn]

theorem obverse_nonneg (f : E → EReal) (x : E) : 0 ≤ obverse f x := by
  rw [obverse_eq_gaugeFn]
  exact gaugeFn_nonneg _ _

theorem obverse_ne_bot (f : E → EReal) (x : E) : obverse f x ≠ ⊥ := by
  rw [obverse_eq_gaugeFn]
  exact gaugeFn_ne_bot _ _

end Obverse

/-! ### Two `EReal` lemmas used for the obverse -/

section ErealAux

theorem biInf_coe_pos_ge_eq {z : EReal} (hz : 0 ≤ z) :
    (⨅ ν ∈ {ν : ℝ | 0 < ν ∧ z ≤ (ν : EReal)}, (ν : EReal)) = z := by
  refine le_antisymm ?_ (le_iInf₂ fun ν hν => hν.2)
  rcases eq_or_lt_of_le (le_top (a := z)) with htop | hlt
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (fun hb => by simp [hb] at hz) hlt
  have hr0 : (0 : ℝ) ≤ r := by rw [hr] at hz; exact EReal.coe_nonneg.1 hz
  refine le_of_le_of_eq (le_coe_of_forall_gt_le fun d hd => ?_) hr.symm
  refine iInf₂_le (f := fun (ν : ℝ) (_ : ν ∈ {ν : ℝ | 0 < ν ∧ z ≤ (ν : EReal)}) => (ν : EReal))
    d ⟨lt_of_le_of_lt hr0 hd, ?_⟩
  rw [hr]
  exact_mod_cast hd.le

theorem eq_of_forall_pos_le_iff {A B : EReal} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ ν : ℝ, 0 < ν → (A ≤ (ν : EReal) ↔ B ≤ (ν : EReal))) : A = B := by
  refine le_antisymm ?_ ?_
  · by_contra hcon
    obtain ⟨ν, hBν, hνA⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hν0 : (0 : ℝ) < ν := by
      have hlt : (0 : EReal) < (ν : EReal) := lt_of_le_of_lt hB hBν
      rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hlt
      exact hlt
    exact absurd ((h ν hν0).2 hBν.le) (not_le.2 hνA)
  · by_contra hcon
    obtain ⟨ν, hAν, hνB⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hcon)
    have hν0 : (0 : ℝ) < ν := by
      have hlt : (0 : EReal) < (ν : EReal) := lt_of_le_of_lt hA hAν
      rw [← EReal.coe_zero, EReal.coe_lt_coe_iff] at hlt
      exact hlt
    exact absurd ((h ν hν0).1 hAν.le) (not_le.2 hνB)

end ErealAux

/-! ### The obverse of a nonnegative closed convex function -/

section ObverseClosed

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup E] {f : E → EReal} {ν : ℝ}

omit [ContinuousSMul ℝ E] in
/-- The epigraph of an `IsPolarFn` is convex, closed, and contains the origin — the hypotheses of
the closed gauge theory. -/
theorem IsPolarFn.epi_closed_convex_zero (h : IsPolarFn f) :
    Convex ℝ (epi f) ∧ IsClosed (epi f) ∧ (0 : E × ℝ) ∈ epi f :=
  ⟨h.convexFn.convex_epi, isClosed_epi_of_closedFn h.nonneg h.closedFn, by
    rw [mem_epi]; simpa using h.map_zero.le⟩

/-- **The defining inequality of the obverse**, for an `IsPolarFn`: `g(x) ≤ ν` exactly when
`(fν)(x) ≤ 1`, for `ν > 0`. -/
theorem obverse_le_coe_iff (h : IsPolarFn f) (hν : 0 < ν) (z : E) :
    obverse f z ≤ (ν : EReal) ↔ f (ν⁻¹ • z) ≤ ((ν⁻¹ : ℝ) : EReal) := by
  obtain ⟨hC, hCcl, hC0⟩ := h.epi_closed_convex_zero
  rw [obverse_eq_gaugeFn, gaugeFn_le_coe_iff hC hC0 hCcl hν, mk_mem_smul_epi_iff hν, mul_one]

/-- The obverse vanishes at the origin. -/
@[simp] theorem obverse_zero (h : IsPolarFn f) : obverse f 0 = 0 := by
  refine le_antisymm (le_coe_of_forall_gt_le fun d hd => ?_) (obverse_nonneg f 0)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [obverse_le_coe_iff h hd0, smul_zero, h.map_zero]
  exact_mod_cast le_of_lt (inv_pos.2 hd0)

omit [ContinuousSMul ℝ E] [IsTopologicalAddGroup E] in
theorem convexFn_obverse (h : IsPolarFn f) : ConvexFn (obverse f) := by
  have hk : ConvexFn (gaugeFn (epi f)) := convexFn_gaugeFn h.convexFn.convex_epi
  refine convexFn_iff_convex_epi.2 fun p hp q hq s t hs ht hst => ?_
  rw [mem_epi, obverse_eq_gaugeFn] at hp hq ⊢
  have hcomb := hk.convex_epi (show ((p.1, (1 : ℝ)), p.2) ∈ epi (gaugeFn (epi f)) from hp)
    (show ((q.1, (1 : ℝ)), q.2) ∈ epi (gaugeFn (epi f)) from hq) hs ht hst
  have hkey : s • (((p.1, (1 : ℝ))), p.2) + t • (((q.1, (1 : ℝ))), q.2)
      = ((((s • p + t • q).1, (1 : ℝ))), (s • p + t • q).2) := by
    simp [hst]
  rw [hkey] at hcomb
  exact hcomb

theorem closedFn_obverse (h : IsPolarFn f) : ClosedFn (obverse f) := by
  obtain ⟨hC, hCcl, hC0⟩ := h.epi_closed_convex_zero
  refine closedFn_of_isClosed_epi (obverse_nonneg f) ?_
  rw [epi_obverse]
  refine IsClosed.preimage ?_
    (isClosed_epi_of_closedFn (gaugeFn_nonneg _) (closedFn_gaugeFn hC hC0 hCcl))
  exact (continuous_fst.prodMk continuous_const).prodMk continuous_snd

/-- The obverse of a nonnegative closed convex function vanishing at the origin is another one. -/
theorem isPolarFn_obverse (h : IsPolarFn f) : IsPolarFn (obverse f) where
  nonneg := obverse_nonneg f
  map_zero := obverse_zero h
  convexFn := convexFn_obverse h
  closedFn := closedFn_obverse h

/-- **The obverse is an involution**: `f` is the obverse of its obverse. -/
theorem obverse_obverse (h : IsPolarFn f) : obverse (obverse f) = f := by
  funext z
  rw [obverse_apply, obverseSet_eq]
  have hset : {a : ℝ | 0 ≤ a ∧ (z, (1 : ℝ)) ∈ a • epi (obverse f)}
      = {a : ℝ | 0 < a ∧ f z ≤ (a : EReal)} := by
    ext a
    constructor
    · rintro ⟨ha0, hmem⟩
      rcases eq_or_lt_of_le ha0 with hzero | ha
      · exfalso
        obtain ⟨p, -, hp⟩ := hmem
        rw [← hzero] at hp
        simpa using congrArg Prod.snd hp
      refine ⟨ha, ?_⟩
      rw [mk_mem_smul_epi_iff ha, mul_one, obverse_le_coe_iff h (inv_pos.2 ha), inv_inv,
        smul_inv_smul₀ ha.ne'] at hmem
      exact hmem
    · rintro ⟨ha, hle⟩
      refine ⟨ha.le, ?_⟩
      rw [mk_mem_smul_epi_iff ha, mul_one, obverse_le_coe_iff h (inv_pos.2 ha), inv_inv,
        smul_inv_smul₀ ha.ne']
      exact hle
  rw [hset]
  exact biInf_coe_pos_ge_eq (h.nonneg z)

end ObverseClosed

/-! ### The polar, the conjugate and the obverse

The book obtains these from the symmetry of a closed convex cone in `R^(n+2)` under exchanging two
coordinates. Here the single computation `f* = (f°)ᵒ` (`conj_eq_obverse_polarFn`) does the work: it
is a level-set comparison, and everything else follows from it together with `obverse_obverse` and
`polarFn_polarFn`. -/

section ConjEpi

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {y : F}

/-- `f*(y) ≤ ν` read off the epigraph of `f`: the `⊤` value of `f` imposes no condition. -/
theorem conj_le_coe_iff_epi (hnn : ∀ x, 0 ≤ f x) {ν : ℝ} :
    conj B f y ≤ (ν : EReal) ↔ ∀ (x : E) (α : ℝ), f x ≤ (α : EReal) → B x y - α ≤ ν := by
  rw [conj_apply, iSup_le_iff]
  constructor
  · intro h x α hα
    have h2 : ((B x y : ℝ) : EReal) - (α : EReal) ≤ ((B x y : ℝ) : EReal) - f x :=
      EReal.sub_le_sub le_rfl hα
    have h3 := le_trans h2 (h x)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h3
    exact h3
  · intro h x
    rcases eq_or_lt_of_le (le_top (a := f x)) with htop | hlt
    · rw [htop, EReal.sub_top]
      exact bot_le
    obtain ⟨c, hc⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (fun hb => by simpa [hb] using hnn x) hlt
    rw [hc, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact h x c (le_of_eq hc)

end ConjEpi

section ConjPolarClass

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsContinuousPairing B.flip] {f : E → EReal}

/-- The conjugate of an `IsPolarFn` is again one: nonnegativity, vanishing at the origin,
convexity and closedness are all apparent from the definition of `f*`. -/
theorem isPolarFn_conj (h : IsPolarFn f) : IsPolarFn (conj B f) where
  nonneg := zero_le_conj h.map_zero.le
  map_zero := conj_zero_eq_zero h.nonneg h.map_zero.le
  convexFn := convexFn_conj B f
  closedFn := closedFn_conj

end ConjPolarClass

section ObverseFormula

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F]
  [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] [IsTopologicalAddGroup F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {f : E → EReal}

/-- **The conjugate is the obverse of the polar**: `f* = (f°)ᵒ`.

Both sides are nonnegative, so it suffices to compare them against the positive reals, and there
the statement unwinds to `⟨x, y⟩ - α ≤ ν` for every `(x, α) ∈ epi f`. -/
theorem conj_eq_obverse_polarFn (h : IsPolarFn f) : conj B f = obverse (polarFn B f) := by
  funext y
  refine eq_of_forall_pos_le_iff (zero_le_conj h.map_zero.le y) (obverse_nonneg _ y) fun ν hν => ?_
  rw [obverse_le_coe_iff (isPolarFn_polarFn h) hν, polarFn_le_coe_iff h.nonneg,
    conj_le_coe_iff_epi h.nonneg]
  refine forall_congr' fun x => forall_congr' fun α => imp_congr_right fun _ => ?_
  rw [map_smul, smul_eq_mul]
  have hrw : ν⁻¹ * B x y - α * ν⁻¹ = ν⁻¹ * (B x y - α) := by ring
  rw [hrw, inv_mul_le_iff₀ hν, mul_one]

/-- **The polar is the obverse of the conjugate**: `f° = (f*)ᵒ`. Together with
`conj_eq_obverse_polarFn`, `f°` and `f*` are the obverses of each other. -/
theorem polarFn_eq_obverse_conj (h : IsPolarFn f) : polarFn B f = obverse (conj B f) := by
  rw [conj_eq_obverse_polarFn h, obverse_obverse (isPolarFn_polarFn h)]

end ObverseFormula

section PolarConjObverse

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- **The obverse of `f` is `f*°`**, the expression from which the book derives the formula
`g(x) = inf {λ > 0 | (fλ)(x) ≤ 1}`. -/
theorem obverse_eq_polarFn_conj (h : IsPolarFn f) :
    obverse f = polarFn B.flip (conj B f) := by
  rw [polarFn_eq_obverse_conj (B := B.flip) (isPolarFn_conj (B := B) h)]
  have h2 : conj B.flip (conj B f) = f := by
    change biconj B f = f
    rw [biconj_eq_clFn h.convexFn]
    exact h.closedFn
  rw [h2]

/-- `g° = f*`, where `g` is the obverse of `f`. -/
theorem polarFn_obverse (h : IsPolarFn f) : polarFn B (obverse f) = conj B f := by
  have hc : IsPolarFn (conj B f) := isPolarFn_conj (B := B) h
  rw [obverse_eq_polarFn_conj (B := B) h]
  have h3 := polarFn_polarFn (B := B.flip) hc.convexFn hc.nonneg hc.map_zero_le
  rw [LinearMap.flip_flip] at h3
  rw [h3]
  exact hc.closedFn

/-- `f° = g*`, where `g` is the obverse of `f`. -/
theorem conj_obverse (h : IsPolarFn f) : conj B (obverse f) = polarFn B f := by
  rw [conj_eq_obverse_polarFn (isPolarFn_obverse h), polarFn_obverse (B := B) h,
    ← polarFn_eq_obverse_conj (B := B) h]

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- **The polar and the conjugate commute**: `f*° = f°*`. -/
theorem polarFn_conj_eq_conj_polarFn (h : IsPolarFn f) :
    polarFn B.flip (conj B f) = conj B.flip (polarFn B f) := by
  rw [← obverse_eq_polarFn_conj (B := B) h,
    conj_eq_obverse_polarFn (B := B.flip) (isPolarFn_polarFn (B := B) h),
    polarFn_polarFn h.convexFn h.nonneg h.map_zero_le, h.closedFn]

omit [LocallyConvexSpace ℝ E] in
/-- **The level sets of the obverse**: `{g ≤ α} = α {f ≤ α⁻¹}` for `α > 0`. -/
theorem setOf_obverse_le (h : IsPolarFn f) {α : ℝ} (hα : 0 < α) :
    {x : E | obverse f x ≤ (α : EReal)} = α • {x : E | f x ≤ ((α⁻¹ : ℝ) : EReal)} := by
  ext z
  rw [Set.mem_ofPred_eq, obverse_le_coe_iff h hα, mem_smul_set_iff_inv_smul_mem₀ hα.ne']
  exact Iff.rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [LocallyConvexSpace ℝ F] [IsCompatiblePairing B] in
/-- **The level sets of the polar and of the conjugate**: `{f° ≤ α⁻¹} = α⁻¹ {f* ≤ α}` for
`α > 0`. This is the middle set of `polarSet_setOf_le_subset_and_subset`. -/
theorem setOf_polarFn_le (h : IsPolarFn f) {α : ℝ} (hα : 0 < α) :
    {y : F | polarFn B f y ≤ ((α⁻¹ : ℝ) : EReal)}
      = α⁻¹ • {y : F | conj B f y ≤ (α : EReal)} := by
  rw [polarFn_eq_obverse_conj (B := B) h,
    setOf_obverse_le (isPolarFn_conj (B := B) h) (inv_pos.2 hα), inv_inv]

end PolarConjObverse

/-! ### Norms

A gauge that is finite everywhere, symmetric, and positive away from the origin is a **norm**. The
book states the correspondence with the *symmetric closed bounded convex sets `C` with
`0 ∈ int C`*. Two of those three conditions on `C` are the finite-dimensional readings of conditions
that make sense in general, and it is the general readings that are proved here:

* "`0 ∈ int C`", which in `Rⁿ` says that `C` contains a positive multiple of every vector, is
  `AbsorbsAll C`;
* "`C` is bounded", which in `Rⁿ` says that `C` contains no half-line, is `RayFree C`.

Closedness is *not* part of the correspondence here. The book gets it from the continuity of a
finite convex function on `Rⁿ`, which is genuinely finite-dimensional; in an infinite-dimensional
space a finite symmetric positive gauge need not be lower semicontinuous. -/

section Norm

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E} {k : E → EReal}

/-- `C` **absorbs every point**: every `x` lies in some nonnegative dilate of `C`. This is the
elementary form in which absorbency enters the gauge; `absorbsAll_of_absorbent` relates it to
Mathlib's `Absorbent`. -/
def AbsorbsAll (C : Set E) : Prop := ∀ x : E, ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C

/-- `C` **contains no ray**: for every `x ≠ 0` some positive multiple of `x` is outside `C`. -/
def RayFree (C : Set E) : Prop := ∀ x : E, x ≠ 0 → ∃ l : ℝ, 0 < l ∧ l • x ∉ C

/-- **A norm** in Rockafellar's sense: a gauge that is finite everywhere, symmetric, and positive
away from the origin. -/
structure IsNorm (k : E → EReal) : Prop extends IsGauge k where
  /-- A norm is finite. -/
  ne_top : ∀ x, k x ≠ ⊤
  /-- A norm is symmetric. -/
  map_neg : ∀ x, k (-x) = k x
  /-- A norm is positive away from the origin. -/
  pos : ∀ x, x ≠ 0 → 0 < k x

theorem gaugeFn_neg_set (C : Set E) (x : E) : gaugeFn (-C) x = gaugeFn C (-x) := by
  have hset : {a : ℝ | 0 ≤ a ∧ x ∈ a • (-C)} = {a : ℝ | 0 ≤ a ∧ -x ∈ a • C} := by
    ext a
    simp only [Set.mem_ofPred, Set.smul_set_neg, Set.mem_neg]
  rw [gaugeFn_apply, gaugeFn_apply, hset]

theorem gaugeFn_map_neg (hsymm : -C = C) (x : E) : gaugeFn C (-x) = gaugeFn C x := by
  rw [← gaugeFn_neg_set, hsymm]

/-- The gauge is finite at `x` exactly when some dilate of `C` contains `x`. -/
theorem gaugeFn_ne_top_iff (C : Set E) (x : E) :
    gaugeFn C x ≠ ⊤ ↔ ∃ a : ℝ, 0 ≤ a ∧ x ∈ a • C := by
  rw [← lt_top_iff_ne_top, gaugeFn_lt_iff]
  constructor
  · rintro ⟨a, ha0, hmem, -⟩
    exact ⟨a, ha0, hmem⟩
  · rintro ⟨a, ha0, hmem⟩
    exact ⟨a, ha0, hmem, EReal.coe_lt_top a⟩

/-- **The gauge vanishes exactly on the rays inside `C`.** -/
theorem gaugeFn_eq_zero_iff (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (x : E) :
    gaugeFn C x = 0 ↔ ∀ l : ℝ, 0 < l → l • x ∈ C := by
  constructor
  · intro h l hl
    have hle : gaugeFn C x ≤ ((0 : ℝ) : EReal) := by rw [h, EReal.coe_zero]
    rw [gaugeFn_le_coe_iff_forall_lt hC h0 le_rfl] at hle
    have hmem := hle l⁻¹ (inv_pos.2 hl)
    rwa [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne') C x, inv_inv] at hmem
  · intro h
    refine le_antisymm ?_ (gaugeFn_nonneg C x)
    rw [← EReal.coe_zero, gaugeFn_le_coe_iff_forall_lt hC h0 le_rfl]
    intro d hd
    rw [mem_smul_set_iff_inv_smul_mem₀ hd.ne' C x]
    exact h d⁻¹ (inv_pos.2 hd)

/-- The gauge of a symmetric convex set that absorbs every point and contains no ray is a
norm. -/
theorem isNorm_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hsymm : -C = C)
    (habs : AbsorbsAll C) (hray : RayFree C) : IsNorm (gaugeFn C) where
  toIsGauge := isGauge_gaugeFn hC ⟨0, h0⟩
  ne_top x := (gaugeFn_ne_top_iff C x).2 (habs x)
  map_neg x := gaugeFn_map_neg hsymm x
  pos x hx := by
    refine lt_of_le_of_ne (gaugeFn_nonneg C x) fun hcon => ?_
    obtain ⟨l, hl, hlx⟩ := hray x hx
    exact hlx (((gaugeFn_eq_zero_iff hC h0 x).1 hcon.symm) l hl)

/-- The unit level set of a norm is a symmetric convex set that absorbs every point and contains
no ray. -/
theorem IsNorm.level_one (hk : IsNorm k) :
    Convex ℝ {x : E | k x ≤ 1} ∧ (0 : E) ∈ {x : E | k x ≤ 1} ∧ -{x : E | k x ≤ 1} =
      {x : E | k x ≤ 1} ∧ AbsorbsAll {x : E | k x ≤ 1} ∧ RayFree {x : E | k x ≤ 1} := by
  refine ⟨hk.toIsGauge.convex_level_one, hk.toIsGauge.zero_mem_level_one, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_neg, Set.mem_ofPred, hk.map_neg]
  · intro x
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hk.toIsGauge.ne_bot x)
      (lt_top_iff_ne_top.2 (hk.ne_top x))
    have hc0 : (0 : ℝ) ≤ c := by
      have := hk.nonneg x; rw [hc] at this; exact EReal.coe_nonneg.1 this
    refine ⟨max c 1, le_trans zero_le_one (le_max_right c 1), ?_⟩
    have hmax : (0 : ℝ) < max c 1 := lt_of_lt_of_le zero_lt_one (le_max_right c 1)
    rw [mem_smul_set_iff_inv_smul_mem₀ hmax.ne']
    change k ((max c 1)⁻¹ • x) ≤ 1
    rw [hk.posHomogeneous _ (inv_pos.2 hmax) x, hc, ← EReal.coe_one,
      ← EReal.coe_mul, EReal.coe_le_coe_iff, inv_mul_le_iff₀ hmax, mul_one]
    exact le_max_left c 1
  · intro x hx
    obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hk.toIsGauge.ne_bot x)
      (lt_top_iff_ne_top.2 (hk.ne_top x))
    have hcpos : (0 : ℝ) < c := by
      have := hk.pos x hx; rw [hc, ← EReal.coe_zero, EReal.coe_lt_coe_iff] at this
      exact this
    refine ⟨2 / c, by positivity, ?_⟩
    intro hmem
    have hle : k ((2 / c) • x) ≤ 1 := hmem
    rw [hk.posHomogeneous _ (by positivity) x, hc, ← EReal.coe_one,
      ← EReal.coe_mul, EReal.coe_le_coe_iff, div_mul_cancel₀ (2 : ℝ) hcpos.ne'] at hle
    linarith

/-- **The norms are exactly the gauges of the symmetric convex sets that absorb every point and
contain no ray.** -/
theorem isNorm_iff :
    IsNorm k ↔ ∃ C : Set E, Convex ℝ C ∧ (0 : E) ∈ C ∧ -C = C ∧ AbsorbsAll C ∧ RayFree C ∧
      k = gaugeFn C := by
  constructor
  · intro hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hk.level_one
    exact ⟨{x : E | k x ≤ 1}, h1, h2, h3, h4, h5,
      (gaugeFn_level_one hk.nonneg hk.posHomogeneous hk.map_zero).symm⟩
  · rintro ⟨C, hC, h0, hsymm, habs, hray, rfl⟩
    exact isNorm_gaugeFn hC h0 hsymm habs hray

/-! #### A norm is a `Seminorm`

Mathlib's `Seminorm 𝕜 E` is purely algebraic — subadditive, absolutely homogeneous, and nothing
about a topology — so a Rockafellar norm is one on the nose. It is *not* a `NormedSpace` norm
unless it happens to be continuous, which in general it is not; that is the distinction, and it is
the only one. -/

theorem IsNorm.coe_toReal (hk : IsNorm k) (x : E) : (((k x).toReal : ℝ) : EReal) = k x :=
  EReal.coe_toReal (hk.ne_top x) (hk.toIsGauge.ne_bot x)

/-- **A norm is absolutely homogeneous**, not merely positively homogeneous: symmetry upgrades
`k (a • x) = a * k x` for `a > 0` to `k (a • x) = |a| * k x` for every real `a`. -/
theorem IsNorm.apply_smul (hk : IsNorm k) (a : ℝ) (x : E) :
    k (a • x) = ((|a| : ℝ) : EReal) * k x := by
  rcases lt_trichotomy a 0 with h | h | h
  · have hx : a • x = -((-a) • x) := by rw [neg_smul, neg_neg]
    rw [hx, hk.map_neg, hk.toIsGauge.posHomogeneous (-a) (neg_pos.2 h) x, abs_of_neg h]
  · subst h
    simp [hk.toIsGauge.map_zero]
  · rw [hk.toIsGauge.posHomogeneous a h x, abs_of_pos h]

/-- **A Rockafellar norm is a `Seminorm`.** `Seminorm ℝ E` asks for subadditivity (which follows
from convexity and positive homogeneity), invariance under negation, and absolute homogeneity —
all three of which `IsNorm` carries, and none of which mentions a topology.

This is the bridge that lets a surface over `ℝⁿ` hand a Rockafellar norm to Mathlib's seminorm
API. What it does *not* give is a `NormedSpace`: for that the norm must be continuous, and
continuity of a finite convex function is a finite-dimensional fact. -/
noncomputable def IsNorm.toSeminorm (hk : IsNorm k) : Seminorm ℝ E where
  toFun x := (k x).toReal
  map_zero' := by simp [hk.toIsGauge.map_zero]
  add_le' x y := by
    have hsub :=
      (PosHomogeneous.convexFn_iff_subadditive hk.toIsGauge.posHomogeneous
        hk.toIsGauge.ne_bot).1 hk.toIsGauge.convexFn x y
    have hcoe : (((k (x + y)).toReal : ℝ) : EReal)
        ≤ (((k x).toReal + (k y).toReal : ℝ) : EReal) := by
      rw [hk.coe_toReal, EReal.coe_add, hk.coe_toReal, hk.coe_toReal]
      exact hsub
    exact_mod_cast hcoe
  neg' x := by rw [hk.map_neg]
  smul' a x := by
    rw [hk.apply_smul a x, EReal.toReal_mul, EReal.toReal_coe, Real.norm_eq_abs]

/-- The `Seminorm` really is `k`. -/
@[simp] theorem IsNorm.coe_toSeminorm (hk : IsNorm k) (x : E) :
    ((hk.toSeminorm x : ℝ) : EReal) = k x := hk.coe_toReal x

end Norm

/-! ### The polar of a norm -/

section NormPolar

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E}

theorem polarSet_neg_eq (hsymm : -C = C) : -polarSet B C = polarSet B C := by
  have hnegC : ∀ x ∈ C, -x ∈ C := fun x hx => by
    rw [← hsymm]
    exact Set.neg_mem_neg.2 hx
  have hb : ∀ (x : E) (y : F), B (-x) (-y) = B x y := fun x y => by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  have hb2 : ∀ (x : E) (y : F), B x (-y) = B (-x) y := fun x y => by
    simp only [map_neg, LinearMap.neg_apply]
  ext y
  simp only [Set.mem_neg, mem_polarSet]
  constructor
  · intro h x hx
    have hle := h (-x) (hnegC x hx)
    rwa [hb] at hle
  · intro h x hx
    have hle := h (-x) (hnegC x hx)
    rwa [← hb2] at hle

/-- The polar of a set on which every `⟨·, y⟩` is bounded above absorbs every point. -/
theorem absorbsAll_polarSet (hbdd : ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c) :
    AbsorbsAll (polarSet B C) := by
  intro y
  obtain ⟨c, hc⟩ := hbdd y
  refine ⟨max c 1, le_trans zero_le_one (le_max_right c 1), ?_⟩
  have hmax : (0 : ℝ) < max c 1 := lt_of_lt_of_le zero_lt_one (le_max_right c 1)
  rw [mem_smul_set_iff_inv_smul_mem₀ hmax.ne']
  intro x hx
  rw [map_smul, smul_eq_mul, inv_mul_le_iff₀ hmax, mul_one]
  exact le_trans (hc x hx) (le_max_left c 1)

/-- If the pairing separates the points of `F` using `C` alone, the polar of `C` contains no
ray. -/
theorem rayFree_polarSet (hsymm : -C = C)
    (hsep : ∀ y : F, y ≠ 0 → ∃ x ∈ C, B x y ≠ 0) : RayFree (polarSet B C) := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hsep y hy
  have hpos : ∃ z ∈ C, 0 < B z y := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · refine ⟨-x, by rw [← hsymm]; exact Set.neg_mem_neg.2 hx, ?_⟩
      simp only [map_neg, LinearMap.neg_apply]
      linarith
    · exact ⟨x, hx, hgt⟩
  obtain ⟨z, hz, hzy⟩ := hpos
  refine ⟨2 / B z y, by positivity, fun hmem => ?_⟩
  have h := hmem z hz
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ (2 : ℝ) hzy.ne'] at h
  linarith

/-- **The polar of a norm is a norm.**

The two hypotheses are the general forms of "`C` is bounded" and "`0 ∈ int C`": boundedness in the
pairing sense makes the polar absorbing, and separation of `F` by `C` makes the polar ray-free. -/
theorem isNorm_polarGauge_gaugeFn (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) (hsymm : -C = C)
    (hbdd : ∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c)
    (hsep : ∀ y : F, y ≠ 0 → ∃ x ∈ C, B x y ≠ 0) :
    IsNorm (polarGauge B (gaugeFn C)) := by
  rw [polarGauge_gaugeFn hC ⟨0, h0⟩]
  exact isNorm_gaugeFn (convex_polarSet B C) (fun x _ => by simp) (polarSet_neg_eq hsymm)
    (absorbsAll_polarSet hbdd) (rayFree_polarSet hsymm hsep)

end NormPolar

/-! ### Bridge to Mathlib's `gauge` -/

section MathlibGauge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {C : Set E}

/-- **`gaugeFn` is Mathlib's `gauge`, wherever the latter is meaningful.** Mathlib's `gauge` takes
the infimum over *positive* scalars in `ℝ`, so on a set that does not absorb `x` it returns
`sInf ∅ = 0` rather than `+∞`; under an absorbency hypothesis the two agree. -/
theorem gaugeFn_eq_gauge (hC : Absorbent ℝ C) (x : E) : gaugeFn C x = (gauge C x : EReal) := by
  refine le_antisymm (le_coe_of_forall_gt_le fun d hd => ?_) ?_
  · obtain ⟨b, hb0, hbd, hbx⟩ := exists_lt_of_gauge_lt hC hd
    exact le_trans (gaugeFn_le_of_mem_smul hb0.le hbx) (by exact_mod_cast hbd.le)
  · rw [gaugeFn_apply]
    refine le_iInf₂ (f := fun (a : ℝ) (_ : a ∈ {a : ℝ | 0 ≤ a ∧ x ∈ a • C}) => (a : EReal))
      fun a ha => ?_
    exact_mod_cast gauge_le_of_mem ha.1 ha.2

/-- An absorbent set has a finite gauge. -/
theorem gaugeFn_lt_top_of_absorbent (hC : Absorbent ℝ C) (x : E) : gaugeFn C x < ⊤ := by
  rw [gaugeFn_eq_gauge hC]
  exact EReal.coe_lt_top _

/-- Mathlib's `Absorbent` implies the elementary absorbency `AbsorbsAll`. -/
theorem absorbsAll_of_absorbent (hC : Absorbent ℝ C) : AbsorbsAll C := fun x => by
  obtain ⟨r, hr0, hr⟩ := (hC x).exists_pos
  exact ⟨r, hr0.le, hr r (Real.norm_of_nonneg hr0.le).ge rfl⟩

end MathlibGauge


end ConvexAnalysis
