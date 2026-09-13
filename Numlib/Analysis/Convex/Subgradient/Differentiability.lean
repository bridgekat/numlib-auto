import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.Monotone
import Numlib.Analysis.Convex.Subgradient.Convergence
import Numlib.Analysis.Convex.Subgradient.Gradient
import Numlib.Analysis.Convex.Subgradient.OneDim

/-!
# Where a convex function is differentiable

The continuity theory of one-sided derivatives, read as an existence theory for derivatives. A
convex function on the line has a two-sided derivative off a countable set, and that derivative is
continuous and nondecreasing there. In a fixed direction `y`, the two-sided directional derivative
exists exactly where `x ↦ f'(x; y)` is continuous, and that happens on a dense subset of
`int (dom f)`.

## Main results

* `continuousAt_rightDeriv_iff` — a continuity criterion: `f'₊` is continuous at `x` exactly when
  `f'₋(x) = f'₊(x)`.
* `countable_leftDeriv_ne_rightDeriv` — the jump set of `f'₊` is countable.
* `differentiableAtFn_iff_leftDeriv_eq_rightDeriv` — on the line, differentiability at an interior
  point of `dom f` *is* the equality of the two one-sided derivatives.
* `countable_not_differentiableAtFn`, `continuousAt_rightDeriv_of_differentiableAtFn`,
  `subset_closure_differentiableAtFn` — a countable exceptional set, continuity of the derivative
  where it exists, and density of the points of differentiability (Theorem 25.3 in [^1]).
* `continuousAt_dirDeriv_iff`, `subset_closure_twoSided_dirDeriv` — the same in a fixed direction
  (Theorem 25.4 in [^1]).

## Implementation notes

`rightDeriv f` is defined on the whole line, not only on the set `D` where the derivative exists,
so the continuity assertions here are the ordinary `ContinuousAt`, stronger than the book's
"continuous relative to `D`". Monotonicity is likewise global.

Three of the classical hypotheses are absent. The countability and density clauses need no
closedness of `f`, because only the easy half of the continuity criterion is used; closedness
enters only in the converse, through the one-sided limit formulas for `f'₊`. The directional form
needs no `y ≠ 0`, since at `y = 0` both sides hold, and its density clause is proved by restricting
to a line rather than through Lebesgue measure, so it needs no finite-dimensionality.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §25.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### A continuity criterion for `f'₊` -/

section Line

variable {f : ℝ → EReal} {x : ℝ}

/-- Continuity of `f'₊` at `x` forces the two-sided derivative: monotonicity gives
`f'₊(z) → ⨆ {f'₊(z) | z < x}` as `z ↑ x`, continuity identifies that supremum with `f'₊(x)`, and
every `f'₊(z)` with `z < x` lies below `f'₋(x)`. Unlike the converse this needs no closedness. -/
theorem leftDeriv_eq_rightDeriv_of_continuousAt (hf : ConvexFn f) (hp : Proper f)
    (hc : ContinuousAt (rightDeriv f) x) : leftDeriv f x = rightDeriv f x := by
  have hsup : ⨆ z ∈ Iio x, rightDeriv f z = rightDeriv f x :=
    tendsto_nhds_unique (tendsto_nhdsWithin_Iio_of_monotone (monotone_rightDeriv hf hp) x)
      (Filter.Tendsto.mono_left hc nhdsWithin_le_nhds)
  refine le_antisymm (leftDeriv_le_rightDeriv hf hp x) ?_
  rw [← hsup]
  exact iSup₂_le fun z hz => rightDeriv_le_leftDeriv hp hz

/-- For a closed proper convex function on the line, the nondecreasing function `f'₊` is continuous
at `x` exactly when it agrees with `f'₋` there. -/
theorem continuousAt_rightDeriv_iff (hf : ClosedProperConvexFn f) (x : ℝ) :
    ContinuousAt (rightDeriv f) x ↔ leftDeriv f x = rightDeriv f x := by
  refine ⟨leftDeriv_eq_rightDeriv_of_continuousAt hf.convex hf.proper, fun h => ?_⟩
  have h1 : Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (rightDeriv f x)) := by
    rw [← h]
    exact tendsto_rightDeriv_nhdsWithin_Iio hf x
  have h2 : Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
    tendsto_rightDeriv_nhdsWithin_Ioi hf x
  have h3 : Tendsto (rightDeriv f) (pure x) (𝓝 (rightDeriv f x)) := tendsto_pure_nhds _ x
  have hsup : Tendsto (rightDeriv f) (𝓝[≠] x ⊔ pure x) (𝓝 (rightDeriv f x)) := by
    rw [← nhdsLT_sup_nhdsGT]
    exact (h1.sup h2).sup h3
  rwa [nhdsNE_sup_pure] at hsup

/-- The jump set of `f'₊` is countable: `f'₊` is nondecreasing into the second-countable order
topology of `EReal`, and its discontinuity set contains the set where `f'₋ ≠ f'₊`. -/
theorem countable_leftDeriv_ne_rightDeriv (hf : ConvexFn f) (hp : Proper f) :
    {x : ℝ | leftDeriv f x ≠ rightDeriv f x}.Countable := by
  refine Set.Countable.mono ?_ (monotone_rightDeriv hf hp).countable_not_continuousAt
  intro z hz
  have hz' : leftDeriv f z ≠ rightDeriv f z := hz
  exact fun hcon => hz' (leftDeriv_eq_rightDeriv_of_continuousAt hf hp hcon)

/-! ### The two-sided derivative on the line -/

/-- On the line a two-sided derivative makes `f'(x; ·)` linear: positive homogeneity reduces
`f'(x; v)` to the directions `±1`, where the values are `f'₊(x)` and `-f'₋(x)`. -/
theorem dirDeriv_eq_of_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (h : leftDeriv f x = rightDeriv f x) (v : ℝ) :
    dirDeriv f x v = (((rightDeriv f x).toReal * v : ℝ) : EReal) := by
  obtain ⟨hbot, htop⟩ := rightDeriv_finite_of_mem_interior_dom hf hp hx
  set c : ℝ := (rightDeriv f x).toReal with hcdef
  have hrc : rightDeriv f x = (c : EReal) := (EReal.coe_toReal htop hbot).symm
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have h1 : dirDeriv f x 1 = (c : EReal) := by rw [← rightDeriv_eq_dirDeriv hfx hfb, hrc]
  have hm1 : dirDeriv f x (-1) = ((-c : ℝ) : EReal) := by
    have hL := leftDeriv_eq_neg_dirDeriv hfx hfb
    rw [h, hrc] at hL
    rw [EReal.coe_neg, hL, neg_neg]
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · have hvv : v = (-v) • (-1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x (-v) (by linarith) (-1), hm1, ← EReal.coe_mul]
    congr 1
    ring
  · rw [dirDeriv_zero hfx.ne hfb]
    simp
  · have hvv : v = v • (1 : ℝ) := by rw [smul_eq_mul]; ring
    rw [hvv, posHomogeneous_dirDeriv f x v hv 1, h1, ← EReal.coe_mul]
    congr 1
    ring

/-- On the line, a convex function is differentiable at an interior point of its effective domain
exactly when its two one-sided derivatives agree there. -/
theorem differentiableAtFn_iff_leftDeriv_eq_rightDeriv (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) :
    DifferentiableAtFn f x ↔ leftDeriv f x = rightDeriv f x := by
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  constructor
  · rintro ⟨y₀, hy₀⟩
    have hd := hy₀.dirDeriv_eq hf
    rw [rightDeriv_eq_dirDeriv hfx hfb, leftDeriv_eq_neg_dirDeriv hfx hfb, hd 1, hd (-1),
      ← EReal.coe_neg]
    congr 1
    have hneg : y₀ (-1 : ℝ) = -y₀ (1 : ℝ) := by rw [← map_neg]
    rw [hneg, neg_neg]
  · intro h
    exact ⟨(rightDeriv f x).toReal • ContinuousLinearMap.id ℝ ℝ,
      hasGradientAtFn_of_dirDeriv_eq hf hfx.ne hfb fun v => by
        rw [dirDeriv_eq_of_leftDeriv_eq_rightDeriv hf hp hx h v]
        norm_num⟩

/-! ### Differentiability off a countable set -/

/-- **First assertion**: a convex function on the line is differentiable at all but countably many
points of the interior of its effective domain. No closedness is needed, so the usual preliminary
extension of `f` to a closed proper convex function on `ℝ` is not made. -/
theorem countable_not_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    {x ∈ interior (dom f) | ¬DifferentiableAtFn f x}.Countable := by
  refine Set.Countable.mono ?_ (countable_leftDeriv_ne_rightDeriv hf hp)
  rintro z ⟨hz, hzd⟩
  exact fun hcon => hzd ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hz).2 hcon)

/-- **Second assertion**: the derivative is continuous where it exists. Stronger than "continuous
relative to `D`": `rightDeriv f` is continuous at `x` on the whole line. -/
theorem continuousAt_rightDeriv_of_differentiableAtFn (hf : ClosedProperConvexFn f)
    (hx : x ∈ interior (dom f)) (hd : DifferentiableAtFn f x) :
    ContinuousAt (rightDeriv f) x :=
  (continuousAt_rightDeriv_iff hf x).2
    ((differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf.convex hf.proper hx).1 hd)

/-- **Third assertion**: the points of differentiability are dense in the interior of the effective
domain, a countable subset of `ℝ` having dense complement. -/
theorem subset_closure_differentiableAtFn (hf : ConvexFn f) (hp : Proper f) :
    interior (dom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} := by
  intro z hz
  rw [mem_closure_iff]
  intro U hU hzU
  obtain ⟨w, hw, hwU⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hf hp)).exists_mem_open
      (hU.inter isOpen_interior) ⟨z, hzU, hz⟩
  exact ⟨w, hwU.1,
    (differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hwU.2).2 (not_not.1 hw)⟩

end Line

/-! ### Restriction to a line -/

section Restrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- The restriction of `f` to the line `t ↦ x + t • y` is convex. -/
theorem convexFn_lineRestrict (hf : ConvexFn f) (x y : E) :
    ConvexFn fun t : ℝ => f (x + t • y) := by
  refine convexFn_of_epi_combo fun t₁ t₂ μ ν h₁ h₂ a b ha hb hab => ?_
  have hpt : x + (a • t₁ + b • t₂) • y = a • (x + t₁ • y) + b • (x + t₂ • y) := by
    rw [smul_eq_mul, smul_eq_mul]
    match_scalars <;> linarith [hab]
  rw [hpt]
  exact hf.epi_combo h₁ h₂ ha hb hab

/-- The restriction of `f` to a line through a point of `dom f` is proper. -/
theorem proper_lineRestrict (hp : Proper f) (hx : x ∈ dom f) (y : E) :
    Proper fun t : ℝ => f (x + t • y) :=
  ⟨⟨0, by simpa using hx⟩, fun t => hp.ne_bot _⟩

/-- The one-dimensional restriction computes the directional derivative along the line. This is
what lets the one-dimensional theory be applied in a fixed direction. -/
theorem dirDeriv_lineRestrict (f : E → EReal) (x y : E) (t v : ℝ) :
    dirDeriv (fun s : ℝ => f (x + s • y)) t v = dirDeriv f (x + t • y) (v • y) := by
  have harg : ∀ a : ℝ, x + (t + a • v) • y = x + t • y + a • (v • y) := by
    intro a
    rw [smul_eq_mul, smul_smul]
    module
  simp only [dirDeriv_apply, harg]

end Restrict

/-! ### The two-sided derivative in a fixed direction -/

section TwoSided

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}

/-- For a fixed direction `y`, the function `z ↦ f'(z; y)` is upper semicontinuous at every
interior point of `dom f`. -/
theorem upperSemicontinuousAt_dirDeriv_left [FiniteDimensional ℝ E] (hf : ConvexFn f)
    (hp : Proper f) (hx : x ∈ interior (dom f)) (y : E) :
    UpperSemicontinuousAt (fun z => dirDeriv f z y) x := by
  intro c hc
  have hcont : Continuous fun z : E => (z, y) := by fun_prop
  exact (hcont.tendsto x).eventually (upperSemicontinuousAt_dirDeriv hf hp hx y c hc)

/-- For every `λ > 0`, `f'(x - λ y; y) ≤ (f x - f (x - λ y)) / λ ≤ -f'(x; -y)`: the first
inequality is the term of the defining infimum at `x - λ y` with step `λ`, which lands exactly on
`x`, and the second is the corresponding term at `x` in the direction `-y`, negated. No convexity
and no interiority are used, only properness. -/
theorem dirDeriv_sub_smul_le (hp : Proper f) (hfx : f x < ⊤) (y : E) {l : ℝ} (hl : 0 < l) :
    dirDeriv f (x - l • y) y ≤ -dirDeriv f x (-y) := by
  rcases eq_or_lt_of_le (le_top : f (x - l • y) ≤ ⊤) with hu | hu
  · rw [dirDeriv_eq_bot_of_eq_top hu]
    exact bot_le
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x) hfx
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot (x - l • y)) hu
  have h1 : dirDeriv f (x - l • y) y ≤ (((r - s) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f (x - l • y) y hl
    rwa [show x - l • y + l • y = x from by abel, hr, hs, ← EReal.coe_sub,
      ← EReal.coe_div] at hq
  have h2 : dirDeriv f x (-y) ≤ (((s - r) / l : ℝ) : EReal) := by
    have hq := dirDeriv_le f x (-y) hl
    rwa [show x + l • (-y) = x - l • y from by module, hr, hs, ← EReal.coe_sub,
      ← EReal.coe_div] at hq
  refine h1.trans ?_
  have h3 := EReal.neg_le_neg_iff.2 h2
  rwa [← EReal.coe_neg, show -((s - r) / l) = (r - s) / l from by ring] at h3

/-- **First assertion**: on the interior of `dom f`, the set where the two-sided directional
derivative in the direction `y` exists is exactly the set where `x ↦ f'(x; y)` is continuous. The
usual `y ≠ 0` is not needed — at `y = 0` both sides hold. -/
theorem continuousAt_dirDeriv_iff [FiniteDimensional ℝ E] (hf : ConvexFn f) (hp : Proper f)
    (hx : x ∈ interior (dom f)) (y : E) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) := by
  have hfx : f x < ⊤ := mem_dom.1 (interior_subset hx)
  constructor
  · intro hc
    refine le_antisymm ?_ (neg_dirDeriv_neg_le hf hfx.ne (hp.ne_bot x) y)
    have hray : Tendsto (fun l : ℝ => x - l • y) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have hcont : Continuous fun l : ℝ => x - l • y := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc' : Tendsto (fun z : E => dirDeriv f z y) (𝓝 x) (𝓝 (dirDeriv f x y)) := hc
    have hlim : Tendsto (fun l : ℝ => dirDeriv f (x - l • y) y) (𝓝[>] (0 : ℝ))
        (𝓝 (dirDeriv f x y)) := hc'.comp hray
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact dirDeriv_sub_smul_le hp hfx y (mem_Ioi.1 hl)
  · intro h
    refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
    · have ha' : a < dirDeriv f x y := ha
      rw [h] at ha'
      have hev := upperSemicontinuousAt_dirDeriv_left hf hp hx (-y) (-a)
        (EReal.lt_neg_of_lt_neg ha')
      filter_upwards [hev, isOpen_interior.mem_nhds hx] with z hz hzi
      have hz' : dirDeriv f z (-y) < -a := hz
      have hzt : f z < ⊤ := mem_dom.1 (interior_subset hzi)
      exact lt_of_lt_of_le (EReal.lt_neg_of_lt_neg hz')
        (neg_dirDeriv_neg_le hf hzt.ne (hp.ne_bot z) y)
    · have hc' : dirDeriv f x y < c := hc
      exact upperSemicontinuousAt_dirDeriv_left hf hp hx y c hc'

/-- **Density**: the points of `int (dom f)` at which the two-sided directional
derivative in the direction `y` exists are dense in `int (dom f)`. Proved on a line rather than
through Lebesgue measure: `t ↦ f (x + t • y)` is a proper convex function of one variable whose
one-sided derivatives at `t` are `f'(x + t y; ±y)`, and its jump set is countable. -/
theorem subset_closure_twoSided_dirDeriv (hf : ConvexFn f) (hp : Proper f) (y : E) :
    interior (dom f) ⊆
      closure {z ∈ interior (dom f) | dirDeriv f z y = -dirDeriv f z (-y)} := by
  intro x hx
  rw [mem_closure_iff]
  intro U hU hxU
  have hgc : ConvexFn fun t : ℝ => f (x + t • y) := convexFn_lineRestrict hf x y
  have hgp : Proper fun t : ℝ => f (x + t • y) :=
    proper_lineRestrict hp (interior_subset hx) y
  have hVopen : IsOpen {t : ℝ | x + t • y ∈ U ∩ interior (dom f)} := by
    have hcont : Continuous fun t : ℝ => x + t • y := by fun_prop
    exact hcont.isOpen_preimage _ (hU.inter isOpen_interior)
  have hV0 : (0 : ℝ) ∈ {t : ℝ | x + t • y ∈ U ∩ interior (dom f)} := by
    simpa using And.intro hxU hx
  obtain ⟨t, ht, htV⟩ :=
    (Set.Countable.dense_compl ℝ (countable_leftDeriv_ne_rightDeriv hgc hgp)).exists_mem_open
      hVopen ⟨0, hV0⟩
  have hgt : f (x + t • y) < ⊤ := mem_dom.1 (interior_subset htV.2)
  have hgb : f (x + t • y) ≠ ⊥ := hp.ne_bot _
  have heq : leftDeriv (fun s : ℝ => f (x + s • y)) t
      = rightDeriv (fun s : ℝ => f (x + s • y)) t := not_not.1 ht
  rw [rightDeriv_eq_dirDeriv hgt hgb, leftDeriv_eq_neg_dirDeriv hgt hgb, dirDeriv_lineRestrict,
    dirDeriv_lineRestrict] at heq
  simp only [one_smul, neg_one_smul] at heq
  exact ⟨x + t • y, htV.1, htV.2, heq.symm⟩

end TwoSided

end ConvexAnalysis
