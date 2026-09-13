import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth

/-!
# Condition (c) of essential smoothness, in directional-derivative form

Given conditions (a) and (b) of essential smoothness, condition (c) — the norms of the gradients
blow up at the boundary of `C = int (dom f)` — may be replaced by

```
(c')  f'(x + λ(a − x); a − x) ↓ −∞ as λ ↓ 0,   for every a ∈ C and every x ∉ C.
```

Both say the same thing at a single point `x`, namely that `∂f x = ∅`: (c) because `∂f` has a
closed graph and is recovered from limits of gradients, and (c') because along the line through `x`
and `a` the directional derivative collapses to `−∞` exactly when `∂f x` is empty. Those two halves
are separate theorems below, so either can be used on its own.

## Main results

* `closedProperConvexFn_lineRestrict` — the restriction of a closed proper convex function to a
  line is closed proper convex, based at *any* point of the line, not only a point of `dom f`.
* `subdifferential_eq_empty_iff_tendsto_dirDeriv`,
  `subdifferential_eq_empty_iff_tendsto_norm_fderiv` — conditions (c') and (c) at `x` each say that
  `∂f x = ∅`.
* `essentiallySmooth_iff_tendsto_dirDeriv` — (c) may be replaced by (c')
  ([rockafellar1970convex] Lemma 26.2).

## Implementation notes

`f` is assumed closed, where the book says "without loss of generality" and replaces `f` by `cl f`;
every consumer already carries `ClosedFn f`. Condition (c') is stated as a `Tendsto` to `𝓝 ⊥`: the
book's `↓` also records monotonicity of `λ ↦ f'(x + λ(a − x); a − x)`, but only the value of the
limit is used.

## References

* [rockafellar1970convex] §26.
-/

namespace ConvexAnalysis

open Filter Metric Topology

/-! ### The restriction to a line, based at an arbitrary point -/

section LineRestrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x y : E}

/-- The restriction of a closed function to a line is closed. -/
theorem closedFn_lineRestrict (hp : Proper f) (hcl : ClosedFn f) (x y : E) :
    ClosedFn fun t : ℝ => f (x + t • y) := by
  have hcont : Continuous fun s : ℝ => x + s • y := by fun_prop
  exact (closedFn_iff_lowerSemicontinuous fun _ => hp.ne_bot _).2 fun t c hc =>
    (hcont.tendsto t).eventually (hcl.lowerSemicontinuous _ c hc)

/-- The restriction of a proper function to a line is proper as soon as the line meets `dom f`.
Unlike `proper_lineRestrict`, this does not ask the *base point* to lie in `dom f` — here the base
point `x` is precisely the one that may fail to. -/
theorem proper_lineRestrict_of_mem_dom (hp : Proper f) {t₀ : ℝ} (ht : x + t₀ • y ∈ dom f) :
    Proper fun t : ℝ => f (x + t • y) :=
  ⟨⟨t₀, ht⟩, fun _ => hp.ne_bot _⟩

/-- The restriction of a closed proper convex function to a line meeting `dom f` is closed proper
convex, which is what the one-dimensional theory runs on. -/
theorem closedProperConvexFn_lineRestrict (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    {t₀ : ℝ} (ht : x + t₀ • y ∈ dom f) :
    ClosedProperConvexFn fun t : ℝ => f (x + t • y) :=
  ⟨convexFn_lineRestrict hf x y, closedFn_lineRestrict hp hcl x y,
    proper_lineRestrict_of_mem_dom hp ht⟩

/-- The right derivative of the restriction is the directional derivative along the line. Both
sides are `−∞` where `f (x + t y) = ⊤`, so the only hypothesis needed is that the line meets
`dom f` somewhere to the right of `t`; without it `g'₊(t)` is `+∞` by fiat and the two differ. -/
theorem rightDeriv_lineRestrict_eq_dirDeriv (hp : Proper f) (x y : E) {t : ℝ}
    (ht : ∃ s, t < s ∧ f (x + s • y) < ⊤) :
    rightDeriv (fun s : ℝ => f (x + s • y)) t = dirDeriv f (x + t • y) y := by
  rcases eq_or_lt_of_le (le_top : f (x + t • y) ≤ ⊤) with htop | htop
  · rw [rightDeriv_eq_bot_of_eq_top htop ht, dirDeriv_eq_bot_of_eq_top htop y]
  · rw [rightDeriv_eq_dirDeriv htop (hp.ne_bot _), dirDeriv_lineRestrict, one_smul]

end LineRestrict

/-! ### The directional derivative along a segment -/

section LineSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {a : E}

/-- Along the segment from `x` to `a`, the directional derivative `f'(x + t(a − x); a − x)` tends,
as `t` decreases to `0`, to the right derivative at `0` of the restriction of `f` to that line. -/
theorem tendsto_dirDeriv_lineRestrict (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (ha : a ∈ dom f) (x : E) :
    Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0)
      (𝓝 (rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0)) := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hcpc : ClosedProperConvexFn fun s : ℝ => f (x + s • y) :=
    closedProperConvexFn_lineRestrict hf hp hcl (t₀ := 1) (by rw [hone]; exact ha)
  refine (tendsto_rightDeriv_nhdsWithin_Ioi hcpc 0).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact rightDeriv_lineRestrict_eq_dirDeriv hp x y ⟨1, ht.2, by rw [hone]; exact mem_dom.1 ha⟩

end LineSegment

/-! ### Condition (c') at a single point -/

section Condition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {a x : E}


/-- `g'₊(0) = −∞` exactly when `f` has no subgradient at `x`, where `g` is the restriction of `f`
to the line from `x` towards a relative interior point `a` of `dom f`. Off `dom f` both sides hold;
on `dom f` the right derivative is `f'(x; a − x)`, which is `−∞` exactly when `∂f x` is empty. -/
theorem rightDeriv_lineRestrict_zero_eq_bot_iff (hf : ConvexFn f) (hp : Proper f)
    (ha : a ∈ ri (dom f)) (x : E) :
    rightDeriv (fun s : ℝ => f (x + s • (a - x))) 0 = ⊥ ↔ subdifferential (innerₗ E) f x = ∅ := by
  set y : E := a - x with hy
  have hone : x + (1 : ℝ) • y = a := by rw [hy]; module
  have hex : ∃ s, (0 : ℝ) < s ∧ f (x + s • y) < ⊤ :=
    ⟨1, zero_lt_one, by rw [hone]; exact mem_dom.1 (intrinsicInterior_subset ha)⟩
  rw [rightDeriv_lineRestrict_eq_dirDeriv hp x y hex, zero_smul, add_zero]
  rcases eq_or_lt_of_le (le_top : f x ≤ ⊤) with htop | htop
  · refine ⟨fun _ => ?_, fun _ => dirDeriv_eq_bot_of_eq_top htop y⟩
    refine Set.eq_empty_of_forall_notMem fun v hv => ?_
    exact absurd (mem_dom.1 (mem_dom_of_mem_subdifferential hp hv)) (by rw [htop]; simp)
  · refine ⟨fun hbot => ?_, fun hempty => ?_⟩
    · exact (subdifferential_eq_empty_iff_exists_dirDeriv_eq_bot (B := innerₗ E) hf htop.ne
        (hp.ne_bot x)).2 ⟨y, hbot⟩
    · have h := dirDeriv_eq_bot_of_subdifferential_eq_empty (B := innerₗ E) hf htop.ne
        (hp.ne_bot x) hempty ha
      rwa [hy]

/-- Condition (c') at `x` says exactly that `f` has no subgradient at `x`. -/
theorem subdifferential_eq_empty_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (ha : a ∈ ri (dom f)) (x : E) :
    subdifferential (innerₗ E) f x = ∅ ↔
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  have htend := tendsto_dirDeriv_lineRestrict hf hp hcl (intrinsicInterior_subset ha) x
  refine ⟨fun hempty => ?_, fun hlim => ?_⟩
  · rwa [(rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).2 hempty] at htend
  · exact (rightDeriv_lineRestrict_zero_eq_bot_iff hf hp ha x).1
      (tendsto_nhds_unique htend hlim)

/-- Condition (c) at `x` says exactly that `f` has no subgradient at `x`. Forwards, a bounded
subsequence of gradients has a convergent sub-subsequence whose limit is a subgradient at `x`.
Backwards, a subgradient at `x` is built from limits of gradients, and that produces a convergent
sequence of gradients which (c) forbids. -/
theorem subdifferential_eq_empty_iff_tendsto_norm_fderiv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) (x : E) :
    subdifferential (innerₗ E) f x = ∅ ↔
      ∀ zs : ℕ → E, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop := by
  constructor
  · intro hempty zs hzs hlim
    by_contra hcon
    -- A bounded subsequence of gradients, converging after a second extraction.
    obtain ⟨b, hb⟩ := not_forall.1 (Filter.tendsto_atTop.not.1 hcon)
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
    set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
    have hgrad : ∀ i, HasGradientAtFn f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
      rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
      exact (hdiff (hzs i)).hasGradientAtFn_fderiv
    have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
      rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
      exact (not_le.1 (hφb n)).le
    obtain ⟨w, -, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
    have hmem : w ∈ gradientLimits f x :=
      ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
        fun n => hgrad (φ (ψ n)), hψlim⟩
    exact absurd (gradientLimits_subset_subdifferential hf hp hcl hmem) (by rw [hempty]; simp)
  · intro hc
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨v, hv⟩
    -- A subgradient is built from limits of gradients, by convex hull and normal cone.
    rw [subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne] at hv
    obtain ⟨u, hu, -, -, -⟩ := hv
    obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ : (gradientLimits f x).Nonempty := by
      rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne'
      · rw [hempty, convexHull_empty, closure_empty] at hu
        exact absurd hu (Set.notMem_empty u)
      · exact hne'
    have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
      rw [(hgrad i).fderiv_toReal_eq, LinearIsometryEquiv.norm_map]
    have htop := hc xs (fun i => (hgrad i).mem_interior_dom) hxs
    rw [tendsto_congr hnorm] at htop
    exact not_tendsto_atTop_of_tendsto_nhds hvs.norm htop

/-- At a single point: given (a) and (b), condition (c) at `x` and condition (c') at `x` in the
direction of any `a ∈ C` say the same thing. -/
theorem tendsto_norm_fderiv_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f)
    (hcl : ClosedFn f) (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z)
    (ha : a ∈ interior (dom f)) (x : E) :
    (∀ zs : ℕ → E, (∀ i, zs i ∈ interior (dom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  (subdifferential_eq_empty_iff_tendsto_norm_fderiv hf hp hcl hne hdiff x).symm.trans
    (subdifferential_eq_empty_iff_tendsto_dirDeriv hf hp hcl
      (Convex.interior_subset_relint hf.convex_dom hne ha) x)

/-- For a closed proper convex function satisfying (a) and (b), essential smoothness is condition
(c'), the collapse of the directional derivative to `−∞` along every segment reaching a point
outside `C = int (dom f)`. -/
theorem essentiallySmooth_iff_tendsto_dirDeriv (hf : ConvexFn f) (hp : Proper f) (hcl : ClosedFn f)
    (hne : (interior (dom f)).Nonempty)
    (hdiff : ∀ ⦃z : E⦄, z ∈ interior (dom f) → DifferentiableAtFn f z) :
    EssentiallySmooth f ↔ ∀ x ∉ interior (dom f), ∀ a ∈ interior (dom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) := by
  constructor
  · intro hes x hx a haC
    exact (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC x).1
      (hes.tendsto_norm_fderiv hx)
  · intro hc
    obtain ⟨a, haC⟩ := id hne
    exact ⟨hne, hdiff, fun z hz =>
      (tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff haC z).2 (hc z hz a haC)⟩

end Condition

end ConvexAnalysis
