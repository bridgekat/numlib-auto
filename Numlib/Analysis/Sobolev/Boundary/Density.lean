import Numlib.Analysis.Sobolev.Extension
import Numlib.Analysis.Sobolev.TranslationCurve
import Numlib.Geometry.Triangulation

/-!
# Density of smooth functions up to the boundary

The two density statements that the trace theory of `Numlib/Analysis/Sobolev/Boundary/Trace.lean`
consumes, as predicates on an open set `Ω ⊆ ℝ^N`, and their instances.

* `SobolevEuclidean.HasSmoothDensity N p Ω`: every `u ∈ W^{1,p}(Ω)` is the limit in `W^{1,p}(Ω)`
  of restrictions of `C_c^∞(ℝ^N)` functions — the conclusion of [brezis2011functional]
  Corollary 9.8 as a predicate, so that a trace can be extended from the smooth functions by
  continuity (the dense subspace is `SobolevEuclidean.smoothRestrictions N p Ω`).
* `SobolevEuclidean.HasUniformSmoothDensity N p Ω`: when moreover `u` has a representative `ũ`
  continuous on `closure Ω`, the approximants can be taken to converge to `ũ` *uniformly on
  `closure Ω`* as well. This is what identifies the trace of `u` with `ũ|_{∂Ω}` (Evans, *Partial
  Differential Equations*, §5.5, Theorem 1 (ii): "the functions constructed in §5.3.3 converge
  uniformly").

The extension theorem gives the first predicate on every extension domain
(`IsSobolevExtensionDomain.hasSmoothDensity`), but not the second, whose approximants must be
built with an eye on continuity. Both are proved here for every bounded open set with the
**segment property** of Adams and Fournier, *Sobolev Spaces*, 2nd edition, 3.21–3.22
(`HasSegmentProperty Ω`: each boundary point has a neighbourhood `U` and a direction `y` with
`closure Ω ∩ U + t y ⊆ Ω` for `0 < t < 1`), by the classical translation-and-mollification
construction (`HasSegmentProperty.exists_seq_contDiff_hasCompactSupport_tendsto`). The segment
property holds for every domain whose boundary is locally the graph of a *continuous* function
(`IsBoundaryOfClass.hasSegmentProperty`: the `C^n` and the Lipschitz graph domains) and for
every convex open set (`Convex.hasSegmentProperty`), hence for every triangle. By-products
beyond the trace theory: the density of `C_c^∞(ℝ^N)` in `W^{1,p}(Ω)` on bounded *Lipschitz*
graph domains (`IsLipschitzDomain.hasSmoothDensity`, the Lipschitz case of Atkinson–Han
Theorem 7.3.2, which the extension route does not reach) and on convex polygons.

## The construction

For `u ∈ W^{1,p}(Ω)`, a representative `ũ`, and `ε > 0`
(`HasSegmentProperty.exists_contDiff_hasCompactSupport_norm_sub_lt`):

0. `frontier Ω` is compact, so finitely many of the neighbourhoods `U_i` of the segment
   property, with directions `y_i`, cover it; Brezis's Lemma 9.3
   (`IsCompact.exists_contDiff_partitionOfUnity`) gives smooth `θ₀, θ_i` with `θ₀ + ∑ θ_i = 1`,
   `tsupport θ_i ⊆ U_i` compact, `tsupport θ₀` disjoint from `frontier Ω`.
1. **One piece** (`SobolevEuclidean.exists_translatePiece`): for a smooth `θ` and a translation
   `h` such that `z + h ∈ Ω` whenever `z ∈ closure Ω` lies in a set `U ⊇ tsupport θ − h`, the
   translate `F(x) = χ(x) θ(x + h) ũ(x + h)` of the zero extension of `θ u`, cut off by a smooth
   `χ` equal to `1` on `closure Ω` and supported in the open set
   `(Ω − h) ∪ (tsupport θ − h)ᶜ ⊇ closure Ω`, lies in `W^{1,p}(ℝ^N)` with compact support: on
   `Ω − h` it is `α · ũ(· + h)` with
   `α = χ θ(· + h)` smooth and supported inside `Ω − h`, and `ũ(· + h) ∈ W^{1,p}(Ω − h)`
   (`HasWeakIteratedLineDerivOn.comp_add_right_of_preimage`, the translation of a weak
   derivative to a translated domain), so the zero extension across `∂(Ω − h)` is
   `HasWeakIteratedLineDerivOn.indicator_smul_of_tsupport_inter_subset` of `Cutoff.lean`. On
   `Ω` its function is `(θ u)^0(· + h)` and its gradient `(θ ∇u + u ∇θ)^0(· + h)` — the translates
   of the zero extensions — and it is continuous when `ũ` is continuous on `closure Ω`. The
   interior piece is the case `h = 0`, `U = (frontier Ω)ᶜ`.
2. **Translation is continuous in `L^p`** (`MeasureTheory.Lp.continuous_translateCurve`): the
   sum `F_t` of the interior piece and the boundary pieces at `h_i = t y_i` differs from `u` in
   `W^{1,p}(Ω)` by at most `∑_i ‖τ_{t y_i} H_i − H_i‖_{L^p(ℝ^N)}` over the finitely many zero
   extensions `H_i` involved (`SobolevEuclidean.norm_le_sum_norm_translateCurve_sub`), which
   tends to `0` with `t`; and on `closure Ω`, `F_t − ũ = ∑_i [(θ_i ũ)^0(· + t y_i) − θ_i ũ]`, each
   term small by the uniform continuity of `θ_i ũ` on the compact `closure Ω` when `z + t y_i ∈ Ω`,
   and *zero* otherwise (the segment property forces `z ∉ U_i`, so `θ_i z = 0`).
3. **Mollification** (`MemSobolev.exists_contDiff_hasCompactSupport_sobolevNorm_sub_lt`): a
   mollification of `F_t` is smooth with compact support, within `ε/2` of `F_t` in `W^{1,p}(ℝ^N)`
   (`MemSobolev.tendsto_sobolevNorm_convolution_sub`), and within `ε/2` uniformly when `F_t` is
   continuous (`ContDiffBump.dist_normed_convolution_le` with uniform continuity).

## References

Adams–Fournier, *Sobolev Spaces*, 3.21–3.22; Evans, *PDE*, §5.3.3 and §5.5;
[brezis2011functional] §9.2 (Lemma 9.3), Corollary 9.8.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology Convolution

noncomputable section

/-! ### The density predicates -/

section Predicates

variable (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- **Smooth functions are dense in `W^{1,p}(Ω)` up to the boundary**: every `u ∈ W^{1,p}(Ω)` is
the limit in `W^{1,p}(Ω)` of elements whose functions are the restrictions to `Ω` of smooth
compactly supported functions on `ℝ^N` — the conclusion of [brezis2011functional] Corollary 9.8
(`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto`) as a predicate on `Ω`. It is
the hypothesis under which a trace is extended from the smooth functions by continuity. -/
def SobolevEuclidean.HasSmoothDensity : Prop :=
  ∀ u : SobolevEuclidean N 1 p Ω, ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ,
    (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → SobolevEuclidean N 1 p Ω,
        (∀ n, fn (w n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
          Tendsto w atTop (𝓝 u)

/-- **Smooth approximation in `W^{1,p}(Ω)` and uniformly on `closure Ω`** of a Sobolev function
continuous up to the boundary: for `u ∈ W^{1,p}(Ω)` with a representative `ũ` continuous on
`closure Ω`, there are smooth compactly supported `v n` on `ℝ^N` whose restrictions converge to
`u` in `W^{1,p}(Ω)` and which converge to `ũ` uniformly on `closure Ω`. It is the hypothesis
under which the trace of `u` is the restriction `ũ|_{∂Ω}` (Evans, *PDE*, §5.5, Theorem 1 (ii)). -/
def SobolevEuclidean.HasUniformSmoothDensity : Prop :=
  ∀ (u : SobolevEuclidean N 1 p Ω) (ũ : EuclideanSpace ℝ (Fin N) → ℝ),
    fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ →
    ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
        (∃ w : ℕ → SobolevEuclidean N 1 p Ω,
          (∀ n, fn (w n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
            Tendsto w atTop (𝓝 u)) ∧
        TendstoUniformlyOn v ũ atTop (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))

/-- **The restrictions of smooth compactly supported functions**, as a subspace of `W^{1,p}(Ω)`:
the elements whose function is, almost everywhere on `Ω`, a `C_c^∞(ℝ^N)` function. This is the
dense subspace (`SobolevEuclidean.HasSmoothDensity.dense_smoothRestrictions`) from which the
trace is extended by continuity. -/
def SobolevEuclidean.smoothRestrictions : Submodule ℝ (SobolevEuclidean N 1 p Ω) where
  carrier := {u | ∃ v : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
    fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, fn_zero⟩
  add_mem' {u v} := fun ⟨a, ha, hac, hua⟩ ⟨b, hb, hbc, hvb⟩ ↦
    ⟨a + b, ha.add hb, hac.add hbc, (fn_add u v).trans (hua.add hvb)⟩
  smul_mem' c u := fun ⟨a, ha, hac, hua⟩ ↦
    ⟨c • a, ha.const_smul c, hac.mono (Function.support_const_smul_subset c a),
      (fn_smul c u).trans (hua.const_smul c)⟩

variable {N p Ω}

omit [Fact (1 ≤ p)] in
/-- Membership of `smoothRestrictions` unfolded. -/
theorem SobolevEuclidean.mem_smoothRestrictions {u : SobolevEuclidean N 1 p Ω} :
    u ∈ SobolevEuclidean.smoothRestrictions N p Ω ↔
      ∃ v : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
        fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v :=
  Iff.rfl

omit [Fact (1 ≤ p)] in
/-- The smooth compactly supported representative of an element of `smoothRestrictions`. -/
theorem SobolevEuclidean.exists_contDiff_of_mem_smoothRestrictions
    {u : SobolevEuclidean N 1 p Ω} (hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω) :
    ∃ v : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v :=
  hu

/-- **The dense subspace**: under `HasSmoothDensity`, the restrictions of smooth compactly
supported functions are dense in `W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.HasSmoothDensity.dense_smoothRestrictions
    (h : SobolevEuclidean.HasSmoothDensity N p Ω) :
    Dense (SobolevEuclidean.smoothRestrictions N p Ω : Set (SobolevEuclidean N 1 p Ω)) := by
  intro u
  obtain ⟨v, hv, hvc, w, hw, hwu⟩ := h u
  exact mem_closure_iff_seq_limit.2 ⟨w, fun n ↦ ⟨v n, hv n, hvc n, hw n⟩, hwu⟩

/-- `HasSmoothDensity` with `C^1` approximants in place of `C^∞` ones (a weakening). -/
theorem SobolevEuclidean.HasSmoothDensity.exists_seq_contDiff_one
    (h : SobolevEuclidean.HasSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ n, ContDiff ℝ 1 (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
        ∃ w : ℕ → SobolevEuclidean N 1 p Ω,
          (∀ n, fn (w n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
            Tendsto w atTop (𝓝 u) :=
  let ⟨v, hv, hvc, w, hw, hwu⟩ := h u
  ⟨v, fun n ↦ (hv n).of_le (by simp), hvc, w, hw, hwu⟩

omit [Fact (1 ≤ p)] in
/-- **Uniqueness of continuous representatives up to the boundary**: two functions continuous on
`closure Ω` and both almost everywhere equal to `fn u` on `Ω` agree on `closure Ω`. They agree on
the open set `Ω` (`MeasureTheory.Measure.eqOn_open_of_ae_eq`), hence on its closure by
continuity. -/
theorem SobolevEuclidean.eqOn_closure_of_ae_eq_of_continuousOn (u : SobolevEuclidean N 1 p Ω)
    {v₁ v₂ : EuclideanSpace ℝ (Fin N) → ℝ}
    (h₁ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v₁)
    (h₂ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v₂)
    (hc₁ : ContinuousOn v₁ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hc₂ : ContinuousOn v₂ (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    EqOn v₁ v₂ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (Measure.eqOn_open_of_ae_eq (h₁.symm.trans h₂) Ω.isOpen (hc₁.mono subset_closure)
    (hc₂.mono subset_closure)).of_subset_closure hc₁ hc₂ subset_closure le_rfl

/-- **An extension domain has smooth density** ([brezis2011functional] Corollary 9.8 in its
abstract form, the density
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` on the
subspace `⊤`). -/
theorem IsSobolevExtensionDomain.hasSmoothDensity (h : IsSobolevExtensionDomain N p Ω)
    (hp' : p ≠ ⊤) : SobolevEuclidean.HasSmoothDensity N p Ω := fun u ↦
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp' h
    ⟨u, Submodule.mem_top⟩

/-- A `C^1` chart domain (with no boundedness of the boundary) has smooth density:
[brezis2011functional] Corollary 9.8. -/
theorem IsContDiffChartDomain.hasSmoothDensity {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity (d + 1) p Ω := fun u ↦
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto hp' hΩ u

/-- A `C^1` graph domain has smooth density, through `IsContDiffDomain.isContDiffChartDomain`. -/
theorem IsContDiffDomain.hasSmoothDensity {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity (d + 1) p Ω :=
  hΩ.isContDiffChartDomain.hasSmoothDensity hp'

/-- Every triangle with non-collinear vertices has smooth density
(`isSobolevExtensionDomainAll_openTriangleOpens`). -/
theorem EuclideanSpace.hasSmoothDensity_openTriangleOpens (A B C : EuclideanSpace ℝ (Fin 2))
    (h : LinearIndependent ℝ ![B - A, C - A]) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity 2 p (A.openTriangleOpens B C h) :=
  (isSobolevExtensionDomainAll_openTriangleOpens A B C h p).hasSmoothDensity hp'

end Predicates

/-! ### The segment property -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The segment property** (Adams–Fournier, *Sobolev Spaces*, 3.21): near each boundary point
of `Ω` a fixed direction `y` pushes the closure of `Ω` into `Ω`: there is a neighbourhood `U` of
the point with `z + t y ∈ Ω` for every `z ∈ closure Ω ∩ U` and `0 < t < 1`. It excludes sets
lying on both sides of a piece of their boundary (a slit) and cusps pointing inwards, and it is
what the translation construction of
`HasSegmentProperty.exists_seq_contDiff_hasCompactSupport_tendsto` needs. It holds for every
domain whose boundary is locally the graph of a continuous function
(`IsBoundaryOfClass.hasSegmentProperty`) and for every convex open set
(`Convex.hasSegmentProperty`). -/
def HasSegmentProperty (Ω : Set E) : Prop :=
  ∀ x ∈ frontier Ω, ∃ U ∈ 𝓝 x, ∃ y : E, ∀ z ∈ closure Ω ∩ U, ∀ t ∈ Ioo (0 : ℝ) 1, z + t • y ∈ Ω

/-- **A convex open set has the segment property**: with `x₀ ∈ Ω`, `ball x₀ δ ⊆ Ω`, the direction
at `x` is `x₀ − x`, on the neighbourhood `ball x (δ / 2)`: for `z ∈ closure Ω ∩ ball x (δ / 2)`
the point `z + t (x₀ − x) = (1 − t) z + t (x₀ + (z − x))` lies on the open segment from a point of
`closure Ω` to a point of `ball x₀ (δ / 2) ⊆ interior Ω`, hence in `interior Ω = Ω`
(`Convex.openSegment_closure_interior_subset_interior`). Boundedness is not needed. -/
theorem Convex.hasSegmentProperty {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    (hne : Ω.Nonempty) : HasSegmentProperty Ω := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  intro x _
  refine ⟨ball x (δ / 2), ball_mem_nhds x (half_pos hδ), x₀ - x, ?_⟩
  rintro z ⟨hz, hzx⟩ t ⟨ht0, ht1⟩
  have hmem : x₀ + (z - x) ∈ interior Ω := by
    rw [hΩ.interior_eq]
    refine hball ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm]
    exact (mem_ball.1 hzx).trans (half_lt_self hδ)
  have hseg := hc.openSegment_closure_interior_subset_interior hz hmem
  rw [hΩ.interior_eq] at hseg
  refine hseg ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  module

end Segment

section Graph

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
  {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A domain whose boundary is locally the graph of a continuous function has the segment
property**: at a boundary point `x₀` with the graph chart `(T, g)` on `ball x₀ r` the direction
is the rotated vertical `(r / 4) T⁻¹ e_N`, on the neighbourhood `ball x₀ (r / 2)`. A point
`z ∈ closure Ω ∩ ball x₀ (r / 2)` lies in the closed region `{g (init (T x)) ≤ (T x)_N}` (the open
ball meets `closure Ω` inside the closure of `Ω ∩ ball x₀ r`, the region above the graph), and
the translate `z + t y` stays in `ball x₀ r`, keeps the first `d` coordinates of `T z` and raises
the last one by `t r / 4 > 0`, so it lies strictly above the graph, in `Ω ∩ ball x₀ r`. Neither
openness nor boundedness of `Ω` is used. -/
theorem IsBoundaryOfClass.hasSegmentProperty (hV : V ⊆ {g | Continuous g})
    (h : IsBoundaryOfClass V Ω) : HasSegmentProperty Ω := by
  intro x₀ hx₀
  obtain ⟨r, hr, T, g, hg, hgraph⟩ := h x₀ hx₀
  have hgc : Continuous g := hV hg
  refine ⟨ball x₀ (r / 2), ball_mem_nhds x₀ (half_pos hr),
    (r / 4) • T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) (1 : ℝ)), ?_⟩
  rintro z ⟨hz, hzx⟩ t ⟨ht0, ht1⟩
  -- the translate stays in the ball
  have hnorm : ‖t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ))‖ = t * (r / 4) := by
    rw [norm_smul, norm_smul, LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg (by positivity)]
  have hball : z + t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ)) ∈ ball x₀ r := by
    rw [mem_ball, dist_eq_norm, add_sub_right_comm]
    calc ‖z - x₀ + t • (r / 4) • T.linearIsometryEquiv.symm
          (EuclideanSpace.single (Fin.last d) (1 : ℝ))‖
        ≤ ‖z - x₀‖ + t * (r / 4) := by rw [← hnorm]; exact norm_add_le _ _
      _ < r / 2 + r / 4 := by
          have := mem_ball.1 hzx
          rw [dist_eq_norm] at this
          exact add_lt_add_of_lt_of_le this (by nlinarith)
      _ ≤ r := by linarith
  -- `z` lies in the closed region above the graph
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin (d + 1)) |
      g (EuclideanSpace.init (T x)) ≤ T x (Fin.last d)} :=
    isClosed_le (hgc.comp (EuclideanSpace.continuous_init.comp T.continuous))
      (continuous_apply_last.comp T.continuous)
  have hzle : g (EuclideanSpace.init (T z)) ≤ T z (Fin.last d) := by
    have h1 : z ∈ closure (Ω ∩ ball x₀ r) :=
      isOpen_ball.closure_inter ⟨hz, ball_subset_ball (half_le_self hr.le) hzx⟩
    rw [hgraph] at h1
    exact closure_minimal (fun x hx ↦ le_of_lt hx.2) hclosed h1
  -- the coordinates of the translate
  have hT : T (z + t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ)))
      = T z + (t * (r / 4)) • EuclideanSpace.single (Fin.last d) (1 : ℝ) := by
    have := T.map_vadd z (t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ)))
    rw [vadd_eq_add, vadd_eq_add] at this
    simp only [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul]
      at this
    rw [add_comm z, smul_smul, this]
    exact add_comm _ _
  have hinit : EuclideanSpace.init (T (z + t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ)))) = EuclideanSpace.init (T z) := by
    rw [hT]
    ext j
    simp [EuclideanSpace.init_apply]
  have hlast : T (z + t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ))) (Fin.last d)
      = T z (Fin.last d) + t * (r / 4) := by
    rw [hT]
    simp
  have hmem : z + t • (r / 4) • T.linearIsometryEquiv.symm
      (EuclideanSpace.single (Fin.last d) (1 : ℝ)) ∈ Ω ∩ ball x₀ r := by
    rw [hgraph]
    refine ⟨hball, ?_⟩
    rw [hinit, hlast]
    have : 0 < t * (r / 4) := by positivity
    linarith
  exact hmem.1

/-- A `C^n` graph domain has the segment property. -/
theorem IsContDiffDomain.hasSegmentProperty {n : WithTop ℕ∞} (hΩ : IsContDiffDomain n Ω) :
    HasSegmentProperty Ω :=
  hΩ.isBoundaryOfClass.hasSegmentProperty fun _ hg ↦ ContDiff.continuous hg

/-- A Lipschitz graph domain has the segment property. -/
theorem IsLipschitzDomain.hasSegmentProperty (hΩ : IsLipschitzDomain Ω) :
    HasSegmentProperty Ω :=
  hΩ.isBoundaryOfClass.hasSegmentProperty fun _ hg ↦ hg.choose_spec.continuous

end Graph

/-! ### Translation to a translated domain

The translation `u ↦ u(· + h)` carries `W^{1,p}(Ω)` to `W^{1,p}(Ω − h)`, with the weak
derivatives translated. `Numlib/Analysis/Sobolev/Translate.lean` treats the case of an open set
invariant under the translation; the version here, for `Ω' = (· + h) ⁻¹' Ω`, belongs beside it. -/

section TranslatePreimage

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  {Ω Ω' : Opens E} {h : E}

/-- The translate `x ↦ φ (x - h)` of a test function on `Ω' = Ω − h`, as a test function on
`Ω`. -/
def TestFunction.compSubRightOfPreimage (φ : 𝓓(Ω', F))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) : 𝓓(Ω, F) where
  toFun x := φ (x - h)
  contDiff' := φ.contDiff.comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight h)
  tsupport_subset' := by
    have : tsupport (fun x ↦ φ (x - h)) = (Homeomorph.subRight h) ⁻¹' tsupport φ := by
      rw [tsupport, tsupport, (Homeomorph.subRight h).preimage_closure]
      rfl
    rw [this]
    intro x hx
    have := φ.tsupport_subset hx
    rw [hΩ'] at this
    simpa using this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The translate of a function locally integrable on `Ω` is locally integrable on `Ω − h`. -/
theorem LocallyIntegrableOn.comp_add_right_of_preimage [μ.IsAddRightInvariant] [ProperSpace E]
    {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    LocallyIntegrableOn (fun x ↦ u (x + h)) Ω' μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu
  rw [locallyIntegrableOn_iff Ω'.isOpen.isLocallyClosed]
  intro k hk hkc
  have hk' : (· + h) '' k ⊆ (Ω : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    have := hk hx
    rw [hΩ'] at this
    exact this
  have := hu ((· + h) '' k) hk' (hkc.image (continuous_id.add continuous_const))
  exact ((measurePreserving_add_right μ h).integrableOn_image
    (MeasurableEquiv.addRight h).measurableEmbedding).1 this

omit [NormedSpace ℝ E] in
/-- The translation `x ↦ x + h` carries `μ.restrict (Ω − h)` to `μ.restrict Ω`. -/
theorem measurePreserving_add_right_restrict_of_preimage [μ.IsAddRightInvariant]
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MeasurePreserving (· + h) (μ.restrict (Ω' : Set E)) (μ.restrict (Ω : Set E)) := by
  have := (measurePreserving_add_right μ h).restrict_preimage Ω.isOpen.measurableSet
  rwa [← hΩ'] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The translate of an `L^p(Ω)` function lies in `L^p(Ω − h)`. -/
theorem MeasureTheory.MemLp.comp_add_right_of_preimage [μ.IsAddRightInvariant] {u : E → F}
    {p : ℝ≥0∞} (hu : MemLp u p (μ.restrict (Ω : Set E)))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MemLp (fun x ↦ u (x + h)) p (μ.restrict (Ω' : Set E)) :=
  hu.comp_measurePreserving (measurePreserving_add_right_restrict_of_preimage hΩ')

/-- The change of variables `x ↦ x + h` from `Ω − h` to `Ω`, against a test function on `Ω − h`:
`∫_{Ω − h} ψ(x) u(x + h) dx = ∫_Ω ψ(x − h) u(x) dx`. -/
theorem integral_smul_comp_add_right_of_preimage [μ.IsAddRightInvariant] (u : E → F)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) (ψ : 𝓓(Ω', ℝ)) :
    ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ := by
  have e1 : ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x, ψ x • u (x + h) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ = ∫ x, ψ (x - h) • u x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      have := (ψ.compSubRightOfPreimage hΩ').eq_zero_of_notMem hx
      exact by rw [show ψ (x - h) = 0 from this, zero_smul]
  rw [e1, e2, ← integral_add_right_eq_self (fun x ↦ ψ (x - h) • u x) h]
  simp only [add_sub_cancel_right]

/-- **Translation commutes with the weak derivative, from `Ω` to `Ω − h`**: if `w` is a weak
derivative of `u` along the tuple `y` on `Ω`, then `w(· + h)` is one of `u(· + h)` on `Ω − h`.
The test function `φ` on `Ω − h` is traded for its translate `φ(· − h)`, a test function on
`Ω`. -/
theorem HasWeakIteratedLineDerivOn.comp_add_right_of_preimage [μ.IsAddRightInvariant]
    [ProperSpace E] {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u (x + h)) (fun x ↦ w (x + h)) Ω' μ where
  locallyIntegrableOn := LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn hΩ'
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn_weakDeriv hΩ'
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : E → ℝ) = fun x ↦ φ (x - h) :=
      ⟨φ.compSubRightOfPreimage hΩ', rfl⟩
    have hψd : ∀ x, iteratedFDeriv ℝ n (ψ : E → ℝ) x y
        = iteratedFDeriv ℝ n (φ : E → ℝ) (x - h) y := fun x ↦ by
      rw [hψ, iteratedFDeriv_comp_sub']
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • u (x + h) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n ψ x y • u x ∂μ := by
      have := integral_smul_comp_add_right_of_preimage (μ := μ) u hΩ' (φ.iteratedFDerivApply n y)
      simp only [TestFunction.iteratedFDerivApply_apply] at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψd])
    have e2 : ∫ x in (Ω' : Set E), φ x • w (x + h) ∂μ = ∫ x in (Ω : Set E), ψ x • w x ∂μ := by
      rw [integral_smul_comp_add_right_of_preimage (μ := μ) w hΩ' φ]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψ])
    rw [e1, e2, hu.integral_smul_eq ψ]

end TranslatePreimage

/-! ### Small general lemmas -/

section General

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

omit [Fact (1 ≤ p)] in
/-- The partial derivative `∂_j u` of `u ∈ W^{1,p}(Ω)` is a weak derivative of `fn u` along
`e_j`. (Also `ExtensionHigher.weakDeriv_hasWeakIteratedLineDerivOn_single`.) -/
theorem SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single (u : SobolevEuclidean N 1 p Ω)
    (j : Fin N) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] (fn u)
      (weakDeriv u (MultiIndexLE.single j)) Ω volume := by
  have := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single j)).of_perm
    (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) j)
  rwa [EuclideanSpace.basisFun_toBasis_apply] at this

/-- **Membership of `W^{1,p}(Ω)` from the partial derivatives**: a function of `L^p(Ω)` with a
weak derivative in `L^p(Ω)` along each `e_j` lies in `W^{1,p}(Ω)`. -/
theorem SobolevEuclidean.memSobolevMultiIndex_one_of_forall {F : EuclideanSpace ℝ (Fin N) → ℝ}
    (hF : MemLp F p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {G : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (hG : ∀ j, MemLp (G j) p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (hFG : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F (G j) Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis F 1 p Ω volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  refine ⟨hF, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hF.locallyIntegrableOn hp), hF⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    refine ⟨G i, ?_, hG i⟩
    have h' : HasWeakIteratedLineDerivOn
        ![((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i]
        F (G i) Ω volume := by
      rw [EuclideanSpace.basisFun_toBasis_apply]
      exact hFG i
    exact h'.of_perm (multiIndexTuple_single_perm
      ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → EuclideanSpace ℝ (Fin N)) i).symm

omit [Fact (1 ≤ p)] in
/-- **Uniqueness of the partial derivatives**: if `fn u` is almost everywhere `F` on `Ω` and
`G` is a weak derivative of `F` along `e_j` on `Ω`, then `∂_j u` is almost everywhere `G`. -/
theorem SobolevEuclidean.weakDeriv_single_ae_eq (u : SobolevEuclidean N 1 p Ω)
    {F G : EuclideanSpace ℝ (Fin N) → ℝ}
    (hF : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] F) {j : Fin N}
    (hG : HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F G Ω volume) :
    weakDeriv u (MultiIndexLE.single j) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      G :=
  (ae_restrict_iff' Ω.isOpen.measurableSet).2
    (((SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u j).congr_ae hF
      (EventuallyEq.refl _ _)).ae_eq hG)

/-- The support of `x ↦ θ (x + h)` lies in the translate of the support of `θ`. -/
theorem tsupport_comp_add_right_subset {E : Type*} [NormedAddCommGroup E] {θ : E → ℝ} (h : E) :
    tsupport (fun x ↦ θ (x + h)) ⊆ (fun x ↦ x + h) ⁻¹' tsupport θ :=
  closure_minimal (fun y hy ↦ subset_closure (by simpa [Function.support] using hy))
    ((isClosed_tsupport θ).preimage (continuous_add_const h))

end General

/-! ### One piece of the construction -/

section Piece

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

open SobolevMultiIndex

omit [Fact (1 ≤ p)] in
/-- **One piece of the translation construction.** For `ũ ∈ W^{1,p}(Ω)` with partial
derivatives `w j` (as functions), a smooth `θ` and a translation `h` such that every
`z ∈ closure Ω` with `z + h ∈ tsupport θ` lies in a set `U` on which `z + h ∈ Ω`, the function
`F = 1_{Ω − h} · χ · θ(· + h) · ũ(· + h)`, with `χ` a smooth cut-off equal to `1` on `closure Ω`
and supported in `(Ω − h) ∪ (tsupport θ − h)ᶜ`, has compact support, lies in `L^p(ℝ^N)`, has
weak derivatives `G j ∈ L^p(ℝ^N)` along each `e_j` on the whole space, equals the translate
`(θ ũ)^0(· + h)` of the zero extension on `closure Ω`, has `G j = (θ w_j + ∂_j θ ũ)^0(· + h)`
on `Ω`, and is continuous when `ũ` is continuous on `closure Ω`. -/
theorem SobolevEuclidean.exists_translatePiece (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {ũ : 𝔼 → ℝ} {w : Fin N → 𝔼 → ℝ} (hũp : MemLp ũ p (volume.restrict (Ω : Set 𝔼)))
    (hw : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] ũ (w j) Ω volume)
    (hwp : ∀ j, MemLp (w j) p (volume.restrict (Ω : Set 𝔼)))
    {θ : 𝔼 → ℝ} (hθ : ContDiff ℝ ∞ θ) {U : Set 𝔼} {h : 𝔼}
    (hθU' : ∀ z, z + h ∈ tsupport θ → z ∈ U)
    (hseg : ∀ z ∈ closure (Ω : Set 𝔼), z ∈ U → z + h ∈ Ω) :
    ∃ (F : 𝔼 → ℝ) (G : Fin N → 𝔼 → ℝ),
      HasCompactSupport F ∧ MemLp F p volume ∧ (∀ j, MemLp (G j) p volume) ∧
      (∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F (G j) ⊤ volume) ∧
      (∀ z ∈ closure (Ω : Set 𝔼), F z = (Ω : Set 𝔼).indicator (fun x ↦ θ x * ũ x) (z + h)) ∧
      (∀ j, ∀ z ∈ (Ω : Set 𝔼), G j z = (Ω : Set 𝔼).indicator
        (fun x ↦ θ x * w j x + fderiv ℝ θ x (EuclideanSpace.single j (1 : ℝ)) * ũ x) (z + h)) ∧
      (ContinuousOn ũ (closure (Ω : Set 𝔼)) → Continuous F) := by
  -- the translated domain
  obtain ⟨Ω', hΩ'⟩ : ∃ Ω' : Opens 𝔼, (Ω' : Set 𝔼) = (fun x ↦ x + h) ⁻¹' Ω :=
    ⟨⟨(fun x ↦ x + h) ⁻¹' Ω, Ω.isOpen.preimage (continuous_add_const h)⟩, rfl⟩
  have hmemΩ' : ∀ x, x ∈ (Ω' : Set 𝔼) ↔ x + h ∈ Ω := fun x ↦ by rw [hΩ']; exact Iff.rfl
  -- the open neighbourhood `V` of `closure Ω`
  obtain ⟨V, hVdef⟩ : ∃ V : Set 𝔼,
      V = (Ω' : Set 𝔼) ∪ ((fun x ↦ x + h) ⁻¹' tsupport θ)ᶜ := ⟨_, rfl⟩
  have hVo : IsOpen V := hVdef ▸ Ω'.isOpen.union
    ((isClosed_tsupport θ).preimage (continuous_add_const h)).isOpen_compl
  have hclV : closure (Ω : Set 𝔼) ⊆ V := by
    intro z hz
    rw [hVdef]
    by_cases hzθ : z + h ∈ tsupport θ
    · exact Or.inl ((hmemΩ' z).2 (hseg z hz (hθU' z hzθ)))
    · exact Or.inr hzθ
  -- the cut-off `χ`
  obtain ⟨L, hLc, hL, hLV⟩ := exists_compact_between hb.isCompact_closure hVo hclV
  obtain ⟨χ, hχ, hχ1, hχs, -⟩ := hb.isCompact_closure.exists_contDiff_eqOn_one isOpen_interior hL
  have hχc : HasCompactSupport χ :=
    hLc.of_isClosed_subset (isClosed_tsupport χ) (hχs.trans interior_subset)
  have hχV : tsupport χ ⊆ V := hχs.trans (interior_subset.trans hLV)
  -- the multiplier `α`
  obtain ⟨α, hαdef⟩ : ∃ α : 𝔼 → ℝ, α = fun x ↦ χ x * θ (x + h) := ⟨_, rfl⟩
  have hα : ContDiff ℝ ∞ α := hαdef ▸ hχ.mul (hθ.comp (contDiff_id.add contDiff_const))
  have hαc : HasCompactSupport α := hαdef ▸ hχc.mul_right
  have hαΩ' : tsupport α ⊆ Ω' := by
    intro x hx
    rw [hαdef] at hx
    have h1 : x ∈ tsupport χ :=
      tsupport_mul_subset_left (f := χ) (g := fun x ↦ θ (x + h)) hx
    have h2 : x + h ∈ tsupport θ :=
      tsupport_comp_add_right_subset h
        (tsupport_mul_subset_right (f := χ) (g := fun x ↦ θ (x + h)) hx)
    have := hχV h1
    rw [hVdef] at this
    rcases this with h3 | h3
    · exact h3
    · exact absurd h2 h3
  have hα1 : ∀ z ∈ closure (Ω : Set 𝔼), α z = θ (z + h) := fun z hz ↦ by
    rw [hαdef]
    simp only [hχ1 hz, Pi.one_apply, one_mul]
  have hαd : ∀ z ∈ (Ω : Set 𝔼), ∀ v, fderiv ℝ α z v = fderiv ℝ θ (z + h) v := by
    intro z hz v
    have hχ0 : fderiv ℝ χ z = 0 := by
      have : χ =ᶠ[𝓝 z] fun _ ↦ (1 : ℝ) :=
        Filter.eventually_of_mem (Ω.isOpen.mem_nhds hz) fun y hy ↦ hχ1 (subset_closure hy)
      rw [this.fderiv_eq, fderiv_fun_const]
      rfl
    have hθh : DifferentiableAt ℝ (fun x ↦ θ (x + h)) z :=
      (differentiableAt_comp_add_right h).2 (hθ.differentiable (by simp) (z + h))
    rw [hαdef, fderiv_fun_mul (hχ.differentiable (by simp) z) hθh]
    simp only [hχ0, hχ1 (subset_closure hz), Pi.one_apply, smul_zero, one_smul]
    rw [fderiv_comp_add_right, add_zero]
  -- the piece
  obtain ⟨F, hFdef⟩ : ∃ F : 𝔼 → ℝ, F = (Ω' : Set 𝔼).indicator fun x ↦ α x • ũ (x + h) :=
    ⟨_, rfl⟩
  have hFc : HasCompactSupport F := by
    refine hαc.mono fun x hx ↦ ?_
    rw [hFdef] at hx
    intro hαx
    apply hx
    by_cases hxΩ' : x ∈ (Ω' : Set 𝔼)
    · rw [Set.indicator_of_mem hxΩ', hαx, zero_smul]
    · exact Set.indicator_of_notMem hxΩ' _
  -- the translate of `ũ` and of its derivatives on `Ω'`
  have hũ' : MemLp (fun x ↦ ũ (x + h)) p (volume.restrict (Ω' : Set 𝔼)) :=
    hũp.comp_add_right_of_preimage hΩ'
  have hw' : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)]
      (fun x ↦ ũ (x + h)) (fun x ↦ w j (x + h)) Ω' volume :=
    fun j ↦ (hw j).comp_add_right_of_preimage hΩ'
  have hwp' : ∀ j, MemLp (fun x ↦ w j (x + h)) p (volume.restrict (Ω' : Set 𝔼)) :=
    fun j ↦ (hwp j).comp_add_right_of_preimage hΩ'
  -- the weak derivatives of `F` on the whole space
  obtain ⟨G, hGdef⟩ : ∃ G : Fin N → 𝔼 → ℝ, ∀ j, G j = (Ω' : Set 𝔼).indicator fun x ↦
      α x • w j (x + h) + fderiv ℝ α x (EuclideanSpace.single j (1 : ℝ)) • ũ (x + h) :=
    ⟨_, fun _ ↦ rfl⟩
  have hFG : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F (G j)
      ⊤ volume := fun j ↦ by
    rw [hFdef, hGdef j]
    exact (hw' j).indicator_smul_of_tsupport_inter_subset le_top hα (fun x hx ↦ hαΩ' hx.1)
  -- the `L^p` memberships
  obtain ⟨M, hM⟩ := hαc.exists_bound_of_continuous hα.continuous
  have hFp : MemLp F p volume := by
    rw [hFdef]
    have := hũ'.indicator_smul_of_le (Ω := ⊤) hα.continuous
      (M := M) (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM x))
    rwa [Measure.restrict_coe_top] at this
  have hGp : ∀ j, MemLp (G j) p volume := fun j ↦ by
    obtain ⟨M', hM'⟩ := HasCompactSupport.exists_bound_of_continuous
      (hαc.fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ)))
      ((hα.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
    have h1 := (hwp' j).indicator_smul_of_le (Ω := ⊤) hα.continuous
      (M := M) (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM x))
    have h2 := hũ'.indicator_smul_of_le (Ω := ⊤)
      ((hα.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
      (M := M') (fun x ↦ (Real.norm_eq_abs _).symm.trans_le (hM' x))
    rw [Measure.restrict_coe_top] at h1 h2
    refine (h1.add h2).ae_eq (Eventually.of_forall fun x ↦ ?_)
    rw [hGdef j]
    by_cases hx : x ∈ (Ω' : Set 𝔼) <;> simp [hx]
  refine ⟨F, G, hFc, hFp, hGp, hFG, ?_, ?_, ?_⟩
  · -- the values on `closure Ω`
    intro z hz
    rw [hFdef]
    by_cases hzΩ : z + h ∈ (Ω : Set 𝔼)
    · rw [Set.indicator_of_mem ((hmemΩ' z).2 hzΩ), Set.indicator_of_mem hzΩ, hα1 z hz,
        smul_eq_mul]
    · rw [Set.indicator_of_notMem (fun h' ↦ hzΩ ((hmemΩ' z).1 h')), Set.indicator_of_notMem hzΩ]
  · -- the weak derivatives on `Ω`
    intro j z hz
    rw [hGdef j]
    by_cases hzΩ : z + h ∈ (Ω : Set 𝔼)
    · rw [Set.indicator_of_mem ((hmemΩ' z).2 hzΩ), Set.indicator_of_mem hzΩ,
        hα1 z (subset_closure hz), hαd z hz, smul_eq_mul, smul_eq_mul]
    · rw [Set.indicator_of_notMem (fun h' ↦ hzΩ ((hmemΩ' z).1 h')), Set.indicator_of_notMem hzΩ]
  · -- continuity
    intro hũc
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ (Ω' : Set 𝔼)
    · have hx' : x + h ∈ (Ω : Set 𝔼) := (hmemΩ' x).1 hx
      have hc : ContinuousAt (fun y ↦ α y • ũ (y + h)) x := by
        refine hα.continuous.continuousAt.smul ?_
        have : ContinuousAt ũ (x + h) :=
          hũc.continuousAt (mem_nhds_iff.2 ⟨Ω, subset_closure, Ω.isOpen, hx'⟩)
        exact ContinuousAt.comp (g := ũ) (f := fun y ↦ y + h) this
          (continuous_add_const h).continuousAt
      refine hc.congr ?_
      filter_upwards [Ω'.isOpen.mem_nhds hx] with y hy
      rw [hFdef, Set.indicator_of_mem hy]
    · have hxα : x ∉ tsupport α := fun h' ↦ hx (hαΩ' h')
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [(isClosed_tsupport α).isOpen_compl.mem_nhds hxα] with y hy
      rw [hFdef]
      by_cases hyΩ' : y ∈ (Ω' : Set 𝔼)
      · rw [Set.indicator_of_mem hyΩ', image_eq_zero_of_notMem_tsupport hy, zero_smul]
      · rw [Set.indicator_of_notMem hyΩ']

end Piece

/-! ### Mollification of a compactly supported `W^{1,p}(ℝ^N)` function -/

section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}

/-- **Mollification of a compactly supported `W^{1,p}(ℝ^N)` function**: for `G ∈ W^{1,p}(ℝ^N)`
with compact support, `1 ≤ p < ∞`, `η > 0` and `ε > 0`, there is a smooth compactly supported
`v` with `‖v − G‖_{W^{1,p}(ℝ^N)} < η` and, if `G` is continuous, `|v − G| < ε` everywhere: a
mollification `ρ_δ ⋆ G` for `δ` small
(`MemSobolev.tendsto_sobolevNorm_convolution_sub`, `ContDiffBump.dist_normed_convolution_le` with
the uniform continuity of `G`). -/
theorem MemSobolev.exists_contDiff_hasCompactSupport_sobolevNorm_sub_lt {G : E → ℝ}
    (hG : MemSobolev G 1 p ⊤ μ) (hGc : HasCompactSupport G) (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {η : ℝ≥0∞} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ sobolevNorm (v - G) 1 p ⊤ μ < η ∧
      (Continuous G → ∀ x, dist (v x) (G x) < ε) := by
  obtain ⟨φ, hφ⟩ := exists_seq_contDiffBump_tendsto_rOut_zero E
  have h1 : ∀ᶠ k in atTop,
      sobolevNorm ((φ k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G - G) 1 p ⊤ μ < η :=
    (hG.tendsto_sobolevNorm_convolution_sub hφ hp hp').eventually_lt_const hη
  have h2 : Continuous G → ∀ᶠ k in atTop,
      ∀ x, dist (((φ k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) x) (G x) < ε := by
    intro hGc'
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1
      (hGc.uniformContinuous_of_continuous hGc') (ε / 2) (half_pos hε)
    filter_upwards [hφ.eventually_lt_const hδ] with k hk x
    refine lt_of_le_of_lt ((φ k).dist_normed_convolution_le hGc'.aestronglyMeasurable
      fun y hy ↦ ?_) (half_lt_self hε)
    exact (hδε (lt_trans (mem_ball.1 hy) hk)).le
  have h3 : ∀ᶠ k in atTop,
      sobolevNorm ((φ k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G - G) 1 p ⊤ μ < η ∧
      (Continuous G →
        ∀ x, dist (((φ k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] G) x) (G x) < ε) := by
    by_cases hGc' : Continuous G
    · exact (h1.and (h2 hGc')).mono fun k hk ↦ ⟨hk.1, fun _ ↦ hk.2⟩
    · exact h1.mono fun k hk ↦ ⟨hk, fun h ↦ absurd h hGc'⟩
  obtain ⟨k, hk1, hk2⟩ := h3.exists
  have hloc : LocallyIntegrable G μ := hG.memLp_top.locallyIntegrable hp
  exact ⟨_, hloc.contDiff_convolution_normed (φ k),
    (φ k).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hGc, hk1, hk2⟩

end Mollify

/-! ### The translation estimate -/

section Estimate

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

open SobolevMultiIndex

/-- **The translation estimate**: an element `d` of `L^p(Ω)` which is, on `Ω`, the sum over `i`
of the differences `H_i(· + t y_i) − H_i` of translates of `L^p(ℝ^N)` functions `H_i` has norm
at most `∑ i, ‖τ_{t y_i} H_i − H_i‖_{L^p(ℝ^N)}` (Minkowski, and `L^p(Ω) ≤ L^p(ℝ^N)`). -/
theorem SobolevEuclidean.norm_le_sum_norm_translateCurve_sub {ι : Type*} [Fintype ι]
    (d : Lp ℝ p (volume.restrict (Ω : Set 𝔼)))
    (H : ι → Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) (y : ι → 𝔼) (t : ℝ)
    (hd : (d : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun z ↦ ∑ i, (H i (z + t • y i) - H i z)) :
    ‖d‖ ≤ ∑ i, ‖Lp.translateCurve ℝ p (y i) (H i) t - H i‖ := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- each summand is the function of an `L^p(ℝ^N)` element
  have hae : ∀ i, (fun z ↦ H i (z + t • y i) - H i z) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      (Lp.translateCurve ℝ p (y i) (H i) t - H i :
        Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) := by
    intro i
    have h1 := Lp.coeFn_sub (Lp.translateCurve ℝ p (y i) (H i) t) (H i)
    have h2 := Lp.coeFn_translateCurve (y i) (H i) t
    refine ae_mono (Measure.restrict_mono le_top le_rfl) ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, Pi.sub_apply, hz2]
  obtain ⟨g, hgdef⟩ : ∃ g : ι → 𝔼 → ℝ, ∀ i, g i = (Lp.translateCurve ℝ p (y i) (H i) t - H i :
      Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) := ⟨_, fun _ ↦ rfl⟩
  have hd' : (d : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] ∑ i, g i := by
    refine hd.trans ?_
    have := Filter.eventually_all.2 hae
    filter_upwards [this] with z hz
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ (hz i).trans (by rw [hgdef i])
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _]
  simp only [ofReal_norm, Lp.enorm_def]
  rw [eLpNorm_congr_ae hd']
  refine le_trans (MeasureTheory.eLpNorm_sum_le_of_norm (a := g) (s := Finset.univ) hp) ?_
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [hgdef i]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono le_top le_rfl)

end Estimate

/-! ### The translation construction -/

section Construction

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

open SobolevMultiIndex

/-- The derivatives of a partition of unity `θ₀ + ∑ θ_i = 1` sum to zero. -/
theorem fderiv_add_sum_eq_zero_of_partition {ι : Type*} [Fintype ι] {θ₀ : 𝔼 → ℝ}
    {θ : ι → 𝔼 → ℝ} (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ : ∀ i, ContDiff ℝ ∞ (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (z v : 𝔼) :
    fderiv ℝ θ₀ z v + ∑ i, fderiv ℝ (θ i) z v = 0 := by
  have h1 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x)
      (fderiv ℝ θ₀ z + ∑ i, fderiv ℝ (θ i) z) z :=
    (hθ₀.differentiable (by simp) z).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ ↦ ((hθ i).differentiable (by simp) z).hasFDerivAt)
  have h2 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x) (0 : 𝔼 →L[ℝ] ℝ) z := by
    have : (fun x ↦ θ₀ x + ∑ i, θ i x) = fun _ ↦ (1 : ℝ) := funext hsum
    rw [this]
    exact hasFDerivAt_const 1 z
  have := congrArg (fun L : 𝔼 →L[ℝ] ℝ ↦ L v) (h1.unique h2)
  simpa using this

/-- **The translate approximation, at the level of functions.** For a bounded `Ω` with the
segment property, `ũ ∈ W^{1,p}(Ω)` with partial derivatives `w j`, and `ε > 0`, there is a
compactly supported `Fs ∈ W^{1,p}(ℝ^N)` with weak derivatives `Gs j`, built from a partition of
unity `θ₀ + ∑ θ_i = 1` subordinate to the segment-property neighbourhoods and the pieces of
`SobolevEuclidean.exists_translatePiece` at the translations `t y_i`, such that: on `Ω`,
`Fs − ũ` and `Gs j − w j` are the sums over `i` of the differences `H(· + t y_i) − H` of
translates of the `L^p(ℝ^N)` functions `H = (θ_i ũ)^0`, respectively `(θ_i w_j + ∂_j θ_i ũ)^0`,
and the total `L^p(ℝ^N)` size of these differences is less than `ε`; and, when `ũ` is
continuous on `closure Ω`, `Fs` is continuous and within `ε` of `ũ` on `closure Ω`. The
statement is kept free of the typed space `W^{1,p}(Ω)` so that its long proof elaborates
cheaply (every `obtain` under a goal mentioning `W^{1,p}(Ω)` costs seconds);
`HasSegmentProperty.exists_hasCompactSupport_norm_restrictL_sub_lt` reads it in `W^{1,p}(Ω)`. -/
theorem HasSegmentProperty.exists_translateApprox
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hΩ : HasSegmentProperty (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    {ũ : 𝔼 → ℝ} {w : Fin N → 𝔼 → ℝ} (hũp : MemLp ũ p (volume.restrict (Ω : Set 𝔼)))
    (hw : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] ũ (w j) Ω volume)
    (hwp : ∀ j, MemLp (w j) p (volume.restrict (Ω : Set 𝔼))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Fs : 𝔼 → ℝ) (Gs : Fin N → 𝔼 → ℝ), HasCompactSupport Fs ∧
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis Fs 1 p ⊤ volume ∧
      (∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] Fs (Gs j) ⊤ volume) ∧
      (∃ (s : Finset 𝔼) (H0 : s → Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)))
        (H1 : s → Fin N → Lp ℝ p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼))) (y : s → 𝔼) (t : ℝ),
        ((fun z ↦ Fs z - ũ z) =ᵐ[volume.restrict (Ω : Set 𝔼)]
          fun z ↦ ∑ i, (H0 i (z + t • y i) - H0 i z)) ∧
        (∀ j, (fun z ↦ Gs j z - w j z) =ᵐ[volume.restrict (Ω : Set 𝔼)]
          fun z ↦ ∑ i, (H1 i j (z + t • y i) - H1 i j z)) ∧
        ∑ i, ‖Lp.translateCurve ℝ p (y i) (H0 i) t - H0 i‖
          + ∑ j, ∑ i, ‖Lp.translateCurve ℝ p (y i) (H1 i j) t - H1 i j‖ < ε) ∧
      (ContinuousOn ũ (closure (Ω : Set 𝔼)) →
        Continuous Fs ∧ ∀ z ∈ closure (Ω : Set 𝔼), dist (Fs z) (ũ z) < ε) := by
  classical
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- Step 0: the finite cover of the frontier and the partition of unity
  have hK : IsCompact (frontier (Ω : Set 𝔼)) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  choose! U hU y hy using hΩ
  obtain ⟨s, hs, hcov⟩ := hK.elim_nhds_subcover (fun x ↦ interior (U x))
    fun x hx ↦ interior_mem_nhds.2 (hU x hx)
  obtain ⟨θ₀, θ, hθ₀, hθ, -, hθ01, hsum, hθc, hθU, hθ₀f⟩ :=
    hK.exists_contDiff_partitionOfUnity (ι := s) (U := fun i ↦ interior (U i))
      (fun _ ↦ isOpen_interior) (fun z hz ↦ by
        obtain ⟨x, hxs, hx⟩ := mem_iUnion₂.1 (hcov hz)
        exact mem_iUnion.2 ⟨⟨x, hxs⟩, hx⟩)
  -- the thickening radii: `tsupport θ_i − v ⊆ interior (U i)` for `‖v‖ < δ i`
  have hδ : ∀ i : s, ∃ δ > 0, ∀ v : 𝔼, ‖v‖ < δ →
      ∀ z, z + v ∈ tsupport (θ i) → z ∈ interior (U i) := by
    intro i
    obtain ⟨δ, hδ, hδU⟩ := (hθc i).exists_thickening_subset_open isOpen_interior (hθU i)
    refine ⟨δ, hδ, fun v hv z hz ↦ hδU ?_⟩
    rw [Metric.mem_thickening_iff]
    exact ⟨z + v, hz, by rw [dist_eq_norm]; simpa using hv⟩
  choose δ hδpos hδ using hδ
  -- the zero extensions whose translates enter
  obtain ⟨H0f, hH0def⟩ : ∃ H0f : s → 𝔼 → ℝ,
      ∀ i, H0f i = (Ω : Set 𝔼).indicator fun x ↦ θ i x * ũ x := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨H1f, hH1def⟩ : ∃ H1f : s → Fin N → 𝔼 → ℝ, ∀ i j, H1f i j = (Ω : Set 𝔼).indicator
      fun x ↦ θ i x * w j x + fderiv ℝ (θ i) x (EuclideanSpace.single j (1 : ℝ)) * ũ x :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hθ1 : ∀ (i : s) (x : 𝔼), x ∈ (Ω : Set 𝔼) → ‖θ i x‖ ≤ 1 := fun i x _ ↦ by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [(hθ01 i x).1], (hθ01 i x).2⟩
  have hH0 : ∀ i, MemLp (H0f i) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := fun i ↦ by
    rw [hH0def i, Measure.restrict_coe_top]
    exact memLp_indicator_smul_of_forall_norm_le (μ := volume) Ω.isOpen.measurableSet (hθ1 i)
      (hθ i).continuous.aestronglyMeasurable hũp
  have hH1 : ∀ i j, MemLp (H1f i j) p (volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)) := fun i j ↦ by
    rw [hH1def i j, Measure.restrict_coe_top]
    have hcont : Continuous fun x ↦ fderiv ℝ (θ i) x (EuclideanSpace.single j (1 : ℝ)) :=
      (((hθ i).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
    obtain ⟨M, hM⟩ := HasCompactSupport.exists_bound_of_continuous
      ((hθc i).fderiv_apply ℝ (EuclideanSpace.single j (1 : ℝ))) hcont
    have h1 := memLp_indicator_smul_of_forall_norm_le (μ := volume) Ω.isOpen.measurableSet
      (hθ1 i) (hθ i).continuous.aestronglyMeasurable (hwp j)
    have h2 := memLp_indicator_smul_of_forall_norm_le (μ := volume) Ω.isOpen.measurableSet
      (g := fun x ↦ fderiv ℝ (θ i) x (EuclideanSpace.single j (1 : ℝ))) (fun x _ ↦ hM x)
      hcont.aestronglyMeasurable hũp
    refine (h1.add h2).ae_eq (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ (Ω : Set 𝔼) <;> simp [hx]
  -- the translation error
  obtain ⟨err, herrdef⟩ : ∃ err : ℝ → ℝ, ∀ t, err t
      = ∑ i : s, ‖Lp.translateCurve ℝ p (y i) ((hH0 i).toLp (H0f i)) t - (hH0 i).toLp (H0f i)‖
        + ∑ j, ∑ i : s, ‖Lp.translateCurve ℝ p (y i) ((hH1 i j).toLp (H1f i j)) t
          - (hH1 i j).toLp (H1f i j)‖ := ⟨_, fun _ ↦ rfl⟩
  have herr_cont : Continuous err := by
    rw [show err = fun t ↦ _ from funext herrdef]
    exact (continuous_finsetSum (Finset.univ : Finset s) fun i _ ↦
        ((Lp.continuous_translateCurve (y i) ((hH0 i).toLp (H0f i)) hp').sub
          continuous_const).norm).add
      (continuous_finsetSum (Finset.univ : Finset (Fin N)) fun j _ ↦
        continuous_finsetSum (Finset.univ : Finset s) fun i _ ↦
          ((Lp.continuous_translateCurve (y i) ((hH1 i j).toLp (H1f i j)) hp').sub
            continuous_const).norm)
  have herr0 : err 0 = 0 := by
    rw [herrdef]
    simp [Lp.translateCurve_zero]
  -- the uniform-continuity moduli, when `ũ` is continuous
  obtain ⟨ε', hε'pos, hε'⟩ : ∃ ε' > 0, (s.card : ℝ) * ε' < ε := by
    refine ⟨ε / (s.card + 1), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [hε, (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)]
  have hmul : ∀ i : s, Tendsto (fun t : ℝ ↦ t * ‖y i‖) (𝓝 0) (𝓝 0) := fun i ↦ by
    have := (continuous_mul_const ‖y i‖).tendsto (0 : ℝ)
    simpa using this
  -- everything small for `t` small
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
  have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i : s, t * ‖y i‖ < δ i :=
    eventually_nhdsWithin_of_eventually_nhds
      (Filter.eventually_all.2 fun i ↦ (hmul i).eventually_lt_const (hδpos i))
  have hev4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), err t < ε := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have := herr_cont.tendsto 0
    rw [herr0] at this
    exact this.eventually_lt_const hε
  have hev5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContinuousOn ũ (closure (Ω : Set 𝔼)) →
      ∀ i : s, ∀ z ∈ closure (Ω : Set 𝔼), ∀ z' ∈ closure (Ω : Set 𝔼), dist z' z ≤ t * ‖y i‖ →
        dist (θ i z' * ũ z') (θ i z * ũ z) < ε' := by
    by_cases hũc : ContinuousOn ũ (closure (Ω : Set 𝔼))
    · have hmod : ∀ i : s, ∃ η > 0, ∀ z ∈ closure (Ω : Set 𝔼), ∀ z' ∈ closure (Ω : Set 𝔼),
          dist z' z < η → dist (θ i z' * ũ z') (θ i z * ũ z) < ε' := fun i ↦ by
        have hunif : UniformContinuousOn (fun x ↦ θ i x * ũ x) (closure (Ω : Set 𝔼)) :=
          hb.isCompact_closure.uniformContinuousOn_of_continuous
            ((hθ i).continuous.continuousOn.mul hũc)
        obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.1 hunif ε' hε'pos
        exact ⟨η, hη, fun z hz z' hz' hd ↦ h z' hz' z hz hd⟩
      choose η hηpos hη using hmod
      refine eventually_nhdsWithin_of_eventually_nhds ((Filter.eventually_all.2 fun i ↦
        (hmul i).eventually_lt_const (hηpos i)).mono fun t ht _ i z hz z' hz' hd ↦ ?_)
      exact hη i z hz z' hz' (hd.trans_lt (ht i))
    · exact Eventually.of_forall fun _ h ↦ absurd h hũc
  obtain ⟨t, ht0, ht1, htδ, hterr, htunif⟩ :=
    (hev1.and (hev2.and (hev3.and (hev4.and hev5)))).exists
  -- Step 1: the pieces at `t`
  have hΩint : ∀ z ∈ closure (Ω : Set 𝔼), z ∉ frontier (Ω : Set 𝔼) → z ∈ (Ω : Set 𝔼) := by
    intro z hz hzf
    by_contra h
    exact hzf ⟨hz, fun h' ↦ h (by rwa [Ω.isOpen.interior_eq] at h')⟩
  obtain ⟨F₀, G₀, hF₀c, hF₀p, hG₀p, hF₀G, hF₀val, hG₀val, hF₀cont⟩ :=
    SobolevEuclidean.exists_translatePiece hb hũp hw hwp hθ₀ (U := (frontier (Ω : Set 𝔼))ᶜ)
      (h := 0) (fun z hz ↦ by rw [add_zero] at hz; exact Set.disjoint_left.1 hθ₀f hz)
      (fun z hz hzf ↦ by rw [add_zero]; exact hΩint z hz hzf)
  have hpieces : ∀ i : s, ∃ (F : 𝔼 → ℝ) (G : Fin N → 𝔼 → ℝ),
      HasCompactSupport F ∧ MemLp F p volume ∧ (∀ j, MemLp (G j) p volume) ∧
      (∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] F (G j) ⊤ volume) ∧
      (∀ z ∈ closure (Ω : Set 𝔼),
        F z = (Ω : Set 𝔼).indicator (fun x ↦ θ i x * ũ x) (z + t • y i)) ∧
      (∀ j, ∀ z ∈ (Ω : Set 𝔼), G j z = (Ω : Set 𝔼).indicator
        (fun x ↦ θ i x * w j x + fderiv ℝ (θ i) x (EuclideanSpace.single j (1 : ℝ)) * ũ x)
        (z + t • y i)) ∧
      (ContinuousOn ũ (closure (Ω : Set 𝔼)) → Continuous F) := fun i ↦
    SobolevEuclidean.exists_translatePiece hb hũp hw hwp (hθ i) (U := interior (U i))
      (h := t • y i)
      (fun z hz ↦ hδ i (t • y i)
        (by rw [norm_smul, Real.norm_of_nonneg ht0.le]; exact htδ i) z hz)
      (fun z hz hzU ↦ hy i (hs i i.2) z ⟨hz, interior_subset hzU⟩ t ⟨ht0, ht1⟩)
  choose F G hFc hFp hGp hFG hFval hGval hFcont using hpieces
  -- the sum of the pieces
  obtain ⟨Fs, hFsdef⟩ : ∃ Fs : 𝔼 → ℝ, Fs = F₀ + ∑ i, F i := ⟨_, rfl⟩
  obtain ⟨Gs, hGsdef⟩ : ∃ Gs : Fin N → 𝔼 → ℝ, ∀ j, Gs j = G₀ j + ∑ i, G i j := ⟨_, fun _ ↦ rfl⟩
  have hFsc : HasCompactSupport Fs :=
    hFsdef ▸ hF₀c.add (HasCompactSupport.finset_sum fun i _ ↦ hFc i)
  have hFsp : MemLp Fs p volume := hFsdef ▸ hF₀p.add (memLp_finsetSum' _ fun i _ ↦ hFp i)
  have hGsp : ∀ j, MemLp (Gs j) p volume := fun j ↦
    hGsdef j ▸ (hG₀p j).add (memLp_finsetSum' _ fun i _ ↦ hGp i j)
  have hFsG : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] Fs (Gs j)
      ⊤ volume := fun j ↦ by
    rw [hFsdef, hGsdef j]
    have := (hF₀G j).add (HasWeakIteratedLineDerivOn.finset_sum (s := Finset.univ)
      fun i _ ↦ hFG i j)
    exact this.congr_ae (Eventually.of_forall fun x ↦ by simp [Finset.sum_apply])
      (Eventually.of_forall fun x ↦ by simp [Finset.sum_apply])
  have hFsmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis Fs 1 p ⊤ volume :=
    SobolevEuclidean.memSobolevMultiIndex_one_of_forall
      (by simpa [Measure.restrict_coe_top] using hFsp)
      (fun j ↦ by simpa [Measure.restrict_coe_top] using hGsp j) hFsG
  -- Step 2: the identities on `Ω`
  have hfd := fderiv_add_sum_eq_zero_of_partition hθ₀ hθ hsum
  have hfn : (fun z ↦ Fs z - ũ z) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun z ↦ ∑ i : s, ((hH0 i).toLp (H0f i) (z + t • y i) - (hH0 i).toLp (H0f i) z) := by
    have hae : ∀ i : s, ∀ᵐ z ∂(volume.restrict (Ω : Set 𝔼)),
        (hH0 i).toLp (H0f i) (z + t • y i) = H0f i (z + t • y i) ∧
          (hH0 i).toLp (H0f i) z = H0f i z := fun i ↦ by
      refine ae_mono (Measure.restrict_mono le_top le_rfl) ?_
      have h4 := ((IsTranslationInvariant.top (t • y i)).measurePreserving
        (μ := volume)).quasiMeasurePreserving.ae_eq_comp (hH0 i).coeFn_toLp
      filter_upwards [(hH0 i).coeFn_toLp, h4] with z hz1 hz2
      exact ⟨hz2, hz1⟩
    filter_upwards [Filter.eventually_all.2 hae, ae_restrict_mem Ω.isOpen.measurableSet]
      with z hz' hz
    have e1 : ∀ i : s, F i z = H0f i (z + t • y i) := fun i ↦ by
      rw [hFval i z (subset_closure hz), hH0def]
    have e2 : ∀ i : s, H0f i z = θ i z * ũ z := fun i ↦ by
      rw [hH0def, Set.indicator_of_mem hz]
    simp only [(hz' _).1, (hz' _).2]
    rw [hFsdef, Pi.add_apply, Finset.sum_apply, hF₀val z (subset_closure hz), add_zero,
      Set.indicator_of_mem hz]
    simp only [e1, e2, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    linear_combination (ũ z) * hsum z
  have hder : ∀ j, (fun z ↦ Gs j z - w j z) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun z ↦ ∑ i : s, ((hH1 i j).toLp (H1f i j) (z + t • y i)
        - (hH1 i j).toLp (H1f i j) z) := by
    intro j
    have hae : ∀ i : s, ∀ᵐ z ∂(volume.restrict (Ω : Set 𝔼)),
        (hH1 i j).toLp (H1f i j) (z + t • y i) = H1f i j (z + t • y i) ∧
          (hH1 i j).toLp (H1f i j) z = H1f i j z := fun i ↦ by
      refine ae_mono (Measure.restrict_mono le_top le_rfl) ?_
      have h4 := ((IsTranslationInvariant.top (t • y i)).measurePreserving
        (μ := volume)).quasiMeasurePreserving.ae_eq_comp (hH1 i j).coeFn_toLp
      filter_upwards [(hH1 i j).coeFn_toLp, h4] with z hz1 hz2
      exact ⟨hz2, hz1⟩
    filter_upwards [Filter.eventually_all.2 hae, ae_restrict_mem Ω.isOpen.measurableSet]
      with z hz' hz
    have e1 : ∀ i : s, G i j z = H1f i j (z + t • y i) := fun i ↦ by
      rw [hGval i j z hz, hH1def]
    have e2 : ∀ i : s, H1f i j z = θ i z * w j z
        + fderiv ℝ (θ i) z (EuclideanSpace.single j (1 : ℝ)) * ũ z := fun i ↦ by
      rw [hH1def, Set.indicator_of_mem hz]
    simp only [(hz' _).1, (hz' _).2]
    rw [hGsdef j, Pi.add_apply, Finset.sum_apply, hG₀val j z hz, add_zero,
      Set.indicator_of_mem hz]
    simp only [e1, e2, Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    linear_combination (w j z) * hsum z + (ũ z) * hfd z (EuclideanSpace.single j (1 : ℝ))
  refine ⟨Fs, Gs, hFsc, hFsmem, hFsG, ⟨s, fun i ↦ (hH0 i).toLp (H0f i),
    fun i j ↦ (hH1 i j).toLp (H1f i j), fun i ↦ y i, t, hfn, hder, (herrdef t).symm ▸ hterr⟩,
    fun hũc ↦ ⟨?_, ?_⟩⟩
  · exact hFsdef ▸ (hF₀cont hũc).add
      ((continuous_finsetSum (Finset.univ : Finset s) fun i _ ↦ hFcont i hũc).congr
        fun x ↦ by simp [Finset.sum_apply])
  · intro z hz
    -- `θ₀ ũ` is its zero extension on `closure Ω`
    have hθ₀val : (Ω : Set 𝔼).indicator (fun x ↦ θ₀ x * ũ x) z = θ₀ z * ũ z := by
      by_cases hzΩ : z ∈ (Ω : Set 𝔼)
      · exact Set.indicator_of_mem hzΩ _
      · rw [Set.indicator_of_notMem hzΩ, image_eq_zero_of_notMem_tsupport
          (Set.disjoint_right.1 hθ₀f ⟨hz, fun h' ↦ hzΩ (by rwa [Ω.isOpen.interior_eq] at h')⟩),
          zero_mul]
    have hFsz : Fs z - ũ z = ∑ i : s,
        ((Ω : Set 𝔼).indicator (fun x ↦ θ i x * ũ x) (z + t • y i) - θ i z * ũ z) := by
      rw [hFsdef, Pi.add_apply, Finset.sum_apply, hF₀val z hz, add_zero, hθ₀val,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [hFval _ z hz]
      linear_combination (ũ z) * hsum z
    have hterm : ∀ i : s, |(Ω : Set 𝔼).indicator (fun x ↦ θ i x * ũ x) (z + t • y i)
        - θ i z * ũ z| ≤ ε' := by
      intro i
      by_cases hmem : z + t • y i ∈ (Ω : Set 𝔼)
      · rw [Set.indicator_of_mem hmem, ← Real.dist_eq]
        refine (htunif hũc i z hz (z + t • y i) (subset_closure hmem) ?_).le
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
      · have hθz : θ i z = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun hzθ ↦ hmem ?_
          exact hy i (hs i i.2) z ⟨hz, interior_subset (hθU i hzθ)⟩ t ⟨ht0, ht1⟩
        rw [Set.indicator_of_notMem hmem, hθz, zero_mul, sub_zero, abs_zero]
        exact hε'pos.le
    rw [Real.dist_eq, hFsz]
    calc |∑ i : s, ((Ω : Set 𝔼).indicator (fun x ↦ θ i x * ũ x) (z + t • y i) - θ i z * ũ z)|
        ≤ ∑ i : s, |(Ω : Set 𝔼).indicator (fun x ↦ θ i x * ũ x) (z + t • y i) - θ i z * ũ z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : s, ε' := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (s.card : ℝ) * ε' := by simp
      _ < ε := hε'

/-- **The translate approximation, in `W^{1,p}(Ω)`**: for a bounded `Ω` with the segment
property, `u ∈ W^{1,p}(Ω)` with representative `ũ`, and `ε > 0`, there is a compactly supported
`Fs ∈ W^{1,p}(ℝ^N)`, with typed element `Ft`, whose restriction to `Ω` is within `ε` of `u` in
`W^{1,p}(Ω)`, and which is continuous and within `ε` of `ũ` on `closure Ω` when `ũ` is
continuous there. This reads `HasSegmentProperty.exists_translateApprox` in `W^{1,p}(Ω)`: the
weak derivatives of `Ft` are the `Gs j` (uniqueness), and each component of `R Ft − u` is a sum
of translation differences, bounded by `SobolevEuclidean.norm_le_sum_norm_translateCurve_sub`. -/
theorem HasSegmentProperty.exists_hasCompactSupport_norm_restrictL_sub_lt
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hΩ : HasSegmentProperty (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p Ω) {ũ : 𝔼 → ℝ} (hũ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Fs : 𝔼 → ℝ) (Ft : SobolevEuclidean N 1 p ⊤), HasCompactSupport Fs ∧
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis Fs 1 p ⊤ volume ∧
      fn Ft =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)] Fs ∧
      ‖restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume (le_top : Ω ≤ ⊤) Ft
        - u‖ < ε ∧
      (ContinuousOn ũ (closure (Ω : Set 𝔼)) →
        Continuous Fs ∧ ∀ z ∈ closure (Ω : Set 𝔼), dist (Fs z) (ũ z) < ε) := by
  have hw : ∀ j, HasWeakIteratedLineDerivOn ![EuclideanSpace.single j (1 : ℝ)] ũ
      (weakDeriv u (MultiIndexLE.single j)) Ω volume := fun j ↦
    (SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u j).congr_ae hũ
      (EventuallyEq.refl _ _)
  obtain ⟨Fs, Gs, hFsc, hFsmem, hFsG, ⟨s, H0, H1, y, t, hfn0, hder0, herr⟩, hcont⟩ :=
    HasSegmentProperty.exists_translateApprox hb hΩ hp' ((memLp u).ae_eq hũ) hw
      (fun j ↦ Lp.memLp _) hε
  obtain ⟨Ft, hFt⟩ := hFsmem.exists_sobolevMultiIndex
  have hFtd : ∀ j, weakDeriv Ft (MultiIndexLE.single j)
      =ᵐ[volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼)] Gs j := fun j ↦
    SobolevEuclidean.weakDeriv_single_ae_eq Ft hFt (hFsG j)
  have hΩsub : volume.restrict (Ω : Set 𝔼) ≤ volume.restrict ((⊤ : Opens 𝔼) : Set 𝔼) :=
    Measure.restrict_mono le_top le_rfl
  refine ⟨Fs, Ft, hFsc, hFsmem, hFt, ?_, hcont⟩
  have hfn : ((weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
      (le_top : Ω ≤ ⊤) Ft - u) 0 : Lp ℝ p (volume.restrict (Ω : Set 𝔼))) : 𝔼 → ℝ)
      =ᵐ[volume.restrict (Ω : Set 𝔼)] fun z ↦ ∑ i, (H0 i (z + t • y i) - H0 i z) := by
    rw [weakDeriv_sub]
    filter_upwards [Lp.coeFn_sub (weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 p volume (le_top : Ω ≤ ⊤) Ft) 0) (weakDeriv u 0), fn_restrictL (le_top : Ω ≤ ⊤) Ft,
      ae_mono hΩsub hFt, hũ, hfn0] with z hz1 hz2 hz3 hz4 hz5
    rw [hz1, Pi.sub_apply, weakDeriv_zero, weakDeriv_zero, hz2, hz3, hz4]
    exact hz5
  have hder : ∀ j, ((weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p
      volume (le_top : Ω ≤ ⊤) Ft - u) (MultiIndexLE.single j) :
        Lp ℝ p (volume.restrict (Ω : Set 𝔼))) : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun z ↦ ∑ i, (H1 i j (z + t • y i) - H1 i j z) := fun j ↦ by
    rw [weakDeriv_sub]
    filter_upwards [Lp.coeFn_sub (weakDeriv (restrictL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume (le_top : Ω ≤ ⊤) Ft)
      (MultiIndexLE.single j)) (weakDeriv u (MultiIndexLE.single j)),
      weakDeriv_restrictL (le_top : Ω ≤ ⊤) Ft (MultiIndexLE.single j), ae_mono hΩsub (hFtd j),
      hder0 j] with z hz1 hz2 hz3 hz5
    rw [hz1, Pi.sub_apply, hz2, hz3]
    exact hz5
  calc ‖restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume (le_top : Ω ≤ ⊤) Ft
        - u‖
      ≤ ∑ α, ‖weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
        (le_top : Ω ≤ ⊤) Ft - u) α‖ := norm_le_sum_norm_weakDeriv _
    _ = ‖weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
        (le_top : Ω ≤ ⊤) Ft - u) 0‖
        + ∑ j, ‖weakDeriv (restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
          (le_top : Ω ≤ ⊤) Ft - u) (MultiIndexLE.single j)‖ := MultiIndexLE.sum_univ_one _
    _ ≤ ∑ i, ‖Lp.translateCurve ℝ p (y i) (H0 i) t - H0 i‖
        + ∑ j, ∑ i, ‖Lp.translateCurve ℝ p (y i) (H1 i j) t - H1 i j‖ := add_le_add
        (SobolevEuclidean.norm_le_sum_norm_translateCurve_sub _ H0 y t hfn)
        (Finset.sum_le_sum fun j _ ↦
          SobolevEuclidean.norm_le_sum_norm_translateCurve_sub _ (fun i ↦ H1 i j) y t (hder j))
    _ < ε := herr

/-- **Density up to the boundary, one `ε` at a time**: for a bounded `Ω` with the segment
property, `1 ≤ p < ∞`, `u ∈ W^{1,p}(Ω)` with representative `ũ`, and `ε > 0`, there are
`v ∈ C_c^∞(ℝ^N)` and `w ∈ W^{1,p}(Ω)` with `w = v` on `Ω`, `‖w − u‖ < ε`, and, if `ũ` is
continuous on `closure Ω`, `|v − ũ| < ε` on `closure Ω`: the translate approximation
`HasSegmentProperty.exists_hasCompactSupport_norm_restrictL_sub_lt` at `ε / 2`, mollified
(`MemSobolev.exists_contDiff_hasCompactSupport_sobolevNorm_sub_lt`) to within `ε / 2` in
`W^{1,p}(ℝ^N)` (`SobolevMultiIndex.ofReal_norm_le_sobolevNorm` for the typed norm) and
uniformly. -/
theorem HasSegmentProperty.exists_contDiff_hasCompactSupport_norm_sub_lt
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hΩ : HasSegmentProperty (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p Ω) {ũ : 𝔼 → ℝ} (hũ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : 𝔼 → ℝ) (w : SobolevEuclidean N 1 p Ω), ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] v ∧ ‖w - u‖ < ε ∧
      (ContinuousOn ũ (closure (Ω : Set 𝔼)) →
        ∀ z ∈ closure (Ω : Set 𝔼), dist (v z) (ũ z) < ε) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨R, hRdef⟩ : ∃ R : SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclidean N 1 p Ω,
      R = restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p volume
        (le_top : Ω ≤ ⊤) := ⟨_, rfl⟩
  have hRfn : ∀ w, fn (R w) =ᵐ[volume.restrict (Ω : Set 𝔼)] fn w := fun w ↦ by
    rw [hRdef]; exact fn_restrictL _ _
  have hRle : ∀ w, ‖R w‖ ≤ ‖w‖ := fun w ↦ by
    rw [hRdef]; exact norm_restrictL_apply_le _ _
  obtain ⟨Fs, Ft, hFsc, hFsmem, hFt, hFtu, hFscont⟩ :=
    HasSegmentProperty.exists_hasCompactSupport_norm_restrictL_sub_lt hb hΩ hp' u hũ
      (half_pos hε)
  rw [← hRdef] at hFtu
  -- the constant of `ofReal_norm_le_sobolevNorm`
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ≥0∞, C = 1 + ∑ i, ‖ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin 1 ↦ 𝔼) ℝ ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]‖ₑ := ⟨_, rfl⟩
  have hC0 : C ≠ 0 := by
    rw [hCdef]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one le_self_add)
  have hC : C ≠ ⊤ := by
    rw [hCdef]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩
  -- mollification
  obtain ⟨v, hv, hvc, hvF, hvunif⟩ :=
    MemSobolev.exists_contDiff_hasCompactSupport_sobolevNorm_sub_lt
      (MemSobolevMultiIndex.memSobolev hFsmem) hFsc hp hp'
      (η := ENNReal.ofReal (ε / 2) / C)
      (ENNReal.div_pos (ENNReal.ofReal_pos.2 (half_pos hε)).ne' hC) (half_pos hε)
  obtain ⟨V, hV⟩ := hv.exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (Ω := (⊤ : Opens 𝔼))
    (μ := volume) hvc
  have hVF : ‖V - Ft‖ < ε / 2 := by
    have h1 := ofReal_norm_le_sobolevNorm hp' (V - Ft)
    have h2 : sobolevNorm (fn (V - Ft)) 1 p ⊤ volume = sobolevNorm (v - Fs) 1 p ⊤ volume :=
      sobolevNorm_congr_ae ((fn_sub V Ft).trans (hV.sub hFt))
    rw [h2, ← hCdef] at h1
    have h3 : C * sobolevNorm (v - Fs) 1 p ⊤ volume < C * (ENNReal.ofReal (ε / 2) / C) :=
      ENNReal.mul_lt_mul_right hC0 hC hvF
    exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).1
      (lt_of_le_of_lt h1 (lt_of_lt_of_le h3 ENNReal.mul_div_le))
  refine ⟨v, R V, hv, hvc,
    (hRfn V).trans (ae_mono (Measure.restrict_mono le_top le_rfl) hV), ?_, ?_⟩
  · have hRVF : ‖R V - R Ft‖ ≤ ‖V - Ft‖ := by
      have h := hRle (V - Ft)
      rw [map_sub] at h
      exact h
    calc ‖R V - u‖ ≤ ‖R V - R Ft‖ + ‖R Ft - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hRVF.trans hVF.le) hFtu
      _ = ε := add_halves ε
  · intro hũc z hz
    obtain ⟨hFsc', hFsz⟩ := hFscont hũc
    calc dist (v z) (ũ z) ≤ dist (v z) (Fs z) + dist (Fs z) (ũ z) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hvunif hFsc' z) (hFsz z hz)
      _ = ε := add_halves ε

end Construction

/-! ### The density theorem and its instances -/

section Density

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- **Density of `C_c^∞(ℝ^N)` up to the boundary on a bounded open set with the segment
property, with uniform convergence for continuous functions** (Adams–Fournier, *Sobolev
Spaces*, Theorem 3.22 at order one, with Evans's remark on uniform convergence, *PDE* §5.5):
for `1 ≤ p < ∞`, `u ∈ W^{1,p}(Ω)` and a representative `ũ` of `u`, there are smooth compactly
supported `v n` on `ℝ^N` and `w n ∈ W^{1,p}(Ω)` with `w n = v n` on `Ω` and `w n → u` in
`W^{1,p}(Ω)`, such that moreover `v n → ũ` uniformly on `closure Ω` whenever `ũ` is continuous
on `closure Ω`. The sequence is
`HasSegmentProperty.exists_contDiff_hasCompactSupport_norm_sub_lt` at `ε = 1 / (n + 1)`;
taking `ũ = fn u` gives `SobolevEuclidean.HasSmoothDensity`, and a continuous representative
gives `SobolevEuclidean.HasUniformSmoothDensity`. -/
theorem HasSegmentProperty.exists_seq_contDiff_hasCompactSupport_tendsto
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩ : HasSegmentProperty (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hp' : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p Ω) {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hũ : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
        (∃ w : ℕ → SobolevEuclidean N 1 p Ω,
          (∀ n, fn (w n) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
            Tendsto w atTop (𝓝 u)) ∧
        (ContinuousOn ũ (closure (Ω : Set (EuclideanSpace ℝ (Fin N)))) →
          TendstoUniformlyOn v ũ atTop (closure (Ω : Set (EuclideanSpace ℝ (Fin N))))) := by
  choose v w hv hvc hw hwu hunif using fun n : ℕ ↦
    HasSegmentProperty.exists_contDiff_hasCompactSupport_norm_sub_lt hb hΩ hp' u hũ
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨v, hv, hvc, ⟨w, hw, ?_⟩, fun hũc ↦ ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hwu n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop n₀] with n hn z hz
    rw [dist_comm]
    calc dist (v n z) (ũ z) < 1 / ((n : ℝ) + 1) := hunif n hũc z hz
      _ ≤ 1 / ((n₀ : ℝ) + 1) := by gcongr
      _ < ε := hn₀

/-- A bounded open set with the segment property has smooth density. -/
theorem HasSegmentProperty.hasSmoothDensity
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩ : HasSegmentProperty (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity N p Ω := fun u ↦
  let ⟨v, hv, hvc, ⟨w, hw, hwu⟩, _⟩ :=
    hΩ.exists_seq_contDiff_hasCompactSupport_tendsto hb hp' u (EventuallyEq.refl _ _)
  ⟨v, hv, hvc, w, hw, hwu⟩

/-- A bounded open set with the segment property has uniform smooth density. -/
theorem HasSegmentProperty.hasUniformSmoothDensity
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hΩ : HasSegmentProperty (Ω : Set (EuclideanSpace ℝ (Fin N)))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasUniformSmoothDensity N p Ω := fun u _ hũ hũc ↦
  let ⟨v, hv, hvc, hw, hunif⟩ := hΩ.exists_seq_contDiff_hasCompactSupport_tendsto hb hp' u hũ
  ⟨v, hv, hvc, hw, hunif hũc⟩

/-- A bounded convex open set has smooth density (a by-product: convex polygons). -/
theorem Convex.hasSmoothDensity (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hc : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin N))).Nonempty) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity N p Ω :=
  (hc.hasSegmentProperty Ω.isOpen hne).hasSmoothDensity hb hp'

/-- A bounded convex open set has uniform smooth density. -/
theorem Convex.hasUniformSmoothDensity
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hc : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin N))).Nonempty) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasUniformSmoothDensity N p Ω :=
  (hc.hasSegmentProperty Ω.isOpen hne).hasUniformSmoothDensity hb hp'

/-- A triangle with non-collinear vertices has uniform smooth density. -/
theorem EuclideanSpace.hasUniformSmoothDensity_openTriangleOpens
    (A B C : EuclideanSpace ℝ (Fin 2)) (h : LinearIndependent ℝ ![B - A, C - A]) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasUniformSmoothDensity 2 p (A.openTriangleOpens B C h) :=
  Convex.hasUniformSmoothDensity (isBounded_openTriangle A B C) (convex_openTriangle A B C)
    ⟨_, mem_openTriangle.2 ⟨1 / 3, 1 / 3, by norm_num, by norm_num, by norm_num, rfl⟩⟩ hp'

end Density

section GraphDensity

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- A bounded `C^n` graph domain has uniform smooth density. -/
theorem IsContDiffDomain.hasUniformSmoothDensity {n : WithTop ℕ∞}
    (hΩ : IsContDiffDomain n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasUniformSmoothDensity (d + 1) p Ω :=
  hΩ.hasSegmentProperty.hasUniformSmoothDensity hb hp'

/-- A bounded Lipschitz graph domain has smooth density (the Lipschitz case of Atkinson–Han
Theorem 7.3.2, which the extension route does not reach). -/
theorem IsLipschitzDomain.hasSmoothDensity
    (hΩ : IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasSmoothDensity (d + 1) p Ω :=
  hΩ.hasSegmentProperty.hasSmoothDensity hb hp'

/-- A bounded Lipschitz graph domain has uniform smooth density. -/
theorem IsLipschitzDomain.hasUniformSmoothDensity
    (hΩ : IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hp' : p ≠ ⊤) :
    SobolevEuclidean.HasUniformSmoothDensity (d + 1) p Ω :=
  hΩ.hasSegmentProperty.hasUniformSmoothDensity hb hp'

end GraphDensity

end
