import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Numlib.Analysis.Sobolev.Calculus
import Numlib.Approximation.NodalInterpolation
import Numlib.Geometry.Euclidean.TriangleShape
import NumlibSurface.AtkinsonHan.Chapter07.Section02

/-!
# Atkinson–Han §10.3: local interpolation and regular families

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §10.3.

The section estimates the finite element interpolation error on an element by transporting the
problem to the reference element. The estimates themselves are Sobolev statements and are not
available yet — *Not formalized here* below says what each one waits on, which is no longer the
Sobolev space — but the transport itself, Theorem 10.3.4, is here, and two of the results are not
Sobolev statements at all:

* **Theorem 10.3.1**, that nodal interpolation commutes with the affine pullback, is an algebraic
  identity between two finite sums. It is the backbone's `Approximation.nodalInterp_comp`, and the
  book's `Π̂` and `Π_K` of (10.3.1) and (10.3.2) are `Approximation.nodalInterp` at the reference
  nodes and at their images under `F_K`.
* **Definition 10.3.6**, the regularity of a family of partitions, needs only the diameter of an
  element and a ball inscribed in it.

## Main definitions

* `meshSize` — the mesh parameter (10.3.9), `h = max_{K ∈ 𝒯_h} h_K`, written as a supremum of
  diameters so that it is defined for any collection of elements; `diam_le_meshSize` is the
  maximum property for a finite one.
* `IsRegularFamily` — Definition 10.3.6: a family of partitions is regular when the ratios
  `h_K / ρ_K` are bounded uniformly and the mesh parameter tends to `0` along the family.

## Main results

* `theorem_10_3_1` — `Π̂ (v ∘ F_K) = (Π_K v) ∘ F_K`.
* `theorem_10_3_4` — the affine change of variables in `H^m`: `v ∈ H^m(K)` iff `v ∘ F_K ∈ H^m(K̂)`,
  with the seminorm bounds (10.3.5)–(10.3.6); the general lemmas `eLpNorm_comp_affine`,
  `memSobolev_comp_affine_iff` and `sobolevSeminorm_comp_affine_le` (every order, every `p`) sit
  beside it and belong in `Numlib/Analysis/Sobolev/Calculus.lean`.
* `example_10_3_2` — the linear element: the barycentric coordinates of a simplex are nodal for its
  vertices, so `Π_K` is the interpolant through the vertex values, and
  `nodalInterp_coord_affineMap` says that it reproduces affine functions.

## Deviations from the book

The book's `ρ_K` is the diameter of the *largest* ball inscribed in `K`, a supremum Mathlib has no
name for and which need not be attained for a general set. Condition (a) of Definition 10.3.6 uses
it only through the inequality `h_K ≤ σ ρ_K`, so `IsRegularFamily` asks instead for *some* inscribed
ball with `h_K ≤ σ · (2 r)`. For a `K` whose largest inscribed ball exists — the book's triangles —
the two readings agree, and in either reading the condition says the elements do not degenerate.

`𝒯_h` is read as a collection of elements, `Set (Set (EuclideanSpace ℝ (Fin d)))`, and the family is
indexed by an arbitrary type with a filter along which the mesh parameter tends to zero: the book
indexes by `h` itself and lets `h → 0`. The partition axioms (1)–(4) of §10.2 — that the elements
are triangles covering `Ω̄` with disjoint interiors and matching faces — play no part in Definition
10.3.6 and are not formalized; that is why the definition is stated for a family of collections and
not for a family of triangulations.

## Not formalized here

Theorems 10.3.3, 10.3.5, Corollary 10.3.7 and Theorem 10.3.9, the interpolation error
estimates: they are inequalities between `H^m` seminorms and rest on the Deny–Lions estimate
(the Bramble–Hilbert lemma, Exercises 10.3.5 and 10.3.6), on the transformation of a Sobolev
seminorm under an affine map (Theorem 10.3.4, proved here), and — for the global bound — on the
additivity of the `H^m` norm over a triangulation. `H^m(K)` is not the obstruction: the weak
derivative on an open set of `ℝᵈ` is `Chapter07.definition_7_1_3_multiIndex` and the space with
its norm is `Chapter07.definition_7_2_2` / `Chapter07.definition_7_2_2_multiIndex` with
`Chapter07.definition_7_2_2_multiIndex_norm`, all proved; the seminorm `|·|_{m,K}` used here is
the backbone's `sobolevSeminorm`, the tensor form, equivalent to the book's sum over `|α| = m`
with constants depending on `d` and `m` only. What is missing is §7.3 over them — Deny–Lions is
Theorem 7.3.12, Bramble–Hilbert is Theorem 7.3.17, and the embedding `H^{k+1}(K̂) ↪ C(K̂)` that
makes the interpolant of a Sobolev function meaningful is Theorem 7.3.7; the Brezis backbone
proves these on `C¹` domains and on Sobolev extension domains (`IsSobolevExtensionDomain`), which
the reference simplex, a Lipschitz domain, is not known to be, while the unit square is
(`SobolevEuclidean.exists_extensionL_unitSquare`). The same gap rules out Exercises 10.3.1,
10.3.2, 10.3.4 and 10.3.7. Exercise 10.3.3 (`h_K / ρ_K` bounded if and only if the minimal angles
are bounded below) is Sobolev-free, and is
`exercise_10_3_3` below.
-/

open Filter Metric Topology

open scoped Real

namespace AtkinsonHan.Chapter10

variable {d : ℕ}

/-- **Theorem 10.3.1.**  Let `F_K` be an affine bijection of the reference element onto `K`, let
`x̂ᵢ` be the nodal points of the reference element and `φ̂ᵢ` the associated basis functions, and put
`xᵢᴷ = F_K(x̂ᵢ)` and `φᵢᴷ = φ̂ᵢ ∘ F_K⁻¹` as in (10.2.27). Then the interpolation operators (10.3.1)
`Π̂ v̂ = Σ v̂(x̂ᵢ) φ̂ᵢ` and (10.3.2) `Π_K v = Σ v(xᵢᴷ) φᵢᴷ` satisfy

  `Π̂ (v ∘ F_K) = (Π_K v) ∘ F_K`.

The proof is the definition read twice: `v(xᵢᴷ) = v̂(x̂ᵢ)` and `φᵢᴷ ∘ F_K = φ̂ᵢ`. Neither the
affinity of `F_K` nor the duality `φ̂ᵢ(x̂ⱼ) = δᵢⱼ` is used — only that `F_K` is invertible — so this
is the backbone's `Approximation.nodalInterp_comp` for the equivalence `F_K`. The nodal property
survives the transport (`Approximation.IsNodalBasis.comp`), which is the book's display
`φᵢᴷ(xⱼᴷ) = δᵢⱼ`. -/
theorem theorem_10_3_1 {I : ℕ} (F : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : Fin I → EuclideanSpace ℝ (Fin d)) (φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    Approximation.nodalInterp x φ (v ∘ F) =
      Approximation.nodalInterp (F ∘ x) (fun i => φ i ∘ F.symm) v ∘ F :=
  (Approximation.nodalInterp_comp x φ v (F := F) (G := F.symm) F.symm_apply_apply).symm

/-- **Example 10.3.2, the linear element.**  On a simplex with vertices `b i` the shape functions of
the linear element are the barycentric coordinates `λᵢ`, and they are nodal for the vertices:
`λᵢ(bⱼ) = δᵢⱼ`. So `Approximation.nodalInterp b (fun i => λᵢ)` *is* the operator `Π_K` of (10.3.2)
for that element — the function agreeing with `v` at each vertex — and Theorem 10.3.1 applies to it,
the transported shape functions `λᵢ ∘ F_K⁻¹` being the barycentric coordinates of the image simplex.

The book writes the reference element as a triangle in the plane; nothing here needs the dimension
or the number of vertices, and the coordinates are Mathlib's `AffineBasis.coord`. -/
theorem example_10_3_2 {ι : Type*} (b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin d))) :
    Approximation.IsNodalBasis (b : ι → EuclideanSpace ℝ (Fin d))
      (fun i => (b.coord i : EuclideanSpace ℝ (Fin d) → ℝ)) where
  eval_self _ := b.coord_apply_eq _
  eval_of_ne _ _ hij := b.coord_apply_ne hij

/-- **The linear element is exact on affine functions**: `Π_K f = f` for an affine `f`. It is the
`k = 1` case of the reproduction property that makes the interpolation error estimates of §10.3
worth having, and it is the identity `f(y) = Σᵢ λᵢ(y) f(bᵢ)`, which is the affine map applied to the
barycentric representation `y = Σᵢ λᵢ(y) bᵢ`. -/
theorem nodalInterp_coord_affineMap {ι : Type*} [Fintype ι]
    (b : AffineBasis ι ℝ (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ) :
    Approximation.nodalInterp (b : ι → EuclideanSpace ℝ (Fin d))
      (fun i => (b.coord i : EuclideanSpace ℝ (Fin d) → ℝ)) f = f := by
  funext y
  rw [Approximation.nodalInterp_apply]
  have hw : ∑ i, b.coord i y = 1 := b.sum_coord_apply_eq_one y
  have h := Finset.univ.map_affineCombination (b : ι → EuclideanSpace ℝ (Fin d))
    (fun i => b.coord i y) hw f
  rw [b.affineCombination_coord_eq_self y] at h
  rw [h, Finset.univ.affineCombination_eq_linear_combination _ _ hw]
  rfl

/-- **The mesh parameter (10.3.9)**, `h = max_{K ∈ 𝒯_h} h_K`, of a collection of elements: the
supremum of their diameters. For a finite collection — the book's partitions are finite — the
supremum is the maximum, which is `diam_le_meshSize`. -/
noncomputable def meshSize (T : Set (Set (EuclideanSpace ℝ (Fin d)))) : ℝ :=
  sSup (Metric.diam '' T)

/-- Every element of a finite collection has diameter at most the mesh parameter. -/
theorem diam_le_meshSize {T : Set (Set (EuclideanSpace ℝ (Fin d)))} (hT : T.Finite)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : K ∈ T) : Metric.diam K ≤ meshSize T :=
  le_csSup (hT.image _).bddAbove (Set.mem_image_of_mem _ hK)

/-- **Definition 10.3.6.**  A family `{𝒯_h}` of finite element partitions is **regular** if

* (a) there is a `σ` with `h_K / ρ_K ≤ σ` for every element `K` of every member of the family, and
* (b) the mesh parameter `h` tends to `0` along the family.

Here `h_K = diam K` and `ρ_K` is the diameter of the largest ball inscribed in `K`; condition (a) is
written as the existence of an inscribed ball of radius `r` with `h_K ≤ σ (2 r)`, which is what the
inequality `h_K ≤ σ ρ_K` says whenever the largest inscribed ball exists. Condition (b) is a limit
along a filter `l` on the index type, the book's `h → 0`.

Regularity is what turns the element-wise estimate (10.3.7), whose right-hand side carries both
`h_K` and `ρ_K`, into a bound in `h_K` alone (Corollary 10.3.7). -/
def IsRegularFamily {ι : Type*} (l : Filter ι)
    (T : ι → Set (Set (EuclideanSpace ℝ (Fin d)))) : Prop :=
  (∃ σ : ℝ, ∀ i, ∀ K ∈ T i, ∃ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ),
      0 < r ∧ Metric.closedBall c r ⊆ K ∧ Metric.diam K ≤ σ * (2 * r)) ∧
    Tendsto (fun i => meshSize (T i)) l (𝓝 0)

/-! ### Exercise 10.3.3: regularity against the minimal angle

The exercise is about triangles, and `ρ_K` is the diameter `2 ρ` of the inscribed circle, which for
a triangle is `Affine.Simplex.inradius`. The statement below is therefore condition (a) of
Definition 10.3.6 read on a family of triangles with the *actual* inradius, rather than through the
weaker "some inscribed ball" form that `IsRegularFamily` uses for a family of arbitrary sets. The
geometry is `Numlib.Geometry.Euclidean.TriangleShape`. -/

/-- **Exercise 10.3.3.** For a family of triangles, condition (a) of Definition 10.3.6 — the ratios
`h_K / ρ_K` are bounded — holds if and only if the angles of the triangles are bounded away from
zero.

Both directions are quantitative: a bound `h_K ≤ σ ρ_K` gives every angle at least
`arcsin (1 / (2 σ))`, and a bound `α ≤ θ` on all the angles gives `h_K ≤ (3 / sin² α) ρ_K`. -/
theorem exercise_10_3_3 {ι : Type*}
    (T : ι → Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    (∃ σ : ℝ, ∀ t, Metric.diam (Set.range (T t).points) ≤ σ * (2 * (T t).inradius))
      ↔ ∃ α : ℝ, 0 < α ∧ ∀ t i, α ≤ (T t).triangleAngle i := by
  constructor
  · rintro ⟨σ, hσ⟩
    have hσ' : ∀ t, Metric.diam (Set.range (T t).points) ≤ max σ 1 * (2 * (T t).inradius) := by
      intro t
      refine (hσ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      linarith [(T t).inradius_pos]
    set τ := max σ 1 with hτ
    have hτpos : (0 : ℝ) < τ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hle1 : 1 / (2 * τ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [le_max_right σ 1]
    refine ⟨Real.arcsin (1 / (2 * τ)), Real.arcsin_pos.2 (by positivity), fun t i => ?_⟩
    have hD := (T t).diam_pos
    have hr := (T t).inradius_pos
    have hsin : 1 / (2 * τ) ≤ Real.sin ((T t).triangleAngle i) := by
      have h1 := (T t).inradius_le_diam_mul_sin_triangleAngle i
      have h2 := hσ' t
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(T t).sin_triangleAngle_nonneg i]
    calc Real.arcsin (1 / (2 * τ)) ≤ Real.arcsin (Real.sin ((T t).triangleAngle i)) :=
          Real.arcsin_le_arcsin hsin
      _ ≤ (T t).triangleAngle i := by
          rcases le_total ((T t).triangleAngle i) (π / 2) with h | h
          · rw [Real.arcsin_sin (by linarith [(T t).triangleAngle_nonneg i, Real.pi_pos]) h]
          · exact (Real.arcsin_le_pi_div_two _).trans h
  · rintro ⟨α, hαpos, hα⟩
    set β := min α (π / 2) with hβ
    have hβpos : 0 < β := lt_min hαpos (by linarith [Real.pi_pos])
    have hβle : β ≤ π / 2 := min_le_right _ _
    have hsinβ : 0 < Real.sin β :=
      Real.sin_pos_of_pos_of_lt_pi hβpos (by linarith [Real.pi_pos])
    refine ⟨3 / (2 * Real.sin β ^ 2), fun t => ?_⟩
    have h := (T t).diam_mul_sin_sq_le hβpos hβle
      (fun i => le_trans (min_le_left _ _) (hα t i))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [h, (T t).inradius_pos]

/-! ### The affine change of variables in `W^{m,p}`: the general lemmas -/

section Affine

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {G : Type*} [NormedAddCommGroup G]

/-- The open set `F⁻¹(Ω)` for the affine map `F x = T x + c`, as an open set. -/
abbrev affinePreimage (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) : Opens E :=
  ⟨(fun x ↦ T x + c) ⁻¹' Ω, Ω.isOpen.preimage (T.continuous.add continuous_const)⟩

/-- (General; belongs beside `setIntegral_comp_affine` in `Numlib/Analysis/Sobolev/Calculus.lean`.)
**The affine change of variables in an `L^p` norm**: for `F x = T x + c`,
`‖f ∘ F‖_{L^p(F⁻¹ A)} = |det T|^{-1/p} ‖f‖_{L^p(A)}`, for every `p`, by the pushforward formula
`map_affine_addHaar`. -/
theorem eLpNorm_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    (f : E → G) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A))
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
        * eLpNorm f p (μ.restrict A) := by
  have hmeas : Measurable fun x ↦ T x + c := (measurableEmbedding_affine T c).measurable
  have h1 : (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)).map (fun x ↦ T x + c)
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| • μ.restrict A := by
    rw [← Measure.restrict_map hmeas hA, map_affine_addHaar, Measure.restrict_smul]
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero
    (by simp [(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero]), ← h1,
    (measurableEmbedding_affine T c).eLpNorm_map_measure]
  rfl

/-- (General.) `L^p` membership transports along an affine map, onto the preimage. -/
theorem memLp_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    {f : E → G} {p : ℝ≥0∞} (hf : MemLp f p (μ.restrict A)) :
    MemLp (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)) := by
  rw [memLp_iff, eLpNorm_comp_affine T c hA]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    hf

/-- (General; the all-orders affine form of `MemSobolev.comp_diffeoOn` of
`Numlib/Analysis/Sobolev/Calculus.lean`.) **Membership of `W^{m,p}` transports along an affine
map**: `v ∈ W^{m,p}(Ω)` gives `v ∘ F ∈ W^{m,p}(F⁻¹ Ω)` for `F x = T x + c`, the weak derivatives
being `x ↦ ∂^n v (F x) ∘ (T, …, T)` (`HasWeakIteratedFDerivOn.comp_affineEquiv`). -/
theorem memSobolev_comp_affine [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memLp_comp_affine T c Ω.isOpen.measurableSet h.1, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  refine ⟨_, hw.comp_affineEquiv T c, ?_⟩
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ : Fin n ↦ (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse of the affine map `x ↦ T x + c` is `y ↦ T⁻¹ y + (-T⁻¹ c)`, and the preimage of
the preimage is the set itself. -/
theorem affinePreimage_symm (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    affinePreimage T.symm (-T.symm c) (affinePreimage T c Ω) = Ω := by
  ext y
  simp

/-- (General.) **Membership of `W^{m,p}` is equivalent along an affine map.** -/
theorem memSobolev_comp_affine_iff [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} :
    MemSobolev v m p Ω μ ↔ MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memSobolev_comp_affine T c, fun h ↦ ?_⟩
  have := memSobolev_comp_affine T.symm (-T.symm c) h
  rw [affinePreimage_symm] at this
  simpa using this

/-- (General.) **The seminorm bound of the affine change of variables**, (10.3.5) of
[han2009theoretical] Theorem 10.3.4 for the tensor seminorm and every `p`:
`|v ∘ F|_{m,p,F⁻¹ Ω} ≤ ‖T‖^m |det T|^{-1/p} |v|_{m,p,Ω}`, since
`∂^m (v ∘ F) x = ∂^m v (F x) ∘ (T, …, T)` has norm at most `‖T‖^m ‖∂^m v (F x)‖`
(`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`) and the `L^p` norm transports with
the factor `|det T|^{-1/p}` (`eLpNorm_comp_affine`). -/
theorem sobolevSeminorm_comp_affine_le [NormedSpace ℝ G] [CompleteSpace G] (T : E ≃L[ℝ] E) (c : E)
    {Ω : Opens E} {v : E → G} {m : ℕ} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      ≤ ENNReal.ofReal (‖(T : E →L[ℝ] E)‖ ^ m)
        * (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
          * sobolevSeminorm v m p Ω μ) := by
  obtain ⟨w, hw, hwp⟩ := h.2 m le_rfl
  have hw' := hw.comp_affineEquiv T c
  -- the chosen weak derivatives are `w` and its transport, almost everywhere
  have e1 : sobolevSeminorm v m p Ω μ = eLpNorm w p (μ.restrict Ω) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_)
    exact hw.weakIteratedFDeriv_ae_eq
  have e2 : sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      = eLpNorm (fun x ↦ (w (T x + c)).compContinuousLinearMap fun _ ↦ (T : E →L[ℝ] E)) p
        (μ.restrict ((fun x ↦ T x + c) ⁻¹' Ω)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (affinePreimage T c Ω).isOpen.measurableSet).2 ?_)
    exact hw'.weakIteratedFDeriv_ae_eq
  rw [e1, e2, ← eLpNorm_comp_affine T c Ω.isOpen.measurableSet,
    ← Real.enorm_eq_ofReal (by positivity), ← eLpNorm_const_smul]
  refine eLpNorm_mono_ae ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ : Fin m ↦
      (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp))
      |>.aestronglyMeasurable
  · simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) m)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

end Affine

/-! ### Theorem 10.3.4 -/

section Theorem1034

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The determinant of the inverse of `T` is the inverse of the determinant of `T`. -/
theorem det_symm_eq_inv (T : 𝔼 ≃L[ℝ] 𝔼) :
    LinearMap.det (T.symm : 𝔼 →ₗ[ℝ] 𝔼) = (LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← LinearMap.det_comp]
  have : (T.symm : 𝔼 →ₗ[ℝ] 𝔼).comp (T : 𝔼 →ₗ[ℝ] 𝔼) = LinearMap.id :=
    LinearMap.ext fun x ↦ T.symm_apply_apply x
  rw [this, LinearMap.det_id]

/-- The constants of (10.3.5)–(10.3.6) in `ℝ≥0∞`: `ofReal (a^m) * ofReal |x| ^ (1/2)` is
`ofReal (a^m |x|^{1/2})`. -/
theorem ofReal_pow_mul_ofReal_abs_rpow {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (x : ℝ) :
    ENNReal.ofReal (a ^ m) * ENNReal.ofReal |x| ^ (1 / (2 : ℝ≥0∞)).toReal
      = ENNReal.ofReal (a ^ m * |x| ^ (1 / 2 : ℝ)) := by
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h2, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (pow_nonneg ha m)]

/-- **Theorem 10.3.4** (affine change of variables in `H^m`). Let `x = T x̂ + b` be a bijection of
the reference element `K̂` onto the element `K`, both open subsets of `ℝ^d`, and let
`v̂ = v ∘ F`, `F x̂ = T x̂ + b`. Then `v ∈ H^m(K)` if and only if `v̂ ∈ H^m(K̂)`, and the estimates
(10.3.5) `|v̂|_{m,K̂} ≤ ‖T‖^m |det T|^{-1/2} |v|_{m,K}` and (10.3.6)
`|v|_{m,K} ≤ ‖T⁻¹‖^m |det T|^{1/2} |v̂|_{m,K̂}` hold.

`H^m(K)` is `Chapter07.definition_7_2_2 m 2 K` (the bundled reading of Definition 7.2.2), and the
seminorm `|·|_{m,K}` is the backbone's `sobolevSeminorm · m 2 K volume`, the `L²(K)` norm of the
operator norm of the derivative tensor of order `m`. That seminorm is equivalent to the book's
`(∑_{|α| = m} ‖∂^α v‖²_{L²(K)})^{1/2}` with constants depending on `d` and `m` only (the book's
`c`, which it does not specify); for the tensor seminorm the constant is exactly `1`, and this is
what is proved: `∂^m v̂ (x̂) = ∂^m v (F x̂) ∘ (T, …, T)` has operator norm at most
`‖T‖^m ‖∂^m v (F x̂)‖`, and the change of variables `x = F x̂` in the `L²` integral contributes
`|det T|^{-1/2}` (`sobolevSeminorm_comp_affine_le`, `eLpNorm_comp_affine`); (10.3.6) is (10.3.5)
for `F⁻¹`. The membership equivalence is `memSobolev_comp_affine_iff`, from the backbone's
`HasWeakIteratedFDerivOn.comp_affineEquiv`. `‖T‖` is the operator norm of `T` on Euclidean
`ℝ^d` and `det T` the determinant of its linear map. -/
theorem theorem_10_3_4 (T : 𝔼 ≃L[ℝ] 𝔼) (b : 𝔼) (Khat K : Opens 𝔼)
    (hK : (fun x ↦ T x + b) '' Khat = K) (m : ℕ) (v : 𝔼 → ℝ) :
    (Chapter07.definition_7_2_2 m 2 K v ↔
      Chapter07.definition_7_2_2 m 2 Khat (fun x ↦ v (T x + b))) ∧
    (Chapter07.definition_7_2_2 m 2 K v →
      sobolevSeminorm (fun x ↦ v (T x + b)) m 2 Khat volume
        ≤ ENNReal.ofReal (‖(T : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (-(1 / 2 : ℝ)))
          * sobolevSeminorm v m 2 K volume) ∧
    (Chapter07.definition_7_2_2 m 2 K v →
      sobolevSeminorm v m 2 K volume
        ≤ ENNReal.ofReal
            (‖(T.symm : 𝔼 →L[ℝ] 𝔼)‖ ^ m * |LinearMap.det (T : 𝔼 →ₗ[ℝ] 𝔼)| ^ (1 / 2 : ℝ))
          * sobolevSeminorm (fun x ↦ v (T x + b)) m 2 Khat volume) := by
  -- `K̂` is the preimage of `K`
  have hKhat : Khat = affinePreimage T b K := by
    ext x
    change x ∈ (Khat : Set 𝔼) ↔ T x + b ∈ (K : Set 𝔼)
    rw [← hK]
    exact ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ ↦ by
      rwa [← T.injective (add_right_cancel hxy)]⟩
  subst hKhat
  refine ⟨memSobolev_comp_affine_iff T b, fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (sobolevSeminorm_comp_affine_le T b h).trans (le_of_eq ?_)
    rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _), abs_inv,
      Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
  · have h' : MemSobolev (fun x ↦ v (T x + b)) m 2 (affinePreimage T b K) volume :=
      memSobolev_comp_affine T b h
    have key := sobolevSeminorm_comp_affine_le T.symm (-T.symm b) h'
    rw [affinePreimage_symm] at key
    have hfun : (fun y ↦ v (T (T.symm y + -T.symm b) + b)) = v := by
      funext y
      simp
    rw [hfun] at key
    refine key.trans (le_of_eq ?_)
    rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _), det_symm_eq_inv, inv_inv]

end Theorem1034

end AtkinsonHan.Chapter10
