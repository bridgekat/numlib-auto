import Numlib.Analysis.Sobolev.Boundary.ChartGraph
import Numlib.Analysis.Sobolev.Extension
import NumlibSurface.Brezis.Chapter09.Section01

/-!
# Brezis §9.2: extension operators

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.2, on `ℝ^N = EuclideanSpace ℝ (Fin (d + 1))` — the
dimension is written `N = d + 1` because the section singles out the last coordinate `x_N`.

The notation of the section is the backbone's (`Numlib/Analysis/Sobolev/Chart`): the half space
`ℝ^N_+ = {x_N > 0}` is `EuclideanSpace.upperHalfSpace d`, the cylinder
`Q = {|x'| < 1, |x_N| < 1}` is `unitChartCube d`, `Q_+ = Q ∩ ℝ^N_+` is `unitChartCubePos d` and
`Q_0 = {(x', 0) : |x'| < 1}` is `unitChartCubeZero d`; as open sets, `Q` is `unitChartCubeOpens d`
and `Q_+` is `posHalf e_N Q`, `e_N` the last basis vector, whose carrier is `unitChartCubePos d`
(`coe_posHalf_unitChartCubeOpens`). "Ω of class `C^1`" is `IsClassC1 Ω`, the book's definition
by local charts `H : Q → U` (`IsOfClassC`, `isOfClassC_iff`), which is the backbone's
`IsContDiffChartDomain 1 Ω` (decision D9 of the planning brief); Atkinson–Han's definition by
local graphs, `IsContDiffDomain 1 Ω`, is equivalent to it (`isClassC1_of_isContDiffDomain`,
and the converse `isContDiffDomain_of_isClassC1` by the implicit function theorem,
`IsContDiffChartDomain.isContDiffDomain` of `Numlib/Analysis/Sobolev/Boundary/ChartGraph`). The
extension by reflection `u^⋆` of Lemma 9.2 is the backbone's `evenReflection e_N u`, the odd
reflection `f^□` of its proof is `oddReflection e_N f`.

## Main results

* `IsOfClassC`, `isOfClassC_iff`, `IsClassC1`, `isClassC1_of_isContDiffDomain`,
  `isContDiffDomain_of_isClassC1`, `isClassC1_iff_isContDiffDomain` — the Definition, and its
  equivalence with Atkinson–Han's.
* `theorem_9_7`, `theorem_9_7_halfSpace` — the extension operator
  `P : W^{1,p}(Ω) → W^{1,p}(ℝ^N)` for `Ω` of class `C^1` with bounded boundary, and for the half
  space.
* `lemma_9_2`, `lemma_9_2_halfSpace` — extension by reflection from `Q_+` to `Q` and from `ℝ^N_+`
  to `ℝ^N`, with the identities (7) and (8) and the constant `2` for the book's norms.
* `lemma_9_3` — the partition of unity.
* `corollary_9_8`, `corollary_9_8_dense`, `corollary_9_8_bounded` — density of the restrictions of
  `C_c^∞(ℝ^N)` functions in `W^{1,p}(Ω)`, `1 ≤ p < ∞`.
-/

open Filter MeasureTheory Metric Topology TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

namespace Brezis.Chapter09

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The last basis vector `e_N` of `ℝ^N`, the normal of the hyperplane `x_N = 0`. -/
local notation "eN" => EuclideanSpace.single (Fin.last d) (1 : ℝ)

/-! ### Open sets of class `C^m` -/

/-- **The Definition of "`Ω` is of class `C^m`"** (§9.2 for `m = 1`, §9.6 for general `m`): for
every `x ∈ ∂Ω = Γ` there are a neighbourhood `U` of `x` in `ℝ^N` and a bijective map
`H : Q → U` such that `H ∈ C^m(Q̄)`, `H⁻¹ ∈ C^m(Ū)`, `H(Q_+) = U ∩ Ω` and `H(Q_0) = U ∩ Γ`
(`isOfClassC_iff` for this wording); the backbone's chart condition `IsContDiffChartDomain`.

The book defines "of class `C^∞`" as "of class `C^m` for every `m`"; `IsOfClassC ⊤ Ω` asks for
one chart of class `C^∞` at each boundary point, which is a priori stronger and is what the
regularity theorems of §9.6 and chapter 10 use. The two readings agree through the implicit
function theorem (`IsContDiffChartDomain.isContDiffDomain`, the deferred converse of
`isClassC1_of_isContDiffDomain`): a boundary that is locally a `C^m` graph for every `m` is a
`C^∞` graph. -/
def IsOfClassC (m : ℕ∞) (Ω : Set 𝔼) : Prop :=
  IsContDiffChartDomain m Ω

/-- **The Definition of "`Ω` is of class `C^m`", unfolded to the book's wording**, for an
integer `m`: `Ω` is open and for every `x ∈ ∂Ω` there are an open neighbourhood `U` of `x` and a
map `H : Q → U`, a bijection with inverse `H⁻¹`, with `H ∈ C^m(Q̄)`, `H⁻¹ ∈ C^m(Ū)`,
`H(Q_+) = U ∩ Ω` and `H(Q_0) = U ∩ ∂Ω`. -/
theorem isOfClassC_iff (m : ℕ) (Ω : Set 𝔼) :
    IsOfClassC m Ω ↔ IsOpen Ω ∧ ∀ x ∈ frontier Ω, ∃ (U : Set 𝔼) (H Hinv : 𝔼 → 𝔼),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ m H (closure (unitChartCube d)) ∧
      ContDiffOn ℝ m Hinv (closure U) ∧ Set.BijOn H (unitChartCube d) U ∧
      Set.InvOn Hinv H (unitChartCube d) U ∧ H '' unitChartCubePos d = U ∩ Ω ∧
      H '' unitChartCubeZero d = U ∩ frontier Ω := by
  constructor
  · rintro ⟨hΩ, h⟩
    refine ⟨hΩ, fun x hx ↦ ?_⟩
    obtain ⟨c, hc⟩ := h x hx
    exact ⟨c.U, c.toFun, c.invFun, c.isOpen_U, hc, c.contDiffOn, c.contDiffOn_invFun, c.bijOn,
      c.invOn, c.image_pos, c.image_zero⟩
  · rintro ⟨hΩ, h⟩
    refine ⟨hΩ, fun x hx ↦ ?_⟩
    obtain ⟨U, H, Hinv, hU, hxU, hH, hHinv, hbij, hinv, hpos, hzero⟩ := h x hx
    exact ⟨⟨U, H, Hinv, hU, hH, hHinv, hbij, hinv, hpos, hzero⟩, hxU⟩

/-- An open set of class `C^m` is of class `C^k` for every `k ≤ m`. -/
theorem IsOfClassC.of_le {m k : ℕ∞} {Ω : Set 𝔼} (h : IsOfClassC m Ω) (hkm : k ≤ m) :
    IsOfClassC k Ω :=
  IsContDiffChartDomain.of_le h (by exact_mod_cast hkm)

/-- An open set of class `C^m` is open. -/
theorem IsOfClassC.isOpen {m : ℕ∞} {Ω : Set 𝔼} (h : IsOfClassC m Ω) : IsOpen Ω :=
  h.1

/-- **The Definition of "`Ω` is of class `C^1`"** (§9.2): `IsOfClassC 1 Ω`, the hypothesis of
Theorem 9.7, Corollary 9.8, and of Corollaries 9.14–9.15, Theorem 9.16 and Remark 21 in §9.3
and §9.4. -/
abbrev IsClassC1 (Ω : Set 𝔼) : Prop :=
  IsOfClassC 1 Ω

/-- **The two readings of "`C^1` domain" agree, one way**: Atkinson–Han's `C^1` domains
(`IsContDiffDomain 1 Ω`, Definition 7.2.1, the definition by local graphs of
`Numlib/Analysis/Sobolev/Domain`) are of class `C^1` in Brezis's sense, a local graph giving a
local chart by straightening (`IsContDiffDomain.isContDiffChartDomain`). The converse,
`isContDiffDomain_of_isClassC1`, is the implicit function theorem. -/
theorem isClassC1_of_isContDiffDomain {Ω : Set 𝔼} (h : IsContDiffDomain 1 Ω) : IsClassC1 Ω :=
  h.isContDiffChartDomain

/-- **The two readings of "`C^1` domain" agree, the other way**: an open set of class `C^1` in
Brezis's sense (`IsClassC1 Ω`, by local charts) is a `C^1` domain in Atkinson–Han's sense
(`IsContDiffDomain 1 Ω`, Definition 7.2.1, by local graphs). This is the backbone's chart ⇒
graph bridge `IsContDiffChartDomain.isContDiffDomain`
(`Numlib/Analysis/Sobolev/Boundary/ChartGraph`): the implicit function theorem applied to the
last coordinate of the inverse chart, whose derivative is invertible, after a rigid motion
sending its gradient to `e_N`. -/
theorem isContDiffDomain_of_isClassC1 {Ω : Set 𝔼} (h : IsClassC1 Ω) : IsContDiffDomain 1 Ω :=
  h.isContDiffDomain le_rfl WithTop.coe_ne_top

/-- **The two readings of "`C^1` domain" agree**: Brezis's `IsClassC1 Ω` (local charts) is
Atkinson–Han's `IsContDiffDomain 1 Ω` (local graphs). -/
theorem isClassC1_iff_isContDiffDomain {Ω : Set 𝔼} : IsClassC1 Ω ↔ IsContDiffDomain 1 Ω :=
  ⟨isContDiffDomain_of_isClassC1, isClassC1_of_isContDiffDomain⟩

/-! ### Theorem 9.7 -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The three properties of the extension operator of Theorem 9.7, with the book's norm
`‖·‖_{W^{1,p}}` (`bookNorm`), from the backbone's statement with the norm of the type. -/
theorem exists_extension_of_backbone {Ω : Opens 𝔼}
    (h : ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        ‖P u‖ ≤ C * ‖u‖) :
    ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        bookNorm (P u) ≤ C * bookNorm u := by
  obtain ⟨P, C, hP⟩ := h
  refine ⟨P, ((d + 1 : ℕ) + 1) * max C 0, fun u ↦ ⟨(hP u).1, ?_, ?_⟩⟩
  · refine (hP u).2.1.trans ?_
    gcongr
    calc C ≤ max C 0 := le_max_left _ _
      _ = 1 * max C 0 := (one_mul _).symm
      _ ≤ ((d + 1 : ℕ) + 1) * max C 0 :=
          mul_le_mul_of_nonneg_right (by norm_cast; omega) (le_max_right _ _)
  · calc bookNorm (P u) ≤ ((d + 1 : ℕ) + 1) * ‖P u‖ := (bookNorm_equiv (P u)).2
      _ ≤ ((d + 1 : ℕ) + 1) * (C * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hP u).2.2 (by positivity)
      _ ≤ ((d + 1 : ℕ) + 1) * (max C 0 * bookNorm u) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc C * ‖u‖ ≤ max C 0 * ‖u‖ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
            _ ≤ max C 0 * bookNorm u :=
                mul_le_mul_of_nonneg_left (bookNorm_equiv u).1 (le_max_right _ _)
      _ = ((d + 1 : ℕ) + 1) * max C 0 * bookNorm u := by ring

/-- **Theorem 9.7.** Suppose that `Ω` is of class `C^1` with `Γ = ∂Ω` bounded. Then there is a
linear extension operator `P : W^{1,p}(Ω) → W^{1,p}(ℝ^N)`, `1 ≤ p ≤ ∞`, such that for all
`u ∈ W^{1,p}(Ω)`: `P u|_Ω = u`, `‖P u‖_{L^p(ℝ^N)} ≤ C ‖u‖_{L^p(Ω)}` and
`‖P u‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(Ω)}`, where `C` depends only on `Ω` (and `p`). The
operator is bounded, and the last bound is stated for the book's norm `‖·‖_{W^{1,p}}`
(`bookNorm`). -/
theorem theorem_9_7 {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ (P : sobolevSpace (d + 1) p Ω →L[ℝ] sobolevSpace (d + 1) p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict Ω) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone (SobolevEuclidean.exists_extensionL hΩ hΓ)

/-- **Theorem 9.7 for the half space `Ω = ℝ^N_+`.** There is a linear extension operator
`P : W^{1,p}(ℝ^N_+) → W^{1,p}(ℝ^N)`, `1 ≤ p ≤ ∞`, with the three properties of Theorem 9.7:
the extension by reflection of Lemma 9.2. -/
theorem theorem_9_7_halfSpace :
    ∃ (P : sobolevSpace (d + 1) p (upperHalfSpaceOpens d) →L[ℝ] sobolevSpace (d + 1) p ⊤)
      (C : ℝ), ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone SobolevEuclidean.exists_extensionL_upperHalfSpace

/-- **Remark 9.** Lemma 9.2 gives a very simple construction of extension operators for certain
open sets that are not of class `C^1`: for the square `Ω = {x ∈ ℝ² ; 0 < x_1 < 1, 0 < x_2 < 1}`
(`EuclideanSpace.rect 0 1 0 1`) there is a linear extension operator
`P : W^{1,p}(Ω) → W^{1,p}(ℝ²)`, `1 ≤ p ≤ ∞`, with the three properties of Theorem 9.7 — by four
successive reflections (Figure 6) reaching `ũ ∈ W^{1,p}(Ω̃)`, `Ω̃ = (−1, 3)²`, followed by a
cut-off: the backbone's `SobolevEuclidean.exists_extensionL_unitSquare`. -/
theorem remark_9_9 :
    ∃ (P : sobolevSpace 2 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ] sobolevSpace 2 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))]
            SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        bookNorm (P u) ≤ C * bookNorm u :=
  exists_extension_of_backbone (d := 1) SobolevEuclidean.exists_extensionL_unitSquare

/-! ### Lemma 9.2 -/

/-- The reflection across `x_N = 0` fixes the basis vectors `e_i`, `i < N`, and sends `e_N` to
`−e_N`; so the reflected derivative in a basis direction has the norm of the even reflection of
that partial derivative. -/
theorem norm_reflectFDeriv_single (w : 𝔼 → 𝔼 →L[ℝ] ℝ) (x : 𝔼) (i : Fin (d + 1)) :
    ‖reflectFDeriv eN w x (EuclideanSpace.single i 1)‖
      = ‖evenReflection eN (fun z ↦ w z (EuclideanSpace.single i 1)) x‖ := by
  by_cases hx : 0 ≤ ⟪x, eN⟫_ℝ
  · rw [reflectFDeriv_of_nonneg _ hx, evenReflection_of_nonneg _ hx]
  · rw [reflectFDeriv_of_neg _ (not_le.1 hx), evenReflection_of_neg _ (not_le.1 hx),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    by_cases hi : i = Fin.last d
    · subst hi
      rw [hyperplaneReflection_apply_self, map_neg, norm_neg]
    · have h2 : ⟪(EuclideanSpace.single i (1 : ℝ) : 𝔼), eN⟫_ℝ = 0 := by
        rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
        simp [hi]
      rw [hyperplaneReflection_apply_of_inner_eq_zero _ h2]

/-- The odd reflection only sees the function up to a null set of `V_+`. -/
theorem oddReflection_congr_ae {V : Opens 𝔼} (hV : hyperplaneReflection eN '' (V : Set 𝔼) = V)
    {f g : 𝔼 → ℝ} (h : f =ᵐ[volume.restrict (posHalf eN V : Set 𝔼)] g) :
    oddReflection eN f =ᵐ[volume.restrict (V : Set 𝔼)] oddReflection eN g := by
  have hv0 : (eN : 𝔼) ≠ 0 :=
    ne_zero_of_norm_ne_zero (by rw [norm_single_last_one]; exact one_ne_zero)
  filter_upwards [evenReflection_congr_ae hv0 hV h] with x hx
  simp only [evenReflection, oddReflection] at hx ⊢
  split_ifs at hx ⊢ with h0
  · exact hx
  · rw [hx]

/-- **Lemma 9.2, for any open `V` symmetric under the reflection across `x_N = 0`.** For
`u ∈ W^{1,p}(V_+)`, `V_+ = V ∩ {x_N > 0}`, `1 ≤ p ≤ ∞`, the extension by reflection `u^⋆` lies
in `W^{1,p}(V)`, with `‖u^⋆‖_{L^p(V)} ≤ 2 ‖u‖_{L^p(V_+)}`,
`‖u^⋆‖_{W^{1,p}(V)} ≤ 2 ‖u‖_{W^{1,p}(V_+)}` (the book's norms), and the identities (7)
`∂_i u^⋆ = (∂_i u)^⋆` for `i < N` and (8) `∂_N u^⋆ = (∂_N u)^□`. The cases `V = Q` and
`V = ℝ^N` are `lemma_9_2` and `lemma_9_2_halfSpace`. -/
theorem lemma_9_2_of_symm {V : Opens 𝔼} (hV : hyperplaneReflection eN '' (V : Set 𝔼) = V)
    (u : sobolevSpace (d + 1) p (posHalf eN V)) :
    ∃ w : sobolevSpace (d + 1) p V,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict V)
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (posHalf eN V)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume.restrict (V : Set 𝔼)]
        oddReflection eN (partialDeriv u (Fin.last d)) := by
  have hv : ‖(eN : 𝔼)‖ = 1 := norm_single_last_one
  have hv0 : (eN : 𝔼) ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨W, hW, hWp, hWi, -, -⟩ := exists_hasWeakFDerivOn_fn_gradient u
  -- the reflected element, with its specification and the operator forgotten
  obtain ⟨w, hw1, hw2, hwd⟩ : ∃ w : sobolevSpace (d + 1) p V,
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (V : Set 𝔼)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict V)
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (posHalf eN V)) ∧
      ∀ i, partialDeriv w i =ᵐ[volume.restrict (V : Set 𝔼)]
        fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i 1) := by
    refine ⟨SobolevEuclidean.evenReflectionL hv hV u, SobolevMultiIndex.fn_evenReflectionL hv hV u,
      SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV u, fun i ↦ ?_⟩
    have := SobolevMultiIndex.weakDeriv_evenReflection_single hv hV u hW hWp i
    rwa [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] at this
  refine ⟨w, hw1, hw2, ?_, ?_, ?_⟩
  -- the book's norm: each partial derivative of `w` is bounded by twice the one of `u`
  · have hle : ∀ i, ‖partialDeriv w i‖ ≤ 2 * ‖partialDeriv u i‖ := fun i ↦ by
      have hm1 : AEStronglyMeasurable (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i 1))
          (volume.restrict (V : Set 𝔼)) :=
        (Lp.aestronglyMeasurable _).congr (hwd i)
      have hm2 : AEStronglyMeasurable (fun z ↦ W z (EuclideanSpace.single i 1))
          (volume.restrict (posHalf eN V : Set 𝔼)) :=
        (Lp.aestronglyMeasurable _).congr (hWi i).symm
      have h1 : eLpNorm (partialDeriv w i) p (volume.restrict (V : Set 𝔼))
          ≤ 2 * eLpNorm (partialDeriv u i) p (volume.restrict (posHalf eN V : Set 𝔼)) := by
        rw [eLpNorm_congr_ae (hwd i), eLpNorm_congr_norm_ae hm1
          (aestronglyMeasurable_evenReflection hv0 hV hm2)
          (Eventually.of_forall fun x ↦ norm_reflectFDeriv_single W x i),
          ← eLpNorm_congr_ae (hWi i)]
        exact eLpNorm_evenReflection_le hv0 hV hp hm2
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Lp.eLpNorm_ne_top _)) h1
    have h0 : ‖SobolevMultiIndex.weakDeriv w 0‖ ≤ 2 * ‖SobolevMultiIndex.weakDeriv u 0‖ := by
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Lp.eLpNorm_ne_top _)) hw2
    calc bookNorm w ≤ 2 * ‖SobolevMultiIndex.weakDeriv u 0‖ + ∑ i, 2 * ‖partialDeriv u i‖ :=
          add_le_add h0 (Finset.sum_le_sum fun i _ ↦ hle i)
      _ = 2 * bookNorm u := by rw [bookNorm, mul_add, Finset.mul_sum]
  -- (7): the tangential derivatives are even reflections
  · intro i
    have h2 : ⟪(EuclideanSpace.single i.castSucc (1 : ℝ) : 𝔼), eN⟫_ℝ = 0 := by
      rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
      simp [Fin.castSucc_ne_last]
    have h3 : (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single i.castSucc 1))
        =ᵐ[volume.restrict (V : Set 𝔼)]
          evenReflection eN (fun z ↦ W z (EuclideanSpace.single i.castSucc 1)) :=
      Eventually.of_forall fun x ↦ reflectFDeriv_apply_of_inner_eq_zero _ W h2 x
    exact (hwd i.castSucc).trans (h3.trans (evenReflection_congr_ae hv0 hV (hWi i.castSucc)))
  -- (8): the normal derivative is an odd reflection
  · have h3 : (fun x ↦ reflectFDeriv eN W x (EuclideanSpace.single (Fin.last d) 1))
        =ᵐ[volume.restrict (V : Set 𝔼)] oddReflection eN (fun z ↦ W z eN) :=
      Eventually.of_forall fun x ↦ reflectFDeriv_apply_self _ W x
    exact (hwd (Fin.last d)).trans (h3.trans (oddReflection_congr_ae hV (hWi (Fin.last d))))

/-- **Lemma 9.2.** Given `u ∈ W^{1,p}(Q_+)`, `1 ≤ p ≤ ∞`, the extension by reflection
`u^⋆(x', x_N) = u(x', x_N)` for `x_N > 0`, `u(x', −x_N)` for `x_N < 0` (the backbone's
`evenReflection e_N u`) lies in `W^{1,p}(Q)`, with `‖u^⋆‖_{L^p(Q)} ≤ 2 ‖u‖_{L^p(Q_+)}` and
`‖u^⋆‖_{W^{1,p}(Q)} ≤ 2 ‖u‖_{W^{1,p}(Q_+)}` for the book's norms; moreover (7)
`∂_i u^⋆ = (∂_i u)^⋆` for `1 ≤ i ≤ N − 1` and (8) `∂_N u^⋆ = (∂_N u)^□`, where
`f^□(x', x_N) = f(x', x_N)` for `x_N > 0`, `−f(x', −x_N)` for `x_N < 0` (`oddReflection e_N f`).
Here `Q_+` is `posHalf e_N Q`, whose carrier is `unitChartCubePos d`. -/
theorem lemma_9_2 (u : sobolevSpace (d + 1) p (posHalf eN (unitChartCubeOpens d))) :
    ∃ w : sobolevSpace (d + 1) p (unitChartCubeOpens d),
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (unitChartCube d)]
        evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (unitChartCube d))
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (unitChartCubePos d)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume.restrict (unitChartCube d)]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume.restrict (unitChartCube d)]
        oddReflection eN (partialDeriv u (Fin.last d)) := by
  have h := lemma_9_2_of_symm (p := p) hyperplaneReflection_image_unitChartCubeOpens u
  rwa [eLpNorm_restrict_congr_set_eq _ p coe_posHalf_unitChartCubeOpens] at h

/-- **Lemma 9.2 for the half space**: "the conclusion of Lemma 9.2 remains valid if `Q_+` is
replaced by `ℝ^N_+`". Here `ℝ^N_+` is `posHalf e_N ⊤`, whose carrier is `upperHalfSpace d`
(`coe_posHalf_top_eq_upperHalfSpace`). -/
theorem lemma_9_2_halfSpace (u : sobolevSpace (d + 1) p (posHalf eN ⊤)) :
    ∃ w : sobolevSpace (d + 1) p ⊤,
      SobolevMultiIndex.fn w =ᵐ[volume] evenReflection eN (SobolevMultiIndex.fn u) ∧
      eLpNorm (SobolevMultiIndex.fn w) p volume
        ≤ 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) ∧
      bookNorm w ≤ 2 * bookNorm u ∧
      (∀ i : Fin d, partialDeriv w i.castSucc =ᵐ[volume]
        evenReflection eN (partialDeriv u i.castSucc)) ∧
      partialDeriv w (Fin.last d) =ᵐ[volume] oddReflection eN (partialDeriv u (Fin.last d)) := by
  obtain ⟨w, h1, h2, h3, h4, h5⟩ :=
    lemma_9_2_of_symm (p := p) (hyperplaneReflection_image_top (eN : 𝔼)) u
  refine ⟨w, eventuallyEq_restrict_coe_top_iff.1 h1, ?_, h3,
    fun i ↦ eventuallyEq_restrict_coe_top_iff.1 (h4 i), eventuallyEq_restrict_coe_top_iff.1 h5⟩
  rwa [eLpNorm_restrict_coe_top,
    eLpNorm_restrict_congr_set_eq _ p coe_posHalf_top_eq_upperHalfSpace] at h2

/-! ### Lemma 9.3 and Corollary 9.8 -/

/-- **Lemma 9.3 (partition of unity).** Let `Γ ⊆ ℝ^N` be compact and let `U_1, …, U_k` be an
open covering of `Γ`. Then there are `θ_0, θ_1, …, θ_k ∈ C^∞(ℝ^N)` with `0 ≤ θ_i ≤ 1`,
`∑_{i=0}^k θ_i = 1` on `ℝ^N`, `supp θ_i` compact with `supp θ_i ⊆ U_i` for `i ≥ 1`, and
`supp θ_0 ⊆ ℝ^N ∖ Γ`. If moreover `Ω` is open and bounded with `Γ = ∂Ω`, then
`θ_0|_Ω ∈ C_c^∞(Ω)`: the part of the support of `θ_0` in `Ω̄` is a compact subset of `Ω`. -/
theorem lemma_9_3 {Γ : Set 𝔼} (hΓ : IsCompact Γ) {k : ℕ} {U : Fin k → Set 𝔼}
    (hU : ∀ i, IsOpen (U i)) (hΓU : Γ ⊆ ⋃ i, U i) :
    ∃ (θ₀ : 𝔼 → ℝ) (θ : Fin k → 𝔼 → ℝ), ContDiff ℝ ∞ θ₀ ∧ (∀ i, ContDiff ℝ ∞ (θ i)) ∧
      (∀ x, θ₀ x ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i x, θ i x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, θ₀ x + ∑ i, θ i x = 1) ∧ (∀ i, HasCompactSupport (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ U i) ∧ tsupport θ₀ ⊆ Γᶜ ∧
      ∀ Ω : Set 𝔼, IsOpen Ω → Bornology.IsBounded Ω → frontier Ω = Γ →
        IsCompact (tsupport θ₀ ∩ closure Ω) ∧ tsupport θ₀ ∩ closure Ω ⊆ Ω := by
  obtain ⟨θ₀, θ, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hΓ.exists_contDiff_partitionOfUnity hU hΓU
  refine ⟨θ₀, θ, h0, h1, h2, h3, h4, h5, h6, Set.disjoint_left.1 h7, fun Ω hΩ hΩb hΓΩ ↦
    ⟨(isClosed_tsupport θ₀).isCompact_inter_closure_of_isBounded hΩb,
      inter_closure_subset_of_disjoint_frontier hΩ (hΓΩ ▸ h7)⟩⟩

/-- **Corollary 9.8 (density).** Assume that `Ω` is of class `C^1` and let `u ∈ W^{1,p}(Ω)`,
`1 ≤ p < ∞`. Then there is a sequence `(u_n)` from `C_c^∞(ℝ^N)` such that `u_n|_Ω → u` in
`W^{1,p}(Ω)`: the elements `w n` of `W^{1,p}(Ω)` whose functions are the restrictions of the
`u_n` converge to `u`. -/
theorem corollary_9_8 {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace (d + 1) p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto hp' hΩ u

/-- **Corollary 9.8, "in other words"**: for `Ω` of class `C^1` and `1 ≤ p < ∞`, the
restrictions to `Ω` of `C_c^∞(ℝ^N)` functions form a dense subspace of `W^{1,p}(Ω)`. -/
theorem corollary_9_8_dense {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼)) (hp' : p ≠ ⊤) :
    Dense {w : sobolevSpace (d + 1) p Ω | ∃ v : 𝔼 → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] v} := by
  intro u
  obtain ⟨v, hvs, hvc, w, hw, hwu⟩ := corollary_9_8 hΩ hp' u
  exact mem_closure_of_tendsto hwu (Eventually.of_forall fun n ↦ ⟨v n, hvs n, hvc n, hw n⟩)

/-- **Corollary 9.8, the case of a bounded boundary**, proved through the extension operator of
Theorem 9.7 as in the first paragraph of the book's proof: for `Ω` of class `C^1` with `Γ`
bounded and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(Ω)` is the limit in `W^{1,p}(Ω)` of restrictions
of `C_c^∞(ℝ^N)` functions. -/
theorem corollary_9_8_bounded {Ω : Opens 𝔼} (hΩ : IsClassC1 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hp' : p ≠ ⊤)
    (u : sobolevSpace (d + 1) p Ω) :
    ∃ v : ℕ → 𝔼 → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      ∃ w : ℕ → sobolevSpace (d + 1) p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set 𝔼)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isBounded_frontier hp' hΩ hΓ u

end Brezis.Chapter09
