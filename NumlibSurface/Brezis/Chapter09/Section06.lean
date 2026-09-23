import Numlib.Analysis.PDE.Elliptic.Regularity
import NumlibSurface.Brezis.Chapter09.Section05

/-!
# Brezis §9.6: Regularity of weak solutions

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.6, on `ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue
measure: the definition of an open set of class `C^m` (`IsOfClassC`, defined in §9.2 with its
`C^1` case `IsClassC1`), Theorem 9.25 (regularity for the Dirichlet problem, in its four clauses
`H²` with the constant, `H^{m+2}`, `C²(Ω̄)`, `C^∞(Ω̄)`, and the half-space alternative), the three
lemmas 9.6–9.8 of its proof, and Remark 25 (interior regularity and hypoellipticity). Everything
delegates to `Numlib/Analysis/PDE/Elliptic/Regularity`, whose theorems follow the book's proof case
by case (A: `ℝ^N`; B: `ℝ^N_+`; C₁: interior; C₂: near the boundary, through the charts).

## Conventions

* `H^1(Ω) = hSpace N Ω`, `H^1_0(Ω) = hZeroSpace N Ω`, `H^m(Ω) = sobolevSpaceHigher N m 2 Ω`
  (§9.1, §9.4); "`u ∈ H^m(Ω)`" for `u ∈ H^1(Ω)` is the existence of an element of `H^m(Ω)` with
  the same function, and `‖u‖_{H^m}` is the Hilbert norm of the type (`hSpaceHigher`). The weak
  equation (48) is `IsWeakSolutionDirichlet` of §9.5, with the book's integrals.
* The book's `C^k(Ω̄)` (footnote 16 of §9.3) is `ContDiffOnClosure ℝ k · Ω` together with the
  continuity of the function itself on `Ω̄`, as in §9.5; the conclusions of Theorem 9.25 are
  stated in that reading, from the backbone's continuous extensions of the derivatives.
* "`Ω` of class `C^m`" is `IsOfClassC m Ω` (the chart condition `IsContDiffChartDomain`), and
  "`Γ` bounded" is `Bornology.IsBounded (frontier Ω)`; the half space `ℝ^N_+` is
  `EuclideanSpace.upperHalfSpaceOpens d`, and `h ∥ Γ` is `h_N = 0`.
* Theorem 9.25's `C^∞(Ω̄)` clause is stated for a bounded `Ω` (`theorem_9_25_smooth`, where
  `f ∈ C^∞(Ω̄)` gives `f ∈ H^m(Ω)` for every `m`) and, for a `Γ` bounded only, under the
  hypothesis `f ∈ H^m(Ω)` for every `m` (`theorem_9_25_smooth_of_forall_mem`).
* Lemma 9.8 takes the chart `H : Q → U` as a `ContDiffChart 2 Ω` and the open sets `Ω ∩ U`
  and `Q₊` as `Opens` variables with their carriers; its coefficients `a_{kℓ}` are the backbone's
  `Elliptic.chartCoeff H J` and its datum `g̃` is `Elliptic.chartDatum H g`.
* Remark 25 is stated with the book's global hypotheses `u ∈ H^1(Ω)`, `f ∈ H^m(Ω)`; the backbone
  needs only the local ones. The hypoellipticity clause is stated for any open `ω ⊆ Ω` (the
  book's `ω ⊂⊂ Ω` is not needed).
* Theorem 9.26 (Neumann) and Remark 24 (general operators) are stated by the book without proof.
  Of Theorem 9.26, the `H²` clause on the half space is `theorem_9_26_upperHalfSpace` and the
  `H^{m+2}` clause there is `theorem_9_26_upperHalfSpace_higher` (the book's own alternative "or
  else `Ω = ℝ^N_+`" in Theorem 9.25, inherited by 9.26; the `H^{m+2}` clause is stated as a
  membership, the book's norm bound needing a solution map for the Neumann problem that the
  backbone does not build). The boundary condition `∂u/∂n = 0` that the `H²` solution
  satisfies — meaningful once the trace exists — is
  `theorem_9_26_normalDeriv`, on a bounded `C¹` domain in the graph form `IsContDiffDomain 1 Ω`
  of `Numlib/Analysis/Sobolev/Boundary/`, with the normal derivative
  `BoundaryData.TraceFamily.normalTrace`. Theorem 9.26 on a general `C²` domain and both
  halves of Remark 24 are not formalized; see `## Not formalized here`.

## Main results

* `theorem_9_25`, `theorem_9_25_upperHalfSpace`, `theorem_9_25_higher`,
  `theorem_9_25_contDiffOn`, `theorem_9_25_smooth`, `theorem_9_25_smooth_of_forall_mem`.
* `lemma_9_6`, `lemma_9_7`, `lemma_9_8`.
* `remark_9_25`, `remark_9_25_smooth`, `remark_9_25_local`.
* `theorem_9_26_upperHalfSpace`, `theorem_9_26_upperHalfSpace_higher`,
  `theorem_9_26_normalDeriv`.

## Not formalized here

Everything §9.6 proves is here. What is left out is what the book states without proof, and the
line falls exactly at the boundary of a general domain: proved nearby are Theorem 9.25 in all its
clauses for the Dirichlet problem (`theorem_9_25`, `theorem_9_25_higher`,
`theorem_9_25_contDiffOn`, `theorem_9_25_smooth`), Theorem 9.26's `H²` and `H^{m+2}` clauses on
the half space (`theorem_9_26_upperHalfSpace`, `theorem_9_26_upperHalfSpace_higher`) and
Theorem 9.26's boundary condition for an `H²` solution (`theorem_9_26_normalDeriv`).

* **Theorem 9.26 on a general domain.** For `Ω` of class `C²` with `Γ` bounded, `f ∈ L²(Ω)` and
  `u ∈ H^1(Ω)` with `∫_Ω ∇u·∇φ + ∫_Ω u φ = ∫_Ω f φ` for *every* `φ ∈ H^1(Ω)` (49): the
  conclusions of Theorem 9.25, `u ∈ H²(Ω)` with `‖u‖_{H²} ≤ C ‖f‖_{L²}` and `u ∈ H^{m+2}(Ω)` for
  `f ∈ H^m(Ω)` on a `C^{m+2}` domain. The book says only "the proof of Theorem 9.26 is entirely
  analogous", and the analogy fails at case C₂: a Neumann solution cut off by a partition
  function `θᵢ` does **not** solve a homogeneous Neumann problem on `Ω ∩ Uᵢ` but the
  inhomogeneous one `∂(θᵢu)/∂n = (∂θᵢ/∂n) u` on `Γ ∩ Uᵢ`. (One dimension: `Ω = (0, ∞)`,
  `θ ∈ C_c^∞(−1, 1)` with `θ(0) = 1`, `θ'(0) = a ≠ 0`; a Neumann solution has `u'(0) = 0`, so
  `(θu)'(0) = a u(0) ≠ 0`.) The correct proof cuts off the test function instead — the method of
  translations with `ψ = D_{−h}(ζ² D_h w)`, a Caccioppoli estimate — which the backbone does not
  have; the details and the cost are in the `## Not formalized here` of
  `Numlib/Analysis/PDE/Elliptic/Regularity.lean`.
* **Remark 24, the Dirichlet half.** The conclusions of Theorem 9.25 for the Dirichlet problem of
  a general second-order elliptic operator: if `u ∈ H^1_0(Ω)` solves (50) — `a_{ij} ∈ C¹(Ω̄)`
  elliptic, `a_i ∈ C(Ω̄)`, `a₀ ∈ L^∞(Ω)`, with bounded derivatives of the coefficients when `Ω`
  is unbounded (footnote 26) — with `f ∈ L²(Ω)`, then `u ∈ H²(Ω)`; and for `m ≥ 1`,
  `f ∈ H^m(Ω)`, `a_{ij} ∈ C^{m+1}(Ω̄)`, `a_i ∈ C^m(Ω̄)` give `u ∈ H^{m+2}(Ω)`. The book gives no
  proof; the route is real (case C₂ of Theorem 9.25 is already the variable-coefficient estimate,
  and the lower-order terms move to the right-hand side) and is recorded in the backbone module's
  own `## Not formalized here`, at about 600 lines beyond Theorem 9.25. No node of the corpus
  consumes it.
* **Remark 24, the Neumann half** ("or Neumann"). The same conclusions for the Neumann problem of
  the general operator, together with the conormal boundary condition
  `∑_{ij} a_{ij} ν_j γ(∂_i u) = 0` `σ`-a.e. on `Γ`. This needs the `H²` regularity of the Neumann
  problem for a variable-coefficient operator — hence the missing Caccioppoli machinery above,
  which the Laplacian case already lacks on a general domain — and, for the boundary-condition
  clause alone (with `H²` as a hypothesis, as in `theorem_9_26_normalDeriv`, about 150 lines), an
  `H²` Green formula for the conormal derivative: the analogue of
  `BoundaryData.TraceFamily.green_laplacian` for `Elliptic.generalForm`, obtained from
  `BoundaryData.TraceFamily.green` against the products `a_{ij} ∂_i u ∈ H^1(Ω)`, which needs
  `a_{ij} ∈ C¹(Ω̄)` and the product rule in `H^1`. Neither is in the backbone.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

section Interior

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`, the basis of the backbone's multi-index Sobolev spaces. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 25: interior regularity -/

/-- **Remark 25 (interior regularity).** Let `Ω` be an arbitrary open set and let `u ∈ H^1(Ω)`
be such that `∫_Ω ∇u · ∇φ = ∫_Ω f φ` for all `φ ∈ C_c^∞(Ω)`. We suppose that `f ∈ H^m(Ω)`. Then
`θu ∈ H^{m+2}(Ω)` for every `θ ∈ C_c^∞(Ω)`: we say that `u ∈ H^{m+2}_loc(Ω)` — the backbone's
`MemSobolevMultiIndexLoc` (membership in `H^{m+2}(ω)` for every `ω ⊂⊂ Ω`), and the book's
`θ`-reading. The proof "proceeds as in case C₁ and argues by induction on `m`"
(`Elliptic.regularity_interior_higher`, which assumes only `u ∈ H^1_loc(Ω)`, `f ∈ H^m_loc(Ω)`);
the `θ`-reading is `MemSobolevMultiIndexLoc.smul_testFunction`, restricted from `ℝ^N` to `Ω`. -/
theorem remark_9_25 (m : ℕ) (u : hSpace N Ω) (f : sobolevSpaceHigher N m 2 Ω)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn f x * φ x) :
    MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) (m + 2) 2 Ω volume ∧
    ∀ θ : 𝓓(Ω, ℝ), ∃ v : sobolevSpaceHigher N (m + 2) 2 Ω,
      SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set 𝔼)]
        fun x ↦ θ x * SobolevMultiIndex.fn u x := by
  have hloc := Elliptic.regularity_interior_higher m
    (SobolevMultiIndex.memSobolevMultiIndex u).memSobolevMultiIndexLoc
    (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
    (SobolevMultiIndex.memSobolevMultiIndex f).memSobolevMultiIndexLoc heq
  refine ⟨hloc, fun θ ↦ ?_⟩
  have h1 := (hloc.smul_testFunction one_le_two θ).mono_set (le_top : Ω ≤ ⊤)
  refine (h1.congr_ae ?_).exists_sobolevMultiIndex
  refine ae_restrict_of_forall_mem Ω.isOpen.measurableSet fun x hx ↦ ?_
  rw [Set.indicator_of_mem hx, smul_eq_mul]

/-- **Remark 25, "in particular, `f ∈ C^∞(Ω) ⇒ u ∈ C^∞(Ω)`"**: for `u ∈ H^1(Ω)` with
`∫_Ω ∇u · ∇φ = ∫_Ω f φ` for all `φ ∈ C_c^∞(Ω)` and `f` of class `C^∞` on `Ω`, `u` agrees almost
everywhere on `Ω` with a `C^∞` function on `Ω`. A `C^∞` function lies in `H^m_loc(Ω)` for every
`m` (`ContDiffOn.memSobolevMultiIndexLoc`), so `u ∈ H^{m+2}_loc(Ω)` for every `m` by
`Elliptic.regularity_interior_higher`, and `MemSobolevMultiIndexLoc.exists_contDiffOn` gives the
smooth representative. Footnote 33 — nothing can be said about `u` up to the boundary — is a
remark and not a node. -/
theorem remark_9_25_smooth (u : hSpace N Ω) {f : 𝔼 → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (heq : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), f x * φ x) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ ∞ ũ Ω ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ :=
  MemSobolevMultiIndexLoc.exists_contDiffOn fun m ↦
    (Elliptic.regularity_interior_higher m
      (SobolevMultiIndex.memSobolevMultiIndex u).memSobolevMultiIndexLoc
      (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
      (hf.memSobolevMultiIndexLoc (by simp)) heq).mono_order (Nat.le_add_right m 2)

/-- **Remark 25, hypoellipticity.** Let `f ∈ L²(Ω)` and let `u ∈ H^1_0(Ω)` be the weak solution
of `∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all `φ ∈ H^1_0(Ω)`, and fix an open `ω ⊆ Ω` (the book
takes `ω ⊂⊂ Ω`). The regularity of `u|_ω` depends only on the regularity of `f|_ω`: if
`f ∈ H^m(ω)` then `u ∈ H^{m+2}_loc(ω)`, and if `f` agrees almost everywhere on `ω` with a `C^∞`
function on `ω` then so does `u` — `f ∈ C^∞(ω) ⇒ u ∈ C^∞(ω)` even if `f` is very irregular
outside `ω`. Interior regularity on the open set `ω` with the datum `f − u`, whose regularity on
`ω` is that of `f` one step behind, bootstrapped
(`Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul`). The sentence before, that
`u|_ω`
depends on the values of `f` in all of `Ω`, is footnote 34's pointer to the strong maximum
principle and is not a node. -/
theorem remark_9_25_local {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : IsWeakSolutionDirichlet Ω f u) {Ω' : Opens 𝔼} (hω : Ω' ≤ Ω) :
    (∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω' volume →
      MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) (m + 2) 2 Ω' volume) ∧
    ∀ f₀ : 𝔼 → ℝ, ContDiffOn ℝ ∞ f₀ Ω' → (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω' : Set 𝔼)] f₀ →
      ∃ ũ : 𝔼 → ℝ, ContDiffOn ℝ ∞ ũ Ω' ∧
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω' : Set 𝔼)] ũ := by
  have hu' := (isWeakSolutionDirichlet_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  have hpred := Elliptic.forall_testFunction_of_forall_testFunctions
    (fun Φ hΦ ↦ hg Φ (SobolevMultiIndexZero.testFunctions_le hΦ))
  have hsub : ⇑(f - SobolevMultiIndex.weakDeriv u 0) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      fun x ↦ f x + (-1) * SobolevMultiIndex.fn u x := by
    filter_upwards [Lp.coeFn_sub f (SobolevMultiIndex.weakDeriv u 0)] with x hx
    rw [hx, Pi.sub_apply]
    change f x - SobolevMultiIndex.weakDeriv u 0 x = f x + -1 * SobolevMultiIndex.weakDeriv u 0 x
    ring
  have hpred' : ∀ φ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set 𝔼),
      ∑ i, partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in (Ω : Set 𝔼), (f x + (-1) * SobolevMultiIndex.fn u x) * φ x := fun φ ↦ by
    have hint : ∀ i, Integrable
        (fun x ↦ partialDeriv u i x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict (Ω : Set 𝔼)) := fun i ↦
      (Lp.memLp _).integrable_mul_two
        ((TestFunction.memLp (φ.fderivApply (EuclideanSpace.single i 1)) 2 volume).restrict _)
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    refine (hpred φ).trans (integral_congr_ae ?_)
    filter_upwards [hsub] with x hx
    rw [hx]
  have hpredω := Elliptic.forall_testFunction_of_le hω hpred'
  have huω : MemSobolevMultiIndexLoc 𝔟 (SobolevMultiIndex.fn u) 1 2 Ω' volume :=
    ((SobolevMultiIndex.memSobolevMultiIndex u).mono_set hω).memSobolevMultiIndexLoc
  have hwω : ∀ i, HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (SobolevMultiIndex.fn u)
      (partialDeriv u i) Ω' volume := fun i ↦
    (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i).mono hω
  refine ⟨fun m hf ↦ Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul m huω hwω
    hf.memSobolevMultiIndexLoc hpredω, fun f₀ hf₀ hff ↦ ?_⟩
  refine MemSobolevMultiIndexLoc.exists_contDiffOn fun m ↦ ?_
  have hfm : MemSobolevMultiIndexLoc 𝔟 (⇑f) m 2 Ω' volume :=
    (hf₀.memSobolevMultiIndexLoc (by simp)).congr_ae hff.symm
  exact (Elliptic.memSobolevMultiIndexLoc_of_forall_testFunction_add_mul m huω hwω hfm
    hpredω).mono_order (Nat.le_add_right m 2)

end Interior

section Regularity

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of `ℝ^N`, the basis of the backbone's multi-index Sobolev spaces. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

/-- The half space `ℝ^N_+ = {x ∈ ℝ^N : x_N > 0}`. -/
local notation "ℝ₊" => EuclideanSpace.upperHalfSpaceOpens d

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The book's `Ω` of class `C^{m+2}` is the backbone's chart condition at the order `m + 2`
of `WithTop ℕ∞`. -/
theorem IsOfClassC.isContDiffChartDomain_add_two {m : ℕ} (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼)) :
    IsContDiffChartDomain (m + 2) (Ω : Set 𝔼) := by
  have : (((m + 2 : ℕ∞)) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 2 := by push_cast; rfl
  rw [IsOfClassC, this] at hΩ
  exact hΩ

/-! ### Theorem 9.25 -/

/-- **Theorem 9.25 (regularity for the Dirichlet problem), the `H²` clause.** Let `Ω` be an
open set of class `C²` with `Γ` bounded. Let `f ∈ L²(Ω)` and let `u ∈ H^1_0(Ω)` satisfy
`∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all `φ ∈ H^1_0(Ω)` (48). Then `u ∈ H²(Ω)` and
`‖u‖_{H²} ≤ C ‖f‖_{L²}`, where `C` is a constant depending only on `Ω`: there is `C ≥ 0` such
that for every such `f` and `u`, `u` is the function of an element `U ∈ H²(Ω)`, and every such
`U` has `‖U‖_{H²} ≤ C ‖f‖_{L²}`. The backbone's `Elliptic.regularity_dirichlet` — the method of
translations in the cases A (`ℝ^N`), B (`ℝ^N_+`), C₁ (interior) and C₂ (near the boundary,
through the charts), with the constant from the closed graph theorem. The alternative
"or else `Ω = ℝ^N_+`" is `theorem_9_25_upperHalfSpace`. -/
theorem theorem_9_25 (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) (u : hSpace (d + 1) Ω),
      IsWeakSolutionDirichlet Ω f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := Elliptic.regularity_dirichlet hΩ hΓ
  refine ⟨C, hC0, fun f u hu ↦ ?_⟩
  obtain ⟨hmem, hbound⟩ := hC f u ((isWeakSolutionDirichlet_iff f u).1 hu)
  exact ⟨hmem.exists_sobolevMultiIndex, hbound⟩

/-- **Theorem 9.25, the alternative "or else `Ω = ℝ^N_+`"**, `H²` clause: on the half space,
the weak solution `u ∈ H^1_0(ℝ^N_+)` of (48) lies in `H²(ℝ^N_+)` with `‖u‖_{H²} ≤ C ‖f‖_{L²}`.
Case B of the book's proof (`Elliptic.regularity_upperHalfSpace`) for the equation
`∫ ∇u · ∇φ = ∫ (f − u) φ`, with the constant `3 C_N` from `‖u‖_{H¹} ≤ ‖f‖_{L²}` and
`‖f − u‖_{L²} ≤ 2 ‖f‖_{L²}`. -/
theorem theorem_9_25_upperHalfSpace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)))
      (u : hSpace (d + 1) ℝ₊), IsWeakSolutionDirichlet ℝ₊ f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  have hC0 : (0 : ℝ) ≤ Elliptic.regularityConst d 1 1 0 := by
    unfold Elliptic.regularityConst
    positivity
  refine ⟨3 * Elliptic.regularityConst d 1 1 0, by linarith, fun f u hu ↦ ?_⟩
  have hu' := (isWeakSolutionDirichlet_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨U, hU, hUn⟩ := Elliptic.regularity_upperHalfSpace ⟨hu'.1, hg⟩
  have hun : ‖u‖ ≤ ‖f‖ := Elliptic.norm_le_of_isGalerkinSolution_laplace _ hu'
  have hg' : ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ 2 * ‖f‖ := by
    calc ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ ‖f‖ + ‖SobolevMultiIndex.weakDeriv u 0‖ :=
          norm_sub_le _ _
      _ ≤ ‖f‖ + ‖u‖ := by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le u 0
      _ ≤ 2 * ‖f‖ := by linarith
  refine ⟨⟨U, hU⟩, fun U' hU' ↦ ?_⟩
  rw [SobolevMultiIndex.ext_of_fn_ae_eq (hU'.trans hU.symm)]
  calc ‖U‖ ≤ Elliptic.regularityConst d 1 1 0 * (‖u‖ + ‖f - SobolevMultiIndex.weakDeriv u 0‖) :=
        hUn
    _ ≤ Elliptic.regularityConst d 1 1 0 * (‖f‖ + 2 * ‖f‖) := by gcongr
    _ = 3 * Elliptic.regularityConst d 1 1 0 * ‖f‖ := by ring

/-- **Theorem 9.25, the `H^{m+2}` clause.** Furthermore, if `Ω` is of class `C^{m+2}` (with `Γ`
bounded) and `f ∈ H^m(Ω)`, then `u ∈ H^{m+2}(Ω)` and `‖u‖_{H^{m+2}} ≤ C ‖f‖_{H^m}`: for the weak
solution `u ∈ H^1_0(Ω)` of (48) with datum `f ∈ H^m(Ω)`, `u` is the function of an element
`U ∈ H^{m+2}(Ω)`, and every such `U` has `‖U‖_{H^{m+2}} ≤ C ‖f‖_{H^m}`, with `C` depending only
on `Ω` and `m`. The backbone's `Elliptic.regularity_dirichlet_higher`: the induction on `m` of
cases A, B and C, differentiating the equation (Lemma 9.7 and (58)) instead of the book's
order-`m` Leibniz rule, with the constant from the closed graph theorem. -/
theorem theorem_9_25_higher (m : ℕ) (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : sobolevSpaceHigher (d + 1) m 2 Ω) (u : hSpace (d + 1) Ω),
      IsWeakSolutionDirichlet Ω (SobolevMultiIndex.fnL ℝ 𝔟 m 2 Ω volume f) u →
        (∃ U : sobolevSpaceHigher (d + 1) (m + 2) 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) (m + 2) 2 Ω,
          SobolevMultiIndex.fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    Elliptic.regularity_dirichlet_higher m hΩ.isContDiffChartDomain_add_two hΓ
  refine ⟨C, hC0, fun f u hu ↦ ?_⟩
  obtain ⟨hmem, hbound⟩ := hC f u ((isWeakSolutionDirichlet_iff _ u).1 hu)
  exact ⟨hmem.exists_sobolevMultiIndex, hbound⟩

/-- **Theorem 9.25, "in particular, if `f ∈ H^m(Ω)` with `m > N/2`, then `u ∈ C²(Ω̄)`"**: for
`Ω` of class `C^{m+2}` with `Γ` bounded, `f ∈ H^m(Ω)` and `N/2 < m`, the weak solution
`u ∈ H^1_0(Ω)` of (48) agrees almost everywhere on `Ω` with a function `ũ` of class `C²(Ω̄)` in
the sense of footnote 16 of §9.3 (`ContDiffOnClosure ℝ 2 ũ Ω`, with `ũ` continuous on `Ω̄`). The
`H^{m+2}` clause and Corollary 9.15 (`Elliptic.regularity_dirichlet_contDiffOn`, whose
representative is continuous on `ℝ^N` with derivatives of order `≤ 2` extending continuously
from `Ω` to `ℝ^N`); "`m > N/2`" is the condition `2 + N/2 < m + 2` of Corollary 9.15. -/
theorem theorem_9_25_contDiffOn (m : ℕ) (hΩ : IsOfClassC (m + 2) (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hm : ((d + 1 : ℕ) : ℝ) / 2 < m)
    (f : sobolevSpaceHigher (d + 1) m 2 Ω) {u : hSpace (d + 1) Ω}
    (hu : IsWeakSolutionDirichlet Ω (SobolevMultiIndex.fnL ℝ 𝔟 m 2 Ω volume f) u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ 2 ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_contDiffOn m
    hΩ.isContDiffChartDomain_add_two hΓ hm (SobolevMultiIndex.memSobolevMultiIndex f)
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j hj ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j (by exact_mod_cast hj)
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-- **Theorem 9.25, "finally, if `Ω` is of class `C^∞` and `f ∈ C^∞(Ω̄)`, then
`u ∈ C^∞(Ω̄)`"**, for a bounded `Ω`: if `Ω` is bounded and of class `C^∞` (a `C^∞` chart at
every boundary point) and the datum `f ∈ L²(Ω)` agrees almost everywhere with a function of class
`C^∞(Ω̄)` (`ContDiffOnClosure ℝ ∞ · Ω`), then the weak solution `u ∈ H^1_0(Ω)` of (48) agrees
almost everywhere on `Ω` with a function `ũ` of class `C^∞(Ω̄)`, continuous on `Ω̄`. On the
bounded `Ω`, `f ∈ C^∞(Ω̄)` gives `f ∈ H^m(Ω)` for every `m`
(`ContDiffOnClosure.memSobolevMultiIndex_of_isBounded_of_le`), and the backbone's
`Elliptic.regularity_dirichlet_smooth` is the `C²(Ω̄)` clause at every order, with one
representative for all orders. For an unbounded `Ω` with bounded `Γ` the hypothesis
`f ∈ C^∞(Ω̄)` does not give `f ∈ H^m(Ω)`; that case is `theorem_9_25_smooth_of_forall_mem`. -/
theorem theorem_9_25_smooth (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼)) (hb : Bornology.IsBounded (Ω : Set 𝔼))
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {f₀ : 𝔼 → ℝ} (hf : ContDiffOnClosure ℝ ∞ f₀ Ω)
    (hff : (f : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] f₀) {u : hSpace (d + 1) Ω}
    (hu : IsWeakSolutionDirichlet Ω f u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)) :=
    hb.isCompact_closure.isBounded.subset frontier_subset_closure
  have hfm : ∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω volume := fun m ↦
    (hf.memSobolevMultiIndex_of_isBounded_of_le Ω hb 2 (by simp)).congr_ae hff.symm
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_smooth hΩ hΓ hfm
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-- **Theorem 9.25, the `C^∞(Ω̄)` clause for `Ω` of class `C^∞` with `Γ` bounded**, under the
hypothesis `f ∈ H^m(Ω)` for every `m` (which is what `f ∈ C^∞(Ω̄)` provides on a bounded `Ω`,
`theorem_9_25_smooth`, and what the book's clause uses): the weak solution `u ∈ H^1_0(Ω)` of (48)
agrees almost everywhere on `Ω` with a function of class `C^∞(Ω̄)`, continuous on `Ω̄`. The
backbone's `Elliptic.regularity_dirichlet_smooth`. -/
theorem theorem_9_25_smooth_of_forall_mem (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    (hf : ∀ m : ℕ, ∃ F : sobolevSpaceHigher (d + 1) m 2 Ω,
      SobolevMultiIndex.fn F =ᵐ[volume.restrict (Ω : Set 𝔼)] f)
    {u : hSpace (d + 1) Ω} (hu : IsWeakSolutionDirichlet Ω f u) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hfm : ∀ m : ℕ, MemSobolevMultiIndex 𝔟 (⇑f) m 2 Ω volume := fun m ↦
    (exists_fn_ae_eq_iff (m := m) (p := 2) (f : 𝔼 → ℝ)).1 (hf m)
  obtain ⟨ũ, hc, h2, hae, hG⟩ := Elliptic.regularity_dirichlet_smooth hΩ hΓ hfm
    ((isWeakSolutionDirichlet_iff _ u).1 hu)
  refine ⟨ũ, ⟨h2, fun j _ ↦ ?_⟩, hc.continuousOn, hae⟩
  obtain ⟨G, hGc, hGe⟩ := hG j
  exact ⟨G, hGc.continuousOn, hGe.symm⟩

/-! ### The lemmas of the proof: Lemmas 9.6, 9.7 (case B) and 9.8 (case C₂) -/

/-- **Lemma 9.6.** On `Ω = ℝ^N_+`, `‖D_h v‖_{L²(Ω)} ≤ ‖∇v‖_{L²(Ω)}` for all `v ∈ H^1(Ω)` and all
`h ∥ Γ` (`h_N = 0`), where `D_h v(x) = (v(x + h) − v(x))/|h|` is the difference quotient
`Elliptic.diffQuot h v` and `‖∇v‖_{L²}` is the `L²` norm of the gradient vector (§9.1). The
book's proof starts with `v ∈ C_c^1(ℝ^N)` as in Proposition 9.3 and argues by density; the
backbone's `Elliptic.eLpNorm_diffQuot_le_of_tangential` is Proposition 9.3 (i) ⇒ (iii) on the
translation-invariant half space, whose bound is the `ℓ²` gradient norm, equal at `p = 2` to the
Euclidean one (`gradNorm_eq_toReal_eLpNorm_gradient_two`). -/
theorem lemma_9_6 {h : 𝔼} (hh : h (Fin.last d) = 0) (v : hSpace (d + 1) ℝ₊) :
    eLpNorm (Elliptic.diffQuot h (SobolevMultiIndex.fn v)) 2
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼))
      ≤ eLpNorm (gradient v) 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) := by
  refine (Elliptic.eLpNorm_diffQuot_le_of_tangential hh v).trans ?_
  rw [gradNorm_eq_toReal_eLpNorm_gradient_two,
    ENNReal.ofReal_toReal (memLp_gradient v).eLpNorm_ne_top]

/-- **Lemma 9.7.** On `Ω = ℝ^N_+`, let `u ∈ H²(Ω) ∩ H^1_0(Ω)` satisfy (48) with `f ∈ H¹(Ω)`.
Then every tangential derivative `Du = ∂u/∂x_j`, `1 ≤ j ≤ N − 1`, belongs to `H^1_0(Ω)`, and
moreover `∫ ∇(Du) · ∇φ + ∫ (Du) φ = ∫ (Df) φ` for all `φ ∈ H^1_0(Ω)` (58): there is `w ∈ H^1(Ω)`,
the weak derivative of `u` along `e_j`, which is a weak solution of (48) with the datum
`∂_j f` (`IsWeakSolutionDirichlet`, whose first clause is `w ∈ H^1_0(Ω)`). The membership is the
"delicate point" of the book's proof, `Elliptic.tangentialDeriv_mem_zero_of_isGalerkinSolution`
(weak compactness of the tangential difference quotients in `H^1_0(Ω)`); (58) "is derived from
(48) by choosing `Dφ` instead of `φ` (with `φ ∈ C_c^∞(Ω)`) and then arguing by density"
(`Elliptic.forall_testFunction_deriv`, `Elliptic.apply_eq_zero_of_forall_testFunctions`). -/
theorem lemma_9_7 {f u : hSpace (d + 1) ℝ₊}
    (hu2 : ∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊,
      SobolevMultiIndex.fn U =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u)
    (hu : IsWeakSolutionDirichlet ℝ₊ (SobolevMultiIndex.fnL ℝ 𝔟 1 2 ℝ₊ volume f) u)
    {j : Fin (d + 1)} (hj : j ≠ Fin.last d) :
    ∃ w : hSpace (d + 1) ℝ₊,
      HasWeakIteratedLineDerivOn ![EuclideanSpace.single j 1] (SobolevMultiIndex.fn u)
        (SobolevMultiIndex.fn w) ℝ₊ volume ∧
      IsWeakSolutionDirichlet ℝ₊ (partialDeriv f j) w := by
  have hΩm : MeasurableSet ((ℝ₊ : Opens 𝔼) : Set 𝔼) := (ℝ₊ : Opens 𝔼).isOpen.measurableSet
  obtain ⟨U, hU⟩ := hu2
  have hu' := (isWeakSolutionDirichlet_iff _ u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨w, hw0, hwd⟩ := Elliptic.tangentialDeriv_mem_zero_of_isGalerkinSolution ⟨hu'.1, hg⟩ hj
  have hwfn : SobolevMultiIndex.fn w =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
      SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) :=
    (ae_restrict_iff' hΩm).2
      (hwd.ae_eq (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u j))
  -- the first derivatives of `u` as `H¹` elements
  have hV : ∀ k, ∃ V : hSpace (d + 1) ℝ₊, SobolevMultiIndex.fn V
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.weakDeriv u
        (MultiIndexLE.single k) := fun k ↦
    Elliptic.exists_sobolevEuclidean_one_fn_ae_eq_weakDeriv hU k
  choose V hV using hV
  -- the predicate form of the equation, with the datum `f - u`
  have hpred := Elliptic.forall_testFunction_of_forall_testFunctions
    (fun Φ hΦ ↦ hg Φ (SobolevMultiIndexZero.testFunctions_le hΦ))
  have hsub : ⇑(SobolevMultiIndex.fnL ℝ 𝔟 1 2 ℝ₊ volume f - SobolevMultiIndex.weakDeriv u 0)
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
        fun x ↦ SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x :=
    Lp.coeFn_sub _ _
  have hpred' : ∀ φ : 𝓓(ℝ₊, ℝ), ∑ i, ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
      SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) x
        * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        (SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x) * φ x := fun φ ↦ by
    rw [hpred φ]
    refine integral_congr_ae ?_
    filter_upwards [hsub] with x hx
    rw [hx]
  -- the derivatives of the datum along `e_k`
  have hgj : ∀ k, HasWeakIteratedLineDerivOn ![EuclideanSpace.single k 1]
      (fun x ↦ SobolevMultiIndex.fn f x - SobolevMultiIndex.fn u x)
      (fun x ↦ partialDeriv f k x - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single k) x)
      ℝ₊ volume := fun k ↦
    (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single f k).sub
      (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u k)
  -- the differentiated equation against the test functions
  have hderiv := Elliptic.forall_testFunction_deriv
    (w := fun i ↦ ⇑(SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)))
    (v := fun i k ↦ ⇑(SobolevMultiIndex.weakDeriv (V k) (MultiIndexLE.single i)))
    (fun i ↦ Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single u i)
    (fun i k ↦ (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single (V k) i).congr_ae (hV k)
      (EventuallyEq.refl _ _))
    hgj hpred' j
  -- `∂_i (V j) = ∂_i w` almost everywhere
  have hvw : ∀ i, ⇑(SobolevMultiIndex.weakDeriv (V j) (MultiIndexLE.single i))
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)]
        SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) := fun i ↦ by
    have h1 := (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single (V j) i).congr_ae (hV j)
      (EventuallyEq.refl _ _)
    have h2 := (Elliptic.weakDeriv_hasWeakIteratedLineDerivOn_single w i).congr_ae hwfn
      (EventuallyEq.refl _ _)
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq h2)
  -- the typed equation for `w` on the test-function elements
  have hweq : ∀ Φ ∈ SobolevMultiIndex.testFunctions ℝ 𝔟 1 2 ℝ₊ volume,
      Elliptic.laplaceForm ℝ₊ w Φ = Elliptic.load ℝ₊ (partialDeriv f j) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [Elliptic.laplaceForm_apply_eq_dirichletForm_add_weakDeriv,
      Elliptic.dirichletForm_apply_eq_of_ae_eq (fun i ↦ EventuallyEq.refl _ _) hψ,
      Elliptic.load_apply_eq_of_ae_eq (EventuallyEq.refl _ _) hψ, L2.inner_eq_integral_mul]
    have e1 : ∑ i, ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        SobolevMultiIndex.weakDeriv w (MultiIndexLE.single i) x
          * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
          (partialDeriv f j x - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x) * ψ x := by
      rw [← hderiv ψ]
      refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ?_
      filter_upwards [hvw i] with x hx
      rw [hx]
    have e2 : ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
        SobolevMultiIndex.weakDeriv w 0 x * SobolevMultiIndex.weakDeriv Φ 0 x
        = ∫ x in ((ℝ₊ : Opens 𝔼) : Set 𝔼),
          SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x * ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [hwfn, hψ] with x hx hx'
      change SobolevMultiIndex.fn w x * SobolevMultiIndex.fn Φ x = _
      rw [hx, hx']
    have hψ2 : MemLp ψ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      (TestFunction.memLp ψ 2 volume).restrict _
    have hi1 : Integrable (fun x ↦ (partialDeriv f j x
        - SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x) * ψ x)
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      ((Lp.memLp (partialDeriv f j)).sub (Lp.memLp _)).integrable_mul_two hψ2
    have hi2 : Integrable (fun x ↦ SobolevMultiIndex.weakDeriv u (MultiIndexLE.single j) x * ψ x)
        (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)) :=
      (Lp.memLp _).integrable_mul_two hψ2
    rw [e1, e2, ← integral_add hi1 hi2]
    congr 1
    funext x
    ring
  refine ⟨w, hwd, (isWeakSolutionDirichlet_iff _ w).2 ⟨hw0, fun Φ hΦ ↦ ?_⟩⟩
  have := Elliptic.apply_eq_zero_of_forall_testFunctions
    (L := Elliptic.laplaceForm ℝ₊ w - Elliptic.load ℝ₊ (partialDeriv f j))
    (fun Ψ hΨ ↦ by rw [sub_apply, hweq Ψ hΨ, sub_self]) hΦ
  rwa [sub_apply, sub_eq_zero] at this

/-- **Lemma 9.8.** With the notation of case C₂ — a `C²` chart `H : Q → U`, `J = H⁻¹`
(`c : ContDiffChart 2 Ω`), the open sets `Ω ∩ U` (`Ω₁`) and `Q₊` (`Qp`, whose carrier is
`unitChartCubePos d`), and `v ∈ H^1_0(Ω ∩ U)` a weak solution of `−Δv = g` on `Ω ∩ U`,
`∫_{Ω ∩ U} ∇v · ∇φ = ∫_{Ω ∩ U} g φ` for all `φ ∈ H^1_0(Ω ∩ U)` (59) — the function
`w(y) = v(H(y))` belongs to `H^1_0(Q₊)` and satisfies
`∑_{k,ℓ} ∫_{Q₊} a_{kℓ} ∂_k w ∂_ℓ ψ = ∫_{Q₊} g̃ ψ` for all `ψ ∈ H^1_0(Q₊)` (60), where
`g̃ = (g ∘ H) |det Jac H| ∈ L²(Q₊)` (`Elliptic.chartDatum H g`) and the functions
`a_{kℓ} = ∑_j ∂_j J_k ∂_j J_ℓ |det Jac H|` (`Elliptic.chartCoeff H J k ℓ`) are of class `C¹` on
the cylinder `Q ⊇ Q₊` and satisfy the ellipticity condition (36) on `Q₊`. The backbone's
`Elliptic.transfer_chart_ae_eq` (the change of variables of Proposition 9.6 and Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`), with
`Elliptic.contDiffOn_chartCoeff` and `Elliptic.chartCoeff_elliptic` for the coefficients. -/
theorem lemma_9_8 (c : ContDiffChart 2 (Ω : Set 𝔼)) {Ω₁ Qp : Opens 𝔼}
    (hΩ₁ : (Ω₁ : Set 𝔼) = c.U ∩ Ω) (hQp : (Qp : Set 𝔼) = unitChartCubePos d)
    {v : hSpace (d + 1) Ω₁} (hv : v ∈ hZeroSpace (d + 1) Ω₁)
    {g : Lp ℝ 2 (volume.restrict (Ω₁ : Set 𝔼))}
    (heq : ∀ φ ∈ hZeroSpace (d + 1) Ω₁,
      ∫ x in (Ω₁ : Set 𝔼), ∑ i, partialDeriv v i x * partialDeriv φ i x
        = ∫ x in (Ω₁ : Set 𝔼), g x * SobolevMultiIndex.fn φ x) :
    ∃ w : hSpace (d + 1) Qp, w ∈ hZeroSpace (d + 1) Qp ∧
      (SobolevMultiIndex.fn w =ᵐ[volume.restrict (Qp : Set 𝔼)]
        fun y ↦ SobolevMultiIndex.fn v (c.toFun y)) ∧
      MemLp (Elliptic.chartDatum c.toFun g) 2 (volume.restrict (Qp : Set 𝔼)) ∧
      (∀ k l, ContDiffOn ℝ 1 (Elliptic.chartCoeff c.toFun c.invFun k l) (unitChartCube d)) ∧
      (∃ α, ellipticityCondition Qp (Elliptic.chartCoeff c.toFun c.invFun) α) ∧
      ∀ ψ ∈ hZeroSpace (d + 1) Qp,
        ∑ k, ∑ l, ∫ y in (Qp : Set 𝔼), Elliptic.chartCoeff c.toFun c.invFun k l y
          * partialDeriv w k y * partialDeriv ψ l y
          = ∫ y in (Qp : Set 𝔼), Elliptic.chartDatum c.toFun g y * SobolevMultiIndex.fn ψ y := by
  -- the chart as a diffeomorphism `Q₊ → Ω ∩ U`, and as a diffeomorphism `Q → U`
  obtain ⟨M, h⟩ := c.isDiffeoOnWithBoundedJacobian_pos (by norm_num) Ω.isOpen
  have h' : IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (Qp : Set 𝔼) (Ω₁ : Set 𝔼) M := by
    rw [hQp, hΩ₁]; exact h
  obtain ⟨M', hfull⟩ := c.isDiffeoOnWithBoundedJacobian (by norm_num)
  -- the typed equation (59)
  have heq' : ∀ Ψ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω₁,
      Elliptic.dirichletForm Ω₁ v Ψ = Elliptic.load Ω₁ g Ψ := fun Ψ hΨ ↦ by
    rw [Elliptic.dirichletForm_apply, Elliptic.load_apply]
    exact heq Ψ hΨ
  obtain ⟨w, A, G', hw0, hwfn, hAa, hG', hweq⟩ := Elliptic.transfer_chart_ae_eq h' hv heq'
  refine ⟨w, hw0, hwfn, Elliptic.memLp_chartDatum h' g, fun k l ↦ ?_, ?_, fun ψ hψ ↦ ?_⟩
  · exact Elliptic.contDiffOn_chartCoeff isOpen_unitChartCube c.isOpen_U
      (c.contDiffOn.mono subset_closure) (c.contDiffOn_invFun.mono subset_closure)
      c.bijOn.mapsTo (fun y hy ↦ hfull.det_fderiv_ne_zero hy) k l
  · obtain ⟨α, hα, hell⟩ := Elliptic.chartCoeff_elliptic h'
    exact ⟨α, hα, hell⟩
  · have e := hweq ψ hψ
    rw [Elliptic.generalForm_zero_zero_apply, Elliptic.load_apply] at e
    have e2 : ∫ y in (Qp : Set 𝔼), G' y * SobolevMultiIndex.fn ψ y
        = ∫ y in (Qp : Set 𝔼), Elliptic.chartDatum c.toFun g y * SobolevMultiIndex.fn ψ y :=
      integral_congr_ae (hG'.mono fun y hy ↦ by dsimp only; rw [hy])
    rw [e2] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Elliptic.inner_mulL_eq_integral]
    refine integral_congr_ae ((hAa k l).mono fun y hy ↦ ?_)
    dsimp only
    rw [hy]
    rfl

/-! ### Theorem 9.26: the half space, and the Neumann boundary condition -/

/-- **Theorem 9.26 (regularity for the Neumann problem), the alternative "or else
`Ω = ℝ^N_+`"**, `H²` clause: on the half space, the weak solution `u ∈ H^1(ℝ^N_+)` of
`∫ ∇u · ∇φ + ∫ u φ = ∫ f φ` for all `φ ∈ H^1(ℝ^N_+)` (49) lies in `H²(ℝ^N_+)` with
`‖u‖_{H²} ≤ C ‖f‖_{L²}`. Case B of the book's proof, whose method of translations asks of the
test space only that it contain the test functions and be invariant under the tangential
translations — both trivial for `H^1(ℝ^N_+)`, so that the book's delicate point (Lemma 9.7)
does not arise: `Elliptic.regularity_neumann_upperHalfSpace` is the Dirichlet case B with the
test space `⊤`, and the constant is the same `3 C_N` as in `theorem_9_25_upperHalfSpace` (from
`‖u‖_{H¹} ≤ ‖f‖_{L²}` and `‖f − u‖_{L²} ≤ 2 ‖f‖_{L²}`). On a general `C²` domain with `Γ`
bounded the theorem is not formalized; see `## Not formalized here` in the module
documentation. -/
theorem theorem_9_26_upperHalfSpace :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)))
      (u : hSpace (d + 1) ℝ₊), IsWeakSolutionNeumann ℝ₊ f u →
        (∃ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u) ∧
        ∀ U : sobolevSpaceHigher (d + 1) 2 2 ℝ₊, SobolevMultiIndex.fn U
          =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u →
            ‖U‖ ≤ C * ‖f‖ := by
  have hC0 : (0 : ℝ) ≤ Elliptic.regularityConst d 1 1 0 := by
    unfold Elliptic.regularityConst
    positivity
  refine ⟨3 * Elliptic.regularityConst d 1 1 0, by linarith, fun f u hu ↦ ?_⟩
  have hu' := (isWeakSolutionNeumann_iff f u).1 hu
  have hg := Elliptic.dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hu'
  obtain ⟨U, hU, hUn⟩ := Elliptic.regularity_neumann_upperHalfSpace ⟨hu'.1, hg⟩
  have hun : ‖u‖ ≤ ‖f‖ := Elliptic.norm_le_of_isGalerkinSolution_laplace _ hu'
  have hg' : ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ 2 * ‖f‖ := by
    calc ‖f - SobolevMultiIndex.weakDeriv u 0‖ ≤ ‖f‖ + ‖SobolevMultiIndex.weakDeriv u 0‖ :=
          norm_sub_le _ _
      _ ≤ ‖f‖ + ‖u‖ := by gcongr; exact SobolevMultiIndex.norm_weakDeriv_le u 0
      _ ≤ 2 * ‖f‖ := by linarith
  refine ⟨⟨U, hU⟩, fun U' hU' ↦ ?_⟩
  rw [SobolevMultiIndex.ext_of_fn_ae_eq (hU'.trans hU.symm)]
  calc ‖U‖ ≤ Elliptic.regularityConst d 1 1 0 * (‖u‖ + ‖f - SobolevMultiIndex.weakDeriv u 0‖) :=
        hUn
    _ ≤ Elliptic.regularityConst d 1 1 0 * (‖f‖ + 2 * ‖f‖) := by gcongr
    _ = 3 * Elliptic.regularityConst d 1 1 0 * ‖f‖ := by ring

/-- **Theorem 9.26, the alternative "or else `Ω = ℝ^N_+`"**, `H^{m+2}` clause: on the half
space, if `f ∈ H^m(ℝ^N_+)` then the weak solution `u ∈ H^1(ℝ^N_+)` of (49) lies in
`H^{m+2}(ℝ^N_+)`. Case B of the book's proof at every order
(`Elliptic.regularity_neumann_upperHalfSpace_higher_mem_laplace`): the tangential derivatives of
a Neumann solution are Neumann solutions with the differentiated data — the Neumann analogue of
Lemma 9.7, proved here by a tangential integration by parts against the test functions of `ℝ^N`
rather than by the book's weak compactness — and the normal-normal derivative is read off the
equation. The book's norm bound `‖u‖_{H^{m+2}} ≤ C ‖f‖_{H^m}` is not stated: the closed-graph
argument of `theorem_9_25_higher` needs a solution map for the Neumann problem, and the
backbone's `Elliptic.solutionMap` is built for the test space `H^1_0(Ω)` only. -/
theorem theorem_9_26_upperHalfSpace_higher (m : ℕ) (f : sobolevSpaceHigher (d + 1) m 2 ℝ₊)
    {u : hSpace (d + 1) ℝ₊}
    (hu : IsWeakSolutionNeumann ℝ₊ (SobolevMultiIndex.fnL ℝ 𝔟 m 2 ℝ₊ volume f) u) :
    ∃ U : sobolevSpaceHigher (d + 1) (m + 2) 2 ℝ₊, SobolevMultiIndex.fn U
      =ᵐ[volume.restrict ((ℝ₊ : Opens 𝔼) : Set 𝔼)] SobolevMultiIndex.fn u := by
  refine (Elliptic.regularity_neumann_upperHalfSpace_higher_mem_laplace m ?_
    ((isWeakSolutionNeumann_iff _ u).1 hu)).exists_sobolevMultiIndex
  rw [SobolevMultiIndex.fnL_apply]
  exact SobolevMultiIndex.memSobolevMultiIndex f

/-- **Theorem 9.26, the boundary condition.** On a bounded `C¹` domain (`hΩ : IsContDiffDomain 1 Ω`,
`hb`; the `C²` hypothesis of Theorem 9.26 is needed only for the `H²` regularity, which is here a
hypothesis), if `U₂ ∈ H²(Ω)` is such that its `H¹` shadow `toLowerOrderL U₂` is a weak solution of
the Neumann problem (49), then its normal derivative in the trace sense vanishes:
`∂U₂/∂n = ∑ᵢ nᵢ γ(∂ᵢU₂) = 0` `σ`-a.e. on `Γ`, with `γ` the trace `IsContDiffDomain.traceL`,
`σ = hΩ.boundaryMeasure hb` and `n = hΩ.outwardNormal hb` (`BoundaryData.TraceFamily.normalTrace`,
the `∂u/∂n` of the Comments on chapter 9, 7 (iii)). This is the sense in which the Neumann
condition `∂u/∂n = 0` on `Γ` of (44) holds for the `H²` solution of Theorem 9.26; together with
the `H²` regularity — which is `theorem_9_26_upperHalfSpace` on the half space and is not
formalized on a general `C²` domain, the book giving no proof — it is the full Theorem 9.26. The
backbone's `BoundaryData.TraceFamily.normalTrace_eq_zero_of_forall_laplaceForm_eq` through
`isWeakSolutionNeumann_iff`. -/
theorem theorem_9_26_normalDeriv (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼))
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    (U₂ : SobolevEuclidean (d + 1) 2 2 Ω)
    (hU : IsWeakSolutionNeumann Ω f
      (SobolevMultiIndex.toLowerOrderL ℝ 𝔟 2 Ω volume (by norm_num) U₂)) :
    (hΩ.traceFamily hb).normalTrace U₂ =ᵐ[hΩ.boundaryMeasure hb] 0 :=
  (hΩ.traceFamily hb).normalTrace_eq_zero_of_forall_laplaceForm_eq U₂ f fun φ ↦
    ((isWeakSolutionNeumann_iff f _).1 hU).2 φ Submodule.mem_top

end Regularity

end Brezis.Chapter09
