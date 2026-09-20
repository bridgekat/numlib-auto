import Numlib.Analysis.PDE.Bochner.SpaceTime
import Numlib.Analysis.PDE.Heat
import Numlib.Analysis.PDE.Heat.Classical
import NumlibSurface.Brezis.Chapter07.Section04
import NumlibSurface.Brezis.Chapter09.Section08

/-!
# Brezis §10.1: The heat equation — existence, uniqueness, and regularity

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §10.1: the heat equation `∂ₜu − Δu = 0` in
`Q = Ω × (0, ∞)`, `u = 0` on `Σ = Γ × (0, ∞)`, `u(·, 0) = u₀`, solved by the Hille–Yosida theory of
chapter 7 in `H = L²(Ω)` — Theorem 10.1 (existence, uniqueness, the smoothing (5), the energy
identity (6)), the display (7) for `D(A^ℓ)`, Theorem 10.2 (regularity up to `t = 0` for data in
`H¹₀`, `H² ∩ H¹₀`, and for data satisfying the compatibility conditions (8)) and Remarks 1, 3, 4.
The backbone is `Numlib/Analysis/PDE/DirichletLaplacian` (the operator `A`),
`Numlib/Analysis/PDE/Heat` (§10.1 in Bochner form), `Numlib/Analysis/PDE/Bochner/SpaceTime` (the
space–time bridge behind (5)) and `Numlib/Analysis/PDE/Heat/Classical` (Remark 4).

## Conventions

* The book reads `u(x, t)` as a function of `t` with values in a space of functions of `x`:
  "when we write `u(t)`, we mean the element `x ↦ u(x, t)` of `H`". A solution is therefore a
  curve `u : ℝ → L²(Ω)`, `L²(Ω) = Lp ℝ 2 (volume.restrict Ω)`; the classes `C^k(I; V)` for
  `V = H²(Ω)`, `H¹₀(Ω)` are the backbone's `Bochner.ContDiffOnThrough J k u I` (a `C^k` lift of
  `u` through the inclusion `J : V → L²(Ω)`), `L²(I; V)` is `Bochner.MemLpThrough J 2 u I`, and
  `C^∞(Ω̄ × [ε, ∞))` is `ContDiffOnClosure ℝ ∞ U (Ω ×ˢ Ioi ε)` for a function `U` of `(x, t)`
  representing the curve — footnote 16 of chapter 9's sense of `C^k` up to the boundary.
* The book's operator `A`, `D(A) = H²(Ω) ∩ H¹₀(Ω)`, `Au = −Δu`, is `heatOperator Ω`: the
  backbone's Dirichlet Laplacian `dirichletLaplacian Ω` (weak domain `{u ∈ H¹₀ : Δu ∈ L²}`)
  restricted to the functions of `H²(Ω)` elements. On a domain of class `C²` with bounded boundary
  the two operators coincide (`heatOperator_eq_dirichletLaplacian`, Theorem 9.25), which is how
  every backbone statement about `dirichletLaplacian` is read for the book's `A`.
* `H^k(Ω) = sobolevSpaceHigher N k 2 Ω`, `H¹(Ω) = hSpace N Ω`, `H¹₀(Ω) = hZeroSpace N Ω` (§9.1,
  §9.4); an `L²(Ω)` function "lies in `H^k(Ω)`" when it is the function `fnL w` of some
  `w ∈ H^k(Ω)`, and "`u₀ ∈ H¹₀(Ω)`" is the datum `fnL v₀` of some `v₀ ∈ H¹₀(Ω)`. Footnote 3's
  `|∇u(t)|²_{L²} = ∑ᵢ ∫_Ω |∂ᵢu(x, t)|²` is written for the `H¹₀`-lift of `u(t)` with the weak
  partial derivatives `partialDeriv` of §9.1 (`sum_integral_partialDeriv_sq`).
* The standing hypothesis of the chapter, "`Ω` of class `C^∞` with `Γ` bounded", is
  `Brezis.Chapter09.IsOfClassC ⊤ Ω` and `Bornology.IsBounded (frontier Ω)`, with `N = d + 1`
  (the chart definition of §9.2 needs a boundary variable). It is carried by the theorems whose
  proofs use it (the identification `D(A) = H² ∩ H¹₀` and its iterates, hence the class (4), the
  smoothing (5) and Theorem 10.2 (b), (c)); the statements whose proofs hold on every open set
  (the operator's monotonicity and symmetry, the energy identities (6) and (11), Theorem 10.2 (a),
  Remark 3) are stated without it, as the book itself notes ("this assumption may be
  considerably weakened if we are interested only in weak solutions").
* Errata (recorded in `notes/book-errata.md`): the clauses `u ∈ L²(0, ∞; H¹₀(Ω))` of Theorem
  10.1 and `u ∈ L²(0, ∞; H²(Ω))`, `L²(0, ∞; H³(Ω))` of Theorem 10.2 are false on unbounded `Ω`
  (`Ω = ℝ` with a Gaussian datum); what the proofs show on every open set is the finiteness of
  the gradient integral, `∫₀^∞ |∇u(t)|² dt ≤ ½ |u₀|²` (`theorem_10_1_memLp_gradient`), and the
  Bochner memberships hold for **bounded** `Ω` (`theorem_10_1_memLp`, `theorem_10_2_a_memLp`,
  `theorem_10_2_b_memLp`). The `C^∞` conclusion (5) is `u ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0`, as
  the book states it — not `C^∞(Ω̄ × [0, ∞))`, which is false for `L²` data. Remark 4 is stated
  for `u` smooth on `ℝ^N × ℝ`, where its statement is meaningful as written.

## Main results

* `heatOperator`, `heatOperator_mem_domain_iff`, `heatOperator_apply`, `heatOperator_isMonotone`,
  `heatOperator_isSymmetric`, `heatOperator_eq_dirichletLaplacian`,
  `heatOperator_isMaximalMonotone`, `heatOperator_isSelfAdjoint` — the operator and the claims
  (i)–(iii) of the proof of Theorem 10.1.
* `IsHeatSolution`, `IsHeatSolution.isSolution`, `isHeatSolution_iff` — the problem (1)–(3) in
  the class (4), and its identification with the backbone's `Heat.IsSolution`.
* `theorem_10_1`, `theorem_10_1_smooth`, `theorem_10_1_energy`, `theorem_10_1_memLp_gradient`,
  `theorem_10_1_memLp`, `equation_10_7`.
* `theorem_10_2_a`, `theorem_10_2_a_memLp`, `theorem_10_2_b`, `theorem_10_2_b_memLp`,
  `theorem_10_2_c`.
* `IsBackwardHeatSolution`, `remark_10_1`, `remark_10_1_necessary`, `remark_10_3`, `remark_10_4`.

Two lemmas written here belong in the backbone and are marked for relocation:
`contDiffOnThrough_infty_of_forall` (`Numlib/Analysis/PDE/Bochner`) and
`exists_contDiffOnClosure_infty_of_forall_memSobolevMultiIndex`
(`Numlib/Analysis/PDE/Elliptic/Regularity`, beside `Elliptic.regularity_dirichlet_smooth`, whose
proof it repeats).
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal InnerProductSpace

namespace Brezis.Chapter10

open Brezis.Chapter07 Brezis.Chapter09 SobolevMultiIndex

/-! ### Two lemmas for the backbone -/

/-- **A curve of class `C^n(s; V)` for every finite `n` is of class `C^∞(s; V)`** when the
inclusion `J` is injective: the lifts of the different orders agree on `s`, so the lift of order
`0` is of every class. (Belongs beside `Bochner.ContDiffOnThrough.of_le` in
`Numlib/Analysis/PDE/Bochner`.) -/
theorem contDiffOnThrough_infty_of_forall {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {J : V →L[ℝ] W} (hJ : Function.Injective J)
    {u : ℝ → W} {s : Set ℝ} (h : ∀ n : ℕ, Bochner.ContDiffOnThrough J n u s) :
    Bochner.ContDiffOnThrough J ∞ u s := by
  obtain ⟨v, -, hv⟩ := h 0
  refine ⟨v, contDiffOn_infty.2 fun n ↦ ?_, hv⟩
  obtain ⟨w, hw, hwu⟩ := h n
  exact hw.congr fun t ht ↦ hJ ((hv t ht).symm.trans (hwu t ht))

section Smooth

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of `ℝ^N`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A function in `H^m(Ω)` for every `m` is `C^∞(Ω̄)`** on a `C¹` domain with bounded
boundary: it agrees almost everywhere on `Ω` with a function of class `C^∞(Ω̄)` in the sense of
footnote 16 of §9.3 (`ContDiffOnClosure`), continuous on `Ω̄`. Corollary 9.15 at every order
(`Elliptic.exists_contDiffOn_of_memSobolevMultiIndex`) gives a `C^k(Ω̄)` representative for each
`k`; two continuous representatives agree on the open set `Ω`, so the representative of order `0`
is of every class, with the derivative extensions of the representative of order `k`. (The
gluing argument of `Elliptic.regularity_dirichlet_smooth`, which belongs beside it in
`Numlib/Analysis/PDE/Elliptic/Regularity`.) -/
theorem exists_contDiffOnClosure_infty_of_forall_memSobolevMultiIndex
    (hΩ : IsContDiffChartDomain 1 (Ω : Set 𝔼)) (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    {f : 𝔼 → ℝ} (hf : ∀ m : ℕ, MemSobolevMultiIndex 𝔟 f m 2 Ω volume) :
    ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
      f =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hrep : ∀ k : ℕ, ∃ ũ : 𝔼 → ℝ, Continuous ũ ∧ ContDiffOn ℝ k ũ Ω ∧
      f =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ ∧ ∀ j ≤ k, ∃ G : 𝔼 → (𝔼 [×j]→L[ℝ] ℝ),
        Continuous G ∧ EqOn (iteratedFDeriv ℝ j ũ) G Ω := fun k ↦ by
    refine Elliptic.exists_contDiffOn_of_memSobolevMultiIndex k hΩ hΓ (m := k + (d + 1)) ?_
      (hf _)
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  choose v hvc hvk hvae hvG using hrep
  have hagree : ∀ k, EqOn (v 0) (v k) Ω := fun k ↦
    Measure.eqOn_open_of_ae_eq ((hvae 0).symm.trans (hvae k)) Ω.isOpen
      (hvc 0).continuousOn (hvc k).continuousOn
  refine ⟨v 0, ⟨?_, fun j _ ↦ ?_⟩, (hvc 0).continuousOn, hvae 0⟩
  · rw [contDiffOn_infty]
    intro k
    exact (hvk k).congr fun x hx ↦ hagree k hx
  · obtain ⟨G, hGc, hGeq⟩ := hvG j j le_rfl
    refine ⟨G, hGc.continuousOn, fun x hx ↦ ?_⟩
    rw [← hGeq hx]
    have h : v j =ᶠ[𝓝 x] v 0 :=
      Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy ↦ (hagree j hy).symm
    exact (h.iteratedFDeriv ℝ j).eq_of_nhds

end Smooth

section General

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- The standard basis of `ℝ^N`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin N) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The operator `A` of the proof of Theorem 10.1 -/

variable (Ω) in
/-- **The operator `A` of the proof of Theorem 10.1**: the unbounded operator
`A : D(A) ⊂ L²(Ω) → L²(Ω)` with `D(A) = H²(Ω) ∩ H¹₀(Ω)` and `Au = −Δu`, "the boundary condition
(2) being incorporated in the definition of the domain". It is the backbone's Dirichlet Laplacian
`dirichletLaplacian Ω` (whose domain is the weak one, `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}`) restricted to
the submodule of `L²(Ω)` functions of `H²(Ω)` elements, `LinearPMap.domRestrict`; the weak domain
contains `H²(Ω) ∩ H¹₀(Ω)` on every open set (`mem_dirichletLaplacianDomain_of_sobolev_two`), so
the domain is `H²(Ω) ∩ H¹₀(Ω)` (`heatOperator_mem_domain_iff`) and `A u = −∑ᵢ ∂ᵢᵢu`
(`heatOperator_apply`). -/
noncomputable def heatOperator :
    Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) →ₗ.[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) :=
  (dirichletLaplacian Ω).domRestrict (LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap)

/-- `D(A)` is contained in the weak domain of the Dirichlet Laplacian. -/
theorem heatOperator_domain_le : (heatOperator Ω).domain ≤ (dirichletLaplacian Ω).domain :=
  inf_le_right

/-- **`D(A) = H²(Ω) ∩ H¹₀(Ω)`**: `f ∈ D(A)` iff `f` is the function of an element of `H²(Ω)` and
of an element of `H¹₀(Ω)`. -/
theorem heatOperator_mem_domain_iff {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} :
    f ∈ (heatOperator Ω).domain ↔
      (∃ w : sobolevSpaceHigher N 2 2 Ω, fnL ℝ 𝔟 2 2 Ω volume w = f) ∧
        ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = f := by
  change f ∈ LinearMap.range (fnL ℝ 𝔟 2 2 Ω volume).toLinearMap ⊓ dirichletLaplacianDomain Ω ↔ _
  rw [Submodule.mem_inf, LinearMap.mem_range]
  exact ⟨fun ⟨hw, hf⟩ ↦ ⟨hw, dirichletLaplacian_exists_lift ⟨f, hf⟩⟩,
    fun ⟨hw, hv⟩ ↦ ⟨hw, mem_dirichletLaplacianDomain_of_exists_sobolev_two hw hv⟩⟩

/-- `A f` is the value of the Dirichlet Laplacian at `f`, for `f ∈ D(A)`. -/
theorem heatOperator_apply_eq (f : (heatOperator Ω).domain) :
    heatOperator Ω f = dirichletLaplacian Ω ⟨f, heatOperator_domain_le f.2⟩ :=
  LinearPMap.domRestrict_apply rfl

/-- **`A u = −Δu`**: for `f ∈ D(A)` the function of `w ∈ H²(Ω)`, `A f = −∑ᵢ ∂²w/∂xᵢ²`, the weak
second derivatives of `w` at the multi-indices `2eᵢ`. -/
theorem heatOperator_apply (f : (heatOperator Ω).domain) (w : sobolevSpaceHigher N 2 2 Ω)
    (hw : fnL ℝ 𝔟 2 2 Ω volume w = f) :
    heatOperator Ω f = -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  rw [heatOperator_apply_eq, ← sobolevLaplacianL_apply]
  exact dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w _ hw

/-- **(i) `A` is monotone** (proof of Theorem 10.1): `(Au, u)_{L²} = ∫_Ω |∇u|² ≥ 0` for every
`u ∈ D(A)`; on every open set. -/
theorem heatOperator_isMonotone : Brezis.Chapter07.IsMonotone (heatOperator Ω) := fun f ↦ by
  rw [heatOperator_apply_eq]
  exact dirichletLaplacian_inner_self_nonneg _

/-- **(iii) `A` is symmetric** (proof of Theorem 10.1): `(Au, v)_{L²} = ∫_Ω ∇u · ∇v = (u, Av)_{L²}`
for `u, v ∈ D(A)`; on every open set. -/
theorem heatOperator_isSymmetric : IsSymmetricOperator (heatOperator Ω) := fun f g ↦ by
  rw [heatOperator_apply_eq, heatOperator_apply_eq]
  exact dirichletLaplacian_isFormalAdjoint
    (⟨f, heatOperator_domain_le f.2⟩ : (dirichletLaplacian Ω).domain)
    ⟨g, heatOperator_domain_le g.2⟩

/-! ### The problem (1), (2), (3) in the class (4) -/

variable (Ω) in
/-- **The problem (1), (2), (3) in the class (4) of Theorem 10.1**: `u : ℝ → L²(Ω)` (the book's
`u(x, t)`, read as the curve `t ↦ u(·, t)`) is a solution with initial datum `u₀` if
`u ∈ C([0, ∞); L²(Ω))`, `u ∈ C((0, ∞); H²(Ω) ∩ H¹₀(Ω))` — `u(t) ∈ D(A) = H² ∩ H¹₀` for `t > 0`,
which is the boundary condition (2), and `u` lifts continuously to `H²(Ω)` on `(0, ∞)` —,
`u ∈ C¹((0, ∞); L²(Ω))`, `∂ₜu = Δu = −A u` in `L²(Ω)` for `t > 0` (1), and `u(0) = u₀` (3). -/
structure IsHeatSolution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Prop where
  /-- `u ∈ C([0, ∞); L²(Ω))`. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- `u(t) ∈ H²(Ω) ∩ H¹₀(Ω)` for `t > 0`: the boundary condition (2). -/
  mem_domain : ∀ t, 0 < t → u t ∈ (heatOperator Ω).domain
  /-- `u ∈ C((0, ∞); H²(Ω))`. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ioi 0)
  /-- `u ∈ C¹((0, ∞); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 1 u (Ioi 0)
  /-- The heat equation (1): `∂ₜu(t) = Δu(t) = −A u(t)` for `t > 0`. -/
  hasDerivAt : ∀ t (ht : 0 < t), HasDerivAt u (-(heatOperator Ω ⟨u t, mem_domain t ht⟩)) t
  /-- The initial condition (3): `u(0) = u₀`. -/
  apply_zero : u 0 = u₀

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **A solution in the class (4) is a solution of the backbone's weak class** `Heat.IsSolution`
(the class of Theorem 7.7 for the Dirichlet Laplacian with its weak domain), on every open set:
`D(A) ⊆ {u ∈ H¹₀ : Δu ∈ L²}` and `A` agrees with the Dirichlet Laplacian there. -/
theorem IsHeatSolution.isSolution (h : IsHeatSolution Ω u₀ u) : Heat.IsSolution Ω u₀ u where
  toIsSolutionOn :=
    { apply_zero := h.apply_zero
      mem_domain := fun t ht ↦ heatOperator_domain_le (h.mem_domain t ht)
      hasDerivWithinAt := fun t ht ↦
        ((h.hasDerivAt t ht).congr_deriv (congrArg Neg.neg (heatOperator_apply_eq _)))
          |>.hasDerivWithinAt }
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn

/-- **Footnote 3**: `|∇v|²_{L²(Ω)} = ∑ᵢ ∫_Ω |∂v/∂xᵢ|²` is the Dirichlet form `∫_Ω |∇v|²` of the
backbone, for `v ∈ H¹(Ω)`. -/
theorem sum_integral_partialDeriv_sq (v : hSpace N Ω) :
    ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2 = Elliptic.dirichletForm Ω v v := by
  rw [Elliptic.dirichletForm_apply_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.L2.inner_eq_integral_mul]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ sq _)

/-- The gradient norm of `u(t)`, read on any `H¹₀`-lift, is `(A u(t), u(t))_{L²}`. -/
theorem IsHeatSolution.inner_apply_self_eq (h : IsHeatSolution Ω u₀ u) {t : ℝ} (ht : 0 < t)
    {v : hSpace N Ω} (hv : v ∈ hZeroSpace N Ω) (hvt : fnL ℝ 𝔟 1 2 Ω volume v = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.isSolution.mem_domain ht⟩, u t⟫_ℝ
      = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2 := by
  rw [sum_integral_partialDeriv_sq]
  exact dirichletLaplacian_inner_self_eq_dirichletForm _ hv hvt

/-! ### Theorem 10.1, the energy identity (6) -/

/-- **Theorem 10.1, the energy identity (6)**: for a solution `u` of (1), (2), (3) and any
function `g` with `g(t) = |∇u(t)|²_{L²(Ω)} = ∑ᵢ ∫_Ω |∂ᵢu(x, t)|² dx` for `t > 0` (footnote 3, read
on the `H¹₀`-lift of `u(t)`), `g` is integrable on `(0, T]` and
`½ |u(T)|²_{L²} + ∫₀ᵀ |∇u(t)|²_{L²} dt = ½ |u₀|²_{L²}` for every `T > 0`. The book's argument with
`φ(t) = ½ |u(t)|²`, `φ' = (u, Δu) = −|∇u|²` on `(0, ∞)` and `ε → 0`, is the backbone's
`Heat.IsSolution.energy`; it holds on every open set. -/
theorem theorem_10_1_energy (hu : IsHeatSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = u t ∧
      g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t = 1 / 2 * ‖u₀‖ ^ 2 :=
  hu.isSolution.energy (fun t ht ↦ by
    obtain ⟨v, hv, hvt, hgt⟩ := hg t ht
    rw [hgt, hu.inner_apply_self_eq ht hv hvt]) hT

/-- **Theorem 10.1, the gradient half of "`u ∈ L²(0, ∞; H¹₀(Ω))`"**, which is what the book's
proof establishes on every open set: `t ↦ |∇u(t)|²_{L²(Ω)}` is integrable on `(0, ∞)` and
`∫₀^∞ |∇u(t)|²_{L²} dt ≤ ½ |u₀|²_{L²}` ((6) for every `T`, with `|u(T)|² ≥ 0`). The membership
`u ∈ L²(0, ∞; H¹₀(Ω))` itself holds for bounded `Ω` (`theorem_10_1_memLp`) and fails on
unbounded domains, where `∫₀^∞ |u(t)|²_{L²} dt` need not be finite. -/
theorem theorem_10_1_memLp_gradient (hu : IsHeatSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t, 0 < t → ∃ v : hSpace N Ω, v ∈ hZeroSpace N Ω ∧ fnL ℝ 𝔟 1 2 Ω volume v = u t ∧
      g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2) :
    IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 :=
  hu.isSolution.integral_inner_apply_le fun t ht ↦ by
    obtain ⟨v, hv, hvt, hgt⟩ := hg t ht
    rw [hgt, hu.inner_apply_self_eq ht hv hvt]

/-! ### Theorem 10.2 (a) -/

/-- **Theorem 10.2 (a)**, the clauses that hold on every open set: if `u₀ ∈ H¹₀(Ω)` — the datum
is `fnL v₀` for some `v₀ ∈ H¹₀(Ω)` — then the solution `u` of (1), (2), (3) satisfies
`u ∈ C([0, ∞); H¹₀(Ω))`, `∂ₜu ∈ L²(0, ∞; L²(Ω))`, and (11):
`∫₀ᵀ |∂ₜu(t)|²_{L²} dt + ½ |∇u(T)|²_{L²} = ½ |∇u₀|²_{L²}` for every `T > 0`, with `|∇u(T)|²` read
on any `H¹₀`-lift `v` of `u(T)` (footnote 3). The book's proof — the operator `A₁` in
`H₁ = H¹₀(Ω)` with the scalar product `∫ ∇u · ∇v + ∫ uv` (the backbone's `dirichletLaplacianH10`,
maximal monotone and symmetric on any open set), Theorem 7.7 there, uniqueness, and
`φ(t) = ½ |∇u(t)|²` with `φ' = −|∂ₜu|²` — is the backbone's
`Heat.IsSolution.contDiffOnThrough_sobolevZero_of_mem`, `memLp_deriv` and `energy_sobolevZero`.
The clause `u ∈ L²(0, ∞; H²(Ω))` is `theorem_10_2_a_memLp` (bounded `Ω`). -/
theorem theorem_10_2_a {v₀ : hZeroSpace N Ω}
    (hu : IsHeatSolution Ω (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u) :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 0 u (Ici 0) ∧
      MemLp (deriv u) 2 (volume.restrict (Ioi 0)) ∧
      ∀ T, 0 < T → ∀ v : hSpace N Ω, v ∈ hZeroSpace N Ω → fnL ℝ 𝔟 1 2 Ω volume v = u T →
        (∫ t in (0 : ℝ)..T, ‖deriv u t‖ ^ 2)
            + 1 / 2 * ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv v i x ^ 2
          = 1 / 2 * ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv (v₀ : hSpace N Ω) i x ^ 2 := by
  refine ⟨hu.isSolution.contDiffOnThrough_sobolevZero_of_mem rfl,
    (hu.isSolution.memLp_deriv rfl).1, fun T hT v hv hvT ↦ ?_⟩
  have e := (hu.isSolution.energy_sobolevZero rfl hT).2
  rw [hu.inner_apply_self_eq hT hv hvT, ← sum_integral_partialDeriv_sq] at e
  exact e

/-! ### Remark 1: the backward problem (9'), (10), (11) -/

variable (Ω) in
/-- **The backward problem (9'), (10), (11)** of Remark 1, `−∂ₜu − Δu = 0` in `Ω × (−∞, T)`,
`u = 0` on `Γ × (−∞, T)`, with the final datum `u(T) = u_T`, in the class of Theorem 10.1
transported by `t ↦ T − t`: `u ∈ C((−∞, T]; L²(Ω)) ∩ C((−∞, T); H²(Ω) ∩ H¹₀(Ω))`,
`u ∈ C¹((−∞, T); L²(Ω))`, `∂ₜu = −Δu = A u` for `t < T`, `u(T) = u_T`. -/
structure IsBackwardHeatSolution (T : ℝ) (uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) : Prop where
  /-- `u ∈ C((−∞, T]; L²(Ω))`. -/
  continuousOn : ContinuousOn u (Iic T)
  /-- `u(t) ∈ H²(Ω) ∩ H¹₀(Ω)` for `t < T`: the boundary condition (10). -/
  mem_domain : ∀ t, t < T → u t ∈ (heatOperator Ω).domain
  /-- `u ∈ C((−∞, T); H²(Ω))`. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Iio T)
  /-- `u ∈ C¹((−∞, T); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 1 u (Iio T)
  /-- The equation (9'): `∂ₜu(t) = −Δu(t) = A u(t)` for `t < T`. -/
  hasDerivAt : ∀ t (ht : t < T), HasDerivAt u (heatOperator Ω ⟨u t, mem_domain t ht⟩) t
  /-- The final condition (11): `u(T) = u_T`. -/
  apply_eq : u T = uT

/-- A solution of the backward problem in the class of Remark 1 is one in the backbone's weak
class `Heat.IsBackwardSolution`, on every open set. -/
theorem IsBackwardHeatSolution.isBackwardSolution {T : ℝ}
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} (h : IsBackwardHeatSolution Ω T uT u) :
    Heat.IsBackwardSolution Ω T uT u where
  apply_eq := h.apply_eq
  mem_domain := fun t ht ↦ heatOperator_domain_le (h.mem_domain t ht)
  hasDerivAt := fun t ht ↦ (h.hasDerivAt t ht).congr_deriv (heatOperator_apply_eq _)
  continuousOn := h.continuousOn
  contDiffOn := h.contDiffOn

/-! ### Remark 4: the compatibility conditions are necessary -/

/-- **Remark 4.** The compatibility conditions (8) are necessary for a solution of (1), (2), (3)
that is smooth up to `t = 0`: if `u : ℝ^N × ℝ → ℝ` is of class `C^∞` (on `ℝ^N × ℝ`, so that
`u ∈ C^∞(Ω̄ × [0, ∞))` and the boundary values of `Δ^j u(·, 0)` are meaningful as written) and
satisfies `∂ₜu = Δu` in `Q = Ω × (0, ∞)` and `u = 0` on `Σ = Γ × (0, ∞)`, then
`Δ^j u(·, 0) = 0` on `Γ` for every `j`: `∂ₜ^j u = 0` on `Γ × [0, ∞)` by continuity (15),
`∂ₜ^j u = Δ^j u` in `Q̄` by induction and continuity (16), and the two are compared on `Γ × {0}`.
The backbone's `Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier` (with diffusivity
`1`, on the cylinder `Ω × (0, 1)`). -/
theorem remark_10_4 {u : 𝔼 × ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (heq : ∀ x ∈ Ω, ∀ t, 0 < t → deriv (fun s ↦ u (x, s)) t = Δ (fun y ↦ u (y, t)) x)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), ∀ t, 0 < t → u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier (Ω : Set 𝔼), (Δ^[j] fun y ↦ u (y, 0)) x = 0 := by
  have hcl : Heat.IsClassicalSolution 1 (Ω : Set 𝔼) 1 u :=
    { continuousOn := hu.continuous.continuousOn
      differentiableAt_snd := fun x _ t _ ↦
        ((hu.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
      contDiffAt_fst := fun x _ t _ ↦
        ((hu.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)).contDiffAt
      deriv_eq_laplacian := fun x hx t ht ↦ by rw [one_mul]; exact heq x hx t ht.1 }
  exact Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier Ω.isOpen one_ne_zero
    one_pos hcl hu (fun x hx t ht ↦ hΓ x hx t ht.1) j

end General

section Regular

variable {d : ℕ}

/-- The book's `ℝ^N`, with `N = d + 1`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))

/-- The standard basis of `ℝ^N`. -/
local notation "𝔟" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-! ### `A` on a regular domain: claims (i)–(iii) of the proof of Theorem 10.1 -/

/-- **`A` is the Dirichlet Laplacian** on a domain of class `C²` with `Γ` bounded: the weak
domain `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}` is `H²(Ω) ∩ H¹₀(Ω)` — Theorem 9.25 applied to
`u − Δu ∈ L²(Ω)` (step (ii) of the book's proof; the backbone's
`dirichletLaplacianDomain_eq_of_isContDiffChartDomain`). Under the chapter's standing `C^∞`
hypothesis this identification is what lets every backbone statement about `dirichletLaplacian`
be read for the book's `A`. -/
theorem heatOperator_eq_dirichletLaplacian (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    heatOperator Ω = dirichletLaplacian Ω := by
  refine LinearPMap.eq_of_le_of_domain_eq LinearPMap.domRestrict_le ?_
  ext f
  rw [heatOperator_mem_domain_iff]
  exact ((dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1 f).symm

/-- **(i)–(ii): `A` is maximal monotone** (proof of Theorem 10.1) on a `C²` domain with `Γ`
bounded: `(Au, u) = ∫_Ω |∇u|² ≥ 0`, and `R(I + A) = L²(Ω)` since for every `f ∈ L²(Ω)` the
equation `u − Δu = f` has a solution `u ∈ H²(Ω) ∩ H¹₀(Ω)` (Theorem 9.25). The backbone's
`dirichletLaplacian_isMaximalMonotone` through `heatOperator_eq_dirichletLaplacian`. -/
theorem heatOperator_isMaximalMonotone (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    Brezis.Chapter07.IsMaximalMonotone (heatOperator Ω) := by
  rw [heatOperator_eq_dirichletLaplacian hΩ hΓ, isMaximalMonotone_iff]
  exact dirichletLaplacian_isMaximalMonotone

/-- **(iii): `A` is self-adjoint** (proof of Theorem 10.1) on a `C²` domain with `Γ` bounded:
`A` is symmetric (`heatOperator_isSymmetric`) and maximal monotone, hence self-adjoint by
Proposition 7.6. -/
theorem heatOperator_isSelfAdjoint (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsSelfAdjointOperator (heatOperator Ω) :=
  proposition_7_6 (heatOperator_isMaximalMonotone hΩ hΓ) heatOperator_isSymmetric

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **The class (4) is the backbone's weak class** on a `C²` domain with `Γ` bounded:
`IsHeatSolution Ω u₀ u ↔ Heat.IsSolution Ω u₀ u`. The forward direction holds on every open set
(`IsHeatSolution.isSolution`); conversely a weak solution has `u(t) ∈ D(A) = H² ∩ H¹₀` for `t > 0`
by `heatOperator_eq_dirichletLaplacian` and lifts continuously to `H²(Ω)` on `(0, ∞)` by the
graph-norm estimate of Theorem 9.25 (`Heat.IsSolution.contDiffOnThrough_two`). -/
theorem isHeatSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) :
    IsHeatSolution Ω u₀ u ↔ Heat.IsSolution Ω u₀ u := by
  refine ⟨fun h ↦ h.isSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, 0 < t → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain ht))
  exact
    { continuousOn := h.continuousOn
      mem_domain := hmem
      contDiffOnThrough := (h.contDiffOnThrough_two hΩ hΓ).1
      contDiffOn := h.contDiffOn
      hasDerivAt := fun t ht ↦
        (h.hasDerivAt ht).congr_deriv
          (congrArg Neg.neg (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm)
      apply_zero := h.apply_zero }

/-! ### Theorem 10.1 -/

/-- **Theorem 10.1, existence and uniqueness.** Let `Ω` be of class `C^∞` with `Γ` bounded and
`u₀ ∈ L²(Ω)`. Then there exists a unique function `u` satisfying (1), (2), (3) in the class (4),
`u ∈ C([0, ∞); L²(Ω)) ∩ C((0, ∞); H²(Ω) ∩ H¹₀(Ω))`, `u ∈ C¹((0, ∞); L²(Ω))` — unique on `[0, ∞)`,
the class not constraining negative times. The book's proof: `A` is a self-adjoint maximal
monotone operator in `H = L²(Ω)` (`heatOperator_isSelfAdjoint`), and Theorem 7.7 applies. The
backbone (`Heat.existsUnique_isSolution`) proves it on every open set for the weak class, which
the `C²` hypothesis identifies with the book's (`isHeatSolution_iff`); the solution is the
semigroup `t ↦ S_A(t) u₀` (`Heat.solution`). The smoothing (5) is `theorem_10_1_smooth`, the
energy identity (6) `theorem_10_1_energy`, and `u ∈ L²(0, ∞; H¹₀(Ω))` is `theorem_10_1_memLp`. -/
theorem theorem_10_1 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ u, IsHeatSolution Ω u₀ u ∧ ∀ v, IsHeatSolution Ω u₀ v → EqOn v u (Ici 0) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ := Heat.existsUnique_isSolution (Ω := Ω) u₀
  exact ⟨u, (isHeatSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isSolution⟩

/-- **Theorem 10.1, "`u ∈ L²(0, ∞; H¹₀(Ω))`"**, for **bounded** `Ω`: the solution `u` of (1), (2),
(3) lifts on `(0, ∞)` to a curve of `L²((0, ∞); H¹₀(Ω))` through the inclusion `H¹₀(Ω) → L²(Ω)`.
From the gradient bound `∫₀^∞ |∇u(t)|² dt ≤ ½ |u₀|²` (`theorem_10_1_memLp_gradient`) and
Poincaré's inequality (Corollary 9.19), `|u(t)|_{H¹} ≤ C |∇u(t)|_{L²}`; the backbone's
`Heat.IsSolution.memLpThrough_sobolevZero_of_isBounded`. The book states the clause for every
`Ω` of class `C^∞` with `Γ` bounded; on an unbounded domain it is false (erratum). -/
theorem theorem_10_1_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hu : IsHeatSolution Ω u₀ u) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 2 u (Ioi 0) :=
  hu.isSolution.memLpThrough_sobolevZero_of_isBounded hb

/-- **The display (7) of the proof of Theorem 10.1.** For `Ω` of class `C^∞` with `Γ` bounded and
every `ℓ`, `D(A^ℓ) = {u ∈ H^{2ℓ}(Ω) : u = Δu = ⋯ = Δ^{ℓ−1}u = 0 on Γ}` with continuous injection
`D(A^ℓ) ⊆ H^{2ℓ}(Ω)`: `u ∈ D(A^ℓ)` (chapter 7's `domainPow`) iff `u` is the function of an
element of `H^{2ℓ}(Ω)` and the iterates `u, −Δu, …, (−Δ)^{ℓ−1}u` all lie in `H¹₀(Ω)`
(`IsDirichletLaplacianChain`, "`= 0` on `Γ`" read as membership of `H¹₀(Ω)`, Theorem 9.17's
trace-free reading, each iterate being in `H²(Ω)` with the next iterate its weak Laplacian), and
there is `C` with `‖w‖_{H^{2ℓ}} ≤ C ‖x‖_{D(A^ℓ)}` for every `x ∈ D(A^ℓ)` (chapter 7's Hilbert
space `PowDomain`, graph norm `(∑ⱼ |A^j u|²)^{1/2}`) and every `H^{2ℓ}`-lift `w` of `u = A^0 x`.
Theorem 9.25 iterated (`theorem_9_25_higher`): the backbone's `dirichletLaplacian_mem_powDomain_iff`
and `dirichletLaplacian_norm_sobolev_le_of_powDomain`; the inclusion `⊇` needs no regularity. -/
theorem equation_10_7 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (ℓ : ℕ) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)), f ∈ domainPow (heatOperator Ω) ℓ ↔
      (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω, fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = f) ∧
        IsDirichletLaplacianChain Ω ℓ f) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (heatOperator Ω).PowDomain ℓ)
      (w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω),
      fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = LinearPMap.PowDomain.applyL (heatOperator Ω) ℓ 0 x →
        ‖w‖ ≤ C * ‖x‖ := by
  have hΩ' : IsContDiffChartDomain (2 * ℓ) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  rw [heatOperator_eq_dirichletLaplacian (hΩ.of_le le_top) hΓ]
  exact ⟨fun f ↦ by rw [mem_domainPow_iff]; exact dirichletLaplacian_mem_powDomain_iff hΩ' hΓ f,
    dirichletLaplacian_norm_sobolev_le_of_powDomain hΩ' hΓ⟩

/-- **Theorem 10.1, the smoothing (5)**: for `Ω` of class `C^∞` with `Γ` bounded, the solution
`u` of (1), (2), (3) satisfies `u ∈ C^∞(Ω̄ × [ε, ∞))` for every `ε > 0` — there is a function
`U : ℝ^N × ℝ → ℝ` with `U(·, t) = u(t)` a.e. on `Ω` for every `t > 0`, of class `C^∞` on
`Ω × (ε, ∞)` with every derivative extending continuously to `Ω̄ × [ε, ∞)`, for every `ε > 0`
(`ContDiffOnClosure`, footnote 16 of chapter 9). The book's argument: `u ∈ C^k((0, ∞); D(A^ℓ))`
for all `k, ℓ` (Theorem 7.7), `D(A^ℓ) ⊆ H^{2ℓ}(Ω)` with continuous injection ((7),
`equation_10_7`), hence `u ∈ C^k((0, ∞); H^{2ℓ}(Ω))` for all `k, ℓ`, and Corollary 9.15
(`H^{2ℓ}(Ω) ⊆ C^k(Ω̄)` for `k + N/2 < 2ℓ`, the integer-safe form) — the backbone's
`Heat.IsSolution.contDiffOnThrough_sobolev` and the space–time bridge
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi`. The conclusion cannot be
strengthened to `C^∞(Ω̄ × [0, ∞))` (Theorem 10.2 (c) and Remark 4). -/
theorem theorem_10_1_smooth (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 < t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ∀ ε > 0, ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi ε) := by
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ
  have hm : ∀ m : ℕ, Bochner.ContDiffOnThrough (fnL ℝ 𝔟 m 2 Ω volume) ∞ u (Ioi 0) := fun m ↦
    (hu.isSolution.contDiffOnThrough_sobolev (ℓ := m) (hΩ.of_le (by simp)) hΓ).sobolev_of_le
      (by omega)
  obtain ⟨U, hU, hc⟩ := Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi hext hm
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

/-! ### Theorem 10.2 (a)–(c) on a regular domain -/

/-- **Theorem 10.2 (a), "`u ∈ L²(0, ∞; H²(Ω))`"**, for **bounded** `Ω` of class `C²` with `Γ`
bounded: if `u₀ ∈ H¹₀(Ω)` then the solution lifts on `(0, ∞)` to a curve of `L²((0, ∞); H²(Ω))`.
The `H²`-lift satisfies `|w(t)|_{H²} ≤ C (|u(t)| + |∂ₜu(t)|)` (the graph-norm estimate of
Theorem 9.25), and both are square integrable (Poincaré and (11)); the backbone's
`Heat.IsSolution.memLpThrough_two_of_isBounded`. On an unbounded domain only
`∫₀^∞ |Δu(t)|² dt = ∫₀^∞ |∂ₜu(t)|² dt < ∞` holds (erratum). -/
theorem theorem_10_2_a_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC 2 (Ω : Set 𝔼)) (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    {v₀ : hZeroSpace (d + 1) Ω}
    (hu : IsHeatSolution Ω (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume v₀) u) :
    Bochner.MemLpThrough (fnL ℝ 𝔟 2 2 Ω volume) 2 u (Ioi 0) :=
  hu.isSolution.memLpThrough_two_of_isBounded hb hΩ hΓ rfl

/-- **Theorem 10.2 (b)**, on a `C²` domain with `Γ` bounded: if `u₀ ∈ H²(Ω) ∩ H¹₀(Ω)`
(`u₀ ∈ D(A)`) then the solution `u` of (1), (2), (3) satisfies `u ∈ C([0, ∞); H²(Ω))`, and the
identity of the book's proof holds: for any `g` with `g(t) = |∇Δu(t)|²_{L²} = |∇∂ₜu(t)|²_{L²}` for
`t > 0` (footnote 3, on the `H¹₀`-lift of `∂ₜu(t) = Δu(t)`) and every `T > 0`, `g` is integrable
on `(0, T]` and `½ |Δu(T)|²_{L²} + ∫₀ᵀ |∇Δu(t)|²_{L²} dt = ½ |Δu₀|²_{L²}`, with `Δu(T) = −A u(T)`.
The book's route is Theorem 7.7 for `A₂` in `H₂ = H² ∩ H¹₀`; the backbone's is Theorem 7.4 for
`u₀ ∈ D(A)` (`Heat.IsSolution.contDiffOnThrough_two_Ici_of_mem_domain`) and `φ(t) = ½ |Δu(t)|²`
with `φ' = −|∇Δu|²` (`Heat.IsSolution.energy_domain`, on every open set). The clauses
`u ∈ L²(0, ∞; H³(Ω))` and `∂ₜu ∈ L²(0, ∞; H¹₀(Ω))` are `theorem_10_2_b_memLp`. -/
theorem theorem_10_2_b (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (hu₀ : u₀ ∈ (heatOperator Ω).domain)
    (hu : IsHeatSolution Ω u₀ u) :
    Bochner.ContDiffOnThrough (fnL ℝ 𝔟 2 2 Ω volume) 0 u (Ici 0) ∧
      ∀ g : ℝ → ℝ, (∀ t, 0 < t → ∃ z : hSpace (d + 1) Ω, z ∈ hZeroSpace (d + 1) Ω ∧
          fnL ℝ 𝔟 1 2 Ω volume z = deriv u t ∧
          g t = ∑ i, ∫ x in (Ω : Set 𝔼), partialDeriv z i x ^ 2) →
        ∀ T (hT : 0 < T), IntegrableOn g (Ioc 0 T) ∧
          1 / 2 * ‖heatOperator Ω ⟨u T, hu.mem_domain T hT⟩‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t
            = 1 / 2 * ‖heatOperator Ω ⟨u₀, hu₀⟩‖ ^ 2 := by
  have h := hu.isSolution
  refine ⟨h.contDiffOnThrough_two_Ici_of_mem_domain (heatOperator_domain_le hu₀) hΩ hΓ,
    fun g hg T hT ↦ ?_⟩
  have hg' : ∀ t (ht : 0 < t),
      g t = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ := by
    intro t ht
    obtain ⟨z, hz, hzt, hgt⟩ := hg t ht
    rw [hgt, sum_integral_partialDeriv_sq]
    exact (dirichletLaplacian_inner_self_eq_dirichletForm _ hz hzt).symm
  obtain ⟨hint, e⟩ := h.energy_domain (heatOperator_domain_le hu₀) hg' hT
  refine ⟨hint, ?_⟩
  rw [heatOperator_apply_eq, heatOperator_apply_eq, ← e, h.deriv_eq hT, norm_neg]

/-- **Theorem 10.2 (b), "`u ∈ L²(0, ∞; H³(Ω))` and `∂ₜu ∈ L²(0, ∞; H¹₀(Ω))`"**, for **bounded**
`Ω` of class `C³` with `Γ` bounded and `u₀ ∈ H²(Ω) ∩ H¹₀(Ω)`: the solution lifts on `(0, ∞)` to a
curve of `L²((0, ∞); H³(Ω))`, and `∂ₜu` to a curve of `L²((0, ∞); H¹₀(Ω))`. The book's "(why?)":
the `H³` estimate of Theorem 9.25 for `−Δu = ∂ₜu ∈ H¹₀` and Poincaré; the backbone's
`Heat.IsSolution.memLpThrough_three_of_isBounded` and `memLpThrough_sobolevZero_deriv_of_isBounded`.
On unbounded `Ω` the memberships fail (erratum). -/
theorem theorem_10_2_b_memLp (hb : Bornology.IsBounded (Ω : Set 𝔼))
    (hΩ : IsOfClassC 3 (Ω : Set 𝔼)) (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : u₀ ∈ (heatOperator Ω).domain) (hu : IsHeatSolution Ω u₀ u) :
    Bochner.MemLpThrough (fnL ℝ 𝔟 3 2 Ω volume) 2 u (Ioi 0) ∧
      Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ 𝔟 1 2 Ω volume) 2 (deriv u) (Ioi 0) :=
  ⟨hu.isSolution.memLpThrough_three_of_isBounded hb hΩ hΓ (heatOperator_domain_le hu₀),
    hu.isSolution.memLpThrough_sobolevZero_deriv_of_isBounded hb (heatOperator_domain_le hu₀)⟩

/-- Theorem 10.2 (c)'s input to the space–time bridge: if `u₀ ∈ D(A^k)` for every `k`, then
`u ∈ C^∞([0, ∞); H^m(Ω))` for every `m` (Theorem 7.5 and (7); one lift for all orders by
`contDiffOnThrough_infty_of_forall`, then every `m` from every `2ℓ`). To be replaced by the
backbone's `Heat.IsSolution.contDiffOnClosure_spaceTime_Ici` once it exists. -/
private theorem forall_contDiffOnThrough_Ici_of_forall_powDomain (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (h : Heat.IsSolution Ω u₀ u)
    (hk : ∀ k : ℕ, ∃ x : (dirichletLaplacian Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) k 0 x = u₀) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ 𝔟 m 2 Ω volume) ∞ u (Ici 0) := by
  have hΩ' : IsContDiffChartDomain (2 * m) (Ω : Set 𝔼) := hΩ.of_le (by simp)
  have h2m : ∀ n : ℕ, Bochner.ContDiffOnThrough (fnL ℝ 𝔟 (2 * m) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hk (m + n)
    exact (h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx (ℓ := m) (by omega) hΩ' hΓ).of_le
      (by exact_mod_cast (by omega : n ≤ m + n - m))
  -- the injectivity of the inclusion, with its type spelled out (instance search on the
  -- implicit form of `fnL_injective` takes a minute)
  have hJ : Function.Injective (fnL ℝ 𝔟 (2 * m) 2 Ω volume) := SobolevMultiIndex.fnL_injective
  exact (contDiffOnThrough_infty_of_forall hJ h2m).sobolev_of_le (by omega)

/-- **Theorem 10.2 (c).** Let `Ω` be of class `C^∞` with `Γ` bounded. If `u₀ ∈ H^k(Ω)` for every
`k` and satisfies the compatibility conditions (8), `u₀ = Δu₀ = ⋯ = Δ^j u₀ = ⋯ = 0` on `Γ` for
every `j` — read, as in (7), as: for every `ℓ` the iterates `u₀, −Δu₀, …, (−Δ)^{ℓ−1}u₀` lie in
`H¹₀(Ω)` (`IsDirichletLaplacianChain Ω ℓ u₀`) — then `u ∈ C^∞(Ω̄ × [0, ∞))`: there is
`U : ℝ^N × ℝ → ℝ` with `U(·, t) = u(t)` a.e. on `Ω` for every `t ≥ 0`, of class `C^∞` on
`Ω × (0, ∞)` with every derivative extending continuously to `closure (Ω × (0, ∞)) = Ω̄ × [0, ∞)`.
The book's proof: "assumption (8) says precisely that `u₀ ∈ D(A^k)` for every `k`" ((7),
`equation_10_7`), Theorem 7.5 gives `u ∈ C^{k−j}([0, ∞); D(A^j))` for all `j ≤ k`, and (7) with
Corollary 9.15 as in Theorem 10.1 — the backbone's
`Heat.IsSolution.contDiffOnThrough_sobolev_Ici_of_powDomain` and the bridge
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`. -/
theorem theorem_10_2_c (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼)))
    (hu₀ : ∀ k : ℕ, ∃ w : sobolevSpaceHigher (d + 1) k 2 Ω, fnL ℝ 𝔟 k 2 Ω volume w = u₀)
    (hcomp : ∀ ℓ : ℕ, IsDirichletLaplacianChain Ω ℓ u₀) (hu : IsHeatSolution Ω u₀ u) :
    ∃ U : 𝔼 × ℝ → ℝ, (∀ t, 0 ≤ t → (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set 𝔼)] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set 𝔼) ×ˢ Ioi 0) := by
  have hk : ∀ k : ℕ, ∃ x : (dirichletLaplacian Ω).PowDomain k,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) k 0 x = u₀ := fun k ↦
    (dirichletLaplacian_mem_powDomain_iff (hΩ.of_le (by simp)) hΓ u₀).2 ⟨hu₀ (2 * k), hcomp k⟩
  have hext : IsSobolevExtensionDomainAll (d + 1) Ω :=
    IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ
  obtain ⟨U, hU, hc⟩ := Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici hext
    (forall_contDiffOnThrough_Ici_of_forall_powDomain hΩ hΓ hu.isSolution hk)
  exact ⟨U, fun t ht ↦ hU t ht, hc⟩

/-! ### Remark 1 -/

/-- **The backward problem's class is the backbone's**, on a `C²` domain with `Γ` bounded:
`IsBackwardHeatSolution Ω T u_T u ↔ Heat.IsBackwardSolution Ω T u_T u`. -/
theorem isBackwardHeatSolution_iff (hΩ : IsOfClassC 2 (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {T : ℝ}
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} :
    IsBackwardHeatSolution Ω T uT u ↔ Heat.IsBackwardSolution Ω T uT u := by
  refine ⟨fun h ↦ h.isBackwardSolution, fun h ↦ ?_⟩
  have hdom := (dirichletLaplacianDomain_eq_of_isContDiffChartDomain hΩ hΓ).1
  have hmem : ∀ t, t < T → u t ∈ (heatOperator Ω).domain := fun t ht ↦
    heatOperator_mem_domain_iff.2 ((hdom _).1 (h.mem_domain t ht))
  -- the `H²`-lift, transported from the forward solution `s ↦ u (T − s)`
  obtain ⟨v, hv, hvu⟩ := ((Heat.isBackwardSolution_iff.1 h).contDiffOnThrough_two hΩ hΓ).1
  exact
    { continuousOn := h.continuousOn
      mem_domain := hmem
      contDiffOnThrough := ⟨fun t ↦ v (T - t),
        hv.comp (contDiffOn_const.sub contDiffOn_id) fun t (ht : t < T) ↦
          show T - t ∈ Ioi (0 : ℝ) from sub_pos.2 ht,
        fun t (ht : t < T) ↦ by
          have := hvu (T - t) (sub_pos.2 ht)
          simp only [sub_sub_cancel] at this
          exact this⟩
      contDiffOn := h.contDiffOn
      hasDerivAt := fun t ht ↦
        (h.hasDerivAt t ht).congr_deriv (heatOperator_apply_eq ⟨u t, hmem t ht⟩).symm
      apply_eq := h.apply_eq }

/-- **Remark 1, the well-posed half.** For `Ω` of class `C^∞` with `Γ` bounded, every `T` and
every final datum `u_T ∈ L²(Ω)`, the problem (9'), (10), (11) — `−∂ₜu − Δu = 0` in
`Ω × (−∞, T)`, `u = 0` on `Γ × (−∞, T)`, `u(T) = u_T` — has a unique solution in the class of
Theorem 10.1 (unique on `(−∞, T]`): "change `t` into `T − t` and apply Theorem 10.1". The
backbone's `Heat.existsUnique_isSolution_backward`; the solution is `t ↦ S_A(T − t) u_T`. -/
theorem remark_10_1 (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    ∃ u, IsBackwardHeatSolution Ω T uT u ∧
      ∀ v, IsBackwardHeatSolution Ω T uT v → EqOn v u (Iic T) := by
  have hΩ2 : IsOfClassC 2 (Ω : Set 𝔼) := hΩ.of_le le_top
  obtain ⟨u, hu, huniq⟩ := Heat.existsUnique_isSolution_backward (Ω := Ω) T uT
  exact ⟨u, (isBackwardHeatSolution_iff hΩ2 hΓ).2 hu, fun v hv ↦ huniq v hv.isBackwardSolution⟩

/-- **Remark 1, the necessary condition (12) for the backward problem (9), (10), (11).** For
`Ω` of class `C^∞` with `Γ` bounded, if the backward problem `∂ₜu − Δu = 0` in `Ω × (0, T)`,
`u = 0` on `Γ × (0, T)`, `u(T) = u_T` has a solution in the class of Theorem 10.1 — a solution
`u` of (1), (2), (3) on `[0, ∞)` (with datum `u(0)`; by uniqueness this is the only way a solution
on `[0, T]` in that class arises) with `u(T) = u_T` — then necessarily `u_T ∈ D(A^ℓ)` for every
`ℓ`, hence by (7) `u_T ∈ H^{2ℓ}(Ω)` with `Δ^j u_T = 0` on `Γ` for all `j < ℓ`, for every `ℓ`, and
`u_T ∈ C^∞(Ω̄)` (Corollary 9.15 at every order): `u_T = u(T)` is as smooth as Theorem 10.1 makes
the solution at any positive time (`Heat.IsSolution.exists_powDomain`). The book's further claim,
that even under (12) a solution need not exist, is a counterexample claim and is not formalized. -/
theorem remark_10_1_necessary (hΩ : IsOfClassC ⊤ (Ω : Set 𝔼))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set 𝔼))) {T : ℝ} (hT : 0 < T)
    {uT : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} (hu : IsHeatSolution Ω u₀ u) (huT : u T = uT) :
    (∀ ℓ, uT ∈ domainPow (heatOperator Ω) ℓ) ∧
      (∀ ℓ, (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω, fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = uT) ∧
        IsDirichletLaplacianChain Ω ℓ uT) ∧
      ∃ ũ : 𝔼 → ℝ, ContDiffOnClosure ℝ ∞ ũ Ω ∧ ContinuousOn ũ (closure (Ω : Set 𝔼)) ∧
        (uT : 𝔼 → ℝ) =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ := by
  have hpow : ∀ ℓ, ∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = uT := fun ℓ ↦
    huT ▸ hu.isSolution.exists_powDomain hT ℓ
  have h7 : ∀ ℓ, (∃ w : sobolevSpaceHigher (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ 𝔟 (2 * ℓ) 2 Ω volume w = uT) ∧ IsDirichletLaplacianChain Ω ℓ uT := fun ℓ ↦
    (dirichletLaplacian_mem_powDomain_iff (hΩ.of_le (by simp)) hΓ uT).1 (hpow ℓ)
  refine ⟨fun ℓ ↦ ?_, h7, ?_⟩
  · rw [heatOperator_eq_dirichletLaplacian (hΩ.of_le le_top) hΓ, mem_domainPow_iff]
    exact hpow ℓ
  · refine exists_contDiffOnClosure_infty_of_forall_memSobolevMultiIndex (hΩ.of_le (by simp)) hΓ
      fun m ↦ ?_
    obtain ⟨w, hw⟩ := (h7 m).1
    have hw' : fn w =ᵐ[volume.restrict (Ω : Set 𝔼)] uT :=
      Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)) ↦
        (z : 𝔼 → ℝ)) hw)
    exact ((SobolevMultiIndex.memSobolevMultiIndex w).congr_ae hw').mono_order (by omega)

/-! ### Remark 3: the Fourier method -/

/-- **Remark 3, the Fourier method.** For a bounded (nonempty) `Ω`, let `(eₙ)`, `(λₙ)` be the
Dirichlet eigenbasis of `−Δ` of Theorem 9.31 (the backbone's `Elliptic.dirichletEigenbasis`,
`Elliptic.dirichletEigenvalue`; `theorem_9_31_weak`), and let `u` be the solution of (1), (2),
(3). Then the coefficients `aₙ(t) = (u(t), eₙ)_{L²}` of `u(t) = ∑ₙ aₙ(t) eₙ` satisfy (13),
`aₙ' + λₙ aₙ = 0` on `(0, ∞)`, so that `aₙ(t) = aₙ(0) e^{−λₙ t}` with `aₙ(0) = ∫_Ω u₀ eₙ`, and
the solution is given by the series (14): `u(t) = ∑ₙ (∫_Ω u₀ eₙ) e^{−λₙ t} eₙ` in `L²(Ω)`, for
every `t ≥ 0`. The backbone's `Heat.IsSolution.hasDerivAt_inner_eigenfunction`,
`inner_eigenfunction`, `hasSum_eigenfunction`; no regularity of `Ω` is needed, and the
convergence question the book refers to the literature for is settled by uniqueness. -/
theorem remark_10_3 (hb : Bornology.IsBounded (Ω : Set 𝔼)) (hne : (Ω : Set 𝔼).Nonempty)
    (hu : IsHeatSolution Ω u₀ u) :
    (∀ n, ∀ t, 0 < t → HasDerivAt (fun t ↦ ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)
      (-(Elliptic.dirichletEigenvalue Ω hb n
        * ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ)) t) ∧
    (∀ n, ∀ t, 0 ≤ t → ⟪u t, Elliptic.dirichletEigenbasis Ω hb hne n⟫_ℝ
      = (∫ x in (Ω : Set 𝔼), u₀ x * Elliptic.dirichletEigenbasis Ω hb hne n x)
        * Real.exp (-(Elliptic.dirichletEigenvalue Ω hb n * t))) ∧
    ∀ t, 0 ≤ t → HasSum (fun n ↦
      ((∫ x in (Ω : Set 𝔼), u₀ x * Elliptic.dirichletEigenbasis Ω hb hne n x)
        * Real.exp (-(Elliptic.dirichletEigenvalue Ω hb n * t)))
        • Elliptic.dirichletEigenbasis Ω hb hne n) (u t) := by
  have h := hu.isSolution
  refine ⟨fun n t ht ↦ (h.hasDerivAt_inner_eigenfunction hb hne n ht).congr_deriv (neg_mul _ _),
    fun n t ht ↦ ?_, fun t ht ↦ (h.hasSum_eigenfunction hb hne ht).congr_fun fun n ↦ ?_⟩
  · rw [h.inner_eigenfunction hb hne n ht, MeasureTheory.L2.inner_eq_integral_mul, neg_mul,
      mul_comm]
  · rw [MeasureTheory.L2.inner_eq_integral_mul, neg_mul, mul_comm]

end Regular

end Brezis.Chapter10
