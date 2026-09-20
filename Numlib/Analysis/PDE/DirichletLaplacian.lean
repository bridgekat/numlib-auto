import Numlib.Analysis.Distributions.TestFunctionOps
import Numlib.Analysis.ODE.HilleYosida
import Numlib.Analysis.PDE.Bochner
import Numlib.Analysis.PDE.Elliptic.Regularity

/-!
# The Dirichlet Laplacian as an unbounded operator on `L²(Ω)`

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §10.1 (the
proof of Theorem 10.1): the operator `A = -Δ` on `L²(Ω)` with the Dirichlet boundary condition,
on which both the heat equation and the wave equation of chapter 10 rest.

## Design

`Ω : Opens (EuclideanSpace ℝ (Fin N))`, `L²(Ω) = Lp ℝ 2 (volume.restrict Ω)`,
`H¹(Ω) = SobolevEuclidean N 1 2 Ω`, `H¹₀(Ω) = SobolevEuclideanZero N 1 2 Ω`; an `L²(Ω)` function
"lies in `H¹₀(Ω)`" when it is the function `fnL v` of some `v ∈ H¹₀(Ω)`, which is how every
boundary condition `u = 0` on `Γ` of chapter 10 is read.

The operator is Mathlib's `LinearPMap`, `L²(Ω) →ₗ.[ℝ] L²(Ω)`. Its domain is **not**
`H²(Ω) ∩ H¹₀(Ω)` by definition but the weak one,

  `D(A) = {u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)} = {u ∈ H¹₀(Ω) : ∃ g ∈ L²(Ω), ∫ ∇u·∇φ = ∫ g φ ∀ φ ∈ H¹₀(Ω)}`,

with `A u = g` (`dirichletLaplacianDomain`, `dirichletLaplacian`). Everything the book proves
about `A` in the proof of Theorem 10.1 — monotone, symmetric, `R(I + A) = L²(Ω)` — then holds
on an **arbitrary** open set (`dirichletLaplacian_isMaximalMonotone`,
`dirichletLaplacian_isSelfAdjoint`): maximality is the Riesz representation on `H¹₀(Ω)`, that
is, the Dirichlet principle (Theorem 9.21, `Elliptic.existsUnique_isGalerkinSolution_laplace`),
and no regularity theory enters, so the Hille–Yosida theory of chapter 7 applies at once. The
regularity theorem 9.25 (`Elliptic.regularity_dirichlet`) enters exactly once, as the
identification `D(A) = H²(Ω) ∩ H¹₀(Ω)` with the graph-norm estimate on a `C²` domain with bounded
boundary (`dirichletLaplacianDomain_eq_of_isContDiffChartDomain`), and, iterated with the
higher-order clause (`Elliptic.regularity_dirichlet_higher_mem`), as the continuous injection
`D(A^ℓ) ↪ H^{2ℓ}(Ω)` (`dirichletLaplacian.powDomainToSobolevL`), the book's (7). Conversely
`H²(Ω) ∩ H¹₀(Ω) ⊆ D(A)` on every open set (`mem_dirichletLaplacianDomain_of_sobolev_two`).

`D(A^ℓ)` is chapter 7's Hilbert space `LinearPMap.PowDomain A ℓ`; "`u ∈ D(A^ℓ)`" is
`∃ x : A.PowDomain ℓ, applyL A ℓ 0 x = u`. The passage from chapter 7's `C^k(s; D(A^ℓ))` lifts to
the Bochner classes `C^k(s; H^{2ℓ}(Ω))` is `Bochner.ContDiffOnThrough.of_contDiffOnPowDomain`.

Also here: the same operator considered in the Hilbert space `H¹₀(Ω)` (the book's `A₁` in the
proof of Theorem 10.2 (a), `dirichletLaplacianH10`), maximal monotone and symmetric there on any
open set.

## References

[brezis2011functional], §10.1, the proof of Theorem 10.1 (claims (i)–(iii) and (7)) and of
Theorem 10.2 (a).
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex Elliptic

/-! ### Continuous linear functionals agreeing on the test functions agree on `H¹₀` -/

/-- **Two continuous linear functionals on `H¹(Ω)` agreeing on the test-function elements agree on
`H¹₀(Ω)`**: `H¹₀(Ω)` is the closure of the test functions, and the set where two continuous maps
agree is closed. -/
theorem SobolevEuclideanZero.ext_on_testFunctions {L₁ L₂ : SobolevEuclidean N 1 2 Ω →L[ℝ] ℝ}
    (h : ∀ φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      L₁ φ = L₂ φ)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) : L₁ φ = L₂ φ := by
  have := Elliptic.apply_eq_zero_of_forall_testFunctions (L := L₁ - L₂)
    (fun ψ hψ ↦ by rw [sub_apply, h ψ hψ, sub_self]) hφ
  rwa [sub_apply, sub_eq_zero] at this

/-! ### The domain `{u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}` -/

variable (Ω) in
/-- **The domain of the Dirichlet Laplacian**: the `L²(Ω)` functions `f` that are the function of
some `v ∈ H¹₀(Ω)` whose weak Laplacian lies in `L²(Ω)`, that is, for which there is `g ∈ L²(Ω)`
with `∫_Ω ∇v · ∇φ = ∫_Ω g φ` for every `φ ∈ H¹₀(Ω)` (`A f = g`, the book's `-Δf = g`). A
submodule: the witnesses add and scale. -/
def dirichletLaplacianDomain :
    Submodule ℝ (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) where
  carrier := {f | ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
    ∃ g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ}
  zero_mem' := ⟨0, Submodule.zero_mem _, map_zero _, 0, fun φ _ ↦ by
    rw [map_zero, zero_apply, load_apply_inner, inner_zero_left]⟩
  add_mem' := by
    rintro f₁ f₂ ⟨v₁, hv₁, hf₁, g₁, hg₁⟩ ⟨v₂, hv₂, hf₂, g₂, hg₂⟩
    refine ⟨v₁ + v₂, add_mem hv₁ hv₂, by rw [map_add, hf₁, hf₂], g₁ + g₂, fun φ hφ ↦ ?_⟩
    rw [dirichletForm_add_left, load_add, hg₁ φ hφ, hg₂ φ hφ]
  smul_mem' := by
    rintro c f ⟨v, hv, hf, g, hg⟩
    refine ⟨c • v, Submodule.smul_mem _ c hv, by rw [map_smul, hf], c • g, fun φ hφ ↦ ?_⟩
    rw [dirichletForm_smul_left, load_smul, hg φ hφ]

/-- Membership of the domain of the Dirichlet Laplacian, unfolded. -/
theorem mem_dirichletLaplacianDomain_iff
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} :
    f ∈ dirichletLaplacianDomain Ω ↔ ∃ v : SobolevEuclidean N 1 2 Ω,
      v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
      ∃ g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ :=
  Iff.rfl

/-- **The weak Laplacian is unique**: two `L²(Ω)` functions with the same loads on `H¹₀(Ω)` are
equal, the test functions being dense in `L²(Ω)` (`SobolevEuclideanZero.toDualL2_injective`). -/
theorem eq_of_forall_load_eq
    {g₁ g₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, load Ω g₁ φ = load Ω g₂ φ) : g₁ = g₂ := by
  refine SobolevEuclideanZero.toDualL2_injective (ContinuousLinearMap.ext fun v ↦ ?_)
  exact h v v.2

/-- **The `H¹₀`-lift is unique**: the inclusion `H¹₀(Ω) → L²(Ω)` is injective. -/
theorem eq_of_fnL_eq {v₁ v₂ : SobolevEuclidean N 1 2 Ω}
    (h : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₁
      = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₂) : v₁ = v₂ :=
  SobolevMultiIndex.fnL_injective h

/-! ### The operator -/

variable (Ω) in
/-- The value of the Dirichlet Laplacian on an `L²(Ω)` function: the weak Laplacian `g` of the
definition of the domain, chosen, and `0` off the domain. -/
def dirichletLaplacianApply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  open Classical in
  if hf : f ∈ dirichletLaplacianDomain Ω then Classical.choose (Classical.choose_spec hf).2.2
  else 0

/-- The defining property of `dirichletLaplacianApply` on the domain. -/
theorem dirichletLaplacianApply_spec
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hf : f ∈ dirichletLaplacianDomain Ω) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f ∧
      ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω,
        dirichletForm Ω v φ = load Ω (dirichletLaplacianApply Ω f) φ := by
  refine ⟨Classical.choose hf, (Classical.choose_spec hf).1, (Classical.choose_spec hf).2.1, ?_⟩
  unfold dirichletLaplacianApply
  rw [dite_eq_left hf]
  exact Classical.choose_spec (Classical.choose_spec hf).2.2

/-- **Any weak Laplacian of `f` is the value of the operator**: for `v ∈ H¹₀(Ω)` with `fnL v = f`
and `g ∈ L²(Ω)` with `∫ ∇v · ∇φ = ∫ g φ` on `H¹₀(Ω)`, `g = dirichletLaplacianApply Ω f`. -/
theorem eq_dirichletLaplacianApply
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ) :
    g = dirichletLaplacianApply Ω f := by
  have hf : f ∈ dirichletLaplacianDomain Ω := ⟨v, hv, hvf, g, hg⟩
  obtain ⟨v', hv', hv'f, hg'⟩ := dirichletLaplacianApply_spec hf
  obtain rfl : v' = v := eq_of_fnL_eq (hv'f.trans hvf.symm)
  exact eq_of_forall_load_eq fun φ hφ ↦ (hg φ hφ).symm.trans (hg' φ hφ)

/-- `dirichletLaplacianApply` is additive on the domain. -/
theorem dirichletLaplacianApply_add
    {f₁ f₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h₁ : f₁ ∈ dirichletLaplacianDomain Ω) (h₂ : f₂ ∈ dirichletLaplacianDomain Ω) :
    dirichletLaplacianApply Ω (f₁ + f₂)
      = dirichletLaplacianApply Ω f₁ + dirichletLaplacianApply Ω f₂ := by
  obtain ⟨v₁, hv₁, hf₁, hg₁⟩ := dirichletLaplacianApply_spec h₁
  obtain ⟨v₂, hv₂, hf₂, hg₂⟩ := dirichletLaplacianApply_spec h₂
  refine (eq_dirichletLaplacianApply (v := v₁ + v₂) (add_mem hv₁ hv₂)
    (by rw [map_add, hf₁, hf₂]) fun φ hφ ↦ ?_).symm
  rw [dirichletForm_add_left, load_add, hg₁ φ hφ, hg₂ φ hφ]

/-- `dirichletLaplacianApply` is homogeneous on the domain. -/
theorem dirichletLaplacianApply_smul (c : ℝ)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : f ∈ dirichletLaplacianDomain Ω) :
    dirichletLaplacianApply Ω (c • f) = c • dirichletLaplacianApply Ω f := by
  obtain ⟨v, hv, hf, hg⟩ := dirichletLaplacianApply_spec h
  refine (eq_dirichletLaplacianApply (v := c • v) (Submodule.smul_mem _ c hv)
    (by rw [map_smul, hf]) fun φ hφ ↦ ?_).symm
  rw [dirichletForm_smul_left, load_smul, hg φ hφ]

/-- `dirichletLaplacianApply` vanishes at `0`. -/
theorem dirichletLaplacianApply_zero : dirichletLaplacianApply Ω 0 = 0 :=
  (eq_dirichletLaplacianApply (v := 0) (Submodule.zero_mem _)
    (map_zero (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)) fun φ _ ↦ by
      rw [map_zero, zero_apply, load_apply_inner, inner_zero_left]).symm

variable (Ω) in
/-- **The Dirichlet Laplacian** `A = -Δ` on `L²(Ω)`, as an unbounded operator (Mathlib's
`LinearPMap`) with domain `dirichletLaplacianDomain Ω = {u ∈ H¹₀(Ω) : Δu ∈ L²(Ω)}` and
`A u = g` the weak Laplacian, `∫_Ω ∇u · ∇φ = ∫_Ω (A u) φ` for all `φ ∈ H¹₀(Ω)`
([brezis2011functional], proof of Theorem 10.1). On a `C²` domain with bounded boundary the
domain is `H²(Ω) ∩ H¹₀(Ω)` (`dirichletLaplacianDomain_eq_of_isContDiffChartDomain`); on an
arbitrary open set it is the Friedrichs extension, on which the book's three claims (i)–(iii)
hold without any regularity of `Ω`. -/
def dirichletLaplacian : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →ₗ.[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) where
  domain := dirichletLaplacianDomain Ω
  toFun :=
    { toFun := fun f ↦ dirichletLaplacianApply Ω f
      map_add' := fun f₁ f₂ ↦ dirichletLaplacianApply_add f₁.2 f₂.2
      map_smul' := fun c f ↦ dirichletLaplacianApply_smul c f.2 }

/-- The domain of the Dirichlet Laplacian is `dirichletLaplacianDomain Ω`. -/
@[simp]
theorem dirichletLaplacian_domain : (dirichletLaplacian Ω).domain = dirichletLaplacianDomain Ω :=
  rfl

/-- The value of the Dirichlet Laplacian is `dirichletLaplacianApply`. -/
theorem dirichletLaplacian_apply (f : (dirichletLaplacian Ω).domain) :
    dirichletLaplacian Ω f = dirichletLaplacianApply Ω f :=
  rfl

/-- **`A f` is the only weak Laplacian of `f`**: for `v ∈ H¹₀(Ω)` with `fnL v = f` and `g` with
`∫ ∇v · ∇φ = ∫ g φ` on `H¹₀(Ω)`, `A f = g`. -/
theorem dirichletLaplacian_apply_unique (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, dirichletForm Ω v φ = load Ω g φ) :
    dirichletLaplacian Ω f = g :=
  (eq_dirichletLaplacianApply hv hvf hg).symm

/-- **The defining identity, in usable form**: for `f ∈ D(A)` with `H¹₀`-lift `v` (`fnL v = f`)
and every `φ ∈ H¹₀(Ω)`, `⟪A f, fnL φ⟫ = ∫_Ω ∇v · ∇φ`. -/
theorem dirichletLaplacian_inner_eq_dirichletForm (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f)
    {φ : SobolevEuclidean N 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero N 1 2 Ω) :
    ⟪dirichletLaplacian Ω f, fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ
      = dirichletForm Ω v φ := by
  obtain ⟨v', hv', hv'f, hg'⟩ := dirichletLaplacianApply_spec f.2
  obtain rfl : v' = v := eq_of_fnL_eq (hv'f.trans hvf.symm)
  rw [dirichletLaplacian_apply]
  exact (hg' φ hφ).symm

/-- Every `f ∈ D(A)` has an `H¹₀`-lift. -/
theorem dirichletLaplacian_exists_lift (f : (dirichletLaplacian Ω).domain) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f := by
  obtain ⟨v, hv, hvf, -⟩ := dirichletLaplacianApply_spec f.2
  exact ⟨v, hv, hvf⟩

/-- **`⟪A f, f⟫ = ∫_Ω |∇f|²`**: the book's `(Au, u) = ∫ |∇u|²`, for the `H¹₀`-lift `v` of `f`. -/
theorem dirichletLaplacian_inner_self_eq_dirichletForm (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    ⟪dirichletLaplacian Ω f, (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ
      = dirichletForm Ω v v := by
  rw [← hvf]
  exact dirichletLaplacian_inner_eq_dirichletForm f hv hvf hv

/-- **(i) `A` is monotone**: `0 ≤ ⟪A f, f⟫` for every `f ∈ D(A)` ([brezis2011functional], proof
of Theorem 10.1, (i)). -/
theorem dirichletLaplacian_inner_self_nonneg (f : (dirichletLaplacian Ω).domain) :
    0 ≤ ⟪dirichletLaplacian Ω f,
      (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  rw [dirichletLaplacian_inner_self_eq_dirichletForm f hv hvf]
  exact dirichletForm_self_nonneg Ω v

/-- **The Dirichlet Laplacian is monotone** in the sense of chapter 7. -/
theorem dirichletLaplacian_isMonotone : (dirichletLaplacian Ω).IsMonotone := fun f ↦ by
  simpa using dirichletLaplacian_inner_self_nonneg f

/-- **(iii) `A` is symmetric**: `⟪A f, g⟫ = ⟪f, A g⟫` for `f, g ∈ D(A)`, both sides being
`∫_Ω ∇f · ∇g` ([brezis2011functional], proof of Theorem 10.1, (iii)). -/
theorem dirichletLaplacian_isFormalAdjoint :
    (dirichletLaplacian Ω).IsFormalAdjoint (dirichletLaplacian Ω) := fun f g ↦ by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨w, hw, hwg⟩ := dirichletLaplacian_exists_lift g
  rw [← hwg, dirichletLaplacian_inner_eq_dirichletForm f hv hvf hw, real_inner_comm, ← hvf,
    dirichletLaplacian_inner_eq_dirichletForm g hw hwg hv]
  exact (dirichletForm_isHermitian Ω w v).symm.trans (by simp)

/-! ### Maximality: `R(λ I + A) = L²(Ω)` -/

/-- **(ii) `R(I + A) = L²(Ω)`** ([brezis2011functional], proof of Theorem 10.1, (ii)): for every
`f ∈ L²(Ω)` there is `u ∈ D(A)` with `u + A u = f`. The Dirichlet principle (Theorem 9.21,
`Elliptic.existsUnique_isGalerkinSolution_laplace`) gives `v ∈ H¹₀(Ω)` with
`∫ ∇v · ∇φ + ∫ v φ = ∫ f φ` on `H¹₀(Ω)`, so `u = fnL v ∈ D(A)` with `A u = f − u`. No regularity
of `Ω` is needed on the weak domain. -/
theorem dirichletLaplacian_exists_add_apply_eq
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u : (dirichletLaplacian Ω).domain,
      (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) + dirichletLaplacian Ω u
        = f := by
  obtain ⟨v, hv⟩ := (existsUnique_isGalerkinSolution_laplace Ω f).exists
  have heq := dirichletForm_eq_load_sub_of_isGalerkinSolution_laplace hv
  have hmem : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω := ⟨v, hv.1, rfl, f - weakDeriv v 0, heq⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [dirichletLaplacian_apply_unique ⟨_, hmem⟩ hv.1 rfl heq]
  change fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v + (f - weakDeriv v 0) = f
  rw [fnL_eq_weakDeriv_zero]
  abel

/-- **The Dirichlet Laplacian is maximal monotone** on every open set ([brezis2011functional],
proof of Theorem 10.1, (i) and (ii)). -/
theorem dirichletLaplacian_isMaximalMonotone : (dirichletLaplacian Ω).IsMaximalMonotone :=
  ⟨dirichletLaplacian_isMonotone, dirichletLaplacian_exists_add_apply_eq⟩

/-- **`R(λ I + A) = L²(Ω)` for every `λ > 0`**: for every `f ∈ L²(Ω)` there is `u ∈ D(A)` with
`λ u + A u = f` (chapter 7's Proposition 7.1 (c) applied to the maximal monotone `A`). -/
theorem dirichletLaplacian_exists_smul_add_apply_eq {c : ℝ} (hc : 0 < c)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u : (dirichletLaplacian Ω).domain,
      c • (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacian Ω u = f := by
  obtain ⟨u, hu⟩ := dirichletLaplacian_isMaximalMonotone.exists_add_smul_eq (inv_pos.2 hc)
    (c⁻¹ • f)
  refine ⟨u, ?_⟩
  have := congrArg (fun z ↦ c • z) hu
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at this
  simpa [mul_inv_cancel₀ hc.ne'] using this

/-- The book's spelling of the range condition: `R(λ I + A) = L²(Ω)` for `λ > 0`, with
Mathlib's `+ᵥ` of a linear map on a partial map. -/
theorem dirichletLaplacian_range_smul_id_vadd_eq_top {c : ℝ} (hc : 0 < c) :
    LinearMap.range ((c • (LinearMap.id :
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) →ₗ[ℝ]
        Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))) +ᵥ
        dirichletLaplacian Ω).toFun = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro f
  obtain ⟨u, hu⟩ := dirichletLaplacian_exists_smul_add_apply_eq hc f
  exact ⟨u, hu⟩

/-- The Dirichlet Laplacian is a closed operator (chapter 7's Proposition 7.1). -/
theorem dirichletLaplacian_isClosed : (dirichletLaplacian Ω).IsClosed :=
  dirichletLaplacian_isMaximalMonotone.isClosed

/-- The domain of the Dirichlet Laplacian is dense in `L²(Ω)` (chapter 7's Proposition 7.1). -/
theorem dirichletLaplacian_dense_domain :
    Dense ((dirichletLaplacian Ω).domain :
      Set (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))) :=
  dirichletLaplacian_isMaximalMonotone.dense_domain

/-- **The Dirichlet Laplacian is self-adjoint** (Mathlib's `IsSelfAdjoint` for
`LinearPMap.adjoint`): Proposition 7.6 applied to the symmetric maximal monotone `A`
([brezis2011functional], proof of Theorem 10.1, (iii)). This is the hypothesis of Theorem 7.7
that makes every `u₀ ∈ L²(Ω)` an admissible datum for the heat equation. -/
theorem dirichletLaplacian_isSelfAdjoint : IsSelfAdjoint (dirichletLaplacian Ω) :=
  dirichletLaplacian_isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint
    dirichletLaplacian_isFormalAdjoint

/-! ### The `H¹₀`-lift of `D(A)` as a bounded operator -/

section SobolevZeroLift

open LinearPMap LinearPMap.PowDomain

/-- Every `f ∈ D(A)` has an `H¹₀`-lift, as an element of the type `H¹₀(Ω)`. -/
theorem dirichletLaplacian_exists_sobolevZero_lift (f : (dirichletLaplacian Ω).domain) :
    ∃ v : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
        = f := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  exact ⟨⟨v, hv⟩, hvf⟩

variable (Ω) in
/-- **The `H¹₀`-lift `D(A) → H¹₀(Ω)` as a bounded linear map** on the Hilbert space `D(A)` with
the graph norm (`PowDomain 1`): `x ↦ v` with `fnL v = A^0 x`, continuous by the closed graph
theorem (`exists_continuousLinearMap_comp_eq_of_injective`); `fnL_sobolevZeroLiftL` is its
defining property. It turns the semigroup lifts into `H¹₀`-valued curves. -/
def dirichletLaplacian.sobolevZeroLiftL :
    (dirichletLaplacian Ω).PowDomain 1 →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain 1) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain 1
  Classical.choose (exists_continuousLinearMap_comp_eq_of_injective
    (J := SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective (S := applyL (dirichletLaplacian Ω) 1 0)
    fun x ↦ dirichletLaplacian_exists_sobolevZero_lift ⟨_, applyL_mem_domain x 0⟩)

/-- The function of `sobolevZeroLiftL x` is `A^0 x`. -/
theorem fnL_sobolevZeroLiftL (x : (dirichletLaplacian Ω).PowDomain 1) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacian.sobolevZeroLiftL Ω x) = applyL (dirichletLaplacian Ω) 1 0 x :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain 1) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain 1
  Classical.choose_spec (exists_continuousLinearMap_comp_eq_of_injective
    (J := SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective (S := applyL (dirichletLaplacian Ω) 1 0)
    fun x ↦ dirichletLaplacian_exists_sobolevZero_lift ⟨_, applyL_mem_domain x 0⟩) x

/-- **The `H¹` norm of an `H¹₀`-lift of `f ∈ D(A)`**: `‖v‖²_{H¹} = ‖f‖² + ⟪A f, f⟫`
(`‖v‖² = ‖v‖₂² + ∫ |∇v|²`, `laplaceForm_eq_innerSL`). -/
theorem dirichletLaplacian_norm_sq_lift_eq (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = f) :
    ‖v‖ ^ 2 = ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖ ^ 2
      + ⟪dirichletLaplacian Ω f,
        (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ := by
  have h1 : ‖v‖ ^ 2 = ‖(v : SobolevEuclidean N 1 2 Ω)‖ ^ 2 := by rw [Submodule.norm_coe]
  have h2 := Elliptic.norm_sq_eq Ω (v : SobolevEuclidean N 1 2 Ω)
  have h3 := dirichletForm_self_eq Ω (v : SobolevEuclidean N 1 2 Ω)
  have h4 := dirichletLaplacian_inner_self_eq_dirichletForm f v.2 hv
  have h5 : weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0 = f := hv
  have h5' : ‖weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0‖ ^ 2
      = ‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖ ^ 2 := by rw [h5]
  linarith

end SobolevZeroLift

/-! ### The `H¹₀`-preimage of an `L²` function -/

section ToSobolevZero


variable (Ω) in
/-- **The `H¹₀`-preimage of `v ∈ L²(Ω)`**: the element `w ∈ H¹₀(Ω)` with `fnL w = v` when there is
one (it is then unique, `SobolevMultiIndexZero.fnL_injective`), and `0` otherwise. -/
def toSobolevZero (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    SobolevEuclideanZero N 1 2 Ω :=
  open Classical in
  if h : ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v
  then h.choose else 0

/-- `fnL (toSobolevZero v) = v` when `v` lies in `H¹₀(Ω)`. -/
theorem fnL_toSobolevZero {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hv : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω v) = v := by
  unfold toSobolevZero
  rw [dite_eq_left hv]
  exact hv.choose_spec

/-- `toSobolevZero (fnL w) = w`. -/
theorem toSobolevZero_fnL (w : SobolevEuclideanZero N 1 2 Ω) :
    toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume w) = w :=
  SobolevMultiIndexZero.fnL_injective (fnL_toSobolevZero ⟨w, rfl⟩)

/-- The preimage is unique: `toSobolevZero v = w` for any `w` with `fnL w = v`. -/
theorem toSobolevZero_eq {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {w : SobolevEuclideanZero N 1 2 Ω}
    (hw : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
      = v) : toSobolevZero Ω v = w := by
  rw [← hw, toSobolevZero_fnL]

/-- The preimage of a sum of two `H¹₀` functions. -/
theorem toSobolevZero_add {v₁ v₂ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h₁ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₁)
    (h₂ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = v₂) :
    toSobolevZero Ω (v₁ + v₂) = toSobolevZero Ω v₁ + toSobolevZero Ω v₂ :=
  toSobolevZero_eq (by rw [_root_.map_add, fnL_toSobolevZero h₁, fnL_toSobolevZero h₂])

/-- The preimage of a scalar multiple of an `H¹₀` function. -/
theorem toSobolevZero_smul (c : ℝ)
    {v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v) :
    toSobolevZero Ω (c • v) = c • toSobolevZero Ω v :=
  toSobolevZero_eq (by rw [_root_.map_smul, fnL_toSobolevZero h])

end ToSobolevZero

/-! ### `H²(Ω) ∩ H¹₀(Ω) ⊆ D(A)` on any open set -/

variable (Ω) in
/-- **The weak Laplacian on `H²(Ω)`**, `w ↦ ∑ᵢ ∂ᵢᵢ w`, as a bounded linear map `H²(Ω) → L²(Ω)`:
the sum of the components of `w` at the multi-indices `2 eᵢ`. -/
def sobolevLaplacianL : SobolevEuclidean N 2 2 Ω →L[ℝ]
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  ∑ i : Fin N, weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume
    (MultiIndexLE.addSingle i (MultiIndexLE.single i))

/-- The weak Laplacian of `w ∈ H²(Ω)` is `∑ᵢ ∂ᵢᵢ w`, the components at `2 eᵢ`. -/
theorem sobolevLaplacianL_apply (w : SobolevEuclidean N 2 2 Ω) :
    sobolevLaplacianL Ω w
      = ∑ i : Fin N, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) := by
  simp only [sobolevLaplacianL, sum_apply, weakDerivL_apply]

/-- **`H²(Ω) ∩ H¹₀(Ω) ⊆ D(A)` on any open set, with `A f = −∑ᵢ ∂ᵢᵢ f`**: if `w ∈ H²(Ω)` and
`v ∈ H¹₀(Ω)` have the same function, then `f = fnL v` lies in `D(A)` and `A f` is minus the weak
Laplacian of `w` (`sobolevLaplacianL Ω w`). For a test function `φ`, `∫ ∂ᵢv ∂ᵢφ = −∫ ∂ᵢᵢw φ` is
the weak-derivative identity of the `H²` element (the first derivatives of `w` and `v` agree by
uniqueness of weak derivatives), and the identity extends from the test functions to `H¹₀(Ω)`
(`Elliptic.dirichletForm_eq_load_of_forall_testFunctions`). This is the inclusion that makes
the book's uniqueness class `C((0,∞); H² ∩ H¹₀)` a subclass of the weak one. -/
theorem mem_dirichletLaplacianDomain_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω
      ∧ dirichletLaplacianApply Ω (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
        = -sobolevLaplacianL Ω w := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  -- the first derivatives of `v` are the functions of the `∂ᵢ w ∈ H¹(Ω)`
  have hd : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) := by
    intro i
    have h1 := (weakDeriv_hasWeakIteratedLineDerivOn_single v i).congr_ae hvw
      (EventuallyEq.refl _ _)
    have h2 := hasWeakIteratedLineDerivOn_fn_partialDeriv i w
    rw [EuclideanSpace.basisFun_toBasis_apply] at h2
    exact (ae_restrict_iff' hΩm).2 (h1.ae_eq h2)
  -- the datum, as a function
  have hg : ⇑(-sobolevLaplacianL Ω w) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ -∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x := by
    rw [sobolevLaplacianL_apply]
    filter_upwards [Lp.coeFn_neg
      (∑ i, weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))),
      Lp.coeFn_finsetSum Finset.univ
        fun i ↦ weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i))] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply]
  -- the equation against test functions
  have heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω v Φ = load Ω (-sobolevLaplacianL Ω w) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq hd hψ, load_apply_eq_of_ae_eq hg hψ]
    have hterm : ∀ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) x
          * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x := by
      intro i
      have key := (weakDeriv_hasWeakIteratedLineDerivOn_single
        (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) i)
        |>.integral_fderiv_mul_eq_of_eqOn ψ (fun _ _ ↦ rfl)
      rw [weakDeriv_partialDeriv] at key
      calc ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) x
              * fderiv ℝ ψ x (EuclideanSpace.single i 1)
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              fderiv ℝ ψ x (EuclideanSpace.single i 1)
                * fn (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w)
                  x :=
            integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              ψ x * weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x := key
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x := by
            congr 1
            exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    simp only [hterm, Finset.sum_neg_distrib]
    have hI : ∀ i, Integrable
        (fun x ↦ weakDeriv w (MultiIndexLE.addSingle i (MultiIndexLE.single i)) x * ψ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
      have := ((weakDeriv_hasWeakIteratedLineDerivOn_single
        (partialDeriv ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 Ω volume i w) i)
        |>.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      rw [weakDeriv_partialDeriv] at this
      exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [← integral_finsetSum _ fun i _ ↦ hI i, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [Finset.sum_mul, neg_mul])
  have heq' : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω v φ = load Ω (-sobolevLaplacianL Ω w) φ := fun φ hφ ↦
    dirichletForm_eq_load_of_forall_testFunctions heq hφ
  exact ⟨⟨v, hv, rfl, _, heq'⟩, (eq_dirichletLaplacianApply hv rfl heq').symm⟩

/-- **`H²(Ω) ∩ H¹₀(Ω) ⊆ D(A)`**, the membership alone. -/
theorem fnL_mem_dirichletLaplacianDomain_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω :=
  (mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw).1

/-- **`A f = −∑ᵢ ∂ᵢᵢ w` for `f ∈ H²(Ω) ∩ H¹₀(Ω)`.** -/
theorem dirichletLaplacian_apply_of_sobolev_two (w : SobolevEuclidean N 2 2 Ω)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w)
    (f : (dirichletLaplacian Ω).domain)
    (hf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  rw [dirichletLaplacian_apply, ← hf]
  exact (mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw).2

/-! ### Test functions lie in every `D(A^ℓ)` -/

/-- The classical second derivatives `∂ᵢ∂ᵢ φ` of a test function are the components at `2 eᵢ`
of any `H²(Ω)` element with function `φ`. -/
theorem weakDeriv_addSingle_ae_eq_of_testFunction (φ : 𝓓(Ω, ℝ)) {u : SobolevEuclidean N 2 2 Ω}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] φ) (i : Fin N) :
    ⇑(weakDeriv u (MultiIndexLE.addSingle i (MultiIndexLE.single i)))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin N))) := Ω.isOpen.measurableSet
  have hφ1 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (φ : EuclideanSpace ℝ (Fin N) → ℝ) (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      Ω volume :=
    (φ.contDiff.contDiffOn.of_le (by simp)).hasWeakIteratedLineDerivOn_single Ω i
  have hdφ : ContDiff ℝ ∞ fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (φ.contDiff.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hφ2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1]
      (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))
      (fun x ↦ fderiv ℝ (fun z ↦ fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) Ω volume :=
    (hdφ.contDiffOn.of_le (by simp)).hasWeakIteratedLineDerivOn_single Ω i
  -- the first derivative of `u` along `eᵢ` is `∂ᵢ φ`
  have h1 := (hasWeakIteratedLineDerivOn_single u i).congr_ae hu (EventuallyEq.refl _ _)
  rw [EuclideanSpace.basisFun_toBasis_apply] at h1
  have e1 : ⇑(weakDeriv u (MultiIndexLE.singleLE i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (ae_restrict_iff' hΩm).2 (h1.ae_eq hφ1)
  -- the second derivative
  have h2 := ((hasWeakIteratedLineDerivOn_addSingle u i (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
      Fin N → EuclideanSpace ℝ (Fin N)) i)).congr_ae e1 (EventuallyEq.refl _ _)
  rw [EuclideanSpace.basisFun_toBasis_apply] at h2
  exact (ae_restrict_iff' hΩm).2 (h2.ae_eq hφ2)

/-- **Every test function lies in `D(A)`, with `A φ = −Δφ`** ([brezis2011functional], the
`C_c^∞(Ω)` data of Theorem 10.2 (c) and Corollary 10.5): the `H²` and `H¹₀` elements of `φ`
with `mem_dirichletLaplacianDomain_of_sobolev_two`, whose weak second derivatives are the
classical ones. -/
theorem testFunction_mem_dirichletLaplacianDomain (φ : 𝓓(Ω, ℝ)) :
    φ.toL2 ∈ dirichletLaplacianDomain Ω ∧
      dirichletLaplacianApply Ω φ.toL2 = φ.negLaplacian.toL2 := by
  obtain ⟨u₂, -, hu₂φ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 2) (p := 2) (μ := volume)
  obtain ⟨u₁, hu₁, hu₁φ⟩ := φ.exists_mem_sobolevMultiIndex_testFunctions
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := 1) (p := 2) (μ := volume)
  have hv : u₁ ∈ SobolevEuclideanZero N 1 2 Ω := SobolevMultiIndexZero.testFunctions_le hu₁
  obtain ⟨hmem, happ⟩ := mem_dirichletLaplacianDomain_of_sobolev_two u₂ hv
    (hu₁φ.trans hu₂φ.symm)
  have e1 : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₁ = φ.toL2 :=
    Lp.ext (hu₁φ.trans φ.coeFn_toL2.symm)
  have e2 : -sobolevLaplacianL Ω u₂ = φ.negLaplacian.toL2 := by
    refine Lp.ext ?_
    rw [sobolevLaplacianL_apply]
    have hsum := Lp.coeFn_finsetSum Finset.univ
      fun i ↦ weakDeriv u₂ (MultiIndexLE.addSingle i (MultiIndexLE.single i))
    filter_upwards [Lp.coeFn_neg
      (∑ i, weakDeriv u₂ (MultiIndexLE.addSingle i (MultiIndexLE.single i))),
      hsum, φ.negLaplacian.coeFn_toL2,
      ae_all_iff.2 fun i ↦ weakDeriv_addSingle_ae_eq_of_testFunction φ hu₂φ i]
      with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply, hx3, TestFunction.negLaplacian_coe]
    simp only [hx4]
  rw [e1] at hmem happ
  exact ⟨hmem, happ.trans e2⟩

/-- Consecutive iterates `(−Δ)^j φ`, `(−Δ)^{j+1} φ` of a test function are related by `A`. -/
theorem testFunction_iterate_negLaplacian_chain (φ : 𝓓(Ω, ℝ)) (j : ℕ) :
    ∃ h : (TestFunction.negLaplacian^[j] φ).toL2 ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨(TestFunction.negLaplacian^[j] φ).toL2, h⟩
        = (TestFunction.negLaplacian^[j + 1] φ).toL2 := by
  refine ⟨(testFunction_mem_dirichletLaplacianDomain _).1, ?_⟩
  rw [dirichletLaplacian_apply, (testFunction_mem_dirichletLaplacianDomain _).2,
    Function.iterate_succ_apply']

/-- **Every test function lies in every `D(A^ℓ)`**, with `A^j φ = (−Δ)^j φ`: the tuple
`(φ, −Δφ, (−Δ)²φ, …)` of `L²` classes of test functions is an element of `D(A^ℓ)`
(`LinearPMap.PowDomain.mk`), consecutive entries being related by `A` by
`testFunction_mem_dirichletLaplacianDomain`. -/
theorem testFunction_exists_powDomain (φ : 𝓓(Ω, ℝ)) (ℓ : ℕ) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, ∀ j : Fin (ℓ + 1),
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ j x
        = (TestFunction.negLaplacian^[j] φ).toL2 := by
  have hchain : ∀ i : Fin ℓ, ∃ h : (fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2)
      i.castSucc ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨(fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2)
        i.castSucc, h⟩ = (fun j : Fin (ℓ + 1) ↦ (TestFunction.negLaplacian^[j] φ).toL2) i.succ := by
    intro i
    obtain ⟨h, hh⟩ := testFunction_iterate_negLaplacian_chain φ i
    exact LinearPMap.PowDomain.exists_apply_eq_of_eq h hh (by simp) (by simp)
  exact ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) _ hchain, fun j ↦
    LinearPMap.PowDomain.applyL_mk _ _ j⟩

/-! ### `D(A) = H²(Ω) ∩ H¹₀(Ω)` on a `C²` domain with bounded boundary -/

/-- **The `H¹₀`-lift of `f ∈ D(A)` is the weak solution of `−Δv + v = f + A f`**: for `v ∈ H¹₀(Ω)`
with `fnL v = f`, `v` is the Galerkin solution of the form of `−Δ + 1` with datum `f + A f` on
`H¹₀(Ω)` — the book's (48) in the proof of Theorem 10.1. -/
theorem dirichletLaplacian_isGalerkinSolution_laplace (f : (dirichletLaplacian Ω).domain)
    {v : SobolevEuclidean N 1 2 Ω} (hv : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hvf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    IsGalerkinSolution (laplaceForm Ω) (load Ω ((f : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N))))) + dirichletLaplacian Ω f))
      (SobolevEuclideanZero N 1 2 Ω) v := by
  refine ⟨hv, fun φ hφ ↦ ?_⟩
  have h1 := laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω v φ
  have h2 := dirichletLaplacian_inner_eq_dirichletForm f hv hvf hφ
  rw [fnL_eq_weakDeriv_zero] at h2
  have h3 : load Ω ((f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      + dirichletLaplacian Ω f) φ
      = ⟪(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
          weakDeriv φ 0⟫_ℝ + ⟪dirichletLaplacian Ω f, weakDeriv φ 0⟫_ℝ := by
    rw [load_add, load_apply_inner, load_apply_inner]
  have h4 : weakDeriv v 0 = f := (fnL_eq_weakDeriv_zero v).symm.trans hvf
  rw [h4] at h1
  rw [h1, h3, h2, add_comm]

/-- **`D(A) ⊆ H²(Ω)` from the regularity theorem, with the graph-norm estimate**: if every weak
solution `u ∈ H¹₀(Ω)` of `−Δu + u = g` lies in `H²(Ω)` with `‖U‖_{H²} ≤ C ‖g‖` (the conclusion
of Theorem 9.25, `Elliptic.regularity_dirichlet`), then every `f ∈ D(A)` is the function of some
`w ∈ H²(Ω)`, and every such `w` has `‖w‖_{H²} ≤ C (‖f‖ + ‖A f‖)`: the `H¹₀`-lift of `f` solves
`−Δv + v = f + A f`. -/
theorem dirichletLaplacian_exists_sobolev_two_of_forall {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
      (u : SobolevEuclidean N 1 2 Ω),
      IsGalerkinSolution (laplaceForm Ω) (load Ω g) (SobolevEuclideanZero N 1 2 Ω) u →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fn u) 2 2 Ω volume ∧
      ∀ U : SobolevEuclidean N 2 2 Ω,
        fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn u → ‖U‖ ≤ C * ‖g‖)
    (f : (dirichletLaplacian Ω).domain) :
    (∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f) ∧
    ∀ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f →
      ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))‖
        + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  obtain ⟨hmem, hbound⟩ := hC _ v (dirichletLaplacian_isGalerkinSolution_laplace f hv hvf)
  refine ⟨?_, fun w hwf ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hmem.exists_sobolevMultiIndex
    refine ⟨w, Lp.ext (hw.trans ?_)⟩
    rw [← hvf]
    rfl
  · have hwv : fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn v :=
      Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
        (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
        (hwf.trans hvf.symm))
    exact (hbound w hwv).trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hC0)

/-- **`D(A) ⊆ H²(Ω)` on a `C²` domain with bounded boundary**, with the graph-norm estimate:
there is `C` such that every `f ∈ D(A)` is the function of some `w ∈ H²(Ω)`, and every such `w`
has `‖w‖_{H²} ≤ C (‖f‖ + ‖A f‖)` — Theorem 9.25 (`Elliptic.regularity_dirichlet`) applied to the
`H¹₀`-lift of `f`, which solves `−Δv + v = f + A f`. -/
theorem dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (dirichletLaplacian Ω).domain,
      (∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f) ∧
      ∀ w : SobolevEuclidean (d + 1) 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f →
        ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖
          + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨C, hC0, hC⟩ := regularity_dirichlet hΩ hΓ
  exact ⟨C, hC0, fun f ↦ dirichletLaplacian_exists_sobolev_two_of_forall hC0 hC f⟩

/-- **`H²(Ω) ∩ H¹₀(Ω) ⊆ D(A)`**, for an `L²(Ω)` function given by its two lifts. -/
theorem mem_dirichletLaplacianDomain_of_exists_sobolev_two
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hw : ∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f)
    (hv : ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = f) :
    f ∈ dirichletLaplacianDomain Ω := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨v, hv, hvf⟩ := hv
  rw [← hvf]
  refine fnL_mem_dirichletLaplacianDomain_of_sobolev_two w hv ?_
  exact Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
    (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
    (hvf.trans hw.symm))

/-- **`D(A) = H²(Ω) ∩ H¹₀(Ω)` with the graph-norm estimate, on a `C²` domain with bounded
boundary** — [brezis2011functional] Theorem 9.25 read on the operator (the proof of Theorem
10.1). (a) `f ∈ D(A)` iff `f` is the function of an element of `H²(Ω)` and of an element of
`H¹₀(Ω)`: `⊇` is `mem_dirichletLaplacianDomain_of_sobolev_two`, and `⊆` is the regularity
theorem `Elliptic.regularity_dirichlet` applied to the `H¹₀`-lift `v` of `f`, which solves
`−Δv + v = f + A f` weakly; (b) a constant `C` with `‖w‖_{H²} ≤ C (‖f‖ + ‖A f‖)` for every
`f ∈ D(A)` and every `H²`-lift `w` of `f` — the continuous injection `D(A) ↪ H²(Ω)`, the graph
norm being `‖f‖ + ‖A f‖`. -/
theorem dirichletLaplacianDomain_eq_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∀ f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      f ∈ dirichletLaplacianDomain Ω ↔
        (∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f) ∧
        ∃ v : SobolevEuclidean (d + 1) 1 2 Ω, v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω ∧
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v = f) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (dirichletLaplacian Ω).domain) (w : SobolevEuclidean (d + 1) 2 2 Ω),
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f →
      ‖w‖ ≤ C * (‖(f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))‖
        + ‖dirichletLaplacian Ω f‖) := by
  obtain ⟨C, hC0, hC⟩ := dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain hΩ hΓ
  exact ⟨fun f ↦ ⟨fun hf ↦ ⟨(hC ⟨f, hf⟩).1, dirichletLaplacian_exists_lift ⟨f, hf⟩⟩,
    fun h ↦ mem_dirichletLaplacianDomain_of_exists_sobolev_two h.1 h.2⟩, C, hC0,
    fun f w hwf ↦ (hC f).2 w hwf⟩

/-! ### From chapter 7's lifts to Bochner lifts -/

/-- **A chapter-7 lift is a Bochner lift**: if `u : ℝ → H` has a `C^n` lift `v : ℝ → D(A^j)` on
`s` (`LinearPMap.ContDiffOnPowDomain`), then for bounded `J : D(A^j) →L V` and `K : V →L H`
with `K ∘ J` the inclusion `D(A^j) → H`, `u` is of class `C^n(s; V)` read through `K`
(`Bochner.ContDiffOnThrough K n u s`), with lift `J ∘ v`. Used with
`J = dirichletLaplacian.powDomainToSobolevL` and `K = SobolevMultiIndex.fnL` to turn the
`C^k([0,∞); D(A^ℓ))` clauses of the heat equation into `C^k([0,∞); H^{2ℓ}(Ω))`. -/
theorem Bochner.ContDiffOnThrough.of_contDiffOnPowDomain {H V : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V] {A : H →ₗ.[ℝ] H}
    {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ} (h : A.ContDiffOnPowDomain n j u s)
    (J : A.PowDomain j →L[ℝ] V) (K : V →L[ℝ] H)
    (hKJ : ∀ x, K (J x) = LinearPMap.PowDomain.applyL A j 0 x) :
    Bochner.ContDiffOnThrough K n u s := by
  obtain ⟨v, hv0, hv⟩ := h
  exact ⟨fun t ↦ J (v t), J.contDiff.comp_contDiffOn hv, fun t ht ↦ by rw [hKJ, hv0 t ht]⟩

/-! ### The Dirichlet Laplacian in `H¹₀(Ω)`, the book's `A₁` -/

variable (Ω) in
/-- The membership condition of the domain of the Dirichlet Laplacian in `H¹₀(Ω)`: `v ∈ H¹₀(Ω)`
with `fnL v ∈ D(A)` and `A (fnL v) ∈ H¹₀(Ω)`. -/
def MemDirichletLaplacianH10Domain (v : SobolevEuclideanZero N 1 2 Ω) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
      = dirichletLaplacianApply Ω
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)

/-- The membership condition of `D(A₁)` holds at `0`. -/
theorem memDirichletLaplacianH10Domain_zero : MemDirichletLaplacianH10Domain Ω 0 := by
  refine ⟨by rw [map_zero]; exact Submodule.zero_mem _, 0, ?_⟩
  rw [map_zero, dirichletLaplacianApply_zero]

/-- The membership condition of `D(A₁)` is closed under addition. -/
theorem MemDirichletLaplacianH10Domain.add {v₁ v₂ : SobolevEuclideanZero N 1 2 Ω}
    (h₁ : MemDirichletLaplacianH10Domain Ω v₁) (h₂ : MemDirichletLaplacianH10Domain Ω v₂) :
    MemDirichletLaplacianH10Domain Ω (v₁ + v₂) := by
  obtain ⟨h₁, w₁, hw₁⟩ := h₁
  obtain ⟨h₂, w₂, hw₂⟩ := h₂
  have e₁ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) v₁ v₂
  have e₂ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) w₁ w₂
  refine ⟨e₁ ▸ add_mem h₁ h₂, w₁ + w₂, ?_⟩
  exact (e₂.trans (congrArg₂ (· + ·) hw₁ hw₂)).trans
    ((dirichletLaplacianApply_add h₁ h₂).symm.trans (congrArg _ e₁.symm))

/-- The membership condition of `D(A₁)` is closed under scalar multiplication. -/
theorem MemDirichletLaplacianH10Domain.smul (c : ℝ) {v : SobolevEuclideanZero N 1 2 Ω}
    (h : MemDirichletLaplacianH10Domain Ω v) : MemDirichletLaplacianH10Domain Ω (c • v) := by
  obtain ⟨h, w, hw⟩ := h
  have e₁ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c v
  have e₂ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c w
  refine ⟨e₁ ▸ Submodule.smul_mem _ c h, c • w, ?_⟩
  exact (e₂.trans (congrArg (c • ·) hw)).trans
    ((dirichletLaplacianApply_smul c h).symm.trans (congrArg _ e₁.symm))

variable (Ω) in
/-- The domain of the Dirichlet Laplacian in `H¹₀(Ω)`: the `v ∈ H¹₀(Ω)` with `fnL v ∈ D(A)` and
`A (fnL v) ∈ H¹₀(Ω)` — the book's `{u ∈ H³ ∩ H¹₀ : Δu ∈ H¹₀}` once the regularity theorem
identifies the domains. -/
def dirichletLaplacianH10Domain : Submodule ℝ (SobolevEuclideanZero N 1 2 Ω) where
  carrier := {v | MemDirichletLaplacianH10Domain Ω v}
  zero_mem' := memDirichletLaplacianH10Domain_zero
  add_mem' := fun h₁ h₂ ↦ h₁.add h₂
  smul_mem' := fun c _ h ↦ h.smul c

/-- Membership of the domain of `A₁`, unfolded. -/
theorem mem_dirichletLaplacianH10Domain_iff {v : SobolevEuclideanZero N 1 2 Ω} :
    v ∈ dirichletLaplacianH10Domain Ω ↔
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
        ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = dirichletLaplacianApply Ω
          (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            v) :=
  Iff.rfl

variable (Ω) in
/-- The value of `A₁` on `v ∈ H¹₀(Ω)`: the `H¹₀`-preimage of `A (fnL v)`, chosen, and `0` off
the domain. -/
def dirichletLaplacianH10Apply (v : SobolevEuclideanZero N 1 2 Ω) : SobolevEuclideanZero N 1 2 Ω :=
  open Classical in
  if hv : v ∈ dirichletLaplacianH10Domain Ω then Classical.choose hv.2 else 0

/-- The defining property of `dirichletLaplacianH10Apply` on the domain. -/
theorem fnL_dirichletLaplacianH10Apply {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : v ∈ dirichletLaplacianH10Domain Ω) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacianH10Apply Ω v)
      = dirichletLaplacianApply Ω
        (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          v) := by
  unfold dirichletLaplacianH10Apply
  rw [dite_eq_left hv]
  exact Classical.choose_spec hv.2

/-- `dirichletLaplacianH10Apply` is additive on the domain. -/
theorem dirichletLaplacianH10Apply_add {v₁ v₂ : SobolevEuclideanZero N 1 2 Ω}
    (h₁ : v₁ ∈ dirichletLaplacianH10Domain Ω) (h₂ : v₂ ∈ dirichletLaplacianH10Domain Ω) :
    dirichletLaplacianH10Apply Ω (v₁ + v₂)
      = dirichletLaplacianH10Apply Ω v₁ + dirichletLaplacianH10Apply Ω v₂ := by
  have e₁ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) v₁ v₂
  have e₂ := map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) (dirichletLaplacianH10Apply Ω v₁) (dirichletLaplacianH10Apply Ω v₂)
  have h₁₂ : v₁ + v₂ ∈ dirichletLaplacianH10Domain Ω := add_mem h₁ h₂
  refine SobolevMultiIndexZero.fnL_injective ?_
  refine (fnL_dirichletLaplacianH10Apply h₁₂).trans ?_
  refine ((congrArg _ e₁).trans (dirichletLaplacianApply_add h₁.1 h₂.1)).trans ?_
  refine (congrArg₂ (· + ·) (fnL_dirichletLaplacianH10Apply h₁).symm
    (fnL_dirichletLaplacianH10Apply h₂).symm).trans e₂.symm

/-- `dirichletLaplacianH10Apply` is homogeneous on the domain. -/
theorem dirichletLaplacianH10Apply_smul (c : ℝ) {v : SobolevEuclideanZero N 1 2 Ω}
    (h : v ∈ dirichletLaplacianH10Domain Ω) :
    dirichletLaplacianH10Apply Ω (c • v) = c • dirichletLaplacianH10Apply Ω v := by
  have e₁ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c v
  have e₂ := map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) c (dirichletLaplacianH10Apply Ω v)
  have hc : c • v ∈ dirichletLaplacianH10Domain Ω := Submodule.smul_mem _ c h
  refine SobolevMultiIndexZero.fnL_injective ?_
  refine (fnL_dirichletLaplacianH10Apply hc).trans ?_
  refine ((congrArg _ e₁).trans (dirichletLaplacianApply_smul c h.1)).trans ?_
  exact (congrArg (c • ·) (fnL_dirichletLaplacianH10Apply h).symm).trans e₂.symm

variable (Ω) in
/-- **The Dirichlet Laplacian in `H¹₀(Ω)`**, the book's `A₁` (the proof of Theorem 10.2 (a)):
the unbounded operator on the Hilbert space `H¹₀(Ω)` (with the `H¹` inner product) whose domain
is `{v : fnL v ∈ D(A) ∧ A (fnL v) ∈ H¹₀(Ω)}` and whose value is the `H¹₀`-preimage of
`A (fnL v)` (`fnL_dirichletLaplacianH10_apply`). -/
def dirichletLaplacianH10 : SobolevEuclideanZero N 1 2 Ω →ₗ.[ℝ] SobolevEuclideanZero N 1 2 Ω where
  domain := dirichletLaplacianH10Domain Ω
  toFun :=
    { toFun := fun v ↦ dirichletLaplacianH10Apply Ω v
      map_add' := fun v₁ v₂ ↦ dirichletLaplacianH10Apply_add v₁.2 v₂.2
      map_smul' := fun c v ↦ dirichletLaplacianH10Apply_smul c v.2 }

/-- The domain of `A₁`. -/
@[simp]
theorem dirichletLaplacianH10_domain :
    (dirichletLaplacianH10 Ω).domain = dirichletLaplacianH10Domain Ω :=
  rfl

/-- **`fnL (A₁ v) = A (fnL v)`**: `A₁` is `A` read in `H¹₀(Ω)`. -/
theorem fnL_dirichletLaplacianH10_apply (v : (dirichletLaplacianH10 Ω).domain) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (dirichletLaplacianH10 Ω v)
      = dirichletLaplacian Ω
        ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
          v.2.1⟩ :=
  fnL_dirichletLaplacianH10Apply v.2

/-- **`∫ ∇(A₁ u) · ∇v = ⟪A u, A v⟫`** for `u, v ∈ D(A₁)`: the Dirichlet form of `A₁ u` against
`v ∈ H¹₀(Ω)` is `⟪A (fnL v), fnL (A₁ u)⟫ = ⟪A (fnL v), A (fnL u)⟫`. -/
theorem dirichletForm_dirichletLaplacianH10_apply (u v : (dirichletLaplacianH10 Ω).domain) :
    dirichletForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
        (v : SobolevEuclidean N 1 2 Ω)
      = ⟪dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u,
            u.2.1⟩,
        dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
            v.2.1⟩⟫_ℝ := by
  have h1 : dirichletForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
      (v : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω)
        (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) := by
    rw [dirichletForm_isHermitian Ω _ _, conj_trivial]
  have h2 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, v.2.1⟩
    (v : SobolevEuclideanZero N 1 2 Ω).2 rfl (dirichletLaplacianH10 Ω u).2
  have h3 := congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨_, v.2.1⟩, z⟫_ℝ)
    (fnL_dirichletLaplacianH10_apply u)
  exact (h1.trans h2.symm).trans (h3.trans (real_inner_comm _ _))

/-- **`⟪fnL (A₁ u), fnL v⟫ = ∫ ∇u · ∇v`** for `u, v ∈ D(A₁)`. -/
theorem inner_fnL_dirichletLaplacianH10_apply (u v : (dirichletLaplacianH10 Ω).domain) :
    ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (dirichletLaplacianH10 Ω u),
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
  have h1 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, u.2.1⟩
    (u : SobolevEuclideanZero N 1 2 Ω).2 rfl (v : SobolevEuclideanZero N 1 2 Ω).2
  have h2 := congrArg (fun z ↦ ⟪z, SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ)
    (fnL_dirichletLaplacianH10_apply u)
  exact h2.trans h1

/-- **`⟪A₁ u, v⟫_{H¹} = ⟪A u, A v⟫ + ∫ ∇u · ∇v`** for `u, v ∈ D(A₁)` (the book's (iii) in the
proof of Theorem 10.2 (a)), where `A u = A (fnL u)`. -/
theorem dirichletLaplacianH10_inner_eq (u v : (dirichletLaplacianH10 Ω).domain) :
    ⟪dirichletLaplacianH10 Ω u, (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = ⟪dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u,
            u.2.1⟩,
        dirichletLaplacian Ω
          ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v,
            v.2.1⟩⟫_ℝ
        + dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
  have h1 : ⟪dirichletLaplacianH10 Ω u, (v : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ
      = laplaceForm Ω (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω)
        (v : SobolevEuclidean N 1 2 Ω) := by
    rw [laplaceForm_apply_eq_inner, Submodule.coe_inner]
  have h2 := laplaceForm_apply_eq_dirichletForm_add_weakDeriv Ω
    (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω)
  have h3 := dirichletForm_dirichletLaplacianH10_apply u v
  have h4 : ⟪weakDeriv (dirichletLaplacianH10 Ω u : SobolevEuclidean N 1 2 Ω) 0,
      weakDeriv (v : SobolevEuclidean N 1 2 Ω) 0⟫_ℝ
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) :=
    inner_fnL_dirichletLaplacianH10_apply u v
  exact h1.trans (h2.trans (congrArg₂ (· + ·) h3 h4))

/-- **(i) `A₁` is monotone**: `⟪A₁ v, v⟫_{H¹} = ‖A v‖² + ∫ |∇v|² ≥ 0`. -/
theorem dirichletLaplacianH10_isMonotone : (dirichletLaplacianH10 Ω).IsMonotone := fun v ↦ by
  rw [RCLike.re_to_real, dirichletLaplacianH10_inner_eq v v]
  exact add_nonneg real_inner_self_nonneg (dirichletForm_self_nonneg Ω _)

/-- **(iii) `A₁` is symmetric**: `⟪A₁ u, v⟫_{H¹} = ⟪A u, A v⟫ + ∫ ∇u · ∇v` is symmetric in
`u, v`. -/
theorem dirichletLaplacianH10_isFormalAdjoint :
    (dirichletLaplacianH10 Ω).IsFormalAdjoint (dirichletLaplacianH10 Ω) := fun u v ↦ by
  have h1 := dirichletLaplacianH10_inner_eq u v
  have h2 := dirichletLaplacianH10_inner_eq v u
  have h3 : ⟪(u : SobolevEuclideanZero N 1 2 Ω), dirichletLaplacianH10 Ω v⟫_ℝ
      = ⟪dirichletLaplacianH10 Ω v, (u : SobolevEuclideanZero N 1 2 Ω)⟫_ℝ := real_inner_comm _ _
  have h4 := real_inner_comm (dirichletLaplacian Ω ⟨_, v.2.1⟩) (dirichletLaplacian Ω ⟨_, u.2.1⟩)
  have h5 : dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω) (u : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (u : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) := by
    have := dirichletForm_isHermitian Ω (v : SobolevEuclidean N 1 2 Ω)
      (u : SobolevEuclidean N 1 2 Ω)
    rwa [conj_trivial] at this
  exact h1.trans ((congrArg₂ (· + ·) h4 h5.symm).trans (h2.symm.trans h3.symm))

/-- The `H¹₀`-lift `v` of a solution `u ∈ D(A)` of `u + A u = fnL f`, `f ∈ H¹₀(Ω)`, lies in
`D(A₁)`, with `A₁ v = f − v`. -/
theorem mem_dirichletLaplacianH10Domain_of_add_apply_eq {f : SobolevEuclideanZero N 1 2 Ω}
    {u : (dirichletLaplacian Ω).domain}
    (hu : (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacian Ω u
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hvu : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = u) :
    v ∈ dirichletLaplacianH10Domain Ω ∧ ∀ hv : v ∈ dirichletLaplacianH10Domain Ω,
      dirichletLaplacianH10 Ω ⟨v, hv⟩ = f - v := by
  have hmem : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      ∈ dirichletLaplacianDomain Ω := hvu ▸ u.2
  have e1 := map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume) f v
  have e2 : dirichletLaplacian Ω u
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f
        - (u : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :=
    eq_sub_of_add_eq' hu
  have e3 : dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v) = dirichletLaplacian Ω u :=
    congrArg (dirichletLaplacianApply Ω) hvu
  have hA : dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (f - v) :=
    (e3.trans e2).trans ((congrArg (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f - ·) hvu.symm).trans e1.symm)
  refine ⟨mem_dirichletLaplacianH10Domain_iff.2 ⟨hmem, f - v, hA.symm⟩, fun hv ↦ ?_⟩
  refine SobolevMultiIndexZero.fnL_injective ?_
  exact (fnL_dirichletLaplacianH10Apply hv).trans hA

/-- **(ii) `R(I + A₁) = H¹₀(Ω)`**: for `f ∈ H¹₀(Ω)`, the solution `u ∈ D(A)` of `u + A u = fnL f`
has `A u = fnL f − u ∈ H¹₀(Ω)`, so its `H¹₀`-lift lies in `D(A₁)` and solves `v + A₁ v = f`. -/
theorem dirichletLaplacianH10_exists_add_apply_eq (f : SobolevEuclideanZero N 1 2 Ω) :
    ∃ v : (dirichletLaplacianH10 Ω).domain,
      (v : SobolevEuclideanZero N 1 2 Ω) + dirichletLaplacianH10 Ω v = f := by
  obtain ⟨u, hu⟩ := dirichletLaplacian_exists_add_apply_eq
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume f)
  obtain ⟨v, hv, hvu⟩ := dirichletLaplacian_exists_lift u
  obtain ⟨hmem, hA₁⟩ := mem_dirichletLaplacianH10Domain_of_add_apply_eq hu (v := ⟨v, hv⟩) hvu
  refine ⟨⟨⟨v, hv⟩, hmem⟩, ?_⟩
  rw [hA₁ hmem]
  abel

/-- **`A₁` is maximal monotone** in `H¹₀(Ω)`, on any open set ([brezis2011functional], proof of
Theorem 10.2 (a), (i)–(ii)). -/
theorem dirichletLaplacianH10_isMaximalMonotone : (dirichletLaplacianH10 Ω).IsMaximalMonotone :=
  ⟨dirichletLaplacianH10_isMonotone, dirichletLaplacianH10_exists_add_apply_eq⟩

/-- **`A₁` is self-adjoint** in `H¹₀(Ω)` (Proposition 7.6 for the symmetric maximal monotone
`A₁`), which is what gives `u ∈ C([0,∞); H¹₀(Ω))` for `u₀ ∈ H¹₀(Ω)` in Theorem 10.2 (a). -/
theorem dirichletLaplacianH10_isSelfAdjoint : IsSelfAdjoint (dirichletLaplacianH10 Ω) :=
  dirichletLaplacianH10_isMaximalMonotone.isSelfAdjoint_of_isFormalAdjoint
    dirichletLaplacianH10_isFormalAdjoint

/-! ### `D(A^ℓ) ↪ H^{2ℓ}(Ω)` on a `C^{2ℓ}` domain -/

/-- **The elliptic step at every order**: on a `C^{m+2}` domain with bounded boundary, if
`f ∈ D(−Δ)` and `−Δ f` is the function of an element of `H^m(Ω)`, then `f` is the function of an
element of `H^{m+2}(Ω)` (`dirichletLaplacian_exists_sobolev_of_apply` is the even case): the
`H¹₀`-lift of `f` solves `−Δv = −Δ f` weakly, and `Elliptic.regularity_dirichlet_higher_mem`
applies. -/
theorem dirichletLaplacian_exists_sobolev_add_two_of_apply {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (m k : ℕ) (hk : k = m + 2)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : (dirichletLaplacian Ω).domain} (w' : SobolevEuclidean (d + 1) m 2 Ω)
    (hw' : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume w'
      = dirichletLaplacian Ω f) :
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w = f := by
  subst hk
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(dirichletLaplacian Ω f)) m 2 Ω volume := by
    refine (memSobolevMultiIndex w').congr_ae ?_
    rw [← hw']
    rfl
  have heq : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      dirichletForm Ω v Φ = load Ω (dirichletLaplacian Ω f) Φ := fun Φ hΦ ↦
    (dirichletLaplacian_inner_eq_dirichletForm f hv hvf hΦ).symm
  obtain ⟨w, hw⟩ :=
    (regularity_dirichlet_higher_mem m hΩ hΓ hv hg heq).exists_sobolevMultiIndex
  refine ⟨w, Lp.ext (hw.trans ?_)⟩
  rw [← hvf]
  rfl

/-- **The inductive step of `D(A^ℓ) ⊆ H^{2ℓ}(Ω)`**: on a `C^{2ℓ+2}` domain with bounded boundary,
if `f ∈ D(A)` and `A f` is the function of an element of `H^{2ℓ}(Ω)`, then `f` is the function
of an element of `H^{2ℓ+2}(Ω)` — the even case of
`dirichletLaplacian_exists_sobolev_add_two_of_apply`. -/
theorem dirichletLaplacian_exists_sobolev_of_apply {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ k : ℕ) (hk : k = 2 * ℓ + 2)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {f : (dirichletLaplacian Ω).domain} (w' : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω)
    (hw' : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w'
      = dirichletLaplacian Ω f) :
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w = f :=
  dirichletLaplacian_exists_sobolev_add_two_of_apply (2 * ℓ) k hk hΩ hΓ w' hw'

/-- **`D(A^ℓ) ⊆ H^{2ℓ}(Ω)` on a `C^{2ℓ}` domain with bounded boundary**, in the form of the
induction on `ℓ` (`k = 2ℓ` kept as a variable so that no arithmetic on the order is needed):
`f ∈ D(A^{ℓ+1})` has `A f ∈ D(A^ℓ) ⊆ H^{2ℓ}(Ω)`, hence `f ∈ H^{2ℓ+2}(Ω)` by
`dirichletLaplacian_exists_sobolev_of_apply`. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain' {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ) :
    ∀ k : ℕ, k = 2 * ℓ → IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
    Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
    ∀ x : (dirichletLaplacian Ω).PowDomain ℓ, ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x := by
  induction ℓ with
  | zero =>
    intro k hk _ _ x
    subst hk
    obtain ⟨w, hw⟩ := (memSobolevMultiIndex_zero_iff.2
      (Lp.memLp (LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) 0 0
        x))).exists_sobolevMultiIndex (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis)
    exact ⟨w, Lp.ext hw⟩
  | succ ℓ ih =>
    intro k hk hΩ hΓ x
    have hΩ' : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 * ℓ ≤ k))
    obtain ⟨w', hw'⟩ :=
      ih (2 * ℓ) rfl hΩ' hΓ (LinearPMap.PowDomain.shiftL (dirichletLaplacian Ω) ℓ x)
    exact dirichletLaplacian_exists_sobolev_of_apply ℓ k (by omega) hΩ hΓ w'
      (hw'.trans (LinearPMap.PowDomain.applyL_zero_shiftL x))

/-- **`D(A^ℓ) ⊆ H^{2ℓ}(Ω)` on a `C^{2ℓ}` domain with bounded boundary**, the membership half of
the book's (7): every `f ∈ D(A^ℓ)` is the function of an element of `H^{2ℓ}(Ω)`. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x :=
  dirichletLaplacian_exists_sobolev_of_powDomain' ℓ (2 * ℓ) rfl hΩ hΓ x

open LinearPMap.PowDomain in
/-- **`D_{2ℓ+1} ⊆ H^{2ℓ+1}(Ω)` on a `C^{2ℓ+1}` domain with bounded boundary**, in the form of an
induction on `ℓ` (`k = 2ℓ + 1` kept as a variable): if `x ∈ D((−Δ)^ℓ)` has its last coordinate
`(−Δ)^ℓ x` in `H¹₀(Ω)`, then `x` is the function of an element of `H^{2ℓ+1}(Ω)`. The step is
`dirichletLaplacian_exists_sobolev_add_two_of_apply` applied to `−Δ x ∈ H^{2ℓ+1}` — the odd-order
companion of `dirichletLaplacian_exists_sobolev_of_powDomain`. -/
theorem dirichletLaplacian_exists_sobolev_of_powDomain_of_last {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (ℓ : ℕ) :
    ∀ k : ℕ, k = 2 * ℓ + 1 →
    IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
    Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →
    ∀ x : (dirichletLaplacian Ω).PowDomain ℓ,
    (∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume w
        = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) x) →
    ∃ w : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume w
        = applyL (dirichletLaplacian Ω) ℓ 0 x := by
  induction ℓ with
  | zero =>
    intro k hk _ _ x hx
    subst hk
    obtain ⟨w, hw⟩ := hx
    exact ⟨(w : SobolevEuclidean (d + 1) 1 2 Ω), hw.trans (congrArg
      (fun i ↦ applyL (dirichletLaplacian Ω) 0 i x) (by simp : Fin.last 0 = 0))⟩
  | succ ℓ ih =>
    intro k hk hΩ hΓ x hx
    have hΩ' : IsContDiffChartDomain (2 * ℓ + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 * ℓ + 1 ≤ k))
    have hlast : ∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
          w = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) (shiftL (dirichletLaplacian Ω) ℓ x) := by
      obtain ⟨w, hw⟩ := hx
      exact ⟨w, hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i x)
        (Fin.succ_last ℓ).symm).trans (applyL_shiftL (Fin.last ℓ) x).symm)⟩
    obtain ⟨w', hw'⟩ := ih (2 * ℓ + 1) rfl hΩ' hΓ (shiftL (dirichletLaplacian Ω) ℓ x) hlast
    have := dirichletLaplacian_exists_sobolev_add_two_of_apply (2 * ℓ + 1) k (by omega) hΩ hΓ
      (f := ⟨applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x, applyL_mem_domain x 0⟩) w'
      (hw'.trans (applyL_zero_shiftL x))
    exact this

/-- **The continuous injection `D(A^ℓ) ↪ H^{2ℓ}(Ω)`** on a `C^{2ℓ}` domain with bounded boundary
([brezis2011functional] §10.1, the identification (7) and "`D(A^ℓ) ⊂ H^{2ℓ}(Ω)` with continuous
injection"): the bounded linear map `x ↦ w` taking `x ∈ D(A^ℓ)` to the `H^{2ℓ}` element whose
function is `A^0 x` (`dirichletLaplacian_exists_sobolev_of_powDomain`), continuous by the closed
graph theorem (`SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq`);
`fnL_powDomainToSobolevL` is its defining property. It turns chapter 7's `ContDiffOnPowDomain`
lifts into `Bochner.ContDiffOnThrough` lifts
(`Bochner.ContDiffOnThrough.of_contDiffOnPowDomain`). -/
def dirichletLaplacian.powDomainToSobolevL {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {ℓ : ℕ} (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (dirichletLaplacian Ω).PowDomain ℓ →L[ℝ] SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain ℓ) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain ℓ
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0)
    (dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ))

/-- **The function of `powDomainToSobolevL x` is `A^0 x`**: the injection `D(A^ℓ) ↪ H^{2ℓ}(Ω)`
preserves the `0`-th component. -/
theorem fnL_powDomainToSobolevL {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume
        (dirichletLaplacian.powDomainToSobolevL hΩ hΓ x)
      = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x :=
  haveI : CompleteSpace ((dirichletLaplacian Ω).PowDomain ℓ) :=
    dirichletLaplacian_isClosed.completeSpace_powDomain ℓ
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0)
    (dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ)) x

/-- **`‖w‖_{H^{2ℓ}} ≤ C ‖x‖_{D(A^ℓ)}`**: the norm bound of the continuous injection, for every
`H^{2ℓ}`-lift `w` of `A^0 x`. -/
theorem dirichletLaplacian_norm_sobolev_le_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : (dirichletLaplacian Ω).PowDomain ℓ)
      (w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω),
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w
        = LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x → ‖w‖ ≤ C * ‖x‖ := by
  refine ⟨‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖, norm_nonneg _, fun x w hw ↦ ?_⟩
  have : w = dirichletLaplacian.powDomainToSobolevL hΩ hΓ x :=
    SobolevMultiIndex.fnL_injective (hw.trans (fnL_powDomainToSobolevL hΩ hΓ x).symm)
  rw [this]
  exact ContinuousLinearMap.le_opNorm _ x

/-! ### The identification (7): `D(A^ℓ) = {u ∈ H^{2ℓ} : u = Δu = ⋯ = Δ^{ℓ-1} u = 0 on Γ}` -/

variable (Ω) in
/-- **The boundary conditions of the book's (7)**, `u = Δu = ⋯ = Δ^{ℓ-1} u = 0` on `Γ`, read
without a trace: `IsDirichletLaplacianChain Ω ℓ f` says that there is a chain
`g₀ = f, g₁, …, g_ℓ` of `L²(Ω)` functions such that each `g_j`, `j < ℓ`, is the function of an
element of `H¹₀(Ω)` (the condition "`Δ^j u = 0` on `Γ`" in the trace-free reading of Theorem
9.17) and of an element `w_j ∈ H²(Ω)` whose weak Laplacian gives the next term,
`g_{j+1} = −∑ᵢ ∂ᵢᵢ w_j` (`sobolevLaplacianL`), so that `g_j = (−Δ)^j f`. -/
def IsDirichletLaplacianChain (ℓ : ℕ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop :=
  ∃ g : Fin (ℓ + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), g 0 = f ∧
    ∀ j : Fin ℓ, (∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
        fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = g j.castSucc) ∧
      ∃ w : SobolevEuclidean N 2 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = g j.castSucc ∧
        g j.succ = -sobolevLaplacianL Ω w

/-- Consecutive terms of a chain are related by `A`: `g_j ∈ D(A)` with `A g_j = g_{j+1}`. -/
theorem IsDirichletLaplacianChain.exists_apply_eq {ℓ : ℕ}
    {g : Fin (ℓ + 1) → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {j : Fin ℓ}
    (hv : ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v = g j.castSucc)
    (hw : ∃ w : SobolevEuclidean N 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = g j.castSucc ∧
      g j.succ = -sobolevLaplacianL Ω w) :
    ∃ h : g j.castSucc ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨g j.castSucc, h⟩ = g j.succ := by
  obtain ⟨v, hv, hvg⟩ := hv
  obtain ⟨w, hwg, hg⟩ := hw
  have hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
      (hvg.trans hwg.symm))
  obtain ⟨hmem, happ⟩ := mem_dirichletLaplacianDomain_of_sobolev_two w hv hvw
  rw [hvg] at hmem happ
  exact ⟨hmem, (dirichletLaplacian_apply _).trans (happ.trans hg.symm)⟩

/-- **A chain lies in `D(A^ℓ)`**, on any open set: the tuple `(f, −Δf, …)` of a chain is an
element of `D(A^ℓ)` (`LinearPMap.PowDomain.mk`), consecutive entries being related by `A` by
`mem_dirichletLaplacianDomain_of_sobolev_two`. This is the inclusion `⊇` of the book's (7),
which needs no regularity of `Ω`. -/
theorem IsDirichletLaplacianChain.exists_powDomain {ℓ : ℕ}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : IsDirichletLaplacianChain Ω ℓ f) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
      LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = f := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) g fun j ↦ ?_, hg0⟩
  exact IsDirichletLaplacianChain.exists_apply_eq (hg j).1 (hg j).2

/-- **`A f = −∑ᵢ ∂ᵢᵢ w` for any `H²`-lift `w` of `f ∈ D(A)`.** -/
theorem dirichletLaplacian_apply_eq_neg_sobolevLaplacianL (w : SobolevEuclidean N 2 2 Ω)
    (f : (dirichletLaplacian Ω).domain)
    (hwf : fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 2 2 Ω volume w = f) :
    dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  obtain ⟨v, hv, hvf⟩ := dirichletLaplacian_exists_lift f
  have hvw : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn w :=
    Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N)))) ↦ (z : EuclideanSpace ℝ (Fin N) → ℝ))
      (hvf.trans hwf.symm))
  exact dirichletLaplacian_apply_of_sobolev_two w hv hvw f hvf

/-- **Every `f ∈ D(A)` has an `H²`-lift** on a `C²` domain with bounded boundary. -/
theorem dirichletLaplacian_exists_sobolev_two_lift {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : (dirichletLaplacian Ω).domain) :
    ∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f := by
  obtain ⟨C, -, hC⟩ := dirichletLaplacian_exists_sobolev_two_of_isContDiffChartDomain hΩ hΓ
  exact (hC f).1

/-- **An element of `D(A)` on a `C²` domain is the weak Laplacian datum of its `H²`-lift**: for
`f ∈ D(A)`, there are `v ∈ H¹₀(Ω)` and `w ∈ H²(Ω)` with functions `f`, and `A f = −∑ᵢ ∂ᵢᵢ w`. -/
theorem dirichletLaplacian_exists_lifts_of_isContDiffChartDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : (dirichletLaplacian Ω).domain) :
    (∃ v : SobolevEuclidean (d + 1) 1 2 Ω, v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω ∧
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v = f) ∧
    ∃ w : SobolevEuclidean (d + 1) 2 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume w = f ∧
      dirichletLaplacian Ω f = -sobolevLaplacianL Ω w := by
  obtain ⟨w, hw⟩ := dirichletLaplacian_exists_sobolev_two_lift hΩ hΓ f
  exact ⟨dirichletLaplacian_exists_lift f, w, hw,
    dirichletLaplacian_apply_eq_neg_sobolevLaplacianL w f hw⟩

/-- **The iterates of an element of `D(A^ℓ)` form a chain** on a `C²` domain with bounded
boundary: `g_j = A^j x` lies in `D(A) = H²(Ω) ∩ H¹₀(Ω)` for `j < ℓ`, and `A g_j = −∑ᵢ ∂ᵢᵢ w_j`
for its `H²`-lift `w_j` (`dirichletLaplacian_exists_lifts_of_isContDiffChartDomain`). -/
theorem isDirichletLaplacianChain_of_powDomain {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain ℓ) :
    IsDirichletLaplacianChain Ω ℓ (LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x) := by
  refine ⟨fun j ↦ LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ j x, rfl, fun j ↦ ?_⟩
  obtain ⟨hv, w, hw, hA⟩ := dirichletLaplacian_exists_lifts_of_isContDiffChartDomain hΩ hΓ
    ⟨_, LinearPMap.PowDomain.applyL_mem_domain x j⟩
  refine ⟨hv, w, hw, ?_⟩
  exact (LinearPMap.PowDomain.apply_applyL x j).symm.trans hA

/-- **The identification (7)** — [brezis2011functional] §10.1, the proof of Theorem 10.1: on a
`C^{2ℓ}` domain with bounded boundary,
`D(A^ℓ) = {u ∈ H^{2ℓ}(Ω) : u = Δu = ⋯ = Δ^{ℓ-1} u = 0 on Γ}`, the boundary conditions read as
`IsDirichletLaplacianChain` (each iterate `(−Δ)^j u`, `j < ℓ`, lies in `H¹₀(Ω)` and in `H²(Ω)`,
the next iterate being its weak Laplacian). `⊆` is `dirichletLaplacian_exists_sobolev_of_powDomain`
(the regularity theorem iterated) with `isDirichletLaplacianChain_of_powDomain`; `⊇` is
`IsDirichletLaplacianChain.exists_powDomain`, on any open set. For `ℓ = 0` both sides are
trivially true. -/
theorem dirichletLaplacian_mem_powDomain_iff {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (∃ x : (dirichletLaplacian Ω).PowDomain ℓ,
        LinearPMap.PowDomain.applyL (dirichletLaplacian Ω) ℓ 0 x = f) ↔
      (∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w = f) ∧
      IsDirichletLaplacianChain Ω ℓ f := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨hx ▸ dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ x, ?_⟩,
    fun h ↦ h.2.exists_powDomain⟩
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact ⟨fun _ ↦ f, rfl, fun j ↦ j.elim0⟩
  · have hΩ2 : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
      hΩ.of_le (by exact_mod_cast (by omega : 2 ≤ 2 * ℓ))
    exact hx ▸ isDirichletLaplacianChain_of_powDomain hΩ2 hΓ x

/-! ### The bounded injection `D(A₁) ↪ H³(Ω)` on a `C³` domain -/

section SobolevThree

open LinearPMap LinearPMap.PowDomain

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The weak equation of an element of `D(A₁)`**: `∫ ∇y · ∇φ = ∫ (A₁ y) φ` for `y ∈ D(A₁)` and
`φ ∈ H¹₀(Ω)`. -/
theorem dirichletForm_eq_load_fnL_dirichletLaplacianH10_apply (y : (dirichletLaplacianH10 Ω).domain)
    {φ : SobolevEuclidean (d + 1) 1 2 Ω} (hφ : φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω ((y : SobolevEuclideanZero (d + 1) 1 2 Ω) : SobolevEuclidean (d + 1) 1 2 Ω) φ
      = load Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (dirichletLaplacianH10 Ω y)) φ := by
  have h1 := fnL_dirichletLaplacianH10_apply y
  have h2 := dirichletLaplacian_inner_eq_dirichletForm ⟨_, y.2.1⟩
    (y : SobolevEuclideanZero (d + 1) 1 2 Ω).2 rfl hφ
  have h3 := congrArg (fun z ↦ ⟪z, fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
    volume φ⟫_ℝ) h1
  exact h2.symm.trans h3.symm

/-- **`H³` regularity of a weak solution with an `H¹` datum** on a `C³` domain with bounded
boundary, in the typed form: for `v ∈ H¹₀(Ω)` with `∫ ∇v · ∇φ = ∫ g φ` on `H¹₀(Ω)` and `g ∈ H¹(Ω)`,
there is `U ∈ H³(Ω)` with the same function as `v` (Theorem 9.25,
`Elliptic.regularity_dirichlet_higher_mem` at `m = 1`). -/
theorem Elliptic.exists_sobolev_three_of_forall_dirichletForm_eq_load
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {v : SobolevEuclidean (d + 1) 1 2 Ω} (hv : v ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    {g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (⇑g) 1 2 Ω volume)
    (heq : ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω v φ = load Ω g φ) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume v := by
  have hΩ' : IsContDiffChartDomain ((1 : ℕ) + 2) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  have hmem := regularity_dirichlet_higher_mem 1 hΩ' hΓ hv hg heq
  have key : ∀ k : ℕ, k = 1 + 2 →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn v) k 2 Ω
        volume := by
    intro k hk
    subst hk
    exact hmem
  obtain ⟨U, hU⟩ := (key 3 rfl).exists_sobolevMultiIndex
  exact ⟨U, Lp.ext hU⟩

/-- **An element of `D(A₁)` lies in `H³(Ω)`** on a `C³` domain with bounded boundary: for
`y ∈ D(A₁)` (`y ∈ H¹₀(Ω)` with `A (fnL y) ∈ H¹₀(Ω)`), `y` solves `−Δy = fnL (A₁ y)` weakly with a
datum in `H¹(Ω)`, so Theorem 9.25 gives `y ∈ H³(Ω)`. -/
theorem dirichletLaplacianH10_exists_sobolev_three
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (y : (dirichletLaplacianH10 Ω).domain) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume (y : SobolevEuclideanZero (d + 1) 1 2 Ω) := by
  have hg : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (⇑(SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (dirichletLaplacianH10 Ω y))) 1 2 Ω volume :=
    (memSobolevMultiIndex ((dirichletLaplacianH10 Ω y : SobolevEuclideanZero (d + 1) 1 2 Ω) :
      SobolevEuclidean (d + 1) 1 2 Ω)).congr_ae
      (Filter.EventuallyEq.of_eq (SobolevMultiIndexZero.fnL_apply _).symm)
  exact exists_sobolev_three_of_forall_dirichletForm_eq_load hΩ hΓ
    (y : SobolevEuclideanZero (d + 1) 1 2 Ω).2 hg
    fun φ hφ ↦ dirichletForm_eq_load_fnL_dirichletLaplacianH10_apply y hφ

/-- `dirichletLaplacianH10_exists_sobolev_three` for the `0`-th coordinate of `x ∈ D(A₁^1)`, in
the composed form used by the closed graph theorem. -/
theorem dirichletLaplacianH10_exists_sobolev_three_comp
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacianH10 Ω).PowDomain 1) :
    ∃ U : SobolevEuclidean (d + 1) 3 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume U
        = ((SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0)) x := by
  have hmem := applyL_mem_domain x 0
  have h := dirichletLaplacianH10_exists_sobolev_three hΩ hΓ
    ⟨applyL (dirichletLaplacianH10 Ω) 1 0 x, hmem⟩
  rw [ContinuousLinearMap.comp_apply]
  exact h

set_option maxHeartbeats 1000000 in
-- The instance chain of `D(A₁)` (a submodule of `PiLp 2 (Fin 2 → H¹₀(Ω))`, itself a submodule
-- of a subtype of a `PiLp` of `L²` spaces) makes the defeq checks of the closed graph lemma's
-- instance arguments exceed the default budget; the term itself is a single application.
variable (Ω) in
/-- **The bounded injection `D(A₁) ↪ H³(Ω)`** on a `C³` domain with bounded boundary, on the
Hilbert space `D(A₁)` with the graph norm (`PowDomain 1` of `dirichletLaplacianH10 Ω`), by the
closed graph theorem (`exists_continuousLinearMap_comp_eq_of_injective`);
`fnL_powDomainOneToSobolevThreeL` is its defining property. -/
def dirichletLaplacianH10.powDomainOneToSobolevThreeL
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (dirichletLaplacianH10 Ω).PowDomain 1 →L[ℝ] SobolevEuclidean (d + 1) 3 2 Ω :=
  haveI : CompleteSpace ((dirichletLaplacianH10 Ω).PowDomain 1) :=
    dirichletLaplacianH10_isMaximalMonotone.isClosed.completeSpace_powDomain 1
  Classical.choose (exists_continuousLinearMap_comp_eq_of_injective
    (J := fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume)
    SobolevMultiIndex.fnL_injective
    (S := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0))
    (dirichletLaplacianH10_exists_sobolev_three_comp hΩ hΓ))

set_option maxHeartbeats 1000000 in
-- Same instance chain as in the definition above.
/-- The function of `powDomainOneToSobolevThreeL x` is the function of `A₁^0 x ∈ H¹₀(Ω)`. -/
theorem fnL_powDomainOneToSobolevThreeL
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (dirichletLaplacianH10 Ω).PowDomain 1) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume
      (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ x)
      = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (applyL (dirichletLaplacianH10 Ω) 1 0 x) :=
  haveI : CompleteSpace ((dirichletLaplacianH10 Ω).PowDomain 1) :=
    dirichletLaplacianH10_isMaximalMonotone.isClosed.completeSpace_powDomain 1
  (Classical.choose_spec (exists_continuousLinearMap_comp_eq_of_injective
    (J := fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume)
    SobolevMultiIndex.fnL_injective
    (S := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume).comp (applyL (dirichletLaplacianH10 Ω) 1 0))
    (dirichletLaplacianH10_exists_sobolev_three_comp hΩ hΓ)) x).trans
    (ContinuousLinearMap.comp_apply _ _ _)

end SobolevThree

end
