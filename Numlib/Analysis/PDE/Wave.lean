import Mathlib.Analysis.InnerProductSpace.ProdL2
import Numlib.Analysis.ODE.HarmonicOscillator
import Numlib.Analysis.PDE.Heat
import Numlib.Analysis.PDE.Heat.Classical
import Numlib.Analysis.Sobolev.TranslationCurve

/-!
# The wave equation

The wave equation `∂ₜₜu − Δu = 0` on `Ω × (0, ∞)`, `u = 0` on `∂Ω × (0, ∞)`, `u(·, 0) = u₀`,
`∂ₜu(·, 0) = v₀`, as [brezis2011functional] §10.3 solves it: the first-order system
`U' + A U = 0` for `U = (u, ∂ₜu)` in the phase space `H = H¹₀(Ω) × L²(Ω)` with the inner product
`⟪(u₁, v₁), (u₂, v₂)⟫ = ∫ ∇u₁·∇u₂ + ∫ u₁u₂ + ∫ v₁v₂` (the book's (34)) and
`A(u, v) = (−v, −Δu)` with `D(A) = D(−Δ) × H¹₀(Ω)`, where `−Δ` is the Dirichlet Laplacian of
`Numlib/Analysis/PDE/DirichletLaplacian` — so `D(A) = (H² ∩ H¹₀) × H¹₀` on a `C²` domain with
bounded boundary and the weak domain in general. `A + I` is maximal monotone (not `A` itself for
this inner product, and `A` is not symmetric), so Theorem 7.4 (Hille–Yosida,
`LinearPMap.IsMaximalMonotone.exists_isSolutionOn`) together with the shift of chapter 7's
Remark 6 (`LinearPMap.isSolutionOn_smul_id_vadd_iff`: `V = e^{−t} U` solves `V' + (A + I) V = 0`)
gives Theorem 10.7, and Theorem 7.5 with the description of `D(A^k)` gives Theorem 10.8.
Everything except the `H^{k+1} × H^k` reading of `D(A^k)` and the space–time smoothness holds
on an arbitrary open set, for the same reason as in `Numlib/Analysis/PDE/Heat`.
`Ω : Opens (EuclideanSpace ℝ (Fin N))`.

## Theorem 10.8

`D(A^k)` is described on every open set through the domains `D_m` of the Dirichlet Laplacian
(`Wave.MemLaplacianDomain`: `D_0 = L²`, `D_1 = H¹₀`, `D_{m+2} = {f ∈ D(−Δ) : −Δf ∈ D_m}`, the
book's "`w ∈ H^m`, `Δ^j w = 0` on `Γ` for `2j < m`" before Sobolev spaces are read in):
`D(A^k) = D_{k+1} × D_k` (`Wave.mem_operator_powGraph_iff`). On a `C^m` domain with bounded
boundary `D_m ⊆ H^m(Ω)` (`MemLaplacianDomain.exists_sobolev`, Theorem 9.25 at even and at odd
orders), whence the continuous injection `D(A^k) → H^{k+1}(Ω) × H^k(Ω)`
(`Wave.operator.powDomainToSobolevL`, closed graph). Theorem 7.5 is stated for the maximal
monotone `A + I`; the transport `D((A + I)^j) ≃ D(A^j)` of
`Numlib/Analysis/InnerProductSpace/MaximalMonotone` (`LinearPMap.IsAddSmulId.transport`) and
the shift `e^t` give `U ∈ C^{k−j}([0, ∞); D(A^j))`
(`IsSolution.contDiffOnPowDomain_of_powDomain`), hence `u ∈ C^{k−j}([0, ∞); H^{j+1}(Ω))`
(`IsSolution.contDiffOnThrough_of_powDomain`) and, through the space–time bridge of
`Numlib/Analysis/PDE/Bochner/SpaceTime`, `u ∈ C^∞(Ω̄ × [0, ∞))`
(`IsSolution.contDiffOnClosure_spaceTime`). Remark 10, the necessity of the compatibility
conditions, is `Wave.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`, on the pattern of
the heat equation's Remark 4 (`Numlib/Analysis/PDE/Heat/Classical`).

## Types

The phase space is Mathlib's `WithLp 2 (H¹₀(Ω) × L²(Ω))` (`WithLp.instProdInnerProductSpace`),
complete since both factors are, wrapped in a `def` type synonym `Wave.phaseSpace Ω` that
carries only its `NormedAddCommGroup`, `InnerProductSpace ℝ` and `CompleteSpace` instances: every
algebraic instance of the phase space is then reached through `NormedAddCommGroup`, the shape
chapter 7's `LinearPMap` theory expects (an `abbrev` would put `WithLp.instAddCommGroup` in the
type of the operator, and the Hille–Yosida statements no longer unify with it). Its components
are `phaseSpace.fst`, `phaseSpace.snd`, `phaseSpace.mk`, with `phaseSpace.inner_def` (34) and
`phaseSpace.norm_sq_eq`; `H¹₀(Ω) = SobolevEuclideanZero N 1 2 Ω` with its `H¹` inner product,
which is (34) by `Elliptic.laplaceForm_eq_innerSL`. The operator is a `LinearPMap` on it whose
domain asks the first component to lie in `D(−Δ)` after the embedding `SobolevMultiIndexZero.fnL`
and the second to be in the range of that embedding (`Wave.MemOperatorDomain`, with
`toSobolevZero` of `Numlib/Analysis/PDE/DirichletLaplacian` the `H¹₀`-preimage). A solution is
a curve `u : ℝ → L²(Ω)` — the book's `u`, not `U` — in the class (31): `C²([0, ∞); L²)`,
`C¹([0, ∞); H¹₀)` through the embedding (`Bochner.ContDiffOnThrough`), `u(t) ∈ D(−Δ)` with
`−Δu` continuous, `u'' = Δu`, `u 0 = u₀`,
`u' 0 = v₀`; the translation between `U` and `u` (`Wave.isSolution_of_isSolutionOn`,
`Wave.IsSolution.isSolutionOn`) is the bulk of `Wave.existsUnique_isSolution`.

## The remarks

Remark 7 needs the *other* inner product on `H¹₀(Ω)`, `∫ ∇u₁·∇u₂` alone, an inner product
equivalent to the `H¹` one exactly when Poincaré's inequality holds (bounded `Ω`,
Corollary 9.19); for it `⟪AU, U⟫ = 0`, and `A` and `−A` are maximal monotone. That is a second
phase-space type, `Wave.dirichletPhaseSpace`, with the same operator (`Wave.operator'`); the
two-sided solvability and the energy identity for all `t ∈ ℝ` are obtained without it by time
reversal (`t ↦ −t`, `v₀ ↦ −v₀`, `Wave.existsUnique_isSolution_backward`). Remark 8 (d'Alembert's
formula on `Ω = ℝ`, `Wave.dAlembert`) is the one place where a concrete solution is exhibited:
for `u₀ ∈ H²(ℝ)` and `v₀ ∈ H¹(ℝ) = H¹₀(ℝ)` the curve
`Wave.dAlembertL2 u₀ v₀ t = ½ (τ_t u₀ + τ_{−t} u₀) + ½ ∫_{−t}^{t} τ_s v₀ ds` in `L²(ℝ)` — the class
of `x ↦ ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀` (`Wave.coeFn_dAlembertL2_dAlembert`) — is a
solution in the class (31) (`Wave.isSolution_dAlembert`), hence *the* solution on `[0, ∞)`
(`Wave.IsSolution.eqOn_dAlembertL2`). The calculus of the translation group
`t ↦ τ_t f = f(· + t)` in `L²(ℝ)` and `H¹(ℝ)` (`C^k` for `f ∈ H^k`, derivative `τ_t f'`) and of
the primitive curve `∫_{−t}^{t} τ_s v₀ ds` is `Numlib/Analysis/Sobolev/TranslationCurve`; here
`u(t) ∈ D(−Δ)` is read through the `H¹` element `Wave.dAlembertH1Space` carrying `∂ₓu(t)`
(`Wave.mem_dirichletLaplacianDomain_of_forall_ae_eq`: `v ∈ H¹₀` with `∂ᵢv = fn Qᵢ`, `Qᵢ ∈ H¹`,
lies in `D(−Δ)` with `−Δv = −∑ ∂ᵢQᵢ`), and `−Δu(t) = −∂ₜₜu(t)` is the identity
`½ (τ_t u₀'' + τ_{−t} u₀'') + ½ (τ_t v₀' − τ_{−t} v₀')` on both sides.
Remark 9 (the Fourier method, `Wave.IsSolution.inner_eigenfunction`) reduces to the harmonic
oscillator on `[0, ∞)` (`eq_cos_add_sin_of_hasDerivWithinAt_oscillator` of
`Numlib/Analysis/ODE/HarmonicOscillator`).

## References

[brezis2011functional], §10.3: Theorems 10.7, 10.8, Remarks 6–10; chapter 7, Theorems 7.4, 7.5,
Remark 6.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology InnerProductSpace

noncomputable section

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The phase space `H¹₀(Ω) × L²(Ω)` -/

variable (Ω) in
/-- **The phase space of the wave equation** `H = H¹₀(Ω) × L²(Ω)` with the inner product (34),
`⟪(u₁, v₁), (u₂, v₂)⟫ = ⟪u₁, u₂⟫_{H¹} + ⟪v₁, v₂⟫_{L²}` ([brezis2011functional] §10.3): Mathlib's
`ℓ²`-product `WithLp 2` of the two Hilbert spaces, as a type synonym carrying only its
`NormedAddCommGroup` and `InnerProductSpace` structures (so that every algebraic instance of the
phase space is reached through them, as chapter 7's `LinearPMap` theory expects). -/
def phaseSpace : Type :=
  WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

instance : NormedAddCommGroup (phaseSpace Ω) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

instance : InnerProductSpace ℝ (phaseSpace Ω) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

instance : CompleteSpace (phaseSpace Ω) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))))

namespace phaseSpace

variable (Ω) in
/-- The point `(u, v)` of the phase space. -/
def mk (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : phaseSpace Ω :=
  WithLp.toLp 2 (u, v)

/-- The first component `u ∈ H¹₀(Ω)` of a point `(u, v)` of the phase space. -/
def fst (U : phaseSpace Ω) : SobolevEuclideanZero N 1 2 Ω :=
  (WithLp.ofLp (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))).1

/-- The second component `v ∈ L²(Ω)` of a point `(u, v)` of the phase space. -/
def snd (U : phaseSpace Ω) : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (WithLp.ofLp (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))).2

@[simp]
theorem mk_fst (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : (mk Ω u v).fst = u :=
  rfl

@[simp]
theorem mk_snd (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : (mk Ω u v).snd = v :=
  rfl

/-- Two points of the phase space with the same components are equal. -/
theorem ext {U V : phaseSpace Ω} (h1 : U.fst = V.fst) (h2 : U.snd = V.snd) : U = V :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

/-- Every point is `mk` of its components. -/
theorem mk_fst_snd (U : phaseSpace Ω) : mk Ω U.fst U.snd = U :=
  rfl

/-- **The inner product (34)**: `⟪U₁, U₂⟫ = ⟪u₁, u₂⟫_{H¹} + ⟪v₁, v₂⟫_{L²}`. -/
theorem inner_def (U V : phaseSpace Ω) :
    ⟪U, V⟫_ℝ = ⟪U.fst, V.fst⟫_ℝ + ⟪U.snd, V.snd⟫_ℝ :=
  rfl

/-- `‖U‖² = ‖u‖²_{H¹} + ‖v‖²_{L²}`. -/
theorem norm_sq_eq (U : phaseSpace Ω) : ‖U‖ ^ 2 = ‖U.fst‖ ^ 2 + ‖U.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (U : WithLp 2 (SobolevEuclideanZero N 1 2 Ω
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))))

@[simp]
theorem zero_fst : (0 : phaseSpace Ω).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : phaseSpace Ω).snd = 0 :=
  rfl

@[simp]
theorem add_fst (U V : phaseSpace Ω) : (U + V).fst = U.fst + V.fst :=
  rfl

@[simp]
theorem add_snd (U V : phaseSpace Ω) : (U + V).snd = U.snd + V.snd :=
  rfl

@[simp]
theorem neg_fst (U : phaseSpace Ω) : (-U).fst = -U.fst :=
  rfl

@[simp]
theorem neg_snd (U : phaseSpace Ω) : (-U).snd = -U.snd :=
  rfl

@[simp]
theorem sub_fst (U V : phaseSpace Ω) : (U - V).fst = U.fst - V.fst :=
  rfl

@[simp]
theorem sub_snd (U V : phaseSpace Ω) : (U - V).snd = U.snd - V.snd :=
  rfl

@[simp]
theorem smul_fst (c : ℝ) (U : phaseSpace Ω) : (c • U).fst = c • U.fst :=
  rfl

@[simp]
theorem smul_snd (c : ℝ) (U : phaseSpace Ω) : (c • U).snd = c • U.snd :=
  rfl

variable (Ω) in
/-- The first component as a continuous linear map. -/
def fstL : phaseSpace Ω →L[ℝ] SobolevEuclideanZero N 1 2 Ω :=
  WithLp.fstL 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

variable (Ω) in
/-- The second component as a continuous linear map. -/
def sndL : phaseSpace Ω →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  WithLp.sndL 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

@[simp]
theorem fstL_apply (U : phaseSpace Ω) : fstL Ω U = U.fst :=
  rfl

@[simp]
theorem sndL_apply (U : phaseSpace Ω) : sndL Ω U = U.snd :=
  rfl

end phaseSpace

/-- The `H¹` inner product of `H¹₀(Ω)` is `∫ ∇u₁·∇u₂ + ∫ u₁ u₂`. -/
theorem inner_sobolevZero_eq (u₁ u₂ : SobolevEuclideanZero N 1 2 Ω) :
    ⟪u₁, u₂⟫_ℝ = dirichletForm Ω (u₁ : SobolevEuclidean N 1 2 Ω) (u₂ : SobolevEuclidean N 1 2 Ω)
      + ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₁,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₂⟫_ℝ :=
  (laplaceForm_apply_eq_inner Ω (u₁ : SobolevEuclidean N 1 2 Ω)
    (u₂ : SobolevEuclidean N 1 2 Ω)).symm.trans (laplaceForm_apply_eq_dirichletForm_add Ω _ _)

/-! ### The operator `A(u, v) = (−v, −Δu)` -/

variable (Ω) in
/-- **The membership condition of the domain of the wave operator**: `(u, v)` with `fnL u ∈ D(−Δ)`
and `v` the function of an element of `H¹₀(Ω)` ([brezis2011functional] §10.3, (35), with the
weak domain of `−Δ`). -/
def MemOperatorDomain (U : phaseSpace Ω) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst
    ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = U.snd

/-- `0 ∈ D(A)`. -/
theorem memOperatorDomain_zero : MemOperatorDomain Ω (0 : phaseSpace Ω) := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · rw [phaseSpace.zero_fst, _root_.map_zero]
    exact Submodule.zero_mem _
  · rw [_root_.map_zero, phaseSpace.zero_snd]

/-- `D(A)` is closed under addition. -/
theorem MemOperatorDomain.add {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) : MemOperatorDomain Ω (U + V) := by
  obtain ⟨hU1, w, hw⟩ := hU
  obtain ⟨hV1, w', hw'⟩ := hV
  refine ⟨?_, ⟨w + w', ?_⟩⟩
  · rw [phaseSpace.add_fst, _root_.map_add]
    exact add_mem hU1 hV1
  · rw [_root_.map_add, hw, hw', phaseSpace.add_snd]

/-- `D(A)` is closed under scalar multiplication. -/
theorem MemOperatorDomain.smul (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    MemOperatorDomain Ω (c • U) := by
  obtain ⟨hU1, w, hw⟩ := hU
  refine ⟨?_, ⟨c • w, ?_⟩⟩
  · rw [phaseSpace.smul_fst, _root_.map_smul]
    exact Submodule.smul_mem _ c hU1
  · rw [_root_.map_smul, hw, phaseSpace.smul_snd]

variable (Ω) in
/-- **The domain of the wave operator**: `D(A) = D(−Δ) × H¹₀(Ω)` read in the phase space, as a
submodule (`MemOperatorDomain`). -/
def operatorDomain : Submodule ℝ (phaseSpace Ω) where
  carrier := {U | MemOperatorDomain Ω U}
  zero_mem' := memOperatorDomain_zero
  add_mem' := fun hU hV ↦ hU.add hV
  smul_mem' := fun c _ hU ↦ hU.smul c

/-- Membership of the domain of the wave operator is `MemOperatorDomain`. -/
theorem mem_operatorDomain_iff {U : phaseSpace Ω} :
    U ∈ operatorDomain Ω ↔ MemOperatorDomain Ω U :=
  Iff.rfl

variable (Ω) in
/-- The value of the wave operator: `A(u, v) = (−ṽ, A u)` with `ṽ` the `H¹₀`-preimage of `v`
and `A` the Dirichlet Laplacian. -/
def operatorApply (U : phaseSpace Ω) : phaseSpace Ω :=
  phaseSpace.mk Ω (-toSobolevZero Ω U.snd) (dirichletLaplacianApply Ω
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst))

/-- The first component of `A(u, v)` is `−ṽ`. -/
theorem operatorApply_fst (U : phaseSpace Ω) :
    (operatorApply Ω U).fst = -toSobolevZero Ω U.snd :=
  rfl

/-- The second component of `A(u, v)` is `−Δu`. -/
theorem operatorApply_snd (U : phaseSpace Ω) :
    (operatorApply Ω U).snd = dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        U.fst) :=
  rfl

/-- The first component of `A(U + V)`. -/
theorem operatorApply_add_fst {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    (operatorApply Ω (U + V)).fst = (operatorApply Ω U + operatorApply Ω V).fst := by
  change -toSobolevZero Ω (U.snd + V.snd) = -toSobolevZero Ω U.snd + -toSobolevZero Ω V.snd
  rw [toSobolevZero_add hU.2 hV.2, neg_add]

/-- The second component of `A(U + V)`. -/
theorem operatorApply_add_snd {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    (operatorApply Ω (U + V)).snd = (operatorApply Ω U + operatorApply Ω V).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U.fst + V.fst)) = _ + _
  rw [_root_.map_add]
  exact dirichletLaplacianApply_add hU.1 hV.1

/-- `operatorApply` is additive on the domain. -/
theorem operatorApply_add {U V : phaseSpace Ω} (hU : MemOperatorDomain Ω U)
    (hV : MemOperatorDomain Ω V) :
    operatorApply Ω (U + V) = operatorApply Ω U + operatorApply Ω V :=
  phaseSpace.ext (operatorApply_add_fst hU hV) (operatorApply_add_snd hU hV)

/-- The first component of `A(c • U)`. -/
theorem operatorApply_smul_fst (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    (operatorApply Ω (c • U)).fst = (c • operatorApply Ω U).fst := by
  change -toSobolevZero Ω (c • U.snd) = c • -toSobolevZero Ω U.snd
  rw [toSobolevZero_smul c hU.2, smul_neg]

/-- The second component of `A(c • U)`. -/
theorem operatorApply_smul_snd (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    (operatorApply Ω (c • U)).snd = (c • operatorApply Ω U).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (c • U.fst)) = c • _
  rw [_root_.map_smul]
  exact dirichletLaplacianApply_smul c hU.1

/-- `operatorApply` is homogeneous on the domain. -/
theorem operatorApply_smul (c : ℝ) {U : phaseSpace Ω} (hU : MemOperatorDomain Ω U) :
    operatorApply Ω (c • U) = c • operatorApply Ω U :=
  phaseSpace.ext (operatorApply_smul_fst c hU) (operatorApply_smul_snd c hU)

variable (Ω) in
/-- **The wave operator** `A(u, v) = (−v, −Δu)` on the phase space `H¹₀(Ω) × L²(Ω)`, with
domain `D(A) = D(−Δ) × H¹₀(Ω)` ([brezis2011functional] §10.3, (35)), as a `LinearPMap`. -/
def operator : phaseSpace Ω →ₗ.[ℝ] phaseSpace Ω where
  domain := operatorDomain Ω
  toFun :=
    { toFun := fun U ↦ operatorApply Ω U
      map_add' := fun U V ↦ operatorApply_add U.2 V.2
      map_smul' := fun c U ↦ operatorApply_smul c U.2 }

/-- The domain of the wave operator is `operatorDomain Ω`. -/
@[simp]
theorem operator_domain : (operator Ω).domain = operatorDomain Ω :=
  rfl

/-- Membership of the domain of the wave operator: `(u, v)` with `fnL u ∈ D(−Δ)` and
`v ∈ H¹₀(Ω)`. -/
theorem mem_operator_domain_iff {U : phaseSpace Ω} :
    U ∈ (operator Ω).domain ↔
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst
        ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero N 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
          = U.snd :=
  Iff.rfl

/-- Membership of the domain of the wave operator, as `MemOperatorDomain`. -/
theorem memOperatorDomain_of_mem {U : phaseSpace Ω} (hU : U ∈ (operator Ω).domain) :
    MemOperatorDomain Ω U :=
  hU

/-- The value of the wave operator is `operatorApply`. -/
theorem operator_apply (U : (operator Ω).domain) : operator Ω U = operatorApply Ω U :=
  rfl

/-- **The first component of `A(u, v)` is `−v`**, read in `H¹₀(Ω)`. -/
theorem operator_apply_fst (U : (operator Ω).domain) :
    (operator Ω U).fst = -toSobolevZero Ω (U : phaseSpace Ω).snd :=
  rfl

/-- **The second component of `A(u, v)` is `−Δu`**, the Dirichlet Laplacian of `u`. -/
theorem operator_apply_snd (U : (operator Ω).domain) :
    (operator Ω U).snd = dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U : phaseSpace Ω).fst, (mem_operator_domain_iff.1 U.2).1⟩ :=
  rfl

/-- `fnL (A(u, v)).fst = −v`. -/
theorem fnL_operator_apply_fst (U : (operator Ω).domain) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (operator Ω U).fst = -(U : phaseSpace Ω).snd := by
  rw [operator_apply_fst, _root_.map_neg, fnL_toSobolevZero (mem_operator_domain_iff.1 U.2).2]


/-! ### Maximal monotonicity of `A + I` -/

/-- `0 ≤ a + (‖x‖² + ‖y‖²)` when `a = −⟪e, y⟫` with `‖e‖ ≤ ‖x‖`:
`⟪e, y⟫ ≤ ‖e‖ ‖y‖ ≤ ‖x‖ ‖y‖ ≤ ½(‖x‖² + ‖y‖²)`. -/
theorem nonneg_add_sq_of_eq_neg_inner {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : E) (y : F) {a : ℝ} {e : F} (ha : a = -⟪e, y⟫_ℝ) (he : ‖e‖ ≤ ‖x‖) :
    0 ≤ a + (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  rw [ha]
  have h1 := abs_real_inner_le_norm e y
  have h3 := le_abs_self ⟪e, y⟫_ℝ
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_le_mul_of_nonneg_right he (norm_nonneg y),
    norm_nonneg e, norm_nonneg y]

/-- **The key identity** `⟪A U, U⟫ = −⟪u, v⟫_{L²}` for `U = (u, v) ∈ D(A)` ([brezis2011functional]
§10.3, the computation before (36)): the Dirichlet-form terms `−∫ ∇ṽ·∇u` of `⟪−ṽ, u⟫_{H¹}` and
`∫ ∇u·∇ṽ = ⟪−Δu, v⟫` cancel. -/
theorem operator_inner_self_eq (U : (operator Ω).domain) :
    ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ
      = -⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U : phaseSpace Ω).fst, (U : phaseSpace Ω).snd⟫_ℝ := by
  have hmem := mem_operator_domain_iff.1 U.2
  have hwv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U : phaseSpace Ω).snd) = (U : phaseSpace Ω).snd :=
    fnL_toSobolevZero hmem.2
  have h0 : ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ
      = ⟪-toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ
        + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst,
            hmem.1⟩, (U : phaseSpace Ω).snd⟫_ℝ :=
    rfl
  have h1 : ⟪-toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ
      = -⟪toSobolevZero Ω (U : phaseSpace Ω).snd, (U : phaseSpace Ω).fst⟫_ℝ :=
    inner_neg_left (𝕜 := ℝ) (toSobolevZero Ω (U : phaseSpace Ω).snd) (U : phaseSpace Ω).fst
  have h2 := inner_sobolevZero_eq (toSobolevZero Ω (U : phaseSpace Ω).snd) (U : phaseSpace Ω).fst
  have h3 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst, hmem.1⟩,
      (U : phaseSpace Ω).snd⟫_ℝ
      = dirichletForm Ω ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω) :=
    (congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst, hmem.1⟩,
      z⟫_ℝ) hwv).symm.trans (dirichletLaplacian_inner_eq_dirichletForm _
        (U : phaseSpace Ω).fst.2 rfl (toSobolevZero Ω (U : phaseSpace Ω).snd).2)
  have h4 : dirichletForm Ω ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω)
      (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω)
      = dirichletForm Ω (toSobolevZero Ω (U : phaseSpace Ω).snd : SobolevEuclidean N 1 2 Ω)
        ((U : phaseSpace Ω).fst : SobolevEuclidean N 1 2 Ω) :=
    (dirichletForm_isHermitian Ω _ _).trans (conj_trivial _)
  have h5 : ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U : phaseSpace Ω).snd),
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U : phaseSpace Ω).fst⟫_ℝ
      = ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U : phaseSpace Ω).fst, (U : phaseSpace Ω).snd⟫_ℝ :=
    (congrArg (fun z ↦ ⟪z, SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst⟫_ℝ)
        hwv).trans (real_inner_comm _ _)
  linarith

/-- **(i) `A + I` is monotone**: `0 ≤ ⟪A U, U⟫ + ‖U‖²` for `U = (u, v) ∈ D(A)`, since
`⟪A U, U⟫ = −⟪u, v⟫_{L²} ≥ −‖u‖_{L²} ‖v‖_{L²} ≥ −½(‖u‖²_{H¹} + ‖v‖²_{L²})`
([brezis2011functional] §10.3, proof of Theorem 10.7, (i)). -/
theorem operator_add_id_inner_self_nonneg (U : (operator Ω).domain) :
    0 ≤ ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ + ‖(U : phaseSpace Ω)‖ ^ 2 := by
  have h := nonneg_add_sq_of_eq_neg_inner (U : phaseSpace Ω).fst (U : phaseSpace Ω).snd
    (operator_inner_self_eq U) (SobolevMultiIndexZero.norm_fnL_apply_le _)
  rw [phaseSpace.norm_sq_eq]
  exact h

/-- **`A + I` is monotone** in the sense of chapter 7 (`LinearPMap.IsMonotone`). -/
theorem operator_add_id_isMonotone :
    ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsMonotone := fun U ↦ by
  have h1 : ⟪((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω) U,
      (U : phaseSpace Ω)⟫_ℝ = ⟪(U : phaseSpace Ω), (U : phaseSpace Ω)⟫_ℝ
        + ⟪operator Ω U, (U : phaseSpace Ω)⟫_ℝ :=
    inner_add_left _ _ _
  have h2 : ⟪(U : phaseSpace Ω), (U : phaseSpace Ω)⟫_ℝ = ‖(U : phaseSpace Ω)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h3 := operator_add_id_inner_self_nonneg U
  change 0 ≤ ⟪((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω) U,
    (U : phaseSpace Ω)⟫_ℝ
  linarith


/-- **(ii) `R(A + 2I) = H`** ([brezis2011functional] §10.3, proof of Theorem 10.7, (ii),
(36)–(37)): for every `F = (f, g)` there is `U = (u, v) ∈ D(A)` with `2U + AU = F`. Solve
`4u − Δu = 2f + g` in `D(−Δ)` (`dirichletLaplacian_exists_smul_add_apply_eq` at `λ = 4`, on
any open set), then `v := fnL (2u − f)`. -/
theorem operator_exists_two_smul_add_apply_eq (F : phaseSpace Ω) :
    ∃ U : (operator Ω).domain,
      (U : phaseSpace Ω) + ((U : phaseSpace Ω) + operator Ω U) = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_smul_add_apply_eq (Ω := Ω) (c := 4) (by norm_num)
    (F.snd + (2 : ℝ) • SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume F.fst)
  obtain ⟨v', hv', hv'x⟩ := dirichletLaplacian_exists_lift x
  have hux : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) = x := hv'x
  have hmem : MemOperatorDomain Ω (phaseSpace.mk Ω (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, phaseSpace.ext ?_ ?_⟩
  · change (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) + ((⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      + -toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst))) = F.fst
    have hw := toSobolevZero_fnL ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
    exact (congrArg (fun z ↦ (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)
      + ((⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) + -z)) hw).trans
      (by module)
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
      + (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
        + dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω))) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω) - F.fst)
        = (2 : ℝ) • (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
          - SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
            F.fst :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
        1 2 Ω volume) ((2 : ℝ) • (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)) F.fst).trans
        (congrArg (fun z ↦ z - SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume F.fst)
          ((_root_.map_smul (SobolevMultiIndexZero.fnL ℝ
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) (2 : ℝ)
            (⟨v', hv'⟩ : SobolevEuclideanZero N 1 2 Ω)).trans
            (congrArg (fun z ↦ (2 : ℝ) • z) hux)))
    have hx' : (4 : ℝ) • (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
        + dirichletLaplacianApply Ω x = F.snd + (2 : ℝ) • SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume F.fst := hx
    refine (congrArg₂ (fun a b ↦ a + (a + dirichletLaplacianApply Ω b)) h1 hux).trans ?_
    linear_combination (norm := module) hx'

/-- **`A + I` is maximal monotone** on the phase space `H¹₀(Ω) × L²(Ω)`, for every open `Ω`
([brezis2011functional] §10.3, proof of Theorem 10.7, (i)–(ii)): `LinearMap.id +ᵥ operator Ω`
is Mathlib's `A + I` with domain `D(A)`, and its `exists_add_apply_eq` field is `R(A + 2I) = H`. -/
theorem operator_add_id_isMaximalMonotone :
    ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsMaximalMonotone where
  isMonotone := operator_add_id_isMonotone
  exists_add_apply_eq F := by
    obtain ⟨U, hU⟩ := operator_exists_two_smul_add_apply_eq F
    exact ⟨U, hU⟩

/-! ### The solutions of the wave equation -/

variable (Ω) in
/-- **A solution of the wave equation** ([brezis2011functional] §10.3, (27)–(30) in the class
(31) of Theorem 10.7, with the weak domain `D(−Δ)` for `H² ∩ H¹₀`): `u : ℝ → L²(Ω)` with
`u ∈ C²([0, ∞); L²(Ω))`, `u ∈ C¹([0, ∞); H¹₀(Ω))` through the embedding `fnL`,
`u(t) ∈ D(−Δ)` continuously (`u ∈ C([0, ∞); D(−Δ))`), `∂ₜₜu = Δu` on `[0, ∞)` (with the one-sided
second derivative at `0`), `u(0) = u₀` and `∂ₜu(0) = v₀`. Only the values on `[0, ∞)` are
constrained. -/
structure IsSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- `u ∈ C²([0, ∞); L²(Ω))`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ici 0)
  /-- `u ∈ C¹([0, ∞); H¹₀(Ω))`. -/
  contDiffOnThrough : Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume : SobolevEuclideanZero N 1 2 Ω →L[ℝ]
      Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) 1 u (Ici 0)
  /-- `u(t) ∈ D(−Δ)` for `t ≥ 0`. -/
  mem_domain : ∀ t, 0 ≤ t → u t ∈ (dirichletLaplacian Ω).domain
  /-- `u ∈ C([0, ∞); D(−Δ))`. -/
  contDiffOnPowDomain : (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ici 0)
  /-- The wave equation `∂ₜₜu = Δu`, i.e. `u'' = −(−Δ)u`, on `[0, ∞)`. -/
  eqn : ∀ t (ht : 0 ≤ t),
    iteratedDerivWithin 2 u (Ici 0) t = -(dirichletLaplacian Ω ⟨u t, mem_domain t ht⟩)
  /-- `u(0) = u₀`. -/
  apply_zero : u 0 = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2
    Ω volume u₀
  /-- `∂ₜu(0) = v₀`. -/
  derivWithin_zero : derivWithin u (Ici 0) 0 = v₀

/-! ### From the phase space to `L²(Ω)` -/

section Translation

variable {U : ℝ → phaseSpace Ω} {U₀ : phaseSpace Ω}

/-- The first component of a `C¹` curve in the phase space is `C¹` in `H¹₀(Ω)`. -/
theorem contDiffOn_fst_of_contDiffOn (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 1 (fun t ↦ (U t).fst) (Ici 0) :=
  (phaseSpace.fstL Ω).contDiff.comp_contDiffOn hU1

/-- The second component of a `C¹` curve in the phase space is `C¹` in `L²(Ω)`. -/
theorem contDiffOn_snd_of_contDiffOn (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 1 (fun t ↦ (U t).snd) (Ici 0) :=
  (phaseSpace.sndL Ω).contDiff.comp_contDiffOn hU1

/-- `(−A U).fst = ṽ` for `U = (u, v) ∈ D(A)`. -/
theorem neg_operator_apply_fst (V : (operator Ω).domain) :
    (-(operator Ω V)).fst = toSobolevZero Ω (V : phaseSpace Ω).snd :=
  neg_neg (toSobolevZero Ω (V : phaseSpace Ω).snd)

/-- `(−A U).snd = −(−Δu)` for `U = (u, v) ∈ D(A)`. -/
theorem neg_operator_apply_snd (V : (operator Ω).domain) :
    (-(operator Ω V)).snd = -(dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (V : phaseSpace Ω).fst, (mem_operator_domain_iff.1 V.2).1⟩) :=
  rfl

/-- **The first component of `U' + A U = 0`**: `u' = ṽ` in `H¹₀(Ω)`. -/
theorem hasDerivWithinAt_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (U t).fst) (toSobolevZero Ω (U t).snd) (Ici 0) t := by
  have h := (phaseSpace.fstL Ω).hasFDerivAt.comp_hasDerivWithinAt t (hU.hasDerivWithinAt t ht)
  rw [phaseSpace.fstL_apply, neg_operator_apply_fst] at h
  exact h

/-- **The second component of `U' + A U = 0`**: `v' = Δu` in `L²(Ω)`. -/
theorem hasDerivWithinAt_snd (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ (U t).snd) (-(dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
        (U t).fst, (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1⟩)) (Ici 0) t := by
  have h := (phaseSpace.sndL Ω).hasFDerivAt.comp_hasDerivWithinAt t (hU.hasDerivWithinAt t ht)
  rw [phaseSpace.sndL_apply, neg_operator_apply_snd] at h
  exact h

/-- `fnL ṽ = v` along a solution. -/
theorem fnL_toSobolevZero_snd (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (U t).snd) = (U t).snd :=
  fnL_toSobolevZero (mem_operator_domain_iff.1 (hU.mem_domain t ht)).2

/-- **`u' = v` in `L²(Ω)`** for `u = fnL ∘ U.fst`. -/
theorem hasDerivWithinAt_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (U t).snd (Ici 0) t := by
  have h := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_fst hU ht)
  rw [fnL_toSobolevZero_snd hU ht] at h
  exact h

/-- `derivWithin u (Ici 0) = U.snd` on `[0, ∞)`. -/
theorem derivWithin_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) t
      = (U t).snd :=
  (hasDerivWithinAt_fnL_fst hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- `u ∈ C²([0, ∞); L²(Ω))` for `u = fnL ∘ U.fst`. -/
theorem contDiffOn_two_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    ContDiffOn ℝ 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht ↦ (hasDerivWithinAt_fnL_fst hU ht).differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  exact (contDiffOn_snd_of_contDiffOn hU1).congr fun t ht ↦ derivWithin_fnL_fst hU ht

/-- **The wave equation for `u = fnL ∘ U.fst`**: `u'' = −(−Δ)u` on `[0, ∞)`. -/
theorem iteratedDerivWithin_two_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U) {t : ℝ}
    (ht : 0 ≤ t) :
    iteratedDerivWithin 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) t
      = -(dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst,
        (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1⟩) := by
  have e : iteratedDerivWithin 2 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)
      = derivWithin (derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)) (Ici 0) :=
    iteratedDerivWithin_succ.trans
      (congrArg (fun g ↦ derivWithin g (Ici 0)) iteratedDerivWithin_one)
  have e2 : derivWithin (derivWithin (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0)) (Ici 0) t
      = derivWithin (fun t ↦ (U t).snd) (Ici 0) t :=
    derivWithin_congr (fun s hs ↦ derivWithin_fnL_fst hU hs) (derivWithin_fnL_fst hU ht)
  exact (congrFun e t).trans
    (e2.trans ((hasDerivWithinAt_snd hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)))

/-- `u ∈ C([0, ∞); D(−Δ))` for `u = fnL ∘ U.fst`: `−Δu = −v'` is continuous. -/
theorem contDiffOnPowDomain_fnL_fst (hU : (operator Ω).IsSolutionOn U₀ (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 (fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst) (Ici 0) := by
  rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
  refine ⟨![fun t ↦ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume (U t).fst, fun t ↦ -derivWithin (fun t ↦ (U t).snd) (Ici 0) t], fun t _ ↦ rfl, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · exact ((SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
        volume).contDiff.comp_contDiffOn (contDiffOn_fst_of_contDiffOn hU1)).of_le (by simp)
    · exact contDiffOn_zero.2 ((contDiffOn_snd_of_contDiffOn hU1).continuousOn_derivWithin
        (uniqueDiffOn_Ici 0) le_rfl).neg
  · intro t ht i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    change ∃ h : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (U t).fst ∈ (dirichletLaplacian Ω).domain, dirichletLaplacian Ω
        ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          (U t).fst, h⟩ = -derivWithin (fun t ↦ (U t).snd) (Ici 0) t
    refine ⟨(mem_operator_domain_iff.1 (hU.mem_domain t ht)).1, ?_⟩
    exact (neg_neg _).symm.trans (congrArg Neg.neg
      ((hasDerivWithinAt_snd hU ht).derivWithin (uniqueDiffOn_Ici 0 t ht)).symm)

/-- **The forward translation of Theorem 10.7**: a `C¹` solution `U = (ũ, v)` of `U' + A U = 0`
on `[0, ∞)` with `U(0) = (u₀, v₀)` yields the solution `u = fnL ∘ ũ` of the wave equation. -/
theorem isSolution_of_isSolutionOn {u₀ : SobolevEuclideanZero N 1 2 Ω}
    {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hU : (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0) U)
    (hU1 : ContDiffOn ℝ 1 U (Ici 0)) :
    IsSolution Ω u₀ v₀ fun t ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U t).fst where
  contDiffOn := contDiffOn_two_fnL_fst hU hU1
  contDiffOnThrough := ⟨fun t ↦ (U t).fst, contDiffOn_fst_of_contDiffOn hU1, fun _ _ ↦ rfl⟩
  mem_domain t ht := (mem_operator_domain_iff.1 (hU.mem_domain t ht)).1
  contDiffOnPowDomain := contDiffOnPowDomain_fnL_fst hU hU1
  eqn _ ht := iteratedDerivWithin_two_fnL_fst hU ht
  apply_zero := congrArg (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    1 2 Ω volume) (congrArg phaseSpace.fst hU.apply_zero)
  derivWithin_zero := (derivWithin_fnL_fst hU le_rfl).trans (congrArg phaseSpace.snd hU.apply_zero)

end Translation

/-! ### Existence: the shifted semigroup of `A + I` -/

/-- `1 • I + A = I + A`. -/
theorem one_smul_id_vadd_operator :
    (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω)
      = (LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω := by
  rw [one_smul]

variable (Ω) in
/-- **The solution in the phase space**: `U(t) = e^t S_{A+I}(t) (u₀, v₀)`, the semigroup of the
maximal monotone `A + I` (chapter 7's `LinearPMap.semigroup`) shifted by chapter 7's Remark 6
([brezis2011functional] §10.3, proof of Theorem 10.7). -/
def phaseSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    phaseSpace Ω :=
  Real.exp t • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
    (phaseSpace.mk Ω u₀ v₀)

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The data `(u₀, v₀)` lie in `D(A)` when `fnL u₀ ∈ D(−Δ)` and `v₀ ∈ H¹₀(Ω)`. -/
theorem memOperatorDomain_mk
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀) :=
  ⟨hu₀, hv₀⟩

/-- **`U` solves `U' + A U = 0` on `[0, ∞)` with `U(0) = (u₀, v₀)`** for data in `D(A)`
(Theorem 7.4 for `A + I` and the shift `e^t` of chapter 7's Remark 6). -/
theorem isSolutionOn_phaseSolution (h₀ : MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀)) :
    (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0) (phaseSolution Ω u₀ v₀) := by
  have hV : ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn
      (phaseSpace.mk Ω u₀ v₀) (Ici 0) fun t ↦
        ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
          (phaseSpace.mk Ω u₀ v₀) :=
    operator_add_id_isMaximalMonotone.isSolutionOn_semigroup ⟨phaseSpace.mk Ω u₀ v₀, h₀⟩
  have hV' : (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn
      (phaseSpace.mk Ω u₀ v₀) (Ici 0) fun t ↦
        ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).semigroup t
          (phaseSpace.mk Ω u₀ v₀) := by
    rw [one_smul_id_vadd_operator]
    exact hV
  have := (LinearPMap.isSolutionOn_smul_id_vadd_iff (c := 1)).1 hV'
  have e : (fun t ↦ Real.exp (1 * t) • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω)
      +ᵥ operator Ω).semigroup t (phaseSpace.mk Ω u₀ v₀)) = phaseSolution Ω u₀ v₀ :=
    funext fun t ↦ by
      rw [one_mul]
      rfl
  rw [e] at this
  exact this

/-- **`U ∈ C¹([0, ∞); H)`**. -/
theorem contDiffOn_phaseSolution (h₀ : MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀)) :
    ContDiffOn ℝ 1 (phaseSolution Ω u₀ v₀) (Ici 0) :=
  Real.contDiff_exp.contDiffOn.smul
    (operator_add_id_isMaximalMonotone.contDiffOn_semigroup_apply ⟨phaseSpace.mk Ω u₀ v₀, h₀⟩)

variable (Ω) in
/-- **The solution of the wave equation** with data `(u₀, v₀)`: the first component of the
phase-space solution `e^t S_{A+I}(t) (u₀, v₀)`, read in `L²(Ω)` ([brezis2011functional]
Theorem 10.7). -/
def solution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (phaseSolution Ω u₀ v₀ t).fst

/-- **Theorem 10.7, existence** ([brezis2011functional]): for `fnL u₀ ∈ D(−Δ)` (the book's
`u₀ ∈ H² ∩ H¹₀`) and `v₀ ∈ H¹₀(Ω)`, `solution Ω u₀ v₀` solves the wave equation. -/
theorem isSolution_solution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ v₀ (solution Ω u₀ v₀) :=
  isSolution_of_isSolutionOn (isSolutionOn_phaseSolution (memOperatorDomain_mk hu₀ hv₀))
    (contDiffOn_phaseSolution (memOperatorDomain_mk hu₀ hv₀))

/-! ### Uniqueness: from `L²(Ω)` back to the phase space -/

/-- A curve `t ↦ (f t, g t)` in the phase space has the derivative `(f', g')`. -/
theorem phaseSpace.hasDerivWithinAt_mk {f : ℝ → SobolevEuclideanZero N 1 2 Ω}
    {g : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {a : SobolevEuclideanZero N 1 2 Ω}
    {b : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f a s t) (hg : HasDerivWithinAt g b s t) :
    HasDerivWithinAt (fun t ↦ phaseSpace.mk Ω (f t) (g t)) (phaseSpace.mk Ω a b) s t :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (SobolevEuclideanZero N 1 2 Ω)
    (Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))).symm.hasFDerivAt
    |>.comp_hasDerivWithinAt t (hf.prodMk hg)

/-- **Uniqueness for `U' + A U = 0`**: two solutions on `[0, ∞)` with the same datum agree on
`[0, ∞)`, by the monotonicity of `A + I` after the shift `e^{−t}` (chapter 7's Remark 6 and
`LinearPMap.IsMonotone.eqOn_of_isSolutionOn`). -/
theorem operator_eqOn_of_isSolutionOn {U₀ : phaseSpace Ω} {U₁ U₂ : ℝ → phaseSpace Ω}
    (h₁ : (operator Ω).IsSolutionOn U₀ (Ici 0) U₁) (h₂ : (operator Ω).IsSolutionOn U₀ (Ici 0) U₂) :
    EqOn U₁ U₂ (Ici 0) := by
  have hm := operator_add_id_isMonotone (Ω := Ω)
  rw [← one_smul_id_vadd_operator] at hm
  have key : ∀ U : ℝ → phaseSpace Ω, (operator Ω).IsSolutionOn U₀ (Ici 0) U →
      (((1 : ℝ) • LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω) +ᵥ operator Ω).IsSolutionOn U₀
        (Ici 0) fun t ↦ Real.exp (-t) • U t := fun U hU ↦ by
    refine (LinearPMap.isSolutionOn_smul_id_vadd_iff (c := 1)).2 ?_
    convert hU using 1
    funext t
    simp only [smul_smul, ← Real.exp_add, one_mul, add_neg_cancel, Real.exp_zero, one_smul]
  intro t ht
  have h := hm.eqOn_of_isSolutionOn (key U₁ h₁) (key U₂ h₂) ht
  have h' := congrArg (fun z ↦ Real.exp t • z) h
  simpa only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul] using h'

namespace IsSolution

variable {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The `H¹₀` lift of a solution** `t ↦ ũ(t) = toSobolevZero (u t)` is `C¹` on `[0, ∞)`. -/
theorem contDiffOn_toSobolevZero (h : IsSolution Ω u₀ v₀ u) :
    ContDiffOn ℝ 1 (fun t ↦ toSobolevZero Ω (u t)) (Ici 0) := by
  obtain ⟨v, hv, huv⟩ := h.contDiffOnThrough
  exact hv.congr fun t ht ↦ toSobolevZero_eq (huv t ht).symm

/-- `fnL ũ(t) = u(t)` for `t ≥ 0`. -/
theorem fnL_toSobolevZero_apply (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (toSobolevZero Ω (u t)) = u t := by
  obtain ⟨v, -, huv⟩ := h.contDiffOnThrough
  exact fnL_toSobolevZero ⟨v t, (huv t ht).symm⟩

/-- `u'(t) ∈ H¹₀(Ω)` for `t ≥ 0`. -/
theorem exists_fnL_eq_derivWithin (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = derivWithin u (Ici 0) t := by
  obtain ⟨v, hv, huv⟩ := h.contDiffOnThrough
  exact ⟨derivWithin v (Ici 0) t, (Bochner.ContDiffOnThrough.derivWithin_eq hv huv le_rfl
    (uniqueDiffOn_Ici 0) ht).symm⟩

/-- **`ũ' = (u')~`**: the lift of `u'` is the derivative of the lift. -/
theorem hasDerivWithinAt_toSobolevZero (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ toSobolevZero Ω (u t))
      (toSobolevZero Ω (derivWithin u (Ici 0) t)) (Ici 0) t := by
  have h1 := (h.contDiffOn_toSobolevZero.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  have h2 := Bochner.ContDiffOnThrough.derivWithin_eq h.contDiffOn_toSobolevZero
    (fun t ht ↦ (h.fnL_toSobolevZero_apply ht).symm) le_rfl (uniqueDiffOn_Ici 0) ht
  rw [toSobolevZero_eq h2.symm]
  exact h1

/-- **`u'' = −(−Δ)u`** as a derivative of `u'` within `[0, ∞)`. -/
theorem hasDerivWithinAt_derivWithin (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (derivWithin u (Ici 0)) (-(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩))
      (Ici 0) t := by
  have hc := h.contDiffOn
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)] at hc
  have h2 := (hc.2.2.differentiableOn one_ne_zero t ht).hasDerivWithinAt
  have h3 : derivWithin (derivWithin u (Ici 0)) (Ici 0) t
      = -(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩) :=
    (congrFun (iteratedDerivWithin_two u (Ici 0)) t).symm.trans (h.eqn t ht)
  rw [h3] at h2
  exact h2

/-- `(ũ(t), u'(t)) ∈ D(A)` for `t ≥ 0`. -/
theorem memOperatorDomain (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    MemOperatorDomain Ω
      (phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t)) := by
  refine ⟨?_, h.exists_fnL_eq_derivWithin ht⟩
  change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
    (toSobolevZero Ω (u t)) ∈ dirichletLaplacianDomain Ω
  rw [h.fnL_toSobolevZero_apply ht]
  exact h.mem_domain t ht

/-- **The backward translation of Theorem 10.7**: a solution `u` of the wave equation yields the
solution `U = (ũ, u')` of `U' + A U = 0` on `[0, ∞)` with `U(0) = (u₀, v₀)`. -/
theorem isSolutionOn (h : IsSolution Ω u₀ v₀ u) :
    (operator Ω).IsSolutionOn (phaseSpace.mk Ω u₀ v₀) (Ici 0)
      fun t ↦ phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t) where
  apply_zero := phaseSpace.ext (toSobolevZero_eq h.apply_zero.symm) h.derivWithin_zero
  mem_domain _ ht := h.memOperatorDomain ht
  hasDerivWithinAt t ht := by
    refine (phaseSpace.hasDerivWithinAt_mk (h.hasDerivWithinAt_toSobolevZero ht)
      (h.hasDerivWithinAt_derivWithin ht)).congr_deriv (phaseSpace.ext ?_ ?_)
    · exact (neg_operator_apply_fst ⟨phaseSpace.mk Ω (toSobolevZero Ω (u t))
        (derivWithin u (Ici 0) t), h.memOperatorDomain ht⟩).symm
    · exact (congrArg (fun z ↦ -(dirichletLaplacian Ω z))
        (Subtype.ext (h.fnL_toSobolevZero_apply ht).symm)).trans
        (neg_operator_apply_snd ⟨phaseSpace.mk Ω (toSobolevZero Ω (u t))
          (derivWithin u (Ici 0) t), h.memOperatorDomain ht⟩).symm

/-- **Theorem 10.7, uniqueness**: two solutions with the same data agree on `[0, ∞)`. -/
theorem unique {v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (h : IsSolution Ω u₀ v₀ u) (h' : IsSolution Ω u₀ v₀ v) : EqOn u v (Ici 0) := fun _ ht ↦
  (h.fnL_toSobolevZero_apply ht).symm.trans
    ((congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst)
      (operator_eqOn_of_isSolutionOn h.isSolutionOn h'.isSolutionOn ht)).trans
      (h'.fnL_toSobolevZero_apply ht))

/-- The data of a solution lie in `D(A)`: `fnL u₀ ∈ D(−Δ)` and `v₀ ∈ H¹₀(Ω)`. -/
theorem memOperatorDomain_mk (h : IsSolution Ω u₀ v₀ u) :
    MemOperatorDomain Ω (phaseSpace.mk Ω u₀ v₀) :=
  h.isSolutionOn.apply_zero ▸ h.isSolutionOn.mem_domain 0 self_mem_Ici

/-- **Every solution is `solution Ω u₀ v₀` on `[0, ∞)`**. -/
theorem eqOn_solution (h : IsSolution Ω u₀ v₀ u) : EqOn u (solution Ω u₀ v₀) (Ici 0) := fun _ ht ↦
  (h.fnL_toSobolevZero_apply ht).symm.trans
    (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst)
      (operator_eqOn_of_isSolutionOn h.isSolutionOn
        (isSolutionOn_phaseSolution h.memOperatorDomain_mk) ht))

end IsSolution

/-- **Theorem 10.7, existence and uniqueness** ([brezis2011functional]) on an arbitrary open
set: for `fnL u₀ ∈ D(−Δ)` (the book's `u₀ ∈ H² ∩ H¹₀`) and `v₀ ∈ H¹₀(Ω)` there is a solution of
the wave equation, and any two solutions agree on `[0, ∞)` (`IsSolution` does not constrain
negative times). -/
theorem existsUnique_isSolution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃ u, IsSolution Ω u₀ v₀ u ∧ ∀ v, IsSolution Ω u₀ v₀ v → EqOn v u (Ici 0) :=
  ⟨solution Ω u₀ v₀, isSolution_solution hu₀ hv₀, fun _ hv ↦ hv.eqOn_solution⟩

/-! ### Linearity of the solution in the data -/

/-- `(u + u', v + v') = (u, v) + (u', v')`. -/
theorem phaseSpace.mk_add (u u' : SobolevEuclideanZero N 1 2 Ω)
    (v v' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    phaseSpace.mk Ω (u + u') (v + v') = phaseSpace.mk Ω u v + phaseSpace.mk Ω u' v' :=
  rfl

/-- `(c • u, c • v) = c • (u, v)`. -/
theorem phaseSpace.mk_smul (c : ℝ) (u : SobolevEuclideanZero N 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    phaseSpace.mk Ω (c • u) (c • v) = c • phaseSpace.mk Ω u v :=
  rfl

variable {u₀' : SobolevEuclideanZero N 1 2 Ω}
  {v₀' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The phase-space solution is additive in the data. -/
theorem phaseSolution_add (t : ℝ) :
    phaseSolution Ω (u₀ + u₀') (v₀ + v₀') t
      = phaseSolution Ω u₀ v₀ t + phaseSolution Ω u₀' v₀' t := by
  unfold phaseSolution
  rw [phaseSpace.mk_add, _root_.map_add, smul_add]

/-- The phase-space solution is homogeneous in the data. -/
theorem phaseSolution_smul (c : ℝ) (t : ℝ) :
    phaseSolution Ω (c • u₀) (c • v₀) t = c • phaseSolution Ω u₀ v₀ t := by
  unfold phaseSolution
  rw [phaseSpace.mk_smul, _root_.map_smul, smul_comm]

/-- **The solution is additive in the data** (each `S_{A+I}(t)` is linear). -/
theorem solution_add (t : ℝ) :
    solution Ω (u₀ + u₀') (v₀ + v₀') t = solution Ω u₀ v₀ t + solution Ω u₀' v₀' t :=
  (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) (phaseSolution_add t)).trans
    (_root_.map_add (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) (phaseSolution Ω u₀ v₀ t).fst (phaseSolution Ω u₀' v₀' t).fst)

/-- **The solution is homogeneous in the data**. -/
theorem solution_smul (c : ℝ) (t : ℝ) :
    solution Ω (c • u₀) (c • v₀) t = c • solution Ω u₀ v₀ t :=
  (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) (phaseSolution_smul c t)).trans
    (_root_.map_smul (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume) c (phaseSolution Ω u₀ v₀ t).fst)

/-! ### Conservation of energy -/

variable (Ω) in
/-- **The energy** `E(t) = ‖u'(t)‖² + ∫_Ω |∇ũ(t)|²` of a curve `u`, with `ũ` its `H¹₀` lift
([brezis2011functional] §10.3, (32)). -/
def energyFun (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    ℝ :=
  ‖derivWithin u (Ici 0) t‖ ^ 2
    + ⟪dirichletOperator Ω (toSobolevZero Ω (u t)), toSobolevZero Ω (u t)⟫_ℝ

namespace IsSolution

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- `∫ ∇ũ(t)·∇ũ'(t) = ⟪−Δu(t), u'(t)⟫` along a solution. -/
theorem inner_dirichletOperator_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ⟪dirichletOperator Ω (toSobolevZero Ω (u t)),
      toSobolevZero Ω (derivWithin u (Ici 0) t)⟫_ℝ
      = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, derivWithin u (Ici 0) t⟫_ℝ :=
  (inner_dirichletOperator _ _ _).trans
    ((dirichletLaplacian_inner_eq_dirichletForm ⟨u t, h.mem_domain t ht⟩
      (toSobolevZero Ω (u t)).2 (h.fnL_toSobolevZero_apply ht)
      (toSobolevZero Ω (derivWithin u (Ici 0) t)).2).symm.trans
      (congrArg (fun z ↦ ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, z⟫_ℝ)
        (fnL_toSobolevZero (h.exists_fnL_eq_derivWithin ht))))

/-- **`E' = 0`**: `d/dt ‖u'‖² = 2⟪u', Δu⟫` and `d/dt ∫|∇ũ|² = 2 ∫ ∇ũ·∇ũ' = 2⟪−Δu, u'⟫` cancel
([brezis2011functional] §10.3, proof of (32)). -/
theorem hasDerivWithinAt_energyFun (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (energyFun Ω u) 0 (Ici 0) t := by
  have h1 := (h.hasDerivWithinAt_derivWithin ht).norm_sq
  have hũ := h.hasDerivWithinAt_toSobolevZero ht
  have h2 : HasDerivWithinAt
      (fun t ↦ ⟪dirichletOperator Ω (toSobolevZero Ω (u t)), toSobolevZero Ω (u t)⟫_ℝ)
      (⟪dirichletOperator Ω (toSobolevZero Ω (u t)),
        toSobolevZero Ω (derivWithin u (Ici 0) t)⟫_ℝ
        + ⟪dirichletOperator Ω (toSobolevZero Ω (derivWithin u (Ici 0) t)),
          toSobolevZero Ω (u t)⟫_ℝ) (Ici 0) t :=
    ((dirichletOperator Ω).hasFDerivAt.comp_hasDerivWithinAt t hũ).inner ℝ hũ
  refine (h1.add h2).congr_deriv ?_
  have e1 := h.inner_dirichletOperator_eq ht
  have e2 := inner_dirichletOperator_comm _ (toSobolevZero Ω (derivWithin u (Ici 0) t))
    (toSobolevZero Ω (u t))
  have e3 : ⟪derivWithin u (Ici 0) t, -(dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩)⟫_ℝ
      = -⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, derivWithin u (Ici 0) t⟫_ℝ := by
    rw [inner_neg_right, real_inner_comm]
  rw [e2, e1, e3]
  ring

/-- **The energy is constant on `[0, ∞)`**. -/
theorem energyFun_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    energyFun Ω u t = energyFun Ω u 0 := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rfl
  refine constant_of_derivWithin_zero (f := energyFun Ω u) (a := 0) (b := t)
    (fun x hx ↦
      ((h.hasDerivWithinAt_energyFun hx.1).mono Icc_subset_Ici_self).differentiableWithinAt)
    (fun x hx ↦ ((h.hasDerivWithinAt_energyFun hx.1).mono Icc_subset_Ici_self).derivWithin
      (uniqueDiffOn_Icc hpos x ⟨hx.1, hx.2.le⟩)) t (right_mem_Icc.2 ht)

/-- **(32), conservation of energy, in terms of the `H¹₀` lift**:
`‖u'(t)‖² + ∫_Ω |∇ũ(t)|² = ‖v₀‖² + ∫_Ω |∇u₀|²` for `t ≥ 0` ([brezis2011functional] §10.3,
Remark 6). -/
theorem energy_dirichletForm (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2
      + dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
      = ‖v₀‖ ^ 2
        + dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) := by
  have e := h.energyFun_eq ht
  have e1 : energyFun Ω u t = ‖derivWithin u (Ici 0) t‖ ^ 2
      + dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω) :=
    congrArg (fun z ↦ ‖derivWithin u (Ici 0) t‖ ^ 2 + z) (inner_dirichletOperator _ _ _)
  have e2 : energyFun Ω u 0 = ‖v₀‖ ^ 2
      + dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) := by
    unfold energyFun
    rw [h.derivWithin_zero, toSobolevZero_eq h.apply_zero.symm, inner_dirichletOperator]
  exact e1.symm.trans (e.trans e2)

/-- **(32), conservation of energy** ([brezis2011functional] §10.3): for `t ≥ 0`,
`‖u'(t)‖² + ⟪−Δu(t), u(t)⟫ = ‖v₀‖² + ⟪−Δu₀, u₀⟫`, the two inner products being `∫_Ω |∇u(t)|²` and
`∫_Ω |∇u₀|²` (`dirichletLaplacian_inner_self_eq_dirichletForm`). -/
theorem energy (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ‖derivWithin u (Ici 0) t‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, u t⟫_ℝ
      = ‖v₀‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₀⟫_ℝ := by
  have e1 : ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain t ht⟩, u t⟫_ℝ
      = dirichletForm Ω (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω)
        (toSobolevZero Ω (u t) : SobolevEuclidean N 1 2 Ω) :=
    dirichletLaplacian_inner_self_eq_dirichletForm ⟨u t, h.mem_domain t ht⟩
      (toSobolevZero Ω (u t)).2 (h.fnL_toSobolevZero_apply ht)
  have e2 : ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀⟫_ℝ
      = dirichletForm Ω (u₀ : SobolevEuclidean N 1 2 Ω) (u₀ : SobolevEuclidean N 1 2 Ω) :=
    dirichletLaplacian_inner_self_eq_dirichletForm ⟨_, h.memOperatorDomain_mk.1⟩ u₀.2 rfl
  exact (congrArg (fun z ↦ ‖derivWithin u (Ici 0) t‖ ^ 2 + z) e1).trans
    ((h.energy_dirichletForm ht).trans (congrArg (fun z ↦ ‖v₀‖ ^ 2 + z) e2).symm)

end IsSolution

/-! ### Remark 8: d'Alembert's formula -/

/-- **d'Alembert's formula** ([brezis2011functional] §10.3, Remark 8, (40)): for data
`u₀ v₀ : ℝ → ℝ`, the function
`u(x, t) = ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀(s) ds`, as a curve `t ↦ u(·, t)` of
functions of `x`. For `v₀ = 0` it is (41). -/
def dAlembert (u₀ v₀ : ℝ → ℝ) (t : ℝ) : ℝ → ℝ := fun x ↦
  (1 / 2) * (u₀ (x + t) + u₀ (x - t)) + (1 / 2) * ∫ s in (x - t)..(x + t), v₀ s

/-- The value of d'Alembert's formula. -/
theorem dAlembert_apply (u₀ v₀ : ℝ → ℝ) (t x : ℝ) :
    dAlembert u₀ v₀ t x
      = (1 / 2) * (u₀ (x + t) + u₀ (x - t)) + (1 / 2) * ∫ s in (x - t)..(x + t), v₀ s :=
  rfl

/-- **(41)**: with `v₀ = 0`, `u(x, t) = ½ (u₀(x + t) + u₀(x − t))`. -/
theorem dAlembert_zero_apply (u₀ : ℝ → ℝ) (t x : ℝ) :
    dAlembert u₀ 0 t x = (1 / 2) * (u₀ (x + t) + u₀ (x - t)) := by
  rw [dAlembert_apply]
  simp

/-- **Remark 8, propagation of singularities** ([brezis2011functional] §10.3): if `u₀` is `C^n`
off a point `x₀` and `v₀ = 0`, then `(x, t) ↦ u(x, t)` given by (41) is `C^n` off the two
characteristics `{x + t = x₀}` and `{x − t = x₀}` through `(x₀, 0)`: a singularity of the datum
propagates along the characteristics and nowhere else. -/
theorem dAlembert_contDiffOn_off_characteristics {u₀ : ℝ → ℝ} {x₀ : ℝ} {n : WithTop ℕ∞}
    (hu₀ : ContDiffOn ℝ n u₀ {x₀}ᶜ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ dAlembert u₀ 0 p.2 p.1)
      {p : ℝ × ℝ | p.1 + p.2 ≠ x₀ ∧ p.1 - p.2 ≠ x₀} := by
  have e : (fun p : ℝ × ℝ ↦ dAlembert u₀ 0 p.2 p.1)
      = fun p : ℝ × ℝ ↦ (1 / 2) * (u₀ (p.1 + p.2) + u₀ (p.1 - p.2)) :=
    funext fun p ↦ dAlembert_zero_apply u₀ p.2 p.1
  rw [e]
  refine contDiffOn_const.mul (ContDiffOn.add ?_ ?_)
  · exact hu₀.comp (contDiff_fst.add contDiff_snd).contDiffOn fun p hp ↦ hp.1
  · exact hu₀.comp (contDiff_fst.sub contDiff_snd).contDiffOn fun p hp ↦ hp.2

/-! ### Remark 7: the two-sided solution, by time reversal -/

variable {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The solution class only depends on the values on `[0, ∞)`.** -/
theorem IsSolution.congr (h : IsSolution Ω u₀ v₀ u) (huv : EqOn u v (Ici 0)) :
    IsSolution Ω u₀ v₀ v where
  contDiffOn := h.contDiffOn.congr fun _ ht ↦ (huv ht).symm
  contDiffOnThrough := by
    obtain ⟨w, hw, hwu⟩ := h.contDiffOnThrough
    exact ⟨w, hw, fun t ht ↦ (huv ht).symm.trans (hwu t ht)⟩
  mem_domain t ht := huv ht ▸ h.mem_domain t ht
  contDiffOnPowDomain := h.contDiffOnPowDomain.congr huv
  eqn t ht := by
    rw [← iteratedDerivWithin_congr huv ht, h.eqn t ht]
    exact congrArg (fun z ↦ -(dirichletLaplacian Ω z)) (Subtype.ext (huv ht))
  apply_zero := (huv self_mem_Ici).symm.trans h.apply_zero
  derivWithin_zero := (derivWithin_congr huv (huv self_mem_Ici)).symm.trans h.derivWithin_zero

/-- `−v₀ ∈ H¹₀(Ω)` when `v₀ ∈ H¹₀(Ω)`. -/
theorem exists_fnL_eq_neg
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = -v₀ := by
  obtain ⟨w, hw⟩ := hv₀
  exact ⟨-w, (_root_.map_neg _ w).trans (congrArg Neg.neg hw)⟩

variable (Ω) in
/-- **The two-sided solution**: `solution Ω u₀ v₀ t` for `t ≥ 0` and `solution Ω u₀ (−v₀) (−t)`
for `t < 0` ([brezis2011functional] §10.3, Remark 7). -/
def twoSidedSolution (u₀ : SobolevEuclideanZero N 1 2 Ω)
    (v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) (t : ℝ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  if 0 ≤ t then solution Ω u₀ v₀ t else solution Ω u₀ (-v₀) (-t)

/-- The two-sided solution is `solution Ω u₀ v₀` on `[0, ∞)`. -/
theorem twoSidedSolution_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    twoSidedSolution Ω u₀ v₀ t = solution Ω u₀ v₀ t :=
  ite_eq_left ht

/-- The reflected two-sided solution is `solution Ω u₀ (−v₀)` on `[0, ∞)`. -/
theorem twoSidedSolution_neg_of_nonneg
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀)
    {t : ℝ} (ht : 0 ≤ t) : twoSidedSolution Ω u₀ v₀ (-t) = solution Ω u₀ (-v₀) t := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [neg_zero, twoSidedSolution_of_nonneg le_rfl, (isSolution_solution hu₀ hv₀).apply_zero,
      (isSolution_solution hu₀ (exists_fnL_eq_neg hv₀)).apply_zero]
  · rw [twoSidedSolution, ite_eq_right (by linarith), neg_neg]

/-- **Remark 7, the forward half**: the two-sided solution solves the wave equation with data
`(u₀, v₀)`. -/
theorem isSolution_twoSidedSolution
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ v₀ (twoSidedSolution Ω u₀ v₀) :=
  (isSolution_solution hu₀ hv₀).congr fun _ ht ↦ (twoSidedSolution_of_nonneg ht).symm

/-- **Remark 7, the backward half**: the reflection `t ↦ u(−t)` of the two-sided solution solves
the wave equation with data `(u₀, −v₀)` — time reversal preserves (27)–(29) and changes the
sign of (30). -/
theorem isSolution_twoSidedSolution_neg
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    IsSolution Ω u₀ (-v₀) fun t ↦ twoSidedSolution Ω u₀ v₀ (-t) :=
  (isSolution_solution hu₀ (exists_fnL_eq_neg hv₀)).congr fun _ ht ↦
    (twoSidedSolution_neg_of_nonneg hu₀ hv₀ ht).symm

/-- **Remark 7, the two-sided problem** ([brezis2011functional] §10.3): for `fnL u₀ ∈ D(−Δ)` and
`v₀ ∈ H¹₀(Ω)` there is a unique `u : ℝ → L²(Ω)` which solves the wave equation on `[0, ∞)` with
data `(u₀, v₀)` and whose reflection `t ↦ u(−t)` solves it with data `(u₀, −v₀)` — the wave
equation is solvable backward in time, without the Dirichlet inner product of the book's
argument. Its energy at negative times is `IsSolution.energy` for the reflected solution, with
`‖−v₀‖ = ‖v₀‖` (`IsSolution.energy_neg`). -/
theorem existsUnique_isSolution_backward
    (hu₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀
      ∈ dirichletLaplacianDomain Ω)
    (hv₀ : ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = v₀) :
    ∃! u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      IsSolution Ω u₀ v₀ u ∧ IsSolution Ω u₀ (-v₀) fun t ↦ u (-t) := by
  refine ⟨twoSidedSolution Ω u₀ v₀, ⟨isSolution_twoSidedSolution hu₀ hv₀,
    isSolution_twoSidedSolution_neg hu₀ hv₀⟩, fun v ⟨hv, hv'⟩ ↦ funext fun t ↦ ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · exact (hv.eqOn_solution ht).trans (twoSidedSolution_of_nonneg ht).symm
  · have h1 := hv'.eqOn_solution (Left.nonneg_neg_iff.2 ht.le)
    simp only [neg_neg] at h1
    rw [h1, twoSidedSolution, ite_eq_right (not_le.2 ht)]

/-- **The energy at negative times**: for `u` a solution with data `(u₀, v₀)` whose reflection
solves with data `(u₀, −v₀)`, and `t ≤ 0`,
`‖∂ₜ(u(−·))(−t)‖² + ⟪−Δu(t), u(t)⟫ = ‖v₀‖² + ⟪−Δu₀, u₀⟫` — the book's `|U(t)|_H = |U₀|_H` for
all `t ∈ ℝ` in the energy norm, the two halves being `IsSolution.energy`. -/
theorem IsSolution.energy_neg (h : IsSolution Ω u₀ (-v₀) fun t ↦ u (-t))
    {t : ℝ} (ht : t ≤ 0) :
    ‖derivWithin (fun t ↦ u (-t)) (Ici 0) (-t)‖ ^ 2
      + ⟪dirichletLaplacian Ω ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u t⟫_ℝ
      = ‖v₀‖ ^ 2 + ⟪dirichletLaplacian Ω ⟨SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume u₀, h.memOperatorDomain_mk.1⟩,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
          u₀⟫_ℝ := by
  have e := h.energy (neg_nonneg.2 ht)
  have hx : (⟨u (-(-t)), h.mem_domain (-t) (neg_nonneg.2 ht)⟩ : (dirichletLaplacian Ω).domain)
      = ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩ :=
    Subtype.ext (congrArg u (neg_neg t))
  have e2 : ⟪dirichletLaplacian Ω ⟨u (-(-t)), h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u (-(-t))⟫_ℝ
      = ⟪dirichletLaplacian Ω ⟨u t, neg_neg t ▸ h.mem_domain (-t) (neg_nonneg.2 ht)⟩, u t⟫_ℝ :=
    congrArg (fun z : (dirichletLaplacian Ω).domain ↦ ⟪dirichletLaplacian Ω z,
      (z : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))⟫_ℝ) hx
  have e3 : ‖-v₀‖ ^ 2 = ‖v₀‖ ^ 2 := by rw [norm_neg]
  linarith

end Wave

/-! ### Remark 9: the eigenfunction expansion -/

section Eigen

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
  {u₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

namespace Wave.IsSolution

/-- `a_n' = ⟪u', e_n⟫` for the coefficient `a_n(t) = ⟪u(t), e_n⟫`. -/
theorem hasDerivWithinAt_inner_eigenbasis (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ (Ici 0) t := by
  have h1 := (h.contDiffOn.differentiableOn two_ne_zero t ht).hasDerivWithinAt.inner ℝ
    (hasDerivWithinAt_const t (Ici 0) (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add]

/-- `(⟪u', e_n⟫)' = ⟪u'', e_n⟫ = −⟪−Δu, e_n⟫ = −⟪u, −Δe_n⟫ = −λ_n ⟪u, e_n⟫`. -/
theorem hasDerivWithinAt_inner_derivWithin_eigenbasis (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) (Ici 0) t := by
  obtain ⟨hmem, hAe⟩ := dirichletLaplacian_apply_dirichletEigenbasis hΩ hne n
  have h1 := (h.hasDerivWithinAt_derivWithin ht).inner ℝ
    (hasDerivWithinAt_const t (Ici 0) (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_neg_left,
    dirichletLaplacian_isFormalAdjoint ⟨u t, h.mem_domain t ht⟩ ⟨_, hmem⟩, hAe, inner_smul_right,
    neg_mul]

/-- **Remark 9, the coefficients** ([brezis2011functional] §10.3): for bounded nonempty `Ω`,
the coefficients `a_n(t) = ⟪u(t), e_n⟫` of the solution in the Dirichlet eigenbasis are
`a_n(t) = ⟪u₀, e_n⟫ cos(√λ_n t) + (⟪v₀, e_n⟫ / √λ_n) sin(√λ_n t)` for `t ≥ 0`: `a_n` solves the
harmonic oscillator `a_n'' = −λ_n a_n` with `a_n(0) = ⟪u₀, e_n⟫`, `a_n'(0) = ⟪v₀, e_n⟫`
(`eq_cos_add_sin_of_hasDerivWithinAt_oscillator`). -/
theorem inner_eigenfunction (h : IsSolution Ω u₀ v₀ u) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
      = ⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
          volume u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
          * Real.cos (√(dirichletEigenvalue Ω hΩ n) * t)
        + ⟪v₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ / √(dirichletEigenvalue Ω hΩ n)
          * Real.sin (√(dirichletEigenvalue Ω hΩ n) * t) := by
  have h1 : ∀ s, 0 ≤ s → HasDerivWithinAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      ((fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) s) (Ici 0) s :=
    fun s hs ↦ h.hasDerivWithinAt_inner_eigenbasis hΩ hne n hs
  have h2 : ∀ s, 0 ≤ s → HasDerivWithinAt
      (fun t ↦ ⟪derivWithin u (Ici 0) t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) s)
      (Ici 0) s :=
    fun s hs ↦ h.hasDerivWithinAt_inner_derivWithin_eigenbasis hΩ hne n hs
  have h3 := eq_cos_add_sin_of_hasDerivWithinAt_oscillator (dirichletEigenvalue_pos Ω hΩ hne n)
    h1 h2 ht
  simp only [h.apply_zero, h.derivWithin_zero] at h3
  exact h3

/-- **Remark 9, the series** ([brezis2011functional] §10.3): for bounded nonempty `Ω` and
`t ≥ 0`, `u(t) = ∑ₙ (⟪u₀, e_n⟫ cos(√λ_n t) + (⟪v₀, e_n⟫ / √λ_n) sin(√λ_n t)) e_n` in `L²(Ω)`. -/
theorem hasSum_eigenfunction (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n ↦ (⟪SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
          * Real.cos (√(dirichletEigenvalue Ω hΩ n) * t)
        + ⟪v₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ / √(dirichletEigenvalue Ω hΩ n)
          * Real.sin (√(dirichletEigenvalue Ω hΩ n) * t)) • dirichletEigenbasis Ω hΩ hne n)
      (u t) := by
  have := (dirichletEigenbasis Ω hΩ hne).hasSum_repr (u t)
  refine this.congr_fun fun n ↦ ?_
  have e1 : (dirichletEigenbasis Ω hΩ hne).repr (u t) n
      = ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ :=
    (HilbertBasis.repr_apply_apply _ _ _).trans (real_inner_comm _ _)
  exact congrArg (fun c : ℝ ↦ c • dirichletEigenbasis Ω hΩ hne n)
    ((h.inner_eigenfunction hΩ hne n ht).symm.trans e1.symm)

end Wave.IsSolution

end Eigen

/-! ### Remark 7: the phase space with the Dirichlet inner product -/

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

section DirichletPhaseSpace

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}

variable (Ω hΩ) in
/-- **`H¹₀(Ω)` with the Dirichlet inner product `∫ ∇u·∇v`**, for bounded `Ω`: the energy space
of the operator of the Dirichlet form (`Elliptic.dirichletOperator`), an inner product equivalent
to the `H¹` one by Poincaré's inequality ([brezis2011functional] §10.3, Remark 7; chapter 9,
Remark 28). -/
abbrev dirichletEnergySpace : Type :=
  WithEnergy (dirichletOperator Ω).toLinearMap (dirichletOperator_isSymmetricCoercive Ω hΩ)

instance : CompleteSpace (dirichletEnergySpace Ω hΩ) :=
  WithEnergy.instCompleteSpace_of_continuousLinearMap _

variable (Ω hΩ) in
/-- **Remark 7's phase space** `H¹₀(Ω) × L²(Ω)` with the inner product
`⟪(u₁, v₁), (u₂, v₂)⟫ = ∫ ∇u₁·∇u₂ + ∫ v₁v₂`, for bounded `Ω`: the `ℓ²`-product of the Dirichlet
energy space and `L²(Ω)`, as a type synonym carrying its `NormedAddCommGroup` and
`InnerProductSpace` structures (as `phaseSpace`). -/
def dirichletPhaseSpace : Type :=
  WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))

instance : NormedAddCommGroup (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

instance : InnerProductSpace ℝ (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

instance : CompleteSpace (dirichletPhaseSpace Ω hΩ) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))))

namespace dirichletPhaseSpace

variable (Ω hΩ) in
/-- The point `(u, v)` of Remark 7's phase space. -/
def mk (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    dirichletPhaseSpace Ω hΩ :=
  WithLp.toLp 2 (WithEnergy.equiv _ _ u, v)

/-- The first component, read in `H¹₀(Ω)`. -/
def fst (U : dirichletPhaseSpace Ω hΩ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  (WithEnergy.equiv (dirichletOperator Ω).toLinearMap
    (dirichletOperator_isSymmetricCoercive Ω hΩ)).symm (WithLp.ofLp (U : WithLp 2
      (dirichletEnergySpace Ω hΩ
        × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))).1

/-- The second component `v ∈ L²(Ω)`. -/
def snd (U : dirichletPhaseSpace Ω hΩ) :
    Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (WithLp.ofLp (U : WithLp 2 (dirichletEnergySpace Ω hΩ
    × Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))))).2

@[simp]
theorem mk_fst (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (mk Ω hΩ u v).fst = u :=
  rfl

@[simp]
theorem mk_snd (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (mk Ω hΩ u v).snd = v :=
  rfl

/-- Two points with the same components are equal. -/
theorem ext {U V : dirichletPhaseSpace Ω hΩ} (h1 : U.fst = V.fst) (h2 : U.snd = V.snd) : U = V :=
  WithLp.ofLp_injective 2 (Prod.ext ((WithEnergy.equiv _ _).symm.injective h1) h2)

/-- **The inner product of Remark 7**: `⟪U₁, U₂⟫ = ∫ ∇u₁·∇u₂ + ⟪v₁, v₂⟫_{L²}`. -/
theorem inner_def (U V : dirichletPhaseSpace Ω hΩ) :
    ⟪U, V⟫_ℝ = dirichletForm Ω (U.fst : SobolevEuclidean (d + 1) 1 2 Ω)
      (V.fst : SobolevEuclidean (d + 1) 1 2 Ω) + ⟪U.snd, V.snd⟫_ℝ :=
  congrArg (· + ⟪U.snd, V.snd⟫_ℝ) (inner_dirichletOperator Ω U.fst V.fst)

/-- **`‖(u, v)‖² = ∫ |∇u|² + ‖v‖²_{L²}`**. -/
theorem norm_sq_eq (U : dirichletPhaseSpace Ω hΩ) :
    ‖U‖ ^ 2 = dirichletForm Ω (U.fst : SobolevEuclidean (d + 1) 1 2 Ω)
      (U.fst : SobolevEuclidean (d + 1) 1 2 Ω) + ‖U.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def, real_inner_self_eq_norm_sq]

@[simp]
theorem add_fst (U V : dirichletPhaseSpace Ω hΩ) : (U + V).fst = U.fst + V.fst :=
  rfl

@[simp]
theorem add_snd (U V : dirichletPhaseSpace Ω hΩ) : (U + V).snd = U.snd + V.snd :=
  rfl

@[simp]
theorem smul_fst (c : ℝ) (U : dirichletPhaseSpace Ω hΩ) : (c • U).fst = c • U.fst :=
  rfl

@[simp]
theorem smul_snd (c : ℝ) (U : dirichletPhaseSpace Ω hΩ) : (c • U).snd = c • U.snd :=
  rfl

@[simp]
theorem zero_fst : (0 : dirichletPhaseSpace Ω hΩ).fst = 0 :=
  rfl

@[simp]
theorem zero_snd : (0 : dirichletPhaseSpace Ω hΩ).snd = 0 :=
  rfl

@[simp]
theorem neg_fst (U : dirichletPhaseSpace Ω hΩ) : (-U).fst = -U.fst :=
  rfl

@[simp]
theorem neg_snd (U : dirichletPhaseSpace Ω hΩ) : (-U).snd = -U.snd :=
  rfl

/-- `(u + u', v + v') = (u, v) + (u', v')`. -/
theorem mk_add (u u' : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v v' : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    mk Ω hΩ (u + u') (v + v') = mk Ω hΩ u v + mk Ω hΩ u' v' :=
  rfl

/-- `(c • u, c • v) = c • (u, v)`. -/
theorem mk_smul (c : ℝ) (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    mk Ω hΩ (c • u) (c • v) = c • mk Ω hΩ u v :=
  rfl

/-- **The two-sided comparison with `phaseSpace Ω`**: `‖(u, v)‖²_{Remark 7} ≤ ‖(u, v)‖²_{(34)}`
(the Dirichlet form is bounded by the `H¹` norm). -/
theorem norm_sq_le (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
    (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ‖mk Ω hΩ u v‖ ^ 2 ≤ ‖phaseSpace.mk Ω u v‖ ^ 2 := by
  rw [norm_sq_eq, phaseSpace.norm_sq_eq, mk_fst, mk_snd, phaseSpace.mk_fst, phaseSpace.mk_snd]
  have h1 := dirichletForm_self_le Ω (u : SobolevEuclidean (d + 1) 1 2 Ω)
  have h2 : ‖(u : SobolevEuclidean (d + 1) 1 2 Ω)‖ ^ 2 = ‖u‖ ^ 2 := rfl
  linarith

/-- **The two-sided comparison with `phaseSpace Ω`, the other half** (Poincaré's inequality,
`Elliptic.dirichletForm_restrict_isCoercive`): `c ‖(u, v)‖²_{(34)} ≤ ‖(u, v)‖²_{Remark 7}` for
some `c > 0`. -/
theorem exists_norm_sq_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : SobolevEuclideanZero (d + 1) 1 2 Ω)
      (v : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
      c * ‖phaseSpace.mk Ω u v‖ ^ 2 ≤ ‖mk Ω hΩ u v‖ ^ 2 := by
  obtain ⟨c, hc, hcoer⟩ := dirichletForm_restrict_isCoercive Ω hΩ
  refine ⟨min c 1, lt_min hc one_pos, fun u v ↦ ?_⟩
  rw [norm_sq_eq, phaseSpace.norm_sq_eq, mk_fst, mk_snd, phaseSpace.mk_fst, phaseSpace.mk_snd]
  have h1 : c * ‖u‖ ^ 2 ≤ dirichletForm Ω (u : SobolevEuclidean (d + 1) 1 2 Ω)
      (u : SobolevEuclidean (d + 1) 1 2 Ω) := hcoer u
  have h2 := min_le_left c 1
  have h3 := min_le_right c 1
  have h4 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have h5 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith

end dirichletPhaseSpace

end DirichletPhaseSpace

/-! ### Remark 7: the wave operator on the Dirichlet phase space -/

section DirichletOperator

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))}

variable (Ω hΩ) in
/-- The domain condition of `operator'`: `(u, v)` with `fnL u ∈ D(−Δ)` and `v ∈ H¹₀(Ω)`
(`MemOperatorDomain` read in Remark 7's phase space). -/
def MemOperatorDomain' (U : dirichletPhaseSpace Ω hΩ) : Prop :=
  SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume U.fst
    ∈ dirichletLaplacianDomain Ω ∧ ∃ w : SobolevEuclideanZero (d + 1) 1 2 Ω,
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume w
      = U.snd

/-- The domain condition is that of `operator Ω`, through `phaseSpace.mk`. -/
theorem memOperatorDomain'_iff {U : dirichletPhaseSpace Ω hΩ} :
    MemOperatorDomain' Ω hΩ U ↔ MemOperatorDomain Ω (phaseSpace.mk Ω U.fst U.snd) :=
  Iff.rfl

/-- `0 ∈ D(A)`. -/
theorem memOperatorDomain'_zero : MemOperatorDomain' Ω hΩ (0 : dirichletPhaseSpace Ω hΩ) :=
  memOperatorDomain_zero

/-- `D(A)` is closed under addition. -/
theorem MemOperatorDomain'.add {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) : MemOperatorDomain' Ω hΩ (U + V) :=
  MemOperatorDomain.add (Ω := Ω) (U := phaseSpace.mk Ω U.fst U.snd)
    (V := phaseSpace.mk Ω V.fst V.snd) hU hV

/-- `D(A)` is closed under scalar multiplication. -/
theorem MemOperatorDomain'.smul (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) : MemOperatorDomain' Ω hΩ (c • U) :=
  MemOperatorDomain.smul (Ω := Ω) c (U := phaseSpace.mk Ω U.fst U.snd) hU

variable (Ω hΩ) in
/-- The domain `D(A) = D(−Δ) × H¹₀(Ω)` in Remark 7's phase space. -/
def operatorDomain' : Submodule ℝ (dirichletPhaseSpace Ω hΩ) where
  carrier := {U | MemOperatorDomain' Ω hΩ U}
  zero_mem' := memOperatorDomain'_zero
  add_mem' := fun hU hV ↦ hU.add hV
  smul_mem' := fun c _ hU ↦ hU.smul c

variable (Ω hΩ) in
/-- The value `A(u, v) = (−ṽ, −Δu)` in Remark 7's phase space. -/
def operatorApply' (U : dirichletPhaseSpace Ω hΩ) : dirichletPhaseSpace Ω hΩ :=
  dirichletPhaseSpace.mk Ω hΩ (-toSobolevZero Ω U.snd) (dirichletLaplacianApply Ω
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      U.fst))

/-- The first component of `A(U + V)`. -/
theorem operatorApply'_add_fst {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) :
    (operatorApply' Ω hΩ (U + V)).fst = (operatorApply' Ω hΩ U + operatorApply' Ω hΩ V).fst := by
  change -toSobolevZero Ω (U.snd + V.snd) = -toSobolevZero Ω U.snd + -toSobolevZero Ω V.snd
  rw [toSobolevZero_add hU.2 hV.2, neg_add]

/-- The second component of `A(U + V)`. -/
theorem operatorApply'_add_snd {U V : dirichletPhaseSpace Ω hΩ} (hU : MemOperatorDomain' Ω hΩ U)
    (hV : MemOperatorDomain' Ω hΩ V) :
    (operatorApply' Ω hΩ (U + V)).snd = (operatorApply' Ω hΩ U + operatorApply' Ω hΩ V).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (U.fst + V.fst)) = _ + _
  rw [_root_.map_add]
  exact dirichletLaplacianApply_add hU.1 hV.1

/-- The first component of `A(c • U)`. -/
theorem operatorApply'_smul_fst (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) :
    (operatorApply' Ω hΩ (c • U)).fst = (c • operatorApply' Ω hΩ U).fst := by
  change -toSobolevZero Ω (c • U.snd) = c • -toSobolevZero Ω U.snd
  rw [toSobolevZero_smul c hU.2, smul_neg]

/-- The second component of `A(c • U)`. -/
theorem operatorApply'_smul_snd (c : ℝ) {U : dirichletPhaseSpace Ω hΩ}
    (hU : MemOperatorDomain' Ω hΩ U) :
    (operatorApply' Ω hΩ (c • U)).snd = (c • operatorApply' Ω hΩ U).snd := by
  change dirichletLaplacianApply Ω
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (c • U.fst)) = c • _
  rw [_root_.map_smul]
  exact dirichletLaplacianApply_smul c hU.1

variable (Ω hΩ) in
/-- **Remark 7's wave operator** `A(u, v) = (−v, −Δu)` on the phase space with the Dirichlet inner
product, the same map as `operator Ω` on the same domain `D(−Δ) × H¹₀(Ω)`
([brezis2011functional] §10.3, Remark 7). -/
def operator' : dirichletPhaseSpace Ω hΩ →ₗ.[ℝ] dirichletPhaseSpace Ω hΩ where
  domain := operatorDomain' Ω hΩ
  toFun :=
    { toFun := fun U ↦ operatorApply' Ω hΩ U
      map_add' := fun U V ↦ dirichletPhaseSpace.ext (operatorApply'_add_fst U.2 V.2)
        (operatorApply'_add_snd U.2 V.2)
      map_smul' := fun c U ↦ dirichletPhaseSpace.ext (operatorApply'_smul_fst c U.2)
        (operatorApply'_smul_snd c U.2) }

/-- Membership of the domain of `operator'`: `(u, v)` with `fnL u ∈ D(−Δ)` and `v ∈ H¹₀(Ω)`. -/
theorem mem_operator'_domain_iff {U : dirichletPhaseSpace Ω hΩ} :
    U ∈ (operator' Ω hΩ).domain ↔ MemOperatorDomain' Ω hΩ U :=
  Iff.rfl

/-- The first component of `A(u, v)` is `−ṽ`. -/
theorem operator'_apply_fst (U : (operator' Ω hΩ).domain) :
    (operator' Ω hΩ U).fst = -toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :=
  rfl

/-- The second component of `A(u, v)` is `−Δu`. -/
theorem operator'_apply_snd (U : (operator' Ω hΩ).domain) :
    (operator' Ω hΩ U).snd = dirichletLaplacian Ω
      ⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (U : dirichletPhaseSpace Ω hΩ).fst, (mem_operator'_domain_iff.1 U.2).1⟩ :=
  rfl

/-- **`⟪A U, U⟫ = 0`** in Remark 7's inner product: `−∫ ∇ṽ·∇u + ⟪−Δu, v⟫ = 0` by
`dirichletLaplacian_inner_eq_dirichletForm` ([brezis2011functional] §10.3, Remark 7). -/
theorem operator'_inner_self_eq_zero (U : (operator' Ω hΩ).domain) :
    ⟪operator' Ω hΩ U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ = 0 := by
  have hmem := mem_operator'_domain_iff.1 U.2
  have hwv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd)
      = (U : dirichletPhaseSpace Ω hΩ).snd :=
    fnL_toSobolevZero hmem.2
  have h0 := dirichletPhaseSpace.inner_def (operator' Ω hΩ U) (U : dirichletPhaseSpace Ω hΩ)
  have h1 : dirichletForm Ω ((operator' Ω hΩ U).fst : SobolevEuclidean (d + 1) 1 2 Ω)
      ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)
      = -dirichletForm Ω (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :
          SobolevEuclidean (d + 1) 1 2 Ω)
        ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (congrArg (fun z ↦ dirichletForm Ω z
      ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω))
      (Submodule.coe_neg _ (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd))).trans
      ((congrArg (fun L : SobolevEuclidean (d + 1) 1 2 Ω →L[ℝ] ℝ ↦
        L ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω))
        (_root_.map_neg (dirichletForm Ω)
          (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd :
            SobolevEuclidean (d + 1) 1 2 Ω))).trans
        (neg_apply _ _))
  have h2 : ⟪(operator' Ω hΩ U).snd, (U : dirichletPhaseSpace Ω hΩ).snd⟫_ℝ
      = dirichletForm Ω ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)
        (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd : SobolevEuclidean (d + 1) 1 2 Ω) :=
    (congrArg (fun z ↦ ⟪(operator' Ω hΩ U).snd, z⟫_ℝ) hwv).symm.trans
      (dirichletLaplacian_inner_eq_dirichletForm ⟨_, hmem.1⟩
        (U : dirichletPhaseSpace Ω hΩ).fst.2 rfl
        (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd).2)
  have h3 := (dirichletForm_isHermitian Ω
    (toSobolevZero Ω (U : dirichletPhaseSpace Ω hΩ).snd : SobolevEuclidean (d + 1) 1 2 Ω)
    ((U : dirichletPhaseSpace Ω hΩ).fst : SobolevEuclidean (d + 1) 1 2 Ω)).trans (conj_trivial _)
  linarith

/-- **Remark 7 (i)**: `A` is monotone on Remark 7's phase space, `⟪A U, U⟫ = 0`. -/
theorem operator'_isMonotone : (operator' Ω hΩ).IsMonotone := fun U ↦ by
  change (0 : ℝ) ≤ ⟪operator' Ω hΩ U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ
  rw [operator'_inner_self_eq_zero]

/-- **Remark 7 (i)**: `−A` is monotone on Remark 7's phase space. -/
theorem neg_operator'_isMonotone : (-operator' Ω hΩ).IsMonotone := fun U ↦ by
  change (0 : ℝ) ≤ ⟪(-operator' Ω hΩ) U, (U : dirichletPhaseSpace Ω hΩ)⟫_ℝ
  rw [LinearPMap.neg_apply, inner_neg_left, operator'_inner_self_eq_zero, neg_zero]

/-- From `x + a = g + f`: `(x − f) + a = g` (stated once, so that the rewriting happens on the
abstract group and not on the `L²` terms). -/
private theorem sub_add_eq_of_add_eq {E : Type*} [AddCommGroup E] {x f g a : E}
    (h : x + a = g + f) : x - f + a = g := by
  rw [sub_add_eq_add_sub, h, add_sub_cancel_right]

/-- From `x + a = f − g`: `(f − x) − a = g`. -/
private theorem sub_sub_eq_of_add_eq {E : Type*} [AddCommGroup E] {x f g a : E}
    (h : x + a = f - g) : f - x - a = g := by
  rw [sub_sub, h, sub_sub_cancel]

/-- **Remark 7 (ii), `R(I + A) = H`**: for `F = (f, g)` solve `−Δu + u = g + f` in `D(−Δ)`
(`dirichletLaplacian_exists_add_apply_eq`) and take `v := fnL (u − f)`
([brezis2011functional] §10.3, Remark 7). -/
theorem operator'_exists_add_apply_eq (F : dirichletPhaseSpace Ω hΩ) :
    ∃ U : (operator' Ω hΩ).domain,
      (U : dirichletPhaseSpace Ω hΩ) + operator' Ω hΩ U = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_add_apply_eq (Ω := Ω) (F.snd
    + SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      F.fst)
  obtain ⟨u, hux⟩ := dirichletLaplacian_exists_sobolevZero_lift x
  have hmem : MemOperatorDomain' Ω hΩ (dirichletPhaseSpace.mk Ω hΩ u
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (u - F.fst))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume u ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, dirichletPhaseSpace.ext ?_ ?_⟩
  · change u + -toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (u - F.fst)) = F.fst
    exact (congrArg (fun z ↦ u + -z) (toSobolevZero_fnL (u - F.fst))).trans
      (by abel)
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (u - F.fst) + dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (u - F.fst)
        = (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          - SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
            volume F.fst :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume) u F.fst).trans (congrArg (fun z ↦ z - SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst) hux)
    refine (congrArg₂ (fun a b ↦ a + dirichletLaplacianApply Ω b) h1 hux).trans ?_
    exact sub_add_eq_of_add_eq hx

/-- **Remark 7 (ii), `R(I − A) = H`**: for `F = (f, g)` solve `−Δu + u = f − g` in `D(−Δ)` and
take `v := fnL (f − u)`. -/
theorem neg_operator'_exists_add_apply_eq (F : dirichletPhaseSpace Ω hΩ) :
    ∃ U : (-operator' Ω hΩ).domain,
      (U : dirichletPhaseSpace Ω hΩ) + (-operator' Ω hΩ) U = F := by
  obtain ⟨x, hx⟩ := dirichletLaplacian_exists_add_apply_eq (Ω := Ω)
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      F.fst - F.snd)
  obtain ⟨u, hux⟩ := dirichletLaplacian_exists_sobolevZero_lift x
  have hmem : MemOperatorDomain' Ω hΩ (dirichletPhaseSpace.mk Ω hΩ u
      (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
        (F.fst - u))) := by
    refine ⟨?_, ⟨_, rfl⟩⟩
    change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume u ∈ dirichletLaplacianDomain Ω
    rw [hux]
    exact x.2
  refine ⟨⟨_, hmem⟩, dirichletPhaseSpace.ext ?_ ?_⟩
  · change u + -(-toSobolevZero Ω (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (F.fst - u))) = F.fst
    exact (congrArg (fun z ↦ u + -(-z)) (toSobolevZero_fnL (F.fst - u))).trans
      ((congrArg (fun z ↦ u + z) (neg_neg (F.fst - u))).trans (add_sub_cancel u F.fst))
  · change SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume (F.fst - u) + -dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume u) = F.snd
    have h1 : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
        volume (F.fst - u) = SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst
          - (x : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :=
      (_root_.map_sub (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        1 2 Ω volume) F.fst u).trans (congrArg (fun z ↦ SobolevMultiIndexZero.fnL ℝ
          (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume F.fst - z) hux)
    refine (congrArg₂ (fun a b ↦ a + -dirichletLaplacianApply Ω b) h1 hux).trans ?_
    rw [← sub_eq_add_neg]
    exact sub_sub_eq_of_add_eq hx

/-- **Remark 7 (i)–(ii): `A` is maximal monotone** on the phase space with the Dirichlet inner
product ([brezis2011functional] §10.3, Remark 7). -/
theorem operator'_isMaximalMonotone : (operator' Ω hΩ).IsMaximalMonotone :=
  ⟨operator'_isMonotone, operator'_exists_add_apply_eq⟩

/-- **Remark 7 (i)–(ii): `−A` is maximal monotone** on the phase space with the Dirichlet inner
product, so that the wave equation is solvable backward in time. -/
theorem neg_operator'_isMaximalMonotone : (-operator' Ω hΩ).IsMaximalMonotone :=
  ⟨neg_operator'_isMonotone, neg_operator'_exists_add_apply_eq⟩

end DirichletOperator

end Wave

namespace Wave

/-! ### Remark 10: the compatibility conditions are necessary -/

section Classical

open Heat Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Set E} {T : ℝ} {u : E × ℝ → ℝ}

/-- **A classical solution of the wave equation** `∂ₜₜ u = Δ u` on the open cylinder
`Ω × (0, T)`, for a function `u : E × ℝ → ℝ` of space and time: the equation holds pointwise
there, written with the operators `Heat.timeDeriv` (`∂ₜ`) and `Heat.spaceLaplacian` (`Δ_x`) of
`Numlib/Analysis/PDE/Heat/Classical`. No regularity, boundary or initial condition is bundled;
Remark 10 of [brezis2011functional] chapter 10 assumes `u` smooth on `E × ℝ` beside it. -/
structure IsClassicalSolution (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- The wave equation `∂ₜₜ u = Δ_x u` on the open cylinder. -/
  eqn : EqOn (timeDeriv (timeDeriv u)) (spaceLaplacian u) (Ω ×ˢ Ioo 0 T)

/-- **The iterated wave equation**: a smooth classical solution of `∂ₜₜ u = Δ_x u` on
`Ω × (0, T)` satisfies `∂ₜ^{2j} u = Δ_x^j u` and `∂ₜ^{2j+1} u = Δ_x^j ∂ₜ u` there, for every `j`:
by induction, using the commutation `∂ₜ Δ_x^j = Δ_x^j ∂ₜ` of smooth functions
(`Heat.timeDeriv_spaceLaplacian_iterate`) and the locality of both operators on the open
cylinder. -/
theorem IsClassicalSolution.timeDeriv_iterate_eqOn (hΩ : IsOpen Ω)
    (hu : IsClassicalSolution Ω T u) (hsmooth : ContDiff ℝ ∞ u) (j : ℕ) :
    EqOn (timeDeriv^[2 * j] u) (spaceLaplacian^[j] u) (Ω ×ˢ Ioo 0 T) ∧
      EqOn (timeDeriv^[2 * j + 1] u) (spaceLaplacian^[j] (timeDeriv u)) (Ω ×ˢ Ioo 0 T) := by
  have hV : IsOpen (Ω ×ˢ Ioo 0 T) := hΩ.prod isOpen_Ioo
  induction j with
  | zero => exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have h2 : EqOn (timeDeriv^[2 * (j + 1)] u) (spaceLaplacian^[j + 1] u) (Ω ×ˢ Ioo 0 T) := by
      intro p hp
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Function.iterate_succ_apply',
        timeDeriv_eqOn hV h1 hp, timeDeriv_spaceLaplacian_iterate (contDiff_timeDeriv hsmooth) j,
        spaceLaplacian_iterate_eqOn hV hu.eqn j hp, Function.iterate_succ_apply]
    refine ⟨h2, fun p hp ↦ ?_⟩
    rw [Function.iterate_succ_apply', timeDeriv_eqOn hV h2 hp,
      timeDeriv_spaceLaplacian_iterate hsmooth (j + 1)]

/-- **Remark 10: the compatibility conditions of Theorem 10.8 are necessary**
([brezis2011functional] chapter 10, Remark 10). Let `u` be a classical solution of the wave
equation `∂ₜₜ u = Δ u` on the cylinder `Ω × (0, T)` (`T > 0`, `Ω` open) which is `C^∞` on
`E × ℝ` and vanishes on the lateral boundary `frontier Ω × (0, T)`. Then the data
`u₀ = u(·, 0)` and `v₀ = ∂ₜu(·, 0)` satisfy `Δ^j u₀ = 0` and `Δ^j v₀ = 0` on `frontier Ω` for
every `j`.

Proof, as for the heat equation (`Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`,
Remark 4): `∂ₜ^{2j} u = Δ_x^j u` and `∂ₜ^{2j+1} u = Δ_x^j ∂ₜ u` on `Ω × (0, T)`
(`IsClassicalSolution.timeDeriv_iterate_eqOn`); all time derivatives of `u` vanish on
`frontier Ω × (0, T)`, hence at `(x, 0)` for `x ∈ frontier Ω` by continuity
(`timeDeriv_iterate_apply_zero_eq_zero`); both sides of the identities are continuous on
`E × ℝ`, so they pass to `closure Ω × [0, T]`, and comparing them at `(x, 0)` gives the
conditions through `Heat.spaceLaplacian_iterate_slice`.

The book states the remark for `u ∈ C^∞(Ω̄ × [0, ∞))` in the sense of chapter 9's footnote 16,
where `Δ^j u₀` on the boundary refers to continuous extensions; the smoothness of `u` on all of
`E × ℝ` assumed here makes the statement meaningful as written. -/
theorem IsClassicalSolution.iteratedLaplacian_eq_zero_frontier (hΩ : IsOpen Ω) (hT : 0 < T)
    (hu : IsClassicalSolution Ω T u) (hsmooth : ContDiff ℝ ∞ u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier Ω, (Laplacian.laplacian^[j] fun y ↦ u (y, 0)) x = 0 ∧
      (Laplacian.laplacian^[j] fun y ↦ timeDeriv u (y, 0)) x = 0 := by
  intro x hx
  obtain ⟨h0, h1⟩ := hu.timeDeriv_iterate_eqOn hΩ hsmooth j
  have hcl : closure Ω ×ˢ Icc 0 T ⊆ closure (Ω ×ˢ Ioo 0 T) := by
    rw [closure_prod_eq, closure_Ioo hT.ne]
  have hsub : Ω ×ˢ Ioo 0 T ⊆ closure Ω ×ˢ Icc 0 T := prod_mono subset_closure Ioo_subset_Icc_self
  have hx0 : (x, (0 : ℝ)) ∈ closure Ω ×ˢ Icc 0 T :=
    ⟨frontier_subset_closure hx, left_mem_Icc.2 hT.le⟩
  constructor
  · -- `Δ^j u (x, 0) = ∂ₜ^{2j} u (x, 0) = 0`
    have h := h0.of_subset_closure (contDiff_timeDeriv_iterate hsmooth _).continuous.continuousOn
      (contDiff_spaceLaplacian_iterate hsmooth j).continuous.continuousOn hsub hcl hx0
    rw [← spaceLaplacian_iterate_slice]
    exact h.symm.trans (timeDeriv_iterate_apply_zero_eq_zero hT hsmooth (hΓ x hx) _)
  · -- `Δ^j ∂ₜ u (x, 0) = ∂ₜ^{2j+1} u (x, 0) = 0`
    have h := h1.of_subset_closure (contDiff_timeDeriv_iterate hsmooth _).continuous.continuousOn
      (contDiff_spaceLaplacian_iterate (contDiff_timeDeriv hsmooth) j).continuous.continuousOn
      hsub hcl hx0
    rw [← spaceLaplacian_iterate_slice]
    exact h.symm.trans (timeDeriv_iterate_apply_zero_eq_zero hT hsmooth (hΓ x hx) _)

end Classical

end Wave

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic

section LaplacianDomain

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The domains `D_m` of the Dirichlet Laplacian, and `D(A^k)` -/

variable (Ω) in
/-- **The `m`-th domain `D_m` of the Dirichlet Laplacian**, the space the book's display in the
proof of Theorem 10.8 calls `{w ∈ H^m(Ω) : Δ^j w = 0 on Γ for 2j < m}` before the Sobolev
spaces are read in ([brezis2011functional] §10.3): `D_0 = L²(Ω)`, `D_1 = H¹₀(Ω)` (the range of
`fnL`), and `D_{m+2} = {f ∈ D(−Δ) : −Δ f ∈ D_m}`, so that `D_{2ℓ} = D((−Δ)^ℓ)` and
`D_{2ℓ+1} = {f ∈ D((−Δ)^ℓ) : (−Δ)^ℓ f ∈ H¹₀(Ω)}` (`memLaplacianDomain_two_mul_iff`,
`memLaplacianDomain_two_mul_add_one_iff`). The domain of the `k`-th power of the wave operator
is `D_{k+1} × D_k` (`mem_operator_powGraph_iff`). -/
def MemLaplacianDomain :
    ℕ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) → Prop
  | 0, _ => True
  | 1, f => ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w = f
  | m + 2, f => f ∈ dirichletLaplacianDomain Ω ∧
      MemLaplacianDomain m (dirichletLaplacianApply Ω f)

variable {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- `D_0 = L²(Ω)`. -/
theorem memLaplacianDomain_zero : MemLaplacianDomain Ω 0 f := trivial

/-- `D_1 = H¹₀(Ω)`. -/
theorem memLaplacianDomain_one_iff :
    MemLaplacianDomain Ω 1 f ↔ ∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = f :=
  Iff.rfl

/-- `D_{m+2} = {f ∈ D(−Δ) : −Δ f ∈ D_m}`. -/
theorem memLaplacianDomain_add_two_iff {m : ℕ} :
    MemLaplacianDomain Ω (m + 2) f ↔ f ∈ dirichletLaplacianDomain Ω ∧
      MemLaplacianDomain Ω m (dirichletLaplacianApply Ω f) :=
  Iff.rfl

/-- `D_m` is closed under scalar multiplication. -/
theorem MemLaplacianDomain.smul {m : ℕ} (c : ℝ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω m f → MemLaplacianDomain Ω m (c • f) := by
  induction m using Nat.twoStepInduction with
  | zero => intro f _; trivial
  | one =>
    rintro f ⟨w, hw⟩
    exact ⟨c • w, by rw [_root_.map_smul, hw]⟩
  | more m ih _ =>
    rintro f ⟨hf, hf'⟩
    refine ⟨Submodule.smul_mem _ c hf, ?_⟩
    rw [dirichletLaplacianApply_smul c hf]
    exact ih hf'

/-- `D_m` is closed under negation. -/
theorem MemLaplacianDomain.neg {m : ℕ} (h : MemLaplacianDomain Ω m f) :
    MemLaplacianDomain Ω m (-f) := by
  simpa using h.smul (-1)

/-- `−f ∈ D_m` iff `f ∈ D_m`. -/
theorem memLaplacianDomain_neg_iff {m : ℕ} :
    MemLaplacianDomain Ω m (-f) ↔ MemLaplacianDomain Ω m f :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩

/-- `D_{m+1} ⊆ H¹₀(Ω)`. -/
theorem MemLaplacianDomain.exists_fnL_eq {m : ℕ} :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (m + 1) f → ∃ w : SobolevEuclideanZero N 1 2 Ω,
        SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
          = f := by
  cases m with
  | zero => intro f h; exact h
  | succ m => rintro f ⟨hf, -⟩; exact dirichletLaplacian_exists_sobolevZero_lift ⟨f, hf⟩

/-- `f ∈ D_{m+1}` iff `f ∈ H¹₀(Ω)` and `−f ∈ D_{m+1}` (the form met in the induction of
`mem_operator_powGraph_iff`). -/
theorem memLaplacianDomain_succ_iff_neg {m : ℕ} :
    MemLaplacianDomain Ω (m + 1) f ↔ (∃ w : SobolevEuclideanZero N 1 2 Ω,
      SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume w
        = f) ∧ MemLaplacianDomain Ω (m + 1) (-f) :=
  ⟨fun h ↦ ⟨h.exists_fnL_eq, h.neg⟩, fun h ↦ memLaplacianDomain_neg_iff.1 h.2⟩

/-- The conditions `D_{k+1} × D_k` on `A U = (−v, −Δu)` are the conditions `v ∈ D_{k+1}`,
`−Δ u ∈ D_k` on `U = (u, v)`. -/
theorem memLaplacianDomain_operator_apply_iff (k : ℕ) (U : (operator Ω).domain) :
    (MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (operator Ω U).fst) ∧
      MemLaplacianDomain Ω k (operator Ω U).snd) ↔
    (MemLaplacianDomain Ω (k + 1) (U : phaseSpace Ω).snd ∧
      MemLaplacianDomain Ω k (dirichletLaplacianApply Ω (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume (U : phaseSpace Ω).fst))) := by
  rw [fnL_operator_apply_fst, memLaplacianDomain_neg_iff]
  exact Iff.rfl

/-- **`D(A^k) = D_{k+1} × D_k`** ([brezis2011functional] §10.3, the display in the proof of
Theorem 10.8 read on the weak domains): `(u, v)` is the base point of an element of
`D(A^k)` (`LinearPMap.PowDomain`) iff `fnL u ∈ D_{k+1}` and `v ∈ D_k`. Induction on `k`
through `D(A^{k+1}) = {U ∈ D(A) : A U ∈ D(A^k)}`
(`LinearPMap.PowDomain.exists_applyL_zero_eq_succ_iff`) and `A(u, v) = (−v, −Δu)`. -/
theorem mem_operator_powGraph_iff (k : ℕ) (U : phaseSpace Ω) :
    (∃ x : (operator Ω).PowDomain k, applyL (operator Ω) k 0 x = U) ↔
      MemLaplacianDomain Ω (k + 1) (SobolevMultiIndexZero.fnL ℝ
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume U.fst) ∧
      MemLaplacianDomain Ω k U.snd := by
  induction k generalizing U with
  | zero =>
    refine ⟨fun _ ↦ ⟨⟨U.fst, rfl⟩, trivial⟩, fun _ ↦ ?_⟩
    exact ⟨LinearPMap.PowDomain.mk (operator Ω) (fun _ ↦ U) fun i ↦ i.elim0, rfl⟩
  | succ k ih =>
    rw [exists_applyL_zero_eq_succ_iff]
    constructor
    · rintro ⟨hU, y, hy⟩
      have h1 := (memLaplacianDomain_operator_apply_iff k ⟨U, hU⟩).1 ((ih _).1 ⟨y, hy⟩)
      obtain ⟨hU1, -⟩ := mem_operator_domain_iff.1 hU
      exact ⟨⟨hU1, h1.2⟩, h1.1⟩
    · rintro ⟨⟨hU1, hU2⟩, hv⟩
      have hU : U ∈ (operator Ω).domain := mem_operator_domain_iff.2 ⟨hU1, hv.exists_fnL_eq⟩
      exact ⟨hU, (ih _).2 ((memLaplacianDomain_operator_apply_iff k ⟨U, hU⟩).2 ⟨hv, hU2⟩)⟩

/-- The inductive step of `D_{2ℓ} = D((−Δ)^ℓ)`, forward: `f ∈ D(−Δ)` with `−Δ f ∈ D((−Δ)^ℓ)`
gives `f ∈ D((−Δ)^{ℓ+1})` (`LinearPMap.PowDomain.cons`). -/
theorem exists_powDomain_succ_of_apply {ℓ : ℕ} (hf : f ∈ dirichletLaplacianDomain Ω)
    (y : (dirichletLaplacian Ω).PowDomain ℓ)
    (hy : applyL (dirichletLaplacian Ω) ℓ 0 y = dirichletLaplacianApply Ω f) :
    ∃ x : (dirichletLaplacian Ω).PowDomain (ℓ + 1),
      applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x = f :=
  ⟨cons ⟨f, hf⟩ y ((dirichletLaplacian_apply ⟨f, hf⟩).trans hy.symm), applyL_cons_zero _ _ _⟩

/-- The inductive step of `D_{2ℓ} = D((−Δ)^ℓ)`, backward: `f ∈ D((−Δ)^{ℓ+1})` lies in `D(−Δ)`
with `−Δ f ∈ D((−Δ)^ℓ)` (`LinearPMap.PowDomain.shiftL`). -/
theorem mem_and_exists_powDomain_of_powDomain_succ {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain (ℓ + 1))
    (hx : applyL (dirichletLaplacian Ω) (ℓ + 1) 0 x = f) :
    f ∈ dirichletLaplacianDomain Ω ∧ ∃ y : (dirichletLaplacian Ω).PowDomain ℓ,
      applyL (dirichletLaplacian Ω) ℓ 0 y = dirichletLaplacianApply Ω f := by
  have hf : f ∈ dirichletLaplacianDomain Ω := by
    rw [← hx]
    exact applyL_mem_domain x 0
  exact ⟨hf, shiftL (dirichletLaplacian Ω) ℓ x, (applyL_zero_shiftL x).trans
    ((dirichletLaplacian_apply _).trans (congrArg (dirichletLaplacianApply Ω) hx))⟩

/-- **`D_{2ℓ} = D((−Δ)^ℓ)`**: `f ∈ D_{2ℓ}` iff `f` is the base point of an element of
`(dirichletLaplacian Ω).PowDomain ℓ`. -/
theorem memLaplacianDomain_two_mul_iff (ℓ : ℕ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (2 * ℓ) f ↔
        ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = f := by
  induction ℓ with
  | zero =>
    intro f
    exact ⟨fun _ ↦ ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) (fun _ ↦ f) fun i ↦ i.elim0,
      applyL_mk _ _ 0⟩, fun _ ↦ trivial⟩
  | succ ℓ ih =>
    intro f
    change MemLaplacianDomain Ω (2 * ℓ + 2) f ↔ _
    refine memLaplacianDomain_add_two_iff.trans ((and_congr_right fun _ ↦ ih).trans ?_)
    constructor
    · rintro ⟨hf, y, hy⟩
      exact exists_powDomain_succ_of_apply hf y hy
    · rintro ⟨x, hx⟩
      exact mem_and_exists_powDomain_of_powDomain_succ x hx

/-- **`D_{2ℓ+1} = {f ∈ D((−Δ)^ℓ) : (−Δ)^ℓ f ∈ H¹₀(Ω)}`**: `f ∈ D_{2ℓ+1}` iff `f` is the base
point of an element `x` of `(dirichletLaplacian Ω).PowDomain ℓ` whose last coordinate lies in
`H¹₀(Ω)`. -/
theorem memLaplacianDomain_two_mul_add_one_iff (ℓ : ℕ) :
    ∀ {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))},
      MemLaplacianDomain Ω (2 * ℓ + 1) f ↔
        ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = f ∧
          ∃ w : SobolevEuclideanZero N 1 2 Ω,
            SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
              w = applyL (dirichletLaplacian Ω) ℓ (Fin.last ℓ) x := by
  induction ℓ with
  | zero =>
    intro f
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨LinearPMap.PowDomain.mk (dirichletLaplacian Ω) (fun _ ↦ f) fun i ↦ i.elim0,
        applyL_mk _ _ 0, w, hw.trans (applyL_mk (A := dirichletLaplacian Ω) (fun _ ↦ f)
          (fun i ↦ i.elim0) (Fin.last 0)).symm⟩
    · rintro ⟨x, hx, w, hw⟩
      exact ⟨w, hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) 0 i x)
        (by simp : Fin.last 0 = 0)).trans hx)⟩
  | succ ℓ ih =>
    intro f
    change MemLaplacianDomain Ω (2 * ℓ + 1 + 2) f ↔ _
    refine memLaplacianDomain_add_two_iff.trans ((and_congr_right fun _ ↦ ih).trans ?_)
    constructor
    · rintro ⟨hf, y, hy, w, hw⟩
      refine ⟨cons ⟨f, hf⟩ y ((dirichletLaplacian_apply ⟨f, hf⟩).trans hy.symm),
        applyL_cons_zero _ _ _, w, ?_⟩
      exact hw.trans ((applyL_cons_succ _ _ _ (Fin.last ℓ)).symm.trans
        (congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i _) (Fin.succ_last ℓ)))
    · rintro ⟨x, hx, w, hw⟩
      refine ⟨(mem_and_exists_powDomain_of_powDomain_succ x hx).1,
        shiftL (dirichletLaplacian Ω) ℓ x, ?_, w, ?_⟩
      · exact (applyL_zero_shiftL x).trans ((dirichletLaplacian_apply _).trans
          (congrArg (dirichletLaplacianApply Ω) hx))
      · exact hw.trans ((congrArg (fun i ↦ applyL (dirichletLaplacian Ω) (ℓ + 1) i x)
          (Fin.succ_last ℓ).symm).trans (applyL_shiftL (Fin.last ℓ) x).symm)

end LaplacianDomain

end Wave

namespace Wave

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

/-! ### Theorem 10.8: `D(A^k) ⊆ H^{k+1}(Ω) × H^k(Ω)` and the regularity of the solution -/

section Regularity

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- `D_{2ℓ} ⊆ H^{2ℓ}(Ω)` on a `C^{2ℓ}` domain with bounded boundary (Theorem 9.25 through
`dirichletLaplacian_exists_sobolev_of_powDomain`). -/
theorem MemLaplacianDomain.exists_sobolev_two_mul (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω (2 * ℓ) f) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume w = f := by
  obtain ⟨x, hx⟩ := (memLaplacianDomain_two_mul_iff ℓ).1 h
  obtain ⟨w, hw⟩ := dirichletLaplacian_exists_sobolev_of_powDomain ℓ hΩ hΓ x
  exact ⟨w, hw.trans hx⟩

/-- `D_{2ℓ+1} ⊆ H^{2ℓ+1}(Ω)` on a `C^{2ℓ+1}` domain with bounded boundary
(`dirichletLaplacian_exists_sobolev_of_powDomain_of_last`). -/
theorem MemLaplacianDomain.exists_sobolev_two_mul_add_one (ℓ : ℕ)
    (hΩ : IsContDiffChartDomain (2 * ℓ + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω (2 * ℓ + 1) f) :
    ∃ w : SobolevEuclidean (d + 1) (2 * ℓ + 1) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ + 1) 2 Ω volume w = f := by
  obtain ⟨x, hx, hlast⟩ := (memLaplacianDomain_two_mul_add_one_iff ℓ).1 h
  obtain ⟨w, hw⟩ :=
    dirichletLaplacian_exists_sobolev_of_powDomain_of_last ℓ (2 * ℓ + 1) rfl hΩ hΓ x hlast
  exact ⟨w, hw.trans hx⟩

/-- **`D_m ⊆ H^m(Ω)` on a `C^m` domain with bounded boundary** ([brezis2011functional] §10.3,
the reading of the display in the proof of Theorem 10.8 in Sobolev spaces): every `f ∈ D_m` is
the function of an element of `H^m(Ω)`. Even `m` is `D((−Δ)^ℓ) ⊆ H^{2ℓ}`
(`dirichletLaplacian_exists_sobolev_of_powDomain`, Theorem 9.25), odd `m` its companion
`dirichletLaplacian_exists_sobolev_of_powDomain_of_last`. -/
theorem MemLaplacianDomain.exists_sobolev (m : ℕ)
    (hΩ : IsContDiffChartDomain m (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : MemLaplacianDomain Ω m f) :
    ∃ w : SobolevEuclidean (d + 1) m 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω volume w = f := by
  obtain ⟨ℓ, hℓ | hℓ⟩ := Nat.even_or_odd' m
  · subst hℓ
    exact MemLaplacianDomain.exists_sobolev_two_mul ℓ hΩ hΓ h
  · subst hℓ
    exact MemLaplacianDomain.exists_sobolev_two_mul_add_one ℓ hΩ hΓ h

end Regularity

section Coord

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **The wave operator is closed**: `A + I` is maximal monotone, hence closed, and closedness
is unchanged by the shift (`LinearPMap.IsAddSmulId.isClosed`). -/
theorem operator_isClosed : (operator Ω).IsClosed :=
  (isAddSmulId_id_vadd (operator Ω)).isClosed operator_add_id_isMaximalMonotone.isClosed

variable (Ω) in
/-- The `L²` function of the first component of the base point of `x ∈ D(A^k)`,
`x ↦ fnL (x_0).fst`, as a bounded linear map. -/
def fstCoordL (k : ℕ) :
    (operator Ω).PowDomain k →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume).comp
    ((phaseSpace.fstL Ω).comp (applyL (operator Ω) k 0))

/-- `fstCoordL x = fnL (x_0).fst`. -/
theorem fstCoordL_apply {k : ℕ} (x : (operator Ω).PowDomain k) :
    fstCoordL Ω k x = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (applyL (operator Ω) k 0 x).fst :=
  rfl

variable (Ω) in
/-- The second component of the base point of `x ∈ D(A^k)`, `x ↦ (x_0).snd`, as a bounded
linear map. -/
def sndCoordL (k : ℕ) :
    (operator Ω).PowDomain k →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  (phaseSpace.sndL Ω).comp (applyL (operator Ω) k 0)

/-- `sndCoordL x = (x_0).snd`. -/
theorem sndCoordL_apply {k : ℕ} (x : (operator Ω).PowDomain k) :
    sndCoordL Ω k x = (applyL (operator Ω) k 0 x).snd :=
  rfl

/-- The first component of an element of `D(A^k)` lies in `D_{k+1}`. -/
theorem memLaplacianDomain_fstCoordL (k : ℕ) (x : (operator Ω).PowDomain k) :
    MemLaplacianDomain Ω (k + 1) (fstCoordL Ω k x) :=
  ((mem_operator_powGraph_iff k _).1 ⟨x, rfl⟩).1

/-- The second component of an element of `D(A^k)` lies in `D_k`. -/
theorem memLaplacianDomain_sndCoordL (k : ℕ) (x : (operator Ω).PowDomain k) :
    MemLaplacianDomain Ω k (sndCoordL Ω k x) :=
  ((mem_operator_powGraph_iff k _).1 ⟨x, rfl⟩).2

end Coord

section PowDomainToSobolev

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- `fnL (x_0).fst` is the function of an element of `H^{k+1}(Ω)` for `x ∈ D(A^k)`, on a
`C^{k+1}` domain with bounded boundary. -/
theorem exists_sobolev_fstCoordL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    ∃ w : SobolevEuclidean (d + 1) (k + 1) 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume w
        = fstCoordL Ω k x :=
  (memLaplacianDomain_fstCoordL k x).exists_sobolev (k + 1) hΩ hΓ

/-- `(x_0).snd` is the function of an element of `H^k(Ω)` for `x ∈ D(A^k)`, on a `C^k` domain
with bounded boundary. -/
theorem exists_sobolev_sndCoordL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    ∃ z : SobolevEuclidean (d + 1) k 2 Ω,
      fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume z = sndCoordL Ω k x :=
  (memLaplacianDomain_sndCoordL k x).exists_sobolev k hΩ hΓ

/-- **The continuous injection `D(A^k) → H^{k+1}(Ω)`, first component**: the bounded linear map
`x ↦ w` with `fnL w = fnL (x_0).fst`, continuous by the closed graph theorem
(`SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq`, `D(A^k)` being complete
since `A` is closed). -/
def operator.powDomainToSobolevFstL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ] SobolevEuclidean (d + 1) (k + 1) 2 Ω :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := fstCoordL Ω k) (exists_sobolev_fstCoordL k hΩ hΓ))

/-- `fnL (powDomainToSobolevFstL x) = fnL (x_0).fst`. -/
theorem fnL_powDomainToSobolevFstL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume
      (operator.powDomainToSobolevFstL k hΩ hΓ x) = fstCoordL Ω k x :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := fstCoordL Ω k) (exists_sobolev_fstCoordL k hΩ hΓ)) x

/-- **The continuous injection `D(A^k) → H^k(Ω)`, second component**. -/
def operator.powDomainToSobolevSndL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ] SobolevEuclidean (d + 1) k 2 Ω :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := sndCoordL Ω k) (exists_sobolev_sndCoordL k hΩ hΓ))

/-- `fnL (powDomainToSobolevSndL x) = (x_0).snd`. -/
theorem fnL_powDomainToSobolevSndL (k : ℕ)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume
      (operator.powDomainToSobolevSndL k hΩ hΓ x) = sndCoordL Ω k x :=
  haveI : CompleteSpace ((operator Ω).PowDomain k) := operator_isClosed.completeSpace_powDomain k
  Classical.choose_spec (SobolevEuclidean.exists_continuousLinearMap_of_forall_exists_fnL_eq
    (S := sndCoordL Ω k) (exists_sobolev_sndCoordL k hΩ hΓ)) x

/-- **`D(A^k) ⊆ H^{k+1}(Ω) × H^k(Ω)` with continuous injection** ([brezis2011functional]
§10.3, the "in particular" of the proof of Theorem 10.8), on a `C^{k+1}` domain with bounded
boundary: the bounded linear map `x ↦ (w, z)` on `D(A^k)` with `fnL w = fnL u`, `fnL z = v` for
the base point `(u, v)` of `x` (`fnL_powDomainToSobolevL_fst`, `fnL_powDomainToSobolevL_snd`);
`‖w‖_{H^{k+1}} + ‖z‖_{H^k} ≤ C ‖x‖_{D(A^k)}` is its boundedness. The memberships come from
`D(A^k) = D_{k+1} × D_k` (`mem_operator_powGraph_iff`) and `D_m ⊆ H^m(Ω)`
(`MemLaplacianDomain.exists_sobolev`, Theorem 9.25 at every order), the continuity from the
closed graph theorem. -/
def operator.powDomainToSobolevL (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (operator Ω).PowDomain k →L[ℝ]
      SobolevEuclidean (d + 1) (k + 1) 2 Ω × SobolevEuclidean (d + 1) k 2 Ω :=
  (operator.powDomainToSobolevFstL k hΩ hΓ).prod
    (operator.powDomainToSobolevSndL k (hΩ.of_le (by exact_mod_cast Nat.le_succ k)) hΓ)

/-- The first component of `powDomainToSobolevL x` has the function `fnL (x_0).fst`. -/
theorem fnL_powDomainToSobolevL_fst (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (k + 1) 2 Ω volume
      (operator.powDomainToSobolevL k hΩ hΓ x).1 = fstCoordL Ω k x :=
  fnL_powDomainToSobolevFstL k hΩ hΓ x

/-- The second component of `powDomainToSobolevL x` has the function `(x_0).snd`. -/
theorem fnL_powDomainToSobolevL_snd (k : ℕ)
    (hΩ : IsContDiffChartDomain (k + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (x : (operator Ω).PowDomain k) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis k 2 Ω volume
      (operator.powDomainToSobolevL k hΩ hΓ x).2 = sndCoordL Ω k x :=
  fnL_powDomainToSobolevSndL k _ hΓ x

end PowDomainToSobolev

/-! ### Theorem 10.8 -/

section Regularity10_8

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {u₀ : SobolevEuclideanZero N 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- The shifted semigroup curve of Theorem 7.5 for `A + I`, at `c = 1`, is the phase-space
solution `e^t S_{A+I}(t) (u₀, v₀)`. -/
theorem exp_smul_semigroup_eq_phaseSolution {k : ℕ} (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) (t : ℝ) :
    Real.exp (1 * t) • ((LinearMap.id : phaseSpace Ω →ₗ[ℝ] phaseSpace Ω)
      +ᵥ operator Ω).semigroup t (applyL (operator Ω) k 0 x) = phaseSolution Ω u₀ v₀ t := by
  rw [one_mul, hx]
  rfl

/-- **The phase-space solution is `(ũ, u')`**: for a solution `u` of the wave equation and
`t ≥ 0`, `phaseSolution Ω u₀ v₀ t = (toSobolevZero (u t), u'(t))` (uniqueness for
`U' + A U = 0`, `operator_eqOn_of_isSolutionOn`). -/
theorem IsSolution.phaseSolution_eq (h : IsSolution Ω u₀ v₀ u) {t : ℝ} (ht : 0 ≤ t) :
    phaseSolution Ω u₀ v₀ t
      = phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t) :=
  operator_eqOn_of_isSolutionOn (isSolutionOn_phaseSolution h.memOperatorDomain_mk)
    h.isSolutionOn ht

/-- **`U = (ũ, u') ∈ C^{k−j}([0, ∞); D(A^j))` for data in `D(A^k)`** ([brezis2011functional],
proof of Theorem 10.8, "by Theorem 7.5"): Theorem 7.5 for the maximal monotone `A + I`, shifted
back by `e^t` (`LinearPMap.IsMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup`, with the
transport of `D((A + I)^j)` to `D(A^j)`), applied to `U = e^t S_{A+I}(t) (u₀, v₀)`. Any open
`Ω`. -/
theorem IsSolution.contDiffOnPowDomain_of_powDomain (h : IsSolution Ω u₀ v₀ u) {k : ℕ}
    (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) {j : ℕ} (hj : j ≤ k) :
    (operator Ω).ContDiffOnPowDomain (k - j : ℕ) j
      (fun t ↦ phaseSpace.mk Ω (toSobolevZero Ω (u t)) (derivWithin u (Ici 0) t)) (Ici 0) := by
  have h1 := operator_add_id_isMaximalMonotone.contDiffOnPowDomain_exp_smul_semigroup
    (isAddSmulId_id_vadd (operator Ω)) x hj
  exact h1.congr fun t ht ↦ (exp_smul_semigroup_eq_phaseSolution x hx t).trans
    (h.phaseSolution_eq ht)

end Regularity10_8

section Regularity10_8'

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {u₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
  {v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- **Theorem 10.8, the Bochner form** ([brezis2011functional] Theorem 10.8, the lines
"`U ∈ C^{k−j}([0, ∞); D(A^j))`, hence `u ∈ C^{k−j}([0, ∞); H^{j+1}(Ω))`"): if the data
`(u₀, v₀)` are the base point of an element of `D(A^k)`, then on a `C^{j+1}` domain with bounded
boundary, `j ≤ k`, the solution `u` is of class `C^{k−j}([0, ∞); H^{j+1}(Ω))` through the
inclusion `H^{j+1}(Ω) → L²(Ω)`: the lift is `t ↦ (powDomainToSobolevL (V t)).1` for the
`D(A^j)`-lift `V` of `U = (ũ, u')` (`IsSolution.contDiffOnPowDomain_of_powDomain`). -/
theorem IsSolution.contDiffOnThrough_of_powDomain (h : IsSolution Ω u₀ v₀ u) {k : ℕ}
    (x : (operator Ω).PowDomain k)
    (hx : applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀) {j : ℕ} (hj : j ≤ k)
    (hΩ : IsContDiffChartDomain (j + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (j + 1) 2
      Ω volume) (k - j : ℕ) u (Ici 0) := by
  obtain ⟨V, hV0, hV⟩ := h.contDiffOnPowDomain_of_powDomain x hx hj
  refine ⟨operator.powDomainToSobolevFstL j hΩ hΓ ∘ V,
    (operator.powDomainToSobolevFstL j hΩ hΓ).contDiff.comp_contDiffOn hV, fun t ht ↦ ?_⟩
  have e1 : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (j + 1) 2 Ω volume
      ((operator.powDomainToSobolevFstL j hΩ hΓ ∘ V) t) = fstCoordL Ω j (V t) :=
    fnL_powDomainToSobolevFstL j hΩ hΓ (V t)
  have e2 : fstCoordL Ω j (V t) = SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume (toSobolevZero Ω (u t)) :=
    (congrArg (fun U : phaseSpace Ω ↦ SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume U.fst) (hV0 t ht)).trans
      (congrArg (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2
        Ω volume) (phaseSpace.mk_fst _ _))
  rw [e1, e2, h.fnL_toSobolevZero_apply ht]

/-- **`u ∈ C^∞([0, ∞); H^m(Ω))` for every `m`** when the data lie in every `D(A^k)`, on a `C^∞`
domain with bounded boundary: one lift for all orders
(`Bochner.ContDiffOnThrough.infty_of_forall_nat`) from `contDiffOnThrough_of_powDomain` at
`j = m`, `k = m + n`, lowered from `H^{m+1}` to `H^m`
(`Bochner.ContDiffOnThrough.sobolev_of_le`). -/
theorem IsSolution.contDiffOnThrough_sobolev_forall (h : IsSolution Ω u₀ v₀ u)
    (hU₀ : ∀ k, ∃ x : (operator Ω).PowDomain k,
      applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ici 0) := by
  have hm : IsContDiffChartDomain (m + 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (WithTop.coe_le_coe.2 le_top)
  have key : ∀ n : ℕ, Bochner.ContDiffOnThrough
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (m + 1) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hU₀ (m + n)
    have := h.contDiffOnThrough_of_powDomain x hx (j := m) (by omega) hm hΓ
    rwa [show m + n - m = n by omega] at this
  have hJ : Function.Injective
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (m + 1) 2 Ω volume) :=
    fnL_injective
  exact (Bochner.ContDiffOnThrough.infty_of_forall_nat hJ key).sobolev_of_le (Nat.le_succ m)

/-- **Theorem 10.8** ([brezis2011functional]): on a `C^∞` domain with bounded boundary, if the
data `(u₀, v₀)` lie in `D(A^k)` for every `k` — the book's `u₀, v₀ ∈ H^k(Ω)` for all `k` with
the compatibility conditions `Δ^j u₀ = Δ^j v₀ = 0` on `Γ`, read through
`mem_operator_powGraph_iff` and `MemLaplacianDomain` — then the solution `u` of the wave
equation belongs to `C^∞(Ω̄ × [0, ∞))`: there is `U : ℝ^N × ℝ → ℝ` with `U(·, t) = u(t)` almost
everywhere on `Ω` for every `t ≥ 0`, `C^∞` on `Ω × (0, ∞)` with every derivative extending
continuously to `closure Ω × [0, ∞)` (`ContDiffOnClosure`). Proof:
`u ∈ C^∞([0, ∞); H^m(Ω))` for every `m` (`contDiffOnThrough_sobolev_forall`) and the
space–time bridge on `[0, ∞)`
(`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`). -/
theorem IsSolution.contDiffOnClosure_spaceTime (h : IsSolution Ω u₀ v₀ u)
    (hU₀ : ∀ k, ∃ x : (operator Ω).PowDomain k,
      applyL (operator Ω) k 0 x = phaseSpace.mk Ω u₀ v₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi 0) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_forall hU₀ hΩ hΓ)

end Regularity10_8'

end Wave

namespace Wave

open LinearPMap.PowDomain SobolevMultiIndex Elliptic SobolevEuclidean MeasureTheory.Lp

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### Remark 8: d'Alembert's formula solves the wave equation on `ℝ` -/

/-- **Membership in `D(−Δ)` through `H¹` derivatives**: if `v ∈ H¹₀(Ω)` and each `∂ᵢ v` is the
function of some `Qᵢ ∈ H¹(Ω)`, then `f = fnL v` lies in `D(−Δ)` and `−Δ f = −∑ᵢ ∂ᵢ Qᵢ`. This is
`mem_dirichletLaplacianDomain_of_sobolev_two` with the `H²` element replaced by the family of
its first derivatives, the only thing the proof uses. -/
theorem mem_dirichletLaplacianDomain_of_forall_ae_eq {v : SobolevEuclidean N 1 2 Ω}
    (hv : v ∈ SobolevEuclideanZero N 1 2 Ω) (Q : Fin N → SobolevEuclidean N 1 2 Ω)
    (hQ : ∀ i, ⇑(weakDeriv v (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] fn (Q i)) :
    fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v ∈ dirichletLaplacianDomain Ω
      ∧ dirichletLaplacianApply Ω (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v)
        = -∑ i, weakDeriv (Q i) (MultiIndexLE.single i) := by
  -- the datum, as a function
  have hg : ⇑(-∑ i, weakDeriv (Q i) (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ -∑ i, weakDeriv (Q i) (MultiIndexLE.single i) x := by
    filter_upwards [Lp.coeFn_neg (∑ i, weakDeriv (Q i) (MultiIndexLE.single i)),
      Lp.coeFn_finsetSum Finset.univ fun i ↦ weakDeriv (Q i) (MultiIndexLE.single i)] with x hx1 hx2
    rw [hx1, Pi.neg_apply, hx2, Finset.sum_apply]
  -- the equation against test functions
  have heq : ∀ Φ ∈ testFunctions ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume,
      dirichletForm Ω v Φ = load Ω (-∑ i, weakDeriv (Q i) (MultiIndexLE.single i)) Φ := by
    intro Φ hΦ
    obtain ⟨ψ, hψ⟩ := hΦ
    rw [dirichletForm_apply_eq_of_ae_eq hQ hψ, load_apply_eq_of_ae_eq hg hψ]
    have hterm : ∀ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        fn (Q i) x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
        = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
          weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x := by
      intro i
      have key := (weakDeriv_hasWeakIteratedLineDerivOn_single (Q i) i)
        |>.integral_fderiv_mul_eq_of_eqOn ψ (fun _ _ ↦ rfl)
      calc ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
            fn (Q i) x * fderiv ℝ ψ x (EuclideanSpace.single i 1)
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              fderiv ℝ ψ x (EuclideanSpace.single i 1) * fn (Q i) x :=
            integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              ψ x * weakDeriv (Q i) (MultiIndexLE.single i) x := key
        _ = -∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
              weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x := by
            congr 1
            exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    simp only [hterm, Finset.sum_neg_distrib]
    have hI : ∀ i, Integrable
        (fun x ↦ weakDeriv (Q i) (MultiIndexLE.single i) x * ψ x)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦ by
      have := ((weakDeriv_hasWeakIteratedLineDerivOn_single (Q i) i)
        |>.integrable_smul_weakDeriv ψ).integrableOn (s := (Ω : Set (EuclideanSpace ℝ (Fin N))))
      exact this.congr (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
    rw [← integral_finsetSum _ fun i _ ↦ hI i, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp only [Finset.sum_mul, neg_mul])
  have heq' : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω,
      dirichletForm Ω v φ = load Ω (-∑ i, weakDeriv (Q i) (MultiIndexLE.single i)) φ :=
    fun φ hφ ↦ dirichletForm_eq_load_of_forall_testFunctions heq hφ
  exact ⟨⟨v, hv, rfl, _, heq'⟩, (eq_dirichletLaplacianApply hv rfl heq').symm⟩

/-- **The inclusion `W^{1,p}(ℝ^N) → W_0^{1,p}(ℝ^N)`** as a bounded linear map, `p < ∞`: the two
spaces coincide (`SobolevEuclideanZero.eq_top`), and the map is the identity. -/
def toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean N 1 p ⊤ →L[ℝ] SobolevEuclideanZero N 1 p ⊤ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (SobolevEuclideanZero N 1 p ⊤) LinearMap.id fun u ↦ by
      rw [SobolevEuclideanZero.eq_top hp]; exact Submodule.mem_top)
    1 fun u ↦ by rw [one_mul]; exact le_rfl

/-- The function of `toZeroTopL u` is the function of `u`. -/
theorem fnL_toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume
      (toZeroTopL hp u) = fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p ⊤ volume u :=
  rfl

/-- `toZeroTopL u` is `u` as an element of `W^{1,p}`. -/
theorem coe_toZeroTopL {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤) :
    (toZeroTopL hp u : SobolevEuclidean N 1 p ⊤) = u :=
  rfl


/-! ### d'Alembert's formula as a solution on `ℝ` -/

section DAlembertSolution

local notation "𝔼₁" => EuclideanSpace ℝ (Fin 1)
local notation "𝔟₁" => OrthonormalBasis.toBasis (EuclideanSpace.basisFun (Fin 1) ℝ)
local notation "𝕖" => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
local notation "L2₁" => Lp ℝ 2 (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) :
  Set (EuclideanSpace ℝ (Fin 1))))

variable (u₀ : SobolevEuclidean 1 2 2 ⊤) (v₀ : SobolevEuclidean 1 1 2 ⊤)

/-- The datum `u₀ ∈ H²(ℝ)` as an element of `H¹(ℝ)`. -/
abbrev dAlembertU₀ : SobolevEuclidean 1 1 2 ⊤ := toLowerOrderL ℝ 𝔟₁ 2 ⊤ volume (by omega) u₀

/-- The derivative `u₀' ∈ H¹(ℝ)` of the datum `u₀ ∈ H²(ℝ)`. -/
abbrev dAlembertU₀' : SobolevEuclidean 1 1 2 ⊤ := partialDerivL ℝ 𝔟₁ 2 ⊤ volume 0 u₀

/-- **d'Alembert's formula as a curve in `L²(ℝ)`**:
`u(t) = ½ (τ_t u₀ + τ_{−t} u₀) + ½ ∫_{−t}^{t} τ_s v₀ ds`, the `L²` class of
`x ↦ ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀(s) ds` (`coeFn_dAlembertL2`). -/
def dAlembertL2 (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t
      + translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t))
    + (1 / 2 : ℝ) • primitiveCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t

/-- The time derivative of d'Alembert's curve:
`∂ₜu(t) = ½ (τ_t u₀' − τ_{−t} u₀') + ½ (τ_t v₀ + τ_{−t} v₀)`. -/
def dAlembertL2Deriv (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀)) t
      - translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀)) (-t))
    + (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t
      + translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) (-t))

/-- The second time derivative of d'Alembert's curve, which is also its second space derivative:
`∂ₜₜu(t) = ½ (τ_t u₀'' + τ_{−t} u₀'') + ½ (τ_t v₀' − τ_{−t} v₀')`. -/
def dAlembertL2Deriv2 (t : ℝ) : L2₁ :=
  (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) t
      + translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) (-t))
    + (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv v₀ (MultiIndexLE.single 0)) t
      - translateCurve ℝ 2 𝕖 (weakDeriv v₀ (MultiIndexLE.single 0)) (-t))

/-- `weakDeriv (toLowerOrderL u₀) e₀ = fnL u₀'`. -/
theorem weakDeriv_dAlembertU₀ :
    weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0) = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀' u₀) :=
  (fnL_partialDerivL (k := 1) 0 u₀).symm

/-- **`∂ₜ u = ∂ₜu`**: d'Alembert's curve is differentiable in `L²(ℝ)`. -/
theorem hasDerivAt_dAlembertL2 (t : ℝ) :
    HasDerivAt (dAlembertL2 u₀ v₀) (dAlembertL2Deriv u₀ v₀ t) t := by
  have h1 := ((hasDerivAt_translateCurve_add_neg (by simp) (dAlembertU₀ u₀) 0 t).congr_deriv
    (by rw [weakDeriv_dAlembertU₀])).const_smul (1 / 2 : ℝ)
  have h2 := (hasDerivAt_primitiveCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) (by simp) t).const_smul
    (1 / 2 : ℝ)
  exact h1.add h2

/-- **`∂ₜₜ u`**: the time derivative of d'Alembert's curve is differentiable in `L²(ℝ)`. -/
theorem hasDerivAt_dAlembertL2Deriv (t : ℝ) :
    HasDerivAt (dAlembertL2Deriv u₀ v₀) (dAlembertL2Deriv2 u₀ v₀ t) t := by
  have h1 := (hasDerivAt_translateCurve_sub_neg (by simp) (dAlembertU₀' u₀) 0 t).const_smul
    (1 / 2 : ℝ)
  have h2 := (hasDerivAt_translateCurve_add_neg (by simp) v₀ 0 t).const_smul (1 / 2 : ℝ)
  exact h1.add h2

/-- The second derivative of d'Alembert's curve is continuous in `L²(ℝ)`. -/
theorem continuous_dAlembertL2Deriv2 : Continuous (dAlembertL2Deriv2 u₀ v₀) := by
  have h1 := (continuous_translateCurve_add_neg 𝕖
    (weakDeriv (dAlembertU₀' u₀) (MultiIndexLE.single 0)) (by simp)).const_smul (1 / 2 : ℝ)
  have h2 := (continuous_translateCurve_sub_neg 𝕖
    (weakDeriv v₀ (MultiIndexLE.single 0)) (by simp)).const_smul (1 / 2 : ℝ)
  exact h1.add h2

/-- **`u ∈ C²(ℝ; L²(ℝ))`** for d'Alembert's curve. -/
theorem contDiff_dAlembertL2 : ContDiff ℝ 2 (dAlembertL2 u₀ v₀) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).differentiableAt, fun h ↦ by simp at h, ?_⟩
  have e : deriv (dAlembertL2 u₀ v₀) = dAlembertL2Deriv u₀ v₀ :=
    funext fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).deriv
  rw [e, contDiff_one_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).differentiableAt, ?_⟩
  have e2 : deriv (dAlembertL2Deriv u₀ v₀) = dAlembertL2Deriv2 u₀ v₀ :=
    funext fun t ↦ (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).deriv
  rw [e2]
  exact continuous_dAlembertL2Deriv2 u₀ v₀

/-- The translation `τ_{t e}` on `H¹(ℝ)`. -/
abbrev dAlembertTL (w : SobolevEuclidean 1 1 2 ⊤) (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  translateL ℝ 𝔟₁ 1 2 volume (IsTranslationInvariant.top (t • 𝕖)) w

/-- **The lift of d'Alembert's curve to `H¹(ℝ)`**:
`ũ(t) = ½ (τ_t u₀ + τ_{−t} u₀) + ½ ∫_{−t}^{t} τ_s v₀ ds` in `H¹(ℝ)`. -/
def dAlembertH1 (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  (1 / 2 : ℝ) • (dAlembertTL (dAlembertU₀ u₀) t + dAlembertTL (dAlembertU₀ u₀) (-t))
    + (1 / 2 : ℝ) • primitiveCurveL 1 𝕖 v₀ t

/-- **The space derivative of d'Alembert's curve as an `H¹(ℝ)` element**:
`∂ₓu(t) = ½ (τ_t u₀' + τ_{−t} u₀') + ½ (τ_t v₀ − τ_{−t} v₀)`. -/
def dAlembertH1Space (t : ℝ) : SobolevEuclidean 1 1 2 ⊤ :=
  (1 / 2 : ℝ) • (dAlembertTL (dAlembertU₀' u₀) t + dAlembertTL (dAlembertU₀' u₀) (-t))
    + (1 / 2 : ℝ) • (dAlembertTL v₀ t - dAlembertTL v₀ (-t))

/-- The function of the `H¹` lift is d'Alembert's curve. -/
theorem fnL_dAlembertH1 (t : ℝ) :
    fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertH1 u₀ v₀ t) = dAlembertL2 u₀ v₀ t := by
  change (1 / 2 : ℝ) • (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertTL (dAlembertU₀ u₀) t)
      + fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertTL (dAlembertU₀ u₀) (-t)))
    + (1 / 2 : ℝ) • fnL ℝ 𝔟₁ 1 2 ⊤ volume (primitiveCurveL 1 𝕖 v₀ t) = _
  rw [fnL_primitiveCurveL (by simp) 𝕖 v₀ t]
  rfl

/-- **The weak derivative of the `H¹` lift is the function of `dAlembertH1Space`**: the space
derivative of `∫_{−t}^{t} τ_s v₀ ds` is `τ_t v₀ − τ_{−t} v₀` (`primitiveCurve_weakDeriv_single`). -/
theorem weakDeriv_dAlembertH1 (t : ℝ) :
    weakDeriv (dAlembertH1 u₀ v₀ t) (MultiIndexLE.single 0)
      = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertH1Space u₀ v₀ t) := by
  change (1 / 2 : ℝ) • (translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0)) t
      + translateCurve ℝ 2 𝕖 (weakDeriv (dAlembertU₀ u₀) (MultiIndexLE.single 0)) (-t))
    + (1 / 2 : ℝ) • weakDeriv (primitiveCurveL 1 𝕖 v₀ t) (MultiIndexLE.single 0) = _
  simp only [weakDeriv_primitiveCurveL (by simp) 𝕖 v₀ t,
    primitiveCurve_weakDeriv_single (by simp) v₀ 0 t, weakDeriv_dAlembertU₀]
  rfl

/-- The weak derivative of `dAlembertH1Space` is the second derivative `dAlembertL2Deriv2`. -/
theorem weakDeriv_dAlembertH1Space (t : ℝ) :
    weakDeriv (dAlembertH1Space u₀ v₀ t) (MultiIndexLE.single 0) = dAlembertL2Deriv2 u₀ v₀ t :=
  rfl

/-- **`u ∈ C¹(ℝ; H¹(ℝ))`** for the `H¹` lift of d'Alembert's curve. -/
theorem contDiff_dAlembertH1 : ContDiff ℝ 1 (dAlembertH1 u₀ v₀) :=
  ((contDiff_translateL_add_neg (by simp) u₀ 0).const_smul (1 / 2 : ℝ)).add
    ((contDiff_primitiveCurveL (by simp) 𝕖 v₀).const_smul (1 / 2 : ℝ))

/-- **d'Alembert's curve lies in `D(−Δ)` with `−Δ u(t) = −∂ₜₜu(t)`**: through the `H¹` lift and
the `H¹` element `dAlembertH1Space` carrying its space derivative
(`mem_dirichletLaplacianDomain_of_forall_ae_eq`). -/
theorem dAlembertL2_mem_dirichletLaplacianDomain (t : ℝ) :
    dAlembertL2 u₀ v₀ t ∈ dirichletLaplacianDomain ⊤
      ∧ dirichletLaplacianApply ⊤ (dAlembertL2 u₀ v₀ t) = -dAlembertL2Deriv2 u₀ v₀ t := by
  have hmem : dAlembertH1 u₀ v₀ t ∈ SobolevEuclideanZero 1 1 2 ⊤ := by
    rw [SobolevEuclideanZero.eq_top (by simp)]
    exact Submodule.mem_top
  have h := mem_dirichletLaplacianDomain_of_forall_ae_eq hmem (fun _ ↦ dAlembertH1Space u₀ v₀ t)
    fun i ↦ by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [weakDeriv_dAlembertH1]
      exact EventuallyEq.rfl
  rw [fnL_dAlembertH1, Fin.sum_univ_one, weakDeriv_dAlembertH1Space] at h
  exact h

/-- d'Alembert's curve at `t = 0` is `u₀`. -/
theorem dAlembertL2_zero : dAlembertL2 u₀ v₀ 0 = fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀) := by
  unfold dAlembertL2
  simp only [neg_zero, translateCurve_zero, primitiveCurve_zero]
  module

/-- The time derivative of d'Alembert's curve at `t = 0` is `v₀`. -/
theorem dAlembertL2Deriv_zero : dAlembertL2Deriv u₀ v₀ 0 = fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀ := by
  unfold dAlembertL2Deriv
  simp only [neg_zero, translateCurve_zero]
  module

/-- **Remark 8: d'Alembert's formula solves the wave equation on `ℝ`** ([brezis2011functional]
§10.3, Remark 8, (40)): for `u₀ ∈ H²(ℝ)` and `v₀ ∈ H¹(ℝ)` (`= H¹₀(ℝ)`), the curve
`t ↦ ½ (τ_t u₀ + τ_{−t} u₀) + ½ ∫_{−t}^{t} τ_s v₀ ds` in `L²(ℝ)` — the `L²` class of
`x ↦ ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀(s) ds` (`coeFn_dAlembertL2`) — is a solution
in the class (31) of Theorem 10.7 with data `(u₀, v₀)`: it is `C²` into `L²` and `C¹` into
`H¹₀ = H¹` (the translation calculus of `Numlib/Analysis/Sobolev/TranslationCurve`), `u(t)` lies
in `D(−Δ)` with `−Δu(t) = −∂ₜₜu(t) = −½ (τ_t u₀'' + τ_{−t} u₀'') − ½ (τ_t v₀' − τ_{−t} v₀')`, and
the initial conditions hold. By uniqueness (`IsSolution.unique`) it is the solution of
Theorem 10.7 (`IsSolution.eqOn_dAlembertL2`). -/
theorem isSolution_dAlembert :
    IsSolution ⊤ (toZeroTopL (by simp) (dAlembertU₀ u₀)) (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀)
      (dAlembertL2 u₀ v₀) where
  contDiffOn := (contDiff_dAlembertL2 u₀ v₀).contDiffOn
  contDiffOnThrough := ⟨fun t ↦ toZeroTopL (by simp) (dAlembertH1 u₀ v₀ t),
    ((toZeroTopL (N := 1) (p := 2) (by simp)).contDiff.comp
      (contDiff_dAlembertH1 u₀ v₀)).contDiffOn,
    fun t _ ↦ (fnL_dAlembertH1 u₀ v₀ t).symm⟩
  mem_domain t _ := (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).1
  contDiffOnPowDomain := by
    rw [LinearPMap.contDiffOnPowDomain_iff dirichletLaplacian_isClosed]
    refine ⟨![dAlembertL2 u₀ v₀, fun t ↦ -dAlembertL2Deriv2 u₀ v₀ t], fun t _ ↦ rfl, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      exact ⟨contDiffOn_zero.2 (contDiff_dAlembertL2 u₀ v₀).continuous.continuousOn,
        contDiffOn_zero.2 (continuous_dAlembertL2Deriv2 u₀ v₀).neg.continuousOn⟩
    · intro t _ i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      exact ⟨(dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).1,
        (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).2⟩
  eqn t ht := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
      (contDiff_dAlembertL2 u₀ v₀).contDiffAt ht, iteratedDeriv_succ, iteratedDeriv_one,
      dirichletLaplacian_apply, (dAlembertL2_mem_dirichletLaplacianDomain u₀ v₀ t).2, neg_neg]
    have e : deriv (dAlembertL2 u₀ v₀) = dAlembertL2Deriv u₀ v₀ :=
      funext fun t ↦ (hasDerivAt_dAlembertL2 u₀ v₀ t).deriv
    rw [e]
    exact (hasDerivAt_dAlembertL2Deriv u₀ v₀ t).deriv
  apply_zero := dAlembertL2_zero u₀ v₀
  derivWithin_zero := by
    rw [(hasDerivAt_dAlembertL2 u₀ v₀ 0).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 0
      self_mem_Ici)]
    exact dAlembertL2Deriv_zero u₀ v₀

/-- **Remark 8, uniqueness: every solution with data `(u₀, v₀)` is d'Alembert's curve on
`[0, ∞)`** (`IsSolution.unique`). -/
theorem IsSolution.eqOn_dAlembertL2 {u : ℝ → L2₁}
    (h : IsSolution ⊤ (toZeroTopL (by simp) (dAlembertU₀ u₀)) (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) u) :
    EqOn u (dAlembertL2 u₀ v₀) (Ici 0) :=
  h.unique (isSolution_dAlembert u₀ v₀)

/-- **d'Alembert's curve, pointwise**: `u(t)` is the class of
`x ↦ ½ (u₀(x + t e) + u₀(x − t e)) + ½ ∫_0^t (v₀(x + s e) + v₀(x − s e)) ds`, `e` the unit
vector of `ℝ¹`. -/
theorem coeFn_dAlembertL2 (t : ℝ) :
    dAlembertL2 u₀ v₀ t
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ (1 / 2 : ℝ) * (fn u₀ (x + t • 𝕖) + fn u₀ (x - t • 𝕖))
        + (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, (fn v₀ (x + s • 𝕖) + fn v₀ (x - s • 𝕖)) := by
  refine (Lp.coeFn_smul_add_add_smul (1 / 2 : ℝ)
    (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t)
    (translateCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t))
    (primitiveCurve ℝ 2 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t)).trans ?_
  filter_upwards [coeFn_translateCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) t,
    coeFn_translateCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume (dAlembertU₀ u₀)) (-t),
    coeFn_primitiveCurve 𝕖 (fnL ℝ 𝔟₁ 1 2 ⊤ volume v₀) t] with x h1 h2 h3
  simp only [h1, h2, h3, neg_smul, ← sub_eq_add_neg]
  rfl

/-- The line `ℝ` as `ℝ¹ = EuclideanSpace ℝ (Fin 1)`: `r ↦ (r)`. -/
def lineEmbed (r : ℝ) : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ ↦ r

/-- The coordinate of `lineEmbed r` is `r`. -/
@[simp]
theorem lineEmbed_apply (r : ℝ) (i : Fin 1) : lineEmbed r i = r := rfl

/-- Every point of `ℝ¹` is `lineEmbed` of its coordinate. -/
theorem lineEmbed_coord (x : EuclideanSpace ℝ (Fin 1)) : lineEmbed (x 0) = x := by
  ext i
  rw [lineEmbed_apply, Subsingleton.elim i 0]

/-- `x + t e = lineEmbed (x₀ + t)`. -/
theorem add_smul_single_eq_lineEmbed (x : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    x + t • 𝕖 = lineEmbed (x 0 + t) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [lineEmbed]

/-- `x − t e = lineEmbed (x₀ − t)`. -/
theorem sub_smul_single_eq_lineEmbed (x : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    x - t • 𝕖 = lineEmbed (x 0 - t) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [lineEmbed]

/-- `lineEmbed` preserves Lebesgue measure. -/
theorem measurePreserving_lineEmbed : MeasurePreserving lineEmbed volume volume :=
  (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm (MeasurableEquiv.funUnique (Fin 1) ℝ))

/-- `lineEmbed` preserves Lebesgue measure, read on the whole space `⊤ : Opens ℝ¹`. -/
theorem measurePreserving_lineEmbed_top : MeasurePreserving lineEmbed volume
    (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))) :=
  ⟨measurePreserving_lineEmbed.measurable, by
    rw [measurePreserving_lineEmbed.map_eq, Measure.restrict_coe_top]⟩

/-- The composite of an `L²(ℝ¹)` function with `lineEmbed` is interval integrable on `ℝ`. -/
theorem intervalIntegrable_comp_lineEmbed (w : SobolevEuclidean 1 1 2 ⊤) (a b : ℝ) :
    IntervalIntegrable (fun r ↦ fn w (lineEmbed r)) volume a b := by
  have h : MemLp (fun r ↦ fn w (lineEmbed r)) 2 (volume : Measure ℝ) :=
    (SobolevMultiIndex.memLp w).comp_measurePreserving measurePreserving_lineEmbed_top
  have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ι a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact intervalIntegrable_iff.2 ((h.restrict (Ι a b)).integrable one_le_two)

/-- The interval integral `∫_{x₀−t}^{x₀+t} g` as `∫_0^t (g(x₀ + s) + g(x₀ − s)) ds`. -/
theorem integral_add_sub_eq_integral_sub_add {g : ℝ → ℝ}
    (hg : ∀ a b, IntervalIntegrable g volume a b) (x₀ t : ℝ) :
    ∫ s in (0 : ℝ)..t, (g (x₀ + s) + g (x₀ - s)) = ∫ s in (x₀ - t)..(x₀ + t), g s := by
  have h1 : IntervalIntegrable (fun s ↦ g (x₀ + s)) volume 0 t := by
    have := (hg x₀ (x₀ + t)).comp_add_left x₀
    simpa using this
  have h2 : IntervalIntegrable (fun s ↦ g (x₀ - s)) volume 0 t := by
    have := (hg (x₀ - t) x₀).comp_sub_left x₀
    simpa using this.symm
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_comp_add_left g,
    intervalIntegral.integral_comp_sub_left g, add_zero, sub_zero, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hg _ _) (hg _ _)]

/-- **d'Alembert's curve is d'Alembert's formula (40)**: `u(t)` is the class of
`x ↦ ½ (u₀(x + t) + u₀(x − t)) + ½ ∫_{x−t}^{x+t} v₀(s) ds`, the data read as functions on `ℝ`
through `lineEmbed` and the point `x ∈ ℝ¹` through its coordinate (`Wave.dAlembert`). -/
theorem coeFn_dAlembertL2_dAlembert (t : ℝ) :
    dAlembertL2 u₀ v₀ t
      =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 1))) : Set (EuclideanSpace ℝ (Fin 1)))]
      fun x ↦ dAlembert (fun r ↦ fn u₀ (lineEmbed r)) (fun r ↦ fn v₀ (lineEmbed r)) t (x 0) := by
  refine (coeFn_dAlembertL2 u₀ v₀ t).trans (Eventually.of_forall fun x ↦ ?_)
  beta_reduce
  rw [dAlembert_apply, add_smul_single_eq_lineEmbed, sub_smul_single_eq_lineEmbed]
  congr 2
  have e : ∀ s, fn v₀ (x + s • 𝕖) + fn v₀ (x - s • 𝕖)
      = fn v₀ (lineEmbed (x 0 + s)) + fn v₀ (lineEmbed (x 0 - s)) := fun s ↦ by
    rw [add_smul_single_eq_lineEmbed, sub_smul_single_eq_lineEmbed]
  simp only [e]
  exact integral_add_sub_eq_integral_sub_add (intervalIntegrable_comp_lineEmbed v₀) (x 0) t

end DAlembertSolution

end Wave
