import Numlib.Variational.LaxMilgram
import Numlib.LinearSolve.Projection.Optimality
import Numlib.Approximation.BestApprox
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Galerkin and Petrov–Galerkin methods for variational problems

* `IsGalerkinSolution a ℓ K u`: `u ∈ K` and `a u v = ℓ v` for all `v ∈ K` (AH (9.1.4)); bridge to
  the operator specification `IsGalerkin (toOperator a) (rieszRep ℓ) 0 K u` (§2.4.1) and to the
  stiffness-matrix system (9.1.5).
* Céa's lemma `‖u - u_N‖ ≤ (M / c) inf_{v ∈ K} ‖u - v‖` (AH Thm 9.1.3), the Hermitian
  sharpening `√(M / c)` (AH (9.1.7)–(9.1.8)), and convergence for monotone dense families
  (AH Cor 9.1.4).
* `IsPetrovGalerkinSolution a ℓ K L u` for two-space forms, Babuška's theorem
  `‖u - u_N‖ ≤ (1 + M / α_N) inf ‖u - v‖` under the discrete inf–sup condition (AH Thm 9.2.1),
  and its quasi-optimality corollary (AH Cor 9.2.3).
* Strang's first lemma for the generalized Galerkin method on an abstract normed space `W`
  (AH Thm 9.3.1).
-/

open scoped InnerProductSpace

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The Galerkin problem: `u ∈ K`, `a u v = ℓ v` for all `v ∈ K` (AH (9.1.4)). -/
def IsGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, a u v = ℓ v

/-- The Petrov–Galerkin problem: `u ∈ K`, `a u v = ℓ v` for all `v ∈ L` (AH (9.2.5)). -/
def IsPetrovGalerkinSolution {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (u : U) :
    Prop :=
  u ∈ K ∧ ∀ v ∈ L, a u v = ℓ v

theorem isGalerkinSolution_iff_isPetrovGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)
    (K : Submodule 𝕜 V) (u : V) :
    IsGalerkinSolution a ℓ K u ↔ IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 V V) ℓ K K u :=
  Iff.rfl

namespace IsGalerkinSolution

variable {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 V} {u : V}

/-- Bridge to the operator specification (§2.4.1): Galerkin for the form is Galerkin for
`A = toOperator a`, `b = rieszRep ℓ`, `x₀ = 0`. -/
theorem iff_isGalerkin [CompleteSpace V] :
    IsGalerkinSolution a ℓ K u ↔
      IsGalerkin (SesqForm.toOperator a : V →ₗ[𝕜] V) (SesqForm.rieszRep ℓ) 0 K u := by
  sorry

/-- Existence and uniqueness on a finite-dimensional (or complete) subspace for coercive `a`
(Lax–Milgram on `K`, AH §9.1). -/
theorem existsUnique {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u := by
  sorry

/-- Galerkin orthogonality: `a (u - u_N) v = 0` for `v ∈ K` when `u` is the exact solution. -/
theorem apply_sub_eq_zero (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) : a (ustar - u) v = 0 := by
  sorry

/-- Céa's lemma (AH Thm 9.1.3), pointwise form: `‖u - u_N‖ ≤ (M / c) ‖u - v‖` for all `v ∈ K`. -/
theorem norm_sub_le {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hN : IsGalerkinSolution a ℓ K u) {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) {v : V}
    (hv : v ∈ K) : ‖ustar - u‖ ≤ M / c * ‖ustar - v‖ := by
  sorry

/-- Céa's lemma with the infimum. -/
theorem norm_sub_le_infDist {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M)
    (ha : a.IsCoerciveWith c) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) : ‖ustar - u‖ ≤ M / c * Metric.infDist ustar (K : Set V) := by
  sorry

/-- Hermitian case (AH (9.1.7)–(9.1.8)): `u_N` is the best approximation in the energy norm,
hence `‖u - u_N‖ ≤ √(M / c) ‖u - v‖`. -/
theorem energyNorm_sub_le (ha : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) :
    a.energyNorm (ustar - u) ≤ a.energyNorm (ustar - v) := by
  sorry

theorem norm_sub_le_sqrt {M c : ℝ} (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hh : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u) {ustar : V}
    (hstar : ∀ v, a ustar v = ℓ v) {v : V} (hv : v ∈ K) :
    ‖ustar - u‖ ≤ Real.sqrt (M / c) * ‖ustar - v‖ := by
  sorry

/-- Stiffness-matrix form (AH (9.1.5)): with a basis `φ` of `K`, `∑ ξ_j φ_j` is the Galerkin
solution iff `(a (φ j) (φ i))_{ij} ξ = (ℓ (φ i))_i`. -/
theorem iff_mulVec {ι : Type*} [Fintype ι] (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
    IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
      (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec ξ = fun i => ℓ (φ i) := by
  sorry

end IsGalerkinSolution

/-- Distances to a monotone family of subspaces with dense union tend to zero (shared lemma
for AH Cor 9.1.4, Cor 9.2.3, Kress §11). -/
theorem tendsto_infDist_of_monotone_dense {K : ℕ → Submodule 𝕜 V} (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set V))) (u : V) :
    Filter.Tendsto (fun n => Metric.infDist u (K n : Set V)) Filter.atTop (nhds 0) := by
  sorry

/-- AH Cor 9.1.4: Galerkin solutions on a monotone dense family converge to the solution. -/
theorem IsGalerkinSolution.tendsto {a : SesqForm 𝕜 V} {ℓ : V →L[𝕜] 𝕜} {M c : ℝ} (hc : 0 < c)
    (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c) {K : ℕ → Submodule 𝕜 V}
    (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V))) {uN : ℕ → V}
    (hN : ∀ n, IsGalerkinSolution a ℓ (K n) (uN n))
    {ustar : V} (hstar : ∀ v, a ustar v = ℓ v) :
    Filter.Tendsto uN Filter.atTop (nhds ustar) := by
  sorry

namespace IsPetrovGalerkinSolution

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] {a : SesqForm₂ 𝕜 U V}
  {ℓ : V →L[𝕜] 𝕜} {K : Submodule 𝕜 U} {L : Submodule 𝕜 V} {u : U}

/-- The discrete inf–sup condition (AH (9.2.6)): `α ‖w‖ ≤ sup_{v ∈ L, v ≠ 0} |a w v| / ‖v‖` for
`w ∈ K`, stated with the restricted functional's norm. -/
def DiscreteInfSup (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (α : ℝ) :
    Prop :=
  ∀ w ∈ K, α * ‖w‖ ≤ ‖(a w).comp L.subtypeL‖

/-- Babuška (AH Thm 9.2.1): with `dim K = dim L` and the discrete inf–sup condition, the
Petrov–Galerkin problem is uniquely solvable and `‖u - u_N‖ ≤ (1 + M / α) inf_{w ∈ K} ‖u - w‖`. -/
theorem existsUnique [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {α : ℝ} (hα : 0 < α)
    (hinf : DiscreteInfSup a K L α) : ∃! u, IsPetrovGalerkinSolution a ℓ K L u := by
  sorry

theorem norm_sub_le [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) {M α : ℝ} (hα : 0 < α)
    (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖) (hinf : DiscreteInfSup a K L α)
    (hN : IsPetrovGalerkinSolution a ℓ K L u) {ustar : U} (hstar : ∀ v, a ustar v = ℓ v) {w : U}
    (hw : w ∈ K) : ‖ustar - u‖ ≤ (1 + M / α) * ‖ustar - w‖ := by
  sorry

/-- AH Cor 9.2.3: under a uniform discrete inf–sup condition on a monotone dense family,
Petrov–Galerkin solutions converge. -/
theorem tendsto {K : ℕ → Submodule 𝕜 U} {L : ℕ → Submodule 𝕜 V} [∀ n, FiniteDimensional 𝕜 (K n)]
    [∀ n, FiniteDimensional 𝕜 (L n)] (hdim : ∀ n, Module.finrank 𝕜 (K n) = Module.finrank 𝕜 (L n))
    {M α : ℝ} (hα : 0 < α) (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hinf : ∀ n, DiscreteInfSup a (K n) (L n) α) (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set U))) {uN : ℕ → U}
    (hN : ∀ n, IsPetrovGalerkinSolution a ℓ (K n) (L n) (uN n)) {ustar : U}
    (hstar : ∀ v, a ustar v = ℓ v) : Filter.Tendsto uN Filter.atTop (nhds ustar) := by
  sorry

end IsPetrovGalerkinSolution

section Strang

/-! ### The generalized Galerkin method (AH §9.3)

Stated on one abstract normed space `W` (the book's `V + V_N` with `‖·‖_N`): the exact solution
`u`, a form `a_N` bounded on `W × K` and coercive on `K`, a functional `ℓ_N` on `K`; the
Hilbert space `V` and the original problem never enter. -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The generalized Galerkin problem (AH (9.3.1)). -/
def IsGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜) (K : Submodule 𝕜 W)
    (uN : W) : Prop :=
  uN ∈ K ∧ ∀ v ∈ K, aN uN v = ℓN v

/-- Strang's first lemma (AH Thm 9.3.1): with `a_N` bounded by `M` on `W × K` and coercive with
constant `c` on `K`,
`‖u - u_N‖ ≤ (1 + M/c) inf_{v ∈ K} ‖u - v‖ + (1/c) sup_{w ∈ K, w ≠ 0} |a_N(u, w) - ℓ_N(w)| / ‖w‖`,
in the pointwise form with an explicit consistency bound `δ`. -/
theorem strang_first {aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜} {ℓN : W →ₗ[𝕜] 𝕜} {K : Submodule 𝕜 W} {M c : ℝ}
    (hc : 0 < c) (hM : ∀ w, ∀ v ∈ K, ‖aN w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) {uN : W}
    (hN : IsGeneralizedGalerkinSolution aN ℓN K uN) (u : W) {δ : ℝ}
    (hδ : ∀ w ∈ K, ‖aN u w - ℓN w‖ ≤ δ * ‖w‖) {v : W} (hv : v ∈ K) :
    ‖u - uN‖ ≤ (1 + M / c) * ‖u - v‖ + δ / c := by
  sorry

/-- Unique solvability of the generalized Galerkin problem on a finite-dimensional `K` with
coercive `a_N` (needs only finite dimension, not Lax–Milgram). -/
theorem existsUnique_isGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜)
    (K : Submodule 𝕜 W) [FiniteDimensional 𝕜 K] {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) :
    ∃! uN, IsGeneralizedGalerkinSolution aN ℓN K uN := by
  sorry

end Strang
