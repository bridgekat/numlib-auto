import Numlib.Krylov.LanczosTridiag
import Numlib.Optimization.Subproblem.KrylovConvergence
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis–Gould–Toint §10.1: Krylov-subspace methods

Surface file for [cartis2022evaluation] §10.1: the subspace subproblems (10.1.1)–(10.1.2), the
Krylov subspaces `𝒦ₖ = 𝒦(M⁻¹H, M⁻¹g, k)`, the preconditioned Lanczos method (Algorithm 10.1.1)
with its properties (10.1.3)–(10.1.7), (10.2.1), and the hard-case obstruction of §10.1.2.

## Main definitions

* `krylovSpace H M g k` — the Krylov subspace `𝒦ₖ = span {(M⁻¹H)ⁱ M⁻¹g}_{i<k}`;
  `gradeHM H M g` — the grade of `M⁻¹H` with respect to `M⁻¹g`.
* `IsTRSubspaceSolution`, `IsRegSubspaceSolution` — the subspace subproblems (10.1.1).
* `lanczosVec hM H g j` (the book's `q_{j+1}`), `lanczosBasis hM H g k` (the matrix `Qₖ`),
  `lanczosTridiag hM H g k` (the tridiagonal `Tₖ`) and `lanczosGrad hM H g k` (`Qₖᵀ g`): the
  output of the preconditioned Lanczos method, defined through the Lanczos process of the operator
  `M⁻¹H` in the `M`-inner product (`Subproblem.ScaledSpace`).
* `algorithm_10_1_1` — runs of Algorithm 10.1.1.

## Main results

* `subspaceSolution_iff_reduced` — (10.1.2): a subspace subproblem with basis matrix `S` is the
  subproblem for the reduced data `Sᵀg`, `SᵀHS`, `SᵀMS`.
* `algorithm_10_1_1.q_eq_lanczosVec` and companions — every run of Algorithm 10.1.1 computes the
  Lanczos vectors and coefficients; `algorithm_10_1_1_spec` — (10.1.3)–(10.1.4), (10.2.1),
  (10.1.7) and the termination at the grade.
* `isRegSubspaceSolution_krylov_iff`, `isTRSubspaceSolution_krylov_iff` — (10.1.5)–(10.1.6): on
  `𝒦ₖ`, the subspace subproblems are the problems for `(γ₁ e₁, Tₖ)` in the Euclidean norm of `ℝᵏ`.
* `krylov_hardCase_10_1_2` — §10.1.2: in the hard case the Krylov subspaces never see the
  leftmost eigenvectors.

## Implementation notes

Lanczos indices are `0`-based in the definitions: `lanczosVec hM H g j` is the book's `q_{j+1}`.
Runs of Algorithm 10.1.1 are indexed as in the book (`k ≥ 1`); the stopping test `γₖ = 0` is
modelled by Lean's convention `x / 0 = 0`, under which every quantity vanishes after the stop.

## Corrections to the source

* (10.1.7): the leading block of `Tₖ` is `T_{k-1}`, not `T_{k-1}⁻¹`
  (`algorithm_10_1_1_spec`). The nesting of the Krylov subspaces is
  `𝒦(A, b, k + 1) = span (𝒦(A, b, k) ∪ {Aᵏ b})`, not a union.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08

variable {n : ℕ}

/-! ### Krylov subspaces -/

section KrylovSpace

variable (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))

/-- The **Krylov subspace** `𝒦ₖ = 𝒦(M⁻¹H, M⁻¹g, k) = span {(M⁻¹H)ⁱ M⁻¹g}_{i<k}` of
[cartis2022evaluation] §10.1.1. -/
noncomputable def krylovSpace (k : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Krylov.subspace (toEuclideanLin (M⁻¹ * H)) (toEuclideanLin M⁻¹ g) k

/-- The **grade** `grade(M⁻¹H, M⁻¹g)` of [cartis2022evaluation] §10.1.1: the least `k` with
`𝒦(M⁻¹H, M⁻¹g, k) = 𝒦(M⁻¹H, M⁻¹g)`. -/
noncomputable def gradeHM : ℕ :=
  Krylov.grade (toEuclideanLin (M⁻¹ * H)) (toEuclideanLin M⁻¹ g)

/-- The Krylov subspaces are nested. -/
theorem krylovSpace_mono : Monotone (krylovSpace H M g) :=
  Krylov.subspace_mono _ _

/-- `dim 𝒦ₖ = min k grade`: in particular `dim 𝒦ₖ ≤ k`. -/
theorem finrank_krylovSpace (k : ℕ) :
    Module.finrank ℝ (krylovSpace H M g k) = min k (gradeHM H M g) :=
  Krylov.finrank_subspace _ _ k

/-- `grade(M⁻¹H, M⁻¹g) ≤ n`. -/
theorem gradeHM_le : gradeHM H M g ≤ n :=
  (Krylov.grade_le_finrank _ _).trans_eq (finrank_euclideanSpace_fin)

/-- The Krylov subspaces stabilize at the grade. -/
theorem krylovSpace_eq_of_gradeHM_le {k : ℕ} (h : gradeHM H M g ≤ k) :
    krylovSpace H M g k = krylovSpace H M g (gradeHM H M g) :=
  Krylov.subspace_eq_of_grade_le _ _ h

/-- `𝒦(A, b, k + 1) = span (𝒦(A, b, k) ∪ {Aᵏ b})`. -/
theorem krylovSpace_succ (k : ℕ) :
    krylovSpace H M g (k + 1) =
      krylovSpace H M g k ⊔ ℝ ∙ ((toEuclideanLin (M⁻¹ * H)) ^ k) (toEuclideanLin M⁻¹ g) := by
  simp only [krylovSpace, Krylov.subspace]
  rw [show Set.range (fun i : Fin (k + 1) => ((toEuclideanLin (M⁻¹ * H)) ^ (i : ℕ))
      (toEuclideanLin M⁻¹ g)) = Set.range (fun i : Fin k => ((toEuclideanLin (M⁻¹ * H)) ^ (i : ℕ))
      (toEuclideanLin M⁻¹ g)) ∪ {((toEuclideanLin (M⁻¹ * H)) ^ k) (toEuclideanLin M⁻¹ g)} by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.lastCases (motive := fun i : Fin (k + 1) => (i : ℕ) = k ∨ (i : ℕ) < k)
        (Or.inl rfl) (fun j => Or.inr j.2) i with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl ⟨⟨i, h⟩, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨i.castSucc, rfl⟩
      · exact ⟨Fin.last k, rfl⟩, Submodule.span_union]

/-- At the grade, the Krylov subspace is invariant under `M⁻¹H`. -/
theorem krylovSpace_gradeHM_mem_invtSubmodule :
    krylovSpace H M g (gradeHM H M g) ∈ Module.End.invtSubmodule (toEuclideanLin (M⁻¹ * H)) :=
  Krylov.subspace_grade_mem_invtSubmodule _ _

end KrylovSpace

/-! ### The bridge to the `M`-inner product space -/

section Bridge

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- The scaled operator, as a linear map, is the energy-space transport of `M⁻¹ H`. -/
theorem coe_scaledOp_eq (hM : M.PosDef) :
    (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) =
      hM.isPreconditioner_toEuclideanLin.energyEnd (toEuclideanLin (M⁻¹ * H)) := by
  rw [scaledOp, LinearMap.coe_toContinuousLinearMap, toEuclideanLin_mul]

/-- The Krylov subspaces of `M⁻¹H` and `M⁻¹g` are the Krylov subspaces of the scaled operator and
gradient, transported to the `M`-inner product space. -/
theorem map_toScaled_krylovSpace (hM : M.PosDef) (k : ℕ) :
    (krylovSpace H M g k).map (toScaled hM : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ScaledSpace hM) =
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) k := by
  rw [coe_scaledOp_eq, scaledGrad, hM.isPreconditioner_toEuclideanLin.subspace_energyEnd]
  rfl

/-- Membership in the Krylov subspace, in the `M`-inner product space. -/
theorem toScaled_mem_krylov_iff (hM : M.PosDef) {k : ℕ} {s : EuclideanSpace ℝ (Fin n)} :
    toScaled hM s ∈
        Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k ↔
      s ∈ krylovSpace H M g k := by
  rw [← map_toScaled_krylovSpace hM k]
  constructor
  · rintro ⟨x, hx, hxs⟩
    rwa [← (toScaled hM).injective hxs]
  · intro hs
    exact ⟨s, hs, rfl⟩

/-- The grade of `M⁻¹H` with respect to `M⁻¹g` is that of the scaled operator and gradient. -/
theorem gradeHM_eq (hM : M.PosDef) :
    gradeHM H M g =
      Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) := by
  have h : ∀ m, min m (gradeHM H M g) =
      min m (Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g)) := fun m => by
    rw [← finrank_krylovSpace, ← Krylov.finrank_subspace, ← map_toScaled_krylovSpace hM m,
      LinearEquiv.finrank_map_eq]
  have := h (gradeHM H M g + Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
    (scaledGrad hM g))
  omega

end Bridge

/-! ### Subspace subproblems -/

section Subspace

variable {k : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- `s` is a **global minimizer of the trust-region subproblem on the subspace `S`** (10.1.1) of
[cartis2022evaluation]: `s ∈ S`, `‖s‖_M ≤ Δ` and `m(s) ≤ m(u)` for every `u ∈ S` with
`‖u‖_M ≤ Δ`. -/
def IsTRSubspaceSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (Δ : ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ S ∧ mNorm M s ≤ Δ ∧ ∀ u ∈ S, mNorm M u ≤ Δ → model g H s ≤ model g H u

/-- `s` is a **global minimizer of the regularization subproblem on the subspace `S`** (10.1.1) of
[cartis2022evaluation]: `s ∈ S` and `m^R(s, σ, r) ≤ m^R(u, σ, r)` for every `u ∈ S`. -/
def IsRegSubspaceSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ S ∧ ∀ u ∈ S, regModel g H M σ r s ≤ regModel g H M σ r u

/-- The quadratic model at `S y` is the reduced model of `Sᵀ g`, `Sᵀ H S` at `y`. -/
theorem model_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    model g H (toEuclideanLin S y) = model (toEuclideanLin Sᵀ g) (Sᵀ * H * S) y := by
  rw [model_def, model_def, toEuclideanLin_transpose_inner_left, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_transpose_inner_right]

/-- The scaled norm of `S y` is the scaled norm of `y` for the reduced scaling `Sᵀ M S`. -/
theorem mNorm_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    mNorm M (toEuclideanLin S y) = mNorm (Sᵀ * M * S) y := by
  rw [mNorm_def, mNorm_def, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right]

/-- The regularized model at `S y` is the reduced regularized model at `y`. -/
theorem regModel_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (σ r : ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    regModel g H M σ r (toEuclideanLin S y) =
      regModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) σ r y := by
  rw [Chapter08.regModel_def, Chapter08.regModel_def, model_toEuclideanLin, mNorm_toEuclideanLin]

/-- **The reduced subproblems** (10.1.2) of [cartis2022evaluation]. If the columns of `S` span the
subspace `𝒮` (`𝒮 = range S`), then `s = S s̄` solves the subspace subproblems (10.1.1) iff `s̄`
solves the subproblems (8.1.2)/(8.1.3) for the reduced data `ḡ = Sᵀ g`, `H̄ = Sᵀ H S`,
`M̄ = Sᵀ M S` on `ℝᵏ`. -/
theorem subspaceSolution_iff_reduced (S : Matrix (Fin n) (Fin k) ℝ)
    (sbar : EuclideanSpace ℝ (Fin k)) :
    (∀ Δ, IsTRSubspaceSolution g H M Δ (LinearMap.range (toEuclideanLin S))
        (toEuclideanLin S sbar) ↔
      IsTrustRegionSolution (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) Δ sbar) ∧
    ∀ σ r, IsRegSubspaceSolution g H M σ r (LinearMap.range (toEuclideanLin S))
        (toEuclideanLin S sbar) ↔
      IsRegularizationSolution (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) σ r sbar := by
  refine ⟨fun Δ => ?_, fun σ r => ?_⟩
  · simp only [IsTRSubspaceSolution, isTrustRegionSolution_iff, LinearMap.mem_range,
      exists_apply_eq_apply, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      mNorm_toEuclideanLin, model_toEuclideanLin]
  · simp only [IsRegSubspaceSolution, isRegularizationSolution_iff, LinearMap.mem_range,
      exists_apply_eq_apply, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      regModel_toEuclideanLin]

end Subspace

/-! ### The Lanczos vectors, the basis `Qₖ` and the tridiagonal `Tₖ` -/

section Lanczos

/-- The **Lanczos vector** `q_{j+1}` of [cartis2022evaluation] (10.1.3) (`0`-based index `j`): the
`j`-th vector of the Lanczos process of `M⁻¹H` started from `M⁻¹g` in the `M`-inner product, read
back in `ℝⁿ`. It is `0` from the grade on. Algorithm 10.1.1 computes it
(`algorithm_10_1_1.q_eq_lanczosVec`). -/
noncomputable def lanczosVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (toScaled hM).symm
    (Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j)

/-- The **Lanczos basis matrix** `Qₖ = (q₁, …, qₖ)` of [cartis2022evaluation] (10.1.3). -/
noncomputable def lanczosBasis {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => lanczosVec hM H g j i

/-- The **Lanczos tridiagonal matrix** `Tₖ` of [cartis2022evaluation] (10.1.3): diagonal
`ρ₁, …, ρₖ` and off-diagonal `γ₂, …, γₖ` (`Lanczos.tridiag` of `M⁻¹H` in the `M`-inner
product). -/
noncomputable def lanczosTridiag {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Lanczos.tridiag (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k

theorem lanczosTridiag_def {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    lanczosTridiag hM H g k =
      Lanczos.tridiag (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
  rfl

/-- The **reduced gradient** `ḡₖ = Qₖᵀ g` of [cartis2022evaluation] (10.1.2); it is `γ₁ e₁`
(`lanczosGrad_eq`). -/
noncomputable def lanczosGrad {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin k) :=
  toEuclideanLin (lanczosBasis hM H g k)ᵀ g

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)} (hM : M.PosDef) {k : ℕ}

/-- The Lanczos vectors in the `M`-inner product space are the Arnoldi vectors. -/
@[simp]
theorem toScaled_lanczosVec (j : ℕ) :
    toScaled hM (lanczosVec hM H g j) =
      Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j :=
  (toScaled hM).apply_symm_apply _

/-- `Qₖ y = ∑ⱼ yⱼ qⱼ₊₁`. -/
theorem toEuclideanLin_lanczosBasis (y : EuclideanSpace ℝ (Fin k)) :
    toEuclideanLin (lanczosBasis hM H g k) y = ∑ j, y j • lanczosVec hM H g j := by
  ext i
  simp [lanczosBasis, toEuclideanLin_apply, mulVec, dotProduct, mul_comm]

/-- `Qₖ eⱼ = qⱼ₊₁`. -/
theorem toEuclideanLin_lanczosBasis_single (j : Fin k) :
    toEuclideanLin (lanczosBasis hM H g k) (EuclideanSpace.single j 1) = lanczosVec hM H g j := by
  rw [toEuclideanLin_lanczosBasis]
  simp [PiLp.single_apply]

/-- In the `M`-inner product space, `Qₖ y = ∑ⱼ yⱼ vⱼ` for the Arnoldi vectors `vⱼ`. -/
theorem toScaled_lanczosBasis (y : EuclideanSpace ℝ (Fin k)) :
    toScaled hM (toEuclideanLin (lanczosBasis hM H g k) y) =
      ∑ j, y j • Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) j := by
  rw [toEuclideanLin_lanczosBasis, map_sum]
  simp only [map_smul, toScaled_lanczosVec]

/-- **The columns of `Qₖ` span `𝒦ₖ`**: `range Qₖ = 𝒦ₖ`. -/
theorem range_lanczosBasis :
    LinearMap.range (toEuclideanLin (lanczosBasis hM H g k)) = krylovSpace H M g k := by
  ext s
  rw [LinearMap.mem_range, ← toScaled_mem_krylov_iff hM]
  constructor
  · rintro ⟨y, rfl⟩
    rw [toScaled_lanczosBasis]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ j.2)
  · intro hs
    refine ⟨WithLp.toLp 2 fun j : Fin k => ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) j, toScaled hM s⟫, (toScaled hM).injective ?_⟩
    rw [toScaled_lanczosBasis]
    conv_rhs => rw [Arnoldi.eq_sum_inner_smul_vec _ _ hs]
    exact Fin.sum_univ_eq_sum_range (fun j => ⟪Arnoldi.vec (scaledOp H hM : _ →ₗ[ℝ] _)
      (scaledGrad hM g) j, toScaled hM s⟫ • Arnoldi.vec (scaledOp H hM : _ →ₗ[ℝ] _)
        (scaledGrad hM g) j) k

/-- A matrix entry is a bilinear form of coordinate vectors. -/
private theorem entry_eq_inner {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    A i j = ⟪EuclideanSpace.single i 1, toEuclideanLin A (EuclideanSpace.single j 1)⟫ := by
  simp [EuclideanSpace.inner_single_left, toEuclideanLin_apply]

/-- A matrix entry is a coordinate of the image of a coordinate vector. -/
private theorem entry_eq_apply_single {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (i : Fin m)
    (j : Fin p) :
    A i j = toEuclideanLin A (EuclideanSpace.single j 1) i := by
  simp [toEuclideanLin_apply]

/-- The entries of `Qₖᵀ A Qₖ` are `⟪qᵢ₊₁, A qⱼ₊₁⟫`. -/
theorem lanczosBasis_transpose_mul_mul_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin k) :
    ((lanczosBasis hM H g k)ᵀ * A * lanczosBasis hM H g k) i j =
      ⟪lanczosVec hM H g i, toEuclideanLin A (lanczosVec hM H g j)⟫ := by
  refine (entry_eq_inner _ i j).trans ?_
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right, toEuclideanLin_lanczosBasis_single,
    toEuclideanLin_lanczosBasis_single]

/-- The entries of `Qₖᵀ g` are `⟪qᵢ₊₁, g⟫`. -/
theorem lanczosGrad_apply (i : Fin k) : lanczosGrad hM H g k i = ⟪lanczosVec hM H g i, g⟫ := by
  rw [← toEuclideanLin_lanczosBasis_single hM (H := H) (g := g) i,
    ← toEuclideanLin_transpose_inner_right, EuclideanSpace.inner_single_left]
  simp [lanczosGrad]

/-- `⟪qᵢ₊₁, M qⱼ₊₁⟫` is the `M`-inner product of the Arnoldi vectors. -/
theorem inner_lanczosVec_M (i j : ℕ) :
    ⟪lanczosVec hM H g i, toEuclideanLin M (lanczosVec hM H g j)⟫ =
      ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i,
        Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j⟫ := by
  rw [real_inner_comm, ← inner_toScaled, real_inner_comm, toScaled_lanczosVec, toScaled_lanczosVec]

/-- `⟪qᵢ₊₁, H qⱼ₊₁⟫` is the Arnoldi coefficient `hᵢⱼ` of the scaled operator. -/
theorem inner_lanczosVec_H (i j : ℕ) :
    ⟪lanczosVec hM H g i, toEuclideanLin H (lanczosVec hM H g j)⟫ =
      Arnoldi.coeff (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) i j := by
  rw [real_inner_comm, ← inner_scaledOp_toScaled, real_inner_comm, toScaled_lanczosVec,
    toScaled_lanczosVec, Arnoldi.coeff]
  rfl

/-- `⟪qᵢ₊₁, g⟫ = ⟪vᵢ, M⁻¹ g⟫_M`. -/
theorem inner_lanczosVec_g (i : ℕ) :
    ⟪lanczosVec hM H g i, g⟫ =
      ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i,
        scaledGrad hM g⟫ := by
  rw [← toScaled_lanczosVec, inner_toScaled_scaledGrad]

/-- **`Qₖ` is `M`-orthonormal** ((10.1.3)): `Qₖᵀ M Qₖ = Iₖ` for `k ≤ grade(M⁻¹H, M⁻¹g)`. -/
theorem lanczosBasis_transpose_mul_M (hk : k ≤ gradeHM H M g) :
    (lanczosBasis hM H g k)ᵀ * M * lanczosBasis hM H g k = 1 := by
  ext i j
  rw [lanczosBasis_transpose_mul_mul_apply, inner_lanczosVec_M, Matrix.one_apply]
  rw [gradeHM_eq hM] at hk
  split_ifs with hij
  · subst hij
    rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hk),
      one_pow]
  · exact Arnoldi.inner_vec_eq_zero _ _ (fun h => hij (Fin.ext h))

/-- **`Qₖ` tridiagonalizes `H`** ((10.1.3)): `Qₖᵀ H Qₖ = Tₖ`. -/
theorem lanczosBasis_transpose_mul_H (hH : H.IsHermitian) :
    (lanczosBasis hM H g k)ᵀ * H * lanczosBasis hM H g k = lanczosTridiag hM H g k := by
  ext i j
  rw [lanczosBasis_transpose_mul_mul_apply, inner_lanczosVec_H]
  have h := congrFun (congrFun (Lanczos.hessenbergSq_eq_map_tridiag (scaledGrad hM g)
    (isSymmetric_scaledOp (hM := hM) hH) k) i) j
  simpa [Arnoldi.hessenbergSq, lanczosTridiag] using h

/-- **The reduced gradient** ((10.1.3)–(10.1.4)): `Qₖᵀ g = γ₁ e₁` with `γ₁ = ‖g‖_{M⁻¹}`. -/
theorem lanczosGrad_eq (hk : 0 < k) :
    lanczosGrad hM H g k = EuclideanSpace.single ⟨0, hk⟩ (mNorm M⁻¹ g) := by
  ext i
  rw [lanczosGrad_apply, inner_lanczosVec_g, mNorm_inv_eq_norm_scaledGrad hM,
    PiLp.single_apply]
  rcases eq_or_ne (scaledGrad hM g) 0 with hb | hb
  · rw [hb]; simp
  · set V := Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
      with hV
    have hv0 : V 0 = ‖scaledGrad hM g‖⁻¹ • scaledGrad hM g := by
      rw [hV, Arnoldi.vec_zero _ _ hb]; rfl
    have hb' : scaledGrad hM g = ‖scaledGrad hM g‖ • V 0 := by
      rw [hv0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hb), one_smul]
    have hi : ⟪V i, scaledGrad hM g⟫ = ‖scaledGrad hM g‖ * ⟪V i, V 0⟫ := by
      conv_lhs => rw [hb']
      rw [real_inner_smul_right]
    rw [hi]
    split_ifs with hi0
    · subst hi0
      have : (0 : ℕ) < Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
          (scaledGrad hM g) := Krylov.grade_pos_of_ne_zero _ _ hb
      rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade _ _ this]
      simp
    · rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hi0 (Fin.ext h)), mul_zero]

/-- **The Lanczos relation** (10.2.1) of [cartis2022evaluation]: with `k = m + 1`,
`H Qₖ - M Qₖ Tₖ = γₖ₊₁ wₖ₊₁ eₖᵀ`, where `γₖ₊₁ wₖ₊₁ = γₖ₊₁ M qₖ₊₁` and `γₖ₊₁ = β_m` is the next
Lanczos coefficient (`0` at the grade). -/
theorem lanczos_relation (hH : H.IsHermitian) (m : ℕ) :
    H * lanczosBasis hM H g (m + 1) -
        M * lanczosBasis hM H g (m + 1) * lanczosTridiag hM H g (m + 1) =
      Matrix.of fun a (j : Fin (m + 1)) => if j = Fin.last m then
        Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
          toEuclideanLin M (lanczosVec hM H g (m + 1)) a else 0 := by
  -- the relation applied to a vector `y`
  have key : ∀ y : EuclideanSpace ℝ (Fin (m + 1)),
      toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g (m + 1)) y) =
        toEuclideanLin M (toEuclideanLin (lanczosBasis hM H g (m + 1))
          (toEuclideanLin (lanczosTridiag hM H g (m + 1)) y)) +
        (Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
          y (Fin.last m)) • toEuclideanLin M (lanczosVec hM H g (m + 1)) := by
    intro y
    have h1 := Lanczos.apply_sum (scaledGrad hM g) (isSymmetric_scaledOp (hM := hM) hH) m
      (WithLp.ofLp y)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, RCLike.ofReal_real_eq_id,
      id] at h1
    have h2 : toEuclideanLin M⁻¹ (toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g (m + 1)) y))
        = toEuclideanLin (lanczosBasis hM H g (m + 1))
            (toEuclideanLin (lanczosTridiag hM H g (m + 1)) y) +
          (Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
            y (Fin.last m)) • lanczosVec hM H g (m + 1) := by
      apply (toScaled hM).injective
      rw [← scaledOp_toScaled, toScaled_lanczosBasis, map_add, toScaled_lanczosBasis, map_smul,
        toScaled_lanczosVec]
      exact h1
    have h3 := congrArg (toEuclideanLin M) h2
    rw [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_add, map_smul] at h3
    exact h3
  ext a j
  refine (entry_eq_apply_single _ a j).trans ?_
  rw [map_sub, LinearMap.sub_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, key, PiLp.sub_apply, PiLp.add_apply,
    add_sub_cancel_left, PiLp.smul_apply, Matrix.of_apply, PiLp.single_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp
  · simp [hj, Ne.symm hj]

end Lanczos

/-! ### The reduced Krylov subproblems (10.1.5)–(10.1.6) -/

section Reduced

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)} (hM : M.PosDef) {k : ℕ}

/-- **The trust-region subproblem on `𝒦ₖ`** ((10.1.5) of [cartis2022evaluation]): for
`k ≤ grade(M⁻¹H, M⁻¹g)`, `Qₖ s̄` solves the trust-region subproblem on `𝒦ₖ` iff `s̄` solves the
trust-region subproblem for `(Qₖᵀ g, Tₖ) = (γ₁ e₁, Tₖ)` in the Euclidean norm of `ℝᵏ`. Every
element of `𝒦ₖ` is some `Qₖ s̄` (`range_lanczosBasis`). -/
theorem isTRSubspaceSolution_krylov_iff (hH : H.IsHermitian) (hk : k ≤ gradeHM H M g) (Δ : ℝ)
    (sbar : EuclideanSpace ℝ (Fin k)) :
    IsTRSubspaceSolution g H M Δ (krylovSpace H M g k)
        (toEuclideanLin (lanczosBasis hM H g k) sbar) ↔
      IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbar := by
  have h := (subspaceSolution_iff_reduced (g := g) (H := H) (M := M) (lanczosBasis hM H g k)
    sbar).1 Δ
  rwa [range_lanczosBasis, lanczosBasis_transpose_mul_M hM hk,
    lanczosBasis_transpose_mul_H hM hH] at h

/-- **The regularization subproblem on `𝒦ₖ`** ((10.1.6) of [cartis2022evaluation]): for
`k ≤ grade(M⁻¹H, M⁻¹g)`, `Qₖ s̄` solves the regularization subproblem on `𝒦ₖ` iff `s̄` solves the
regularization subproblem for `(Qₖᵀ g, Tₖ) = (γ₁ e₁, Tₖ)` in the Euclidean norm of `ℝᵏ`. -/
theorem isRegSubspaceSolution_krylov_iff (hH : H.IsHermitian) (hk : k ≤ gradeHM H M g)
    (σ r : ℝ) (sbar : EuclideanSpace ℝ (Fin k)) :
    IsRegSubspaceSolution g H M σ r (krylovSpace H M g k)
        (toEuclideanLin (lanczosBasis hM H g k) sbar) ↔
      IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar := by
  have h := (subspaceSolution_iff_reduced (g := g) (H := H) (M := M) (lanczosBasis hM H g k)
    sbar).2 σ r
  rwa [range_lanczosBasis, lanczosBasis_transpose_mul_M hM hk,
    lanczosBasis_transpose_mul_H hM hH] at h

/-- `‖Qₖ y‖_M = ‖y‖` for `k ≤ grade(M⁻¹H, M⁻¹g)`. -/
theorem mNorm_lanczosBasis (hk : k ≤ gradeHM H M g) (y : EuclideanSpace ℝ (Fin k)) :
    mNorm M (toEuclideanLin (lanczosBasis hM H g k) y) = ‖y‖ := by
  rw [mNorm_toEuclideanLin, lanczosBasis_transpose_mul_M hM hk, mNorm_one]

/-- The regularization subproblem on `𝒦ₖ` in the `M`-inner product space. -/
theorem isRegSubspaceSolution_iff_scaled {σ r : ℝ} {s : EuclideanSpace ℝ (Fin n)} :
    IsRegSubspaceSolution g H M σ r (krylovSpace H M g k) s ↔
      toScaled hM s ∈
          Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
            (scaledGrad hM g) k ∧
        IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
          (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
            (scaledGrad hM g) k : Set (ScaledSpace hM)) (toScaled hM s) := by
  rw [IsRegSubspaceSolution, toScaled_mem_krylov_iff, isMinOn_iff]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h u hu => ?_⟩
  · obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
    rw [← regModel_eq_regModel, ← regModel_eq_regModel]
    exact h u ((toScaled_mem_krylov_iff hM).1 hx)
  · rw [regModel_eq_regModel hM, regModel_eq_regModel hM]
    exact h _ ((toScaled_mem_krylov_iff hM).2 hu)

end Reduced

/-! ### Algorithm 10.1.1 -/

/-- **Algorithm 10.1.1 of [cartis2022evaluation] (the preconditioned Lanczos method)**, as a run:
sequences indexed by the book's `k ≥ 1` with `t₁ = g`, `w₀ = 0` and, for `k ≥ 1`,
`yₖ = M⁻¹ tₖ`, `γₖ = √⟪tₖ, yₖ⟫`, `wₖ = tₖ/γₖ`, `qₖ = yₖ/γₖ`, `ρₖ = ⟪qₖ, H qₖ⟫` and
`tₖ₊₁ = H qₖ - ρₖ wₖ - γₖ wₖ₋₁`. The stop at `γₖ = 0` is built in through the convention
`x / 0 = 0`: from then on every quantity vanishes. -/
structure algorithm_10_1_1 (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (t y w q : ℕ → EuclideanSpace ℝ (Fin n)) (γ ρ : ℕ → ℝ) : Prop where
  /-- `t₁ = g`. -/
  t_one : t 1 = g
  /-- `w₀ = 0`. -/
  w_zero : w 0 = 0
  /-- `yₖ = M⁻¹ tₖ`. -/
  y_eq : ∀ k, 1 ≤ k → y k = toEuclideanLin M⁻¹ (t k)
  /-- `γₖ = √⟪tₖ, yₖ⟫`. -/
  gamma_eq : ∀ k, 1 ≤ k → γ k = √⟪t k, y k⟫
  /-- `wₖ = tₖ / γₖ`. -/
  w_eq : ∀ k, 1 ≤ k → w k = (γ k)⁻¹ • t k
  /-- `qₖ = yₖ / γₖ`. -/
  q_eq : ∀ k, 1 ≤ k → q k = (γ k)⁻¹ • y k
  /-- `ρₖ = ⟪qₖ, H qₖ⟫`. -/
  rho_eq : ∀ k, 1 ≤ k → ρ k = ⟪q k, toEuclideanLin H (q k)⟫
  /-- `tₖ₊₁ = H qₖ - ρₖ wₖ - γₖ wₖ₋₁`. -/
  t_succ : ∀ k, 1 ≤ k → t (k + 1) = toEuclideanLin H (q k) - ρ k • w k - γ k • w (k - 1)

/-- The state `(tₖ₊₁, wₖ)` of Algorithm 10.1.1 after `k` iterations. -/
private noncomputable def lanczosState (H M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)
  | 0 => (g, 0)
  | k + 1 =>
    let t := (lanczosState H M g k).1
    let y := toEuclideanLin M⁻¹ t
    let γ := √⟪t, y⟫
    let q := γ⁻¹ • y
    (toEuclideanLin H q - ⟪q, toEuclideanLin H q⟫ • (γ⁻¹ • t) - γ • (lanczosState H M g k).2,
      γ⁻¹ • t)

/-- The Arnoldi vector `v₀ = b/‖b‖`, also for `b = 0`. -/
private theorem vec_zero' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (b : E) : Arnoldi.vec A b 0 = ‖b‖⁻¹ • b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [smul_zero, Arnoldi.vec_eq_zero_iff_pow_apply_mem, Krylov.subspace_zero, map_zero]
    exact Submodule.zero_mem _
  · exact Arnoldi.vec_zero A b hb

namespace algorithm_10_1_1

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}
  {t y w q : ℕ → EuclideanSpace ℝ (Fin n)} {γ ρ : ℕ → ℝ}

/-- **Algorithm 10.1.1 is well defined**: it has a run. -/
theorem exists_run (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    ∃ t y w q γ ρ, algorithm_10_1_1 H M g t y w q γ ρ := by
  set T : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (lanczosState H M g (k - 1)).1
  set Y : ℕ → EuclideanSpace ℝ (Fin n) := fun k => toEuclideanLin M⁻¹ (T k)
  set Γ : ℕ → ℝ := fun k => √⟪T k, Y k⟫
  set W : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Γ k)⁻¹ • T k
  set Q : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Γ k)⁻¹ • Y k
  refine ⟨T, Y, fun k => if k = 0 then 0 else W k, Q, Γ,
    fun k => ⟪Q k, toEuclideanLin H (Q k)⟫, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun k hk => by simp [Nat.one_le_iff_ne_zero.1 hk, W], fun _ _ => rfl, fun _ _ => rfl,
    fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, ite_false]
  change (lanczosState H M g (j + 1)).1 = _
  rw [lanczosState]
  rcases j with _ | j
  · simp [T, W, Q, Y, Γ, lanczosState]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rfl

variable (h : algorithm_10_1_1 H M g t y w q γ ρ)
include h

/-- `tₖ = M yₖ`. -/
theorem t_eq (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : t k = toEuclideanLin M (y k) := by
  rw [h.y_eq k hk, toEuclideanLin_mul_nonsing_inv_apply hM.isUnit]

/-- `γₖ = ‖yₖ‖_M`. -/
theorem gamma_eq_norm (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : γ k = ‖toScaled hM (y k)‖ := by
  rw [h.gamma_eq k hk, h.t_eq hM hk, norm_toScaled]

/-- `wₖ = M qₖ`. -/
theorem w_eq_M (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : w k = toEuclideanLin M (q k) := by
  rw [h.w_eq k hk, h.q_eq k hk, map_smul, h.t_eq hM hk]

/-- The vector `M⁻¹ wₖ₋₁` (with `w₀ = 0`). -/
theorem inv_w_pred (hM : M.PosDef) (k : ℕ) :
    toEuclideanLin M⁻¹ (w k) = if k = 0 then 0 else q k := by
  split_ifs with hk
  · rw [hk, h.w_zero, map_zero]
  · rw [h.w_eq_M hM (Nat.one_le_iff_ne_zero.2 hk), toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- `yₖ₊₁ = M⁻¹ H qₖ - ρₖ qₖ - γₖ qₖ₋₁` (with `q₀` replaced by `0`). -/
theorem y_succ (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    y (k + 1) = toEuclideanLin M⁻¹ (toEuclideanLin H (q k)) - ρ k • q k -
      γ k • (if k - 1 = 0 then 0 else q (k - 1)) := by
  rw [h.y_eq (k + 1) (by omega), h.t_succ k hk, map_sub, map_sub, map_smul, map_smul,
    h.inv_w_pred hM k, h.inv_w_pred hM (k - 1), ite_eq_right (by omega)]

/-- One step of the identification: if `M⁻¹`-transported `yᵢ₊₁` is the `i`-th unnormalized
Lanczos vector (`M⁻¹g` for `i = 0`), then `qᵢ₊₁`, `γᵢ₊₁`, `ρᵢ₊₁` are the Lanczos vector, its
normalization and the diagonal Lanczos coefficient. -/
private theorem step_of_y (hH : H.IsHermitian) (hM : M.PosDef) (i : ℕ)
    (hi : toScaled hM (y (i + 1)) =
      if i = 0 then scaledGrad hM g
      else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (i - 1)) :
    toScaled hM (q (i + 1)) =
        Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i ∧
      γ (i + 1) = ‖if i = 0 then scaledGrad hM g
        else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
          (i - 1)‖ ∧
      ρ (i + 1) =
        Lanczos.alpha (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
          (scaledGrad hM g) i := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  have hγ : γ (i + 1) = ‖if i = 0 then b else Arnoldi.w A b (i - 1)‖ := by
    rw [h.gamma_eq_norm hM (by omega), hi]
  have hqi : toScaled hM (q (i + 1)) = Arnoldi.vec A b i := by
    rw [h.q_eq _ (by omega), map_smul, hi, hγ]
    rcases i with _ | i
    · simp [vec_zero']
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
      rw [Arnoldi.vec_succ_eq]
      simp
  refine ⟨hqi, hγ, ?_⟩
  have hc := Lanczos.coe_alpha b hA i
  simp only [RCLike.ofReal_real_eq_id, id] at hc
  rw [hc, h.rho_eq _ (by omega), real_inner_comm, ← inner_scaledOp_toScaled, real_inner_comm, hqi]
  rfl

/-- **Identification of Algorithm 10.1.1 with the Lanczos process** of `M⁻¹H` from `M⁻¹g` in the
`M`-inner product: `M⁻¹`-transported, `yⱼ₊₁` is `M⁻¹g` for `j = 0` and the unnormalized Lanczos
vector `w_{j-1}` (`Arnoldi.w`) otherwise. -/
theorem toScaled_y (hH : H.IsHermitian) (hM : M.PosDef) (j : ℕ) :
    toScaled hM (y (j + 1)) =
      if j = 0 then scaledGrad hM g
      else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (j - 1) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | i
    · rw [ite_eq_left rfl, h.y_eq 1 le_rfl, h.t_one]
      rfl
    · rw [h.y_succ hM (by omega : 1 ≤ i + 1), ite_eq_right (Nat.succ_ne_zero i),
        Nat.add_sub_cancel, map_sub, map_sub, map_smul, map_smul,
        ← scaledOp_toScaled]
      obtain ⟨hqi, -, hρi⟩ := h.step_of_y hH hM i (ih i (by omega))
      rw [hqi, hρi]
      rcases i with _ | i
      · rw [ite_eq_left rfl, map_zero, smul_zero, sub_zero, Arnoldi.w, Finset.sum_range_one]
        have hc := Lanczos.coe_alpha b hA 0
        simp only [RCLike.ofReal_real_eq_id, id] at hc
        rw [hc]
        rfl
      · rw [ite_eq_right (Nat.succ_ne_zero i)]
        obtain ⟨hqi', -, -⟩ := h.step_of_y hH hM i (ih i (by omega))
        obtain ⟨-, hγi, -⟩ := h.step_of_y hH hM (i + 1) (ih (i + 1) (by omega))
        rw [hqi', hγi, ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]
        have hw := Lanczos.w_succ_eq b hA i
        simp only [RCLike.ofReal_real_eq_id, id] at hw
        rw [hw]
        rfl

/-- **Algorithm 10.1.1 computes the Lanczos vectors**: `qₖ = lanczosVec hM H g (k - 1)` for
`k ≥ 1`. -/
theorem q_eq_lanczosVec (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    q k = lanczosVec hM H g (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  apply (toScaled hM).injective
  rw [toScaled_lanczosVec, Nat.add_sub_cancel]
  exact (h.step_of_y hH hM j (h.toScaled_y hH hM j)).1

/-- `γ₁ = ‖g‖_{M⁻¹}` ((10.1.4)). -/
theorem gamma_one (hH : H.IsHermitian) (hM : M.PosDef) : γ 1 = mNorm M⁻¹ g := by
  rw [(h.step_of_y hH hM 0 (h.toScaled_y hH hM 0)).2.1, ite_eq_left rfl,
    mNorm_inv_eq_norm_scaledGrad hM]

/-- `γₖ₊₁` is the off-diagonal Lanczos coefficient `β_{k-1}` for `k ≥ 1`. -/
theorem gamma_succ (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    γ (k + 1) =
      Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (k - 1) := by
  rw [(h.step_of_y hH hM k (h.toScaled_y hH hM k)).2.1, ite_eq_right (by omega)]
  rfl

/-- `ρₖ` is the diagonal Lanczos coefficient `α_{k-1}` for `k ≥ 1`. -/
theorem rho_eq_alpha (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    ρ k = Lanczos.alpha (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
      (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (h.step_of_y hH hM j (h.toScaled_y hH hM j)).2.2

end algorithm_10_1_1

/-- **Properties of Algorithm 10.1.1** ([cartis2022evaluation] (10.1.3)–(10.1.4), (10.1.7),
(10.2.1) and the termination remark). Let `H` be symmetric, `M` positive definite and
`1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)`, and consider any run of Algorithm 10.1.1. Then:
(i) the columns of `Qₖ` are the computed vectors `q₁, …, qₖ`;
(ii) `Qₖᵀ M Qₖ = Iₖ`;
(iii) `Qₖᵀ H Qₖ = Tₖ` is the symmetric tridiagonal matrix with diagonal `ρ₁, …, ρₖ` and
off-diagonal `γ₂, …, γₖ`;
(iv) `Qₖᵀ g = γ₁ e₁` with `γ₁ = ‖g‖_{M⁻¹} > 0`, and `γᵢ > 0` for `2 ≤ i ≤ k` (`Tₖ` is
unreduced);
(v) `H Qₖ - M Qₖ Tₖ = γₖ₊₁ wₖ₊₁ eₖᵀ` (10.2.1);
(vi) the leading `(k-1) × (k-1)` block of `Tₖ` is `Tₖ₋₁` (the correct form of (10.1.7));
(vii) the iteration stops after `k` steps (`γₖ₊₁ = 0`) iff `k = grade(M⁻¹H, M⁻¹g)` (`≤ n`), and
then `𝒦ₖ` is invariant under `M⁻¹H` (`krylovSpace_gradeHM_mem_invtSubmodule`). -/
theorem algorithm_10_1_1_spec {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}
    {t y w q : ℕ → EuclideanSpace ℝ (Fin n)} {γ ρ : ℕ → ℝ} (hH : H.IsHermitian) (hM : M.PosDef)
    (h : algorithm_10_1_1 H M g t y w q γ ρ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) :
    lanczosBasis hM H g k = Matrix.of (fun i (j : Fin k) => q (j + 1) i) ∧
    (lanczosBasis hM H g k)ᵀ * M * lanczosBasis hM H g k = 1 ∧
    ((lanczosBasis hM H g k)ᵀ * H * lanczosBasis hM H g k = lanczosTridiag hM H g k ∧
      lanczosTridiag hM H g k = symTridiag (fun i => ρ (i + 1)) (fun i => γ (i + 1)) k) ∧
    (toEuclideanLin (lanczosBasis hM H g k)ᵀ g = EuclideanSpace.single ⟨0, hk1⟩ (γ 1) ∧
      γ 1 = mNorm M⁻¹ g ∧ 0 < γ 1 ∧ ∀ i, 2 ≤ i → i ≤ k → 0 < γ i) ∧
    H * lanczosBasis hM H g k - M * lanczosBasis hM H g k * lanczosTridiag hM H g k =
      Matrix.of (fun a (j : Fin k) => if (j : ℕ) + 1 = k then γ (k + 1) * w (k + 1) a else 0) ∧
    (lanczosTridiag hM H g k).submatrix (Fin.castLE (Nat.sub_le k 1))
        (Fin.castLE (Nat.sub_le k 1)) = lanczosTridiag hM H g (k - 1) ∧
    (γ (k + 1) = 0 ↔ k = gradeHM H M g) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hG : gradeHM H M g = Krylov.grade A b := gradeHM_eq hM
  have hb : b ≠ 0 := fun hb0 => by
    have : Krylov.grade A b = 0 := by rw [hb0]; exact Krylov.grade_zero A
    omega
  have hT : lanczosTridiag hM H g k = symTridiag (fun i => ρ (i + 1)) (fun i => γ (i + 1)) k := by
    rw [lanczosTridiag, Lanczos.tridiag_eq_symTridiag]
    ext i j
    rw [symTridiag_apply, symTridiag_apply, h.rho_eq_alpha hH hM (by omega : 1 ≤ (i : ℕ) + 1),
      Nat.add_sub_cancel]
    split_ifs with h1 h2 h3 <;> try rfl
    · rw [h.gamma_succ hH hM (by omega)]
    · rw [h.gamma_succ hH hM (by omega)]
  have hγpos : ∀ i, 2 ≤ i → i ≤ k → 0 < γ i := fun i hi2 hik => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [h.gamma_succ hH hM (by omega)]
    refine lt_of_le_of_ne (Lanczos.beta_nonneg _ _ _) (Ne.symm ?_)
    rw [Ne, Lanczos.beta_eq_zero_iff]
    have := gradeHM_eq (H := H) (g := g) hM
    omega
  have hγ1 : γ 1 = mNorm M⁻¹ g := h.gamma_one hH hM
  refine ⟨?_, lanczosBasis_transpose_mul_M hM hk, ⟨lanczosBasis_transpose_mul_H hM hH, hT⟩,
    ⟨?_, hγ1, ?_, hγpos⟩, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.of_apply, lanczosBasis]
    rw [h.q_eq_lanczosVec hH hM (by omega), Nat.add_sub_cancel]
  · rw [hγ1]; exact lanczosGrad_eq hM hk1
  · rw [hγ1, mNorm_inv_eq_norm_scaledGrad hM]; exact norm_pos_iff.2 hb
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [lanczos_relation hM hH m]
    ext a j
    simp only [Matrix.of_apply, Nat.add_right_cancel_iff]
    rw [h.gamma_succ hH hM (by omega), Nat.add_sub_cancel, h.w_eq_M hM (by omega),
      h.q_eq_lanczosVec hH hM (by omega), Nat.add_sub_cancel]
    simp [Fin.ext_iff]
  · rw [lanczosTridiag, lanczosTridiag, Lanczos.tridiag_eq_symTridiag,
      Lanczos.tridiag_eq_symTridiag,
      symTridiag_submatrix_castLE]
  · rw [h.gamma_succ hH hM hk1, Lanczos.beta_eq_zero_iff, ← hG]
    omega

/-! ### The hard case (§10.1.2) -/

section HardCase

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- The generalized eigenvectors of `(H, M)` for `μ` are, `M⁻¹`-transported, the eigenvectors of
the scaled operator. -/
theorem map_toScaled_ker (hM : M.PosDef) (μ : ℝ) :
    (LinearMap.ker (toEuclideanLin (H - μ • M))).map
        (toScaled hM : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ScaledSpace hM) =
      Module.End.eigenspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) μ := by
  ext x
  obtain ⟨v, rfl⟩ := (toScaled hM).surjective x
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, scaledOp_toScaled, ← map_smul]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [LinearEquiv.coe_coe] at huv
    rw [← (toScaled hM).injective huv]
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, sub_eq_zero, map_smul,
      LinearMap.smul_apply] at hu
    rw [hu, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]
  · intro hv
    refine ⟨v, ?_, rfl⟩
    have hv' := congrArg (toEuclideanLin M) ((toScaled hM).injective hv)
    rw [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_smul] at hv'
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, hv',
      sub_self]

/-- **The hard case defeats the Krylov subspaces** ([cartis2022evaluation] §10.1.2). Let `λ₁` be
the leftmost eigenvalue of the pencil `(H, M)` and suppose the hard-case condition: `⟪v, g⟫ = 0`
for every generalized eigenvector `H v = λ₁ M v`. Then
(i) every `𝒦ₖ` is `M`-orthogonal to the eigenspace of `λ₁`, i.e. lies in the span of the
generalized eigenvectors for the other eigenvalues;
(ii) `grade(M⁻¹H, M⁻¹g) ≤ n - i₁`, `i₁` the multiplicity of `λ₁`;
(iii) every subspace solution `sₖ` of (10.1.1) on `𝒦ₖ` is `M`-orthogonal to the eigenspace of
`λ₁`. -/
theorem krylov_hardCase_10_1_2 (hH : H.IsHermitian) (hM : M.PosDef)
    (hhard : ∀ v, toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v → ⟪v, g⟫ = 0) :
    (∀ k, ∀ s ∈ krylovSpace H M g k, ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) ∧
      gradeHM H M g + Module.finrank ℝ
          (LinearMap.ker (toEuclideanLin (H - leftmostPencil hH hM • M))) ≤ n ∧
      (∀ k Δ s, IsTRSubspaceSolution g H M Δ (krylovSpace H M g k) s → ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) ∧
      (∀ k σ r s, IsRegSubspaceSolution g H M σ r (krylovSpace H M g k) s → ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  set μ := leftmostPencil hH hM
  set E₁ := Module.End.eigenspace A μ
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  have hmemE : ∀ v, toEuclideanLin H v = μ • toEuclideanLin M v → toScaled hM v ∈ E₁ := by
    intro v hv
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm]
    refine ⟨v, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, hv,
      sub_self]
  -- `b ⟂ E₁` and `E₁ᗮ` is invariant
  have hb : b ∈ E₁ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, sub_eq_zero, map_smul,
      LinearMap.smul_apply] at hv
    rw [LinearEquiv.coe_coe, inner_toScaled_scaledGrad]
    exact hhard v hv
  have hinv : E₁ᗮ ∈ Module.End.invtSubmodule A := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro e he
    rw [← hA, (Module.End.mem_eigenspace_iff.1 he), inner_smul_left, hx e he, mul_zero]
  have hfull : Krylov.fullSubspace A b ≤ E₁ᗮ :=
    Krylov.fullSubspace_le_of_mem_invtSubmodule A b hinv hb
  have hK : ∀ k, ∀ s ∈ krylovSpace H M g k, ∀ v,
      toEuclideanLin H v = μ • toEuclideanLin M v → ⟪v, toEuclideanLin M s⟫ = 0 := by
    intro k s hs v hv
    have hs' := hfull (Krylov.subspace_le_fullSubspace A b k ((toScaled_mem_krylov_iff hM).2 hs))
    have := (Submodule.mem_orthogonal _ _).1 hs' _ (hmemE v hv)
    rw [inner_toScaled] at this
    rw [← isSymmetric_toEuclideanLin_iff.2 hM.isHermitian v s]
    exact this
  refine ⟨hK, ?_, fun k Δ s hs => hK k s hs.1, fun k σ r s hs => hK k s hs.1⟩
  -- the grade
  have h1 : gradeHM H M g ≤ Module.finrank ℝ E₁ᗮ := by
    rw [gradeHM_eq hM]
    exact Submodule.finrank_mono hfull
  have h2 := Submodule.finrank_add_finrank_orthogonal E₁
  have h3 : Module.finrank ℝ E₁ =
      Module.finrank ℝ (LinearMap.ker (toEuclideanLin (H - μ • M))) := by
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm, LinearEquiv.finrank_map_eq]
  rw [finrank_scaledSpace, Fintype.card_fin] at h2
  omega

end HardCase

end CartisGouldToint.Chapter10
