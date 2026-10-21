import Numlib.Analysis.InnerProductSpace.RayleighBounds
import Numlib.Optimization.WeightedQuadraticSubproblem

/-!
# Appendix A, Section 5: spectral endpoints and Rayleigh quotients

The variational endpoints are actual eigenvalues for symmetric matrices of positive dimension.
A positive definite metric transports generalized eigenvalues to an ordinary symmetric operator
on its energy inner product space. Rayleigh interval bounds exclude the zero vector, as required
for the source formulas (A.2)–(A.4).
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.QuadraticSubproblem

namespace CartisGouldToint.AppendixA.Section05

variable {n : ℕ}

/-- The leftmost and rightmost eigenvalues of a symmetric matrix, in the order of (A.1).
For positive-dimensional symmetric matrices the variational definitions are eigenvalues. -/
def spectralEndpoints (H : Matrix (Fin n) (Fin n) ℝ) : ℝ × ℝ :=
  ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).rayleighInfimum,
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).rayleighSupremum)

/-- The source notation `λ_min[H]`. -/
def minEigenvalue (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := (spectralEndpoints H).1

/-- The source notation `λ_max[H]`. -/
def maxEigenvalue (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := (spectralEndpoints H).2

/-- The spectral condition number `λ_max[H] / λ_min[H]`, used for positive definite matrices. -/
def spectralConditionNumber (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  maxEigenvalue H / minEigenvalue H

/-- The generalized Rayleigh quotient (A.2). -/
def generalizedRayleighQuotient (H M : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ x (Matrix.toEuclideanLin H x) / inner ℝ x (Matrix.toEuclideanLin M x)

/-- The quotient for the identity metric is the ordinary Rayleigh quotient. -/
@[simp] theorem generalizedRayleighQuotient_one (H : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    generalizedRayleighQuotient H 1 x =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).rayleighQuotient x := by
  simp [generalizedRayleighQuotient, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]
  rfl

/-- The generalized endpoints are those of the actual preconditioned Hessian in the metric
inner product; they require a positive definite metric. -/
def generalizedSpectralEndpoints (H : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) : ℝ × ℝ :=
  let T := energyHessian hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
  (T.rayleighInfimum, T.rayleighSupremum)

/-- The quotient is unchanged by transport to the metric inner product. -/
theorem generalizedRayleighQuotient_eq_energy (H : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    generalizedRayleighQuotient H M x =
      (energyHessian hM.isPreconditioner_toEuclideanLin
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)).rayleighQuotient
        (hM.isPreconditioner_toEuclideanLin.toEnergy x) := by
  let p := hM.isPreconditioner_toEuclideanLin
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, energyHessian_apply, RCLike.re_to_real,
    p.norm_toEnergy_sq, generalizedRayleighQuotient]
  rw [real_inner_comm (p.toEnergy _), p.inner_toEnergy_inv]
  rw [real_inner_comm (Matrix.toEuclideanLin M x) x]
  rfl

/-- The generalized Rayleigh interval bound (A.3), with the necessary nonzero-vector hypothesis. -/
theorem generalizedRayleighQuotient_mem_Icc (H : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    generalizedRayleighQuotient H M x ∈
      Set.Icc (generalizedSpectralEndpoints H hM).1 (generalizedSpectralEndpoints H hM).2 := by
  rw [generalizedRayleighQuotient_eq_energy H hM]
  have hn : hM.isPreconditioner_toEuclideanLin.toEnergy x ≠ 0 := by
    intro h
    exact hx (hM.isPreconditioner_toEuclideanLin.toEnergy.map_eq_zero_iff.mp h)
  exact ⟨ContinuousLinearMap.rayleighInfimum_le _ hn,
    ContinuousLinearMap.le_rayleighSupremum _ hn⟩

/-- The norm bound (A.4). This also holds for a nonsymmetric matrix. -/
theorem rayleighQuotient_norm_bound (H : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |generalizedRayleighQuotient H 1 x| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H‖ := by
  rw [generalizedRayleighQuotient_one]
  exact ContinuousLinearMap.rayleighQuotient_le_norm _ x

variable [NeZero n]

/-- The variational left endpoint really is an eigenvalue of the original symmetric matrix. -/
theorem hasEigenvalue_minEigenvalue {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin H) (minEigenvalue H) :=
by
  have hs : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact hH.isSymmetric_toEuclideanLin
  simpa only [minEigenvalue, spectralEndpoints, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    RCLike.ofReal_real_eq_id, id_eq] using
    ContinuousLinearMap.IsSymmetric.hasEigenvalue_rayleighInfimum hs

/-- The variational right endpoint really is an eigenvalue of the original symmetric matrix. -/
theorem hasEigenvalue_maxEigenvalue {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin H) (maxEigenvalue H) :=
by
  have hs : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).IsSymmetric := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact hH.isSymmetric_toEuclideanLin
  simpa only [maxEigenvalue, spectralEndpoints, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    RCLike.ofReal_real_eq_id, id_eq] using
    ContinuousLinearMap.IsSymmetric.hasEigenvalue_rayleighSupremum hs

/-- Both generalized endpoints in (A.1) are eigenvalues of the matrix pencil `H - mu M`. -/
theorem generalizedSpectralEndpoints_eigenvectors {H M : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hM : M.PosDef) :
    (∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧ Matrix.toEuclideanLin H x =
      (generalizedSpectralEndpoints H hM).1 • Matrix.toEuclideanLin M x) ∧
    (∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧ Matrix.toEuclideanLin H x =
      (generalizedSpectralEndpoints H hM).2 • Matrix.toEuclideanLin M x) := by
  let p := hM.isPreconditioner_toEuclideanLin
  have : Nontrivial p.EnergySpace := p.toEnergy.symm.toEquiv.nontrivial
  let T := energyHessian p (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
  have hs : T.IsSymmetric := by
    apply isSymmetric_energyHessian
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact hH.isSymmetric_toEuclideanLin
  have transfer (mu : ℝ) (he : Module.End.HasEigenvalue T.toLinearMap mu) :
      ∃ x : EuclideanSpace ℝ (Fin n), x ≠ 0 ∧
        Matrix.toEuclideanLin H x = mu • Matrix.toEuclideanLin M x := by
    obtain ⟨y, hy, hy0⟩ := he.exists_hasEigenvector
    let x := p.toEnergy.symm y
    have hx : x ≠ 0 := by
      intro h
      exact hy0 (by simpa [x, h] using (p.toEnergy.apply_symm_apply y).symm)
    refine ⟨x, hx, ?_⟩
    have heq : T (p.toEnergy x) = mu • p.toEnergy x := by
      simpa [x] using Module.End.mem_eigenspace_iff.mp hy
    exact (energy_eigenvector_iff p _ x mu).mp heq
  exact ⟨transfer _ (ContinuousLinearMap.IsSymmetric.hasEigenvalue_rayleighInfimum hs),
    transfer _ (ContinuousLinearMap.IsSymmetric.hasEigenvalue_rayleighSupremum hs)⟩

/-- The spectral condition number of a positive definite matrix is at least one. -/
theorem one_le_spectralConditionNumber {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) :
    1 ≤ spectralConditionNumber H := by
  have he := hasEigenvalue_minEigenvalue (Matrix.isHermitian_iff_isSymm.mp hH.1)
  have hp : 0 < minEigenvalue H :=
    (Matrix.posDef_iff_isSymmetricCoercive H).mp hH |>.re_pos_of_hasEigenvalue he
  change 1 ≤ maxEigenvalue H / minEigenvalue H
  apply (le_div_iff₀ hp).mpr
  simpa [spectralConditionNumber, minEigenvalue, maxEigenvalue, spectralEndpoints] using
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).rayleighInfimum_le_rayleighSupremum

/-- The least-eigenvalue perturbation bound (A.5). Symmetry identifies the variational
endpoints with eigenvalues; the perturbation estimate itself holds for arbitrary operators. -/
theorem min_eigenvalue_lipschitz {H₁ H₂ : Matrix (Fin n) (Fin n) ℝ}
    (_h₁ : H₁.IsSymm) (_h₂ : H₂.IsSymm) :
    |minEigenvalue H₁ - minEigenvalue H₂| ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (H₁ - H₂)‖ := by
  simpa only [minEigenvalue, spectralEndpoints, map_sub] using
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H₁).abs_rayleighInfimum_sub_le
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H₂)

end CartisGouldToint.AppendixA.Section05
