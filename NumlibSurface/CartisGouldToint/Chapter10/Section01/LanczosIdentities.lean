import NumlibSurface.CartisGouldToint.Chapter10.Section01
import Numlib.Krylov.PreconditionedLanczosCorrectness
import Numlib.Optimization.KrylovSubproblemReduction

/-!
# The actual preconditioned Lanczos basis identities

The legal raw recurrence generates the existing energy-space Lanczos basis. Its Gram,
Hessian, gradient and full operator identities are stated coordinatewise; these are exactly
`Qᵀ M Q = I`, `Qᵀ H Q = T`, `Qᵀ g = γ₁ e₁` and the rank-one Lanczos relation.
The final unnormalized residual avoids assigning a normalized vector at breakdown.
-/

noncomputable section
open scoped InnerProductSpace
open Optimization.KrylovSubproblem
namespace CartisGouldToint.Chapter10.Section01
variable {n N : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}
  {g : EuclideanSpace ℝ (Fin n)}
  {states : ℕ → Krylov.PreconditionedLanczos.State (EuclideanSpace ℝ (Fin n))}
  {trials : ℕ → Krylov.PreconditionedLanczos.Trial (EuclideanSpace ℝ (Fin n))}

/-- The actual columns produced by the raw preconditioned algorithm. -/
def lanczosBasisMatrix (trials : ℕ → Krylov.PreconditionedLanczos.Trial
    (EuclideanSpace ℝ (Fin n))) (N : ℕ) : Matrix (Fin n) (Fin N) ℝ :=
  fun i j => (trials j).primal i

/-- The source recurrence restricted to any active initial segment, including segments
strictly before its eventual stopping index. -/
abbrev algorithm_10_1_1_prefix (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ)
    (states : ℕ → Krylov.PreconditionedLanczos.State (EuclideanSpace ℝ (Fin n)))
    (trials : ℕ → Krylov.PreconditionedLanczos.Trial (EuclideanSpace ℝ (Fin n))) (N : ℕ) :=
  Krylov.PreconditionedLanczos.Prefix (Matrix.toEuclideanLin H)
    (Matrix.toEuclideanLin M⁻¹) g states trials N

/-- Actual preconditioned primal vectors agree with the existing energy-space Lanczos basis. -/
theorem algorithm_10_1_1_primal_eq (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) {i : ℕ} (hi : i < N) :
    hM.isPreconditioner_toEuclideanLin.toEnergy (trials i).primal =
      Arnoldi.vec (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) i :=
  h.primal_eq_vec hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin hi

/-- The dimension budget stops the actual source algorithm exactly at its Krylov grade. -/
theorem algorithm_10_1_1_length_eq_grade (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1 g H M states trials N) :
    N = Krylov.grade (Chapter08.Section02.secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) := by
  apply h.length_eq_grade_of_grade_le_budget hM.isPreconditioner_toEuclideanLin
    hH.isSymmetric_toEuclideanLin
  have hd : Module.finrank ℝ hM.isPreconditioner_toEuclideanLin.EnergySpace = n := by
    rw [← hM.isPreconditioner_toEuclideanLin.toEnergy.finrank_eq]
    simp
  simpa only [hd] using Krylov.grade_le_finrank
    (hM.isPreconditioner_toEuclideanLin.energyEnd
      (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H))
    (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))

/-- The stopping index is also the Krylov grade in the original preconditioned coordinates. -/
theorem algorithm_10_1_1_length_eq_preconditioned_grade (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1 g H M states trials N) :
    N = Krylov.grade (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
      (Matrix.toEuclideanLin M⁻¹ g) := by
  rw [algorithm_10_1_1_length_eq_grade hH hM h, Krylov.grade, Krylov.grade]
  have he := Krylov.map_fullSubspace_of_semiconj
    (N := hM.isPreconditioner_toEuclideanLin.toEnergy.toLinearMap)
    (B := Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
    (C := Chapter08.Section02.secularHessian H hM) (fun _ => rfl)
    (Matrix.toEuclideanLin M⁻¹ g)
  exact (congrArg (fun K : Submodule ℝ hM.isPreconditioner_toEuclideanLin.EnergySpace =>
    Module.finrank ℝ K) he).symm.trans
    (hM.isPreconditioner_toEuclideanLin.toEnergy.finrank_map_eq _)

/-- Coordinate form of the exact Gram identity `Qᵀ M Q = I`. -/
theorem algorithm_10_1_1_gram (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) (i j : Fin N) :
    ⟪Matrix.toEuclideanLin M (trials i).primal, (trials j).primal⟫_ℝ =
      if i = j then 1 else 0 := by
  change ⟪hM.isPreconditioner_toEuclideanLin.toEnergy (trials i).primal,
    hM.isPreconditioner_toEuclideanLin.toEnergy (trials j).primal⟫_ℝ = _
  rw [algorithm_10_1_1_primal_eq hH hM h i.isLt,
    algorithm_10_1_1_primal_eq hH hM h j.isLt]
  have hlen : N ≤ Krylov.grade (Chapter08.Section02.secularHessian H hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) :=
    h.length_le_grade hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade _ _
      (i.isLt.trans_le hlen), one_pow, ite_eq_left rfl]
  · rw [Arnoldi.inner_vec_eq_zero _ _ (by intro he; exact hij (Fin.ext he)), ite_eq_right hij]

/-- Coordinate form of the exact compressed Hessian identity `Qᵀ H Q = T`. -/
theorem algorithm_10_1_1_hessian (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) (i j : Fin N) :
    ⟪(trials i).primal, Matrix.toEuclideanLin H (trials j).primal⟫_ℝ =
      Lanczos.tridiag (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) N i j := by
  rw [← hM.isPreconditioner_toEuclideanLin.inner_energyEnd_right,
    algorithm_10_1_1_primal_eq hH hM h i.isLt,
    algorithm_10_1_1_primal_eq hH hM h j.isLt]
  exact inner_vec_apply_eq_tridiag (Chapter08.Section02.secularHessian_isSymmetric hH hM) i j

/-- Coordinate form of the exact initial-gradient identity `Qᵀ g = γ₁ e₁`. -/
theorem algorithm_10_1_1_gradient (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) (i : Fin N) :
    ⟪(trials i).primal, g⟫_ℝ = if (i : ℕ) = 0 then (trials 0).gamma else 0 := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  rw [← hM.isPreconditioner_toEuclideanLin.inner_toEnergy_inv,
    algorithm_10_1_1_primal_eq hH hM h i.isLt,
    h.gamma_zero hM.isPreconditioner_toEuclideanLin hN]
  cases N with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hm : m + 1 ≤ Krylov.grade (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) :=
      h.length_le_grade hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin
    have he := adjoint_lanczosEmbedding_start hm i
    rw [adjoint_lanczosEmbedding_apply] at he
    simpa only [Fin.ext_iff, Fin.val_zero] using he

/-- A linear combination of the actual primal columns transports to the existing Lanczos
expansion, with no assumed basis identity. -/
theorem algorithm_10_1_1_energy_sum (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) (y : Fin N → ℝ) :
    hM.isPreconditioner_toEuclideanLin.toEnergy (∑ i : Fin N, y i • (trials i).primal) =
      lanczosStep (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) y := by
  rw [map_sum]
  simp only [lanczosStep]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, algorithm_10_1_1_primal_eq hH hM h i.isLt]

/-- The full source relation `H Q - M Q T` evaluated on every coordinate vector. The last
unnormalized residual is `γ_(k+1) w_(k+1)` before breakdown and zero at breakdown. -/
theorem algorithm_10_1_1_operator_relation (hH : H.IsSymm) (hM : M.PosDef) {m : ℕ}
    (h : algorithm_10_1_1_prefix g H M states trials (m + 1)) (y : Fin (m + 1) → ℝ) :
    Matrix.toEuclideanLin H (∑ i : Fin (m + 1), y i • (trials i).primal) -
      Matrix.toEuclideanLin M
        (∑ i : Fin (m + 1), (Lanczos.tridiag (Chapter08.Section02.secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
          (m + 1)).mulVec y i • (trials i).primal) =
      y (Fin.last m) • (states (m + 1)).residual := by
  have hinv : Function.Injective (Matrix.toEuclideanLin M⁻¹) := by
    intro x z he
    have he' := congrArg (Matrix.toEuclideanLin M) he
    simpa only [hM.isPreconditioner_toEuclideanLin.apply_inv] using he'
  apply hinv
  apply hM.isPreconditioner_toEuclideanLin.toEnergy.injective
  simp only [map_sub, map_smul, hM.isPreconditioner_toEuclideanLin.inv_apply]
  change Chapter08.Section02.secularHessian H hM
      (hM.isPreconditioner_toEuclideanLin.toEnergy
        (∑ i : Fin (m + 1), y i • (trials i).primal)) - _ = _
  rw [algorithm_10_1_1_energy_sum hH hM h, algorithm_10_1_1_energy_sum hH hM h]
  have hr : hM.isPreconditioner_toEuclideanLin.toEnergy
      (Matrix.toEuclideanLin M⁻¹ (states (m + 1)).residual) =
      Arnoldi.w (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) m :=
    h.residual_eq_w hM.isPreconditioner_toEuclideanLin hH.isSymmetric_toEuclideanLin
      (by omega)
  rw [hr]
  exact lanczos_apply_sub (Chapter08.Section02.secularHessian_isSymmetric hH hM) m y

/-- The actual basis matrix realizes exactly the primal-column linear combination. -/
theorem lanczosBasisMatrix_apply (y : EuclideanSpace ℝ (Fin N)) :
    Matrix.toEuclideanLin (lanczosBasisMatrix trials N) y =
      ∑ i : Fin N, y i • (trials i).primal := by
  ext j
  simp [lanczosBasisMatrix, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The literal matrix Gram identity for every legal active initial segment. -/
theorem algorithm_10_1_1_gram_matrix (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) :
    (lanczosBasisMatrix trials N).transpose * M * lanczosBasisMatrix trials N = 1 := by
  ext i j
  rw [Matrix.mul_assoc]
  have he := algorithm_10_1_1_gram hH hM h i j
  rw [hM.isSymmetricCoercive_toEuclideanLin.isSymmetric] at he
  simpa [lanczosBasisMatrix, Matrix.mul_apply, PiLp.inner_apply,
    Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, mul_comm] using he

/-- The literal matrix Hessian compression for every legal active initial segment. -/
theorem algorithm_10_1_1_hessian_matrix (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) :
    (lanczosBasisMatrix trials N).transpose * H * lanczosBasisMatrix trials N =
      Lanczos.tridiag (Chapter08.Section02.secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) N := by
  ext i j
  rw [Matrix.mul_assoc]
  have he := algorithm_10_1_1_hessian hH hM h i j
  simpa [lanczosBasisMatrix, Matrix.mul_apply, PiLp.inner_apply,
    Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, mul_comm] using he

/-- The literal matrix initial-gradient compression for every legal active initial segment. -/
theorem algorithm_10_1_1_gradient_matrix (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) :
    Matrix.toEuclideanLin (lanczosBasisMatrix trials N).transpose g =
      WithLp.toLp 2 (fun i : Fin N => if (i : ℕ) = 0 then (trials 0).gamma else 0) := by
  ext i
  have he := algorithm_10_1_1_gradient hH hM h i
  simpa [lanczosBasisMatrix, PiLp.inner_apply,
    Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, mul_comm] using he

/-- The actual tridiagonal reduced data (10.1.3), derived from the raw algorithm rather
than supplied as input assumptions. -/
theorem algorithm_10_1_1_reduced_coefficients (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) :
    (subspaceQuadraticProblems g H M (lanczosBasisMatrix trials N)).gradient =
        WithLp.toLp 2 (fun i : Fin N => if (i : ℕ) = 0 then (trials 0).gamma else 0) ∧
      (subspaceQuadraticProblems g H M (lanczosBasisMatrix trials N)).hessian =
        Lanczos.tridiag (Chapter08.Section02.secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) N ∧
      (subspaceQuadraticProblems g H M (lanczosBasisMatrix trials N)).metric = 1 :=
  ⟨algorithm_10_1_1_gradient_matrix hH hM h, algorithm_10_1_1_hessian_matrix hH hM h,
    algorithm_10_1_1_gram_matrix hH hM h⟩

/-- The normalized version of the full source Lanczos relation at any iteration before
breakdown, with the actual next coefficient and normalized dual vector. -/
theorem algorithm_10_1_1_operator_relation_normalized (hH : H.IsSymm) (hM : M.PosDef)
    {m : ℕ} (h : algorithm_10_1_1_prefix g H M states trials (m + 2))
    (y : Fin (m + 1) → ℝ) :
    Matrix.toEuclideanLin H (∑ i : Fin (m + 1), y i • (trials i).primal) -
      Matrix.toEuclideanLin M
        (∑ i : Fin (m + 1), (Lanczos.tridiag (Chapter08.Section02.secularHessian H hM)
          (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g))
          (m + 1)).mulVec y i • (trials i).primal) =
      ((trials (m + 1)).gamma * y (Fin.last m)) • (trials (m + 1)).dual := by
  have he := algorithm_10_1_1_operator_relation hH hM (h.mono (by omega : m + 1 ≤ m + 2)) y
  rw [h.residual_eq_gamma_smul_dual (by omega : m + 1 < m + 2), smul_smul, mul_comm] at he
  exact he

/-- The actual primal columns span exactly the source preconditioned Krylov subspace. -/
theorem algorithm_10_1_1_basis_range (hH : H.IsSymm) (hM : M.PosDef)
    (h : algorithm_10_1_1_prefix g H M states trials N) :
    (Matrix.toEuclideanLin (lanczosBasisMatrix trials N)).range =
      preconditionedKrylovSpace g H M N := by
  let hp := hM.isPreconditioner_toEuclideanLin
  let A := hp.energyEnd (Matrix.toEuclideanLin M⁻¹ ∘ₗ Matrix.toEuclideanLin H)
  let b := hp.toEnergy (Matrix.toEuclideanLin M⁻¹ g)
  have hlen : N ≤ Krylov.grade A b := h.length_le_grade hp hH.isSymmetric_toEuclideanLin
  have henergy (y : EuclideanSpace ℝ (Fin N)) :
      hp.toEnergy (Matrix.toEuclideanLin (lanczosBasisMatrix trials N) y) =
        lanczosEmbedding A b hlen y := by
    rw [lanczosBasisMatrix_apply, lanczosEmbedding_apply]
    exact algorithm_10_1_1_energy_sum hH hM h y
  have hK (x : EuclideanSpace ℝ (Fin n)) : hp.toEnergy x ∈ Krylov.subspace A b N ↔
      x ∈ preconditionedKrylovSpace g H M N := by
    rw [hp.subspace_energyEnd]
    change hp.toEnergy x ∈ (preconditionedKrylovSpace g H M N).map hp.toEnergy.toLinearMap ↔ _
    constructor
    · rintro ⟨z, hz, he⟩
      exact hp.toEnergy.injective he ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply (hK _).mp
    rw [henergy]
    change lanczosEmbedding A b hlen y ∈ (Krylov.subspace A b N : Set _)
    rw [← range_lanczosEmbedding A b hlen]
    exact ⟨y, rfl⟩
  · intro hx
    have he := (hK x).mpr hx
    change hp.toEnergy x ∈ (Krylov.subspace A b N : Set _) at he
    rw [← range_lanczosEmbedding A b hlen] at he
    obtain ⟨y, hy⟩ := he
    refine ⟨y, hp.toEnergy.injective ?_⟩
    rw [henergy]
    exact hy

end CartisGouldToint.Chapter10.Section01
