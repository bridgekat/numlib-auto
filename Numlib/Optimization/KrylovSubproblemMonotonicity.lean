import Numlib.Optimization.KrylovSubproblemBounds
import Numlib.Optimization.InvariantCompression
import Numlib.Optimization.QuadraticSubproblemMultiplier
import Numlib.LinearAlgebra.Matrix.StieltjesSolutionComparison

/-!
# Comparison of nested Lanczos systems

Conjugating the Lanczos tridiagonal by the alternating-sign diagonal makes it a
Stieltjes matrix at every positive definite shift. Its stationary solutions then
solve systems with nonnegative first-coordinate forcing, so the discrete comparison
principle applies to the actual nested compressions.
-/

noncomputable section
open scoped Matrix InnerProductSpace
namespace Optimization.KrylovSubproblem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual Lanczos matrix conjugated by the alternating-sign diagonal. -/
def signedLanczosMatrix (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (-1 : ℝ) ^ (i : ℕ) * Lanczos.tridiag A g m i j * (-1 : ℝ) ^ (j : ℕ)

/-- Negated alternating-sign coordinates turn the stationary right-hand side nonnegative. -/
def signedLanczosVector {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => -((-1 : ℝ) ^ (i : ℕ) * y i))

private theorem sign_sq (i : ℕ) : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by
  rw [← mul_pow]
  norm_num

/-- Alternating coordinate signs preserve the Euclidean norm. -/
theorem norm_signedLanczosVector {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ‖signedLanczosVector y‖ = ‖y‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change (-((-1 : ℝ) ^ (i : ℕ) * y i)) ^ 2 = y i ^ 2
  rw [neg_sq, mul_pow]
  have hi : ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 := by
    simpa only [pow_two] using sign_sq (i : ℕ)
  rw [hi, one_mul]

/-- Nested signed Lanczos matrices are exactly principal submatrices. -/
theorem signedLanczosMatrix_submatrix (A : E →ₗ[ℝ] E) (g : E) {m n : ℕ}
    (hmn : m ≤ n) :
    (signedLanczosMatrix A g n).submatrix (Fin.castLE hmn) (Fin.castLE hmn) =
      signedLanczosMatrix A g m := by
  ext i j
  rfl

/-- A positive definite shifted Lanczos matrix becomes Stieltjes after alternating signs. -/
theorem signedLanczosMatrix_isStieltjes (A : E →ₗ[ℝ] E) (g : E) {m : ℕ}
    (lambda : ℝ) (hpos : (Lanczos.tridiag A g m + lambda • 1).PosDef) :
    (signedLanczosMatrix A g m + lambda • 1).IsStieltjes := by
  classical
  let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (fun i => (-1 : ℝ) ^ (i : ℕ))
  have hDD : D * D = 1 := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    simp only [sign_sq]
    exact Matrix.diagonal_one
  have hinj : Function.Injective (D *ᵥ ·) := by
    intro x y hxy
    have h := congrArg (D *ᵥ ·) hxy
    simpa only [Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec] using h
  have hstar : Dᴴ = D := by simp [D]
  have heq : Dᴴ * (Lanczos.tridiag A g m + lambda • 1) * D =
      signedLanczosMatrix A g m + lambda • 1 := by
    rw [hstar, Matrix.mul_add, Matrix.add_mul]
    have hT : D * Lanczos.tridiag A g m * D = signedLanczosMatrix A g m := by
      ext i j
      simp [D, signedLanczosMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [hT]
    congr 1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hDD]
  refine ⟨heq ▸ hpos.conjTranspose_mul_mul_same hinj, ?_⟩
  intro i j hij
  have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
    smul_eq_mul, mul_zero, add_zero, signedLanczosMatrix, Lanczos.tridiag_apply,
    ite_eq_right hv]
  by_cases hnext : (i : ℕ) + 1 = j
  · rw [ite_eq_left hnext, ← hnext, pow_succ]
    have hs := sign_sq (i : ℕ)
    nlinarith [Lanczos.beta_nonneg A g (i : ℕ)]
  · rw [ite_eq_right hnext]
    by_cases hprev : (j : ℕ) + 1 = i
    · rw [ite_eq_left hprev, ← hprev, pow_succ]
      have hs := sign_sq (j : ℕ)
      nlinarith [Lanczos.beta_nonneg A g (j : ℕ)]
    · simp [hprev]

/-- The signed actual stationary system has the nonnegative initial-gradient forcing. -/
theorem signedLanczosVector_stationary (A : E →ₗ[ℝ] E) (g : E) {m : ℕ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (lambda : ℝ)
    (hy : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec y i +
      lambda * y i = -(if i = 0 then ‖g‖ else 0)) :
    (signedLanczosMatrix A g (m + 1) + lambda • 1) *ᵥ signedLanczosVector y =
      fun i => if i = 0 then ‖g‖ else 0 := by
  ext i
  have hmul : (signedLanczosMatrix A g (m + 1) *ᵥ signedLanczosVector y) i =
      -((-1 : ℝ) ^ (i : ℕ) * (Lanczos.tridiag A g (m + 1) *ᵥ y) i) := by
    simp only [Matrix.mulVec, dotProduct, signedLanczosMatrix, signedLanczosVector,
      WithLp.ofLp_toLp]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = -((-1 : ℝ) ^ (i : ℕ) * Lanczos.tridiag A g (m + 1) i j * y j) *
          ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) := by ring
      _ = _ := by rw [sign_sq]; ring
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, hmul]
  change -((-1 : ℝ) ^ (i : ℕ) * (Lanczos.tridiag A g (m + 1) *ᵥ y) i) +
    lambda * -((-1 : ℝ) ^ (i : ℕ) * y i) = _
  have h := hy i
  by_cases hi : i = 0
  · subst i
    simp only [Fin.val_zero, pow_zero, one_mul, ite_true] at h ⊢
    linarith
  · rw [ite_eq_right hi] at h ⊢
    linear_combination -((-1 : ℝ) ^ (i : ℕ)) * h

/-- At ordered positive definite shifts, actual nested Lanczos stationary solutions
have ordered norms. The larger system is evaluated at the smaller shift. -/
theorem lanczos_stationary_norm_le_of_shift_le (A : E →ₗ[ℝ] E) (g : E)
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) {tau sigma : ℝ} (hshift : tau ≤ sigma)
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec x i +
      sigma * x i = -(if i = 0 then ‖g‖ else 0))
    (hy : ∀ i : Fin (n + 1), (Lanczos.tridiag A g (n + 1)).mulVec y i +
      tau * y i = -(if i = 0 then ‖g‖ else 0))
    (hsmall : (Lanczos.tridiag A g (m + 1) + sigma • 1).PosDef)
    (hlarge : (Lanczos.tridiag A g (n + 1) + tau • 1).PosDef) : ‖x‖ ≤ ‖y‖ := by
  have hs := signedLanczosMatrix_isStieltjes A g sigma hsmall
  have hl := signedLanczosMatrix_isStieltjes A g tau hlarge
  have hxs := signedLanczosVector_stationary A g x sigma hx
  have hys := signedLanczosVector_stationary A g y tau hy
  have hrhs : (fun i : Fin (m + 1) => if i = 0 then ‖g‖ else 0) =
      (fun i : Fin (n + 1) => if i = 0 then ‖g‖ else 0) ∘ Fin.castLE hmn := by
    ext i
    simp only [Function.comp_apply]
    have hi : Fin.castLE hmn i = 0 ↔ i = 0 := by
      constructor <;> intro h
      · exact Fin.ext (congrArg (fun z : Fin (n + 1) => (z : ℕ)) h)
      · subst i; rfl
    simp only [hi]
  have hcomp := hl.norm_principal_shift_solution_le (Fin.castLE_injective hmn)
    (by simpa only [signedLanczosMatrix_submatrix] using hs) hshift
    (show 0 ≤ (fun i : Fin (n + 1) => if i = 0 then ‖g‖ else 0) by
      intro i; change 0 ≤ (if i = 0 then ‖g‖ else 0); positivity)
    (by simpa only [signedLanczosMatrix_submatrix, ← hrhs] using hxs) hys
  change ‖signedLanczosVector x‖ ≤ ‖signedLanczosVector y‖ at hcomp
  simpa only [norm_signedLanczosVector] using hcomp

/-- Strictly decreasing the shift while enlarging the actual Lanczos system strictly
increases the solution norm when the smaller solution is nonzero. -/
theorem lanczos_stationary_norm_lt_of_shift_lt (A : E →ₗ[ℝ] E) (g : E)
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) {tau sigma : ℝ} (hshift : tau < sigma)
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hxne : x ≠ 0)
    (hx : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec x i +
      sigma * x i = -(if i = 0 then ‖g‖ else 0))
    (hy : ∀ i : Fin (n + 1), (Lanczos.tridiag A g (n + 1)).mulVec y i +
      tau * y i = -(if i = 0 then ‖g‖ else 0))
    (hsmall : (Lanczos.tridiag A g (m + 1) + sigma • 1).PosDef)
    (hlarge : (Lanczos.tridiag A g (n + 1) + tau • 1).PosDef) : ‖x‖ < ‖y‖ := by
  have hs := signedLanczosMatrix_isStieltjes A g sigma hsmall
  have hl := signedLanczosMatrix_isStieltjes A g tau hlarge
  have hxs := signedLanczosVector_stationary A g x sigma hx
  have hys := signedLanczosVector_stationary A g y tau hy
  have hrhs : (fun i : Fin (m + 1) => if i = 0 then ‖g‖ else 0) =
      (fun i : Fin (n + 1) => if i = 0 then ‖g‖ else 0) ∘ Fin.castLE hmn := by
    ext i
    simp only [Function.comp_apply]
    have hi : Fin.castLE hmn i = 0 ↔ i = 0 := by
      constructor <;> intro h
      · exact Fin.ext (congrArg (fun z : Fin (n + 1) => (z : ℕ)) h)
      · subst i; rfl
    simp only [hi]
  have hsne : (signedLanczosVector x).ofLp ≠ 0 := by
    intro h
    have hz : signedLanczosVector x = 0 := by
      apply PiLp.ext
      exact fun i => congrFun h i
    apply hxne
    apply norm_eq_zero.mp
    rw [← norm_signedLanczosVector, hz, norm_zero]
  have hcomp := hl.norm_principal_shift_solution_lt (Fin.castLE_injective hmn)
    (by simpa only [signedLanczosMatrix_submatrix] using hs) hshift
    (show 0 ≤ (fun i : Fin (n + 1) => if i = 0 then ‖g‖ else 0) by
      intro i; change 0 ≤ (if i = 0 then ‖g‖ else 0); positivity) hsne
    (by simpa only [signedLanczosMatrix_submatrix, ← hrhs] using hxs) hys
  change ‖signedLanczosVector x‖ < ‖signedLanczosVector y‖ at hcomp
  simpa only [norm_signedLanczosVector] using hcomp

/-- Common-radius complementarity orders both norms and multipliers of actual nested
Lanczos stationary systems. The reference radius may include components orthogonal to
the full Krylov space, which is needed for a full-space hard case. -/
theorem lanczos_trustRegion_stationary_norm_mono (A : E →ₗ[ℝ] E) (g : E)
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) {tau sigma delta R : ℝ}
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hxne : x ≠ 0) (hsigma : 0 ≤ sigma) (htau : 0 ≤ tau)
    (hxR : ‖x‖ ≤ delta) (hyR : ‖y‖ ≤ R) (hR : R ≤ delta) (hR0 : 0 ≤ R)
    (hxcomp : sigma * (‖x‖ ^ 2 - delta ^ 2) = 0)
    (hycomp : tau * (R ^ 2 - delta ^ 2) = 0)
    (hx : ∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec x i +
      sigma * x i = -(if i = 0 then ‖g‖ else 0))
    (hy : ∀ i : Fin (n + 1), (Lanczos.tridiag A g (n + 1)).mulVec y i +
      tau * y i = -(if i = 0 then ‖g‖ else 0))
    (hsmall : (Lanczos.tridiag A g (m + 1) + sigma • 1).PosDef)
    (hlarge : (Lanczos.tridiag A g (n + 1) + tau • 1).PosDef) :
    ‖x‖ ≤ R ∧ sigma ≤ tau := by
  have hdelta0 : 0 ≤ delta := hR0.trans hR
  have hnorm : ‖x‖ ≤ R := by
    by_contra h
    have hlt : R < ‖x‖ := lt_of_not_ge h
    have ht0 : tau = 0 := by
      apply (mul_eq_zero.mp hycomp).resolve_right
      nlinarith [norm_nonneg x]
    have hcomp := lanczos_stationary_norm_le_of_shift_le A g hmn
      (show tau ≤ sigma by simpa only [ht0] using hsigma) hx hy hsmall hlarge
    exact (not_le_of_gt hlt) (hcomp.trans hyR)
  refine ⟨hnorm, ?_⟩
  by_contra h
  have hlt : tau < sigma := lt_of_not_ge h
  have hspos : 0 < sigma := lt_of_le_of_lt htau hlt
  have hxdelta : ‖x‖ = delta := by
    have heq := (mul_eq_zero.mp hxcomp).resolve_left hspos.ne'
    nlinarith [norm_nonneg x]
  have hcomp := lanczos_stationary_norm_lt_of_shift_lt A g hmn hlt hxne hx hy hsmall hlarge
  linarith

variable {A : E →ₗ[ℝ] E} {g : E}
  [FiniteDimensional ℝ (Krylov.fullSubspace A g)]

/-- Actual nested Lanczos radial global minimizers have nondecreasing norms and multipliers.
The proof uses Stieltjes comparison at the optimizers' actual shifts, rather than
inferring norm growth from decreasing optimal objective values. -/
theorem lanczos_regularized_norm_mono_nested (hg : g ≠ 0)
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) (hn : n + 1 ≤ Krylov.grade A g)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap sigma r)
      Set.univ x)
    (hy : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (n + 1))).toContinuousLinearMap sigma r)
      Set.univ y) :
    ‖x‖ ≤ ‖y‖ ∧ sigma * ‖x‖ ^ (r - 2) ≤ sigma * ‖y‖ ^ (r - 2) := by
  obtain ⟨hxs, hxp⟩ := lanczos_regularized_shift_posDef hg (hmn.trans hn) hsigma hr hx
  obtain ⟨hys, hyp⟩ := lanczos_regularized_shift_posDef hg hn hsigma hr hy
  have hnorm : ‖x‖ ≤ ‖y‖ := by
    by_contra h
    have hlt : ‖y‖ < ‖x‖ := lt_of_not_ge h
    have hshift : sigma * ‖y‖ ^ (r - 2) ≤ sigma * ‖x‖ ^ (r - 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hlt.le (by linarith)) hsigma
    exact (not_le_of_gt hlt)
      (lanczos_stationary_norm_le_of_shift_le A g hmn hshift hxs hys hxp hyp)
  exact ⟨hnorm, mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)) hsigma⟩

/-- Associated trust-region conditions imply a nonzero coordinate solution and a positive
definite shifted Lanczos matrix, even when the associated multiplier vanishes. -/
theorem lanczos_trustRegion_shift_spec (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade A g) {delta lambda : ℝ}
    {x : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap
      delta lambda x) :
    (∀ i : Fin (m + 1), (Lanczos.tridiag A g (m + 1)).mulVec x i +
      lambda * x i = -(if i = 0 then ‖g‖ else 0)) ∧
    (Lanczos.tridiag A g (m + 1) + lambda • 1).PosDef ∧ x ≠ 0 := by
  have hs : ‖g‖ • EuclideanSpace.single 0 1 +
      Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1)) x + lambda • x = 0 := by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using hx.stationary
  obtain ⟨hstat, hpos⟩ := lanczos_shift_posDef_of_stationary hg hm lambda hs hx.positive
  refine ⟨hstat, hpos, ?_⟩
  intro hzero
  have h := hstat 0
  have hnorm : ‖g‖ = 0 := by simpa [hzero] using h.symm
  exact hg (norm_eq_zero.mp hnorm)

/-- Nested actual trust-region Lanczos minimizers have nondecreasing norms and associated
multipliers, including inactive constraints and zero multipliers. -/
theorem lanczos_trustRegion_norm_mono_nested (hg : g ≠ 0)
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) (hn : n + 1 ≤ Krylov.grade A g)
    {delta lambda mu : ℝ}
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (m + 1))).toContinuousLinearMap delta lambda x)
    (hy : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag A g (n + 1))).toContinuousLinearMap delta mu y) :
    ‖x‖ ≤ ‖y‖ ∧ lambda ≤ mu := by
  obtain ⟨hxs, hxp, hxne⟩ := lanczos_trustRegion_shift_spec hg (hmn.trans hn) hx
  obtain ⟨hys, hyp, _⟩ := lanczos_trustRegion_shift_spec hg hn hy
  exact lanczos_trustRegion_stationary_norm_mono A g hmn hxne hx.nonneg hy.nonneg
    hx.feasible le_rfl hy.feasible (norm_nonneg _) hx.complementary hy.complementary
    hxs hys hxp hyp

section FullSpace
variable [CompleteSpace E]

/-- Only at the full Krylov grade does projecting a full stationary point give an exact
reduced system. A singular full-space shift is allowed: cyclicity makes its compression
positive definite, and discarded hard-case components can only increase the full norm. -/
theorem lanczos_grade_projected_stationary {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]
    {d : ℕ} (hd : d + 1 = Krylov.grade H.toLinearMap g) {z : E} {lambda : ℝ}
    (hstat : g + H z + lambda • z = 0)
    (hpos : (H + lambda • ContinuousLinearMap.id ℝ E).IsPositive) :
    let y := (lanczosEmbedding H.toLinearMap g hd.le).toContinuousLinearMap.adjoint z
    (∀ i : Fin (d + 1), (Lanczos.tridiag H.toLinearMap g (d + 1)).mulVec y i +
      lambda * y i = -(if i = 0 then ‖g‖ else 0)) ∧
    (Lanczos.tridiag H.toLinearMap g (d + 1) + lambda • 1).PosDef ∧ ‖y‖ ≤ ‖z‖ := by
  let Q := lanczosEmbedding H.toLinearMap g hd.le
  let y := Q.toContinuousLinearMap.adjoint z
  have hrange : Set.range Q = Krylov.fullSubspace H.toLinearMap g := by
    change Set.range (lanczosEmbedding H.toLinearMap g hd.le) = _
    rw [range_lanczosEmbedding]
    rw [hd, Krylov.subspace_grade_eq_fullSubspace]
  have hinv : ∀ v, H (Q v) ∈ Set.range Q := by
    intro v
    rw [hrange]
    apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem H.toLinearMap).mp
      (Krylov.fullSubspace_mem_invtSubmodule H.toLinearMap g)
    have hv : Q v ∈ (Krylov.fullSubspace H.toLinearMap g : Set E) :=
      hrange ▸ (show Q v ∈ Set.range Q from ⟨v, rfl⟩)
    exact hv
  have hcompress : compressedHessian Q H =
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (d + 1))).toContinuousLinearMap := by
    ext v i
    exact compressedHessian_lanczosEmbedding_apply hH rfl hd.le v i
  have hstart : Q.toContinuousLinearMap.adjoint g = ‖g‖ • EuclideanSpace.single 0 1 := by
    ext i
    rw [adjoint_lanczosEmbedding_start]
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hs : ‖g‖ • EuclideanSpace.single 0 1 +
      Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (d + 1)) y + lambda • y = 0 := by
    have h := congrArg Q.toContinuousLinearMap.adjoint hstat
    rw [map_add, map_add, map_smul, map_zero, hstart,
      ← compressedHessian_adjoint_of_invariant Q hH hinv z, hcompress] at h
    exact h
  have hp := compressedHessian_shift_isPositive Q hpos
  rw [hcompress] at hp
  obtain ⟨hys, hyp⟩ := lanczos_shift_posDef_of_stationary hg hd.le lambda hs hp
  refine ⟨hys, hyp, ?_⟩
  have hi : ⟪Q y, z⟫_ℝ = ‖y‖ ^ 2 := by
    calc
      _ = ⟪y, Q.toContinuousLinearMap.adjoint z⟫_ℝ :=
        (ContinuousLinearMap.adjoint_inner_right Q.toContinuousLinearMap y z).symm
      _ = _ := real_inner_self_eq_norm_sq y
  have hc := real_inner_le_norm (Q y) z
  rw [Q.norm_map, hi] at hc
  nlinarith [norm_nonneg y, norm_nonneg z]

/-- Every reduced radial minimizer is bounded in norm and multiplier by every full-space
minimizer. The proof projects only at the full grade, retaining the full-space hard case. -/
theorem lanczos_regularized_norm_le_full {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade H.toLinearMap g)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {x : EuclideanSpace ℝ (Fin (m + 1))} {z : E}
    (hx : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1))).toContinuousLinearMap
      sigma r) Set.univ x)
    (hz : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic g H sigma r)
      Set.univ z) :
    ‖x‖ ≤ ‖z‖ ∧ sigma * ‖x‖ ^ (r - 2) ≤ sigma * ‖z‖ ^ (r - 2) := by
  obtain ⟨hxs, hxp⟩ := lanczos_regularized_shift_posDef hg hm hsigma hr hx
  obtain ⟨hzs, hzp⟩ :=
    (Optimization.QuadraticSubproblem.isMin_powerRegularized_iff_shift hH hsigma hr).mp hz
  have hgpos := Krylov.grade_pos_of_ne_zero H.toLinearMap g hg
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = Krylov.grade H.toLinearMap g :=
    ⟨Krylov.grade H.toLinearMap g - 1, by omega⟩
  have hgrade := lanczos_grade_projected_stationary hH hg hd hzs hzp
  dsimp only at hgrade
  have hnorm : ‖x‖ ≤ ‖z‖ := by
    by_contra h
    have hlt : ‖z‖ < ‖x‖ := lt_of_not_ge h
    have hshift : sigma * ‖z‖ ^ (r - 2) ≤ sigma * ‖x‖ ^ (r - 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hlt.le (by linarith)) hsigma
    have hcomp := lanczos_stationary_norm_le_of_shift_le H.toLinearMap g
      (show m + 1 ≤ d + 1 by omega) hshift hxs hgrade.1 hxp hgrade.2.1
    exact (not_le_of_gt hlt) (hcomp.trans hgrade.2.2)
  exact ⟨hnorm, mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)) hsigma⟩

/-- Full-space associated trust-region multipliers bound every reduced associated multiplier
and norm. Full-space singular shifts and nonunique minimizers are included. -/
theorem lanczos_trustRegion_norm_le_full {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]
    {m : ℕ} (hm : m + 1 ≤ Krylov.grade H.toLinearMap g) {delta lambda mu : ℝ}
    {x : EuclideanSpace ℝ (Fin (m + 1))} {z : E}
    (hx : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1))).toContinuousLinearMap
      delta lambda x)
    (hz : Optimization.QuadraticSubproblem.TrustRegionShiftConditions g H delta mu z) :
    ‖x‖ ≤ ‖z‖ ∧ lambda ≤ mu := by
  obtain ⟨hxs, hxp, hxne⟩ := lanczos_trustRegion_shift_spec hg hm hx
  have hgpos := Krylov.grade_pos_of_ne_zero H.toLinearMap g hg
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = Krylov.grade H.toLinearMap g :=
    ⟨Krylov.grade H.toLinearMap g - 1, by omega⟩
  have hgrade := lanczos_grade_projected_stationary hH hg hd hz.stationary hz.positive
  dsimp only at hgrade
  exact lanczos_trustRegion_stationary_norm_mono H.toLinearMap g
    (show m + 1 ≤ d + 1 by omega) hxne hx.nonneg hz.nonneg hx.feasible
    hgrade.2.2 hz.feasible (norm_nonneg _) hx.complementary hz.complementary
    hxs hgrade.1 hxp hgrade.2.1

/-- Full nested and full-space trust-region Lanczos norm and associated multiplier comparisons.
Neither full-space uniqueness nor positive definiteness of the full shifted Hessian is needed. -/
theorem lanczos_trustRegion_norm_mono {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) (hn : n + 1 ≤ Krylov.grade H.toLinearMap g)
    {delta lambda mu nu : ℝ}
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))} {z : E}
    (hx : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1))).toContinuousLinearMap
      delta lambda x)
    (hy : Optimization.QuadraticSubproblem.TrustRegionShiftConditions
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (n + 1))).toContinuousLinearMap
      delta mu y)
    (hz : Optimization.QuadraticSubproblem.TrustRegionShiftConditions g H delta nu z) :
    lambda ≤ mu ∧ mu ≤ nu ∧ ‖x‖ ≤ ‖y‖ ∧ ‖y‖ ≤ ‖z‖ := by
  have hxy := lanczos_trustRegion_norm_mono_nested hg hmn hn hx hy
  have hyz := lanczos_trustRegion_norm_le_full hH hg hn hy hz
  exact ⟨hxy.2, hyz.2, hxy.1, hyz.1⟩

/-- Full norm and multiplier monotonicity for nested actual Lanczos radial minimizers.
All exponents greater than two are allowed. Every full-space global minimizer is a valid
reference, including singular full-space hard cases. The trust-region counterpart is
`lanczos_trustRegion_norm_mono`. -/
theorem lanczos_regularized_norm_mono {H : E →L[ℝ] E} (hH : H.IsSymmetric)
    (hg : g ≠ 0) [FiniteDimensional ℝ (Krylov.fullSubspace H.toLinearMap g)]
    {m n : ℕ} (hmn : m + 1 ≤ n + 1) (hn : n + 1 ≤ Krylov.grade H.toLinearMap g)
    {sigma r : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    {x : EuclideanSpace ℝ (Fin (m + 1))} {y : EuclideanSpace ℝ (Fin (n + 1))} {z : E}
    (hx : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (m + 1))).toContinuousLinearMap
      sigma r) Set.univ x)
    (hy : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic
      (‖g‖ • EuclideanSpace.single 0 1)
      (Matrix.toEuclideanLin (Lanczos.tridiag H.toLinearMap g (n + 1))).toContinuousLinearMap
      sigma r) Set.univ y)
    (hz : IsMinOn (Optimization.QuadraticSubproblem.powerRegularizedQuadratic g H sigma r)
      Set.univ z) :
    sigma * ‖x‖ ^ (r - 2) ≤ sigma * ‖y‖ ^ (r - 2) ∧
      sigma * ‖y‖ ^ (r - 2) ≤ sigma * ‖z‖ ^ (r - 2) ∧ ‖x‖ ≤ ‖y‖ ∧ ‖y‖ ≤ ‖z‖ := by
  have hxy := lanczos_regularized_norm_mono_nested hg hmn hn hsigma hr hx hy
  have hyz := lanczos_regularized_norm_le_full hH hg hn hsigma hr hy hz
  exact ⟨hxy.2, hyz.2, hxy.1, hyz.1⟩

end FullSpace

end Optimization.KrylovSubproblem
