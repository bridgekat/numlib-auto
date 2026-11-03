import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.CompleteOrthogonal
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.Analysis.InnerProductSpace.Energy

/-! # Least-squares problems and projections

Least-squares and projection systems in Section 4.4 of [conn2000trust].
In (4.4.10) the range-space component lies in the range of `Aᵀ`, which is
the orthogonal complement of the null space of `A`.
After (4.4.14), semidefinite reduced curvature proves global optimality of
a stationary feasible point. Positive definite reduced curvature gives uniqueness.
-/

open Matrix
open scoped Matrix RealInnerProductSpace

namespace ConnGouldToint.Chapter04

variable {m n : ℕ}

/-- **(4.4.1)** A least-squares multiplier minimizes the residual of the transposed system. -/
abbrev IsLeastSquaresMultiplier (A : Matrix (Fin m) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) : Prop := Matrix.IsLeastSquaresSolution Aᵀ g y

/-- **(4.4.2)** The squared residual equals the quadratic objective. -/
theorem least_squares_square_4_4_2 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    ‖Aᵀ.toEuclideanLin y - g‖ ^ 2 =
      inner ℝ y ((A * Aᵀ).toEuclideanLin y) - 2 * inner ℝ y (A.toEuclideanLin g) + inner ℝ g g := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq (Aᵀ.toEuclideanLin y),
    ← real_inner_self_eq_norm_sq g, Matrix.toEuclideanLin_mul_apply,
    Matrix.toEuclideanLin_transpose_inner_left A (Aᵀ.toEuclideanLin y) y,
    Matrix.toEuclideanLin_transpose_inner_left A g y]

/-- **(4.4.3)** The normal equations characterize the least-squares multipliers. -/
theorem normal_equations_4_4_3 {A : Matrix (Fin m) (Fin n) ℝ}
    {g : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)} :
    IsLeastSquaresMultiplier A g y ↔ (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g := by
  simpa only [conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isLeastSquaresSolution_iff_normalEquations (A := Aᵀ) (b := g) (x := y))

/-- **(4.4.5)** The coefficient matrix of the augmented least-squares system. -/
abbrev leastSquaresMatrix (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ := Matrix.fromBlocks 1 Aᵀ A 0

/-- The augmented matrix (4.4.5) is nonsingular exactly when the rows of `A`
are linearly independent. -/
theorem isUnit_leastSquaresMatrix (A : Matrix (Fin m) (Fin n) ℝ) :
    IsUnit (leastSquaresMatrix A) ↔ LinearIndependent ℝ A := by
  simpa only [leastSquaresMatrix, conjTranspose_eq_transpose_of_trivial, transpose_transpose] using
    (Matrix.isUnit_augmented_iff Aᵀ)

/-- **(4.4.4)** The least-squares multipliers are exactly the second components of the
solutions of the augmented system, with the residual as the first component. -/
theorem augmented_least_squares_4_4_4 (A : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    IsLeastSquaresMultiplier A g y ↔
      ∃ r : Fin n → ℝ,
        leastSquaresMatrix A *ᵥ Sum.elim r (WithLp.ofLp y) =
          Sum.elim (WithLp.ofLp g) 0 := by
  rw [normal_equations_4_4_3]
  have hnormal :
      (A * Aᵀ).toEuclideanLin y = A.toEuclideanLin g ↔
        A *ᵥ (Aᵀ *ᵥ WithLp.ofLp y) = A *ᵥ WithLp.ofLp g := by
    rw [Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_apply, Matrix.toEuclideanLin_apply,
      Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, (WithLp.toLp_injective 2).eq_iff]
  rw [hnormal]
  have hblock (r : Fin n → ℝ) :
      leastSquaresMatrix A *ᵥ Sum.elim r (WithLp.ofLp y) = Sum.elim (WithLp.ofLp g) 0 ↔
        r + Aᵀ *ᵥ WithLp.ofLp y = WithLp.ofLp g ∧ A *ᵥ r = 0 := by
    rw [leastSquaresMatrix, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      Sum.elim_eq_iff]
    simp
  constructor
  · intro h
    refine ⟨WithLp.ofLp g - Aᵀ *ᵥ WithLp.ofLp y, (hblock _).2 ⟨by abel, ?_⟩⟩
    rw [Matrix.mulVec_sub, h, sub_self]
  · rintro ⟨r, hr⟩
    obtain ⟨he, hz⟩ := (hblock r).1 hr
    rw [← he, Matrix.mulVec_add, hz, zero_add]

/-- **(4.4.6)** A complete orthogonal decomposition with leading block of order
`rank A`. An SVD gives a diagonal leading block, in particular a lower triangular one. -/
theorem complete_orthogonal_4_4_6 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U V, ∃ h : Matrix.IsCompleteOrthogonal A U V A.rank,
      ((Uᵀ * A * V).submatrix (Fin.castLE h.le_rows) (Fin.castLE h.le_cols)).IsLowerTriangular := by
  obtain ⟨U, σ, V, h⟩ := A.exists_isSVD
  refine ⟨U, V, Matrix.isCompleteOrthogonal_of_svd h, ?_⟩
  have he : Uᵀ * A * V = Matrix.rectDiagonal σ := by
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.star_mul_mul
  rw [he]
  intro i j hij
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => (ne_of_lt hij) (Fin.ext h.symm)
  simp [Matrix.rectDiagonal_apply, hne]

/-- **(4.4.7)** A weighted projection minimizes half the squared energy distance
over the affine constraint set. -/
def IsWeightedProjection (H : Matrix (Fin n) (Fin n) ℝ) (_ : H.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x₀ x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ {z | A.toEuclideanLin z = b} ∧
    IsMinOn (fun z => (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2)
      {z | A.toEuclideanLin z = b} x

/-- **(4.4.8)–(4.4.9)** The augmented system is equivalent to the stationarity and
feasibility equations, with the multiplier negated in the augmented unknown. -/
theorem projection_system_4_4_8 (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (x g : Fin n → ℝ) (y b : Fin m → ℝ) :
    Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim x (-y) = Sum.elim g b ↔
      H *ᵥ x = g + Aᵀ *ᵥ y ∧ A *ᵥ x = b := by
  rw [Matrix.saddleMatrix_mulVec_elim]
  simp [conjTranspose_eq_transpose_of_trivial, mulVec_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add]

/-- **(4.4.10)** Every vector decomposes into a row-space component and a null-space
component. The row space is the range of the transpose, the space in the domain
orthogonal to the kernel. -/
theorem range_null_decomposition_4_4_10 (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ r : EuclideanSpace ℝ (Fin m), ∃ z : EuclideanSpace ℝ (Fin n),
      A.toEuclideanLin z = 0 ∧ x = Aᵀ.toEuclideanLin r + z := by
  obtain ⟨z, hz, w, hw, hx⟩ := (LinearMap.ker A.toEuclideanLin).exists_add_mem_mem_orthogonal x
  rw [LinearMap.orthogonal_ker, ← Matrix.toEuclideanLin_transpose_eq_adjoint] at hw
  obtain ⟨r, hr⟩ := hw
  exact ⟨r, z, hz, by rw [hr, add_comm]; exact hx⟩

/-- **(4.4.11)** The difference of two feasible points is a null-space displacement. -/
theorem feasible_null_decomposition_4_4_11 {k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (N : Matrix (Fin n) (Fin k) ℝ) (x xF : Fin n → ℝ) (b : Fin m → ℝ)
    (hx : A *ᵥ x = b) (hF : A *ᵥ xF = b)
    (hN : ∀ z : Fin n → ℝ, A *ᵥ z = 0 → ∃ u, N *ᵥ u = z) :
    ∃ u, x = xF + N *ᵥ u := by
  obtain ⟨u, hu⟩ := hN (x - xF) (by rw [Matrix.mulVec_sub, hx, hF, sub_self])
  exact ⟨u, by rw [hu]; abel⟩

/-- **(4.4.12)** Premultiplying stationarity by the transpose of the null basis
gives the reduced system for the null-space coordinates. -/
theorem reduced_system_4_4_12 {k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (xF g : Fin n → ℝ) (y : Fin m → ℝ) (u : Fin k → ℝ)
    (hN : A * N = 0) (hstat : H *ᵥ (xF + N *ᵥ u) = g + Aᵀ *ᵥ y) :
    (Nᵀ * H * N) *ᵥ u = Nᵀ *ᵥ g - Nᵀ *ᵥ (H *ᵥ xF) := by
  have h := congrArg (fun v => Nᵀ *ᵥ v) hstat
  have hzero : Nᵀ * Aᵀ = 0 := by rw [← Matrix.transpose_mul, hN, transpose_zero]
  simp only [mulVec_add, mulVec_mulVec, hzero, zero_mulVec, add_zero] at h
  rw [mulVec_mulVec]
  exact eq_sub_of_add_eq (by simpa [add_comm, Matrix.mul_assoc] using h)

/-- **(4.4.13)** In pivot/free coordinates, the null basis has blocks
`[-R⁻¹ C; I]`. Reindexing these coordinates by the column permutation preserves
the kernel representation and the uniqueness of the free coefficients. -/
theorem null_basis_4_4_13 {k : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (C : Matrix (Fin m) (Fin k) ℝ)
    (hR : IsUnit R) (e : Fin (m + k) ≃ (Fin m ⊕ Fin k)) :
    let A := (Matrix.fromCols R C).submatrix id e
    let N := (Matrix.fromRows (-(R⁻¹ * C)) (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix e id
    Function.Injective N.mulVec ∧ ∀ z, A *ᵥ z = 0 ↔ ∃ u, N *ᵥ u = z := by
  dsimp only
  let N := (Matrix.fromRows (-(R⁻¹ * C)) (1 : Matrix (Fin k) (Fin k) ℝ)).submatrix e id
  have hN (u : Fin k → ℝ) :
      N *ᵥ u = Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e := by
    dsimp only [N]
    rw [show (id : Fin k → Fin k) = (Equiv.refl (Fin k) : Fin k → Fin k) from rfl,
      Matrix.submatrix_mulVec_equiv]
    simp [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  refine ⟨fun u v huv => ?_, fun z => ?_⟩
  · change N *ᵥ u = N *ᵥ v at huv
    rw [hN, hN] at huv
    funext j
    simpa using congrFun huv (e.symm (Sum.inr j))
  · rw [Matrix.submatrix_mulVec_equiv, Function.comp_id, Matrix.fromCols_mulVec]
    constructor
    · intro hz
      let u := z ∘ e.symm ∘ Sum.inr
      have hz' : R *ᵥ (z ∘ e.symm ∘ Sum.inl) = -(C *ᵥ u) := eq_neg_of_add_eq_zero_left hz
      have hp := (Matrix.nonsing_inv_mulVec_eq hR hz').symm
      rw [Matrix.mulVec_neg] at hp
      refine ⟨u, ?_⟩
      change N *ᵥ u = z
      rw [hN, ← hp]
      funext j
      have h : z (e.symm (e j)) = z j := by simp
      cases hj : e j <;> simpa [Function.comp_apply, hj, u] using h
    · rintro ⟨u, hu⟩
      change N *ᵥ u = z at hu
      rw [← hu, hN]
      have h₁ : ((Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e) ∘ e.symm) ∘ Sum.inl =
          -(R⁻¹ *ᵥ (C *ᵥ u)) := by ext i; simp
      have h₂ : ((Sum.elim (-(R⁻¹ *ᵥ (C *ᵥ u))) u ∘ e) ∘ e.symm) ∘ Sum.inr = u := by
        ext i
        simp
      rw [h₁, h₂, Matrix.mulVec_neg, Matrix.mulVec_nonsing_inv_mulVec hR, neg_add_cancel]

/-- **(4.4.14)** A minimizer of the equality-constrained quadratic objective. -/
def IsEqualityQuadraticMin (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (g x : Fin n → ℝ) (b : Fin m → ℝ) : Prop :=
  A *ᵥ x = b ∧ IsMinOn (fun z => (1 / 2 : ℝ) * (z ⬝ᵥ (H *ᵥ z)) - z ⬝ᵥ g)
    {z | A *ᵥ z = b} x

/-- **(4.4.14)** A stationary feasible point globally minimizes the quadratic if the
reduced Hessian is positive semidefinite. If it is positive definite, this global
minimizer is unique. -/
theorem quadratic_minimum_4_4_14 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) {x g : Fin n → ℝ} {y b : Fin m → ℝ}
    (hx : A *ᵥ x = b) (hstat : H *ᵥ x = g + Aᵀ *ᵥ y)
    (hnonneg : ∀ d : Fin n → ℝ, A *ᵥ d = 0 → 0 ≤ d ⬝ᵥ (H *ᵥ d)) :
    IsEqualityQuadraticMin H A g x b ∧
      ((∀ d : Fin n → ℝ, A *ᵥ d = 0 → d ≠ 0 → 0 < d ⬝ᵥ (H *ᵥ d)) →
        ∀ z, IsEqualityQuadraticMin H A g z b → z = x) := by
  let f (z : Fin n → ℝ) := (1 / 2 : ℝ) * (z ⬝ᵥ (H *ᵥ z)) - z ⬝ᵥ g
  have hd (z : Fin n → ℝ) (hz : A *ᵥ z = b) : A *ᵥ (z - x) = 0 := by
    rw [mulVec_sub, hz, hx, sub_self]
  have hdiff (z : Fin n → ℝ) (hz : A *ᵥ z = b) :
      f z - f x = (1 / 2 : ℝ) * ((z - x) ⬝ᵥ (H *ᵥ (z - x))) := by
    let d := z - x
    have hsplit : z = x + d := by dsimp [d]; abel
    have hsym : x ⬝ᵥ (H *ᵥ d) = d ⬝ᵥ (H *ᵥ x) := by
      conv_lhs => rw [← hH.eq]
      exact Matrix.dotProduct_transpose_mulVec H x d
    have hzstat : d ⬝ᵥ (H *ᵥ x) = d ⬝ᵥ g := by
      rw [hstat, dotProduct_add, Matrix.dotProduct_transpose_mulVec, hd z hz,
        dotProduct_zero, add_zero]
    change f z - f x = (1 / 2 : ℝ) * (d ⬝ᵥ (H *ᵥ d))
    conv_lhs => rw [hsplit]
    simp only [f, mulVec_add, dotProduct_add, add_dotProduct, hsym, hzstat]
    ring
  have hmin : IsEqualityQuadraticMin H A g x b :=
    ⟨hx, fun z hz => sub_nonneg.mp (by
      rw [hdiff z hz]
      exact mul_nonneg (by norm_num) (hnonneg (z - x) (hd z hz)))⟩
  refine ⟨hmin, fun hpos z hz => ?_⟩
  by_contra hne
  have hp := hpos (z - x) (hd z hz.1) (sub_ne_zero.2 hne)
  have hle : f z ≤ f x := hz.2 hx
  linarith [hdiff z hz.1]

/-- **(4.4.7)–(4.4.8)** A solution of the augmented system for a positive-definite
weight gives the weighted projection onto the affine constraint set. -/
theorem weighted_projection_of_system_4_4_8 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (x₀ x : EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (b : EuclideanSpace ℝ (Fin m))
    (h : Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim (WithLp.ofLp x) (-y) =
      Sum.elim (H *ᵥ WithLp.ofLp x₀) (WithLp.ofLp b)) :
    IsWeightedProjection H hH A b x₀ x := by
  obtain ⟨hs, hx⟩ := (projection_system_4_4_8 H A _ _ _ _).1 h
  have hSym : H.IsSymm := Matrix.isHermitian_iff_isSymm.1 hH.isHermitian
  have hpsd (d : Fin n → ℝ) : 0 ≤ d ⬝ᵥ (H *ᵥ d) := by
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg d
  have hmin := (quadratic_minimum_4_4_14 hSym A hx hs (fun d _ => hpsd d)).1.2
  have henergy (v : EuclideanSpace ℝ (Fin n)) :
      energyNorm H.toEuclideanLin v ^ 2 = WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp v) := by
    have he : energyNorm H.toEuclideanLin v = √(WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp v)) := by
      simp [energyNorm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply]
    rw [he, Real.sq_sqrt (hpsd _)]
  have hObj (z : EuclideanSpace ℝ (Fin n)) :
      (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2 =
        ((1 / 2 : ℝ) * (WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp z)) -
          WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp x₀)) +
        (1 / 2 : ℝ) * (WithLp.ofLp x₀ ⬝ᵥ (H *ᵥ WithLp.ofLp x₀)) := by
    have hcross : WithLp.ofLp x₀ ⬝ᵥ (H *ᵥ WithLp.ofLp z) =
        WithLp.ofLp z ⬝ᵥ (H *ᵥ WithLp.ofLp x₀) := by
      conv_lhs => rw [← hSym.eq]
      exact Matrix.dotProduct_transpose_mulVec _ _ _
    rw [henergy]
    simp only [WithLp.ofLp_sub, mulVec_sub, dotProduct_sub, sub_dotProduct, hcross]
    ring
  refine ⟨?_, fun z hz => ?_⟩
  · change A.toEuclideanLin x = b
    rw [Matrix.toEuclideanLin_apply, hx, WithLp.toLp_ofLp]
  · change A.toEuclideanLin z = b at hz
    have hz' : A *ᵥ WithLp.ofLp z = WithLp.ofLp b := by
      simpa only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hz
    change (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - x) ^ 2 ≤
      (1 / 2 : ℝ) * energyNorm H.toEuclideanLin (x₀ - z) ^ 2
    rw [hObj x, hObj z]
    exact add_le_add_left (isMinOn_iff.mp hmin _ hz') _

/-- A zero quadratic on an unconstrained line has semidefinite reduced curvature
and distinct global minimizers. -/
theorem semidefinite_reduced_quadratic_not_unique :
    let H : Matrix (Fin 1) (Fin 1) ℝ := 0
    let A : Matrix (Fin 0) (Fin 1) ℝ := 0
    (∀ d : Fin 1 → ℝ, 0 ≤ d ⬝ᵥ (H *ᵥ d)) ∧
      ∃ x z, x ≠ z ∧ IsEqualityQuadraticMin H A 0 x 0 ∧ IsEqualityQuadraticMin H A 0 z 0 := by
  dsimp only
  refine ⟨by simp, 0, fun _ => 1, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (0 : Fin 1)
    simp at this
  · exact ⟨by simp, fun _ _ => by simp⟩
  · exact ⟨by simp, fun _ _ => by simp⟩

end ConnGouldToint.Chapter04
