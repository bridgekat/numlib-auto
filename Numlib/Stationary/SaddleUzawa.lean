import Numlib.Stationary.Splitting

/-!
# Stationary iterations for saddle-point systems

For the system $Ax+B^Ty=f$, $Bx=g$, a primal residual correction followed by a multiplier
residual correction includes the Uzawa and Arrow–Hurwicz methods. The same update is induced
by a lower triangular matrix splitting when both correction matrices are invertible.

## Main definitions

* Matrix.saddleResidualStep: the two successive residual corrections.
* Matrix.saddleUzawaStep: the exact primal solve followed by a multiplier correction.
* Matrix.saddleLowerSplitting: the splitting with a lower triangular first factor.

## Main results

* Matrix.saddleUzawaStep_snd: eliminating the primal variable gives Richardson iteration.
* Matrix.saddleUzawaStep_snd_sub_of_residual: an inexact primal solve adds a forcing term.
* Matrix.saddleLowerSplitting_mulVec_step: the triangular splitting gives the residual step.
-/

set_option autoImplicit false

namespace Matrix

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [Field 𝕜]

/-- With primal and dual correction matrices $H$ and $K$, the stationary step computes
$x^+=x+H(f-Ax-B^Ty)$ and then $y^+=y+K(Bx^+-g)$. -/
def saddleResidualStep (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (H : Matrix n n 𝕜) (K : Matrix m m 𝕜) (f : n → 𝕜) (g : m → 𝕜)
    (state : (n → 𝕜) × (m → 𝕜)) : (n → 𝕜) × (m → 𝕜) :=
  let x := state.1 + H *ᵥ (f - A *ᵥ state.1 - Bᵀ *ᵥ state.2)
  (x, state.2 + K *ᵥ (B *ᵥ x - g))

/-- The exact Uzawa step computes $x^+=A^{-1}(f-B^Ty)$, $y^+=y+\omega(Bx^+-g)$.
The matrix inverse is the total nonsingular inverse. -/
noncomputable def saddleUzawaStep (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (ω : 𝕜) (f : n → 𝕜) (g y : m → 𝕜) : (n → 𝕜) × (m → 𝕜) :=
  let x := A⁻¹ *ᵥ (f - Bᵀ *ᵥ y)
  (x, y + ω • (B *ᵥ x - g))

/-- For nonsingular $A$, using $H=A^{-1}$ and $K=\omega I$ in the two residual corrections
gives the exact Uzawa step. -/
theorem saddleUzawaStep_eq_residualStep (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (hA : IsUnit A) (ω : 𝕜) (f : n → 𝕜) (g : m → 𝕜)
    (state : (n → 𝕜) × (m → 𝕜)) :
    saddleUzawaStep A B ω f g state.2 = saddleResidualStep A B A⁻¹ (ω • 1) f g state := by
  have hx :
      state.1 + A⁻¹ *ᵥ (f - A *ᵥ state.1 - Bᵀ *ᵥ state.2) = A⁻¹ *ᵥ (f - Bᵀ *ᵥ state.2) := by
    rw [mulVec_sub, mulVec_sub, mulVec_sub, mulVec_mulVec,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
      one_mulVec]
    abel
  simp [saddleUzawaStep, saddleResidualStep, hx, smul_mulVec]

omit [DecidableEq m] in
/-- The multiplier component of exact Uzawa is one Richardson step with coefficient
$BA^{-1}B^T$ and right-hand side $BA^{-1}f-g$. -/
theorem saddleUzawaStep_snd (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (ω : 𝕜) (f : n → 𝕜) (g y : m → 𝕜) :
    (saddleUzawaStep A B ω f g y).2 =
      y + ω • ((B * A⁻¹) *ᵥ f - g - (B * A⁻¹ * Bᵀ) *ᵥ y) := by
  simp only [saddleUzawaStep, mulVec_sub, mulVec_mulVec, Matrix.mul_assoc]
  congr 2
  abel

omit [DecidableEq n] [DecidableEq m] in
/-- If $(x_*,y_*)$ solves the saddle equations, the error of a residual step taken from
$(x,y)$ is the same residual step for zero right-hand sides, taken from
$(x-x_*,y-y_*)$. -/
theorem saddleResidualStep_sub (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (H : Matrix n n 𝕜) (K : Matrix m m 𝕜) (f : n → 𝕜) (g : m → 𝕜)
    (state sol : (n → 𝕜) × (m → 𝕜))
    (hf : A *ᵥ sol.1 + Bᵀ *ᵥ sol.2 = f) (hg : B *ᵥ sol.1 = g) :
    saddleResidualStep A B H K f g state - sol =
      saddleResidualStep A B H K 0 0 (state - sol) := by
  have hres :
      f - A *ᵥ state.1 - Bᵀ *ᵥ state.2 =
        0 - A *ᵥ (state.1 - sol.1) - Bᵀ *ᵥ (state.2 - sol.2) := by
    rw [← hf, mulVec_sub, mulVec_sub]
    abel
  let dx := H *ᵥ (f - A *ᵥ state.1 - Bᵀ *ᵥ state.2)
  have hx : state.1 + dx - sol.1 = state.1 - sol.1 + dx := by abel
  apply Prod.ext
  · change state.1 + dx - sol.1 =
      state.1 - sol.1 + H *ᵥ (0 - A *ᵥ (state.1 - sol.1) - Bᵀ *ᵥ (state.2 - sol.2))
    rw [← hres]
    exact hx
  have hBx : B *ᵥ (state.1 + dx - sol.1) = B *ᵥ (state.1 + dx) - g := by
    rw [mulVec_sub, hg]
  change state.2 + K *ᵥ (B *ᵥ (state.1 + dx) - g) - sol.2 =
    state.2 - sol.2 +
      K *ᵥ (B *ᵥ (state.1 - sol.1 + H *ᵥ
        (0 - A *ᵥ (state.1 - sol.1) - Bᵀ *ᵥ (state.2 - sol.2))) - 0)
  rw [← hres, ← hx, hBx, sub_zero]
  abel

/-- Suppose $A$ is nonsingular and $(x_*,y_*)$ solves the saddle equations. For a candidate
primal solution $x^+$ with inner residual $r=f-B^Ty-Ax^+$, the multiplier update satisfies
$$y^+-y_*=(I-\omega BA^{-1}B^T)(y-y_*)-\omega BA^{-1}r.$$ -/
theorem saddleUzawaStep_snd_sub_of_residual (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (hA : IsUnit A) (ω : 𝕜) (f x xStar : n → 𝕜) (g y yStar : m → 𝕜)
    (hf : A *ᵥ xStar + Bᵀ *ᵥ yStar = f) (hg : B *ᵥ xStar = g) :
    y + ω • (B *ᵥ x - g) - yStar =
      (1 - ω • (B * A⁻¹ * Bᵀ)) *ᵥ (y - yStar) -
        ω • ((B * A⁻¹) *ᵥ (f - Bᵀ *ᵥ y - A *ᵥ x)) := by
  have hdiff : A *ᵥ (x - xStar) =
      -(Bᵀ *ᵥ (y - yStar)) - (f - Bᵀ *ᵥ y - A *ᵥ x) := by
    rw [mulVec_sub, mulVec_sub, ← hf]
    abel
  have h := congrArg (fun v => (B * A⁻¹) *ᵥ v) hdiff
  simp only [mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
    Matrix.mul_one, mulVec_sub, mulVec_neg] at h
  have h' : B *ᵥ x - g = -((B * A⁻¹ * Bᵀ) *ᵥ (y - yStar)) -
      (B * A⁻¹) *ᵥ (f - Bᵀ *ᵥ y - A *ᵥ x) := by
    rw [← hg]
    simpa only [mulVec_sub, mulVec_mulVec, Matrix.mul_assoc,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), Matrix.mul_one] using h
  rw [h', sub_mulVec, one_mulVec, smul_mulVec, smul_sub, smul_neg]
  abel

/-- With $P$ and $D$ nonsingular, the saddle matrix splits using the lower triangular
matrix $\begin{bmatrix}P&0\\B&D\end{bmatrix}$ as the first factor. -/
noncomputable def saddleLowerSplitting (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (P : Matrix n n 𝕜) (D : Matrix m m 𝕜) (hP : IsUnit P) (hD : IsUnit D) :
    Stationary.Splitting (fromBlocks A Bᵀ B (0 : Matrix m m 𝕜)) where
  m := fromBlocks P 0 B D
  isUnit := by
    rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
    exact ((isUnit_iff_isUnit_det P).mp hP).mul ((isUnit_iff_isUnit_det D).mp hD)

/-- The remainder of the lower triangular splitting is
$\begin{bmatrix}P-A&-B^T\\0&D\end{bmatrix}$. -/
theorem saddleLowerSplitting_n (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (P : Matrix n n 𝕜) (D : Matrix m m 𝕜) (hP : IsUnit P) (hD : IsUnit D) :
    (saddleLowerSplitting A B P D hP hD).n = fromBlocks (P - A) (-Bᵀ) 0 D := by
  change fromBlocks P 0 B D - fromBlocks A Bᵀ B 0 = _
  ext (row | row) (col | col) <;> simp

/-- The iteration matrix is obtained by applying the inverse lower factor to its remainder.
Its top row consists of $U=P^{-1}(P-A)$ and $V=-P^{-1}B^T$. Its bottom row consists of
$-D^{-1}BU$ and $I-D^{-1}BV$. -/
theorem saddleLowerSplitting_iterationOperator (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (P : Matrix n n 𝕜) (D : Matrix m m 𝕜) (hP : IsUnit P) (hD : IsUnit D) :
    let U := P⁻¹ * (P - A)
    let V := P⁻¹ * (-Bᵀ)
    (saddleLowerSplitting A B P D hP hD).iterationOperator =
      fromBlocks U V (-(D⁻¹ * B * U)) (1 - D⁻¹ * B * V) := by
  intro U V
  let split := saddleLowerSplitting A B P D hP hD
  change split.iterationOperator = _
  rw [split.iterationOperator_eq]
  have hPD : P * P⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP)
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det D).mp hD)
  have h : split.m * fromBlocks U V (-(D⁻¹ * B * U)) (1 - D⁻¹ * B * V) = split.n := by
    change fromBlocks P 0 B D * _ = _
    rw [saddleLowerSplitting_n, fromBlocks_multiply]
    simp [U, V, ← Matrix.mul_assoc, hPD, hDD, Matrix.mul_sub, Matrix.mul_add]
  rw [← h, ← Matrix.mul_assoc, Ring.inverse_mul_cancel _ split.isUnit, Matrix.one_mul]

/-- The two residual corrections with $H=P^{-1}$ and $K=-D^{-1}$ give exactly the next
iterate of the lower triangular splitting. -/
theorem saddleLowerSplitting_mulVec_step (A : Matrix n n 𝕜) (B : Matrix m n 𝕜)
    (P : Matrix n n 𝕜) (D : Matrix m m 𝕜) (hP : IsUnit P) (hD : IsUnit D)
    (f : n → 𝕜) (g : m → 𝕜) (state : (n → 𝕜) × (m → 𝕜)) :
    let split := saddleLowerSplitting A B P D hP hD
    let next := saddleResidualStep A B P⁻¹ (-D⁻¹) f g state
    split.m *ᵥ Sum.elim next.1 next.2 =
      split.n *ᵥ Sum.elim state.1 state.2 + Sum.elim f g := by
  intro split next
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hP)
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det D).mp hD)
  change fromBlocks P 0 B D *ᵥ Sum.elim next.1 next.2 =
    (saddleLowerSplitting A B P D hP hD).n *ᵥ _ + _
  rw [saddleLowerSplitting_n, fromBlocks_mulVec, fromBlocks_mulVec]
  funext index
  cases index with
  | inl index =>
    simp only [Pi.add_apply, Sum.elim_inl, zero_mulVec, add_zero]
    change (P *ᵥ (state.1 + P⁻¹ *ᵥ (f - A *ᵥ state.1 - Bᵀ *ᵥ state.2))) index =
      (((P - A) *ᵥ state.1 + (-Bᵀ) *ᵥ state.2) + f) index
    simp only [mulVec_add, mulVec_mulVec, hPP, one_mulVec, sub_mulVec, neg_mulVec, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
    abel
  | inr index =>
    simp only [Pi.add_apply, Sum.elim_inr, zero_mulVec, zero_add]
    change ((B *ᵥ next.1) + D *ᵥ (state.2 + (-D⁻¹) *ᵥ (B *ᵥ next.1 - g))) index =
      (D *ᵥ state.2) index + g index
    simp only [mulVec_add, neg_mulVec, mulVec_neg, mulVec_mulVec, hDD, one_mulVec, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
    abel

end Matrix
