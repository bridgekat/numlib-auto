import Numlib.Stationary.SaddleUzawa
import Numlib.Stationary.SPD
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.LinearAlgebra.Matrix.SaddlePoint.Penalty

/-!
# Benzi, Golub and Liesen, Section 8: Stationary iterations

Section 8 of [benzi2005numerical] studies stationary methods for $Ax+B^Ty=f$, $Bx=g$.
Exact Uzawa uses an exact primal solve; Arrow–Hurwicz replaces it by one Richardson step.
The penalty method approximates the saddle system by a regularized system, while the method
of multipliers applies Uzawa to an equivalent augmented system. The algebraic proofs use
`Numlib.Stationary.SaddleUzawa` and `Numlib.LinearAlgebra.Matrix.SaddlePoint.Penalty`.

## Main definitions

* Equations (8.1), (8.2), `BenziGolubLiesen.uzawaStep` and `BenziGolubLiesen.uzawaSplitting`:
  the exact primal solve and multiplier update, and their lower triangular splitting.
* Equations (8.5)–(8.7), `BenziGolubLiesen.arrowHurwiczStep`,
  `BenziGolubLiesen.arrowHurwiczSplitting` and `BenziGolubLiesen.preconditionedArrowHurwiczStep`:
  the two residual corrections and their preconditioned version.
* Equations (8.8)–(8.10), `BenziGolubLiesen.saddleObjective`, `BenziGolubLiesen.IsFeasible`
  and `BenziGolubLiesen.penaltyStep`: the constrained quadratic and its penalty approximation.
* Equations (8.12)–(8.14), `BenziGolubLiesen.augmentedLagrangian` and
  `BenziGolubLiesen.multiplierStep`: augmentation of the quadratic and iteration.

## Main results

* Equations (8.3), (8.4), `BenziGolubLiesen.uzawa_reduced_step` and
  `BenziGolubLiesen.uzawa_reduced_system`: exact Uzawa is Richardson on the reduced system.
* Equation (8.11), `BenziGolubLiesen.penaltyStep_regularized`: the penalty pair solves the
  regularized saddle equations, and `BenziGolubLiesen.penalty_error` bounds the two errors.
* Equations (8.13), (8.14), `BenziGolubLiesen.augmentedLagrangian_minimizer` and
  `BenziGolubLiesen.multiplier_system_iff`: the augmented solve minimizes the augmented
  Lagrangian at fixed multiplier, and the augmented saddle system preserves the solution.
* `BenziGolubLiesen.multiplier_tendsto`: every positive parameter gives convergence.
* `BenziGolubLiesen.multiplier_spectralRadius_tendsto_zero`: the reduced factor tends to zero.

## Deviations from the source

* **Before (8.3)** (correction). Reality of the Uzawa spectrum requires a symmetry hypothesis;
  invertibility of $A$ alone is not enough.
* **After (8.4)** (correction). Positive definiteness of $BA^{-1}B^T$ requires full row rank of $B$.

## Not formalized

* **Section 8.1, Stokes applications.** The mesh-independent Schur bounds for particular
  Stokes discretizations require discrete operator and inf-sup hypotheses.
* **Section 8.1, convergence of variants.** The text cites inexact, preconditioned and variable
  relaxation methods and Arrow–Hurwicz parameter estimates without giving their bounds.
* **Section 8.2, conditioning of the augmented primal block.** Linear growth of the condition
  number is not unconditional: with square $A=B=I$, the augmented block is $(1+gamma)I$,
  whose condition number is one. The growth estimate for $0<\operatorname{rank}B<n$ is not proved.
* **Section 8.3.** This section names SOR, block SOR, and alternating-direction methods but
  states no updates or bounds for specific saddle-point variants.
-/

set_option autoImplicit false

open Matrix Stationary Filter Asymptotics
open scoped Topology

namespace BenziGolubLiesen

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Equation (8.1)** of [benzi2005numerical]. For real blocks $A,B$, right-hand sides
$f,g$ and relaxation parameter $\omega$, the **Uzawa step** from multiplier $y$ is
$x^+=A^{-1}(f-B^Ty)$, $y^+=y+\omega(Bx^+-g)$. The matrix inverse is zero when $A$ is singular. -/
noncomputable abbrev uzawaStep (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (ω : ℝ) (f : n → ℝ) (g y : m → ℝ) :=
  saddleUzawaStep A B ω f g y

omit [DecidableEq m] in
/-- **Equation (8.1)** of [benzi2005numerical]. For nonsingular $A$, a next pair equals
the Uzawa step if and only if it satisfies both coupled update equations. -/
theorem uzawaStep_eq_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) (ω : ℝ) (f xNext : n → ℝ) (g y yNext : m → ℝ) :
    (xNext, yNext) = uzawaStep A B ω f g y ↔
      A *ᵥ xNext = f - Bᵀ *ᵥ y ∧ yNext = y + ω • (B *ᵥ xNext - g) := by
  have hdet := (isUnit_iff_isUnit_det A).mp hA
  constructor
  · intro he
    cases he
    simp only [mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec, true_and]
  · rintro ⟨hx, hy⟩
    have h := congrArg (fun z => A⁻¹ *ᵥ z) hx
    change A⁻¹ *ᵥ (A *ᵥ xNext) = A⁻¹ *ᵥ (f - Bᵀ *ᵥ y) at h
    rw [mulVec_mulVec, nonsing_inv_mul A hdet, one_mulVec] at h
    exact Prod.ext h (by rw [hy, h]; rfl)

private theorem isUnit_scalar_one {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix ι ι ℝ)) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact hc.isUnit.map (algebraMap ℝ (Matrix ι ι ℝ))

private theorem inv_scalar_one {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : c ≠ 0) :
    (c • (1 : Matrix ι ι ℝ))⁻¹ = c⁻¹ • 1 := by
  rw [nonsing_inv_eq_ringInverse, ringInverse_smul hc isUnit_one, Ring.inverse_one]

private theorem inv_neg_relaxation {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ℝ} (hω : ω ≠ 0) :
    ((-ω⁻¹) • (1 : Matrix ι ι ℝ))⁻¹ = (-ω) • 1 := by
  rw [inv_scalar_one (neg_ne_zero.mpr (inv_ne_zero hω)), inv_neg, inv_inv]

private theorem neg_inv_neg_relaxation {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ℝ}
    (hω : ω ≠ 0) :
    -(((-ω⁻¹) • (1 : Matrix ι ι ℝ))⁻¹) = ω • 1 := by
  rw [inv_neg_relaxation hω, neg_smul, neg_neg]

/-- **Equation (8.2)** of [benzi2005numerical]. For nonsingular $A$ and $\omega\ne 0$,
the **Uzawa splitting** has first factor
$\mathcal{P}=\begin{bmatrix}A&0\\B&-\omega^{-1}I\end{bmatrix}$. -/
noncomputable def uzawaSplitting (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) :
    Splitting (fromBlocks A Bᵀ B (0 : Matrix m m ℝ)) :=
  saddleLowerSplitting A B A ((-ω⁻¹) • 1) hA (isUnit_scalar_one (neg_ne_zero.mpr (inv_ne_zero hω)))

/-- **Equation (8.2)** of [benzi2005numerical]. For nonsingular $A$ and $\omega\ne0$ the
remainder of the Uzawa splitting is
$\mathcal{Q}=\begin{bmatrix}0&-B^T\\0&-\omega^{-1}I\end{bmatrix}$. -/
theorem uzawaSplitting_n (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) :
    (uzawaSplitting A B hA hω).n = fromBlocks (0 : Matrix n n ℝ) (-Bᵀ) 0 ((-ω⁻¹) • 1) := by
  rw [uzawaSplitting, saddleLowerSplitting_n, sub_self]

/-- **Equation (8.2)** of [benzi2005numerical], iteration matrix. For nonsingular $A$ and
$\omega\ne0$, the Uzawa iteration matrix is
$$\mathcal{T}=\begin{bmatrix}0&-A^{-1}B^T\\0&I-\omega BA^{-1}B^T\end{bmatrix}.$$ -/
theorem uzawa_iterationOperator (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) :
    (uzawaSplitting A B hA hω).iterationOperator =
      fromBlocks 0 (-(A⁻¹ * Bᵀ)) 0 (1 - ω • (B * A⁻¹ * Bᵀ)) := by
  rw [uzawaSplitting, saddleLowerSplitting_iterationOperator, inv_neg_relaxation hω]
  simp [Matrix.mul_assoc]

/-- **Equation (8.2)** of [benzi2005numerical], splitting update. With nonsingular $A$ and
$\omega\ne0$, the Uzawa step gives $\mathcal{P}u^+=\mathcal{Q}u+(f,g)$. -/
theorem uzawa_splitting_step (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) (f x : n → ℝ) (g y : m → ℝ) :
    let split := uzawaSplitting A B hA hω
    let next := uzawaStep A B ω f g y
    split.m *ᵥ Sum.elim next.1 next.2 = split.n *ᵥ Sum.elim x y + Sum.elim f g := by
  rw [show uzawaStep A B ω f g y = saddleResidualStep A B A⁻¹ (ω • 1) f g (x, y)
      from saddleUzawaStep_eq_residualStep A B hA ω f g (x, y)]
  have h := saddleLowerSplitting_mulVec_step A B A ((-ω⁻¹) • 1) hA
    (isUnit_scalar_one (neg_ne_zero.mpr (inv_ne_zero hω))) f g (x, y)
  rw [neg_inv_neg_relaxation hω] at h
  exact h

/-- **Section 8.1** of [benzi2005numerical], spectrum of the Uzawa iteration matrix.
For nonsingular $A$ and $\omega\ne0$, the characteristic polynomial is $X^n$ times the
characteristic polynomial of $I-\omega BA^{-1}B^T$. -/
theorem uzawa_iterationCharpoly (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) :
    (uzawaSplitting A B hA hω).iterationOperator.charpoly =
      Polynomial.X ^ Fintype.card n * (1 - ω • (B * A⁻¹ * Bᵀ)).charpoly := by
  rw [uzawa_iterationOperator, charpoly_fromBlocks_zero₂₁, charpoly_zero]

/-- **Section 8.1** of [benzi2005numerical], spectrum of the Uzawa iteration matrix.
For nonsingular $A$ and $\omega\ne0$, a complex scalar is in the spectrum of the full
iteration matrix if and only if it is a root of $X^n$ or it is in the spectrum of the
reduced iteration matrix. -/
theorem uzawa_mem_iterationSpectrum_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify (uzawaSplitting A B hA hω).iterationOperator) ↔
      μ ^ Fintype.card n = 0 ∨ μ ∈ spectrum ℂ (complexify (1 - ω • (B * A⁻¹ * Bᵀ))) := by
  rw [mem_spectrum_complexify_iff, uzawa_iterationCharpoly, mem_spectrum_complexify_iff]
  simp only [Polynomial.IsRoot.def, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, mul_eq_zero]

/-- **Section 8.1** of [benzi2005numerical], reality of the Uzawa spectrum. If $A$ is nonsingular
and symmetric and $\omega\ne0$, all eigenvalues of the iteration matrix are real.

**Correction.** Invertibility alone is not enough. Take $A=\begin{bmatrix}0&-1\\1&0\end{bmatrix}$,
$B=I$ and $\omega=1$; the reduced iteration matrix has eigenvalues $1\pm i$. -/
theorem uzawa_iterationSpectrum_real {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : IsUnit A) (hs : A.IsHermitian) {ω : ℝ} (hω : ω ≠ 0) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify (uzawaSplitting A B hA hω).iterationOperator)) :
    μ.im = 0 := by
  rcases (uzawa_mem_iterationSpectrum_iff A B hA hω μ).mp hμ with h | h
  · by_contra hn
    have hz : μ ≠ 0 := by intro hm; exact hn (by simp [hm])
    exact pow_ne_zero _ hz h
  · have hS : (B * A⁻¹ * Bᵀ).IsHermitian := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        isHermitian_conjTranspose_mul_mul Bᵀ hs.inv
    have hG : (1 - ω • (B * A⁻¹ * Bᵀ)).IsHermitian :=
      isHermitian_one.sub (hS.smul (show IsSelfAdjoint ω from rfl))
    rw [((isHermitian_complexify_iff _).mpr hG).spectrum_eq_image_range] at h
    obtain ⟨-, -, rfl⟩ := h
    exact Complex.ofReal_im _

omit [DecidableEq m] in
/-- **Equation (8.3)** of [benzi2005numerical]. The multiplier update of exact Uzawa is
$y^+=y+\omega(BA^{-1}f-g-BA^{-1}B^T y)$. -/
theorem uzawa_reduced_step (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (ω : ℝ) (f : n → ℝ) (g y : m → ℝ) :
    (uzawaStep A B ω f g y).2 =
      y + ω • ((B * A⁻¹) *ᵥ f - g - (B * A⁻¹ * Bᵀ) *ᵥ y) :=
  saddleUzawaStep_snd A B ω f g y

omit [DecidableEq m] in
/-- **Equation (8.4)** of [benzi2005numerical]. For nonsingular $A$, $(x,y)$ solves the
saddle equations if and only if $x=A^{-1}(f-B^Ty)$ and $BA^{-1}B^Ty=BA^{-1}f-g$. -/
theorem uzawa_reduced_system (A : Matrix n n ℝ) (B : Matrix m n ℝ) (hA : IsUnit A)
    (f x : n → ℝ) (g y : m → ℝ) :
    (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x = g) ↔
      (x = A⁻¹ *ᵥ (f - Bᵀ *ᵥ y) ∧ (B * A⁻¹ * Bᵀ) *ᵥ y = (B * A⁻¹) *ᵥ f - g) := by
  have hdet := (isUnit_iff_isUnit_det A).mp hA
  have htop : A *ᵥ x + Bᵀ *ᵥ y = f ↔ x = A⁻¹ *ᵥ (f - Bᵀ *ᵥ y) := by
    rw [← eq_sub_iff_add_eq]
    constructor
    · intro h
      rw [← h, mulVec_mulVec, nonsing_inv_mul A hdet, one_mulVec]
    · intro h
      rw [h, mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  rw [htop]
  refine and_congr_right fun h => ?_
  simp only [h, mulVec_sub, mulVec_mulVec, Matrix.mul_assoc]
  rw [sub_eq_iff_eq_add]
  constructor <;> intro he <;> rw [he] <;> abel

omit [DecidableEq m] in
/-- **Section 8.1** of [benzi2005numerical], positive definiteness of the reduced matrix.
If $A$ is symmetric positive definite and $B$ has full row rank, then $BA^{-1}B^T$ is
symmetric positive definite.

**Correction.** The text does not require full row rank. If $B=0$ and has at least one
row, the reduced matrix is zero, regardless of $A$. -/
theorem uzawa_schur_posDef {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : A.PosDef) (hB : Function.Injective Bᵀ.mulVec) : (B * A⁻¹ * Bᵀ).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hA.inv.conjTranspose_mul_mul_same hB

/-- **Section 8.1** of [benzi2005numerical], convergence interval. For symmetric positive
definite $A$ and full row rank $B$, let $\ell$ and $L$ be the smallest and largest eigenvalues
of $S=BA^{-1}B^T$. The iteration matrix $I-\omega S$ has spectral radius less than one if
and only if $0<\omega<2/L$. -/
theorem uzawa_convergenceCriterion {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : A.PosDef) (hB : Function.Injective Bᵀ.mulVec) {ℓ L : ℝ}
    (hsub : spectrum ℝ (B * A⁻¹ * Bᵀ) ⊆ Set.Icc ℓ L)
    (hℓ : ℓ ∈ spectrum ℝ (B * A⁻¹ * Bᵀ)) (hL : L ∈ spectrum ℝ (B * A⁻¹ * Bᵀ)) (ω : ℝ) :
    complexSpectralRadius (1 - ω • (B * A⁻¹ * Bᵀ)) < 1 ↔ 0 < ω ∧ ω < 2 / L := by
  have hS := uzawa_schur_posDef B hA hB
  obtain ⟨index, hindex⟩ := (hS.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hℓ)
  have hpos : 0 < ℓ := hindex ▸ hS.eigenvalues_pos index
  exact Splitting.complexSpectralRadius_one_sub_smul_lt_one_iff
    (hS.isHermitian.spectrum_complexify_subset hsub) hℓ hL hpos ω

/-- **Section 8.1** of [benzi2005numerical], optimal relaxation. For symmetric positive
definite $A$ and full row rank $B$, let $\ell$ and $L$ be the smallest and largest eigenvalues
of $S=BA^{-1}B^T$. Then $\omega_*=2/(\ell+L)$ minimizes the spectral radius of $I-\omega S$
over positive $\omega$. -/
theorem uzawa_optimalRelaxation {A : Matrix n n ℝ} (B : Matrix m n ℝ)
    (hA : A.PosDef) (hB : Function.Injective Bᵀ.mulVec) {ℓ L : ℝ}
    (hsub : spectrum ℝ (B * A⁻¹ * Bᵀ) ⊆ Set.Icc ℓ L)
    (hℓ : ℓ ∈ spectrum ℝ (B * A⁻¹ * Bᵀ)) (hL : L ∈ spectrum ℝ (B * A⁻¹ * Bᵀ)) :
    IsMinOn (fun ω : ℝ => complexSpectralRadius (1 - ω • (B * A⁻¹ * Bᵀ))) (Set.Ioi 0)
      (2 / (ℓ + L)) := by
  have hS := uzawa_schur_posDef B hA hB
  obtain ⟨index, hindex⟩ := (hS.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hℓ)
  exact Splitting.isMinOn_richardson_complexSpectralRadius hS.isHermitian hsub hℓ hL
    (hindex ▸ hS.eigenvalues_pos index)

/-- **Section 8.1** of [benzi2005numerical], convergence of the coupled iterates. If $A$
is nonsingular, there is at least one constraint, $\omega\ne0$, and the reduced iteration
has spectral radius less than one, the Uzawa iterates from any initial pair converge to the
saddle-system solution. -/
theorem uzawa_tendsto_of_spectralRadius_lt_one [Nonempty m]
    (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : IsUnit A) {ω : ℝ} (hω : ω ≠ 0)
    (hρ : complexSpectralRadius (1 - ω • (B * A⁻¹ * Bᵀ)) < 1)
    (f : n → ℝ) (g : m → ℝ) (initial sol : (n → ℝ) × (m → ℝ))
    (hf : A *ᵥ sol.1 + Bᵀ *ᵥ sol.2 = f) (hg : B *ᵥ sol.1 = g) :
    let update := fun state : (n → ℝ) × (m → ℝ) => uzawaStep A B ω f g state.2
    let join := fun state : (n → ℝ) × (m → ℝ) => Sum.elim state.1 state.2
    Tendsto (fun k => join (update^[k] initial)) atTop (𝓝 (join sol)) := by
  intro update join
  let split := uzawaSplitting A B hA hω
  let rhs := Sum.elim f g
  let advance := fun u => split.iterationOperator *ᵥ u + split.m⁻¹ *ᵥ rhs
  have hfull : complexSpectralRadius split.iterationOperator < 1 := by
    rw [complexSpectralRadius_lt_one_iff_forall_norm_lt] at hρ ⊢
    intro μ hμ
    rcases (uzawa_mem_iterationSpectrum_iff A B hA hω μ).mp hμ with h | h
    · have : μ = 0 := by
        by_contra hn
        exact pow_ne_zero _ hn h
      simp [this]
    · exact hρ _ h
  have hstep (state : (n → ℝ) × (m → ℝ)) : join (update state) = advance (join state) := by
    have h := uzawa_splitting_step A B hA hω f state.1 g state.2
    change split.m *ᵥ join (update state) = split.n *ᵥ join state + rhs at h
    have eq := congrArg (fun v => split.m⁻¹ *ᵥ v) h
    simpa only [advance, mulVec_add, mulVec_mulVec, one_mulVec, split.iterationOperator_eq,
      nonsing_inv_eq_ringInverse, Ring.inverse_mul_cancel _ split.isUnit] using eq
  have hiter (k : ℕ) : join (update^[k] initial) = advance^[k] (join initial) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]
  have hsol : (fromBlocks A Bᵀ B (0 : Matrix m m ℝ)) *ᵥ join sol = rhs := by
    rw [fromBlocks_mulVec]
    change Sum.elim (A *ᵥ sol.1 + Bᵀ *ᵥ sol.2) (B *ᵥ sol.1 + 0 *ᵥ sol.2) = rhs
    simp [hf, hg, rhs]
  have hfix : (fromBlocks A Bᵀ B (0 : Matrix m m ℝ))⁻¹ *ᵥ rhs = join sol := by
    have hunit := split.isUnit_of_complexSpectralRadius_lt_one hfull
    rw [← hsol, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hunit), one_mulVec]
  simp only [hiter]
  simpa only [hfix] using
    split.tendsto_iterate_of_complexSpectralRadius_lt_one hfull rhs (join initial)

/-- **Equation (8.5)** of [benzi2005numerical]. The **Arrow–Hurwicz step** updates
$x^+=x+\alpha(f-Ax-B^Ty)$ and then $y^+=y+\omega(Bx^+-g)$. -/
noncomputable def arrowHurwiczStep (A : Matrix n n ℝ) (B : Matrix m n ℝ) (α ω : ℝ)
    (f : n → ℝ) (g : m → ℝ) (state : (n → ℝ) × (m → ℝ)) :=
  saddleResidualStep A B (α • 1) (ω • 1) f g state

/-- **Equation (8.6)** of [benzi2005numerical]. For $\alpha,\omega\ne0$, the
**Arrow–Hurwicz splitting** has lower factor
$\mathcal{P}=\begin{bmatrix}\alpha^{-1}I&0\\B&-\omega^{-1}I\end{bmatrix}$. -/
noncomputable def arrowHurwiczSplitting (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    {α ω : ℝ} (hα : α ≠ 0) (hω : ω ≠ 0) :
    Splitting (fromBlocks A Bᵀ B (0 : Matrix m m ℝ)) :=
  saddleLowerSplitting A B (α⁻¹ • 1) ((-ω⁻¹) • 1)
    (isUnit_scalar_one (inv_ne_zero hα)) (isUnit_scalar_one (neg_ne_zero.mpr (inv_ne_zero hω)))

/-- **Equation (8.6)** of [benzi2005numerical]. For $\alpha,\omega\ne0$ the remainder is
$\mathcal{Q}=\begin{bmatrix}\alpha^{-1}I-A&-B^T\\0&-\omega^{-1}I\end{bmatrix}$. -/
theorem arrowHurwiczSplitting_n (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    {α ω : ℝ} (hα : α ≠ 0) (hω : ω ≠ 0) :
    (arrowHurwiczSplitting A B hα hω).n =
      fromBlocks (α⁻¹ • 1 - A) (-Bᵀ) 0 ((-ω⁻¹) • 1) :=
  saddleLowerSplitting_n _ _ _ _ _ _

/-- **Equation (8.6)** of [benzi2005numerical], splitting update. For $\alpha,\omega\ne0$
the Arrow–Hurwicz step gives $\mathcal{P}u^+=\mathcal{Q}u+(f,g)$. -/
theorem arrowHurwicz_splitting_step (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    {α ω : ℝ} (hα : α ≠ 0) (hω : ω ≠ 0) (f x : n → ℝ) (g y : m → ℝ) :
    let split := arrowHurwiczSplitting A B hα hω
    let next := arrowHurwiczStep A B α ω f g (x, y)
    split.m *ᵥ Sum.elim next.1 next.2 = split.n *ᵥ Sum.elim x y + Sum.elim f g := by
  have h := saddleLowerSplitting_mulVec_step A B (α⁻¹ • 1) ((-ω⁻¹) • 1)
    (isUnit_scalar_one (inv_ne_zero hα)) (isUnit_scalar_one (neg_ne_zero.mpr (inv_ne_zero hω)))
    f g (x, y)
  rw [inv_scalar_one (inv_ne_zero hα), inv_inv, neg_inv_neg_relaxation hω] at h
  exact h

/-- **Equation (8.7)** of [benzi2005numerical]. The **preconditioned Arrow–Hurwicz step**
uses $x^+=x+\alpha Q_A^{-1}(f-Ax-B^Ty)$ and $y^+=y+\omega Q_B^{-1}(Bx^+-g)$.
The matrix inverses are total and are zero for singular preconditioners. -/
noncomputable def preconditionedArrowHurwiczStep (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (QA : Matrix n n ℝ) (QB : Matrix m m ℝ) (α ω : ℝ) (f : n → ℝ) (g : m → ℝ)
    (state : (n → ℝ) × (m → ℝ)) :=
  saddleResidualStep A B (α • QA⁻¹) (ω • QB⁻¹) f g state

/-- **Section 8.1** of [benzi2005numerical], inexact Uzawa. Use the inner solver $F$ with
the current primal iterate as its initial guess and $f-B^Ty$ as its right-hand side.
If $x^+=F(x,f-B^Ty)$, return $(x^+,y+\omega(Bx^+-g))$. -/
def inexactUzawaStep (B : Matrix m n ℝ) (solve : (n → ℝ) → (n → ℝ) → (n → ℝ))
    (ω : ℝ) (f : n → ℝ) (g : m → ℝ) (state : (n → ℝ) × (m → ℝ)) : (n → ℝ) × (m → ℝ) :=
  let x := solve state.1 (f - Bᵀ *ᵥ state.2)
  (x, state.2 + ω • (B *ᵥ x - g))

/-- **Section 8.1** of [benzi2005numerical], Arrow–Hurwicz as inexact Uzawa. Taking just one
Richardson step of length $\alpha$ as the inner solver gives the Arrow–Hurwicz step. -/
theorem inexactUzawaStep_eq_arrowHurwiczStep (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (α ω : ℝ) (f : n → ℝ) (g : m → ℝ) (state : (n → ℝ) × (m → ℝ)) :
    inexactUzawaStep B (fun x rhs => x + α • (rhs - A *ᵥ x)) ω f g state =
      arrowHurwiczStep A B α ω f g state := by
  have hres : f - Bᵀ *ᵥ state.2 - A *ᵥ state.1 = f - A *ᵥ state.1 - Bᵀ *ᵥ state.2 := by
    abel
  simp [inexactUzawaStep, arrowHurwiczStep, saddleResidualStep, smul_mulVec, hres]

/-- **Section 8.1** of [benzi2005numerical], inexact Uzawa. With nonsingular $A$, exact solution
$(x_*,y_*)$, and primal inner residual $r=f-B^Ty-Ax^+$, the multiplier error after updating
using the approximate $x^+$ is $(I-\omega BA^{-1}B^T)(y-y_*)-\omega BA^{-1}r$. -/
theorem inexactUzawa_error (A : Matrix n n ℝ) (B : Matrix m n ℝ) (hA : IsUnit A)
    (ω : ℝ) (f x xStar : n → ℝ) (g y yStar : m → ℝ)
    (hf : A *ᵥ xStar + Bᵀ *ᵥ yStar = f) (hg : B *ᵥ xStar = g) :
    y + ω • (B *ᵥ x - g) - yStar =
      (1 - ω • (B * A⁻¹ * Bᵀ)) *ᵥ (y - yStar) -
        ω • ((B * A⁻¹) *ᵥ (f - Bᵀ *ᵥ y - A *ᵥ x)) :=
  saddleUzawaStep_snd_sub_of_residual A B hA ω f x xStar g y yStar hf hg

/-! ### Penalty and multiplier methods -/

/-- **Equation (8.8)** of [benzi2005numerical]. The **primal objective** is
$J(x)=\frac12x^TAx-f^Tx$. -/
noncomputable abbrev saddleObjective (A : Matrix n n ℝ) (f x : n → ℝ) : ℝ :=
  saddleQuadratic A f x

omit [DecidableEq m] in
/-- **Section 8.1** of [benzi2005numerical], primal minimization. If $A$ is symmetric positive
definite, the next Uzawa primal iterate uniquely minimizes the quadratic with linear term
$f-B^Ty$. -/
theorem uzawa_primal_lt (A : Matrix n n ℝ) (B : Matrix m n ℝ) (hA : A.PosDef)
    (ω : ℝ) (f z : n → ℝ) (g y : m → ℝ) (hz : z ≠ (uzawaStep A B ω f g y).1) :
    saddleObjective A (f - Bᵀ *ᵥ y) (uzawaStep A B ω f g y).1 <
      saddleObjective A (f - Bᵀ *ᵥ y) z := by
  exact saddleQuadratic_lt_of_mulVec_eq hA
    ((uzawaStep_eq_iff A B hA.isUnit ω f (uzawaStep A B ω f g y).1 g y
      (uzawaStep A B ω f g y).2).mp rfl).1 hz

/-- **Equation (8.9)** of [benzi2005numerical]. A primal vector $x$ is **feasible** if $Bx=g$. -/
def IsFeasible (B : Matrix m n ℝ) (g : m → ℝ) (x : n → ℝ) : Prop := B *ᵥ x = g

omit [DecidableEq n] [DecidableEq m] in
/-- **Equations (8.8) and (8.9)** of [benzi2005numerical]. For positive semidefinite $A$
with $\ker A\cap\ker B=\{0\}$, the primal component of a saddle solution is the unique
minimizer of $J$ among feasible vectors. -/
theorem saddleObjective_lt_of_feasible (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (f x z : n → ℝ) (g y : m → ℝ) (hf : A *ᵥ x + Bᵀ *ᵥ y = f)
    (hx : IsFeasible B g x) (hz : IsFeasible B g z) (hne : z ≠ x) :
    saddleObjective A f x < saddleObjective A f z :=
  saddleQuadratic_lt_of_saddle_solution B hA hker hf (hz.trans hx.symm) hne

/-- **Section 8.2** of [benzi2005numerical], penalty objective. The **penalized quadratic**
adds $\frac{\gamma}{2}\|Bx-g\|_2^2$ to the primal objective. -/
noncomputable def penaltyObjective (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f x : n → ℝ) (g : m → ℝ) : ℝ := saddleAugmentedLagrangian A B γ f x g 0

/-- **Equation (8.10)** of [benzi2005numerical]. The **penalty approximation** for $\gamma$
solves $(A+\gamma B^TB)x=f+\gamma B^Tg$ by matrix inversion and returns $(x,\gamma(Bx-g))$.
The matrix inverse is zero if the primal block is singular. -/
noncomputable def penaltyStep (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f : n → ℝ) (g : m → ℝ) : (n → ℝ) × (m → ℝ) :=
  let x := (saddleAugmentedPrimal A B γ)⁻¹ *ᵥ saddleAugmentedRhs B γ f g
  (x, saddlePenaltyMultiplier B γ g x)

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (8.11)** of [benzi2005numerical]. For $\gamma\ne0$ the penalty equation and
the associated multiplier formula are equivalent to $Ax+B^Ty=f$, $Bx-\gamma^{-1}y=g$. -/
theorem penalty_regularized_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    {γ : ℝ} (hγ : γ ≠ 0) (f x : n → ℝ) (g y : m → ℝ) :
    (saddleAugmentedPrimal A B γ *ᵥ x = saddleAugmentedRhs B γ f g ∧
      y = saddlePenaltyMultiplier B γ g x) ↔
      (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x - γ⁻¹ • y = g) :=
  saddlePenalty_equations_iff A B hγ f x g y

omit [DecidableEq m] in
/-- **Equations (8.10) and (8.11)** of [benzi2005numerical]. For positive $\gamma$ and
positive semidefinite $A$ with $\ker A\cap\ker B=\{0\}$, the penalty approximation solves
the regularized saddle equations. -/
theorem penaltyStep_regularized (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) (f : n → ℝ) (g : m → ℝ) :
    let state := penaltyStep A B γ f g
    A *ᵥ state.1 + Bᵀ *ᵥ state.2 = f ∧ B *ᵥ state.1 - γ⁻¹ • state.2 = g := by
  have hP := posDef_saddleAugmentedPrimal B hA hker hγ
  apply (penalty_regularized_iff A B hγ.ne' _ _ _ _).mp
  refine ⟨?_, rfl⟩
  dsimp [penaltyStep]
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP.isUnit), one_mulVec]

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (8.11)** of [benzi2005numerical]. The penalized saddle system has a unique pair
of solutions. The constraint matrix need not have full row rank. -/
theorem existsUnique_penalty_regularized (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) (f : n → ℝ) (g : m → ℝ) :
    ∃! state : (n → ℝ) × (m → ℝ),
      A *ᵥ state.1 + Bᵀ *ᵥ state.2 = f ∧ B *ᵥ state.1 - γ⁻¹ • state.2 = g := by
  classical
  let state := penaltyStep A B γ f g
  have hs := penaltyStep_regularized A B hA hker hγ f g
  refine ⟨state, hs, ?_⟩
  rintro ⟨x, y⟩ hxy
  have ⟨hx, hy⟩ := (penalty_regularized_iff A B hγ.ne' f x g y).mpr hxy
  have ⟨hs₁, hs₂⟩ := (penalty_regularized_iff A B hγ.ne' f state.1 g state.2).mpr hs
  have hP := posDef_saddleAugmentedPrimal B hA hker hγ
  have hxs : x = state.1 := mulVec_injective_iff_isUnit.mpr hP.isUnit (hx.trans hs₁.symm)
  exact Prod.ext hxs (hy.trans ((congrArg (saddlePenaltyMultiplier B γ g) hxs).trans hs₂.symm))

private noncomputable def euclideanRestriction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (embed : κ → ι) : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ κ :=
  (show (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ κ from
    { toFun := fun z => WithLp.toLp 2 (z ∘ embed)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

omit [DecidableEq m] in
/-- **Section 8.2** of [benzi2005numerical], error of the penalty method. Assume $A$
is symmetric positive semidefinite, $B$ has full row rank, and $\ker A\cap\ker B=\{0\}$.
For a saddle solution $(x_*,y_*)$ and the pair $(x(\gamma),y(\gamma))$ computed by the
penalty method, the errors in both components are $O(\gamma^{-1})$ in Euclidean norm
as $\gamma\to+\infty$. -/
theorem penalty_error (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (f xStar : n → ℝ) (g yStar : m → ℝ)
    (hsol : A *ᵥ xStar + Bᵀ *ᵥ yStar = f ∧ B *ᵥ xStar = g) :
    (fun γ => WithLp.toLp 2 ((penaltyStep A B γ f g).1 - xStar)) =O[atTop] (fun γ : ℝ => γ⁻¹) ∧
    (fun γ => WithLp.toLp 2 ((penaltyStep A B γ f g).2 - yStar)) =O[atTop] (fun γ : ℝ => γ⁻¹) := by
  classical
  let M := fromBlocks A Bᵀ B (0 : Matrix m m ℝ)
  let D := fromBlocks (0 : Matrix n n ℝ) 0 0 (1 : Matrix m m ℝ)
  let e := fun γ => Sum.elim ((penaltyStep A B γ f g).1 - xStar)
    ((penaltyStep A B γ f g).2 - yStar)
  have hM : IsUnit M := by
    have hBker : LinearMap.ker Bᵀ.mulVecLin = ⊥ :=
      LinearMap.ker_eq_bot.mpr hB
    simpa only [M, neg_zero] using
      (isUnit_fromBlocks_transpose_neg_iff B hA (C := 0) PosSemidef.zero).mpr
        ⟨hker, by rw [hBker, inf_bot_eq]⟩
  have he : ∀ᶠ γ in atTop, (M - γ⁻¹ • D) *ᵥ e γ = γ⁻¹ • Sum.elim (0 : n → ℝ) yStar := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
    have hreg : M - γ⁻¹ • D = fromBlocks A Bᵀ B (-(γ⁻¹ • 1)) := by
      ext (row | row) (col | col) <;> simp [M, D]
    rw [hreg]
    exact saddlePenalty_error_mulVec A B γ⁻¹ _ _ _ _ _ _ hsol
      (penaltyStep_regularized A B hA hker hγ f g)
  exact ⟨isBigO_saddlePenalty_error M D hM _ e he (euclideanRestriction Sum.inl),
    isBigO_saddlePenalty_error M D hM _ e he (euclideanRestriction Sum.inr)⟩

omit [DecidableEq m] in
/-- **Section 8.2** of [benzi2005numerical], penalty limit. Under the positive semidefinite,
full-row-rank and trivial common kernel assumptions, the pair of penalty approximations
converges to the saddle solution as $\gamma\to+\infty$. -/
theorem penalty_tendsto (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    (f xStar : n → ℝ) (g yStar : m → ℝ)
    (hsol : A *ᵥ xStar + Bᵀ *ᵥ yStar = f ∧ B *ᵥ xStar = g) :
    Tendsto (fun γ => WithLp.toLp 2 (penaltyStep A B γ f g).1) atTop (𝓝 (WithLp.toLp 2 xStar)) ∧
    Tendsto (fun γ => WithLp.toLp 2 (penaltyStep A B γ f g).2) atTop (𝓝 (WithLp.toLp 2 yStar)) := by
  have herr := penalty_error A B hA hB hker f xStar g yStar hsol
  exact ⟨tendsto_sub_nhds_zero_iff.mp (herr.1.trans_tendsto tendsto_inv_atTop_zero),
    tendsto_sub_nhds_zero_iff.mp (herr.2.trans_tendsto tendsto_inv_atTop_zero)⟩

/-- **Equation (8.12)** of [benzi2005numerical]. The **augmented Lagrangian** is
$\mathcal{L}(x,y)=J(x)+(Bx-g)^Ty+\frac{\gamma}{2}\|Bx-g\|_2^2$. -/
noncomputable abbrev augmentedLagrangian (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f x : n → ℝ) (g y : m → ℝ) : ℝ := saddleAugmentedLagrangian A B γ f x g y

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (8.13)** of [benzi2005numerical]. If $A$ is positive semidefinite,
$\ker A\cap\ker B=\{0\}$ and $\gamma>0$, then minimizing the augmented Lagrangian over $x$
at fixed $y$ is equivalent to solving $(A+\gamma B^TB)x=f-B^Ty+\gamma B^Tg$. -/
theorem augmentedLagrangian_minimizer (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) (f x : n → ℝ) (g y : m → ℝ) :
    IsLeast (Set.range fun z => augmentedLagrangian A B γ f z g y)
      (augmentedLagrangian A B γ f x g y) ↔
      saddleAugmentedPrimal A B γ *ᵥ x = saddleAugmentedRhs B γ f g - Bᵀ *ᵥ y :=
  isLeast_saddleAugmentedLagrangian_iff A B γ f x g y (posDef_saddleAugmentedPrimal B hA hker hγ)

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (8.10)** of [benzi2005numerical], minimization. For positive $\gamma$,
positive semidefinite $A$ and $\ker A\cap\ker B=\{0\}$, a vector minimizes the penalty
objective if and only if it solves $(A+\gamma B^TB)x=f+\gamma B^Tg$. -/
theorem penaltyObjective_minimizer (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) (f x : n → ℝ) (g : m → ℝ) :
    IsLeast (Set.range fun z => penaltyObjective A B γ f z g) (penaltyObjective A B γ f x g) ↔
      saddleAugmentedPrimal A B γ *ᵥ x = saddleAugmentedRhs B γ f g := by
  simpa [penaltyObjective] using augmentedLagrangian_minimizer A B hA hker hγ f x g 0

/-- **Equations (8.13) and (8.14)** of [benzi2005numerical]. One **method-of-multipliers step**
uses Uzawa with relaxation $\gamma$, primal matrix $A+\gamma B^TB$ and right-hand side
$f+\gamma B^Tg$. -/
noncomputable def multiplierStep (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f : n → ℝ) (g y : m → ℝ) : (n → ℝ) × (m → ℝ) :=
  uzawaStep (saddleAugmentedPrimal A B γ) B γ (saddleAugmentedRhs B γ f g) g y

omit [DecidableEq n] [DecidableEq m] in
/-- **Equation (8.14)** of [benzi2005numerical]. The augmented system with primal block
$A+\gamma B^TB$ and primal right-hand side $f+\gamma B^Tg$ has exactly the same solutions as
the original system. -/
theorem multiplier_system_iff (A : Matrix n n ℝ) (B : Matrix m n ℝ) (γ : ℝ)
    (f x : n → ℝ) (g y : m → ℝ) :
    (saddleAugmentedPrimal A B γ *ᵥ x + Bᵀ *ᵥ y = saddleAugmentedRhs B γ f g ∧ B *ᵥ x = g) ↔
      (A *ᵥ x + Bᵀ *ᵥ y = f ∧ B *ᵥ x = g) :=
  saddleAugmented_equations_iff A B γ f x g y

/-- **Section 8.2** of [benzi2005numerical], convergence of the method of multipliers.
If $A$ is symmetric positive semidefinite, $B$ has at least one row and full row rank, and
$\ker A\cap\ker B=\{0\}$,
then for every $\gamma>0$ the reduced iteration matrix
$I-\gamma B(A+\gamma B^TB)^{-1}B^T$ has spectral radius less than one.

The eigenvalues $\lambda$ of the augmented Schur complement satisfy $0<\gamma\lambda\le1$;
in particular the parameter satisfies the Richardson bound stated in the text. -/
theorem multiplier_convergence [Nonempty m] (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) :
    complexSpectralRadius (1 - γ • (B * (saddleAugmentedPrimal A B γ)⁻¹ * Bᵀ)) < 1 := by
  let P := saddleAugmentedPrimal A B γ
  let S := B * P⁻¹ * Bᵀ
  have hP := posDef_saddleAugmentedPrimal B hA hker hγ
  have hS := uzawa_schur_posDef B hP hB
  have hspectrum : spectrum ℂ (complexify (1 - γ • S)) =
      (fun mu : ℂ => 1 + ((-γ : ℝ) : ℂ) * mu) '' spectrum ℂ (complexify S) := by
    simpa only [one_smul, neg_smul, sub_eq_add_neg, Complex.ofReal_one] using
      spectrum_complexify_affine S (c := 1) (neg_ne_zero.mpr hγ.ne')
  change complexSpectralRadius (1 - γ • S) < 1
  rw [complexSpectralRadius_lt_one_iff_forall_norm_lt, hspectrum]
  rintro _ ⟨μ, hμ, rfl⟩
  have hμreal := hμ
  rw [((isHermitian_complexify_iff _).mpr hS.isHermitian).spectrum_eq_image_range] at hμreal
  obtain ⟨lam, -, rfl⟩ := hμreal
  have hlam := (ofReal_mem_spectrum_complexify_iff S lam).mp hμ
  obtain ⟨index, hindex⟩ := (hS.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hlam)
  have hp : 0 < lam := hindex ▸ hS.eigenvalues_pos index
  obtain ⟨v, hv, he⟩ := (mem_spectrum_iff_exists_mulVec_eq_smul S lam).mp hlam
  have hb := mul_le_one_of_saddleAugmentedSchur_eigenvector B hA γ hP.isUnit hp hv he
  change ‖(1 : ℂ) + ((-γ : ℝ) : ℂ) * (lam : ℂ)‖ < 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, neg_mul, ← sub_eq_add_neg, abs_of_nonneg (sub_nonneg.mpr hb)]
  linarith [mul_pos hγ hp]

omit [DecidableEq m] in
/-- **Section 8.2** of [benzi2005numerical], convergence to the original saddle solution.
Suppose $A$ is positive semidefinite, $B$ has full row rank and at least one row, and
$\ker A\cap\ker B=\{0\}$. Iterating from any initial pair converges to the solution of the
original saddle equations for every $\gamma>0$. -/
theorem multiplier_tendsto [Nonempty m] (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥)
    {γ : ℝ} (hγ : 0 < γ) (f : n → ℝ) (g : m → ℝ) (initial sol : (n → ℝ) × (m → ℝ))
    (hf : A *ᵥ sol.1 + Bᵀ *ᵥ sol.2 = f) (hg : B *ᵥ sol.1 = g) :
    let update := fun state : (n → ℝ) × (m → ℝ) => multiplierStep A B γ f g state.2
    let join := fun state : (n → ℝ) × (m → ℝ) => Sum.elim state.1 state.2
    Tendsto (fun k => join (update^[k] initial)) atTop (𝓝 (join sol)) := by
  classical
  have hP := posDef_saddleAugmentedPrimal B hA hker hγ
  have hsol := (multiplier_system_iff A B γ f sol.1 g sol.2).mpr ⟨hf, hg⟩
  exact uzawa_tendsto_of_spectralRadius_lt_one _ B hP.isUnit hγ.ne'
    (multiplier_convergence A B hA hB hker hγ) _ g initial sol hsol.1 hsol.2

/-- **Section 8.2** of [benzi2005numerical], large-penalty limit. If $A$ is positive
semidefinite, $B$ has full row rank and $\ker A\cap\ker B=\{0\}$, the reduced multiplier
iteration matrix $I-\gamma B(A+\gamma B^TB)^{-1}B^T$ tends to zero entrywise. -/
theorem multiplier_iterationMatrix_tendsto_zero (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    Tendsto (fun γ => 1 - γ • (B * (saddleAugmentedPrimal A B γ)⁻¹ * Bᵀ))
      atTop (𝓝 (0 : Matrix m m ℝ)) := by
  let S := fun γ => B * (saddleAugmentedPrimal A B γ)⁻¹ * Bᵀ
  let G := fun γ => 1 - γ • S γ
  have hcol (col : m) : Tendsto (fun γ => G γ *ᵥ Pi.single col 1) atTop (𝓝 (0 : m → ℝ)) := by
    let z : m → ℝ := Pi.single col 1
    have hsol : A *ᵥ (0 : n → ℝ) + Bᵀ *ᵥ z = Bᵀ *ᵥ z ∧ B *ᵥ (0 : n → ℝ) = 0 := by simp
    have hpen := (penalty_tendsto A B hA hB hker (Bᵀ *ᵥ z) 0 0 z hsol).2
    have hconv := ((PiLp.continuous_ofLp 2 (fun _ : m => ℝ)).tendsto _).comp hpen
    have heq (γ : ℝ) : (penaltyStep A B γ (Bᵀ *ᵥ z) 0).2 = γ • (S γ *ᵥ z) := by
      simp [penaltyStep, saddlePenaltyMultiplier, saddleAugmentedRhs, S, Matrix.mul_assoc]
    simp only [Function.comp_def, heq] at hconv
    simpa only [G, z, sub_mulVec, one_mulVec, smul_mulVec, sub_self] using
      (tendsto_const_nhds (x := z)).sub hconv
  refine tendsto_pi_nhds.mpr fun row => tendsto_pi_nhds.mpr fun col => ?_
  have h := ((continuous_apply row).tendsto (0 : m → ℝ)).comp (hcol col)
  change Tendsto (fun γ => G γ row col) atTop (𝓝 (0 : ℝ))
  simpa only [Function.comp_def, mulVec_single_one, col_apply, Pi.zero_apply] using h

open scoped Matrix.Norms.L2Operator in
/-- **Section 8.2** of [benzi2005numerical], asymptotic convergence factor. If $A$ is positive
semidefinite, $B$ has full row rank and $\ker A\cap\ker B=\{0\}$, the spectral radius of the
reduced multiplier iteration tends to zero as $\gamma\to+\infty$. -/
theorem multiplier_spectralRadius_tendsto_zero (A : Matrix n n ℝ) (B : Matrix m n ℝ)
    (hA : A.PosSemidef) (hB : Function.Injective Bᵀ.mulVec)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    Tendsto (fun γ => (complexSpectralRadius
      (1 - γ • (B * (saddleAugmentedPrimal A B γ)⁻¹ * Bᵀ))).toReal) atTop (𝓝 0) := by
  have h := (multiplier_iterationMatrix_tendsto_zero A B hA hB hker).norm
  rw [norm_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
  have hS := uzawa_schur_posDef B (posDef_saddleAugmentedPrimal B hA hker hγ) hB
  exact l2_opNorm_eq_complexSpectralRadius_of_isHermitian
    (isHermitian_one.sub (hS.isHermitian.smul (show IsSelfAdjoint γ from rfl)))

end BenziGolubLiesen
