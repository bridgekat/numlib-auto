import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Circulant
import Numlib.Analysis.Fourier.Circulant
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.FiniteDifference.Stencil

/-!
# Von Neumann stability analysis on the periodic grid

A constant-coefficient explicit two-level scheme on the periodic grid of `N` nodes is the
circulant matrix `Matrix.circulant c` of its stencil (`FiniteDifference.periodicScheme`). The
discrete Fourier modes `j ↦ ω^{jk}`, the columns of `Matrix.dft N`, are its common eigenvectors
(`FiniteDifference.fourierMode`), with eigenvalues the **amplification factors** `γ_k = ∑_s c s
ω^{-sk}`, the discrete Fourier transform of the stencil (`FiniteDifference.amplificationFactor`,
`FiniteDifference.periodicScheme_mulVec_fourierMode`). Iterating,
`Qⁿ e_k = γ_kⁿ e_k` ([quarteroni2000numerical] (13.52)). This is the diagonalization of circulant
matrices of `Numlib.Analysis.Fourier.Circulant` in the convention whose eigenvectors are the
columns of `dft N` (`Matrix.circulant_mulVec_dft_col`), the complex conjugate of the textbook
convention of numerical linear algebra.

**The `ℓ²` norm of the powers.** Any matrix `A` with `A e_k = γ_k e_k` for every mode is
`N⁻¹ F diag(γ) Fᴴ` (`FiniteDifference.eq_dft_mul_diagonal_of_forall_mulVec_fourierMode`), and the
discrete Parseval identity `‖Fᴴ y‖² = N ‖y‖²`
(`FiniteDifference.sum_normSq_conjTranspose_dft_mulVec`, the orthogonality `Fᴴ F = N` of
[quarteroni2000numerical] Lemma 10.1) then gives `‖A u‖₂ ≤ (max_k |γ_k|) ‖u‖₂`
(`FiniteDifference.norm_toEuclideanLin_le_of_forall_mulVec_fourierMode`), with equality attained on
the modes (`FiniteDifference.norm_amplificationFactor_pow_le`). Hence the two halves of the
classical criterion:

* **Von Neumann's sufficient condition** ([quarteroni2000numerical] Theorem 13.1): `|γ_k| ≤ 1` for
  all `k` gives `‖Qⁿ u‖₂ ≤ ‖u‖₂` for every `n` — stability in `‖·‖_{Δ,2}` with constant `1`
  (`FiniteDifference.norm_toEuclideanLin_periodicScheme_pow_le`);
* **the necessary condition**: stability over a horizon `T`, `‖Qⁿ‖ ≤ C` for `n Δt ≤ T`, forces
  `|γ_k| ≤ 1 + 2 (C - 1) Δt / T`
  (`FiniteDifference.norm_amplificationFactor_le_one_add_of_forall_norm_pow_le`, Bernoulli's
  inequality) — the argument by which [quarteroni2000numerical] §13.8.4 conclude that the forward
  Euler/centred scheme, whose factors satisfy `|γ_k| > 1` independently of the mesh, is
  unconditionally unstable.

**Implicit and multi-level schemes.** The two-level scheme `B u^{n+1} = C u^n` with circulant `B`
and `C` is `B⁻¹ C` (`FiniteDifference.periodicTwoLevel`), whose amplification factors are the
quotients `γ^C_k / γ^B_k` (`FiniteDifference.periodicTwoLevel_mulVec_fourierMode`); the norm results
above apply verbatim, since they are stated for any matrix with the modes as eigenvectors. A
multi-level scheme is a two-level scheme for a vector of unknowns; its periodic form is the block
circulant `FiniteDifference.periodicBlockScheme`, diagonalized modewise into the `m × m`
amplification matrices `G_k = ∑_s ω^{-sk} G_s` (`FiniteDifference.amplificationMatrix`,
`FiniteDifference.periodicBlockScheme_pow_mulVec_fourierMode`).

**From the line to the circle.** A stencil `c : ℤ →₀ ℝ` of `Numlib.FiniteDifference.Stencil` wraps
onto the periodic grid as `Stencil.toPeriodic N c`; the periodic scheme agrees with the stencil on
`N`-periodic grid functions (`Stencil.periodicScheme_toPeriodic_mulVec`), and its amplification
factors are the symbol sampled at `φ_k = 2πk/N`
(`Stencil.amplificationFactor_toPeriodic_eq_symbol`); for a three-point stencil,
`γ_k = c0 + cm e^{-iφ_k} + cp e^{iφ_k}` (`Stencil.amplificationFactor_toPeriodic_threePoint`), the
formula behind every entry of the stability column of [quarteroni2000numerical] Table 13.1.
-/

open Complex Matrix Finset
open scoped Real Fin.IntCast Fin.CommRing

namespace FiniteDifference

variable {N : ℕ}

/-- A grid point `j : Fin N` witnesses `N ≠ 0`, which is what the group structure of `Fin N`
needs. -/
private theorem neZero_of_fin (j : Fin N) : NeZero N := ⟨fun h => (h ▸ j).elim0⟩

/-! ### The periodic scheme, the Fourier modes and the amplification factors -/

/-- **The explicit constant-coefficient scheme on the periodic grid** `Fin N` with stencil `c`:
the circulant matrix `(Q u) j = ∑ s, c s * u (j - s)` (subtraction in `Fin N`). -/
noncomputable abbrev periodicScheme (c : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.circulant c

/-- The action of the periodic scheme: `(Q u) j = ∑ s, c s * u (j - s)`. -/
theorem periodicScheme_mulVec_apply (c : Fin N → ℂ) (u : Fin N → ℂ) (j : Fin N) :
    (periodicScheme c *ᵥ u) j = ∑ s, c s * u (j - s) := by
  have := neZero_of_fin j
  rw [mulVec, dotProduct]
  simp only [circulant_apply]
  exact (Equiv.sum_comp (Equiv.subLeft j) fun l => c (j - l) * u l).symm.trans
    (Finset.sum_congr rfl fun s _ => by simp)

/-- **The `k`-th Fourier mode** on the grid of `N` points, `j ↦ ω^{jk}` with `ω = exp (2πi/N)`:
the grid values `e^{ikjh}`, `h = 2π/N`, of the `k`-th harmonic; the `k`-th column of `Matrix.dft N`.
-/
noncomputable def fourierMode (N : ℕ) (k : Fin N) : Fin N → ℂ := fun j => Matrix.dft N j k

/-- The entries of a Fourier mode: `e_k j = ω^{jk}`. -/
theorem fourierMode_apply (k j : Fin N) :
    fourierMode N k j = Complex.exp (2 * π * I / N) ^ ((j : ℕ) * (k : ℕ)) := rfl

/-- **The amplification factor** of the `k`-th mode under the scheme with stencil `c`:
`γ_k = ∑ s, c s ω^{-sk}`, the discrete Fourier transform of the stencil at `k`. -/
noncomputable def amplificationFactor (c : Fin N → ℂ) (k : Fin N) : ℂ :=
  ((Matrix.dft N)ᴴ *ᵥ c) k

/-- The amplification factor as an explicit sum: `γ_k = ∑ s, ω^{-sk} c s`. -/
theorem amplificationFactor_eq_sum (c : Fin N → ℂ) (k : Fin N) :
    amplificationFactor c k
      = ∑ s : Fin N, (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * (k : ℕ)) * c s :=
  Matrix.conjTranspose_dft_mulVec_apply c k

/-- A Fourier mode evaluated at a difference of grid points: `e_k (j - s) = e_k j ω^{-sk}`. -/
theorem fourierMode_sub (k j s : Fin N) :
    fourierMode N k (j - s)
      = fourierMode N k j * (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * k) := by
  rw [fourierMode, fourierMode, Matrix.dft_apply_sub, conjTranspose_dft_apply, Nat.mul_comm]

/-- **The Fourier modes are eigenvectors of every circulant scheme**, with eigenvalues the
amplification factors: `Q e_k = γ_k e_k` ([quarteroni2000numerical] (13.52) at one step). -/
theorem periodicScheme_mulVec_fourierMode (c : Fin N → ℂ) (k : Fin N) :
    periodicScheme c *ᵥ fourierMode N k = amplificationFactor c k • fourierMode N k :=
  Matrix.circulant_mulVec_dft_col c k

/-- `Qⁿ e_k = γ_kⁿ e_k` ([quarteroni2000numerical] (13.52)): the recursion on one harmonic. -/
theorem periodicScheme_pow_mulVec_fourierMode (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    (periodicScheme c ^ n) *ᵥ fourierMode N k
      = amplificationFactor c k ^ n • fourierMode N k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, periodicScheme_mulVec_fourierMode,
      smul_smul, pow_succ]

/-! ### Spectral decomposition and discrete Parseval -/

/-- A matrix having every Fourier mode as an eigenvector, `A e_k = γ_k e_k`, satisfies
`A F = F diag(γ)`. -/
theorem mul_dft_eq_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ} {γ : Fin N → ℂ}
    (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) :
    A * Matrix.dft N = Matrix.dft N * diagonal γ :=
  Matrix.mul_eq_mul_diagonal_of_forall_mulVec_col hA

/-- **Spectral decomposition through the discrete Fourier transform**: a matrix with every Fourier
mode as an eigenvector, `A e_k = γ_k e_k`, is `N⁻¹ F diag(γ) Fᴴ`. -/
theorem eq_dft_mul_diagonal_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) :
    A = (N : ℂ)⁻¹ • (Matrix.dft N * diagonal γ * (Matrix.dft N)ᴴ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Subsingleton.elim _ _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← mul_dft_eq_of_forall_mulVec_fourierMode hA, Matrix.mul_assoc,
    Matrix.dft_mul_conjTranspose_dft, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ hN', one_smul]

/-- **Spectral decomposition of a circulant**: `Q = N⁻¹ F diag(γ) Fᴴ`, with `γ` the amplification
factors. -/
theorem periodicScheme_eq_dft_mul_diagonal (c : Fin N → ℂ) :
    periodicScheme c
      = (N : ℂ)⁻¹ • (Matrix.dft N * diagonal (amplificationFactor c) * (Matrix.dft N)ᴴ) :=
  Matrix.circulant_eq_dft_mul_diagonal_mul_conjTranspose_dft c

/-- Parseval for a matrix with orthogonal columns: `Mᴴ M = N • 1` gives
`∑ k, ‖(M y) k‖² = N ∑ j, ‖y j‖²`. -/
theorem sum_normSq_mulVec_of_conjTranspose_mul {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : Mᴴ * M = (N : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (y : Fin N → ℂ) :
    ∑ k, ‖(M *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 := by
  have h : star (M *ᵥ y) ⬝ᵥ (M *ᵥ y) = (N : ℂ) * (star y ⬝ᵥ y) := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_smul, vecMul_one, smul_dotProduct,
      smul_eq_mul]
  have h' : ∀ z : Fin N → ℂ, star z ⬝ᵥ z = ∑ k, ((‖z k‖ ^ 2 : ℝ) : ℂ) := fun z => by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  rw [h', h', ← Complex.ofReal_sum, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- **Discrete Parseval** ([quarteroni2000numerical] Lemma 10.1 in norm form):
`∑ k, ‖(Fᴴ y) k‖² = N ∑ j, ‖y j‖²`. -/
theorem sum_normSq_conjTranspose_dft_mulVec (y : Fin N → ℂ) :
    ∑ k, ‖((Matrix.dft N)ᴴ *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 :=
  sum_normSq_mulVec_of_conjTranspose_mul
    (by rw [conjTranspose_conjTranspose, Matrix.dft_mul_conjTranspose_dft]) y

/-- **Discrete Parseval** for the inverse transform: `∑ k, ‖(F y) k‖² = N ∑ j, ‖y j‖²`. -/
theorem sum_normSq_dft_mulVec (y : Fin N → ℂ) :
    ∑ k, ‖(Matrix.dft N *ᵥ y) k‖ ^ 2 = N * ∑ j, ‖y j‖ ^ 2 :=
  sum_normSq_mulVec_of_conjTranspose_mul (Matrix.conjTranspose_dft_mul_dft N) y

/-- The Euclidean norm of `Fᴴ y` is `√N ‖y‖`. -/
theorem norm_toEuclideanLin_conjTranspose_dft (y : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (Matrix.dft N)ᴴ y‖ = √N * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N),
    ← sum_normSq_conjTranspose_dft_mulVec]
  rfl

/-- The Euclidean norm of `F y` is `√N ‖y‖`. -/
theorem norm_toEuclideanLin_dft (y : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (Matrix.dft N) y‖ = √N * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N),
    ← sum_normSq_dft_mulVec]
  rfl

/-- A diagonal matrix with entries of modulus at most `ρ` is bounded by `ρ` in the Euclidean norm.
-/
theorem norm_toEuclideanLin_diagonal_le {γ : Fin N → ℂ} {ρ : ℝ} (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ)
    (y : EuclideanSpace ℂ (Fin N)) : ‖toEuclideanLin (diagonal γ) y‖ ≤ ρ * ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ,
    ← Real.sqrt_mul (sq_nonneg ρ), Finset.mul_sum]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  rw [toEuclideanLin_apply, WithLp.ofLp_toLp, mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hγ k) 2) (sq_nonneg _)

/-! ### The `ℓ²` norm of the powers -/

/-- **The `ℓ²` bound through the eigenvalues on the Fourier modes**: if `A e_k = γ_k e_k` for every
mode and `‖γ_k‖ ≤ ρ`, then `‖A u‖₂ ≤ ρ ‖u‖₂`. Through the decomposition `A = N⁻¹ F diag(γ) Fᴴ`
and Parseval twice: `‖A u‖ = N⁻¹ √N ‖diag(γ) (Fᴴ u)‖ ≤ N⁻¹ √N ρ √N ‖u‖`. -/
theorem norm_toEuclideanLin_le_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {ρ : ℝ}
    (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin A u‖ ≤ ρ * ‖u‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Subsingleton.elim u 0]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [eq_dft_mul_diagonal_of_forall_mulVec_fourierMode hA, toEuclideanLin_smul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, norm_smul, norm_toEuclideanLin_dft,
    norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * (√N * ‖toEuclideanLin (diagonal γ) (toEuclideanLin (Matrix.dft N)ᴴ u)‖)
      ≤ (N : ℝ)⁻¹ * (√N * (ρ * ‖toEuclideanLin (Matrix.dft N)ᴴ u‖)) := by
        gcongr
        exact norm_toEuclideanLin_diagonal_le hγ hρ _
    _ = (N : ℝ)⁻¹ * (√N * (ρ * (√N * ‖u‖))) := by rw [norm_toEuclideanLin_conjTranspose_dft]
    _ = ρ * ‖u‖ := by
        have : √(N : ℝ) * √N = N := Real.mul_self_sqrt hN'.le
        field_simp
        linear_combination ρ * ‖u‖ * this

/-- Powers preserve the eigenvector relation: `Aⁿ e_k = γ_kⁿ e_k`. -/
theorem pow_mulVec_fourierMode_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) (n : ℕ) (k : Fin N) :
    (A ^ n) *ᵥ fourierMode N k = γ k ^ n • fourierMode N k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hA, smul_smul, pow_succ]

/-- **The `ℓ²` norm of the powers** of a matrix with the Fourier modes as eigenvectors:
`‖Aⁿ u‖₂ ≤ ρⁿ ‖u‖₂` when `‖γ_k‖ ≤ ρ` for every mode. -/
theorem norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {ρ : ℝ}
    (hγ : ∀ k, ‖γ k‖ ≤ ρ) (hρ : 0 ≤ ρ) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (A ^ n) u‖ ≤ ρ ^ n * ‖u‖ :=
  norm_toEuclideanLin_le_of_forall_mulVec_fourierMode
    (pow_mulVec_fourierMode_of_forall_mulVec_fourierMode hA n)
    (fun k => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hγ k) n) (by positivity) u

/-- `‖Qⁿ u‖₂ ≤ ρⁿ ‖u‖₂` whenever every amplification factor has modulus at most `ρ`. -/
theorem norm_toEuclideanLin_periodicScheme_pow (c : Fin N → ℂ) (n : ℕ) {ρ : ℝ}
    (hρ : ∀ k, ‖amplificationFactor c k‖ ≤ ρ) (hρ0 : 0 ≤ ρ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicScheme c ^ n) u‖ ≤ ρ ^ n * ‖u‖ :=
  norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    hρ hρ0 n u

/-- **Von Neumann's sufficient condition** ([quarteroni2000numerical] Theorem 13.1): if
`|γ_k| ≤ 1` for every `k`, the scheme is stable in `‖·‖_{Δ,2}` with constant `1` and for every
number of steps, `‖Qⁿ u‖₂ ≤ ‖u‖₂`. -/
theorem norm_toEuclideanLin_periodicScheme_pow_le (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor c k‖ ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicScheme c ^ n) u‖ ≤ ‖u‖ := by
  simpa using norm_toEuclideanLin_periodicScheme_pow c n h zero_le_one u

/-- The operator-norm form of von Neumann's sufficient condition: `‖Qⁿ‖₂ ≤ 1` when `|γ_k| ≤ 1` for
every `k`. -/
theorem norm_toEuclideanCLM_periodicScheme_pow_le (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor c k‖ ≤ 1) (n : ℕ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]; exact norm_toEuclideanLin_periodicScheme_pow_le c h n u

/-- A Fourier mode is not the zero vector (its value at `j = 0` is `1`). -/
theorem fourierMode_ne_zero (k : Fin N) : fourierMode N k ≠ 0 := fun h => by
  have := congrFun h ⟨0, k.pos⟩
  simp [fourierMode_apply] at this

/-- **The eigenvalues bound the operator norm from below**: `‖γ_k‖ⁿ ≤ ‖Aⁿ‖₂` for any matrix with
`A e_k = γ_k e_k`, by testing `Aⁿ` on the mode `e_k`. -/
theorem norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) (k : Fin N) (n : ℕ) :
    ‖γ k‖ ^ n ≤ ‖toEuclideanCLM (𝕜 := ℂ) (A ^ n)‖ := by
  have hek : (WithLp.toLp 2 (fourierMode N k) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro h
    exact fourierMode_ne_zero k (by simpa using congrArg WithLp.ofLp h)
  have h := (toEuclideanCLM (𝕜 := ℂ) (A ^ n)).le_opNorm (WithLp.toLp 2 (fourierMode N k))
  rw [toEuclideanCLM_toLp, pow_mulVec_fourierMode_of_forall_mulVec_fourierMode hA, WithLp.toLp_smul,
    norm_smul, norm_pow] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hek)

/-- **The amplification factors bound the norm of the powers from below**: `‖γ_k‖ⁿ ≤ ‖Qⁿ‖₂`. -/
theorem norm_amplificationFactor_pow_le (c : Fin N → ℂ) (k : Fin N) (n : ℕ) :
    ‖amplificationFactor c k‖ ^ n ≤ ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ :=
  norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    k n

/-- **Von Neumann's necessary condition**: if `‖Aⁿ‖₂ ≤ C` for every `n` with `n Δt ≤ T`, where
`1 ≤ C`, `0 < Δt ≤ T/2` and `A e_k = γ_k e_k`, then `‖γ_k‖ ≤ 1 + 2 (C - 1) Δt / T`. With
`n = ⌊T/Δt⌋ ≥ 1`, `‖γ_k‖ⁿ ≤ C ≤ (1 + (C - 1)/n)ⁿ` by Bernoulli's inequality, and `1/n ≤ 2Δt/T`. -/
theorem norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode {A : Matrix (Fin N) (Fin N) ℂ}
    {γ : Fin N → ℂ} (hA : ∀ k, A *ᵥ fourierMode N k = γ k • fourierMode N k) {C Δt T : ℝ}
    (hC : 1 ≤ C) (hΔt : 0 < Δt) (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖toEuclideanCLM (𝕜 := ℂ) (A ^ n)‖ ≤ C) (k : Fin N) :
    ‖γ k‖ ≤ 1 + 2 * (C - 1) * Δt / T := by
  have hT : 0 < T := by linarith
  set n : ℕ := ⌊T / Δt⌋₊ with hn
  have hx : (2 : ℝ) ≤ T / Δt := by rw [le_div_iff₀ hΔt]; linarith
  have hn2 : (2 : ℝ) ≤ n := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ T / Δt)
    have h2 : (2 : ℕ) ≤ n := Nat.le_floor hx
    exact_mod_cast h2
  have hn0 : n ≠ 0 := by
    intro h; rw [h] at hn2; norm_num at hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hnT : (n : ℝ) * Δt ≤ T := by
    rw [← le_div_iff₀ hΔt]; exact Nat.floor_le (by positivity)
  have hbound : ‖γ k‖ ^ n ≤ C :=
    (norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode hA k n).trans (hstab n hnT)
  -- Bernoulli: `C ≤ (1 + (C - 1)/n)^n`
  have hbern : C ≤ (1 + (C - 1) / n) ^ n := by
    have := one_add_mul_le_pow (a := (C - 1) / n) (by
      have : 0 ≤ (C - 1) / n := by positivity
      linarith) n
    rwa [mul_div_cancel₀ _ hnpos.ne', add_sub_cancel] at this
  have hle : ‖γ k‖ ≤ 1 + (C - 1) / n :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hn0).1 (hbound.trans hbern)
  -- `1/n ≤ 2 Δt / T`, since `n ≥ T/Δt - 1 ≥ T/(2 Δt)`
  have hfloor : T / Δt - 1 ≤ n := by
    have h := Nat.lt_floor_add_one (T / Δt)
    rw [← hn] at h
    linarith
  have hhalf : T / (2 * Δt) ≤ n := by
    have : T / (2 * Δt) ≤ T / Δt - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : T / Δt * Δt = T := div_mul_cancel₀ T hΔt.ne'
      nlinarith
    linarith
  have hinv : (C - 1) / n ≤ 2 * (C - 1) * Δt / T := by
    rw [div_le_div_iff₀ hnpos hT]
    have h1 : T ≤ n * (2 * Δt) := by
      rw [div_le_iff₀ (by positivity)] at hhalf; linarith
    nlinarith
  linarith

/-- **Von Neumann's necessary condition** for the periodic scheme: stability over a horizon `T`,
`‖Qⁿ‖₂ ≤ C` for `n Δt ≤ T`, forces `‖γ_k‖ ≤ 1 + 2 (C - 1) Δt / T` for every amplification
factor. A mode with `‖γ_k‖ ≥ 1 + ε` independently of the mesh therefore makes the family
unstable, which is how [quarteroni2000numerical] §13.8.4 conclude that the forward Euler/centred
scheme is unconditionally unstable. -/
theorem norm_amplificationFactor_le_one_add_of_forall_norm_pow_le (c : Fin N → ℂ) {C Δt T : ℝ}
    (hC : 1 ≤ C) (hΔt : 0 < Δt) (hΔT : Δt ≤ T / 2)
    (hstab : ∀ n : ℕ, (n : ℝ) * Δt ≤ T → ‖toEuclideanCLM (𝕜 := ℂ) (periodicScheme c ^ n)‖ ≤ C)
    (k : Fin N) : ‖amplificationFactor c k‖ ≤ 1 + 2 * (C - 1) * Δt / T :=
  norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode (periodicScheme_mulVec_fourierMode c)
    hC hΔt hΔT hstab k

/-! ### Implicit two-level schemes -/

/-- **The implicit two-level scheme** `B u^{n+1} = C u^n` with circulant `B = circulant b` and
`C = circulant c`: the solution operator `B⁻¹ C`. -/
noncomputable def periodicTwoLevel (b c : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (periodicScheme b)⁻¹ * periodicScheme c

/-- The amplification factors of the implicit two-level scheme: the quotients `γ^C_k / γ^B_k`. -/
noncomputable def amplificationFactor₂ (b c : Fin N → ℂ) (k : Fin N) : ℂ :=
  amplificationFactor c k / amplificationFactor b k

/-- A circulant whose amplification factors all differ from zero is invertible. -/
theorem isUnit_periodicScheme_of_forall_ne_zero {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) : IsUnit (periodicScheme b) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact isUnit_of_subsingleton _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [periodicScheme_eq_dft_mul_diagonal]
  have hF : IsUnit (Matrix.dft N) :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse (by
      rw [Matrix.mul_smul, Matrix.dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hN',
        one_smul] : Matrix.dft N * ((N : ℂ)⁻¹ • (Matrix.dft N)ᴴ) = 1))
  have hFH : IsUnit (Matrix.dft N)ᴴ :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (by
      rw [Matrix.smul_mul, Matrix.dft_mul_conjTranspose_dft, smul_smul, inv_mul_cancel₀ hN',
        one_smul] : ((N : ℂ)⁻¹ • Matrix.dft N) * (Matrix.dft N)ᴴ = 1))
  have hD : IsUnit (diagonal (amplificationFactor b)) := by
    rw [isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hb k
  have hprod := (isUnit_iff_isUnit_det _).1 ((hF.mul hD).mul hFH)
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hN')) (isUnit_iff_ne_zero.1 hprod)

/-- The inverse of a circulant with nonzero amplification factors has the Fourier modes as
eigenvectors, with the reciprocal factors. -/
theorem inv_periodicScheme_mulVec_fourierMode {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (k : Fin N) :
    (periodicScheme b)⁻¹ *ᵥ fourierMode N k = (amplificationFactor b k)⁻¹ • fourierMode N k := by
  have hu := isUnit_periodicScheme_of_forall_ne_zero hb
  have hdet : IsUnit (periodicScheme b).det := (isUnit_iff_isUnit_det _).1 hu
  have h2 : fourierMode N k
      = amplificationFactor b k • ((periodicScheme b)⁻¹ *ᵥ fourierMode N k) :=
    calc fourierMode N k = ((periodicScheme b)⁻¹ * periodicScheme b) *ᵥ fourierMode N k := by
          rw [nonsing_inv_mul _ hdet, one_mulVec]
      _ = (periodicScheme b)⁻¹ *ᵥ (amplificationFactor b k • fourierMode N k) := by
          rw [← mulVec_mulVec, periodicScheme_mulVec_fourierMode]
      _ = amplificationFactor b k • ((periodicScheme b)⁻¹ *ᵥ fourierMode N k) :=
          mulVec_smul _ _ _
  conv_rhs => rw [h2]
  rw [smul_smul, inv_mul_cancel₀ (hb k), one_smul]

/-- **The Fourier modes are eigenvectors of the implicit two-level scheme**, with the quotient
amplification factors: `B⁻¹ C e_k = (γ^C_k / γ^B_k) e_k` when no `γ^B_k` vanishes. The `ℓ²` bounds
`norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode`,
`norm_pow_le_norm_toEuclideanCLM_pow_of_mulVec_fourierMode` and
`norm_le_one_add_of_forall_norm_pow_le_of_mulVec_fourierMode` then apply to it verbatim. -/
theorem periodicTwoLevel_mulVec_fourierMode {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (c : Fin N → ℂ) (k : Fin N) :
    periodicTwoLevel b c *ᵥ fourierMode N k = amplificationFactor₂ b c k • fourierMode N k := by
  rw [periodicTwoLevel, ← mulVec_mulVec, periodicScheme_mulVec_fourierMode, mulVec_smul,
    inv_periodicScheme_mulVec_fourierMode hb, smul_smul, amplificationFactor₂, div_eq_mul_inv]

/-- Von Neumann's sufficient condition for the implicit two-level scheme: if
`‖γ^C_k / γ^B_k‖ ≤ 1` for every `k` (and no `γ^B_k` vanishes), then `‖(B⁻¹ C)ⁿ u‖₂ ≤ ‖u‖₂`. -/
theorem norm_toEuclideanLin_periodicTwoLevel_pow_le {b : Fin N → ℂ}
    (hb : ∀ k, amplificationFactor b k ≠ 0) (c : Fin N → ℂ)
    (h : ∀ k, ‖amplificationFactor₂ b c k‖ ≤ 1) (n : ℕ) (u : EuclideanSpace ℂ (Fin N)) :
    ‖toEuclideanLin (periodicTwoLevel b c ^ n) u‖ ≤ ‖u‖ := by
  simpa using norm_toEuclideanLin_pow_le_of_forall_mulVec_fourierMode
    (periodicTwoLevel_mulVec_fourierMode hb c) h zero_le_one n u

/-! ### Wrapping a stencil onto the periodic grid -/

namespace Stencil

/-- **A stencil wrapped onto the periodic grid** of `N` points: the weight of `j : Fin N` is the sum
of the weights `c s` over the `s ≡ j (mod N)`. -/
noncomputable def toPeriodic (N : ℕ) [NeZero N] (c : Stencil) : Fin N → ℂ :=
  fun j => ∑ s ∈ c.support, if (s : Fin N) = j then (c s : ℂ) else 0

variable [NeZero N]

/-- **The periodic scheme agrees with the stencil on periodic grid functions**: for `v : Fin N → ℂ`
and its `N`-periodic extension `i ↦ v (i : Fin N)` to `ℤ`,
`(periodicScheme (toPeriodic N c) *ᵥ v) j = (c u) j`. -/
theorem periodicScheme_toPeriodic_mulVec (c : Stencil) (v : Fin N → ℂ) (j : ℤ) :
    (periodicScheme (toPeriodic N c) *ᵥ v) (j : Fin N)
      = apply c (fun i : ℤ => v (i : Fin N)) j := by
  rw [periodicScheme_mulVec_apply, apply_apply]
  simp only [toPeriodic, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.real_smul, Int.cast_sub, Finset.sum_ite_eq Finset.univ (s : Fin N)]
  simp

/-- The natural-number value of the wrap of `s : ℤ` onto `Fin N` is congruent to `s` modulo `N`. -/
private theorem exp_val_intCast (s : ℤ) (k : Fin N) :
    (Complex.exp (2 * π * I / N))⁻¹ ^ (((s : Fin N) : ℕ) * (k : ℕ))
      = Complex.exp (-(I * s * (2 * π * k / N))) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval : (((s : Fin N) : ℕ) : ℤ) = s % N := by
    rw [Fin.val_intCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N))]
  rw [inv_pow, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  have hdiv : s = s % N + N * (s / N) := (Int.emod_add_mul_ediv s N).symm
  have hcast : ((((s : Fin N) : ℕ) * (k : ℕ) : ℕ) : ℂ) = ((s % N : ℤ) : ℂ) * (k : ℕ) := by
    push_cast
    rw [← hval]
    push_cast
    ring
  rw [hcast]
  conv_rhs => rw [hdiv]
  rw [show -(I * ((s % N + N * (s / N) : ℤ) : ℂ) * (2 * π * k / N))
      = -(((s % N : ℤ) : ℂ) * (k : ℕ) * (2 * π * I / N)) + (-(s / N) * k : ℤ) * (2 * π * I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The amplification factors of a wrapped stencil are its symbol sampled at `φ_k = 2πk/N`**:
`amplificationFactor (toPeriodic N c) k = symbol c (2πk/N)`. -/
theorem amplificationFactor_toPeriodic_eq_symbol (c : Stencil) (k : Fin N) :
    amplificationFactor (toPeriodic N c) k = symbol c (2 * π * k / N) := by
  rw [amplificationFactor_eq_sum, symbol]
  simp only [toPeriodic, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (s : Fin N)]
  simp only [Finset.mem_univ, ite_true]
  rw [exp_val_intCast, mul_comm]
  push_cast
  ring_nf

/-- **The three-point amplification factor**: for the stencil `j ↦ cm u_{j-1} + c0 u_j + cp u_{j+1}`
wrapped onto `N` points, `γ_k = c0 + cm e^{-iφ_k} + cp e^{iφ_k}` with `φ_k = 2πk/N`. Every entry of
the stability column of [quarteroni2000numerical] Table 13.1 is this formula plus a modulus
computation. -/
theorem amplificationFactor_toPeriodic_threePoint (cm c0 cp : ℝ) (k : Fin N) :
    amplificationFactor (toPeriodic N (threePoint cm c0 cp)) k
      = c0 + cm * Complex.exp (-(I * (2 * π * k / N)))
        + cp * Complex.exp (I * (2 * π * k / N)) := by
  rw [amplificationFactor_toPeriodic_eq_symbol, symbol_threePoint]
  push_cast
  ring_nf

end Stencil

/-! ### Block circulants for multi-level schemes -/

section Block

variable {m : ℕ}

/-- **A multi-level scheme as a block circulant**: for a stencil of `m × m` blocks
`G : Fin N → Matrix (Fin m) (Fin m) ℂ`, the matrix on `Fin N × Fin m` with block `(j, l)` equal to
`G (j - l)`. Leap-frog for the wave equation is the case `m = 2` with unknowns `(u^{n+1}, u^n)`. -/
noncomputable def periodicBlockScheme (G : Fin N → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin N × Fin m) (Fin N × Fin m) ℂ :=
  Matrix.of fun jp lq => G (jp.1 - lq.1) jp.2 lq.2

/-- **The amplification matrix** of mode `k` of a block scheme: `G_k = ∑ s, ω^{-sk} • G s`. -/
noncomputable def amplificationMatrix (G : Fin N → Matrix (Fin m) (Fin m) ℂ) (k : Fin N) :
    Matrix (Fin m) (Fin m) ℂ :=
  ∑ s : Fin N, (Complex.exp (2 * π * I / N))⁻¹ ^ ((s : ℕ) * (k : ℕ)) • G s

/-- The mode `e_k` tensored with a block vector `v`: `(j, p) ↦ e_k j * v p`. -/
noncomputable def modeTensor (N : ℕ) (k : Fin N) (v : Fin m → ℂ) : Fin N × Fin m → ℂ :=
  fun jp => fourierMode N k jp.1 * v jp.2

/-- The action of a block scheme: `(B u) (j, p) = ∑ l, (G (j - l) *ᵥ u (l, ·)) p`. -/
theorem periodicBlockScheme_mulVec_apply (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (u : Fin N × Fin m → ℂ) (j : Fin N) (p : Fin m) :
    (periodicBlockScheme G *ᵥ u) (j, p) = ∑ l, (G (j - l) *ᵥ fun q => u (l, q)) p := by
  rw [mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product]
  rfl

/-- **The tensored modes are eigenvectors of a block scheme**, with the amplification matrix acting
on the block: `B (e_k ⊗ v) = e_k ⊗ (G_k v)`. -/
theorem periodicBlockScheme_mulVec_modeTensor (G : Fin N → Matrix (Fin m) (Fin m) ℂ) (k : Fin N)
    (v : Fin m → ℂ) :
    periodicBlockScheme G *ᵥ modeTensor N k v = modeTensor N k (amplificationMatrix G k *ᵥ v) := by
  ext ⟨j, p⟩
  have := neZero_of_fin j
  rw [periodicBlockScheme_mulVec_apply, modeTensor, amplificationMatrix, sum_mulVec,
    Finset.sum_apply, Finset.mul_sum]
  refine (Equiv.sum_comp (Equiv.subLeft j)
    fun l => (G (j - l) *ᵥ fun q => modeTensor N k v (l, q)) p).symm.trans
    (Finset.sum_congr rfl fun s _ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel, modeTensor, smul_mulVec, Pi.smul_apply,
    smul_eq_mul]
  rw [fourierMode_sub]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **The powers of a block scheme on the tensored modes**: `Bⁿ (e_k ⊗ v) = e_k ⊗ (G_kⁿ v)`
(the multi-level analogue of [quarteroni2000numerical] (13.52)), so the `ℓ²` stability of a
multi-level scheme is the uniform boundedness of the powers of its `m × m` amplification
matrices. -/
theorem periodicBlockScheme_pow_mulVec_fourierMode (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (k : Fin N) (v : Fin m → ℂ) (n : ℕ) :
    (periodicBlockScheme G ^ n) *ᵥ modeTensor N k v
      = modeTensor N k ((amplificationMatrix G k ^ n) *ᵥ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ih, periodicBlockScheme_mulVec_modeTensor, pow_succ',
      ← mulVec_mulVec]

/-! #### The `ℓ²` norm of the powers of a block scheme

The scalar argument transposes: expanding a block grid function in the tensored modes
`e_k ⊗ v` diagonalizes the block circulant into the `m × m` amplification matrices, and the
discrete Parseval identity applied to each block component turns the `ℓ²` norm of the powers into
the maximum of the norms of the powers of the amplification matrices. -/

/-- The modulus of an entry of a Fourier mode is `1`. -/
private theorem norm_fourierMode (k j : Fin N) : ‖fourierMode N k j‖ = 1 := by
  rw [fourierMode_apply, norm_pow]
  have h : Complex.exp (2 * π * I / N) = Complex.exp (((2 * π / N : ℝ) : ℂ) * I) := by
    congr 1
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- **Blockwise Parseval**: `∑_{k,p} |û(k, p)|² = N ∑_{j,p} |u(j, p)|²` for the componentwise
transform `û(k, p) = (Fᴴ u(·, p))(k)`. -/
private theorem sum_normSq_blockDft (u : Fin N × Fin m → ℂ) :
    (∑ kp : Fin N × Fin m, ‖((Matrix.dft N)ᴴ *ᵥ fun j => u (j, kp.2)) kp.1‖ ^ 2)
      = N * ∑ jp : Fin N × Fin m, ‖u jp‖ ^ 2 := by
  have h : ∀ p : Fin m, (∑ k : Fin N, ‖((Matrix.dft N)ᴴ *ᵥ fun j => u (j, p)) k‖ ^ 2)
      = N * ∑ j : Fin N, ‖u (j, p)‖ ^ 2 :=
    fun p => sum_normSq_conjTranspose_dft_mulVec fun j => u (j, p)
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => h p

/-- **Blockwise Parseval** for the inverse transform. -/
private theorem sum_normSq_blockExpand (v : Fin N × Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖(Matrix.dft N *ᵥ fun k => v (k, jp.2)) jp.1‖ ^ 2)
      = N * ∑ kp : Fin N × Fin m, ‖v kp‖ ^ 2 := by
  have h : ∀ p : Fin m, (∑ j : Fin N, ‖(Matrix.dft N *ᵥ fun k => v (k, p)) j‖ ^ 2)
      = N * ∑ k : Fin N, ‖v (k, p)‖ ^ 2 :=
    fun p => sum_normSq_dft_mulVec fun k => v (k, p)
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => h p

/-- A superposition of tensored modes is the inverse transform of its coefficients, componentwise.
-/
private theorem sum_modeTensor_apply (w : Fin N → Fin m → ℂ) (jp : Fin N × Fin m) :
    (∑ k : Fin N, modeTensor N k (w k)) jp = (Matrix.dft N *ᵥ fun k => w k jp.2) jp.1 := by
  rw [Finset.sum_apply, mulVec, dotProduct]
  rfl

/-- The squared `ℓ²` norm of a tensored mode: `‖e_k ⊗ w‖² = N ‖w‖²`. -/
private theorem sum_normSq_modeTensor (k : Fin N) (w : Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖modeTensor N k w jp‖ ^ 2) = N * ∑ p, ‖w p‖ ^ 2 := by
  have h : ∀ j : Fin N, (∑ p, ‖modeTensor N k w (j, p)‖ ^ 2) = ∑ p, ‖w p‖ ^ 2 := by
    intro j
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [modeTensor, norm_mul, norm_fourierMode, one_mul]
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun j _ => h j, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- An operator-norm bound on a matrix, in the form of a bound between sums of squares. -/
private theorem sum_normSq_mulVec_le {M : Matrix (Fin m) (Fin m) ℂ} {ρ : ℝ}
    (hρ : ‖toEuclideanCLM (𝕜 := ℂ) M‖ ≤ ρ) (w : Fin m → ℂ) :
    (∑ p, ‖(M *ᵥ w) p‖ ^ 2) ≤ ρ ^ 2 * ∑ p, ‖w p‖ ^ 2 := by
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hρ
  have h := (toEuclideanCLM (𝕜 := ℂ) M).le_opNorm (WithLp.toLp 2 w)
  rw [toEuclideanCLM_toLp] at h
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ w) : EuclideanSpace ℂ (Fin m))‖
      ≤ ρ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin m))‖ :=
    h.trans (mul_le_mul_of_nonneg_right hρ (norm_nonneg _))
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → √a ≤ ρ * √b → a ≤ ρ ^ 2 * b := by
    intro a b ha hb hab
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  exact key _ _ (by positivity) (by positivity) (by simpa [EuclideanSpace.norm_eq] using h2)

/-- The squared `ℓ²` norm of the image of a block grid function under the powers of a block
scheme, bounded through the amplification matrices. -/
private theorem sum_normSq_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hN : 0 < N)
    (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ)
    (y : Fin N × Fin m → ℂ) :
    (∑ jp : Fin N × Fin m, ‖((periodicBlockScheme G ^ n) *ᵥ y) jp‖ ^ 2)
      ≤ ρ ^ 2 * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set û : Fin N × Fin m → ℂ :=
    fun kp => ((Matrix.dft N)ᴴ *ᵥ fun j => y (j, kp.2)) kp.1 with hû
  set z : Fin N × Fin m → ℂ :=
    fun kp => ((amplificationMatrix G kp.1 ^ n) *ᵥ fun q => û (kp.1, q)) kp.2 with hz
  -- `y` is the inverse transform of `û`, hence a superposition of tensored modes
  have hinv : ∀ p : Fin m, (Matrix.dft N *ᵥ fun k => û (k, p)) = (N : ℂ) • fun j => y (j, p) := by
    intro p
    change (Matrix.dft N *ᵥ ((Matrix.dft N)ᴴ *ᵥ fun j => y (j, p))) = _
    rw [mulVec_mulVec, Matrix.dft_mul_conjTranspose_dft, smul_mulVec, one_mulVec]
  have hy : y = ((N : ℂ))⁻¹ • ∑ k : Fin N, modeTensor N k (fun q => û (k, q)) := by
    funext jp
    rw [Pi.smul_apply, smul_eq_mul, sum_modeTensor_apply, hinv jp.2, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hNC, one_mul]
  -- the powers act modewise
  have hstep : ∀ k : Fin N, (periodicBlockScheme G ^ n) *ᵥ modeTensor N k (fun q => û (k, q))
      = modeTensor N k (fun q => z (k, q)) :=
    fun k => periodicBlockScheme_pow_mulVec_fourierMode G k (fun q => û (k, q)) n
  have hBy : (periodicBlockScheme G ^ n) *ᵥ y
      = fun jp => ((N : ℂ))⁻¹ * (Matrix.dft N *ᵥ fun k => z (k, jp.2)) jp.1 := by
    rw [hy, mulVec_smul, mulVec_sum, Finset.sum_congr rfl fun k _ => hstep k]
    funext jp
    rw [Pi.smul_apply, smul_eq_mul, sum_modeTensor_apply]
  -- Parseval on both sides
  have h1 : (∑ jp : Fin N × Fin m, ‖((periodicBlockScheme G ^ n) *ᵥ y) jp‖ ^ 2)
      = ((N : ℝ))⁻¹ * ∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2 := by
    rw [hBy]
    simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    rw [← Finset.mul_sum, sum_normSq_blockExpand]
    field_simp
  have hblock : ∀ k : Fin N, (∑ p : Fin m, ‖z (k, p)‖ ^ 2)
      ≤ ρ ^ 2 * ∑ p : Fin m, ‖û (k, p)‖ ^ 2 :=
    fun k => sum_normSq_mulVec_le (hρ k) fun q => û (k, q)
  have h2 : (∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2) ≤ ρ ^ 2 * ∑ kp : Fin N × Fin m, ‖û kp‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hblock k
  have h3 : (∑ kp : Fin N × Fin m, ‖û kp‖ ^ 2) = N * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 :=
    sum_normSq_blockDft y
  rw [h3] at h2
  rw [h1]
  calc ((N : ℝ))⁻¹ * ∑ kp : Fin N × Fin m, ‖z kp‖ ^ 2
      ≤ ((N : ℝ))⁻¹ * (ρ ^ 2 * ((N : ℝ) * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ρ ^ 2 * ∑ jp : Fin N × Fin m, ‖y jp‖ ^ 2 := by field_simp

/-- **The `ℓ²` bound for the powers of a block scheme**: if every amplification matrix satisfies
`‖G_kⁿ‖₂ ≤ ρ`, then `‖Bⁿ u‖₂ ≤ ρ ‖u‖₂`. Expanding `u` in the tensored modes diagonalizes `Bⁿ`
into the blocks `G_kⁿ` (`FiniteDifference.periodicBlockScheme_pow_mulVec_fourierMode`), and
discrete Parseval applied to each block component of the transform turns the modewise bounds into
the global one. -/
theorem norm_toEuclideanLin_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ)
    (u : EuclideanSpace ℂ (Fin N × Fin m)) :
    ‖toEuclideanLin (periodicBlockScheme G ^ n) u‖ ≤ ρ * ‖u‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ ⟨0, hN⟩)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hρ0,
    ← Real.sqrt_mul (sq_nonneg ρ)]
  refine Real.sqrt_le_sqrt ?_
  exact sum_normSq_periodicBlockScheme_pow_le G hN hρ (WithLp.ofLp u)

/-- The operator-norm form: `‖Bⁿ‖₂ ≤ ρ` when every amplification matrix satisfies `‖G_kⁿ‖₂ ≤ ρ`.
-/
theorem norm_toEuclideanCLM_periodicBlockScheme_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    {ρ : ℝ} {n : ℕ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ k, ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖ ≤ ρ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)‖ ≤ ρ :=
  ContinuousLinearMap.opNorm_le_bound _ hρ0 fun u =>
    norm_toEuclideanLin_periodicBlockScheme_pow_le G hρ u

/-- **The amplification matrices bound the norm of the powers from below**:
`‖G_kⁿ‖₂ ≤ ‖Bⁿ‖₂` for every mode `k`, by testing `Bⁿ` on the tensored modes `e_k ⊗ v`, whose norm
is `√N ‖v‖`. With `norm_toEuclideanCLM_periodicBlockScheme_pow_le` this makes the `ℓ²` stability
of a multi-level scheme exactly the uniform boundedness of the powers of its `m × m`
amplification matrices. -/
theorem norm_toEuclideanCLM_amplificationMatrix_pow_le (G : Fin N → Matrix (Fin m) (Fin m) ℂ)
    (k : Fin N) (n : ℕ) :
    ‖toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n)‖
      ≤ ‖toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)‖ := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr k.pos
  have hsqrt : (0 : ℝ) < √N := Real.sqrt_pos.mpr hNR
  have hnorm : ∀ u : Fin m → ℂ,
      ‖(WithLp.toLp 2 (modeTensor N k u) : EuclideanSpace ℂ (Fin N × Fin m))‖
        = √N * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin m))‖ := by
    intro u
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul (Nat.cast_nonneg N)]
    congr 1
    simpa using sum_normSq_modeTensor k u
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  have h := (toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n)).le_opNorm
    (WithLp.toLp 2 (modeTensor N k (WithLp.ofLp v)))
  rw [toEuclideanCLM_toLp, periodicBlockScheme_pow_mulVec_fourierMode, hnorm, hnorm] at h
  have hv : (WithLp.toLp 2 (WithLp.ofLp v) : EuclideanSpace ℂ (Fin m)) = v := rfl
  rw [hv] at h
  have hgv : toEuclideanCLM (𝕜 := ℂ) (amplificationMatrix G k ^ n) v
      = WithLp.toLp 2 ((amplificationMatrix G k ^ n) *ᵥ WithLp.ofLp v) := rfl
  rw [hgv]
  nlinarith [h, norm_nonneg (WithLp.toLp 2 ((amplificationMatrix G k ^ n) *ᵥ WithLp.ofLp v) :
    EuclideanSpace ℂ (Fin m)), norm_nonneg v,
    norm_nonneg (toEuclideanCLM (𝕜 := ℂ) (periodicBlockScheme G ^ n))]

end Block

end FiniteDifference
