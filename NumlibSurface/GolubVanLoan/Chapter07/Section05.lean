import Numlib.Eigen.RayleighQuotientIteration
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub–Van Loan §7.5: the practical QR algorithm

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.5: the shifted QR step (7.5.3) as an orthogonal similarity and the rate of
the fixed-shift iteration (§7.5.2), the exact shift (Theorem 7.5.1) and the quadratic convergence
of the single-shift iteration (§7.5.3), the double-shift identities (7.5.6)–(7.5.8), the first
column of `M` that starts the Francis step, the Francis QR step (Algorithm 7.5.1) and its
essential uniqueness (§7.5.5), and the QR algorithm (Algorithm 7.5.2, §7.5.6).

## Conventions

Real upper Hessenberg `H : Matrix (Fin n) (Fin n) ℝ`, complex shifts through `Matrix.complexify`.
"A QR factorization" is given as data: a unitary (orthogonal over `ℝ`) `U` and an upper triangular
`R` with `H - μ I = U R`, so that the statements hold for every factorization, as the book's do. The
backbone's canonical steps are `Matrix.shiftedQrStep`, `Matrix.doubleShiftQrStep`, and the
predicates `Matrix.IsShiftedQrStep`, `Matrix.IsFrancisStep` (`Numlib/Eigen/QRAlgorithm`). Indices
are 0-based: the book's `h_{n,n-1}` is `H (Fin.last _) (Fin.castSucc (Fin.last _))`.

## Algorithms

The programs follow the conventions of `NumlibSurface/GolubVanLoan` (generic in a monad `M` and a
rounding hook `rnd`) and call chapter 5's shared helpers. `algorithm_7_5_1` is the Francis step on
a window `w` of consecutive indices, bulge chasing by `houseOn` and
`householderApplyLeft/Right` over the book's restricted row and column ranges
(`francisReflect`, `francisChaseStep`); it returns the reflector data, so that
`Z = householderProduct data`. Its exact semantics `algorithm_7_5_1_spec` (on the full window)
rests on the bulge pattern `IsFrancisBulge`: each reflector annihilates the bulge column, and the
restricted ranges miss only zeros, so each step is the full similarity `P H P`; the triangularity
of `Zᵀ (H - a₁ I)(H - a₂ I)` is the implicit-shift principle
`Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval`. `triangularize2x2` is the
book's unspecified "upper triangularize all 2-by-2 diagonal blocks with real eigenvalues" (an
eigenvector, then `givens`), with `triangularize2x2_spec`. `algorithm_7_5_2` runs Algorithm 7.4.2,
the backward accumulation of its reflectors, at most `fuel` deflation-and-Francis passes
(`qrDeflate`, `schurTrailingStart`, `unreducedStart`, `qrPass`) and the final standardization.

## Not formalized

The deflation criterion (7.5.2) as a heuristic and the "decoupling" discussion; Stewart's worked
example `h̃_{n,n-1} = -ε² b/(a² + ε²)` (its rigorous content is `single_shift_quadratic`); the
roundoff claims of §7.5.6 (`≈`, no derivation); balancing (§7.5.7); flop counts. The exact
semantics of Algorithm 7.5.2 (`algorithm_7_5_2_spec`) is planned and not yet proved.
-/

open Matrix Polynomial FloatingPoint

open GolubVanLoan.Chapter05 (houseOn houseOn_spec householderApplyLeft householderApplyRight
  householderApplyLeft_spec householderApplyRight_spec householderProduct householderProduct_concat
  householderProduct_cons householderProduct_nil householderProduct_mem_orthogonalGroup
  backwardAccumulation algorithm_5_1_3 algorithm_5_1_3_spec givensRotation
  givensRotation_mem_orthogonalGroup givensRotation_transpose_mulVec_apply givensApplyLeft
  givensApplyRight givensApplyLeft_spec givensApplyRight_spec givensApplyRight_spec_of_forall_mem)

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-- A QR step `H' = R U + μ I` after `H - μ I = U R` is the unitary similarity `H' = Uᴴ H U`. -/
private theorem qr_step_eq_conj {𝕜 : Type*} [RCLike 𝕜] {H U R H' : Matrix (Fin n) (Fin n) 𝕜}
    {μ : 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜) (hQR : H - μ • 1 = U * R)
    (hH' : H' = R * U + μ • 1) : H' = star U * H * U := by
  have h1 : star U * U = 1 := mem_unitaryGroup_iff'.1 hU
  have hR : R = star U * (H - μ • 1) := by rw [hQR, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hH', hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1,
    sub_add_cancel]

/-- A unimodular diagonal matrix is unitary. -/
private theorem diagonal_mem_unitaryGroup {𝕜 : Type*} [RCLike 𝕜] {d : Fin n → 𝕜}
    (hd : ∀ i, ‖d i‖ = 1) : diagonal d ∈ unitaryGroup (Fin n) 𝕜 := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, hd i]
  simp

/-- A shifted QR step of a unimodular diagonal similarity `D* H D` of `H` (taken with the factors
`D* U`, `R D` of the factorization `H - μ I = U R`) lands on the same matrix as the step of `H`. -/
private theorem isShiftedQrStep_diagonal_conj {𝕜 : Type*} [RCLike 𝕜] {μ : 𝕜}
    {H H' : Matrix (Fin n) (Fin n) 𝕜} {d : Fin n → 𝕜} (hd : ∀ i, ‖d i‖ = 1)
    (h : IsShiftedQrStep μ H H') :
    IsShiftedQrStep μ (star (diagonal d) * H * diagonal d) H' := by
  obtain ⟨U, hU, R, hR, hQR, rfl⟩ := h
  have hD := diagonal_mem_unitaryGroup hd
  have hDD : star (diagonal d) * diagonal d = 1 := mem_unitaryGroup_iff'.1 hD
  have hDD' : diagonal d * star (diagonal d) = 1 := mem_unitaryGroup_iff.1 hD
  refine ⟨star (diagonal d) * U, Submonoid.mul_mem _ (Unitary.star_mem hD) hU, R * diagonal d,
    hR.mul (blockTriangular_diagonal d), ?_, ?_⟩
  · have hH : H = U * R + μ • 1 := by rw [← hQR, sub_add_cancel]
    rw [hH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hDD, add_sub_cancel_right]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal d), hDD', Matrix.one_mul]

/-! ### §7.5.2 The shifted QR iteration -/

/-- **(7.5.3).** Each matrix of the shifted QR iteration is orthogonally similar to its predecessor:
if `H - μ I = U R` with `U` orthogonal, then `R U + μ I = Uᵀ (U R + μ I) U = Uᵀ H U`. -/
theorem equation_7_5_3 {H U R : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (hQR : H - μ • 1 = U * R) :
    R * U + μ • 1 = Uᵀ * H * U := by
  have h := qr_step_eq_conj hU hQR rfl
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- An entry of a real unimodular diagonal similarity has the modulus of the original entry. -/
private theorem abs_diagonal_conj_apply {d : Fin n → ℝ} (hd : ∀ i, ‖d i‖ = 1)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    |(star (diagonal d) * S * diagonal d) i j| = |S i j| := by
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  have hi : |d i| = 1 := by simpa using hd i
  have hj : |d j| = 1 := by simpa using hd j
  simp [abs_mul, hi, hj]

/-- A real unimodular diagonal similarity keeps the diagonal. -/
private theorem diagonal_conj_apply_self {d : Fin n → ℝ} (hd : ∀ i, ‖d i‖ = 1)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (star (diagonal d) * S * diagonal d) i i = S i i := by
  rw [star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  have hi : |d i| = 1 := by simpa using hd i
  have hii : d i * d i = 1 := by rw [← abs_mul_abs_self, hi, one_mul]
  simp only [Pi.star_apply, star_trivial]
  calc d i * S i i * d i = (d i * d i) * S i i := by ring
    _ = S i i := by rw [hii, one_mul]

/-- **Any fixed-shift QR iteration is the canonical one up to a unimodular diagonal
similarity**, as long as `A - μ I` is nonsingular: the QR factorization of a nonsingular matrix is
unique up to such a diagonal (`Matrix.IsShiftedQrStep.unique_of_isUnit`). -/
private theorem exists_eq_diagonal_conj_shiftedQrIterate {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hA : IsUnit (A - μ • 1).det) {H : ℕ → Matrix (Fin n) (Fin n) ℝ} (hH0 : H 0 = A)
    (hH : ∀ k, IsShiftedQrStep μ (H k) (H (k + 1))) (k : ℕ) :
    ∃ d : Fin n → ℝ, (∀ i, ‖d i‖ = 1) ∧
      H k = star (diagonal d) * shiftedQrIterate A μ k * diagonal d := by
  induction k with
  | zero =>
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [diagonal_one, star_one, Matrix.one_mul, Matrix.mul_one, hH0, shiftedQrIterate_zero]
  | succ k ih =>
    obtain ⟨d, hd, hk⟩ := ih
    have hD := diagonal_mem_unitaryGroup hd
    have hDD : star (diagonal d) * diagonal d = 1 := mem_unitaryGroup_iff'.1 hD
    have hDD' : diagonal d * star (diagonal d) = 1 := mem_unitaryGroup_iff.1 hD
    have hc : IsShiftedQrStep μ (H k) (shiftedQrIterate A μ (k + 1)) := by
      rw [hk, shiftedQrIterate_succ]
      exact isShiftedQrStep_diagonal_conj hd (isShiftedQrStep_shiftedQrStep _ _)
    have hsub : H k - μ • 1 = star (diagonal d) * qrIterate (A - μ • 1) k * diagonal d := by
      rw [hk, ← add_sub_cancel_right (qrIterate (A - μ • 1) k) (μ • 1),
        ← shiftedQrIterate_eq_qrIterate_sub_add, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hDD]
    have hdet : IsUnit (H k - μ • 1).det := by
      rw [hsub, det_mul, det_mul]
      exact ((isUnit_det_of_right_inverse hDD).mul (isUnit_det_qrIterate hA k)).mul
        (isUnit_det_of_right_inverse hDD')
    exact hc.unique_of_isUnit (hH k) hdet

/-- **§7.5.2, the rate of the fixed-shift QR iteration.** "If `μ` is a fixed shift and the
eigenvalues `λ_i` of `H` are ordered so that `|λ₁ - μ| ≥ ⋯ ≥ |λ_n - μ|`, then the theory of §7.3
says that the `p`th subdiagonal entry in `H_k` converges to zero with rate
`|(λ_{p+1} - μ)/(λ_p - μ)|^k`." Rigorous form: for `A = X diag(λ) X⁻¹` with
`|λ₁ - μ| > ⋯ > |λ_n - μ| > 0` and `X⁻¹` with nonsingular leading principal submatrices (the
general-position hypothesis of the theory of §7.3), every fixed-shift QR iteration `H_{k+1}` of
`H_k` (`H_k - μ I = U_k R_k`, `H_{k+1} = R_k U_k + μ I`, any factorizations), `H_0 = A`, has
`|H_k(p+1, p)| ≤ C (r / |λ_p - μ|)^k` for every `r > |λ_{p+1} - μ|` (0-based indices). -/
theorem shiftedQr_rate {A X : Matrix (Fin n) (Fin n) ℝ} {l : Fin n → ℝ} {μ : ℝ}
    (hX : IsUnit X.det) (hXA : X⁻¹ * A * X = diagonal l)
    (hsep : ∀ j k : Fin n, j < k → |l k - μ| < |l j - μ|) (hμ : ∀ j, l j ≠ μ)
    (hgen : ∀ (m : ℕ) (hm : m ≤ n),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det)
    {H : ℕ → Matrix (Fin n) (Fin n) ℝ} (hH0 : H 0 = A)
    (hH : ∀ k, IsShiftedQrStep μ (H k) (H (k + 1))) {p q : Fin n} (hpq : (q : ℕ) = p + 1)
    {r : ℝ} (hr : |l q - μ| < r) :
    ∃ C : ℝ, ∀ k, |H k q p| ≤ C * (r / |l p - μ|) ^ k := by
  set B := A - μ • (1 : Matrix (Fin n) (Fin n) ℝ) with hBdef
  have hXu : IsUnit X := (isUnit_iff_isUnit_det X).2 hX
  have hXB : X⁻¹ * B * X = diagonal fun j => l j - μ := by
    rw [hBdef, Matrix.mul_sub, Matrix.sub_mul, hXA, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, nonsing_inv_mul _ hX]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hdetB : IsUnit B.det := by
    have h := congrArg det hXB
    rw [det_mul, det_mul, det_diagonal] at h
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero, zero_mul] at h
    exact (Finset.prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 (hμ j)) h.symm
  have hpq' : p < q := Fin.lt_def.2 (by omega)
  set L := |l p - μ| with hLdef
  set ρ := |l q - μ| with hρdef
  have hρL : ρ < L := hsep p q hpq'
  set r' := min r ((ρ + L) / 2) with hr'def
  have hr'0 : 0 ≤ r' := le_min ((abs_nonneg _).trans hr.le) (by positivity)
  have hr'r : r' ≤ r := min_le_left _ _
  have hρr' : ρ < r' := lt_min hr (by linarith)
  have hr'L : r' < L := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨C, hC⟩ := exists_abs_qrIterate_apply_le hdetB (x := euclideanCol X)
    (l := fun j => l j - μ) (linearIndependent_euclideanCol hX)
    (span_range_euclideanCol_eq_top hX) (toEuclideanLin_euclideanCol_of_conj_eq_diagonal hXu hXB)
    (fun j k hjk => by simpa [Real.norm_eq_abs] using hsep j k hjk)
    ((forall_isLowerSet_disjoint_iff_isUnit_leadingPrincipal hX).2 hgen) hpq' hr'0
    (fun j' hj' => by
      simp only [Real.norm_eq_abs]
      rcases eq_or_lt_of_le (Fin.le_def.2 (show (q : ℕ) ≤ j' by
        have := Fin.lt_def.1 hj'; omega)) with h | h
      · rw [← h]; exact hρr'.le
      · exact ((hsep q j' h).trans hρr').le)
    (by simpa [Real.norm_eq_abs] using hr'L)
  have hL0 : 0 < L := (abs_nonneg _).trans_lt hρL
  refine ⟨max C 0, fun k => ?_⟩
  obtain ⟨d, hd, hk⟩ := exists_eq_diagonal_conj_shiftedQrIterate hdetB hH0 hH k
  have hqp : q ≠ p := hpq'.ne'
  have hentry : |H k q p| = ‖qrIterate B k q p‖ := by
    rw [hk, abs_diagonal_conj_apply hd, shiftedQrIterate_eq_qrIterate_sub_add, Matrix.add_apply,
      Matrix.smul_apply, one_apply_ne hqp, smul_zero, add_zero, Real.norm_eq_abs]
  rw [hentry]
  calc ‖qrIterate B k q p‖ ≤ C * (r' / ‖l p - μ‖) ^ k := hC k
    _ ≤ max C 0 * (r' / L) ^ k := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (r / L) ^ k := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k)
          (le_max_right _ _)
        exact div_le_div_of_nonneg_right hr'r hL0.le


/-- **Theorem 7.5.1 (the exact shift)**, over `ℂ` as printed (the eigenvalue `μ` of the real `H` may
be complex). Let `H ∈ ℝ^{n×n}` be unreduced upper Hessenberg and `μ` an eigenvalue of `H`. If
`H̃ = R U + μ I` where `H - μ I = U R` is a QR factorization (`U` unitary, `R` upper triangular),
then `h̃_{n,n-1} = 0` and `h̃_{nn} = μ`: indeed the whole last row of `H̃` is `μ e_nᵀ`. -/
theorem theorem_7_5_1 {N : ℕ} {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hH : IsUnreduced H)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ H.complexify) {U R H' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hU : U ∈ unitaryGroup (Fin (N + 1)) ℂ) (hR : R.IsUpperTriangular)
    (hQR : H.complexify - μ • 1 = U * R) (hH' : H' = R * U + μ • 1) (j : Fin (N + 1)) :
    H' (Fin.last N) j = if j = Fin.last N then μ else 0 :=
  IsUnreducedUpperHessenberg.isShiftedQrStep_apply_last
    (hH.map (f := Complex.ofRealHom) Complex.ofReal_injective) hμ ⟨U, hU, R, hR, hQR, hH'⟩ j

/-! ### §7.5.3 The single-shift strategy -/

/-- **§7.5.3, the single-shift iteration (7.5.4): "If the `(n, n-1)` entry converges to zero, it is
likely to do so at a quadratic rate."** Rigorous local form: for `A` with an algebraically simple
real eigenvalue `l` there are `C` and `δ > 0` such that, for every Hessenberg orthogonal conjugate
`T = Qᵀ A Q` with `|t_{n,n-1}| ≤ δ`, `|t_nn - l| ≤ δ` and `T - t_nn I` nonsingular, every
single-shift QR step `T'` (`T - t_nn I = U R`, `T' = R U + t_nn I`, any factorization) has
`|t'_{n,n-1}| ≤ C t_{n,n-1}²` and `|t'_nn - l| ≤ C t_{n,n-1}²` (0-based: `n` is `Fin.last`). The
last row of a shifted step is one step of Rayleigh quotient iteration on `Tᵀ`
(`Matrix.abs_shiftedQrStep_last_le_of_conj`). -/
theorem single_shift_quadratic {N : ℕ} {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ} {l : ℝ}
    (hl : A.charpoly.rootMultiplicity l = 1) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ Q T T' : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ,
      Q ∈ orthogonalGroup (Fin (N + 2)) ℝ → T = Qᵀ * A * Q → T.IsUpperHessenberg →
      IsUnit (T - T (Fin.last (N + 1)) (Fin.last (N + 1)) • 1) →
      |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ δ →
      |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ δ →
      IsShiftedQrStep (T (Fin.last (N + 1)) (Fin.last (N + 1))) T T' →
      |T' (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 ∧
        |T' (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤
          C * |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
  obtain ⟨x, y, K, hx, hy, hyx, hK, hKw⟩ := exists_eigenvector_data_of_rootMultiplicity_eq_one hl
  set C₀ : ℝ := ‖LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)‖ + |l| with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  have hCz : ∀ z : EuclideanSpace ℝ (Fin (N + 2)), ‖toEuclideanLin Aᵀ z - l • z‖ ≤ C₀ * ‖z‖ :=
    fun z => by
      calc ‖toEuclideanLin Aᵀ z - l • z‖ ≤ ‖toEuclideanLin Aᵀ z‖ + ‖l • z‖ := norm_sub_le _ _
        _ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)‖ * ‖z‖ + |l| * ‖z‖ := by
          gcongr
          · exact (LinearMap.toContinuousLinearMap (toEuclideanLin Aᵀ)).le_opNorm z
          · rw [norm_smul, Real.norm_eq_abs]
        _ = C₀ * ‖z‖ := by ring
  set A' : ℝ := 2 * K * (1 + ‖x‖ * ‖y‖) with hA'def
  have hA'0 : 0 < A' := by positivity
  set D : ℝ := 4 * A' + 2 * K * C₀ * A' + 2 * K with hDdef
  have hD : 0 < D := by positivity
  refine ⟨4 * K * C₀ ^ 2 * A' ^ 2, 1 / D, by positivity,
    fun Q T T' hQ hTQ hT hunit ht hd hstep => ?_⟩
  set t := |T (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| with htdef
  have ht0 : 0 ≤ t := abs_nonneg _
  have hsub1 : 4 * A' * t ≤ 1 := by
    calc 4 * A' * t ≤ 4 * A' * (1 / D) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [mul_nonneg (mul_nonneg hK.le hC₀) hA'0.le]
  have hsub2 : 2 * K * C₀ * A' * t ≤ 1 := by
    calc 2 * K * C₀ * A' * t ≤ 2 * K * C₀ * A' * (1 / D) := by
          gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [hA'0, hK]
  have hdiag : 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 1 := by
    calc 2 * K * |T (Fin.last (N + 1)) (Fin.last (N + 1)) - l| ≤ 2 * K * (1 / D) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one hD]
        nlinarith [mul_nonneg (mul_nonneg hK.le hC₀) hA'0.le, hA'0]
  obtain ⟨h₁, h₂⟩ := abs_shiftedQrStep_last_le_of_conj hQ hTQ hT hx hy hyx hK.le hKw hCz hunit
    hsub1 hsub2 hdiag
  obtain ⟨d, hd, hT'⟩ := (isShiftedQrStep_shiftedQrStep _ T).unique_of_isUnit hstep
    ((isUnit_iff_isUnit_det _).1 hunit)
  have hne : Fin.castSucc (Fin.last N) ≠ Fin.last (N + 1) := Fin.castSucc_lt_last _ |>.ne
  refine ⟨?_, ?_⟩
  · rw [hT', abs_diagonal_conj_apply hd]
    exact h₁ _ hne
  · rw [hT', diagonal_conj_apply_self hd]
    exact h₂


/-! ### §7.5.4 The double-shift strategy -/

/-- **(7.5.6)–(7.5.7).** If `H - a₁ I = U₁ R₁`, `H₁ = R₁ U₁ + a₁ I`, `H₁ - a₂ I = U₂ R₂`,
`H₂ = R₂ U₂ + a₂ I` (complex shifts, factorizations of complex matrices), then
`(U₁ U₂)(R₂ R₁) = M` with `M = (H - a₁ I)(H - a₂ I)` (7.5.8), and `H₂ = (U₁ U₂)ᴴ H (U₁ U₂)`. -/
theorem equation_7_5_7 {H H₁ H₂ U₁ U₂ R₁ R₂ : Matrix (Fin n) (Fin n) ℂ} {a₁ a₂ : ℂ}
    (hU₁ : U₁ ∈ unitaryGroup (Fin n) ℂ) (hU₂ : U₂ ∈ unitaryGroup (Fin n) ℂ)
    (h₁ : H - a₁ • 1 = U₁ * R₁) (hH₁ : H₁ = R₁ * U₁ + a₁ • 1)
    (h₂ : H₁ - a₂ • 1 = U₂ * R₂) (hH₂ : H₂ = R₂ * U₂ + a₂ • 1) :
    U₁ * U₂ * (R₂ * R₁) = (H - a₁ • 1) * (H - a₂ • 1) ∧
      H₂ = star (U₁ * U₂) * H * (U₁ * U₂) := by
  constructor
  · have hstep : U₂ * R₂ = R₁ * U₁ + (a₁ - a₂) • 1 := by
      rw [← h₂, hH₁, sub_smul]; abel
    calc U₁ * U₂ * (R₂ * R₁) = U₁ * (U₂ * R₂) * R₁ := by simp only [Matrix.mul_assoc]
      _ = U₁ * R₁ * (U₁ * R₁) + (a₁ - a₂) • (U₁ * R₁) := by
          rw [hstep]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = (H - a₁ • 1) * (H - a₂ • 1) := by
          rw [← h₁]
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul, Matrix.mul_one, sub_smul, smul_sub, smul_smul]
          module
  · rw [qr_step_eq_conj hU₂ h₂ hH₂, qr_step_eq_conj hU₁ h₁ hH₁, star_mul]
    simp only [Matrix.mul_assoc]

/-- **(7.5.5) and (7.5.8).** Let `G = [h_mm h_mn; h_nm h_nn]` (`m = n - 1`) be the trailing `2 × 2`
block of a real `H` and `a₁`, `a₂` its (possibly complex) eigenvalues. Then `s = a₁ + a₂ = tr G`
and `t = a₁ a₂ = det G` are real, and `M = (H - a₁ I)(H - a₂ I) = H² - s H + t I` is real even
when `a₁`, `a₂` are complex. -/
theorem equation_7_5_8 {N : ℕ} (H : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) {a₁ a₂ : ℂ}
    (ha : (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).complexify.charpoly.roots = {a₁, a₂}) :
    a₁ + a₂ = ((H.submatrix (Fin.natAdd N) (Fin.natAdd N)).trace : ℂ) ∧
      a₁ * a₂ = ((H.submatrix (Fin.natAdd N) (Fin.natAdd N)).det : ℂ) ∧
      (H.complexify - a₁ • 1) * (H.complexify - a₂ • 1) =
        (H * H - (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).trace • H +
          (H.submatrix (Fin.natAdd N) (Fin.natAdd N)).det • 1).complexify := by
  set G := H.submatrix (Fin.natAdd N) (Fin.natAdd N)
  have htr : a₁ + a₂ = (G.trace : ℂ) := by
    have h := trace_eq_sum_roots_charpoly G.complexify
    rw [ha] at h
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at h
    rw [← h]
    simp [Matrix.trace, complexify, Fin.sum_univ_two]
  have hdet : a₁ * a₂ = (G.det : ℂ) := by
    have h := det_eq_prod_roots_charpoly G.complexify
    rw [ha] at h
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton] at h
    rw [← h]
    simp [det_fin_two, complexify]
  refine ⟨htr, hdet, ?_⟩
  rw [complexify_add, complexify_sub, complexify_mul, complexify_smul, complexify_smul,
    complexify_one, ← htr, ← hdet]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, add_smul]
  module

/-- **§7.5.4: "(7.5.7) is the QR factorization of a real matrix and we may choose `U₁` and `U₂` so
that `Z = U₁ U₂` is real orthogonal. It then follows that `H₂ = Zᵀ H Z` is real."** For real `H`
and a shift `a₁ = a` that is not an eigenvalue, with `a₂ = ā`, the canonical double-shift step is
real: it is the complexification of `Zᵀ H Z` with `Z` the canonical orthogonal factor of the real
`M = H² - 2 Re(a) H + |a|² I`; and for any choice of the two QR factorizations the result is a
unimodular diagonal similarity of it. -/
theorem double_shift_real (H : Matrix (Fin n) (Fin n) ℝ) {a : ℂ}
    (ha : a ∉ spectrum ℂ H.complexify) :
    qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1) ∈ orthogonalGroup (Fin n) ℝ ∧
      doubleShiftQrStep H.complexify a =
        ((qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1))ᵀ * H *
          qrQ (H * H - (2 * a.re) • H + Complex.normSq a • 1)).complexify ∧
      ∀ H₁ H₂ : Matrix (Fin n) (Fin n) ℂ, IsShiftedQrStep a H.complexify H₁ →
        IsShiftedQrStep (starRingEnd ℂ a) H₁ H₂ →
        ∃ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) ∧
          H₂ = star (diagonal d) * doubleShiftQrStep H.complexify a * diagonal d := by
  refine ⟨qrQ_mem_unitaryGroup _, doubleShiftQrStep_map_ofReal H ha, fun H₁ H₂ h₁ h₂ => ?_⟩
  have hdet₁ : IsUnit (H.complexify - a • 1).det := isUnit_det_sub_smul_one_of_notMem_spectrum ha
  obtain ⟨d, hd, hH₁⟩ := (isShiftedQrStep_shiftedQrStep a H.complexify).unique_of_isUnit h₁ hdet₁
  -- the canonical second step, taken from `H₁`
  have hc₂ : IsShiftedQrStep (starRingEnd ℂ a) H₁
      (shiftedQrStep (starRingEnd ℂ a) (shiftedQrStep a H.complexify)) := by
    rw [hH₁]
    exact isShiftedQrStep_diagonal_conj hd (isShiftedQrStep_shiftedQrStep _ _)
  -- `H₁ - ā I` is nonsingular: `ā` is not an eigenvalue of the real `H`, nor of its conjugates
  have hā : starRingEnd ℂ a ∉ spectrum ℂ H.complexify := fun h =>
    ha ((star_mem_spectrum_complexify_iff H a).1 h)
  obtain ⟨V, hV, hHV⟩ := h₁.eq_conj
  have hdet₂ : IsUnit (H₁ - starRingEnd ℂ a • 1).det := by
    have hVV : star V * V = 1 := mem_unitaryGroup_iff'.1 hV
    have hVV' : V * star V = 1 := mem_unitaryGroup_iff.1 hV
    have hsim : H₁ - starRingEnd ℂ a • 1 = star V * (H.complexify - starRingEnd ℂ a • 1) * V := by
      rw [hHV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        hVV]
    rw [hsim, det_mul, det_mul]
    exact ((isUnit_det_of_right_inverse hVV).mul
      (isUnit_det_sub_smul_one_of_notMem_spectrum hā)).mul (isUnit_det_of_right_inverse hVV')
  obtain ⟨e, he, hH₂⟩ := hc₂.unique_of_isUnit h₂ hdet₂
  exact ⟨e, he, hH₂⟩

/-! ### §7.5.5 The Francis step -/

/-- **§7.5.5, the first column of `M`.** For upper Hessenberg `H` with `n ≥ 3` and
`M = H² - s H + t I`, the first column `M e₁ = (x, y, z, 0, …, 0)ᵀ` with
`x = h₁₁² + h₁₂ h₂₁ - s h₁₁ + t`, `y = h₂₁ (h₁₁ + h₂₂ - s)`, `z = h₂₁ h₃₂` (0-based in Lean): only
the first three entries of the first column of `M` can be nonzero, which is why the Francis step
starts with a `3 × 3` reflector. -/
theorem francis_first_column {N : ℕ} {H : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    (hH : H.IsUpperHessenberg) (s t : ℝ) :
    (H * H - s • H + t • 1) 0 0 = H 0 0 * H 0 0 + H 0 1 * H 1 0 - s * H 0 0 + t ∧
      (H * H - s • H + t • 1) 1 0 = H 1 0 * (H 0 0 + H 1 1 - s) ∧
      (H * H - s • H + t • 1) ⟨2, by omega⟩ 0 = H 1 0 * H ⟨2, by omega⟩ 1 ∧
      ∀ i : Fin (N + 3), 3 ≤ (i : ℕ) → (H * H - s • H + t • 1) i 0 = 0 := by
  rw [isUpperHessenberg_iff_fin] at hH
  have hHH : ∀ i, (H * H) i 0 = H i 0 * H 0 0 + H i 1 * H 1 0 := by
    intro i
    rw [mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
    · rfl
    · intro k _
      rw [hH _ 0 (by simp), mul_zero]
  have hM : ∀ i, (H * H - s • H + t • 1) i 0 = H i 0 * H 0 0 + H i 1 * H 1 0 - s * H i 0 +
      t * (1 : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ) i 0 :=
    fun i => by
      rw [Matrix.add_apply, Matrix.sub_apply, hHH, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
  have h10 : (1 : Fin (N + 3)) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩
  · rw [hM, one_apply_eq]
    ring
  · rw [hM, one_apply_ne h10]
    ring
  · have h20 : H ⟨2, by omega⟩ 0 = 0 := hH _ _ (by simp)
    have hne : (⟨2, by omega⟩ : Fin (N + 3)) ≠ 0 := fun h => by simp [Fin.ext_iff] at h
    rw [hM, one_apply_ne hne, h20]
    ring
  · have hne : i ≠ 0 := fun h => by rw [h] at hi; simp at hi
    have hi0 : H i 0 = 0 := hH i 0 (by simp; omega)
    have hi1 : H i 1 = 0 := hH i 1 (by simp; omega)
    rw [hM, one_apply_ne hne, hi0, hi1]
    ring

/-! ### §7.5.5 Algorithm 7.5.1 -/

/-! ### Programs -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The window `[p, m)`**: the indices `p ≤ i < m` in increasing order — the unreduced block
`H₂₂` of Algorithm 7.5.2, on which the Francis step runs. -/
def francisWindow (n p m : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun i => p ≤ (i : ℕ) ∧ (i : ℕ) < m

/-- The consecutive triples `(w₀, w₁, w₂), (w₁, w₂, w₃), …` of a window `w`: the index lists
`o_k = [w_k, w_{k+1}, w_{k+2}]` of the bulge-chasing steps of Algorithm 7.5.1. -/
def francisTriples {α : Type*} : List α → List (α × α × α)
  | a :: b :: c :: t => (a, b, c) :: francisTriples (b :: c :: t)
  | _ => []

/-- The first column of `(H - a₁ I)(H - a₂ I)` in Algorithm 7.5.1, with `s`, `t` from the trailing
`2 × 2` block `H([m, l], [m, l])`:
```
s = H(m,m) + H(l,l)
t = H(m,m)·H(l,l) - H(m,l)·H(l,m)
x = H(1,1)·H(1,1) + H(1,2)·H(2,1) - s·H(1,1) + t
y = H(2,1)·(H(1,1) + H(2,2) - s)
z = H(2,1)·H(3,2)
```
each operation rounded in the printed order; `x`, `y`, `z` are placed at the indices `a`, `b`, `c`
(the book's `1, 2, 3`), zero elsewhere. -/
noncomputable def francisShiftVector (a b c m l : Fin n) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Fin n → ℝ) := do
  let s ← rnd (H m m + H l l)
  let t ← rnd ((← rnd (H m m * H l l)) - (← rnd (H m l * H l m)))
  let x ← rnd ((← rnd ((← rnd ((← rnd (H a a * H a a)) + (← rnd (H a b * H b a)))) -
    (← rnd (s * H a a)))) + t)
  let y ← rnd (H b a * (← rnd ((← rnd (H a a + H b b)) - s)))
  let z ← rnd (H b a * H c b)
  pure fun i => if i = a then x else if i = b then y else if i = c then z else 0

/-- One two-sided Householder update of Algorithm 7.5.1: `[v, β] = house(u(o))` (chapter 5's
`houseOn`), `H(o, cols) = (I - β v vᵀ) H(o, cols)`, `H(rows, o) = H(rows, o) (I - β v vᵀ)`;
returns the new matrix and the reflector data `(v, β)`. -/
noncomputable def francisReflect (o : List (Fin n)) (u : Fin n → ℝ) (cols rows : List (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) : M (Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ)) := do
  let vβ ← houseOn rnd o u
  let H ← householderApplyLeft rnd vβ.1 vβ.2 o cols H
  let H ← householderApplyRight rnd vβ.1 vβ.2 rows o H
  pure (H, vβ)

/-- One bulge-chasing step `k ≥ 1` of Algorithm 7.5.1 on the triple `t = (a, a+1, a+2)`:
`[v, β] = house(H(a:a+2, a-1))`, the two-sided update of `francisReflect` with the column range
`q:n` (`a ≤ j + 1`) and the row range `1:r` (`i ≤ a + 3`) of the window `w`, and the reflector data
appended to the list. -/
noncomputable def francisChaseStep (w : List (Fin n))
    (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) (t : Fin n × Fin n × Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) := do
  let r ← francisReflect rnd [t.1, t.2.1, t.2.2]
    (fun i => st.1 i ⟨(t.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.1.isLt⟩)
    (w.filter fun j => (t.1 : ℕ) ≤ j + 1) (w.filter fun i => (i : ℕ) ≤ t.1 + 3) st.1
  pure (r.1, st.2 ++ [r.2])

/-- **Algorithm 7.5.1 (Francis QR step)** on a window `w` of consecutive indices (the book's
algorithm is `w = List.finRange n`; Algorithm 7.5.2 runs it on the unreduced block `H₂₂`):
"Given the unreduced upper Hessenberg matrix `H ∈ ℝ^{n×n}` whose trailing 2-by-2 principal
submatrix has eigenvalues `a₁` and `a₂`, this algorithm overwrites `H` with `Zᵀ H Z`, where `Z` is
a product of Householder matrices and `Zᵀ (H - a₁ I)(H - a₂ I)` is upper triangular."
```
m = n - 1
s = H(m,m) + H(n,n);  t = H(m,m)·H(n,n) - H(m,n)·H(n,m)
x = H(1,1)·H(1,1) + H(1,2)·H(2,1) - s·H(1,1) + t
y = H(2,1)·(H(1,1) + H(2,2) - s);  z = H(2,1)·H(3,2)
for k = 0:n-3
    [v, β] = house([x y z]ᵀ)
    q = max{1, k};  H(k+1:k+3, q:n) = (I - β v vᵀ) H(k+1:k+3, q:n)
    r = min{k+4, n};  H(1:r, k+1:k+3) = H(1:r, k+1:k+3) (I - β v vᵀ)
    x = H(k+2, k+1);  y = H(k+3, k+1);  if k < n-3, z = H(k+4, k+1) end
end
[v, β] = house([x y]ᵀ)
H(n-1:n, n-2:n) = (I - β v vᵀ) H(n-1:n, n-2:n)
H(1:n, n-1:n) = H(1:n, n-1:n) (I - β v vᵀ)
```
The step `k` works on the triple `o_k = (a, a+1, a+2)` of window indices (`francisTriples`); for
`k ≥ 1` the vector `[x y z]ᵀ` is column `a - 1` of `H` on `o_k`, read in place by `houseOn`; the
column range `q:n` is the window indices `j` with `a ≤ j + 1`, the row range `1:r` those with
`i ≤ a + 3`. Only the block `H(w, w)` changes. Returns the new `H` and the reflector data in order
of application (convention 13), so that `Z = householderProduct data`. For a window of fewer than
three indices nothing is done. -/
noncomputable def algorithm_7_5_1 (w : List (Fin n)) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) :=
  match francisTriples w with
  | [] => pure (H, [])
  | t₀ :: ts => do
    let tl := (t₀ :: ts).getLast (List.cons_ne_nil _ _)
    let u ← francisShiftVector rnd t₀.1 t₀.2.1 t₀.2.2 tl.2.1 tl.2.2 H
    let st ← francisReflect rnd [t₀.1, t₀.2.1, t₀.2.2] u
      (w.filter fun j => (t₀.1 : ℕ) ≤ j + 1) (w.filter fun i => (i : ℕ) ≤ t₀.1 + 3) H
    let st ← ts.foldlM (francisChaseStep rnd w) (st.1, [st.2])
    let r ← francisReflect rnd [tl.2.1, tl.2.2] (fun i => st.1 i tl.1)
      (w.filter fun j => (tl.1 : ℕ) ≤ j) w st.1
    pure (r.1, st.2 ++ [r.2])

end Programs

/-! ### Index bookkeeping -/

section Triples

variable {α : Type*}

/-- The number of consecutive triples of a list. -/
theorem length_francisTriples : ∀ w : List α, (francisTriples w).length = w.length - 2
  | a :: b :: c :: t => by
    rw [francisTriples, List.length_cons, length_francisTriples (b :: c :: t)]
    simp
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl

/-- The `k`-th consecutive triple of a list. -/
theorem getElem_francisTriples : ∀ (w : List α) (k : ℕ) (hk : k < (francisTriples w).length),
    (francisTriples w)[k] =
      (w[k]'(by rw [length_francisTriples] at hk; omega),
        w[k + 1]'(by rw [length_francisTriples] at hk; omega),
        w[k + 2]'(by rw [length_francisTriples] at hk; omega))
  | a :: b :: c :: t, 0, _ => rfl
  | a :: b :: c :: t, k + 1, hk => by
    have hk' : k < (francisTriples (b :: c :: t)).length := by
      rw [francisTriples, List.length_cons] at hk; omega
    exact getElem_francisTriples (b :: c :: t) k hk'
  | [], _, hk => absurd hk (by simp [francisTriples])
  | [_], _, hk => absurd hk (by simp [francisTriples])
  | [_, _], _, hk => absurd hk (by simp [francisTriples])

end Triples

/-! ### Reflector algebra -/

section Reflector

variable {v : Fin n → ℝ} {β : ℝ} {S : Fin n → Prop}

/-- An entry of `(I - β v vᵀ) H`. -/
private theorem one_sub_smul_vecMulVec_mul_apply (β : ℝ) (v : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    ((1 - β • vecMulVec v v) * H) i j = H i j - β * v i * ∑ r, v r * H r j := by
  have hPA : ((1 - β • vecMulVec v v) * H) i j = ((1 - β • vecMulVec v v) *ᵥ fun r => H r j) i :=
    rfl
  rw [hPA, one_sub_smul_vecMulVec_mulVec_apply]
  rfl

/-- An entry of `H (I - β v vᵀ)`. -/
private theorem mul_one_sub_smul_vecMulVec_apply (β : ℝ) (v : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (H * (1 - β • vecMulVec v v)) i j = H i j - β * (∑ r, H i r * v r) * v j := by
  have hAP : (H * (1 - β • vecMulVec v v)) i j = ((1 - β • vecMulVec v v) *ᵥ H i) j := by
    conv_rhs => rw [← transpose_one_sub_smul_vecMulVec β v, mulVec_transpose]
    rfl
  rw [hAP, one_sub_smul_vecMulVec_mulVec_apply, dotProduct,
    Finset.sum_congr rfl fun r _ => mul_comm (v r) (H i r)]
  ring

/-- A column vanishing on the support of `v` is fixed by `I - β v vᵀ`. -/
private theorem one_sub_smul_vecMulVec_mul_apply_of_forall (hv : ∀ i, ¬ S i → v i = 0)
    {H : Matrix (Fin n) (Fin n) ℝ} {j : Fin n} (hH : ∀ r, S r → H r j = 0) (i : Fin n) :
    ((1 - β • vecMulVec v v) * H) i j = H i j := by
  rw [one_sub_smul_vecMulVec_mul_apply, Finset.sum_eq_zero, mul_zero, sub_zero]
  intro r _
  by_cases hr : S r
  · rw [hH r hr, mul_zero]
  · rw [hv r hr, zero_mul]

/-- A row vanishing on the support of `v` is fixed by `I - β v vᵀ` on the right. -/
private theorem mul_one_sub_smul_vecMulVec_apply_of_forall (hv : ∀ i, ¬ S i → v i = 0)
    {H : Matrix (Fin n) (Fin n) ℝ} {i : Fin n} (hH : ∀ r, S r → H i r = 0) (j : Fin n) :
    (H * (1 - β • vecMulVec v v)) i j = H i j := by
  rw [mul_one_sub_smul_vecMulVec_apply, Finset.sum_eq_zero, mul_zero, zero_mul, sub_zero]
  intro r _
  by_cases hr : S r
  · rw [hH r hr, zero_mul]
  · rw [hv r hr, mul_zero]

/-- `(I - β v vᵀ) H` agrees with `H` off the support of `v`. -/
private theorem one_sub_smul_vecMulVec_mul_apply_of_notMem (hv : ∀ i, ¬ S i → v i = 0)
    (H : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (hi : ¬ S i) (j : Fin n) :
    ((1 - β • vecMulVec v v) * H) i j = H i j := by
  rw [one_sub_smul_vecMulVec_mul_apply, hv i hi, mul_zero, zero_mul, sub_zero]

/-- `H (I - β v vᵀ)` agrees with `H` off the support of `v`. -/
private theorem mul_one_sub_smul_vecMulVec_apply_of_notMem (hv : ∀ i, ¬ S i → v i = 0)
    (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) {j : Fin n} (hj : ¬ S j) :
    (H * (1 - β • vecMulVec v v)) i j = H i j := by
  rw [mul_one_sub_smul_vecMulVec_apply, hv j hj, mul_zero, sub_zero]

end Reflector

/-! ### Windows and block similarities -/

section Window

/-- The membership in the window `[p, m)`. -/
theorem mem_francisWindow {p m : ℕ} {i : Fin n} :
    i ∈ francisWindow n p m ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < m := by
  simp [francisWindow]

/-- The window has no repeated index. -/
theorem nodup_francisWindow (n p m : ℕ) : (francisWindow n p m).Nodup :=
  (List.nodup_finRange n).filter _

/-- The window `[0, n)` is the full index list. -/
theorem francisWindow_zero (n : ℕ) : francisWindow n 0 n = List.finRange n :=
  List.filter_eq_self.2 fun i _ => by simp

private theorem val_ofNat_lt [NeZero n] {k : ℕ} (hk : k < n) : (Fin.ofNat n k : ℕ) = k := by
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hk]

/-- The window `[p, m)` lists `p, p + 1, …, m - 1` in increasing order. -/
theorem francisWindow_eq_map [NeZero n] {p m : ℕ} (hm : m ≤ n) :
    francisWindow n p m = (List.range (m - p)).map fun k => Fin.ofNat n (p + k) := by
  have hmap : ∀ k ∈ List.range (m - p), (Fin.ofNat n (p + k) : ℕ) = p + k := fun k hk => by
    rw [List.mem_range] at hk
    exact val_ofNat_lt (by omega)
  refine List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl a))
    ((List.pairwise_lt_finRange n).filter _) ?_ ?_
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
    rw [Fin.lt_def, hmap a ha, hmap b hb]
    omega
  · rw [List.perm_ext_iff_of_nodup (nodup_francisWindow n p m)]
    · intro i
      rw [mem_francisWindow, List.mem_map]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(i : ℕ) - p, List.mem_range.2 (by omega), Fin.ext ?_⟩
        rw [val_ofNat_lt (by omega)]
        omega
      · rintro ⟨k, hk, rfl⟩
        rw [hmap k hk]
        rw [List.mem_range] at hk
        omega
    · refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
      have := congrArg Fin.val hab
      rw [hmap a ha, hmap b hb] at this
      omega

/-- The triple `(k, k+1, k+2)` of `Fin n`. -/
def francisTri (n : ℕ) [NeZero n] (k : ℕ) : Fin n × Fin n × Fin n :=
  (Fin.ofNat n k, Fin.ofNat n (k + 1), Fin.ofNat n (k + 2))

/-- The values of the triple `(k, k+1, k+2)`. -/
theorem francisTri_val [NeZero n] {k : ℕ} (hk : k + 2 < n) :
    ((francisTri n k).1 : ℕ) = k ∧ ((francisTri n k).2.1 : ℕ) = k + 1 ∧
      ((francisTri n k).2.2 : ℕ) = k + 2 :=
  ⟨val_ofNat_lt (by omega), val_ofNat_lt (by omega), val_ofNat_lt hk⟩

/-- The consecutive triples of the window `[p, m)`. -/
theorem francisTriples_francisWindow [NeZero n] {p m : ℕ} (hm : m ≤ n) :
    francisTriples (francisWindow n p m) =
      (List.range (m - p - 2)).map fun k => francisTri n (p + k) := by
  rw [francisWindow_eq_map hm]
  refine List.ext_getElem (by simp [length_francisTriples]) fun k h₁ h₂ => ?_
  rw [getElem_francisTriples]
  simp only [List.getElem_map, List.getElem_range, francisTri, Nat.add_assoc]

/-- **A similarity on the block `[p, m) × [p, m)`**: `Qᵀ H Q` on the block and `H` elsewhere — what
Algorithm 7.5.1 does to a matrix when it runs on the window `[p, m)`. -/
def blockConj (p m : ℕ) (Q H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if (p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) then
    (Qᵀ * H * Q) i j else H i j

/-- On the full window the block similarity is the similarity. -/
theorem blockConj_zero (Q H : Matrix (Fin n) (Fin n) ℝ) : blockConj 0 n Q H = Qᵀ * H * Q := by
  ext i j
  simp [blockConj]

/-- `Q` acts on the block `[p, m)` only: it is the identity outside `[p, m) × [p, m)`. -/
def IsBlockSupported (p m : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, ¬ ((p ≤ (i : ℕ) ∧ (i : ℕ) < m) ∧ (p ≤ (j : ℕ) ∧ (j : ℕ) < m)) →
    Q i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j

/-- The identity acts on any block. -/
theorem isBlockSupported_one (p m : ℕ) : IsBlockSupported p m (1 : Matrix (Fin n) (Fin n) ℝ) :=
  fun _ _ _ => rfl

/-- A reflector whose vector vanishes off the block acts on the block. -/
theorem isBlockSupported_reflector {p m : ℕ} {v : Fin n → ℝ} (β : ℝ)
    (hv : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v i = 0) :
    IsBlockSupported p m (1 - β • vecMulVec v v) := fun i j hij => by
  rw [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
  · rw [hv j fun hj => hij ⟨hi, hj⟩, mul_zero, mul_zero, sub_zero]
  · rw [hv i hi, zero_mul, mul_zero, sub_zero]

/-- Products of matrices acting on a block act on it. -/
theorem IsBlockSupported.mul {p m : ℕ} {Q P : Matrix (Fin n) (Fin n) ℝ}
    (hQ : IsBlockSupported p m Q) (hP : IsBlockSupported p m P) : IsBlockSupported p m (Q * P) :=
  fun i j hij => by
    by_cases hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m
    · have hj : ¬ (p ≤ (j : ℕ) ∧ (j : ℕ) < m) := fun hj => hij ⟨hi, hj⟩
      rw [mul_apply, Finset.sum_eq_single j, hP j j (fun h => hj h.2), one_apply_eq, mul_one,
        hQ i j hij]
      · intro k _ hkj
        rw [hP k j (fun h => hj h.2), one_apply_ne hkj, mul_zero]
      · simp
    · rw [mul_apply, Finset.sum_eq_single i, hQ i i (fun h => hi h.1), one_apply_eq, one_mul,
        hP i j (fun h => hi h.1)]
      · intro k _ hki
        rw [hQ i k (fun h => hi h.1), one_apply_ne (Ne.symm hki), zero_mul]
      · simp

/-- A product of reflector data supported on the block acts on the block. -/
theorem isBlockSupported_householderProduct {p m : ℕ} {data : List ((Fin n → ℝ) × ℝ)}
    (h : ∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) :
    IsBlockSupported p m (householderProduct data) := by
  induction data with
  | nil => exact isBlockSupported_one p m
  | cons q data ih =>
    rw [householderProduct_cons]
    exact (isBlockSupported_reflector q.2 (h q List.mem_cons_self)).mul
      (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- A similarity by a matrix acting on the block sees only the block of the conjugated matrix. -/
private theorem transpose_mul_mul_apply_congr {p m : ℕ} {P X Y : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsBlockSupported p m P)
    (hXY : ∀ k l : Fin n, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → (p ≤ (l : ℕ) ∧ (l : ℕ) < m) →
      X k l = Y k l) {i j : Fin n} (hi : p ≤ (i : ℕ) ∧ (i : ℕ) < m)
    (hj : p ≤ (j : ℕ) ∧ (j : ℕ) < m) : (Pᵀ * X * P) i j = (Pᵀ * Y * P) i j := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
  · by_cases hl : p ≤ (l : ℕ) ∧ (l : ℕ) < m
    · rw [hXY k l hk hl]
    · rw [hP l j (fun h => hl h.1), one_apply_ne (fun e => hl (by rw [e]; exact hj)), mul_zero,
        mul_zero]
  · rw [hP k i (fun h => hk h.1), one_apply_ne (fun e => hk (by rw [e]; exact hi)), zero_mul,
      zero_mul,
      zero_mul, zero_mul]

/-- **Block similarities compose**: for `Z`, `P` acting on the block,
`blockConj P (blockConj Z H) = blockConj (Z P) H`. -/
theorem blockConj_blockConj {p m : ℕ} {Z P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsBlockSupported p m P) (H : Matrix (Fin n) (Fin n) ℝ) :
    blockConj p m P (blockConj p m Z H) = blockConj p m (Z * P) H := by
  ext i j
  simp only [blockConj, of_apply]
  split_ifs with hin
  · rw [transpose_mul_mul_apply_congr hP (Y := Zᵀ * H * Z) (fun k l hk hl => by
      simp only [of_apply, hk, hl, and_self, ↓reduceIte]) hin.1 hin.2, transpose_mul]
    simp only [Matrix.mul_assoc]
  · rfl

end Window

/-! ### The bulge-chasing invariant -/

section Bulge

/-- **The zero pattern of Algorithm 7.5.1 on the window `[p, m)` before the step on the triple
`(a, a+1, a+2)`**: upper Hessenberg except for the bulge entries `(a+1, a-1)`, `(a+2, a-1)` and
`(a+2, a)` inside the window (for `a = p` only `(p+2, p)`): `h_ij = 0` for `j + 1 < i` unless
`p ≤ j`, `i < m`, `a ≤ j + 1`, `j ≤ a`, `i ≤ a + 2`. -/
def IsFrancisBulge (p m a : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < i →
    ¬ (p ≤ (j : ℕ) ∧ (i : ℕ) < m ∧ a ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ a ∧ (i : ℕ) ≤ a + 2) → H i j = 0

/-- An upper Hessenberg matrix has every bulge pattern. -/
theorem isFrancisBulge_of_isUpperHessenberg {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsUpperHessenberg) (p m a : ℕ) : IsFrancisBulge p m a H := fun i j hij _ =>
  hH i j ⟨⟨(j : ℕ) + 1, by omega⟩, Fin.lt_def.2 (by simp), Fin.lt_def.2 (by simpa using hij)⟩

variable {v u : Fin n → ℝ} {β : ℝ}

/-- `(I - β v vᵀ) H` in a column equal to `u` is `(I - β v vᵀ) u`. -/
private theorem one_sub_smul_vecMulVec_mul_apply_eq_mulVec {H : Matrix (Fin n) (Fin n) ℝ}
    {j : Fin n} (hu : ∀ r, H r j = u r) (i : Fin n) :
    ((1 - β • vecMulVec v v) * H) i j = ((1 - β • vecMulVec v v) *ᵥ u) i := by
  have h : (fun r => H r j) = u := funext hu
  rw [← h]
  rfl

/-- **One bulge-chasing step keeps the pattern** ([golub2013matrix] §7.5.5, the pictures of the
Francis step), on the window `[p, m)`: if `H` has the pattern before the step on `(a, a+1, a+2)`,
`p ≤ a`, `a + 2 < m`, `v` is supported on those rows, and `P = I - β v vᵀ` maps `u` — column
`a - 1` of `H` when `p < a` — to a vector vanishing at `a + 1`, `a + 2`, then the block similarity
by `P` has the pattern before the step on `(a+1, a+2, a+3)`. -/
theorem IsFrancisBulge.conj {p m a : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m a H)
    (hv : ∀ i : Fin n, (i : ℕ) < a ∨ a + 2 < (i : ℕ) → v i = 0)
    (hPu : ∀ i : Fin n, a < (i : ℕ) → (i : ℕ) ≤ a + 2 → ((1 - β • vecMulVec v v) *ᵥ u) i = 0)
    (hu : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) + 1 = a → ∀ r, H r j = u r) :
    IsFrancisBulge p m (a + 1) (blockConj p m (1 - β • vecMulVec v v) H) := by
  intro i j hij hex
  have hv' : ∀ r : Fin n, ¬ (a ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2) → v r = 0 := fun r hr =>
    hv r (by omega)
  simp only [blockConj, of_apply]
  split_ifs with hin
  swap
  · exact hB i j hij (by omega)
  rw [transpose_one_sub_smul_vecMulVec, mul_one_sub_smul_vecMulVec_apply]
  by_cases hj : a ≤ (j : ℕ) ∧ (j : ℕ) ≤ a + 2
  · -- a column of the active block: row `i ≥ a + 4` is outside the block and vanishes on it
    have hi : a + 3 < (i : ℕ) := by omega
    have hrow : ∀ r : Fin n, ((1 - β • vecMulVec v v) * H) i r = H i r := fun r =>
      one_sub_smul_vecMulVec_mul_apply_of_notMem hv' H (by omega) r
    have hHi : ∀ r : Fin n, (r : ℕ) ≤ a + 2 → H i r = 0 := fun r hr =>
      hB i r (by omega) (by omega)
    rw [hrow, hHi j hj.2, Finset.sum_eq_zero, mul_zero, zero_mul, sub_zero]
    intro r _
    rw [hrow]
    by_cases hr : a ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2
    · rw [hHi r hr.2, zero_mul]
    · rw [hv' r hr, mul_zero]
  · rw [hv' j hj, mul_zero, sub_zero]
    by_cases hi : a ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + 2
    · -- a row of the active block: `j < a`
      rcases Nat.lt_or_ge ((j : ℕ) + 1) a with hja | hja
      · rw [one_sub_smul_vecMulVec_mul_apply_of_forall hv' (fun r hr => hB r j (by omega)
          (by omega))]
        exact hB i j hij (by omega)
      · rw [one_sub_smul_vecMulVec_mul_apply_eq_mulVec (hu j hin.2.1 (by omega))]
        exact hPu i (by omega) hi.2
    · rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv' H hi]
      exact hB i j hij (by omega)

/-- **The last step of Algorithm 7.5.1 restores Hessenberg form**, on the window `[p, a + 3)`: if
`H` has the pattern before the step on `(a+1, a+2, a+3)` — only the entry `(a+2, a)` below the
subdiagonal inside the window — `v` is supported on `a + 1`, `a + 2`, and `P = I - β v vᵀ` maps
column `a` of `H` to a vector vanishing at `a + 2`, then the block similarity by `P` is upper
Hessenberg. -/
theorem IsFrancisBulge.conj_last {p m a : ℕ} (ham : a + 3 = m)
    {H : Matrix (Fin n) (Fin n) ℝ} (hB : IsFrancisBulge p m (a + 1) H)
    (hv : ∀ i : Fin n, (i : ℕ) ≤ a ∨ a + 2 < (i : ℕ) → v i = 0)
    (hPu : ∀ i : Fin n, (i : ℕ) = a + 2 → ((1 - β • vecMulVec v v) *ᵥ u) i = 0)
    (hu : ∀ j : Fin n, (j : ℕ) = a → ∀ r, H r j = u r) :
    (blockConj p m (1 - β • vecMulVec v v) H).IsUpperHessenberg := by
  intro i j ⟨k, hjk, hki⟩
  have hij : (j : ℕ) + 1 < i := by
    have := Fin.lt_def.1 hjk
    have := Fin.lt_def.1 hki
    omega
  have hv' : ∀ r : Fin n, ¬ (a + 1 ≤ (r : ℕ) ∧ (r : ℕ) ≤ a + 2) → v r = 0 := fun r hr =>
    hv r (by omega)
  simp only [blockConj, of_apply]
  split_ifs with hin
  swap
  · exact hB i j hij (by omega)
  rw [transpose_one_sub_smul_vecMulVec, mul_one_sub_smul_vecMulVec_apply, hv' j (by omega),
    mul_zero, sub_zero]
  by_cases hi : a + 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ a + 2
  · rcases Nat.lt_or_ge (j : ℕ) a with hja | hja
    · rw [one_sub_smul_vecMulVec_mul_apply_of_forall hv' (fun r hr => hB r j (by omega)
        (by omega))]
      exact hB i j hij (by omega)
    · rw [one_sub_smul_vecMulVec_mul_apply_eq_mulVec (hu j (by omega))]
      exact hPu i (by omega)
  · rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv' H hi]
    exact hB i j hij (by omega)

end Bulge

/-! ### Algorithm 7.5.1: the exact semantics of one step -/

section FrancisSpec

/-- **The exact two-sided update on a window**: if the reflector's rows `o` lie in the window
`[p, m)` and in both ranges, the columns of the window outside the column range vanish on `o`,
and the rows of the window outside the row range vanish on `o`, then the restricted updates of
`francisReflect` compute the block similarity by `P = I - β v vᵀ`. -/
theorem francisReflect_window {p m : ℕ} {o : List (Fin n)} (ho : o.Nodup) (hne : o ≠ [])
    (u : Fin n → ℝ) {cols rows : List (Fin n)} (hcols : cols.Nodup) (hrows : rows.Nodup)
    {C R : Fin n → Prop} (hcm : ∀ q, q ∈ cols ↔ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) ∧ C q)
    (hrm : ∀ r, r ∈ rows ↔ (p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ R r)
    (hoin : ∀ k ∈ o, (p ≤ (k : ℕ) ∧ (k : ℕ) < m) ∧ C k ∧ R k) {H : Matrix (Fin n) (Fin n) ℝ}
    (hc : ∀ q : Fin n, p ≤ (q : ℕ) → (q : ℕ) < m → ¬ C q → ∀ k ∈ o, H k q = 0)
    (hr : ∀ r : Fin n, p ≤ (r : ℕ) → (r : ℕ) < m → ¬ R r → ∀ k ∈ o, H r k = 0) :
    Id.run (francisReflect pure o u cols rows H) =
      (blockConj p m (1 - (Id.run (houseOn pure o u)).2 • vecMulVec (Id.run (houseOn pure o u)).1
        (Id.run (houseOn pure o u)).1) H, Id.run (houseOn pure o u)) := by
  have hv := (houseOn_spec ho hne u).2.1
  change (Id.run (householderApplyRight pure (Id.run (houseOn pure o u)).1
      (Id.run (houseOn pure o u)).2 rows o
      (Id.run (householderApplyLeft pure (Id.run (houseOn pure o u)).1
        (Id.run (houseOn pure o u)).2 o cols H))), Id.run (houseOn pure o u)) = _
  generalize Id.run (houseOn pure o u) = vβ at hv ⊢
  obtain ⟨v, β⟩ := vβ
  simp only at hv ⊢
  have hvS : ∀ k : Fin n, ¬ (p ≤ (k : ℕ) ∧ (k : ℕ) < m) → v k = 0 := fun k hk =>
    hv k fun h => hk (hoin k h).1
  rw [householderApplyLeft_spec ho hcols hv]
  set L : Matrix (Fin n) (Fin n) ℝ :=
    of fun i q => if q ∈ cols then ((1 - β • vecMulVec v v) * H) i q else H i q with hL
  have hLin : ∀ i q : Fin n, (p ≤ (q : ℕ) ∧ (q : ℕ) < m) →
      L i q = ((1 - β • vecMulVec v v) * H) i q := by
    intro i q hq
    rw [hL, of_apply]
    by_cases hqc : q ∈ cols
    · simp only [hqc, ↓reduceIte]
    · have hC : ¬ C q := fun h => hqc ((hcm q).2 ⟨hq, h⟩)
      simp only [hqc, ↓reduceIte]
      exact (one_sub_smul_vecMulVec_mul_apply_of_forall hv (fun k hk =>
        hc q hq.1 hq.2 hC k hk) i).symm
  have hLout : ∀ i q : Fin n, ¬ (p ≤ (q : ℕ) ∧ (q : ℕ) < m) → L i q = H i q := by
    intro i q hq
    have hqc : q ∉ cols := fun h => hq ((hcm q).1 h).1
    rw [hL, of_apply]
    simp only [hqc, ↓reduceIte]
  have hsum : ∀ r : Fin n, ∑ k, L r k * v k = ∑ k, ((1 - β • vecMulVec v v) * H) r k * v k :=
    fun r => Finset.sum_congr rfl fun k _ => by
      by_cases hk : p ≤ (k : ℕ) ∧ (k : ℕ) < m
      · rw [hLin r k hk]
      · rw [hvS k hk, mul_zero, mul_zero]
  rw [householderApplyRight_spec hrows ho hv]
  congr 1
  ext r c
  simp only [of_apply, blockConj, transpose_one_sub_smul_vecMulVec]
  by_cases hrB : p ≤ (r : ℕ) ∧ (r : ℕ) < m
  · by_cases hcB : p ≤ (c : ℕ) ∧ (c : ℕ) < m
    · simp only [hrB, hcB, and_self, ↓reduceIte]
      by_cases hrR : R r
      · have hrr : r ∈ rows := (hrm r).2 ⟨hrB, hrR⟩
        simp only [hrr, ↓reduceIte]
        rw [mul_one_sub_smul_vecMulVec_apply, mul_one_sub_smul_vecMulVec_apply, hsum,
          hLin r c hcB]
      · have hrr : r ∉ rows := fun h => hrR ((hrm r).1 h).2
        have hro : r ∉ o := fun h => hrR (hoin r h).2.2
        simp only [hrr, ↓reduceIte]
        rw [hLin r c hcB, mul_one_sub_smul_vecMulVec_apply, Finset.sum_eq_zero, mul_zero,
          zero_mul, sub_zero]
        intro k _
        rw [one_sub_smul_vecMulVec_mul_apply_of_notMem hv H hro]
        by_cases hk : k ∈ o
        · rw [hr r hrB.1 hrB.2 hrR k hk, zero_mul]
        · rw [hv k hk, mul_zero]
    · have hcond : ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (c : ℕ) ∧ (c : ℕ) < m)) :=
        fun h => hcB h.2
      simp only [hcond, ↓reduceIte]
      split_ifs with hrr
      · rw [mul_one_sub_smul_vecMulVec_apply, hvS c hcB, mul_zero, sub_zero, hLout r c hcB]
      · exact hLout r c hcB
  · have hcond : ¬ ((p ≤ (r : ℕ) ∧ (r : ℕ) < m) ∧ (p ≤ (c : ℕ) ∧ (c : ℕ) < m)) :=
      fun h => hrB h.1
    have hrr : r ∉ rows := fun h => hrB ((hrm r).1 h).1
    simp only [hcond, hrr, ↓reduceIte]
    by_cases hcB : p ≤ (c : ℕ) ∧ (c : ℕ) < m
    · rw [hLin r c hcB, one_sub_smul_vecMulVec_mul_apply_of_notMem hv H
        (fun h => hrB (hoin r h).1)]
    · exact hLout r c hcB

/-- **One bulge-chasing step on a window, exactly**: on the triple `(a, a+1, a+2)` of the window
`[p, m)` with the pattern `IsFrancisBulge p m a`, the two restricted updates of Algorithm 7.5.1
compute the block similarity by the reflector `P = I - β v vᵀ` of `house(u)`, which has the pattern
`IsFrancisBulge p m (a + 1)`. -/
theorem francis_step {p m : ℕ} {a b c : Fin n} (hb : (b : ℕ) = a + 1) (hc : (c : ℕ) = a + 2)
    (hpa : p ≤ a) (ham : (a : ℕ) + 2 < m) {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m a H) {u : Fin n → ℝ}
    (hu : ∀ j : Fin n, p ≤ (j : ℕ) → (j : ℕ) + 1 = a → ∀ r, H r j = u r) {v : Fin n → ℝ} {β : ℝ}
    (hvβ : Id.run (houseOn pure [a, b, c] u) = (v, β)) :
    Id.run (francisReflect pure [a, b, c] u
        ((francisWindow n p m).filter fun j => (a : ℕ) ≤ j + 1)
        ((francisWindow n p m).filter fun i => (i : ℕ) ≤ a + 3) H) =
      (blockConj p m (1 - β • vecMulVec v v) H, (v, β)) ∧
      IsFrancisBulge p m (a + 1) (blockConj p m (1 - β • vecMulVec v v) H) ∧
      (β = 0 ∨ β * (v ⬝ᵥ v) = 2) ∧ (∀ i : Fin n, (i : ℕ) < a ∨ (a : ℕ) + 2 < i → v i = 0) ∧
      (1 - β • vecMulVec v v) *ᵥ u = fun i => if i = a then
          ‖(WithLp.toLp 2 (fun j : {j // j ∈ [a, b, c]} => u j) :
            EuclideanSpace ℝ {j // j ∈ [a, b, c]})‖
        else if i ∈ [a, b, c] then 0 else u i := by
  have hmem : ∀ i : Fin n, i ∈ [a, b, c] ↔ (a : ℕ) ≤ i ∧ (i : ℕ) ≤ a + 2 := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc]
    omega
  have hnd : [a, b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  have hspec := houseOn_spec hnd (List.cons_ne_nil _ _) u
  rw [hvβ] at hspec
  obtain ⟨-, hvout, hβ, -, hPu⟩ := hspec
  have hv : ∀ i : Fin n, (i : ℕ) < a ∨ (a : ℕ) + 2 < i → v i = 0 := fun i hi =>
    hvout i fun h => by rw [hmem] at h; omega
  have hPu' : ∀ i : Fin n, (a : ℕ) < i → (i : ℕ) ≤ a + 2 →
      ((1 - β • vecMulVec v v) *ᵥ u) i = 0 := fun i h1 h2 => by
    rw [hPu]
    have hia : i ≠ a := fun e => by rw [e] at h1; omega
    simp only [List.head_cons, hia, ↓reduceIte, (hmem i).2 ⟨h1.le, h2⟩]
  refine ⟨?_, hB.conj hv hPu' hu, hβ, hv, hPu⟩
  rw [francisReflect_window (p := p) (m := m) hnd (List.cons_ne_nil _ _) u
    ((nodup_francisWindow n p m).filter _) ((nodup_francisWindow n p m).filter _)
    (C := fun j => (a : ℕ) ≤ j + 1) (R := fun i => (i : ℕ) ≤ a + 3)
    (fun q => by simp [List.mem_filter, mem_francisWindow])
    (fun r => by simp [List.mem_filter, mem_francisWindow])
    (fun k hk => by
      rw [hmem] at hk
      exact ⟨⟨by omega, by omega⟩, show (a : ℕ) ≤ k + 1 by omega, show (k : ℕ) ≤ a + 3 by omega⟩),
    hvβ]
  · intro q hq1 hq2 hC k hk
    have hC' : ¬ ((a : ℕ) ≤ q + 1) := hC
    rw [hmem] at hk
    exact hB k q (by omega) (by omega)
  · intro r hr1 hr2 hR k hk
    have hR' : ¬ ((r : ℕ) ≤ a + 3) := hR
    rw [hmem] at hk
    exact hB r k (by omega) (by omega)

/-- **The last step of Algorithm 7.5.1 on a window, exactly**: on the pair `(a+1, a+2)` of the
window `[p, a + 3)` with the pattern `IsFrancisBulge p m (a + 1)`, the restricted updates compute
the block similarity by the reflector, which is upper Hessenberg. -/
theorem francis_step_last {p m : ℕ} {a b c : Fin n} (hb : (b : ℕ) = a + 1)
    (hc : (c : ℕ) = a + 2) (hpa : p ≤ a) (ham : (a : ℕ) + 3 = m) {H : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsFrancisBulge p m (a + 1) H) {v : Fin n → ℝ} {β : ℝ}
    (hvβ : Id.run (houseOn pure [b, c] (fun i => H i a)) = (v, β)) :
    Id.run (francisReflect pure [b, c] (fun i => H i a)
        ((francisWindow n p m).filter fun j => (a : ℕ) ≤ j) (francisWindow n p m) H) =
      (blockConj p m (1 - β • vecMulVec v v) H, (v, β)) ∧
      (blockConj p m (1 - β • vecMulVec v v) H).IsUpperHessenberg ∧
      (β = 0 ∨ β * (v ⬝ᵥ v) = 2) ∧ (∀ i : Fin n, (i : ℕ) ≤ a ∨ (a : ℕ) + 2 < i → v i = 0) := by
  have hmem : ∀ i : Fin n, i ∈ [b, c] ↔ (a : ℕ) + 1 ≤ i ∧ (i : ℕ) ≤ a + 2 := fun i => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc]
    omega
  have hnd : [b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, hb, hc,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  have hspec := houseOn_spec hnd (List.cons_ne_nil _ _) (fun i => H i a)
  rw [hvβ] at hspec
  obtain ⟨-, hvout, hβ, -, hPu⟩ := hspec
  have hv : ∀ i : Fin n, (i : ℕ) ≤ a ∨ (a : ℕ) + 2 < i → v i = 0 := fun i hi =>
    hvout i fun h => by rw [hmem] at h; omega
  have hPu' : ∀ i : Fin n, (i : ℕ) = a + 2 →
      ((1 - β • vecMulVec v v) *ᵥ fun i => H i a) i = 0 := fun i h => by
    rw [hPu]
    have hib : i ≠ b := fun e => by rw [e] at h; omega
    simp only [List.head_cons, hib, ↓reduceIte, (hmem i).2 ⟨by omega, h.le⟩]
  refine ⟨?_, hB.conj_last ham hv hPu' (fun j hj r => by rw [show j = a from Fin.ext hj]),
    hβ, hv⟩
  rw [francisReflect_window (p := p) (m := m) hnd (List.cons_ne_nil _ _) _
    ((nodup_francisWindow n p m).filter _) (nodup_francisWindow n p m)
    (C := fun j => (a : ℕ) ≤ j) (R := fun _ => True)
    (fun q => by simp [List.mem_filter, mem_francisWindow])
    (fun r => by simp [mem_francisWindow])
    (fun k hk => by
      rw [hmem] at hk
      exact ⟨⟨by omega, by omega⟩, show (a : ℕ) ≤ k by omega, trivial⟩), hvβ]
  · intro q hq1 hq2 hC k hk
    have hC' : ¬ ((a : ℕ) ≤ q) := hC
    rw [hmem] at hk
    exact hB k q (by omega) (by omega)
  · intro r _ _ hR
    exact absurd trivial hR

end FrancisSpec

/-! ### Algorithm 7.5.1 on a window -/

section FrancisWindow

variable [NeZero n]

/-- **The invariant of the loop of Algorithm 7.5.1 on the window `[p, m)`** after `k` further
steps: the pattern before the step on `(p+k+1, p+k+2, p+k+3)`, the accumulated block similarity
by `Z = householderProduct data`, the `β` dichotomy and the support of every reflector in the
window, and every reflector after the first acting trivially on the indices `≤ p`. -/
private def FrancisWinInv (p m : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (p₀ : (Fin n → ℝ) × ℝ)
    (k : ℕ) (st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)) : Prop :=
  IsFrancisBulge p m (p + k + 1) st.1 ∧ st.1 = blockConj p m (householderProduct st.2) H ∧
    (∀ q ∈ st.2, (q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2) ∧
      ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) ∧
    ∃ rest, st.2 = p₀ :: rest ∧ ∀ q ∈ rest, ∀ i : Fin n, (i : ℕ) ≤ p → q.1 i = 0

/-- The loop of Algorithm 7.5.1 at the exact model keeps `FrancisWinInv`. -/
private theorem francisWinLoop_inv {p m : ℕ} (hm : m ≤ n) {H : Matrix (Fin n) (Fin n) ℝ}
    {p₀ : (Fin n → ℝ) × ℝ} {st : Matrix (Fin n) (Fin n) ℝ × List ((Fin n → ℝ) × ℝ)}
    (hst : FrancisWinInv p m H p₀ 0 st) :
    ∀ k, p + k + 3 ≤ m → FrancisWinInv p m H p₀ k
      (((List.range k).map fun k => francisTri n (p + (k + 1))).foldl
        (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t)) st) := by
  intro k
  induction k with
  | zero => intro _; simpa using hst
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append]
    obtain ⟨hB, hconj, hdata, rest, hrest, h0⟩ := ih (by omega)
    generalize ((List.range k).map fun k => francisTri n (p + (k + 1))).foldl
      (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t)) st = st' at *
    obtain ⟨ha, hb, hc⟩ := francisTri_val (n := n) (k := p + (k + 1)) (by omega)
    set u : Fin n → ℝ := fun i => st'.1 i ⟨((francisTri n (p + (k + 1))).1 : ℕ) - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) (francisTri n (p + (k + 1))).1.isLt⟩ with hu
    obtain ⟨⟨v, β⟩, hvβ⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n (p + (k + 1))).1,
        (francisTri n (p + (k + 1))).2.1, (francisTri n (p + (k + 1))).2.2] u) = vβ :=
      ⟨_, rfl⟩
    obtain ⟨hstep, hB', hβ', hv', -⟩ := francis_step (p := p) (m := m) (by rw [hb, ha])
      (by rw [hc, ha]) (by rw [ha]; omega) (by rw [ha]; omega) (H := st'.1) (u := u)
      (by rw [ha, ← Nat.add_assoc]; exact hB)
      (fun j _ hj r => by
        have hj' : j = ⟨((francisTri n (p + (k + 1))).1 : ℕ) - 1,
            lt_of_le_of_lt (Nat.sub_le _ _) (francisTri n (p + (k + 1))).1.isLt⟩ :=
          Fin.ext (by change (j : ℕ) = (francisTri n (p + (k + 1))).1 - 1; omega)
        rw [hu, hj']) hvβ
    have hvS : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v i = 0 := fun i hi =>
      hv' i (by rw [ha]; omega)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    change FrancisWinInv p m H p₀ (k + 1)
      ((Id.run (francisReflect pure _ _ _ _ st'.1)).1,
        st'.2 ++ [(Id.run (francisReflect pure _ _ _ _ st'.1)).2])
    rw [hstep]
    refine ⟨by rw [ha] at hB'; exact hB', ?_, ?_, rest ++ [(v, β)],
      by rw [hrest]; rfl, ?_⟩
    · rw [hconj, blockConj_blockConj (isBlockSupported_reflector β hvS),
        householderProduct_concat]
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hdata q hq
      · rw [List.mem_singleton.1 hq]; exact ⟨hβ', hvS⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h0 q hq
      · rw [List.mem_singleton.1 hq]
        exact fun i hi => hv' i (Or.inl (by rw [ha]; omega))

/-- The consecutive triples of the window `[p, m)`, `m ≥ p + 3`: the first, then the others. -/
private theorem francisTriples_francisWindow_cons {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m) :
    francisTriples (francisWindow n p m) =
      francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1)) := by
  rw [francisTriples_francisWindow hm, show m - p - 2 = m - p - 3 + 1 by omega,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- The last triple of the window `[p, m)` is `(m - 3, m - 2, m - 1)`. -/
private theorem getLast_francisTri {p m : ℕ} (hpm : p + 3 ≤ m) :
    (francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))).getLast
      (List.cons_ne_nil _ _) = francisTri n (m - 3) := by
  have hl : (francisTri n p :: (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))) =
      (List.range (m - p - 2)).map fun k => francisTri n (p + k) := by
    rw [show m - p - 2 = m - p - 3 + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    rfl
  rw [List.getLast_congr _ (by simp; omega) hl, List.getLast_map, List.getLast_range,
    show p + (m - p - 2 - 1) = m - 3 by omega]

/-- The unfolded exact run of Algorithm 7.5.1 on the window `[p, m)`. -/
private theorem algorithm_7_5_1_window_eq {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (algorithm_7_5_1 pure (francisWindow n p m) H) =
      let L := (List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))
      let tl := (francisTri n p :: L).getLast (List.cons_ne_nil _ _)
      let u := Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
        (francisTri n p).2.2 tl.2.1 tl.2.2 H)
      let st := Id.run (francisReflect pure [(francisTri n p).1, (francisTri n p).2.1,
        (francisTri n p).2.2] u
        ((francisWindow n p m).filter fun j => ((francisTri n p).1 : ℕ) ≤ j + 1)
        ((francisWindow n p m).filter fun i => (i : ℕ) ≤ (francisTri n p).1 + 3) H)
      let st := Id.run (L.foldlM (francisChaseStep pure (francisWindow n p m)) (st.1, [st.2]))
      let r := Id.run (francisReflect pure [tl.2.1, tl.2.2] (fun i => st.1 i tl.1)
        ((francisWindow n p m).filter fun j => (tl.1 : ℕ) ≤ j) (francisWindow n p m) st.1)
      (r.1, st.2 ++ [r.2]) := by
  rw [algorithm_7_5_1, francisTriples_francisWindow_cons hm hpm]
  rfl

/-- The internal form of `algorithm_7_5_1_window`: besides the block similarity, the first
reflector and its action on the first column of `(H - a₁ I)(H - a₂ I)`. -/
private theorem algorithm_7_5_1_window_aux {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m)
    {H H' : Matrix (Fin n) (Fin n) ℝ} {data : List ((Fin n → ℝ) × ℝ)}
    (hH : H.IsUpperHessenberg)
    (h : Id.run (algorithm_7_5_1 pure (francisWindow n p m) H) = (H', data)) :
    householderProduct data ∈ orthogonalGroup (Fin n) ℝ ∧
      IsBlockSupported p m (householderProduct data) ∧
      (∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0) ∧
      H' = blockConj p m (householderProduct data) H ∧ H'.IsUpperHessenberg ∧
      ∃ v₀ β₀ rest, data = (v₀, β₀) :: rest ∧
        (∀ q ∈ rest, ∀ i : Fin n, (i : ℕ) ≤ p → q.1 i = 0) ∧
        (β₀ = 0 ∨ β₀ * (v₀ ⬝ᵥ v₀) = 2) ∧
        (1 - β₀ • vecMulVec v₀ v₀) *ᵥ Id.run (francisShiftVector pure (francisTri n p).1
          (francisTri n p).2.1 (francisTri n p).2.2 (francisTri n (m - 3)).2.1
          (francisTri n (m - 3)).2.2 H) = fun i => if i = (francisTri n p).1 then
            ‖(WithLp.toLp 2 (fun j : {j // j ∈ [(francisTri n p).1, (francisTri n p).2.1,
              (francisTri n p).2.2]} => Id.run (francisShiftVector pure (francisTri n p).1
                (francisTri n p).2.1 (francisTri n p).2.2 (francisTri n (m - 3)).2.1
                (francisTri n (m - 3)).2.2 H) j) :
              EuclideanSpace ℝ {j // j ∈ [(francisTri n p).1, (francisTri n p).2.1,
                (francisTri n p).2.2]})‖
          else if i ∈ [(francisTri n p).1, (francisTri n p).2.1, (francisTri n p).2.2] then 0
          else Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
            (francisTri n p).2.2 (francisTri n (m - 3)).2.1 (francisTri n (m - 3)).2.2 H) i := by
  obtain ⟨ha₀, hb₀, hc₀⟩ := francisTri_val (n := n) (k := p) (by omega)
  rw [algorithm_7_5_1_window_eq hm hpm] at h
  dsimp only at h
  rw [getLast_francisTri hpm] at h
  set u₀ := Id.run (francisShiftVector pure (francisTri n p).1 (francisTri n p).2.1
    (francisTri n p).2.2 (francisTri n (m - 3)).2.1 (francisTri n (m - 3)).2.2 H) with hu₀
  obtain ⟨⟨v₀, β₀⟩, hvβ₀⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n p).1,
      (francisTri n p).2.1, (francisTri n p).2.2] u₀) = vβ := ⟨_, rfl⟩
  obtain ⟨hs₁, hB₁, hβ₁, hv₁, hPu₀⟩ := francis_step (p := p) (m := m) (by rw [hb₀, ha₀])
    (by rw [hc₀, ha₀]) (by rw [ha₀]) (by rw [ha₀]; omega)
    (isFrancisBulge_of_isUpperHessenberg hH _ _ _) (u := u₀) (fun j hj1 hj2 => by omega) hvβ₀
  rw [hs₁] at h
  dsimp only at h
  rw [List.idRun_foldlM] at h
  set P₀ := 1 - β₀ • vecMulVec v₀ v₀ with hP₀
  have hv₁S : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v₀ i = 0 := fun i hi =>
    hv₁ i (by rw [ha₀]; omega)
  have hinv0 : FrancisWinInv p m H (v₀, β₀) 0 (blockConj p m P₀ H, [(v₀, β₀)]) := by
    refine ⟨by rw [ha₀] at hB₁; simpa using hB₁, ?_, ?_, [], rfl, by simp⟩
    · simp only [householderProduct_cons, householderProduct_nil, Matrix.mul_one, hP₀]
    · intro q hq
      rw [List.mem_singleton.1 hq]
      exact ⟨hβ₁, hv₁S⟩
  have hloop := francisWinLoop_inv hm hinv0 (m - p - 3) (by omega)
  set st := ((List.range (m - p - 3)).map fun k => francisTri n (p + (k + 1))).foldl
    (fun st t => Id.run (francisChaseStep pure (francisWindow n p m) st t))
    (blockConj p m P₀ H, [(v₀, β₀)]) with hst
  obtain ⟨hB₂, hconj₂, hdata₂, rest, hrest, hrest0⟩ := hloop
  obtain ⟨hvN0, hvN1, hvN2⟩ := francisTri_val (n := n) (k := m - 3) (by omega)
  obtain ⟨⟨v₃, β₃⟩, hvβ₃⟩ : ∃ vβ, Id.run (houseOn pure [(francisTri n (m - 3)).2.1,
      (francisTri n (m - 3)).2.2] (fun i => st.1 i (francisTri n (m - 3)).1)) = vβ :=
    ⟨_, rfl⟩
  have hB₂' : IsFrancisBulge p m ((francisTri n (m - 3)).1 + 1) st.1 := by
    rw [hvN0, show m - 3 + 1 = p + (m - p - 3) + 1 by omega]
    exact hB₂
  obtain ⟨hs₃, hHess', hβ₃, hv₃⟩ := francis_step_last (p := p) (m := m)
    (by rw [hvN1, hvN0]) (by rw [hvN2, hvN0]) (by rw [hvN0]; omega) (by rw [hvN0]; omega) hB₂'
    hvβ₃
  rw [hs₃] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hv₃S : ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → v₃ i = 0 := fun i hi =>
    hv₃ i (by rw [hvN0]; omega)
  have hall : ∀ q ∈ st.2 ++ [(v₃, β₃)], (q.2 = 0 ∨ q.2 * (q.1 ⬝ᵥ q.1) = 2) ∧
      ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0 := by
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hdata₂ q hq
    · rw [List.mem_singleton.1 hq]; exact ⟨hβ₃, hv₃S⟩
  refine ⟨householderProduct_mem_orthogonalGroup fun q hq => (hall q hq).1,
    isBlockSupported_householderProduct fun q hq => (hall q hq).2,
    fun q hq => (hall q hq).2, ?_, hHess',
    v₀, β₀, rest ++ [(v₃, β₃)], by rw [hrest]; rfl, ?_, hβ₁, hPu₀⟩
  · rw [hconj₂, blockConj_blockConj (isBlockSupported_reflector β₃ hv₃S),
      householderProduct_concat]
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hrest0 q hq
    · rw [List.mem_singleton.1 hq]
      exact fun i hi => hv₃ i (Or.inl (by rw [hvN0]; omega))

/-- **Algorithm 7.5.1 on a window** (what Algorithm 7.5.2 runs on the unreduced block `H₂₂`): for an
upper Hessenberg `H` and a window `[p, m)` of at least three indices, the exact run `(H', data)`
has `Z = householderProduct data` orthogonal and acting on the window only, `H'` is the block
similarity `blockConj p m Z H` (`Zᵀ H Z` on the block `H₂₂`, `H` elsewhere), and `H'` is upper
Hessenberg. -/
theorem algorithm_7_5_1_window {p m : ℕ} (hm : m ≤ n) (hpm : p + 3 ≤ m)
    {H H' : Matrix (Fin n) (Fin n) ℝ} {data : List ((Fin n → ℝ) × ℝ)}
    (hH : H.IsUpperHessenberg)
    (h : Id.run (algorithm_7_5_1 pure (francisWindow n p m) H) = (H', data)) :
    householderProduct data ∈ orthogonalGroup (Fin n) ℝ ∧
      IsBlockSupported p m (householderProduct data) ∧
      H' = blockConj p m (householderProduct data) H ∧ H'.IsUpperHessenberg ∧
      ∀ q ∈ data, ∀ i : Fin n, ¬ (p ≤ (i : ℕ) ∧ (i : ℕ) < m) → q.1 i = 0 := by
  obtain ⟨hZ, hZS, hsupp, hH', hHess, -⟩ := algorithm_7_5_1_window_aux hm hpm hH h
  exact ⟨hZ, hZS, hH', hHess, hsupp⟩

end FrancisWindow

/-! ### Algorithm 7.5.1: the specification -/

section FrancisTheorem

variable {N : ℕ}

/-- A reflector `I - β v vᵀ` with `v` vanishing at `p` fixes `e_p`. -/
private theorem one_sub_smul_vecMulVec_mulVec_single {v : Fin n → ℝ} {p : Fin n} (hv : v p = 0)
    (β : ℝ) : (1 - β • vecMulVec v v) *ᵥ Pi.single p 1 = Pi.single p 1 := by
  funext i
  rw [one_sub_smul_vecMulVec_mulVec_apply, dotProduct_single, hv, zero_mul, mul_zero, sub_zero]

/-- A product of reflectors whose vectors vanish at `p` fixes `e_p`. -/
private theorem householderProduct_mulVec_single {data : List ((Fin n → ℝ) × ℝ)} {p : Fin n}
    (h : ∀ q ∈ data, q.1 p = 0) :
    householderProduct data *ᵥ Pi.single p 1 = Pi.single p 1 := by
  induction data with
  | nil => rw [householderProduct_nil, one_mulVec]
  | cons q data ih =>
    rw [householderProduct_cons, ← mulVec_mulVec,
      ih fun r hr => h r (List.mem_cons_of_mem _ hr),
      one_sub_smul_vecMulVec_mulVec_single (h q List.mem_cons_self)]

/-- A Householder reflector is symmetric, so an orthogonal one is an involution. -/
private theorem one_sub_smul_vecMulVec_mul_self_of_mem {v : Fin n → ℝ} {β : ℝ}
    (h : (1 - β • vecMulVec v v) ∈ orthogonalGroup (Fin n) ℝ) :
    (1 - β • vecMulVec v v) * (1 - β • vecMulVec v v) = 1 := by
  have h1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 h
  rwa [transpose_one_sub_smul_vecMulVec] at h1

/-- The exact first column of `francisShiftVector`. -/
theorem francisShiftVector_pure (a b c m l : Fin n) (H : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (francisShiftVector pure a b c m l H) = fun i =>
      if i = a then H a a * H a a + H a b * H b a - (H m m + H l l) * H a a +
          (H m m * H l l - H m l * H l m)
      else if i = b then H b a * (H a a + H b b - (H m m + H l l))
      else if i = c then H b a * H c b else 0 := rfl

/-- The polynomial of the double shift, evaluated at `H`. -/
private theorem aeval_francisPoly (H : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    aeval H (X ^ 2 - C s * X + C t) = H * H - s • H + t • 1 := by
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, sq]

/-- **Algorithm 7.5.1 computes a Francis step** ([golub2013matrix] Algorithm 7.5.1, header): for
`H ∈ ℝ^{n×n}` unreduced upper Hessenberg, `n ≥ 3`, and `s`, `t` the trace and determinant of the
trailing `2 × 2` block (so that `H² - s H + t I = (H - a₁ I)(H - a₂ I)`, (7.5.8)), the exact run
`(H', data)` of the program on the full window has `Z = householderProduct data` orthogonal,
`H' = Zᵀ H Z` upper Hessenberg, `Zᵀ (H² - s H + t I)` upper triangular and `Z e₁` parallel to
`(H² - s H + t I) e₁`; so `H'` is a Francis step of `H` (`Matrix.IsFrancisStep`). The proof is the
bulge-chasing invariant `IsFrancisBulge` (`algorithm_7_5_1_window` at the full window), and the
implicit-shift principle `Matrix.IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval` for
the triangularity. -/
theorem algorithm_7_5_1_spec {H H' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {data : List ((Fin (N + 3) → ℝ) × ℝ)} (hH : IsUnreduced H)
    (h : Id.run (algorithm_7_5_1 pure (List.finRange (N + 3)) H) = (H', data)) :
    let s := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      H (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        H (Fin.last (N + 2)) (Fin.last (N + 2)) -
      H (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        H (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    householderProduct data ∈ orthogonalGroup (Fin (N + 3)) ℝ ∧
      H' = (householderProduct data)ᵀ * H * householderProduct data ∧ H'.IsUpperHessenberg ∧
      ((householderProduct data)ᵀ * (H * H - s • H + t • 1)).IsUpperTriangular ∧
      (householderProduct data).col 0 ∈ Submodule.span ℝ {(H * H - s • H + t • 1).col 0} ∧
      IsFrancisStep s t H H' := by
  intro s t
  have hHess : H.IsUpperHessenberg := hH.1
  rw [← francisWindow_zero] at h
  obtain ⟨hZo, -, -, hH'eq, hHess', v₀, β₀, rest, hdata, hrest0, hβ₁, hPu₀⟩ :=
    algorithm_7_5_1_window_aux (p := 0) (m := N + 3) le_rfl (by omega) hHess h
  rw [blockConj_zero] at hH'eq
  obtain ⟨hv0, hv1, hv2⟩ := francisTri_val (n := N + 3) (k := 0) (by omega)
  obtain ⟨-, hvm, hvl⟩ := francisTri_val (n := N + 3) (k := N + 3 - 3) (by omega)
  have h0 : (francisTri (N + 3) 0).1 = 0 := Fin.ext (by rw [hv0]; simp)
  have h1 : (francisTri (N + 3) 0).2.1 = 1 := Fin.ext (by rw [hv1]; simp)
  have h2 : (francisTri (N + 3) 0).2.2 = ⟨2, by omega⟩ := Fin.ext (by rw [hv2])
  have hm : (francisTri (N + 3) (N + 3 - 3)).2.1 = (Fin.last (N + 1)).castSucc :=
    Fin.ext (by rw [hvm]; simp only [Fin.val_castSucc, Fin.val_last]; omega)
  have hl : (francisTri (N + 3) (N + 3 - 3)).2.2 = Fin.last (N + 2) :=
    Fin.ext (by rw [hvl]; simp only [Fin.val_last]; omega)
  set u₀ := Id.run (francisShiftVector pure (francisTri (N + 3) 0).1 (francisTri (N + 3) 0).2.1
    (francisTri (N + 3) 0).2.2 (francisTri (N + 3) (N + 3 - 3)).2.1
    (francisTri (N + 3) (N + 3 - 3)).2.2 H) with hu₀
  set Z := householderProduct data with hZ
  set P₀ := 1 - β₀ • vecMulVec v₀ v₀ with hP₀
  -- the first column of `Z`
  have hZcol : Z *ᵥ Pi.single 0 1 = P₀ *ᵥ Pi.single 0 1 := by
    rw [hZ, hdata, householderProduct_cons, ← mulVec_mulVec,
      householderProduct_mulVec_single fun q hq => hrest0 q hq 0 (by simp)]
  set M := H * H - s • H + t • 1 with hM
  have hMu : M.col 0 = u₀ := by
    obtain ⟨fx, fy, fz, frest⟩ := francis_first_column hHess s t
    funext i
    rw [hu₀, francisShiftVector_pure, h0, h1, h2, hm, hl, col_apply]
    by_cases hi0 : i = 0
    · subst hi0; simp only [↓reduceIte]; exact fx
    by_cases hi1 : i = 1
    · subst hi1; simp only [hi0, ↓reduceIte]; exact fy
    by_cases hi2 : i = ⟨2, by omega⟩
    · subst hi2; simp only [hi0, hi1, ↓reduceIte]; exact fz
    · simp only [hi0, hi1, hi2, ↓reduceIte]
      refine frest i ?_
      have : (i : ℕ) ≠ 0 := fun e => hi0 (Fin.ext e)
      have : (i : ℕ) ≠ 1 := fun e => hi1 (Fin.ext e)
      have : (i : ℕ) ≠ 2 := fun e => hi2 (Fin.ext e)
      omega
  -- the first reflector is an involution mapping `u₀` to a multiple of `e₀`
  have hP₀o : P₀ ∈ orthogonalGroup (Fin (N + 3)) ℝ := by
    refine one_sub_smul_vecMulVec_mem_orthogonalGroup ?_
    rcases hβ₁ with hb | hb
    · rw [hb, zero_mul]
    · rw [hb, sub_self, mul_zero]
  have hPP : P₀ * P₀ = 1 := one_sub_smul_vecMulVec_mul_self_of_mem hP₀o
  set cn := ‖(WithLp.toLp 2 (fun j : {j // j ∈ [(francisTri (N + 3) 0).1,
    (francisTri (N + 3) 0).2.1, (francisTri (N + 3) 0).2.2]} => u₀ j) :
      EuclideanSpace ℝ {j // j ∈ [(francisTri (N + 3) 0).1, (francisTri (N + 3) 0).2.1,
        (francisTri (N + 3) 0).2.2]})‖ with hcn
  have hPu : P₀ *ᵥ u₀ = cn • Pi.single 0 1 := by
    rw [hPu₀]
    funext i
    rw [Pi.smul_apply, Pi.single_apply, h0]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte, smul_zero]
      split_ifs with hl'
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl'
        rw [hu₀, francisShiftVector_pure]
        simp [h0, hl'.1, hl'.2.1, hl'.2.2]
  have hu0 : u₀ ≠ 0 := by
    intro hu
    have hz := congrFun (hMu.trans hu) ⟨2, by omega⟩
    rw [col_apply, Pi.zero_apply, hM, (francis_first_column hHess s t).2.2.1] at hz
    have hsub := (isUnreduced_iff.1 hH).2
    have e10 : H 1 0 ≠ 0 := by
      convert hsub 0 (by omega) using 2 <;> exact Fin.ext (by simp)
    have e21 : H ⟨2, by omega⟩ 1 ≠ 0 := by
      convert hsub 1 (by omega) using 2
      exact Fin.ext (by simp)
    exact mul_ne_zero e10 e21 hz
  have hcn0 : cn ≠ 0 := by
    intro hc
    refine hu0 ?_
    rw [← one_mulVec u₀, ← hPP, ← mulVec_mulVec, hPu, hc, zero_smul, mulVec_zero]
  have hPe : P₀ *ᵥ Pi.single 0 1 = cn⁻¹ • u₀ := by
    have h' : u₀ = cn • (P₀ *ᵥ Pi.single 0 1) := by
      rw [← mulVec_smul, ← hPu, mulVec_mulVec, hPP, one_mulVec]
    rw [h', smul_smul, inv_mul_cancel₀ hcn0, one_smul]
  have hcol : Z.col 0 ∈ Submodule.span ℝ {M.col 0} := by
    rw [← mulVec_single_one Z 0, hZcol, hPe, hMu]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hstarZ : star Z = Zᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have htri : (Zᵀ * M).IsUpperTriangular := by
    have := IsUnreducedUpperHessenberg.isUpperTriangular_star_mul_aeval hH
      (X ^ 2 - C s * X + C t) hZo (by rw [hstarZ, ← hH'eq]; exact hHess')
      (by rw [aeval_francisPoly, mulVec_single_one]; exact hcol)
    rwa [aeval_francisPoly, hstarZ] at this
  exact ⟨hZo, hH'eq, hHess', htri, hcol, Z, hZo, hH'eq, hHess', htri⟩

end FrancisTheorem

section FrancisEssential

variable {N : ℕ}

/-- **§7.5.5: "we can assert that `Z₁` essentially equals `Z` provided that the upper Hessenberg
matrices `Zᵀ H Z` and `Z₁ᵀ H Z₁` are each unreduced"** — the implicit Q theorem (the book cites
"Theorem 7.4.3", it is Theorem 7.4.2). For `H` unreduced and `M = H² - s H + t I` nonsingular, the
output `H'` of Algorithm 7.5.1 is `D (Zᵀ H Z) D` for a `±1` diagonal `D`, `Z` the orthogonal factor
of the explicit QR factorization `M = Z R` (`Matrix.qrQ`); and when the trailing eigenvalues are a
complex conjugate pair `a, ā` (`s = 2 Re a`, `t = |a|²`, `a` not an eigenvalue), `H'` is, over `ℂ`,
the same `±1` diagonal similarity of the double-shift QR step `H₂` of (7.5.6)–(7.5.7). -/
theorem algorithm_7_5_1_essential {H H' : Matrix (Fin (N + 3)) (Fin (N + 3)) ℝ}
    {data : List ((Fin (N + 3) → ℝ) × ℝ)} (hH : IsUnreduced H)
    (h : Id.run (algorithm_7_5_1 pure (List.finRange (N + 3)) H) = (H', data)) :
    let s := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc +
      H (Fin.last (N + 2)) (Fin.last (N + 2))
    let t := H (Fin.last (N + 1)).castSucc (Fin.last (N + 1)).castSucc *
        H (Fin.last (N + 2)) (Fin.last (N + 2)) -
      H (Fin.last (N + 1)).castSucc (Fin.last (N + 2)) *
        H (Fin.last (N + 2)) (Fin.last (N + 1)).castSucc
    IsUnit (H * H - s • H + t • 1).det →
    ∃ d : Fin (N + 3) → ℝ, (∀ i, d i = 1 ∨ d i = -1) ∧
      H' = diagonal d * ((qrQ (H * H - s • H + t • 1))ᵀ * H * qrQ (H * H - s • H + t • 1)) *
        diagonal d ∧
      ∀ a : ℂ, s = 2 * a.re → t = Complex.normSq a → a ∉ spectrum ℂ H.complexify →
        H'.complexify = (diagonal d).complexify * doubleShiftQrStep H.complexify a *
          (diagonal d).complexify := by
  intro s t hM
  obtain ⟨-, -, -, -, -, hF⟩ := algorithm_7_5_1_spec hH h
  obtain ⟨d, hd, hH'⟩ := hF.eq_diagonal_conj hH hM
  refine ⟨d, hd, hH', fun a hs ht ha => ?_⟩
  have hds := (double_shift_real H ha).2.1
  have hMM : H * H - (2 * a.re) • H + Complex.normSq a • 1 = H * H - s • H + t • 1 := by
    rw [hs, ht]
  rw [hds, hMM, hH', complexify_mul, complexify_mul]

end FrancisEssential

/-! ### §7.5.6 The overall process -/

section StandardizeProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **The standardization of a `2 × 2` diagonal block with real eigenvalues** (the last step of
Algorithm 7.5.2, "upper triangularize all 2-by-2 diagonal blocks in `H` that have real
eigenvalues and accumulate the transformations"; the book gives no algorithm). For the block
`[w x; y z]` in rows and columns `(i, j)`, `j = i + 1`: `δ = w - z`, `d = δ² + 4xy`; if `d ≥ 0`,
the eigenvalue of larger modulus `λ = (w + z)/2 + sign(δ) √d / 2` (`sign(δ)·` a copy or a negation,
exact), its eigenvector `(x, λ - w)` (or `(λ - z, y)` when `x = 0`), `(c, s) = givens` of it
(Algorithm 5.1.3), and the rotation applied to rows `i, j` over the columns `≥ i`, to columns
`i, j` over the rows `≤ j`, and to the columns `i, j` of `Q`; if `d < 0` nothing is done. Every
arithmetic operation is rounded, the comparisons are exact. -/
noncomputable def triangularize2x2 (i j : Fin n)
    (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let H := HQ.1
  let δ ← rnd (H i i - H j j)
  let d ← rnd ((← rnd (δ * δ)) + (← rnd ((← rnd (4 * H i j)) * H j i)))
  if 0 ≤ d then do
    let m ← rnd ((← rnd (H i i + H j j)) / 2)
    let r ← rnd ((← rnd √d) / 2)
    let lam ← rnd (m + if 0 ≤ δ then r else -r)
    let ab ← if H i j = 0 then do pure ((← rnd (lam - H j j)), H j i)
      else do pure (H i j, (← rnd (lam - H i i)))
    let cs ← algorithm_5_1_3 rnd ab.1 ab.2
    let H ← givensApplyLeft rnd i j cs.1 cs.2 ((List.finRange n).filter fun q => i ≤ q) H
    let H ← givensApplyRight rnd i j cs.1 cs.2 ((List.finRange n).filter fun r => r ≤ j) H
    let Q ← givensApplyRight rnd i j cs.1 cs.2 (List.finRange n) HQ.2
    pure (H, Q)
  else pure HQ

end StandardizeProgram

section Standardize

/-- The `(k, j)` entry of a matrix conjugated by a plane rotation. -/
private theorem conj_planeRotation_apply_kj {j k : Fin n} (hjk : j ≠ k) (c s : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ((planeRotation j k c s)ᵀ * M * planeRotation j k c s) k j
      = -s * (c * M j j + s * M j k) + c * (c * M k j + s * M k k) := by
  simp [transpose_planeRotation_mul_apply hjk, mul_planeRotation_apply hjk, Ne.symm hjk]
  ring

/-- A plane rotation in the plane `(i, j)` is block diagonal for any block index with
`p i = p j`. -/
private theorem planeRotation_apply_eq_zero_of_ne {i j : Fin n} (hij : i ≠ j) {p : Fin n → ℕ}
    (hp : p i = p j) (c s : ℝ) {r q : Fin n} (hrq : p r ≠ p q) : planeRotation i j c s r q = 0 := by
  rw [planeRotation_apply hij]
  have hrq' : r ≠ q := fun e => hrq (by rw [e])
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all

/-- **Conjugation by a rotation in the plane of one diagonal block keeps a block triangular
structure** (the "rest of the quasi-triangular structure" of Algorithm 7.5.2's last step): if
`p i = p j`, `Gᵀ H G` is block upper triangular for `p` whenever `H` is. -/
theorem blockTriangular_givens_conj {i j : Fin n} (hij : i ≠ j) {p : Fin n → ℕ} (hp : p i = p j)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.BlockTriangular p) (c s : ℝ) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s).BlockTriangular p := by
  have hG : (givensRotation i j c s).BlockTriangular p := fun r q hqr =>
    planeRotation_apply_eq_zero_of_ne hij hp c (-s) hqr.ne'
  have hGt : (givensRotation i j c s)ᵀ.BlockTriangular p := fun r q hqr => by
    rw [transpose_apply]
    exact planeRotation_apply_eq_zero_of_ne hij hp c (-s) hqr.ne
  exact (hGt.mul hH).mul hG

/-- The first column of `G(i, j, θ)`: `c e_i - s e_j`. -/
private theorem givensRotation_mulVec_single {i j : Fin n} (hij : i ≠ j) (c s : ℝ) :
    givensRotation i j c s *ᵥ Pi.single i 1 = c • Pi.single i 1 - s • Pi.single j 1 := by
  funext t
  rw [mulVec_single_one, col_apply, givensRotation, planeRotation_apply hij]
  by_cases hti : t = i
  · subst hti; simp [hij]
  · by_cases htj : t = j
    · subst htj; simp [hij.symm]
    · simp [hti, htj]

/-- The subdiagonal entry of `Gᵀ H G` in the plane `(i, j)`. -/
private theorem givens_conj_apply_ji {i j : Fin n} (hij : i ≠ j) (c s : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) j i =
      s * (c * H i i - s * H i j) + c * (c * H j i - s * H j j) := by
  rw [givensRotation, conj_planeRotation_apply_kj hij]
  ring

/-- `givens(a, 0) = (1, 0)` exactly. -/
private theorem algorithm_5_1_3_pure_zero (a : ℝ) : Id.run (algorithm_5_1_3 pure a 0) = (1, 0) := by
  simp [algorithm_5_1_3]

/-- The rotation with `c = 1`, `s = 0` is the identity. -/
private theorem givensRotation_one_zero {i j : Fin n} (hij : i ≠ j) :
    givensRotation i j 1 0 = 1 := by
  ext r q
  rw [givensRotation, planeRotation_apply hij, one_apply]
  split_ifs <;> simp_all

/-- **The eigenvector rotation triangularizes the block**: if `(a, b) ≠ 0`-or-`b = 0` is an
eigenvector of `[w x; y z]` for `λ` and `(c, s)` satisfy `c² + s² = 1`, `s a + c b = 0`, then the
subdiagonal entry `s (c w - s x) + c (c y - s z)` of the rotated block vanishes, provided it does
when `a = b = 0` (where `givens` returns `(1, 0)` and `y = 0`). -/
private theorem givens_entry_eq_zero {w x y z lam a b c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1)
    (hz : s * a + c * b = 0) (h1 : w * a + x * b = lam * a) (h2 : y * a + z * b = lam * b)
    (h0 : a = 0 → b = 0 → s * (c * w - s * x) + c * (c * y - s * z) = 0) :
    s * (c * w - s * x) + c * (c * y - s * z) = 0 := by
  set ρ := c * a - s * b with hρ
  have ha : a = ρ * c := by rw [hρ]; linear_combination (-a) * hcs + s * hz
  have hb : b = -ρ * s := by rw [hρ]; linear_combination (-b) * hcs + c * hz
  by_cases hρ0 : ρ = 0
  · exact h0 (by rw [ha, hρ0, zero_mul]) (by rw [hb, hρ0, neg_zero, zero_mul])
  · have e1 : ρ * (w * c - x * s) = ρ * (lam * c) := by
      rw [ha, hb] at h1; linear_combination h1
    have e2 : ρ * (y * c - z * s) = ρ * (-(lam * s)) := by
      rw [ha, hb] at h2; linear_combination h2
    have e1' := mul_left_cancel₀ hρ0 e1
    have e2' := mul_left_cancel₀ hρ0 e2
    linear_combination s * e1' + c * e2'

end Standardize


section Standardize2

/-- **Exact semantics of `triangularize2x2`**: if rows `i`, `j = i + 1` vanish in the columns
`< i` and columns `i`, `j` vanish in the rows `> j` (the block is a diagonal block of a block upper
triangular `H`), the program returns `(Gᵀ H G, Q G)` for a rotation `G = G(i, j, θ)`,
`c² + s² = 1` (so `G` is orthogonal, `givensRotation_mem_orthogonalGroup`), and when the block
`[w x; y z]` has real eigenvalues, `(w - z)² + 4xy ≥ 0`, the rotated block is upper triangular:
the first column of `G` is an eigenvector of the block. With `d < 0` nothing is done.
Block triangular structure with `i`, `j` in one block is kept
(`blockTriangular_givens_conj`). -/
theorem triangularize2x2_spec {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (H Q : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ q : Fin n, (q : ℕ) < i → H i q = 0 ∧ H j q = 0)
    (hcol : ∀ r : Fin n, (j : ℕ) < r → H r i = 0 ∧ H r j = 0) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      Id.run (triangularize2x2 pure i j (H, Q)) =
        ((givensRotation i j c s)ᵀ * H * givensRotation i j c s, Q * givensRotation i j c s) ∧
      (0 ≤ (H i i - H j j) ^ 2 + 4 * H i j * H j i →
        ((givensRotation i j c s)ᵀ * H * givensRotation i j c s) j i = 0) ∧
      ((H i i - H j j) ^ 2 + 4 * H i j * H j i < 0 →
        Id.run (triangularize2x2 pure i j (H, Q)) = (H, Q)) := by
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  set w := H i i with hw
  set x := H i j with hx
  set y := H j i with hy
  set z := H j j with hz
  set d := (w - z) * (w - z) + 4 * x * y with hd
  set lam := (w + z) / 2 + (if 0 ≤ w - z then √d / 2 else -(√d / 2)) with hlam
  set ab : ℝ × ℝ := if x = 0 then (lam - z, y) else (x, lam - w) with hab
  set cs := Id.run (algorithm_5_1_3 pure ab.1 ab.2) with hcs
  set G := givensRotation i j cs.1 cs.2 with hG
  set rest : ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ := fun ab =>
    (Id.run (givensApplyRight pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
      (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 ((List.finRange n).filter fun r => r ≤ j)
      (Id.run (givensApplyLeft pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
        (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 ((List.finRange n).filter fun q => i ≤ q) H))),
      Id.run (givensApplyRight pure i j (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).1
        (Id.run (algorithm_5_1_3 pure ab.1 ab.2)).2 (List.finRange n) Q)) with hrest
  have hrun : Id.run (triangularize2x2 pure i j (H, Q)) = if 0 ≤ d then rest ab else (H, Q) := by
    rw [hab, apply_ite rest]
    rfl
  by_cases hd0 : 0 ≤ d
  swap
  · refine ⟨1, 0, by norm_num, ?_, fun h => absurd (by rw [hd]; nlinarith) hd0,
      fun _ => by rw [hrun, ite_eq_right hd0]⟩
    rw [hrun, ite_eq_right hd0, givensRotation_one_zero hne, transpose_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_one]
  obtain ⟨hcs1, hcs2, -⟩ := algorithm_5_1_3_spec ab.1 ab.2
  rw [← hcs] at hcs1 hcs2
  refine ⟨cs.1, cs.2, hcs1, ?_, fun _ => ?_, fun h => absurd hd0 (by rw [hd]; nlinarith)⟩
  · rw [hrun, ite_eq_left hd0]
    change (Id.run (givensApplyRight pure i j cs.1 cs.2 ((List.finRange n).filter fun r => r ≤ j)
        (Id.run (givensApplyLeft pure i j cs.1 cs.2 ((List.finRange n).filter fun q => i ≤ q) H))),
        Id.run (givensApplyRight pure i j cs.1 cs.2 (List.finRange n) Q)) = _
    have hL : Id.run (givensApplyLeft pure i j cs.1 cs.2
        ((List.finRange n).filter fun q => i ≤ q) H) = Gᵀ * H := by
      rw [givensApplyLeft_spec hne _ _ ((List.nodup_finRange n).filter _)]
      ext r q
      rw [of_apply]
      split_ifs with hq
      · rfl
      · have hq' : (q : ℕ) < i := by
          have : ¬ i ≤ q := fun h =>
            hq (List.mem_filter.2 ⟨List.mem_finRange q, decide_eq_true h⟩)
          rw [Fin.le_def] at this
          omega
        obtain ⟨h1, h2⟩ := hrow q hq'
        have hGq : (Gᵀ * H) r q = (Gᵀ *ᵥ fun p => H p q) r := rfl
        rw [hGq, givensRotation_transpose_mulVec_apply hne]
        split_ifs with hri hrj
        · rw [hri, h1, h2]; ring
        · rw [hrj, h1, h2]; ring
        · rfl
    have hR : Id.run (givensApplyRight pure i j cs.1 cs.2
        ((List.finRange n).filter fun r => r ≤ j) (Gᵀ * H)) = Gᵀ * H * G := by
      rw [givensApplyRight_spec hne _ _ ((List.nodup_finRange n).filter _)]
      ext r q
      rw [of_apply]
      split_ifs with hr
      · rfl
      · have hr' : (j : ℕ) < r := by
          have : ¬ r ≤ j := fun h =>
            hr (List.mem_filter.2 ⟨List.mem_finRange r, decide_eq_true h⟩)
          rw [Fin.le_def] at this
          omega
        have hri : r ≠ i := fun e => by rw [e] at hr'; omega
        have hrj : r ≠ j := fun e => by rw [e] at hr'; omega
        obtain ⟨h1, h2⟩ := hcol r hr'
        have hrow' : ∀ p, (Gᵀ * H) r p = H r p := fun p => by
          have hGp : (Gᵀ * H) r p = (Gᵀ *ᵥ fun t => H t p) r := rfl
          rw [hGp, givensRotation_transpose_mulVec_apply hne, ite_eq_right hri, ite_eq_right hrj]
        have hGq : (Gᵀ * H * G) r q = (Gᵀ *ᵥ (Gᵀ * H) r) q := by
          rw [mulVec_transpose]; rfl
        rw [hGq, givensRotation_transpose_mulVec_apply hne, hrow' q, hrow' i, hrow' j, h1, h2]
        split_ifs with hqi hqj
        · rw [hqi, h1]; ring
        · rw [hqj, h2]; ring
        · rfl
    rw [hL, hR, givensApplyRight_spec_of_forall_mem hne _ _ (List.nodup_finRange n)
      List.mem_finRange]
  · rw [givens_conj_apply_ji hne]
    have hsq := Real.mul_self_sqrt hd0
    have hkey : (lam - w) * (lam - z) = x * y := by
      rw [hlam]
      split_ifs <;> linear_combination (1 / 4 : ℝ) * hsq
    by_cases hx0 : x = 0
    · have hab' : ab = (lam - z, y) := by rw [hab, ite_eq_left hx0]
      rw [hab'] at hcs2 hcs
      refine givens_entry_eq_zero hcs1 hcs2 (lam := lam) ?_ ?_ ?_
      · change w * (lam - z) + x * y = lam * (lam - z)
        rw [hx0] at hkey ⊢
        linear_combination (-1 : ℝ) * hkey
      · change y * (lam - z) + z * y = lam * y
        ring
      · intro _ hy0
        have hy0' : y = 0 := hy0
        have hcs0 : cs = (1, 0) := by
          rw [hcs]
          change Id.run (algorithm_5_1_3 pure (lam - z) y) = (1, 0)
          rw [hy0']
          exact algorithm_5_1_3_pure_zero _
        rw [hcs0]
        change (0 : ℝ) * (1 * w - 0 * x) + 1 * (1 * y - 0 * z) = 0
        rw [hy0']
        ring
    · have hab' : ab = (x, lam - w) := by rw [hab, ite_eq_right hx0]
      rw [hab'] at hcs2
      refine givens_entry_eq_zero hcs1 hcs2 (lam := lam) ?_ ?_ ?_
      · change w * x + x * (lam - w) = lam * x
        ring
      · change y * x + z * (lam - w) = lam * (lam - w)
        linear_combination (-1 : ℝ) * hkey
      · intro ha0
        exact absurd ha0 hx0

end Standardize2

section QRAlgorithm

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The subdiagonal entry above row `i` is zero, or `i = 0`, or `i ≥ n`: the positions where
`H` splits into diagonal blocks (Algorithm 7.5.2's partition; a comparison, exact). -/
def SubdiagZero (H : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : Prop :=
  ∀ h : i < n, 0 < i → H ⟨i, h⟩ ⟨i - 1, by omega⟩ = 0

noncomputable instance (H : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : Decidable (SubdiagZero H i) :=
  Classical.dec _

/-- **The start of the trailing quasi-triangular part** of an upper Hessenberg `H`
(Algorithm 7.5.2, "find the largest nonnegative `q` … such that `H₃₃` is upper
quasi-triangular"): scanning from the bottom, a zero subdiagonal entry above the last row closes a
`1 × 1` block, one above the second-to-last a `2 × 2` block; `schurTrailingStart H m` is the first
row of the decoupled quasi-triangular trailing part of the leading `m × m` block, so
`q = n - schurTrailingStart H n`. -/
noncomputable def schurTrailingStart (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | m + 2 => if SubdiagZero H (m + 1) then schurTrailingStart H (m + 1)
      else if SubdiagZero H m then schurTrailingStart H m else m + 2

/-- **The start of the unreduced block ending at row `e`** (Algorithm 7.5.2, "the smallest
non-negative `p` such that … `H₂₂` is unreduced"): the last row `≤ e` with a zero subdiagonal
entry above it (or `0`). -/
noncomputable def unreducedStart (H : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if SubdiagZero H (e + 1) then e + 1 else unreducedStart H e

/-- **One test of the deflation criterion** of Algorithm 7.5.2, on row `i ≥ 1`: "set to zero
`h_{i,i-1}` if `|h_{i,i-1}| ≤ tol · (|h_ii| + |h_{i-1,i-1}|)`"; the right side is rounded (two
operations), `|·|` and the comparison are exact (convention 1). -/
noncomputable def qrDeflateStep (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  if 0 < (i : ℕ) then do
    let j : Fin n := ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    let b ← rnd (tol * (← rnd (|H i i| + |H j j|)))
    pure (if |H i j| ≤ b then H.updateRow i (Function.update (H i) j 0) else H)
  else pure H

/-- **The deflation step** of Algorithm 7.5.2: "set to zero all subdiagonal elements that satisfy
`|h_{i,i-1}| ≤ tol · (|h_ii| + |h_{i-1,i-1}|)`", row by row. -/
noncomputable def qrDeflate (tol : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (qrDeflateStep rnd tol) H

/-- One reflector `(v, β)` of the Francis step on the window `[p, m)` applied outside the block
`H₂₂` (Algorithm 7.5.2): `Q = Q diag(I_p, P, I_q)` (all rows, the window's columns),
`H₁₂ = H₁₂ P` (rows `< p`) and `H₂₃ = Pᵀ H₂₃` (columns `≥ m`). -/
noncomputable def francisOffBlockStep (p m : ℕ)
    (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) (vβ : (Fin n → ℝ) × ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) := do
  let Q ← householderApplyRight rnd vβ.1 vβ.2 (List.finRange n) (francisWindow n p m) HQ.2
  let H ← householderApplyRight rnd vβ.1 vβ.2
    ((List.finRange n).filter fun (i : Fin n) => (i : ℕ) < p) (francisWindow n p m) HQ.1
  let H ← householderApplyLeft rnd vβ.1 vβ.2 (francisWindow n p m)
    ((List.finRange n).filter fun (j : Fin n) => m ≤ (j : ℕ)) H
  pure (H, Q)

/-- One pass of the `until` loop of Algorithm 7.5.2 on the state `(H, Q, done)`: once `done`,
nothing; else deflate, find `q = n - m` and `p`, stop if `q = n`, else run the Francis step
(Algorithm 7.5.1) on the window `[p, m)` of `H₂₂` and apply its reflectors to `Q`, `H₁₂` and
`H₂₃` (`francisOffBlockStep`). -/
noncomputable def qrPass (tol : ℝ)
    (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) :=
  if st.2.2 then pure st else do
    let H ← qrDeflate rnd tol st.1
    let m := schurTrailingStart H n
    if m = 0 then pure (H, st.2.1, true) else do
      let p := unreducedStart H (m - 1)
      let r ← algorithm_7_5_1 rnd (francisWindow n p m) H
      let HQ ← r.2.foldlM (francisOffBlockStep rnd p m) (r.1, st.2.1)
      pure (HQ.1, HQ.2, false)

/-- The last step of Algorithm 7.5.2 at row `i`: if `(i, i+1)` is a `2 × 2` diagonal block (a
nonzero subdiagonal entry between zero ones), standardize it by `triangularize2x2`. -/
noncomputable def standardizeStep (HQ : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
  if h : (i : ℕ) + 1 < n then
    if ¬ SubdiagZero HQ.1 (i + 1) ∧ SubdiagZero HQ.1 i ∧ SubdiagZero HQ.1 (i + 2) then
      triangularize2x2 rnd i ⟨(i : ℕ) + 1, h⟩ HQ
    else pure HQ
  else pure HQ

/-- **Algorithm 7.5.2 (QR algorithm)**: "Given `A ∈ ℝ^{n×n}` and a tolerance `tol` greater than the
unit roundoff, this algorithm computes the real Schur canonical form `Qᵀ A Q = T`."
```
Use Algorithm 7.4.2 to compute the Hessenberg reduction H = U₀ᵀ A U₀, Q = P₁ ⋯ P_{n-2}
until q = n
    Set to zero all subdiagonal elements that satisfy |h_{i,i-1}| ≤ tol·(|h_ii| + |h_{i-1,i-1}|)
    Find the largest nonnegative q and the smallest non-negative p such that
        H = [H₁₁ H₁₂ H₁₃; 0 H₂₂ H₂₃; 0 0 H₃₃]  (sizes p, n-p-q, q)
    where H₃₃ is upper quasi-triangular and H₂₂ is unreduced
    if q < n
        Perform a Francis QR step on H₂₂: H₂₂ = Zᵀ H₂₂ Z
        Q = Q·diag(I_p, Z, I_q);  H₁₂ = H₁₂ Z;  H₂₃ = Zᵀ H₂₃
    end
end
Upper triangularize all 2-by-2 diagonal blocks in H that have real eigenvalues and accumulate
the transformations
```
`H` is the Hessenberg part of Algorithm 7.4.2's array and `Q` the backward accumulation of its
returned reflector data (§5.1.6); the `until` loop is at most `fuel` passes of `qrPass`
(convention 3, `done` set when `q = n`); the last step runs `standardizeStep` along the diagonal.
Returns `(Q, T, done)`. -/
noncomputable def algorithm_7_5_2 (tol : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (fuel : ℕ) :
    M (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Bool) := do
  let r ← algorithm_7_4_2 rnd A
  let Q ← backwardAccumulation rnd r.2
  let st ← (List.range fuel).foldlM (fun st _ => qrPass rnd tol st)
    (hessenbergPart r.1, Q, false)
  let HQ ← (List.finRange n).foldlM (standardizeStep rnd) (st.1, st.2.1)
  pure (HQ.2, HQ.1, st.2.2)

end QRAlgorithm

end GolubVanLoan.Chapter07
