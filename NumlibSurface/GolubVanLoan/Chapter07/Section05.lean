import NumlibSurface.GolubVanLoan.Chapter07.Section04

/-!
# Golub–Van Loan §7.5: the practical QR algorithm

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.5: the shifted QR step (7.5.3) as an orthogonal similarity, the exact shift
(Theorem 7.5.1), the double-shift identities (7.5.6)–(7.5.8), and the first column of `M` that
starts the Francis step (§7.5.5).

## Conventions

Real upper Hessenberg `H : Matrix (Fin n) (Fin n) ℝ`, complex shifts through `Matrix.complexify`.
"A QR factorization" is given as data: a unitary (orthogonal over `ℝ`) `U` and an upper triangular
`R` with `H - μ I = U R`, so that the statements hold for every factorization, as the book's do. The
backbone's canonical steps are `Matrix.shiftedQrStep`, `Matrix.doubleShiftQrStep`, and the
predicates `Matrix.IsShiftedQrStep`, `Matrix.IsFrancisStep` (`Numlib/Eigen/QRAlgorithm`).

## Algorithms

The Francis step (Algorithm 7.5.1), the `2 × 2` standardization helper and the QR algorithm
(Algorithm 7.5.2) run chapter 5's shared helpers (`houseOn`, `householderApplyLeft/Right`,
`givensApplyLeft/Right`, `backwardAccumulation`), which are not yet available; they are planned in
this section's group and not written here.

## Not formalized

The deflation criterion (7.5.2) and the "decoupling" heuristics; Stewart's worked example
`h̃_{n,n-1} = -ε² b/(a² + ε²)`; the roundoff claims of §7.5.6 (`≈`, no derivation); balancing
(§7.5.7); flop counts.
-/

open Matrix Polynomial

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

/-! ### §7.5.2 The shifted QR iteration -/

/-- **(7.5.3).** Each matrix of the shifted QR iteration is orthogonally similar to its predecessor:
if `H - μ I = U R` with `U` orthogonal, then `R U + μ I = Uᵀ (U R + μ I) U = Uᵀ H U`. -/
theorem equation_7_5_3 {H U R : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hU : U ∈ orthogonalGroup (Fin n) ℝ) (hQR : H - μ • 1 = U * R) :
    R * U + μ • 1 = Uᵀ * H * U := by
  have h := qr_step_eq_conj hU hQR rfl
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

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

/-- A unimodular diagonal matrix is unitary. -/
private theorem diagonal_mem_unitaryGroup {d : Fin n → ℂ} (hd : ∀ i, ‖d i‖ = 1) :
    diagonal d ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, hd i]
  simp

/-- A shifted QR step of a unimodular diagonal similarity `D* H D` of `H` (taken with the factors
`D* U`, `R D` of the factorization `H - μ I = U R`) lands on the same matrix as the step of `H`. -/
private theorem isShiftedQrStep_diagonal_conj {μ : ℂ} {H H' : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℂ} (hd : ∀ i, ‖d i‖ = 1) (h : IsShiftedQrStep μ H H') :
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

end GolubVanLoan.Chapter07
