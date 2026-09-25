import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Numlib.Analysis.Matrix.Function.Exp
import Numlib.Analysis.Matrix.Function.Pade
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Schur
import NumlibSurface.GolubVanLoan.Chapter09.Section02

/-!
# Golub–Van Loan §9.3: the matrix exponential

Surface file for [golub2013matrix] §9.3: the Padé approximants of the exponential and the
remainder (9.3.1), the Moler–Van Loan backward error of scaling and squaring, the even/odd
evaluation of `N_qq`, `D_qq`; the ODE characterization and the perturbation theory of `e^{At}`
(the variation-of-constants identity, (9.3.2) with the spectral abscissa (9.3.3), the relative
bound, Van Loan's condition number `ν(A, t)`), normal matrices ((9.3.4)), the `2 × 2` example
(9.3.5), and the normal case of §9.3.4.

## Conventions

`e^{At}` is Mathlib's `NormedSpace.exp (t • A)`, which needs no norm on matrices. `A` is real,
`Matrix (Fin n) (Fin n) ℝ`, where the book is real (§9.3.1, the start of §9.3.2), and complex where
the book uses the Schur decomposition `Qᴴ A Q = diag(λ_i) + N` (`Q ∈ unitaryGroup`, `star Q = Qᴴ`).
The `∞`-norm of §9.3.1 is the scoped `Matrix.Norms.Operator`, the `2`-norm of §9.3.2–§9.3.4 the
scoped `Matrix.Norms.L2Operator`; integrals of matrix-valued functions are taken in whichever of
them is open (all norms give the same integral). The Padé functions are the backbone's
`Pade.expNum ℝ p q = N_pq`, `Pade.expDen ℝ p q = D_pq` and `Pade.expApprox ℝ p q A = R_pq(A)`;
`ε(p, q)` is `Pade.errorBound p q`; Van Loan's `ν(A, t)` is `NormedSpace.expCondNumber A t`, the
operator norm of the Fréchet derivative `E ↦ ∫₀ᵗ e^{A(t-s)} E e^{As} ds` times `‖A‖₂/‖e^{At}‖₂`,
which is the book's `max_{‖E‖₂ ≤ 1}`.

## Sources

`Numlib/Analysis/Matrix/Function/{Pade,Exp}`, `Numlib/Analysis/Normed/Algebra/Exponential`
(`NormedSpace.exp_smul_add_sub_exp_smul`, `NormedSpace.eq_exp_smul_of_hasDerivAt`,
`NormedSpace.expCondNumber`), `Numlib/Analysis/Normed/Algebra/SpectralRadius`
(`spectralAbscissa`), `Numlib/LinearAlgebra/Matrix/Schur`
(`Matrix.isStarNormal_iff_strictUpper_eq_zero`).

## Not formalized

The flop counts, Figure 9.3.1 and `α_{.01}(A)/.01 ≈ 216`, and the heuristic claims of §9.3.2 ("a
matrix `E` for which … `≈`") and §9.3.4 (the rounding estimate `γ`, "numerical experiments
suggest").

## Errata

(9.3.2) prints `e^{α(A) t M_S(t)}` for `e^{α(A) t} M_S(t)`; §9.3.2's "equality holding for all
nonnegative `t` if and only if the matrix `A` is normal" is false in the "only if" direction
(`expCondNumber_eq_iff_counterexample`); (9.3.6) cites "(7.8.8)" for (7.9.8); Algorithm 9.3.1's
`j = max{0, 1 + ⌊log₂ ‖A‖_∞⌋}` only guarantees `‖A/2^j‖_∞ < 1`, not the `≤ 1/2` that the
Moler–Van Loan bound needs (`2 + ⌊log₂ ‖A‖_∞⌋` does).
-/

open Polynomial Finset NormedSpace
open scoped Nat

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### A Padé approximation method -/

/-- **The Padé functions** of §9.3.1: `R_pq(z) = D_pq(z)⁻¹ N_pq(z)` with
`N_pq(z) = ∑_{k=0}^{p} (p+q-k)! p! / ((p+q)! k! (p-k)!) zᵏ` and
`D_pq(z) = ∑_{k=0}^{q} (p+q-k)! q! / ((p+q)! k! (q-k)!) (-z)ᵏ`; and
`R_p0(z) = 1 + z + ⋯ + z^p/p!` is the order-`p` Taylor polynomial. -/
theorem pade_def (p q : ℕ) :
    (∀ k, (Pade.expNum ℝ p q).coeff k = if k ≤ p then
      (((p + q - k)! * p ! : ℕ) / ((p + q)! * k ! * (p - k)! : ℕ) : ℝ) else 0) ∧
    (∀ k, (Pade.expDen ℝ p q).coeff k = if k ≤ q then
      (-1) ^ k * (((p + q - k)! * q ! : ℕ) / ((p + q)! * k ! * (q - k)! : ℕ) : ℝ) else 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, Pade.expApprox ℝ p q A =
      (aeval A (Pade.expDen ℝ p q))⁻¹ * aeval A (Pade.expNum ℝ p q)) ∧
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p 0 A = ∑ k ∈ range (p + 1), ((k ! : ℝ)⁻¹) • A ^ k := by
  refine ⟨Pade.coeff_expNum p q, Pade.coeff_expDen p q, fun A => ?_, fun A => ?_⟩
  · rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  · rw [Pade.expApprox, Pade.expDen_zero_right, Pade.expNum_zero_right, map_one,
      Ring.inverse_one, one_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]

section Infinity

open scoped Matrix.Norms.Operator

/-- **(9.3.1)**: if `D_pq(A)` is nonsingular, then
`e^A = R_pq(A) + (-1)^q/(p+q)! A^{p+q+1} D_pq(A)⁻¹ ∫₀¹ u^p (1-u)^q e^{A(1-u)} du`. -/
theorem equation_9_3_1 (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : IsUnit (aeval A (Pade.expDen ℝ p q))) :
    exp A = Pade.expApprox ℝ p q A + ((-1) ^ q / (p + q)! : ℝ) • (A ^ (p + q + 1) *
      (aeval A (Pade.expDen ℝ p q))⁻¹ *
        ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • A)) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact Pade.exp_eq_expApprox_add p q A hD

/-- **The Moler–Van Loan bound** quoted in §9.3.1: if `‖A‖_∞/2^j ≤ 1/2`, then
`F_pq = (R_pq(A/2^j))^{2^j} = e^{A+E}` for some `E` with `AE = EA` and
`‖E‖_∞ ≤ ε(p, q) ‖A‖_∞`, `ε(p, q) = 2^{3-(p+q)} p! q!/((p+q)! (p+q+1)!)`; and consequently
`‖e^A - F_pq‖_∞ / ‖e^A‖_∞ ≤ ε(p, q) ‖A‖_∞ e^{ε(p, q) ‖A‖_∞}`. -/
theorem molerVanLoan [NeZero n] (p q j : ℕ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    (∃ E : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j = exp (A + E) ∧ A * E = E * A ∧
        ‖E‖ ≤ Pade.errorBound p q * ‖A‖) ∧
    ‖exp A - Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j‖ / ‖exp A‖ ≤
      Pade.errorBound p q * ‖A‖ * Real.exp (Pade.errorBound p q * ‖A‖) := by
  have hA' : ‖A‖ ≤ 2 ^ j / 2 := by
    rw [div_le_iff₀ (by positivity)] at hA
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hc, hE, h⟩ := Pade.exists_exp_add_eq_expApprox_pow p q j hA'
    exact ⟨E, h, hc.eq, hE⟩
  · have hpos : 0 < ‖exp A‖ := norm_pos_iff.mpr (Matrix.isUnit_exp A).ne_zero
    rw [div_le_iff₀ hpos]
    exact Pade.norm_exp_sub_expApprox_pow_le p q j hA'

end Infinity

/-- Splitting a sum over `range (2m)` into its even and odd terms. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, f (2 * k) + ∑ k ∈ range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- §9.3.1's cheaper evaluation of the diagonal approximants: with `c_k` the coefficients of
`N_qq`, `U = ∑_k c_{2k} A^{2k}` and `V = ∑_k c_{2k+1} A^{2k}`, `N_qq(A) = U + A V` and
`D_qq(A) = U - A V` (for `q = 8` the book's explicit `U`, `V`, evaluated by Horner in `A²`). -/
theorem pade_even_odd (q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    let c := fun k => (Pade.expNum ℝ q q).coeff k
    let U := ∑ k ∈ range (q + 1), c (2 * k) • A ^ (2 * k)
    let V := ∑ k ∈ range (q + 1), c (2 * k + 1) • A ^ (2 * k)
    aeval A (Pade.expNum ℝ q q) = U + A * V ∧ aeval A (Pade.expDen ℝ q q) = U - A * V := by
  intro c U V
  have hden : ∀ k, (Pade.expDen ℝ q q).coeff k = (-1) ^ k * c k := fun k => by
    simp only [c, Pade.coeff_expDen, Pade.coeff_expNum]
    split_ifs <;> simp
  have hdeg : ∀ P : ℝ[X], (∀ k, q < k → P.coeff k = 0) → P.natDegree < 2 * (q + 1) :=
    fun P hP => lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hP k
      (by exact_mod_cast hk)) (by omega)
  have hNz : ∀ k, q < k → (Pade.expNum ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expNum, ite_eq_right (by omega)]
  have hDz : ∀ k, q < k → (Pade.expDen ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expDen, ite_eq_right (by omega)]
  have hodd : ∀ (d : ℝ) (k : ℕ), d • A ^ (2 * k + 1) = A * (d • A ^ (2 * k)) := fun d k => by
    rw [mul_smul_comm, ← pow_succ']
  constructor
  · rw [aeval_eq_sum_range' (hdeg _ hNz), sum_range_two_mul]
    simp only [U, V, c, Finset.mul_sum, hodd]
  · rw [aeval_eq_sum_range' (hdeg _ hDz), sum_range_two_mul, sub_eq_add_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_succ (-1 : ℝ) (2 * k), pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul,
        neg_one_mul, neg_smul, hodd]

/-! ### Perturbation theory -/

section Two

open scoped Matrix.Norms.L2Operator

/-- §9.3.2: `X(t) = e^{At}` solves `Ẋ(t) = A X(t)`, `X(0) = I`, and is its unique solution. -/
theorem exp_unique_ode (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t) ∧
    exp ((0 : ℝ) • A) = 1 ∧
    ∀ X : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt X (A * X t) t) → X 0 = 1 →
      ∀ t, X t = exp (t • A) :=
  ⟨fun t => hasDerivAt_exp_smul_const' A t, by rw [zero_smul, exp_zero],
    fun _ hX h0 t => eq_exp_smul_of_hasDerivAt hX h0 t⟩

/-- §9.3.2: `e^{(A+E)t} - e^{At} = ∫₀ᵗ e^{A(t-s)} E e^{(A+E)s} ds`, and for `t ≥ 0`
`‖e^{(A+E)t} - e^{At}‖₂ / ‖e^{At}‖₂ ≤ (‖E‖₂ / ‖e^{At}‖₂) ∫₀ᵗ ‖e^{A(t-s)}‖₂ ‖e^{(A+E)s}‖₂ ds`. -/
theorem exp_perturbation_integral (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    exp (t • (A + E)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * E * exp (s • (A + E)) ∧
    (0 ≤ t → ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      ‖E‖ / ‖exp (t • A)‖ * ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • A)‖ * ‖exp (s • (A + E))‖) := by
  refine ⟨exp_smul_add_sub_exp_smul A E t, fun ht => ?_⟩
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (norm_exp_smul_add_sub_exp_smul_le A E ht) (norm_nonneg _)

/-- **(9.3.3), the spectral abscissa** `α(A) = max {Re λ : λ ∈ λ(A)}`: it is attained by an
eigenvalue and bounds the real part of every eigenvalue. -/
theorem equation_9_3_3 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ μ ∈ spectrum ℂ A, μ.re = spectralAbscissa A) ∧
    ∀ μ ∈ spectrum ℂ A, μ.re ≤ spectralAbscissa A :=
  ⟨exists_mem_spectrum_re_eq_spectralAbscissa (Matrix.finite_spectrum A).isCompact
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A),
    fun _ hμ => re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hμ⟩

/-- **(9.3.2)**, corrected: if `Qᴴ A Q = diag(λ_i) + N` is a Schur decomposition, then for `t ≥ 0`
`‖e^{At}‖₂ ≤ e^{α(A) t} M_S(t)`, `M_S(t) = ∑_{k=0}^{n-1} ‖N t‖₂ᵏ / k!`. The book prints
`e^{α(A) t M_S(t)}`, which fails for `α(A) < 0` and `N ≠ 0`. -/
theorem equation_9_3_2 [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (spectralAbscissa A * t) * ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! := by
  simpa only [Fintype.card_fin] using Matrix.l2_opNorm_exp_smul_le_of_schur hQ hT ht

/-- §9.3.2, "with a little manipulation": for `t ≥ 0`,
`‖e^{(A+E)t} - e^{At}‖₂ / ‖e^{At}‖₂ ≤ t ‖E‖₂ M_S(t)² exp(t M_S(t) ‖E‖₂)`. -/
theorem exp_perturbation_schur [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular)
    (E : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    let N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
    let MS : ℝ → ℝ := fun s => (∑ k ∈ range n, ‖s • N‖ ^ k / k !)
    ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      t * ‖E‖ * MS t ^ 2 * Real.exp (t * MS t * ‖E‖) := by
  have h := Matrix.l2_opNorm_exp_smul_add_sub_le hQ hT E ht
  simp only [Fintype.card_fin] at h
  exact h

/-- §9.3.2: `M_S(t) = 1` for all `t > 0` if and only if `A` is normal (its Schur form is then
diagonal, `N = 0`). -/
theorem schurDeparture_eq_one_iff [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) :
    (∀ t : ℝ, 0 < t → ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! = 1) ↔
      IsStarNormal A := by
  rw [Matrix.isStarNormal_iff_strictUpper_eq_zero hQ hT, ← sub_eq_zero]
  set N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      add_eq_right] at h1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp h1
    rcases m with _ | m
    · ext i j
      obtain rfl : i = j := Fin.ext (by have := i.2; have := j.2; omega)
      simp [N]
    · have h0 := hz 0 (Finset.mem_range.mpr (Nat.succ_pos m))
      simpa [one_smul] using h0
  · intro hN t _
    rw [hN, Finset.sum_range_succ']
    simp

/-- §9.3.2: Van Loan's condition number satisfies `ν(A, t) ≥ t ‖A‖₂` for `t ≥ 0`. -/
theorem expCondNumber_ge [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    t * ‖A‖ ≤ expCondNumber A t :=
  mul_norm_le_expCondNumber A ht

/-- **(9.3.4)**: if `A` is normal, then `‖e^{At}‖₂ = e^{α(A) t}` for `t ≥ 0`. -/
theorem equation_9_3_4 [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp (t • A)‖ = Real.exp (spectralAbscissa A * t) :=
  Matrix.l2_opNorm_exp_smul_of_isStarNormal hA ht

/-- §9.3.2, the true half of "equality holding for all nonnegative `t` if and only if the matrix
`A` is normal": for normal `A`, `ν(A, t) = t ‖A‖₂` for every `t ≥ 0`. -/
theorem expCondNumber_eq_of_isStarNormal [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) {t : ℝ} (ht : 0 ≤ t) : expCondNumber A t = t * ‖A‖ :=
  Matrix.expCondNumber_eq_of_isStarNormal hA ht

end Two

/-- A square-zero matrix has `e^N = I + N`. -/
private theorem exp_eq_one_add_of_sq_eq_zero {𝕜 : Type} [RCLike 𝕜] {m : ℕ}
    {N : Matrix (Fin m) (Fin m) 𝕜} (hN : N ^ 2 = 0) : exp N = 1 + N := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) 𝕜) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra 𝕜 (Matrix (Fin m) (Fin m) 𝕜) := Matrix.linftyOpNormedAlgebra
  rw [exp_eq_tsum 𝕜]
  beta_reduce
  rw [tsum_eq_sum (s := range 2) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [show k = 2 + (k - 2) by omega, pow_add, hN, zero_mul, smul_zero]]
  simp [Finset.sum_range_succ]

/-- **(9.3.5)**: for `A = [-1 1000; 0 -1]`, `e^{At} = e^{-t} [1 1000t; 0 1]`. -/
theorem equation_9_3_5 (t : ℝ) :
    exp (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.exp (-t) • !![1, 1000 * t; 0, 1] := by
  set N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1000 * t; 0, 0]
  have hsplit : (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal (fun _ => -t) + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, mul_comm]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hc : Commute (Matrix.diagonal fun _ : Fin 2 => -t) N := by
    rw [← Matrix.smul_one_eq_diagonal]
    exact (Commute.one_left N).smul_left _
  have hexpN : exp N = 1 + N := exp_eq_one_add_of_sq_eq_zero hN2
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal, hexpN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Pi.exp_def, ← Real.exp_eq_exp_ℝ]

section Counterexample

open scoped Matrix.Norms.L2Operator

/-- The exponential of the counterexample matrix `[1] ⊕ [0 1; 0 0]`. -/
private theorem exp_smul_cex (s : ℝ) :
    exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)) =
      !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1] := by
  set N : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, (s : ℂ); 0, 0, 0]
  have hsplit : (s • !![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![(s : ℂ), 0, 0] + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hc : Commute (Matrix.diagonal ![(s : ℂ), 0, 0]) N := by
    unfold Commute SemiconjBy
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal,
    exp_eq_one_add_of_sq_eq_zero hN2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_three, Pi.exp_def, ← Complex.exp_eq_exp_ℂ,
      Complex.ofReal_exp]

/-- The spectral norm of `e^{sA}` for the counterexample matrix is `e^s`, `s ≥ 0`: the block
`[1 s; 0 1]` has norm at most `1 + s ≤ e^s`. -/
private theorem norm_exp_smul_cex {s : ℝ} (hs : 0 ≤ s) :
    ‖exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ))‖ = Real.exp s := by
  rw [exp_smul_cex]
  set M : Matrix (Fin 3) (Fin 3) ℂ := !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1]
  set E := Real.exp s
  have hE : 0 < E := Real.exp_pos s
  have hv : ∀ x : EuclideanSpace ℂ (Fin 3),
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 0 = (E : ℂ) * x 0 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 1 = x 1 + (s : ℂ) * x 2 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 2 = x 2 := fun x => by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [M, E, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsq : ∀ x : EuclideanSpace ℂ (Fin 3),
      ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ ^ 2 =
        ‖(E : ℂ) * x 0‖ ^ 2 + ‖x 1 + (s : ℂ) * x 2‖ ^ 2 + ‖x 2‖ ^ 2 := fun x => by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, (hv x).1, (hv x).2.1, (hv x).2.2]
  have hEn : ‖(E : ℂ)‖ = E := by rw [Complex.norm_real, Real.norm_of_nonneg hE.le]
  apply le_antisymm
  · rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hE.le fun x => ?_
    have h1 : 1 + s ≤ E := by linarith [Real.add_one_le_exp s]
    set a := ‖x 1‖
    set b := ‖x 2‖
    set c := ‖x 0‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hab : ‖x 1 + (s : ℂ) * x 2‖ ≤ a + s * b := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    have hx : ‖x‖ ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), hsq, mul_pow, hx, norm_mul, hEn]
    have h2 : ‖x 1 + (s : ℂ) * x 2‖ ^ 2 ≤ (a + s * b) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hab 2
    have h3 : (a + s * b) ^ 2 + b ^ 2 ≤ (1 + s) ^ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [mul_nonneg hs (sq_nonneg (a - b)), sq_nonneg (s * a),
        mul_nonneg hs (add_nonneg (sq_nonneg a) (sq_nonneg b))]
    have h4 : (1 + s) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [mul_le_mul_of_nonneg_right h4 (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  · rw [Matrix.cstar_norm_def]
    set x : EuclideanSpace ℂ (Fin 3) := EuclideanSpace.single 0 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hMx : ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ = E := by
      rw [← sq_eq_sq₀ (norm_nonneg _) hE.le, hsq]
      simp [x]
    calc E = ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ := hMx.symm
      _ ≤ ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx, mul_one]

/-- **§9.3.2's "only if" is false**: `A = [1] ⊕ [0 1; 0 0]` is not normal, and yet
`ν(A, t) = t ‖A‖₂` for every `t ≥ 0`, because `‖e^{sA}‖₂ = e^s` for `s ≥ 0` (the book: "equality
holding for all nonnegative `t` if and only if the matrix `A` is normal"). -/
theorem expCondNumber_eq_iff_counterexample :
    ¬ IsStarNormal (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) ∧
    ∀ t : ℝ, 0 ≤ t → expCondNumber (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) t =
      t * ‖(!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)‖ := by
  refine ⟨fun h => ?_, fun t ht => expCondNumber_eq_of_norm_exp_smul_eq _ ht fun s hs => by
    rw [one_mul]
    exact norm_exp_smul_cex hs.1⟩
  have := congrFun (congrFun h.star_comm_self 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose] at this

end Counterexample

/-! ### Some stability issues -/

/-- A matrix commuting with `B` commutes with every polynomial in `B`. -/
private theorem commute_aeval {X B : Matrix (Fin n) (Fin n) ℂ} (h : Commute X B) (p : ℂ[X]) :
    Commute X (aeval B p) := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun k a ih => ?_)
  · rw [aeval_C]
    exact Algebra.commute_algebraMap_right a X
  · rw [map_add]
    exact hp.add_right hq
  · rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h

section Two

open scoped Matrix.Norms.L2Operator

/-- §9.3.4: if `A` is normal, then so is `G = R_qq(A/2^j)`, and `‖G^m‖₂ = ‖G‖₂^m` for every
`m`. -/
theorem normal_squaring [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (q j : ℕ) :
    IsStarNormal (Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)) ∧
    ∀ m : ℕ, ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A) ^ m‖ =
      ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)‖ ^ m := by
  set B := (2⁻¹ : ℂ) ^ j • A
  have hB : IsStarNormal B := ⟨by
    rw [star_smul]
    exact (hA.star_comm_self.smul_left _).smul_right _⟩
  obtain ⟨r, hr⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hB
  have hsB : star B = aeval B r := by rw [Matrix.star_eq_conjTranspose, hr]
  set Dm := aeval B (Pade.expDen ℂ q q)
  set Nm := aeval B (Pade.expNum ℂ q q)
  have hG : Pade.expApprox ℂ q q B = Dm⁻¹ * Nm := by
    rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  -- anything commuting with `B` commutes with `G`
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) ℂ, Commute X B → Commute X (Dm⁻¹ * Nm) :=
    fun X hX => (Matrix.commute_nonsing_inv_right (commute_aeval hX _)).mul_right
      (commute_aeval hX _)
  have hGB : Commute (Dm⁻¹ * Nm) B := (hcomm B (Commute.refl B)).symm
  have hGsB : Commute (Dm⁻¹ * Nm) (star B) := by
    rw [hsB]
    exact commute_aeval hGB r
  have hsGB : Commute (star (Dm⁻¹ * Nm)) B := by
    simpa only [star_star] using hGsB.star_star
  have hN : IsStarNormal (Pade.expApprox ℂ q q B) := by
    rw [hG]
    exact ⟨hcomm _ hsGB⟩
  refine ⟨hN, fun m => ?_⟩
  have hNm : IsStarNormal (Pade.expApprox ℂ q q B ^ m) := IsStarNormal.pow m
  have h1 := Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal (Pade.expApprox ℂ q q B ^ m)
  rw [spectralRadius_pow, ← Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal] at h1
  have h2 : ‖Pade.expApprox ℂ q q B ^ m‖₊ = ‖Pade.expApprox ℂ q q B‖₊ ^ m := by
    exact_mod_cast h1
  rw [← coe_nnnorm, h2, NNReal.coe_pow, coe_nnnorm]

end Two

end GolubVanLoan.Chapter09
