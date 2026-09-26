import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Analysis.Matrix.Function.Triangular
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic
import NumlibSurface.GolubVanLoan.Chapter07.Section01

/-!
# Golub–Van Loan §9.1: eigenvalue methods

Surface file for [golub2013matrix] §9.1: the Jordan-based definition (9.1.1)–(9.1.4), here the
theorem that the backbone's `pfc f A` has the Jordan-form expression; Lemma 9.1.1 and Theorem 9.1.2
(Taylor series), the series of `exp`, `log`, `sin`, `cos`; (9.1.6)–(9.1.8); Corollary 9.1.3; the
Schur approach (Theorem 9.1.4, the Parlett recurrence (9.1.11) and Algorithm 9.1.1); the block
Parlett equations (9.1.12) with the unique solvability of their Sylvester equations; and the
relative condition number of §9.1.6.

## Conventions

`A : Matrix (Fin n) (Fin n) ℂ`, `f : ℂ → ℂ`, and the book's `f(A)` is the backbone's primary
functional calculus `pfc f A` (Hermite interpolation of `f` and its derivatives on the roots of the
minimal polynomial). The book *defines* `f(A)` by (9.1.3); here (9.1.3) is a theorem
(`equation_9_1_3`), so its right side does not depend on the Jordan decomposition chosen. `pfc` is
total: "`f(A)` is defined" is a hypothesis only where a proof uses it, and Mathlib's junk value
`iteratedDeriv k f z = 0` at a nondifferentiable point enters both sides of every identity alike.
Indices are `0`-based (`Fin n`); upper triangular is `Matrix.IsUpperTriangular`
(`T.BlockTriangular id`); the strictly increasing sequences `S_ij` of Theorem 9.1.4 are the lists
`Matrix.path i s j` for `s ⊆ Finset.Ioo i j`. Block partitions are `Matrix.toBlock` along a block
index `b : Fin n → Fin p`. Algorithm 9.1.1 follows the algorithm conventions of
`NumlibSurface.GolubVanLoan`, over any field; the evaluation `f(t_ii)` is rounded once.

## Sources

`Numlib/Analysis/Normed/Algebra/PrimaryFunctionalCalculus/{Basic,Analytic}` (`pfc`, `hasSum_pfc`,
`pfc_mul`, `pfc_inv`, `commute_pfc`) and `Numlib/Analysis/Matrix/Function/{Basic,Triangular}`
(`Matrix.pfc_conj`, `Matrix.pfc_jordanBlock`, `Matrix.pfc_conj_jordanForm`,
`Matrix.pfc_apply_eq_sum_divDiff`, `Matrix.pfc_apply_eq_parlett`,
`Matrix.BlockTriangular.pfc_sylvester`); chapter 7's Lemma 7.1.5
(`GolubVanLoan.Chapter07.lemma_7_1_5`) for the Sylvester equations of §9.1.5, applied on the blocks'
index types after reindexing to `Fin`.

## Not formalized

The numerical example of §9.1.3 (the `1 ± 10⁻⁵` matrix), the `3 × 3` illustration of Theorem 9.1.4,
the flop counts, and the forward-stability heuristic
`‖F̂ - f(A)‖/‖f(A)‖ ≈ u cond_rel(f, A)` of §9.1.6.

## Errata

(9.1.8) prints `f(X⁻¹AX) = X f(A) X⁻¹`, with `X` and `X⁻¹` exchanged on the right; §9.1.2 prints
`log(I - A) = ∑_{k ≥ 1} A^k/k`, which is `-log(I - A)`. Both are stated corrected.
-/

open Polynomial Finset Filter Topology
open scoped Nat ENNReal

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### Glue: complex matrices are integral with split minimal polynomial -/

/-- An eigenvalue of `A` in the sense of the minimal polynomial is one of the spectrum. -/
private theorem mem_spectrum_of_mem_roots {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : μ ∈ (minpoly ℂ A).roots) : μ ∈ spectrum ℂ A :=
  (spectrum.mem_iff_isRoot_minpoly (Algebra.IsIntegral.isIntegral A)).2
    (Polynomial.isRoot_of_mem_roots hμ)

/-- `pfc` of an affine function. -/
private theorem pfc_affine (a b : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    pfc (fun z => a + b * z) A = a • 1 + b • A := by
  have h := pfc_polynomial (Algebra.IsIntegral.isIntegral A) (IsAlgClosed.splits _) (C a + C b * X)
  simp only [eval_add, eval_C, eval_mul, eval_X, map_add, aeval_C, map_mul, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  exact h

/-! ### The Jordan-based definition -/

/-- The rational examples of the chapter introduction and §9.1: `p(A) = I + A` for
`p(z) = 1 + z`; `r(A) = (I - A/2)⁻¹ (I + A/2)` for `r(z) = (1 - z/2)⁻¹ (1 + z/2)`, `2 ∉ λ(A)`; and
"if `f(z) = (1 + z)/(1 - z)` and `1 ∉ λ(A)`, then `f(A) = (I + A)(I - A)⁻¹`". -/
theorem rational_example (A : Matrix (Fin n) (Fin n) ℂ) :
    pfc (fun z : ℂ => 1 + z) A = 1 + A ∧
    ((2 : ℂ) ∉ spectrum ℂ A → pfc (fun z : ℂ => (1 - z / 2)⁻¹ * (1 + z / 2)) A =
      (1 - (2 : ℂ)⁻¹ • A)⁻¹ * (1 + (2 : ℂ)⁻¹ • A)) ∧
    ((1 : ℂ) ∉ spectrum ℂ A → pfc (fun z : ℂ => (1 + z) / (1 - z)) A = (1 + A) * (1 - A)⁻¹) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  -- affine functions and their `pfc`
  have hlin : ∀ a b : ℂ, pfc (fun z => a + b * z) A = a • 1 + b • A := fun a b => pfc_affine a b A
  have hcd : ∀ (a b : ℂ) (k : ℕ) (μ : ℂ), ContDiffAt ℂ k (fun z : ℂ => a + b * z) μ :=
    fun a b k μ => (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffAt
  -- the inverse of an affine function without a root on the spectrum
  have hinv : ∀ a b : ℂ, (∀ μ ∈ spectrum ℂ A, a + b * μ ≠ 0) →
      pfc (fun z => (a + b * z)⁻¹) A = (a • 1 + b • A)⁻¹ := by
    intro a b h0
    have h := (pfc_inv hI hs (fun μ _ => hcd a b _ μ)
      fun μ hμ => h0 μ (mem_spectrum_of_mem_roots hμ)).2
    rw [h, hlin, Matrix.nonsing_inv_eq_ringInverse]
  have hcdi : ∀ a b : ℂ, (∀ μ ∈ spectrum ℂ A, a + b * μ ≠ 0) → ∀ (k : ℕ) (μ : ℂ),
      μ ∈ (minpoly ℂ A).roots → ContDiffAt ℂ k (fun z : ℂ => (a + b * z)⁻¹) μ :=
    fun a b h0 k μ hμ => (hcd a b k μ).inv (h0 μ (mem_spectrum_of_mem_roots hμ))
  refine ⟨?_, fun h2 => ?_, fun h1 => ?_⟩
  · simpa using hlin 1 1
  · have h0 : ∀ μ ∈ spectrum ℂ A, (1 : ℂ) + (-2⁻¹) * μ ≠ 0 := fun μ hμ h => by
      apply h2
      convert hμ
      linear_combination 2 * h
    have hf : (fun z : ℂ => (1 - z / 2)⁻¹ * (1 + z / 2)) =
        (fun z : ℂ => (1 + (-2⁻¹) * z)⁻¹) * fun z : ℂ => 1 + 2⁻¹ * z := by
      funext z
      simp only [Pi.mul_apply]
      ring_nf
    rw [hf, pfc_mul hI hs (fun μ hμ => hcdi _ _ h0 _ μ hμ) (fun μ _ => hcd _ _ _ μ), hinv _ _ h0,
      hlin]
    congr 1
    · congr 1
      simp only [one_smul, neg_smul, sub_eq_add_neg]
    · simp only [one_smul]
  · have h0 : ∀ μ ∈ spectrum ℂ A, (1 : ℂ) + (-1) * μ ≠ 0 := fun μ hμ h => by
      apply h1
      convert hμ
      linear_combination h
    have hf : (fun z : ℂ => (1 + z) / (1 - z)) =
        (fun z : ℂ => 1 + 1 * z) * fun z : ℂ => (1 + (-1) * z)⁻¹ := by
      funext z
      simp only [Pi.mul_apply]
      ring
    rw [hf, pfc_mul hI hs (fun μ _ => hcd _ _ _ μ) (fun μ hμ => hcdi _ _ h0 _ μ hμ), hinv _ _ h0,
      hlin]
    simp only [one_smul, neg_smul, sub_eq_add_neg]

/-- **(9.1.1)–(9.1.4), the Jordan-based definition, as a theorem**: if
`A = X · diag(J₁, …, J_q) · X⁻¹` is a Jordan decomposition — `X⁻¹ A X` is the Jordan form with
blocks `J_i = J_{e i}(μ i)` laid out by `σ` — then `f(A) = X · diag(F₁, …, F_q) · X⁻¹` with
`F_i = f(J_i)`, the matrices (9.1.4) (`equation_9_1_4`). -/
theorem equation_9_1_3 {q : ℕ} (e : Fin q → ℕ) (μ : Fin q → ℂ) (σ : (Σ i, Fin (e i)) ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = Matrix.reindex σ σ (Matrix.jordanForm e μ)) (f : ℂ → ℂ) :
    pfc f A = X * Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => pfc f (Matrix.jordanBlock (e i) (μ i))) * X⁻¹ :=
  Matrix.pfc_conj_jordanForm σ hX h f

/-- **(9.1.4)**: `f` of a Jordan block `J = J_m(μ)` is upper triangular Toeplitz, with entries
`f⁽ʲ⁻ⁱ⁾(μ)/(j - i)!` on and above the diagonal. -/
theorem equation_9_1_4 (f : ℂ → ℂ) (m : ℕ) (μ : ℂ) (i j : Fin m) :
    pfc f (Matrix.jordanBlock m μ) i j =
      if i ≤ j then iteratedDeriv ((j : ℕ) - i) f μ / ((j : ℕ) - i)! else 0 :=
  Matrix.pfc_jordanBlock_apply f m μ i j

/-! ### The Taylor series representation -/

/-- The coefficients of a power series of `f` at `z₀` are its Taylor coefficients (9.1.5). -/
private theorem coeff_eq_taylor {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r) (k : ℕ) :
    p.coeff k = iteratedDeriv k f z₀ / k ! := by
  rw [hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt,
    FormalMultilinearSeries.coeff_ofScalars]

/-- `hasSum_pfc` for complex matrices, with the series' own coefficients. -/
private theorem hasSum_pfc_matrix {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ ∈ spectrum ℂ A, μ ∈ Metric.eball z₀ r) :
    HasSum (fun k => p.coeff k • (A - z₀ • 1) ^ k) (pfc f A) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    hasSum_pfc hf (Algebra.IsIntegral.isIntegral A) (IsAlgClosed.splits _) hA

/-- The spectrum of a Jordan block is its eigenvalue. -/
private theorem spectrum_jordanBlock_subset (m : ℕ) (c : ℂ) :
    spectrum ℂ (Matrix.jordanBlock m c) ⊆ {c} := by
  intro μ hμ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_jordanBlock, IsRoot.def,
    eval_pow, eval_sub, eval_X, eval_C] at hμ
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp hμ).1

/-- **Lemma 9.1.1**: if `f(z) = ∑ f⁽ᵏ⁾(z₀)/k! (z - z₀)ᵏ` for `|z - z₀| < r` (9.1.5) and
`B = λ I + E` is a Jordan block with `|λ - z₀| < r`, then
`f(B) = ∑_{k ≥ 0} f⁽ᵏ⁾(z₀)/k! (B - z₀ I)ᵏ`. -/
theorem lemma_9_1_1 {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (m : ℕ) {c : ℂ} (hc : c ∈ Metric.eball z₀ r) :
    HasSum (fun k => (iteratedDeriv k f z₀ / k !) • (Matrix.jordanBlock m c - z₀ • 1) ^ k)
      (pfc f (Matrix.jordanBlock m c)) := by
  simpa only [coeff_eq_taylor hf] using hasSum_pfc_matrix hf fun μ hμ => by
    rw [Set.mem_singleton_iff.mp (spectrum_jordanBlock_subset m c hμ)]
    exact hc

/-- **(9.1.6)**: for a Jordan block `B = λ I + E`, `E` its strictly upper bidiagonal part,
`f(B) = ∑_{p = 0}^{m-1} f⁽ᵖ⁾(λ) Eᵖ/p!`, where `[Eᵖ]_ij = δ_{i, j-p}`. -/
theorem equation_9_1_6 (f : ℂ → ℂ) (m : ℕ) (c : ℂ) :
    Matrix.jordanBlock m c = c • 1 + Matrix.jordanBlock m 0 ∧
    (∀ (p : ℕ) (i j : Fin m),
      (Matrix.jordanBlock m (0 : ℂ) ^ p) i j = if (i : ℕ) + p = j then 1 else 0) ∧
    pfc f (Matrix.jordanBlock m c) =
      ∑ p ∈ range m, (iteratedDeriv p f c / p !) • Matrix.jordanBlock m 0 ^ p := by
  refine ⟨by rw [Matrix.jordanBlock_eq_add_smul_one, add_comm],
    fun p i j => Matrix.jordanBlock_zero_pow_apply p i j, ?_⟩
  rw [Matrix.pfc_jordanBlock]
  rfl

/-- **Theorem 9.1.2**: if `f` has the Taylor series (9.1.5) on `|z - z₀| < r` and `|λ - z₀| < r`
for every `λ ∈ λ(A)`, then `f(A) = ∑_{k ≥ 0} f⁽ᵏ⁾(z₀)/k! (A - z₀ I)ᵏ`. The series converges in the
(entrywise) topology of `ℂ^{n×n}`. -/
theorem theorem_9_1_2 {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ ∈ spectrum ℂ A, μ ∈ Metric.eball z₀ r) :
    HasSum (fun k => (iteratedDeriv k f z₀ / k !) • (A - z₀ • 1) ^ k) (pfc f A) := by
  simpa only [coeff_eq_taylor hf] using hasSum_pfc_matrix hf hA

/-- A scalar power series converging everywhere is a power series of its sum on all of `ℂ`. -/
private theorem hasFPowerSeriesOnBall_of_hasSum {f : ℂ → ℂ} {c : ℕ → ℂ}
    (h : ∀ z, HasSum (fun k => c k * z ^ k) (f z)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 ⊤ where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r _ => ?_
    refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) ?_
    have := (h r).summable.tendsto_atTop_zero.norm
    simp only [norm_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      NNReal.abs_eq] at this
    simpa only [FormalMultilinearSeries.ofScalars_norm] using this
  r_pos := ENNReal.zero_lt_top
  hasSum := fun {y} _ => by
    simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using h y

/-- The matrix form of an everywhere convergent series: `f(A) = ∑ c_k Aᵏ`. -/
private theorem hasSum_pfc_of_hasSum {f : ℂ → ℂ} {c : ℕ → ℂ}
    (h : ∀ z, HasSum (fun k => c k * z ^ k) (f z)) (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k => c k • A ^ k) (pfc f A) := by
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_smul, sub_zero] using
    hasSum_pfc_matrix (hasFPowerSeriesOnBall_of_hasSum h) (A := A) fun μ _ => by simp

/-- **The exponential series** of §9.1.2: `exp(A) = ∑_{k ≥ 0} Aᵏ/k!`, and `pfc exp A` is
Mathlib's matrix exponential `NormedSpace.exp A`. -/
theorem taylor_exp (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k => ((k ! : ℂ)⁻¹) • A ^ k) (pfc Complex.exp A) ∧
    pfc Complex.exp A = NormedSpace.exp A := by
  refine ⟨hasSum_pfc_of_hasSum (fun z => ?_) A,
    pfc_exp_eq_normedSpace_exp (Algebra.IsIntegral.isIntegral A)⟩
  rw [Complex.exp_eq_exp_ℂ]
  simpa only [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z

/-- The series `log(1 - z) = -∑_{k ≥ 1} zᵏ/k` on the unit disk. -/
private theorem hasFPowerSeriesOnBall_log_one_sub :
    HasFPowerSeriesOnBall (fun z => Complex.log (1 - z))
      (FormalMultilinearSeries.ofScalars ℂ fun k => -((k : ℂ)⁻¹)) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun k => ?_
    have hr1 : (r : ℝ) ≤ 1 := by exact_mod_cast (ENNReal.coe_lt_one_iff.mp hr).le
    calc ‖FormalMultilinearSeries.ofScalars ℂ (fun k => -((k : ℂ)⁻¹)) k‖ * (r : ℝ) ^ k
        ≤ 1 * 1 := by
          gcongr
          · rw [FormalMultilinearSeries.ofScalars_norm, norm_neg, norm_inv, Complex.norm_natCast]
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp
            · exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)
          · exact pow_le_one₀ r.2 hr1
      _ = 1 := one_mul 1
  r_pos := one_pos
  hasSum := fun {y} hy => by
    have hy' : ‖y‖ < 1 := by
      have : ‖y‖ₑ < 1 := by simpa [Metric.mem_eball, edist_zero_right] using hy
      rwa [← ofReal_norm, ENNReal.ofReal_lt_one] at this
    convert (Complex.hasSum_taylorSeries_neg_log hy').neg using 1
    · ext k
      rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      ring
    · simp

/-- **The logarithm series** of §9.1.2, sign corrected: if `|λ| < 1` for every `λ ∈ λ(A)`, then
`log(I - A) = -∑_{k ≥ 1} Aᵏ/k`. The book prints `log(I - A) = ∑_{k ≥ 1} Aᵏ/k`, which is the
series of `-log(I - A)`. -/
theorem taylor_log_one_sub {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, ‖μ‖ < 1) :
    HasSum (fun k : ℕ => -(((k + 1 : ℕ) : ℂ)⁻¹) • A ^ (k + 1))
      (pfc (fun z => Complex.log (1 - z)) A) := by
  have h := hasSum_pfc_matrix hasFPowerSeriesOnBall_log_one_sub (A := A) fun μ hμ => by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hA μ hμ
  simp only [FormalMultilinearSeries.coeff_ofScalars, zero_smul, sub_zero] at h
  simpa using (hasSum_nat_add_iff' 1).mpr h

/-- The coefficients of the sine series, `0` at even powers. -/
private noncomputable def sinCoeff (k : ℕ) : ℂ :=
  if Even k then 0 else (-1) ^ (k / 2) / (k ! : ℂ)

/-- The coefficients of the cosine series, `0` at odd powers. -/
private noncomputable def cosCoeff (k : ℕ) : ℂ :=
  if Even k then (-1) ^ (k / 2) / (k ! : ℂ) else 0

private theorem sinCoeff_odd (k : ℕ) : sinCoeff (2 * k + 1) = (-1) ^ k / ((2 * k + 1) ! : ℂ) := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [sinCoeff, ite_eq_right h1, h2]

private theorem cosCoeff_even (k : ℕ) : cosCoeff (2 * k) = (-1) ^ k / ((2 * k) ! : ℂ) := by
  have h2 : 2 * k / 2 = k := by omega
  rw [cosCoeff, ite_eq_left (even_two_mul k), h2]

private theorem sinCoeff_eq_zero {k : ℕ} (hk : k ∉ Set.range fun j : ℕ => 2 * j + 1) :
    sinCoeff k = 0 := by
  rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
  · rw [sinCoeff, ite_eq_left he]
  · exact absurd ⟨j, rfl⟩ hk

private theorem cosCoeff_eq_zero {k : ℕ} (hk : k ∉ Set.range fun j : ℕ => 2 * j) :
    cosCoeff k = 0 := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ho
  · exact absurd ⟨j, by ring⟩ hk
  · rw [cosCoeff, ite_eq_right (Nat.not_even_iff_odd.mpr ho)]

private theorem injective_two_mul_add_one : Function.Injective fun j : ℕ => 2 * j + 1 :=
  fun a b h => by simp only at h; omega

private theorem injective_two_mul : Function.Injective fun j : ℕ => 2 * j :=
  fun a b h => by simp only at h; omega

/-- **The sine and cosine series** of §9.1.2: `sin(A) = ∑_{k ≥ 0} (-1)ᵏ A^{2k+1}/(2k+1)!` and
`cos(A) = ∑_{k ≥ 0} (-1)ᵏ A^{2k}/(2k)!`. -/
theorem taylor_sin_cos (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k : ℕ => ((-1) ^ k / ((2 * k + 1) ! : ℂ)) • A ^ (2 * k + 1)) (pfc Complex.sin A) ∧
    HasSum (fun k : ℕ => ((-1) ^ k / ((2 * k) ! : ℂ)) • A ^ (2 * k)) (pfc Complex.cos A) := by
  constructor
  · have hs : ∀ z, HasSum (fun k => sinCoeff k * z ^ k) (Complex.sin z) := fun z => by
      rw [← injective_two_mul_add_one.hasSum_iff fun k hk => by rw [sinCoeff_eq_zero hk, zero_mul]]
      simpa only [Function.comp_def, sinCoeff_odd, div_mul_eq_mul_div] using Complex.hasSum_sin z
    have h := hasSum_pfc_of_hasSum hs A
    rw [← injective_two_mul_add_one.hasSum_iff fun k hk => by rw [sinCoeff_eq_zero hk, zero_smul]]
      at h
    simpa only [Function.comp_def, sinCoeff_odd] using h
  · have hc : ∀ z, HasSum (fun k => cosCoeff k * z ^ k) (Complex.cos z) := fun z => by
      rw [← injective_two_mul.hasSum_iff fun k hk => by rw [cosCoeff_eq_zero hk, zero_mul]]
      simpa only [Function.comp_def, cosCoeff_even, div_mul_eq_mul_div] using Complex.hasSum_cos z
    have h := hasSum_pfc_of_hasSum hc A
    rw [← injective_two_mul.hasSum_iff fun k hk => by rw [cosCoeff_eq_zero hk, zero_smul]] at h
    simpa only [Function.comp_def, cosCoeff_even] using h

/-- **(9.1.7)**: `A f(A) = f(A) A`. The book restricts to Taylor-series functions "for clarity";
it holds for every `f`. -/
theorem equation_9_1_7 (f : ℂ → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * pfc f A = pfc f A * A :=
  (commute_pfc A f).eq

/-- **(9.1.8)**, corrected: `f(X⁻¹ A X) = X⁻¹ f(A) X` for nonsingular `X`. The book prints
`X f(A) X⁻¹` on the right; its own use in §9.1.4 (`f(A) = Q f(T) Qᴴ` from `A = Q T Qᴴ`) is the
corrected form. -/
theorem equation_9_1_8 (f : ℂ → ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (A : Matrix (Fin n) (Fin n) ℂ) : pfc f (X⁻¹ * A * X) = X⁻¹ * pfc f A * X := by
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have h := Matrix.pfc_conj ((Matrix.isUnit_nonsing_inv_iff).mpr hX) f A
  rwa [Matrix.nonsing_inv_nonsing_inv X hdet] at h

/-! ### The eigenvector approach -/

/-- **Corollary 9.1.3** with (9.1.9): if `A = X · diag(λ₁, …, λ_n) · X⁻¹` then
`f(A) = X · diag(f(λ₁), …, f(λ_n)) · X⁻¹` — for every `f`: a diagonalizable matrix needs only
the values of `f` on its spectrum. -/
theorem corollary_9_1_3 (f : ℂ → ℂ) {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (d : Fin n → ℂ) (hA : A = X * Matrix.diagonal d * X⁻¹) :
    pfc f A = X * Matrix.diagonal (f ∘ d) * X⁻¹ := by
  rw [hA, Matrix.pfc_conj hX, Matrix.pfc_diagonal]

/-! ### The Schur decomposition approach -/

/-- **Theorem 9.1.4** with (9.1.10): for upper triangular `T` with `λ_i = t_ii` and
`F = f(T)`: `f_ij = 0` for `i > j`, `f_ii = f(λ_i)`, and for `i < j`
`f_ij = ∑_{(s₀, …, s_k) ∈ S_ij} t_{s₀s₁} ⋯ t_{s_{k-1}s_k} f[λ_{s₀}, …, λ_{s_k}]`, the sum over the
strictly increasing sequences from `i` to `j`, with confluent divided differences where eigenvalues
repeat. -/
theorem theorem_9_1_4 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) (f : ℂ → ℂ) :
    (∀ i j, j < i → pfc f T i j = 0) ∧ (∀ i, pfc f T i i = f (T i i)) ∧
    ∀ i j, i < j → pfc f T i j = ∑ s ∈ (Ioo i j).powerset,
      Matrix.pathProd T (Matrix.path i s j) *
        Hermite.divDiff f ((Matrix.path i s j).map fun k => T k k) :=
  ⟨fun _ _ hji => Matrix.BlockTriangular.pfc hT f hji,
    Matrix.pfc_apply_self_of_isUpperTriangular hT f,
    fun _ _ hij => Matrix.pfc_apply_eq_sum_divDiff hT f hij⟩

/-- **(9.1.11), the Parlett recurrence**, with the commutativity equation it comes from: for
upper triangular `T`, `F = f(T)` and `i < j`, `∑_{k=i}^{j} f_ik t_kj = ∑_{k=i}^{j} t_ik f_kj`, and
if `t_ii ≠ t_jj`, then
`f_ij = t_ij (f_jj - f_ii)/(t_jj - t_ii) + ∑_{k=i+1}^{j-1} (t_ik f_kj - f_ik t_kj)/(t_jj - t_ii)`.
-/
theorem equation_9_1_11 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) (f : ℂ → ℂ)
    {i j : Fin n} (hij : i < j) :
    (∑ k ∈ Icc i j, pfc f T i k * T k j = ∑ k ∈ Icc i j, T i k * pfc f T k j) ∧
    (T i i ≠ T j j → pfc f T i j = T i j * (pfc f T j j - pfc f T i i) / (T j j - T i i) +
      ∑ k ∈ Ioo i j, (T i k * pfc f T k j - pfc f T i k * T k j) / (T j j - T i i)) := by
  have hF : (pfc f T).IsUpperTriangular := Matrix.BlockTriangular.pfc hT f
  refine ⟨?_, Matrix.pfc_apply_eq_parlett hT f hij⟩
  rw [← Matrix.IsUpperTriangular.mul_apply hF hT, ← Matrix.IsUpperTriangular.mul_apply hT hF,
    (commute_pfc T f).eq]

section Algorithm

variable {K : Type} [Field K] {M : Type → Type} [Monad M]

/-- The superdiagonal order of Algorithm 9.1.1: the pairs `(i, j = i + p)`, `p = 1, …, n-1`,
`i = 0, …, n-1-p` (the book's `p = 1 : n-1`, `i = 1 : n-p`), one superdiagonal after another. -/
def superdiagPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.range' 1 (n - 1)).flatMap fun p =>
    (List.finRange n).filterMap fun (i : Fin n) =>
      if h : (i : ℕ) + p < n then some (i, ⟨i + p, h⟩) else none

/-- **Algorithm 9.1.1 (Schur–Parlett)**: `F = f(T)` for upper triangular `T` with distinct
eigenvalues.
```
for i = 1:n
    f_ii = f(t_ii)
end
for p = 1:n-1
    for i = 1:n-p
        j = i + p
        s = t_ij (f_jj - f_ii)
        for k = i+1:j-1
            s = s + t_ik f_kj - f_ik t_kj
        end
        f_ij = s/(t_jj - t_ii)
    end
end
```
Over any field; `f(t_ii)` is rounded once, and the loop body rounds every `+ − × /` in the book's
left-to-right order. -/
def algorithm_9_1_1 (rnd : K → M K) (f : K → K) (T : Matrix (Fin n) (Fin n) K) :
    M (Matrix (Fin n) (Fin n) K) := do
  let F₀ ← (List.finRange n).foldlM (fun F i => do
      let v ← rnd (f (T i i))
      pure (F.updateRow i (Function.update (F i) i v))) (0 : Matrix (Fin n) (Fin n) K)
  (superdiagPairs n).foldlM (fun F ij => do
      let d₀ ← rnd (F ij.2 ij.2 - F ij.1 ij.1)
      let s₀ ← rnd (T ij.1 ij.2 * d₀)
      let s ← ((List.finRange n).filter fun k => ij.1 < k ∧ k < ij.2).foldlM (fun s k => do
          let a ← rnd (T ij.1 k * F k ij.2)
          let t ← rnd (s + a)
          let b ← rnd (F ij.1 k * T k ij.2)
          rnd (t - b)) s₀
      let d ← rnd (T ij.2 ij.2 - T ij.1 ij.1)
      let v ← rnd (s / d)
      pure (F.updateRow ij.1 (Function.update (F ij.1) ij.2 v))) F₀

end Algorithm

/-- The pairs of `superdiagPairs n` are the strictly upper triangular positions. -/
private theorem mem_superdiagPairs {a b : Fin n} : (a, b) ∈ superdiagPairs n ↔ a < b := by
  simp only [superdiagPairs, List.mem_flatMap, List.mem_range', List.mem_filterMap,
    List.mem_finRange, true_and, Option.dite_none_right_eq_some, Option.some.injEq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨p, ⟨k, hk, rfl⟩, i, h, rfl, rfl⟩
    rw [Fin.lt_def]
    simp only
    omega
  · intro hab
    rw [Fin.lt_def] at hab
    refine ⟨(b : ℕ) - a, ⟨(b : ℕ) - a - 1, by omega, by omega⟩, a, by omega, rfl, ?_⟩
    ext
    simp only
    omega

/-- `superdiagPairs n` visits the superdiagonals in order. -/
private theorem pairwise_superdiagPairs :
    (superdiagPairs n).Pairwise fun x y => (x.2 : ℕ) - x.1 ≤ (y.2 : ℕ) - y.1 := by
  have hdiff : ∀ p, ∀ x ∈ (List.finRange n).filterMap (fun (i : Fin n) =>
      if h : (i : ℕ) + p < n then some (i, (⟨i + p, h⟩ : Fin n)) else none),
      (x.2 : ℕ) - x.1 = p := by
    intro p x hx
    simp only [List.mem_filterMap, List.mem_finRange, true_and,
      Option.dite_none_right_eq_some, Option.some.injEq] at hx
    obtain ⟨i, h, rfl⟩ := hx
    simp
  rw [superdiagPairs, List.pairwise_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      fun _ _ => trivial)
    intro x y hx hy _
    rw [hdiff p x hx, hdiff p y hy]
  · refine (List.pairwise_lt_range' (s := 1) (n := n - 1)).imp_of_mem ?_
    intro p q _ _ hpq x hx y hy
    rw [hdiff p x hx, hdiff q y hy]
    exact hpq.le

/-- The exact inner loop of Algorithm 9.1.1 is the running sum. -/
private theorem foldl_add_sub {ι : Type*} (a b : ι → ℂ) (l : List ι) (s₀ : ℂ) :
    l.foldl (fun s k => s + a k - b k) s₀ = s₀ + (l.map fun k => a k - b k).sum := by
  induction l generalizing s₀ with
  | nil => simp
  | cons k l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

/-- A sum over a filtered `List.finRange` is a `Finset` sum over the filter. -/
private theorem sum_map_filter_finRange (P : Fin n → Prop) [DecidablePred P] (g : Fin n → ℂ) :
    (((List.finRange n).filter fun k => decide (P k)).map g).sum = ∑ k with P k, g k := by
  rw [Finset.sum_filter, Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

/-- **Exact semantics of Algorithm 9.1.1**: for upper triangular `T` with distinct diagonal
entries, the algorithm returns `f(T)`. Each step is the Parlett recurrence (9.1.11), whose right
side reads only entries on earlier superdiagonals. -/
theorem algorithm_9_1_1_spec (f : ℂ → ℂ) {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsUpperTriangular) (hdist : Function.Injective fun i => T i i) :
    Id.run (algorithm_9_1_1 pure f T) = pfc f T := by
  set G := pfc f T with hG
  have hGu : G.IsUpperTriangular := Matrix.BlockTriangular.pfc hT f
  -- the exact loop body
  let body : Matrix (Fin n) (Fin n) ℂ → Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ := fun F ij =>
    F.updateRow ij.1 (Function.update (F ij.1) ij.2
      ((((List.finRange n).filter fun k => ij.1 < k ∧ k < ij.2).foldl
        (fun s k => s + T ij.1 k * F k ij.2 - F ij.1 k * T k ij.2)
        (T ij.1 ij.2 * (F ij.2 ij.2 - F ij.1 ij.1))) / (T ij.2 ij.2 - T ij.1 ij.1)))
  let F₀ : Matrix (Fin n) (Fin n) ℂ := (List.finRange n).foldl
    (fun F i => F.updateRow i (Function.update (F i) i (f (T i i)))) 0
  have hrun : Id.run (algorithm_9_1_1 pure f T) = (superdiagPairs n).foldl body F₀ := by
    simp only [algorithm_9_1_1, Id.run_bind, Id.run_pure, List.idRun_foldlM]
    rfl
  -- the diagonal and lower triangle after the first loop
  have key : ∀ (l : List (Fin n)) (F : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n),
      (l.foldl (fun F i => F.updateRow i (Function.update (F i) i (f (T i i)))) F) a b =
        if a = b ∧ a ∈ l then f (T a a) else F a b := by
    intro l
    induction l with
    | nil => intro F a b; simp
    | cons x l ih =>
      intro F a b
      rw [List.foldl_cons, ih]
      by_cases hab : a = b
      · subst hab
        by_cases hax : a = x
        · subst hax
          simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, hax]
      · rw [ite_eq_right (fun h => hab h.1), ite_eq_right (fun h => hab h.1),
          Matrix.updateRow_apply]
        split_ifs with hax
        · subst hax
          rw [Function.update_of_ne (Ne.symm hab)]
        · rfl
  have hF₀ : ∀ a b : Fin n, b ≤ a → F₀ a b = G a b := by
    intro a b hba
    rw [show F₀ a b = if a = b ∧ a ∈ List.finRange n then f (T a a)
      else (0 : Matrix (Fin n) (Fin n) ℂ) a b from key _ _ a b]
    rcases eq_or_lt_of_le hba with rfl | hlt
    · rw [ite_eq_left ⟨rfl, List.mem_finRange b⟩, hG, Matrix.pfc_apply_self_of_isUpperTriangular hT]
    · rw [ite_eq_right (fun h => (ne_of_gt hlt) h.1), Matrix.zero_apply,
        hGu (show id b < id a from hlt)]
  -- one step of the superdiagonal loop keeps the invariant
  have hstep : ∀ (pre : List (Fin n × Fin n)) (i j : Fin n) (post : List (Fin n × Fin n))
      (F : Matrix (Fin n) (Fin n) ℂ), pre ++ (i, j) :: post = superdiagPairs n →
      (∀ a b, b ≤ a ∨ (a, b) ∈ pre → F a b = G a b) →
      ∀ a b, b ≤ a ∨ (a, b) ∈ pre ++ [(i, j)] → body F (i, j) a b = G a b := by
    intro pre i j post F hL hF
    have hij : i < j := mem_superdiagPairs.mp (hL ▸ List.mem_append_right _ List.mem_cons_self)
    have hpre : ∀ a b : Fin n, a < b → (b : ℕ) - a < (j : ℕ) - i → (a, b) ∈ pre := by
      intro a b hab hd
      have hmem : (a, b) ∈ pre ++ (i, j) :: post := hL ▸ mem_superdiagPairs.mpr hab
      rcases List.mem_append.mp hmem with h | h
      · exact h
      · exfalso
        rcases List.mem_cons.mp h with h | h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          omega
        · have hp := pairwise_superdiagPairs (n := n)
          rw [← hL, List.pairwise_append, List.pairwise_cons] at hp
          have := hp.2.1.1 _ h
          simp only at this
          omega
    have hne : T i i ≠ T j j := fun h => (ne_of_lt hij) (hdist h)
    have hval : ((((List.finRange n).filter fun k => i < k ∧ k < j).foldl
        (fun s k => s + T i k * F k j - F i k * T k j) (T i j * (F j j - F i i))) /
          (T j j - T i i)) = G i j := by
      rw [foldl_add_sub, sum_map_filter_finRange (fun k => i < k ∧ k < j),
        hF j j (Or.inl le_rfl), hF i i (Or.inl le_rfl),
        hG, Matrix.pfc_apply_eq_parlett hT f hij hne, ← hG, add_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr (by ext k; simp) fun k hk => ?_
      rw [Finset.mem_Ioo] at hk
      rw [Fin.lt_def] at hij
      have hk1 := hk.1
      have hk2 := hk.2
      rw [Fin.lt_def] at hk1 hk2
      rw [hF k j (Or.inr (hpre k j hk.2 (by omega))), hF i k (Or.inr (hpre i k hk.1 (by omega)))]
    intro a b hab
    simp only [body, Matrix.updateRow_apply]
    by_cases hai : a = i
    · subst hai
      by_cases hbj : b = j
      · subst hbj
        rw [ite_eq_left rfl, Function.update_self, hval]
      · rw [ite_eq_left rfl, Function.update_of_ne hbj]
        refine hF a b ?_
        rcases hab with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · simp [hbj] at h
    · rw [ite_eq_right hai]
      refine hF a b ?_
      rcases hab with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr h
        · simp [hai] at h
  -- the whole loop
  have hfold : ∀ (post pre : List (Fin n × Fin n)) (F : Matrix (Fin n) (Fin n) ℂ),
      pre ++ post = superdiagPairs n → (∀ a b, b ≤ a ∨ (a, b) ∈ pre → F a b = G a b) →
      ∀ a b, post.foldl body F a b = G a b := by
    intro post
    induction post with
    | nil =>
      intro pre F hL hF a b
      rw [List.append_nil] at hL
      refine hF a b ?_
      rcases le_or_gt b a with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hL]; exact mem_superdiagPairs.mpr h)
    | cons x post ih =>
      intro pre F hL hF
      obtain ⟨i, j⟩ := x
      rw [List.foldl_cons]
      exact ih (pre ++ [(i, j)]) (body F (i, j)) (by rw [← hL]; simp)
        (hstep pre i j post F hL hF)
  ext a b
  rw [hrun]
  exact hfold _ [] F₀ (List.nil_append _) (fun a b h => hF₀ a b (h.resolve_right (by simp))) a b

/-! ### A block Schur–Parlett approach -/

/-- §9.1.5: for block upper triangular `T` (`T.BlockTriangular b`, `b : Fin n → Fin p` the block
index), the conformal blocks of `F = f(T)` satisfy `F_ij = 0` for `i > j` and
`F_ii = f(T_ii)`. -/
theorem blockParlett_diag {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) :
    (∀ i j : Fin p, j < i → (pfc f T).toBlock (b · = i) (b · = j) = 0) ∧
    ∀ i : Fin p, (pfc f T).toBlock (b · = i) (b · = i) = pfc f (T.toBlock (b · = i) (b · = i)) := by
  refine ⟨fun i j hji => ?_, fun i => Matrix.BlockTriangular.toBlock_pfc hT
    (IsAlgClosed.splits _) i f⟩
  ext x y
  rw [Matrix.toBlock_apply, Matrix.zero_apply]
  exact Matrix.BlockTriangular.pfc hT f (by rw [x.2, y.2]; exact hji)

/-- **(9.1.12), the block Parlett equations**: with blocks as in `blockParlett_diag` and `i < j`,
`F_ij T_jj - T_ii F_ij = T_ij F_jj - F_ii T_ij + ∑_{k=i+1}^{j-1} (T_ik F_kj - F_ik T_kj)`, a
Sylvester system for the block `F_ij` whose right side involves only blocks nearer the
diagonal. -/
theorem equation_9_1_12 {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) {i j : Fin p} (hij : i < j) :
    let F := pfc f T
    let blk := fun (X : Matrix (Fin n) (Fin n) ℂ) (k l : Fin p) => X.toBlock (b · = k) (b · = l)
    blk F i j * blk T j j - blk T i i * blk F i j =
      blk T i j * blk F j j - blk F i i * blk T i j +
        ∑ k ∈ Ioo i j, (blk T i k * blk F k j - blk F i k * blk T k j) :=
  Matrix.BlockTriangular.pfc_sylvester hT f hij

/-- A Sylvester equation `S D - D R = 0` between square matrices over any finite index types with
disjoint spectra has only the solution `D = 0`: reindex to `Fin` and apply Lemma 7.1.5. -/
private theorem eq_zero_of_mul_sub_mul_eq_zero {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {S : Matrix α α ℂ} {R : Matrix β β ℂ}
    (h : spectrum ℂ S ∩ spectrum ℂ R = ∅) {D : Matrix α β ℂ} (hD : S * D - D * R = 0) :
    D = 0 := by
  set e₁ := Fintype.equivFin α
  set e₂ := Fintype.equivFin β
  have hs₁ : spectrum ℂ (Matrix.reindex e₁ e₁ S) = spectrum ℂ S := by
    rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ e₁, AlgEquiv.spectrum_eq]
  have hs₂ : spectrum ℂ (Matrix.reindex e₂ e₂ R) = spectrum ℂ R := by
    rw [← Matrix.coe_reindexAlgEquiv ℂ ℂ e₂, AlgEquiv.spectrum_eq]
  have hbij := (Chapter07.lemma_7_1_5 (Matrix.reindex e₁ e₁ S) (Matrix.reindex e₂ e₂ R)).2
    (by rw [hs₁, hs₂]; exact h)
  have h0 : Matrix.sylvesterMap (Matrix.reindex e₁ e₁ S) (Matrix.reindex e₂ e₂ R)
      (Matrix.reindex e₁ e₂ D) = Matrix.sylvesterMap (Matrix.reindex e₁ e₁ S)
        (Matrix.reindex e₂ e₂ R) 0 := by
    rw [map_zero, Matrix.sylvesterMap_apply]
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    ext a c
    have := congrFun (congrFun hD (e₁.symm a)) (e₂.symm c)
    simpa [Matrix.sub_apply] using this
  have hD' := hbij.1 h0
  ext a c
  have := congrFun (congrFun hD' (e₁ a)) (e₂ c)
  simpa using this

/-- **§9.1.5, the blocks of `F = f(T)` one superdiagonal at a time**: if `T` is block upper
triangular and `λ(T_ii) ∩ λ(T_jj) = ∅` (as the clustering of §9.1.5 arranges), then `F_ij` is the
unique solution `X` of the Sylvester equation `X T_jj - T_ii X = C_ij`, `C_ij` the right side of
(9.1.12) — which involves only blocks of `F` nearer the diagonal. (9.1.12) and chapter 7's
Lemma 7.1.5 (`X ↦ T_ii X - X T_jj` is nonsingular iff the spectra are disjoint), on the blocks'
index types. -/
theorem equation_9_1_12_unique {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) {i j : Fin p} (hij : i < j)
    (hdisj : spectrum ℂ (T.toBlock (b · = i) (b · = i)) ∩
      spectrum ℂ (T.toBlock (b · = j) (b · = j)) = ∅) :
    let F := pfc f T
    let blk := fun (X : Matrix (Fin n) (Fin n) ℂ) (k l : Fin p) => X.toBlock (b · = k) (b · = l)
    ∀ X : Matrix {a // b a = i} {a // b a = j} ℂ,
      X * blk T j j - blk T i i * X =
          blk T i j * blk F j j - blk F i i * blk T i j +
            ∑ k ∈ Ioo i j, (blk T i k * blk F k j - blk F i k * blk T k j) ↔
        X = blk F i j := by
  have h12 := equation_9_1_12 hT f hij
  dsimp only at h12 ⊢
  intro X
  set Ti := T.toBlock (b · = i) (b · = i) with hTi
  set Tj := T.toBlock (b · = j) (b · = j) with hTj
  set Fij := (pfc f T).toBlock (b · = i) (b · = j) with hFij
  constructor
  · intro hX
    rw [← h12, ← sub_eq_zero] at hX
    refine sub_eq_zero.1 (eq_zero_of_mul_sub_mul_eq_zero hdisj ?_)
    calc Ti * (X - Fij) - (X - Fij) * Tj = -(X * Tj - Ti * X - (Fij * Tj - Ti * Fij)) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
      _ = 0 := by rw [hX, neg_zero]
  · rintro rfl
    exact h12

/-! ### Sensitivity of matrix functions -/

section Condition

/-- **The relative condition number of a matrix function** (§9.1.6):
`cond_rel(f, A) = lim_{ε → 0} sup_{‖E‖ ≤ ε‖A‖} ‖f(A + E) - f(A)‖ / (ε ‖f(A)‖)`, for a map
`F : V → V` of a normed space (for `f(A)`: `F = pfc f` on `ℂ^{n×n}` with a chosen norm). The
book's `lim` is made total as a `limsup` over `ε → 0⁺`, in `ℝ≥0∞`. -/
noncomputable def condRel {V : Type*} [NormedAddCommGroup V] (F : V → V) (A : V) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => ⨆ (E : V) (_ : ‖E‖ ≤ ε * ‖A‖),
    ‖F (A + E) - F A‖ₑ / (ENNReal.ofReal ε * ‖F A‖ₑ)) (𝓝[>] 0)

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The remainder of a Fréchet derivative is eventually small on the balls `‖E‖ ≤ ε ‖A‖`. -/
private theorem eventually_norm_remainder_le {F : V → V} {L : V →L[𝕜] V} {A : V}
    (hF : HasFDerivAt F L A) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ E : V, ‖E‖ ≤ ε * ‖A‖ → ‖F (A + E) - F A - L E‖ ≤ c * ‖E‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF).def hc
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp h
  have hA' : 0 < ‖A‖ + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / (‖A‖ + 1) by positivity)] with ε hε E hE
  refine hball ?_
  rw [dist_zero_right]
  calc ‖E‖ ≤ ε * ‖A‖ := hE
    _ ≤ ε * (‖A‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.1.le
    _ < ρ := (lt_div_iff₀ hA').mp hε.2

/-- The upper half of `condRel_eq_of_hasFDerivAt`. -/
private theorem eventually_condRel_le {F : V → V} {L : V →L[𝕜] V} {A : V}
    (hF : HasFDerivAt F L A) (hFA : F A ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ (E : V) (_ : ‖E‖ ≤ ε * ‖A‖),
      ‖F (A + E) - F A‖ₑ / (ENNReal.ofReal ε * ‖F A‖ₑ)) ≤
        ENNReal.ofReal ((‖L‖ + c) * ‖A‖ / ‖F A‖) := by
  filter_upwards [eventually_norm_remainder_le hF hc, self_mem_nhdsWithin] with ε hR hε
  have hε0 : 0 < ε := hε
  have hφ : 0 < ‖F A‖ := norm_pos_iff.mpr hFA
  refine iSup₂_le fun E hE => ENNReal.div_le_of_le_mul ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hε0.le,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖F (A + E) - F A‖ = ‖L E + (F (A + E) - F A - L E)‖ := by congr 1; abel
    _ ≤ ‖L E‖ + ‖F (A + E) - F A - L E‖ := norm_add_le _ _
    _ ≤ ‖L‖ * ‖E‖ + c * ‖E‖ := add_le_add (L.le_opNorm E) (hR E hE)
    _ = (‖L‖ + c) * ‖E‖ := by ring
    _ ≤ (‖L‖ + c) * (ε * ‖A‖) := by gcongr
    _ = (‖L‖ + c) * ‖A‖ / ‖F A‖ * (ε * ‖F A‖) := by field_simp

/-- The lower half of `condRel_eq_of_hasFDerivAt`. -/
private theorem eventually_le_condRel {F : V → V} {L : V →L[𝕜] V} {A : V}
    (hF : HasFDerivAt F L A) (hFA : F A ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((‖L‖ - c) * ‖A‖ / ‖F A‖) ≤
      ⨆ (E : V) (_ : ‖E‖ ≤ ε * ‖A‖), ‖F (A + E) - F A‖ₑ / (ENNReal.ofReal ε * ‖F A‖ₑ) := by
  have hφ : 0 < ‖F A‖ := norm_pos_iff.mpr hFA
  rcases le_or_gt ‖L‖ c with hLc | hLc
  · refine Eventually.of_forall fun ε => ?_
    rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _))]
    exact zero_le
  obtain ⟨x, hx1, hx⟩ := L.exists_lt_apply_of_lt_opNorm (show ‖L‖ - c / 2 < ‖L‖ by linarith)
  filter_upwards [eventually_norm_remainder_le hF (half_pos hc), self_mem_nhdsWithin]
    with ε hR hε
  have hε0 : 0 < ε := hε
  have hεA : 0 ≤ ε * ‖A‖ := by positivity
  set E : V := ((ε * ‖A‖ : ℝ) : 𝕜) • x with hEdef
  have hEn : ‖E‖ = ε * ‖A‖ * ‖x‖ := by
    rw [hEdef, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hεA]
  have hE : ‖E‖ ≤ ε * ‖A‖ := by
    rw [hEn]
    exact mul_le_of_le_one_right hεA hx1.le
  have hLE : ‖L E‖ = ε * ‖A‖ * ‖L x‖ := by
    rw [hEdef, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hεA]
  have hsub : ‖L E‖ ≤ ‖F (A + E) - F A‖ + ‖F (A + E) - F A - L E‖ := by
    calc ‖L E‖ = ‖(F (A + E) - F A) - (F (A + E) - F A - L E)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h3 : ε * ‖A‖ * (‖L‖ - c / 2) ≤ ε * ‖A‖ * ‖L x‖ := mul_le_mul_of_nonneg_left hx.le hεA
  have h4 : c / 2 * ‖E‖ ≤ c / 2 * (ε * ‖A‖) := mul_le_mul_of_nonneg_left hE (by positivity)
  have hmain : (‖L‖ - c) * ‖A‖ / ‖F A‖ * (ε * ‖F A‖) ≤ ‖F (A + E) - F A‖ := by
    have : (‖L‖ - c) * ‖A‖ / ‖F A‖ * (ε * ‖F A‖) = ε * ‖A‖ * (‖L‖ - c) := by
      field_simp
    rw [this]
    nlinarith [hR E hE]
  refine le_iSup₂_of_le E hE ?_
  have hden0 : ENNReal.ofReal ε * ‖F A‖ₑ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hε0).ne' (enorm_ne_zero.mpr hFA)
  have hdent : ENNReal.ofReal ε * ‖F A‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent), ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hε0.le,
    ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) hφ.le)]
  exact ENNReal.ofReal_le_ofReal hmain

/-- §9.1.6, "essentially a normalized Fréchet derivative", made precise: if `F` has Fréchet
derivative `L` at `A ≠ 0` and `F(A) ≠ 0`, then `cond_rel(F, A) = ‖L‖ ‖A‖ / ‖F(A)‖`. -/
theorem condRel_eq_of_hasFDerivAt {F : V → V} {L : V →L[𝕜] V} {A : V} (hF : HasFDerivAt F L A)
    (hA : A ≠ 0) (hFA : F A ≠ 0) : condRel F A = ‖L‖ₑ * ‖A‖ₑ / ‖F A‖ₑ := by
  have hφ : 0 < ‖F A‖ := norm_pos_iff.mpr hFA
  have ha : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hC : ‖L‖ₑ * ‖A‖ₑ / ‖F A‖ₑ = ENNReal.ofReal (‖L‖ * ‖A‖ / ‖F A‖) := by
    rw [ENNReal.ofReal_div_of_pos hφ, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
      ofReal_norm, ofReal_norm]
  rw [hC]
  refine Tendsto.limsup_eq (tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩)
  · have hbt : b ≠ ⊤ := ne_top_of_lt hb
    have hb' : b.toReal < ‖L‖ * ‖A‖ / ‖F A‖ := (ENNReal.lt_ofReal_iff_toReal_lt hbt).mp hb
    have hc : 0 < (‖L‖ * ‖A‖ / ‖F A‖ - b.toReal) * ‖F A‖ / (2 * ‖A‖) :=
      div_pos (mul_pos (sub_pos.mpr hb') hφ) (by positivity)
    filter_upwards [eventually_le_condRel hF hFA hc] with ε hε
    refine lt_of_lt_of_le ?_ hε
    rw [ENNReal.lt_ofReal_iff_toReal_lt hbt]
    have : (‖L‖ - (‖L‖ * ‖A‖ / ‖F A‖ - b.toReal) * ‖F A‖ / (2 * ‖A‖)) * ‖A‖ / ‖F A‖ =
        ‖L‖ * ‖A‖ / ‖F A‖ - (‖L‖ * ‖A‖ / ‖F A‖ - b.toReal) / 2 := by
      field_simp
    rw [this]
    linarith
  · by_cases hbt : b = ⊤
    · filter_upwards [eventually_condRel_le hF hFA one_pos] with ε hε
      exact lt_of_le_of_lt hε (hbt ▸ ENNReal.ofReal_lt_top)
    · have hb' : ‖L‖ * ‖A‖ / ‖F A‖ < b.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbt).mp hb
      have hc : 0 < (b.toReal - ‖L‖ * ‖A‖ / ‖F A‖) * ‖F A‖ / (2 * ‖A‖) :=
        div_pos (mul_pos (sub_pos.mpr hb') hφ) (by positivity)
      filter_upwards [eventually_condRel_le hF hFA hc] with ε hε
      refine lt_of_le_of_lt hε ?_
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbt]
      have : (‖L‖ + (b.toReal - ‖L‖ * ‖A‖ / ‖F A‖) * ‖F A‖ / (2 * ‖A‖)) * ‖A‖ / ‖F A‖ =
          ‖L‖ * ‖A‖ / ‖F A‖ + (b.toReal - ‖L‖ * ‖A‖ / ‖F A‖) / 2 := by
        field_simp
      rw [this]
      linarith

end Condition

end GolubVanLoan.Chapter09
