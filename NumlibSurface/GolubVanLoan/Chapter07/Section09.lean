import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Pseudospectrum
import NumlibSurface.GolubVanLoan.Chapter07.Section03

/-!
# Golub–Van Loan §7.9: pseudospectra

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.9: matrix powers and the spectral radius ((7.9.1)–(7.9.3) and the `2 × 2`
power bound), the `ε`-pseudospectrum and its three definitions ((7.9.5)–(7.9.7)), monotonicity and
the connected components, the elementary properties (Theorems 7.9.1–7.9.8 with Corollaries
7.9.3, 7.9.5, 7.9.7), computing `σ_min(zI - A)` through a Schur form (§7.9.5), the pseudospectral
abscissa and radius ((7.9.8)–(7.9.9)) with the ray-crossing matrix (7.9.10) and the
characterization of the largest crossing, and transient growth (7.9.11).

## Conventions

Complex matrices; the 2-norm is the scoped `Matrix.Norms.L2Operator` norm and
`σ_min(M) = ⨅ i, M.singularValues i` (the backbone's column-indexed `Matrix.singularValues`). The
surface defines `pseudospectrum ε A` literally by (7.9.5), `{z | σ_min(A - z I) ≤ ε}` (the book
writes `λ` for `z` inside the set-builder, a misprint), for a matrix over any finite index type —
the book's `n × n`, and the block matrices of Theorem 7.9.6 on `Fin p ⊕ Fin q` — and proves it
equal to the backbone's `(toEuclideanCLM A).closedPseudospectrum ε`, the approximate-eigenvector
form (`pseudospectrum_eq`, for a nonempty index type). The resolvent form (7.9.6) is stated for
`ε > 0` with `λ(A) ⊆ Λ_ε(A)` explicit, since `‖(zI - A)⁻¹‖ ≥ 1/ε` has no meaning at an eigenvalue
(Lean's matrix inverse is `0` there).

## Not formalized

(7.9.4) (it repeats (7.9.1) and illustrates transient growth); the Eigtool plots and the Kahan,
Demmel and `Gallery(5)` matrices; the strategies of §7.9.5 for computing pseudospectra and the
Burke–Lewis–Overton and Mengi–Overton algorithms; "`σ_min(zI - T) ≈ 1/‖y‖₂`" (heuristic).
-/

open Matrix Filter Topology Metric

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.9.1 Motivation: matrix powers -/

section L2

open scoped Matrix.Norms.L2Operator

/-- **(7.9.1), rigorous.** For every `ε > 0` there is `C` with `‖A^k‖₂ ≤ C (ρ(A) + ε)^k` for all
`k`, and `‖A^k‖₂^{1/k} → ρ(A)` (Gelfand's formula): if `ρ(A) < 1` then `A^k → 0`, and the decay is
"like `ρ(A)^k`" in this sense. -/
theorem equation_7_9_1 (A : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 (spectralRadius A)) ∧
      ∀ ε > 0, ∃ C : ℝ, ∀ k : ℕ, ‖A ^ k‖ ≤ C * (spectralRadius A + ε) ^ k := by
  have := FiniteDimensional.complete ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hfin : _root_.spectralRadius ℂ A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm A)
  have hlim : Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / k : ℝ)) atTop (𝓝 (spectralRadius A)) := by
    have h := (ENNReal.tendsto_toReal hfin).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A)
    rw [spectralRadius_eq]
    refine h.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm]
  refine ⟨hlim, fun ε hε => ?_⟩
  have hρ0 : 0 ≤ spectralRadius A := by rw [spectralRadius_eq]; exact ENNReal.toReal_nonneg
  have hpos : 0 < spectralRadius A + ε := by linarith
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hlim.eventually (gt_mem_nhds (by linarith :
    spectralRadius A < spectralRadius A + ε))).and (eventually_ge_atTop 1))
  refine ⟨1 + ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k, fun k => ?_⟩
  have hsum : 0 ≤ ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases lt_or_ge k K with hk | hk
  · have hle : ‖A ^ k‖ / (spectralRadius A + ε) ^ k ≤
        1 + ∑ k ∈ Finset.range K, ‖A ^ k‖ / (spectralRadius A + ε) ^ k := by
      have := Finset.single_le_sum (f := fun k => ‖A ^ k‖ / (spectralRadius A + ε) ^ k)
        (fun _ _ => by positivity) (Finset.mem_range.2 hk)
      linarith
    calc ‖A ^ k‖ = ‖A ^ k‖ / (spectralRadius A + ε) ^ k * (spectralRadius A + ε) ^ k := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (by positivity)
  · obtain ⟨hlt, hk1⟩ := hK k hk
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have h1 : ‖A ^ k‖ ≤ (spectralRadius A + ε) ^ k := by
      have h2 := Real.rpow_le_rpow (by positivity) hlt.le (Nat.cast_nonneg k)
      rwa [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hk0, Real.rpow_one,
        Real.rpow_natCast] at h2
    calc ‖A ^ k‖ ≤ 1 * (spectralRadius A + ε) ^ k := by rw [one_mul]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end L2

/-- **(7.9.2).** For `λ₁ ≠ λ₂`, `[λ₁ M; 0 λ₂] = X diag(λ₁, λ₂) X⁻¹` with `X = [1 M/(λ₂ - λ₁); 0 1]`.
-/
theorem equation_7_9_2 {l₁ l₂ M : ℂ} (hl : l₁ ≠ l₂) :
    !![l₁, M; 0, l₂] = !![1, M / (l₂ - l₁); 0, 1] * diagonal ![l₁, l₂] *
      (!![1, M / (l₂ - l₁); 0, 1])⁻¹ := by
  have hsub : l₂ - l₁ ≠ 0 := sub_ne_zero.2 hl.symm
  set X : Matrix (Fin 2) (Fin 2) ℂ := !![1, M / (l₂ - l₁); 0, 1] with hX
  have hXd : IsUnit X.det := by
    rw [hX, det_fin_two]
    simp
  have hAX : !![l₁, M; 0, l₂] * X = X * diagonal ![l₁, l₂] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [X, mul_apply, Fin.sum_univ_two]
    · simpa [X, mul_apply, Fin.sum_univ_two] using
        (show l₁ * (M / (l₂ - l₁)) + M = M / (l₂ - l₁) * l₂ by field_simp; ring)
    · simp [X, mul_apply, Fin.sum_univ_two]
    · simp [X, mul_apply, Fin.sum_univ_two]
  rw [← hAX, Matrix.mul_assoc, mul_nonsing_inv _ hXd, Matrix.mul_one]

/-- **(7.9.3).** `[λ₁ M; 0 λ₂]^k = [λ₁^k, M ∑_{j=0}^{k-1} λ₁^{k-1-j} λ₂^j; 0, λ₂^k]` (no hypothesis
`λ₁ ≠ λ₂` is needed, although the book derives it from (7.9.2)). -/
theorem equation_7_9_3 (l₁ l₂ M : ℂ) (k : ℕ) :
    !![l₁, M; 0, l₂] ^ k =
      !![l₁ ^ k, M * ∑ j ∈ Finset.range k, l₂ ^ j * l₁ ^ (k - 1 - j); 0, l₂ ^ k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ', ih, Nat.add_sub_cancel, geom_sum₂_succ_eq]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [mul_apply, Fin.sum_univ_two, pow_succ']
    · simp [mul_apply, Fin.sum_univ_two]
      ring
    · simp [mul_apply, Fin.sum_univ_two]
    · simp [mul_apply, Fin.sum_univ_two, pow_succ']

/-- The strictly upper part of the `2 × 2` upper triangular example. -/
private theorem strictUpper_two_by_two (l₁ l₂ M : ℂ) :
    strictUpper !![l₁, M; 0, l₂] = !![0, M; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [strictUpper_apply]

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius norm of the strictly upper part of `[λ₁ M; 0 λ₂]` is `M` for `M ≥ 0`. -/
private theorem frobenius_norm_strictUpper_two_by_two (l₁ l₂ : ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ‖strictUpper !![l₁, (M : ℂ); 0, l₂]‖ = M := by
  rw [strictUpper_two_by_two, frobenius_norm_def]
  simp only [of_apply, cons_val', cons_val_fin_one, Real.rpow_ofNat, Fin.sum_univ_two, Fin.isValue,
    cons_val_zero, cons_val_one, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, zero_add, add_zero, one_div]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  norm_num

section L2

open scoped Matrix.Norms.L2Operator

/-- **§7.9.1**: for `A = [λ₁ M; 0 λ₂]` with `M > 0`, (a) `‖A^k‖₂ → 0` iff `|λ₁| < 1` and
`|λ₂| < 1`, and (b) `‖A^k‖₂ ≤ (M/ε)(ρ(A) + ε)^k` for all `k`, with `ρ(A) = max{|λ₁|, |λ₂|}`, for
every `0 < ε ≤ M` — Lemma 7.3.2 with `n = 2` and `1 + μ = M/ε` (the book cites it as "Lemma
7.3.1"). The book says "for any `ε > 0`"; at `k = 0` the bound reads `1 ≤ M/ε`, so `ε ≤ M` is
needed. -/
theorem two_by_two_power_bound {l₁ l₂ : ℂ} {M : ℝ} (hM : 0 < M) :
    (Tendsto (fun k : ℕ => ‖!![l₁, (M : ℂ); 0, l₂] ^ k‖) atTop (𝓝 0) ↔
        ‖l₁‖ < 1 ∧ ‖l₂‖ < 1) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ M → ∀ k : ℕ,
        ‖!![l₁, (M : ℂ); 0, l₂] ^ k‖ ≤ M / ε * (max ‖l₁‖ ‖l₂‖ + ε) ^ k := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![l₁, (M : ℂ); 0, l₂] with hA
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ M → ∀ k : ℕ,
      ‖A ^ k‖ ≤ M / ε * (max ‖l₁‖ ‖l₂‖ + ε) ^ k := by
    intro ε hε hεM k
    have hQ : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ := one_mem _
    have hT : star (1 : Matrix (Fin 2) (Fin 2) ℂ) * A * 1 = A := by simp
    have hTu : A.IsUpperTriangular := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [A]
    have hμ : 0 ≤ M / ε - 1 := by
      rw [sub_nonneg, le_div_iff₀ hε, one_mul]
      exact hεM
    have h := (lemma_7_3_2 hQ hT hTu hμ).1 k
    have hsup : ⨆ i, ‖A i i‖ = max ‖l₁‖ ‖l₂‖ := by
      refine le_antisymm (ciSup_le fun i => ?_) (max_le ?_ ?_)
      · fin_cases i <;> simp [A]
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove 0 (by simp [A])
      · exact le_ciSup_of_le (Set.finite_range _).bddAbove 1 (by simp [A])
    rw [lpOpNorm_two, hsup, frobenius_norm_strictUpper_two_by_two l₁ l₂ hM.le] at h
    have h1 : 1 + (M / ε - 1) = M / ε := by ring
    have h2 : M / (M / ε) = ε := by field_simp
    rwa [h1, h2, show 2 - 1 = 1 from rfl, pow_one] at h
  refine ⟨⟨fun h => ?_, fun ⟨h₁, h₂⟩ => ?_⟩, hbound⟩
  · have hpow : ∀ k : ℕ, A ^ k = !![l₁ ^ k,
        (M : ℂ) * ∑ j ∈ Finset.range k, l₂ ^ j * l₁ ^ (k - 1 - j); 0, l₂ ^ k] :=
      equation_7_9_3 l₁ l₂ M
    have hlim : ∀ i : Fin 2, Tendsto (fun k : ℕ => ‖(A ^ k) i i‖) atTop (𝓝 0) := fun i =>
      squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_entry_le_l2_opNorm _ i i) h
    have e₁ := hlim 0
    have e₂ := hlim 1
    simp only [hpow, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, norm_pow] at e₁ e₂
    refine ⟨?_, ?_⟩
    · have := tendsto_pow_atTop_nhds_zero_iff.1 e₁
      rwa [abs_norm] at this
    · have := tendsto_pow_atTop_nhds_zero_iff.1 e₂
      rwa [abs_norm] at this
  · set ρ := max ‖l₁‖ ‖l₂‖ with hρ
    have hρ1 : ρ < 1 := max_lt h₁ h₂
    have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
    set ε := min M ((1 - ρ) / 2) with hε
    have hε0 : 0 < ε := lt_min hM (by linarith)
    have hεM : ε ≤ M := min_le_left _ _
    have hlt : ρ + ε < 1 := by
      have : ε ≤ (1 - ρ) / 2 := min_le_right _ _
      linarith
    have hgeo : Tendsto (fun k : ℕ => M / ε * (ρ + ε) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) hlt).const_mul (M / ε)
    exact squeeze_zero (fun _ => norm_nonneg _) (hbound ε hε0 hεM) hgeo

end L2

/-! ### §7.9.2 Definitions -/

section Pseudospectrum

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **(7.9.5), the `ε`-pseudospectrum** `Λ_ε(A) = {z ∈ ℂ : σ_min(A - z I) ≤ ε}`, with
`σ_min(M) = ⨅ i, M.singularValues i`. Its members are the `ε`-pseudoeigenvalues; for a nonempty
index type it is the backbone's closed pseudospectrum of the Euclidean operator of `A`
(`pseudospectrum_eq`). -/
noncomputable def pseudospectrum (ε : ℝ) (A : Matrix m m ℂ) : Set ℂ :=
  {z | ⨅ i, (A - z • 1).singularValues i ≤ ε}

/-- The residual `‖A w - z w‖` is the image of `w` under `A - z I`. -/
private theorem toEuclideanLin_sub_smul (A : Matrix m m ℂ) (z : ℂ) (w : EuclideanSpace ℂ m) :
    toEuclideanLin (A - z • 1) w = toEuclideanCLM (n := m) (𝕜 := ℂ) A w - z • w := by
  rw [map_sub, map_smul, toLpLin_one, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rfl

/-- The least singular value of `A - z I` is the least residual on the unit sphere. -/
private theorem iInf_singularValues_sub_smul (A : Matrix m m ℂ) (z : ℂ) :
    ⨅ i, (A - z • 1).singularValues i =
      ⨅ w : {w : EuclideanSpace ℂ m // ‖w‖ = 1},
        ‖toEuclideanCLM (n := m) (𝕜 := ℂ) A w - z • (w : EuclideanSpace ℂ m)‖ := by
  rw [iInf_singularValues_eq_iInf_norm]
  simp only [toEuclideanLin_sub_smul]

/-- The pseudospectrum (7.9.5) is the backbone's closed pseudospectrum of the Euclidean operator
of `A`: `σ_min(A - z I)` is the least residual `min_{‖w‖₂ = 1} ‖(A - z I) w‖₂`. -/
theorem pseudospectrum_eq [Nonempty m] (ε : ℝ) (A : Matrix m m ℂ) :
    pseudospectrum ε A = (toEuclideanCLM (n := m) (𝕜 := ℂ) A).closedPseudospectrum ε := by
  ext z
  rw [ContinuousLinearMap.mem_closedPseudospectrum_iff_iInf, ← iInf_singularValues_sub_smul]
  rfl

/-- The spectrum of the Euclidean operator of a matrix is the spectrum of the matrix. -/
private theorem spectrum_toEuclideanCLM (A : Matrix m m ℂ) :
    spectrum ℂ (toEuclideanCLM (n := m) (𝕜 := ℂ) A) = spectrum ℂ A :=
  AlgEquiv.spectrum_eq (toEuclideanCLM (n := m) (𝕜 := ℂ)) A

/-- **§7.9.2–7.9.3**: `Λ₀(A) = λ(A)`, and `ε₁ ≤ ε₂ → Λ_{ε₁}(A) ⊆ Λ_{ε₂}(A)`. -/
theorem pseudospectrum_zero [Nonempty m] (A : Matrix m m ℂ) :
    pseudospectrum 0 A = spectrum ℂ A ∧
      ∀ ε₁ ε₂ : ℝ, ε₁ ≤ ε₂ → pseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A := by
  refine ⟨?_, fun ε₁ ε₂ h => ?_⟩
  · rw [pseudospectrum_eq, ContinuousLinearMap.closedPseudospectrum_zero, spectrum_toEuclideanCLM]
  · rw [pseudospectrum_eq, pseudospectrum_eq]
    exact ContinuousLinearMap.closedPseudospectrum_mono h

section L2

open scoped Matrix.Norms.L2Operator

/-- The Euclidean operator of the matrix inverse is the ring inverse of the Euclidean operator. -/
private theorem toEuclideanCLM_inv (M : Matrix m m ℂ) :
    toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ = Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := by
  by_cases hM : IsUnit M.det
  · have h1 : toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ * toEuclideanCLM (n := m) (𝕜 := ℂ) M = 1 := by
      rw [← map_mul, nonsing_inv_mul _ hM, map_one]
    have h2 : toEuclideanCLM (n := m) (𝕜 := ℂ) M * toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ = 1 := by
      rw [← map_mul, mul_nonsing_inv _ hM, map_one]
    have hu : IsUnit (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := ⟨⟨_, _, h2, h1⟩, rfl⟩
    symm
    calc Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M)
        = Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M) *
            (toEuclideanCLM (n := m) (𝕜 := ℂ) M * toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹) := by
          rw [h2, mul_one]
      _ = toEuclideanCLM (n := m) (𝕜 := ℂ) M⁻¹ := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  · have hT : ¬ IsUnit (toEuclideanCLM (n := m) (𝕜 := ℂ) M) := fun h => by
      apply hM
      refine isUnit_det_of_right_inverse (B := (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm
        (Ring.inverse (toEuclideanCLM (n := m) (𝕜 := ℂ) M))) ?_
      have h3 := congrArg (toEuclideanCLM (n := m) (𝕜 := ℂ)).symm (Ring.mul_inverse_cancel _ h)
      rwa [map_mul, StarAlgEquiv.symm_apply_apply, map_one] at h3
    rw [nonsing_inv_apply_not_isUnit _ hM, map_zero, Ring.inverse_non_unit _ hT]

/-- **(7.9.6)**: for `ε > 0`, `z ∈ Λ_ε(A)` exactly when `z ∈ λ(A)` or `‖(zI - A)⁻¹‖₂ ≥ 1/ε` (the
book's resolvent form, with the eigenvalues included explicitly). -/
theorem equation_7_9_6 [Nonempty m] {ε : ℝ} (hε : 0 < ε) (A : Matrix m m ℂ) (z : ℂ) :
    z ∈ pseudospectrum ε A ↔ z ∈ spectrum ℂ A ∨ 1 / ε ≤ ‖(z • 1 - A)⁻¹‖ := by
  rw [pseudospectrum_eq, ContinuousLinearMap.mem_closedPseudospectrum_iff_resolvent hε,
    spectrum_toEuclideanCLM, ← l2_opNorm_toEuclideanCLM, toEuclideanCLM_inv, map_sub, map_smul,
    map_one]

/-- **(7.9.7)**: `z ∈ Λ_ε(A)` exactly when `z` is an eigenvalue of `A + E` for some `E` with
`‖E‖₂ ≤ ε`. -/
theorem equation_7_9_7 [Nonempty m] (ε : ℝ) (A : Matrix m m ℂ) (z : ℂ) :
    z ∈ pseudospectrum ε A ↔ ∃ E : Matrix m m ℂ, ‖E‖ ≤ ε ∧ z ∈ spectrum ℂ (A + E) := by
  rw [pseudospectrum_eq,
    ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add]
  constructor
  · rintro ⟨B, hB, hz⟩
    refine ⟨(toEuclideanCLM (n := m) (𝕜 := ℂ)).symm B, ?_, ?_⟩
    · rwa [← l2_opNorm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]
    · rwa [← spectrum_toEuclideanCLM, map_add, StarAlgEquiv.apply_symm_apply]
  · rintro ⟨E, hE, hz⟩
    refine ⟨toEuclideanCLM (n := m) (𝕜 := ℂ) E, by rwa [l2_opNorm_toEuclideanCLM], ?_⟩
    rwa [← map_add, spectrum_toEuclideanCLM]

end L2

/-- **§7.9.3**: "each connected component of `Λ_ε(A)` contains at least one eigenvalue of `A`". -/
theorem pseudospectrum_component [Nonempty m] {ε : ℝ} (A : Matrix m m ℂ) {z : ℂ}
    (hz : z ∈ pseudospectrum ε A) :
    ∃ μ ∈ spectrum ℂ A, μ ∈ connectedComponentIn (pseudospectrum ε A) z := by
  rw [pseudospectrum_eq] at hz ⊢
  obtain ⟨μ, hμ, hc⟩ := ContinuousLinearMap.exists_mem_spectrum_mem_connectedComponentIn _ hz
  exact ⟨μ, by rwa [spectrum_toEuclideanCLM] at hμ, hc⟩

/-! ### §7.9.4 Some elementary properties -/

/-- **Theorem 7.9.1**: `Λ_{ε|β|}(αI + βA) = α + β Λ_ε(A)` for `β ≠ 0`; at `β = 0` both sides are
`{α}` (for `ε ≥ 0`). (The book's proof's first chain ends in `= Λ_ε(A)` for `α + Λ_ε(A)`.) -/
theorem theorem_7_9_1 [Nonempty m] (A : Matrix m m ℂ) (α β : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    pseudospectrum (ε * ‖β‖) (α • 1 + β • A) = (fun z => α + β * z) '' pseudospectrum ε A := by
  rcases eq_or_ne β 0 with rfl | hβ
  · have hspec : spectrum ℂ (α • (1 : Matrix m m ℂ)) = {α} := by
      rw [← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq]
    rw [norm_zero, mul_zero, zero_smul, add_zero, (pseudospectrum_zero _).1, hspec]
    have hne : (pseudospectrum ε A).Nonempty := by
      rw [pseudospectrum_eq]
      exact ContinuousLinearMap.closedPseudospectrum_nonempty hε _
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_image, zero_mul, add_zero]
    exact ⟨fun h => ⟨_, hne.some_mem, h.symm⟩, fun ⟨_, _, h⟩ => h.symm⟩
  · rw [pseudospectrum_eq, pseudospectrum_eq, map_add, map_smul, map_smul, map_one]
    exact ContinuousLinearMap.closedPseudospectrum_smul_add α hβ

section L2

open scoped Matrix.Norms.L2Operator

/-- **Theorem 7.9.2**: if `B = X⁻¹ A X` then `Λ_ε(B) ⊆ Λ_{ε κ₂(X)}(A)`. (The book's proof writes
`X⁻¹ (zI - A)⁻¹ X⁻¹` for `X⁻¹ (zI - A)⁻¹ X`.) -/
theorem theorem_7_9_2 [Nonempty m] {X : Matrix m m ℂ} (hX : IsUnit X) (A : Matrix m m ℂ)
    (ε : ℝ) :
    pseudospectrum ε (X⁻¹ * A * X) ⊆ pseudospectrum (ε * NormedRing.condNumber X) A := by
  rw [pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_conj_subset hX A ε

end L2

/-- **Corollary 7.9.3**: for unitary `X`, `Λ_ε(X⁻¹ A X) = Λ_ε(A)`. -/
theorem corollary_7_9_3 [Nonempty m] {X : Matrix m m ℂ} (hX : X ∈ unitaryGroup m ℂ)
    (A : Matrix m m ℂ) (ε : ℝ) : pseudospectrum ε (X⁻¹ * A * X) = pseudospectrum ε A := by
  rw [Matrix.inv_eq_left_inv (mem_unitaryGroup_iff'.1 hX), pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_unitary_conj hX A ε

/-- **Theorem 7.9.4**: `Λ_ε(diag(λ₁, …, λₙ)) = {λ₁, …, λₙ} + Δ_ε`, the union of the closed discs of
radius `ε` about the diagonal entries. -/
theorem theorem_7_9_4 [Nonempty m] (d : m → ℂ) (ε : ℝ) :
    pseudospectrum ε (diagonal d) = ⋃ i, closedBall (d i) ε := by
  rw [pseudospectrum_eq]
  exact closedPseudospectrum_diagonal d ε

/-- **Corollary 7.9.5**: if `A` is normal, `Λ_ε(A) = Λ(A) + Δ_ε`. -/
theorem corollary_7_9_5 [Nonempty m] {A : Matrix m m ℂ} (hA : IsStarNormal A) (ε : ℝ) :
    pseudospectrum ε A = ⋃ μ ∈ spectrum ℂ A, closedBall μ ε := by
  rw [pseudospectrum_eq]
  exact closedPseudospectrum_of_isStarNormal hA ε

/-- **Theorem 7.9.6**: for `T = [T₁₁ T₁₂; 0 T₂₂]` with square diagonal blocks,
`Λ_ε(T₁₁) ∪ Λ_ε(T₂₂) ⊆ Λ_ε(T)`. -/
theorem theorem_7_9_6 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₁₂ : Matrix (Fin p) (Fin q) ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) (ε : ℝ) :
    pseudospectrum ε T₁₁ ∪ pseudospectrum ε T₂₂ ⊆ pseudospectrum ε (fromBlocks T₁₁ T₁₂ 0 T₂₂) := by
  rw [pseudospectrum_eq, pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_fromBlocks_zero₂₁_supset T₁₁ T₁₂ T₂₂ ε

/-- **Corollary 7.9.7**: `Λ_ε(diag(T₁₁, T₂₂)) = Λ_ε(T₁₁) ∪ Λ_ε(T₂₂)`. -/
theorem corollary_7_9_7 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) (ε : ℝ) :
    pseudospectrum ε (fromBlocks T₁₁ 0 0 T₂₂) = pseudospectrum ε T₁₁ ∪ pseudospectrum ε T₂₂ := by
  rw [pseudospectrum_eq, pseudospectrum_eq, pseudospectrum_eq]
  exact closedPseudospectrum_fromBlocks_diagonal T₁₁ T₂₂ ε

section L2

open scoped Matrix.Norms.L2Operator

/-- **Theorem 7.9.8**: every `z₀` is at distance at least `σ_min(z₀ I - A) - ε` from `Λ_ε(A)` (for
`ε ≥ 0`); for `z₀ ∉ λ(A)` this is the book's `dist(z₀, Λ_ε(A)) ≥ 1/‖(z₀ I - A)⁻¹‖₂ - ε`, since then
`σ_min(z₀ I - A) = 1/‖(z₀ I - A)⁻¹‖₂`. -/
theorem theorem_7_9_8 [Nonempty m] {ε : ℝ} (hε : 0 ≤ ε) (A : Matrix m m ℂ) (z₀ : ℂ) :
    (⨅ i, (z₀ • 1 - A).singularValues i) - ε ≤ infDist z₀ (pseudospectrum ε A) ∧
      (z₀ ∉ spectrum ℂ A → 1 / ‖(z₀ • 1 - A)⁻¹‖ - ε ≤ infDist z₀ (pseudospectrum ε A)) := by
  have hσ : ⨅ i, (z₀ • 1 - A).singularValues i = ⨅ i, (A - z₀ • 1).singularValues i := by
    rw [iInf_singularValues_eq_iInf_norm, iInf_singularValues_eq_iInf_norm]
    congr 1
    ext w
    rw [← neg_sub A, map_neg, LinearMap.neg_apply, norm_neg]
  have h1 : (⨅ i, (z₀ • 1 - A).singularValues i) - ε ≤ infDist z₀ (pseudospectrum ε A) := by
    rw [hσ, iInf_singularValues_sub_smul, pseudospectrum_eq]
    exact ContinuousLinearMap.le_infDist_closedPseudospectrum
      (ContinuousLinearMap.closedPseudospectrum_nonempty hε _) z₀
  refine ⟨h1, fun hz => le_trans ?_ h1⟩
  have hunit : IsUnit (z₀ • (1 : Matrix m m ℂ) - A).det := by
    rw [← isUnit_iff_isUnit_det]
    rwa [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hz
  rw [l2_opNorm_inv_eq_inv_iInf_singularValues _ hunit, one_div, inv_inv]

end L2

/-! ### §7.9.5 Computing pseudospectra -/

/-- **§7.9.5**: for a Schur decomposition `Qᴴ A Q = T`, `σ_min(zI - A) = σ_min(zI - T)`; and if
`‖d‖₂ = 1` and `(zI - T) y = d`, then `σ_min(zI - T) ≤ 1/‖y‖₂`. -/
theorem sigmaMin_schur [NeZero n] {A Q T : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hT : star Q * A * Q = T) (z : ℂ) :
    ⨅ i, (z • 1 - A).singularValues i = ⨅ i, (z • 1 - T).singularValues i ∧
      ∀ d y : EuclideanSpace ℂ (Fin n), ‖d‖ = 1 → toEuclideanLin (z • 1 - T) y = d →
        ⨅ i, (z • 1 - T).singularValues i ≤ 1 / ‖y‖ := by
  refine ⟨?_, fun d y hd hy => ?_⟩
  · have h : z • 1 - T = star Q * (z • 1 - A) * Q := by
      rw [← hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        mem_unitaryGroup_iff'.1 hQ]
    rw [h, iInf_singularValues_unitary_mul_mul _ (Unitary.star_mem hQ) hQ]
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [map_zero] at hy
      rw [← hy, norm_zero] at hd
      exact absurd hd zero_ne_one
    · have h := (z • 1 - T).iInf_singularValues_mul_norm_le y
      rw [hy, hd] at h
      rw [le_div_iff₀ (norm_pos_iff.2 hy0)]
      exact h

/-! ### §7.9.6 Computing the ε-pseudospectral abscissa and radius -/

/-- **(7.9.8), the pseudospectral abscissa** `α_ε(A) = max {Re(z) : z ∈ Λ_ε(A)}`, attained for a
nonempty index type and `ε ≥ 0`; it is the backbone's `Matrix.pseudospectralAbscissa`
(`pseudospectralAbscissa_spec`). -/
noncomputable def pseudospectralAbscissa (ε : ℝ) (A : Matrix m m ℂ) : ℝ :=
  sSup (Complex.re '' pseudospectrum ε A)

/-- **(7.9.9), the pseudospectral radius** `ρ_ε(A) = max {|z| : z ∈ Λ_ε(A)}`, attained for a
nonempty index type and `ε ≥ 0`; it is the backbone's `Matrix.pseudospectralRadius`
(`pseudospectralAbscissa_spec`). -/
noncomputable def pseudospectralRadius (ε : ℝ) (A : Matrix m m ℂ) : ℝ :=
  sSup ((‖·‖) '' pseudospectrum ε A)

/-- The pseudospectral abscissa and radius (7.9.8)–(7.9.9) are the backbone's, and both maxima are
attained. -/
theorem pseudospectralAbscissa_spec [Nonempty m] {ε : ℝ} (hε : 0 ≤ ε) (A : Matrix m m ℂ) :
    pseudospectralAbscissa ε A = Matrix.pseudospectralAbscissa ε A ∧
      pseudospectralRadius ε A = Matrix.pseudospectralRadius ε A ∧
      (∃ z ∈ pseudospectrum ε A, z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ pseudospectrum ε A, ‖z‖ = pseudospectralRadius ε A := by
  have ha : pseudospectralAbscissa ε A = Matrix.pseudospectralAbscissa ε A := by
    rw [pseudospectralAbscissa, pseudospectrum_eq]
    rfl
  have hr : pseudospectralRadius ε A = Matrix.pseudospectralRadius ε A := by
    rw [pseudospectralRadius, pseudospectrum_eq]
    rfl
  obtain ⟨h1, h2⟩ := Matrix.exists_eq_pseudospectralAbscissa_radius hε A
  rw [ha, hr, pseudospectrum_eq]
  exact ⟨rfl, rfl, h1, h2⟩

/-- **(7.9.10), the matrix** `M = [i e^{iθ} Aᴴ, -ε I; ε I, i e^{-iθ} A]` of §7.9.6, whose purely
imaginary eigenvalues `i r` locate the points `r e^{iθ}` of the ray of angle `θ` at which `ε` is a
singular value of `A - r e^{iθ} I` (Byers; Mengi and Overton). -/
noncomputable def rayCrossingMatrix (θ ε : ℝ) (A : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks ((Complex.I * Complex.exp (θ * Complex.I)) • Aᴴ) (-(ε : ℂ) • 1) ((ε : ℂ) • 1)
    ((Complex.I * Complex.exp (-(θ * Complex.I))) • A)

/-- `e^{iθ} e^{-iθ} = 1`. -/
private theorem exp_mul_exp_neg_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `(i e^{iθ}) (-(i e^{-iθ})) = 1`. -/
private theorem I_exp_mul_neg_I_exp (θ : ℝ) :
    Complex.I * Complex.exp (θ * Complex.I) * -(Complex.I * Complex.exp (-(θ * Complex.I))) =
      1 := by
  linear_combination (-Complex.I ^ 2) * exp_mul_exp_neg_mul_I θ - Complex.I_sq

omit [Fintype m] in
/-- `(A - r e^{iθ} I)ᴴ = Aᴴ - r e^{-iθ} I`. -/
private theorem conjTranspose_sub_ray (θ r : ℝ) (A : Matrix m m ℂ) :
    (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ =
      Aᴴ - ((r : ℂ) * Complex.exp (-(θ * Complex.I))) • 1 := by
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def, map_mul,
    Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg]

/-- The eigen-equation `M [f; g] = i r [f; g]` of (7.9.10), block row by block row, in terms of
`B = A - r e^{iθ} I`: `i e^{iθ} Bᴴ f = ε g` and `ε f = -i e^{-iθ} B g`. -/
private theorem rayCrossingMatrix_mulVec_eq_iff (θ r ε : ℝ) (A : Matrix m m ℂ) (f g : m → ℂ) :
    rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g ↔
      (Complex.I * Complex.exp (θ * Complex.I)) •
          ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *ᵥ f) = (ε : ℂ) • g ∧
        (ε : ℂ) • f = -(Complex.I * Complex.exp (-(θ * Complex.I))) •
          ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1) *ᵥ g) := by
  have hcc := exp_mul_exp_neg_mul_I θ
  rw [conjTranspose_sub_ray, rayCrossingMatrix, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  generalize Complex.exp (θ * Complex.I) = c at hcc ⊢
  generalize Complex.exp (-(θ * Complex.I)) = c' at hcc ⊢
  have hs : (Complex.I * r) • Sum.elim f g =
      Sum.elim ((Complex.I * r) • f) ((Complex.I * r) • g) := by
    ext (i | i) <;> rfl
  rw [hs]
  simp only [smul_mulVec, one_mulVec, sub_mulVec]
  constructor
  · intro h
    have h1 := funext fun i => congrFun h (Sum.inl i)
    have h2 := funext fun i => congrFun h (Sum.inr i)
    simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2
    exact ⟨by linear_combination (norm := module) h1 - (Complex.I * r * hcc) • f,
      by linear_combination (norm := module) h2 - (Complex.I * r * hcc) • g⟩
  · rintro ⟨h1, h2⟩
    have e1 : (Complex.I * c) • (Aᴴ *ᵥ f) + (-(ε : ℂ)) • g = (Complex.I * r) • f := by
      linear_combination (norm := module) h1 + (Complex.I * r * hcc) • f
    have e2 : (ε : ℂ) • f + (Complex.I * c') • (A *ᵥ g) = (Complex.I * r) • g := by
      linear_combination (norm := module) h2 + (Complex.I * r * hcc) • g
    rw [e1, e2]

/-- If `Bᴴ B g = s² g` for some `g ≠ 0` and `s ≥ 0`, then `s` is a singular value of `B`. -/
private theorem exists_singularValues_eq_of_mulVec {B : Matrix m m ℂ} {g : m → ℂ} (hg : g ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) (h : (Bᴴ * B) *ᵥ g = ((s : ℂ) ^ 2) • g) :
    ∃ i, B.singularValues i = s := by
  have hspec : ((s ^ 2 : ℝ) : ℂ) ∈ spectrum ℂ (Bᴴ * B) := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := g)
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, hg⟩
    rw [toLin'_apply, h]
    push_cast
    rfl
  rw [(isHermitian_conjTranspose_mul_self B).spectrum_eq_image_range] at hspec
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hspec
  have he : (isHermitian_conjTranspose_mul_self B).eigenvalues i = s ^ 2 :=
    Complex.ofReal_injective hi
  refine ⟨i, (sq_eq_sq₀ (singularValues_nonneg _ _) hs).1 ?_⟩
  rw [sq_singularValues, he]

/-- **(7.9.10)**: "if `i · r` is an eigenvalue of the matrix `M`, then `ε` is a singular value of
`A - r e^{iθ} I`. To see this, observe that if `M [f; g] = i · r [f; g]`, then
`(A - r e^{iθ} I)ᴴ (A - r e^{iθ} I) g = ε² g`" — the Gram identity holds for every eigenvector
`[f; g]` of `M` for `i r`, and for `ε > 0` (where `g = 0` forces `f = 0`) the eigenvalues `i r` of
`M` are exactly the `r` for which `ε` is a singular value of `A - r e^{iθ} I` (the converse from a
singular pair). -/
theorem equation_7_9_10 (θ r ε : ℝ) (A : Matrix m m ℂ) :
    (∀ f g : m → ℂ, rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g →
      ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *
          (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)) *ᵥ g = ((ε : ℂ) ^ 2) • g) ∧
      (0 < ε → ((∃ v : m ⊕ m → ℂ, v ≠ 0 ∧
          rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * r) • v) ↔
        ∃ i, (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).singularValues i = ε)) := by
  have hdd := I_exp_mul_neg_I_exp θ
  have hgram : ∀ f g : m → ℂ,
      rayCrossingMatrix θ ε A *ᵥ Sum.elim f g = (Complex.I * r) • Sum.elim f g →
      ((A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)ᴴ *
          (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1)) *ᵥ g = ((ε : ℂ) ^ 2) • g := by
    intro f g h
    obtain ⟨h1, h2⟩ := (rayCrossingMatrix_mulVec_eq_iff θ r ε A f g).1 h
    rw [← mulVec_mulVec]
    generalize A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 = B at h1 h2 ⊢
    have h3 := congrArg (Bᴴ *ᵥ ·) h2
    simp only [mulVec_smul] at h3
    linear_combination (norm := module) (ε : ℂ) • h1 - (Complex.I * Complex.exp (θ * Complex.I)) •
      h3 - hdd • (Bᴴ *ᵥ (B *ᵥ g))
  refine ⟨hgram, fun hε => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv0, hv⟩
    rw [← Sum.elim_comp_inl_inr v] at hv hv0
    have hg : v ∘ Sum.inr ≠ 0 := by
      intro hg
      obtain ⟨-, h2⟩ := (rayCrossingMatrix_mulVec_eq_iff θ r ε A _ _).1 hv
      rw [hg, mulVec_zero, smul_zero, smul_eq_zero] at h2
      refine hv0 ?_
      rw [hg, h2.resolve_left (by exact_mod_cast hε.ne')]
      ext (i | i) <;> rfl
    exact exists_singularValues_eq_of_mulVec hg hε.le (hgram _ _ hv)
  · rintro ⟨i, hi⟩
    set B := A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 with hB
    obtain ⟨g, hg0, hgB⟩ : ∃ g : m → ℂ, g ≠ 0 ∧ Bᴴ *ᵥ (B *ᵥ g) = ((ε : ℂ) ^ 2) • g := by
      have h := (isHermitian_conjTranspose_mul_self B).mulVec_eigenvectorBasis i
      have he : (isHermitian_conjTranspose_mul_self B).eigenvalues i = ε ^ 2 := by
        rw [← sq_singularValues, hi]
      rw [he, ← mulVec_mulVec, ← Complex.coe_smul] at h
      refine ⟨_, fun h0 =>
        (isHermitian_conjTranspose_mul_self B).eigenvectorBasis.orthonormal.ne_zero i
          (by ext j; simpa using congrFun h0 j), ?_⟩
      rw [h]
      push_cast
      rfl
    have hεinv : (ε : ℂ) * (ε : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hε.ne')
    set d := Complex.I * Complex.exp (θ * Complex.I) with hd
    set d' := -(Complex.I * Complex.exp (-(θ * Complex.I))) with hd'
    refine ⟨Sum.elim (((ε : ℂ)⁻¹ * d') • (B *ᵥ g)) g, fun h0 => hg0 (funext fun j => by
      simpa using congrFun h0 (Sum.inr j)), ?_⟩
    refine (rayCrossingMatrix_mulVec_eq_iff θ r ε A _ _).2 ⟨?_, ?_⟩
    · rw [← hB, mulVec_smul, ← hd]
      linear_combination (norm := module) (d * (ε : ℂ)⁻¹ * d') • hgB +
        ((ε : ℂ) * (d * d') * hεinv) • g + ((ε : ℂ) * hdd) • g
    · rw [← hB, ← hd']
      linear_combination (norm := module) (d' * hεinv) • (B *ᵥ g)

open scoped Matrix.Norms.L2Operator in
/-- **§7.9.6**: "It can be shown that if `i r_max` is the largest pure imaginary eigenvalue of `M`,
then `ε = σ_min(A - r_max e^{iθ} I)`" — for `ε > 0`, with `σ_min = ⨅ i, σ_i`. `≤` is (7.9.10);
if it were `<`, the continuous `r ↦ σ_min(A - r e^{iθ} I)`, which grows like `|r|`, would take the
value `ε` at some `r > r_max` (intermediate value theorem), and `i r` would be an eigenvalue of `M`
by the converse of (7.9.10). So `r_max e^{iθ}` is the farthest point of the ray `{r e^{iθ}}` on the
boundary of `Λ_ε(A)`. -/
theorem equation_7_9_10_max {θ ε rmax : ℝ} (hε : 0 < ε) {A : Matrix m m ℂ}
    (hmax : ∃ v : m ⊕ m → ℂ, v ≠ 0 ∧ rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * rmax) • v)
    (hnot : ∀ r : ℝ, rmax < r → ∀ v : m ⊕ m → ℂ,
      rayCrossingMatrix θ ε A *ᵥ v = (Complex.I * r) • v → v = 0) :
    ⨅ i, (A - ((rmax : ℂ) * Complex.exp (θ * Complex.I)) • 1).singularValues i = ε := by
  set s : ℝ → ℝ := fun r =>
    ⨅ i, (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).singularValues i with hs
  obtain ⟨i₀, hi₀⟩ := ((equation_7_9_10 θ rmax ε A).2 hε).1 hmax
  have : Nonempty m := ⟨i₀⟩
  have hle : s rmax ≤ ε := hi₀ ▸ ciInf_le (Set.finite_range _).bddBelow i₀
  change s rmax = ε
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  have hcont : Continuous s := by
    have hlip : ∀ r r' : ℝ, dist (s r) (s r') ≤ (‖(1 : Matrix m m ℂ)‖₊ : ℝ) * dist r r' := by
      intro r r'
      rw [Real.dist_eq, Real.dist_eq, coe_nnnorm]
      refine (iInf_singularValues_sub_le _ _).trans (le_of_eq ?_)
      have e : A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1 -
          (A - ((r' : ℂ) * Complex.exp (θ * Complex.I)) • 1) =
          (((r' - r : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) • 1 := by
        push_cast
        module
      rw [e, norm_smul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
        Real.norm_eq_abs, abs_sub_comm]
      ring
    exact (LipschitzWith.of_dist_le_mul hlip).continuous
  have hgrow : ∀ r : ℝ, |r| - ‖A‖ ≤ s r := by
    intro r
    simp only [hs]
    rw [iInf_singularValues_eq_iInf_norm]
    have : Nonempty {x : EuclideanSpace ℂ m // ‖x‖ = 1} :=
      ⟨⟨EuclideanSpace.single i₀ 1, by simp⟩⟩
    refine le_ciInf fun x => ?_
    rw [toEuclideanLin_sub_smul]
    have h1 := norm_sub_norm_le (((r : ℂ) * Complex.exp (θ * Complex.I)) • (x : EuclideanSpace ℂ m))
      (toEuclideanCLM (n := m) (𝕜 := ℂ) A x)
    have h2 : ‖toEuclideanCLM (n := m) (𝕜 := ℂ) A x‖ ≤ ‖A‖ := by
      have := (toEuclideanCLM (n := m) (𝕜 := ℂ) A).le_opNorm x
      rwa [x.2, mul_one, l2_opNorm_toEuclideanCLM] at this
    rw [norm_smul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, x.2,
      Real.norm_eq_abs, mul_one, mul_one, norm_sub_rev] at h1
    linarith
  set R := |rmax| + ‖A‖ + ε + 1 with hR
  have hRmax : rmax < R := by
    have := le_abs_self rmax
    have := norm_nonneg A
    linarith
  have hsR : ε ≤ s R := by
    have h := hgrow R
    rw [abs_of_pos (by have := abs_nonneg rmax; have := norm_nonneg A; linarith : 0 < R)] at h
    have := abs_nonneg rmax
    linarith
  obtain ⟨r, ⟨hr1, -⟩, hr⟩ :=
    intermediate_value_Icc hRmax.le hcont.continuousOn ⟨hlt.le, hsR⟩
  have hrr : rmax < r := lt_of_le_of_ne hr1 fun h => by rw [← h] at hr; linarith
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
    (f := fun i => (A - ((r : ℂ) * Complex.exp (θ * Complex.I)) • 1).singularValues i)
  obtain ⟨v, hv0, hv⟩ := ((equation_7_9_10 θ r ε A).2 hε).2 ⟨i, hi.trans hr⟩
  exact hv0 (hnot r hrr v hv)

section L2

open scoped Matrix.Norms.L2Operator

/-- **(7.9.11)** (Trefethen–Embree pp. 160–161): for `ε > 0`, `sup_{k ≥ 0} ‖A^k‖₂ ≥ (ρ_ε(A) - 1)/ε`,
stated as: if `‖A^k‖₂ ≤ M` for all `k`, then `(ρ_ε(A) - 1)/ε ≤ M`. -/
theorem equation_7_9_11 [Nonempty m] {ε : ℝ} (hε : 0 < ε) (A : Matrix m m ℂ) {M : ℝ}
    (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) : (pseudospectralRadius ε A - 1) / ε ≤ M := by
  rw [(pseudospectralAbscissa_spec hε.le A).2.1]
  exact Matrix.pseudospectralRadius_sub_one_div_le_norm_pow hε A hM

end L2

end Pseudospectrum

end GolubVanLoan.Chapter07
