import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section06

/-!
# Quarteroni–Sacco–Saleri §5.7: the QR iteration with shifting techniques

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.7, over the backbone `Numlib/Eigen/QRAlgorithm` (the shifted QR
step and iterations, their similarity identities, and the reduction of a fixed shift to the basic
iteration on `A − μI`), and over §5.5's Property 5.9 and (5.37) for the convergence claim of
§5.7.1.

## Conventions

The shifted iterations are written as the book writes them, as recursions on `Matrix (Fin n)
(Fin n) 𝕜` for any `RCLike` field `𝕜` — real in §5.7.1, complex in §5.7.2 — with the QR
factorization `Matrix.qrQ`, `Matrix.qrR` of positive diagonal at every step; each recursion carries
its identification with the backbone's `Matrix.shiftedQrIterate`, `Matrix.rayleighShiftQrIterate`,
`Matrix.doubleShiftQrStep`. The similarity statements are the book's, over `ℝ` with orthogonal
matrices, and the double-shift step is over `ℂ` with unitary ones. As in §5.4, the iteration
starts from `T⁽⁰⁾ = A`; the book's `T⁽⁰⁾ = Q⁽⁰⁾ᵀ A Q⁽⁰⁾` in Hessenberg form is the case
`A := hessenbergReduce A₀` of §5.6.

## Contents

* `shiftedQrStep`, `shiftedQrIterate`, `shiftedQrStep_eq`, `shiftedQrIterate_eq` — the single-shift
  iteration (5.52).
* `shiftedQrIterate_eq_conj` — the shifted iterates are orthogonally similar to `A`.
* `shiftedQrIterate_eq_qrIterate`, `shiftedQrIterate_rate` — a fixed shift is the basic iteration
  on `A − μI`, and the convergence claim of §5.7.1.
* `equation_5_53`, `equation_5_53_eq`, `equation_5_53_eq_conj` — the Rayleigh-quotient shift
  `μ = t_nn^{(k)}`.
* `equation_5_55`, `equation_5_55_eq`, `equation_5_55_eq_conj` — the double-shift step.

## Readings and errata

The convergence claim of §5.7.1 is stated by the book with the non-strict ordering
`|λ_1 − μ| ≥ … ≥ |λ_n − μ|` and "a rate proportional to `|(λ_j − μ)/(λ_{j−1} − μ)|^k`"; with a tie
the ratio is `1` and nothing tends to zero, so `shiftedQrIterate_rate` takes the strict ordering
and `|λ_n − μ| > 0`, together with the general-position hypothesis of Property 5.9 for the
eigenvector matrix, which the shift does not change. The two quadratic-convergence claims — for
the Rayleigh shift (5.53) and for the Francis double shift of §5.7.2 — are stated by the book
without proof and are not formalized (`equation_5_53_quadratic`, `doubleShiftQr_quadratic`); the
stopping test (5.54) is part of a program. "Remark 5.13", cited in §5.7.2, does not exist
(Exercise 14 is meant). Examples 5.10–5.13 are numerical and Programs 36–37 are not nodes.
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### (5.52): the QR method with single shift -/

/-- **(5.52), one step of the QR iteration with shift `μ`**: determine `Q`, `R` with
`Q R = T − μ I` (the QR factorization), then let `T' = R Q + μ I`. -/
noncomputable def shiftedQrStep (μ : 𝕜) (T : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  qrR (T - μ • 1) * qrQ (T - μ • 1) + μ • 1

/-- **(5.52), the shifted QR iteration** with fixed shift `μ`, from `T⁽⁰⁾ = A`: for `k = 1, 2, …`,
`Q⁽ᵏ⁾ R⁽ᵏ⁾ = T⁽ᵏ⁻¹⁾ − μ I` and `T⁽ᵏ⁾ = R⁽ᵏ⁾ Q⁽ᵏ⁾ + μ I`. -/
noncomputable def shiftedQrIterate (A : Matrix (Fin N) (Fin N) 𝕜) (μ : 𝕜) :
    ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep μ (shiftedQrIterate A μ k)

/-- The book's shifted step is the backbone's `Matrix.shiftedQrStep`. -/
theorem shiftedQrStep_eq (μ : 𝕜) (T : Matrix (Fin N) (Fin N) 𝕜) :
    shiftedQrStep μ T = Matrix.shiftedQrStep μ T := rfl

/-- **The book's shifted iteration (5.52) is the backbone's `Matrix.shiftedQrIterate`.** -/
theorem shiftedQrIterate_eq (A : Matrix (Fin N) (Fin N) 𝕜) (μ : 𝕜) :
    ∀ k, shiftedQrIterate A μ k = Matrix.shiftedQrIterate A μ k
  | 0 => rfl
  | k + 1 => by
    rw [shiftedQrIterate, shiftedQrIterate_eq A μ k, shiftedQrStep_eq,
      Matrix.shiftedQrIterate_succ]

/-- **The shifted iterates are similar to `A`** (the display after (5.52)). One step is the
orthogonal similarity `R Q + μ I = Qᵀ (Q R + μ I) Q = Qᵀ T Q` with `Q = qrQ (T − μ I)`, and hence
every iterate is `T⁽ᵏ⁾ = (Q⁽¹⁾ ⋯ Q⁽ᵏ⁾)ᵀ A (Q⁽¹⁾ ⋯ Q⁽ᵏ⁾)` with `Q⁽¹⁾ ⋯ Q⁽ᵏ⁾ = qrAccum (A − μ I) k`
orthogonal. Backbone `Matrix.shiftedQrStep_eq_conj` and
`Matrix.shiftedQrIterate_eq_conj_qrAccum`. -/
theorem shiftedQrIterate_eq_conj (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) :
    (∀ T : Matrix (Fin N) (Fin N) ℝ, qrQ (T - μ • 1) ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      shiftedQrStep μ T = (qrQ (T - μ • 1))ᵀ * T * qrQ (T - μ • 1)) ∧
      ∀ k, qrAccum (A - μ • 1) k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
        shiftedQrIterate A μ k = (qrAccum (A - μ • 1) k)ᵀ * A * qrAccum (A - μ • 1) k := by
  refine ⟨fun T => ⟨qrQ_mem_unitaryGroup _, ?_⟩, fun k => ⟨qrAccum_mem_unitaryGroup _ k, ?_⟩⟩
  · rw [shiftedQrStep_eq, Matrix.shiftedQrStep_eq_conj, conjTranspose_eq_transpose_of_trivial]
  · rw [shiftedQrIterate_eq, Matrix.shiftedQrIterate_eq_conj_qrAccum,
      conjTranspose_eq_transpose_of_trivial]

/-- **A fixed shift is the basic iteration on the shifted matrix**: for every `k`,
`shiftedQrIterate A μ k = qrIterate (A − μ I) k + μ I`. Backbone
`Matrix.shiftedQrIterate_eq_qrIterate_sub_add`. -/
theorem shiftedQrIterate_eq_qrIterate (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (k : ℕ) :
    shiftedQrIterate A μ k = qrIterate (A - μ • 1) k + μ • 1 := by
  rw [shiftedQrIterate_eq, qrIterate_eq, Matrix.shiftedQrIterate_eq_qrIterate_sub_add]

/-- **The convergence claim of §5.7.1.** Let `A ∈ ℝ^{n×n}` be diagonalizable, `X⁻¹ A X =
diag(λ_1, …, λ_n)`, let the shift `μ` be fixed with the eigenvalues ordered so that
`|λ_1 − μ| > |λ_2 − μ| > … > |λ_n − μ| > 0`, and assume the general-position hypothesis of Property
5.9 (nonzero leading principal minors of `X⁻¹`). Then for `1 < j ≤ n` the subdiagonal entry
`t_{j,j−1}^{(k)}` of the shifted iteration (5.52) tends to zero, at a rate proportional to
`|(λ_j − μ)/(λ_{j−1} − μ)|^k`: `|t_{j,j−1}^{(k)}| ≤ C |(λ_j − μ)/(λ_{j−1} − μ)|^k`. This is
Property 5.9 and (5.37) for the matrix `A − μ I`, whose eigenvalues are the `λ_i − μ` for the same
eigenvectors, through `shiftedQrIterate_eq_qrIterate`. Reading: the book orders with `≥`; the
strict ordering is what makes the ratio less than `1`. -/
theorem shiftedQrIterate_rate {A X : Matrix (Fin N) (Fin N) ℝ} (hX : IsUnit X) {lam : Fin N → ℝ}
    (hD : X⁻¹ * A * X = diagonal lam) (μ : ℝ) (hne : ∀ i, lam i - μ ≠ 0)
    (hsep : ∀ i j, i < j → |lam j - μ| < |lam i - μ|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det)
    {i j : Fin N} (hij : (i : ℕ) = j + 1) :
    Tendsto (fun k => shiftedQrIterate A μ k i j) atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ k, |shiftedQrIterate A μ k i j| ≤ C * (|lam i - μ| / |lam j - μ|) ^ k := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hD' : X⁻¹ * (A - μ • 1) * X = diagonal fun i => lam i - μ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      nonsing_inv_mul X hdet, smul_one_eq_diagonal, diagonal_sub]
  have hji : j ≠ i := fun h => by rw [h] at hij; omega
  have hentry : ∀ k, shiftedQrIterate A μ k i j = qrIterate (A - μ • 1) k i j := fun k => by
    rw [shiftedQrIterate_eq_qrIterate, Matrix.add_apply, Matrix.smul_apply, one_apply_ne hji.symm,
      smul_zero, add_zero]
  simp only [hentry]
  exact ⟨(property_5_9 hX hD' hne hsep hminor).1 i j (Fin.lt_def.2 (by omega)),
    equation_5_37 hX hD' hne hsep hminor hij⟩

/-! ### (5.53): the Rayleigh-quotient shift -/

/-- **(5.53), the QR iteration with single shift `μ = t_nn^{(k)}`**: at every step the shift is the
current last diagonal entry, `T⁽ᵏ⁺¹⁾ = R Q + t_nn^{(k)} I` where `Q R = T⁽ᵏ⁾ − t_nn^{(k)} I`. -/
noncomputable def equation_5_53 (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep (equation_5_53 A k (Fin.last N) (Fin.last N)) (equation_5_53 A k)

/-- **The book's iteration (5.53) is the backbone's `Matrix.rayleighShiftQrIterate`.** -/
theorem equation_5_53_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ∀ k, equation_5_53 A k = Matrix.rayleighShiftQrIterate A k
  | 0 => rfl
  | k + 1 => by
    rw [equation_5_53, equation_5_53_eq A k, shiftedQrStep_eq,
      Matrix.rayleighShiftQrIterate_succ]

/-- Every iterate of the Rayleigh-shift iteration (5.53) is orthogonally similar to `A`, each step
being the similarity of `shiftedQrIterate_eq_conj`. Backbone
`Matrix.exists_unitary_conj_rayleighShiftQrIterate`. -/
theorem equation_5_53_eq_conj (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : ℕ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin (N + 1)) ℝ, equation_5_53 A k = Qᵀ * A * Q := by
  obtain ⟨Q, hQ, h⟩ := Matrix.exists_unitary_conj_rayleighShiftQrIterate A k
  exact ⟨Q, hQ, by rw [equation_5_53_eq, h, conjTranspose_eq_transpose_of_trivial]⟩

/-! ### (5.55): the QR method with double shift -/

/-- **(5.55), the double-shift step.** When a `2 × 2` diagonal block cannot be reduced to
triangular form its two eigenvalues are a complex conjugate pair `λ`, `λ̄`; the double shift takes
two consecutive shifted steps (5.52) with the shifts `λ` and `λ̄`: `Q⁽ᵏ⁾ R⁽ᵏ⁾ = T⁽ᵏ⁻¹⁾ − λ I`,
`T⁽ᵏ⁾ = R⁽ᵏ⁾ Q⁽ᵏ⁾ + λ I`, then `Q⁽ᵏ⁺¹⁾ R⁽ᵏ⁺¹⁾ = T⁽ᵏ⁾ − λ̄ I`, `T⁽ᵏ⁺¹⁾ = R⁽ᵏ⁺¹⁾ Q⁽ᵏ⁺¹⁾ + λ̄ I`, in
complex arithmetic. The real-arithmetic Francis implementation is not defined; the book only
sketches it. -/
noncomputable def equation_5_55 (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  shiftedQrStep (starRingEnd ℂ lam) (shiftedQrStep lam T)

/-- The book's double-shift step is the backbone's `Matrix.doubleShiftQrStep`. -/
theorem equation_5_55_eq (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    equation_5_55 T lam = Matrix.doubleShiftQrStep T lam := rfl

/-- The double-shift step is a unitary similarity, the product of the two similarities of its
steps. Backbone `Matrix.exists_unitary_conj_doubleShiftQrStep`. -/
theorem equation_5_55_eq_conj (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin N) ℂ, equation_5_55 T lam = Qᴴ * T * Q :=
  Matrix.exists_unitary_conj_doubleShiftQrStep T lam

end QuarteroniSaccoSaleri.Chapter05
