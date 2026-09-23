import Numlib.Eigen.RayleighQuotientIteration
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section06

/-!
# Quarteroni–Sacco–Saleri §5.7: the QR iteration with shifting techniques

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.7, over the backbone `Numlib/Eigen/QRAlgorithm` (the shifted QR
step and iterations, their similarity identities, and the reduction of a fixed shift to the basic
iteration on `A − μI`), over §5.5's Property 5.9 and (5.37) for the convergence claim of
§5.7.1, and over `Numlib/Eigen/RayleighQuotientIteration` (the local quadratic convergence of
Rayleigh quotient iteration and the last row of a shifted QR step) for the quadratic convergence
of the single-shift iteration.

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
* `equation_5_53_quadratic`, `equation_5_53_quadratic_iterate` — the quadratic convergence of
  `t_{n,n−1}^{(k)}` to zero (and of `t_{nn}^{(k)}` to the eigenvalue) for the single-shift
  iteration at a simple real eigenvalue: the one-step bound, and the tail of the iteration from
  the first iterate in the basin.
* `equation_5_55`, `equation_5_55_eq`, `equation_5_55_eq_conj` — the double-shift step.

## Readings and errata

The convergence claim of §5.7.1 is stated by the book with the non-strict ordering
`|λ_1 − μ| ≥ … ≥ |λ_n − μ|` and "a rate proportional to `|(λ_j − μ)/(λ_{j−1} − μ)|^k`"; with a tie
the ratio is `1` and nothing tends to zero, so `shiftedQrIterate_rate` takes the strict ordering
and `|λ_n − μ| > 0`, together with the general-position hypothesis of Property 5.9 for the
eigenvector matrix, which the shift does not change. The quadratic-convergence claim for the
Rayleigh shift (5.53) is stated by the book without proof, citing [Dem97] pp. 161–163, and in the
form "`|t_{n,n−1}^{(k+1)}| / ‖T⁽⁰⁾‖₂ = O(η_k²)`" at a single `k`; `equation_5_53_quadratic` is
the rigorous local statement that reading stands for — constants `c, ε₀` uniform in `k`, at a
simple real eigenvalue `λ`, with the two hypotheses the book leaves implicit: `t_{nn}^{(k)}` is
close to `λ` (which eigenvalue the last row is converging to) and no shift is exactly an
eigenvalue (the QR factorizations are unique and Hessenberg form is preserved); the book's
"unreduced" is not needed. The corresponding claim for the Francis double shift of §5.7.2 is not
formalized; the record is below. The stopping test (5.54) is part of a program. "Remark 5.13",
cited in §5.7.2, does not exist (Exercise 14 is meant). Examples 5.10–5.13 are numerical and
Programs 36–37 are not nodes.

## Not formalized here

* **§5.7.2, the quadratic convergence of the QR iteration with the Francis double shift.** The
  claim is that, when the two shifts of a double step are the eigenvalues of the trailing `2 × 2`
  block of `T⁽ᵏ⁾`, the iterates converge to the real Schur form *quadratically*: the subdiagonal
  entry `t_{n−1,n−2}^{(k+1)}` below the trailing block is of the order of the square of
  `t_{n−1,n−2}^{(k)}`. The book itself says why this cannot be stated as printed. It cites
  [Fra61], [GL89] §7.5 and [Dem97] §4.4.5 without proof; it notes that special matrices defeat the
  strategy — the cyclic permutation matrix of Exercise 14, proved as `property_5_9_counterexample`
  in §5.5, is left fixed by the iteration, so nothing converges at all; and it calls a shift
  strategy that provably converges for *every* matrix an **open problem**. Any faithful statement
  therefore carries a genericity hypothesis that none of the cited sources supplies (Golub–Van
  Loan and Demmel give the heuristic and the exceptional-shift remedy, not a theorem), so there is
  no rigorous form of the printed claim to prove in its place.

  What *is* proved, and what the block form would need. The single-shift case is
  `equation_5_53_quadratic` with `equation_5_53_quadratic_iterate` above: local quadratic
  convergence of `t_{n,n−1}^{(k)}` to `0` at a simple real eigenvalue, over the backbone
  `Numlib/Eigen/RayleighQuotientIteration` (`Krylov.norm_sub_inner_smul_le_sq_mul_norm` and the
  last-row identification `Matrix.abs_shiftedQrStep_last_le`), under the two hypotheses the book
  leaves implicit — `t_{nn}^{(k)}` close to the eigenvalue, and no shift exactly an eigenvalue.
  The double step itself is `equation_5_55`, `equation_5_55_eq`, `equation_5_55_eq_conj`: one real
  double step is two complex single steps. What is missing is that argument in *block* form, that
  is, a **subspace** Rayleigh quotient iteration. The last two columns of `Q` for the double step
  are `(T − λ)⁻ᵀ (T − λ̄)⁻ᵀ [e_{n−1}, e_n]` orthonormalized, so `t_{n−1,n−2}^{(k+1)}` has to be
  controlled by the sine of the angle between `span {e_{n−1}, e_n}` and the two-dimensional left
  invariant subspace of the complex pair, with the gap `Submodule.gap` of
  `Numlib/Analysis/InnerProductSpace/Projection/Angle` in place of the complementary component and
  a resolvent bound on the complement of the invariant pair. Estimate: about 400 lines for the
  block form of `Numlib/Eigen/RayleighQuotientIteration`, after which the genericity hypothesis
  would still have to be invented.
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

/-! ### The quadratic convergence of the single-shift iteration -/

open scoped Matrix.Norms.L2Operator in
/-- **The quadratic convergence of the QR iteration with single shift (5.53)**, in the rigorous
form the book's "if `|t_{n,n-1}^{(k)}| / ‖T⁽⁰⁾‖₂ = η_k < 1` then `|t_{n,n-1}^{(k+1)}| / ‖T⁽⁰⁾‖₂ =
O(η_k²)`" stands for, following the source it cites ([Dem97] §4.4.5, pp. 161–163). Let
`T⁽⁰⁾ = A ∈ ℝ^{n×n}` (`n = N + 2`) be upper Hessenberg, let `λ` be a simple real eigenvalue of `A`
(a simple root of the characteristic polynomial), and let `T⁽ᵏ⁾ = equation_5_53 A k` with the
shifts never exactly an eigenvalue (`T⁽ᵏ⁾ − t_{nn}^{(k)} I` nonsingular for every `k`, so that
the QR factorization of every step is the unique one with positive diagonal and Hessenberg form
is preserved). Then there are `c, ε₀ > 0` with `c ε₀ ≤ 1` such that for every `k`: if
`|t_{n,n-1}^{(k)}| ≤ ε₀ ‖T⁽⁰⁾‖₂` and `|t_{nn}^{(k)} − λ| ≤ ε₀ ‖T⁽⁰⁾‖₂`, then

`|t_{n,n-1}^{(k+1)}| ≤ c |t_{n,n-1}^{(k)}|² / ‖T⁽⁰⁾‖₂` and
`|t_{nn}^{(k+1)} − λ| ≤ c |t_{n,n-1}^{(k)}|² / ‖T⁽⁰⁾‖₂`;

since `c ε₀ ≤ 1` the two hypotheses then hold again at `k + 1`, so once an iterate enters the
basin the subdiagonal entry `t_{n,n-1}^{(k)}` tends to zero quadratically and `t_{nn}^{(k)}` to `λ`.

Readings. (i) The book states the bound with `|t_{n,n-1}^{(k)}|` alone; the second hypothesis
`|t_{nn}^{(k)} − λ|` small says which eigenvalue the last row is converging to, and is needed: a
small `t_{n,n-1}^{(k)}` alone puts `t_{nn}^{(k)}` near *some* eigenvalue, which could be a defective
one where the convergence is only linear. It is the closeness of `e_n` to the left eigenvector
of `λ` that [Dem97]'s local statement about Rayleigh quotient iteration assumes. (ii) The book
cites [Dem97] for an *unreduced* Hessenberg `T⁽⁰⁾`; that hypothesis is not needed here — it is
what makes the QR factorization of the singular matrix `T − λ I` unique in [Dem97]'s discussion,
and the nonsingularity hypothesis `hreg` (the shift is never exactly an eigenvalue, the generic
case in which the book's algorithm and `Matrix.qrQ` agree) replaces it. (iii) The constants
depend on `λ`'s conditioning: `c` is `4 K C² A'² ‖A‖₂` with `K` the bound of the resolvent of
`Aᵀ − λ` on the complement of the right eigenvector, `C = ‖A‖₂ + |λ|` and
`A' = 2 K (1 + ‖x‖ ‖y‖)` for the left and right eigenvectors normalized by `yᵀ x = 1`.

Backbone: `Matrix.abs_shiftedQrStep_last_le_of_conj` (one step, on the Hessenberg orthogonal
conjugate `T⁽ᵏ⁾ = Qᵀ A Q` of `equation_5_53_eq_conj`), whose proof is the identification of the
last row of a shifted QR step with a step of Rayleigh quotient iteration on `Tᵀ` from `e_n`
(`Matrix.toEuclideanLin_transpose_euclideanCol_qrQ_last`) and the local quadratic convergence of
that iteration at a simple eigenvalue (`Krylov.norm_sub_inner_smul_le_sq_mul_norm`);
`Matrix.exists_eigenvector_data_of_rootMultiplicity_eq_one` supplies the eigenvectors and `K`
from the simplicity of `λ`, and `Matrix.isUpperHessenberg_rayleighShiftQrIterate` the Hessenberg
form of every iterate. -/
theorem equation_5_53_quadratic {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hA : A.IsUpperHessenberg) {lam : ℝ} (hlam : A.charpoly.rootMultiplicity lam = 1)
    (hreg : ∀ k, IsUnit (equation_5_53 A k -
      equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) •
        (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ))) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ c * ε₀ ≤ 1 ∧ ∀ k,
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤ ε₀ * ‖A‖ →
        |equation_5_53 A (k + 1) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
            c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 / ‖A‖ ∧
          |equation_5_53 A (k + 1) (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤
            c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 / ‖A‖ := by
  obtain ⟨x, y, K, hx, hy, hyx, hK, hKw⟩ :=
    Matrix.exists_eigenvector_data_of_rootMultiplicity_eq_one hlam
  -- the starting matrix is not zero, its shifted form being nonsingular
  have hA0 : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · exfalso
      have hA' : A = 0 := norm_eq_zero.mp h.symm
      have hu := hreg 0
      rw [show equation_5_53 A 0 = A from rfl, hA', Matrix.zero_apply, zero_smul, sub_zero] at hu
      exact not_isUnit_zero hu
  -- the constants
  set C : ℝ := ‖A‖ + |lam| with hCdef
  have hC0 : 0 < C := by positivity
  have hCz : ∀ z : EuclideanSpace ℝ (Fin (N + 2)),
      ‖toEuclideanLin Aᵀ z - lam • z‖ ≤ C * ‖z‖ := fun z => by
    calc ‖toEuclideanLin Aᵀ z - lam • z‖ ≤ ‖toEuclideanLin Aᵀ z‖ + ‖lam • z‖ := norm_sub_le _ _
      _ ≤ ‖Aᵀ‖ * ‖z‖ + |lam| * ‖z‖ := by
        gcongr
        · exact norm_toEuclideanLin_apply_le _ _
        · rw [norm_smul, Real.norm_eq_abs]
      _ = C * ‖z‖ := by
        rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
        ring
  set A' : ℝ := 2 * K * (1 + ‖x‖ * ‖y‖) with hA'def
  have hA'0 : 0 < A' := by positivity
  set c₁ : ℝ := 4 * K * C ^ 2 * A' ^ 2 with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  set D : ℝ := 4 * A' + 2 * K * C * A' + 2 * K + c₁ with hDdef
  have hD : 0 < D := by positivity
  have hKCA : 0 ≤ 2 * K * C * A' := by positivity
  -- every iterate is upper Hessenberg
  have hess : ∀ k, (equation_5_53 A k).IsUpperHessenberg := fun k => by
    rw [equation_5_53_eq]
    refine Matrix.isUpperHessenberg_rayleighShiftQrIterate hA (fun j => ?_) k
    rw [← equation_5_53_eq]
    exact hreg j
  refine ⟨c₁ * ‖A‖, 1 / (D * ‖A‖), by positivity, by positivity, ?_, fun k ht hd => ?_⟩
  · rw [mul_one_div, mul_div_mul_right _ _ hA0.ne', div_le_one hD]
    linarith
  · have hε : 1 / (D * ‖A‖) * ‖A‖ = 1 / D := by field_simp
    rw [hε] at ht hd
    obtain ⟨Q, hQ, hTQ⟩ := equation_5_53_eq_conj A k
    have ht0 : 0 ≤ |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| :=
      abs_nonneg _
    have hsub1 : 4 * A' * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
        1 := by
      calc 4 * A' * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))|
          ≤ 4 * A' * (1 / D) := by gcongr
        _ ≤ 1 := by
          rw [mul_one_div, div_le_one hD]
          linarith
    have hsub2 : 2 * K * C * A' *
        |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ 1 := by
      calc 2 * K * C * A' * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))|
          ≤ 2 * K * C * A' * (1 / D) := by gcongr
        _ ≤ 1 := by
          rw [mul_one_div, div_le_one hD]
          linarith
    have hdiag : 2 * K * |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤ 1 := by
      calc 2 * K * |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam|
          ≤ 2 * K * (1 / D) := by gcongr
        _ ≤ 1 := by
          rw [mul_one_div, div_le_one hD]
          linarith
    have h := Matrix.abs_shiftedQrStep_last_le_of_conj hQ hTQ (hess k) hx hy hyx hK.le hKw hCz
      (hreg k) hsub1 hsub2 hdiag
    have hnext : equation_5_53 A (k + 1) =
        Matrix.shiftedQrStep (equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)))
          (equation_5_53 A k) := rfl
    have hc : c₁ * ‖A‖ * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 /
        ‖A‖ = c₁ * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
      field_simp
    have hne : Fin.castSucc (Fin.last N) ≠ Fin.last (N + 1) := fun h => by
      simpa using congrArg Fin.val h
    rw [hnext, hc]
    exact ⟨h.1 _ hne, h.2⟩


open scoped Matrix.Norms.L2Operator in
/-- **(5.53), the quadratic convergence as a statement about the whole tail of the iteration.**
Under the hypotheses of `equation_5_53_quadratic`, there are `c, ε₀ > 0` such that once an
iterate `T⁽ᵏ⁾` is in the basin — `|t_{n,n-1}^{(k)}| ≤ ε₀ ‖T⁽⁰⁾‖₂` and
`|t_{nn}^{(k)} − λ| ≤ ε₀ ‖T⁽⁰⁾‖₂` — the normalized subdiagonal entries
`η_{k+j} = c |t_{n,n-1}^{(k+j)}| / ‖T⁽⁰⁾‖₂` satisfy
`η_{k+j} ≤ η_k ^ (2 ^ j)` for every `j`, with `η_k ≤ 1/2`; consequently `t_{n,n-1}^{(k+j)} → 0` and
`t_{nn}^{(k+j)} → λ` as `j → ∞`. This is the sense in which the book's "the convergence to zero of
the sequence `{t_{n,n-1}^{(k)}}` is quadratic" holds: by induction on `j` from the one-step bound of
`equation_5_53_quadratic`, whose hypotheses propagate because `c ε₀ ≤ 1`. -/
theorem equation_5_53_quadratic_iterate {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hA : A.IsUpperHessenberg) {lam : ℝ} (hlam : A.charpoly.rootMultiplicity lam = 1)
    (hreg : ∀ k, IsUnit (equation_5_53 A k -
      equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) •
        (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ))) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ∀ k,
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤ ε₀ * ‖A‖ →
        c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖ ≤ 1 / 2 ∧
        (∀ j, c * |equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖ ≤
          (c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖) ^
            (2 ^ j)) ∧
        Tendsto (fun j => equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N)))
          atTop (𝓝 0) ∧
        Tendsto (fun j => equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.last (N + 1)))
          atTop (𝓝 lam) := by
  obtain ⟨c, ε₀, hc, hε₀, hcε, hstep⟩ := equation_5_53_quadratic hA hlam hreg
  have hA0 : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · exfalso
      have hA' : A = 0 := norm_eq_zero.mp h.symm
      have hu := hreg 0
      rw [show equation_5_53 A 0 = A from rfl, hA', Matrix.zero_apply, zero_smul, sub_zero] at hu
      exact not_isUnit_zero hu
  refine ⟨c, ε₀ / 2, hc, by positivity, fun k ht hd => ?_⟩
  set n : Fin (N + 2) := Fin.last (N + 1) with hn
  set m : Fin (N + 2) := Fin.castSucc (Fin.last N) with hm
  set η : ℕ → ℝ := fun i => c * |equation_5_53 A i n m| / ‖A‖ with hη
  have hη0 : ∀ i, 0 ≤ η i := fun i => by positivity
  -- the basin, and the one-step bound in normalized form
  have hbasin : ∀ i, |equation_5_53 A i n m| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A i n n - lam| ≤ ε₀ * ‖A‖ →
      η (i + 1) ≤ η i ^ 2 ∧ |equation_5_53 A (i + 1) n m| ≤ ε₀ * ‖A‖ ∧
        |equation_5_53 A (i + 1) n n - lam| ≤ ε₀ * ‖A‖ := by
    intro i hti hdi
    obtain ⟨h1, h2⟩ := hstep i hti hdi
    have hsq : c * |equation_5_53 A i n m| ^ 2 / ‖A‖ ≤ ε₀ * ‖A‖ := by
      calc c * |equation_5_53 A i n m| ^ 2 / ‖A‖
          ≤ c * (ε₀ * ‖A‖) ^ 2 / ‖A‖ := by gcongr
        _ = (c * ε₀) * (ε₀ * ‖A‖) := by field_simp
        _ ≤ 1 * (ε₀ * ‖A‖) := by gcongr
        _ = ε₀ * ‖A‖ := one_mul _
    refine ⟨?_, h1.trans hsq, h2.trans hsq⟩
    calc η (i + 1) = c * |equation_5_53 A (i + 1) n m| / ‖A‖ := rfl
      _ ≤ c * (c * |equation_5_53 A i n m| ^ 2 / ‖A‖) / ‖A‖ := by gcongr
      _ = η i ^ 2 := by simp only [hη]; field_simp
  -- the tail stays in the basin and the normalized entries square
  have hht : ∀ j, |equation_5_53 A (k + j) n m| ≤ ε₀ * ‖A‖ ∧
      |equation_5_53 A (k + j) n n - lam| ≤ ε₀ * ‖A‖ ∧ η (k + j) ≤ η k ^ (2 ^ j) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_, by simp⟩
      · exact ht.trans (by nlinarith [hA0.le])
      · exact hd.trans (by nlinarith [hA0.le])
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨h4, h5, h6⟩ := hbasin (k + j) h1 h2
      refine ⟨h5, h6, ?_⟩
      calc η (k + (j + 1)) = η (k + j + 1) := rfl
        _ ≤ η (k + j) ^ 2 := h4
        _ ≤ (η k ^ (2 ^ j)) ^ 2 := by gcongr
        _ = η k ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]
  have hηk : η k ≤ 1 / 2 := by
    calc η k = c * |equation_5_53 A k n m| / ‖A‖ := rfl
      _ ≤ c * (ε₀ / 2 * ‖A‖) / ‖A‖ := by gcongr
      _ = (c * ε₀) / 2 := by field_simp
      _ ≤ 1 / 2 := by linarith
  refine ⟨hηk, fun j => (hht j).2.2, ?_, ?_⟩
  -- the subdiagonal entry tends to zero
  · have hlim : Tendsto (fun j : ℕ => η k ^ (2 ^ j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (hη0 k) (by linarith)).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim' : Tendsto (fun j : ℕ => ‖A‖ / c * η k ^ (2 ^ j)) atTop (𝓝 0) := by
      simpa using hlim.const_mul (‖A‖ / c)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim'
    calc |equation_5_53 A (k + j) n m| = ‖A‖ / c * η (k + j) := by
          simp only [hη]
          field_simp
      _ ≤ ‖A‖ / c * η k ^ (2 ^ j) :=
          mul_le_mul_of_nonneg_left (hht j).2.2 (by positivity)
  -- the diagonal entry tends to the eigenvalue
  · have hlim : Tendsto (fun j : ℕ => η k ^ (2 ^ j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (hη0 k) (by linarith)).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim' : Tendsto (fun j : ℕ => ‖A‖ / c * (η k ^ (2 ^ j)) ^ 2) atTop (𝓝 0) := by
      have := (hlim.pow 2).const_mul (‖A‖ / c)
      simpa using this
    rw [← tendsto_sub_nhds_zero_iff, ← tendsto_add_atTop_iff_nat 1,
      tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim'
    obtain ⟨h1, h2, h3⟩ := hht j
    have h := (hstep (k + j) h1 h2).2
    calc |equation_5_53 A (k + (j + 1)) n n - lam|
        = |equation_5_53 A (k + j + 1) n n - lam| := rfl
      _ ≤ c * |equation_5_53 A (k + j) n m| ^ 2 / ‖A‖ := h
      _ = ‖A‖ / c * η (k + j) ^ 2 := by
          simp only [hη]
          field_simp
      _ ≤ ‖A‖ / c * (η k ^ (2 ^ j)) ^ 2 := by
          have := (hht j).2.2
          gcongr

end QuarteroniSaccoSaleri.Chapter05
