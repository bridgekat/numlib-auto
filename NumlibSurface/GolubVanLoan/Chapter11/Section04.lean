import Numlib.Krylov.Bidiagonalization
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.TransposeFree
import NumlibSurface.GolubVanLoan.Chapter01.Section04

/-!
# Golub–Van Loan §11.4: other Krylov methods

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §11.4:
MINRES and SYMMLQ for symmetric indefinite systems ((11.4.1)–(11.4.5)), LSQR and LSMR for least
squares ((11.4.6)–(11.4.7)), GMRES ((11.4.8)–(11.4.11), Algorithm 11.4.2), the polynomial point of
view (§11.4.4), and the unsymmetric-Lanczos family BiCG, CGS, BiCGstab and QMR
((11.4.12)–(11.4.14), Figure 11.4.1).

## Design

The book's paradigm "Krylov process + matrix factorization + clever recursions" is, in the
backbone, a *specification* plus a *transport* layer: the minimal-residual iterate
`Krylov.IsMinResidualIterate` (MINRES, GMRES, LSMR) of `Numlib/Krylov/Iterate`; the Arnoldi and
Lanczos relations `A Q_k = Q_{k+1} H̃_k` and the ℕ-indexed Givens layer (`Krylov.rotated`,
`Krylov.givensQ`, `Krylov.gvec`, `Krylov.gamma`) of `Numlib/Krylov/{Arnoldi,Lanczos,Hessenberg}`;
the two-sided Lanczos process, BiCG and QMR of `Numlib/Krylov/BiLanczos`; and the transpose-free
methods CGS and BiCGstab of `Numlib/Krylov/TransposeFree`, whose recurrences are line by line those
of Figure 11.4.1. The theorems of this file are those facts read in the book's notation.

The three columns of Figure 11.4.1 are programs over a rounding hook `rnd : ℝ → M ℝ`
(`bicg`, `cgs`, `bicgstab`; conventions 1–14 of `NumlibSurface/GolubVanLoan`), built from
chapter 1's dot product (Algorithm 1.1.1), saxpy (Algorithm 1.1.2), gaxpy (Algorithm 1.1.3) and
rounded vector sum (`GolubVanLoan.Chapter01.vecAdd`). The figure gives only the initializations
and the update formulae, with no stopping test, so each program runs `k` passes of the update
(`k` its last argument). Their exact semantics (`M := Id`, `rnd := pure`) is the backbone
iteration: `bicg_spec`, `cgs_residual_eq`, `bicgstab_residual_eq`. The book analyses no rounding
error in this section.

## Conventions

Real matrices `A : Matrix (Fin n) (Fin n) ℝ` act on `EuclideanSpace ℝ (Fin n)` as
`T = Matrix.toEuclideanLin A` (and `Aᵀ` as `Matrix.toEuclideanLin Aᵀ`, which is the adjoint of
`T`); vectors of `ℝⁿ` are carried there by `WithLp.toLp 2`. Indices are `0`-based: the book's
Lanczos or Arnoldi vector `q_j` (`j ≥ 1`) is `Arnoldi.vec T r₀ (j - 1)`, the book's `H̃_k` is
`Arnoldi.hessenberg T r₀ k` (for symmetric `A`, `Lanczos.tridiagExt T r₀ k`), and the book's
Givens quantities after `k` rotations are `R_k = hessenbergSqOf (rotated h k) k`,
`p_k = (gvec h β₀ i)_{i<k}` and `ρ_k = gamma h β₀ k` for `h = Arnoldi.coeff T r₀`, `β₀ = ‖r₀‖₂`.
The book's `𝒦(A, b, k)` in the first line of §11.4.3 means `𝒦(A, r₀, k)`.

## Main results

* `energyFunctional_unbounded_of_indefinite` — `φ` has no lower bound for indefinite `A`.
* `equation_11_4_2`, `minres_reduction`, `equation_11_4_1`, `minres_givens_update` — MINRES.
* `equation_11_4_5`, `symmlq_minNorm_solution` — SYMMLQ: the residual is orthogonal to
  `q₁, …, q_{k−1}`, and the LQ (transposed Givens QR) solve gives the minimum-norm `y_k`.
* `IsLSMRIterate`, `lsmr_norm_residual_antitone` — LSMR and its monotone residuals.
* `equation_11_4_8`, `gmres_reduction`, `equation_11_4_9`, `equation_11_4_10`,
  `gmres_givens_prefix` — GMRES.
* `krylov_eq_aeval`, `minResidual_eq_iInf_poly` — §11.4.4.
* `equation_11_4_12`, `equation_11_4_13`, `bicg_residual_orthogonal` — the unsymmetric Lanczos
  relations and BiCG's Petrov–Galerkin condition.
* `bicg`, `bicg_spec`, `bicg_eq_cg`, `equation_11_4_14`, `bicg_inner_eq_poly` — BiCG.
* `cgs`, `cgs_residual_eq`, `bicgstab`, `bicgstab_residual_eq` — CGS and BiCGstab.
* `qmr_residual_eq`, `qmr_eq_gmres_of_orthonormal` — QMR.

## Not formalized here

The flop counts ("`O(1)` flops", "`O(n)` work", P11.4.1), the prose descriptions of the short
recurrences of MINRES, SYMMLQ and LSQR that avoid storing all Lanczos vectors, the look-ahead
remark, "CGS typically outperforms BiCG" (quoted, not a statement), the when-to-use-what advice,
and the Notes and References. Algorithm 11.4.2 (`m`-step GMRES) is not yet here: its program calls
chapter 3's back substitution (Algorithm 3.1.2) and chapter 5's `givens` (Algorithm 5.1.3), whose
surface modules do not exist yet; its mathematics is `equation_11_4_8`–`gmres_givens_prefix`.
There is no Algorithm 11.4.1 in the source: §11.4.1 describes MINRES
and SYMMLQ in prose and the first numbered algorithm of the section is 11.4.2.

## Errata (recorded in the plan)

(11.4.3): the first row is `α₁ β₁`, not `α₁ β₂`. SYMMLQ's derivation: `r_k = r₀ − A Q_k y_k`, not
`r₀ − A Q_{k−1} y_k`; `φ(αx) = α²λ_min‖x‖²/2 − αxᵀb`. §11.4.2: `β₀e₁`, not `β₁e₁`. §11.4.4: the
middle term is `‖b − A(x₀ + φ(A)r₀)‖`. (11.4.14): `φ_k(0) = 1` is false (`φ₁(0) = 1 + τ₀`).
Figure 11.4.1: CGS and BiCGstab need `r̃₀ᵀr₀ ≠ 0`, not `r̃₀ᵀr̃₀ ≠ 0`.
-/

open Matrix Polynomial Filter Topology Krylov

namespace GolubVanLoan.Chapter11

variable {n : ℕ}

/-! ### Transport between `ℝⁿ` and `EuclideanSpace ℝ (Fin n)` -/

/-- The transpose of a real matrix acts as the adjoint of the matrix on `EuclideanSpace`. -/
private theorem inner_toEuclideanLin_transpose (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_right]

/-- The real inner product of two transported vectors is their dot product. -/
private theorem inner_toLp (u v : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- Complex conjugation on `ℝ` is the identity. -/
private theorem starRingEnd_real : starRingEnd ℝ = RingHom.id ℝ :=
  RingHom.ext fun x => by simp

/-- Conjugating the coefficients of a real polynomial does nothing. -/
private theorem map_starRingEnd_real (p : ℝ[X]) : p.map (starRingEnd ℝ) = p := by
  rw [starRingEnd_real, Polynomial.map_id]

/-- A loop running `k` passes of a step, read in exact arithmetic through a transport map that
takes each pass to one application of `g`, is the `k`-th iterate of `g`. -/
private theorem foldlM_range_transport {σ τ : Type*} (step : σ → Id σ) (g : τ → τ) (π : σ → τ)
    (h : ∀ s, π (Id.run (step s)) = g (π s)) (k : ℕ) (s₀ : σ) :
    π (Id.run ((List.range k).foldlM (fun s _ => step s) s₀)) = g^[k] (π s₀) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldlM_append, Function.iterate_succ_apply', ← ih]
    simp only [List.foldlM_cons, List.foldlM_nil, Id.run_bind, bind_pure]
    exact h _

/-- A matrix with a Euclidean vector: the real transpose moves across the inner product as the
adjoint, for rectangular matrices. -/
private theorem inner_toEuclideanLin_transpose' {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_right]

/-- A real matrix mapped by `algebraMap ℝ ℝ` is itself. -/
private theorem map_algebraMap_real {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ) :
    M.map (algebraMap ℝ ℝ) = M := by
  ext i j
  simp

/-- The first `k` Arnoldi vectors, `k` at most the grade, are orthonormal. -/
private theorem orthonormal_vec_fin (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k ≤ grade T r) :
    Orthonormal ℝ fun i : Fin k => Arnoldi.vec T r i :=
  (Arnoldi.orthonormal T r).comp (Fin.castLE hk) (Fin.castLE_injective hk)

/-- Coordinates in an orthonormal family: `⟪∑ c_i q_i, ∑ d_i q_i⟫ = ∑ c_i d_i`. -/
private theorem inner_sum_smul_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} {q : Fin k → E} (hq : Orthonormal ℝ q) (c d : Fin k → ℝ) :
    inner ℝ (∑ i, c i • q i) (∑ i, d i • q i) = ∑ i, c i * d i := by
  rw [hq.inner_sum c d Finset.univ]
  simp

/-- The norm of a combination of an orthonormal family is the Euclidean norm of its
coordinates. -/
private theorem norm_sum_smul_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} {q : Fin k → E} (hq : Orthonormal ℝ q) (c : Fin k → ℝ) :
    ‖∑ i, c i • q i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ := by
  have h1 : ‖∑ i, c i • q i‖ ^ 2 = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_sum_smul_of_orthonormal hq, inner_toLp]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

/-! ### §11.4.1: MINRES and SYMMLQ -/

/-- **§11.4.1: `φ` has no lower bound for an indefinite matrix.** "If `Ax = λ_min x`, then
`φ(αx) = α²λ_min − αxᵀb` approaches `−∞` as `α` gets big." With `φ(x) = ½xᵀAx − xᵀb`
(`energyFunctional`) and `λ_min < 0`: `φ(αx) = ½α²λ_min‖x‖₂² − αxᵀb → −∞` (the book's display
omits the factor `½‖x‖₂²`, which does not change the conclusion), so `φ` is not bounded
below. -/
theorem energyFunctional_unbounded_of_indefinite (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    {μ : ℝ} {x : Fin n → ℝ} (hx : A *ᵥ x = μ • x) (hx0 : x ≠ 0) (hμ : μ < 0) :
    Tendsto (fun α : ℝ => energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b)
        (α • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))) atTop atBot ∧
      ¬ BddBelow (Set.range (energyFunctional (toEuclideanLin A)
        (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin n)))) := by
  set u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hu0 : u ≠ 0 := fun h => hx0 (by simpa [u] using congrArg WithLp.ofLp h)
  have hTu : toEuclideanLin A u = μ • u := by
    rw [toEuclideanLin_toLp, hx, WithLp.toLp_smul]
  set c : ℝ := μ * ‖u‖ ^ 2 / 2
  set d : ℝ := inner ℝ (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin n)) u
  have hc : c < 0 := by
    have : 0 < ‖u‖ ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hμ this) two_pos
  have hf : ∀ α : ℝ, energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b) (α • u) =
      α * (c * α - d) := by
    intro α
    simp only [energyFunctional, map_smul, hTu, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, RCLike.re_to_real, conj_trivial, c, d]
    ring
  have hlin : Tendsto (fun α : ℝ => c * α - d) atTop atBot := by
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_right atTop (-d) (tendsto_id.const_mul_atTop_of_neg hc)
  have htend : Tendsto (fun α : ℝ => energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b)
      (α • u)) atTop atBot := by
    simp only [hf]
    exact tendsto_id.atTop_mul_atBot₀ hlin
  refine ⟨htend, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨α, hα⟩ := (tendsto_atBot.1 htend (B - 1)).exists
  have := hB ⟨α • u, rfl⟩
  linarith

/-- **(11.4.2)–(11.4.3).** After `k` Lanczos steps from `r₀`, `A Q_k = Q_{k+1} H_k` with
`H_k ∈ ℝ^{(k+1)×k}` the tridiagonal matrix (11.4.3) — the Lanczos `T_k` bordered by the row
`β_k e_kᵀ` (`Lanczos.tridiagExt`), stated column-combination-wise: `A (Q_k y) = Q_{k+1} (H_k y)`
for every `y ∈ ℝ^k`. The printed first row `α₁ β₂` of (11.4.3) should read `α₁ β₁`. -/
theorem equation_11_4_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (y : Fin k → ℝ) :
    toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Lanczos.tridiagExt (toEuclideanLin A) r₀ k *ᵥ y) i •
        Arnoldi.vec (toEuclideanLin A) r₀ i := by
  rw [Arnoldi.apply_sum, Lanczos.hessenberg_eq_map_tridiagExt r₀ hA.isSymmetric_toEuclideanLin,
    map_algebraMap_real]

/-- **§11.4.1, the MINRES reduction.** For `x = x₀ + Q_k y`, `ran Q_k = 𝒦(A, r₀, k)`:
"`‖A(x₀ + Q_k y) − b‖₂ = ‖Q_{k+1}H_k y − (b − Ax₀)‖₂ = ‖H_k y − β₀e₁‖₂`", for `k` at most the
grade (the Lanczos vectors `q₁, …, q_{k+1}` orthonormal). -/
theorem minres_reduction {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      ‖(WithLp.toLp 2 (Lanczos.tridiagExt (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  rw [norm_sub_rev, norm_residual_eq_norm_firstVec_sub_mulVec hk y,
    Lanczos.hessenberg_eq_map_tridiagExt _ hA.isSymmetric_toEuclideanLin, map_algebraMap_real,
    ← norm_neg, ← WithLp.toLp_neg, neg_sub]
  rfl

/-- The Givens solve of the least-squares problem `min ‖β₀e₁ − H̃_k y‖₂`: if the first `k`
rotations have been applied and `R_k y = p_k`, then `x₀ + Q_k y` is the minimal-residual iterate and
its residual norm is `|ρ_k|`. Shared by MINRES (11.4.1) and GMRES (11.4.10). -/
private theorem isMinResidualIterate_of_rotated_mulVec (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
          (b - toEuclideanLin A x₀) j)‖ =
        |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k| := by
  set T := toEuclideanLin A
  set h := Arnoldi.coeff T (b - T x₀)
  have hh : ∀ i j, j + 1 < i → h i j = 0 := fun i j hij => Arnoldi.coeff_eq_zero_of_lt _ _ hij
  have hρ : ∀ l < k, givensRho h l ≠ 0 := fun l hl => givensRho_arnoldi_ne_zero (by omega)
  have hsq := norm_sq_firstVec_sub_mulVec_eq h hh hρ (‖b - T x₀‖ : ℝ)
  have hzero : ‖(WithLp.toLp 2 ((fun i : Fin k => gvec h (‖b - T x₀‖ : ℝ) (i : ℕ)) -
      (hessenbergSqOf (rotated h k) k).mulVec y) : EuclideanSpace ℝ (Fin k))‖ = 0 := by
    rw [hy, sub_self]
    simp
  have hy2 := hsq y
  rw [hzero] at hy2
  refine ⟨(isMinResidualIterate_iff_isMinOn hk.le y).2 ?_, ?_⟩
  · rw [isMinOn_iff]
    intro z _
    have hz2 := hsq z
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Arnoldi.hessenberg_eq, hy2, hz2]
    nlinarith [sq_nonneg ‖(WithLp.toLp 2 ((fun i : Fin k => gvec h (‖b - T x₀‖ : ℝ) (i : ℕ)) -
      (hessenbergSqOf (rotated h k) k).mulVec z) : EuclideanSpace ℝ (Fin k))‖]
  · rw [norm_residual_eq_norm_firstVec_sub_mulVec hk.le y, ← Real.norm_eq_abs]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Arnoldi.hessenberg_eq, hy2]
    ring

/-- **(11.4.1) solved by Givens QR (MINRES).** "If `y_k ∈ ℝ^k` solves `R_k y_k = p_k`, then
`x_k = x₀ + Q_k y_k` solves (11.4.1) and the norm of the residual is given by
`‖b − A x_k‖₂ = |ρ_k|`." Here `R_k`, `p_k`, `ρ_k` are the backbone's rotated coefficients after `k`
Givens rotations of `H_k` (`Krylov.rotated`, `Krylov.gvec`, `Krylov.gamma`), and (11.4.1) is
`Krylov.IsMinResidualIterate`: `x_k` minimizes `‖b − Ax‖₂` over `x₀ + 𝒦(A, r₀, k)`, for `k` below
the grade. For symmetric `A` (MINRES) `H_k` is the tridiagonal matrix (11.4.3)
(`equation_11_4_2`); the statement holds for every `A`, and for unsymmetric `A` it is GMRES'
(11.4.10). -/
theorem equation_11_4_1 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
          (b - toEuclideanLin A x₀) j)‖ =
        |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k| :=
  isMinResidualIterate_of_rotated_mulVec A b x₀ hk hy

/-- Rotation `k` acts on rows `k` and `k + 1` only: the rows above are final. -/
private theorem rotated_succ_of_lt (h : ℕ → ℕ → ℝ) {k i : ℕ} (hi : i < k) (j : ℕ) :
    rotated h (k + 1) i j = rotated h k i j := by
  rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The rotated coefficients of a tridiagonal array have upper bandwidth `2`: rotation `k` mixes
row `k` (bandwidth `2` already) with the untouched row `k + 1` (bandwidth `1`). -/
private theorem rotated_eq_zero_of_add_two_lt (h : ℕ → ℕ → ℝ)
    (hh : ∀ i j, i + 1 < j → h i j = 0) (k : ℕ) :
    ∀ i j, i + 2 < j → rotated h k i j = 0 := by
  induction k with
  | zero => intro i j hij; exact hh i j (by omega)
  | succ k ih =>
    intro i j hij
    have hrow : ∀ j, k + 2 < j → rotated h k (k + 1) j = 0 := fun j hj => by
      rw [rotated_eq_of_le h k (k + 1) j le_rfl]
      exact hh _ _ (by omega)
    rw [rotated_succ_apply]
    split_ifs with h1 h2
    · subst h1
      rw [ih i j hij, hrow j (by omega), mul_zero, mul_zero, add_zero]
    · subst h2
      rw [ih k j (by omega), hrow j (by omega), mul_zero, mul_zero, add_zero]
    · exact ih i j hij

/-- **§11.4.1, the MINRES update.** "The transition `{H_{k−1}, R_{k−1}, p_{k−1}, ρ_{k−1}} →
{H_k, R_k, p_k, ρ_k}` can be realized … after the `k`th Lanczos step": one new rotation, since
`R_{k−1}` is the leading block of `R_k` and `p_{k−1}` the leading part of `p_k`; and "the matrix
`R_k` has upper bandwidth 2" (for symmetric `A`, where `H_k` is tridiagonal). Stated at `k + 1`:
the leading `k × k` block of `R_{k+1}` is `R_k`, the first `k` entries of `p_{k+1}` are `p_k`, and
`(R_k)_{ij} = 0` for `j > i + 2`. The flop counts are not formalized. -/
theorem minres_givens_update {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) (β₀ : ℝ) (k : ℕ) :
    (∀ i j : Fin k, hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) (k + 1))
        (k + 1) i.castSucc j.castSucc =
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j) ∧
    (∀ i : Fin k, (fun l : Fin (k + 1) => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l)
        i.castSucc = (fun l : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l) i) ∧
    ∀ i j : Fin k, (i : ℕ) + 2 < j →
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j = 0 := by
  refine ⟨fun i _ => rotated_succ_of_lt _ i.isLt _, fun i => rfl, fun i j hij => ?_⟩
  exact rotated_eq_zero_of_add_two_lt _
    (fun i j hij => Arnoldi.coeff_eq_zero_of_isSymmetric hA.isSymmetric_toEuclideanLin r₀ hij)
    k i j hij

/-- The Arnoldi vector `q_i` in coordinates. -/
private theorem sum_single_smul_vec (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : EuclideanSpace ℝ (Fin n)) {k : ℕ} (i : Fin k) :
    ∑ j : Fin k, (Pi.single i (1 : ℝ) : Fin k → ℝ) j • Arnoldi.vec T r j = Arnoldi.vec T r i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- **(11.4.5), SYMMLQ.** "Suppose `x_k = x₀ + Q_k y_k` where `y_k` is the … solution to the
`(k−1)`-by-`k` underdetermined system `H_{k−1}ᵀ y_k = β₀e₁`. … Thus, the residual `r_k = b − Ax_k`
is orthogonal to `q₁, …, q_{k−1}`." Stated at `k + 1`: for `y ∈ ℝ^{k+1}` with
`H_kᵀ y = β₀e₁` (any solution, not only the minimum-norm one) and `k + 1` at most the grade,
`⟪q_i, b − A(x₀ + Q_{k+1} y)⟫ = 0` for `i < k`. The printed derivation writes
`r_k = r₀ − AQ_{k−1}y_k` for `r₀ − AQ_k y_k`. -/
theorem equation_11_4_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k + 1 ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin (k + 1) → ℝ}
    (hy : (Lanczos.tridiagExt (toEuclideanLin A) (b - toEuclideanLin A x₀) k)ᵀ *ᵥ y =
      firstVec ‖b - toEuclideanLin A x₀‖ k) (i : Fin k) :
    inner ℝ (Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) i)
      (b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j)) = 0 := by
  set T := toEuclideanLin A
  set r₀ := b - T x₀
  set q := Arnoldi.vec T r₀
  have hT := hA.isSymmetric_toEuclideanLin
  have hon := orthonormal_vec_fin T r₀ hk
  have hres : b - T (x₀ + ∑ j, y j • q j) = r₀ - T (∑ j, y j • q j) := by
    rw [map_add, sub_add_eq_sub_sub]
  -- `⟪q_i, r₀⟫ = β₀ δ_{i0}`
  have hr0 : r₀ = ∑ j : Fin (k + 1), firstVec ‖r₀‖ (k + 1) j • q j := by
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp only [firstVec, Fin.val_zero, ↓reduceIte]
      exact (Arnoldi.smul_vec_zero T r₀).symm
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp [firstVec, hj']
    · simp
  have hqi : q i = ∑ j : Fin (k + 1), (Pi.single i.castSucc (1 : ℝ) : Fin (k + 1) → ℝ) j • q j :=
    (sum_single_smul_vec T r₀ i.castSucc).symm
  have h1 : inner ℝ (q i) r₀ = firstVec ‖r₀‖ k i := by
    rw [hqi]
    conv_lhs => rw [hr0]
    rw [inner_sum_smul_of_orthonormal hon, Finset.sum_eq_single i.castSucc]
    · simp [firstVec]
    · intro j _ hj; simp [hj]
    · simp
  -- `⟪q_i, A Q y⟫ = (H_kᵀ y)_i`
  have hTqi : T (q i) = ∑ l : Fin (k + 1),
      (Lanczos.tridiagExt T r₀ k *ᵥ (Pi.single i (1 : ℝ))) l • q l := by
    rw [← equation_11_4_2 hA r₀ k, sum_single_smul_vec]
  have h2 : inner ℝ (q i) (T (∑ j, y j • q j)) = ((Lanczos.tridiagExt T r₀ k)ᵀ *ᵥ y) i := by
    rw [← hT, hTqi, inner_sum_smul_of_orthonormal hon]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Pi.single_apply]
  rw [hres, inner_sub_right, h1, h2, hy, sub_self]

/-- `R̄_mᵀ z` only sees the first `m` entries of `z`: the last row of `R̄_m` vanishes. -/
private theorem rotated_transpose_mulVec (h : ℕ → ℕ → ℝ) (hh : ∀ i j, j + 1 < i → h i j = 0)
    (m : ℕ) (z : Fin (m + 1) → ℝ) :
    (hessenbergOf (rotated h m) m)ᵀ *ᵥ z =
      (hessenbergSqOf (rotated h m) m)ᵀ *ᵥ fun i => z i.castSucc := by
  funext j
  simp only [mulVec, dotProduct, transpose_apply, Fin.sum_univ_castSucc, hessenbergOf,
    hessenbergSqOf, Matrix.of_apply, Fin.val_last, Fin.val_castSucc]
  rw [rotated_last_row h hh m j j.isLt, zero_mul, add_zero]

/-- The squared Euclidean norm of `z ∈ ℝ^{m+1}` splits off its last entry. -/
private theorem norm_sq_toLp_snoc {m : ℕ} (z : Fin (m + 1) → ℝ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i : Fin m => z i.castSucc) : EuclideanSpace ℝ (Fin m))‖ ^ 2 +
        z (Fin.last m) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [Real.norm_eq_abs, sq_abs]

/-- The accumulated Givens rotation is orthogonal: `Q_mᵀ ∈ O(m+1)` and `Q_mᵀQ_m = 1`. -/
private theorem givensQ_transpose_mem (h : ℕ → ℕ → ℝ) {m : ℕ}
    (hρ : ∀ l < m, givensRho h l ≠ 0) :
    (givensQ h m)ᵀ ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ ∧ (givensQ h m)ᵀ * givensQ h m = 1 := by
  have hQ := givensQ_mem_unitaryGroup h m hρ
  have h1 : star (givensQ h m) * givensQ h m = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have h2 : star (givensQ h m) = (givensQ h m)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, h2 ▸ h1⟩
  rw [← h2]
  exact Unitary.star_mem hQ

/-- The minimum-norm solve of the underdetermined `H̄_mᵀ y = c` by the transposed Givens QR:
`y = Q_mᵀ[w; 0]` with `R_mᵀ w = c` solves it, with least norm. -/
private theorem minNorm_snoc (h : ℕ → ℕ → ℝ) (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρ : ∀ l < m, givensRho h l ≠ 0) (c w : Fin m → ℝ)
    (hw : (hessenbergSqOf (rotated h m) m)ᵀ *ᵥ w = c) :
    (hessenbergOf h m)ᵀ *ᵥ ((givensQ h m)ᵀ *ᵥ Fin.snoc w 0) = c ∧
    ∀ y' : Fin (m + 1) → ℝ, (hessenbergOf h m)ᵀ *ᵥ y' = c →
      ‖(WithLp.toLp 2 ((givensQ h m)ᵀ *ᵥ Fin.snoc w 0) : EuclideanSpace ℝ (Fin (m + 1)))‖ ≤
        ‖(WithLp.toLp 2 y' : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  obtain ⟨hQt, hQQ⟩ := givensQ_transpose_mem h hρ
  have hRtu : IsUnit (hessenbergSqOf (rotated h m) m)ᵀ :=
    (isUnit_transpose _).2 (isUnit_hessenbergSqOf_rotated_self h hh hρ)
  have hkey : ∀ z : Fin (m + 1) → ℝ, (hessenbergOf h m)ᵀ *ᵥ ((givensQ h m)ᵀ *ᵥ z) =
      (hessenbergSqOf (rotated h m) m)ᵀ *ᵥ fun i => z i.castSucc := fun z => by
    rw [mulVec_mulVec, ← Matrix.transpose_mul, givensQ_mul_hessenbergOf,
      rotated_transpose_mulVec h hh]
  refine ⟨?_, fun y' hy' => ?_⟩
  · rw [hkey]
    simpa using hw
  · have hyz : y' = (givensQ h m)ᵀ *ᵥ (givensQ h m *ᵥ y') := by
      rw [mulVec_mulVec, hQQ, one_mulVec]
    have hzw : (fun i : Fin m => (givensQ h m *ᵥ y') i.castSucc) = w := by
      have h1 : (hessenbergSqOf (rotated h m) m)ᵀ *ᵥ
          (fun i : Fin m => (givensQ h m *ᵥ y') i.castSucc) =
          (hessenbergSqOf (rotated h m) m)ᵀ *ᵥ w := by
        rw [← hkey, ← hyz, hy', hw]
      exact (Matrix.mulVec_injective_iff_isUnit.2 hRtu) h1
    rw [hyz, norm_toLp_mulVec_of_mem_unitaryGroup hQt, norm_toLp_mulVec_of_mem_unitaryGroup hQt]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_sq_toLp_snoc, norm_sq_toLp_snoc (givensQ h m *ᵥ y'), hzw]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    nlinarith [sq_nonneg ((givensQ h m *ᵥ y') (Fin.last m))]

/-- **§11.4.1, SYMMLQ's minimum-norm solution.** "Note that the underdetermined system (11.4.5) has
full row rank and that `y_k` can be determined via a Givens rotation lower triangularization …
`H_{k−1}ᵀG₁⋯G_{k−1} = [L_{k−1} | 0]` where `L_{k−1}` is lower triangular. (This is just the
transpose of the Givens QR factorization of `H_{k−1}`.) If `w_{k−1} ∈ ℝ^{k−1}` solves the
necessarily nonsingular system `L_{k−1}w_{k−1} = β₀e₁`, then `y_k = G₁⋯G_{k−1}[w_{k−1}; 0]`."
"The special structure of `L_{k−1}` (it has lower bandwidth equal to 2)."

With `m = k − 1` below the grade, `G₁⋯G_m = Q_mᵀ` for the backbone's accumulated rotation
`Q_m = Krylov.givensQ` (orthogonal) and `L_m = R_mᵀ`, `R_m` the rotated square block: (i)
`H_mᵀQ_mᵀ = R̄_mᵀ = [L_m | 0]`; (ii) `L_m` is lower triangular and nonsingular, and has lower
bandwidth `2` for symmetric `A`; (iii) for `L_mw = β₀e₁`, `y = Q_mᵀ[w; 0]` solves (11.4.5) and has
the least norm among its solutions. -/
theorem symmlq_minNorm_solution {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (hm : m < grade (toEuclideanLin A) r₀) (β₀ : ℝ) :
    (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *
        (givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ =
      (hessenbergOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ ∧
    (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ.IsLowerTriangular ∧
    IsUnit (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ ∧
    (∀ i j : Fin m, (j : ℕ) + 2 < i →
      (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ i j = 0) ∧
    ∀ w : Fin m → ℝ,
      (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ *ᵥ w = firstVec β₀ m →
      (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *ᵥ
          ((givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ *ᵥ Fin.snoc w 0) =
        firstVec β₀ m ∧
      ∀ y' : Fin (m + 1) → ℝ, (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *ᵥ y' = firstVec β₀ m →
        ‖(WithLp.toLp 2 ((givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ *ᵥ Fin.snoc w 0) :
            EuclideanSpace ℝ (Fin (m + 1)))‖ ≤
          ‖(WithLp.toLp 2 y' : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  have hh : ∀ i j, j + 1 < i → Arnoldi.coeff (toEuclideanLin A) r₀ i j = 0 :=
    fun i j hij => Arnoldi.coeff_eq_zero_of_lt _ _ hij
  have hρ : ∀ l < m, givensRho (Arnoldi.coeff (toEuclideanLin A) r₀) l ≠ 0 := fun l hl => by
    have := givensRho_arnoldi_ne_zero (A := toEuclideanLin A) (b := r₀) (x₀ := 0) (k := l)
      (by simpa using (show l + 1 < grade (toEuclideanLin A) r₀ by omega))
    simpa using this
  rw [Arnoldi.hessenberg_eq]
  refine ⟨?_, ?_, ?_, fun i j hij => ?_, fun w hw => minNorm_snoc _ hh hρ _ w hw⟩
  · rw [← Matrix.transpose_mul, givensQ_mul_hessenbergOf]
  · exact (hessenbergSqOf_rotated_isUpperTriangular _ hh (Nat.le_succ m)).transpose
  · exact (isUnit_transpose _).2 (isUnit_hessenbergSqOf_rotated_self _ hh hρ)
  · rw [transpose_apply]
    exact rotated_eq_zero_of_add_two_lt _
      (fun i j hij => Arnoldi.coeff_eq_zero_of_isSymmetric hA.isSymmetric_toEuclideanLin r₀ hij)
      m j i hij

/-! ### §11.4.2: LSQR and LSMR -/

/-- The image of `{j | j < k}` is the range over `Fin k`. -/
private theorem image_Iio_eq_range {α : Type*} (f : ℕ → α) (k : ℕ) :
    f '' Set.Iio k = Set.range fun j : Fin k => f j := by
  ext v
  simp only [Set.mem_image, Set.mem_Iio, Set.mem_range]
  exact ⟨fun ⟨j, hj, hv⟩ => ⟨⟨j, hj⟩, hv⟩, fun ⟨j, hj⟩ => ⟨j, j.isLt, hj⟩⟩

section LeastSquares

variable {m : ℕ}

/-- The lower bidiagonal matrix of the Paige–Saunders process, mapped along `algebraMap ℝ ℝ`, is
the coefficient array of its Hessenberg relation. -/
private theorem bidiagLower_eq_hessenbergOf (A : Matrix (Fin m) (Fin n) ℝ)
    (u₁ : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k =
      hessenbergOf (fun i j =>
        ((if i = j then GolubKahan.alpha (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j
          else if i = j + 1 then GolubKahan.beta (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j
          else 0 : ℝ) : ℝ)) k := by
  ext i j
  simp only [GolubKahan.bidiagLower_apply, hessenbergOf, Matrix.of_apply]

/-- **(11.4.6).** "If we apply Algorithm 10.4.2 with `u₁ = r₀/β₀` … then after `k` steps we have
… `A V_k = U_{k+1} B̃_k`" with `B̃_k ∈ ℝ^{(k+1)×k}` lower bidiagonal (`α_j` on the diagonal,
`β_j` below), and `V_k`, `U_{k+1}` with orthonormal columns. The Paige–Saunders lower
bidiagonalization of `A` from `u₁` is the Golub–Kahan process of the pair `(Aᵀ, A)`
(`Numlib/Krylov/Bidiagonalization`): its `v_j` are `GolubKahan.leftVec Aᵀ A u₁`, its `u_j`
`GolubKahan.rightVec Aᵀ A u₁`, and `B̃_k` is `GolubKahan.bidiagLower Aᵀ A u₁ k`. The relation is
stated column-combination-wise, `A (V_k y) = U_{k+1} (B̃_k y)`, and the orthonormality for `k` (or
`k + 1`) at most the grade of the Gram operator; the book's `p_k ≠ 0` is the second grade
condition. -/
theorem equation_11_4_6 (A : Matrix (Fin m) (Fin n) ℝ) (u₁ : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    (∀ y : Fin k → ℝ, toEuclideanLin A
        (∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) =
      ∑ i : Fin (k + 1), (GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ
        y) i • GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ i) ∧
    (k ≤ grade (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ u₁) →
      Orthonormal ℝ fun j : Fin k =>
        GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) ∧
    (k + 1 ≤ grade (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) u₁ →
      Orthonormal ℝ fun i : Fin (k + 1) =>
        GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ i) := by
  refine ⟨fun y => ?_, fun hk => ?_, fun hk => ?_⟩
  · have hrel := GolubKahan.hessenbergRelation₂ (A := toEuclideanLin Aᵀ)
      (Astar := toEuclideanLin A) u₁ (fun u x => inner_toEuclideanLin_transpose' A u x)
    rw [bidiagLower_eq_hessenbergOf]
    exact hrel.apply_sum k y
  · exact (Arnoldi.orthonormal _ _).comp (Fin.castLE hk) (Fin.castLE_injective hk)
  · exact (Arnoldi.orthonormal _ _).comp (Fin.castLE hk) (Fin.castLE_injective hk)

/-- **§11.4.2.** "It can be shown that `span{v₁, …, v_k} = 𝒦(AᵀA, Aᵀr₀, k)`": for the
Paige–Saunders process from `u₁ = r₀/β₀` (any nonzero multiple of `r₀`), the span of its first `k`
right vectors is the Krylov subspace of the normal equations. `GolubKahan.span_leftVec` (the
book's (10.4.12) for the adjoint pair), and the invariance of a Krylov subspace under scaling of
its starting vector. -/
theorem lsqr_span_eq (A : Matrix (Fin m) (Fin n) ℝ) {r₀ u₁ : EuclideanSpace ℝ (Fin m)} {β₀ : ℝ}
    (hβ : β₀ ≠ 0) (hr : r₀ = β₀ • u₁) (k : ℕ) :
    Submodule.span ℝ (GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (Aᵀ * A)) (toEuclideanLin Aᵀ r₀) k := by
  rw [GolubKahan.span_leftVec, toEuclideanLin_mul, hr, map_smul]
  refine le_antisymm ?_ (subspace_smul _ _ _ _)
  calc Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ u₁) k
      = Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
          (β₀⁻¹ • β₀ • toEuclideanLin Aᵀ u₁) k := by rw [inv_smul_smul₀ hβ]
    _ ≤ _ := subspace_smul _ _ _ _

/-- **(11.4.7), LSQR.** "The `k`th approximate minimizer `x_k` solves
`min_{x ∈ x₀ + 𝒦(AᵀA, Aᵀr₀, k)} ‖Ax − b‖₂`. Thus, `x_k = x₀ + V_k y_k` where `y_k` is the minimizer
of `‖A(x₀ + V_k y) − b‖₂ = ‖U_{k+1}B̃_k y − (b − Ax₀)‖₂ = ‖B̃_k y − β₀e₁‖₂`." For `r₀ = β₀u₁`,
`‖u₁‖ = 1` and `U_{k+1}` orthonormal (`k + 1` at most the grade): (i) the reduction
`‖b − A(x₀ + V_k y)‖₂ = ‖β₀e₁ − B̃_k y‖₂` for every `y`, and (ii) if `y` minimizes the right side
then `x₀ + V_k y` minimizes `‖b − Ax‖₂` over `x₀ + 𝒦(AᵀA, Aᵀr₀, k)` (`IsMinResidual`). The
printed `β₁e₁` in the Givens display is this `β₀e₁`. -/
theorem equation_11_4_7 (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n)) {u₁ : EuclideanSpace ℝ (Fin m)} {β₀ : ℝ} (hu : ‖u₁‖ = 1)
    (hβ : β₀ ≠ 0) (hr : b - toEuclideanLin A x₀ = β₀ • u₁) {k : ℕ}
    (hk : k + 1 ≤ grade (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) u₁) :
    (∀ y : Fin k → ℝ, ‖b - toEuclideanLin A
        (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j)‖ =
      ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ y) :
          EuclideanSpace ℝ (Fin (k + 1)))‖) ∧
    ∀ y : Fin k → ℝ, IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ z) :
          EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ y →
      (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) - x₀ ∈
          Krylov.subspace (toEuclideanLin (Aᵀ * A)) (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀))
            k ∧
        ∀ x, x - x₀ ∈ Krylov.subspace (toEuclideanLin (Aᵀ * A))
            (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀)) k →
          ‖b - toEuclideanLin A
              (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j)‖ ≤
            ‖b - toEuclideanLin A x‖ := by
  set T := toEuclideanLin A
  set V := GolubKahan.leftVec (toEuclideanLin Aᵀ) T u₁
  have hon := (equation_11_4_6 A u₁ k).2.2 hk
  have hred : ∀ y : Fin k → ℝ, ‖b - T (x₀ + ∑ j, y j • V j)‖ =
      ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) T u₁ k *ᵥ y) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := by
    intro y
    have hres := GolubKahan.residual_eq (A := T) (Astar := toEuclideanLin Aᵀ)
      (fun u x => (real_inner_comm _ _).trans
        ((inner_toEuclideanLin_transpose' A x u).symm.trans (real_inner_comm _ _))) hu hr k y
    rw [hres, map_algebraMap_real, norm_sum_smul_of_orthonormal hon]
  refine ⟨hred, fun y hy => ⟨?_, fun x hx => ?_⟩⟩
  · rw [add_sub_cancel_left, ← lsqr_span_eq A hβ hr k]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.isLt, rfl⟩)
  · rw [← lsqr_span_eq A hβ hr k, image_Iio_eq_range] at hx
    have hx' : x - x₀ ∈ Submodule.span ℝ (Set.range fun j : Fin k => V j) := hx
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx'
    have hxe : x = x₀ + ∑ j, z j • V j := by rw [hz]; abel
    rw [hxe, hred, hred]
    exact hy (Set.mem_univ z)

/-- **§11.4.2, LSMR**, as the book defines it: "mathematically equivalent to MINRES applied to the
normal equations `AᵀAx = Aᵀb`". `x` is the `k`-th LSMR iterate from `x₀` when it is the
minimal-residual iterate (`Krylov.IsMinResidualIterate`) of the system `AᵀAx = Aᵀb`: it minimizes
`‖Aᵀ(b − Ax)‖₂` over `x₀ + 𝒦(AᵀA, Aᵀr₀, k)`, `r₀ = b − Ax₀`. -/
def IsLSMRIterate (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) (k : ℕ)
    (x : Fin n → ℝ) : Prop :=
  IsMinResidualIterate (toEuclideanLin (Aᵀ * A)) (WithLp.toLp 2 (Aᵀ *ᵥ b)) (WithLp.toLp 2 x₀) k
    (WithLp.toLp 2 x)

/-- **§11.4.2.** "The 2-norms of the vectors `r_k = b − Ax_k` and `Aᵀr_k` decrease
monotonically": along a sequence of LSMR iterates, `‖Aᵀr_k‖₂` is nonincreasing (minimal residuals
over nested spaces), and so is `‖r_k‖₂` when `A` has full column rank (Fong–Saunders:
`‖r_k‖₂² = ‖b − Ax_LS‖₂² + ‖x_k − x_LS‖²_{AᵀA}`, and the energy error of MINRES on the positive
definite system is nonincreasing). -/
theorem lsmr_norm_residual_antitone (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) {x : ℕ → Fin n → ℝ} (hx : ∀ k, IsLSMRIterate A b x₀ k (x k)) :
    Antitone (fun k => ‖(WithLp.toLp 2 (Aᵀ *ᵥ (b - A *ᵥ x k)) : EuclideanSpace ℝ (Fin n))‖) ∧
      (Function.Injective A.mulVec →
        Antitone fun k => ‖(WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m))‖) := by
  refine ⟨?_, fun hinj => ?_⟩
  · have h := IsMinResidualIterate.norm_residual_antitone hx
    simpa only [toEuclideanLin_toLp, ← WithLp.toLp_sub, mulVec_sub, mulVec_mulVec] using h
  have hG : (Aᵀ * A).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using PosDef.conjTranspose_mul_self A hinj
  set xs : Fin n → ℝ := (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)
  have hGxs : (Aᵀ * A) *ᵥ xs = Aᵀ *ᵥ b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit),
      one_mulVec]
  have hstar : toEuclideanLin (Aᵀ * A) (WithLp.toLp 2 xs) = WithLp.toLp 2 (Aᵀ *ᵥ b) := by
    rw [toEuclideanLin_toLp, hGxs]
  have he := IsMinResidualIterate.energyNorm_error_antitone
    (hG.isSymmetricCoercive_toEuclideanLin) hx hstar
  -- the energy norm of `G = AᵀA` is `‖A ·‖₂`
  have hen : ∀ w : Fin n → ℝ, energyNorm (toEuclideanLin (Aᵀ * A)) (WithLp.toLp 2 w) =
      ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℝ (Fin m))‖ := by
    intro w
    rw [energyNorm, toEuclideanLin_toLp, RCLike.re_to_real, inner_toLp, ← mulVec_mulVec,
      mulVec_transpose, ← dotProduct_mulVec, ← inner_toLp, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
  -- Pythagoras: `‖r_k‖² = ‖b − A xs‖² + ‖A (xs − x_k)‖²`
  have hpyth : ∀ k, ‖(WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m))‖ ^ 2 =
      ‖(WithLp.toLp 2 (b - A *ᵥ xs) : EuclideanSpace ℝ (Fin m))‖ ^ 2 +
        ‖(WithLp.toLp 2 (A *ᵥ (xs - x k)) : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
    intro k
    have horth : inner ℝ (WithLp.toLp 2 (b - A *ᵥ xs) : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 (A *ᵥ (xs - x k))) = 0 := by
      rw [inner_toLp, dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, mulVec_mulVec, hGxs,
        sub_self, zero_dotProduct]
    have hsum : (WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m)) =
        WithLp.toLp 2 (b - A *ᵥ xs) + WithLp.toLp 2 (A *ᵥ (xs - x k)) := by
      rw [← WithLp.toLp_add, mulVec_sub]; congr 1; abel
    rw [hsum, norm_add_sq_real, horth]
    ring
  intro k l hkl
  have hel := he hkl
  simp only [← WithLp.toLp_sub, hen] at hel
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hpyth, hpyth]
  have := pow_le_pow_left₀ (norm_nonneg _) hel 2
  linarith

end LeastSquares

/-! ### §11.4.3: GMRES -/

/-- **(11.4.8) and the displays after it.** "After `k` steps of the Arnoldi iteration … it is easy
to confirm using (10.5.2) that `AQ_k = Q_{k+1}H̃_k` where the columns of `Q_{k+1}` are the
orthonormal Arnoldi vectors and the upper Hessenberg matrix `H̃_k` … Moreover, if `q₁ = r₀/β₀` …
then `span{q₁, …, q_k} = 𝒦(A, r₀, k)`." The relation column-combination-wise,
`H̃_k = Arnoldi.hessenberg` upper Hessenberg, the span, and the orthonormality for `k + 1` at most
the grade. -/
theorem equation_11_4_8 (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (∀ y : Fin k → ℝ, toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Arnoldi.hessenberg (toEuclideanLin A) r₀ k *ᵥ y) i •
        Arnoldi.vec (toEuclideanLin A) r₀ i) ∧
    (Arnoldi.hessenberg (toEuclideanLin A) r₀ k).IsUpperHessenbergRect ∧
    Submodule.span ℝ (Arnoldi.vec (toEuclideanLin A) r₀ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin A) r₀ k ∧
    (k + 1 ≤ grade (toEuclideanLin A) r₀ →
      Orthonormal ℝ fun i : Fin (k + 1) => Arnoldi.vec (toEuclideanLin A) r₀ i) :=
  ⟨fun y => Arnoldi.apply_sum _ r₀ k y,
    (Arnoldi.hessenbergRelation _ r₀).hessenbergOf_isUpperHessenbergRect k,
    Arnoldi.span_vec _ r₀ k, fun hk => orthonormal_vec_fin _ r₀ hk⟩

/-- **§11.4.3, the GMRES reduction.** "As with MINRES, we must find a vector `y ∈ ℝ^k` so that
`‖A(x₀ + Q_k y) − b‖₂ = ‖Q_{k+1}H̃_k y − (b − Ax₀)‖₂ = ‖H̃_k y − β₀e₁‖₂` is minimized. If `y_k` is
the solution to this `(k+1)`-by-`k` least squares problem, then the `k`-th GMRES iterate is given by
`x_k = x₀ + Q_k y_k`": the norm identity, and `x₀ + Q_k y` is the minimal-residual iterate exactly
when `y` minimizes the least-squares objective, for `k` at most the grade. -/
theorem gmres_reduction (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      ‖(WithLp.toLp 2 (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ ∧
    (IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ↔
      IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2
        (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z -
          firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖)
        Set.univ y) := by
  have hneg : ∀ z : Fin k → ℝ, ‖(WithLp.toLp 2
      (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ =
      ‖(WithLp.toLp 2 (firstVec ‖b - toEuclideanLin A x₀‖ (k + 1) -
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := fun z => by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  refine ⟨?_, ?_⟩
  · rw [norm_sub_rev, norm_residual_eq_norm_firstVec_sub_mulVec hk y, hneg]
    rfl
  · simp only [hneg]
    exact isMinResidualIterate_iff_isMinOn hk y

/-- **(11.4.9).** "If Givens rotations `G₁, …, G_k` have been determined so that
`G_kᵀ⋯G₁ᵀH̃_k = [R_k; 0]`, `R_k ∈ ℝ^{k×k}`, is upper triangular": the accumulated rotation
`Krylov.givensQ` (the book's `G_kᵀ⋯G₁ᵀ`) is orthogonal for `k` below the grade, it carries `H̃_k` to
the rotated coefficients, whose square part `R_k` is upper triangular and whose last row
vanishes. -/
theorem equation_11_4_9 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) :
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k ∈
      Matrix.orthogonalGroup (Fin (k + 1)) ℝ ∧
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k *
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k =
      hessenbergOf (rotated (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k) k ∧
    (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
      (b - toEuclideanLin A x₀)) k) k).IsUpperTriangular ∧
    ∀ j < k, rotated (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k k j = 0 := by
  set h := Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)
  have hh : ∀ i j, j + 1 < i → h i j = 0 := fun i j hij => Arnoldi.coeff_eq_zero_of_lt _ _ hij
  exact ⟨givensQ_mem_unitaryGroup h k fun l hl => givensRho_arnoldi_ne_zero (by omega),
    givensQ_mul_hessenbergOf h k, hessenbergSqOf_rotated_isUpperTriangular h hh (by omega),
    fun j hj => rotated_last_row h hh k j hj⟩

/-- **(11.4.10) and the line after it.** "If … `G_kᵀ⋯G₁ᵀ(β₀e₁) = [p_k; ρ_k]` … then `R_k y_k = p_k`
and `|ρ_k| = ‖Ax_k − b‖₂`": the rotated right-hand side is `(p_k, ρ_k)` with
`p_k = (gvec h β₀ i)_{i<k}` and `ρ_k = gamma h β₀ k`; for `k` below the grade the solution of
`R_k y = p_k` gives the GMRES iterate, with residual norm `|ρ_k|`. -/
theorem equation_11_4_10 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k *ᵥ
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1) =
      (fun i : Fin (k + 1) => if (i : ℕ) < k then
        gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ i
        else gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k) ∧
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ k| := by
  obtain ⟨h1, h2⟩ := isMinResidualIterate_of_rotated_mulVec A b x₀ hk hy
  exact ⟨givensQ_mulVec_firstVec _ _ k, h1, by rw [norm_sub_rev, h2]⟩

/-- **§11.4.3, one new rotation per step.** "The transition `{R_{k−1}, p_{k−1}, ρ_{k−1}} →
{R_k, p_k, ρ_k}` is a particularly simple update that involves the generation of a single rotation
`G_k` and exploitation of the identities `R_{k−1} = R_k(1:k−1, 1:k−1)` and
`p_k(1:k−1) = p_{k−1}`." Stated at `k + 1`. -/
theorem gmres_givens_prefix (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : EuclideanSpace ℝ (Fin n))
    (β₀ : ℝ) (k : ℕ) :
    (∀ i j : Fin k, hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) (k + 1))
        (k + 1) i.castSucc j.castSucc =
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j) ∧
    ∀ i : Fin k, (fun l : Fin (k + 1) => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l)
        i.castSucc = (fun l : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l) i :=
  ⟨fun i _ => rotated_succ_of_lt _ i.isLt _, fun _ => rfl⟩

/-! ### §11.4.4: the polynomial point of view -/

/-- **§11.4.4.** "Suppose the columns of `Q_k ∈ ℝ^{n×k}` span `𝒦(A, q₁, k)`. It follows that if
`y ∈ ℝ^k`, then `Q_k y = φ(A)q₁` for some polynomial `φ` that has degree `k − 1` or less" — and
conversely every such `φ(A)q₁` is some `Q_k y`. -/
theorem krylov_eq_aeval (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (Q : Fin k → EuclideanSpace ℝ (Fin n))
    (hQ : Submodule.span ℝ (Set.range Q) = Krylov.subspace (toEuclideanLin A) q₁ k) :
    (∀ y : Fin k → ℝ, ∃ φ : ℝ[X], φ.degree < k ∧ ∑ j, y j • Q j = aeval (toEuclideanLin A) φ q₁) ∧
      ∀ φ : ℝ[X], φ.degree < k → ∃ y : Fin k → ℝ,
        ∑ j, y j • Q j = aeval (toEuclideanLin A) φ q₁ := by
  refine ⟨fun y => ?_, fun φ hφ => ?_⟩
  · have hmem : ∑ j, y j • Q j ∈ Krylov.subspace (toEuclideanLin A) q₁ k := by
      rw [← hQ]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨φ, hφ, h⟩ := (mem_subspace_iff_exists_aeval _ _).1 hmem
    exact ⟨φ, hφ, h.symm⟩
  · have hmem := aeval_apply_mem_subspace (toEuclideanLin A) q₁ hφ
    rw [← hQ] at hmem
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem

/-- **§11.4.4, the three-line display.** For a minimal-residual iterate `x_k`,
`min_{x ∈ x₀ + 𝒦(A, r₀, k)} ‖b − Ax‖₂ = min_{φ ∈ ℙ_{k−1}} ‖(I − Aφ(A))r₀‖₂ =
min_{ψ ∈ ℙ_k, ψ(0) = 1} ‖ψ(A)r₀‖₂`, as infima over the polynomials of degree `< k` and over the
consistent polynomials of degree `≤ k`. The printed middle term `‖b − A(x₀ + φ(A))r₀‖₂` misplaces a
parenthesis: it is `‖b − A(x₀ + φ(A)r₀)‖₂ = ‖(I − Aφ(A))r₀‖₂`. -/
theorem minResidual_eq_iInf_poly (A : Matrix (Fin n) (Fin n) ℝ) {b x₀ x : EuclideanSpace ℝ (Fin n)}
    {k : ℕ} (hx : IsMinResidualIterate (toEuclideanLin A) b x₀ k x) :
    ‖b - toEuclideanLin A x‖ = ⨅ φ : {φ : ℝ[X] // φ.degree < k},
        ‖(b - toEuclideanLin A x₀) -
          toEuclideanLin A (aeval (toEuclideanLin A) φ.1 (b - toEuclideanLin A x₀))‖ ∧
      ‖b - toEuclideanLin A x‖ = ⨅ ψ : {ψ : ℝ[X] // ψ.degree ≤ k ∧ ψ.eval 0 = 1},
        ‖aeval (toEuclideanLin A) ψ.1 (b - toEuclideanLin A x₀)‖ := by
  set T := toEuclideanLin A
  refine ⟨?_, hx.norm_residual_eq_iInf⟩
  have hne : Nonempty {φ : ℝ[X] // φ.degree < k} := ⟨⟨0, by
    rw [degree_zero]; exact WithBot.bot_lt_coe k⟩⟩
  have hbdd : BddBelow (Set.range fun φ : {φ : ℝ[X] // φ.degree < k} =>
      ‖(b - T x₀) - T (aeval T φ.1 (b - T x₀))‖) :=
    ⟨0, by rintro _ ⟨φ, rfl⟩; exact norm_nonneg _⟩
  have hres : ∀ v, b - T (x₀ + v) = (b - T x₀) - T v := fun v => by rw [map_add]; abel
  refine le_antisymm (le_ciInf fun φ => ?_) ?_
  · have h := hx.min (x₀ + aeval T φ.1 (b - T x₀))
      (by rw [add_sub_cancel_left]; exact aeval_apply_mem_subspace T _ φ.2)
    rwa [hres] at h
  · obtain ⟨φ, hφ, h⟩ := (mem_subspace_iff_exists_aeval T (b - T x₀)).1 hx.mem
    refine (ciInf_le hbdd ⟨φ, hφ⟩).trans_eq ?_
    rw [h, ← hres, add_sub_cancel]

/-! ### §11.4.5: the unsymmetric Lanczos family -/

/-- `𝒦(A, c • v, k) = 𝒦(A, v, k)` for `c ≠ 0`. -/
private theorem subspace_smul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (v : E) {c : ℝ} (hc : c ≠ 0) (k : ℕ) :
    Krylov.subspace T (c • v) k = Krylov.subspace T v k := by
  refine le_antisymm (subspace_smul _ _ _ _) ?_
  calc Krylov.subspace T v k = Krylov.subspace T (c⁻¹ • c • v) k := by rw [inv_smul_smul₀ hc]
    _ ≤ _ := subspace_smul _ _ _ _

/-- **(11.4.12)–(11.4.13), two-sided Lanczos.** "Suppose we complete `k` steps of (10.5.11) with
`q₁ = r₀/β₀` … and `r₀ᵀr̃₀ ≠ 0`. This means we have the partial factorizations
`AQ_k = Q_kT_k + r_ke_kᵀ`, `Q̃_kᵀr_k = 0`, `AᵀQ̃_k = Q̃_kT_kᵀ + r̃_ke_kᵀ`, `Q_kᵀr̃_k = 0` where
`ran(Q_k) = 𝒦(A, r₀, k)`, `ran(Q̃_k) = 𝒦(Aᵀ, r̃₀, k)`. In addition, `Q̃_kᵀQ_k = I_k` and
`Q̃_kᵀAQ_k = T_k` is tridiagonal."

The process is the backbone's `BiLanczos` for `T = toEuclideanLin A` and its adjoint
`toEuclideanLin Aᵀ`, started from `q₁ = r₀/β₀` and the shadow `q̃₁` scaled so that `q̃₁ᵀq₁ = 1`
(the book's normalization of the pair); "no serious breakdown through step `k`" is
`BiLanczos.NoBreakdown … k`. With `0`-based indices (`q_j` for the book's `q_{j+1}`, the book's
`r_k = β_k q_{k+1}` being `δ_k q_k`), the clauses are: the three-term relation of column `j < k`
of `AQ_k = Q_kT_k + r_ke_kᵀ` (`T_k`'s entries `BiLanczos.coeff`: `α` on the diagonal, `δ` below,
`β` above); `Q̃_kᵀ r_k = 0`; the biorthogonality `Q̃_kᵀQ_k = I_k`; `Q̃_kᵀAQ_k = T_k` (`T_k`
tridiagonal); and the two ranges. The dual relation (11.4.13) is `equation_11_4_13`. -/
theorem equation_11_4_12 (A : Matrix (Fin n) (Fin n) ℝ) {r₀ rt₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)}
    {β₀ γ₀ : ℝ} (hβ : β₀ ≠ 0) (hγ : γ₀ ≠ 0) (hr : r₀ = β₀ • q₁) (hrt : rt₀ = γ₀ • qt₁) {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) :
    (∀ j < k, toEuclideanLin A (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.vecPrev (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1) •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1)) ∧
    (∀ i < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) = 0) ∧
    (∀ i < k, ∀ j < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) = if i = j then 1 else 0) ∧
    (∀ i < k, ∀ j < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (toEuclideanLin A (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j)) =
        BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i j) ∧
    (∀ i j, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i j = 0) ∧
    Submodule.span ℝ (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin A) r₀ k ∧
    Submodule.span ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin Aᵀ) rt₀ k := by
  refine ⟨fun j hj => BiLanczos.apply_vec _ _ _ _ (h.delta_ne_zero j hj), fun i hi => ?_,
    fun i hi j hj => BiLanczos.inner_dualVec_vec h hi.le hj.le, fun i hi j hj => ?_,
    fun i j h1 h2 h3 => BiLanczos.coeff_eq_zero _ _ _ _ h1 h2 h3, ?_, ?_⟩
  · rw [BiLanczos.inner_dualVec_vec h hi.le le_rfl, ite_eq_right hi.ne]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact BiLanczos.inner_dualVec_apply_vec h (by omega) (by omega)
  · rw [BiLanczos.span_vec h, hr, subspace_smul_eq _ _ hβ]
  · rw [BiLanczos.span_dualVec h, hrt, subspace_smul_eq _ _ hγ]

/-- **(11.4.13).** The dual relation of the two-sided Lanczos process: column `j < k` of
`AᵀQ̃_k = Q̃_kT_kᵀ + r̃_ke_kᵀ` (the three-term recurrence of the dual vectors, the entries of `T_kᵀ`
read off `BiLanczos.coeff`), and `Q_kᵀr̃_k = 0`, the book's `r̃_k` being a multiple of
`q̃_{k+1}`. -/
theorem equation_11_4_13 (A : Matrix (Fin n) (Fin n) ℝ) {q₁ qt₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) :
    (∀ j < k, toEuclideanLin Aᵀ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.dualVecPrev (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1) •
          BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1)) ∧
    ∀ i < k, inner ℝ (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) = 0 := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := BiLanczos.apply_dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁
      (h.delta_ne_zero j hj)
    simpa only [starRingEnd_real, RingHom.id_apply] using this
  · rw [BiLanczos.inner_vec_dualVec h hi.le le_rfl, ite_eq_right hi.ne]

/-- **§11.4.5, BiCG as a Petrov–Galerkin method.** "In step `k` of the biconjugate gradient (BiCG)
method, an iterate `x_k = x₀ + Q_ky_k` is produced where `y_k ∈ ℝ^k` solves the `k`-by-`k`
tridiagonal system `T_ky_k = Q̃_kᵀr₀`. It follows that `Q̃_kᵀ(b − Ax_k) = 0`. … Assume that
`T_k` has an LU factorization `T_k = L_kU_k` … It follows that
`x_k = x₀ + (Q_kU_k⁻¹)(L_k⁻¹(Q̃_kᵀr₀))`." Stated at `k + 1` steps: (i) the residual of
`x₀ + Q_{k+1}y` is orthogonal to `q̃_0, …, q̃_k` whenever `T_{k+1}y = Q̃_{k+1}ᵀr₀`; (ii) if
`T_{k+1} = LU` with `L`, `U` invertible, that `y` is `U⁻¹(L⁻¹(Q̃_{k+1}ᵀr₀))`. The BiCG recurrence
of Figure 11.4.1 computes this iterate
(`BCG.isPetrovGalerkin`, through `bicg_spec`). -/
theorem bicg_residual_orthogonal (A : Matrix (Fin n) (Fin n) ℝ)
    {b x₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (k + 1))
    {y : Fin (k + 1) → ℝ}
    (hy : hessenbergSqOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) (k + 1)
        *ᵥ y = fun i : Fin (k + 1) => inner ℝ
          (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (i : ℕ))
          (b - toEuclideanLin A x₀)) :
    (∀ i : Fin (k + 1), inner ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
        (b - toEuclideanLin A (x₀ + ∑ j, y j •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j)) = 0) ∧
    ∀ L U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, IsUnit L → IsUnit U →
      hessenbergSqOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) (k + 1) =
        L * U →
      y = U⁻¹ *ᵥ (L⁻¹ *ᵥ fun i : Fin (k + 1) => inner ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (i : ℕ))
        (b - toEuclideanLin A x₀)) := by
  set T := toEuclideanLin A
  set q := BiLanczos.vec T (toEuclideanLin Aᵀ) q₁ qt₁
  set qt := BiLanczos.dualVec T (toEuclideanLin Aᵀ) q₁ qt₁
  refine ⟨fun i => ?_, fun L U hL hU hLU => ?_⟩
  · have hres : b - T (x₀ + ∑ j, y j • q j) = (b - T x₀) - ∑ j, y j • T (q j) := by
      rw [map_add, map_sum]; simp only [map_smul]; abel
    have hsum : inner ℝ (qt i) (∑ j, y j • T (q j)) =
        (hessenbergSqOf (BiLanczos.coeff T (toEuclideanLin Aᵀ) q₁ qt₁) (k + 1) *ᵥ y) i := by
      rw [inner_sum]
      simp only [inner_smul_right, mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [BiLanczos.inner_dualVec_apply_vec h (by omega) (by omega), mul_comm]
    rw [hres, inner_sub_right, hsum, hy, sub_self]
  · have hLd := (Matrix.isUnit_iff_isUnit_det L).mp hL
    have hUd := (Matrix.isUnit_iff_isUnit_det U).mp hU
    rw [← hy, mulVec_mulVec, mulVec_mulVec, hLU, Matrix.mul_assoc, ← Matrix.mul_assoc L⁻¹,
      nonsing_inv_mul L hLd, Matrix.one_mul, nonsing_inv_mul U hUd, one_mulVec]

/-! ### Figure 11.4.1 as programs -/

/-- The state of the BiCG column of Figure 11.4.1: the iterate `x_c`, the residual `r_c`, the
shadow residual `r̃_c`, and the two directions `p_c`, `p̃_c`. -/
structure BiCGState (n : ℕ) where
  /-- The iterate `x_c`. -/
  x : Fin n → ℝ
  /-- The residual `r_c`. -/
  r : Fin n → ℝ
  /-- The shadow residual `r̃_c`. -/
  rt : Fin n → ℝ
  /-- The direction `p_c`. -/
  p : Fin n → ℝ
  /-- The shadow direction `p̃_c`. -/
  pt : Fin n → ℝ

/-- The state of the CGS column of Figure 11.4.1: `x_c`, `r_c`, `u_c`, `p_c`. -/
structure CGSState (n : ℕ) where
  /-- The iterate `x_c`. -/
  x : Fin n → ℝ
  /-- The residual `r_c`. -/
  r : Fin n → ℝ
  /-- The auxiliary vector `u_c`. -/
  u : Fin n → ℝ
  /-- The direction `p_c`. -/
  p : Fin n → ℝ

/-- The state of the BiCGstab column of Figure 11.4.1: `x_c`, `r_c`, `p_c`. -/
structure BiCGstabState (n : ℕ) where
  /-- The iterate `x_c`. -/
  x : Fin n → ℝ
  /-- The residual `r_c`. -/
  r : Fin n → ℝ
  /-- The direction `p_c`. -/
  p : Fin n → ℝ

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the BiCG update formulae of Figure 11.4.1:
```
μ = r̃_cᵀr_c / p̃_cᵀAp_c,   x₊ = x_c + μp_c,   r₊ = r_c − μAp_c,   r̃₊ = r̃_c − μAᵀp̃_c,
τ = r̃₊ᵀr₊ / r̃_cᵀr_c,      p₊ = r₊ + τp_c,    p̃₊ = r̃₊ + τp̃_c
```
The products with `A` and `Aᵀ` are gaxpys onto `0` (Algorithm 1.1.3), the inner products
Algorithm 1.1.1, the updates saxpys (Algorithm 1.1.2), the quotients rounded. -/
noncomputable def bicgStep (A : Matrix (Fin n) (Fin n) ℝ) (s : BiCGState n) :
    M (BiCGState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A s.p 0
  let Atpt ← Chapter01.algorithm_1_1_3 rnd Aᵀ s.pt 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd s.rt s.r
  let σ ← Chapter01.algorithm_1_1_1 rnd s.pt Ap
  let μ ← rnd (ρ / σ)
  let x ← Chapter01.algorithm_1_1_2 rnd μ s.p s.x
  let r ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
  let rt ← Chapter01.algorithm_1_1_2 rnd (-μ) Atpt s.rt
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt r
  let τ ← rnd (ρn / ρ)
  let p ← Chapter01.algorithm_1_1_2 rnd τ s.p r
  let pt ← Chapter01.algorithm_1_1_2 rnd τ s.pt rt
  pure ⟨x, r, rt, p, pt⟩

/-- **The BiCG column of Figure 11.4.1**, run for `k` passes: "`r₀ = b − Ax₀`, `r̃₀ᵀr₀ ≠ 0`,
`x_c = x₀`, `p_c = r_c = r₀`, `p̃_c = r̃_c = r̃₀`", then `k` passes of `bicgStep`. The figure gives
no stopping test, so the number of passes `k` is the last argument; the condition `r̃₀ᵀr₀ ≠ 0` is
a hypothesis of the theorems, not a test of the program. -/
noncomputable def bicg (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    M (BiCGState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range k).foldlM (fun s _ => bicgStep rnd A s) ⟨x₀, r₀, rt₀, r₀, rt₀⟩

/-- One pass of the CGS update formulae of Figure 11.4.1:
```
μ = r̃₀ᵀr_c / r̃₀ᵀAp_c,   q_c = u_c − μAp_c,   x₊ = x_c + μ(u_c + q_c),
r₊ = r_c − μA(u_c + q_c),   τ = r̃₀ᵀr₊ / r̃₀ᵀr_c,   u₊ = r₊ + τq_c,   p₊ = u₊ + τ(q_c + τp_c)
```
-/
noncomputable def cgsStep (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ) (s : CGSState n) :
    M (CGSState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A s.p 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd rt₀ s.r
  let σ ← Chapter01.algorithm_1_1_1 rnd rt₀ Ap
  let μ ← rnd (ρ / σ)
  let q ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.u
  let uq ← Chapter01.vecAdd rnd s.u q
  let Auq ← Chapter01.algorithm_1_1_3 rnd A uq 0
  let x ← Chapter01.algorithm_1_1_2 rnd μ uq s.x
  let r ← Chapter01.algorithm_1_1_2 rnd (-μ) Auq s.r
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt₀ r
  let τ ← rnd (ρn / ρ)
  let u ← Chapter01.algorithm_1_1_2 rnd τ q r
  let w ← Chapter01.algorithm_1_1_2 rnd τ s.p q
  let p ← Chapter01.algorithm_1_1_2 rnd τ w u
  pure ⟨x, r, u, p⟩

/-- **The CGS column of Figure 11.4.1**, run for `k` passes: "`r₀ = b − Ax₀`, `x_c = x₀`,
`p_c = r_c = r₀`, `u_c = r_c`", then `k` passes of `cgsStep`. Only products with `A` occur. The
printed initial condition `r̃₀ᵀr̃₀ ≠ 0` should be `r̃₀ᵀr₀ ≠ 0`. -/
noncomputable def cgs (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    M (CGSState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range k).foldlM (fun s _ => cgsStep rnd A rt₀ s) ⟨x₀, r₀, r₀, r₀⟩

/-- One pass of the BiCGstab update formulae of Figure 11.4.1:
```
μ = r̃₀ᵀr_c / r̃₀ᵀAp_c,   s_c = r_c − μAp_c,   ω = s_cᵀAs_c / (As_c)ᵀ(As_c),
x₊ = x_c + μp_c + ωs_c,   r₊ = s_c − ωAs_c,   τ = (r̃₀ᵀr₊)μ / ((r̃₀ᵀr_c)ω),
p₊ = r₊ + τ(p_c − ωAp_c)
```
(the inner product `s_cᵀAs_c` is accumulated as `(As_c)ᵀs_c`, the same products). -/
noncomputable def bicgstabStep (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (st : BiCGstabState n) : M (BiCGstabState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A st.p 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd rt₀ st.r
  let σ ← Chapter01.algorithm_1_1_1 rnd rt₀ Ap
  let μ ← rnd (ρ / σ)
  let s ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap st.r
  let As ← Chapter01.algorithm_1_1_3 rnd A s 0
  let η ← Chapter01.algorithm_1_1_1 rnd As s
  let θ ← Chapter01.algorithm_1_1_1 rnd As As
  let ω ← rnd (η / θ)
  let x₁ ← Chapter01.algorithm_1_1_2 rnd μ st.p st.x
  let x ← Chapter01.algorithm_1_1_2 rnd ω s x₁
  let r ← Chapter01.algorithm_1_1_2 rnd (-ω) As s
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt₀ r
  let num ← rnd (ρn * μ)
  let den ← rnd (ρ * ω)
  let τ ← rnd (num / den)
  let w ← Chapter01.algorithm_1_1_2 rnd (-ω) Ap st.p
  let p ← Chapter01.algorithm_1_1_2 rnd τ w r
  pure ⟨x, r, p⟩

/-- **The BiCGstab column of Figure 11.4.1**, run for `k` passes: "`r₀ = b − Ax₀`, `x_c = x₀`,
`p_c = r_c = r₀`", then `k` passes of `bicgstabStep`. The printed initial condition `r̃₀ᵀr̃₀ ≠ 0`
should be `r̃₀ᵀr₀ ≠ 0`. -/
noncomputable def bicgstab (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    M (BiCGstabState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range k).foldlM (fun s _ => bicgstabStep rnd A rt₀ s) ⟨x₀, r₀, r₀⟩

end Programs

/-! #### Exact semantics: the backbone iterations -/

/-- A BiCG state read as a backbone `BCG.State` on `EuclideanSpace ℝ (Fin n)`. -/
def BiCGState.toState (s : BiCGState n) : BCG.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.rt, WithLp.toLp 2 s.p, WithLp.toLp 2 s.pt⟩

/-- A CGS state read as a backbone `CGS.State`. -/
def CGSState.toState (s : CGSState n) : CGS.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.u, WithLp.toLp 2 s.p⟩

/-- A BiCGstab state read as a backbone `BiCGSTAB.State`. -/
def BiCGstabState.toState (s : BiCGstabState n) :
    BiCGSTAB.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.p⟩

/-- The exact BiCG pass is the backbone `BCG.step` for `A` and its adjoint `Aᵀ`. -/
private theorem bicgStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (s : BiCGState n) :
    (Id.run (bicgStep pure A s)).toState =
      BCG.step (toEuclideanLin A) (toEuclideanLin Aᵀ) s.toState := by
  simp only [bicgStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, zero_add]
  simp only [BiCGState.toState, BCG.step, BCG.stepAlpha, starRingEnd_real, RingHom.id_apply,
    ← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp,
    neg_smul, ← sub_eq_add_neg]

/-- The exact CGS pass is the backbone `CGS.step`. -/
private theorem cgsStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (s : CGSState n) :
    (Id.run (cgsStep pure A rt₀ s)).toState =
      CGS.step (toEuclideanLin A) (WithLp.toLp 2 rt₀) s.toState := by
  simp only [cgsStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, Chapter01.vecAdd_spec,
    zero_add]
  simp only [CGSState.toState, CGS.step, ← WithLp.toLp_add, ← WithLp.toLp_smul,
    ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp, neg_smul, ← sub_eq_add_neg]

/-- The exact BiCGstab pass is the backbone `BiCGSTAB.step`. -/
private theorem bicgstabStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (s : BiCGstabState n) :
    (Id.run (bicgstabStep pure A rt₀ s)).toState =
      BiCGSTAB.step (toEuclideanLin A) (WithLp.toLp 2 rt₀) s.toState := by
  simp only [bicgstabStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, zero_add]
  simp only [BiCGstabState.toState, BiCGSTAB.step, ← WithLp.toLp_add, ← WithLp.toLp_smul,
    ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp, neg_smul, ← sub_eq_add_neg,
    div_mul_div_comm]

/-- The exact initialization `r₀ = b − Ax₀`. -/
private theorem residual_init_exact (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (Chapter01.vecSub pure b (Id.run (Chapter01.algorithm_1_1_3 pure A x₀ 0))) =
      b - A *ᵥ x₀ := by
  rw [Chapter01.algorithm_1_1_3_spec, zero_add, Chapter01.vecSub_spec]

/-- **Figure 11.4.1, BiCG, in exact arithmetic.** The exact run of `bicg` is the backbone's
biconjugate gradient iteration `BCG.iterate` (the same recurrence, [saad2003iterative] Algorithm
7.3) for `A` and its adjoint `Aᵀ`; hence, as long as BiCG does not break down through step `m`
(`BCG.NoBreakdown`), its residuals are biorthogonal, `r̃_jᵀr_i = 0`, its directions are
`A`-biconjugate, `p̃_jᵀAp_i = 0` (`i ≠ j ≤ m`), and its `m`-th iterate is the Petrov–Galerkin
iterate
of `bicg_residual_orthogonal`: `x_m ∈ x₀ + 𝒦(A, r₀, m)` with residual orthogonal to
`𝒦(Aᵀ, r̃₀, m)`. -/
theorem bicg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) :
    (∀ k, (Id.run (bicg pure A b x₀ rt₀ k)).toState =
      BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k) ∧
    ∀ m, BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) m →
      (∀ i j, i ≤ m → j ≤ m → i ≠ j →
        (Id.run (bicg pure A b x₀ rt₀ j)).rt ⬝ᵥ (Id.run (bicg pure A b x₀ rt₀ i)).r = 0 ∧
        (Id.run (bicg pure A b x₀ rt₀ j)).pt ⬝ᵥ (A *ᵥ (Id.run (bicg pure A b x₀ rt₀ i)).p) = 0) ∧
      IsPetrovGalerkin (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (Krylov.subspace (toEuclideanLin A) (WithLp.toLp 2 (b - A *ᵥ x₀)) m)
        (Krylov.subspace (toEuclideanLin Aᵀ) (WithLp.toLp 2 rt₀) m)
        (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ m)).x) := by
  have hspec : ∀ k, (Id.run (bicg pure A b x₀ rt₀ k)).toState =
      BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k := by
    intro k
    have h := foldlM_range_transport (bicgStep pure A)
      (BCG.step (toEuclideanLin A) (toEuclideanLin Aᵀ)) BiCGState.toState (bicgStep_exact A) k
    simp only [bicg, Id.run_bind, residual_init_exact, h]
    simp only [BCG.iterate, BiCGState.toState, WithLp.toLp_sub, toEuclideanLin_toLp]
  refine ⟨hspec, fun m hm => ⟨fun i j hi hj hij => ⟨?_, ?_⟩, ?_⟩⟩
  · have h := BCG.inner_residual_dualResidual_eq_zero hm hi hj hij
    rw [BCG.dualResidual, BCG.residual, ← hspec, ← hspec] at h
    simpa only [BiCGState.toState, inner_toLp, dotProduct_comm] using h
  · have h := BCG.inner_dualDirection_apply_direction_eq_zero hm hi hj hij
    rw [BCG.dualDirection, BCG.direction, ← hspec, ← hspec] at h
    simpa only [BiCGState.toState, toEuclideanLin_toLp, inner_toLp, dotProduct_comm] using h
  · have h := BCG.isPetrovGalerkin hm
    rw [← hspec] at h
    simpa only [WithLp.toLp_sub, toEuclideanLin_toLp, BiCGState.toState] using h

/-- For `Aᵀ = A` and the shadow residual `r̃₀ = r₀`, the biconjugate gradient iteration is the
conjugate gradient iteration with the shadow sequences equal to the primal ones (backbone form, any
real inner product space, `B = A`). -/
private theorem bcg_iterate_self_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (b x₀ : E) (k : ℕ) :
    BCG.iterate T T b x₀ (b - T x₀) k =
      ⟨(CG.iterate T b x₀ k).x, (CG.iterate T b x₀ k).r, (CG.iterate T b x₀ k).r,
        (CG.iterate T b x₀ k).p, (CG.iterate T b x₀ k).p⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BCG.iterate_succ, ih, CG.iterate_succ]
    set c := CG.iterate T b x₀ k
    have hα : BCG.stepAlpha T ⟨c.x, c.r, c.r, c.p, c.p⟩ = CG.alpha T c := by
      simp only [BCG.stepAlpha, CG.alpha]
      rw [real_inner_comm (T c.p) c.p]
    simp only [BCG.step, CG.step, hα, starRingEnd_real, RingHom.id_apply]

/-- **§11.4.5: "BiCG collapses to CG if `A` is symmetric positive definite and `r̃₀ = r₀`."** For
symmetric `A` and `r̃₀ = r₀ = b − Ax₀` the exact run of `bicg` has `r̃_k = r_k`, `p̃_k = p_k`, and
its `x_k`, `r_k`, `p_k` are those of the conjugate gradient iteration `CG.iterate` — the iteration
Algorithm 11.3.3 computes. (Positive definiteness is not needed for the identity of the
recurrences; it is what makes CG well defined.) -/
theorem bicg_eq_cg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (b x₀ : Fin n → ℝ) (k : ℕ) :
    WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).x =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).x ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).r =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).r ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).p =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).p ∧
      (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).rt =
        (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).r ∧
      (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).pt =
        (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).p := by
  have h := (bicg_spec A b x₀ (b - A *ᵥ x₀)).1 k
  have hT : Aᵀ = A := hA
  have hr₀ : (WithLp.toLp 2 (b - A *ᵥ x₀) : EuclideanSpace ℝ (Fin n)) =
      WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀) := by
    rw [WithLp.toLp_sub, toEuclideanLin_toLp]
  rw [hT, hr₀, bcg_iterate_self_eq] at h
  have hx := congrArg BCG.State.x h
  have hr := congrArg BCG.State.r h
  have hrs := congrArg BCG.State.rs h
  have hp := congrArg BCG.State.p h
  have hps := congrArg BCG.State.ps h
  simp only [BiCGState.toState] at hx hr hrs hp hps
  exact ⟨hx, hr, hp, WithLp.toLp_injective 2 (hrs.trans hr.symm),
    WithLp.toLp_injective 2 (hps.trans hp.symm)⟩

/-- **(11.4.14).** "After `k` steps of the procedure we have degree-`k` polynomials `ψ_k` and `φ_k`
so that `r_k = ψ_k(A)r₀`, `p_k = φ_k(A)r₀`, `r̃_k = ψ_k(Aᵀ)r̃₀`, `p̃_k = φ_k(Aᵀ)r̃₀` and
`ψ_k(0) = 1`." For the exact BiCG run the polynomials are the backbone's `BCG.residualPoly` and
`BCG.directionPoly` (the recurrences `ψ_{k+1} = ψ_k − μ_k Xφ_k`, `φ_{k+1} = ψ_{k+1} + τ_kφ_k`), of
degree at most `k`. The printed "`φ_k(0) = 1`" is false (`φ₁(0) = 1 + τ₀`) and is not part of the
statement. -/
theorem equation_11_4_14 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).r =
        aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).p =
        aeval (toEuclideanLin A) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).rt =
        aeval (toEuclideanLin Aᵀ) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k) (WithLp.toLp 2 rt₀) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).pt =
        aeval (toEuclideanLin Aᵀ) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k) (WithLp.toLp 2 rt₀) ∧
      (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).eval 0 = 1 ∧
      (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).natDegree ≤ k ∧
      (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).natDegree ≤ k := by
  obtain ⟨h1, h2, h3, h4⟩ := BCG.residual_eq_aeval (toEuclideanLin A) (toEuclideanLin Aᵀ)
    (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k
  rw [map_starRingEnd_real] at h3 h4
  have hs := (bicg_spec A b x₀ rt₀).1 k
  refine ⟨?_, ?_, ?_, ?_, BCG.residualPoly_eval_zero _ _ _ _ _ k,
    BCG.residualPoly_natDegree_le _ _ _ _ _ k, BCG.directionPoly_natDegree_le _ _ _ _ _ k⟩
  · rw [← h1, BCG.residual, ← hs]; rfl
  · rw [← h2, BCG.direction, ← hs]; rfl
  · rw [← h3, BCG.dualResidual, ← hs]; rfl
  · rw [← h4, BCG.dualDirection, ← hs]; rfl

/-- `p(T)` commutes with `T`. -/
private theorem aeval_apply_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ[ℝ] E) (p : ℝ[X]) (v : E) : aeval T p (T v) = T (aeval T p v) := by
  have hmul : aeval T (p * X) = aeval T (X * p) := by rw [mul_comm]
  have := congrArg (fun f : E →ₗ[ℝ] E => f v) hmul
  simpa only [map_mul, aeval_X, Module.End.mul_apply] using this

/-- **§11.4.5, the transpose-free scalars.** "This enables us to characterize expressions like
`r̃_kᵀr_k` and `p̃_kᵀAp_k` in a way that involves only `A`-times-vector:
`r̃_kᵀr_k = r̃₀ᵀ(ψ_k²(A)r₀)`, `p̃_kᵀAp_k = r̃₀ᵀ(Aφ_k²(A)r₀)`." For the exact BiCG run, moving the
polynomial in `Aᵀ` across the inner product (`BiLanczos.inner_aeval_map_eq`). -/
theorem bicg_inner_eq_poly (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    inner ℝ (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).rt : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).r) =
      inner ℝ (WithLp.toLp 2 rt₀ : EuclideanSpace ℝ (Fin n))
        (aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) ∧
    inner ℝ (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).pt : EuclideanSpace ℝ (Fin n))
        (toEuclideanLin A (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).p)) =
      inner ℝ (WithLp.toLp 2 rt₀ : EuclideanSpace ℝ (Fin n))
        (toEuclideanLin A (aeval (toEuclideanLin A)
          (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
            (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)))) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := equation_11_4_14 A b x₀ rt₀ k
  have hB : ∀ x y : EuclideanSpace ℝ (Fin n),
      inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) :=
    inner_toEuclideanLin_transpose A
  set T := toEuclideanLin A
  set ψ := BCG.residualPoly T (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    (WithLp.toLp 2 rt₀) k
  set φ := BCG.directionPoly T (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    (WithLp.toLp 2 rt₀) k
  set r₀ := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
  have hsq : ∀ (q : ℝ[X]) (v : EuclideanSpace ℝ (Fin n)), aeval T (q ^ 2) v =
      aeval T q (aeval T q v) := fun q v => by
    rw [sq, map_mul]; rfl
  refine ⟨?_, ?_⟩
  · have key := BiLanczos.inner_aeval_map_eq hB ψ (WithLp.toLp 2 rt₀) (aeval T ψ r₀)
    rw [map_starRingEnd_real] at key
    rw [h3, h1, key, hsq]
  · have key := BiLanczos.inner_aeval_map_eq hB φ (WithLp.toLp 2 rt₀) (T (aeval T φ r₀))
    rw [map_starRingEnd_real] at key
    rw [h4, h2, key, hsq, aeval_apply_apply]

/-- **§11.4.5, CGS (Sonneveld).** "It produces iterates `x_k` whose residuals `r_k` satisfy
`r_k = ψ_k(A)²r₀`" with `ψ_k` the BiCG residual polynomial of (11.4.14), and likewise
`p_k = φ_k(A)²r₀`, using only products with `A`. The exact run of `cgs` is the backbone's
`CGS.iterate` (Saad's Algorithm 7.6, line by line the same), and the polynomial identities are
`CGS.residual_eq_aeval_sq`; no breakdown hypothesis is needed. -/
theorem cgs_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    (Id.run (cgs pure A b x₀ rt₀ k)).toState =
        CGS.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ∧
      WithLp.toLp 2 (Id.run (cgs pure A b x₀ rt₀ k)).r =
        aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (cgs pure A b x₀ rt₀ k)).p =
        aeval (toEuclideanLin A) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) := by
  have hs : (Id.run (cgs pure A b x₀ rt₀ k)).toState =
      CGS.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k := by
    have h := foldlM_range_transport (cgsStep pure A rt₀)
      (CGS.step (toEuclideanLin A) (WithLp.toLp 2 rt₀)) CGSState.toState (cgsStep_exact A rt₀) k
    simp only [cgs, Id.run_bind, residual_init_exact, h]
    simp only [CGS.iterate, CGSState.toState, WithLp.toLp_sub, toEuclideanLin_toLp]
  obtain ⟨h1, h2, -⟩ := CGS.residual_eq_aeval_sq (inner_toEuclideanLin_transpose A) k
    (b := WithLp.toLp 2 b) (x₀ := WithLp.toLp 2 x₀) (rs₀ := WithLp.toLp 2 rt₀)
  exact ⟨hs, by rw [← h1, ← hs]; rfl, by rw [← h2, ← hs]; rfl⟩

/-- **§11.4.5, BiCGstab (van der Vorst).** "It … produces iterates `x_k` whose residuals satisfy
`r_k = (1 − ω_kA)⋯(1 − ω₁A)ψ_k(A)r₀` where `ψ_k` is the BiCG residual polynomial defined in
(11.4.14). The parameter `ω_k` is chosen in step `k` to minimize `‖r_k‖₂` given `ω₁, …, ω_{k−1}` and
the vector `ψ_k(A)r₀`." The exact run of `bicgstab` is the backbone's `BiCGSTAB.iterate` (Saad's
Algorithm 7.7); the residual identity holds when BiCG does not break down and no `ω_j` vanishes
(`BiCGSTAB.residual_eq`; the product of the `(1 − ω_jA)` is `BiCGSTAB.stabPoly`); and each `ω_k`
minimizes `‖s_k − ωAs_k‖₂` over `ω` ([the book's P11.4.2]; the one-dimensional minimal-residual
step `Projection.minResStep`). -/
theorem bicgstab_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    (Id.run (bicgstab pure A b x₀ rt₀ k)).toState =
        BiCGSTAB.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
          (WithLp.toLp 2 rt₀) k ∧
      (BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k →
        (∀ i < k, BiCGSTAB.omega (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
          (WithLp.toLp 2 rt₀) i ≠ 0) →
        WithLp.toLp 2 (Id.run (bicgstab pure A b x₀ rt₀ k)).r =
          aeval (toEuclideanLin A) (BiCGSTAB.stabPoly (toEuclideanLin A) (WithLp.toLp 2 b)
            (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k *
              BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
                (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
            (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) ∧
      ∀ ω : ℝ,
        ‖BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k -
            BiCGSTAB.omega (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
              (WithLp.toLp 2 rt₀) k •
              toEuclideanLin A (BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b)
                (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)‖ ≤
          ‖BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
              (WithLp.toLp 2 rt₀) k -
            ω • toEuclideanLin A (BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b)
              (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)‖ := by
  set T := toEuclideanLin A
  set b' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  set x₀' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x₀
  set rt₀' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 rt₀
  have hs : (Id.run (bicgstab pure A b x₀ rt₀ k)).toState = BiCGSTAB.iterate T b' x₀' rt₀' k := by
    have h := foldlM_range_transport (bicgstabStep pure A rt₀) (BiCGSTAB.step T rt₀')
      BiCGstabState.toState (bicgstabStep_exact A rt₀) k
    simp only [bicgstab, Id.run_bind, residual_init_exact, h]
    simp only [BiCGSTAB.iterate, BiCGstabState.toState, WithLp.toLp_sub, toEuclideanLin_toLp,
      b', x₀', T]
  refine ⟨hs, fun hbd hω => ?_, fun ω => ?_⟩
  · have h := (BiCGSTAB.residual_eq (B := toEuclideanLin Aᵀ) hbd hω le_rfl).1
    rw [← h, ← hs]
    rfl
  · set z := (BiCGSTAB.iterate T b' x₀' rt₀' k).x +
      BiCGSTAB.alpha T b' x₀' rt₀' k • (BiCGSTAB.iterate T b' x₀' rt₀' k).p
    set s := BiCGSTAB.s T b' x₀' rt₀' k
    have hz : b' - T z = s := by
      simp only [z, s, BiCGSTAB.s, BiCGSTAB.r_eq_sub_apply_x, map_add, map_smul]
      abel
    have hmin := Projection.minResStep_isMinResidual (A := T) (b := b') z
    have h1 := hmin.min (z + ω • s) (by
      rw [add_sub_cancel_left, hz]
      exact Submodule.smul_mem _ ω (Submodule.mem_span_singleton_self s))
    rw [← BiCGSTAB.iterate_succ_x_eq_minResStep, ← BiCGSTAB.r_eq_sub_apply_x,
      BiCGSTAB.iterate_succ_r, map_add, map_smul,
      show b' - (T z + ω • T s) = (b' - T z) - ω • T s by abel, hz] at h1
    exact h1

/-- **§11.4.5, QMR.** "As in BiCG, the `k`th iterate has the form `x_k = x₀ + Q_ky_k` … This
equation can be rewritten as `AQ_k = Q_{k+1}T̃_k` where `T̃_k ∈ ℝ^{(k+1)×k}` is tridiagonal. It
follows that if `q₁ = r₀/β₀` … then `b − A(x₀ + Q_ky) = Q_{k+1}(β₀e₁ − T̃_ky)`. In QMR, `y` is
chosen to minimize `‖β₀e₁ − T̃_ky‖₂`." The residual identity holds under
`BiLanczos.NoSeriousBreakdown` (`Krylov.HessenbergRelation₂.residual_eq` for
`BiLanczos.hessenbergRelation`), and the QMR iterate is the backbone's `QMR.IsQuasiMinResidual`,
which is literally the minimization the book describes. -/
theorem qmr_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) {b x₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)}
    {β₀ : ℝ} (h : BiLanczos.NoSeriousBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁)
    (hr : b - toEuclideanLin A x₀ = β₀ • q₁) (k : ℕ) :
    (∀ y : Fin k → ℝ, b - toEuclideanLin A
        (x₀ + ∑ j, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      ∑ i : Fin (k + 1), (firstVec β₀ (k + 1) -
        hessenbergOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) k *ᵥ y) i •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i) ∧
    ∀ x, QMR.IsQuasiMinResidual (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ β₀ x₀ k x ↔
      ∃ y : Fin k → ℝ,
        x = x₀ + ∑ j, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j ∧
        IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
          hessenbergOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) k *ᵥ z) :
            EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ y :=
  ⟨fun y => (BiLanczos.hessenbergRelation h).residual_eq hr k y, fun _ => Iff.rfl⟩

/-- **§11.4.5: "GMRES minimizes the same quantity because `Q_{k+1}` has orthonormal columns in
Arnoldi."** When the basis is the Arnoldi basis (orthonormal) and `k` is at most the grade, the
quasi-minimal-residual iterate — `y` minimizing `‖β₀e₁ − H̃_ky‖₂` — is exactly the
minimal-residual (GMRES) iterate. -/
theorem qmr_eq_gmres_of_orthonormal (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (x : EuclideanSpace ℝ (Fin n)) :
    IsQuasiMinResidualIterate (Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀))
        (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) ‖b - toEuclideanLin A x₀‖
        x₀ k x ↔
      IsMinResidualIterate (toEuclideanLin A) b x₀ k x :=
  isQuasiMinResidualIterate_iff_isMinResidualIterate hk x

end GolubVanLoan.Chapter11
