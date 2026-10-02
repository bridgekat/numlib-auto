import Numlib.Krylov.Bidiagonalization
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.TransposeFree
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter10.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section05

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
and the update formulae, with no stopping test, so each program runs `fuel` passes of the update
(`fuel` its last argument). Their exact semantics (`M := Id`, `rnd := pure`) is the backbone
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
* `equation_11_4_6`, `lsqr_span_eq`, `equation_11_4_7` — LSQR: the lower bidiagonalization
  `A V_k = U_{k+1} B̃_k`, whose right vectors span `𝒦(AᵀA, Aᵀr₀, k)`, reduces the LSQR iterate to
  the bidiagonal least squares problem `min ‖B̃_k y − β₀e₁‖₂`.
* `IsLSMRIterate`, `lsmr_norm_residual_antitone` — LSMR and its monotone residuals.
* `equation_11_4_8`, `gmres_reduction`, `equation_11_4_9`, `equation_11_4_10`,
  `gmres_givens_prefix` — GMRES.
* `algorithm_11_4_2`, `algorithm_11_4_2_spec` — `m`-step GMRES as a program (the Arnoldi pass of
  chapter 10's Algorithm 10.5.1, chapter 5's `givens` and row rotations, chapter 3's back
  substitution), whose exact run is the minimal-residual iterate; its loop `gmresCore` takes the
  operator as a routine (`gmresCore_spec`), which Algorithm 11.5.2 reuses with `M`-solves.
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
and the Notes and References. There is no Algorithm 11.4.1 in the source: §11.4.1 describes MINRES
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
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) :=
  (toEuclideanLin_transpose_inner_right A x y).symm

/-- The real inner product of two transported vectors is their dot product. -/
private theorem inner_toLp (u v : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) = u ⬝ᵥ v :=
  EuclideanSpace.inner_toLp_toLp_real u v

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
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) :=
  (toEuclideanLin_transpose_inner_right A x y).symm

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
right vectors is the Krylov subspace of the normal equations: (10.4.12) for `Aᵀ`
(`Chapter10.equation_10_4_12`), and the invariance of a Krylov subspace under scaling of its
starting vector. -/
theorem lsqr_span_eq (A : Matrix (Fin m) (Fin n) ℝ) {r₀ u₁ : EuclideanSpace ℝ (Fin m)} {β₀ : ℝ}
    (hβ : β₀ ≠ 0) (hr : r₀ = β₀ • u₁) (k : ℕ) :
    Submodule.span ℝ (GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (Aᵀ * A)) (toEuclideanLin Aᵀ r₀) k := by
  have h := GolubVanLoan.Chapter10.equation_10_4_12 Aᵀ u₁ k
  rw [transpose_transpose] at h
  rw [h, toEuclideanLin_mul, hr, map_smul]
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
definite system is nonincreasing). The book needs no rank assumption; the general case runs the
same energy argument on `ran Aᵀ`, where `AᵀA` is positive definite, and is not formalized here
(the full-rank hypothesis is a deliberate restriction). -/
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

/-! #### Algorithm 11.4.2 -/

/-- The state of Algorithm 11.4.2 (`m`-step GMRES): the state of the Arnoldi loop of
Algorithm 10.5.1 (the step count `k`, the vectors `q_j`, the Hessenberg entries `h_ij`, the residual
`r_k`, the `done` flag of `β_k > 0`), the rotated Hessenberg matrix `[R_k; 0]` (columns `0, …, k−1`
filled, the others zero), the rotated right-hand side `[p_k; ρ_k]` and the rotations `(c_j, s_j)`
determined so far. -/
structure GMRESState (n m : ℕ) where
  /-- The state of the Arnoldi loop. -/
  arnoldi : GolubVanLoan.Chapter10.ArnoldiState n
  /-- The rotated Hessenberg matrix `G_kᵀ ⋯ G_1ᵀ H̃_k`, padded with zero columns. -/
  R : Matrix (Fin (m + 1)) (Fin m) ℝ
  /-- The rotated right-hand side `G_kᵀ ⋯ G_1ᵀ (β₀ e₁)`. -/
  g : Fin (m + 1) → ℝ
  /-- The rotations: `G_{j+1}` acts in the plane `(j, j+1)` with `(c, s) = cs j`. -/
  cs : Fin m → ℝ × ℝ

section GMRES

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}

/-- A pass of the Arnoldi loop of Algorithm 10.5.1 with the product `A q_k` replaced by a routine
`op` (a no-op once `done`): `q_{k+1} = r_k/h_{k+1,k}`, `k = k + 1`, `r_k = op(q_k)`, the modified
Gram–Schmidt loop (chapter 10's `mgsLoop`, the book's (11.4.11)), `h_{k+1,k} = ‖r_k‖₂`. With
`op q = Aq` (chapter 1's gaxpy) it is chapter 10's `arnoldiStep` (`arnoldiStepOp_gaxpy`, by
definition); with `op q = M⁻¹(Aq)` it is the pass of the preconditioned GMRES of §11.5. -/
noncomputable def arnoldiStepOp (op : (Fin n → ℝ) → M (Fin n → ℝ))
    (s : GolubVanLoan.Chapter10.ArnoldiState n) : M (GolubVanLoan.Chapter10.ArnoldiState n) :=
  if s.done then pure s else do
    let hk : ℝ := if s.k = 0 then 1 else s.h s.k (s.k - 1)
    let qk ← GolubVanLoan.Chapter10.vecDiv rnd s.r hk
    let q := Function.update s.q s.k qk
    let v ← op qk
    let vh ← GolubVanLoan.Chapter10.mgsLoop rnd q (s.k + 1) v
    let b ← GolubVanLoan.Chapter10.vecNorm rnd vh.1
    pure
      { k := s.k + 1
        q := q
        h := fun i j => if j = s.k then (if i = s.k + 1 then b else vh.2 i) else s.h i j
        r := vh.1
        done := decide (b = 0) }

/-- With the gaxpy as its routine, `arnoldiStepOp` is chapter 10's pass of Algorithm 10.5.1. -/
theorem arnoldiStepOp_gaxpy (A : Matrix (Fin n) (Fin n) ℝ)
    (s : GolubVanLoan.Chapter10.ArnoldiState n) :
    arnoldiStepOp rnd (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0) s =
      GolubVanLoan.Chapter10.arnoldiStep rnd A s := rfl

/-- One pass `j` (`0 ≤ j < m`) of the `while` loop of Algorithm 11.4.2 (a no-op once `β_k = 0`):
the Arnoldi pass (`arnoldiStepOp`), then the new column `H(1:k+1, k)` is copied into the rotated
matrix, `G_1, …, G_{k−1}` are applied to it, `G_k` is determined by chapter 5's `givens`
(Algorithm 5.1.3) from `(r_kk, h_{k+1,k})` and applied to the column and to the right-hand side
(chapter 5's `givensApplyLeft`, `givensRotateVec`). -/
noncomputable def gmresStep (op : (Fin n → ℝ) → M (Fin n → ℝ)) (s : GMRESState n m) (j : Fin m) :
    M (GMRESState n m) :=
  if s.arnoldi.done then pure s else do
    let L ← arnoldiStepOp rnd op s.arnoldi
    let R₀ := s.R.updateCol j fun i => if (i : ℕ) ≤ j + 1 then L.h i j else 0
    let R₁ ← ((List.finRange m).filter (· < j)).foldlM
      (fun (R : Matrix (Fin (m + 1)) (Fin m) ℝ) (i : Fin m) =>
        GolubVanLoan.Chapter05.givensApplyLeft rnd i.castSucc i.succ (s.cs i).1 (s.cs i).2 [j] R)
      R₀
    let c ← GolubVanLoan.Chapter05.algorithm_5_1_3 rnd (R₁ j.castSucc j) (R₁ j.succ j)
    let R₂ ← GolubVanLoan.Chapter05.givensApplyLeft rnd j.castSucc j.succ c.1 c.2 [j] R₁
    let g ← GolubVanLoan.Chapter05.givensRotateVec rnd j.castSucc j.succ c.1 c.2 s.g
    pure ⟨L, R₂, g, Function.update s.cs j c⟩

/-- The body of the `m`-step GMRES programs from the initial residual `z₀` (`r₀` for
Algorithm 11.4.2, `M⁻¹r₀` for Algorithm 11.5.2) and the operator routine `op`: `β₀ = ‖z₀‖₂`,
`q₁ = z₀/β₀`, the `m` passes `gmresStep`, then `R_k y_k = p_k` by chapter 3's back substitution
(Algorithm 3.1.2) on the leading `k × k` block of the rotated matrix, and `x̃ = x₀ + Q_k y_k` by
chapter 1's gaxpy. Returns the final state and `x̃`. -/
noncomputable def gmresCore (op : (Fin n → ℝ) → M (Fin n → ℝ)) (x₀ z₀ : Fin n → ℝ) (m : ℕ) :
    M (GMRESState n m × (Fin n → ℝ)) := do
  let β₀ ← GolubVanLoan.Chapter10.vecNorm rnd z₀
  let q₁ ← GolubVanLoan.Chapter10.vecDiv rnd z₀ β₀
  let s ← (List.finRange m).foldlM (gmresStep rnd op)
    ⟨⟨0, fun _ => 0, fun _ _ => 0, q₁, decide (β₀ = 0)⟩, 0, Krylov.firstVec β₀ (m + 1),
      fun _ => (1, 0)⟩
  if h : s.arnoldi.k ≤ m then do
    let y ← GolubVanLoan.Chapter03.algorithm_3_1_2 rnd
      (s.R.submatrix (Fin.castLE (Nat.le_succ_of_le h)) (Fin.castLE h))
      (fun i => s.g (Fin.castLE (Nat.le_succ_of_le h) i))
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd
      (of fun i (l : Fin s.arnoldi.k) => s.arnoldi.q l i) y x₀
    pure (s, x)
  else pure (s, x₀)

/-- **Algorithm 11.4.2 (`m`-step GMRES).** "If `A ∈ ℝ^{n×n}` is nonsingular, `b ∈ ℝⁿ`,
`Ax₀ ≈ b`, and `m` is a positive iteration limit, then this algorithm computes `x̃ ∈ ℝⁿ` where
either `x̃` solves `Ax = b` or minimizes `‖Ax − b‖₂` over the affine space `x₀ + 𝒦(A, r₀, m)`
where `r₀ = b − Ax₀`":
```
k = 0, r₀ = b − Ax₀, β₀ = ‖r₀‖₂
while (β_k > 0) and k < m
  q_{k+1} = r_k/β_k,  k = k + 1,  r_k = Aq_k
  for i = 1:k: h_ik = q_iᵀr_k, r_k = r_k − h_ik q_i end        (11.4.11)
  β_k = ‖r_k‖₂,  h_{k+1,k} = β_k
  apply G_1, …, G_{k−1} to H(1:k, k) and determine G_k, R_k, p_k, ρ_k
end
solve R_k y_k = p_k and set x̃ = x₀ + Q_k y_k
```
`r₀` by chapter 1's gaxpy, then `gmresCore` with `op q = Aq`: the loop is `m` passes of
`gmresStep` (the test `k < m` is the length of the pass list), whose Arnoldi part is chapter 10's
pass of Algorithm 10.5.1 started from `q₁ = r₀/β₀` (its first normalization divides again by its
`h_{10} = 1`: in the rounded model one rounding per entry of `q₁` more than the book's single
division, a deviation kept to reuse chapter 10's loop unchanged). Returns the final state and
`x̃`. -/
noncomputable def algorithm_11_4_2 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (m : ℕ) :
    M (GMRESState n m × (Fin n → ℝ)) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  gmresCore rnd (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0) x₀ r₀ m

end GMRES

/-! #### Algorithm 11.4.2: exact semantics -/

section GMRESSpec

variable {m : ℕ}

/-! Rotations in the planes `(i, i + 1)` and their accumulation. -/

/-- The rotation `G_{i+1}` of the GMRES programs, in the plane `(i, i+1)` of `ℝ^{m+1}`. -/
private noncomputable def gmresRot (c : ℝ × ℝ) (i : Fin m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  GolubVanLoan.Chapter05.givensRotation i.castSucc i.succ c.1 c.2

/-- `G_tᵀ ⋯ G_1ᵀ`, the accumulated transposed rotations of the first `t` planes. -/
private noncomputable def gmresW (cs : Fin m → ℝ × ℝ) : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  | 0 => 1
  | t + 1 => if h : t < m then (gmresRot (cs ⟨t, h⟩) ⟨t, h⟩)ᵀ * gmresW cs t else gmresW cs t

/-- The `j`-th Hessenberg column `H(1:j+2, j+1)` copied by a GMRES pass, padded with zeros. -/
private def gmresHcol (L : GolubVanLoan.Chapter10.ArnoldiState n) (j : Fin m) :
    Fin (m + 1) → ℝ :=
  fun a => if (a : ℕ) ≤ j + 1 then L.h a j else 0

private theorem castSucc_ne_succ (i : Fin m) : i.castSucc ≠ i.succ :=
  (Fin.castSucc_lt_succ (i := i)).ne

private theorem gmresRot_mulVec_apply (c : ℝ × ℝ) (i : Fin m) (v : Fin (m + 1) → ℝ)
    (a : Fin (m + 1)) :
    ((gmresRot c i)ᵀ *ᵥ v) a = if a = i.castSucc then c.1 * v i.castSucc - c.2 * v i.succ
      else if a = i.succ then c.2 * v i.castSucc + c.1 * v i.succ else v a :=
  GolubVanLoan.Chapter05.givensRotation_transpose_mulVec_apply (castSucc_ne_succ i) _ _ v a

/-- `G(i, i+1, θ)ᵀ` fixes a vector whose entries `i`, `i + 1` vanish. -/
private theorem gmresRot_mulVec_of_eq_zero (c : ℝ × ℝ) (i : Fin m) {v : Fin (m + 1) → ℝ}
    (h1 : v i.castSucc = 0) (h2 : v i.succ = 0) : (gmresRot c i)ᵀ *ᵥ v = v := by
  ext a
  rw [gmresRot_mulVec_apply, h1, h2]
  split_ifs with ha hb
  · rw [ha, h1]; ring
  · rw [hb, h2]; ring
  · rfl

private theorem gmresW_succ (cs : Fin m → ℝ × ℝ) {t : ℕ} (ht : t < m) :
    gmresW cs (t + 1) = (gmresRot (cs ⟨t, ht⟩) ⟨t, ht⟩)ᵀ * gmresW cs t := by
  simp only [gmresW, ht, ↓reduceDIte]

private theorem gmresW_succ_of_le (cs : Fin m → ℝ × ℝ) {t : ℕ} (ht : m ≤ t) :
    gmresW cs (t + 1) = gmresW cs t := by
  simp only [gmresW, show ¬ t < m by omega, ↓reduceDIte]

/-- The accumulated rotations depend only on the rotations below `t`. -/
private theorem gmresW_congr {cs cs' : Fin m → ℝ × ℝ} {t : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < t → cs i = cs' i) : gmresW cs t = gmresW cs' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, gmresW_succ cs' ht, ih fun i hi => h i (by omega),
        h ⟨t, ht⟩ (by simp)]
    · rw [gmresW_succ_of_le cs (by omega), gmresW_succ_of_le cs' (by omega)]
      exact ih fun i hi => h i (by omega)

/-- The accumulated rotations are orthogonal. -/
private theorem gmresW_mem {cs : Fin m → ℝ × ℝ} {t : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < t → (cs i).1 ^ 2 + (cs i).2 ^ 2 = 1) :
    gmresW cs t ∈ orthogonalGroup (Fin (m + 1)) ℝ := by
  induction t with
  | zero => exact one_mem _
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht]
      refine mul_mem ?_ (ih fun i hi => h i (by omega))
      have hG := Unitary.star_mem (GolubVanLoan.Chapter05.givensRotation_mem_orthogonalGroup
        (castSucc_ne_succ ⟨t, ht⟩) (h ⟨t, ht⟩ (by simp)))
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hG
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih fun i hi => h i (by omega)

/-- The accumulated rotations of the first `t` planes do not change the entries beyond `t`. -/
private theorem gmresW_mulVec_apply_of_lt (cs : Fin m → ℝ × ℝ) (t : ℕ) (v : Fin (m + 1) → ℝ)
    {a : Fin (m + 1)} (ha : t < a) : (gmresW cs t *ᵥ v) a = v a := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, ← mulVec_mulVec, gmresRot_mulVec_apply,
        ite_eq_right fun h => by subst h; simp at ha,
        ite_eq_right fun h => by subst h; simp at ha]
      exact ih (by omega)
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih (by omega)

/-- The accumulated rotations of the first `t` planes fix a vector vanishing on `0, …, t`. -/
private theorem gmresW_mulVec_of_eq_zero (cs : Fin m → ℝ × ℝ) (t : ℕ) {v : Fin (m + 1) → ℝ}
    (hv : ∀ i : Fin (m + 1), (i : ℕ) ≤ t → v i = 0) : gmresW cs t *ᵥ v = v := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, ← mulVec_mulVec, ih fun i hi => hv i (by omega)]
      exact gmresRot_mulVec_of_eq_zero _ _ (hv _ (by simp)) (hv _ (by simp))
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih fun i hi => hv i (by omega)

/-- The entries of the accumulated rotations beyond column `t` are those of the identity. -/
private theorem gmresW_apply_of_lt (cs : Fin m → ℝ × ℝ) (t : ℕ) (a : Fin (m + 1))
    {c : Fin (m + 1)} (hc : t < c) : gmresW cs t a c = if a = c then 1 else 0 := by
  have h := congrFun (gmresW_mulVec_of_eq_zero cs t (v := Pi.single c 1)
    fun i hi => Pi.single_eq_of_ne (by rintro rfl; omega) _) a
  rw [mulVec_single_one, col_apply, Pi.single_apply] at h
  exact h

/-! The program's rotation loops at `Id`. -/

/-- Membership in the planes below `t + 1`. -/
private theorem finRange_filter_lt_succ {t : ℕ} (ht : t < m) :
    (List.finRange m).filter (fun i : Fin m => (i : ℕ) < t + 1) =
      (List.finRange m).filter (fun i : Fin m => (i : ℕ) < t) ++ [⟨t, ht⟩] := by
  have hp := (List.sortedLT_finRange m).pairwise
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (hp.filter _) ?_ fun a => ?_
  · rw [List.pairwise_append]
    refine ⟨hp.filter _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_singleton] at ha hb
    subst hb
    exact Fin.lt_def.2 ha
  · simp only [List.mem_append, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_singleton]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Fin.ext h)
    · rintro (h | rfl)
      · omega
      · simp

/-- Applying the rotations of the planes below `t` in order is `gmresW`. -/
private theorem foldl_rot_eq (cs : Fin m → ℝ × ℝ) (v : Fin (m + 1) → ℝ) {t : ℕ} (ht : t ≤ m) :
    ((List.finRange m).filter (fun i : Fin m => (i : ℕ) < t)).foldl
      (fun v i => (gmresRot (cs i) i)ᵀ *ᵥ v) v = gmresW cs t *ᵥ v := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    rw [finRange_filter_lt_succ (by omega), List.foldl_append, ih (by omega), List.foldl_cons,
      List.foldl_nil, gmresW_succ cs (by omega), mulVec_mulVec]

/-- Chapter 5's row rotation on the single column `j`. -/
private theorem givensApplyLeft_col {p q : Fin (m + 1)} (hpq : p ≠ q) (c s : ℝ) (j : Fin m)
    (R : Matrix (Fin (m + 1)) (Fin m) ℝ) :
    Id.run (GolubVanLoan.Chapter05.givensApplyLeft pure p q c s [j] R) =
      R.updateCol j ((GolubVanLoan.Chapter05.givensRotation p q c s)ᵀ *ᵥ fun a => R a j) := by
  rw [GolubVanLoan.Chapter05.givensApplyLeft_spec hpq c s (List.nodup_singleton j)]
  ext a b
  rw [of_apply, updateCol_apply]
  by_cases hb : b = j
  · subst hb
    simp only [List.mem_singleton, ↓reduceIte]
    rfl
  · simp only [List.mem_singleton, hb, ↓reduceIte]

/-- The rotation loop of a GMRES pass on the column `j`. -/
private theorem foldlM_rot_col (cs : Fin m → ℝ × ℝ) (j : Fin m) :
    ∀ (l : List (Fin m)) (R₀ : Matrix (Fin (m + 1)) (Fin m) ℝ),
      Id.run (l.foldlM (fun (R : Matrix (Fin (m + 1)) (Fin m) ℝ) (i : Fin m) =>
          GolubVanLoan.Chapter05.givensApplyLeft pure i.castSucc i.succ (cs i).1 (cs i).2 [j] R)
          R₀) =
        R₀.updateCol j (l.foldl (fun v i => (gmresRot (cs i) i)ᵀ *ᵥ v) fun a => R₀ a j)
  | [], R₀ => by
    ext a b
    rw [List.foldlM_nil, List.foldl_nil, updateCol_apply]
    split_ifs with h
    · subst h; rfl
    · rfl
  | i :: l, R₀ => by
    rw [List.foldlM_cons, Id.run_bind, givensApplyLeft_col (castSucc_ne_succ i),
      foldlM_rot_col cs j l, List.foldl_cons]
    ext a b
    simp only [updateCol_apply, ↓reduceIte]
    split_ifs <;> rfl

/-- Exact semantics of chapter 5's vector rotation. -/
private theorem givensRotateVec_run {p q : Fin (m + 1)} (hpq : p ≠ q) (c s : ℝ)
    (x : Fin (m + 1) → ℝ) :
    Id.run (GolubVanLoan.Chapter05.givensRotateVec pure p q c s x) =
      (GolubVanLoan.Chapter05.givensRotation p q c s)ᵀ *ᵥ x := by
  ext r
  rw [GolubVanLoan.Chapter05.givensRotation_transpose_mulVec_apply hpq]
  change Function.update (Function.update x p (c * x p - s * x q)) q (s * x p + c * x q) r = _
  by_cases hrq : r = q
  · subst hrq
    rw [Function.update_self, ite_eq_right hpq.symm, ite_eq_left rfl]
  · rw [Function.update_of_ne hrq]
    by_cases hrp : r = p
    · subst hrp; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hrp, ite_eq_right hrp, ite_eq_right hrq]


/-! The exact passes. -/

/-- With exact semantics `q ↦ Bq`, the pass `arnoldiStepOp` is chapter 10's pass of
Algorithm 10.5.1 for `B`. -/
private theorem arnoldiStepOp_run {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q)
    (s : GolubVanLoan.Chapter10.ArnoldiState n) :
    Id.run (arnoldiStepOp pure op s) = Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B s) := by
  have hop' : op = fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 pure B q 0 := by
    funext q
    have h2 := GolubVanLoan.Chapter01.algorithm_1_1_3_spec B q 0
    rw [zero_add] at h2
    exact (hop q).trans h2.symm
  rw [hop']
  rfl

/-- The bookkeeping of a genuine Arnoldi pass: one more step, the earlier Hessenberg columns kept,
and `done` only when the new subdiagonal entry vanishes. -/
private theorem arnoldiStepOp_fields (op : (Fin n → ℝ) → Id (Fin n → ℝ))
    (s : GolubVanLoan.Chapter10.ArnoldiState n) (hd : s.done = false) :
    (Id.run (arnoldiStepOp pure op s)).k = s.k + 1 ∧
      (∀ i j, j ≠ s.k → (Id.run (arnoldiStepOp pure op s)).h i j = s.h i j) ∧
      ((Id.run (arnoldiStepOp pure op s)).done = true →
        (Id.run (arnoldiStepOp pure op s)).h (s.k + 1) s.k = 0) := by
  unfold arnoldiStepOp
  simp only [hd, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, fun i j hj => ite_eq_right hj,
    fun h => (ite_eq_left rfl).trans ((ite_eq_left rfl).trans (of_decide_eq_true h))⟩

/-- The vector `G_{j}ᵀ ⋯ G_1ᵀ h_{:,j}` that a genuine pass `j` rotates last. -/
private noncomputable def gmresV (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) : Fin (m + 1) → ℝ :=
  gmresW s.cs j *ᵥ gmresHcol (Id.run (arnoldiStepOp pure op s.arnoldi)) j

/-- The rotation `(c, s) = givens(v_j, v_{j+1})` determined by a genuine pass `j`. -/
private noncomputable def gmresC (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) : ℝ × ℝ :=
  Id.run (GolubVanLoan.Chapter05.algorithm_5_1_3 pure (gmresV op s j j.castSucc)
    (gmresV op s j j.succ))

/-- The exact run of a genuine GMRES pass. -/
private theorem gmresStep_run (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) (hd : s.arnoldi.done = false) :
    Id.run (gmresStep pure op s j) =
      ⟨Id.run (arnoldiStepOp pure op s.arnoldi),
        s.R.updateCol j ((gmresRot (gmresC op s j) j)ᵀ *ᵥ gmresV op s j),
        (gmresRot (gmresC op s j) j)ᵀ *ᵥ s.g, Function.update s.cs j (gmresC op s j)⟩ := by
  have hl : (List.finRange m).filter (· < j) =
      (List.finRange m).filter (fun i : Fin m => (i : ℕ) < j) :=
    List.filter_congr fun i _ => decide_eq_decide.2 Fin.lt_def
  unfold gmresStep
  simp only [hd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
  rw [hl, foldlM_rot_col, foldl_rot_eq _ _ j.2.le, givensApplyLeft_col (castSucc_ne_succ j),
    givensRotateVec_run (castSucc_ne_succ j)]
  simp only [updateCol_self, gmresV, gmresC, gmresRot]
  congr 1
  ext a b
  simp only [updateCol_apply]
  split_ifs <;> rfl

/-- The Arnoldi part of an exact GMRES pass is chapter 10's pass of Algorithm 10.5.1 for `B`. -/
private theorem gmresStep_arnoldi {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) (s : GMRESState n m)
    (j : Fin m) :
    (Id.run (gmresStep pure op s j)).arnoldi =
      Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B s.arnoldi) := by
  cases hd : s.arnoldi.done
  · rw [gmresStep_run op s j hd]
    exact arnoldiStepOp_run hop _
  · simp only [gmresStep, GolubVanLoan.Chapter10.arnoldiStep, hd, ↓reduceIte, Id.run_pure]

/-- The Arnoldi part of the exact GMRES passes iterates chapter 10's pass. -/
private theorem foldl_gmresStep_arnoldi {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) :
    ∀ (l : List (Fin m)) (s : GMRESState n m),
      (l.foldl (fun s j => Id.run (gmresStep pure op s j)) s).arnoldi =
        (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[l.length] s.arnoldi
  | [], _ => rfl
  | j :: l, s => by
    rw [List.foldl_cons, foldl_gmresStep_arnoldi hop l, gmresStep_arnoldi hop,
      List.length_cons, Function.iterate_succ_apply]

/-- The exact run of Algorithm 10.5.1 iterates its pass. -/
private theorem algorithm_10_5_1_run_eq_iterate (B : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ)
    (t : ℕ) :
    Id.run (GolubVanLoan.Chapter10.algorithm_10_5_1 pure B q₁ t) =
      (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[t]
        { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := q₁, done := false } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp only [GolubVanLoan.Chapter10.algorithm_10_5_1, List.range_succ, List.foldlM_append,
      List.foldlM_cons, List.foldlM_nil, bind_pure, Id.run_bind]

/-- The exact initial state of `gmresCore` from `z₀`. -/
private noncomputable def gmresInit (z₀ : Fin n → ℝ) (m : ℕ) : GMRESState n m :=
  ⟨⟨0, fun _ => 0, fun _ _ => 0, (‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖)⁻¹ • z₀,
      decide (‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ = 0)⟩, 0,
    Krylov.firstVec ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ (m + 1), fun _ => (1, 0)⟩

/-- The exact triangular solve and update after the loop of `gmresCore`. -/
private noncomputable def gmresFinish (x₀ : Fin n → ℝ) (s : GMRESState n m) :
    GMRESState n m × (Fin n → ℝ) :=
  if h : s.arnoldi.k ≤ m then
    (s, x₀ + (of fun i (l : Fin s.arnoldi.k) => s.arnoldi.q l i) *ᵥ
      Id.run (GolubVanLoan.Chapter03.algorithm_3_1_2 pure
        (s.R.submatrix (Fin.castLE (Nat.le_succ_of_le h)) (Fin.castLE h))
        (fun i => s.g (Fin.castLE (Nat.le_succ_of_le h) i))))
  else (s, x₀)

/-- The exact run of `gmresCore`. -/
private theorem gmresCore_run (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (x₀ z₀ : Fin n → ℝ) (m : ℕ) :
    Id.run (gmresCore pure op x₀ z₀ m) =
      gmresFinish x₀ (Id.run ((List.finRange m).foldlM (gmresStep pure op) (gmresInit z₀ m))) := by
  simp only [gmresCore, Id.run_bind, GolubVanLoan.Chapter10.vecNorm_spec,
    GolubVanLoan.Chapter10.vecDiv_spec]
  unfold gmresFinish gmresInit
  split_ifs
  · simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec]
  · rfl

/-! The invariant of the rotations. -/

/-- The state of the exact GMRES loop after `t` passes: the step count, the exit test, the
rotations, and the rotated Hessenberg matrix and right-hand side. -/
private def GInv (β₀ : ℝ) (t : ℕ) (s : GMRESState n m) : Prop :=
  s.arnoldi.k ≤ t ∧ (s.arnoldi.done = false → s.arnoldi.k = t) ∧
    (s.arnoldi.done = true → (s.arnoldi.k = 0 ∧ β₀ = 0) ∨
      (0 < s.arnoldi.k ∧ s.arnoldi.h s.arnoldi.k (s.arnoldi.k - 1) = 0)) ∧
    (∀ i : Fin m, (i : ℕ) < s.arnoldi.k → (s.cs i).1 ^ 2 + (s.cs i).2 ^ 2 = 1) ∧
    (∀ b : Fin m, s.arnoldi.k ≤ b → ∀ a, s.R a b = 0) ∧
    (∀ b : Fin m, (b : ℕ) < s.arnoldi.k → ∀ a,
      s.R a b = (gmresW s.cs s.arnoldi.k *ᵥ gmresHcol s.arnoldi b) a) ∧
    (∀ b : Fin m, (b : ℕ) < s.arnoldi.k → ∀ a : Fin (m + 1), (b : ℕ) < a → s.R a b = 0) ∧
    s.g = gmresW s.cs s.arnoldi.k *ᵥ Krylov.firstVec β₀ (m + 1)

/-- One exact pass keeps the invariant. -/
private theorem gInv_step (op : (Fin n → ℝ) → Id (Fin n → ℝ)) {β₀ : ℝ} {t : ℕ} (ht : t < m)
    {s : GMRESState n m} (hs : GInv β₀ t s) :
    GInv β₀ (t + 1) (Id.run (gmresStep pure op s ⟨t, ht⟩)) := by
  unfold GInv at hs ⊢
  obtain ⟨hkt, hnd, hdn, hcs, hR0, hRW, hRlow, hg⟩ := hs
  cases hd : s.arnoldi.done
  · have hk : s.arnoldi.k = t := hnd hd
    obtain ⟨hLk, hLh, hLd⟩ := arnoldiStepOp_fields op s.arnoldi hd
    rw [gmresStep_run op s ⟨t, ht⟩ hd]
    set j : Fin m := ⟨t, ht⟩ with hj
    set L := Id.run (arnoldiStepOp pure op s.arnoldi) with hL
    set c := gmresC op s j with hc
    set v := gmresV op s j with hv
    obtain ⟨hc1, hc2, -⟩ := GolubVanLoan.Chapter05.algorithm_5_1_3_spec (v j.castSucc) (v j.succ)
    have hcv : c = Id.run (GolubVanLoan.Chapter05.algorithm_5_1_3 pure (v j.castSucc)
        (v j.succ)) := rfl
    rw [← hcv] at hc1 hc2
    have hW : gmresW (Function.update s.cs j c) (t + 1) = (gmresRot c j)ᵀ * gmresW s.cs t := by
      rw [gmresW_succ _ ht, Function.update_self]
      congr 1
      exact gmresW_congr fun i hi => Function.update_of_ne (fun h => by
        rw [h] at hi; simp [j] at hi) _ _
    have hLk' : L.k = t + 1 := by rw [hLk, hk]
    have hcol : ∀ b : Fin m, (b : ℕ) < t → gmresHcol L b = gmresHcol s.arnoldi b := by
      intro b hb
      funext a
      simp only [gmresHcol]
      rw [hLh _ _ (by omega)]
    have hvW : v = gmresW s.cs t *ᵥ gmresHcol L j := rfl
    dsimp only
    refine ⟨hLk'.le, fun _ => hLk', fun hd' => Or.inr ⟨by omega, ?_⟩,
      fun i hi => ?_, fun b hb a => ?_, fun b hb a => ?_, fun b hb a hab => ?_, ?_⟩
    · rw [hLk', Nat.add_sub_cancel, ← hk]
      exact hLd hd'
    · simp only [hLk'] at hi
      by_cases hij : i = j
      · rw [hij, Function.update_self]; exact hc1
      · rw [Function.update_of_ne hij]
        have hne : (i : ℕ) ≠ t := fun h => hij (Fin.ext h)
        exact hcs i (by omega)
    · simp only [hLk'] at hb
      have hbj : b ≠ j := fun h => by rw [h] at hb; simp [j] at hb
      rw [updateCol_apply, ite_eq_right hbj]
      exact hR0 b (by omega) a
    · simp only [hLk'] at hb ⊢
      rw [hW, ← mulVec_mulVec]
      by_cases hbj : b = j
      · subst hbj
        rw [updateCol_apply, ite_eq_left rfl, hvW]
      · have hne : (b : ℕ) ≠ t := fun h => hbj (Fin.ext h)
        have hbt : (b : ℕ) < t := by omega
        rw [updateCol_apply, ite_eq_right hbj, hcol b hbt, ← hk]
        have hcolb : gmresW s.cs s.arnoldi.k *ᵥ gmresHcol s.arnoldi b = fun a => s.R a b :=
          funext fun a => (hRW b (by omega) a).symm
        rw [hcolb, gmresRot_mulVec_of_eq_zero _ _ (hRlow b (by omega) _ (by simp [j]; omega))
          (hRlow b (by omega) _ (by simp [j]; omega))]
    · simp only [hLk'] at hb
      by_cases hbj : b = j
      · subst hbj
        rw [updateCol_apply, ite_eq_left rfl, gmresRot_mulVec_apply]
        have ha1 : a ≠ j.castSucc := fun h => by rw [h] at hab; simp [j] at hab
        rw [ite_eq_right ha1]
        by_cases ha2 : a = j.succ
        · rw [ite_eq_left ha2]
          linear_combination hc2
        · rw [ite_eq_right ha2, hvW, gmresW_mulVec_apply_of_lt _ _ _ (by simp [j] at hab; omega)]
          simp only [gmresHcol]
          split_ifs with hle
          · exfalso
            apply ha2
            ext
            simp [j] at hab hle ⊢
            omega
          · rfl
      · rw [updateCol_apply, ite_eq_right hbj]
        have hne : (b : ℕ) ≠ t := fun h => hbj (Fin.ext h)
        exact hRlow b (by omega) a hab
    · simp only [hLk']
      rw [hW, ← mulVec_mulVec, ← hk, ← hg]
  · have hs' : Id.run (gmresStep pure op s ⟨t, ht⟩) = s := by
      simp only [gmresStep, hd, ↓reduceIte, Id.run_pure]
    rw [hs']
    exact ⟨by omega, fun h => absurd (h.symm.trans hd) Bool.false_ne_true, hdn, hcs, hR0, hRW,
      hRlow, hg⟩

/-- The invariant after the first `t` exact passes. -/
private theorem gInv_foldl (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (z₀ : Fin n → ℝ) :
    ∀ t ≤ m, GInv ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ t
      (((List.finRange m).take t).foldl (fun s j => Id.run (gmresStep pure op s j))
        (gmresInit z₀ m)) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [List.take_zero, List.foldl_nil]
    unfold GInv
    refine ⟨le_rfl, fun _ => rfl, fun h => Or.inl ⟨rfl, by simpa [gmresInit] using h⟩,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun b _ a => rfl,
      fun b hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _), ?_⟩
    simp [gmresInit, gmresW]
  | succ t ih =>
    intro ht
    rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hget : (List.finRange m)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
    rw [hget]
    exact gInv_step op ht (ih (by omega))


/-! Scaling the starting vector. -/

/-- Rescaling the starting vector by a positive number does not change the Arnoldi vectors (both
sequences satisfy the modified Gram–Schmidt recurrence from `v/‖v‖`). -/
private theorem vec_smul_of_pos (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0 < c) :
    Arnoldi.vec T (c • v) = Arnoldi.vec T v := by
  simpa using Arnoldi.vec_smul_of_pos T v hc

/-- A sum over `Fin p` whose terms vanish from index `k` on is the sum over its first `k`
indices. -/
private theorem sum_castLE_eq {k p : ℕ} (h : k ≤ p) (f : Fin p → ℝ)
    (hf : ∀ c : Fin p, k ≤ (c : ℕ) → f c = 0) :
    ∑ a : Fin k, f (Fin.castLE h a) = ∑ c, f c := by
  have e1 : ∑ c, f c = ∑ i ∈ Finset.range p, (if hi : i < p then f ⟨i, hi⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if hi : i < p then f ⟨i, hi⟩ else 0)]
    exact Finset.sum_congr rfl fun c _ => by rw [dite_eq_left c.2]
  have e2 : ∑ a : Fin k, f (Fin.castLE h a) =
      ∑ i ∈ Finset.range k, (if hi : i < p then f ⟨i, hi⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if hi : i < p then f ⟨i, hi⟩ else 0)]
    exact Finset.sum_congr rfl fun a _ => by rw [dite_eq_left (lt_of_lt_of_le a.2 h)]; rfl
  rw [e1, e2]
  refine Finset.sum_subset (Finset.range_mono h) fun i hi hk => ?_
  simp only [Finset.mem_range] at hi hk
  rw [dite_eq_left hi]
  exact hf ⟨i, hi⟩ (by simpa using hk)

/-- The rows of the accumulated rotations beyond `t` are those of the identity. -/
private theorem gmresW_apply_of_lt_left (cs : Fin m → ℝ × ℝ) (t : ℕ) {a : Fin (m + 1)}
    (ha : t < a) (c : Fin (m + 1)) : gmresW cs t a c = if a = c then 1 else 0 := by
  have h := gmresW_mulVec_apply_of_lt cs t (Pi.single c 1) ha
  rw [mulVec_single_one, col_apply, Pi.single_apply] at h
  exact h

/-- The Arnoldi data of the exact GMRES loop: `k = min(m, grade)` steps, the Arnoldi vectors and
the Hessenberg entries of `z₀`. -/
private theorem gmres_arnoldi_spec {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) (z₀ : Fin n → ℝ)
    (m : ℕ) :
    ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
        (gmresInit z₀ m)).arnoldi.k = min m (grade (toEuclideanLin B) (WithLp.toLp 2 z₀)) ∧
      ∀ j < ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
          (gmresInit z₀ m)).arnoldi.k,
        WithLp.toLp 2 (((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
            (gmresInit z₀ m)).arnoldi.q j) =
          Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) j ∧
        ∀ i ≤ j + 1, ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
            (gmresInit z₀ m)).arnoldi.h i j =
          Arnoldi.coeff (toEuclideanLin B) (WithLp.toLp 2 z₀) i j := by
  rw [foldl_gmresStep_arnoldi hop, List.length_finRange]
  set β₀ := ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ with hβ₀
  by_cases h0 : β₀ = 0
  · have hfix : ∀ t, (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[t]
        (gmresInit z₀ m).arnoldi = (gmresInit z₀ m).arnoldi := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply', ih]
        simp [GolubVanLoan.Chapter10.arnoldiStep, gmresInit, ← hβ₀, h0]
    rw [hfix]
    have hz : (WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n)) = 0 := norm_eq_zero.1 h0
    rw [hz, grade_zero]
    refine ⟨by simp [gmresInit], fun j hj => absurd hj (by simp [gmresInit])⟩
  · have hinit : (gmresInit z₀ m).arnoldi =
        { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := β₀⁻¹ • z₀, done := false } := by
      simp [gmresInit, ← hβ₀, h0]
    rw [hinit, ← algorithm_10_5_1_run_eq_iterate]
    have hβpos : 0 < β₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hq : (WithLp.toLp 2 (β₀⁻¹ • z₀) : EuclideanSpace ℝ (Fin n)) =
        β₀⁻¹ • WithLp.toLp 2 z₀ := WithLp.toLp_smul _ _ _
    have hqn : ‖(WithLp.toLp 2 (β₀⁻¹ • z₀) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      rw [hq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hβpos.le), ← hβ₀,
        inv_mul_cancel₀ h0]
    obtain ⟨hk, hvec, -⟩ := GolubVanLoan.Chapter10.algorithm_10_5_1_spec B hqn m
    have hvs : Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 (β₀⁻¹ • z₀)) =
        Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) := by
      rw [hq]; exact vec_smul_of_pos _ _ (inv_pos.2 hβpos)
    have hgr : grade (toEuclideanLin B) (WithLp.toLp 2 (β₀⁻¹ • z₀)) =
        grade (toEuclideanLin B) (WithLp.toLp 2 z₀) := by
      rw [hq]; exact grade_smul _ _ (inv_ne_zero h0)
    refine ⟨by rw [hk, hgr], fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hvec j hj
    refine ⟨by rw [h1, WithLp.toLp_ofLp, hvs], fun i hi => ?_⟩
    rw [h2 i hi, Arnoldi.coeff, Arnoldi.coeff, hvs]

/-- **Exact semantics of the GMRES loop** (`gmresCore`), for an operator routine with exact
semantics `q ↦ Bq`, `B` nonsingular, and `z₀ = c − Bx₀`: the run makes `k = min(m, grade)`
Arnoldi steps on `z₀` (`Arnoldi.vec`, `Arnoldi.coeff`: modified Gram–Schmidt is Gram–Schmidt in
exact arithmetic, chapter 10's `algorithm_10_5_1_spec`); its rotations bring `H̃_k` to `[R_k; 0]`
with `R_k` upper triangular and nonsingular, so the back substitution solves `R_k y_k = p_k` and
`x̃ = x₀ + Q_k y_k` is the minimal-residual iterate of `Bx = c` on `x₀ + 𝒦(B, z₀, k)`
(`Krylov.IsMinResidualIterate`), with residual norm `|ρ_k|`; if the loop stopped on `β_k = 0`,
`x̃` solves `Bx = c` (`Krylov.IsMinResidualIterate.apply_eq_of_grade_le`). The rotations need not
be the backbone's (`Krylov.givensQ`): `givens` fixes their signs differently, and the argument
uses only that they are orthogonal and triangularize `H̃_k`. -/
theorem gmresCore_spec {op : (Fin n → ℝ) → Id (Fin n → ℝ)} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B) (hop : ∀ q, Id.run (op q) = B *ᵥ q) (c x₀ z₀ : Fin n → ℝ)
    (hz : z₀ = c - B *ᵥ x₀) (m : ℕ) :
    (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k =
        min m (grade (toEuclideanLin B) (WithLp.toLp 2 z₀)) ∧
      (∀ j < (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k,
        WithLp.toLp 2 ((Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.q j) =
            Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) j ∧
          ∀ i ≤ j + 1, (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.h i j =
            Arnoldi.coeff (toEuclideanLin B) (WithLp.toLp 2 z₀) i j) ∧
      IsMinResidualIterate (toEuclideanLin B) (WithLp.toLp 2 c) (WithLp.toLp 2 x₀)
        (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k
        (WithLp.toLp 2 (Id.run (gmresCore pure op x₀ z₀ m)).2) ∧
      (∀ i : Fin (m + 1), (i : ℕ) = (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k →
        |(Id.run (gmresCore pure op x₀ z₀ m)).1.g i| =
          ‖WithLp.toLp 2 c -
            toEuclideanLin B (WithLp.toLp 2 (Id.run (gmresCore pure op x₀ z₀ m)).2)‖) ∧
      ((Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.done = true →
        B *ᵥ (Id.run (gmresCore pure op x₀ z₀ m)).2 = c) := by
  rw [gmresCore_run, List.idRun_foldlM]
  set T := toEuclideanLin B with hT
  set z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z₀ with hzdef
  set β₀ := ‖z‖ with hβ₀
  set s := (List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
    (gmresInit z₀ m) with hs
  obtain ⟨hk, hvec⟩ := gmres_arnoldi_spec hop z₀ m
  rw [← hs] at hk hvec
  have hGI := gInv_foldl op z₀ m le_rfl
  rw [List.take_of_length_le (by simp), ← hs] at hGI
  obtain ⟨hkt, -, hdn, hcs, -, hRW, hRlow, hg⟩ := hGI
  set k := s.arnoldi.k with hkdef
  have hkm : k ≤ m := hkt
  have hkg : k ≤ grade T z := by rw [hk]; exact min_le_right _ _
  -- the triangular solve and the update
  set Rk : Matrix (Fin k) (Fin k) ℝ :=
    s.R.submatrix (Fin.castLE (Nat.le_succ_of_le hkm)) (Fin.castLE hkm) with hRk
  set pk : Fin k → ℝ := fun i => s.g (Fin.castLE (Nat.le_succ_of_le hkm) i) with hpk
  set y := Id.run (GolubVanLoan.Chapter03.algorithm_3_1_2 pure Rk pk) with hy
  have hfin : gmresFinish x₀ s =
      (s, x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y) := by
    unfold gmresFinish
    exact dite_eq_left hkm
  rw [hfin]
  dsimp only
  -- the Hessenberg columns
  set h := Arnoldi.coeff T z with hh
  have hcolh : ∀ b : Fin m, (b : ℕ) < k →
      gmresHcol s.arnoldi b = fun a : Fin (m + 1) => h (a : ℕ) (b : ℕ) := by
    intro b hb
    funext a
    simp only [gmresHcol]
    split_ifs with ha
    · exact (hvec b hb).2 a ha
    · exact (Arnoldi.coeff_eq_zero_of_lt T z (by omega)).symm
  -- the rotations, restricted to the first `k + 1` entries
  set W := gmresW s.cs k with hW
  have hWmem : W ∈ orthogonalGroup (Fin (m + 1)) ℝ := gmresW_mem hcs
  have hk1 : k + 1 ≤ m + 1 := Nat.succ_le_succ hkm
  set ι : Fin (k + 1) → Fin (m + 1) := Fin.castLE hk1 with hι
  set κ : Fin k → Fin m := Fin.castLE hkm with hκ
  set W' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := W.submatrix ι ι with hW'
  set Hk := Arnoldi.hessenberg T z k with hHk
  set R' : Matrix (Fin (k + 1)) (Fin k) ℝ := s.R.submatrix ι κ with hR'
  have hWrow : ∀ (a : Fin (k + 1)) (c : Fin (m + 1)), k + 1 ≤ (c : ℕ) → W (ι a) c = 0 := by
    intro a c hc
    rw [hW, gmresW_apply_of_lt _ _ _ (by omega)]
    split_ifs with h'
    · have := congrArg Fin.val h'
      simp [ι] at this
      omega
    · rfl
  have hWcol : ∀ (d : Fin (m + 1)) (a : Fin (k + 1)), k + 1 ≤ (d : ℕ) → W d (ι a) = 0 := by
    intro d a hd
    rw [hW, gmresW_apply_of_lt_left _ _ (by omega)]
    split_ifs with h'
    · have := congrArg Fin.val h'
      simp [ι] at this
      omega
    · rfl
  have hC1 : W' * Hk = R' := by
    ext a b
    rw [mul_apply, hR', submatrix_apply, hRW (κ b) b.2 (ι a), hcolh (κ b) b.2, mulVec,
      dotProduct]
    rw [← sum_castLE_eq hk1 (fun c => W (ι a) c * h c (κ b))
      fun c hc => by rw [hWrow a c hc, zero_mul]]
    rfl
  have hWo : W'ᵀ * W' = 1 := by
    have hWW := (mem_orthogonalGroup_iff' _ _).1 hWmem
    ext a c
    rw [mul_apply]
    have e := congrFun (congrFun hWW (ι a)) (ι c)
    rw [mul_apply, ← sum_castLE_eq hk1 (fun d => Wᵀ (ι a) d * W d (ι c))
      fun d hd => by rw [transpose_apply, hWcol d a hd, zero_mul]] at e
    refine e.trans ?_
    rw [one_apply, one_apply]
    simp [ι, Fin.ext_iff]
  have hW'mem : W' ∈ orthogonalGroup (Fin (k + 1)) ℝ := (mem_orthogonalGroup_iff' _ _).2 hWo
  have hC3 : (fun a => s.g (ι a)) = W' *ᵥ Krylov.firstVec β₀ (k + 1) := by
    funext a
    rw [hg, mulVec, dotProduct, mulVec, dotProduct,
      ← sum_castLE_eq hk1 (fun c => W (ι a) c * Krylov.firstVec β₀ (m + 1) c)
        fun c hc => by rw [hWrow a c hc, zero_mul]]
    rfl
  have hC4 : ∀ b : Fin k, R' (Fin.last k) b = 0 := fun b =>
    hRlow (κ b) b.2 (ι (Fin.last k)) (by simp [κ, ι])
  -- the least-squares identity
  have hLS : ∀ w : Fin k → ℝ,
      ‖(WithLp.toLp 2 (Krylov.firstVec β₀ (k + 1) - Hk *ᵥ w) : EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2
        = ‖(WithLp.toLp 2 (pk - Rk *ᵥ w) : EuclideanSpace ℝ (Fin k))‖ ^ 2 +
          s.g (ι (Fin.last k)) ^ 2 := by
    intro w
    rw [← norm_toLp_mulVec_of_mem_unitaryGroup hW'mem, mulVec_sub, mulVec_mulVec, hC1, ← hC3,
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    congr 1
    all_goals simp only [Pi.sub_apply, mulVec, dotProduct, hC4, zero_mul,
      Finset.sum_const_zero, sub_zero]
  -- `R_k` is upper triangular and nonsingular
  have hRkU : Rk.IsUpperTriangular := fun a b hab => hRlow (κ b) b.2 _ (by simpa [κ] using hab)
  have hTinj : Function.Injective T := by
    intro u v huv
    have h1 : B *ᵥ u.ofLp = B *ᵥ v.ofLp := by
      have := congrArg WithLp.ofLp huv
      simpa [hT] using this
    exact WithLp.ofLp_injective 2 ((mulVec_injective_iff_isUnit.2 hB) h1)
  have hker : ∀ w : Fin k → ℝ, Rk *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hR'w : R' *ᵥ w = 0 := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · simp only [mulVec, dotProduct, hC4, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
      · have e : (R' *ᵥ w) a.castSucc = (Rk *ᵥ w) a := rfl
        rw [e, hw]
        rfl
    have hHw : Hk *ᵥ w = 0 := by
      have e : W'ᵀ *ᵥ (W' *ᵥ (Hk *ᵥ w)) = Hk *ᵥ w := by
        rw [mulVec_mulVec, hWo, one_mulVec]
      have e2 : W' *ᵥ (Hk *ᵥ w) = 0 := by rw [mulVec_mulVec, hC1, hR'w]
      rw [← e, e2, mulVec_zero]
    have hsum : ∑ j, w j • Arnoldi.vec T z j = 0 := by
      apply hTinj
      rw [map_zero, Arnoldi.apply_sum, ← hHk, hHw]
      simp
    funext i
    have h1 := congrArg (fun v => inner ℝ (Arnoldi.vec T z i) v) hsum
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at h1
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hji (Fin.ext h.symm)), mul_zero])
      (by simp), real_inner_self_eq_norm_sq,
      Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hkg), one_pow, mul_one] at h1
    exact h1
  have hRkunit : IsUnit Rk := mulVec_injective_iff_isUnit.1 fun w w' h' =>
    sub_eq_zero.1 (hker _ (by rw [mulVec_sub, h', sub_self]))
  have hdiag : ∀ i, Rk i i ≠ 0 := by
    have hdet := (isUnit_iff_isUnit_det Rk).1 hRkunit
    rw [det_of_isUpperTriangular hRkU] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.1 hdet.ne_zero) i (Finset.mem_univ i)
  have hyR : Rk *ᵥ y = pk := GolubVanLoan.Chapter03.algorithm_3_1_2_spec hRkU hdiag pk
  -- the computed iterate in `𝔼`
  have hxE : WithLp.toLp 2 (x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y) =
      WithLp.toLp 2 x₀ + ∑ j, y j • Arnoldi.vec T z j := by
    rw [WithLp.toLp_add]
    congr 1
    have hq : ∀ j : Fin k, Arnoldi.vec T z j = WithLp.toLp 2 (s.arnoldi.q j) :=
      fun j => ((hvec j j.2).1).symm
    simp_rw [hq, ← WithLp.toLp_smul, ← WithLp.toLp_sum]
    congr 1
    ext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hzE : z = WithLp.toLp 2 c - T (WithLp.toLp 2 x₀) := by
    rw [hzdef, hz, hT, toEuclideanLin_toLp, WithLp.toLp_sub]
  have hmin : IsMinResidualIterate T (WithLp.toLp 2 c) (WithLp.toLp 2 x₀) k
      (WithLp.toLp 2 (x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y)) := by
    rw [hxE]
    have key := isMinResidualIterate_iff_isMinOn (A := T) (b := WithLp.toLp 2 c)
      (x₀ := WithLp.toLp 2 x₀) (hzE ▸ hkg) y
    rw [← hzE] at key
    refine key.2 (isMinOn_iff.2 fun w _ => ?_)
    have e1 := hLS y
    have e2 := hLS w
    rw [hyR, sub_self] at e1
    simp only [WithLp.toLp_zero, norm_zero] at e1
    simp only [RCLike.ofReal_real_eq_id, id_eq] at key
    have hle : ‖(WithLp.toLp 2 (Krylov.firstVec β₀ (k + 1) - Hk *ᵥ y) :
        EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (Krylov.firstVec β₀ (k + 1) - Hk *ᵥ w) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ ^ 2 := by
      rw [e1, e2]
      nlinarith [sq_nonneg ‖(WithLp.toLp 2 (pk - Rk *ᵥ w) : EuclideanSpace ℝ (Fin k))‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle
  refine ⟨hk, hvec, hmin, fun i hi => ?_, fun hdone => ?_⟩
  · have hiι : i = ι (Fin.last k) := Fin.ext hi
    have e1 := hLS y
    rw [hyR, sub_self, WithLp.toLp_zero, norm_zero] at e1
    have hres := norm_residual_eq_norm_firstVec_sub_mulVec (A := T) (b := WithLp.toLp 2 c)
      (x₀ := WithLp.toLp 2 x₀) (hzE ▸ hkg) y
    rw [← hzE] at hres
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hres
    rw [hxE, hres, hiι, ← Real.sqrt_sq (norm_nonneg _), e1, zero_pow two_ne_zero,
      zero_add, Real.sqrt_sq_eq_abs]
  · have hgk : grade T z ≤ k := by
      rcases hdn hdone with ⟨-, hb0⟩ | ⟨hpos, hh0⟩
      · have hz0 : z = 0 := norm_eq_zero.1 hb0
        rw [hz0, grade_zero]
        exact Nat.zero_le _
      · have e := (hvec (k - 1) (by omega)).2 k (by omega)
        rw [hh0] at e
        have e' : Arnoldi.coeff T z (k - 1 + 1) (k - 1) = 0 := by
          rw [Nat.sub_add_cancel hpos]; exact e.symm
        have := (Arnoldi.coeff_succ_self_eq_zero_iff T z (k - 1)).1 e'
        omega
    have happ := hmin.apply_eq_of_grade_le (hzE ▸ hgk) hTinj.injOn
    rw [hT, toEuclideanLin_toLp] at happ
    exact WithLp.toLp_injective 2 happ

/-- **Exact semantics of Algorithm 11.4.2** (`A` nonsingular): the exact run makes
`k = min(m, grade)` steps on `r₀ = b − Ax₀`; the computed `q_j`, `h_ij` are the Arnoldi vectors
and coefficients of `r₀` (the modified Gram–Schmidt loop (11.4.11) is Gram–Schmidt in exact
arithmetic, chapter 10's `algorithm_10_5_1_spec`); `x̃` minimizes `‖b − Ax‖₂` over
`x₀ + 𝒦(A, r₀, k)` (`Krylov.IsMinResidualIterate`) with `|ρ_k| = ‖Ax̃ − b‖₂`; and if the loop
stopped on `β_k = 0`, `Ax̃ = b`. This is the book's "either `x̃` solves `Ax = b` or minimizes
`‖Ax − b‖₂` over the affine space `x₀ + 𝒦(A, r₀, m)`" (when the loop did not stop early, `k = m`).
The rotations are those of chapter 5's `givens`, whose signs differ from the backbone's
`Krylov.givensQ`; only their orthogonality and the triangular form they produce are used
(`gmresCore_spec`). -/
theorem algorithm_11_4_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b x₀ : Fin n → ℝ)
    (m : ℕ) :
    let out := Id.run (algorithm_11_4_2 pure A b x₀ m)
    let T := toEuclideanLin A
    let r₀ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    out.1.arnoldi.k = min m (grade T r₀) ∧
      (∀ j < out.1.arnoldi.k, WithLp.toLp 2 (out.1.arnoldi.q j) = Arnoldi.vec T r₀ j ∧
        ∀ i ≤ j + 1, out.1.arnoldi.h i j = Arnoldi.coeff T r₀ i j) ∧
      IsMinResidualIterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) out.1.arnoldi.k
        (WithLp.toLp 2 out.2) ∧
      (∀ i : Fin (m + 1), (i : ℕ) = out.1.arnoldi.k →
        |out.1.g i| = ‖WithLp.toLp 2 b - T (WithLp.toLp 2 out.2)‖) ∧
      (out.1.arnoldi.done = true → A *ᵥ out.2 = b) := by
  have hrun : Id.run (algorithm_11_4_2 pure A b x₀ m) =
      Id.run (gmresCore pure (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 pure A q 0) x₀
        (b - A *ᵥ x₀) m) := by
    simp only [algorithm_11_4_2, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
      mulVec_neg, ← sub_eq_add_neg]
  have hr₀ : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀) =
      (WithLp.toLp 2 (b - A *ᵥ x₀) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanLin_toLp, WithLp.toLp_sub]
  dsimp only
  rw [hrun, hr₀]
  exact gmresCore_spec hA
    (fun q => (GolubVanLoan.Chapter01.algorithm_1_1_3_spec A q 0).trans (zero_add _))
    b x₀ (b - A *ᵥ x₀) rfl m

end GMRESSpec

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
  · rw [BiLanczos.span_vec h, hr, subspace_smul_of_ne_zero _ _ hβ]
  · rw [BiLanczos.span_dualVec h, hrt, subspace_smul_of_ne_zero _ _ hγ]

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

/-- **The BiCG column of Figure 11.4.1**, run for `fuel` passes: "`r₀ = b − Ax₀`, `r̃₀ᵀr₀ ≠ 0`,
`x_c = x₀`, `p_c = r_c = r₀`, `p̃_c = r̃_c = r̃₀`", then `fuel` passes of `bicgStep`. The figure
gives no stopping test, so the number of passes `fuel` is the last argument; the condition
`r̃₀ᵀr₀ ≠ 0` is a hypothesis of the theorems, not a test of the program. -/
noncomputable def bicg (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (BiCGState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => bicgStep rnd A s) ⟨x₀, r₀, rt₀, r₀, rt₀⟩

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

/-- **The CGS column of Figure 11.4.1**, run for `fuel` passes: "`r₀ = b − Ax₀`, `x_c = x₀`,
`p_c = r_c = r₀`, `u_c = r_c`", then `fuel` passes of `cgsStep`. Only products with `A` occur. The
printed initial condition `r̃₀ᵀr̃₀ ≠ 0` should be `r̃₀ᵀr₀ ≠ 0`. -/
noncomputable def cgs (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (CGSState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => cgsStep rnd A rt₀ s) ⟨x₀, r₀, r₀, r₀⟩

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

/-- **The BiCGstab column of Figure 11.4.1**, run for `fuel` passes: "`r₀ = b − Ax₀`, `x_c = x₀`,
`p_c = r_c = r₀`", then `fuel` passes of `bicgstabStep`. The printed initial condition `r̃₀ᵀr̃₀ ≠ 0`
should be `r̃₀ᵀr₀ ≠ 0`. -/
noncomputable def bicgstab (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (BiCGstabState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => bicgstabStep rnd A rt₀ s) ⟨x₀, r₀, r₀⟩

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
  rw [hT, hr₀, BCG.iterate_self_eq_cg] at h
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
    rw [h4, h2, key, hsq, Module.End.aeval_apply_apply]

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
