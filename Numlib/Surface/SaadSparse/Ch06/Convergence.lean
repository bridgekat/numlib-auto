import Numlib.Surface.SaadSparse.Ch06.CG
import Numlib.Surface.SaadSparse.Ch06.Chebyshev
import Numlib.Surface.SaadSparse.Ch06.GMRES

/-!
# Saad, §6.11.3–6.11.4: convergence of the conjugate gradient method and of GMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.11.3–6.11.4.

The quantities of §6.11.3–6.11.4 are `η` (6.122), the condition number `κ`, the `A`-norm `anorm`
(the backbone's `energyNorm`, `Numlib/Analysis/InnerProductSpace/Energy.lean`) and `ε^{(m)}`
(`epsMin`, Proposition 6.32); `C k` and the min–max theorem live in `Ch06/Chebyshev.lean`.

Everything here is a specialization of the backbone:

* Lemma 6.28, Theorem 6.29 with (6.123), and (6.128) come from
  `Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T` and
  `Krylov.IsGalerkinIterate.energyNorm_error_le` (`Numlib/Krylov/Convergence/CG.lean`) applied to
  `cgX_isGalerkinIterate` of `Ch06/CG.lean`. The backbone's hypothesis is the quadratic-form
  bound `LinearMap.IsSymmetricBoundedBy lmin lmax`, matched to the book's extreme eigenvalues by
  `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`; its proof uses the compression trick
  rather than a functional calculus, so no diagonalization of `A` is needed.
* (6.124)–(6.127) are the book's chain of real identities for the Chebyshev argument `1 + 2η`.
* Theorem 6.30 is `Krylov.restarted_minRes_tendsto`: the work here is only to show that a cycle
  of GMRES(m) satisfies the backbone's per-cycle minimal-residual specification
  (`gmres_isMinResIterate`), and to identify the book's constants `μ = λ_min((A + Aᵀ)/2)` and
  `σ = ‖A‖₂` with the backbone's coercivity constant and operator norm.
* Lemma 6.31 is `Krylov.IsMinResIterate.norm_residual_le_norm_aeval` through the GMRES
  identification `gmresFixed_isMinResIterate` of `Ch06/GMRES.lean`, and Proposition 6.32 adds the
  surface bound `norm_aeval_diagonal_mulVec_le` for a diagonalizable complex matrix.

Deferred to the later phase (`tracker/saadsparse-ch6.md` §4, the complex-ellipse results):
Corollary 6.33, which needs Theorem 6.27 and hence the complex Chebyshev and ellipse theory the
backbone does not yet have.
-/

open scoped Polynomial

namespace SaadSparse.Ch06

/-! ### The quantities of §6.11.3 -/

section Quantities

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-- **(6.122)**: `η = λ_min / (λ_max - λ_min)`. -/
noncomputable def η (lmin lmax : ℝ) : ℝ := lmin / (lmax - lmin)

/-- The spectral condition number `κ = λ_max / λ_min` of §6.11.3. -/
noncomputable def κ (lmin lmax : ℝ) : ℝ := lmax / lmin

/-- The `A`-norm `‖x‖_A = √((A x, x))` of §6.11.3. -/
noncomputable def anorm (A : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : ℝ :=
  Real.sqrt (RCLike.re (inner 𝕜 (op A x) x))

/-- The book's `A`-norm is the backbone's energy norm. -/
theorem anorm_eq (A : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) : anorm A x = energyNorm (op A) x := rfl

/-- The Chebyshev argument of (6.123) written with the extreme eigenvalues:
`1 + 2η = (λ_max + λ_min)/(λ_max - λ_min)`. -/
theorem one_add_two_mul_η {lmin lmax : ℝ} (h : lmin ≠ lmax) :
    1 + 2 * η lmin lmax = (lmax + lmin) / (lmax - lmin) := by
  have hd : lmax - lmin ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [η]
  field_simp
  ring

/-- Polynomials in `A` commute with `A`. -/
private theorem aeval_apply_comm (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝕜[X]) (u : 𝔼) :
    Polynomial.aeval (op A) p (op A u) = op A (Polynomial.aeval (op A) p u) := by
  have h1 : Polynomial.aeval (op A) p (op A u) = (Polynomial.aeval (op A) p * op A) u := rfl
  have h2 : op A (Polynomial.aeval (op A) p u) = (op A * Polynomial.aeval (op A) p) u := rfl
  rw [h1, h2,
    show Polynomial.aeval (op A) p * op A = Polynomial.aeval (op A) (p * Polynomial.X) by
      rw [map_mul, Polynomial.aeval_X],
    show op A * Polynomial.aeval (op A) p = Polynomial.aeval (op A) (Polynomial.X * p) by
      rw [map_mul, Polynomial.aeval_X],
    mul_comm]

end Quantities

/-! ### Extreme values of a finite family of reals

The book's `λ_min` and `λ_max` are the `⨅` and `⨆` of the eigenvalue family; these are the facts
about them that the specializations need. -/

section Extremes

variable {ι : Type*} [Finite ι] {f : ι → ℝ}

private theorem ciInf_le' (i : ι) : ⨅ j, f j ≤ f i := ciInf_le (Finite.bddBelow_range f) i

private theorem le_ciSup' (i : ι) : f i ≤ ⨆ j, f j := le_ciSup (Finite.bddAbove_range f) i

private theorem lt_ciInf_of_forall [Nonempty ι] {a : ℝ} (h : ∀ i, a < f i) : a < ⨅ i, f i := by
  obtain ⟨i, hi⟩ := Finite.exists_min f
  exact lt_of_lt_of_le (h i) (le_ciInf hi)

end Extremes

section Infimum

variable {ι : Type*} [Nonempty ι] {f : ι → ℝ}

/-- `L ≤ c ⨅ f` from `L ≤ c f i` for every `i`, with `c ≥ 0`. -/
private theorem le_mul_ciInf {L c : ℝ} (hc : 0 ≤ c) (h : ∀ i, L ≤ c * f i) :
    L ≤ c * ⨅ i, f i := by
  rcases hc.eq_or_lt with h0 | h0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hi := h i
    rw [← h0, zero_mul] at hi ⊢
    exact hi
  · have h1 : ∀ i, L / c ≤ f i := fun i => (div_le_iff₀ h0).2 ((h i).trans_eq (mul_comm _ _))
    exact ((div_le_iff₀ h0).1 (le_ciInf h1)).trans_eq (mul_comm _ _)

end Infimum

/-! ### §6.11.3: convergence of the conjugate gradient method -/

section ConjugateGradient

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ xstar : EuclideanSpace ℝ (Fin n)}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- `(I - A q(A)) d_0 = x_* - (x_0 + q(A) r_0)`: the book's two ways of writing the error of a
Krylov iterate, related by `r_0 = A d_0`. -/
private theorem error_eq (hstar : op A xstar = b) (q : ℝ[X]) :
    ((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (xstar - x₀) =
      xstar - (x₀ + Polynomial.aeval (op A) q (r₀ A b x₀)) := by
  have hr : op A (xstar - x₀) = r₀ A b x₀ := by rw [map_sub, hstar]
  rw [← hr, aeval_apply_comm]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply]
  abel

/-- **Lemma 6.28**: the `m`-th conjugate gradient iterate is `x_m = x_0 + q_m(A) r_0` with
`deg q_m < m`, and `q_m` minimizes `‖(I - A q(A)) d_0‖_A` over the polynomials of degree `< m`. -/
theorem lemma_6_28 (hA : A.PosDef) (hstar : op A xstar = b) (m : ℕ) :
    ∃ q : ℝ[X], q.degree < m ∧ cgX A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) ∧
      ∀ q' : ℝ[X], q'.degree < m →
        anorm A (((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (xstar - x₀)) ≤
          anorm A (((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q') (xstar - x₀)) := by
  have hAc : (op A).IsSymmetricCoercive := isSymmetricCoercive_op_of_posDef hA
  have hgal := cgX_isGalerkinIterate (b := b) (x₀ := x₀) hA m
  obtain ⟨q, hq, hqe⟩ :=
    (Krylov.mem_subspace_iff_exists_aeval (op A) (b - op A x₀)).1 hgal.mem
  have hxeq : cgX A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) :=
    sub_eq_iff_eq_add'.1 hqe.symm
  refine ⟨q, hq, hxeq, fun q' hq' => ?_⟩
  have hy : x₀ + Polynomial.aeval (op A) q' (r₀ A b x₀) - x₀ ∈
      Krylov.subspace (op A) (b - op A x₀) m := by
    rw [add_sub_cancel_left]
    exact Krylov.aeval_apply_mem_subspace (op A) _ hq'
  rw [anorm_eq, anorm_eq, error_eq hstar q, error_eq hstar q', ← hxeq]
  exact IsGalerkin.energyNorm_le hAc hgal hstar hy

/-- The eigenvalues of a positive definite matrix are positive: the backbone's
`LinearMap.IsSymmetricCoercive.re_pos_of_hasEigenvalue` read through the eigenvalue bridge
`Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff`. -/
private theorem eigenvalues_pos_of_posDef (hA : A.PosDef) (hH : A.IsHermitian) (i : Fin n) :
    0 < hH.eigenvalues i := by
  have hAc : (op A).IsSymmetricCoercive := isSymmetricCoercive_op_of_posDef hA
  have hev : Module.End.HasEigenvalue (op A) ((hH.eigenvalues i : ℝ)) :=
    (Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff hH _).2 ⟨i, by simp⟩
  simpa using hAc.re_pos_of_hasEigenvalue hev

variable (A)

/-- The quadratic-form bounds of a positive definite matrix are its extreme eigenvalues; this is
the form in which the backbone's Chebyshev bounds take the book's spectral hypothesis. -/
theorem isSymmetricBoundedBy_op [NeZero n] (hA : A.PosDef) :
    (op A).IsSymmetricBoundedBy (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i) :=
  Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin hA.1
    fun i => ⟨ciInf_le' i, le_ciSup' i⟩

/-- `0 < λ_min` for a positive definite matrix. -/
theorem iInf_eigenvalues_pos [NeZero n] (hA : A.PosDef) : 0 < ⨅ i, hA.1.eigenvalues i := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact lt_ciInf_of_forall fun i => eigenvalues_pos_of_posDef hA hA.1 i

/-- `λ_min ≤ λ_max`. -/
theorem iInf_eigenvalues_le_iSup [NeZero n] (hA : A.PosDef) :
    ⨅ i, hA.1.eigenvalues i ≤ ⨆ i, hA.1.eigenvalues i := by
  obtain ⟨i⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact (ciInf_le' i).trans (le_ciSup' i)

variable {A}

/-- **Theorem 6.29**, **(6.123)**: for a symmetric positive definite `A` with extreme eigenvalues
`λ_min < λ_max` and `η = λ_min/(λ_max - λ_min)`,
`‖x_* - x_m‖_A ≤ ‖x_* - x_0‖_A / C_m(1 + 2η)`.

The book's `η` is `+∞` when `λ_min = λ_max`, so the hypothesis `hl` — at least two distinct
extreme eigenvalues — is the book's tacit assumption; without it use (6.128), `eq_6_128`. -/
theorem thm_6_29 [NeZero n] (hA : A.PosDef) (hstar : op A xstar = b)
    (hl : ⨅ i, hA.1.eigenvalues i < ⨆ i, hA.1.eigenvalues i) (m : ℕ) :
    anorm A (xstar - cgX A b x₀ m) ≤
      anorm A (xstar - x₀) /
        (C m).eval (1 + 2 * η (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) := by
  rw [anorm_eq, anorm_eq, one_add_two_mul_η hl.ne]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T (iInf_eigenvalues_pos A hA) hl
    (isSymmetricBoundedBy_op A hA) (cgX_isGalerkinIterate hA m) hstar

/-- **(6.124)**: `½ (1 + 2η + √((1+2η)² - 1))^m ≤ C_m(1 + 2η)`. -/
theorem eq_6_124 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (m : ℕ) :
    (1 + 2 * η lmin lmax + Real.sqrt ((1 + 2 * η lmin lmax) ^ 2 - 1)) ^ m / 2 ≤
      (C m).eval (1 + 2 * η lmin lmax) := by
  refine eq_6_112 m ?_
  rw [one_add_two_mul_η hll.ne, le_div_iff₀ (by linarith)]
  linarith

/-- **(6.125)**: `√((1 + 2η)² - 1) = 2√(η(η+1))`. -/
theorem eq_6_125 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    Real.sqrt ((1 + 2 * η lmin lmax) ^ 2 - 1) =
      2 * Real.sqrt (η lmin lmax * (η lmin lmax + 1)) := by
  have hη : 0 ≤ η lmin lmax := div_nonneg hl.le (by linarith)
  rw [show (1 + 2 * η lmin lmax) ^ 2 - 1 = 2 ^ 2 * (η lmin lmax * (η lmin lmax + 1)) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- **(6.126)**: `1 + 2η + 2√(η(η+1)) = (√η + √(η+1))²`. -/
theorem eq_6_126 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    1 + 2 * η lmin lmax + 2 * Real.sqrt (η lmin lmax * (η lmin lmax + 1)) =
      (Real.sqrt (η lmin lmax) + Real.sqrt (η lmin lmax + 1)) ^ 2 := by
  have hη : 0 ≤ η lmin lmax := div_nonneg hl.le (by linarith)
  have hs : Real.sqrt (η lmin lmax * (η lmin lmax + 1)) =
      Real.sqrt (η lmin lmax) * Real.sqrt (η lmin lmax + 1) := Real.sqrt_mul hη _
  rw [add_sq, Real.sq_sqrt hη, Real.sq_sqrt (by linarith), hs]
  ring

/-- **(6.127)**: `(√η + √(η+1))² = (√κ + 1)/(√κ - 1)`, with `κ = λ_max/λ_min`. -/
theorem eq_6_127 {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) :
    (Real.sqrt (η lmin lmax) + Real.sqrt (η lmin lmax + 1)) ^ 2 =
      (Real.sqrt (κ lmin lmax) + 1) / (Real.sqrt (κ lmin lmax) - 1) := by
  have hd : (0 : ℝ) < lmax - lmin := by linarith
  have hmax : (0 : ℝ) < lmax := by linarith
  have key : ∀ s S D : ℝ, 0 < s → 0 < D → s < S → D ^ 2 = S ^ 2 - s ^ 2 →
      (s / D + S / D) ^ 2 = (S / s + 1) / (S / s - 1) := by
    intro s S D hs hD hsS hD2
    have hSs : S - s ≠ 0 := sub_ne_zero.mpr hsS.ne'
    have hSs' : S + s ≠ 0 := ne_of_gt (by linarith)
    have hq : S / s - 1 ≠ 0 := (sub_pos.2 ((one_lt_div hs).2 hsS)).ne'
    have e2 : (S / s + 1) / (S / s - 1) = (S + s) / (S - s) := by field_simp
    rw [← add_div, div_pow, hD2, e2, show S ^ 2 - s ^ 2 = (S - s) * (S + s) by ring,
      div_eq_div_iff (mul_ne_zero hSs hSs') hSs]
    ring
  have h1 : Real.sqrt (η lmin lmax) = Real.sqrt lmin / Real.sqrt (lmax - lmin) := by
    rw [η, Real.sqrt_div hl.le]
  have h2 : Real.sqrt (η lmin lmax + 1) = Real.sqrt lmax / Real.sqrt (lmax - lmin) := by
    rw [show η lmin lmax + 1 = lmax / (lmax - lmin) by rw [η]; field_simp; ring,
      Real.sqrt_div hmax.le]
  have h3 : Real.sqrt (κ lmin lmax) = Real.sqrt lmax / Real.sqrt lmin := by
    rw [κ, Real.sqrt_div hmax.le]
  rw [h1, h2, h3]
  exact key _ _ _ (Real.sqrt_pos.2 hl) (Real.sqrt_pos.2 hd) (Real.sqrt_lt_sqrt hl.le hll)
    (by rw [Real.sq_sqrt hd.le, Real.sq_sqrt hmax.le, Real.sq_sqrt hl.le])

/-- **(6.128)**: `‖x_* - x_m‖_A ≤ 2 ((√κ - 1)/(√κ + 1))^m ‖x_* - x_0‖_A`, `κ = λ_max/λ_min`.
Unlike (6.123) this needs no strict spectral gap. -/
theorem eq_6_128 [NeZero n] (hA : A.PosDef) (hstar : op A xstar = b) (m : ℕ) :
    anorm A (xstar - cgX A b x₀ m) ≤
      2 * ((Real.sqrt (κ (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) - 1) /
        (Real.sqrt (κ (⨅ i, hA.1.eigenvalues i) (⨆ i, hA.1.eigenvalues i)) + 1)) ^ m *
        anorm A (xstar - x₀) := by
  rw [anorm_eq, anorm_eq, κ]
  exact Krylov.IsGalerkinIterate.energyNorm_error_le (iInf_eigenvalues_pos A hA)
    (iInf_eigenvalues_le_iSup A hA) (isSymmetricBoundedBy_op A hA)
    (cgX_isGalerkinIterate hA m) hstar

end ConjugateGradient

/-! ### §6.11.4: convergence of GMRES -/

section GMRESConvergence

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

open scoped Matrix Matrix.Norms.L2Operator

/-- The symmetric part `(A + Aᵀ)/2` of Theorem 6.30. -/
noncomputable def symmPart (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2⁻¹ : ℝ) • (A + Aᵀ)

/-- `(A + Aᵀ)/2` is symmetric. -/
theorem symmPart_isHermitian (A : Matrix (Fin n) (Fin n) ℝ) : (symmPart A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm, symmPart]
  simp [Matrix.transpose_add, add_comm]

private theorem op_symmPart (A : Matrix (Fin n) (Fin n) ℝ) :
    op (symmPart A) = (2⁻¹ : ℝ) • (op A + LinearMap.adjoint (op A)) := by
  have h : Matrix.toEuclideanLin ((2⁻¹ : ℝ) • (A + Aᴴ)) =
      (2⁻¹ : ℝ) • (Matrix.toEuclideanLin A + LinearMap.adjoint (Matrix.toEuclideanLin A)) := by
    rw [map_smul, map_add, Matrix.toEuclideanLin_conjTranspose]
  rw [symmPart, show (Aᵀ : Matrix (Fin n) (Fin n) ℝ) = Aᴴ from
    (Matrix.conjTranspose_eq_transpose_of_trivial A).symm]
  exact h

/-- The book's hypothesis `(A x, x) > 0` only sees the symmetric part of `A`. -/
private theorem inner_op_symmPart (A : Matrix (Fin n) (Fin n) ℝ) (x : 𝔼) :
    inner ℝ (op (symmPart A) x) x = inner ℝ (op A x) x := by
  rw [op_symmPart, LinearMap.smul_apply, LinearMap.add_apply, real_inner_smul_left,
    inner_add_left, LinearMap.adjoint_inner_left, real_inner_comm x (op A x)]
  ring

/-- Theorem 6.30's hypothesis, "`A` is positive definite" in the book's sense
(`(A x, x) > 0` for real `x ≠ 0`), makes `(A + Aᵀ)/2` a positive definite matrix. -/
theorem symmPart_posDef (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) :
    (symmPart A).PosDef := by
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.2 (symmPart_isHermitian A), ?_⟩
  rw [LinearMap.isCoercive_iff_forall_pos]
  intro x hx
  simpa [inner_op_symmPart] using hA x hx

variable (A)

/-- The coercivity constant of Theorem 6.30 is `μ = λ_min((A + Aᵀ)/2)`: the quadratic form of `A`
is that of its symmetric part, whose smallest eigenvalue bounds it below. -/
theorem isCoerciveWith_op [NeZero n] :
    (op A).IsCoerciveWith (⨅ i, (symmPart_isHermitian A).eigenvalues i) := by
  have hbdd := Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin (symmPart_isHermitian A)
    (lmin := ⨅ i, (symmPart_isHermitian A).eigenvalues i)
    (lmax := ⨆ i, (symmPart_isHermitian A).eigenvalues i) fun i => ⟨ciInf_le' i, le_ciSup' i⟩
  intro x
  simpa [inner_op_symmPart] using hbdd.le_re_inner x

/-- `0 < μ`: the coercivity constant of Theorem 6.30 is positive. -/
theorem iInf_eigenvalues_symmPart_pos [NeZero n]
    (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) :
    0 < ⨅ i, (symmPart_isHermitian A).eigenvalues i := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero (NeZero.ne n))
  exact lt_ciInf_of_forall fun i =>
    eigenvalues_pos_of_posDef (symmPart_posDef hA) (symmPart_isHermitian A) i

/-- A matrix positive definite in the book's sense is nonsingular. -/
theorem isUnit_of_forall_inner_pos (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) : IsUnit A := by
  have hco : (op A).IsCoercive := by
    rw [LinearMap.isCoercive_iff_forall_pos]
    intro x hx
    simpa using hA x hx
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  have h : op A (WithLp.toLp 2 u) = op A (WithLp.toLp 2 v) := by
    simp only [Matrix.toLpLin_apply]
    rw [huv]
  simpa using congrArg WithLp.ofLp (hco.injective h)

variable {A}

/-- The residual after one cycle of GMRES(m) is the minimal one over `x + 𝒦_m`: the book's rule
"if `h_{j+1,j} = 0` then set `m := j`" stops the Arnoldi process only once `𝒦_m` has been
exhausted, so the truncated cycle still minimizes over the whole of `𝒦_m`. -/
theorem gmres_isMinResIterate (hAu : IsUnit A) (b y : 𝔼) (m : ℕ) :
    Krylov.IsMinResIterate (op A) b y m (gmres A b y m) := by
  have hsub : Krylov.subspace (op A) (b - op A y) (mEff A b y m) =
      Krylov.subspace (op A) (b - op A y) m := by
    rw [mEff, grade_v₁]
    rcases le_total m (Krylov.grade (op A) (r₀ A b y)) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Krylov.subspace_eq_of_grade_le (op A) (b - op A y) h]
  have h := gmresFixed_isMinResIterate A b y (mEff_le A b y m)
    (isUnit_R_of_isUnit A b y hAu (mEff_le A b y m))
  have hg : gmres A b y m = gmresFixed A b y (mEff A b y m) := rfl
  rw [hg]
  exact ⟨hsub ▸ h.mem, fun z hz => h.min z (hsub ▸ hz)⟩

/-- The coercivity inequality `c ‖x‖ ≤ ‖A x‖`, which turns a residual bound into an error
bound. -/
private theorem mul_norm_le_norm_op {c : ℝ} (hc : (op A).IsCoerciveWith c) (z : 𝔼) :
    c * ‖z‖ ≤ ‖op A z‖ := by
  have h1 : c * ‖z‖ ^ 2 ≤ inner ℝ (op A z) z := by simpa using hc z
  have h2 : (inner ℝ (op A z) z : ℝ) ≤ ‖op A z‖ * ‖z‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h, mul_zero]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_right (by nlinarith) h

/-- Each cycle of GMRES(m) is a minimal-residual iterate over `𝒦_m` from the previous one. -/
private theorem restarted_isMinResIterate (hAu : IsUnit A) (b x₀ : 𝔼) (m k : ℕ) :
    Krylov.IsMinResIterate (op A) b (gmresRestarted A b m x₀ k) m
      (gmresRestarted A b m x₀ (k + 1)) := by
  have h : gmresRestarted A b m x₀ (k + 1) = gmres A b (gmresRestarted A b m x₀ k) m :=
    Function.iterate_succ_apply' _ _ _
  rw [h]
  exact gmres_isMinResIterate hAu b _ m

/-- **Theorem 6.30**, the rate: each cycle of GMRES(m) reduces the residual by at least the
factor `√(1 - μ²/σ²)`, with `μ = λ_min((A + Aᵀ)/2)` and `σ = ‖A‖₂` — the book's (5.15), since one
cycle is at least as good as one minimal-residual step. -/
theorem thm_6_30_rate [NeZero n] (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) (b x₀ : 𝔼)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ‖b - op A (gmresRestarted A b m x₀ (k + 1))‖ ≤
      Real.sqrt (1 - (⨅ i, (symmPart_isHermitian A).eigenvalues i) ^ 2 / ‖A‖ ^ 2) *
        ‖b - op A (gmresRestarted A b m x₀ k)‖ := by
  have h := Krylov.IsMinResIterate.norm_residual_le_of_isCoerciveWith
    (A := LinearMap.toContinuousLinearMap (op A)) (iInf_eigenvalues_symmPart_pos A hA)
    (isCoerciveWith_op A) hm
    (restarted_isMinResIterate (isUnit_of_forall_inner_pos A hA) b x₀ m k)
  rwa [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]

/-- **Theorem 6.30**: if `A` is positive definite in the book's sense — `(A x, x) > 0` for every
real `x ≠ 0`, equivalently `(A + Aᵀ)/2` symmetric positive definite — then GMRES(m) converges to
the solution for every `m ≥ 1`.

This is the backbone's `Krylov.restarted_minRes_tendsto`: a cycle of Algorithm 6.11 satisfies the
per-cycle minimal-residual specification (`gmres_isMinResIterate`), and coercivity turns the
convergence of the residuals into convergence of the iterates. -/
theorem thm_6_30 [NeZero n] (hA : ∀ x : 𝔼, x ≠ 0 → 0 < inner ℝ (op A x) x) (b x₀ xstar : 𝔼)
    (hstar : op A xstar = b) {m : ℕ} (hm : 1 ≤ m) :
    Filter.Tendsto (fun k => gmresRestarted A b m x₀ k) Filter.atTop (nhds xstar) := by
  have hc := iInf_eigenvalues_symmPart_pos A hA
  have hco := isCoerciveWith_op A
  have hres : Filter.Tendsto (fun k => ‖b - op A (gmresRestarted A b m x₀ k)‖)
      Filter.atTop (nhds 0) :=
    Krylov.restarted_minRes_tendsto (A := LinearMap.toContinuousLinearMap (op A)) hc hco hm _
      (restarted_isMinResIterate (isUnit_of_forall_inner_pos A hA) b x₀ m)
  have hbound : ∀ k, ‖gmresRestarted A b m x₀ k - xstar‖ ≤
      ‖b - op A (gmresRestarted A b m x₀ k)‖ /
        ⨅ i, (symmPart_isHermitian A).eigenvalues i := by
    intro k
    rw [le_div_iff₀ hc]
    calc ‖gmresRestarted A b m x₀ k - xstar‖ * ⨅ i, (symmPart_isHermitian A).eigenvalues i
        = (⨅ i, (symmPart_isHermitian A).eigenvalues i) *
            ‖gmresRestarted A b m x₀ k - xstar‖ := mul_comm _ _
      _ ≤ ‖op A (gmresRestarted A b m x₀ k - xstar)‖ := mul_norm_le_norm_op hco _
      _ = ‖b - op A (gmresRestarted A b m x₀ k)‖ := by rw [map_sub, hstar, norm_sub_rev]
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _) hbound
    (by simpa using hres.div_const (⨅ i, (symmPart_isHermitian A).eigenvalues i)))

/-- **Lemma 6.31**: the `m`-th GMRES iterate is `x_m = x_0 + q_m(A) r_0` with `deg q_m < m`, its
residual is `(I - A q_m(A)) r_0`, and `q_m` minimizes `‖(I - A q(A)) r_0‖₂` over the polynomials
of degree `< m`. -/
theorem lemma_6_31 (b x₀ : 𝔼) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ∃ q : ℝ[X], q.degree < m ∧
      gmresFixed A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) ∧
      ‖b - op A (gmresFixed A b x₀ m)‖ =
        ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (r₀ A b x₀)‖ ∧
      ∀ q' : ℝ[X], q'.degree < m →
        ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q) (r₀ A b x₀)‖ ≤
          ‖((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) q') (r₀ A b x₀)‖ := by
  have hx := gmresFixed_isMinResIterate A b x₀ hm hR
  obtain ⟨q, hq, hqe⟩ := (Krylov.mem_subspace_iff_exists_aeval (op A) (b - op A x₀)).1 hx.mem
  have hres : ∀ p : ℝ[X], b - op A (x₀ + Polynomial.aeval (op A) p (r₀ A b x₀)) =
      ((1 : 𝔼 →ₗ[ℝ] 𝔼) - op A ∘ₗ Polynomial.aeval (op A) p) (r₀ A b x₀) := by
    intro p
    have hr : r₀ A b x₀ = b - op A x₀ := rfl
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply, map_add, hr]
    abel
  have hxeq : gmresFixed A b x₀ m = x₀ + Polynomial.aeval (op A) q (r₀ A b x₀) :=
    sub_eq_iff_eq_add'.1 hqe.symm
  refine ⟨q, hq, hxeq, by rw [hxeq, hres q], fun q' hq' => ?_⟩
  rw [← hres q, ← hres q', ← hxeq]
  refine hx.min _ ?_
  rw [add_sub_cancel_left]
  exact Krylov.aeval_apply_mem_subspace (op A) _ hq'

end GMRESConvergence

/-! ### Proposition 6.32: diagonalizable matrices -/

section Diagonalizable

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

open scoped Matrix Matrix.Norms.L2Operator

/-- `ε^{(m)} = min_{p ∈ P_m, p(0) = 1} max_i |p(λ_i)|` of Proposition 6.32. -/
noncomputable def epsMin (lam : Fin n → ℂ) (m : ℕ) : ℝ :=
  ⨅ p : {p : ℂ[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (lam i)‖

private theorem degree_one_le (m : ℕ) : (1 : ℂ[X]).degree ≤ (m : WithBot ℕ) :=
  Polynomial.natDegree_le_iff_degree_le.1 (by simp)

private instance nonempty_consistent (m : ℕ) :
    Nonempty {p : ℂ[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1} :=
  ⟨⟨1, degree_one_le m, by simp⟩⟩

private theorem aeval_diagonal (d : Fin n → ℂ) (p : ℂ[X]) :
    Polynomial.aeval (Matrix.diagonal d) p = Matrix.diagonal fun i => p.eval (d i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Matrix.diagonal_add]; simp
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Matrix.diagonal_pow, Matrix.algebraMap_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Polynomial.eval_monomial]

private theorem aeval_conj {P Q D : Matrix (Fin n) (Fin n) ℂ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (p : ℂ[X]) : Polynomial.aeval (P * D * Q) p = P * Polynomial.aeval D p * Q := by
  have hpow : ∀ k : ℕ, (P * D * Q) ^ k = P * D ^ k * Q := by
    intro k
    induction k with
    | zero => simp [hPQ]
    | succ k ih =>
      calc (P * D * Q) ^ (k + 1) = P * D ^ k * Q * (P * D * Q) := by rw [pow_succ, ih]
        _ = P * D ^ k * (Q * P) * D * Q := by simp only [mul_assoc]
        _ = P * D ^ (k + 1) * Q := by rw [hQP, mul_one, pow_succ, mul_assoc P (D ^ k) D]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, hpow k]
    simp only [mul_assoc]
    rw [← mul_assoc, Algebra.commutes, mul_assoc]

private theorem norm_op_apply_le (A : Matrix (Fin n) (Fin n) ℂ) (x : 𝔼) :
    ‖op A x‖ ≤ ‖A‖ * ‖x‖ := by
  rw [Matrix.l2_opNorm_eq_norm_toEuclideanLin A]
  exact (LinearMap.toContinuousLinearMap (op A)).le_opNorm x

private theorem norm_le_iSup (d : Fin n → ℂ) : ‖d‖ ≤ ⨆ i, ‖d i‖ :=
  (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg (d i))).2
    fun i => le_ciSup (Finite.bddAbove_range fun j => ‖d j‖) i

/-- The surface ingredient of Proposition 6.32: for `A = X Λ X⁻¹` with `Λ` diagonal,
`‖p(A) y‖₂ ≤ κ₂(X) max_i |p(λ_i)| ‖y‖₂`. The backbone's `norm_aeval_apply_le_of_conj`
(`Numlib/Krylov/Convergence/Polynomial.lean`) covers the case of a real spectrum; here `Λ` is
complex, and `p(Λ)` is the diagonal matrix with entries `p(λ_i)`. -/
theorem norm_aeval_diagonal_mulVec_le {A : Matrix (Fin n) (Fin n) ℂ}
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X) (lam : Fin n → ℂ)
    (hA : A = X * Matrix.diagonal lam * X⁻¹) (p : ℂ[X]) (y : 𝔼) :
    ‖Polynomial.aeval (op A) p y‖ ≤ ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖y‖ := by
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  have hp : Polynomial.aeval A p = X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹ := by
    rw [hA, aeval_conj (Matrix.mul_nonsing_inv X hdet) (Matrix.nonsing_inv_mul X hdet),
      aeval_diagonal]
  have hdiag : ‖Matrix.diagonal fun i => p.eval (lam i)‖ ≤ ⨆ i, ‖p.eval (lam i)‖ := by
    rw [Matrix.l2_opNorm_diagonal]
    exact norm_le_iSup _
  have hsub : ‖X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹‖ ≤
      ‖X‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖X⁻¹‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hdiag (norm_nonneg X)))
      (norm_nonneg _))
  rw [← op_aeval, hp]
  calc ‖op (X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹) y‖
      ≤ ‖X * Matrix.diagonal (fun i => p.eval (lam i)) * X⁻¹‖ * ‖y‖ := norm_op_apply_le _ _
    _ ≤ ‖X‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖X⁻¹‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right hsub (norm_nonneg _)
    _ = ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.eval (lam i)‖) * ‖y‖ := by ring

/-- **Proposition 6.32**: for a diagonalizable `A = X Λ X⁻¹` with `Λ = diag(λ_1, …, λ_n)`, the
`m`-th GMRES residual satisfies `‖r_m‖₂ ≤ κ₂(X) ε^{(m)} ‖r_0‖₂`, `κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂`. -/
theorem prop_6_32 {A : Matrix (Fin n) (Fin n) ℂ} (b x₀ : 𝔼) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (lam : Fin n → ℂ) (hA : A = X * Matrix.diagonal lam * X⁻¹) {m : ℕ}
    (hm : m ≤ grade A (v₁ A b x₀)) (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ ≤ ‖X‖ * ‖X⁻¹‖ * epsMin lam m * ‖r₀ A b x₀‖ := by
  have hx := gmresFixed_isMinResIterate A b x₀ hm hR
  have key : ∀ p : {p : ℂ[X] // p.degree ≤ (m : WithBot ℕ) ∧ p.eval 0 = 1},
      ‖b - op A (gmresFixed A b x₀ m)‖ ≤
        ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * ⨆ i, ‖p.1.eval (lam i)‖ := by
    intro p
    calc ‖b - op A (gmresFixed A b x₀ m)‖ ≤ ‖Polynomial.aeval (op A) p.1 (r₀ A b x₀)‖ :=
          hx.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2
      _ ≤ ‖X‖ * ‖X⁻¹‖ * (⨆ i, ‖p.1.eval (lam i)‖) * ‖r₀ A b x₀‖ :=
          norm_aeval_diagonal_mulVec_le X hX lam hA p.1 (r₀ A b x₀)
      _ = ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * ⨆ i, ‖p.1.eval (lam i)‖ := by ring
  have hgoal : ‖b - op A (gmresFixed A b x₀ m)‖ ≤
      ‖X‖ * ‖X⁻¹‖ * ‖r₀ A b x₀‖ * epsMin lam m := le_mul_ciInf (by positivity) key
  exact hgoal.trans_eq (by rw [epsMin]; ring)

end Diagonalizable

end SaadSparse.Ch06
