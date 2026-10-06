import Numlib.Eigen.JacobiDavidson
import Numlib.Eigen.SymmetricPencil
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.6: Jacobi–Davidson and related methods

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.6:
the approximate Newton framework (10.6.1)–(10.6.10), the Jacobi orthogonal component correction
(10.6.11)–(10.6.15), Davidson's method (10.6.16), the Jacobi–Davidson correction (10.6.17)–(10.6.19)
and framework, and the trace-min principle.

## Conventions

`A : Matrix (Fin n) (Fin n) ℝ`; vectors are `Fin n → ℝ` where only algebra enters and
`EuclideanSpace ℝ (Fin n)` where derivatives and norms do. The eigenpair residuals are the
backbone's `ContinuousLinearMap.eigenpairResidual` (normalization `wᵀ x = 1`) and
`ContinuousLinearMap.eigenpairResidualSphere` (normalization `xᵀ x = 1`) of
`Matrix.toEuclideanCLM A`. The bordered matrix `A = [α cᵀ; c A₁]` of (10.6.11) is
`borderedMatrix α c A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ` and `[1; z]` is `Fin.cons 1 z`.

Davidson's method and the Jacobi–Davidson framework share one program, `subspaceExpansion`, with the
correction step and the choice of Ritz pair as arguments: `davidson` passes the diagonal solve of
(10.6.16) and `e₁`, `jacobiDavidson` a caller-supplied solver of (10.6.19) (a Chapter 11 iterative
method, convention 5) and any unit start. The basis `V_k` is the family `v 0, …, v (k − 1)` of the
state (`basisCols` as a matrix), its span `ran V_k` a `Submodule.span` in
`EuclideanSpace ℝ (Fin n)`.

## Not formalized

No convergence claim is made by the book and none is formalized; the trace-min iteration of
§10.6.5 is a sketch without a claim; restarting the Davidson and Jacobi–Davidson loops (mentioned
only) is not formalized.
-/

open scoped Matrix InnerProductSpace
open Krylov
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### The approximate Newton framework (§10.6.1) -/

/-- **(10.6.1)**: if `A (x_c + δx) = (λ_c + δl)(x_c + δx)` then
`(A − λ_c I) δx − δl x_c = −r_c + δl δx` with `r_c = A x_c − λ_c x_c`. -/
theorem equation_10_6_1 (A : Matrix (Fin n) (Fin n) ℝ) {x δx : Fin n → ℝ} {μ δμ : ℝ}
    (h : A *ᵥ (x + δx) = (μ + δμ) • (x + δx)) :
    (A - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) + δμ • δx := by
  rw [Matrix.mulVec_add, add_smul, smul_add, smul_add] at h
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h' : A *ᵥ δx = μ • x + μ • δx + (δμ • x + δμ • δx) - A *ᵥ x := eq_sub_of_add_eq' h
  rw [h']
  abel

/-- **(10.6.4)**: with `x₊ = x_c + δx` (10.6.3), if `wᵀ x₊ = 1` and `wᵀ x_c = 1` then
`wᵀ δx = 0`. -/
theorem equation_10_6_4 {w x δx : Fin n → ℝ} (hplus : w ⬝ᵥ (x + δx) = 1) (hc : w ⬝ᵥ x = 1) :
    w ⬝ᵥ δx = 0 := by
  rw [dotProduct_add, hc] at hplus
  linarith

/-- **(10.6.5)**: the bordered system `[A − λ_c I, −x_c; wᵀ, 0] [δx; δl] = −[r_c; 0]` is the Newton
system of `F([x; λ]) = [A x − λ x; wᵀ x − 1]` at `(x_c, λ_c)` when `wᵀ x_c = 1`: `(δx, δl)` solves
it iff `F'(x_c, λ_c)(δx, δl) = −F(x_c, λ_c)`. Backbone
`ContinuousLinearMap.hasFDerivAt_eigenpairResidual` with `ℓ = ⟪w, ·⟫`. -/
theorem equation_10_6_5 (A : Matrix (Fin n) (Fin n) ℝ) {w x : EuclideanSpace ℝ (Fin n)}
    (hwx : ⟪w, x⟫_ℝ = 1) (μ : ℝ) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let F := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).eigenpairResidual (innerSL ℝ w)
    fderiv ℝ F (x, μ) (δx, δμ) = -F (x, μ) ↔
      (Matrix.toEuclideanLin A δx - μ • δx - δμ • x = -(Matrix.toEuclideanLin A x - μ • x) ∧
        ⟪w, δx⟫_ℝ = 0) := by
  intro F
  rw [((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).hasFDerivAt_eigenpairResidual
    (innerSL ℝ w) x μ).fderiv]
  simp only [F, ContinuousLinearMap.eigenpairResidual, ContinuousLinearMap.prod_apply,
    sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_apply, ContinuousLinearMap.id_apply, Prod.neg_mk, Prod.mk.injEq,
    hwx, sub_self, neg_zero, sub_apply]
  rfl

/-- The matrix inverse under `Matrix.toLin'` is the ring inverse of the endomorphism. -/
private theorem ringInverse_toLin' {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M) :
    Ring.inverse (Matrix.toLin' M) = Matrix.toLin' M⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det M).1 hM
  have h1 : Matrix.toLin' M * Matrix.toLin' M⁻¹ = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hd,
      Matrix.toLin'_one, Module.End.one_eq_id]
  have h2 : Matrix.toLin' M⁻¹ * Matrix.toLin' M = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hd,
      Matrix.toLin'_one, Module.End.one_eq_id]
  have hu : IsUnit (Matrix.toLin' M) := ⟨⟨_, _, h1, h2⟩, rfl⟩
  have := (Ring.inverse_mul_eq_iff_eq_mul _ 1 (Matrix.toLin' M⁻¹) hu).2 h1.symm
  rwa [mul_one] at this

/-- The bordered system in closed form, for a matrix `M` in the operator slot: the common form of
(10.6.7) (`M = A`) and (10.6.10) (`M` the approximation of `A`). Backbone
`JacobiDavidson.newtonCorrection_eq`. -/
private theorem bordered_iff {M : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} (hM : IsUnit (M - μ • 1))
    {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x) ≠ 0) (r δx : Fin n → ℝ) (δμ : ℝ) :
    ((M - μ • 1) *ᵥ δx - δμ • x = -r ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ r)) / (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((M - μ • 1)⁻¹ *ᵥ (r - δμ • x))) := by
  have hT : Matrix.toLin' M - μ • 1 = Matrix.toLin' (M - μ • 1) := by
    rw [map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
  have hU : IsUnit (Matrix.toLin' M - μ • 1) := by
    rw [hT]
    obtain ⟨u, hu⟩ := hM
    exact ⟨⟨Matrix.toLin' u, Matrix.toLin' ↑u⁻¹, by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, u.mul_inv, Matrix.toLin'_one,
        Module.End.one_eq_id], by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, u.inv_mul, Matrix.toLin'_one,
        Module.End.one_eq_id]⟩, by rw [← hu]⟩
  have hR : Ring.inverse (Matrix.toLin' M - μ • 1) = Matrix.toLin' (M - μ • 1)⁻¹ := by
    rw [hT, ringInverse_toLin' hM]
  have h := JacobiDavidson.newtonCorrection_eq hU (dotProductBilin ℝ ℝ w) (x := x)
    (by rw [hR]; simpa using hx) r δx δμ
  rw [hR, hT] at h
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using h

/-- **(10.6.6)–(10.6.7)**: if `A − λ_c I` is nonsingular and `wᵀ (A − λ_c I)⁻¹ x_c ≠ 0`, the
bordered system (10.6.5) has exactly one solution, `δl = wᵀ(A − λ_c I)⁻¹ r_c / wᵀ(A − λ_c I)⁻¹ x_c`,
`δx = −(A − λ_c I)⁻¹ (r_c − δl x_c)`. Backbone `JacobiDavidson.newtonCorrection_eq`. -/
theorem equation_10_6_7 {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} (hA : IsUnit (A - μ • 1))
    {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ x) ≠ 0) (δx : Fin n → ℝ) (δμ : ℝ) :
    ((A - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ (A *ᵥ x - μ • x))) / (w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((A - μ • 1)⁻¹ *ᵥ ((A *ᵥ x - μ • x) - δμ • x))) :=
  bordered_iff hA hx _ δx δμ

/-- **(10.6.8)–(10.6.10)**, the approximate Newton correction: with `M ≈ A` in the operator slot
(`N = M − A`, the term `N δx` dropped) the solution of (10.6.8) is
`δl = wᵀ(M − λ_c I)⁻¹ r_c / wᵀ(M − λ_c I)⁻¹ x_c`, `δx = −(M − λ_c I)⁻¹ (r_c − δl x_c)`, the right
side still `r_c = A x_c − λ_c x_c`. The same lemma `JacobiDavidson.newtonCorrection_eq`. -/
theorem equation_10_6_10 (A : Matrix (Fin n) (Fin n) ℝ) {M : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hM : IsUnit (M - μ • 1)) {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x) ≠ 0)
    (δx : Fin n → ℝ) (δμ : ℝ) :
    ((M - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ (A *ᵥ x - μ • x))) / (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((M - μ • 1)⁻¹ *ᵥ ((A *ᵥ x - μ • x) - δμ • x))) :=
  bordered_iff hM hx _ δx δμ

/-! ### The Jacobi orthogonal component correction (§10.6.2) -/

/-- The bordered matrix `A = [α cᵀ; c A₁]` of (10.6.11). -/
def borderedMatrix (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases α c j) (fun i' => Fin.cases (c i') (A₁ i') j) i

/-- `[α cᵀ; c A₁] [t; z] = [α t + cᵀ z; t c + A₁ z]`. -/
theorem borderedMatrix_mulVec_cons (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (z : Fin n → ℝ) :
    borderedMatrix α c A₁ *ᵥ Fin.cons t z = Fin.cons (α * t + c ⬝ᵥ z) (t • c + A₁ *ᵥ z) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [borderedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [borderedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

/-- **(10.6.15)**: with `λ_k = α + cᵀ z_k` and `x_k = [1; z_k]`,
`r_k = (A − λ_k I) x_k = [0; (A₁ − λ_k I) z_k + c]`: the first component vanishes. -/
theorem equation_10_6_15 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) :
    (borderedMatrix α c A₁ - (α + c ⬝ᵥ z) • 1) *ᵥ Fin.cons 1 z =
      Fin.cons 0 ((A₁ - (α + c ⬝ᵥ z) • 1) *ᵥ z + c) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    borderedMatrix_mulVec_cons, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_succ, Pi.add_apply, smul_eq_mul]
    ring

/-! ### The Jacobi–Davidson correction (§10.6.4) -/

/-- **(10.6.17)**: for `x_cᵀ x_c = 1`, the system `[A − λ_c I, −x_c; x_cᵀ, 0] [δx; δl] = −[r_c; 0]`
is the Newton system of `F([x; λ]) = [A x − λ x; (xᵀx − 1)/2]` at `(x_c, λ_c)`. Backbone
`ContinuousLinearMap.hasFDerivAt_eigenpairResidualSphere`. -/
theorem equation_10_6_17 (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (μ : ℝ) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let F := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).eigenpairResidualSphere
    fderiv ℝ F (x, μ) (δx, δμ) = -F (x, μ) ↔
      (Matrix.toEuclideanLin A δx - μ • δx - δμ • x = -(Matrix.toEuclideanLin A x - μ • x) ∧
        ⟪x, δx⟫_ℝ = 0) := by
  intro F
  rw [((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).hasFDerivAt_eigenpairResidualSphere
    x μ).fderiv]
  simp only [F, ContinuousLinearMap.eigenpairResidualSphere, ContinuousLinearMap.prod_apply,
    sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_apply, ContinuousLinearMap.id_apply, Prod.neg_mk, Prod.mk.injEq,
    hx, one_pow, sub_self, zero_div, neg_zero]
  rfl

/-- **(10.6.18)**: if `‖x_c‖ = 1` and `λ_c = x_cᵀ A x_c`, then `(δx, δl)` solves (10.6.17) iff `x_cᵀ
δx = 0`, `(I − x_c x_cᵀ)(A − λ_c I)(I − x_c x_cᵀ) δx = −r_c` and `δl = x_cᵀ (A − λ_c I) δx`. The
book derives `⇒`; `⇐` is what "the correction is obtained by solving the projected system" uses.
Backbone `JacobiDavidson.newtonStep_iff_projected`, with `I − x_c x_cᵀ` the orthogonal projection
onto `x_c^⊥`. -/
theorem equation_10_6_18 (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let T := Matrix.toEuclideanLin A
    let μ := ⟪x, T x⟫_ℝ
    let P := (ℝ ∙ x)ᗮ.starProjection
    ((T - μ • 1) δx - δμ • x = -(T x - μ • x) ∧ ⟪x, δx⟫_ℝ = 0) ↔
      (⟪x, δx⟫_ℝ = 0 ∧ P ((T - μ • 1) (P δx)) = -(T x - μ • x) ∧
        δμ = ⟪x, (T - μ • 1) δx⟫_ℝ) := by
  intro T μ P
  have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have hr : ⟪x, T x - μ • x⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hxx, mul_one, sub_self]
  -- the multiplier of any solution of the bordered system
  have hmult : ∀ δμ', (T - μ • 1) δx - δμ' • x = -(T x - μ • x) →
      δμ' = ⟪x, (T - μ • 1) δx⟫_ℝ := fun δμ' h => by
    have := congrArg (fun y => ⟪x, y⟫_ℝ) h
    simp only [inner_sub_right, real_inner_smul_right, hxx, mul_one, inner_neg_right, hr,
      neg_zero] at this
    linarith
  have hb := JacobiDavidson.newtonStep_iff_projected T hx δx
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨h2', h3⟩ := hb.1 ⟨δμ, h1, h2⟩
    exact ⟨h2', h3, hmult δμ h1⟩
  · rintro ⟨h2, h3, h4⟩
    obtain ⟨δμ', h1', -⟩ := hb.2 ⟨h2, h3⟩
    refine ⟨?_, h2⟩
    rwa [h4, ← hmult δμ' h1']

/-- **(10.6.19)**, the Jacobi–Davidson correction: `δv` is a Jacobi–Davidson correction for the unit
Ritz vector `x_k`, the Ritz value `λ_k`, the residual `r_k` and the preconditioner `M` if
`x_kᵀ δv = 0` and `(I − x_k x_kᵀ)(M − λ_k I)(I − x_k x_kᵀ) δv = −r_k`. -/
def IsJDCorrection (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (r δv : EuclideanSpace ℝ (Fin n)) : Prop :=
  ⟪x, δv⟫_ℝ = 0 ∧
    (ℝ ∙ x)ᗮ.starProjection ((Matrix.toEuclideanLin M - μ • 1)
      ((ℝ ∙ x)ᗮ.starProjection δv)) = -r

/-- For `M = A`, a Jacobi–Davidson correction is exactly the Newton correction of (10.6.18): with
`‖x‖ = 1`, `λ = xᵀ A x` and `r = A x − λ x`, `δv` is a correction iff `(δv, xᵀ(A − λ I) δv)` solves
the bordered Newton system (10.6.17). -/
theorem isJDCorrection_self_iff (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (δv : EuclideanSpace ℝ (Fin n)) :
    IsJDCorrection A x ⟪x, Matrix.toEuclideanLin A x⟫_ℝ
        (Matrix.toEuclideanLin A x - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • x) δv ↔
      ((Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv -
          ⟪x, (Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv⟫_ℝ • x =
        -(Matrix.toEuclideanLin A x - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • x) ∧
        ⟪x, δv⟫_ℝ = 0) := by
  have h := equation_10_6_18 A hx δv
    ⟪x, (Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv⟫_ℝ
  exact ⟨fun h' => h.2 ⟨h'.1, h'.2, rfl⟩, fun h' => ⟨(h.1 h').1, (h.1 h').2.1⟩⟩

/-! ### JOCC (§10.6.2, continued) -/

/-- `(A − μ I) [t; z] = [(α − μ) t + cᵀ z; t c + (A₁ − μ I) z]` for `A = [α cᵀ; c A₁]`. -/
theorem borderedMatrix_sub_mulVec_cons (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (μ t : ℝ) (z : Fin n → ℝ) :
    (borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons t z =
      Fin.cons ((α - μ) * t + c ⬝ᵥ z) (t • c + (A₁ - μ • 1) *ᵥ z) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, borderedMatrix_mulVec_cons,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_succ, Pi.add_apply, smul_eq_mul]
    ring

/-- Vectors `[a; u]` are equal iff their parts are. -/
private theorem cons_eq_cons_iff {a b : ℝ} {u w : Fin n → ℝ} :
    (Fin.cons a u : Fin (n + 1) → ℝ) = Fin.cons b w ↔ a = b ∧ u = w :=
  Fin.cons_injective2.eq_iff

/-- **(10.6.13)** and the JOCC rearrangement: for `A = [α cᵀ; c A₁]` (10.6.11), `w = e₁`,
`x_c = [1; z_c]` and `δx = [δμ; δz]`, (a) the Newton system (10.6.5)
`(A − λ_c I) δx − δl x_c = −r_c`, `e₁ᵀ δx = 0` is equivalent to `δμ = 0` together with
`[A₁ − λ_c I, −z_c; cᵀ, −1] [δz; δl] = −[(A₁ − λ_c I) z_c + c; α + cᵀ z_c − λ_c]` (the book's first
row prints `α + + cᵀz_c`); (b) if `A₁ = M₁ − N₁` then any solution of the reduced system gives
`z₊ = z_c + δz`, `λ₊ = λ_c + δl` with `(M₁ − λ_c I) z₊ = −c + N₁ z_c + (δl z_c + N₁ δz)` and
`λ₊ = α + cᵀ z₊`. -/
theorem equation_10_6_13 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (μ δμ : ℝ) (δz : Fin n → ℝ) (δl : ℝ) :
    (((borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons δμ δz - δl • (Fin.cons 1 z : Fin (n + 1) → ℝ) =
          -((borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons 1 z) ∧
        (Fin.cons 1 0 : Fin (n + 1) → ℝ) ⬝ᵥ Fin.cons δμ δz = 0) ↔
      (δμ = 0 ∧ (A₁ - μ • 1) *ᵥ δz - δl • z = -((A₁ - μ • 1) *ᵥ z + c) ∧
        c ⬝ᵥ δz - δl = -(α + c ⬝ᵥ z - μ))) ∧
    ∀ M₁ N₁ : Matrix (Fin n) (Fin n) ℝ, A₁ = M₁ - N₁ →
      (A₁ - μ • 1) *ᵥ δz - δl • z = -((A₁ - μ • 1) *ᵥ z + c) →
      c ⬝ᵥ δz - δl = -(α + c ⬝ᵥ z - μ) →
      (M₁ - μ • 1) *ᵥ (z + δz) = -c + N₁ *ᵥ z + (δl • z + N₁ *ᵥ δz) ∧
        μ + δl = α + c ⬝ᵥ (z + δz) := by
  refine ⟨?_, fun M₁ N₁ hA h1 h2 => ⟨?_, ?_⟩⟩
  · have hsmul : δl • (Fin.cons 1 z : Fin (n + 1) → ℝ) = Fin.cons δl (δl • z) := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hsub : ∀ (a b : ℝ) (u w : Fin n → ℝ),
        (Fin.cons a u : Fin (n + 1) → ℝ) - Fin.cons b w = Fin.cons (a - b) (u - w) := by
      intro a b u w
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hneg : ∀ (a : ℝ) (u : Fin n → ℝ),
        -(Fin.cons a u : Fin (n + 1) → ℝ) = Fin.cons (-a) (-u) := by
      intro a u
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hdot : (Fin.cons 1 0 : Fin (n + 1) → ℝ) ⬝ᵥ Fin.cons δμ δz = δμ := by
      simp [dotProduct, Fin.sum_univ_succ]
    rw [borderedMatrix_sub_mulVec_cons, borderedMatrix_sub_mulVec_cons, hsmul, hsub, hneg,
      cons_eq_cons_iff, hdot]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      subst h3
      refine ⟨rfl, ?_, ?_⟩
      · rw [zero_smul, zero_add] at h2
        rw [h2, one_smul]
        abel
      · linarith
    · rintro ⟨rfl, h2, h3⟩
      refine ⟨⟨by linarith, ?_⟩, rfl⟩
      rw [zero_smul, zero_add, h2, one_smul]
      abel
  · rw [hA] at h1
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_add]
      at h1 ⊢
    rw [← sub_eq_zero] at h1 ⊢
    rw [← h1]
    module
  · rw [dotProduct_add]
    linarith

/-- The state of the JOCC iteration (10.6.14): the step counter `k` (`0`-based: the book's
`k + 1`), the iterates `z j`, the eigenvalue estimates `lam j`, the residual norms `rho j`, and the
`done` flag of the `while ρ_k > tol` loop. -/
structure JoccState (n : ℕ) where
  /-- The number of passes taken. -/
  k : ℕ
  /-- The iterates `z`, `0`-based (`z 0 = 0`). -/
  z : ℕ → Fin n → ℝ
  /-- The eigenvalue estimates `λ`, `0`-based (`lam 0 = α`). -/
  lam : ℕ → ℝ
  /-- The residual norms `ρ`, `0`-based (`rho 0 = ‖c‖₂`). -/
  rho : ℕ → ℝ
  /-- Whether the loop has stopped (`ρ_k ≤ tol`). -/
  done : Bool

/-- The off-diagonal splitting matrix `N₁ = M₁ − A₁` of JOCC, `M₁` the diagonal of `A₁`: its
entries are copies and negations of those of `A₁` (exact, convention 1). -/
def joccN (A₁ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else -A₁ i j

section Jocc

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One entry of the solve step of (10.6.14): `(w_i − c_i)/(A₁(i, i) − λ)`, one rounded difference,
one rounded shifted diagonal and one rounded quotient. -/
noncomputable def joccEntry (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ)
    (i : Fin n) : M ℝ := do
  let num ← rnd (w i - c i)
  let den ← rnd (A₁ i i - l)
  rnd (num / den)

/-- The solve step of (10.6.14), `(M₁ − λ I) z = w − c` with `M₁` the diagonal of `A₁`: entrywise
`z_i = (w_i − c_i)/(A₁(i, i) − λ)`, one rounded difference, one rounded shifted diagonal and one
rounded quotient per entry. -/
noncomputable def joccSolve (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (z : Fin n → ℝ) i => do
    let q ← joccEntry rnd A₁ w c l i
    pure (Function.update z i q)) 0

/-- One pass of (10.6.14) (a no-op once `done`): solve `(M₁ − λ_k I) z_{k+1} = −c + N₁ z_k` with
`M₁ = diag(A₁)` (entrywise, one rounded difference, one rounded shifted diagonal and one rounded
quotient per entry), `λ_{k+1} = α + cᵀ z_{k+1}`, `k = k + 1`, `ρ_k = ‖A₁ z_k − λ_k z_k + c‖₂`. -/
noncomputable def joccStep (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) (tol : ℝ)
    (s : JoccState n) : M (JoccState n) :=
  if s.done then pure s else do
    let w ← algorithm_1_1_3 rnd (joccN A₁) (s.z s.k) 0
    let z ← joccSolve rnd A₁ w c (s.lam s.k)
    let d ← algorithm_1_1_1 rnd c z
    let l ← rnd (α + d)
    let r ← algorithm_1_1_3 rnd A₁ z 0
    let r ← algorithm_1_1_2 rnd (-l) z r
    let r ← vecAdd rnd r c
    let ρ ← vecNorm rnd r
    pure
      { k := s.k + 1
        z := Function.update s.z (s.k + 1) z
        lam := Function.update s.lam (s.k + 1) l
        rho := Function.update s.rho (s.k + 1) ρ
        done := decide (ρ ≤ tol) }

/-- **(10.6.14), the Jacobi orthogonal component correction (JOCC)** for `A = [α cᵀ; c A₁]`:
```
λ_1 = α, z_1 = 0, ρ_1 = ‖c‖₂, k = 1
while ρ_k > tol
  Solve (M₁ − λ_k I) z_{k+1} = −c + N₁ z_k   (M₁ the diagonal of A₁, N₁ = M₁ − A₁)
  λ_{k+1} = α + cᵀ z_{k+1},  k = k + 1,  ρ_k = ‖A₁ z_k − λ_k z_k + c‖₂
end
```
The `while` loop is at most `fuel` passes (convention 3). -/
noncomputable def joccIteration (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (tol : ℝ) (fuel : ℕ) : M (JoccState n) := do
  let ρ ← vecNorm rnd c
  (List.range fuel).foldlM (fun s _ => joccStep rnd α c A₁ tol s)
    { k := 0, z := fun _ => 0, lam := Function.update (fun _ => 0) 0 α,
      rho := Function.update (fun _ => 0) 0 ρ, done := decide (ρ ≤ tol) }

end Jocc

/-- Exact semantics of the JOCC solve step. -/
theorem joccSolve_spec (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ) :
    Id.run (joccSolve pure A₁ w c l) = fun i => (w i - c i) / (A₁ i i - l) := by
  funext i
  rw [joccSolve, List.idRun_foldlM_update_apply (fun i (_ : ℝ) => joccEntry pure A₁ w c l i) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange i)]
  rfl

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem joccIteration_succ (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (tol : ℝ) (t : ℕ) :
    Id.run (joccIteration pure α c A₁ tol (t + 1)) =
      Id.run (joccStep pure α c A₁ tol (Id.run (joccIteration pure α c A₁ tol t))) := by
  simp only [joccIteration, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Exact semantics of (10.6.14)**: every iterate satisfies the two update equations — `(M₁ − λ_j
I) z_{j+1} = −c + N₁ z_j` whenever `M₁ − λ_j I` is nonsingular (`A₁(i,i) ≠ λ_j`), and `λ_{j+1} = α +
cᵀ z_{j+1}`; `ρ_j = ‖r_j‖₂` for the residual `r_j = (A₁ − λ_j I) z_j + c` of (10.6.15) (so `x_j =
[1; z_j]` has `(A − λ_j I) x_j = [0; r_j]`, and the corrections `x_{j+1} − x_j = [0; z_{j+1} − z_j]`
are orthogonal to `e₁`, the name of the method); and the loop stops with `ρ_k ≤ tol` or after `fuel`
passes, each pass having found `ρ > tol`. -/
theorem equation_10_6_14 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) (tol : ℝ)
    (fuel : ℕ) :
    let s := Id.run (joccIteration pure α c A₁ tol fuel)
    s.lam 0 = α ∧ s.z 0 = 0 ∧
      (∀ j ≤ s.k, s.rho j =
        ‖(WithLp.toLp 2 ((A₁ - s.lam j • 1) *ᵥ s.z j + c) : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ j < s.k, (∀ i, A₁ i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A₁ i i) - s.lam j • 1) *ᵥ s.z (j + 1) = -c + joccN A₁ *ᵥ s.z j) ∧
      (∀ j < s.k, s.lam (j + 1) = α + c ⬝ᵥ s.z (j + 1)) ∧
      (∀ j < s.k, tol < s.rho j) ∧ (s.k = fuel ∨ s.rho s.k ≤ tol) := by
  intro s
  -- the invariant after `t` passes
  let P : ℕ → JoccState n → Prop := fun t s =>
    s.k ≤ t ∧ s.lam 0 = α ∧ s.z 0 = 0 ∧
      (∀ j ≤ s.k, s.rho j =
        ‖(WithLp.toLp 2 ((A₁ - s.lam j • 1) *ᵥ s.z j + c) : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ j < s.k, (∀ i, A₁ i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A₁ i i) - s.lam j • 1) *ᵥ s.z (j + 1) = -c + joccN A₁ *ᵥ s.z j) ∧
      (∀ j < s.k, s.lam (j + 1) = α + c ⬝ᵥ s.z (j + 1)) ∧
      (∀ j < s.k, tol < s.rho j) ∧ s.done = decide (s.rho s.k ≤ tol) ∧
      (s.k = t ∨ s.done = true)
  have hP : ∀ t, P t (Id.run (joccIteration pure α c A₁ tol t)) := by
    intro t
    induction t with
    | zero =>
      simp only [P, joccIteration, Id.run_bind, vecNorm_spec, List.range_zero, List.foldlM_nil,
        Id.run_pure]
      refine ⟨le_rfl, by simp, by simp, fun j hj => ?_, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega), by simp, by simp⟩
      obtain rfl : j = 0 := by omega
      simp
    | succ t ih =>
      rw [joccIteration_succ]
      set s := Id.run (joccIteration pure α c A₁ tol t)
      obtain ⟨hkt, hl0, hz0, hrho, hupd, hlam, hgt, hdone, hfin⟩ := ih
      cases hsd : s.done with
      | true =>
        simp only [joccStep, hsd, ↓reduceIte, Id.run_pure]
        exact ⟨by omega, hl0, hz0, hrho, hupd, hlam, hgt, hsd ▸ hdone, Or.inr hsd⟩
      | false =>
        have hkt' : s.k = t := hfin.resolve_right (by simp [hsd])
        have hρ : tol < s.rho s.k := by
          have : ¬ s.rho s.k ≤ tol := by simpa [hsd] using hdone.symm
          linarith [not_le.1 this]
        set z' : Fin n → ℝ := fun i =>
          ((joccN A₁ *ᵥ s.z s.k) i - c i) / (A₁ i i - s.lam s.k) with hz'
        simp only [P, joccStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          algorithm_1_1_3_spec, zero_add, joccSolve_spec, Id.run_pure, algorithm_1_1_1_spec,
          algorithm_1_1_2_spec, vecAdd_spec, vecNorm_spec]
        rw [← hz']
        have hres : A₁ *ᵥ z' + (-(α + c ⬝ᵥ z')) • z' + c =
            (A₁ - (α + c ⬝ᵥ z') • 1) *ᵥ z' + c := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, neg_smul, sub_eq_add_neg]
        rw [hres]
        refine ⟨by omega, ?_, ?_, fun j hj => ?_, fun j hj hne => ?_, fun j hj => ?_,
          fun j hj => ?_, by simp only [Function.update_self], Or.inl (by omega)⟩
        · rw [Function.update_of_ne (by omega)]; exact hl0
        · rw [Function.update_of_ne (by omega)]; exact hz0
        · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hrho j (by omega)
          · simp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hupd j hj (by
              intro i
              have := hne i
              rwa [Function.update_of_ne (by omega)] at this)
          · rw [Function.update_of_ne (by omega), Function.update_self,
              Function.update_of_ne (by omega)]
            have hne' : ∀ i, A₁ i i - s.lam s.k ≠ 0 := fun i => sub_ne_zero.2 (by
              have := hne i
              rwa [Function.update_of_ne (by omega)] at this)
            ext i
            simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
              Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
              Pi.neg_apply, z']
            field_simp [hne' i]
            ring
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hlam j hj
          · simp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega)]
            exact hgt j hj
          · rw [Function.update_of_ne (by omega)]
            exact hρ
  obtain ⟨-, hl0, hz0, hrho, hupd, hlam, hgt, hdone, hfin⟩ := hP fuel
  refine ⟨hl0, hz0, hrho, hupd, hlam, hgt, ?_⟩
  rcases hfin with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [h] using hdone.symm)

/-! ### Davidson's method and the Jacobi–Davidson framework (§10.6.3–10.6.4) -/

/-- The state of the subspace expansion loop shared by Davidson's method (10.6.16) and the
Jacobi–Davidson framework (§10.6.4), `0`-based: after `k` passes the basis is `v 0, …, v k` (the
book's `V_{k+1}`), `lam j`, `x j` are the Ritz pair and `dv j` the correction of pass `j`, `sNorm j`
the norm `‖s‖₂` of the orthogonalized correction of pass `j`, and `r`, `rho` the current residual
and its norm. -/
structure DavidsonState (n : ℕ) where
  /-- The number of passes taken. -/
  k : ℕ
  /-- The orthonormal basis vectors, `v 0, …, v k`. -/
  v : ℕ → Fin n → ℝ
  /-- The Ritz values, `lam 0 = x₁ᵀ A x₁`. -/
  lam : ℕ → ℝ
  /-- The Ritz vectors, `x 0 = x₁`. -/
  x : ℕ → Fin n → ℝ
  /-- The corrections `δv`, one per pass. -/
  dv : ℕ → Fin n → ℝ
  /-- The norms `‖s‖₂` of the orthogonalized corrections, one per pass. -/
  sNorm : ℕ → ℝ
  /-- The current residual `r_k = A x_k − λ_k x_k`. -/
  r : Fin n → ℝ
  /-- Its norm `‖r_k‖₂`. -/
  rho : ℝ
  /-- Whether the loop has stopped (`‖r_k‖₂ ≤ tol`). -/
  done : Bool

/-- The columns `v 0, …, v (p − 1)` as the matrix `V_p = [v_1 | ⋯ | v_p]` (a copy). -/
def basisCols (v : ℕ → Fin n → ℝ) (p : ℕ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun i j => v j i

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The modified Gram–Schmidt expansion `s = (I − V_p V_pᵀ) δv` of (10.6.16) ("the transition from
`V_k` to `V_{k+1}` can be effectively carried out by a modified Gram–Schmidt process"): for
`j = 0 : p − 1` in order, `s ← s − (v_jᵀ s) v_j`, by chapter 1's dot product and saxpy. -/
noncomputable def mgsExpand (v : ℕ → Fin n → ℝ) (p : ℕ) (δ : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.range p).foldlM (fun s j => do
    let h ← algorithm_1_1_1 rnd (v j) s
    algorithm_1_1_2 rnd (-h) (v j) s) δ

/-- One entry of Davidson's correction: `−r_i / (a_ii − λ)`, one rounded difference and one rounded
quotient (the negation is exact). -/
noncomputable def davidsonEntry (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ)
    (i : Fin n) : M ℝ := do
  let d ← rnd (A i i - l)
  rnd (-r i / d)

/-- Davidson's residual correction equation `(M − λ I) δv = −r`, `M` the diagonal of `A`: entrywise
`δv_i = −r_i / (a_ii − λ)` (`davidsonEntry`). -/
noncomputable def davidsonCorrection (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (z : Fin n → ℝ) i => do
    let q ← davidsonEntry rnd A l r i
    pure (Function.update z i q)) 0

/-- One pass of the subspace expansion loop (a no-op once `done`): the correction
`δv = correct x_k λ_k r_k`, the expansion `s = (I − V V ᵀ) δv` (`mgsExpand`),
`v_{k+1} = s/‖s‖₂`, `H = V_{k+1}ᵀ A V_{k+1}` (two of chapter 1's matrix products), a Ritz pair
`(θ, t) = ritz H` of `H`, `λ_{k+1} = θ`, `x_{k+1} = V_{k+1} t`,
`r_{k+1} = A x_{k+1} − λ_{k+1} x_{k+1}` and its norm. -/
noncomputable def subspaceExpansionStep (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (tol : ℝ)
    (s : DavidsonState n) : M (DavidsonState n) :=
  if s.done then pure s else do
    let δ ← correct (s.x s.k) (s.lam s.k) s.r
    let w ← mgsExpand rnd s.v (s.k + 1) δ
    let ν ← vecNorm rnd w
    let vnew ← vecDiv rnd w ν
    let v := Function.update s.v (s.k + 1) vnew
    let AV ← algorithm_1_1_5 rnd A (basisCols v (s.k + 2)) 0
    let H ← algorithm_1_1_5 rnd (basisCols v (s.k + 2))ᵀ AV 0
    let θt ← ritz (s.k + 2) H
    let x ← algorithm_1_1_3 rnd (basisCols v (s.k + 2)) θt.2 0
    let Ax ← algorithm_1_1_3 rnd A x 0
    let r ← algorithm_1_1_2 rnd (-θt.1) x Ax
    let ρ ← vecNorm rnd r
    pure
      { k := s.k + 1
        v := v
        lam := Function.update s.lam (s.k + 1) θt.1
        x := Function.update s.x (s.k + 1) x
        dv := Function.update s.dv s.k δ
        sNorm := Function.update s.sNorm s.k ν
        r := r
        rho := ρ
        done := decide (ρ ≤ tol) }

/-- The subspace expansion loop shared by (10.6.16) and §10.6.4, from a starting vector `x₁`:
`λ_1 = x₁ᵀ A x₁`, `r_1 = A x₁ − λ_1 x₁`, `V_1 = [x₁]`, then `while ‖r_k‖ > tol` the pass
`subspaceExpansionStep` with the correction `correct` and the Ritz selector `ritz`, at most `fuel`
passes (convention 3). -/
noncomputable def subspaceExpansion (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (DavidsonState n) := do
  let Ax ← algorithm_1_1_3 rnd A x₁ 0
  let l ← algorithm_1_1_1 rnd x₁ Ax
  let r ← algorithm_1_1_2 rnd (-l) x₁ Ax
  let ρ ← vecNorm rnd r
  (List.range fuel).foldlM (fun s _ => subspaceExpansionStep rnd A correct ritz tol s)
    { k := 0, v := Function.update (fun _ => 0) 0 x₁, lam := Function.update (fun _ => 0) 0 l,
      x := Function.update (fun _ => 0) 0 x₁, dv := fun _ => 0, sNorm := fun _ => 0, r := r,
      rho := ρ, done := decide (ρ ≤ tol) }

/-- **(10.6.16), Davidson's method**:
```
x_1 = e_1, λ_1 = x_1ᵀ A x_1, r_1 = A x_1 − λ_1 x_1, V_1 = [e_1], k = 1
while ‖r_k‖ > tol
  Solve (M − λ_k I) δv_k = −r_k                  (M the diagonal of A)
  s_{k+1} = (I − V_k V_kᵀ) δv_k,  v_{k+1} = s_{k+1}/‖s_{k+1}‖₂,  V_{k+1} = [V_k | v_{k+1}]
  (V_{k+1}ᵀ A V_{k+1}) t_{k+1} = θ_{k+1} t_{k+1}  (a suitably chosen Ritz pair)
  λ_{k+1} = θ_{k+1},  x_{k+1} = V_{k+1} t_{k+1},  k = k + 1,  r_k = A x_k − λ_k x_k
end
```
The orthogonalization is modified Gram–Schmidt (the book's remark); the "suitably chosen" Ritz pair
of the small symmetric matrix is a caller-supplied selector `ritz` (the book leaves the choice
open). -/
noncomputable def davidson (A : Matrix (Fin n) (Fin n) ℝ)
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (tol : ℝ) (fuel : ℕ) :
    M (DavidsonState n) :=
  subspaceExpansion rnd A (fun _ l r => davidsonCorrection rnd A l r) ritz
    (fun i => if (i : ℕ) = 0 then 1 else 0) tol fuel

/-- **The Jacobi–Davidson framework** (§10.6.4): (10.6.16) with the Davidson correction replaced
by the solution of the projected correction equation (10.6.19), `(I − x_k x_kᵀ)(M − λ_k I)(I −
x_k x_kᵀ) δv_k = −r_k` with `x_kᵀ δv_k = 0`, computed by a caller-supplied solver
`solve x_k λ_k r_k` ("various Chapter 11 iterative solvers can be applied", convention 5), from
an arbitrary unit starting vector `x₁`. -/
noncomputable def jacobiDavidson (A : Matrix (Fin n) (Fin n) ℝ)
    (solve : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (DavidsonState n) :=
  subspaceExpansion rnd A solve ritz x₁ tol fuel

end Programs

/-! #### Exact semantics -/

/-- Exact semantics of the MGS expansion: against an orthonormal family `v 0, …, v (p − 1)` it is
the classical projection `δ − ∑_{j<p} (v_jᵀ δ) v_j` (MGS and CGS agree in exact arithmetic,
`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`). -/
theorem mgsExpand_spec {v : ℕ → Fin n → ℝ} {p : ℕ}
    (hv : ∀ i < p, ∀ j < p, v i ⬝ᵥ v j = if i = j then 1 else 0) (δ : Fin n → ℝ) :
    Id.run (mgsExpand pure v p δ) = δ - ∑ j ∈ Finset.range p, (v j ⬝ᵥ δ) • v j := by
  induction p with
  | zero => simp [mgsExpand]
  | succ p ih =>
    have ih' := ih (fun i hi j hj => hv i (by omega) j (by omega))
    have hstep : Id.run (mgsExpand pure v (p + 1) δ) =
        Id.run (mgsExpand pure v p δ) -
          (v p ⬝ᵥ Id.run (mgsExpand pure v p δ)) • v p := by
      simp only [mgsExpand, List.range_succ, List.foldlM_append, List.foldlM_cons,
        List.foldlM_nil, bind_pure, Id.run_bind, algorithm_1_1_1_spec, algorithm_1_1_2_spec]
      rw [neg_smul, ← sub_eq_add_neg]
    rw [hstep, ih', Finset.sum_range_succ]
    have hdot : v p ⬝ᵥ (δ - ∑ j ∈ Finset.range p, (v j ⬝ᵥ δ) • v j) = v p ⬝ᵥ δ := by
      rw [dotProduct_sub, dotProduct_sum]
      rw [Finset.sum_eq_zero fun j hj => by
        rw [dotProduct_smul, hv p (by omega) j (by simp at hj; omega),
          ite_eq_right (by simp at hj; omega), smul_zero], sub_zero]
    rw [hdot]
    abel

/-- Exact semantics of Davidson's correction: `δv_i = −r_i/(a_ii − λ)`, so `(M − λ I) δv = −r`
whenever `a_ii ≠ λ` for all `i` (`M` the diagonal of `A`). -/
theorem davidsonCorrection_spec (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ) :
    Id.run (davidsonCorrection pure A l r) = fun i => -r i / (A i i - l) := by
  funext i
  rw [davidsonCorrection, List.idRun_foldlM_update_apply
    (fun i (_ : ℝ) => davidsonEntry pure A l r i) _ (List.nodup_finRange n),
    ite_eq_left (List.mem_finRange i)]
  rfl

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem subspaceExpansion_succ (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (t : ℕ) :
    Id.run (subspaceExpansion pure A correct ritz x₁ tol (t + 1)) =
      Id.run (subspaceExpansionStep pure A correct ritz tol
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol t))) := by
  simp only [subspaceExpansion, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- `(V_pᵀ y)_i = v_iᵀ y`. -/
private theorem basisCols_transpose_mulVec_apply (v : ℕ → Fin n → ℝ) (p : ℕ) (y : Fin n → ℝ)
    (i : Fin p) : ((basisCols v p)ᵀ *ᵥ y) i = v i ⬝ᵥ y := by
  simp [basisCols, Matrix.mulVec, dotProduct]

/-- `V_p t = ∑_i t_i v_i`. -/
private theorem basisCols_mulVec (v : ℕ → Fin n → ℝ) (p : ℕ) (t : Fin p → ℝ) :
    basisCols v p *ᵥ t = ∑ i : Fin p, t i • v i := by
  ext a
  simp [basisCols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- The orthonormality of the columns of `V_p`, read as `V_pᵀ V_p = I`. -/
private theorem basisCols_transpose_mul_self {v : ℕ → Fin n → ℝ} {p : ℕ}
    (hv : ∀ i < p, ∀ j < p, v i ⬝ᵥ v j = if i = j then 1 else 0) :
    (basisCols v p)ᵀ * basisCols v p = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := hv i i.isLt j j.isLt
  simp only [basisCols, Matrix.transpose_apply, Matrix.of_apply] at h ⊢
  rw [← dotProduct.eq_def, h]
  simp [Fin.ext_iff]

/-- A vector orthogonal to `v 0, …, v (p − 1)` is orthogonal to their span `ran V_p`. -/
private theorem toLp_mem_orthogonal_span {p : ℕ} (v : ℕ → Fin n → ℝ) (y : Fin n → ℝ)
    (h : ∀ i < p, v i ⬝ᵥ y = 0) :
    (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) ∈ (Submodule.span ℝ
      (Set.range fun i : Fin p => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
    exact h i i.isLt
  | zero => simp
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul c z _ hz => rw [inner_smul_left, hz, mul_zero]

/-- A unit vector in the Euclidean norm: `xᵀ x = 1` gives `‖x‖₂ = 1`. -/
private theorem norm_toLp_eq_one {x : Fin n → ℝ} (h : x ⬝ᵥ x = 1) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h2 := real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, h] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), ← h2, Real.sqrt_one]

/-- The conclusion of the exact semantics of the subspace expansion loop at pass `j`: `x_j` is a
unit vector of `ran V_{j+1}` whose residual `A x_j − λ_j x_j` is orthogonal to `v_0, …, v_j`. -/
private theorem isRitzPair_of_cond {A : Matrix (Fin n) (Fin n) ℝ} {v : ℕ → Fin n → ℝ}
    {x : Fin n → ℝ} {l : ℝ} {j : ℕ} (hc : ∃ c : Fin (j + 1) → ℝ, x = ∑ i, c i • v i)
    (hx : x ⬝ᵥ x = 1) (hr : ∀ i ≤ j, v i ⬝ᵥ (A *ᵥ x - l • x) = 0) :
    Krylov.IsRitzPair (Matrix.toEuclideanLin A)
      (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
        (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n)))) l (WithLp.toLp 2 x) where
  mem := by
    obtain ⟨c, rfl⟩ := hc
    rw [WithLp.toLp_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [WithLp.toLp_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ne_zero := fun h => by
    have h0 : x = 0 := by simpa using congrArg WithLp.ofLp h
    rw [h0, dotProduct_zero] at hx
    exact zero_ne_one hx
  residual_mem_orthogonal := by
    rw [Matrix.toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub]
    exact toLp_mem_orthogonal_span v _ fun i hi => hr i (by omega)

/-- **Exact semantics of the subspace expansion loop** shared by (10.6.16) and §10.6.4, for
symmetric `A`, a unit start `x₁` and a Ritz selector returning a unit eigenpair of every symmetric
matrix: the loop stops with `‖r_k‖ ≤ tol` or after `fuel` passes; `r_k = A x_k − λ_k x_k`,
`ρ_k = ‖r_k‖₂`; the correction of pass `j` is `correct x_j λ_j r_j`; and as long as no
orthogonalized correction `s_{j+1}` vanishes, `V_{k+1}` has orthonormal columns and every
`(λ_j, x_j)` is a Ritz pair of `A` on `ran V_{j+1}` with `x_j` a unit vector and
`V_{j+1}ᵀ r_j = 0`. The correction solver plays no role in these claims. -/
theorem subspaceExpansion_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.x 0 = x₁ ∧
      s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, s.dv j = Id.run (correct (s.x j) (s.lam j) (A *ᵥ s.x j - s.lam j • s.x j))) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ‖(WithLp.toLp 2 (s.x j) : EuclideanSpace ℝ (Fin n))‖ = 1 ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) := by
  intro s
  let P : ℕ → DavidsonState n → Prop := fun t s =>
    s.k ≤ t ∧ (s.k = t ∨ s.done = true) ∧ s.done = decide (s.rho ≤ tol) ∧ s.x 0 = x₁ ∧
      s.v 0 = x₁ ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, s.dv j = Id.run (correct (s.x j) (s.lam j) (A *ᵥ s.x j - s.lam j • s.x j))) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, (∃ c : Fin (j + 1) → ℝ, s.x j = ∑ i, c i • s.v i) ∧ s.x j ⬝ᵥ s.x j = 1 ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0)
  have hP : ∀ t, P t (Id.run (subspaceExpansion pure A correct ritz x₁ tol t)) := by
    intro t
    induction t with
    | zero =>
      simp only [subspaceExpansion, Id.run_bind, algorithm_1_1_3_spec, algorithm_1_1_1_spec,
        algorithm_1_1_2_spec, vecNorm_spec, zero_add, List.range_zero, List.foldlM_nil,
        Id.run_pure]
      refine ⟨le_rfl, Or.inl rfl, rfl, ?_, ?_, ?_, rfl, fun j hj => absurd hj (by simp),
        fun _ => ⟨fun i hi j hj => ?_, fun j hj => ?_⟩⟩
      · simp only [Function.update_self]
      · simp only [Function.update_self]
      · simp only [Function.update_self]
        rw [neg_smul, ← sub_eq_add_neg]
      · dsimp only at hi hj
        obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        simpa using hx₁
      · dsimp only at hj
        obtain rfl : j = 0 := by omega
        simp only [Function.update_self]
        refine ⟨⟨fun _ => 1, by simp⟩, hx₁, fun i hi => ?_⟩
        obtain rfl : i = 0 := by omega
        simp only [Function.update_self]
        rw [dotProduct_sub, dotProduct_smul, hx₁, smul_eq_mul, mul_one, sub_self]
    | succ t ih =>
      rw [subspaceExpansion_succ]
      obtain ⟨hkt, hfin, hdone, hx0, hv0, hr, hrho, hdv, hortho⟩ := ih
      set s := Id.run (subspaceExpansion pure A correct ritz x₁ tol t) with hs
      cases hsd : s.done with
      | true =>
        simp only [subspaceExpansionStep, hsd, ↓reduceIte, Id.run_pure]
        exact ⟨by omega, Or.inr hsd, hdone, hx0, hv0, hr, hrho, hdv, hortho⟩
      | false =>
        have hkt' : s.k = t := hfin.resolve_right (by simp [hsd])
        simp only [subspaceExpansionStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          vecNorm_spec, vecDiv_spec, algorithm_1_1_5_spec, algorithm_1_1_3_spec,
          algorithm_1_1_2_spec, zero_add, Id.run_pure]
        set k := s.k with hk
        set δ := Id.run (correct (s.x k) (s.lam k) s.r) with hδ
        set w := Id.run (mgsExpand pure s.v (k + 1) δ) with hw
        set ν := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ with hν
        set v' := Function.update s.v (k + 1) (ν⁻¹ • w) with hv'
        set V := basisCols v' (k + 2) with hV
        set H := Vᵀ * (A * V) with hH
        set θ := (Id.run (ritz (k + 2) H)).1 with hθ
        set tt := (Id.run (ritz (k + 2) H)).2 with htt
        set x' := V *ᵥ tt with hx'
        have hv'lo : ∀ i ≤ k, v' i = s.v i := fun i hi => by
          rw [hv', Function.update_of_ne (by omega)]
        refine ⟨?_, Or.inl ?_, rfl, ?_, ?_, ?_, rfl, fun j hj => ?_, fun hs' => ?_⟩
        · dsimp only
          omega
        · dsimp only
          omega
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hx0
        · dsimp only
          rw [hv'lo 0 (by omega)]
          exact hv0
        · dsimp only
          simp only [Function.update_self]
          rw [neg_smul, ← sub_eq_add_neg]
        · dsimp only at hj ⊢
          rw [Function.update_of_ne (show j ≠ k + 1 by omega) x' s.x,
            Function.update_of_ne (show j ≠ k + 1 by omega) θ s.lam]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (show j ≠ k by omega) δ s.dv]
            exact hdv j hj
          · rw [Function.update_self, hδ, hr]
        -- the orthonormal half
        dsimp only at hs' ⊢
        have hsk : ∀ j < k, s.sNorm j ≠ 0 := fun j hj => by
          have := hs' j (by omega)
          rwa [Function.update_of_ne (by omega)] at this
        have hν0 : ν ≠ 0 := by
          have := hs' k (by omega)
          rwa [Function.update_self] at this
        obtain ⟨horth, hcond⟩ := hortho hsk
        have hwe : w = δ - ∑ j ∈ Finset.range (k + 1), (s.v j ⬝ᵥ δ) • s.v j :=
          mgsExpand_spec (fun i hi j hj => horth i (by omega) j (by omega)) δ
        have hvw : ∀ j ≤ k, s.v j ⬝ᵥ w = 0 := fun j hj => by
          rw [hwe, dotProduct_sub, dotProduct_sum, Finset.sum_eq_single j]
          · rw [dotProduct_smul, horth j hj j hj, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
          · intro l hl hlj
            rw [dotProduct_smul, horth j hj l (by simp at hl; omega), ite_eq_right (Ne.symm hlj),
              smul_zero]
          · intro h
            exact absurd (Finset.mem_range.2 (by omega)) h
        have hww : w ⬝ᵥ w = ν ^ 2 := by
          rw [hν, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
        have horth' : ∀ i ≤ k + 1, ∀ j ≤ k + 1, v' i ⬝ᵥ v' j = if i = j then 1 else 0 := by
          intro i hi j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hi | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
          · rw [hv'lo i (by omega), hv'lo j (by omega)]
            exact horth i (by omega) j (by omega)
          · rw [hv'lo i (by omega), hv', Function.update_self, dotProduct_smul, hvw i (by omega),
              smul_zero, ite_eq_right (by omega)]
          · rw [hv'lo j (by omega), hv', Function.update_self, smul_dotProduct, dotProduct_comm,
              hvw j (by omega), smul_zero, ite_eq_right (by omega)]
          · rw [hv', Function.update_self, smul_dotProduct, dotProduct_smul, hww, ite_eq_left rfl,
              smul_eq_mul, smul_eq_mul]
            field_simp
        have hVV : Vᵀ * V = 1 :=
          basisCols_transpose_mul_self fun i hi j hj => horth' i (by omega) j (by omega)
        have hHs : H.IsSymm := by
          rw [Matrix.IsSymm, hH, Matrix.transpose_mul, Matrix.transpose_mul, hA.eq,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        obtain ⟨hHt, htt1⟩ := hritz (k + 2) H hHs
        refine ⟨horth', fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          obtain ⟨⟨c, hc⟩, hx1, hres⟩ := hcond j (by omega)
          refine ⟨⟨c, ?_⟩, hx1, fun i hi => ?_⟩
          · rw [hc]
            exact Finset.sum_congr rfl fun i _ => by rw [hv'lo i (by omega)]
          · rw [hv'lo i (by omega)]
            exact hres i hi
        · simp only [Function.update_self]
          refine ⟨⟨tt, by rw [hx', hV, basisCols_mulVec]⟩, ?_, fun i hi => ?_⟩
          · rw [hx', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
              hVV, Matrix.one_mulVec, dotProduct_comm, htt1]
          · have hi' : v' i ⬝ᵥ (A *ᵥ x' - θ • x') =
                (Vᵀ *ᵥ (A *ᵥ x' - θ • x')) ⟨i, by omega⟩ :=
              (basisCols_transpose_mulVec_apply v' (k + 2) _ ⟨i, by omega⟩).symm
            rw [hi', Matrix.mulVec_sub, Matrix.mulVec_smul, hx', Matrix.mulVec_mulVec,
              Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec,
              Matrix.mul_assoc, ← hH, hHt, sub_self]
            rfl
  obtain ⟨-, hfin, hdone, hx0, -, hr, hrho, hdv, hortho⟩ := hP fuel
  refine ⟨?_, hx0, hr, hrho, hdv, fun hs => ?_⟩
  · rcases hfin with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [h] using hdone.symm)
  · obtain ⟨horth, hcond⟩ := hortho hs
    refine ⟨horth, fun j hj => ?_⟩
    obtain ⟨hc, hx1, hres⟩ := hcond j hj
    exact ⟨isRitzPair_of_cond hc hx1 hres, norm_toLp_eq_one hx1, hres⟩

/-- **Exact semantics of (10.6.16)** (the claims of §10.6.3): for symmetric `A` (`n ≥ 1`) and a
Ritz selector returning a unit eigenpair of every symmetric matrix, the loop stops with
`‖r_k‖ ≤ tol` or after `fuel` passes; `r_k = A x_k − λ_k x_k`; each correction solves
`(M − λ_j I) δv_j = −r_j` (`M` the diagonal of `A`) whenever `M − λ_j I` is nonsingular; and as
long as no `s_{j+1}` vanishes, `V_{k+1}` has orthonormal columns ("`V_k` is an `n`-by-`k` matrix
with orthonormal columns") and every `(λ_j, x_j)` is a Ritz pair of `A` on `ran V_{j+1}`
(`Krylov.IsRitzPair`), hence `V_{j+1}ᵀ r_j = 0` ("`r_k` is orthogonal to the range of `V_k` as
required"). From `subspaceExpansion_spec` and `davidsonCorrection_spec`. -/
theorem equation_10_6_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hn : 0 < n) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (davidson pure A ritz tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, (∀ i, A i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A i i) - s.lam j • 1) *ᵥ s.dv j =
          -(A *ᵥ s.x j - s.lam j • s.x j)) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) := by
  intro s
  have he : (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) ⬝ᵥ
      (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
    rw [dotProduct, Finset.sum_eq_single ⟨0, hn⟩
      (fun b _ hb => by rw [ite_eq_right (fun h => hb (Fin.ext h)), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  obtain ⟨hfin, -, hr, hrho, hdv, hortho⟩ :=
    subspaceExpansion_spec hA (fun _ l r => davidsonCorrection pure A l r) hritz he tol fuel
  set s' := Id.run (subspaceExpansion pure A (fun _ l r => davidsonCorrection pure A l r) ritz
    (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) tol fuel) with hs'
  rw [show s = s' from rfl]
  refine ⟨hfin, hr, hrho, fun j hj hne => ?_, fun hs => ?_⟩
  · have h := hdv j hj
    simp only [davidsonCorrection_spec] at h
    ext i
    rw [h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Matrix.mulVec_diagonal]
    have hi : A i i - s'.lam j ≠ 0 := sub_ne_zero.2 (hne i)
    field_simp
    ring
  · obtain ⟨horth, hcond⟩ := hortho hs
    exact ⟨horth, fun j hj => ⟨(hcond j hj).1, (hcond j hj).2.2⟩⟩

/-- One pass of the subspace expansion loop that is not yet done: the counter advances, the old
basis vectors, Ritz values and correction norms are kept, and the new Ritz value is the selector's
eigenvalue of `V_{k+2}ᵀ A V_{k+2}`. -/
private theorem subspaceExpansionStep_facts (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))) (tol : ℝ)
    (s₀ : DavidsonState n) (hd : s₀.done = false) :
    (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).k = s₀.k + 1 ∧
      (∀ i ≤ s₀.k, (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v i = s₀.v i) ∧
      (∀ j ≠ s₀.k + 1,
        (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).lam j = s₀.lam j) ∧
      (∀ j ≠ s₀.k,
        (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).sNorm j = s₀.sNorm j) ∧
      (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).lam (s₀.k + 1) =
        (Id.run (ritz (s₀.k + 2)
          ((basisCols (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v
            (s₀.k + 2))ᵀ * (A * basisCols
              (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v (s₀.k + 2))))).1 := by
  simp only [subspaceExpansionStep, hd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
    vecNorm_spec, vecDiv_spec, algorithm_1_1_5_spec, algorithm_1_1_3_spec,
    algorithm_1_1_2_spec, zero_add, Id.run_pure]
  refine ⟨by trivial, fun i hi => Function.update_of_ne (by omega) _ _,
    fun j hj => Function.update_of_ne hj _ _, fun j hj => Function.update_of_ne hj _ _, ?_⟩
  simp

/-- A Rayleigh quotient on `ran V_{k+1}` is at most the largest eigenvalue of
`V_{k+2}ᵀ A V_{k+2}` for orthonormal `v 0, …, v (k + 1)`. -/
private theorem rayleigh_le_of_mem_span {A : Matrix (Fin n) (Fin n) ℝ}
    {v : ℕ → Fin n → ℝ} {k : ℕ}
    (hv : ∀ i ≤ k + 1, ∀ j ≤ k + 1, v i ⬝ᵥ v j = if i = j then 1 else 0)
    {x : Fin n → ℝ} (c : Fin (k + 1) → ℝ) (hx : x = ∑ i, c i • v i) (hx1 : x ⬝ᵥ x = 1)
    {θ : ℝ} (hθ : ∀ y : Fin (k + 2) → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (((basisCols v (k + 2))ᵀ * (A * basisCols v (k + 2))) *ᵥ y) ≤ θ) :
    x ⬝ᵥ (A *ᵥ x) ≤ θ := by
  set V := basisCols v (k + 2) with hV
  have hVV : Vᵀ * V = 1 :=
    basisCols_transpose_mul_self fun i hi j hj => hv i (by omega) j (by omega)
  set y : Fin (k + 2) → ℝ := Fin.snoc c 0 with hy
  have hVy : V *ᵥ y = x := by
    rw [hV, basisCols_mulVec, Fin.sum_univ_castSucc, hx]
    simp [hy]
  have hyy : y ⬝ᵥ y = x ⬝ᵥ x := by
    calc y ⬝ᵥ y = y ⬝ᵥ ((Vᵀ * V) *ᵥ y) := by rw [hVV, Matrix.one_mulVec]
      _ = x ⬝ᵥ x := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hVy]
  have hyHy : y ⬝ᵥ ((Vᵀ * (A * V)) *ᵥ y) = x ⬝ᵥ (A *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, hVy]
  rw [← hyHy]
  exact hθ y (by rw [hyy, hx1])

/-- A Ritz value is the Rayleigh quotient of its unit Ritz vector. -/
private theorem rayleigh_eq_of_residual {A : Matrix (Fin n) (Fin n) ℝ} {v : ℕ → Fin n → ℝ}
    {k : ℕ} {x : Fin n → ℝ} {l : ℝ} (c : Fin (k + 1) → ℝ) (hx : x = ∑ i, c i • v i)
    (hx1 : x ⬝ᵥ x = 1) (hres : ∀ i ≤ k, v i ⬝ᵥ (A *ᵥ x - l • x) = 0) :
    x ⬝ᵥ (A *ᵥ x) = l := by
  set w := A *ᵥ x - l • x with hw
  have h0 : x ⬝ᵥ w = 0 := by
    rw [hx, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by
      rw [smul_dotProduct, hres i (by omega), smul_zero]
  rw [hw, dotProduct_sub, dotProduct_smul, hx1, smul_eq_mul, mul_one, sub_eq_zero] at h0
  exact h0

/-- The coefficients of a vector of `ran V_{k+1}`. -/
private theorem exists_coeffs_of_mem_span {v : ℕ → Fin n → ℝ} {k : ℕ} {x : Fin n → ℝ}
    (h : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ∈ Submodule.span ℝ
      (Set.range fun i : Fin (k + 1) => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n)))) :
    ∃ c : Fin (k + 1) → ℝ, x = ∑ i, c i • v i := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 h
  refine ⟨c, ?_⟩
  have := congrArg WithLp.ofLp hc
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at this
  exact this.symm

/-- The Ritz values of the subspace expansion loop are nondecreasing when the selector returns the
largest Rayleigh quotient of the small matrix. -/
theorem subspaceExpansion_ritzValue_mono {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hmax : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm → ∀ y : Fin p → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (H *ᵥ y) ≤ (Id.run (ritz p H)).1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    (∀ j < (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).k,
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).sNorm j ≠ 0) →
      ∀ j < (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).k,
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).lam j ≤
          (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).lam (j + 1) := by
  induction fuel with
  | zero =>
    intro _ j hj
    simp only [subspaceExpansion, Id.run_bind, List.range_zero, List.foldlM_nil,
      Id.run_pure] at hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ t ih =>
    intro hs j hj
    have hspec1 := (subspaceExpansion_spec hA correct hritz hx₁ tol (t + 1)).2.2.2.2.2 hs
    rw [subspaceExpansion_succ] at hs hj hspec1 ⊢
    set s₀ := Id.run (subspaceExpansion pure A correct ritz x₁ tol t) with hs₀
    cases hd : s₀.done with
    | true =>
      simp only [subspaceExpansionStep, hd, ↓reduceIte, Id.run_pure] at hs hj ⊢
      exact ih hs j hj
    | false =>
      obtain ⟨hk, hv, hlam, hsn, hθ⟩ := subspaceExpansionStep_facts A correct ritz tol s₀ hd
      set s := Id.run (subspaceExpansionStep pure A correct ritz tol s₀) with hsdef
      rw [hk] at hj hs hspec1
      have hs₀n : ∀ j < s₀.k, s₀.sNorm j ≠ 0 := fun j hj' => by
        rw [← hsn j (by omega)]; exact hs j (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hlam j (by omega), hlam (j + 1) (by omega)]
        exact ih hs₀n j hj
      · rw [hlam _ (by omega), hθ]
        obtain ⟨-, hcond⟩ := (subspaceExpansion_spec hA correct hritz hx₁ tol t).2.2.2.2.2 hs₀n
        obtain ⟨hR, hn1, hres⟩ := hcond s₀.k le_rfl
        obtain ⟨c, hc⟩ := exists_coeffs_of_mem_span hR.mem
        have hx1 : s₀.x s₀.k ⬝ᵥ s₀.x s₀.k = 1 := by
          have h2 := real_inner_self_eq_norm_sq
            (WithLp.toLp 2 (s₀.x s₀.k) : EuclideanSpace ℝ (Fin n))
          rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hn1, one_pow] at h2
          rw [dotProduct_comm]; exact h2
        rw [← rayleigh_eq_of_residual c hc hx1 hres]
        have hH : ((basisCols s.v (s₀.k + 2))ᵀ * (A * basisCols s.v (s₀.k + 2))).IsSymm := by
          rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, hA.eq,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        refine rayleigh_le_of_mem_span (hspec1.1) c ?_ hx1 (hmax _ _ hH)
        rw [hc]
        exact Finset.sum_congr rfl fun i _ => by rw [hv i (by omega)]

/-- **The Davidson monotonicity** (split off `equation_10_6_16`; not claimed by the book): when the
selector returns an eigenpair of the small symmetric matrix `V_{k+1}ᵀ A V_{k+1}` whose eigenvalue
is its largest Rayleigh quotient, the Ritz values `λ_k` of Davidson's method (10.6.16) are
nondecreasing as long as no `s_{k+1}` vanishes: `x_k ∈ ran V_k ⊆ ran V_{k+1}` and
`λ_k = x_kᵀ A x_k`. -/
theorem davidson_ritzValue_mono {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hmax : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm → ∀ y : Fin p → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (H *ᵥ y) ≤ (Id.run (ritz p H)).1)
    (hn : 0 < n) (tol : ℝ) (fuel : ℕ) :
    (∀ j < (Id.run (davidson pure A ritz tol fuel)).k,
        (Id.run (davidson pure A ritz tol fuel)).sNorm j ≠ 0) →
      ∀ j < (Id.run (davidson pure A ritz tol fuel)).k,
        (Id.run (davidson pure A ritz tol fuel)).lam j ≤
          (Id.run (davidson pure A ritz tol fuel)).lam (j + 1) := by
  have he : (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) ⬝ᵥ
      (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
    rw [dotProduct, Finset.sum_eq_single ⟨0, hn⟩
      (fun b _ hb => by rw [ite_eq_right (fun h => hb (Fin.ext h)), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  exact subspaceExpansion_ritzValue_mono hA (fun _ l r => davidsonCorrection pure A l r) hritz
    hmax he tol fuel

/-- **Exact semantics of the Jacobi–Davidson framework** (§10.6.4): for symmetric `A`, a unit start
`x₁`, a Ritz selector returning a unit eigenpair of every symmetric matrix, and a correction solver
returning a Jacobi–Davidson correction (10.6.19) for the preconditioner `M` (`IsJDCorrection`)
whenever it is called at a unit vector `x` with `xᵀ r = 0`: the specification of (10.6.16) — the
loop stops with `‖r_k‖ ≤ tol` or after `fuel` passes, `r_k = A x_k − λ_k x_k`, and as long as no
expansion vector lies in `ran V_{j+1}` (`s_{j+1} ≠ 0`), `V_{k+1}` has orthonormal columns and every
`(λ_j, x_j)` is a Ritz pair on `ran V_{j+1}` with `V_{j+1}ᵀ r_j = 0` — and every correction
`δv_j` is a Jacobi–Davidson correction at `(x_j, λ_j, r_j)`, in particular orthogonal to the
current Ritz vector `x_j` ("the Jacobi–Davidson method insists that `δx_c` be orthogonal to the
current eigenvector approximation"). -/
theorem jacobiDavidson_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {M : Matrix (Fin n) (Fin n) ℝ} {solve : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ)}
    (hsolve : ∀ x l r, x ⬝ᵥ x = 1 → x ⬝ᵥ r = 0 →
      IsJDCorrection M (WithLp.toLp 2 x) l (WithLp.toLp 2 r) (WithLp.toLp 2 (Id.run (solve x l r))))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (jacobiDavidson pure A solve ritz x₁ tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        (∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) ∧
        ∀ j < s.k, IsJDCorrection M (WithLp.toLp 2 (s.x j)) (s.lam j)
            (WithLp.toLp 2 (A *ᵥ s.x j - s.lam j • s.x j)) (WithLp.toLp 2 (s.dv j)) ∧
          s.x j ⬝ᵥ s.dv j = 0) := by
  intro s
  obtain ⟨hfin, -, hr, -, hdv, hortho⟩ :=
    subspaceExpansion_spec hA solve hritz hx₁ tol fuel
  set s' := Id.run (subspaceExpansion pure A solve ritz x₁ tol fuel) with hs'
  rw [show s = s' from rfl]
  refine ⟨hfin, hr, fun hs => ?_⟩
  obtain ⟨horth, hcond⟩ := hortho hs
  have hcorr : ∀ j < s'.k, IsJDCorrection M (WithLp.toLp 2 (s'.x j)) (s'.lam j)
      (WithLp.toLp 2 (A *ᵥ s'.x j - s'.lam j • s'.x j)) (WithLp.toLp 2 (s'.dv j)) := by
    intro j hj
    obtain ⟨hR, hx1, hres⟩ := hcond j (by omega)
    have hx1' : s'.x j ⬝ᵥ s'.x j = 1 := by
      have h2 := real_inner_self_eq_norm_sq (WithLp.toLp 2 (s'.x j) : EuclideanSpace ℝ (Fin n))
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hx1, one_pow] at h2
      exact h2
    have hxr : s'.x j ⬝ᵥ (A *ᵥ s'.x j - s'.lam j • s'.x j) = 0 := by
      have h := hR.residual_mem_orthogonal
      rw [Submodule.mem_orthogonal] at h
      have h' := h _ hR.mem
      rwa [Matrix.toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
        EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h'
    rw [hdv j hj]
    exact hsolve _ _ _ hx1' hxr
  refine ⟨horth, fun j hj => ⟨(hcond j hj).1, (hcond j hj).2.2⟩, fun j hj => ⟨hcorr j hj, ?_⟩⟩
  have h := (hcorr j hj).1
  rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h

/-! ### The trace-min principle (§10.6.5) -/

/-- `(Xᵀ C X)(a, b) = ⟪C x_b, x_a⟫` over the columns of `X`. -/
private theorem transpose_mul_mul_apply {k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin k) ℝ) (a b : Fin k) :
    (Xᵀ * C * X) a b = RCLike.re (inner ℝ
      (Matrix.toEuclideanLin C (WithLp.toLp 2 (X.col b))) (WithLp.toLp 2 (X.col a))) := by
  simp only [RCLike.re_to_real, EuclideanSpace.inner_toLp_toLp, Matrix.toEuclideanLin_toLp,
    star_trivial, Matrix.mul_apply, Matrix.transpose_apply, Matrix.col_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- `tr(Xᵀ C X) = ∑ᵢ ⟪C xᵢ, xᵢ⟫` over the columns `xᵢ` of `X`. -/
private theorem trace_transpose_mul_mul_eq_sum {k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin k) ℝ) :
    (Xᵀ * C * X).trace = ∑ i : Fin k, RCLike.re (inner ℝ
      (Matrix.toEuclideanLin C (WithLp.toLp 2 (X.col i))) (WithLp.toLp 2 (X.col i))) := by
  simp only [Matrix.trace, Matrix.diag, transpose_mul_mul_apply]

/-- **The trace-min principle** (§10.6.5, Sameh–Wisniewski): for a symmetric `A`, a positive
definite `B` and `k ≤ n`, with the pencil eigenvalues `μ_1 ≤ ⋯ ≤ μ_n` of `A − λB` (the book counts
from the smallest here; `Matrix.pencilEigenvalues` is decreasing, so the book's `μ_1, …, μ_k` are
its last `k`), `min {tr(VᵀAV) : V ∈ ℝ^{n×k}, VᵀBV = I_k} = μ_1 + ⋯ + μ_k`, attained at a `V_opt`
with `V_optᵀ A V_opt = diag(μ_1, …, μ_k)` and `A V_opt(:, j) = μ_j B V_opt(:, j)`. The book's "if
`V_opt` solves the problem then `V_optᵀ A V_opt = diag(μ)`" holds for *some* minimizer, not every
one (any `V_opt Q`, `Q` orthogonal, also minimizes). Proof: with a normalizer `W`, `WᵀBW = I`, every
feasible `V` is `W X` with `XᵀX = I_k` and `tr(VᵀAV) = tr(Xᵀ(WᵀAW)X)`; Ky Fan's minimum principle
`LinearMap.IsSymmetric.sum_eigenvalues_le_sum_re_inner` for `WᵀAW`, whose sorted eigenvalues are the
pencil eigenvalues (`Matrix.pencilEigenvalues_eq_of_conj_eq_one`); equality at `X` = the last `k`
eigenvectors. -/
theorem isLeast_trace_transpose_mul_mul {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hB : B.PosDef) {k : ℕ} (hkn : k ≤ n) :
    let μ := Matrix.pencilEigenvalues (Matrix.isHermitian_iff_isSymm.mpr hA) hB
    let low : Fin k → ℝ := fun i => μ ⟨i + (n - k), by rw [Fintype.card_fin]; omega⟩
    IsLeast {t | ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * B * V = 1 ∧ t = (Vᵀ * A * V).trace}
        (∑ i, low i) ∧
      ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * B * V = 1 ∧ Vᵀ * A * V = Matrix.diagonal low ∧
        ∀ j, A *ᵥ V.col j = low j • (B *ᵥ V.col j) := by
  intro μ low
  have hA' : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  obtain ⟨W, hWu, hWstar⟩ := hB.exists_isUnit_conj_eq_one
  have hWs : star W = Wᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hW : Wᵀ * B * W = 1 := by rw [← hWs]; exact hWstar
  have hC : (Wᵀ * A * W).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq, Matrix.mul_assoc]
  have key : ∀ (M N : Matrix (Fin n) (Fin n) ℝ) (h : M = N) (hM : M.IsHermitian)
      (hN : N.IsHermitian), hM.eigenvalues₀ = hN.eigenvalues₀ := by
    intro M N h hM hN
    subst h
    rfl
  have hμ : hC.eigenvalues₀ = μ :=
    (key _ _ (by rw [hWs]) hC _).trans (Matrix.pencilEigenvalues_eq_of_conj_eq_one hA' hB hWstar)
  set T := Matrix.toEuclideanLin (Wᵀ * A * W) with hTdef
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) :=
    finrank_euclideanSpace
  have hev : ∀ i, hT.eigenvalues hn i = μ i := fun i => by rw [← hμ]; rfl
  have hkn' : k ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hkn
  have hlow : ∀ i : Fin k, low i = hT.eigenvalues hn ⟨i + (Fintype.card (Fin n) - k), by omega⟩ :=
    fun i => by rw [hev]; simp only [low, Fintype.card_fin]
  have hdet := (Matrix.isUnit_iff_isUnit_det W).1 hWu
  -- `B = W⁻ᵀ W⁻¹`
  have hB' : B = (W⁻¹)ᵀ * W⁻¹ := by
    have h1 : (W⁻¹)ᵀ * (Wᵀ * B * W) * W⁻¹ = B := by
      rw [Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]), Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    rw [← h1, hW, Matrix.mul_one]
  -- the attaining matrix
  set X : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun a i =>
    (hT.eigenvectorBasis hn ⟨i + (Fintype.card (Fin n) - k), by omega⟩) a with hX
  have hXcol : ∀ i, WithLp.toLp 2 (X.col i) =
      hT.eigenvectorBasis hn ⟨i + (Fintype.card (Fin n) - k), by omega⟩ := fun i => rfl
  have hXX : Xᵀ * X = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal]
    simp only [hXcol]
    exact (hT.eigenvectorBasis hn).orthonormal.comp _ (fun i j h => Fin.ext (by
      have := congrArg Fin.val h; simp at this; omega))
  have hXCX : Xᵀ * (Wᵀ * A * W) * X = Matrix.diagonal low := by
    ext i j
    have hmul : ∀ a b : Fin k, (Xᵀ * (Wᵀ * A * W) * X) a b = RCLike.re (inner ℝ
        (T (WithLp.toLp 2 (X.col b))) (WithLp.toLp 2 (X.col a))) := fun a b =>
      transpose_mul_mul_apply _ X a b
    rw [hmul, hXcol, hXcol, hT.apply_eigenvectorBasis, inner_smul_left,
      OrthonormalBasis.inner_eq_ite, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [hlow]
    · have hij' : (j : ℕ) ≠ i := fun h => hij (Fin.ext h).symm
      simp [hij, hij']
  -- the feasible matrices
  have hfeas : ∀ X' : Matrix (Fin n) (Fin k) ℝ, X'ᵀ * X' = 1 →
      (W * X')ᵀ * B * (W * X') = 1 := fun X' h => by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B,
      ← Matrix.mul_assoc Wᵀ, ← Matrix.mul_assoc Wᵀ, hW, Matrix.one_mul, h]
  have hconj : ∀ X' : Matrix (Fin n) (Fin k) ℝ,
      (W * X')ᵀ * A * (W * X') = X'ᵀ * (Wᵀ * A * W) * X' := fun X' => by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  -- the columns of `W X` are eigenvectors of the pencil
  have heig : ∀ j, A *ᵥ (W * X).col j = low j • (B *ᵥ (W * X).col j) := by
    intro j
    have hx : (Wᵀ * A * W) *ᵥ X.col j = low j • X.col j := by
      have h := congrArg WithLp.ofLp (hT.apply_eigenvectorBasis hn
        ⟨j + (Fintype.card (Fin n) - k), by omega⟩)
      rw [← hXcol, hlow] at *
      simpa [hTdef, Matrix.toEuclideanLin_toLp, Matrix.mul_assoc] using h
    have hcol : (W * X).col j = W *ᵥ X.col j := by
      ext r
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hWT : (W⁻¹)ᵀ * Wᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one]
    have hA1 : A *ᵥ (W *ᵥ X.col j) = (W⁻¹)ᵀ *ᵥ ((Wᵀ * A * W) *ᵥ X.col j) := by
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hWT, Matrix.one_mul]
    have hB1 : B *ᵥ (W *ᵥ X.col j) = (W⁻¹)ᵀ *ᵥ X.col j := by
      rw [hB', Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    rw [hcol, hA1, hB1, hx, Matrix.mulVec_smul]
  refine ⟨⟨⟨W * X, hfeas X hXX, ?_⟩, ?_⟩, W * X, hfeas X hXX, by rw [hconj, hXCX], heig⟩
  · rw [hconj, hXCX, Matrix.trace_diagonal]
  · rintro t ⟨V, hV, rfl⟩
    set X' := W⁻¹ * V with hX'
    have hVX : V = W * X' := by
      rw [hX', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    have hXX' : X'ᵀ * X' = 1 := by
      rw [← hV, hB', hX', Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have horth : Orthonormal ℝ fun i => WithLp.toLp 2 (X'.col i) := by
      rw [← Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal,
        Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hXX'
    have hky := hT.sum_eigenvalues_le_sum_re_inner hn horth hkn'
    rw [hVX, hconj, trace_transpose_mul_mul_eq_sum]
    simp only [hlow]
    exact hky

end GolubVanLoan.Chapter10
