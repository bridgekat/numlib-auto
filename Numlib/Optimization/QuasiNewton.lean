import Mathlib.LinearAlgebra.Matrix.PosDef
import Numlib.Analysis.Calculus.MeanValue
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Nonlinear.QuasiNewton

/-!
# Secant updates of a Hessian approximation

The secant (quasi-Newton) updates of a symmetric approximation `B` to the Hessian of an objective
function ([quarteroni2000numerical] §7.2.7; Dennis–Schnabel, *Numerical Methods for Unconstrained
Optimization and Nonlinear Equations*, §9.1–9.2; Nocedal–Wright, *Numerical Optimization*, §6.1),
on `Matrix n n ℝ`. With `s = xp - x` the last step and `y = ∇f(xp) - ∇f(x)` the corresponding change
of the gradient, every update enforces the secant equation `B₊ s = y`:

* `Matrix.rankOneSecantUpdate B s y c`, the rank-one update (7.42) with an arbitrary scaling
  vector `c`, of which Broyden's update `Matrix.broydenUpdate` (`Numlib/Nonlinear/QuasiNewton`)
  is the case `c = s`;
* `Matrix.sr1Update B s y`, the symmetric rank-one update (7.43), the case `c = y - B s`, which
  preserves symmetry; its inverse (7.44) is `Matrix.sr1Update_inv`, by the Sherman–Morrison
  formula `Matrix.inv_add_vecMulVec` of `Numlib/LinearAlgebra/Matrix/NonsingularInverse`;
* `Matrix.symmetrizationStep s y c`, one double step of the symmetrization iteration (7.45) —
  a rank-one update followed by the symmetric part — whose limit from a symmetric `B` is the
  general symmetric update (7.46), `Matrix.generalSymmetricUpdate B s y c`
  (`Matrix.tendsto_symmetrizationStep_iterate`);
* `Matrix.psbUpdate B s y`, the Powell-symmetric-Broyden update, the case `c = s` of (7.46),
  characterized as the closest symmetric matrix to `B` in the Frobenius norm among those satisfying
  the secant equation (`Matrix.frobenius_norm_psbUpdate_sub_le`, with uniqueness
  `Matrix.frobenius_norm_psbUpdate_sub_lt`; Dennis–Schnabel Theorem 9.1.1), and its bounded
  deterioration against a Lipschitz Hessian (`Matrix.frobenius_norm_psbUpdate_sub_le_add`, the last
  display of [quarteroni2000numerical] §7.2.7);
* `Matrix.dfpUpdate` and `Matrix.bfgsUpdate`, the Davidon–Fletcher–Powell and
  Broyden–Fletcher–Goldfarb–Shanno updates, which the book defers to Dennis–Schnabel §9.2, with
  the preservation of positive definiteness under the curvature condition `⟪y, s⟫ > 0`
  (`Matrix.dfpUpdate_posDef`, `Matrix.bfgsUpdate_posDef`).

## Design

Matrices rather than operators: every statement here is about symmetry and the Frobenius norm,
which are matrix notions; the operator form of the nonsymmetric update is `Broyden.update` in
`Numlib/Nonlinear/QuasiNewton`. The Frobenius norm is the scoped instance
`Matrix.Norms.Frobenius`, opened in the sections that use it; the convergence of the
symmetrization iteration is stated in the product topology of `Matrix n n ℝ`, which every matrix
norm induces. Divisions follow Lean's convention `x / 0 = 0`, so the updates are total and the
nondegeneracy conditions (`c ⬝ᵥ s ≠ 0`, `s ≠ 0`, `0 < y ⬝ᵥ s`) appear only in the theorems.

Two hypotheses that the book's text leaves implicit are made explicit. The symmetrization
iteration (7.45) converges to (7.46) only from a *symmetric* `B`: one step already produces a
symmetric matrix, whereas (7.46) with a nonsymmetric `B` is not symmetric. The bounded
deterioration estimate needs the current approximation `B` symmetric as well: the least-change
projection `Δ ↦ Δ - (1 - P) Δ (1 - P)` is a contraction in the Frobenius norm on symmetric `Δ`
only.
-/

open scoped InnerProductSpace
open WithLp Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n]

/-! ### The rank-one secant update (7.42) and the symmetric rank-one update (7.43) -/

/-- **The rank-one secant update** ([quarteroni2000numerical] (7.42)):
`B₊ = B + ((y - B s) cᵀ) / (cᵀ s)`, with an arbitrary scaling vector `c`. With `c = s` it is
Broyden's update `Matrix.broydenUpdate`; with `c = y - B s` it is the symmetric rank-one update
`Matrix.sr1Update`. For `cᵀ s = 0` the coefficient is the junk value `0` and `B₊ = B`. -/
noncomputable def rankOneSecantUpdate (B : Matrix n n ℝ) (s y c : n → ℝ) : Matrix n n ℝ :=
  B + (1 / (c ⬝ᵥ s)) • vecMulVec (y - B *ᵥ s) c

/-- Broyden's update is the rank-one secant update with `c = s`. -/
theorem broydenUpdate_eq_rankOneSecantUpdate (B : Matrix n n ℝ) (s y : n → ℝ) :
    broydenUpdate B s y = rankOneSecantUpdate B s y s :=
  rfl

/-- **The secant equation** for the rank-one update: `B₊ s = y` whenever `cᵀ s ≠ 0`. -/
theorem rankOneSecantUpdate_mulVec (B : Matrix n n ℝ) {s c : n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : n → ℝ) : rankOneSecantUpdate B s y c *ᵥ s = y := by
  simp only [rankOneSecantUpdate, add_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, one_div, inv_mul_cancel₀ hcs, one_smul]
  abel

/-- **The symmetric rank-one update** ([quarteroni2000numerical] (7.43)):
`B₊ = B + ((y - B s)(y - B s)ᵀ) / ((y - B s)ᵀ s)`, the rank-one secant update with
`c = y - B s`. -/
noncomputable def sr1Update (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  rankOneSecantUpdate B s y (y - B *ᵥ s)

/-- The symmetric rank-one update written out. -/
theorem sr1Update_eq (B : Matrix n n ℝ) (s y : n → ℝ) :
    sr1Update B s y
      = B + (1 / ((y - B *ᵥ s) ⬝ᵥ s)) • vecMulVec (y - B *ᵥ s) (y - B *ᵥ s) :=
  rfl

/-- The symmetric rank-one update of a symmetric matrix is symmetric. -/
theorem sr1Update_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (sr1Update B s y).IsSymm :=
  hB.add (IsSymm.smul (transpose_vecMulVec (y - B *ᵥ s) (y - B *ᵥ s)) _)

/-- **The secant equation** for the symmetric rank-one update: `B₊ s = y` whenever
`(y - B s)ᵀ s ≠ 0`. -/
theorem sr1Update_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (h : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) :
    sr1Update B s y *ᵥ s = y :=
  rankOneSecantUpdate_mulVec B h y

section Inverse

variable [DecidableEq n]

/-- The transposition identity `(B s)ᵀ (C y) = yᵀ s` for `C = B⁻¹` and symmetric `B`. -/
private theorem mulVec_dotProduct_inv_mulVec {B : Matrix n n ℝ} (hB : B.IsSymm) (hu : IsUnit B)
    (s y : n → ℝ) : (B *ᵥ s) ⬝ᵥ (B⁻¹ *ᵥ y) = y ⬝ᵥ s := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hB.eq,
    mulVec_nonsing_inv_mulVec hu]

/-- **The inverse of the symmetric rank-one update** ([quarteroni2000numerical] (7.44)): for a
symmetric invertible `B` with `C = B⁻¹`, `(y - B s)ᵀ s ≠ 0` and `(s - C y)ᵀ y ≠ 0`,
`(B₊)⁻¹ = C + ((s - C y)(s - C y)ᵀ) / ((s - C y)ᵀ y)`, so that the inverse approximation can be
updated directly. By the Sherman–Morrison formula `Matrix.inv_add_vecMulVec` with
`u = (y - B s) / ((y - B s)ᵀ s)`, `v = y - B s`, using `C (y - B s) = -(s - C y)` and
`(y - B s)ᵀ (s - C y) = (y - B s)ᵀ s + (s - C y)ᵀ y`. -/
theorem sr1Update_inv {B : Matrix n n ℝ} (hB : B.IsSymm) (hu : IsUnit B) {s y : n → ℝ}
    (hσ : (y - B *ᵥ s) ⬝ᵥ s ≠ 0) (hw : (s - B⁻¹ *ᵥ y) ⬝ᵥ y ≠ 0) :
    (sr1Update B s y)⁻¹
      = B⁻¹ + (1 / ((s - B⁻¹ *ᵥ y) ⬝ᵥ y)) • vecMulVec (s - B⁻¹ *ᵥ y) (s - B⁻¹ *ᵥ y) := by
  set C : Matrix n n ℝ := B⁻¹ with hC
  set r : n → ℝ := y - B *ᵥ s with hr
  set w : n → ℝ := s - C *ᵥ y with hwdef
  set σ : ℝ := r ⬝ᵥ s with hσdef
  have hCr : C *ᵥ r = -w := by
    rw [hr, hwdef, mulVec_sub, hC, nonsing_inv_mulVec_mulVec hu, neg_sub]
  have hCt : Cᵀ = C := by rw [hC, transpose_nonsing_inv, hB.eq]
  have hrC : r ᵥ* C = -w := by rw [← hCt, vecMul_transpose, hCr]
  have hrw : r ⬝ᵥ w = σ + w ⬝ᵥ y := by
    simp only [hr, hwdef, hσdef, sub_dotProduct, dotProduct_sub]
    rw [mulVec_dotProduct_inv_mulVec hB hu, dotProduct_comm (B *ᵥ s) s,
      dotProduct_comm (C *ᵥ y) y, dotProduct_comm s y]
    ring
  have hden' : 1 + r ⬝ᵥ (C *ᵥ ((1 / σ) • r)) = -(w ⬝ᵥ y) / σ := by
    rw [mulVec_smul, hCr, smul_neg, dotProduct_neg, dotProduct_smul, hrw, smul_eq_mul]
    field_simp
    ring
  have hden : 1 + r ⬝ᵥ (C *ᵥ ((1 / σ) • r)) ≠ 0 := by
    rw [hden']
    exact div_ne_zero (neg_ne_zero.2 hw) hσ
  rw [sr1Update_eq, ← hr, ← hσdef, ← smul_vecMulVec, inv_add_vecMulVec hu hden, ← hC, hrC, hden',
    mulVec_smul, hCr, smul_neg, neg_vecMulVec, vecMulVec_neg, neg_neg, smul_vecMulVec, smul_smul,
    sub_eq_add_neg, ← neg_smul]
  congr 2
  field_simp

end Inverse

/-! ### The symmetrization iteration (7.45) and its limit (7.46) -/

/-- **One double step of the symmetrization iteration** ([quarteroni2000numerical] (7.45)):
the rank-one secant update `B⁽²ʲ⁺¹⁾ = B⁽²ʲ⁾ + ((y - B⁽²ʲ⁾ s) cᵀ) / (cᵀ s)` followed by its symmetric
part `B⁽²ʲ⁺²⁾ = (B⁽²ʲ⁺¹⁾ + (B⁽²ʲ⁺¹⁾)ᵀ) / 2`, so that `B⁽²ʲ⁾ = (symmetrizationStep s y c)^[j] B`. -/
noncomputable def symmetrizationStep (s y c : n → ℝ) (B : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (rankOneSecantUpdate B s y c + (rankOneSecantUpdate B s y c)ᵀ)

/-- **The general symmetric secant update** ([quarteroni2000numerical] (7.46)) with scaling
vector `c`:
`B₊ = B + ((y - B s) cᵀ + c (y - B s)ᵀ) / (cᵀ s) - (((y - B s)ᵀ s) / (cᵀ s)²) c cᵀ`,
the limit of the symmetrization iteration from a symmetric `B`
(`Matrix.tendsto_symmetrizationStep_iterate`). With `c = s` it is the Powell-symmetric-Broyden
update `Matrix.psbUpdate`. -/
noncomputable def generalSymmetricUpdate (B : Matrix n n ℝ) (s y c : n → ℝ) : Matrix n n ℝ :=
  B + (1 / (c ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) c + vecMulVec c (y - B *ᵥ s))
    - (((y - B *ᵥ s) ⬝ᵥ s) / (c ⬝ᵥ s) ^ 2) • vecMulVec c c

/-- The general symmetric update of a symmetric matrix is symmetric. -/
theorem generalSymmetricUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y c : n → ℝ) :
    (generalSymmetricUpdate B s y c).IsSymm := by
  unfold IsSymm generalSymmetricUpdate
  rw [transpose_sub, transpose_add, transpose_smul, transpose_add, transpose_vecMulVec,
    transpose_vecMulVec, transpose_smul, transpose_vecMulVec, hB.eq, add_comm (vecMulVec c _)]

/-- **The secant equation** for the general symmetric update: `B₊ s = y` whenever `cᵀ s ≠ 0`. -/
theorem generalSymmetricUpdate_mulVec (B : Matrix n n ℝ) {s c : n → ℝ} (hcs : c ⬝ᵥ s ≠ 0)
    (y : n → ℝ) : generalSymmetricUpdate B s y c *ᵥ s = y := by
  simp only [generalSymmetricUpdate, sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_add, smul_smul]
  rw [one_div_mul_cancel hcs, one_smul,
    show (y - B *ᵥ s) ⬝ᵥ s / (c ⬝ᵥ s) ^ 2 * (c ⬝ᵥ s) = 1 / (c ⬝ᵥ s) * ((y - B *ᵥ s) ⬝ᵥ s) by
      field_simp]
  abel

/-- **The Powell-symmetric-Broyden update** ([quarteroni2000numerical] (7.46) with `c = s`):
`B₊ = B + ((y - B s) sᵀ + s (y - B s)ᵀ) / (sᵀ s) - (((y - B s)ᵀ s) / (sᵀ s)²) s sᵀ`. -/
noncomputable def psbUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  generalSymmetricUpdate B s y s

/-- The Powell-symmetric-Broyden update written out. -/
theorem psbUpdate_eq (B : Matrix n n ℝ) (s y : n → ℝ) :
    psbUpdate B s y
      = B + (1 / (s ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) s + vecMulVec s (y - B *ᵥ s))
        - (((y - B *ᵥ s) ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s :=
  rfl

/-- The Powell-symmetric-Broyden update of a symmetric matrix is symmetric. -/
theorem psbUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (psbUpdate B s y).IsSymm :=
  generalSymmetricUpdate_isSymm hB s y s

/-- **The secant equation** for the Powell-symmetric-Broyden update: `B₊ s = y` for `s ≠ 0`. -/
theorem psbUpdate_mulVec (B : Matrix n n ℝ) {s : n → ℝ} (hs : s ≠ 0) (y : n → ℝ) :
    psbUpdate B s y *ᵥ s = y :=
  generalSymmetricUpdate_mulVec B (mt dotProduct_self_eq_zero.1 hs) y

section Symmetrization

variable {s y c : n → ℝ}

/-- One symmetrization step from a perturbation of a symmetric matrix `M` satisfying the secant
equation: `T (M + Δ) = M + Δ - ((Δ s) cᵀ + c (Δ s)ᵀ) / (2 cᵀ s)` for symmetric `Δ`. -/
theorem symmetrizationStep_add_of_isSymm {M Δ : Matrix n n ℝ} (hM : M.IsSymm) (hMs : M *ᵥ s = y)
    (hΔ : Δ.IsSymm) :
    symmetrizationStep s y c (M + Δ)
      = M + Δ - (1 / (2 * (c ⬝ᵥ s))) • (vecMulVec (Δ *ᵥ s) c + vecMulVec c (Δ *ᵥ s)) := by
  have h1 : rankOneSecantUpdate (M + Δ) s y c
      = M + Δ - (1 / (c ⬝ᵥ s)) • vecMulVec (Δ *ᵥ s) c := by
    rw [rankOneSecantUpdate, add_mulVec, hMs, sub_add_cancel_left, neg_vecMulVec, smul_neg,
      ← sub_eq_add_neg]
  rw [symmetrizationStep, h1, transpose_sub, transpose_add, transpose_smul, transpose_vecMulVec,
    hM.eq, hΔ.eq]
  module

/-- The first symmetrization step from a symmetric `B`:
`T B = B + ((y - B s) cᵀ + c (y - B s)ᵀ) / (2 cᵀ s)`. -/
theorem symmetrizationStep_of_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) :
    symmetrizationStep s y c B
      = B + (1 / (2 * (c ⬝ᵥ s))) • (vecMulVec (y - B *ᵥ s) c + vecMulVec c (y - B *ᵥ s)) := by
  rw [symmetrizationStep, rankOneSecantUpdate, transpose_add, transpose_smul, transpose_vecMulVec,
    hB.eq]
  module

/-- The deviation of the first symmetrization step from the limit (7.46),
`Δ₁ = T B - generalSymmetricUpdate B s y c`, is halved by the linear part of `T`:
`((Δ₁ s) cᵀ + c (Δ₁ s)ᵀ) / (cᵀ s) = Δ₁`. This is the whole content of the convergence of the
symmetrization iteration. -/
theorem symmetrizationStep_sub_generalSymmetricUpdate_key (hcs : c ⬝ᵥ s ≠ 0)
    {B : Matrix n n ℝ} (hB : B.IsSymm) :
    (1 / (c ⬝ᵥ s)) • (vecMulVec ((symmetrizationStep s y c B - generalSymmetricUpdate B s y c)
        *ᵥ s) c
      + vecMulVec c ((symmetrizationStep s y c B - generalSymmetricUpdate B s y c) *ᵥ s))
      = symmetrizationStep s y c B - generalSymmetricUpdate B s y c := by
  set r : n → ℝ := y - B *ᵥ s with hr
  set σ : ℝ := c ⬝ᵥ s with hσ
  set ρ : ℝ := r ⬝ᵥ s with hρ
  have hΔ : symmetrizationStep s y c B - generalSymmetricUpdate B s y c
      = (-(1 / (2 * σ))) • (vecMulVec r c + vecMulVec c r) + (ρ / σ ^ 2) • vecMulVec c c := by
    rw [symmetrizationStep_of_isSymm hB, generalSymmetricUpdate]
    module
  have hΔs : (symmetrizationStep s y c B - generalSymmetricUpdate B s y c) *ᵥ s
      = (-(1 / 2 : ℝ)) • r + (ρ / (2 * σ)) • c := by
    rw [hΔ]
    simp only [add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      smul_add, smul_smul, ← hσ, ← hρ]
    rw [show -(1 / (2 * σ)) * σ = -(1 / 2 : ℝ) by field_simp,
      show ρ / σ ^ 2 * σ = ρ / σ by field_simp,
      show -(1 / (2 * σ)) * ρ = -(ρ / (2 * σ)) by ring]
    module
  rw [hΔs]
  conv_rhs => rw [hΔ]
  simp only [add_vecMulVec, vecMulVec_add, smul_vecMulVec, vecMulVec_smul]
  module

/-- **The closed form of the symmetrization iteration** from a symmetric `B`: for `cᵀ s ≠ 0`,
`T^[j+1] B = B̄ + 2⁻ʲ (T B - B̄)` where `B̄ = generalSymmetricUpdate B s y c` and
`T = symmetrizationStep s y c`. The limit `B̄` is a fixed point of `T` (it is symmetric and
satisfies the secant equation), `T` is affine, and its linear part halves the deviation
`T B - B̄`. -/
theorem symmetrizationStep_iterate_succ (hcs : c ⬝ᵥ s ≠ 0) {B : Matrix n n ℝ} (hB : B.IsSymm)
    (j : ℕ) :
    (symmetrizationStep s y c)^[j + 1] B
      = generalSymmetricUpdate B s y c
        + ((1 / 2 : ℝ) ^ j) • (symmetrizationStep s y c B - generalSymmetricUpdate B s y c) := by
  set B' : Matrix n n ℝ := generalSymmetricUpdate B s y c with hB'
  set Δ : Matrix n n ℝ := symmetrizationStep s y c B - B' with hΔ
  have hB's : B' *ᵥ s = y := generalSymmetricUpdate_mulVec B hcs y
  have hB'sym : B'.IsSymm := generalSymmetricUpdate_isSymm hB s y c
  have hΔsym : Δ.IsSymm := by
    refine IsSymm.sub ?_ hB'sym
    rw [symmetrizationStep_of_isSymm hB]
    refine hB.add (IsSymm.smul ?_ _)
    unfold IsSymm
    rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]
  have hkey := symmetrizationStep_sub_generalSymmetricUpdate_key (y := y) hcs hB
  rw [← hB', ← hΔ] at hkey
  induction j with
  | zero =>
    rw [zero_add, Function.iterate_one, pow_zero, one_smul, hΔ, add_sub_cancel]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, symmetrizationStep_add_of_isSymm hB'sym hB's
      (hΔsym.smul _), smul_mulVec, vecMulVec_smul, smul_vecMulVec, ← smul_add, smul_smul,
      show 1 / (2 * (c ⬝ᵥ s)) * (1 / 2 : ℝ) ^ j = (1 / 2 : ℝ) ^ j * (1 / 2) * (1 / (c ⬝ᵥ s)) by
        ring,
      mul_smul, mul_smul, hkey, pow_succ, mul_smul]
    module

/-- **The symmetrization iteration converges to the general symmetric update**
([quarteroni2000numerical] (7.45)–(7.46); Dennis–Schnabel §9.1; Powell 1970): from a symmetric
`B` and for `cᵀ s ≠ 0`, `(symmetrizationStep s y c)^[j] B → generalSymmetricUpdate B s y c` as
`j → ∞`, with the geometric rate `2⁻ʲ` given by `Matrix.symmetrizationStep_iterate_succ`. The
book states the limit without proof and without the symmetry of `B`, which is needed: the first
step is symmetric whatever `B` is, whereas (7.46) is symmetric only when `B` is. -/
theorem tendsto_symmetrizationStep_iterate (hcs : c ⬝ᵥ s ≠ 0) {B : Matrix n n ℝ}
    (hB : B.IsSymm) :
    Tendsto (fun j => (symmetrizationStep s y c)^[j] B) atTop
      (𝓝 (generalSymmetricUpdate B s y c)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simp only [symmetrizationStep_iterate_succ hcs hB]
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).smul_const (symmetrizationStep s y c B - generalSymmetricUpdate B s y c))
  simpa using tendsto_const_nhds.add h

end Symmetrization

/-! ### Least change in the Frobenius norm -/

section Frobenius

open scoped Matrix.Norms.Frobenius

variable [DecidableEq n]

/-- The Frobenius norm squared of a real matrix is the trace of `Aᵀ A`. -/
private theorem frobenius_norm_sq_eq_trace_transpose (A : Matrix n n ℝ) :
    ‖A‖ ^ 2 = trace (Aᵀ * A) := by
  have h := frobenius_norm_sq_eq_trace (𝕜 := ℝ) A
  simpa [conjTranspose_eq_transpose_of_trivial] using h

/-- **Pythagoras for the two-sided compression by a symmetric idempotent**: for `Qᵀ = Q` and
`Q² = Q`, `‖A‖_F² = ‖A - Q A Q‖_F² + ‖Q A Q‖_F²`, since `Q A Q` is the Frobenius-orthogonal
projection of `A` onto `{Q Z Q}`. In the trace form `‖M‖_F² = tr(Mᵀ M)` the cross terms are
`tr(Aᵀ Q A Q) = tr((Q A Q)ᵀ (Q A Q))`, by cyclicity and `Q² = Q`. -/
theorem frobenius_norm_sq_sub_mul_mul_add_sq (A : Matrix n n ℝ) {Q : Matrix n n ℝ}
    (hQt : Qᵀ = Q) (hQQ : Q * Q = Q) :
    ‖A - Q * A * Q‖ ^ 2 + ‖Q * A * Q‖ ^ 2 = ‖A‖ ^ 2 := by
  set N : Matrix n n ℝ := Q * A * Q with hN
  have hNt : Nᵀ = Q * Aᵀ * Q := by
    rw [hN, transpose_mul, transpose_mul, hQt, Matrix.mul_assoc]
  have hNN : trace (Nᵀ * N) = trace (Aᵀ * N) := by
    rw [hNt, hN]
    calc trace (Q * Aᵀ * Q * (Q * A * Q))
        = trace (Q * (Aᵀ * Q * (Q * A * Q))) := by simp only [Matrix.mul_assoc]
      _ = trace (Aᵀ * Q * (Q * A * Q) * Q) := trace_mul_comm _ _
      _ = trace (Aᵀ * (Q * Q) * A * (Q * Q)) := by simp only [Matrix.mul_assoc]
      _ = trace (Aᵀ * (Q * A * Q)) := by rw [hQQ]; simp only [Matrix.mul_assoc]
  have hNA : trace (Nᵀ * A) = trace (Aᵀ * N) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
  rw [frobenius_norm_sq_eq_trace_transpose, frobenius_norm_sq_eq_trace_transpose,
    frobenius_norm_sq_eq_trace_transpose, transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub]
  simp only [trace_sub, hNN, hNA]
  ring

/-- **The two-sided compression by a symmetric idempotent does not increase the Frobenius
norm of the complement**: `‖A - Q A Q‖_F ≤ ‖A‖_F` for `Qᵀ = Q`, `Q² = Q`. -/
theorem frobenius_norm_sub_mul_mul_le (A : Matrix n n ℝ) {Q : Matrix n n ℝ} (hQt : Qᵀ = Q)
    (hQQ : Q * Q = Q) : ‖A - Q * A * Q‖ ≤ ‖A‖ := by
  have h := frobenius_norm_sq_sub_mul_mul_add_sq A hQt hQQ
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖Q * A * Q‖]) (norm_nonneg _)

variable {s : n → ℝ}

omit [DecidableEq n] in
/-- The orthogonal projector `P = s sᵀ / (sᵀ s)` onto `span {s}` is symmetric. -/
private theorem transpose_proj (s : n → ℝ) :
    ((1 / (s ⬝ᵥ s)) • vecMulVec s s)ᵀ = (1 / (s ⬝ᵥ s)) • vecMulVec s s := by
  rw [transpose_smul, transpose_vecMulVec]

omit [DecidableEq n] in
/-- The orthogonal projector `P = s sᵀ / (sᵀ s)` is idempotent. -/
private theorem proj_mul_proj (hs : s ≠ 0) :
    (1 / (s ⬝ᵥ s)) • vecMulVec s s * ((1 / (s ⬝ᵥ s)) • vecMulVec s s)
      = (1 / (s ⬝ᵥ s)) • vecMulVec s s := by
  have hss : s ⬝ᵥ s ≠ 0 := mt dotProduct_self_eq_zero.1 hs
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul,
    smul_smul]
  congr 1
  field_simp

/-- **The PSB correction is the least-change projection.** For a symmetric `Δ` with `Δ s = R`,
the correction `psbUpdate B s (B s + R) - B` equals `Δ - (1 - P) Δ (1 - P)` with
`P = s sᵀ / (sᵀ s)`: the update moves `B` by the component of `Δ` outside the subspace
`{(1 - P) Z (1 - P)}` of symmetric matrices vanishing on `s`. -/
theorem psbUpdate_sub_eq_of_isSymm {B Δ : Matrix n n ℝ} (hΔ : Δ.IsSymm) (hs : s ≠ 0) {y : n → ℝ}
    (hΔs : Δ *ᵥ s = y - B *ᵥ s) :
    psbUpdate B s y - B
      = Δ - (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s) * Δ * (1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s) := by
  have hss : s ⬝ᵥ s ≠ 0 := mt dotProduct_self_eq_zero.1 hs
  have hsΔ : s ᵥ* Δ = y - B *ᵥ s := by rw [← mulVec_transpose, hΔ.eq, hΔs]
  have hE : psbUpdate B s y - B
      = (1 / (s ⬝ᵥ s)) • (vecMulVec (y - B *ᵥ s) s + vecMulVec s (y - B *ᵥ s))
        - (((y - B *ᵥ s) ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s := by
    rw [psbUpdate_eq]
    abel
  rw [hE]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, mul_vecMulVec, vecMulVec_mul, hΔs, hsΔ, sub_mulVec, smul_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, sub_vecMulVec, smul_vecMulVec, smul_smul]
  module

/-- **Least change of the Powell-symmetric-Broyden update in the Frobenius norm**
(Dennis–Schnabel Theorem 9.1.1; the characterization stated after (7.46) in
[quarteroni2000numerical]): if `B` is symmetric, `s ≠ 0`, and `B'` is any symmetric matrix
satisfying the secant equation `B' s = y`, then `‖psbUpdate B s y - B‖_F ≤ ‖B' - B‖_F`. With
`Δ = B' - B` the correction is `Δ - (1 - P) Δ (1 - P)`, the complement of a two-sided
compression by the symmetric idempotent `1 - P`, hence no longer than `Δ`
(`Matrix.frobenius_norm_sub_mul_mul_le`). -/
theorem frobenius_norm_psbUpdate_sub_le {B B' : Matrix n n ℝ} (hB : B.IsSymm) (hs : s ≠ 0)
    {y : n → ℝ} (hB' : B'.IsSymm) (hB's : B' *ᵥ s = y) :
    ‖psbUpdate B s y - B‖ ≤ ‖B' - B‖ := by
  have hΔ : (B' - B).IsSymm := hB'.sub hB
  have hΔs : (B' - B) *ᵥ s = y - B *ᵥ s := by rw [sub_mulVec, hB's]
  rw [psbUpdate_sub_eq_of_isSymm hΔ hs hΔs]
  exact frobenius_norm_sub_mul_mul_le _ (by rw [transpose_sub, transpose_one, transpose_proj])
    (by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one, proj_mul_proj hs]
      abel)

/-- **Uniqueness in the least-change characterization**: a symmetric `B'` satisfying the secant
equation and different from `psbUpdate B s y` is strictly farther from `B` in the Frobenius
norm, so the PSB update is *the* solution of the book's minimization problem. -/
theorem frobenius_norm_psbUpdate_sub_lt {B B' : Matrix n n ℝ} (hB : B.IsSymm) (hs : s ≠ 0)
    {y : n → ℝ} (hB' : B'.IsSymm) (hB's : B' *ᵥ s = y) (hne : B' ≠ psbUpdate B s y) :
    ‖psbUpdate B s y - B‖ < ‖B' - B‖ := by
  have hΔ : (B' - B).IsSymm := hB'.sub hB
  have hΔs : (B' - B) *ᵥ s = y - B *ᵥ s := by rw [sub_mulVec, hB's]
  set Q : Matrix n n ℝ := 1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s with hQ
  have hQt : Qᵀ = Q := by rw [hQ, transpose_sub, transpose_one, transpose_proj]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, proj_mul_proj hs]
    abel
  have hE := psbUpdate_sub_eq_of_isSymm hΔ hs hΔs
  rw [← hQ] at hE
  have hpyth := frobenius_norm_sq_sub_mul_mul_add_sq (B' - B) hQt hQQ
  have hN : Q * (B' - B) * Q ≠ 0 := by
    intro h0
    apply hne
    rw [h0, sub_zero] at hE
    exact (sub_left_inj.1 hE).symm
  have hNpos : 0 < ‖Q * (B' - B) * Q‖ := norm_pos_iff.2 hN
  rw [hE]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by nlinarith)

/-- The linear part of the PSB correction: the map
`r ↦ (r sᵀ + s rᵀ) / (sᵀ s) - ((rᵀ s) / (sᵀ s)²) s sᵀ`, so that
`psbUpdate B s y - B` is its value at `r = y - B s`. -/
private noncomputable def psbCorrection (s r : n → ℝ) : Matrix n n ℝ :=
  (1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r) - ((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s

omit [DecidableEq n] in
private theorem psbCorrection_sub (s r₁ r₂ : n → ℝ) :
    psbCorrection s (r₁ - r₂) = psbCorrection s r₁ - psbCorrection s r₂ := by
  simp only [psbCorrection, sub_vecMulVec, vecMulVec_sub, sub_dotProduct]
  module

omit [DecidableEq n] in
private theorem psbUpdate_sub_eq_psbCorrection (B : Matrix n n ℝ) (s y : n → ℝ) :
    psbUpdate B s y - B = psbCorrection s (y - B *ᵥ s) := by
  rw [psbUpdate_eq, psbCorrection]
  abel

/-- The Frobenius norm of the PSB correction is at most `3 ‖r‖ / ‖s‖`. -/
private theorem frobenius_norm_psbCorrection_le (hs : s ≠ 0) (r : n → ℝ) :
    ‖psbCorrection s r‖ ≤ 3 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hrs : |r ⬝ᵥ s| ≤ ‖toLp 2 r‖ * ‖toLp 2 s‖ := by
    have h := abs_real_inner_le_norm (toLp 2 r) (toLp 2 s)
    rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h
  have h1 : ‖(1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r)‖
      ≤ 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_of_nonneg (by positivity)]
    calc 1 / ‖toLp 2 s‖ ^ 2 * ‖vecMulVec r s + vecMulVec s r‖
        ≤ 1 / ‖toLp 2 s‖ ^ 2 * (‖toLp 2 r‖ * ‖toLp 2 s‖ + ‖toLp 2 s‖ * ‖toLp 2 r‖) := by
          gcongr
          exact (norm_add_le _ _).trans
            (add_le_add (frobenius_norm_vecMulVec_le _ _) (frobenius_norm_vecMulVec_le _ _))
      _ = 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by field_simp; ring
  have h2 : ‖((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s‖ ≤ ‖toLp 2 r‖ / ‖toLp 2 s‖ := by
    rw [norm_smul, Real.norm_eq_abs, dotProduct_self_eq_norm_sq, abs_div, abs_of_nonneg
      (by positivity : (0 : ℝ) ≤ (‖toLp 2 s‖ ^ 2) ^ 2)]
    calc |r ⬝ᵥ s| / (‖toLp 2 s‖ ^ 2) ^ 2 * ‖vecMulVec s s‖
        ≤ ‖toLp 2 r‖ * ‖toLp 2 s‖ / (‖toLp 2 s‖ ^ 2) ^ 2 * (‖toLp 2 s‖ * ‖toLp 2 s‖) := by
          gcongr
          exact frobenius_norm_vecMulVec_le _ _
      _ = ‖toLp 2 r‖ / ‖toLp 2 s‖ := by field_simp
  calc ‖psbCorrection s r‖
      ≤ ‖(1 / (s ⬝ᵥ s)) • (vecMulVec r s + vecMulVec s r)‖
        + ‖((r ⬝ᵥ s) / (s ⬝ᵥ s) ^ 2) • vecMulVec s s‖ := norm_sub_le _ _
    _ ≤ 2 * ‖toLp 2 r‖ / ‖toLp 2 s‖ + ‖toLp 2 r‖ / ‖toLp 2 s‖ := add_le_add h1 h2
    _ = 3 * ‖toLp 2 r‖ / ‖toLp 2 s‖ := by ring

/-- **Bounded deterioration of the Powell-symmetric-Broyden update** (Dennis–Schnabel §9.1; the
last display of [quarteroni2000numerical] §7.2.7): if the gradient `g` has the symmetric Hessian
`H` on a convex set `D` containing `x` and `xp = x + s`, with `H` `L`-Lipschitz in the Frobenius
norm on `D`, and `B` is symmetric, then with `y = g xp - g x`

  `‖psbUpdate B s y - H xp‖_F ≤ ‖B - H x‖_F + 3 L ‖s‖`.

The correction is linear in the secant residual `y - B s = (y - H xp s) - (B - H xp) s`; its
value at `-(B - H xp) s` combines with `B - H xp` into the compression
`(1 - P) (B - H xp) (1 - P)`, of norm at most `‖B - H xp‖_F ≤ ‖B - H x‖_F + L ‖s‖`, and its value
at `y - H xp s` has norm at most `3 ‖y - H xp s‖ / ‖s‖ ≤ (3 / 2) L ‖s‖` by the mean value
inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`. The constant obtained is
`5 / 2`; the book's `3` is kept. -/
theorem frobenius_norm_psbUpdate_sub_le_add {g : EuclideanSpace ℝ n → EuclideanSpace ℝ n}
    {H : EuclideanSpace ℝ n → Matrix n n ℝ} {D : Set (EuclideanSpace ℝ n)} (hD : Convex ℝ D)
    (hg : ∀ w ∈ D, HasFDerivAt g (toEuclideanCLM (𝕜 := ℝ) (H w)) w)
    (hH : ∀ w ∈ D, (H w).IsSymm) {L : ℝ} (hL : ∀ w ∈ D, ∀ z ∈ D, ‖H w - H z‖ ≤ L * ‖w - z‖)
    {x : EuclideanSpace ℝ n} (hx : x ∈ D) (hs : s ≠ 0) (hxs : x + toLp 2 s ∈ D)
    {B : Matrix n n ℝ} (hB : B.IsSymm) :
    ‖psbUpdate B s (ofLp (g (x + toLp 2 s) - g x)) - H (x + toLp 2 s)‖
      ≤ ‖B - H x‖ + 3 * L * ‖toLp 2 s‖ := by
  set xp : EuclideanSpace ℝ n := x + toLp 2 s with hxp
  set y : n → ℝ := ofLp (g xp - g x) with hy
  set w : n → ℝ := y - H xp *ᵥ s with hw
  set Δ : Matrix n n ℝ := B - H xp with hΔ
  set Q : Matrix n n ℝ := 1 - (1 / (s ⬝ᵥ s)) • vecMulVec s s with hQ
  have hs0 : 0 < ‖toLp 2 s‖ := norm_pos_iff.2 (by simpa using hs)
  have hsn : ‖xp - x‖ = ‖toLp 2 s‖ := by rw [hxp, add_sub_cancel_left]
  -- `L ≥ 0`
  have hL0 : 0 ≤ L := by
    have h := hL _ hxs _ hx
    rw [hsn] at h
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) hs0
  -- the decomposition of the error
  have hΔsym : Δ.IsSymm := hB.sub (hH _ hxs)
  have hdecomp : psbUpdate B s y - H xp = Q * Δ * Q + psbCorrection s w := by
    have h1 : psbUpdate B s y - H xp = Δ + (psbUpdate B s y - B) := by rw [hΔ]; abel
    have h2 : y - B *ᵥ s = w - Δ *ᵥ s := by rw [hw, hΔ, sub_mulVec]; abel
    have h3 : psbCorrection s (Δ *ᵥ s) = Δ - Q * Δ * Q := by
      have := psbUpdate_sub_eq_of_isSymm (B := H xp) (y := H xp *ᵥ s + Δ *ᵥ s) hΔsym hs
        (by rw [add_sub_cancel_left])
      rw [psbUpdate_sub_eq_psbCorrection, add_sub_cancel_left] at this
      rw [this]
    rw [h1, psbUpdate_sub_eq_psbCorrection, h2, psbCorrection_sub, h3]
    abel
  -- the compression is bounded by `‖Δ‖`
  have hQt : Qᵀ = Q := by rw [hQ, transpose_sub, transpose_one, transpose_proj]
  have hQQ : Q * Q = Q := by
    rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, proj_mul_proj hs]
    abel
  have hcomp : ‖Q * Δ * Q‖ ≤ ‖B - H x‖ + L * ‖toLp 2 s‖ := by
    have h1 : ‖Q * Δ * Q‖ ≤ ‖Δ‖ := by
      have h2 := frobenius_norm_sq_sub_mul_mul_add_sq Δ hQt hQQ
      exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖Δ - Q * Δ * Q‖]) (norm_nonneg _)
    have h2 : ‖Δ‖ ≤ ‖B - H x‖ + ‖H x - H xp‖ := by
      rw [hΔ, show B - H xp = (B - H x) + (H x - H xp) by abel]
      exact norm_add_le _ _
    have h3 : ‖H x - H xp‖ ≤ L * ‖toLp 2 s‖ := by
      have := hL _ hx _ hxs
      rwa [norm_sub_rev x xp, hsn] at this
    linarith
  -- the mean value estimate for the secant residual
  have hopL : ∀ z ∈ D, ‖toEuclideanCLM (𝕜 := ℝ) (H z) - toEuclideanCLM (𝕜 := ℝ) (H xp)‖
      ≤ L * ‖z - xp‖ := fun z hz => by
    rw [← map_sub]
    exact (norm_toEuclideanCLM_le_frobenius_norm _).trans (hL z hz xp hxs)
  have hmv : ‖toLp 2 w‖ ≤ L / 2 * ‖toLp 2 s‖ ^ 2 := by
    have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hD hg hxs hx hopL
    rw [show x - xp = -toLp 2 s from sub_add_cancel_left x (toLp 2 s), map_neg, norm_neg,
      toEuclideanCLM_toLp, sub_neg_eq_add] at h
    have heq : toLp 2 w = -(g x - g xp + toLp 2 (H xp *ᵥ s)) := by
      rw [hw, toLp_sub, toLp_ofLp]
      abel
    rw [heq, norm_neg]
    exact h
  have hcorr : ‖psbCorrection s w‖ ≤ 3 / 2 * L * ‖toLp 2 s‖ := by
    calc ‖psbCorrection s w‖ ≤ 3 * ‖toLp 2 w‖ / ‖toLp 2 s‖ := frobenius_norm_psbCorrection_le hs w
      _ ≤ 3 * (L / 2 * ‖toLp 2 s‖ ^ 2) / ‖toLp 2 s‖ := by gcongr
      _ = 3 / 2 * L * ‖toLp 2 s‖ := by field_simp
  calc ‖psbUpdate B s y - H xp‖ = ‖Q * Δ * Q + psbCorrection s w‖ := by rw [hdecomp]
    _ ≤ ‖Q * Δ * Q‖ + ‖psbCorrection s w‖ := norm_add_le _ _
    _ ≤ (‖B - H x‖ + L * ‖toLp 2 s‖) + 3 / 2 * L * ‖toLp 2 s‖ := add_le_add hcomp hcorr
    _ ≤ ‖B - H x‖ + 3 * L * ‖toLp 2 s‖ := by nlinarith [mul_nonneg hL0 hs0.le]

end Frobenius

/-! ### The BFGS and DFP updates -/

/-- The quadratic form of a symmetric matrix is symmetric in its arguments:
`uᵀ B v = vᵀ B u`. -/
theorem dotProduct_mulVec_comm_of_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (u v : n → ℝ) :
    u ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]

/-- **The Broyden–Fletcher–Goldfarb–Shanno update** (Nocedal–Wright (6.19)) of a Hessian
approximation: `B₊ = B - (B s)(B s)ᵀ / (sᵀ B s) + y yᵀ / (yᵀ s)`. It satisfies the secant
equation, preserves symmetry and, under the curvature condition `yᵀ s > 0`, positive
definiteness; its inverse is the DFP update of the inverse with the roles of `s` and `y`
exchanged. -/
noncomputable def bfgsUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  B - (1 / (s ⬝ᵥ (B *ᵥ s))) • vecMulVec (B *ᵥ s) (B *ᵥ s) + (1 / (y ⬝ᵥ s)) • vecMulVec y y

/-- **The secant equation** for the BFGS update: `B₊ s = y` whenever `sᵀ B s ≠ 0` and
`yᵀ s ≠ 0`. -/
theorem bfgsUpdate_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (hBs : s ⬝ᵥ (B *ᵥ s) ≠ 0)
    (hys : y ⬝ᵥ s ≠ 0) : bfgsUpdate B s y *ᵥ s = y := by
  rw [bfgsUpdate, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec,
    vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, smul_smul,
    smul_smul, dotProduct_comm (B *ᵥ s) s, one_div_mul_cancel hBs, one_div_mul_cancel hys,
    one_smul, one_smul, sub_self, zero_add]

/-- The BFGS update of a symmetric matrix is symmetric. -/
theorem bfgsUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (bfgsUpdate B s y).IsSymm := by
  unfold IsSymm bfgsUpdate
  simp only [transpose_add, transpose_sub, transpose_smul, transpose_vecMulVec, hB.eq]

/-- **The BFGS update preserves positive definiteness under the curvature condition**
(Dennis–Schnabel Theorem 9.2.1 in its BFGS form; Nocedal–Wright §6.1): if `B` is positive
definite and `yᵀ s > 0`, then `bfgsUpdate B s y` is positive definite. For `z ≠ 0`, with
`t = (zᵀ B s) / (sᵀ B s)` and `u = z - t s`,
`zᵀ B₊ z = uᵀ B u + (yᵀ z)² / (yᵀ s)`; the first term is positive unless `z = t s`, in which
case `t ≠ 0` and the second term is `t² yᵀ s > 0`. -/
theorem bfgsUpdate_posDef {B : Matrix n n ℝ} (hB : B.PosDef) {s y : n → ℝ} (hys : 0 < y ⬝ᵥ s) :
    (bfgsUpdate B s y).PosDef := by
  have hBs : B.IsSymm := isHermitian_iff_isSymm.1 hB.isHermitian
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hys
  have ha : 0 < s ⬝ᵥ (B *ᵥ s) := by simpa using hB.dotProduct_mulVec_pos hs
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_iff_isSymm.2 (bfgsUpdate_isSymm hBs s y))
    fun z hz => ?_
  rw [star_trivial]
  set a : ℝ := s ⬝ᵥ (B *ᵥ s) with ha_def
  set b : ℝ := y ⬝ᵥ s with hb_def
  set t : ℝ := z ⬝ᵥ (B *ᵥ s) / a with ht_def
  have hq : z ⬝ᵥ (bfgsUpdate B s y *ᵥ z)
      = (z - t • s) ⬝ᵥ (B *ᵥ (z - t • s)) + 1 / b * (y ⬝ᵥ z) ^ 2 := by
    simp only [bfgsUpdate, sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, dotProduct_sub, dotProduct_add, dotProduct_smul, mulVec_sub,
      mulVec_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, ← ha_def, ← hb_def]
    rw [dotProduct_comm (B *ᵥ s) z, dotProduct_mulVec_comm_of_isSymm hBs s z,
      dotProduct_comm z y, ht_def]
    field_simp
    ring
  rw [hq]
  by_cases hu : z - t • s = 0
  · have hz' : z = t • s := sub_eq_zero.1 hu
    have ht : t ≠ 0 := by
      rintro ht0
      rw [ht0, zero_smul] at hz'
      exact hz hz'
    rw [hu, mulVec_zero, dotProduct_zero, zero_add, hz', dotProduct_smul, smul_eq_mul, ← hb_def,
      show 1 / b * (t * b) ^ 2 = t ^ 2 * b by field_simp]
    positivity
  · have h := hB.dotProduct_mulVec_pos hu
    rw [star_trivial] at h
    have : 0 ≤ 1 / b * (y ⬝ᵥ z) ^ 2 := by positivity
    linarith

section DFP

variable [DecidableEq n]

/-- **The Davidon–Fletcher–Powell update** (Dennis–Schnabel (9.2.7); Nocedal–Wright (6.13)) of
a Hessian approximation: with `ρ = 1 / (yᵀ s)`,
`B₊ = (1 - ρ y sᵀ) B (1 - ρ s yᵀ) + ρ y yᵀ`. It satisfies the secant equation, preserves symmetry
and, under the curvature condition `yᵀ s > 0`, positive definiteness. Not in the text of
[quarteroni2000numerical], which defers positive definite updates to Dennis–Schnabel §9.2. -/
noncomputable def dfpUpdate (B : Matrix n n ℝ) (s y : n → ℝ) : Matrix n n ℝ :=
  (1 - (1 / (y ⬝ᵥ s)) • vecMulVec y s) * B * (1 - (1 / (y ⬝ᵥ s)) • vecMulVec s y)
    + (1 / (y ⬝ᵥ s)) • vecMulVec y y

/-- **The secant equation** for the DFP update: `B₊ s = y` whenever `yᵀ s ≠ 0`. -/
theorem dfpUpdate_mulVec (B : Matrix n n ℝ) {s y : n → ℝ} (hys : y ⬝ᵥ s ≠ 0) :
    dfpUpdate B s y *ᵥ s = y := by
  have h : (1 - (1 / (y ⬝ᵥ s)) • vecMulVec s y) *ᵥ s = 0 := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      smul_smul, one_div_mul_cancel hys, one_smul, sub_self]
  rw [dfpUpdate, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, h, mulVec_zero, mulVec_zero,
    zero_add, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    one_div_mul_cancel hys, one_smul]

/-- The DFP update of a symmetric matrix is symmetric. -/
theorem dfpUpdate_isSymm {B : Matrix n n ℝ} (hB : B.IsSymm) (s y : n → ℝ) :
    (dfpUpdate B s y).IsSymm := by
  unfold IsSymm dfpUpdate
  simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, transpose_smul,
    transpose_vecMulVec, hB.eq, Matrix.mul_assoc]

/-- **The DFP update preserves positive definiteness under the curvature condition**
(Dennis–Schnabel Theorem 9.2.1; Nocedal–Wright §6.1): if `B` is positive definite and
`yᵀ s > 0`, then `dfpUpdate B s y` is positive definite. For `z ≠ 0`, with
`w = (1 - ρ s yᵀ) z = z - ρ (yᵀ z) s`, `zᵀ B₊ z = wᵀ B w + ρ (yᵀ z)²`; the first term is positive
unless `w = 0`, in which case `yᵀ z ≠ 0` (else `z = 0`) and the second term is positive. -/
theorem dfpUpdate_posDef {B : Matrix n n ℝ} (hB : B.PosDef) {s y : n → ℝ} (hys : 0 < y ⬝ᵥ s) :
    (dfpUpdate B s y).PosDef := by
  have hBs : B.IsSymm := isHermitian_iff_isSymm.1 hB.isHermitian
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_iff_isSymm.2 (dfpUpdate_isSymm hBs s y))
    fun z hz => ?_
  rw [star_trivial]
  set ρ : ℝ := 1 / (y ⬝ᵥ s) with hρ
  have hρ0 : 0 < ρ := by positivity
  set N : Matrix n n ℝ := 1 - ρ • vecMulVec s y with hN
  have hNt : (1 - ρ • vecMulVec y s)ᵀ = N := by
    rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
  have hNz : N *ᵥ z = z - (ρ * (y ⬝ᵥ z)) • s := by
    rw [hN, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
  have hq : z ⬝ᵥ (dfpUpdate B s y *ᵥ z) = (N *ᵥ z) ⬝ᵥ (B *ᵥ (N *ᵥ z)) + ρ * (y ⬝ᵥ z) ^ 2 := by
    rw [dfpUpdate, ← hρ, ← hN, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_add,
      dotProduct_mulVec, ← mulVec_transpose, hNt, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      dotProduct_smul, dotProduct_smul, dotProduct_comm z y, smul_eq_mul, smul_eq_mul, sq]
  rw [hq]
  by_cases hw : N *ᵥ z = 0
  · have hyz : y ⬝ᵥ z ≠ 0 := by
      intro h0
      rw [hNz, h0, mul_zero, zero_smul, sub_zero] at hw
      exact hz hw
    rw [hw, mulVec_zero, dotProduct_zero, zero_add]
    positivity
  · have h := hB.dotProduct_mulVec_pos hw
    rw [star_trivial] at h
    have : 0 ≤ ρ * (y ⬝ᵥ z) ^ 2 := by positivity
    linarith

end DFP

end Matrix
