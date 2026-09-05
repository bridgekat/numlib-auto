import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.CG
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Section04
import NumlibSurface.SaadSparse.Chapter06.Section06

/-!
# Saad, §6.7: the conjugate gradient method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.7.

The four algorithms of the section are `cg` (**Algorithm 6.18**, the two-term conjugate
gradient recurrence, with `cgX`, `cgR`, `cgP`, `cgAlpha`, `cgBeta` reading off its state),
`cg3` (**Algorithm 6.19**, the three-term variant, with `cgGamma` and `cgRho`),
`lanczosMethod` (**Algorithm 6.16**, `x_m = x_0 + V_m T_m^{-1}(β e_1)`, (6.86)) and
`dLanczosX` (**Algorithm 6.17**, D-Lanczos, with `dlLambda`, `dlEta`, `dlZeta`, `dlP` for
(6.88)–(6.89)).

The pivot is `cg_eq_CG`: Algorithm 6.18 *is* the backbone recurrence `CG.iterate`, so the
orthogonality of the residuals, the `A`-conjugacy of the directions, the Galerkin property, the
identification of the residuals with the Lanczos vectors and the three-term form all come from
`Numlib/Krylov/CG.lean`. The other three algorithms are then tied to it: `lanczosMethodAt` is
the Galerkin iterate (`lanczosMethodAt_isGalerkinIterate`, (6.86)) with residual (6.87),
D-Lanczos produces the same iterates (`dLanczosX_eq_lanczosMethodAt`, `cgX_eq_dLanczosX`), and
the three-term algorithm produces the CG iterates (`cg3_eq`).

Indices are `0`-based: `cgX A b x₀ j` is the book's `x_j` and `cgAlpha A b x₀ j` its `α_j`
(the book already numbers the conjugate gradient iterates from `0`), while
`lanczosV A v₁ j` is the book's `v_{j+1}` and `lanczosBeta A v₁ j` its `β_{j+1}`, as in
`Chapter06/Section06.lean`. Division by a vanishing quantity is `0`, which reproduces the book's
breakdown behaviour.

Definitions are polymorphic in `𝕜`; the numbered results are stated over `ℝ` with `A`
symmetric positive definite, the book's generality in §6.7.
-/

open scoped ComplexOrder Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.18: the conjugate gradient method -/

/-- The step length `α_j = (r_j, r_j)/(A p_j, p_j)` of Algorithm 6.18, line 3. -/
noncomputable def cgStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2)

/-- The next residual `r_{j+1} = r_j - α_j A p_j` of Algorithm 6.18, line 5. -/
noncomputable def cgStepR (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 :=
  s.2.1 - cgStepAlpha A s • op A s.2.2

/-- The coefficient `β_j = (r_{j+1}, r_{j+1})/(r_j, r_j)` of Algorithm 6.18, line 6. -/
noncomputable def cgStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝕜 :=
  inner 𝕜 (cgStepR A s) (cgStepR A s) / inner 𝕜 s.2.1 s.2.1

/-- One pass through lines 3–7 of **Algorithm 6.18** on the triple `(x_j, r_j, p_j)`. -/
noncomputable def cgStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + cgStepAlpha A s • s.2.2, cgStepR A s, cgStepR A s + cgStepBeta A s • s.2.2)

/-- **Algorithm 6.18** (conjugate gradient) run for `j` steps: the triple `(x_j, r_j, p_j)`,
started from `r_0 = b - A x_0` and `p_0 = r_0`. -/
noncomputable def cg (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (cgStep A)^[j] (x₀, b - op A x₀, b - op A x₀)

theorem cgStepAlpha_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepAlpha A s = inner 𝕜 s.2.1 s.2.1 / inner 𝕜 s.2.2 (op A s.2.2) := rfl

theorem cgStepR_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepR A s = s.2.1 - cgStepAlpha A s • op A s.2.2 := rfl

theorem cgStepBeta_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : 𝔼 × 𝔼 × 𝔼) :
    cgStepBeta A s = inner 𝕜 (cgStepR A s) (cgStepR A s) / inner 𝕜 s.2.1 s.2.1 := rfl

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The `j`-th conjugate gradient iterate `x_j` of Algorithm 6.18. -/
noncomputable def cgX (j : ℕ) : 𝔼 := (cg A b x₀ j).1

/-- The `j`-th conjugate gradient residual `r_j` of Algorithm 6.18. -/
noncomputable def cgR (j : ℕ) : 𝔼 := (cg A b x₀ j).2.1

/-- The `j`-th conjugate gradient search direction `p_j` of Algorithm 6.18. -/
noncomputable def cgP (j : ℕ) : 𝔼 := (cg A b x₀ j).2.2

/-- The step length `α_j` of Algorithm 6.18 at step `j`. -/
noncomputable def cgAlpha (j : ℕ) : 𝕜 := cgStepAlpha A (cg A b x₀ j)

/-- The direction coefficient `β_j` of Algorithm 6.18 at step `j`. -/
noncomputable def cgBeta (j : ℕ) : 𝕜 := cgStepBeta A (cg A b x₀ j)

theorem cg_succ (j : ℕ) : cg A b x₀ (j + 1) = cgStep A (cg A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem cgX_zero : cgX A b x₀ 0 = x₀ := rfl

@[simp] theorem cgR_zero : cgR A b x₀ 0 = b - op A x₀ := rfl

/-- Algorithm 6.18, line 1: `p_0 = r_0`. -/
@[simp] theorem cgP_zero : cgP A b x₀ 0 = cgR A b x₀ 0 := rfl

/-- (6.92): `α_j = (r_j, r_j)/(A p_j, p_j)`. -/
theorem cgAlpha_eq (j : ℕ) : cgAlpha A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j)) := rfl

/-- (6.90): `x_{j+1} = x_j + α_j p_j`. -/
theorem cgX_succ (j : ℕ) :
    cgX A b x₀ (j + 1) = cgX A b x₀ j + cgAlpha A b x₀ j • cgP A b x₀ j := by
  rw [cgX, cg_succ]
  rfl

/-- (6.91): `r_{j+1} = r_j - α_j A p_j`. -/
theorem cgR_succ (j : ℕ) :
    cgR A b x₀ (j + 1) = cgR A b x₀ j - cgAlpha A b x₀ j • op A (cgP A b x₀ j) := by
  rw [cgR, cg_succ]
  rfl

theorem cgR_succ_eq_cgStepR (j : ℕ) : cgR A b x₀ (j + 1) = cgStepR A (cg A b x₀ j) := by
  rw [cgR, cg_succ]
  rfl

/-- `β_j = (r_{j+1}, r_{j+1})/(r_j, r_j)`, Algorithm 6.18, line 6. -/
theorem cgBeta_eq (j : ℕ) : cgBeta A b x₀ j =
    inner 𝕜 (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) /
      inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) := by
  rw [cgBeta, cgStepBeta_def, cgR_succ_eq_cgStepR]
  rfl

/-- (6.93): `p_{j+1} = r_{j+1} + β_j p_j`. -/
theorem cgP_succ (j : ℕ) :
    cgP A b x₀ (j + 1) = cgR A b x₀ (j + 1) + cgBeta A b x₀ j • cgP A b x₀ j := by
  rw [cgP, cg_succ, cgR_succ_eq_cgStepR]
  rfl

/-- (6.94) in division-free form: `α_j A p_j = r_j - r_{j+1}`. -/
theorem cgAlpha_smul_apply_cgP (j : ℕ) :
    cgAlpha A b x₀ j • op A (cgP A b x₀ j) = cgR A b x₀ j - cgR A b x₀ (j + 1) := by
  rw [cgR_succ]
  abel

/-! ### Identification with the backbone conjugate gradient recurrence -/

private theorem cgStepAlpha_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepAlpha A (s.x, s.r, s.p) = CG.alpha (op A) s := by
  change (inner 𝕜 s.r s.r / inner 𝕜 s.p (op A s.p) : 𝕜)
    = inner 𝕜 s.r s.r / inner 𝕜 (op A s.p) s.p
  rw [hA s.p s.p]

private theorem cgStepR_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepR A (s.x, s.r, s.p) = (CG.step (op A) s).r := by
  rw [cgStepR_def, cgStepAlpha_eq_CG A hA s, CG.step_r]

private theorem cgStepBeta_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStepBeta A (s.x, s.r, s.p) = CG.beta (op A) s := by
  rw [cgStepBeta_def, cgStepR_eq_CG A hA s]
  rfl

private theorem cgStep_eq_CG (hA : (op A).IsSymmetric) (s : CG.State 𝔼) :
    cgStep A (s.x, s.r, s.p) =
      ((CG.step (op A) s).x, (CG.step (op A) s).r, (CG.step (op A) s).p) := by
  rw [cgStep, cgStepAlpha_eq_CG A hA s, cgStepR_eq_CG A hA s, cgStepBeta_eq_CG A hA s,
    CG.step_x, CG.step_p]

/-- **The bridge to the backbone**: Algorithm 6.18 is the backbone conjugate gradient
recurrence `CG.iterate`. Only the symmetry of `A` is needed, to move `A` across the inner
product in `α_j`. -/
theorem cg_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cg A b x₀ j = ((CG.iterate (op A) b x₀ j).x, (CG.iterate (op A) b x₀ j).r,
      (CG.iterate (op A) b x₀ j).p) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [cg_succ, ih, CG.iterate_succ, cgStep_eq_CG A hA]

theorem cgX_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgX A b x₀ j = (CG.iterate (op A) b x₀ j).x := by rw [cgX, cg_eq_CG A b x₀ hA]

theorem cgR_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgR A b x₀ j = (CG.iterate (op A) b x₀ j).r := by rw [cgR, cg_eq_CG A b x₀ hA]

theorem cgP_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgP A b x₀ j = (CG.iterate (op A) b x₀ j).p := by rw [cgP, cg_eq_CG A b x₀ hA]

theorem cgAlpha_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgAlpha A b x₀ j = CG.alpha (op A) (CG.iterate (op A) b x₀ j) := by
  rw [cgAlpha, cg_eq_CG A b x₀ hA, cgStepAlpha_eq_CG A hA]

theorem cgBeta_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgBeta A b x₀ j = CG.beta (op A) (CG.iterate (op A) b x₀ j) := by
  rw [cgBeta, cg_eq_CG A b x₀ hA, cgStepBeta_eq_CG A hA]

/-- The state's residual is the true residual, `r_j = b - A x_j`. -/
theorem cgR_eq_residual (hA : (op A).IsSymmetric) (j : ℕ) :
    cgR A b x₀ j = b - op A (cgX A b x₀ j) := by
  rw [cgR_eq_CG A b x₀ hA, cgX_eq_CG A b x₀ hA, CG.residual_eq]

/-! ### The orthogonality relations of §6.7.1 (Proposition 6.20 for Algorithm 6.18) -/

/-- A positive definite matrix is a symmetric coercive operator on `𝕜ⁿ`. -/
theorem isSymmetricCoercive_op_of_posDef {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) :
    (op A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 hA

variable {A b x₀}

/-- The residuals of Algorithm 6.18 are mutually orthogonal. -/
theorem inner_cgR_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (cgR A b x₀ i) (cgR A b x₀ j) = 0 := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- The search directions of Algorithm 6.18 are `A`-conjugate. -/
theorem inner_apply_cgP_eq_zero (hA : A.PosDef) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (op A (cgP A b x₀ i)) (cgP A b x₀ j) = 0 := by
  rw [cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_apply_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- `(r_i, p_j) = 0` for `j < i`: the Galerkin condition in the form used in §6.7.1. -/
theorem inner_cgR_cgP_eq_zero (hA : A.PosDef) {i j : ℕ} (h : j < i) :
    inner 𝕜 (cgR A b x₀ i) (cgP A b x₀ j) = 0 := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_direction_eq_zero b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- `(r_i, p_j) = ‖r_j‖²` for `i ≤ j`. -/
theorem inner_cgR_cgP (hA : A.PosDef) {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (cgR A b x₀ i) (cgP A b x₀ j) = ((‖cgR A b x₀ j‖ ^ 2 : ℝ) : 𝕜) := by
  rw [cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgP_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
    cgR_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.inner_residual_direction_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) h

/-- The direction vanishes with the residual, so the algorithm is stationary after
breakdown. -/
theorem cgP_eq_zero_of_cgR_eq_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j = 0) :
    cgP A b x₀ j = 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgP_eq_CG A b x₀ hs]
  exact CG.direction_eq_zero_of_residual_eq_zero (op A) b x₀ (by rwa [cgR_eq_CG A b x₀ hs] at hr)

/-- `(A p_j, p_j) ≠ 0` as long as `r_j ≠ 0`: Algorithm 6.18 is well defined until the residual
vanishes. -/
theorem inner_cgP_apply_cgP_ne_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j)) ≠ 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  have hp := CG.re_inner_apply_direction_pos b x₀ (isSymmetricCoercive_op_of_posDef hA)
    (k := j) (by rwa [cgR_eq_CG A b x₀ hs] at hr)
  rw [← cgP_eq_CG A b x₀ hs, hs (cgP A b x₀ j) (cgP A b x₀ j)] at hp
  intro h
  rw [h] at hp
  simp at hp

/-- `α_j ≠ 0` as long as `r_j ≠ 0`. -/
theorem cgAlpha_ne_zero (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    cgAlpha A b x₀ j ≠ 0 := by
  rw [cgAlpha_eq]
  exact div_ne_zero (fun h => hr (inner_self_eq_zero.1 h)) (inner_cgP_apply_cgP_ne_zero hA hr)

/-- (6.92), second form: `(A p_j, p_j) = (A p_j, r_j)`, because `p_j - r_j` is a multiple of
`p_{j-1}` and the directions are `A`-conjugate. -/
theorem inner_cgP_apply_cgP_eq (hA : A.PosDef) (j : ℕ) :
    inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ j))
      = inner 𝕜 (cgR A b x₀ j) (op A (cgP A b x₀ j)) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  cases j with
  | zero => rw [cgP_zero]
  | succ j =>
    have hconj : inner 𝕜 (cgP A b x₀ j) (op A (cgP A b x₀ (j + 1))) = 0 := by
      rw [← hs (cgP A b x₀ j) (cgP A b x₀ (j + 1))]
      exact inner_apply_cgP_eq_zero hA (by omega)
    nth_rewrite 1 [cgP_succ]
    rw [inner_add_left, inner_smul_left, hconj, mul_zero, add_zero]

/-- (6.92): `α_j = (r_j, r_j)/(A p_j, r_j)`, the form the book's derivation produces. -/
theorem cgAlpha_eq' (hA : A.PosDef) (j : ℕ) : cgAlpha A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgP A b x₀ j)) := by
  rw [cgAlpha_eq, inner_cgP_apply_cgP_eq hA]

/-- (6.94): `A p_j = -(r_{j+1} - r_j)/α_j` as long as `r_j ≠ 0`. -/
theorem apply_cgP_eq (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    op A (cgP A b x₀ j) =
      -((cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ (j + 1) - cgR A b x₀ j)) := by
  have h2 : -((cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ (j + 1) - cgR A b x₀ j))
      = (cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ j - cgR A b x₀ (j + 1)) := by
    rw [← smul_neg, neg_sub]
  rw [h2, ← cgAlpha_smul_apply_cgP, smul_smul, inv_mul_cancel₀ (cgAlpha_ne_zero hA hr), one_smul]

variable (A b x₀)

/-! ### The starting vector of Algorithms 6.16 and 6.17 -/

/-- The unit starting vector `v_1 = r_0/β`, `β = ‖r_0‖₂`, of Algorithms 6.16 and 6.17,
line 1. -/
noncomputable def unitResidual : 𝔼 := ((‖b - op A x₀‖ : 𝕜))⁻¹ • (b - op A x₀)

theorem unitResidual_def :
    unitResidual A b x₀ = ((‖b - op A x₀‖ : 𝕜))⁻¹ • (b - op A x₀) := rfl

theorem norm_unitResidual {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼}
    (hb : b - op A x₀ ≠ 0) : ‖unitResidual A b x₀‖ = 1 :=
  norm_norm_inv_smul hb

/-- The Krylov subspaces of the unit starting vector are those of the residual `r_0`. -/
theorem krylov_unitResidual {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼}
    (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    krylov A (unitResidual A b x₀) m = Krylov.subspace (op A) (b - op A x₀) m := by
  have hc : ((‖b - op A x₀‖ : 𝕜))⁻¹ ≠ 0 :=
    inv_ne_zero (by simpa using norm_ne_zero_iff.2 hb)
  rw [unitResidual_def, krylov_smul A _ hc, krylov_eq]

/-! ### Algorithm 6.19: the three-term recurrence variant -/

private theorem inner_self_div (x y : 𝔼) :
    inner 𝕜 x x / inner 𝕜 y y = ((‖x‖ ^ 2 / ‖y‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- `γ_j = (r_j, r_j)/(A r_j, r_j)`, Algorithm 6.19, line 3. -/
noncomputable def cgGamma (j : ℕ) : 𝕜 :=
  inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgR A b x₀ j))

theorem cgGamma_def (j : ℕ) : cgGamma A b x₀ j =
    inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j) / inner 𝕜 (cgR A b x₀ j) (op A (cgR A b x₀ j)) := rfl

/-- `ρ_0 = 1` and (6.97) for `j > 0`, Algorithm 6.19, line 4. -/
noncomputable def cgRho (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℕ → 𝕜
  | 0 => 1
  | j + 1 => (1 - cgGamma A b x₀ (j + 1) / cgGamma A b x₀ j *
      (inner 𝕜 (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) /
        inner 𝕜 (cgR A b x₀ j) (cgR A b x₀ j)) / cgRho A b x₀ j)⁻¹

@[simp] theorem cgRho_zero : cgRho A b x₀ 0 = 1 := rfl

/-- (6.97). -/
theorem cgRho_succ (j : ℕ) : cgRho A b x₀ (j + 1) =
    (1 - cgGamma A b x₀ (j + 1) / cgGamma A b x₀ j *
      ((‖cgR A b x₀ (j + 1)‖ ^ 2 / ‖cgR A b x₀ j‖ ^ 2 : ℝ) : 𝕜) / cgRho A b x₀ j)⁻¹ := by
  rw [cgRho, inner_self_div]

theorem cgGamma_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgGamma A b x₀ j = CG.gamma (op A) b x₀ j := by
  have h : CG.gamma (op A) b x₀ j =
      inner 𝕜 (CG.iterate (op A) b x₀ j).r (CG.iterate (op A) b x₀ j).r /
        inner 𝕜 (CG.iterate (op A) b x₀ j).r (op A (CG.iterate (op A) b x₀ j).r) := by
    change inner 𝕜 _ _ / inner 𝕜 (op A _) _ = _
    rw [hA _ _]
  rw [h, cgGamma_def, cgR_eq_CG A b x₀ hA]

theorem cgRho_eq_CG (hA : (op A).IsSymmetric) (j : ℕ) :
    cgRho A b x₀ j = CG.rho (op A) b x₀ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hCG : CG.rho (op A) b x₀ (j + 1) =
        (1 - CG.gamma (op A) b x₀ (j + 1) / CG.gamma (op A) b x₀ j *
          ((‖(CG.iterate (op A) b x₀ (j + 1)).r‖ ^ 2 /
            ‖(CG.iterate (op A) b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) / CG.rho (op A) b x₀ j)⁻¹ := rfl
    rw [cgRho_succ, hCG, ih, cgGamma_eq_CG A b x₀ hA, cgGamma_eq_CG A b x₀ hA,
      cgR_eq_CG A b x₀ hA, cgR_eq_CG A b x₀ hA]

variable {A b x₀}

/-- (6.98): `x_{m+1} = ρ_m (x_m + γ_m r_m) + (1 - ρ_m) x_{m-1}`, with `x_{-1}` read as `x_0`
(harmless because `ρ_0 = 1`). -/
theorem equation_6_98 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m, cgR A b x₀ j ≠ 0) :
    cgX A b x₀ (m + 1) = cgRho A b x₀ m • (cgX A b x₀ m + cgGamma A b x₀ m • cgR A b x₀ m) +
      (1 - cgRho A b x₀ m) • cgX A b x₀ (m - 1) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgX_eq_CG A b x₀ hs, cgX_eq_CG A b x₀ hs, cgX_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs,
    cgRho_eq_CG A b x₀ hs, cgGamma_eq_CG A b x₀ hs]
  exact CG.iterate_succ_eq_three_term b x₀ (isSymmetricCoercive_op_of_posDef hA) m
    fun j hj => by rw [← cgR_eq_CG A b x₀ hs]; exact hr j hj

/-- (6.96): `r_{m+1} = ρ_m (r_m - γ_m A r_m) + (1 - ρ_m) r_{m-1}`. -/
theorem equation_6_96 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m, cgR A b x₀ j ≠ 0) :
    cgR A b x₀ (m + 1) =
      cgRho A b x₀ m • (cgR A b x₀ m - cgGamma A b x₀ m • op A (cgR A b x₀ m)) +
        (1 - cgRho A b x₀ m) • cgR A b x₀ (m - 1) := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  rw [cgR_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs, cgR_eq_CG A b x₀ hs,
    cgRho_eq_CG A b x₀ hs, cgGamma_eq_CG A b x₀ hs]
  exact CG.residual_succ_eq_three_term b x₀ (isSymmetricCoercive_op_of_posDef hA) m
    fun j hj => by rw [← cgR_eq_CG A b x₀ hs]; exact hr j hj

variable (A b x₀)

/-- The running state of **Algorithm 6.19** after `j` steps:
`(x_j, x_{j-1}, r_j, r_{j-1}, ρ_{j-1}, γ_{j-1})`. The book's `x_{-1} = 0` is the initial
`xPrev`; the initial `rPrev = 0` makes `(r_0,r_0)/(r_{-1},r_{-1}) = 0` in Lean, which
reproduces line 1's `ρ_0 = 1`. -/
structure CG3State (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] where
  /-- The current iterate `x_j`. -/
  x : EuclideanSpace 𝕜 (Fin n)
  /-- The previous iterate `x_{j-1}`. -/
  xPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The current residual `r_j`. -/
  r : EuclideanSpace 𝕜 (Fin n)
  /-- The previous residual `r_{j-1}`. -/
  rPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The previous coefficient `ρ_{j-1}`. -/
  rho : 𝕜
  /-- The previous coefficient `γ_{j-1}`. -/
  gamma : 𝕜

/-- `γ_j = (r_j, r_j)/(A r_j, r_j)`, Algorithm 6.19, line 3. -/
noncomputable def cg3StepGamma (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : 𝕜 :=
  inner 𝕜 s.r s.r / inner 𝕜 s.r (op A s.r)

/-- (6.97), Algorithm 6.19, line 4. -/
noncomputable def cg3StepRho (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : 𝕜 :=
  (1 - cg3StepGamma A s / s.gamma * (inner 𝕜 s.r s.r / inner 𝕜 s.rPrev s.rPrev) / s.rho)⁻¹

/-- One pass through lines 3–6 of **Algorithm 6.19**. -/
noncomputable def cg3Step (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) : CG3State n 𝕜 :=
  { x := cg3StepRho A s • (s.x + cg3StepGamma A s • s.r) + (1 - cg3StepRho A s) • s.xPrev,
    xPrev := s.x,
    r := cg3StepRho A s • (s.r - cg3StepGamma A s • op A s.r) + (1 - cg3StepRho A s) • s.rPrev,
    rPrev := s.r,
    rho := cg3StepRho A s,
    gamma := cg3StepGamma A s }

/-- The initial state of **Algorithm 6.19**, line 1: `x_0`, `x_{-1} = 0`, `r_0 = b - A x_0`
and `r_{-1} = 0`. -/
noncomputable def cg3Init (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : CG3State n 𝕜 :=
  { x := x₀, xPrev := 0, r := b - op A x₀, rPrev := 0, rho := 1, gamma := 1 }

/-- **Algorithm 6.19** (conjugate gradient, three-term recurrence variant) run for `j` steps. -/
noncomputable def cg3 (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (j : ℕ) : CG3State n 𝕜 :=
  (cg3Step A)^[j] (cg3Init A b x₀)

theorem cg3StepGamma_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3StepGamma A s = inner 𝕜 s.r s.r / inner 𝕜 s.r (op A s.r) := rfl

theorem cg3StepRho_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3StepRho A s =
      (1 - cg3StepGamma A s / s.gamma * (inner 𝕜 s.r s.r / inner 𝕜 s.rPrev s.rPrev) / s.rho)⁻¹ :=
  rfl

theorem cg3Step_def (A : Matrix (Fin n) (Fin n) 𝕜) (s : CG3State n 𝕜) :
    cg3Step A s =
      { x := cg3StepRho A s • (s.x + cg3StepGamma A s • s.r) + (1 - cg3StepRho A s) • s.xPrev,
        xPrev := s.x,
        r := cg3StepRho A s • (s.r - cg3StepGamma A s • op A s.r) +
          (1 - cg3StepRho A s) • s.rPrev,
        rPrev := s.r, rho := cg3StepRho A s, gamma := cg3StepGamma A s } := rfl

theorem cg3_succ (j : ℕ) : cg3 A b x₀ (j + 1) = cg3Step A (cg3 A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

private theorem cg3Step_state (j : ℕ) :
    cg3Step A
      { x := cgX A b x₀ (j + 1), xPrev := cgX A b x₀ j, r := cgR A b x₀ (j + 1),
        rPrev := cgR A b x₀ j, rho := cgRho A b x₀ j, gamma := cgGamma A b x₀ j } =
      { x := cgRho A b x₀ (j + 1) •
            (cgX A b x₀ (j + 1) + cgGamma A b x₀ (j + 1) • cgR A b x₀ (j + 1)) +
          (1 - cgRho A b x₀ (j + 1)) • cgX A b x₀ j,
        xPrev := cgX A b x₀ (j + 1),
        r := cgRho A b x₀ (j + 1) •
            (cgR A b x₀ (j + 1) - cgGamma A b x₀ (j + 1) • op A (cgR A b x₀ (j + 1))) +
          (1 - cgRho A b x₀ (j + 1)) • cgR A b x₀ j,
        rPrev := cgR A b x₀ (j + 1),
        rho := cgRho A b x₀ (j + 1),
        gamma := cgGamma A b x₀ (j + 1) } := rfl

private theorem cg3_zero : cg3 A b x₀ 0 = cg3Init A b x₀ := rfl

private theorem cg3StepGamma_init :
    cg3StepGamma A (cg3Init A b x₀) = cgGamma A b x₀ 0 := rfl

private theorem cg3StepRho_init : cg3StepRho A (cg3Init A b x₀) = 1 := by
  rw [cg3StepRho_def]
  simp [cg3Init]

variable {A b x₀}

/-- **Algorithm 6.19 computes the conjugate gradient iterates**: as long as the residuals do
not vanish, its state after `j + 1` steps holds `x_{j+1}, x_j, r_{j+1}, r_j` of Algorithm 6.18
together with `ρ_j` and `γ_j`. -/
theorem cg3_eq (hA : A.PosDef) {j : ℕ} (hr : ∀ i ≤ j, cgR A b x₀ i ≠ 0) :
    cg3 A b x₀ (j + 1) =
      { x := cgX A b x₀ (j + 1), xPrev := cgX A b x₀ j, r := cgR A b x₀ (j + 1),
        rPrev := cgR A b x₀ j, rho := cgRho A b x₀ j, gamma := cgGamma A b x₀ j } := by
  induction j with
  | zero =>
    rw [cg3_succ, cg3_zero, cg3Step_def, cg3StepRho_init, cg3StepGamma_init,
      equation_6_98 hA (m := 0) hr, equation_6_96 hA (m := 0) hr]
    simp [cg3Init]
  | succ j ih =>
    rw [cg3_succ, ih (fun i hi => hr i (by omega)), cg3Step_state,
      equation_6_98 hA (m := j + 1) hr, equation_6_96 hA (m := j + 1) hr]
    simp

/-- **P-6.17**: (6.97) is forced by (6.96) and the orthogonality of the residuals. Any scalar
`ρ` for which the three-term residual recurrence holds at step `m + 1` is the `ρ_{m+1}` of
(6.97). -/
theorem equation_6_97_of_eq_6_96 (hA : A.PosDef) {m : ℕ} (hr : ∀ j ≤ m + 1, cgR A b x₀ j ≠ 0)
    {ρ : 𝕜}
    (h96 : cgR A b x₀ (m + 2) =
      ρ • (cgR A b x₀ (m + 1) - cgGamma A b x₀ (m + 1) • op A (cgR A b x₀ (m + 1))) +
        (1 - ρ) • cgR A b x₀ m) :
    ρ = cgRho A b x₀ (m + 1) := by
  set c := cgRho A b x₀ (m + 1) with hc
  set X := cgGamma A b x₀ (m + 1) *
    inner 𝕜 (cgR A b x₀ m) (op A (cgR A b x₀ (m + 1))) + inner 𝕜 (cgR A b x₀ m) (cgR A b x₀ m)
    with hX
  have key : ∀ σ : 𝕜, cgR A b x₀ (m + 2) =
      σ • (cgR A b x₀ (m + 1) - cgGamma A b x₀ (m + 1) • op A (cgR A b x₀ (m + 1))) +
        (1 - σ) • cgR A b x₀ m → σ * X = inner 𝕜 (cgR A b x₀ m) (cgR A b x₀ m) := by
    intro σ hσ
    have h := congrArg (fun z => (inner 𝕜 (cgR A b x₀ m) z : 𝕜)) hσ
    simp only [inner_add_right, inner_smul_right, inner_sub_right] at h
    rw [inner_cgR_eq_zero hA (show m ≠ m + 2 by omega),
      inner_cgR_eq_zero hA (show m ≠ m + 1 by omega)] at h
    rw [hX]
    linear_combination h
  have hcX := key c (equation_6_96 hA (m := m + 1) hr)
  have hρX := key ρ h96
  have hXne : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcX
    exact hr m (by omega) (inner_self_eq_zero.1 hcX.symm)
  exact mul_right_cancel₀ hXne (hρX.trans hcX.symm)

end General

section Real

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### Algorithm 6.16: the Lanczos method for linear systems -/

/-- `y_m = T_m^{-1}(β e_1)` of (6.86). -/
noncomputable def lanczosMethodY (m : ℕ) : Fin m → ℝ :=
  (T A (unitResidual A b x₀) m)⁻¹ *ᵥ Krylov.firstVec ‖b - op A x₀‖ m

theorem lanczosMethodY_def (m : ℕ) : lanczosMethodY A b x₀ m =
    (T A (unitResidual A b x₀) m)⁻¹ *ᵥ Krylov.firstVec ‖b - op A x₀‖ m := rfl

/-- (6.86): `x_m = x_0 + V_m y_m`, `m` steps of Algorithm 6.16 carried out unconditionally. -/
noncomputable def lanczosMethodAt (m : ℕ) : 𝔼 :=
  x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • lanczosV A (unitResidual A b x₀) (j : ℕ)

/-- **Algorithm 6.16** (the Lanczos method for linear systems), with the book's
"if `β_{j+1} = 0` then set `m := j` and Stop". -/
noncomputable def lanczosMethod (m : ℕ) : 𝔼 :=
  lanczosMethodAt A b x₀ (min m (grade A (b - op A x₀)))

theorem lanczosMethodAt_def (m : ℕ) : lanczosMethodAt A b x₀ m =
    x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • lanczosV A (unitResidual A b x₀) (j : ℕ) :=
  rfl

/-- Below the grade the book's stopping rule does not fire, and Algorithm 6.16 is the
unconditional form. -/
theorem lanczosMethod_eq_lanczosMethodAt {m : ℕ} (hm : m ≤ grade A (b - op A x₀)) :
    lanczosMethod A b x₀ m = lanczosMethodAt A b x₀ m := by
  rw [lanczosMethod, min_eq_left hm]

variable {A b x₀}

/-- Running Algorithm 6.15 from `v_1 = r_0/‖r_0‖` computes the backbone Arnoldi vectors of
`r_0` itself, the indexing the backbone Krylov results use. -/
theorem lanczosV_unitResidual (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (j : ℕ) :
    lanczosV A (unitResidual A b x₀) j = Arnoldi.vec (op A) (b - op A x₀) j := by
  rw [lanczosV_eq A _ (isSymmetric_op_of_isSymm hA) (norm_unitResidual hb), unitResidual_def]
  exact arnoldiCGS_normalize A hb j

/-- `T_m` computed from `v_1 = r_0/‖r_0‖` is the backbone Arnoldi matrix `H_m` of `r_0`. -/
theorem T_unitResidual (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    T A (unitResidual A b x₀) m = Arnoldi.hessenbergSq (op A) (b - op A x₀) m := by
  rw [T_eq_H A _ hA (norm_unitResidual hb), unitResidual_def]
  exact H_normalize A hb m

theorem lanczosBeta_unitResidual (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (j : ℕ) :
    lanczosBeta A (unitResidual A b x₀) (j + 1)
      = Arnoldi.coeff (op A) (b - op A x₀) (j + 1) j := by
  have h := lanczosBeta_succ_eq_arnoldiCoeff A (unitResidual A b x₀)
    (isSymmetric_op_of_isSymm hA) (norm_unitResidual hb) j
  have h2 : arnoldiCoeff A (unitResidual A b x₀) (j + 1) j
      = Arnoldi.coeff (op A) (b - op A x₀) (j + 1) j := by
    rw [unitResidual_def]
    exact arnoldiCoeff_normalize A hb (j + 1) j
  rw [h2] at h
  simpa using h

theorem mulVec_lanczosMethodY {m : ℕ} (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    T A (unitResidual A b x₀) m *ᵥ lanczosMethodY A b x₀ m
      = Krylov.firstVec ‖b - op A x₀‖ m := by
  rw [lanczosMethodY_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]

private theorem lanczosMethodAt_eq_sum (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    lanczosMethodAt A b x₀ m =
      x₀ + ∑ j : Fin m, lanczosMethodY A b x₀ m j • Arnoldi.vec (op A) (b - op A x₀) (j : ℕ) := by
  rw [lanczosMethodAt_def]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [lanczosV_unitResidual hA hb])

private theorem mulVec_hessenbergSq (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ lanczosMethodY A b x₀ m
      = Krylov.firstVec ‖b - op A x₀‖ m := by
  rw [← T_unitResidual hA hb]
  exact mulVec_lanczosMethodY hT

/-- (6.86): the iterate of Algorithm 6.16 is the orthogonal projection (Galerkin) iterate onto
`𝒦_m`. -/
theorem lanczosMethodAt_isGalerkinIterate (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (lanczosMethodAt A b x₀ m) := by
  rw [lanczosMethodAt_eq_sum hA hb]
  exact (Krylov.isGalerkinIterate_iff_mulVec_eq (by rwa [← grade_eq]) _).2
    (mulVec_hessenbergSq hA hb hT)

/-- (6.87): `b - A x_m = -β_{m+1}(e_m^T y_m) v_{m+1}`. -/
theorem equation_6_87 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ} (hm : 0 < m)
    (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    b - op A (lanczosMethodAt A b x₀ m) =
      -(lanczosBeta A (unitResidual A b x₀) m * lanczosMethodY A b x₀ m ⟨m - 1, by omega⟩) •
        lanczosV A (unitResidual A b x₀) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [lanczosMethodAt_eq_sum hA hb, lanczosV_unitResidual hA hb, lanczosBeta_unitResidual hA hb]
  exact Krylov.residual_galerkin_eq hm (lanczosMethodY A b x₀ (k + 1))
    (mulVec_hessenbergSq hA hb hT)

/-- **Proposition 6.20** (1) for Algorithm 6.16: the residual is a multiple of `v_{m+1}`. -/
theorem proposition_6_20_1 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ} (hm : 0 < m)
    (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    ∃ σ : ℝ, b - op A (lanczosMethodAt A b x₀ m) = σ • lanczosV A (unitResidual A b x₀) m :=
  ⟨_, equation_6_87 hA hb hm hT⟩

/-- **Proposition 6.20** (1), second half: the residuals of Algorithm 6.16 are mutually
orthogonal, because each is a multiple of a Lanczos vector. -/
theorem inner_residual_lanczosMethodAt_eq_zero (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hij : i ≠ j)
    (hTi : IsUnit (T A (unitResidual A b x₀) i).det)
    (hTj : IsUnit (T A (unitResidual A b x₀) j).det) :
    inner ℝ (b - op A (lanczosMethodAt A b x₀ i)) (b - op A (lanczosMethodAt A b x₀ j)) = 0 := by
  rw [equation_6_87 hA hb hi hTi, equation_6_87 hA hb hj hTj, inner_smul_left, inner_smul_right,
    lanczosV_unitResidual hA hb, lanczosV_unitResidual hA hb,
    Arnoldi.inner_vec_eq_zero (op A) (b - op A x₀) hij]
  simp

/-! ### Algorithm 6.17: the direct version of the Lanczos method (D-Lanczos) -/

variable (A b x₀)

/-- (6.89): `η_1 = α_1` and `η_{m+1} = α_{m+1} - λ_{m+1} β_{m+1}`, the diagonal of `U_m` in the
`LU` factorization `T_m = L_m U_m` of (6.84). -/
noncomputable def dlEta (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → ℝ
  | 0 => lanczosAlpha A v₁ 0
  | m + 1 => lanczosAlpha A v₁ (m + 1) -
      lanczosBeta A v₁ (m + 1) / dlEta A v₁ m * lanczosBeta A v₁ (m + 1)

/-- (6.88): `λ_1 = 0` and `λ_{m+1} = β_{m+1}/η_m`, the subdiagonal of `L_m`. -/
noncomputable def dlLambda (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → ℝ
  | 0 => 0
  | m + 1 => lanczosBeta A v₁ (m + 1) / dlEta A v₁ m

/-- `ζ_1 = β` and `ζ_{m+1} = -λ_{m+1} ζ_m`, the entries of `z_m = L_m^{-1}(β e_1)`. -/
noncomputable def dlZeta (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) (β : ℝ) : ℕ → ℝ
  | 0 => β
  | m + 1 => -dlLambda A v₁ (m + 1) * dlZeta A v₁ β m

/-- `p_1 = η_1^{-1} v_1` and `p_{m+1} = η_{m+1}^{-1}(v_{m+1} - β_{m+1} p_m)`, the columns of
`P_m = V_m U_m^{-1}`. -/
noncomputable def dlP (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => (dlEta A v₁ 0)⁻¹ • lanczosV A v₁ 0
  | m + 1 => (dlEta A v₁ (m + 1))⁻¹ •
      (lanczosV A v₁ (m + 1) - lanczosBeta A v₁ (m + 1) • dlP A v₁ m)

/-- **Algorithm 6.17** (D-Lanczos): `x_m = x_{m-1} + ζ_m p_m`, started at `x_0`. -/
noncomputable def dLanczosX (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => dLanczosX A b x₀ m +
      dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ m • dlP A (unitResidual A b x₀) m

variable {A b x₀}

theorem dlEta_zero (v₁ : 𝔼) : dlEta A v₁ 0 = lanczosAlpha A v₁ 0 := rfl

theorem dlLambda_zero (v₁ : 𝔼) : dlLambda A v₁ 0 = 0 := rfl

/-- (6.88). -/
theorem dlLambda_succ (v₁ : 𝔼) (m : ℕ) :
    dlLambda A v₁ (m + 1) = lanczosBeta A v₁ (m + 1) / dlEta A v₁ m := rfl

/-- (6.89). -/
theorem dlEta_succ (v₁ : 𝔼) (m : ℕ) : dlEta A v₁ (m + 1) =
    lanczosAlpha A v₁ (m + 1) - dlLambda A v₁ (m + 1) * lanczosBeta A v₁ (m + 1) := rfl

theorem dlZeta_zero (v₁ : 𝔼) (β : ℝ) : dlZeta A v₁ β 0 = β := rfl

theorem dlZeta_succ (v₁ : 𝔼) (β : ℝ) (m : ℕ) :
    dlZeta A v₁ β (m + 1) = -dlLambda A v₁ (m + 1) * dlZeta A v₁ β m := rfl

theorem dlP_zero (v₁ : 𝔼) : dlP A v₁ 0 = (dlEta A v₁ 0)⁻¹ • lanczosV A v₁ 0 := rfl

theorem dlP_succ (v₁ : 𝔼) (m : ℕ) : dlP A v₁ (m + 1) = (dlEta A v₁ (m + 1))⁻¹ •
    (lanczosV A v₁ (m + 1) - lanczosBeta A v₁ (m + 1) • dlP A v₁ m) := rfl

@[simp] theorem dLanczosX_zero : dLanczosX A b x₀ 0 = x₀ := rfl

theorem dLanczosX_succ (m : ℕ) : dLanczosX A b x₀ (m + 1) = dLanczosX A b x₀ m +
    dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ m • dlP A (unitResidual A b x₀) m := rfl

/-- `A p_m = v_m + λ_{m+1} v_{m+1}`: the auxiliary vectors of Algorithm 6.17 are mapped into
the span of two consecutive Lanczos vectors. This is the whole content of the `LU`
factorization `T_m = L_m U_m`, in the form the induction needs. -/
theorem apply_dlP (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) :
    ∀ m : ℕ, (∀ i ≤ m, dlEta A v₁ i ≠ 0) →
      op A (dlP A v₁ m) = lanczosV A v₁ m + dlLambda A v₁ (m + 1) • lanczosV A v₁ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro hη
    have h0 : lanczosAlpha A v₁ 0 ≠ 0 := hη 0 le_rfl
    rw [dlP_zero, map_smul, apply_lanczosV_zero_real A v₁ hA hv, dlLambda_succ, dlEta_zero]
    match_scalars
    · field_simp
    · field_simp
  | succ m ih =>
    intro hη
    have hlam : dlLambda A v₁ (m + 2) = lanczosBeta A v₁ (m + 2) / dlEta A v₁ (m + 1) :=
      dlLambda_succ v₁ (m + 1)
    have hne : dlEta A v₁ (m + 1) ≠ 0 := hη (m + 1) le_rfl
    have heta := dlEta_succ (A := A) v₁ m
    rw [dlP_succ, map_smul, map_sub, map_smul, apply_lanczosV_real A v₁ hA hv,
      ih fun i hi => hη i (by omega), hlam]
    match_scalars
    · field_simp
      ring
    · field_simp
      linear_combination -heta
    · field_simp

/-- The residual of Algorithm 6.17 is `ζ_{m+1} v_{m+1}`: **Proposition 6.20** (1) for
D-Lanczos, and the reason the algorithm computes the Galerkin iterate. -/
theorem residual_dLanczosX (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) :
    ∀ m : ℕ, (∀ i < m, dlEta A (unitResidual A b x₀) i ≠ 0) →
      b - op A (dLanczosX A b x₀ m) =
        dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ m • lanczosV A (unitResidual A b x₀) m := by
  have hv := norm_unitResidual hb
  have hn : ‖b - op A x₀‖ ≠ 0 := norm_ne_zero_iff.2 hb
  intro m
  induction m with
  | zero =>
    intro _
    have hone : (‖b - op A x₀‖ : ℝ) • unitResidual A b x₀ = b - op A x₀ := by
      rw [unitResidual_def, smul_smul]
      simp [mul_inv_cancel₀ hn]
    rw [dLanczosX_zero, dlZeta_zero, lanczosV_zero]
    exact hone.symm
  | succ m ih =>
    intro hη
    have h := ih fun i hi => hη i (by omega)
    have hp := apply_dlP hA hv m fun i hi => hη i (by omega)
    have hstep : b - op A (dLanczosX A b x₀ (m + 1)) = (b - op A (dLanczosX A b x₀ m)) -
        dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ m •
          op A (dlP A (unitResidual A b x₀) m) := by
      rw [dLanczosX_succ, map_add, map_smul]
      abel
    rw [hstep, h, hp, dlZeta_succ]
    module

/-- The auxiliary vectors of Algorithm 6.17 lie in the Krylov subspaces. -/
theorem dlP_mem_krylov (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) (m : ℕ) :
    dlP A v₁ m ∈ krylov A v₁ (m + 1) := by
  have hA' := isSymmetric_op_of_isSymm hA
  induction m with
  | zero =>
    rw [dlP_zero]
    exact Submodule.smul_mem _ _ (lanczosV_mem_krylov A v₁ hA' hv 0)
  | succ m ih =>
    have hmono : krylov A v₁ (m + 1) ≤ krylov A v₁ (m + 2) := by
      rw [krylov_eq, krylov_eq]
      exact Krylov.subspace_mono (op A) v₁ (by omega)
    rw [dlP_succ]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (lanczosV_mem_krylov A v₁ hA' hv (m + 1)) (Submodule.smul_mem _ _ (hmono ih)))

theorem dLanczosX_sub_mem (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ) :
    dLanczosX A b x₀ m - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) m := by
  have hv := norm_unitResidual hb
  induction m with
  | zero => simp
  | succ m ih =>
    have hmem : dlP A (unitResidual A b x₀) m ∈ Krylov.subspace (op A) (b - op A x₀) (m + 1) := by
      rw [← krylov_unitResidual hb]
      exact dlP_mem_krylov hA hv m
    have hmono := Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m)
    rw [dLanczosX_succ, show dLanczosX A b x₀ m + _ - x₀ = (dLanczosX A b x₀ m - x₀) +
      dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ m • dlP A (unitResidual A b x₀) m from by abel]
    exact Submodule.add_mem _ (hmono ih) (Submodule.smul_mem _ _ hmem)

/-- **(6.86)–(6.89)**: Algorithm 6.17 computes the orthogonal projection (Galerkin) iterate
onto `𝒦_m`, hence the same iterate as Algorithm 6.16. -/
theorem dLanczosX_isGalerkinIterate (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) (m : ℕ)
    (hη : ∀ i < m, dlEta A (unitResidual A b x₀) i ≠ 0) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (dLanczosX A b x₀ m) := by
  have hv := norm_unitResidual hb
  refine ⟨dLanczosX_sub_mem hA hb m, ?_⟩
  rw [residual_dLanczosX hA hb m hη]
  refine Submodule.smul_mem _ _ ?_
  rw [← krylov_unitResidual hb]
  exact lanczosV_mem_orthogonal A _ (isSymmetric_op_of_isSymm hA) hv m

/-! ### §6.7.1: the three algorithms compute the same iterates -/

/-- A real positive definite matrix is symmetric. -/
theorem isSymm_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : A.IsSymm :=
  Matrix.isHermitian_iff_isSymm.1 hA.1

/-- The Galerkin iterate is unique for positive definite `A`. -/
theorem galerkin_unique (hA : A.PosDef) {m : ℕ} {x y : 𝔼}
    (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x)
    (hy : Krylov.IsGalerkinIterate (op A) b x₀ m y) : x = y := by
  obtain ⟨z, _, hz⟩ := Krylov.existsUnique_isGalerkinIterate_of_isCoercive
    (isSymmetricCoercive_op_of_posDef hA).isCoercive b x₀ m
  rw [hz x hx, hz y hy]

/-- Algorithm 6.18 realises the orthogonal projection (Galerkin) specification. -/
theorem cgX_isGalerkinIterate (hA : A.PosDef) (m : ℕ) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (cgX A b x₀ m) := by
  rw [cgX_eq_CG A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric]
  exact CG.isGalerkinIterate b x₀ (isSymmetricCoercive_op_of_posDef hA) m

/-- §6.7.1: **CG is mathematically equivalent to D-Lanczos** — both compute the Galerkin
iterate onto `𝒦_m`. -/
theorem cgX_eq_dLanczosX (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) (m : ℕ)
    (hη : ∀ i < m, dlEta A (unitResidual A b x₀) i ≠ 0) :
    cgX A b x₀ m = dLanczosX A b x₀ m :=
  galerkin_unique hA (cgX_isGalerkinIterate hA m)
    (dLanczosX_isGalerkinIterate (isSymm_of_posDef hA) hb m hη)

/-- §6.7.1: Algorithm 6.17 delivers the iterate of Algorithm 6.16. -/
theorem dLanczosX_eq_lanczosMethodAt (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hη : ∀ i < m, dlEta A (unitResidual A b x₀) i ≠ 0)
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    dLanczosX A b x₀ m = lanczosMethodAt A b x₀ m :=
  galerkin_unique hA (dLanczosX_isGalerkinIterate (isSymm_of_posDef hA) hb m hη)
    (lanczosMethodAt_isGalerkinIterate (isSymm_of_posDef hA) hb hm hT)

/-- §6.7: **Algorithm 6.16 is the Full Orthogonalization Method for symmetric `A`.** Both
`lanczosMethod` and `fom` are *the* Galerkin iterate on `𝒦_m(A, r_0)`, so they agree; the book's
"if `β_{j+1} = 0` set `m := j`" and FOM's `mEff` stop at the same step, since `v_1` and `r_0`
have the same grade. -/
theorem lanczosMethod_eq_fom (hA : A.IsSymm) {m : ℕ}
    (hH : FOMDefined A b x₀ (mEff A b x₀ m)) :
    lanczosMethod A b x₀ m = fom A b x₀ m := by
  have hmE : mEff A b x₀ m = min m (grade A (b - op A x₀)) := by
    rw [mEff, grade_v₁, grade_eq]
  rcases eq_or_ne (b - op A x₀) 0 with hb | hb
  · have h0 : grade A (b - op A x₀) = 0 := by rw [hb, grade_eq, Krylov.grade_zero]
    rw [lanczosMethod, h0, min_zero, fom, hmE, h0, min_zero, fomFixed_zero, lanczosMethodAt_def]
    simp
  · have hT : IsUnit (T A (unitResidual A b x₀) (mEff A b x₀ m)).det := by
      rw [T_unitResidual hA hb, ← H_v₁ A b x₀]
      exact (Matrix.isUnit_iff_isUnit_det _).1 hH
    rw [lanczosMethod, ← hmE, fom]
    exact eq_fomFixed_of_isGalerkinIterate A b x₀ hH (mEff_le A b x₀ m)
      (lanczosMethodAt_isGalerkinIterate hA hb (hmE ▸ min_le_right m _) hT)

/-- §6.7.1: Algorithm 6.18 delivers the iterate of Algorithm 6.16. -/
theorem cgX_eq_lanczosMethodAt (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀)) (hT : IsUnit (T A (unitResidual A b x₀) m).det) :
    cgX A b x₀ m = lanczosMethodAt A b x₀ m :=
  galerkin_unique hA (cgX_isGalerkinIterate hA m)
    (lanczosMethodAt_isGalerkinIterate (isSymm_of_posDef hA) hb hm hT)

/-- `(v_k, p_j) = 0` for `k > j`: the auxiliary vectors of Algorithm 6.17 lie in `𝒦_{j+1}`. -/
theorem inner_lanczosV_dlP_eq_zero (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) :
    ∀ (j : ℕ) {k : ℕ}, j < k → inner ℝ (lanczosV A v₁ k) (dlP A v₁ j) = 0 := by
  have hA' := isSymmetric_op_of_isSymm hA
  intro j
  induction j with
  | zero =>
    intro k hk
    rw [dlP_zero, real_inner_smul_right, inner_lanczosV_eq_zero A v₁ hA' hv (by omega), mul_zero]
  | succ j ih =>
    intro k hk
    rw [dlP_succ, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      inner_lanczosV_eq_zero A v₁ hA' hv (show k ≠ j + 1 by omega), ih (by omega), mul_zero,
      sub_zero, mul_zero]

/-- **Proposition 6.20** (2): the auxiliary vectors `p_i` of Algorithm 6.17 are `A`-conjugate,
`(A p_i, p_j) = 0` for `i ≠ j`. -/
theorem proposition_6_20_2 (hA : A.IsSymm) {v₁ : 𝔼} (hv : ‖v₁‖ = 1) {i j : ℕ} (hij : i ≠ j)
    (hη : ∀ k ≤ max i j, dlEta A v₁ k ≠ 0) :
    inner ℝ (op A (dlP A v₁ i)) (dlP A v₁ j) = 0 := by
  have key : ∀ a c : ℕ, c < a → (∀ k ≤ a, dlEta A v₁ k ≠ 0) →
      inner ℝ (op A (dlP A v₁ a)) (dlP A v₁ c) = 0 := by
    intro a c hca hη'
    rw [apply_dlP hA hv a hη', inner_add_left, real_inner_smul_left,
      inner_lanczosV_dlP_eq_zero hA hv c (by omega),
      inner_lanczosV_dlP_eq_zero hA hv c (by omega), mul_zero, add_zero]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [isSymmetric_op_of_isSymm hA (dlP A v₁ i) (dlP A v₁ j), real_inner_comm]
    exact key j i h fun k hk => hη k (hk.trans (le_max_right i j))
  · exact key i j h fun k hk => hη k (hk.trans (le_max_left i j))

/-! ### §6.7.3: eigenvalue estimates, (6.99)–(6.103) -/

/-- The residuals of Algorithm 6.18 vanish from some step on, so a nonzero residual at step `k`
means nonzero residuals at every earlier step. -/
theorem cgR_ne_zero_of_le (hA : A.PosDef) {k j : ℕ} (hr : cgR A b x₀ k ≠ 0) (hj : j ≤ k) :
    cgR A b x₀ j ≠ 0 := by
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  intro h0
  refine hr ?_
  rw [cgR_eq_CG A b x₀ hs] at h0 ⊢
  rw [CG.iterate_eq_of_residual_eq_zero' (op A) b x₀ h0 k hj]
  exact h0

/-- (6.99): the Lanczos vector `v_{j+1}` is `(-1)^j r_j/‖r_j‖`. -/
theorem lanczosV_eq_smul_cgR (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    lanczosV A (unitResidual A b x₀) k =
      ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹) • cgR A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := by simpa using cgR_ne_zero_of_le hA hr (Nat.zero_le k)
  have hs := (isSymmetricCoercive_op_of_posDef hA).isSymmetric
  have h := CG.arnoldi_vec_eq b x₀ (isSymmetricCoercive_op_of_posDef hA) k
    (by rwa [cgR_eq_CG A b x₀ hs] at hr)
  rw [lanczosV_unitResidual (isSymm_of_posDef hA) hb, cgR_eq_CG A b x₀ hs]
  simpa using h

/-- (6.99): the CG residual `r_j` is a nonzero multiple of the Lanczos vector `v_{j+1}`. -/
theorem equation_6_99 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ k ≠ 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ cgR A b x₀ k = σ • lanczosV A (unitResidual A b x₀) k := by
  have hn : ‖cgR A b x₀ k‖ ≠ 0 := norm_ne_zero_iff.2 hr
  have hpow : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨k, rfl⟩
  refine ⟨(-1 : ℝ) ^ k * ‖cgR A b x₀ k‖,
    mul_ne_zero (pow_ne_zero k (by norm_num)) hn, ?_⟩
  have hone : ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖) * ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹) = 1 :=
    calc ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖) * ((-1 : ℝ) ^ k * ‖cgR A b x₀ k‖⁻¹)
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (‖cgR A b x₀ k‖ * ‖cgR A b x₀ k‖⁻¹) := by ring
      _ = 1 := by rw [hpow, mul_inv_cancel₀ hn, mul_one]
  rw [lanczosV_eq_smul_cgR hA hr, smul_smul, hone, one_smul]

/-- (6.100): `r_j = p_j - β_{j-1} p_{j-1}`. -/
theorem equation_6_100 (j : ℕ) :
    cgR A b x₀ (j + 1) = cgP A b x₀ (j + 1) - cgBeta A b x₀ j • cgP A b x₀ j := by
  rw [cgP_succ]
  abel

/-- §6.7.1: `β_j = -(r_{j+1}, A p_j)/(p_j, A p_j)`, the form the book's derivation produces. -/
theorem cgBeta_eq' (hA : A.PosDef) (j : ℕ) : cgBeta A b x₀ j =
    -(inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1)) /
      inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j)) := by
  by_cases hr : cgR A b x₀ j = 0
  · rw [cgBeta_eq, hr, cgP_eq_zero_of_cgR_eq_zero hA hr]
    simp
  · have hX : inner ℝ (cgP A b x₀ j) (op A (cgP A b x₀ j)) ≠ 0 :=
      inner_cgP_apply_cgP_ne_zero hA hr
    have hX' : inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j) ≠ 0 := by
      rw [real_inner_comm]
      exact hX
    have hR : (inner ℝ (cgR A b x₀ j) (cgR A b x₀ j) : ℝ) ≠ 0 := fun h =>
      hr (inner_self_eq_zero.1 h)
    have h1 : cgAlpha A b x₀ j * inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j)
        = inner ℝ (cgR A b x₀ j) (cgR A b x₀ j) := by
      rw [cgAlpha_eq, real_inner_comm (op A (cgP A b x₀ j)), div_mul_cancel₀ _ hX']
    have h2 : cgAlpha A b x₀ j * inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1))
        = -inner ℝ (cgR A b x₀ (j + 1)) (cgR A b x₀ (j + 1)) := by
      rw [← real_inner_smul_left, cgAlpha_smul_apply_cgP, inner_sub_left,
        inner_cgR_eq_zero hA (show j ≠ j + 1 by omega), zero_sub]
    rw [cgBeta_eq]
    field_simp
    linear_combination inner ℝ (op A (cgP A b x₀ j)) (cgP A b x₀ j) * h2 -
      inner ℝ (op A (cgP A b x₀ j)) (cgR A b x₀ (j + 1)) * h1

private theorem apply_cgP_eq' (hA : A.PosDef) {j : ℕ} (hr : cgR A b x₀ j ≠ 0) :
    op A (cgP A b x₀ j) = (cgAlpha A b x₀ j)⁻¹ • (cgR A b x₀ j - cgR A b x₀ (j + 1)) := by
  rw [← cgAlpha_smul_apply_cgP, smul_smul, inv_mul_cancel₀ (cgAlpha_ne_zero hA hr), one_smul]

private theorem apply_cgR_zero' (hA : A.PosDef) (hr : cgR A b x₀ 0 ≠ 0) :
    op A (cgR A b x₀ 0) = (cgAlpha A b x₀ 0)⁻¹ • (cgR A b x₀ 0 - cgR A b x₀ 1) := by
  have h := apply_cgP_eq' hA hr
  rwa [cgP_zero] at h

private theorem apply_cgR_succ' (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    op A (cgR A b x₀ (k + 1)) =
      (cgAlpha A b x₀ (k + 1))⁻¹ • (cgR A b x₀ (k + 1) - cgR A b x₀ (k + 1 + 1)) -
        (cgBeta A b x₀ k * (cgAlpha A b x₀ k)⁻¹) • (cgR A b x₀ k - cgR A b x₀ (k + 1)) := by
  have hrk : cgR A b x₀ k ≠ 0 := cgR_ne_zero_of_le hA hr (by omega)
  have h100 := equation_6_100 (A := A) (b := b) (x₀ := x₀) k
  conv_lhs => rw [h100]
  rw [map_sub, map_smul, apply_cgP_eq' hA hr, apply_cgP_eq' hA hrk, smul_smul]

private theorem inner_cgR_apply_cgR_zero (hA : A.PosDef) (hr : cgR A b x₀ 0 ≠ 0) :
    inner ℝ (cgR A b x₀ 0) (op A (cgR A b x₀ 0))
      = (cgAlpha A b x₀ 0)⁻¹ * ‖cgR A b x₀ 0‖ ^ 2 := by
  rw [apply_cgR_zero' hA hr, real_inner_smul_right, inner_sub_right,
    inner_cgR_eq_zero hA (show (0 : ℕ) ≠ 1 by omega), sub_zero, real_inner_self_eq_norm_sq]

private theorem inner_cgR_apply_cgR_succ (hA : A.PosDef) {k : ℕ}
    (hr : cgR A b x₀ (k + 1) ≠ 0) :
    inner ℝ (cgR A b x₀ (k + 1)) (op A (cgR A b x₀ (k + 1)))
      = ((cgAlpha A b x₀ (k + 1))⁻¹ + cgBeta A b x₀ k * (cgAlpha A b x₀ k)⁻¹)
        * ‖cgR A b x₀ (k + 1)‖ ^ 2 := by
  rw [apply_cgR_succ' hA hr, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    inner_sub_right, inner_sub_right,
    inner_cgR_eq_zero hA (show k + 1 ≠ k + 1 + 1 by omega),
    inner_cgR_eq_zero hA (show k + 1 ≠ k by omega), real_inner_self_eq_norm_sq]
  ring

private theorem inner_cgR_succ_apply_cgR (hA : A.PosDef) {k : ℕ}
    (hr : cgR A b x₀ (k + 1) ≠ 0) :
    inner ℝ (cgR A b x₀ (k + 1)) (op A (cgR A b x₀ k))
      = -((cgAlpha A b x₀ k)⁻¹ * ‖cgR A b x₀ (k + 1)‖ ^ 2) := by
  have hrk : cgR A b x₀ k ≠ 0 := cgR_ne_zero_of_le hA hr (by omega)
  cases k with
  | zero =>
    rw [apply_cgR_zero' hA hrk, real_inner_smul_right, inner_sub_right,
      inner_cgR_eq_zero hA (show (1 : ℕ) ≠ 0 by omega), zero_sub, real_inner_self_eq_norm_sq]
    ring
  | succ k =>
    rw [apply_cgR_succ' hA hrk, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      inner_sub_right, inner_sub_right,
      inner_cgR_eq_zero hA (show k + 1 + 1 ≠ k + 1 by omega),
      inner_cgR_eq_zero hA (show k + 1 + 1 ≠ k by omega), real_inner_self_eq_norm_sq]
    ring

private theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

private theorem sign_norm_sq (k : ℕ) (t : ℝ) :
    ((-1 : ℝ) ^ k * t⁻¹) * ((-1 : ℝ) ^ k * t⁻¹) = (t ^ 2)⁻¹ := by
  calc ((-1 : ℝ) ^ k * t⁻¹) * ((-1 : ℝ) ^ k * t⁻¹)
      = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (t⁻¹ * t⁻¹) := by ring
    _ = (t ^ 2)⁻¹ := by
        rw [neg_one_pow_mul_self, one_mul, ← mul_inv, ← sq]

private theorem sign_norm_mul (k : ℕ) (s t : ℝ) :
    ((-1 : ℝ) ^ (k + 1) * s⁻¹) * ((-1 : ℝ) ^ k * t⁻¹) = -(s * t)⁻¹ := by
  have h : ((-1 : ℝ) ^ (k + 1)) * ((-1 : ℝ) ^ k) = -1 := by
    rw [pow_succ]
    calc ((-1 : ℝ) ^ k * (-1)) * (-1 : ℝ) ^ k
        = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (-1) := by ring
      _ = -1 := by rw [neg_one_pow_mul_self]; ring
  calc ((-1 : ℝ) ^ (k + 1) * s⁻¹) * ((-1 : ℝ) ^ k * t⁻¹)
      = ((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k) * (s⁻¹ * t⁻¹) := by ring
    _ = -(s * t)⁻¹ := by rw [h, ← mul_inv]; ring

/-- (6.102): `δ_1 = 1/α_0`. -/
theorem equation_6_102 (hA : A.PosDef) (hr : cgR A b x₀ 0 ≠ 0) :
    lanczosAlpha A (unitResidual A b x₀) 0 = 1 / cgAlpha A b x₀ 0 := by
  have hb : b - op A x₀ ≠ 0 := hr
  have hn : ‖cgR A b x₀ 0‖ ≠ 0 := norm_ne_zero_iff.2 hr
  rw [lanczosAlpha_eq_inner_real A _ (isSymm_of_posDef hA) (norm_unitResidual hb),
    lanczosV_eq_smul_cgR hA hr, map_smul, real_inner_smul_left, real_inner_smul_right,
    inner_cgR_apply_cgR_zero hA hr]
  field_simp

/-- (6.101): `δ_{j+1} = 1/α_j + β_{j-1}/α_{j-1}`. -/
theorem equation_6_101 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    lanczosAlpha A (unitResidual A b x₀) (k + 1) =
      1 / cgAlpha A b x₀ (k + 1) + cgBeta A b x₀ k / cgAlpha A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := cgR_ne_zero_of_le hA hr (Nat.zero_le _)
  have hn : ‖cgR A b x₀ (k + 1)‖ ≠ 0 := norm_ne_zero_iff.2 hr
  rw [lanczosAlpha_eq_inner_real A _ (isSymm_of_posDef hA) (norm_unitResidual hb),
    lanczosV_eq_smul_cgR hA hr, map_smul, real_inner_smul_left, real_inner_smul_right,
    inner_cgR_apply_cgR_succ hA hr, ← mul_assoc, sign_norm_sq]
  field_simp

/-- (6.103): `η_{j+1} = √(β_{j-1})/α_{j-1}`. -/
theorem equation_6_103 (hA : A.PosDef) {k : ℕ} (hr : cgR A b x₀ (k + 1) ≠ 0) :
    lanczosBeta A (unitResidual A b x₀) (k + 1) =
      Real.sqrt (cgBeta A b x₀ k) / cgAlpha A b x₀ k := by
  have hb : b - op A x₀ ≠ 0 := cgR_ne_zero_of_le hA hr (Nat.zero_le _)
  have hrk : cgR A b x₀ k ≠ 0 := cgR_ne_zero_of_le hA hr (by omega)
  have hn : ‖cgR A b x₀ (k + 1)‖ ≠ 0 := norm_ne_zero_iff.2 hr
  have hnk : ‖cgR A b x₀ k‖ ≠ 0 := norm_ne_zero_iff.2 hrk
  have hbeta : cgBeta A b x₀ k = ‖cgR A b x₀ (k + 1)‖ ^ 2 / ‖cgR A b x₀ k‖ ^ 2 := by
    rw [cgBeta_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hsqrt : Real.sqrt (cgBeta A b x₀ k) = ‖cgR A b x₀ (k + 1)‖ / ‖cgR A b x₀ k‖ := by
    rw [hbeta, ← div_pow, Real.sqrt_sq (by positivity)]
  have hα : cgAlpha A b x₀ k ≠ 0 := cgAlpha_ne_zero hA hrk
  rw [lanczosBeta_succ_eq_inner_real A _ (isSymm_of_posDef hA) (norm_unitResidual hb),
    lanczosV_eq_smul_cgR hA hr, lanczosV_eq_smul_cgR hA hrk, map_smul, real_inner_smul_left,
    real_inner_smul_right, inner_cgR_succ_apply_cgR hA hr, ← mul_assoc, sign_norm_mul,
    hsqrt]
  field_simp

/-- §6.7.1, last sentence: the search directions of Algorithm 6.18 are nonzero multiples of
the auxiliary vectors of Algorithm 6.17. -/
theorem cgP_smul_dlP (hA : A.PosDef) (hb : b - op A x₀ ≠ 0) {j : ℕ} (hr : cgR A b x₀ j ≠ 0)
    (hη : ∀ i < j + 1, dlEta A (unitResidual A b x₀) i ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ cgP A b x₀ j = c • dlP A (unitResidual A b x₀) j := by
  have hα := cgAlpha_ne_zero hA hr
  have hxj := cgX_eq_dLanczosX hA hb j fun i hi => hη i (by omega)
  have hxj1 := cgX_eq_dLanczosX hA hb (j + 1) hη
  have hres := residual_dLanczosX (isSymm_of_posDef hA) hb j fun i hi => hη i (by omega)
  have hζ : dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ j ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hres
    exact hr (by rw [cgR_eq_residual A b x₀ (isSymmetricCoercive_op_of_posDef hA).isSymmetric,
      hxj, hres])
  have hstep : cgAlpha A b x₀ j • cgP A b x₀ j =
      dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ j • dlP A (unitResidual A b x₀) j := by
    have h1 : cgX A b x₀ (j + 1) = cgX A b x₀ j + cgAlpha A b x₀ j • cgP A b x₀ j
        := cgX_succ A b x₀ j
    have h2 := dLanczosX_succ (A := A) (b := b) (x₀ := x₀) j
    rw [hxj1, hxj] at h1
    rw [h2] at h1
    exact (add_right_injective (dLanczosX A b x₀ j) h1.symm)
  refine ⟨dlZeta A (unitResidual A b x₀) ‖b - op A x₀‖ j / cgAlpha A b x₀ j,
    div_ne_zero hζ hα, ?_⟩
  rw [div_eq_inv_mul, ← smul_smul, ← hstep, smul_smul, inv_mul_cancel₀ hα, one_smul]

end Real

/-! ### §6.7.1: D-Lanczos is DIOM(2)

The book's remark that Algorithm 6.17 "is DIOM(2)" — and hence that the conjugate gradient
algorithm is a variation of DIOM(2) — rests on the fact that for a symmetric matrix the
incomplete orthogonalization procedure of Algorithm 6.6 with `k = 2` recomputes Algorithm 6.1:
the only coefficients it drops are the `h_{ij}` with `i + 1 < j`, and those vanish by symmetry.
-/

section IncompleteTwo

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-- Before the band starts, the truncated inner loop of Algorithm 6.6 does nothing. -/
private theorem iopW_of_le (u : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) :
    ∀ {N : ℕ}, N ≤ lo → iopW u lo w₀ N = w₀ := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    rw [iopW_succ, ih (by omega), iopCoeffOf]
    split_ifs with h1
    · omega
    · rw [zero_smul, sub_zero]

variable (M : Matrix (Fin n) (Fin n) 𝕜) (w₁ : EuclideanSpace 𝕜 (Fin n))

/-- The Arnoldi coefficients of a symmetric matrix are tridiagonal: `h_{ij} = 0` for
`i + 1 < j`. -/
theorem arnoldiCoeff_eq_zero_of_isSymmetric (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1)
    {i j : ℕ} (h : i + 1 < j) : arnoldiCoeff M w₁ i j = 0 := by
  rw [arnoldiCoeff_eq M w₁ hw]
  exact Arnoldi.coeff_eq_zero_of_isSymmetric hM w₁ h

/-- The inner loop of Algorithm 6.6 with `k = 2`, run on the Arnoldi vectors of a symmetric
matrix, produces the Arnoldi coefficients: the terms it skips are already `0`, and the terms it
keeps are unchanged by the modified Gram–Schmidt order because the vectors are orthogonal. -/
private theorem iopCoeffOf_two (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) {i : ℕ}
    (hi : i < j + 1) :
    iopCoeffOf (arnoldiCGS M w₁) (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) i
      = arnoldiCoeff M w₁ i j := by
  match j with
  | 0 =>
    obtain rfl : i = 0 := by omega
    rw [iopCoeffOf]
    split_ifs with h1
    · rw [iopW_of_le _ _ _ (Nat.zero_le _)]
      rfl
    · omega
  | (k + 1) =>
    have hlo : k + 1 + 1 - 2 = k := by omega
    rw [hlo, iopCoeffOf]
    split_ifs with h1
    · rcases eq_or_lt_of_le h1 with h2 | h2
      · obtain rfl : i = k := h2.symm
        rw [iopW_of_le _ _ _ le_rfl]
        rfl
      · obtain rfl : i = k + 1 := by omega
        rw [iopW_succ, iopCoeffOf]
        split_ifs with h3
        · rw [iopW_of_le _ _ _ le_rfl, inner_sub_right, inner_smul_right,
            inner_arnoldiCGS_eq_zero M w₁ hw (by omega : k + 1 ≠ k), mul_zero, sub_zero]
          rfl
        · omega
    · exact (arnoldiCoeff_eq_zero_of_isSymmetric M w₁ hM hw (by omega)).symm

/-- **Algorithm 6.6 with `k = 2` is Algorithm 6.1** for a symmetric matrix. -/
theorem iop_two_eq_arnoldiCGS (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) :
    iop M w₁ 2 j = arnoldiCGS M w₁ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 => rw [iop_zero, arnoldiCGS_zero]
    | (j + 1) =>
      have hfam : ∀ i < j + 1, iop M w₁ 2 i = arnoldiCGS M w₁ i := fun i hi => ih i (by omega)
      have hsum : ∑ i ∈ Finset.range (j + 1),
          iopCoeffOf (arnoldiCGS M w₁) (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) i •
            arnoldiCGS M w₁ i
          = ∑ i ∈ Finset.range (j + 1), arnoldiCoeff M w₁ i j • arnoldiCGS M w₁ i :=
        Finset.sum_congr rfl fun i hi => by
          rw [iopCoeffOf_two M w₁ hM hw j (Finset.mem_range.1 hi)]
      have hW : iopVecW M w₁ 2 j = arnoldiW M w₁ j := by
        rw [iopVecW, hfam j (by omega),
          iopW_congr (j + 1 - 2) (op M (arnoldiCGS M w₁ j)) hfam, iopW_eq_sub_sum, arnoldiW,
          hsum]
      rw [iop_succ, hW, arnoldiCGS_succ]

theorem iop_two_eq (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) :
    iop M w₁ 2 = arnoldiCGS M w₁ :=
  funext (iop_two_eq_arnoldiCGS M w₁ hM hw)

theorem iopVecW_two_eq_arnoldiW (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (j : ℕ) :
    iopVecW M w₁ 2 j = arnoldiW M w₁ j := by
  rw [iopVecW, iop_two_eq M w₁ hM hw, iopW_eq_sub_sum, arnoldiW]
  exact congrArg _ (Finset.sum_congr rfl fun i hi => by
    rw [iopCoeffOf_two M w₁ hM hw j (Finset.mem_range.1 hi)])

/-- The truncated coefficients of Algorithm 6.6 with `k = 2` are the Arnoldi coefficients. -/
theorem iopCoeff_two_eq_arnoldiCoeff (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (i j : ℕ) :
    iopCoeff M w₁ 2 i j = arnoldiCoeff M w₁ i j := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · rw [iop_two_eq M w₁ hM hw]
    exact iopCoeffOf_two M w₁ hM hw j (by omega)
  · rw [h2, iopVecW_two_eq_arnoldiW M w₁ hM hw, arnoldiCoeff_succ_self M w₁ hw]
  · exact (arnoldiCoeff_eq_zero_of_lt M w₁ hw (by omega)).symm

/-- `V_m` of Algorithm 6.6 with `k = 2` is the Arnoldi `V_m`. -/
theorem VI_two_eq_V (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (m : ℕ) :
    VI M w₁ 2 m = V M w₁ m := by
  rw [VI, V, iop_two_eq M w₁ hM hw]

/-- `H_m` of Algorithm 6.6 with `k = 2` is the Arnoldi `H_m`. -/
theorem HI_two_eq_H (hM : (op M).IsSymmetric) (hw : ‖w₁‖ = 1) (m : ℕ) :
    HI M w₁ 2 m = H M w₁ m := by
  ext i j
  rw [HI_apply, H_apply, iopCoeff_two_eq_arnoldiCoeff M w₁ hM hw]

variable (c x₀ : EuclideanSpace 𝕜 (Fin n))

/-- **IOM(2) is FOM** for a symmetric matrix. -/
theorem iomFixed_two_eq_fomFixed (hM : (op M).IsSymmetric) (hr : r₀ M c x₀ ≠ 0) (m : ℕ) :
    iomFixed M c x₀ 2 m = fomFixed M c x₀ m := by
  have hw : ‖v₁ M c x₀‖ = 1 := norm_v₁ M c x₀ hr
  rw [iomFixed, fomFixed, VI_two_eq_V M _ hM hw, iomY, fomY, HI_two_eq_H M _ hM hw]

/-- **DIOM(2) is FOM** for a symmetric matrix, wherever Algorithm 6.8 does not divide by `0`. -/
theorem diom_two_eq_fomFixed (hM : (op M).IsSymmetric) (hr : r₀ M c x₀ ≠ 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff M (v₁ M c x₀) 2) l l ≠ 0) :
    diom M c x₀ 2 m = fomFixed M c x₀ m :=
  (diom_eq_iomFixed M c x₀ 2 hpiv).trans (iomFixed_two_eq_fomFixed M c x₀ hM hr m)

end IncompleteTwo

section RealTwo

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}

/-- §6.7.1: **Algorithm 6.17 (D-Lanczos) is DIOM(2)**, the book's remark that the conjugate
gradient algorithm is a variation of DIOM(2). Both are the Galerkin iterate on `𝒦_m(A, r_0)`:
D-Lanczos by `dLanczosX_isGalerkinIterate`, DIOM(2) because for symmetric `A` the truncated
orthogonalization of Algorithm 6.6 with `k = 2` is the Arnoldi process, so DIOM(2) is FOM. -/
theorem dLanczos_eq_diom2 (hA : A.IsSymm) (hb : b - op A x₀ ≠ 0) {m : ℕ}
    (hm : m ≤ grade A (b - op A x₀))
    (hη : ∀ i < m, dlEta A (unitResidual A b x₀) i ≠ 0)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) 2) l l ≠ 0) :
    dLanczosX A b x₀ m = diom A b x₀ 2 m := by
  have hsym := isSymmetric_op_of_isSymm hA
  have hw : ‖v₁ A b x₀‖ = 1 := norm_v₁ A b x₀ hb
  have hH : FOMDefined A b x₀ m := by
    rw [FOMDefined, ← HI_two_eq_H A (v₁ A b x₀) hsym hw]
    exact isUnit_HI_of_pivots A (v₁ A b x₀) 2 hpiv
  rw [diom_two_eq_fomFixed A b x₀ hsym hb hpiv]
  exact eq_fomFixed_of_isGalerkinIterate A b x₀ hH (by rwa [grade_v₁, ← grade_eq])
    (dLanczosX_isGalerkinIterate hA hb m hη)

end RealTwo

end SaadSparse.Ch06
