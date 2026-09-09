import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section02

/-!
# Saad Chapter 6: the data of a linear system

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, Chapter 6.

Every Krylov method of the chapter starts from the same three quantities: the initial residual
`r₀ = b - A x₀`, its norm `β = ‖r₀‖₂` and the unit vector `v₁ = r₀/β` on which Algorithm 6.1 is
run. They are named here, once, together with what §6.2 already says about them: `v₁` is a unit
vector, and it has the grade and the Krylov subspaces of `r₀`.

`e₁` is the first coordinate vector, and `mEff` implements the book's "if `h_{j+1,j} = 0` then
set `m := j`" as `min m (grade A v₁)`.

The backbone indexes the Arnoldi process by the residual `r₀` itself, so each algorithm needs a
translation between the book's `v₁`-indexed data and the backbone's `r₀`-indexed data. That
translation is the `*_v₁` family, and it names the Arnoldi process, so it lives in
`Chapter06/Section03.lean` — §6.3 is where Algorithm 6.1 is — rather than here.  This file
therefore comes between §6.2, whose `grade` and `krylov` it uses, and §6.3, which needs `v₁` to
state that family.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The initial residual and the starting vector -/

/-- The initial residual `r_0 = b - A x_0` (Algorithm 6.4 and Algorithm 6.9, line 1). -/
noncomputable abbrev r₀ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 := b - op A x₀

/-- `β = ‖r_0‖₂` (Algorithm 6.4 and Algorithm 6.9, line 1). -/
noncomputable abbrev β (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℝ := ‖r₀ A b x₀‖

/-- The starting vector `v_1 = r_0/β` of the Arnoldi process (Algorithm 6.4 and Algorithm 6.9,
line 1); `0` when `r_0 = 0`, by Lean's `x / 0 = 0`. -/
noncomputable def v₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 :=
  (β A b x₀ : 𝕜)⁻¹ • r₀ A b x₀

/-- The first coordinate vector `e_1 ∈ 𝕜^m`. -/
def e₁ (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then 1 else 0

/-- The number of Arnoldi steps the algorithm actually performs: the book's "if `h_{j+1,j} = 0`
then set `m := j`" stops the Arnoldi process at the grade of `v_1`. -/
noncomputable def mEff (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℕ :=
  min m (grade A (v₁ A b x₀))

/-- `β e_1` is the backbone's `Krylov.firstVec β`. -/
theorem smul_e₁_eq_firstVec (c : 𝕜) (m : ℕ) : c • e₁ m = Krylov.firstVec c m := by
  funext i
  by_cases h : (i : ℕ) = 0 <;> simp [e₁, Krylov.firstVec, h]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

theorem r₀_def : r₀ A b x₀ = b - op A x₀ := rfl

theorem β_def : (β A b x₀ : 𝕜) = (‖b - op A x₀‖ : 𝕜) := rfl

theorem β_eq_norm_r₀ : (β A b x₀ : 𝕜) = (‖r₀ A b x₀‖ : 𝕜) := rfl

theorem v₁_def : v₁ A b x₀ = (‖b - op A x₀‖ : 𝕜)⁻¹ • (b - op A x₀) := rfl

/-- The number of Arnoldi steps actually performed never exceeds the grade of `v_1`. -/
theorem mEff_le (m : ℕ) : mEff A b x₀ m ≤ grade A (v₁ A b x₀) := min_le_right _ _

/-- Normalizing a nonzero vector gives a unit vector: this is the `v_1 = r_0/β` of the
algorithms started from a residual. -/
theorem norm_norm_inv_smul {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) :
    ‖(‖r‖⁻¹ : 𝕜) • r‖ = 1 := by
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hr)]

/-- `‖v_1‖ = 1` unless `x_0` already solves the system. -/
theorem norm_v₁ (hr : r₀ A b x₀ ≠ 0) : ‖v₁ A b x₀‖ = 1 :=
  norm_norm_inv_smul hr

/-- The book's grade `μ` of `v_1` is the backbone grade of `r_0`: the two starting vectors are
proportional. -/
theorem grade_v₁ : grade A (v₁ A b x₀) = Krylov.grade (op A) (r₀ A b x₀) := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero]
    exact grade_eq A 0
  · rw [v₁, grade_normalize A h, grade_eq]

/-- The book's `𝒦_m(A, v_1)` is the backbone Krylov subspace of `r_0`: the two starting vectors
are proportional. -/
theorem krylov_v₁ (m : ℕ) : krylov A (v₁ A b x₀) m = Krylov.subspace (op A) (r₀ A b x₀) m := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero, krylov_eq]
  · have hc : ((‖r₀ A b x₀‖ : 𝕜))⁻¹ ≠ 0 := inv_ne_zero (by simpa using norm_ne_zero_iff.2 h)
    rw [v₁, krylov_smul A _ hc, krylov_eq]

end General

end SaadSparse.Chapter06
