import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Subspace
import Numlib.Surface.SaadSparse.Chapter06.Section03

/-!
# Saad, Chapter 6: the data of a linear system

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, Chapter 6.

Every Krylov method of the chapter starts from the same three quantities: the initial residual
`r₀ = b - A x₀`, its norm `β = ‖r₀‖₂` and the unit vector `v₁ = r₀/β` on which Algorithm 6.1 is
run. The backbone indexes the Arnoldi process by the residual `r₀` itself, so each algorithm
needs the same translation between the book's `v₁`-indexed data and the backbone's `r₀`-indexed
data; that translation is the `*_v₁` family below, shared by
`Chapter06/Section04.lean`, `Chapter06/Section05.lean` and everything downstream of them.

The bridge lemmas need no hypothesis on `r₀`: when `r₀ = 0` both sides vanish, because Lean's
`(0 : ℝ)⁻¹ = 0` makes `v₁ = 0` and the backbone Arnoldi data of `0` is `0` as well.

`e₁` is the first coordinate vector, and `mEff` implements the book's "if `h_{j+1,j} = 0` then
set `m := j`" as `min m (grade A v₁)`.
-/

open scoped Matrix

namespace SaadSparse.Ch06

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

theorem mEff_le (m : ℕ) : mEff A b x₀ m ≤ grade A (v₁ A b x₀) := min_le_right _ _

/-- `‖v_1‖ = 1` unless `x_0` already solves the system. -/
theorem norm_v₁ (hr : r₀ A b x₀ ≠ 0) : ‖v₁ A b x₀‖ = 1 :=
  norm_norm_inv_smul hr

/-! ### The bridge to the backbone Arnoldi data of `r₀`

The book runs Algorithm 6.1 on the unit vector `v_1`, the backbone indexes the Arnoldi process
by the residual `r_0` itself; these lemmas translate. They hold with no hypothesis: when
`r_0 = 0` both sides vanish. -/

private theorem vec_zero_eq_v₁ : Arnoldi.vec (op A) (r₀ A b x₀) 0 = v₁ A b x₀ := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero]
    exact (Arnoldi.vec_eq_zero_iff_pow_apply_mem (op A) 0 0).2 (by simp)
  · exact Arnoldi.vec_zero (op A) _ h

/-- Algorithm 6.1 run on `v_1 = r_0/β` computes the backbone Arnoldi vectors of `r_0`. -/
theorem arnoldiCGS_v₁_apply (j : ℕ) :
    arnoldiCGS A (v₁ A b x₀) j = Arnoldi.vec (op A) (r₀ A b x₀) j :=
  arnoldiCGS_eq_vec_of_vec_zero A _ (vec_zero_eq_v₁ A b x₀) j

theorem arnoldiCGS_v₁ : arnoldiCGS A (v₁ A b x₀) = Arnoldi.vec (op A) (r₀ A b x₀) :=
  funext (arnoldiCGS_v₁_apply A b x₀)

/-- The book's `h_{ij}` computed from `v_1` are the backbone Arnoldi coefficients of `r_0`. -/
theorem arnoldiCoeff_v₁_apply (i j : ℕ) :
    arnoldiCoeff A (v₁ A b x₀) i j = Arnoldi.coeff (op A) (r₀ A b x₀) i j := by
  rw [arnoldiCoeff, arnoldiCGS_v₁_apply, arnoldiCGS_v₁_apply]
  rfl

theorem arnoldiCoeff_v₁ : arnoldiCoeff A (v₁ A b x₀) = Arnoldi.coeff (op A) (r₀ A b x₀) :=
  funext fun i => funext fun j => arnoldiCoeff_v₁_apply A b x₀ i j

theorem Hbar_v₁ (m : ℕ) : Hbar A (v₁ A b x₀) m = Arnoldi.hessenberg (op A) (r₀ A b x₀) m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_v₁]
  rfl

theorem H_v₁ (m : ℕ) : H A (v₁ A b x₀) m = Arnoldi.hessenbergSq (op A) (r₀ A b x₀) m := by
  ext i j
  rw [H_apply, arnoldiCoeff_v₁]
  rfl

/-- The Hessenberg structure of the coefficients, with no hypothesis on `v_1`. -/
theorem arnoldiCoeff_v₁_eq_zero_of_lt {i j : ℕ} (hij : j + 1 < i) :
    arnoldiCoeff A (v₁ A b x₀) i j = 0 := by
  rw [arnoldiCoeff_v₁]
  exact Arnoldi.coeff_eq_zero_of_lt (op A) _ hij

/-- The book's grade `μ` of `v_1` is the backbone grade of `r_0`: the two starting vectors are
proportional. -/
theorem grade_v₁ : grade A (v₁ A b x₀) = Krylov.grade (op A) (r₀ A b x₀) := by
  rcases eq_or_ne (r₀ A b x₀) 0 with h | h
  · rw [v₁, h, smul_zero]
    exact grade_eq A 0
  · rw [v₁, grade_normalize A h, grade_eq]

end General

end SaadSparse.Ch06
