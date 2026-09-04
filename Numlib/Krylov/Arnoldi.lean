import Numlib.Krylov.Subspace
import Numlib.Matrix.Hessenberg
import Numlib.InnerProductSpace.Compression
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Arnoldi's process

The Arnoldi vectors are the Gram–Schmidt orthonormalization of the Krylov sequence
`b, A b, A² b, …` (`InnerProductSpace.gramSchmidtNormed`), which is `0` after breakdown. This
gives orthonormality, `span {v₀, …, v_{m-1}} = 𝒦_m` (Saad Prop 6.4), breakdown iff grade
(Prop 6.6), the Hessenberg structure of `h i j = ⟪v i, A v j⟫` and the Arnoldi relation
`A v_j = ∑_{i ≤ j+1} h i j v_i` (Prop 6.5, (6.9)), and the identification with the classical
recurrence `w_j = A v_j - ∑_{i ≤ j} h_{ij} v_i`, `v_{j+1} = w_j / ‖w_j‖` (Alg 6.1).
Indices are `0`-based: `v 0 = b / ‖b‖`.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

/-- Arnoldi vectors: Gram–Schmidt of the Krylov sequence; `0` after breakdown. -/
noncomputable def vec (A : E →ₗ[𝕜] E) (b : E) : ℕ → E :=
  InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) b)

/-- Arnoldi (Hessenberg) coefficients `h i j = ⟪v i, A v j⟫`. -/
noncomputable def coeff (A : E →ₗ[𝕜] E) (b : E) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (vec A b i) (A (vec A b j))

variable (A : E →ₗ[𝕜] E) (b : E)

theorem vec_zero (hb : b ≠ 0) : vec A b 0 = (‖b‖⁻¹ : 𝕜) • b := by
  sorry

theorem norm_vec_eq_one_of_lt_grade [FiniteDimensional 𝕜 (fullSubspace A b)] {j : ℕ}
    (h : j < grade A b) :
    ‖vec A b j‖ = 1 := by
  sorry

/-- Saad Prop 6.6: breakdown at step `j` iff `j ≥ grade`. -/
theorem vec_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    vec A b j = 0 ↔ grade A b ≤ j := by
  sorry

theorem inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A b i) (vec A b j) = 0 := by
  sorry

theorem orthonormal [FiniteDimensional 𝕜 (fullSubspace A b)] :
    Orthonormal 𝕜 (fun i : Fin (grade A b) => vec A b i) := by
  sorry

/-- Saad Prop 6.4: the Arnoldi vectors span the Krylov subspaces. -/
theorem span_vec (m : ℕ) : Submodule.span 𝕜 (vec A b '' Set.Iio m) = subspace A b m := by
  sorry

theorem vec_mem_subspace (j : ℕ) : vec A b j ∈ subspace A b (j + 1) := by
  sorry

theorem vec_mem_orthogonal (j : ℕ) : vec A b j ∈ (subspace A b j)ᗮ := by
  sorry

/-- The Arnoldi vectors form an orthonormal basis of `𝒦_m` for `m ≤ grade`. -/
noncomputable def orthonormalBasis [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) :
    OrthonormalBasis (Fin m) 𝕜 (subspace A b m) := by
  sorry

/-- Hessenberg structure: `h i j = 0` for `i > j + 1`. -/
theorem coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A b i j = 0 := by
  sorry

/-- Arnoldi relation `A v_j = ∑_{i ≤ j+1} h i j v_i` (Saad (6.9)). -/
theorem apply_vec (j : ℕ) :
    A (vec A b j) = ∑ i ∈ Finset.range (j + 2), coeff A b i j • vec A b i := by
  sorry

/-- The unnormalized next vector `w_j = A v_j - ∑_{i ≤ j} h i j v_i` (Saad Alg 6.1, line 4). -/
noncomputable def w (j : ℕ) : E :=
  A (vec A b j) - ∑ i ∈ Finset.range (j + 1), coeff A b i j • vec A b i

theorem w_eq_sub_starProjection (j : ℕ) :
    w A b j = A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j)) := by
  sorry

/-- Saad Prop 6.22 (band structure, generalizing Lanczos tridiagonality): if `A` has an adjoint
`B` (`⟪A x, y⟫ = ⟪x, B y⟫`) with `B v ∈ 𝒦_s(A, v)` for every `v`, then `h i j = 0` for
`i + s ≤ j`. -/
theorem coeff_eq_zero_of_adjoint_mem {B : E →ₗ[𝕜] E} (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y))
    {s : ℕ} (hs : ∀ v, B v ∈ subspace A v s) {i j : ℕ} (h : i + s ≤ j) : coeff A b i j = 0 := by
  sorry

/-- `h_{j+1,j} = ‖w_j‖` (real and nonnegative). -/
theorem coeff_succ_self (j : ℕ) : coeff A b (j + 1) j = (‖w A b j‖ : 𝕜) := by
  sorry

/-- Saad Alg 6.1, line 7: `v_{j+1} = w_j / ‖w_j‖` (and `0` on breakdown). -/
theorem vec_succ_eq (j : ℕ) : vec A b (j + 1) = (‖w A b j‖⁻¹ : 𝕜) • w A b j := by
  sorry

theorem coeff_succ_self_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    coeff A b (j + 1) j = 0 ↔ grade A b ≤ j + 1 := by
  sorry

/-- The `(m+1) × m` Hessenberg matrix `H̄_m` (Saad (6.11)). -/
noncomputable def hessenberg (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

/-- The square Hessenberg matrix `H_m` (Saad (6.10)). -/
noncomputable def hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

theorem hessenberg_isUpperHessenbergRect (m : ℕ) :
    (hessenberg A b m).IsUpperHessenbergRect := by
  sorry

theorem hessenbergSq_isUpperHessenberg (m : ℕ) : (hessenbergSq A b m).IsUpperHessenberg := by
  sorry

/-- `A V_m = V_{m+1} H̄_m` (Saad (6.7)), coordinate form. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • vec A b j) = ∑ i : Fin (m + 1), (hessenberg A b m).mulVec y i • vec A b i := by
  sorry

/-- `H_m = V_mᴴ A V_m` is the matrix of the compression of `A` to `𝒦_m` (Saad (6.10),
Prop 6.5). -/
theorem hessenbergSq_eq_toMatrix_compression [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) :
    hessenbergSq A b m =
      LinearMap.toMatrix (orthonormalBasis A b hm).toBasis (orthonormalBasis A b hm).toBasis
        (compression A (subspace A b m)) := by
  sorry

/-- Basis-free form of the Arnoldi relation: `(1 - P_m) A P_m = h_{m+1,m} v_{m+1} v_mᴴ`, hence
`‖P_m A (1 - P_m)‖`-type identities (Saad-eig Prop 6.6, P-6.1). -/
theorem starProjection_apply_vec (m : ℕ) :
    A (vec A b m) - (subspace A b (m + 1)).starProjection (A (vec A b m)) =
      coeff A b (m + 1) m • vec A b (m + 1) := by
  sorry

end Arnoldi
