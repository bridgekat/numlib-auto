import NumlibSurface.SaadSparse.Chapter07.Section01

/-!
# Saad §7.2: the two-sided Lanczos algorithm for linear systems

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §7.2.

**Algorithm 7.2** is `lanczosSolve`: run Algorithm 7.1 from `v_1 = r_0/β` and a dual starting
vector `w_1`, solve the tridiagonal system `T_m y_m = β e_1` and set `x_m = x_0 + V_m y_m`. It has
the shape of FOM (§6.4) with the Arnoldi basis replaced by the biorthogonal one, and
`lanczosSolve_isPetrovGalerkin` is the identification the section opens with: `x_m` is the
Petrov–Galerkin iterate onto `𝒦_m(A, v_1)` orthogonally to `𝒦_m(Aᴴ, w_1)`, the oblique
projection process §7.3.1 opens with. Only `NoBreakdown` and the nonsingularity of `T_m` are
needed, since
the orthogonality is tested against the dual basis directly through (7.5).

(7.9) is `equation_7_9`, the analogue of (6.18) and (6.87): the residual is a multiple of the
next Lanczos vector, `b - A x_m = -δ_{m+1}(e_mᵀ y_m) v_{m+1}`, so its norm costs nothing to
monitor. The factor `‖v_{m+1}‖₂` — which is `1` in FOM and in the symmetric Lanczos method — is
what survives when the basis is only biorthogonal. Both statements come from the backbone
`Krylov.HessenbergRelation` of §7.1 through `bilanczos_hessenbergRelation`, so the residual
formula is the same lemma that serves FOM.

Indices are `0`-based as in `Chapter07/Section01.lean`: `bilanczosV A v₁ w₁ j` is the book's
`v_{j+1}` and `bilanczosDelta A v₁ w₁ m` its `δ_{m+1}`.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The starting vector -/

/-- `β v_1 = r_0`: the normalization of Algorithm 6.4, line 1, with no hypothesis, since
`r_0 = 0` makes both sides vanish. -/
theorem smul_v₁_eq_r₀ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (Chapter06.β A b x₀ : 𝕜) • Chapter06.v₁ A b x₀ = b - op A x₀ := by
  rw [Chapter06.v₁, smul_smul]
  rcases eq_or_ne (Chapter06.β A b x₀) 0 with h | h
  · have hr : Chapter06.r₀ A b x₀ = 0 := norm_eq_zero.1 h
    rw [hr, smul_zero]
    exact hr.symm
  · rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 h), one_smul]

/-! ### Algorithm 7.2 -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- The coordinate vector `y_m = T_m⁻¹ (β e_1)` of the last line of Algorithm 7.2.
`Matrix.inv` is `0` at a singular `T_m`, which is the book's breakdown case. -/
noncomputable def lanczosSolveY (m : ℕ) : Fin m → 𝕜 :=
  (T A (Chapter06.v₁ A b x₀) w₁ m)⁻¹ *ᵥ ((Chapter06.β A b x₀ : 𝕜) • Chapter06.e₁ m)

/-- **Algorithm 7.2** (the two-sided Lanczos algorithm for linear systems):
`x_m = x_0 + V_m T_m⁻¹ (β e_1)`, with `V_m` the primal Lanczos basis of Algorithm 7.1 started
from `v_1 = r_0/β` and the dual vector `w_1`. -/
noncomputable def lanczosSolve (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + Matrix.toEuclideanLin (V A (Chapter06.v₁ A b x₀) w₁ m)
    (WithLp.toLp 2 (lanczosSolveY A b x₀ w₁ m))

/-- `x_m - x_0 = V_m y_m = ∑_j (y_m)_j v_j`, the form the backbone consumes. -/
theorem lanczosSolve_eq_add_sum (m : ℕ) :
    lanczosSolve A b x₀ w₁ m
      = x₀ + ∑ j, lanczosSolveY A b x₀ w₁ m j • bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ) :=
  congrArg (fun z => x₀ + z)
    (Chapter06.toEuclideanLin_colMatrix_apply _ (lanczosSolveY A b x₀ w₁ m))

/-- Nothing happens at step `0`. -/
@[simp] theorem lanczosSolve_zero : lanczosSolve A b x₀ w₁ 0 = x₀ := by
  rw [lanczosSolve_eq_add_sum]
  simp

/-- `T_m y_m = β e_1` whenever `T_m` is nonsingular: `y_m` really solves the tridiagonal
system of Algorithm 7.2. -/
theorem T_mulVec_lanczosSolveY {m : ℕ} (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) :
    T A (Chapter06.v₁ A b x₀) w₁ m *ᵥ lanczosSolveY A b x₀ w₁ m
      = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m := by
  rw [lanczosSolveY, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hT), Matrix.one_mulVec,
    Chapter06.smul_e₁_eq_firstVec]

end Algorithm

/-! ### The Petrov–Galerkin identification -/

section PetrovGalerkin

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- (7.5) entry by entry: `(A v_j, w_i) = T_{ij}` while the process has not broken down. -/
private theorem inner_bilanczosW_apply_bilanczosV {v : EuclideanSpace 𝕜 (Fin n)}
    (h : NoBreakdown A v w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j + 1 ≤ m) :
    inner 𝕜 (bilanczosW A v w₁ i) (op A (bilanczosV A v w₁ j)) = bilanczosCoeff A v w₁ i j := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
  exact BiLanczos.inner_dualVec_apply_vec h.toBiLanczos hi (by omega)

/-- **Saad §7.2**: the Algorithm 7.2 iterate is the Petrov–Galerkin approximation onto
`𝒦_m(A, v_1)` orthogonally to `𝒦_m(Aᴴ, w_1)` — the projection process (7.6) the section is
derived from. Only the no-breakdown hypothesis of §7.1 and the nonsingularity of `T_m` are
needed. -/
theorem lanczosSolve_isPetrovGalerkin (h : NoBreakdown A (Chapter06.v₁ A b x₀) w₁ m)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) :
    IsPetrovGalerkin (op A) b x₀ (Chapter06.krylov A (Chapter06.v₁ A b x₀) m)
      (Chapter06.krylov Aᴴ w₁ m) (lanczosSolve A b x₀ w₁ m) := by
  have hsum := lanczosSolve_eq_add_sum A b x₀ w₁ m
  constructor
  · rw [hsum, add_sub_cancel_left, ← (proposition_7_1_span h).1]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [← (proposition_7_1_span h).2, Submodule.mem_orthogonal_span]
    rintro _ ⟨i, rfl⟩
    have hres : b - op A (lanczosSolve A b x₀ w₁ m)
        = (b - op A x₀)
          - ∑ j, lanczosSolveY A b x₀ w₁ m j
              • op A (bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ)) := by
      rw [hsum, map_add, map_sum]
      simp only [map_smul]
      abel
    have hstart : inner 𝕜 (bilanczosW A (Chapter06.v₁ A b x₀) w₁ (i : ℕ)) (b - op A x₀)
        = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m i := by
      have h0 : b - op A x₀
          = (Chapter06.β A b x₀ : 𝕜) • bilanczosV A (Chapter06.v₁ A b x₀) w₁ 0 := by
        rw [bilanczosV_zero]
        exact (smul_v₁_eq_r₀ A b x₀).symm
      rw [h0, inner_smul_right, proposition_7_1 h (le_of_lt i.2) (Nat.zero_le m)]
      by_cases h1 : (i : ℕ) = 0 <;> simp [Krylov.firstVec, h1]
    have hcoeff : ∀ j : Fin m,
        inner 𝕜 (bilanczosW A (Chapter06.v₁ A b x₀) w₁ (i : ℕ))
            (op A (bilanczosV A (Chapter06.v₁ A b x₀) w₁ (j : ℕ)))
          = T A (Chapter06.v₁ A b x₀) w₁ m i j := fun j =>
      inner_bilanczosW_apply_bilanczosV h (le_of_lt i.2) j.2
    have hmv : (T A (Chapter06.v₁ A b x₀) w₁ m *ᵥ lanczosSolveY A b x₀ w₁ m) i
        = ∑ j, lanczosSolveY A b x₀ w₁ m j * T A (Chapter06.v₁ A b x₀) w₁ m i j := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hres, inner_sub_right, inner_sum, hstart]
    simp only [inner_smul_right, hcoeff]
    rw [← hmv, T_mulVec_lanczosSolveY A b x₀ w₁ hT, sub_self]

end PetrovGalerkin

/-! ### (7.9): the residual norm -/

section Residual

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Saad (7.9)**, in vector form: the residual of Algorithm 7.2 is a multiple of the next
Lanczos vector, `b - A x_m = -δ_{m+1} (e_mᵀ y_m) v_{m+1}`. -/
theorem residual_lanczosSolve (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) (hm : 0 < m) :
    b - op A (lanczosSolve A b x₀ w₁ m)
      = -(bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m
          * lanczosSolveY A b x₀ w₁ m ⟨m - 1, by omega⟩)
        • bilanczosV A (Chapter06.v₁ A b x₀) w₁ m := by
  have hstart : b - op A x₀
      = (Chapter06.β A b x₀ : 𝕜) • bilanczosV A (Chapter06.v₁ A b x₀) w₁ 0 := by
    rw [bilanczosV_zero]
    exact (smul_v₁_eq_r₀ A b x₀).symm
  have hmul : Krylov.hessenbergSqOf (bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁) m
      *ᵥ lanczosSolveY A b x₀ w₁ m = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) m := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hdelta : bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁ m (m - 1)
      = bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m := by
    obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, bilanczosCoeff_succ_self]
  rw [lanczosSolve_eq_add_sum, ← hdelta]
  exact (bilanczos_hessenbergRelation h).residual_eq_of_mulVec_eq hstart hm _ hmul

/-- **Saad (7.9)**: `‖b - A x_m‖₂ = |δ_{m+1} (e_mᵀ y_m)| ‖v_{m+1}‖₂`, so the residual norm of
Algorithm 7.2 is available without forming the iterate. This is the analogue of (6.18) for FOM
and of (6.87) for the symmetric Lanczos method; the factor `‖v_{m+1}‖₂`, which is `1` there, is
what a merely biorthogonal basis leaves behind. -/
theorem equation_7_9 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ m)) (hm : 0 < m) :
    ‖b - op A (lanczosSolve A b x₀ w₁ m)‖
      = ‖bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ m
          * lanczosSolveY A b x₀ w₁ m ⟨m - 1, by omega⟩‖
        * ‖bilanczosV A (Chapter06.v₁ A b x₀) w₁ m‖ := by
  rw [residual_lanczosSolve h hT hm, norm_smul, norm_neg]

end Residual

end SaadSparse.Chapter07
