import Numlib.Krylov.Hessenberg

/-!
# Perturbed Arnoldi and Lanczos relations

A finite-precision Arnoldi or Lanczos process does not produce the exact relation `A v_j = ∑_{i ≤
j+1} h_ij v_i` with an orthonormal `v`; it produces that relation up to a residual `F_j` of small
norm, with vectors that are orthonormal only up to a defect ([meurant2006lanczos] Thm 14, after
Paige).  This module isolates that as a hypothesis, `Arnoldi.IsPerturbedRelation`, so that the
exact-arithmetic identities can be restated with the perturbation carried along and applied to
computed quantities once a rounding model supplies the two bounds.

The structure is indexed by the number of steps `m`: `A v_j` is expanded for `j < m`, and the
orthogonality defect is controlled for the `m + 1` vectors `v_0, …, v_m` that those expansions
involve.  The exact process is the instance with `F = 0` and both bounds `0`
(`Arnoldi.hessenbergRelation_isPerturbedRelation`), which needs `m < grade` because the Arnoldi
vectors from the grade onwards are zero rather than unit.

What is carried along is the coordinate form of the residual, [saad2003iterative], (6.27).
`Arnoldi.IsPerturbedRelation.residual_eq` and `norm_residual_sub_le` bound the gap between the true
residual and the small-problem residual `V_{m+1} (β e₁ - H̄_m y)` that an implementation monitors,
and `abs_norm_sq_sub_sum_le` does the same for the Pythagoras identity that turns coordinates into
norms.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Arnoldi

/-- **A perturbed Hessenberg relation over `m` steps**: `A v_j = ∑_{i ≤ j+1} h_ij v_i + F_j` for `j
< m`, with `‖F_j‖ ≤ ε`, `h` upper Hessenberg, and the vectors `v_0, …, v_m` orthonormal up to a
defect `ε'` in every inner product.

This is the hypothesis a finite-precision Arnoldi or Lanczos process satisfies (Meurant and Strakoš,
*The Lanczos and conjugate gradient algorithms in finite precision arithmetic*, Theorem 14, with `ε`
and `ε'` of order `u ‖A‖`); the exact process is the case `ε = ε' = 0` and `F = 0`. -/
structure IsPerturbedRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) (F : ℕ → E) (m : ℕ)
    (ε ε' : ℝ) : Prop where
  /-- The Arnoldi expansion of `A v_j`, up to the residual `F_j`. -/
  apply_eq : ∀ j < m, A (v j) = ∑ i ∈ range (j + 2), h i j • v i + F j
  /-- The coefficients are upper Hessenberg. -/
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0
  /-- The residuals are small. -/
  norm_F_le : ∀ j < m, ‖F j‖ ≤ ε
  /-- The vectors are orthonormal up to the defect `ε'`. -/
  inner_sub_le : ∀ i ≤ m, ∀ j ≤ m,
    ‖(inner 𝕜 (v i) (v j) : 𝕜) - (if i = j then 1 else 0)‖ ≤ ε'

namespace IsPerturbedRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} {F : ℕ → E} {m : ℕ} {ε ε' : ℝ}
  (hv : IsPerturbedRelation A v h F m ε ε')
include hv

/-- The expansion of `A v_j` may be taken over any range containing `j + 2`. -/
private theorem apply_eq_range {j : ℕ} (hj : j < m) (N : ℕ) (hN : j + 2 ≤ N) :
    A (v j) = ∑ i ∈ range N, h i j • v i + F j := by
  rw [hv.apply_eq j hj]
  congr 1
  refine Finset.sum_subset (by simpa using hN) fun i _ hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- **The perturbed form of `Krylov.HessenbergRelation.apply_sum`**: `A V_m = V_{m+1} H̄_m + Δ`,
where the defect `Δ = ∑_j y_j F_j` is the residual combination. -/
theorem apply_sum (y : Fin m → 𝕜) :
    A (∑ j, y j • v j)
      = (∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i) + ∑ j, y j • F j := by
  rw [map_sum]
  have hleft : ∀ j : Fin m,
      A (y j • v j) = (∑ i : Fin (m + 1), (y j * h i j) • v i) + y j • F j := by
    intro j
    rw [map_smul, hv.apply_eq_range j.isLt (m + 1) (by omega), smul_add, Finset.smul_sum,
      Fin.sum_univ_eq_sum_range (fun i => (y j * h i (j : ℕ)) • v i) (m + 1)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [hessenbergOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **The perturbed form of `Krylov.HessenbergRelation.residual_eq`** ([saad2003iterative], (6.27)):
with `r₀ = β v₀`, the residual of `x₀ + V_m y` is `V_{m+1} (β e₁ - H̄_m y)` minus the residual
combination `∑_j y_j F_j`. -/
theorem residual_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j)
      = (∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i)
        - ∑ j, y j • F j := by
  have hfirst : ∑ i : Fin (m + 1), firstVec β (m + 1) i • v i = β • v 0 := by
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))]
    · rfl
    · intro i _ hi
      have hne : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
      simp [firstVec, hne]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hsplit : ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
      = β • v 0 - ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, map_add, hv.apply_sum y, ← hr]
  abel

/-- **The residual of the small problem is the true residual up to `ε ‖y‖₁`**: under a perturbed
relation the residual of `x₀ + V_m y` differs from `V_{m+1} (β e₁ - H̄_m y)`, the quantity a
finite-precision implementation monitors, by at most `ε ∑_j |y_j|`. -/
theorem norm_residual_sub_le {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (y : Fin m → 𝕜) :
    ‖(b - A (x₀ + ∑ j, y j • v j))
        - ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i‖
      ≤ ε * ∑ j, ‖y j‖ := by
  rw [hv.residual_eq hr y, sub_sub_cancel_left, norm_neg]
  calc ‖∑ j, y j • F j‖ ≤ ∑ j, ‖y j • F j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin m, ‖y j‖ * ε := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hv.norm_F_le j j.isLt) (norm_nonneg _)
    _ = ε * ∑ j, ‖y j‖ := by rw [← Finset.sum_mul, mul_comm]

/-- **The orthogonality defect in the Pythagoras identity**: `‖∑ c_i v_i‖²` differs from `∑ |c_i|²`
by at most `ε' (∑ |c_i|)²`, so at `ε' = 0` the coordinates carry the norm exactly, and in general
the small-problem norm is the true norm up to a term of order `ε'`. -/
theorem abs_norm_sq_sub_sum_le (c : Fin (m + 1) → 𝕜) :
    |‖∑ i, c i • v i‖ ^ 2 - ∑ i, ‖c i‖ ^ 2| ≤ ε' * (∑ i, ‖c i‖) ^ 2 := by
  classical
  -- the orthogonality defect of the pair `(i, j)`
  set e : Fin (m + 1) → Fin (m + 1) → 𝕜 := fun i j =>
    (inner 𝕜 (v i) (v j) : 𝕜) - (if (i : ℕ) = (j : ℕ) then 1 else 0) with he
  have hebound : ∀ i j, ‖e i j‖ ≤ ε' := fun i j =>
    hv.inner_sub_le i (Nat.lt_succ_iff.1 i.isLt) j (Nat.lt_succ_iff.1 j.isLt)
  have hinner : ∀ i j : Fin (m + 1),
      (inner 𝕜 (v i) (v j) : 𝕜) = (if (i : ℕ) = (j : ℕ) then 1 else 0) + e i j := by
    intro i j; rw [he]; ring
  -- expand the inner product of the sum with itself
  have hexpand : (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
      = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
          starRingEnd 𝕜 (c i) * c j * (inner 𝕜 (v i) (v j) : 𝕜) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum,
      ← mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hdiag : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        starRingEnd 𝕜 (c i) * c j * (if (i : ℕ) = (j : ℕ) then (1 : 𝕜) else 0)
      = ∑ i : Fin (m + 1), ((‖c i‖ : 𝕜) ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [RCLike.conj_mul]
    · intro j _ hj
      have hne : (i : ℕ) ≠ (j : ℕ) := fun hc => hj (Fin.ext hc.symm)
      simp [hne]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  -- the remainder
  set R : 𝕜 := ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    starRingEnd 𝕜 (c i) * c j * e i j with hR
  have hsum : (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
      = (∑ i : Fin (m + 1), ((‖c i‖ : 𝕜) ^ 2)) + R := by
    rw [hexpand, hR, ← hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hinner i j]; ring
  have hre : ‖∑ i, c i • v i‖ ^ 2 - ∑ i, ‖c i‖ ^ 2 = RCLike.re R := by
    have h1 : RCLike.re (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i) : 𝕜)
        = ‖∑ i : Fin (m + 1), c i • v i‖ ^ 2 := inner_self_eq_norm_sq _
    rw [hsum] at h1
    rw [map_add, map_sum] at h1
    have h2 : ∀ i : Fin (m + 1), RCLike.re ((‖c i‖ : 𝕜) ^ 2) = ‖c i‖ ^ 2 := by
      intro i; norm_cast
    simp only [h2] at h1
    linarith
  -- bound the remainder
  have hRbound : ‖R‖ ≤ ε' * (∑ i, ‖c i‖) ^ 2 := by
    calc ‖R‖ ≤ ∑ i : Fin (m + 1), ‖∑ j : Fin (m + 1), starRingEnd 𝕜 (c i) * c j * e i j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), ‖c i‖ * (‖c j‖ * ε') := by
          refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hebound i j) (norm_nonneg _)) (norm_nonneg _)
      _ = ε' * (∑ i, ‖c i‖) ^ 2 := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          rw [sq]
          ring
  rw [hre]
  exact (RCLike.abs_re_le_norm R).trans hRbound

end IsPerturbedRelation

/-- **The exact Arnoldi process is the unperturbed instance**: below the grade the Arnoldi vectors
are orthonormal and satisfy the Hessenberg relation exactly, so they satisfy
`Arnoldi.IsPerturbedRelation` with no residual and both bounds `0`.

The hypothesis `m < grade` is what the orthogonality clause needs: from the grade onwards the
Arnoldi vectors are `0` rather than unit (`Arnoldi.vec_eq_zero_iff`). -/
theorem hessenbergRelation_isPerturbedRelation (A : E →ₗ[𝕜] E) (b : E)
    [FiniteDimensional 𝕜 (Krylov.fullSubspace A b)] {m : ℕ} (hm : m < grade A b) :
    IsPerturbedRelation A (vec A b) (coeff A b) 0 m 0 0 where
  apply_eq j _ := by simpa using (hessenbergRelation A b).apply_eq j
  eq_zero_of_lt := (hessenbergRelation A b).eq_zero_of_lt
  norm_F_le j _ := by simp
  inner_sub_le i hi j hj := by
    rcases eq_or_ne i j with rfl | hij
    · have hnorm : ‖vec A b i‖ = 1 :=
        norm_vec_eq_one_of_lt_grade A b (lt_of_le_of_lt hi hm)
      simp [hnorm]
    · rw [inner_vec_eq_zero A b hij]
      simp [hij]

end Arnoldi
