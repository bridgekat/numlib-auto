import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Analysis.InnerProductSpace.Projection.Compression
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

/-! ### The unnormalized Gram–Schmidt vectors

`gs` is `vec` before normalization; the statements about `vec` and `w` are proved by first
identifying both with a nonnegative real multiple of `gs`. -/

/-- The unnormalized Gram–Schmidt vectors of the Krylov sequence. -/
private noncomputable def gs : ℕ → E :=
  InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b)

private theorem gs_def (j : ℕ) :
    gs A b j = InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) j := rfl

private theorem vec_eq_smul_gs (j : ℕ) : vec A b j = (‖gs A b j‖ : 𝕜)⁻¹ • gs A b j := rfl

private theorem gs_orthogonal {i j : ℕ} (h : i ≠ j) : inner 𝕜 (gs A b i) (gs A b j) = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal 𝕜 _ h

/-- `x⁻¹ (y⁻¹ x²) = y⁻¹ x`, also when `x = 0`. -/
private theorem inv_mul_inv_mul_sq (x y : ℝ) :
    ((x : 𝕜))⁻¹ * ((y : 𝕜)⁻¹ * (x : 𝕜) ^ 2) = ((y⁻¹ * x : ℝ) : 𝕜) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : ((x : ℝ) : 𝕜) ≠ 0 := by simpa using hx
    push_cast
    field_simp

/-- `(y⁻¹ x)⁻¹ y⁻¹ = x⁻¹` for `y ≠ 0`, also when `x = 0`. -/
private theorem inv_mul_inv_cancel (x y : ℝ) (hy : y ≠ 0) :
    (((y⁻¹ * x : ℝ)) : 𝕜)⁻¹ * ((y : ℝ) : 𝕜)⁻¹ = ((x : ℝ) : 𝕜)⁻¹ := by
  have hy' : ((y : ℝ) : 𝕜) ≠ 0 := by simpa using hy
  push_cast
  rw [mul_inv, inv_inv, mul_right_comm, mul_inv_cancel₀ hy', one_mul]

/-- A vector orthogonal to a generating set is orthogonal to the span. -/
private theorem mem_orthogonal_span {s : Set E} {x : E}
    (h : ∀ u ∈ s, inner 𝕜 u x = (0 : 𝕜)) : x ∈ (Submodule.span 𝕜 s)ᗮ := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

private theorem subspace_eq_span_gs_image (m : ℕ) :
    subspace A b m = Submodule.span 𝕜 (gs A b '' Set.Iio m) := by
  rw [subspace_eq_span_image_Iio]
  exact (InnerProductSpace.span_gramSchmidt_Iio 𝕜 (fun i : ℕ => (A ^ i) b) m).symm

private theorem gs_mem_subspace {i j : ℕ} (h : i < j) : gs A b i ∈ subspace A b j := by
  rw [subspace_eq_span_gs_image]
  exact Submodule.subset_span ⟨i, h, rfl⟩

private theorem gs_mem_orthogonal (j : ℕ) : gs A b j ∈ (subspace A b j)ᗮ := by
  rw [subspace_eq_span_gs_image]
  refine mem_orthogonal_span ?_
  rintro _ ⟨i, hi, rfl⟩
  exact gs_orthogonal A b hi.ne

/-- `gs j` is the component of `A^j b` orthogonal to `𝒦_j`. -/
private theorem gs_eq_sub_starProjection (j : ℕ) :
    gs A b j = (A ^ j) b - (subspace A b j).starProjection ((A ^ j) b) := by
  have hd := InnerProductSpace.gramSchmidt_def' 𝕜 (fun i : ℕ => (A ^ i) b) j
  have hsum : (A ^ j) b - gs A b j =
      ∑ i ∈ Finset.Iio j,
        (𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) b) i).starProjection
          ((A ^ j) b) := sub_eq_of_eq_add' hd
  have hP : (subspace A b j).starProjection ((A ^ j) b) = (A ^ j) b - gs A b j := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hsum]
      refine Submodule.sum_mem _ fun i hi => ?_
      refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_ (Submodule.starProjection_apply_mem _ _)
      exact gs_mem_subspace A b (Finset.mem_Iio.1 hi)
    · intro y hy
      rw [sub_sub_cancel]
      exact Submodule.inner_left_of_mem_orthogonal hy (gs_mem_orthogonal A b j)
  rw [hP, sub_sub_cancel]

private theorem gs_eq_zero_iff (j : ℕ) : gs A b j = 0 ↔ (A ^ j) b ∈ subspace A b j := by
  rw [gs_eq_sub_starProjection, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-! ### Basic properties of the Arnoldi vectors -/

-- `hb` is not needed: for `b = 0` both sides are `0`.
set_option linter.unusedVariables false in
theorem vec_zero (hb : b ≠ 0) : vec A b 0 = (‖b‖⁻¹ : 𝕜) • b := by
  have h0 : gs A b 0 = b := by
    rw [gs_def, show (0 : ℕ) = ⊥ from rfl, InnerProductSpace.gramSchmidt_bot]
    simp
  rw [vec_eq_smul_gs, h0]

theorem vec_eq_zero_iff_pow_apply_mem (j : ℕ) :
    vec A b j = 0 ↔ (A ^ j) b ∈ subspace A b j := by
  rw [← gs_eq_zero_iff, vec_eq_smul_gs, smul_eq_zero]
  refine ⟨fun h => h.elim (fun hc => ?_) id, fun h => Or.inr h⟩
  rw [inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero] at hc
  exact hc

theorem norm_vec_eq_one_of_ne_zero {j : ℕ} (h : vec A b j ≠ 0) : ‖vec A b j‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length' h

theorem vec_mem_subspace (j : ℕ) : vec A b j ∈ subspace A b (j + 1) := by
  rw [vec_eq_smul_gs]
  exact Submodule.smul_mem _ _ (gs_mem_subspace A b j.lt_succ_self)

theorem vec_mem_subspace_of_lt {i m : ℕ} (h : i < m) : vec A b i ∈ subspace A b m :=
  subspace_mono A b h (vec_mem_subspace A b i)

theorem vec_mem_orthogonal (j : ℕ) : vec A b j ∈ (subspace A b j)ᗮ := by
  rw [vec_eq_smul_gs]
  exact Submodule.smul_mem _ _ (gs_mem_orthogonal A b j)

theorem inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A b i) (vec A b j) = 0 := by
  rw [vec_eq_smul_gs, vec_eq_smul_gs, inner_smul_left, inner_smul_right, gs_orthogonal A b h]
  simp

/-- Saad Prop 6.4: the Arnoldi vectors span the Krylov subspaces. -/
theorem span_vec (m : ℕ) : Submodule.span 𝕜 (vec A b '' Set.Iio m) = subspace A b m := by
  rw [subspace_eq_span_gs_image]
  exact InnerProductSpace.span_gramSchmidtNormed (fun i : ℕ => (A ^ i) b) (Set.Iio m)

section FiniteDimensional

variable [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Saad Prop 6.6: breakdown at step `j` iff `j ≥ grade`. -/
theorem vec_eq_zero_iff (j : ℕ) : vec A b j = 0 ↔ grade A b ≤ j := by
  rw [vec_eq_zero_iff_pow_apply_mem, grade_le_iff]

theorem norm_vec_eq_one_of_lt_grade {j : ℕ} (h : j < grade A b) : ‖vec A b j‖ = 1 :=
  norm_vec_eq_one_of_ne_zero A b (fun hz => absurd ((vec_eq_zero_iff A b j).1 hz) (not_le.2 h))

theorem orthonormal : Orthonormal 𝕜 (fun i : Fin (grade A b) => vec A b i) :=
  ⟨fun i => norm_vec_eq_one_of_lt_grade A b i.2,
    fun _ _ hij => inner_vec_eq_zero A b fun h => hij (Fin.val_injective h)⟩

end FiniteDimensional

/-! ### Expansion in the Arnoldi vectors -/

private theorem sub_sum_inner_smul_vec_mem_orthogonal (x : E) (m : ℕ) :
    x - ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i ∈ (subspace A b m)ᗮ := by
  rw [← span_vec]
  refine mem_orthogonal_span ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [inner_sub_right, inner_sum, Finset.sum_eq_single k]
  · rcases eq_or_ne (vec A b k) 0 with h0 | h0
    · simp [h0]
    · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_vec_eq_one_of_ne_zero A b h0]
      simp
  · intro i _ hik
    rw [inner_smul_right, inner_vec_eq_zero A b (Ne.symm hik), mul_zero]
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

/-- Every element of `𝒦_m` is its own orthonormal expansion in the Arnoldi vectors (the vectors
that vanish after breakdown contribute nothing). -/
theorem eq_sum_inner_smul_vec {x : E} {m : ℕ} (hx : x ∈ subspace A b m) :
    x = ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i := by
  have hy : x - ∑ i ∈ Finset.range m, inner 𝕜 (vec A b i) x • vec A b i ∈ subspace A b m :=
    Submodule.sub_mem _ hx (Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b (Finset.mem_range.1 hi)))
  have h0 := Submodule.inner_right_of_mem_orthogonal hy
    (sub_sum_inner_smul_vec_mem_orthogonal A b x m)
  rw [inner_self_eq_zero, sub_eq_zero] at h0
  exact h0

section OrthonormalBasis

/-- The Arnoldi vectors of `𝒦_m`, as elements of `𝒦_m`. -/
private noncomputable def vecIn {m : ℕ} (i : Fin m) : subspace A b m :=
  ⟨vec A b i, vec_mem_subspace_of_lt A b i.2⟩

private theorem orthonormal_vecIn [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) : Orthonormal 𝕜 (vecIn A b (m := m)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact norm_vec_eq_one_of_lt_grade A b (i.2.trans_le hm)
  · exact inner_vec_eq_zero A b fun h => hij (Fin.val_injective h)

private theorem span_vecIn {m : ℕ} :
    ⊤ ≤ Submodule.span 𝕜 (Set.range (vecIn A b (m := m))) := by
  intro x _
  have hxe : x = ∑ i : Fin m, inner 𝕜 (vec A b i) (x : E) • vecIn A b i := by
    apply Subtype.ext
    push_cast [vecIn]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => inner 𝕜 (vec A b i) (x : E) • vec A b i) m]
    exact eq_sum_inner_smul_vec A b x.2
  rw [hxe]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The Arnoldi vectors form an orthonormal basis of `𝒦_m` for `m ≤ grade`. -/
noncomputable def orthonormalBasis [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) : OrthonormalBasis (Fin m) 𝕜 (subspace A b m) :=
  OrthonormalBasis.mk (orthonormal_vecIn A b hm) (span_vecIn A b)

@[simp]
theorem coe_orthonormalBasis_apply [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) (i : Fin m) : (orthonormalBasis A b hm i : E) = vec A b i :=
  congrArg Subtype.val
    (congrFun (OrthonormalBasis.coe_mk (orthonormal_vecIn A b hm) (span_vecIn A b)) i)

end OrthonormalBasis

/-! ### The Hessenberg structure -/

/-- Hessenberg structure: `h i j = 0` for `i > j + 1`. -/
theorem coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A b i j = 0 := by
  refine Submodule.inner_left_of_mem_orthogonal (K := subspace A b (j + 2))
    (map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩) ?_
  exact Submodule.orthogonal_le (subspace_mono A b (by omega)) (vec_mem_orthogonal A b i)

/-- Arnoldi relation `A v_j = ∑_{i ≤ j+1} h i j v_i` (Saad (6.9)). -/
theorem apply_vec (j : ℕ) :
    A (vec A b j) = ∑ i ∈ Finset.range (j + 2), coeff A b i j • vec A b i := by
  have hx : A (vec A b j) ∈ subspace A b (j + 1 + 1) :=
    map_subspace_le A b (j + 1) ⟨_, vec_mem_subspace A b j, rfl⟩
  simpa [coeff] using eq_sum_inner_smul_vec A b hx

theorem apply_vec_of_le {j n : ℕ} (h : j + 2 ≤ n) :
    A (vec A b j) = ∑ i ∈ Finset.range n, coeff A b i j • vec A b i := by
  rw [apply_vec]
  refine Finset.sum_subset (fun i hi => Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le h))
    fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  rw [coeff_eq_zero_of_lt A b (by omega), zero_smul]

/-- The unnormalized next vector `w_j = A v_j - ∑_{i ≤ j} h i j v_i` (Saad Alg 6.1, line 4). -/
noncomputable def w (j : ℕ) : E :=
  A (vec A b j) - ∑ i ∈ Finset.range (j + 1), coeff A b i j • vec A b i

theorem w_eq_sub_starProjection (j : ℕ) :
    w A b j = A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j)) := by
  rw [w]
  congr 1
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_).symm
  · exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b (Finset.mem_range.1 hi))
  · intro y hy
    exact Submodule.inner_left_of_mem_orthogonal hy
      (sub_sum_inner_smul_vec_mem_orthogonal A b (A (vec A b j)) (j + 1))

/-- Saad Prop 6.22 (band structure, generalizing Lanczos tridiagonality): if `A` has an adjoint
`B` (`⟪A x, y⟫ = ⟪x, B y⟫`) with `B v ∈ 𝒦_s(A, v)` for every `v`, then `h i j = 0` for
`i + s ≤ j`. -/
theorem coeff_eq_zero_of_adjoint_mem {B : E →ₗ[𝕜] E} (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y))
    {s : ℕ} (hs : ∀ v, B v ∈ subspace A v s) {i j : ℕ} (h : i + s ≤ j) : coeff A b i j = 0 := by
  have hle : subspace A (vec A b i) s ≤ subspace A b j := by
    rw [subspace, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < s := k.2
    exact subspace_mono A b (by omega)
      (pow_apply_mem_subspace_of_mem A b (vec_mem_subspace A b i) k)
  have hconj : coeff A b i j = starRingEnd 𝕜 (inner 𝕜 (vec A b j) (B (vec A b i))) := by
    rw [coeff, ← hB, inner_conj_symm]
  rw [hconj, Submodule.inner_left_of_mem_orthogonal (hle (hs (vec A b i)))
    (vec_mem_orthogonal A b j), map_zero]

/-! ### The classical recurrence -/

private theorem w_eq_smul_gs (j : ℕ) : w A b j = (‖gs A b j‖ : 𝕜)⁻¹ • gs A b (j + 1) := by
  have hz : A ((subspace A b j).starProjection ((A ^ j) b)) ∈ subspace A b (j + 1) :=
    map_subspace_le A b j ⟨_, Submodule.starProjection_apply_mem _ _, rfl⟩
  have hpow : (A ^ (j + 1)) b = A ((A ^ j) b) := by rw [pow_succ']; rfl
  have hkey : A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b ∈ subspace A b (j + 1) := by
    have hrw : A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b =
        -((‖gs A b j‖ : 𝕜)⁻¹ • A ((subspace A b j).starProjection ((A ^ j) b))) := by
      rw [vec_eq_smul_gs, gs_eq_sub_starProjection, map_smul, map_sub, hpow]
      module
    rw [hrw]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hz)
  have hcongr : A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j)) =
      (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b -
        (subspace A b (j + 1)).starProjection ((‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b) := by
    have hself : (subspace A b (j + 1)).starProjection
        (A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b) =
        A (vec A b j) - (‖gs A b j‖ : 𝕜)⁻¹ • (A ^ (j + 1)) b :=
      Submodule.starProjection_eq_self_iff.2 hkey
    rw [map_sub] at hself
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hself.symm
  rw [w_eq_sub_starProjection, hcongr, map_smul, ← smul_sub, ← gs_eq_sub_starProjection]

private theorem norm_w (j : ℕ) : ‖w A b j‖ = ‖gs A b j‖⁻¹ * ‖gs A b (j + 1)‖ := by
  rw [w_eq_smul_gs, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

private theorem inner_vec_succ_w (j : ℕ) :
    inner 𝕜 (vec A b (j + 1)) (w A b j) = (‖w A b j‖ : 𝕜) := by
  rw [norm_w, w_eq_smul_gs, vec_eq_smul_gs, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal]
  exact inv_mul_inv_mul_sq _ _

/-- `h_{j+1,j} = ‖w_j‖` (real and nonnegative). -/
theorem coeff_succ_self (j : ℕ) : coeff A b (j + 1) j = (‖w A b j‖ : 𝕜) := by
  have hsplit : A (vec A b j) =
      w A b j + (subspace A b (j + 1)).starProjection (A (vec A b j)) := by
    rw [w_eq_sub_starProjection]; abel
  rw [coeff, hsplit, inner_add_right, inner_vec_succ_w,
    Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
      (vec_mem_orthogonal A b (j + 1)), add_zero]

/-- Saad Alg 6.1, line 7: `v_{j+1} = w_j / ‖w_j‖` (and `0` on breakdown). -/
theorem vec_succ_eq (j : ℕ) : vec A b (j + 1) = (‖w A b j‖⁻¹ : 𝕜) • w A b j := by
  rcases eq_or_ne (gs A b j) 0 with h0 | h0
  · have h1 : gs A b (j + 1) = 0 := by
      rw [gs_eq_zero_iff]
      exact pow_apply_mem_subspace_of_le A b ((gs_eq_zero_iff A b j).1 h0) j.le_succ
    rw [vec_eq_smul_gs, h1, w_eq_smul_gs, h1, smul_zero, smul_zero, smul_zero]
  · have ha : ((‖gs A b j‖ : ℝ) : 𝕜) ≠ 0 := by simpa using norm_ne_zero_iff.2 h0
    rw [vec_eq_smul_gs, norm_w, w_eq_smul_gs, smul_smul]
    exact congrArg (· • gs A b (j + 1))
      (inv_mul_inv_cancel (𝕜 := 𝕜) _ _ (norm_ne_zero_iff.2 h0)).symm

private theorem w_eq_zero_iff (j : ℕ) : w A b j = 0 ↔ vec A b (j + 1) = 0 := by
  rw [vec_succ_eq]
  refine ⟨fun h => by rw [h, smul_zero], fun h => ?_⟩
  by_contra h0
  exact smul_ne_zero (inv_ne_zero (by simpa using norm_ne_zero_iff.2 h0)) h0 h

theorem coeff_succ_self_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    coeff A b (j + 1) j = 0 ↔ grade A b ≤ j + 1 := by
  rw [coeff_succ_self, RCLike.ofReal_eq_zero, norm_eq_zero, w_eq_zero_iff, vec_eq_zero_iff]

/-! ### The Hessenberg matrices -/

/-- The `(m+1) × m` Hessenberg matrix `H̄_m` (Saad (6.11)). -/
noncomputable def hessenberg (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

/-- The square Hessenberg matrix `H_m` (Saad (6.10)). -/
noncomputable def hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => coeff A b i j

theorem hessenberg_isUpperHessenbergRect (m : ℕ) :
    (hessenberg A b m).IsUpperHessenbergRect := fun _ _ h => coeff_eq_zero_of_lt A b h

theorem hessenbergSq_isUpperHessenberg (m : ℕ) : (hessenbergSq A b m).IsUpperHessenberg := by
  rintro i j ⟨k, hjk, hki⟩
  rw [Fin.lt_def] at hjk hki
  exact coeff_eq_zero_of_lt A b (by omega)

/-- `A V_m = V_{m+1} H̄_m` (Saad (6.7)), coordinate form. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • vec A b j) = ∑ i : Fin (m + 1), (hessenberg A b m).mulVec y i • vec A b i := by
  rw [map_sum]
  have hAv : ∀ j : Fin m, y j • A (vec A b j) =
      ∑ i : Fin (m + 1), (y j * coeff A b i j) • vec A b i := by
    intro j
    rw [apply_vec_of_le A b (n := m + 1) (by omega),
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ => coeff A b i j • vec A b i) (m + 1),
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  simp only [map_smul, hAv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmv : (hessenberg A b m).mulVec y i = ∑ j : Fin m, y j * coeff A b i j := by
    simp [Matrix.mulVec, dotProduct, hessenberg, mul_comm]
  rw [hmv, Finset.sum_smul]

/-- `H_m = V_mᴴ A V_m` is the matrix of the compression of `A` to `𝒦_m` (Saad (6.10),
Prop 6.5). -/
theorem hessenbergSq_eq_toMatrix_compression [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) :
    hessenbergSq A b m =
      LinearMap.toMatrix (orthonormalBasis A b hm).toBasis (orthonormalBasis A b hm).toBasis
        (compression A (subspace A b m)) := by
  rw [compression.toMatrix_orthonormalBasis]
  ext i j
  simp [hessenbergSq, coeff]

/-- Basis-free form of the Arnoldi relation: `(1 - P_m) A P_m = h_{m+1,m} v_{m+1} v_mᴴ`, hence
`‖P_m A (1 - P_m)‖`-type identities (Saad-eig Prop 6.6, P-6.1). -/
theorem starProjection_apply_vec (m : ℕ) :
    A (vec A b m) - (subspace A b (m + 1)).starProjection (A (vec A b m)) =
      coeff A b (m + 1) m • vec A b (m + 1) := by
  rw [← w_eq_sub_starProjection, coeff_succ_self, vec_succ_eq, smul_smul]
  rcases eq_or_ne (w A b m) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

end Arnoldi
