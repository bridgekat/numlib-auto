import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter09.Section03

/-!
# Saad §9.4: flexible variants

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §9.4.

FGMRES is the first method of the book whose search space is not a Krylov subspace: the
preconditioner may change at every step, so the iterate is expanded in the arbitrary directions
`z_j = M_j⁻¹ v_j` while the residual is still expanded in the orthonormal Arnoldi basis `v_i`.
That is a `Krylov.HessenbergRelation₂` with two families — `equation_9_22` — and the whole of the
section follows from `Numlib/Krylov/QuasiMinRes.lean` and `Numlib/Krylov/Preconditioned.lean`.

* `fgmresV`, `fgmresZ`, `fgmresW` and `fgmresCoeff` are Algorithm 9.6 lines 3–9, and `fgmres` is
  its iterate `x_m = x₀ + Z_m y_m` with `y_m` the minimizer of `‖β e₁ - H̄_m y‖₂` computed, as in
  Algorithm 6.9, by the Givens process.
* `orthonormal_fgmresV` is the statement that the Arnoldi basis is orthonormal as long as the
  process does not break down; this is what makes the quasi-residual the true residual.
* `proposition_9_2` is the optimality of FGMRES and `proposition_9_3` its breakdown criterion,
  with `hessenbergSq_isUnit_of_linearIndependent` the book's remark that the extra nonsingularity
  hypothesis of Proposition 9.3 is not vacuous.
* `fgmres_eq_of_apply_fgmresZ_eq` is §9.4.1's consequence of Proposition 9.3: an inner solve that
  happens to be exact at one step, `A z_j = v_j`, ends the outer iteration.
* `fgmres_eq_gmresRight` says that a constant preconditioner gives back Algorithm 9.5.
* `fdqgmres` is (9.28), flexible DQGMRES: Algorithm 6.13 fed the preconditioned vectors
  `M_j⁻¹ v_j`, which it consumes at once and need not store.
-/

open Matrix Finset

open scoped SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Algorithm 9.6 -/

/-- **Algorithm 9.6** (FGMRES), lines 3–9, `0`-based: the Arnoldi basis of the flexible process.
`v_0 = v₁` and `v_{j+1} = w_j / ‖w_j‖` with `w_j = A M_j⁻¹ v_j - ∑_{i ≤ j} h_{ij} v_i` and
`h_{ij} = (A M_j⁻¹ v_j, v_i)`. The book's "if `h_{j+1,j} = 0` then Stop" is Lean's `x / 0 = 0`. -/
noncomputable def fgmresV (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n)
  | 0 => v₁
  | j + 1 =>
    let v : Fin (j + 1) → EuclideanSpace 𝕜 (Fin n) := fun i => fgmresV M A v₁ (i : ℕ)
    let Az := op A (op (M j)⁻¹ (v (Fin.last j)))
    let w := Az - ∑ i : Fin (j + 1), inner 𝕜 (v i) Az • v i
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact i.isLt

/-- **Algorithm 9.6**, line 3: the preconditioned direction `z_j = M_j⁻¹ v_j`, in which FGMRES
expands its iterate. -/
noncomputable def fgmresZ (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op (M j)⁻¹ (fgmresV M A v₁ j)

/-- **Algorithm 9.6**, lines 4–7: the unnormalized vector `w_j = A z_j - ∑_{i ≤ j} h_{ij} v_i`. -/
noncomputable def fgmresW (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op A (fgmresZ M A v₁ j) -
    ∑ i ∈ Finset.range (j + 1),
      inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i

/-- **Algorithm 9.6**, lines 6 and 9: the Hessenberg coefficients `h_{ij} = (A z_j, v_i)` for
`i ≤ j` and `h_{j+1,j} = ‖w_j‖₂`, and `0` below the subdiagonal. -/
noncomputable def fgmresCoeff (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) (i j : ℕ) : 𝕜 :=
  if i = j + 1 then (‖fgmresW M A v₁ j‖ : 𝕜)
  else if i ≤ j then inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j))
  else 0

variable {M : ℕ → Matrix (Fin n) (Fin n) 𝕜} {A : Matrix (Fin n) (Fin n) 𝕜}
variable {v₁ : EuclideanSpace 𝕜 (Fin n)}

/-- Algorithm 9.6, line 1: the Arnoldi basis starts at `v_1`. -/
@[simp]
theorem fgmresV_zero : fgmresV M A v₁ 0 = v₁ := by rw [fgmresV]

/-- Algorithm 9.6, line 9: `v_{j+1} = w_j/‖w_j‖₂`, and `0` at a breakdown. -/
theorem fgmresV_succ (j : ℕ) :
    fgmresV M A v₁ (j + 1) = ((‖fgmresW M A v₁ j‖ : 𝕜)⁻¹) • fgmresW M A v₁ j := by
  rw [fgmresV, fgmresW, fgmresZ]
  simp only [Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner 𝕜 (fgmresV M A v₁ i) (op A (op (M j)⁻¹ (fgmresV M A v₁ j))) •
      fgmresV M A v₁ i) (j + 1)]

/-- On and above the diagonal the coefficient is `h_{ij} = (A z_j, v_i)`. -/
theorem fgmresCoeff_of_le {i j : ℕ} (hij : i ≤ j) :
    fgmresCoeff M A v₁ i j = inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) := by
  rw [fgmresCoeff, ite_eq_right (by omega), ite_eq_left hij]

/-- The subdiagonal coefficient is `h_{j+1,j} = ‖w_j‖₂`. -/
theorem fgmresCoeff_succ_self (j : ℕ) :
    fgmresCoeff M A v₁ (j + 1) j = (‖fgmresW M A v₁ j‖ : 𝕜) := by
  rw [fgmresCoeff, ite_eq_left rfl]

/-- The coefficient array is upper Hessenberg. -/
theorem fgmresCoeff_eq_zero_of_lt {i j : ℕ} (hij : j + 1 < i) : fgmresCoeff M A v₁ i j = 0 := by
  rw [fgmresCoeff, ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ### (9.22): the two-family Hessenberg relation -/

/-- `‖w‖ • (‖w‖⁻¹ • w) = w`, including at a breakdown, where both sides vanish. -/
private theorem smul_inv_smul_norm (w : EuclideanSpace 𝕜 (Fin n)) :
    ((‖w‖ : 𝕜)) • (((‖w‖ : 𝕜))⁻¹ • w) = w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [smul_smul, mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 hw), one_smul]

/-- **(9.22)–(9.23)**: `A Z_m = V_{m+1} H̄_m`, the two-family Hessenberg relation of the flexible
process, which replaces the relation `(A M⁻¹) V_m = V_{m+1} H̄_m` of the fixed-preconditioner
case. It holds unconditionally, a breakdown `h_{j+1,j} = 0` included. -/
theorem equation_9_22 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ : EuclideanSpace 𝕜 (Fin n)) :
    Krylov.HessenbergRelation₂ (op A) (fgmresZ M A v₁) (fgmresV M A v₁) (fgmresCoeff M A v₁) := by
  refine ⟨fun j => ?_, fun i j hij => fgmresCoeff_eq_zero_of_lt hij⟩
  rw [Finset.sum_range_succ, fgmresCoeff_succ_self, fgmresV_succ, smul_inv_smul_norm, fgmresW]
  rw [Finset.sum_congr rfl fun i (hi : i ∈ Finset.range (j + 1)) => by
    rw [fgmresCoeff_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]]
  abel

/-! ### Orthonormality of the flexible Arnoldi basis -/

/-- The normalized vector of the next step is a unit vector, away from a breakdown. -/
private theorem norm_fgmresV_succ {j : ℕ} (hw : fgmresW M A v₁ j ≠ 0) :
    ‖fgmresV M A v₁ (j + 1)‖ = 1 := by
  rw [fgmresV_succ, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]

/-- The Gram matrix of the flexible Arnoldi basis is the identity, as long as the process has not
broken down: this is the induction behind `SaadSparse.Chapter09.orthonormal_fgmresV`. -/
private theorem inner_fgmresV (hv : ‖v₁‖ = 1) :
    ∀ m : ℕ, (∀ j, j < m → fgmresW M A v₁ j ≠ 0) →
      ∀ a ≤ m, ∀ b ≤ m,
        inner 𝕜 (fgmresV M A v₁ a) (fgmresV M A v₁ b) = if a = b then 1 else 0 := by
  intro m
  induction m with
  | zero =>
    intro _ a ha b hb
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    obtain rfl : b = 0 := Nat.le_zero.1 hb
    rw [ite_eq_left rfl, fgmresV_zero, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  | succ m ih =>
    intro hbreak
    have hIH := ih fun j hj => hbreak j (by omega)
    -- the new vector is orthogonal to all the previous ones
    have hperp : ∀ c ≤ m, inner 𝕜 (fgmresV M A v₁ c) (fgmresW M A v₁ m) = 0 := by
      intro c hc
      rw [fgmresW, inner_sub_right, inner_sum]
      have hterm : ∀ i ∈ Finset.range (m + 1),
          inner 𝕜 (fgmresV M A v₁ c)
              (inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ m)) • fgmresV M A v₁ i)
            = if i = c then inner 𝕜 (fgmresV M A v₁ c) (op A (fgmresZ M A v₁ m)) else 0 := by
        intro i hi
        rw [inner_smul_right, hIH c hc i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
        by_cases hic : c = i
        · rw [ite_eq_left hic, ite_eq_left hic.symm, mul_one, hic]
        · rw [ite_eq_right hic, ite_eq_right (fun h => hic h.symm), mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (m + 1)) c
        (fun _ => inner 𝕜 (fgmresV M A v₁ c) (op A (fgmresZ M A v₁ m))),
        ite_eq_left (Finset.mem_range.2 (by omega)), sub_self]
    have hnew : ∀ c ≤ m, inner 𝕜 (fgmresV M A v₁ c) (fgmresV M A v₁ (m + 1)) = 0 := by
      intro c hc
      rw [fgmresV_succ, inner_smul_right, hperp c hc, mul_zero]
    intro a ha b hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ha) with ha' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hb) with hb' | rfl
      · exact hIH a (by omega) b (by omega)
      · rw [hnew a (by omega), ite_eq_right (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hb) with hb' | rfl
      · rw [← inner_conj_symm, hnew b (by omega), map_zero, ite_eq_right (by omega)]
      · rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
          norm_fgmresV_succ (hbreak m (by omega))]
        norm_num

/-- **The flexible Arnoldi basis is orthonormal** as long as the process has not broken down.
This is what makes the quasi-residual of §9.4 the true residual norm, and hence what makes
Proposition 9.2 a genuine optimality statement. -/
theorem orthonormal_fgmresV (hv : ‖v₁‖ = 1) {m : ℕ}
    (hbreak : ∀ j, j < m → fgmresW M A v₁ j ≠ 0) :
    Orthonormal 𝕜 fun i : Fin (m + 1) => fgmresV M A v₁ (i : ℕ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [h0, fgmresV_zero]; exact hv
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      rw [hk]
      exact norm_fgmresV_succ (hbreak k (by omega : k < m))
  · dsimp only
    have h := inner_fgmresV hv m hbreak (i : ℕ) (by omega) (j : ℕ) (by omega)
    rwa [ite_eq_right fun hc => hij (Fin.ext hc)] at h

/-! ### Algorithm 9.6: the iterate -/

/-- **Algorithm 9.6**, line 12: the minimizer `y_m` of `‖β e₁ - H̄_m y‖₂`, computed as in
Algorithm 6.9 by the Givens process, `y_m = R_m⁻¹ g_m`. -/
noncomputable def fgmresY (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Fin m → 𝕜 :=
  (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)⁻¹ *ᵥ
    Chapter06.g (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (Chapter06.β A b x₀ : 𝕜) m

/-- **Algorithm 9.6** (FGMRES), line 12: `x_m = x₀ + Z_m y_m`. The iterate is expanded in the
preconditioned directions `z_j = M_j⁻¹ v_j`, which the flexible algorithm must therefore
store. -/
noncomputable def fgmres (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + ∑ j : Fin m, fgmresY M A b x₀ m j • fgmresZ M A (Chapter06.v₁ A b x₀) (j : ℕ)

/-- `r₀ = β v_0`, the starting relation of the Arnoldi process. -/
private theorem residual_eq_smul_fgmresV (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    b - op A x₀ = (Chapter06.β A b x₀ : 𝕜) • fgmresV M A (Chapter06.v₁ A b x₀) 0 := by
  rw [fgmresV_zero]
  exact (smul_inv_smul_norm (b - op A x₀)).symm

/-- The minimizer computed by the Givens process really minimizes the quasi-residual. -/
private theorem isMinOn_fgmresY (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ}
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    IsMinOn
      (Krylov.quasiResidual (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (Chapter06.β A b x₀ : 𝕜) m)
      Set.univ (fgmresY M A b x₀ m) :=
  (Chapter06.isMinOn_lsq _ _ (fun _ _ hij => fgmresCoeff_eq_zero_of_lt hij) hR).1

/-! ### Propositions 9.2 and 9.3 -/

/-- **Proposition 9.2**, (9.24)–(9.26): the FGMRES iterate `x_m` minimizes the residual norm
`‖b - A x‖₂` over `x₀ + span {z_0, …, z_{m-1}}`.

Unlike GMRES, the space searched is not a Krylov subspace; what makes the minimization work is
only the two-family relation (9.22) together with the orthonormality of `V_{m+1}`. -/
theorem proposition_9_2 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hbreak : ∀ j, j < m → fgmresW M A (Chapter06.v₁ A b x₀) j ≠ 0)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    IsMinRes (op A) b x₀
      (Submodule.span 𝕜 (Set.range fun j : Fin m => fgmresZ M A (Chapter06.v₁ A b x₀) (j : ℕ)))
      (fgmres M A b x₀ m) :=
  Krylov.FGMRES.isMinRes (equation_9_22 M A _) (residual_eq_smul_fgmresV M A b x₀)
    (orthonormal_fgmresV (Chapter06.norm_v₁ A b x₀ hr) hbreak) (isMinOn_fgmresY M A b x₀ hR)

/-- **Proposition 9.3**: if the initial residual is nonzero, the previous steps have not broken
down and the square Hessenberg matrix `H_m` is nonsingular, then the FGMRES iterate is exact
exactly when `h_{m+1,m} = 0`.

The nonsingularity of `H_m` is a genuine extra hypothesis in the flexible case — see
`SaadSparse.Chapter09.hessenbergSq_isUnit_of_linearIndependent` for the book's remark that it is not
vacuous. -/
theorem proposition_9_3 (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hr : Chapter06.r₀ A b x₀ ≠ 0) (hm : 0 < m)
    (hsub : ∀ i, i + 1 < m → fgmresCoeff M A (Chapter06.v₁ A b x₀) (i + 1) i ≠ 0)
    (hH : IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m).det)
    (hbreak : ∀ j, j < m → fgmresW M A (Chapter06.v₁ A b x₀) j ≠ 0)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) m)) :
    op A (fgmres M A b x₀ m) = b ↔ fgmresCoeff M A (Chapter06.v₁ A b x₀) m (m - 1) = 0 :=
  Krylov.FGMRES.apply_eq_iff_coeff_eq_zero (equation_9_22 M A _)
    (residual_eq_smul_fgmresV M A b x₀)
    (by simpa [Chapter06.β] using (RCLike.ofReal_ne_zero (K := 𝕜)).2 (norm_ne_zero_iff.2 hr))
    hm hsub hH (orthonormal_fgmresV (Chapter06.norm_v₁ A b x₀ hr) hbreak)
    (isMinOn_fgmresY M A b x₀ hR)

/-! ### §9.4.1: an exact preconditioning step ends the iteration -/

/-- **§9.4.1**: if the preconditioning is *exact* at step `j`, that is `A z_j = v_j`, then the
orthogonalization of line 5 leaves nothing: `ŵ_j = 0`, and hence `h_{j+1,j} = 0`. The reason is
that `A z_j` is one of the vectors it is being orthogonalized against. -/
theorem fgmresW_eq_zero_of_apply_fgmresZ_eq (hv : ‖v₁‖ = 1) {j : ℕ}
    (hbreak : ∀ i, i < j → fgmresW M A v₁ i ≠ 0)
    (hz : op A (fgmresZ M A v₁ j) = fgmresV M A v₁ j) : fgmresW M A v₁ j = 0 := by
  have hsum : ∑ i ∈ Finset.range (j + 1),
      inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i
        = fgmresV M A v₁ j := by
    have hterm : ∀ i ∈ Finset.range (j + 1),
        inner 𝕜 (fgmresV M A v₁ i) (op A (fgmresZ M A v₁ j)) • fgmresV M A v₁ i
          = if i = j then fgmresV M A v₁ j else 0 := by
      intro i hi
      rw [hz, inner_fgmresV hv j hbreak i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) j le_rfl]
      by_cases hij : i = j
      · rw [ite_eq_left hij, ite_eq_left hij, one_smul, hij]
      · rw [ite_eq_right hij, ite_eq_right hij, zero_smul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (j + 1)) j
      (fun _ => fgmresV M A v₁ j), ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_self j))]
  rw [fgmresW, hsum, hz, sub_self]

/-- **§9.4.1**: an exact inner solve ends the outer iteration. If `A z_j = v_j` at step `j` — the
preconditioner happens to invert `A` on that vector — then, provided the previous steps have not
broken down and the square Hessenberg matrix `H_{j+1}` is nonsingular, the flexible GMRES iterate
`x_{j+1}` already solves `A x = b`.

The book calls this "a consequence of the above proposition", and it is: `h_{j+1,j} = 0` by
`fgmresW_eq_zero_of_apply_fgmresZ_eq`, and a vanishing subdiagonal entry makes the iterate exact
(`Krylov.FGMRES.apply_eq_of_coeff_eq_zero`). It is what makes the flexible framework attractive:
any inner solve good enough to be exact on one vector terminates the outer one. Note that
Proposition 9.3 itself cannot be quoted here, since its orthonormality hypothesis covers
`v_0, …, v_{j+1}` and the vector `v_{j+1}` is exactly the one this step fails to produce. -/
theorem fgmres_eq_of_apply_fgmresZ_eq (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n)) {j : ℕ}
    (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hbreak : ∀ i, i < j → fgmresW M A (Chapter06.v₁ A b x₀) i ≠ 0)
    (hz : op A (fgmresZ M A (Chapter06.v₁ A b x₀) j) = fgmresV M A (Chapter06.v₁ A b x₀) j)
    (hH : IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (j + 1)).det)
    (hR : IsUnit (Chapter06.R (fgmresCoeff M A (Chapter06.v₁ A b x₀)) (j + 1))) :
    op A (fgmres M A b x₀ (j + 1)) = b := by
  have hw := fgmresW_eq_zero_of_apply_fgmresZ_eq (Chapter06.norm_v₁ A b x₀ hr) hbreak hz
  have hzero : fgmresCoeff M A (Chapter06.v₁ A b x₀) (j + 1) (j + 1 - 1) = 0 := by
    rw [Nat.add_sub_cancel, fgmresCoeff_succ_self, hw, norm_zero, RCLike.ofReal_zero]
  exact Krylov.FGMRES.apply_eq_of_coeff_eq_zero (equation_9_22 M A _)
    (residual_eq_smul_fgmresV M A b x₀) (Nat.succ_pos j) hH hzero
    (isMinOn_fgmresY M A b x₀ hR)

/-- **The remark after Proposition 9.3**: if `A` is nonsingular, the directions `z_0, …, z_{m-1}`
are linearly independent and the process has broken down at step `m`, then the square Hessenberg
matrix `H_m` is nonsingular — so the extra hypothesis of Proposition 9.3 is not vacuous.

This is the flexible form of the first part of Proposition 6.9: `A Z_m = V_m H_m` with `A Z_m` of
full rank and `V_m` orthonormal forces `H_m` to have full rank. -/
theorem hessenbergSq_isUnit_of_linearIndependent (M : ℕ → Matrix (Fin n) (Fin n) 𝕜)
    (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hm : 0 < m)
    (hA : IsUnit A) (hz : LinearIndependent 𝕜 fun j : Fin m => fgmresZ M A v₁ (j : ℕ))
    (hlast : fgmresCoeff M A v₁ m (m - 1) = 0) :
    IsUnit (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 fun y w hyw => ?_
  have key : ∀ u : Fin m → 𝕜,
      (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec u = 0 →
        ∀ i : Fin m, u i = 0 := by
    intro u hu
    have hzero : op A (∑ j, u j • fgmresZ M A v₁ (j : ℕ)) = 0 := by
      rw [(equation_9_22 M A v₁).apply_sum m u]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
      · have hi : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.ext heq
        have hrow : (Krylov.hessenbergOf (fgmresCoeff M A v₁) m).mulVec u
            ⟨m, Nat.lt_succ_self m⟩ = 0 := by
          simp only [Matrix.mulVec, dotProduct, Krylov.hessenbergOf, Matrix.of_apply]
          refine Finset.sum_eq_zero fun k _ => ?_
          rcases eq_or_ne (k : ℕ) (m - 1) with hk | hk
          · rw [hk, hlast, zero_mul]
          · rw [fgmresCoeff_eq_zero_of_lt (by omega : (k : ℕ) + 1 < m), zero_mul]
        rw [hi, hrow, zero_smul]
      · have hrow : (Krylov.hessenbergOf (fgmresCoeff M A v₁) m).mulVec u i
            = (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec u ⟨(i : ℕ), hlt⟩ := by
          simp only [Matrix.mulVec, dotProduct, Krylov.hessenbergOf, Krylov.hessenbergSqOf,
            Matrix.of_apply]
        rw [hrow, hu, Pi.zero_apply, zero_smul]
    have hinj := Chapter06.injective_op_of_isUnit hA
    have h0 : ∑ j, u j • fgmresZ M A v₁ (j : ℕ) = 0 := by
      have := hinj (by rw [hzero, map_zero] : op A (∑ j, u j • fgmresZ M A v₁ (j : ℕ)) = op A 0)
      exact this
    exact fun i => Fintype.linearIndependent_iff.1 hz u h0 i
  have hsub : (Krylov.hessenbergSqOf (fgmresCoeff M A v₁) m).mulVec (y - w) = 0 := by
    rw [Matrix.mulVec_sub, hyw, sub_self]
  funext i
  have := key (y - w) hsub i
  simpa [sub_eq_zero] using this

/-! ### A constant preconditioner gives back Algorithm 9.5 -/

section Const

variable (M A : Matrix (Fin n) (Fin n) 𝕜)

/-- `A M⁻¹` acts as `A` after `M⁻¹`. -/
private theorem op_rightPreconditioned_apply (x : EuclideanSpace 𝕜 (Fin n)) :
    op (rightPreconditioned M A) x = op A (op M⁻¹ x) := op_mul_apply A M⁻¹ x

/-- With a constant preconditioner, the flexible Arnoldi basis is the Arnoldi basis of
`A M⁻¹`. -/
private theorem fgmresV_const (u : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    fgmresV (fun _ => M) A u j = Chapter06.arnoldiCGS (rightPreconditioned M A) u j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [fgmresV_zero, Chapter06.arnoldiCGS_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hlt : ∀ i, i ≤ k →
          fgmresV (fun _ => M) A u i = Chapter06.arnoldiCGS (rightPreconditioned M A) u i :=
        fun i hi => ih i (by omega)
      have hAz : op A (op M⁻¹ (fgmresV (fun _ => M) A u k))
          = op (rightPreconditioned M A) (Chapter06.arnoldiCGS (rightPreconditioned M A) u k) := by
        rw [hlt k le_rfl, op_rightPreconditioned_apply]
      have hW : fgmresW (fun _ => M) A u k
          = Chapter06.arnoldiW (rightPreconditioned M A) u k := by
        simp only [fgmresW, fgmresZ, Chapter06.arnoldiW, Chapter06.arnoldiCoeff]
        rw [hAz]
        congr 1
        exact Finset.sum_congr rfl fun i hi =>
          by rw [hlt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
      rw [fgmresV_succ, Chapter06.arnoldiCGS_succ, hW]

/-- With a constant preconditioner, the unnormalized vectors agree with those of Algorithm 6.1
applied to `A M⁻¹`. -/
private theorem fgmresW_const (u : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    fgmresW (fun _ => M) A u k = Chapter06.arnoldiW (rightPreconditioned M A) u k := by
  have hAz : op A (op M⁻¹ (fgmresV (fun _ => M) A u k))
      = op (rightPreconditioned M A) (Chapter06.arnoldiCGS (rightPreconditioned M A) u k) := by
    rw [fgmresV_const, op_rightPreconditioned_apply]
  simp only [fgmresW, fgmresZ, Chapter06.arnoldiW, Chapter06.arnoldiCoeff]
  rw [hAz]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [fgmresV_const]

/-- With a constant preconditioner, the Hessenberg coefficients agree with those of Algorithm 6.1
applied to `A M⁻¹`. -/
private theorem fgmresCoeff_const {u : EuclideanSpace 𝕜 (Fin n)} (hu : ‖u‖ = 1) :
    fgmresCoeff (fun _ => M) A u = Chapter06.arnoldiCoeff (rightPreconditioned M A) u := by
  funext i j
  rcases lt_trichotomy i (j + 1) with h | rfl | h
  · rw [fgmresCoeff_of_le (by omega), fgmresZ]
    simp only [fgmresV_const]
    rw [← op_rightPreconditioned_apply]
    rfl
  · rw [fgmresCoeff_succ_self, fgmresW_const, Chapter06.arnoldiCoeff_succ_self _ _ hu]
  · rw [fgmresCoeff_eq_zero_of_lt h, Chapter06.arnoldiCoeff_eq_zero_of_lt _ _ hu h]

/-- **A constant preconditioner gives back Algorithm 9.5**: FGMRES run with `M_j = M` at every
step produces the iterates of GMRES with right preconditioning, so the flexible algorithm is a
genuine generalization and nothing more. -/
theorem fgmres_eq_gmresRight (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (hM : IsUnit M)
    (hr : Chapter06.r₀ A b x₀ ≠ 0) :
    fgmres (fun _ => M) A b x₀ m = gmresRight M A b x₀ m := by
  have hMM : ∀ x : EuclideanSpace 𝕜 (Fin n), op M⁻¹ (op M x) = x := by
    intro x
    have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
    rw [← op_mul_apply, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), h1,
      LinearMap.id_apply]
  have hr0 : Chapter06.r₀ (rightPreconditioned M A) b (op M x₀) = Chapter06.r₀ A b x₀ := by
    rw [Chapter06.r₀_def, Chapter06.r₀_def, op_rightPreconditioned_apply, hMM]
  have hbetaR : Chapter06.β (rightPreconditioned M A) b (op M x₀) = Chapter06.β A b x₀ :=
    congrArg norm hr0
  have hv1 : Chapter06.v₁ (rightPreconditioned M A) b (op M x₀) = Chapter06.v₁ A b x₀ := by
    have e1 : Chapter06.v₁ (rightPreconditioned M A) b (op M x₀)
        = (‖Chapter06.r₀ (rightPreconditioned M A) b (op M x₀)‖ : 𝕜) ⁻¹ •
            Chapter06.r₀ (rightPreconditioned M A) b (op M x₀) := rfl
    have e2 : Chapter06.v₁ A b x₀ = (‖Chapter06.r₀ A b x₀‖ : 𝕜)⁻¹ • Chapter06.r₀ A b x₀ := rfl
    rw [e1, e2, hr0]
  have hcoeff : fgmresCoeff (fun _ => M) A (Chapter06.v₁ A b x₀)
      = Chapter06.arnoldiCoeff (rightPreconditioned M A) (Chapter06.v₁ A b x₀) :=
    fgmresCoeff_const M A (Chapter06.norm_v₁ A b x₀ hr)
  have hy : fgmresY (fun _ => M) A b x₀ m
      = Chapter06.gmresY (rightPreconditioned M A) b (op M x₀) m := by
    rw [fgmresY, Chapter06.gmresY, hv1, hcoeff, hbetaR]
  have hvec : ∀ j : ℕ, fgmresZ (fun _ => M) A (Chapter06.v₁ A b x₀) j
      = op M⁻¹ (Arnoldi.vec (op (rightPreconditioned M A))
          (Chapter06.r₀ (rightPreconditioned M A) b (op M x₀)) j) := by
    intro j
    rw [fgmresZ, fgmresV_const, ← Chapter06.arnoldiCGS_v₁_apply, hv1]
  rw [fgmres, gmresRight, Chapter06.gmresFixed, Chapter06.krylovIterate_eq_sum, add_sub_cancel_left,
    map_sum, hy]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hvec, map_smul]

end Const

/-! ### §9.4.2: flexible DQGMRES -/

/-- **§9.4.2**, (9.28): flexible DQGMRES — Algorithm 6.13 fed the preconditioned vectors
`M_j⁻¹ v_j` in place of the `v_j` in the direction update
`p_j = (M_j⁻¹ v_j - ∑_{i=j-k+1}^{j-1} r_{ij} p_i)/r_{jj}`, so that the preconditioned vector is
consumed at once and need not be stored.

The book states nothing about it beyond the algorithm; the identification with Algorithm 6.13 at
`M_j = I` is `SaadSparse.Chapter09.fdqgmres_eq_dqgmres`. -/
noncomputable def fdqgmres (M : ℕ → Matrix (Fin n) (Fin n) 𝕜) (x₀ : EuclideanSpace 𝕜 (Fin n))
    (v : ℕ → EuclideanSpace 𝕜 (Fin n)) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    ℕ → EuclideanSpace 𝕜 (Fin n) :=
  Chapter06.dqgmres x₀ (fun j => op (M j)⁻¹ (v j)) h β k

/-- With the identity preconditioner at every step, flexible DQGMRES is Algorithm 6.13. -/
theorem fdqgmres_eq_dqgmres (x₀ : EuclideanSpace 𝕜 (Fin n)) (v : ℕ → EuclideanSpace 𝕜 (Fin n))
    (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    fdqgmres (fun _ => (1 : Matrix (Fin n) (Fin n) 𝕜)) x₀ v h β k
      = Chapter06.dqgmres x₀ v h β k := by
  have hv : (fun j => op ((1 : Matrix (Fin n) (Fin n) 𝕜))⁻¹ (v j)) = v := by
    funext j
    have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
    rw [_root_.inv_one, h1, LinearMap.id_apply]
  rw [fdqgmres, hv]

end SaadSparse.Chapter09
