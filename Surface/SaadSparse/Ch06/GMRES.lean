import SaadSparse.Ch06.Givens
import SaadSparse.Ch06.Residual

/-!
# Saad, §6.5.1–6.5.5: GMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.5.1–6.5.5.

The data of the system — `r₀ = b - A x₀`, `β = ‖r₀‖₂`, `v₁ = r₀/β`, the first coordinate vector
`e₁`, and `mEff`, which implements the book's "if `h_{j+1,j} = 0` set `m := j`" — are shared
with `Ch06/FOM.lean` and live in `Ch06/Residual.lean`. The
element `x = x₀ + V_m y` of (6.25) is `krylovIterate`, the least-squares function `J(y)` of
(6.26)/(6.28) is `J`, and Algorithm 6.9 line 12 ("compute `y_m` the minimizer") is the relation
`IsGMRESIterate`. `gmresY = R_m⁻¹ g_m` is the minimizer as §6.5.3 computes it (Proposition
6.9(2)), `gmresFixed` the resulting iterate, `gmres` Algorithm 6.9 with the "set `m := j`" rule,
and `gmresRestarted` is Algorithm 6.11, GMRES(m). Algorithm 6.10 (Householder GMRES) is
`gmresHH`, built on the Householder Arnoldi basis of `Ch06/Arnoldi.lean` with the accumulation
`hornerAccumulate` of (6.31)–(6.33); `gmresHH_eq` is the statement that it computes the same
approximation as Algorithm 6.9.

**The hinge of the file is `isGMRESIterate_iff`** (6.29)–(6.30): the GMRES approximation, defined
by the least-squares problem in Hessenberg coordinates, *is* the backbone's minimal-residual
Krylov iterate `Krylov.IsMinResIterate` on `𝒦_m(A, r₀)`. Everything else — Proposition 6.9(2),
(6.41), (6.42), Proposition 6.10, the "at most `n` steps" remark — is a specialization of a
backbone theorem through that equivalence, the Givens layer of `Ch06/Givens.lean`, and the
bridge family `arnoldiCGS_v₁`, `arnoldiCoeff_v₁`, `Hbar_v₁`, `grade_v₁` of
`Ch06/Residual.lean` (the backbone indexes the Arnoldi data by `r₀`, the book by `v₁`).

Definitions are polymorphic in `𝕜`, so §6.5.9 (complex GMRES) is the same code; the numbered
results are stated over `ℝ`, the book's generality in §6.5.

Proposition 6.9 and Proposition 6.10 belong to §6.5.3–6.5.4, which the plan's file table assigns
to `Ch06/Givens.lean`; they are here because they are statements about GMRES itself, while
`Ch06/Givens.lean` holds the rotation algebra they use.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-! ### (6.25)–(6.28) -/

/-- (6.25): the general element `x = x_0 + V_m y` of `x_0 + 𝒦_m(A, r_0)`. -/
noncomputable def krylovIterate (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ)
    (y : Fin m → 𝕜) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m) (WithLp.toLp 2 y)

/-- `x_0 + V_m y = x_0 + ∑_j y_j v_j`, the form the backbone uses. -/
theorem krylovIterate_eq_sum {m : ℕ} (y : Fin m → 𝕜) :
    krylovIterate A b x₀ m y = x₀ + ∑ j, y j • Arnoldi.vec (op A) (r₀ A b x₀) (j : ℕ) := by
  rw [krylovIterate, toEuclideanLin_V_apply]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [arnoldiCGS_v₁_apply])

/-- (6.26)/(6.28): the function `J(y) = ‖β e_1 - H̄_m y‖₂` minimized by GMRES. -/
noncomputable def J (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

theorem J_eq (m : ℕ) :
    J A b x₀ m = fun y : Fin m → 𝕜 =>
      ‖(WithLp.toLp 2 (Krylov.firstVec (‖r₀ A b x₀‖ : 𝕜) (m + 1) -
        Arnoldi.hessenberg (op A) (r₀ A b x₀) m *ᵥ y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  funext y
  rw [J, smul_e₁_eq_firstVec, Hbar_v₁, β_eq_norm_r₀]

/-- (6.27): `b - A(x_0 + V_m y) = V_{m+1}(β e_1 - H̄_m y)`. -/
theorem eq_6_27 {m : ℕ} (y : Fin m → 𝕜) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) := by
  rw [krylovIterate_eq_sum, toEuclideanLin_V_apply, smul_e₁_eq_firstVec, Hbar_v₁, β_eq_norm_r₀,
    Arnoldi.hessenberg_eq,
    (Arnoldi.hessenbergRelation (op A) (r₀ A b x₀)).residual_eq
      (Arnoldi.smul_vec_zero (op A) (r₀ A b x₀)).symm m y]
  exact Finset.sum_congr rfl fun j _ => by rw [arnoldiCGS_v₁_apply]

/-- (6.28): `‖b - A(x_0 + V_m y)‖₂ = J(y)`, for as many steps as Arnoldi can take. -/
theorem eq_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → 𝕜) :
    ‖b - op A (krylovIterate A b x₀ m y)‖ = J A b x₀ m y := by
  rw [krylovIterate_eq_sum, J_eq]
  exact Krylov.norm_residual_eq_norm_firstVec_sub_mulVec (by rwa [← grade_v₁]) y

/-! ### (6.29)–(6.30): Algorithm 6.9 and the minimal-residual specification -/

/-- **Algorithm 6.9** (GMRES), line 12: `x` is a GMRES approximation at step `m` when
`x = x_0 + V_m y_m` for a minimizer `y_m` of `J` (6.29)–(6.30). -/
def IsGMRESIterate (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) (x : 𝔼) : Prop :=
  ∃ y : Fin m → 𝕜, IsMinOn (J A b x₀ m) Set.univ y ∧ x = krylovIterate A b x₀ m y

/-- **(6.29)–(6.30)**: the GMRES approximation is exactly the minimal-residual Krylov iterate on
`𝒦_m(A, r_0)`; this is the identification from which the rest of §6.5 follows. -/
theorem isGMRESIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) {x : 𝔼} :
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResIterate (op A) b x₀ m x := by
  have hm' : m ≤ Krylov.grade (op A) (r₀ A b x₀) := by rwa [← grade_v₁]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [krylovIterate_eq_sum]
    exact (Krylov.isMinResIterate_iff_isMinOn hm' y).2 (by rwa [J_eq] at hy)
  · intro hx
    obtain ⟨y, -, hxe⟩ := hx.exists_mulVec_rotated_eq hm'
    refine ⟨y, ?_, by rw [krylovIterate_eq_sum]; exact hxe⟩
    rw [J_eq]
    exact (Krylov.isMinResIterate_iff_isMinOn hm' y).1 (by rwa [← hxe])

/-- The GMRES approximation exists at every step. -/
theorem exists_isGMRESIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) :
    ∃ x, IsGMRESIterate A b x₀ m x := by
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResIterate (op A) b x₀ m
  exact ⟨x, (isGMRESIterate_iff A b x₀ hm).2 hx⟩

/-- `A` nonsingular makes `x ↦ A x` injective. -/
theorem injective_op_of_isUnit {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A) :
    Function.Injective (op A) := by
  obtain ⟨u, hu⟩ := hA
  have h1 : op (↑u⁻¹ : Matrix (Fin n) (Fin n) 𝕜) ∘ₗ op A = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_mul, ← hu, ← Units.val_mul]
    simp
  exact Function.LeftInverse.injective (g := op (↑u⁻¹ : Matrix (Fin n) (Fin n) 𝕜))
    fun y => by rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]

/-- **(6.29)–(6.30)**, uniqueness: for nonsingular `A` the GMRES approximation is the unique
vector of `x_0 + 𝒦_m` minimizing (6.26). -/
theorem existsUnique_isGMRESIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    ∃! x, IsGMRESIterate A b x₀ m x := by
  obtain ⟨x, hx, huniq⟩ :=
    Krylov.existsUnique_isMinResIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  exact ⟨x, (isGMRESIterate_iff A b x₀ hm).2 hx,
    fun z hz => huniq z ((isGMRESIterate_iff A b x₀ hm).1 hz)⟩

/-! ### §6.5.3: the minimizer `y_m = R_m⁻¹ g_m` and Algorithm 6.9 -/

/-- Proposition 6.9(2): the minimizer of `J` computed by the Givens process, `y_m = R_m⁻¹ g_m`
(line 12 of Algorithm 6.9 in its practical form). -/
noncomputable def gmresY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Fin m → 𝕜 :=
  (R (arnoldiCoeff A (v₁ A b x₀)) m)⁻¹ *ᵥ g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m

/-- **Algorithm 6.9** (GMRES) run for exactly `m` Arnoldi steps: `x_m = x_0 + V_m y_m`. -/
noncomputable def gmresFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  krylovIterate A b x₀ m (gmresY A b x₀ m)

/-- **Algorithm 6.9** (GMRES), with the book's rule "if `h_{j+1,j} = 0` set `m := j`". -/
noncomputable def gmres (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  gmresFixed A b x₀ (mEff A b x₀ m)

/-- One cycle of **Algorithm 6.11** (GMRES(m)). -/
noncomputable def gmresCycle (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼) : 𝔼 :=
  gmres A b x₀ m

/-- **Algorithm 6.11** (GMRES(m)): `k` restart cycles started from `x_0`. -/
noncomputable def gmresRestarted (A : Matrix (Fin n) (Fin n) 𝕜) (b : 𝔼) (m : ℕ) (x₀ : 𝔼)
    (k : ℕ) : 𝔼 :=
  (gmresCycle A b m)^[k] x₀

theorem J_nonneg {m : ℕ} (y : Fin m → 𝕜) : 0 ≤ J A b x₀ m y := norm_nonneg _

/-- The Hessenberg structure of the GMRES coefficients, packaged for the Givens lemmas. -/
private theorem hessenberg_coeffs :
    ∀ i j : ℕ, j + 1 < i → arnoldiCoeff A (v₁ A b x₀) i j = 0 :=
  fun _ _ hij => arnoldiCoeff_v₁_eq_zero_of_lt A b x₀ hij

/-- (6.43) for GMRES: `J(y)² = |γ_{m+1}|² + ‖g_m - R_m y‖₂²`. -/
theorem sq_J_eq {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) k ≠ 0) (y : Fin m → 𝕜) :
    J A b x₀ m y ^ 2 = ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ ^ 2 +
      ‖(WithLp.toLp 2 (g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m -
        R (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 := by
  rw [J, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf]
  exact norm_sq_firstVec_sub_mulVec _ _ (hessenberg_coeffs A b x₀) hρ y

/-- `J` is the least-squares function `lsq` of `Ch06/Givens.lean` at the Arnoldi coefficients. -/
theorem J_eq_lsq (m : ℕ) : J A b x₀ m = lsq (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m := by
  funext y
  rw [J, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf, lsq]

/-- The Givens system `R_m y_m = g_m` solved by `gmresY`. -/
theorem mulVec_R_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    R (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m =
      g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m :=
  mulVec_R_inv_mulVec_g _ _ hR

/-- **Proposition 6.9(2)**: `y_m = R_m⁻¹ g_m` is the minimizer of `J`, and it is the only one. -/
theorem prop_6_9_2 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
      ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m := by
  rw [J_eq_lsq]
  exact isMinOn_lsq _ _ (hessenberg_coeffs A b x₀) hR

/-- Algorithm 6.9 computes a GMRES approximation. -/
theorem gmresFixed_isGMRESIterate {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsGMRESIterate A b x₀ m (gmresFixed A b x₀ m) :=
  ⟨gmresY A b x₀ m, (prop_6_9_2 A b x₀ hR).1, rfl⟩

/-- Algorithm 6.9 computes the minimal-residual Krylov iterate. -/
theorem gmresFixed_isMinResIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    Krylov.IsMinResIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
  (isGMRESIterate_iff A b x₀ hm).1 (gmresFixed_isGMRESIterate A b x₀ hR)

/-! ### Proposition 6.9(1), (6.41), (6.42) -/

/-- **Proposition 6.9(1)**, in the direction the book uses: for nonsingular `A` no rotation
degenerates in the first `μ` steps, so `R_m` is nonsingular. Contrapositive: a vanishing
diagonal entry `r_{mm}` of `R_m` forces `A` to be singular.

Below the grade this is `Krylov.givensRho_arnoldi_ne_zero`; at the grade itself the argument is
the book's — a nonsingular `A` is a bijection of the invariant subspace `𝒦_μ`, so the Galerkin
iterate at step `μ` exists and is unique, `H_μ` is nonsingular, and `c_{μ-1} ≠ 0`. -/
theorem isUnit_R_of_isUnit {m : ℕ} (hA : IsUnit A) (hm : m ≤ grade A (v₁ A b x₀)) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  have hinj : Function.Injective (op A) := injective_op_of_isUnit hA
  have hm' : m ≤ Krylov.grade (op A) (r₀ A b x₀) := by rwa [← grade_v₁]
  refine (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).2 fun k hk => ?_
  rw [arnoldiCoeff_v₁]
  rcases lt_or_ge (k + 1) (Krylov.grade (op A) (r₀ A b x₀)) with h1 | h1
  · exact Krylov.givensRho_arnoldi_ne_zero h1
  · have hgal : ∃! x, Krylov.IsGalerkinIterate (op A) b x₀ (k + 1) x := by
      obtain ⟨x, hx⟩ := Krylov.exists_isMinResIterate (op A) b x₀ (k + 1)
      have hAx : op A x = b := hx.apply_eq_of_grade_le h1 hinj.injOn
      refine ⟨x, ⟨hx.mem, ?_⟩, fun z hz => hinj ?_⟩
      · rw [hAx, sub_self]
        exact Submodule.zero_mem _
      · rw [hAx, hz.apply_eq_of_grade_le h1]
    have hU : IsUnit (Arnoldi.hessenbergSq (op A) (r₀ A b x₀) (k + 1)) :=
      (Krylov.existsUnique_isGalerkinIterate_iff_isUnit (le_trans hk hm')).1 hgal
    have hc := (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (le_trans hk hm')).1 hU
    exact Krylov.givensRho_ne_zero_of_rotated_ne_zero _
      fun h0 => hc ((Krylov.givensC_eq_zero_iff _ k).2 h0)

/-- **(6.41)**: `b - A x_m = V_{m+1} Q_mᴴ (γ_{m+1} e_{m+1})`. -/
theorem eq_6_41 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    b - op A (gmresFixed A b x₀ m) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ *ᵥ
          Pi.single (Fin.last m) (γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m))) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  have hQ := Qrot_mem_unitaryGroup (arnoldiCoeff A (v₁ A b x₀)) m hρ
  have h1 : (Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ * Qrot (arnoldiCoeff A (v₁ A b x₀)) m = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := Qrot (arnoldiCoeff A (v₁ A b x₀)) m)).1 hQ
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [gmresFixed, eq_6_27, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf]
  congr 2
  conv_lhs => rw [← Matrix.one_mulVec (Krylov.firstVec (β A b x₀ : 𝕜) (m + 1) -
    Krylov.hessenbergOf (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m), ← h1]
  rw [← Matrix.mulVec_mulVec, Qrot_mulVec_firstVec_sub,
    gbar_sub_Rbar_mulVec _ _ (hessenberg_coeffs A b x₀) (mulVec_R_gmresY A b x₀ hR)]

/-- **(6.42)**: `‖b - A x_m‖₂ = |γ_{m+1}|`, the residual norm read off the rotated right-hand
side. -/
theorem eq_6_42 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ =
      ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  rw [arnoldiCoeff_v₁] at hρ ⊢
  exact Krylov.IsMinResIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero
    (by rwa [← grade_v₁]) hρ (gmresFixed_isMinResIterate A b x₀ hm hR)

/-- (6.47) and (6.42): if `s_{m+1} = 0` the GMRES approximation at step `m+1` is exact. -/
theorem apply_eq_of_s_eq_zero {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1)))
    (hs : s (arnoldiCoeff A (v₁ A b x₀)) m = 0) : op A (gmresFixed A b x₀ (m + 1)) = b := by
  have h1 := eq_6_42 A b x₀ hm hR
  rw [gamma_succ, hs, neg_zero, zero_mul, norm_zero] at h1
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h1.le)).symm

/-! ### P-6.5: GMRES from Saad (5.7) -/

/-- **P-6.5**: the GMRES coordinates satisfy the normal equations
`H̄_mᴴ H̄_m y_m = H̄_mᴴ (β e_1)` of the least-squares problem (6.29) — the Petrov-Galerkin
formula Saad (5.7) with `V = V_m` and `W = A V_m`. -/
theorem normalEquations_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) *ᵥ gmresY A b x₀ m
      = (Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1)) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  rw [Hbar_eq_hessenbergOf, smul_e₁_eq_firstVec]
  exact normalEquations _ _ (hessenberg_coeffs A b x₀) hρ (mulVec_R_gmresY A b x₀ hR)

/-- **P-6.5**: `y_m = (H̄_mᴴ H̄_m)⁻¹ H̄_mᴴ (β e_1)`. -/
theorem p_6_5 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1))) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  have hN : IsUnit ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) := by
    rw [Hbar_eq_hessenbergOf]
    exact isUnit_conjTranspose_mul_self_hessenbergOf _ (hessenberg_coeffs A b x₀) hρ hR
  rw [← normalEquations_gmresY A b x₀ hR, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hN), Matrix.one_mulVec]

/-! ### Proposition 6.10 and the "at most `n` steps" remark -/

/-- **Proposition 6.10**: for nonsingular `A`, GMRES breaks down at step `j` — that is,
`h_{j+1,j} = 0` — exactly when the approximation `x_j` is already exact. -/
theorem prop_6_10 (hA : IsUnit A) {j : ℕ} (hj : 0 < j) (hjg : j ≤ grade A (v₁ A b x₀)) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b := by
  have hj1 : j - 1 + 1 = j := by omega
  have hbd : arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔
      Krylov.grade (op A) (r₀ A b x₀) ≤ j := by
    rw [arnoldiCoeff_v₁, ← hj1]
    exact Arnoldi.coeff_succ_self_eq_zero_iff (op A) (r₀ A b x₀) (j - 1)
  have hx := gmresFixed_isMinResIterate A b x₀ hjg (isUnit_R_of_isUnit A b x₀ hA hjg)
  rw [hbd]
  refine ⟨fun hg => hx.apply_eq_of_grade_le hg (injective_op_of_isUnit hA).injOn, fun hex => ?_⟩
  exact Krylov.grade_le_of_apply_eq hx.mem hex

/-- §6.5.5: full GMRES converges in at most `n` steps for a nonsingular `A`. -/
theorem gmres_apply_eq (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) : op A (gmres A b x₀ m) = b := by
  have hg : grade A (v₁ A b x₀) ≤ n := grade_le_card A _
  have hmEff : mEff A b x₀ m = grade A (v₁ A b x₀) := min_eq_right (le_trans hg hmn)
  rw [gmres, hmEff]
  exact (gmresFixed_isMinResIterate A b x₀ le_rfl
    (isUnit_R_of_isUnit A b x₀ hA le_rfl)).apply_eq_of_grade_le (by rw [← grade_v₁])
    (injective_op_of_isUnit hA).injOn

/-- §6.5.5: some step `m ≤ n` of full GMRES is exact. -/
theorem exists_gmres_apply_eq (hA : IsUnit A) : ∃ m ≤ n, op A (gmres A b x₀ m) = b :=
  ⟨n, le_rfl, gmres_apply_eq A b x₀ hA le_rfl⟩

end General

/-! ### Algorithm 6.10: Householder GMRES (§6.5.2) -/

section Householder

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- (6.31)–(6.33): the accumulation `z := 0; z := P_j(η_j e_j + z)` of Algorithm 6.10, run for
`l` steps from index `j`; the book's loop `j = m, m-1, …, 1` is `hornerAccumulate P η 0 m`. -/
noncomputable def hornerAccumulate (P : ℕ → (𝔼 →ₗ[ℝ] 𝔼)) (η : ℕ → ℝ) : ℕ → ℕ → 𝔼
  | _, 0 => 0
  | j, l + 1 => P j (η j • stdVec j + hornerAccumulate P η (j + 1) l)

variable (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- The inner loop of (6.31)–(6.33), started at `j + 1` and closed off by `Q_jᵀ`, is the partial
sum `∑ η_i v_i` over the Householder Arnoldi vectors. -/
private theorem QhhT_hornerAccumulate (v : 𝔼) (η : ℕ → ℝ) :
    ∀ (l j : ℕ), QhhT A v j (hornerAccumulate (fun i => householder (hhW A v i)) η (j + 1) l)
      = ∑ i ∈ Finset.range l, η (j + 1 + i) • hhV A v (j + 1 + i) := by
  intro l
  induction l with
  | zero => intro j; simp [hornerAccumulate]
  | succ l ih =>
      intro j
      rw [hornerAccumulate, ← LinearMap.comp_apply, ← QhhT_succ, map_add, map_smul, ih (j + 1),
        Finset.sum_range_succ']
      have hs : ∑ i ∈ Finset.range l, η (j + 1 + (i + 1)) • hhV A v (j + 1 + (i + 1))
          = ∑ i ∈ Finset.range l, η (j + 1 + 1 + i) • hhV A v (j + 1 + 1 + i) :=
        Finset.sum_congr rfl fun i _ => by rw [show j + 1 + (i + 1) = j + 1 + 1 + i by omega]
      rw [hs]
      exact add_comm _ _

/-- (6.31)–(6.33): the accumulation of Algorithm 6.10 computes `∑_{j<m} η_j v_j` in the
Householder Arnoldi basis. -/
theorem hornerAccumulate_eq_sum (v : 𝔼) (η : ℕ → ℝ) (m : ℕ) :
    hornerAccumulate (fun i => householder (hhW A v i)) η 0 m
      = ∑ i ∈ Finset.range m, η i • hhV A v i := by
  cases m with
  | zero => simp [hornerAccumulate]
  | succ l =>
      rw [hornerAccumulate]
      have h0 : (householder (hhW A v 0) : 𝔼 →ₗ[ℝ] 𝔼) = QhhT A v 0 := (QhhT_zero A v).symm
      rw [h0, map_add, map_smul, QhhT_hornerAccumulate A v η l 0, Finset.sum_range_succ']
      have hs : ∑ i ∈ Finset.range l, η (0 + 1 + i) • hhV A v (0 + 1 + i)
          = ∑ i ∈ Finset.range l, η (i + 1) • hhV A v (i + 1) :=
        Finset.sum_congr rfl fun i _ => by rw [show 0 + 1 + i = i + 1 by omega]
      rw [hs]
      exact add_comm _ _

/-- **Algorithm 6.10**, line 1: the scalar `β = e_1ᵀ h_0`. -/
noncomputable def βHH (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) : ℝ :=
  coordAt (hhH A (r₀ A b x₀) 0) 0

/-- §6.5.2: the Householder scalar `β` is minus the `β` of Saad (1.25). -/
theorem βHH_eq (hn : 0 < n) : βHH A b x₀ = -householderBeta (r₀ A b x₀) 0 := by
  rw [βHH, hhH_zero, coordAt, dite_eq_left hn]
  simp [stdVec_coord]

/-- §6.5.2: the Householder scalar `β` is `±‖r_0‖₂`. -/
theorem abs_βHH (hn : 0 < n) : |βHH A b x₀| = ‖r₀ A b x₀‖ := by
  rw [βHH_eq A b x₀ hn, abs_neg, abs_householderBeta_zero]

/-- `r_0 = β v_1` for the Householder basis, the hypothesis of the Hessenberg residual
formula. -/
theorem βHH_smul_hhV_zero (hn : 0 < n) :
    b - op A x₀ = βHH A b x₀ • hhV A (r₀ A b x₀) 0 := by
  rw [βHH_eq A b x₀ hn]
  exact (smul_hhV_zero A (r₀ A b x₀)).symm

/-- Norms of expansions in an orthonormal family are Euclidean norms of the coefficients. -/
private theorem norm_sum_smul_of_orthonormal {N : ℕ} {e : Fin N → 𝔼} (he : Orthonormal ℝ e)
    (cc : Fin N → ℝ) :
    ‖∑ i, cc i • e i‖ = ‖(WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N))‖ := by
  have h1 : ‖∑ i, cc i • e i‖ ^ 2 = ∑ i, ‖cc i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, he.inner_sum cc cc Finset.univ]
    exact Finset.sum_congr rfl fun i _ => by
      simp [Real.norm_eq_abs, sq]
  have h2 : ‖(WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N))‖ ^ 2 = ∑ i, ‖cc i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  nlinarith [norm_nonneg (∑ i, cc i • e i),
    norm_nonneg (WithLp.toLp 2 cc : EuclideanSpace ℝ (Fin N)), h1, h2]

/-- §6.5.2: the residual norm of `x_0 + V^{HH}_m y` is `‖β e_1 - H̄^{HH}_m y‖₂` — the same
least-squares problem as (6.28), with the Householder data. -/
theorem norm_residual_hh {m : ℕ} (hn : m + 1 ≤ n) (y : Fin m → ℝ) :
    ‖b - op A (x₀ + ∑ j : Fin m, y j • hhV A (r₀ A b x₀) (j : ℕ))‖
      = lsq (hhCoeff A (r₀ A b x₀)) (βHH A b x₀) m y := by
  have hn0 : 0 < n := by omega
  rw [(hh_hessenbergRelation A (r₀ A b x₀)).residual_eq (βHH_smul_hhV_zero A b x₀ hn0) m y,
    norm_sum_smul_of_orthonormal (hh_orthonormal A (r₀ A b x₀) hn), lsq]

/-- **Algorithm 6.10** (Householder GMRES), line 12: the minimizer `y_m = R_m⁻¹ g_m` of the
Householder least-squares problem. -/
noncomputable def gmresHHY (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) (m : ℕ) : Fin m → ℝ :=
  (R (hhCoeff A (r₀ A b x₀)) m)⁻¹ *ᵥ g (hhCoeff A (r₀ A b x₀)) (βHH A b x₀) m

/-- **Algorithm 6.10** (Householder GMRES): `x_m = x_0 + z`, with `z` accumulated by
(6.31)–(6.33). -/
noncomputable def gmresHH (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  x₀ + hornerAccumulate (fun i => householder (hhW A (r₀ A b x₀) i))
    (fun i => if h : i < m then gmresHHY A b x₀ m ⟨i, h⟩ else 0) 0 m

theorem gmresHH_eq_add_sum (m : ℕ) :
    gmresHH A b x₀ m = x₀ + ∑ j : Fin m, gmresHHY A b x₀ m j • hhV A (r₀ A b x₀) (j : ℕ) := by
  rw [gmresHH, hornerAccumulate_eq_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun i => (if h : i < m then gmresHHY A b x₀ m ⟨i, h⟩ else 0) •
        hhV A (r₀ A b x₀) i) m]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [dite_eq_left j.isLt]

/-- §6.5.2: Algorithm 6.10 computes the minimal-residual Krylov iterate — the same vector as
Algorithm 6.9. The Householder basis spans the same Krylov flag and is orthonormal, so the
least-squares problem it solves is the same one, in another orthonormal basis. -/
theorem gmresHH_isMinResIterate {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (r₀ A b x₀))
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    Krylov.IsMinResIterate (op A) b x₀ m (gmresHH A b x₀ m) := by
  have hrange : (Set.range fun i : Fin m => hhV A (r₀ A b x₀) (i : ℕ))
      = hhV A (r₀ A b x₀) '' Set.Iio m := by
    ext w
    simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
    tauto
  have hspan : Submodule.span ℝ (Set.range fun i : Fin m => hhV A (r₀ A b x₀) (i : ℕ))
      = Krylov.subspace (op A) (r₀ A b x₀) m := by
    rw [hrange, span_hhV_eq A _ (by omega) hm, krylov_eq]
  have hmin := (isMinOn_lsq (hhCoeff A (r₀ A b x₀)) (βHH A b x₀)
    (fun i j hij => hhCoeff_eq_zero_of_lt A _ hij) hR).1
  refine ⟨?_, fun w hw => ?_⟩
  · rw [gmresHH_eq_add_sum, add_sub_cancel_left, ← hspan]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [← hspan] at hw
    obtain ⟨zz, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
    have hwe : w = x₀ + ∑ j : Fin m, zz j • hhV A (r₀ A b x₀) (j : ℕ) := by
      rw [hz]
      abel
    rw [gmresHH_eq_add_sum, hwe, norm_residual_hh A b x₀ hn, norm_residual_hh A b x₀ hn]
    exact isMinOn_iff.1 hmin zz (Set.mem_univ zz)

/-- §6.5.2: **Algorithm 6.10 computes the GMRES approximation** of Algorithm 6.9. -/
theorem gmresHH_eq {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    gmresHH A b x₀ m = gmresFixed A b x₀ m := by
  obtain ⟨xx, -, huniq⟩ := Krylov.existsUnique_isMinResIterate_of_injective
    (injective_op_of_isUnit hA) b x₀ m
  have hmr : m ≤ grade A (r₀ A b x₀) := by
    rw [grade_eq, ← grade_v₁]
    exact hm
  rw [huniq _ (gmresHH_isMinResIterate A b x₀ hn hmr hR),
    huniq _ (gmresFixed_isMinResIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm))]

end Householder

/-! ### The numbered results of §6.5, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- (6.27): `b - A(x_0 + V_m y) = V_{m+1}(β e_1 - H̄_m y)`. -/
theorem residual_eq_6_27 {m : ℕ} (y : Fin m → ℝ) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : ℝ) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) :=
  eq_6_27 A b x₀ y

/-- (6.28): `J(y) = ‖b - A(x_0 + V_m y)‖₂ = ‖β e_1 - H̄_m y‖₂`. -/
theorem residual_eq_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → ℝ) :
    ‖b - op A (krylovIterate A b x₀ m y)‖ = J A b x₀ m y :=
  eq_6_28 A b x₀ hm y

/-- **(6.29)–(6.30)**: the GMRES approximation is the unique vector of `x_0 + 𝒦_m` minimizing
`‖b - A x‖₂`; equivalently, it is the backbone's minimal-residual Krylov iterate. -/
theorem gmres_isMinResIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    {x : EuclideanSpace ℝ (Fin n)} :
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResIterate (op A) b x₀ m x :=
  isGMRESIterate_iff A b x₀ hm

theorem gmres_unique {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    ∃! x, IsGMRESIterate A b x₀ m x :=
  existsUnique_isGMRESIterate A b x₀ hm hA

/-- **Proposition 6.9**(1)–(3), the parts the book uses: for nonsingular `A` the triangular
factor `R_m` is nonsingular (so a vanishing `r_{mm}` forces `A` singular); `y_m = R_m⁻¹ g_m` is
the unique minimizer of `J`; and the residual satisfies (6.41) and (6.42). -/
theorem prop_6_9 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) ∧
      (IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
        ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m) ∧
      ‖b - op A (gmresFixed A b x₀ m)‖ =
        ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : ℝ) m‖ :=
  ⟨isUnit_R_of_isUnit A b x₀ hA hm, prop_6_9_2 A b x₀ (isUnit_R_of_isUnit A b x₀ hA hm),
    eq_6_42 A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)⟩

/-- **Proposition 6.10**: GMRES breaks down at step `j` if and only if `x_j` is exact
(`A` nonsingular). The hypothesis "the first `j` steps were taken" is the book's implicit one. -/
theorem prop_6_10_book (hA : IsUnit A) (hr : r₀ A b x₀ ≠ 0) {j : ℕ} (hj : 0 < j)
    (hnb : NoBreakdownBefore A (v₁ A b x₀) j) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b :=
  prop_6_10 A b x₀ hA hj ((noBreakdownBefore_iff A _ (norm_v₁ A b x₀ hr) j).1 hnb)

/-- **P-6.5**: GMRES is Saad (5.7) with `V = V_m`, `W = A V_m`: the coordinates `y_m` solve the
normal equations, `y_m = (H̄_mᵀ H̄_m)⁻¹ H̄_mᵀ (β e_1)`. -/
theorem p_6_5_book {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᵀ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᵀ *ᵥ ((β A b x₀ : ℝ) • e₁ (m + 1))) := by
  have hT : (Hbar A (v₁ A b x₀) m)ᴴ = (Hbar A (v₁ A b x₀) m)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hT]
  exact p_6_5 A b x₀ hR

/-- §6.5.2: **Algorithm 6.10** (Householder GMRES). Its scalar `β = e_1ᵀ h_0` is `±‖r_0‖₂`,
the accumulation (6.31)–(6.33) computes `x_0 + ∑_j η_j v_j` in the Householder Arnoldi basis, and
the result is the GMRES approximation of Algorithm 6.9. -/
theorem alg_6_10 {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    |βHH A b x₀| = ‖r₀ A b x₀‖ ∧
      gmresHH A b x₀ m = x₀ + ∑ j : Fin m, gmresHHY A b x₀ m j • hhV A (r₀ A b x₀) (j : ℕ) ∧
        gmresHH A b x₀ m = gmresFixed A b x₀ m :=
  ⟨abs_βHH A b x₀ (by omega), gmresHH_eq_add_sum A b x₀ m, gmresHH_eq A b x₀ hn hm hA hR⟩

/-- §6.5.5: the full GMRES algorithm converges in at most `n` steps. -/
theorem gmres_exact_of_card_le (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) :
    op A (gmres A b x₀ m) = b :=
  gmres_apply_eq A b x₀ hA hmn

end BookResults

end SaadSparse.Ch06
