import Numlib.Surface.SaadSparse.Ch06.Arnoldi

/-!
# Saad, §6.5.3 and §6.5.9: Givens rotations and the factorization `Q_m H̄_m = R̄_m`

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.5.3 (the plane rotations of GMRES) and §6.5.9 (their complex form).

The rotation parameters `c_i`, `s_i` of (6.37)/(6.81), the rotations `Ω_i` of (6.34)/(6.80),
their product `Q_m = Ω_m ⋯ Ω_1` (6.38), the triangular factor `R̄_m = Q_m H̄_m` (6.39) and the
rotated right-hand side `ḡ_m = Q_m(β e_1)` (6.40) are `c`, `s`, `Ω`, `Qrot`, `Rbar`, `gbar`;
`R` and `g` drop the last row and component, and `γ` is the book's `γ_{i+1}`. Indices are
`0`-based, so `c h i` is the book's `c_{i+1}`.

All of these are `ℕ`-indexed functions of the Hessenberg coefficient function `h` alone, not of
the step count `m`; that is the content of the book's remark that the previous rotations need
not be recomputed when a column is appended, and it makes (6.44)–(6.46) hold by definition
(`g_apply`, `Rbar_succ_submatrix`).

Everything here is a specialization of the backbone Givens layer in `Numlib/Krylov/Hessenberg.lean`
(`Krylov.givensC`, `givensS`, `givensMatrix`, `givensQ`, `rotated`, `gamma`, `gvec`), whose
`Krylov.rotated h m` is the book's `H̄_m^{(m)}`. The two bridging lemmas are `Rbar_eq` and
`gbar_eq`; every numbered fact below is read off from them.

This file is placed before `Ch06/GMRES.lean` (not after it, as in the plan's table) because the
GMRES iterate of Algorithm 6.9 is *defined* through `R` and `g` (Proposition 6.9(2)).
Proposition 6.9, Proposition 6.10 and the "at most `n` steps" remark, which §6.5.3–6.5.4 state
about GMRES itself, are therefore in `Ch06/GMRES.lean`.

Definitions and lemmas are polymorphic in `𝕜`; the book's §6.5.3 is real and its §6.5.9 is
complex, and the two are the same code — the numbered results are collected at the end over `ℝ`
and over `ℂ`.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The rotation parameters (6.37), (6.81) -/

/-- (6.37)/(6.81): the book's `c_{i+1} = h_{ii}^{(i-1)} / ρ_i`, where
`ρ_i = (|h_{ii}^{(i-1)}|² + |h_{i+1,i}|²)^{1/2}` is `Krylov.givensRho h i`; `0` at a breakdown,
by Lean's `x / 0 = 0`. -/
noncomputable abbrev c (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensC h i

/-- (6.37)/(6.81): the book's `s_{i+1} = h_{i+1,i} / ρ_i`. -/
noncomputable abbrev s (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := Krylov.givensS h i

/-- (6.34)/(6.80): the rotation `Ω_{i+1}` acting in the `(i, i+1)` plane, as an
`(m+1) × (m+1)` matrix: row `i` is `(c̄_i, s̄_i)`, row `i+1` is `(-s_i, c_i)`, and the rest is
the identity. -/
noncomputable abbrev Ω (h : ℕ → ℕ → 𝕜) (i m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Krylov.givensMatrix h i m

/-- (6.38): `Q_m = Ω_m ⋯ Ω_1`. -/
noncomputable abbrev Qrot (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Krylov.givensQ h m

/-- The book's `γ_{i+1}`, the last entry of `ḡ_i`: `γ 0 = β` and `γ (i+1) = -s_i γ i` (6.47). -/
noncomputable abbrev γ (h : ℕ → ℕ → 𝕜) (β : 𝕜) (i : ℕ) : 𝕜 := Krylov.gamma h β i

/-- (6.39): the triangular factor `R̄_m = Q_m H̄_m`. -/
noncomputable def Rbar (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Qrot h m * Krylov.hessenbergOf h m

/-- (6.40): the rotated right-hand side `ḡ_m = Q_m (β e_1) = (γ_1, …, γ_{m+1})ᵀ`. -/
noncomputable def gbar (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin (m + 1) → 𝕜 :=
  (Qrot h m).mulVec (Krylov.firstVec β (m + 1))

/-- `R_m`: the `m × m` matrix obtained from `R̄_m` by deleting its (vanishing) last row. -/
noncomputable def R (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  (Rbar h m).submatrix Fin.castSucc id

/-- `g_m`: the vector obtained from `ḡ_m` by deleting its last component `γ_{m+1}`. -/
noncomputable def g (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  fun i => gbar h β m i.castSucc

variable (h : ℕ → ℕ → 𝕜) (β : 𝕜)

/-! ### The bridge to the backbone: `R̄_m` is `H̄_m^{(m)}` and `ḡ_m` is `(g_0, …, γ_m)` -/

/-- The book's `R̄_m = Q_m H̄_m` is the backbone's Hessenberg matrix of the coefficients after
`m` rotations. -/
theorem Rbar_eq (m : ℕ) : Rbar h m = Krylov.hessenbergOf (Krylov.rotated h m) m :=
  Krylov.givensQ_mul_hessenbergOf h m

theorem Rbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Rbar h m i j = Krylov.rotated h m i j := by
  rw [Rbar_eq]
  rfl

/-- The book's `ḡ_m = Q_m(β e_1)` is `(g_0, …, g_{m-1}, γ_m)`. -/
theorem gbar_eq (m : ℕ) :
    gbar h β m =
      fun i : Fin (m + 1) => if (i : ℕ) < m then Krylov.gvec h β i else Krylov.gamma h β m :=
  Krylov.givensQ_mulVec_firstVec h β m

theorem gbar_apply_of_lt {m : ℕ} {i : Fin (m + 1)} (hi : (i : ℕ) < m) :
    gbar h β m i = Krylov.gvec h β i := by
  rw [gbar_eq]
  exact ite_eq_left hi

/-- The last component of `ḡ_m` is `γ_{m+1}`. -/
theorem gbar_last (m : ℕ) : gbar h β m (Fin.last m) = γ h β m := by
  rw [gbar_eq]
  exact ite_eq_right (by simp)

theorem R_apply {m : ℕ} (i j : Fin m) : R h m i j = Krylov.rotated h m i j := by
  rw [R, Matrix.submatrix_apply, Rbar_apply, Fin.val_castSucc]
  rfl

theorem R_eq (m : ℕ) : R h m = Krylov.hessenbergSqOf (Krylov.rotated h m) m := by
  ext i j
  rw [R_apply]
  rfl

/-- (6.44)–(6.46): the entry `g_i` of `g_m` does not depend on `m` — appending a column and
rotating it leaves the earlier components of the right-hand side alone. -/
theorem g_apply {m : ℕ} (i : Fin m) : g h β m i = Krylov.gvec h β (i : ℕ) := by
  rw [g, gbar_apply_of_lt h β (by simp)]
  rfl

theorem g_eq (m : ℕ) : g h β m = fun i : Fin m => Krylov.gvec h β (i : ℕ) :=
  funext fun i => g_apply h β i

/-! ### The least-squares function (6.26)/(6.28) at the level of a coefficient function -/

/-- `‖β e_1 - H̄_m y‖₂`, the function (6.26)/(6.28) that GMRES and QGMRES minimize, as a
function of the Hessenberg coefficients alone. `J` of `Ch06/GMRES.lean` is its instance at the
Arnoldi coefficients of `v_1`. -/
noncomputable def lsq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

theorem lsq_nonneg {m : ℕ} (y : Fin m → 𝕜) : 0 ≤ lsq h β m y := norm_nonneg _

/-- The triangular system `R_m y = g_m` of Proposition 6.9(2) is solved by `y = R_m⁻¹ g_m`. -/
theorem mulVec_R_inv_mulVec_g {m : ℕ} (hR : IsUnit (R h m)) :
    R h m *ᵥ ((R h m)⁻¹ *ᵥ g h β m) = g h β m := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hR),
    Matrix.one_mulVec]

/-! ### (6.35), (6.36), (6.80): the rotations are unitary -/

/-- (6.35)/(6.80): `|c_i|² + |s_i|² = 1` (away from a breakdown, where both vanish). -/
theorem norm_c_sq_add_norm_s_sq {i : ℕ} (hρ : Krylov.givensRho h i ≠ 0) :
    ‖c h i‖ ^ 2 + ‖s h i‖ ^ 2 = 1 :=
  Krylov.norm_givensC_sq_add_norm_givensS_sq h i hρ

/-- (6.34)/(6.80): each `Ω_i` is unitary. -/
theorem Ω_mem_unitaryGroup {i m : ℕ} (hi : i < m) (hρ : Krylov.givensRho h i ≠ 0) :
    Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  Krylov.givensMatrix_mem_unitaryGroup h i m hi hρ

/-- (6.38): `Q_m = Ω_m ⋯ Ω_1` is unitary. -/
theorem Qrot_mem_unitaryGroup (m : ℕ) (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0) :
    Qrot h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 :=
  Krylov.givensQ_mem_unitaryGroup h m hρ

/-- `Q_m` preserves the Euclidean norm, the only property of the rotations that (6.43) uses. -/
theorem norm_toLp_Qrot_mulVec {m : ℕ} (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0)
    (z : Fin (m + 1) → 𝕜) :
    ‖(WithLp.toLp 2 (Qrot h m *ᵥ z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖ :=
  Matrix.norm_toLp_mulVec_of_mem_unitaryGroup (Qrot_mem_unitaryGroup h m hρ) z

/-! ### (6.39): `R̄_m` is upper triangular with vanishing last row -/

variable (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
include hh

/-- (6.39): `R̄_m` is upper triangular. -/
theorem Rbar_eq_zero_of_lt {m : ℕ} {i : Fin (m + 1)} {j : Fin m} (hij : (j : ℕ) < (i : ℕ)) :
    Rbar h m i j = 0 := by
  rw [Rbar_apply]
  exact Krylov.rotated_eq_zero_of_lt h hh m i j j.isLt hij

/-- (6.39): the last row of `R̄_m` vanishes. -/
theorem Rbar_last_row {m : ℕ} (j : Fin m) : Rbar h m (Fin.last m) j = 0 :=
  Rbar_eq_zero_of_lt h hh (by simp)

/-- `R_m` is upper triangular. -/
theorem R_isUpperTriangular (m : ℕ) : (R h m).IsUpperTriangular := by
  rw [R_eq]
  exact Krylov.hessenbergSqOf_rotated_isUpperTriangular h hh (by omega)

/-- (6.37): the diagonal entry `r_{ii}` of `R_m` is the nonnegative real `ρ_i`. Over `ℂ` this is
the §6.5.9 statement that the diagonal of `R_m` is real and nonnegative. -/
theorem R_diag {m : ℕ} (i : Fin m) : R h m i i = ((Krylov.givensRho h i : ℝ) : 𝕜) := by
  rw [R_apply]
  exact Krylov.rotated_diag h hh i.isLt

/-- `R_m` is nonsingular as soon as no rotation has degenerated. -/
theorem isUnit_R {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) : IsUnit (R h m) := by
  rw [R_eq]
  exact Krylov.isUnit_hessenbergSqOf_rotated_self h hh hρ

/-- `R_m` is nonsingular exactly when no rotation among the first `m` has degenerated: the
diagonal of the triangular factor is `ρ_0, …, ρ_{m-1}`. -/
theorem isUnit_R_iff {m : ℕ} : IsUnit (R h m) ↔ ∀ k < m, Krylov.givensRho h k ≠ 0 := by
  refine ⟨fun hR k hk => ?_, isUnit_R h hh⟩
  have hdet : (R h m).det = ∏ i : Fin m, ((Krylov.givensRho h (i : ℕ) : ℝ) : 𝕜) := by
    rw [Matrix.det_of_isUpperTriangular (R_isUpperTriangular h hh m)]
    exact Finset.prod_congr rfl fun i _ => R_diag h hh i
  have hne : (R h m).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hR).ne_zero
  rw [hdet, Finset.prod_ne_zero_iff] at hne
  simpa using hne ⟨k, hk⟩ (Finset.mem_univ _)

/-! ### (6.43): the least-squares residual after rotation -/

omit hh in
/-- `Q_m` carries the least-squares residual `β e_1 - H̄_m y` to `ḡ_m - R̄_m y`. -/
theorem Qrot_mulVec_firstVec_sub {m : ℕ} (y : Fin m → 𝕜) :
    Qrot h m *ᵥ (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y)
      = gbar h β m - Rbar h m *ᵥ y := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rfl

/-- (6.41): when `R_m y = g_m` the rotated least-squares residual is `γ_{m+1} e_{m+1}` — the
last row of `R̄_m` vanishes and the last entry of `ḡ_m` is `γ_{m+1}`. -/
theorem gbar_sub_Rbar_mulVec {m : ℕ} {y : Fin m → 𝕜} (hy : R h m *ᵥ y = g h β m) :
    gbar h β m - Rbar h m *ᵥ y = Pi.single (Fin.last m) (γ h β m) := by
  funext i
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · have hz : (Rbar h m *ᵥ y) (Fin.last m) = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by rw [Rbar_last_row h hh j, zero_mul]
    rw [Pi.sub_apply, gbar_last, hz, sub_zero, Pi.single_eq_same]
  · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
    have hz : (Rbar h m *ᵥ y) i'.castSucc = g h β m i' := by
      rw [← hy]
      rfl
    rw [Pi.sub_apply, hz, Pi.single_eq_of_ne hi]
    exact sub_eq_zero.2 rfl

omit hh in
/-- (6.43), first equality: `Q_m` is an isometry, so `‖β e_1 - H̄_m y‖₂ = ‖ḡ_m - R̄_m y‖₂`. -/
theorem norm_firstVec_sub_mulVec_eq_norm_gbar_sub {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (y : Fin m → 𝕜) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      ‖(WithLp.toLp 2 (gbar h β m - Rbar h m *ᵥ y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  have hmul : Qrot h m *ᵥ (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) =
      gbar h β m - Rbar h m *ᵥ y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    rfl
  rw [← norm_toLp_Qrot_mulVec h hρ, hmul]

/-- (6.43): `‖β e_1 - H̄_m y‖₂² = |γ_{m+1}|² + ‖g_m - R_m y‖₂²`; the rotations split the
least-squares problem into the part `R_m y = g_m` can annihilate and the fixed remainder. -/
theorem norm_sq_firstVec_sub_mulVec {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0)
    (y : Fin m → 𝕜) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 =
      ‖γ h β m‖ ^ 2 +
        ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 := by
  rw [Krylov.norm_sq_firstVec_sub_mulVec_eq h hh hρ β y, R_eq, g_eq, add_comm]

/-- **Proposition 6.9(2)** at the level of a coefficient function: `y = R_m⁻¹ g_m` minimizes
`‖β e_1 - H̄_m y‖₂`, and is the only minimizer, as soon as `R_m` is nonsingular. This is (6.43):
the square of the objective is `|γ_{m+1}|² + ‖g_m - R_m y‖₂²`, whose second term the triangular
system annihilates. -/
theorem isMinOn_lsq {m : ℕ} (hR : IsUnit (R h m)) :
    IsMinOn (lsq h β m) Set.univ ((R h m)⁻¹ *ᵥ g h β m) ∧
      ∀ y, IsMinOn (lsq h β m) Set.univ y → y = (R h m)⁻¹ *ᵥ g h β m := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsq : ∀ y : Fin m → 𝕜, lsq h β m y ^ 2 = ‖γ h β m‖ ^ 2 +
      ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 :=
    fun y => norm_sq_firstVec_sub_mulVec h β hh hρ y
  have hzero : lsq h β m ((R h m)⁻¹ *ᵥ g h β m) ^ 2 = ‖γ h β m‖ ^ 2 := by
    rw [hsq, mulVec_R_inv_mulVec_g h β hR, sub_self]
    simp
  have hle : ∀ y : Fin m → 𝕜, lsq h β m ((R h m)⁻¹ *ᵥ g h β m) ≤ lsq h β m y := by
    intro y
    nlinarith [hsq y, lsq_nonneg h β ((R h m)⁻¹ *ᵥ g h β m), lsq_nonneg h β y,
      sq_nonneg ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖]
  refine ⟨isMinOn_iff.2 fun y _ => hle y, fun y hy => ?_⟩
  have h3 : ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))‖ = 0 := by
    nlinarith [hsq y, hle y, isMinOn_iff.1 hy _ (Set.mem_univ ((R h m)⁻¹ *ᵥ g h β m)),
      lsq_nonneg h β y, lsq_nonneg h β ((R h m)⁻¹ *ᵥ g h β m),
      norm_nonneg (WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace 𝕜 (Fin m))]
  rw [norm_eq_zero, WithLp.toLp_eq_zero, sub_eq_zero] at h3
  exact Matrix.mulVec_injective_iff_isUnit.2 hR (by rw [← h3, mulVec_R_inv_mulVec_g h β hR])

/-- (6.44)–(6.46): the first `m` columns of `R̄_{m+1}` are those of `R̄_m`, extended by a zero
row — appending an Arnoldi column and rotating it does not touch the earlier columns. -/
theorem Rbar_succ_submatrix {m : ℕ} :
    (Rbar h (m + 1)).submatrix Fin.castSucc Fin.castSucc = Rbar h m := by
  ext i j
  rw [Matrix.submatrix_apply, Rbar_apply, Rbar_apply, Fin.val_castSucc, Fin.val_castSucc,
    Krylov.rotated_succ_eq_of_lt h hh m (j : ℕ) j.isLt (i : ℕ)]

/-- (6.41): with `R_m y = g_m` the least-squares residual `β e_1 - H̄_m y` is
`Q_mᴴ (γ_{m+1} e_{m+1})`. -/
theorem firstVec_sub_mulVec_eq {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0)
    {y : Fin m → 𝕜} (hy : R h m *ᵥ y = g h β m) :
    Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y
      = (Qrot h m)ᴴ *ᵥ Pi.single (Fin.last m) (γ h β m) := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  conv_lhs => rw [← Matrix.one_mulVec (Krylov.firstVec β (m + 1) -
    Krylov.hessenbergOf h m *ᵥ y), ← h1]
  rw [← Matrix.mulVec_mulVec, Qrot_mulVec_firstVec_sub, gbar_sub_Rbar_mulVec h β hh hy]

/-- (6.42) at the level of a coefficient function: the minimum of `‖β e_1 - H̄_m y‖₂` is
`|γ_{m+1}|`. -/
theorem lsq_eq_norm_gamma {m : ℕ} (hR : IsUnit (R h m)) :
    lsq h β m ((R h m)⁻¹ *ᵥ g h β m) = ‖γ h β m‖ := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsq := norm_sq_firstVec_sub_mulVec h β hh hρ ((R h m)⁻¹ *ᵥ g h β m)
  rw [mulVec_R_inv_mulVec_g h β hR, sub_self] at hsq
  simp only [WithLp.toLp_zero, norm_zero] at hsq
  rw [lsq]
  nlinarith [norm_nonneg (WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
      Krylov.hessenbergOf h m *ᵥ ((R h m)⁻¹ *ᵥ g h β m)) : EuclideanSpace 𝕜 (Fin (m + 1))),
    norm_nonneg (γ h β m), hsq]

/-! ### P-6.5: the normal equations of the least-squares problem -/

/-- The last row of `R̄_m` vanishes, so `R̄_mᴴ R̄_m = R_mᴴ R_m`. -/
theorem conjTranspose_mul_self_Rbar {m : ℕ} : (Rbar h m)ᴴ * Rbar h m = (R h m)ᴴ * R h m := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fin.sum_univ_castSucc, Rbar_last_row h hh i, star_zero, zero_mul, add_zero]
  rfl

/-- The last row of `R̄_m` vanishes and the last entry of `ḡ_m` is dropped, so
`R̄_mᴴ ḡ_m = R_mᴴ g_m`. -/
theorem conjTranspose_mulVec_gbar {m : ℕ} :
    (Rbar h m)ᴴ *ᵥ gbar h β m = (R h m)ᴴ *ᵥ g h β m := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Fin.sum_univ_castSucc, Rbar_last_row h hh i, star_zero, zero_mul, add_zero]
  rfl

/-- `H̄_mᴴ H̄_m = R_mᴴ R_m`: the rotations are unitary, so they drop out of the normal
equations. -/
theorem conjTranspose_mul_self_hessenbergOf {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) :
    (Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m = (R h m)ᴴ * R h m := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  have h2 : (Rbar h m)ᴴ * Rbar h m
      = (Krylov.hessenbergOf h m)ᴴ * ((Qrot h m)ᴴ * Qrot h m) * Krylov.hessenbergOf h m := by
    rw [Rbar, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [← conjTranspose_mul_self_Rbar h hh, h2, h1, Matrix.mul_one]

/-- `H̄_mᴴ (β e_1) = R_mᴴ g_m`. -/
theorem conjTranspose_hessenbergOf_mulVec_firstVec {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) :
    (Krylov.hessenbergOf h m)ᴴ *ᵥ Krylov.firstVec β (m + 1) = (R h m)ᴴ *ᵥ g h β m := by
  have h1 : (Qrot h m)ᴴ * Qrot h m = 1 := by
    have hq := (Matrix.mem_unitaryGroup_iff' (A := Qrot h m)).1 (Qrot_mem_unitaryGroup h m hρ)
    rwa [Matrix.star_eq_conjTranspose] at hq
  rw [← conjTranspose_mulVec_gbar h β hh, gbar, Rbar, Matrix.conjTranspose_mul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one]

/-- The normal-equations matrix `H̄_mᴴ H̄_m` is nonsingular exactly when `R_m` is. -/
theorem isUnit_conjTranspose_mul_self_hessenbergOf {m : ℕ}
    (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (hR : IsUnit (R h m)) :
    IsUnit ((Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m) := by
  have hRH : IsUnit ((R h m)ᴴ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hR).star
  rw [conjTranspose_mul_self_hessenbergOf h hh hρ]
  exact hRH.mul hR

/-- **P-6.5**: the triangular solution `y = R_m⁻¹ g_m` of Proposition 6.9(2) satisfies the normal
equations `H̄_mᴴ H̄_m y = H̄_mᴴ (β e_1)` of the least-squares problem (6.29) — that is, GMRES is
Saad (5.7) with `V = V_m` and `W = A V_m`. -/
theorem normalEquations {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) {y : Fin m → 𝕜}
    (hy : R h m *ᵥ y = g h β m) :
    ((Krylov.hessenbergOf h m)ᴴ * Krylov.hessenbergOf h m) *ᵥ y
      = (Krylov.hessenbergOf h m)ᴴ *ᵥ Krylov.firstVec β (m + 1) := by
  rw [conjTranspose_mul_self_hessenbergOf h hh hρ,
    conjTranspose_hessenbergOf_mulVec_firstVec h β hh hρ, ← Matrix.mulVec_mulVec, hy]

/-! ### (6.44)–(6.47): the progressive form of the right-hand side -/

omit hh

/-- (6.47): `γ_{j+2} = -s_{j+1} γ_{j+1}`. -/
theorem gamma_succ (j : ℕ) : γ h β (j + 1) = -(s h j) * γ h β j :=
  Krylov.gamma_succ h β j

/-- (6.44)–(6.46): the entry of `ḡ_{m+1}` at the position of the last entry of `ḡ_m` is
`c̄_{m+1} γ_{m+1}` (the book's `c_{m+1} γ_{m+1}`; the conjugate is the complex convention
(6.80)). -/
theorem gbar_succ_castSucc (m : ℕ) :
    gbar h β (m + 1) (Fin.last m).castSucc = starRingEnd 𝕜 (c h m) * γ h β m :=
  gbar_apply_of_lt h β (by simp)

/-- (6.44)–(6.46): the last entry of `ḡ_{m+1}` is `-s_{m+1} γ_{m+1}`. -/
theorem gbar_succ_last (m : ℕ) : gbar h β (m + 1) (Fin.last (m + 1)) = -(s h m) * γ h β m := by
  rw [gbar_last]
  exact Krylov.gamma_succ h β m

/-- `|γ_{m+1}| = |s_1 ⋯ s_m| |β|`, the product form of (6.47). -/
theorem norm_gamma_eq_prod (m : ℕ) :
    ‖γ h β m‖ = (∏ k ∈ Finset.range m, ‖s h k‖) * ‖β‖ :=
  Krylov.norm_gamma_eq_prod h β m

/-! ### §6.5.9: reality of `s_i` and of the `γ_i` for Arnoldi coefficients -/

section Arnoldi

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

/-- `s_{i+1} = h_{i+1,i} / ρ_i`, the second half of (6.37)/(6.81). -/
theorem s_eq_div (i : ℕ) : s h i = h (i + 1) i / ((Krylov.givensRho h i : ℝ) : 𝕜) := by
  change Krylov.givensS h i = _
  rw [Krylov.givensS, Krylov.rotated_eq_of_le h i (i + 1) i le_rfl]

/-- §6.5.9: for Arnoldi coefficients the subdiagonal entry is the real number `‖w_i‖`, so `s_i`
is real and nonnegative even over `ℂ`. -/
theorem s_arnoldiCoeff_eq (hv : ‖v₁‖ = 1) (i : ℕ) :
    s (arnoldiCoeff A v₁) i =
      ((‖arnoldiW A v₁ i‖ / Krylov.givensRho (arnoldiCoeff A v₁) i : ℝ) : 𝕜) := by
  rw [s_eq_div, arnoldiCoeff_succ_self A v₁ hv, RCLike.ofReal_div]

/-- §6.5.9: `s_i` is a nonnegative real. -/
theorem s_arnoldiCoeff_nonneg (hv : ‖v₁‖ = 1) (i : ℕ) :
    ∃ t : ℝ, 0 ≤ t ∧ s (arnoldiCoeff A v₁) i = (t : 𝕜) :=
  ⟨_, div_nonneg (norm_nonneg _) (Krylov.givensRho_nonneg _ i), s_arnoldiCoeff_eq A v₁ hv i⟩

/-- §6.5.9: starting from a real `β` all the `γ_i` are real, since every `s_i` is
(`s_arnoldiCoeff_nonneg`). -/
theorem exists_real_gamma_arnoldiCoeff (hv : ‖v₁‖ = 1) (t : ℝ) (i : ℕ) :
    ∃ u : ℝ, γ (arnoldiCoeff A v₁) ((t : ℝ) : 𝕜) i = (u : 𝕜) := by
  induction i with
  | zero => exact ⟨t, rfl⟩
  | succ i ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨w, -, hw⟩ := s_arnoldiCoeff_nonneg A v₁ hv i
      refine ⟨-(w * u), ?_⟩
      rw [gamma_succ, hu, hw]
      push_cast
      ring

end Arnoldi

end General

/-! ### The numbered facts of §6.5.3, in the book's real setting -/

section BookResultsReal

variable (h : ℕ → ℕ → ℝ) (β : ℝ) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)

/-- (6.35): `c_i² + s_i² = 1`. -/
theorem equation_6_35 {i : ℕ} (hρ : Krylov.givensRho h i ≠ 0) : c h i ^ 2 + s h i ^ 2 = 1 := by
  have := norm_c_sq_add_norm_s_sq h hρ
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at this

/-- (6.36), (6.38): the rotations `Ω_i` and their product `Q_m` are orthogonal. -/
theorem equation_6_38 (m : ℕ) (hρ : ∀ i < m, Krylov.givensRho h i ≠ 0) :
    (∀ i < m, Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ) ∧
      Qrot h m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ :=
  ⟨fun i hi => Ω_mem_unitaryGroup h hi (hρ i hi), Qrot_mem_unitaryGroup h m hρ⟩

include hh

/-- (6.39): `R̄_m = Q_m H̄_m` is upper triangular with vanishing last row. -/
theorem equation_6_39 (m : ℕ) :
    (∀ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) < (i : ℕ) → Rbar h m i j = 0) ∧
      ∀ j : Fin m, Rbar h m (Fin.last m) j = 0 :=
  ⟨fun _ _ hij => Rbar_eq_zero_of_lt h hh hij, fun j => Rbar_last_row h hh j⟩

/-- (6.43): `‖β e_1 - H̄_m y‖₂² = |γ_{m+1}|² + ‖g_m - R_m y‖₂²`. -/
theorem equation_6_43 {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) (y : Fin m → ℝ) :
    ‖(WithLp.toLp 2 (Krylov.firstVec β (m + 1) - Krylov.hessenbergOf h m *ᵥ y) :
        EuclideanSpace ℝ (Fin (m + 1)))‖ ^ 2 =
      ‖γ h β m‖ ^ 2 +
        ‖(WithLp.toLp 2 (g h β m - R h m *ᵥ y) : EuclideanSpace ℝ (Fin m))‖ ^ 2 :=
  norm_sq_firstVec_sub_mulVec h β hh hρ y

/-- (6.44)–(6.46): appending a column changes neither the earlier columns of `R̄` nor the
earlier entries of `ḡ`; the two new entries of `ḡ_{m+1}` are `c_{m+1} γ_{m+1}` and
`-s_{m+1} γ_{m+1}`. -/
theorem equation_6_44 {m : ℕ} :
    (Rbar h (m + 1)).submatrix Fin.castSucc Fin.castSucc = Rbar h m ∧
      (∀ i : Fin m, g h β (m + 1) i.castSucc = g h β m i) ∧
        gbar h β (m + 1) (Fin.last m).castSucc = c h m * γ h β m ∧
          gbar h β (m + 1) (Fin.last (m + 1)) = -(s h m) * γ h β m := by
  refine ⟨Rbar_succ_submatrix h hh, fun i => ?_, ?_, gbar_succ_last h β m⟩
  · rw [g_apply, g_apply, Fin.val_castSucc]
  · rw [gbar_succ_castSucc]
    rfl

omit hh

/-- (6.47): `γ_{j+2} = -s_{j+1} γ_{j+1}`. -/
theorem equation_6_47 (j : ℕ) : γ h β (j + 1) = -(s h j) * γ h β j :=
  gamma_succ h β j

end BookResultsReal

/-! ### §6.5.9: the complex rotations (6.80)–(6.81) -/

section BookResultsComplex

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v₁ : EuclideanSpace ℂ (Fin n))

/-- (6.80): the complex rotation `Ω_i` has row `i` equal to `(c̄_i, s̄_i)`, row `i+1` equal to
`(-s_i, c_i)`, and agrees with the identity elsewhere. -/
theorem equation_6_80 (h : ℕ → ℕ → ℂ) (i m : ℕ) (p q : Fin (m + 1)) :
    Ω h i m p q =
      if (p : ℕ) = i ∧ (q : ℕ) = i then starRingEnd ℂ (c h i)
      else if (p : ℕ) = i ∧ (q : ℕ) = i + 1 then starRingEnd ℂ (s h i)
      else if (p : ℕ) = i + 1 ∧ (q : ℕ) = i then -s h i
      else if (p : ℕ) = i + 1 ∧ (q : ℕ) = i + 1 then c h i
      else if p = q then 1 else 0 := rfl

/-- (6.80): `|c_i|² + |s_i|² = 1`, so the complex rotations are unitary. -/
theorem equation_6_80_unitary (h : ℕ → ℕ → ℂ) {i m : ℕ} (hi : i < m)
    (hρ : Krylov.givensRho h i ≠ 0) :
    ‖c h i‖ ^ 2 + ‖s h i‖ ^ 2 = 1 ∧ Ω h i m ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ :=
  ⟨norm_c_sq_add_norm_s_sq h hρ, Ω_mem_unitaryGroup h hi hρ⟩

/-- (6.81), §6.5.9: for the Arnoldi coefficients `s_i` is real and nonnegative, the diagonal of
`R_m` is real and nonnegative, and all the `γ_i` are real. -/
theorem equation_6_81 (hv : ‖v₁‖ = 1) (t : ℝ) (m : ℕ) :
    (∀ i, ∃ u : ℝ, 0 ≤ u ∧ s (arnoldiCoeff A v₁) i = (u : ℂ)) ∧
      (∀ i : Fin m, R (arnoldiCoeff A v₁) m i i =
        ((Krylov.givensRho (arnoldiCoeff A v₁) i : ℝ) : ℂ)) ∧
        ∀ i, ∃ u : ℝ, γ (arnoldiCoeff A v₁) ((t : ℝ) : ℂ) i = (u : ℂ) :=
  ⟨fun i => s_arnoldiCoeff_nonneg A v₁ hv i,
    fun i => R_diag _ (fun _ _ hij => arnoldiCoeff_eq_zero_of_lt A v₁ hv hij) i,
    fun i => exists_real_gamma_arnoldiCoeff A v₁ hv t i⟩

end BookResultsComplex

end SaadSparse.Ch06
