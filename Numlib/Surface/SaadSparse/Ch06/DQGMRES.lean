import Numlib.Surface.SaadSparse.Ch06.GMRES

/-!
# Saad, §6.5.6: QGMRES and DQGMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.5.6.

Algorithm 6.12 (QGMRES) is Algorithm 6.9 run on the *incomplete* orthogonalization basis, and
Algorithm 6.13 (DQGMRES) is its progressive, truncated form. Both are stated here for an
arbitrary basis `u : ℕ → 𝔼` with Hessenberg coefficients `h` — that is, for any pair satisfying
the backbone relation `Krylov.HessenbergRelation (op A) u h` — because that is precisely the
book's reason why (6.41) and its consequences survive the loss of orthogonality: "orthogonality
was not used". The incomplete orthogonalization process itself (Algorithm 6.6, `iop`/`iopCoeff`)
is §6.4 material and lives in `Ch06/FOM.lean`; instantiating `u := iop A v₁ k`,
`h := iopCoeff A v₁ k` through `iop_hessenbergRelation` turns every statement below into the
book's QGMRES/DQGMRES statement, and `u := arnoldiCGS A v₁`, `h := arnoldiCoeff A v₁` turns it
into GMRES (`qgmres_eq_gmresFixed`, the book's "QGMRES = GMRES for `k ≥ m`").

Contents: `qgmresY`, `qgmres` (Algorithm 6.12), `Z`, `z`, `ζ` of (6.52), `quasiResidualNorm`
`= |γ_{m+1}|`, (6.49)–(6.50), and Algorithm 6.13 (`dqgmresP`, `dqgmres`) with its equivalence
`dqgmres_eq_qgmres` to Algorithm 6.12.

Also (6.53)–(6.55) and P-6.25 (`equation_6_53`, `equation_6_54`, `equation_6_55`, `problem_6_25`,
`problem_6_25_le`); the
size-compatibility lemmas for `Krylov.givensQAux` that (6.53) needs are private here and are a
backbone demand.

(6.51) is `equation_6_51`, derived from P-6.25. Its hypothesis `ζ_{k+1} ≤ 1`, like P-6.25's, is what
the truncation supplies through the orthonormality of the first `k + 1` vectors of the
incomplete orthogonalization process, which lives in `Ch06/FOM.lean`.

Not formalized here (reported to the plan): (6.56)–(6.58) and Theorem 6.11, which need the IOM
iterate of §6.4 (`Ch06/FOM.lean`) and, for Theorem 6.11, a Gram–Schmidt factorization of the
IOP basis under the L2 operator norm.

Definitions are polymorphic in `𝕜`; Theorem 6.11 is the book's only complex statement here.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Coordinate helpers -/

private theorem toEuclideanLin_toLp {m : ℕ} (M : Matrix (Fin n) (Fin m) 𝕜) (v : Fin m → 𝕜) :
    Matrix.toEuclideanLin M (WithLp.toLp 2 v) = WithLp.toLp 2 (M *ᵥ v) := rfl

/-! ### Algorithm 6.12 (QGMRES) and the quantities of (6.52) -/

/-- The coordinates `y_m = R_m⁻¹ g_m` computed by **Algorithm 6.12** (QGMRES); the same formula
as GMRES (Proposition 6.9(2)), applied to the incomplete-orthogonalization coefficients. -/
noncomputable def qgmresY (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (R h m)⁻¹ *ᵥ g h β m

/-- **Algorithm 6.12** (QGMRES): `x_m = x_0 + V_m y_m`. -/
noncomputable def qgmres (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 (qgmresY h β m))

/-- (6.52): `Z_{m+1} = V_{m+1} Q_mᴴ`. -/
noncomputable def Z (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin n) (Fin (m + 1)) 𝕜 :=
  colMatrix u (m + 1) * (Qrot h m)ᴴ

/-- (6.52): `z_{m+1}`, the last column of `Z_{m+1}`. -/
noncomputable def z (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝔼 :=
  Matrix.toEuclideanLin (Z u h m) (WithLp.toLp 2 (Pi.single (Fin.last m) 1))

/-- (6.52): `ζ_{m+1} = ‖z_{m+1}‖₂`. -/
noncomputable def ζ (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) : ℝ := ‖z u h m‖

/-- The quasi-residual norm `|γ_{m+1}|` monitored by QGMRES and DQGMRES. -/
noncomputable def quasiResidualNorm (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : ℝ := ‖γ h β m‖

theorem z_eq (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h m = Matrix.toEuclideanLin (colMatrix u (m + 1))
      (WithLp.toLp 2 ((Qrot h m)ᴴ *ᵥ Pi.single (Fin.last m) 1)) := by
  rw [z, Z, toEuclideanLin_toLp, toEuclideanLin_toLp, Matrix.mulVec_mulVec]

/-- (6.49): QGMRES minimizes the *quasi*-residual norm `‖β e_1 - H̄_m y‖₂`, whose value at the
minimizer is `|γ_{m+1}|`. Without orthogonality this is no longer the residual norm. -/
theorem qgmresY_isMinOn (h : ℕ → ℕ → 𝕜) (β : 𝕜) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {m : ℕ}
    (hR : IsUnit (R h m)) :
    IsMinOn (lsq h β m) Set.univ (qgmresY h β m) ∧
      lsq h β m (qgmresY h β m) = quasiResidualNorm h β m :=
  ⟨(isMinOn_lsq h β hh hR).1, lsq_eq_norm_gamma h β hh hR⟩

/-- (6.50): `b - A x_m = γ_{m+1} z_{m+1}`. Equation (6.41) survives the loss of orthogonality
because its proof uses only the Hessenberg relation and the unitarity of the rotations. -/
theorem equation_6_50 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) :
    b - op A (qgmres x₀ u h β m) = γ h β m • z u h m := by
  have hh := hu.eq_zero_of_lt
  have hρ := (isUnit_R_iff h hh).1 hR
  have hsingle : (Pi.single (Fin.last m) (γ h β m) : Fin (m + 1) → 𝕜)
      = γ h β m • Pi.single (Fin.last m) 1 := by
    funext j
    rcases eq_or_ne j (Fin.last m) with rfl | hj
    · simp
    · simp [Pi.single_eq_of_ne hj]
  rw [qgmres, toEuclideanLin_colMatrix_apply,
    hu.residual_eq hr m (qgmresY h β m), ← toEuclideanLin_colMatrix_apply u, qgmresY,
    firstVec_sub_mulVec_eq h β hh hρ (mulVec_R_inv_mulVec_g h β hR), hsingle, z_eq,
    toEuclideanLin_toLp, toEuclideanLin_toLp, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

/-- With the full Arnoldi data QGMRES is GMRES: the book's "QGMRES coincides with GMRES when
`k ≥ m`", once the incomplete orthogonalization has become the complete one. -/
theorem qgmres_eq_gmresFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) :
    qgmres x₀ (arnoldiCGS A (v₁ A b x₀)) (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m
      = gmresFixed A b x₀ m := rfl

/-! ### (6.53)–(6.55): the progressive form of `z_{m+1}`

The rotations are `ℕ`-indexed but their products live in a matrix of a fixed size, so (6.53)
compares `Q_m` at two sizes. The private lemmas below supply what the backbone Givens layer does
not: the last row of `Ω_m`, the fact that rows beyond `n` in `Q^{(n)}_m` are rows of the
identity, and the fact that the leading block of `Q^{(n)}_{m+1}` is `Q^{(n)}_m`. -/

/-- `z_{m+1}` expanded in the basis: `z_{m+1} = ∑_k conj((Q_m)_{m+1,k}) v_k`. -/
theorem z_eq_sum (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h m = ∑ k : Fin (m + 1), starRingEnd 𝕜 (Qrot h m (Fin.last m) k) • u (k : ℕ) := by
  rw [z_eq, toEuclideanLin_colMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (starRingEnd_apply _).symm


private theorem givensQ_succ_last_castSucc (h : ℕ → ℕ → 𝕜) (m : ℕ) (k : Fin (m + 1)) :
    Qrot h (m + 1) (Fin.last (m + 1)) k.castSucc = -(s h m) * Qrot h m (Fin.last m) k := by
  change Krylov.givensQAux h (m + 1) (m + 1) (Fin.last (m + 1)) k.castSucc
      = -Krylov.givensS h m * Krylov.givensQAux h m m (Fin.last m) k
  rw [Krylov.givensQAux_succ, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ k.castSucc := by
    have := k.isLt
    simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
    omega
  have hlast : Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1)) *
      Krylov.givensQAux h m (m + 1) (Fin.last (m + 1)) k.castSucc = 0 := by
    rw [Krylov.givensQAux_apply_of_row_lt h (m + 1) k.castSucc m (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_right hne, mul_zero]
  rw [hlast, add_zero]
  have hterm : ∀ p : Fin (m + 1),
      Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) p.castSucc *
        Krylov.givensQAux h m (m + 1) p.castSucc k.castSucc
      = (if (p : ℕ) = m then -Krylov.givensS h m else 0) *
        Krylov.givensQAux h m m p k := fun p => by
    have hp : (p : ℕ) ≠ m + 1 := by
      have := p.isLt
      omega
    rw [Krylov.givensMatrix_last_row, Krylov.givensQAux_castSucc h m m le_rfl p k, Fin.val_castSucc,
      ite_eq_right hp]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_eq_single (Fin.last m)]
  · rw [Fin.val_last, ite_eq_left rfl]
  · intro p _ hp
    have hpm : (p : ℕ) ≠ m := fun hc => hp (Fin.ext (by rw [hc, Fin.val_last]))
    rw [ite_eq_right hpm, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

private theorem givensQ_succ_last_last (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Qrot h (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1)) = c h m := by
  change Krylov.givensQAux h (m + 1) (m + 1) (Fin.last (m + 1)) (Fin.last (m + 1))
      = Krylov.givensC h m
  rw [Krylov.givensQAux_succ, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hz : ∀ p : Fin (m + 1),
      Krylov.givensMatrix h m (m + 1) (Fin.last (m + 1)) p.castSucc *
        Krylov.givensQAux h m (m + 1) p.castSucc (Fin.last (m + 1)) = 0 := fun p => by
    have hne : (p.castSucc : Fin (m + 2)) ≠ (Fin.last (m + 1) : Fin (m + 2)) := by
      have := p.isLt
      simp only [Ne, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
      omega
    rw [Krylov.givensQAux_apply_of_lt h m (m + 1) p.castSucc (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_right hne, mul_zero]
  rw [Finset.sum_congr rfl fun p _ => hz p, Finset.sum_const_zero, zero_add,
    Krylov.givensQAux_apply_of_row_lt h (m + 1) (Fin.last (m + 1)) m (Fin.last (m + 1))
      (by rw [Fin.val_last]; omega), ite_eq_left rfl, mul_one, Krylov.givensMatrix_last_row]
  simp

/-- (6.53): `z_{m+2} = -conj(s_{m+1}) z_{m+1} + conj(c_{m+1}) v_{m+2}`. Over `ℝ`, and over `ℂ`
for the Arnoldi and IOP coefficients (where `s` is real and nonnegative), this is the book's
`z_{m+1} = -s_m z_m + c_m v_{m+1}`. -/
theorem equation_6_53 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    z u h (m + 1) = starRingEnd 𝕜 (-(s h m)) • z u h m
      + starRingEnd 𝕜 (c h m) • u (m + 1) := by
  rw [z_eq_sum, z_eq_sum, Fin.sum_univ_castSucc, Finset.smul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by
      rw [givensQ_succ_last_castSucc, map_mul, smul_smul, Fin.val_castSucc]
  · rw [givensQ_succ_last_last, Fin.val_last]

/-- (6.54): `ζ_{m+2} ≤ |s_{m+1}| ζ_{m+1} + |c_{m+1}| ‖v_{m+2}‖`; with unit basis vectors this is
the book's `ζ_{m+1} ≤ |s_m| ζ_m + |c_m|`. -/
theorem equation_6_54 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    ζ u h (m + 1) ≤ ‖s h m‖ * ζ u h m + ‖c h m‖ * ‖u (m + 1)‖ := by
  rw [ζ, ζ, equation_6_53]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_smul, RCLike.norm_conj, norm_neg]
  · rw [norm_smul, RCLike.norm_conj]

/-- (6.55): two successive quasi-residuals,
`r_{m+1} = |s_{m+1}|² r_m + conj(c_{m+1}) γ_{m+2} v_{m+2}`. Over `ℝ`, where the Arnoldi and IOP
`s_i` are nonnegative reals, this is the book's `r_m = s_m² r_{m−1} + c_m γ_{m+1} v_{m+1}`. -/
theorem equation_6_55 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hR' : IsUnit (R h (m + 1))) :
    b - op A (qgmres x₀ u h β (m + 1))
      = ((‖s h m‖ : 𝕜) ^ 2) • (b - op A (qgmres x₀ u h β m))
        + (starRingEnd 𝕜 (c h m) * γ h β (m + 1)) • u (m + 1) := by
  have h1 : γ h β (m + 1) * starRingEnd 𝕜 (-(s h m)) = (‖s h m‖ : 𝕜) ^ 2 * γ h β m := by
    rw [gamma_succ, map_neg, ← RCLike.mul_conj (s h m)]
    ring
  have h2 : γ h β (m + 1) * starRingEnd 𝕜 (c h m)
      = starRingEnd 𝕜 (c h m) * γ h β (m + 1) := mul_comm _ _
  rw [equation_6_50 hu hr hR', equation_6_50 hu hr hR, equation_6_53, smul_add,
    smul_smul, smul_smul, smul_smul,
    h1, h2]

/-- **P-6.25**: (6.54) bounds the growth of `ζ` by one square root per step, so from
`ζ_{k+1} ≤ 1` one gets `ζ_{m+1} ≤ √(m − k + 1)` for `m ≥ k`. The base hypothesis
`ζ_{k+1} ≤ 1` is what the truncation supplies: the first `k + 1` incomplete-orthogonalization
vectors are orthonormal, so `z_{k+1}`, a unit vector of `Q_k` combined with them, has norm `1`.
This is sharper than (6.51). -/
theorem problem_6_25 (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k : ℕ} (hbase : ζ u h k ≤ 1) (j : ℕ) :
    ζ u h (k + j) ≤ Real.sqrt ((j : ℝ) + 1) := by
  induction j with
  | zero => simpa using hbase
  | succ j ih =>
      set a := ‖s h (k + j)‖ with ha
      set bb := ‖c h (k + j)‖ with hb
      set zz := ζ u h (k + j) with hzz
      set w := ‖u (k + j + 1)‖ with hw
      have hz0 : 0 ≤ zz := norm_nonneg _
      have ha0 : 0 ≤ a := norm_nonneg _
      have hb0 : 0 ≤ bb := norm_nonneg _
      have hw0 : 0 ≤ w := norm_nonneg _
      have hw1 : w ≤ 1 := hu _
      have hw2 : w ^ 2 ≤ 1 := by nlinarith
      have hab : a ^ 2 + bb ^ 2 = 1 := by
        have := norm_c_sq_add_norm_s_sq h (hρ (k + j))
        linarith
      have hsq : zz ^ 2 ≤ (j : ℝ) + 1 := by
        have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
        nlinarith [ih, hz0]
      have hC : (a * zz + bb * w) ^ 2 ≤ (a ^ 2 + bb ^ 2) * (zz ^ 2 + w ^ 2) := by
        nlinarith [sq_nonneg (a * w - bb * zz)]
      rw [hab, one_mul] at hC
      have hnn : 0 ≤ a * zz + bb * w := by positivity
      have hkey : (a * zz + bb * w) ^ 2 ≤ ((j : ℝ) + 1) + 1 := by linarith
      calc ζ u h (k + (j + 1)) ≤ a * zz + bb * w := equation_6_54 u h (k + j)
        _ = Real.sqrt ((a * zz + bb * w) ^ 2) := (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt (((j : ℝ) + 1) + 1) := Real.sqrt_le_sqrt hkey
        _ = Real.sqrt (((j + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf

/-- **P-6.25** in the book's indexing: `ζ_{m+1} ≤ √(m − k + 1)` for `m ≥ k`. -/
theorem problem_6_25_le (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k m : ℕ} (hbase : ζ u h k ≤ 1) (hkm : k ≤ m) :
    ζ u h m ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  simpa using problem_6_25 u h hu hρ hbase j

/-- (6.51): `‖b − A x_m‖ ≤ √(m − k + 1) |γ_{m+1}|` — the quasi-residual norm overestimates the
true residual norm by at most `√(m − k + 1)`. Here it is derived from the sharper P-6.25 rather
than from the book's direct splitting of `Q_mᵀ e_{m+1}`. -/
theorem equation_6_51 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hA : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hρ : ∀ i, Krylov.givensRho h i ≠ 0) {k m : ℕ}
    (hbase : ζ u h k ≤ 1) (hkm : k ≤ m) (hR : IsUnit (R h m)) :
    ‖b - op A (qgmres x₀ u h β m)‖
      ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) * quasiResidualNorm h β m := by
  have hzz : ζ u h m ≤ Real.sqrt (((m - k : ℕ) : ℝ) + 1) := problem_6_25_le u h hu hρ hbase hkm
  rw [equation_6_50 hA hr hR, norm_smul, quasiResidualNorm]
  calc ‖γ h β m‖ * ‖z u h m‖
      ≤ ‖γ h β m‖ * Real.sqrt (((m - k : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hzz (norm_nonneg _)
    _ = Real.sqrt (((m - k : ℕ) : ℝ) + 1) * ‖γ h β m‖ := mul_comm _ _

/-! ### Algorithm 6.13 (DQGMRES) -/

/-- **Algorithm 6.13** (DQGMRES), line 8: the direction vectors
`p_m = (v_m - ∑_{i=m-k}^{m-1} h_{im} p_i)/h_{mm}` of (6.48), where the `h_{im}` are the entries
of column `m` of the triangular factor `R̄` — the last column of `H̄_m` after the rotations
`Ω_{m-k}, …, Ω_m` have been applied to it. (Rotation `m` touches only rows `m` and `m+1`, so for
`i < m` the entry `Krylov.rotated h (m+1) i m` used here is the book's `h_{im}` obtained after
`Ω_{m-k}, …, Ω_{m-1}`, and at `i = m` it is the book's updated `h_{mm} = c_m h_{mm} + s_m
h_{m+1,m} = ρ_m`.) Division by `0` is `0`, the book's breakdown convention. -/
noncomputable def dqgmresP (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (k : ℕ) : ℕ → 𝔼
  | m =>
    let p : Fin m → 𝔼 := fun i => dqgmresP u h k (i : ℕ)
    ((Krylov.rotated h (m + 1) m m)⁻¹) •
      (u m - ∑ i : Fin m,
        (if m ≤ (i : ℕ) + k then Krylov.rotated h (m + 1) (i : ℕ) m else 0) • p i)
  termination_by m => m
  decreasing_by exact i.isLt

theorem dqgmresP_eq (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (k m : ℕ) :
    dqgmresP u h k m = ((Krylov.rotated h (m + 1) m m)⁻¹) •
      (u m - ∑ i ∈ Finset.range m,
        (if m ≤ i + k then Krylov.rotated h (m + 1) i m else 0) • dqgmresP u h k i) := by
  rw [dqgmresP]
  simp only []
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if m ≤ i + k then Krylov.rotated h (m + 1) i m else 0) • dqgmresP u h k i) m]

/-- **Algorithm 6.13** (DQGMRES), line 9: `x_m = x_{m-1} + γ_m p_m`, where the book's updated
`γ_m` is `c̄_m γ_m`, the entry `g_m` of the rotated right-hand side. -/
noncomputable def dqgmres (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => dqgmres x₀ u h β k m + Krylov.gvec h β m • dqgmresP u h k m

theorem dqgmres_eq_sum (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k m : ℕ) :
    dqgmres x₀ u h β k m
      = x₀ + ∑ j : Fin m, Krylov.gvec h β (j : ℕ) • dqgmresP u h k (j : ℕ) := by
  induction m with
  | zero => simp [dqgmres]
  | succ m ih =>
      rw [dqgmres, ih, Fin.sum_univ_castSucc, add_assoc]
      rfl

/-! ### DQGMRES is QGMRES -/

/-- Column `j` of the triangular factor is fixed once rotation `j` has been applied. -/
private theorem rotated_of_col_lt {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    {j : ℕ} : ∀ M, j + 1 ≤ M → ∀ i, Krylov.rotated h M i j = Krylov.rotated h (j + 1) i j := by
  intro M
  induction M with
  | zero => intro hM; omega
  | succ M ih =>
      intro hM i
      rcases Nat.lt_or_ge j M with hjM | hjM
      · rw [Krylov.rotated_succ_eq_of_lt h hh M j hjM i]
        exact ih (by omega) i
      · have hMj : M = j := by omega
        subst hMj
        rfl

/-- `R_m i j` is the entry `Krylov.rotated h (j+1) i j` used by the DQGMRES recurrence. -/
private theorem R_apply_eq_rotated_succ {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    {m : ℕ} (i j : Fin m) : R h m i j = Krylov.rotated h ((j : ℕ) + 1) i j := by
  rw [R_apply]
  exact rotated_of_col_lt hh m j.isLt (i : ℕ)

/-- The DQGMRES directions satisfy `P_m R_m = V_m`: the untruncated recurrence is exactly the
back-substitution for the triangular system. -/
theorem sum_R_smul_dqgmresP {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {k m : ℕ}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (hk : m ≤ k)
    (hd : ∀ j < m, Krylov.rotated h (j + 1) j j ≠ 0) (j : Fin m) :
    ∑ i : Fin m, R h m i j • dqgmresP u h k (i : ℕ) = u (j : ℕ) := by
  have hjm : (j : ℕ) < m := j.isLt
  have hzero : ∀ i ∈ Finset.range m, i ∉ Finset.range ((j : ℕ) + 1) →
      Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Krylov.rotated_eq_zero_of_lt h hh ((j : ℕ) + 1) i (j : ℕ) (Nat.lt_succ_self _)
      (by omega), zero_smul]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range m := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hpj := dqgmresP_eq u h k (j : ℕ)
  have hcond : ∀ i ∈ Finset.range (j : ℕ),
      (if (j : ℕ) ≤ i + k then Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) else 0) •
          dqgmresP u h k i
        = Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i := by
    intro i _
    rw [ite_eq_left (by omega)]
  rw [Finset.sum_congr rfl fun i _ => by rw [R_apply_eq_rotated_succ hh i j],
    Fin.sum_univ_eq_sum_range
      (fun i => Krylov.rotated h ((j : ℕ) + 1) i (j : ℕ) • dqgmresP u h k i) m,
    ← Finset.sum_subset hsub hzero,
    Finset.sum_range_succ, hpj, Finset.sum_congr rfl hcond, smul_smul,
    mul_inv_cancel₀ (hd (j : ℕ) hjm), one_smul]
  abel

/-- **Algorithm 6.13 computes Algorithm 6.12**: with no truncation (`m ≤ k`) and a nonsingular
triangular factor, DQGMRES and QGMRES produce the same iterate. -/
theorem dqgmres_eq_qgmres {x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜} {β : 𝕜} {k m : ℕ}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (hk : m ≤ k) (hR : IsUnit (R h m)) :
    dqgmres x₀ u h β k m = qgmres x₀ u h β m := by
  have hρ := (isUnit_R_iff h hh).1 hR
  have hd : ∀ j < m, Krylov.rotated h (j + 1) j j ≠ 0 := by
    intro j hj
    rw [Krylov.rotated_succ_self]
    simpa using hρ j hj
  have key := sum_R_smul_dqgmresP (u := u) (k := k) hh hk hd
  rw [dqgmres_eq_sum, qgmres, toEuclideanLin_colMatrix_apply]
  refine congrArg _ ?_
  have hg : ∀ i : Fin m, Krylov.gvec h β (i : ℕ) = (R h m *ᵥ qgmresY h β m) i := by
    intro i
    rw [qgmresY, mulVec_R_inv_mulVec_g h β hR, g_apply]
  calc ∑ i : Fin m, Krylov.gvec h β (i : ℕ) • dqgmresP u h k (i : ℕ)
      = ∑ i : Fin m, ∑ j : Fin m,
          (R h m i j * qgmresY h β m j) • dqgmresP u h k (i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    _ = ∑ j : Fin m, qgmresY h β m j • ∑ i : Fin m, R h m i j • dqgmresP u h k (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    _ = ∑ j : Fin m, qgmresY h β m j • u (j : ℕ) :=
        Finset.sum_congr rfl fun j _ => by rw [key j]

end General

end SaadSparse.Ch06
