import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.Relations
import Numlib.Krylov.Subspace
import Numlib.LinearSolve.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section03
import NumlibSurface.SaadSparse.Chapter06.Section04

/-!
# Saad §6.5: GMRES

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §6.5, together with the problems P-6.9, P-6.13, P-6.14, P-6.25 and P-6.26.

The data of the system — `r₀ = b - A x₀`, `β = ‖r₀‖₂`, `v₁ = r₀/β`, the first coordinate vector
`e₁`, and `mEff`, which implements the book's "if `h_{j+1,j} = 0` set `m := j`" — are shared with
`Chapter06/Section04.lean` and live in `Chapter06/Common.lean`. Definitions are polymorphic in `𝕜`,
so §6.5.9 (complex GMRES) is the same code; the numbered results are stated over `ℝ`, the book's
generality in §6.5, except in §6.5.9.

The file follows the book's order of subsections with one exception: §6.5.3, the Givens layer,
comes first, because the GMRES iterate of Algorithm 6.9 is *defined* through the triangular factor
`R` and the rotated right-hand side `g` (Proposition 6.9(2)).

## §6.5.3 and §6.5.9: Givens rotations and the factorization `Q_m H̄_m = R̄_m`

The rotation parameters `c_i`, `s_i` of (6.37)/(6.81), the rotations `Ω_i` of (6.34)/(6.80), their
product `Q_m = Ω_m ⋯ Ω_1` (6.38), the triangular factor `R̄_m = Q_m H̄_m` (6.39) and the rotated
right-hand side `ḡ_m = Q_m(β e_1)` (6.40) are `c`, `s`, `Ω`, `Qrot`, `Rbar`, `gbar`; `R` and `g`
drop the last row and component, and `γ` is the book's `γ_{i+1}`. Indices are `0`-based, so `c h i`
is the book's `c_{i+1}`.

All of these are `ℕ`-indexed functions of the Hessenberg coefficient function `h` alone, not of the
step count `m`; that is the content of the book's remark that the previous rotations need not be
recomputed when a column is appended, and it makes (6.44)–(6.46) hold by definition (`g_apply`,
`Rbar_succ_submatrix`). Everything here is a specialization of the backbone Givens layer in
`Numlib/Krylov/Hessenberg.lean` (`Krylov.givensC`, `givensS`, `givensMatrix`, `givensQ`, `rotated`,
`gamma`, `gvec`), whose `Krylov.rotated h m` is the book's `H̄_m^{(m)}`. The two bridging lemmas are
`Rbar_eq` and `gbar_eq`; every numbered fact of §6.5.3 is read off from them. The book's §6.5.3 is
real and its §6.5.9 is complex, and the two are the same code, so the numbered results are
collected at the end of the part over `ℝ` and over `ℂ`.

## §6.5.1–6.5.5: GMRES

The element `x = x₀ + V_m y` of (6.25) is `krylovIterate`, the least-squares function `J(y)` of
(6.26)/(6.28) is `J`, and Algorithm 6.9 line 12 ("compute `y_m` the minimizer") is the relation
`IsGMRESIterate`. `gmresY = R_m⁻¹ g_m` is the minimizer as §6.5.3 computes it (Proposition 6.9(2)),
`gmresFixed` the resulting iterate, `gmres` Algorithm 6.9 with the "set `m := j`" rule, and
`gmresRestarted` is Algorithm 6.11, GMRES(m). Algorithm 6.10 (Householder GMRES) is `gmresHH`,
built on the Householder Arnoldi basis of `Chapter06/Section03.lean` with the accumulation
`hornerAccumulate` of (6.31)–(6.33); `gmresHH_eq` is the statement that it computes the same
approximation as Algorithm 6.9.

**The hinge of the part is `isGMRESIterate_iff`** (6.29)–(6.30): the GMRES approximation, defined
by the least-squares problem in Hessenberg coordinates, *is* the backbone's minimal-residual
Krylov iterate `Krylov.IsMinResidualIterate` on `𝒦_m(A, r₀)`. Everything else — Proposition 6.9(2),
(6.41), (6.42), Proposition 6.10, the "at most `n` steps" remark — is a specialization of a
backbone theorem through that equivalence, the Givens layer above, and the bridge family
`arnoldiCGS_v₁`, `arnoldiCoeff_v₁`, `Hbar_v₁`, `grade_v₁` of `Chapter06/Common.lean` (the backbone
indexes the Arnoldi data by `r₀`, the book by `v₁`). Propositions 6.9 and 6.10 belong to
§6.5.3–6.5.4 but are statements about GMRES itself, so they are here rather than in the Givens
part.

## §6.5.6: QGMRES and DQGMRES

Algorithm 6.12 (QGMRES) is Algorithm 6.9 run on the *incomplete* orthogonalization basis, and
Algorithm 6.13 (DQGMRES) is its progressive, truncated form. Both are stated here for an
arbitrary basis `u : ℕ → 𝔼` with Hessenberg coefficients `h` — that is, for any pair satisfying
the backbone relation `Krylov.HessenbergRelation (op A) u h` — because that is precisely the
book's reason why (6.41) and its consequences survive the loss of orthogonality: "orthogonality
was not used". The incomplete orthogonalization process itself (Algorithm 6.6, `iop`/`iopCoeff`)
is §6.4 material and lives in `Chapter06/Section04.lean`; instantiating `u := iop A v₁ k`,
`h := iopCoeff A v₁ k` through `iop_hessenbergRelation` turns every statement into the book's
QGMRES/DQGMRES statement, and `u := arnoldiCGS A v₁`, `h := arnoldiCoeff A v₁` turns it into GMRES
(`qgmres_eq_gmresFixed`, the book's "QGMRES = GMRES for `k ≥ m`").

Contents: `qgmresY`, `qgmres` (Algorithm 6.12), `Z`, `z`, `ζ` of (6.52), `quasiResidualNorm`
`= |γ_{m+1}|`, (6.49)–(6.50), and Algorithm 6.13 (`dqgmresP`, `dqgmres`) with its equivalence
`dqgmres_eq_qgmres` to Algorithm 6.12. Also (6.53)–(6.55) and P-6.25 (`equation_6_53`,
`equation_6_54`, `equation_6_55`, `problem_6_25`, `problem_6_25_le`); the size-compatibility lemmas
for `Krylov.givensQAux` that (6.53) needs are private here and are a backbone demand. (6.51) is
`equation_6_51`, derived from P-6.25; its hypothesis `ζ_{k+1} ≤ 1`, like P-6.25's, is what the
truncation supplies through the orthonormality of the first `k + 1` vectors of the incomplete
orthogonalization process, which lives in `Chapter06/Section04.lean`.

**Theorem 6.11** (Freund–Nachtigal) is `theorem_6_11`, two lines of
`Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul` once `qgmres_isQuasiMinResidualIterate` identifies
Algorithm 6.12 as a quasi-minimal-residual iterate. The book factors `V_{m+1} = W S` with `W`
orthonormal, which needs `V_{m+1}` to have full rank; the backbone needs only the two-sided bound
`c ‖w‖₂ ≤ ‖V_{m+1} w‖₂ ≤ C ‖w‖₂`, whose ratio `C/c` is `κ₂(V_{m+1})`, and no factorization.

(6.56)–(6.58) compare the quasi-residual with the residual of the *Galerkin* iterate built on the
same basis — IOM or DIOM for the incomplete orthogonalization, FOM for the Arnoldi basis. That
iterate is `iomOfBasis` (`iomOfBasis_eq_iomFixed`, `iomOfBasis_eq_fomFixed`) and its residual is
`residual_iomOfBasis`. (6.56) is an identity with no nonvanishing hypothesis, where the book's
derivation through `tan θ_m` divides by `h_{mm}^{(m)}`; (6.57) is its reading in norms and (6.58)
is (6.55) with (6.56) substituted.

## §6.5.7: relations between FOM and GMRES

The subsection compares the two Krylov methods built on the same Arnoldi basis: FOM
(`Chapter06/Section04.lean`, the Galerkin iterate) and GMRES (the minimal-residual iterate above).
`ρF` and `ρG` are their residual norms, `ξ` the diagonal entry of `Q_{m-1} H̄_m` of Proposition
6.12, and `Rtilde`, `gtilde`, `ytilde` the "one rotation short" Givens data of Lemma 6.16
(Freund); `ρFmin` is the book's `ρ^F_{m*}`.

Every numbered result is a specialization. (6.62) and Proposition 6.12 come from the Givens layer
of `Numlib/Krylov/Hessenberg.lean`; Propositions 6.13, 6.15, 6.17, Corollary 6.14 and (6.74)–(6.75)
from the specification-level relations of `Numlib/Krylov/Relations.lean`. Only Lemma 6.16, whose
statement is about the *coordinates* `y_m` rather than about the iterates, is proved here, by the
book's own computation (6.72)–(6.73): `R̃_m` and `R_m` differ in the single entry `(m, m)`, where
the former carries `ξ_m` and the latter `ρ_{m-1} = ξ_m/c_m`.

## §6.5.8: residual smoothing

Residual smoothing turns an arbitrary sequence of approximations `(x^O_m, r^O_m)` into a sequence
`(x^S_m, r^S_m)` with monotone residual norms. `smoothEta` is the coefficient `η_m` of
Algorithm 6.14, `mrs` is Algorithm 6.14 itself and `qmrs` its quasi-minimal variant QMRS, whose
scale factors `τ_m` are `qmrsTau`.

The bridge to the backbone is `smoothEta_eq` (the book's `η_m` is `Krylov.smoothingCoeff`) and
`mrs_eq` (Algorithm 6.14 run on `(x^O_m, b - A x^O_m)` computes `Krylov.mrs`); Lemma 6.18
(Weiss) is then `Krylov.inv_sq_norm_smoothing`, and "minimal residual smoothing of FOM gives
GMRES" is `Krylov.IsGalerkinIterate.mrs_isMinResidualIterate`, both from
`Numlib/Krylov/Relations.lean`. The remaining items — (6.77)–(6.79) and their QMRS analogues —
are the short inductions the book performs, shared by the single private lemma
`residual_eq_weighted`. §6.5.8 is real throughout in the book, so this part is written over `ℝ`.

The subsection's closing claim — "QMRS applied to IOM/DIOM yields, in exact arithmetic, the same
sequence as QGMRES/DQGMRES" — is `qmrs_iomOfBasis_eq_qgmres`. The book's route is the one taken:
`τ_m` turns out to be the quasi-residual norm `|γ_{m+1}|` (by (6.57) and (6.47), which give
`1/τ_m² = 1/τ_{m-1}² + 1/ρ_m²`), the smoothing coefficient `η_{m+1}` turns out to be `c_m²`, and
(6.58) is then exactly the QMRS residual recurrence.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

/-! ## §6.5.3 and §6.5.9: Givens rotations and the factorization `Q_m H̄_m = R̄_m` -/

section Givens

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
function of the Hessenberg coefficients alone. `J` of the GMRES part below is its instance at the
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
theorem normal_equations {m : ℕ} (hρ : ∀ k < m, Krylov.givensRho h k ≠ 0) {y : Fin m → 𝕜}
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

end Givens

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

/-! ## §6.5.1–6.5.5: GMRES -/

section GMRES

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
theorem equation_6_27 {m : ℕ} (y : Fin m → 𝕜) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : 𝕜) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) := by
  rw [krylovIterate_eq_sum, toEuclideanLin_V_apply, smul_e₁_eq_firstVec, Hbar_v₁, β_eq_norm_r₀,
    Arnoldi.hessenberg_eq,
    (Arnoldi.hessenbergRelation (op A) (r₀ A b x₀)).residual_eq
      (Arnoldi.smul_vec_zero (op A) (r₀ A b x₀)).symm m y]
  exact Finset.sum_congr rfl fun j _ => by rw [arnoldiCGS_v₁_apply]

/-- (6.28): `‖b - A(x_0 + V_m y)‖₂ = J(y)`, for as many steps as Arnoldi can take. -/
theorem equation_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → 𝕜) :
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
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResidualIterate (op A) b x₀ m x := by
  have hm' : m ≤ Krylov.grade (op A) (r₀ A b x₀) := by rwa [← grade_v₁]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [krylovIterate_eq_sum]
    exact (Krylov.isMinResidualIterate_iff_isMinOn hm' y).2 (by rwa [J_eq] at hy)
  · intro hx
    obtain ⟨y, -, hxe⟩ := hx.exists_mulVec_rotated_eq hm'
    refine ⟨y, ?_, by rw [krylovIterate_eq_sum]; exact hxe⟩
    rw [J_eq]
    exact (Krylov.isMinResidualIterate_iff_isMinOn hm' y).1 (by rwa [← hxe])

/-- The GMRES approximation exists at every step. -/
theorem exists_isGMRESIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) :
    ∃ x, IsGMRESIterate A b x₀ m x := by
  obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (op A) b x₀ m
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
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
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

/-- `J` is the least-squares function `lsq` of the Givens part above, at the Arnoldi
coefficients. -/
theorem J_eq_lsq (m : ℕ) : J A b x₀ m = lsq (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m := by
  funext y
  rw [J, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf, lsq]

/-- The Givens system `R_m y_m = g_m` solved by `gmresY`. -/
theorem mulVec_R_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    R (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m =
      g (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m :=
  mulVec_R_inv_mulVec_g _ _ hR

/-- **Proposition 6.9(2)**: `y_m = R_m⁻¹ g_m` is the minimizer of `J`, and it is the only one. -/
theorem proposition_6_9_2 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
      ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m := by
  rw [J_eq_lsq]
  exact isMinOn_lsq _ _ (hessenberg_coeffs A b x₀) hR

/-- Algorithm 6.9 computes a GMRES approximation. -/
theorem gmresFixed_isGMRESIterate {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    IsGMRESIterate A b x₀ m (gmresFixed A b x₀ m) :=
  ⟨gmresY A b x₀ m, (proposition_6_9_2 A b x₀ hR).1, rfl⟩

/-- Algorithm 6.9 computes the minimal-residual Krylov iterate. -/
theorem gmresFixed_isMinResidualIterate {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
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
      obtain ⟨x, hx⟩ := Krylov.exists_isMinResidualIterate (op A) b x₀ (k + 1)
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
theorem equation_6_41 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    b - op A (gmresFixed A b x₀ m) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ *ᵥ
          Pi.single (Fin.last m) (γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m))) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  have hQ := Qrot_mem_unitaryGroup (arnoldiCoeff A (v₁ A b x₀)) m hρ
  have h1 : (Qrot (arnoldiCoeff A (v₁ A b x₀)) m)ᴴ * Qrot (arnoldiCoeff A (v₁ A b x₀)) m = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff' (A := Qrot (arnoldiCoeff A (v₁ A b x₀)) m)).1 hQ
    rwa [Matrix.star_eq_conjTranspose] at h
  rw [gmresFixed, equation_6_27, smul_e₁_eq_firstVec, Hbar_eq_hessenbergOf]
  congr 2
  conv_lhs => rw [← Matrix.one_mulVec (Krylov.firstVec (β A b x₀ : 𝕜) (m + 1) -
    Krylov.hessenbergOf (arnoldiCoeff A (v₁ A b x₀)) m *ᵥ gmresY A b x₀ m), ← h1]
  rw [← Matrix.mulVec_mulVec, Qrot_mulVec_firstVec_sub,
    gbar_sub_Rbar_mulVec _ _ (hessenberg_coeffs A b x₀) (mulVec_R_gmresY A b x₀ hR)]

/-- **(6.42)**: `‖b - A x_m‖₂ = |γ_{m+1}|`, the residual norm read off the rotated right-hand
side. -/
theorem equation_6_42 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ‖b - op A (gmresFixed A b x₀ m)‖ =
      ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  rw [arnoldiCoeff_v₁] at hρ ⊢
  exact Krylov.IsMinResidualIterate.norm_residual_eq_norm_gamma_of_givensRho_ne_zero
    (by rwa [← grade_v₁]) hρ (gmresFixed_isMinResidualIterate A b x₀ hm hR)

/-- (6.47) and (6.42): if `s_{m+1} = 0` the GMRES approximation at step `m+1` is exact. -/
theorem apply_eq_of_s_eq_zero {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1)))
    (hs : s (arnoldiCoeff A (v₁ A b x₀)) m = 0) : op A (gmresFixed A b x₀ (m + 1)) = b := by
  have h1 := equation_6_42 A b x₀ hm hR
  rw [gamma_succ, hs, neg_zero, zero_mul, norm_zero] at h1
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h1.le)).symm

/-! ### P-6.5: GMRES from Saad (5.7) -/

/-- **P-6.5**: the GMRES coordinates satisfy the normal equations
`H̄_mᴴ H̄_m y_m = H̄_mᴴ (β e_1)` of the least-squares problem (6.29) — the Petrov–Galerkin
formula Saad (5.7) with `V = V_m` and `W = A V_m`. -/
theorem normal_equations_gmresY {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) *ᵥ gmresY A b x₀ m
      = (Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1)) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  rw [Hbar_eq_hessenbergOf, smul_e₁_eq_firstVec]
  exact normal_equations _ _ (hessenberg_coeffs A b x₀) hρ (mulVec_R_gmresY A b x₀ hR)

/-- **P-6.5**: `y_m = (H̄_mᴴ H̄_m)⁻¹ H̄_mᴴ (β e_1)`. -/
theorem problem_6_5 {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᴴ *ᵥ ((β A b x₀ : 𝕜) • e₁ (m + 1))) := by
  have hρ := (isUnit_R_iff _ (hessenberg_coeffs A b x₀)).1 hR
  have hN : IsUnit ((Hbar A (v₁ A b x₀) m)ᴴ * Hbar A (v₁ A b x₀) m) := by
    rw [Hbar_eq_hessenbergOf]
    exact isUnit_conjTranspose_mul_self_hessenbergOf _ (hessenberg_coeffs A b x₀) hρ hR
  rw [← normal_equations_gmresY A b x₀ hR, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hN), Matrix.one_mulVec]

/-! ### Proposition 6.10 and the "at most `n` steps" remark -/

/-- **Proposition 6.10**: for nonsingular `A`, GMRES breaks down at step `j` — that is,
`h_{j+1,j} = 0` — exactly when the approximation `x_j` is already exact. -/
theorem proposition_6_10 (hA : IsUnit A) {j : ℕ} (hj : 0 < j) (hjg : j ≤ grade A (v₁ A b x₀)) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b := by
  have hj1 : j - 1 + 1 = j := by omega
  have hbd : arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔
      Krylov.grade (op A) (r₀ A b x₀) ≤ j := by
    rw [arnoldiCoeff_v₁, ← hj1]
    exact Arnoldi.coeff_succ_self_eq_zero_iff (op A) (r₀ A b x₀) (j - 1)
  have hx := gmresFixed_isMinResidualIterate A b x₀ hjg (isUnit_R_of_isUnit A b x₀ hA hjg)
  rw [hbd]
  refine ⟨fun hg => hx.apply_eq_of_grade_le hg (injective_op_of_isUnit hA).injOn, fun hex => ?_⟩
  exact Krylov.grade_le_of_apply_eq hx.mem hex

/-- §6.5.5: full GMRES converges in at most `n` steps for a nonsingular `A`. -/
theorem gmres_apply_eq (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) : op A (gmres A b x₀ m) = b := by
  have hg : grade A (v₁ A b x₀) ≤ n := grade_le_card A _
  have hmEff : mEff A b x₀ m = grade A (v₁ A b x₀) := min_eq_right (le_trans hg hmn)
  rw [gmres, hmEff]
  exact (gmresFixed_isMinResidualIterate A b x₀ le_rfl
    (isUnit_R_of_isUnit A b x₀ hA le_rfl)).apply_eq_of_grade_le (by rw [← grade_v₁])
    (injective_op_of_isUnit hA).injOn

/-- §6.5.5: some step `m ≤ n` of full GMRES is exact. -/
theorem exists_gmres_apply_eq (hA : IsUnit A) : ∃ m ≤ n, op A (gmres A b x₀ m) = b :=
  ⟨n, le_rfl, gmres_apply_eq A b x₀ hA le_rfl⟩

end GMRES

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
theorem gmresHH_isMinResidualIterate {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (r₀ A b x₀))
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresHH A b x₀ m) := by
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
  obtain ⟨xx, -, huniq⟩ := Krylov.existsUnique_isMinResidualIterate_of_injective
    (injective_op_of_isUnit hA) b x₀ m
  have hmr : m ≤ grade A (r₀ A b x₀) := by
    rw [grade_eq, ← grade_v₁]
    exact hm
  rw [huniq _ (gmresHH_isMinResidualIterate A b x₀ hn hmr hR),
    huniq _ (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm))]

end Householder

/-! ### The numbered results of §6.5, in the book's real setting -/

section BookResultsGMRES

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-- (6.27): `b - A(x_0 + V_m y) = V_{m+1}(β e_1 - H̄_m y)`. -/
theorem residual_eq_6_27 {m : ℕ} (y : Fin m → ℝ) :
    b - op A (krylovIterate A b x₀ m y) =
      Matrix.toEuclideanLin (V A (v₁ A b x₀) (m + 1))
        (WithLp.toLp 2 ((β A b x₀ : ℝ) • e₁ (m + 1) - Hbar A (v₁ A b x₀) m *ᵥ y)) :=
  equation_6_27 A b x₀ y

/-- (6.28): `J(y) = ‖b - A(x_0 + V_m y)‖₂ = ‖β e_1 - H̄_m y‖₂`. -/
theorem residual_eq_6_28 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (y : Fin m → ℝ) :
    ‖b - op A (krylovIterate A b x₀ m y)‖ = J A b x₀ m y :=
  equation_6_28 A b x₀ hm y

/-- **(6.29)–(6.30)**: the GMRES approximation is the unique vector of `x_0 + 𝒦_m` minimizing
`‖b - A x‖₂`; equivalently, it is the backbone's minimal-residual Krylov iterate. -/
theorem gmres_isMinResidualIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    {x : EuclideanSpace ℝ (Fin n)} :
    IsGMRESIterate A b x₀ m x ↔ Krylov.IsMinResidualIterate (op A) b x₀ m x :=
  isGMRESIterate_iff A b x₀ hm

/-- **(6.29)–(6.30)**, uniqueness: for nonsingular `A` there is exactly one GMRES approximation
at step `m`, so "the" GMRES approximation is well defined; `gmresFixed_isGMRESIterate` identifies
it with the vector Algorithm 6.9 computes. -/
theorem gmres_unique {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    ∃! x, IsGMRESIterate A b x₀ m x :=
  existsUnique_isGMRESIterate A b x₀ hm hA

/-- **Proposition 6.9**(1)–(3), the parts the book uses: for nonsingular `A` the triangular
factor `R_m` is nonsingular (so a vanishing `r_{mm}` forces `A` singular); `y_m = R_m⁻¹ g_m` is
the unique minimizer of `J`; and the residual satisfies (6.41) and (6.42). -/
theorem proposition_6_9 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) ∧
      (IsMinOn (J A b x₀ m) Set.univ (gmresY A b x₀ m) ∧
        ∀ y, IsMinOn (J A b x₀ m) Set.univ y → y = gmresY A b x₀ m) ∧
      ‖b - op A (gmresFixed A b x₀ m)‖ =
        ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : ℝ) m‖ :=
  ⟨isUnit_R_of_isUnit A b x₀ hA hm, proposition_6_9_2 A b x₀ (isUnit_R_of_isUnit A b x₀ hA hm),
    equation_6_42 A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)⟩

/-- **Proposition 6.10**: GMRES breaks down at step `j` if and only if `x_j` is exact
(`A` nonsingular). The hypothesis "the first `j` steps were taken" is the book's implicit one. -/
theorem proposition_6_10_book (hA : IsUnit A) (hr : r₀ A b x₀ ≠ 0) {j : ℕ} (hj : 0 < j)
    (hnb : NoBreakdownBefore A (v₁ A b x₀) j) :
    arnoldiCoeff A (v₁ A b x₀) j (j - 1) = 0 ↔ op A (gmresFixed A b x₀ j) = b :=
  proposition_6_10 A b x₀ hA hj ((noBreakdownBefore_iff A _ (norm_v₁ A b x₀ hr) j).1 hnb)

/-- **P-6.5**: GMRES is Saad (5.7) with `V = V_m`, `W = A V_m`: the coordinates `y_m` solve the
normal equations, `y_m = (H̄_mᵀ H̄_m)⁻¹ H̄_mᵀ (β e_1)`. -/
theorem problem_6_5_book {m : ℕ} (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    gmresY A b x₀ m = ((Hbar A (v₁ A b x₀) m)ᵀ * Hbar A (v₁ A b x₀) m)⁻¹ *ᵥ
      ((Hbar A (v₁ A b x₀) m)ᵀ *ᵥ ((β A b x₀ : ℝ) • e₁ (m + 1))) := by
  have hT : (Hbar A (v₁ A b x₀) m)ᴴ = (Hbar A (v₁ A b x₀) m)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [← hT]
  exact problem_6_5 A b x₀ hR

/-- §6.5.2: **Algorithm 6.10** (Householder GMRES). Its scalar `β = e_1ᵀ h_0` is `±‖r_0‖₂`,
the accumulation (6.31)–(6.33) computes `x_0 + ∑_j η_j v_j` in the Householder Arnoldi basis, and
the result is the GMRES approximation of Algorithm 6.9. -/
theorem algorithm_6_10 {m : ℕ} (hn : m + 1 ≤ n) (hm : m ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hR : IsUnit (R (hhCoeff A (r₀ A b x₀)) m)) :
    |βHH A b x₀| = ‖r₀ A b x₀‖ ∧
      gmresHH A b x₀ m = x₀ + ∑ j : Fin m, gmresHHY A b x₀ m j • hhV A (r₀ A b x₀) (j : ℕ) ∧
        gmresHH A b x₀ m = gmresFixed A b x₀ m :=
  ⟨abs_βHH A b x₀ (by omega), gmresHH_eq_add_sum A b x₀ m, gmresHH_eq A b x₀ hn hm hA hR⟩

/-- §6.5.5: the full GMRES algorithm converges in at most `n` steps. -/
theorem gmres_exact_of_card_le (hA : IsUnit A) {m : ℕ} (hmn : n ≤ m) :
    op A (gmres A b x₀ m) = b :=
  gmres_apply_eq A b x₀ hA hmn

end BookResultsGMRES

/-! ## §6.5.6: QGMRES and DQGMRES -/

section QGMRES

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

/-! ### (6.56)–(6.58): DQGMRES versus IOM

The book compares the quasi-minimal-residual iterate above with the *Galerkin* iterate built on
the same, possibly non-orthogonal, basis — IOM or DIOM when the basis is the incomplete
orthogonalization of Algorithm 6.6 (the book writes `x_m^I`, `r_m^I`), FOM when it is the full
Arnoldi basis.  That iterate is `iomOfBasis`. -/

/-- The coordinates `y_m^I = H_m⁻¹(β e_1)` of the Galerkin approximation in the basis `u`. -/
noncomputable def iomOfBasisY (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (Krylov.hessenbergSqOf h m)⁻¹ *ᵥ Krylov.firstVec β m

/-- The Galerkin iterate `x_m^I = x_0 + U_m y_m^I` in the basis `u`: **Algorithm 6.7** (IOM) on
the incomplete orthogonalization basis, Algorithm 6.4 (FOM) on the Arnoldi basis. -/
noncomputable def iomOfBasis (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 (iomOfBasisY h β m))

/-- On the incomplete orthogonalization basis `iomOfBasis` is Algorithm 6.7 (IOM), so
(6.56)–(6.58) below are the book's statements about `x_m^I`. -/
theorem iomOfBasis_eq_iomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) :
    iomOfBasis x₀ (iop A (v₁ A b x₀) k) (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m
      = iomFixed A b x₀ k m := by
  rw [iomOfBasis, iomFixed, iomOfBasisY, iomY, VI, HI, smul_e₁_eq_firstVec]

/-- On the full Arnoldi basis it is Algorithm 6.4 (FOM). -/
theorem iomOfBasis_eq_fomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) :
    iomOfBasis x₀ (arnoldiCGS A (v₁ A b x₀)) (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m
      = fomFixed A b x₀ m := by
  rw [iomOfBasis, fomFixed, iomOfBasisY, fomY, V, H_eq_hessenbergSqOf, smul_e₁_eq_firstVec]

/-- `H_m y_m^I = β e_1` whenever `H_m` is nonsingular, which is what makes `x_m^I` the Galerkin
approximation rather than an arbitrary element of the affine space. -/
theorem hessenbergSqOf_mulVec_iomOfBasisY {h : ℕ → ℕ → 𝕜} {β : 𝕜} {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h m)) :
    Krylov.hessenbergSqOf h m *ᵥ iomOfBasisY h β m = Krylov.firstVec β m := by
  rw [iomOfBasisY, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH), Matrix.one_mulVec]

/-- **Proposition 6.7 in the basis `u`**: `r_m^I = -h_{m+1,m}(e_mᵀ y_m^I) v_{m+1}`.  Like (6.50)
this uses only the Hessenberg relation, so the loss of orthogonality is immaterial — the book's
"the result of Proposition 6.7 is still valid" of §6.4.2. -/
theorem residual_iomOfBasis {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    b - op A (iomOfBasis x₀ u h β (m + 1))
      = -(h (m + 1) m * iomOfBasisY h β (m + 1) (Fin.last m)) • u (m + 1) := by
  rw [iomOfBasis, toEuclideanLin_colMatrix_apply]
  exact hu.residual_eq_of_mulVec_eq hr (Nat.succ_pos m) _
    (hessenbergSqOf_mulVec_iomOfBasisY hH)

/-- **(6.56)**: `γ_{m+1} v_{m+1} = c_m r_m^I`.  Both sides are the scalar
`-(r_{mm}^{(m-1)} h_{m+1,m} e_mᵀ y_m^I)/ρ_m` times `v_{m+1}`, because `c_m = r_{mm}^{(m-1)}/ρ_m`
and `s_m = h_{m+1,m}/ρ_m` carry the same denominator.  The book reads the relation off
`h_{m+1,m}/h_{mm}^{(m)} = tan θ_m`, which divides by `h_{mm}^{(m)}`; the identity as stated needs
no nonvanishing hypothesis and holds with both sides `0` at a breakdown. -/
theorem equation_6_56 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    γ h β (m + 1) • u (m + 1) = c h m • (b - op A (iomOfBasis x₀ u h β (m + 1))) := by
  have hg : Krylov.rotated h m m m * iomOfBasisY h β (m + 1) (Fin.last m) = γ h β m :=
    Krylov.rotated_self_mul_eq_gamma h hu.eq_zero_of_lt β (hessenbergSqOf_mulVec_iomOfBasisY hH)
  have hsub : Krylov.rotated h m (m + 1) m = h (m + 1) m :=
    Krylov.rotated_eq_of_le h m (m + 1) m le_rfl
  have key : γ h β (m + 1)
      = c h m * -(h (m + 1) m * iomOfBasisY h β (m + 1) (Fin.last m)) := by
    rw [gamma_succ, ← hg, show c h m = Krylov.givensC h m from rfl,
      show s h m = Krylov.givensS h m from rfl, Krylov.givensC, Krylov.givensS, hsub]
    ring
  rw [residual_iomOfBasis hu hr hH, smul_smul, ← key]

/-- **(6.57)**: `ρ_m^Q = |c_m| ρ_m`, the quasi-residual norm of QGMRES against the true residual
norm of IOM.  It is (6.56) read in norms, so it needs the basis vector `v_{m+1}` to be a unit
vector — which the incomplete orthogonalization supplies — and nothing else. -/
theorem equation_6_57 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hnorm : ‖u (m + 1)‖ = 1) (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    quasiResidualNorm h β (m + 1)
      = ‖c h m‖ * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ := by
  have h56 := congrArg norm (equation_6_56 hu hr hH)
  rwa [norm_smul, norm_smul, hnorm, mul_one] at h56

/-- **(6.58)**: `r_m^Q = s_m² r_{m-1}^Q + c_m² r_m^I`, the residual recurrence of QGMRES and
DQGMRES with the IOM residual in place of the basis vector.  This is (6.55) with (6.56)
substituted for `γ_{m+1} v_{m+1}`. -/
theorem equation_6_58 {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : 𝔼} {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hR' : IsUnit (R h (m + 1)))
    (hH : IsUnit (Krylov.hessenbergSqOf h (m + 1))) :
    b - op A (qgmres x₀ u h β (m + 1))
      = ((‖s h m‖ : 𝕜) ^ 2) • (b - op A (qgmres x₀ u h β m))
        + ((‖c h m‖ : 𝕜) ^ 2) • (b - op A (iomOfBasis x₀ u h β (m + 1))) := by
  rw [equation_6_55 hu hr hR hR', ← smul_smul, equation_6_56 hu hr hH, smul_smul,
    ← RCLike.mul_conj (c h m)]
  ring_nf

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

/-! ### Theorem 6.11: the Freund–Nachtigal bound -/

/-- QGMRES is the backbone's quasi-minimal-residual iterate: `x_m = x_0 + V_m y_m` with `y_m`
minimizing the quasi-residual `‖β e_1 - H̄_m y‖₂`. This is the identification that carries the
general quasi-minimal-residual theory of `Numlib/Krylov/QuasiMinRes.lean` — which QMR, TFQMR and
FGMRES also use — down to Algorithms 6.12 and 6.13. -/
theorem qgmres_isQuasiMinResidualIterate (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜)
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {m : ℕ} (hR : IsUnit (R h m)) :
    Krylov.IsQuasiMinResidualIterate u h β x₀ m (qgmres x₀ u h β m) :=
  ⟨qgmresY h β m, (isMinOn_lsq h β hh hR).1, by rw [qgmres, toEuclideanLin_colMatrix_apply]⟩

/-- **Theorem 6.11** (Freund–Nachtigal). Assume that `m` steps of DQGMRES have been taken and
that the basis `V_{m+1}` produced by the incomplete orthogonalization satisfies
`c ‖w‖₂ ≤ ‖V_{m+1} w‖₂ ≤ C ‖w‖₂` with `c > 0` — so that `C/c` is its condition number
`κ₂(V_{m+1})`, the ratio of its extreme singular values. If moreover `v_1, …, v_m` span
`𝒦_m(A, r_0)`, then **(6.59)**:
`‖r^Q_m‖₂ ≤ κ₂(V_{m+1}) ‖r^G_m‖₂`, with `r^G_m` the residual of the `m`-th GMRES iterate.

The book proves this by factoring `V_{m+1} = W S` with `W` orthonormal, which needs `V_{m+1}` to
have full rank; the backbone's `Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul` needs neither
the factorization nor the full rank, only the two-sided bound, and gives the same estimate
against *every* point of `x_0 + span {v_1, …, v_m}` — the GMRES iterate being the point that
makes it sharpest. -/
theorem theorem_6_11 {A : Matrix (Fin n) (Fin n) 𝕜} (b x₀ : 𝔼) {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    {β : 𝕜} (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0) {m : ℕ}
    (hR : IsUnit (R h m)) (hm : m ≤ grade A (v₁ A b x₀))
    (hRA : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m))
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => u (i : ℕ))
      = krylov A (r₀ A b x₀) m)
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜,
      c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤ ‖∑ i, w i • u (i : ℕ)‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • u (i : ℕ)‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qgmres x₀ u h β m)‖ ≤ C / c * ‖b - op A (gmresFixed A b x₀ m)‖ := by
  have hmem : gmresFixed A b x₀ m - x₀ ∈
      Submodule.span 𝕜 (Set.range fun i : Fin m => u (i : ℕ)) := by
    rw [hspan, krylov_eq]
    exact (gmresFixed_isMinResidualIterate A b x₀ hm hRA).mem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem
  have hxG : gmresFixed A b x₀ m = x₀ + ∑ j, w j • u (j : ℕ) := by
    rw [hw]
    abel
  rw [hxG]
  exact Krylov.IsQuasiMinResidualIterate.norm_residual_le_mul
    (Krylov.HessenbergRelation₂.of_hessenbergRelation hu) hr hc0 hc hC
    (qgmres_isQuasiMinResidualIterate x₀ u h β hu.eq_zero_of_lt hR) w

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

/-! ### Nondegeneracy from a nonvanishing `γ` -/

/-- A nonvanishing `γ_{m+1}` forces rotation `m` to be nondegenerate: at a breakdown `s_m = 0`
and (6.47) makes `γ_{m+1}` vanish. -/
theorem givensRho_ne_zero_of_gamma_ne_zero {h : ℕ → ℕ → 𝕜} {β : 𝕜} {l : ℕ}
    (hγ : γ h β (l + 1) ≠ 0) : Krylov.givensRho h l ≠ 0 := fun h0 => hγ (by
  rw [gamma_succ, show s h l = Krylov.givensS h l from rfl, Krylov.givensS, h0]
  simp)

/-- `R_k` is nonsingular as soon as `γ_0, …, γ_k` are all nonzero. -/
theorem isUnit_R_of_gamma_ne_zero {h : ℕ → ℕ → 𝕜} {β : 𝕜}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) {k : ℕ} (hγ : ∀ j ≤ k, γ h β j ≠ 0) :
    IsUnit (R h k) :=
  (isUnit_R_iff h hh).2 fun l hl => givensRho_ne_zero_of_gamma_ne_zero (hγ (l + 1) (by omega))

/-- Step `0` of Algorithm 6.12 does nothing. -/
theorem qgmres_zero (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) :
    qgmres x₀ u h β 0 = x₀ := by
  rw [qgmres, toEuclideanLin_colMatrix_apply]
  simp

/-- Step `0` of Algorithm 6.7 does nothing. -/
theorem iomOfBasis_zero (x₀ : 𝔼) (u : ℕ → 𝔼) (h : ℕ → ℕ → 𝕜) (β : 𝕜) :
    iomOfBasis x₀ u h β 0 = x₀ := by
  rw [iomOfBasis, toEuclideanLin_colMatrix_apply]
  simp

end QGMRES

/-! ## §6.5.7: relations between FOM and GMRES -/

section Relations

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### D10: the two residual norms and the Freund data -/

/-- `ρ_m^G = ‖b - A x_m^G‖₂`, the GMRES residual norm after `m` steps (§6.5.7). -/
noncomputable abbrev ρG (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (gmresFixed A b x₀ m)‖

/-- `ρ_m^F = ‖b - A x_m^F‖₂`, the FOM residual norm after `m` steps; the book's `ρ_m^F` is
meaningful exactly when `H_m` is nonsingular (`FOMDefined`). -/
noncomputable abbrev ρF (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ‖b - op A (fomFixed A b x₀ m)‖

/-- Proposition 6.12: `ξ = (Q_{m-1} H̄_m)_{mm}`, the diagonal entry left by the first `m - 1`
rotations (`0`-based: the `(m-1, m-1)` entry of `H̄^{(m-1)}`). -/
noncomputable def ξ (h : ℕ → ℕ → 𝕜) (m : ℕ) : 𝕜 := Krylov.rotated h (m - 1) (m - 1) (m - 1)

/-- Lemma 6.16: `R̃_m`, the top `m × m` block of `Q_{m-1} H̄_m` — the triangular factor one
rotation short of `R_m`. -/
noncomputable def Rtilde (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Krylov.hessenbergSqOf (Krylov.rotated h (m - 1)) m

/-- Lemma 6.16: `g̃_m`, the first `m` entries of `Q_{m-1}(β e_1)`. -/
noncomputable def gtilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  fun i => if (i : ℕ) < m - 1 then Krylov.gvec h c (i : ℕ) else Krylov.gamma h c (m - 1)

/-- Lemma 6.16: `ỹ_m = R̃_m⁻¹ g̃_m`, the coordinates of the FOM approximation in the Givens
description of §6.5.3. -/
noncomputable def ytilde (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) : Fin m → 𝕜 :=
  (Rtilde h m)⁻¹ *ᵥ gtilde h c m

theorem Rtilde_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    Rtilde h m i j = Krylov.rotated h (m - 1) (i : ℕ) (j : ℕ) := rfl

theorem gtilde_last (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) :
    gtilde h c (m + 1) (Fin.last m) = Krylov.gamma h c m := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_right (by simp)

theorem gtilde_castSucc (h : ℕ → ℕ → 𝕜) (c : 𝕜) {m : ℕ} (i : Fin m) :
    gtilde h c (m + 1) i.castSucc = Krylov.gvec h c (i : ℕ) := by
  rw [gtilde, Nat.add_sub_cancel]
  exact ite_eq_left i.isLt

/-! ### `R̃_m` versus `R_m`

The two triangular factors differ in a single entry, which is the whole content of the book's
block computation (6.72)–(6.73). The unfolding `rotated_succ_apply'` is definitional. -/

private theorem rotated_succ_apply' (h : ℕ → ℕ → 𝕜) (k i j : ℕ) :
    Krylov.rotated h (k + 1) i j =
      if i = k then
        starRingEnd 𝕜 (Krylov.givensC h k) * Krylov.rotated h k k j +
          starRingEnd 𝕜 (Krylov.givensS h k) * Krylov.rotated h k (k + 1) j
      else if i = k + 1 then
        -Krylov.givensS h k * Krylov.rotated h k k j +
          Krylov.givensC h k * Krylov.rotated h k (k + 1) j
      else Krylov.rotated h k i j := rfl

/-- Rotation `k` changes only rows `k` and `k + 1`. -/
private theorem rotated_succ_of_ne (h : ℕ → ℕ → 𝕜) {k i : ℕ} (h1 : i ≠ k) (h2 : i ≠ k + 1)
    (j : ℕ) : Krylov.rotated h (k + 1) i j = Krylov.rotated h k i j := by
  rw [rotated_succ_apply', ite_eq_right h1, ite_eq_right h2]

/-- **(6.72)–(6.73)**: `R_{m+1}` and `R̃_{m+1}` agree except in the entry `(m, m)`, where the
former carries `ρ_m` and the latter the pivot `ξ_{m+1}`. -/
theorem R_mulVec_eq_Rtilde_mulVec_add (h : ℕ → ℕ → 𝕜)
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (m : ℕ) (v : Fin (m + 1) → 𝕜) :
    R h (m + 1) *ᵥ v = Rtilde h (m + 1) *ᵥ v +
      Pi.single (Fin.last m)
        ((((Krylov.givensRho h m : ℝ) : 𝕜) - Krylov.rotated h m m m) * v (Fin.last m)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    have h2 : ∀ j : Fin m, Rtilde h (m + 1) (Fin.last m) j.castSucc * v j.castSucc = 0 := by
      intro j
      rw [Rtilde_apply, Nat.add_sub_cancel, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh m m (j : ℕ) j.isLt j.isLt, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)]
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel, Fin.val_last,
      Krylov.rotated_succ_self h m]
    ring
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [R_apply, Rtilde_apply, Nat.add_sub_cancel,
      rotated_succ_of_ne h (by omega) (by omega) (j : ℕ)]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- Step `0` of FOM is the trivial one: `H_0` is the empty matrix. -/
theorem fomDefined_zero : FOMDefined A b x₀ 0 := by
  rw [FOMDefined, Matrix.isUnit_iff_isUnit_det, Matrix.det_isEmpty]
  exact isUnit_one

open scoped Classical in
/-- Proposition 6.15: `ρ^F_{m*}`, the smallest FOM residual norm reached in the first `m` steps,
the steps with a singular `H_i` being skipped. The minimum runs over the `m + 1` indices
`0, …, m`, as the sum of (6.66) does; step `0` contributes the initial residual norm, which the
book writes `ρ^F_0 = ρ^G_0`. -/
noncomputable def ρFmin (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℝ :=
  ((Finset.range (m + 1)).filter (FOMDefined A b x₀)).inf'
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos m), fomDefined_zero A b x₀⟩⟩
    (ρF A b x₀)

/-! ### Nonsingularity of `R_m` and `R̃_m` -/

/-- The Arnoldi coefficients are Hessenberg, the standing hypothesis of the Givens layer. -/
theorem arnoldiCoeff_hessenberg :
    ∀ i j : ℕ, j + 1 < i → arnoldiCoeff A (v₁ A b x₀) i j = 0 :=
  fun _ _ hij => arnoldiCoeff_v₁_eq_zero_of_lt A b x₀ hij

/-- Below the grade no rotation degenerates, so `R_m` is nonsingular with no hypothesis on
`A`. -/
theorem isUnit_R_of_lt_grade {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_hessenberg A b x₀)).2 fun k hk => ?_
  rw [arnoldiCoeff_v₁]
  exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)

/-- A nonsingular `H_{m+1}` gives a nonzero cosine `c_m`
(`Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero`). -/
theorem givensC_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : c (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  rw [arnoldiCoeff_v₁]
  refine (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).1 ?_
  rw [← H_v₁ A b x₀]
  exact hH

/-- The pivot `ξ_{m+1}` is nonzero when `H_{m+1}` is nonsingular. -/
theorem ξ_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ≠ 0 := by
  rw [ξ, Nat.add_sub_cancel]
  intro h0
  exact givensC_ne_zero_of_fomDefined A b x₀ hm hH
    ((Krylov.givensC_eq_zero_iff (arnoldiCoeff A (v₁ A b x₀)) m).2 h0)

/-- `ρ_m` is nonzero when `H_{m+1}` is nonsingular. -/
theorem givensRho_ne_zero_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) m ≠ 0 := by
  refine Krylov.givensRho_ne_zero_of_rotated_ne_zero _ ?_
  have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
  rwa [ξ, Nat.add_sub_cancel] at this

/-- `R_m` is nonsingular as soon as `m` Arnoldi steps have been taken and `H_m` is nonsingular:
the earlier rotations are nondegenerate below the grade, the last one because its pivot is
`ξ_m ≠ 0`. -/
theorem isUnit_R_of_fomDefined {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m) := by
  refine (isUnit_R_iff _ (arnoldiCoeff_hessenberg A b x₀)).2 fun k hk => ?_
  rcases Nat.lt_or_ge (k + 1) m with h1 | h1
  · rw [arnoldiCoeff_v₁]
    exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
  · have hkm : m = k + 1 := by omega
    subst hkm
    exact givensRho_ne_zero_of_fomDefined A b x₀ hm hH

/-- `R̃_{m+1}` is nonsingular under the same hypotheses: its diagonal is `ρ_0, …, ρ_{m-1}, ξ`. -/
theorem isUnit_Rtilde_of_fomDefined {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    IsUnit (Rtilde (arnoldiCoeff A (v₁ A b x₀)) (m + 1)) := by
  rw [Rtilde, Nat.add_sub_cancel]
  refine Krylov.isUnit_hessenbergSqOf_rotated _ (arnoldiCoeff_hessenberg A b x₀)
    (le_refl (m + 1)) fun j hj => ?_
  rcases Nat.lt_or_ge j m with h1 | h1
  · rw [Krylov.rotated_diag _ (arnoldiCoeff_hessenberg A b x₀) h1]
    have hρ : Krylov.givensRho (arnoldiCoeff A (v₁ A b x₀)) j ≠ 0 := by
      rw [arnoldiCoeff_v₁]
      exact Krylov.givensRho_arnoldi_ne_zero (by rw [← grade_v₁]; omega)
    simpa using hρ
  · have hjm : j = m := by omega
    subst hjm
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [ξ, Nat.add_sub_cancel] at this

/-! ### The two iterates as backbone specifications -/

/-- The GMRES residual norm is `|γ_{m+1}|` (6.42), the form used throughout §6.5.7. -/
theorem ρG_eq_norm_gamma {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) :
    ρG A b x₀ m = ‖γ (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀ : 𝕜) m‖ :=
  equation_6_42 A b x₀ hm hR

/-- Algorithm 6.9 computes the minimal-residual iterate at every step below the grade. -/
theorem gmresFixed_isMinResidualIterate_of_lt {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (gmresFixed A b x₀ m) :=
  gmresFixed_isMinResidualIterate A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm)

/-- Algorithm 6.4 computes the Galerkin iterate whenever `H_m` is nonsingular. -/
theorem fomFixed_isGalerkin {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ m) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH hm

/-- `ρ_m^G ≤ ρ_m^F`: the two iterates minimize over the same affine space. -/
theorem ρG_le_ρF {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ m)
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) m)) : ρG A b x₀ m ≤ ρF A b x₀ m :=
  Krylov.norm_residual_minRes_le_galerkin (gmresFixed_isMinResidualIterate A b x₀ hm hR)
    (fomFixed_isGalerkin A b x₀ hm hH)

/-- The GMRES residual norms are nonincreasing (`𝒦_m ⊆ 𝒦_{m+1}`). -/
theorem ρG_succ_le {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hR : IsUnit (R (arnoldiCoeff A (v₁ A b x₀)) (m + 1))) :
    ρG A b x₀ (m + 1) ≤ ρG A b x₀ m :=
  IsMinResidual.norm_residual_le (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm hR)
    (Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m))

/-- The padded GMRES vector `(y_m; 0)` solves the system of step `m + 1` except in its last
entry, which it misses entirely: this is the book's remark that `R_{m+1}` acquires one new row
and one new column. -/
theorem R_mulVec_snoc (h : ℕ → ℕ → 𝕜) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (t : 𝕜) {m : ℕ}
    (yp : Fin m → 𝕜) (hyp : R h m *ᵥ yp = g h t m) :
    R h (m + 1) *ᵥ (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜)
      = g h t (m + 1) - Pi.single (Fin.last m) (Krylov.gvec h t m) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [Fin.sum_univ_castSucc, Fin.snoc_last, mul_zero, add_zero]
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.single_eq_same, g_apply, Fin.val_last, sub_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [R_apply, Fin.val_last, Fin.val_castSucc,
      Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
  · have hlt : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext (by simpa using hc))
      omega
    rw [Pi.single_eq_of_ne hi, sub_zero]
    have hrow : ∀ j : Fin m, R h (m + 1) i j.castSucc *
        (Fin.snoc yp (0 : 𝕜) : Fin (m + 1) → 𝕜) j.castSucc
        = R h m ⟨(i : ℕ), hlt⟩ j * yp j := by
      intro j
      rw [Fin.snoc_castSucc, R_apply, R_apply, Fin.val_castSucc,
        Krylov.rotated_succ_eq_of_lt h hh m (j : ℕ) j.isLt (i : ℕ)]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    have hval := congrFun hyp ⟨(i : ℕ), hlt⟩
    simp only [Matrix.mulVec, dotProduct] at hval
    rw [hval, g_apply, g_apply]

open scoped Classical in
/-- `ρ^F_{m*}` is at most any FOM residual norm of the first `m` steps. -/
theorem ρFmin_le {m i : ℕ} (hi : i ≤ m) (hH : FOMDefined A b x₀ i) :
    ρFmin A b x₀ m ≤ ρF A b x₀ i := by
  rw [ρFmin]
  exact Finset.inf'_le _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hH⟩)

open scoped Classical in
/-- A lower bound for every FOM step of the first `m` bounds `ρ^F_{m*}` from below. -/
theorem le_ρFmin {m : ℕ} {r : ℝ} (h : ∀ i ≤ m, FOMDefined A b x₀ i → r ≤ ρF A b x₀ i) :
    r ≤ ρFmin A b x₀ m := by
  rw [ρFmin]
  refine Finset.le_inf' _ _ fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  exact h i (by have := Finset.mem_range.1 hi1; omega) hi2

end Relations

/-! ### The numbered results of §6.5.7, in the book's real setting -/

section BookResultsRelations

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

/-! #### (6.62) -/

/-- **(6.62)**: `ρ_{m+1}^G = |s_{m+1}| ρ_m^G`. -/
theorem ρG_succ {m : ℕ} (hm : m + 1 < grade A (v₁ A b x₀)) :
    ρG A b x₀ (m + 1) = ‖s (arnoldiCoeff A (v₁ A b x₀)) m‖ * ρG A b x₀ m := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsMinResidualIterate.norm_residual_succ_eq (by rw [← grade_v₁]; exact hm)
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ hm)

/-- **(6.62)**: `ρ_m^G = |s_1 s_2 ⋯ s_m| β`. -/
theorem equation_6_62 {m : ℕ} (hm : m < grade A (v₁ A b x₀)) :
    ρG A b x₀ m
      = (∏ i ∈ Finset.range m, ‖s (arnoldiCoeff A (v₁ A b x₀)) i‖) * β A b x₀ := by
  rw [ρG_eq_norm_gamma A b x₀ hm.le (isUnit_R_of_lt_grade A b x₀ hm), norm_gamma_eq_prod,
    RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-! #### Proposition 6.12 (Brown) and (6.63) -/

/-- **Proposition 6.12**, first form: `ρ_{m+1}^F = ρ_{m+1}^G/|c_{m+1}|`. -/
theorem ρF_eq_div_norm_c {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) / ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ := by
  rw [arnoldiCoeff_v₁]
  exact Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) (fomFixed_isGalerkin A b x₀ hm hH)
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))

/-- The subdiagonal Arnoldi entry survives the first `m` rotations unchanged. -/
private theorem rotated_succ_row (h : ℕ → ℕ → ℝ) (m : ℕ) :
    Krylov.rotated h m (m + 1) m = h (m + 1) m :=
  Krylov.rotated_eq_of_le h m (m + 1) m le_rfl

/-- **(6.63)**: `ρ_{m+1}^F = ρ_{m+1}^G √(1 + h_{m+2,m+1}²/ξ²)`. -/
theorem equation_6_63 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) *
      Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) (m + 1) m ^ 2 /
        ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) ^ 2) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hξ : ξ h (m + 1) = Krylov.rotated h m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated h m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  have hρ0 : Krylov.givensRho h m ≠ 0 := givensRho_ne_zero_of_fomDefined A b x₀ hm hH
  have hρpos : 0 < Krylov.givensRho h m :=
    lt_of_le_of_ne (Krylov.givensRho_nonneg h m) (Ne.symm hρ0)
  have hsq : Krylov.givensRho h m ^ 2 = Krylov.rotated h m m m ^ 2 + h (m + 1) m ^ 2 := by
    rw [Krylov.givensRho_sq, rotated_succ_row, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
  have hc : ‖c h m‖ = |Krylov.rotated h m m m| / Krylov.givensRho h m := by
    rw [show c h m = Krylov.givensC h m from rfl, Krylov.givensC, norm_div,
      RCLike.norm_ofReal, abs_of_nonneg (Krylov.givensRho_nonneg h m), Real.norm_eq_abs]
  have hcne : ‖c h m‖ ≠ 0 := by
    rw [hc]
    exact div_ne_zero (abs_ne_zero.2 hξ0) hρ0
  have habs : (0 : ℝ) < |Krylov.rotated h m m m| := abs_pos.2 hξ0
  have hkey : Real.sqrt (1 + h (m + 1) m ^ 2 / ξ h (m + 1) ^ 2) = 1 / ‖c h m‖ := by
    rw [hξ, hc, one_div_div]
    rw [show (1 : ℝ) + h (m + 1) m ^ 2 / Krylov.rotated h m m m ^ 2
        = (Krylov.givensRho h m / |Krylov.rotated h m m m|) ^ 2 by
      rw [div_pow, sq_abs, hsq]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [ρF_eq_div_norm_c A b x₀ hm hH, hkey, ← hdef, div_eq_mul_one_div]

/-- **Proposition 6.12** (Brown), as stated in the book: if `m ≥ 1` Arnoldi steps have been
taken and `H_m` is nonsingular, then `c_m ≠ 0` and
`ρ_m^F = ρ_m^G/|c_m| = ρ_m^G √(1 + h_{m+1,m}²/ξ²)`. -/
theorem proposition_6_12 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m)
    (hH : FOMDefined A b x₀ m) :
    c (arnoldiCoeff A (v₁ A b x₀)) (m - 1) ≠ 0 ∧
      ρF A b x₀ m = ρG A b x₀ m / ‖c (arnoldiCoeff A (v₁ A b x₀)) (m - 1)‖ ∧
        ρF A b x₀ m = ρG A b x₀ m *
          Real.sqrt (1 + arnoldiCoeff A (v₁ A b x₀) m (m - 1) ^ 2 /
            ξ (arnoldiCoeff A (v₁ A b x₀)) m ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨givensC_ne_zero_of_fomDefined A b x₀ hm hH, ρF_eq_div_norm_c A b x₀ hm hH,
    equation_6_63 A b x₀ hm hH⟩

/-! #### Proposition 6.13 (Cullum–Greenbaum), (6.64)–(6.65) -/

/-- **(6.65)**: `1/(ρ_{m+1}^F)² + 1/(ρ_m^G)² = 1/(ρ_{m+1}^G)²`. -/
theorem equation_6_65 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    1 / ρF A b x₀ (m + 1) ^ 2 + 1 / ρG A b x₀ m ^ 2 = 1 / ρG A b x₀ (m + 1) ^ 2 := by
  have hkey := Krylov.inv_sq_norm_residual_minRes
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm hH))
    (fomFixed_isGalerkin A b x₀ hm hH) (norm_ne_zero_iff.1 h0)
  linarith

/-- **(6.64)** (Cullum–Greenbaum): `ρ_{m+1}^F = ρ_{m+1}^G/√(1 - (ρ_{m+1}^G/ρ_m^G)²)`. -/
theorem proposition_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    ρF A b x₀ (m + 1)
      = ρG A b x₀ (m + 1) /
        Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
  have h65 := equation_6_65 A b x₀ hm hH h0
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have hGG := ρG_succ_le A b x₀ hm hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hp : 0 < ρG A b x₀ m := lt_of_lt_of_le ha hGG
  have hmul : ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2)
      = ρG A b x₀ m ^ 2 * ρG A b x₀ (m + 1) ^ 2 := by
    field_simp at h65
    nlinarith [h65]
  have hgap : 0 < ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2 := by
    have hprod : (0 : ℝ) <
        ρF A b x₀ (m + 1) ^ 2 * (ρG A b x₀ m ^ 2 - ρG A b x₀ (m + 1) ^ 2) := by
      rw [hmul]; positivity
    rcases mul_pos_iff.1 hprod with ⟨-, hgt⟩ | ⟨hlt', -⟩
    · exact hgt
    · nlinarith
  have hnn : (0 : ℝ) ≤ 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := by
    rw [div_pow]
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hs2 : Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) ^ 2
      = 1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2 := Real.sq_sqrt hnn
  have hspos : 0 < Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2) := by
    refine Real.sqrt_pos.2 ?_
    rw [div_pow, sub_pos, div_lt_one (by positivity)]
    nlinarith
  rw [eq_div_iff (ne_of_gt hspos)]
  have hsq : (ρF A b x₀ (m + 1) *
      Real.sqrt (1 - (ρG A b x₀ (m + 1) / ρG A b x₀ m) ^ 2)) ^ 2
      = ρG A b x₀ (m + 1) ^ 2 := by
    rw [mul_pow, hs2, div_pow]
    field_simp
    nlinarith [hmul]
  nlinarith [hsq, ha.le, mul_pos hf hspos]

/-! #### (6.66) and Corollary 6.14, (6.67) -/

/-- **(6.66)**: `∑_{i=0}^m 1/(ρ_i^F)² = 1/(ρ_m^G)²`. -/
theorem equation_6_66 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2 = 1 / ρG A b x₀ m ^ 2 :=
  (Krylov.inv_sq_norm_residual_minRes_eq_sum (xF := fun i => fomFixed A b x₀ i)
    (gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl)))
    (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    (norm_ne_zero_iff.1 h0)).symm

/-- **Corollary 6.14**, (6.67): `ρ_m^G = 1/√(∑_{i=0}^m (1/ρ_i^F)²)`. -/
theorem corollary_6_14 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) (hH : ∀ i ≤ m, FOMDefined A b x₀ i)
    (h0 : ρG A b x₀ m ≠ 0) :
    ρG A b x₀ m = 1 / Real.sqrt (∑ i ∈ Finset.range (m + 1), 1 / ρF A b x₀ i ^ 2) := by
  have ha : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  rw [equation_6_66 A b x₀ hm hH h0,
    show (1 : ℝ) / ρG A b x₀ m ^ 2 = (1 / ρG A b x₀ m) ^ 2 by rw [div_pow, one_pow],
    Real.sqrt_sq (by positivity), one_div_one_div]

/-! #### Proposition 6.15, (6.68) -/

/-- **Proposition 6.15**, (6.68): `ρ_m^G ≤ ρ^F_{m*} ≤ √(m+1) ρ_m^G`.

The book prints `√m` in (6.68), but the inequality displayed two lines above it —
`1/(ρ_m^G)² = ∑_{i=0}^m 1/(ρ_i^F)² ≤ (m+1)/(ρ^F_{m*})²`, which is what (6.66) gives — yields
`√(m+1)`, and the sum really does run over the `m + 1` indices `0, …, m`, `ρ^F_0` being the
initial residual norm. The constant here is the one the book's own derivation supports. -/
theorem proposition_6_15 {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : ∀ i ≤ m, FOMDefined A b x₀ i) :
    ρG A b x₀ m ≤ ρFmin A b x₀ m ∧
      ρFmin A b x₀ m ≤ Real.sqrt (m + 1) * ρG A b x₀ m := by
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm
    (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  constructor
  · refine le_ρFmin A b x₀ fun i hi' _ => ?_
    exact hG.min (fomFixed A b x₀ i)
      (Krylov.subspace_mono (op A) (b - op A x₀) hi'
        (fomFixed_isGalerkin A b x₀ (hi'.trans hm) (hH i hi')).mem)
  · obtain ⟨i, hi, hle⟩ := Krylov.exists_norm_residual_galerkin_le
      (xF := fun i => fomFixed A b x₀ i) hG
      (fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi))
    exact le_trans (ρFmin_le A b x₀ hi (hH i hi)) hle

/-! #### (6.74)–(6.75) -/

/-- **(6.74)**: `x_{m+1}^G = s_{m+1}² x_m^G + c_{m+1}² x_{m+1}^F`. -/
theorem equation_6_74 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1)
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • gmresFixed A b x₀ m +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • fomFixed A b x₀ (m + 1) := by
  set h := arnoldiCoeff A (v₁ A b x₀) with hdef
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hGF := ρG_le_ρF A b x₀ hm hH hRm1
  have ha : 0 < ρG A b x₀ (m + 1) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hf : 0 < ρF A b x₀ (m + 1) := lt_of_lt_of_le ha hGF
  have hF0 : b - op A (fomFixed A b x₀ (m + 1)) ≠ 0 := norm_ne_zero_iff.1 (ne_of_gt hf)
  have hcne : ‖c h m‖ ≠ 0 := norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hratio : ρG A b x₀ (m + 1) ^ 2 / ρF A b x₀ (m + 1) ^ 2 = c h m ^ 2 := by
    rw [ρF_eq_div_norm_c A b x₀ hm hH, div_pow, div_div_eq_mul_div, ← hdef]
    rw [show ‖c h m‖ ^ 2 = c h m ^ 2 by rw [Real.norm_eq_abs, sq_abs]]
    field_simp
  have hcs : 1 - c h m ^ 2 = s h m ^ 2 := by
    have := equation_6_35 h (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    linarith
  have hcomb := Krylov.minRes_eq_combination
    (gmresFixed_isMinResidualIterate_of_lt A b x₀ (by omega))
    (gmresFixed_isMinResidualIterate A b x₀ hm hRm1) (fomFixed_isGalerkin A b x₀ hm hH)
    (injective_op_of_isUnit hA) hF0
  rw [hcomb, hratio, hcs]
  norm_num

/-- Splitting the residual of a convex combination, the vector identity behind (6.75). -/
private theorem residual_combination {N : ℕ}
    (Aop : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (u v w : EuclideanSpace ℝ (Fin N)) {p q : ℝ} (hpq : p + q = 1) :
    u - Aop (p • v + q • w) = p • (u - Aop v) + q • (u - Aop w) := by
  rw [map_add, map_smul, map_smul]
  match_scalars <;> linarith

/-- **(6.75)**: `r_{m+1}^G = s_{m+1}² r_m^G + c_{m+1}² r_{m+1}^F`. -/
theorem equation_6_75 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    b - op A (gmresFixed A b x₀ (m + 1))
      = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (gmresFixed A b x₀ m)) +
        c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))) := by
  have hcs := equation_6_35 (arnoldiCoeff A (v₁ A b x₀))
    (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
  rw [equation_6_74 A b x₀ hm hA hH h0]
  exact residual_combination (op A) b _ _ (by linarith)

/-! #### P-6.14: Proposition 6.12 from (6.75) -/

/-- **P-6.14**: the two residuals on the right of (6.75) are orthogonal, so
`(ρ_{m+1}^G)² = s⁴ (ρ_m^G)² + c⁴ (ρ_{m+1}^F)²`. -/
theorem problem_6_14 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (hH : FOMDefined A b x₀ (m + 1)) (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    inner ℝ (b - op A (gmresFixed A b x₀ m)) (b - op A (fomFixed A b x₀ (m + 1))) = 0 ∧
      ρG A b x₀ (m + 1) ^ 2
        = s (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρG A b x₀ m ^ 2 +
          c (arnoldiCoeff A (v₁ A b x₀)) m ^ 4 * ρF A b x₀ (m + 1) ^ 2 := by
  have hG := gmresFixed_isMinResidualIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hF := fomFixed_isGalerkin A b x₀ hm hH
  have horth : inner ℝ (b - op A (gmresFixed A b x₀ m))
      (b - op A (fomFixed A b x₀ (m + 1))) = 0 :=
    IsPetrovGalerkin.inner_residual_eq_zero hF (Krylov.residual_mem_subspace_succ hG.mem)
  refine ⟨horth, ?_⟩
  have horth' : inner ℝ (s (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
      (b - op A (gmresFixed A b x₀ m)))
      (c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 • (b - op A (fomFixed A b x₀ (m + 1))))
      = (0 : ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, horth, mul_zero, mul_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth'
  rw [← equation_6_75 A b x₀ hm hA hH h0, norm_smul, norm_smul,
    Real.norm_of_nonneg (sq_nonneg (s (arnoldiCoeff A (v₁ A b x₀)) m)),
    Real.norm_of_nonneg (sq_nonneg (c (arnoldiCoeff A (v₁ A b x₀)) m))] at hpy
  nlinarith [hpy]

/-! #### P-6.13: `x_m^G = x_m^F` forces both to be exact -/

/-- **P-6.13**: if `H_m` is nonsingular and the two approximations coincide, both are exact. -/
theorem problem_6_13 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1))
    (heq : gmresFixed A b x₀ (m + 1) = fomFixed A b x₀ (m + 1)) :
    b - op A (gmresFixed A b x₀ (m + 1)) = 0 ∧ b - op A (fomFixed A b x₀ (m + 1)) = 0 := by
  have hRm1 := isUnit_R_of_fomDefined A b x₀ hm hH
  have hcne : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ≠ 0 :=
    norm_ne_zero_iff.2 (givensC_ne_zero_of_fomDefined A b x₀ hm hH)
  have hdiv := ρF_eq_div_norm_c A b x₀ hm hH
  have hG0 : ρG A b x₀ (m + 1) = 0 := by
    by_contra h0
    have hFG : ρF A b x₀ (m + 1) = ρG A b x₀ (m + 1) :=
      congrArg (fun x => ‖b - op A x‖) heq.symm
    rw [hFG, eq_div_iff hcne] at hdiv
    have hc1 : ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ = 1 :=
      mul_left_cancel₀ h0 (by rw [mul_one]; exact hdiv)
    have hs0 : s (arnoldiCoeff A (v₁ A b x₀)) m = 0 := by
      have hcs := equation_6_35 (arnoldiCoeff A (v₁ A b x₀))
        (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
      have hc2 : c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 = 1 := by
        rw [show c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2
            = ‖c (arnoldiCoeff A (v₁ A b x₀)) m‖ ^ 2 by rw [Real.norm_eq_abs, sq_abs], hc1]
        norm_num
      nlinarith
    have : ρG A b x₀ (m + 1) = 0 := by
      rw [ρG_eq_norm_gamma A b x₀ hm hRm1, gamma_succ, hs0, neg_zero, zero_mul, norm_zero]
    exact h0 this
  have hF0 : ρF A b x₀ (m + 1) = 0 := by rw [hdiv, hG0, zero_div]
  exact ⟨norm_eq_zero.1 hG0, norm_eq_zero.1 hF0⟩

/-! #### Proposition 6.17 (Brown) and P-6.9 -/

/-- A Galerkin iterate at step `m + 1` exists exactly when `H_{m+1}` is nonsingular, provided
GMRES has not converged. -/
private theorem exists_galerkin_iff {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    (∃ x, Krylov.IsGalerkinIterate (op A) b x₀ (m + 1) x) ↔ FOMDefined A b x₀ (m + 1) := by
  refine ⟨fun ⟨xF, hF⟩ => ?_, fun hH => ⟨_, fomFixed_isGalerkin A b x₀ hm hH⟩⟩
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hkey := Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC
    (by rw [← grade_v₁]; exact hm) hF hG
  have hcne : Krylov.givensC (Arnoldi.coeff (op A) (r₀ A b x₀)) m ≠ 0 := by
    intro hc
    rw [hc, norm_zero, div_zero] at hkey
    exact h0 (le_antisymm (by rw [← hkey]; exact hG.min xF hF.mem) (norm_nonneg _))
  rw [FOMDefined, H_v₁]
  exact (Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero (by rw [← grade_v₁]; exact hm)).2 hcne

/-- **Proposition 6.17** (Brown) and **P-6.9**: GMRES makes no progress at step `m + 1` exactly
when FOM breaks down there (`H_{m+1}` singular). -/
theorem proposition_6_17 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hA : IsUnit A)
    (h0 : ρG A b x₀ (m + 1) ≠ 0) :
    gmresFixed A b x₀ (m + 1) = gmresFixed A b x₀ m ↔ ¬ FOMDefined A b x₀ (m + 1) := by
  have hG := gmresFixed_isMinResidualIterate_of_lt A b x₀ (show m < grade A (v₁ A b x₀) by omega)
  have hG' := gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_isUnit A b x₀ hA hm)
  have hbb := Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin hG hG'
    (norm_ne_zero_iff.1 h0) (by rw [← grade_v₁]; exact hm)
  rw [← exists_galerkin_iff A b x₀ hm hA h0, ← hbb]
  constructor
  · intro heq
    rw [heq]
  · intro heq
    obtain ⟨z, -, huniq⟩ :=
      Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ (m + 1)
    have hGm : Krylov.IsMinResidualIterate (op A) b x₀ (m + 1) (gmresFixed A b x₀ m) := by
      refine ⟨Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ m) hG.mem, fun y hy => ?_⟩
      rw [← heq]
      exact hG'.min y hy
    rw [huniq _ hG', huniq _ hGm]

/-! #### Lemma 6.16 (Freund), (6.69)–(6.73) -/

/-- **(6.70)**: the last entry of `g_{m+1}` is `c_{m+1} γ_{m+1}`. -/
theorem equation_6_70 (h : ℕ → ℕ → ℝ) (t : ℝ) (m : ℕ) :
    g h t (m + 1) (Fin.last m) = c h m * γ h t m := by
  rw [g_apply, Fin.val_last, Krylov.gvec]
  simp

/-- **(6.71)**: the last diagonal entry of `R_{m+1}` is `ξ_{m+1}/c_{m+1}`. -/
theorem equation_6_71 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀)) (hH : FOMDefined A b x₀ (m + 1)) :
    R (arnoldiCoeff A (v₁ A b x₀)) (m + 1) (Fin.last m) (Fin.last m)
      = ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1) / c (arnoldiCoeff A (v₁ A b x₀)) m := by
  have hξ : ξ (arnoldiCoeff A (v₁ A b x₀)) (m + 1)
      = Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m := by rw [ξ, Nat.add_sub_cancel]
  have hξ0 : Krylov.rotated (arnoldiCoeff A (v₁ A b x₀)) m m m ≠ 0 := by
    have := ξ_ne_zero_of_fomDefined A b x₀ hm hH
    rwa [hξ] at this
  rw [R_apply, Fin.val_last, Krylov.rotated_succ_self, hξ,
    show c (arnoldiCoeff A (v₁ A b x₀)) m = Krylov.givensC (arnoldiCoeff A (v₁ A b x₀)) m from
      rfl,
    Krylov.givensC, div_div_eq_mul_div, eq_div_iff hξ0]
  ring

/-- The core of **Lemma 6.16**, at the level of the Givens data alone: `R_{m+1}` and `R̃_{m+1}`
differ only in the entry `(m, m)`, and the right-hand sides `g_{m+1}` and `g̃_{m+1}` only in
their last entry `c_m γ_m` versus `γ_m`; solving both systems against the padded previous
solution therefore gives two multiples of the same vector. -/
private theorem sub_snoc_eq_smul (h : ℕ → ℕ → ℝ) (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0)
    (t : ℝ) {m : ℕ} (hρ : Krylov.givensRho h m ≠ 0)
    (hRt : IsUnit (Rtilde h (m + 1))) (y : Fin (m + 1) → ℝ) (yp : Fin m → ℝ)
    (hy : R h (m + 1) *ᵥ y = g h t (m + 1)) (hyp : R h m *ᵥ yp = g h t m) :
    y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = Krylov.givensC h m ^ 2 •
        (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hzlast : (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) (Fin.last m) = 0 := Fin.snoc_last _ _
  have hRz := R_mulVec_snoc h hh t yp hyp
  have hρ' : Krylov.rotated h (m + 1) m m ≠ 0 := by
    rw [Krylov.rotated_succ_self]
    simpa using hρ
  have hcdef : Krylov.givensC h m =
      Krylov.rotated h m m m / Krylov.rotated h (m + 1) m m := by
    rw [Krylov.rotated_succ_self, Krylov.givensC]
  have hgv : Krylov.gvec h t m = Krylov.givensC h m * Krylov.gamma h t m := by
    rw [Krylov.gvec]
    simp
  have hRtz : Rtilde h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)
      = R h (m + 1) *ᵥ (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ) := by
    rw [R_mulVec_eq_Rtilde_mulVec_add h hh m _, hzlast, mul_zero, Pi.single_zero, add_zero]
  have hu : R h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gvec h t m) := by
    rw [Matrix.mulVec_sub, hy, hRz]
    abel
  have hw : Rtilde h (m + 1) *ᵥ
      (ytilde h t (m + 1) - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.gamma h t m) := by
    rw [Matrix.mulVec_sub, ytilde, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hRt), Matrix.one_mulVec,
      hRtz, hRz]
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · rw [Pi.sub_apply, Pi.sub_apply, gtilde_last, g_apply, Fin.val_last, Pi.single_eq_same,
        Pi.single_eq_same]
      ring
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      rw [Pi.sub_apply, Pi.sub_apply, gtilde_castSucc, g_apply, Fin.val_castSucc,
        Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
      ring
  have hulast : Krylov.rotated h (m + 1) m m *
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m * Krylov.gamma h t m := by
    have hlast := congrFun hu (Fin.last m)
    simp only [Matrix.mulVec, dotProduct, Pi.single_eq_same] at hlast
    rw [Fin.sum_univ_castSucc] at hlast
    have hz : ∀ j : Fin m, R h (m + 1) (Fin.last m) j.castSucc *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) j.castSucc = 0 := by
      intro j
      rw [R_apply, Fin.val_last, Fin.val_castSucc,
        Krylov.rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hz j, Finset.sum_const_zero, zero_add, R_apply,
      Fin.val_last] at hlast
    rw [hlast, hgv]
  have hentry : Krylov.gvec h t m -
      (Krylov.rotated h (m + 1) m m - Krylov.rotated h m m m) *
        (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ)) (Fin.last m)
      = Krylov.givensC h m ^ 2 * Krylov.gamma h t m := by
    have hxi : Krylov.rotated h m m m
        = Krylov.givensC h m * Krylov.rotated h (m + 1) m m := by
      rw [hcdef]
      field_simp
    rw [hgv, hxi]
    linear_combination (Krylov.givensC h m - 1) * hulast
  have hRtu : Rtilde h (m + 1) *ᵥ (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
      = Pi.single (Fin.last m) (Krylov.givensC h m ^ 2 * Krylov.gamma h t m) := by
    have hsplit := R_mulVec_eq_Rtilde_mulVec_add h hh m
      (y - (Fin.snoc yp (0 : ℝ) : Fin (m + 1) → ℝ))
    rw [hu, ← Krylov.rotated_succ_self h m] at hsplit
    funext i
    rcases eq_or_ne i (Fin.last m) with rfl | hi
    · have hval := congrFun hsplit (Fin.last m)
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_same] at hval
      rw [Pi.single_eq_same, ← hentry]
      linarith [hval]
    · have hval := congrFun hsplit i
      rw [Pi.add_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, add_zero] at hval
      rw [Pi.single_eq_of_ne hi, ← hval]
  refine Matrix.mulVec_injective_iff_isUnit.2 hRt ?_
  rw [hRtu, Matrix.mulVec_smul, hw]
  funext i
  rcases eq_or_ne i (Fin.last m) with rfl | hi
  · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, smul_eq_mul, mul_zero]

/-- **(6.69)** (Lemma 6.16, Freund): `y_{m+1} - (y_m; 0) = c_{m+1}²(ỹ_{m+1} - (y_m; 0))`. -/
theorem lemma_6_16 {m : ℕ} (hm : m + 1 ≤ grade A (v₁ A b x₀))
    (hH : FOMDefined A b x₀ (m + 1)) :
    gmresY A b x₀ (m + 1) - (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)
      = c (arnoldiCoeff A (v₁ A b x₀)) m ^ 2 •
        (ytilde (arnoldiCoeff A (v₁ A b x₀)) (β A b x₀) (m + 1) -
          (Fin.snoc (gmresY A b x₀ m) (0 : ℝ) : Fin (m + 1) → ℝ)) := by
  have hy := mulVec_R_gmresY A b x₀ (isUnit_R_of_fomDefined A b x₀ hm hH)
  have hyp := mulVec_R_gmresY A b x₀
    (isUnit_R_of_lt_grade A b x₀ (show m < grade A (v₁ A b x₀) by omega))
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hy hyp
  exact sub_snoc_eq_smul (arnoldiCoeff A (v₁ A b x₀)) (arnoldiCoeff_hessenberg A b x₀)
    (β A b x₀) (givensRho_ne_zero_of_fomDefined A b x₀ hm hH)
    (isUnit_Rtilde_of_fomDefined A b x₀ hm hH) _ _ hy hyp

end BookResultsRelations

/-! ## §6.5.8: residual smoothing -/

section Smoothing

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-! ### D11: Algorithm 6.14 and QMRS -/

/-- **Algorithm 6.14**, line 3: `η_m = -(r^S_{m-1}, r^O_m - r^S_{m-1})/‖r^O_m - r^S_{m-1}‖₂²`.
The book's inner product `(x, y) = ∑ x_i ȳ_i` is Mathlib's `inner ℝ y x`. -/
noncomputable def smoothEta (s r : 𝔼) : ℝ := -inner ℝ (r - s) s / ‖r - s‖ ^ 2

/-- The book's `η_m` is the backbone's residual-minimizing smoothing coefficient. -/
theorem smoothEta_eq (s r : 𝔼) : smoothEta s r = Krylov.smoothingCoeff s r := by
  rw [smoothEta, Krylov.smoothingCoeff, inner_neg_right]
  simp [RCLike.ofReal_real_eq_id]

/-- **Algorithm 6.14** (minimal residual smoothing, Weiss): the smoothed pair
`(x^S_m, r^S_m)` produced from an original sequence `(x^O_m, r^O_m)`. -/
noncomputable def mrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
    let p := mrs xO rO m
    let η := smoothEta p.2 (rO (m + 1))
    (p.1 + η • (xO (m + 1) - p.1), p.2 + η • (rO (m + 1) - p.2))

/-- The smoothed approximations `x^S_m` of Algorithm 6.14. -/
noncomputable abbrev mrsX (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).1

/-- The smoothed residuals `r^S_m` of Algorithm 6.14. -/
noncomputable abbrev mrsR (xO rO : ℕ → 𝔼) (m : ℕ) : 𝔼 := (mrs xO rO m).2

/-- The coefficient `η_{m+1}` of Algorithm 6.14 (`0`-based). -/
noncomputable abbrev mrsEta (xO rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  smoothEta (mrsR xO rO m) (rO (m + 1))

theorem mrsX_zero (xO rO : ℕ → 𝔼) : mrsX xO rO 0 = xO 0 := rfl

theorem mrsR_zero (xO rO : ℕ → 𝔼) : mrsR xO rO 0 = rO 0 := rfl

theorem mrsX_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsX xO rO (m + 1) = mrsX xO rO m + mrsEta xO rO m • (xO (m + 1) - mrsX xO rO m) := rfl

theorem mrsR_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    mrsR xO rO (m + 1) = mrsR xO rO m + mrsEta xO rO m • (rO (m + 1) - mrsR xO rO m) := rfl

/-- QMRS (§6.5.8): `τ_0 = ρ_0` and `1/τ_m² = 1/τ_{m-1}² + 1/ρ_m²`, with `ρ_j = ‖r^O_j‖₂`. -/
noncomputable def qmrsTau (rO : ℕ → 𝔼) : ℕ → ℝ
  | 0 => ‖rO 0‖
  | m + 1 => Real.sqrt (1 / (1 / qmrsTau rO m ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2))

/-- QMRS (§6.5.8): the coefficient `η_m = τ_{m-1}²/(τ_{m-1}² + ρ_m²)` (`0`-based). -/
noncomputable def qmrsEta (rO : ℕ → 𝔼) (m : ℕ) : ℝ :=
  qmrsTau rO m ^ 2 / (qmrsTau rO m ^ 2 + ‖rO (m + 1)‖ ^ 2)

/-- **QMRS** (§6.5.8): Algorithm 6.14 with `η_m` replaced by the quasi-residual ratio. -/
noncomputable def qmrs (xO rO : ℕ → 𝔼) : ℕ → 𝔼 × 𝔼
  | 0 => (xO 0, rO 0)
  | m + 1 =>
    let p := qmrs xO rO m
    (p.1 + qmrsEta rO m • (xO (m + 1) - p.1), p.2 + qmrsEta rO m • (rO (m + 1) - p.2))

theorem qmrs_zero (xO rO : ℕ → 𝔼) : qmrs xO rO 0 = (xO 0, rO 0) := rfl

theorem qmrs_succ (xO rO : ℕ → 𝔼) (m : ℕ) :
    qmrs xO rO (m + 1) =
      ((qmrs xO rO m).1 + qmrsEta rO m • (xO (m + 1) - (qmrs xO rO m).1),
        (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)) := rfl

/-! ### The bridge to `Krylov.mrs` -/

/-- **D11**: Algorithm 6.14 applied to a sequence of iterates and their residuals computes the
backbone's minimal-residual smoothing, and its second component really is the residual of the
first. -/
theorem mrs_eq (A : Matrix (Fin n) (Fin n) ℝ) (b : 𝔼) (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j)) (m : ℕ) :
    mrsX xO rO m = Krylov.mrs (op A) b xO m ∧
      mrsR xO rO m = b - op A (Krylov.mrs (op A) b xO m) := by
  induction m with
  | zero => exact ⟨rfl, by rw [mrsR_zero, hr 0, Krylov.mrs]⟩
  | succ m ih =>
    obtain ⟨ihx, ihr⟩ := ih
    have hη : mrsEta xO rO m =
        Krylov.smoothingCoeff (b - op A (Krylov.mrs (op A) b xO m)) (b - op A (xO (m + 1))) := by
      rw [mrsEta, ihr, hr (m + 1), smoothEta_eq]
    have hx : mrsX xO rO (m + 1) = Krylov.mrs (op A) b xO (m + 1) := by
      rw [mrsX_succ, ihx, hη, Krylov.mrs]
    refine ⟨hx, ?_⟩
    rw [mrsR_succ, ihr, hη, hr (m + 1), Krylov.mrs]
    simp only [map_add, map_smul, map_sub]
    module

/-! ### Lemma 6.18 (Weiss), (6.76)–(6.77) -/

/-- A vector orthogonal to `r^O_0, …, r^O_m` is orthogonal to `r^S_m`: the smoothed residual is
a combination of the original ones. -/
theorem inner_mrsR_eq_zero (xO rO : ℕ → 𝔼) (w : 𝔼) :
    ∀ m : ℕ, (∀ i ≤ m, inner ℝ w (rO i) = 0) → inner ℝ w (mrsR xO rO m) = 0 := by
  intro m
  induction m with
  | zero => intro h; rw [mrsR_zero]; exact h 0 le_rfl
  | succ m ih =>
    intro h
    rw [mrsR_succ, inner_add_right, real_inner_smul_right, inner_sub_right,
      ih fun i hi => h i (by omega), h (m + 1) le_rfl]
    ring

/-- **(6.76)** (Lemma 6.18, Weiss): if `r^O_{m+1} ⟂ r^S_m` then
`1/‖r^S_{m+1}‖² = 1/‖r^S_m‖² + 1/‖r^O_{m+1}‖²`. -/
theorem equation_6_76 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0) (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 := by
  have hkey := Krylov.inv_sq_norm_smoothing (𝕜 := ℝ) h0 h1 horth
  rw [mrsR_succ, mrsEta, smoothEta_eq]
  exact hkey

/-- **(6.77)** (Lemma 6.18, Weiss): if `r^O_{m+1} ⟂ r^S_m` then
`η_{m+1} = ‖r^S_m‖²/(‖r^S_m‖² + ‖r^O_{m+1}‖²)`. -/
theorem equation_6_77 (xO rO : ℕ → 𝔼) {m : ℕ}
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    mrsEta xO rO m
      = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) := by
  have hnum : inner ℝ (rO (m + 1) - mrsR xO rO m) (mrsR xO rO m) = -‖mrsR xO rO m‖ ^ 2 := by
    rw [inner_sub_left, horth, real_inner_self_eq_norm_sq]
    ring
  have hden : ‖rO (m + 1) - mrsR xO rO m‖ ^ 2
      = ‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2 := by
    rw [norm_sub_sq_real, horth]
    ring
  rw [mrsEta, smoothEta, hnum, hden, neg_neg]

/-! ### (6.78)–(6.79) and the QMRS identities

Both the smoothed and the quasi-smoothed residual obey the same recurrence, once the weight is
written in terms of the partial sums `∑_{i ≤ j} 1/ρ_i²`; this single induction gives (6.79) and
its QMRS analogue. -/

/-- The scalar identity behind (6.79). -/
private theorem smul_combination_eq {S rho : ℝ} (hS : 0 < S) (hr : 0 < rho) (u v : 𝔼) :
    (1 - S⁻¹ / (S⁻¹ + rho)) • (S⁻¹ • u) + (S⁻¹ / (S⁻¹ + rho)) • v
      = (S + 1 / rho)⁻¹ • (u + (1 / rho) • v) := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hr0 : rho ≠ 0 := ne_of_gt hr
  have hd : S⁻¹ + rho ≠ 0 := ne_of_gt (by have := inv_pos.2 hS; linarith)
  have hd2 : S + 1 / rho ≠ 0 := ne_of_gt (by have := one_div_pos.2 hr; linarith)
  have e1 : (1 - S⁻¹ / (S⁻¹ + rho)) * S⁻¹ = (S + 1 / rho)⁻¹ := by
    field_simp
    ring
  have e2 : S⁻¹ / (S⁻¹ + rho) = (S + 1 / rho)⁻¹ * (1 / rho) := by
    field_simp
    ring
  rw [smul_smul, e1, smul_add, smul_smul, e2]

private theorem sum_inv_sq_pos {rO : ℕ → 𝔼} {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (0 : ℝ) < ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 :=
  Finset.sum_pos (fun j hj => one_div_pos.2 (pow_pos
    (norm_pos_iff.2 (hr j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))) 2)) ⟨0, by simp⟩

/-- The induction behind **(6.79)**: a sequence started at `r^O_0` and obeying the smoothing
recurrence with the weights of Lemma 6.18 is the weighted average of the original residuals. -/
private theorem residual_eq_weighted (rO S : ℕ → 𝔼) (hS0 : S 0 = rO 0) {m : ℕ}
    (hr : ∀ j ≤ m, rO j ≠ 0)
    (hstep : ∀ j < m, S (j + 1) = S j +
      ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ /
        ((∑ i ∈ Finset.range (j + 1), 1 / ‖rO i‖ ^ 2)⁻¹ + ‖rO (j + 1)‖ ^ 2)) •
        (rO (j + 1) - S j)) :
    S m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  induction m with
  | zero =>
    have hne : ‖rO 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (hr 0 le_rfl))
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hS0, smul_smul, inv_mul_cancel₀ (one_div_ne_zero hne), one_smul]
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hSpos := sum_inv_sq_pos hrk
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hcomb : ∀ (t : ℝ) (a v : 𝔼), a + t • (v - a) = (1 - t) • a + t • v := by
      intro t a v
      module
    rw [hstep k (by omega), ih hrk (fun j hj => hstep j (by omega)), hcomb,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1),
      Finset.sum_range_succ (fun j => (1 / ‖rO j‖ ^ 2) • rO j) (k + 1)]
    exact smul_combination_eq hSpos hrpos _ _

/-! #### The QMRS scale factors -/

theorem qmrsTau_pos (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) : 0 < qmrsTau rO m := by
  induction m with
  | zero => rw [qmrsTau]; exact norm_pos_iff.2 (hr 0 le_rfl)
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    rw [qmrsTau]
    refine Real.sqrt_pos.2 (one_div_pos.2 ?_)
    have : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 := by positivity
    have : (0 : ℝ) < 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    linarith

/-- The defining relation of QMRS: `1/τ_m² = ∑_{j ≤ m} 1/ρ_j²`. -/
theorem inv_qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    1 / qmrsTau rO m ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [qmrsTau]; simp
  | succ k ih =>
    have hk := ih fun j hj => hr j (by omega)
    have hkpos := qmrsTau_pos rO fun j hj => hr j (Nat.le_succ_of_le hj)
    have hrpos : (0 : ℝ) < ‖rO (k + 1)‖ ^ 2 :=
      pow_pos (norm_pos_iff.2 (hr (k + 1) le_rfl)) 2
    have hsum : (0 : ℝ) < 1 / qmrsTau rO k ^ 2 + 1 / ‖rO (k + 1)‖ ^ 2 := by positivity
    rw [qmrsTau, Real.sq_sqrt (le_of_lt (one_div_pos.2 hsum)), one_div_one_div,
      Finset.sum_range_succ, ← hk]

/-- `τ_m² = (∑_{j ≤ m} 1/ρ_j²)⁻¹`. -/
theorem qmrsTau_sq (rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    qmrsTau rO m ^ 2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ := by
  rw [← inv_qmrsTau_sq rO hr, one_div, inv_inv]

/-- **(6.79) for QMRS**: the quasi-smoothed residual is the weighted average of the original
residuals. -/
theorem qmrs_eq_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0) :
    (qmrs xO rO m).2 = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  refine residual_eq_weighted rO (fun j => (qmrs xO rO j).2) rfl hr fun j hj => ?_
  rw [qmrs_succ, qmrsEta, qmrsTau_sq rO fun i hi => hr i (by omega)]

/-- **(6.78) for QMRS**: the quasi-smoothed residual is the convex combination
`r^S_{m+1} = (ρ²/(ρ² + τ_m²)) r^S_m + (τ_m²/(ρ² + τ_m²)) r^O_{m+1}`. -/
theorem qmrs_eq_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : rO (m + 1) ≠ 0) :
    (qmrs xO rO (m + 1)).2
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • (qmrs xO rO m).2 +
        (qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2)) • rO (m + 1) := by
  have hrpos : (0 : ℝ) < ‖rO (m + 1)‖ ^ 2 := pow_pos (norm_pos_iff.2 hr) 2
  have hden : ‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2 ≠ 0 := by positivity
  have he : qmrsEta rO m = qmrsTau rO m ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [qmrsEta, add_comm (qmrsTau rO m ^ 2)]
  have he' : 1 - qmrsEta rO m
      = ‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + qmrsTau rO m ^ 2) := by
    rw [he]
    field_simp
    ring
  rw [qmrs_succ]
  simp only
  rw [show (qmrs xO rO m).2 + qmrsEta rO m • (rO (m + 1) - (qmrs xO rO m).2)
      = (1 - qmrsEta rO m) • (qmrs xO rO m).2 + qmrsEta rO m • rO (m + 1) by module, he', he]

/-! #### Algorithm 6.14 under the orthogonality hypothesis of Lemma 6.18 -/

/-- Under the hypothesis of Lemma 6.18, `1/‖r^S_m‖² = ∑_{j ≤ m} 1/ρ_j²`: the smoothed residual
norms are the QMRS scale factors. -/
theorem inv_sq_norm_mrsR (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    1 / ‖mrsR xO rO m‖ ^ 2 = ∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2 := by
  induction m with
  | zero => rw [mrsR_zero]; simp
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hne : mrsR xO rO k ≠ 0 := by
      intro h0
      have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO k‖ ^ 2 := hk ▸ sum_inv_sq_pos hrk
      rw [h0, norm_zero] at hpos
      norm_num at hpos
    rw [equation_6_76 xO rO hne (hr (k + 1) le_rfl) (horth k (by omega)), hk,
      Finset.sum_range_succ (fun j => 1 / ‖rO j‖ ^ 2) (k + 1)]

/-- Under the hypothesis of Lemma 6.18 the smoothed residual norms are exactly the QMRS scale
factors `τ_m`. -/
theorem norm_mrsR_eq_qmrsTau (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    ‖mrsR xO rO m‖ = qmrsTau rO m := by
  have h1 := inv_sq_norm_mrsR xO rO hr horth
  have h2 := inv_qmrsTau_sq rO hr
  have hne : ‖mrsR xO rO m‖ ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < 1 / ‖mrsR xO rO m‖ ^ 2 := h1 ▸ sum_inv_sq_pos hr
    rw [h0] at hpos
    norm_num at hpos
  have hsq : ‖mrsR xO rO m‖ ^ 2 = qmrsTau rO m ^ 2 := by
    have h3 : (‖mrsR xO rO m‖ ^ 2)⁻¹ = (qmrsTau rO m ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact h1.trans h2.symm
    exact inv_injective h3
  have hpos := qmrsTau_pos rO hr
  nlinarith [norm_nonneg (mrsR xO rO m), hpos, hsq]

/-- **§6.5.8**: under the hypothesis of Lemma 6.18, Algorithm 6.14 and QMRS coincide. -/
theorem mrs_eq_qmrs (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrs xO rO m = qmrs xO rO m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hrk : ∀ j ≤ k, rO j ≠ 0 := fun j hj => hr j (by omega)
    have hk := ih hrk fun j hj => horth j (by omega)
    have hη : mrsEta xO rO k = qmrsEta rO k := by
      rw [equation_6_77 xO rO (horth k (by omega)), qmrsEta,
        norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)]
    rw [qmrs_succ, ← hk]
    have hx : mrs xO rO (k + 1) =
        (mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k),
          mrsR xO rO k + mrsEta xO rO k • (rO (k + 1) - mrsR xO rO k)) := rfl
    rw [hx, hη]

/-- **(6.78)**: `r^S_{m+1} = (ρ²/(ρ² + τ_m²)) r^S_m + (τ_m²/(ρ² + τ_m²)) r^O_{m+1}` with
`τ_m = ‖r^S_m‖`. -/
theorem equation_6_78 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m + 1, rO j ≠ 0)
    (horth : ∀ j < m + 1, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO (m + 1)
      = (‖rO (m + 1)‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • mrsR xO rO m +
        (‖mrsR xO rO m‖ ^ 2 / (‖rO (m + 1)‖ ^ 2 + ‖mrsR xO rO m‖ ^ 2)) • rO (m + 1) := by
  have hrk : ∀ j ≤ m, rO j ≠ 0 := fun j hj => hr j (by omega)
  have hτ := norm_mrsR_eq_qmrsTau xO rO hrk fun j hj => horth j (by omega)
  have hq := qmrs_eq_6_78 xO rO (hr (m + 1) le_rfl)
  have h1 : mrsR xO rO (m + 1) = (qmrs xO rO (m + 1)).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)
  have h2 : mrsR xO rO m = (qmrs xO rO m).2 :=
    congrArg Prod.snd (mrs_eq_qmrs xO rO hrk fun j hj => horth j (by omega))
  rw [h1, hq, ← h2, hτ]

/-- **(6.79)**: the smoothed residual is the weighted average
`r^S_m = (∑_{j ≤ m} r^O_j/ρ_j²)/(∑_{j ≤ m} 1/ρ_j²)`.

The book prints both sums of (6.79) from `j = 1`, but the identity it combines with (6.78) to get
them — displayed just above as `1/τ_j² = ∑_{i=0}^j 1/ρ_i²` — starts at `0`, and so does
Algorithm 6.14, whose line 1 sets `r^S_0 = r^O_0`. At `m = 1` the printed range would give
`r^S_1 = r^O_1`. The sums here therefore run over `0, …, m`. -/
theorem equation_6_79 (xO rO : ℕ → 𝔼) {m : ℕ} (hr : ∀ j ≤ m, rO j ≠ 0)
    (horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR xO rO j) = 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  rw [show mrsR xO rO m = (qmrs xO rO m).2 from
    congrArg Prod.snd (mrs_eq_qmrs xO rO hr horth)]
  exact qmrs_eq_6_79 xO rO hr

/-- **Lemma 6.18** (Weiss), as stated in the book: under `r^O_{m+1} ⟂ r^S_m` the smoothed
residual norms satisfy (6.76) and the coefficient is given by (6.77). -/
theorem lemma_6_18 (xO rO : ℕ → 𝔼) {m : ℕ} (h0 : mrsR xO rO m ≠ 0)
    (h1 : rO (m + 1) ≠ 0)
    (horth : inner ℝ (rO (m + 1)) (mrsR xO rO m) = 0) :
    1 / ‖mrsR xO rO (m + 1)‖ ^ 2 = 1 / ‖mrsR xO rO m‖ ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2 ∧
      mrsEta xO rO m
        = ‖mrsR xO rO m‖ ^ 2 / (‖mrsR xO rO m‖ ^ 2 + ‖rO (m + 1)‖ ^ 2) :=
  ⟨equation_6_76 xO rO h0 h1 horth, equation_6_77 xO rO horth⟩

/-! ### §6.5.8: QMRS applied to IOM/DIOM yields QGMRES/DQGMRES

The book's "it can easily be shown", proved here from (6.47), (6.57) and (6.58). The QMRS scale
factor `τ_m` turns out to be exactly the quasi-residual norm `|γ_{m+1}|`, and the smoothing
coefficient `η_{m+1}` exactly `c_m²`; (6.58) then *is* the QMRS residual recurrence. -/

section QMRSIOM

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ : EuclideanSpace ℝ (Fin n)}
  {u : ℕ → EuclideanSpace ℝ (Fin n)} {h : ℕ → ℕ → ℝ} {β : ℝ}

/-- **§6.5.8**: quasi-minimal residual smoothing of the IOM/DIOM iterates produces, step for step,
the QGMRES/DQGMRES iterates, and its scale factor `τ_m` is the quasi-residual norm `|γ_{m+1}|`.

The hypothesis `hγ` — the quasi-residual has not vanished — is the algorithm's own termination
test; it supplies `c_m ≠ 0` and `s_m ≠ 0` through (6.57) and (6.47), which is what makes `τ_m` and
`η_{m+1}` well defined. It is stated as a bound `∀ j ≤ m` rather than as `∀ j`, which would be
unsatisfiable in finite dimension. `hH` is that IOM itself is defined at every step. -/
theorem qmrs_iomOfBasis_eq_qgmres (hA : IsUnit A)
    (hu : Krylov.HessenbergRelation (op A) u h) (hr : b - op A x₀ = β • u 0)
    (hnorm : ∀ i, ‖u i‖ = 1) {m : ℕ} (hγ : ∀ j ≤ m, γ h β j ≠ 0)
    (hH : ∀ j ≤ m, IsUnit (Krylov.hessenbergSqOf h j)) :
    qmrs (fun j => iomOfBasis x₀ u h β j) (fun j => b - op A (iomOfBasis x₀ u h β j)) m
        = (qgmres x₀ u h β m, b - op A (qgmres x₀ u h β m)) ∧
      qmrsTau (fun j => b - op A (iomOfBasis x₀ u h β j)) m = ‖γ h β m‖ := by
  induction m with
  | zero =>
    have h0 : iomOfBasis x₀ u h β 0 = x₀ := iomOfBasis_zero x₀ u h β
    refine ⟨by rw [qmrs_zero, h0, qgmres_zero], ?_⟩
    rw [qmrsTau, h0, hr, norm_smul, hnorm 0, mul_one]
    rfl
  | succ m ih =>
    obtain ⟨ihq, ihτ⟩ := ih (fun j hj => hγ j (by omega)) (fun j hj => hH j (by omega))
    have hhh := hu.eq_zero_of_lt
    -- the four quantities of the book's computation
    have h57 : ‖γ h β (m + 1)‖
        = ‖c h m‖ * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ := by
      have h := equation_6_57 hu hr (hnorm (m + 1)) (hH (m + 1) le_rfl)
      rwa [quasiResidualNorm] at h
    have h47 : ‖γ h β (m + 1)‖ = ‖s h m‖ * ‖γ h β m‖ := by
      rw [gamma_succ, norm_mul, norm_neg]
    have hγ1 : ‖γ h β (m + 1)‖ ≠ 0 := norm_ne_zero_iff.2 (hγ (m + 1) le_rfl)
    have hcc : ‖c h m‖ ≠ 0 := fun hc => hγ1 (by rw [h57, hc, zero_mul])
    have hss : ‖s h m‖ ≠ 0 := fun hc => hγ1 (by rw [h47, hc, zero_mul])
    have hgm : ‖γ h β m‖ ≠ 0 := fun hc => hγ1 (by rw [h47, hc, mul_zero])
    have hp : ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ≠ 0 :=
      fun hc => hγ1 (by rw [h57, hc, mul_zero])
    have hcs : ‖c h m‖ ^ 2 + ‖s h m‖ ^ 2 = 1 :=
      norm_c_sq_add_norm_s_sq h (givensRho_ne_zero_of_gamma_ne_zero (hγ (m + 1) le_rfl))
    have e1 : ‖γ h β (m + 1)‖ ^ 2 = ‖s h m‖ ^ 2 * ‖γ h β m‖ ^ 2 := by rw [h47]; ring
    have e2 : ‖γ h β (m + 1)‖ ^ 2
        = ‖c h m‖ ^ 2 * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2 := by rw [h57]; ring
    -- `τ_{m+1} = |γ_{m+2}|`
    have hτ : qmrsTau (fun j => b - op A (iomOfBasis x₀ u h β j)) (m + 1)
        = ‖γ h β (m + 1)‖ := by
      have hsum : 1 / ‖γ h β m‖ ^ 2
            + 1 / ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2
          = 1 / ‖γ h β (m + 1)‖ ^ 2 := by
        rw [div_add_div _ _ (pow_ne_zero 2 hgm) (pow_ne_zero 2 hp),
          div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2) * e1
          + (‖γ h β m‖ ^ 2) * e2
          + (‖γ h β m‖ ^ 2 * ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2) * hcs
      rw [qmrsTau, ihτ, hsum, one_div_one_div, Real.sqrt_sq (norm_nonneg _)]
    -- `η_{m+1} = c_m²`
    have hη : qmrsEta (fun j => b - op A (iomOfBasis x₀ u h β j)) m = ‖c h m‖ ^ 2 := by
      have hden : (0 : ℝ) < ‖γ h β m‖ ^ 2
          + ‖b - op A (iomOfBasis x₀ u h β (m + 1))‖ ^ 2 :=
        add_pos_of_pos_of_nonneg (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hgm)) 2)
          (sq_nonneg _)
      rw [qmrsEta, ihτ, div_eq_iff hden.ne']
      linear_combination (-1 : ℝ) * e1 + e2 - (‖γ h β m‖ ^ 2) * hcs
    -- the residual recurrence (6.58) with `‖s_m‖² = 1 - ‖c_m‖²`
    have hs2 : ‖s h m‖ ^ 2 = 1 - ‖c h m‖ ^ 2 := by linarith
    have hRm : IsUnit (R h m) := isUnit_R_of_gamma_ne_zero hhh fun j hj => hγ j (by omega)
    have hRm1 : IsUnit (R h (m + 1)) := isUnit_R_of_gamma_ne_zero hhh fun j hj => hγ j hj
    have hres : b - op A (qgmres x₀ u h β (m + 1))
        = b - op A (qgmres x₀ u h β m + ‖c h m‖ ^ 2 •
            (iomOfBasis x₀ u h β (m + 1) - qgmres x₀ u h β m)) := by
      rw [equation_6_58 hu hr hRm hRm1 (hH (m + 1) le_rfl)]
      simp only [RCLike.ofReal_real_eq_id, id_eq, map_add, map_smul, map_sub]
      rw [hs2]
      module
    have hstep : qgmres x₀ u h β (m + 1)
        = qgmres x₀ u h β m + ‖c h m‖ ^ 2 •
            (iomOfBasis x₀ u h β (m + 1) - qgmres x₀ u h β m) :=
      injective_op_of_isUnit hA (sub_right_injective hres)
    refine ⟨?_, hτ⟩
    rw [qmrs_succ, ihq, hη, hstep]
    simp only [Prod.mk.injEq, true_and]
    rw [map_add, map_smul, map_sub]
    module

end QMRSIOM

end Smoothing

/-! ### §6.5.8: minimal residual smoothing of FOM gives GMRES -/

section FOM

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The smoothed iterate stays in the affine space `x_0 + 𝒦_m`. -/
theorem mrsX_sub_mem (xO rO : ℕ → 𝔼) {m : ℕ}
    (hO : ∀ i ≤ m, xO i - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) i) :
    mrsX xO rO m - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) m := by
  induction m with
  | zero => rw [mrsX_zero]; exact hO 0 le_rfl
  | succ k ih =>
    have hmono := Krylov.subspace_mono (op A) (b - op A x₀) (Nat.le_succ k)
    have ihk := ih fun i hi => hO i (by omega)
    rw [mrsX_succ, show mrsX xO rO k + mrsEta xO rO k • (xO (k + 1) - mrsX xO rO k) - x₀
        = (mrsX xO rO k - x₀) + mrsEta xO rO k • ((xO (k + 1) - x₀) - (mrsX xO rO k - x₀)) by
      module]
    exact Submodule.add_mem _ (hmono ihk)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hO (k + 1) le_rfl) (hmono ihk)))

/-- **§6.5.8**: minimal residual smoothing of a sequence of Galerkin (FOM) iterates produces the
minimal-residual (GMRES) iterates. -/
theorem mrs_isMinResidualIterate (hA : IsUnit A) (xO rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (xO j)) (m : ℕ)
    (hO : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (xO i)) :
    Krylov.IsMinResidualIterate (op A) b x₀ m (mrsX xO rO m) := by
  rw [(mrs_eq A b xO rO hr m).1]
  exact Krylov.IsGalerkinIterate.mrs_isMinResidualIterate (injective_op_of_isUnit hA) m hO

/-- **§6.5.8**: minimal residual smoothing of the FOM approximations produces exactly the GMRES
approximations. The FOM residuals are mutually orthogonal, so Lemma 6.18 applies at every step
and the smoothed residual norms satisfy (6.66)–(6.67); GMRES minimizes over the same subspace,
so the two sequences agree. -/
theorem mrs_fom_eq_gmres (hA : IsUnit A) (rO : ℕ → 𝔼)
    (hr : ∀ j, rO j = b - op A (fomFixed A b x₀ j)) {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀))
    (hH : ∀ i ≤ m, FOMDefined A b x₀ i) (h0 : ρG A b x₀ m ≠ 0) :
    mrsX (fomFixed A b x₀) rO m = gmresFixed A b x₀ m := by
  have hgal : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (fomFixed A b x₀ i) :=
    fun i hi => fomFixed_isGalerkin A b x₀ (hi.trans hm) (hH i hi)
  have hG := gmresFixed_isMinResidualIterate A b x₀ hm (isUnit_R_of_fomDefined A b x₀ hm (hH m le_rfl))
  have hrne : ∀ j ≤ m, rO j ≠ 0 := by
    intro j hj hz
    rw [hr j] at hz
    have hAy : op A (fomFixed A b x₀ j) = b := (sub_eq_zero.1 hz).symm
    have hex := hG.apply_eq_of_exists
      (Krylov.subspace_mono (op A) (b - op A x₀) hj (hgal j hj).mem) hAy
    exact h0 (norm_eq_zero.2 (by rw [hex, sub_self]))
  have hpair : ∀ i ≤ m, ∀ j ≤ m, i ≠ j → inner ℝ (rO i) (rO j) = 0 := by
    intro i hi j hj hij
    rw [hr i, hr j]
    exact Krylov.IsGalerkinIterate.inner_residual_eq_zero (hgal i hi) (hgal j hj) hij
  have horth : ∀ j < m, inner ℝ (rO (j + 1)) (mrsR (fomFixed A b x₀) rO j) = 0 := fun j hj =>
    inner_mrsR_eq_zero (fomFixed A b x₀) rO _ j fun i hi =>
      hpair (j + 1) (by omega) i (by omega) (by omega)
  have hsum := inv_sq_norm_mrsR (fomFixed A b x₀) rO hrne horth
  have h66 := equation_6_66 A b x₀ hm hH h0
  have heq := mrs_eq A b (fomFixed A b x₀) rO hr m
  have hres : mrsR (fomFixed A b x₀) rO m
      = b - op A (mrsX (fomFixed A b x₀) rO m) := by rw [heq.1]; exact heq.2
  have hGpos : 0 < ρG A b x₀ m := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have hnorm : ‖b - op A (mrsX (fomFixed A b x₀) rO m)‖ = ρG A b x₀ m := by
    rw [← hres]
    have hsum' : 1 / ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = 1 / ρG A b x₀ m ^ 2 := by
      rw [hsum, ← h66]
      exact Finset.sum_congr rfl fun j _ => by rw [hr j]
    have hne : ‖mrsR (fomFixed A b x₀) rO m‖ ≠ 0 := by
      intro hz
      rw [hz] at hsum'
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at hsum'
      exact (one_div_pos.2 (pow_pos hGpos 2)).ne hsum'
    have hsq : ‖mrsR (fomFixed A b x₀) rO m‖ ^ 2 = ρG A b x₀ m ^ 2 := by
      field_simp at hsum'
      linarith
    nlinarith [norm_nonneg (mrsR (fomFixed A b x₀) rO m), hGpos, hsq]
  have hmres : Krylov.IsMinResidualIterate (op A) b x₀ m (mrsX (fomFixed A b x₀) rO m) := by
    refine ⟨mrsX_sub_mem A b x₀ _ rO fun i hi => (hgal i hi).mem, fun y hy => ?_⟩
    rw [hnorm]
    exact hG.min y hy
  obtain ⟨z, -, huniq⟩ :=
    Krylov.existsUnique_isMinResidualIterate_of_injective (injective_op_of_isUnit hA) b x₀ m
  rw [huniq _ hmres, huniq _ hG]

/-- **(6.79)** for a sequence of Galerkin (FOM) iterates, read off the backbone directly. -/
theorem residual_mrs_eq (hA : IsUnit A) (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    {m : ℕ} (hO : ∀ i ≤ m, Krylov.IsGalerkinIterate (op A) b x₀ i (xO i))
    (h0 : ∀ j ≤ m, rO j ≠ 0) :
    mrsR xO rO m = (∑ j ∈ Finset.range (m + 1), 1 / ‖rO j‖ ^ 2)⁻¹ •
      ∑ j ∈ Finset.range (m + 1), (1 / ‖rO j‖ ^ 2) • rO j := by
  have hkey := Krylov.residual_mrs_eq (injective_op_of_isUnit hA) m hO
    (fun j hj => by rw [← hr j]; exact h0 j hj)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hkey
  rw [(mrs_eq A b xO rO hr m).2, hkey]
  simp only [← hr]

/-- **P-6.26**: the directions `x^O_{j+1} - x^S_j` produced by Algorithm 6.14 from a sequence of
Galerkin iterates are `AᵀA`-orthogonal, the hypothesis of Lemma 6.21 (GCR / ORTHOMIN). -/
theorem problem_6_26 (hA : IsUnit A) (xO rO : ℕ → 𝔼) (hr : ∀ j, rO j = b - op A (xO j))
    (hO : ∀ m, Krylov.IsGalerkinIterate (op A) b x₀ m (xO m)) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (op A (xO (i + 1) - mrsX xO rO i)) (op A (xO (j + 1) - mrsX xO rO j)) = 0 := by
  have hmemS : ∀ k, mrsX xO rO k - x₀ ∈ Krylov.subspace (op A) (b - op A x₀) k :=
    fun k => mrsX_sub_mem A b x₀ xO rO fun i _ => (hO i).mem
  have hres : ∀ k, mrsR xO rO k = b - op A (mrsX xO rO k) := fun k => by
    have h := mrs_eq A b xO rO hr k
    rw [h.1]
    exact h.2
  have hminres : ∀ k, Krylov.IsMinResidualIterate (op A) b x₀ k (mrsX xO rO k) :=
    fun k => mrs_isMinResidualIterate A b x₀ hA xO rO hr k fun i _ => hO i
  have key : ∀ p q : ℕ, p < q →
      inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (op A (xO (q + 1) - mrsX xO rO q)) = 0 := by
    intro p q hpq
    have hmem : op A (xO (p + 1) - mrsX xO rO p)
        ∈ (Krylov.subspace (op A) (b - op A x₀) q).map (op A) := by
      refine Submodule.mem_map_of_mem ?_
      rw [show xO (p + 1) - mrsX xO rO p = (xO (p + 1) - x₀) - (mrsX xO rO p - x₀) by abel]
      exact Submodule.sub_mem _
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hO (p + 1)).mem)
        (Krylov.subspace_mono (op A) (b - op A x₀) (by omega) (hmemS p))
    have h1 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (mrsR xO rO q) = 0 := by
      rw [hres q]
      exact (Submodule.mem_orthogonal _ _).1
        (Krylov.IsMinResidualIterate.residual_mem_orthogonal (hminres q)) _ hmem
    have h2 : inner ℝ (op A (xO (p + 1) - mrsX xO rO p)) (rO (q + 1)) = 0 := by
      rw [hr (q + 1)]
      exact IsPetrovGalerkin.inner_residual_eq_zero (hO (q + 1))
        (Krylov.map_subspace_le (op A) (b - op A x₀) q hmem)
    have hd : op A (xO (q + 1) - mrsX xO rO q) = mrsR xO rO q - rO (q + 1) := by
      rw [hres q, hr (q + 1), map_sub]
      abel
    rw [hd, inner_sub_right, h1, h2, sub_zero]
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [real_inner_comm]
    exact key j i h

end FOM

end SaadSparse.Chapter06
