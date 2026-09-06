import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter07.Section02

/-!
# Saad §7.3: BCG and QMR

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §7.3.

**Algorithm 7.3** (BCG) is `bcg`, the five-vector recurrence `(x, r, r*, p, p*)` with
`α_j = (r_j, r*_j)/(A p_j, p*_j)` and `β_j = (r_{j+1}, r*_{j+1})/(r_j, r*_j)`; `bcg_eq` identifies
it with the backbone `BCG.iterate`, so that Proposition 7.2 (`proposition_7_2`) and the
Petrov–Galerkin identification (`bcg_isPetrovGalerkin`) are read off `Numlib/Krylov/BiLanczos.lean`.
`bcg_eq_lanczosSolve` is the content of (7.10)–(7.12): BCG computes the Algorithm 7.2 iterate.
The book gets there through the `LDU` factorization `T_m = L_m U_m` and the direction matrices
`P_m = V_m U_m⁻¹`, `P*_m = W_m L_m⁻ᴴ`; here it is one line, because both iterates are
Petrov–Galerkin approximations on the same pair of spaces and `T_m` nonsingular is exactly the
nondegeneracy that makes such an approximation unique.

**Algorithm 7.4** (QMR) is `qmr`, and it is not a new algorithm: it is Algorithm 6.12 run on the
two-sided Lanczos basis, so the whole QGMRES layer of `Chapter06/Section05.lean` applies at
`u := bilanczosV`, `h := bilanczosCoeff`. `qmr_isQuasiMinResIterate` is that instantiation, and
after it (7.16)–(7.31) are the backbone quasi-minimal-residual theorems of
`Numlib/Krylov/QuasiMinRes.lean` read through it: Proposition 7.3 is
`Krylov.IsQuasiMinResIterate.norm_residual_le`, Theorem 7.4 is
`Krylov.IsQuasiMinResIterate.norm_residual_le_mul` — the same theorem as Saad's Theorem 6.11 —
and (7.23), (7.24), Proposition 7.5 are `Krylov.inv_sq_norm_gamma`,
`Krylov.inv_sq_norm_gamma_eq_sum` and `Krylov.exists_norm_gamma_div_givensC_le`.

The conditioning `κ₂(V_{m+1})` of Theorem 7.4 enters as the ratio `C/c` of a two-sided bound
`c ‖y‖₂ ≤ ‖V_{m+1} y‖₂ ≤ C ‖y‖₂` on the coordinate map; such a `c > 0` exists because `V_{m+1}`
has full rank (`problem_7_2`), which is why the full-rank hypothesis the book has to assume in
Theorem 6.11 can be dropped here.

From (7.18) on the book normalizes the Lanczos vectors to unit 2-norm — a different scaling from
Algorithm 7.1, admissible by (7.1). That is the hypothesis `∀ j, ‖v_j‖₂ = 1` carried by
`equation_7_20` and everything after it.

Indices are `0`-based as in `Chapter07/Section01.lean`: `qmrV A b x₀ w₁ j` is the book's
`v_{j+1}`, `Chapter06.γ h β m` its `γ_{m+1}` and `Chapter06.c h m` its `c_{m+1}`.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### §7.3.1: Algorithm 7.3, the biconjugate gradient algorithm -/

section BCG

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- One pass through lines 4–10 of **Algorithm 7.3**, on the state `(x_j, r_j, r*_j, p_j, p*_j)`.
The backbone record `BCG.State` carries exactly that data. -/
noncomputable def bcgStep (s : BCG.State (EuclideanSpace 𝕜 (Fin n))) :
    BCG.State (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 s.rs s.r / inner 𝕜 s.ps (op A s.p)
  let r : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A s.p
  let rs : EuclideanSpace 𝕜 (Fin n) := s.rs - starRingEnd 𝕜 α • op Aᴴ s.ps
  let β : 𝕜 := inner 𝕜 rs r / inner 𝕜 s.rs s.r
  { x := s.x + α • s.p
    r := r
    rs := rs
    p := r + β • s.p
    ps := rs + starRingEnd 𝕜 β • s.ps }

/-- **Algorithm 7.3** (BCG) run for `k` steps from `x_0`, with the shadow residual `r*_0`
initialized to an arbitrary `rs₀` (the book's `r_0^*`, subject only to `(r_0, r_0^*) ≠ 0`). -/
noncomputable def bcg (k : ℕ) : BCG.State (EuclideanSpace 𝕜 (Fin n)) :=
  (bcgStep A)^[k] { x := x₀, r := b - op A x₀, rs := rs₀, p := b - op A x₀, ps := rs₀ }

private theorem bcgStep_eq (s : BCG.State (EuclideanSpace 𝕜 (Fin n))) :
    bcgStep A s = BCG.step (op A) (op Aᴴ) s := rfl

/-- **The bridge to the backbone**: the book's Algorithm 7.3 computes `BCG.iterate` of `op A` and
its adjoint `op Aᴴ`. -/
theorem bcg_eq (k : ℕ) : bcg A b x₀ rs₀ k = BCG.iterate (op A) (op Aᴴ) b x₀ rs₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [bcg, Function.iterate_succ_apply', ← bcg, ih, bcgStep_eq, ← BCG.iterate_succ]

/-- **Algorithm 7.3**, lines 1 and 2: the initial state of BCG. -/
@[simp] theorem bcg_zero :
    bcg A b x₀ rs₀ 0
      = { x := x₀, r := b - op A x₀, rs := rs₀, p := b - op A x₀, ps := rs₀ } := rfl

end BCG

section BCGBreakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Algorithm 7.3** has not broken down before step `m`: neither of the two denominators of
lines 4 and 8 vanishes. The adjoint relation `(A x, y) = (x, Aᴴ y)`, which the backbone takes as
data, is automatic for matrices, so this is the whole of the book's hypothesis. -/
structure BCGNoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Prop where
  /-- The numerator of `α_j`, which is the denominator of `β_j`, does not vanish. -/
  inner_residual_ne_zero : ∀ k < m, inner 𝕜 (bcg A b x₀ rs₀ k).rs (bcg A b x₀ rs₀ k).r ≠ 0
  /-- The denominator of `α_j` does not vanish. -/
  inner_apply_direction_ne_zero : ∀ k < m,
    inner 𝕜 (bcg A b x₀ rs₀ k).ps (op A (bcg A b x₀ rs₀ k).p) ≠ 0

/-- Running `m` steps without breakdown entails running `k ≤ m` steps without breakdown. -/
theorem BCGNoBreakdown.mono {k : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) (hk : k ≤ m) :
    BCGNoBreakdown A b x₀ rs₀ k :=
  ⟨fun j hj => h.inner_residual_ne_zero j (hj.trans_le hk),
    fun j hj => h.inner_apply_direction_ne_zero j (hj.trans_le hk)⟩

/-- The surface no-breakdown hypothesis is the backbone one. -/
theorem BCGNoBreakdown.toBCG (h : BCGNoBreakdown A b x₀ rs₀ m) :
    BCG.NoBreakdown (op A) (op Aᴴ) b x₀ rs₀ m where
  adjoint := inner_op_conjTranspose A
  inner_residual_ne_zero k hk := by
    have := h.inner_residual_ne_zero k hk
    rwa [bcg_eq] at this
  inner_apply_direction_ne_zero k hk := by
    have := h.inner_apply_direction_ne_zero k hk
    rwa [bcg_eq] at this

/-- **Proposition 7.2**, (7.13)–(7.14) (also P-7.10): the BCG residuals are biorthogonal,
`(r_j, r*_i) = 0`, and the BCG directions are `A`-biconjugate, `(A p_j, p*_i) = 0`, for `i ≠ j`. -/
theorem proposition_7_2 (h : BCGNoBreakdown A b x₀ rs₀ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m)
    (hij : i ≠ j) :
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ i).r = 0 ∧
      inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ i).p) = 0 := by
  simp only [bcg_eq]
  exact ⟨BCG.inner_residual_dualResidual_eq_zero h.toBCG hi hj hij,
    BCG.inner_dualDirection_apply_direction_eq_zero h.toBCG hi hj hij⟩

/-- **Saad §7.3.1**: the BCG iterate is the Petrov–Galerkin approximation onto `𝒦_m(A, r_0)`
orthogonally to `𝒦_m(Aᴴ, r*_0)` — the projection process the section opens with. -/
theorem bcg_isPetrovGalerkin (h : BCGNoBreakdown A b x₀ rs₀ m) :
    IsPetrovGalerkin (op A) b x₀ (Chapter06.krylov A (Chapter06.r₀ A b x₀) m)
      (Chapter06.krylov Aᴴ rs₀ m) (bcg A b x₀ rs₀ m).x := by
  simp only [Chapter06.krylov_eq, bcg_eq]
  exact BCG.isPetrovGalerkin h.toBCG

/-- **(7.5)** entry by entry: `(A v_j, w_i) = T_{ij}` while Algorithm 7.1 has not broken down. -/
private theorem inner_bilanczosW_apply_bilanczosV {v w : EuclideanSpace 𝕜 (Fin n)} {k : ℕ}
    (hnb : NoBreakdown A v w k) {i j : ℕ} (hi : i ≤ k) (hj : j + 1 ≤ k) :
    inner 𝕜 (bilanczosW A v w i) (op A (bilanczosV A v w j)) = bilanczosCoeff A v w i j := by
  obtain ⟨M, rfl⟩ : ∃ M, k = M + 1 := ⟨k - 1, by omega⟩
  rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
  exact BiLanczos.inner_dualVec_apply_vec hnb.toBiLanczos hi (by omega)

/-- The Petrov–Galerkin pair `(𝒦_m(A, v_1), 𝒦_m(Aᴴ, w_1))` is nondegenerate exactly when `T_m` is
nonsingular: if `z` lies in the trial space and `A z` is orthogonal to the test space, then by
(7.5) the coordinates of `z` solve `T_m y = 0`, so `z = 0`. This is what makes the Algorithm 7.2
iterate the *unique* Petrov–Galerkin approximation. -/
private theorem eq_zero_of_apply_mem_orthogonal {v w : EuclideanSpace 𝕜 (Fin n)}
    (hnb : NoBreakdown A v w m) (hT : IsUnit (T A v w m)) {z : EuclideanSpace 𝕜 (Fin n)}
    (hz : z ∈ Chapter06.krylov A v m) (hAz : op A z ∈ (Chapter06.krylov Aᴴ w m)ᗮ) : z = 0 := by
  rw [← (proposition_7_1_span hnb).1] at hz
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hz
  have hTy : T A v w m *ᵥ y = 0 := by
    funext i
    have hmem : bilanczosW A v w (i : ℕ) ∈ Chapter06.krylov Aᴴ w m := by
      rw [← (proposition_7_1_span hnb).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h0 : inner 𝕜 (bilanczosW A v w (i : ℕ)) (op A z) = 0 :=
      (Submodule.mem_orthogonal _ _).1 hAz _ hmem
    have hentry : ∀ j : Fin m,
        inner 𝕜 (bilanczosW A v w (i : ℕ)) (op A (bilanczosV A v w (j : ℕ)))
          = T A v w m i j := fun j =>
      inner_bilanczosW_apply_bilanczosV hnb (le_of_lt i.2) j.2
    rw [← hy, map_sum, inner_sum] at h0
    simp only [map_smul, inner_smul_right, hentry] at h0
    rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, ← h0]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hy0 : y = 0 := by
    have h1 : (T A v w m)⁻¹ *ᵥ (T A v w m *ᵥ y) = 0 := by rw [hTy, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hT),
      Matrix.one_mulVec] at h1
  rw [← hy, hy0]
  simp

/-- **(7.10)–(7.12)**: BCG computes the Algorithm 7.2 iterate. The book derives this from the
`LDU` factorization `T_m = L_m U_m` and the direction matrices `P_m = V_m U_m⁻¹`,
`P*_m = W_m L_m⁻ᴴ`; both iterates are Petrov–Galerkin approximations on `𝒦_m(A, r_0)` against
`𝒦_m(Aᴴ, r*_0)`, and a nonsingular `T_m` is exactly the nondegeneracy that makes such an
approximation unique. -/
theorem bcg_eq_lanczosSolve (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hnb : NoBreakdown A (Chapter06.v₁ A b x₀) (w₁ A b x₀ rs₀) m)
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) (w₁ A b x₀ rs₀) m))
    (hr : Chapter06.r₀ A b x₀ ≠ 0) (hw : inner 𝕜 (Chapter06.v₁ A b x₀) rs₀ ≠ 0) :
    (bcg A b x₀ rs₀ m).x = lanczosSolve A b x₀ (w₁ A b x₀ rs₀) m := by
  have hK : Chapter06.krylov A (Chapter06.v₁ A b x₀) m
      = Chapter06.krylov A (Chapter06.r₀ A b x₀) m := by
    rw [Chapter06.v₁_def,
      Chapter06.krylov_smul A _ (inv_ne_zero (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hr)))]
  have hL : Chapter06.krylov Aᴴ (w₁ A b x₀ rs₀) m = Chapter06.krylov Aᴴ rs₀ m := by
    rw [show w₁ A b x₀ rs₀ = (inner 𝕜 (Chapter06.v₁ A b x₀) rs₀)⁻¹ • rs₀ from rfl,
      Chapter06.krylov_smul Aᴴ _ (inv_ne_zero hw)]
  have hlan := lanczosSolve_isPetrovGalerkin hnb hT
  rw [hK, hL] at hlan
  refine (bcg_isPetrovGalerkin h).eq_of_forall hlan fun z hz hAz => ?_
  exact eq_zero_of_apply_mem_orthogonal hnb hT (by rw [hK]; exact hz) (by rw [hL]; exact hAz)

end BCGBreakdown

/-! ### §7.3.2: Algorithm 7.4, the quasi-minimal residual method -/

section QMR

/-- The basis QMR expands its iterate in: the primal two-sided Lanczos vectors of Algorithm 7.1
started from `v_1 = r_0/β` and the dual vector `w_1`. -/
noncomputable abbrev qmrV (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → EuclideanSpace 𝕜 (Fin n) :=
  bilanczosV A (Chapter06.v₁ A b x₀) w₁

/-- The tridiagonal coefficient array `T̄_m` of (7.15) that QMR rotates, at the starting pair
`(v_1, w_1) = (r_0/β, w_1)`. -/
noncomputable abbrev qmrCoeff (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n)) : ℕ → ℕ → 𝕜 :=
  bilanczosCoeff A (Chapter06.v₁ A b x₀) w₁

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 7.4** (QMR): Algorithm 6.12 (QGMRES) run on the two-sided Lanczos basis. The
minimization of (7.17) is over the *quasi*-residual `‖β e_1 - T̄_m y‖₂`, and its solution is the
same rotated triangular back-substitution `y_m = R_m⁻¹ g_m` as in GMRES. -/
noncomputable def qmr (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  Chapter06.qgmres x₀ (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m

/-- The starting relation `r_0 = β v_1` in the form the backbone consumes. -/
private theorem smul_qmrV_zero :
    b - op A x₀ = (Chapter06.β A b x₀ : 𝕜) • qmrV A b x₀ w₁ 0 := (smul_v₁_eq_r₀ A b x₀).symm

/-- `ρ^Q_m` is the norm of the backbone's `γ_m`; the unfolding `rw` cannot do by itself. -/
private theorem quasiResidualNorm_eq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) :
    Chapter06.quasiResidualNorm h β m = ‖Krylov.gamma h β m‖ := rfl

private theorem gamma_eq (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) :
    Chapter06.γ h β m = Krylov.gamma h β m := rfl

private theorem givensC_eq (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Chapter06.c h m = Krylov.givensC h m := rfl

private theorem givensS_eq (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Chapter06.s h m = Krylov.givensS h m := rfl

/-- `‖β‖ = ‖r_0‖₂`: the scalar `β` is the real number `‖r_0‖` seen in `𝕜`. -/
private theorem norm_beta : ‖(Chapter06.β A b x₀ : 𝕜)‖ = ‖Chapter06.r₀ A b x₀‖ := by
  rw [Chapter06.β_eq_norm_r₀, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-- **(7.19) at the level of the rotations**: when the Galerkin system `H_{m+1} y = β e_1` is
solvable, `γ_{m+2} = c_{m+1}(-h_{m+2,m+1} y_m)` — the quasi-residual scalar is `c` times the
Galerkin residual scalar. No hypothesis is needed at a degenerate rotation, where both sides
vanish. -/
private theorem gamma_succ_eq_givensC_mul {h : ℕ → ℕ → 𝕜}
    (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (β : 𝕜) {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (Krylov.hessenbergSqOf h (m + 1)).mulVec y = Krylov.firstVec β (m + 1)) :
    Krylov.gamma h β (m + 1)
      = Krylov.givensC h m * -(h (m + 1) m * y ⟨m, Nat.lt_succ_self m⟩) := by
  rw [Krylov.gamma_succ, ← Krylov.rotated_self_mul_eq_gamma h hh β hy, Krylov.givensS,
    Krylov.givensC, Krylov.rotated_eq_of_le h m (m + 1) m le_rfl]
  ring

/-- A nonvanishing rotated pivot makes rotation `m` nondegenerate. -/
private theorem givensRho_ne_zero_of_rotated_self (h : ℕ → ℕ → 𝕜) {m : ℕ}
    (hd : Krylov.rotated h m m m ≠ 0) : Krylov.givensRho h m ≠ 0 := by
  intro h0
  have hsq := Krylov.givensRho_sq h m
  rw [h0] at hsq
  have h1 : ‖Krylov.rotated h m m m‖ ^ 2 = 0 := by
    nlinarith [norm_nonneg (Krylov.rotated h m (m + 1) m), sq_nonneg (0 : ℝ)]
  exact hd (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

/-- If the quasi-residual scalar `γ_{m+1}` does not vanish and the Galerkin system at step `m + 1`
is solvable, then the rotation cosine `c_{m+1}` does not vanish — the Galerkin iterate exists. -/
private theorem givensC_ne_zero {h : ℕ → ℕ → 𝕜} (hh : ∀ i j : ℕ, j + 1 < i → h i j = 0) (β : 𝕜)
    {m : ℕ} {y : Fin (m + 1) → 𝕜}
    (hy : (Krylov.hessenbergSqOf h (m + 1)).mulVec y = Krylov.firstVec β (m + 1))
    (h0 : Krylov.gamma h β m ≠ 0) : Krylov.givensC h m ≠ 0 := by
  have hd : Krylov.rotated h m m m ≠ 0 := fun hc =>
    h0 (by rw [← Krylov.rotated_self_mul_eq_gamma h hh β hy, hc, zero_mul])
  exact div_ne_zero hd (RCLike.ofReal_ne_zero.2 (givensRho_ne_zero_of_rotated_self h hd))

/-- The quasi-residual scalars vanish from the first vanishing one onwards. -/
private theorem gamma_eq_zero_of_le (h : ℕ → ℕ → 𝕜) (β : 𝕜) {k m : ℕ} (hk : k ≤ m)
    (hc : Krylov.gamma h β k = 0) : Krylov.gamma h β m = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using hc
  | succ d ih =>
    rw [← Nat.add_assoc, Krylov.gamma_succ, ih (Nat.le_add_right k d), mul_zero]

/-- The Galerkin residual norms `ρ^F` in the shape the harmonic identities of
`Numlib/Krylov/QuasiMinRes.lean` take them: `ρ^F_0 = ‖β‖` and `ρ^F_{k+1} = ‖γ_{k+1}‖/|c_k|`. -/
private noncomputable def rhoF (h : ℕ → ℕ → 𝕜) (β : 𝕜) : ℕ → ℝ
  | 0 => ‖β‖
  | k + 1 => ‖Krylov.gamma h β (k + 1)‖ / ‖Krylov.givensC h k‖

private theorem rhoF_zero (h : ℕ → ℕ → 𝕜) (β : 𝕜) : rhoF h β 0 = ‖β‖ := rfl

private theorem rhoF_succ (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) :
    rhoF h β (k + 1) = ‖Krylov.gamma h β (k + 1)‖ / ‖Krylov.givensC h k‖ := rfl

/-- Nothing happens at step `0`. -/
@[simp] theorem qmr_zero : qmr A b x₀ w₁ 0 = x₀ := by
  rw [qmr, Chapter06.qgmres, Chapter06.toEuclideanLin_colMatrix_apply]
  simp

variable {A b x₀ w₁}

/-- **The hinge of §7.3.2**: the QMR iterate meets the backbone quasi-minimal-residual
specification for the two-sided Lanczos data — it is `x_0 + V_m y` with `y` minimizing the
quasi-residual `‖β e_1 - T̄_m y‖₂`. Everything after (7.17) is this identification plus a
theorem of `Numlib/Krylov/QuasiMinRes.lean`. -/
theorem qmr_isQuasiMinResIterate {m : ℕ} (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) :
    Krylov.IsQuasiMinResIterate (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) x₀ m
      (qmr A b x₀ w₁ m) :=
  Chapter06.qgmres_isQuasiMinResIterate x₀ _ _ _
    (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) hR

/-- **(7.16)**: `b - A (x_0 + V_m y) = V_{m+1}(β e_1 - T̄_m y)`. Taking norms gives (7.17); were
the `v_i` orthonormal the right-hand side would be `‖β e_1 - T̄_m y‖₂`, as in GMRES, and the
quasi-residual would be the residual. -/
theorem equation_7_16 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) (m : ℕ) (y : Fin m → 𝕜) :
    b - op A (x₀ + ∑ j, y j • qmrV A b x₀ w₁ (j : ℕ))
      = ∑ i, (Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1)
          - (Tbar A (Chapter06.v₁ A b x₀) w₁ m).mulVec y) i • qmrV A b x₀ w₁ (i : ℕ) := by
  rw [Tbar_eq_hessenbergOf]
  exact (bilanczos_hessenbergRelation h).residual_eq (smul_qmrV_zero A b x₀ w₁) m y

/-- **(7.18)**: the quasi-residual norm is the running product of the sines,
`ρ^Q_m = |s_1 s_2 ⋯ s_m| ‖r_0‖₂`, hence `ρ^Q_{m+1} = |s_{m+1}| ρ^Q_m`. -/
theorem equation_7_18 (m : ℕ) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
        = (∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖) * ‖Chapter06.r₀ A b x₀‖ ∧
      Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)
        = ‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖
          * Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m := by
  refine ⟨?_, ?_⟩
  · rw [quasiResidualNorm_eq, Krylov.norm_gamma_eq_prod, norm_beta]
  · rw [quasiResidualNorm_eq, quasiResidualNorm_eq, Krylov.gamma_succ, norm_mul, norm_neg]

/-- **(7.19)**: `γ_{m+1} v_{m+1} = c_m r_m`, with `r_m` the residual of the Algorithm 7.2 (BCG)
iterate — the two-sided form of (6.56). Both sides are multiples of `v_{m+1}`, by (7.9). -/
theorem equation_7_19 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) • qmrV A b x₀ w₁ (m + 1)
      = Chapter06.c (qmrCoeff A b x₀ w₁) m • (b - op A (lanczosSolve A b x₀ w₁ (m + 1))) := by
  have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (m + 1)).mulVec
      (lanczosSolveY A b x₀ w₁ (m + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1) := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hres : b - op A (lanczosSolve A b x₀ w₁ (m + 1))
      = -(qmrCoeff A b x₀ w₁ (m + 1) m
          * lanczosSolveY A b x₀ w₁ (m + 1) ⟨m, Nat.lt_succ_self m⟩)
        • qmrV A b x₀ w₁ (m + 1) := by
    rw [show qmrCoeff A b x₀ w₁ (m + 1) m = bilanczosDelta A (Chapter06.v₁ A b x₀) w₁ (m + 1) from
      bilanczosCoeff_succ_self A _ _ m]
    exact residual_lanczosSolve h hT (Nat.succ_pos m)
  rw [hres, smul_smul, gamma_eq, givensC_eq,
    gamma_succ_eq_givensC_mul (h := qmrCoeff A b x₀ w₁)
      (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy]

/-- **(7.20)**: `ρ^Q_m = |c_m| ρ_m`, with `ρ_m` the true residual norm of the Algorithm 7.2
iterate, under the book's normalization `‖v_j‖₂ = 1`. -/
theorem equation_7_20 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)
      = ‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ * ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ := by
  have hnorm := congrArg norm (equation_7_19 h hT)
  rw [norm_smul, norm_smul, hv (m + 1), mul_one] at hnorm
  rw [quasiResidualNorm_eq]
  exact hnorm

/-- The Galerkin data of the harmonic identities is the residual sequence of Algorithm 7.2: the
`ρ^F` of `Numlib/Krylov/QuasiMinRes.lean` are the norms `ρ_i = ‖b - A x_i‖₂`. -/
private theorem rhoF_eq_norm_residual (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0) {i : ℕ} (hi : i ≤ m) :
    rhoF (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) i
      = ‖b - op A (lanczosSolve A b x₀ w₁ i)‖ := by
  cases i with
  | zero => rw [rhoF_zero, lanczosSolve_zero, norm_beta]
  | succ k =>
    have hk : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) k ≠ 0 := fun hcc =>
      h0 (gamma_eq_zero_of_le _ _ (by omega) hcc)
    have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (k + 1)).mulVec
        (lanczosSolveY A b x₀ w₁ (k + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (k + 1) := by
      rw [← T_eq_hessenbergSqOf]
      exact T_mulVec_lanczosSolveY A b x₀ w₁ (hT (k + 1))
    have hcne : ‖Krylov.givensC (qmrCoeff A b x₀ w₁) k‖ ≠ 0 := norm_ne_zero_iff.2
      (givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy hk)
    have h20 := equation_7_20 hs hv (hT (k + 1))
    rw [quasiResidualNorm_eq, givensC_eq] at h20
    rw [rhoF_succ, h20, mul_comm, mul_div_assoc, div_self hcne, mul_one]

/-- As long as no residual of Algorithm 7.2 vanishes, neither does the quasi-residual scalar: by
(7.20), `ρ^Q_{m+1} = |c_m| ρ_{m+1}`, and `c_m ≠ 0` follows inductively from `γ_m ≠ 0`. -/
private theorem gamma_ne_zero (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0 := by
  induction m with
  | zero =>
    intro hcc
    have hb : (Chapter06.β A b x₀ : 𝕜) = 0 := hcc
    have hnb : ‖Chapter06.r₀ A b x₀‖ = 0 := by
      rw [← norm_beta (A := A) (b := b) (x₀ := x₀), hb, norm_zero]
    exact hne 0 (by rw [lanczosSolve_zero]; exact norm_eq_zero.1 hnb)
  | succ k ih =>
    have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (k + 1)).mulVec
        (lanczosSolveY A b x₀ w₁ (k + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (k + 1) := by
      rw [← T_eq_hessenbergSqOf]
      exact T_mulVec_lanczosSolveY A b x₀ w₁ (hT (k + 1))
    have hc := givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy ih
    have h20 := equation_7_20 hs hv (hT (k + 1))
    rw [quasiResidualNorm_eq, givensC_eq] at h20
    intro hcc
    rw [hcc, norm_zero] at h20
    exact mul_ne_zero (norm_ne_zero_iff.2 hc) (norm_ne_zero_iff.2 (hne (k + 1))) h20.symm

/-- **Proposition 7.3**, (7.21): `‖b - A x^Q_m‖₂ ≤ ‖V_{m+1}‖₂ |s_1 ⋯ s_m| ‖r_0‖₂`, where
`‖V_{m+1}‖₂` enters as any bound `C` on the coordinate map `y ↦ ∑ y_i v_i`. -/
theorem proposition_7_3 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) {C : ℝ}
    (hC : ∀ w : Fin (m + 1) → 𝕜, ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖
      ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qmr A b x₀ w₁ m)‖
      ≤ C * ((∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖)
        * ‖Chapter06.r₀ A b x₀‖) := by
  have hprod := (equation_7_18 (A := A) (b := b) (x₀ := x₀) (w₁ := w₁) m).1
  rw [quasiResidualNorm_eq] at hprod
  rw [← hprod]
  exact Krylov.IsQuasiMinResIterate.norm_residual_le
    (Krylov.HessenbergRelation₂.of_hessenbergRelation (bilanczos_hessenbergRelation h))
    (smul_qmrV_zero A b x₀ w₁)
    ((Chapter06.isUnit_R_iff _ (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij)).1 hR) hC
    (qmr_isQuasiMinResIterate hR)

/-- **Proposition 7.3**, the Cauchy–Schwarz form: for unit Lanczos vectors `‖V_{m+1}‖₂ ≤ √(m+1)`,
so `‖b - A x^Q_m‖₂ ≤ √(m+1) |s_1 ⋯ s_m| ‖r_0‖₂`. -/
theorem proposition_7_3_sqrt (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ ≤ 1) :
    ‖b - op A (qmr A b x₀ w₁ m)‖
      ≤ Real.sqrt (m + 1)
        * ((∏ k ∈ Finset.range m, ‖Chapter06.s (qmrCoeff A b x₀ w₁) k‖)
          * ‖Chapter06.r₀ A b x₀‖) := by
  refine proposition_7_3 h hR fun w => ?_
  have := Krylov.norm_sum_smul_le_sqrt_mul (v := qmrV A b x₀ w₁) hv w
  rwa [Nat.cast_add, Nat.cast_one] at this

/-- **Theorem 7.4**: `‖r^Q_m‖₂ ≤ κ₂(V_{m+1}) ‖r^G_m‖₂`, the QMR residual against the GMRES
residual after `m` steps, with `κ₂(V_{m+1}) = C/c` the conditioning of the Lanczos basis. This is
the same theorem as Saad's Theorem 6.11; the full-rank hypothesis the book assumes there is
subsumed in `0 < c`, and here it is a consequence of P-7.2 rather than an assumption. -/
theorem theorem_7_4 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hnb : NoBreakdown A (Chapter06.v₁ A b x₀) w₁ m) (hr : Chapter06.r₀ A b x₀ ≠ 0)
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hm : m ≤ Chapter06.grade A (Chapter06.v₁ A b x₀))
    (hRA : IsUnit (Chapter06.R (Chapter06.arnoldiCoeff A (Chapter06.v₁ A b x₀)) m))
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜, c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖
      ≤ ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜, ‖∑ i, w i • qmrV A b x₀ w₁ (i : ℕ)‖
      ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖) :
    ‖b - op A (qmr A b x₀ w₁ m)‖ ≤ C / c * ‖b - op A (Chapter06.gmresFixed A b x₀ m)‖ := by
  have hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => qmrV A b x₀ w₁ (i : ℕ))
      = Chapter06.krylov A (Chapter06.r₀ A b x₀) m := by
    rw [(proposition_7_1_span hnb).1, Chapter06.v₁_def,
      Chapter06.krylov_smul A _ (inv_ne_zero (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hr)))]
  exact Chapter06.theorem_6_11 b x₀ (bilanczos_hessenbergRelation h) (smul_qmrV_zero A b x₀ w₁) hR
    hm hRA hspan hc0 hc hC

/-- **(7.23)**: `1/(ρ^Q_{m+1})² = 1/(ρ^Q_m)² + 1/(ρ_{m+1})²`, the harmonic relation between the
QMR quasi-residual norms and the residual norms of Algorithm 7.2 — the two-sided analogue of
(6.65). -/
theorem equation_7_23 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) {m : ℕ}
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1)))
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) ≠ 0) :
    1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1) ^ 2
      = 1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ^ 2
        + 1 / ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ ^ 2 := by
  have hk : Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0 := fun hcc =>
    h0 (gamma_eq_zero_of_le _ _ (Nat.le_succ m) hcc)
  have hy : (Krylov.hessenbergSqOf (qmrCoeff A b x₀ w₁) (m + 1)).mulVec
      (lanczosSolveY A b x₀ w₁ (m + 1)) = Krylov.firstVec (Chapter06.β A b x₀ : 𝕜) (m + 1) := by
    rw [← T_eq_hessenbergSqOf]
    exact T_mulVec_lanczosSolveY A b x₀ w₁ hT
  have hcne : ‖Krylov.givensC (qmrCoeff A b x₀ w₁) m‖ ≠ 0 := norm_ne_zero_iff.2
    (givensC_ne_zero (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) _ hy hk)
  have h20 := equation_7_20 h hv hT
  rw [quasiResidualNorm_eq, givensC_eq] at h20
  have hkey : ‖Krylov.gamma (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) (m + 1)‖
      / ‖Krylov.givensC (qmrCoeff A b x₀ w₁) m‖
      = ‖b - op A (lanczosSolve A b x₀ w₁ (m + 1))‖ := by
    rw [h20, mul_comm, mul_div_assoc, div_self hcne, mul_one]
  rw [quasiResidualNorm_eq, quasiResidualNorm_eq, Krylov.inv_sq_norm_gamma _ _ h0, hkey]

/-- **(7.24)**: the smoothing property of QMR — the quasi-residual norm is the harmonic average
`1/(ρ^Q_m)² = ∑_{i ≤ m} 1/(ρ_i)²` of the residual norms of Algorithm 7.2. -/
theorem equation_7_24 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0) :
    1 / Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ^ 2
      = ∑ i ∈ Finset.range (m + 1), 1 / ‖b - op A (lanczosSolve A b x₀ w₁ i)‖ ^ 2 := by
  rw [quasiResidualNorm_eq,
    Krylov.inv_sq_norm_gamma_eq_sum _ _ (rhoF_zero _ _) (rhoF_succ _ _) h0]
  exact Finset.sum_congr rfl fun i hi => by
    rw [rhoF_eq_norm_residual h hv hT h0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/-- **Proposition 7.5**, (7.25): `ρ^Q_m ≤ ρ_{m*} ≤ √(m+1) ρ^Q_m`, where `ρ_{m*}` is the smallest
residual norm of Algorithm 7.2 among the first `m` steps. -/
theorem proposition_7_5 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k)) {m : ℕ}
    (h0 : Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m ≠ 0)
    (hne : ∀ i ≤ m, b - op A (lanczosSolve A b x₀ w₁ i) ≠ 0) :
    Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
        ≤ (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩
            (fun i => ‖b - op A (lanczosSolve A b x₀ w₁ i)‖) ∧
      (Finset.range (m + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩
          (fun i => ‖b - op A (lanczosSolve A b x₀ w₁ i)‖)
        ≤ Real.sqrt (m + 1)
          * Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m := by
  rw [quasiResidualNorm_eq]
  refine ⟨Finset.le_inf' _ _ fun i hi => ?_, ?_⟩
  · have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [← rhoF_eq_norm_residual h hv hT h0 hi']
    refine Krylov.norm_gamma_le _ _ (rhoF_zero _ _) (rhoF_succ _ _) hi' h0 ?_
    rw [rhoF_eq_norm_residual h hv hT h0 hi']
    exact norm_ne_zero_iff.2 (hne i hi')
  · obtain ⟨i, hi, hle⟩ := Krylov.exists_norm_gamma_div_givensC_le (qmrCoeff A b x₀ w₁)
      (Chapter06.β A b x₀ : 𝕜) (rhoF_zero _ _) (rhoF_succ _ _) m
    refine le_trans (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) ?_
    rw [← rhoF_eq_norm_residual h hv hT h0 hi]
    exact hle

/-- **(7.26)–(7.27)**: the QMR residual is `b - A x^Q_m = γ_{m+1} z_{m+1}`, and the auxiliary
vector obeys `z_{m+2} = -s̄_{m+1} z_{m+1} + c̄_{m+1} v_{m+2}`. -/
theorem equation_7_26 (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁) {m : ℕ}
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m)) :
    b - op A (qmr A b x₀ w₁ m)
        = Chapter06.γ (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : 𝕜) m
          • Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) m ∧
      Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) (m + 1)
        = starRingEnd 𝕜 (-Chapter06.s (qmrCoeff A b x₀ w₁) m)
            • Chapter06.z (qmrV A b x₀ w₁) (qmrCoeff A b x₀ w₁) m
          + starRingEnd 𝕜 (Chapter06.c (qmrCoeff A b x₀ w₁) m) • qmrV A b x₀ w₁ (m + 1) := by
  exact ⟨Chapter06.equation_6_50 (bilanczos_hessenbergRelation h) (smul_qmrV_zero A b x₀ w₁) hR,
    Chapter06.equation_6_53 _ _ m⟩

/-- **(7.30)**: QMR is a residual smoothing of Algorithm 7.2 with parameter `|c_{m+1}|²`,
`x^Q_{m+1} = |s_{m+1}|² x^Q_m + |c_{m+1}|² x_{m+1}`. It is the iterate form of the residual
relation (7.29), and (7.31) rewrites it as `x^Q_{m+1} = x^Q_m + |c_{m+1}|² (x_{m+1} - x^Q_m)`.
No no-serious-breakdown hypothesis is needed: the identity is one about the rotations and the
two coordinate systems, not about the basis. The declaration keeps the name `equation_7_29`
the plan gave it. -/
theorem equation_7_29 {m : ℕ}
    (hρ : ∀ k < m + 1, Krylov.givensRho (qmrCoeff A b x₀ w₁) k ≠ 0)
    (hRm : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) m))
    (hR : IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) (m + 1)))
    (hT : IsUnit (T A (Chapter06.v₁ A b x₀) w₁ (m + 1))) :
    qmr A b x₀ w₁ (m + 1)
      = ((‖Chapter06.s (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜) • qmr A b x₀ w₁ m
        + ((‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ ^ 2 : ℝ) : 𝕜)
          • lanczosSolve A b x₀ w₁ (m + 1) := by
  refine Krylov.IsQuasiMinResIterate.eq_combination
    (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij) hρ
    (w := lanczosSolveY A b x₀ w₁ (m + 1)) (qmr_isQuasiMinResIterate hR)
    (qmr_isQuasiMinResIterate hRm) ?_ (lanczosSolve_eq_add_sum A b x₀ w₁ (m + 1))
  rw [← T_eq_hessenbergSqOf]
  exact T_mulVec_lanczosSolveY A b x₀ w₁ hT

end QMR

/-! ### Algorithm 7.5: quasi-minimal residual smoothing -/

section Smoothing

/-- **Algorithm 7.5** (Zhou–Walker quasi-minimal residual smoothing): given any sequence `x_j`
with residuals `r_j`, set `τ_0 = ‖r_0‖`, `1/τ_j² = 1/τ_{j-1}² + 1/‖r_j‖²`, `η_j = (τ_j/‖r_j‖)²`
and `x^Q_j = x^Q_{j-1} + η_j (x_j - x^Q_{j-1})`. It is `SaadSparse.Chapter06.qmrs`, the smoothing of
§6.5.8 written for an arbitrary sequence. -/
noncomputable abbrev qmrSmoothing (xO rO : ℕ → EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := Chapter06.qmrs xO rO

variable {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ w₁ : EuclideanSpace ℝ (Fin n)}

private theorem qmrsTau_zero (rO : ℕ → EuclideanSpace ℝ (Fin n)) :
    Chapter06.qmrsTau rO 0 = ‖rO 0‖ := rfl

private theorem qmrsTau_succ (rO : ℕ → EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Chapter06.qmrsTau rO (m + 1)
      = Real.sqrt (1 / (1 / Chapter06.qmrsTau rO m ^ 2 + 1 / ‖rO (m + 1)‖ ^ 2)) := rfl

private theorem qmrsEta_def (rO : ℕ → EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    Chapter06.qmrsEta rO m
      = Chapter06.qmrsTau rO m ^ 2 / (Chapter06.qmrsTau rO m ^ 2 + ‖rO (m + 1)‖ ^ 2) := rfl

/-- The scalar identity behind Algorithm 7.5: from `ρ^Q_{m+1} = |c| ρ_{m+1}` and the harmonic
relation (7.23), the smoothing parameter `τ_m²/(τ_m² + ρ_{m+1}²)` of Algorithm 6.14 *is* `|c|²`. -/
private theorem eta_eq_sq (P R c : ℝ) (hP : 0 < P) (hR : 0 < R)
    (h23 : 1 / (c * R) ^ 2 = 1 / P ^ 2 + 1 / R ^ 2) :
    P ^ 2 / (P ^ 2 + R ^ 2) = c ^ 2 := by
  have hP2 : (0 : ℝ) < P ^ 2 := by positivity
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_mul] at h23
    have : (0 : ℝ) < 1 / P ^ 2 + 1 / R ^ 2 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at h23
    linarith
  have hfin : P ^ 2 = (P ^ 2 + R ^ 2) * c ^ 2 := by
    field_simp at h23
    linear_combination h23
  rw [div_eq_iff (by positivity)]
  linear_combination hfin

/-- The scale factors of Algorithm 7.5 applied to the Algorithm 7.2 sequence are the
quasi-residual norms: `τ_m = ρ^Q_m`, by (7.23). -/
private theorem qmrsTau_eq (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Chapter06.qmrsTau (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m
      = Chapter06.quasiResidualNorm (qmrCoeff A b x₀ w₁) (Chapter06.β A b x₀ : ℝ) m := by
  induction m with
  | zero =>
    have habs : ‖(Chapter06.β A b x₀ : ℝ)‖ = ‖Chapter06.r₀ A b x₀‖ :=
      (Real.norm_eq_abs (Chapter06.β A b x₀)).trans
        (abs_of_nonneg (norm_nonneg (Chapter06.r₀ A b x₀)))
    rw [qmrsTau_zero, quasiResidualNorm_eq, lanczosSolve_zero]
    exact habs.symm
  | succ k ih =>
    have h23 := equation_7_23 hs hv (hT (k + 1)) (gamma_ne_zero hs hv hT hne (k + 1))
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h23
    rw [qmrsTau_succ, ih, ← h23, one_div_one_div, quasiResidualNorm_eq,
      Real.sqrt_sq (norm_nonneg _)]

/-- The smoothing parameter of Algorithm 7.5 applied to the Algorithm 7.2 sequence is `|c_m|²`,
which is what makes that algorithm reproduce QMR. -/
private theorem qmrsEta_eq (hs : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1) (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    Chapter06.qmrsEta (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m
      = ‖Chapter06.c (qmrCoeff A b x₀ w₁) m‖ ^ 2 := by
  have h20 := equation_7_20 hs hv (hT (m + 1))
  have h23 := equation_7_23 hs hv (hT (m + 1)) (gamma_ne_zero hs hv hT hne (m + 1))
  have hpos := gamma_ne_zero hs hv hT hne m
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h20 h23 hpos
  rw [qmrsEta_def, qmrsTau_eq hs hv hT hne m, quasiResidualNorm_eq]
  refine eta_eq_sq _ _ _ (norm_pos_iff.2 hpos) (norm_pos_iff.2 (hne (m + 1))) ?_
  rw [← h20, h23, quasiResidualNorm_eq]

/-- The book's remark closing §7.3: applying Algorithm 7.5 to the Algorithm 7.2 (BCG) sequence
reproduces the QMR iterates, because (7.29) is exactly the smoothing recurrence with
`η_m = |c_m|² = (ρ^Q_m/ρ_m)²`. -/
theorem qmrSmoothing_eq_qmr {A : Matrix (Fin n) (Fin n) ℝ}
    {b x₀ w₁ : EuclideanSpace ℝ (Fin n)} (h : NoSeriousBreakdown A (Chapter06.v₁ A b x₀) w₁)
    (hv : ∀ j, ‖qmrV A b x₀ w₁ j‖ = 1)
    (hT : ∀ k, IsUnit (T A (Chapter06.v₁ A b x₀) w₁ k))
    (hR : ∀ k, IsUnit (Chapter06.R (qmrCoeff A b x₀ w₁) k))
    (hne : ∀ j, b - op A (lanczosSolve A b x₀ w₁ j) ≠ 0) (m : ℕ) :
    (qmrSmoothing (fun j => lanczosSolve A b x₀ w₁ j)
        (fun j => b - op A (lanczosSolve A b x₀ w₁ j)) m).1 = qmr A b x₀ w₁ m := by
  simp only [qmrSmoothing]
  induction m with
  | zero => simp [Chapter06.qmrs_zero]
  | succ k ih =>
    have hρ := (Chapter06.isUnit_R_iff (qmrCoeff A b x₀ w₁)
      (fun _ _ hij => bilanczosCoeff_eq_zero_of_lt A _ _ hij)).1 (hR (k + 1))
    have hcs := Krylov.norm_givensC_sq_add_norm_givensS_sq (qmrCoeff A b x₀ w₁) k
      (hρ k (Nat.lt_succ_self k))
    rw [Chapter06.qmrs_succ, ih, qmrsEta_eq h hv hT hne k,
      equation_7_29 hρ (hR k) (hR (k + 1)) (hT (k + 1))]
    simp only [RCLike.ofReal_real_eq_id, id_eq, givensC_eq, givensS_eq] at hcs ⊢
    rw [show ‖Krylov.givensS (qmrCoeff A b x₀ w₁) k‖ ^ 2
        = 1 - ‖Krylov.givensC (qmrCoeff A b x₀ w₁) k‖ ^ 2 from by linarith]
    module

end Smoothing

end SaadSparse.Chapter07
