import Numlib.LinearSolve.Projection.OneDimensional
import NumlibSurface.SaadSparse.Chapter07.Section03

/-!
# Saad §7.4: transpose-free variants

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §7.4.

The section presents three algorithms and proves no numbered result about any of them. What is
theorem content, and what this file states, is the polynomial identification that gives each method
its meaning.

`bcgResidualPoly` and `bcgDirectionPoly` are the polynomials `φ_j`, `π_j` of (7.32)–(7.33), defined
by the recurrences (7.35)–(7.36) from the coefficients of the run of Algorithm 7.3 itself;
`bcg_residual_eq_aeval` is (7.32)–(7.33) together with the observation that the starred recurrences
are the unstarred ones with `A` replaced by `Aᴴ`, so that `r*_j = φ̄_j(Aᴴ) r*_0`. Every scalar of
the section is then computed by moving a polynomial across the inner product, which is
`BiLanczos.inner_aeval_map_eq`.

**Algorithm 7.6** (CGS, Sonneveld) is `cgs`, and `cgs_residual_eq` is (7.40)–(7.45): its vectors are
`r_j = φ_j²(A) r_0`, `p_j = π_j²(A) r_0`, `u_j = φ_j(A) π_j(A) r_0` and `q_j = φ_{j+1}(A) π_j(A)
r_0` for the BCG polynomials of the *same* run, and its `α_j`, `β_j` are the BCG ones. No
hypothesis is needed: the squared polynomials are computed without ever touching `Aᴴ`, which is the
whole point of the method.

**Algorithm 7.7** (BICGSTAB, van der Vorst) is `bicgstab`, with the stabilizing polynomial `ψ_j` of
(7.47) as `bicgstabPoly`; `bicgstab_residual_eq` is (7.46) and (7.52), and `equation_7_53` is
(7.53)–(7.54), the formulas that make the BCG coefficients computable from the BICGSTAB vectors.
Here hypotheses are needed, and they are exactly the two the book's leading-coefficient argument
uses: Algorithm 7.3 has not broken down, so that `γ_1^{(j)} ≠ 0`, and no `ω_i` has vanished, so
that `η_1^{(j)} ≠ 0`. `equation_7_55` is the steepest-descent characterization of `ω_j`: the
BICGSTAB half-step is `Projection.minResStep` along `s_j`.

**Algorithm 7.8** (TFQMR, Freund) is `tfqmr`, on the doubled-index vectors of (7.65);
`tfqmr_eq_cgs` is (7.56)–(7.62), that the even-indexed state is the CGS state, and
`cgsHalfIterate_two_mul` is (7.63)–(7.64), that the half-step iterates interleave the CGS ones.
`equation_7_70` is (7.68)–(7.73): `A u_j = (w_j - w_{j+1})/α_j` is a `Krylov.HessenbergRelation₂`
for the *two* families `u` and `w` — the iterates live in the span of the `u`-vectors and the
residuals in the span of the `w`-vectors — with the bidiagonal coefficient array `H̄_m = Δ_{m+1}
B̄_m` of (7.72) and (7.81). It is stated for an arbitrary column scaling `Δ_{m+1}`, which is what
P-7.9 asks about; `equation_7_76` is the FOM formula for the CGS iterates, likewise for an
arbitrary scaling. With the scaling `δ_i = ‖w_i‖₂` of (7.73) the residual basis has unit columns,
and `tfqmr_isQuasiMinResIterate` identifies Algorithm 7.8's `θ, c, τ, η, d` recurrence with the
quasi-minimal-residual iterate of that relation — it is Algorithm 6.13 with `k = 1`, because `H̄_m`
is bidiagonal — whence (7.83), `‖b - A x_m‖₂ ≤ √(m+1) τ_m`, as `equation_7_83`.
Two hypotheses appear there, and both are bounded or conditional, because `∀ m, α_m ≠ 0` is
unsatisfiable in finite dimension — Algorithm 7.3 terminates, and `ρ_j = 0` from the grade on, so a
theorem assuming it would say nothing. `TFQMRNoBreakdown … m` asks that no `α_i` and no `w_i`
vanish *through step `m`*, which is what the first `m` rotations need; `TFQMRNoSeriousBreakdown`
asks that a vanishing `α_m` come with `A u_m = 0`, which is what (7.70) needs and what a regular
termination gives — the analogue of `NoSeriousBreakdown` for Algorithm 7.1.

Over `ℂ` the book's real recurrence for `θ_m`, `c_m` and `τ_m` still computes the right thing:
`τ_m = |γ_m|` is the modulus of the backbone `Krylov.gamma`, and `η_{m+1} = c_{m+1}² α_m` is
exactly `g_m / ρ_m`, the phase of `α_m` entering through `η` alone.

Indices are `0`-based as in the rest of the chapter: `cgs A b x₀ rs₀ j` is the book's state after
`j` steps, `tfqmr A b x₀ rs₀ m` its state after `m` half-steps, and `bcgResidualPoly A b x₀ rs₀ j`
its `φ_j`.
-/

open Matrix Polynomial

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Polynomials in an operator and its adjoint -/

section AevalHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `p(T)` commutes with `T`. -/
private theorem aeval_apply_apply (T : E →ₗ[𝕜] E) (p : 𝕜[X]) (v : E) :
    aeval T p (T v) = T (aeval T p v) := by
  have hmul : aeval T (p * X) = aeval T (X * p) := by rw [mul_comm]
  have := congrArg (fun f : E →ₗ[𝕜] E => f v) hmul
  simpa only [map_mul, aeval_X, Module.End.mul_apply] using this

/-- `(p q)(T) v = p(T) (q(T) v)`. -/
private theorem aeval_mul_apply (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p * q) v = aeval T p (aeval T q v) := by
  rw [map_mul]
  rfl

/-- Evaluation is additive in the polynomial. -/
private theorem aeval_apply_add (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p + q) v = aeval T p v + aeval T q v := by
  rw [map_add]; rfl

/-- Evaluation is additive in the polynomial. -/
private theorem aeval_apply_sub (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p - q) v = aeval T p v - aeval T q v := by
  rw [map_sub]; rfl

/-- A constant factor becomes a scalar. -/
private theorem aeval_apply_C_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p : 𝕜[X]) (v : E) :
    aeval T (C c * p) v = c • aeval T p v := by
  rw [map_mul, aeval_C]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- A factor of `t` becomes an application of `T`. -/
private theorem aeval_apply_X_mul (T : E →ₗ[𝕜] E) (p : 𝕜[X]) (v : E) :
    aeval T (X * p) v = T (aeval T p v) := by
  rw [aeval_mul_apply, aeval_X]

/-- The evaluation of `p - c X q`. -/
private theorem aeval_sub_C_mul_X_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p q : 𝕜[X]) (v : E) :
    aeval T (p - C c * (X * q)) v = aeval T p v - c • T (aeval T q v) := by
  rw [map_sub, map_mul, map_mul, aeval_C, aeval_X]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- The evaluation of `p + c q`. -/
private theorem aeval_add_C_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p q : 𝕜[X]) (v : E) :
    aeval T (p + C c * q) v = aeval T p v + c • aeval T q v := by
  rw [map_add, map_mul, aeval_C]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

end AevalHelpers

/-! ### §7.4.1: the BCG residual and direction polynomials -/

section BCGPolynomials

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- The step length `α_j` of **Algorithm 7.3**, read off the run of `bcg`. -/
noncomputable abbrev bcgAlpha (j : ℕ) : 𝕜 := BCG.alpha (op A) (op Aᴴ) b x₀ rs₀ j

/-- The direction coefficient `β_j` of **Algorithm 7.3**, read off the run of `bcg`. -/
noncomputable abbrev bcgBeta (j : ℕ) : 𝕜 := BCG.beta (op A) (op Aᴴ) b x₀ rs₀ j

/-- `α_j = (r_j, r*_j)/(A p_j, p*_j)`, the formula of **Algorithm 7.3**, line 4. -/
theorem bcgAlpha_eq (j : ℕ) : bcgAlpha A b x₀ rs₀ j =
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r /
      inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ j).p) := by
  rw [bcg_eq]; rfl

/-- `β_j = (r_{j+1}, r*_{j+1})/(r_j, r*_j)`, the formula of **Algorithm 7.3**, line 8. -/
theorem bcgBeta_eq (j : ℕ) : bcgBeta A b x₀ rs₀ j =
    inner 𝕜 (bcg A b x₀ rs₀ (j + 1)).rs (bcg A b x₀ rs₀ (j + 1)).r /
      inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r := by
  rw [bcg_eq, bcg_eq]; rfl

/-- The pair `(φ_j, π_j)` of (7.35)–(7.36), defined together because each recurrence feeds the
other. -/
private noncomputable def bcgPolyPair (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 => (1, 1)
  | j + 1 =>
      let φ : 𝕜[X] :=
        (bcgPolyPair A b x₀ rs₀ j).1
          - C (bcgAlpha A b x₀ rs₀ j) * (X * (bcgPolyPair A b x₀ rs₀ j).2)
      (φ, φ + C (bcgBeta A b x₀ rs₀ j) * (bcgPolyPair A b x₀ rs₀ j).2)

/-- (7.32), (7.35): the **BCG residual polynomial** `φ_j`, the polynomial of degree at most `j` with
`φ_j(0) = 1` and `r_j = φ_j(A) r_0`, defined from the coefficients of Algorithm 7.3 by `φ_0 = 1`,
`φ_{j+1} = φ_j - α_j t π_j`.  Its degree is exactly `j` while no `α_i` vanishes. -/
noncomputable def bcgResidualPoly (j : ℕ) : 𝕜[X] := (bcgPolyPair A b x₀ rs₀ j).1

/-- (7.33), (7.36): the **BCG direction polynomial** `π_j`, the polynomial of degree at most `j`
with `p_j = π_j(A) r_0`, defined by `π_0 = 1`, `π_{j+1} = φ_{j+1} + β_j π_j`. -/
noncomputable def bcgDirectionPoly (j : ℕ) : 𝕜[X] := (bcgPolyPair A b x₀ rs₀ j).2

@[simp] theorem bcgResidualPoly_zero : bcgResidualPoly A b x₀ rs₀ 0 = 1 := rfl

@[simp] theorem bcgDirectionPoly_zero : bcgDirectionPoly A b x₀ rs₀ 0 = 1 := rfl

/-- (7.35): `φ_{j+1} = φ_j - α_j t π_j`. -/
theorem bcgResidualPoly_succ (j : ℕ) : bcgResidualPoly A b x₀ rs₀ (j + 1) =
    bcgResidualPoly A b x₀ rs₀ j
      - C (bcgAlpha A b x₀ rs₀ j) * (X * bcgDirectionPoly A b x₀ rs₀ j) := rfl

/-- (7.36): `π_{j+1} = φ_{j+1} + β_j π_j`. -/
theorem bcgDirectionPoly_succ (j : ℕ) : bcgDirectionPoly A b x₀ rs₀ (j + 1) =
    bcgResidualPoly A b x₀ rs₀ (j + 1)
      + C (bcgBeta A b x₀ rs₀ j) * bcgDirectionPoly A b x₀ rs₀ j := rfl

/-- The residual polynomials are *consistent*: `φ_j(0) = 1` for every `j`, which is what makes
`φ_j(A) r_0` a residual. -/
@[simp] theorem bcgResidualPoly_eval_zero (j : ℕ) :
    (bcgResidualPoly A b x₀ rs₀ j).eval 0 = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [bcgResidualPoly_succ]; simp [ih]

/-- `deg φ_j ≤ j` and `deg π_j ≤ j`. -/
private theorem bcgPoly_natDegree_le (j : ℕ) :
    (bcgResidualPoly A b x₀ rs₀ j).natDegree ≤ j ∧
      (bcgDirectionPoly A b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hπ := ih.2
    have hφ : (bcgResidualPoly A b x₀ rs₀ (j + 1)).natDegree ≤ j + 1 := by
      rw [bcgResidualPoly_succ]
      refine (natDegree_sub_le _ _).trans (max_le (ih.1.trans (Nat.le_succ j)) ?_)
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      simp only [natDegree_X]
      omega
    refine ⟨hφ, ?_⟩
    rw [bcgDirectionPoly_succ]
    refine (natDegree_add_le _ _).trans (max_le hφ ?_)
    exact (natDegree_C_mul_le _ _).trans (hπ.trans (Nat.le_succ j))

theorem bcgResidualPoly_natDegree_le (j : ℕ) : (bcgResidualPoly A b x₀ rs₀ j).natDegree ≤ j :=
  (bcgPoly_natDegree_le A b x₀ rs₀ j).1

theorem bcgDirectionPoly_natDegree_le (j : ℕ) : (bcgDirectionPoly A b x₀ rs₀ j).natDegree ≤ j :=
  (bcgPoly_natDegree_le A b x₀ rs₀ j).2

/-- The two polynomials of a step have the same leading coefficient, `π_{j+1}` differing from
`φ_{j+1}` only by a multiple of the lower-degree `π_j`.  This is the "the leading coefficients for
`φ_j(Aᴴ) r*_0` and `π_j(Aᴴ) r*_0` are identical" of the derivation of (7.54). -/
theorem bcgDirectionPoly_coeff_self (j : ℕ) :
    (bcgDirectionPoly A b x₀ rs₀ j).coeff j = (bcgResidualPoly A b x₀ rs₀ j).coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [bcgDirectionPoly_succ, coeff_add, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (bcgDirectionPoly_natDegree_le A b x₀ rs₀ j) (Nat.lt_succ_self j)),
      mul_zero, add_zero]

/-- The leading coefficients obey `γ_1^{(j+1)} = -α_j γ_1^{(j)}`, the first of the two relations
the derivation of (7.53) compares. -/
theorem bcgResidualPoly_coeff_succ (j : ℕ) :
    (bcgResidualPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -bcgAlpha A b x₀ rs₀ j * (bcgResidualPoly A b x₀ rs₀ j).coeff j := by
  rw [bcgResidualPoly_succ, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (bcgResidualPoly_natDegree_le A b x₀ rs₀ j) (Nat.lt_succ_self j)),
    ← mul_assoc, mul_comm (C (bcgAlpha A b x₀ rs₀ j)) X, mul_assoc, coeff_X_mul, coeff_C_mul,
    bcgDirectionPoly_coeff_self]
  ring

/-- The recurrences of **Algorithm 7.3** in the book's own notation, lines 6, 7, 9 and 10. -/
theorem bcg_succ (j : ℕ) :
    (bcg A b x₀ rs₀ (j + 1)).r
        = (bcg A b x₀ rs₀ j).r - bcgAlpha A b x₀ rs₀ j • op A (bcg A b x₀ rs₀ j).p ∧
      (bcg A b x₀ rs₀ (j + 1)).rs
        = (bcg A b x₀ rs₀ j).rs
          - starRingEnd 𝕜 (bcgAlpha A b x₀ rs₀ j) • op Aᴴ (bcg A b x₀ rs₀ j).ps ∧
      (bcg A b x₀ rs₀ (j + 1)).p
        = (bcg A b x₀ rs₀ (j + 1)).r + bcgBeta A b x₀ rs₀ j • (bcg A b x₀ rs₀ j).p ∧
      (bcg A b x₀ rs₀ (j + 1)).ps
        = (bcg A b x₀ rs₀ (j + 1)).rs
          + starRingEnd 𝕜 (bcgBeta A b x₀ rs₀ j) • (bcg A b x₀ rs₀ j).ps := by
  simp only [bcg_eq]
  exact ⟨BCG.residual_succ _ _ _ _ _ j, BCG.dualResidual_succ _ _ _ _ _ j,
    BCG.direction_succ _ _ _ _ _ j, BCG.dualDirection_succ _ _ _ _ _ j⟩

/-- **(7.32)–(7.33)**: the four BCG sequences are the two polynomials evaluated at `A` on `r_0` and
at `Aᴴ` on `r*_0`.  The starred recurrences are the unstarred ones with `A` replaced by `Aᴴ` and
every coefficient conjugated, so the starred vectors carry the *conjugate* polynomials — over `ℝ`,
where the book works, `φ̄_j = φ_j` and this is the book's `r*_j = φ_j(Aᵀ) r*_0`. -/
theorem bcg_residual_eq_aeval (j : ℕ) :
    (bcg A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bcg A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bcg A b x₀ rs₀ j).rs
        = aeval (op Aᴴ) ((bcgResidualPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ ∧
      (bcg A b x₀ rs₀ j).ps
        = aeval (op Aᴴ) ((bcgDirectionPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hrs, hps⟩ := ih
    obtain ⟨sr, srs, sp, sps⟩ := bcg_succ A b x₀ rs₀ j
    have hrmap : ((bcgResidualPoly A b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜))
        = (bcgResidualPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)
          - C (starRingEnd 𝕜 (bcgAlpha A b x₀ rs₀ j))
            * (X * (bcgDirectionPoly A b x₀ rs₀ j).map (starRingEnd 𝕜)) := by
      rw [bcgResidualPoly_succ]
      simp [Polynomial.map_sub, Polynomial.map_mul]
    have hpmap : ((bcgDirectionPoly A b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜))
        = (bcgResidualPoly A b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
          + C (starRingEnd 𝕜 (bcgBeta A b x₀ rs₀ j))
            * (bcgDirectionPoly A b x₀ rs₀ j).map (starRingEnd 𝕜) := by
      rw [bcgDirectionPoly_succ]
      simp [Polynomial.map_add, Polynomial.map_mul]
    have h1 : (bcg A b x₀ rs₀ (j + 1)).r
        = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1)) (b - op A x₀) := by
      rw [sr, bcgResidualPoly_succ, aeval_sub_C_mul_X_mul, hr, hp]
    have h3 : (bcg A b x₀ rs₀ (j + 1)).rs
        = aeval (op Aᴴ) ((bcgResidualPoly A b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)) rs₀ := by
      rw [srs, hrmap, aeval_sub_C_mul_X_mul, hrs, hps]
    exact ⟨h1, by rw [sp, bcgDirectionPoly_succ, aeval_add_C_mul, h1, hp], h3,
      by rw [sps, hpmap, aeval_add_C_mul, h3, hps]⟩

end BCGPolynomials

/-! ### §7.4.1: Algorithm 7.6, the conjugate gradient squared algorithm -/

section CGS

/-- The state `(x_j, r_j, u_j, p_j)` of **Algorithm 7.6**; the auxiliary `q_j` of line 5 is read off
it by `cgsQ`. -/
@[ext]
structure CGSState (E : Type*) where
  /-- The iterate `x_j`. -/
  x : E
  /-- The residual `r_j`, which is `φ_j²(A) r_0`. -/
  r : E
  /-- The auxiliary vector `u_j = r_j + β_{j-1} q_{j-1}`, which is `φ_j(A) π_j(A) r_0`. -/
  u : E
  /-- The direction `p_j`, which is `π_j²(A) r_0`. -/
  p : E

/-- One pass through lines 4–10 of **Algorithm 7.6**, on the state `(x_j, r_j, u_j, p_j)`. -/
noncomputable def cgsStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (s : CGSState (EuclideanSpace 𝕜 (Fin n))) : CGSState (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (op A s.p)
  let q : EuclideanSpace 𝕜 (Fin n) := s.u - α • op A s.p
  let r : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A (s.u + q)
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r
  let u : EuclideanSpace 𝕜 (Fin n) := r + β • q
  { x := s.x + α • (s.u + q), r := r, u := u, p := u + β • (q + β • s.p) }

/-- **Algorithm 7.6** (CGS, Sonneveld) run for `k` steps from `x_0`, with the shadow residual `r*_0`
initialized to an arbitrary `rs₀`.  Lines 1 and 2 set `p_0 = u_0 = r_0 = b - A x_0`. -/
noncomputable def cgs (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → CGSState (EuclideanSpace 𝕜 (Fin n))
  | 0 => { x := x₀, r := b - op A x₀, u := b - op A x₀, p := b - op A x₀ }
  | k + 1 => cgsStep A rs₀ (cgs A b x₀ rs₀ k)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 7.6**, lines 1 and 2. -/
@[simp] theorem cgs_zero :
    cgs A b x₀ rs₀ 0 = { x := x₀, r := b - op A x₀, u := b - op A x₀, p := b - op A x₀ } := rfl

/-- One pass of **Algorithm 7.6**. -/
theorem cgs_succ (k : ℕ) : cgs A b x₀ rs₀ (k + 1) = cgsStep A rs₀ (cgs A b x₀ rs₀ k) := rfl

/-- **Algorithm 7.6**, line 4: `α_j = (r_j, r*_0)/(A p_j, r*_0)`. -/
noncomputable def cgsAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r / inner 𝕜 rs₀ (op A (cgs A b x₀ rs₀ j).p)

/-- **Algorithm 7.6**, line 8: `β_j = (r_{j+1}, r*_0)/(r_j, r*_0)`. -/
noncomputable def cgsBeta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (cgs A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r

/-- **Algorithm 7.6**, line 5: `q_j = u_j - α_j A p_j`. -/
noncomputable def cgsQ (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  (cgs A b x₀ rs₀ j).u - cgsAlpha A b x₀ rs₀ j • op A (cgs A b x₀ rs₀ j).p

/-- **Algorithm 7.6**, line 6: `x_{j+1} = x_j + α_j (u_j + q_j)`. -/
theorem cgs_succ_x (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).x =
    (cgs A b x₀ rs₀ j).x
      + cgsAlpha A b x₀ rs₀ j • ((cgs A b x₀ rs₀ j).u + cgsQ A b x₀ rs₀ j) := rfl

/-- **Algorithm 7.6**, line 7: `r_{j+1} = r_j - α_j A (u_j + q_j)`. -/
theorem cgs_succ_r (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).r =
    (cgs A b x₀ rs₀ j).r
      - cgsAlpha A b x₀ rs₀ j • op A ((cgs A b x₀ rs₀ j).u + cgsQ A b x₀ rs₀ j) := rfl

/-- **Algorithm 7.6**, line 9: `u_{j+1} = r_{j+1} + β_j q_j`. -/
theorem cgs_succ_u (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).u =
    (cgs A b x₀ rs₀ (j + 1)).r + cgsBeta A b x₀ rs₀ j • cgsQ A b x₀ rs₀ j := rfl

/-- **Algorithm 7.6**, line 10: `p_{j+1} = u_{j+1} + β_j (q_j + β_j p_j)`. -/
theorem cgs_succ_p (j : ℕ) : (cgs A b x₀ rs₀ (j + 1)).p =
    (cgs A b x₀ rs₀ (j + 1)).u
      + cgsBeta A b x₀ rs₀ j • (cgsQ A b x₀ rs₀ j + cgsBeta A b x₀ rs₀ j • (cgs A b x₀ rs₀ j).p) :=
  rfl

/-- The CGS residual is the true residual of the CGS iterate. -/
theorem cgs_residual (j : ℕ) : (cgs A b x₀ rs₀ j).r = b - op A (cgs A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [cgs_succ_r, cgs_succ_x, ih, map_add, map_smul]
    abel

/-- **The step that removes the transpose**: a bilinear expression in `p(A) r_0` and `q̄(Aᴴ) r*_0`
is one in `(q p)(A) r_0` and `r*_0`.  This is `BiLanczos.inner_aeval_map_eq` at the pair `(op A, op
Aᴴ)`, and it is what turns `α_j = (φ_j(A) r_0, φ_j(Aᴴ) r*_0)/(A π_j(A) r_0, π_j(Aᴴ) r*_0)` into
`(φ_j²(A) r_0, r*_0)/(A π_j²(A) r_0, r*_0)`. -/
theorem inner_aeval_conjTranspose_aeval (p q : 𝕜[X]) (v w : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 (aeval (op Aᴴ) (q.map (starRingEnd 𝕜)) w) (aeval (op A) p v)
      = inner 𝕜 w (aeval (op A) (q * p) v) := by
  rw [BiLanczos.inner_aeval_map_eq (inner_op_conjTranspose A) q, aeval_mul_apply]

variable {A b x₀ rs₀}

/-- The numerator of `α_j` (which is the denominator of `β_j`): `(r_j, r*_j) = (φ_j²(A) r_0, r*_0)`.
-/
private theorem inner_bcg_residual_eq {j : ℕ}
    (hr : (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀)) :
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r
      = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r := by
  obtain ⟨hbr, -, hbrs, -⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  rw [hbr, hbrs, inner_aeval_conjTranspose_aeval, hr, ← sq]

/-- The denominator of `α_j`: `(A p_j, p*_j) = (A π_j²(A) r_0, r*_0)`. -/
private theorem inner_bcg_direction_eq {j : ℕ}
    (hp : (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀)) :
    inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ j).p)
      = inner 𝕜 rs₀ (op A (cgs A b x₀ rs₀ j).p) := by
  obtain ⟨-, hbp, -, hbps⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  have hpoly : bcgDirectionPoly A b x₀ rs₀ j * (X * bcgDirectionPoly A b x₀ rs₀ j)
      = X * bcgDirectionPoly A b x₀ rs₀ j ^ 2 := by ring
  rw [hbp, hbps, ← aeval_apply_X_mul, inner_aeval_conjTranspose_aeval, hpoly, hp,
    aeval_apply_X_mul]

/-- The CGS `α_j` is the BCG one, given the polynomial form of `r_j` and `p_j`. -/
private theorem cgsAlpha_eq_aux {j : ℕ}
    (hr : (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀))
    (hp : (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀)) :
    cgsAlpha A b x₀ rs₀ j = bcgAlpha A b x₀ rs₀ j := by
  rw [cgsAlpha, bcgAlpha_eq, inner_bcg_residual_eq hr, inner_bcg_direction_eq hp]

/-- The CGS `β_j` is the BCG one, given the polynomial form of `r_j` and `r_{j+1}`. -/
private theorem cgsBeta_eq_aux {j : ℕ}
    (hr : (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀))
    (hr' : (cgs A b x₀ rs₀ (j + 1)).r
      = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) ^ 2) (b - op A x₀)) :
    cgsBeta A b x₀ rs₀ j = bcgBeta A b x₀ rs₀ j := by
  rw [cgsBeta, bcgBeta_eq, inner_bcg_residual_eq hr, inner_bcg_residual_eq hr']

/-- (7.44): `q_j = φ_{j+1}(A) π_j(A) r_0`, given the polynomial form of `u_j`, `p_j` and `α_j`. -/
private theorem cgsQ_eq_aux {j : ℕ}
    (hp : (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀))
    (hu : (cgs A b x₀ rs₀ j).u
      = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j) (b - op A x₀))
    (hα : cgsAlpha A b x₀ rs₀ j = bcgAlpha A b x₀ rs₀ j) :
    cgsQ A b x₀ rs₀ j
      = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j)
          (b - op A x₀) := by
  have hpoly : bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j
      = bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j
        - C (bcgAlpha A b x₀ rs₀ j) * (X * bcgDirectionPoly A b x₀ rs₀ j ^ 2) := by
    rw [bcgResidualPoly_succ]; ring
  rw [cgsQ, hu, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- (7.40)–(7.42): the three CGS vectors are the squared BCG polynomials evaluated at `A` on `r_0`.
The heart of the induction; `cgs_residual_eq` states it together with the coefficient identities. -/
private theorem cgs_vec_eq (j : ℕ) :
    (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).u
        = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hu⟩ := ih
    have hα := cgsAlpha_eq_aux hr hp
    have hq := cgsQ_eq_aux hp hu hα
    have hr' : (cgs A b x₀ rs₀ (j + 1)).r
        = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) ^ 2) (b - op A x₀) := by
      have hpoly : bcgResidualPoly A b x₀ rs₀ (j + 1) ^ 2
          = bcgResidualPoly A b x₀ rs₀ j ^ 2
            - C (bcgAlpha A b x₀ rs₀ j)
              * (X * (bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j
                  + bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j)) := by
        rw [bcgResidualPoly_succ]; ring
      rw [cgs_succ_r, hu, hq, hr, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul,
        aeval_apply_X_mul, aeval_apply_add]
    have hβ := cgsBeta_eq_aux hr hr'
    have hu' : (cgs A b x₀ rs₀ (j + 1)).u
        = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ (j + 1))
            (b - op A x₀) := by
      have hpoly : bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ (j + 1)
          = bcgResidualPoly A b x₀ rs₀ (j + 1) ^ 2
            + C (bcgBeta A b x₀ rs₀ j)
              * (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j) := by
        rw [bcgDirectionPoly_succ (A := A) (b := b) (x₀ := x₀) (rs₀ := rs₀) j]; ring
      rw [cgs_succ_u, hq, hr', hβ, hpoly, aeval_apply_add, aeval_apply_C_mul]
    refine ⟨hr', ?_, hu'⟩
    have hpoly : bcgDirectionPoly A b x₀ rs₀ (j + 1) ^ 2
        = bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ (j + 1)
          + C (bcgBeta A b x₀ rs₀ j)
            * (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j
              + C (bcgBeta A b x₀ rs₀ j) * bcgDirectionPoly A b x₀ rs₀ j ^ 2) := by
      rw [bcgDirectionPoly_succ (A := A) (b := b) (x₀ := x₀) (rs₀ := rs₀) j]; ring
    rw [cgs_succ_p, hu', hq, hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul, aeval_apply_add,
      aeval_apply_C_mul]

variable (A b x₀ rs₀)

/-- **(7.40)–(7.45)**: Algorithm 7.6 computes the *squared* BCG polynomials.  Its vectors are
`r_j = φ_j²(A) r_0`, `p_j = π_j²(A) r_0`, `u_j = φ_j(A) π_j(A) r_0` and `q_j = φ_{j+1}(A) π_j(A)
r_0` for the BCG polynomials of the same run, and its `α_j` and `β_j` are the BCG ones.  This is
what makes Algorithm 7.6 a method: it delivers the residual `φ_j²(A) r_0` of (7.34) without ever
applying `Aᴴ`.  No hypothesis is needed — the coefficients agree even where both are `0 / 0`. -/
theorem cgs_residual_eq (j : ℕ) :
    (cgs A b x₀ rs₀ j).r = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).p = aeval (op A) (bcgDirectionPoly A b x₀ rs₀ j ^ 2) (b - op A x₀) ∧
      (cgs A b x₀ rs₀ j).u
          = aeval (op A) (bcgResidualPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) ∧
        cgsQ A b x₀ rs₀ j
          = aeval (op A) (bcgResidualPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) ∧
        cgsAlpha A b x₀ rs₀ j = bcgAlpha A b x₀ rs₀ j ∧
        cgsBeta A b x₀ rs₀ j = bcgBeta A b x₀ rs₀ j := by
  obtain ⟨hr, hp, hu⟩ := cgs_vec_eq (A := A) (b := b) (x₀ := x₀) (rs₀ := rs₀) j
  have hα := cgsAlpha_eq_aux hr hp
  have hr' := (cgs_vec_eq (A := A) (b := b) (x₀ := x₀) (rs₀ := rs₀) (j + 1)).1
  exact ⟨hr, hp, hu, cgsQ_eq_aux hp hu hα, hα, cgsBeta_eq_aux hr hr'⟩

end CGS

/-! ### §7.4.2: Algorithm 7.7, BICGSTAB -/

section BICGSTAB

/-- The state `(x_j, r_j, p_j)` of **Algorithm 7.7**; the half-step residual `s_j` of line 5 is read
off it by `bicgstabS`. -/
@[ext]
structure BICGSTABState (E : Type*) where
  /-- The iterate `x_j`. -/
  x : E
  /-- The residual `r_j`, which is `ψ_j(A) φ_j(A) r_0`. -/
  r : E
  /-- The direction `p_j`, which is `ψ_j(A) π_j(A) r_0`. -/
  p : E

/-- One pass through lines 4–10 of **Algorithm 7.7**, on the state `(x_j, r_j, p_j)`. -/
noncomputable def bicgstabStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (s : BICGSTABState (EuclideanSpace 𝕜 (Fin n))) : BICGSTABState (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (op A s.p)
  let sv : EuclideanSpace 𝕜 (Fin n) := s.r - α • op A s.p
  let ω : 𝕜 := inner 𝕜 (op A sv) sv / inner 𝕜 (op A sv) (op A sv)
  let r : EuclideanSpace 𝕜 (Fin n) := sv - ω • op A sv
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r * (α / ω)
  { x := s.x + α • s.p + ω • sv, r := r, p := r + β • (s.p - ω • op A s.p) }

/-- **Algorithm 7.7** (BICGSTAB, van der Vorst) run for `k` steps from `x_0`, with the shadow
residual `r*_0` initialized to an arbitrary `rs₀`.  Lines 1 and 2 set `p_0 = r_0 = b - A x_0`. -/
noncomputable def bicgstab (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → BICGSTABState (EuclideanSpace 𝕜 (Fin n))
  | 0 => { x := x₀, r := b - op A x₀, p := b - op A x₀ }
  | k + 1 => bicgstabStep A rs₀ (bicgstab A b x₀ rs₀ k)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 7.7**, lines 1 and 2. -/
@[simp] theorem bicgstab_zero :
    bicgstab A b x₀ rs₀ 0 = { x := x₀, r := b - op A x₀, p := b - op A x₀ } := rfl

/-- One pass of **Algorithm 7.7**. -/
theorem bicgstab_succ (k : ℕ) :
    bicgstab A b x₀ rs₀ (k + 1) = bicgstabStep A rs₀ (bicgstab A b x₀ rs₀ k) := rfl

/-- **Algorithm 7.7**, line 4: `α_j = (r_j, r*_0)/(A p_j, r*_0)`. -/
noncomputable def bicgstabAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r / inner 𝕜 rs₀ (op A (bicgstab A b x₀ rs₀ j).p)

/-- **Algorithm 7.7**, line 5: `s_j = r_j - α_j A p_j`. -/
noncomputable def bicgstabS (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  (bicgstab A b x₀ rs₀ j).r - bicgstabAlpha A b x₀ rs₀ j • op A (bicgstab A b x₀ rs₀ j).p

/-- **Algorithm 7.7**, line 6: `ω_j = (A s_j, s_j)/(A s_j, A s_j)`. -/
noncomputable def bicgstabOmega (j : ℕ) : 𝕜 :=
  inner 𝕜 (op A (bicgstabS A b x₀ rs₀ j)) (bicgstabS A b x₀ rs₀ j) /
    inner 𝕜 (op A (bicgstabS A b x₀ rs₀ j)) (op A (bicgstabS A b x₀ rs₀ j))

/-- **Algorithm 7.7**, line 9: `β_j = ((r_{j+1}, r*_0)/(r_j, r*_0)) (α_j/ω_j)`. -/
noncomputable def bicgstabBeta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
    * (bicgstabAlpha A b x₀ rs₀ j / bicgstabOmega A b x₀ rs₀ j)

/-- **Algorithm 7.7**, line 7: `x_{j+1} = x_j + α_j p_j + ω_j s_j`. -/
theorem bicgstab_succ_x (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).x =
    (bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p
      + bicgstabOmega A b x₀ rs₀ j • bicgstabS A b x₀ rs₀ j := rfl

/-- **Algorithm 7.7**, line 8: `r_{j+1} = s_j - ω_j A s_j`. -/
theorem bicgstab_succ_r (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).r =
    bicgstabS A b x₀ rs₀ j - bicgstabOmega A b x₀ rs₀ j • op A (bicgstabS A b x₀ rs₀ j) := rfl

/-- **Algorithm 7.7**, line 10: `p_{j+1} = r_{j+1} + β_j (p_j - ω_j A p_j)`. -/
theorem bicgstab_succ_p (j : ℕ) : (bicgstab A b x₀ rs₀ (j + 1)).p =
    (bicgstab A b x₀ rs₀ (j + 1)).r + bicgstabBeta A b x₀ rs₀ j •
      ((bicgstab A b x₀ rs₀ j).p
        - bicgstabOmega A b x₀ rs₀ j • op A (bicgstab A b x₀ rs₀ j).p) := rfl

/-- The BICGSTAB residual is the true residual of the BICGSTAB iterate. -/
theorem bicgstab_residual (j : ℕ) :
    (bicgstab A b x₀ rs₀ j).r = b - op A (bicgstab A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [bicgstab_succ_r, bicgstab_succ_x, bicgstabS, ih, map_add, map_smul]
    abel

/-- (7.47): the **stabilizing polynomial** `ψ_j` of BICGSTAB, `ψ_0 = 1` and
`ψ_{j+1} = (1 - ω_j t) ψ_j` for the `ω_j` that Algorithm 7.7 computes. -/
noncomputable def bicgstabPoly (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) : ℕ → 𝕜[X]
  | 0 => 1
  | j + 1 => (1 - C (bicgstabOmega A b x₀ rs₀ j) * X) * bicgstabPoly A b x₀ rs₀ j

@[simp] theorem bicgstabPoly_zero : bicgstabPoly A b x₀ rs₀ 0 = 1 := rfl

/-- (7.47): `ψ_{j+1} = (1 - ω_j t) ψ_j`. -/
theorem bicgstabPoly_succ (j : ℕ) : bicgstabPoly A b x₀ rs₀ (j + 1) =
    (1 - C (bicgstabOmega A b x₀ rs₀ j) * X) * bicgstabPoly A b x₀ rs₀ j := rfl

/-- `deg ψ_j ≤ j`. -/
theorem bicgstabPoly_natDegree_le (j : ℕ) : (bicgstabPoly A b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsub : bicgstabPoly A b x₀ rs₀ (j + 1)
        = bicgstabPoly A b x₀ rs₀ j
          - C (bicgstabOmega A b x₀ rs₀ j) * (X * bicgstabPoly A b x₀ rs₀ j) := by
      rw [bicgstabPoly_succ]; ring
    rw [hsub]
    refine (natDegree_sub_le _ _).trans (max_le (ih.trans (Nat.le_succ j)) ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    simp only [natDegree_X]
    omega

/-- The leading coefficients obey `η_1^{(j+1)} = -ω_j η_1^{(j)}`, the second of the two relations
the derivation of (7.53) compares. -/
theorem bicgstabPoly_coeff_succ (j : ℕ) :
    (bicgstabPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -bicgstabOmega A b x₀ rs₀ j * (bicgstabPoly A b x₀ rs₀ j).coeff j := by
  have hsub : bicgstabPoly A b x₀ rs₀ (j + 1)
      = bicgstabPoly A b x₀ rs₀ j
        - C (bicgstabOmega A b x₀ rs₀ j) * (X * bicgstabPoly A b x₀ rs₀ j) := by
    rw [bicgstabPoly_succ]; ring
  rw [hsub, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (bicgstabPoly_natDegree_le A b x₀ rs₀ j) (Nat.lt_succ_self j)),
    coeff_C_mul, coeff_X_mul]
  ring

/-- `η_1^{(j)} = ∏_{i<j} (-ω_i)` does not vanish while no `ω_i` does. -/
theorem bicgstabPoly_coeff_ne_zero {j : ℕ}
    (hω : ∀ i < j, bicgstabOmega A b x₀ rs₀ i ≠ 0) :
    (bicgstabPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [bicgstabPoly_coeff_succ]
    exact mul_ne_zero (neg_ne_zero.2 (hω j (Nat.lt_succ_self j)))
      (ih fun i hi => hω i (by omega))

/-- `a b / (a c) = b / c` for `a ≠ 0`, the cancellation the leading-coefficient argument runs on. -/
private theorem mul_div_mul_left_cancel {a b c : 𝕜} (ha : a ≠ 0) : a * b / (a * c) = b / c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [div_eq_div_iff (mul_ne_zero ha hc) hc]
    ring

/-- **Only the leading coefficient survives**: for `deg q ≤ j` and `v` orthogonal to `𝒦_j(Aᴴ,
r*_0)`, `(r*_0, q(A) v) = q_j ((Aᴴ)^j r*_0, v)`.  This is the step "since `φ_j(A) r_0` is orthogonal
to all vectors `(Aᴴ)^k r*_0` with `k < j`, only the leading power is relevant" of the derivation of
(7.53). -/
private theorem inner_aeval_eq_coeff_mul {j : ℕ} {q : 𝕜[X]} (hq : q.natDegree ≤ j)
    {v : EuclideanSpace 𝕜 (Fin n)}
    (hv : ∀ u ∈ Krylov.subspace (op Aᴴ) rs₀ j, inner 𝕜 u v = 0) :
    inner 𝕜 rs₀ (aeval (op A) q v) = q.coeff j * inner 𝕜 ((op Aᴴ ^ j) rs₀) v := by
  have hz : ∀ i < j, inner 𝕜 rs₀ ((op A ^ i) v) = 0 := by
    intro i hi
    rw [← BiLanczos.inner_pow_apply_eq (inner_op_conjTranspose A) i rs₀ v]
    exact hv _ (Krylov.pow_apply_mem_subspace (op Aᴴ) rs₀ hi)
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hq) (op A), LinearMap.sum_apply, inner_sum,
    Finset.sum_eq_single j]
  · rw [LinearMap.smul_apply, inner_smul_right,
      BiLanczos.inner_pow_apply_eq (inner_op_conjTranspose A) j rs₀ v]
  · intro i hi hij
    rw [Finset.mem_range] at hi
    rw [LinearMap.smul_apply, inner_smul_right, hz i (by omega), mul_zero]
  · intro hc
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hc

variable {A b x₀ rs₀}

/-- **Proposition 7.2** against the whole shadow Krylov space: `r_j` and `A p_j` are orthogonal to
`𝒦_j(Aᴴ, r*_0)`. -/
private theorem inner_bcg_eq_zero {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) {j : ℕ} (hj : j ≤ m)
    {u : EuclideanSpace 𝕜 (Fin n)} (hu : u ∈ Krylov.subspace (op Aᴴ) rs₀ j) :
    inner 𝕜 u (bcg A b x₀ rs₀ j).r = 0 ∧ inner 𝕜 u (op A (bcg A b x₀ rs₀ j).p) = 0 := by
  have hb := (h.mono hj).toBCG
  rw [bcg_eq]
  exact ⟨BCG.inner_residual_eq_zero_of_mem_subspace hb hu,
    BCG.inner_apply_direction_eq_zero_of_mem_subspace hb hu⟩

/-- `ρ_j = (r_j, r*_j) = γ_1^{(j)} ((Aᴴ)^j r*_0, r_j)`. -/
private theorem inner_bcg_rs_r {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (bcg A b x₀ rs₀ j).rs (bcg A b x₀ rs₀ j).r
      = (bcgResidualPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((op Aᴴ ^ j) rs₀) (bcg A b x₀ rs₀ j).r := by
  obtain ⟨-, -, hbrs, -⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  rw [hbrs, BiLanczos.inner_aeval_map_eq (inner_op_conjTranspose A)]
  exact inner_aeval_eq_coeff_mul A rs₀ (bcgResidualPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => (inner_bcg_eq_zero h hj hu).1

/-- `(A p_j, p*_j) = γ_1^{(j)} ((Aᴴ)^j r*_0, A p_j)`: the leading coefficient of `π_j` is that of
`φ_j`. -/
private theorem inner_bcg_ps_ap {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (bcg A b x₀ rs₀ j).ps (op A (bcg A b x₀ rs₀ j).p)
      = (bcgResidualPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((op Aᴴ ^ j) rs₀) (op A (bcg A b x₀ rs₀ j).p) := by
  obtain ⟨-, -, -, hbps⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  rw [hbps, BiLanczos.inner_aeval_map_eq (inner_op_conjTranspose A),
    ← bcgDirectionPoly_coeff_self A b x₀ rs₀ j]
  refine inner_aeval_eq_coeff_mul A rs₀ (bcgDirectionPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => (inner_bcg_eq_zero h hj hu).2

/-- `ρ̃_j = (r_j, r*_0) = η_1^{(j)} ((Aᴴ)^j r*_0, r_j^{BCG})`, once `r_j = ψ_j(A) φ_j(A) r_0`. -/
private theorem inner_bicgstab_r {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) {j : ℕ} (hj : j ≤ m)
    (hr : (bicgstab A b x₀ rs₀ j).r
      = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀)) :
    inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
      = (bicgstabPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((op Aᴴ ^ j) rs₀) (bcg A b x₀ rs₀ j).r := by
  obtain ⟨hbr, -, -, -⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  rw [hr, aeval_mul_apply, ← hbr]
  exact inner_aeval_eq_coeff_mul A rs₀ (bicgstabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => (inner_bcg_eq_zero h hj hu).1

/-- `(A p_j, r*_0) = η_1^{(j)} ((Aᴴ)^j r*_0, A p_j^{BCG})`, once `p_j = ψ_j(A) π_j(A) r_0`. -/
private theorem inner_bicgstab_ap {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m) {j : ℕ} (hj : j ≤ m)
    (hp : (bicgstab A b x₀ rs₀ j).p
      = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j) (b - op A x₀)) :
    inner 𝕜 rs₀ (op A (bicgstab A b x₀ rs₀ j).p)
      = (bicgstabPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((op Aᴴ ^ j) rs₀) (op A (bcg A b x₀ rs₀ j).p) := by
  obtain ⟨-, hbp, -, -⟩ := bcg_residual_eq_aeval A b x₀ rs₀ j
  rw [hp, aeval_mul_apply, ← aeval_apply_apply, ← hbp]
  exact inner_aeval_eq_coeff_mul A rs₀ (bicgstabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => (inner_bcg_eq_zero h hj hu).2

/-- The BICGSTAB `α_j` is the BCG one, given the polynomial form of `r_j` and `p_j`: numerator and
denominator both lose their degree-`j` polynomial in favour of its leading coefficient, and the two
leading coefficients cancel. -/
private theorem bicgstabAlpha_eq_aux {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hω : ∀ i < m, bicgstabOmega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m)
    (hr : (bicgstab A b x₀ rs₀ j).r
      = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀))
    (hp : (bicgstab A b x₀ rs₀ j).p
      = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j) (b - op A x₀)) :
    bicgstabAlpha A b x₀ rs₀ j = bcgAlpha A b x₀ rs₀ j := by
  have hg : (bcgResidualPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
    intro hc
    exact h.inner_residual_ne_zero j hj (by rw [inner_bcg_rs_r h hj.le, hc, zero_mul])
  have he := bicgstabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  rw [bicgstabAlpha, bcgAlpha_eq, inner_bicgstab_r h hj.le hr, inner_bicgstab_ap h hj.le hp,
    inner_bcg_rs_r h hj.le, inner_bcg_ps_ap h hj.le, mul_div_mul_left_cancel he,
    mul_div_mul_left_cancel hg]

/-- (7.46), (7.52): the BICGSTAB vectors carry the stabilized BCG polynomials.  The induction
carries the coefficient identities with it, because the polynomials `φ_{j+1}` and `π_{j+1}` are
built from the BCG coefficients while the algorithm computes its own. -/
theorem bicgstab_residual_eq {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hω : ∀ i < m, bicgstabOmega A b x₀ rs₀ i ≠ 0) :
    ∀ j ≤ m, (bicgstab A b x₀ rs₀ j).r
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ j) (b - op A x₀) ∧
      (bicgstab A b x₀ rs₀ j).p
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)
            (b - op A x₀) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hjm : j < m := by omega
    have hα := bicgstabAlpha_eq_aux h hω hjm hr hp
    -- `s_j = ψ_j(A) φ_{j+1}(A) r_0`
    have hs : bicgstabS A b x₀ rs₀ j
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ (j + 1))
            (b - op A x₀) := by
      have hpoly : bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ (j + 1)
          = bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ j
            - C (bcgAlpha A b x₀ rs₀ j)
              * (X * (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j)) := by
        rw [bcgResidualPoly_succ]; ring
      rw [bicgstabS, hr, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    -- (7.52): `r_{j+1} = ψ_{j+1}(A) φ_{j+1}(A) r_0`
    have hr' : (bicgstab A b x₀ rs₀ (j + 1)).r
        = aeval (op A) (bicgstabPoly A b x₀ rs₀ (j + 1) * bcgResidualPoly A b x₀ rs₀ (j + 1))
            (b - op A x₀) := by
      have hpoly : bicgstabPoly A b x₀ rs₀ (j + 1) * bcgResidualPoly A b x₀ rs₀ (j + 1)
          = bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ (j + 1)
            - C (bicgstabOmega A b x₀ rs₀ j)
              * (X * (bicgstabPoly A b x₀ rs₀ j * bcgResidualPoly A b x₀ rs₀ (j + 1))) := by
        rw [bicgstabPoly_succ]; ring
      rw [bicgstab_succ_r, hs, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    refine ⟨hr', ?_⟩
    -- the direction needs `β_j` as well
    have hβ : bicgstabBeta A b x₀ rs₀ j = bcgBeta A b x₀ rs₀ j := by
      have hg : (bcgResidualPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
        intro hc
        exact h.inner_residual_ne_zero j hjm (by rw [inner_bcg_rs_r h hjm.le, hc, zero_mul])
      have hL : inner 𝕜 ((op Aᴴ ^ j) rs₀) (bcg A b x₀ rs₀ j).r ≠ 0 := by
        intro hc
        exact h.inner_residual_ne_zero j hjm (by rw [inner_bcg_rs_r h hjm.le, hc, mul_zero])
      have he := bicgstabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
      have hωj := hω j hjm
      rw [bicgstabBeta, bcgBeta_eq, inner_bicgstab_r h hjm.le hr, inner_bicgstab_r h hj hr',
        inner_bcg_rs_r h hjm.le, inner_bcg_rs_r h hj, bcgResidualPoly_coeff_succ,
        bicgstabPoly_coeff_succ, hα]
      field_simp
    have hpoly : bicgstabPoly A b x₀ rs₀ (j + 1) * bcgDirectionPoly A b x₀ rs₀ (j + 1)
        = bicgstabPoly A b x₀ rs₀ (j + 1) * bcgResidualPoly A b x₀ rs₀ (j + 1)
          + C (bcgBeta A b x₀ rs₀ j)
            * (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j
              - C (bicgstabOmega A b x₀ rs₀ j)
                * (X * (bicgstabPoly A b x₀ rs₀ j * bcgDirectionPoly A b x₀ rs₀ j))) := by
      rw [bcgDirectionPoly_succ (A := A) (b := b) (x₀ := x₀) (rs₀ := rs₀) j, bicgstabPoly_succ]
      ring
    rw [bicgstab_succ_p, hr', hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul, aeval_apply_sub,
      aeval_apply_C_mul, aeval_apply_X_mul]

/-- **(7.53)–(7.54)**: the BCG coefficients are computable from the BICGSTAB vectors alone,
`α_j = ρ̃_j/(A p_j, r*_0)` and `β_j = (ρ̃_{j+1}/ρ̃_j)(α_j/ω_j)` with `ρ̃_j = (r_j, r*_0)`.
The proof replaces `ψ_j(Aᴴ) r*_0` and `φ_j(Aᴴ) r*_0` by their leading terms — legitimate because
`r_j^{BCG}`
and `A p_j^{BCG}` are orthogonal to `(Aᴴ)^k r*_0` for `k < j` — and compares the two leading
coefficients, `η_1^{(j+1)} = -ω_j η_1^{(j)}` against `γ_1^{(j+1)} = -α_j γ_1^{(j)}`. -/
theorem equation_7_53 {m : ℕ} (h : BCGNoBreakdown A b x₀ rs₀ m)
    (hω : ∀ i < m, bicgstabOmega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    bcgAlpha A b x₀ rs₀ j
        = inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
          / inner 𝕜 rs₀ (op A (bicgstab A b x₀ rs₀ j).p) ∧
      bcgBeta A b x₀ rs₀ j
        = inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (bicgstab A b x₀ rs₀ j).r
          * (bcgAlpha A b x₀ rs₀ j / bicgstabOmega A b x₀ rs₀ j) := by
  obtain ⟨hr, hp⟩ := bicgstab_residual_eq h hω j hj.le
  have hα := bicgstabAlpha_eq_aux h hω hj hr hp
  refine ⟨hα.symm, ?_⟩
  have hg : (bcgResidualPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
    intro hc
    exact h.inner_residual_ne_zero j hj (by rw [inner_bcg_rs_r h hj.le, hc, zero_mul])
  have hL : inner 𝕜 ((op Aᴴ ^ j) rs₀) (bcg A b x₀ rs₀ j).r ≠ 0 := by
    intro hc
    exact h.inner_residual_ne_zero j hj (by rw [inner_bcg_rs_r h hj.le, hc, mul_zero])
  have he := bicgstabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  have hωj := hω j hj
  have hr' := (bicgstab_residual_eq h hω (j + 1) hj).1
  rw [bcgBeta_eq, inner_bicgstab_r h hj.le hr, inner_bicgstab_r h hj hr',
    inner_bcg_rs_r h hj.le, inner_bcg_rs_r h hj, bcgResidualPoly_coeff_succ,
    bicgstabPoly_coeff_succ]
  field_simp

variable (A b x₀ rs₀)

/-- **(7.55)**: `ω_j = (A s_j, s_j)/(A s_j, A s_j)` is the steepest-descent step in the residual
direction: the second half of the BICGSTAB update is `Projection.minResStep` from the half-step
iterate `x_j + α_j p_j`, whose residual is exactly `s_j`, and it minimizes `‖(I - ω A) s_j‖₂` over
`ω`. -/
theorem equation_7_55 (j : ℕ) :
    (bicgstab A b x₀ rs₀ (j + 1)).x
        = Projection.minResStep (op A) b
            ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) ∧
      IsMinRes (op A) b
        ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p)
        (𝕜 ∙ bicgstabS A b x₀ rs₀ j) (bicgstab A b x₀ rs₀ (j + 1)).x := by
  have hres : b - op A ((bicgstab A b x₀ rs₀ j).x
      + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) = bicgstabS A b x₀ rs₀ j := by
    rw [bicgstabS, bicgstab_residual, map_add, map_smul]
    abel
  have hstep : (bicgstab A b x₀ rs₀ (j + 1)).x
      = Projection.minResStep (op A) b
        ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p) := by
    rw [Projection.minResStep, Projection.step1, hres, bicgstab_succ_x]
    rfl
  refine ⟨hstep, ?_⟩
  have := Projection.minResStep_isMinRes (A := op A) (b := b)
    ((bicgstab A b x₀ rs₀ j).x + bicgstabAlpha A b x₀ rs₀ j • (bicgstab A b x₀ rs₀ j).p)
  rwa [hres, ← hstep] at this

end BICGSTAB

/-! ### §7.4.3: Algorithm 7.8, TFQMR -/

section TFQMR

/-- The state of **Algorithm 7.8** after `m` half-steps.  The vectors `v_m` and the scalars `ρ_m`,
`β_m` of the book are defined only at even `m`, so the corresponding fields carry the value from the
last even index; `α` carries `α_{m-1}`, which by (7.65) is `α_m` when `m` is odd. -/
structure TFQMRState (𝕜 E : Type*) where
  /-- The iterate `x_m`. -/
  x : E
  /-- The auxiliary residual `w_m`, the CGS residual `r_m` of the doubled-index notation. -/
  w : E
  /-- The direction `u_m` of (7.65). -/
  u : E
  /-- `v_{2j} = A p_{2j}`, carried unchanged through the odd steps. -/
  v : E
  /-- The search direction `d_m` of (7.78). -/
  d : E
  /-- `τ_m`, the quasi-residual norm of (7.82). -/
  τ : ℝ
  /-- `θ_m`, the tangent of the rotation angle. -/
  θ : ℝ
  /-- `η_m = c_m² α_{m-1}` of (7.78). -/
  η : 𝕜
  /-- `ρ_{2j} = (w_{2j}, r*_0)`, carried unchanged through the odd steps. -/
  ρ : 𝕜
  /-- `α_{m-1}`. -/
  α : 𝕜

/-- **Algorithm 7.8**, line 5: `α_m = ρ_m/(v_m, r*_0)` at even `m`, and `α_m = α_{m-1}` at odd `m`,
which is (7.65). -/
noncomputable def tfqmrStepAlpha (rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ)
    (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : 𝕜 :=
  if Even m then s.ρ / inner 𝕜 rs₀ s.v else s.α

/-- **Algorithm 7.8**, line 8: `w_{m+1} = w_m - α_m A u_m`. -/
noncomputable def tfqmrStepW (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : EuclideanSpace 𝕜 (Fin n) :=
  s.w - tfqmrStepAlpha rs₀ m s • op A s.u

/-- **Algorithm 7.8**, line 15: `β_{m-1} = ρ_{m+1}/ρ_{m-1}`, used at odd `m` only. -/
noncomputable def tfqmrStepBeta (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) : 𝕜 :=
  inner 𝕜 rs₀ (tfqmrStepW A rs₀ m s) / s.ρ

/-- One pass through the loop of **Algorithm 7.8**, at step `m`. -/
noncomputable def tfqmrStep (A : Matrix (Fin n) (Fin n) 𝕜) (rs₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) (s : TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := tfqmrStepAlpha rs₀ m s
  let w : EuclideanSpace 𝕜 (Fin n) := tfqmrStepW A rs₀ m s
  let β : 𝕜 := tfqmrStepBeta A rs₀ m s
  let d : EuclideanSpace 𝕜 (Fin n) := s.u + (((s.θ ^ 2 : ℝ) : 𝕜) / α * s.η) • s.d
  let θ : ℝ := ‖w‖ / s.τ
  let c : ℝ := (Real.sqrt (1 + θ ^ 2))⁻¹
  { x := s.x + (((c ^ 2 : ℝ) : 𝕜) * α) • d
    w := w
    u := if Even m then s.u - α • s.v else w + β • s.u
    v := if Even m then s.v else op A (w + β • s.u) + β • (op A s.u + β • s.v)
    d := d
    τ := s.τ * θ * c
    θ := θ
    η := ((c ^ 2 : ℝ) : 𝕜) * α
    ρ := if Even m then s.ρ else inner 𝕜 rs₀ w
    α := α }

/-- **Algorithm 7.8** (TFQMR, Freund) after `m` half-steps, from `x_0` and an arbitrary shadow
residual `r*_0`.  Lines 1–3 set `w_0 = u_0 = r_0 = b - A x_0`, `v_0 = A u_0`, `d_0 = 0`,
`τ_0 = ‖r_0‖₂` and `θ_0 = η_0 = 0`. -/
noncomputable def tfqmr (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) :
    ℕ → TFQMRState 𝕜 (EuclideanSpace 𝕜 (Fin n))
  | 0 =>
      { x := x₀, w := b - op A x₀, u := b - op A x₀, v := op A (b - op A x₀), d := 0,
        τ := ‖b - op A x₀‖, θ := 0, η := 0, ρ := inner 𝕜 rs₀ (b - op A x₀), α := 0 }
  | m + 1 => tfqmrStep A rs₀ m (tfqmr A b x₀ rs₀ m)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Algorithm 7.8**, lines 1–3. -/
@[simp] theorem tfqmr_zero :
    tfqmr A b x₀ rs₀ 0 =
      { x := x₀, w := b - op A x₀, u := b - op A x₀, v := op A (b - op A x₀), d := 0,
        τ := ‖b - op A x₀‖, θ := 0, η := 0, ρ := inner 𝕜 rs₀ (b - op A x₀), α := 0 } := rfl

/-- One pass of **Algorithm 7.8**. -/
theorem tfqmr_succ (m : ℕ) :
    tfqmr A b x₀ rs₀ (m + 1) = tfqmrStep A rs₀ m (tfqmr A b x₀ rs₀ m) := rfl

/-- The vector `u_m` of (7.65). -/
noncomputable abbrev tfqmrU (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).u

/-- The vector `w_m`, which is the CGS residual `r_m` of the doubled-index notation. -/
noncomputable abbrev tfqmrW (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).w

/-- The scalar `α_m` of (7.65). -/
noncomputable abbrev tfqmrAlpha (m : ℕ) : 𝕜 := (tfqmr A b x₀ rs₀ (m + 1)).α

/-- The scalar `τ_m` of (7.82), the running quasi-residual estimate. -/
noncomputable abbrev tfqmrTau (m : ℕ) : ℝ := (tfqmr A b x₀ rs₀ m).τ

/-- The scalar `θ_m` of (7.82). -/
noncomputable abbrev tfqmrTheta (m : ℕ) : ℝ := (tfqmr A b x₀ rs₀ m).θ

/-- The scalar `c_m = (1 + θ_m²)^{-1/2}` of (7.82). -/
noncomputable abbrev tfqmrC (m : ℕ) : ℝ :=
  (Real.sqrt (1 + tfqmrTheta A b x₀ rs₀ m ^ 2))⁻¹

/-- The scalar `η_m = c_m² α_{m-1}` of (7.78). -/
noncomputable abbrev tfqmrEta (m : ℕ) : 𝕜 := (tfqmr A b x₀ rs₀ m).η

/-- The direction `d_m` of (7.78). -/
noncomputable abbrev tfqmrD (m : ℕ) : EuclideanSpace 𝕜 (Fin n) := (tfqmr A b x₀ rs₀ m).d

/-- **Algorithm 7.8**, line 8: `w_{m+1} = w_m - α_m A u_m`. -/
theorem tfqmr_succ_w (m : ℕ) : tfqmrW A b x₀ rs₀ (m + 1) =
    tfqmrW A b x₀ rs₀ m - tfqmrAlpha A b x₀ rs₀ m • op A (tfqmrU A b x₀ rs₀ m) := rfl

/-- **Algorithm 7.8**, line 9: `d_{m+1} = u_m + (θ_m²/α_m) η_m d_m`. -/
theorem tfqmr_succ_d (m : ℕ) : tfqmrD A b x₀ rs₀ (m + 1) =
    tfqmrU A b x₀ rs₀ m
      + (((tfqmrTheta A b x₀ rs₀ m ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ m
        * tfqmrEta A b x₀ rs₀ m) • tfqmrD A b x₀ rs₀ m := rfl

/-- **Algorithm 7.8**, line 10: `θ_{m+1} = ‖w_{m+1}‖₂/τ_m`. -/
theorem tfqmr_succ_theta (m : ℕ) : tfqmrTheta A b x₀ rs₀ (m + 1) =
    ‖tfqmrW A b x₀ rs₀ (m + 1)‖ / tfqmrTau A b x₀ rs₀ m := rfl

/-- **Algorithm 7.8**, line 11: `τ_{m+1} = τ_m θ_{m+1} c_{m+1}`. -/
theorem tfqmr_succ_tau (m : ℕ) : tfqmrTau A b x₀ rs₀ (m + 1) =
    tfqmrTau A b x₀ rs₀ m * tfqmrTheta A b x₀ rs₀ (m + 1) * tfqmrC A b x₀ rs₀ (m + 1) := rfl

/-- **Algorithm 7.8**, line 11: `η_{m+1} = c_{m+1}² α_m`. -/
theorem tfqmr_succ_eta (m : ℕ) : tfqmrEta A b x₀ rs₀ (m + 1) =
    ((tfqmrC A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) * tfqmrAlpha A b x₀ rs₀ m := rfl

/-- **Algorithm 7.8**, line 12: `x_{m+1} = x_m + η_{m+1} d_{m+1}`. -/
theorem tfqmr_succ_x (m : ℕ) : (tfqmr A b x₀ rs₀ (m + 1)).x =
    (tfqmr A b x₀ rs₀ m).x + tfqmrEta A b x₀ rs₀ (m + 1) • tfqmrD A b x₀ rs₀ (m + 1) := rfl

/-- **Algorithm 7.8**, line 5, at even `m`. -/
theorem tfqmr_alpha_even {m : ℕ} (hm : Even m) : tfqmrAlpha A b x₀ rs₀ m =
    (tfqmr A b x₀ rs₀ m).ρ / inner 𝕜 rs₀ (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- (7.65) at odd `m`: `α_m = α_{m-1}`. -/
theorem tfqmr_alpha_odd {m : ℕ} (hm : ¬ Even m) :
    tfqmrAlpha A b x₀ rs₀ m = (tfqmr A b x₀ rs₀ m).α := ite_eq_right hm

/-- **Algorithm 7.8**, line 6, at even `m`: `u_{m+1} = u_m - α_m v_m`. -/
theorem tfqmr_succ_u_even {m : ℕ} (hm : Even m) : tfqmrU A b x₀ rs₀ (m + 1) =
    tfqmrU A b x₀ rs₀ m - tfqmrAlpha A b x₀ rs₀ m • (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- `v` is untouched at even `m`. -/
theorem tfqmr_succ_v_even {m : ℕ} (hm : Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).v = (tfqmr A b x₀ rs₀ m).v := ite_eq_left hm

/-- `ρ` is untouched at even `m`. -/
theorem tfqmr_succ_rho_even {m : ℕ} (hm : Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).ρ = (tfqmr A b x₀ rs₀ m).ρ := ite_eq_left hm

/-- **Algorithm 7.8**, line 14, at odd `m`: `ρ_{m+1} = (w_{m+1}, r*_0)`. -/
theorem tfqmr_succ_rho_odd {m : ℕ} (hm : ¬ Even m) :
    (tfqmr A b x₀ rs₀ (m + 1)).ρ = inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) := ite_eq_right hm

/-- **Algorithm 7.8**, line 16, at odd `m`: `u_{m+1} = w_{m+1} + β_{m-1} u_m`. -/
theorem tfqmr_succ_u_odd {m : ℕ} (hm : ¬ Even m) : tfqmrU A b x₀ rs₀ (m + 1) =
    tfqmrW A b x₀ rs₀ (m + 1)
      + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
        • tfqmrU A b x₀ rs₀ m := ite_eq_right hm

/-- **Algorithm 7.8**, line 17, at odd `m`:
`v_{m+1} = A u_{m+1} + β_{m-1}(A u_m + β_{m-1} v_{m-1})`. -/
theorem tfqmr_succ_v_odd {m : ℕ} (hm : ¬ Even m) : (tfqmr A b x₀ rs₀ (m + 1)).v =
    op A (tfqmrU A b x₀ rs₀ (m + 1))
      + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
        • (op A (tfqmrU A b x₀ rs₀ m)
          + (inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (m + 1)) / (tfqmr A b x₀ rs₀ m).ρ)
            • (tfqmr A b x₀ rs₀ m).v) := by
  rw [tfqmr_succ_u_odd A b x₀ rs₀ hm]
  exact ite_eq_right hm

/-- The even half-steps of Algorithm 7.8 carry the CGS state of Algorithm 7.6. -/
private theorem tfqmr_even_state (j : ℕ) :
    tfqmrW A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).r ∧
      tfqmrU A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).u ∧
      (tfqmr A b x₀ rs₀ (2 * j)).v = op A (cgs A b x₀ rs₀ j).p ∧
      (tfqmr A b x₀ rs₀ (2 * j)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r := by
  induction j with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨hw, hu, hv, hρ⟩ := ih
    have hev : Even (2 * j) := ⟨j, by ring⟩
    have hod : ¬ Even (2 * j + 1) := by rw [Nat.even_add_one, not_not]; exact hev
    have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    have hα : tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j := by
      rw [tfqmr_alpha_even A b x₀ rs₀ hev, hρ, hv, cgsAlpha]
    have hα1 : tfqmrAlpha A b x₀ rs₀ (2 * j + 1) = cgsAlpha A b x₀ rs₀ j := by
      rw [tfqmr_alpha_odd A b x₀ rs₀ hod]; exact hα
    have hu1 : tfqmrU A b x₀ rs₀ (2 * j + 1) = cgsQ A b x₀ rs₀ j := by
      rw [tfqmr_succ_u_even A b x₀ rs₀ hev, hu, hv, hα, cgsQ]
    have hw1 : tfqmrW A b x₀ rs₀ (2 * j + 1)
        = (cgs A b x₀ rs₀ j).r - cgsAlpha A b x₀ rs₀ j • op A (cgs A b x₀ rs₀ j).u := by
      rw [tfqmr_succ_w A b x₀ rs₀ (2 * j), hw, hu, hα]
    have hw2 : tfqmrW A b x₀ rs₀ (2 * j + 1 + 1) = (cgs A b x₀ rs₀ (j + 1)).r := by
      rw [tfqmr_succ_w A b x₀ rs₀ (2 * j + 1), hw1, hu1, hα1, cgs_succ_r, map_add, smul_add]
      abel
    have hρ1 : (tfqmr A b x₀ rs₀ (2 * j + 1)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r := by
      rw [tfqmr_succ_rho_even A b x₀ rs₀ hev]; exact hρ
    have hβ : inner 𝕜 rs₀ (tfqmrW A b x₀ rs₀ (2 * j + 1 + 1)) / (tfqmr A b x₀ rs₀ (2 * j + 1)).ρ
        = cgsBeta A b x₀ rs₀ j := by
      rw [hw2, hρ1, cgsBeta]
    have hu2 : tfqmrU A b x₀ rs₀ (2 * j + 1 + 1) = (cgs A b x₀ rs₀ (j + 1)).u := by
      rw [tfqmr_succ_u_odd A b x₀ rs₀ hod, hβ, hw2, hu1, cgs_succ_u]
    refine ⟨by rw [hidx]; exact hw2, by rw [hidx]; exact hu2, ?_, ?_⟩
    · rw [hidx, tfqmr_succ_v_odd A b x₀ rs₀ hod, hβ, hu2, hu1,
        tfqmr_succ_v_even A b x₀ rs₀ hev, hv]
      simp only [cgs_succ_p, map_add, map_smul]
    · rw [hidx, tfqmr_succ_rho_odd A b x₀ rs₀ hod, hw2]

/-- **(7.56)–(7.62)**: doubling the subscripts of Algorithm 7.6 gives Algorithm 7.8.  The even
half-steps carry the CGS state — `w_{2j} = r_j`, `u_{2j} = u_j`, `v_{2j} = A p_j`,
`ρ_{2j} = (r_j, r*_0)` — the odd ones carry `u_{2j+1} = q_j` of (7.57), and the step lengths agree,
`α_{2j} = α_{2j+1} = α_j`, which is (7.65). -/
theorem tfqmr_eq_cgs (j : ℕ) :
    tfqmrW A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).r ∧
      tfqmrU A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).u ∧
      (tfqmr A b x₀ rs₀ (2 * j)).v = op A (cgs A b x₀ rs₀ j).p ∧
      (tfqmr A b x₀ rs₀ (2 * j)).ρ = inner 𝕜 rs₀ (cgs A b x₀ rs₀ j).r ∧
      tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j ∧
      tfqmrAlpha A b x₀ rs₀ (2 * j + 1) = cgsAlpha A b x₀ rs₀ j ∧
      tfqmrU A b x₀ rs₀ (2 * j + 1) = cgsQ A b x₀ rs₀ j := by
  obtain ⟨hw, hu, hv, hρ⟩ := tfqmr_even_state A b x₀ rs₀ j
  have hev : Even (2 * j) := ⟨j, by ring⟩
  have hod : ¬ Even (2 * j + 1) := by rw [Nat.even_add_one, not_not]; exact hev
  have hα : tfqmrAlpha A b x₀ rs₀ (2 * j) = cgsAlpha A b x₀ rs₀ j := by
    rw [tfqmr_alpha_even A b x₀ rs₀ hev, hρ, hv, cgsAlpha]
  refine ⟨hw, hu, hv, hρ, hα, ?_, ?_⟩
  · rw [tfqmr_alpha_odd A b x₀ rs₀ hod]; exact hα
  · rw [tfqmr_succ_u_even A b x₀ rs₀ hev, hu, hv, hα, cgsQ]

/-- (7.66)–(7.67): the CGS iterates extended to half steps, `x̃_m = x_0 + U_m z_m` with
`z_m = (α_0, …, α_{m-1})ᵀ`.  For even `m` these are the iterates of Algorithm 7.6
(`cgsHalfIterate_two_mul`); the odd ones are the intermediate iterates
`x_{j+1/2} = x_j + α_j u_j` that Algorithm 7.6 does not name. -/
noncomputable def cgsHalfIterate (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + ∑ i ∈ Finset.range m, tfqmrAlpha A b x₀ rs₀ i • tfqmrU A b x₀ rs₀ i

/-- (7.67): `x̃_m = x̃_{m-1} + α_{m-1} u_{m-1}`. -/
theorem cgsHalfIterate_succ (m : ℕ) : cgsHalfIterate A b x₀ rs₀ (m + 1) =
    cgsHalfIterate A b x₀ rs₀ m + tfqmrAlpha A b x₀ rs₀ m • tfqmrU A b x₀ rs₀ m := by
  rw [cgsHalfIterate, cgsHalfIterate, Finset.sum_range_succ, add_assoc]

/-- **(7.63)–(7.64)**: the two half-steps of `x_{2j} → x_{2j+2}` compose to the CGS step, so the
even-indexed half iterates are the iterates of Algorithm 7.6. -/
theorem cgsHalfIterate_two_mul (j : ℕ) :
    cgsHalfIterate A b x₀ rs₀ (2 * j) = (cgs A b x₀ rs₀ j).x := by
  induction j with
  | zero => simp [cgsHalfIterate]
  | succ j ih =>
    obtain ⟨-, hu, -, -, hα, hα1, hu1⟩ := tfqmr_eq_cgs A b x₀ rs₀ j
    have hidx : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [hidx, cgsHalfIterate_succ, cgsHalfIterate_succ, ih, hu, hu1, hα, hα1, cgs_succ_x,
      smul_add, add_assoc]

/-! #### (7.68)–(7.76): the two-family Hessenberg relation -/

/-- (7.72), (7.81): the bidiagonal coefficient array `H̄_m = Δ_{m+1} B̄_m`, with `δ_j/α_j` on the
diagonal and `-δ_{j+1}/α_j` below it, for a step-length sequence `α` and a column scaling `δ`. -/
noncomputable def tfqmrCoeff (α δ : ℕ → 𝕜) : ℕ → ℕ → 𝕜 := fun i j =>
  if i = j then δ j / α j else if i = j + 1 then -(δ i / α j) else 0

variable (α δ : ℕ → 𝕜)

@[simp] theorem tfqmrCoeff_self (j : ℕ) : tfqmrCoeff α δ j j = δ j / α j := ite_eq_left rfl

@[simp] theorem tfqmrCoeff_succ_self (j : ℕ) :
    tfqmrCoeff α δ (j + 1) j = -(δ (j + 1) / α j) := by
  rw [tfqmrCoeff, ite_eq_right (Nat.succ_ne_self j), ite_eq_left rfl]

theorem tfqmrCoeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) : tfqmrCoeff α δ i j = 0 := by
  rw [tfqmrCoeff, ite_eq_right h₁, ite_eq_right h₂]

variable {α δ}

variable {A b x₀ rs₀}

/-- (7.69): `α_m A u_m = w_m - w_{m+1}`, the only relation Algorithm 7.8 needs between the two
families. -/
theorem tfqmr_smul_apply_u (m : ℕ) :
    tfqmrAlpha A b x₀ rs₀ m • op A (tfqmrU A b x₀ rs₀ m)
      = tfqmrW A b x₀ rs₀ m - tfqmrW A b x₀ rs₀ (m + 1) := by
  rw [tfqmr_succ_w]
  abel

/-- **Algorithm 7.8 has not broken down seriously**: wherever a step length vanishes, so does
`A u_m`.  This is exactly what (7.69) needs at a *regular* termination — once `w_M = 0` the
algorithm produces `u_m = 0` and `α_m = 0` for every `m ≥ M`, and `A u_m = (w_m - w_{m+1})/α_m`
survives with both sides `0` — while it excludes a genuine breakdown, where `ρ_{2j}` vanishes with
`w_{2j} ≠ 0`.  It is the analogue of `NoSeriousBreakdown` for Algorithm 7.1, and like it it is a
*conditional* hypothesis: `∀ m, α_m ≠ 0` is unsatisfiable in finite dimension, because Algorithm
7.3 terminates. -/
structure TFQMRNoSeriousBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) : Prop where
  /-- At a vanishing step length the direction is annihilated by `A`. -/
  apply_u_eq_zero : ∀ m, tfqmrAlpha A b x₀ rs₀ m = 0 → op A (tfqmrU A b x₀ rs₀ m) = 0

/-- **(7.68)–(7.73)**: `A u_i = (w_i - w_{i+1})/α_i`, which in matrix form is `A U_m = R_{m+1} B̄_m`
of (7.70); after the column scaling `R_{m+1} Δ_{m+1}⁻¹` of (7.73) it is a *two-family* Hessenberg
relation `Krylov.HessenbergRelation₂` — the iterates expand in the `u`-vectors, the residuals in the
`w`-vectors — with the bidiagonal `H̄_m = Δ_{m+1} B̄_m`.  The scaling `δ` is arbitrary, which is
what P-7.9 asks about; it is asked only to vanish where the column it scales does, which a nonzero
scaling satisfies vacuously and the normalization `δ_i = ‖w_i‖₂` of (7.73) satisfies exactly. -/
theorem equation_7_70 {δ : ℕ → 𝕜} (h : TFQMRNoSeriousBreakdown A b x₀ rs₀)
    (hδ : ∀ i, δ i = 0 → tfqmrW A b x₀ rs₀ i = 0) :
    (∀ i, op A (tfqmrU A b x₀ rs₀ i)
        = (tfqmrAlpha A b x₀ rs₀ i)⁻¹ • (tfqmrW A b x₀ rs₀ i - tfqmrW A b x₀ rs₀ (i + 1))) ∧
      Krylov.HessenbergRelation₂ (op A) (tfqmrU A b x₀ rs₀)
        (fun i => (δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) := by
  have hAu : ∀ i, op A (tfqmrU A b x₀ rs₀ i)
      = (tfqmrAlpha A b x₀ rs₀ i)⁻¹ • (tfqmrW A b x₀ rs₀ i - tfqmrW A b x₀ rs₀ (i + 1)) := by
    intro i
    rcases eq_or_ne (tfqmrAlpha A b x₀ rs₀ i) 0 with h0 | h0
    · rw [h.apply_u_eq_zero i h0, ← tfqmr_smul_apply_u i, h0, zero_smul, smul_zero]
    · rw [← tfqmr_smul_apply_u i, smul_smul, inv_mul_cancel₀ h0, one_smul]
  have key : ∀ (i : ℕ) (c : 𝕜),
      (δ i / c) • ((δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) = c⁻¹ • tfqmrW A b x₀ rs₀ i := by
    intro i c
    rcases eq_or_ne (δ i) 0 with h0 | h0
    · rw [hδ i h0, smul_zero, smul_zero, smul_zero]
    · rw [smul_smul, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ h0, one_mul]
  refine ⟨hAu, ⟨fun j => ?_, fun i j hij => tfqmrCoeff_eq_zero _ _ (by omega) (by omega)⟩⟩
  have hzero : ∑ i ∈ Finset.range j,
      tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ i j • ((δ i)⁻¹ • tfqmrW A b x₀ rs₀ i) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_smul]
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, hzero,
    zero_add, tfqmrCoeff_self, tfqmrCoeff_succ_self, key, neg_smul, key, hAu j, smul_sub,
    sub_eq_add_neg]

/-- The bidiagonal `H_m` is lower triangular with nonzero diagonal, hence nonsingular. -/
private theorem isUnit_hessenbergSqOf_tfqmrCoeff {α δ : ℕ → 𝕜} (m : ℕ) (hα : ∀ i < m, α i ≠ 0)
    (hδ : ∀ i < m, δ i ≠ 0) : IsUnit (Krylov.hessenbergSqOf (tfqmrCoeff α δ) m) := by
  have hlow : (Krylov.hessenbergSqOf (tfqmrCoeff α δ) m).IsLowerTriangular := by
    intro i j hij
    have hlt : (i : ℕ) < (j : ℕ) := hij
    exact tfqmrCoeff_eq_zero _ _ (by omega) (by omega)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ hlow, isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro i _
  change tfqmrCoeff α δ (i : ℕ) (i : ℕ) ≠ 0
  rw [tfqmrCoeff_self]
  exact div_ne_zero (hδ _ i.isLt) (hα _ i.isLt)

/-- **(7.74)–(7.76)** and **P-7.9**: the CGS iterates, extended to half steps, satisfy the FOM
formula `x_m = x_0 + U_m H_m⁻¹(δ_0 e_1)` for the relation (7.70), because the vector of step lengths
`z_m = (α_0, …, α_{m-1})ᵀ` solves `H_m z_m = δ_0 e_1` — the two entries of each row of the
bidiagonal `H_m` cancel.  The identity holds for every scaling `Δ_{m+1}`, which answers P-7.9. -/
theorem equation_7_76 {δ : ℕ → 𝕜} (m : ℕ) (hα : ∀ i < m, tfqmrAlpha A b x₀ rs₀ i ≠ 0)
    (hδ : ∀ i < m, δ i ≠ 0) :
    Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m
          *ᵥ (fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ)) = Krylov.firstVec (δ 0) m ∧
      IsUnit (Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m) ∧
      cgsHalfIterate A b x₀ rs₀ m
        = x₀ + ∑ j : Fin m,
            ((Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m)⁻¹
              *ᵥ Krylov.firstVec (δ 0) m) j • tfqmrU A b x₀ rs₀ (j : ℕ) := by
  have happ : ∀ i j : Fin m,
      Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m i j
        = tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ (i : ℕ) (j : ℕ) := fun _ _ => rfl
  have hfv : ∀ i : Fin m,
      Krylov.firstVec (δ 0) m i = if (i : ℕ) = 0 then δ 0 else 0 := fun _ => rfl
  have hunit := isUnit_hessenbergSqOf_tfqmrCoeff (α := tfqmrAlpha A b x₀ rs₀) m hα hδ
  have hmul : Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m
      *ᵥ (fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ)) = Krylov.firstVec (δ 0) m := by
    funext i
    have him : (i : ℕ) < m := i.isLt
    rw [Matrix.mulVec, dotProduct, hfv]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [Finset.sum_eq_single i]
      · rw [happ, tfqmrCoeff_self, div_mul_cancel₀ _ (hα _ him), ite_eq_left h0, h0]
      · intro j _ hj
        have hjne : (j : ℕ) ≠ (i : ℕ) := fun hc => hj (Fin.ext hc)
        rw [happ, tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      have hkm : k < m := by omega
      have hne : (⟨k, hkm⟩ : Fin m) ≠ i := by
        intro hc
        have hik : (i : ℕ) = k := by rw [← hc]
        omega
      have hzr : ∀ j ∈ Finset.univ, j ∉ ({(⟨k, hkm⟩ : Fin m), i} : Finset (Fin m)) →
          Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m i j
            * tfqmrAlpha A b x₀ rs₀ (j : ℕ) = 0 := by
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        have h1 : (j : ℕ) ≠ k := fun hc => hj.1 (Fin.ext hc)
        have h2 : (j : ℕ) ≠ (i : ℕ) := fun hc => hj.2 (Fin.ext hc)
        rw [happ, tfqmrCoeff_eq_zero _ _ (by omega) (by omega), zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ ({(⟨k, hkm⟩ : Fin m), i} : Finset (Fin m))) hzr,
        Finset.sum_pair hne, happ, happ, ite_eq_right (by omega : ¬ (i : ℕ) = 0)]
      rw [show ((⟨k, hkm⟩ : Fin m) : ℕ) = k from rfl, hk, tfqmrCoeff_succ_self, tfqmrCoeff_self,
        neg_mul, div_mul_cancel₀ _ (hα k hkm), div_mul_cancel₀ _ (hα (k + 1) (by omega)),
        neg_add_cancel]
  refine ⟨hmul, hunit, ?_⟩
  have hinv : (Krylov.hessenbergSqOf (tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) δ) m)⁻¹
      *ᵥ Krylov.firstVec (δ 0) m = fun j : Fin m => tfqmrAlpha A b x₀ rs₀ (j : ℕ) := by
    rw [← hmul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), Matrix.one_mulVec]
  rw [hinv, cgsHalfIterate, Fin.sum_univ_eq_sum_range
    (fun i => tfqmrAlpha A b x₀ rs₀ i • tfqmrU A b x₀ rs₀ i) m]

/-! #### (7.77)–(7.83): the rotations and the quasi-minimal-residual property -/

/-- **Algorithm 7.8** has not broken down through step `m`: no step length vanishes — equivalently
no `ρ_{2j}` does, which is the book's condition on `r*_0` propagated — and no `w_i` does, so that
the columns of `R_{m+1}` can be normalized.  The bound is not decoration: `∀ i, α_i ≠ 0` is
unsatisfiable in finite dimension, Algorithm 7.3 terminating with `ρ_j = 0` from the grade on. -/
structure TFQMRNoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) : Prop where
  /-- No step length vanishes through step `m`. -/
  alpha_ne_zero : ∀ i ≤ m, tfqmrAlpha A b x₀ rs₀ i ≠ 0
  /-- No auxiliary residual vanishes through step `m`, so `δ_i = ‖w_i‖₂ ≠ 0`. -/
  w_ne_zero : ∀ i ≤ m, tfqmrW A b x₀ rs₀ i ≠ 0

/-- Running `m` steps without breakdown entails running `k ≤ m` steps without breakdown. -/
theorem TFQMRNoBreakdown.mono {A : Matrix (Fin n) (Fin n) 𝕜}
    {b x₀ rs₀ : EuclideanSpace 𝕜 (Fin n)} {m k : ℕ}
    (h : TFQMRNoBreakdown A b x₀ rs₀ m) (hk : k ≤ m) : TFQMRNoBreakdown A b x₀ rs₀ k :=
  ⟨fun i hi => h.alpha_ne_zero i (hi.trans hk), fun i hi => h.w_ne_zero i (hi.trans hk)⟩

variable (A b x₀ rs₀)

/-- (7.73): the column scaling `δ_i = ‖w_i‖₂` that makes the residual basis `R_{m+1} Δ_{m+1}⁻¹`
have unit columns. -/
noncomputable def tfqmrDelta (i : ℕ) : 𝕜 := ((‖tfqmrW A b x₀ rs₀ i‖ : ℝ) : 𝕜)

/-- (7.81): the bidiagonal `H̄_m = Δ_{m+1} B̄_m` at the normalization `δ_i = ‖w_i‖₂`. -/
noncomputable abbrev tfqmrH : ℕ → ℕ → 𝕜 :=
  tfqmrCoeff (tfqmrAlpha A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀)

theorem norm_tfqmrDelta (i : ℕ) : ‖tfqmrDelta A b x₀ rs₀ i‖ = ‖tfqmrW A b x₀ rs₀ i‖ := by
  rw [tfqmrDelta, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]

/-- `H̄_m` vanishes strictly above the diagonal. -/
theorem tfqmrH_eq_zero_of_lt {i j : ℕ} (hij : i < j) : tfqmrH A b x₀ rs₀ i j = 0 :=
  tfqmrCoeff_eq_zero _ _ (by omega) (by omega)

/-- The diagonal of `H̄_m` is `δ_j/α_j`. -/
theorem tfqmrH_self (j : ℕ) :
    tfqmrH A b x₀ rs₀ j j = tfqmrDelta A b x₀ rs₀ j / tfqmrAlpha A b x₀ rs₀ j :=
  tfqmrCoeff_self _ _ j

/-- The subdiagonal of `H̄_m` is `-δ_{j+1}/α_j`. -/
theorem tfqmrH_succ_self (j : ℕ) :
    tfqmrH A b x₀ rs₀ (j + 1) j = -(tfqmrDelta A b x₀ rs₀ (j + 1) / tfqmrAlpha A b x₀ rs₀ j) :=
  tfqmrCoeff_succ_self _ _ j

/-- `H̄_m` is upper Hessenberg, trivially: it is bidiagonal. -/
theorem tfqmrH_eq_zero_of_succ_lt {i j : ℕ} (hij : j + 1 < i) : tfqmrH A b x₀ rs₀ i j = 0 :=
  tfqmrCoeff_eq_zero _ _ (by omega) (by omega)

variable {A b x₀ rs₀}

theorem TFQMRNoBreakdown.delta_ne_zero {m : ℕ} (h : TFQMRNoBreakdown A b x₀ rs₀ m) {i : ℕ}
    (hi : i ≤ m) : tfqmrDelta A b x₀ rs₀ i ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_tfqmrDelta]
  exact norm_ne_zero_iff.2 (h.w_ne_zero i hi)

/-- `c_m > 0`: the cosine of Algorithm 7.8 is a positive real by construction. -/
private theorem tfqmrC_pos (m : ℕ) : 0 < tfqmrC A b x₀ rs₀ m :=
  inv_pos.2 (Real.sqrt_pos.2 (by positivity))

/-- `τ_m > 0` while no `w_m` vanishes. -/
private theorem tfqmrTau_pos : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    0 < tfqmrTau A b x₀ rs₀ m := by
  intro m
  induction m with
  | zero => intro h; exact norm_pos_iff.2 (h.w_ne_zero 0 le_rfl)
  | succ m ih =>
    intro h
    have ihm := ih (h.mono (Nat.le_succ m))
    rw [tfqmr_succ_tau, tfqmr_succ_theta]
    exact mul_pos (mul_pos ihm (div_pos (norm_pos_iff.2 (h.w_ne_zero (m + 1) le_rfl)) ihm))
      (tfqmrC_pos (m + 1))

/-- The scalar identity behind `c_{m+1} = τ_m/√(τ_m² + δ_{m+1}²)`. -/
private theorem sqrt_one_add_div_sq {t d : ℝ} (ht : 0 < t) :
    Real.sqrt (1 + (d / t) ^ 2) = Real.sqrt (t ^ 2 + d ^ 2) / t := by
  rw [eq_div_iff ht.ne']
  have hmul : Real.sqrt (1 + (d / t) ^ 2) * Real.sqrt (t ^ 2)
      = Real.sqrt ((1 + (d / t) ^ 2) * t ^ 2) := (Real.sqrt_mul (by positivity) _).symm
  rw [Real.sqrt_sq ht.le] at hmul
  rw [hmul]
  congr 1
  field_simp

/-- (7.82): `c_{m+1} = τ_m/√(τ_m² + δ_{m+1}²)`. -/
private theorem tfqmrC_succ_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    tfqmrC A b x₀ rs₀ (m + 1) = tfqmrTau A b x₀ rs₀ m
      / Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) := by
  rw [tfqmrC, tfqmr_succ_theta, sqrt_one_add_div_sq (tfqmrTau_pos m h), inv_div]

/-- (7.82): `τ_{m+1} = τ_m δ_{m+1}/√(τ_m² + δ_{m+1}²)`. -/
private theorem tfqmrTau_succ_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    tfqmrTau A b x₀ rs₀ (m + 1) = tfqmrTau A b x₀ rs₀ m * ‖tfqmrW A b x₀ rs₀ (m + 1)‖
      / Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) := by
  have ht := tfqmrTau_pos m h
  rw [tfqmr_succ_tau, tfqmr_succ_theta, tfqmrC_succ_eq m h]
  field_simp

/-- The subdiagonal entry of column `m` is untouched by the first `m` rotations. -/
private theorem rotated_succ_col (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) m (m + 1) m
      = -(tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ m) := by
  rw [Krylov.rotated_eq_of_le _ m (m + 1) m le_rfl]
  exact tfqmrCoeff_succ_self _ _ m

/-- The new diagonal entry after rotation `m`: `r_{m+1,m+1} = c_m δ_{m+1}/α_{m+1}`. -/
private theorem rotated_succ_diag (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1) (m + 1) (m + 1)
      = Krylov.givensC (tfqmrH A b x₀ rs₀) m
        * (tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ (m + 1)) := by
  rw [Krylov.rotated_succ_apply, ite_eq_right (by omega), ite_eq_left rfl,
    Krylov.rotated_eq_zero_of_lt_of_lt_col _ (fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij)
      m m (m + 1) (by omega) (by omega),
    Krylov.rotated_eq_of_le _ m (m + 1) (m + 1) le_rfl, tfqmrH_self A b x₀ rs₀ (m + 1),
    mul_zero, zero_add]

/-- The entry rotation `m` puts one row above the diagonal of column `m+1`. -/
private theorem rotated_above_diag (m : ℕ) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
      = starRingEnd 𝕜 (Krylov.givensS (tfqmrH A b x₀ rs₀) m)
        * (tfqmrDelta A b x₀ rs₀ (m + 1) / tfqmrAlpha A b x₀ rs₀ (m + 1)) := by
  rw [Krylov.rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega),
    Krylov.rotated_succ_apply, ite_eq_left rfl,
    Krylov.rotated_eq_zero_of_lt_of_lt_col _ (fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij)
      m m (m + 1) (by omega) (by omega),
    Krylov.rotated_eq_of_le _ m (m + 1) (m + 1) le_rfl, tfqmrH_self A b x₀ rs₀ (m + 1),
    mul_zero, zero_add]

/-- `√(x/a²) = √x/a` for `a > 0`. -/
private theorem sqrt_div_sq {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.sqrt (x / a ^ 2) = Real.sqrt x / a := by
  rw [eq_div_iff ha.ne']
  have hmul : Real.sqrt (x / a ^ 2) * Real.sqrt (a ^ 2) = Real.sqrt (x / a ^ 2 * a ^ 2) :=
    (Real.sqrt_mul (by positivity) _).symm
  rw [Real.sqrt_sq ha.le] at hmul
  rw [hmul, div_mul_cancel₀ _ (by positivity : (a : ℝ) ^ 2 ≠ 0)]

variable (A b x₀ rs₀)

/-- The unimodular factor that the book's real recurrence for `τ_m` does not see: `σ_m = ∏_{i<m}
|α_i|/α_i`, which is `1` over `ℝ`, where the book works. -/
private noncomputable def tfqmrPhase (m : ℕ) : 𝕜 :=
  ∏ i ∈ Finset.range m, ((‖tfqmrAlpha A b x₀ rs₀ i‖ : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ i

private theorem tfqmrPhase_zero : tfqmrPhase A b x₀ rs₀ 0 = 1 := by
  rw [tfqmrPhase, Finset.range_zero, Finset.prod_empty]

private theorem tfqmrPhase_succ (m : ℕ) : tfqmrPhase A b x₀ rs₀ (m + 1)
    = tfqmrPhase A b x₀ rs₀ m
      * (((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ m) := by
  rw [tfqmrPhase, tfqmrPhase, Finset.prod_range_succ]

variable {A b x₀ rs₀}

private theorem norm_tfqmrPhase (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    ‖tfqmrPhase A b x₀ rs₀ m‖ = 1 := by
  rw [tfqmrPhase, norm_prod]
  refine Finset.prod_eq_one fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [norm_div, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.2 (h.alpha_ne_zero i (by omega)))]

/-- `ρ_m = √(τ_m² + δ_{m+1}²)/|α_m|`, once the diagonal entry is known. -/
private theorem givensRho_eq_aux (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m)
    (hrot : Krylov.rotated (tfqmrH A b x₀ rs₀) m m m
      = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m
        / tfqmrAlpha A b x₀ rs₀ m) :
    Krylov.givensRho (tfqmrH A b x₀ rs₀) m
      = Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
        / ‖tfqmrAlpha A b x₀ rs₀ m‖ := by
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 (h.alpha_ne_zero m le_rfl)
  have hnaz : ‖tfqmrAlpha A b x₀ rs₀ m‖ ≠ 0 := hna.ne'
  rw [Krylov.givensRho, hrot, rotated_succ_col, norm_neg, norm_div, norm_div, norm_mul,
    RCLike.norm_ofReal, abs_of_pos (tfqmrTau_pos m h), norm_tfqmrPhase m h, mul_one,
    norm_tfqmrDelta,
    show (tfqmrTau A b x₀ rs₀ m / ‖tfqmrAlpha A b x₀ rs₀ m‖) ^ 2
        + (‖tfqmrW A b x₀ rs₀ (m + 1)‖ / ‖tfqmrAlpha A b x₀ rs₀ m‖) ^ 2
        = (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
          / ‖tfqmrAlpha A b x₀ rs₀ m‖ ^ 2 from by field_simp,
    sqrt_div_sq (by positivity) hna]

/-- **The rotations of Algorithm 6.12 on the bidiagonal `H̄_m`**: the quasi-residual scalar `γ_m` is
the book's `τ_m` times a unimodular factor, and the diagonal entry left by rotation `m` is that
divided by `α_m`.  Over `ℝ` the factor is `1` and this is `γ_{m+1} = τ_m` of the text after (7.83).
-/
private theorem tfqmr_rotation : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
        = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m ∧
      Krylov.rotated (tfqmrH A b x₀ rs₀) m m m
        = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) * tfqmrPhase A b x₀ rs₀ m
          / tfqmrAlpha A b x₀ rs₀ m := by
  intro m
  induction m with
  | zero =>
    intro _
    have hg : Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) 0
        = tfqmrDelta A b x₀ rs₀ 0 := rfl
    have hr : Krylov.rotated (tfqmrH A b x₀ rs₀) 0 0 0
        = tfqmrDelta A b x₀ rs₀ 0 / tfqmrAlpha A b x₀ rs₀ 0 := tfqmrH_self A b x₀ rs₀ 0
    have ht : tfqmrTau A b x₀ rs₀ 0 = ‖tfqmrW A b x₀ rs₀ 0‖ := rfl
    refine ⟨?_, ?_⟩
    · rw [hg, tfqmrPhase_zero, mul_one, tfqmrDelta, ht]
    · rw [hr, tfqmrPhase_zero, mul_one, tfqmrDelta, ht]
  | succ m ih =>
    intro h
    obtain ⟨hgam, hrot⟩ := ih (h.mono (Nat.le_succ m))
    have hαm := h.alpha_ne_zero m (by omega)
    have hαm' := h.alpha_ne_zero (m + 1) le_rfl
    have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m (h.mono (Nat.le_succ m))
    have hd : 0 < ‖tfqmrW A b x₀ rs₀ (m + 1)‖ := norm_pos_iff.2 (h.w_ne_zero (m + 1) le_rfl)
    have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 hαm
    have hS : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    have hSK : ((Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) : ℝ) : 𝕜)
        ≠ 0 := RCLike.ofReal_ne_zero.2 hS.ne'
    have hnaK : ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hna.ne'
    have hrho := givensRho_eq_aux m (h.mono (Nat.le_succ m)) hrot
    constructor
    · rw [Krylov.gamma_succ, Krylov.givensS, rotated_succ_col, hgam, hrho,
        tfqmrTau_succ_eq m (h.mono (Nat.le_succ m)), tfqmrPhase_succ, tfqmrDelta]
      push_cast
      field_simp
    · rw [rotated_succ_diag, Krylov.givensC, hrot, hrho,
        tfqmrTau_succ_eq m (h.mono (Nat.le_succ m)), tfqmrPhase_succ, tfqmrDelta]
      push_cast
      field_simp

/-- `ρ_m = √(τ_m² + δ_{m+1}²)/|α_m|`, and in particular `ρ_m > 0`. -/
private theorem givensRho_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.givensRho (tfqmrH A b x₀ rs₀) m
      = Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2)
        / ‖tfqmrAlpha A b x₀ rs₀ m‖ :=
  givensRho_eq_aux m h (tfqmr_rotation m h).2

private theorem givensRho_pos (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    0 < Krylov.givensRho (tfqmrH A b x₀ rs₀) m := by
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 (h.alpha_ne_zero m le_rfl)
  have ht := tfqmrTau_pos m h
  rw [givensRho_eq m h]
  have : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  positivity

/-- The text after (7.83): `γ_{m+1} = τ_m`, in modulus. -/
theorem norm_gamma_eq_tfqmrTau (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    ‖Krylov.gamma (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m‖ = tfqmrTau A b x₀ rs₀ m := by
  rw [(tfqmr_rotation m h).1, norm_mul, RCLike.norm_ofReal, abs_of_pos (tfqmrTau_pos m h),
    norm_tfqmrPhase m h, mul_one]

/-- `g_m = c̄_m γ_m = τ_m²/(ᾱ_m ρ_m)`: the unimodular factor cancels against its conjugate. -/
private theorem gvec_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
      = ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) ^ 2
        / (starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m)
          * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜)) := by
  obtain ⟨hgam, hrot⟩ := tfqmr_rotation m h
  have hαm := h.alpha_ne_zero m le_rfl
  have hcαm : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m) ≠ 0 := by simpa using hαm
  have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.2 (givensRho_pos m h).ne'
  have hσne : tfqmrPhase A b x₀ rs₀ m ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_tfqmrPhase m h]
    norm_num
  have hσinv : starRingEnd 𝕜 (tfqmrPhase A b x₀ rs₀ m) = (tfqmrPhase A b x₀ rs₀ m)⁻¹ := by
    field_simp
    rw [RCLike.conj_mul, norm_tfqmrPhase m h]
    norm_num
  rw [Krylov.gvec, Krylov.givensC, hrot, hgam]
  simp only [map_div₀, map_mul, RCLike.conj_ofReal, hσinv]
  field_simp

/-- **(7.78)**: `η_{m+1} = c_{m+1}² α_m` is exactly `g_m/ρ_m`, the DQGMRES step length. -/
private theorem gvec_eq_givensRho_mul_eta (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
      = ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) * tfqmrEta A b x₀ rs₀ (m + 1) := by
  have hαm := h.alpha_ne_zero m le_rfl
  have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m h
  have hna : (0 : ℝ) < ‖tfqmrAlpha A b x₀ rs₀ m‖ := norm_pos_iff.2 hαm
  have hS : (0 : ℝ) < Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hSK : ((Real.sqrt (tfqmrTau A b x₀ rs₀ m ^ 2 + ‖tfqmrW A b x₀ rs₀ (m + 1)‖ ^ 2) : ℝ) : 𝕜)
      ≠ 0 := RCLike.ofReal_ne_zero.2 hS.ne'
  have hnaK : ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hna.ne'
  have hcα : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m)
      = ((‖tfqmrAlpha A b x₀ rs₀ m‖ : ℝ) : 𝕜) ^ 2 / tfqmrAlpha A b x₀ rs₀ m := by
    rw [eq_div_iff hαm, ← RCLike.mul_conj]
    ring
  rw [gvec_eq m h, tfqmr_succ_eta, tfqmrC_succ_eq m h, givensRho_eq m h, hcα]
  push_cast
  field_simp

/-- **(7.79)**: the entry rotation `m` puts above the diagonal of column `m+1` is
`-(θ_{m+1}²/α_{m+1}) g_m`, which is what makes the `d`-recurrence of Algorithm 7.8 the
back-substitution of Algorithm 6.13. -/
private theorem rotated_above_diag_eq (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ (m + 1)) :
    Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
      = -(((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1))
        * Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m := by
  have hαm := h.alpha_ne_zero m (by omega)
  have hαm' := h.alpha_ne_zero (m + 1) le_rfl
  have hcαm : starRingEnd 𝕜 (tfqmrAlpha A b x₀ rs₀ m) ≠ 0 := by simpa using hαm
  have ht : 0 < tfqmrTau A b x₀ rs₀ m := tfqmrTau_pos m (h.mono (Nat.le_succ m))
  have htK : ((tfqmrTau A b x₀ rs₀ m : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 ht.ne'
  have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) m : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.2 (givensRho_pos m (h.mono (Nat.le_succ m))).ne'
  rw [rotated_above_diag, Krylov.givensS, rotated_succ_col,
    gvec_eq m (h.mono (Nat.le_succ m)), tfqmr_succ_theta,
    tfqmrDelta]
  simp only [map_div₀, map_neg, RCLike.conj_ofReal]
  push_cast
  field_simp

/-- Algorithm 6.13 with `k = 1` never truncates anything here: column `m+1` of the triangular
factor has only the two entries `(m, m+1)` and `(m+1, m+1)`. -/
private theorem dqgmresP_zero_eq :
    Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 0
      = (Krylov.rotated (tfqmrH A b x₀ rs₀) 1 0 0)⁻¹ • tfqmrU A b x₀ rs₀ 0 := by
  rw [Chapter06.dqgmresP_eq]
  simp

private theorem dqgmresP_succ_eq (m : ℕ) :
    Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (m + 1)
      = (Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) (m + 1) (m + 1))⁻¹ •
        (tfqmrU A b x₀ rs₀ (m + 1)
          - Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1)
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m) := by
  have hz : ∑ i ∈ Finset.range m,
      (if m + 1 ≤ i + 1 then Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) i (m + 1) else 0)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      rw [ite_eq_right (by omega), zero_smul]
  rw [Chapter06.dqgmresP_eq, Finset.sum_range_succ, hz, zero_add, ite_eq_left (by omega)]

/-- **The hinge of §7.4.3**: Algorithm 7.8's update `η_{m+1} d_{m+1}` is the update `g_m p_m` of
Algorithm 6.13 with `k = 1`.  The two ingredients are `η_{m+1} = g_m/ρ_m` and the identification of
the above-diagonal entry with `-(θ_m²/α_m) g_{m-1}`. -/
private theorem tfqmr_eta_smul_d : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    tfqmrEta A b x₀ rs₀ (m + 1) • tfqmrD A b x₀ rs₀ (m + 1)
      = Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m := by
  intro m
  induction m with
  | zero =>
    intro h
    have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) 0 : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.2 (givensRho_pos 0 h).ne'
    have hd1 : tfqmrD A b x₀ rs₀ 1 = tfqmrU A b x₀ rs₀ 0 := by
      rw [tfqmr_succ_d, show tfqmrEta A b x₀ rs₀ 0 = 0 from rfl, mul_zero, zero_smul, add_zero]
    have hsc : Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) 0
        * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) 0 : ℝ) : 𝕜)⁻¹ = tfqmrEta A b x₀ rs₀ 1 := by
      rw [gvec_eq_givensRho_mul_eta 0 h]
      field_simp
    rw [hd1, dqgmresP_zero_eq, Krylov.rotated_succ_self, smul_smul, hsc]
  | succ m ih =>
    intro h
    have ihm := ih (h.mono (Nat.le_succ m))
    have hρK : ((Krylov.givensRho (tfqmrH A b x₀ rs₀) (m + 1) : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.2 (givensRho_pos (m + 1) h).ne'
    have hsc : Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (m + 1)
        * ((Krylov.givensRho (tfqmrH A b x₀ rs₀) (m + 1) : ℝ) : 𝕜)⁻¹
          = tfqmrEta A b x₀ rs₀ (m + 1 + 1) := by
      rw [gvec_eq_givensRho_mul_eta (m + 1) h]
      field_simp
    have hassoc : tfqmrEta A b x₀ rs₀ (m + 1 + 1)
        * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1)
          * tfqmrEta A b x₀ rs₀ (m + 1))
        = tfqmrEta A b x₀ rs₀ (m + 1 + 1)
            * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1))
          * tfqmrEta A b x₀ rs₀ (m + 1) := by
      ring
    have hkey : (tfqmrEta A b x₀ rs₀ (m + 1 + 1)
          * (((tfqmrTheta A b x₀ rs₀ (m + 1) ^ 2 : ℝ) : 𝕜) / tfqmrAlpha A b x₀ rs₀ (m + 1)
            * tfqmrEta A b x₀ rs₀ (m + 1))) • tfqmrD A b x₀ rs₀ (m + 1)
        = -(tfqmrEta A b x₀ rs₀ (m + 1 + 1)
            * Krylov.rotated (tfqmrH A b x₀ rs₀) (m + 1 + 1) m (m + 1))
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 m := by
      rw [hassoc, ← smul_smul, ihm, smul_smul, rotated_above_diag_eq m h]
      congr 1
      ring
    rw [tfqmr_succ_d, dqgmresP_succ_eq, Krylov.rotated_succ_self, smul_smul, hsc, smul_add,
      smul_sub, smul_smul, smul_smul, hkey, neg_smul, sub_eq_add_neg]

/-- **Algorithm 7.8 is Algorithm 6.13 with `k = 1`** on the bidiagonal `H̄_m` of (7.81): the
`θ, c, τ, η, d` recurrence is the DQGMRES back-substitution. -/
theorem tfqmr_eq_dqgmres : ∀ (m : ℕ), TFQMRNoBreakdown A b x₀ rs₀ m →
    (tfqmr A b x₀ rs₀ m).x
      = Chapter06.dqgmres x₀ (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
          (tfqmrDelta A b x₀ rs₀ 0) 1 m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [tfqmr_succ_x, ih (h.mono (Nat.le_succ m)), Chapter06.dqgmres,
      tfqmr_eta_smul_d m (h.mono (Nat.le_succ m))]

/-- Column `j` of the triangular factor is fixed once rotation `j` has been applied. -/
private theorem rotated_of_col_lt {j : ℕ} : ∀ M, j + 1 ≤ M → ∀ i,
    Krylov.rotated (tfqmrH A b x₀ rs₀) M i j
      = Krylov.rotated (tfqmrH A b x₀ rs₀) (j + 1) i j := by
  intro M
  induction M with
  | zero => intro hM; omega
  | succ M ih =>
    intro hM i
    rcases Nat.lt_or_ge j M with hjM | hjM
    · rw [Krylov.rotated_succ_eq_of_lt _
        (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij) M j hjM i]
      exact ih (by omega) i
    · have hMj : M = j := by omega
      subst hMj
      rfl

/-- `P_m R_m = U_m`: the truncated recurrence with `k = 1` is the full back-substitution for the
bidiagonal triangular factor. -/
private theorem sum_R_smul_dqgmresP {m : ℕ} (h : TFQMRNoBreakdown A b x₀ rs₀ m) (j : Fin m) :
    ∑ i : Fin m, Chapter06.R (tfqmrH A b x₀ rs₀) m i j
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ)
      = tfqmrU A b x₀ rs₀ (j : ℕ) := by
  have hhess : ∀ i j : ℕ, j + 1 < i → tfqmrH A b x₀ rs₀ i j = 0 :=
    fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij
  have hlow : ∀ i j : ℕ, i < j → tfqmrH A b x₀ rs₀ i j = 0 :=
    fun i j hij => tfqmrH_eq_zero_of_lt A b x₀ rs₀ hij
  have hjm : (j : ℕ) < m := j.isLt
  have hd : Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) (j : ℕ) (j : ℕ) ≠ 0 := by
    rw [Krylov.rotated_succ_self]
    exact RCLike.ofReal_ne_zero.2 (givensRho_pos (j : ℕ) (h.mono (le_of_lt j.isLt))).ne'
  have hzero : ∀ i ∈ Finset.range m, i ∉ Finset.range ((j : ℕ) + 1) →
      Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i = 0 := by
    intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Krylov.rotated_eq_zero_of_lt _ hhess ((j : ℕ) + 1) i (j : ℕ) (Nat.lt_succ_self _)
      (by omega), zero_smul]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range m := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  have hpj := Chapter06.dqgmresP_eq (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (j : ℕ)
  have hcond : ∀ i ∈ Finset.range (j : ℕ),
      (if (j : ℕ) ≤ i + 1 then Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ) else 0)
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i
        = Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
          • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hc : (j : ℕ) ≤ i + 1
    · rw [ite_eq_left hc]
    · rw [ite_eq_right hc, Krylov.rotated_eq_zero_of_succ_lt_col _ hlow ((j : ℕ) + 1) i (j : ℕ)
        (by omega), zero_smul]
  rw [Finset.sum_congr rfl fun i _ => by
      rw [Chapter06.R_apply, rotated_of_col_lt (j := (j : ℕ)) m (by omega) (i : ℕ)],
    Fin.sum_univ_eq_sum_range
      (fun i => Krylov.rotated (tfqmrH A b x₀ rs₀) ((j : ℕ) + 1) i (j : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 i) m,
    ← Finset.sum_subset hsub hzero, Finset.sum_range_succ, hpj, Finset.sum_congr rfl hcond,
    smul_smul, mul_inv_cancel₀ hd, one_smul]
  abel

/-- Algorithm 7.8 computes the QGMRES iterate of the relation (7.70): with `H̄_m` bidiagonal the
truncated Algorithm 6.13 loses nothing. -/
theorem tfqmr_eq_qgmres (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    (tfqmr A b x₀ rs₀ m).x
      = Chapter06.qgmres x₀ (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
          (tfqmrDelta A b x₀ rs₀ 0) m := by
  have hR : IsUnit (Chapter06.R (tfqmrH A b x₀ rs₀) m) :=
    Chapter06.isUnit_R _ (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
      fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne'
  rw [tfqmr_eq_dqgmres m h, Chapter06.dqgmres_eq_sum, Chapter06.qgmres,
    Chapter06.toEuclideanLin_colMatrix_apply]
  refine congrArg _ ?_
  have hg : ∀ i : Fin m, Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (i : ℕ)
      = (Chapter06.R (tfqmrH A b x₀ rs₀) m
        *ᵥ Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m) i := by
    intro i
    rw [Chapter06.qgmresY, Chapter06.mulVec_R_inv_mulVec_g _ _ hR, Chapter06.g_apply]
  calc ∑ i : Fin m, Krylov.gvec (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) (i : ℕ)
        • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ)
      = ∑ i : Fin m, ∑ j : Fin m,
          (Chapter06.R (tfqmrH A b x₀ rs₀) m i j
            * Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j)
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hg i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    _ = ∑ j : Fin m, Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j
          • ∑ i : Fin m, Chapter06.R (tfqmrH A b x₀ rs₀) m i j
            • Chapter06.dqgmresP (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀) 1 (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]
    _ = ∑ j : Fin m, Chapter06.qgmresY (tfqmrH A b x₀ rs₀) (tfqmrDelta A b x₀ rs₀ 0) m j
          • tfqmrU A b x₀ rs₀ (j : ℕ) :=
        Finset.sum_congr rfl fun j _ => by rw [sum_R_smul_dqgmresP h j]

/-- **Algorithm 7.8 computes the quasi-minimal-residual iterate of the relation (7.70)**: `x_m =
x_0 + U_m y` with `y` minimizing `‖δ_0 e_1 - H̄_m y‖₂`.  This is Algorithm 6.12 on the two-family
data of `equation_7_70`, reached through Algorithm 6.13 with `k = 1`. -/
theorem tfqmr_isQuasiMinResIterate (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m) :
    Krylov.IsQuasiMinResIterate (tfqmrU A b x₀ rs₀) (tfqmrH A b x₀ rs₀)
      (tfqmrDelta A b x₀ rs₀ 0) x₀ m (tfqmr A b x₀ rs₀ m).x := by
  rw [tfqmr_eq_qgmres m h]
  exact Chapter06.qgmres_isQuasiMinResIterate x₀ _ _ _
    (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
    (Chapter06.isUnit_R _ (fun i j hij => tfqmrH_eq_zero_of_succ_lt A b x₀ rs₀ hij)
      fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne')

/-- **(7.83)**: `‖b - A x_m‖₂ ≤ √(m+1) τ_m`.  The residual basis `R_{m+1} Δ_{m+1}⁻¹` has unit
columns, so the constant of `Krylov.IsQuasiMinResIterate.norm_residual_le` is `√(m+1)`, and the
quasi-residual is `‖γ_m‖ = τ_m`. -/
theorem equation_7_83 (m : ℕ) (h : TFQMRNoBreakdown A b x₀ rs₀ m)
    (hs : TFQMRNoSeriousBreakdown A b x₀ rs₀) :
    ‖b - op A (tfqmr A b x₀ rs₀ m).x‖
      ≤ Real.sqrt (m + 1) * tfqmrTau A b x₀ rs₀ m := by
  have hδ0 : ∀ i, tfqmrDelta A b x₀ rs₀ i = 0 → tfqmrW A b x₀ rs₀ i = 0 := by
    intro i hi
    rw [← norm_eq_zero, ← norm_tfqmrDelta, hi, norm_zero]
  have hrel := (equation_7_70 (δ := tfqmrDelta A b x₀ rs₀) hs hδ0).2
  have hunit : ∀ i, ‖(tfqmrDelta A b x₀ rs₀ i)⁻¹ • tfqmrW A b x₀ rs₀ i‖ ≤ 1 := by
    intro i
    rcases eq_or_ne (tfqmrW A b x₀ rs₀ i) 0 with h0 | h0
    · rw [h0, smul_zero, norm_zero]
      norm_num
    · rw [norm_smul, norm_inv, norm_tfqmrDelta, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  have hr : b - op A x₀
      = tfqmrDelta A b x₀ rs₀ 0 • (tfqmrDelta A b x₀ rs₀ 0)⁻¹ • tfqmrW A b x₀ rs₀ 0 := by
    rw [smul_smul, mul_inv_cancel₀ (h.delta_ne_zero (Nat.zero_le m)), one_smul]
    rfl
  have hle := Krylov.IsQuasiMinResIterate.norm_residual_le hrel hr
    (fun k hk => (givensRho_pos k (h.mono (le_of_lt hk))).ne')
    (fun w => Krylov.norm_sum_smul_le_sqrt_mul hunit w) (tfqmr_isQuasiMinResIterate m h)
  rw [norm_gamma_eq_tfqmrTau m h] at hle
  refine hle.trans_eq ?_
  norm_num

end TFQMR

end SaadSparse.Chapter07
