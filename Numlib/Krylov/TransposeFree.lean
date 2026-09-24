import Numlib.Krylov.BiLanczos
import Numlib.Projection.OneDimensional

/-!
# Transpose-free variants of the biconjugate gradient method

The conjugate gradient squared method (CGS, Sonneveld) and BiCGSTAB (van der Vorst), with the
polynomial identification that gives each its meaning ([saad2003iterative] §7.4, Algorithms
7.6–7.7, (7.32)–(7.54); [golub2013matrix] §11.4.5 and Figure 11.4.1, whose recurrences are line by
line the same).

As for `BCG` in `Numlib/Krylov/BiLanczos`, the operator is `A : E →ₗ[𝕜] E` on an inner product
space and its adjoint is a second operator `B` with `⟪A x, y⟫ = ⟪x, B y⟫`, taken as data.

## Main definitions

* `BCG.residualPoly`, `BCG.directionPoly`: the polynomials `φ_j`, `π_j` of a BCG run, defined by
  `φ_0 = π_0 = 1`, `φ_{j+1} = φ_j - α_j X π_j` and `π_{j+1} = φ_{j+1} + β_j π_j` from the run's own
  coefficients `BCG.alpha`, `BCG.beta`.
* `CGS.iterate`: Algorithm 7.6 in the `State`/`step`/`iterate` convention of the Krylov layer, with
  the coefficients `CGS.alpha`, `CGS.beta` and the auxiliary vector `CGS.q` read off the iterates.
  It applies `A` only.
* `BiCGSTAB.iterate`: Algorithm 7.7 likewise, with `BiCGSTAB.alpha`, `BiCGSTAB.s`, `BiCGSTAB.omega`,
  `BiCGSTAB.beta`, and the stabilizing polynomial `BiCGSTAB.stabPoly`, `ψ_{j+1} = (1 - ω_j X) ψ_j`.

## Main statements

* `BCG.residual_eq_aeval`: the four BCG sequences are `φ_j(A) r₀`, `π_j(A) r₀`, `φ̄_j(B) r*₀` and
  `π̄_j(B) r*₀`. Every scalar of the transpose-free methods is then computed by moving a polynomial
  across the inner product (`BiLanczos.inner_aeval_map_eq`).
* `CGS.residual_eq_aeval_sq`: the CGS vectors are `φ_j² r₀`, `π_j² r₀`, `φ_j π_j r₀` and
  `φ_{j+1} π_j r₀`, and the CGS coefficients are the BCG ones. No breakdown hypothesis is needed:
  the coefficients agree even where both are `0 / 0`.
* `BiCGSTAB.residual_eq`: `r_j = ψ_j(A) φ_j(A) r₀` and `p_j = ψ_j(A) π_j(A) r₀`, under
  `BCG.NoBreakdown` and `ω_i ≠ 0` — the two hypotheses the leading-coefficient argument behind
  the coefficient identities `BiCGSTAB.alpha_eq`, `BiCGSTAB.beta_eq` ([saad2003iterative]
  (7.53)–(7.54)) needs.
* `BiCGSTAB.iterate_succ_x_eq_minResStep`: the second half of a BiCGSTAB step is the
  one-dimensional minimal-residual step along `s_j` ([saad2003iterative] (7.55)).
* `CGS.r_eq_sub_apply_x`, `BiCGSTAB.r_eq_sub_apply_x`: the residual fields are true residuals.

Indices are `0`-based: `CGS.iterate A b x₀ rs₀ j` is the state after `j` steps and
`BCG.residualPoly A B b x₀ rs₀ j` is `φ_j`.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Polynomials in an operator, applied to a vector -/

section AevalHelpers

/-- `(p q)(T) v = p(T) (q(T) v)`. -/
private theorem aeval_mul_apply' (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p * q) v = aeval T p (aeval T q v) := by
  rw [map_mul]; rfl

/-- `p(T)` commutes with `T`. -/
private theorem aeval_apply_apply (T : E →ₗ[𝕜] E) (p : 𝕜[X]) (v : E) :
    aeval T p (T v) = T (aeval T p v) := by
  have hmul : aeval T (p * X) = aeval T (X * p) := by rw [mul_comm]
  have := congrArg (fun f : E →ₗ[𝕜] E => f v) hmul
  simpa only [map_mul, aeval_X, Module.End.mul_apply] using this

/-- Evaluation is additive in the polynomial. -/
private theorem aeval_apply_add (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p + q) v = aeval T p v + aeval T q v := by
  rw [map_add]; rfl

/-- Evaluation is subtractive in the polynomial. -/
private theorem aeval_apply_sub (T : E →ₗ[𝕜] E) (p q : 𝕜[X]) (v : E) :
    aeval T (p - q) v = aeval T p v - aeval T q v := by
  rw [map_sub]; rfl

/-- A constant factor becomes a scalar. -/
private theorem aeval_apply_C_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p : 𝕜[X]) (v : E) :
    aeval T (C c * p) v = c • aeval T p v := by
  rw [map_mul, aeval_C]
  simp [Module.End.mul_apply, Module.algebraMap_end_apply]

/-- A factor of `X` becomes an application of `T`. -/
private theorem aeval_apply_X_mul (T : E →ₗ[𝕜] E) (p : 𝕜[X]) (v : E) :
    aeval T (X * p) v = T (aeval T p v) := by
  rw [aeval_mul_apply', aeval_X]

/-- The evaluation of `p - c X q`. -/
private theorem aeval_sub_C_mul_X_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p q : 𝕜[X]) (v : E) :
    aeval T (p - C c * (X * q)) v = aeval T p v - c • T (aeval T q v) := by
  rw [aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- The evaluation of `p + c q`. -/
private theorem aeval_add_C_mul (T : E →ₗ[𝕜] E) (c : 𝕜) (p q : 𝕜[X]) (v : E) :
    aeval T (p + C c * q) v = aeval T p v + c • aeval T q v := by
  rw [aeval_apply_add, aeval_apply_C_mul]

/-- **The step that removes the transpose**: with `B` the adjoint of `A`, a bilinear expression in
`p(A) v` and `q̄(B) w` is one in `(q p)(A) v` and `w`. -/
private theorem inner_aeval_map_aeval {A B : E →ₗ[𝕜] E}
    (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (p q : 𝕜[X]) (v w : E) :
    inner 𝕜 (aeval B (q.map (starRingEnd 𝕜)) w) (aeval A p v) = inner 𝕜 w (aeval A (q * p) v) := by
  rw [BiLanczos.inner_aeval_map_eq hB q, aeval_mul_apply']

end AevalHelpers

/-! ### The BCG residual and direction polynomials -/

namespace BCG

/-- The pair `(φ_j, π_j)`, defined together because each recurrence feeds the other. -/
private noncomputable def polyPair (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 => (1, 1)
  | j + 1 =>
      let φ : 𝕜[X] :=
        (polyPair A B b x₀ rs₀ j).1 - C (alpha A B b x₀ rs₀ j) * (X * (polyPair A B b x₀ rs₀ j).2)
      (φ, φ + C (beta A B b x₀ rs₀ j) * (polyPair A B b x₀ rs₀ j).2)

variable (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The **BCG residual polynomial** `φ_j` ([saad2003iterative] (7.32), (7.35);
[golub2013matrix] (11.4.14)): `φ_0 = 1` and `φ_{j+1} = φ_j - α_j X π_j` for the coefficients of
the BCG run itself. It has degree at most `j` and `φ_j(0) = 1`, and `r_j = φ_j(A) r₀`
(`BCG.residual_eq_aeval`). -/
noncomputable def residualPoly (j : ℕ) : 𝕜[X] := (polyPair A B b x₀ rs₀ j).1

/-- The **BCG direction polynomial** `π_j` ([saad2003iterative] (7.33), (7.36);
[golub2013matrix] (11.4.14)): `π_0 = 1` and `π_{j+1} = φ_{j+1} + β_j π_j`, so that
`p_j = π_j(A) r₀`. Its value at `0` is not `1` in general. -/
noncomputable def directionPoly (j : ℕ) : 𝕜[X] := (polyPair A B b x₀ rs₀ j).2

@[simp] theorem residualPoly_zero : residualPoly A B b x₀ rs₀ 0 = 1 := rfl

@[simp] theorem directionPoly_zero : directionPoly A B b x₀ rs₀ 0 = 1 := rfl

/-- `φ_{j+1} = φ_j - α_j X π_j`. -/
theorem residualPoly_succ (j : ℕ) : residualPoly A B b x₀ rs₀ (j + 1) =
    residualPoly A B b x₀ rs₀ j
      - C (alpha A B b x₀ rs₀ j) * (X * directionPoly A B b x₀ rs₀ j) := rfl

/-- `π_{j+1} = φ_{j+1} + β_j π_j`. -/
theorem directionPoly_succ (j : ℕ) : directionPoly A B b x₀ rs₀ (j + 1) =
    residualPoly A B b x₀ rs₀ (j + 1)
      + C (beta A B b x₀ rs₀ j) * directionPoly A B b x₀ rs₀ j := rfl

/-- The residual polynomials are *consistent*: `φ_j(0) = 1`. -/
@[simp] theorem residualPoly_eval_zero (j : ℕ) : (residualPoly A B b x₀ rs₀ j).eval 0 = 1 := by
  induction j with
  | zero => simp
  | succ j ih => rw [residualPoly_succ]; simp [ih]

private theorem natDegree_polyPair_le (j : ℕ) :
    (residualPoly A B b x₀ rs₀ j).natDegree ≤ j ∧ (directionPoly A B b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hφ : (residualPoly A B b x₀ rs₀ (j + 1)).natDegree ≤ j + 1 := by
      rw [residualPoly_succ]
      refine (natDegree_sub_le _ _).trans (max_le (ih.1.trans (Nat.le_succ j)) ?_)
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      have := ih.2
      simp only [natDegree_X]
      omega
    refine ⟨hφ, ?_⟩
    rw [directionPoly_succ]
    exact (natDegree_add_le _ _).trans
      (max_le hφ ((natDegree_C_mul_le _ _).trans (ih.2.trans (Nat.le_succ j))))

/-- `deg φ_j ≤ j`. -/
theorem residualPoly_natDegree_le (j : ℕ) : (residualPoly A B b x₀ rs₀ j).natDegree ≤ j :=
  (natDegree_polyPair_le A B b x₀ rs₀ j).1

/-- `deg π_j ≤ j`. -/
theorem directionPoly_natDegree_le (j : ℕ) : (directionPoly A B b x₀ rs₀ j).natDegree ≤ j :=
  (natDegree_polyPair_le A B b x₀ rs₀ j).2

/-- `φ_j` and `π_j` have the same coefficient of `X^j`: `π_{j+1}` differs from `φ_{j+1}` by a
multiple of the lower-degree `π_j`. -/
theorem directionPoly_coeff_self (j : ℕ) :
    (directionPoly A B b x₀ rs₀ j).coeff j = (residualPoly A B b x₀ rs₀ j).coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [directionPoly_succ, coeff_add, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (directionPoly_natDegree_le A B b x₀ rs₀ j) (Nat.lt_succ_self j)),
      mul_zero, add_zero]

/-- The coefficients of `X^j` obey `γ^{(j+1)} = -α_j γ^{(j)}`. -/
theorem residualPoly_coeff_succ (j : ℕ) :
    (residualPoly A B b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -alpha A B b x₀ rs₀ j * (residualPoly A B b x₀ rs₀ j).coeff j := by
  rw [residualPoly_succ, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (residualPoly_natDegree_le A B b x₀ rs₀ j) (Nat.lt_succ_self j)),
    ← mul_assoc, mul_comm (C (alpha A B b x₀ rs₀ j)) X, mul_assoc, coeff_X_mul, coeff_C_mul,
    directionPoly_coeff_self]
  ring

/-- **The BCG sequences are polynomials in the operators** ([saad2003iterative] (7.32)–(7.33);
[golub2013matrix] (11.4.14)): `r_j = φ_j(A) r₀`, `p_j = π_j(A) r₀`, and the shadow sequences are
the *conjugate* polynomials in `B` applied to `r*₀`, `r*_j = φ̄_j(B) r*₀`, `p*_j = π̄_j(B) r*₀`.
No hypothesis is needed. -/
theorem residual_eq_aeval (j : ℕ) :
    residual A B b x₀ rs₀ j = aeval A (residualPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      direction A B b x₀ rs₀ j = aeval A (directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      dualResidual A B b x₀ rs₀ j =
        aeval B ((residualPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ ∧
      dualDirection A B b x₀ rs₀ j =
        aeval B ((directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) rs₀ := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hrs, hps⟩ := ih
    have hrmap : (residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
        = (residualPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)
          - C (starRingEnd 𝕜 (alpha A B b x₀ rs₀ j))
            * (X * (directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜)) := by
      rw [residualPoly_succ]
      simp [Polynomial.map_sub, Polynomial.map_mul]
    have hpmap : (directionPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
        = (residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)
          + C (starRingEnd 𝕜 (beta A B b x₀ rs₀ j))
            * (directionPoly A B b x₀ rs₀ j).map (starRingEnd 𝕜) := by
      rw [directionPoly_succ]
      simp [Polynomial.map_add, Polynomial.map_mul]
    have h1 : residual A B b x₀ rs₀ (j + 1)
        = aeval A (residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      rw [residual_succ, residualPoly_succ, aeval_sub_C_mul_X_mul, hr, hp]
    have h3 : dualResidual A B b x₀ rs₀ (j + 1)
        = aeval B ((residualPoly A B b x₀ rs₀ (j + 1)).map (starRingEnd 𝕜)) rs₀ := by
      rw [dualResidual_succ, hrmap, aeval_sub_C_mul_X_mul, hrs, hps]
    exact ⟨h1, by rw [direction_succ, directionPoly_succ, aeval_add_C_mul, h1, hp], h3,
      by rw [dualDirection_succ, hpmap, aeval_add_C_mul, h3, hps]⟩

end BCG

/-! ### Conjugate gradient squared -/

namespace CGS

/-- The state `(x_j, r_j, u_j, p_j)` of the conjugate gradient squared method; the auxiliary
`q_j` is read off it by `CGS.q`. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate `x_j`. -/
  x : E
  /-- The residual `r_j`, which is `φ_j²(A) r₀`. -/
  r : E
  /-- The auxiliary vector `u_j = r_j + β_{j-1} q_{j-1}`, which is `φ_j(A) π_j(A) r₀`. -/
  u : E
  /-- The direction `p_j`, which is `π_j²(A) r₀`. -/
  p : E

/-- One step of the **conjugate gradient squared** method ([saad2003iterative] Algorithm 7.6,
lines 4–10; [golub2013matrix] Figure 11.4.1): `α = ⟪r*₀, r⟫/⟪r*₀, A p⟫`, `q = u - α A p`,
`x' = x + α (u + q)`, `r' = r - α A (u + q)`, `β = ⟪r*₀, r'⟫/⟪r*₀, r⟫`, `u' = r' + β q` and
`p' = u' + β (q + β p)`. -/
noncomputable def step (A : E →ₗ[𝕜] E) (rs₀ : E) (s : State E) : State E :=
  let α : 𝕜 := inner 𝕜 rs₀ s.r / inner 𝕜 rs₀ (A s.p)
  let q : E := s.u - α • A s.p
  let r : E := s.r - α • A (s.u + q)
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ s.r
  let u : E := r + β • q
  { x := s.x + α • (s.u + q), r := r, u := u, p := u + β • (q + β • s.p) }

/-- The **conjugate gradient squared** method ([saad2003iterative] Algorithm 7.6;
[golub2013matrix] Figure 11.4.1) run for `k` steps from `x₀`, with an arbitrary shadow residual
`rs₀`, started from `r₀ = u₀ = p₀ = b - A x₀`. Only `A` is applied. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A rs₀)^[k] { x := x₀, r := b - A x₀, u := b - A x₀, p := b - A x₀ }

variable (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The CGS step length `α_j = ⟪r*₀, r_j⟫/⟪r*₀, A p_j⟫`. -/
noncomputable def alpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r / inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)

/-- The CGS coefficient `β_j = ⟪r*₀, r_{j+1}⟫/⟪r*₀, r_j⟫`. -/
noncomputable def beta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r

/-- The auxiliary CGS vector `q_j = u_j - α_j A p_j`. -/
noncomputable def q (j : ℕ) : E :=
  (iterate A b x₀ rs₀ j).u - alpha A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p

@[simp] theorem iterate_zero :
    iterate A b x₀ rs₀ 0 = { x := x₀, r := b - A x₀, u := b - A x₀, p := b - A x₀ } := rfl

/-- The recurrence: state `k + 1` is one `CGS.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ rs₀ (k + 1) = step A rs₀ (iterate A b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- `x_{j+1} = x_j + α_j (u_j + q_j)`. -/
theorem iterate_succ_x (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).x =
    (iterate A b x₀ rs₀ j).x
      + alpha A b x₀ rs₀ j • ((iterate A b x₀ rs₀ j).u + q A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- `r_{j+1} = r_j - α_j A (u_j + q_j)`. -/
theorem iterate_succ_r (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).r =
    (iterate A b x₀ rs₀ j).r
      - alpha A b x₀ rs₀ j • A ((iterate A b x₀ rs₀ j).u + q A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- `u_{j+1} = r_{j+1} + β_j q_j`. -/
theorem iterate_succ_u (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).u =
    (iterate A b x₀ rs₀ (j + 1)).r + beta A b x₀ rs₀ j • q A b x₀ rs₀ j := by
  simp only [beta, iterate_succ]; rfl

/-- `p_{j+1} = u_{j+1} + β_j (q_j + β_j p_j)`. -/
theorem iterate_succ_p (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).p =
    (iterate A b x₀ rs₀ (j + 1)).u
      + beta A b x₀ rs₀ j • (q A b x₀ rs₀ j + beta A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p) := by
  simp only [beta, iterate_succ]; rfl

/-- The CGS residual is the true residual of the CGS iterate. -/
theorem r_eq_sub_apply_x (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = b - A (iterate A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [iterate_succ_r, iterate_succ_x, ih, map_add, map_smul]
    abel

variable {A b x₀ rs₀}

section Polynomial

variable {B : E →ₗ[𝕜] E} (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y))
include hB

/-- The numerator of the BCG `α_j`: `⟪r*_j, r_j⟫ = ⟪r*₀, φ_j²(A) r₀⟫`. -/
private theorem inner_dualResidual_residual_eq {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    inner 𝕜 (BCG.dualResidual A B b x₀ rs₀ j) (BCG.residual A B b x₀ rs₀ j)
      = inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r := by
  obtain ⟨hbr, -, hbrs, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbr, hbrs, inner_aeval_map_aeval hB, hr, ← sq]

/-- The denominator of the BCG `α_j`: `⟪p*_j, A p_j⟫ = ⟪r*₀, A π_j²(A) r₀⟫`. -/
private theorem inner_dualDirection_apply_direction_eq {j : ℕ}
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    inner 𝕜 (BCG.dualDirection A B b x₀ rs₀ j) (A (BCG.direction A B b x₀ rs₀ j))
      = inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p) := by
  obtain ⟨-, hbp, -, hbps⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  have hpoly : BCG.directionPoly A B b x₀ rs₀ j * (X * BCG.directionPoly A B b x₀ rs₀ j)
      = X * BCG.directionPoly A B b x₀ rs₀ j ^ 2 := by ring
  rw [hbp, hbps, ← aeval_apply_X_mul, inner_aeval_map_aeval hB, hpoly, hp, aeval_apply_X_mul]

private theorem alpha_eq_aux {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀)) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  rw [alpha, BCG.alpha, inner_dualResidual_residual_eq hB hr,
    inner_dualDirection_apply_direction_eq hB hp]

private theorem beta_eq_aux {j : ℕ}
    (hr : (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hr' : (iterate A b x₀ rs₀ (j + 1)).r
      = aeval A (BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2) (b - A x₀)) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  rw [beta, BCG.beta, inner_dualResidual_residual_eq hB hr, inner_dualResidual_residual_eq hB hr']

omit hB in
private theorem q_eq_aux {j : ℕ}
    (hp : (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀))
    (hu : (iterate A b x₀ rs₀ j).u = aeval A
      (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀))
    (hα : alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j) :
    q A b x₀ rs₀ j = aeval A
      (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j
      = BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
        - C (BCG.alpha A B b x₀ rs₀ j) * (X * BCG.directionPoly A B b x₀ rs₀ j ^ 2) := by
    rw [BCG.residualPoly_succ]; ring
  rw [q, hu, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]

/-- The three CGS vectors are the squared BCG polynomials evaluated at `A` on `r₀`: the heart of
the induction behind `CGS.residual_eq_aeval_sq`. -/
private theorem vec_eq (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hr, hp, hu⟩ := ih
    have hα := alpha_eq_aux hB hr hp
    have hq := q_eq_aux hp hu hα
    have hr' : (iterate A b x₀ rs₀ (j + 1)).r
        = aeval A (BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2) (b - A x₀) := by
      have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2
          = BCG.residualPoly A B b x₀ rs₀ j ^ 2
            - C (BCG.alpha A B b x₀ rs₀ j)
              * (X * (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
                  + BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j)) := by
        rw [BCG.residualPoly_succ]; ring
      rw [iterate_succ_r, hu, hq, hr, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul,
        aeval_apply_X_mul, aeval_apply_add]
    have hβ := beta_eq_aux hB hr hr'
    have hu' : (iterate A b x₀ rs₀ (j + 1)).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1))
          (b - A x₀) := by
      have hpoly : BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
          = BCG.residualPoly A B b x₀ rs₀ (j + 1) ^ 2
            + C (BCG.beta A B b x₀ rs₀ j)
              * (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) := by
        rw [BCG.directionPoly_succ A B b x₀ rs₀ j]; ring
      rw [iterate_succ_u, hq, hr', hβ, hpoly, aeval_apply_add, aeval_apply_C_mul]
    refine ⟨hr', ?_, hu'⟩
    have hpoly : BCG.directionPoly A B b x₀ rs₀ (j + 1) ^ 2
        = BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
          + C (BCG.beta A B b x₀ rs₀ j)
            * (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j
              + C (BCG.beta A B b x₀ rs₀ j) * BCG.directionPoly A B b x₀ rs₀ j ^ 2) := by
      rw [BCG.directionPoly_succ A B b x₀ rs₀ j]; ring
    rw [iterate_succ_p, hu', hq, hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul,
      aeval_apply_add, aeval_apply_C_mul]

/-- **CGS computes the squared BCG polynomials** ([saad2003iterative] (7.40)–(7.45), Sonneveld;
[golub2013matrix] §11.4.5): with `B` the adjoint of `A`, `φ_j`, `π_j` the BCG polynomials of the
*same* run and `r₀ = b - A x₀`, the CGS vectors are `r_j = φ_j²(A) r₀`, `p_j = π_j²(A) r₀`,
`u_j = φ_j(A) π_j(A) r₀` and `q_j = φ_{j+1}(A) π_j(A) r₀`, and the CGS coefficients are the BCG
ones. No breakdown hypothesis is needed: the coefficients agree even where both are `0 / 0`. -/
theorem residual_eq_aeval_sq (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = aeval A (BCG.residualPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p = aeval A (BCG.directionPoly A B b x₀ rs₀ j ^ 2) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).u = aeval A
        (BCG.residualPoly A B b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      q A b x₀ rs₀ j = aeval A
        (BCG.residualPoly A B b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j ∧
      beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hr, hp, hu⟩ := vec_eq hB j
  have hα := alpha_eq_aux hB hr hp
  exact ⟨hr, hp, hu, q_eq_aux hp hu hα, hα, beta_eq_aux hB hr (vec_eq hB (j + 1)).1⟩

end Polynomial

end CGS

/-! ### BiCGSTAB -/

namespace BiCGSTAB

/-- The state `(x_j, r_j, p_j)` of BiCGSTAB; the half-step residual `s_j` is read off it by
`BiCGSTAB.s`. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate `x_j`. -/
  x : E
  /-- The residual `r_j`, which is `ψ_j(A) φ_j(A) r₀`. -/
  r : E
  /-- The direction `p_j`, which is `ψ_j(A) π_j(A) r₀`. -/
  p : E

/-- One step of **BiCGSTAB** ([saad2003iterative] Algorithm 7.7, lines 4–10; [golub2013matrix]
Figure 11.4.1): `α = ⟪r*₀, r⟫/⟪r*₀, A p⟫`, `s = r - α A p`, `ω = ⟪A s, s⟫/⟪A s, A s⟫`,
`x' = x + α p + ω s`, `r' = s - ω A s`, `β = (⟪r*₀, r'⟫/⟪r*₀, r⟫)(α/ω)` and
`p' = r' + β (p - ω A p)`. -/
noncomputable def step (A : E →ₗ[𝕜] E) (rs₀ : E) (st : State E) : State E :=
  let α : 𝕜 := inner 𝕜 rs₀ st.r / inner 𝕜 rs₀ (A st.p)
  let s : E := st.r - α • A st.p
  let ω : 𝕜 := inner 𝕜 (A s) s / inner 𝕜 (A s) (A s)
  let r : E := s - ω • A s
  let β : 𝕜 := inner 𝕜 rs₀ r / inner 𝕜 rs₀ st.r * (α / ω)
  { x := st.x + α • st.p + ω • s, r := r, p := r + β • (st.p - ω • A st.p) }

/-- **BiCGSTAB** ([saad2003iterative] Algorithm 7.7; [golub2013matrix] Figure 11.4.1) run for `k`
steps from `x₀`, with an arbitrary shadow residual `rs₀`, started from `r₀ = p₀ = b - A x₀`. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A rs₀)^[k] { x := x₀, r := b - A x₀, p := b - A x₀ }

variable (A : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The BiCGSTAB step length `α_j = ⟪r*₀, r_j⟫/⟪r*₀, A p_j⟫`. -/
noncomputable def alpha (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r / inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)

/-- The half-step residual `s_j = r_j - α_j A p_j`. -/
noncomputable def s (j : ℕ) : E :=
  (iterate A b x₀ rs₀ j).r - alpha A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p

/-- The stabilizing step `ω_j = ⟪A s_j, s_j⟫/⟪A s_j, A s_j⟫`. -/
noncomputable def omega (j : ℕ) : 𝕜 :=
  inner 𝕜 (A (s A b x₀ rs₀ j)) (s A b x₀ rs₀ j) /
    inner 𝕜 (A (s A b x₀ rs₀ j)) (A (s A b x₀ rs₀ j))

/-- The BiCGSTAB coefficient `β_j = (⟪r*₀, r_{j+1}⟫/⟪r*₀, r_j⟫)(α_j/ω_j)`. -/
noncomputable def beta (j : ℕ) : 𝕜 :=
  inner 𝕜 rs₀ (iterate A b x₀ rs₀ (j + 1)).r / inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r
    * (alpha A b x₀ rs₀ j / omega A b x₀ rs₀ j)

@[simp] theorem iterate_zero :
    iterate A b x₀ rs₀ 0 = { x := x₀, r := b - A x₀, p := b - A x₀ } := rfl

/-- The recurrence: state `k + 1` is one `BiCGSTAB.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A b x₀ rs₀ (k + 1) = step A rs₀ (iterate A b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- `x_{j+1} = x_j + α_j p_j + ω_j s_j`. -/
theorem iterate_succ_x (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).x =
    (iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p
      + omega A b x₀ rs₀ j • s A b x₀ rs₀ j := by
  rw [iterate_succ]; rfl

/-- `r_{j+1} = s_j - ω_j A s_j`. -/
theorem iterate_succ_r (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).r =
    s A b x₀ rs₀ j - omega A b x₀ rs₀ j • A (s A b x₀ rs₀ j) := by
  rw [iterate_succ]; rfl

/-- `p_{j+1} = r_{j+1} + β_j (p_j - ω_j A p_j)`. -/
theorem iterate_succ_p (j : ℕ) : (iterate A b x₀ rs₀ (j + 1)).p =
    (iterate A b x₀ rs₀ (j + 1)).r + beta A b x₀ rs₀ j •
      ((iterate A b x₀ rs₀ j).p - omega A b x₀ rs₀ j • A (iterate A b x₀ rs₀ j).p) := by
  simp only [beta, iterate_succ]; rfl

/-- The BiCGSTAB residual is the true residual of the BiCGSTAB iterate. -/
theorem r_eq_sub_apply_x (j : ℕ) :
    (iterate A b x₀ rs₀ j).r = b - A (iterate A b x₀ rs₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iterate_succ_r, iterate_succ_x, s, ih, map_add, map_add, map_smul, map_smul]
    abel

/-- **The stabilizing half-step is a minimal-residual step** ([saad2003iterative] (7.55)): the
residual of the half-step iterate `x_j + α_j p_j` is `s_j`, and `x_{j+1}` is the one-dimensional
minimal-residual step `Projection.minResStep` from it, which minimizes `‖(1 - ω A) s_j‖` over
`ω`. -/
theorem iterate_succ_x_eq_minResStep (j : ℕ) :
    (iterate A b x₀ rs₀ (j + 1)).x = Projection.minResStep A b
      ((iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p) := by
  have hres : b - A ((iterate A b x₀ rs₀ j).x + alpha A b x₀ rs₀ j • (iterate A b x₀ rs₀ j).p)
      = s A b x₀ rs₀ j := by
    rw [s, r_eq_sub_apply_x, map_add, map_smul]
    abel
  rw [Projection.minResStep, Projection.step1, hres, iterate_succ_x]
  rfl

/-- The **stabilizing polynomial** `ψ_j` of BiCGSTAB ([saad2003iterative] (7.47)): `ψ_0 = 1` and
`ψ_{j+1} = (1 - ω_j X) ψ_j` for the `ω_j` the method computes. -/
noncomputable def stabPoly : ℕ → 𝕜[X]
  | 0 => 1
  | j + 1 => (1 - C (omega A b x₀ rs₀ j) * X) * stabPoly j

@[simp] theorem stabPoly_zero : stabPoly A b x₀ rs₀ 0 = 1 := rfl

/-- `ψ_{j+1} = (1 - ω_j X) ψ_j`. -/
theorem stabPoly_succ (j : ℕ) : stabPoly A b x₀ rs₀ (j + 1) =
    (1 - C (omega A b x₀ rs₀ j) * X) * stabPoly A b x₀ rs₀ j := rfl

private theorem stabPoly_succ_eq_sub (j : ℕ) : stabPoly A b x₀ rs₀ (j + 1) =
    stabPoly A b x₀ rs₀ j - C (omega A b x₀ rs₀ j) * (X * stabPoly A b x₀ rs₀ j) := by
  rw [stabPoly_succ]; ring

/-- `deg ψ_j ≤ j`. -/
theorem stabPoly_natDegree_le (j : ℕ) : (stabPoly A b x₀ rs₀ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [stabPoly_succ_eq_sub]
    refine (natDegree_sub_le _ _).trans (max_le (ih.trans (Nat.le_succ j)) ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    simp only [natDegree_X]
    omega

/-- The coefficients of `X^j` obey `η^{(j+1)} = -ω_j η^{(j)}`. -/
theorem stabPoly_coeff_succ (j : ℕ) :
    (stabPoly A b x₀ rs₀ (j + 1)).coeff (j + 1) =
      -omega A b x₀ rs₀ j * (stabPoly A b x₀ rs₀ j).coeff j := by
  rw [stabPoly_succ_eq_sub, coeff_sub,
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (stabPoly_natDegree_le A b x₀ rs₀ j) (Nat.lt_succ_self j)),
    coeff_C_mul, coeff_X_mul]
  ring

/-- The coefficient of `X^j` in `ψ_j` is `∏_{i<j} (-ω_i)`, nonzero while no `ω_i` vanishes. -/
theorem stabPoly_coeff_ne_zero {j : ℕ} (hω : ∀ i < j, omega A b x₀ rs₀ i ≠ 0) :
    (stabPoly A b x₀ rs₀ j).coeff j ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [stabPoly_coeff_succ]
    exact mul_ne_zero (neg_ne_zero.2 (hω j (Nat.lt_succ_self j)))
      (ih fun i hi => hω i (by omega))

variable {A b x₀ rs₀}

section Polynomial

variable {B : E →ₗ[𝕜] E}

omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in
/-- `a b / (a c) = b / c` for `a ≠ 0`. -/
private theorem mul_div_mul_left_cancel {a b c : 𝕜} (ha : a ≠ 0) : a * b / (a * c) = b / c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [div_eq_div_iff (mul_ne_zero ha hc) hc]
    ring

/-- **Only the leading coefficient survives**: for `deg q ≤ j` and `v` orthogonal to
`𝒦_j(B, r*₀)`, `⟪r*₀, q(A) v⟫ = q_j ⟪B^j r*₀, v⟫`. -/
private theorem inner_aeval_eq_coeff_mul (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y))
    {j : ℕ} {p : 𝕜[X]} (hp : p.natDegree ≤ j) {v : E}
    (hv : ∀ u ∈ Krylov.subspace B rs₀ j, inner 𝕜 u v = 0) :
    inner 𝕜 rs₀ (aeval A p v) = p.coeff j * inner 𝕜 ((B ^ j) rs₀) v := by
  have hz : ∀ i < j, inner 𝕜 rs₀ ((A ^ i) v) = 0 := by
    intro i hi
    rw [← BiLanczos.inner_pow_apply_eq hB i rs₀ v]
    exact hv _ (Krylov.pow_apply_mem_subspace B rs₀ hi)
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hp) A, LinearMap.sum_apply, inner_sum,
    Finset.sum_eq_single j]
  · rw [LinearMap.smul_apply, inner_smul_right, BiLanczos.inner_pow_apply_eq hB j rs₀ v]
  · intro i hi hij
    rw [Finset.mem_range] at hi
    rw [LinearMap.smul_apply, inner_smul_right, hz i (by omega), mul_zero]
  · intro hc
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hc

variable {m : ℕ} (h : BCG.NoBreakdown A B b x₀ rs₀ m)
include h

/-- `⟪r*_j, r_j⟫ = γ^{(j)} ⟪B^j r*₀, r_j⟫` for the BCG sequences. -/
private theorem inner_dualResidual_residual {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (BCG.dualResidual A B b x₀ rs₀ j) (BCG.residual A B b x₀ rs₀ j)
      = (BCG.residualPoly A B b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) := by
  obtain ⟨-, -, hbrs, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbrs, BiLanczos.inner_aeval_map_eq h.adjoint]
  exact inner_aeval_eq_coeff_mul h.adjoint (BCG.residualPoly_natDegree_le A B b x₀ rs₀ j)
    fun u hu => BCG.inner_residual_eq_zero_of_mem_subspace (h.mono hj) hu

/-- `⟪p*_j, A p_j⟫ = γ^{(j)} ⟪B^j r*₀, A p_j⟫`: `π_j` and `φ_j` have the same leading
coefficient. -/
private theorem inner_dualDirection_apply_direction {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (BCG.dualDirection A B b x₀ rs₀ j) (A (BCG.direction A B b x₀ rs₀ j))
      = (BCG.residualPoly A B b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (A (BCG.direction A B b x₀ rs₀ j)) := by
  obtain ⟨-, -, -, hbps⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hbps, BiLanczos.inner_aeval_map_eq h.adjoint, ← BCG.directionPoly_coeff_self A B b x₀ rs₀ j]
  exact inner_aeval_eq_coeff_mul h.adjoint (BCG.directionPoly_natDegree_le A B b x₀ rs₀ j)
    fun u hu => BCG.inner_apply_direction_eq_zero_of_mem_subspace (h.mono hj) hu

/-- `⟪r*₀, r_j⟫ = η^{(j)} ⟪B^j r*₀, r^{BCG}_j⟫`, once `r_j = ψ_j(A) φ_j(A) r₀`. -/
private theorem inner_residual {j : ℕ} (hj : j ≤ m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀)) :
    inner 𝕜 rs₀ (iterate A b x₀ rs₀ j).r
      = (stabPoly A b x₀ rs₀ j).coeff j * inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) := by
  obtain ⟨hbr, -, -, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hr, aeval_mul_apply', ← hbr]
  exact inner_aeval_eq_coeff_mul h.adjoint (stabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => BCG.inner_residual_eq_zero_of_mem_subspace (h.mono hj) hu

/-- `⟪r*₀, A p_j⟫ = η^{(j)} ⟪B^j r*₀, A p^{BCG}_j⟫`, once `p_j = ψ_j(A) π_j(A) r₀`. -/
private theorem inner_apply_direction {j : ℕ} (hj : j ≤ m)
    (hp : (iterate A b x₀ rs₀ j).p
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀)) :
    inner 𝕜 rs₀ (A (iterate A b x₀ rs₀ j).p)
      = (stabPoly A b x₀ rs₀ j).coeff j
        * inner 𝕜 ((B ^ j) rs₀) (A (BCG.direction A B b x₀ rs₀ j)) := by
  obtain ⟨-, hbp, -, -⟩ := BCG.residual_eq_aeval A B b x₀ rs₀ j
  rw [hp, aeval_mul_apply', ← aeval_apply_apply, ← hbp]
  exact inner_aeval_eq_coeff_mul h.adjoint (stabPoly_natDegree_le A b x₀ rs₀ j)
    fun u hu => BCG.inner_apply_direction_eq_zero_of_mem_subspace (h.mono hj) hu

/-- Without breakdown the leading coefficient `γ^{(j)}` of `φ_j` and the pairing
`⟪B^j r*₀, r_j⟫` are both nonzero. -/
private theorem coeff_ne_zero_and {j : ℕ} (hj : j < m) :
    (BCG.residualPoly A B b x₀ rs₀ j).coeff j ≠ 0 ∧
      inner 𝕜 ((B ^ j) rs₀) (BCG.residual A B b x₀ rs₀ j) ≠ 0 := by
  have h0 := h.inner_residual_ne_zero j hj
  rw [inner_dualResidual_residual h hj.le] at h0
  exact ⟨left_ne_zero_of_mul h0, right_ne_zero_of_mul h0⟩

private theorem alpha_eq_aux (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀))
    (hp : (iterate A b x₀ rs₀ j).p
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀)) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  have he := stabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  rw [alpha, BCG.alpha, inner_residual h hj.le hr, inner_apply_direction h hj.le hp,
    inner_dualResidual_residual h hj.le, inner_dualDirection_apply_direction h hj.le,
    mul_div_mul_left_cancel he, mul_div_mul_left_cancel (coeff_ne_zero_and h hj).1]

private theorem beta_eq_aux (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m)
    (hr : (iterate A b x₀ rs₀ j).r
      = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀))
    (hr' : (iterate A b x₀ rs₀ (j + 1)).r
      = aeval A (stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀))
    (hα : alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hg, hL⟩ := coeff_ne_zero_and h hj
  have he := stabPoly_coeff_ne_zero A b x₀ rs₀ (j := j) fun i hi => hω i (by omega)
  have hωj := hω j hj
  rw [beta, BCG.beta, inner_residual h hj.le hr, inner_residual h hj hr',
    inner_dualResidual_residual h hj.le, inner_dualResidual_residual h hj,
    BCG.residualPoly_coeff_succ, stabPoly_coeff_succ, hα]
  field_simp

/-- The induction behind `BiCGSTAB.residual_eq`, `BiCGSTAB.alpha_eq` and `BiCGSTAB.beta_eq`. -/
private theorem vec_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) :
    ∀ j ≤ m, (iterate A b x₀ rs₀ j).r
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hjm : j < m := by omega
    have hα := alpha_eq_aux h hω hjm hr hp
    have hs : s A b x₀ rs₀ j
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      have hpoly : stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          = stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j
            - C (BCG.alpha A B b x₀ rs₀ j)
              * (X * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j)) := by
        rw [BCG.residualPoly_succ]; ring
      rw [s, hr, hp, hα, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    have hr' : (iterate A b x₀ rs₀ (j + 1)).r = aeval A
        (stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)) (b - A x₀) := by
      have hpoly : stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          = stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1)
            - C (omega A b x₀ rs₀ j)
              * (X * (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ (j + 1))) := by
        rw [stabPoly_succ]; ring
      rw [iterate_succ_r, hs, hpoly, aeval_apply_sub, aeval_apply_C_mul, aeval_apply_X_mul]
    refine ⟨hr', ?_⟩
    have hβ := beta_eq_aux h hω hjm hr hr' hα
    have hpoly : stabPoly A b x₀ rs₀ (j + 1) * BCG.directionPoly A B b x₀ rs₀ (j + 1)
        = stabPoly A b x₀ rs₀ (j + 1) * BCG.residualPoly A B b x₀ rs₀ (j + 1)
          + C (BCG.beta A B b x₀ rs₀ j)
            * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j
              - C (omega A b x₀ rs₀ j)
                * (X * (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j))) := by
      rw [BCG.directionPoly_succ A B b x₀ rs₀ j, stabPoly_succ]
      ring
    rw [iterate_succ_p, hr', hp, hβ, hpoly, aeval_apply_add, aeval_apply_C_mul, aeval_apply_sub,
      aeval_apply_C_mul, aeval_apply_X_mul]

/-- **BiCGSTAB computes the stabilized BCG polynomials** ([saad2003iterative] (7.46), (7.52), van
der Vorst; [golub2013matrix] §11.4.5): if the BCG run with `B` the adjoint of `A` does not break
down through step `m` and no `ω_i` with `i < m` vanishes, then for `j ≤ m`, with
`r₀ = b - A x₀`, `r_j = ψ_j(A) φ_j(A) r₀` and `p_j = ψ_j(A) π_j(A) r₀`. -/
theorem residual_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j ≤ m) :
    (iterate A b x₀ rs₀ j).r
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.residualPoly A B b x₀ rs₀ j) (b - A x₀) ∧
      (iterate A b x₀ rs₀ j).p
        = aeval A (stabPoly A b x₀ rs₀ j * BCG.directionPoly A B b x₀ rs₀ j) (b - A x₀) :=
  vec_eq h hω j hj

/-- **The BCG step length from the BiCGSTAB vectors** ([saad2003iterative] (7.53)): under the
hypotheses of `BiCGSTAB.residual_eq`, the BiCGSTAB `α_j = ⟪r*₀, r_j⟫/⟪r*₀, A p_j⟫` is the BCG
`α_j`, for `j < m`. -/
theorem alpha_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    alpha A b x₀ rs₀ j = BCG.alpha A B b x₀ rs₀ j := by
  obtain ⟨hr, hp⟩ := vec_eq h hω j hj.le
  exact alpha_eq_aux h hω hj hr hp

/-- **The BCG direction coefficient from the BiCGSTAB vectors** ([saad2003iterative] (7.54)):
under the hypotheses of `BiCGSTAB.residual_eq`, the BiCGSTAB
`β_j = (⟪r*₀, r_{j+1}⟫/⟪r*₀, r_j⟫)(α_j/ω_j)` is the BCG `β_j`, for `j < m`. -/
theorem beta_eq (hω : ∀ i < m, omega A b x₀ rs₀ i ≠ 0) {j : ℕ} (hj : j < m) :
    beta A b x₀ rs₀ j = BCG.beta A B b x₀ rs₀ j := by
  obtain ⟨hr, hp⟩ := vec_eq h hω j hj.le
  exact beta_eq_aux h hω hj hr (vec_eq h hω (j + 1) hj).1 (alpha_eq_aux h hω hj hr hp)

end Polynomial

end BiCGSTAB
