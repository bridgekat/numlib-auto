import Numlib.Krylov.Hessenberg

/-!
# The two-sided Lanczos process

The Lanczos biorthogonalization of [saad2003iterative], Alg 7.1: two sequences `v_j` and `w_j`,
built from a starting pair with `⟪w₁, v₁⟫ = 1` by the coupled three-term recurrences

```
δ_{j+1} v_{j+1} = A v_j - α_j v_j - β_j v_{j-1},
conj β_{j+1} w_{j+1} = Aᴴ w_j - conj α_j w_j - conj δ_j w_{j-1},
```

with `α_j = ⟪w_j, A v_j⟫`, `δ_{j+1} = |⟪ŵ_{j+1}, v̂_{j+1}⟫|^{1/2}` and `β_{j+1} = ⟪ŵ_{j+1},
v̂_{j+1}⟫ / δ_{j+1}`, the normalization that keeps `⟪w_j, v_j⟫ = 1`. The adjoint enters as a second
operator `B` with `⟪A x, y⟫ = ⟪x, B y⟫`, taken as data because the ambient space is neither assumed
complete nor finite-dimensional.

The main results are [saad2003iterative] Prop 7.1: the two families are biorthogonal
(`BiLanczos.inner_vec_dualVec`), they span `𝒦_m(A, v₁)` and `𝒦_m(B, w₁)` (`BiLanczos.span_vec`,
`BiLanczos.span_dualVec`), and `W_mᴴ A V_m = T_m` for the tridiagonal coefficient array
(`BiLanczos.inner_dualVec_apply_vec`). The relation `A V_m = V_{m+1} T̄_m` is a
`Krylov.HessenbergRelation` of `Numlib/Krylov/Hessenberg` with a basis that is *not* orthonormal
(`BiLanczos.hessenbergRelation`), so the residual formula `Krylov.HessenbergRelation.residual_eq`
applies verbatim.

Breakdown comes in two kinds. A *lucky* one, `v̂_{j+1} = 0`, is benign: it implies
`BiLanczos.NoSeriousBreakdown` (`BiLanczos.NoSeriousBreakdown.of_vhat_eq_zero`), the span built so
far is `𝒦_{j+1}(A, v₁)` (`BiLanczos.span_vec_succ`) and it is `A`-invariant
(`BiLanczos.subspace_succ_mem_invtSubmodule_of_vhat_eq_zero`). A *serious* one,
`⟪ŵ_{j+1}, v̂_{j+1}⟫ = 0` with `v̂_{j+1} ≠ 0`, is what the theory has to exclude.

The last section is the polynomial picture. Every vector the process builds is a polynomial in `A`
applied to `v₁` (`BiLanczos.poly`, `BiLanczos.vhatPoly`, `BiLanczos.aeval_poly`,
`BiLanczos.aeval_vhatPoly`), the dual vectors are the *conjugate* polynomials in `B` applied to
`w₁` up to a scalar (`BiLanczos.dualVhat_eq_smul`), and the form these are orthogonal for is the
indefinite `BiLanczos.polyForm`, `⟨p, q⟩ = ⟪q̄(B) w₁, p(A) v₁⟫`. That form is a *moment functional*
(`BiLanczos.polyForm_eq_moment`), which makes it symmetric and makes its moment matrix a Hankel
matrix (`BiLanczos.momentMatrix_apply_eq_of_add_eq`); and a serious breakdown is exactly the
vanishing of `⟨p, p⟩` on the current polynomial
(`BiLanczos.delta_succ_eq_zero_iff_polyForm_eq_zero`).

The two methods built on the process are here as well. `BCG` is the biconjugate gradient algorithm
(Alg 7.3): its residuals are biorthogonal and its directions `A`-biconjugate
(`BCG.inner_residual_dualResidual_eq_zero`, `BCG.inner_dualDirection_apply_direction_eq_zero`, Prop
7.2), which makes its iterate the Petrov–Galerkin iterate with `L = 𝒦_m(Aᴴ, r*₀)`
(`BCG.isPetrovGalerkin`). `QMR` minimizes the *quasi*-residual `‖β e₁ - T̄_m y‖` rather than the
residual itself (`QMR.IsQuasiMinResidual`, (7.15)–(7.17)); `QMR.norm_residual_le_norm_quasiResidual` is
Prop 7.3 and `QMR.norm_residual_le` is Thm 7.4, the comparison `‖r^Q_m‖ ≤ κ₂(V_{m+1}) ‖r^G_m‖` with
the GMRES residual. Because an abstract inner product space has no matrix `V_{m+1}`, the two
singular-value bounds `c ‖z‖ ≤ ‖∑ z_i v_i‖ ≤ C ‖z‖` on the coordinate map are hypotheses and
`κ₂(V_{m+1})` is `C / c`.

Indices are `0`-based as in the rest of the Krylov layer, so `vec A B v₁ w₁ 0 = v₁` and the
coefficient `delta A B v₁ w₁ j` is the book's `δ_{j+1}`. Breakdown is uniform: the recurrence
returns `0` from the first vanishing `δ` onwards, because `(0 : 𝕜)⁻¹ = 0`.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace BiLanczos

/-- The state of the two-sided Lanczos recurrence at step `j`: the current pair `(v_j, w_j)`, the
previous pair, and the two scalars the next step consumes. -/
structure State (𝕜 E : Type*) where
  /-- The primal vector `v_j`. -/
  v : E
  /-- The dual vector `w_j`. -/
  w : E
  /-- The previous primal vector `v_{j-1}`, and `0` at `j = 0`. -/
  vPrev : E
  /-- The previous dual vector `w_{j-1}`, and `0` at `j = 0`. -/
  wPrev : E
  /-- The coefficient `β_j`, and `0` at `j = 0`. -/
  beta : 𝕜
  /-- The coefficient `δ_j`, and `0` at `j = 0`. -/
  delta : 𝕜

/-- The diagonal coefficient `α_j = ⟪w_j, A v_j⟫` computed from a state. -/
noncomputable def stepAlpha (A : E →ₗ[𝕜] E) (s : State 𝕜 E) : 𝕜 := inner 𝕜 s.w (A s.v)

/-- The unnormalized primal vector `v̂_{j+1} = A v_j - α_j v_j - β_j v_{j-1}` of one step. -/
noncomputable def stepVhat (A : E →ₗ[𝕜] E) (s : State 𝕜 E) : E :=
  A s.v - stepAlpha A s • s.v - s.beta • s.vPrev

/-- The unnormalized dual vector `ŵ_{j+1} = B w_j - conj α_j w_j - conj δ_j w_{j-1}` of one step. -/
noncomputable def stepWhat (A B : E →ₗ[𝕜] E) (s : State 𝕜 E) : E :=
  B s.w - starRingEnd 𝕜 (stepAlpha A s) • s.w - starRingEnd 𝕜 s.delta • s.wPrev

/-- One step of [saad2003iterative], Alg 7.1. -/
noncomputable def step (A B : E →ₗ[𝕜] E) (s : State 𝕜 E) : State 𝕜 E :=
  let vh := stepVhat A s
  let wh := stepWhat A B s
  let z : 𝕜 := inner 𝕜 wh vh
  let d : 𝕜 := ((Real.sqrt ‖z‖ : ℝ) : 𝕜)
  { v := d⁻¹ • vh
    w := (starRingEnd 𝕜 (z / d))⁻¹ • wh
    vPrev := s.v
    wPrev := s.w
    beta := z / d
    delta := d }

/-- The state of the process after `j` steps, started from the pair `(v₁, w₁)`. -/
noncomputable def state (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : State 𝕜 E :=
  (step A B)^[j] { v := v₁, w := w₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

section Recurrence

variable (A B : E →ₗ[𝕜] E) (v₁ w₁ : E)

/-- The primal two-sided Lanczos vectors `v_j`, a basis of `𝒦_m(A, v₁)`. -/
noncomputable def vec (j : ℕ) : E := (state A B v₁ w₁ j).v

/-- The dual two-sided Lanczos vectors `w_j`, a basis of `𝒦_m(B, w₁)`. -/
noncomputable def dualVec (j : ℕ) : E := (state A B v₁ w₁ j).w

/-- `v_{j-1}`, with the convention `v_{-1} = 0`. -/
noncomputable def vecPrev (j : ℕ) : E := (state A B v₁ w₁ j).vPrev

/-- `w_{j-1}`, with the convention `w_{-1} = 0`. -/
noncomputable def dualVecPrev (j : ℕ) : E := (state A B v₁ w₁ j).wPrev

/-- The superdiagonal coefficient `β_j` (the book's `β_{j+1}`), with `β_0 = 0`. -/
noncomputable def beta (j : ℕ) : 𝕜 := (state A B v₁ w₁ j).beta

/-- The subdiagonal coefficient `δ_j` (the book's `δ_{j+1}`), with `δ_0 = 0`. -/
noncomputable def delta (j : ℕ) : 𝕜 := (state A B v₁ w₁ j).delta

/-- The diagonal coefficient `α_j = ⟪w_j, A v_j⟫`. -/
noncomputable def alpha (j : ℕ) : 𝕜 := stepAlpha A (state A B v₁ w₁ j)

/-- The unnormalized primal vector `v̂_{j+1} = A v_j - α_j v_j - β_j v_{j-1}`. -/
noncomputable def vhat (j : ℕ) : E := stepVhat A (state A B v₁ w₁ j)

/-- The unnormalized dual vector `ŵ_{j+1} = B w_j - conj α_j w_j - conj δ_j w_{j-1}`. -/
noncomputable def dualVhat (j : ℕ) : E := stepWhat A B (state A B v₁ w₁ j)

/-- The biorthogonality scalar `⟪ŵ_{j+1}, v̂_{j+1}⟫` whose vanishing is a breakdown. -/
noncomputable def zeta (j : ℕ) : 𝕜 := inner 𝕜 (dualVhat A B v₁ w₁ j) (vhat A B v₁ w₁ j)

/-! ### Unfolding the recurrence -/

@[simp] theorem vec_zero : vec A B v₁ w₁ 0 = v₁ := rfl

@[simp] theorem dualVec_zero : dualVec A B v₁ w₁ 0 = w₁ := rfl

@[simp] theorem vecPrev_zero : vecPrev A B v₁ w₁ 0 = 0 := rfl

@[simp] theorem dualVecPrev_zero : dualVecPrev A B v₁ w₁ 0 = 0 := rfl

@[simp] theorem beta_zero : beta A B v₁ w₁ 0 = 0 := rfl

@[simp] theorem delta_zero : delta A B v₁ w₁ 0 = 0 := rfl

/-- The recurrence: state `j + 1` is one `BiLanczos.step` applied to state `j`. -/
theorem state_succ (j : ℕ) : state A B v₁ w₁ (j + 1) = step A B (state A B v₁ w₁ j) :=
  Function.iterate_succ_apply' _ _ _

/-- The unnormalized next primal vector: `v̂_{j+1} = A v_j - α_j v_j - β_j v_{j-1}`
([saad2003iterative], Alg 7.1, line 5). -/
theorem vhat_eq (j : ℕ) : vhat A B v₁ w₁ j =
    A (vec A B v₁ w₁ j) - alpha A B v₁ w₁ j • vec A B v₁ w₁ j -
      beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j := rfl

/-- The unnormalized next dual vector: `ŵ_{j+1} = Aᴴ w_j - conj α_j w_j - conj δ_j w_{j-1}`
([saad2003iterative], Alg 7.1, line 6). -/
theorem dualVhat_eq (j : ℕ) : dualVhat A B v₁ w₁ j =
    B (dualVec A B v₁ w₁ j) - starRingEnd 𝕜 (alpha A B v₁ w₁ j) • dualVec A B v₁ w₁ j -
      starRingEnd 𝕜 (delta A B v₁ w₁ j) • dualVecPrev A B v₁ w₁ j := rfl

/-- `α_j = ⟪w_j, A v_j⟫` ([saad2003iterative], Alg 7.1, line 4). -/
theorem alpha_eq (j : ℕ) :
    alpha A B v₁ w₁ j = inner 𝕜 (dualVec A B v₁ w₁ j) (A (vec A B v₁ w₁ j)) := rfl

@[simp] theorem vecPrev_succ (j : ℕ) : vecPrev A B v₁ w₁ (j + 1) = vec A B v₁ w₁ j := by
  rw [vecPrev, state_succ]; rfl

@[simp] theorem dualVecPrev_succ (j : ℕ) :
    dualVecPrev A B v₁ w₁ (j + 1) = dualVec A B v₁ w₁ j := by
  rw [dualVecPrev, state_succ]; rfl

/-- `δ_{j+1} = |⟪ŵ_{j+1}, v̂_{j+1}⟫|^{1/2}` ([saad2003iterative], Alg 7.1, line 7). -/
theorem delta_succ (j : ℕ) :
    delta A B v₁ w₁ (j + 1) = ((Real.sqrt ‖zeta A B v₁ w₁ j‖ : ℝ) : 𝕜) := by
  rw [delta, state_succ]; rfl

/-- `β_{j+1} = ⟪ŵ_{j+1}, v̂_{j+1}⟫ / δ_{j+1}` ([saad2003iterative], Alg 7.1, line 8). -/
theorem beta_succ (j : ℕ) :
    beta A B v₁ w₁ (j + 1) = zeta A B v₁ w₁ j / delta A B v₁ w₁ (j + 1) := by
  rw [delta_succ, beta, state_succ]; rfl

/-- `v_{j+1} = v̂_{j+1} / δ_{j+1}` ([saad2003iterative], Alg 7.1, line 10), and `0` on breakdown. -/
theorem vec_succ (j : ℕ) :
    vec A B v₁ w₁ (j + 1) = (delta A B v₁ w₁ (j + 1))⁻¹ • vhat A B v₁ w₁ j := by
  rw [delta_succ, vec, state_succ]; rfl

/-- `w_{j+1} = ŵ_{j+1} / conj β_{j+1}` ([saad2003iterative], Alg 7.1, line 9), and `0` on breakdown.
-/
theorem dualVec_succ (j : ℕ) : dualVec A B v₁ w₁ (j + 1) =
    (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ • dualVhat A B v₁ w₁ j := by
  rw [beta_succ, delta_succ, dualVec, state_succ]; rfl

/-! ### The coefficients -/

/-- The subdiagonal coefficients are real and nonnegative. -/
theorem conj_delta (j : ℕ) :
    starRingEnd 𝕜 (delta A B v₁ w₁ j) = delta A B v₁ w₁ j := by
  cases j with
  | zero => rw [delta_zero, map_zero]
  | succ j => rw [delta_succ, RCLike.conj_ofReal]

/-- Breakdown is exactly the vanishing of the biorthogonality scalar. -/
theorem delta_succ_eq_zero_iff (j : ℕ) :
    delta A B v₁ w₁ (j + 1) = 0 ↔ zeta A B v₁ w₁ j = 0 := by
  rw [delta_succ, RCLike.ofReal_eq_zero, Real.sqrt_eq_zero', ← not_lt]
  simp [norm_pos_iff]

/-- `β` breaks down with `δ`, at the same scalar. -/
theorem beta_succ_eq_zero_iff (j : ℕ) :
    beta A B v₁ w₁ (j + 1) = 0 ↔ zeta A B v₁ w₁ j = 0 := by
  rw [beta_succ, div_eq_zero_iff, delta_succ_eq_zero_iff, or_self]

/-- The two coefficients of a step vanish together, so either may serve as the breakdown test. -/
theorem beta_succ_ne_zero_iff (j : ℕ) :
    beta A B v₁ w₁ (j + 1) ≠ 0 ↔ delta A B v₁ w₁ (j + 1) ≠ 0 := by
  rw [ne_eq, ne_eq, beta_succ_eq_zero_iff, delta_succ_eq_zero_iff]

/-- [saad2003iterative], (7.1): the two scaling scalars of Alg 7.1, lines 7–8, multiply to the
biorthogonality scalar, `δ_{j+1} β_{j+1} = ⟪ŵ_{j+1}, v̂_{j+1}⟫`. Lines 9 and 10 divide the two
unnormalized vectors by them, so this product is the *only* constraint the normalization
`⟪w_{j+1}, v_{j+1}⟫ = 1` places on the pair; see `BiLanczos.inner_smul_smul_eq_one_of_mul_eq`.
No hypothesis is needed, since at a breakdown both sides vanish. -/
theorem delta_mul_beta_succ (j : ℕ) :
    delta A B v₁ w₁ (j + 1) * beta A B v₁ w₁ (j + 1) = zeta A B v₁ w₁ j := by
  rcases eq_or_ne (delta A B v₁ w₁ (j + 1)) 0 with hd | hd
  · rw [hd, zero_mul, (delta_succ_eq_zero_iff A B v₁ w₁ j).1 hd]
  · rw [beta_succ]
    field_simp

/-- The scaling freedom behind [saad2003iterative], (7.1): *any* pair `(δ, β)` of scalars whose
product is `⟪ŵ, v̂⟫ ≠ 0` normalizes a step of the two-sided Lanczos process,
`⟪ŵ / conj β, v̂ / δ⟫ = 1`. The choice of Alg 7.1, lines 7–8 is one such pair
(`BiLanczos.delta_mul_beta_succ`); so is the unit-2-norm scaling `δ = ‖v̂‖₂` the book switches to
at its (7.18). -/
theorem inner_smul_smul_eq_one_of_mul_eq {vh wh : E} {δ β : 𝕜} (hne : inner 𝕜 wh vh ≠ 0)
    (h : δ * β = inner 𝕜 wh vh) :
    inner 𝕜 ((starRingEnd 𝕜 β)⁻¹ • wh) (δ⁻¹ • vh) = 1 := by
  have hd : δ ≠ 0 := by rintro rfl; exact hne (by rw [← h, zero_mul])
  have hb : β ≠ 0 := by rintro rfl; exact hne (by rw [← h, mul_zero])
  rw [inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_conj, ← h]
  field_simp

/-- With the determination of [saad2003iterative], Alg 7.1 lines 7–8 the two coefficients have the
same modulus, `|β_{j+1}| = δ_{j+1}` — the book's "the `δ_j`'s are positive and `β_j = ±δ_j`". -/
theorem norm_beta_succ (j : ℕ) :
    ‖beta A B v₁ w₁ (j + 1)‖ = ‖delta A B v₁ w₁ (j + 1)‖ := by
  rw [beta_succ, norm_div, delta_succ, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.div_sqrt]

/-- Off breakdown, `v̂_{j+1} = δ_{j+1} v_{j+1}`. -/
theorem smul_vec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) = vhat A B v₁ w₁ j := by
  rw [vec_succ, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Off breakdown, `ŵ_{j+1} = conj β_{j+1} w_{j+1}`. -/
theorem smul_dualVec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) • dualVec A B v₁ w₁ (j + 1) =
      dualVhat A B v₁ w₁ j := by
  have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
    simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 h
  rw [dualVec_succ, smul_smul, mul_inv_cancel₀ hb, one_smul]

/-- The normalization of [saad2003iterative] Algorithm 7.1: off breakdown, `⟪w_{j+1}, v_{j+1}⟫ = 1`.
-/
theorem inner_dualVec_vec_succ {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    inner 𝕜 (dualVec A B v₁ w₁ (j + 1)) (vec A B v₁ w₁ (j + 1)) = 1 := by
  have hz : zeta A B v₁ w₁ j ≠ 0 := fun hc =>
    h ((delta_succ_eq_zero_iff A B v₁ w₁ j).2 hc)
  rw [dualVec_succ, vec_succ, inner_smul_left, inner_smul_right, ← zeta, beta_succ]
  rw [map_inv₀, RCLike.conj_conj]
  field_simp

/-! ### The three-term recurrences -/

/-- [saad2003iterative], (7.3): `A v_j = β_j v_{j-1} + α_j v_j + δ_{j+1} v_{j+1}`. -/
theorem apply_vec {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    A (vec A B v₁ w₁ j) = beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j +
      alpha A B v₁ w₁ j • vec A B v₁ w₁ j + delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  rw [smul_vec_succ A B v₁ w₁ h, vhat_eq]
  abel

/-- [saad2003iterative], (7.4): `B w_j = conj δ_j w_{j-1} + conj α_j w_j + conj β_{j+1} w_{j+1}`. -/
theorem apply_dualVec {j : ℕ} (h : delta A B v₁ w₁ (j + 1) ≠ 0) :
    B (dualVec A B v₁ w₁ j) =
      starRingEnd 𝕜 (delta A B v₁ w₁ j) • dualVecPrev A B v₁ w₁ j +
        starRingEnd 𝕜 (alpha A B v₁ w₁ j) • dualVec A B v₁ w₁ j +
        starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) • dualVec A B v₁ w₁ (j + 1) := by
  rw [smul_dualVec_succ A B v₁ w₁ h, dualVhat_eq]
  abel

/-- The tridiagonal coefficient array of the process ([saad2003iterative], (7.5)): `α` on the
diagonal, `δ` on the subdiagonal and `β` on the superdiagonal. -/
noncomputable def coeff (i j : ℕ) : 𝕜 :=
  if i = j then alpha A B v₁ w₁ i
  else if i = j + 1 then delta A B v₁ w₁ i
  else if j = i + 1 then beta A B v₁ w₁ j
  else 0

@[simp] theorem coeff_self (j : ℕ) : coeff A B v₁ w₁ j j = alpha A B v₁ w₁ j := by
  rw [coeff, ite_eq_left rfl]

@[simp] theorem coeff_succ_self (j : ℕ) :
    coeff A B v₁ w₁ (j + 1) j = delta A B v₁ w₁ (j + 1) := by
  rw [coeff, ite_eq_right (by omega), ite_eq_left rfl]

@[simp] theorem coeff_self_succ (j : ℕ) :
    coeff A B v₁ w₁ j (j + 1) = beta A B v₁ w₁ (j + 1) := by
  rw [coeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

/-- The coefficient array is tridiagonal: everything off the three central diagonals is `0`. -/
theorem coeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) (h₃ : j ≠ i + 1) :
    coeff A B v₁ w₁ i j = 0 := by
  rw [coeff, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]

/-- The array is upper Hessenberg, which is what `Krylov.HessenbergRelation` asks for. -/
theorem coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A B v₁ w₁ i j = 0 :=
  coeff_eq_zero A B v₁ w₁ (by omega) (by omega) (by omega)

/-- Everything strictly to the left of the subdiagonal collapses to the single `β_j` term. -/
private theorem sum_coeff_lt (j : ℕ) :
    ∑ i ∈ Finset.range j, coeff A B v₁ w₁ i j • vec A B v₁ w₁ i =
      beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ n =>
    have hz : ∑ i ∈ Finset.range n, coeff A B v₁ w₁ i (n + 1) • vec A B v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hin : i < n := Finset.mem_range.1 hi
        rw [coeff_eq_zero A B v₁ w₁ (by omega) (by omega) (by omega), zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, coeff_self_succ, vecPrev_succ]

/-! ### The Krylov subspaces -/

private theorem mem_subspace_aux (j : ℕ) :
    vec A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) ∧
      vecPrev A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) := by
  induction j with
  | zero =>
    exact ⟨Krylov.self_mem_subspace A v₁ Nat.one_pos, Submodule.zero_mem _⟩
  | succ j ih =>
    have hmono := Krylov.subspace_mono A v₁ (Nat.le_succ (j + 1))
    refine ⟨?_, by rw [vecPrev_succ]; exact hmono ih.1⟩
    rw [vec_succ]
    refine Submodule.smul_mem _ _ ?_
    rw [vhat_eq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (Krylov.map_subspace_le A v₁ (j + 1) ⟨_, ih.1, rfl⟩)
      (Submodule.smul_mem _ _ (hmono ih.1))) (Submodule.smul_mem _ _ (hmono ih.2))

/-- `v_j ∈ 𝒦_{j+1}(A, v₁)`: the process only ever combines `v₁, A v₁, …, A^j v₁`. -/
theorem vec_mem_subspace (j : ℕ) : vec A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) :=
  (mem_subspace_aux A B v₁ w₁ j).1

/-- `v_{j-1} ∈ 𝒦_{j+1}(A, v₁)`, the previous primal vector carried in the state. -/
theorem vecPrev_mem_subspace (j : ℕ) : vecPrev A B v₁ w₁ j ∈ Krylov.subspace A v₁ (j + 1) :=
  (mem_subspace_aux A B v₁ w₁ j).2

private theorem dualMem_subspace_aux (j : ℕ) :
    dualVec A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) ∧
      dualVecPrev A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) := by
  induction j with
  | zero =>
    exact ⟨Krylov.self_mem_subspace B w₁ Nat.one_pos, Submodule.zero_mem _⟩
  | succ j ih =>
    have hmono := Krylov.subspace_mono B w₁ (Nat.le_succ (j + 1))
    refine ⟨?_, by rw [dualVecPrev_succ]; exact hmono ih.1⟩
    rw [dualVec_succ]
    refine Submodule.smul_mem _ _ ?_
    rw [dualVhat_eq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (Krylov.map_subspace_le B w₁ (j + 1) ⟨_, ih.1, rfl⟩)
      (Submodule.smul_mem _ _ (hmono ih.1))) (Submodule.smul_mem _ _ (hmono ih.2))

/-- `w_j ∈ 𝒦_{j+1}(B, w₁)` for `B` the adjoint of `A`. -/
theorem dualVec_mem_subspace (j : ℕ) : dualVec A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) :=
  (dualMem_subspace_aux A B v₁ w₁ j).1

/-- `w_{j-1} ∈ 𝒦_{j+1}(B, w₁)`, the previous dual vector carried in the state. -/
theorem dualVecPrev_mem_subspace (j : ℕ) :
    dualVecPrev A B v₁ w₁ j ∈ Krylov.subspace B w₁ (j + 1) :=
  (dualMem_subspace_aux A B v₁ w₁ j).2

end Recurrence

/-! ### Biorthogonality

[saad2003iterative], Prop 7.1. The hypotheses of the whole section are bundled as
`BiLanczos.NoBreakdown`: `B` is the adjoint of `A`, the starting pair is normalized, and no `δ`
vanishes before step `m`. -/

section Biorthogonality

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The two-sided Lanczos process of `A`, with `B` the adjoint of `A`, started at the pair `(v₁,
w₁)`, runs without breakdown through step `m`. -/
structure NoBreakdown (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (m : ℕ) : Prop where
  /-- `B` is the adjoint of `A`. It is taken as data because the ambient space is assumed neither
  complete nor finite-dimensional. -/
  adjoint : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)
  /-- The starting pair is normalized: `⟪w₁, v₁⟫ = 1`. -/
  inner_start : inner 𝕜 w₁ v₁ = 1
  /-- No breakdown occurs before step `m`. -/
  delta_ne_zero : ∀ j < m, delta A B v₁ w₁ (j + 1) ≠ 0

/-- Running without breakdown for `m` steps includes running without breakdown for fewer. -/
theorem NoBreakdown.mono {m n : ℕ} (h : NoBreakdown A B v₁ w₁ m) (hnm : n ≤ m) :
    NoBreakdown A B v₁ w₁ n :=
  ⟨h.adjoint, h.inner_start, fun j hj => h.delta_ne_zero j (hj.trans_le hnm)⟩

/-- Moving `A` across the inner product, with `B` its adjoint. -/
theorem inner_apply_eq (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (x y : E) :
    inner 𝕜 x (A y) = inner 𝕜 (B x) y := by
  rw [← inner_conj_symm x (A y), hB y x, inner_conj_symm (B x) y]

/-- Moving a power of `A` across the inner product: `B^k` is the adjoint of `A^k`. -/
theorem inner_pow_apply_eq (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (k : ℕ) (x y : E) :
    inner 𝕜 ((B ^ k) x) y = inner 𝕜 x ((A ^ k) y) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hB' : (B ^ (k + 1)) x = (B ^ k) (B x) := by rw [pow_succ]; rfl
    have hA' : (A ^ (k + 1)) y = A ((A ^ k) y) := by rw [pow_succ']; rfl
    rw [hB', ih (B x), ← inner_apply_eq hB, hA']

/-- Moving a *polynomial* in `A` across the inner product: the adjoint of `p(A)` is `p̄(B)`, the
polynomial with conjugated coefficients evaluated at the adjoint `B`.  Over `ℝ` it says that the
transpose of `p(A)` is `p(Aᵀ)`; it is what turns a bilinear expression in `p(A) v` and `q(B) w`
into one in `(q̄ p)(A) v` and `w`. -/
theorem inner_aeval_map_eq (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (p : Polynomial 𝕜)
    (x y : E) :
    inner 𝕜 (Polynomial.aeval B (p.map (starRingEnd 𝕜)) x)
        y = inner 𝕜 x (Polynomial.aeval A p y) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro q r hq hr
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
      hq, hr]
  · intro k a
    have hB' : Polynomial.aeval B (Polynomial.monomial k (starRingEnd 𝕜 a)) x
        = starRingEnd 𝕜 a • (B ^ k) x := by
      rw [Polynomial.aeval_monomial]
      simp [Module.algebraMap_end_apply]
    have hA' : Polynomial.aeval A (Polynomial.monomial k a) y = a • (A ^ k) y := by
      rw [Polynomial.aeval_monomial]
      simp [Module.algebraMap_end_apply]
    rw [Polynomial.map_monomial, hB', hA', inner_smul_left, inner_smul_right, RCLike.conj_conj,
      inner_pow_apply_eq hB]

/-- The biorthogonality relation up to step `m`, the invariant the induction carries. -/
private def Biorth (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (m : ℕ) : Prop :=
  ∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (dualVec A B v₁ w₁ i) (vec A B v₁ w₁ j) = if i = j then 1 else 0

private theorem inner_dualVec_vecPrev {n : ℕ} (hP : Biorth A B v₁ w₁ n) {i j : ℕ} (hi : i ≤ n)
    (hj : j ≤ n) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (vecPrev A B v₁ w₁ j) = if i + 1 = j then 1 else 0 := by
  cases j with
  | zero => simp
  | succ j => rw [vecPrev_succ, hP i hi j (by omega)]; simp

private theorem inner_dualVecPrev_vec {n : ℕ} (hP : Biorth A B v₁ w₁ n) {i j : ℕ} (hi : i ≤ n)
    (hj : j ≤ n) :
    inner 𝕜 (dualVecPrev A B v₁ w₁ i) (vec A B v₁ w₁ j) = if i = j + 1 then 1 else 0 := by
  cases i with
  | zero => simp
  | succ i => rw [dualVecPrev_succ, hP i (by omega) j hj]; simp

/-- The new primal vector is orthogonal to every dual vector built so far. -/
private theorem inner_dualVec_vhat {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1))
    (hP : Biorth A B v₁ w₁ m) {i : ℕ} (hi : i ≤ m) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (vhat A B v₁ w₁ m) = 0 := by
  rw [vhat_eq, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
    hP i hi m le_rfl, inner_dualVec_vecPrev hP hi le_rfl]
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [← alpha_eq]
    simp
  · have hd : delta A B v₁ w₁ (i + 1) ≠ 0 := h.delta_ne_zero i (by omega)
    have hne1 : i ≠ m := Nat.ne_of_lt hlt
    have hne2 : i ≠ m + 1 := by omega
    rw [inner_apply_eq h.adjoint, apply_dualVec _ _ _ _ hd, inner_add_left, inner_add_left,
      inner_smul_left, inner_smul_left, inner_smul_left, RCLike.conj_conj, RCLike.conj_conj,
      RCLike.conj_conj, inner_dualVecPrev_vec hP (le_of_lt hlt) le_rfl, hP i hi m le_rfl,
      hP (i + 1) hlt m le_rfl]
    by_cases hi1 : i + 1 = m
    · rw [hi1]
      simp [hne1, hne2]
    · simp [hne1, hne2, hi1]

/-- The new dual vector is orthogonal to every primal vector built so far. -/
private theorem inner_dualVhat_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1))
    (hP : Biorth A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (dualVhat A B v₁ w₁ m) (vec A B v₁ w₁ j) = 0 := by
  rw [dualVhat_eq, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left,
    RCLike.conj_conj, RCLike.conj_conj, hP m le_rfl j hj, inner_dualVecPrev_vec hP le_rfl hj]
  rw [← inner_apply_eq h.adjoint]
  rcases eq_or_lt_of_le hj with rfl | hlt
  · rw [← alpha_eq]
    simp
  · have hd : delta A B v₁ w₁ (j + 1) ≠ 0 := h.delta_ne_zero j (by omega)
    have hne1 : m ≠ j := Nat.ne_of_gt hlt
    have hne2 : m + 1 ≠ j := by omega
    rw [apply_vec _ _ _ _ hd, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, inner_smul_right, inner_dualVec_vecPrev hP le_rfl (le_of_lt hlt),
      hP m le_rfl j hj, hP m le_rfl (j + 1) hlt]
    by_cases hj1 : m = j + 1
    · rw [← hj1]
      simp [hne1, hne2]
    · simp [hne1, hne2, hj1]

private theorem biorth_succ {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1))
    (hP : Biorth A B v₁ w₁ m) : Biorth A B v₁ w₁ (m + 1) := by
  have hd : delta A B v₁ w₁ (m + 1) ≠ 0 := h.delta_ne_zero m (Nat.lt_succ_self m)
  intro i hi j hj
  by_cases hi' : i = m + 1
  · subst hi'
    by_cases hj' : j = m + 1
    · subst hj'
      rw [inner_dualVec_vec_succ _ _ _ _ hd]
      simp
    · rw [dualVec_succ, inner_smul_left, inner_dualVhat_vec h hP (by omega), mul_zero]
      simp [Ne.symm hj']
  · by_cases hj' : j = m + 1
    · subst hj'
      rw [vec_succ, inner_smul_right, inner_dualVec_vhat h hP (by omega), mul_zero]
      simp [hi']
    · exact hP i (by omega) j (by omega)

private theorem biorth {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) : Biorth A B v₁ w₁ m := by
  induction m with
  | zero =>
    intro i hi j hj
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    obtain rfl : j = 0 := Nat.le_zero.1 hj
    simpa using h.inner_start
  | succ m ih => exact biorth_succ h (ih (h.mono (Nat.le_succ m)))

/-- [saad2003iterative], Prop 7.1: the primal and dual two-sided Lanczos vectors are biorthogonal,
`⟪w_i, v_j⟫ = δ_{ij}`, as long as the process has not broken down. -/
theorem inner_dualVec_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (vec A B v₁ w₁ j) = if i = j then 1 else 0 :=
  biorth h i hi j hj

/-- [saad2003iterative], Prop 7.1, in the other order: `⟪v_i, w_j⟫ = δ_{ij}`. -/
theorem inner_vec_dualVec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) :
    inner 𝕜 (vec A B v₁ w₁ i) (dualVec A B v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [← inner_conj_symm, inner_dualVec_vec h hj hi]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

/-- [saad2003iterative], Prop 7.1: `W_mᴴ A V_m = T_m`, the tridiagonal coefficient array is the
oblique compression of `A` to `𝒦_m(A, v₁)` along `𝒦_m(B, w₁)`. -/
theorem inner_dualVec_apply_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ (m + 1)) {i j : ℕ}
    (hi : i ≤ m + 1) (hj : j ≤ m) :
    inner 𝕜 (dualVec A B v₁ w₁ i) (A (vec A B v₁ w₁ j)) = coeff A B v₁ w₁ i j := by
  have hd : delta A B v₁ w₁ (j + 1) ≠ 0 := h.delta_ne_zero j (by omega)
  rw [apply_vec _ _ _ _ hd, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right, inner_dualVec_vecPrev (biorth h) hi (by omega),
    inner_dualVec_vec h hi (by omega), inner_dualVec_vec h hi (by omega), coeff]
  by_cases h1 : i = j
  · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_left h1,
      ite_eq_right (by omega : i ≠ j + 1), ite_eq_left h1, h1]
    ring
  · by_cases h2 : i = j + 1
    · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_right h1, ite_eq_left h2,
        ite_eq_right h1, ite_eq_left h2, h2]
      ring
    · by_cases h3 : j = i + 1
      · rw [ite_eq_left (by omega : i + 1 = j), ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        ring
      · rw [ite_eq_right (by omega : i + 1 ≠ j), ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        ring

end Biorthogonality

/-! ### The Hessenberg relation and the Krylov bases -/

section Relation

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The process suffers no *serious* breakdown: whenever `δ_{j+1}` vanishes, the primal recurrence
has already terminated. This holds generically and at a regular termination `v̂_{j+1} = 0`, and it
is exactly what the Hessenberg relation needs — a serious breakdown (`⟪ŵ_{j+1}, v̂_{j+1}⟫ = 0` with
`v̂_{j+1} ≠ 0`) genuinely destroys it, since the relation then has no vector to expand `A v_j`
along. -/
structure NoSeriousBreakdown (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : Prop where
  /-- At a breakdown the primal recurrence has already terminated. -/
  vhat_eq_zero : ∀ j, delta A B v₁ w₁ (j + 1) = 0 → vhat A B v₁ w₁ j = 0

/-- `v̂_{j+1} = δ_{j+1} v_{j+1}` at every step, degenerate ones included. -/
theorem NoSeriousBreakdown.vhat_eq_smul (h : NoSeriousBreakdown A B v₁ w₁) (j : ℕ) :
    vhat A B v₁ w₁ j = delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  by_cases hd : delta A B v₁ w₁ (j + 1) = 0
  · rw [h.vhat_eq_zero j hd, hd, zero_smul]
  · rw [smul_vec_succ _ _ _ _ hd]

/-- Once the primal recurrence has terminated it stays terminated: `v̂_{m+1} = 0` forces
`v̂_{j+1} = 0` for every `j ≥ m`, because `v_{m+1}` and every vector after it is `0`. -/
theorem vhat_eq_zero_of_le {m : ℕ} (hv : vhat A B v₁ w₁ m = 0) {j : ℕ} (hj : m ≤ j) :
    vhat A B v₁ w₁ j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    change vhat A B v₁ w₁ (m + k + 1) = 0
    have hz : zeta A B v₁ w₁ (m + k) = 0 := by rw [zeta, ih, inner_zero_right]
    have hvec : vec A B v₁ w₁ (m + k + 1) = 0 := by rw [vec_succ, ih, smul_zero]
    have hb : beta A B v₁ w₁ (m + k + 1) = 0 := by rw [beta_succ, hz, zero_div]
    simp [vhat_eq, hvec, hb]

/-- **A lucky breakdown is not a serious one** ([saad2003iterative], §7.1.2): if the process runs
`m` clean steps and then the primal recurrence terminates, `v̂_{m+1} = 0`, then
`BiLanczos.NoSeriousBreakdown` holds globally — before step `m` because no `δ` vanishes there, and
from step `m` on because every later `v̂` vanishes too. So the Hessenberg relation and everything
built on it survive a lucky breakdown. -/
theorem NoSeriousBreakdown.of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) : NoSeriousBreakdown A B v₁ w₁ where
  vhat_eq_zero j hj := by
    rcases lt_or_ge j m with hjm | hjm
    · exact absurd hj (h.delta_ne_zero j hjm)
    · exact vhat_eq_zero_of_le hv hjm

/-- The three-term recurrence `A v_j = β_j v_{j-1} + α_j v_j + δ_{j+1} v_{j+1}` at every step. -/
theorem NoSeriousBreakdown.apply_vec (h : NoSeriousBreakdown A B v₁ w₁) (j : ℕ) :
    A (vec A B v₁ w₁ j) = beta A B v₁ w₁ j • vecPrev A B v₁ w₁ j +
      alpha A B v₁ w₁ j • vec A B v₁ w₁ j +
      delta A B v₁ w₁ (j + 1) • vec A B v₁ w₁ (j + 1) := by
  rw [← h.vhat_eq_smul j, vhat_eq]
  abel

/-- [saad2003iterative], (7.3): `A V_m = V_{m+1} T̄_m` is a `Krylov.HessenbergRelation` whose basis
is biorthogonal rather than orthonormal, so the residual formula
`Krylov.HessenbergRelation.residual_eq` applies to it verbatim. -/
theorem hessenbergRelation (h : NoSeriousBreakdown A B v₁ w₁) :
    Krylov.HessenbergRelation A (vec A B v₁ w₁) (coeff A B v₁ w₁) where
  apply_eq j := by
    have hr : j + 2 = j + 1 + 1 := rfl
    rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, sum_coeff_lt, coeff_self,
      coeff_succ_self]
    exact h.apply_vec j
  eq_zero_of_lt _ _ hij := coeff_eq_zero_of_lt _ _ _ _ hij

private theorem map_span_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    Submodule.map A (Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio k)) ≤
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < k := hi
  have hd : delta A B v₁ w₁ (i + 1) ≠ 0 := h.delta_ne_zero i (lt_of_lt_of_le hi' hk)
  have hmem : ∀ l < k + 1, vec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, apply_vec _ _ _ _ hd]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · cases i with
    | zero => rw [vecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [vecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem (i + 1) (by omega))

private theorem pow_apply_mem_span {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    (A ^ k) v₁ ∈ Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  induction k with
  | zero =>
    have h0 : (A ^ 0) v₁ = vec A B v₁ w₁ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ k ih =>
    have hpow : (A ^ (k + 1)) v₁ = A ((A ^ k) v₁) := by rw [pow_succ']; rfl
    rw [hpow]
    exact map_span_le h hk ⟨_, ih (by omega), rfl⟩

/-- [saad2003iterative], Prop 7.1: the primal vectors are a basis of `𝒦_m(A, v₁)`. -/
theorem span_vec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio m) = Krylov.subspace A v₁ m := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact Krylov.subspace_mono A v₁ (Nat.succ_le_of_lt hi) (vec_mem_subspace A B v₁ w₁ i)
  · rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m := hk
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (pow_apply_mem_span h hk'.le)

/-- `m` good steps produce `v_0, …, v_m`, one vector more than `BiLanczos.span_vec` accounts for,
and they span `𝒦_{m+1}(A, v₁)`. This is the form the lucky-breakdown statement of
[saad2003iterative], §7.1.2 needs: at a breakdown after step `m` there is no `NoBreakdown (m+1)` to
appeal to, yet `v_m` is there and the span has already closed up. -/
theorem span_vec_succ {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) = Krylov.subspace A v₁ (m + 1) := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact Krylov.subspace_mono A v₁ (Nat.succ_le_of_lt hi) (vec_mem_subspace A B v₁ w₁ i)
  · rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m + 1 := hk
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (pow_apply_mem_span h (by omega))

/-- The lucky breakdown of [saad2003iterative], §7.1.2: if the primal recurrence terminates,
`v̂_{m+1} = 0`, then `A` maps the span of `v_0, …, v_m` into itself — the last three-term relation
loses its `v_{m+1}` term and the span closes up. -/
theorem map_span_vec_succ_le_of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) :
    Submodule.map A (Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1))) ≤
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < m + 1 := hi
  have hmem : ∀ l < m + 1, vec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (vec A B v₁ w₁ '' Set.Iio (m + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with him | him
  · exact map_span_le h (le_refl m) ⟨_, Submodule.subset_span ⟨i, him, rfl⟩, rfl⟩
  · subst him
    have happ : A (vec A B v₁ w₁ i) =
        alpha A B v₁ w₁ i • vec A B v₁ w₁ i + beta A B v₁ w₁ i • vecPrev A B v₁ w₁ i := by
      have h0 : A (vec A B v₁ w₁ i) - alpha A B v₁ w₁ i • vec A B v₁ w₁ i -
          beta A B v₁ w₁ i • vecPrev A B v₁ w₁ i = 0 := by
        rw [← vhat_eq]; exact hv
      rw [sub_sub, sub_eq_zero] at h0
      exact h0
    rw [SetLike.mem_coe, happ]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem i hi')) ?_
    cases i with
    | zero => rw [vecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [vecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))

/-- The lucky breakdown of [saad2003iterative], §7.1.2, as a statement about the Krylov subspace:
a terminating primal recurrence leaves `𝒦_{m+1}(A, v₁)` invariant under `A`. -/
theorem subspace_succ_mem_invtSubmodule_of_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m)
    (hv : vhat A B v₁ w₁ m = 0) :
    Krylov.subspace A v₁ (m + 1) ∈ Module.End.invtSubmodule A := by
  rw [← span_vec_succ h]
  exact (Module.End.mem_invtSubmodule_iff_map_le A).2 (map_span_vec_succ_le_of_vhat_eq_zero h hv)

private theorem map_dualSpan_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ} (hk : k ≤ m) :
    Submodule.map B (Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio k)) ≤
      Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hi' : i < k := hi
  have hd : delta A B v₁ w₁ (i + 1) ≠ 0 := h.delta_ne_zero i (lt_of_lt_of_le hi' hk)
  have hmem : ∀ l < k + 1, dualVec A B v₁ w₁ l ∈
      Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := fun l hl =>
    Submodule.subset_span ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, apply_dualVec _ _ _ _ hd]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · cases i with
    | zero => rw [dualVecPrev_zero, smul_zero]; exact Submodule.zero_mem _
    | succ i => rw [dualVecPrev_succ]; exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem i (by omega))
  · exact Submodule.smul_mem _ _ (hmem (i + 1) (by omega))

private theorem pow_apply_mem_dualSpan {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {k : ℕ}
    (hk : k < m) : (B ^ k) w₁ ∈ Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (k + 1)) := by
  induction k with
  | zero =>
    have h0 : (B ^ 0) w₁ = dualVec A B v₁ w₁ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ k ih =>
    have hpow : (B ^ (k + 1)) w₁ = B ((B ^ k) w₁) := by rw [pow_succ']; rfl
    rw [hpow]
    exact map_dualSpan_le h (le_of_lt hk) ⟨_, ih (by omega), rfl⟩

/-- [saad2003iterative], Prop 7.1: the dual vectors are a basis of `𝒦_m(Aᴴ, w₁)`. -/
theorem span_dualVec {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) :
    Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio m) = Krylov.subspace B w₁ m := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨i, hi, rfl⟩
    exact Krylov.subspace_mono B w₁ (Nat.succ_le_of_lt hi) (dualVec_mem_subspace A B v₁ w₁ i)
  · rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < m := hk
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (pow_apply_mem_dualSpan h hk')

end Relation

/-! ### Formal orthogonal polynomials and the moment matrix

[saad2003iterative], §7.1.2. Every vector the process builds is a polynomial in `A` applied to
`v₁`: `BiLanczos.poly` is the sequence with `p_j(A) v₁ = v_j` and `BiLanczos.vhatPoly` the one with
`p̂_j(A) v₁ = v̂_{j+1}`, both defined by the divided recurrence so that they survive breakdown.
The bilinear form the process orthogonalizes them against is `BiLanczos.polyForm`,
`⟨p, q⟩ = (p(A) v₁, q(Aᴴ) w₁)`, which is *indefinite* — `⟨p, p⟩` may vanish on a nonzero
polynomial, and that is what a serious breakdown is.

The one structural fact about the form is `BiLanczos.polyForm_eq_moment`: it is a moment
functional, `⟨p, q⟩ = L(p q)` with `L(r) = ⟪w₁, r(A) v₁⟫`. Symmetry (`BiLanczos.polyForm_comm`)
and the Hankel structure of the moment matrix
(`BiLanczos.momentMatrix_apply_eq_of_add_eq`) are immediate from it. -/

section FormalOrthogonalPolynomials

open Polynomial

variable (A B : E →ₗ[𝕜] E) (v₁ w₁ : E)

/-- The moment functional of the pair, `L(p) = ⟪w₁, p(A) v₁⟫`; its values on the monomials are the
moments `L(x^k) = ⟪w₁, A^k v₁⟫` of [saad2003iterative], §7.1.2. -/
noncomputable def moment (p : 𝕜[X]) : 𝕜 := inner 𝕜 w₁ (Polynomial.aeval A p v₁)

/-- [saad2003iterative], (7.7): the bilinear form `⟨p, q⟩ = (p(A) v₁, q(Aᴴ) w₁)` on `𝕜[X]`. The
conjugation applied to `q` is what makes it bilinear rather than sesquilinear over `ℂ`; over `ℝ`
it is the book's form verbatim. It is an *indefinite* form: `⟨p, p⟩` can vanish on a nonzero `p`,
which is exactly a serious breakdown of the process. -/
noncomputable def polyForm (p q : 𝕜[X]) : 𝕜 :=
  inner 𝕜 (Polynomial.aeval B (q.map (starRingEnd 𝕜)) w₁) (Polynomial.aeval A p v₁)

/-- [saad2003iterative], §7.1.2: the moment matrix `M_k = {⟨x^{i-1}, x^{j-1}⟩}_{i,j=1..k}`. -/
noncomputable def momentMatrix (k : ℕ) : Matrix (Fin k) (Fin k) 𝕜 :=
  Matrix.of fun i j => polyForm A B v₁ w₁ (X ^ (i : ℕ)) (X ^ (j : ℕ))

variable {A B v₁ w₁}

/-- The form of [saad2003iterative], (7.7) is a *moment functional*: `⟨p, q⟩ = L(p q)`. Everything
else about the form follows from this one identity. -/
theorem polyForm_eq_moment (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (p q : 𝕜[X]) :
    polyForm A B v₁ w₁ p q = moment A v₁ w₁ (p * q) := by
  rw [polyForm, inner_aeval_map_eq hB, moment, mul_comm, map_mul, Module.End.mul_apply]

/-- The form of [saad2003iterative], (7.7) is symmetric, `⟨p, q⟩ = ⟨q, p⟩`, because it depends only
on the product `p q`. -/
theorem polyForm_comm (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (p q : 𝕜[X]) :
    polyForm A B v₁ w₁ p q = polyForm A B v₁ w₁ q p := by
  rw [polyForm_eq_moment hB, polyForm_eq_moment hB, mul_comm]

/-- The entries of the moment matrix are the moments: `(M_k)_{ij} = L(x^{i+j})`. -/
theorem momentMatrix_apply (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (k : ℕ) (i j : Fin k) :
    momentMatrix A B v₁ w₁ k i j = moment A v₁ w₁ (X ^ ((i : ℕ) + (j : ℕ))) := by
  rw [momentMatrix, Matrix.of_apply, polyForm_eq_moment hB, ← pow_add]

/-- [saad2003iterative], §7.1.2: the moment matrix is a *Hankel* matrix, constant along
antidiagonals, because `⟨x^i, x^j⟩ = L(x^{i+j})` depends on `i` and `j` only through `i + j`. -/
theorem momentMatrix_apply_eq_of_add_eq (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) {k : ℕ}
    {i j i' j' : Fin k} (h : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ)) :
    momentMatrix A B v₁ w₁ k i j = momentMatrix A B v₁ w₁ k i' j' := by
  rw [momentMatrix_apply hB, momentMatrix_apply hB, h]

/-! #### The polynomials the process computes -/

variable (A B v₁ w₁)

/-- The pair `(p_j, p_{j+1})` of consecutive primal polynomials, as a one-step recursion so that
the equations of `BiLanczos.poly` hold by `rfl`. -/
private noncomputable def polyPair (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 =>
    (1, C (delta A B v₁ w₁ 1)⁻¹ *
      ((X - C (alpha A B v₁ w₁ 0)) * 1 - C (beta A B v₁ w₁ 0) * 0))
  | j + 1 =>
    ((polyPair A B v₁ w₁ j).2,
      C (delta A B v₁ w₁ (j + 2))⁻¹ *
        ((X - C (alpha A B v₁ w₁ (j + 1))) * (polyPair A B v₁ w₁ j).2 -
          C (beta A B v₁ w₁ (j + 1)) * (polyPair A B v₁ w₁ j).1))

/-- The polynomials of the two-sided Lanczos process: `p_0 = 1` and
`δ_{j+1} p_{j+1} = (X - α_j) p_j - β_j p_{j-1}`, so that `p_j(A) v₁ = v_j`
(`BiLanczos.aeval_poly`). The recurrence is divided by `δ_{j+1}` rather than multiplied out, which
makes it hold at every index: past a breakdown the vanishing `δ` inverts to `0` and both `p_j` and
`v_j` are `0`. -/
noncomputable def poly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] := (polyPair A B v₁ w₁ j).1

/-- `p_{j-1}`, with the convention `p_{-1} = 0` matching `BiLanczos.vecPrev`. -/
noncomputable def polyPrev (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X]
  | 0 => 0
  | j + 1 => poly A B v₁ w₁ j

/-- [saad2003iterative], §7.1.2: the polynomial `p̂_j = (X - α_j) p_j - β_j p_{j-1}` with
`p̂_j(A) v₁ = v̂_{j+1}` (`BiLanczos.aeval_vhatPoly`). This is the book's `p_j`, the polynomial whose
indefinite norm `⟨p̂_j, p̂_j⟩` decides whether the process breaks down. -/
noncomputable def vhatPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (X - C (alpha A B v₁ w₁ j)) * poly A B v₁ w₁ j - C (beta A B v₁ w₁ j) * polyPrev A B v₁ w₁ j

@[simp] theorem poly_zero : poly A B v₁ w₁ 0 = 1 := rfl

@[simp] theorem polyPrev_zero : polyPrev A B v₁ w₁ 0 = 0 := rfl

@[simp] theorem polyPrev_succ (j : ℕ) : polyPrev A B v₁ w₁ (j + 1) = poly A B v₁ w₁ j := rfl

/-- The normalization step at the level of polynomials: `p_{j+1} = p̂_j / δ_{j+1}`. -/
theorem poly_succ (j : ℕ) :
    poly A B v₁ w₁ (j + 1) = C (delta A B v₁ w₁ (j + 1))⁻¹ * vhatPoly A B v₁ w₁ j := by
  cases j with
  | zero => rfl
  | succ j => rfl

private theorem aeval_C_mul_apply (T : E →ₗ[𝕜] E) (c : 𝕜) (p : 𝕜[X]) (x : E) :
    Polynomial.aeval T (C c * p) x = c • Polynomial.aeval T p x := by
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]

private theorem aeval_step (T : E →ₗ[𝕜] E) (a b : 𝕜) (p q : 𝕜[X]) (x : E) :
    Polynomial.aeval T ((X - C a) * p - C b * q) x =
      T (Polynomial.aeval T p x) - a • Polynomial.aeval T p x - b • Polynomial.aeval T q x := by
  rw [map_sub, LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    aeval_X, aeval_C, Module.algebraMap_end_apply, aeval_C_mul_apply]

private theorem aeval_poly_aux (j : ℕ) :
    Polynomial.aeval A (poly A B v₁ w₁ j) v₁ = vec A B v₁ w₁ j ∧
      Polynomial.aeval A (polyPrev A B v₁ w₁ j) v₁ = vecPrev A B v₁ w₁ j := by
  induction j with
  | zero => exact ⟨by simp, by simp⟩
  | succ j ih =>
    have hv : Polynomial.aeval A (vhatPoly A B v₁ w₁ j) v₁ = vhat A B v₁ w₁ j := by
      rw [vhatPoly, aeval_step, ih.1, ih.2, vhat_eq]
    exact ⟨by rw [poly_succ, aeval_C_mul_apply, hv, vec_succ],
      by rw [polyPrev_succ, ih.1, vecPrev_succ]⟩

/-- [saad2003iterative], §7.1.2: the Lanczos vectors are polynomials in `A` applied to the starting
vector, `p_j(A) v₁ = v_j`. No hypothesis is needed — past a breakdown both sides are `0`. -/
theorem aeval_poly (j : ℕ) : Polynomial.aeval A (poly A B v₁ w₁ j) v₁ = vec A B v₁ w₁ j :=
  (aeval_poly_aux A B v₁ w₁ j).1

/-- [saad2003iterative], §7.1.2: "there is a polynomial `p_j` of degree `j` such that
`v̂_{j+1} = p_j(A) v₁`". -/
theorem aeval_vhatPoly (j : ℕ) :
    Polynomial.aeval A (vhatPoly A B v₁ w₁ j) v₁ = vhat A B v₁ w₁ j := by
  rw [vhatPoly, aeval_step, aeval_poly, (aeval_poly_aux A B v₁ w₁ j).2, vhat_eq]

/-! #### Degrees -/

private theorem natDegree_step (a b : 𝕜) {p q : 𝕜[X]} {k : ℕ} (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k + 1) : ((X - C a) * p - C b * q).natDegree ≤ k + 1 := by
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans natDegree_mul_le ?_)
    (le_trans natDegree_mul_le ?_))
  · rw [natDegree_X_sub_C]; omega
  · rw [natDegree_C]; omega

private theorem coeff_step (a b : 𝕜) {p q : 𝕜[X]} {k : ℕ} (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k) : ((X - C a) * p - C b * q).coeff (k + 1) = p.coeff k := by
  rw [sub_mul, coeff_sub, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (n := k + 1) (by omega),
    coeff_eq_zero_of_natDegree_lt (n := k + 1) (by omega), mul_zero, mul_zero, sub_zero, sub_zero]

private theorem natDegree_aux (j : ℕ) :
    (poly A B v₁ w₁ j).natDegree ≤ j ∧ (polyPrev A B v₁ w₁ j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hv : (vhatPoly A B v₁ w₁ j).natDegree ≤ j + 1 :=
      natDegree_step _ _ ih.1 (le_trans ih.2 (by omega))
    refine ⟨?_, by rw [polyPrev_succ]; exact le_trans ih.1 (by omega)⟩
    rw [poly_succ]
    exact le_trans natDegree_mul_le (by rw [natDegree_C]; simpa using hv)

/-- `p_j` has degree at most `j`; exactly `j` while the process has not broken down
(`BiLanczos.poly_natDegree`). -/
theorem poly_natDegree_le (j : ℕ) : (poly A B v₁ w₁ j).natDegree ≤ j :=
  (natDegree_aux A B v₁ w₁ j).1

theorem polyPrev_natDegree_le (j : ℕ) : (polyPrev A B v₁ w₁ j).natDegree ≤ j :=
  (natDegree_aux A B v₁ w₁ j).2

/-- `p̂_j` has degree at most `j + 1`. -/
theorem vhatPoly_natDegree_le (j : ℕ) : (vhatPoly A B v₁ w₁ j).natDegree ≤ j + 1 :=
  natDegree_step _ _ (poly_natDegree_le A B v₁ w₁ j)
    (le_trans (polyPrev_natDegree_le A B v₁ w₁ j) (Nat.le_succ j))

/-- The leading coefficient of `p̂_j` is that of `p_j`: multiplying by `X - α_j` shifts it up. -/
theorem vhatPoly_coeff_succ (j : ℕ) :
    (vhatPoly A B v₁ w₁ j).coeff (j + 1) = (poly A B v₁ w₁ j).coeff j :=
  coeff_step _ _ (poly_natDegree_le A B v₁ w₁ j) (polyPrev_natDegree_le A B v₁ w₁ j)

/-- The `j`-th coefficient of `p_j` is the product of the inverted subdiagonal entries. -/
theorem poly_coeff_self (j : ℕ) :
    (poly A B v₁ w₁ j).coeff j = ∏ i ∈ range j, (delta A B v₁ w₁ (i + 1))⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [poly_succ, coeff_C_mul, vhatPoly_coeff_succ, ih, Finset.prod_range_succ]
    ring

variable {A B v₁ w₁}

theorem poly_coeff_self_ne_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (poly A B v₁ w₁ j).coeff j ≠ 0 := by
  rw [poly_coeff_self]
  exact Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero (h.delta_ne_zero i (lt_of_lt_of_le (Finset.mem_range.1 hi) hj))

/-- While the process has not broken down, `p_j` has degree exactly `j`. -/
theorem poly_natDegree {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (poly A B v₁ w₁ j).natDegree = j :=
  le_antisymm (poly_natDegree_le A B v₁ w₁ j)
    (le_natDegree_of_ne_zero (poly_coeff_self_ne_zero h hj))

/-- [saad2003iterative], §7.1.2: the polynomial with `v̂_{j+1} = p̂_j(A) v₁` has degree exactly
`j + 1` while the process has not broken down. -/
theorem vhatPoly_natDegree {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (vhatPoly A B v₁ w₁ j).natDegree = j + 1 :=
  le_antisymm (vhatPoly_natDegree_le A B v₁ w₁ j)
    (le_natDegree_of_ne_zero (by rw [vhatPoly_coeff_succ]; exact poly_coeff_self_ne_zero h hj))

/-! #### The dual polynomials, and the breakdown criterion -/

variable (A B v₁ w₁)

/-- The pair `(p*_j, p*_{j+1})` of consecutive dual polynomials. -/
private noncomputable def dualPolyPair (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 =>
    (1, C (starRingEnd 𝕜 (beta A B v₁ w₁ 1))⁻¹ *
      ((X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ 0))) * 1 -
        C (starRingEnd 𝕜 (delta A B v₁ w₁ 0)) * 0))
  | j + 1 =>
    ((dualPolyPair A B v₁ w₁ j).2,
      C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 2)))⁻¹ *
        ((X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ (j + 1)))) * (dualPolyPair A B v₁ w₁ j).2 -
          C (starRingEnd 𝕜 (delta A B v₁ w₁ (j + 1))) * (dualPolyPair A B v₁ w₁ j).1))

/-- The dual polynomials of the process: `p*_0 = 1` and
`conj β_{j+1} p*_{j+1} = (X - conj α_j) p*_j - conj δ_j p*_{j-1}`, so that `p*_j(Aᴴ) w₁ = w_j`
(`BiLanczos.aeval_dualPoly`). -/
noncomputable def dualPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (dualPolyPair A B v₁ w₁ j).1

/-- `p*_{j-1}`, with the convention `p*_{-1} = 0`. -/
noncomputable def dualPolyPrev (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜[X]
  | 0 => 0
  | j + 1 => dualPoly A B v₁ w₁ j

/-- The dual counterpart of `BiLanczos.vhatPoly`: `p̂*_j(Aᴴ) w₁ = ŵ_{j+1}`. -/
noncomputable def dualVhatPoly (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (j : ℕ) : 𝕜[X] :=
  (X - C (starRingEnd 𝕜 (alpha A B v₁ w₁ j))) * dualPoly A B v₁ w₁ j -
    C (starRingEnd 𝕜 (delta A B v₁ w₁ j)) * dualPolyPrev A B v₁ w₁ j

/-- The scalar `γ_j` of [saad2003iterative], §7.1.2, which relates the dual polynomials to the
primal ones (`BiLanczos.dualVhat_eq_smul`): `γ_0 = 1` and
`γ_{j+1} = γ_j δ_{j+1} / conj β_{j+1}`. -/
noncomputable def dualPolyScalar (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) : ℕ → 𝕜
  | 0 => 1
  | j + 1 => dualPolyScalar A B v₁ w₁ j *
      (delta A B v₁ w₁ (j + 1) / starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))

@[simp] theorem dualPoly_zero : dualPoly A B v₁ w₁ 0 = 1 := rfl

@[simp] theorem dualPolyPrev_zero : dualPolyPrev A B v₁ w₁ 0 = 0 := rfl

@[simp] theorem dualPolyPrev_succ (j : ℕ) :
    dualPolyPrev A B v₁ w₁ (j + 1) = dualPoly A B v₁ w₁ j := rfl

@[simp] theorem dualPolyScalar_zero : dualPolyScalar A B v₁ w₁ 0 = 1 := rfl

theorem dualPolyScalar_succ (j : ℕ) : dualPolyScalar A B v₁ w₁ (j + 1) =
    dualPolyScalar A B v₁ w₁ j *
      (delta A B v₁ w₁ (j + 1) / starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1))) := rfl

theorem dualPoly_succ (j : ℕ) : dualPoly A B v₁ w₁ (j + 1) =
    C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ * dualVhatPoly A B v₁ w₁ j := by
  cases j with
  | zero => rfl
  | succ j => rfl

private theorem aeval_dualPoly_aux (j : ℕ) :
    Polynomial.aeval B (dualPoly A B v₁ w₁ j) w₁ = dualVec A B v₁ w₁ j ∧
      Polynomial.aeval B (dualPolyPrev A B v₁ w₁ j) w₁ = dualVecPrev A B v₁ w₁ j := by
  induction j with
  | zero => exact ⟨by simp, by simp⟩
  | succ j ih =>
    have hv : Polynomial.aeval B (dualVhatPoly A B v₁ w₁ j) w₁ = dualVhat A B v₁ w₁ j := by
      rw [dualVhatPoly, aeval_step, ih.1, ih.2, dualVhat_eq]
    exact ⟨by rw [dualPoly_succ, aeval_C_mul_apply, hv, dualVec_succ],
      by rw [dualPolyPrev_succ, ih.1, dualVecPrev_succ]⟩

/-- The dual vectors are polynomials in `B` applied to `w₁`: `p*_j(Aᴴ) w₁ = w_j`. -/
theorem aeval_dualPoly (j : ℕ) :
    Polynomial.aeval B (dualPoly A B v₁ w₁ j) w₁ = dualVec A B v₁ w₁ j :=
  (aeval_dualPoly_aux A B v₁ w₁ j).1

/-- `p̂*_j(Aᴴ) w₁ = ŵ_{j+1}`. -/
theorem aeval_dualVhatPoly (j : ℕ) :
    Polynomial.aeval B (dualVhatPoly A B v₁ w₁ j) w₁ = dualVhat A B v₁ w₁ j := by
  rw [dualVhatPoly, aeval_step, aeval_dualPoly, (aeval_dualPoly_aux A B v₁ w₁ j).2, dualVhat_eq]

private theorem map_conj_map_conj (p : 𝕜[X]) :
    (p.map (starRingEnd 𝕜)).map (starRingEnd 𝕜) = p :=
  Polynomial.ext fun k => by rw [coeff_map, coeff_map, RCLike.conj_conj]

private theorem dualPolyScalar_step (j : ℕ) :
    (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)))⁻¹ * dualPolyScalar A B v₁ w₁ j =
        dualPolyScalar A B v₁ w₁ (j + 1) * (delta A B v₁ w₁ (j + 1))⁻¹ ∧
      delta A B v₁ w₁ (j + 1) * dualPolyScalar A B v₁ w₁ j =
        dualPolyScalar A B v₁ w₁ (j + 1) * starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) := by
  rcases eq_or_ne (delta A B v₁ w₁ (j + 1)) 0 with hd | hd
  · have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) = 0 := by
      rw [(beta_succ_eq_zero_iff A B v₁ w₁ j).2 ((delta_succ_eq_zero_iff A B v₁ w₁ j).1 hd),
        map_zero]
    rw [dualPolyScalar_succ, hd, hb]
    simp
  · have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
      simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 hd
    rw [dualPolyScalar_succ]
    constructor <;> field_simp

private theorem dualPoly_eq_aux (j : ℕ) :
    dualPoly A B v₁ w₁ j =
        C (dualPolyScalar A B v₁ w₁ j) * (poly A B v₁ w₁ j).map (starRingEnd 𝕜) ∧
      dualVhatPoly A B v₁ w₁ j =
        C (dualPolyScalar A B v₁ w₁ j) * (vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜) := by
  induction j with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [dualVhatPoly, vhatPoly, dualPoly_zero, dualPolyPrev_zero, poly_zero, polyPrev_zero,
      dualPolyScalar_zero, delta_zero, beta_zero]
    simp
  | succ j ih =>
    obtain ⟨hs1, hs2⟩ := dualPolyScalar_step A B v₁ w₁ j
    have hpoly : (poly A B v₁ w₁ (j + 1)).map (starRingEnd 𝕜) =
        C (delta A B v₁ w₁ (j + 1))⁻¹ * (vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜) := by
      rw [poly_succ, Polynomial.map_mul, Polynomial.map_C, map_inv₀, conj_delta]
    have h1 : dualPoly A B v₁ w₁ (j + 1) =
        C (dualPolyScalar A B v₁ w₁ (j + 1)) * (poly A B v₁ w₁ (j + 1)).map (starRingEnd 𝕜) := by
      rw [dualPoly_succ, ih.2, hpoly, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs1]
    refine ⟨h1, ?_⟩
    rw [dualVhatPoly, h1, dualPolyPrev_succ, ih.1, vhatPoly, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_C, polyPrev_succ, conj_delta, mul_sub]
    rw [show C (delta A B v₁ w₁ (j + 1)) *
          (C (dualPolyScalar A B v₁ w₁ j) * (poly A B v₁ w₁ j).map (starRingEnd 𝕜))
        = C (dualPolyScalar A B v₁ w₁ (j + 1)) *
            (C (starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1))) *
              (poly A B v₁ w₁ j).map (starRingEnd 𝕜)) by
      rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hs2]]
    ring

/-- [saad2003iterative], §7.1.2: "the same polynomial intervenes in the equivalent expression of
`ŵ_{j+1}`". There is a scalar `γ_j` — `BiLanczos.dualPolyScalar` — with
`ŵ_{j+1} = γ_j p̄_j(Aᴴ) w₁`, the *conjugate* of the polynomial `p_j` that produces `v̂_{j+1}`; over
`ℝ` the conjugation is invisible and this is the book's statement verbatim. -/
theorem dualVhat_eq_smul (j : ℕ) :
    dualVhat A B v₁ w₁ j = dualPolyScalar A B v₁ w₁ j •
      Polynomial.aeval B ((vhatPoly A B v₁ w₁ j).map (starRingEnd 𝕜)) w₁ := by
  rw [← aeval_dualVhatPoly, (dualPoly_eq_aux A B v₁ w₁ j).2, aeval_C_mul_apply]

/-- [saad2003iterative], §7.1.2: `⟨p_j, p_j⟩ = γ_j (p_j(A) v₁, p_j(Aᴴ) w₁)` — the breakdown scalar
of the process is the indefinite norm of `p_j` up to the factor `γ_j`. -/
theorem zeta_eq_polyForm (j : ℕ) :
    zeta A B v₁ w₁ j = starRingEnd 𝕜 (dualPolyScalar A B v₁ w₁ j) *
      polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) (vhatPoly A B v₁ w₁ j) := by
  rw [zeta, dualVhat_eq_smul, inner_smul_left, polyForm, ← aeval_vhatPoly]

variable {A B v₁ w₁}

/-- The factor `γ_j` does not vanish while the process has not broken down. -/
theorem dualPolyScalar_ne_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    dualPolyScalar A B v₁ w₁ j ≠ 0 := by
  induction j with
  | zero => rw [dualPolyScalar_zero]; exact one_ne_zero
  | succ j ih =>
    have hd : delta A B v₁ w₁ (j + 1) ≠ 0 := h.delta_ne_zero j (by omega)
    have hb : starRingEnd 𝕜 (beta A B v₁ w₁ (j + 1)) ≠ 0 := by
      simpa using (beta_succ_ne_zero_iff A B v₁ w₁ j).2 hd
    rw [dualPolyScalar_succ]
    exact mul_ne_zero (ih (by omega)) (div_ne_zero hd hb)

/-- [saad2003iterative], §7.1.2: **the process breaks down at step `j` exactly when the indefinite
norm of `p_j` vanishes**, `⟨p_j, p_j⟩ = 0`. This is the criterion that separates a serious
breakdown from a lucky one only through the form: `⟨·,·⟩` is indefinite, so `⟨p, p⟩ = 0` does not
force `p(A) v₁ = 0`. -/
theorem delta_succ_eq_zero_iff_polyForm_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j ≤ m) :
    delta A B v₁ w₁ (j + 1) = 0 ↔
      polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) (vhatPoly A B v₁ w₁ j) = 0 := by
  rw [delta_succ_eq_zero_iff, zeta_eq_polyForm]
  refine ⟨fun hc => ?_, fun hc => by rw [hc, mul_zero]⟩
  rcases mul_eq_zero.1 hc with h1 | h2
  · exact absurd (by simpa using h1) (dualPolyScalar_ne_zero h hj)
  · exact h2

/-! #### Orthogonality -/

private theorem inner_dualVec_vhat_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ}
    (hi : i ≤ j) (hj : j < m) : inner 𝕜 (dualVec A B v₁ w₁ i) (vhat A B v₁ w₁ j) = 0 := by
  rw [← smul_vec_succ A B v₁ w₁ (h.delta_ne_zero j hj), inner_smul_right,
    inner_dualVec_vec h (by omega) (by omega), ite_eq_right (by omega), mul_zero]

private theorem inner_eq_zero_of_mem_dualSpan {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j < m) {x : E} (hx : x ∈ Submodule.span 𝕜 (dualVec A B v₁ w₁ '' Set.Iio (j + 1))) :
    inner 𝕜 x (vhat A B v₁ w₁ j) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : i < j + 1 := hi
    exact inner_dualVec_vhat_eq_zero h (by omega) hj
  | zero => rw [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- [saad2003iterative], §7.1.2: `p̂_j` is orthogonal, for the indefinite form (7.7), to every
polynomial of degree below its own. This is the sense in which the two-sided Lanczos process
computes *formal orthogonal polynomials*. -/
theorem polyForm_vhatPoly_eq_zero_of_natDegree_le {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {j : ℕ}
    (hj : j < m) {r : 𝕜[X]} (hr : r.natDegree ≤ j) :
    polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ j) r = 0 := by
  have hle : (r.map (starRingEnd 𝕜)).natDegree ≤ j :=
    le_trans (Polynomial.natDegree_map_le) hr
  have hdeg : (r.map (starRingEnd 𝕜)).degree < ((j + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_of_le hle
  rw [polyForm, aeval_vhatPoly]
  refine inner_eq_zero_of_mem_dualSpan h hj ?_
  rw [span_dualVec (h.mono (by omega))]
  exact Krylov.aeval_apply_mem_subspace B w₁ hdeg

/-- [saad2003iterative], §7.1.2: the polynomials `p̂_j` are pairwise orthogonal for the indefinite
form (7.7). -/
theorem polyForm_vhatPoly_eq_zero {m : ℕ} (h : NoBreakdown A B v₁ w₁ m) {i j : ℕ} (hi : i < m)
    (hj : j < m) (hij : i ≠ j) :
    polyForm A B v₁ w₁ (vhatPoly A B v₁ w₁ i) (vhatPoly A B v₁ w₁ j) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · rw [polyForm_comm h.adjoint]
    exact polyForm_vhatPoly_eq_zero_of_natDegree_le h hj
      (le_trans (vhatPoly_natDegree_le A B v₁ w₁ i) (by omega))
  · exact polyForm_vhatPoly_eq_zero_of_natDegree_le h hi
      (le_trans (vhatPoly_natDegree_le A B v₁ w₁ j) (by omega))

end FormalOrthogonalPolynomials

end BiLanczos

/-! ### The biconjugate gradient algorithm -/

namespace BCG

/-- State of the biconjugate gradient iteration ([saad2003iterative], Alg 7.3). -/
@[ext]
structure State (E : Type*) where
  /-- The iterate `x_k`. -/
  x : E
  /-- The residual `r_k = b - A x_k`. -/
  r : E
  /-- The shadow residual `r*_k`. -/
  rs : E
  /-- The search direction `p_k`. -/
  p : E
  /-- The shadow direction `p*_k`. -/
  ps : E

/-- The BCG step length `⟪r*, r⟫ / ⟪p*, A p⟫`, which is [saad2003iterative] `(r_j, r*_j)/(A p_j,
p*_j)` read in Mathlib's convention, where the inner product is conjugate-linear in its *first*
argument. -/
noncomputable def stepAlpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.rs s.r / inner 𝕜 s.ps (A s.p)

/-- One step of [saad2003iterative], Alg 7.3, with `B` the adjoint of `A`. -/
noncomputable def step (A B : E →ₗ[𝕜] E) (s : State E) : State E :=
  let a := stepAlpha A s
  let r' := s.r - a • A s.p
  let rs' := s.rs - starRingEnd 𝕜 a • B s.ps
  let c : 𝕜 := inner 𝕜 rs' r' / inner 𝕜 s.rs s.r
  { x := s.x + a • s.p
    r := r'
    rs := rs'
    p := r' + c • s.p
    ps := rs' + starRingEnd 𝕜 c • s.ps }

/-- The `k`-th BCG state, started from `x₀` with the shadow residual `rs₀`. -/
noncomputable def iterate (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (k : ℕ) : State E :=
  (step A B)^[k] { x := x₀, r := b - A x₀, rs := rs₀, p := b - A x₀, ps := rs₀ }

section Recurrence

variable (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E)

/-- The BCG residual `r_k`. -/
noncomputable def residual (k : ℕ) : E := (iterate A B b x₀ rs₀ k).r

/-- The BCG shadow residual `r*_k`, the residual of the transposed system. -/
noncomputable def dualResidual (k : ℕ) : E := (iterate A B b x₀ rs₀ k).rs

/-- The BCG search direction `p_k`. -/
noncomputable def direction (k : ℕ) : E := (iterate A B b x₀ rs₀ k).p

/-- The BCG shadow direction `p*_k`. -/
noncomputable def dualDirection (k : ℕ) : E := (iterate A B b x₀ rs₀ k).ps

/-- The BCG step length `α_k = ⟪r*_k, r_k⟫ / ⟪p*_k, A p_k⟫`. -/
noncomputable def alpha (k : ℕ) : 𝕜 :=
  inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) /
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k))

/-- The BCG direction update coefficient `β_k = ⟪r*_{k+1}, r_{k+1}⟫ / ⟪r*_k, r_k⟫`. -/
noncomputable def beta (k : ℕ) : 𝕜 :=
  inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ (k + 1)) /
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k)

/-- The recurrence: state `k + 1` is one `BCG.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A B b x₀ rs₀ (k + 1) = step A B (iterate A B b x₀ rs₀ k) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem iterate_zero_x : (iterate A B b x₀ rs₀ 0).x = x₀ := rfl

@[simp] theorem residual_zero : residual A B b x₀ rs₀ 0 = b - A x₀ := rfl

@[simp] theorem dualResidual_zero : dualResidual A B b x₀ rs₀ 0 = rs₀ := rfl

@[simp] theorem direction_zero : direction A B b x₀ rs₀ 0 = b - A x₀ := rfl

@[simp] theorem dualDirection_zero : dualDirection A B b x₀ rs₀ 0 = rs₀ := rfl

/-- `x_{k+1} = x_k + α_k p_k` ([saad2003iterative], Alg 7.3, line 5). -/
theorem iterate_succ_x (k : ℕ) : (iterate A B b x₀ rs₀ (k + 1)).x =
    (iterate A B b x₀ rs₀ k).x + alpha A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- `r_{k+1} = r_k - α_k A p_k` ([saad2003iterative], Alg 7.3, line 6). -/
theorem residual_succ (k : ℕ) : residual A B b x₀ rs₀ (k + 1) =
    residual A B b x₀ rs₀ k - alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k) := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- `r*_{k+1} = r*_k - conj α_k Aᴴ p*_k` ([saad2003iterative], Alg 7.3, line 7). -/
theorem dualResidual_succ (k : ℕ) : dualResidual A B b x₀ rs₀ (k + 1) =
    dualResidual A B b x₀ rs₀ k -
      starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) • B (dualDirection A B b x₀ rs₀ k) := by
  simp only [alpha, residual, dualResidual, direction, dualDirection, iterate_succ]
  rfl

/-- `p_{k+1} = r_{k+1} + β_k p_k` ([saad2003iterative], Alg 7.3, line 9). -/
theorem direction_succ (k : ℕ) : direction A B b x₀ rs₀ (k + 1) =
    residual A B b x₀ rs₀ (k + 1) + beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  simp only [beta, residual, dualResidual, direction, iterate_succ]
  rfl

/-- `p*_{k+1} = r*_{k+1} + conj β_k p*_k` ([saad2003iterative], Alg 7.3, line 10). -/
theorem dualDirection_succ (k : ℕ) : dualDirection A B b x₀ rs₀ (k + 1) =
    dualResidual A B b x₀ rs₀ (k + 1) +
      starRingEnd 𝕜 (beta A B b x₀ rs₀ k) • dualDirection A B b x₀ rs₀ k := by
  simp only [beta, residual, dualResidual, dualDirection, iterate_succ]
  rfl

/-! #### Three-term recurrences ([saad2003iterative], P-7.7)

Eliminating the direction vectors from the coupled two-term recurrences leaves a three-term
recurrence for the residuals alone, and eliminating the residuals leaves one for the directions.
The direction recurrence is unconditional; the residual one divides by `α_k`, so its closed form
carries `α_k ≠ 0` and `BCG.alpha_smul_residual_add_two` is the division-free identity behind it. -/

/-- The division-free form of the residual three-term recurrence ([saad2003iterative], P-7.7):
`α_k r_{k+2} = (α_k + α_{k+1} β_k) r_{k+1} - α_k α_{k+1} A r_{k+1} - α_{k+1} β_k r_k`. It holds at
every step, breakdown included. -/
theorem alpha_smul_residual_add_two (k : ℕ) :
    alpha A B b x₀ rs₀ k • residual A B b x₀ rs₀ (k + 2) =
      (alpha A B b x₀ rs₀ k + alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ (k + 1) -
        (alpha A B b x₀ rs₀ k * alpha A B b x₀ rs₀ (k + 1)) •
          A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) • residual A B b x₀ rs₀ k := by
  have h2 : residual A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 1) -
      alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) :=
    residual_succ A B b x₀ rs₀ (k + 1)
  have h3 : direction A B b x₀ rs₀ (k + 1) =
      residual A B b x₀ rs₀ (k + 1) + beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k :=
    direction_succ A B b x₀ rs₀ k
  have hX : alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k) =
      residual A B b x₀ rs₀ k - residual A B b x₀ rs₀ (k + 1) := by
    rw [residual_succ A B b x₀ rs₀ k]; abel
  have expand : alpha A B b x₀ rs₀ k • (residual A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • (A (residual A B b x₀ rs₀ (k + 1)) +
          beta A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k))) =
      alpha A B b x₀ rs₀ k • residual A B b x₀ rs₀ (k + 1) -
        (alpha A B b x₀ rs₀ k * alpha A B b x₀ rs₀ (k + 1)) •
          A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k) •
          (alpha A B b x₀ rs₀ k • A (direction A B b x₀ rs₀ k)) := by
    module
  rw [h2, h3, map_add, map_smul, expand, hX]
  module

/-- The residual three-term recurrence of [saad2003iterative], P-7.7:
`r_{k+2} = (1 + α_{k+1} β_k/α_k) r_{k+1} - α_{k+1} A r_{k+1} - (α_{k+1} β_k/α_k) r_k`, started
from `r_0 = b - A x_0` and `r_1 = r_0 - α_0 A r_0` (`BCG.residual_zero`, `BCG.residual_one`). -/
theorem residual_add_two {k : ℕ} (hk : alpha A B b x₀ rs₀ k ≠ 0) :
    residual A B b x₀ rs₀ (k + 2) =
      (1 + alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k / alpha A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • A (residual A B b x₀ rs₀ (k + 1)) -
        (alpha A B b x₀ rs₀ (k + 1) * beta A B b x₀ rs₀ k / alpha A B b x₀ rs₀ k) •
          residual A B b x₀ rs₀ k := by
  refine smul_right_injective E hk ?_
  dsimp only
  rw [alpha_smul_residual_add_two]
  match_scalars <;> field_simp

/-- `r_1 = r_0 - α_0 A r_0`: the second residual, which starts the three-term recurrence
`BCG.residual_add_two`. -/
theorem residual_one : residual A B b x₀ rs₀ 1 =
    residual A B b x₀ rs₀ 0 - alpha A B b x₀ rs₀ 0 • A (residual A B b x₀ rs₀ 0) := by
  rw [residual_succ, direction_zero, residual_zero]

/-- The direction three-term recurrence of [saad2003iterative], P-7.7:
`p_{k+2} = (1 + β_{k+1}) p_{k+1} - α_{k+1} A p_{k+1} - β_k p_k`, started from `p_0 = b - A x_0`
and `p_1 = (1 + β_0) p_0 - α_0 A p_0` (`BCG.direction_zero`, `BCG.direction_one`). Unlike the
residual recurrence this one needs no hypothesis. -/
theorem direction_add_two (k : ℕ) :
    direction A B b x₀ rs₀ (k + 2) =
      (1 + beta A B b x₀ rs₀ (k + 1)) • direction A B b x₀ rs₀ (k + 1) -
        alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) -
        beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
  have h1 : direction A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 2) +
      beta A B b x₀ rs₀ (k + 1) • direction A B b x₀ rs₀ (k + 1) :=
    direction_succ A B b x₀ rs₀ (k + 1)
  have h2 : residual A B b x₀ rs₀ (k + 2) = residual A B b x₀ rs₀ (k + 1) -
      alpha A B b x₀ rs₀ (k + 1) • A (direction A B b x₀ rs₀ (k + 1)) :=
    residual_succ A B b x₀ rs₀ (k + 1)
  have h3 : residual A B b x₀ rs₀ (k + 1) = direction A B b x₀ rs₀ (k + 1) -
      beta A B b x₀ rs₀ k • direction A B b x₀ rs₀ k := by
    rw [direction_succ A B b x₀ rs₀ k]; abel
  rw [h1, h2, h3]
  module

/-- `p_1 = (1 + β_0) p_0 - α_0 A p_0`: the second direction, which starts the three-term
recurrence `BCG.direction_add_two`. -/
theorem direction_one : direction A B b x₀ rs₀ 1 =
    (1 + beta A B b x₀ rs₀ 0) • direction A B b x₀ rs₀ 0 -
      alpha A B b x₀ rs₀ 0 • A (direction A B b x₀ rs₀ 0) := by
  rw [direction_succ, residual_succ, direction_zero, residual_zero]
  module

/-- The state's residual field is the true residual. -/
theorem residual_eq (k : ℕ) :
    residual A B b x₀ rs₀ k = b - A (iterate A B b x₀ rs₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [residual_succ, iterate_succ_x, ih, map_add, map_smul, sub_sub, direction]

/-- Telescoping the shadow recurrence: `α_k ⟪p*_k, A y⟫ = ⟪r*_k, y⟫ - ⟪r*_{k+1}, y⟫`, the only way
`B` enters the shadow residuals. -/
theorem mul_inner_dualDirection_apply (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) (k : ℕ)
    (y : E) :
    alpha A B b x₀ rs₀ k * inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A y) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ k) y -
        inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) y := by
  rw [dualResidual_succ, inner_sub_left, inner_smul_left, RCLike.conj_conj,
    BiLanczos.inner_apply_eq hB]
  ring

/-- Telescoping the residual recurrence: `α_k ⟪y, A p_k⟫ = ⟪y, r_k⟫ - ⟪y, r_{k+1}⟫`. -/
theorem mul_inner_apply_direction (k : ℕ) (y : E) :
    alpha A B b x₀ rs₀ k * inner 𝕜 y (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 y (residual A B b x₀ rs₀ k) - inner 𝕜 y (residual A B b x₀ rs₀ (k + 1)) := by
  rw [residual_succ, inner_sub_right, inner_smul_right]
  ring

private theorem mem_subspace_aux (k : ℕ) :
    residual A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) ∧
      direction A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) := by
  induction k with
  | zero =>
    exact ⟨Krylov.self_mem_subspace _ _ Nat.one_pos, Krylov.self_mem_subspace _ _ Nat.one_pos⟩
  | succ k ih =>
    have hmono := Krylov.subspace_mono A (b - A x₀) (Nat.le_succ (k + 1))
    have hr : residual A B b x₀ rs₀ (k + 1) ∈ Krylov.subspace A (b - A x₀) (k + 1 + 1) := by
      rw [residual_succ]
      exact Submodule.sub_mem _ (hmono ih.1) (Submodule.smul_mem _ _
        (Krylov.map_subspace_le A (b - A x₀) (k + 1) ⟨_, ih.2, rfl⟩))
    refine ⟨hr, ?_⟩
    rw [direction_succ]
    exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ih.2))

/-- `r_k ∈ 𝒦_{k+1}(A, r₀)`. -/
theorem residual_mem_subspace (k : ℕ) :
    residual A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) :=
  (mem_subspace_aux A B b x₀ rs₀ k).1

/-- `p_k ∈ 𝒦_{k+1}(A, r₀)`. -/
theorem direction_mem_subspace (k : ℕ) :
    direction A B b x₀ rs₀ k ∈ Krylov.subspace A (b - A x₀) (k + 1) :=
  (mem_subspace_aux A B b x₀ rs₀ k).2

/-- The BCG iterate lies in the affine Krylov space `x₀ + 𝒦_m(A, r₀)`. -/
theorem iterate_x_sub_mem (m : ℕ) :
    (iterate A B b x₀ rs₀ m).x - x₀ ∈ Krylov.subspace A (b - A x₀) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (iterate A B b x₀ rs₀ (m + 1)).x - x₀ =
        ((iterate A B b x₀ rs₀ m).x - x₀) +
          alpha A B b x₀ rs₀ m • direction A B b x₀ rs₀ m := by
      rw [iterate_succ_x]; abel
    rw [hsplit]
    exact Submodule.add_mem _ (Krylov.subspace_mono A (b - A x₀) (Nat.le_succ m) ih)
      (Submodule.smul_mem _ _ (direction_mem_subspace A B b x₀ rs₀ m))

end Recurrence

/-! #### Biorthogonality of the biconjugate gradient sequences -/

section Biorthogonality

variable {A B : E →ₗ[𝕜] E} {b x₀ rs₀ : E}

/-- The biconjugate gradient iteration runs without breakdown through step `m`: `B` is the adjoint
of `A`, and neither denominator of [saad2003iterative], Alg 7.3 vanishes before step `m`. -/
structure NoBreakdown (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (m : ℕ) : Prop where
  /-- `B` is the adjoint of `A`. -/
  adjoint : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)
  /-- The numerator of `α_k` does not vanish. -/
  inner_residual_ne_zero : ∀ k < m,
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) ≠ 0
  /-- The denominator of `α_k` does not vanish. -/
  inner_apply_direction_ne_zero : ∀ k < m,
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) ≠ 0

/-- Running without breakdown for `m` steps includes running without breakdown for fewer. -/
theorem NoBreakdown.mono {m n : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) (hnm : n ≤ m) :
    NoBreakdown A B b x₀ rs₀ n :=
  ⟨h.adjoint, fun k hk => h.inner_residual_ne_zero k (hk.trans_le hnm),
    fun k hk => h.inner_apply_direction_ne_zero k (hk.trans_le hnm)⟩

/-- Without breakdown the step lengths are nonzero, both parts of the quotient being nonzero. -/
theorem NoBreakdown.alpha_ne_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ} (hk : k < m) :
    alpha A B b x₀ rs₀ k ≠ 0 :=
  div_ne_zero (h.inner_residual_ne_zero k hk) (h.inner_apply_direction_ne_zero k hk)

/-- The invariant of [saad2003iterative], Prop 7.2 up to step `m`: the residuals are biorthogonal
and the directions are `A`-biconjugate. -/
private def Biorth (A B : E →ₗ[𝕜] E) (b x₀ rs₀ : E) (m : ℕ) : Prop :=
  (∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ i) = 0) ∧
    ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ i)) = 0

private theorem inner_dualResidual_apply_direction_of_lt {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {j l : ℕ} (hj : j ≤ m) (hl : l ≤ m) (hjl : j < l) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ l)) = 0 := by
  cases j with
  | zero => exact hP.2 l hl 0 hj (by omega)
  | succ n =>
    have hrs : dualResidual A B b x₀ rs₀ (n + 1) =
        dualDirection A B b x₀ rs₀ (n + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ n) • dualDirection A B b x₀ rs₀ n := by
      rw [dualDirection_succ]; abel
    rw [hrs, inner_sub_left, inner_smul_left, RCLike.conj_conj,
      hP.2 l hl (n + 1) hj (by omega), hP.2 l hl n (by omega) (by omega)]
    ring

private theorem inner_dualDirection_apply_residual_of_lt {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {j l : ℕ} (hj : j ≤ m) (hl : l ≤ m) (hjl : j < l) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ l) (A (residual A B b x₀ rs₀ j)) = 0 := by
  cases j with
  | zero => exact hP.2 0 hj l hl (by omega)
  | succ n =>
    have hr : residual A B b x₀ rs₀ (n + 1) =
        direction A B b x₀ rs₀ (n + 1) - beta A B b x₀ rs₀ n • direction A B b x₀ rs₀ n := by
      rw [direction_succ]; abel
    rw [hr, map_sub, map_smul, inner_sub_right, inner_smul_right,
      hP.2 (n + 1) hj l hl (by omega), hP.2 n (by omega) l hl (by omega)]
    ring

private theorem inner_dualResidual_apply_direction_self {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {k : ℕ} (hk : k ≤ m) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) := by
  cases k with
  | zero => rfl
  | succ n =>
    rw [dualDirection_succ, inner_add_left, inner_smul_left, RCLike.conj_conj,
      hP.2 (n + 1) hk n (by omega) (by omega)]
    ring

private theorem inner_dualDirection_apply_residual_self {m : ℕ} (hP : Biorth A B b x₀ rs₀ m)
    {k : ℕ} (hk : k ≤ m) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (residual A B b x₀ rs₀ k)) =
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) := by
  cases k with
  | zero => rfl
  | succ n =>
    rw [direction_succ, map_add, map_smul, inner_add_right, inner_smul_right,
      hP.2 n (by omega) (n + 1) hk (by omega)]
    ring

private theorem biorth_succ {k : ℕ} (h : NoBreakdown A B b x₀ rs₀ (k + 1))
    (hP : Biorth A B b x₀ rs₀ k) : Biorth A B b x₀ rs₀ (k + 1) := by
  have hn : inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) ≠ 0 :=
    h.inner_residual_ne_zero k (Nat.lt_succ_self k)
  have hd : inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) ≠ 0 :=
    h.inner_apply_direction_ne_zero k (Nat.lt_succ_self k)
  have hαk : alpha A B b x₀ rs₀ k *
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k)) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ k) (residual A B b x₀ rs₀ k) := div_mul_cancel₀ _ hd
  have hX : alpha A B b x₀ rs₀ k * (beta A B b x₀ rs₀ k *
      inner 𝕜 (dualDirection A B b x₀ rs₀ k) (A (direction A B b x₀ rs₀ k))) =
      inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ (k + 1)) := by
    rw [alpha, beta]
    field_simp
  have step1 : ∀ j ≤ k,
      inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ (k + 1)) = 0 := by
    intro j hj
    rw [residual_succ, inner_sub_right, inner_smul_right]
    rcases eq_or_lt_of_le hj with rfl | hjk
    · rw [inner_dualResidual_apply_direction_self hP le_rfl, hαk, sub_self]
    · rw [hP.1 k le_rfl j hj (by omega),
        inner_dualResidual_apply_direction_of_lt hP hj le_rfl hjk]
      ring
  have step2 : ∀ i ≤ k,
      inner 𝕜 (dualResidual A B b x₀ rs₀ (k + 1)) (residual A B b x₀ rs₀ i) = 0 := by
    intro i hi
    have hmul := mul_inner_dualDirection_apply A B b x₀ rs₀ h.adjoint k
      (residual A B b x₀ rs₀ i)
    rcases eq_or_lt_of_le hi with rfl | hik
    · rw [inner_dualDirection_apply_residual_self hP le_rfl, hαk] at hmul
      linear_combination hmul
    · rw [hP.1 i hi k le_rfl (by omega),
        inner_dualDirection_apply_residual_of_lt hP hi le_rfl hik] at hmul
      linear_combination hmul
  have step3 : ∀ j ≤ k,
      inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ (k + 1))) = 0 := by
    intro j hj
    have hαj : alpha A B b x₀ rs₀ j ≠ 0 := h.alpha_ne_zero (by omega)
    have hmul := mul_inner_dualDirection_apply A B b x₀ rs₀ h.adjoint j
      (residual A B b x₀ rs₀ (k + 1))
    rw [direction_succ, map_add, map_smul, inner_add_right, inner_smul_right]
    rcases eq_or_lt_of_le hj with rfl | hjk
    · rw [step1 j le_rfl] at hmul
      refine mul_left_cancel₀ hαj ?_
      linear_combination hmul + hX
    · rw [step1 j hj, step1 (j + 1) (by omega)] at hmul
      rw [hP.2 k le_rfl j hj (by omega)]
      refine mul_left_cancel₀ hαj ?_
      linear_combination hmul
  have step4 : ∀ i ≤ k,
      inner 𝕜 (dualDirection A B b x₀ rs₀ (k + 1)) (A (direction A B b x₀ rs₀ i)) = 0 := by
    intro i hi
    have hαi : alpha A B b x₀ rs₀ i ≠ 0 := h.alpha_ne_zero (by omega)
    have hmul := mul_inner_apply_direction A B b x₀ rs₀ i (dualResidual A B b x₀ rs₀ (k + 1))
    rw [dualDirection_succ, inner_add_left, inner_smul_left, RCLike.conj_conj]
    rcases eq_or_lt_of_le hi with rfl | hik
    · rw [step2 i le_rfl] at hmul
      refine mul_left_cancel₀ hαi ?_
      linear_combination hmul + hX
    · rw [step2 i hi, step2 (i + 1) (by omega)] at hmul
      rw [hP.2 i hi k le_rfl (by omega)]
      refine mul_left_cancel₀ hαi ?_
      linear_combination hmul
  refine ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩
  · by_cases hi' : i = k + 1
    · subst hi'
      exact step1 j (by omega)
    · by_cases hj' : j = k + 1
      · subst hj'
        exact step2 i (by omega)
      · exact hP.1 i (by omega) j (by omega) hij
  · by_cases hi' : i = k + 1
    · subst hi'
      exact step3 j (by omega)
    · by_cases hj' : j = k + 1
      · subst hj'
        exact step4 i (by omega)
      · exact hP.2 i (by omega) j (by omega) hij

private theorem biorth {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) : Biorth A B b x₀ rs₀ m := by
  induction m with
  | zero =>
    refine ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩ <;>
      · obtain rfl : i = 0 := Nat.le_zero.1 hi
        obtain rfl : j = 0 := Nat.le_zero.1 hj
        exact absurd rfl hij
  | succ m ih => exact biorth_succ h (ih (h.mono (Nat.le_succ m)))

/-- [saad2003iterative], Prop 7.2: the BCG residuals are biorthogonal, `⟪r*_j, r_i⟫ = 0` for `i ≠
j`. -/
theorem inner_residual_dualResidual_eq_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {i j : ℕ}
    (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) :
    inner 𝕜 (dualResidual A B b x₀ rs₀ j) (residual A B b x₀ rs₀ i) = 0 :=
  (biorth h).1 i hi j hj hij

/-- [saad2003iterative], Prop 7.2: the BCG directions are `A`-biconjugate, `⟪p*_j, A p_i⟫ = 0` for
`i ≠ j`. -/
theorem inner_dualDirection_apply_direction_eq_zero {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m)
    {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) :
    inner 𝕜 (dualDirection A B b x₀ rs₀ j) (A (direction A B b x₀ rs₀ i)) = 0 :=
  (biorth h).2 i hi j hj hij

/-! #### BCG as a Petrov–Galerkin method -/

private theorem apply_dualDirection_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ}
    (hk : k < m) : B (dualDirection A B b x₀ rs₀ k) ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (k + 2)) := by
  have hα : starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) ≠ 0 := by
    simpa using h.alpha_ne_zero hk
  have hsub : dualResidual A B b x₀ rs₀ k - dualResidual A B b x₀ rs₀ (k + 1) =
      starRingEnd 𝕜 (alpha A B b x₀ rs₀ k) • B (dualDirection A B b x₀ rs₀ k) := by
    rw [dualResidual_succ]; abel
  have key : B (dualDirection A B b x₀ rs₀ k) =
      (starRingEnd 𝕜 (alpha A B b x₀ rs₀ k))⁻¹ •
        (dualResidual A B b x₀ rs₀ k - dualResidual A B b x₀ rs₀ (k + 1)) := by
    rw [hsub, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.subset_span ⟨k, by simp, rfl⟩) (Submodule.subset_span ⟨k + 1, by simp, rfl⟩))

private theorem apply_dualResidual_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {k : ℕ}
    (hk : k < m) : B (dualResidual A B b x₀ rs₀ k) ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (k + 2)) := by
  cases k with
  | zero => exact apply_dualDirection_mem_span h hk
  | succ n =>
    have hrs : dualResidual A B b x₀ rs₀ (n + 1) =
        dualDirection A B b x₀ rs₀ (n + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ n) • dualDirection A B b x₀ rs₀ n := by
      rw [dualDirection_succ]; abel
    rw [hrs, map_sub, map_smul]
    refine Submodule.sub_mem _ (apply_dualDirection_mem_span h hk) (Submodule.smul_mem _ _ ?_)
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
      (apply_dualDirection_mem_span h (by omega))

private theorem pow_apply_mem_dualSpan {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {i : ℕ}
    (hi : i < m) : (B ^ i) rs₀ ∈
      Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 1)) := by
  induction i with
  | zero =>
    have h0 : (B ^ 0) rs₀ = dualResidual A B b x₀ rs₀ 0 := by simp
    rw [h0]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ i ih =>
    have hpow : (B ^ (i + 1)) rs₀ = B ((B ^ i) rs₀) := by rw [pow_succ']; rfl
    have hmap : Submodule.map B
        (Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 1))) ≤
          Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio (i + 2)) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      have hj' : j < i + 1 := hj
      exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
        (apply_dualResidual_mem_span h (by omega))
    rw [hpow]
    exact hmap ⟨_, ih (by omega), rfl⟩

/-- The shadow Krylov space is spanned by the shadow residuals, which is what makes the BCG residual
orthogonal to all of it. -/
theorem subspace_le_span_dualResidual {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    Krylov.subspace B rs₀ m ≤ Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio m) := by
  rw [Krylov.subspace_eq_span_image_Iio, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i < m := hi
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
    (pow_apply_mem_dualSpan h hi')

private theorem inner_eq_zero_of_mem_span {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Submodule.span 𝕜 (dualResidual A B b x₀ rs₀ '' Set.Iio m)) :
    inner 𝕜 u (residual A B b x₀ rs₀ m) = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j < m := hj
    exact inner_residual_dualResidual_eq_zero h le_rfl (le_of_lt hj') (by omega)
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- The BCG residual is orthogonal to the whole shadow Krylov space, `⟪u, r_m⟫ = 0` for every `u ∈
𝒦_m(B, r*₀)`.  This is the biorthogonality of [saad2003iterative], Prop 7.2 in the form the
polynomial arguments of the transpose-free variants use it: the shadow residuals span that
subspace, so nothing beyond `⟪r*_i, r_m⟫ = 0` for `i < m` is involved. -/
theorem inner_residual_eq_zero_of_mem_subspace {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Krylov.subspace B rs₀ m) : inner 𝕜 u (residual A B b x₀ rs₀ m) = 0 :=
  inner_eq_zero_of_mem_span h (subspace_le_span_dualResidual h hu)

/-- The shadow residuals lie in the span of the shadow directions: `r*_0 = p*_0` and `r*_{k+1} =
p*_{k+1} - conj β_k p*_k`. -/
private theorem dualResidual_mem_span_dualDirection (k : ℕ) :
    dualResidual A B b x₀ rs₀ k ∈
      Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio (k + 1)) := by
  cases k with
  | zero => exact Submodule.subset_span ⟨0, by simp, rfl⟩
  | succ j =>
    have hrs : dualResidual A B b x₀ rs₀ (j + 1) =
        dualDirection A B b x₀ rs₀ (j + 1) -
          starRingEnd 𝕜 (beta A B b x₀ rs₀ j) • dualDirection A B b x₀ rs₀ j := by
      rw [dualDirection_succ]; abel
    rw [hrs]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨j + 1, by simp, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, by simp, rfl⟩))

/-- The shadow Krylov space is spanned by the shadow directions as well: the two families are
related by a triangular change of basis. -/
theorem subspace_le_span_dualDirection {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    Krylov.subspace B rs₀ m ≤ Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio m) := by
  refine (subspace_le_span_dualResidual h).trans ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < m := hj
  exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
    (dualResidual_mem_span_dualDirection j)

private theorem inner_apply_direction_eq_zero_of_mem_span {m : ℕ}
    (h : NoBreakdown A B b x₀ rs₀ m) {u : E}
    (hu : u ∈ Submodule.span 𝕜 (dualDirection A B b x₀ rs₀ '' Set.Iio m)) :
    inner 𝕜 u (A (direction A B b x₀ rs₀ m)) = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j < m := hj
    exact inner_dualDirection_apply_direction_eq_zero h le_rfl (le_of_lt hj') (by omega)
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- `A p_m` is orthogonal to the whole shadow Krylov space, `⟪u, A p_m⟫ = 0` for every `u ∈ 𝒦_m(B,
r*₀)`: the `A`-biconjugacy of [saad2003iterative], Prop 7.2 against the subspace rather than against
the individual shadow directions. -/
theorem inner_apply_direction_eq_zero_of_mem_subspace {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m)
    {u : E} (hu : u ∈ Krylov.subspace B rs₀ m) :
    inner 𝕜 u (A (direction A B b x₀ rs₀ m)) = 0 :=
  inner_apply_direction_eq_zero_of_mem_span h (subspace_le_span_dualDirection h hu)

/-- [saad2003iterative], Prop 7.2: the BCG iterate is the Petrov–Galerkin iterate with `K = 𝒦_m(A,
r₀)` and `L = 𝒦_m(Aᴴ, r*₀)`. -/
theorem isPetrovGalerkin {m : ℕ} (h : NoBreakdown A B b x₀ rs₀ m) :
    IsPetrovGalerkin A b x₀ (Krylov.subspace A (b - A x₀) m) (Krylov.subspace B rs₀ m)
      (iterate A B b x₀ rs₀ m).x where
  mem := iterate_x_sub_mem A B b x₀ rs₀ m
  orth := (Submodule.mem_orthogonal _ _).2 fun u hu => by
    rw [← residual_eq]
    exact inner_eq_zero_of_mem_span h (subspace_le_span_dualResidual h hu)

end Biorthogonality

end BCG

/-! ### The quasi-minimal residual method

QMR minimizes the *quasi-residual*, the coordinate vector of the residual in the two-sided Lanczos
basis, rather than the residual itself; because the basis is not orthonormal the two differ, and the
price is the conditioning of `V_{m+1}` ([saad2003iterative], §7.3). -/

open BiLanczos

namespace QMR

private theorem range_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun j : Fin m => f (j : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- The quasi-residual `β e₁ - T̄_m y` of the two-sided Lanczos relation ([saad2003iterative],
(7.13)): the coordinate vector, in the basis `v_0, …, v_m`, of the residual of `x₀ + V_m y` when `b
- A x₀ = β v₁`. -/
noncomputable def quasiResidual (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    EuclideanSpace 𝕜 (Fin (m + 1)) :=
  WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
    (Krylov.hessenbergOf (BiLanczos.coeff A B v₁ w₁) m).mulVec y)

/-- `QMR.quasiResidual` unfolded: the coordinate vector `β e₁ - T̄_m y` read in `ℓ²`. -/
theorem quasiResidual_def (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    quasiResidual A B v₁ w₁ β m y = WithLp.toLp 2 (Krylov.firstVec β (m + 1) -
      (Krylov.hessenbergOf (BiLanczos.coeff A B v₁ w₁) m).mulVec y) := rfl

variable {A B : E →ₗ[𝕜] E} {v₁ w₁ : E}

/-- The quasi-minimal-residual specification ([saad2003iterative], (7.15)–(7.17)): `x` is `x₀ + V_m
y` for a coordinate vector `y` minimizing the quasi-residual `‖β e₁ - T̄_m y‖`, where `b - A x₀ = β
v₁`. Replacing the true residual `‖V_{m+1} (β e₁ - T̄_m y)‖` by the norm of its coordinate vector
turns the step into a small least-squares problem; the price is the factor `κ₂(V_{m+1})` of
`QMR.norm_residual_le`. -/
def IsQuasiMinResidual (A B : E →ₗ[𝕜] E) (v₁ w₁ : E) (β : 𝕜) (x₀ : E) (m : ℕ) (x : E) : Prop :=
  ∃ y : Fin m → 𝕜, x = x₀ + ∑ j, y j • BiLanczos.vec A B v₁ w₁ (j : ℕ) ∧
    IsMinOn (fun z => ‖quasiResidual A B v₁ w₁ β m z‖) Set.univ y

/-- [saad2003iterative], Prop 7.3: the true residual of a point of `x₀ + 𝒦_m` is at most `‖V_{m+1}‖`
times its quasi-residual. The bound `C` on the coordinate map is a hypothesis because in an abstract
inner product space there is no matrix to take a norm of; for `E = 𝕜^n` it is the largest singular
value of `V_{m+1}`. -/
theorem norm_residual_le_norm_quasiResidual (h : NoSeriousBreakdown A B v₁ w₁) {b x₀ : E}
    {β : 𝕜} (hr : b - A x₀ = β • v₁) {m : ℕ} {C : ℝ}
    (hC : ∀ z : Fin (m + 1) → 𝕜, ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖ ≤
      C * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • vec A B v₁ w₁ (j : ℕ))‖ ≤
      C * ‖quasiResidual A B v₁ w₁ β m y‖ := by
  rw [(hessenbergRelation h).residual_eq hr m y, quasiResidual_def]
  exact hC _

/-- [saad2003iterative], Prop 7.3, Givens form: when no rotation of the progressive QR factorization
of `T̄_m` degenerates, the minimal quasi-residual is `|γ_m|`, which `Krylov.norm_gamma_eq_prod`
writes as `|s_m| ⋯ |s_1| |β|`. -/
theorem norm_quasiResidual_eq_norm_gamma {m : ℕ} {β : 𝕜}
    (hρ : ∀ k < m, givensRho (BiLanczos.coeff A B v₁ w₁) k ≠ 0) {y : Fin m → 𝕜}
    (hy : IsMinOn (fun z => ‖quasiResidual A B v₁ w₁ β m z‖) Set.univ y) :
    ‖quasiResidual A B v₁ w₁ β m y‖ = ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ := by
  have hh : ∀ i j, j + 1 < i → BiLanczos.coeff A B v₁ w₁ i j = 0 := fun _ _ hij =>
    BiLanczos.coeff_eq_zero_of_lt A B v₁ w₁ hij
  have hsplit : ∀ z : Fin m → 𝕜, ‖quasiResidual A B v₁ w₁ β m z‖ ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin m => gvec (BiLanczos.coeff A B v₁ w₁) β (i : ℕ)) -
          (hessenbergSqOf (rotated (BiLanczos.coeff A B v₁ w₁) m) m).mulVec z) :
        EuclideanSpace 𝕜 (Fin m))‖ ^ 2 + ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ ^ 2 := by
    intro z
    rw [quasiResidual_def]
    exact norm_sq_firstVec_sub_mulVec_eq _ hh hρ β z
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin m → 𝕜,
      (hessenbergSqOf (rotated (BiLanczos.coeff A B v₁ w₁) m) m).mulVec z₀ =
        fun i : Fin m => gvec (BiLanczos.coeff A B v₁ w₁) β (i : ℕ) := by
    have hU := isUnit_hessenbergSqOf_rotated_self (BiLanczos.coeff A B v₁ w₁) hh hρ
    rw [Matrix.isUnit_iff_isUnit_det] at hU
    refine ⟨(hessenbergSqOf (rotated (BiLanczos.coeff A B v₁ w₁) m) m)⁻¹.mulVec
      (fun i : Fin m => gvec (BiLanczos.coeff A B v₁ w₁) β (i : ℕ)), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have h0 : ‖quasiResidual A B v₁ w₁ β m z₀‖ = ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ := by
    have hsq := hsplit z₀
    rw [hz₀, sub_self] at hsq
    simp only [WithLp.toLp_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_add] at hsq
    have h1 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
  refine le_antisymm (h0 ▸ isMinOn_iff.1 hy z₀ (Set.mem_univ z₀)) ?_
  have hsq : ‖gamma (BiLanczos.coeff A B v₁ w₁) β m‖ ^ 2 ≤
      ‖quasiResidual A B v₁ w₁ β m y‖ ^ 2 := by
    rw [hsplit y]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- [saad2003iterative], Thm 7.4: the QMR residual is within `κ₂(V_{m+1}) = C / c` of the GMRES
residual over the same affine space, where `c` and `C` are the extreme singular values of the
coordinate map `z ↦ V_{m+1} z`. The GMRES iterate lies in the same affine space, so its coordinate
vector is a competitor for the quasi-residual minimization; `c` converts its quasi-residual back
into a true residual and `C` converts the QMR one forward. -/
theorem norm_residual_le (hs : NoSeriousBreakdown A B v₁ w₁) {m : ℕ}
    (hnb : NoBreakdown A B v₁ w₁ m) {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v₁)
    {c C : ℝ} (hc0 : 0 < c) (hC0 : 0 ≤ C)
    (hc : ∀ z : Fin (m + 1) → 𝕜, c * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤
      ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖)
    (hC : ∀ z : Fin (m + 1) → 𝕜, ‖∑ i, z i • vec A B v₁ w₁ (i : ℕ)‖ ≤
      C * ‖(WithLp.toLp 2 z : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    {x xG : E} (hx : IsQuasiMinResidual A B v₁ w₁ β x₀ m x)
    (hG : Krylov.IsMinResidualIterate A b x₀ m xG) :
    ‖b - A x‖ ≤ C / c * ‖b - A xG‖ := by
  obtain ⟨y, rfl, hy⟩ := hx
  have hmem0 : xG - x₀ ∈ Krylov.subspace A v₁ m := by
    have hmem := hG.mem
    rw [hr] at hmem
    exact Krylov.subspace_smul A v₁ β m hmem
  have hmem : xG - x₀ ∈ Submodule.span 𝕜 (Set.range fun j : Fin m => vec A B v₁ w₁ (j : ℕ)) := by
    rw [range_eq_image_Iio, span_vec hnb]
    exact hmem0
  obtain ⟨zG, hzG⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem
  have hxGeq : xG = x₀ + ∑ j, zG j • vec A B v₁ w₁ (j : ℕ) := by rw [hzG]; abel
  have hlow : c * ‖quasiResidual A B v₁ w₁ β m zG‖ ≤ ‖b - A xG‖ := by
    rw [hxGeq, (hessenbergRelation hs).residual_eq hr m zG, quasiResidual_def]
    exact hc _
  have hmin : ‖quasiResidual A B v₁ w₁ β m y‖ ≤ ‖quasiResidual A B v₁ w₁ β m zG‖ :=
    isMinOn_iff.1 hy zG (Set.mem_univ zG)
  have h1 : ‖quasiResidual A B v₁ w₁ β m zG‖ ≤ ‖b - A xG‖ / c := by
    rw [le_div_iff₀ hc0]
    linarith
  calc ‖b - A (x₀ + ∑ j, y j • vec A B v₁ w₁ (j : ℕ))‖
      ≤ C * ‖quasiResidual A B v₁ w₁ β m y‖ :=
        norm_residual_le_norm_quasiResidual hs hr hC y
    _ ≤ C * (‖b - A xG‖ / c) := mul_le_mul_of_nonneg_left (hmin.trans h1) hC0
    _ = C / c * ‖b - A xG‖ := by ring

end QMR
