import Numlib.Krylov.Iterate
import Numlib.Krylov.Relations

/-!
# Hessenberg relations, FOM/GMRES coordinates and Givens rotations

* `Krylov.HessenbergRelation A v h`: a sequence `v` with `A v_j = ∑_{i ≤ j+1} h i j v_i`
  (Saad (6.6)–(6.7)), *without* orthogonality, so that the residual formulas (6.18), (6.27)
  and Prop 6.7 apply verbatim to IOM/DIOM/DQGMRES and (Ch. 7) to the bi-Lanczos basis of QMR;
  Arnoldi is the instance `Arnoldi.hessenbergRelation`.
* FOM and GMRES in coordinates (Saad (6.16)–(6.17), (6.28)–(6.30)): for `m ≤ grade`, the
  Galerkin iterate is `x₀ + V_m y` with `H_m y = β e₁`, exists uniquely iff `H_m` is a unit,
  and the minimal-residual iterate is `x₀ + V_m y` with `y` the least-squares solution of
  `H̄_m y ≈ β e₁`.
* Givens rotations, indexed by `ℕ` (no `Fin` casts): the progressive QR factorization of the
  Hessenberg coefficients `h`, the parameters `c_k, s_k, ρ_k`, the transformed right-hand side
  `γ_k, g_k` with `γ_{k+1} = -s_k γ_k` (Saad (6.37), (6.44)–(6.47), (6.80)–(6.81); Choi §2.2.3;
  Fong–Saunders §4.2), `‖r_m‖ = |γ_m|` (6.42), and the spec-level identifications
  `|s_m| = ‖r^G_{m+1}‖ / ‖r^G_m‖`, `|c_m| = ‖r^G_{m+1}‖ / ‖r^F_{m+1}‖`, `H_{m+1}` unit iff
  `c_m ≠ 0` (Saad Prop 6.9, (6.75), Lemma 6.16). Because the rotations are computed from the
  infinite coefficient function, prefix stability across `m` is automatic.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- The rectangular `(m+1) × m` Hessenberg matrix of a coefficient function `h`. -/
def hessenbergOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- The square `m × m` Hessenberg matrix of a coefficient function `h`. -/
def hessenbergSqOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => h i j

/-- `β e₁ ∈ 𝕜^m`. -/
def firstVec (β : 𝕜) (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then β else 0

/-- A sequence `v` satisfying the Hessenberg relation `A v_j = ∑_{i ≤ j+1} h i j v_i` with `h`
upper Hessenberg (Saad (6.6)–(6.9) without orthogonality). -/
structure HessenbergRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) : Prop where
  apply_eq : ∀ j, A (v j) = ∑ i ∈ range (j + 2), h i j • v i
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0

namespace HessenbergRelation

variable {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜} (hv : HessenbergRelation A v h)
include hv

theorem hessenbergOf_isUpperHessenbergRect (m : ℕ) : (hessenbergOf h m).IsUpperHessenbergRect := by
  sorry

/-- `A V_m = V_{m+1} H̄_m` (Saad (6.7)) in coordinates. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • v j) = ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
  sorry

/-- Saad (6.27): with `r₀ = β v₀`, the residual of `x₀ + V_m y` is `V_{m+1} (β e₁ - H̄_m y)`. -/
theorem residual_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j) =
      ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i := by
  sorry

/-- Saad Prop 6.7 / (6.18): if `H_m y = β e₁` then the residual of `x₀ + V_m y` is
`-(h_{m,m-1} y_{m-1}) v_m`. -/
theorem residual_eq_of_mulVec_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hm : 0 < m) (y : Fin m → 𝕜) (hy : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    b - A (x₀ + ∑ j, y j • v j) = -(h m (m - 1) * y ⟨m - 1, by omega⟩) • v m := by
  sorry

end HessenbergRelation

end Krylov

namespace Arnoldi

variable (A : E →ₗ[𝕜] E) (b : E)

theorem hessenberg_eq (m : ℕ) : hessenberg A b m = hessenbergOf (coeff A b) m := rfl

theorem hessenbergSq_eq (m : ℕ) : hessenbergSq A b m = hessenbergSqOf (coeff A b) m := rfl

/-- The Arnoldi vectors and coefficients satisfy the Hessenberg relation (for every `j`, also
after breakdown where both sides vanish). -/
theorem hessenbergRelation : HessenbergRelation A (vec A b) (coeff A b) := by
  sorry

end Arnoldi

namespace Krylov

section Coordinates

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Saad (6.28): for `m ≤ grade`, `‖b - A (x₀ + V_m y)‖ = ‖β e₁ - H̄_m y‖₂`. -/
theorem norm_residual_eq_norm_firstVec_sub_mulVec {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j)‖ =
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖ := by
  sorry

/-- FOM (Saad (6.16)–(6.17)): `x₀ + V_m y` is the Galerkin iterate iff `H_m y = β e₁`. -/
theorem isGalerkinIterate_iff_mulVec_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsGalerkinIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m := by
  sorry

theorem isGalerkinIterate_iff_exists_mulVec_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (x : E) :
    IsGalerkinIterate A b x₀ m x ↔
      ∃ y : Fin m → 𝕜, (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y =
        firstVec (‖b - A x₀‖ : 𝕜) m ∧ x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  sorry

/-- FOM is well defined iff `H_m` is nonsingular (Saad §6.4, Props 6.12–6.17's hypothesis). -/
theorem existsUnique_isGalerkinIterate_iff_isUnit {m : ℕ} (hm : m ≤ grade A (b - A x₀)) :
    (∃! x, IsGalerkinIterate A b x₀ m x) ↔ IsUnit (Arnoldi.hessenbergSq A (b - A x₀) m) := by
  sorry

/-- Saad Prop 6.7 for Arnoldi: the Galerkin residual is `-(h_{m,m-1} y_{m-1}) v_m`. -/
theorem residual_galerkin_eq {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜)
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m) :
    b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) =
      -(Arnoldi.coeff A (b - A x₀) m (m - 1) * y ⟨m - 1, by omega⟩) •
        Arnoldi.vec A (b - A x₀) m := by
  sorry

/-- GMRES (Saad (6.29)–(6.30)): `x₀ + V_m y` is the minimal-residual iterate iff `y` minimizes
`‖β e₁ - H̄_m z‖₂`. -/
theorem isMinResIterate_iff_isMinOn {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsMinResIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      IsMinOn (fun z : Fin m → 𝕜 => ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
        Set.univ y := by
  sorry

end Coordinates

section Givens

/-! ### Givens rotations, `ℕ`-indexed

`rotated h k` is the coefficient function after the first `k` rotations; rotation `k` acts on
rows `k, k+1` and annihilates the entry `(k+1, k)`. With `a = (rotated h k) k k`,
`d = (rotated h k) (k+1) k`, `ρ_k = √(|a|² + |d|²)`, `c_k = a / ρ_k`, `s_k = d / ρ_k`, the rotation
is `[[c̄_k, s̄_k], [-s_k, c_k]]` (Saad (6.80) for complex `𝕜`; `s_k` is real for Arnoldi
coefficients). -/

/-- The Hessenberg coefficients after `k` Givens rotations. -/
noncomputable def rotated (h : ℕ → ℕ → 𝕜) : ℕ → ℕ → ℕ → 𝕜
  | 0 => h
  | k + 1 => fun i j =>
      let a := rotated h k k k
      let d := rotated h k (k + 1) k
      let ρ : 𝕜 := (Real.sqrt (‖a‖ ^ 2 + ‖d‖ ^ 2) : 𝕜)
      if i = k then
        starRingEnd 𝕜 (a / ρ) * rotated h k k j + starRingEnd 𝕜 (d / ρ) * rotated h k (k + 1) j
      else if i = k + 1 then -(d / ρ) * rotated h k k j + (a / ρ) * rotated h k (k + 1) j
      else rotated h k i j

variable (h : ℕ → ℕ → 𝕜)

/-- `ρ_k = √(|r_kk|² + |h_{k+1,k}|²)`. -/
noncomputable def givensRho (k : ℕ) : ℝ :=
  Real.sqrt (‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2)

/-- `c_k = r_kk / ρ_k`. -/
noncomputable def givensC (k : ℕ) : 𝕜 := rotated h k k k / (givensRho h k : 𝕜)

/-- `s_k = h_{k+1,k} / ρ_k`. -/
noncomputable def givensS (k : ℕ) : 𝕜 := rotated h k (k + 1) k / (givensRho h k : 𝕜)

/-- `γ_0 = β`, `γ_{k+1} = -s_k γ_k` (Saad (6.47)): the last entry of the rotated right-hand
side. -/
noncomputable def gamma (β : 𝕜) : ℕ → 𝕜
  | 0 => β
  | k + 1 => -givensS h k * gamma β k

/-- `g_k = c̄_k γ_k`: the `k`-th entry of `Q_m (β e₁)` for `k < m`. -/
noncomputable def gvec (β : 𝕜) (k : ℕ) : 𝕜 := starRingEnd 𝕜 (givensC h k) * gamma h β k

theorem gamma_succ (β : 𝕜) (k : ℕ) : gamma h β (k + 1) = -givensS h k * gamma h β k := rfl

/-- `‖γ_m‖ = ∏_{k < m} |s_k| ‖β‖` (Saad (6.47)). -/
theorem norm_gamma_eq_prod (β : 𝕜) (m : ℕ) :
    ‖gamma h β m‖ = (∏ k ∈ range m, ‖givensS h k‖) * ‖β‖ := by
  sorry

theorem norm_givensC_sq_add_norm_givensS_sq (k : ℕ) (hρ : givensRho h k ≠ 0) :
    ‖givensC h k‖ ^ 2 + ‖givensS h k‖ ^ 2 = 1 := by
  sorry

/-- Rotation `k` produces the real diagonal entry `ρ_k` and annihilates `(k+1, k)`. -/
theorem rotated_succ_self (k : ℕ) : rotated h (k + 1) k k = (givensRho h k : 𝕜) := by
  sorry

theorem rotated_succ_succ_self (k : ℕ) : rotated h (k + 1) (k + 1) k = 0 := by
  sorry

/-- Rows below `k` are untouched by the first `k` rotations. -/
theorem rotated_eq_of_le (k i j : ℕ) (hi : k + 1 ≤ i) : rotated h k i j = h i j := by
  sorry

/-- Columns `j < k` are not changed by rotation `k`, for Hessenberg `h`. -/
theorem rotated_succ_eq_of_lt (hh : ∀ i j, j + 1 < i → h i j = 0) (k j : ℕ) (hj : j < k) (i : ℕ) :
    rotated h (k + 1) i j = rotated h k i j := by
  sorry

/-- After `k` rotations the first `k` columns are upper triangular. -/
theorem rotated_eq_zero_of_lt (hh : ∀ i j, j + 1 < i → h i j = 0) (k i j : ℕ) (hj : j < k)
    (hij : j < i) : rotated h k i j = 0 := by
  sorry

/-- The `k`-th rotation as an `(m+1) × (m+1)` matrix (identity outside rows/columns `k, k+1`). -/
noncomputable def givensMatrix (k m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  Matrix.of fun i j =>
    if (i : ℕ) = k ∧ (j : ℕ) = k then starRingEnd 𝕜 (givensC h k)
    else if (i : ℕ) = k ∧ (j : ℕ) = k + 1 then starRingEnd 𝕜 (givensS h k)
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k then -givensS h k
    else if (i : ℕ) = k + 1 ∧ (j : ℕ) = k + 1 then givensC h k
    else if i = j then 1 else 0

theorem givensMatrix_mem_unitaryGroup (k m : ℕ) (hρ : givensRho h k ≠ 0) :
    givensMatrix h k m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := by
  sorry

/-- `Ω_k H̄^{(k)} = H̄^{(k+1)}` for `k < m`. -/
theorem givensMatrix_mul_hessenbergOf_rotated (k m : ℕ) (hk : k < m) :
    givensMatrix h k m * hessenbergOf (rotated h k) m = hessenbergOf (rotated h (k + 1)) m := by
  sorry

/-- `Q_m = Ω_{m-1} ⋯ Ω_0`. -/
noncomputable def givensQ (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
  (((List.range m).map fun k => givensMatrix h k m).reverse).prod

/-- `Q_m H̄_m = R̄_m` (Saad (6.38)–(6.39)): the rotated coefficients form the triangular factor. -/
theorem givensQ_mul_hessenbergOf (m : ℕ) :
    givensQ h m * hessenbergOf h m = hessenbergOf (rotated h m) m := by
  sorry

theorem givensQ_mem_unitaryGroup (m : ℕ) (hρ : ∀ k < m, givensRho h k ≠ 0) :
    givensQ h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜 := by
  sorry

/-- `Q_m (β e₁) = (g_0, …, g_{m-1}, γ_m)` (Saad (6.40), (6.44)–(6.47)). -/
theorem givensQ_mulVec_firstVec (β : 𝕜) (m : ℕ) :
    (givensQ h m).mulVec (firstVec β (m + 1)) =
      fun i : Fin (m + 1) => if (i : ℕ) < m then gvec h β i else gamma h β m := by
  sorry

/-- The last row of `R̄_m` vanishes. -/
theorem rotated_last_row (hh : ∀ i j, j + 1 < i → h i j = 0) (m j : ℕ) (hj : j < m) :
    rotated h m m j = 0 := by
  sorry

end Givens

section GivensArnoldi

/-! ### Identifications for the Arnoldi coefficients (`β = ‖r₀‖`) -/

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Saad (6.42), Prop 6.9(3): `‖r^G_m‖ = |γ_m|` for `m ≤ grade`. -/
theorem IsMinResIterate.norm_residual_eq_norm_gamma {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ := by
  sorry

/-- Saad (6.43)/(6.30): the minimal-residual iterate is `x₀ + V_m y` with `R_m y = g_m`. -/
theorem IsMinResIterate.exists_mulVec_rotated_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j := by
  sorry

/-- `|s_m| = ‖r^G_{m+1}‖ / ‖r^G_m‖` (Saad (6.47), Prop 6.9). -/
theorem IsMinResIterate.norm_residual_succ_eq {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) {x x' : E}
    (hx : IsMinResIterate A b x₀ m x) (hx' : IsMinResIterate A b x₀ (m + 1) x') :
    ‖b - A x'‖ = ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * ‖b - A x‖ := by
  sorry

/-- `H_{m+1}` is nonsingular iff `c_m ≠ 0` (Saad Prop 6.9(1) / Lemma 6.16, `m + 1 ≤ grade`). -/
theorem isUnit_hessenbergSq_iff_givensC_ne_zero {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) :
    IsUnit (Arnoldi.hessenbergSq A (b - A x₀) (m + 1)) ↔
      givensC (Arnoldi.coeff A (b - A x₀)) m ≠ 0 := by
  sorry

/-- Saad (6.75) / Prop 6.12: `‖r^F_{m+1}‖ = ‖r^G_{m+1}‖ / |c_m|`. -/
theorem IsGalerkinIterate.norm_residual_eq_div_norm_givensC {m : ℕ}
    (hm : m + 1 ≤ grade A (b - A x₀)) {xF xG : E} (hF : IsGalerkinIterate A b x₀ (m + 1) xF)
    (hG : IsMinResIterate A b x₀ (m + 1) xG) :
    ‖b - A xF‖ = ‖b - A xG‖ / ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖ := by
  sorry

/-- The rotation `s_m` is real and nonnegative for Arnoldi coefficients (Saad §6.5.9). -/
theorem givensS_arnoldi_eq (m : ℕ) :
    givensS (Arnoldi.coeff A (b - A x₀)) m =
      (‖Arnoldi.w A (b - A x₀) m‖ / givensRho (Arnoldi.coeff A (b - A x₀)) m : ℝ) := by
  sorry

end GivensArnoldi

end Krylov
