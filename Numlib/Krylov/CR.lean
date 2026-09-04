import Numlib.Krylov.Iterate

/-!
# The conjugate residual recurrence (Stiefel)

`CR.step` is one step of the CR recurrence (Saad Alg 6.20, Fong–Saunders Table 2.1, Choi
Table 2.12), with `q = A p` carried in the state. Main theorems: CR realises the
minimal-residual specification (`CR.isMinResIterate`), the orthogonality relations
(Fong–Saunders Thm 2.1 / Luenberger), the sign properties on SPD systems (Fong–Saunders
Thm 2.2), and the resulting monotonicity of `‖x_k‖` (Fong–Saunders Thm 2.3). Also the general
GCR lemma (Saad Lemma 6.21) that any `AᴴA`-orthogonal direction sequence spanning the Krylov
spaces yields minimal-residual iterates.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CR

/-- State of the CR iteration: iterate, residual, direction, and `q = A p`. -/
structure State (E : Type*) where
  x : E
  r : E
  p : E
  q : E

/-- `α = ⟪r, A r⟫ / ⟪A p, A p⟫`. -/
noncomputable def alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r (A s.r) / inner 𝕜 s.q s.q

/-- One CR step. -/
noncomputable def step (A : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α := alpha A s
  let r' := s.r - α • s.q
  let β : 𝕜 := inner 𝕜 r' (A r') / inner 𝕜 s.r (A s.r)
  { x := s.x + α • s.p, r := r', p := r' + β • s.p, q := A r' + β • s.q }

def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := b - A x₀, q := A (b - A x₀) }

noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) := by
  sorry

theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  sorry

/-- The invariant `q = A p`. -/
theorem q_eq (k : ℕ) : (iterate A b x₀ k).q = A (iterate A b x₀ k).p := by
  sorry

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-- Fong–Saunders Thm 2.1 (a) / Luenberger: `⟪A p_i, A p_j⟫ = 0` for `i ≠ j`. -/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (A (iterate A b x₀ j).p) = 0 := by
  sorry

/-- Fong–Saunders Thm 2.1 (b): `⟪r_i, A p_j⟫ = 0` for `j < i`. -/
theorem inner_residual_apply_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) = 0 := by
  sorry

/-- Residuals are `A`-orthogonal: `⟪r_i, A r_j⟫ = 0` for `i ≠ j`. -/
theorem inner_residual_apply_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0 := by
  sorry

theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k := by
  sorry

/-- CR realises the minimal-residual specification (`= MINRES = GMRES` on symmetric systems). -/
theorem isMinResIterate (k : ℕ) : IsMinResIterate A b x₀ k (iterate A b x₀ k).x := by
  sorry

/-- Fong–Saunders Thm 2.2 (a)–(b): `α_i ≥ 0`, `β_i ≥ 0` (real, nonnegative). -/
theorem re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) := by
  sorry

/-- Fong–Saunders Thm 2.2 (c): `re ⟪p_i, A p_j⟫ ≥ 0`. -/
theorem re_inner_direction_apply_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p)) := by
  sorry

/-- Fong–Saunders Thm 2.2 (d): `re ⟪p_i, p_j⟫ ≥ 0` (uses finite termination). -/
theorem re_inner_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  sorry

/-- Fong–Saunders Thm 2.2 (e): `re ⟪x_i, p_j⟫ ≥ 0` for `x₀ = 0`. -/
theorem re_inner_iterate_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p) := by
  sorry

/-- Fong–Saunders Thm 2.2 (f): `re ⟪r_i, p_j⟫ ≥ 0`. -/
theorem re_inner_residual_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p) := by
  sorry

/-- Fong–Saunders Thm 2.3: `‖x_k‖` is nondecreasing for `x₀ = 0`. -/
theorem norm_iterate_monotone [FiniteDimensional 𝕜 E] :
    Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  sorry

/-- Fong–Saunders Thm 2.4: `‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  sorry

/-- Fong–Saunders Thm 2.5: `‖x* - x_k‖_A` is nonincreasing (strictly while `r_k ≠ 0`). -/
theorem energyNorm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  sorry

theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  sorry

/-- CR on a symmetric, possibly indefinite or singular, operator (Fong–Saunders §2, Choi):
as long as no breakdown occurs (`⟪r_j, A r_j⟫ ≠ 0` and `A p_j ≠ 0` for `j < k`), the iterate
`x_k` is the minimal-residual iterate. -/
theorem isMinResIterate_of_no_breakdown (hA : A.IsSymmetric) (k : ℕ)
    (h1 : ∀ j < k, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) ≠ 0)
    (h2 : ∀ j < k, (iterate A b x₀ j).q ≠ 0) :
    IsMinResIterate A b x₀ k (iterate A b x₀ k).x := by
  sorry

end CR

namespace Krylov

/-- Saad Lemma 6.21 (GCR / ORTHOMIN / ORTHODIR): if `p_0, …, p_{m-1}` are `AᴴA`-orthogonal and
span `𝒦_m(A, r₀)`, then `x_m = x₀ + ∑_j (⟪r_j, A p_j⟫ / ‖A p_j‖²) p_j` (with `r_j` the
successive residuals) is the minimal-residual iterate. -/
theorem isMinResIterate_of_orthogonal_directions {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ}
    (p : ℕ → E) (horth : ∀ i < m, ∀ j < m, i ≠ j → inner 𝕜 (A (p i)) (A (p j)) = 0)
    (hne : ∀ i < m, A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p i) = subspace A (b - A x₀) m)
    (x : ℕ → E) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j) :
    IsMinResIterate A b x₀ m (x m) := by
  sorry

end Krylov
