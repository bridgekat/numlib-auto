import Numlib.Krylov.Iterate
import Numlib.Krylov.Lanczos

/-!
# The conjugate gradient recurrence (Hestenes–Stiefel)

`CG.step` is one step of the two-term CG recurrence
(Saad, *Iterative Methods*[^saad-iterative] Alg 6.18, Atkinson–Han[^atkinson-han] (5.6.2)/§9.4,
Fong–Saunders[^fong-saunders] Table 2.1, Meurant–Strakoš[^meurant-strakos] (3.2),
Choi[^choi] Table 2.7). The main theorems: CG realises the Galerkin specification
(`CG.isGalerkinIterate`), the orthogonality invariants (Saad Prop 6.20), the identification of
CG residuals with Lanczos vectors (Saad (6.101)–(6.103), Meurant–Strakoš (3.4)), and the
Hestenes–Stiefel[^hestenes-stiefel] error identities and monotonicity results
(Hestenes–Stiefel Thm 6:1, 6:3; Steihaug[^steihaug], including his form for a symmetric but
possibly indefinite `A`).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
[^hestenes-stiefel]: Magnus R. Hestenes and Eduard Stiefel, *Methods of conjugate gradients for
  solving linear systems*, Journal of Research of the National Bureau of Standards 49 (1952),
  409–436.
[^steihaug]: Trond Steihaug, *The conjugate gradient method and trust regions in large scale
  optimization*, SIAM Journal on Numerical Analysis 20 (1983), 626–637.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CG

/-- State of the CG iteration: iterate, residual, search direction. -/
@[ext]
structure State (E : Type*) where
  /-- The iterate `x_k`. -/
  x : E
  /-- The residual `r_k = b - A x_k` (see `CG.residual_eq`). -/
  r : E
  /-- The search direction `p_k`. -/
  p : E

/-- The CG step length `α = ⟪r, r⟫ / ⟪A p, p⟫`. -/
noncomputable def alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r s.r / inner 𝕜 (A s.p) s.p

/-- One CG step. -/
noncomputable def step (A : E →ₗ[𝕜] E) (s : State E) : State E :=
  let q := A s.p
  let α := alpha A s
  let r' := s.r - α • q
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.r s.r
  { x := s.x + α • s.p, r := r', p := r' + β • s.p }

/-- The CG direction update coefficient `β = ⟪r', r'⟫ / ⟪r, r⟫`. -/
noncomputable def beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A s).r (step A s).r / inner 𝕜 s.r s.r

/-- Initial state `x₀, r₀ = b - A x₀, p₀ = r₀`. -/
def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E := { x := x₀, r := b - A x₀, p := b - A x₀ }

/-- The `k`-th CG state. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

@[simp] theorem init_x : (init A b x₀).x = x₀ := rfl

@[simp] theorem init_r : (init A b x₀).r = b - A x₀ := rfl

@[simp] theorem init_p : (init A b x₀).p = b - A x₀ := rfl

@[simp] theorem iterate_zero : iterate A b x₀ 0 = init A b x₀ := rfl

/-- The recurrence: state `k + 1` is one `CG.step` applied to state `k`. This is the orientation
the algorithm is read in; `Function.iterate` reduces by peeling a step off the front instead, so
unfolding `(step A)^[k+1]` directly gives an extra step applied to the *initial* state. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem step_x (s : State E) : (step A s).x = s.x + alpha A s • s.p := rfl

theorem step_r (s : State E) : (step A s).r = s.r - alpha A s • A s.p := rfl

/-- The direction update `p' = r' + β p` of one CG step. -/
theorem step_p (s : State E) : (step A s).p = (step A s).r + beta A s • s.p := rfl

/-- The state's residual field is the true residual. -/
theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_r, step_x, ih, map_add, map_smul, sub_sub]

/-! ### Unfolding the recurrence -/

theorem iterate_succ_x (k : ℕ) : (iterate A b x₀ (k + 1)).x =
    (iterate A b x₀ k).x + alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ, step_x]

theorem iterate_succ_r (k : ℕ) : (iterate A b x₀ (k + 1)).r =
    (iterate A b x₀ k).r - alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p := by
  rw [iterate_succ, step_r]

theorem iterate_succ_p (k : ℕ) : (iterate A b x₀ (k + 1)).p =
    (iterate A b x₀ (k + 1)).r + beta A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ]; exact step_p A _

theorem beta_iterate (k : ℕ) : beta A (iterate A b x₀ k) =
    inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r /
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
  rw [beta, iterate_succ]

/-- `p₀ = r₀`. -/
theorem direction_zero : (iterate A b x₀ 0).p = (iterate A b x₀ 0).r := rfl

/-- `α_k A p_k = r_k - r_{k+1}`: the only way `A` enters the residual recurrence. -/
theorem alpha_smul_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p =
      (iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r := by
  rw [iterate_succ_r]; abel

/-- If the residual vanishes so does the search direction (`β = 0 / … = 0`). -/
theorem direction_eq_zero_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ k).p = 0 := by
  cases k with
  | zero => rw [direction_zero]; exact hr
  | succ k =>
    rw [iterate_succ_p, hr, beta_iterate, hr, inner_zero_left, zero_div, zero_smul, add_zero]

/-- The iteration is stationary once the residual vanishes (Lean's `x / 0 = 0`). -/
theorem step_eq_self_of_residual_eq_zero (s : State E) (hr : s.r = 0) (hp : s.p = 0) :
    step A s = s := by
  obtain ⟨x, r, p⟩ := s
  simp_all [step]

theorem iterate_eq_of_residual_eq_zero' {k : ℕ} (hk : (iterate A b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate A b x₀ l = iterate A b x₀ k := by
  induction l with
  | zero => obtain rfl : k = 0 := Nat.le_zero.1 hl; rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · rw [iterate_succ, ih (Nat.lt_succ_iff.1 h), step_eq_self_of_residual_eq_zero A _ hk
        (direction_eq_zero_of_residual_eq_zero A b x₀ hk)]
    · obtain rfl : k = l + 1 := le_antisymm hl h
      rfl

/-- `r_{k+1} = 0` as soon as `r_k = 0`. -/
theorem residual_succ_eq_zero_of_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ (k + 1)).r = 0 := by
  rw [iterate_eq_of_residual_eq_zero' A b x₀ hr (k + 1) (Nat.le_succ k), hr]

/-! ### Elementary consequences of the recurrence, before any orthogonality -/

private theorem inner_self_eq_ofReal_norm_sq (x : E) : inner 𝕜 x x = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  ring

private theorem conj_beta (s : State E) : (starRingEnd 𝕜) (beta A s) = beta A s := by
  rw [beta, map_div₀, inner_self_conj, inner_self_conj]

/-- `β_k ⟪r_k, r_k⟫ = ⟪r_{k+1}, r_{k+1}⟫`, valid also at a breakdown. -/
private theorem beta_mul_inner_self (k : ℕ) :
    beta A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r =
      inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ (k + 1)).r := by
  by_cases h : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r = 0
  · rw [h, mul_zero, residual_succ_eq_zero_of_eq_zero A b x₀ (inner_self_eq_zero.1 h),
      inner_zero_left]
  · rw [beta_iterate, div_mul_cancel₀ _ h]

/-- Each residual is a combination of two consecutive directions, so orthogonality to the
directions gives orthogonality to the residuals. -/
private theorem inner_residual_eq_zero_of_inner_direction {j : ℕ} {v : E}
    (h : ∀ l ≤ j, inner 𝕜 v (iterate A b x₀ l).p = 0) :
    inner 𝕜 v (iterate A b x₀ j).r = 0 := by
  cases j with
  | zero => rw [← direction_zero]; exact h 0 le_rfl
  | succ i =>
    have hi : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [hi, inner_sub_right, inner_smul_right, h _ le_rfl, h i (Nat.le_succ i), mul_zero,
      sub_zero]

/-- `v ⟂ span s` follows from `v ⟂ s`. -/
private theorem mem_orthogonal_span {s : Set E} {v : E} (h : ∀ u ∈ s, inner 𝕜 u v = 0) :
    v ∈ (Submodule.span 𝕜 s)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- Both `r_k` and `p_k` lie in `𝒦_{k+1}`. -/
private theorem residual_direction_mem_subspace (k : ℕ) :
    (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) ∧
      (iterate A b x₀ k).p ∈ subspace A (b - A x₀) (k + 1) := by
  induction k with
  | zero =>
    have h : b - A x₀ ∈ subspace A (b - A x₀) 1 := self_mem_subspace A (b - A x₀) one_pos
    exact ⟨h, h⟩
  | succ k ih =>
    have hmono := subspace_mono A (b - A x₀) (Nat.le_succ (k + 1))
    have hr : (iterate A b x₀ (k + 1)).r ∈ subspace A (b - A x₀) (k + 1 + 1) := by
      rw [iterate_succ_r]
      exact Submodule.sub_mem _ (hmono ih.1) (Submodule.smul_mem _ _
        (map_subspace_le A (b - A x₀) (k + 1) ⟨_, ih.2, rfl⟩))
    exact ⟨hr, by
      rw [iterate_succ_p]
      exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ih.2))⟩

theorem residual_mem_subspace (k : ℕ) : (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) :=
  (residual_direction_mem_subspace A b x₀ k).1

theorem direction_mem_subspace (k : ℕ) : (iterate A b x₀ k).p ∈ subspace A (b - A x₀) (k + 1) :=
  (residual_direction_mem_subspace A b x₀ k).2

/-- The span of the first `k` search directions. -/
private noncomputable def dirSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p)

/-- The span of the first `k` residuals. -/
private noncomputable def resSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).r)

private theorem direction_mem_dirSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).p ∈ dirSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem residual_mem_resSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).r ∈ resSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem dirSpan_mono {k l : ℕ} (h : k ≤ l) : dirSpan A b x₀ k ≤ dirSpan A b x₀ l := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact direction_mem_dirSpan A b x₀ (lt_of_lt_of_le i.2 h)

private theorem resSpan_mono {k l : ℕ} (h : k ≤ l) : resSpan A b x₀ k ≤ resSpan A b x₀ l := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact residual_mem_resSpan A b x₀ (lt_of_lt_of_le i.2 h)

private theorem residual_mem_dirSpan (i : ℕ) : (iterate A b x₀ i).r ∈ dirSpan A b x₀ (i + 1) := by
  cases i with
  | zero => rw [← direction_zero]; exact direction_mem_dirSpan A b x₀ Nat.zero_lt_one
  | succ i =>
    have h : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [h]
    exact Submodule.sub_mem _ (direction_mem_dirSpan A b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (direction_mem_dirSpan A b x₀ (by omega)))

private theorem direction_mem_resSpan (i : ℕ) : (iterate A b x₀ i).p ∈ resSpan A b x₀ (i + 1) := by
  induction i with
  | zero => rw [direction_zero]; exact residual_mem_resSpan A b x₀ Nat.zero_lt_one
  | succ i ih =>
    rw [iterate_succ_p]
    exact Submodule.add_mem _ (residual_mem_resSpan A b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (resSpan_mono A b x₀ (by omega) ih))

private theorem dirSpan_le_subspace (k : ℕ) : dirSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (direction_mem_subspace A b x₀ i)

private theorem resSpan_le_subspace (k : ℕ) : resSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (residual_mem_subspace A b x₀ i)

private theorem dirSpan_le_resSpan (k : ℕ) : dirSpan A b x₀ k ≤ resSpan A b x₀ k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact resSpan_mono A b x₀ i.2 (direction_mem_resSpan A b x₀ i)

private theorem resSpan_le_dirSpan (k : ℕ) : resSpan A b x₀ k ≤ dirSpan A b x₀ k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact dirSpan_mono A b x₀ i.2 (residual_mem_dirSpan A b x₀ i)

private theorem energyNorm_nonneg (x : E) : 0 ≤ energyNorm A x := Real.sqrt_nonneg _

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-! ### The joint induction (Saad, *Iterative Methods*, Prop 6.20) -/

private theorem re_inner_apply_self_nonneg (x : E) : 0 ≤ RCLike.re (inner 𝕜 (A x) x) := by
  obtain ⟨c, hc, h⟩ := hA.isCoercive
  exact le_trans (by positivity) (h x)

omit hA in
private theorem inner_apply_self_ofReal (hAs : A.IsSymmetric) (x : E) :
    ((RCLike.re (inner 𝕜 (A x) x) : ℝ) : 𝕜) = inner 𝕜 (A x) x :=
  RCLike.conj_eq_iff_re.1 (by rw [inner_conj_symm, ← hAs])

private theorem eq_zero_of_inner_apply_self_eq_zero {x : E} (h : inner 𝕜 (A x) x = 0) : x = 0 := by
  by_contra hx
  have := hA.isCoercive.inner_self_pos hx
  rw [h, map_zero] at this
  exact lt_irrefl 0 this

omit hA in
private theorem conj_alpha (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (alpha A s) = alpha A s := by
  rw [alpha, map_div₀, inner_self_conj, inner_conj_symm, ← hAs]

omit hA in
/-- `α_k ⟪A p_k, p_k⟫ = ⟪r_k, r_k⟫`, valid also at a breakdown.  `hdeg` is the only thing
coercivity is used for here, so any nondegeneracy hypothesis that supplies it will do. -/
private theorem alpha_mul_inner_apply_direction' (k : ℕ)
    (hdeg : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0 →
      (iterate A b x₀ k).p = 0)
    (hdiag : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r) :
    alpha A (iterate A b x₀ k) * inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
  by_cases h : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0
  · rw [h, mul_zero, ← hdiag, hdeg h, inner_zero_right]
  · rw [alpha, div_mul_cancel₀ _ h]

omit hA in
/-- `A p_k = 0` when the step length degenerates. -/
private theorem apply_direction_eq_zero_of_alpha_eq_zero {k : ℕ}
    (hdeg : inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p = 0 →
      (iterate A b x₀ k).p = 0)
    (h : alpha A (iterate A b x₀ k) = 0) : A (iterate A b x₀ k).p = 0 := by
  rcases div_eq_zero_iff.1 h with h' | h'
  · rw [direction_eq_zero_of_residual_eq_zero A b x₀ (inner_self_eq_zero.1 h'), map_zero]
  · rw [hdeg h', map_zero]

omit hA in
/-- `⟪v, A p_j⟫ = 0` whenever `v` is orthogonal to `r_j` and to `r_{j+1}`. -/
private theorem inner_apply_direction_eq_zero_of {j : ℕ} {v : E}
    (hdeg : inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p = 0 →
      (iterate A b x₀ j).p = 0)
    (h1 : inner 𝕜 v (iterate A b x₀ j).r = 0)
    (h2 : inner 𝕜 v (iterate A b x₀ (j + 1)).r = 0) :
    inner 𝕜 v (A (iterate A b x₀ j).p) = 0 := by
  by_cases hα : alpha A (iterate A b x₀ j) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀ hdeg hα, inner_zero_right]
  · have h : alpha A (iterate A b x₀ j) * inner 𝕜 v (A (iterate A b x₀ j).p) = 0 := by
      rw [← inner_smul_right, alpha_smul_apply_direction, inner_sub_right, h1, h2, sub_zero]
    exact (mul_eq_zero.1 h).resolve_left hα

/-- The joint CG invariant at step `k` (Saad, *Iterative Methods*, Prop 6.20): the residual is
orthogonal to all earlier search directions, the current direction is `A`-conjugate to all
earlier ones, and
`⟪r_k, p_k⟫ = ⟪r_k, r_k⟫`. -/
private structure Invariant (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Prop where
  /-- `r_k ⟂ p_j` for `j < k`. -/
  rp : ∀ j < k, inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ j).p = 0
  /-- `p_k` is `A`-conjugate to `p_j` for `j < k`. -/
  pp : ∀ j < k, inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ j).p = 0
  /-- `⟪r_k, p_k⟫ = ⟪r_k, r_k⟫`. -/
  diag : inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).p =
    inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r

omit hA in
/-- The invariant under the one fact coercivity is used for: a direction whose `A`-norm
degenerates is itself zero.  Besides that only symmetry of `A` enters, which is what lets
Steihaug's indefinite theorem below reuse the whole induction. -/
private theorem invariant_of (hAs : A.IsSymmetric) (k : ℕ) :
    (∀ j < k, inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p = 0 →
      (iterate A b x₀ j).p = 0) → Invariant A b x₀ k := by
  induction k with
  | zero =>
    exact fun _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j), by rw [direction_zero]⟩
  | succ k ihk =>
    intro hdeg
    have ih := ihk fun j hj => hdeg j (by omega)
    -- Step 1: `r_{k+1} ⟂ p_j` for `j ≤ k`.
    have rp : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ j).p = 0 := by
      intro j hj
      rw [iterate_succ_r, inner_sub_left, inner_smul_left, conj_alpha hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.rp j h, ih.pp j h, mul_zero, sub_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        rw [ih.diag, alpha_mul_inner_apply_direction' b x₀ j (hdeg j (by omega)) ih.diag, sub_self]
    -- Step 2: `r_{k+1} ⟂ r_j` for `j ≤ k`.
    have rr : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (iterate A b x₀ j).r = 0 :=
      fun j hj => inner_residual_eq_zero_of_inner_direction A b x₀ fun l hl => rp l (by omega)
    refine ⟨rp, fun j hj => ?_, ?_⟩
    · -- Step 3: `p_{k+1}` is `A`-conjugate to `p_j` for `j ≤ k`.
      rw [iterate_succ_p, map_add, map_smul, inner_add_left, inner_smul_left, conj_beta, hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.pp j h, mul_zero, add_zero,
          inner_apply_direction_eq_zero_of b x₀ (hdeg j (by omega)) (rr j (by omega))
            (rr (j + 1) (by omega))]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        by_cases hα : alpha A (iterate A b x₀ j) = 0
        · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀ (hdeg j (by omega)) hα,
            inner_zero_right, inner_zero_left, mul_zero, add_zero]
        · have key : alpha A (iterate A b x₀ j) *
              (inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ j).p) +
                beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) = 0 := by
            rw [mul_add, ← inner_smul_right, alpha_smul_apply_direction, inner_sub_right,
              rr j (by omega), zero_sub, inner_self_eq_ofReal_norm_sq]
            rw [show alpha A (iterate A b x₀ j) * (beta A (iterate A b x₀ j) *
                inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) =
                beta A (iterate A b x₀ j) * (alpha A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p) by ring,
              alpha_mul_inner_apply_direction' b x₀ j (hdeg j (by omega)) ih.diag,
              beta_mul_inner_self A b x₀ j, inner_self_eq_ofReal_norm_sq]
            ring
          exact (mul_eq_zero.1 key).resolve_left hα
    · -- Step 4: `⟪r_{k+1}, p_{k+1}⟫ = ⟪r_{k+1}, r_{k+1}⟫`.
      rw [iterate_succ_p, inner_add_right, inner_smul_right, rp k (Nat.lt_succ_self k), mul_zero,
        add_zero]

private theorem invariant (k : ℕ) : Invariant A b x₀ k :=
  invariant_of b x₀ hA.isSymmetric k fun _ _ h => eq_zero_of_inner_apply_self_eq_zero hA h

/-! ### The named orthogonality relations -/

private theorem alpha_mul_inner_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) * inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r :=
  alpha_mul_inner_apply_direction' b x₀ k
    (fun h => eq_zero_of_inner_apply_self_eq_zero hA h) (invariant b x₀ hA k).diag

/-- Well-definedness: `⟪A p_k, p_k⟫ > 0` as long as `r_k ≠ 0`. -/
theorem re_inner_apply_direction_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p) := by
  refine hA.isCoercive.inner_self_pos fun hp => hr ?_
  have h := (invariant b x₀ hA k).diag
  rw [hp, inner_zero_right] at h
  exact inner_self_eq_zero.1 h.symm

set_option linter.unusedSectionVars false in
/-- Once the residual vanishes the iteration is stationary. -/
theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) (j : ℕ) :
    iterate A b x₀ (k + j) = iterate A b x₀ k :=
  iterate_eq_of_residual_eq_zero' A b x₀ hr (k + j) (Nat.le_add_right k j)

/-- Saad, *Iterative Methods*, Prop 6.20 (i): residuals are mutually orthogonal. -/
theorem inner_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0 := by
  have key : ∀ m n : ℕ, n < m → inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ n).r = 0 :=
    fun m n hmn => inner_residual_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant b x₀ hA m).rp l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, key j i h', map_zero]
  · exact key i j h'

/-- Saad, *Iterative Methods*, Prop 6.20 (ii): directions are `A`-conjugate. -/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (iterate A b x₀ j).p = 0 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [hA.isSymmetric, ← inner_conj_symm, (invariant b x₀ hA j).pp i h', map_zero]
  · exact (invariant b x₀ hA i).pp j h'

/-- `⟪r_i, p_j⟫ = 0` for `j < i`. -/
theorem inner_residual_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p = 0 :=
  (invariant b x₀ hA i).rp j h

/-- `⟪r_i, p_j⟫ = ‖r_j‖²` for `i ≤ j`.

Statement correction: the skeleton had `‖r_i‖²` on the right.  That is false as soon as `i < j`:
expanding `p_j = ∑_{l ≤ j} (∏_{m=l}^{j-1} β_m) r_l` and using `∏_{m=i}^{j-1} β_m = ‖r_j‖²/‖r_i‖²`
gives `⟪r_i, p_j⟫ = ‖r_j‖²`; already `⟪r₀, p₁⟫ = β₀ ‖r₀‖² = ‖r₁‖²`.  The two agree at `i = j`,
which is the only case the companion statement `inner_residual_direction_eq_zero` leaves open. -/
theorem inner_residual_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p =
      (‖(iterate A b x₀ j).r‖ ^ 2 : ℝ) := by
  induction j, h using Nat.le_induction with
  | base => rw [(invariant b x₀ hA i).diag, inner_self_eq_ofReal_norm_sq]
  | succ j hij ih =>
    rw [iterate_succ_p, inner_add_right, inner_smul_right, ih,
      inner_residual_eq_zero b x₀ hA (show i ≠ j + 1 by omega), zero_add,
      ← inner_self_eq_ofReal_norm_sq, ← inner_self_eq_ofReal_norm_sq, beta_mul_inner_self A b x₀ j]

/-! ### Spans and the Galerkin property -/

private theorem apply_direction_mem_dirSpan (i : ℕ) :
    A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2) := by
  by_cases hα : alpha A (iterate A b x₀ i) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero b x₀
      (fun h => eq_zero_of_inner_apply_self_eq_zero hA h) hα]
    exact Submodule.zero_mem _
  · have h : A (iterate A b x₀ i).p = (alpha A (iterate A b x₀ i))⁻¹ •
        ((iterate A b x₀ i).r - (iterate A b x₀ (i + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ i))
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ (i + 1))))

private theorem pow_apply_mem_dirSpan (k : ℕ)
    (ih : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k) :
    (A ^ k) (b - A x₀) ∈ dirSpan A b x₀ (k + 1) := by
  cases k with
  | zero =>
    have h : (iterate A b x₀ 0).p ∈ dirSpan A b x₀ 1 :=
      direction_mem_dirSpan A b x₀ Nat.zero_lt_one
    simpa [init] using h
  | succ j =>
    have hmem : (A ^ j) (b - A x₀) ∈ dirSpan A b x₀ (j + 1) :=
      ih (pow_apply_mem_subspace A _ (Nat.lt_succ_self j))
    have hpow : (A ^ (j + 1)) (b - A x₀) = A ((A ^ j) (b - A x₀)) := by rw [pow_succ']; rfl
    have hcomap : dirSpan A b x₀ (j + 1) ≤ Submodule.comap A (dirSpan A b x₀ (j + 1 + 1)) := by
      rw [dirSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact dirSpan_mono A b x₀ (by omega) (apply_direction_mem_dirSpan b x₀ hA l)
    rw [hpow]
    exact hcomap hmem

private theorem subspace_le_dirSpan (k : ℕ) : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k := by
  induction k with
  | zero => rw [subspace_zero]; exact bot_le
  | succ k ih =>
    rw [subspace, Submodule.span_le, Set.range_subset_iff]
    intro i
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · exact dirSpan_mono A b x₀ (Nat.le_succ k) (ih (pow_apply_mem_subspace A _ h))
    · have h' : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) h
      rw [h']
      exact pow_apply_mem_dirSpan b x₀ hA k ih

/-- `span {p_0, …, p_{k-1}} = 𝒦_k(A, r₀)`. -/
theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
  le_antisymm (dirSpan_le_subspace A b x₀ k) (subspace_le_dirSpan b x₀ hA k)

/-- `span {r_0, …, r_{k-1}} = 𝒦_k(A, r₀)`. -/
theorem span_residual_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).r) =
      subspace A (b - A x₀) k :=
  le_antisymm (resSpan_le_subspace A b x₀ k)
    ((subspace_le_dirSpan b x₀ hA k).trans (dirSpan_le_resSpan A b x₀ k))

set_option linter.unusedSectionVars false in
/-- CG stays in the affine Krylov space: `x_k ∈ x₀ + 𝒦_k(A, r₀)`. This is the membership half of
the Galerkin specification `CG.isGalerkinIterate`, and it follows from the recurrence alone —
each correction is a multiple of a direction `p_j ∈ 𝒦_{j+1}`. The section's symmetry and
coercivity hypothesis appears in the signature but is not used by the proof. -/
theorem iterate_sub_mem (k : ℕ) : (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k := by
  induction k with
  | zero => simp [init]
  | succ k ih =>
    have h : (iterate A b x₀ (k + 1)).x - x₀ = ((iterate A b x₀ k).x - x₀) +
        alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
      rw [iterate_succ_x]; abel
    rw [h]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ (direction_mem_subspace A b x₀ k))

/-- CG realises the Galerkin specification (hence minimizes the energy-norm error). -/
theorem isGalerkinIterate (k : ℕ) : IsGalerkinIterate A b x₀ k (iterate A b x₀ k).x := by
  refine ⟨iterate_sub_mem b x₀ hA k, ?_⟩
  rw [← residual_eq, ← span_direction_eq b x₀ hA k]
  refine mem_orthogonal_span ?_
  rintro _ ⟨i, rfl⟩
  rw [← inner_conj_symm, inner_residual_direction_eq_zero b x₀ hA i.2, map_zero]

/-! ### Identification with the Lanczos vectors -/

omit hA in
/-- Residuals do not vanish before step `k` if `r_k ≠ 0`. -/
private theorem residual_ne_zero_of_le {k j : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) (hj : j ≤ k) :
    (iterate A b x₀ j).r ≠ 0 := fun h =>
  hr (by rw [iterate_eq_of_residual_eq_zero' A b x₀ h k hj]; exact h)

/-- The step lengths are *positive* reals as long as the residual survives. -/
private theorem alpha_eq_ofReal_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ alpha A (iterate A b x₀ k) = (s : 𝕜) := by
  refine ⟨‖(iterate A b x₀ k).r‖ ^ 2 /
      RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p),
    div_pos (pow_pos (norm_pos_iff.2 hr) 2) (re_inner_apply_direction_pos b x₀ hA hr), ?_⟩
  rw [RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq,
    inner_apply_self_ofReal hA.isSymmetric, alpha]

/-- `∏_{j<k} (-α_j) = (-1)^k · (positive real)`. -/
private theorem prod_neg_alpha (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) = (-1 : 𝕜) ^ k * (c : 𝕜) := by
  induction k with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ k ih =>
    have hk := residual_ne_zero_of_le b x₀ hr (Nat.le_succ k)
    obtain ⟨c, hcpos, hc⟩ := ih hk
    obtain ⟨s, hspos, hs⟩ := alpha_eq_ofReal_pos b x₀ hA hk
    refine ⟨c * s, mul_pos hcpos hspos, ?_⟩
    rw [Finset.prod_range_succ, hc, hs]
    push_cast
    ring

set_option linter.unusedSectionVars false in
/-- Leading coefficients: `r_k` and `p_k` both lie in `(∏_{j<k} (-α_j)) A^k r₀ + 𝒦_k`. -/
private theorem leading (k : ℕ) :
    (iterate A b x₀ k).r -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) ∈
      subspace A (b - A x₀) k ∧
    (iterate A b x₀ k).p -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) ∈
      subspace A (b - A x₀) k := by
  induction k with
  | zero => constructor <;> · simp [iterate, init]
  | succ k ih =>
    obtain ⟨ihr, ihp⟩ := ih
    have hpow : (A ^ (k + 1)) (b - A x₀) = A ((A ^ k) (b - A x₀)) := by rw [pow_succ']; rfl
    have hmono := subspace_mono A (b - A x₀) (Nat.le_succ k)
    have hmem : (A ^ k) (b - A x₀) ∈ subspace A (b - A x₀) (k + 1) :=
      pow_apply_mem_subspace A _ (Nat.lt_succ_self k)
    have hAp : A (iterate A b x₀ k).p -
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) ∈
          subspace A (b - A x₀) (k + 1) := by
      have h := map_subspace_le A (b - A x₀) k ⟨_, ihp, rfl⟩
      rwa [map_sub, map_smul, ← hpow] at h
    have hr : (iterate A b x₀ (k + 1)).r -
        (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) ∈
          subspace A (b - A x₀) (k + 1) := by
      have key : (iterate A b x₀ (k + 1)).r -
          (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) =
        ((iterate A b x₀ k).r -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) +
          (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) -
          alpha A (iterate A b x₀ k) • (A (iterate A b x₀ k).p -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀)) := by
        rw [iterate_succ_r, Finset.prod_range_succ]
        module
      rw [key]
      exact Submodule.sub_mem _
        (Submodule.add_mem _ (hmono ihr) (Submodule.smul_mem _ _ hmem))
        (Submodule.smul_mem _ _ hAp)
    refine ⟨hr, ?_⟩
    have key : (iterate A b x₀ (k + 1)).p -
        (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀) =
      ((iterate A b x₀ (k + 1)).r -
          (∏ j ∈ Finset.range (k + 1), -alpha A (iterate A b x₀ j)) • (A ^ (k + 1)) (b - A x₀)) +
        beta A (iterate A b x₀ k) • ((iterate A b x₀ k).p -
          (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) +
        beta A (iterate A b x₀ k) •
          ((∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) := by
      rw [iterate_succ_p]
      module
    rw [key]
    exact Submodule.add_mem _ (Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ihp)))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hmem))

omit hA in
/-- Gram–Schmidt normalises with a *positive* leading coefficient:
`⟪gramSchmidtNormed f n, f n⟫ = ‖gramSchmidt f n‖ ≥ 0`. -/
private theorem inner_gramSchmidtNormed_self (f : ℕ → E) (n : ℕ) :
    inner 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 f n) (f n) =
      ((‖InnerProductSpace.gramSchmidt 𝕜 f n‖ : ℝ) : 𝕜) := by
  have hz : ∀ i ∈ Finset.Iio n,
      inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f n)
        ((𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 f i).starProjection (f n)) = 0 := by
    intro i hi
    rw [Submodule.starProjection_singleton, inner_smul_right,
      InnerProductSpace.gramSchmidt_orthogonal 𝕜 f (Finset.mem_Iio.1 hi).ne', mul_zero]
  have hmain : inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f n) (f n) =
      ((‖InnerProductSpace.gramSchmidt 𝕜 f n‖ : 𝕜)) ^ 2 := by
    conv_lhs => rw [InnerProductSpace.gramSchmidt_def' 𝕜 f n]
    rw [inner_add_right, inner_sum, Finset.sum_eq_zero hz, add_zero, inner_self_eq_norm_sq_to_K]
  rw [InnerProductSpace.gramSchmidtNormed, inner_smul_left, hmain, map_inv₀, RCLike.conj_ofReal]
  rcases eq_or_ne (InnerProductSpace.gramSchmidt 𝕜 f n) 0 with h | h
  · simp [h]
  · have h0 : ((‖InnerProductSpace.gramSchmidt 𝕜 f n‖ : ℝ) : 𝕜) ≠ 0 := by
      simpa using norm_ne_zero_iff.2 h
    rw [sq, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-- CG residuals are the Lanczos vectors up to sign: `v_k = (-1)^k r_k / ‖r_k‖`
(Saad, *Iterative Methods*, (6.101); Meurant–Strakoš (3.4)). -/
theorem arnoldi_vec_eq (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    Arnoldi.vec A (b - A x₀) k =
      ((-1 : 𝕜) ^ k * (‖(iterate A b x₀ k).r‖⁻¹ : ℝ)) • (iterate A b x₀ k).r := by
  have hveq : Arnoldi.vec A (b - A x₀) k =
      InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) (b - A x₀)) k := rfl
  -- `v_k` and `r_k` are orthogonal to `𝒦_k`, and both lie in `𝒦_{k+1}`
  have hvperp : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 u (Arnoldi.vec A (b - A x₀) k) = 0 :=
    (Submodule.mem_orthogonal _ _).1 (Arnoldi.vec_mem_orthogonal A (b - A x₀) k)
  have hvperp' : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) u = 0 := fun u hu => by
    rw [← inner_conj_symm, hvperp u hu, map_zero]
  have hrperp : ∀ u ∈ subspace A (b - A x₀) k,
      inner 𝕜 u (iterate A b x₀ k).r = 0 := by
    have h := (isGalerkinIterate b x₀ hA k).orth
    rw [← residual_eq A b x₀ k] at h
    exact (Submodule.mem_orthogonal _ _).1 h
  have hrmem : (iterate A b x₀ k).r ∈ subspace A (b - A x₀) (k + 1) :=
    residual_mem_subspace A b x₀ k
  -- `v_k ≠ 0`: otherwise `𝒦_{k+1} = 𝒦_k` and `r_k ⟂ r_k`
  have hvne : Arnoldi.vec A (b - A x₀) k ≠ 0 := by
    intro h0
    refine hr (inner_self_eq_zero.1 (hrperp _ ?_))
    have hle : subspace A (b - A x₀) (k + 1) ≤ subspace A (b - A x₀) k := by
      rw [← Arnoldi.span_vec A (b - A x₀) (k + 1), Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i k with h | h
      · rw [← Arnoldi.span_vec A (b - A x₀) k]
        exact Submodule.subset_span ⟨i, h, rfl⟩
      · obtain rfl : i = k := le_antisymm (Nat.lt_succ_iff.1 hi) h
        rw [h0]
        exact Submodule.zero_mem _
    exact hle hrmem
  have hnorm : ‖Arnoldi.vec A (b - A x₀) k‖ = 1 := by
    rw [hveq]
    exact InnerProductSpace.gramSchmidtNormed_unit_length' (by rwa [hveq] at hvne)
  -- `r_k` is a multiple of `v_k`, the coefficient being `⟪v_k, r_k⟫`
  have hrep : (iterate A b x₀ k).r =
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
        Arnoldi.vec A (b - A x₀) k := by
    have hzmem : (iterate A b x₀ k).r -
        inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
          Arnoldi.vec A (b - A x₀) k ∈ subspace A (b - A x₀) (k + 1) :=
      Submodule.sub_mem _ hrmem
        (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace A (b - A x₀) k))
    have hzperp : (iterate A b x₀ k).r -
        inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r •
          Arnoldi.vec A (b - A x₀) k ∈ (subspace A (b - A x₀) (k + 1))ᗮ := by
      rw [← Arnoldi.span_vec A (b - A x₀) (k + 1)]
      refine mem_orthogonal_span ?_
      rintro _ ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i k with h | h
      · have hmem : Arnoldi.vec A (b - A x₀) i ∈ subspace A (b - A x₀) k :=
          subspace_mono A (b - A x₀) h (Arnoldi.vec_mem_subspace A (b - A x₀) i)
        rw [inner_sub_right, hrperp _ hmem, inner_smul_right,
          Arnoldi.inner_vec_eq_zero A (b - A x₀) (by omega : i ≠ k), mul_zero, sub_zero]
      · obtain rfl : i = k := le_antisymm (Nat.lt_succ_iff.1 hi) h
        rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
        simp
    have hzero := inner_self_eq_zero (𝕜 := 𝕜).1
      ((Submodule.mem_orthogonal _ _).1 hzperp _ hzmem)
    exact sub_eq_zero.1 hzero
  -- the coefficient is `(-1)^k` times a positive real
  obtain ⟨c, hcpos, hc⟩ := prod_neg_alpha b x₀ hA k hr
  obtain ⟨g, hgpos, hg⟩ : ∃ g : ℝ, 0 < g ∧
      inner 𝕜 (Arnoldi.vec A (b - A x₀) k) ((A ^ k) (b - A x₀)) = (g : 𝕜) := by
    refine ⟨‖InnerProductSpace.gramSchmidt 𝕜 (fun i : ℕ => (A ^ i) (b - A x₀)) k‖, ?_,
      hveq ▸ inner_gramSchmidtNormed_self (fun i : ℕ => (A ^ i) (b - A x₀)) k⟩
    rw [norm_pos_iff]
    intro h0
    exact hvne (by rw [hveq, InnerProductSpace.gramSchmidtNormed, h0, smul_zero])
  have ht : inner 𝕜 (Arnoldi.vec A (b - A x₀) k) (iterate A b x₀ k).r =
      (-1 : 𝕜) ^ k * ((c * g : ℝ) : 𝕜) := by
    have hsplit : (iterate A b x₀ k).r =
        (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀) +
          ((iterate A b x₀ k).r -
            (∏ j ∈ Finset.range k, -alpha A (iterate A b x₀ j)) • (A ^ k) (b - A x₀)) := by
      abel
    rw [hsplit, inner_add_right, hvperp' _ (leading b x₀ hA k).1, add_zero, inner_smul_right,
      hc, hg]
    push_cast
    ring
  have hnr : ‖(iterate A b x₀ k).r‖ = c * g := by
    rw [hrep, norm_smul, hnorm, mul_one, ht, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, RCLike.norm_ofReal, abs_of_pos (mul_pos hcpos hgpos)]
  have hsq : (-1 : 𝕜) ^ k * (-1 : 𝕜) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have h0 : ((c * g : ℝ) : 𝕜) ≠ 0 := by
    simpa using (mul_pos hcpos hgpos).ne'
  rw [hnr, hrep, smul_smul, ht, mul_mul_mul_comm, hsq, one_mul, RCLike.ofReal_inv,
    inv_mul_cancel₀ h0, one_smul]

/-- Termination: `r_k = 0` for `k ≥ grade` (CG is a direct method in `≤ n` steps). -/
theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  rw [residual_eq, sub_eq_zero]
  exact ((isGalerkinIterate b x₀ hA k).apply_eq_of_grade_le hk).symm

/-- Sharpness of `CG.residual_eq_zero_of_grade_le`: before the grade the residual is still
nonzero, so CG takes exactly `grade A r₀` steps, never fewer. A vanishing `r_k` would make `x_k`
an exact solution inside `x₀ + 𝒦_k`, and an exact Krylov solution at step `k` forces the grade
down to `k` (`Krylov.grade_le_of_apply_eq`). -/
theorem residual_ne_zero_of_lt_grade [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : k < grade A (b - A x₀)) : (iterate A b x₀ k).r ≠ 0 := by
  intro h
  rw [residual_eq, sub_eq_zero] at h
  exact absurd (grade_le_of_apply_eq (iterate_sub_mem b x₀ hA k) h.symm) (by omega)

/-! ### Real coefficients and their signs -/

omit hA in
private theorem alpha_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : alpha A (iterate A b x₀ k) =
    ((‖(iterate A b x₀ k).r‖ ^ 2 /
      RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p) : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq, inner_apply_self_ofReal hAs, alpha]

omit hA in
/-- The step length is nonnegative as soon as the current direction has nonnegative `A`-norm,
which for a coercive `A` is automatic (`CG.re_alpha_nonneg`). -/
private theorem re_alpha_nonneg' (hAs : A.IsSymmetric) {k : ℕ}
    (h : 0 ≤ RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p)) :
    0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (sq_nonneg _) h

theorem re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) :=
  re_alpha_nonneg' b x₀ hA.isSymmetric (re_inner_apply_self_nonneg hA _)

omit hA in
private theorem beta_eq_ofReal (k : ℕ) : beta A (iterate A b x₀ k) =
    ((‖(iterate A b x₀ (k + 1)).r‖ ^ 2 / ‖(iterate A b x₀ k).r‖ ^ 2 : ℝ) : 𝕜) := by
  rw [beta_iterate, RCLike.ofReal_div, ← inner_self_eq_ofReal_norm_sq,
    ← inner_self_eq_ofReal_norm_sq]

omit hA in
private theorem re_beta_nonneg (k : ℕ) : 0 ≤ RCLike.re (beta A (iterate A b x₀ k)) := by
  rw [beta_eq_ofReal b x₀ k, RCLike.ofReal_re]
  positivity

omit hA in
/-- `re (α_k z) = re α_k * re z`: the step length is real. -/
private theorem re_alpha_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (alpha A (iterate A b x₀ k) * z) =
      RCLike.re (alpha A (iterate A b x₀ k)) * RCLike.re z := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
private theorem re_beta_mul (k : ℕ) (z : 𝕜) :
    RCLike.re (beta A (iterate A b x₀ k) * z) =
      RCLike.re (beta A (iterate A b x₀ k)) * RCLike.re z := by
  rw [beta_eq_ofReal b x₀ k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- `⟪p_i, p_j⟫ ≥ 0` for CG on SPD systems (ingredient of Steihaug's theorem). -/
theorem re_inner_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  have key : ∀ m n : ℕ, m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (iterate A b x₀ n).p) := by
    intro m
    induction m with
    | zero =>
      intro n _
      rw [direction_zero, inner_residual_direction_eq b x₀ hA (Nat.zero_le n), RCLike.ofReal_re]
      positivity
    | succ m ih =>
      intro n hn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta, map_add,
        inner_residual_direction_eq b x₀ hA (show m + 1 ≤ n by omega), RCLike.ofReal_re,
        re_beta_mul b x₀]
      exact add_nonneg (by positivity)
        (mul_nonneg (re_beta_nonneg b x₀ m) (ih n (by omega)))
  rcases le_total i j with h | h
  · exact key i j h
  · rw [← inner_conj_symm, RCLike.conj_re]
    exact key j i h

/-- Partial sums of `α_j p_j` have nonnegative inner products with the directions. -/
private theorem re_inner_sub_iterate_direction_nonneg {k m : ℕ} (hkm : k ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ k).x)
      (iterate A b x₀ j).p) := by
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ k).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ k).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hA.isSymmetric, map_add,
      re_alpha_mul b x₀ hA.isSymmetric]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg b x₀ hA m)
      (re_inner_direction_nonneg b x₀ hA m j))

/-! ### Error identities and monotonicity -/

section Errors

variable {xstar : E} (hstar : A xstar = b)
include hstar

/-- Hestenes–Stiefel Thm 6:1 / Meurant–Strakoš Thm 11:
`‖ε_k‖_A² - ‖ε_{k+1}‖_A² = α_k ‖r_k‖²`. -/
theorem energyNorm_error_sq_sub (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 -
        energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 =
      RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 := by
  have alg : ∀ (u q : E) (a R : 𝕜), inner 𝕜 (A u) q = R → inner 𝕜 (A q) u = R →
      (starRingEnd 𝕜) a = a → a * inner 𝕜 (A q) q = R →
      inner 𝕜 (A (u - a • q)) (u - a • q) = inner 𝕜 (A u) u - a * R := by
    intro u q a R h1 h2 h3 h4
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, h1, h2, h3]
    linear_combination a * h4
  have hAe : A (xstar - (iterate A b x₀ k).x) = (iterate A b x₀ k).r := by
    rw [map_sub, hstar, ← residual_eq]
  have hsub : xstar - (iterate A b x₀ (k + 1)).x =
      (xstar - (iterate A b x₀ k).x) - alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hup : inner 𝕜 (A (xstar - (iterate A b x₀ k).x)) (iterate A b x₀ k).p =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
    rw [hAe, (invariant b x₀ hA k).diag]
  have hpu : inner 𝕜 (A (iterate A b x₀ k).p) (xstar - (iterate A b x₀ k).x) =
      inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r := by
    rw [hA.isSymmetric, hAe, ← inner_conj_symm, (invariant b x₀ hA k).diag, inner_self_conj]
  have hre : RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ k).x))
        (xstar - (iterate A b x₀ k).x) -
      alpha A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (iterate A b x₀ k).r) =
      RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ k).x)) (xstar - (iterate A b x₀ k).x)) -
        RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 := by
    rw [map_sub, re_alpha_mul b x₀ hA.isSymmetric, inner_self_eq_norm_sq]
  rw [hA.energyNorm_sq, hA.energyNorm_sq, hsub,
    alg _ _ _ _ hup hpu (conj_alpha hA.isSymmetric _)
      (alpha_mul_inner_apply_direction b x₀ hA k), hre]
  ring

/-- `‖ε_k‖_A² = ∑_{j ≥ k} α_j ‖r_j‖²` (finite sum up to the grade). -/
theorem energyNorm_error_sq_eq_sum [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 =
      ∑ j ∈ Finset.Ico k (grade A (b - A x₀)),
        RCLike.re (alpha A (iterate A b x₀ j)) * ‖(iterate A b x₀ j).r‖ ^ 2 := by
  have hzero : ∀ m, grade A (b - A x₀) ≤ m →
      energyNorm A (xstar - (iterate A b x₀ m).x) ^ 2 = 0 := by
    intro m hm
    have hr := residual_eq_zero_of_grade_le b x₀ hA hm
    rw [residual_eq, sub_eq_zero] at hr
    have hx : xstar = (iterate A b x₀ m).x := hA.isCoercive.injective (hstar.trans hr)
    rw [hx, sub_self]
    simp [energyNorm]
  have tel : ∀ n : ℕ, energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 =
      (∑ j ∈ Finset.Ico k (k + n), RCLike.re (alpha A (iterate A b x₀ j)) *
        ‖(iterate A b x₀ j).r‖ ^ 2) +
      energyNorm A (xstar - (iterate A b x₀ (k + n)).x) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := energyNorm_error_sq_sub b x₀ hA hstar (k + n)
      rw [show k + (n + 1) = k + n + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
      linarith [ih]
  rcases Nat.lt_or_ge (grade A (b - A x₀)) k with h | h
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, hzero k (le_of_lt h)]
  · have hn := tel (grade A (b - A x₀) - k)
    rw [show k + (grade A (b - A x₀) - k) = grade A (b - A x₀) by omega] at hn
    rw [hn, hzero _ le_rfl, add_zero]

/-- Hestenes–Stiefel Thm 6:3 / Meurant–Strakoš Thm 12: the Euclidean error is nonincreasing.

Statement correction: the skeleton had no finite-dimensionality hypothesis.  The proof (and the
Hestenes–Stiefel argument) needs the expansion `x* - x_k = ∑_{j ≥ k} α_j p_j`, i.e. finite
termination of the recurrence, so `[FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]` was added,
matching `energyNorm_error_sq_eq_sum` above.  (Without it the statement is an infinite-dimensional
convergence result; see the note in `plans/backbone.md` §3.11 that Hilbert-space extensions are
phase 3.) -/
theorem norm_error_antitone [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  refine antitone_nat_of_succ_le fun k => ?_
  set m := max (k + 1) (grade A (b - A x₀)) with hm
  have hxm : xstar = (iterate A b x₀ m).x := by
    have hr := residual_eq_zero_of_grade_le b x₀ hA (le_max_right (k + 1) (grade A (b - A x₀)))
    rw [residual_eq, sub_eq_zero] at hr
    exact hA.isCoercive.injective (hstar.trans hr)
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (xstar - (iterate A b x₀ (k + 1)).x)
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    refine mul_nonneg (re_alpha_nonneg b x₀ hA k) ?_
    rw [hxm]
    exact re_inner_sub_iterate_direction_nonneg b x₀ hA (le_max_left (k + 1) _) k
  have hsq : ‖xstar - (iterate A b x₀ (k + 1)).x‖ ^ 2 ≤ ‖xstar - (iterate A b x₀ k).x‖ ^ 2 := by
    rw [hexp, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p‖]
  nlinarith [norm_nonneg (xstar - (iterate A b x₀ (k + 1)).x),
    norm_nonneg (xstar - (iterate A b x₀ k).x)]

/-- The energy norm of the CG error never increases: one step subtracts the nonnegative amount
`α_k ‖r_k‖²` from its square (`CG.energyNorm_error_sq_sub`). Unlike the Euclidean statement
`CG.norm_error_antitone`, this needs no finite-dimensionality, because the identity behind it is
local to a single step rather than an expansion of the whole remaining error. -/
theorem energyNorm_error_antitone :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h := energyNorm_error_sq_sub b x₀ hA hstar k
  have hnn : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2 :=
    mul_nonneg (re_alpha_nonneg b x₀ hA k) (sq_nonneg _)
  nlinarith [energyNorm_nonneg A (xstar - (iterate A b x₀ k).x),
    energyNorm_nonneg A (xstar - (iterate A b x₀ (k + 1)).x)]

end Errors

/-! ### Steihaug's theorem, for a symmetric but possibly indefinite operator

Coercivity enters the sign lemmas above only through `0 ≤ re ⟪A p_j, p_j⟫` and the
nondegeneracy it gives.  Assuming that quantity *positive* at the steps taken so far — which is
precisely what a trust-region method monitors — runs the same chain on a symmetric, possibly
indefinite `A`, and makes the conclusion strict. -/

omit hA in
/-- The invariant at every step up to `k`, when the directions taken so far have positive
`A`-norm. -/
private theorem invariant_le (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {m : ℕ} (hm : m ≤ k) : Invariant A b x₀ m := by
  refine invariant_of b x₀ hAs m fun j hj h => ?_
  have hj' := hpos j (lt_of_lt_of_le hj hm)
  rw [h, map_zero] at hj'
  exact absurd hj' (lt_irrefl 0)

omit hA in
/-- `⟪r_i, r_j⟫ = 0` for `i ≠ j` up to step `k` (`CG.inner_residual_eq_zero` localized). -/
private theorem inner_residual_eq_zero' (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0 := by
  have key : ∀ m, m ≤ k → ∀ n, n < m →
      inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ n).r = 0 := by
    intro m hm n hnm
    exact inner_residual_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant_le b x₀ hAs hpos hm).rp l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, key j hj i h', map_zero]
  · exact key i hi j h'

omit hA in
/-- `⟪r_i, p_j⟫ = ‖r_j‖²` for `i ≤ j ≤ k` (`CG.inner_residual_direction_eq` localized). -/
private theorem inner_residual_direction_eq' (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p =
      ((‖(iterate A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) := by
  revert hjk
  induction j, hij using Nat.le_induction with
  | base =>
    intro hjk
    rw [(invariant_le b x₀ hAs hpos hjk).diag, inner_self_eq_ofReal_norm_sq]
  | succ j hij ih =>
    intro hjk
    rw [iterate_succ_p, inner_add_right, inner_smul_right, ih (by omega),
      inner_residual_eq_zero' b x₀ hAs hpos (by omega) hjk (show i ≠ j + 1 by omega), zero_add,
      ← inner_self_eq_ofReal_norm_sq, ← inner_self_eq_ofReal_norm_sq, beta_mul_inner_self A b x₀ j]

omit hA in
/-- `re ⟪p_i, p_j⟫ ≥ 0` up to step `k` (`CG.re_inner_direction_nonneg` localized). -/
private theorem re_inner_direction_nonneg' (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  have key : ∀ m, m ≤ k → ∀ n, n ≤ k → m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (iterate A b x₀ n).p) := by
    intro m
    induction m with
    | zero =>
      intro _ n hn _
      rw [direction_zero, inner_residual_direction_eq' b x₀ hAs hpos (Nat.zero_le n) hn,
        RCLike.ofReal_re]
      positivity
    | succ m ih =>
      intro hm n hn hmn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta, map_add,
        inner_residual_direction_eq' b x₀ hAs hpos (show m + 1 ≤ n by omega) hn, RCLike.ofReal_re,
        re_beta_mul b x₀]
      exact add_nonneg (by positivity)
        (mul_nonneg (re_beta_nonneg b x₀ m) (ih (by omega) n hn (by omega)))
  rcases le_total i j with h | h
  · exact key i hi j hj h
  · rw [← inner_conj_symm, RCLike.conj_re]
    exact key j hj i hi h

omit hA in
/-- `re ⟪x_m - x_l, p_j⟫ ≥ 0` up to step `k`
(`CG.re_inner_sub_iterate_direction_nonneg` localized). -/
private theorem re_inner_sub_iterate_direction_nonneg' (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ j).p) (iterate A b x₀ j).p))
    {l m : ℕ} (hlm : l ≤ m) (hm : m ≤ k) {j : ℕ} (hj : j ≤ k) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ l).x)
      (iterate A b x₀ j).p) := by
  revert hm
  induction m, hlm using Nat.le_induction with
  | base => intro _; simp
  | succ m hlm ih =>
    intro hm
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ l).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ l).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hAs, map_add, re_alpha_mul b x₀ hAs]
    exact add_nonneg (ih (by omega))
      (mul_nonneg (re_alpha_nonneg' b x₀ hAs (le_of_lt (hpos m (by omega))))
        (re_inner_direction_nonneg' b x₀ hAs hpos (by omega) hj))

omit hA in
/-- Steihaug's theorem for a symmetric, possibly indefinite `A`: started at `x₀ = 0`, the CG
iterates grow in norm at every step whose direction has positive `A`-norm,
`‖x_i‖ < ‖x_{i+1}‖` for `i < k` whenever `0 < re ⟪A p_j, p_j⟫` for all `j < k`.  This is the
hypothesis a trust-region method can check as it goes, and it is what makes the CG path leave
the trust region monotonically.  The coercive `CG.norm_iterate_monotone` is the corollary in
which the hypothesis holds at every step the iteration moves at all. -/
theorem norm_iterate_lt_of_re_inner_apply_direction_pos (hAs : A.IsSymmetric) {k : ℕ}
    (hpos : ∀ j < k, 0 < RCLike.re (inner 𝕜 (A (iterate A b 0 j).p) (iterate A b 0 j).p))
    {i : ℕ} (hi : i < k) : ‖(iterate A b 0 i).x‖ < ‖(iterate A b 0 (i + 1)).x‖ := by
  have hp := hpos i hi
  have hpne : (iterate A b 0 i).p ≠ 0 := by
    intro h
    rw [h, map_zero, inner_zero_left, map_zero] at hp
    exact lt_irrefl 0 hp
  have hrne : (iterate A b 0 i).r ≠ 0 := fun h =>
    hpne (direction_eq_zero_of_residual_eq_zero A b 0 h)
  have hαpos : 0 < RCLike.re (alpha A (iterate A b 0 i)) := by
    rw [alpha_eq_ofReal b 0 hAs i, RCLike.ofReal_re]
    exact div_pos (pow_pos (norm_pos_iff.2 hrne) 2) hp
  have hαne : alpha A (iterate A b 0 i) ≠ 0 := fun h => by
    rw [h, map_zero] at hαpos; exact lt_irrefl 0 hαpos
  have hxp : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 i).p) := by
    have h := re_inner_sub_iterate_direction_nonneg' b 0 hAs hpos (Nat.zero_le i)
      (le_of_lt hi) (le_of_lt hi)
    rwa [show (iterate A b 0 0).x = 0 from rfl, sub_zero] at h
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x
      (alpha A (iterate A b 0 i) • (iterate A b 0 i).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hAs]
    exact mul_nonneg (le_of_lt hαpos) hxp
  have hnz : 0 < ‖alpha A (iterate A b 0 i) • (iterate A b 0 i).p‖ := by
    rw [norm_smul]
    exact mul_pos (norm_pos_iff.2 hαne) (norm_pos_iff.2 hpne)
  have hsq : ‖(iterate A b 0 i).x‖ ^ 2 < ‖(iterate A b 0 (i + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [hnz]
  nlinarith [norm_nonneg (iterate A b 0 i).x, norm_nonneg (iterate A b 0 (i + 1)).x]

/-- Steihaug: `‖x_k‖` is nondecreasing for CG started at `x₀ = 0`.  A coercive `A` makes
`0 < re ⟪A p_j, p_j⟫` hold at every step before the residual dies
(`CG.re_inner_apply_direction_pos`), and once it dies the iterate stops moving. -/
theorem norm_iterate_monotone : Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  refine monotone_nat_of_le_succ fun k => ?_
  by_cases hr : (iterate A b 0 k).r = 0
  · have h : (iterate A b 0 (k + 1)).x = (iterate A b 0 k).x := by
      rw [iterate_succ_x, direction_eq_zero_of_residual_eq_zero A b 0 hr, smul_zero, add_zero]
    exact le_of_eq (congrArg norm h.symm)
  · exact le_of_lt (norm_iterate_lt_of_re_inner_apply_direction_pos b hA.isSymmetric
      (k := k + 1) (fun j hj => re_inner_apply_direction_pos b 0 hA
        (residual_ne_zero_of_le b 0 hr (by omega))) (Nat.lt_succ_self k))

section ThreeTerm

omit hA
variable (A)

/-! ### The three-term form (Saad, *Iterative Methods*, §6.7.2, Alg 6.19)

`γ_m = ⟪r_m, r_m⟫ / ⟪A r_m, r_m⟫`, `ρ_0 = 1`,
`ρ_m = (1 - (γ_m/γ_{m-1}) (‖r_m‖²/‖r_{m-1}‖²) / ρ_{m-1})⁻¹`, and
`x_{m+1} = ρ_m (x_m + γ_m r_m) + (1 - ρ_m) x_{m-1}`,
`r_{m+1} = ρ_m (r_m - γ_m A r_m) + (1 - ρ_m) r_{m-1}` (Saad (6.96)–(6.98)). -/

/-- `γ_m = ⟪r_m, r_m⟫ / ⟪A r_m, r_m⟫` (Saad, *Iterative Methods*, (6.97)). -/
noncomputable def gamma (m : ℕ) : 𝕜 :=
  inner 𝕜 (iterate A b x₀ m).r (iterate A b x₀ m).r /
    inner 𝕜 (A (iterate A b x₀ m).r) (iterate A b x₀ m).r

/-- `ρ_m` of Saad, *Iterative Methods*, (6.98), with `ρ_0 = 1`. -/
noncomputable def rho : ℕ → 𝕜
  | 0 => 1
  | m + 1 => (1 - gamma A b x₀ (m + 1) / gamma A b x₀ m *
      ((‖(iterate A b x₀ (m + 1)).r‖ ^ 2 / ‖(iterate A b x₀ m).r‖ ^ 2 : ℝ) : 𝕜) / rho m)⁻¹

variable {A}

/-! #### Scalar identities behind the three-term form -/

private theorem rho_succ (m : ℕ) : rho A b x₀ (m + 1) =
    (1 - gamma A b x₀ (m + 1) / gamma A b x₀ m * beta A (iterate A b x₀ m) /
      rho A b x₀ m)⁻¹ := by
  rw [beta_eq_ofReal b x₀ m, rho]

private theorem inner_apply_residual_self_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) :
    inner 𝕜 (A (iterate A b x₀ k).r) (iterate A b x₀ k).r ≠ 0 :=
  fun h => hk (eq_zero_of_inner_apply_self_eq_zero hA h)

private theorem inner_apply_direction_self_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) :
    inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p ≠ 0 := by
  intro h
  exact absurd (h ▸ re_inner_apply_direction_pos b x₀ hA hk) (by simp)

private theorem gamma_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) : gamma A b x₀ k ≠ 0 :=
  div_ne_zero (fun h => hk (inner_self_eq_zero.1 h))
    (inner_apply_residual_self_ne_zero b x₀ hA hk)

private theorem alpha_ne_zero (hA : A.IsSymmetricCoercive) {k : ℕ}
    (hk : (iterate A b x₀ k).r ≠ 0) : alpha A (iterate A b x₀ k) ≠ 0 :=
  div_ne_zero (fun h => hk (inner_self_eq_zero.1 h))
    (inner_apply_direction_self_ne_zero b x₀ hA hk)

/-- The Hestenes–Stiefel identity `α_m ⟪A p_{m+1}, p_{m+1}⟫ = α_m ⟪A r_{m+1}, r_{m+1}⟫ -
β_m ⟪r_{m+1}, r_{m+1}⟫`, the bridge between the two- and three-term recurrences.  It holds
without any nondegeneracy hypothesis. -/
private theorem alpha_mul_inner_apply_direction_succ (hA : A.IsSymmetricCoercive) (m : ℕ) :
    alpha A (iterate A b x₀ m) *
        inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p =
      alpha A (iterate A b x₀ m) *
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r -
        beta A (iterate A b x₀ m) *
          inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
  have alg : ∀ (u q : E) (c : 𝕜), (starRingEnd 𝕜) c = c →
      inner 𝕜 (A (u + c • q)) (u + c • q) = inner 𝕜 (A u) u + c * inner 𝕜 (A u) q +
        c * inner 𝕜 (A q) u + c * c * inner 𝕜 (A q) q := by
    intro u q c hc
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hc]
    ring
  have hT : alpha A (iterate A b x₀ m) *
      inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ m).p =
        -inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
    rw [hA.isSymmetric, ← inner_smul_right, alpha_smul_apply_direction, inner_sub_right,
      inner_residual_eq_zero b x₀ hA (show m + 1 ≠ m by omega), zero_sub]
  have hT' : alpha A (iterate A b x₀ m) *
      inner 𝕜 (A (iterate A b x₀ m).p) (iterate A b x₀ (m + 1)).r =
        -inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r := by
    rw [← conj_alpha hA.isSymmetric (iterate A b x₀ m), ← inner_smul_left,
      alpha_smul_apply_direction,
      inner_sub_left, inner_residual_eq_zero b x₀ hA (show m ≠ m + 1 by omega), zero_sub]
  have hQ := alpha_mul_inner_apply_direction b x₀ hA m
  have hB := beta_mul_inner_self A b x₀ m
  rw [iterate_succ_p, alg _ _ _ (conj_beta A (iterate A b x₀ m))]
  linear_combination beta A (iterate A b x₀ m) * hT + beta A (iterate A b x₀ m) * hT' +
    beta A (iterate A b x₀ m) * beta A (iterate A b x₀ m) * hQ + beta A (iterate A b x₀ m) * hB

/-- `ρ_{m+1} = ⟪A r_{m+1}, r_{m+1}⟫ / ⟪A p_{m+1}, p_{m+1}⟫`. -/
private theorem rho_succ_eq_div (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hm : (iterate A b x₀ m).r ≠ 0) (hm1 : (iterate A b x₀ (m + 1)).r ≠ 0)
    (ih : alpha A (iterate A b x₀ m) = rho A b x₀ m * gamma A b x₀ m) :
    rho A b x₀ (m + 1) =
      inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r /
        inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p := by
  have hS := inner_apply_residual_self_ne_zero b x₀ hA hm1
  have hQ := inner_apply_direction_self_ne_zero b x₀ hA hm1
  have hg := gamma_ne_zero b x₀ hA hm
  have ha := alpha_ne_zero b x₀ hA hm
  have hK := alpha_mul_inner_apply_direction_succ b x₀ hA m
  have hrhon : rho A b x₀ m = alpha A (iterate A b x₀ m) / gamma A b x₀ m := by
    rw [ih]; field_simp
  have hX : (1 : 𝕜) - gamma A b x₀ (m + 1) / gamma A b x₀ m * beta A (iterate A b x₀ m) /
      rho A b x₀ m = inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p /
        inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r := by
    rw [hrhon, show gamma A b x₀ (m + 1) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r from rfl]
    field_simp
    linear_combination -hK
  rw [rho_succ b x₀ m, hX, inv_div]

/-- `α_m = ρ_m γ_m` (Saad, *Iterative Methods*, (6.97)–(6.98)). -/
private theorem alpha_eq_rho_mul_gamma (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    alpha A (iterate A b x₀ m) = rho A b x₀ m * gamma A b x₀ m := by
  induction m with
  | zero => rw [rho, one_mul, alpha, gamma, direction_zero]
  | succ m ih =>
    have hm := hr m (by omega)
    have hm1 := hr (m + 1) le_rfl
    have hS := inner_apply_residual_self_ne_zero b x₀ hA hm1
    have hQ := inner_apply_direction_self_ne_zero b x₀ hA hm1
    rw [rho_succ_eq_div b x₀ hA m hm hm1 (ih fun j hj => hr j (by omega)),
      show gamma A b x₀ (m + 1) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).r) (iterate A b x₀ (m + 1)).r from rfl,
      show alpha A (iterate A b x₀ (m + 1)) =
        inner 𝕜 (iterate A b x₀ (m + 1)).r (iterate A b x₀ (m + 1)).r /
          inner 𝕜 (A (iterate A b x₀ (m + 1)).p) (iterate A b x₀ (m + 1)).p from rfl]
    field_simp

/-- `α_m (ρ_{m+1} - 1) = α_{m+1} β_m`. -/
private theorem alpha_mul_rho_succ_sub_one (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m + 1, (iterate A b x₀ j).r ≠ 0) :
    alpha A (iterate A b x₀ m) * (rho A b x₀ (m + 1) - 1) =
      alpha A (iterate A b x₀ (m + 1)) * beta A (iterate A b x₀ m) := by
  have hm := hr m (by omega)
  have hm1 := hr (m + 1) le_rfl
  have hQ := inner_apply_direction_self_ne_zero b x₀ hA hm1
  have hK := alpha_mul_inner_apply_direction_succ b x₀ hA m
  have ha' := alpha_mul_inner_apply_direction b x₀ hA (m + 1)
  rw [rho_succ_eq_div b x₀ hA m hm hm1
    (alpha_eq_rho_mul_gamma b x₀ hA m fun j hj => hr j (by omega))]
  field_simp
  linear_combination -hK - beta A (iterate A b x₀ m) * ha'

/-- Saad, *Iterative Methods*, (6.96): `x_{m+1} = ρ_m (x_m + γ_m r_m) + (1 - ρ_m) x_{m-1}`
(with `x_{-1}` read as `x_0`, harmless since `1 - ρ_0 = 0`), valid while `r_j ≠ 0` for
`j ≤ m`. -/
theorem iterate_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).x =
      rho A b x₀ m • ((iterate A b x₀ m).x + gamma A b x₀ m • (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).x := by
  cases m with
  | zero =>
    have h0 : alpha A (iterate A b x₀ 0) = gamma A b x₀ 0 := by
      rw [alpha, gamma, direction_zero]
    rw [iterate_succ_x, h0, rho]
    simp [init]
  | succ n =>
    have hn := hr n (by omega)
    have ha := alpha_ne_zero b x₀ hA hn
    have hrho := alpha_mul_rho_succ_sub_one b x₀ hA n hr
    have hag := alpha_eq_rho_mul_gamma b x₀ hA (n + 1) hr
    have hpn : (iterate A b x₀ n).p = (alpha A (iterate A b x₀ n))⁻¹ •
        ((iterate A b x₀ (n + 1)).x - (iterate A b x₀ n).x) := by
      rw [iterate_succ_x, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [Nat.add_sub_cancel, iterate_succ_x, iterate_succ_p, hpn]
    match_scalars
    · field_simp
      linear_combination -hrho
    · field_simp
      linear_combination hag
    · field_simp
      linear_combination hrho

/-- Saad, *Iterative Methods*, (6.96) for the residuals:
`r_{m+1} = ρ_m (r_m - γ_m A r_m) + (1 - ρ_m) r_{m-1}`. -/
theorem residual_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).r =
      rho A b x₀ m • ((iterate A b x₀ m).r - gamma A b x₀ m • A (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).r := by
  cases m with
  | zero =>
    have h0 : alpha A (iterate A b x₀ 0) = gamma A b x₀ 0 := by
      rw [alpha, gamma, direction_zero]
    rw [iterate_succ_r, h0, rho, direction_zero]
    simp
  | succ n =>
    have hn := hr n (by omega)
    have ha := alpha_ne_zero b x₀ hA hn
    have hrho := alpha_mul_rho_succ_sub_one b x₀ hA n hr
    have hag := alpha_eq_rho_mul_gamma b x₀ hA (n + 1) hr
    have hpn : A (iterate A b x₀ n).p = (alpha A (iterate A b x₀ n))⁻¹ •
        ((iterate A b x₀ n).r - (iterate A b x₀ (n + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [Nat.add_sub_cancel, iterate_succ_r, iterate_succ_p, map_add, map_smul, hpn]
    match_scalars
    · field_simp
      linear_combination -hrho
    · field_simp
      linear_combination -hag
    · field_simp
      linear_combination hrho

end ThreeTerm

end CG
