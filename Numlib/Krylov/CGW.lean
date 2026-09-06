import Numlib.Krylov.CG

/-!
# The Concus–Golub–Widlund recurrence

The recurrence of [concus1976generalized] and [widlund1978lanczos], in the form
[saad2003iterative] §9.6 gives it.

A conjugate-gradient-shaped two-term recurrence for an operator that differs from the identity by a
*skew-adjoint* one, `B = 1 - S` with `S* = -S`, equivalently `B + B* = 2`
(`LinearMap.IsShiftedSkewAdjoint`).  Such a `B` is not self-adjoint, so the conjugate gradient
theory of `Numlib/Krylov/CG.lean` does not apply; what survives is that `B*` is again a polynomial
of degree one in `B`, which keeps the Arnoldi process short and lets the same two-term recurrence be
run with **the sign of `β` reversed**:

`α_k = ⟪r_k, r_k⟫ / ⟪p_k, B p_k⟫`, `x_{k+1} = x_k + α_k p_k`, `r_{k+1} = r_k - α_k B p_k`,
`β_k = -⟪r_{k+1}, r_{k+1}⟫ / ⟪r_k, r_k⟫`, `p_{k+1} = r_{k+1} + β_k p_k`.

`CGW.isGalerkinIterate` is the point of the module: the iterate is the Galerkin (FOM) iterate over
the Krylov space, so `CGW` is a projection method exactly as CG is.  The reversed sign is what makes
it one: in the step that proves the directions one-sidedly `B`-conjugate, `⟪p_k, B r_{k+1}⟫` and
`β_k ⟪p_k, B p_k⟫` cancel only for that sign.

## The real field

The module is over `ℝ`.  Over `ℂ` the recurrence above is **not** a projection method, and the
obstruction is visible already at step two: `⟪p_0, B p_1⟫ = ‖r_1‖² (conj α_0⁻¹ - α_0⁻¹)`, which
vanishes exactly when the step length `α_0` is real.  Over `ℝ` it always is, because
`⟪p, B p⟫ = ⟪p, p⟫` (`LinearMap.IsShiftedSkewAdjoint.inner_self`, the skew part having no quadratic
form); over `ℂ` the quadratic form of a skew-adjoint operator is purely imaginary and generally
nonzero, `α_0` is genuinely complex, and `⟪r_1, r_2⟫ ≠ 0`.  Concus–Golub–Widlund is an algorithm for
real nearly symmetric systems, and this is the reason.

## Main statements

* `CGW.inner_residual_eq_zero`: the residuals are mutually orthogonal;
* `CGW.inner_direction_apply_direction_eq_zero`: the directions are `B`-conjugate in the one
  direction `⟪p_i, B p_j⟫ = 0` for `i < j` — unlike CG this is *not* symmetric in `i` and `j`,
  because `B` is not;
* `CGW.span_direction_eq`, `CGW.span_residual_eq`: the directions and the residuals span the Krylov
  spaces;
* `CGW.isGalerkinIterate`: the iterate realises the Galerkin specification.
-/

open Krylov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LinearMap

/-- **A shifted skew-adjoint operator**: `B + B* = 2`, that is `B = 1 - S` with `S` skew-adjoint.
The preconditioned operator `M⁻¹ A` of a splitting `A = M - N` with `M` the Hermitian part of `A` is
of this shape in the `M`-inner product, which is what the Concus–Golub–Widlund algorithm
exploits. -/
def IsShiftedSkewAdjoint (B : E →ₗ[ℝ] E) : Prop :=
  ∀ x y, inner ℝ (B x) y + inner ℝ x (B y) = 2 * inner ℝ x y

namespace IsShiftedSkewAdjoint

variable {B : E →ₗ[ℝ] E}

/-- **The skew part carries no quadratic form**: `⟪x, B x⟫ = ⟪x, x⟫`.  Over `ℝ` this is what makes
the Concus–Golub–Widlund step length positive and the whole recurrence well posed. -/
theorem inner_self (h : IsShiftedSkewAdjoint B) (x : E) : inner ℝ x (B x) = inner ℝ x x := by
  have h1 := h x x
  have h2 := real_inner_comm (B x) x
  linarith

/-- Moving `B` across the inner product costs the shift: `⟪B x, y⟫ = 2 ⟪x, y⟫ - ⟪x, B y⟫`. -/
theorem inner_left (h : IsShiftedSkewAdjoint B) (x y : E) :
    inner ℝ (B x) y = 2 * inner ℝ x y - inner ℝ x (B y) := by
  have h1 := h x y
  linarith

end IsShiftedSkewAdjoint

end LinearMap

namespace CGW

open CG (State)

/-- The Concus–Golub–Widlund step length `α = ⟪r, r⟫ / ⟪p, B p⟫`. -/
noncomputable def alpha (B : E →ₗ[ℝ] E) (s : State E) : ℝ :=
  inner ℝ s.r s.r / inner ℝ s.p (B s.p)

/-- One Concus–Golub–Widlund step: the conjugate gradient step with the sign of `β` reversed. -/
noncomputable def step (B : E →ₗ[ℝ] E) (s : State E) : State E :=
  let α := alpha B s
  let r' := s.r - α • B s.p
  let β : ℝ := -(inner ℝ r' r' / inner ℝ s.r s.r)
  { x := s.x + α • s.p, r := r', p := r' + β • s.p }

/-- The direction update coefficient `β = -⟪r', r'⟫ / ⟪r, r⟫`, the negative of the conjugate
gradient one. -/
noncomputable def beta (B : E →ₗ[ℝ] E) (s : State E) : ℝ :=
  -(inner ℝ (step B s).r (step B s).r / inner ℝ s.r s.r)

/-- Initial state `x₀, r₀ = b - B x₀, p₀ = r₀`. -/
def init (B : E →ₗ[ℝ] E) (b x₀ : E) : State E := { x := x₀, r := b - B x₀, p := b - B x₀ }

/-- The `k`-th Concus–Golub–Widlund state. -/
noncomputable def iterate (B : E →ₗ[ℝ] E) (b x₀ : E) (k : ℕ) : State E :=
  (step B)^[k] (init B b x₀)

variable (B : E →ₗ[ℝ] E) (b x₀ : E)

@[simp] theorem init_x : (init B b x₀).x = x₀ := rfl

@[simp] theorem init_r : (init B b x₀).r = b - B x₀ := rfl

@[simp] theorem init_p : (init B b x₀).p = b - B x₀ := rfl

@[simp] theorem iterate_zero : iterate B b x₀ 0 = init B b x₀ := rfl

/-- The recurrence: state `k + 1` is one `CGW.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) : iterate B b x₀ (k + 1) = step B (iterate B b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update `x' = x + α p`. -/
theorem step_x (s : State E) : (step B s).x = s.x + alpha B s • s.p := rfl

/-- The residual update `r' = r - α B p`. -/
theorem step_r (s : State E) : (step B s).r = s.r - alpha B s • B s.p := rfl

/-- The direction update `p' = r' + β p`. -/
theorem step_p (s : State E) : (step B s).p = (step B s).r + beta B s • s.p := rfl

/-- The state's residual field is the true residual `b - B x`. -/
theorem residual_eq (k : ℕ) : (iterate B b x₀ k).r = b - B (iterate B b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_r, step_x, ih, map_add, map_smul, sub_sub]

/-! ### Unfolding the recurrence -/

/-- `x_{k+1} = x_k + α_k p_k`. -/
theorem iterate_succ_x (k : ℕ) : (iterate B b x₀ (k + 1)).x =
    (iterate B b x₀ k).x + alpha B (iterate B b x₀ k) • (iterate B b x₀ k).p := by
  rw [iterate_succ, step_x]

/-- `r_{k+1} = r_k - α_k B p_k`. -/
theorem iterate_succ_r (k : ℕ) : (iterate B b x₀ (k + 1)).r =
    (iterate B b x₀ k).r - alpha B (iterate B b x₀ k) • B (iterate B b x₀ k).p := by
  rw [iterate_succ, step_r]

/-- `p_{k+1} = r_{k+1} + β_k p_k`. -/
theorem iterate_succ_p (k : ℕ) : (iterate B b x₀ (k + 1)).p =
    (iterate B b x₀ (k + 1)).r + beta B (iterate B b x₀ k) • (iterate B b x₀ k).p := by
  rw [iterate_succ]; exact step_p B _

/-- `β_k = -‖r_{k+1}‖² / ‖r_k‖²`, written as a quotient of inner products. -/
theorem beta_iterate (k : ℕ) : beta B (iterate B b x₀ k) =
    -(inner ℝ (iterate B b x₀ (k + 1)).r (iterate B b x₀ (k + 1)).r /
      inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r) := by
  rw [beta, iterate_succ]

/-- `p₀ = r₀`. -/
theorem direction_zero : (iterate B b x₀ 0).p = (iterate B b x₀ 0).r := rfl

/-- `α_k B p_k = r_k - r_{k+1}`: the only way `B` enters the residual recurrence. -/
theorem alpha_smul_apply_direction (k : ℕ) :
    alpha B (iterate B b x₀ k) • B (iterate B b x₀ k).p =
      (iterate B b x₀ k).r - (iterate B b x₀ (k + 1)).r := by
  rw [iterate_succ_r]; abel

/-- If the residual vanishes so does the search direction. -/
theorem direction_eq_zero_of_residual_eq_zero {k : ℕ} (hr : (iterate B b x₀ k).r = 0) :
    (iterate B b x₀ k).p = 0 := by
  cases k with
  | zero => rw [direction_zero]; exact hr
  | succ k =>
    rw [iterate_succ_p, hr, beta_iterate, hr, inner_zero_left, zero_div, neg_zero, zero_smul,
      add_zero]

/-- The iteration is stationary once the residual vanishes (Lean's `x / 0 = 0`). -/
theorem step_eq_self_of_residual_eq_zero (s : State E) (hr : s.r = 0) (hp : s.p = 0) :
    step B s = s := by
  obtain ⟨x, r, p⟩ := s
  simp_all [step]

/-- Once the residual vanishes at step `k`, every later state equals the state at `k`. -/
theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hk : (iterate B b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate B b x₀ l = iterate B b x₀ k := by
  induction l with
  | zero => obtain rfl : k = 0 := Nat.le_zero.1 hl; rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · rw [iterate_succ, ih (Nat.lt_succ_iff.1 h), step_eq_self_of_residual_eq_zero B _ hk
        (direction_eq_zero_of_residual_eq_zero B b x₀ hk)]
    · obtain rfl : k = l + 1 := le_antisymm hl h
      rfl

/-- `r_{k+1} = 0` as soon as `r_k = 0`. -/
theorem residual_succ_eq_zero_of_eq_zero {k : ℕ} (hr : (iterate B b x₀ k).r = 0) :
    (iterate B b x₀ (k + 1)).r = 0 := by
  rw [iterate_eq_of_residual_eq_zero B b x₀ hr (k + 1) (Nat.le_succ k), hr]

/-! ### Elementary consequences of the recurrence, before any orthogonality -/

/-- `β_k ⟪r_k, r_k⟫ = -⟪r_{k+1}, r_{k+1}⟫`, valid also at a breakdown. -/
private theorem beta_mul_inner_self (k : ℕ) :
    beta B (iterate B b x₀ k) * inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r =
      -inner ℝ (iterate B b x₀ (k + 1)).r (iterate B b x₀ (k + 1)).r := by
  by_cases h : inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r = 0
  · rw [h, mul_zero, residual_succ_eq_zero_of_eq_zero B b x₀ (inner_self_eq_zero.1 h),
      inner_zero_left, neg_zero]
  · rw [beta_iterate, neg_mul, div_mul_cancel₀ _ h]

/-- Each residual is a combination of two consecutive directions, so orthogonality to the directions
gives orthogonality to the residuals. -/
private theorem inner_residual_eq_zero_of_inner_direction {j : ℕ} {v : E}
    (h : ∀ l ≤ j, inner ℝ v (iterate B b x₀ l).p = 0) :
    inner ℝ v (iterate B b x₀ j).r = 0 := by
  cases j with
  | zero => rw [← direction_zero]; exact h 0 le_rfl
  | succ i =>
    have hi : (iterate B b x₀ (i + 1)).r =
        (iterate B b x₀ (i + 1)).p - beta B (iterate B b x₀ i) • (iterate B b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [hi, inner_sub_right, real_inner_smul_right, h _ le_rfl, h i (Nat.le_succ i), mul_zero,
      sub_zero]

/-- Both `r_k` and `p_k` lie in `𝒦_{k+1}`. -/
private theorem residual_direction_mem_subspace (k : ℕ) :
    (iterate B b x₀ k).r ∈ subspace B (b - B x₀) (k + 1) ∧
      (iterate B b x₀ k).p ∈ subspace B (b - B x₀) (k + 1) := by
  induction k with
  | zero =>
    have h : b - B x₀ ∈ subspace B (b - B x₀) 1 := self_mem_subspace B (b - B x₀) one_pos
    exact ⟨h, h⟩
  | succ k ih =>
    have hmono := subspace_mono B (b - B x₀) (Nat.le_succ (k + 1))
    have hr : (iterate B b x₀ (k + 1)).r ∈ subspace B (b - B x₀) (k + 1 + 1) := by
      rw [iterate_succ_r]
      exact Submodule.sub_mem _ (hmono ih.1) (Submodule.smul_mem _ _
        (map_subspace_le B (b - B x₀) (k + 1) ⟨_, ih.2, rfl⟩))
    exact ⟨hr, by
      rw [iterate_succ_p]
      exact Submodule.add_mem _ hr (Submodule.smul_mem _ _ (hmono ih.2))⟩

/-- `r_k ∈ 𝒦_{k+1}(B, r₀)`. -/
theorem residual_mem_subspace (k : ℕ) : (iterate B b x₀ k).r ∈ subspace B (b - B x₀) (k + 1) :=
  (residual_direction_mem_subspace B b x₀ k).1

/-- `p_k ∈ 𝒦_{k+1}(B, r₀)`. -/
theorem direction_mem_subspace (k : ℕ) : (iterate B b x₀ k).p ∈ subspace B (b - B x₀) (k + 1) :=
  (residual_direction_mem_subspace B b x₀ k).2

/-- The span of the first `k` search directions. -/
private noncomputable def dirSpan (B : E →ₗ[ℝ] E) (b x₀ : E) (k : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Fin k => (iterate B b x₀ i).p)

/-- The span of the first `k` residuals. -/
private noncomputable def resSpan (B : E →ₗ[ℝ] E) (b x₀ : E) (k : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Fin k => (iterate B b x₀ i).r)

private theorem direction_mem_dirSpan {i k : ℕ} (h : i < k) :
    (iterate B b x₀ i).p ∈ dirSpan B b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem residual_mem_resSpan {i k : ℕ} (h : i < k) :
    (iterate B b x₀ i).r ∈ resSpan B b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem dirSpan_mono {k l : ℕ} (h : k ≤ l) : dirSpan B b x₀ k ≤ dirSpan B b x₀ l := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact direction_mem_dirSpan B b x₀ (lt_of_lt_of_le i.2 h)

private theorem resSpan_mono {k l : ℕ} (h : k ≤ l) : resSpan B b x₀ k ≤ resSpan B b x₀ l := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact residual_mem_resSpan B b x₀ (lt_of_lt_of_le i.2 h)

private theorem residual_mem_dirSpan (i : ℕ) : (iterate B b x₀ i).r ∈ dirSpan B b x₀ (i + 1) := by
  cases i with
  | zero => rw [← direction_zero]; exact direction_mem_dirSpan B b x₀ Nat.zero_lt_one
  | succ i =>
    have h : (iterate B b x₀ (i + 1)).r =
        (iterate B b x₀ (i + 1)).p - beta B (iterate B b x₀ i) • (iterate B b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [h]
    exact Submodule.sub_mem _ (direction_mem_dirSpan B b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (direction_mem_dirSpan B b x₀ (by omega)))

private theorem direction_mem_resSpan (i : ℕ) : (iterate B b x₀ i).p ∈ resSpan B b x₀ (i + 1) := by
  induction i with
  | zero => rw [direction_zero]; exact residual_mem_resSpan B b x₀ Nat.zero_lt_one
  | succ i ih =>
    rw [iterate_succ_p]
    exact Submodule.add_mem _ (residual_mem_resSpan B b x₀ (Nat.lt_succ_self _))
      (Submodule.smul_mem _ _ (resSpan_mono B b x₀ (by omega) ih))

private theorem dirSpan_le_subspace (k : ℕ) : dirSpan B b x₀ k ≤ subspace B (b - B x₀) k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono B (b - B x₀) i.2 (direction_mem_subspace B b x₀ i)

private theorem resSpan_le_subspace (k : ℕ) : resSpan B b x₀ k ≤ subspace B (b - B x₀) k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono B (b - B x₀) i.2 (residual_mem_subspace B b x₀ i)

private theorem dirSpan_le_resSpan (k : ℕ) : dirSpan B b x₀ k ≤ resSpan B b x₀ k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact resSpan_mono B b x₀ i.2 (direction_mem_resSpan B b x₀ i)

private theorem resSpan_le_dirSpan (k : ℕ) : resSpan B b x₀ k ≤ dirSpan B b x₀ k := by
  rw [resSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact dirSpan_mono B b x₀ i.2 (residual_mem_dirSpan B b x₀ i)

/-! ### The joint induction -/

variable {B}

/-- `α_k ⟪p_k, B p_k⟫ = ⟪r_k, r_k⟫`, valid also at a breakdown: the denominator is `‖p_k‖²`, and
when it vanishes `p_k = 0`, so the diagonal relation makes the numerator vanish too. -/
private theorem alpha_mul_inner_apply_direction' (hB : B.IsShiftedSkewAdjoint) (k : ℕ)
    (hdiag : inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).p =
      inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r) :
    alpha B (iterate B b x₀ k) * inner ℝ (iterate B b x₀ k).p (B (iterate B b x₀ k).p) =
      inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r := by
  by_cases h : inner ℝ (iterate B b x₀ k).p (B (iterate B b x₀ k).p) = 0
  · rw [h, mul_zero]
    have hp : (iterate B b x₀ k).p = 0 := by
      refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
      rw [← hB.inner_self]
      exact h
    rw [← hdiag, hp, inner_zero_right]
  · rw [alpha, div_mul_cancel₀ _ h]

/-- `B p_k = 0` when the step length degenerates. -/
private theorem apply_direction_eq_zero_of_alpha_eq_zero (hB : B.IsShiftedSkewAdjoint) {k : ℕ}
    (h : alpha B (iterate B b x₀ k) = 0) : B (iterate B b x₀ k).p = 0 := by
  rcases div_eq_zero_iff.1 h with h' | h'
  · rw [direction_eq_zero_of_residual_eq_zero B b x₀ (inner_self_eq_zero.1 h'), map_zero]
  · have hp : (iterate B b x₀ k).p = 0 := by
      refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
      rw [← hB.inner_self]
      exact h'
    rw [hp, map_zero]

/-- `⟪v, B p_j⟫ = 0` whenever `v` is orthogonal to `r_j` and to `r_{j+1}`. -/
private theorem inner_apply_direction_eq_zero_of (hB : B.IsShiftedSkewAdjoint) {j : ℕ} {v : E}
    (h1 : inner ℝ v (iterate B b x₀ j).r = 0)
    (h2 : inner ℝ v (iterate B b x₀ (j + 1)).r = 0) :
    inner ℝ v (B (iterate B b x₀ j).p) = 0 := by
  by_cases hα : alpha B (iterate B b x₀ j) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero (b := b) (x₀ := x₀) hB hα, inner_zero_right]
  · have h : alpha B (iterate B b x₀ j) * inner ℝ v (B (iterate B b x₀ j).p) = 0 := by
      rw [← real_inner_smul_right, alpha_smul_apply_direction, inner_sub_right, h1, h2, sub_zero]
    exact (mul_eq_zero.1 h).resolve_left hα

/-- The joint invariant at step `k`: the residual is orthogonal to all earlier search directions,
the current direction is `B`-conjugate to all earlier ones *on the right*, and
`⟪r_k, p_k⟫ = ⟪r_k, r_k⟫`. -/
private structure Invariant (B : E →ₗ[ℝ] E) (b x₀ : E) (k : ℕ) : Prop where
  /-- `r_k ⟂ p_j` for `j < k`. -/
  rp : ∀ j < k, inner ℝ (iterate B b x₀ k).r (iterate B b x₀ j).p = 0
  /-- `⟪p_j, B p_k⟫ = 0` for `j < k`. -/
  pp : ∀ j < k, inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ k).p) = 0
  /-- `⟪r_k, p_k⟫ = ⟪r_k, r_k⟫`. -/
  diag : inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).p =
    inner ℝ (iterate B b x₀ k).r (iterate B b x₀ k).r

private theorem invariant (hB : B.IsShiftedSkewAdjoint) (k : ℕ) : Invariant B b x₀ k := by
  induction k with
  | zero =>
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => absurd hj (Nat.not_lt_zero j),
      by rw [direction_zero]⟩
  | succ k ih =>
    -- Step 1: `r_{k+1} ⟂ p_j` for `j ≤ k`.
    have rp : ∀ j < k + 1, inner ℝ (iterate B b x₀ (k + 1)).r (iterate B b x₀ j).p = 0 := by
      intro j hj
      rw [iterate_succ_r, inner_sub_left, real_inner_smul_left]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.rp j h, real_inner_comm, ih.pp j h, mul_zero, sub_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        rw [ih.diag, real_inner_comm (iterate B b x₀ j).p (B (iterate B b x₀ j).p),
          alpha_mul_inner_apply_direction' (b := b) (x₀ := x₀) hB j ih.diag, sub_self]
    -- Step 2: `r_{k+1} ⟂ r_j` for `j ≤ k`.
    have rr : ∀ j < k + 1, inner ℝ (iterate B b x₀ (k + 1)).r (iterate B b x₀ j).r = 0 :=
      fun j hj => inner_residual_eq_zero_of_inner_direction B b x₀ fun l hl => rp l (by omega)
    refine ⟨rp, fun j hj => ?_, ?_⟩
    · -- Step 3: `⟪p_j, B p_{k+1}⟫ = 0` for `j ≤ k`.
      have hBr : inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ (k + 1)).r) =
          -inner ℝ (B (iterate B b x₀ j).p) (iterate B b x₀ (k + 1)).r := by
        have h1 := hB (iterate B b x₀ j).p (iterate B b x₀ (k + 1)).r
        have h2 : inner ℝ (iterate B b x₀ j).p (iterate B b x₀ (k + 1)).r = 0 := by
          rw [real_inner_comm]; exact rp j hj
        linarith
      rw [iterate_succ_p, map_add, map_smul, inner_add_right, real_inner_smul_right, hBr]
      rcases Nat.lt_or_ge j k with h | h
      · have hz : inner ℝ (B (iterate B b x₀ j).p) (iterate B b x₀ (k + 1)).r = 0 := by
          rw [real_inner_comm]
          exact inner_apply_direction_eq_zero_of (b := b) (x₀ := x₀) hB
            (rr j (by omega)) (rr (j + 1) (by omega))
        rw [hz, ih.pp j h, neg_zero, mul_zero, add_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        by_cases hα : alpha B (iterate B b x₀ j) = 0
        · rw [apply_direction_eq_zero_of_alpha_eq_zero (b := b) (x₀ := x₀) hB hα,
            inner_zero_left, inner_zero_right, neg_zero, mul_zero, add_zero]
        · have hkey : alpha B (iterate B b x₀ j) *
              (-inner ℝ (B (iterate B b x₀ j).p) (iterate B b x₀ (j + 1)).r +
                beta B (iterate B b x₀ j) *
                  inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ j).p)) = 0 := by
            have e1 : alpha B (iterate B b x₀ j) *
                inner ℝ (B (iterate B b x₀ j).p) (iterate B b x₀ (j + 1)).r =
                  -inner ℝ (iterate B b x₀ (j + 1)).r (iterate B b x₀ (j + 1)).r := by
              have h0 : inner ℝ (iterate B b x₀ j).r (iterate B b x₀ (j + 1)).r = 0 := by
                rw [real_inner_comm]
                exact rr j (by omega)
              rw [← real_inner_smul_left, alpha_smul_apply_direction, inner_sub_left, h0,
                zero_sub]
            have e2 : alpha B (iterate B b x₀ j) * (beta B (iterate B b x₀ j) *
                inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ j).p)) =
                  -inner ℝ (iterate B b x₀ (j + 1)).r (iterate B b x₀ (j + 1)).r := by
              rw [show alpha B (iterate B b x₀ j) * (beta B (iterate B b x₀ j) *
                    inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ j).p)) =
                  beta B (iterate B b x₀ j) * (alpha B (iterate B b x₀ j) *
                    inner ℝ (iterate B b x₀ j).p (B (iterate B b x₀ j).p)) by ring,
                alpha_mul_inner_apply_direction' (b := b) (x₀ := x₀) hB j ih.diag,
                beta_mul_inner_self B b x₀ j]
            rw [mul_add, mul_neg, e1, e2]
            ring
          exact (mul_eq_zero.1 hkey).resolve_left hα
    · -- Step 4: `⟪r_{k+1}, p_{k+1}⟫ = ⟪r_{k+1}, r_{k+1}⟫`.
      rw [iterate_succ_p, inner_add_right, real_inner_smul_right, rp k (Nat.lt_succ_self k),
        mul_zero, add_zero]

/-! ### The named orthogonality relations -/

variable (hB : B.IsShiftedSkewAdjoint)
include hB

/-- The residuals are mutually orthogonal, as in CG. -/
theorem inner_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner ℝ (iterate B b x₀ i).r (iterate B b x₀ j).r = 0 := by
  have key : ∀ m n : ℕ, n < m → inner ℝ (iterate B b x₀ m).r (iterate B b x₀ n).r = 0 :=
    fun m n hmn => inner_residual_eq_zero_of_inner_direction B b x₀
      fun l hl => (invariant (b := b) (x₀ := x₀) hB m).rp l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [real_inner_comm]; exact key j i h'
  · exact key i j h'

/-- **The one-sided conjugacy of the directions**: `⟪p_i, B p_j⟫ = 0` for `i < j`.  Unlike the CG
relation this is not symmetric in `i` and `j`, because `B` is not self-adjoint; the reverse inner
product `⟪p_j, B p_i⟫` is `2 ⟪p_j, p_i⟫ - ⟪p_i, B p_j⟫` and generally nonzero. -/
theorem inner_direction_apply_direction_eq_zero {i j : ℕ} (h : i < j) :
    inner ℝ (iterate B b x₀ i).p (B (iterate B b x₀ j).p) = 0 :=
  (invariant (b := b) (x₀ := x₀) hB j).pp i h

/-- `⟪r_i, p_j⟫ = 0` for `j < i`. -/
theorem inner_residual_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner ℝ (iterate B b x₀ i).r (iterate B b x₀ j).p = 0 :=
  (invariant (b := b) (x₀ := x₀) hB i).rp j h

/-! ### Spans and the Galerkin property -/

private theorem apply_direction_mem_dirSpan (i : ℕ) :
    B (iterate B b x₀ i).p ∈ dirSpan B b x₀ (i + 2) := by
  by_cases hα : alpha B (iterate B b x₀ i) = 0
  · rw [apply_direction_eq_zero_of_alpha_eq_zero (b := b) (x₀ := x₀) hB hα]
    exact Submodule.zero_mem _
  · have h : B (iterate B b x₀ i).p = (alpha B (iterate B b x₀ i))⁻¹ •
        ((iterate B b x₀ i).r - (iterate B b x₀ (i + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (dirSpan_mono B b x₀ (by omega) (residual_mem_dirSpan B b x₀ i))
      (dirSpan_mono B b x₀ (by omega) (residual_mem_dirSpan B b x₀ (i + 1))))

private theorem pow_apply_mem_dirSpan (k : ℕ)
    (ih : subspace B (b - B x₀) k ≤ dirSpan B b x₀ k) :
    (B ^ k) (b - B x₀) ∈ dirSpan B b x₀ (k + 1) := by
  cases k with
  | zero =>
    have h : (iterate B b x₀ 0).p ∈ dirSpan B b x₀ 1 :=
      direction_mem_dirSpan B b x₀ Nat.zero_lt_one
    simpa [init] using h
  | succ j =>
    have hmem : (B ^ j) (b - B x₀) ∈ dirSpan B b x₀ (j + 1) :=
      ih (pow_apply_mem_subspace B _ (Nat.lt_succ_self j))
    have hpow : (B ^ (j + 1)) (b - B x₀) = B ((B ^ j) (b - B x₀)) := by rw [pow_succ']; rfl
    have hcomap : dirSpan B b x₀ (j + 1) ≤ Submodule.comap B (dirSpan B b x₀ (j + 1 + 1)) := by
      rw [dirSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact dirSpan_mono B b x₀ (by omega) (apply_direction_mem_dirSpan b x₀ hB l)
    rw [hpow]
    exact hcomap hmem

private theorem subspace_le_dirSpan (k : ℕ) : subspace B (b - B x₀) k ≤ dirSpan B b x₀ k := by
  induction k with
  | zero => rw [subspace_zero]; exact bot_le
  | succ k ih =>
    rw [subspace, Submodule.span_le, Set.range_subset_iff]
    intro i
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · exact dirSpan_mono B b x₀ (Nat.le_succ k) (ih (pow_apply_mem_subspace B _ h))
    · have h' : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) h
      rw [h']
      exact pow_apply_mem_dirSpan b x₀ hB k ih

/-- `span {p_0, …, p_{k-1}} = 𝒦_k(B, r₀)`. -/
theorem span_direction_eq (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin k => (iterate B b x₀ i).p) =
      subspace B (b - B x₀) k :=
  le_antisymm (dirSpan_le_subspace B b x₀ k) (subspace_le_dirSpan b x₀ hB k)

/-- `span {r_0, …, r_{k-1}} = 𝒦_k(B, r₀)`. -/
theorem span_residual_eq (k : ℕ) :
    Submodule.span ℝ (Set.range fun i : Fin k => (iterate B b x₀ i).r) =
      subspace B (b - B x₀) k :=
  le_antisymm (resSpan_le_subspace B b x₀ k)
    ((subspace_le_dirSpan b x₀ hB k).trans (dirSpan_le_resSpan B b x₀ k))

omit hB in
/-- The iteration stays in the affine Krylov space: `x_k ∈ x₀ + 𝒦_k(B, r₀)`. -/
theorem iterate_sub_mem (k : ℕ) : (iterate B b x₀ k).x - x₀ ∈ subspace B (b - B x₀) k := by
  induction k with
  | zero => simp [init]
  | succ k ih =>
    have h : (iterate B b x₀ (k + 1)).x - x₀ = ((iterate B b x₀ k).x - x₀) +
        alpha B (iterate B b x₀ k) • (iterate B b x₀ k).p := by
      rw [iterate_succ_x]; abel
    rw [h]
    exact Submodule.add_mem _ (subspace_mono B (b - B x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ (direction_mem_subspace B b x₀ k))

/-- **The Concus–Golub–Widlund iterate is a Galerkin iterate**: it lies in `x₀ + 𝒦_k(B, r₀)` and its
residual is orthogonal to that space.  So the recurrence is a projection method (the FOM iterate of
the tridiagonal relation), even though `B` is not self-adjoint and no minimization property comes
with it. -/
theorem isGalerkinIterate (k : ℕ) : IsGalerkinIterate B b x₀ k (iterate B b x₀ k).x := by
  refine ⟨iterate_sub_mem b x₀ k, ?_⟩
  rw [← residual_eq, ← span_direction_eq b x₀ hB k]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [real_inner_comm]
  exact inner_residual_direction_eq_zero b x₀ hB i.2

end CGW
