import Numlib.Krylov.Iterate

/-!
# The conjugate residual recurrence (Stiefel)

`CR.step` is one step of the CR recurrence (Saad, *Iterative Methods*[^saad-iterative]
Alg 6.20, Fong–Saunders[^fong-saunders] Table 2.1, Choi[^choi] Table 2.12), with `q = A p`
carried in the state so that each step applies `A` once.

## Main definitions

* `CR.State`: the iteration state, carrying `x_k`, `r_k`, `p_k` and `q_k = A p_k`;
* `CR.alpha`, `CR.step`, `CR.init`, `CR.iterate`: the recurrence.

## Main statements

* `CR.isMinResIterate`: CR realises the minimal-residual specification of
  `Numlib/Krylov/Iterate`, and `CR.isMinResIterate_of_no_breakdown` is the same for a symmetric,
  possibly indefinite or singular `A` as long as no breakdown occurs;
* `CR.inner_apply_direction_eq_zero`, `CR.inner_residual_apply_direction_eq_zero`,
  `CR.inner_residual_apply_residual_eq_zero`: the orthogonality relations
  (Fong–Saunders Thm 2.1 / Luenberger);
* `CR.re_alpha_nonneg`, `CR.re_inner_direction_apply_direction_nonneg`,
  `CR.re_inner_direction_nonneg`, `CR.re_inner_iterate_direction_nonneg`,
  `CR.re_inner_residual_direction_nonneg`: the sign properties on SPD systems
  (Fong–Saunders Thm 2.2);
* `CR.norm_iterate_monotone`, `CR.norm_error_antitone`, `CR.energyNorm_error_antitone`: the
  resulting monotonicity (Fong–Saunders Thm 2.3–2.5), with Steihaug's strict form for a
  symmetric but possibly indefinite `A` in `CR.norm_iterate_lt_of_pos`;
* `Krylov.isMinResIterate_of_orthogonal_directions`: the general GCR lemma (Saad Lemma 6.21),
  that any `AᴴA`-orthogonal direction sequence spanning the Krylov spaces yields
  minimal-residual iterates.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^fong-saunders]: David Chin-Lung Fong and Michael Saunders, *CG versus MINRES: an empirical
  comparison*, SQU Journal for Science 17 (2012), 44–62.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace CR

/-- State of the CR iteration: iterate, residual, direction, and `q = A p`. -/
structure State (E : Type*) where
  /-- The iterate `x_k`. -/
  x : E
  /-- The residual `r_k = b - A x_k` (see `CR.residual_eq`). -/
  r : E
  /-- The search direction `p_k`. -/
  p : E
  /-- The image `q_k = A p_k` of the search direction (see `CR.q_eq`), carried so that a step
  applies `A` only to the new residual. -/
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

/-- The starting state of the conjugate residual iteration at `x₀`: the residual and the first
search direction are both `r₀ = b - A x₀`, and `q₀ = A p₀` is stored alongside them so that each
later step applies `A` only once, to the new residual. -/
def init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := b - A x₀, q := A (b - A x₀) }

/-- The `k`-th state of the conjugate residual iteration for `A x = b` started at `x₀`: `k`
applications of `CR.step` to `CR.init`. The approximate solution is `(iterate A b x₀ k).x`.

On a symmetric coercive `A` this state realises the minimal-residual specification over
`x₀ + 𝒦_k(A, r₀)` (`CR.isMinResIterate`). The specification, not this recurrence, is the canonical
object: everything proved of it holds of any method that meets it. On an indefinite `A` the
recurrence can break down while the minimal-residual iterate still exists, and
`CR.isMinResIterate_of_no_breakdown` is what survives there. The definition is total either way,
since Lean's `x / 0 = 0` gives the degenerate steps a value; once the residual vanishes the state
stops moving. -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A)^[k] (init A b x₀)

variable (A : E →ₗ[𝕜] E) (b x₀ : E)

/-- The recurrence: state `k + 1` is one `CR.step` applied to state `k`. This is the orientation
the algorithm is read in; `Function.iterate` reduces by peeling a step off the front instead, so
unfolding `(step A)^[k+1]` directly gives an extra step applied to the *initial* state. -/
theorem iterate_succ (k : ℕ) : iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The CR direction update coefficient `β = ⟪r', A r'⟫ / ⟪r, A r⟫`. -/
private noncomputable def beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A s).r (A (step A s).r) / inner 𝕜 s.r (A s.r)

private theorem step_x (s : State E) : (step A s).x = s.x + alpha A s • s.p := rfl

private theorem step_r (s : State E) : (step A s).r = s.r - alpha A s • s.q := rfl

private theorem step_p (s : State E) : (step A s).p = (step A s).r + beta A s • s.p := rfl

private theorem step_q (s : State E) : (step A s).q = A (step A s).r + beta A s • s.q := rfl

/-- The invariant `q = A p`. -/
theorem q_eq (k : ℕ) : (iterate A b x₀ k).q = A (iterate A b x₀ k).p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, step_q, step_p, map_add, map_smul, ih]

private theorem iterate_succ_x (k : ℕ) : (iterate A b x₀ (k + 1)).x =
    (iterate A b x₀ k).x + alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ, step_x]

private theorem iterate_succ_r (k : ℕ) : (iterate A b x₀ (k + 1)).r =
    (iterate A b x₀ k).r - alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p := by
  rw [iterate_succ, step_r, q_eq]

private theorem iterate_succ_p (k : ℕ) : (iterate A b x₀ (k + 1)).p =
    (iterate A b x₀ (k + 1)).r + beta A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
  rw [iterate_succ]; exact step_p A _

private theorem beta_iterate (k : ℕ) : beta A (iterate A b x₀ k) =
    inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r) /
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) := by
  rw [beta, iterate_succ]

/-- `p₀ = r₀`. -/
private theorem direction_zero : (iterate A b x₀ 0).p = (iterate A b x₀ 0).r := rfl

/-- The state's residual field is the true residual. -/
theorem residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_r, iterate_succ_x, ih, map_add, map_smul, sub_sub]

/-- `α_k A p_k = r_k - r_{k+1}`. -/
private theorem alpha_smul_apply_direction (k : ℕ) :
    alpha A (iterate A b x₀ k) • A (iterate A b x₀ k).p =
      (iterate A b x₀ k).r - (iterate A b x₀ (k + 1)).r := by
  rw [iterate_succ_r]; abel

/-- If the residual vanishes so does the search direction. -/
private theorem direction_eq_zero_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ k).p = 0 := by
  cases k with
  | zero => rw [direction_zero]; exact hr
  | succ k =>
    rw [iterate_succ_p, hr, beta_iterate, hr, inner_zero_left, zero_div, zero_smul, add_zero]

private theorem step_eq_self (s : State E) (hr : s.r = 0) (hp : s.p = 0) (hq : s.q = 0) :
    step A s = s := by
  obtain ⟨x, r, p, q⟩ := s
  simp_all [step]

private theorem iterate_eq_of_residual_eq_zero {k : ℕ} (hk : (iterate A b x₀ k).r = 0) (l : ℕ)
    (hl : k ≤ l) : iterate A b x₀ l = iterate A b x₀ k := by
  have hp : (iterate A b x₀ k).p = 0 := direction_eq_zero_of_residual_eq_zero A b x₀ hk
  have hq : (iterate A b x₀ k).q = 0 := by rw [q_eq, hp, map_zero]
  induction l with
  | zero => obtain rfl : k = 0 := Nat.le_zero.1 hl; rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · rw [iterate_succ, ih (Nat.lt_succ_iff.1 h), step_eq_self A _ hk hp hq]
    · obtain rfl : k = l + 1 := le_antisymm hl h
      rfl

private theorem residual_succ_eq_zero_of_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) :
    (iterate A b x₀ (k + 1)).r = 0 := by
  rw [iterate_eq_of_residual_eq_zero A b x₀ hr (k + 1) (Nat.le_succ k), hr]

/-! ### Elementary consequences of the recurrence -/

private theorem inner_self_eq_ofReal_norm_sq (x : E) : inner 𝕜 x x = ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- Each residual is a combination of two consecutive directions. -/
private theorem inner_eq_zero_of_inner_direction {j : ℕ} {v : E}
    (h : ∀ l ≤ j, inner 𝕜 v (A (iterate A b x₀ l).p) = 0) :
    inner 𝕜 v (A (iterate A b x₀ j).r) = 0 := by
  cases j with
  | zero => rw [← direction_zero]; exact h 0 le_rfl
  | succ i =>
    have hi : (iterate A b x₀ (i + 1)).r =
        (iterate A b x₀ (i + 1)).p - beta A (iterate A b x₀ i) • (iterate A b x₀ i).p := by
      rw [iterate_succ_p]; abel
    rw [hi, map_sub, map_smul, inner_sub_right, inner_smul_right, h _ le_rfl,
      h i (Nat.le_succ i), mul_zero, sub_zero]

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

/-- The span of the first `k` search directions. -/
private noncomputable def dirSpan (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p)

private theorem direction_mem_dirSpan {i k : ℕ} (h : i < k) :
    (iterate A b x₀ i).p ∈ dirSpan A b x₀ k :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

private theorem dirSpan_mono {k l : ℕ} (h : k ≤ l) : dirSpan A b x₀ k ≤ dirSpan A b x₀ l := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact direction_mem_dirSpan A b x₀ (lt_of_lt_of_le i.2 h)

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

private theorem dirSpan_le_subspace (k : ℕ) : dirSpan A b x₀ k ≤ subspace A (b - A x₀) k := by
  rw [dirSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact subspace_mono A (b - A x₀) i.2 (residual_direction_mem_subspace A b x₀ i).2

private theorem iterate_sub_mem (k : ℕ) :
    (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k := by
  induction k with
  | zero => simp [iterate, init]
  | succ k ih =>
    have h : (iterate A b x₀ (k + 1)).x - x₀ = ((iterate A b x₀ k).x - x₀) +
        alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
      rw [iterate_succ_x]; abel
    rw [h]
    exact Submodule.add_mem _ (subspace_mono A (b - A x₀) (Nat.le_succ k) ih)
      (Submodule.smul_mem _ _ (residual_direction_mem_subspace A b x₀ k).2)

variable {A} (hA : A.IsSymmetricCoercive)
include hA

/-! ### The joint induction (Fong–Saunders, *CG versus MINRES*, Thm 2.1) -/

private theorem re_inner_self_nonneg (x : E) : 0 ≤ RCLike.re (inner 𝕜 x (A x)) := by
  obtain ⟨c, hc, h⟩ := hA.isCoercive
  rw [← hA.isSymmetric]
  exact le_trans (by positivity) (h x)

omit hA in
private theorem inner_self_ofReal (hAs : A.IsSymmetric) (x : E) :
    ((RCLike.re (inner 𝕜 x (A x)) : ℝ) : 𝕜) = inner 𝕜 x (A x) :=
  RCLike.conj_eq_iff_re.1 (by rw [inner_conj_symm, hAs])

private theorem eq_zero_of_inner_self_eq_zero {x : E} (h : inner 𝕜 x (A x) = 0) : x = 0 := by
  by_contra hx
  have hpos := hA.isCoercive.inner_self_pos hx
  rw [hA.isSymmetric, h, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-- The first fact coercivity supplies to the sign theory below. -/
private theorem re_inner_residual_self_nonneg :
    ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)) :=
  fun _ => re_inner_self_nonneg hA _

/-- The second fact coercivity supplies to the sign theory below. -/
private theorem residual_eq_zero_of_inner_self :
    ∀ j, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 →
      (iterate A b x₀ j).r = 0 :=
  fun _ h => eq_zero_of_inner_self_eq_zero hA h

omit hA in
private theorem conj_alpha (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (alpha A s) = alpha A s := by
  rw [alpha, map_div₀, inner_conj_symm, hAs, inner_self_conj]

omit hA in
private theorem conj_beta (hAs : A.IsSymmetric) (s : State E) :
    (starRingEnd 𝕜) (beta A s) = beta A s := by
  rw [beta, map_div₀, inner_conj_symm, hAs, inner_conj_symm, hAs]

omit hA in
/-- `α_k ⟪A p_k, A p_k⟫ = ⟪r_k, A r_k⟫`, valid also at a breakdown. -/
private theorem alpha_mul_inner_apply_direction' (k : ℕ)
    (hdiag : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).p) =
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) :
    alpha A (iterate A b x₀ k) *
        inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ k).p) =
      inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) := by
  by_cases h : inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ k).p) = 0
  · rw [h, mul_zero, ← hdiag, inner_self_eq_zero.1 h, inner_zero_right]
  · rw [alpha, q_eq, div_mul_cancel₀ _ h]

omit hA in
/-- `β_k ⟪r_k, A r_k⟫ = ⟪r_{k+1}, A r_{k+1}⟫`, valid also at a breakdown. -/
private theorem beta_mul_inner_self
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (k : ℕ) :
    beta A (iterate A b x₀ k) * inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) =
      inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r) := by
  by_cases h : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r) = 0
  · rw [h, mul_zero, residual_succ_eq_zero_of_eq_zero A b x₀ (hz k h), inner_zero_left]
  · rw [beta_iterate, div_mul_cancel₀ _ h]

omit hA in
/-- `A p_k = 0` when the step length degenerates. -/
private theorem apply_direction_eq_zero_of_alpha_eq_zero
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0) {k : ℕ}
    (h : alpha A (iterate A b x₀ k) = 0) : A (iterate A b x₀ k).p = 0 := by
  rcases div_eq_zero_iff.1 h with h' | h'
  · rw [direction_eq_zero_of_residual_eq_zero A b x₀ (hz k h'), map_zero]
  · rw [← q_eq]
    exact inner_self_eq_zero.1 h'

omit hA in
/-- `⟪v, A (A p_j)⟫ = 0` whenever `v` is `A`-orthogonal to `r_j` and to `r_{j+1}`. -/
private theorem inner_apply_apply_direction_eq_zero_of {j : ℕ} {v : E}
    (hdeg : alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0)
    (h1 : inner 𝕜 v (A (iterate A b x₀ j).r) = 0)
    (h2 : inner 𝕜 v (A (iterate A b x₀ (j + 1)).r) = 0) :
    inner 𝕜 v (A (A (iterate A b x₀ j).p)) = 0 := by
  by_cases hα : alpha A (iterate A b x₀ j) = 0
  · rw [hdeg hα, map_zero, inner_zero_right]
  · have h : alpha A (iterate A b x₀ j) * inner 𝕜 v (A (A (iterate A b x₀ j).p)) = 0 := by
      rw [← inner_smul_right, ← map_smul, alpha_smul_apply_direction, map_sub, inner_sub_right,
        h1, h2, sub_zero]
    exact (mul_eq_zero.1 h).resolve_left hα

/-- The joint CR invariant at step `k` (Fong–Saunders, *CG versus MINRES*, Thm 2.1). -/
private structure Invariant (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : Prop where
  /-- `⟪r_k, A p_j⟫ = 0` for `j < k`. -/
  rq : ∀ j < k, inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ j).p) = 0
  /-- `⟪A p_k, A p_j⟫ = 0` for `j < k`. -/
  qq : ∀ j < k, inner 𝕜 (A (iterate A b x₀ k).p) (A (iterate A b x₀ j).p) = 0
  /-- `⟪r_k, A p_k⟫ = ⟪r_k, A r_k⟫`. -/
  diag : inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).p) =
    inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)

omit hA in
/-- The invariant, under the two facts that coercivity is only used for: at a degenerate step
the direction dies (`hdeg`) and the `β` recurrence transports the `A`-norms (`hbeta`). -/
private theorem invariant_of (hAs : A.IsSymmetric) (k : ℕ) :
    (∀ j < k, alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0) →
      (∀ j < k, beta A (iterate A b x₀ j) *
          inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) =
        inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ (j + 1)).r)) →
      Invariant A b x₀ k := by
  induction k with
  | zero =>
    exact fun _ _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j), by rw [direction_zero]⟩
  | succ k ihk =>
    intro hdeg hbeta
    have ih := ihk (fun j hj => hdeg j (by omega)) (fun j hj => hbeta j (by omega))
    have rq : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ j).p) = 0 := by
      intro j hj
      rw [iterate_succ_r, inner_sub_left, inner_smul_left, conj_alpha hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.rq j h, ih.qq j h, mul_zero, sub_zero]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        rw [ih.diag, alpha_mul_inner_apply_direction' b x₀ j ih.diag, sub_self]
    have rr : ∀ j < k + 1, inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ j).r) = 0 :=
      fun j hj => inner_eq_zero_of_inner_direction A b x₀ fun l hl => rq l (by omega)
    refine ⟨rq, fun j hj => ?_, ?_⟩
    · rw [iterate_succ_p, map_add, map_smul, inner_add_left, inner_smul_left, conj_beta hAs]
      rcases Nat.lt_or_ge j k with h | h
      · rw [ih.qq j h, mul_zero, add_zero, hAs,
          inner_apply_apply_direction_eq_zero_of b x₀ (hdeg j (by omega)) (rr j (by omega))
            (rr (j + 1) (by omega))]
      · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) h
        by_cases hα : alpha A (iterate A b x₀ j) = 0
        · rw [hdeg j (by omega) hα]
          simp
        · have key : alpha A (iterate A b x₀ j) *
              (inner 𝕜 (A (iterate A b x₀ (j + 1)).r) (A (iterate A b x₀ j).p) +
                beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) = 0 := by
            rw [mul_add, ← inner_smul_right, alpha_smul_apply_direction, hAs,
              map_sub, inner_sub_right, rr j (by omega), zero_sub,
              show alpha A (iterate A b x₀ j) * (beta A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) =
                beta A (iterate A b x₀ j) * (alpha A (iterate A b x₀ j) *
                  inner 𝕜 (A (iterate A b x₀ j).p) (A (iterate A b x₀ j).p)) by ring,
              alpha_mul_inner_apply_direction' b x₀ j ih.diag, hbeta j (by omega)]
            ring
          exact (mul_eq_zero.1 key).resolve_left hα
    · rw [iterate_succ_p, map_add, map_smul, inner_add_right, inner_smul_right,
        rq k (Nat.lt_succ_self k), mul_zero, add_zero]

omit hA in
/-- The invariant under symmetry and the nondegeneracy hypothesis alone. -/
private theorem invariant' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (k : ℕ) : Invariant A b x₀ k :=
  invariant_of b x₀ hAs k
    (fun _ _ h => apply_direction_eq_zero_of_alpha_eq_zero b x₀ hz h)
    (fun j _ => beta_mul_inner_self b x₀ hz j)

private theorem invariant (k : ℕ) : Invariant A b x₀ k :=
  invariant' b x₀ hA.isSymmetric (residual_eq_zero_of_inner_self b x₀ hA) k

/-! ### The named orthogonality relations -/

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.1 (a) / Luenberger: `⟪A p_i, A p_j⟫ = 0`
for `i ≠ j`. -/
theorem inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (A (iterate A b x₀ j).p) = 0 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← inner_conj_symm, (invariant b x₀ hA j).qq i h', map_zero]
  · exact (invariant b x₀ hA i).qq j h'

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.1 (b): `⟪r_i, A p_j⟫ = 0` for `j < i`. -/
theorem inner_residual_apply_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) = 0 :=
  (invariant b x₀ hA i).rq j h

omit hA in
/-- Residuals are `A`-orthogonal under symmetry and nondegeneracy alone. -/
private theorem inner_residual_apply_residual_eq_zero' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0 := by
  have key : ∀ m n : ℕ, n < m →
      inner 𝕜 (iterate A b x₀ m).r (A (iterate A b x₀ n).r) = 0 :=
    fun m n hmn => inner_eq_zero_of_inner_direction A b x₀
      fun l hl => (invariant' b x₀ hAs hz m).rq l (by omega)
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [← hAs, ← inner_conj_symm, key j i h', map_zero]
  · exact key i j h'

/-- Residuals are `A`-orthogonal: `⟪r_i, A r_j⟫ = 0` for `i ≠ j`. -/
theorem inner_residual_apply_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0 :=
  inner_residual_apply_residual_eq_zero' b x₀ hA.isSymmetric
    (residual_eq_zero_of_inner_self b x₀ hA) h

omit hA in
/-- `⟪r_i, A p_j⟫ = ⟪r_j, A r_j⟫` under symmetry and nondegeneracy alone. -/
private theorem inner_residual_apply_direction_eq' (hAs : A.IsSymmetric)
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) =
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) := by
  induction j, h using Nat.le_induction with
  | base => exact (invariant' b x₀ hAs hz i).diag
  | succ j hij ih =>
    rw [iterate_succ_p, map_add, map_smul, inner_add_right, inner_smul_right, ih,
      inner_residual_apply_residual_eq_zero' b x₀ hAs hz (show i ≠ j + 1 by omega), zero_add,
      beta_mul_inner_self b x₀ hz j]

/-- `⟪r_i, A p_j⟫ = ⟪r_j, A r_j⟫` for `i ≤ j` (the CR analogue of `⟪r_i, p_j⟫ = ‖r_j‖²`). -/
theorem inner_residual_apply_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) =
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) :=
  inner_residual_apply_direction_eq' b x₀ hA.isSymmetric
    (residual_eq_zero_of_inner_self b x₀ hA) h

/-! ### Spans and the minimal-residual property -/

omit hA in
private theorem apply_direction_mem_dirSpan (i : ℕ)
    (hdeg : alpha A (iterate A b x₀ i) = 0 → A (iterate A b x₀ i).p = 0) :
    A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2) := by
  by_cases hα : alpha A (iterate A b x₀ i) = 0
  · rw [hdeg hα]
    exact Submodule.zero_mem _
  · have h : A (iterate A b x₀ i).p = (alpha A (iterate A b x₀ i))⁻¹ •
        ((iterate A b x₀ i).r - (iterate A b x₀ (i + 1)).r) := by
      rw [← alpha_smul_apply_direction, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ i))
      (dirSpan_mono A b x₀ (by omega) (residual_mem_dirSpan A b x₀ (i + 1))))

omit hA in
private theorem pow_apply_mem_dirSpan (k : ℕ)
    (hmem : ∀ i < k, A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2))
    (ih : subspace A (b - A x₀) k ≤ dirSpan A b x₀ k) :
    (A ^ k) (b - A x₀) ∈ dirSpan A b x₀ (k + 1) := by
  cases k with
  | zero =>
    have h : (iterate A b x₀ 0).p ∈ dirSpan A b x₀ 1 :=
      direction_mem_dirSpan A b x₀ Nat.zero_lt_one
    simpa [iterate, init] using h
  | succ j =>
    have hmemj : (A ^ j) (b - A x₀) ∈ dirSpan A b x₀ (j + 1) :=
      ih (pow_apply_mem_subspace A _ (Nat.lt_succ_self j))
    have hpow : (A ^ (j + 1)) (b - A x₀) = A ((A ^ j) (b - A x₀)) := by rw [pow_succ']; rfl
    have hcomap : dirSpan A b x₀ (j + 1) ≤ Submodule.comap A (dirSpan A b x₀ (j + 1 + 1)) := by
      rw [dirSpan, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact dirSpan_mono A b x₀ (by omega) (hmem l (by omega))
    rw [hpow]
    exact hcomap hmemj

omit hA in
private theorem subspace_le_dirSpan (k : ℕ)
    (hmem : ∀ i < k, A (iterate A b x₀ i).p ∈ dirSpan A b x₀ (i + 2)) :
    subspace A (b - A x₀) k ≤ dirSpan A b x₀ k := by
  induction k with
  | zero => rw [subspace_zero]; exact bot_le
  | succ k ihk =>
    have ih := ihk fun i hi => hmem i (by omega)
    rw [subspace, Submodule.span_le, Set.range_subset_iff]
    intro i
    rcases Nat.lt_or_ge (i : ℕ) k with h | h
    · exact dirSpan_mono A b x₀ (Nat.le_succ k) (ih (pow_apply_mem_subspace A _ h))
    · have h' : (i : ℕ) = k := le_antisymm (Nat.lt_succ_iff.1 i.2) h
      rw [h']
      exact pow_apply_mem_dirSpan b x₀ k (fun i hi => hmem i (by omega)) ih

/-- The first `k` conjugate residual directions span the Krylov space:
`span {p_0, …, p_{k-1}} = 𝒦_k(A, r₀)`. This is what turns the orthogonality relations — which only
say that `r_k` is `A`-orthogonal to the earlier directions — into the minimal-residual property
`CR.isMinResIterate`, since orthogonality to the span is what the specification asks for.
Degenerate steps cost nothing: a direction whose image under `A` dies contributes no new
dimension, and the residuals, which lie in the same span, still fill the Krylov space out. -/
theorem span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
  le_antisymm (dirSpan_le_subspace A b x₀ k) (subspace_le_dirSpan b x₀ k
    fun i _ => apply_direction_mem_dirSpan b x₀ i
      fun h => apply_direction_eq_zero_of_alpha_eq_zero b x₀
        (residual_eq_zero_of_inner_self b x₀ hA) h)

/-- CR realises the minimal-residual specification (`= MINRES = GMRES` on symmetric systems). -/
theorem isMinResIterate (k : ℕ) : IsMinResIterate A b x₀ k (iterate A b x₀ k).x := by
  refine IsMinRes.iff_isPetrovGalerkin.2 ⟨iterate_sub_mem A b x₀ k, ?_⟩
  rw [← residual_eq, ← span_direction_eq b x₀ hA k, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [← inner_conj_symm, inner_residual_apply_direction_eq_zero b x₀ hA i.2, map_zero]

/-- Finite termination: on a symmetric coercive `A` the conjugate residual iteration is exact once
`k` reaches the grade of `r₀`, so it is a direct method in at most `grade A r₀` steps. The iterate
minimizes the residual over `x₀ + 𝒦_k`, and at the grade that space already contains the exact
correction. -/
theorem residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0 := by
  rw [residual_eq, sub_eq_zero]
  exact ((isMinResIterate b x₀ hA k).apply_eq_of_grade_le hk
    hA.isCoercive.injective.injOn).symm

/-- The third fact coercivity supplies: the iteration terminates, so every index is passed by
a step whose residual has died. -/
private theorem exists_residual_eq_zero [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] :
    ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0 :=
  fun n => ⟨max n (grade A (b - A x₀)), le_max_left _ _,
    residual_eq_zero_of_grade_le b x₀ hA (le_max_right _ _)⟩

/-- For `x₀ = 0` and `b ≠ 0` the first CR iterate `x₁ = α₀ b` is nonzero, so the backward-error
ratio `‖r_k‖ / ‖x_k‖` is well defined from step `1` on. -/
theorem iterate_one_x_ne_zero (hb : b ≠ 0) : (iterate A b 0 1).x ≠ 0 := by
  have h0 : (iterate A b 0 0).x = 0 := rfl
  have hp : (iterate A b 0 0).p = b := by simp [iterate, init]
  have hr : (iterate A b 0 0).r = b := by simp [iterate, init]
  rw [iterate_succ_x, h0, hp, zero_add, smul_ne_zero_iff]
  refine ⟨?_, hb⟩
  rw [alpha, hr, q_eq, hp]
  refine div_ne_zero (fun h => hb (eq_zero_of_inner_self_eq_zero hA h)) fun h => hb ?_
  exact hA.isCoercive.injective (by rw [inner_self_eq_zero.1 h, map_zero])

/-! ### Signs (Fong–Saunders, *CG versus MINRES*, Thm 2.2) -/

omit hA in
private theorem alpha_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : alpha A (iterate A b x₀ k) =
    ((RCLike.re (inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) /
      ‖(iterate A b x₀ k).q‖ ^ 2 : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, inner_self_ofReal hAs, ← inner_self_eq_ofReal_norm_sq, alpha]

omit hA in
private theorem re_alpha_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r))) (k : ℕ) :
    0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (hnn k) (sq_nonneg _)

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (a): the step lengths `α_i` are nonnegative
reals.  Clause (b), the same for the direction coefficients `β_i`, is used only inside this
module. -/
theorem re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k)) :=
  re_alpha_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA) k

omit hA in
private theorem beta_eq_ofReal (hAs : A.IsSymmetric) (k : ℕ) : beta A (iterate A b x₀ k) =
    ((RCLike.re (inner 𝕜 (iterate A b x₀ (k + 1)).r (A (iterate A b x₀ (k + 1)).r)) /
      RCLike.re (inner 𝕜 (iterate A b x₀ k).r (A (iterate A b x₀ k).r)) : ℝ) : 𝕜) := by
  rw [RCLike.ofReal_div, inner_self_ofReal hAs, inner_self_ofReal hAs, beta_iterate]

omit hA in
private theorem re_beta_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r))) (k : ℕ) :
    0 ≤ RCLike.re (beta A (iterate A b x₀ k)) := by
  rw [beta_eq_ofReal b x₀ hAs k, RCLike.ofReal_re]
  exact div_nonneg (hnn (k + 1)) (hnn k)

omit hA in
private theorem re_alpha_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (alpha A (iterate A b x₀ k) * z) =
      RCLike.re (alpha A (iterate A b x₀ k)) * RCLike.re z := by
  rw [alpha_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
private theorem re_beta_mul (hAs : A.IsSymmetric) (k : ℕ) (z : 𝕜) :
    RCLike.re (beta A (iterate A b x₀ k) * z) =
      RCLike.re (beta A (iterate A b x₀ k)) * RCLike.re z := by
  rw [beta_eq_ofReal b x₀ hAs k, RCLike.re_ofReal_mul, RCLike.ofReal_re]

omit hA in
/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (c) under symmetry, the sign hypothesis and
nondegeneracy alone. -/
private theorem re_inner_direction_apply_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p)) := by
  have key : ∀ m n : ℕ, m ≤ n →
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ m).p (A (iterate A b x₀ n).p)) := by
    intro m
    induction m with
    | zero =>
      intro n _
      rw [direction_zero, inner_residual_apply_direction_eq' b x₀ hAs hz (Nat.zero_le n)]
      exact hnn n
    | succ m ih =>
      intro n hn
      rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta hAs, map_add,
        inner_residual_apply_direction_eq' b x₀ hAs hz (show m + 1 ≤ n by omega),
        re_beta_mul b x₀ hAs]
      exact add_nonneg (hnn n)
        (mul_nonneg (re_beta_nonneg b x₀ hAs hnn m) (ih n (by omega)))
  rcases le_total i j with h | h
  · exact key i j h
  · rw [← hAs, ← inner_conj_symm, RCLike.conj_re]
    exact key j i h

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (c): `re ⟪p_i, A p_j⟫ ≥ 0`. -/
theorem re_inner_direction_apply_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p)) :=
  re_inner_direction_apply_direction_nonneg' b x₀ hA.isSymmetric
    (re_inner_residual_self_nonneg b x₀ hA) (residual_eq_zero_of_inner_self b x₀ hA) i j

omit hA in
/-- `re ⟪A (x_m - x_i), p_j⟫ ≥ 0` for `i ≤ m`: the telescoping sum `∑ α_l A p_l`. -/
private theorem re_inner_apply_sub_direction_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    {i m : ℕ} (him : i ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (A ((iterate A b x₀ m).x - (iterate A b x₀ i).x))
      (iterate A b x₀ j).p) := by
  induction m, him using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ i).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ i).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    have h2 : inner 𝕜 (A (iterate A b x₀ m).p) (iterate A b x₀ j).p =
        inner 𝕜 (iterate A b x₀ m).p (A (iterate A b x₀ j).p) := hAs _ _
    rw [h, map_add, map_smul, inner_add_left, inner_smul_left, conj_alpha hAs, map_add,
      re_alpha_mul b x₀ hAs, h2]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg' b x₀ hAs hnn m)
      (re_inner_direction_apply_direction_nonneg' b x₀ hAs hnn hz m j))

omit hA in
/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (f) under symmetry, the sign hypothesis,
nondegeneracy and termination alone. -/
private theorem re_inner_residual_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p) := by
  obtain ⟨m, him, hr⟩ := hterm i
  rw [residual_eq, sub_eq_zero] at hr
  have hri : (iterate A b x₀ i).r = A ((iterate A b x₀ m).x - (iterate A b x₀ i).x) := by
    rw [map_sub, ← hr, ← residual_eq]
  rw [hri]
  exact re_inner_apply_sub_direction_nonneg b x₀ hAs hnn hz him j

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (f): `re ⟪r_i, p_j⟫ ≥ 0`. -/
theorem re_inner_residual_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p) :=
  re_inner_residual_direction_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA)
    (residual_eq_zero_of_inner_self b x₀ hA) (exists_residual_eq_zero b x₀ hA) i j

omit hA in
/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (d) under the same hypotheses. -/
private theorem re_inner_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) := by
  induction i with
  | zero =>
    rw [direction_zero]
    exact re_inner_residual_direction_nonneg' b x₀ hAs hnn hz hterm 0 j
  | succ i ih =>
    rw [iterate_succ_p, inner_add_left, inner_smul_left, conj_beta hAs, map_add,
      re_beta_mul b x₀ hAs]
    exact add_nonneg (re_inner_residual_direction_nonneg' b x₀ hAs hnn hz hterm (i + 1) j)
      (mul_nonneg (re_beta_nonneg b x₀ hAs hnn i) ih)

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (d): `re ⟪p_i, p_j⟫ ≥ 0` (uses finite
termination). -/
theorem re_inner_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p) :=
  re_inner_direction_nonneg' b x₀ hA.isSymmetric (re_inner_residual_self_nonneg b x₀ hA)
    (residual_eq_zero_of_inner_self b x₀ hA) (exists_residual_eq_zero b x₀ hA) i j

omit hA in
/-- `re ⟪x_m - x_i, p_j⟫ ≥ 0` for `i ≤ m`. -/
private theorem re_inner_sub_direction_nonneg (hAs : A.IsSymmetric)
    (hnn : ∀ j,
      0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r)))
    (hz : ∀ j,
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) = 0 → (iterate A b x₀ j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b x₀ m).r = 0) {i m : ℕ} (him : i ≤ m) (j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 ((iterate A b x₀ m).x - (iterate A b x₀ i).x)
      (iterate A b x₀ j).p) := by
  induction m, him using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h : (iterate A b x₀ (m + 1)).x - (iterate A b x₀ i).x =
        ((iterate A b x₀ m).x - (iterate A b x₀ i).x) +
          alpha A (iterate A b x₀ m) • (iterate A b x₀ m).p := by
      rw [iterate_succ_x]; abel
    rw [h, inner_add_left, inner_smul_left, conj_alpha hAs, map_add, re_alpha_mul b x₀ hAs]
    exact add_nonneg ih (mul_nonneg (re_alpha_nonneg' b x₀ hAs hnn m)
      (re_inner_direction_nonneg' b x₀ hAs hnn hz hterm m j))

omit hA in
/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (e) under the same hypotheses. -/
private theorem re_inner_iterate_direction_nonneg' (hAs : A.IsSymmetric)
    (hnn : ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)))
    (hz : ∀ j, inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r) = 0 →
      (iterate A b 0 j).r = 0)
    (hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b 0 m).r = 0) (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p) := by
  have h := re_inner_sub_direction_nonneg b 0 hAs hnn hz hterm (Nat.zero_le i) j
  rwa [show (iterate A b 0 0).x = 0 from rfl, sub_zero] at h

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.2 (e): `re ⟪x_i, p_j⟫ ≥ 0` for `x₀ = 0`. -/
theorem re_inner_iterate_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p) :=
  re_inner_iterate_direction_nonneg' b hA.isSymmetric (re_inner_residual_self_nonneg b 0 hA)
    (residual_eq_zero_of_inner_self b 0 hA) (exists_residual_eq_zero b 0 hA) i j

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.3: `‖x_k‖` is nondecreasing for `x₀ = 0`. -/
theorem norm_iterate_monotone [FiniteDimensional 𝕜 E] :
    Monotone fun k => ‖(iterate A b 0 k).x‖ := by
  refine monotone_nat_of_le_succ fun k => ?_
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 k).x
      (alpha A (iterate A b 0 k) • (iterate A b 0 k).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hA.isSymmetric]
    exact mul_nonneg (re_alpha_nonneg b 0 hA k) (re_inner_iterate_direction_nonneg b hA k k)
  have hsq : ‖(iterate A b 0 k).x‖ ^ 2 ≤ ‖(iterate A b 0 (k + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b 0 k) • (iterate A b 0 k).p‖]
  nlinarith [norm_nonneg (iterate A b 0 k).x, norm_nonneg (iterate A b 0 (k + 1)).x]

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.4: `‖x* - x_k‖` is nonincreasing. -/
theorem norm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖ := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hr : (iterate A b x₀ (max (k + 1) (grade A (b - A x₀)))).r = 0 :=
    residual_eq_zero_of_grade_le b x₀ hA (le_max_right (k + 1) _)
  rw [residual_eq, sub_eq_zero] at hr
  have hxm : xstar = (iterate A b x₀ (max (k + 1) (grade A (b - A x₀)))).x :=
    hA.isCoercive.injective (hstar.trans hr)
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hnn : 0 ≤ RCLike.re (inner 𝕜 (xstar - (iterate A b x₀ (k + 1)).x)
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    refine mul_nonneg (re_alpha_nonneg b x₀ hA k) ?_
    rw [hxm]
    exact re_inner_sub_direction_nonneg b x₀ hA.isSymmetric
      (re_inner_residual_self_nonneg b x₀ hA) (residual_eq_zero_of_inner_self b x₀ hA)
      (exists_residual_eq_zero b x₀ hA) (le_max_left (k + 1) _) k
  have hsq : ‖xstar - (iterate A b x₀ (k + 1)).x‖ ^ 2 ≤ ‖xstar - (iterate A b x₀ k).x‖ ^ 2 := by
    rw [hexp, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [sq_nonneg ‖alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p‖]
  nlinarith [norm_nonneg (xstar - (iterate A b x₀ (k + 1)).x),
    norm_nonneg (xstar - (iterate A b x₀ k).x)]

/-- `re ⟪A (u + w), u + w⟫ = re ⟪A u, u⟫ + 2 re ⟪A u, w⟫ + re ⟪A w, w⟫`. -/
private theorem re_inner_apply_add (u w : E) :
    RCLike.re (inner 𝕜 (A (u + w)) (u + w)) =
      RCLike.re (inner 𝕜 (A u) u) + 2 * RCLike.re (inner 𝕜 (A u) w) +
        RCLike.re (inner 𝕜 (A w) w) := by
  have h : inner 𝕜 (A w) u = (starRingEnd 𝕜) (inner 𝕜 (A u) w) := by
    rw [inner_conj_symm, hA.isSymmetric]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, h]
  simp only [map_add, RCLike.conj_re]
  ring

/-- Fong–Saunders, *CG versus MINRES*, Thm 2.5: `‖x* - x_k‖_A` is nonincreasing.  The paper
states the strict decrease, which holds while the iteration is still moving; the nonstrict form
proved here is the one valid at every step, the iterate being stationary past termination. -/
theorem energyNorm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hexp : xstar - (iterate A b x₀ k).x = (xstar - (iterate A b x₀ (k + 1)).x) +
      alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p := by
    rw [iterate_succ_x]; abel
  have hAe : A (xstar - (iterate A b x₀ (k + 1)).x) = (iterate A b x₀ (k + 1)).r := by
    rw [map_sub, hstar, ← residual_eq]
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (A (xstar - (iterate A b x₀ (k + 1)).x))
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [hAe, inner_smul_right, re_alpha_mul b x₀ hA.isSymmetric]
    exact mul_nonneg (re_alpha_nonneg b x₀ hA k)
      (re_inner_residual_direction_nonneg b x₀ hA (k + 1) k)
  have hself : 0 ≤ RCLike.re (inner 𝕜 (A (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p))
      (alpha A (iterate A b x₀ k) • (iterate A b x₀ k).p)) := by
    rw [hA.isSymmetric]
    exact re_inner_self_nonneg hA _
  have hsq : energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 ≤
      energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 := by
    rw [hA.energyNorm_sq, hA.energyNorm_sq, hexp, re_inner_apply_add hA]
    linarith
  nlinarith [energyNorm_nonneg A (xstar - (iterate A b x₀ k).x),
    energyNorm_nonneg A (xstar - (iterate A b x₀ (k + 1)).x)]

omit hA in
/-- The CR/MINRES analogue of Steihaug's theorem (Fong–Saunders, *CG versus MINRES*, §4.2): for
a symmetric, possibly indefinite `A` and the CR iterates from `x₀ = 0`, if the iteration
terminates at step `ℓ` and `0 < re ⟪r_j, A r_j⟫` for every `j < ℓ`, then `‖x_i‖ < ‖x_{i+1}‖` for
every `i < ℓ`.

Positivity is assumed all the way up to the termination index `ℓ`, not merely up to `i`, and
weakening it to nonvanishing is not enough: the paper's proof of Thm 2.2 (d)
expands `r_i` as `A (x_ℓ - x_i) = ∑_{m ≥ i} α_m A p_m`, so a single `re ⟪r_m, A r_m⟫ < 0` beyond
`i` turns `re ⟪r_i, p_j⟫` negative and breaks the chain (f) ⇒ (d) ⇒ (e).  A separate
nondegeneracy hypothesis `0 < re ⟪A p_j, p_j⟫` would be redundant, since
`⟪r_j, A p_j⟫ = ⟪r_j, A r_j⟫ ≠ 0` already forces `A p_j ≠ 0`.

Transfers to MINRES through `CR.isMinResIterate_of_no_breakdown`. -/
theorem norm_iterate_lt_of_pos (hAs : A.IsSymmetric) {ℓ : ℕ}
    (hstop : (iterate A b 0 ℓ).r = 0)
    (hpos : ∀ j < ℓ, 0 < RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)))
    {i : ℕ} (hi : i < ℓ) :
    ‖(iterate A b 0 i).x‖ < ‖(iterate A b 0 (i + 1)).x‖ := by
  have hzero : ∀ j, ℓ ≤ j → (iterate A b 0 j).r = 0 := fun j hj => by
    rw [iterate_eq_of_residual_eq_zero A b 0 hstop j hj]; exact hstop
  have hnn : ∀ j, 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r)) := by
    intro j
    rcases lt_or_ge j ℓ with h | h
    · exact le_of_lt (hpos j h)
    · rw [hzero j h, inner_zero_left, map_zero]
  have hz : ∀ j, inner 𝕜 (iterate A b 0 j).r (A (iterate A b 0 j).r) = 0 →
      (iterate A b 0 j).r = 0 := by
    intro j h
    rcases lt_or_ge j ℓ with hj | hj
    · exact absurd (hpos j hj) (by rw [h, map_zero]; exact lt_irrefl 0)
    · exact hzero j hj
  have hterm : ∀ n, ∃ m, n ≤ m ∧ (iterate A b 0 m).r = 0 :=
    fun n => ⟨max n ℓ, le_max_left _ _, hzero _ (le_max_right _ _)⟩
  have hri := hpos i hi
  -- `⟪r_i, A p_i⟫ = ⟪r_i, A r_i⟫ ≠ 0`, so neither `A p_i` nor `p_i` can vanish
  have hqne : (iterate A b 0 i).q ≠ 0 := by
    intro h
    have hd := (invariant' b 0 hAs hz i).diag
    rw [q_eq] at h
    rw [h, inner_zero_right] at hd
    rw [← hd, map_zero] at hri
    exact lt_irrefl 0 hri
  have hpne : (iterate A b 0 i).p ≠ 0 := fun h => hqne (by rw [q_eq, h, map_zero])
  have hαpos : 0 < RCLike.re (alpha A (iterate A b 0 i)) := by
    rw [alpha_eq_ofReal b 0 hAs i, RCLike.ofReal_re]
    exact div_pos hri (pow_pos (norm_pos_iff.2 hqne) 2)
  have hαne : alpha A (iterate A b 0 i) ≠ 0 := fun h => by
    rw [h, map_zero] at hαpos; exact lt_irrefl 0 hαpos
  have hcross : 0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x
      (alpha A (iterate A b 0 i) • (iterate A b 0 i).p)) := by
    rw [inner_smul_right, re_alpha_mul b 0 hAs]
    exact mul_nonneg (le_of_lt hαpos)
      (re_inner_iterate_direction_nonneg' b hAs hnn hz hterm i i)
  have hnz : 0 < ‖alpha A (iterate A b 0 i) • (iterate A b 0 i).p‖ := by
    rw [norm_smul]
    exact mul_pos (norm_pos_iff.2 hαne) (norm_pos_iff.2 hpne)
  have hsq : ‖(iterate A b 0 i).x‖ ^ 2 < ‖(iterate A b 0 (i + 1)).x‖ ^ 2 := by
    rw [iterate_succ_x, norm_add_sq (𝕜 := 𝕜)]
    nlinarith [hnz]
  nlinarith [norm_nonneg (iterate A b 0 i).x, norm_nonneg (iterate A b 0 (i + 1)).x]

omit hA in
/-- CR on a symmetric, possibly indefinite or singular, operator
(Fong–Saunders, *CG versus MINRES*, §2; Choi, *Iterative Methods for Singular Linear Equations
and Least-Squares Problems*): as long as no breakdown occurs (`⟪r_j, A r_j⟫ ≠ 0` and
`A p_j ≠ 0` for `j < k`), the iterate `x_k` is the minimal-residual iterate.

The section's coercivity hypothesis is deliberately omitted here: carrying it would make this a
special case of `CR.isMinResIterate` instead of the indefinite or singular statement. -/
theorem isMinResIterate_of_no_breakdown (hA : A.IsSymmetric) (k : ℕ)
    (h1 : ∀ j < k, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) ≠ 0)
    (h2 : ∀ j < k, (iterate A b x₀ j).q ≠ 0) :
    IsMinResIterate A b x₀ k (iterate A b x₀ k).x := by
  have halpha : ∀ j < k, alpha A (iterate A b x₀ j) ≠ 0 := by
    intro j hj
    rw [alpha]
    exact div_ne_zero (h1 j hj) fun hq => h2 j hj (inner_self_eq_zero.1 hq)
  have hdeg : ∀ j < k, alpha A (iterate A b x₀ j) = 0 → A (iterate A b x₀ j).p = 0 :=
    fun j hj h => absurd h (halpha j hj)
  have hbeta : ∀ j < k, beta A (iterate A b x₀ j) *
      inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) =
        inner 𝕜 (iterate A b x₀ (j + 1)).r (A (iterate A b x₀ (j + 1)).r) := by
    intro j hj
    rw [beta_iterate, div_mul_cancel₀ _ (h1 j hj)]
  have hinv := invariant_of b x₀ hA k hdeg hbeta
  have hspan : Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) =
      subspace A (b - A x₀) k :=
    le_antisymm (dirSpan_le_subspace A b x₀ k)
      (subspace_le_dirSpan b x₀ k fun i hi => apply_direction_mem_dirSpan b x₀ i (hdeg i hi))
  refine IsMinRes.iff_isPetrovGalerkin.2 ⟨iterate_sub_mem A b x₀ k, ?_⟩
  rw [← residual_eq, ← hspan, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [← inner_conj_symm, hinv.rq i i.2, map_zero]

end CR

namespace Krylov

/-- Saad, *Iterative Methods*, Lemma 6.21 (GCR / ORTHOMIN / ORTHODIR): if `p_0, …, p_{m-1}` are
`AᴴA`-orthogonal and span `𝒦_m(A, r₀)`, then `x_m = x₀ + ∑_j (⟪r_j, A p_j⟫ / ‖A p_j‖²) p_j`
(with `r_j` the successive residuals) is the minimal-residual iterate. -/
theorem isMinResIterate_of_orthogonal_directions {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ}
    (p : ℕ → E) (horth : ∀ i < m, ∀ j < m, i ≠ j → inner 𝕜 (A (p i)) (A (p j)) = 0)
    (hne : ∀ i < m, A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p i) = subspace A (b - A x₀) m)
    (x : ℕ → E) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j +
      (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j) :
    IsMinResIterate A b x₀ m (x m) := by
  -- the residual recurrence `r_{j+1} = r_j - c_j A p_j`
  have hres : ∀ j, b - A (x (j + 1)) = (b - A (x j)) -
      (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • A (p j) := by
    intro j
    rw [hstep j, map_add, map_smul]
    abel
  -- `x_j - x₀` lies in the span of the directions
  have hmem : ∀ j ≤ m, x j - x₀ ∈ Submodule.span 𝕜 (Set.range fun i : Fin m => p i) := by
    intro j hj
    induction j with
    | zero => rw [hx0, sub_self]; exact Submodule.zero_mem _
    | succ j ih =>
      have h : x (j + 1) - x₀ = (x j - x₀) +
          (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j := by
        rw [hstep j]; abel
      rw [h]
      exact Submodule.add_mem _ (ih (by omega)) (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩))
  -- the residual becomes orthogonal to `A p_i` at step `i + 1` and stays so
  have hkill : ∀ i < m, inner 𝕜 (A (p i)) (b - A (x (i + 1))) = 0 := by
    intro i hi
    rw [hres i, inner_sub_right, inner_smul_right,
      div_mul_cancel₀ _ (fun h => hne i hi (inner_self_eq_zero.1 h)), sub_self]
  have hstay : ∀ i < m, ∀ l, i + 1 ≤ l → l ≤ m → inner 𝕜 (A (p i)) (b - A (x l)) = 0 := by
    intro i hi l hl
    induction l, hl using Nat.le_induction with
    | base => exact fun _ => hkill i hi
    | succ l hl ih =>
      intro hlm
      rw [hres l, inner_sub_right, inner_smul_right, ih (by omega),
        horth i hi l (by omega) (by omega), mul_zero, sub_zero]
  refine IsMinRes.iff_isPetrovGalerkin.2 ⟨hspan ▸ hmem m le_rfl, ?_⟩
  rw [← hspan, Submodule.map_span]
  refine Submodule.mem_orthogonal_span.2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hstay i i.2 m (by omega) le_rfl

end Krylov
