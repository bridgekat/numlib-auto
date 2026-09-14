import Numlib.Projection.OneDimensional

/-!
# Conjugate-direction methods

The conjugate-direction method for `A x = b` along a family of directions `d : ℕ → E`
([quarteroni2000numerical] §4.3.4 and §7.2.4, [hestenes1952methods] §3–4, Nocedal–Wright,
*Numerical Optimization*, §5.1): `x_{k+1} = x_k + α_k d_k` with the exact line-search step
`α_k = ⟪d_k, r_k⟫ / ⟪d_k, A d_k⟫`, `r_k = b - A x_k`, which is `Projection.step1 A b (d k) (d k)`
of `Numlib/Projection/OneDimensional`, for directions that are mutually `A`-conjugate,
`⟪A d_k, d_m⟫ = 0` for `k ≠ m`.

## Main definitions

* `ConjugateDirection.IsConjugateFamily A d`: the directions are pairwise `A`-conjugate. The
  directions are *not* required to be nonzero: the conjugate gradient directions vanish past the
  grade of the residual and are still conjugate (`CG.isConjugateFamily_direction` in
  `Numlib/Krylov/CG`), the step is total (a zero direction gives a zero step), and the one
  statement that needs `d k ≠ 0`, finite termination, says so.
* `ConjugateDirection.iterate A b d x₀ k`: the `k`-th iterate from `x₀`.

## Main statements

The *expanding subspace theorem* ([quarteroni2000numerical] Theorem 4.11 and Property 7.6,
Nocedal–Wright Theorem 5.2): for coercive `A` and conjugate directions,

* `ConjugateDirection.inner_residual_direction_eq_zero`: `r_{k+1} ⟂ d_m` for every `m ≤ k`;
* `ConjugateDirection.isGalerkin_iterate`: `x_k` is the Galerkin iterate over
  `x₀ + span {d_0, …, d_{k-1}}`, hence (for symmetric `A`, by `IsGalerkin.quadratic_le` and
  `IsGalerkin.iff_energyNorm_min` of `Numlib/Projection/Optimality`) it minimizes the energy
  functional `½ ⟪A x, x⟫ - ⟪b, x⟫`, equivalently the energy norm of the error, over that affine
  space;
* `ConjugateDirection.apply_iterate_eq_of_span_eq_top`,
  `ConjugateDirection.iterate_eq_of_finrank_le`: finite termination — once the directions span
  the space the iterate is exact, and `n` nonzero conjugate directions in dimension `n` do span
  it (`IsConjugateFamily.linearIndependent`).

## Design

Nothing here is Krylov-specific: the directions are arbitrary, which is why the module sits under
`Projection` and below `Krylov`. The conjugate gradient recurrence of `Numlib/Krylov/CG` is the
instance in which the directions are generated from the residuals
(`CG.iterate_x_eq_conjugateDirection_iterate`), and the nonlinear conjugate gradient methods of
`Numlib/Optimization/ConjugateGradient` reduce to it on a quadratic. The statements need only
coercivity of `A` (symmetry enters through the consumers' optimality characterizations), and are
at rung L1: an inner product space, no completeness; termination is at L3.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace ConjugateDirection

/-- A family of mutually `A`-conjugate (`A`-orthogonal) directions: `⟪A d_k, d_m⟫ = 0` for
`k ≠ m` ([quarteroni2000numerical] §4.3.4, §7.2.4). Both orders `k ≠ m` and `m ≠ k` are
included, so no symmetry of `A` is presupposed; the directions may vanish. -/
def IsConjugateFamily (A : E →ₗ[𝕜] E) (d : ℕ → E) : Prop :=
  ∀ k m, k ≠ m → inner 𝕜 (A (d k)) (d m) = 0

/-- The conjugate-direction iterates: `iterate 0 = x₀` and
`iterate (k + 1) = Projection.step1 A b (d k) (d k) (iterate k)`, that is
`x_{k+1} = x_k + (⟪d_k, r_k⟫ / ⟪d_k, A d_k⟫) • d_k` with `r_k = b - A x_k` — the descent method
([quarteroni2000numerical] (7.25)) along the directions `d` with the exact step
([quarteroni2000numerical] (4.39), (7.36)). -/
noncomputable def iterate (A : E →ₗ[𝕜] E) (b : E) (d : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => Projection.step1 A b (d k) (d k) (iterate A b d x₀ k)

variable (A : E →ₗ[𝕜] E) (b : E) (d : ℕ → E) (x₀ : E)

@[simp] theorem iterate_zero : iterate A b d x₀ 0 = x₀ := rfl

/-- The recurrence: the next iterate is one exact step along the current direction. -/
theorem iterate_succ (k : ℕ) :
    iterate A b d x₀ (k + 1) = Projection.step1 A b (d k) (d k) (iterate A b d x₀ k) := rfl

/-- The recurrence with the step written out: `x_{k+1} = x_k + α_k • d_k`,
`α_k = ⟪d_k, r_k⟫ / ⟪d_k, A d_k⟫`. -/
theorem iterate_succ_eq (k : ℕ) :
    iterate A b d x₀ (k + 1) = iterate A b d x₀ k +
      (inner 𝕜 (d k) (b - A (iterate A b d x₀ k)) / inner 𝕜 (d k) (A (d k))) • d k := rfl

/-- The residual recurrence `r_{k+1} = r_k - α_k • A d_k`. -/
theorem residual_succ (k : ℕ) :
    b - A (iterate A b d x₀ (k + 1)) = (b - A (iterate A b d x₀ k)) -
      (inner 𝕜 (d k) (b - A (iterate A b d x₀ k)) / inner 𝕜 (d k) (A (d k))) • A (d k) := by
  rw [iterate_succ_eq, map_add, map_smul]
  abel

/-- The iterates stay in the affine space spanned by the directions used so far:
`x_k - x₀ ∈ span {d_0, …, d_{k-1}}`. -/
theorem iterate_sub_mem_span (k : ℕ) :
    iterate A b d x₀ k - x₀ ∈ Submodule.span 𝕜 (Set.range fun i : Fin k => d i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmono : Submodule.span 𝕜 (Set.range fun i : Fin k => d i) ≤
        Submodule.span 𝕜 (Set.range fun i : Fin (k + 1) => d i) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Fin.castSucc i, rfl⟩
    rw [iterate_succ_eq, add_sub_right_comm]
    exact Submodule.add_mem _ (hmono ih)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last k, rfl⟩))

/-- Once an iterate is exact the iteration is stationary: the residual vanishes, so every later
step has coefficient `0`. -/
theorem iterate_add_eq_of_apply_eq {k : ℕ} (hk : A (iterate A b d x₀ k) = b) (j : ℕ) :
    iterate A b d x₀ (k + j) = iterate A b d x₀ k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, iterate_succ_eq, ih, hk, sub_self, inner_zero_right, zero_div, zero_smul,
      add_zero]

variable {A d}

/-- The step along `d_k` makes the new residual orthogonal to `d_k`: `⟪r_{k+1}, d_k⟫ = 0`.  This is
the exactness of the line search, `Projection.step1_isGalerkin`; coercivity supplies the
nondegeneracy of the step, and a zero direction gives a zero step. -/
theorem inner_residual_succ_direction_self_eq_zero (hA : A.IsCoercive) (k : ℕ) :
    inner 𝕜 (b - A (iterate A b d x₀ (k + 1))) (d k) = 0 := by
  rw [iterate_succ, inner_eq_zero_symm]
  exact (Projection.step1_isGalerkin hA (d k) _).inner_residual_eq_zero
    (Submodule.mem_span_singleton_self _)

/-- [quarteroni2000numerical] Property 7.6, third clause (and (4.44)): with coercive `A` and
conjugate directions the residual `r_{k+1}` is orthogonal to every direction used so far,
`⟪r_{k+1}, d_m⟫ = 0` for `m ≤ k`.  The step along `d_k` makes `r_{k+1} ⟂ d_k`, and since
`A d_k ⟂ d_m` for `m < k` it leaves `⟪r, d_m⟫`, already zero by induction, unchanged. -/
theorem inner_residual_direction_eq_zero (hA : A.IsCoercive) (hd : IsConjugateFamily A d) :
    ∀ k m, m ≤ k → inner 𝕜 (b - A (iterate A b d x₀ (k + 1))) (d m) = 0 := by
  intro k
  induction k with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := Nat.le_zero.1 hm
    exact inner_residual_succ_direction_self_eq_zero b x₀ hA 0
  | succ k ih =>
    intro m hm
    rcases hm.lt_or_eq with hlt | rfl
    · rw [residual_succ, inner_sub_left, inner_smul_left, ih m (Nat.lt_succ_iff.1 hlt),
        hd (k + 1) m hlt.ne', mul_zero, sub_zero]
    · exact inner_residual_succ_direction_self_eq_zero b x₀ hA (k + 1)

/-- The direction-first form of `inner_residual_direction_eq_zero`: `⟪d_m, r_{k+1}⟫ = 0` for
`m ≤ k`. -/
theorem inner_direction_residual_eq_zero (hA : A.IsCoercive) (hd : IsConjugateFamily A d)
    {k m : ℕ} (h : m ≤ k) : inner 𝕜 (d m) (b - A (iterate A b d x₀ (k + 1))) = 0 :=
  inner_eq_zero_symm.1 (inner_residual_direction_eq_zero b x₀ hA hd k m h)

/-- The expanding subspace theorem ([quarteroni2000numerical] Theorem 4.11 and Property 7.6,
second clause; Nocedal–Wright, *Numerical Optimization*, Theorem 5.2): with coercive `A` and
conjugate directions the `k`-th iterate is the Galerkin iterate over `x₀ + span {d_0, …, d_{k-1}}`.
For symmetric `A` this says, by `IsGalerkin.quadratic_le` and `IsGalerkin.iff_energyNorm_min`,
that `x_k` minimizes the energy functional `½ ⟪A x, x⟫ - ⟪b, x⟫`, equivalently the energy norm of
the error, over that affine space. -/
theorem isGalerkin_iterate (hA : A.IsCoercive) (hd : IsConjugateFamily A d) (k : ℕ) :
    IsGalerkin A b x₀ (Submodule.span 𝕜 (Set.range fun i : Fin k => d i))
      (iterate A b d x₀ k) := by
  refine ⟨iterate_sub_mem_span A b d x₀ k, Submodule.mem_orthogonal_span.2 ?_⟩
  rintro _ ⟨i, rfl⟩
  cases k with
  | zero => exact i.elim0
  | succ k => exact inner_direction_residual_eq_zero b x₀ hA hd (Nat.lt_succ_iff.1 i.2)

/-- Nonzero conjugate directions of a coercive operator are linearly independent: testing a
vanishing combination against `A d_j` isolates the `j`-th coefficient times `⟪A d_j, d_j⟫ ≠ 0`.
Stated for the first `k` directions, since in finite dimension a whole sequence of nonzero
conjugate directions cannot exist. -/
theorem IsConjugateFamily.linearIndependent (hA : A.IsCoercive) (hd : IsConjugateFamily A d)
    {k : ℕ} (h0 : ∀ i < k, d i ≠ 0) : LinearIndependent 𝕜 (fun i : Fin k => d i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg j => ?_
  have hsum : inner 𝕜 (A (∑ i, g i • d i)) (d j) = 0 := by rw [hg, map_zero, inner_zero_left]
  rw [map_sum, sum_inner, Finset.sum_eq_single j (fun i _ hij => ?_)
    (fun h => (h (Finset.mem_univ j)).elim)] at hsum
  · rw [map_smul, inner_smul_left, mul_eq_zero] at hsum
    rcases hsum with h | h
    · simpa using h
    · exact absurd h fun h' => by
        have := hA.inner_self_pos (h0 j j.2)
        rw [h', map_zero] at this
        exact lt_irrefl 0 this
  · rw [map_smul, inner_smul_left, hd i j (fun h => hij (Fin.ext h)), mul_zero]

/-- Finite termination, in its intrinsic form: once the directions used span the whole space the
iterate is exact, because its residual is orthogonal to everything. -/
theorem apply_iterate_eq_of_span_eq_top (hA : A.IsCoercive) (hd : IsConjugateFamily A d) {k : ℕ}
    (hk : Submodule.span 𝕜 (Set.range fun i : Fin k => d i) = ⊤) :
    A (iterate A b d x₀ k) = b := by
  have h := (isGalerkin_iterate b x₀ hA hd k).orth
  rw [hk, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-- [quarteroni2000numerical] Theorem 4.11 and Property 7.6, first clause: in dimension `n`, a
conjugate-direction method with nonzero directions `d_0, …, d_{n-1}` is exact after `n` steps,
since `n` nonzero conjugate directions span the space. -/
theorem apply_iterate_finrank_eq [FiniteDimensional 𝕜 E] (hA : A.IsCoercive)
    (hd : IsConjugateFamily A d) (h0 : ∀ i < Module.finrank 𝕜 E, d i ≠ 0) :
    A (iterate A b d x₀ (Module.finrank 𝕜 E)) = b := by
  refine apply_iterate_eq_of_span_eq_top b x₀ hA hd (Submodule.eq_top_of_finrank_eq ?_)
  rw [finrank_span_eq_card (hd.linearIndependent hA h0), Fintype.card_fin]

/-- Finite termination as a statement about the solution: for `A x* = b`, every iterate from the
`n`-th on equals `x*` when the first `n = dim E` directions are nonzero. -/
theorem iterate_eq_of_finrank_le [FiniteDimensional 𝕜 E] (hA : A.IsCoercive)
    (hd : IsConjugateFamily A d) (h0 : ∀ i < Module.finrank 𝕜 E, d i ≠ 0) {xstar : E}
    (hstar : A xstar = b) {k : ℕ} (hk : Module.finrank 𝕜 E ≤ k) :
    iterate A b d x₀ k = xstar := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [iterate_add_eq_of_apply_eq A b d x₀ (apply_iterate_finrank_eq b x₀ hA hd h0)]
  exact hA.injective (by rw [apply_iterate_finrank_eq b x₀ hA hd h0, hstar])

end ConjugateDirection
