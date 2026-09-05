import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG

/-!
# Krylov methods on the normal equations (CGNR and CGNE)

The two ways of running a symmetric Krylov method on a system that is not symmetric: CGNR is CG
on `Aᴴ A x = Aᴴ b`, and CGNE (Craig's method) is CG on `A Aᴴ u = b` with `x = Aᴴ u`
(Saad, *Iterative Methods*[^saad-iterative] §8.3, Algorithms 8.4 and 8.5).

Nothing here is a new algorithm. The module records that the specifications of
`Numlib/Krylov/Iterate` applied to `Aᴴ A` on the Krylov space `𝒦_m(Aᴴ A, Aᴴ r₀)` are, read back
in the original variables, a minimal-residual specification for `A x = b`
(`Krylov.isGalerkinIterate_adjoint_comp_iff_isMinRes`, CGNR) and a minimal-error specification
(`Krylov.isMinError_of_isGalerkinIterate_comp_adjoint`, CGNE) — Saad's two optimality properties
of §8.3. Every convergence theorem of the CG layer then applies with the spectrum of `Aᴴ A`, that
is with `κ(A)²` in place of `κ(A)`
(`Krylov.IsMinRes.norm_residual_le_of_adjoint_comp`). `Krylov.CGNR.iterate` and
`Krylov.CGNE.iterate` are the two recurrences as a program writes them — one application of `A`
and one of `Aᴴ` per step, never forming a product — identified with the corresponding CG
iterates.

The adjoint enters as a *hypothesis* `∀ u v, ⟪Aᴴ u, v⟫ = ⟪u, A v⟫` on a second operator rather
than as `LinearMap.adjoint A`, so that the module needs neither finite-dimensionality nor
completeness; `LinearMap.adjoint_inner_left` and `ContinuousLinearMap.adjoint_inner_left` supply
the hypothesis where those are available.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

section Adjoint

variable {A Astar : E →ₗ[𝕜] E}

variable (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v))
include hadj

/-- The adjoint relation read the other way round: `⟪u, Aᴴ v⟫ = ⟪A u, v⟫`. -/
theorem inner_adjoint_right (u v : E) : inner 𝕜 u (Astar v) = inner 𝕜 (A u) v := by
  rw [← inner_conj_symm, hadj, inner_conj_symm]

/-- The quadratic form of `Aᴴ A` is the squared norm of `A`: `⟪Aᴴ A x, x⟫ = ‖A x‖²`. This one
identity is what turns every statement about the energy norm of `Aᴴ A` into a statement about
the residual norm of `A`. -/
theorem inner_adjoint_comp_self (x : E) :
    inner 𝕜 ((Astar ∘ₗ A) x) x = ((‖A x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [LinearMap.comp_apply, hadj, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- The energy norm of `Aᴴ A` is the norm of the image under `A`: `‖x‖_{AᴴA} = ‖A x‖`. -/
theorem energyNorm_adjoint_comp (x : E) : energyNorm (Astar ∘ₗ A) x = ‖A x‖ := by
  rw [energyNorm, inner_adjoint_comp_self hadj, RCLike.ofReal_re]
  exact Real.sqrt_sq (norm_nonneg _)

/-- `Aᴴ A` is symmetric, whatever `A` is. -/
theorem adjoint_comp_isSymmetric : (Astar ∘ₗ A).IsSymmetric := by
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hadj, inner_adjoint_right hadj]

/-- `Aᴴ A` is coercive with constant `c` as soon as `A` is bounded below by `√c`, that is
`c ‖x‖² ≤ ‖A x‖²`. -/
theorem adjoint_comp_isCoerciveWith {c : ℝ} (hc : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) :
    (Astar ∘ₗ A).IsCoerciveWith c := by
  intro x
  rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]
  exact hc x

/-- Singular value bounds are quadratic form bounds on `Aᴴ A`: if
`σmin ‖x‖ ≤ ‖A x‖ ≤ σmax ‖x‖` then `Aᴴ A` is symmetric with form between `σmin²` and `σmax²`.
This is the shape in which the Chebyshev convergence theory consumes them. -/
theorem adjoint_comp_isSymmetricBoundedBy {smin smax : ℝ}
    (hmin : ∀ x : E, smin ^ 2 * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hmax : ∀ x : E, ‖A x‖ ^ 2 ≤ smax ^ 2 * ‖x‖ ^ 2) :
    (Astar ∘ₗ A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2) where
  isSymmetric := adjoint_comp_isSymmetric hadj
  le_re_inner x := by rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]; exact hmin x
  re_inner_le x := by rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]; exact hmax x

/-- `Aᴴ A` is symmetric coercive as soon as `A` is bounded below: `c ‖x‖ ≤ ‖A x‖` with `c > 0`.
This is the hypothesis under which the normal equations are a well-posed SPD system, and hence
under which CGNR and CGNE are well defined. -/
theorem adjoint_comp_isSymmetricCoercive {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : E, c * ‖x‖ ≤ ‖A x‖) : (Astar ∘ₗ A).IsSymmetricCoercive where
  isSymmetric := adjoint_comp_isSymmetric hadj
  isCoercive := ⟨c ^ 2, by positivity, adjoint_comp_isCoerciveWith hadj fun x => by
    have h := hbound x
    have h0 : 0 ≤ c * ‖x‖ := by positivity
    nlinarith [norm_nonneg (A x)]⟩

/-- In finite dimension injectivity is enough: `Aᴴ A` is symmetric coercive whenever `A` is
injective, since `⟪Aᴴ A x, x⟫ = ‖A x‖² > 0` off the origin and compactness of the sphere supplies
the constant (`LinearMap.isCoercive_iff_forall_pos`). -/
theorem adjoint_comp_isSymmetricCoercive_of_injective [FiniteDimensional 𝕜 E]
    (hinj : Function.Injective A) : (Astar ∘ₗ A).IsSymmetricCoercive where
  isSymmetric := adjoint_comp_isSymmetric hadj
  isCoercive := (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => by
    rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]
    have : A x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    positivity

end Adjoint

section Optimality

variable {A Astar : E →ₗ[𝕜] E}
  (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) (b x₀ : E)
include hadj

omit hadj in
/-- The initial residual of the normal equations is the image of the initial residual:
`Aᴴ b - Aᴴ A x₀ = Aᴴ (b - A x₀)`. -/
theorem adjoint_residual : Astar b - (Astar ∘ₗ A) x₀ = Astar (b - A x₀) := by
  rw [LinearMap.comp_apply, ← map_sub]

/-- CGNR's optimality (Saad, *Iterative Methods*, §8.3.1): a Galerkin iterate for the normal
equations `Aᴴ A x = Aᴴ b` is exactly a minimal-residual iterate for `A x = b` over the same
affine space `x₀ + 𝒦_m(Aᴴ A, Aᴴ r₀)`.

Both sides say that `b - A x` is orthogonal to `A 𝒦_m`: on the left because the residual of the
normal equations is `Aᴴ (b - A x)`, on the right by `Krylov.IsMinRes.iff_isPetrovGalerkin`. -/
theorem isGalerkinIterate_adjoint_comp_iff_isMinRes (m : ℕ) (x : E) :
    IsGalerkinIterate (Astar ∘ₗ A) (Astar b) x₀ m x ↔
      IsMinRes A b x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m) x := by
  rw [IsMinRes.iff_isPetrovGalerkin]
  constructor <;> rintro ⟨hmem, horth⟩
  · rw [adjoint_residual (A := A) (Astar := Astar) b x₀] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth w
      (by rwa [adjoint_residual (A := A) (Astar := Astar) b x₀])
    rwa [LinearMap.comp_apply, ← map_sub, inner_adjoint_right hadj] at h
  · rw [← adjoint_residual (A := A) (Astar := Astar) b x₀] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    rw [adjoint_residual (A := A) (Astar := Astar) b x₀] at hw
    have h := (Submodule.mem_orthogonal _ _).1 horth (A w) (Submodule.mem_map_of_mem hw)
    rwa [LinearMap.comp_apply, ← map_sub, inner_adjoint_right hadj]

/-- CGNE's optimality (Saad, *Iterative Methods*, §8.3.2): if `u` is a Galerkin iterate for
`A Aᴴ u = b` over `𝒦_m(A Aᴴ, r₀)` and `x = x₀ + Aᴴ (u - u₀)`, then `x` minimizes the *error*
`‖x* - y‖` over `y ∈ x₀ + 𝒦_m(Aᴴ A, Aᴴ r₀)` — the same affine space CGNR minimizes the residual
over, with the other optimality.

Statement correction: the plan asked for `Krylov.IsMinErrorIterate (Aᴴ ∘ A) xstar x₀ m x`.  That
abbreviation is the SYMMLQ specification, whose subspace carries an extra application of the
operator: `IsMinErrorIterate B xstar x₀ m` minimizes over `x₀ + B 𝒦_m(B, B (x* - x₀))`, which for
`B = Aᴴ A` is `x₀ + 𝒦_m(Aᴴ A, Aᴴ A Aᴴ r₀)`, one step short of the space CGNE actually searches.
The conclusion below is `Krylov.IsMinError` over the space the plan's prose names, and the node
is renamed accordingly. -/
theorem isMinError_of_isGalerkinIterate_comp_adjoint {u₀ u xstar : E} {m : ℕ}
    (hx₀ : x₀ = Astar u₀) (hstar : A xstar = b)
    (hu : IsGalerkinIterate (A ∘ₗ Astar) b u₀ m u) :
    IsMinError xstar x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m)
      (x₀ + Astar (u - u₀)) := by
  have hres : b - (A ∘ₗ Astar) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hx₀]
  have hmem : u - u₀ ∈ subspace (A ∘ₗ Astar) (b - A x₀) m := by
    have h := hu.mem; rwa [hres] at h
  have horth : b - (A ∘ₗ Astar) u ∈ (subspace (A ∘ₗ Astar) (b - A x₀) m)ᗮ := by
    have h := hu.orth; rwa [hres] at h
  -- the transported Krylov space: `Aᴴ 𝒦_m(A Aᴴ, r₀) = 𝒦_m(Aᴴ A, Aᴴ r₀)`
  have hmap := map_subspace_comp A Astar (b - A x₀) m
  rw [← hmap]
  refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hmem, fun y hy => ?_⟩
  rw [show xstar - (x₀ + Astar (u - u₀)) = (xstar - x₀) - Astar (u - u₀) by abel,
    show xstar - y = (xstar - x₀) - (y - x₀) by abel]
  refine Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_ hy
  rintro _ ⟨z, hz, rfl⟩
  have h1 : A (Astar (u - u₀)) = (A ∘ₗ Astar) u - (A ∘ₗ Astar) u₀ := by
    rw [← LinearMap.comp_apply]
    exact map_sub _ _ _
  have h2 : A x₀ = (A ∘ₗ Astar) u₀ := by rw [hx₀, LinearMap.comp_apply]
  have h3 : A ((xstar - x₀) - Astar (u - u₀)) = (A xstar - A x₀) - A (Astar (u - u₀)) := by
    rw [map_sub, map_sub]
  have hA : A ((xstar - x₀) - Astar (u - u₀)) = b - (A ∘ₗ Astar) u := by
    rw [h3, hstar, h1, h2]; abel
  rw [inner_adjoint_right hadj, hA, ← inner_conj_symm,
    (Submodule.mem_orthogonal _ _).1 horth z hz, map_zero]

end Optimality

section Convergence

variable {A Astar : E →ₗ[𝕜] E}
  (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v))
include hadj

/-- The CG convergence bound transported to CGNR: with singular values in `[σmin, σmax]`, a
minimal-residual iterate over the normal-equations Krylov space satisfies
`‖r_m‖ ≤ 2 ((κ - 1)/(κ + 1))^m ‖r₀‖` with `κ = σmax/σmin`.

The condition number that appears is the condition number of `Aᴴ A`, whose square root is
`κ(A)`; that squaring is the price of the normal equations, and it is the reason CGNR is slow on
an ill-conditioned system. -/
theorem IsMinRes.norm_residual_le_of_adjoint_comp {smin smax : ℝ} (hs : 0 < smin)
    (hss : smin ≤ smax) (hB : (Astar ∘ₗ A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2))
    {b x₀ : E} {m : ℕ} {x xstar : E} (hstar : A xstar = b)
    (hx : IsMinRes A b x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m) x) :
    ‖b - A x‖ ≤ 2 * ((smax / smin - 1) / (smax / smin + 1)) ^ m * ‖b - A x₀‖ := by
  have hgal : IsGalerkinIterate (Astar ∘ₗ A) (Astar b) x₀ m x :=
    (isGalerkinIterate_adjoint_comp_iff_isMinRes hadj b x₀ m x).2 hx
  have hstar' : (Astar ∘ₗ A) xstar = Astar b := by rw [LinearMap.comp_apply, hstar]
  have h := IsGalerkinIterate.energyNorm_error_le (by positivity)
    (by nlinarith : smin ^ 2 ≤ smax ^ 2) hB hgal hstar'
  have hsqrt : Real.sqrt (smax ^ 2 / smin ^ 2) = smax / smin := by
    rw [← div_pow]
    exact Real.sqrt_sq (div_nonneg (by linarith) hs.le)
  rw [hsqrt, energyNorm_adjoint_comp hadj, energyNorm_adjoint_comp hadj, map_sub, map_sub,
    hstar] at h
  exact h

end Convergence

/-! ### The two recurrences

Saad's Algorithms 8.4 and 8.5, written in the original variables: one application of `A` and one
of `Aᴴ` per step, and the product `Aᴴ A` never formed. Each is identified with the corresponding
`CG.iterate`, so the whole CG theory — the orthogonality relations, finite termination, the
Chebyshev bounds — transfers without a second induction. -/

namespace CGNR

/-- State of the CGNR iteration (Saad, *Iterative Methods*, Algorithm 8.4): iterate, residual
`r = b - A x`, and search direction. The normal-equations residual `z = Aᴴ r` is recomputed
rather than stored. -/
structure State (E : Type*) where
  /-- The current iterate. -/
  x : E
  /-- The residual `b - A x` of the *original* system. -/
  r : E
  /-- The search direction. -/
  p : E

/-- The CGNR step length `α = ‖Aᴴ r‖² / ‖A p‖²`, which is the CG step length of `Aᴴ A`. -/
noncomputable def alpha (A Astar : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (Astar s.r) (Astar s.r) / inner 𝕜 (A s.p) (A s.p)

/-- One CGNR step. -/
noncomputable def step (A Astar : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α := alpha A Astar s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 (Astar r') (Astar r') / inner 𝕜 (Astar s.r) (Astar s.r)
  { x := s.x + α • s.p, r := r', p := Astar r' + β • s.p }

/-- The CGNR direction update coefficient `β = ‖Aᴴ r'‖² / ‖Aᴴ r‖²`. -/
noncomputable def beta (A Astar : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (Astar (step A Astar s).r) (Astar (step A Astar s).r) /
    inner 𝕜 (Astar s.r) (Astar s.r)

/-- The starting state: `r₀ = b - A x₀` and `p₀ = Aᴴ r₀`. -/
def init (A Astar : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := Astar (b - A x₀) }

/-- The `k`-th CGNR state for `A x = b` started at `x₀`. -/
noncomputable def iterate (A Astar : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A Astar)^[k] (init A Astar b x₀)

variable (A Astar : E →ₗ[𝕜] E) (b x₀ : E)

/-- The recurrence: state `k + 1` is one `CGNR.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A Astar b x₀ (k + 1) = step A Astar (iterate A Astar b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem step_x (s : State E) : (step A Astar s).x = s.x + alpha A Astar s • s.p := rfl

theorem step_r (s : State E) : (step A Astar s).r = s.r - alpha A Astar s • A s.p := rfl

theorem step_p (s : State E) :
    (step A Astar s).p = Astar (step A Astar s).r + beta A Astar s • s.p := rfl

/-- CGNR is CG on the normal equations, state by state: the iterate and the search direction
are the CG ones for `Aᴴ A x = Aᴴ b`, the CG residual is `Aᴴ` of the CGNR residual, and the CGNR
residual is the true residual `b - A x`.  Everything proved of `CG.iterate` — the orthogonality
relations, finite termination, the Chebyshev bounds — therefore holds of CGNR. -/
theorem iterate_eq (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) (k : ℕ) :
    (iterate A Astar b x₀ k).x = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).x ∧
      Astar (iterate A Astar b x₀ k).r = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).r ∧
      (iterate A Astar b x₀ k).p = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).p ∧
      (iterate A Astar b x₀ k).r = b - A (iterate A Astar b x₀ k).x := by
  have hinit : Astar (b - A x₀) = Astar b - (Astar ∘ₗ A) x₀ := by
    rw [LinearMap.comp_apply, map_sub]
  induction k with
  | zero => exact ⟨rfl, hinit, hinit, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hres⟩ := ih
    have hq : inner 𝕜 ((Astar ∘ₗ A) (iterate A Astar b x₀ k).p) (iterate A Astar b x₀ k).p
        = inner 𝕜 (A (iterate A Astar b x₀ k).p) (A (iterate A Astar b x₀ k).p) := by
      rw [LinearMap.comp_apply, hadj]
    have halpha : alpha A Astar (iterate A Astar b x₀ k)
        = CG.alpha (Astar ∘ₗ A) (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k) := by
      rw [alpha, CG.alpha, ← hr, ← hp, hq]
    have hr' : Astar (iterate A Astar b x₀ (k + 1)).r
        = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, map_sub, map_smul, hr, hp, halpha,
        LinearMap.comp_apply]
    have hbeta : beta A Astar (iterate A Astar b x₀ k)
        = CG.beta (Astar ∘ₗ A) (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, hr', hr]
    refine ⟨?_, hr', ?_, ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, hx, hp, halpha]
    · rw [iterate_succ, step_p, ← iterate_succ, hr', hbeta, hp, CG.iterate_succ_p]
    · rw [iterate_succ, step_r, step_x, hres, map_add, map_smul, sub_sub]

/-- Saad, *Iterative Methods*, Algorithm 8.4 computes the CG iterates of the normal equations. -/
theorem iterate_x_eq (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) (k : ℕ) :
    (iterate A Astar b x₀ k).x = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).x :=
  (iterate_eq A Astar b x₀ hadj k).1

/-- The CGNR state's residual field is the true residual `b - A x`. -/
theorem residual_eq (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) (k : ℕ) :
    (iterate A Astar b x₀ k).r = b - A (iterate A Astar b x₀ k).x :=
  (iterate_eq A Astar b x₀ hadj k).2.2.2

end CGNR

namespace CGNE

/-- State of the CGNE (Craig) iteration (Saad, *Iterative Methods*, Algorithm 8.5): iterate,
residual `r = b - A x`, and search direction `p`, which is `Aᴴ` of the direction of the
`A Aᴴ` system. -/
structure State (E : Type*) where
  /-- The current iterate. -/
  x : E
  /-- The residual `b - A x`. -/
  r : E
  /-- The search direction. -/
  p : E

/-- The CGNE step length `α = ‖r‖² / ‖p‖²`. -/
noncomputable def alpha (s : State E) : 𝕜 := inner 𝕜 s.r s.r / inner 𝕜 s.p s.p

/-- One CGNE step. -/
noncomputable def step (A Astar : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α : 𝕜 := alpha s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.r s.r
  { x := s.x + α • s.p, r := r', p := Astar r' + β • s.p }

/-- The CGNE direction update coefficient `β = ‖r'‖² / ‖r‖²`. -/
noncomputable def beta (A Astar : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A Astar s).r (step A Astar s).r / inner 𝕜 s.r s.r

/-- The starting state: `r₀ = b - A x₀` and `p₀ = Aᴴ r₀`. -/
def init (A Astar : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := Astar (b - A x₀) }

/-- The `k`-th CGNE state for `A x = b` started at `x₀`. -/
noncomputable def iterate (A Astar : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A Astar)^[k] (init A Astar b x₀)

variable (A Astar : E →ₗ[𝕜] E) (b x₀ : E)

/-- The recurrence: state `k + 1` is one `CGNE.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A Astar b x₀ (k + 1) = step A Astar (iterate A Astar b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem step_x (s : State E) : (step A Astar s).x = s.x + (alpha s : 𝕜) • s.p := rfl

theorem step_r (s : State E) : (step A Astar s).r = s.r - (alpha s : 𝕜) • A s.p := rfl

theorem step_p (s : State E) :
    (step A Astar s).p = Astar (step A Astar s).r + beta A Astar s • s.p := rfl

/-- CGNE is CG on `A Aᴴ u = b` read through `x = Aᴴ u`: for any `u₀` with `Aᴴ u₀ = x₀`, the CGNE
iterate is `Aᴴ` of the CG iterate, the CGNE direction is `Aᴴ` of the CG direction, and the two
residuals agree.  This is Saad, *Iterative Methods*, Algorithm 8.5 (Craig's method). -/
theorem iterate_eq (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) {u₀ : E}
    (hu₀ : Astar u₀ = x₀) (k : ℕ) :
    (iterate A Astar b x₀ k).x = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).x ∧
      (iterate A Astar b x₀ k).r = (CG.iterate (A ∘ₗ Astar) b u₀ k).r ∧
      (iterate A Astar b x₀ k).p = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p := by
  have hinit : b - (A ∘ₗ Astar) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hu₀]
  induction k with
  | zero =>
    refine ⟨hu₀.symm, hinit.symm, ?_⟩
    change Astar (b - A x₀) = Astar (b - (A ∘ₗ Astar) u₀)
    rw [hinit]
  | succ k ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have hq : inner 𝕜 ((A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k).p)
          (CG.iterate (A ∘ₗ Astar) b u₀ k).p
        = inner 𝕜 (Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p)
          (Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p) := by
      rw [LinearMap.comp_apply, ← inner_conj_symm, inner_adjoint_right hadj, inner_conj_symm]
    have halpha : (alpha (iterate A Astar b x₀ k) : 𝕜)
        = CG.alpha (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k) := by
      rw [alpha, CG.alpha, hq, hr, hp]
    have hAp : A (iterate A Astar b x₀ k).p
        = (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k).p := by
      rw [hp, LinearMap.comp_apply]
    have hr' : (iterate A Astar b x₀ (k + 1)).r = (CG.iterate (A ∘ₗ Astar) b u₀ (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, hr, hAp, halpha]
    have hbeta : beta A Astar (iterate A Astar b x₀ k)
        = CG.beta (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, hr', hr]
    refine ⟨?_, hr', ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, hx, hp, halpha, map_add, map_smul]
    · rw [iterate_succ, step_p, ← iterate_succ, hr', hbeta, hp, CG.iterate_succ_p, map_add,
        map_smul]

/-- Craig's method computes `Aᴴ` of the CG iterates of `A Aᴴ u = b`. -/
theorem iterate_x_eq (hadj : ∀ u v : E, inner 𝕜 (Astar u) v = inner 𝕜 u (A v)) {u₀ : E}
    (hu₀ : Astar u₀ = x₀) (k : ℕ) :
    (iterate A Astar b x₀ k).x = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).x :=
  (iterate_eq A Astar b x₀ hadj hu₀ k).1

end CGNE

end Krylov
