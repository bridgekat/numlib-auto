import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.QuasiMinRes

/-!
# Preconditioned Krylov methods

Preconditioning is a change of inner product, not a new algorithm. For a symmetric coercive
preconditioner `M` with a linear inverse `M⁻¹` (`Krylov.IsPreconditioner`), the space `E` carries
the `M`-inner product `⟪M x, y⟫` — Mathlib-style, the type synonym `WithEnergy M` of
`Numlib/Analysis/InnerProductSpace/Energy` — and in it the preconditioned operator `M⁻¹ A` is
symmetric whenever `A` is, with quadratic form `⟪A x, x⟫`. Everything the unpreconditioned theory
proves therefore transports.

## Main definitions

* `Krylov.IsPreconditioner M Minv`: a symmetric coercive `M` together with a linear inverse;
* `Krylov.IsPreconditioner.EnergySpace`, `toEnergy`, `energySubmodule`, `energyEnd`: the `M`-inner
  product space and the transport of vectors, subspaces and operators into it;
* `Krylov.PCG.State`, `alpha`, `beta`, `step`, `init`, `iterate`: the preconditioned conjugate
  gradient iteration ([saad2003iterative] Algorithm 9.1).

## Main statements

* `Krylov.IsPreconditioner.isGalerkin_energyEnd_iff` and
  `Krylov.IsPreconditioner.isMinRes_energyEnd_iff`: the Galerkin condition for `M⁻¹ A x = M⁻¹ b` in
  the `M`-inner product *is* the Galerkin condition for `A x = b` in the original one, and the
  minimal-residual condition there is minimality of `‖b - A x‖_{M⁻¹}`;
* `Krylov.PCG.iterate_eq_CG_iterate_withEnergy`: the preconditioned conjugate gradient iteration is
  `CG.iterate` for `M⁻¹ A` in that space — this is the one-line statement "PCG is CG on the
  preconditioned system";
* `Krylov.PCG.isGalerkinIterate` and `Krylov.PCG.energyNorm_error_le`: consequently the PCG iterate
  minimizes the `A`-norm of the error over `x₀ + 𝒦_k(M⁻¹ A, M⁻¹ r₀)` and obeys the Chebyshev bound
  with the condition number of the *generalized* eigenvalue problem `A x = λ M x`, which is the
  condition number of `M⁻¹ A`;
* `Krylov.exists_aeval_of_isMinResIterate_preconditioned` and
  `Krylov.isMinRes_of_isMinResIterate_rightPreconditioned` ([saad2003iterative], Proposition 9.1):
  left and right preconditioning search the *same* affine space `x₀ + 𝒦_m(M⁻¹ A, M⁻¹ r₀)`, and
  differ only in the norm they minimize over it — `‖M⁻¹ (b - A x)‖` on the left, `‖b - A x‖` on the
  right;
* `Krylov.FGMRES.isMinRes` and `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero`: [saad2003iterative]
  Propositions 9.2 and 9.3 for flexible GMRES, whose search space is not a Krylov subspace at all,
  with `Krylov.FGMRES.apply_eq_of_coeff_eq_zero` the half of the latter that needs no orthonormal
  residual basis and so survives the breakdown step itself.

## Implementation notes

The inverse is carried as data rather than deduced from surjectivity of `M`: that is what a
preconditioner is in practice (a routine that solves `M z = r`), and it keeps the module free of
completeness and finite-dimensionality hypotheses.
-/

open Polynomial Krylov

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-- A preconditioner: a symmetric coercive `M` together with a linear right inverse `Minv`, which is
then a two-sided inverse (`Krylov.IsPreconditioner.inv_apply`) and itself symmetric
(`Krylov.IsPreconditioner.isSymmetric_inv`). -/
structure IsPreconditioner (M Minv : E →ₗ[𝕜] E) : Prop where
  /-- The preconditioner is symmetric coercive, so `⟪M x, y⟫` is an inner product. -/
  isSymmetricCoercive : M.IsSymmetricCoercive
  /-- `Minv` inverts `M`. -/
  apply_inv : ∀ x, M (Minv x) = x

namespace IsPreconditioner

variable {M Minv : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv)
include hM

/-- A right inverse of a coercive operator is a left inverse. -/
theorem inv_apply (x : E) : Minv (M x) = x :=
  hM.isSymmetricCoercive.isCoercive.injective (by rw [hM.apply_inv])

/-- The inverse of a symmetric operator is symmetric. -/
theorem isSymmetric_inv : Minv.IsSymmetric := fun x y => by
  conv_lhs => rw [← hM.apply_inv y]
  rw [← hM.isSymmetricCoercive.isSymmetric, hM.apply_inv]

/-- The `M`-inner product space: `E` with `⟪x, y⟫_M = ⟪M x, y⟫`, the space in which the
preconditioned operator `M⁻¹ A` is symmetric. -/
noncomputable abbrev EnergySpace : Type _ := WithEnergy M hM.isSymmetricCoercive

/-- The identity map from `E` to the `M`-inner product space. -/
noncomputable abbrev toEnergy : E ≃ₗ[𝕜] hM.EnergySpace :=
  WithEnergy.equiv M hM.isSymmetricCoercive

/-- A submodule of `E` seen in the `M`-inner product space. -/
noncomputable abbrev energySubmodule (K : Submodule 𝕜 E) : Submodule 𝕜 hM.EnergySpace :=
  WithEnergy.submoduleMap M hM.isSymmetricCoercive K

/-- An endomorphism of `E` seen as an endomorphism of the `M`-inner product space. -/
noncomputable def energyEnd (B : E →ₗ[𝕜] E) : hM.EnergySpace →ₗ[𝕜] hM.EnergySpace :=
  (hM.toEnergy).toLinearMap ∘ₗ B ∘ₗ (hM.toEnergy).symm.toLinearMap

/-- The transported operator acts on a transported vector as the original one does. -/
@[simp]
theorem energyEnd_apply (B : E →ₗ[𝕜] E) (x : E) :
    hM.energyEnd B (hM.toEnergy x) = hM.toEnergy (B x) := rfl

/-- `‖x‖²` in the `M`-inner product is the quadratic form of `M`. -/
theorem norm_toEnergy_sq (x : E) : ‖hM.toEnergy x‖ ^ 2 = RCLike.re (inner 𝕜 (M x) x) := by
  rw [WithEnergy.norm_equiv, hM.isSymmetricCoercive.energyNorm_sq]

/-- The `M`-inner product of `w` with a preconditioned vector is the original inner product: `⟪w,
M⁻¹ u⟫_M = ⟪w, u⟫`.  This is the identity that makes preconditioning a change of inner product and
nothing more. -/
theorem inner_toEnergy_inv (w u : E) :
    inner 𝕜 (hM.toEnergy w) (hM.toEnergy (Minv u)) = inner 𝕜 w u := by
  rw [WithEnergy.inner_equiv, energyInner, ← hM.isSymmetric_inv, hM.inv_apply]

variable (A : E →ₗ[𝕜] E)

/-- The quadratic form of `M⁻¹ A` in the `M`-inner product is the quadratic form of `A`. -/
theorem inner_energyEnd_left (x y : E) :
    inner 𝕜 (hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x)) (hM.toEnergy y) = inner 𝕜 (A x) y := by
  rw [energyEnd_apply, WithEnergy.inner_equiv, energyInner, LinearMap.comp_apply, hM.apply_inv]

/-- The other side of `Krylov.IsPreconditioner.inner_energyEnd_left`. -/
theorem inner_energyEnd_right (x y : E) :
    inner 𝕜 (hM.toEnergy x) (hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy y)) = inner 𝕜 x (A y) := by
  rw [energyEnd_apply, WithEnergy.inner_equiv, energyInner, LinearMap.comp_apply,
    ← hM.isSymmetric_inv, hM.inv_apply]

/-- The energy norm of `M⁻¹ A` in the `M`-inner product is the energy norm of `A` in the original
one.  So the Chebyshev bounds proved for `M⁻¹ A` there are bounds on `‖x* - x_k‖_A`. -/
theorem energyNorm_energyEnd (x : E) :
    energyNorm (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy x) = energyNorm A x := by
  rw [energyNorm, energyNorm, hM.inner_energyEnd_left A x x]

/-- Powers of the transported operator are the transports of the powers. -/
theorem pow_energyEnd (B : E →ₗ[𝕜] E) (i : ℕ) (x : E) :
    ((hM.energyEnd B) ^ i) (hM.toEnergy x) = hM.toEnergy ((B ^ i) x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, energyEnd_apply,
      ← Module.End.mul_apply, ← pow_succ']

/-- The Krylov subspaces of the transported operator are the transported Krylov subspaces:
preconditioning does not move the search space, only the geometry on it. -/
theorem subspace_energyEnd (B : E →ₗ[𝕜] E) (v : E) (m : ℕ) :
    subspace (hM.energyEnd B) (hM.toEnergy v) m = hM.energySubmodule (subspace B v m) := by
  have hsub : hM.energySubmodule (subspace B v m)
      = (subspace B v m).map (hM.toEnergy).toLinearMap := rfl
  rw [hsub, subspace, subspace, Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(B ^ (i : ℕ)) v, ⟨i, rfl⟩, (hM.pow_energyEnd B i v).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, hM.pow_energyEnd B i v⟩

/-- **The Galerkin condition is preconditioning-invariant.**  A Galerkin iterate for the
preconditioned system `M⁻¹ A x = M⁻¹ b` in the `M`-inner product is a Galerkin iterate for `A x = b`
in the original inner product, over the same subspace, and conversely.  This is what makes every
optimality statement of `Numlib/Krylov/Iterate` available to a preconditioned method with no new
proof. -/
theorem isGalerkin_energyEnd_iff (b x₀ : E) (K : Submodule 𝕜 E) (x : E) :
    IsGalerkin (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
        (hM.energySubmodule K) (hM.toEnergy x) ↔ IsGalerkin A b x₀ K x := by
  have hres : hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x) =
      hM.toEnergy (Minv (b - A x)) := by
    rw [energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  constructor
  · rintro ⟨hmem, horth⟩
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth (hM.toEnergy w)
      ((WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hw)
    rwa [hres, hM.inner_toEnergy_inv] at h
  · rintro ⟨hmem, horth⟩
    refine ⟨by
        rw [← map_sub]
        exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hmem,
      (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [show (hM.toEnergy).toLinearMap v = hM.toEnergy v from rfl, hres, hM.inner_toEnergy_inv]
    exact (Submodule.mem_orthogonal _ _).1 horth v hv

/-- The `M`-norm of a preconditioned vector is the `M⁻¹`-norm of the vector: `‖M⁻¹ u‖_M² = re ⟪u,
M⁻¹ u⟫`.  So the residual norm that a left-preconditioned minimal-residual method minimizes is `‖b -
A x‖_{M⁻¹}`. -/
theorem norm_toEnergy_inv_sq (u : E) :
    ‖hM.toEnergy (Minv u)‖ ^ 2 = RCLike.re (inner 𝕜 u (Minv u)) := by
  rw [hM.norm_toEnergy_sq, hM.apply_inv]

/-- **The minimal-residual condition is preconditioning-invariant too.**  Minimizing the residual of
the preconditioned system `M⁻¹ A x = M⁻¹ b` in the `M`-inner product is minimizing the `M⁻¹`-norm of
the true residual `b - A x`, which is what left-preconditioned GMRES and MINRES do
([saad2003iterative], §9.3.1). -/
theorem isMinRes_energyEnd_iff (b x₀ : E) (K : Submodule 𝕜 E) (x : E) :
    IsMinRes (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
        (hM.energySubmodule K) (hM.toEnergy x) ↔
      (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K →
        energyNorm M (Minv (b - A x)) ≤ energyNorm M (Minv (b - A y))) := by
  have hres : ∀ y : E, hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy y)
      = hM.toEnergy (Minv (b - A y)) := fun y => by
    rw [energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  have hnorm : ∀ y : E, ‖hM.toEnergy (Minv (b - A y))‖ = energyNorm M (Minv (b - A y)) :=
    fun y => WithEnergy.norm_equiv M hM.isSymmetricCoercive _
  constructor
  · rintro ⟨hmem, hmin⟩
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hmem
    refine ⟨hmem, fun y hy => ?_⟩
    have h := hmin (hM.toEnergy y) (by
      rw [← map_sub]
      exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hy)
    rwa [hres, hres, hnorm, hnorm] at h
  · rintro ⟨hmem, hmin⟩
    refine ⟨by
        rw [← map_sub]
        exact (WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive).2 hmem,
      fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective z
    rw [← map_sub, WithEnergy.equiv_mem_submoduleMap_iff M hM.isSymmetricCoercive] at hz
    rw [hres, hres, hnorm, hnorm]
    exact hmin y hz

/-- Generalized eigenvalue bounds `λmin ⟪M x, x⟫ ≤ ⟪A x, x⟫ ≤ λmax ⟪M x, x⟫` are exactly the
quadratic form bounds of `M⁻¹ A` in the `M`-inner product, which is the shape in which the Chebyshev
convergence theory consumes them.  `λmax / λmin` is the condition number of `M⁻¹ A`, the quantity
preconditioning exists to reduce. -/
theorem isSymmetricBoundedBy_energyEnd (hA : A.IsSymmetric) {lmin lmax : ℝ}
    (hmin : ∀ x : E, lmin * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    (hmax : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * RCLike.re (inner 𝕜 (M x) x)) :
    (hM.energyEnd (Minv ∘ₗ A)).IsSymmetricBoundedBy lmin lmax where
  isSymmetric := by
    intro u v
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective v
    rw [hM.inner_energyEnd_left A, hM.inner_energyEnd_right A, hA]
  le_re_inner := by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hmin x
  re_inner_le := by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hmax x

/-- The preconditioned operator is symmetric coercive in the `M`-inner product as soon as `A` is
symmetric and bounded below relative to `M`, which is what makes PCG well defined. -/
theorem isSymmetricCoercive_energyEnd (hA : A.IsSymmetric) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x)) :
    (hM.energyEnd (Minv ∘ₗ A)).IsSymmetricCoercive where
  isSymmetric := by
    intro u v
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    obtain ⟨y, rfl⟩ := (hM.toEnergy).surjective v
    rw [hM.inner_energyEnd_left A, hM.inner_energyEnd_right A, hA]
  isCoercive := ⟨c, hc, by
    intro u
    obtain ⟨x, rfl⟩ := (hM.toEnergy).surjective u
    rw [hM.inner_energyEnd_left A, hM.norm_toEnergy_sq]
    exact hcoer x⟩

end IsPreconditioner

/-! ### Left and right preconditioning search the same space ([saad2003iterative], Proposition 9.1)
-/

variable {M Minv A : E →ₗ[𝕜] E}

/-- [saad2003iterative], Proposition 9.1 (left preconditioning): the left-preconditioned
minimal-residual iterate — the one minimizing `‖M⁻¹ (b - A x)‖` — has the form `x = x₀ + s(M⁻¹ A)
M⁻¹ r₀` with `deg s < m`. -/
theorem exists_aeval_of_isMinResIterate_preconditioned
    {b x₀ : E} {m : ℕ} {x : E} (hx : IsMinResIterate (Minv ∘ₗ A) (Minv b) x₀ m x) :
    ∃ s : 𝕜[X], s.degree < m ∧ x = x₀ + aeval (Minv ∘ₗ A) s (Minv (b - A x₀)) := by
  have hr : Minv b - (Minv ∘ₗ A) x₀ = Minv (b - A x₀) := by
    rw [LinearMap.comp_apply, ← map_sub]
  have hmem := hx.mem
  rw [hr] at hmem
  obtain ⟨s, hs, hsx⟩ := (mem_subspace_iff_exists_aeval _ _).1 hmem
  exact ⟨s, hs, by rw [hsx]; abel⟩

/-- [saad2003iterative], Proposition 9.1 (right preconditioning): the right-preconditioned iterate
for `A M⁻¹ u = b`, mapped back by `x = M⁻¹ u`, lies in the *same* affine space `x₀ + 𝒦_m(M⁻¹ A, M⁻¹
r₀)` as the left-preconditioned one, and there it minimizes the true residual `‖b - A x‖` rather
than the preconditioned one. -/
theorem isMinRes_of_isMinResIterate_rightPreconditioned {b x₀ : E} {m : ℕ} {u₀ u : E}
    (hx₀ : x₀ = Minv u₀) (hu : IsMinResIterate (A ∘ₗ Minv) b u₀ m u) :
    IsMinRes A b x₀ (subspace (Minv ∘ₗ A) (Minv (b - A x₀)) m) (Minv u) := by
  have hr : b - (A ∘ₗ Minv) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hx₀]
  have hmap := map_subspace_comp A Minv (b - A x₀) m
  have hmem := hu.mem
  rw [hr] at hmem
  refine ⟨?_, fun y hy => ?_⟩
  · have hsub : Minv u - x₀ = Minv (u - u₀) := by rw [hx₀, map_sub]
    rw [hsub, ← hmap]
    exact Submodule.mem_map_of_mem hmem
  · rw [← hmap] at hy
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hy
    have hyu : y = Minv (u₀ + w) := by rw [map_add, ← hx₀, hwy]; abel
    have h := hu.min (u₀ + w) (by rw [hr, add_sub_cancel_left]; exact hw)
    rwa [hyu, ← LinearMap.comp_apply, ← LinearMap.comp_apply (f := A)]

/-! ### The preconditioned conjugate gradient iteration ([saad2003iterative], Algorithm 9.1) -/

namespace PCG

/-- State of the preconditioned CG iteration: iterate, residual `r = b - A x`, and search direction.
The preconditioned residual `z = M⁻¹ r` is recomputed rather than stored. -/
structure State (E : Type*) where
  /-- The current iterate. -/
  x : E
  /-- The residual `b - A x`. -/
  r : E
  /-- The search direction. -/
  p : E

/-- The PCG step length `α = ⟪r, M⁻¹ r⟫ / ⟪A p, p⟫`. -/
noncomputable def alpha (A Minv : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 s.r (Minv s.r) / inner 𝕜 (A s.p) s.p

/-- One PCG step ([saad2003iterative], Algorithm 9.1). -/
noncomputable def step (A Minv : E →ₗ[𝕜] E) (s : State E) : State E :=
  let α := alpha A Minv s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 r' (Minv r') / inner 𝕜 s.r (Minv s.r)
  { x := s.x + α • s.p, r := r', p := Minv r' + β • s.p }

/-- The PCG direction update coefficient `β = ⟪r', M⁻¹ r'⟫ / ⟪r, M⁻¹ r⟫`. -/
noncomputable def beta (A Minv : E →ₗ[𝕜] E) (s : State E) : 𝕜 :=
  inner 𝕜 (step A Minv s).r (Minv (step A Minv s).r) / inner 𝕜 s.r (Minv s.r)

/-- The starting state: `r₀ = b - A x₀` and `p₀ = M⁻¹ r₀`. -/
def init (A Minv : E →ₗ[𝕜] E) (b x₀ : E) : State E :=
  { x := x₀, r := b - A x₀, p := Minv (b - A x₀) }

/-- The `k`-th PCG state for `A x = b` started at `x₀` with preconditioner `M`. -/
noncomputable def iterate (A Minv : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E :=
  (step A Minv)^[k] (init A Minv b x₀)

variable (A Minv : E →ₗ[𝕜] E) (b x₀ : E)

/-- The recurrence: state `k + 1` is one `PCG.step` applied to state `k`. -/
theorem iterate_succ (k : ℕ) :
    iterate A Minv b x₀ (k + 1) = step A Minv (iterate A Minv b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update `x' = x + α p` of one PCG step. -/
theorem step_x (s : State E) : (step A Minv s).x = s.x + alpha A Minv s • s.p := rfl

/-- The residual update `r' = r - α A p` of one PCG step. -/
theorem step_r (s : State E) : (step A Minv s).r = s.r - alpha A Minv s • A s.p := rfl

/-- The direction update `p' = M⁻¹ r' + β p` of one PCG step. -/
theorem step_p (s : State E) :
    (step A Minv s).p = Minv (step A Minv s).r + beta A Minv s • s.p := rfl

/-- **PCG is CG on the preconditioned system.**  Transported to the `M`-inner product space, the PCG
iterate and search direction are those of `CG.iterate` for `M⁻¹ A` with right-hand side `M⁻¹ b`, and
the CG residual is `M⁻¹` of the PCG residual, which is the true residual `b - A x`. This is
[saad2003iterative], §9.2.1: everything proved of `CG.iterate` holds of PCG. -/
theorem iterate_eq_CG_iterate_withEnergy {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    hM.toEnergy (iterate A Minv b x₀ k).x
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x ∧
      hM.toEnergy (Minv (iterate A Minv b x₀ k).r)
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).r ∧
      hM.toEnergy (iterate A Minv b x₀ k).p
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).p ∧
      (iterate A Minv b x₀ k).r = b - A (iterate A Minv b x₀ k).x := by
  have hinit : hM.toEnergy (Minv (b - A x₀))
      = hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀) := by
    rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  induction k with
  | zero => exact ⟨rfl, hinit, hinit, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hres⟩ := ih
    have hnum : inner 𝕜 (hM.toEnergy (Minv (iterate A Minv b x₀ k).r))
          (hM.toEnergy (Minv (iterate A Minv b x₀ k).r))
        = inner 𝕜 (iterate A Minv b x₀ k).r (Minv (iterate A Minv b x₀ k).r) := by
      rw [WithEnergy.inner_equiv, energyInner, hM.apply_inv]
    have halpha : alpha A Minv (iterate A Minv b x₀ k)
        = CG.alpha (hM.energyEnd (Minv ∘ₗ A))
          (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k) := by
      rw [alpha, CG.alpha, ← hr, ← hp, hnum, hM.inner_energyEnd_left A]
    have hr' : hM.toEnergy (Minv (iterate A Minv b x₀ (k + 1)).r)
        = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b))
            (hM.toEnergy x₀) (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, map_sub, map_sub, map_smul, map_smul, hr,
        ← hp, halpha, IsPreconditioner.energyEnd_apply, LinearMap.comp_apply]
    have hbeta : beta A Minv (iterate A Minv b x₀ k)
        = CG.beta (hM.energyEnd (Minv ∘ₗ A))
          (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, ← hr', ← hr, hnum]
      congr 1
      rw [WithEnergy.inner_equiv, energyInner, hM.apply_inv]
    refine ⟨?_, hr', ?_, ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, map_add, map_smul, hx, hp, halpha]
    · rw [iterate_succ, step_p, ← iterate_succ, CG.iterate_succ_p, map_add, map_smul, hr', hp,
        hbeta]
    · rw [iterate_succ, step_r, step_x, hres, map_add, map_smul, sub_sub]

/-- The PCG iterate is the CG iterate of the preconditioned system, in one line. -/
theorem toEnergy_iterate_x {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    hM.toEnergy (iterate A Minv b x₀ k).x
      = (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x :=
  (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM k).1

/-- The PCG state's residual field is the true residual `b - A x`. -/
theorem residual_eq {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (k : ℕ) :
    (iterate A Minv b x₀ k).r = b - A (iterate A Minv b x₀ k).x :=
  (iterate_eq_CG_iterate_withEnergy A Minv b x₀ hM k).2.2.2

variable {A Minv b x₀}

/-- The PCG iterate is the Galerkin iterate of `A x = b` over the *preconditioned* Krylov space `x₀
+ 𝒦_k(M⁻¹ A, M⁻¹ r₀)`, in the original inner product.  In particular it minimizes the `A`-norm of
the error there (`Krylov.IsGalerkin.energyNorm_le`). -/
theorem isGalerkinIterate {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (hA : A.IsSymmetric)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : E, c * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x)) (k : ℕ) :
    IsGalerkin A b x₀ (subspace (Minv ∘ₗ A) (Minv (b - A x₀)) k)
      (iterate A Minv b x₀ k).x := by
  have hgal : IsGalerkin (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
      (subspace (hM.energyEnd (Minv ∘ₗ A))
        (hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀)) k)
      (CG.iterate (hM.energyEnd (Minv ∘ₗ A)) (hM.toEnergy (Minv b)) (hM.toEnergy x₀) k).x :=
    CG.isGalerkinIterate (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
      (hM.isSymmetricCoercive_energyEnd A hA hc hcoer) k
  rw [show hM.toEnergy (Minv b) - hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy x₀)
        = hM.toEnergy (Minv (b - A x₀)) by
      rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub],
    hM.subspace_energyEnd, ← toEnergy_iterate_x A Minv b x₀ hM k] at hgal
  exact (hM.isGalerkin_energyEnd_iff A b x₀ _ _).1 hgal

/-- The Chebyshev bound for PCG ([saad2003iterative], §9.2): with the generalized eigenvalues of `A
x = λ M x` in `[λmin, λmax]` and `κ = λmax / λmin`, `‖x* - x_k‖_A ≤ 2 ((√κ - 1)/(√κ + 1))^k ‖x* -
x₀‖_A`.  The bound is the unpreconditioned one transported: the energy norm of `M⁻¹ A` in the
`M`-inner product is the `A`-norm, so preconditioning changes only which condition number appears.
-/
theorem energyNorm_error_le {M : E →ₗ[𝕜] E} (hM : IsPreconditioner M Minv) (hA : A.IsSymmetric)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax)
    (hmin : ∀ x : E, lmin * RCLike.re (inner 𝕜 (M x) x) ≤ RCLike.re (inner 𝕜 (A x) x))
    (hmax : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * RCLike.re (inner 𝕜 (M x) x))
    {xstar : E} (hstar : A xstar = b) (k : ℕ) :
    energyNorm A (xstar - (iterate A Minv b x₀ k).x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ k *
        energyNorm A (xstar - x₀) := by
  have hB := hM.isSymmetricBoundedBy_energyEnd A hA hmin hmax
  have hgal := CG.isGalerkinIterate (hM.toEnergy (Minv b)) (hM.toEnergy x₀)
    (hB.isSymmetricCoercive hl) k
  have hstar' : hM.energyEnd (Minv ∘ₗ A) (hM.toEnergy xstar) = hM.toEnergy (Minv b) := by
    rw [IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, hstar]
  have h := IsGalerkinIterate.energyNorm_error_le hl hll hB hgal hstar'
  rw [← toEnergy_iterate_x A Minv b x₀ hM k, ← map_sub, ← map_sub,
    hM.energyNorm_energyEnd, hM.energyNorm_energyEnd] at h
  exact h

end PCG

/-! ### Flexible GMRES -/

namespace FGMRES

/-- **[saad2003iterative], Proposition 9.2**: the flexible GMRES iterate minimizes the residual norm
over `x₀ + span {z_0, …, z_{m-1}}`.

FGMRES expands the *iterate* in arbitrary preconditioned directions `z_j = M_j⁻¹ v_j` while
expanding the *residual* in the orthonormal Arnoldi basis `v_i`, so its search space is not a Krylov
subspace; what makes the minimization work is only the two-family relation `A Z_m = V_{m+1} H̄_m` of
[saad2003iterative] (9.22) together with orthonormality of `V_{m+1}`. This is
`Krylov.IsQuasiMinResIterate.isMinOn_norm_residual` with the minimizer given explicitly. -/
theorem isMinRes {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E} {β : 𝕜}
    (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hon : Orthonormal 𝕜 fun i : Fin (m + 1) => v (i : ℕ)) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    IsMinRes A b x₀ (Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ)))
      (x₀ + ∑ j, y j • z j) :=
  IsQuasiMinResIterate.isMinOn_norm_residual hv hr hon ⟨y, hy, rfl⟩

/-- The last row of the rectangular Hessenberg matrix carries only its subdiagonal entry. -/
private theorem mulVec_hessenbergOf_last {h : ℕ → ℕ → 𝕜} (hH : ∀ i k, k + 1 < i → h i k = 0)
    {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜) :
    (hessenbergOf h m).mulVec y ⟨m, Nat.lt_succ_self m⟩
      = h m (m - 1) * y ⟨m - 1, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, hessenbergOf, Matrix.of_apply]
  refine Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin m) (fun k _ hk => ?_)
    (fun hc => absurd (Finset.mem_univ _) hc)
  have hklt := k.isLt
  have hk' : (k : ℕ) ≠ m - 1 := fun hcc => hk (Fin.ext hcc)
  rw [hH m (k : ℕ) (by omega), zero_mul]

/-- **Back substitution in a Hessenberg system**: if the subdiagonal entries `h_{i+1,i}` do not
vanish and `H_m y = β e₁` with `β ≠ 0`, then the last coordinate of `y` is nonzero.

Were it zero, the last equation would force the one before it to vanish, and so on down to `y_0 =
0`; the first equation would then read `0 = β`. -/
private theorem last_ne_zero_of_mulVec_eq {h : ℕ → ℕ → 𝕜} {β : 𝕜} (hβ : β ≠ 0) {m : ℕ}
    (hm : 0 < m) (hH : ∀ i k, k + 1 < i → h i k = 0)
    (hsub : ∀ i, i + 1 < m → h (i + 1) i ≠ 0) {y : Fin m → 𝕜}
    (hyeq : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    y ⟨m - 1, by omega⟩ ≠ 0 := by
  intro hlast
  have hrow : ∀ (r : ℕ) (hr : r < m),
      ∑ k : Fin m, h r (k : ℕ) * y k = firstVec β m ⟨r, hr⟩ := by
    intro r hr
    have hcong := congrFun hyeq ⟨r, hr⟩
    simpa only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply] using hcong
  have hall : ∀ t : ℕ, ∀ i : Fin m, m - 1 - t ≤ (i : ℕ) → y i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have hilt := i.isLt
      have hval : (i : ℕ) = m - 1 := by omega
      have : i = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hval
      rw [this]
      exact hlast
    | succ t ih =>
      intro i hi
      by_cases hcase : m - 1 - t ≤ (i : ℕ)
      · exact ih i hcase
      have hilt := i.isLt
      have hij : (i : ℕ) + 1 < m := by omega
      have hz := hrow ((i : ℕ) + 1) hij
      have hfv : firstVec β m ⟨(i : ℕ) + 1, hij⟩ = 0 := by simp [firstVec]
      rw [hfv] at hz
      have hsum : ∑ k : Fin m, h ((i : ℕ) + 1) (k : ℕ) * y k
          = h ((i : ℕ) + 1) (i : ℕ) * y i := by
        refine Finset.sum_eq_single i (fun k _ hk => ?_)
          (fun hc => absurd (Finset.mem_univ _) hc)
        have hkne : (k : ℕ) ≠ (i : ℕ) := fun hcc => hk (Fin.ext hcc)
        rcases lt_or_gt_of_ne hkne with hlt | hgt
        · rw [hH ((i : ℕ) + 1) (k : ℕ) (by omega), zero_mul]
        · rw [ih k (by omega), mul_zero]
      rw [hsum] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hsub (i : ℕ) hij)
  have hy0 : ∀ i : Fin m, y i = 0 := fun i => hall (m - 1) i (by omega)
  have h0 := hrow 0 hm
  rw [show firstVec β m ⟨0, hm⟩ = β from by simp [firstVec]] at h0
  rw [Finset.sum_congr rfl fun k _ => by rw [hy0 k, mul_zero]] at h0
  exact hβ (by simpa using h0.symm)

/-- A row of `H̄_m` above the last one is the corresponding row of the square `H_m`. -/
private theorem mulVec_hessenbergOf_of_lt {h : ℕ → ℕ → 𝕜} {j : ℕ} (w : Fin j → 𝕜) (r : ℕ)
    (hr : r < j) :
    (hessenbergOf h j).mulVec w ⟨r, by omega⟩ = (hessenbergSqOf h j).mulVec w ⟨r, hr⟩ := by
  simp only [Matrix.mulVec, dotProduct, hessenbergOf, hessenbergSqOf, Matrix.of_apply]

/-- `β e₁` of length `j + 1` agrees with `β e₁` of length `j` below the last entry. -/
private theorem firstVec_succ_of_lt {β : 𝕜} {j : ℕ} (r : ℕ) (hr : r < j) :
    firstVec β (j + 1) ⟨r, by omega⟩ = firstVec β j ⟨r, hr⟩ := by
  simp [firstVec]

/-- The quasi-residual vanishes exactly when its coefficient vector does. -/
private theorem quasiResidual_eq_zero_iff (h : ℕ → ℕ → 𝕜) (β : 𝕜) (j : ℕ) :
    ∀ w : Fin j → 𝕜, quasiResidual h β j w = 0 ↔
      ∀ i : Fin (j + 1), (firstVec β (j + 1) - (hessenbergOf h j).mulVec w) i = 0 := by
  intro w
  rw [quasiResidual_def, norm_eq_zero]
  constructor
  · intro hw i
    have := congrArg (WithLp.ofLp (p := 2)) hw
    simpa using congrFun this i
  · intro hw
    have : (firstVec β (j + 1) - (hessenbergOf h j).mulVec w) = 0 := funext hw
    rw [this]
    simp

/-- **A vanishing subdiagonal entry makes the flexible GMRES iterate exact**, with no
orthonormality hypothesis on the residual basis: if `h_{m,m-1} = 0` and the square Hessenberg
matrix `H_m` is nonsingular, then any minimizer of the quasi-residual gives `A (x₀ + Z_m y) = b`.

This is the half of `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero` that survives a breakdown at step
`m - 1`, where the residual basis stops one vector short and `v_0, …, v_m` cannot be orthonormal.
It is what [saad2003iterative] §9.4.1 needs: an *exact* inner solve `A z_j = v_j` empties the
orthogonalization, and the outer iteration is finished. -/
theorem apply_eq_of_coeff_eq_zero {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E}
    {β : 𝕜} (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) {m : ℕ} (hm : 0 < m)
    (hH : IsUnit (hessenbergSqOf h m).det) (hzero : h m (m - 1) = 0) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    A (x₀ + ∑ i, y i • z i) = b := by
  set y' : Fin m → 𝕜 := (hessenbergSqOf h m)⁻¹.mulVec (firstVec β m) with hy'
  have hy'eq : (hessenbergSqOf h m).mulVec y' = firstVec β m := by
    rw [hy', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  have hq' : quasiResidual h β m y' = 0 := by
    refine (quasiResidual_eq_zero_iff h β m y').2 fun i => ?_
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
    · have hi : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.ext heq
      rw [hi, Pi.sub_apply, mulVec_hessenbergOf_last hv.eq_zero_of_lt hm y', hzero, zero_mul,
        show firstVec β (m + 1) ⟨m, Nat.lt_succ_self m⟩ = 0 from by simp [firstVec]; omega,
        sub_zero]
    · rw [Pi.sub_apply, mulVec_hessenbergOf_of_lt y' (i : ℕ) hlt, hy'eq,
        firstVec_succ_of_lt (i : ℕ) hlt, sub_self]
  have hq : quasiResidual h β m y = 0 :=
    le_antisymm (hq' ▸ isMinOn_iff.1 hy y' (Set.mem_univ y')) (quasiResidual_nonneg h β m y)
  have hc0 := (quasiResidual_eq_zero_iff h β m y).1 hq
  have h0 : b - A (x₀ + ∑ i, y i • z i) = 0 := by
    rw [hv.residual_eq hr m y]
    exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
  exact (sub_eq_zero.1 h0).symm

/-- **[saad2003iterative], Proposition 9.3**: if the residual is nonzero, the previous steps have
not broken down and the square Hessenberg matrix `H_j` is nonsingular, then the flexible GMRES
iterate at step `j` is exact exactly when the subdiagonal entry `h_{j+1,j}` vanishes.

The nonsingularity of `H_j` is a genuine extra hypothesis in the flexible case: unlike GMRES, where
`A Z_j = A V_j` and nonsingularity of `A` transfers, the `z_j` are arbitrary. The forward direction
is back substitution in `H_j y = β e₁`; the reverse builds the exact solution from `H_j⁻¹ (β e₁)`
and uses minimality. -/
theorem apply_eq_iff_coeff_eq_zero {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ : E}
    {β : 𝕜} (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0) (hβ : β ≠ 0)
    {j : ℕ} (hj : 0 < j) (hsub : ∀ i, i + 1 < j → h (i + 1) i ≠ 0)
    (hH : IsUnit (hessenbergSqOf h j).det)
    (hon : Orthonormal 𝕜 fun i : Fin (j + 1) => v (i : ℕ))
    {y : Fin j → 𝕜} (hy : IsMinOn (quasiResidual h β j) Set.univ y) :
    A (x₀ + ∑ i, y i • z i) = b ↔ h j (j - 1) = 0 := by
  classical
  -- the coefficients of the residual in the basis `v`
  have hrowj : ∀ (w : Fin j → 𝕜) (r : ℕ) (hr : r < j),
      (hessenbergOf h j).mulVec w ⟨r, by omega⟩ = (hessenbergSqOf h j).mulVec w ⟨r, hr⟩ :=
    fun w r hr => mulVec_hessenbergOf_of_lt w r hr
  have hfirst : ∀ (r : ℕ) (hr : r < j),
      firstVec β (j + 1) ⟨r, by omega⟩ = firstVec β j ⟨r, hr⟩ :=
    fun r hr => firstVec_succ_of_lt r hr
  -- `quasiResidual` vanishes exactly when the coefficient vector does
  have hqz := quasiResidual_eq_zero_iff h β j
  -- exactness is vanishing of the coefficient vector
  have hexact : A (x₀ + ∑ i, y i • z i) = b ↔ quasiResidual h β j y = 0 := by
    rw [hqz]
    constructor
    · intro hax
      have h0 : ∑ i : Fin (j + 1),
          (firstVec β (j + 1) - (hessenbergOf h j).mulVec y) i • v (i : ℕ) = 0 := by
        rw [← hv.residual_eq hr j y, hax, sub_self]
      exact fun i => Fintype.linearIndependent_iff.1 hon.linearIndependent _ h0 i
    · intro hc0
      have h0 : b - A (x₀ + ∑ i, y i • z i) = 0 := by
        rw [hv.residual_eq hr j y]
        exact Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
      exact (sub_eq_zero.1 h0).symm
  rw [hexact]
  constructor
  · intro hq
    have hc0 := (hqz y).1 hq
    have hlast := hc0 ⟨j, Nat.lt_succ_self j⟩
    rw [Pi.sub_apply, sub_eq_zero, mulVec_hessenbergOf_last hv.eq_zero_of_lt hj y,
      show firstVec β (j + 1) ⟨j, Nat.lt_succ_self j⟩ = 0 from by simp [firstVec]; omega] at hlast
    have hyeq : (hessenbergSqOf h j).mulVec y = firstVec β j := by
      funext r
      have := hc0 ⟨(r : ℕ), by omega⟩
      rw [Pi.sub_apply, sub_eq_zero, hfirst (r : ℕ) r.isLt, hrowj y (r : ℕ) r.isLt] at this
      exact this.symm
    exact (mul_eq_zero.1 hlast.symm).resolve_right
      (last_ne_zero_of_mulVec_eq hβ hj hv.eq_zero_of_lt hsub hyeq)
  · intro hzero
    set y' : Fin j → 𝕜 := (hessenbergSqOf h j)⁻¹.mulVec (firstVec β j) with hy'
    have hy'eq : (hessenbergSqOf h j).mulVec y' = firstVec β j := by
      rw [hy', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    have hq' : quasiResidual h β j y' = 0 := by
      refine (hqz y').2 fun i => ?_
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 i.isLt) with heq | hlt
      · have hi : i = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) := Fin.ext heq
        rw [hi, Pi.sub_apply, mulVec_hessenbergOf_last hv.eq_zero_of_lt hj y', hzero, zero_mul,
          show firstVec β (j + 1) ⟨j, Nat.lt_succ_self j⟩ = 0 from by simp [firstVec]; omega,
          sub_zero]
      · have hi : i = (⟨(i : ℕ), by omega⟩ : Fin (j + 1)) := Fin.ext rfl
        rw [Pi.sub_apply, hrowj y' (i : ℕ) hlt, hy'eq, hfirst (i : ℕ) hlt, sub_self]
    have hle := isMinOn_iff.1 hy y' (Set.mem_univ y')
    exact le_antisymm (hq' ▸ hle) (quasiResidual_nonneg h β j y)

end FGMRES

end Krylov
