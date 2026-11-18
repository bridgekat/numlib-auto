import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Abel

/-!
# Residual-correction cycles

A linear residual response $M$ for $Ax=b$ defines the update $x\mapsto x+M(b-Ax)$
and the error map $I-MA$. A damped coarse response is $\alpha PDR$, where $R$ is restriction,
$D$ the coarse solver, and $P$ prolongation. Neither symmetry nor definiteness is required.

## Main definitions

* `Multigrid.TransferPair`: restriction $R$ and prolongation $P$.
* `Multigrid.TransferPair.petrovGalerkinCoarse`: the coarse operator $RAP$.
* `Multigrid.twoGridStep`: pre-smoothing, coarse correction, and post-smoothing in order.
* `Multigrid.vCycleResponse`: the linear residual response of a recursive V-cycle.

## Main results

* `Multigrid.TransferPair.restricted_residual_eq_zero`: exact undamped coarse correction
  annihilates the restricted residual when the coarse operator is $RAP$.
* `Multigrid.twoGridStep_error`: the error map is the ordered product of the three error maps.
* `Multigrid.residualCorrection_vCycleResponse_succ`: at a non-base level the V-cycle uses
  the preceding level's V-cycle in its coarse solve.
-/

namespace Multigrid

variable {𝕜 E F : Type*} [CommRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A **transfer pair** consists of restriction $R$ from the fine space $E$ to the coarse
space $F$ and prolongation $P$ from $F$ to $E$, both linear over the scalar ring. -/
structure TransferPair (𝕜 E F : Type*) [CommRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] where
  /-- The linear fine-to-coarse restriction $R$. -/
  restrict : E →ₗ[𝕜] F
  /-- The linear coarse-to-fine prolongation $P$. -/
  prolong : F →ₗ[𝕜] E

namespace TransferPair

/-- For a fine operator $A$ and transfers $R$ and $P$, the **Petrov–Galerkin coarse operator**
is $RAP$. Restriction need not be the adjoint of prolongation. -/
def petrovGalerkinCoarse (transfer : TransferPair 𝕜 E F) (A : Module.End 𝕜 E) :
    Module.End 𝕜 F :=
  transfer.restrict ∘ₗ A ∘ₗ transfer.prolong

/-- The coarse operator applies prolongation, the fine operator, and restriction in order. -/
@[simp]
theorem petrovGalerkinCoarse_apply (transfer : TransferPair 𝕜 E F) (A : Module.End 𝕜 E)
    (coarse : F) :
    transfer.petrovGalerkinCoarse A coarse = transfer.restrict (A (transfer.prolong coarse)) :=
  rfl

/-- If $c$ solves $RAPc = R(b - Ax)$, the corrected iterate $x + Pc$ has restricted residual
zero. This holds even when $RAP$ is singular. -/
theorem restricted_residual_eq_zero (transfer : TransferPair 𝕜 E F) (A : Module.End 𝕜 E)
    (rhs iterate : E) (coarse : F)
    (hcoarse : transfer.petrovGalerkinCoarse A coarse = transfer.restrict (rhs - A iterate)) :
    transfer.restrict (rhs - A (iterate + transfer.prolong coarse)) = 0 := by
  rw [map_add, ← sub_sub, map_sub, ← petrovGalerkinCoarse_apply, hcoarse, sub_self]

/-- For a linear coarse solver $D$, the **coarse response** to a fine residual is $\alpha PDR$,
where $\alpha$ is the correction damping. The solver may be approximate. -/
def coarseResponse (transfer : TransferPair 𝕜 E F) (solve : Module.End 𝕜 F) (α : 𝕜) :
    Module.End 𝕜 E :=
  α • (transfer.prolong ∘ₗ solve ∘ₗ transfer.restrict)

/-- The coarse response restricts, solves, prolongs, and scales a fine residual. -/
@[simp]
theorem coarseResponse_apply (transfer : TransferPair 𝕜 E F) (solve : Module.End 𝕜 F)
    (α : 𝕜) (residual : E) :
    transfer.coarseResponse solve α residual =
      α • transfer.prolong (solve (transfer.restrict residual)) :=
  rfl

end TransferPair

/-- The **residual correction** with fine operator $A$, right-hand side $b$, and response $M$
is the update $x \mapsto x + M(b - Ax)$. -/
def residualCorrection (A response : Module.End 𝕜 E) (rhs iterate : E) : E :=
  iterate + response (rhs - A iterate)

/-- The **residual-correction error operator** for $A$ and response $M$ is $I - MA$. -/
def residualError (A response : Module.End 𝕜 E) : Module.End 𝕜 E :=
  1 - response * A

/-- The error operator subtracts the response to $Ae$ from an error $e$. -/
@[simp]
theorem residualError_apply (A response : Module.End 𝕜 E) (error : E) :
    residualError A response error = error - response (A error) :=
  rfl

/-- If $Ax_* = b$, the residual correction of $x$ gives error $(I - MA)(x_* - x)$. -/
theorem residualCorrection_error (A response : Module.End 𝕜 E) {rhs solution : E}
    (hsol : A solution = rhs) (iterate : E) :
    solution - residualCorrection A response rhs iterate =
      residualError A response (solution - iterate) := by
  rw [residualCorrection, residualError_apply, A.map_sub, hsol, sub_sub]

/-- If the response $M$ is injective, a fixed point of $x \mapsto x+M(b-Ax)$ is exactly a
solution of $Ax=b$. Injectivity of $A$ is not required. -/
theorem residualCorrection_fixed_iff (A response : Module.End 𝕜 E)
    (hinj : Function.Injective response) (rhs iterate : E) :
    residualCorrection A response rhs iterate = iterate ↔ A iterate = rhs := by
  change iterate + response (rhs - A iterate) = iterate ↔ _
  rw [add_eq_left, ← response.map_zero, hinj.eq_iff, sub_eq_zero, eq_comm]

/-- Applying the same correction $k$ times propagates the error by $(I - MA)^k$. -/
theorem residualCorrection_iterate_error (A response : Module.End 𝕜 E) {rhs solution : E}
    (hsol : A solution = rhs) (count : ℕ) (iterate : E) :
    solution - (residualCorrection A response rhs)^[count] iterate =
      (residualError A response ^ count) (solution - iterate) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply', residualCorrection_error A response hsol, ih,
      pow_succ', Module.End.mul_apply]

/-- For two successive responses $M$ and $N$, the **combined response** to the original
residual is $M + N(I - AM)$: the second update uses the residual after the first. -/
def combineResponses (A first second : Module.End 𝕜 E) : Module.End 𝕜 E :=
  first + second * (1 - A * first)

/-- The combined response to $r$ adds $Mr$ and the second response to $r - AMr$. -/
@[simp]
theorem combineResponses_apply (A first second : Module.End 𝕜 E) (residual : E) :
    combineResponses A first second residual =
      first residual + second (residual - A (first residual)) :=
  rfl

/-- A correction with the combined response gives a correction with the first response
followed by a correction with the second one. -/
theorem residualCorrection_combineResponses (A first second : Module.End 𝕜 E)
    (rhs iterate : E) :
    residualCorrection A (combineResponses A first second) rhs iterate =
      residualCorrection A second rhs (residualCorrection A first rhs iterate) := by
  simp only [residualCorrection, combineResponses_apply, map_add, ← sub_sub, add_assoc]

/-- The **response for repeated corrections** is zero at count zero and appends a correction
with response $M$ at each successor count. -/
def repeatResponse (A response : Module.End 𝕜 E) : ℕ → Module.End 𝕜 E
  | 0 => 0
  | count + 1 => combineResponses A (repeatResponse A response count) response

/-- A correction with the repeated response is the corresponding repeated affine update. -/
theorem residualCorrection_repeatResponse (A response : Module.End 𝕜 E) (rhs : E)
    (count : ℕ) (iterate : E) :
    residualCorrection A (repeatResponse A response count) rhs iterate =
      (residualCorrection A response rhs)^[count] iterate := by
  induction count with
  | zero => simp [repeatResponse, residualCorrection]
  | succ count ih =>
    rw [repeatResponse, residualCorrection_combineResponses, ih, Function.iterate_succ_apply']

/-- A **two-grid step** applies $\nu_1$ pre-smoothing corrections, restricts the residual,
applies a linear coarse solver $D$, adds the prolonged correction scaled by $\alpha$, and
applies $\nu_2$ post-smoothing corrections. The two smoothing responses may differ. -/
def twoGridStep (A : Module.End 𝕜 E) (transfer : TransferPair 𝕜 E F)
    (solve : Module.End 𝕜 F) (α : 𝕜) (pre post : Module.End 𝕜 E) (nuPre nuPost : ℕ)
    (rhs iterate : E) : E :=
  (residualCorrection A post rhs)^[nuPost]
    (residualCorrection A (transfer.coarseResponse solve α) rhs
      ((residualCorrection A pre rhs)^[nuPre] iterate))

/-- If $Ax_* = b$, the two-grid cycle with coarse solver $D$ sends error $x_* - x$ to
$$S_{\rm post}^{\nu_2}(I-\alpha PDRA)S_{\rm pre}^{\nu_1}(x_* - x),$$
where $S_{\rm pre}=I-M_{\rm pre}A$ and $S_{\rm post}=I-M_{\rm post}A$.
The formula holds even for an inexact linear coarse solver. -/
theorem twoGridStep_error (A : Module.End 𝕜 E) (transfer : TransferPair 𝕜 E F)
    (solve : Module.End 𝕜 F) (α : 𝕜) (pre post : Module.End 𝕜 E) (nuPre nuPost : ℕ)
    {rhs solution : E} (hsol : A solution = rhs) (iterate : E) :
    solution - twoGridStep A transfer solve α pre post nuPre nuPost rhs iterate =
      (residualError A post ^ nuPost * residualError A (transfer.coarseResponse solve α) *
        residualError A pre ^ nuPre) (solution - iterate) := by
  rw [twoGridStep, residualCorrection_iterate_error A post hsol,
    residualCorrection_error A _ hsol, residualCorrection_iterate_error A pre hsol]
  rfl

section Hierarchy

variable {Grid : ℕ → Type*} [∀ level, AddCommGroup (Grid level)] [∀ level, Module 𝕜 (Grid level)]

/-- The **V-cycle response** on a hierarchy of modules uses the given base solver at level
$0$. At level $\ell+1$ it combines pre-smoothing, one correction using the level $\ell$ response
as the linear coarse solver, and post-smoothing. Applying the response to the right-hand side
is the V-cycle starting from zero. -/
def vCycleResponse (A pre post : ∀ level, Module.End 𝕜 (Grid level))
    (transfer : ∀ level, TransferPair 𝕜 (Grid (level + 1)) (Grid level))
    (α : ℕ → 𝕜) (nuPre nuPost : ℕ → ℕ) (base : Module.End 𝕜 (Grid 0)) :
    (level : ℕ) → Module.End 𝕜 (Grid level)
  | 0 => base
  | level + 1 =>
    combineResponses (A (level + 1))
      (combineResponses (A (level + 1))
        (repeatResponse (A (level + 1)) (pre (level + 1)) (nuPre (level + 1)))
        ((transfer level).coarseResponse
          (vCycleResponse A pre post transfer α nuPre nuPost base level) (α (level + 1))))
      (repeatResponse (A (level + 1)) (post (level + 1)) (nuPost (level + 1)))

/-- At level zero the V-cycle response is the prescribed base solver. -/
@[simp]
theorem vCycleResponse_zero (A pre post : ∀ level, Module.End 𝕜 (Grid level))
    (transfer : ∀ level, TransferPair 𝕜 (Grid (level + 1)) (Grid level))
    (α : ℕ → 𝕜) (nuPre nuPost : ℕ → ℕ) (base : Module.End 𝕜 (Grid 0)) :
    vCycleResponse A pre post transfer α nuPre nuPost base 0 = base :=
  rfl

/-- Correcting with the V-cycle response at level $\ell+1$ equals a two-grid step with the
level $\ell$ V-cycle response as coarse solver. That coarse cycle starts from zero. -/
theorem residualCorrection_vCycleResponse_succ
    (A pre post : ∀ level, Module.End 𝕜 (Grid level))
    (transfer : ∀ level, TransferPair 𝕜 (Grid (level + 1)) (Grid level))
    (α : ℕ → 𝕜) (nuPre nuPost : ℕ → ℕ) (base : Module.End 𝕜 (Grid 0))
    (level : ℕ) (rhs iterate : Grid (level + 1)) :
    residualCorrection (A (level + 1))
        (vCycleResponse A pre post transfer α nuPre nuPost base (level + 1)) rhs iterate =
      twoGridStep (A (level + 1)) (transfer level)
        (vCycleResponse A pre post transfer α nuPre nuPost base level) (α (level + 1))
        (pre (level + 1)) (post (level + 1)) (nuPre (level + 1)) (nuPost (level + 1))
        rhs iterate := by
  rw [vCycleResponse, residualCorrection_combineResponses, residualCorrection_combineResponses,
    residualCorrection_repeatResponse, residualCorrection_repeatResponse, twoGridStep]

end Hierarchy

end Multigrid
