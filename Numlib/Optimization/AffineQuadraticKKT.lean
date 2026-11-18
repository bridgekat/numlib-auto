import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Quadratic energies on affine constraint sets

The energy $J(u)=a(u,u)/2-\ell(u)$ for a symmetric nonnegative bilinear form $a$ is
minimized on a fiber of a linear map $B$ precisely when its first variation vanishes
on $\ker B$. The annihilator of that kernel is the range of the dual map, so the
stationarity condition has a multiplier in the algebraic dual of the constraint space.

## Main definitions

* `LinearMap.quadraticEnergy`: the energy $J(u)=a(u,u)/2-\ell(u)$.

## Main results

* `LinearMap.isMinOn_quadraticEnergy_iff_kernel`: the first-variation criterion on a fiber.
* `LinearMap.isMinOn_quadraticEnergy_iff_exists_dual`: the same criterion with a dual multiplier.

## Implementation notes

* The multiplier is algebraic. No continuity, coercivity, or existence of minimizers is assumed.
-/

namespace LinearMap

variable {V Q : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Q] [Module ℝ Q]

/-- If $a t^2+b t\ge 0$ for every real $t$, then $b=0$. -/
theorem linearCoeff_eq_zero_of_quadratic_nonneg {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + b * t) : b = 0 := by
  have hmin : IsLocalMin (fun t : ℝ ↦ a * t ^ 2 + b * t) 0 :=
    Filter.Eventually.of_forall fun t ↦ by simpa using h t
  have hd := (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul a).add
    ((hasDerivAt_id (0 : ℝ)).const_mul b)
  apply hmin.hasDerivAt_eq_zero
  change HasDerivAt ((fun t : ℝ ↦ a * t ^ 2) + (fun t ↦ b * t)) b 0
  simpa using hd

/-- For a bilinear form $a$ and a linear functional $\ell$ on a real vector space, the
**quadratic energy** of $u$ is $a(u,u)/2-\ell(u)$. -/
noncomputable def quadraticEnergy (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (load : Module.Dual ℝ V)
    (u : V) : ℝ :=
  a u u / 2 - load u

/-- Evaluating a quadratic energy gives the half diagonal form minus the load. -/
theorem quadraticEnergy_apply (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (load : Module.Dual ℝ V) (u : V) :
    quadraticEnergy a load u = a u u / 2 - load u :=
  rfl

private theorem quadraticEnergy_add_smul_sub (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (load : Module.Dual ℝ V) (hsymm : ∀ u v, a u v = a v u) (u v : V) (t : ℝ) :
    quadraticEnergy a load (u + t • v) - quadraticEnergy a load u =
      (a v v / 2) * t ^ 2 + (a u v - load v) * t := by
  simp only [quadraticEnergy_apply, map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [hsymm v u]
  ring

/-- For a symmetric bilinear form $a$ with $a(v,v)\ge 0$, linear load $\ell$, linear constraint
$B:V\to Q$, and feasible $u$ with $Bu=g$, the energy $a(u,u)/2-\ell(u)$ is minimal among
points with $Bx=g$ if and only if $a(u,v)=\ell(v)$ for every $v$ with $Bv=0$. -/
theorem isMinOn_quadraticEnergy_iff_kernel (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (load : Module.Dual ℝ V) (B : V →ₗ[ℝ] Q) {u : V} {g : Q}
    (hsymm : ∀ u v, a u v = a v u) (hnonneg : ∀ v, 0 ≤ a v v) (hu : B u = g) :
    IsMinOn (quadraticEnergy a load) {x | B x = g} u ↔ ∀ v, B v = 0 → a u v = load v := by
  constructor
  · intro hmin v hv
    apply sub_eq_zero.mp
    apply linearCoeff_eq_zero_of_quadratic_nonneg (a := a v v / 2)
    intro t
    rw [← quadraticEnergy_add_smul_sub a load hsymm u v t, sub_nonneg]
    exact hmin (show u + t • v ∈ {x | B x = g} by simp [hu, hv])
  · intro hstationary x hx
    have hd : B (x - u) = 0 := by rw [map_sub, show B x = g from hx, hu, sub_self]
    have hdiff := quadraticEnergy_add_smul_sub a load hsymm u (x - u) 1
    rw [one_smul, add_sub_cancel, hstationary _ hd, sub_self] at hdiff
    have hp := hnonneg (x - u)
    change quadraticEnergy a load u ≤ quadraticEnergy a load x
    linarith

/-- For a symmetric bilinear form $a$ with $a(v,v)\ge 0$, linear load $\ell$, linear constraint
$B:V\to Q$, and feasible $u$ with $Bu=g$, the energy $a(u,u)/2-\ell(u)$ is minimal on the
fiber $Bx=g$ if and only if some linear functional $\lambda$ on $Q$ satisfies
$a(u,v)+\lambda(Bv)=\ell(v)$ for every $v\in V$. -/
theorem isMinOn_quadraticEnergy_iff_exists_dual (a : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (load : Module.Dual ℝ V) (B : V →ₗ[ℝ] Q) {u : V} {g : Q}
    (hsymm : ∀ u v, a u v = a v u) (hnonneg : ∀ v, 0 ≤ a v v) (hu : B u = g) :
    IsMinOn (quadraticEnergy a load) {x | B x = g} u ↔
      ∃ multiplier : Module.Dual ℝ Q, ∀ v, a u v + multiplier (B v) = load v := by
  rw [isMinOn_quadraticEnergy_iff_kernel a load B hsymm hnonneg hu]
  constructor
  · intro h
    have hmem : load - a u ∈ range B.dualMap := by
      rw [range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
      intro v hv
      exact sub_eq_zero.mpr (h v (mem_ker.mp hv)).symm
    obtain ⟨multiplier, hmultiplier⟩ := hmem
    refine ⟨multiplier, fun v ↦ ?_⟩
    have heq : multiplier (B v) = load v - a u v :=
      congrArg (fun f : Module.Dual ℝ V ↦ f v) hmultiplier
    linarith
  · rintro ⟨multiplier, hmultiplier⟩ v hv
    simpa [hv] using hmultiplier v

end LinearMap
