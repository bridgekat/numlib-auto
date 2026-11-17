import Numlib.Algebra.Polynomial.Commute
import Numlib.Krylov.Subspace
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Minimal polynomials on invariant subspaces

The minimal polynomial of an endomorphism on an invariant subspace is the minimal polynomial of
its restriction to that subspace. Its multiples are precisely the polynomials whose evaluation
annihilates the subspace.

## Main definitions

* `LinearMap.minpolyOn`: the minimal polynomial of the restricted endomorphism.

## Main results

* `LinearMap.minpolyOn_dvd_iff`: characterization by annihilation on the subspace.
* `LinearMap.minpolyOn_fullKrylovSubspace`: identification with the generator's minimal polynomial.
-/

open Polynomial

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The minimal polynomial of $A$ on its invariant subspace $W$ is the minimal polynomial
of $A$ restricted to $W$. -/
noncomputable def minpolyOn (A : Module.End K V) (W : Submodule K V)
    (hW : Set.MapsTo A W W) : K[X] :=
  minpoly K (A.restrict hW)

/-- Applying $p$ to the restriction of $A$ to $W$ agrees with applying $p(A)$ in the ambient
space and taking the resulting vector in $W$. -/
private theorem coe_aeval_restrict (A : Module.End K V) {W : Submodule K V}
    (hW : Set.MapsTo A W W) (p : K[X]) (v : W) :
    ((aeval (A.restrict hW) p v : W) : V) = aeval A p v := by
  have hpows (n : ℕ) : (((A.restrict hW ^ n) v : W) : V) = (A ^ n) (v : V) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      exact congrArg A ih
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ihp, ihq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpows]

/-- The minimal polynomial of $A$ on a finite-dimensional invariant subspace $W$ divides $p$
if and only if $p(A)v=0$ for every $v\in W$. -/
theorem minpolyOn_dvd_iff (A : Module.End K V) {W : Submodule K V} [FiniteDimensional K W]
    (hW : Set.MapsTo A W W) {p : K[X]} :
    A.minpolyOn W hW ∣ p ↔ ∀ v ∈ W, aeval A p v = 0 := by
  rw [minpolyOn, minpoly.dvd_iff]
  refine ⟨fun h v hv => ?_, fun h => ?_⟩
  · rw [← coe_aeval_restrict A hW p ⟨v, hv⟩, h]
    rfl
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (coe_aeval_restrict A hW p v).trans (h v v.property)

/-- The minimal polynomial of $A$ restricted to the finite-dimensional cyclic subspace of $v$
is the minimal polynomial of $v$ with respect to $A$. -/
theorem minpolyOn_fullKrylovSubspace (A : Module.End K V) (v : V)
    [FiniteDimensional K (Krylov.fullSubspace A v)]
    (hW : Set.MapsTo A (Krylov.fullSubspace A v) (Krylov.fullSubspace A v)) :
    A.minpolyOn (Krylov.fullSubspace A v) hW = Krylov.minpolyVec A v := by
  have hv : v ∈ Krylov.fullSubspace A v :=
    Krylov.subspace_le_fullSubspace A v 1 <| Krylov.self_mem_subspace A v (by decide)
  have hm : (A.minpolyOn (Krylov.fullSubspace A v) hW).Monic :=
    minpoly.monic (IsIntegral.of_finite K (A.restrict hW))
  have hp : (Krylov.minpolyVec A v).Monic :=
    Krylov.minpolyVec_monic A v (Krylov.minpolyVec_ne_zero A v)
  have hdiv : A.minpolyOn (Krylov.fullSubspace A v) hW ∣ Krylov.minpolyVec A v := by
    rw [minpolyOn_dvd_iff]
    change Krylov.fullSubspace A v ≤ (aeval A (Krylov.minpolyVec A v)).ker
    rw [Krylov.fullSubspace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hcomm := ((Commute.refl A).pow_right i).aeval_left (Krylov.minpolyVec A v)
    change aeval A (Krylov.minpolyVec A v) ((A ^ i) v) = 0
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
      Krylov.aeval_minpolyVec, map_zero]
  have hdiv' : Krylov.minpolyVec A v ∣ A.minpolyOn (Krylov.fullSubspace A v) hW :=
    (Krylov.minpolyVec_dvd_iff A v).2 ((minpolyOn_dvd_iff A hW).1 dvd_rfl v hv)
  exact eq_of_dvd_of_natDegree_le_of_leadingCoeff hdiv
    (natDegree_le_of_dvd hdiv' hm.ne_zero) (hm.leadingCoeff.trans hp.leadingCoeff.symm)

end LinearMap
