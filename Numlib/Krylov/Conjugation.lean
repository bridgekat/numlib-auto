import Numlib.Krylov.Subspace
/-!
# Grade invariance under an actual intertwining equivalence

An intertwining linear equivalence identifies the full cyclic subspaces.
Their equal finite ranks give the same grade, including infinite-dimensional
cyclic spaces with the standard zero finite-rank convention.
-/

namespace Krylov
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
/-- An actual intertwining linear equivalence preserves the Krylov grade. -/
theorem grade_eq_of_semiconj_equiv (J : V ≃ₗ[K] W) {A : V →ₗ[K] V} {B : W →ₗ[K] W}
    (h : Function.Semiconj J A B) (v : V) : grade A v = grade B (J v) := by
  unfold grade
  change Module.finrank K (fullSubspace A v) =
    Module.finrank K (fullSubspace B (J.toLinearMap v))
  rw [←map_fullSubspace_of_semiconj (N := J.toLinearMap) h v]
  exact (J.finrank_map_eq _).symm
end Krylov
