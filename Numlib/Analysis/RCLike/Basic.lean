import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Unimodular scalars

A scalar `c` of an `RCLike` field with `star c * c = 1` has norm `1`
(`RCLike.norm_eq_one_of_star_mul_self_eq_one`): the entries of a unitary diagonal matrix are
unimodular, which is the form in which the uniqueness statements of the QR and Hessenberg
factorizations ("unique up to a unimodular diagonal") deliver them.

## Implementation notes

This is Mathlib's `CStarRing.norm_of_mem_unitary` for the `CStarRing` instance of an `RCLike`
field, with membership in `unitary` spelled out (`Unitary.mem_iff_star_mul_self`). It is kept
under this name only as a convenience for its callers; being a one-term corollary, it is not an
upstreaming candidate.
-/

/-- A scalar with `star c * c = 1` has norm `1`. -/
theorem RCLike.norm_eq_one_of_star_mul_self_eq_one {𝕜 : Type*} [RCLike 𝕜] {c : 𝕜}
    (hc : star c * c = 1) : ‖c‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Unitary.mem_iff_star_mul_self.2 hc)
