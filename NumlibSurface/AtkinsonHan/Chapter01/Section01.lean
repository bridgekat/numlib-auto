import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Atkinson–Han §1.1: linear spaces

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §1.1.

Chapter 1 is the book's review of functional analysis, and Mathlib has essentially all of it. This
surface therefore states the chapter's numbered *results* and proves each from Mathlib; it does not
restate the chapter's definitions. Definitions 1.1.1, 1.1.3, 1.1.5, 1.1.8, 1.1.9, 1.1.13, 1.1.14
and 1.1.16 — linear space, subspace, linear independence, span, basis and dimension, linear map,
isomorphism, Cartesian product — are Mathlib's `Module`, `Submodule`, `LinearIndependent`,
`Submodule.span`, `Module.Basis` with `FiniteDimensional`, `LinearMap`, `LinearEquiv` and `Prod`.
A surface `def IsLinearSpace` would carry no information and would invite a later reader to use it
in place of `Module`, so none is written.

## Main results

* `theorem_1_1_10` — all bases of a linear space have the same number of elements, namely `dim V`.

## Not formalized here

Examples 1.1.2, 1.1.4, 1.1.6, 1.1.7, 1.1.11, 1.1.12, 1.1.15 and 1.1.17 and the exercises are
illustrations of the definitions, and none is cited by a later result.
-/

namespace AtkinsonHan.Chapter01

variable {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- **Theorem 1.1.10.** Any two bases of a linear space have the same number of elements, and that
number is the dimension of the space: for every basis `b : Module.Basis ι 𝕜 V` the cardinality of
the index type is `dim V`. Comparing two bases through this equality is the book's statement. -/
theorem theorem_1_1_10 {ι : Type*} (b : Module.Basis ι 𝕜 V) :
    Nat.card ι = Module.finrank 𝕜 V :=
  (Module.finrank_eq_nat_card_basis b).symm

end AtkinsonHan.Chapter01
