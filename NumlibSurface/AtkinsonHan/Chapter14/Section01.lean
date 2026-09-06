import Numlib.Approximation.MvPolynomial

/-!
# Atkinson–Han §14.1: multivariable polynomials and best approximation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §14.1.

The section fixes the notation the chapter runs on: `Π_n^d`, the real polynomials in `d` variables
of total degree at most `n`, its dimension `C(n + d, d)`, the minimax error `E_n(f)`, and the
moduli of continuity that Ragozin's theorem is stated with.

`Π_n^d` is Mathlib's `MvPolynomial.restrictTotalDegree (Fin d) ℝ n`, named `polySpace` here, and
`E_n(f) = inf {‖f − p‖_∞ : p ∈ Π_n^d}` is the distance to the copy of `Π_n^d` inside `C(D, ℝ)` that
the backbone calls `Approximation.mvPolyLE`. The backbone's `IsBestApprox` and `Metric.infDist`
already carry the vocabulary of best approximation, so `minimaxError` names a distance rather than
introducing a notion. What is new is the dimension count.

## Main results

* `polySpace` — the book's `Π_n^d`.
* `finrank_polySpace` — `dim Π_n^d = C(n + d, d)`, the backbone
  `MvPolynomial.finrank_restrictTotalDegree`.
* `finrank_polySpace_two` — the planar case `dim Π_n^2 = (n + 1)(n + 2)/2`, which is the count the
  rest of the chapter uses.
* `minimaxError` — the book's `E_n(f)`, with `minimaxError_antitone`, that it decreases in `n`.

## Not formalized here

* **Theorem 14.1.1**, Ragozin's multivariate Jackson theorem. The book quotes it from D. L.
  Ragozin, *Constructive polynomial approximation on spheres and projective spaces*, Trans. Amer.
  Math. Soc. **162** (1971), and says "the proof is quite complicated and we only reference it".
  Its proof runs through approximation on the sphere `S^d` and needs spherical harmonics, a surface
  measure on `S^d` and a convolution structure on it, none of which Mathlib has.
* The **moduli of continuity** `ω(f, h)`, `ω_n(f, h)` and the norm `‖f‖_{*, n}` that Theorem 14.1.1
  is stated with. Nothing in Mathlib or in `Numlib` defines a modulus of continuity yet; it belongs
  in the backbone, where §12.2 and §12.5 also want it, and not here.
* **Exercise 14.1.1**, that the results of the section carry over to an ellipse by the linear change
  of variables taking it to the disk. What it needs is the invariance of `Π_n^d` under an
  invertible affine substitution, which is a backbone statement about `MvPolynomial.aeval` and is
  not written yet; on its own, with Theorem 14.1.1 out of reach, the exercise has nothing to say.
-/

open Module

namespace AtkinsonHan.Chapter14

/-- `Π_n^d`, the real polynomials in `d` variables of total degree at most `n`. -/
noncomputable abbrev polySpace (d n : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  MvPolynomial.restrictTotalDegree (Fin d) ℝ n

theorem mem_polySpace_iff {d n : ℕ} {p : MvPolynomial (Fin d) ℝ} :
    p ∈ polySpace d n ↔ p.totalDegree ≤ n := by
  rw [polySpace, MvPolynomial.mem_restrictTotalDegree]

theorem polySpace_mono {d : ℕ} : Monotone (polySpace d) := fun _ _ h =>
  MvPolynomial.restrictTotalDegree_mono _ _ h

/-- §14.1: `Π_n^d` has dimension `C(n + d, d)`, the number of monomials `x^α` with `|α| ≤ n`. -/
theorem finrank_polySpace (d n : ℕ) : finrank ℝ (polySpace d n) = (n + d).choose d := by
  simpa using MvPolynomial.finrank_restrictTotalDegree (Fin d) n ℝ

/-- §14.1, the planar case: `dim Π_n^2 = (n + 1)(n + 2)/2`. -/
theorem finrank_polySpace_two (n : ℕ) : finrank ℝ (polySpace 2 n) = (n + 1) * (n + 2) / 2 := by
  rw [finrank_polySpace, Nat.choose_two_right, show n + 2 - 1 = n + 1 from rfl, Nat.mul_comm]

/-- §14.1: the **minimax error** `E_n(f) = inf {‖f − p‖_∞ : p ∈ Π_n^d}` of a continuous function on
a set `D ⊆ ℝ^d`, as the distance from `f` to the copy of `Π_n^d` inside `C(D, ℝ)`. -/
noncomputable def minimaxError {d : ℕ} {D : Set (Fin d → ℝ)} [CompactSpace D] (n : ℕ)
    (f : C(D, ℝ)) : ℝ :=
  Metric.infDist f (Approximation.mvPolyLE D n : Set C(D, ℝ))

/-- §14.1: the minimax error decreases as the degree grows, because the spaces increase. -/
theorem minimaxError_antitone {d : ℕ} {D : Set (Fin d → ℝ)} [CompactSpace D] (f : C(D, ℝ)) :
    Antitone fun n => minimaxError n f := fun _ _ h =>
  Metric.infDist_le_infDist_of_subset (Approximation.mvPolyLE_mono h) ⟨0, Submodule.zero_mem _⟩

end AtkinsonHan.Chapter14
