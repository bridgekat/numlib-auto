import Numlib.Approximation.MvPolynomial
import Numlib.RingTheory.MvPolynomial.TotalDegree

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
* `affineSubst` and `exercise_14_1_1` — an invertible affine change of variables carries `Π_n^d`
  onto `Π_n^d`, which is what carries the results of the section from the disk to an ellipse;
  `image_mulVec_diagonal_ellipsoid` is the change of variables itself.

## Not formalized here

* **Theorem 14.1.1**, Ragozin's multivariate Jackson theorem. The book quotes it from D. L.
  Ragozin, *Constructive polynomial approximation on spheres and projective spaces*, Trans. Amer.
  Math. Soc. **162** (1971), and says "the proof is quite complicated and we only reference it".
  Its proof runs through approximation on the sphere `S^d` and needs spherical harmonics, a surface
  measure on `S^d` and a convolution structure on it, none of which Mathlib has.
* The **moduli of continuity** `ω(f, h)`, `ω_n(f, h)` and the norm `‖f‖_{*, n}` that Theorem 14.1.1
  is stated with. Nothing in Mathlib or in `Numlib` defines a modulus of continuity yet; it belongs
  in the backbone, where §12.2 and §12.5 also want it, and not here.
-/

open Module
open scoped Matrix

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

/-! ### Exercise 14.1.1: an affine change of variables -/

/-- The coordinate polynomials `C (v i) + ∑ j C (M i j) X j` of the affine map `x ↦ M x + v`. -/
noncomputable def affineForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin d) :
    MvPolynomial (Fin d) ℝ :=
  MvPolynomial.C (v i) + ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

@[simp]
theorem eval_affineForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin d)
    (x : Fin d → ℝ) : MvPolynomial.eval x (affineForm M v i) = (M *ᵥ x + v) i := by
  simp [affineForm, Matrix.mulVec, dotProduct, add_comm]

theorem totalDegree_affineForm_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (i : Fin d) : (affineForm M v i).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le (by simp) ?_)
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- **The affine change of variables** `p ↦ p(M x + v)` on polynomials, the substitution
Exercise 14.1.1 transports the results of §14.1 along. -/
noncomputable def affineSubst {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (affineForm M v)

theorem eval_affineSubst {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) :
    MvPolynomial.eval x (affineSubst M v p) = MvPolynomial.eval (M *ᵥ x + v) p := by
  rw [affineSubst, ← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval,
    MvPolynomial.aeval_bind₁]
  exact congrArg (fun w => MvPolynomial.aeval w p) (funext fun i => eval_affineForm M v i x)

/-- The affine map inverse to `x ↦ M x + v` is `x ↦ M⁻¹ x − M⁻¹ v`, so the two substitutions are
mutually inverse: `p(M x + v)` evaluated at `M⁻¹ x − M⁻¹ v` is `p`. -/
theorem affineSubst_affineSubst_inv {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) (q : MvPolynomial (Fin d) ℝ) :
    affineSubst M v (affineSubst M⁻¹ (-(M⁻¹ *ᵥ v)) q) = q := by
  refine MvPolynomial.funext fun x => ?_
  rw [eval_affineSubst, eval_affineSubst]
  congr 1
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM,
    Matrix.one_mulVec]
  abel_nf

theorem affineSubst_inv_affineSubst {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) (p : MvPolynomial (Fin d) ℝ) :
    affineSubst M⁻¹ (-(M⁻¹ *ᵥ v)) (affineSubst M v p) = p := by
  refine MvPolynomial.funext fun x => ?_
  rw [eval_affineSubst, eval_affineSubst]
  congr 1
  simp only [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  abel_nf

/-- **Exercise 14.1.1**: an invertible affine change of variables `x ↦ M x + v` carries `Π_n^d`
*onto* `Π_n^d`.  This is what makes the results of §14.1 on the unit disk the same results on an
ellipse: the linear map that takes the disk onto the ellipse takes the polynomials of degree at
most `n` on the one to the polynomials of degree at most `n` on the other, so the spaces `Π_n^2`
that every statement of the section is about correspond, dimension and all.

The bound on the degree is `MvPolynomial.totalDegree_bind₁_le`, applied to the coordinate
polynomials `affineForm M v i`, each of total degree at most one; the surjectivity is the same
bound applied to the inverse substitution. -/
theorem exercise_14_1_1 {d n : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) :
    (polySpace d n).map (affineSubst M v).toLinearMap = polySpace d n :=
  MvPolynomial.restrictTotalDegree_map_bind₁ (totalDegree_affineForm_le M v)
    (totalDegree_affineForm_le M⁻¹ (-(M⁻¹ *ᵥ v))) (affineSubst_inv_affineSubst hM v)
    (affineSubst_affineSubst_inv hM v) n

/-- The solid ellipsoid with semi-axes `a i`, `{x | ∑ (x_i / a_i)² ≤ 1}`; for `d = 2` and
`a = ![α, β]` it is the ellipse `(x/α)² + (y/β)² ≤ 1` of Exercise 14.1.1, and for `a = 1` it is the
unit ball. -/
def ellipsoid {d : ℕ} (a : Fin d → ℝ) : Set (Fin d → ℝ) := {x | ∑ i, (x i / a i) ^ 2 ≤ 1}

/-- **Exercise 14.1.1, the change of variables**: the diagonal linear map `x ↦ (a_i x_i)` carries
the unit ball onto the ellipsoid with semi-axes `a`, and it is invertible, so `exercise_14_1_1`
applies to it. -/
theorem image_mulVec_diagonal_ellipsoid {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) :
    (fun x => Matrix.diagonal a *ᵥ x) '' ellipsoid 1 = ellipsoid a := by
  ext y
  simp only [Set.mem_image, ellipsoid, Set.mem_ofPred_eq, Pi.one_apply, div_one]
  refine ⟨?_, fun hy => ⟨fun i => y i / a i, ?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have hcoord : ∀ i, (Matrix.diagonal a *ᵥ x) i / a i = x i := fun i => by
      rw [Matrix.mulVec_diagonal, mul_comm, mul_div_assoc, div_self (ha i), mul_one]
    simpa only [hcoord] using hx
  · exact hy
  · funext i
    rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (ha i)]

theorem isUnit_det_diagonal {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) :
    IsUnit (Matrix.diagonal a).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i

end AtkinsonHan.Chapter14
