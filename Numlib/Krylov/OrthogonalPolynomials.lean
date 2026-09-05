import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Perturbation
import Numlib.Eigen.RayleighRitz
import Numlib.Krylov.Convergence.Polynomial
import Numlib.Krylov.Convergence.Superlinear
import Numlib.Krylov.Lanczos
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Lanczos process as orthogonal polynomials

For an endomorphism `A` and a vector `v`, the form `⟪p, q⟫_v = ⟪p(A) v, q(A) v⟫`
(`Krylov.polyInner`) is a sesquilinear form on `𝕜[X]`, and it is an inner product on the
polynomials of degree below the grade of `v`: such a polynomial annihilates `v` only if it is
zero (`Krylov.polyInner_nondegenerate`, which rests on the general fact
`Krylov.aeval_eq_zero_iff_of_degree_lt_grade`). For symmetric `A` the Lanczos vectors are the
orthonormal polynomials of that form evaluated at `A`: `Lanczos.poly A v j` is the polynomial of
degree `j` with `p_j(A) v = v_j` (`Lanczos.aeval_poly`, `Lanczos.poly_degree`), obtained from the
three-term recurrence `β_{j+1} p_{j+2} = (X - α_{j+1}) p_{j+1} - β_j p_j` that the Lanczos
process itself runs, and `Lanczos.polyInner_poly` is its orthonormality
(Meurant–Strakoš[^meurant-strakos] §2.2, Saad, *Iterative Methods*[^saad-iterative] §6.6.2).
As everywhere in this library the recurrence is run past breakdown with no hypothesis, the
inverse of the vanishing `β` being `0`, so that `Lanczos.aeval_poly` holds at every index.

Two consequences follow, both for `m ≤ grade A v`.

* The characteristic polynomial of the tridiagonal matrix `T_m` is the monic multiple of `p_m`:
  `Lanczos.aeval_charpoly_tridiag` evaluates it at `A` on `v` and gets `‖v‖ β_0 ⋯ β_{m-1} v_m`,
  and `Lanczos.charpoly_tridiag_eq` is the identity of polynomials below the grade. It is
  `Arnoldi.aeval_charpoly_mem_orthogonal` of `Numlib.Eigen.RayleighRitz` — Cayley–Hamilton on the
  compression — together with `Lanczos.inner_vec_pow_apply`, which is the only place the scalar
  `‖v‖ β_0 ⋯ β_{m-1}` is computed.
* The Ritz values of `A` on `𝒦_m(A, v)`, that is the eigenvalues of the compression of `A` to
  that subspace, are exactly the eigenvalues of `T_m`
  (`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`), and they are exactly the roots
  of the Lanczos polynomial `p_m` (`Lanczos.hasEigenvalue_compression_iff_isRoot_poly`). The
  first is `Lanczos.hessenbergSq_eq_map_tridiag` read through
  `Arnoldi.hessenbergSq_eq_toMatrix_compression`; the second is the same charpoly identity again.

In finite dimension the form is an integral. `Krylov.spectralMeasure` is the discrete measure
`∑_l |⟪u_l, v⟫|² δ_{λ_l}` over an eigenbasis of the symmetric `A`, and
`Krylov.polyInner_eq_integral` identifies `⟪p, q⟫_v` with `∫ p q` against it, so the Lanczos
polynomials are the orthonormal polynomials of that measure and `Krylov.inner_aeval_eq_integral`
reads its moments off `(A, v)`. The Gauss rule of the measure is then the spectral measure of the
*compressed* pair: `Lanczos.gauss_quadrature` states that the two integrate every polynomial of
degree at most `2m - 1` alike, and `Lanczos.gauss_quadrature_eq_sum` writes the rule out with its
`m` nodes and weights. The nodes are the Ritz values by the second point above, and the weights
are `‖v‖²` times the squared first components of the eigenvectors of `T_m`.

Two results that belong to this circle but not to the Lanczos process itself close the module.
`Polynomial.christoffel_darboux` is the Christoffel–Darboux identity for *any* sequence of
polynomials obeying a three-term recurrence with the orthonormal normalization `c_n a_{n-1} = a_n`
(Atkinson–Han[^atkinson-han] Thm 3.7.3); it is stated division-free, so that it holds over a
commutative ring and at `x = t`, with the quotient form and the confluent form beside it.
`Lanczos.persistence` is the persistence theorem of Paige (Meurant–Strakoš Thm 5): a Ritz value of
`T_{m+1}` whose normalized eigenvector has a small last component `z_m` is approximated to within
`β_m |z_m|` by a Ritz value of every later `T_k`.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-! ### The polynomial inner product of a Krylov pair -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Below the grade a polynomial in `A` annihilates `v` only if it is zero: `p ↦ p(A) v` is
injective on `Polynomial.degreeLT K (grade A v)`, which is what makes `Krylov.polyInner` an
inner product there. -/
theorem aeval_eq_zero_iff_of_degree_lt_grade (A : Module.End K V) (v : V)
    [FiniteDimensional K (fullSubspace A v)] {p : K[X]} (hp : p.degree < grade A v) :
    aeval A p v = 0 ↔ p = 0 := by
  refine ⟨fun h => by_contra fun hp0 => ?_, fun h => by rw [h, map_zero, LinearMap.zero_apply]⟩
  have hd : p.natDegree < grade A v := by
    rw [degree_eq_natDegree hp0, Nat.cast_lt] at hp
    exact hp
  refine pow_apply_notMem_subspace_of_lt_grade A v hd ?_
  rw [pow_apply_mem_subspace_iff_exists_monic]
  refine ⟨p * C p.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hp0,
    natDegree_mul_leadingCoeff_inv p hp0, ?_⟩
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply, map_smul, h, smul_zero]

end Field

variable (A : E →ₗ[𝕜] E) (v : E)

/-- The inner product of the Krylov pair `(A, v)` on polynomials:
`⟪p, q⟫_v = ⟪p(A) v, q(A) v⟫` (Saad, *Iterative Methods*, (6.85);
Meurant–Strakoš, (2.4)). It is sesquilinear on all of `𝕜[X]` — conjugate-linear in the first
argument and linear in the second, as `inner` is — and positive semidefinite, but it is definite
only below the grade of `v` (`Krylov.polyInner_nondegenerate`); above the grade its kernel is the
ideal generated by the minimal polynomial of `v`. -/
noncomputable def polyInner (p q : 𝕜[X]) : 𝕜 := inner 𝕜 (aeval A p v) (aeval A q v)

/-- The form is the inner product of `E` pulled back along the evaluation map
`Krylov.polyEval`, which is where its bilinearity comes from. -/
theorem polyInner_eq_inner_polyEval (p q : 𝕜[X]) :
    polyInner A v p q = inner 𝕜 (polyEval A v p) (polyEval A v q) := rfl

/-- The form is additive in its first argument. -/
theorem polyInner_add_left (p q r : 𝕜[X]) :
    polyInner A v (p + q) r = polyInner A v p r + polyInner A v q r := by
  simp [polyInner, inner_add_left]

/-- The form is additive in its second argument. -/
theorem polyInner_add_right (p q r : 𝕜[X]) :
    polyInner A v p (q + r) = polyInner A v p q + polyInner A v p r := by
  simp [polyInner, inner_add_right]

/-- The form is conjugate-homogeneous in its first argument. -/
theorem polyInner_smul_left (c : 𝕜) (p q : 𝕜[X]) :
    polyInner A v (c • p) q = starRingEnd 𝕜 c * polyInner A v p q := by
  simp [polyInner, inner_smul_left]

/-- The form is homogeneous in its second argument. -/
theorem polyInner_smul_right (c : 𝕜) (p q : 𝕜[X]) :
    polyInner A v p (c • q) = c * polyInner A v p q := by
  simp [polyInner, inner_smul_right]

/-- The form is Hermitian: `⟪q, p⟫_v = conj ⟪p, q⟫_v`. -/
theorem polyInner_conj_symm (p q : 𝕜[X]) :
    starRingEnd 𝕜 (polyInner A v p q) = polyInner A v q p :=
  inner_conj_symm _ _

/-- The quadratic form of `Krylov.polyInner` is the squared norm of `p(A) v`; in particular it is
real and nonnegative. -/
theorem polyInner_self (p : 𝕜[X]) : polyInner A v p p = ((‖aeval A p v‖ : ℝ) : 𝕜) ^ 2 :=
  inner_self_eq_norm_sq_to_K _

/-- The form degenerates exactly on the polynomials that annihilate `v`. -/
theorem polyInner_self_eq_zero_iff (p : 𝕜[X]) : polyInner A v p p = 0 ↔ aeval A p v = 0 :=
  inner_self_eq_zero

/-- `Krylov.polyInner` is an inner product on the polynomials of degree below the grade of `v`:
there it is definite (Meurant–Strakoš, §2.2). -/
theorem polyInner_nondegenerate [FiniteDimensional 𝕜 (fullSubspace A v)] {p : 𝕜[X]}
    (hp : p.degree < grade A v) : polyInner A v p p = 0 ↔ p = 0 := by
  rw [polyInner_self_eq_zero_iff, aeval_eq_zero_iff_of_degree_lt_grade A v hp]

/-! ### The discrete spectral measure -/

section SpectralMeasure

open MeasureTheory

variable [FiniteDimensional 𝕜 E]

/-- A real polynomial, mapped into `𝕜` and evaluated at a real point. -/
private theorem eval_map_ofReal (p : ℝ[X]) (t : ℝ) :
    (p.map (algebraMap ℝ 𝕜)).eval ((t : ℝ) : 𝕜) = ((p.eval t : ℝ) : 𝕜) := by
  rw [← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_hom, RCLike.algebraMap_eq_ofReal]

/-- The discrete spectral measure of the pair `(A, v)` for a symmetric `A` in finite dimension
(Meurant–Strakoš, §2.1): the measure `∑_l ω_l δ_{λ_l}` on `ℝ` carried by the eigenvalues of `A`,
with the weight `ω_l = |⟪u_l, v⟫|²` at the eigenvector `u_l`. Its total mass is `‖v‖²`, and the
inner product `Krylov.polyInner A v` of two real polynomials is the integral of their product
against it (`Krylov.polyInner_eq_integral`), so the Lanczos polynomials of `Numlib.Krylov`'s
`Lanczos.poly` are the orthonormal polynomials of this measure.

The measure is defined from Mathlib's eigenvector basis `hA.eigenvectorBasis hn`, so it takes the
symmetry of `A` and the dimension of `E` as arguments rather than just `A` and `v`; grouping the
weights by eigenvalue would make it a function of `(A, v)` alone. -/
noncomputable def spectralMeasure {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) : Measure ℝ :=
  ∑ i : Fin n, ENNReal.ofReal (‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ ^ 2) •
    Measure.dirac (hA.eigenvalues hn i)

/-- Integration against the spectral measure is the weighted sum over the eigenvalues. -/
theorem integral_spectralMeasure {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (f : ℝ → ℝ) :
    ∫ x, f x ∂(spectralMeasure hA hn v)
      = ∑ i : Fin n, ‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ ^ 2 * f (hA.eigenvalues hn i) := by
  rw [spectralMeasure, integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure (by simp)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Meurant–Strakoš, (2.4): the polynomial inner product of `(A, v)` is the integral against the
discrete spectral measure. Both sides are the sum over the eigenbasis of `p(λ_l) q(λ_l) |⟪u_l,
v⟫|²`, on the left because `p(A)` acts diagonally in that basis
(`LinearMap.IsSymmetric.repr_aeval_apply`) and on the right by `Krylov.integral_spectralMeasure`.
-/
theorem polyInner_eq_integral {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (p q : ℝ[X]) :
    polyInner A v (p.map (algebraMap ℝ 𝕜)) (q.map (algebraMap ℝ 𝕜))
      = ((∫ x, p.eval x * q.eval x ∂(spectralMeasure hA hn v) : ℝ) : 𝕜) := by
  have hrepr : ∀ (r : ℝ[X]) (i : Fin n),
      inner 𝕜 (hA.eigenvectorBasis hn i) (aeval A (r.map (algebraMap ℝ 𝕜)) v)
        = ((r.eval (hA.eigenvalues hn i) : ℝ) : 𝕜) *
          inner 𝕜 (hA.eigenvectorBasis hn i) v := fun r i => by
    rw [← OrthonormalBasis.repr_apply_apply, hA.repr_aeval_apply hn, eval_map_ofReal,
      OrthonormalBasis.repr_apply_apply]
  rw [integral_spectralMeasure, polyInner,
    ← OrthonormalBasis.sum_inner_mul_inner (hA.eigenvectorBasis hn)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : inner 𝕜 (aeval A (p.map (algebraMap ℝ 𝕜)) v) (hA.eigenvectorBasis hn i)
      = starRingEnd 𝕜 (inner 𝕜 (hA.eigenvectorBasis hn i)
        (aeval A (p.map (algebraMap ℝ 𝕜)) v)) := (inner_conj_symm _ _).symm
  have hcc : starRingEnd 𝕜 (inner 𝕜 (hA.eigenvectorBasis hn i) v) *
      inner 𝕜 (hA.eigenvectorBasis hn i) v
      = ((‖inner 𝕜 (hA.eigenvectorBasis hn i) v‖ : ℝ) : 𝕜) ^ 2 := RCLike.conj_mul _
  rw [hconj, hrepr, hrepr, map_mul, RCLike.conj_ofReal, ← hcc]
  ring

/-- The moments of the spectral measure are the moments of `(A, v)`: `∫ f dμ = ⟪v, f(A) v⟫`. It
is `Krylov.polyInner_eq_integral` at `p = 1`, and the form in which the measure is used. -/
theorem inner_aeval_eq_integral {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) (f : ℝ[X]) :
    inner 𝕜 v (aeval A (f.map (algebraMap ℝ 𝕜)) v)
      = ((∫ x, f.eval x ∂(spectralMeasure hA hn v) : ℝ) : 𝕜) := by
  have h := polyInner_eq_integral hA hn v 1 f
  simpa [polyInner] using h

end SpectralMeasure

end Krylov

open Krylov

namespace Lanczos

/-! ### The Lanczos polynomials -/

/-- The pair `(p_j, p_{j+1})` of consecutive Lanczos polynomials: the two-step recurrence of
`Lanczos.poly` written as a one-step recursion, so that the equations of `Lanczos.poly` hold by
`rfl`. -/
private noncomputable def polyPair (A : E →ₗ[𝕜] E) (v : E) : ℕ → 𝕜[X] × 𝕜[X]
  | 0 => (C ((‖v‖ : 𝕜))⁻¹,
      C ((beta A v 0 : 𝕜))⁻¹ * ((X - C (alpha A v 0 : 𝕜)) * C ((‖v‖ : 𝕜))⁻¹))
  | j + 1 => ((polyPair A v j).2,
      C ((beta A v (j + 1) : 𝕜))⁻¹ *
        ((X - C (alpha A v (j + 1) : 𝕜)) * (polyPair A v j).2 -
          C (beta A v j : 𝕜) * (polyPair A v j).1))

/-- The Lanczos polynomials of the pair `(A, v)`: `p_0 = 1/‖v‖` and

`β_{j+1} p_{j+2} = (X - α_{j+1}) p_{j+1} - β_j p_j`,

the three-term recurrence the Lanczos process runs (Meurant–Strakoš, §2.2; Saad,
*Iterative Methods*, §6.6.2). For symmetric `A` they are exactly the polynomials that produce the
Lanczos vectors, `p_j(A) v = v_j` (`Lanczos.aeval_poly`), so below the grade they are the
orthonormal polynomials of `Krylov.polyInner A v` (`Lanczos.polyInner_poly`) and `p_j` has degree
`j` (`Lanczos.poly_degree`). The recurrence is divided by `β_{j+1}` rather than multiplied out,
which makes it hold at every index: from the grade onwards the vanishing `β` inverts to `0` and
both `p_j` and `v_j` are `0`. -/
noncomputable def poly (A : E →ₗ[𝕜] E) (v : E) (j : ℕ) : 𝕜[X] := (polyPair A v j).1

variable (A : E →ₗ[𝕜] E) (v : E)

/-- The Lanczos process starts from the normalized vector: `p_0 = 1/‖v‖`. -/
theorem poly_zero : poly A v 0 = C ((‖v‖ : 𝕜))⁻¹ := rfl

/-- First step of the recurrence: `β_0 p_1 = (X - α_0) p_0`. -/
theorem poly_one :
    poly A v 1 = C ((beta A v 0 : 𝕜))⁻¹ * ((X - C (alpha A v 0 : 𝕜)) * poly A v 0) := rfl

/-- The three-term recurrence `β_{j+1} p_{j+2} = (X - α_{j+1}) p_{j+1} - β_j p_j`, in the
divided form that survives breakdown. -/
theorem poly_add_two (j : ℕ) :
    poly A v (j + 2) = C ((beta A v (j + 1) : 𝕜))⁻¹ *
      ((X - C (alpha A v (j + 1) : 𝕜)) * poly A v (j + 1) - C (beta A v j : 𝕜) * poly A v j) :=
  rfl

/-! #### The recurrence step: evaluated, bounded, and read in its top coefficient

Three computations on the shape `C c * ((X - C a) * p - C b * q)` of the recurrence; each of the
three inductions below uses one of them at both of its base cases (with `b = 0` and `q = 0`) and
at its step. -/

private theorem aeval_recur (c a b : 𝕜) (p q : 𝕜[X]) :
    aeval A (C c * ((X - C a) * p - C b * q)) v =
      c • (A (aeval A p v) - a • aeval A p v - b • aeval A q v) := by
  rw [map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply, map_sub,
    LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply, aeval_X,
    aeval_C, Module.algebraMap_end_apply, map_mul, Module.End.mul_apply, aeval_C,
    Module.algebraMap_end_apply]

private theorem natDegree_recur (c a b : 𝕜) {p q : 𝕜[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n + 1) :
    (C c * ((X - C a) * p - C b * q)).natDegree ≤ n + 1 := by
  refine le_trans (natDegree_mul_le) ?_
  rw [natDegree_C, zero_add]
  refine le_trans (natDegree_sub_le _ _) (max_le (le_trans (natDegree_mul_le) ?_)
    (le_trans (natDegree_mul_le) ?_))
  · rw [natDegree_X_sub_C]
    omega
  · rw [natDegree_C]
    omega

private theorem coeff_recur (c a b : 𝕜) {p q : 𝕜[X]} {n : ℕ} (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n) :
    (C c * ((X - C a) * p - C b * q)).coeff (n + 1) = c * p.coeff n := by
  rw [coeff_C_mul, coeff_sub, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (n := n + 1) (by omega),
    coeff_eq_zero_of_natDegree_lt (n := n + 1) (by omega), mul_zero, mul_zero, sub_zero, sub_zero]

/-- The `j = 1` case of the recurrence, in the shape the three helpers above accept. -/
private theorem poly_one' :
    poly A v 1 = C ((beta A v 0 : 𝕜))⁻¹ *
      ((X - C (alpha A v 0 : 𝕜)) * poly A v 0 - C (0 : 𝕜) * 0) := by
  rw [mul_zero, sub_zero]
  exact poly_one A v

/-! #### The Lanczos polynomials produce the Lanczos vectors -/

private theorem aeval_poly_zero : aeval A (poly A v 0) v = Arnoldi.vec A v 0 := by
  rw [poly_zero, aeval_C, Module.algebraMap_end_apply]
  rcases eq_or_ne v 0 with rfl | hv
  · rw [(Arnoldi.vec_eq_zero_iff_pow_apply_mem A 0 0).2 (by simp), smul_zero]
  · rw [Arnoldi.vec_zero A v hv]

/-- `v_{j+1} = β_j⁻¹ w_j`, the normalization step of the Lanczos process written with `β`. -/
private theorem vec_succ_eq_beta (j : ℕ) :
    Arnoldi.vec A v (j + 1) = ((beta A v j : 𝕜))⁻¹ • Arnoldi.w A v j := by
  have hb : beta A v j = ‖Arnoldi.w A v j‖ := rfl
  rw [Arnoldi.vec_succ_eq, ← hb]

/-- The first step of the process: `w_0 = A v_0 - α_0 v_0`. -/
private theorem w_zero_eq {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) :
    Arnoldi.w A v 0 = A (Arnoldi.vec A v 0) - (alpha A v 0 : 𝕜) • Arnoldi.vec A v 0 := by
  rw [Arnoldi.w, Finset.sum_range_one, coe_alpha v hA 0]

/-- The Lanczos polynomials evaluated at `A` produce the Lanczos vectors: `p_j(A) v = v_j`
(Meurant–Strakoš, §2.2; Saad, *Iterative Methods*, §6.6.2). No hypothesis on the grade is
needed: past breakdown both sides are `0`. -/
theorem aeval_poly {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E) (j : ℕ) :
    aeval A (poly A v j) v = Arnoldi.vec A v j := by
  induction j using Nat.twoStepInduction with
  | zero => exact aeval_poly_zero A v
  | one =>
    rw [poly_one' A v, aeval_recur, aeval_poly_zero, map_zero, LinearMap.zero_apply, smul_zero,
      sub_zero, ← w_zero_eq hA v, vec_succ_eq_beta]
  | more j ih1 ih2 =>
    rw [poly_add_two, aeval_recur, ih1, ih2, ← w_succ_eq v hA j, vec_succ_eq_beta]

/-! #### Degree and orthonormality -/

/-- The `j`-th Lanczos polynomial has degree at most `j`; it has degree exactly `j` below the
grade (`Lanczos.poly_degree`). -/
theorem poly_natDegree_le (j : ℕ) : (poly A v j).natDegree ≤ j := by
  induction j using Nat.twoStepInduction with
  | zero => rw [poly_zero]; exact le_of_eq (natDegree_C _)
  | one =>
    rw [poly_one' A v]
    exact natDegree_recur _ _ _ (by rw [poly_zero]; exact le_of_eq (natDegree_C _)) (by simp)
  | more j _ ih2 => exact poly_add_two A v j ▸ natDegree_recur _ _ _ ih2 (by omega)

/-- The leading coefficient of the `j`-th Lanczos polynomial is `1/(‖v‖ β_0 ⋯ β_{j-1})`, the
reciprocal of the scalar of `Lanczos.aeval_charpoly_tridiag`. -/
theorem poly_coeff_self (j : ℕ) :
    (poly A v j).coeff j = (((‖v‖ * ∏ i ∈ Finset.range j, beta A v i)⁻¹ : ℝ) : 𝕜) := by
  induction j using Nat.twoStepInduction with
  | zero => rw [poly_zero, coeff_C_zero]; norm_num
  | one =>
    rw [poly_one' A v,
      coeff_recur _ _ _ (by rw [poly_zero]; exact le_of_eq (natDegree_C _)) (by simp),
      poly_zero, coeff_C_zero, Finset.prod_range_one]
    push_cast
    rw [mul_inv, mul_comm]
  | more j _ ih2 =>
    rw [poly_add_two, coeff_recur _ _ _ (poly_natDegree_le A v (j + 1))
        (le_trans (poly_natDegree_le A v j) (by omega)), ih2]
    simp only [Finset.prod_range_succ]
    push_cast
    ring

/-- The scalar `‖v‖ β_0 ⋯ β_{j-1}` is nonzero exactly as long as the Lanczos process has not
broken down. -/
theorem norm_mul_prod_beta_ne_zero [FiniteDimensional 𝕜 (fullSubspace A v)] {j : ℕ}
    (hj : j < grade A v) : (‖v‖ * ∏ i ∈ Finset.range j, beta A v i) ≠ 0 := by
  have hv : v ≠ 0 := fun h => by
    rw [h, grade_zero] at hj
    exact Nat.not_lt_zero _ hj
  refine mul_ne_zero (norm_ne_zero_iff.2 hv) (Finset.prod_ne_zero_iff.2 fun i hi h0 => ?_)
  have hc : Arnoldi.coeff A v (i + 1) i = 0 := by
    rw [← coe_beta A v i, h0, RCLike.ofReal_zero]
  have := Finset.mem_range.1 hi
  have := (Arnoldi.coeff_succ_self_eq_zero_iff A v i).1 hc
  omega

/-- Below the grade the `j`-th Lanczos polynomial has degree exactly `j`, so `p_0, …, p_{m-1}` is
a basis of the polynomials of degree `< m` for every `m ≤ grade A v`. -/
theorem poly_degree [FiniteDimensional 𝕜 (fullSubspace A v)] {j : ℕ} (hj : j < grade A v) :
    (poly A v j).degree = j := by
  refine degree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_degree_le.1 (poly_natDegree_le A v j))
    ?_
  rw [poly_coeff_self, Ne, RCLike.ofReal_eq_zero]
  exact inv_ne_zero (norm_mul_prod_beta_ne_zero A v hj)

-- Only the diagonal case needs a bound, and there the two indices are equal.
set_option linter.unusedVariables false in
/-- The Lanczos polynomials are orthonormal for `Krylov.polyInner A v` below the grade
(Meurant–Strakoš, §2.2): they are the orthonormal polynomials of the pair `(A, v)`, which is what
`Arnoldi.orthonormal` says once the Lanczos vectors are read as `p_j(A) v`. -/
theorem polyInner_poly {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {i j : ℕ} (hi : i < grade A v)
    (hj : j < grade A v) :
    polyInner A v (poly A v i) (poly A v j) = if i = j then 1 else 0 := by
  rw [polyInner, aeval_poly hA, aeval_poly hA]
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K,
      Arnoldi.norm_vec_eq_one_of_lt_grade A v hi, RCLike.ofReal_one, one_pow]
  · rw [ite_eq_right hij, Arnoldi.inner_vec_eq_zero A v hij]

/-! ### The characteristic polynomial of the tridiagonal matrix -/

/-- The Arnoldi coefficients, unfolded. -/
private theorem inner_vec_apply_vec (i j : ℕ) :
    inner 𝕜 (Arnoldi.vec A v i) (A (Arnoldi.vec A v j)) = Arnoldi.coeff A v i j := rfl

/-- The scalar of `Lanczos.aeval_charpoly_tridiag`, computed: the component of `A^m v` along the
`m`-th Lanczos vector is `‖v‖ β_0 ⋯ β_{m-1}`. Each step of the Lanczos process multiplies it by
the new `β`, because `v_{m+1}` is orthogonal to `𝒦_{m+1}` and `⟪v_{m+1}, A v_m⟫ = β_m`. -/
theorem inner_vec_pow_apply (m : ℕ) :
    inner 𝕜 (Arnoldi.vec A v m) ((A ^ m) v)
      = ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) := by
  induction m with
  | zero =>
    rw [pow_zero, Module.End.one_apply, Finset.prod_range_zero, mul_one]
    rcases eq_or_ne v 0 with rfl | hv
    · rw [inner_zero_right, norm_zero, RCLike.ofReal_zero]
    · rw [Arnoldi.vec_zero A v hv, inner_smul_left, map_inv₀, RCLike.conj_ofReal,
        inner_self_eq_norm_sq_to_K, sq, ← mul_assoc, inv_mul_cancel₀ (by
          simpa using norm_ne_zero_iff.2 hv), one_mul]
  | succ m ih =>
    have hmem : (A ^ m) v ∈ subspace A v (m + 1) := pow_apply_mem_subspace A v m.lt_succ_self
    have hpow : (A ^ (m + 1)) v = A ((A ^ m) v) := by rw [pow_succ']; rfl
    rw [hpow, Arnoldi.eq_sum_inner_smul_vec A v hmem, map_sum, inner_sum,
      Finset.sum_eq_single m]
    · rw [map_smul, inner_smul_right, inner_vec_apply_vec, ← coe_beta A v m, ih,
        Finset.prod_range_succ]
      push_cast
      ring
    · intro i hi hne
      rw [map_smul, inner_smul_right, inner_vec_apply_vec,
        Arnoldi.coeff_eq_zero_of_lt A v (by have := Finset.mem_range.1 hi; omega), mul_zero]
    · intro h
      exact absurd (Finset.self_mem_range_succ m) h

/-- A vector of `𝒦_{m+1}` orthogonal to `𝒦_m` is a multiple of the `m`-th Lanczos vector. -/
private theorem eq_inner_smul_vec (m : ℕ) {x : E} (hx : x ∈ subspace A v (m + 1))
    (hxo : x ∈ (subspace A v m)ᗮ) :
    x = inner 𝕜 (Arnoldi.vec A v m) x • Arnoldi.vec A v m := by
  have hzero : ∀ i ∈ Finset.range m,
      inner 𝕜 (Arnoldi.vec A v i) x • Arnoldi.vec A v i = (0 : E) := fun i hi => by
    rw [(Submodule.mem_orthogonal _ _).1 hxo _
      (Arnoldi.vec_mem_subspace_of_lt A v (Finset.mem_range.1 hi)), zero_smul]
  conv_lhs => rw [Arnoldi.eq_sum_inner_smul_vec A v hx]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero hzero, zero_add]

variable {A}

/-- `T_m` is the matrix of the compression of `A` to `𝒦_m` in the Lanczos basis
(`Arnoldi.hessenbergSq_eq_toMatrix_compression`, `Lanczos.hessenbergSq_eq_map_tridiag`), so its
characteristic polynomial, read in `𝕜`, is the characteristic polynomial of that compression. -/
theorem charpoly_tridiag_map (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) :
    (tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      = LinearMap.charpoly (compression A (subspace A v m)) := by
  rw [← Matrix.charpoly_map, ← hessenbergSq_eq_map_tridiag v hA m,
    Arnoldi.hessenbergSq_eq_toMatrix_compression A v hm, LinearMap.charpoly_toMatrix]

/-- Saad, *Iterative Methods*, §6.6.2 (e); Meurant–Strakoš, (2.6): the characteristic polynomial
of the tridiagonal matrix `T_m`, evaluated at `A` on `v`, is `‖v‖ β_0 ⋯ β_{m-1} v_m`. It is
therefore the monic multiple of the `m`-th Lanczos polynomial, and its roots are the Ritz values
of `A` on `𝒦_m(A, v)` (`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`).

The proof is Cayley–Hamilton on the compression of `A` to `𝒦_m`
(`Arnoldi.aeval_charpoly_mem_orthogonal`), which puts the vector in `𝒦_{m+1} ∩ 𝒦_mᗮ` — a line
spanned by `v_m` — together with `Lanczos.inner_vec_pow_apply` for the scalar, the two lower-order
terms of the characteristic polynomial contributing nothing to it. -/
theorem aeval_charpoly_tridiag (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) :
    aeval A ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)) v =
      ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) • Arnoldi.vec A v m := by
  have hcp := charpoly_tridiag_map hA v hm
  set c := LinearMap.charpoly (compression A (subspace A v m)) with hc
  have hcm : c.Monic := LinearMap.charpoly_monic _
  have hcd : c.degree = (m : ℕ) := by
    rw [degree_eq_natDegree hcm.ne_zero, hc, LinearMap.charpoly_natDegree, finrank_subspace,
      min_eq_left hm]
  have hlt : (c - X ^ m).degree < (m : WithBot ℕ) := by
    rw [← hcd]
    exact degree_sub_lt_left (by rw [hcd, degree_X_pow]) hcm.ne_zero
      (by rw [hcm.leadingCoeff, (monic_X_pow m).leadingCoeff])
  have hsplit : aeval A c v = (A ^ m) v + aeval A (c - X ^ m) v := by
    rw [map_sub, LinearMap.sub_apply, map_pow, aeval_X]
    abel
  have hinner : inner 𝕜 (Arnoldi.vec A v m) (aeval A c v)
      = inner 𝕜 (Arnoldi.vec A v m) ((A ^ m) v) := by
    rw [hsplit, inner_add_right, Submodule.inner_left_of_mem_orthogonal
      (aeval_apply_mem_subspace A v hlt) (Arnoldi.vec_mem_orthogonal A v m), add_zero]
  rw [hcp]
  refine (eq_inner_smul_vec A v m (aeval_apply_mem_subspace A v (by
    rw [hcd]; exact_mod_cast m.lt_succ_self)) (Arnoldi.aeval_charpoly_mem_orthogonal A v hm)).trans
    ?_
  rw [hinner, inner_vec_pow_apply]

/-! ### The Ritz values are the eigenvalues of the tridiagonal matrix -/

/-- Meurant–Strakoš, §2.3: the Ritz values of `A` on `𝒦_m(A, v)` — the eigenvalues of the
compression of `A` to that subspace, by `Krylov.isRitzPair_iff_hasEigenvector` — are exactly the
eigenvalues of the Lanczos matrix `T_m`. The Lanczos vectors are an orthonormal basis of `𝒦_m`
below the grade and `T_m` is the matrix of the compression in that basis
(`Arnoldi.hessenbergSq_eq_toMatrix_compression`, `Lanczos.hessenbergSq_eq_map_tridiag`), so the
two spectra correspond; that both are real spectra of a real matrix and of an operator on a
`𝕜`-space costs one step through the characteristic polynomial. -/
theorem hasEigenvalue_compression_iff_mem_spectrum_tridiag (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m ≤ grade A v) (θ : ℝ) :
    Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜) ↔
      θ ∈ spectrum ℝ (tridiag A v m) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum,
    ← LinearMap.spectrum_toMatrix _ (Arnoldi.orthonormalBasis A v hm).toBasis,
    ← Arnoldi.hessenbergSq_eq_toMatrix_compression A v hm, hessenbergSq_eq_map_tridiag v hA m,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_map]
  simp only [IsRoot.def, ← RCLike.algebraMap_eq_ofReal, eval_map, eval₂_hom]
  exact map_eq_zero_iff _ (algebraMap ℝ 𝕜).injective

/-- Strictly below the grade the characteristic polynomial of `T_m` is the monic multiple of the
`m`-th Lanczos polynomial: `p_{T_m} = ‖v‖ β_0 ⋯ β_{m-1} p_m` (Meurant–Strakoš, (2.6)). Both sides
have degree `m` and the same leading coefficient, and both annihilate `v` after subtraction, so
they agree by `Krylov.aeval_eq_zero_iff_of_degree_lt_grade`. At `m = grade A v` the statement
fails and is not merely unproved: there `p_m = 0` while the characteristic polynomial is
monic. -/
theorem charpoly_tridiag_eq (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m < grade A v) :
    (tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      = C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m := by
  have hg : (‖v‖ * ∏ i ∈ Finset.range m, beta A v i) ≠ 0 := norm_mul_prod_beta_ne_zero A v hm
  have hg' : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) ≠ 0 := by
    rwa [Ne, RCLike.ofReal_eq_zero]
  have hpd : (poly A v m).degree = (m : ℕ) := poly_degree A v hm
  have hcm : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)).Monic :=
    ((tridiag A v m).charpoly_monic).map _
  have hcd : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)).degree = (m : ℕ) := by
    rw [degree_eq_natDegree hcm.ne_zero, ((tridiag A v m).charpoly_monic).natDegree_map,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmd : (C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).degree
      = (m : ℕ) := by
    rw [degree_mul, degree_C hg', zero_add, hpd]
  have hml : (C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).leadingCoeff
      = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff, natDegree_eq_of_degree_eq_some hpd,
      poly_coeff_self, ← RCLike.ofReal_mul, mul_inv_cancel₀ hg, RCLike.ofReal_one]
  have hsub : ((tridiag A v m).charpoly.map (algebraMap ℝ 𝕜)
      - C ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * poly A v m).degree
      < (grade A v : WithBot ℕ) := by
    refine lt_of_lt_of_le (lt_of_lt_of_le (degree_sub_lt_left (hcd.trans hmd.symm) hcm.ne_zero
      (by rw [hcm.leadingCoeff, hml])) hcd.le) ?_
    exact_mod_cast hm.le
  rw [← sub_eq_zero, ← aeval_eq_zero_iff_of_degree_lt_grade A v hsub, map_sub,
    LinearMap.sub_apply, aeval_charpoly_tridiag hA v hm.le, map_mul, Module.End.mul_apply,
    aeval_C, Module.algebraMap_end_apply, aeval_poly hA, sub_self]

/-- The Ritz values of `A` on `𝒦_m(A, v)` are the roots of the `m`-th Lanczos polynomial: `p_m`
is, up to the factor of `Lanczos.charpoly_tridiag_eq`, the characteristic polynomial of `T_m`.
This is the orthogonal-polynomial reading of
`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag` and, with it, the statement that the
nodes of the `m`-point Gauss rule of the pair `(A, v)` are the Ritz values. -/
theorem hasEigenvalue_compression_iff_isRoot_poly (hA : A.IsSymmetric) (v : E)
    [FiniteDimensional 𝕜 (fullSubspace A v)] {m : ℕ} (hm : m < grade A v) (θ : ℝ) :
    Module.End.HasEigenvalue (compression A (subspace A v m)) (θ : 𝕜) ↔
      (poly A v m).IsRoot (θ : 𝕜) := by
  have hg' : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact norm_mul_prod_beta_ne_zero A v hm
  have key : (((tridiag A v m).charpoly.eval θ : ℝ) : 𝕜)
      = ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * (poly A v m).eval (θ : 𝕜) := by
    rw [← RCLike.algebraMap_eq_ofReal, ← eval₂_hom, ← eval_map, charpoly_tridiag_eq hA v hm,
      eval_mul, eval_C, RCLike.algebraMap_eq_ofReal]
  rw [hasEigenvalue_compression_iff_mem_spectrum_tridiag hA v hm.le θ,
    Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, IsRoot.def]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : ((‖v‖ * ∏ i ∈ Finset.range m, beta A v i : ℝ) : 𝕜) * (poly A v m).eval (θ : 𝕜)
        = 0 := by rw [← key, h, RCLike.ofReal_zero]
    exact (mul_eq_zero.1 h0).resolve_left hg'
  · have h0 : (((tridiag A v m).charpoly.eval θ : ℝ) : 𝕜) = 0 := by rw [key, h, mul_zero]
    rwa [RCLike.ofReal_eq_zero] at h0

/-! ### Gauss quadrature -/

section Gauss

open MeasureTheory

variable [FiniteDimensional 𝕜 E]

/-- Meurant–Strakoš, Thm 1: the `m`-point Gauss quadrature rule of the spectral measure of
`(A, v)` is exact on the polynomials of degree at most `2m - 1`.

The rule is the spectral measure of the *compression* of `A` to `𝒦_m(A, v)` and of the same
vector `v`, that is `∑_j ω_j δ_{θ_j}` over an orthonormal eigenbasis `(θ_j, y_j)` of the
compression with `ω_j = |⟪y_j, v⟫|²` — so it has `m` nodes, its nodes are the Ritz values, which
are the eigenvalues of `T_m` (`Lanczos.hasEigenvalue_compression_iff_mem_spectrum_tridiag`) and
the roots of the `m`-th Lanczos polynomial
(`Lanczos.hasEigenvalue_compression_iff_isRoot_poly`), and its weights are `‖v‖²` times the
squared first components of the eigenvectors of `T_m`, since `v = ‖v‖ v_0` and `(y_j)` is
expanded in the Lanczos basis.

The proof divides `f` by the characteristic polynomial `p` of `T_m`, which is monic of degree
`m`: `f = r + p s` with both `r` and `s` of degree below `m`. The remainder `r` is integrated
identically by the two measures because `r(A) v = r(A_m) v`, the Krylov sequence of `v` staying
inside `𝒦_m` for that many steps. The quotient term contributes nothing on either side: against
the spectral measure of `(A, v)` because `p(A) v` is orthogonal to `𝒦_m ∋ s(A) v`
(`Lanczos.aeval_charpoly_tridiag`), and against the rule because `p(A_m) = 0` by Cayley–Hamilton.
The hypothesis `Module.finrank 𝕜 𝒦_m = m` is `m ≤ grade A v`, the condition that the process has
not yet terminated. -/
theorem gauss_quadrature {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ} (hm : 0 < m)
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) {f : ℝ[X]} (hf : f.natDegree < 2 * m) :
    ∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v)
      = ∫ x, f.eval x ∂(Krylov.spectralMeasure
          (compression.isSymmetric A (subspace A v m) hA) hmk ⟨v, self_mem_subspace A v hm⟩) := by
  have hmg : m ≤ grade A v := by
    have h := finrank_subspace A v m
    rw [hmk] at h
    omega
  have hc : ((tridiag A v m).charpoly).Monic := Matrix.charpoly_monic _
  have hcd : ((tridiag A v m).charpoly).natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨r, s, hfsplit, hrdeg, hsdeg⟩ : ∃ r s : ℝ[X],
      f = r + (tridiag A v m).charpoly * s ∧ r.natDegree < m ∧ s.natDegree < m := by
    refine ⟨f %ₘ (tridiag A v m).charpoly, f /ₘ (tridiag A v m).charpoly,
      (modByMonic_add_div f (tridiag A v m).charpoly).symm, ?_, ?_⟩
    · rcases eq_or_ne (f %ₘ (tridiag A v m).charpoly) 0 with h0 | h0
      · rw [h0, natDegree_zero]
        exact hm
      · have h1 := degree_modByMonic_lt f hc
        rw [degree_eq_natDegree hc.ne_zero, hcd] at h1
        exact (natDegree_lt_iff_degree_lt h0).2 h1
    · rw [natDegree_divByMonic f hc, hcd]
      omega
  have hrmap : (r.map (algebraMap ℝ 𝕜)).natDegree < m :=
    lt_of_le_of_lt natDegree_map_le hrdeg
  have hsmap : (s.map (algebraMap ℝ 𝕜)).degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt degree_map_le ?_
    rcases eq_or_ne s 0 with rfl | h0
    · rw [degree_zero]
      exact WithBot.bot_lt_coe m
    · rw [degree_eq_natDegree h0, Nat.cast_lt]
      exact hsdeg
  have hzeroA : inner 𝕜 v (aeval A (((tridiag A v m).charpoly * s).map (algebraMap ℝ 𝕜)) v)
      = 0 := by
    rw [Polynomial.map_mul, map_mul, Module.End.mul_apply,
      ← hA.aeval_map (tridiag A v m).charpoly v (aeval A (s.map (algebraMap ℝ 𝕜)) v),
      aeval_charpoly_tridiag hA v hmg, inner_smul_left,
      Submodule.inner_left_of_mem_orthogonal (aeval_apply_mem_subspace A v hsmap)
        (Arnoldi.vec_mem_orthogonal A v m), mul_zero]
  have hzeroB : aeval (compression A (subspace A v m))
      (((tridiag A v m).charpoly * s).map (algebraMap ℝ 𝕜))
        ⟨v, self_mem_subspace A v hm⟩ = 0 := by
    rw [Polynomial.map_mul, map_mul, Module.End.mul_apply, charpoly_tridiag_map hA v hmg,
      LinearMap.aeval_self_charpoly, LinearMap.zero_apply]
  have hr : (aeval (compression A (subspace A v m)) (r.map (algebraMap ℝ 𝕜))
      ⟨v, self_mem_subspace A v hm⟩ : E) = aeval A (r.map (algebraMap ℝ 𝕜)) v :=
    compression.aeval_apply_of_forall_pow_mem A (subspace A v m) (r.map (algebraMap ℝ 𝕜))
      fun i hi => pow_apply_mem_subspace A v (lt_of_le_of_lt hi hrmap)
  have key : ((∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v) : ℝ) : 𝕜)
      = ((∫ x, f.eval x ∂(Krylov.spectralMeasure
          (compression.isSymmetric A (subspace A v m) hA) hmk
          ⟨v, self_mem_subspace A v hm⟩) : ℝ) : 𝕜) := by
    rw [← Krylov.inner_aeval_eq_integral, ← Krylov.inner_aeval_eq_integral]
    conv_lhs => rw [hfsplit]
    conv_rhs => rw [hfsplit]
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_right]
    rw [hzeroA, hzeroB, inner_zero_right, add_zero, add_zero, Submodule.coe_inner, hr]
  exact_mod_cast key

/-- `Lanczos.gauss_quadrature` written out as a quadrature rule: the integral of a polynomial of
degree at most `2m - 1` against the spectral measure of `(A, v)` is the `m`-term sum over the
eigenpairs `(θ_j, y_j)` of the compression of `A` to `𝒦_m(A, v)`, with nodes `θ_j` — the Ritz
values, that is the eigenvalues of `T_m` — and weights `|⟪y_j, v⟫|²`. Writing `y_j` in the Lanczos
basis and `v = ‖v‖ v_0`, the weight is `‖v‖²` times the squared first component of the
corresponding eigenvector of `T_m`, which is the form the rule is usually stated in. -/
theorem gauss_quadrature_eq_sum {n : ℕ} {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (v : E) {m : ℕ} (hm : 0 < m)
    (hmk : Module.finrank 𝕜 (subspace A v m) = m) {f : ℝ[X]} (hf : f.natDegree < 2 * m) :
    ∫ x, f.eval x ∂(Krylov.spectralMeasure hA hn v)
      = ∑ j : Fin m, ‖inner 𝕜
            ((compression.isSymmetric A (subspace A v m) hA).eigenvectorBasis hmk j)
            (⟨v, self_mem_subspace A v hm⟩ : subspace A v m)‖ ^ 2 *
          f.eval ((compression.isSymmetric A (subspace A v m) hA).eigenvalues hmk j) := by
  rw [gauss_quadrature hA hn v hm hmk hf, Krylov.integral_spectralMeasure]

end Gauss

end Lanczos

namespace Polynomial

section ChristoffelDarboux

variable {K : Type*} [CommRing K] {p : ℕ → K[X]} {a b c : ℕ → K}
  (hp₁ : p 1 = (C (a 0) * X + C (b 0)) * p 0)
  (hrec : ∀ n, p (n + 2) = (C (a (n + 1)) * X + C (b (n + 1))) * p (n + 1) - C (c (n + 1)) * p n)
  (hac : ∀ n, c (n + 1) * a n = a (n + 1))
include hp₁ hrec hac

/-- **Christoffel–Darboux identity**, division-free form (Atkinson and Han, *Theoretical Numerical
Analysis*, 3rd edition, Thm 3.7.3). For a sequence of polynomials obeying the three-term
recurrence `p_{n+1} = (a_n X + b_n) p_n - c_n p_{n-1}` with the orthonormal normalization
`c_n a_{n-1} = a_n` (and `p_{-1} = 0`, i.e. `p_1 = (a_0 X + b_0) p_0`),

`a_N (x - t) ∑_{n ≤ N} p_n(x) p_n(t) = p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t)`.

Multiplying through by `a_N (x - t)` keeps the statement valid over any commutative ring and at
`x = t`; `Polynomial.christoffel_darboux_div` is the usual quotient form. -/
theorem christoffel_darboux (N : ℕ) (x t : K) :
    a N * (x - t) * ∑ n ∈ Finset.range (N + 1), (p n).eval x * (p n).eval t =
      (p (N + 1)).eval x * (p N).eval t - (p N).eval x * (p (N + 1)).eval t := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, hp₁]
    simp only [eval_mul, eval_add, eval_C, eval_X]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, hrec N, ← hac N]
    simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X]
    linear_combination c (N + 1) * ih

/-- **Christoffel–Darboux identity, confluent form** (Atkinson and Han, *Theoretical Numerical
Analysis*, 3rd edition, Thm 3.7.3). The limit of `Polynomial.christoffel_darboux` as `t → x` is an
identity of polynomials, with the Wronskian of two consecutive members on the right:

`a_N ∑_{n ≤ N} p_n² = p'_{N+1} p_N - p'_N p_{N+1}`.

The hypotheses are those of `Polynomial.christoffel_darboux`. -/
theorem christoffel_darboux_confluent (N : ℕ) :
    C (a N) * ∑ n ∈ Finset.range (N + 1), p n ^ 2 =
      derivative (p (N + 1)) * p N - derivative (p N) * p (N + 1) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, hp₁]
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X]
    ring
  | succ N ih =>
    rw [Finset.sum_range_succ, hrec N, ← hac N, C_mul]
    simp only [derivative_sub, derivative_mul, derivative_add, derivative_C, derivative_X]
    linear_combination C (c (N + 1)) * ih

end ChristoffelDarboux

section Field

variable {K : Type*} [Field K] {p : ℕ → K[X]} {a b c : ℕ → K}
  (hp₁ : p 1 = (C (a 0) * X + C (b 0)) * p 0)
  (hrec : ∀ n, p (n + 2) = (C (a (n + 1)) * X + C (b (n + 1))) * p (n + 1) - C (c (n + 1)) * p n)
  (hac : ∀ n, c (n + 1) * a n = a (n + 1))
include hp₁ hrec hac

/-- **Christoffel–Darboux identity**, quotient form (Atkinson and Han, *Theoretical Numerical
Analysis*, 3rd edition, Thm 3.7.3): for `x ≠ t` and `a_N ≠ 0`,

`∑_{n ≤ N} p_n(x) p_n(t) = (p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t)) / (a_N (x - t))`.

The hypotheses on `p` are those of `Polynomial.christoffel_darboux`. -/
theorem christoffel_darboux_div (N : ℕ) {x t : K} (ha : a N ≠ 0) (hxt : x ≠ t) :
    ∑ n ∈ Finset.range (N + 1), (p n).eval x * (p n).eval t =
      ((p (N + 1)).eval x * (p N).eval t - (p N).eval x * (p (N + 1)).eval t) /
        (a N * (x - t)) := by
  rw [eq_div_iff (mul_ne_zero ha (sub_ne_zero.2 hxt))]
  linear_combination christoffel_darboux hp₁ hrec hac N x t

/-- **Christoffel–Darboux identity, confluent quotient form** (Atkinson and Han, *Theoretical
Numerical Analysis*, 3rd edition, Thm 3.7.3): for `a_N ≠ 0`,

`∑_{n ≤ N} p_n(x)² = (p'_{N+1}(x) p_N(x) - p'_N(x) p_{N+1}(x)) / a_N`.

The hypotheses on `p` are those of `Polynomial.christoffel_darboux`. -/
theorem christoffel_darboux_confluent_div (N : ℕ) (x : K) (ha : a N ≠ 0) :
    ∑ n ∈ Finset.range (N + 1), (p n).eval x ^ 2 =
      ((derivative (p (N + 1))).eval x * (p N).eval x -
        (derivative (p N)).eval x * (p (N + 1)).eval x) / a N := by
  have h := congrArg (eval x) (christoffel_darboux_confluent hp₁ hrec hac N)
  simp only [eval_mul, eval_C, eval_sub, eval_finsetSum, eval_pow] at h
  rw [eq_div_iff ha]
  linear_combination h

end Field

end Polynomial

namespace Lanczos

section Persistence

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (A : E →ₗ[𝕜] E) (b : E) {m k : ℕ}

section Padded

/-- Entrywise description of `T_m`, for reading off a single entry. -/
private theorem tridiag_apply (i j : Fin m) :
    tridiag A b m i j =
      if (i : ℕ) = j then alpha A b i
      else if (i : ℕ) + 1 = j then beta A b i
      else if (j : ℕ) + 1 = i then beta A b j
      else 0 := rfl

/-- The leading `(m+1) × (m+1)` block of `T_k` is `T_{m+1}`: the entries depend only on the
underlying natural numbers. -/
private theorem tridiag_castLE (h : m + 1 ≤ k) (i j : Fin (m + 1)) :
    tridiag A b k (Fin.castLE h i) (Fin.castLE h j) = tridiag A b (m + 1) i j := by
  rw [tridiag_apply, tridiag_apply, Fin.val_castLE, Fin.val_castLE]

/-- A sum over `Fin k` whose summand vanishes past the first `m + 1` indices collapses to a sum
over `Fin (m + 1)`. -/
private theorem sum_eq_sum_castLE (h : m + 1 ≤ k) (F : Fin k → ℝ)
    (hF : ∀ i : Fin k, m + 1 ≤ (i : ℕ) → F i = 0) :
    ∑ i : Fin k, F i = ∑ j : Fin (m + 1), F (Fin.castLE h j) := by
  have hmap : ∑ j : Fin (m + 1), F (Fin.castLE h j) =
      ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), F i :=
    (Finset.sum_map Finset.univ (Fin.castLEEmb h) F).symm
  rw [hmap]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hF x ?_).symm
  by_contra hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

variable (h : m + 1 ≤ k) {y : Fin k → ℝ} {z : Fin (m + 1) → ℝ}
  (hy : ∀ j : Fin (m + 1), y (Fin.castLE h j) = z j)
  (hy0 : ∀ i : Fin k, m + 1 ≤ (i : ℕ) → y i = 0)
include hy hy0

/-- On the first `m + 1` rows the padded vector sees only the leading block, so `T_k ŷ` agrees
there with `T_{m+1} z`. -/
private theorem mulVec_castLE (i : Fin (m + 1)) :
    (tridiag A b k).mulVec y (Fin.castLE h i) = (tridiag A b (m + 1)).mulVec z i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_castLE h _ fun j hj => by rw [hy0 j hj, mul_zero]]
  exact Finset.sum_congr rfl fun j _ => by rw [tridiag_castLE, hy]

/-- Row `m + 1` of `T_k` sees the padding through the single entry `β_m`. -/
private theorem mulVec_of_val_eq {i : Fin k} (hi : (i : ℕ) = m + 1) :
    (tridiag A b k).mulVec y i = beta A b m * z (Fin.last m) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_eq_sum_castLE h _ fun j hj => by rw [hy0 j hj, mul_zero]]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [hy, tridiag_apply, Fin.val_castLE, Fin.val_last, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega)]
  · intro j _ hj
    have hjm : (j : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 j.2) fun hc =>
      hj (Fin.ext (by rw [hc, Fin.val_last]))
    rw [tridiag_apply, Fin.val_castLE, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

omit hy in
/-- Below row `m + 1` the padded vector is annihilated by `T_k`. -/
private theorem mulVec_of_lt_val {i : Fin k} (hi : m + 1 < (i : ℕ)) :
    (tridiag A b k).mulVec y i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases le_or_gt (m + 1) (j : ℕ) with hj | hj
  · rw [hy0 j hj, mul_zero]
  · rw [tridiag_apply, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), zero_mul]

/-- The residual of the padded eigenvector: `T_k ŷ - θ ŷ` is supported on row `m + 1`, where it
equals `β_m z_m`. -/
private theorem mulVec_sub_smul {θ : ℝ} (hθ : (tridiag A b (m + 1)).mulVec z = θ • z)
    (i : Fin k) :
    (tridiag A b k).mulVec y i - θ * y i =
      if (i : ℕ) = m + 1 then beta A b m * z (Fin.last m) else 0 := by
  rcases lt_trichotomy (i : ℕ) (m + 1) with hi | hi | hi
  · have hii : Fin.castLE h ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
    rw [ite_eq_right (by omega), ← hii, mulVec_castLE A b h hy hy0, hy, hθ]
    simp
  · rw [ite_eq_left hi, mulVec_of_val_eq A b h hy hy0 hi, hy0 i hi.ge, mul_zero, sub_zero]
  · rw [ite_eq_right (by omega), mulVec_of_lt_val A b hy0 hi, hy0 i hi.le, mul_zero, sub_zero]

end Padded

/-- A sum of squares over `Fin k` supported on the single value `m + 1` is at most `w ^ 2`:
there is at most one index with that value. -/
private theorem sum_ite_sq_le (h : m + 1 ≤ k) (w : ℝ) :
    ∑ i : Fin k, (if (i : ℕ) = m + 1 then w else 0) ^ 2 ≤ w ^ 2 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · have hzero : ∀ i : Fin k, (if (i : ℕ) = m + 1 then w else 0) ^ 2 = 0 := fun i => by
      have hi := i.isLt
      rw [ite_eq_right (by omega), zero_pow two_ne_zero]
    rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero]
    exact sq_nonneg w
  · rw [Finset.sum_eq_single (⟨m + 1, hlt⟩ : Fin k)]
    · simp
    · intro j _ hj
      rw [ite_eq_right fun hc => hj (Fin.ext hc), zero_pow two_ne_zero]
    · intro hc
      exact absurd (Finset.mem_univ _) hc

/-- **Persistence of Ritz values** (Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate
gradient algorithms in finite precision arithmetic*, Acta Numerica 15 (2006), Thm 5; Chris C.
Paige, *Accuracy and effectiveness of the Lanczos algorithm for the symmetric eigenproblem*,
Linear Algebra and its Applications 34 (1980), 235–258). If `θ` is a Ritz value at step `m + 1`,
that is an eigenvalue of the Lanczos matrix `T_{m+1}` with unit eigenvector `z`, then every later
step `k ≥ m + 1` has a Ritz value `μ` with `|μ - θ| ≤ β_m |z_m|`: a Ritz value whose eigenvector
has a small last component is approximated at every later step.

Indices are `0`-based, so `β_m = (T_k)_{m+1, m}` is the entry of `T_k` that first sees the padding
of `z` by zeros, and `z_m` is the last component of `z`. -/
theorem persistence (h : m + 1 ≤ k) {θ : ℝ} {z : EuclideanSpace ℝ (Fin (m + 1))}
    (hz : ‖z‖ = 1) (hθ : Matrix.toEuclideanLin (tridiag A b (m + 1)) z = θ • z) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (tridiag A b k) ∧
      |μ - θ| ≤ beta A b m * |z (Fin.last m)| := by
  have hθ' : (tridiag A b (m + 1)).mulVec (WithLp.ofLp z) = θ • WithLp.ofLp z := by
    simpa [Matrix.toLpLin_apply] using congrArg WithLp.ofLp hθ
  obtain ⟨y, hy, hy0⟩ : ∃ y : Fin k → ℝ,
      (∀ j : Fin (m + 1), y (Fin.castLE h j) = WithLp.ofLp z j) ∧
        ∀ i : Fin k, m + 1 ≤ (i : ℕ) → y i = 0 :=
    ⟨fun i => if hi : (i : ℕ) < m + 1 then WithLp.ofLp z ⟨i, hi⟩ else 0,
      fun j => by
        dsimp only
        rw [dite_eq_left (by rw [Fin.val_castLE]; exact j.isLt)]
        simp,
      fun i hi => by
        dsimp only
        exact dite_eq_right (by omega)⟩
  have hnorm : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ = 1 := by
    have hsq : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 = 1 ^ 2 := by
      have e1 : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 =
          ∑ j : Fin (m + 1), WithLp.ofLp z j ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq,
          sum_eq_sum_castLE h _ fun i hi => by rw [WithLp.ofLp_toLp, hy0 i hi]; ring]
        exact Finset.sum_congr rfl fun j _ => by rw [WithLp.ofLp_toLp, hy]
      rw [e1, ← EuclideanSpace.real_norm_sq_eq z, hz]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 hsq
  have hres : ‖Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
      (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ≤
        beta A b m * |WithLp.ofLp z (Fin.last m)| := by
    have hcomp : ∀ i : Fin k, (Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
        (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))) i =
          if (i : ℕ) = m + 1 then beta A b m * WithLp.ofLp z (Fin.last m) else 0 := fun i => by
      rw [← mulVec_sub_smul A b h hy hy0 hθ' i]
      simp [Matrix.toLpLin_apply]
    have hsq : ‖Matrix.toEuclideanLin (tridiag A b k) (WithLp.toLp 2 y) -
        (θ : ℝ) • (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤
          (beta A b m * |WithLp.ofLp z (Fin.last m)|) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, mul_pow, sq_abs, ← mul_pow]
      simp only [hcomp]
      exact sum_ite_sq_le h _
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (beta_nonneg A b m) (abs_nonneg _))] at this
  obtain ⟨μ, hμ, hbound⟩ := (Matrix.isSymmetric_toEuclideanLin_iff.2
    (Matrix.isHermitian_iff_isSymm.2 (tridiag_isSymm A b k))).exists_hasEigenvalue_dist_le θ
      (norm_ne_zero_iff.1 (by rw [hnorm]; norm_num))
  refine ⟨μ, (Matrix.hasEigenvalue_toEuclideanLin_iff _ _).1 hμ, ?_⟩
  rw [hnorm, div_one] at hbound
  rw [← Real.norm_eq_abs]
  exact le_trans (by simpa using hbound) hres

end Persistence

end Lanczos
