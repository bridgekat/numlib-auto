/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.GramMatrix`, beside `Matrix.gram`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Gram determinants and the distance to the span of a finite family

Let `v : ι → E` be a finite family in an inner product space and let `f : E`. The **Gram
determinant** `det (Matrix.gram 𝕜 v)` of the family, and the Gram determinant of the family
enlarged by `f`, determine the distance from `f` to the span of `v`:

`‖f - starProjection (span 𝕜 (range v)) f‖ ^ 2 = det G(v, f) / det G(v)`,

the classical formula that reads a best-approximation error off two determinants. It is
`Submodule.norm_sub_starProjection_sq_eq_det_gram_div`, with the equivalent infimum form
`Submodule.iInf_norm_sub_sq_eq_det_gram_div` and the real-scalar restatements
`Submodule.norm_sub_starProjection_sq_eq_det_gram_div_real` and
`Submodule.iInf_norm_sub_sq_eq_det_gram_div_real`. Mathlib has `Matrix.gram` and its positive
semidefiniteness but no determinant formula of this kind.

## Main results

* `Matrix.gram_sum_smul`: `gram 𝕜 (fun j ↦ ∑ i, T i j • v i) = Tᴴ * gram 𝕜 v * T`, the behaviour
  of a Gram matrix under a linear change of the family.
* `Matrix.det_gram_sumElim`: the *product* form, valid with no hypothesis at all,
  `det G(v, f) = det G(v) * ‖f - P f‖ ^ 2` where `P` is the orthogonal projection onto the span
  of `v`.
* `Submodule.norm_sub_starProjection_sq_eq_det_gram_div` and
  `Submodule.iInf_norm_sub_sq_eq_det_gram_div`: the *quotient* form, for a linearly independent
  family, where the denominator is nonzero.
* `Matrix.det_gram_cons`: the same for a family indexed by `Fin n` and enlarged at the front by
  `Fin.cons`, which is the form a concrete family takes, together with the reindexing
  `Matrix.det_gram_sumElim_eq_det_gram_cons` between the two.

## Implementation notes

The enlarged family is `Sum.elim v (fun _ : Unit ↦ f) : ι ⊕ Unit → E`, so that its Gram matrix is
literally a `Matrix.fromBlocks` and no reindexing equivalence appears anywhere. This is the same
convention as `Mathlib.LinearAlgebra.Matrix.SchurComplement`.

The proof does not go through a Schur complement, although the quotient `det G(v, f) / det G(v)`
is one: it is the Schur complement of the `(1,1)` block of `G(v, f)`, a `1 × 1` matrix. Replacing
`f` by `g = f - P f` changes the enlarged family by a *unitriangular* change of basis `T` — add a
combination of the `v i` to the last vector — which leaves the determinant fixed by
`Matrix.gram_sum_smul`, and makes the enlarged Gram matrix block diagonal because `g` is orthogonal
to every `v i`. That is shorter than inverting `G(v)` and identifying the Schur complement with the
squared error through the normal equations, and it needs no hypothesis on `v`.

## References

* [F. R. Gantmacher, *The Theory of Matrices*, Volume 1, Chelsea, 1959], Chapter IX §5, where the
  formula is the recursion satisfied by the Gram determinants of a nested family.
* [K. Atkinson and W. Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
  edition, Springer, 2009], §3.1, where it is the engine of the Müntz–Szász theorem.
-/

open scoped InnerProductSpace

variable {ι κ E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The span of a family indexed by a finite type is finite-dimensional, hence has an orthogonal
projection.

Mathlib has this instance for the span of a `Finset` (`FiniteDimensional.span_finset`) and for a
single vector, but not for the range of a family indexed by a finite type. -/
instance Submodule.hasOrthogonalProjection_span_range [Finite ι] (v : ι → E) :
    (Submodule.span 𝕜 (Set.range v)).HasOrthogonalProjection :=
  haveI := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  inferInstance

namespace Matrix

/-- The Gram matrix of a family of linear combinations `w j = ∑ i, T i j • v i` is
`Tᴴ * gram 𝕜 v * T`. -/
theorem gram_sum_smul [Fintype ι] (v : ι → E) (T : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j ↦ ∑ i, T i j • v i) = Tᴴ * gram 𝕜 v * T := by
  ext j k
  rw [gram_apply, ← star_dotProduct_gram_mulVec v (fun i ↦ T i j) (fun i ↦ T i k),
    Matrix.mul_assoc]
  simp [dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Finset.mul_sum]

/-- Adjoining a vector orthogonal to every member of a family makes the Gram matrix block
diagonal. -/
theorem gram_sumElim_of_inner_eq_zero (v : ι → E) {g : E} (hg : ∀ i, ⟪v i, g⟫_𝕜 = 0) :
    gram 𝕜 (Sum.elim v fun _ : Unit ↦ g)
      = fromBlocks (gram 𝕜 v) 0 0 (of fun _ _ ↦ ⟪g, g⟫_𝕜) := by
  ext i j
  cases i <;> cases j <;> simp [gram_apply, hg, inner_eq_zero_symm.2 (hg _)]

section Adjoin

variable [Fintype ι] [DecidableEq ι]

/-- Adjoining a vector orthogonal to every member of a family multiplies the Gram determinant by
its squared norm. -/
theorem det_gram_sumElim_of_inner_eq_zero (v : ι → E) {g : E} (hg : ∀ i, ⟪v i, g⟫_𝕜 = 0) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ g)).det = (gram 𝕜 v).det * ⟪g, g⟫_𝕜 := by
  rw [gram_sumElim_of_inner_eq_zero v hg, det_fromBlocks_zero₂₁,
    det_unique (of fun _ _ ↦ ⟪g, g⟫_𝕜 : Matrix Unit Unit 𝕜), of_apply]

/-- **Gram's determinant formula for the distance to a span**, product form.

Adjoining `f` to a finite family `v` multiplies the Gram determinant by the squared distance from
`f` to the span of `v`, that distance being realized by the orthogonal projection. No hypothesis on
`v` is needed: if `v` is linearly dependent both sides vanish. -/
theorem det_gram_sumElim (v : ι → E) (f : E) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det
      = (gram 𝕜 v).det * (‖f - (Submodule.span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2 := by
  set K := Submodule.span 𝕜 (Set.range v) with hK
  set g := f - K.starProjection f with hgdef
  have hg : ∀ i, ⟪v i, g⟫_𝕜 = 0 := fun i ↦
    (Submodule.mem_orthogonal K g).1 (K.sub_starProjection_mem_orthogonal f) (v i)
      (Submodule.subset_span (Set.mem_range_self i))
  obtain ⟨a, ha⟩ : ∃ a : ι → 𝕜, ∑ i, a i • v i = K.starProjection f :=
    (Submodule.mem_span_range_iff_exists_fun 𝕜).1 (K.starProjection_apply_mem f)
  set T : Matrix (ι ⊕ Unit) (ι ⊕ Unit) 𝕜 := fromBlocks 1 (of fun i (_ : Unit) ↦ a i) 0 1 with hT
  have key : (Sum.elim v fun _ : Unit ↦ f)
      = fun j ↦ ∑ i, T i j • (Sum.elim v fun _ : Unit ↦ g) i := by
    funext j
    rw [Fintype.sum_sum_type]
    cases j with
    | inl i₀ => simp [hT, Matrix.one_apply]
    | inr u => simp [hT, ha, hgdef]
  have hdetT : T.det = 1 := by rw [hT, det_fromBlocks_zero₂₁, det_one, det_one, one_mul]
  rw [key, gram_sum_smul, det_mul, det_mul, det_conjTranspose, hdetT, star_one, one_mul, mul_one,
    det_gram_sumElim_of_inner_eq_zero v hg, inner_self_eq_norm_sq_to_K]

end Adjoin

section Cons

/-- The equivalence `Fin (n + 1) ≃ Fin n ⊕ Unit` that sends `0` to the `Unit` summand and `i + 1`
to `i`. It carries `Sum.elim v (fun _ ↦ f)` to `Fin.cons f v`. -/
private def finSuccEquivSumUnit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit where
  toFun := Fin.cases (Sum.inr ()) Sum.inl
  invFun := Sum.elim Fin.succ fun _ ↦ 0
  left_inv i := by induction i using Fin.cases <;> simp
  right_inv x := by rcases x with i | ⟨⟩ <;> simp

/-- The two ways of enlarging a `Fin n`-indexed family by one vector — as a `Sum.elim` over
`Fin n ⊕ Unit`, or as a `Fin.cons` over `Fin (n + 1)` — have the same Gram determinant. -/
theorem det_gram_sumElim_eq_det_gram_cons {n : ℕ} (v : Fin n → E) (f : E) :
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det
      = (gram 𝕜 (Fin.cons f v : Fin (n + 1) → E)).det := by
  rw [← det_submatrix_equiv_self (finSuccEquivSumUnit n)
    (gram 𝕜 (Sum.elim v fun _ : Unit ↦ f))]
  congr 1
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp [finSuccEquivSumUnit]

/-- **Gram's determinant formula for the distance to a span**, product form, for a family indexed
by `Fin n` enlarged at the front. -/
theorem det_gram_cons {n : ℕ} (v : Fin n → E) (f : E) :
    (gram 𝕜 (Fin.cons f v : Fin (n + 1) → E)).det
      = (gram 𝕜 v).det * (‖f - (Submodule.span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2 := by
  rw [← det_gram_sumElim_eq_det_gram_cons, det_gram_sumElim]

end Cons

end Matrix

namespace Submodule

variable [Fintype ι] [DecidableEq ι]

/-- **Gram's determinant formula for the distance to a span**, quotient form.

For a linearly independent family `v` the squared distance from `f` to the span of `v` is the
quotient of the Gram determinant of `v` enlarged by `f` and the Gram determinant of `v`. -/
theorem norm_sub_starProjection_sq_eq_det_gram_div {v : ι → E} (hv : LinearIndependent 𝕜 v)
    (f : E) :
    (‖f - (span 𝕜 (Set.range v)).starProjection f‖ : 𝕜) ^ 2
      = (Matrix.gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram 𝕜 v).det :=
  (eq_div_iff (Matrix.det_gram_ne_zero_iff_linearIndependent.2 hv)).2
    (by rw [Matrix.det_gram_sumElim, mul_comm])

/-- **Gram's determinant formula for the distance to a span** in a real inner product space:
the quotient form, with the distance to the span written through the orthogonal projection. -/
theorem norm_sub_starProjection_sq_eq_det_gram_div_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : ι → E} (hv : LinearIndependent ℝ v) (f : E) :
    ‖f - (span ℝ (Set.range v)).starProjection f‖ ^ 2
      = (Matrix.gram ℝ (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram ℝ v).det :=
  norm_sub_starProjection_sq_eq_det_gram_div hv f

/-- **Gram's determinant formula for the distance to a span**, quotient form, with the distance
written as an infimum. -/
theorem iInf_norm_sub_sq_eq_det_gram_div {v : ι → E} (hv : LinearIndependent 𝕜 v) (f : E) :
    ((⨅ x : span 𝕜 (Set.range v), ‖f - (x : E)‖ : ℝ) : 𝕜) ^ 2
      = (Matrix.gram 𝕜 (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram 𝕜 v).det := by
  rw [← starProjection_minimal, norm_sub_starProjection_sq_eq_det_gram_div hv]

/-- **Gram's determinant formula for the distance to a span** in a real inner product space: the
squared distance from `f` to the span of a linearly independent family `v` is the quotient of the
Gram determinant of `v` enlarged by `f` and the Gram determinant of `v`. -/
theorem iInf_norm_sub_sq_eq_det_gram_div_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : ι → E} (hv : LinearIndependent ℝ v) (f : E) :
    (⨅ x : span ℝ (Set.range v), ‖f - (x : E)‖) ^ 2
      = (Matrix.gram ℝ (Sum.elim v fun _ : Unit ↦ f)).det / (Matrix.gram ℝ v).det :=
  iInf_norm_sub_sq_eq_det_gram_div hv f

end Submodule
