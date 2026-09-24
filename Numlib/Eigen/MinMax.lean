import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# Courant–Fischer: the variational characterization of eigenvalues

The eigenvalues of a symmetric operator `T` on a finite-dimensional inner product space, sorted in
decreasing order as `hT.eigenvalues hn : Fin n → ℝ`, are the max–min and min–max values of the
Rayleigh quotient `T.rayleighQuotient x = re ⟪T x, x⟫ / ‖x‖ ^ 2` over subspaces: `λ i` is the
largest number that bounds the Rayleigh quotient from below on some subspace of dimension `i + 1`,
and the smallest number that bounds it from above on some subspace of dimension `n - i`. This is the
min–max theorem of Courant, Fischer, Poincaré and Weyl, stated as the two formulas of
[saad2011numerical], Thm 1.9, and as [kress1998numerical], Thm 7.4.  Mathlib has only the two
extreme eigenvalues, through `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and its
`iInf` twin.

Both books index the eigenvalues from `1` in decreasing order, so their `λ_k` is `hT.eigenvalues hn
i` for `i = k - 1`, and their subspace dimensions `k` and `n + 1 - k` read here as `i + 1` and `n -
i`.

## Main results

* `LinearMap.IsSymmetric.exists_mem_ne_zero_rayleighQuotient_le` and
  `LinearMap.IsSymmetric.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic`: the two directions. Every
  subspace of dimension at least `i + 1` carries a nonzero vector whose Rayleigh quotient is at most
  `λ i`, by the dimension count `(i + 1) + (n - i) > n` against the span of the eigenvectors for the
  eigenvalues from the `i`-th on; and `λ i` is a lower bound for the Rayleigh quotient on the span
  of the eigenvectors for the `i + 1` largest eigenvalues, which has dimension `i + 1`.  These two
  statements are what a consumer usually wants.
* `LinearMap.IsSymmetric.isGreatest_eigenvalues` and `LinearMap.IsSymmetric.isLeast_eigenvalues`:
  the same, as an `IsGreatest`/`IsLeast` over an explicit set of reals, with no junk values.
* `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf` and
  `LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup`: the classical `max min` and `min max` formulas.
* `LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`: Rayleigh's recursive form, the
  maximum over the vectors orthogonal to the `i` leading eigenvectors.
* `LinearMap.IsSymmetric.abs_eigenvalues_sub_le`: Weyl's inequality, one eigenvalue index at a time,
  and its two-sided form `LinearMap.IsSymmetric.eigenvalues_add_mem_Icc`,
  `λ_i(A) + λ_min(E) ≤ λ_i(A + E) ≤ λ_i(A) + λ_max(E)` ([golub2013matrix] Theorem 8.1.5).
* `LinearMap.IsSymmetric.eigenvalues_interlace_of_linearIsometry` and its two faces
  `LinearMap.IsSymmetric.eigenvalues_restrict_interlace` (a subspace) and
  `Matrix.IsHermitian.eigenvalues₀_submatrix_interlace` (a principal submatrix): Cauchy interlacing,
  `λ_{i + (n - m)}(T) ≤ λ_i(S) ≤ λ_i(T)` whenever the quadratic form of `S` on an `m`-dimensional
  space is that of `T` pulled back along a linear isometry.
* `LinearMap.IsSymmetric.eigenvalues_le_of_finrank_range_sub_le`: low-rank interlacing, a
  perturbation of rank at most `r` moves every eigenvalue by at most `r` places,
  `λ_{i+r}(B) ≤ λ_i(A)`; with a positive perturbation this is
  `LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le`
  ([golub2013matrix] Theorem 8.1.8 at `r = 1`).
* `LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues` and
  `LinearMap.IsSymmetric.sum_eigenvalues_le_sum_re_inner`: Ky Fan's maximum and minimum principles,
  `∑_{i<k} λ_{n-k+i} ≤ ∑_{i<k} re ⟪T x_i, x_i⟫ ≤ ∑_{i<k} λ_i` for an orthonormal family `x`. The sum
  is the trace of the compression of `T` to the span of the family, and each eigenvalue of the
  compression is bounded by Cauchy interlacing. They are the one source of the trace-maximization
  results: the trace inequality `LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul`
  (`re tr(A B) ≤ ∑ λ_i(A) λ_i(B)`, by Abel summation over the eigenvectors of `B`) and the
  **Hoffman–Wielandt inequality** `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le`, with its
  matrix form `Matrix.IsHermitian.hoffman_wielandt`, `∑ (λ_k(A) - λ_k(B))² ≤ ‖A - B‖_F²`
  ([golub2013matrix] Theorem 8.1.4).
* `Matrix.IsHermitian.sortedEigenvalues`: the eigenvalues of a Hermitian matrix of order `n`, sorted
  decreasingly and indexed by `Fin n` (Mathlib's `eigenvalues₀` reindexed), with Cauchy interlacing
  for the leading principal submatrix,
  `Matrix.IsHermitian.sortedEigenvalues_submatrix_castSucc_interlace`, and the sorted spectral
  decomposition `Matrix.IsHermitian.exists_unitary_conj_eq_diagonal_eigenvalues₀`
  (`Uᴴ A U = diag(λ_1 ≥ ⋯ ≥ λ_n)`, [golub2013matrix] Theorem 8.1.1).
* `ContinuousLinearMap.hasGradientAt_rayleighQuotient`: the gradient of the Rayleigh quotient,
  `∇r(x) = 2 (T x - r(x) x) / ‖x‖²` ([golub2013matrix] (10.1.1)); hence
  `LinearMap.IsSymmetric.hasFDerivAt_rayleighQuotient_eq_zero_iff`, the stationary points of the
  Rayleigh quotient are exactly the eigenvectors ([golub2013matrix] (12.5.23)). Mathlib has only
  the extremal case, `IsSelfAdjoint.hasEigenvector_of_isLocalExtrOn`.
* `LinearMap.IsSymmetric.eigenvalues_neg`: the eigenvalues of `-T` are the negatives of those of
  `T` in reversed order, which is the reduction that turns any statement about a largest eigenvalue
  into the matching statement about a smallest one; `exists_smul_eigenvectorBasis_neg` transports
  the eigenvector as well, at a simple eigenvalue.

## Implementation notes

The `⨆`/`⨅` forms quantify over *subtypes*, `{S : Submodule 𝕜 E // finrank 𝕜 S = i + 1}` and `{x : E
// x ∈ S ∧ x ≠ 0}`, rather than over all subspaces and all vectors with a nested `⨆ _ : P, ·`.  The
latter is junk: an `iSup` over a false proposition is `sSup ∅ = 0` in `ℝ`, so it would silently
truncate the statement at `0`.  The `IsGreatest` and `IsLeast` forms carry no `iSup` at all and are
the recommended interface.

Weyl's inequality is stated with a hypothesised bound `∀ x, ‖(A - B) x‖ ≤ C * ‖x‖` rather than with
an operator norm, because `E →ₗ[𝕜] E` carries no norm and the hypothesised form does not force a
topology on the consumer.  `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm` is the corollary
for continuous linear maps.  Its workhorse `LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le`
is weaker still: it asks only for the quadratic-form bound `re ⟪A x, x⟫ ≤ re ⟪B x, x⟫ + C ‖x‖ ^ 2`
that [kress1998numerical] proof actually uses, which is the form this library prefers for spectral
hypotheses.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two subspaces whose dimensions add up to more than the dimension of the ambient space meet in a
nonzero vector.  This is the dimension count behind Courant–Fischer. -/
theorem Submodule.exists_mem_inf_ne_zero {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S W : Submodule K V}
    (h : Module.finrank K V < Module.finrank K S + Module.finrank K W) :
    ∃ x ∈ S ⊓ W, x ≠ 0 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hle : Module.finrank K (S ⊔ W : Submodule K V) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  have hpos : 0 < Module.finrank K (S ⊓ W : Submodule K V) := by omega
  have : Nontrivial (S ⊓ W : Submodule K V) := Module.finrank_pos_iff.mp hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : (S ⊓ W : Submodule K V))
  exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0)⟩

namespace LinearMap

/-- The *Rayleigh quotient* of a linear map `T` (over `ℝ` or `ℂ`) at a vector `x` is the real number
`re ⟪T x, x⟫ / ‖x‖ ^ 2`.  This is the `LinearMap` twin of `ContinuousLinearMap.rayleighQuotient`;
the two agree by `ContinuousLinearMap.rayleighQuotient_eq_toLinearMap`. -/
noncomputable abbrev rayleighQuotient (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner 𝕜 (T x) x) / ‖x‖ ^ 2

/-- The Rayleigh quotient is a junk `0` at the zero vector, where the quotient `0 / 0` is not
meaningful; every statement below excludes `x = 0` explicitly. -/
@[simp]
theorem rayleighQuotient_apply_zero (T : E →ₗ[𝕜] E) : T.rayleighQuotient 0 = 0 := by
  simp [rayleighQuotient]

/-- At a unit vector the Rayleigh quotient is just the quadratic form, which is how the approximate
eigenpairs of `Numlib.Eigen.Perturbation` are stated. -/
theorem rayleighQuotient_of_norm_eq_one (T : E →ₗ[𝕜] E) {x : E} (hx : ‖x‖ = 1) :
    T.rayleighQuotient x = RCLike.re (inner 𝕜 (T x) x) := by
  rw [rayleighQuotient, hx, one_pow, div_one]

/-- The Rayleigh quotient is invariant under rescaling, so a bound at a nonzero vector transfers to
its normalization. -/
theorem rayleighQuotient_smul (T : E →ₗ[𝕜] E) (x : E) {c : 𝕜} (hc : c ≠ 0) :
    T.rayleighQuotient (c • x) = T.rayleighQuotient x := by
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  rw [rayleighQuotient, rayleighQuotient, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, norm_smul, mul_pow,
    mul_div_mul_left _ _ hc2]

/-- The Rayleigh quotient is additive in the operator. -/
theorem rayleighQuotient_sub (A B : E →ₗ[𝕜] E) (x : E) :
    (A - B).rayleighQuotient x = A.rayleighQuotient x - B.rayleighQuotient x := by
  rw [rayleighQuotient, rayleighQuotient, rayleighQuotient, sub_apply, inner_sub_left, map_sub,
    sub_div]

/-- The Rayleigh quotient of `-T` is the negative of that of `T`.  This is what exchanges the
max–min and min–max characterizations of the eigenvalues (`IsSymmetric.eigenvalues_neg`). -/
theorem rayleighQuotient_neg (T : E →ₗ[𝕜] E) (x : E) :
    (-T).rayleighQuotient x = -T.rayleighQuotient x := by
  simp [LinearMap.rayleighQuotient, inner_neg_left, neg_div]

/-- The negative of a symmetric operator is symmetric.  The companion of Mathlib's
`LinearMap.IsSymmetric.add`, `sub` and `smul`. -/
theorem IsSymmetric.neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (-T).IsSymmetric := fun x y => by
  simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, hT x y]

end LinearMap

/-- The Rayleigh quotient of a continuous linear map is the Rayleigh quotient of the underlying
linear map. -/
theorem ContinuousLinearMap.rayleighQuotient_eq_toLinearMap (T : E →L[𝕜] E) (x : E) :
    T.rayleighQuotient x = (T : E →ₗ[𝕜] E).rayleighQuotient x :=
  rfl

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-! ### The eigenbasis expansion

Every statement below is read off the coordinates of a vector in the orthonormal eigenvector basis
`hT.eigenvectorBasis hn`, in which the norm and the quadratic form are the two sums here. -/

/-- Parseval's identity in the eigenvector basis. -/
theorem norm_sq_eq_sum_norm_repr_sq (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using
    ((hT.eigenvectorBasis hn).sum_sq_norm_inner_right x).symm

/-- The quadratic form of a symmetric operator, in the coordinates of its eigenvector basis. -/
theorem re_inner_apply_self_eq_sum (x : E) :
    RCLike.re (inner 𝕜 (T x) x) =
      ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner (T x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT x (hT.eigenvectorBasis hn i), hT.apply_eigenvectorBasis hn, inner_smul_right,
    ← inner_conj_symm x (hT.eigenvectorBasis hn i), mul_assoc, RCLike.conj_mul,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- The quadratic form of the shift `c - T` in the eigenvector basis: `c ‖x‖² - re ⟪T x, x⟫ = ∑ i,
(c - λ i) ‖⟪v i, x⟫‖²`.  This is the form in which an eigenvalue minus a Rayleigh quotient is
estimated, one eigenbasis coordinate at a time. -/
theorem mul_norm_sq_sub_re_inner_eq_sum (c : ℝ) (x : E) :
    c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x) =
      ∑ i, (c - hT.eigenvalues hn i) * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [hT.norm_sq_eq_sum_norm_repr_sq hn, hT.re_inner_apply_self_eq_sum hn, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The vectors of an eigenvector basis are nonzero, being unit vectors. -/
theorem eigenvectorBasis_ne_zero (i : Fin n) : hT.eigenvectorBasis hn i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [(hT.eigenvectorBasis hn).norm_eq_one i]; norm_num)

/-- The Rayleigh quotient at an eigenvector of the eigenvector basis is its eigenvalue. -/
@[simp]
theorem rayleighQuotient_eigenvectorBasis (i : Fin n) :
    T.rayleighQuotient (hT.eigenvectorBasis hn i) = hT.eigenvalues hn i := by
  rw [T.rayleighQuotient_of_norm_eq_one ((hT.eigenvectorBasis hn).norm_eq_one i),
    hT.apply_eigenvectorBasis hn, inner_smul_left, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).norm_eq_one i]
  simp

/-! ### Spans of eigenvectors -/

/-- The span of the eigenvectors of `T` indexed by `s`, taken in the orthonormal eigenvector basis
`hT.eigenvectorBasis hn` whose eigenvalues `hT.eigenvalues hn` decrease.  The two cases used by
Courant–Fischer are `s = Finset.Iic i`, the eigenvectors for the `i + 1` largest eigenvalues, and `s
= Finset.Ici i`, the eigenvectors for the `n - i` smallest ones. -/
noncomputable def eigenvectorSpan (s : Finset (Fin n)) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (hT.eigenvectorBasis hn '' s)

/-- Each of the spanning eigenvectors lies in the span. -/
theorem eigenvectorBasis_mem_eigenvectorSpan {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- A vector lies in `hT.eigenvectorSpan hn s` exactly when its eigenbasis coordinates vanish
outside `s`. -/
theorem mem_eigenvectorSpan_iff {s : Finset (Fin n)} {x : E} :
    x ∈ hT.eigenvectorSpan hn s ↔ ∀ i ∉ s, (hT.eigenvectorBasis hn).repr x i = 0 := by
  rw [eigenvectorSpan, ← (hT.eigenvectorBasis hn).coe_toBasis,
    (hT.eigenvectorBasis hn).toBasis.mem_span_image, Finsupp.support_subset_iff]
  simp only [Finset.mem_coe, OrthonormalBasis.coe_toBasis_repr_apply]

/-- The eigenvectors span the whole space. -/
@[simp]
theorem eigenvectorSpan_univ : hT.eigenvectorSpan hn Finset.univ = ⊤ :=
  eq_top_iff.mpr fun _x _ => (hT.mem_eigenvectorSpan_iff hn).mpr fun i hi =>
    absurd (Finset.mem_univ i) hi

/-- The span of `s.card` eigenvectors has dimension `s.card`, the eigenvector basis being
orthonormal and hence linearly independent.  This is the dimension bookkeeping of Courant–Fischer.
-/
theorem finrank_eigenvectorSpan (s : Finset (Fin n)) :
    Module.finrank 𝕜 (hT.eigenvectorSpan hn s) = s.card := by
  have hli : LinearIndependent 𝕜 fun j : (s : Set (Fin n)) => hT.eigenvectorBasis hn j :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [eigenvectorSpan, Set.image_eq_range, finrank_span_eq_card hli]
  simp

/-! ### Bounds on the Rayleigh quotient over a span of eigenvectors -/

/-- On the span of the eigenvectors indexed by `s`, the quadratic form is bounded above by any upper
bound for the eigenvalues indexed by `s`. -/
theorem re_inner_apply_self_le_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s) :
    RCLike.re (inner 𝕜 (T x) x) ≤ c * ‖x‖ ^ 2 := by
  rw [hT.re_inner_apply_self_eq_sum hn, hT.norm_sq_eq_sum_norm_repr_sq hn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i hi]
    simp

/-- On the span of the eigenvectors indexed by `s`, the quadratic form is bounded below by any lower
bound for the eigenvalues indexed by `s`. -/
theorem le_re_inner_apply_self_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
  rw [hT.re_inner_apply_self_eq_sum hn, hT.norm_sq_eq_sum_norm_repr_sq hn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i hi]
    simp

/-- The Rayleigh quotient form of `re_inner_apply_self_le_of_mem_eigenvectorSpan`. -/
theorem rayleighQuotient_le_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s)
    (hx0 : x ≠ 0) : T.rayleighQuotient x ≤ c := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  rw [LinearMap.rayleighQuotient, div_le_iff₀ hpos]
  exact hT.re_inner_apply_self_le_of_mem_eigenvectorSpan hn hc hx

/-- The Rayleigh quotient form of `le_re_inner_apply_self_of_mem_eigenvectorSpan`. -/
theorem le_rayleighQuotient_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s)
    (hx0 : x ≠ 0) : c ≤ T.rayleighQuotient x := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  rw [LinearMap.rayleighQuotient, le_div_iff₀ hpos]
  exact hT.le_re_inner_apply_self_of_mem_eigenvectorSpan hn hc hx

/-- Any upper bound for the eigenvalues bounds every Rayleigh quotient. -/
theorem rayleighQuotient_le_of_forall {c : ℝ} (hc : ∀ i, hT.eigenvalues hn i ≤ c) {x : E}
    (hx0 : x ≠ 0) : T.rayleighQuotient x ≤ c :=
  hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn (fun i _ => hc i)
    (by rw [hT.eigenvectorSpan_univ hn]; trivial) hx0

/-- Any lower bound for the eigenvalues bounds every Rayleigh quotient. -/
theorem le_rayleighQuotient_of_forall {c : ℝ} (hc : ∀ i, c ≤ hT.eigenvalues hn i) {x : E}
    (hx0 : x ≠ 0) : c ≤ T.rayleighQuotient x :=
  hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn (fun i _ => hc i)
    (by rw [hT.eigenvectorSpan_univ hn]; trivial) hx0

/-- The Rayleigh quotient of a nonzero vector lies between the extreme eigenvalues. -/
theorem rayleighQuotient_mem_Icc {m : ℕ} (hn : Module.finrank 𝕜 E = m + 1) {x : E} (hx0 : x ≠ 0) :
    T.rayleighQuotient x ∈
      Set.Icc (hT.eigenvalues hn (Fin.last m)) (hT.eigenvalues hn 0) :=
  ⟨hT.le_rayleighQuotient_of_forall hn (fun i => hT.eigenvalues_antitone hn (Fin.le_last i)) hx0,
    hT.rayleighQuotient_le_of_forall hn
      (fun i => hT.eigenvalues_antitone hn (Fin.zero_le i)) hx0⟩

/-! ### The two directions of Courant–Fischer -/

/-- **Courant–Fischer, first direction.** Every subspace of dimension at least `i + 1` carries a
nonzero vector whose Rayleigh quotient is at most the `i`-th eigenvalue.  The proof is the dimension
count `(i + 1) + (n - i) > n` against the span of the eigenvectors for the eigenvalues from the
`i`-th on. -/
theorem exists_mem_ne_zero_rayleighQuotient_le (i : Fin n) {S : Submodule 𝕜 E}
    (hS : (i : ℕ) + 1 ≤ Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ T.rayleighQuotient x ≤ hT.eigenvalues hn i := by
  have hi := i.isLt
  have hW : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) = n - (i : ℕ) := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  have hlt : Module.finrank 𝕜 E <
      Module.finrank 𝕜 S + Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) := by
    rw [hn, hW]; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_inf_ne_zero hlt
  exact ⟨x, hx.1, hx0, hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj)) hx.2 hx0⟩

/-- **Courant–Fischer, first direction, dual form.** Every subspace of dimension at least `n - i`
carries a nonzero vector whose Rayleigh quotient is at least the `i`-th eigenvalue. -/
theorem exists_mem_ne_zero_le_rayleighQuotient (i : Fin n) {S : Submodule 𝕜 E}
    (hS : n - (i : ℕ) ≤ Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ hT.eigenvalues hn i ≤ T.rayleighQuotient x := by
  have hi := i.isLt
  have hW : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hlt : Module.finrank 𝕜 E <
      Module.finrank 𝕜 S + Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) := by
    rw [hn, hW]; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_inf_ne_zero hlt
  exact ⟨x, hx.1, hx0, hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj)) hx.2 hx0⟩

/-- **Courant–Fischer, second direction.** The `i`-th eigenvalue bounds the Rayleigh quotient from
below throughout the span of the eigenvectors for the `i + 1` largest eigenvalues, a subspace of
dimension `i + 1`; this is where the max–min is attained. -/
theorem le_rayleighQuotient_of_mem_eigenvectorSpan_Iic (i : Fin n) {x : E}
    (hx : x ∈ hT.eigenvectorSpan hn (Finset.Iic i)) (hx0 : x ≠ 0) :
    hT.eigenvalues hn i ≤ T.rayleighQuotient x :=
  hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj)) hx hx0

/-- **Courant–Fischer, second direction, dual form.** The `i`-th eigenvalue bounds the Rayleigh
quotient from above throughout the span of the eigenvectors for the `n - i` smallest eigenvalues, a
subspace of dimension `n - i`; this is where the min–max is attained. -/
theorem rayleighQuotient_le_of_mem_eigenvectorSpan_Ici (i : Fin n) {x : E}
    (hx : x ∈ hT.eigenvectorSpan hn (Finset.Ici i)) (hx0 : x ≠ 0) :
    T.rayleighQuotient x ≤ hT.eigenvalues hn i :=
  hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj)) hx hx0

/-- A vector is orthogonal to the eigenvectors for the `i` eigenvalues before the `i`-th exactly
when it lies in the span of the eigenvectors from the `i`-th on.  This identifies the subspace of
Rayleigh's recursive characterization with a span of eigenvectors. -/
theorem mem_eigenvectorSpan_Ici_iff {i : Fin n} {x : E} :
    x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ↔
      ∀ j < i, inner 𝕜 (hT.eigenvectorBasis hn j) x = 0 := by
  rw [hT.mem_eigenvectorSpan_iff hn]
  simp only [Finset.mem_Ici, not_le, OrthonormalBasis.repr_apply_apply]

/-! ### Courant–Fischer -/

/-- **Courant–Fischer, max–min form**, as an `IsGreatest` over an explicit set of reals: the `i`-th
eigenvalue in decreasing order is the largest number that bounds the Rayleigh quotient from below on
some subspace of dimension `i + 1`.  This is the second formula of [saad2011numerical], Thm 1.9.
The form carries no `iSup`, hence no junk value. -/
theorem isGreatest_eigenvalues (i : Fin n) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = (i : ℕ) + 1 ∧
      ∀ x ∈ S, x ≠ 0 → c ≤ T.rayleighQuotient x} (hT.eigenvalues hn i) := by
  refine ⟨⟨hT.eigenvectorSpan hn (Finset.Iic i), ?_,
    fun x hx hx0 => hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i hx hx0⟩, ?_⟩
  · rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  · rintro c ⟨S, hS, hc⟩
    obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_rayleighQuotient_le hn i hS.ge
    exact (hc x hxS hx0).trans hxle

/-- **Courant–Fischer, min–max form**, as an `IsLeast` over an explicit set of reals: the `i`-th
eigenvalue in decreasing order is the smallest number that bounds the Rayleigh quotient from above
on some subspace of dimension `n - i`.  This is the first formula of [saad2011numerical], Thm 1.9,
and [kress1998numerical], Thm 7.4.  The form carries no `iInf`, hence no junk value. -/
theorem isLeast_eigenvalues (i : Fin n) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - (i : ℕ) ∧
      ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} (hT.eigenvalues hn i) := by
  refine ⟨⟨hT.eigenvectorSpan hn (Finset.Ici i), ?_,
    fun x hx hx0 => hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i hx hx0⟩, ?_⟩
  · rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  · rintro c ⟨S, hS, hc⟩
    obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_le_rayleighQuotient hn i hS.ge
    exact hxle.trans (hc x hxS hx0)

/-- **Courant–Fischer, max–min form** ([saad2011numerical], Thm 1.9, second formula).  The `i`-th
eigenvalue in decreasing order is the maximum over subspaces of dimension `i + 1` of the minimum of
the Rayleigh quotient on the subspace. `LinearMap.IsSymmetric.isGreatest_eigenvalues` is the same
statement without an `iSup`. -/
theorem eigenvalues_eq_iSup_iInf (i : Fin n) :
    hT.eigenvalues hn i =
      ⨆ S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = (i : ℕ) + 1},
        ⨅ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E) := by
  have hlow : ∀ j, Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn) ≤
      hT.eigenvalues hn j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hbdd : ∀ S : Submodule 𝕜 E, BddBelow
      (Set.range fun x : {x : E // x ∈ S ∧ x ≠ 0} => T.rayleighQuotient (x : E)) := by
    refine fun S => ⟨Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hT.le_rayleighQuotient_of_forall hn hlow x.2.2
  have hcard : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hmem : hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn (Finset.Iic i) :=
    hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Iic.mpr le_rfl)
  have hattain : ⨅ x : {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Iic i) ∧ x ≠ 0},
      T.rayleighQuotient (x : E) = hT.eigenvalues hn i := by
    have : Nonempty {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Iic i) ∧ x ≠ 0} :=
      ⟨⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩⟩
    refine le_antisymm ?_ (le_ciInf fun x =>
      hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i x.2.1 x.2.2)
    simpa using ciInf_le (hbdd _) ⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩
  refine (IsGreatest.csSup_eq (s := Set.range
    fun S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = (i : ℕ) + 1} =>
      ⨅ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E))
    ⟨⟨⟨_, hcard⟩, hattain⟩, ?_⟩).symm
  rintro _ ⟨S, rfl⟩
  obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_rayleighQuotient_le hn i S.2.ge
  exact (ciInf_le (hbdd _) ⟨x, hxS, hx0⟩).trans hxle

/-- **Courant–Fischer, min–max form** ([saad2011numerical], Thm 1.9, first formula;
[kress1998numerical], Thm 7.4).  The `i`-th eigenvalue in decreasing order is the minimum over
subspaces of dimension `n - i` (that is, of codimension `i`) of the maximum of the Rayleigh quotient
on the subspace. `LinearMap.IsSymmetric.isLeast_eigenvalues` is the same statement without an
`iInf`. -/
theorem eigenvalues_eq_iInf_iSup (i : Fin n) :
    hT.eigenvalues hn i =
      ⨅ S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = n - (i : ℕ)},
        ⨆ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E) := by
  have hupp : ∀ j, hT.eigenvalues hn j ≤
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn) :=
    fun j => Finset.le_sup' _ (Finset.mem_univ j)
  have hbdd : ∀ S : Submodule 𝕜 E, BddAbove
      (Set.range fun x : {x : E // x ∈ S ∧ x ≠ 0} => T.rayleighQuotient (x : E)) := by
    refine fun S => ⟨Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hT.rayleighQuotient_le_of_forall hn hupp x.2.2
  have hcard : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) = n - (i : ℕ) := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  have hmem : hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn (Finset.Ici i) :=
    hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Ici.mpr le_rfl)
  have hattain : ⨆ x : {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ∧ x ≠ 0},
      T.rayleighQuotient (x : E) = hT.eigenvalues hn i := by
    have : Nonempty {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ∧ x ≠ 0} :=
      ⟨⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩⟩
    refine le_antisymm (ciSup_le fun x =>
      hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i x.2.1 x.2.2) ?_
    simpa using le_ciSup (hbdd _) ⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩
  refine (IsLeast.csInf_eq (s := Set.range
    fun S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = n - (i : ℕ)} =>
      ⨆ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E))
    ⟨⟨⟨_, hcard⟩, hattain⟩, ?_⟩).symm
  rintro _ ⟨S, rfl⟩
  obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_le_rayleighQuotient hn i S.2.ge
  exact hxle.trans (le_ciSup (hbdd _) ⟨x, hxS, hx0⟩)

/-- **Rayleigh's recursive characterization** ([saad2011numerical], Thm 1.10; [kress1998numerical],
Thm 7.3): the `i`-th eigenvalue is the greatest Rayleigh quotient among the nonzero vectors
orthogonal to the eigenvectors for the `i` preceding eigenvalues, and it is attained at the `i`-th
eigenvector.  For `i = 0` the orthogonality condition is vacuous and this is the largest eigenvalue
as a global maximum.

Unlike the min–max form it needs the eigenvectors for the larger eigenvalues, which is why the
min–max form is the one used for a priori bounds. -/
theorem isGreatest_rayleighQuotient_orthogonal (i : Fin n) :
    IsGreatest {c : ℝ | ∃ x : E, x ≠ 0 ∧
      (∀ j < i, inner 𝕜 (hT.eigenvectorBasis hn j) x = 0) ∧ T.rayleighQuotient x = c}
      (hT.eigenvalues hn i) := by
  constructor
  · exact ⟨hT.eigenvectorBasis hn i, hT.eigenvectorBasis_ne_zero hn i,
      fun _j hj => (hT.eigenvectorBasis hn).inner_eq_zero hj.ne,
      hT.rayleighQuotient_eigenvectorBasis hn i⟩
  · rintro c ⟨x, hx0, hxorth, rfl⟩
    exact hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i
      ((hT.mem_eigenvectorSpan_Ici_iff hn).mpr hxorth) hx0

end LinearMap.IsSymmetric

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {A B : E →ₗ[𝕜] E}

/-- Monotonicity of the eigenvalues in the operator, with slack: if the quadratic form of `A`
exceeds that of `B` by at most `C ‖x‖ ^ 2`, then every eigenvalue of `A` exceeds the corresponding
eigenvalue of `B` by at most `C`.  This is the quadratic-form hypothesis that [kress1998numerical]
proof of Weyl's inequality ([kress1998numerical], Cor 7.5) actually uses. -/
theorem eigenvalues_le_add_of_re_inner_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ}
    (h : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ RCLike.re (inner 𝕜 (B x) x) + C * ‖x‖ ^ 2)
    (i : Fin n) : hA.eigenvalues hn i ≤ hB.eigenvalues hn i + C := by
  have hcard : Module.finrank 𝕜 (hA.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hA.finrank_eigenvectorSpan hn, Fin.card_Iic]
  obtain ⟨x, hxS, hx0, hxle⟩ := hB.exists_mem_ne_zero_rayleighQuotient_le hn i hcard.ge
  have hlb := hA.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i hxS hx0
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have key : A.rayleighQuotient x ≤ B.rayleighQuotient x + C := by
    rw [LinearMap.rayleighQuotient, div_le_iff₀ hpos, add_mul, LinearMap.rayleighQuotient,
      div_mul_cancel₀ _ hpos.ne']
    exact h x
  linarith

/-- Monotonicity of the eigenvalues in the operator: if the quadratic form of `A` is everywhere at
most that of `B`, then every eigenvalue of `A` is at most the corresponding eigenvalue of `B`. -/
theorem eigenvalues_le_of_re_inner_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
    (h : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ RCLike.re (inner 𝕜 (B x) x)) (i : Fin n) :
    hA.eigenvalues hn i ≤ hB.eigenvalues hn i := by
  simpa using hA.eigenvalues_le_add_of_re_inner_le hB hn (C := 0) (by simpa using h) i

/-- One half of Weyl's inequality, from a bound on the perturbation through Cauchy–Schwarz. -/
theorem eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ} (hC : ∀ x : E, ‖(A - B) x‖ ≤ C * ‖x‖) (i : Fin n) :
    hA.eigenvalues hn i - hB.eigenvalues hn i ≤ C := by
  refine sub_le_iff_le_add'.mpr (hA.eigenvalues_le_add_of_re_inner_le hB hn (fun x => ?_) i)
  have h1 : RCLike.re (inner 𝕜 ((A - B) x) x) ≤ ‖(A - B) x‖ * ‖x‖ := re_inner_le_norm _ _
  have h2 : ‖(A - B) x‖ * ‖x‖ ≤ C * ‖x‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right (hC x) (norm_nonneg x)
  have h3 : C * ‖x‖ ^ 2 = C * ‖x‖ * ‖x‖ := by ring
  rw [LinearMap.sub_apply, inner_sub_left, map_sub] at h1
  rw [LinearMap.sub_apply] at h2
  linarith

/-- **Weyl's inequality** ([kress1998numerical], Cor 7.5): the `i`-th eigenvalues of two symmetric
operators differ by at most any bound `C` on the perturbation `A - B`. -/
theorem abs_eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ} (hC : ∀ x : E, ‖(A - B) x‖ ≤ C * ‖x‖) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ C := by
  refine abs_sub_le_iff.mpr ⟨hA.eigenvalues_sub_le hB hn hC i,
    hB.eigenvalues_sub_le hA hn (fun x => ?_) i⟩
  have hx := hC x
  rwa [show (B - A) x = -((A - B) x) by simp, norm_neg]

/-- **Weyl's inequality**, operator-norm form: the `i`-th eigenvalues of two symmetric continuous
linear operators differ by at most `‖A - B‖`. -/
theorem abs_eigenvalues_sub_le_opNorm {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A - B‖ := by
  refine hA.abs_eigenvalues_sub_le hB hn (fun x => ?_) i
  rw [← ContinuousLinearMap.toLinearMap_sub]
  exact (A - B).le_opNorm x

/-- **Weyl's inequality, two-sided form** ([golub2013matrix] Theorem 8.1.5): adding a symmetric `E`
to a symmetric `A` moves every eigenvalue by an amount between the extreme eigenvalues of `E`,
`λ_i(A) + λ_min(E) ≤ λ_i(A + E) ≤ λ_i(A) + λ_max(E)`. Both bounds are
`LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le`, with the quadratic-form bounds
`λ_min(E) ‖x‖² ≤ re ⟪E x, x⟫ ≤ λ_max(E) ‖x‖²` as the slack. -/
theorem eigenvalues_add_mem_Icc {m : ℕ} (hA : A.IsSymmetric) (hE : B.IsSymmetric)
    (hAE : (A + B).IsSymmetric) (hn : Module.finrank 𝕜 E = m + 1) (i : Fin (m + 1)) :
    hAE.eigenvalues hn i ∈ Set.Icc (hA.eigenvalues hn i + hE.eigenvalues hn (Fin.last m))
      (hA.eigenvalues hn i + hE.eigenvalues hn 0) := by
  have huniv : ∀ x : E, x ∈ hE.eigenvectorSpan hn Finset.univ := fun x => by
    rw [hE.eigenvectorSpan_univ hn]; trivial
  have hup : ∀ x : E, RCLike.re (inner 𝕜 (B x) x) ≤ hE.eigenvalues hn 0 * ‖x‖ ^ 2 := fun x =>
    hE.re_inner_apply_self_le_of_mem_eigenvectorSpan hn
      (fun j _ => hE.eigenvalues_antitone hn (Fin.zero_le j)) (huniv x)
  have hlo : ∀ x : E, hE.eigenvalues hn (Fin.last m) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x) :=
    fun x => hE.le_re_inner_apply_self_of_mem_eigenvectorSpan hn
      (fun j _ => hE.eigenvalues_antitone hn (Fin.le_last j)) (huniv x)
  constructor
  · have h := hA.eigenvalues_le_add_of_re_inner_le hAE hn
      (C := -hE.eigenvalues hn (Fin.last m)) (fun x => by
        rw [LinearMap.add_apply, inner_add_left, map_add]; linarith [hlo x]) i
    linarith
  · have h := hAE.eigenvalues_le_add_of_re_inner_le hA hn (C := hE.eigenvalues hn 0)
      (fun x => by rw [LinearMap.add_apply, inner_add_left, map_add]; linarith [hup x]) i
    linarith

end LinearMap.IsSymmetric

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-! ### Cauchy interlacing -/

/-- **Cauchy interlacing** along a linear isometry: if `S` is symmetric on an `m`-dimensional `F`,
`ι : F →ₗᵢ[𝕜] E` is a linear isometry and the quadratic form of `S` is that of `T` pulled back along
`ι`, `re ⟪S y, y⟫ = re ⟪T (ι y), ι y⟫`, then the sorted eigenvalues interlace:
`λ_{i + (n - m)}(T) ≤ λ_i(S) ≤ λ_i(T)`. Both inequalities are Courant–Fischer: the subspaces of `F`
are, through `ι`, among the subspaces of `E` of the same dimension, so every max–min or min–max
competitor for `S` is one for `T`. -/
theorem eigenvalues_interlace_of_linearIsometry {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {S : F →ₗ[𝕜] F} (hS : S.IsSymmetric)
    {m : ℕ} (hm : Module.finrank 𝕜 F = m) (hmn : m ≤ n) (ι : F →ₗᵢ[𝕜] E)
    (hSι : ∀ y, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T (ι y)) (ι y))) (i : Fin m) :
    hT.eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩ ≤ hS.eigenvalues hm i ∧
      hS.eigenvalues hm i ≤ hT.eigenvalues hn (Fin.castLE hmn i) := by
  have hRQ : ∀ y, S.rayleighQuotient y = T.rayleighQuotient (ι y) := fun y => by
    rw [LinearMap.rayleighQuotient, LinearMap.rayleighQuotient, hSι, ι.norm_map]
  have hinj : Function.Injective ι.toLinearMap := ι.injective
  have hi := i.isLt
  constructor
  · obtain ⟨⟨S', hS', hb⟩, -⟩ := hS.isLeast_eigenvalues hm i
    refine (hT.isLeast_eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩).2
      ⟨S'.map ι.toLinearMap, ?_, ?_⟩
    · rw [← (Submodule.equivMapOfInjective _ hinj S').finrank_eq, hS']
      simp only
      omega
    · rintro _ ⟨y, hy, rfl⟩ hx0
      rw [LinearIsometry.coe_toLinearMap, ← hRQ]
      exact hb y hy fun h => hx0 (by simp [h])
  · obtain ⟨⟨S', hS', hb⟩, -⟩ := hS.isGreatest_eigenvalues hm i
    refine (hT.isGreatest_eigenvalues hn (Fin.castLE hmn i)).2 ⟨S'.map ι.toLinearMap, ?_, ?_⟩
    · rw [← (Submodule.equivMapOfInjective _ hinj S').finrank_eq, hS']
      rfl
    · rintro _ ⟨y, hy, rfl⟩ hx0
      rw [LinearIsometry.coe_toLinearMap, ← hRQ]
      exact hb y hy fun h => hx0 (by simp [h])

/-- **Cauchy interlacing** for the restriction of the quadratic form to a subspace: for a symmetric
`S : K →ₗ[𝕜] K` on an `m`-dimensional subspace `K` of `E` whose quadratic form is that of `T`,
`re ⟪S y, y⟫ = re ⟪T y, y⟫` for `y : K`, the sorted eigenvalues satisfy
`λ_{i + (n - m)}(T) ≤ λ_i(S) ≤ λ_i(T)`. The upper inequality is
`LinearMap.IsSymmetric.eigenvalues_compression_le` of `Numlib/Eigen/RayleighRitz` when `S` is the
compression; stated with the quadratic-form hypothesis, it applies to the compression
(`Krylov.rayleighQuotient_compression`) and to a principal submatrix alike
([saad2011numerical] Theorem 1.10; [golub1989matrix] Theorem 8.1.7; the weak half of
[quarteroni2000numerical] Property 5.11). -/
theorem eigenvalues_restrict_interlace {K : Submodule 𝕜 E} {S : K →ₗ[𝕜] K} (hS : S.IsSymmetric)
    {m : ℕ} (hm : Module.finrank 𝕜 K = m) (hmn : m ≤ n)
    (hSK : ∀ y : K, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T y) (y : E))) (i : Fin m) :
    hT.eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩ ≤ hS.eigenvalues hm i ∧
      hS.eigenvalues hm i ≤ hT.eigenvalues hn (Fin.castLE hmn i) :=
  hT.eigenvalues_interlace_of_linearIsometry hn hS hm hmn K.subtypeₗᵢ hSK i

end LinearMap.IsSymmetric

/-! ### Low-rank interlacing -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {A B : E →ₗ[𝕜] E}

/-- **Low-rank interlacing**: a perturbation of rank at most `r` moves every eigenvalue by at most
`r` places. For symmetric `A`, `B` with `finrank (range (B - A)) ≤ r`, `λ_{i+r}(B) ≤ λ_i(A)`
(and, exchanging the two, `λ_{i+r}(A) ≤ λ_i(B)`). Courant–Fischer: on the `(i + r + 1)`-dimensional
span of the leading eigenvectors of `B` the Rayleigh quotient of `B` is at least `λ_{i+r}(B)`; its
intersection with `ker (B - A)`, of dimension at least `i + 1`, carries a nonzero vector whose
Rayleigh quotient for `A`, the same as for `B` there, is at most `λ_i(A)`. -/
theorem eigenvalues_le_of_finrank_range_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {r : ℕ} (hr : Module.finrank 𝕜 (LinearMap.range (B - A)) ≤ r)
    (i : Fin n) (hir : (i : ℕ) + r < n) :
    hB.eigenvalues hn ⟨(i : ℕ) + r, hir⟩ ≤ hA.eigenvalues hn i := by
  set S := hB.eigenvectorSpan hn (Finset.Iic ⟨(i : ℕ) + r, hir⟩)
  have hS : Module.finrank 𝕜 S = (i : ℕ) + r + 1 := by
    rw [hB.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hK : n - r ≤ Module.finrank 𝕜 (LinearMap.ker (B - A)) := by
    have := LinearMap.finrank_range_add_finrank_ker (B - A)
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker (B - A))
  have hle : Module.finrank 𝕜 (S ⊔ LinearMap.ker (B - A) : Submodule 𝕜 E) ≤ n :=
    hn ▸ Submodule.finrank_le _
  obtain ⟨x, hxW, hx0, hxle⟩ := hA.exists_mem_ne_zero_rayleighQuotient_le hn i
    (S := S ⊓ LinearMap.ker (B - A)) (by omega)
  have hBx : B x = A x := by
    have := (Submodule.mem_inf.mp hxW).2
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have hlb := hB.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn ⟨(i : ℕ) + r, hir⟩
    (Submodule.mem_inf.mp hxW).1 hx0
  rw [LinearMap.rayleighQuotient, hBx] at hlb
  exact hlb.trans hxle

/-- **Interlacing for a positive low-rank perturbation** ([golub2013matrix] Theorem 8.1.8 is
`r = 1`, `B - A = τ c cᵀ` with `τ ≥ 0`): if `B - A` is positive and of rank at most `r`, then
`λ_{i+r}(B) ≤ λ_i(A) ≤ λ_i(B)`. The first inequality is
`LinearMap.IsSymmetric.eigenvalues_le_of_finrank_range_sub_le`, which needs no positivity; the
second is the monotonicity `LinearMap.IsSymmetric.eigenvalues_le_of_re_inner_le`. -/
theorem eigenvalues_le_of_isPositive_sub_of_finrank_range_le (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (hBA : (B - A).IsPositive) {r : ℕ}
    (hr : Module.finrank 𝕜 (LinearMap.range (B - A)) ≤ r) (i : Fin n) (hir : (i : ℕ) + r < n) :
    hB.eigenvalues hn ⟨(i : ℕ) + r, hir⟩ ≤ hA.eigenvalues hn i ∧
      hA.eigenvalues hn i ≤ hB.eigenvalues hn i :=
  ⟨hA.eigenvalues_le_of_finrank_range_sub_le hB hn hr i hir,
    hA.eigenvalues_le_of_re_inner_le hB hn (fun x => by
      have := hBA.2 x
      rw [LinearMap.sub_apply, inner_sub_left, map_sub] at this
      linarith) i⟩

end LinearMap.IsSymmetric

/-! ### Ky Fan's principles and the Hoffman–Wielandt inequality -/

/-- The quadratic form summed over an orthonormal family is the real trace of the compression of
the operator to the span of the family: the family is an orthonormal basis of its span, in which
the diagonal entries of the compression are `⟪x i, T (x i)⟫`. -/
theorem LinearMap.sum_re_inner_eq_re_trace_compression [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E)
    {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x) :
    ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) =
      RCLike.re (LinearMap.trace 𝕜 _ (compression T (Submodule.span 𝕜 (Set.range x)))) := by
  set K := Submodule.span 𝕜 (Set.range x)
  let b : OrthonormalBasis (Fin k) 𝕜 K :=
    (Module.Basis.span hx.linearIndependent).toOrthonormalBasis
      (K.subtypeₗᵢ.orthonormal_comp_iff.mp (by convert hx; ext; simp))
  have hb : ∀ i, (b i : E) = x i := fun i => by simp [b]
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [compression.inner_apply', hb, ← inner_conj_symm, RCLike.conj_re]

/-- Summation by parts, in the form used for the trace inequality: if every partial sum of `d` is
nonnegative and `f` decreases, then `∑ f i d i ≥ f_last ∑ d i`. -/
private theorem mul_sum_le_sum_mul_of_antitone {n : ℕ} {f d : Fin (n + 1) → ℝ} (hf : Antitone f)
    (hd : ∀ (k : ℕ) (hk : k ≤ n + 1), 0 ≤ ∑ i : Fin k, d (Fin.castLE hk i)) :
    f (Fin.last n) * ∑ i, d i ≤ ∑ i, f i * d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (f := f ∘ Fin.castSucc) (d := d ∘ Fin.castSucc)
      (fun i j hij => hf (Fin.castSucc_le_castSucc_iff.mpr hij))
      (fun k hk => hd k (by omega))
    have h0 : 0 ≤ ∑ i : Fin (n + 1), d (Fin.castSucc i) := hd (n + 1) (by omega)
    have hfl : f (Fin.last (n + 1)) ≤ f (Fin.castSucc (Fin.last n)) := hf (Fin.le_last _)
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (fun i => f i * d i), mul_add]
    simp only [Function.comp] at ih'
    nlinarith

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

section KyFan

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
include hT

/-- **Ky Fan's maximum principle**: for an orthonormal family `x : Fin k → E`, the quadratic forms
`re ⟪T x_i, x_i⟫` sum to at most the sum of the `k` largest eigenvalues, with equality at the
leading eigenvectors (`LinearMap.IsSymmetric.sum_re_inner_eigenvectorBasis`). The sum is the real
trace of the compression of `T` to the span of the family
(`LinearMap.sum_re_inner_eq_re_trace_compression`), that is the sum of the compression's
eigenvalues, each of which is at most the corresponding eigenvalue of `T` by Cauchy interlacing. -/
theorem sum_re_inner_le_sum_eigenvalues {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    (hkn : k ≤ n) :
    ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) ≤
      ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hkn i) := by
  have hK : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range x)) = k := by
    rw [finrank_span_eq_card hx.linearIndependent, Fintype.card_fin]
  have hS := compression.isSymmetric T (Submodule.span 𝕜 (Set.range x)) hT
  rw [T.sum_re_inner_eq_re_trace_compression hx, hS.re_trace_eq_sum_eigenvalues hK]
  exact Finset.sum_le_sum fun i _ =>
    (hT.eigenvalues_restrict_interlace hn hS hK hkn
      (fun y => by rw [compression.inner_apply]) i).2

/-- **Ky Fan's minimum principle**, the dual of
`LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues`: for an orthonormal family
`x : Fin k → E`, the quadratic forms `re ⟪T x_i, x_i⟫` sum to at least the sum of the `k` smallest
eigenvalues (the trace-minimization principle of [golub2013matrix] §10.6.5 for `B = I`). The same
compression argument, with the other half of Cauchy interlacing. -/
theorem sum_eigenvalues_le_sum_re_inner {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    (hkn : k ≤ n) :
    ∑ i : Fin k, hT.eigenvalues hn ⟨(i : ℕ) + (n - k), by omega⟩ ≤
      ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) := by
  have hK : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range x)) = k := by
    rw [finrank_span_eq_card hx.linearIndependent, Fintype.card_fin]
  have hS := compression.isSymmetric T (Submodule.span 𝕜 (Set.range x)) hT
  rw [T.sum_re_inner_eq_re_trace_compression hx, hS.re_trace_eq_sum_eigenvalues hK]
  exact Finset.sum_le_sum fun i _ =>
    (hT.eigenvalues_restrict_interlace hn hS hK hkn
      (fun y => by rw [compression.inner_apply]) i).1

/-- The equality case of Ky Fan's maximum principle: at the `k` leading eigenvectors the quadratic
forms sum to the sum of the `k` largest eigenvalues. -/
theorem sum_re_inner_eigenvectorBasis {k : ℕ} (hkn : k ≤ n) :
    ∑ i : Fin k, RCLike.re (inner 𝕜 (T (hT.eigenvectorBasis hn (Fin.castLE hkn i)))
        (hT.eigenvectorBasis hn (Fin.castLE hkn i))) =
      ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hkn i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← T.rayleighQuotient_of_norm_eq_one ((hT.eigenvectorBasis hn).norm_eq_one _),
    hT.rayleighQuotient_eigenvectorBasis]

/-- The trace of the square of a symmetric operator is the sum of the squared eigenvalues. -/
theorem trace_comp_self_eq_sum_sq :
    LinearMap.trace 𝕜 E (T ∘ₗ T) = ∑ i, ((hT.eigenvalues hn i : 𝕜)) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, hT.apply_eigenvectorBasis, map_smul, hT.apply_eigenvectorBasis,
    smul_smul, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).norm_eq_one]
  simp [sq]

end KyFan

variable {A B : E →ₗ[𝕜] E}

/-- **The trace inequality for two symmetric operators**: `re tr(A B) ≤ ∑ λ_i(A) λ_i(B)`, both
eigenvalue lists sorted decreasingly (the symmetric case of von Neumann's trace inequality). In the
eigenbasis `v` of `B`, `re tr(A B) = ∑ μ_i a_i` with `a_i = re ⟪A v_i, v_i⟫`; the partial sums of
`a` are bounded by those of `λ(A)` (Ky Fan,
`LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues`), with equality for the full sum (the
trace), and summation by parts against the decreasing `μ` gives the claim. -/
theorem re_trace_comp_le_sum_eigenvalues_mul (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    RCLike.re (LinearMap.trace 𝕜 E (A ∘ₗ B)) ≤
      ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i := by
  set v := hB.eigenvectorBasis hn
  set a : Fin n → ℝ := fun i => RCLike.re (inner 𝕜 (A (v i)) (v i))
  have htr : RCLike.re (LinearMap.trace 𝕜 E (A ∘ₗ B)) = ∑ i, hB.eigenvalues hn i * a i := by
    rw [LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, hB.apply_eigenvectorBasis, map_smul, inner_smul_right,
      ← hA, RCLike.re_ofReal_mul]
  have hsum : ∑ i, a i = ∑ i, hA.eigenvalues hn i := by
    rw [← hA.re_trace_eq_sum_eigenvalues hn, LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA]
  rw [htr]
  obtain _ | m := n
  · simp
  have key := mul_sum_le_sum_mul_of_antitone (f := hB.eigenvalues hn)
    (d := fun i => hA.eigenvalues hn i - a i) (hB.eigenvalues_antitone hn) (fun k hk => by
      rw [Finset.sum_sub_distrib, sub_nonneg]
      exact hA.sum_re_inner_le_sum_eigenvalues hn
        (v.orthonormal.comp _ (Fin.castLE_injective hk)) hk)
  rw [Finset.sum_sub_distrib, hsum, sub_self, mul_zero] at key
  have : ∑ i, hB.eigenvalues hn i * (hA.eigenvalues hn i - a i) =
      ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i - ∑ i, hB.eigenvalues hn i * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **The Hoffman–Wielandt inequality**, operator form: for symmetric `A`, `B` with eigenvalues
sorted decreasingly, `∑ (λ_i(A) - λ_i(B))² ≤ re tr((A - B)²)`, the right side being the squared
Hilbert–Schmidt norm of `A - B`. Expand the square: `tr A² = ∑ λ_i(A)²`, `tr B² = ∑ λ_i(B)²`, and
the cross term is the trace inequality
`LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul`. -/
theorem sum_sq_eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    ∑ i, (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 ≤
      RCLike.re (LinearMap.trace 𝕜 E ((A - B) ∘ₗ (A - B))) := by
  have hexp : (A - B) ∘ₗ (A - B) = A ∘ₗ A - A ∘ₗ B - B ∘ₗ A + B ∘ₗ B := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub]; abel
  have hAA := congrArg RCLike.re (hA.trace_comp_self_eq_sum_sq hn)
  have hBB := congrArg RCLike.re (hB.trace_comp_self_eq_sum_sq hn)
  have hAB := re_trace_comp_le_sum_eigenvalues_mul hn hA hB
  have hBA : LinearMap.trace 𝕜 E (B ∘ₗ A) = LinearMap.trace 𝕜 E (A ∘ₗ B) :=
    (LinearMap.trace_comp_comm' B A).symm
  simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hAA hBB
  rw [hexp, map_add, map_sub, map_sub, hBA, map_add, map_sub, map_sub, hAA, hBB]
  have : ∑ i, (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 =
      ∑ i, hA.eigenvalues hn i ^ 2 - 2 * ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i +
        ∑ i, hB.eigenvalues hn i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end LinearMap.IsSymmetric

/-! ### Negation

Every statement about a largest eigenvalue is a statement about a smallest one for `-T`, and this
section is the dictionary: `eigenvalues_neg` for the values, `exists_smul_eigenvectorBasis_neg` for
the vectors at a simple eigenvalue, and the two congruences that let a `rw` happen inside the
dependent types `hT.eigenvalues hn` and `(compression.isSymmetric T K hT).eigenvalues hK`. -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ}

/-- The sorted eigenvalues depend on the operator only, not on the proof that it is symmetric. The
operators are variables, so that `subst` can do the transport that a `rw` inside a dependent type
cannot. -/
theorem eigenvalues_congr {T T' : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hT' : T'.IsSymmetric)
    (h : T = T') (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i = hT'.eigenvalues hn i := by
  subst h; rfl

/-- The eigenvalues of the compressions to two equal subspaces agree. The subspaces are variables,
so that `subst` can do the transport that a `rw` inside a dependent type cannot. -/
theorem eigenvalues_compression_congr {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {K L : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K = L) {m : ℕ}
    (hK : Module.finrank 𝕜 K = m) (hL : Module.finrank 𝕜 L = m) (i : Fin m) :
    (compression.isSymmetric T K hT).eigenvalues hK i
      = (compression.isSymmetric T L hT).eigenvalues hL i := by
  subst hKL; rfl

/-- **The eigenvalues of `-T` are the negatives of those of `T`, in reversed order**: with both
lists sorted decreasingly, the `i`-th eigenvalue of `-T` is minus the `(n - 1 - i)`-th of `T`. The
proof is Courant–Fischer: negating the Rayleigh quotient exchanges the max–min characterization of
`hT.eigenvalues hn i` (`isGreatest_eigenvalues`, over subspaces of dimension `i + 1`) with the
min–max characterization of `hT.eigenvalues hn i.rev` (`isLeast_eigenvalues`, over subspaces of
dimension `n - i.rev = i + 1`), so the two sets of bounds coincide. -/
theorem eigenvalues_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : hT.neg.eigenvalues hn i = -hT.eigenvalues hn i.rev := by
  have hrev : n - ((i.rev : Fin n) : ℕ) = (i : ℕ) + 1 := by
    have := i.isLt
    simp only [Fin.val_rev]
    omega
  refine (hT.neg.isGreatest_eigenvalues hn i).unique ⟨?_, ?_⟩
  · obtain ⟨⟨S, hS, hbd⟩, -⟩ := hT.isLeast_eigenvalues hn i.rev
    refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
    rw [rayleighQuotient_neg]
    linarith [hbd x hx hx0]
  · rintro c ⟨S, hS, hc⟩
    have hmem : -c ∈ {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - ((i.rev : Fin n) : ℕ) ∧
        ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} := by
      refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
      have := hc x hx hx0
      rw [rayleighQuotient_neg] at this
      linarith
    have := (hT.isLeast_eigenvalues hn i.rev).2 hmem
    linarith

/-- **A simple extreme eigenvalue of `-T` has the same eigenvector line as its partner for `T`**:
if the `i.rev`-th eigenvalue of `T` is simple, the `i`-th eigenvector of `-T` is a nonzero multiple
of the `i.rev`-th eigenvector of `T`. Expanding the eigenvector of `-T` in the eigenbasis of `T`,
the coefficients at the other indices carry the factor `λ_j - λ_{i.rev} ≠ 0` and vanish. -/
theorem exists_smul_eigenvectorBasis_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n)
    (hsimple : ∀ j : Fin n, j ≠ i.rev → hT.eigenvalues hn j ≠ hT.eigenvalues hn i.rev) :
    ∃ c : 𝕜, c ≠ 0 ∧
      hT.neg.eigenvectorBasis hn i = c • hT.eigenvectorBasis hn i.rev := by
  set b := hT.eigenvectorBasis hn with hb
  set w := hT.neg.eigenvectorBasis hn i with hw
  have hTw : T w = (hT.eigenvalues hn i.rev : 𝕜) • w := by
    have h := hT.neg.apply_eigenvectorBasis hn i
    rw [eigenvalues_neg hT hn i, LinearMap.neg_apply] at h
    have h' := congrArg Neg.neg h
    rwa [neg_neg, RCLike.ofReal_neg, neg_smul, neg_neg] at h'
  have hzero : ∀ j : Fin n, j ≠ i.rev → b.repr w j = 0 := by
    intro j hj
    have h1 := hT.eigenvectorBasis_apply_self_apply hn w j
    rw [hTw, map_smul] at h1
    simp only [PiLp.smul_apply, smul_eq_mul] at h1
    have h2 : ((hT.eigenvalues hn j : 𝕜) - (hT.eigenvalues hn i.rev : 𝕜)) * b.repr w j = 0 := by
      rw [sub_mul]
      rw [← h1]
      ring
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) (hsimple j hj)
    · exact h3
  have hsum : ∑ j, b.repr w j • b j = w := b.sum_repr w
  rw [Finset.sum_eq_single i.rev (fun j _ hj => by rw [hzero j hj, zero_smul])
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  refine ⟨b.repr w i.rev, ?_, hsum.symm⟩
  intro h0
  rw [h0, zero_smul] at hsum
  exact hT.neg.eigenvectorBasis_ne_zero hn i hsum.symm

end LinearMap.IsSymmetric

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Cauchy interlacing for a compression `Vᴴ A V`** with `Vᴴ V = 1` ([saad2011numerical]
Theorem 1.10; [golub1989matrix] Theorem 8.1.7): the sorted eigenvalues
(`Matrix.IsHermitian.eigenvalues₀`, decreasing) of the `m × m` Hermitian matrix `Vᴴ A V` interlace
those of the `n × n` Hermitian `A`, `λ_{k + (n - m)}(A) ≤ λ_k(Vᴴ A V) ≤ λ_k(A)`. -/
theorem IsHermitian.eigenvalues₀_conjTranspose_mul_mul_interlace {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) (hB : (Vᴴ * A * V).IsHermitian)
    (hmn : Fintype.card m ≤ Fintype.card n) (k : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨(k : ℕ) + (Fintype.card n - Fintype.card m), by omega⟩ ≤ hB.eigenvalues₀ k ∧
      hB.eigenvalues₀ k ≤ hA.eigenvalues₀ (Fin.castLE hmn k) :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues_interlace_of_linearIsometry
    finrank_euclideanSpace (isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace hmn
    (toEuclideanLinearIsometry hV) (fun y => by
      rw [toEuclideanLinearIsometry_apply, Matrix.toEuclideanLin_mul_apply,
        Matrix.toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]) k

/-- **Cauchy interlacing for a principal submatrix** ([quarteroni2000numerical] Property 5.11, the
weak inequalities; [golub1989matrix] Theorem 8.1.7): for a Hermitian `A` and an injective
`f : m → n`, the sorted eigenvalues of `A.submatrix f f` interlace those of `A`,
`λ_{k + (n - m)}(A) ≤ λ_k(A.submatrix f f) ≤ λ_k(A)`. It is the compression by the matrix
`V = (1 : Matrix n n 𝕜).submatrix id f` of the selected columns of the identity, for which
`Vᴴ A V = A.submatrix f f`. -/
theorem IsHermitian.eigenvalues₀_submatrix_interlace {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : m → n} (hf : Function.Injective f) (hB : (A.submatrix f f).IsHermitian)
    (k : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨(k : ℕ) + (Fintype.card n - Fintype.card m),
        by have := Fintype.card_le_of_injective f hf; omega⟩ ≤ hB.eigenvalues₀ k ∧
      hB.eigenvalues₀ k ≤ hA.eigenvalues₀ (Fin.castLE (Fintype.card_le_of_injective f hf) k) := by
  set V : Matrix n m 𝕜 := (1 : Matrix n n 𝕜).submatrix (Equiv.refl n) f with hVdef
  have hVH : Vᴴ = (1 : Matrix n n 𝕜).submatrix f (Equiv.refl n) := by
    rw [hVdef, conjTranspose_submatrix, conjTranspose_one]
  have hVV : Vᴴ * V = 1 := by
    rw [hVH, hVdef, one_submatrix_mul f (Equiv.refl n), submatrix_submatrix]
    simpa using submatrix_one_embedding (α := 𝕜) ⟨f, hf⟩
  have hVAV : Vᴴ * A * V = A.submatrix f f := by
    rw [hVH, hVdef, Matrix.mul_assoc, mul_submatrix_one (Equiv.refl n) f,
      one_submatrix_mul f (Equiv.refl n), submatrix_submatrix]
    simp
  have h := hA.eigenvalues₀_conjTranspose_mul_mul_interlace hVV (hVAV ▸ hB)
    (Fintype.card_le_of_injective f hf) k
  convert h using 3 <;> exact hVAV.symm

end Matrix

/-! ### Traces and the Hoffman–Wielandt inequality for Hermitian matrices -/

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a Hermitian matrix is the sum of its sorted eigenvalues `eigenvalues₀`
([golub2013matrix] P8.1.8). Mathlib's `Matrix.IsHermitian.trace_eq_sum_eigenvalues` is the same
statement for the `n`-indexed `eigenvalues`. -/
theorem trace_eq_sum_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.trace = ∑ k, (hA.eigenvalues₀ k : 𝕜) := by
  rw [← A.trace_toLin_eq (EuclideanSpace.basisFun n 𝕜).toBasis,
    ← toEuclideanLin_eq_toLin_orthonormal]
  exact_mod_cast (isSymmetric_toEuclideanLin_iff.mpr hA).trace_eq_sum_eigenvalues
    finrank_euclideanSpace

open scoped Matrix.Norms.Frobenius in
/-- For a Hermitian `M`, the squared Frobenius norm is the real trace of the square of the operator
`toEuclideanLin M`: `‖M‖_F² = ∑ i j |M i j|² = re tr(M M)`, as `M j i = conj (M i j)`. -/
theorem re_trace_toEuclideanLin_comp_self {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    RCLike.re (LinearMap.trace 𝕜 _ (toEuclideanLin M ∘ₗ toEuclideanLin M)) = ‖M‖ ^ 2 := by
  rw [← toLpLin_mul_same, toLpLin_eq_toLin,
    LinearMap.trace_eq_matrix_trace 𝕜 (PiLp.basisFun 2 𝕜 n), LinearMap.toMatrix_toLin,
    frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  rw [trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hM.apply i j, RCLike.star_def, RCLike.conj_mul, RCLike.norm_conj, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

open scoped Matrix.Norms.Frobenius in
/-- **The Hoffman–Wielandt inequality** ([golub2013matrix] Theorem 8.1.4, "Wielandt–Hoffman"): for
Hermitian `A`, `B` with eigenvalues sorted decreasingly, `∑ k (λ_k(A) - λ_k(B))² ≤ ‖A - B‖_F²`.
The operator form `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le` for `toEuclideanLin`, with
`Matrix.IsHermitian.re_trace_toEuclideanLin_comp_self` for the right side. -/
theorem hoffman_wielandt {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ k, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2 ≤ ‖A - B‖ ^ 2 := by
  rw [← (hA.sub hB).re_trace_toEuclideanLin_comp_self, map_sub]
  exact LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le finrank_euclideanSpace
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)

end Matrix.IsHermitian

/-! ### The sorted eigenvalues of a Hermitian matrix, indexed by `Fin n` -/

namespace Matrix.IsHermitian

variable {n : ℕ}

/-- The eigenvalues of a Hermitian `n × n` matrix, **sorted decreasingly and indexed by `Fin n`**:
`hA.sortedEigenvalues k` is the `(k + 1)`-st largest eigenvalue, the `λ_{k+1}(A)` of
[golub2013matrix] §8.1.1. It is Mathlib's `Matrix.IsHermitian.eigenvalues₀`, whose index type
`Fin (Fintype.card (Fin n))` is not `Fin n` by definition, reindexed along `Fintype.card_fin`, so
that statements about the `k`-th eigenvalue of a matrix and of its leading principal submatrices
read on `Fin n` with `Fin.succ` and `Fin.castSucc`. -/
noncomputable def sortedEigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Fin n → ℝ :=
  hA.eigenvalues₀ ∘ Fin.cast (Fintype.card_fin n).symm

/-- `Matrix.IsHermitian.sortedEigenvalues` in terms of Mathlib's `eigenvalues₀`. -/
theorem sortedEigenvalues_apply {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (k : Fin n) :
    hA.sortedEigenvalues k = hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) :=
  rfl

/-- The sorted eigenvalues depend on the matrix only, not on the proof that it is Hermitian nor on
the way it is written. -/
theorem sortedEigenvalues_congr {A B : Matrix (Fin n) (Fin n) 𝕜} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : hA.sortedEigenvalues = hB.sortedEigenvalues := by
  subst h
  rfl

/-- The sorted eigenvalues decrease. -/
theorem sortedEigenvalues_antitone {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Antitone hA.sortedEigenvalues := fun i j hij =>
  hA.eigenvalues₀_antitone (show Fin.cast _ i ≤ Fin.cast _ j from hij)

/-- The roots of the characteristic polynomial, with multiplicity, are the sorted eigenvalues. -/
theorem roots_charpoly_eq_sortedEigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.sortedEigenvalues) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues₀,
    ← Finset.map_univ_equiv (finCongr (Fintype.card_fin n).symm), Finset.map_val,
    Multiset.map_map]
  rfl

/-- **Cauchy interlacing for the leading principal submatrix** ([golub2013matrix] Theorem 8.1.7;
[quarteroni2000numerical] Property 5.11, the weak inequalities): the eigenvalues of the leading
`n × n` block of a Hermitian `(n + 1) × (n + 1)` matrix `A` separate those of `A`,
`λ_{k+1}(A) ≤ λ_k(A.submatrix castSucc castSucc) ≤ λ_k(A)`. The `Fin`-indexed reading of
`Matrix.IsHermitian.eigenvalues₀_submatrix_interlace`. -/
theorem sortedEigenvalues_submatrix_castSucc_interlace {A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hA : A.IsHermitian) (hB : (A.submatrix Fin.castSucc Fin.castSucc).IsHermitian) (k : Fin n) :
    hA.sortedEigenvalues k.succ ≤ hB.sortedEigenvalues k ∧
      hB.sortedEigenvalues k ≤ hA.sortedEigenvalues k.castSucc := by
  have hmn : Fintype.card (Fin n) ≤ Fintype.card (Fin (n + 1)) := by simp
  have h := hA.eigenvalues₀_submatrix_interlace (Fin.castSucc_injective n) hB
    (Fin.cast (Fintype.card_fin n).symm k)
  have e1 : (⟨(Fin.cast (Fintype.card_fin n).symm k : ℕ) + (Fintype.card (Fin (n + 1))
      - Fintype.card (Fin n)), by simp⟩ : Fin (Fintype.card (Fin (n + 1))))
      = Fin.cast (Fintype.card_fin (n + 1)).symm k.succ := by
    ext; simp
  have e2 : Fin.castLE hmn (Fin.cast (Fintype.card_fin n).symm k)
      = Fin.cast (Fintype.card_fin (n + 1)).symm k.castSucc := by
    ext; simp
  rw [e1, e2] at h
  exact h


/-- **The spectral decomposition with sorted eigenvalues** ([golub2013matrix] Theorem 8.1.1, with
`λ_1 ≥ ⋯ ≥ λ_n`): a Hermitian `A` of order `N` is unitarily similar to the diagonal matrix of its
decreasingly sorted eigenvalues, `Uᴴ A U = diag(λ_1, …, λ_n)`, the `k`-th column of `U` being an
eigenvector for `λ_k`. The columns are the eigenvector basis of `toEuclideanLin A`, which Mathlib
sorts; Mathlib's `Matrix.IsHermitian.spectral_theorem` is the unsorted form. At `𝕜 = ℝ`,
`unitaryGroup = orthogonalGroup`. The name records that the diagonal is `eigenvalues₀`, reindexed
to `Fin N` as `sortedEigenvalues`. -/
theorem exists_unitary_conj_eq_diagonal_eigenvalues₀ {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) 𝕜,
      star U * A * U = Matrix.diagonal (fun k => (hA.sortedEigenvalues k : 𝕜)) ∧
        ∀ k, A *ᵥ U.col k = (hA.sortedEigenvalues k : 𝕜) • U.col k := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let b := (hT.eigenvectorBasis finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin n))
  let U := (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix b.toBasis
  have hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜 :=
    (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary b
  have hcol : ∀ k, A *ᵥ U.col k = (hA.sortedEigenvalues k : 𝕜) • U.col k := fun k => by
    have h := hT.apply_eigenvectorBasis finrank_euclideanSpace
      (Fin.cast (Fintype.card_fin n).symm k)
    have hbk : b k = hT.eigenvectorBasis finrank_euclideanSpace
        (Fin.cast (Fintype.card_fin n).symm k) := by
      simp [b, OrthonormalBasis.reindex_apply]
    have hUk : U.col k = WithLp.ofLp (b k) := by
      ext i; simp [U, Matrix.col, Module.Basis.toMatrix_apply]
    rw [hUk, hbk, ← Matrix.ofLp_toEuclideanLin, h, WithLp.ofLp_smul]
    rfl
  have hAU : A * U = U * Matrix.diagonal (fun k => (hA.sortedEigenvalues k : 𝕜)) := by
    ext i k
    rw [Matrix.mul_diagonal]
    have := congrFun (hcol k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.col, mul_comm] using this
  refine ⟨U, hU, ?_, hcol⟩
  rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff').mp hU,
    Matrix.one_mul]

end Matrix.IsHermitian

/-! ### Stationary points of the Rayleigh quotient -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The gradient of the Rayleigh quotient** ([golub2013matrix] (10.1.1)): on a real Hilbert
space, for a symmetric `T` and `x ≠ 0`, `∇ r(x) = (2 / ‖x‖²) (T x - r(x) x)` with
`r(x) = ⟪T x, x⟫ / ‖x‖²`. The quotient rule on `⟪T x, x⟫` (derivative `2 ⟪T x, ·⟫`, Mathlib's
`LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`) over `‖x‖²` (derivative
`2 ⟪x, ·⟫`). In particular the gradient lies in `span {x, T x}`. -/
theorem ContinuousLinearMap.hasGradientAt_rayleighQuotient [CompleteSpace F] {T : F →L[ℝ] F}
    (hT : (T : F →ₗ[ℝ] F).IsSymmetric) {x : F} (hx : x ≠ 0) :
    HasGradientAt T.rayleighQuotient
      ((2 / ‖x‖ ^ 2) • (T x - T.rayleighQuotient x • x)) x := by
  have hN : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hQ := (hT.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt
  have hD := (hasFDerivAt_inv hN).comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hQ.mul hD using 1
  · ext y; simp [ContinuousLinearMap.rayleighQuotient, div_eq_mul_inv]
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, add_apply, smul_apply, Function.comp_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, inner_smul_left, inner_sub_left,
      ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, RCLike.conj_to_real, nsmul_eq_mul, Nat.cast_ofNat]
    rw [real_inner_comm y (T x), real_inner_comm y x]
    field_simp
    ring

/-- **The stationary points of the Rayleigh quotient are the eigenvectors** ([golub2013matrix]
(12.5.23)): for a symmetric `T` on a finite-dimensional real inner product space and `x ≠ 0`, the
Fréchet derivative of `r(y) = ⟪T y, y⟫ / ‖y‖²` at `x` vanishes iff `T x = r(x) x`. The derivative
is the gradient `ContinuousLinearMap.hasGradientAt_rayleighQuotient`, a nonzero multiple of
`T x - r(x) x`. Mathlib has only the extremal case,
`IsSelfAdjoint.hasEigenvector_of_isLocalExtrOn`. -/
theorem LinearMap.IsSymmetric.hasFDerivAt_rayleighQuotient_eq_zero_iff
    [FiniteDimensional ℝ F] {T : F →ₗ[ℝ] F} (hT : T.IsSymmetric) {x : F} (hx : x ≠ 0)
    {f' : F →L[ℝ] ℝ} (hf : HasFDerivAt T.rayleighQuotient f' x) :
    f' = 0 ↔ T x = T.rayleighQuotient x • x := by
  set T' := LinearMap.toContinuousLinearMap T
  have hg := ContinuousLinearMap.hasGradientAt_rayleighQuotient (T := T') hT hx
  have heq : f' = InnerProductSpace.toDual ℝ F
      ((2 / ‖x‖ ^ 2) • (T' x - T'.rayleighQuotient x • x)) :=
    hf.unique (hasGradientAt_iff_hasFDerivAt.mp hg)
  have hN : 2 / ‖x‖ ^ 2 ≠ 0 :=
    div_ne_zero two_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  rw [heq, map_eq_zero_iff _ (InnerProductSpace.toDual ℝ F).injective, smul_eq_zero, sub_eq_zero]
  simp only [hN, false_or]
  rfl

end Gradient
