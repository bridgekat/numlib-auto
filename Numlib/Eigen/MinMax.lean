import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Courant–Fischer: the variational characterization of eigenvalues

The eigenvalues of a symmetric operator `T` on a finite-dimensional inner product space, sorted
in decreasing order as `hT.eigenvalues hn : Fin n → ℝ`, are the max–min and min–max values of the
Rayleigh quotient `T.rayleighQuotient x = re ⟪T x, x⟫ / ‖x‖ ^ 2` over subspaces: `λ i` is the
largest number that bounds the Rayleigh quotient from below on some subspace of dimension
`i + 1`, and the smallest number that bounds it from above on some subspace of dimension `n - i`.
This is the min–max theorem of Courant, Fischer, Poincaré and Weyl, stated as the two formulas of
Saad, *Numerical Methods for Large Eigenvalue Problems*[^saad-eigenvalue], Thm 1.9, and as
Kress, *Numerical Analysis*[^kress], Thm 7.4.  Mathlib has only the two extreme eigenvalues,
through `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and its `iInf` twin.

Both books index the eigenvalues from `1` in decreasing order, so their `λ_k` is
`hT.eigenvalues hn i` for `i = k - 1`, and their subspace dimensions `k` and `n + 1 - k` read
here as `i + 1` and `n - i`.

## Main results

* `LinearMap.IsSymmetric.exists_mem_ne_zero_rayleighQuotient_le` and
  `LinearMap.IsSymmetric.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic`: the two directions.
  Every subspace of dimension at least `i + 1` carries a nonzero vector whose Rayleigh quotient
  is at most `λ i`, by the dimension count `(i + 1) + (n - i) > n` against the span of the
  eigenvectors for the eigenvalues from the `i`-th on; and `λ i` is a lower bound for the
  Rayleigh quotient on the span of the eigenvectors for the `i + 1` largest eigenvalues, which
  has dimension `i + 1`.  These two statements are what a consumer usually wants.
* `LinearMap.IsSymmetric.isGreatest_eigenvalues` and
  `LinearMap.IsSymmetric.isLeast_eigenvalues`: the same, as an `IsGreatest`/`IsLeast` over an
  explicit set of reals, with no junk values.
* `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf` and
  `LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup`: the classical `max min` and `min max`
  formulas.
* `LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`: Rayleigh's recursive form,
  the maximum over the vectors orthogonal to the `i` leading eigenvectors.
* `LinearMap.IsSymmetric.abs_eigenvalues_sub_le`: Weyl's inequality, one eigenvalue index at a
  time.

## Implementation notes

The `⨆`/`⨅` forms quantify over *subtypes*, `{S : Submodule 𝕜 E // finrank 𝕜 S = i + 1}` and
`{x : E // x ∈ S ∧ x ≠ 0}`, rather than over all subspaces and all vectors with a nested
`⨆ _ : P, ·`.  The latter is junk: an `iSup` over a false proposition is `sSup ∅ = 0` in `ℝ`, so
it would silently truncate the statement at `0`.  The `IsGreatest` and `IsLeast` forms carry no
`iSup` at all and are the recommended interface.

Weyl's inequality is stated with a hypothesised bound `∀ x, ‖(A - B) x‖ ≤ C * ‖x‖` rather than
with an operator norm, because `E →ₗ[𝕜] E` carries no norm and the hypothesised form does not
force a topology on the consumer.  `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm` is the
corollary for continuous linear maps.  Its workhorse
`LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le` is weaker still: it asks only for the
quadratic-form bound `re ⟪A x, x⟫ ≤ re ⟪B x, x⟫ + C ‖x‖ ^ 2` that Kress's proof actually uses,
which is the form this library prefers for spectral hypotheses.

## References

[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two subspaces whose dimensions add up to more than the dimension of the ambient space meet in
a nonzero vector.  This is the dimension count behind Courant–Fischer. -/
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

/-- The *Rayleigh quotient* of a linear map `T` (over `ℝ` or `ℂ`) at a vector `x` is the real
number `re ⟪T x, x⟫ / ‖x‖ ^ 2`.  This is the `LinearMap` twin of
`ContinuousLinearMap.rayleighQuotient`; the two agree by
`ContinuousLinearMap.rayleighQuotient_eq_toLinearMap`. -/
noncomputable abbrev rayleighQuotient (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner 𝕜 (T x) x) / ‖x‖ ^ 2

/-- The Rayleigh quotient is a junk `0` at the zero vector, where the quotient `0 / 0` is not
meaningful; every statement below excludes `x = 0` explicitly. -/
@[simp]
theorem rayleighQuotient_apply_zero (T : E →ₗ[𝕜] E) : T.rayleighQuotient 0 = 0 := by
  simp [rayleighQuotient]

/-- At a unit vector the Rayleigh quotient is just the quadratic form, which is how the
approximate eigenpairs of `Numlib.Eigen.Perturbation` are stated. -/
theorem rayleighQuotient_of_norm_eq_one (T : E →ₗ[𝕜] E) {x : E} (hx : ‖x‖ = 1) :
    T.rayleighQuotient x = RCLike.re (inner 𝕜 (T x) x) := by
  rw [rayleighQuotient, hx, one_pow, div_one]

/-- The Rayleigh quotient is invariant under rescaling, so a bound at a nonzero vector transfers
to its normalization. -/
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

Every statement below is read off the coordinates of a vector in the orthonormal eigenvector
basis `hT.eigenvectorBasis hn`, in which the norm and the quadratic form are the two sums here. -/

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
Courant–Fischer are `s = Finset.Iic i`, the eigenvectors for the `i + 1` largest eigenvalues, and
`s = Finset.Ici i`, the eigenvectors for the `n - i` smallest ones. -/
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
orthonormal and hence linearly independent.  This is the dimension bookkeeping of
Courant–Fischer. -/
theorem finrank_eigenvectorSpan (s : Finset (Fin n)) :
    Module.finrank 𝕜 (hT.eigenvectorSpan hn s) = s.card := by
  have hli : LinearIndependent 𝕜 fun j : (s : Set (Fin n)) => hT.eigenvectorBasis hn j :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [eigenvectorSpan, Set.image_eq_range, finrank_span_eq_card hli]
  simp

/-! ### Bounds on the Rayleigh quotient over a span of eigenvectors -/

/-- On the span of the eigenvectors indexed by `s`, the quadratic form is bounded above by any
upper bound for the eigenvalues indexed by `s`. -/
theorem re_inner_apply_self_le_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s) :
    RCLike.re (inner 𝕜 (T x) x) ≤ c * ‖x‖ ^ 2 := by
  rw [hT.re_inner_apply_self_eq_sum hn, hT.norm_sq_eq_sum_norm_repr_sq hn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i hi]
    simp

/-- On the span of the eigenvectors indexed by `s`, the quadratic form is bounded below by any
lower bound for the eigenvalues indexed by `s`. -/
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
nonzero vector whose Rayleigh quotient is at most the `i`-th eigenvalue.  The proof is the
dimension count `(i + 1) + (n - i) > n` against the span of the eigenvectors for the eigenvalues
from the `i`-th on. -/
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
quotient from above throughout the span of the eigenvectors for the `n - i` smallest eigenvalues,
a subspace of dimension `n - i`; this is where the min–max is attained. -/
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

/-- **Courant–Fischer, max–min form**, as an `IsGreatest` over an explicit set of reals: the
`i`-th eigenvalue in decreasing order is the largest number that bounds the Rayleigh quotient
from below on some subspace of dimension `i + 1`.  This is the second formula of Saad,
*Numerical Methods for Large Eigenvalue Problems*, Thm 1.9.  The form carries no `iSup`, hence no
junk value. -/
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
eigenvalue in decreasing order is the smallest number that bounds the Rayleigh quotient from
above on some subspace of dimension `n - i`.  This is the first formula of Saad, *Numerical
Methods for Large Eigenvalue Problems*, Thm 1.9, and Kress, *Numerical Analysis*, Thm 7.4.  The
form carries no `iInf`, hence no junk value. -/
theorem isLeast_eigenvalues (i : Fin n) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - (i : ℕ) ∧
      ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} (hT.eigenvalues hn i) := by
  refine ⟨⟨hT.eigenvectorSpan hn (Finset.Ici i), ?_,
    fun x hx hx0 => hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i hx hx0⟩, ?_⟩
  · rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  · rintro c ⟨S, hS, hc⟩
    obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_le_rayleighQuotient hn i hS.ge
    exact hxle.trans (hc x hxS hx0)

/-- **Courant–Fischer, max–min form** (Saad, *Numerical Methods for Large Eigenvalue Problems*,
Thm 1.9, second formula).  The `i`-th eigenvalue in decreasing order is the maximum over subspaces
of dimension `i + 1` of the minimum of the Rayleigh quotient on the subspace.
`LinearMap.IsSymmetric.isGreatest_eigenvalues` is the same statement without an `iSup`. -/
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

/-- **Courant–Fischer, min–max form** (Saad, *Numerical Methods for Large Eigenvalue Problems*,
Thm 1.9, first formula; Kress, *Numerical Analysis*, Thm 7.4).  The `i`-th eigenvalue in
decreasing order is the minimum over subspaces of dimension `n - i` (that is, of codimension `i`)
of the maximum of the Rayleigh quotient on the subspace.
`LinearMap.IsSymmetric.isLeast_eigenvalues` is the same statement without an `iInf`. -/
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

/-- **Rayleigh's recursive characterization** (Saad, *Numerical Methods for Large Eigenvalue
Problems*, Thm 1.10; Kress, *Numerical Analysis*, Thm 7.3): the `i`-th eigenvalue is the greatest
Rayleigh quotient among the nonzero vectors orthogonal to the eigenvectors for the `i` preceding
eigenvalues, and it is attained at the `i`-th eigenvector.  For `i = 0` the orthogonality
condition is vacuous and this is the largest eigenvalue as a global maximum.

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
eigenvalue of `B` by at most `C`.  This is the quadratic-form hypothesis that Kress's proof of
Weyl's inequality (Kress, *Numerical Analysis*, Cor 7.5) actually uses. -/
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

/-- **Weyl's inequality** (Kress, *Numerical Analysis*, Cor 7.5): the `i`-th eigenvalues of two
symmetric operators differ by at most any bound `C` on the perturbation `A - B`. -/
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

end LinearMap.IsSymmetric
