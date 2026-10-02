import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.Inverse

/-!
# Approximate inverse preconditioners

Instead of factoring `A`, minimize `‖1 - A M‖` over sparse `M` and use `M` itself as the
preconditioner ([saad2003iterative], §10.5). The algorithms of §10.5 are dropping strategies with no
theorem attached; what has content is here:

* the Frobenius objective decouples into one least-squares problem per column of `M`
  (`Preconditioner.frobenius_sq_mul_sub_one_eq_sum`), and a column constrained to a support `J` only
  sees the rows where `A(:, J)` is nonzero (`Preconditioner.isMinOn_submatrix_iff`), which is how
  [saad2003iterative] §10.5.2 and [golub2013matrix] §11.5.5 compute sparse approximate inverses
  column by column;
* the derivative of the least-squares objective, stated in the general Hilbert-space form `d/dm ‖c -
  T m‖² = -2 ⟪c - T m, T ·⟫`, of which [saad2003iterative] `G = -2 Aᵀ R` for the Frobenius inner
  product is the instance — nothing about matrices is needed for the proof, and Mathlib does not
  carry the Frobenius inner product as an inner product space structure anyway;
* nonsingularity from a small residual, which is Neumann's series;
* the sparsity estimate, a Hölder bound on `M = A⁻¹ - A⁻¹ R`: a sufficiently accurate approximate
  inverse has a nonzero pattern containing the large entries of `A⁻¹`, so when those entries are all
  comparable `M` must be as dense as `A⁻¹`;
* the quadratic convergence of the self-preconditioned minimal-residual iteration, which is a
  statement about a normed *ring*: if the next residual is at most `‖(1 - t) R + t R²‖` for every
  `t`, then it is at most `‖R²‖ ≤ ‖R‖²`. That one-line argument, with the residual recurrence `R' =
  (1 - α) R + α R²`, is the entire content of [saad2003iterative] Propositions 10.13 and 10.14, and
  it mentions neither matrices, nor the Frobenius norm, nor sparsity.

The other half of [saad2003iterative] Proposition 10.13 — one self-preconditioned minimal-residual
step reduces the residual by the sine of the angle between `r` and `C r` — is the one-dimensional
minimal-residual step of `Numlib/Projection/OneDimensional`, and is not restated here.
-/

namespace Preconditioner

/-! ### The least-squares objective -/

/-- The derivative of a least-squares objective in a real inner product space: for a continuous
linear `T : F →L[ℝ] G` and a target `c : G`, the map `z ↦ ‖c - T z‖²` has derivative `e ↦ -2 ⟪c - T
m, T e⟫` at `m`, that is, gradient `-2 T† (c - T m)`. [saad2003iterative] Proposition 10.9 is the
instance where `F` and `G` are the matrices with the Frobenius inner product, `T = (A * ·)` and `c =
1`, whose gradient is `-2 Aᵀ (1 - A M)`. -/
theorem hasFDerivAt_normSq_sub_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (T : F →L[ℝ] G) (c : G) (m : F) :
    HasFDerivAt (fun z => ‖c - T z‖ ^ 2)
      ((-2 : ℝ) • (innerSL ℝ (c - T m)).comp T) m := by
  have hf : HasFDerivAt (fun z => c - T z) (-T) m := by
    have h := (hasFDerivAt_const c m).sub T.hasFDerivAt
    rwa [zero_sub] at h
  refine hf.norm_sq.congr_fderiv ?_
  ext e
  simp [two_smul]

/-! ### Nonsingularity from a small residual -/

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- [saad2003iterative] Proposition 10.10: in a normed ring — in particular for matrices under any
submultiplicative norm, the Frobenius norm included — a residual `1 - a m` of norm less than `1`
forces `a m` to be a unit, so `m` is injective and, in finite dimension, invertible. This is
Neumann's series. -/
theorem isUnit_of_norm_one_sub_mul_lt_one {a m : R} (h : ‖1 - a * m‖ < 1) : IsUnit (a * m) := by
  have h' := isUnit_one_sub_of_norm_lt_one h
  rwa [sub_sub_cancel] at h'

/-- The two-sided scaling variant of [saad2003iterative] (10.54): row and column scalings by units
do not change the conclusion, so a small *scaled* residual is just as good. -/
theorem isUnit_of_norm_one_sub_units_mul_lt_one {a m : R} {d₁ d₂ : Rˣ}
    (h : ‖1 - (d₁ : R) * (a * m) * (d₂ : R)‖ < 1) : IsUnit (a * m) :=
  (Units.isUnit_units_mul d₁ _).mp ((Units.isUnit_mul_units _ d₂).mp
    (isUnit_of_norm_one_sub_mul_lt_one h))

/-! ### Quadratic convergence of the self-preconditioned iteration -/

/-- [saad2003iterative] Propositions 10.13 (10.60) and 10.14: if the new residual `r'` is no larger
than `(1 - t) r + t r²` for *every* real `t` — which is what a minimal-residual step in the
direction `M R` achieves, since `(1 - t) R + t R²` is the residual after a step of length `t`
(`Preconditioner.residual_selfPreconditionedStep`) — then `‖r'‖ ≤ ‖r²‖ ≤ ‖r‖²`. The proof is to take
`t = 1`. This is the whole of the quadratic-convergence claim, in both the global and the
column-oriented form; it says nothing about *whether* the iteration converges, only how fast it does
once it does. -/
theorem norm_le_norm_sq_of_isMinOn {S : Type*} [NormedRing S] [NormedSpace ℝ S] {r r' : S}
    (h : ∀ t : ℝ, ‖r'‖ ≤ ‖(1 - t) • r + t • r ^ 2‖) : ‖r'‖ ≤ ‖r‖ ^ 2 := by
  have h1 := h 1
  rw [sub_self, zero_smul, zero_add, one_smul] at h1
  refine h1.trans ?_
  rw [pow_two, pow_two]
  exact norm_mul_le r r

/-- [saad2003iterative] (10.63): the preconditioned matrix `B = A M` of the self-preconditioned step
satisfies `B' = B + α (B (1 - B))`, so it stays a polynomial in `B₀`. In particular a symmetric
`B₀`, as when `M₀ = α₀ Aᵀ`, keeps every `B_k` symmetric. -/
theorem mul_selfPreconditionedStep {S T : Type*} [CommRing S] [Ring T] [Algebra S T]
    (A M : T) (α : S) :
    A * (M + α • (M * (1 - A * M))) = A * M + α • (A * M * (1 - A * M)) := by
  rw [mul_add, mul_smul_comm, ← mul_assoc]

/-- [saad2003iterative] (10.61)–(10.62): the self-preconditioned global minimal-residual step `M' =
M + α (M R)` with `R = 1 - A M` has residual `R' = (1 - α) R + α R²`. Iterating, `R_k` is a
polynomial of degree `2^k` in `R₀`. -/
theorem residual_selfPreconditionedStep {S T : Type*} [CommRing S] [Ring T] [Algebra S T]
    (A M : T) (α : S) :
    1 - A * (M + α • (M * (1 - A * M))) =
      (1 - α) • (1 - A * M) + α • (1 - A * M) ^ 2 := by
  have h2 : A * M * (1 - A * M) = (1 - A * M) - (1 - A * M) * (1 - A * M) := by noncomm_ring
  rw [mul_selfPreconditionedStep, pow_two, h2, smul_sub, sub_smul, one_smul]
  abel

/-! ### The sparsity estimate -/

open scoped Matrix

/-- The estimate behind [saad2003iterative] Proposition 10.11: with `B` a left inverse of `A` and `R
= 1 - A M` the residual, `M = B - B R`, so each entry of `M` differs from the corresponding entry of
`A⁻¹` by at most `(sup over the row of B) * (column sum of |R|)`. -/
theorem abs_sub_inv_apply_le {n : Type*} [Fintype n] [DecidableEq n] {A B M : Matrix n n ℝ}
    (hBA : B * A = 1) (i j : n) :
    |B i j| - (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| ≤ |M i j| := by
  have hBR : B * (1 - A * M) = B - M := by
    rw [mul_sub, mul_one, ← mul_assoc, hBA, one_mul]
  have hM : M i j = B i j - (B * (1 - A * M)) i j := by
    rw [hBR, Matrix.sub_apply, sub_sub_cancel]
  have hbdd : BddAbove (Set.range fun k => |B i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have h1 : |(B * (1 - A * M)) i j| ≤ (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| := by
    rw [Matrix.mul_apply]
    calc |∑ k, B i k * (1 - A * M) k j| ≤ ∑ k, |B i k * (1 - A * M) k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |B i k| * |(1 - A * M) k j| := by simp [abs_mul]
      _ ≤ ∑ k, (⨆ l, |B i l|) * |(1 - A * M) k j| :=
          Finset.sum_le_sum fun k _ => by gcongr; exact le_ciSup hbdd k
      _ = (⨆ l, |B i l|) * ∑ k, |(1 - A * M) k j| := by rw [Finset.mul_sum]
  calc |B i j| - (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j|
      ≤ |B i j| - |(B * (1 - A * M)) i j| := by linarith
    _ ≤ |B i j - (B * (1 - A * M)) i j| := abs_sub_abs_le_abs_sub _ _
    _ = |M i j| := by rw [← hM]

/-- [saad2003iterative] Corollary 10.12: if the `j`-th column of the residual is small in the `ℓ¹`
norm and the entry `B i j` of the inverse is large relative to its own row, then `M i j` cannot
vanish. So a sufficiently accurate approximate inverse must have a nonzero pattern containing the
large entries of `A⁻¹`, and if those are all comparable — as they are for many matrices — `M` must
be as dense as `A⁻¹`. -/
theorem apply_ne_zero_of_abs_lt {n : Type*} [Fintype n] [DecidableEq n] {A B M : Matrix n n ℝ}
    (hBA : B * A = 1) {τ : ℝ} {i j : n} (hτ : ∑ k, |(1 - A * M) k j| ≤ τ)
    (hlt : τ * (⨆ k, |B i k|) < |B i j|) : M i j ≠ 0 := by
  have hbdd : BddAbove (Set.range fun k => |B i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have hnonneg : 0 ≤ ⨆ k, |B i k| := le_trans (abs_nonneg (B i i)) (le_ciSup hbdd i)
  have hmono : (⨆ k, |B i k|) * ∑ k, |(1 - A * M) k j| ≤ (⨆ k, |B i k|) * τ :=
    mul_le_mul_of_nonneg_left hτ hnonneg
  have h := abs_sub_inv_apply_le (M := M) hBA i j
  have hpos : 0 < |M i j| := by
    rw [mul_comm] at hlt
    linarith
  exact fun h0 => absurd h0 (abs_pos.mp hpos)

/-! ### Column decoupling and reduced least squares -/

section Columns

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
/-- **The Frobenius objective decouples into columns** ([golub2013matrix] §11.5.5,
[saad2003iterative] §10.5.2): `‖A M - 1‖_F² = ∑_k ‖A m_k - e_k‖₂²`, with `m_k` the `k`-th column of
`M`. So minimizing `‖A M - 1‖_F` over the matrices with a prescribed pattern is `n` independent
least-squares problems, one per column. -/
theorem frobenius_sq_mul_sub_one_eq_sum (A M : Matrix n n 𝕜) :
    ‖A * M - 1‖ ^ 2 = ∑ k, ‖WithLp.toLp 2 (A *ᵥ (fun i => M i k) - Pi.single k 1)‖ ^ 2 := by
  rw [Matrix.frobenius_norm_sq_eq_sum_norm_sq_col]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]

/-- The residual of a vector supported in `J` splits into the residual of the reduced problem on
the rows `I` and the part of the right side outside `I`, when every row reached by a column of `J`
is in `I`. -/
private theorem norm_sq_mulVec_sub_eq {A : Matrix n n 𝕜} {c : n → 𝕜} {I J : Finset n}
    (hI : ∀ i, ∀ j ∈ J, A i j ≠ 0 → i ∈ I) {x : n → 𝕜} (hx : ∀ j ∉ J, x j = 0) :
    ‖WithLp.toLp 2 (A *ᵥ x - c)‖ ^ 2 =
      ‖WithLp.toLp 2 (A.submatrix ((↑) : I → n) ((↑) : J → n) *ᵥ (fun j : J => x j) -
        fun i : I => c i)‖ ^ 2 + ∑ i ∈ Iᶜ, ‖c i‖ ^ 2 := by
  have hAx : ∀ i, (A *ᵥ x) i = ∑ j : J, A i j * x j := by
    intro i
    rw [Matrix.mulVec, dotProduct, Finset.sum_coe_sort J (fun j => A i j * x j)]
    exact (Finset.sum_subset (Finset.subset_univ J) fun j _ hj => by rw [hx j hj, mul_zero]).symm
  have hout : ∀ i ∉ I, (A *ᵥ x) i = 0 := by
    intro i hi
    rw [hAx]
    exact Finset.sum_eq_zero fun j _ => by
      rw [show A i j = 0 by by_contra h; exact hi (hI i j j.2 h), zero_mul]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← Finset.sum_add_sum_compl I]
  congr 1
  · rw [← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hAx i
    simp only [Matrix.mulVec, dotProduct] at hi
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [PiLp.toLp_apply, Pi.sub_apply, hout i (Finset.mem_compl.mp hi), zero_sub, norm_neg]

omit [DecidableEq n] in
/-- **Reduced least squares** ([golub2013matrix] §11.5.5, [saad2003iterative] §10.5.2): let `J` be
the allowed support of a column and `I` a set of rows containing every row `i` with `A i j ≠ 0` for
some `j ∈ J`. Then `τ` minimizes the small problem `‖A(I, J) τ - c(I)‖₂` exactly when its extension
by zero (`Function.extend Subtype.val τ 0`) minimizes `‖A x - c‖₂` over the vectors `x` supported in
`J`: the two objectives differ by the constant `‖c(Iᶜ)‖₂²`. -/
theorem isMinOn_submatrix_iff {A : Matrix n n 𝕜} {c : n → 𝕜} {I J : Finset n}
    (hI : ∀ i, ∀ j ∈ J, A i j ≠ 0 → i ∈ I) {τ : J → 𝕜} :
    IsMinOn (fun σ : J → 𝕜 => ‖WithLp.toLp 2 (A.submatrix ((↑) : I → n) ((↑) : J → n) *ᵥ σ -
        fun i : I => c i)‖) Set.univ τ ↔
      IsMinOn (fun x : n → 𝕜 => ‖WithLp.toLp 2 (A *ᵥ x - c)‖) {x | ∀ j ∉ J, x j = 0}
        (Function.extend Subtype.val τ 0) := by
  classical
  set ext : (J → 𝕜) → n → 𝕜 := fun σ => Function.extend Subtype.val σ 0 with hext
  have hsupp : ∀ σ, ∀ j ∉ J, ext σ j = 0 := fun σ j hj => by
    simp only [hext, Function.extend_val_apply' (p := (· ∈ J)) hj, Pi.zero_apply]
  have hres : ∀ σ, (fun j : J => ext σ j) = σ := fun σ => funext fun j => by
    simp only [hext, Function.extend_val_apply (p := (· ∈ J)) j.2]
  simp only [isMinOn_iff, Set.mem_univ, Set.mem_ofPred_eq, forall_const]
  constructor
  · intro h x hx
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_mulVec_sub_eq hI (hsupp τ),
      norm_sq_mulVec_sub_eq hI hx, hres]
    gcongr
    exact h _
  · intro h σ
    have h' := h (ext σ) (hsupp σ)
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_mulVec_sub_eq hI (hsupp τ),
      norm_sq_mulVec_sub_eq hI (hsupp σ), hres, hres] at h'
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    linarith

end Columns

end Preconditioner
