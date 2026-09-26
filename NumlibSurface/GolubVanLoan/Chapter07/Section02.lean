import Mathlib.Analysis.Matrix.Order
import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.Perturbation
import NumlibSurface.GolubVanLoan.Chapter07.Section01

/-!
# Golub–Van Loan §7.2: perturbation theory

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.2: Gershgorin's theorem for a similarity transform (Theorem 7.2.1) and its
isolated discs, the Bauer–Fike theorem in every `p`-norm (Theorem 7.2.2), the resolvent step
(7.2.1) behind Theorems 7.2.1–7.2.3, the Schur-form bound (Theorem 7.2.3), the condition `1/s(λ)`
of a simple eigenvalue ((7.2.2) and its first-order derivation), the `2 × 2` repeated-eigenvalue
example (§7.2.3), the separation (7.2.5), Stewart's invariant-subspace perturbation theorem
(Theorem 7.2.4) with (7.2.6) and Corollary 7.2.5, and eigenvector sensitivity (Corollary 7.2.6,
`sep(λ, T₂₂) = σ_min(T₂₂ - λI)`).

## Conventions

Complex, `A : Matrix (Fin n) (Fin n) ℂ`, as in §7.1 (`GolubVanLoan.Chapter07.Section01`). The
2-norm is the scoped `Matrix.Norms.L2Operator` norm and the Frobenius norm the scoped
`Matrix.Norms.Frobenius` norm, each opened in its own section. A right eigenvector is
`A *ᵥ x = λ • x`, a left eigenvector `star y ᵥ* A = λ • star y` (the book's `yᴴ A = λ yᴴ`), and unit
length is `‖WithLp.toLp 2 x‖ = 1`. The separation `sep(T₁₁, T₂₂)` is the backbone's `Matrix.sep`.
For Theorem 7.2.4 the index type is `Fin r ⊕ Fin s` (`s = n - r`), so that `Q = [Q₁ Q₂]` and the
blocks of `Qᴴ A Q` are `Matrix.fromBlocks`; for Corollary 7.2.6 it is `Unit ⊕ Fin s`. The inverse
square root `(I + Pᴴ P)^{-1/2}` is `(CFC.sqrt (1 + Pᴴ * P))⁻¹` (scoped `MatrixOrder`), the
distance of two subspaces the gap `Submodule.gap`, and where the 2-norm and the Frobenius norm meet
in one statement the 2-norm is `Matrix.lpOpNorm 2`.

## Sources

`Numlib/Eigen/Perturbation` (Gershgorin, Bauer–Fike, the resolvent step, Theorem 7.2.3, the
eigenvalue condition number and the differentiable eigenvalue branch),
`Numlib/LinearAlgebra/Matrix/Sylvester` (`sep`), `Numlib/Eigen/InvariantSubspace` (Stewart's
invariant graph `Matrix.exists_invariant_graph_of_sep`, the gap of a graph
`Matrix.gap_range_fromRows_le`).

## Not formalized

Wilkinson's nearest-multiple-eigenvalue bound `‖E‖₂/‖A‖₂ ≤ s(λ)/√(1 - s(λ)²)` (quoted from
Wilkinson 1972 without proof or construction of `E`); the heuristic "`O(ε)` perturbations can move a
defective eigenvalue by `O(ε^{1/p})`" (its rigorous content is Theorem 7.2.3's `θ^{1/p}`); the
"wobbly eigenvectors" discussion.
-/

open Matrix Polynomial Filter Topology Metric

namespace GolubVanLoan.Chapter07

variable {n : ℕ}

/-! ### §7.2.1 Eigenvalue sensitivity -/

/-- The diagonal of `diag(d) + F` is `d` when `F` has zero diagonal. -/
private theorem diagonal_add_apply_self {d : Fin n → ℂ} {F : Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i, F i i = 0) (i : Fin n) : (diagonal d + F) i i = d i := by
  simp [hF i]

/-- The off-diagonal absolute row sums of `diag(d) + F` are the absolute row sums of `F`. -/
private theorem sum_erase_norm_diagonal_add {d : Fin n → ℂ} {F : Matrix (Fin n) (Fin n) ℂ}
    (hF : ∀ i, F i i = 0) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, ‖(diagonal d + F) i j‖ = ∑ j, ‖F i j‖ := by
  rw [← Finset.add_sum_erase _ (fun j => ‖F i j‖) (Finset.mem_univ i), hF i, norm_zero,
    zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Matrix.add_apply, diagonal_apply_ne _ (Finset.ne_of_mem_erase hj).symm, zero_add]

/-- A similarity preserves the spectrum (Section 1's `spectrum_subset_of_mul_eq_mul`). -/
private theorem spectrum_conj {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) :
    spectrum ℂ (X⁻¹ * A * X) = spectrum ℂ A :=
  (spectrum_subset_of_mul_eq_mul (X := (1 : Matrix (Fin n) (Fin n) ℂ)) (B := A)
    (by rw [Matrix.mul_one, Matrix.one_mul])).2.2.2 X hX

/-- **Theorem 7.2.1 (Gershgorin circle theorem).** If `X⁻¹ A X = D + F` with
`D = diag(d₁, …, dₙ)` and `F` of zero diagonal, then `λ(A) ⊆ ⋃ D_i` with
`D_i = {z : |z - d_i| ≤ ∑_j |f_ij|}`. -/
theorem theorem_7_2_1 {A X F : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = diagonal d + F) (hF : ∀ i, F i i = 0) :
    spectrum ℂ A ⊆ ⋃ i, closedBall (d i) (∑ j, ‖F i j‖) := by
  rw [← spectrum_conj hX, h]
  intro μ hμ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (spectrum_subset_iUnion_closedBall _ hμ)
  rw [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF] at hi
  exact Set.mem_iUnion.2 ⟨i, hi⟩

/-- **§7.2.1: "if the Gershgorin disk `D_i` is isolated from the other disks, then it contains
precisely one eigenvalue of `A`"**, counted with multiplicity: with the notation of Theorem 7.2.1,
if `D_i` is disjoint from the union of the other discs then exactly one root of the characteristic
polynomial of `A` lies in `D_i`. -/
theorem gershgorin_isolated {A X F : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = diagonal d + F) (hF : ∀ i, F i i = 0) (i : Fin n)
    (hdisj : Disjoint (closedBall (d i) (∑ j, ‖F i j‖))
      (⋃ k ∈ ({i} : Finset (Fin n))ᶜ, closedBall (d k) (∑ j, ‖F k j‖))) :
    A.charpoly.countRootsIn (closedBall (d i) (∑ j, ‖F i j‖)) = 1 := by
  have hsim : IsSimilar A (diagonal d + F) := ⟨X, hX, h.symm⟩
  rw [hsim.charpoly_eq]
  refine card_spectrum_of_isolated_gershgorin (diagonal d + F) i
    (S' := ⋃ k ∈ ({i} : Finset (Fin n))ᶜ, closedBall (d k) (∑ j, ‖F k j‖)) ?_ ?_ ?_
  · rw [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF]
  · simp only [diagonal_add_apply_self hF, sum_erase_norm_diagonal_add hF]
  · exact hdisj

/-- **Theorem 7.2.2 (Bauer–Fike).** "If `μ` is an eigenvalue of `A + E ∈ ℂ^{n×n}` and
`X⁻¹ A X = D = diag(λ₁, …, λₙ)`, then `min_{λ ∈ λ(A)} |λ - μ| ≤ κ_p(X) ‖E‖_p` where `‖·‖_p` denotes
any of the `p`-norms." With `p : ℝ≥0∞`, `1 ≤ p`: the backbone's `Matrix.bauer_fike_lpOpNorm` for
`A = X D X⁻¹`. -/
theorem theorem_7_2_2 (p : ENNReal) [Fact (1 ≤ p)] {A X E : Matrix (Fin n) (Fin n) ℂ}
    {d : Fin n → ℂ} (hX : IsUnit X) (hXA : X⁻¹ * A * X = diagonal d) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖d i - μ‖ ≤ condNumberLp p X * lpOpNorm p E := by
  have hdet := (isUnit_iff_isUnit_det X).1 hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hXA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul,
      Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
  obtain ⟨i, hi⟩ := bauer_fike_lpOpNorm p X d hX E (hA ▸ hμ)
  exact ⟨i, by rwa [norm_sub_rev]⟩

section L2

open scoped Matrix.Norms.L2Operator

/-- **(7.2.1)**, the step shared by Theorems 7.2.1–7.2.3 (the book's appeal to its Lemma 2.3.3): if
`μ ∈ λ(A + E)` and `μ ∉ λ(A)` then `1 ≤ ‖(μI - A)⁻¹ E‖₂ ≤ ‖(μI - A)⁻¹‖₂ ‖E‖₂`. -/
theorem equation_7_2_1 {A E : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E))
    (hA : μ ∉ spectrum ℂ A) :
    1 ≤ ‖(μ • 1 - A)⁻¹ * E‖ ∧ ‖(μ • 1 - A)⁻¹ * E‖ ≤ ‖(μ • 1 - A)⁻¹‖ * ‖E‖ :=
  ⟨one_le_norm_mul_of_mem_spectrum_add hμ hA, norm_mul_le _ _⟩

/-- **Theorem 7.2.3.** Let `Qᴴ A Q = D + N` be a Schur decomposition, `μ ∈ λ(A + E)`, and `p ≥ 1`
with `|N|^p = 0` (entrywise absolute value; the book takes the least such `p`, which only improves
the bound). Then `min_{λ ∈ λ(A)} |λ - μ| ≤ max(θ, θ^{1/p})` with
`θ = ‖E‖₂ ∑_{k=0}^{p-1} ‖N‖₂^k`. (The strict upper triangularity of `N` is not needed.) -/
theorem theorem_7_2_3 {A Q N E : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ}
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (hQA : star Q * A * Q = diagonal d + N) {p : ℕ}
    (hp : 1 ≤ p) (hN : (N.map (‖·‖)) ^ p = 0) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖d i - μ‖ ≤
      max (‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k)
        ((‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k) ^ (1 / p : ℝ)) := by
  obtain ⟨i, hi⟩ := infDist_spectrum_le_of_schur hQ hQA hp hN E hμ
  exact ⟨i, by rwa [norm_sub_rev]⟩

end L2

/-! ### §7.2.2 The condition of a simple eigenvalue -/

/-- **(7.2.2): `s(λ) = |yᴴ x|`**, for unit right and left eigenvectors `x`, `y` of a simple
eigenvalue `λ`; the condition of `λ` is `1/s(λ)`. For unit vectors this is the reciprocal of the
backbone's eigenvalue condition number (`eigenvalueSensitivity_eq_inv_eigenvalueCondNumber`). -/
noncomputable def eigenvalueSensitivity (x y : Fin n → ℂ) : ℝ :=
  ‖star y ⬝ᵥ x‖

/-- For unit `x`, `y`, `s(λ)` is the reciprocal of the backbone's condition number
`‖x‖ ‖y‖ / |⟪y, x⟫|`. -/
theorem eigenvalueSensitivity_eq_inv_eigenvalueCondNumber {x y : Fin n → ℂ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) :
    eigenvalueSensitivity x y =
      (Module.End.eigenvalueCondNumber ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y))⁻¹ := by
  rw [Module.End.eigenvalueCondNumber, hx, hy, EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
    eigenvalueSensitivity]
  simp

/-- A left eigenvector tests the image of `A` as it tests the vector: `⟪y, A z⟫ = λ ⟪y, z⟫`. -/
private theorem inner_toEuclideanLin_of_left {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    {y : Fin n → ℂ} (hy : star y ᵥ* A = μ • star y) (z : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (WithLp.toLp 2 y) (toEuclideanLin A z) : ℂ) = μ * inner ℂ (WithLp.toLp 2 y) z := by
  obtain ⟨z, rfl⟩ : ∃ z', z = WithLp.toLp 2 z' := ⟨WithLp.ofLp z, (WithLp.toLp_ofLp _ _).symm⟩
  rw [toLpLin_toLp, toLin'_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, dotProduct_comm, dotProduct_mulVec, hy, smul_dotProduct,
    smul_eq_mul, dotProduct_comm]

/-- The right eigenvector equation in `EuclideanSpace`. -/
private theorem toEuclideanLin_of_right {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} {x : Fin n → ℂ}
    (hx : A *ᵥ x = μ • x) : toEuclideanLin A (WithLp.toLp 2 x) = μ • WithLp.toLp 2 x := by
  rw [toLpLin_toLp, toLin'_apply, hx, WithLp.toLp_smul]

/-- A simple eigenvalue has a one-dimensional generalized eigenspace. -/
private theorem finrank_maxGenEigenspace_of_simple {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : IsSimpleEigenvalue A μ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace (toEuclideanLin A) μ) = 1 := by
  rw [finrank_maxGenEigenspace_toEuclideanLin]
  exact hμ

/-- **§7.2.2: `yᴴ x ≠ 0` for a simple eigenvalue**, so `s(λ) > 0`. The book's argument through the
Jordan form is replaced by the backbone's: the generalized eigenspace of a simple eigenvalue is a
line. -/
theorem inner_ne_zero_of_simple {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : IsSimpleEigenvalue A μ) {x y : Fin n → ℂ} (hx : A *ᵥ x = μ • x) (hx0 : x ≠ 0)
    (hy : star y ᵥ* A = μ • star y) (hy0 : y ≠ 0) : star y ⬝ᵥ x ≠ 0 := by
  have h := Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one
    (toEuclideanLin_of_right hx) (by simpa using hx0) (inner_toEuclideanLin_of_left hy)
    (by simpa using hy0) (finrank_maxGenEigenspace_of_simple hμ)
  rwa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h

section L2

open scoped Matrix.Norms.L2Operator

/-- **§7.2.2, the derivation of (7.2.2), rigorous.** For a simple eigenvalue `λ` of `A` with unit
right and left eigenvectors `x`, `y` and any `F`, there are an eigenvalue branch `λ(ε)` and an
eigenvector branch `x(ε)` of `A + εF` through `(λ, x)`, differentiable at `0`, with
`λ'(0) = yᴴ F x / yᴴ x`, so `|λ'(0)| ≤ ‖F‖₂ / s(λ)` (the book's `1/s(λ)` for `‖F‖₂ = 1`). The bound
is attained for `F = y xᴴ`, which has `‖F‖₂ = 1`. -/
theorem equation_7_2_2 {A F : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} (hμ : IsSimpleEigenvalue A μ)
    {x y : Fin n → ℂ} (hx : A *ᵥ x = μ • x) (hxn : ‖WithLp.toLp 2 x‖ = 1)
    (hy : star y ᵥ* A = μ • star y) (hyn : ‖WithLp.toLp 2 y‖ = 1) :
    (∃ (lam : ℂ → ℂ) (v : ℂ → EuclideanSpace ℂ (Fin n)) (lam' : ℂ), lam 0 = μ ∧
      v 0 = WithLp.toLp 2 x ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), toEuclideanLin (A + t • F) (v t) = lam t • v t) ∧
      DifferentiableAt ℂ v 0 ∧ HasDerivAt lam lam' 0 ∧
      lam' = (star y ⬝ᵥ (F *ᵥ x)) / (star y ⬝ᵥ x) ∧
      ‖lam'‖ ≤ ‖F‖ / eigenvalueSensitivity x y) ∧
    ‖vecMulVec y (star x)‖ = 1 ∧
      ‖(star y ⬝ᵥ (vecMulVec y (star x) *ᵥ x)) / (star y ⬝ᵥ x)‖ =
        1 / eigenvalueSensitivity x y := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxn
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyn
  have hne := inner_ne_zero_of_simple hμ hx hx0 hy hy0
  set A' := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  set B' := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) F
  have hAu : A' (WithLp.toLp 2 x) = μ • WithLp.toLp 2 x := toEuclideanLin_of_right hx
  have hw : ∀ z, (inner ℂ (WithLp.toLp 2 y) (A' z) : ℂ) = μ * inner ℂ (WithLp.toLp 2 y) z :=
    inner_toEuclideanLin_of_left hy
  have hinner : (inner ℂ (WithLp.toLp 2 y) (WithLp.toLp 2 x) : ℂ) = star y ⬝ᵥ x := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have hinnerF : (inner ℂ (WithLp.toLp 2 y) (B' (WithLp.toLp 2 x)) : ℂ) =
      star y ⬝ᵥ (F *ᵥ x) := by
    rw [toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  -- the norm of the rank-one `y xᴴ`
  have hrank : ‖vecMulVec y (star x)‖ = 1 := by
    rw [← l2_opNorm_toEuclideanCLM]
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_) ?_
    · obtain ⟨z, rfl⟩ : ∃ z', z = WithLp.toLp 2 z' := ⟨WithLp.ofLp z, (WithLp.toLp_ofLp _ _).symm⟩
      rw [toEuclideanCLM_toLp, vecMulVec_mulVec, op_smul_eq_smul, WithLp.toLp_smul, norm_smul,
        hyn, mul_one, one_mul]
      have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x) (WithLp.toLp 2 z)
      rw [hxn, one_mul, EuclideanSpace.inner_toLp_toLp] at h
      simpa [dotProduct_comm] using h
    · have h := (toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (vecMulVec y (star x))).le_opNorm
        (WithLp.toLp 2 x)
      rw [toEuclideanCLM_toLp, vecMulVec_mulVec, op_smul_eq_smul, WithLp.toLp_smul, norm_smul,
        hyn, mul_one, hxn, mul_one] at h
      have hxx : star x ⬝ᵥ x = 1 := by
        have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 x)
        rw [hxn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
        simpa using h'
      rwa [hxx, norm_one] at h
  refine ⟨?_, hrank, ?_⟩
  · obtain ⟨lam, v, v', h0, hv0, hev, hv, hlam⟩ :=
      Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one (A := A') (B := B') hAu
        (by simpa using hx0) hw (by simpa using hy0) (finrank_maxGenEigenspace_of_simple hμ)
    refine ⟨lam, v, _, h0, hv0, ?_, hv.differentiableAt, hlam, by rw [hinnerF, hinner], ?_⟩
    · filter_upwards [hev] with t ht
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      exact ht
    · rw [hinnerF, hinner, norm_div, eigenvalueSensitivity, ← l2_opNorm_toEuclideanCLM]
      have hpos : 0 < ‖star y ⬝ᵥ x‖ := norm_pos_iff.2 hne
      rw [div_le_div_iff_of_pos_right hpos]
      calc ‖star y ⬝ᵥ (F *ᵥ x)‖ = ‖(inner ℂ (WithLp.toLp 2 y) (B' (WithLp.toLp 2 x)) : ℂ)‖ := by
            rw [hinnerF]
        _ ≤ ‖WithLp.toLp 2 y‖ * ‖B' (WithLp.toLp 2 x)‖ := norm_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 y‖ * (‖B'‖ * ‖WithLp.toLp 2 x‖) := by
            gcongr
            exact B'.le_opNorm _
        _ = ‖B'‖ := by rw [hxn, hyn, one_mul, mul_one]
  · have hxx : star x ⬝ᵥ x = 1 := by
      have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 x)
      rw [hxn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
      simpa using h'
    have hyy : star y ⬝ᵥ y = 1 := by
      have h' := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 y)
      rw [hyn, EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h'
      simpa using h'
    rw [vecMulVec_mulVec, op_smul_eq_smul, hxx, one_smul, hyy, norm_div, norm_one,
      eigenvalueSensitivity]

end L2

/-! ### §7.2.3 Sensitivity of repeated eigenvalues -/

/-- **§7.2.3.** For `A = [1 a; 0 1]` and `F = [0 0; 1 0]`, `λ(A + εF) = {z : (z - 1)² = ε a}` (the
book's `{1 ± √(εa)}`), and for `a ≠ 0` no branch of eigenvalues is differentiable at `ε = 0` — the
rigorous form of "their rate of change at the origin is infinite": a differentiable `z(ε)` with
`(z(ε) - 1)² = εa` would give `a = 2 (z(0) - 1) z'(0) = 0`. -/
theorem repeated_eigenvalue_example (a : ℂ) :
    (∀ ε : ℂ, spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0]) = {z | (z - 1) ^ 2 = ε * a}) ∧
    (a ≠ 0 → ∀ f : ℂ → ℂ,
      (∀ᶠ ε in 𝓝 (0 : ℂ), f ε ∈ spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0])) →
        ¬ DifferentiableAt ℂ f 0) := by
  have hspec : ∀ ε : ℂ,
      spectrum ℂ (!![1, a; 0, 1] + ε • !![0, 0; 1, 0]) = {z | (z - 1) ^ 2 = ε * a} := by
    intro ε
    ext z
    rw [Set.mem_ofPred_eq, spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
      isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not, det_fin_two]
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, one_apply_eq,
      one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      smul_eq_mul]
    constructor <;> intro h <;> linear_combination h
  refine ⟨hspec, fun ha f hf hd => ha ?_⟩
  have hev : (fun ε => (f ε - 1) ^ 2) =ᶠ[𝓝 (0 : ℂ)] fun ε => ε * a :=
    hf.mono fun ε hε => by rw [hspec] at hε; exact hε
  have h0 : f 0 - 1 = 0 := by
    have := hev.eq_of_nhds
    simpa using this
  have h1 : HasDerivAt (fun ε => (f ε - 1) ^ 2) (↑2 * (f 0 - 1) ^ (2 - 1) * deriv f 0) 0 :=
    (hd.hasDerivAt.sub_const 1).pow 2
  have h2 : HasDerivAt (fun ε => (f ε - 1) ^ 2) a 0 := by
    have h3 : HasDerivAt (fun ε : ℂ => ε * a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const a
    exact h3.congr_of_eventuallyEq hev
  have := h1.unique h2
  rw [h0] at this
  simpa using this.symm

/-! ### §7.2.4 Invariant subspace sensitivity -/

section Frobenius

open scoped Matrix.Norms.Frobenius

/-- **(7.2.5): `sep(T₁₁, T₂₂) = min_{X ≠ 0} ‖T₁₁ X - X T₂₂‖_F / ‖X‖_F`**: the backbone's
`Matrix.sep` (the least value of `‖T₁₁ X - X T₂₂‖_F` on the Frobenius unit sphere) is the least
value of the book's quotient over nonzero `X`, and it is attained. -/
theorem equation_7_2_5 {p q : ℕ} [NeZero p] [NeZero q] (T₁₁ : Matrix (Fin p) (Fin p) ℂ)
    (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    IsLeast {r | ∃ X : Matrix (Fin p) (Fin q) ℂ, X ≠ 0 ∧ ‖T₁₁ * X - X * T₂₂‖ / ‖X‖ = r}
      (sep T₁₁ T₂₂) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨X, hX, hXs⟩ := exists_sep_eq T₁₁ T₂₂
    refine ⟨X, fun h0 => by simp [h0] at hX, ?_⟩
    rw [hX, div_one, hXs]
  · rintro r ⟨X, hX, rfl⟩
    rw [le_div_iff₀ (norm_pos_iff.2 hX)]
    exact sep_mul_norm_le X

end Frobenius

/-! ### §7.2.4–7.2.5 Invariant subspace and eigenvector sensitivity -/

/-- **§7.2.5**: "if `T₁₁ = λ`, then `sep(T₁₁, T₂₂) = σ_min(T₂₂ - λI)`" (the observation in the
proof of Corollary 7.2.6), and "`sep(λ, T₂₂) = σ_min(T₂₂ - λI) ≤ min_{μ ∈ λ(T₂₂)} |μ - λ|`". The
`1 × 1` block `λ` is `of fun _ _ => c` on `Unit`, `σ_min` the least column-indexed singular value
(`Matrix.sep_eq_iInf_singularValues`, `Matrix.sep_le_norm_sub`). -/
theorem sep_one_eq_sigmaMin {q : ℕ} (c : ℂ) (T₂₂ : Matrix (Fin q) (Fin q) ℂ) :
    sep (of fun _ _ => c : Matrix Unit Unit ℂ) T₂₂ = ⨅ i, (T₂₂ - c • 1).singularValues i ∧
      ∀ μ ∈ spectrum ℂ T₂₂, sep (of fun _ _ => c : Matrix Unit Unit ℂ) T₂₂ ≤ ‖μ - c‖ := by
  refine ⟨sep_eq_iInf_singularValues c T₂₂, fun μ hμ => ?_⟩
  have hc : c ∈ spectrum ℂ (of fun _ _ => c : Matrix Unit Unit ℂ) := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    have h0 : c • (1 : Matrix Unit Unit ℂ) - of (fun _ _ => c) = 0 := by
      ext i j
      simp
    rw [h0]
    exact not_isUnit_zero
  rw [norm_sub_rev]
  exact sep_le_norm_sub hc hμ

section Stewart

open scoped ComplexOrder MatrixOrder

variable {r s : ℕ}

/-- The facts about `S = (I + Pᴴ P)^{1/2}` behind Theorem 7.2.4: `S² = I + Pᴴ P`, `S` Hermitian and
nonsingular. -/
theorem sqrt_one_add_conjTranspose_mul_self {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ) :
    CFC.sqrt (1 + Pᴴ * P) * CFC.sqrt (1 + Pᴴ * P) = 1 + Pᴴ * P ∧
      (CFC.sqrt (1 + Pᴴ * P))ᴴ = CFC.sqrt (1 + Pᴴ * P) ∧
      IsUnit (CFC.sqrt (1 + Pᴴ * P)).det := by
  have hpd : (1 + Pᴴ * P).PosDef :=
    PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P)
  have hnn : 0 ≤ 1 + Pᴴ * P := nonneg_iff_posSemidef.2 hpd.posSemidef
  have hSS := CFC.sqrt_mul_sqrt_self _ hnn
  refine ⟨hSS, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 + Pᴴ * P))).star_eq, ?_⟩
  have h : IsUnit (CFC.sqrt (1 + Pᴴ * P) * CFC.sqrt (1 + Pᴴ * P)).det := by
    rw [hSS]
    exact (isUnit_iff_isUnit_det _).1 hpd.isUnit
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- `‖y‖ ≤ ‖(I + Pᴴ P)^{1/2} y‖`: the square of the right side is `‖y‖² + ‖P y‖²`. -/
private theorem norm_le_norm_sqrt_apply {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ)
    (y : EuclideanSpace ℂ (Fin r)) :
    ‖y‖ ≤ ‖toEuclideanLin (CFC.sqrt (1 + Pᴴ * P)) y‖ := by
  obtain ⟨hSS, hSh, -⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  have h1 : (inner ℂ (toEuclideanLin S y) (toEuclideanLin S y) : ℂ) =
      inner ℂ y y + inner ℂ (toEuclideanLin P y) (toEuclideanLin P y) := by
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint, hSh,
      ← toEuclideanLin_mul_apply, hSS, map_add, LinearMap.add_apply, toEuclideanLin_one_apply,
      inner_add_right, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖toEuclideanLin S y‖ ^ 2 = ‖y‖ ^ 2 + ‖toEuclideanLin P y‖ ^ 2 := by
    exact_mod_cast h1
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
    (by nlinarith [sq_nonneg ‖toEuclideanLin P y‖])

open scoped Matrix.Norms.Frobenius in
/-- **(7.2.6)**: "Using the SVD of `P`, it can be shown that
`‖P (I + Pᴴ P)^{-1/2}‖₂ ≤ ‖P‖₂ ≤ ‖P‖_F`" — here without the SVD: with `S = (I + Pᴴ P)^{1/2}`
(`CFC.sqrt`), `‖S y‖² = ‖y‖² + ‖P y‖²`, so `S⁻¹` does not increase norms. The 2-norm is
`lpOpNorm 2`, the Frobenius norm the scoped one. -/
theorem equation_7_2_6 {k : ℕ} (P : Matrix (Fin k) (Fin r) ℂ) :
    lpOpNorm 2 (P * (CFC.sqrt (1 + Pᴴ * P))⁻¹) ≤ lpOpNorm 2 P ∧ lpOpNorm 2 P ≤ ‖P‖ := by
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg 2 P) fun x => ?_,
    l2_opNorm_le_frobenius_norm P⟩
  obtain ⟨-, -, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  set y : EuclideanSpace ℂ (Fin r) := toEuclideanLin S⁻¹ x with hy
  have hx : toEuclideanLin S y = x := by
    rw [hy, ← toEuclideanLin_mul_apply, mul_nonsing_inv _ hSdet, toEuclideanLin_one_apply]
  have happ : lpCLM 2 (P * S⁻¹) x = lpCLM 2 P y := by
    rw [lpCLM_apply, lpCLM_apply, ← mulVec_mulVec]
    rfl
  rw [happ]
  calc ‖lpCLM 2 P y‖ ≤ lpOpNorm 2 P * ‖y‖ := (lpCLM 2 P).le_opNorm y
    _ ≤ lpOpNorm 2 P * ‖x‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (lpOpNorm_nonneg 2 P)
        conv_rhs => rw [← hx]
        exact norm_le_norm_sqrt_apply P y

/-- **The book's `Q̃₁ = (Q₁ + Q₂ P)(I + Pᴴ P)^{-1/2}`** of Theorem 7.2.4, for `Q = [Q₁ Q₂]` with
`Q₁ = Q [I; 0]` (the first `r` columns) and `Q₂ = Q [0; I]`. -/
noncomputable def stewartBasis (Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)
    (P : Matrix (Fin s) (Fin r) ℂ) : Matrix (Fin r ⊕ Fin s) (Fin r) ℂ :=
  (Q * fromRows (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin s) (Fin r) ℂ) +
    Q * fromRows (0 : Matrix (Fin r) (Fin s) ℂ) (1 : Matrix (Fin s) (Fin s) ℂ) * P) *
      (CFC.sqrt (1 + Pᴴ * P))⁻¹

/-- `Q̃₁ = Q [I; P] (I + Pᴴ P)^{-1/2}`. -/
theorem stewartBasis_eq (Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)
    (P : Matrix (Fin s) (Fin r) ℂ) :
    stewartBasis Q P = Q * fromRows 1 P * (CFC.sqrt (1 + Pᴴ * P))⁻¹ := by
  rw [stewartBasis, Matrix.mul_assoc Q (fromRows 0 1), ← Matrix.mul_add, fromRows_mul,
    Matrix.zero_mul, Matrix.one_mul]
  congr 2
  ext (i | i) j <;> simp

/-- The range of `Q M` is the image of the range of `M` under the isometry `Q`. -/
private theorem range_unitary_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Q : Matrix ι ι ℂ} (hQ : Q ∈ unitaryGroup ι ℂ) (M : Matrix ι κ ℂ) :
    LinearMap.range (toEuclideanLin (Q * M)) = (LinearMap.range (toEuclideanLin M)).map
      ((unitaryLinearIsometryEquiv hQ).toLinearEquiv : EuclideanSpace ℂ ι →ₗ[ℂ] _) := by
  rw [← LinearMap.range_comp]
  congr 1
  exact LinearMap.ext fun y => by
    rw [toEuclideanLin_mul_apply, LinearMap.comp_apply]
    rfl

/-- **Corollary 7.2.5's estimate in the coordinates of `Q`**: the gap between the ranges of
`Q [I; 0]` and `Q [I; P]` is at most `‖P‖₂`. -/
private theorem gap_range_unitary_mul_fromRows_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Q : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ} (hQ : Q ∈ unitaryGroup (ι ⊕ κ) ℂ)
    (P : Matrix κ ι ℂ) :
    (LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix ι ι ℂ) (0 : Matrix κ ι ℂ)))).gap
      (LinearMap.range (toEuclideanLin (Q * fromRows 1 P))) ≤ lpOpNorm 2 P := by
  simp only [range_unitary_mul hQ]
  rw [Submodule.gap_map_linearIsometryEquiv]
  exact gap_range_fromRows_le P

/-- An invariant graph in the coordinates of a unitary `Q` is an invariant subspace of `A + E`: if
`Qᴴ A Q = B` and `(B + Qᴴ E Q) X = X M`, then `(A + E) (Q X) = (Q X) M`. -/
private theorem mul_unitary_mul_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {A E Q B : Matrix ι ι ℂ} (hQ : Q ∈ unitaryGroup ι ℂ) (hT : star Q * A * Q = B)
    {X : Matrix ι κ ℂ} {M : Matrix κ κ ℂ} (hX : (B + star Q * E * Q) * X = X * M) :
    (A + E) * (Q * X) = Q * X * M := by
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.1 hQ
  have hAE : A + E = Q * (B + star Q * E * Q) * star Q := by
    rw [← hT, ← Matrix.add_mul, ← Matrix.mul_add]
    simp only [← Matrix.mul_assoc]
    rw [hQQ, Matrix.one_mul, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [hAE, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (star Q) Q, hQQ',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hX, ← Matrix.mul_assoc]

open scoped Matrix.Norms.Frobenius

/-- **Theorem 7.2.4 (Stewart).** "Suppose that (7.2.3) and (7.2.4) hold and that for any matrix
`E ∈ ℂ^{n×n}` we partition `Qᴴ E Q` as `[E₁₁ E₁₂; E₂₁ E₂₂]`. If `sep(T₁₁, T₂₂) > 0` and
`‖E‖_F (1 + 5 ‖T₁₂‖_F / sep(T₁₁, T₂₂)) ≤ sep(T₁₁, T₂₂)/5`, then there exists a
`P ∈ ℂ^{(n-r)×r}` with `‖P‖_F ≤ 4 ‖E₂₁‖_F / sep(T₁₁, T₂₂)` such that the columns of
`Q̃₁ = (Q₁ + Q₂ P)(I + Pᴴ P)^{-1/2}` are an orthonormal basis for a subspace invariant for `A + E`."
On `Fin r ⊕ Fin s` (`s = n - r`), `Q` unitary with `Qᴴ A Q = [T₁₁ T₁₂; 0 T₂₂]` (a Schur form is
not needed), `E₂₁ = (Qᴴ E Q).toBlocks₂₁`, `Q̃₁ = stewartBasis Q P`; "orthonormal" is
`Q̃₁ᴴ Q̃₁ = I` and "invariant" is `(A + E) Q̃₁ = Q̃₁ M`. The backbone's
`Matrix.exists_invariant_graph_of_sep` in the coordinates of `Q` (the Frobenius norm is unitarily
invariant). -/
theorem theorem_7_2_4 {A E Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin r ⊕ Fin s) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂) (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℂ,
      ‖P‖ ≤ 4 * ‖(star Q * E * Q).toBlocks₂₁‖ / sep T₁₁ T₂₂ ∧
      (stewartBasis Q P)ᴴ * stewartBasis Q P = 1 ∧
      ∃ M : Matrix (Fin r) (Fin r) ℂ, (A + E) * stewartBasis Q P = stewartBasis Q P * M := by
  have hQQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.1 hQ
  have hnE : ‖star Q * E * Q‖ = ‖E‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  obtain ⟨P, hP, hinv⟩ := exists_invariant_graph_of_sep hs (E := star Q * E * Q) (by rwa [hnE])
  obtain ⟨hSS, hSh, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  set F : Matrix (Fin r ⊕ Fin s) (Fin r) ℂ := Q * fromRows 1 P with hFdef
  have hbasis : stewartBasis Q P = F * S⁻¹ := stewartBasis_eq Q P
  refine ⟨P, hP, ?_, ?_⟩
  · have hF : Fᴴ * F = S * S := by
      rw [hFdef, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q,
        ← star_eq_conjTranspose, hQQ', Matrix.one_mul,
        conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
        conjTranspose_one, Matrix.one_mul, hSS]
    rw [hbasis, conjTranspose_mul, conjTranspose_nonsing_inv, hSh, Matrix.mul_assoc,
      ← Matrix.mul_assoc Fᴴ, hF, Matrix.mul_assoc S, mul_nonsing_inv _ hSdet, Matrix.mul_one,
      nonsing_inv_mul _ hSdet]
  · set M₀ := T₁₁ + (star Q * E * Q).toBlocks₁₁ + (T₁₂ + (star Q * E * Q).toBlocks₁₂) * P
      with hM₀
    refine ⟨S * M₀ * S⁻¹, ?_⟩
    have hAF : (A + E) * F = F * M₀ := mul_unitary_mul_eq hQ hT hinv
    rw [hbasis, ← Matrix.mul_assoc, hAF]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, nonsing_inv_mul _ hSdet, Matrix.one_mul]

/-- **Corollary 7.2.5.** "If the assumptions in Theorem 7.2.4 hold, then
`dist(ran(Q₁), ran(Q̃₁)) ≤ 4 ‖E₂₁‖_F / sep(T₁₁, T₂₂)`", with `dist` the gap
(`Submodule.gap`) of the column spaces. `ran Q̃₁ = ran(Q [I; P])`, and in the coordinates of `Q`
the gap of `ran [I; 0]` and `ran [I; P]` is at most `‖P‖₂ ≤ ‖P‖_F` (`Matrix.gap_range_fromRows_le`,
(7.2.6)); the book's route through `‖Q₂ᴴ Q̃₁‖₂` is not needed. -/
theorem corollary_7_2_5 {A E Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Fin r ⊕ Fin s) ℂ) {T₁₁ : Matrix (Fin r) (Fin r) ℂ}
    {T₁₂ : Matrix (Fin r) (Fin s) ℂ} {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks T₁₁ T₁₂ 0 T₂₂) (hs : 0 < sep T₁₁ T₂₂)
    (hE : ‖E‖ * (1 + 5 * ‖T₁₂‖ / sep T₁₁ T₂₂) ≤ sep T₁₁ T₂₂ / 5) :
    ∃ P : Matrix (Fin s) (Fin r) ℂ,
      (stewartBasis Q P)ᴴ * stewartBasis Q P = 1 ∧
      (∃ M : Matrix (Fin r) (Fin r) ℂ, (A + E) * stewartBasis Q P = stewartBasis Q P * M) ∧
      (LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix (Fin r) (Fin r) ℂ)
          (0 : Matrix (Fin s) (Fin r) ℂ)))).gap
        (LinearMap.range (toEuclideanLin (stewartBasis Q P))) ≤
          4 * ‖(star Q * E * Q).toBlocks₂₁‖ / sep T₁₁ T₂₂ := by
  obtain ⟨P, hP, horth, hinv⟩ := theorem_7_2_4 hQ hT hs hE
  refine ⟨P, horth, hinv, ?_⟩
  obtain ⟨-, -, hSdet⟩ := sqrt_one_add_conjTranspose_mul_self P
  have hrange : LinearMap.range (toEuclideanLin (stewartBasis Q P)) =
      LinearMap.range (toEuclideanLin (Q * fromRows 1 P)) := by
    rw [stewartBasis_eq, toEuclideanLin_mul]
    refine LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 fun y => ?_)
    refine ⟨toEuclideanLin (CFC.sqrt (1 + Pᴴ * P)) y, ?_⟩
    rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ hSdet, toEuclideanLin_one_apply]
  simp only [hrange]
  exact (gap_range_unitary_mul_fromRows_le hQ P).trans
    ((equation_7_2_6 P).2.trans hP)

/-- The range of a one-column matrix is the span of its column. -/
private theorem range_toEuclideanLin_replicateCol {κ : Type*} (x : κ → ℂ) :
    LinearMap.range (toEuclideanLin (replicateCol Unit x)) = ℂ ∙ WithLp.toLp 2 x := by
  ext y
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z (), ?_⟩
    ext i
    simp [toEuclideanLin_apply, mulVec, dotProduct, mul_comm]
  · rintro ⟨a, rfl⟩
    refine ⟨WithLp.toLp 2 fun _ => a, ?_⟩
    ext i
    simp [mulVec, dotProduct, mul_comm]

/-- A one-column matrix `w` with `X w = w M` is an eigenvector: `X w = M₁₁ w`. -/
private theorem mulVec_eq_smul_of_mul_replicateCol {κ : Type*} [Fintype κ] {X : Matrix κ κ ℂ}
    {w : κ → ℂ} {M : Matrix Unit Unit ℂ} (h : X * replicateCol Unit w = replicateCol Unit w * M) :
    X *ᵥ w = M () () • w := by
  ext i
  have := congrFun (congrFun h i) ()
  simpa [mul_apply, replicateCol_apply, mulVec, dotProduct, mul_comm] using this

/-- **The book's `q̃₁ = (q₁ + Q₂ p)/√(1 + pᴴ p)`** of Corollary 7.2.6, for `Q = [q₁ | Q₂]`
(`q₁ + Q₂ p = Q [1; p]`). -/
noncomputable def stewartVector (Q : Matrix (Unit ⊕ Fin s) (Unit ⊕ Fin s) ℂ) (p : Fin s → ℂ) :
    Unit ⊕ Fin s → ℂ :=
  (((√(1 + ‖WithLp.toLp 2 p‖ ^ 2) : ℝ) : ℂ))⁻¹ • (Q *ᵥ Sum.elim (fun _ => 1) p)

/-- **Corollary 7.2.6** (eigenvector sensitivity). "Suppose `A, E ∈ ℂ^{n×n}` and that
`Q = [q₁ | Q₂]` is unitary with `Qᴴ A Q = [λ vᴴ; 0 T₂₂]`, `Qᴴ E Q = [ε γᴴ; δ E₂₂]`. If
`σ = σ_min(T₂₂ - λI) > 0` and `‖E‖_F (1 + 5 ‖v‖₂ / σ) ≤ σ/5`, then there exists `p ∈ ℂ^{n-1}` with
`‖p‖₂ ≤ 4 ‖δ‖₂ / σ` such that `q̃₁ = (q₁ + Q₂ p)/√(1 + pᴴ p)` is a unit 2-norm eigenvector for
`A + E`. Moreover, `dist(span{q₁}, span{q̃₁}) ≤ 4 ‖δ‖₂ / σ`." On `Unit ⊕ Fin s`; `σ` is the least
singular value, `δ` the first column of `Qᴴ E Q` below the corner and `q̃₁ = stewartVector Q p`.
The `r = 1` case of Theorem 7.2.4 and Corollary 7.2.5 through `sep_one_eq_sigmaMin`, taken from
the backbone's `Matrix.exists_invariant_graph_of_sep` directly (for `r = 1` the inverse square root
is the scalar `1/√(1 + pᴴ p)` and a one-dimensional invariant subspace is an eigenvector). -/
theorem corollary_7_2_6 {A E Q : Matrix (Unit ⊕ Fin s) (Unit ⊕ Fin s) ℂ}
    (hQ : Q ∈ unitaryGroup (Unit ⊕ Fin s) ℂ) {μ : ℂ} {v : Fin s → ℂ}
    {T₂₂ : Matrix (Fin s) (Fin s) ℂ}
    (hT : star Q * A * Q = fromBlocks (of fun _ _ => μ) (replicateCol Unit v)ᴴ 0 T₂₂)
    (hσ : 0 < ⨅ i, (T₂₂ - μ • 1).singularValues i)
    (hE : ‖E‖ * (1 + 5 * ‖WithLp.toLp 2 v‖ / ⨅ i, (T₂₂ - μ • 1).singularValues i) ≤
      (⨅ i, (T₂₂ - μ • 1).singularValues i) / 5) :
    ∃ p : Fin s → ℂ,
      ‖WithLp.toLp 2 p‖ ≤ 4 * ‖WithLp.toLp 2 fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ())‖ /
        (⨅ i, (T₂₂ - μ • 1).singularValues i) ∧
      ‖WithLp.toLp 2 (stewartVector Q p)‖ = 1 ∧
      (∃ μ' : ℂ, (A + E) *ᵥ stewartVector Q p = μ' • stewartVector Q p) ∧
      (ℂ ∙ WithLp.toLp 2 fun i => Q i (Sum.inl ())).gap (ℂ ∙ WithLp.toLp 2 (stewartVector Q p)) ≤
        4 * ‖WithLp.toLp 2 fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ())‖ /
          (⨅ i, (T₂₂ - μ • 1).singularValues i) := by
  set σ := ⨅ i, (T₂₂ - μ • 1).singularValues i with hσdef
  set δ : Fin s → ℂ := fun i => (star Q * E * Q) (Sum.inr i) (Sum.inl ()) with hδdef
  have hsep : sep (of fun _ _ => μ : Matrix Unit Unit ℂ) T₂₂ = σ := (sep_one_eq_sigmaMin μ T₂₂).1
  have hnE : ‖star Q * E * Q‖ = ‖E‖ :=
    frobenius_norm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  have hv : ‖(replicateCol Unit v)ᴴ‖ = ‖WithLp.toLp 2 v‖ := by
    rw [frobenius_norm_conjTranspose, frobenius_norm_replicateCol]
  obtain ⟨P, hP, hinv⟩ := exists_invariant_graph_of_sep (T₁₁ := of fun _ _ => μ)
    (T₁₂ := (replicateCol Unit v)ᴴ) (T₂₂ := T₂₂) (E := star Q * E * Q) (by rw [hsep]; exact hσ)
    (by rw [hnE, hv, hsep]; exact hE)
  set p : Fin s → ℂ := fun i => P i () with hpdef
  have hPp : P = replicateCol Unit p := by
    ext i j
    rfl
  have hδ : (star Q * E * Q).toBlocks₂₁ = replicateCol Unit δ := by
    ext i j
    rfl
  have hpb : ‖WithLp.toLp 2 p‖ ≤ 4 * ‖WithLp.toLp 2 δ‖ / σ := by
    rw [← frobenius_norm_replicateCol (ι := Unit), ← hPp, ← frobenius_norm_replicateCol (ι := Unit),
      ← hδ, ← hsep]
    exact hP
  set w : Unit ⊕ Fin s → ℂ := Q *ᵥ Sum.elim (fun _ => 1) p with hwdef
  have hQw : Q * fromRows (1 : Matrix Unit Unit ℂ) P = replicateCol Unit w := by
    ext i u
    rw [replicateCol_apply, hwdef, mulVec, dotProduct, mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases j with j | j
    · simp
    · simp [hpdef]
  have hq₁ : Q * fromRows (1 : Matrix Unit Unit ℂ) (0 : Matrix (Fin s) Unit ℂ) =
      replicateCol Unit fun i => Q i (Sum.inl ()) := by
    ext i u
    rw [replicateCol_apply, mul_apply, Fintype.sum_sum_type]
    simp
  -- the norm of `w`
  have hwn : ‖WithLp.toLp 2 w‖ = √(1 + ‖WithLp.toLp 2 p‖ ^ 2) := by
    have h1 : WithLp.toLp 2 w = unitaryLinearIsometryEquiv hQ
        (WithLp.toLp 2 (Sum.elim (fun _ => 1) p)) := by
      rw [unitaryLinearIsometryEquiv_apply, toEuclideanLin_apply]
    rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Fintype.sum_sum_type,
      EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp
  have hc : 0 < √(1 + ‖WithLp.toLp 2 p‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hq : stewartVector Q p = (((√(1 + ‖WithLp.toLp 2 p‖ ^ 2) : ℝ) : ℂ))⁻¹ • w := rfl
  refine ⟨p, hpb, ?_, ?_, ?_⟩
  · rw [hq, WithLp.toLp_smul, norm_smul, hwn, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, inv_mul_cancel₀ hc.ne']
  · -- the eigenvector
    have hAQ := mul_unitary_mul_eq hQ hT hinv
    rw [hQw] at hAQ
    have hw := mulVec_eq_smul_of_mul_replicateCol hAQ
    exact ⟨_, by rw [hq, mulVec_smul, hw, smul_comm]⟩
  · -- the distance
    have hspan : (ℂ ∙ WithLp.toLp 2 (stewartVector Q p)) =
        LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix Unit Unit ℂ) P)) := by
      rw [hQw, range_toEuclideanLin_replicateCol, hq, WithLp.toLp_smul,
        Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero (by exact_mod_cast hc.ne')))]
    have hspan₁ : (ℂ ∙ WithLp.toLp 2 fun i => Q i (Sum.inl ())) =
        LinearMap.range (toEuclideanLin (Q * fromRows (1 : Matrix Unit Unit ℂ)
          (0 : Matrix (Fin s) Unit ℂ))) := by
      rw [hq₁, range_toEuclideanLin_replicateCol]
    simp only [hspan, hspan₁]
    refine (gap_range_unitary_mul_fromRows_le hQ P).trans ((l2_opNorm_le_frobenius_norm P).trans ?_)
    rw [hPp, frobenius_norm_replicateCol]
    exact hpb

end Stewart

end GolubVanLoan.Chapter07
