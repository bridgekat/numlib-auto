import Numlib.Eigen.InvariantSubspace
import Numlib.Eigen.Perturbation
import NumlibSurface.GolubVanLoan.Chapter07.Section01

/-!
# Golub–Van Loan §7.2: perturbation theory

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §7.2: Gershgorin's theorem for a similarity transform (Theorem 7.2.1) and its
isolated discs, the resolvent step (7.2.1) behind Theorems 7.2.1–7.2.3, the Schur-form bound
(Theorem 7.2.3), the condition `1/s(λ)` of a simple eigenvalue ((7.2.2) and its first-order
derivation), the `2 × 2` repeated-eigenvalue example (§7.2.3), and the separation (7.2.5).

## Conventions

Complex, `A : Matrix (Fin n) (Fin n) ℂ`, as in §7.1 (`GolubVanLoan.Chapter07.Section01`). The
2-norm is the scoped `Matrix.Norms.L2Operator` norm and the Frobenius norm the scoped
`Matrix.Norms.Frobenius` norm, each opened in its own section. A right eigenvector is
`A *ᵥ x = λ • x`, a left eigenvector `star y ᵥ* A = λ • star y` (the book's `yᴴ A = λ yᴴ`), and unit
length is `‖WithLp.toLp 2 x‖ = 1`. The separation `sep(T₁₁, T₂₂)` is the backbone's `Matrix.sep`.

## Sources

`Numlib/Eigen/Perturbation` (Gershgorin, the resolvent step, Theorem 7.2.3, the eigenvalue
condition number and the differentiable eigenvalue branch), `Numlib/LinearAlgebra/Matrix/Sylvester`
(`sep`).

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

end GolubVanLoan.Chapter07
