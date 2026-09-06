import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.SaadSparse.Chapter04.Section02

/-!
# Saad §13.2: the model problems and the spectra of the smoothers

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §13.2: the one- and two-dimensional discrete Laplaceans on which the whole multigrid chapter
runs, their eigenvalues and eigenvectors, and the spectra of Richardson's iteration (§13.2.1),
weighted Jacobi (§13.2.2) and Gauss–Seidel (§13.2.3) on them.

Everything here is explicit linear algebra, and every statement is proved rather than displayed.
The two conclusions the chapter is built on are

* the spectral radius of each smoother is `1 - O(h²)`, so none of them is a solver
  (`richardson_factor_le`, `equation_13_22`); and
* the *oscillatory* half of the spectrum, `k > n/2`, is damped by a factor bounded away from `1`
  **independently of `h`** — the smoothing property
  (`richardson_factor_le_half_of_oscillatory`, `smoothingFactor_two_thirds`,
  `smoothingFactor2D_four_fifths`).

## Conventions

The matrices of §13.2 are **unscaled**: `laplacian1D n` is `tridiag(-1, 2, -1)`, the `h²`-scaled
form of the operator `-u''` on the grid `x_i = i h`, `h = 1/(n + 1)`.  Saad writes the same matrix
in §2.2.3 with the factor `1/h²`, and `SaadSparse.Chapter02.laplacian1D n h` carries it; the two
live in different namespaces and `SaadSparse.Chapter02.laplacian2D_smul` relates them.  Interior
points are numbered from `0`, so the library's `k : Fin n` is Saad's `k + 1`, and `theta n k` is his
`θ_k = kπ/(n + 1)`.

The two-dimensional matrix is indexed by the **product type** `Fin n × Fin m`, never by
`Fin (n * m)`: that is the indexing of `Numlib.LinearAlgebra.Matrix.KroneckerSum`, and Saad's
tensor sum (13.12) `A = I ⊗ T_x + T_y ⊗ I` is then literally `laplacian1D n ⊕ₖ laplacian1D m`
(`laplacian2D_eq_kroneckerSum`), with the first coordinate indexing the blocks of the block
tridiagonal form (`laplacian2D_block_apply`).

## Where the work is

Nowhere here — it is all in the backbone.  `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz.lean`
has the sine eigenbasis of `tridiag(a, b, a)` and, in
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`, the fact that it *exhausts* the spectrum;
`Numlib/LinearAlgebra/Matrix/KroneckerSum.lean` has the Leibniz rule on an elementary tensor and
the tensor orthonormal basis, which is what makes the two-dimensional eigenpairs exhaustive even
where the sums `σ_k + μ_l` coincide.  The Gauss–Seidel spectrum comes from Young's theorem
(Saad Theorem 4.16, `SaadSparse.Chapter04.theorem_4_16_mpr`), a tridiagonal matrix being
consistently ordered.
-/

open Finset Matrix Stationary
open scoped Kronecker Matrix Real

namespace SaadSparse.Chapter13

/-! ### §13.2 The one-dimensional model problem, (13.4)–(13.9) -/

section OneDimensional

variable {n : ℕ}

/-- Saad (13.4): the one-dimensional model matrix `tridiag(-1, 2, -1)` of size `n`, the
discretization of `-u'' = f` on `(0, 1)` with homogeneous Dirichlet conditions on the uniform grid
`x_i = i h`, `h = 1/(n + 1)`.

This is the **unscaled** matrix of Chapter 13, in which the factor `h²` sits on the right-hand
side; `SaadSparse.Chapter02.laplacian1D n h` is the same matrix scaled by `1/h²`, as §2.2.3 displays
it. -/
def laplacian1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := symmTridiagonalToeplitz n (-1) 2

/-- The model matrix is the backbone's `tridiag(-1, 2, -1)`. -/
theorem laplacian1D_eq (n : ℕ) : laplacian1D n = symmTridiagonalToeplitz n (-1) 2 := rfl

/-- The entries of the one-dimensional model matrix: `2` on the diagonal, `-1` on both
off-diagonals. -/
theorem laplacian1D_apply (n : ℕ) (i j : Fin n) :
    laplacian1D n i j =
      if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 :=
  symmTridiagonalToeplitz_apply' (-1) 2 i j

/-- The one-dimensional model matrix is symmetric. -/
theorem laplacian1D_isSymm (n : ℕ) : (laplacian1D n).IsSymm :=
  symmTridiagonalToeplitz_isSymm (-1) 2

/-- The one-dimensional model matrix is Hermitian. -/
theorem laplacian1D_isHermitian (n : ℕ) : (laplacian1D n).IsHermitian :=
  symmTridiagonalToeplitz_isHermitian (-1) 2

/-- The one-dimensional model matrix is tridiagonal, which is what makes it consistently ordered
in §13.2.3. -/
theorem laplacian1D_isTridiagonal (n : ℕ) : (laplacian1D n).IsTridiagonal :=
  symmTridiagonalToeplitz_isTridiagonal (-1) 2

/-- Saad §13.2: the one-dimensional model matrix is symmetric positive definite. -/
theorem laplacian1D_posDef (n : ℕ) : (laplacian1D n).PosDef :=
  posDef_symmTridiagonalToeplitz_neg_one_two n

/-- The diagonal of the one-dimensional model matrix is `D = 2 I`; this is why `D⁻¹ A = A/2` makes
weighted Jacobi elementary in §13.2.2. -/
theorem diagPart_laplacian1D (n : ℕ) : diagPart (laplacian1D n) = (2 : ℝ) • 1 := by
  ext i j
  rw [diagPart_apply, laplacian1D_eq, symmTridiagonalToeplitz_apply_self, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The diagonal of the one-dimensional model matrix is invertible. -/
theorem isUnit_diagPart_laplacian1D (n : ℕ) : IsUnit (diagPart (laplacian1D n)) :=
  (isUnit_diagPart_iff _).2 fun i => by
    rw [laplacian1D_eq, symmTridiagonalToeplitz_apply_self]; norm_num

/-- Saad (13.6): the angle `θ_k = k π / (n + 1)`, in the library's `0`-based numbering — the index
`k : Fin n` is Saad's `k + 1`, so `theta n k = (k + 1) π / (n + 1)`. -/
noncomputable def theta (n : ℕ) (k : Fin n) : ℝ := (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1)

/-- `0 < θ_k`. -/
theorem theta_pos (n : ℕ) (k : Fin n) : 0 < theta n k := angle_pos n k

/-- `θ_k < π`, which is why the `n` eigenvalues below are distinct. -/
theorem theta_lt_pi (n : ℕ) (k : Fin n) : theta n k < π := angle_lt_pi n k

/-- `sin θ_k > 0`, so the sine eigenvectors are nonzero. -/
theorem sin_theta_pos (n : ℕ) (k : Fin n) : 0 < Real.sin (theta n k) :=
  Real.sin_pos_of_pos_of_lt_pi (theta_pos n k) (theta_lt_pi n k)

/-- The half angle `θ_k / 2` written out, `(k + 1) π / (2 (n + 1))`.  Note that `ring` does not
prove this: it treats `⁻¹` as an atom. -/
theorem theta_div_two (n : ℕ) (k : Fin n) :
    theta n k / 2 = (((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) := by
  rw [theta, div_div, mul_comm ((n : ℝ) + 1) 2]

/-- `0 < θ_k / 2 < π/2`, the interval on which the sine is increasing and positive. -/
theorem theta_div_two_mem_Ioo (n : ℕ) (k : Fin n) : theta n k / 2 ∈ Set.Ioo 0 (π / 2) :=
  Set.mem_Ioo.2 ⟨by linarith [theta_pos n k], by linarith [theta_lt_pi n k]⟩

/-- `sin(θ_k/2) > 0`. -/
theorem sin_theta_div_two_pos (n : ℕ) (k : Fin n) : 0 < Real.sin (theta n k / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (theta_div_two_mem_Ioo n k).1
    (lt_trans (theta_div_two_mem_Ioo n k).2 (by linarith [Real.pi_pos]))

/-- `cos(θ_k/2) > 0`. -/
theorem cos_theta_div_two_pos (n : ℕ) (k : Fin n) : 0 < Real.cos (theta n k / 2) :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(theta_div_two_mem_Ioo n k).1, Real.pi_pos], (theta_div_two_mem_Ioo n k).2⟩

/-- `sin²(θ_k/2) < 1`, since `θ_k/2` stays below `π/2`. -/
theorem sin_sq_theta_div_two_lt_one (n : ℕ) (k : Fin n) : Real.sin (theta n k / 2) ^ 2 < 1 := by
  have h := Real.sin_sq_add_cos_sq (theta n k / 2)
  nlinarith [cos_theta_div_two_pos n k]

/-- Saad (13.7): the eigenvalue `λ_k = 4 sin²(θ_k/2)` of the one-dimensional model matrix. -/
noncomputable def eigenvalue1D (n : ℕ) (k : Fin n) : ℝ := 4 * Real.sin (theta n k / 2) ^ 2

/-- The half-angle identity `2 - 2 cos θ = 4 sin²(θ/2)`. -/
private theorem two_sub_two_mul_cos (θ : ℝ) : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul_eq_one_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- Saad (13.6)–(13.7): the eigenvalue in its other form, `λ_k = 2(1 - cos θ_k)`. -/
theorem eigenvalue1D_eq (n : ℕ) (k : Fin n) :
    eigenvalue1D n k = 2 - 2 * Real.cos (theta n k) := by
  rw [eigenvalue1D, two_sub_two_mul_cos]

/-- The eigenvalues of the one-dimensional model matrix are positive. -/
theorem eigenvalue1D_pos (n : ℕ) (k : Fin n) : 0 < eigenvalue1D n k := by
  rw [eigenvalue1D]
  nlinarith [sin_theta_div_two_pos n k]

/-- The eigenvalues of the one-dimensional model matrix are below `4`, which is the Gershgorin
bound `γ = 4` that §13.2.1 uses for Richardson's iteration. -/
theorem eigenvalue1D_lt_four (n : ℕ) (k : Fin n) : eigenvalue1D n k < 4 := by
  rw [eigenvalue1D]
  linarith [sin_sq_theta_div_two_lt_one n k]

/-- Saad (13.8): the `k`-th discrete sine vector `w_k`, with components `sin(j θ_k)`, is an
eigenvector of the one-dimensional model matrix for the eigenvalue `λ_k = 4 sin²(θ_k/2)`. -/
theorem laplacian1D_mulVec_sineVec (n : ℕ) (k : Fin n) :
    laplacian1D n *ᵥ sineVec n k = eigenvalue1D n k • sineVec n k := by
  rw [laplacian1D_eq, symmTridiagonalToeplitz_mulVec_sineVec]
  congr 1
  rw [eigenvalue1D_eq, theta]
  ring

/-- Saad (13.9): the components of `w_k` are the values `sin(k π x_j)` of a sine at the grid
points `x_j = j h`, `h = 1/(n + 1)` (in the library's `0`-based numbering, `x_j` is the
`(j + 1)`-st grid point and `k` is Saad's `k + 1`). -/
theorem sineVec_eq_sin_grid (n : ℕ) (k j : Fin n) :
    sineVec n k j =
      Real.sin ((((k : ℕ) : ℝ) + 1) * π * ((((j : ℕ) : ℝ) + 1) * (1 / ((n : ℝ) + 1)))) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [sineVec_apply]
  congr 1
  field_simp

/-- **Saad (13.6)–(13.9)**: the spectrum of the one-dimensional model matrix consists of exactly
the `n` numbers `λ_k = 2(1 - cos θ_k) = 4 sin²(θ_k/2)`, `θ_k = kπ/(n+1)`.

The eigenvectors are the discrete sine vectors `w_k` of (13.8) — `laplacian1D_mulVec_sineVec`,
whose components are the grid values `sin(k π x_j)` of `sineVec_eq_sin_grid` — and they are
exhaustive because, normalized, they are the orthonormal basis
`Matrix.sineOrthonormalBasis n`. -/
theorem equation_13_7 (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (laplacian1D n)) μ ↔
      ∃ k : Fin n, μ = eigenvalue1D n k := by
  rw [laplacian1D_eq, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  rw [eigenvalue1D_eq, theta]
  constructor <;> intro h <;> linarith

/-! #### Monotonicity of the eigenvalues in `k` -/

/-- The largest of the `cos θ_k` is the one at `k = 1`. -/
theorem cos_theta_le (n : ℕ) (k : Fin n) :
    Real.cos (theta n k) ≤ Real.cos (π / ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1 : π / ((n : ℝ) + 1) ≤ theta n k := by
    rw [theta, div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (theta_lt_pi n k).le hk1

/-- The smallest of the `cos θ_k` is the one at `k = n`, where it is `-cos(π/(n+1))`. -/
theorem neg_cos_le_cos_theta (n : ℕ) (k : Fin n) :
    -Real.cos (π / ((n : ℝ) + 1)) ≤ Real.cos (theta n k) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk2 : theta n k ≤ π - π / ((n : ℝ) + 1) := by
    have hkn : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast k.isLt
    have hrw : π - π / ((n : ℝ) + 1) = (n : ℝ) * π / ((n : ℝ) + 1) := by field_simp; ring
    rw [theta, hrw, div_le_div_iff_of_pos_right hn]
    nlinarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (theta_pos n k).le
    (by linarith [div_nonneg Real.pi_pos.le hn.le] : π - π / ((n : ℝ) + 1) ≤ π) hk2
  rwa [Real.cos_pi_sub] at h

/-- The half angle at `k = 1`, `π/(2(n+1))`, is the smallest of the `θ_k/2`. -/
theorem sin_sq_theta_div_two_ge (n : ℕ) (k : Fin n) :
    Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 ≤ Real.sin (theta n k / 2) ^ 2 := by
  have h1 := two_sub_two_mul_cos (theta n k)
  have h2 := two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  rw [show π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  linarith [cos_theta_le n k]

/-- The half angle at `k = n` is the largest of the `θ_k/2`, and there
`sin²(θ_n/2) = cos²(π/(2(n+1))) = 1 - sin²(π/(2(n+1)))`. -/
theorem sin_sq_theta_div_two_le (n : ℕ) (k : Fin n) :
    Real.sin (theta n k / 2) ^ 2 ≤ 1 - Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h1 := two_sub_two_mul_cos (theta n k)
  have h2 := two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  rw [show π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  linarith [neg_cos_le_cos_theta n k]

/-- **The oscillatory half of the spectrum**: Saad's `k > n/2` reads, in the library's `0`-based
numbering, `n + 1 ≤ 2(k + 1)`, and it says exactly that `θ_k ≥ π/2`, that is
`sin²(θ_k/2) ≥ 1/2`.  This is the one inequality behind every mesh-independent smoothing factor
of §13.2. -/
theorem sin_sq_theta_div_two_ge_half (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    1 / 2 ≤ Real.sin (theta n k / 2) ^ 2 := by
  have hk' : (n : ℝ) + 1 ≤ 2 * (((k : ℕ) : ℝ) + 1) := by exact_mod_cast hk
  have hcos : Real.cos (theta n k) ≤ 0 := by
    refine Real.cos_nonpos_of_pi_div_two_le_of_le ?_ (by linarith [theta_lt_pi n k, Real.pi_pos])
    rw [theta, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [Real.pi_pos]
  linarith [two_sub_two_mul_cos (theta n k)]

end OneDimensional

/-! ### §13.2 The two-dimensional model problem, (13.10)–(13.14) -/

section TwoDimensional

variable {n m : ℕ}

/-- Saad (13.11)–(13.12): the two-dimensional model matrix on an `n × m` interior grid, the
five-point discretization of `-Δu = f` on the unit square with homogeneous Dirichlet conditions,
indexed by the product type `Fin n × Fin m`.

It is block tridiagonal with `B = tridiag(-1, 4, -1)` on the diagonal and `-I` off it
(`laplacian2D_block_apply`), equivalently the tensor sum
`A = I ⊗ T_x + T_y ⊗ I` of (13.12) (`laplacian2D_eq_kroneckerSum`).  Unscaled, as in §13.2. -/
def laplacian2D (n m : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  Matrix.of fun p q =>
    if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 4
    else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -1
    else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -1
    else 0

/-- The entries of the two-dimensional model matrix: `4` on the diagonal, `-1` at each of the four
grid neighbours. -/
theorem laplacian2D_apply (n m : ℕ) (p q : Fin n × Fin m) :
    laplacian2D n m p q =
      if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 4
      else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -1
      else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -1
      else 0 :=
  rfl

/-- **Saad (13.12)**: the five-point matrix is the tensor sum `A = I ⊗ T_x + T_y ⊗ I` of two
one-dimensional model matrices, one for each coordinate direction. -/
theorem laplacian2D_eq_kroneckerSum (n m : ℕ) :
    laplacian2D n m = laplacian1D n ⊕ₖ laplacian1D m := by
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  rw [Matrix.kroneckerSum_apply, laplacian1D_apply, laplacian1D_apply, laplacian2D_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> first | (exfalso; omega) | ring

/-- Saad (13.11): the block form of the five-point matrix.  Blocks are indexed by the first
coordinate; the diagonal blocks are `B = tridiag(-1, 4, -1)` and the blocks next to the diagonal
are `-I`, every other block vanishing. -/
theorem laplacian2D_block_apply (n m : ℕ) (i₁ j₁ : Fin n) (i₂ j₂ : Fin m) :
    laplacian2D n m (i₁, i₂) (j₁, j₂) =
      if (i₁ : ℕ) = j₁ then symmTridiagonalToeplitz m (-1) 4 i₂ j₂
      else if (i₁ : ℕ) + 1 = j₁ ∨ (j₁ : ℕ) + 1 = i₁ then
        -(1 : Matrix (Fin m) (Fin m) ℝ) i₂ j₂
      else 0 := by
  rw [laplacian2D_eq_kroneckerSum, Matrix.kroneckerSum_apply, laplacian1D_apply,
    laplacian1D_apply, symmTridiagonalToeplitz_apply', Matrix.one_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The diagonal entry of the two-dimensional model matrix is `4`. -/
theorem laplacian2D_apply_self (n m : ℕ) (p : Fin n × Fin m) : laplacian2D n m p p = 4 := by
  rw [laplacian2D_apply, ite_eq_left ⟨rfl, rfl⟩]

/-- The diagonal of the two-dimensional model matrix is `D = 4 I`. -/
theorem diagPart_laplacian2D (n m : ℕ) : diagPart (laplacian2D n m) = (4 : ℝ) • 1 := by
  ext p q
  rw [diagPart_apply, laplacian2D_apply_self, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The diagonal of the two-dimensional model matrix is invertible. -/
theorem isUnit_diagPart_laplacian2D (n m : ℕ) : IsUnit (diagPart (laplacian2D n m)) :=
  (isUnit_diagPart_iff _).2 fun p => by rw [laplacian2D_apply_self]; norm_num

/-- Saad §13.2: the two-dimensional model matrix is symmetric positive definite, because positive
definiteness adds under a tensor sum. -/
theorem laplacian2D_posDef (n m : ℕ) : (laplacian2D n m).PosDef := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.posDef_kroneckerSum (laplacian1D_posDef n) (laplacian1D_posDef m)

/-- Saad (13.13): the tensor product `z_{k,l} = w_k ⊗ v_l` of two discrete sine vectors is an
eigenvector of the two-dimensional model matrix, with eigenvalue `λ_k + μ_l`. -/
theorem laplacian2D_mulVec_kroneckerVec (n m : ℕ) (k : Fin n) (l : Fin m) :
    laplacian2D n m *ᵥ kroneckerVec (sineVec n k) (sineVec m l) =
      (eigenvalue1D n k + eigenvalue1D m l) • kroneckerVec (sineVec n k) (sineVec m l) := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul
    (laplacian1D_mulVec_sineVec n k) (laplacian1D_mulVec_sineVec m l)

/-- Saad (13.13): the values of the eigenvector `z_{k,l}` at the grid points are
`sin(k π x_i) sin(l π y_j)`. -/
theorem kroneckerVec_sineVec_eq_sin_grid (n m : ℕ) (k : Fin n) (l : Fin m)
    (p : Fin n × Fin m) :
    kroneckerVec (sineVec n k) (sineVec m l) p =
      Real.sin ((((k : ℕ) : ℝ) + 1) * π * ((((p.1 : ℕ) : ℝ) + 1) * (1 / ((n : ℝ) + 1)))) *
        Real.sin ((((l : ℕ) : ℝ) + 1) * π * ((((p.2 : ℕ) : ℝ) + 1) * (1 / ((m : ℝ) + 1)))) := by
  obtain ⟨i, j⟩ := p
  rw [Matrix.kroneckerVec_apply, sineVec_eq_sin_grid, sineVec_eq_sin_grid]

/-- A scalar multiple of an eigenvector is an eigenvector, in the `EuclideanSpace` picture. -/
private theorem toEuclideanLin_toLp_smul_eq {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} {v : N → ℝ} {μ : ℝ} (h : A *ᵥ v = μ • v) (c : ℝ) :
    toEuclideanLin A (WithLp.toLp 2 (c • v)) = μ • WithLp.toLp 2 (c • v) := by
  have h1 : toEuclideanLin A (WithLp.toLp 2 (c • v)) = WithLp.toLp 2 (A *ᵥ (c • v)) := rfl
  rw [h1, Matrix.mulVec_smul, h, smul_comm]
  rfl

/-- A symmetric operator diagonalized by an orthonormal basis has exactly the listed eigenvalues:
the basis exhausts the spectrum.  This is the two-dimensional counterpart of
`Matrix.symmTridiagonalToeplitz_hasEigenvalue_iff`, and it is what makes (13.14) a complete list
even when two sums `λ_k + μ_l` coincide. -/
private theorem hasEigenvalue_iff_of_orthonormalBasis {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) {ν : ι → ℝ} (hb : ∀ i, T (b i) = ν i • b i) (μ : ℝ) :
    Module.End.HasEigenvalue T μ ↔ ∃ i, μ = ν i := by
  refine ⟨fun hμ => ?_, ?_⟩
  · by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx
    have hzero : ∀ i, inner ℝ (b i) x = 0 := by
      intro i
      have h1 : inner ℝ (b i) (T x) = μ * inner ℝ (b i) x := by rw [hx, real_inner_smul_right]
      have h2 : inner ℝ (b i) (T x) = ν i * inner ℝ (b i) x := by
        rw [← hT (b i) x, hb i, real_inner_smul_left]
      have h3 : (μ - ν i) * inner ℝ (b i) x = 0 := by rw [sub_mul, ← h1, h2, sub_self]
      rcases mul_eq_zero.1 h3 with h' | h'
      · exact absurd (by linarith : μ = ν i) (hne i)
      · exact h'
    refine hx0 ?_
    rw [← b.sum_repr' x]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_smul]
  · rintro ⟨i, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (hb i), b.orthonormal.ne_zero i⟩

/-- **Saad (13.13)–(13.14)**: the spectrum of the two-dimensional model matrix consists of exactly
the numbers
`λ_{k,l} = 4 (sin²(kπ/(2(n+1))) + sin²(lπ/(2(m+1))))`,
with the eigenvectors `z_{k,l} = w_k ⊗ v_l` of `laplacian2D_mulVec_kroneckerVec`.

The list is exhaustive even where two of the sums coincide, because the normalized `w_k ⊗ v_l` are
the orthonormal basis `Matrix.kroneckerOrthonormalBasis` of the whole space, not merely a family
of eigenvectors. -/
theorem equation_13_14 (n m : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue (toEuclideanLin (laplacian2D n m)) μ ↔
      ∃ (k : Fin n) (l : Fin m), μ = eigenvalue1D n k + eigenvalue1D m l := by
  have hsymm : (toEuclideanLin (laplacian2D n m)).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2 (by
      rw [laplacian2D_eq_kroneckerSum]
      exact isHermitian_kroneckerSum (laplacian1D_isHermitian n) (laplacian1D_isHermitian m))
  have hb : ∀ q : Fin n × Fin m,
      toEuclideanLin (laplacian2D n m)
          (kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q) =
        (fun q : Fin n × Fin m => eigenvalue1D n q.1 + eigenvalue1D m q.2) q •
          kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q := by
    intro q
    have hform :
        kroneckerOrthonormalBasis (sineOrthonormalBasis n) (sineOrthonormalBasis m) q =
          WithLp.toLp 2 ((Real.sqrt (2 / ((n : ℝ) + 1)) * Real.sqrt (2 / ((m : ℝ) + 1))) •
            kroneckerVec (sineVec n q.1) (sineVec m q.2)) := by
      rw [kroneckerOrthonormalBasis_apply, sineOrthonormalBasis_apply, sineOrthonormalBasis_apply,
        WithLp.ofLp_smul, WithLp.ofLp_smul, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
        Matrix.kroneckerVec_smul_left, Matrix.kroneckerVec_smul_right, smul_smul]
    rw [hform]
    exact toEuclideanLin_toLp_smul_eq (laplacian2D_mulVec_kroneckerVec n m q.1 q.2) _
  rw [hasEigenvalue_iff_of_orthonormalBasis _ hsymm _ hb μ]
  exact ⟨fun ⟨q, hq⟩ => ⟨q.1, q.2, hq⟩, fun ⟨k, l, h⟩ => ⟨(k, l), h⟩⟩

end TwoDimensional

/-! ### §13.2.1 Richardson's iteration, (13.15)–(13.16) -/

section Richardson

variable {n : ℕ}

/-- For a symmetric `M` and an eigenvector `w`, the `w`-component of `Mʲ v` is `cʲ` times the
`w`-component of `v`. -/
private theorem dotProduct_pow_mulVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    {w : Fin n → ℝ} {c : ℝ} (hw : M *ᵥ w = c • w) (v : Fin n → ℝ) (j : ℕ) :
    w ⬝ᵥ ((M ^ j) *ᵥ v) = c ^ j * (w ⬝ᵥ v) := by
  have hstep : ∀ u : Fin n → ℝ, w ⬝ᵥ (M *ᵥ u) = c * (w ⬝ᵥ u) := by
    intro u
    rw [dotProduct_mulVec, ← hM.eq, vecMul_transpose, hw, smul_dotProduct, smul_eq_mul]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← mulVec_mulVec, hstep, ih]
    ring

/-- Saad (13.15): the Richardson iteration matrix `M_ω = I - ω A` has the sine vectors as
eigenvectors, with eigenvalues `1 - ω λ_k`. -/
theorem richardson_iterationMatrix_mulVec_sineVec (n : ℕ) (ω : ℝ) (k : Fin n) :
    (1 - ω • laplacian1D n) *ᵥ sineVec n k = (1 - ω * eigenvalue1D n k) • sineVec n k := by
  rw [sub_mulVec, one_mulVec, Matrix.smul_mulVec, laplacian1D_mulVec_sineVec, smul_smul, sub_smul,
    one_smul]

/-- **Saad (13.15)–(13.16)**: for Richardson's iteration `x ← x + (1/γ)(b - A x)` on the
one-dimensional model problem, the `w_k`-component of the error is multiplied by
`η_k = 1 - λ_k/γ` at every step, so after `j` steps it has been multiplied by `η_k^j`.

With `γ = 4`, which is the Gershgorin bound and an upper bound for the spectrum by
`eigenvalue1D_lt_four`, the factor is `η_k = cos²(θ_k/2)`
(`richardson_factor_eq_cos_sq`): it is `1 - sin²(π/(2(n+1))) = 1 - O(h²)` at worst
(`richardson_factor_le`), so the iteration is a very slow solver, while on the oscillatory half
`k > n/2` of the spectrum it is at most `1/2` **whatever the mesh**
(`richardson_factor_le_half_of_oscillatory`).  That contrast is the whole point of §13.2.1.

No hypothesis is needed on `γ`: the identity holds for every `γ`, the degenerate `γ = 0` giving
the do-nothing iteration and the factor `1`. -/
theorem richardson_reduction (n : ℕ) (γ : ℝ) (b x₀ xstar : Fin n → ℝ)
    (hxstar : laplacian1D n *ᵥ xstar = b) (k : Fin n) (j : ℕ) :
    sineVec n k ⬝ᵥ ((Chapter04.richardsonStep (laplacian1D n) γ⁻¹ b)^[j] x₀ - xstar) =
      (1 - eigenvalue1D n k / γ) ^ j * (sineVec n k ⬝ᵥ (x₀ - xstar)) := by
  have hfix : Chapter04.affineStep (1 - γ⁻¹ • laplacian1D n) (γ⁻¹ • b) xstar = xstar := by
    rw [Chapter04.affineStep_fixed_iff, sub_sub_cancel, Matrix.smul_mulVec, hxstar]
  have hsymm : (1 - γ⁻¹ • laplacian1D n).IsSymm :=
    Matrix.isSymm_one.sub ((laplacian1D_isSymm n).smul γ⁻¹)
  have heig : (1 - γ⁻¹ • laplacian1D n) *ᵥ sineVec n k =
      (1 - eigenvalue1D n k / γ) • sineVec n k := by
    rw [richardson_iterationMatrix_mulVec_sineVec, div_eq_inv_mul]
  rw [Chapter04.richardsonStep_eq_affine, Chapter04.affineStep_iterate_sub hfix,
    dotProduct_pow_mulVec hsymm heig]

/-- Saad §13.2.1, the display closing the section: with `γ = 4` the Richardson reduction
factor is `η_k = cos²(θ_k/2)`. -/
theorem richardson_factor_eq_cos_sq (n : ℕ) (k : Fin n) :
    1 - eigenvalue1D n k / 4 = Real.cos (theta n k / 2) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (theta n k / 2)
  rw [eigenvalue1D]
  linarith

/-- Saad §13.2.1: the *smallest* Richardson factor at `γ = 4` is `1 - sin²(π/(2(n+1)))`, attained
at `k = 1`; since `sin(π/(2(n+1))) ≈ π h/2`, that is `1 - O(h²)` and the iteration converges
slowly. -/
theorem richardson_factor_le (n : ℕ) (k : Fin n) :
    1 - eigenvalue1D n k / 4 ≤ 1 - Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h := sin_sq_theta_div_two_ge n k
  rw [eigenvalue1D]
  linarith

/-- **Saad §13.2.1, the smoothing property of Richardson's iteration**: on the oscillatory half
`k > n/2` of the spectrum — in `0`-based indices, `n + 1 ≤ 2(k + 1)` — the reduction factor at
`γ = 4` is at most `1/2`, independently of the mesh size. -/
theorem richardson_factor_le_half_of_oscillatory (n : ℕ) {k : Fin n}
    (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) : 1 - eigenvalue1D n k / 4 ≤ 1 / 2 := by
  have h := sin_sq_theta_div_two_ge_half n hk
  rw [eigenvalue1D]
  linarith

end Richardson

/-! ### §13.2.2 Weighted Jacobi, (13.17)–(13.25) -/

section WeightedJacobi

variable {n m : ℕ} {ω : ℝ}

/-- Saad (13.19)–(13.20): the weighted Jacobi iteration matrix is `J_ω = I - ω D⁻¹ A`.  It is the
backbone's `Matrix.jorSplitting`, whose `M` is `ω⁻¹ D`. -/
theorem jorSplitting_iterationOperator_eq {N : Type*} [Fintype N] [DecidableEq N]
    (A : Matrix N N ℝ) (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator = 1 - ω • ((diagPart A)⁻¹ * A) := by
  have h1 : (jorSplitting A h hω).iterationOperator =
      1 - Ring.inverse (ω⁻¹ • diagPart A) * A := rfl
  have hinv : (ω⁻¹ • diagPart A)⁻¹ = ω • (diagPart A)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hω, one_smul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp h)]
  rw [h1, ← nonsing_inv_eq_ringInverse, hinv, Matrix.smul_mul]

/-- Weighted Jacobi on a matrix whose diagonal is a multiple of the identity is
`J_ω = I - (ω/c) A`. -/
private theorem jorSplitting_of_diagPart_eq {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} {c : ℝ} (hc : c ≠ 0) (hA : diagPart A = c • 1)
    (h : IsUnit (diagPart A)) (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator = 1 - (ω / c) • A := by
  have hinv : (c • (1 : Matrix N N ℝ))⁻¹ = c⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Matrix.one_mul, one_smul]
  rw [jorSplitting_iterationOperator_eq A h hω, hA, hinv, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, ← div_eq_mul_inv]

/-- Since `D = 2 I` for the one-dimensional model matrix, weighted Jacobi on it is
`J_ω = I - (ω/2) A`. -/
theorem jorSplitting_laplacian1D (n : ℕ) (hω : ω ≠ 0) :
    (jorSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n) hω).iterationOperator =
      1 - (ω / 2) • laplacian1D n :=
  jorSplitting_of_diagPart_eq two_ne_zero (diagPart_laplacian1D n) _ hω

/-- Since `D = 4 I` for the two-dimensional model matrix, weighted Jacobi on it is
`J_ω = I - (ω/4) A`. -/
theorem jorSplitting_laplacian2D (n m : ℕ) (hω : ω ≠ 0) :
    (jorSplitting (laplacian2D n m) (isUnit_diagPart_laplacian2D n m) hω).iterationOperator =
      1 - (ω / 4) • laplacian2D n m :=
  jorSplitting_of_diagPart_eq (by norm_num) (diagPart_laplacian2D n m) _ hω

/-- **Saad (13.21)**: the weighted Jacobi iteration matrix of the one-dimensional model problem has
the discrete sine vectors as eigenvectors, with eigenvalues
`μ_k(ω) = 1 - 2 ω sin²(kπ/(2(n+1)))`. -/
theorem equation_13_21 (n : ℕ) (hω : ω ≠ 0) (k : Fin n) :
    (jorSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n) hω).iterationOperator *ᵥ
        sineVec n k =
      (1 - 2 * ω * Real.sin (theta n k / 2) ^ 2) • sineVec n k := by
  rw [jorSplitting_laplacian1D n hω, sub_mulVec, one_mulVec, Matrix.smul_mulVec,
    laplacian1D_mulVec_sineVec, smul_smul, eigenvalue1D,
    show ω / 2 * (4 * Real.sin (theta n k / 2) ^ 2) = 2 * ω * Real.sin (theta n k / 2) ^ 2 by
      ring,
    sub_smul, one_smul]

/-- **Saad (13.21) in two dimensions**: the eigenvalues of the weighted Jacobi iteration matrix of
the two-dimensional model problem are
`μ_{k,l}(ω) = 1 - ω (sin²(kπ/(2(n+1))) + sin²(lπ/(2(m+1))))`, with the tensor eigenvectors
`w_k ⊗ v_l`. -/
theorem equation_13_21_two (n m : ℕ) (hω : ω ≠ 0) (k : Fin n) (l : Fin m) :
    (jorSplitting (laplacian2D n m) (isUnit_diagPart_laplacian2D n m) hω).iterationOperator *ᵥ
        kroneckerVec (sineVec n k) (sineVec m l) =
      (1 - ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)) •
        kroneckerVec (sineVec n k) (sineVec m l) := by
  rw [jorSplitting_laplacian2D n m hω, sub_mulVec, one_mulVec, Matrix.smul_mulVec,
    laplacian2D_mulVec_kroneckerVec, smul_smul, eigenvalue1D, eigenvalue1D,
    show ω / 4 * (4 * Real.sin (theta n k / 2) ^ 2 + 4 * Real.sin (theta m l / 2) ^ 2) =
        ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2) by ring,
    sub_smul, one_smul]

/-- **Saad (13.22)**: for `0 < ω ≤ 1` the spectral radius of the weighted Jacobi iteration matrix
of the one-dimensional model problem is `1 - 2 ω sin²(π/(2(n+1))) ≈ 1 - ω π² h²/2`, attained at
`k = 1`; so `ω = 1` is the best choice *as an iteration*, and every choice converges slowly. -/
theorem equation_13_22 (n : ℕ) (hω0 : 0 < ω) (hω1 : ω ≤ 1) (k : Fin n) :
    |1 - 2 * ω * Real.sin (theta n k / 2) ^ 2| ≤
      1 - 2 * ω * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 := by
  have h1 := sin_sq_theta_div_two_ge n k
  have h2 := sin_sq_theta_div_two_le n k
  rw [abs_le]
  constructor <;> nlinarith

/-- Saad (13.23): on the oscillatory half `k > n/2` of the spectrum the weighted Jacobi
eigenvalues lie in an interval that does not depend on the mesh.

The book prints the upper bound as `1 - ω/2`; that is true but not sharp. On the oscillatory
half `sin²(θ_k/2) ≥ 1/2`, so `μ_k(ω) = 1 - 2ω sin²(θ_k/2) ≤ 1 - ω`, which is what is proved
here. Saad's own conclusion two lines later — that `ω = 2/3` gives eigenvalues between `-1/3`
and `1/3` — needs `1 - ω`, not `1 - ω/2`, which would give `2/3`. The `1 - ω/2` of (13.23) is
the correct bound in *two* dimensions, where it is (13.25). -/
theorem weightedJacobi_eigenvalue_mem_Ioc (n : ℕ) (hω : 0 < ω) {k : Fin n}
    (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    1 - 2 * ω * Real.sin (theta n k / 2) ^ 2 ∈ Set.Ioc (1 - 2 * ω) (1 - ω) := by
  have h1 := sin_sq_theta_div_two_ge_half n hk
  have h2 := sin_sq_theta_div_two_lt_one n k
  exact Set.mem_Ioc.2 ⟨by nlinarith, by nlinarith⟩

/-- Saad §13.2.2, the prose after (13.23): the mesh-independent **smoothing factor** of
weighted Jacobi at `ω = 1/2` in one dimension. The book says `3/4`, reading it off the
unsharp `1 - ω/2` of (13.23); the sharp value is `1/2`, which is what is proved here. -/
theorem smoothingFactor_one_half (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    |1 - 2 * (1 / 2 : ℝ) * Real.sin (theta n k / 2) ^ 2| ≤ 1 / 2 := by
  have h := Set.mem_Ioc.1 (weightedJacobi_eigenvalue_mem_Ioc (ω := 1 / 2) n (by norm_num) hk)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- Saad §13.2.2, the prose after (13.23): the mesh-independent **smoothing factor** of
weighted Jacobi in one dimension is minimized at `ω = 2/3`, where it is `1/3`. -/
theorem smoothingFactor_two_thirds (n : ℕ) {k : Fin n} (hk : n + 1 ≤ 2 * ((k : ℕ) + 1)) :
    |1 - 2 * (2 / 3 : ℝ) * Real.sin (theta n k / 2) ^ 2| ≤ 1 / 3 := by
  have h := Set.mem_Ioc.1 (weightedJacobi_eigenvalue_mem_Ioc (ω := 2 / 3) n (by norm_num) hk)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- **Saad (13.25)**: in two dimensions a mode is oscillatory when at least one of its two
indices is, and then the weighted Jacobi eigenvalue lies in `(1 - 2ω, 1 - ω/2]`. Here the
book's `1 - ω/2` *is* sharp, both ends meeting at `ω = 4/5`. -/
theorem weightedJacobi2D_eigenvalue_mem_Ioc (n m : ℕ) (hω : 0 < ω) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    1 - ω * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2) ∈
      Set.Ioc (1 - 2 * ω) (1 - ω / 2) := by
  have hk2 := sin_sq_theta_div_two_lt_one n k
  have hl2 := sin_sq_theta_div_two_lt_one m l
  have hk1 := sin_theta_div_two_pos n k
  have hl1 := sin_theta_div_two_pos m l
  have hhalf : 1 / 2 ≤ Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2 := by
    rcases hkl with h | h
    · nlinarith [sin_sq_theta_div_two_ge_half n h]
    · nlinarith [sin_sq_theta_div_two_ge_half m h]
  exact Set.mem_Ioc.2 ⟨by nlinarith, by nlinarith⟩

/-- Saad (13.25) and the prose after it: in two dimensions the smoothing factor at `ω = 1/2`
is `3/4`. -/
theorem smoothingFactor2D_one_half (n m : ℕ) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    |1 - (1 / 2 : ℝ) * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)| ≤
      3 / 4 := by
  have h := Set.mem_Ioc.1
    (weightedJacobi2D_eigenvalue_mem_Ioc (ω := 1 / 2) n m (by norm_num) hkl)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

/-- Saad (13.25): in two dimensions the smoothing factor is minimized at `ω = 4/5`, where the
two ends `|1 - 2ω|` and `1 - ω/2` of `weightedJacobi2D_eigenvalue_mem_Ioc` meet at `3/5`.

The book's sentence "`ω = 3/5` yields a smoothing factor of `4/5`" transposes the two
numbers: at `ω = 3/5` the factor is `7/10`, and it is `ω = 4/5` that yields `3/5`. Its next
sentence, that `ω = 4/5` is the best choice, is right. -/
theorem smoothingFactor2D_four_fifths (n m : ℕ) {k : Fin n} {l : Fin m}
    (hkl : n + 1 ≤ 2 * ((k : ℕ) + 1) ∨ m + 1 ≤ 2 * ((l : ℕ) + 1)) :
    |1 - (4 / 5 : ℝ) * (Real.sin (theta n k / 2) ^ 2 + Real.sin (theta m l / 2) ^ 2)| ≤
      3 / 5 := by
  have h := Set.mem_Ioc.1
    (weightedJacobi2D_eigenvalue_mem_Ioc (ω := 4 / 5) n m (by norm_num) hkl)
  rw [abs_le]
  constructor <;> [linarith [h.1]; linarith [h.2]]

end WeightedJacobi

/-! ### §13.2.3 Gauss–Seidel, (13.26)–(13.29) -/

section GaussSeidel

variable {n : ℕ}

/-- Saad §13.2.3: the Gauss–Seidel iteration matrix `G = (D - E)⁻¹ F` of the one-dimensional model
problem. -/
noncomputable def gaussSeidel1D (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (gaussSeidelSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator

/-- Saad (4.20) for Gauss–Seidel: `G = I - (D - E)⁻¹ A`, with `D - E` the lower bidiagonal factor
`diagPart A + strictLower A`. -/
theorem gaussSeidel1D_eq (n : ℕ) :
    gaussSeidel1D n =
      1 - (diagPart (laplacian1D n) + strictLower (laplacian1D n))⁻¹ * laplacian1D n := by
  have h1 : gaussSeidel1D n =
      1 - Ring.inverse (diagPart (laplacian1D n) + strictLower (laplacian1D n)) *
        laplacian1D n := rfl
  rw [h1, nonsing_inv_eq_ringInverse]

/-- Saad (13.29): the vector `u_k` with components `(cos θ_k)^j sin(j θ_k)`.

The book prints `|cos θ_k|^j`; that is a slip.  With the absolute value the vector is *not* an
eigenvector whenever `cos θ_k < 0` — at `n = 2`, `k = 2` it gives `(2, -1)` while the eigenvector
is `(2, 1)` — and the derivation of §13.2.3 produces the signed power: the difference equation
`u_{j+1} = λ(2 u_j - u_{j-1})` forces the ratio to be `cos θ_k` itself. -/
noncomputable def gaussSeidelVec (n : ℕ) (k : Fin n) : Fin n → ℝ :=
  fun j => Real.cos (theta n k) ^ ((j : ℕ) + 1) * Real.sin ((((j : ℕ) : ℝ) + 1) * theta n k)

/-- A vector on `Fin n` extended by the homogeneous Dirichlet boundary values to all of `ℕ`, so
that the three-term rows of the model matrix and of its triangular parts have a uniform
formula. -/
private def pad (v : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => if h : j < n then v ⟨j, h⟩ else 0

/-- The padded vector vanishes at the lower boundary. -/
private theorem pad_zero (v : Fin n → ℝ) : pad v 0 = 0 := rfl

/-- The padded vector at a successor index. -/
private theorem pad_succ (v : Fin n → ℝ) (j : ℕ) :
    pad v (j + 1) = if h : j < n then v ⟨j, h⟩ else 0 := rfl

/-- The padded vector at an interior index. -/
private theorem pad_val_succ (v : Fin n → ℝ) (i : Fin n) : pad v ((i : ℕ) + 1) = v i := by
  rw [pad_succ, dite_eq_left i.isLt]

/-- The padded vector vanishes past the upper boundary. -/
private theorem pad_of_gt (v : Fin n → ℝ) {j : ℕ} (hj : n < j) : pad v j = 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [pad_succ, dite_eq_right (by omega)]

/-- The sum picking out the padded entry at index `j + 1`. -/
private theorem sum_ite_pad (c : ℝ) (v : Fin n → ℝ) (j : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) = j then c * v i else 0) = c * pad v (j + 1) := by
  have h : ∀ i : Fin n, (if (i : ℕ) = j then c * v i else 0) =
      if (i : ℕ) = j then c * pad v ((i : ℕ) + 1) else 0 := by
    intro i; rw [pad_val_succ]
  rw [Finset.sum_congr rfl fun i _ => h i,
    Fin.sum_univ_eq_sum_range fun i => if i = j then c * pad v (i + 1) else 0,
    Finset.sum_ite_eq' (Finset.range n) j fun i => c * pad v (i + 1)]
  by_cases hj : j < n
  · rw [ite_eq_left (Finset.mem_range.2 hj)]
  · rw [ite_eq_right fun hmem => hj (Finset.mem_range.1 hmem), pad_of_gt v (by omega), mul_zero]

/-- The sum picking out the padded entry just below index `j`. -/
private theorem sum_ite_succ_pad (c : ℝ) (v : Fin n → ℝ) (j : ℕ) :
    ∑ i : Fin n, (if (i : ℕ) + 1 = j then c * v i else 0) = c * pad v j := by
  cases j with
  | zero => simp [pad_zero]
  | succ j =>
    have h : ∀ i : Fin n, ((i : ℕ) + 1 = j + 1) = ((i : ℕ) = j) := fun i => by simp
    simp only [h]
    exact sum_ite_pad c v j

/-- The rows of the one-dimensional model matrix, uniformly across the first, the last and the
interior rows. -/
private theorem laplacian1D_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    (laplacian1D n *ᵥ v) i = -pad v (i : ℕ) + 2 * pad v ((i : ℕ) + 1) - pad v ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, laplacian1D n i j * v j =
      (if (j : ℕ) + 1 = (i : ℕ) then -1 * v j else 0) +
        (if (j : ℕ) = (i : ℕ) then 2 * v j else 0) +
        (if (j : ℕ) = (i : ℕ) + 1 then -1 * v j else 0) := by
    intro j
    rw [laplacian1D_apply]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_succ_pad, sum_ite_pad, sum_ite_pad,
    show (i : ℕ) + 1 + 1 = (i : ℕ) + 2 by omega]
  ring

/-- The rows of `D - E`, the lower bidiagonal factor of the Gauss–Seidel splitting. -/
private theorem gsLower_mulVec_apply (v : Fin n → ℝ) (i : Fin n) :
    ((diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ v) i =
      2 * pad v ((i : ℕ) + 1) - pad v (i : ℕ) := by
  have hsplit : ∀ j : Fin n,
      (diagPart (laplacian1D n) + strictLower (laplacian1D n)) i j * v j =
        (if (j : ℕ) + 1 = (i : ℕ) then -1 * v j else 0) +
          (if (j : ℕ) = (i : ℕ) then 2 * v j else 0) := by
    intro j
    simp only [Matrix.add_apply, diagPart_apply, strictLower_apply, laplacian1D_apply,
      ← Fin.val_eq_val, Fin.lt_def]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, sum_ite_succ_pad, sum_ite_pad]
  ring

/-- The padded Gauss–Seidel vector is `(cos θ_k)^j sin(j θ_k)` at every index up to `n + 1`: the
value `0` at both ends is exactly `sin 0 = 0` and `sin((n+1)θ_k) = sin((k+1)π) = 0`. -/
private theorem pad_gaussSeidelVec (n : ℕ) (k : Fin n) {j : ℕ} (hj : j ≤ n + 1) :
    pad (gaussSeidelVec n k) j =
      Real.cos (theta n k) ^ j * Real.sin ((j : ℝ) * theta n k) := by
  cases j with
  | zero => simp [pad_zero]
  | succ j =>
    rw [pad_succ]
    by_cases h : j < n
    · rw [dite_eq_left h]
      simp only [gaussSeidelVec]
      push_cast
      ring
    · rw [dite_eq_right h]
      have hjn : j = n := by omega
      subst hjn
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      have hrw : (((j : ℕ) : ℝ) + 1) * theta j k = (((k : ℕ) : ℤ) + 1 : ℤ) * π := by
        rw [theta]; field_simp; push_cast; ring
      push_cast
      rw [hrw, Real.sin_int_mul_pi, mul_zero]

/-- **Saad (13.29)**: the vector `u_k` of `gaussSeidelVec` is an eigenvector of the Gauss–Seidel
iteration matrix of the one-dimensional model problem, with eigenvalue `cos²θ_k`.

At `cos θ_k = 0` — that is `n` odd and `k = (n+1)/2`, where the eigenvalue is `0` — the formula
degenerates to the zero vector and says nothing; there the eigenvector is `e₁`
(`gaussSeidel1D_mulVec_single`). -/
theorem equation_13_29 (n : ℕ) (k : Fin n) :
    gaussSeidel1D n *ᵥ gaussSeidelVec n k = (Real.cos (theta n k) ^ 2) • gaussSeidelVec n k := by
  have key : laplacian1D n *ᵥ gaussSeidelVec n k =
      (1 - Real.cos (theta n k) ^ 2) •
        ((diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ gaussSeidelVec n k) := by
    funext i
    have hi : (i : ℕ) < n := i.isLt
    rw [laplacian1D_mulVec_apply, Pi.smul_apply, gsLower_mulVec_apply, smul_eq_mul,
      pad_gaussSeidelVec n k (by omega), pad_gaussSeidelVec n k (by omega),
      pad_gaussSeidelVec n k (by omega)]
    have e0 : ((i : ℕ) : ℝ) * theta n k = (((i : ℕ) : ℝ) + 1) * theta n k - theta n k := by ring
    have e2 : (((i : ℕ) : ℝ) + 2) * theta n k =
        (((i : ℕ) : ℝ) + 1) * theta n k + theta n k := by ring
    push_cast
    rw [e0, e2, Real.sin_sub, Real.sin_add]
    ring
  rw [gaussSeidel1D_eq, sub_mulVec, one_mulVec, ← mulVec_mulVec, key, Matrix.mulVec_smul,
    Chapter04.inv_mulVec_mulVec (isUnit_diagPart_add_strictLower (isUnit_diagPart_laplacian1D n))]
  module

/-- The Gauss–Seidel eigenvector of (13.29) is nonzero exactly when `cos θ_k ≠ 0`. -/
theorem gaussSeidelVec_ne_zero (n : ℕ) {k : Fin n} (hk : Real.cos (theta n k) ≠ 0) :
    gaussSeidelVec n k ≠ 0 := by
  intro h
  have h0 : gaussSeidelVec n k ⟨0, k.pos⟩ = 0 := by rw [h]; rfl
  simp only [gaussSeidelVec] at h0
  norm_num at h0
  rcases h0 with h' | h'
  · exact hk h'
  · exact absurd h' (sin_theta_pos n k).ne'

/-- **Saad §13.2.3, the degenerate case of (13.29)**: `e₁` is an eigenvector of the Gauss–Seidel
iteration matrix for the eigenvalue `0`, whatever `n`.  This is what stands in for (13.29) at
`λ_k = 0`, where that formula collapses to the zero vector. -/
theorem gaussSeidel1D_mulVec_single (n : ℕ) (hn : 0 < n) :
    gaussSeidel1D n *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) = 0 := by
  have hkey : laplacian1D n *ᵥ (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) =
      (diagPart (laplacian1D n) + strictLower (laplacian1D n)) *ᵥ
        (Pi.single ⟨0, hn⟩ 1 : Fin n → ℝ) := by
    funext i
    have h2 : pad (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ((i : ℕ) + 2) = 0 := by
      rw [pad_succ]
      by_cases h : (i : ℕ) + 1 < n
      · rw [dite_eq_left h]
        exact Pi.single_eq_of_ne (fun hh => by simpa using congrArg Fin.val hh) 1
      · rw [dite_eq_right h]
    rw [laplacian1D_mulVec_apply, gsLower_mulVec_apply, h2]
    ring
  rw [gaussSeidel1D_eq, sub_mulVec, one_mulVec, ← mulVec_mulVec, hkey,
    Chapter04.inv_mulVec_mulVec (isUnit_diagPart_add_strictLower (isUnit_diagPart_laplacian1D n)),
    sub_self]

/-- The Jacobi iteration matrix of the one-dimensional model problem is `tridiag(1/2, 0, 1/2)`,
whose eigenvalues are the `cos θ_k`. -/
theorem jacobiSplitting_laplacian1D_iterationOperator (n : ℕ) :
    (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator =
      symmTridiagonalToeplitz n (1 / 2) 0 := by
  have h1 : (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator =
      1 - Ring.inverse (diagPart (laplacian1D n)) * laplacian1D n := rfl
  have hinv : ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (2 : ℝ)⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (two_ne_zero (α := ℝ)), Matrix.one_mul, one_smul]
  rw [h1, ← nonsing_inv_eq_ringInverse, diagPart_laplacian1D, hinv, Matrix.smul_mul,
    Matrix.one_mul]
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, laplacian1D_apply,
    symmTridiagonalToeplitz_apply', smul_eq_mul]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- Saad §13.2.3: the eigenvalues of the Jacobi iteration matrix of the one-dimensional model
problem are exactly the `cos θ_k`. -/
theorem jacobi1D_hasEigenvalue_iff (n : ℕ) (μ : ℝ) :
    Module.End.HasEigenvalue
        (toEuclideanLin
          (jacobiSplitting (laplacian1D n) (isUnit_diagPart_laplacian1D n)).iterationOperator)
        μ ↔
      ∃ k : Fin n, μ = Real.cos (theta n k) := by
  rw [jacobiSplitting_laplacian1D_iterationOperator, symmTridiagonalToeplitz_hasEigenvalue_iff]
  refine exists_congr fun k => ?_
  rw [theta]
  constructor <;> intro h <;> linarith

/-- A real eigenvector exhibits its real eigenvalue in the complex spectrum of the
complexification. -/
private theorem ofReal_mem_spectrum_complexify_of_mulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {v : Fin N → ℝ} {μ : ℝ} (hv : A *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ((μ : ℝ) : ℂ) ∈ spectrum ℂ (complexify A) := by
  rw [Matrix.ofReal_mem_spectrum_complexify_iff, ← Matrix.hasEigenvalue_toEuclideanLin_iff]
  refine Module.End.hasEigenvalue_of_hasEigenvector
    (x := WithLp.toLp 2 v) ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h => hv0 ?_⟩
  · change WithLp.toLp 2 (A *ᵥ v) = _
    rw [hv]
    rfl
  · simpa using congrArg WithLp.ofLp h

/-- **Saad §13.2.3**: `cos²θ_k` is an eigenvalue of the Gauss–Seidel iteration matrix of the
one-dimensional model problem, for every `k`.

This is Saad's own shortcut: the model matrix is tridiagonal, hence consistently ordered, so
Young's theorem (Saad Theorem 4.16, `SaadSparse.Chapter04.theorem_4_16_mpr`) says that the SOR
eigenvalues at `ω = 1` are the squares of the Jacobi ones, and the Jacobi eigenvalues are the
`cos θ_k`.  The eigenvectors are (13.29), `equation_13_29`.

The smallest of these eigenvalues are those with `k` near `n/2`, so Gauss–Seidel damps the
*middle* of the spectrum fastest — which is not the same thing as damping the oscillatory modes,
and is why §13.2.3 ends without a smoothing factor. -/
theorem gaussSeidel_eigenvalues (n : ℕ) (k : Fin n) :
    ((Real.cos (theta n k) ^ 2 : ℝ) : ℂ) ∈ spectrum ℂ (complexify (gaussSeidel1D n)) := by
  by_cases hc : Real.cos (theta n k) = 0
  · have h0 : ((Real.cos (theta n k) ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by rw [hc]; norm_num
    rw [h0]
    refine ofReal_mem_spectrum_complexify_of_mulVec
      (v := Pi.single ⟨0, k.pos⟩ 1) ?_ ?_
    · rw [gaussSeidel1D_mulVec_single n k.pos, zero_smul]
    · intro h
      simpa using congrFun h ⟨0, k.pos⟩
  · exact ofReal_mem_spectrum_complexify_of_mulVec (equation_13_29 n k)
      (gaussSeidelVec_ne_zero n hc)

end GaussSeidel

end SaadSparse.Chapter13
