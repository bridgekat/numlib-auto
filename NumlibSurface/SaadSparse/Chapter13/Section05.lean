import Numlib.LinearSolve.Multigrid.TwoGrid
import NumlibSurface.SaadSparse.Chapter13.Section04

/-!
# Saad §13.5: analysis of the two-grid cycle

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §13.5: the two subspaces (13.57)–(13.61) of the Galerkin two-grid cycle, the pair of norms
`‖·‖_D` and `‖·‖_{D⁻¹}` of §13.5.2, the smoothing property (13.62) and the approximation property
(13.63), Theorem 13.3 with its rate (13.64), and Example 13.8, the verification of the smoothing
property for weighted Jacobi.

Everything runs on `Numlib/LinearSolve/Multigrid/TwoGrid.lean`, whose two hypotheses
`Multigrid.IsSmootherWith` and `Multigrid.IsApproximationWith` are (13.62) and (13.63) for an
abstract dual pair of seminorms.  What the surface adds is Saad's concrete pair,
`‖x‖_D = (D x, x)^{1/2}` and `‖y‖_{D⁻¹} = (D⁻¹ y, y)^{1/2}` with `D = diag(A)`, and the proof that
it *is* a dual pair (`isDualSeminormPair_normD`), which is Cauchy–Schwarz in the `D`-inner product.

## The two subspaces, and where Saad (13.61) goes wrong

`smoothSubspace` and `oscillatorySubspace` are Saad's `𝒮_h = Ran(Q_h)` and `𝒯_h = Ran(T_h^H)` of
(13.58).  Of the chain (13.59)–(13.61) the library proves

* `equation_13_59`: `Ω_h = 𝒮_h ⊕ 𝒯_h`;
* `equation_13_60`: `𝒮_h = Null(T_h^H) = Ran(I_H^h)`;
* `equation_13_61`: `𝒯_h = Null(Q_h) = Null(I_h^H A_h)`.

The book's last equality of (13.61) reads `𝒯_h = Null(I_h^H)`, *without* the `A_h`, and that is
false: `𝒯_h` is the `A_h`-orthogonal complement of `Ran(I_H^h)` while `Null(I_h^H)` is its Euclidean
orthogonal complement, and the argument of §13.5.1 — comparing the decomposition
`Ω_h = Ran(Q_h) ⊕ Null(Q_h)` with `Ω_h = Ran(I_H^h) ⊕ Null((I_H^h)^T)` — concludes that two
complements of one subspace are equal, which does not follow.
`oscillatorySubspace_ne_ker_of_restriction` exhibits a coarsening where they differ, already for
`tridiag(-1, 2, -1)` of order two.  Nothing in the chapter uses the false form: the proof of Theorem
13.3 uses only that `𝒯_h` is `A_h`-orthogonal to `Ran(I_H^h)`.

## The two norms

`normD` and `normDinv` are `energyNorm` of `Numlib/Analysis/InnerProductSpace/Energy.lean` at
`diag(A)` and at its inverse; `normD_sq` and `normDinv_sq` give the entrywise sums
`∑ a_ii x_i²` and `∑ y_i²/a_ii`.  Their duality is `Multigrid.isDualSeminormPair_energy`, whose two
inputs are the positive definiteness of the diagonal and the fact that `D⁻¹` is a right inverse
of `D`.

## Example 13.8

The smoothing property of weighted Jacobi is `Multigrid.isSmootherWith_richardson` at `D = diag(A)`;
what the surface supplies is Saad's constant, `γ = ρ(D^{-1/2} A D^{-1/2})`.  For a symmetric
positive definite `A` the scaled matrix `diagScaled A = D^{-1/2} A D^{-1/2}` is symmetric with
positive eigenvalues, so its spectral radius is its largest eigenvalue `gammaJacobi`: that number is
an eigenvalue (`hasEigenvalue_gammaJacobi`) and it bounds the quadratic form,
`(A x, x) ≤ γ (D x, x)` (`le_gammaJacobi`), which is what the backbone consumes.  Saad's other
formula `γ = ρ(D⁻¹ A)` is the same number, `D⁻¹ A` and `D^{-1/2} A D^{-1/2}` being similar; the
library states the bound at the symmetric one, which is where the eigenvalue estimate lives.
-/

open Finset Matrix Stationary

open scoped SaadSparse Real

namespace SaadSparse.Chapter13

variable {n m : ℕ}

/-- The action of a product of matrices on a vector. -/
private theorem mul_act {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (N : Matrix (Fin q) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : ((M * N) ⬝ x) = M ⬝ (N ⬝ x) := by
  rw [Matrix.toLpLin_mul_same]
  rfl

/-- Moving a real matrix from the second slot of the inner product to the first, transposed. -/
private theorem inner_act_act (M N : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : inner ℝ (M ⬝ x) (N ⬝ y) = inner ℝ ((Nᵀ * M) ⬝ x) y := by
  rw [← LinearMap.adjoint_inner_left (toEuclideanLin N) y (M ⬝ x), adjoint_toEuclideanLin,
    mul_act]

/-- Membership in the kernel of a matrix operator is the vanishing of `M *ᵥ v`. -/
private theorem mem_ker_toEuclideanLin_iff {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : Fin q → ℝ) :
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin q)) ∈ LinearMap.ker (toEuclideanLin M)
      ↔ M *ᵥ v = 0 :=
  ⟨fun h => congrArg WithLp.ofLp (LinearMap.mem_ker.1 h),
    fun h => LinearMap.mem_ker.2 (WithLp.ofLp_injective 2 h)⟩

/-! ### §13.5.1 Two important subspaces, (13.57)–(13.61) -/

section Subspaces

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- **Saad (13.58)**: the *smooth* subspace `𝒮_h = Ran(Q_h)`, the range of the coarse-grid
projector.  By `equation_13_60` it is the range of the prolongation. -/
noncomputable def smoothSubspace (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (toEuclideanLin (coarseProjector R A P))

/-- The smooth subspace is the range of the coarse-grid projector, by definition. -/
theorem smoothSubspace_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    smoothSubspace R A P = LinearMap.range (toEuclideanLin (coarseProjector R A P)) := rfl

/-- **Saad (13.58)**: the *oscillatory* subspace `𝒯_h = Ran(T_h^H)`, the range of the coarse-grid
correction — the errors a coarse-grid correction can leave behind. -/
noncomputable def oscillatorySubspace (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (toEuclideanLin (coarseCorrection R A P))

/-- The oscillatory subspace is the range of the coarse-grid correction, by definition. -/
theorem oscillatorySubspace_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    oscillatorySubspace R A P = LinearMap.range (toEuclideanLin (coarseCorrection R A P)) := rfl

/-- **Saad (13.60)**: the smooth subspace is the range of the prolongation,
`𝒮_h = Ran(Q_h) = Ran(I_H^h)`.  The inclusion `⊆` is the shape of `Q_h`; the reverse one is the
Galerkin identity `A_H = I_h^H A_h I_H^h`, which makes `Q_h` fix `Ran(I_H^h)` pointwise. -/
theorem equation_13_60 (h : IsCoarsening A R P) :
    smoothSubspace R A P = LinearMap.range (toEuclideanLin P) := by
  rw [smoothSubspace_def, toEuclideanLin_coarseProjector h, Multigrid.range_coarseProjection]

/-- **Saad (13.60)**: the smooth subspace is also the null space of the coarse-grid correction,
`𝒮_h = Null(T_h^H)`: the coarse-grid correction annihilates exactly the coarse space. -/
theorem equation_13_60_ker (h : IsCoarsening A R P) :
    LinearMap.ker (toEuclideanLin (coarseCorrection R A P)) = smoothSubspace R A P := by
  rw [toEuclideanLin_coarseCorrection h, Multigrid.ker_coarseCorrection, equation_13_60 h]

/-- **Saad (13.61)**: the oscillatory subspace is the null space of `I_h^H A_h`, the vectors whose
residual is `A_h`-orthogonal to the coarse space.

Saad drops the `A_h` here and writes `𝒯_h = Null(I_h^H)`; that is false, see
`oscillatorySubspace_ne_ker_of_restriction`. -/
theorem equation_13_61 (h : IsCoarsening A R P) :
    oscillatorySubspace R A P = LinearMap.ker (toEuclideanLin (R * A)) := by
  have hker : LinearMap.range (Multigrid.coarseCorrection (toEuclideanLin A)
        h.isSymmetricCoercive (toEuclideanLin P))
      = LinearMap.ker (toEuclideanLin (Pᵀ * A)) := by
    rw [Multigrid.range_coarseCorrection, adjoint_toEuclideanLin, ← Matrix.toLpLin_mul_same]
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h, hker, Matrix.smul_mul, map_smul,
    LinearMap.ker_smul _ _ hc.ne']

/-- **Saad (13.61)**: the oscillatory subspace is the null space of the coarse-grid projector,
`𝒯_h = Null(Q_h)`. -/
theorem equation_13_61_ker (h : IsCoarsening A R P) :
    LinearMap.ker (toEuclideanLin (coarseProjector R A P)) = oscillatorySubspace R A P := by
  rw [oscillatorySubspace_def, toEuclideanLin_coarseProjector h, toEuclideanLin_coarseCorrection h,
    Multigrid.ker_coarseProjection, Multigrid.range_coarseCorrection]

/-- **Saad (13.59)**: the fine space is the direct sum of the smooth and the oscillatory subspace,
`Ω_h = 𝒮_h ⊕ 𝒯_h`.  The sum is direct because `Q_h` is a projector, and it is `A_h`-orthogonal by
Lemma 13.1. -/
theorem equation_13_59 (h : IsCoarsening A R P) :
    IsCompl (smoothSubspace R A P) (oscillatorySubspace R A P) := by
  rw [equation_13_60 h, oscillatorySubspace_def, toEuclideanLin_coarseCorrection h,
    Multigrid.range_coarseCorrection]
  exact Multigrid.isCompl_range_ker (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)

end Subspaces

/-! #### The last equality of (13.61) is false -/

/-- A two-point fine grid with a one-point coarse grid: the prolongation that keeps the first
component. -/
private def counterProlongation : Matrix (Fin 2) (Fin 1) ℝ := !![1; 0]

private theorem laplacian1D_two : laplacian1D 2 = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [laplacian1D_apply]

private theorem transpose_mul_counterProlongation :
    counterProlongationᵀ * counterProlongation = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [counterProlongation, Matrix.mul_apply, Fin.sum_univ_two]

private theorem injective_counterProlongation :
    Function.Injective (toEuclideanLin counterProlongation) := by
  intro x y hxy
  have hxy' : counterProlongation *ᵥ WithLp.ofLp x = counterProlongation *ᵥ WithLp.ofLp y :=
    congrArg WithLp.ofLp hxy
  have hres := congrArg (fun z => counterProlongationᵀ *ᵥ z) hxy'
  simp only [Matrix.mulVec_mulVec, transpose_mul_counterProlongation, Matrix.one_mulVec] at hres
  exact WithLp.ofLp_injective 2 hres

/-- **Saad (13.61) is wrong as printed**: the oscillatory subspace `𝒯_h` is *not* the null space of
the restriction `I_h^H`.  With the fine matrix `tridiag(-1, 2, -1)` of order two, the prolongation
that keeps the first component and the restriction `I_h^H = (I_H^h)^T`, the second coordinate vector
lies in `Null(I_h^H)` but not in `𝒯_h = Null(I_h^H A_h)`: its residual `A e = (-1, 2)` is not
`A_h`-orthogonal to the coarse space.

Saad's argument compares the two decompositions `Ω_h = Ran(Q_h) ⊕ Null(Q_h)` and
`Ω_h = Ran(I_H^h) ⊕ Null((I_H^h)^T)`, which have the same first summand but need not have the same
second: the first splitting is `A_h`-orthogonal and the second Euclidean-orthogonal. -/
theorem oscillatorySubspace_ne_ker_of_restriction :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 1) (Fin 2) ℝ)
      (P : Matrix (Fin 2) (Fin 1) ℝ), IsCoarsening A R P ∧
        oscillatorySubspace R A P ≠ LinearMap.ker (toEuclideanLin R) := by
  have hcoarse : IsCoarsening (laplacian1D 2) counterProlongationᵀ counterProlongation :=
    ⟨laplacian1D_posDef 2, injective_counterProlongation, 1, one_pos, (one_smul ℝ _).symm⟩
  refine ⟨laplacian1D 2, counterProlongationᵀ, counterProlongation, hcoarse, ?_⟩
  rw [equation_13_61 hcoarse]
  intro hcontra
  have h1 : (WithLp.toLp 2 ![0, 1] : EuclideanSpace ℝ (Fin 2))
      ∈ LinearMap.ker (toEuclideanLin counterProlongationᵀ) := by
    rw [mem_ker_toEuclideanLin_iff]
    ext i
    fin_cases i
    simp [counterProlongation, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [← hcontra, mem_ker_toEuclideanLin_iff] at h1
  have h2 := congrFun h1 (0 : Fin 1)
  norm_num [counterProlongation, laplacian1D_two, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h2

/-! #### Example 13.7: what full weighting does to a sine mode -/

/-- The coarse index `k` read as a fine index.  The `m` coarse modes `w_k^{2h}` and the first `m`
fine modes `w_k^h` of the `2m + 1`-point grid carry the same `k`, and their angles are related by
`θ_k^{2h} = 2 θ_k^h`. -/
def coarseIndex (m : ℕ) (k : Fin m) : Fin (2 * m + 1) :=
  ⟨(k : ℕ), k.isLt.trans_le (by omega)⟩

/-- The coarse angle is twice the fine angle, `θ_k^{2h} = 2 θ_k^h`. -/
theorem two_mul_theta_coarseIndex (m : ℕ) (k : Fin m) :
    2 * theta (2 * m + 1) (coarseIndex m k) = (((k : ℕ) : ℝ) + 1) * π / ((m : ℝ) + 1) := by
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [theta, show ((coarseIndex m k : Fin (2 * m + 1)) : ℕ) = (k : ℕ) from rfl]
  push_cast
  field_simp
  ring

/-- **Saad Example 13.7**: in one dimension, full weighting turns the fine sine mode `w_k^h` into
the sine wave of the same frequency on the coarse grid, scaled by `cos²(θ_k/2)`:
`(I_h^{2h} w_k^h)_j = cos²(θ_k/2) sin(2 j θ_k)`.

The computation is the `¼[1 2 1]` stencil against the three-term identity
`sin((2j-1)θ) + sin((2j+1)θ) = 2 sin(2jθ) cos θ`, followed by the half-angle formula
`(1 + cos θ)/2 = cos²(θ/2)`. -/
theorem example_13_7 (m : ℕ) (k : Fin (2 * m + 1)) (q : Fin m) :
    (restriction1D m *ᵥ sineVec (2 * m + 1) k) q
      = Real.cos (theta (2 * m + 1) k / 2) ^ 2
        * Real.sin (2 * (((q : ℕ) : ℝ) + 1) * theta (2 * m + 1) k) := by
  have hq := q.isLt
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * m + 1), (a : ℕ) = 2 * (q : ℕ) :=
    ⟨⟨2 * (q : ℕ), by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * m + 1), (b : ℕ) = 2 * (q : ℕ) + 1 :=
    ⟨⟨2 * (q : ℕ) + 1, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * m + 1), (c : ℕ) = 2 * (q : ℕ) + 2 :=
    ⟨⟨2 * (q : ℕ) + 2, by omega⟩, rfl⟩
  have hsine : ∀ j : Fin (2 * m + 1),
      sineVec (2 * m + 1) k j = Real.sin ((((j : ℕ) : ℝ) + 1) * theta (2 * m + 1) k) :=
    fun j => by rw [sineVec_apply, theta]
  have ha' : ((a : ℕ) : ℝ) + 1 = 2 * ((q : ℕ) : ℝ) + 1 := by rw [ha]; push_cast; ring
  have hb' : ((b : ℕ) : ℝ) + 1 = 2 * ((q : ℕ) : ℝ) + 2 := by rw [hb]; push_cast; ring
  have hc' : ((c : ℕ) : ℝ) + 1 = 2 * ((q : ℕ) : ℝ) + 3 := by rw [hc]; push_cast; ring
  have hrhs : 2 * (((q : ℕ) : ℝ) + 1) * theta (2 * m + 1) k
      = (2 * ((q : ℕ) : ℝ) + 2) * theta (2 * m + 1) k := by ring
  have hcos : Real.cos (theta (2 * m + 1) k / 2) ^ 2
      = (1 + Real.cos (theta (2 * m + 1) k)) / 2 := by
    have h := Real.cos_sq (theta (2 * m + 1) k / 2)
    rw [show 2 * (theta (2 * m + 1) k / 2) = theta (2 * m + 1) k by ring] at h
    linarith
  have hsum : Real.sin ((2 * ((q : ℕ) : ℝ) + 1) * theta (2 * m + 1) k)
        + Real.sin ((2 * ((q : ℕ) : ℝ) + 3) * theta (2 * m + 1) k)
      = 2 * Real.sin ((2 * ((q : ℕ) : ℝ) + 2) * theta (2 * m + 1) k)
        * Real.cos (theta (2 * m + 1) k) := by
    rw [show (2 * ((q : ℕ) : ℝ) + 1) * theta (2 * m + 1) k
        = (2 * ((q : ℕ) : ℝ) + 2) * theta (2 * m + 1) k - theta (2 * m + 1) k by ring,
      show (2 * ((q : ℕ) : ℝ) + 3) * theta (2 * m + 1) k
        = (2 * ((q : ℕ) : ℝ) + 2) * theta (2 * m + 1) k + theta (2 * m + 1) k by ring,
      Real.sin_sub, Real.sin_add]
    ring
  rw [restriction1D_mulVec m _ q ha hb hc, hsine, hsine, hsine, ha', hb', hc', hrhs, hcos]
  linear_combination hsum / 4

/-- **Saad Example 13.7**: a fine mode whose index is that of a coarse mode restricts to exactly
that coarse mode, damped by `cos²(θ_k/2)`: `I_h^{2h} w_k^h = cos²(θ_k/2) w_k^{2h}`. -/
theorem example_13_7_smul (m : ℕ) (k : Fin m) :
    restriction1D m *ᵥ sineVec (2 * m + 1) (coarseIndex m k)
      = Real.cos (theta (2 * m + 1) (coarseIndex m k) / 2) ^ 2 • sineVec m k := by
  funext q
  rw [Pi.smul_apply, smul_eq_mul, example_13_7, sineVec_apply,
    ← two_mul_theta_coarseIndex m k]
  ring_nf

/-- **Saad Example 13.7**, the oscillatory half: on the upper half of the spectrum, `k ≥ n/2`, the
damping factor `cos²(θ_k/2)` of full weighting is at most `½`, so an oscillatory mode is close to
the null space of `I_h^{2h}`, that is, close to `𝒯_h`. -/
theorem example_13_7_le_half (m : ℕ) {k : Fin (2 * m + 1)}
    (hk : 2 * m + 2 ≤ 2 * ((k : ℕ) + 1)) :
    Real.cos (theta (2 * m + 1) k / 2) ^ 2 ≤ 1 / 2 := by
  have h := sin_sq_theta_div_two_ge_half (2 * m + 1) (k := k) (by omega)
  have hpy := Real.sin_sq_add_cos_sq (theta (2 * m + 1) k / 2)
  linarith

/-! ### §13.5.2 The two norms of the convergence analysis -/

section Norms

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Saad §13.5.2**: the `D`-norm `‖x‖_D = (D x, x)^{1/2} = ‖D^{1/2} x‖₂`, with `D` the diagonal
of `A`. -/
noncomputable def normD (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm (toEuclideanLin (diagPart A)) x

/-- **Saad §13.5.2**: the `D⁻¹`-norm `‖y‖_{D⁻¹} = (D⁻¹ y, y)^{1/2} = ‖D^{-1/2} y‖₂`.  Applied to a
residual `y = A e` it is the norm Saad abbreviates `‖A e‖_{D⁻¹}`. -/
noncomputable def normDinv (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  energyNorm (toEuclideanLin (diagPart A)⁻¹) y

/-- The diagonal of a symmetric positive definite matrix is positive definite. -/
theorem posDef_diagPart (hA : A.PosDef) : (diagPart A).PosDef := by
  have hd : diagPart A = diagonal fun i => A i i := rfl
  rw [hd, Matrix.posDef_diagonal_iff]
  exact fun i => Matrix.PosDef.diag_pos hA

/-- The diagonal of a symmetric positive definite matrix is invertible. -/
theorem isUnit_diagPart_of_posDef (hA : A.PosDef) : IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).2 fun i => (Matrix.PosDef.diag_pos hA (i := i)).ne'

/-- The inverse of the diagonal of a symmetric positive definite matrix is positive definite, so
`‖·‖_{D⁻¹}` is a norm. -/
theorem posDef_inv_diagPart (hA : A.PosDef) : ((diagPart A)⁻¹).PosDef := by
  rw [inv_diagPart (isUnit_diagPart_of_posDef hA), Matrix.posDef_diagonal_iff]
  exact fun i => inv_pos.2 (Matrix.PosDef.diag_pos hA)

/-- The `D`-norm comes from a symmetric coercive operator. -/
theorem isSymmetricCoercive_diagPart (hA : A.PosDef) :
    (toEuclideanLin (diagPart A)).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive _).1 (posDef_diagPart hA)

/-- The `D⁻¹`-norm comes from a symmetric coercive operator. -/
theorem isSymmetricCoercive_inv_diagPart (hA : A.PosDef) :
    (toEuclideanLin (diagPart A)⁻¹).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive _).1 (posDef_inv_diagPart hA)

/-- `D⁻¹` is a right inverse of `D`, the hypothesis of
`Multigrid.isDualSeminormPair_energy`. -/
theorem toEuclideanLin_diagPart_inv (hA : A.PosDef) (u : EuclideanSpace ℝ (Fin n)) :
    (diagPart A ⬝ ((diagPart A)⁻¹ ⬝ u)) = u := by
  rw [← mul_act, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_diagPart_of_posDef hA))]
  exact congrFun (congrArg _ (Matrix.toLpLin_one 2)) u

/-- **Saad §13.5.2**: `‖x‖_D² = ∑ a_ii x_i²`. -/
theorem normD_sq (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    normD A x ^ 2 = ∑ i, A i i * WithLp.ofLp x i ^ 2 := by
  rw [normD, (isSymmetricCoercive_diagPart hA).energyNorm_sq, real_inner_apply_self,
    RCLike.re_to_real, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show diagPart A = diagonal fun j => A j j from rfl, mulVec_diagonal]
    ring

/-- **Saad §13.5.2**: `‖y‖_{D⁻¹}² = ∑ y_i²/a_ii`. -/
theorem normDinv_sq (hA : A.PosDef) (y : EuclideanSpace ℝ (Fin n)) :
    normDinv A y ^ 2 = ∑ i, WithLp.ofLp y i ^ 2 / A i i := by
  rw [normDinv, (isSymmetricCoercive_inv_diagPart hA).energyNorm_sq, real_inner_apply_self,
    RCLike.re_to_real, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by
    rw [inv_diagPart (isUnit_diagPart_of_posDef hA), mulVec_diagonal]
    ring

/-- **Saad §13.5.2**: `‖·‖_D` and `‖·‖_{D⁻¹}` are dual to each other,
`|(u, w)| ≤ ‖u‖_{D⁻¹} ‖w‖_D`.  This is Cauchy–Schwarz in the `D`-inner product, written
`(u, w) = (D D⁻¹ u, w)`, and it is the only property of the pair that Theorem 13.3 uses. -/
theorem isDualSeminormPair_normD (hA : A.PosDef) :
    Multigrid.IsDualSeminormPair ℝ (normD A) (normDinv A) :=
  Multigrid.isDualSeminormPair_energy (isSymmetricCoercive_diagPart hA)
    (toEuclideanLin_diagPart_inv hA)

end Norms

/-! ### §13.5.2 The smoothing and approximation properties, (13.62)–(13.63) -/

/-- **Saad (13.62)**, the *smoothing property* with constant `α`:
`‖S e‖_A² ≤ ‖e‖_A² - α ‖A e‖_{D⁻¹}²` for every error `e`.  It is a property of the smoother, and it
is not provable by linear algebra alone: Example 13.8 verifies it for weighted Jacobi. -/
def equation_13_62 (A S : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) : Prop :=
  Multigrid.IsSmootherWith (toEuclideanLin A) (normDinv A) (toEuclideanLin S) α

/-- The smoothing property written out. -/
theorem equation_13_62_iff (A S : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    equation_13_62 A S α ↔ ∀ e : EuclideanSpace ℝ (Fin n),
      energyNorm (toEuclideanLin A) (S ⬝ e) ^ 2
        ≤ energyNorm (toEuclideanLin A) e ^ 2 - α * normDinv A (A ⬝ e) ^ 2 :=
  Iff.rfl

/-- **Saad (13.63)**, the *approximation property* with constant `β`: every error is approximated
from the coarse space `Ran(I_H^h)` to within `β ‖e‖_A²` in the `D`-norm.  Saad writes it with a
minimum over `u_H ∈ Ω_H`; on a finite-dimensional coarse space the minimum is attained, so the
existential form `equation_13_63_iff` is the same statement. -/
def equation_13_63 (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) : Prop :=
  Multigrid.IsApproximationWith (toEuclideanLin A) (normD A) (LinearMap.range (toEuclideanLin P)) β

/-- The approximation property written out, with the minimizer of (13.63) as a witness. -/
theorem equation_13_63_iff (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) :
    equation_13_63 A P β ↔ ∀ e : EuclideanSpace ℝ (Fin n), ∃ u : EuclideanSpace ℝ (Fin m),
      normD A (e - (P ⬝ u)) ^ 2 ≤ β * energyNorm (toEuclideanLin A) e ^ 2 := by
  refine ⟨fun h e => ?_, fun h e => ?_⟩
  · obtain ⟨c, ⟨u, rfl⟩, hc⟩ := h e
    exact ⟨u, hc⟩
  · obtain ⟨u, hu⟩ := h e
    exact ⟨_, ⟨u, rfl⟩, hu⟩

/-! ### §13.5.2 Theorem 13.3 -/

section Theorem133

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ} {S : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}

/-- A coarse space of strictly smaller dimension leaves a nonzero error: the oscillatory subspace is
nontrivial as soon as `m < n`.  This is what makes the inequality `α ≤ β` of Theorem 13.3 true —
with `m = n` the coarse-grid correction is zero and every pair of constants qualifies. -/
theorem exists_ne_zero_mem_oscillatorySubspace (h : IsCoarsening A R P) (hmn : m < n) :
    ∃ e ∈ oscillatorySubspace R A P, e ≠ 0 := by
  refine (Submodule.ne_bot_iff _).1 fun hbot => absurd hmn (not_lt.2 ?_)
  set f := LinearMap.adjoint (toEuclideanLin P) ∘ₗ toEuclideanLin A with hf
  have hrange : oscillatorySubspace R A P = LinearMap.ker f := by
    rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h,
      Multigrid.range_coarseCorrection]
  have hker : Module.finrank ℝ (LinearMap.ker f) = 0 := by
    rw [hrange] at hbot
    rw [hbot, finrank_bot]
  have hadd : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.finrank_range_add_finrank_ker f
  have hle : Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) :=
    Submodule.finrank_le _
  rw [hker, add_zero, finrank_euclideanSpace_fin] at hadd
  rw [finrank_euclideanSpace_fin] at hle
  omega

/-- **Saad Theorem 13.3**, first conclusion: the smoothing constant never exceeds the approximation
constant, `α ≤ β`.  It needs a genuinely coarser grid — see
`exists_ne_zero_mem_oscillatorySubspace`. -/
theorem theorem_13_3_le (h : IsCoarsening A R P) (hmn : m < n) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) : α ≤ β := by
  obtain ⟨e, hmem, he0⟩ := exists_ne_zero_mem_oscillatorySubspace h hmn
  rw [oscillatorySubspace_def, toEuclideanLin_coarseCorrection h] at hmem
  exact Multigrid.IsSmootherWith.le_of_isApproximationWith (hA := h.isSymmetricCoercive) hsm
    (isDualSeminormPair_normD h.posDef) happ hmem he0

/-- **Saad Theorem 13.3** for a full two-grid cycle: with any number of pre-smoothing steps and at
least one post-smoothing step, the error propagation operator (13.43) contracts the `A`-norm by the
factor `√(1 - α/β)`. -/
theorem theorem_13_3_cycle (h : IsCoarsening A R P) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) (hα : 0 ≤ α) (hβ : 0 < β) {ν₁ ν₂ : ℕ} (hν : 1 ≤ ν₂)
    (v : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) (equation_13_43 R A P S ν₁ ν₂ ⬝ v)
      ≤ Real.sqrt (1 - α / β) * energyNorm (toEuclideanLin A) v := by
  have hop : (equation_13_43 R A P S ν₁ ν₂ ⬝ v)
      = Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)
          (toEuclideanLin S) ν₁ ν₂ v :=
    congrFun (congrArg _ (equation_13_43_eq h S ν₁ ν₂)) v
  rw [hop]
  exact Multigrid.energyNorm_twoGridOperator_le (hA := h.isSymmetricCoercive) hsm
    (isDualSeminormPair_normD h.posDef) happ hα hβ hν v

/-- **Saad Theorem 13.3** and its bound (13.64): one coarse-grid correction followed by one
smoothing step contracts the `A`-norm of the error, `‖S_h T_h^H e‖_A ≤ √(1 - α/β) ‖e‖_A`. -/
theorem theorem_13_3 (h : IsCoarsening A R P) (hsm : equation_13_62 A S α)
    (happ : equation_13_63 A P β) (hα : 0 ≤ α) (hβ : 0 < β) (v : EuclideanSpace ℝ (Fin n)) :
    energyNorm (toEuclideanLin A) ((S * coarseCorrection R A P) ⬝ v)
      ≤ Real.sqrt (1 - α / β) * energyNorm (toEuclideanLin A) v := by
  have heq : S * coarseCorrection R A P = equation_13_43 R A P S 0 1 := by
    rw [equation_13_43, pow_zero, pow_one, Matrix.mul_one]
  rw [heq]
  exact theorem_13_3_cycle h hsm happ hα hβ le_rfl v

/-- **Saad Theorem 13.3**, second conclusion: the two-level iteration converges, the rate
`√(1 - α/β)` of (13.64) being strictly below one whenever `α > 0`. -/
theorem theorem_13_3_lt_one (hα : 0 < α) (hβ : 0 < β) (hle : α ≤ β) :
    Real.sqrt (1 - α / β) < 1 := by
  have hpos : 0 < α / β := div_pos hα hβ
  calc Real.sqrt (1 - α / β) < Real.sqrt 1 := by
        refine Real.sqrt_lt_sqrt (by linarith [div_le_one_of_le₀ hle hβ.le]) (by linarith)
    _ = 1 := Real.sqrt_one

end Theorem133

/-! ### §13.5.2 Example 13.8: the smoothing property of weighted Jacobi -/

section Example138

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Saad (13.19)** read as a smoother: the weighted Jacobi error propagation operator
`S(ω) = I - ω D⁻¹ A`. -/
noncomputable def weightedJacobiSmoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - ω • ((diagPart A)⁻¹ * A)

/-- The weighted Jacobi smoother is the smoother (13.40) with approximate inverse `ω D⁻¹`. -/
theorem weightedJacobiSmoother_eq_smoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    weightedJacobiSmoother A ω = smoother A (ω • (diagPart A)⁻¹) := by
  rw [weightedJacobiSmoother, smoother_def, Matrix.smul_mul]

/-- The weighted Jacobi smoother is the iteration operator of the JOR splitting, which is how
§13.2.2 writes it. -/
theorem weightedJacobiSmoother_eq_iterationOperator (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit (diagPart A)) {ω : ℝ} (hω : ω ≠ 0) :
    weightedJacobiSmoother A ω = (jorSplitting A h hω).iterationOperator :=
  (jorSplitting_iterationOperator_eq A h hω).symm

/-- The weighted Jacobi smoother as an operator, in the shape
`Multigrid.isSmootherWith_richardson` expects. -/
theorem toEuclideanLin_weightedJacobiSmoother (A : Matrix (Fin n) (Fin n) ℝ) (ω : ℝ) :
    toEuclideanLin (weightedJacobiSmoother A ω)
      = 1 - (ω : ℝ) • (toEuclideanLin (diagPart A)⁻¹ ∘ₗ toEuclideanLin A) := by
  rw [weightedJacobiSmoother, map_sub, map_smul, Matrix.toEuclideanLin_mul,
    Matrix.toEuclideanLin_one]
  rfl

/-- **Saad Example 13.8**: the weighted Jacobi smoother satisfies the smoothing property (13.62)
with `α = ω(2 - ωγ)`, for any `γ` bounding the quadratic form of `A` by that of its diagonal.  The
computation is (13.65): expanding `‖S(ω) e‖_A²` leaves
`‖e‖_A² - (ω(2 I - ω D^{-1/2} A D^{-1/2}) D^{-1/2} A e, D^{-1/2} A e)`. -/
theorem example_13_8_of_le (hA : A.PosDef) {γ : ℝ}
    (hγ : ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (A ⬝ x) x ≤ γ * inner ℝ (diagPart A ⬝ x) x) (ω : ℝ) :
    equation_13_62 A (weightedJacobiSmoother A ω) (ω * (2 - ω * γ)) := by
  have hrich := Multigrid.isSmootherWith_richardson (𝕜 := ℝ)
    ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA) (isSymmetricCoercive_diagPart hA)
    (toEuclideanLin_diagPart_inv hA) (γ := γ) (fun x => by simpa using hγ x) ω
  rw [equation_13_62, toEuclideanLin_weightedJacobiSmoother]
  exact hrich

/-- `D^{1/2}`, the diagonal matrix of the square roots of the diagonal entries of `A`. -/
noncomputable def diagSqrt (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => Real.sqrt (A i i)

/-- `D^{-1/2}`, the diagonal matrix of the inverse square roots of the diagonal entries of `A`. -/
noncomputable def diagInvSqrt (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => (Real.sqrt (A i i))⁻¹

/-- **Saad §13.5.2 and §13.6.1**: the symmetrically scaled matrix `Â = D^{-1/2} A D^{-1/2}`, whose
diagonal entries are ones.  Its spectral radius is the constant `γ` of Example 13.8. -/
noncomputable def diagScaled (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagInvSqrt A * A * diagInvSqrt A

/-- `D^{1/2}` is symmetric. -/
theorem transpose_diagSqrt (A : Matrix (Fin n) (Fin n) ℝ) : (diagSqrt A)ᵀ = diagSqrt A :=
  Matrix.diagonal_transpose _

/-- `D^{1/2} D^{1/2} = D`. -/
theorem diagSqrt_mul_diagSqrt (hA : A.PosDef) : diagSqrt A * diagSqrt A = diagPart A := by
  rw [diagSqrt, Matrix.diagonal_mul_diagonal]
  exact congrArg _ (funext fun i =>
    Real.mul_self_sqrt (Matrix.PosDef.diag_pos hA (i := i)).le)

/-- `D^{-1/2} D^{1/2} = I`. -/
theorem diagInvSqrt_mul_diagSqrt (hA : A.PosDef) : diagInvSqrt A * diagSqrt A = 1 := by
  rw [diagInvSqrt, diagSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i =>
    inv_mul_cancel₀ (Real.sqrt_pos.2 (Matrix.PosDef.diag_pos hA (i := i))).ne')

/-- `D^{1/2} D^{-1/2} = I`. -/
theorem diagSqrt_mul_diagInvSqrt (hA : A.PosDef) : diagSqrt A * diagInvSqrt A = 1 := by
  rw [diagInvSqrt, diagSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i =>
    mul_inv_cancel₀ (Real.sqrt_pos.2 (Matrix.PosDef.diag_pos hA (i := i))).ne')

/-- The symmetrically scaled matrix of a symmetric matrix is symmetric. -/
theorem isHermitian_diagScaled (hA : A.IsHermitian) : (diagScaled A).IsHermitian := by
  have hdiag : (diagInvSqrt A)ᴴ = diagInvSqrt A := by
    rw [diagInvSqrt, Matrix.diagonal_conjTranspose]
    exact congrArg _ (funext fun i => rfl)
  rw [Matrix.IsHermitian, diagScaled, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdiag,
    hA, Matrix.mul_assoc]

/-- **Saad Example 13.8**: `γ = ρ(D^{-1/2} A D^{-1/2})`, the largest eigenvalue of the
symmetrically scaled matrix — the spectral radius, the scaled matrix being symmetric positive
definite.  Saad also writes it `ρ(D⁻¹ A)`, the two matrices being similar. -/
noncomputable def gammaJacobi [NeZero n] (hA : A.PosDef) : ℝ :=
  lambdaMax (isHermitian_diagScaled (Matrix.PosDef.isHermitian hA))

/-- **Saad Example 13.8**: `γ` really is an eigenvalue of `D^{-1/2} A D^{-1/2}`, and by
`le_gammaJacobi` no eigenvalue exceeds it.  The scaled matrix being positive definite, its
eigenvalues are positive, so `γ` is its spectral radius — Saad's `ρ(D^{-1/2} A D^{-1/2})`. -/
theorem hasEigenvalue_gammaJacobi [NeZero n] (hA : A.PosDef) :
    Module.End.HasEigenvalue (toEuclideanLin (diagScaled A)) (gammaJacobi hA) := by
  have hH := isHermitian_diagScaled (Matrix.PosDef.isHermitian hA)
  have hval : ∃ i, hH.eigenvalues i = gammaJacobi hA := by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hH.eigenvalues
    exact ⟨i, hi.symm⟩
  obtain ⟨i, hi⟩ := hval
  exact (hH.hasEigenvalue_toEuclideanLin_iff _).2 ⟨i, by simpa using hi⟩

/-- **Saad Example 13.8**, the quadratic-form form of `γ`: `(A x, x) ≤ γ (D x, x)` for every `x`.
Substituting `v = D^{1/2} x` turns it into the Rayleigh bound
`(D^{-1/2} A D^{-1/2} v, v) ≤ γ (v, v)`. -/
theorem le_gammaJacobi [NeZero n] (hA : A.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ x) x ≤ gammaJacobi hA * inner ℝ (diagPart A ⬝ x) x := by
  have hbd := isSymmetricBoundedBy_toEuclideanLin
    (isHermitian_diagScaled (Matrix.PosDef.isHermitian hA))
  have h := hbd.re_inner_le (diagSqrt A ⬝ x)
  have hmat : diagSqrt A * (diagScaled A * diagSqrt A) = A := by
    calc diagSqrt A * (diagScaled A * diagSqrt A)
        = diagSqrt A * diagInvSqrt A * A * (diagInvSqrt A * diagSqrt A) := by
          rw [diagScaled]; noncomm_ring
      _ = A := by
          rw [diagSqrt_mul_diagInvSqrt hA, diagInvSqrt_mul_diagSqrt hA, Matrix.one_mul,
            Matrix.mul_one]
  have hinner : inner ℝ (diagScaled A ⬝ (diagSqrt A ⬝ x)) (diagSqrt A ⬝ x) = inner ℝ (A ⬝ x) x := by
    rw [← mul_act, inner_act_act, transpose_diagSqrt, hmat]
  have hnorm : ‖(diagSqrt A ⬝ x)‖ ^ 2 = inner ℝ (diagPart A ⬝ x) x := by
    rw [← real_inner_self_eq_norm_sq, inner_act_act, transpose_diagSqrt, diagSqrt_mul_diagSqrt hA]
  rw [RCLike.re_to_real, hinner, hnorm] at h
  exact h

/-- **Saad Example 13.8**: the weighted Jacobi smoother `S(ω) = I - ω D⁻¹ A` of a symmetric positive
definite matrix satisfies the smoothing property (13.62) with `α = ω(2 - ωγ)`, where
`γ = ρ(D^{-1/2} A D^{-1/2})`.  The constant is positive exactly on the classical range
`0 < ω < 2/γ` (`example_13_8_pos`), but the inequality itself holds for every `ω`. -/
theorem example_13_8 [NeZero n] (hA : A.PosDef) (ω : ℝ) :
    equation_13_62 A (weightedJacobiSmoother A ω) (ω * (2 - ω * gammaJacobi hA)) :=
  example_13_8_of_le hA (le_gammaJacobi hA) ω

/-- **Saad Example 13.8**: the constant `α = ω(2 - ωγ)` is positive exactly on Saad's range
`0 < ω < 2/ρ(D⁻¹ A)`, which is also the range on which weighted Jacobi converges. -/
theorem example_13_8_pos {γ ω : ℝ} (hγ : 0 < γ) (hω : 0 < ω) (hω2 : ω < 2 / γ) :
    0 < ω * (2 - ω * γ) := by
  have h : ω * γ < 2 := by
    rw [lt_div_iff₀ hγ] at hω2
    linarith
  exact mul_pos hω (by linarith)

end Example138

end SaadSparse.Chapter13
