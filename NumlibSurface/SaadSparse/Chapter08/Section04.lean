import Mathlib.Analysis.Matrix.PosDef
import Numlib.LinearSolve.Projection.OneDimensional
import Numlib.LinearSolve.Projection.Optimality
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad §8.4: saddle-point problems

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §8.4, with P-8.7.

The block system (8.30) is `saddleMatrix A B D`, `[[A, B], [Bᴴ, D]]`, with `D = 0` the
saddle-point matrix itself and `D = ρ C` the regularization of Example 8.2;
`saddleMatrix_mulVec_iff` reads a block equation off as the pair `A x + B y = b`,
`Bᴴ x + D y = c`.

Three things carry the section.

* `equation_8_30` is the Karush–Kuhn–Tucker statement: for symmetric positive definite `A`, an
  admissible `x` admits a multiplier `y` with `A x + B y = b` exactly when it minimizes
  `f(z) = ½(A z, z) - (z, b)` over `{z | Bᴴ z = c}`. Both directions are the Galerkin
  characterization of the minimizer over the affine space `x + Ker Bᴴ`, whose orthogonal
  complement is `Ran B` — which is where the multiplier comes from.
* `schur_posDef`: the Schur complement `S = Bᴴ A⁻¹ B` is symmetric positive definite when `A` is
  and `B` has full column rank.
* `equation_8_32`: eliminating `x` from **Algorithm 8.6** (`uzawa`) leaves exactly the Richardson
  iteration `y_{k+1} = y_k + ω (g - S y_k)` for `S y = g`, `g = Bᴴ A⁻¹ b - c`. `corollary_8_1` is
  then Example 4.1 applied to `S`: convergence for every right-hand side and every start exactly
  when `0 < ω < 2/λ_max(S)`, with optimum `2/(λ_min + λ_max)`.

`equation_8_32_isMinRes` is Saad's reason why the Stokes preconditioners work: for `c = 0` the
reduced system is the system of normal equations of the least-squares problem
`min_y ‖b - B y‖_{A⁻¹}`. `arrowHurwicz` is **Algorithm 8.7** and `arrowHurwicz_eq_block` its
block form; `example_8_2` is the regularized Schur complement `Bᴴ (ρ - A⁻¹) B`.

`lagrangian_isSaddle` is the sentence that names the section: the solution of (8.30) is the saddle
point of `L(x, y) = ½(A x, x) - (x, b) + (y, Bᴴ x - c)`. `constraintProjector` is the projector
`P = I - B (Bᴴ B)⁻¹ Bᴴ` of **P-8.6**, `problem_8_6_projector` identifies it with the orthogonal
projector onto `Ker Bᴴ`, and `equation_8_35` is P-8.6 (b), the reduction of (8.30) with `c = 0` to
the singular consistent system `P A P x = P b`.

`problem_8_5b` is **P-8.5 (b)**: any solver for the reduced system (8.32) is a solver for (8.30),
since `x = A⁻¹ (b - B y)` completes a solution `y` of the reduced system to one of the block
system — for `c = 0` and for `c ≠ 0` alike.

**P-8.12** is the indefinite saddle-point exercise. `problem_8_12_pos` and `problem_8_12_neg` are
the two choices of `x` part 1 asks for, and `problem_8_12_indefinite` turns them into eigenvalues
of both signs; `problem_8_12_residual` is the initial guess of part 2, after which
`problem_8_12_steepestDescent_stalls` and `problem_8_12_minRes_stalls` are parts 2 and 3 — both
iterations return their starting point, because `(A r_0, r_0) = 0` for a residual of the shape
`(0, s_0)` (`inner_saddleMatrix_blockVec_zero`), and that quantity is the steepest-descent
*denominator* and the minimal-residual *numerator*. `problem_8_12_reduced` is part 5.

Not formalized: **P-8.6 (d)**, which needs a `QR` factorization of a rectangular `B`; the rest of
**P-8.6 (c)** — running CG on `P A P x = P b` needs a theorem about the conjugate gradient method
on a symmetric positive *semi*definite consistent system, which the backbone does not have
(`Numlib/Krylov/Singular.lean` carries the minimal-residual story only), although the question
"in which subspace are the iterates generated?" is answered by `problem_8_6_cg_subspace`; and
**P-8.9** (inexact Uzawa), which needs a perturbed-fixed-point theorem; both are recorded in
`plans/NumlibSurface/SaadSparse/Chapter08/Section04.toml`.
-/

open Matrix Filter Topology

open scoped Matrix SaadSparse ComplexOrder

namespace SaadSparse.Chapter08

variable {n m : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Moving `B` across the inner product -/

/-- `(B u, w) = (u, Bᴴ w)`, the companion of `SaadSparse.Chapter08.inner_conjTranspose` with the
rectangular matrix on the left. -/
theorem inner_mul_conjTranspose (B : Matrix (Fin n) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin m))
    (w : EuclideanSpace 𝕜 (Fin n)) : inner 𝕜 (B ⬝ u) w = inner 𝕜 u (Bᴴ ⬝ w) := by
  have h := inner_conjTranspose Bᴴ u w
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- `(Ran B)ᗮ = Ker Bᴴ`: the constraint space of (8.29) is the orthogonal complement of the
range of `B`. -/
theorem orthogonal_range_eq_ker (B : Matrix (Fin n) (Fin m) 𝕜) :
    (LinearMap.range (Matrix.toEuclideanLin B))ᗮ = LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
  ext z
  simp only [LinearMap.mem_ker]
  constructor
  · intro hz
    have h : ∀ w, inner 𝕜 (Bᴴ ⬝ z) w = (0 : 𝕜) := by
      intro w
      rw [inner_conjTranspose]
      exact inner_eq_zero_symm.1 (hz _ ⟨w, rfl⟩)
    exact inner_self_eq_zero.1 (h (Bᴴ ⬝ z))
  · rintro hz _ ⟨w, rfl⟩
    rw [show (Matrix.toEuclideanLin B) w = (B ⬝ w) from rfl, inner_mul_conjTranspose, hz,
      inner_zero_right]

/-- `(Ker Bᴴ)ᗮ = Ran B`, the form (8.30) needs: a vector orthogonal to every admissible
direction is `B y` for some `y`, and that `y` is the Lagrange multiplier. -/
theorem orthogonal_ker_eq_range (B : Matrix (Fin n) (Fin m) 𝕜) :
    (LinearMap.ker (Matrix.toEuclideanLin Bᴴ))ᗮ = LinearMap.range (Matrix.toEuclideanLin B) := by
  rw [← orthogonal_range_eq_ker, Submodule.orthogonal_orthogonal]

/-- `A A⁻¹ z = z` for a nonsingular `A`. -/
theorem apply_nonsing_inv {A : Matrix (Fin n) (Fin n) 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 (Fin n)) : (A ⬝ (A⁻¹ ⬝ z)) = z := by
  rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).1 hA),
    Matrix.toEuclideanLin_one]
  rfl

/-! ### (8.30): the block system -/

/-- **Saad (8.30)** and **Example 8.2**: the saddle-point block matrix `[[A, B], [Bᴴ, D]]`.
The block system of §8.4 is `D = 0`; the regularized system of Example 8.2 is `D = ρ C`. -/
def saddleMatrix (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (D : Matrix (Fin m) (Fin m) 𝕜) : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) 𝕜 :=
  Matrix.fromBlocks A B Bᴴ D

private theorem toEuclideanLin_zero_apply {k l : ℕ} (v : EuclideanSpace 𝕜 (Fin l)) :
    ((0 : Matrix (Fin k) (Fin l) 𝕜) ⬝ v) = 0 := by
  rw [map_zero]; rfl

private theorem toEuclideanLin_one_apply {k : ℕ} (v : EuclideanSpace 𝕜 (Fin k)) :
    ((1 : Matrix (Fin k) (Fin k) 𝕜) ⬝ v) = v := by
  rw [Matrix.toEuclideanLin_one]; rfl

private theorem toEuclideanLin_neg_apply {k l : ℕ} (M : Matrix (Fin k) (Fin l) 𝕜)
    (v : EuclideanSpace 𝕜 (Fin l)) : ((-M) ⬝ v) = -(M ⬝ v) := by
  rw [map_neg]; rfl

private theorem toEuclideanLin_sub_apply {k l : ℕ} (M N : Matrix (Fin k) (Fin l) 𝕜)
    (v : EuclideanSpace 𝕜 (Fin l)) : ((M - N) ⬝ v) = (M ⬝ v) - (N ⬝ v) := by
  rw [map_sub]; rfl

private theorem toEuclideanLin_smul_apply {k l : ℕ} (r : 𝕜) (M : Matrix (Fin k) (Fin l) 𝕜)
    (v : EuclideanSpace 𝕜 (Fin l)) : ((r • M) ⬝ v) = r • (M ⬝ v) := by
  rw [map_smul]; rfl

private theorem ofLp_eq_add_iff {k : ℕ} (x y z : EuclideanSpace 𝕜 (Fin k)) :
    WithLp.ofLp x = WithLp.ofLp y + WithLp.ofLp z ↔ x = y + z := by
  rw [← WithLp.ofLp_add]
  exact (WithLp.ofLp_injective 2).eq_iff

private theorem fromBlocks_mulVec_elim (M₁ : Matrix (Fin n) (Fin n) 𝕜)
    (M₂ : Matrix (Fin n) (Fin m) 𝕜) (M₃ : Matrix (Fin m) (Fin n) 𝕜)
    (M₄ : Matrix (Fin m) (Fin m) 𝕜) (u : EuclideanSpace 𝕜 (Fin n))
    (v : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks M₁ M₂ M₃ M₄ *ᵥ Sum.elim (WithLp.ofLp u) (WithLp.ofLp v)
      = Sum.elim (WithLp.ofLp ((M₁ ⬝ u) + (M₂ ⬝ v))) (WithLp.ofLp ((M₃ ⬝ u) + (M₄ ⬝ v))) := by
  rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, WithLp.ofLp_add,
    WithLp.ofLp_add]
  rfl

/-- **Saad (8.30)** written out: `(x, y)` solves the block system exactly when
`A x + B y = b` and `Bᴴ x + D y = c`. -/
theorem saddleMatrix_mulVec_iff (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (D : Matrix (Fin m) (Fin m) 𝕜) (x b : EuclideanSpace 𝕜 (Fin n))
    (y c : EuclideanSpace 𝕜 (Fin m)) :
    saddleMatrix A B D *ᵥ Sum.elim (WithLp.ofLp x) (WithLp.ofLp y)
        = Sum.elim (WithLp.ofLp b) (WithLp.ofLp c) ↔
      ((A ⬝ x) + (B ⬝ y) = b ∧ (Bᴴ ⬝ x) + (D ⬝ y) = c) := by
  rw [saddleMatrix, fromBlocks_mulVec_elim, Sum.elim_eq_iff]
  exact and_congr (WithLp.ofLp_injective 2).eq_iff (WithLp.ofLp_injective 2).eq_iff

/-- A block identity `M z' = N z + p` read off as its two rows. -/
private theorem fromBlocks_elim_eq_iff
    (M₁ N₁ : Matrix (Fin n) (Fin n) 𝕜) (M₂ N₂ : Matrix (Fin n) (Fin m) 𝕜)
    (M₃ N₃ : Matrix (Fin m) (Fin n) 𝕜) (M₄ N₄ : Matrix (Fin m) (Fin m) 𝕜)
    (u u' p : EuclideanSpace 𝕜 (Fin n)) (v v' q : EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks M₁ M₂ M₃ M₄ *ᵥ Sum.elim (WithLp.ofLp u') (WithLp.ofLp v')
        = Matrix.fromBlocks N₁ N₂ N₃ N₄ *ᵥ Sum.elim (WithLp.ofLp u) (WithLp.ofLp v)
          + Sum.elim (WithLp.ofLp p) (WithLp.ofLp q) ↔
      ((M₁ ⬝ u') + (M₂ ⬝ v') = (N₁ ⬝ u) + (N₂ ⬝ v) + p ∧
        (M₃ ⬝ u') + (M₄ ⬝ v') = (N₃ ⬝ u) + (N₄ ⬝ v) + q) := by
  rw [fromBlocks_mulVec_elim, fromBlocks_mulVec_elim, ← Sum.elim_add_add, Sum.elim_eq_iff]
  exact and_congr (ofLp_eq_add_iff _ _ _) (ofLp_eq_add_iff _ _ _)

/-! ### (8.28)–(8.30): the constrained minimization problem -/

/-- **Saad (8.28)**: the quadratic objective `f(z) = ½ (A z, z) - (z, b)` that the saddle-point
system minimizes under the constraint `Bᴴ z = c`. -/
noncomputable def saddleObjective (A : Matrix (Fin n) (Fin n) 𝕜)
    (b z : EuclideanSpace 𝕜 (Fin n)) : ℝ :=
  RCLike.re (inner 𝕜 (A ⬝ z) z) / 2 - RCLike.re (inner 𝕜 b z)

section Objective

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b : EuclideanSpace 𝕜 (Fin n)}

/-- Up to an additive constant, `f` is half the squared energy norm of the error. This is what
makes the constrained minimization of (8.28) a Galerkin problem. -/
private theorem saddleObjective_eq (hA : A.PosDef) {xstar : EuclideanSpace 𝕜 (Fin n)}
    (hstar : (A ⬝ xstar) = b) (z : EuclideanSpace 𝕜 (Fin n)) :
    saddleObjective A b z = energyNorm (Matrix.toEuclideanLin A) (xstar - z) ^ 2 / 2
      - RCLike.re (inner 𝕜 b xstar) / 2 := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hsym : inner 𝕜 (A ⬝ z) xstar = inner 𝕜 z b := by
    rw [show inner 𝕜 (A ⬝ z) xstar = inner 𝕜 ((Matrix.toEuclideanLin A) z) xstar from rfl,
      hsc.isSymmetric z xstar, hstar]
  have hre : RCLike.re (inner 𝕜 z b) = RCLike.re (inner 𝕜 b z) := by
    rw [← inner_conj_symm]
    exact RCLike.conj_re _
  rw [hsc.energyNorm_sq, saddleObjective,
    show (Matrix.toEuclideanLin A) (xstar - z) = (A ⬝ xstar) - (A ⬝ z) from map_sub _ _ _,
    hstar, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
  simp only [map_sub]
  rw [hre]
  ring

/-- The Galerkin characterization of the minimizer of `f` over an affine subspace: for symmetric
positive definite `A` the two conditions are the same. This is `IsGalerkin.iff_energyNorm_min`
read through `saddleObjective_eq`. -/
theorem isGalerkin_iff_saddleObjective_min (hA : A.PosDef)
    {K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} [FiniteDimensional 𝕜 K]
    (x₀ x : EuclideanSpace 𝕜 (Fin n)) :
    IsGalerkin (Matrix.toEuclideanLin A) b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ z, z - x₀ ∈ K → saddleObjective A b x ≤ saddleObjective A b z := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  have hstar : (A ⬝ (A⁻¹ ⬝ b)) = b := apply_nonsing_inv hA.isUnit b
  have hx0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - x)
  rw [IsGalerkin.iff_energyNorm_min hsc hstar]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h z hz
    have hz' := h z hz
    have hz0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - z)
    rw [saddleObjective_eq hA hstar, saddleObjective_eq hA hstar]
    nlinarith
  · intro h z hz
    have hz' := h z hz
    have hz0 := energyNorm_nonneg (Matrix.toEuclideanLin A) ((A⁻¹ ⬝ b) - z)
    rw [saddleObjective_eq hA hstar, saddleObjective_eq hA hstar] at hz'
    nlinarith

end Objective

/-- **Saad (8.28)–(8.30)**: the Karush–Kuhn–Tucker statement. For symmetric positive definite
`A`, an admissible `x` carries a Lagrange multiplier `y` — that is, `(x, y)` solves the block
system (8.30) — exactly when `x` minimizes `f(z) = ½(A z, z) - (z, b)` over the admissible set
`{z | Bᴴ z = c}`. The multiplier is unique as soon as `B` has full column rank
(`equation_8_30_unique`). -/
theorem equation_8_30 {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef)
    (B : Matrix (Fin n) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))
    (c : EuclideanSpace 𝕜 (Fin m)) (x : EuclideanSpace 𝕜 (Fin n)) (hx : (Bᴴ ⬝ x) = c) :
    (∃ y, (A ⬝ x) + (B ⬝ y) = b) ↔
      ∀ z, (Bᴴ ⬝ z) = c → saddleObjective A b x ≤ saddleObjective A b z := by
  have hmem : ∀ z : EuclideanSpace 𝕜 (Fin n),
      z - x ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) ↔ (Bᴴ ⬝ z) = c := by
    intro z
    rw [LinearMap.mem_ker,
      show (Matrix.toEuclideanLin Bᴴ) (z - x) = (Bᴴ ⬝ z) - (Bᴴ ⬝ x) from map_sub _ _ _, hx,
      sub_eq_zero]
  have hgal : IsGalerkin (Matrix.toEuclideanLin A) b x
      (LinearMap.ker (Matrix.toEuclideanLin Bᴴ)) x ↔ ∃ y, (A ⬝ x) + (B ⬝ y) = b := by
    constructor
    · intro h
      have h2 := h.orth
      rw [orthogonal_ker_eq_range B] at h2
      obtain ⟨y, hy⟩ := h2
      refine ⟨y, ?_⟩
      rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl] at hy
      rw [hy]
      abel
    · rintro ⟨y, hy⟩
      refine ⟨by rw [sub_self]; exact Submodule.zero_mem _, ?_⟩
      rw [orthogonal_ker_eq_range B]
      exact ⟨y, by rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl, ← hy]; abel⟩
  rw [← hgal, isGalerkin_iff_saddleObjective_min hA x x]
  simp only [hmem]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- **Saad (8.30)**: the Lagrange multiplier is unique when `B` has full column rank. -/
theorem equation_8_30_unique {B : Matrix (Fin n) (Fin m) 𝕜}
    (hB : Function.Injective (Matrix.toEuclideanLin B)) {A : Matrix (Fin n) (Fin n) 𝕜}
    {b x : EuclideanSpace 𝕜 (Fin n)} {y y' : EuclideanSpace 𝕜 (Fin m)}
    (hy : (A ⬝ x) + (B ⬝ y) = b) (hy' : (A ⬝ x) + (B ⬝ y') = b) : y = y' :=
  hB (by rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl,
    show (Matrix.toEuclideanLin B) y' = (B ⬝ y') from rfl, ← add_right_inj (A ⬝ x), hy, hy'])

/-! ### (8.31)–(8.32): the Schur complement -/

/-- **Saad (8.32)** and **Corollary 8.1**: the Schur complement `S = Bᴴ A⁻¹ B` of the block
system (8.30), the coefficient matrix of the system that eliminating `x` leaves. -/
noncomputable def schur (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Bᴴ * A⁻¹ * B

/-- **Saad (8.32)**: the reduced right-hand side `g = Bᴴ A⁻¹ b - c`. -/
noncomputable def schurRhs (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin m) :=
  ((Bᴴ * A⁻¹) ⬝ b) - c

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- The Schur complement acts as `Bᴴ ∘ A⁻¹ ∘ B`. -/
theorem schur_apply (y : EuclideanSpace 𝕜 (Fin m)) :
    (schur A B ⬝ y) = (Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ y))) := by
  rw [schur, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]

private theorem conjTranspose_inv_sub (b : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) = ((Bᴴ * A⁻¹) ⬝ b) - (schur A B ⬝ y) := by
  rw [schur_apply, toEuclideanLin_mul_apply,
    show (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)) = (A⁻¹ ⬝ b) - (A⁻¹ ⬝ (B ⬝ y)) from
      map_sub _ _ _,
    show (Matrix.toEuclideanLin Bᴴ) ((A⁻¹ ⬝ b) - (A⁻¹ ⬝ (B ⬝ y)))
      = (Bᴴ ⬝ (A⁻¹ ⬝ b)) - (Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ y))) from map_sub _ _ _]

/-- **Saad (8.31)–(8.32)**: with `x = A⁻¹ (b - B y)` the first block equation holds
automatically, and the second one is exactly the reduced system `S y = g`. -/
theorem schur_eq (hA : IsUnit A) (b : EuclideanSpace 𝕜 (Fin n)) (c y : EuclideanSpace 𝕜 (Fin m))
    {x : EuclideanSpace 𝕜 (Fin n)} (hx : x = (A⁻¹ ⬝ (b - (B ⬝ y)))) :
    (schur A B ⬝ y) = schurRhs A B b c ↔ ((A ⬝ x) + (B ⬝ y) = b ∧ (Bᴴ ⬝ x) = c) := by
  have h1 : (A ⬝ x) + (B ⬝ y) = b := by
    rw [hx, apply_nonsing_inv hA]
    abel
  have h2 : (Bᴴ ⬝ x) = ((Bᴴ * A⁻¹) ⬝ b) - (schur A B ⬝ y) := by
    rw [hx, conjTranspose_inv_sub]
  rw [schurRhs]
  refine ⟨fun h => ⟨h1, ?_⟩, fun h => ?_⟩
  · rw [h2, h]
    abel
  · have h3 := h.2
    rw [h2] at h3
    rw [← h3]
    abel

/-- **Saad, Corollary 8.1**, first half: the Schur complement `S = Bᴴ A⁻¹ B` is symmetric
positive definite whenever `A` is and `B` has full column rank. -/
theorem schur_posDef (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    (schur A B).PosDef := by
  have hAinv := (Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  refine ⟨fun u v => ?_, (LinearMap.isCoercive_iff_forall_pos _).2 fun y hy => ?_⟩
  · rw [show (Matrix.toEuclideanLin (schur A B)) u = (schur A B ⬝ u) from rfl,
      show (Matrix.toEuclideanLin (schur A B)) v = (schur A B ⬝ v) from rfl, schur_apply,
      schur_apply, inner_conjTranspose B (A⁻¹ ⬝ (B ⬝ u)) v,
      ← inner_mul_conjTranspose B u (A⁻¹ ⬝ (B ⬝ v))]
    exact hAinv.isSymmetric (B ⬝ u) (B ⬝ v)
  · have hBy : (B ⬝ y) ≠ 0 := fun h => hy (hB (by
      rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl, h, map_zero]))
    rw [show (Matrix.toEuclideanLin (schur A B)) y = (schur A B ⬝ y) from rfl, schur_apply,
      inner_conjTranspose B (A⁻¹ ⬝ (B ⬝ y)) y]
    exact hAinv.isCoercive.inner_self_pos hBy

/-- **Saad §8.4**, the reason the Stokes preconditioners of the section work: for `c = 0` the
reduced system `S y = Bᴴ A⁻¹ b` is the system of normal equations of the least-squares problem
`min ‖b - B y‖_{A⁻¹}` in the `A⁻¹` inner product. -/
theorem equation_8_32_isMinRes (hA : A.PosDef) (b : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    (schur A B ⬝ y) = ((Bᴴ * A⁻¹) ⬝ b) ↔
      ∀ z ∈ LinearMap.range (Matrix.toEuclideanLin B),
        energyNorm (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y))
          ≤ energyNorm (Matrix.toEuclideanLin A⁻¹) (b - z) := by
  have hAinv := (Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv
  have hmem : (B ⬝ y) ∈ LinearMap.range (Matrix.toEuclideanLin B) :=
    LinearMap.mem_range_self (Matrix.toEuclideanLin B) y
  have hres : (A⁻¹ ⬝ b) - (Matrix.toEuclideanLin A⁻¹) (B ⬝ y)
      = (Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)) := (map_sub _ _ _).symm
  have hgal : IsGalerkin (Matrix.toEuclideanLin A⁻¹) (A⁻¹ ⬝ b) 0
      (LinearMap.range (Matrix.toEuclideanLin B)) (B ⬝ y)
      ↔ (schur A B ⬝ y) = ((Bᴴ * A⁻¹) ⬝ b) := by
    constructor
    · intro h
      have h2 := h.orth
      rw [hres, orthogonal_range_eq_ker, LinearMap.mem_ker,
        show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)))
          = (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) from rfl, conjTranspose_inv_sub, sub_eq_zero] at h2
      exact h2.symm
    · intro h
      refine ⟨by rw [sub_zero]; exact hmem, ?_⟩
      rw [hres, orthogonal_range_eq_ker, LinearMap.mem_ker,
        show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin A⁻¹) (b - (B ⬝ y)))
          = (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ y)))) from rfl, conjTranspose_inv_sub, h, sub_self]
  rw [← hgal, IsGalerkin.iff_energyNorm_min hAinv (rfl : (A⁻¹ ⬝ b) = (A⁻¹ ⬝ b))]
  simp only [sub_zero]
  exact ⟨fun h z hz => h.2 z hz, fun h => ⟨hmem, fun z hz => h z hz⟩⟩

/-! ### Algorithm 8.6: Uzawa's method -/

section Uzawa

variable (A B) (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) (ω : 𝕜)

/-- One pass through **Algorithm 8.6** (Uzawa): `x_{k+1} = A⁻¹ (b - B y_k)` and
`y_{k+1} = y_k + ω (Bᴴ x_{k+1} - c)`. -/
noncomputable def uzawaStep (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (A⁻¹ ⬝ (b - (B ⬝ s.2)), s.2 + ω • ((Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ s.2)))) - c))

/-- **Algorithm 8.6** (Uzawa) run for `k` steps from the pair `(x_0, y_0)`. -/
noncomputable def uzawa (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (uzawaStep A B b c ω)^[k] s₀

/-- The recurrence: state `k + 1` is one pass of Algorithm 8.6 applied to state `k`. -/
theorem uzawa_succ (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    uzawa A B b c ω s₀ (k + 1) = uzawaStep A B b c ω (uzawa A B b c ω s₀ k) :=
  Function.iterate_succ_apply' _ _ _

variable {A B b c ω}

/-- **Saad (8.31)–(8.32)**: eliminating `x` from Algorithm 8.6 leaves the Richardson iteration
`y_{k+1} = y_k + ω (g - S y_k)` for the reduced system `S y = g`. -/
theorem equation_8_32 (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    (uzawaStep A B b c ω s).2 = s.2 + ω • (schurRhs A B b c - (schur A B ⬝ s.2)) := by
  have h : (Bᴴ ⬝ (A⁻¹ ⬝ (b - (B ⬝ s.2)))) - c = schurRhs A B b c - (schur A B ⬝ s.2) := by
    rw [conjTranspose_inv_sub, schurRhs]
    abel
  rw [uzawaStep, h]

/-- **P-8.7**: Uzawa's method is the fixed-point iteration of the splitting
`M = [[A, 0], [-ω Bᴴ, 1]]`, `N = [[0, -B], [0, 1]]` of the saddle-point matrix. -/
theorem uzawa_eq_splitting (hA : IsUnit A)
    (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks A 0 (-(ω • Bᴴ)) 1
        *ᵥ Sum.elim (WithLp.ofLp (uzawaStep A B b c ω s).1)
          (WithLp.ofLp (uzawaStep A B b c ω s).2)
      = Matrix.fromBlocks 0 (-B) 0 1 *ᵥ Sum.elim (WithLp.ofLp s.1) (WithLp.ofLp s.2)
          + Sum.elim (WithLp.ofLp b) (WithLp.ofLp (-(ω • c))) := by
  have hx : (A ⬝ (uzawaStep A B b c ω s).1) = b - (B ⬝ s.2) := apply_nonsing_inv hA _
  have hy : (uzawaStep A B b c ω s).2
      = s.2 + ω • ((Bᴴ ⬝ (uzawaStep A B b c ω s).1) - c) := rfl
  rw [fromBlocks_elim_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_neg_apply]
    rw [hx]
    abel
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_neg_apply,
      toEuclideanLin_smul_apply]
    rw [hy, smul_sub]
    abel

end Uzawa

/-! ### Algorithm 8.7: the Arrow–Hurwicz method -/

section ArrowHurwicz

variable (A B) (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m)) (ε ω : 𝕜)

/-- One pass through **Algorithm 8.7** (Arrow–Hurwicz):
`x_{k+1} = x_k + ε (b - A x_k - B y_k)` and `y_{k+1} = y_k + ω (Bᴴ x_{k+1} - c)`, one gradient
step in place of the exact solve of Uzawa. -/
noncomputable def arrowHurwiczStep (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)),
    s.2 + ω • ((Bᴴ ⬝ (s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)))) - c))

/-- **Algorithm 8.7** (Arrow–Hurwicz) run for `k` steps from the pair `(x_0, y_0)`. -/
noncomputable def arrowHurwicz
    (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (arrowHurwiczStep A B b c ε ω)^[k] s₀

/-- The recurrence: state `k + 1` is one pass of Algorithm 8.7 applied to state `k`. -/
theorem arrowHurwicz_succ (s₀ : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) (k : ℕ) :
    arrowHurwicz A B b c ε ω s₀ (k + 1)
      = arrowHurwiczStep A B b c ε ω (arrowHurwicz A B b c ε ω s₀ k) :=
  Function.iterate_succ_apply' _ _ _

variable {A B b c ε ω}

/-- **Saad §8.4**: the block form of Algorithm 8.7,
`[[1, 0], [-ω Bᴴ, 1]] (x_{k+1}, y_{k+1}) = [[1 - εA, -εB], [0, 1]] (x_k, y_k) + (ε b, -ω c)`,
which exhibits the Arrow–Hurwicz method as a stationary iteration. -/
theorem arrowHurwicz_eq_block (s : EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) :
    Matrix.fromBlocks 1 0 (-(ω • Bᴴ)) 1
        *ᵥ Sum.elim (WithLp.ofLp (arrowHurwiczStep A B b c ε ω s).1)
          (WithLp.ofLp (arrowHurwiczStep A B b c ε ω s).2)
      = Matrix.fromBlocks (1 - ε • A) (-(ε • B)) 0 1
            *ᵥ Sum.elim (WithLp.ofLp s.1) (WithLp.ofLp s.2)
          + Sum.elim (WithLp.ofLp (ε • b)) (WithLp.ofLp (-(ω • c))) := by
  have hy : (arrowHurwiczStep A B b c ε ω s).2
      = s.2 + ω • ((Bᴴ ⬝ (arrowHurwiczStep A B b c ε ω s).1) - c) := rfl
  have hx : (arrowHurwiczStep A B b c ε ω s).1
      = s.1 + ε • (b - (A ⬝ s.1) - (B ⬝ s.2)) := rfl
  rw [fromBlocks_elim_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_sub_apply,
      toEuclideanLin_neg_apply, toEuclideanLin_smul_apply]
    rw [hx, smul_sub, smul_sub]
    abel
  · simp only [toEuclideanLin_zero_apply, toEuclideanLin_one_apply, toEuclideanLin_neg_apply,
      toEuclideanLin_smul_apply]
    rw [hy, smul_sub]
    abel

end ArrowHurwicz

/-! ### Example 8.2: the regularized Schur complement -/

/-- **Example 8.2**: the Schur complement of the regularized system `[[A, B], [Bᴴ, ρ Bᴴ B]]`,
namely `ρ Bᴴ B - Bᴴ A⁻¹ B = Bᴴ (ρ - A⁻¹) B`. -/
noncomputable def regularizedSchur (A : Matrix (Fin n) (Fin n) 𝕜)
    (B : Matrix (Fin n) (Fin m) 𝕜) (ρ : 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  ρ • (Bᴴ * B) - schur A B

/-- **Example 8.2**: the regularized Schur complement is `Bᴴ (ρ - A⁻¹) B`. -/
theorem regularizedSchur_eq (ρ : 𝕜) :
    regularizedSchur A B ρ = Bᴴ * (ρ • 1 - A⁻¹) * B := by
  rw [regularizedSchur, schur, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]

/-- The regularized Schur complement acts as `Bᴴ ∘ (ρ - A⁻¹) ∘ B`. -/
theorem regularizedSchur_apply (ρ : 𝕜) (y : EuclideanSpace 𝕜 (Fin m)) :
    (regularizedSchur A B ρ ⬝ y) = (Bᴴ ⬝ (ρ • (B ⬝ y) - (A⁻¹ ⬝ (B ⬝ y)))) := by
  rw [regularizedSchur_eq, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  refine congrArg (fun z => (Bᴴ ⬝ z)) ?_
  rw [map_sub, map_smul, Matrix.toEuclideanLin_one]
  rfl

/-- **Example 8.2**: the quadratic form of the regularized Schur complement is that of
`ρ - A⁻¹` on the range of `B`. -/
theorem re_inner_regularizedSchur (ρ : ℝ) (y : EuclideanSpace 𝕜 (Fin m)) :
    RCLike.re (inner 𝕜 (regularizedSchur A B (ρ : 𝕜) ⬝ y) y)
      = ρ * ‖(B ⬝ y)‖ ^ 2 - RCLike.re (inner 𝕜 (A⁻¹ ⬝ (B ⬝ y)) (B ⬝ y)) := by
  rw [regularizedSchur_apply, inner_conjTranspose B _ y, inner_sub_left, inner_smul_left,
    inner_self_eq_norm_sq_to_K]
  simp only [map_sub]
  rw [RCLike.conj_ofReal]
  have h : RCLike.re ((ρ : 𝕜) * ((‖(B ⬝ y)‖ : 𝕜) ^ 2)) = ρ * ‖(B ⬝ y)‖ ^ 2 := by
    rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [h]

/-- **Example 8.2**: for the regularization `C = Bᴴ B`, the modified Schur complement
`S_ρ = Bᴴ (ρ - A⁻¹) B` is symmetric; it is positive definite when `ρ` exceeds every
quadratic-form value of `A⁻¹` — that is, when `ρ > 1/λ_min(A)` — and negative definite when `ρ`
falls below all of them, `ρ < 1/λ_max(A)`. The extremes of the quadratic form of `A⁻¹` are
`1/λ_max(A)` and `1/λ_min(A)`, which is how the book states the two thresholds. The inequalities
are strict: at `ρ = 1/λ_min(A)` the form `ρ - A⁻¹` is only positive *semi*definite. -/
theorem example_8_2 (hB : Function.Injective (Matrix.toEuclideanLin B)) {μmin μmax : ℝ}
    (hbd : (Matrix.toEuclideanLin A⁻¹).IsSymmetricBoundedBy μmin μmax) {ρ : ℝ} :
    (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))).IsSymmetric ∧
      (μmax < ρ → (regularizedSchur A B (ρ : 𝕜)).PosDef) ∧
      (ρ < μmin → ∀ y : EuclideanSpace 𝕜 (Fin m), y ≠ 0 →
        RCLike.re (inner 𝕜 (regularizedSchur A B (ρ : 𝕜) ⬝ y) y) < 0) := by
  have hnorm : ∀ y : EuclideanSpace 𝕜 (Fin m), y ≠ 0 → 0 < ‖(B ⬝ y)‖ ^ 2 := by
    intro y hy
    have hBy : (B ⬝ y) ≠ 0 := fun h => hy (hB (by
      rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl, h, map_zero]))
    have := norm_pos_iff.2 hBy
    positivity
  have hsymm : (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))).IsSymmetric := by
    intro u v
    rw [show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) u
        = (regularizedSchur A B (ρ : 𝕜) ⬝ u) from rfl,
      show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) v
        = (regularizedSchur A B (ρ : 𝕜) ⬝ v) from rfl,
      regularizedSchur_apply, regularizedSchur_apply,
      inner_conjTranspose B ((ρ : 𝕜) • (B ⬝ u) - (A⁻¹ ⬝ (B ⬝ u))) v,
      ← inner_mul_conjTranspose B u ((ρ : 𝕜) • (B ⬝ v) - (A⁻¹ ⬝ (B ⬝ v))),
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
      hbd.isSymmetric (B ⬝ u) (B ⬝ v)]
  refine ⟨hsymm, fun hρ => ?_, fun hρ y hy => ?_⟩
  · rw [Matrix.posDef_iff_isSymmetricCoercive]
    refine ⟨hsymm, (LinearMap.isCoercive_iff_forall_pos _).2 fun y hy => ?_⟩
    rw [show (Matrix.toEuclideanLin (regularizedSchur A B (ρ : 𝕜))) y
      = (regularizedSchur A B (ρ : 𝕜) ⬝ y) from rfl, re_inner_regularizedSchur]
    nlinarith [hbd.re_inner_le (B ⬝ y), hnorm y hy]
  · rw [re_inner_regularizedSchur]
    nlinarith [hbd.le_re_inner (B ⬝ y), hnorm y hy]

/-! ### Corollary 8.1 -/

section Corollary

variable {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
  {b : EuclideanSpace ℝ (Fin n)} {c : EuclideanSpace ℝ (Fin m)} {ω : ℝ}

/-- **Saad (8.32)**: the `y`-component of Uzawa's iteration *is* Richardson's iteration for the
reduced system `S y = g`, so its convergence is Example 4.1 applied to `S`. -/
theorem uzawa_snd_eq_richardson
    (s₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    WithLp.ofLp (uzawa A B b c ω s₀ k).2
      = (Chapter04.richardsonStep (schur A B) ω (WithLp.ofLp (schurRhs A B b c)))^[k]
          (WithLp.ofLp s₀.2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [uzawa_succ, equation_8_32, Function.iterate_succ_apply', ← ih, Chapter04.richardsonStep,
      WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub]
    rfl

/-- **Saad, Corollary 8.1**: for `A` symmetric positive definite and `B` of full column rank the
Schur complement `S` is symmetric positive definite; Uzawa's method converges — for every
right-hand side and every starting pair — exactly when `0 < ω < 2/λ_max(S)`, and the optimal
parameter is `ω_opt = 2/(λ_min(S) + λ_max(S))`. The last two clauses are Example 4.1 applied to
`S`, since `equation_8_32` and `uzawa_snd_eq_richardson` make the `y`-iteration Richardson's for
`S y = g`. -/
theorem corollary_8_1 (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {lmin lmax : ℝ} (hsub : spectrum ℝ (schur A B) ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (schur A B)) (hmax : lmax ∈ spectrum ℝ (schur A B))
    (hpos : 0 < lmin) (hω : ω ≠ 0) :
    (schur A B).PosDef ∧
      ((∀ g y₀ : Fin m → ℝ, ∃ y,
          Tendsto (fun k => (Chapter04.richardsonStep (schur A B) ω g)^[k] y₀) atTop (𝓝 y)) ↔
        0 < ω ∧ ω < 2 / lmax) ∧
      IsMinOn (fun ω : ℝ => Matrix.complexSpectralRadius (1 - ω • schur A B)) (Set.Ioi 0)
        (2 / (lmin + lmax)) :=
  ⟨schur_posDef hA hB,
    Chapter04.example_4_1_tendsto_iff (schur_posDef hA hB).isHermitian hsub hmin hmax hpos hω,
    (Chapter04.example_4_1_opt (schur_posDef hA hB).isHermitian hsub hmin hmax hpos).1⟩

end Corollary

/-! ### §8.4: the Lagrangian and the saddle point -/

section Lagrangian

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **Saad §8.4**: the Lagrangian `L(x, y) = ½ (A x, x) - (x, b) + (y, Bᴴ x - c)` of the
constrained problem (8.28)–(8.29), whose stationarity conditions are the block system (8.30). -/
noncomputable def lagrangian (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin n) (Fin m) 𝕜)
    (b : EuclideanSpace 𝕜 (Fin n)) (c : EuclideanSpace 𝕜 (Fin m))
    (x : EuclideanSpace 𝕜 (Fin n)) (y : EuclideanSpace 𝕜 (Fin m)) : ℝ :=
  saddleObjective A b x + RCLike.re (inner 𝕜 ((Bᴴ ⬝ x) - c) y)

/-- **Saad §8.4**: the sentence that names the section — the solution `(x_*, y_*)` of the block
system (8.30) is the *saddle point* of the Lagrangian:
`L(x_*, y) ≤ L(x_*, y_*) ≤ L(x, y_*)` for every `x` and every `y`.

The two halves are of different kinds. On the `y` side the Lagrangian is affine and `x_*` is
admissible, so `L(x_*, ·)` is *constant* and the inequality is an equality — the saddle point is
never strict in `y`. On the `x` side, `L(x, y_*) - L(x_*, y_*) = ½ (A (x - x_*), x - x_*)`, which
positive definiteness of `A` makes nonnegative. Note that the `x` inequality holds for *every*
`x`, admissible or not: that is what distinguishes the saddle-point statement from the constrained
minimization of `equation_8_30`. -/
theorem lagrangian_isSaddle (hA : A.PosDef) (b : EuclideanSpace 𝕜 (Fin n))
    (c : EuclideanSpace 𝕜 (Fin m)) {xstar : EuclideanSpace 𝕜 (Fin n)}
    {ystar : EuclideanSpace 𝕜 (Fin m)} (hx : (Bᴴ ⬝ xstar) = c)
    (hy : (A ⬝ xstar) + (B ⬝ ystar) = b) (x : EuclideanSpace 𝕜 (Fin n))
    (y : EuclideanSpace 𝕜 (Fin m)) :
    lagrangian A B b c xstar y ≤ lagrangian A B b c xstar ystar ∧
      lagrangian A B b c xstar ystar ≤ lagrangian A B b c x ystar := by
  have hsc := (Matrix.posDef_iff_isSymmetricCoercive A).1 hA
  -- the Lagrangian does not depend on `y` at the admissible point `x_*`
  have hconst : ∀ w : EuclideanSpace 𝕜 (Fin m),
      lagrangian A B b c xstar w = saddleObjective A b xstar := fun w => by
    rw [lagrangian, hx, sub_self, inner_zero_left, map_zero, add_zero]
  refine ⟨le_of_eq (by rw [hconst y, hconst ystar]), ?_⟩
  rw [hconst ystar, lagrangian]
  set e := x - xstar with he
  have hxe : x = xstar + e := by rw [he]; abel
  have hAsym : inner 𝕜 (A ⬝ e) xstar = inner 𝕜 e (A ⬝ xstar) := hsc.isSymmetric e xstar
  have hre : RCLike.re (inner 𝕜 e (A ⬝ xstar)) = RCLike.re (inner 𝕜 (A ⬝ xstar) e) := by
    rw [← inner_conj_symm]
    exact RCLike.conj_re _
  have hquad : RCLike.re (inner 𝕜 (A ⬝ x) x)
      = RCLike.re (inner 𝕜 (A ⬝ xstar) xstar) + 2 * RCLike.re (inner 𝕜 (A ⬝ xstar) e)
        + RCLike.re (inner 𝕜 (A ⬝ e) e) := by
    conv_lhs => rw [hxe]
    rw [show (A ⬝ (xstar + e)) = (A ⬝ xstar) + (A ⬝ e) from map_add _ _ _, inner_add_left,
      inner_add_right, inner_add_right, map_add, map_add, map_add, hAsym, hre]
    ring
  have hlin : RCLike.re (inner 𝕜 b x)
      = RCLike.re (inner 𝕜 b xstar) + RCLike.re (inner 𝕜 b e) := by
    conv_lhs => rw [hxe]
    rw [inner_add_right, map_add]
  have hBe : (Bᴴ ⬝ x) - c = (Bᴴ ⬝ e) := by rw [he, map_sub, hx]
  have hmult : (B ⬝ ystar) = b - (A ⬝ xstar) := by rw [← hy]; abel
  have hcon : RCLike.re (inner 𝕜 ((Bᴴ ⬝ x) - c) ystar)
      = RCLike.re (inner 𝕜 b e) - RCLike.re (inner 𝕜 (A ⬝ xstar) e) := by
    have hbe : RCLike.re (inner 𝕜 e b) = RCLike.re (inner 𝕜 b e) := by
      rw [← inner_conj_symm]
      exact RCLike.conj_re _
    rw [hBe, inner_conjTranspose B e ystar, hmult, inner_sub_right, map_sub, hbe, hre]
  have hnonneg : 0 ≤ RCLike.re (inner 𝕜 (A ⬝ e) e) := by
    rcases eq_or_ne e 0 with h0 | h0
    · rw [h0, show (A ⬝ (0 : EuclideanSpace 𝕜 (Fin n))) = 0 from map_zero _, inner_zero_left,
        map_zero]
    · exact le_of_lt (hsc.isCoercive.inner_self_pos h0)
  rw [saddleObjective, saddleObjective, hquad, hlin, hcon]
  linarith

end Lagrangian

/-! ### P-8.6: the projector onto the constraint space -/

section Projector

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **P-8.6**: the projector `P = I - B (Bᴴ B)⁻¹ Bᴴ` of the null-space method for the
saddle-point system. -/
noncomputable def constraintProjector (B : Matrix (Fin n) (Fin m) 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  1 - B * (Bᴴ * B)⁻¹ * Bᴴ

/-- `B` has full column rank as a matrix exactly when it does as an operator on Euclidean
space. -/
private theorem injective_mulVec (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    Function.Injective B.mulVec := fun u v huv =>
  (WithLp.toLp_injective 2) (hB (show (B ⬝ WithLp.toLp 2 u) = (B ⬝ WithLp.toLp 2 v) from
    congrArg (WithLp.toLp 2) huv))

/-- `Bᴴ B` is nonsingular when `B` has full column rank, which is what makes `P` well defined. -/
private theorem isUnit_conjTranspose_mul_self
    (hB : Function.Injective (Matrix.toEuclideanLin B)) : IsUnit (Bᴴ * B) :=
  (Matrix.PosDef.conjTranspose_mul_self B (injective_mulVec hB)).isUnit

/-- **P-8.6 (a)**: `P = I - B (Bᴴ B)⁻¹ Bᴴ` is the orthogonal projector onto the constraint space
`Ker Bᴴ = (Ran B)ᗮ`. Its range and kernel are read off in
`constraintProjector_apply_eq_self_iff` and `constraintProjector_apply_eq_zero_iff`. -/
theorem problem_8_6_projector (hB : Function.Injective (Matrix.toEuclideanLin B)) :
    (Matrix.toEuclideanLin (constraintProjector B) :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
      = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection :
        EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) := by
  have hu := isUnit_conjTranspose_mul_self hB
  refine LinearMap.ext fun u => ?_
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [LinearMap.mem_ker,
      show (Matrix.toEuclideanLin Bᴴ) ((Matrix.toEuclideanLin (constraintProjector B)) u)
        = ((Bᴴ * constraintProjector B) ⬝ u) from (toEuclideanLin_mul_apply _ _ _).symm,
      constraintProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.one_mul, sub_self, map_zero]
    rfl
  · rw [orthogonal_ker_eq_range B]
    refine ⟨(((Bᴴ * B)⁻¹ * Bᴴ) ⬝ u), ?_⟩
    rw [show (Matrix.toEuclideanLin B) (((Bᴴ * B)⁻¹ * Bᴴ) ⬝ u)
        = ((B * ((Bᴴ * B)⁻¹ * Bᴴ)) ⬝ u) from (toEuclideanLin_mul_apply _ _ _).symm,
      show (Matrix.toEuclideanLin (constraintProjector B)) u
        = (constraintProjector B ⬝ u) from rfl, constraintProjector, Matrix.mul_assoc]
    rw [show ((1 - B * ((Bᴴ * B)⁻¹ * Bᴴ)) ⬝ u)
      = (Matrix.toEuclideanLin (1 - B * ((Bᴴ * B)⁻¹ * Bᴴ))) u from rfl,
      show (Matrix.toEuclideanLin (1 - B * ((Bᴴ * B)⁻¹ * Bᴴ)) :
          EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n))
        = Matrix.toEuclideanLin 1 - Matrix.toEuclideanLin (B * ((Bᴴ * B)⁻¹ * Bᴴ)) from
        map_sub _ _ _]
    rw [LinearMap.sub_apply, Matrix.toEuclideanLin_one]
    simp

/-- **P-8.6 (a)**: `Ran P = Ker Bᴴ` — a vector is fixed by `P` exactly when it is admissible. -/
theorem constraintProjector_apply_eq_self_iff (hB : Function.Injective (Matrix.toEuclideanLin B))
    (u : EuclideanSpace 𝕜 (Fin n)) : (constraintProjector B ⬝ u) = u ↔ (Bᴴ ⬝ u) = 0 := by
  rw [show (constraintProjector B ⬝ u)
    = (Matrix.toEuclideanLin (constraintProjector B)) u from rfl]
  rw [show (Matrix.toEuclideanLin (constraintProjector B)) u
    = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection u) from
    congrFun (congrArg DFunLike.coe (problem_8_6_projector hB)) u]
  exact Submodule.starProjection_eq_self_iff.trans LinearMap.mem_ker

/-- **P-8.6 (a)**: `Ker P = Ran B` — `P` annihilates exactly the range of `B`, which is where the
Lagrange multiplier term lives. -/
theorem constraintProjector_apply_eq_zero_iff (hB : Function.Injective (Matrix.toEuclideanLin B))
    (u : EuclideanSpace 𝕜 (Fin n)) :
    (constraintProjector B ⬝ u) = 0 ↔ u ∈ LinearMap.range (Matrix.toEuclideanLin B) := by
  rw [show (constraintProjector B ⬝ u)
    = ((LinearMap.ker (Matrix.toEuclideanLin Bᴴ)).starProjection u) from
    congrFun (congrArg DFunLike.coe (problem_8_6_projector hB)) u, ← orthogonal_ker_eq_range B]
  constructor
  · intro h
    have hmem := Submodule.sub_starProjection_mem_orthogonal
      (K := LinearMap.ker (Matrix.toEuclideanLin Bᴴ)) u
    rwa [h, sub_zero] at hmem
  · intro h
    exact Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) (by rwa [sub_zero])

/-- **P-8.6 (b)** and **Saad (8.35)**: for `c = 0` and `B` of full column rank, an admissible `x`
solves the block system (8.30) — that is, carries a Lagrange multiplier — exactly when it solves
the singular but consistent system `P A P x = P b`.

Both directions are `constraintProjector_apply_eq_zero_iff`: `P` fixes the admissible `x`, so
(8.35) says `P (A x - b) = 0`, and the kernel of `P` is `Ran B`, which is precisely where the
multiplier term `-B y` lives. `P A P` is symmetric positive *semi*definite and singular whenever
`B ≠ 0`, so parts (c) and (d) of the problem — running CG on it — need the theory of a consistent
semidefinite system; see the module doc. -/
theorem equation_8_35 (hB : Function.Injective (Matrix.toEuclideanLin B))
    (b : EuclideanSpace 𝕜 (Fin n)) {x : EuclideanSpace 𝕜 (Fin n)} (hx : (Bᴴ ⬝ x) = 0) :
    (∃ y, (A ⬝ x) + (B ⬝ y) = b) ↔
      (constraintProjector B ⬝ (A ⬝ (constraintProjector B ⬝ x)))
        = (constraintProjector B ⬝ b) := by
  rw [(constraintProjector_apply_eq_self_iff hB x).2 hx]
  have hsub : ((constraintProjector B ⬝ (A ⬝ x)) = (constraintProjector B ⬝ b)) ↔
      (constraintProjector B ⬝ ((A ⬝ x) - b)) = 0 := by
    rw [map_sub, sub_eq_zero]
  rw [hsub, constraintProjector_apply_eq_zero_iff hB]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨-y, ?_⟩
    rw [show (Matrix.toEuclideanLin B) (-y) = -(B ⬝ y) from map_neg _ _, ← hy]
    abel
  · rintro ⟨y, hy⟩
    rw [show (Matrix.toEuclideanLin B) y = (B ⬝ y) from rfl] at hy
    refine ⟨-y, ?_⟩
    rw [show (B ⬝ (-y)) = -(B ⬝ y) from map_neg _ _, hy]
    abel

/-! ### P-8.6 (c), first half: the subspace the CG iterates live in -/

/-- `Bᴴ P = 0`: the projector of P-8.6 lands in the constraint space `Ker Bᴴ`. -/
theorem conjTranspose_mul_constraintProjector
    (hB : Function.Injective (Matrix.toEuclideanLin B)) : Bᴴ * constraintProjector B = 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_conjTranspose_mul_self (B := B) hB)
  rw [constraintProjector, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, sub_self]

/-- **P-8.6 (c)**, the half that needs no new theory: *in which subspace are the iterates
generated from CG applied to (8.35)?*  In the constraint space `Ker Bᴴ`.  From `x_0 = 0` the CG
iterates lie in the Krylov space `𝒦_m(P A P, P b)`, and every generator of that space is a value
of `P`, which `conjTranspose_mul_constraintProjector` annihilates.  That is what makes the
singular system harmless: the whole iteration takes place on `Ker Bᴴ`, where `P A P` is positive
definite. -/
theorem problem_8_6_cg_subspace (hB : Function.Injective (Matrix.toEuclideanLin B))
    (b : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    Krylov.subspace
        (Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B))
        (Matrix.toEuclideanLin (constraintProjector B) b) k
      ≤ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
  have hBP := conjTranspose_mul_constraintProjector (B := B) hB
  have hstep : ∀ w : EuclideanSpace 𝕜 (Fin n),
      Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B) w
        ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := fun w => by
    rw [LinearMap.mem_ker, show (Matrix.toEuclideanLin Bᴴ)
        ((Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B)) w)
      = ((Bᴴ * (constraintProjector B * A * constraintProjector B)) ⬝ w) from
        (toEuclideanLin_mul_apply _ _ _).symm,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBP, Matrix.zero_mul, Matrix.zero_mul]
    exact toEuclideanLin_zero_apply w
  have hv : Matrix.toEuclideanLin (constraintProjector B) b
      ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
    rw [LinearMap.mem_ker, show (Matrix.toEuclideanLin Bᴴ)
        ((Matrix.toEuclideanLin (constraintProjector B)) b)
      = ((Bᴴ * constraintProjector B) ⬝ b) from (toEuclideanLin_mul_apply _ _ _).symm, hBP]
    exact toEuclideanLin_zero_apply b
  have hpow : ∀ j : ℕ,
      ((Matrix.toEuclideanLin (constraintProjector B * A * constraintProjector B)) ^ j)
          (Matrix.toEuclideanLin (constraintProjector B) b)
        ∈ LinearMap.ker (Matrix.toEuclideanLin Bᴴ) := by
    intro j
    cases j with
    | zero => simpa using hv
    | succ j =>
      rw [pow_succ', Module.End.mul_apply]
      exact hstep _
  rw [Krylov.subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact hpow _

end Projector

/-! ### P-8.5 (b): a method for (8.30) through the reduced system -/

section Problem85b

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- **P-8.5 (b)**: *derive a method for solving the equivalent system (8.30)*.  Any solver for the
reduced system (8.32) is one: if `y` solves `S y = g` then `x = A⁻¹ (b - B y)` completes it to a
solution of the block system, for `c = 0` and for `c ≠ 0` alike.

For `c = 0` the reduced system is the system of normal equations of `min_y ‖b - B y‖_{A⁻¹}`
(`equation_8_32_isMinRes`), so the method P-8.5 (a) asks for is CGNR in the `A⁻¹` inner product;
forming `S y` costs one solve with `A`, which is what the problem's hint asks for.  Compared with
Uzawa's method (`uzawa`, `uzawa_snd_eq_richardson`), which is Richardson's iteration for the same
reduced system with a fixed `ω`, this replaces the fixed step length by the conjugate gradient
one at the same cost per step. -/
theorem problem_8_5b (hA : IsUnit A) (b : EuclideanSpace 𝕜 (Fin n))
    (c y : EuclideanSpace 𝕜 (Fin m)) (hy : (schur A B ⬝ y) = schurRhs A B b c) :
    saddleMatrix A B 0 *ᵥ Sum.elim (WithLp.ofLp (A⁻¹ ⬝ (b - (B ⬝ y)))) (WithLp.ofLp y)
      = Sum.elim (WithLp.ofLp b) (WithLp.ofLp c) := by
  obtain ⟨h1, h2⟩ := (schur_eq hA b c y rfl).1 hy
  rw [saddleMatrix_mulVec_iff]
  refine ⟨h1, ?_⟩
  rw [toEuclideanLin_zero_apply, add_zero]
  exact h2

end Problem85b

/-! ### P-8.12: the indefinite saddle-point matrix -/

section Problem812

variable {A : Matrix (Fin n) (Fin n) 𝕜} {B : Matrix (Fin n) (Fin m) 𝕜}

/-- A vector of `EuclideanSpace 𝕜 (Fin n ⊕ Fin m)` written in blocks: the shape `x = (u, p)` every
vector of P-8.12 has. -/
noncomputable def blockVec (u : EuclideanSpace 𝕜 (Fin n)) (v : EuclideanSpace 𝕜 (Fin m)) :
    EuclideanSpace 𝕜 (Fin n ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp u) (WithLp.ofLp v))

/-- The saddle-point matrix acts on a block vector blockwise. -/
theorem saddleMatrix_apply_blockVec (D : Matrix (Fin m) (Fin m) 𝕜)
    (u : EuclideanSpace 𝕜 (Fin n)) (v : EuclideanSpace 𝕜 (Fin m)) :
    (saddleMatrix A B D ⬝ blockVec u v) = blockVec ((A ⬝ u) + (B ⬝ v)) ((Bᴴ ⬝ u) + (D ⬝ v)) := by
  refine WithLp.ofLp_injective 2 ?_
  rw [show WithLp.ofLp (saddleMatrix A B D ⬝ blockVec u v)
      = saddleMatrix A B D *ᵥ WithLp.ofLp (blockVec u v) from rfl,
    blockVec, WithLp.ofLp_toLp, saddleMatrix, fromBlocks_mulVec_elim, blockVec, WithLp.ofLp_toLp]

/-- The inner product of two block vectors is the sum of the block inner products. -/
theorem inner_blockVec (u u' : EuclideanSpace 𝕜 (Fin n)) (v v' : EuclideanSpace 𝕜 (Fin m)) :
    inner 𝕜 (blockVec u v) (blockVec u' v') = inner 𝕜 u u' + inner 𝕜 v v' := by
  simp [blockVec, PiLp.inner_apply, Fintype.sum_sum_type]

/-- **P-8.12 (1)**, the positive direction: on a vector `x = (u, 0)` the quadratic form of the
saddle-point matrix is `(A u, u)`, positive for `u ≠ 0`. -/
theorem problem_8_12_pos (hA : A.PosDef) {u : EuclideanSpace 𝕜 (Fin n)} (hu : u ≠ 0) :
    0 < RCLike.re (inner 𝕜 (blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
      (saddleMatrix A B 0 ⬝ blockVec u 0)) := by
  rw [saddleMatrix_apply_blockVec, map_zero, add_zero, toEuclideanLin_zero_apply, add_zero,
    inner_blockVec, inner_zero_left, add_zero, ← inner_conj_symm, RCLike.conj_re]
  exact ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA).isCoercive.inner_self_pos hu

/-- **P-8.12 (1)**, the negative direction: on `x = (-A⁻¹ B p, p)` the first block of the product
vanishes and the form is `-(A⁻¹ B p, B p)`, negative once `B p ≠ 0`. -/
theorem problem_8_12_neg (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {p : EuclideanSpace 𝕜 (Fin m)} (hp : p ≠ 0) :
    RCLike.re (inner 𝕜 (blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)
      (saddleMatrix A B 0 ⬝ blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)) < 0 := by
  have hAinv := (Matrix.posDef_iff_isSymmetricCoercive A⁻¹).1 hA.inv
  have hBp : (B ⬝ p) ≠ 0 := fun h => hp (hB (by
    rw [show (Matrix.toEuclideanLin B) p = (B ⬝ p) from rfl, h, map_zero]))
  have hfst : (A ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) + (B ⬝ p) = 0 := by
    rw [show (A ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) = -(A ⬝ (A⁻¹ ⬝ (B ⬝ p))) from map_neg _ _,
      apply_nonsing_inv hA.isUnit]
    abel
  rw [saddleMatrix_apply_blockVec, hfst, toEuclideanLin_zero_apply, add_zero, inner_blockVec,
    inner_zero_right, zero_add,
    show (Bᴴ ⬝ (-(A⁻¹ ⬝ (B ⬝ p)))) = -(Bᴴ ⬝ (A⁻¹ ⬝ (B ⬝ p))) from map_neg _ _,
    inner_neg_right, inner_conjTranspose', map_neg, neg_lt_zero, ← inner_conj_symm, RCLike.conj_re]
  exact hAinv.isCoercive.inner_self_pos hBp

/-- A Hermitian matrix whose real spectrum is nonnegative has a nonnegative quadratic form: the
bridge from "no negative eigenvalue" to the sign of `(M x, x)`, through Mathlib's
`Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`. -/
private theorem re_inner_nonneg_of_spectrum_nonneg {k : Type*} [Fintype k] [DecidableEq k]
    {M : Matrix k k 𝕜} (hM : M.IsHermitian) (hspec : ∀ μ ∈ spectrum ℝ M, 0 ≤ μ)
    (v : EuclideanSpace 𝕜 k) : 0 ≤ RCLike.re (inner 𝕜 v (M ⬝ v)) := by
  have hps : M.PosSemidef :=
    (Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg hM).2 fun i =>
      hspec _ (Matrix.IsHermitian.eigenvalues_mem_spectrum_real hM i)
  have h := hps.re_dotProduct_nonneg (WithLp.ofLp v)
  have hval : star (WithLp.ofLp v) ⬝ᵥ (M *ᵥ WithLp.ofLp v) = inner 𝕜 v (M ⬝ v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  rwa [hval] at h

/-- **P-8.12 (1)**: *the saddle-point matrix has both positive and negative eigenvalues.*  The
two signs of its quadratic form are `problem_8_12_pos` and `problem_8_12_neg`, exactly the two
choices of `x` the problem asks for; a Hermitian matrix whose spectrum has one sign has a
quadratic form of that sign, so each choice forbids the corresponding half-line. -/
theorem problem_8_12_indefinite (hA : A.PosDef) (hB : Function.Injective (Matrix.toEuclideanLin B))
    {u : EuclideanSpace 𝕜 (Fin n)} (hu : u ≠ 0) {p : EuclideanSpace 𝕜 (Fin m)} (hp : p ≠ 0) :
    (∃ μ ∈ spectrum ℝ (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)), 0 < μ) ∧
      ∃ μ ∈ spectrum ℝ (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)), μ < 0 := by
  set M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) 𝕜 :=
    saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) with hMdef
  have hherm : M.IsHermitian := by
    rw [hMdef, Matrix.IsHermitian, saddleMatrix, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_conjTranspose, hA.isHermitian.eq, Matrix.conjTranspose_zero]
  have hhermneg : (-M).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_neg, hherm.eq]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have hneg : ∀ μ ∈ spectrum ℝ (-M), 0 ≤ μ := by
      intro μ hμ
      rw [← spectrum.neg_eq, Set.mem_neg] at hμ
      linarith [hcon _ hμ]
    have h := re_inner_nonneg_of_spectrum_nonneg hhermneg hneg
      (blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
    rw [show ((-M) ⬝ blockVec u (0 : EuclideanSpace 𝕜 (Fin m)))
        = -(M ⬝ blockVec u (0 : EuclideanSpace 𝕜 (Fin m))) from by
      rw [show (Matrix.toEuclideanLin (-M) :
          EuclideanSpace 𝕜 (Fin n ⊕ Fin m) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n ⊕ Fin m))
        = -Matrix.toEuclideanLin M from map_neg _ _]
      rfl, inner_neg_right, map_neg, neg_nonneg] at h
    exact absurd (problem_8_12_pos (B := B) hA hu) (not_lt.2 h)
  · by_contra hcon
    push Not at hcon
    have h := re_inner_nonneg_of_spectrum_nonneg hherm hcon (blockVec (-(A⁻¹ ⬝ (B ⬝ p))) p)
    exact absurd (problem_8_12_neg hA hB hp) (not_lt.2 h)

/-- **P-8.12 (2)–(3)**, the key computation: the quadratic form of the saddle-point matrix
vanishes on every vector of the shape `r = (0, s)`, which is the shape the residual of the
initial guess of P-8.12 (2) has. -/
theorem inner_saddleMatrix_blockVec_zero (s : EuclideanSpace 𝕜 (Fin m)) :
    inner 𝕜 (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) s)
        (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
          ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) s) = 0 := by
  have h1 : (A ⬝ (0 : EuclideanSpace 𝕜 (Fin n))) + (B ⬝ s) = (B ⬝ s) := by
    rw [map_zero, zero_add]
  have h2 : (Bᴴ ⬝ (0 : EuclideanSpace 𝕜 (Fin n)))
      + ((0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ s) = 0 := by
    rw [map_zero, zero_add, toEuclideanLin_zero_apply]
  rw [saddleMatrix_apply_blockVec, h1, h2, inner_blockVec, inner_zero_left, inner_zero_right,
    add_zero]

/-- **P-8.12 (2)**: *how to select an initial guess `x_0 = (u_0, 0)` whose residual is
`r_0 = (0, s_0)`* — take `u_0` with `A u_0 = f`; then the first block of `r_0` vanishes and
`s_0 = -Bᴴ u_0`. -/
theorem problem_8_12_residual (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    blockVec f (0 : EuclideanSpace 𝕜 (Fin m))
        - (saddleMatrix A B 0 ⬝ blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)) := by
  rw [saddleMatrix_apply_blockVec, map_zero, add_zero, toEuclideanLin_zero_apply, add_zero, hu₀]
  refine WithLp.ofLp_injective 2 ?_
  rw [WithLp.ofLp_sub, blockVec, blockVec, blockVec, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, ← Sum.elim_sub_sub]
  simp

/-- **P-8.12 (2)**: *what happens if we attempt to use the steepest descent algorithm with this
initial guess?*  It stalls: the step length `(r_0, r_0)/(A r_0, r_0)` has a vanishing denominator
because `r_0 = (0, s_0)`, so the iteration never leaves `x_0`.  (Division by zero is `0` in Lean,
which is what makes the stalled step literally the identity.) -/
theorem problem_8_12_steepestDescent_stalls (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    Projection.steepestDescentStep
        (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec f 0) (blockVec u₀ 0)
      = blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)) := by
  have hr := problem_8_12_residual (B := B) f hu₀
  rw [Projection.steepestDescentStep, Projection.step1,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ blockVec u₀ 0) from rfl, hr,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) from rfl,
    inner_saddleMatrix_blockVec_zero (A := A) (B := B) _,
    div_zero, zero_smul, add_zero]

/-- **P-8.12 (3)**: *what happens if the minimal residual iteration is applied with the same
initial guess?*  It stalls too, and for the same reason: its step length is
`(A r_0, r_0)/(A r_0, A r_0)`, whose *numerator* is the quantity that vanishes. -/
theorem problem_8_12_minRes_stalls (f : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : (A ⬝ u₀) = f) :
    Projection.minResStep
        (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec f 0) (blockVec u₀ 0)
      = blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)) := by
  have hr := problem_8_12_residual (B := B) f hu₀
  have hzero : inner 𝕜 (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) = 0 := by
    rw [← inner_conj_symm,
      inner_saddleMatrix_blockVec_zero (A := A) (B := B) _,
      map_zero]
  rw [Projection.minResStep, Projection.step1,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec u₀ (0 : EuclideanSpace 𝕜 (Fin m)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜) ⬝ blockVec u₀ 0) from rfl, hr,
    show (Matrix.toEuclideanLin (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)))
        (blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀)))
      = (saddleMatrix A B (0 : Matrix (Fin m) (Fin m) 𝕜)
        ⬝ blockVec (0 : EuclideanSpace 𝕜 (Fin n)) (-(Bᴴ ⬝ u₀))) from rfl, hzero, zero_div,
    zero_smul, add_zero]

/-- **P-8.12 (5)**: in the iteration `u_{k+1} = B⁻¹(f - C p_k)`, `p_{k+1} = p_k + α_k Cᵀ u_{k+1}`
(the book's `B`, `C` are this file's `A`, `B`), the increment `Bᴴ u_{k+1}` *is* the residual
`s_k = g - S p_k` of `p_k` for the reduced system `S p = g` of P-8.12 (4), so
`p_{k+1} = p_k + α_k s_k`; and the steepest-descent choice `α_k = (s_k, s_k)/(S s_k, s_k)` makes
`p_{k+1}` the steepest-descent iterate for that system. -/
theorem problem_8_12_reduced (f : EuclideanSpace 𝕜 (Fin n))
    (p : EuclideanSpace 𝕜 (Fin m)) :
    (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) = schurRhs A B f 0 - (schur A B ⬝ p) ∧
      Projection.steepestDescentStep (Matrix.toEuclideanLin (schur A B)) (schurRhs A B f 0) p
        = p + (inner 𝕜 (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) /
            inner 𝕜 (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p))))
              (schur A B ⬝ (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p))))))
          • (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) := by
  have hs : (Bᴴ ⬝ (A⁻¹ ⬝ (f - (B ⬝ p)))) = schurRhs A B f 0 - (schur A B ⬝ p) := by
    rw [conjTranspose_inv_sub, schurRhs, sub_zero]
  refine ⟨hs, ?_⟩
  rw [Projection.steepestDescentStep, Projection.step1, hs]

end Problem812

end SaadSparse.Chapter08
