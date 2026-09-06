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

Not formalized: **P-8.9** (inexact Uzawa) and **P-8.6**; see `plans/saadsparse-ch7-9.md` §4.
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

end SaadSparse.Chapter08
