import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearSolve.Multigrid.Basic

/-!
# Saad §13.3: inter-grid operations

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §13.3: the two operators that move a vector between a fine grid and the coarse grid obtained
from it by dropping every other point — the *prolongation* `I_{2h}^h` (linear interpolation) and the
*restriction* `I_h^{2h}` (injection, and full weighting) — in one and two dimensions.

## The indexing convention

Saad's fine grid has `n` interior points `x_i^h = i h`, `i = 1, …, n`, with `h = 1/(n + 1)`, and
the coarse grid keeps every other one, `x_j^{2h} = x_{2j}^h`; that forces `n` to be odd. Writing
`n = 2 m + 1` leaves `m` interior coarse points, and no divisibility hypothesis is ever needed
below because the sizes are `2 * m + 1` and `m` by construction.

Interior points are numbered from `0` here, as everywhere in this library: a fine index
`p : Fin (2 * m + 1)` is Saad's `i = p + 1`, and a coarse index `q : Fin m` is Saad's `j = q + 1`.
Saad's coarse point `x_j^{2h} = x_{2j}^h` is therefore the fine point of index `p = 2 q + 1`, and
his (13.30),

`v^h_{2j} = v^{2h}_j`,   `v^h_{2j+1} = (v^{2h}_j + v^{2h}_{j+1}) / 2`,

reads on the `0`-based interior indices as

`v^h_{2q+1} = v^{2h}_q`,   `v^h_{2q} = (v^{2h}_{q-1} + v^{2h}_q) / 2`,

a coarse value outside `Fin m` being the boundary value `0`. So the entries of
`SaadSparse.Chapter13.prolongation1D` are

* `1` at `(2 q + 1, q)` — the fine point that *is* a coarse point;
* `1 / 2` at `(2 q, q)` and at `(2 q + 2, q)` — the two fine points either side of it;

that is, column `q` carries the stencil `½ [1 2 1]` on the fine rows `2 q, 2 q + 1, 2 q + 2`.
Dually, row `q` of `SaadSparse.Chapter13.restriction1D` carries `¼ [1 2 1]` on the fine columns
`2 q, 2 q + 1, 2 q + 2`, which is Saad's full weighting (13.34); the shift is why the `2j` of the
book is the `2q + 1` here.

## What the section says

* `equation_13_35`, and `equation_13_37` in two dimensions: full weighting is the scaled transpose
  of linear interpolation, `I_h^{2h} = 2^{-d} (I_{2h}^h)ᵀ` with `d` the dimension, equivalently
  `I_{2h}^h = 2^d (I_h^{2h})ᵀ`.
* `equation_13_31` and `equation_13_38`: the two-dimensional operators are Kronecker products of
  the one-dimensional ones, so the two-dimensional stencils are the products of the one-dimensional
  ones — `¼[1 2 1] ⊗ ¼[1 2 1] = 1/16 [[1, 2, 1], [2, 4, 2], [1, 2, 1]]` for full weighting.

The use the chapter makes of the transpose relation is that the coarse-grid correction of §13.4 is
unchanged when Saad's restriction is replaced by the *adjoint* of the prolongation, which is the
form `Numlib/LinearSolve/Multigrid/Basic.lean` takes: `Multigrid.coarseProjection A hA Pr` depends
on `Pr` only through `LinearMap.range Pr`, so the positive factor `2^d` cancels
(`coarseProjection_eq_of_scaled`, `coarseProjection_apply_eq_of_smul`).
-/

open Matrix

open scoped Kronecker Matrix

namespace SaadSparse.Chapter13

/-! ### The one-dimensional inter-grid operators -/

/-- Saad (13.30): the one-dimensional **linear interpolation** (prolongation) matrix `I_{2h}^h`,
carrying the `m` interior coarse values to the `2 m + 1` interior fine values.

Column `q` is the stencil `½ [1 2 1]` on the fine rows `2 q`, `2 q + 1`, `2 q + 2`: the fine point
`2 q + 1` is the coarse point `q` and takes its value, and the two fine points either side of it
take the average of their coarse neighbours (a coarse neighbour outside `Fin m` being the boundary
value `0`). For `m = 3` this is Saad's displayed `7 × 3` matrix. -/
noncomputable def prolongation1D (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
    else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
    else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
    else 0

/-- The entries of the interpolation matrix, read off its definition. -/
theorem prolongation1D_apply (m : ℕ) (i : Fin (2 * m + 1)) (j : Fin m) :
    prolongation1D m i j =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 2
      else 0 :=
  rfl

/-- Saad (13.32): the one-dimensional **restriction by injection** `I_h^{2h}`, which reads off the
fine value at the fine point `2 q + 1` that carries the coarse point `q`. -/
def injection1D (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun j i => if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 else 0

/-- The entries of the injection matrix, read off its definition. -/
theorem injection1D_apply (m : ℕ) (j : Fin m) (i : Fin (2 * m + 1)) :
    injection1D m j i = if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 else 0 :=
  rfl

/-- Saad (13.33)–(13.34): the one-dimensional **full weighting** restriction `I_h^{2h}`,
`v^{2h}_j = (v^h_{2j-1} + 2 v^h_{2j} + v^h_{2j+1}) / 4`.

Row `q` is the stencil `¼ [1 2 1]` on the fine columns `2 q`, `2 q + 1`, `2 q + 2`, the middle one
being the fine point that carries the coarse point `q`. Unlike interpolation, this needs no
boundary convention: all three fine indices are interior for every `q : Fin m`. -/
noncomputable def restriction1D (m : ℕ) : Matrix (Fin m) (Fin (2 * m + 1)) ℝ :=
  Matrix.of fun j i =>
    if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 / 2
    else if (i : ℕ) = 2 * (j : ℕ) then 1 / 4
    else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 4
    else 0

/-- The entries of the full-weighting matrix, read off its definition. -/
theorem restriction1D_apply (m : ℕ) (j : Fin m) (i : Fin (2 * m + 1)) :
    restriction1D m j i =
      if (i : ℕ) = 2 * (j : ℕ) + 1 then 1 / 2
      else if (i : ℕ) = 2 * (j : ℕ) then 1 / 4
      else if (i : ℕ) = 2 * (j : ℕ) + 2 then 1 / 4
      else 0 :=
  rfl

/-! ### How the one-dimensional operators act -/

/-- The row of the interpolation matrix at a fine point `p = 2 q + 1` that *is* a coarse point has
the entry `1` in the column `q`. -/
theorem prolongation1D_apply_of_odd (m : ℕ) {p : Fin (2 * m + 1)} {q : Fin m}
    (hp : (p : ℕ) = 2 * (q : ℕ) + 1) : prolongation1D m p q = 1 := by
  rw [prolongation1D_apply, ite_eq_left hp]

/-- The same row is zero in every other column: interpolation is exact, not merely accurate, at the
fine points that are coarse points. -/
theorem prolongation1D_apply_of_odd_of_ne (m : ℕ) {p : Fin (2 * m + 1)} {q b : Fin m}
    (hp : (p : ℕ) = 2 * (q : ℕ) + 1) (hb : b ≠ q) : prolongation1D m p b = 0 := by
  have hbq : (b : ℕ) ≠ (q : ℕ) := fun h => hb (Fin.val_injective h)
  rw [prolongation1D_apply, hp, ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- Linear interpolation is *exact* at the fine points that are coarse points: with `p = 2 q + 1`,
`(I_{2h}^h v)_p = v_q`. This is the first half of Saad (13.30). -/
theorem prolongation1D_mulVec_odd (m : ℕ) (u : Fin m → ℝ) (q : Fin m)
    {p : Fin (2 * m + 1)} (hp : (p : ℕ) = 2 * (q : ℕ) + 1) :
    (prolongation1D m *ᵥ u) p = u q := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single q]
  · rw [prolongation1D_apply_of_odd m hp, one_mul]
  · intro b _ hb
    rw [prolongation1D_apply_of_odd_of_ne m hp hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q) h

/-- Restriction by injection reads off the fine value at the coarse point: with `p = 2 q + 1`,
`(I_h^{2h} v)_q = v_p`. This is Saad (13.32). -/
theorem injection1D_mulVec (m : ℕ) (v : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {p : Fin (2 * m + 1)} (hp : (p : ℕ) = 2 * (q : ℕ) + 1) :
    (injection1D m *ᵥ v) q = v p := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single p]
  · rw [injection1D_apply, ite_eq_left hp, one_mul]
  · intro b _ hb
    have hbp : (b : ℕ) ≠ (p : ℕ) := fun h => hb (Fin.val_injective h)
    rw [injection1D_apply, ite_eq_right (by omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- Saad (13.34) as an action: full weighting averages the three fine values around the coarse
point with the weights `¼, ½, ¼`. -/
theorem restriction1D_mulVec (m : ℕ) (v : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {a b c : Fin (2 * m + 1)} (ha : (a : ℕ) = 2 * (q : ℕ)) (hb : (b : ℕ) = 2 * (q : ℕ) + 1)
    (hc : (c : ℕ) = 2 * (q : ℕ) + 2) :
    (restriction1D m *ᵥ v) q = (v a + 2 * v b + v c) / 4 := by
  have hab : a ≠ b := fun h => by rw [h, hb] at ha; omega
  have hac : a ≠ c := fun h => by rw [h, hc] at ha; omega
  have hbc : b ≠ c := fun h => by rw [h, hc] at hb; omega
  have hzero : ∀ p ∈ Finset.univ, p ∉ ({a, b, c} : Finset (Fin (2 * m + 1))) →
      restriction1D m q p * v p = 0 := by
    intro p _ hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    obtain ⟨hpa, hpb, hpc⟩ := hp
    have h1 : (p : ℕ) ≠ 2 * (q : ℕ) := fun h => hpa (Fin.val_injective (h.trans ha.symm))
    have h2 : (p : ℕ) ≠ 2 * (q : ℕ) + 1 := fun h => hpb (Fin.val_injective (h.trans hb.symm))
    have h3 : (p : ℕ) ≠ 2 * (q : ℕ) + 2 := fun h => hpc (Fin.val_injective (h.trans hc.symm))
    rw [restriction1D_apply, ite_eq_right h2, ite_eq_right h1, ite_eq_right h3, zero_mul]
  rw [mulVec_apply_eq_sum, ← Finset.sum_subset (Finset.subset_univ _) hzero,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, restriction1D_apply, restriction1D_apply, restriction1D_apply,
    ite_eq_right (by omega), ite_eq_left ha, ite_eq_left hb, ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left hc]
  ring

/-- Restriction by injection is a left inverse of linear interpolation: interpolating a coarse
vector and then sampling at the coarse points returns it. -/
theorem injection1D_mul_prolongation1D (m : ℕ) : injection1D m * prolongation1D m = 1 := by
  ext q q'
  obtain ⟨p, hp⟩ : ∃ p : Fin (2 * m + 1), (p : ℕ) = 2 * (q : ℕ) + 1 :=
    ⟨⟨2 * (q : ℕ) + 1, by omega⟩, rfl⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [injection1D_apply, ite_eq_left hp, one_mul, prolongation1D_apply, Matrix.one_apply]
    by_cases h : q = q'
    · subst h
      rw [ite_eq_left hp, ite_eq_left rfl]
    · have hne : (q : ℕ) ≠ (q' : ℕ) := fun hv => h (Fin.val_injective hv)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right h]
  · intro b _ hb
    have hbp : (b : ℕ) ≠ (p : ℕ) := fun hv => hb (Fin.val_injective hv)
    rw [injection1D_apply, ite_eq_right (by omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Linear interpolation is injective, which is the hypothesis of
`Multigrid.galerkinCoarse_isSymmetricCoercive`: it is what makes the Galerkin coarse problem of
§13.4 well posed. -/
theorem injective_prolongation1D (m : ℕ) :
    Function.Injective (toEuclideanLin (prolongation1D m)) := by
  intro x y h
  have hxy : prolongation1D m *ᵥ WithLp.ofLp x = prolongation1D m *ᵥ WithLp.ofLp y :=
    congrArg WithLp.ofLp h
  have hres := congrArg (fun z => injection1D m *ᵥ z) hxy
  simp only [Matrix.mulVec_mulVec, injection1D_mul_prolongation1D, Matrix.one_mulVec] at hres
  exact WithLp.ofLp_injective 2 hres

/-! ### The transpose relation, Saad (13.35) -/

/-- **Saad (13.35)**: in one dimension full weighting is the scaled transpose of linear
interpolation, `I_h^{2h} = 2^{-d} (I_{2h}^h)ᵀ` with `d = 1`. Both stencils are `[1 2 1]`, and the
scaling is the only difference between them: `¼[1 2 1]` against `½[1 2 1]`. -/
theorem equation_13_35 (m : ℕ) : restriction1D m = (1 / 2 : ℝ) • (prolongation1D m)ᵀ := by
  ext j i
  rw [Matrix.smul_apply, Matrix.transpose_apply, prolongation1D_apply, restriction1D_apply,
    smul_eq_mul]
  split_ifs <;> norm_num

/-- Saad (13.35) with the scaling on the other side, `I_{2h}^h = 2^d (I_h^{2h})ᵀ` at `d = 1`. -/
theorem prolongation1D_eq_smul_transpose (m : ℕ) :
    prolongation1D m = (2 : ℝ) • (restriction1D m)ᵀ := by
  rw [equation_13_35, Matrix.transpose_smul, Matrix.transpose_transpose, smul_smul]
  norm_num

/-! ### The two-dimensional operators, Saad (13.31) and (13.38) -/

/-- The two-dimensional **linear interpolation** of Saad (13.31), on a fine grid of
`(2 m₁ + 1) × (2 m₂ + 1)` interior points. It is the Kronecker product of the one-dimensional
interpolations in the two coordinate directions, which is what (13.31) says: the bilinear
interpolation weights `1`, `½`, `¼` are the products of the one-dimensional weights `1`, `½`. -/
noncomputable def prolongation2D (m₁ m₂ : ℕ) :
    Matrix (Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) (Fin m₁ × Fin m₂) ℝ :=
  prolongation1D m₁ ⊗ₖ prolongation1D m₂

/-- Every entry of the two-dimensional interpolation matrix is the product of the two
one-dimensional entries, one per coordinate direction. -/
theorem prolongation2D_apply (m₁ m₂ : ℕ) (i : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1))
    (j : Fin m₁ × Fin m₂) :
    prolongation2D m₁ m₂ i j = prolongation1D m₁ i.1 j.1 * prolongation1D m₂ i.2 j.2 :=
  rfl

/-- The two-dimensional **full weighting** restriction of Saad (13.38), the Kronecker product of
the one-dimensional full weightings. Its stencil is therefore
`¼[1 2 1] ⊗ ¼[1 2 1] = 1/16 [[1, 2, 1], [2, 4, 2], [1, 2, 1]]`, Saad's (13.36). -/
noncomputable def restriction2D (m₁ m₂ : ℕ) :
    Matrix (Fin m₁ × Fin m₂) (Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) ℝ :=
  restriction1D m₁ ⊗ₖ restriction1D m₂

/-- Every entry of the two-dimensional full-weighting matrix is the product of the two
one-dimensional entries; that is the `1/16 [[1, 2, 1], [2, 4, 2], [1, 2, 1]]` stencil of Saad
(13.36), whose centre `¼`, edge `⅛` and corner `1/16` are `½·½`, `½·¼` and `¼·¼`. -/
theorem restriction2D_apply (m₁ m₂ : ℕ) (j : Fin m₁ × Fin m₂)
    (i : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)) :
    restriction2D m₁ m₂ j i = restriction1D m₁ j.1 i.1 * restriction1D m₂ j.2 i.2 :=
  rfl

/-- **Saad (13.31)**: two-dimensional interpolation is the tensor product of the one-dimensional
interpolations, so it separates variables — on a coarse grid function `v ⊗ w` it acts as
`(I_{2h}^h v) ⊗ (I_{2h}^h w)`. -/
theorem equation_13_31 (m₁ m₂ : ℕ) (v : Fin m₁ → ℝ) (w : Fin m₂ → ℝ) :
    prolongation2D m₁ m₂ *ᵥ kroneckerVec v w
      = kroneckerVec (prolongation1D m₁ *ᵥ v) (prolongation1D m₂ *ᵥ w) :=
  kronecker_mulVec _ _ v w

/-- **Saad (13.38)**: two-dimensional full weighting is the tensor product of the one-dimensional
full weightings, and separates variables in the same way. -/
theorem equation_13_38 (m₁ m₂ : ℕ) (v : Fin (2 * m₁ + 1) → ℝ) (w : Fin (2 * m₂ + 1) → ℝ) :
    restriction2D m₁ m₂ *ᵥ kroneckerVec v w
      = kroneckerVec (restriction1D m₁ *ᵥ v) (restriction1D m₂ *ᵥ w) :=
  kronecker_mulVec _ _ v w

/-- The first line of Saad (13.31), `v^h_{2i,2j} = v^{2h}_{i,j}`: two-dimensional interpolation is
exact at the fine points that are coarse points, those whose two indices are both odd. This holds
for an arbitrary coarse grid function, not only for an elementary tensor. -/
theorem prolongation2D_mulVec_odd (m₁ m₂ : ℕ) (u : Fin m₁ × Fin m₂ → ℝ) (q : Fin m₁ × Fin m₂)
    {p : Fin (2 * m₁ + 1) × Fin (2 * m₂ + 1)} (h₁ : (p.1 : ℕ) = 2 * (q.1 : ℕ) + 1)
    (h₂ : (p.2 : ℕ) = 2 * (q.2 : ℕ) + 1) :
    (prolongation2D m₁ m₂ *ᵥ u) p = u q := by
  rw [mulVec_apply_eq_sum, Fintype.sum_prod_type, Finset.sum_eq_single q.1]
  · rw [Finset.sum_eq_single q.2]
    · rw [prolongation2D_apply, prolongation1D_apply_of_odd m₁ h₁,
        prolongation1D_apply_of_odd m₂ h₂, one_mul, one_mul]
    · intro b _ hb
      rw [prolongation2D_apply, prolongation1D_apply_of_odd_of_ne m₂ h₂ hb, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ q.2) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [prolongation2D_apply, prolongation1D_apply_of_odd_of_ne m₁ h₁ hb, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ q.1) h

/-- **Saad (13.37)** at `d = 2`: in two dimensions full weighting is `2^{-d} = ¼` times the
transpose of linear interpolation, `I_h^{2h} = 2^{-d} (I_{2h}^h)ᵀ`. The factor is the product of
the two one-dimensional factors of `equation_13_35`, one per coordinate direction, which is
exactly why the exponent is the dimension. -/
theorem equation_13_37 (m₁ m₂ : ℕ) :
    restriction2D m₁ m₂ = (1 / 4 : ℝ) • (prolongation2D m₁ m₂)ᵀ := by
  have h₁ : restriction2D m₁ m₂ = restriction1D m₁ ⊗ₖ restriction1D m₂ := rfl
  have h₂ : (prolongation2D m₁ m₂)ᵀ = (prolongation1D m₁)ᵀ ⊗ₖ (prolongation1D m₂)ᵀ :=
    (kroneckerMap_transpose _ _ _).symm
  rw [h₁, h₂, equation_13_35, equation_13_35, smul_kronecker, kronecker_smul, smul_smul]
  norm_num

/-! ### Why the scaling does not matter

The coarse-grid correction of §13.4 is built from the pair `(I_{2h}^h, I_h^{2h})`, but the
backbone's `Multigrid.coarseProjection` is built from the prolongation alone, its restriction being
the adjoint `(I_{2h}^h)†`. By (13.35) the two restrictions differ by the positive factor `2^d`, and
the lemmas below are the two ways that factor cancels: it does not change the range of the
prolongation, and it multiplies both sides of the coarse equation. -/

section Backbone

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A nonzero scalar multiple of a linear map has the same range. -/
theorem range_smul_of_ne_zero {c : 𝕜} (hc : c ≠ 0) (Pr : F →ₗ[𝕜] E) :
    LinearMap.range (c • Pr) = LinearMap.range Pr := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨c • x, by simp⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨c⁻¹ • x, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

variable [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive)

/-- The coarse-grid projector depends on the prolongation only through its range. -/
theorem coarseProjection_congr_range {F' : Type*} [NormedAddCommGroup F']
    [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F'] (Pr : F →ₗ[𝕜] E) (Pr' : F' →ₗ[𝕜] E)
    (h : LinearMap.range Pr = LinearMap.range Pr') :
    Multigrid.coarseProjection A hA Pr = Multigrid.coarseProjection A hA Pr' := by
  simp only [Multigrid.coarseProjection, h]

/-- **The scaling of Saad (13.35) cancels.** Rescaling the prolongation by a nonzero scalar leaves
the coarse-grid projector unchanged, because it leaves the coarse space unchanged. -/
theorem coarseProjection_eq_of_scaled (Pr : F →ₗ[𝕜] E) {c : 𝕜} (hc : c ≠ 0) :
    Multigrid.coarseProjection A hA (c • Pr) = Multigrid.coarseProjection A hA Pr :=
  coarseProjection_congr_range A hA (c • Pr) Pr (range_smul_of_ne_zero hc Pr)

/-- The same cancellation on the other side: Saad's coarse equation `A_H y = I_h^{2h} (A x)` with
`I_h^{2h} = c (I_{2h}^h)†` and `A_H = c (I_{2h}^h)† A I_{2h}^h` is the backbone's coarse equation
multiplied by `c`, so it has the same solutions and produces the same coarse-grid projector. -/
theorem coarseProjection_apply_eq_of_smul [FiniteDimensional 𝕜 E] (Pr : F →ₗ[𝕜] E) {c : 𝕜}
    (hc : c ≠ 0) {x : E} {y : F}
    (hy : c • Multigrid.galerkinCoarse A Pr y = c • LinearMap.adjoint Pr (A x)) :
    Multigrid.coarseProjection A hA Pr x = Pr y :=
  Multigrid.coarseProjection_apply_eq A hA Pr (smul_right_injective F hc hy)

end Backbone

/-- The adjoint of the prolongation is Saad's full weighting scaled by `2^d`, here `d = 1`: the
restriction the backbone uses and the restriction the book uses differ by that factor and by
nothing else. -/
theorem adjoint_toEuclideanLin_prolongation1D (m : ℕ) :
    LinearMap.adjoint (toEuclideanLin (prolongation1D m))
      = (2 : ℝ) • toEuclideanLin (restriction1D m) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← map_smul]
  congr 1
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial,
    prolongation1D_eq_smul_transpose, Matrix.smul_apply, Matrix.transpose_apply]

end SaadSparse.Chapter13
