import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Quarteroni–Sacco–Saleri §12.6: a quick glance at the two-dimensional case

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §12.6.

The two-dimensional counterpart of §12.1 is the Poisson problem `-Δu = f` in `Ω` with `u = 0` on
`∂Ω` (12.90). On the unit square with the grid `x_{i,j} = (ih, jh)`, `h = 1/N`, the finite
difference approximation (12.91) with the **five-point discretization of the Laplacian**
`L_h u_h(x_{i,j}) = h⁻² (4 u_{i,j} - u_{i+1,j} - u_{i-1,j} - u_{i,j+1} - u_{i,j-1})` (12.92) has,
on the `(N - 1)²` interior unknowns, the pentadiagonal matrix (12.93); read on the index set
`Fin (N-1) × Fin (N-1)` it is `h⁻²` times the **Kronecker sum** `T ⊕ₖ T` of two copies of the
one-dimensional model matrix `T = tridiag(-1, 2, -1)`, which makes its symmetry, its positive
definiteness and its M-matrix property (Exercise 14) immediate.

## Main definitions

* `equation_12_92 N u i j` — the five-point discrete Laplacian at the interior node
  `x_{i+1,j+1}`, and `IsFivePointSolution N f u` the discrete problem (12.91).
* `fivePointMatrix N` — the matrix (12.93) of the scheme, `h⁻² (T ⊕ₖ T)`.

## Main results

* `equation_12_93` — the entries of `fivePointMatrix`: `4h⁻²` on the diagonal, `-h⁻²` at the four
  grid neighbours, `0` elsewhere, which is (12.93) under the row-major numbering.
* `exercise_12_14` — `fivePointMatrix` is symmetric positive definite and an M-matrix, so the
  discrete maximum principle holds.

* `exercise_12_15_rectangle` — Green's formula (12.95) on a rectangle, with the boundary integral
  written as its four sides: `∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `u ∈ C²`,
  `v ∈ C¹`, by the exercise's own hint over Mathlib's divergence theorem for a rectangle.

## Not formalized here

The two-dimensional finite element space (12.94), Green's formula (12.95) of Exercise 15 on a
*general* plane domain, and Property 12.2 are left as open nodes with their reasons: a
triangulation of a plane domain with continuous piecewise polynomials on it, the trace that makes
`H¹₀(Ω)` meaningful, a boundary measure `dγ` and an outward normal for the divergence theorem, and
the multi-dimensional Bramble–Hilbert interpolation theory behind (12.96)–(12.97) are all outside
the library (the book proves none of them either — Property 12.2 is quoted from [QV94]). The
rectangle is the case the divergence theorem *is* available for, and it is the domain §12.6's own
finite difference discretization uses, so it is proved here.

## Conventions

Grid functions are `ℕ → ℕ → ℝ` and the five-point stencil is written at the indices
`i, i + 1, i + 2` in each direction, so that `equation_12_92 N u i j` is `L_h u_h` at the interior
node `x_{i+1, j+1}`; this avoids truncated subtraction, as in §12.5. The matrix is indexed by
`Fin m × Fin m` with `m = N - 1` rather than by a flattened `Fin (m²)`: the book's offsets
`j = i ± 1`, `i ± (N + 1)` of (12.93) are the row-major reading of the pairs, and its `N + 1`
should read `N - 1` under the indexing that makes the count `(N - 1)²` correct (errata).
-/

open scoped Kronecker

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The five-point discretization (12.91)–(12.92) -/

/-- **The five-point discrete Laplacian (12.92)** at the interior node `x_{i+1, j+1}` of the
uniform grid of step `h = 1/N` on the unit square:
`L_h u_h (x_{i,j}) = h⁻² (4 u_{i,j} - u_{i+1,j} - u_{i-1,j} - u_{i,j+1} - u_{i,j-1})`, the centred
second difference (10.65) in each direction. -/
noncomputable def equation_12_92 (N : ℕ) (u : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (4 * u (i + 1) (j + 1) - u (i + 2) (j + 1) - u i (j + 1)
    - u (i + 1) (j + 2) - u (i + 1) j)

/-- **The five-point finite difference problem (12.91)**: the grid function vanishes on the
boundary indices and satisfies `L_h u_h (x_{i,j}) = f(x_{i,j})` at every interior node. -/
def IsFivePointSolution (N : ℕ) (f : ℕ → ℕ → ℝ) (u : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, i ≤ N → j ≤ N → (i = 0 ∨ i = N ∨ j = 0 ∨ j = N) → u i j = 0) ∧
    ∀ i j, i + 2 ≤ N → j + 2 ≤ N → equation_12_92 N u i j = f (i + 1) (j + 1)

/-! ### The matrix of the scheme (12.93) -/

/-- **The matrix (12.93) of the five-point scheme** on the `(N - 1)²` interior unknowns, indexed
by pairs: `h⁻²` times the Kronecker sum of two copies of the one-dimensional model matrix
`T = tridiag(-1, 2, -1)`. -/
noncomputable def fivePointMatrix (N m : ℕ) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  ((N : ℝ) ^ 2) • (Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ
    Matrix.symmTridiagonalToeplitz m (-1) 2)

/-- **The entries of the five-point matrix (12.93)**: `4 h⁻²` on the diagonal, `-h⁻²` at the four
grid neighbours `(i ± 1, j)` and `(i, j ± 1)`, and `0` elsewhere. -/
theorem equation_12_93 (N m : ℕ) (p q : Fin m × Fin m) :
    fivePointMatrix N m p q =
      if p = q then 4 * (N : ℝ) ^ 2
      else if (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))
          ∨ (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) then -((N : ℝ) ^ 2)
      else 0 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [fivePointMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerSum_apply,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
  simp only [Prod.mk.injEq, Fin.ext_iff]
  split_ifs <;> simp_all
  ring

/-! ### Exercise 12.14 -/

/-- A positive multiple of a positive definite real matrix is positive definite. -/
theorem posDef_smul {m : Type*} [Finite m] {A : Matrix m m ℝ} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) : (c • A).PosDef := by
  classical
  have := Fintype.ofFinite m
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hA.1.smul (IsSelfAdjoint.all c)) fun x hx => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos hc (hA.dotProduct_mulVec_pos hx)

/-- **Exercise 12.14**: the five-point matrix (12.93) is symmetric positive definite and an
M-matrix.  Positive definiteness is `Matrix.posDef_kroneckerSum` applied to the one-dimensional
model matrix `tridiag(-1, 2, -1)` with itself; the M-matrix property is then Stieltjes' criterion
`Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos`, the off-diagonal entries of the Kronecker sum of
two Z-matrices being nonpositive.  Consequently the discrete solution satisfies the maximum
principle `A u ≥ 0 ⇒ u ≥ 0`. -/
theorem exercise_12_14 {N m : ℕ} (hN : N ≠ 0) :
    (fivePointMatrix N m).PosDef ∧ (fivePointMatrix N m).IsMMatrix := by
  have hc : (0 : ℝ) < (N : ℝ) ^ 2 := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
    positivity
  have hpd : (fivePointMatrix N m).PosDef :=
    posDef_smul (Matrix.posDef_kroneckerSum (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m)
      (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two m)) hc
  refine ⟨hpd, Matrix.IsMMatrix.of_posDef_of_offDiag_nonpos hpd fun p q hpq => ?_⟩
  rw [equation_12_93]
  split_ifs with h1 h2
  · exact absurd h1 hpq
  · linarith
  · exact le_rfl

/-! ### Green's formula (12.95) on a rectangle -/

section Green

open Set MeasureTheory

/-- **Green's formula (12.95) on a rectangle**, Exercise 12.15:
`∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `Ω = (a₁, b₁) × (a₂, b₂)`, `u ∈ C²` and
`v ∈ C¹`. The boundary integral is written as the four sides, each carrying its outward normal:
`+(1, 0)` on `x = b₁`, `-(1, 0)` on `x = a₁`, `+(0, 1)` on `y = b₂` and `-(0, 1)` on `y = a₂`, so
that the parenthesized difference of four interval integrals *is* `∫_∂Ω (∇u · n) v dγ`.

The proof is the exercise's own hint — `div (v ∇u) = v Δu + ∇u · ∇v`, integrated over `Ω` and
closed by the divergence theorem — with Mathlib's divergence theorem for a rectangle,
`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le`, applied to the
pair `(v ∂₁u, v ∂₂u)`. A general plane domain would need a boundary measure `dγ` and an outward
normal, which the library does not have; see the description of `exercise_12_15` in the plan.

Partial derivatives are written `fderiv ℝ w p (1, 0)` and `fderiv ℝ w p (0, 1)`, so the Laplacian
of `u` at `p` is `fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0) +
fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)` (Quarteroni–Sacco–Saleri, *Numerical
Mathematics*, equation (12.95) and Exercise 12.15). -/
theorem exercise_12_15_rectangle {u v : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v)
    {a b : ℝ × ℝ} (hab : a ≤ b) :
    (∫ p in Icc a b,
        -(fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
          + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p)
      = (∫ p in Icc a b,
          fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
            + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        - ((∫ y in a.2..b.2, fderiv ℝ u (b.1, y) (1, 0) * v (b.1, y))
            - (∫ y in a.2..b.2, fderiv ℝ u (a.1, y) (1, 0) * v (a.1, y))
            + (∫ x in a.1..b.1, fderiv ℝ u (x, b.2) (0, 1) * v (x, b.2))
            - (∫ x in a.1..b.1, fderiv ℝ u (x, a.2) (0, 1) * v (x, a.2))) := by
  have hu1 : ContDiff ℝ 1 fun q => fderiv ℝ u q (1, 0) :=
    (hu.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const
  have hu2 : ContDiff ℝ 1 fun q => fderiv ℝ u q (0, 1) :=
    (hu.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const
  have hcv1 : Continuous fun p => fderiv ℝ v p (1, 0) :=
    (hv.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcv2 : Continuous fun p => fderiv ℝ v p (0, 1) :=
    (hv.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcu11 : Continuous fun p => fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0) :=
    (hu1.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  have hcu22 : Continuous fun p => fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1) :=
    (hu2.fderiv_right (m := 0) le_rfl).continuous.clm_apply continuous_const
  set f : ℝ × ℝ → ℝ := fun p => fderiv ℝ u p (1, 0) * v p with hf
  set g : ℝ × ℝ → ℝ := fun p => fderiv ℝ u p (0, 1) * v p with hg
  set f' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    fderiv ℝ u p (1, 0) • fderiv ℝ v p
      + v p • fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p with hf'
  set g' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun p =>
    fderiv ℝ u p (0, 1) • fderiv ℝ v p
      + v p • fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p with hg'
  have hdf : ∀ p : ℝ × ℝ, HasFDerivAt f (f' p) p := fun p =>
    (hu1.differentiable one_ne_zero p).hasFDerivAt.mul
      (hv.differentiable one_ne_zero p).hasFDerivAt
  have hdg : ∀ p : ℝ × ℝ, HasFDerivAt g (g' p) p := fun p =>
    (hu2.differentiable one_ne_zero p).hasFDerivAt.mul
      (hv.differentiable one_ne_zero p).hasFDerivAt
  have hcf : Continuous f := hu1.continuous.mul hv.continuous
  have hcg : Continuous g := hu2.continuous.mul hv.continuous
  have hsplit : ∀ p : ℝ × ℝ, f' p (1, 0) + g' p (0, 1)
      = (fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
          + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        + (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
            + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    intro p
    simp only [hf', hg', add_apply, smul_apply, smul_eq_mul]
    ring
  have hK : IsCompact (Icc a b) := isCompact_Icc
  have hGrad : IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
      + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1)) (Icc a b) :=
    ((hu1.continuous.mul hcv1).add (hu2.continuous.mul hcv2)).continuousOn.integrableOn_compact hK
  have hLap : IntegrableOn (fun p : ℝ × ℝ =>
      (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
        + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p) (Icc a b) :=
    ((hcu11.add hcu22).mul hv.continuous).continuousOn.integrableOn_compact hK
  have hi : IntegrableOn (fun p => f' p (1, 0) + g' p (0, 1)) (Icc a b) :=
    (hGrad.add hLap).congr_fun (fun p _ => (hsplit p).symm) measurableSet_Icc
  have hdiv := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    f g f' g' a b hab ∅ Set.countable_empty hcf.continuousOn hcg.continuousOn
    (fun p _ => hdf p) (fun p _ => hdg p) hi
  have hI : (∫ p in Icc a b, (f' p (1, 0) + g' p (0, 1)))
      = (∫ p in Icc a b, fderiv ℝ u p (1, 0) * fderiv ℝ v p (1, 0)
          + fderiv ℝ u p (0, 1) * fderiv ℝ v p (0, 1))
        + ∫ p in Icc a b, (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
            + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    rw [← integral_add hGrad hLap]
    exact setIntegral_congr_fun measurableSet_Icc fun p _ => hsplit p
  have hneg : (∫ p in Icc a b,
      -(fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
        + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p)
      = -∫ p in Icc a b, (fderiv ℝ (fun q => fderiv ℝ u q (1, 0)) p (1, 0)
          + fderiv ℝ (fun q => fderiv ℝ u q (0, 1)) p (0, 1)) * v p := by
    rw [← integral_neg]
    exact setIntegral_congr_fun measurableSet_Icc fun p _ => by ring
  rw [hneg]
  rw [hI] at hdiv
  simp only [hf, hg] at hdiv
  linarith

end Green

end QuarteroniSaccoSaleri.Chapter12
