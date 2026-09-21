import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Boundary.Polygon
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.AtkinsonHan.Chapter10.Section04

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
definiteness and its M-matrix property (Exercise 14) immediate. The finite element method of
the section — the space `V_h` of (12.94) on a triangulation and the error estimate (12.96) of
Property 12.2 — is stated on the triangulation scaffold of `Numlib/Geometry/Triangulation.lean`
and proved through Atkinson–Han's Theorem 10.4.1 (`NumlibSurface/AtkinsonHan/Chapter10/Section04`,
the one module of the other book this file imports, for its `ℙ_k` Lagrange element).

## Main definitions

* `equation_12_92 N u i j` — the five-point discrete Laplacian at the interior node
  `x_{i+1,j+1}`, and `IsFivePointSolution N f u` the discrete problem (12.91).
* `fivePointMatrix N` — the matrix (12.93) of the scheme, `h⁻² (T ⊕ₖ T)`.
* `equation_12_94 𝒯 k` — the finite element space `V_h ⊆ H¹₀(Ω)` (12.94).

## Main results

* `equation_12_93` — the entries of `fivePointMatrix`: `4h⁻²` on the diagonal, `-h⁻²` at the four
  grid neighbours, `0` elsewhere, which is (12.93) under the row-major numbering.
* `exercise_12_14` — `fivePointMatrix` is symmetric positive definite and an M-matrix, so the
  discrete maximum principle holds.

* `exercise_12_15`, `exercise_12_15_polygon` — Green's formula (12.95) of Exercise 12.15,
  `∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `u ∈ C²(Ω̄)` with `∇u` continuous up to
  the boundary and `v ∈ C¹(Ω̄)`, on a bounded `C¹` plane domain and on a triangulated polygon,
  with the arclength measure `dγ` and the outward unit normal `n` of the boundary theory of
  `Numlib/Analysis/Sobolev/Boundary/` (`IsContDiffDomain.boundaryMeasure`/`outwardNormal`,
  `Triangulation.boundaryMeasure`/`outwardNormal`); both are `exercise_12_15_of_boundaryData`,
  the formula for any `BoundaryData`, which is the exercise's own hint over the divergence
  theorem (`BoundaryData.integral_laplacian_mul_add_eq_of_continuousOn_fderiv`). The book's
  general plane domain is restated as one of these two; Lipschitz domains in general are out of
  scope.
* `exercise_12_15_rectangle` — the same formula on a rectangle, with the boundary integral
  written as its four sides, by the exercise's own hint over Mathlib's divergence theorem for a
  rectangle.
* `equation_12_94` — the finite element space `V_h ⊆ H¹₀(Ω)` of continuous piecewise polynomials
  of degree `≤ k` vanishing on `∂Ω` on a triangulation `𝒯_h` (`Triangulation.polySpaceZero`);
  `exists_mem_equation_12_94` says the book's functions are its elements (no trace theorem: a
  continuous `H¹` function vanishing on `∂Ω` is in `H¹₀`, Brezis's Theorem 9.17), and
  `finiteDimensional_equation_12_94` that it is finite-dimensional.
* `property_12_2` — the `H¹` estimate (12.96), `‖u − u_h‖_{H¹₀} ≤ (M/α₀) C h^l ‖u‖_{H^{l+1}}`,
  on a polygon triangulated by a regular family: Atkinson–Han's Theorem 10.4.1
  (`AtkinsonHan.Chapter10.theorem_10_4_1`, Céa's lemma and the interpolation estimate of
  Theorem 10.3.9) with the `ℙ_k` Lagrange element on the principal lattice, whose interpolant of
  a boundary-vanishing function lies in `V_h`.

## Not formalized here

The `L²` estimate (12.97) of Property 12.2 (`property_12_2_l2`) is left as an open node with its
reason: the `H²` regularity of the Dirichlet problem on a convex polygon behind the Aubin–Nitsche
argument (`notes/frontier.md` blocker 18; the abstract duality argument is
`AtkinsonHan.Chapter10.theorem_10_4_3`). Green's formula (12.95) on a *Lipschitz* plane domain in
general is out of scope: it is proved on bounded `C¹` domains and on triangulated polygons (the
boundary round of 2026-09-21, `notes/boundary/planning-brief.md` §1), and on the rectangle, the
domain §12.6's own finite difference discretization uses, directly from Mathlib's divergence
theorem. The book proves neither estimate of
Property 12.2 (both are quoted from [QV94]); (12.96) is proved here on the triangulation
scaffold of `Numlib/Geometry/Triangulation.lean`, with the polygon entering through the
hypothesis that `∂Ω` is a union of element edges (`Triangulation.FrontierSubsetEdges`), the
regularity `u ∈ H^{l+1}(Ω)` read on a representative continuous up to the boundary, and the
boundary condition `u = 0` on `∂Ω` on that representative.

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

/-! #### Green's formula (12.95) on a bounded `C¹` domain and on a triangulated polygon

The general plane domain of (12.95), through the boundary theory of
`Numlib/Analysis/Sobolev/Boundary/`: a domain `Ω` with boundary data `B : BoundaryData Ω` — a
surface measure `B.σ` on `∂Ω` (the arclength `dγ`), an outward unit normal `B.ν` (the book's
`n`) and the divergence theorem `∫_Ω div F = ∫_∂Ω F · ν dσ` for `F ∈ C¹(Ω̄)`
(`Numlib/Analysis/Sobolev/Boundary/Data.lean`). The two instances are the bounded `C¹` domain
(`IsContDiffDomain.boundaryData`, `Numlib/Analysis/Sobolev/Boundary/ContDiffDomain.lean`: the
divergence theorem by Fubini and the fundamental theorem of calculus on graph charts, glued by a
partition of unity) and the triangulated polygon (`Triangulation.boundaryData`,
`Numlib/Analysis/Sobolev/Boundary/Polygon.lean`: the sum over the elements, the interior edges
cancelling in partner pairs). The book's "`Ω` smooth enough" is restated as one of these two;
Lipschitz domains in general are out of scope (`notes/boundary/planning-brief.md` §1). -/

open TopologicalSpace

open scoped InnerProductSpace Laplacian

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **Green's formula (12.95) for boundary data**, Exercise 12.15 on a plane domain `Ω` with
boundary data `B` (surface measure `B.σ = dγ`, outward unit normal `B.ν = n`):
`∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `u ∈ C²(Ω̄)` with `∇u` continuous up to the
boundary and `v ∈ C¹(Ω̄)`. The book's "`u, v` smooth enough" is read as
`ContDiffOnClosure ℝ 2 u Ω`, `ContinuousOn (fderiv ℝ u) (closure Ω)` — the continuity of `∇u` on
`Ω̄` is what gives the boundary term `∇u · n` on `∂Ω` its meaning: the class `C²(Ω̄)` of
`ContDiffOnClosure` says that the derivatives *extend* continuously to `Ω̄`, not that
`fderiv ℝ u` itself is that extension on `∂Ω` — and `ContinuousOn v (closure Ω)`,
`ContDiffOnClosure ℝ 1 v Ω`. The proof is the exercise's own hint,
`div (v ∇u) = v Δu + ∇u · ∇v` over the divergence theorem `B.integral_div_eq`, which is the
backbone's `BoundaryData.integral_laplacian_mul_add_eq_of_continuousOn_fderiv`; here the signs
are rearranged. The two instances are `exercise_12_15` (a bounded `C¹` domain) and
`exercise_12_15_polygon` (a triangulated polygon); the rectangle is `exercise_12_15_rectangle`. -/
theorem exercise_12_15_of_boundaryData {Ω : Opens 𝔼₂} (B : BoundaryData Ω) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, B.ν x⟫_ℝ * v x ∂B.σ := by
  have h := B.integral_laplacian_mul_add_eq_of_continuousOn_fderiv hu' hu hv hv'
  simp only [neg_mul, integral_neg]
  linarith

/-- **Green's formula (12.95) on a bounded `C¹` plane domain**, Exercise 12.15:
`∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `u ∈ C²(Ω̄)` with `∇u` continuous up to the
boundary and `v ∈ C¹(Ω̄)`, with `n = hΩ.outwardNormal hb` the outward unit normal and
`dγ = hΩ.boundaryMeasure hb` the arclength measure on `∂Ω` of
`Numlib/Analysis/Sobolev/Boundary/GraphMeasure.lean`. The book's general plane domain is restated
as a bounded `C¹` domain (`IsContDiffDomain 1 Ω`: `∂Ω` is locally the graph of a `C¹` function
after a rigid motion); the polygonal case is `exercise_12_15_polygon`, and Lipschitz domains in
general are out of scope. This is `exercise_12_15_of_boundaryData` for
`IsContDiffDomain.boundaryData`, whose divergence theorem is
`IsContDiffDomain.integral_div_eq` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation
(12.95) and Exercise 12.15). -/
theorem exercise_12_15 {Ω : Opens 𝔼₂} (hΩ : IsContDiffDomain 1 (Ω : Set 𝔼₂))
    (hb : Bornology.IsBounded (Ω : Set 𝔼₂)) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, hΩ.outwardNormal hb x⟫_ℝ * v x ∂(hΩ.boundaryMeasure hb) :=
  exercise_12_15_of_boundaryData (hΩ.boundaryData hb) hu hu' hv hv'

/-- **Green's formula (12.95) on a triangulated polygon**, Exercise 12.15:
`∫_Ω (-Δu) v = ∫_Ω ∇u · ∇v - ∫_∂Ω (∇u · n) v dγ` for `u ∈ C²(Ω̄)` with `∇u` continuous up to the
boundary and `v ∈ C¹(Ω̄)`, on a plane domain `Ω` triangulated by `𝒯 : Triangulation Ω`
(`Numlib/Geometry/Triangulation.lean`), with `n = 𝒯.outwardNormal` the outward unit normal of the
boundary edges and `dγ = 𝒯.boundaryMeasure` the arclength measure on them, of
`Numlib/Analysis/Sobolev/Boundary/Polygon.lean`. No hypothesis beyond the axioms of
`Triangulation` is needed (the divergence theorem `Triangulation.integral_div_eq` holds for every
triangulation: a field continuous across an interior edge does not see it). This is
`exercise_12_15_of_boundaryData` for `Triangulation.boundaryData`; the `C¹` case is
`exercise_12_15` (Quarteroni–Sacco–Saleri, *Numerical Mathematics*, equation (12.95) and
Exercise 12.15). -/
theorem exercise_12_15_polygon {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {u v : 𝔼₂ → ℝ}
    (hu : ContDiffOnClosure ℝ 2 u Ω) (hu' : ContinuousOn (fderiv ℝ u) (closure (Ω : Set 𝔼₂)))
    (hv : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hv' : ContDiffOnClosure ℝ 1 v Ω) :
    ∫ x in (Ω : Set 𝔼₂), -Δ u x * v x
      = (∫ x in (Ω : Set 𝔼₂), ⟪gradient u x, gradient v x⟫_ℝ)
        - ∫ x, ⟪gradient u x, 𝒯.outwardNormal x⟫_ℝ * v x ∂𝒯.boundaryMeasure :=
  exercise_12_15_of_boundaryData 𝒯.boundaryData hu hu' hv hv'

end Green


/-! ### The finite element space (12.94) and Property 12.2

The two-dimensional finite element method of §12.6 on the triangulation scaffold of
`Numlib/Geometry/Triangulation.lean`: the space `V_h` of (12.94) is `Triangulation.polySpaceZero`
of `Numlib/Analysis/Sobolev/Triangulation.lean`, and Property 12.2 is Atkinson–Han's Theorem
10.4.1 (`AtkinsonHan.Chapter10.theorem_10_4_1`, Céa's lemma with the interpolation estimate of
Theorem 10.3.9) for the `ℙ_k` Lagrange element on the principal lattice
(`AtkinsonHan.Chapter10.latticeNode`, `latticeShapeFun`), the element whose global basis is the
Lagrange basis (8.36)–(8.37) of §8.5.2. -/

section FiniteElement

open MeasureTheory Set TopologicalSpace EuclideanSpace Filter
open scoped ENNReal

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- **The finite element space (12.94)**,

  `V_h = {v_h ∈ C⁰(Ω̄) : v_h|_T ∈ ℙ_k(T) for all T ∈ 𝒯_h, v_h|_∂Ω = 0}`,

as a subspace of `H¹₀(Ω)`: `Triangulation.polySpaceZero`, the elements of `H¹₀(Ω)` whose function
is (almost everywhere on `Ω`) a function continuous on `Ω̄`, polynomial of degree at most `k` on
each closed element in the reference coordinates (`Triangulation.IsPiecewisePoly`), and
vanishing on `∂Ω`. Every such function is the function of an element of `H¹₀(Ω)`
(`exists_mem_equation_12_94`), so `V_h` is the book's space; the membership in `H¹₀(Ω)` is
Brezis's Theorem 9.17, (i) ⇒ (ii), on any open set — no trace theorem is needed to read
`v_h|_∂Ω = 0`, and the piecewise-`ℙ_k` function lies in `H¹(Ω)` by the characterization through
lines (`Triangulation.memSobolev_of_piecewise`), not through Green's formula (12.95). -/
noncomputable def equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) :
    Submodule ℝ (SobolevEuclideanZero 2 1 2 Ω) :=
  𝒯.polySpaceZero 2 k

/-- Membership of `V_h` (12.94), unfolded. -/
theorem mem_equation_12_94_iff {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ)
    {w : SobolevEuclideanZero 2 1 2 Ω} :
    w ∈ equation_12_94 𝒯 k ↔ ∃ v : 𝔼₂ → ℝ, ContinuousOn v (closure (Ω : Set 𝔼₂)) ∧
      𝒯.IsPiecewisePoly k v ∧ EqOn v 0 (frontier (Ω : Set 𝔼₂)) ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  Iff.rfl

/-- **Every function of the book's `V_h` is the function of an element of (12.94)**: a
function continuous on `Ω̄`, piecewise polynomial of degree at most `k` and vanishing on `∂Ω`
lies in `H¹₀(Ω)`. -/
theorem exists_mem_equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {k : ℕ} {v : 𝔼₂ → ℝ}
    (hvc : ContinuousOn v (closure (Ω : Set 𝔼₂))) (hvp : 𝒯.IsPiecewisePoly k v)
    (hv0 : EqOn v 0 (frontier (Ω : Set 𝔼₂))) :
    ∃ w ∈ equation_12_94 𝒯 k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] v :=
  𝒯.exists_mem_polySpaceZero 2 (by simp) hvc hvp hv0

/-- **`V_h` is finite-dimensional**, `k ≥ 1`: its elements are determined by their values at the
nodes of the `ℙ_k` Lagrange element (`Triangulation.finiteDimensional_polySpaceZero`). -/
theorem finiteDimensional_equation_12_94 {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) {k : ℕ}
    (hk : 1 ≤ k) : FiniteDimensional ℝ (equation_12_94 𝒯 k) :=
  𝒯.finiteDimensional_polySpaceZero 2 (AtkinsonHan.Chapter10.isConformingElement_lattice hk 𝒯)
    (AtkinsonHan.Chapter10.latticeNode_mem_closure hk)
    (AtkinsonHan.Chapter10.nodalInterp_lattice_eval hk)

/-- **Property 12.2, the estimate (12.96).** Let `u ∈ H¹₀(Ω)` be the exact solution of the Poisson
problem (12.90), `∫_Ω ∇u · ∇v = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`, on a polygon `Ω ⊆ B(0, R)`
triangulated by a regular family `{𝒯_h}` (mesh parameters at most `H`, `∂Ω` a union of element
edges), and let `u_h ∈ V_h` be its finite element approximation with continuous piecewise
polynomials of degree `k ≥ 1`, the Galerkin solution on `V_h` (12.94). If `u ∈ H^{l+1}(Ω)` for
some `1 ≤ l ≤ k` (the book's `l = min(k, s − 1)` for `u ∈ H^s(Ω)`, `s ≥ 2`), read on a
representative `ũ` continuous up to the boundary with `ũ = 0` on `∂Ω`, then

  `‖u − u_h‖_{H¹₀(Ω)} ≤ (M/α₀) C h^l ‖u‖_{H^{l+1}(Ω)}`,

with `M = 1` the continuity constant of the form and `α₀ = (1 + (2R)²)⁻¹` its coercivity
constant on `H¹₀(Ω)` (Poincaré's inequality), and `C` independent of `h` and of `u`. The book
quotes the estimate from [QV94, Theorem 6.2.1]; it is Céa's lemma
(`IsGalerkinSolution.norm_sub_le`) with `v_h = Π_h u` and the interpolation estimate of
Atkinson–Han's Theorem 10.3.9 for the `ℙ_k` Lagrange element, packaged as
`AtkinsonHan.Chapter10.theorem_10_4_1`; `Π_h u ∈ V_h` because the Lagrange element is conforming,
polynomial and edge unisolvent, so that `Π_h ũ` vanishes on `∂Ω` with `ũ`
(`Triangulation.exists_mem_polySpaceZero_globalInterp`). The regularity `u ∈ H^{l+1}(Ω)` is read on
the continuous representative as in Theorem 10.3.9; the boundary condition `ũ = 0` on `∂Ω` is
the problem's, a hypothesis on a polygon (on a `C¹` domain it follows from `u ∈ H¹₀(Ω)`). The
`L²` estimate (12.97) is `property_12_2_l2`, open. -/
theorem property_12_2 {k : ℕ} (hk : 1 ≤ k) {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι}
    {𝒯 : ι → Triangulation Ω}
    (hreg : AtkinsonHan.Chapter10.IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ Metric.ball 0 R) {s : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
      (u : SobolevEuclideanZero 2 1 2 Ω),
      (∀ v : SobolevEuclideanZero 2 1 2 Ω, Elliptic.dirichletForm Ω u v = Elliptic.load Ω f v) →
      ∀ uh : ι → SobolevEuclideanZero 2 1 2 Ω,
        (∀ i, IsGalerkinSolution
          ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω))
          ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL)
          (equation_12_94 (𝒯 i) k) (uh i)) →
        ∀ ũ : 𝔼₂ → ℝ,
          SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
          MemSobolev ũ (s + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
          EqOn ũ 0 (frontier (Ω : Set 𝔼₂)) →
          ∀ i, ‖u - uh i‖ ≤ (1 / (1 + (2 * R) ^ 2)⁻¹) * C * (𝒯 i).meshSize ^ s
            * (sobolevNorm ũ (s + 1) 2 Ω volume).toReal := by
  have hk0 : 0 < k := hk
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have hα : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  have h10 := AtkinsonHan.Chapter10.theorem_10_4_1 (k := s) hs
    (AtkinsonHan.Chapter10.latticeNode k) (AtkinsonHan.Chapter10.latticeShapeFun k)
    (AtkinsonHan.Chapter10.latticeNode_mem_closure hk0)
    (fun i ↦ (AtkinsonHan.Chapter10.contDiff_latticeShapeFun k i).of_le (by simp))
    (fun q hq x _ ↦ AtkinsonHan.Chapter10.nodalInterp_lattice_eval hk0 q (hq.trans hsk) x)
    hreg hH (fun i ↦ AtkinsonHan.Chapter10.isConformingElement_lattice hk0 (𝒯 i))
    (AtkinsonHan.Chapter10.poissonForm_isBoundedWith Ω) hpos
    (AtkinsonHan.Chapter10.poissonForm_isEllipticWith Ω hR hΩ)
  obtain ⟨c, hc0, hc⟩ := h10
  refine ⟨c / (1 + (2 * R) ^ 2), by positivity, fun f u hu uh huh ũ hũ hũk hũc hũ0 i ↦ ?_⟩
  have hint : ∀ i, ∃ w ∈ equation_12_94 (𝒯 i) k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        (𝒯 i).globalInterp (AtkinsonHan.Chapter10.latticeNode k)
          (AtkinsonHan.Chapter10.latticeShapeFun k) ũ := fun i ↦
    (𝒯 i).exists_mem_polySpaceZero_globalInterp 2 (by simp)
      (AtkinsonHan.Chapter10.isConformingElement_lattice hk0 (𝒯 i))
      (fun i ↦ (AtkinsonHan.Chapter10.contDiff_latticeShapeFun k i).continuous)
      (AtkinsonHan.Chapter10.isEdgeUnisolvent_lattice hk0)
      (AtkinsonHan.Chapter10.latticeShapeFun_eq_eval k) (hedge i) hũ0
  have h := hc (AtkinsonHan.Chapter10.poissonLoad Ω f) u hu (fun i ↦ equation_12_94 (𝒯 i) k) uh
    huh ũ hũ hũk hũc hint i
  refine h.trans ?_
  -- the seminorm is bounded by the norm, and `(M/α₀) C = c`
  have hfin : sobolevNorm ũ (s + 1) 2 Ω volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hũk.sobolevNorm_le_sum_sobolevSeminorm (by simp))
    exact ENNReal.sum_ne_top.2 fun n _ ↦
      (hũk.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have hle : (sobolevSeminorm ũ (s + 1) 2 Ω volume).toReal
      ≤ (sobolevNorm ũ (s + 1) 2 Ω volume).toReal :=
    ENNReal.toReal_mono hfin
      (eLpNorm_weakIteratedFDeriv_le_sobolevNorm (by simp) (by simp) le_rfl)
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  have hcc : 1 / (1 + (2 * R) ^ 2)⁻¹ * (c / (1 + (2 * R) ^ 2)) = c := by
    field_simp
  rw [hcc]
  gcongr

end FiniteElement

end QuarteroniSaccoSaleri.Chapter12
