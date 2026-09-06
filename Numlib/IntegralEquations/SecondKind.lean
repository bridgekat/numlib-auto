import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Analysis.Normed.Ring.Inverse
import Numlib.Variational.ProjectionMethod

/-!
# Equations of the second kind

The abstract theory of the operator equation `(μ - K) u = f` on a Banach space and of its
approximations: what makes a projection method, a Nyström method or a two-grid iteration for such
an equation stable and convergent.  Everything here is operator theory — no kernel, no quadrature
and no function space — although the consumers are integral equations, which is why the module
sits beside `Numlib.IntegralEquations.Basic`.  The account followed is Chapter 12 of Atkinson–Han,
*Theoretical Numerical Analysis*[^atkinson-han].

Invertible operators are carried as a `ContinuousLinearEquiv` together with an equation
identifying its coercion, so that every bound below is about a genuine inverse and never about the
junk value of `Ring.inverse`.

## Projection methods

`(μ - K) u = f` is approximated by `(μ - P K) uₙ = P f` with `uₙ` in the range of an idempotent
`P`, which is `IsProjectionMethodSolution` (Kress[^kress]).  The qualitative stability of that
approximation is `exists_isProjectionMethodSolution_of_isCompactOperator`; what is added here is
the quantitative two-sided estimate.  Everything follows from the purely algebraic error
equation `(μ - P K) (u - uₙ) = μ (u - P u)` (`sub_projection_eq`): `exists_equiv_of_projection`
perturbs `μ - K` into `μ - P K` by the geometric series as soon as `‖K - P K‖` is small, and
`norm_smul_sub_le_of_projection` together with `norm_sub_le_of_projection` sandwiches the error
`‖u - uₙ‖` between two multiples of the approximation error `‖u - P u‖`, so that the two tend to
zero at exactly the same rate.  For a compact `K` and projections converging pointwise to the
identity, `‖K - Pₙ K‖ → 0` by `tendsto_opNorm_comp_of_isCompactOperator`, which is what makes the
hypothesis available.

`exists_equiv_smul_sub_comp_comm` is Jacobson's identity, `(μ - B A)⁻¹ = (1 + B (μ - A B)⁻¹ A) / μ`
whenever `μ - A B` is invertible, and `isUnit_smul_sub_comp_comm` is its qualitative form.  With
`A = P` and `B = K` it ties the projection equations to the equations satisfied by Sloan's
**iterated projection solution** `iterated μ K f uₙ = (f + K uₙ) / μ`, whose error equation
`iterated_error_eq` carries an extra factor `1 - P` inside `K` — the source of Sloan
superconvergence.

## Collectively compact approximation

This is Anselone's theory[^anselone].  `exists_equiv_of_isCompactOperator` is **Anselone's
perturbation theorem**: a compact `S` with
`‖(μ - T)⁻¹‖ ‖(T - S) S‖ < ‖μ‖` inherits the invertibility of `μ - T`, with an explicit bound on
`‖(μ - S)⁻¹‖`.  The hypothesis is on `(T - S) S` and not on `T - S`, which is what makes the
theorem apply to quadrature approximations of an integral operator, where `‖T - S‖` does not tend
to zero while `‖(T - Sₙ) Sₙ‖` does (`IsCollectivelyCompact.tendsto_opNorm_sub_comp`).  Compactness
enters only through the Fredholm alternative, which promotes the injectivity of `μ - S` — all that
the geometric series delivers — to invertibility.  `norm_sub_le` is the companion error estimate,
controlled by the consistency error `‖T u - S u‖` at the exact solution.

## The two-grid iteration

`twoGridStep` is one step of residual correction for `(μ - Kₙ) u = f` in which the residual is
corrected with the *coarse* inverse `(μ - Kₘ)⁻¹`, the only inverse ever formed.  Its error is
multiplied at each step by `twoGridOperator`, that is by `(μ - Kₘ)⁻¹ (Kₙ - Kₘ) Kₙ / μ`
(`twoGrid_error_eq`), so the iteration converges geometrically as soon as that operator is a
contraction (`tendsto_twoGridIterate`).  The factor `(Kₙ - Kₘ) Kₙ` is again of the shape that
collective compactness makes small, so for such a family the contraction hypothesis holds once
both indices are large (`eventually_norm_twoGridOperator_lt_one`).

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.  Section 12.1.3 for the projection method,
  Section 12.3 for Jacobson's identity and the iterated projection solution, Section 12.4.3 for
  Anselone's theorem and Section 12.6.2 for the two-grid iteration.
[^anselone]: Philip M. Anselone, *Collectively Compact Operator Approximation Theory and
  Applications to Integral Equations*, Prentice-Hall, 1971.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
  Chapter 12 for projection methods for equations of the second kind.
-/

open Filter Topology

namespace SecondKind

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### Projection methods -/

/-- **The error equation of a projection method** for an equation of the second kind: if
`(μ - K) u = f` and `uₙ` solves the projected equation `P ((μ - K) uₙ) = P f` inside the range of
the idempotent `P`, then `(μ - P K) (u - uₙ) = μ (u - P u)`.

Nothing but linearity is used — no boundedness of `K`, no invertibility, no compactness — and both
bounds of `norm_smul_sub_le_of_projection` and `norm_sub_le_of_projection` are read off it.
Atkinson–Han[^atkinson-han] (12.1.27). -/
theorem sub_projection_eq {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - P ∘L K : X →L[𝕜] X) (u - un) = μ • (u - P u) := by
  have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP hun
  have h2 : μ • un - P (K un) = μ • P u - P (K u) := by
    have h := hun.2
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self, map_sub,
      map_smul, hPun] at h
    rw [h, ← hu]
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
  have hlhs : (μ • 1 - P ∘L K : X →L[𝕜] X) (u - un)
      = (μ • u - μ • P u) - ((μ • un - P (K un)) - (μ • P u - P (K u))) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hlhs, h2, sub_self, sub_zero, ← smul_sub]

/-- **Stability of a projection method** for an equation of the second kind: if `μ - K` is
invertible and `‖(μ - K)⁻¹‖ ‖K - P K‖ < 1`, then `μ - P K` is invertible as well, with
`‖(μ - P K)⁻¹‖ ≤ ‖(μ - K)⁻¹‖ / (1 - ‖(μ - K)⁻¹‖ ‖K - P K‖)`.

This is the geometric series applied to `μ - P K = (μ - K) + (K - P K)`; for a compact `K` and
projections converging pointwise to the identity the hypothesis holds for all large `n`, by
`tendsto_opNorm_comp_of_isCompactOperator`.  Atkinson–Han[^atkinson-han] Theorem 12.1.2. -/
theorem exists_equiv_of_projection [CompleteSpace X] {μ : 𝕜} {K P : X →L[𝕜] X} (e : X ≃L[𝕜] X)
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖ < 1) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ / (1 - ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖) := by
  obtain ⟨e', he'coe, he'norm, -⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add e (K - P ∘L K) h
  exact ⟨e', by rw [he'coe, he]; abel, he'norm⟩

/-- The lower half of the two-sided estimate for a projection method: the approximation error
`‖u - P u‖` is at most a multiple of the method's error `‖u - uₙ‖`, so the method can converge no
faster than the trial space approximates the solution.  Atkinson–Han[^atkinson-han] (12.1.24). -/
theorem norm_smul_sub_le_of_projection {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f u un : X} (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    ‖μ‖ * ‖u - P u‖ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ := by
  have hkey := sub_projection_eq hP hu hun
  calc ‖μ‖ * ‖u - P u‖ = ‖μ • (u - P u)‖ := (norm_smul μ (u - P u)).symm
    _ = ‖(μ • 1 - P ∘L K : X →L[𝕜] X) (u - un)‖ := by rw [hkey]
    _ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ := ContinuousLinearMap.le_opNorm _ _

/-- The upper half of the two-sided estimate for a projection method: the error is at most
`‖μ‖ ‖(μ - P K)⁻¹‖` times the approximation error `‖u - P u‖`.

Together with `norm_smul_sub_le_of_projection` and the uniform bound on `‖(μ - P K)⁻¹‖` of
`exists_equiv_of_projection`, this says that `‖u - uₙ‖` and `‖u - Pₙ u‖` tend to zero at exactly
the same rate, which is the complete convergence analysis of collocation and Galerkin methods for
equations of the second kind.  Atkinson–Han[^atkinson-han] Theorem 12.1.2, (12.1.24). -/
theorem norm_sub_le_of_projection {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {e' : X ≃L[𝕜] X} (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    ‖u - un‖ ≤ ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ := by
  have hkey := sub_projection_eq hP hu hun
  have h1 : u - un = e'.symm (μ • (u - P u)) := by
    rw [← hkey, ← he', ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [h1]
  calc ‖e'.symm (μ • (u - P u))‖ ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖μ • (u - P u)‖ :=
        ContinuousLinearMap.le_opNorm (e'.symm : X →L[𝕜] X) (μ • (u - P u))
    _ = ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ := by rw [norm_smul]; ring

/-! ### Jacobson's identity -/

/-- Composition of operators of a space into itself is the multiplication of its endomorphism
ring.  The two spellings are definitionally equal; this moves between them where ring lemmas are
wanted. -/
private theorem comp_eq_mul (C D : X →L[𝕜] X) : C ∘L D = C * D := rfl

/-- **Jacobson's identity**, Atkinson–Han[^atkinson-han] Lemma 12.3.1: for bounded operators `A`,
`B` on a Banach space and a nonzero `μ`, an inverse of `μ - A B` produces one of `μ - B A`, namely
`(μ - B A)⁻¹ = (1 + B (μ - A B)⁻¹ A) / μ`.

With `A = P` and `B = K` it says that the projection equations `(μ - P K) uₙ = P f` and the
equations `(μ - K P) ûₙ = f` of the iterated projection solution are solvable together, and the
formula bounds each inverse in terms of the other, which is what makes the iterated projection
method analysable at all. -/
theorem exists_equiv_smul_sub_comp_comm {μ : 𝕜} (hμ : μ ≠ 0) {A B : X →L[𝕜] X} (e : X ≃L[𝕜] X)
    (he : (e : X →L[𝕜] X) = μ • 1 - A ∘L B) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - B ∘L A ∧
      (e'.symm : X →L[𝕜] X) = μ⁻¹ • (1 + B ∘L ((e.symm : X →L[𝕜] X) ∘L A)) := by
  simp only [comp_eq_mul] at he ⊢
  obtain ⟨R, hR⟩ : ∃ R : X →L[𝕜] X, (e.symm : X →L[𝕜] X) = R := ⟨_, rfl⟩
  rw [hR]
  have hRr : ((μ • 1 : X →L[𝕜] X) - A * B) * R = 1 := by
    rw [← hR, ← he]; ext x; simp
  have hRl : R * ((μ • 1 : X →L[𝕜] X) - A * B) = 1 := by
    rw [← hR, ← he]; ext x; simp
  -- `μ - B A` intertwines with `μ - A B` through `A` and through `B`
  have hBl : ((μ • 1 : X →L[𝕜] X) - B * A) * B = B * ((μ • 1 : X →L[𝕜] X) - A * B) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  have hAr : A * ((μ • 1 : X →L[𝕜] X) - B * A) = ((μ • 1 : X →L[𝕜] X) - A * B) * A := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  have hcancelR : ((μ • 1 : X →L[𝕜] X) - A * B) * (R * A) = A := by
    rw [← mul_assoc, hRr, one_mul]
  have hcancelL : R * (((μ • 1 : X →L[𝕜] X) - A * B) * A) = A := by
    rw [← mul_assoc, hRl, one_mul]
  have hGF : ((μ • 1 : X →L[𝕜] X) - B * A) * (μ⁻¹ • (1 + B * (R * A))) = 1 := by
    have hstep : ((μ • 1 : X →L[𝕜] X) - B * A) * (1 + B * (R * A)) = μ • 1 := by
      calc ((μ • 1 : X →L[𝕜] X) - B * A) * (1 + B * (R * A))
          = ((μ • 1 : X →L[𝕜] X) - B * A)
            + (((μ • 1 : X →L[𝕜] X) - B * A) * B) * (R * A) := by
            rw [mul_add, mul_one, ← mul_assoc]
        _ = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * (((μ • 1 : X →L[𝕜] X) - A * B) * (R * A)) := by rw [hBl, mul_assoc]
        _ = μ • 1 := by rw [hcancelR]; abel
    rw [mul_smul_comm, hstep, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hFG : (μ⁻¹ • (1 + B * (R * A))) * ((μ • 1 : X →L[𝕜] X) - B * A) = 1 := by
    have hstep : (1 + B * (R * A)) * ((μ • 1 : X →L[𝕜] X) - B * A) = μ • 1 := by
      calc (1 + B * (R * A)) * ((μ • 1 : X →L[𝕜] X) - B * A)
          = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * ((R * A) * ((μ • 1 : X →L[𝕜] X) - B * A)) := by
            rw [add_mul, one_mul, mul_assoc]
        _ = ((μ • 1 : X →L[𝕜] X) - B * A)
            + B * (R * (((μ • 1 : X →L[𝕜] X) - A * B) * A)) := by rw [mul_assoc, hAr]
        _ = μ • 1 := by rw [hcancelL]; abel
    rw [smul_mul_assoc, hstep, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  exact ⟨ContinuousLinearEquiv.ofUnit ⟨_, _, hGF, hFG⟩, rfl, by ext x; rfl⟩

/-- **Jacobson's identity** as an equivalence: `μ - A B` is invertible if and only if `μ - B A`
is.  Atkinson–Han[^atkinson-han] Lemma 12.3.1. -/
theorem isUnit_smul_sub_comp_comm {μ : 𝕜} (hμ : μ ≠ 0) (A B : X →L[𝕜] X) :
    IsUnit (μ • 1 - A ∘L B : X →L[𝕜] X) ↔ IsUnit (μ • 1 - B ∘L A : X →L[𝕜] X) := by
  have key : ∀ C D : X →L[𝕜] X, IsUnit (μ • 1 - C ∘L D : X →L[𝕜] X) →
      IsUnit (μ • 1 - D ∘L C : X →L[𝕜] X) := by
    intro C D hCD
    obtain ⟨u, hu⟩ := hCD
    obtain ⟨e', he', -⟩ :=
      exists_equiv_smul_sub_comp_comm hμ (ContinuousLinearEquiv.ofUnit u) hu
    exact ⟨ContinuousLinearEquiv.toUnit e', he'⟩
  exact ⟨key A B, key B A⟩

/-! ### The iterated projection solution -/

/-- **Sloan's iterated projection solution** `ûₙ = (f + K uₙ) / μ` of the equation `(μ - K) u = f`:
one fixed-point sweep applied to the projection solution `uₙ`, which improves on it whatever the
size of `‖K‖`.  Atkinson–Han[^atkinson-han] (12.3.1). -/
def iterated (μ : 𝕜) (K : X →L[𝕜] X) (f un : X) : X := μ⁻¹ • (f + K un)

/-- The iterated solution projects back onto the projection solution, `P ûₙ = uₙ`.
Atkinson–Han[^atkinson-han] (12.3.2). -/
theorem apply_iterated {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {f un : X}
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    P (iterated μ K f un) = un := by
  have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP hun
  have h := hun.2
  simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply, one_apply_eq_self, map_sub,
    map_smul, hPun] at h
  simp only [iterated, map_smul, map_add, ← h]
  rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- The iterated solution solves the equation `(μ - K P) ûₙ = f`, which is Jacobson's companion of
the projection equations.  Atkinson–Han[^atkinson-han] (12.3.3). -/
theorem smul_sub_comp_iterated {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (iterated μ K f un) = f := by
  have hPit : P (iterated μ K f un) = un := apply_iterated hμ hP hun
  simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, hPit]
  simp only [iterated, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  abel

/-- **The error equation of the iterated projection solution**,
`(μ - K P) (u - ûₙ) = K (1 - P) u`.

The right-hand side carries an extra factor `1 - P` inside `K`, which is the source of Sloan
superconvergence: the error is bounded by `‖K ∘ (1 - P)‖ ‖u - P u‖`, one power of the
approximation error better than `‖u - uₙ‖`.  Atkinson–Han[^atkinson-han] (12.3.11). -/
theorem iterated_error_eq {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f u un : X} (hu : (μ • 1 - K : X →L[𝕜] X) u = f)
    (hun : IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un) :
    (μ • 1 - K ∘L P : X →L[𝕜] X) (u - iterated μ K f un) = K (u - P u) := by
  have h1 : (μ • 1 - K ∘L P : X →L[𝕜] X) (iterated μ K f un) = f :=
    smul_sub_comp_iterated hμ hP hun
  rw [map_sub, h1, ← hu]
  simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub]
  abel

/-! ### Anselone's perturbation theorem -/

/-- **Anselone's perturbation theorem**, Atkinson–Han[^atkinson-han] Theorem 12.4.3: let `S` and
`T` be bounded operators on a Banach space with `S` compact, let `μ ≠ 0` be such that `μ - T` is
invertible, and assume `‖(μ - T)⁻¹‖ ‖(T - S) S‖ < ‖μ‖`.  Then `μ - S` is invertible and

`‖(μ - S)⁻¹‖ ≤ (1 + ‖(μ - T)⁻¹‖ ‖S‖) / (‖μ‖ - ‖(μ - T)⁻¹‖ ‖(T - S) S‖)`.

The hypothesis constrains `(T - S) S` and not `T - S`, which is why the theorem applies to
quadrature approximations of an integral operator, where `‖T - S‖` does not tend to zero; for a
collectively compact pointwise convergent family `‖(T - Sₙ) Sₙ‖ → 0` holds by
`IsCollectivelyCompact.tendsto_opNorm_sub_comp`.

The candidate inverse `(1 + (μ - T)⁻¹ S) / μ` satisfies
`(1 + (μ - T)⁻¹ S) (μ - S) / μ = 1 + (μ - T)⁻¹ (T - S) S / μ`, whose right-hand side is a unit by
the geometric series; that makes `μ - S` injective, and compactness of `S` is used **only** to
promote injectivity to invertibility through the Fredholm alternative. -/
theorem exists_equiv_of_isCompactOperator [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    {S T : X →L[𝕜] X} (hS : IsCompactOperator S) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - T)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖ < ‖μ‖) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - S ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖S‖) /
        (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖) := by
  have hcs : ((T - S) ∘L S : X →L[𝕜] X) = (T - S) * S := rfl
  rw [hcs] at h ⊢
  obtain ⟨R, hR⟩ : ∃ R : X →L[𝕜] X, (e.symm : X →L[𝕜] X) = R := ⟨_, rfl⟩
  rw [hR] at h ⊢
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  have hμ0 : ‖μ‖ ≠ 0 := hμpos.ne'
  have hRA : R * ((μ • 1 : X →L[𝕜] X) - T) = 1 := by
    rw [← hR, ← he]; ext x; simp
  -- the small correction term, and the geometric series applied to it
  obtain ⟨t, htdef⟩ : ∃ t : X →L[𝕜] X, t = μ⁻¹ • (R * ((T - S) * S)) := ⟨_, rfl⟩
  have htnorm : ‖μ‖ * ‖t‖ ≤ ‖R‖ * ‖(T - S) * S‖ := by
    rw [htdef, norm_smul, norm_inv, ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
    exact norm_mul_le _ _
  have htlt : ‖t‖ < 1 := by
    have h1 : ‖μ‖ * ‖t‖ < ‖μ‖ * 1 := by rw [mul_one]; linarith
    exact lt_of_mul_lt_mul_left h1 hμpos.le
  obtain ⟨w, hw⟩ : IsUnit ((1 : X →L[𝕜] X) + t) := by
    have hu := isUnit_one_sub_of_norm_lt_one (x := -t) (by rwa [norm_neg])
    rwa [sub_neg_eq_add] at hu
  have hwinv : (↑w⁻¹ : X →L[𝕜] X) * ((1 : X →L[𝕜] X) + t) = 1 := by
    rw [← hw]; exact w.inv_mul
  have hwnorm : ‖(↑w⁻¹ : X →L[𝕜] X)‖ ≤ 1 + ‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖t‖ := by
    have hid : (↑w⁻¹ : X →L[𝕜] X) = 1 - (↑w⁻¹ : X →L[𝕜] X) * t := by
      rw [← hwinv, mul_add, mul_one]; abel
    calc ‖(↑w⁻¹ : X →L[𝕜] X)‖ = ‖(1 : X →L[𝕜] X) - (↑w⁻¹ : X →L[𝕜] X) * t‖ := by rw [← hid]
      _ ≤ ‖(1 : X →L[𝕜] X)‖ + ‖(↑w⁻¹ : X →L[𝕜] X) * t‖ := norm_sub_le _ _
      _ ≤ 1 + ‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖t‖ :=
          add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _)
  -- the factorisation `(1 + R S) (μ - S) = μ + R (T - S) S`, which rests on `S (μ - S) = (μ - S) S`
  have hcomm : S * ((μ • 1 : X →L[𝕜] X) - S) = ((μ • 1 : X →L[𝕜] X) - S) * S := by
    rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hTS : (T - S : X →L[𝕜] X) = ((μ • 1 : X →L[𝕜] X) - S) - ((μ • 1 : X →L[𝕜] X) - T) := by
    abel
  have h1 : R * (T - S : X →L[𝕜] X) = R * ((μ • 1 : X →L[𝕜] X) - S) - 1 := by
    rw [hTS, mul_sub, hRA]
  have h2 : (R * ((μ • 1 : X →L[𝕜] X) - S) - 1) * S
      = R * (((μ • 1 : X →L[𝕜] X) - S) * S) - S := by
    rw [sub_mul, one_mul, mul_assoc]
  have hprod : ((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)
      = μ • 1 + R * ((T - S) * S) := by
    calc ((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)
        = ((μ • 1 : X →L[𝕜] X) - S) + R * (S * ((μ • 1 : X →L[𝕜] X) - S)) := by
          rw [add_mul, one_mul, mul_assoc]
      _ = ((μ • 1 : X →L[𝕜] X) - S) + R * (((μ • 1 : X →L[𝕜] X) - S) * S) := by rw [hcomm]
      _ = ((μ • 1 : X →L[𝕜] X) - S) + (R * ((μ • 1 : X →L[𝕜] X) - S) - 1) * S + S := by
          rw [h2]; abel
      _ = μ • 1 + R * ((T - S) * S) := by rw [← h1, mul_assoc]; abel
  have hprod' : μ⁻¹ • (((1 : X →L[𝕜] X) + R * S) * ((μ • 1 : X →L[𝕜] X) - S)) = 1 + t := by
    rw [hprod, htdef, smul_add, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  -- hence `μ - S` has a left inverse, so it is injective
  obtain ⟨V, hVdef⟩ : ∃ V : X →L[𝕜] X, V = μ⁻¹ • ((↑w⁻¹ : X →L[𝕜] X) * (1 + R * S)) := ⟨_, rfl⟩
  have hV : V * ((μ • 1 : X →L[𝕜] X) - S) = 1 := by
    rw [hVdef, smul_mul_assoc, mul_assoc, ← mul_smul_comm, hprod', hwinv]
  have hVx : ∀ x : X, V ((μ • 1 - S : X →L[𝕜] X) x) = x := by
    intro x
    have hx := congrArg (fun Z : X →L[𝕜] X => Z x) hV
    simpa using hx
  have hinj : Function.Injective (μ • 1 - S : X →L[𝕜] X) := by
    intro x y hxy
    rw [← hVx x, ← hVx y, hxy]
  -- and the Fredholm alternative for the compact `S` promotes injectivity to invertibility
  have hres : μ ∈ resolventSet 𝕜 S := by
    refine (IsCompactOperator.hasEigenvalue_or_mem_resolventSet hS hμ).resolve_left ?_
    intro hev
    obtain ⟨x, hx, hx0⟩ := hev.exists_hasEigenvector
    refine hx0 (hinj ?_)
    have hSx : S x = μ • x := Module.End.mem_eigenspace_iff.1 hx
    simp [hSx]
  have hunitS : IsUnit ((μ • 1 : X →L[𝕜] X) - S) := by
    have h' : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) μ - S) := hres
    rwa [Algebra.algebraMap_eq_smul_one] at h'
  obtain ⟨uS, huS⟩ := hunitS
  have hVinv : V = (↑uS⁻¹ : X →L[𝕜] X) := by
    calc V = V * ((uS : X →L[𝕜] X) * (↑uS⁻¹ : X →L[𝕜] X)) := by rw [uS.mul_inv, mul_one]
      _ = (V * ((μ • 1 : X →L[𝕜] X) - S)) * (↑uS⁻¹ : X →L[𝕜] X) := by rw [huS, mul_assoc]
      _ = (↑uS⁻¹ : X →L[𝕜] X) := by rw [hV, one_mul]
  refine ⟨ContinuousLinearEquiv.ofUnit uS, huS, ?_⟩
  have hsymm : ((ContinuousLinearEquiv.ofUnit uS).symm : X →L[𝕜] X) = V := by
    rw [hVinv]; ext x; rfl
  rw [hsymm]
  -- the bound on the inverse
  have hnq : 0 < ‖μ‖ - ‖R‖ * ‖(T - S) * S‖ := by linarith
  have hone : ‖(1 : X →L[𝕜] X) + R * S‖ ≤ 1 + ‖R‖ * ‖S‖ :=
    (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _))
  have hVle : ‖V‖ ≤ ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖) := by
    calc ‖V‖ = ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X) * ((1 : X →L[𝕜] X) + R * S)‖ := by
          rw [hVdef, norm_smul, norm_inv]
      _ ≤ ‖μ‖⁻¹ * (‖(↑w⁻¹ : X →L[𝕜] X)‖ * ‖(1 : X →L[𝕜] X) + R * S‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
      _ ≤ ‖μ‖⁻¹ * (‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hone (norm_nonneg _))
            (by positivity)
      _ = ‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖) := by ring
  have hwq : ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖) ≤ ‖μ‖ := by
    nlinarith [mul_le_mul_of_nonneg_left htnorm (norm_nonneg (↑w⁻¹ : X →L[𝕜] X)),
      mul_le_mul_of_nonneg_left hwnorm hμpos.le, norm_nonneg (↑w⁻¹ : X →L[𝕜] X)]
  rw [le_div_iff₀ hnq]
  calc ‖V‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖)
      ≤ (‖μ‖⁻¹ * ‖(↑w⁻¹ : X →L[𝕜] X)‖ * (1 + ‖R‖ * ‖S‖)) *
          (‖μ‖ - ‖R‖ * ‖(T - S) * S‖) := mul_le_mul_of_nonneg_right hVle hnq.le
    _ = (‖μ‖⁻¹ * (1 + ‖R‖ * ‖S‖)) *
          (‖(↑w⁻¹ : X →L[𝕜] X)‖ * (‖μ‖ - ‖R‖ * ‖(T - S) * S‖)) := by ring
    _ ≤ (‖μ‖⁻¹ * (1 + ‖R‖ * ‖S‖)) * ‖μ‖ := mul_le_mul_of_nonneg_left hwq (by positivity)
    _ = 1 + ‖R‖ * ‖S‖ := by field_simp

/-- **Consistency at the exact solution controls the error**: if `(μ - T) u = f` and `(μ - S) z = f`
with `μ - S` invertible, then `‖u - z‖ ≤ ‖(μ - S)⁻¹‖ ‖T u - S u‖`.

The right-hand side is the consistency error *at the exact solution* rather than an operator norm,
which together with the uniform bound of `exists_equiv_of_isCompactOperator` is the complete
convergence analysis of the Nyström method.  Atkinson–Han[^atkinson-han] (12.4.24). -/
theorem norm_sub_le {μ : 𝕜} {S T : X →L[𝕜] X} {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - S) {f u z : X} (hu : (μ • 1 - T : X →L[𝕜] X) u = f)
    (hz : (μ • 1 - S : X →L[𝕜] X) z = f) :
    ‖u - z‖ ≤ ‖(e.symm : X →L[𝕜] X)‖ * ‖T u - S u‖ := by
  have h : (μ • 1 - T : X →L[𝕜] X) u = e z := by
    rw [hu, ← hz, ← he, ContinuousLinearEquiv.coe_coe]
  have hbound := ContinuousLinearEquiv.norm_sub_le_of_apply_eq (μ • 1 - T : X →L[𝕜] X) e h
  have heq : ((μ • 1 - T : X →L[𝕜] X) - (e : X →L[𝕜] X)) u = S u - T u := by
    rw [he]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  rwa [heq, norm_sub_rev (S u) (T u)] at hbound

/-! ### The two-grid iteration -/

/-- The residual `f - (μ - K) u` of the equation `(μ - K) u = f` at the approximation `u`. -/
def residual (μ : 𝕜) (K : X →L[𝕜] X) (f u : X) : X := f - (μ • 1 - K : X →L[𝕜] X) u

/-- **The two-grid residual correction step** for the fine equation `(μ - Kₙ) u = f`,
Atkinson–Han[^atkinson-han] (12.6.20)–(12.6.22): the residual `r = f - (μ - Kₙ) u` is corrected by
`u ↦ u + (r + (μ - Kₘ)⁻¹ (Kₙ r)) / μ`, where `e` is the *coarse* equivalence, `↑e = μ - Kₘ`.  The
coarse inverse plays the role of the approximate inverse of a residual correction method, and is
the only inverse that is ever formed. -/
def twoGridStep (μ : 𝕜) (e : X ≃L[𝕜] X) (Kn : X →L[𝕜] X) (f u : X) : X :=
  u + μ⁻¹ • (residual μ Kn f u + e.symm (Kn (residual μ Kn f u)))

/-- The operator by which the error of `twoGridStep` is multiplied at each step,
`(μ - Kₘ)⁻¹ (Kₙ - Kₘ) Kₙ / μ`, where `e` is the coarse equivalence `↑e = μ - Kₘ`.
Atkinson–Han[^atkinson-han] (12.6.28). -/
def twoGridOperator (μ : 𝕜) (e : X ≃L[𝕜] X) (Km Kn : X →L[𝕜] X) : X →L[𝕜] X :=
  μ⁻¹ • ((e.symm : X →L[𝕜] X) ∘L ((Kn - Km) ∘L Kn))

/-- **The error equation of the two-grid iteration**, Atkinson–Han[^atkinson-han]
(12.6.27)–(12.6.28): one step multiplies the error by `twoGridOperator`.  The factor `Kₙ - Kₘ`
appears composed with `Kₙ`, which is the shape that collective compactness makes small. -/
theorem twoGrid_error_eq {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u : X) :
    ustar - twoGridStep μ e Kn f u = twoGridOperator μ e Km Kn (ustar - u) := by
  have hKmeq : Km = μ • 1 - (e : X →L[𝕜] X) := by rw [he]; abel
  have hKm : ∀ y : X, e.symm (Km y) = μ • e.symm y - y := by
    intro y
    rw [hKmeq]
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearEquiv.coe_coe, map_sub,
      map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hr : residual μ Kn f u = (μ • 1 - Kn : X →L[𝕜] X) (ustar - u) := by
    rw [residual, ← hstar, map_sub]
  have hkey : residual μ Kn f u + e.symm (Kn (residual μ Kn f u))
      = μ • (ustar - u) - e.symm ((Kn - Km) (Kn (ustar - u))) := by
    rw [hr]
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, hKm]
    module
  simp only [twoGridStep, twoGridOperator, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [hkey, smul_sub, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  abel

/-- The geometric error bound for the two-grid iteration. -/
theorem norm_sub_twoGridStep_iterate_le {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u₀ : X) (k : ℕ) :
    ‖ustar - (twoGridStep μ e Kn f)^[k] u₀‖ ≤
      ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', twoGrid_error_eq hμ he hstar]
    calc ‖twoGridOperator μ e Km Kn (ustar - (twoGridStep μ e Kn f)^[k] u₀)‖
        ≤ ‖twoGridOperator μ e Km Kn‖ * ‖ustar - (twoGridStep μ e Kn f)^[k] u₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖twoGridOperator μ e Km Kn‖ * (‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖) :=
          mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      _ = ‖twoGridOperator μ e Km Kn‖ ^ (k + 1) * ‖ustar - u₀‖ := by ring

/-- **Convergence of the two-grid iteration**, Atkinson–Han[^atkinson-han] Theorem 12.6.1: as soon
as the error operator `twoGridOperator` is a contraction, the two-grid iterates converge to the
solution of the fine equation, geometrically and from every starting point.

For a collectively compact pointwise convergent family the contraction hypothesis holds once both
indices are large enough, which is `eventually_norm_twoGridOperator_lt_one`. -/
theorem tendsto_twoGridIterate {μ : 𝕜} (hμ : μ ≠ 0) {e : X ≃L[𝕜] X} {Km Kn : X →L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - Km) (hM : ‖twoGridOperator μ e Km Kn‖ < 1) {f ustar : X}
    (hstar : (μ • 1 - Kn : X →L[𝕜] X) ustar = f) (u₀ : X) :
    Tendsto (fun k => (twoGridStep μ e Kn f)^[k] u₀) atTop (𝓝 ustar) := by
  have hlim : Tendsto (fun k => ‖twoGridOperator μ e Km Kn‖ ^ k * ‖ustar - u₀‖) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hM).mul_const ‖ustar - u₀‖
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun k => ?_) hlim
  rw [norm_sub_rev]
  exact norm_sub_twoGridStep_iterate_le hμ he hstar u₀ k

/-! ### A collective compactness estimate that belongs upstream -/

/-- A uniform bound on a ball around the origin bounds the operator norm.  The factor `‖c‖` is
unavoidable over a general nontrivially normed field, where the norm need not take the value `1`.

This repeats a private helper of `Numlib.Analysis.Normed.Operator.CollectivelyCompact`, and should
disappear when `eventually_forall_opNorm_sub_comp_lt` moves there. -/
private theorem opNorm_le_of_forall_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {F : X →L[𝕜] X} {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hb : ∀ x : X, ‖x‖ < r → ‖F x‖ ≤ C) : ‖F‖ ≤ ‖c‖ / r * C := by
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  refine ContinuousLinearMap.opNorm_le_of_shell hr (by positivity) hc fun x hx _ => ?_
  refine (hb x ‹_›).trans ?_
  calc C = ‖c‖ / r * C * (r / ‖c‖) := by field_simp
    _ ≤ ‖c‖ / r * C * ‖x‖ := mul_le_mul_of_nonneg_left hx (by positivity)

/-- `a / b ≤ c / d` from `a ≤ c` and `0 < d ≤ b`. -/
private theorem div_le_div_aux {a b c d : ℝ} (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d)
    (hdb : d ≤ b) : a / b ≤ c / d := by gcongr

/-- **Uniform smallness of `(L - Kₘ) Kₙ` in the fine index**: for a collectively compact family
converging pointwise to `L`, the norm `‖(L - Kₘ) ∘ Kₙ‖` is eventually below any given `ε > 0` for
*every* `n` at once, and not only along the diagonal `n = m`.

This is `IsCollectivelyCompact.tendsto_opNorm_sub_comp` with the two indices separated, and the
proof is that lemma's: the convergence `Kₘ → L` is uniform on the compact set that contains the
image of one ball under *every* member of the family, so the index of that member is free.  The
statement belongs in `Numlib.Analysis.Normed.Operator.CollectivelyCompact` beside its companion
and lives here only because this module does not own that file. -/
theorem eventually_forall_opNorm_sub_comp_lt [CompleteSpace X] {K : ℕ → X →L[𝕜] X}
    {L : X →L[𝕜] X} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ n, ‖(L - K m) ∘L K n‖ < ε := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : (0 : ℝ) < ‖c‖ := lt_trans one_pos hc
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hunif : TendstoUniformlyOn (fun n => (K n : X → X)) L atTop
      (closure (⋃ i, K i '' U)) := tendstoUniformlyOn_of_tendsto_of_isCompact hL hcpt
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε * r / (2 * ‖c‖)) (by positivity))
  filter_upwards [eventually_ge_atTop N] with m hm n
  have hbound : ∀ x : X, ‖x‖ < r → ‖((L - K m) ∘L K n) x‖ ≤ ε * r / (2 * ‖c‖) := by
    intro x hx
    have hmem : K n x ∈ closure (⋃ i, K i '' U) :=
      subset_closure (Set.mem_iUnion.2 ⟨n, ⟨x, hrU (mem_ball_zero_iff.2 hx), rfl⟩⟩)
    have hd := hN m hm (K n x) hmem
    rw [dist_eq_norm] at hd
    simpa using hd.le
  refine lt_of_le_of_lt (opNorm_le_of_forall_norm_lt hc hr (by positivity) hbound) ?_
  have heq : ‖c‖ / r * (ε * r / (2 * ‖c‖)) = ε / 2 := by field_simp
  rw [heq]
  linarith

/-- **The two-grid iteration is eventually a contraction**, Atkinson–Han[^atkinson-han]
Theorem 12.6.1: for a collectively compact family `Kₚ` converging pointwise to `L` with `μ - L`
invertible, every sufficiently large coarse index `m` makes the coarse operator `μ - Kₘ`
invertible and makes `twoGridOperator` a contraction for *every* fine index `n ≥ m`.  With
`tendsto_twoGridIterate` this is the convergence of the two-grid method.

The uniform bound on the coarse inverses is `exists_equiv_of_isCompactOperator` together with
`IsCollectivelyCompact.exists_opNorm_le`; the smallness of `(Kₙ - Kₘ) Kₙ` splits into the diagonal
part `(Kₙ - L) Kₙ`, which is `IsCollectivelyCompact.tendsto_opNorm_sub_comp` and needs `n` large,
and the part `(L - Kₘ) Kₙ`, which has to be small uniformly in `n` and is
`eventually_forall_opNorm_sub_comp_lt`.  Both indices therefore have to be large, which is why the
conclusion quantifies over `n ≥ m`. -/
theorem eventually_norm_twoGridOperator_lt_one [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0)
    {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X} (hK : IsCollectivelyCompact K)
    (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∀ᶠ m in atTop, ∃ em : X ≃L[𝕜] X, (em : X →L[𝕜] X) = μ • 1 - K m ∧
      ∀ n ≥ m, ‖twoGridOperator μ em (K m) (K n)‖ < 1 := by
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  obtain ⟨C, hC⟩ := IsCollectivelyCompact.exists_opNorm_le hK
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ‖(e.symm : X →L[𝕜] X)‖ = A := ⟨_, rfl⟩
  have hA0 : (0 : ℝ) ≤ A := hA ▸ norm_nonneg _
  have hnum0 : (0 : ℝ) ≤ 1 + A * C := by linarith [mul_nonneg hA0 hC0]
  have hhalf : (0 : ℝ) < ‖μ‖ / 2 := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, (1 + A * C) / (‖μ‖ / 2) = B := ⟨_, rfl⟩
  have hB0 : (0 : ℝ) ≤ B := hB ▸ div_nonneg hnum0 hhalf.le
  have hk0 : (0 : ℝ) ≤ 2 * ‖μ‖⁻¹ * B := mul_nonneg (by positivity) hB0
  obtain ⟨ε, hεpos, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ 2 * ‖μ‖⁻¹ * B * ε < 1 := by
    refine ⟨1 / (2 * ‖μ‖⁻¹ * B + 1), div_pos one_pos (by linarith), ?_⟩
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  have hq : Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) :=
    IsCollectivelyCompact.tendsto_opNorm_sub_comp hK hL
  obtain ⟨Nc, hNc⟩ := eventually_atTop.1 (hq.eventually (eventually_lt_nhds hεpos))
  have hansel : ∀ᶠ m in atTop, A * ‖(L - K m) ∘L K m‖ < ‖μ‖ / 2 := by
    have h0 : Tendsto (fun n => A * ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
      simpa using hq.const_mul A
    exact h0.eventually (eventually_lt_nhds hhalf)
  filter_upwards [hansel, eventually_forall_opNorm_sub_comp_lt hK hL hεpos,
    eventually_ge_atTop Nc] with m hma hmb hmc
  obtain ⟨em, hem, hemnorm⟩ :=
    exists_equiv_of_isCompactOperator hμ (IsCollectivelyCompact.isCompactOperator hK m) he
      (by rw [hA]; linarith)
  have hemB : ‖(em.symm : X →L[𝕜] X)‖ ≤ B := by
    refine hemnorm.trans ?_
    rw [hA, ← hB]
    exact div_le_div_aux hnum0 (by linarith [mul_le_mul_of_nonneg_left (hC m) hA0]) hhalf
      (by linarith)
  refine ⟨em, hem, fun n hn => ?_⟩
  have hsplit : ‖((K n - K m) ∘L K n : X →L[𝕜] X)‖ ≤ 2 * ε := by
    have hid : ((K n - K m) ∘L K n : X →L[𝕜] X) = (K n - L) ∘L K n + (L - K m) ∘L K n := by
      ext x
      simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply]
      abel
    have hneg : ((K n - L) ∘L K n : X →L[𝕜] X) = -((L - K n) ∘L K n) := by
      ext x
      simp only [neg_apply, ContinuousLinearMap.comp_apply, sub_apply]
      abel
    have h1 : ‖((K n - L) ∘L K n : X →L[𝕜] X)‖ ≤ ε := by
      rw [hneg, norm_neg]
      exact (hNc n (le_trans hmc hn)).le
    have h2 : ‖((L - K m) ∘L K n : X →L[𝕜] X)‖ ≤ ε := (hmb n).le
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  calc ‖twoGridOperator μ em (K m) (K n)‖
      = ‖μ‖⁻¹ * ‖(em.symm : X →L[𝕜] X) ∘L ((K n - K m) ∘L K n)‖ := by
        rw [twoGridOperator, norm_smul, norm_inv]
    _ ≤ ‖μ‖⁻¹ * (‖(em.symm : X →L[𝕜] X)‖ * ‖((K n - K m) ∘L K n : X →L[𝕜] X)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
    _ ≤ ‖μ‖⁻¹ * (B * (2 * ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hemB hsplit (norm_nonneg _) hB0) (by positivity)
    _ = 2 * ‖μ‖⁻¹ * B * ε := by ring
    _ < 1 := hε

end SecondKind
