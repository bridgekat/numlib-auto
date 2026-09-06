import Mathlib.Algebra.Ring.GeomSum
import Numlib.Krylov.Convergence.Polynomial

/-!
# Polynomial preconditioning

A polynomial preconditioner is `M⁻¹ = s(A)` for a low-degree polynomial `s`, so that the
preconditioned operator is `s(A) A` and applying `M⁻¹` costs only matrix–vector products
(Saad, *Iterative Methods for Sparse Linear Systems*[^saad-iterative], §12.3). Two of the three
ingredients are here; the two ways of choosing `s` optimally are
`Numlib/LinearSolve/Preconditioner/Chebyshev` (uniform norm on an enclosing interval) and
`Numlib/RingTheory/Polynomial/KernelPolynomial` (weighted least squares).

Nothing here is analytic.

* The Neumann polynomial `∑_{i ≤ s} (1 - ω X)^i` and the identity behind it are a geometric sum
  in a ring, stated for `1 - m * a` with an arbitrary ring element `m` so that the block-diagonal
  `D` of Saad's general form `M⁻¹ = (∑_{i ≤ s} N^i) D⁻¹`, `N = 1 - ω D⁻¹ A`, costs nothing extra.
  Since `(∑_{i ≤ s} N^i) (m a) = 1 - N^{s+1}`, every bound on the preconditioned operator is a
  bound on `‖N^{s+1}‖`: a Neumann preconditioner is `s + 1` steps of the underlying stationary
  iteration of `Numlib/LinearSolve/Stationary/Basic`.
* The optimality criterion is `Numlib/Krylov/Convergence/Polynomial` read backwards: what a
  polynomial preconditioner controls is `sup_{[α,β]} |1 - t s(t)|`, and that bounds
  `‖x - s(A) (A x)‖` by the compression trick, in any inner product space and with no functional
  calculus.
* The self-adjointness of `s(B) B` in the `D`-inner product is why a nonsymmetric preconditioned
  operator can still be used with CG. It is stated for any `B` that is already `D`-self-adjoint,
  which covers `B = D⁻¹ A` for symmetric `A` and `D` without any inverse appearing
  (`Preconditioner.energyInner_comm_of_comp_eq`).

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Polynomial

namespace Preconditioner

/-! ### Neumann polynomials -/

/-- The truncated Neumann series `∑_{i ≤ s} n ^ i` of a ring element, the shape every Neumann
preconditioner has once the scaling is folded into `n`. -/
def neumannPolyOf {R : Type*} [Ring R] (n : R) (s : ℕ) : R := ∑ i ∈ Finset.range (s + 1), n ^ i

/-- The Neumann polynomial `∑_{i ≤ s} (1 - ω X)^i` of Saad's §12.3.1: the polynomial `p` for
which `p(A)` is the `s`-term truncation of the Neumann series for `(ω A)⁻¹`. -/
noncomputable def neumannPoly {R : Type*} [CommRing R] (ω : R) (s : ℕ) : R[X] :=
  neumannPolyOf (1 - C ω * X) s

/-- Evaluating the Neumann polynomial at an algebra element is the ring-level truncated series. -/
theorem aeval_neumannPoly {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (ω : R) (s : ℕ)
    (a : A) :
    aeval a (neumannPoly ω s) = neumannPolyOf (1 - algebraMap R A ω * a) s := by
  simp [neumannPoly, neumannPolyOf, map_sum]

/-- Saad (12.3): with `n = 1 - m * a` the truncated Neumann series satisfies
`(∑_{i ≤ s} n^i) (m a) = 1 - n^(s+1)` in any ring, so the preconditioned operator `M⁻¹ A` of a
Neumann preconditioner differs from the identity by exactly the `(s+1)`-st power of the iteration
operator of the underlying splitting. -/
theorem neumannPoly_mul_eq {R : Type*} [Ring R] (m a : R) (s : ℕ) :
    neumannPolyOf (1 - m * a) s * (m * a) = 1 - (1 - m * a) ^ (s + 1) := by
  have h : m * a = 1 - (1 - m * a) := (sub_sub_cancel 1 (m * a)).symm
  rw [neumannPolyOf]
  nth_rewrite 2 [h]
  exact geom_sum_mul_neg (1 - m * a) (s + 1)

/-! ### Self-adjointness in the preconditioner's inner product -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Transporting an operator that is self-adjoint for the `D`-inner product to `WithEnergy D hD`
gives a symmetric operator. This is the whole reason `WithEnergy` exists here: the preconditioned
operator is not symmetric for the ambient inner product, and CG only ever needs symmetry for the
one it actually uses. -/
theorem isSymmetric_conj_of_energyInner {D : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    {T : E →ₗ[𝕜] E} (hT : ∀ x y, inner 𝕜 (D (T x)) y = inner 𝕜 (D x) (T y)) :
    ((WithEnergy.equiv D hD).conj T).IsSymmetric := by
  intro x y
  obtain ⟨u, rfl⟩ := (WithEnergy.equiv D hD).surjective x
  obtain ⟨v, rfl⟩ := (WithEnergy.equiv D hD).surjective y
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, WithEnergy.inner_equiv, WithEnergy.inner_equiv]
  exact hT u v

/-- The concrete case: if `D ∘ B = A` with `A` and `D` symmetric — that is, `B = D⁻¹ A`, written
without ever forming an inverse — then `B` is self-adjoint for the `D`-inner product. -/
theorem energyInner_comm_of_comp_eq {D A B : E →ₗ[𝕜] E} (hD : D.IsSymmetric) (hA : A.IsSymmetric)
    (hDB : D ∘ₗ B = A) (x y : E) : inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y) := by
  have h : ∀ z, D (B z) = A z := fun z => congrArg (fun f : E →ₗ[𝕜] E => f z) hDB
  rw [h x, hA x y, ← h y, ← hD x (B y)]

section EnergySelfAdjoint

variable {D B : E →ₗ[𝕜] E}

/-- Powers of a `D`-self-adjoint operator are `D`-self-adjoint. -/
private theorem energyInner_pow_comm
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (n : ℕ) (x y : E) :
    inner 𝕜 (D ((B ^ n) x)) y = inner 𝕜 (D x) ((B ^ n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      calc inner 𝕜 (D ((B ^ (n + 1)) x)) y
          = inner 𝕜 (D ((B ^ n) (B x))) y := by rw [pow_succ, Module.End.mul_apply]
        _ = inner 𝕜 (D (B x)) ((B ^ n) y) := ih (B x) y
        _ = inner 𝕜 (D x) (B ((B ^ n) y)) := hB x ((B ^ n) y)
        _ = inner 𝕜 (D x) ((B ^ (n + 1)) y) := by rw [pow_succ', Module.End.mul_apply]

/-- A real polynomial in a `D`-self-adjoint operator is `D`-self-adjoint. -/
private theorem energyInner_aeval_comm
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (p : ℝ[X]) (x y : E) :
    inner 𝕜 (D (aeval B (p.map (algebraMap ℝ 𝕜)) x)) y =
      inner 𝕜 (D x) (aeval B (p.map (algebraMap ℝ 𝕜)) y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, inner_add_left, inner_add_right,
        hp, hq]
  | monomial n c =>
      have hmon : ∀ z : E, aeval B ((monomial n c : ℝ[X]).map (algebraMap ℝ 𝕜)) z =
          (algebraMap ℝ 𝕜 c) • (B ^ n) z := by
        intro z
        simp [Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply]
      rw [hmon x, hmon y, map_smul, inner_smul_left, inner_smul_right,
        RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, energyInner_pow_comm hB n x y]

end EnergySelfAdjoint

/-- Saad's Exercise 12.1, and the reason polynomial preconditioning is compatible with CG: if `B`
is self-adjoint for the inner product of a symmetric coercive `D` — for `B = D⁻¹ A` with `A`
symmetric, by `Preconditioner.energyInner_comm_of_comp_eq` — then the preconditioned operator
`s(B) B` is symmetric for that same inner product, for every real polynomial `s`. With `D = 1`
this is the statement that `s(A) A` is symmetric. -/
theorem isSymmetric_withEnergy_aeval_mul {D B : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    (hB : ∀ x y, inner 𝕜 (D (B x)) y = inner 𝕜 (D x) (B y)) (s : ℝ[X]) :
    ((WithEnergy.equiv D hD).conj (aeval B (s.map (algebraMap ℝ 𝕜)) * B)).IsSymmetric := by
  refine isSymmetric_conj_of_energyInner hD fun x y => ?_
  have h : aeval B (s.map (algebraMap ℝ 𝕜)) * B = aeval B ((s * X).map (algebraMap ℝ 𝕜)) := by
    rw [Polynomial.map_mul, Polynomial.map_X, map_mul, aeval_X]
  rw [h]
  exact energyInner_aeval_comm hB (s * X) x y

/-! ### The optimality criterion -/

/-- The residual polynomial `1 - X s` of a polynomial preconditioner, applied to an operator. -/
private theorem aeval_one_sub_X_mul_apply (A : E →ₗ[𝕜] E) (s : ℝ[X]) (x : E) :
    aeval A (((1 : ℝ[X]) - X * s).map (algebraMap ℝ 𝕜)) x =
      x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x) := by
  have hcomm : ((1 : ℝ[X]) - X * s) = 1 - s * X := by ring
  rw [hcomm]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, Module.End.mul_apply]

private theorem eval_one_sub_X_mul (s : ℝ[X]) :
    (fun t => |Polynomial.eval t ((1 : ℝ[X]) - X * s)|) = fun t => |1 - t * s.eval t| := by
  funext t
  simp

/-- The optimality criterion of Saad (12.4)–(12.5) as a bound: for a symmetric `A` whose
quadratic form lies in `[α, β]` and a real polynomial `s`,
`‖x - s(A) (A x)‖ ≤ (sup_{t ∈ [α, β]} |1 - t s(t)|) ‖x‖` in any inner product space. Choosing `s`
to make `sup |1 - t s(t)|` small is therefore exactly what makes the preconditioned operator
`s(A) A` close to the identity. The version over the spectrum rather than an enclosing interval
is `LinearMap.IsSymmetric.norm_aeval_apply_le`. -/
theorem norm_sub_aeval_mul_apply_le {A : E →ₗ[𝕜] E} {α β : ℝ} (hA : A.IsSymmetricBoundedBy α β)
    (s : ℝ[X]) (x : E) :
    ‖x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x)‖ ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * ‖x‖ := by
  have h := hA.norm_aeval_map_apply_le ((1 : ℝ[X]) - X * s) x
  rwa [aeval_one_sub_X_mul_apply, eval_one_sub_X_mul] at h

/-- The energy-norm twin of `Preconditioner.norm_sub_aeval_mul_apply_le`, which is the form the
preconditioned conjugate gradient method uses. -/
theorem energyNorm_sub_aeval_mul_apply_le {A : E →ₗ[𝕜] E} {α β : ℝ}
    (hA : A.IsSymmetricBoundedBy α β) (hα : 0 < α) (s : ℝ[X]) (x : E) :
    energyNorm A (x - aeval A (s.map (algebraMap ℝ 𝕜)) (A x)) ≤
      sSup ((fun t => |1 - t * s.eval t|) '' Set.Icc α β) * energyNorm A x := by
  have h := hA.energyNorm_aeval_map_apply_le hα ((1 : ℝ[X]) - X * s) x
  rwa [aeval_one_sub_X_mul_apply, eval_one_sub_X_mul] at h

end Preconditioner
