import Numlib.Optimization.Quadratic.Secular.Factorization
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Secular derivatives from exact factorization solves

Algorithm 9.1.1 is represented by its primitive LDL-adjoint solve equations and
coefficient updates. Correctness includes the last odd-order branch, which omits
the final adjoint solve. The printed derivative right-hand side is missing the
minus sign required by (8.2.29); this formalization restores it so the computed
solution vectors are actual derivatives. The subsequent Cholesky prose also
has an extra factor two: its odd output is minus beta times the squared
intermediate norm, as in the algorithm, rather than minus twice beta.
-/

namespace CartisGouldToint

/-- The exact finite solve trace of Algorithm 9.1.1, with its corrected negative
right-hand sides. The last odd-order branch requires neither the unused final
adjoint solve nor its unused coefficient update. Arbitrary exact factors are
allowed: triangularity and diagonal storage do not affect these identities. -/
abbrev secularDerivativeFactorizationRun {n : ℕ}
    (H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (τ : ℝ)
    (L D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s y w : ℕ → EuclideanSpace ℝ (Fin n)) (α : ℕ → ℝ) (orders : ℕ) : Prop :=
  QuadraticSecular.FiniteDerivativeFactorizationRun H M g τ L D s y w α orders

/-- An exact positive-definite LDL-adjoint factorization admits the algorithm's
primitive solve trace for any requested number of derivatives. -/
theorem secularDerivativeFactorizationRun_exists {n : ℕ}
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    (g : EuclideanSpace ℝ (Fin n)) {τ : ℝ}
    (hpos : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < inner ℝ ((H + τ • M) v) v)
    (L D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hfac : H + τ • M = L.comp (D.comp L.adjoint)) (orders : ℕ) :
    ∃ s y w : ℕ → EuclideanSpace ℝ (Fin n), ∃ α : ℕ → ℝ,
      secularDerivativeFactorizationRun H M g τ L D s y w α orders :=
  B.exists_finiteFactorizationRun g
    (fun i => ne_of_gt (B.denominator_pos_of_positive hpos i)) L D hfac orders

/-- Corollary 9.1.1: all requested odd and even factorization outputs are the
actual secular derivatives. The odd derivatives also have the stated contraction
of consecutive actual solution derivatives. The initial metric pairing is the
actual secular value. The negative derivative right-hand side is corrected as
specified in the module documentation. -/
theorem corollary_9_1_1 {n orders : ℕ}
    {H M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (B : QuadraticSecular.PencilBasis (ι := Fin n) H M)
    {g : EuclideanSpace ℝ (Fin n)} {τ : ℝ}
    (hM : M.toLinearMap.IsSymmetric)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < inner ℝ ((H + τ • M) v) v)
    {L D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {s y w : ℕ → EuclideanSpace ℝ (Fin n)} {α : ℕ → ℝ}
    (_horders : 0 < orders)
    (h : secularDerivativeFactorizationRun H M g τ L D s y w α orders) :
    secularFunction H M g τ = inner ℝ (s 0) (M (s 0)) ∧
      (∀ k, 2 * k + 1 ≤ orders →
        iteratedDeriv (2 * k + 1) (secularFunction H M g) τ =
          -(2 * α k / (k + 1)) * inner ℝ (y (k + 1)) (w (k + 1)) ∧
        iteratedDeriv (2 * k + 1) (secularFunction H M g) τ =
          2 * α k * inner ℝ (iteratedDeriv k (QuadraticSecular.solution H M g) τ)
            (M (iteratedDeriv (k + 1) (QuadraticSecular.solution H M g) τ))) ∧
      (∀ k, 2 * k + 2 ≤ orders →
        iteratedDeriv (2 * k + 2) (secularFunction H M g) τ =
          α (k + 1) * inner ℝ (s (k + 1)) (M (s (k + 1)))) := by
  have hz := fun i => ne_of_gt (B.denominator_pos_of_positive hpos i)
  refine ⟨B.finiteFactorizationRun_initial_value hz h, fun k hk => ?_,
    fun k hk => B.finiteFactorizationRun_even hz h hk⟩
  refine ⟨B.finiteFactorizationRun_odd hM hz h hk, ?_⟩
  rw [h.alpha_eq (by omega)]
  exact B.iteratedDeriv_secular_odd g k hz

end CartisGouldToint
