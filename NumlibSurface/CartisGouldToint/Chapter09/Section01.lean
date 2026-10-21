import Numlib.Optimization.FactoredSecularDerivatives
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Chapter 9, Section 1: derivatives through exact matrix factors

Algorithm 9.1.1 is the source's positive-right-hand-side recurrence, evaluated only at
orders from zero through `lMax`. Its auxiliary vectors are alternating signed actual step
derivatives. The corrected corollary retains the computed scalar outputs and distinguishes
these vectors in the additional pairing identity. All statements concern exact arithmetic.
-/

open scoped InnerProductSpace
open Matrix
open Optimization.SecularResolvent
open CartisGouldToint.Chapter08.Section01
open CartisGouldToint.Chapter08.Section02

namespace CartisGouldToint.Chapter09.Section01

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)}
  {H M L D : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}

/-- Algorithm 9.1.1. The original positive factor-solve recurrence returns exactly the
zeroth through `lMax`th scalar outputs. `ldlAuxiliaryY`, `ldlAuxiliaryZ`, and `ldlAuxiliary`
are the three intermediate vectors; `secularOddCoefficient` is the source's `β`.
The output domain removes the transcription's excess inclusive-loop iterations. -/
noncomputable def algorithm_9_1_1 (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (lMax : ℕ) : Fin (lMax + 1) → ℝ :=
  fun j => ldlSecularOutput L D M g j

/-- The actual secular step solves the shifted system whenever that matrix is positive definite.
This also permits negative shifts, provided the shifted matrix is positive definite. -/
theorem secularStep_stationary_of_posDef (hp : (H + t • M).PosDef) :
    Matrix.toEuclideanLin (H + t • M) (secularStep g H M t) = -g := by
  have hi := hp.isSymmetricCoercive_toEuclideanLin.isCoercive.injective
  have hu := (LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot.mpr hi)
  have hh := congrArg (fun B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n) => B g) (Ring.mul_inverse_cancel _ hu)
  rw [secularStep, map_neg]
  exact congrArg Neg.neg hh

/-- The computed positive auxiliary vectors have alternating signs relative to the actual
vector derivatives; this is the convention missing from the printed corollary. -/
theorem algorithm_9_1_1_auxiliary (hH : H.IsSymm) (hM : M.PosDef)
    (hp : (H + t • M).PosDef) (hL : L.IsLowerTriangular) (hD : D.IsDiag)
    (hf : L * D * Lᵀ = H + t • M) (k : ℕ) :
    ldlAuxiliary L D M g k =
      (-1 : ℝ) ^ k • iteratedDeriv k (secularStep g H M) t := by
  obtain ⟨hl, hd⟩ := ldl_pivots_ne_zero hL hD hf hp.isUnit
  apply ldlAuxiliary_eq_sign hL hl hD hd hf
    hp.isSymmetricCoercive_toEuclideanLin.isCoercive.injective
  · simpa only [iteratedDeriv_zero] using secularStep_stationary_of_posDef hp
  · intro j
    exact ((theorem_8_2_6 (g := g) hH hM hp).2 j).2.2.1

/-- The source's odd scalar output is an actual derivative despite its auxiliary vector signs. -/
theorem algorithm_9_1_1_odd (hH : H.IsSymm) (hM : M.PosDef)
    (hp : (H + t • M).PosDef) (hL : L.IsLowerTriangular) (hD : D.IsDiag)
    (hf : L * D * Lᵀ = H + t • M) (k : ℕ) :
    ldlOddOutput L D M g k = iteratedDeriv (2 * k + 1) (secularData g H M) t := by
  rw [ldlOddOutput_eq_pairing hL (ldl_pivots_ne_zero hL hD hf hp.isUnit).1 hM.isHermitian.isSymm,
    algorithm_9_1_1_auxiliary hH hM hp hL hD hf k,
    algorithm_9_1_1_auxiliary hH hM hp hL hD hf (k + 1), map_smul,
    inner_alternating_consecutive,
    ((theorem_8_2_6 (g := g) hH hM hp).2 k).1]
  ring

/-- The source's even output uses the squared metric norm, so alternating signs cancel. -/
theorem algorithm_9_1_1_even (hH : H.IsSymm) (hM : M.PosDef)
    (hp : (H + t • M).PosDef) (hL : L.IsLowerTriangular) (hD : D.IsDiag)
    (hf : L * D * Lᵀ = H + t • M) (k : ℕ) :
    ldlEvenOutput L D M g k = iteratedDeriv (2 * k) (secularData g H M) t := by
  have hnorm (u : EuclideanSpace ℝ (Fin n)) :
      weightedNorm M u ^ 2 = inner ℝ u (Matrix.toEuclideanLin M u) := by
    rw [weightedNorm_eq_energyNorm, hM.isSymmetricCoercive_toEuclideanLin.energyNorm_sq]
    simp only [RCLike.re_to_real]
    exact real_inner_comm _ _
  rw [ldlEvenOutput, algorithm_9_1_1_auxiliary hH hM hp hL hD hf k, map_smul,
    inner_alternating_self]
  cases k with
  | zero => simp [secularData, hnorm]
  | succ k =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega,
      ((theorem_8_2_6 (g := g) hH hM hp).2 k).2.1, hnorm]

/-- Corrected Corollary 9.1.1. Every requested output is the corresponding actual derivative.
The positive auxiliary vectors yield a minus sign in their consecutive pairing; the source's
plus-sign identity holds with the actual derivatives. -/
theorem corollary_9_1_1_corrected (hH : H.IsSymm) (hM : M.PosDef)
    (hp : (H + t • M).PosDef) (hL : L.IsLowerTriangular) (hD : D.IsDiag)
    (hf : L * D * Lᵀ = H + t • M) (lMax : ℕ) :
    (∀ j : Fin (lMax + 1), algorithm_9_1_1 L D M g lMax j =
      iteratedDeriv j.val (secularData g H M) t) ∧
    (∀ k : ℕ, iteratedDeriv (2 * k + 1) (secularData g H M) t =
      -2 * secularDerivativeCoefficient k * inner ℝ (ldlAuxiliary L D M g k)
        (Matrix.toEuclideanLin M (ldlAuxiliary L D M g (k + 1)))) ∧
    (∀ k : ℕ, iteratedDeriv (2 * k + 1) (secularData g H M) t =
      2 * secularDerivativeCoefficient k * inner ℝ
        (iteratedDeriv k (secularStep g H M) t)
        (Matrix.toEuclideanLin M (iteratedDeriv (k + 1) (secularStep g H M) t))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change ldlSecularOutput L D M g j.val = _
    rcases Nat.even_or_odd j.val with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [show j.val = 2 * k by omega, ldlSecularOutput_even]
      exact algorithm_9_1_1_even hH hM hp hL hD hf k
    · rw [hk, ldlSecularOutput_odd]
      exact algorithm_9_1_1_odd hH hM hp hL hD hf k
  · intro k
    rw [← algorithm_9_1_1_odd hH hM hp hL hD hf k]
    exact ldlOddOutput_eq_pairing hL (ldl_pivots_ne_zero hL hD hf hp.isUnit).1
      hM.isHermitian.isSymm g k
  · intro k
    exact ((theorem_8_2_6 (g := g) hH hM hp).2 k).1

/-- Corrected Cholesky specialization of Corollary 9.1.1. The odd derivative contains
one copy of `β`, rather than the extra factor two printed after the source corollary. -/
theorem corollary_9_1_1_cholesky (hH : H.IsSymm) (hM : M.PosDef)
    (hp : (H + t • M).PosDef) (hL : L.IsLowerTriangular)
    (hf : L * Lᵀ = H + t • M) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (secularData g H M) t = -secularOddCoefficient k *
      ‖ldlAuxiliaryY L 1 M g (k + 1)‖ ^ 2 := by
  rw [← algorithm_9_1_1_odd hH hM hp hL Matrix.isDiag_one
    (by simpa only [Matrix.mul_one] using hf) k]
  exact ldlOddOutput_cholesky L M g k

end CartisGouldToint.Chapter09.Section01
