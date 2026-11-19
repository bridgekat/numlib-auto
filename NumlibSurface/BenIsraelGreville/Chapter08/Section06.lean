/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import Numlib.Analysis.SpecialFunctions.LaplaceTransform
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.Germ.Basic

/-!
# Matrix differential systems in Laplace coordinates

Section 8.6 of [benIsrael2003generalized] describes solving homogeneous
differential systems with initial data by using a generalized inverse over
the field of real rational functions.

The concrete signal class includes a regular right-hand trajectory and a
finite sum of Dirac derivatives at zero. The latter are needed to interpret
(84) for arbitrary rational parameters. The prescribed left initial values
contribute a separate impulse correction in (82). Transforms are represented
by their germs on sufficiently far right half-planes.
-/

namespace BenIsraelGreville.Chapter08

open Matrix
open scoped BigOperators

section PolynomialSystem

variable {m n : Type*} [Fintype n] {q : ℕ}

/-- **Equations (81)–(82)** of [benIsrael2003generalized], Chapter 8.
The coefficient matrix of the transformed differential equation. -/
noncomputable def differentialMatrixPolynomial (A : Fin (q + 1) → Matrix m n ℝ) :
    Matrix m n (RatFunc ℝ) :=
  ∑ i : Fin (q + 1), ((RatFunc.X : RatFunc ℝ) ^ (i : ℕ)) •
    (A i).map (algebraMap ℝ (RatFunc ℝ))

/-- **Equation (82)** of [benIsrael2003generalized], Chapter 8.
Sum the initial-data contributions (s^{i-1-j}A_i x^{(j)}(0^-))
for (j<i). -/
noncomputable def differentialInitialPolynomial (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) : m → RatFunc ℝ :=
  ∑ i : Fin (q + 1), ∑ j ∈ Finset.range (i : ℕ),
    ((RatFunc.X : RatFunc ℝ) ^ ((i : ℕ) - 1 - j)) •
      ((A i).map (algebraMap ℝ (RatFunc ℝ)) *ᵥ (fun k => algebraMap ℝ (RatFunc ℝ) (initial j k)))

end PolynomialSystem

section OrdinarySignals

open Filter MeasureTheory Set Topology LaplaceTransform

variable {m n : Type*} [Fintype n] {q : ℕ}

/-- **Equations (80)–(81)** of [benIsrael2003generalized], Chapter 8.
The matrix differential operator on ordinary functions, with real
coefficient matrices acting on the complexified signals. -/
noncomputable def differentialMatrixApply (A : Fin (q + 1) → Matrix m n ℝ)
    (x : ℝ → n → ℂ) (t : ℝ) : m → ℂ :=
  ∑ i : Fin (q + 1), (A i).map Complex.ofReal *ᵥ iteratedDeriv (i : ℕ) x t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The boundary terms in the iterated derivative transform used in
**Equation (82)**. -/
noncomputable def laplaceInitialDerivativeSum (s : ℂ) (y : ℝ → E) (k : ℕ) : E :=
  ∑ j ∈ Finset.range k, s ^ (k - 1 - j) • iteratedDeriv j y 0

omit [CompleteSpace E] in
private theorem laplaceInitialDerivativeSum_succ (s : ℂ) (y : ℝ → E) (k : ℕ) :
    laplaceInitialDerivativeSum s y (k + 1) =
      s • laplaceInitialDerivativeSum s y k + iteratedDeriv k y 0 := by
  unfold laplaceInitialDerivativeSum
  rw [Finset.sum_range_succ, Finset.smul_sum]
  have hk : k + 1 - 1 - k = 0 := by omega
  rw [hk, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  rw [smul_smul, ← pow_succ', show k + 1 - 1 - j = k - 1 - j + 1 by omega]

/-- **Equation (82)** for an ordinary smooth signal and its derivatives.
The weighted integrability and decay assumptions justify each integration
by parts at the chosen transform argument. -/
theorem laplaceTransform_iteratedDeriv (s : ℂ) (y : ℝ → E) (k : ℕ)
    (hsmooth : ∀ i < k, ContDiff ℝ 1 (iteratedDeriv i y))
    (hint : ∀ i ≤ k, IntegrableOn
      (fun t : ℝ => Complex.exp (-(s * t)) • iteratedDeriv i y t) (Ioi 0))
    (hdecay : ∀ i < k, Tendsto
      (fun t : ℝ => Complex.exp (-(s * t)) • iteratedDeriv i y t) atTop (𝓝 0)) :
    laplaceTransform (iteratedDeriv k y) s =
      s ^ k • laplaceTransform y s - laplaceInitialDerivativeSum s y k := by
  induction k with
  | zero => simp [laplaceInitialDerivativeSum]
  | succ k ih =>
    have hk : k < k + 1 := Nat.lt_succ_self k
    have hD := laplaceTransform_deriv (hsmooth k hk) (hint k hk.le)
      (by rw [← iteratedDeriv_succ]; exact hint (k + 1) le_rfl) (hdecay k hk)
    have hI := ih (fun i hi => hsmooth i (hi.trans hk))
      (fun i hi => hint i (hi.trans hk.le)) (fun i hi => hdecay i (hi.trans hk))
    rw [iteratedDeriv_succ, hD, hI, laplaceInitialDerivativeSum_succ,
      smul_sub, smul_smul, ← pow_succ', sub_sub]

variable [Fintype m]

/-- **Equation (82)** of [benIsrael2003generalized], Chapter 8, for ordinary
signals smooth through zero. The Laplace transform of the differential
operator is its matrix polynomial applied to the transform, with the
initial derivatives subtracted. -/
theorem laplaceTransform_differentialMatrixApply (A : Fin (q + 1) → Matrix m n ℝ)
    (s : ℂ) (x : ℝ → n → ℂ)
    (hsmooth : ∀ i < q, ContDiff ℝ 1 (iteratedDeriv i x))
    (hint : ∀ i ≤ q, IntegrableOn
      (fun t : ℝ => Complex.exp (-(s * t)) • iteratedDeriv i x t) (Ioi 0))
    (hdecay : ∀ i < q, Tendsto
      (fun t : ℝ => Complex.exp (-(s * t)) • iteratedDeriv i x t) atTop (𝓝 0)) :
    laplaceTransform (differentialMatrixApply A x) s =
      (∑ i : Fin (q + 1), s ^ (i : ℕ) • (A i).map Complex.ofReal) *ᵥ laplaceTransform x s -
        ∑ i : Fin (q + 1), (A i).map Complex.ofReal *ᵥ laplaceInitialDerivativeSum s x i := by
  let F (i : Fin (q + 1)) : (n → ℂ) →L[ℂ] (m → ℂ) :=
    ((A i).map Complex.ofReal).mulVecLin.toContinuousLinearMap
  let f (i : Fin (q + 1)) (t : ℝ) := Complex.exp (-(s * t)) • iteratedDeriv i x t
  have hile (i : Fin (q + 1)) : (i : ℕ) ≤ q := Nat.le_of_lt_succ i.isLt
  have hF (i : Fin (q + 1)) (u : n → ℂ) : F i u = (A i).map Complex.ofReal *ᵥ u := rfl
  have hI (i : Fin (q + 1)) : IntegrableOn (fun t => F i (f i t)) (Ioi 0) :=
    (F i).integrable_comp (hint i (hile i))
  have hsum : (fun t : ℝ => Complex.exp (-(s * t)) • differentialMatrixApply A x t) =
      fun t => ∑ i : Fin (q + 1), F i (f i t) := by
    funext t
    simp only [differentialMatrixApply, Finset.smul_sum, f, hF, mulVec_smul]
  have hInt : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • differentialMatrixApply A x t)
      (Ioi 0) := by
    rw [hsum]
    exact integrable_finsetSum _ (fun i _ => hI i)
  calc
    _ = ∑ i : Fin (q + 1), F i (laplaceTransform (iteratedDeriv i x) s) := by
      rw [laplaceTransform_eq_integral hInt, hsum, integral_finsetSum _ (fun i _ => hI i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(F i).integral_comp_comm (hint i (hile i)),
        laplaceTransform_eq_integral (hint i (hile i))]
    _ = _ := by
      rw [Matrix.sum_mulVec, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [laplaceTransform_iteratedDeriv s x i
        (fun j hj => hsmooth j (hj.trans_le (hile i)))
        (fun j hj => hint j (hj.trans (hile i)))
        (fun j hj => hdecay j (hj.trans_le (hile i))),
        map_sub, map_smul, hF, hF, smul_mulVec]

end OrdinarySignals

section RationalInverse

private theorem ratFunc_sum_sq_eq_zero {n : Type*} [Fintype n] (v : n → RatFunc ℝ)
    (h : ∑ i, v i ^ 2 = 0) : v = 0 := by
  classical
  let D := ∏ i, (v i).denom
  let p (i : n) := (v i).num * ∏ j ∈ Finset.univ.erase i, (v j).denom
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => RatFunc.denom_ne_zero (v i)
  have hD' : algebraMap (Polynomial ℝ) (RatFunc ℝ) D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  have hcleared (i : n) : algebraMap (Polynomial ℝ) (RatFunc ℝ) (p i) =
      algebraMap (Polynomial ℝ) (RatFunc ℝ) D * v i := by
    have hd : (v i).denom * (∏ j ∈ Finset.univ.erase i, (v j).denom) = D :=
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)
    have hden : algebraMap (Polynomial ℝ) (RatFunc ℝ) (v i).denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (v i))
    calc
      _ = algebraMap (Polynomial ℝ) (RatFunc ℝ) D *
          (algebraMap (Polynomial ℝ) (RatFunc ℝ) (v i).num /
            algebraMap (Polynomial ℝ) (RatFunc ℝ) (v i).denom) := by
        rw [← hd]
        simp only [p, map_mul]
        field_simp
      _ = _ := by rw [RatFunc.num_div_denom]
  have hp : ∑ i, p i ^ 2 = 0 := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_sum, map_zero]
    simp only [map_pow, hcleared, mul_pow, ← Finset.mul_sum, h, mul_zero]
  have hz (i : n) : p i = 0 := by
    apply Polynomial.funext
    intro x
    have he := congrArg (Polynomial.evalRingHom x) hp
    simp only [map_sum, map_pow, map_zero] at he
    rw [Polynomial.eval_zero]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((p j).eval x))).mp he
      i (Finset.mem_univ i)
    exact pow_eq_zero_iff two_ne_zero |>.mp hi
  funext i
  have hi := hcleared i
  rw [hz i, map_zero] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hD'

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The transpose form of the Moore–Penrose equations, for the real
rational function field used in **Theorem 6**. -/
structure IsRationalMoorePenroseInverse (A : Matrix m n (RatFunc ℝ))
    (X : Matrix n m (RatFunc ℝ)) : Prop where
  inner : A * X * A = A
  outer : X * A * X = X
  image_symm : (A * X).IsSymm
  domain_symm : (X * A).IsSymm

private theorem isUnit_transpose_mul_self_of_mulVec_injective
    (M : Matrix m n (RatFunc ℝ)) (hM : Function.Injective M.mulVec) :
    IsUnit (Mᵀ * M) := by
  refine (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
  intro hdet
  obtain ⟨v, hv, hzero⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hdot : (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = 0 := by
    calc
      _ = v ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ v)) := by
        rw [dotProduct_mulVec v Mᵀ (M *ᵥ v), vecMul_transpose]
      _ = 0 := by rw [mulVec_mulVec, hzero, dotProduct_zero]
  have hs : ∑ i, (M *ᵥ v) i ^ 2 = 0 := by
    simpa only [dotProduct, pow_two] using hdot
  exact hv (hM ((ratFunc_sum_sq_eq_zero _ hs).trans (mulVec_zero M).symm))

variable [DecidableEq m]

omit [DecidableEq m] [DecidableEq n] in
/-- The Moore–Penrose equations have a unique solution over the real
rational function field. The construction uses a full-rank factorization
and the two invertible Gram matrices. -/
theorem existsUnique_rationalMoorePenroseInverse (A : Matrix m n (RatFunc ℝ)) :
    ∃! X, IsRationalMoorePenroseInverse A X := by
  classical
  obtain ⟨F, G, h⟩ := Chapter00.lemma_1 A
  let S := Fᵀ * F
  let T := G * Gᵀ
  have hs : IsUnit S := isUnit_transpose_mul_self_of_mulVec_injective F
    (mulVec_injective_iff_rank_eq_card.mpr h.rank_left)
  have ht : IsUnit T := by
    have hg : Function.Injective Gᵀ.mulVec :=
      mulVec_injective_iff_rank_eq_card.mpr (by rw [rank_transpose, h.rank_right])
    simpa only [transpose_transpose] using
      isUnit_transpose_mul_self_of_mulVec_injective Gᵀ hg
  have hsD := (isUnit_iff_isUnit_det S).mp hs
  have htD := (isUnit_iff_isUnit_det T).mp ht
  let X := Gᵀ * T⁻¹ * S⁻¹ * Fᵀ
  have hAX : A * X = F * S⁻¹ * Fᵀ := by
    calc
      _ = F * (T * T⁻¹) * S⁻¹ * Fᵀ := by
        simp only [h.eq_mul, X, T, Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv T htD, Matrix.mul_one]
  have hXA : X * A = Gᵀ * T⁻¹ * G := by
    calc
      _ = Gᵀ * T⁻¹ * (S⁻¹ * S) * G := by
        simp only [h.eq_mul, X, S, Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul S hsD, Matrix.mul_one]
  have hi : A * X * A = A := by
    calc
      _ = F * (S⁻¹ * S) * G := by
        rw [hAX]
        exact (congrArg (fun M : Matrix m n (RatFunc ℝ) => F * S⁻¹ * Fᵀ * M)
          h.eq_mul).trans (by simp only [S, Matrix.mul_assoc])
      _ = A := by
        rw [nonsing_inv_mul S hsD, Matrix.mul_one]
        exact h.eq_mul.symm
  have ho : X * A * X = X := by
    calc
      _ = Gᵀ * T⁻¹ * (T * T⁻¹) * S⁻¹ * Fᵀ := by
        rw [hXA]
        simp only [X, T, Matrix.mul_assoc]
      _ = X := by rw [mul_nonsing_inv T htD, Matrix.mul_one]
  have hSX : Sᵀ = S := by simp [S, transpose_mul]
  have hTX : Tᵀ = T := by simp [T, transpose_mul]
  have h1 : (A * X).IsSymm := by
    change (A * X)ᵀ = A * X
    rw [hAX, transpose_mul, transpose_mul, transpose_nonsing_inv, hSX, transpose_transpose,
      Matrix.mul_assoc]
  have h2 : (X * A).IsSymm := by
    change (X * A)ᵀ = X * A
    rw [hXA, transpose_mul, transpose_mul, transpose_nonsing_inv, hTX, transpose_transpose,
      Matrix.mul_assoc]
  refine ⟨X, ⟨hi, ho, h1, h2⟩, ?_⟩
  intro Y hY
  have hdom : Y * A = X * A := by
    calc
      Y * A = (Y * A)ᵀ := hY.domain_symm.eq.symm
      _ = (X * A)ᵀ * (Y * A)ᵀ := by
        nth_rw 1 [← hi]
        simp only [transpose_mul, Matrix.mul_assoc]
      _ = X * A := by
        rw [h2.eq, hY.domain_symm.eq, Matrix.mul_assoc X, ← Matrix.mul_assoc A Y, hY.inner]
  have himg : A * Y = A * X := by
    calc
      A * Y = (A * Y)ᵀ := hY.image_symm.eq.symm
      _ = (A * Y)ᵀ * (A * X)ᵀ := by
        nth_rw 1 [← hi]
        simp only [transpose_mul, Matrix.mul_assoc]
      _ = A * X := by
        rw [hY.image_symm.eq, h1.eq, ← Matrix.mul_assoc, hY.inner]
  calc
    Y = (Y * A) * Y := hY.outer.symm
    _ = X * (A * Y) := by rw [hdom, Matrix.mul_assoc]
    _ = X := by rw [himg, ← Matrix.mul_assoc, ho]

omit [DecidableEq m] [DecidableEq n] in
/-- The real-rational Moore–Penrose inverse in **Theorem 6**. -/
noncomputable def rationalPseudoinverse (A : Matrix m n (RatFunc ℝ)) :
    Matrix n m (RatFunc ℝ) :=
  (existsUnique_rationalMoorePenroseInverse A).exists.choose

omit [DecidableEq m] [DecidableEq n] in
/-- The rational pseudoinverse satisfies the four transpose Penrose equations. -/
theorem isRationalMoorePenroseInverse_rationalPseudoinverse (A : Matrix m n (RatFunc ℝ)) :
    IsRationalMoorePenroseInverse A (rationalPseudoinverse A) :=
  (existsUnique_rationalMoorePenroseInverse A).exists.choose_spec

end RationalInverse

section Solution

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (84)** of [benIsrael2003generalized], Chapter 8.
The affine family of transformed solutions indexed by rational vectors. -/
noncomputable def rationalSystemCandidate (M : Matrix m n (RatFunc ℝ))
    (b : m → RatFunc ℝ) (y : n → RatFunc ℝ) : n → RatFunc ℝ :=
  let X := rationalPseudoinverse M
  X *ᵥ b + (1 - X * M) *ᵥ y

omit [DecidableEq m] in
/-- **Theorem 6**, Equations (83)–(84) of [benIsrael2003generalized], Chapter 8.
The projected right-hand side tests consistency over the real-rational
field. If it passes the test, every solution is in the affine family. -/
theorem theorem_6 (M : Matrix m n (RatFunc ℝ)) (b : m → RatFunc ℝ) :
    ((∃ x, M *ᵥ x = b) ↔ M *ᵥ (rationalPseudoinverse M *ᵥ b) = b) ∧
    (M *ᵥ (rationalPseudoinverse M *ᵥ b) = b → ∀ x,
      M *ᵥ x = b ↔ ∃ y, x = rationalSystemCandidate M b y) := by
  let X := rationalPseudoinverse M
  have hX : M * X * M = M := (isRationalMoorePenroseInverse_rationalPseudoinverse M).inner
  refine ⟨⟨?_, fun h => ⟨X *ᵥ b, h⟩⟩, ?_⟩
  · rintro ⟨x, rfl⟩
    change M *ᵥ (X *ᵥ (M *ᵥ x)) = M *ᵥ x
    rw [mulVec_mulVec, mulVec_mulVec, hX]
  · intro hb x
    change M *ᵥ (X *ᵥ b) = b at hb
    constructor
    · intro hx
      refine ⟨x, ?_⟩
      change x = X *ᵥ b + (1 - X * M) *ᵥ x
      rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hx]
      abel
    · rintro ⟨y, rfl⟩
      change M *ᵥ (X *ᵥ b + (1 - X * M) *ᵥ y) = b
      rw [mulVec_add, hb, mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one,
        ← Matrix.mul_assoc, hX, sub_self, zero_mulVec, add_zero]

omit [DecidableEq m] in
/-- **Equations (82)–(84)** of [benIsrael2003generalized], Chapter 8.
For an invertible Laplace representation satisfying the transformed
differential equation, the rational consistency test and general solution
transport to the signal space. -/
theorem theorem_6_of_laplace_representation
    {S T : Type*} [Zero T] {q : ℕ} (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) (L : S ≃ (n → RatFunc ℝ)) (Lout : T ≃ (m → RatFunc ℝ))
    (hzero : Lout 0 = 0) (applyDifferential : S → T)
    (hLaplace : ∀ x, Lout (applyDifferential x) =
      differentialMatrixPolynomial A *ᵥ L x - differentialInitialPolynomial A initial) :
    let M := differentialMatrixPolynomial A
    let b := differentialInitialPolynomial A initial
    ((∃ x, applyDifferential x = 0) ↔ M *ᵥ (rationalPseudoinverse M *ᵥ b) = b) ∧
    (M *ᵥ (rationalPseudoinverse M *ᵥ b) = b → ∀ x,
      applyDifferential x = 0 ↔ ∃ y, x = L.symm (rationalSystemCandidate M b y)) := by
  intro M b
  have hrep (x : S) : applyDifferential x = 0 ↔ M *ᵥ L x = b := by
    rw [← Lout.injective.eq_iff, hLaplace, hzero, sub_eq_zero]
  have h := theorem_6 M b
  refine ⟨?_, fun hb x => ?_⟩
  · exact ⟨fun ⟨x, hx⟩ => h.1.mp ⟨L x, (hrep x).mp hx⟩, fun hb => by
      obtain ⟨u, hu⟩ := h.1.mpr hb
      exact ⟨L.symm u, (hrep _).mpr (by simpa only [Equiv.apply_symm_apply] using hu)⟩⟩
  · rw [hrep, h.2 hb]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, L.injective (by rwa [Equiv.apply_symm_apply])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, L.apply_symm_apply _⟩

end Solution


section ConcreteCausalSignals

open Filter Set MeasureTheory Topology Polynomial
open scoped Nat FourierTransform Polynomial

/-- A function on the real time axis is exponentially bounded on the nonnegative ray. -/
def IsLaplaceExpBounded (f : ℝ → ℂ) : Prop :=
  ∃ C a : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)

private theorem laplaceExpBounded_add {f g : ℝ → ℂ}
    (hf : IsLaplaceExpBounded f) (hg : IsLaplaceExpBounded g) :
    IsLaplaceExpBounded (f + g) := by
  obtain ⟨C, a, hC, hf⟩ := hf
  obtain ⟨D, b, hD, hg⟩ := hg
  refine ⟨C + D, max a b, add_nonneg hC hD, fun t ht => ?_⟩
  calc
    ‖(f + g) t‖ ≤ ‖f t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ C * Real.exp (a * t) + D * Real.exp (b * t) := add_le_add (hf t ht) (hg t ht)
    _ ≤ C * Real.exp (max a b * t) + D * Real.exp (max a b * t) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)) hC)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) ht)) hD)
    _ = _ := (add_mul _ _ _).symm

private theorem laplaceExpBounded_const_mul {f : ℝ → ℂ} (hf : IsLaplaceExpBounded f) (c : ℂ) :
    IsLaplaceExpBounded (fun t => c * f t) := by
  obtain ⟨C, a, hC, hf⟩ := hf
  refine ⟨‖c‖ * C, a, mul_nonneg (norm_nonneg _) hC, fun t ht => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf t ht) (norm_nonneg _)

private theorem laplaceExpBounded_zero : IsLaplaceExpBounded (0 : ℝ → ℂ) :=
  ⟨0, 0, le_rfl, fun t _ => by simp⟩

private theorem laplaceExpBounded_pow_mul_exp (pole : ℂ) (k : ℕ) :
    IsLaplaceExpBounded (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (pole * t)) := by
  refine ⟨k !, pole.re + 1, by positivity, fun t ht => ?_⟩
  have h := (div_le_iff₀ (show 0 < (k ! : ℝ) by positivity)).mp (Real.pow_div_factorial_le_exp t ht k)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [add_mul, one_mul, Real.exp_add, ← mul_assoc]
  refine (mul_le_mul_of_nonneg_right h (Real.exp_pos (pole.re * t)).le).trans_eq ?_
  ring

/-- The regular signal contributed by a complex pole. A pole of order `k+1`
has time-domain kernel `t^k exp(pole t) / k!`. -/
noncomputable def laplacePoleSignal (pole : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ((k ! : ℂ)⁻¹ * (t : ℂ) ^ k) * Complex.exp (pole * t)

private theorem hasDerivAt_laplace_weight (w : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-(w * x))) (-w * Complex.exp (-(w * t))) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul w).neg.cexp).comp_ofReal
  exact h.congr_deriv (by simp [mul_comm])

private theorem integrableOn_pow_mul_laplace_weight (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-(w * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := w.re)
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) zero_lt_one hw
  refine h.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htt : 0 < t := ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg htt.le, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Real.rpow_one, Real.rpow_natCast, neg_mul, le_rfl]

private theorem tendsto_pow_mul_laplace_weight_zero (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-(w * t))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k w.re hw).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Real.rpow_natCast, neg_mul]

private theorem integral_pow_mul_laplace_weight (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ k * Complex.exp (-(w * t)) = (k ! : ℂ) / w ^ (k + 1) := by
  have hw₀ : w ≠ 0 := fun h => by simp [h] at hw
  induction k with
  | zero =>
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (-w)⁻¹ * Complex.exp (-(w * t)))
        (Complex.exp (-(w * t))) t := by
      convert (hasDerivAt_laplace_weight w t).const_mul (-w)⁻¹ using 1
      rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hw₀), one_mul]
    have hLimit : Tendsto (fun t : ℝ => (-w)⁻¹ * Complex.exp (-(w * t))) atTop (𝓝 0) := by
      simpa only [pow_zero, one_mul, mul_zero] using
        (tendsto_pow_mul_laplace_weight_zero w hw 0).const_mul (-w)⁻¹
    have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t)
      (by simpa using integrableOn_pow_mul_laplace_weight w hw 0) hLimit
    simpa [one_div] using hi
  | succ k hk =>
    let F (t : ℝ) := (t : ℂ) ^ (k + 1) * Complex.exp (-(w * t))
    let K (t : ℝ) := (t : ℂ) ^ k * Complex.exp (-(w * t))
    have hD (t : ℝ) : HasDerivAt F ((k + 1 : ℂ) * K t - w * F t) t := by
      have hp : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (k + 1)) ((k + 1 : ℂ) * (t : ℂ) ^ k) t := by
        simpa only [id_eq, Nat.add_sub_cancel, Nat.cast_succ, mul_one, Pi.pow_apply] using
          ((hasDerivAt_id (t : ℂ)).pow (k + 1)).comp_ofReal
      exact (hp.fun_mul (hasDerivAt_laplace_weight w t)).congr_deriv (by dsimp [F, K]; ring)
    have hF := integrableOn_pow_mul_laplace_weight w hw (k + 1)
    have hK := integrableOn_pow_mul_laplace_weight w hw k
    have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hD t)
      ((hK.const_mul _).sub (hF.const_mul _)) (tendsto_pow_mul_laplace_weight_zero w hw (k + 1))
    have h0 : F 0 = 0 := by simp [F]
    rw [h0, sub_zero, integral_sub (hK.const_mul _) (hF.const_mul _), integral_const_mul,
      integral_const_mul] at hi
    have hmul : w * (∫ t in Ioi 0, F t) = (k + 1 : ℂ) * ∫ t in Ioi 0, K t := by
      exact (sub_eq_zero.mp hi).symm
    change w * (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (k + 1) * Complex.exp (-(w * t))) =
      (k + 1 : ℂ) * (∫ t : ℝ in Ioi 0, (t : ℂ) ^ k * Complex.exp (-(w * t))) at hmul
    rw [hk] at hmul
    apply mul_left_cancel₀ hw₀
    rw [hmul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ' _ (k + 1)]
    field_simp

/-- The ordinary Laplace transform of the repeated-pole kernel. -/
theorem laplaceTransform_poleSignal (pole : ℂ) (k : ℕ) {s : ℂ} (hs : pole.re < s.re) :
    LaplaceTransform.laplaceTransform (laplacePoleSignal pole k) s = (s - pole)⁻¹ ^ (k + 1) := by
  have hw : 0 < (s - pole).re := by rw [Complex.sub_re]; exact sub_pos.mpr hs
  have he : (fun t : ℝ => Complex.exp (-(s * t)) • laplacePoleSignal pole k t) =
      fun t : ℝ => (k ! : ℂ)⁻¹ * ((t : ℂ) ^ k * Complex.exp (-((s - pole) * t))) := by
    funext t
    simp only [smul_eq_mul, laplacePoleSignal]
    calc
      _ = (k ! : ℂ)⁻¹ * (t : ℂ) ^ k *
          (Complex.exp (-(s * t)) * Complex.exp (pole * t)) := by ring
      _ = _ := by rw [← Complex.exp_add, show -(s * (t : ℂ)) + pole * t = -((s - pole) * t) by ring,
        mul_assoc]
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) • laplacePoleSignal pole k t) (Ioi 0) := by
    rw [he]
    exact (integrableOn_pow_mul_laplace_weight (s - pole) hw k).const_mul _
  rw [LaplaceTransform.laplaceTransform_eq_integral hi, he, integral_const_mul,
    integral_pow_mul_laplace_weight _ hw, inv_pow]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]


/-- The filter of sufficiently far right complex half-planes. -/
def laplaceRightHalfPlane : Filter ℂ := comap Complex.re atTop

private theorem eventually_laplaceRightHalfPlane {P : ℂ → Prop} :
    (∀ᶠ s in laplaceRightHalfPlane, P s) ↔ ∃ a : ℝ, ∀ s : ℂ, a < s.re → P s := by
  rw [laplaceRightHalfPlane, eventually_comap, eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun s hs => ha _ hs.le s rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨a + 1, fun b hb s hs => ha s ?_⟩
    linarith

instance : NeBot laplaceRightHalfPlane := by
  constructor
  intro h
  have hfalse : ∀ᶠ s in laplaceRightHalfPlane, False := by simp [h]
  obtain ⟨a, ha⟩ := eventually_laplaceRightHalfPlane.mp hfalse
  exact ha (↑(a + 1) : ℂ) (by simp)

private theorem eventually_evaluate_nonzero {K : Type*} [Field K]
    (f : K →+* ℂ) (hf : Function.Injective f) {p : K[X]} (hp : p ≠ 0) :
    ∀ᶠ s in laplaceRightHalfPlane, p.eval₂ f s ≠ 0 := by
  have hmap : p.map f ≠ 0 := fun h => hp ((Polynomial.map_injective f hf) (h.trans (Polynomial.map_zero f).symm))
  obtain ⟨a, ha⟩ := Set.exists_upper_bound_image _ Complex.re (Polynomial.finite_setOfPred_isRoot hmap)
  refine eventually_laplaceRightHalfPlane.mpr ⟨a.re, fun s hs h0 => ?_⟩
  exact (not_le_of_gt hs) (ha s (by change (p.map f).eval s = 0; rwa [← Polynomial.eval₂_eq_eval_map]))

private noncomputable def polynomialEvalLaplaceGerm {K : Type*} [Field K]
    (f : K →+* ℂ) : Polynomial K →+* Germ laplaceRightHalfPlane ℂ where
  toFun p := (fun s : ℂ => p.eval₂ f s)
  map_one' := Germ.coe_eq.mpr (Eventually.of_forall fun s => Polynomial.eval₂_one f s)
  map_mul' _ _ := Germ.coe_eq.mpr (Eventually.of_forall fun s => Polynomial.eval₂_mul f s)
  map_zero' := Germ.coe_eq.mpr (Eventually.of_forall fun s => Polynomial.eval₂_zero f s)
  map_add' _ _ := Germ.coe_eq.mpr (Eventually.of_forall fun s => Polynomial.eval₂_add f s)

private theorem polynomialEvalLaplaceGerm_unit {K : Type*} [Field K]
    (f : K →+* ℂ) (hf : Function.Injective f) (p : nonZeroDivisors K[X]) :
    IsUnit (polynomialEvalLaplaceGerm f p) := by
  have hp := eventually_evaluate_nonzero f hf ((mem_nonZeroDivisors_iff_ne_zero).mp p.property)
  refine ⟨⟨polynomialEvalLaplaceGerm f p, (fun s : ℂ => ((p : K[X]).eval₂ f s)⁻¹), ?_, ?_⟩, rfl⟩
  · change ((fun s : ℂ => (p : K[X]).eval₂ f s * ((p : K[X]).eval₂ f s)⁻¹) : Germ _ ℂ) = ((fun _ : ℂ => (1 : ℂ)) : Germ laplaceRightHalfPlane ℂ)
    exact Germ.coe_eq.mpr (hp.mono fun _ hs => mul_inv_cancel₀ hs)
  · change ((fun s : ℂ => ((p : K[X]).eval₂ f s)⁻¹ * (p : K[X]).eval₂ f s) : Germ _ ℂ) = ((fun _ : ℂ => (1 : ℂ)) : Germ laplaceRightHalfPlane ℂ)
    exact Germ.coe_eq.mpr (hp.mono fun _ hs => inv_mul_cancel₀ hs)

/-- Evaluate rational functions as germs on right half-planes. Every nonzero
polynomial is a unit as a germ, since its finite set of roots is bounded. -/
noncomputable def rationalEvalLaplaceGerm {K : Type*} [Field K] (f : K →+* ℂ) :
    RatFunc K →+* Germ laplaceRightHalfPlane ℂ :=
  IsLocalization.lift (M := nonZeroDivisors K[X]) (polynomialEvalLaplaceGerm_unit f f.injective)

private theorem rationalEvalLaplaceGerm_polynomial {K : Type*} [Field K] (f : K →+* ℂ)
    (p : K[X]) :
    rationalEvalLaplaceGerm f (algebraMap K[X] (RatFunc K) p) =
      (fun s : ℂ => p.eval₂ f s) :=
  show rationalEvalLaplaceGerm f (algebraMap K[X] (RatFunc K) p) = polynomialEvalLaplaceGerm f p from
    IsLocalization.lift_eq (S := RatFunc K) (polynomialEvalLaplaceGerm_unit f f.injective) p

private theorem rationalEvalLaplaceGerm_div_polynomials {K : Type*} [Field K] (f : K →+* ℂ)
    (p q : K[X]) (hq : q ≠ 0) :
    rationalEvalLaplaceGerm f (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) =
      (fun s : ℂ => p.eval₂ f s / q.eval₂ f s) := by
  let q' : nonZeroDivisors K[X] := ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩
  change rationalEvalLaplaceGerm f (algebraMap K[X] (RatFunc K) p /
    algebraMap K[X] (RatFunc K) (q' : K[X])) = _
  rw [← IsFractionRing.mk'_eq_div]
  apply (IsLocalization.lift_mk'_spec (polynomialEvalLaplaceGerm_unit f f.injective) p _ q').mpr
  change ((fun s : ℂ => p.eval₂ f s) : Germ laplaceRightHalfPlane ℂ) =
    ↑(fun s : ℂ => q.eval₂ f s * (p.eval₂ f s / q.eval₂ f s))
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_evaluate_nonzero f f.injective hq] with s hs
  field_simp

/-- The right half-plane evaluation germ has the usual numerator/denominator value. -/
theorem rationalEvalLaplaceGerm_eq_eval {K : Type} [Field K] (f : K →+* ℂ) (r : RatFunc K) :
    rationalEvalLaplaceGerm f r = (fun s : ℂ => r.eval f s) := by
  change _ = ((fun s : ℂ => r.num.eval₂ f s / r.denom.eval₂ f s) : Germ laplaceRightHalfPlane ℂ)
  rw [← rationalEvalLaplaceGerm_div_polynomials f r.num r.denom r.denom_ne_zero, RatFunc.num_div_denom]

/-- Regular causal signals are restrictions to the nonnegative ray of real-time
analytic functions of exponential order, with the same property for each derivative. -/
def IsRegularCausalSignal (f : ℝ → ℂ) : Prop :=
  AnalyticOnNhd ℝ f univ ∧ ∀ n, IsLaplaceExpBounded (iteratedDeriv n f)

private theorem IsRegularCausalSignal.contDiff {f : ℝ → ℂ} (hf : IsRegularCausalSignal f)
    {n : WithTop ℕ∞} : ContDiff ℝ n f := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (hf.1 t (mem_univ _)).contDiffAt

private theorem IsRegularCausalSignal.bound {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    IsLaplaceExpBounded f := by simpa only [iteratedDeriv_zero] using hf.2 0

private theorem regularCausalSignal_zero : IsRegularCausalSignal (0 : ℝ → ℂ) := by
  refine ⟨analyticOnNhd_const, fun n => ?_⟩
  have he : iteratedDeriv n (0 : ℝ → ℂ) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iteratedDeriv_succ, ih]; ext t; simp
  rw [he]
  exact laplaceExpBounded_zero

private theorem IsRegularCausalSignal.add {f g : ℝ → ℂ}
    (hf : IsRegularCausalSignal f) (hg : IsRegularCausalSignal g) :
    IsRegularCausalSignal (f + g) := by
  refine ⟨hf.1.add hg.1, fun n => ?_⟩
  have he : iteratedDeriv n (f + g) = iteratedDeriv n f + iteratedDeriv n g := by
    funext t
    exact iteratedDeriv_add hf.contDiff.contDiffAt hg.contDiff.contDiffAt
  rw [he]
  exact laplaceExpBounded_add (hf.2 n) (hg.2 n)

private theorem IsRegularCausalSignal.const_mul {f : ℝ → ℂ}
    (hf : IsRegularCausalSignal f) (c : ℂ) : IsRegularCausalSignal (fun t => c * f t) := by
  refine ⟨fun t _ => analyticAt_const.mul (hf.1 _ (mem_univ _)), fun n => ?_⟩
  have he : iteratedDeriv n (fun t => c * f t) = fun t => c * iteratedDeriv n f t := by
    funext t
    exact iteratedDeriv_const_mul c hf.contDiff.contDiffAt
  rw [he]
  exact laplaceExpBounded_const_mul (hf.2 n) c

private theorem IsRegularCausalSignal.deriv {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    IsRegularCausalSignal (deriv f) :=
  ⟨hf.1.deriv, fun n => by rw [← iteratedDeriv_succ']; exact hf.2 (n + 1)⟩

private theorem regularCausalSignal_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, IsRegularCausalSignal (f i)) : IsRegularCausalSignal (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using regularCausalSignal_zero
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem IsRegularCausalSignal.conj {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    IsRegularCausalSignal (fun t => star (f t)) := by
  refine ⟨fun t _ => ?_, fun n => ?_⟩
  · have hc := Complex.conjCLE.toContinuousLinearMap.analyticAt (f t)
    exact hc.comp (hf.1 t (mem_univ _))
  · have he (n : ℕ) : iteratedDeriv n (fun t => star (f t)) = fun t => star (iteratedDeriv n f t) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
        funext t
        have hd : DifferentiableAt ℝ (iteratedDeriv n f) t :=
          (hf.contDiff : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f).differentiable_iteratedDeriv' n t
        exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
    obtain ⟨C, a, hC, h⟩ := hf.2 n
    exact ⟨C, a, hC, fun t ht => by simpa only [he, norm_star] using h t ht⟩

private noncomputable def laplaceExponentialPolynomial (pole : ℂ) (p : Polynomial ℂ) (t : ℝ) : ℂ :=
  p.eval (t : ℂ) * Complex.exp (pole * t)

private theorem laplaceExpBounded_exponentialPolynomial (pole : ℂ) (p : Polynomial ℂ) :
    IsLaplaceExpBounded (laplaceExponentialPolynomial pole p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have he : laplaceExponentialPolynomial pole (p + q) =
        laplaceExponentialPolynomial pole p + laplaceExponentialPolynomial pole q := by
      funext t
      simp [laplaceExponentialPolynomial, add_mul]
    rw [he]
    exact laplaceExpBounded_add hp hq
  | monomial k c =>
    have he : laplaceExponentialPolynomial pole (Polynomial.monomial k c) =
        fun t : ℝ => c * ((t : ℂ) ^ k * Complex.exp (pole * t)) := by
      funext t
      simp [laplaceExponentialPolynomial, mul_assoc]
    rw [he]
    exact laplaceExpBounded_const_mul (laplaceExpBounded_pow_mul_exp pole k) c

private theorem deriv_laplaceExponentialPolynomial (pole : ℂ) (p : Polynomial ℂ) :
    deriv (laplaceExponentialPolynomial pole p) =
      laplaceExponentialPolynomial pole (p.derivative + Polynomial.C pole * p) := by
  funext t
  have hp := (p.hasDerivAt (t : ℂ)).comp_ofReal
  have he := (hasDerivAt_laplace_weight (-pole) t)
  simp only [neg_mul, neg_neg] at he
  apply (hp.fun_mul he).deriv.trans
  simp only [laplaceExponentialPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

private theorem regularCausalSignal_exponentialPolynomial (pole : ℂ) (p : Polynomial ℂ) :
    IsRegularCausalSignal (laplaceExponentialPolynomial pole p) := by
  refine ⟨fun t _ => ?_, fun n => ?_⟩
  · have hpol : AnalyticAt ℂ (fun z => p.eval z) (t : ℂ) := by
      induction p using Polynomial.induction_on' with
      | add u v hu hv => simpa only [Polynomial.eval_add, Pi.add_def] using hu.add hv
      | monomial k c =>
        have h : AnalyticAt ℂ (fun z : ℂ => c * z ^ k) (t : ℂ) := by fun_prop
        simpa only [Polynomial.eval_monomial] using h
    have hexp : AnalyticAt ℂ (fun z => Complex.exp (pole * z)) (t : ℂ) := by fun_prop
    exact ((hpol.mul hexp).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  · induction n generalizing p with
    | zero => simpa only [iteratedDeriv_zero] using laplaceExpBounded_exponentialPolynomial pole p
    | succ n ih => rw [iteratedDeriv_succ', deriv_laplaceExponentialPolynomial]; exact ih _

private theorem regularCausalSignal_poleSignal (pole : ℂ) (k : ℕ) :
    IsRegularCausalSignal (laplacePoleSignal pole k) := by
  have he : laplacePoleSignal pole k = laplaceExponentialPolynomial pole (Polynomial.monomial k ((k ! : ℂ)⁻¹)) := by
    funext t
    simp [laplaceExponentialPolynomial, laplacePoleSignal]
  rw [he]
  exact regularCausalSignal_exponentialPolynomial _ _

private noncomputable def regularLaplaceGerm (f : ℝ → ℂ) : Germ laplaceRightHalfPlane ℂ :=
  (fun s : ℂ => LaplaceTransform.laplaceTransform f s)

private theorem norm_laplace_weight_mul_le {f : ℝ → ℂ} {C a : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) (s : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(s * t)) * f t‖ ≤ C * Real.exp (-(s.re - a) * t) := by
  simp only [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  refine (mul_le_mul_of_nonneg_left (h t ht) (Real.exp_pos _).le).trans_eq ?_
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

private theorem integrableOn_laplace_weight_mul {f : ℝ → ℂ} (hf : Continuous f)
    {C a : ℝ} (h : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) {s : ℂ} (hs : a < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0) := by
  refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos (sub_pos.mpr hs)) 0).const_mul C).mono'
    (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_laplace_weight_mul_le h s (le_of_lt ht)

private theorem tendsTo_zero_laplace_weight_mul {f : ℝ → ℂ} {C a : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) {s : ℂ} (hs : a < s.re) :
    Tendsto (fun t : ℝ => Complex.exp (-(s * t)) * f t) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun t => C * Real.exp (-(s.re - a) * t)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using norm_laplace_weight_mul_le h s ht
  · have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hs))).const_mul C
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using he

private theorem IsRegularCausalSignal.integrable_weight {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    ∀ᶠ s in laplaceRightHalfPlane,
      IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * f t) (Ioi 0) := by
  obtain ⟨C, a, -, h⟩ := hf.bound
  exact eventually_laplaceRightHalfPlane.mpr ⟨a, fun _ hs =>
    integrableOn_laplace_weight_mul (hf.contDiff (n := 0)).continuous h hs⟩

private theorem regularLaplaceGerm_add {f g : ℝ → ℂ} (hf : IsRegularCausalSignal f)
    (hg : IsRegularCausalSignal g) : regularLaplaceGerm (f + g) = regularLaplaceGerm f + regularLaplaceGerm g := by
  apply Germ.coe_eq.mpr
  filter_upwards [hf.integrable_weight, hg.integrable_weight] with s hfi hgi
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (f + g) t) (Ioi 0) := by
    simp only [Pi.add_apply, mul_add]
    exact hfi.add hgi
  rw [LaplaceTransform.laplaceTransform_eq_integral hi,
    LaplaceTransform.laplaceTransform_eq_integral hfi, LaplaceTransform.laplaceTransform_eq_integral hgi]
  simpa only [smul_eq_mul, Pi.add_apply, mul_add] using integral_add hfi hgi

private theorem regularLaplaceGerm_const_mul {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) (c : ℂ) :
    regularLaplaceGerm (fun t => c * f t) = (↑c : Germ laplaceRightHalfPlane ℂ) * regularLaplaceGerm f := by
  apply Germ.coe_eq.mpr
  filter_upwards [hf.integrable_weight] with s hfi
  have he : (fun t : ℝ => Complex.exp (-(s * t)) * (c * f t)) =
      fun t : ℝ => c * (Complex.exp (-(s * t)) * f t) := funext fun t => mul_left_comm _ _ _
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (c * f t)) (Ioi 0) := by
    rw [he]
    exact hfi.const_mul c
  rw [LaplaceTransform.laplaceTransform_eq_integral hi,
    LaplaceTransform.laplaceTransform_eq_integral hfi]
  simp only [smul_eq_mul, he, integral_const_mul]

private theorem regularLaplaceGerm_zero : regularLaplaceGerm (0 : ℝ → ℂ) = 0 := by
  apply Germ.coe_eq.mpr
  filter_upwards with s
  have hi : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (0 : ℂ)) (Ioi 0) := by simp
  change LaplaceTransform.laplaceTransform (fun _ : ℝ => (0 : ℂ)) s = 0
  simpa using (LaplaceTransform.laplaceTransform_eq_integral hi)

private theorem regularLaplaceGerm_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, IsRegularCausalSignal (f i)) :
    regularLaplaceGerm (∑ i ∈ S, f i) = ∑ i ∈ S, regularLaplaceGerm (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, regularLaplaceGerm_zero]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, regularLaplaceGerm_add, ih]
    · exact fun j hj => hf j (Finset.mem_insert_of_mem hj)
    · exact hf i (Finset.mem_insert_self _ _)
    · exact regularCausalSignal_sum S f fun j hj => hf j (Finset.mem_insert_of_mem hj)

private theorem regularLaplaceGerm_deriv {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    regularLaplaceGerm (deriv f) = (↑(id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) * regularLaplaceGerm f -
      (↑(f 0) : Germ laplaceRightHalfPlane ℂ) := by
  obtain ⟨C, a, -, h⟩ := hf.bound
  apply Germ.coe_eq.mpr
  have hlim := (eventually_laplaceRightHalfPlane (P := fun s =>
    Tendsto (fun t : ℝ => Complex.exp (-(s * t)) * f t) atTop (𝓝 0))).mpr
    ⟨a, fun _ hs => tendsTo_zero_laplace_weight_mul h hs⟩
  filter_upwards [hf.integrable_weight, hf.deriv.integrable_weight, hlim] with s hfi hdi hli
  exact LaplaceTransform.laplaceTransform_deriv hf.contDiff hfi hdi hli

private theorem tendsTo_regularLaplace_real_zero {f : ℝ → ℂ} (hf : IsRegularCausalSignal f) :
    Tendsto (fun s : ℝ => LaplaceTransform.laplaceTransform f (s : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, a, -, h⟩ := hf.bound
  refine squeeze_zero_norm' (a := fun s => C / (s - a)) ?_ ?_
  · filter_upwards [eventually_gt_atTop a] with s hs
    have hI := integrableOn_laplace_weight_mul (hf.contDiff (n := 0)).continuous h (s := (s : ℂ)) (by simpa using hs)
    rw [LaplaceTransform.laplaceTransform_eq_integral hI]
    have hG := (integrableOn_exp_mul_Ioi (neg_neg_of_pos (sub_pos.mpr hs)) 0).const_mul C
    have hb : (∫ t : ℝ in Ioi 0, C * Real.exp (-(s - a) * t)) = C / (s - a) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (sub_pos.mpr hs))]
      simp only [mul_zero, Real.exp_zero, div_eq_mul_inv, inv_neg, neg_one_mul, neg_neg]
    rw [← hb]
    apply norm_integral_le_of_norm_le hG
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [smul_eq_mul, Complex.ofReal_re] using norm_laplace_weight_mul_le h (s : ℂ) (le_of_lt ht)
  · exact tendsto_const_nhds.div_atTop (by simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right _ (-a) tendsto_id)

private theorem regularLaplaceGerm_injective {f g : ℝ → ℂ} (hf : IsRegularCausalSignal f)
    (hg : IsRegularCausalSignal g) (heq : regularLaplaceGerm f = regularLaplaceGerm g) : f = g := by
  have hdiff : IsRegularCausalSignal (f - g) := hf.add (by simpa using hg.const_mul (-1))
  have hG : regularLaplaceGerm (f - g) = 0 := by
    have he := regularLaplaceGerm_add hf (hg.const_mul (-1))
    rw [regularLaplaceGerm_const_mul hg] at he
    have hfun : f + (fun t => (-1 : ℂ) * g t) = f - g := by ext t; simp [sub_eq_add_neg]
    rw [hfun, heq, show (↑(-1 : ℂ) : Germ laplaceRightHalfPlane ℂ) = -1 from rfl,
      neg_one_mul, add_neg_cancel] at he
    exact he
  let d := f - g
  have hEventually : ∀ᶠ s in laplaceRightHalfPlane,
      LaplaceTransform.laplaceTransform d s = 0 ∧ IntegrableOn
        (fun t : ℝ => Complex.exp (-(s * t)) * d t) (Ioi 0) :=
    (Germ.coe_eq.mp hG).and hdiff.integrable_weight
  obtain ⟨a, ha⟩ := eventually_laplaceRightHalfPlane.mp hEventually
  let c : ℝ := a + 1
  have hc : a < c := by dsimp [c]; linarith
  let F : ℝ → ℂ := fun t => Complex.exp (-(c * t)) * (Ioi 0).indicator d t
  have hFi : Integrable F := by
    have he : F = (Ioi (0 : ℝ)).indicator (fun t => Complex.exp (-(c * t)) * d t) := by
      funext t
      by_cases h : t ∈ Ioi (0 : ℝ) <;> simp [F, h]
    rw [he, integrable_indicator_iff measurableSet_Ioi]
    simpa only [Complex.ofReal_mul] using (ha (c : ℂ) (by simpa using hc)).2
  have hF : 𝓕 F = 0 := by
    funext u
    let s : ℂ := (c : ℂ) + ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I
    have hs : s.re = c := by simp [s, Complex.mul_re]
    have hi : s.im / (2 * Real.pi) = u := by
      have hp := Real.pi_pos.ne'
      simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      field_simp
    have hS := ha s (hs ▸ hc)
    rw [LaplaceTransform.laplaceTransform_eq_fourier hS.2, hs, hi] at hS
    exact hS.1
  have hpos (t : ℝ) (ht : 0 < t) : f t = g t := by
    have hCt : ContinuousAt F t := by
      have hCont : Continuous (fun t : ℝ => Complex.exp (-(c * t)) * d t) := by
        have : Continuous d := (hdiff.contDiff (n := 0)).continuous
        fun_prop
      apply hCont.continuousAt.congr
      filter_upwards [Ioi_mem_nhds ht] with u hu using by simp [F, hu]
    have h := hFi.fourierInv_fourier_eq (by rw [hF]; exact integrable_zero _ _ _) hCt
    rw [hF] at h
    have hz : (𝓕⁻ (0 : ℝ → ℂ)) t = 0 := by
      rw [Real.fourierInv_eq]
      simp
    rw [hz] at h
    have hh : Complex.exp (-(c * t)) * d t = 0 := by simpa [F, ht] using h.symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (Complex.exp_ne_zero _))
  apply hf.1.eq_of_eventuallyEq hg.1 (z₀ := 1)
  filter_upwards [Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht using hpos t ht

private theorem laplaceGerm_poleSignal (pole : ℂ) (k : ℕ) :
    regularLaplaceGerm (laplacePoleSignal pole k) =
      (↑(fun s : ℂ => (s - pole)⁻¹) : Germ laplaceRightHalfPlane ℂ) ^ (k + 1) := by
  exact Germ.coe_eq.mpr (eventually_laplaceRightHalfPlane.mpr
    ⟨pole.re, fun _ hs => laplaceTransform_poleSignal pole k hs⟩)

private theorem exists_complex_rationalLaplace (r : RatFunc ℝ) :
    ∃ p : ℂ[X], ∃ f : ℝ → ℂ, IsRegularCausalSignal f ∧
      rationalEvalLaplaceGerm Complex.ofRealHom r = polynomialEvalLaplaceGerm (RingHom.id ℂ) p +
        regularLaplaceGerm f := by
  classical
  let 𝒢 := Germ laplaceRightHalfPlane ℂ
  let N := r.num.map Complex.ofRealHom
  let D := r.denom.map Complex.ofRealHom
  let S := D.roots.toFinset
  let n (a : ℂ) := D.rootMultiplicity a
  let g (a : ℂ) : ℂ[X] := X - C a
  let R (a : ℂ) : 𝒢 := (fun s : ℂ => (s - a)⁻¹)
  have hD : D.Monic := r.monic_denom.map _
  have hsplit : D.Splits := IsAlgClosed.splits D
  have hFactor : D = ∏ a ∈ S, g a ^ n a :=
    (hsplit.eq_prod_roots_of_monic hD).trans Polynomial.prod_multiset_root_eq_finset_root
  let : Algebra ℂ[X] 𝒢 := (polynomialEvalLaplaceGerm (RingHom.id ℂ)).toAlgebra
  have hPoly (p : ℂ[X]) : (algebraMap ℂ[X] 𝒢) p = ((fun s : ℂ => p.eval s) : 𝒢) := by
    change (polynomialEvalLaplaceGerm (RingHom.id ℂ)) p = _
    exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => Polynomial.eval₂_id)
  have hR (a : ℂ) : R a * algebraMap ℂ[X] 𝒢 (g a) = 1 := by
    rw [hPoly]
    apply Germ.coe_eq.mpr
    refine eventually_laplaceRightHalfPlane.mpr ⟨a.re, fun s hs => ?_⟩
    change (s - a)⁻¹ * (g a).eval s = 1
    dsimp only [g]
    rw [eval_sub, eval_X, eval_C, inv_mul_cancel₀ (sub_ne_zero.mpr (fun h => (ne_of_gt hs) (congrArg Complex.re h)))]
  obtain ⟨p, c, hc, hpf⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := 𝒢) N (g := g) (s := S) (fun a _ => monic_X_sub_C a)
    (fun {a b} _ _ hn => isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit) n
    (fun a _ => hR a)
  let f := ∑ a ∈ S, ∑ j : Fin (n a), (fun t => (c a j).coeff 0 * laplacePoleSignal a j t)
  have hRats : rationalEvalLaplaceGerm Complex.ofRealHom r =
      algebraMap ℂ[X] 𝒢 N * ∏ a ∈ S, R a ^ n a := by
    have hInv : (∏ a ∈ S, R a ^ n a) * algebraMap ℂ[X] 𝒢 D = 1 := by
      rw [hFactor, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun a _ => ?_
      rw [map_pow, ← mul_pow, hR a, one_pow]
    have hNum : (algebraMap ℂ[X] 𝒢 N) =
        ((fun s : ℂ => r.num.eval₂ Complex.ofRealHom s) : 𝒢) := by
      rw [hPoly]
      exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => (Polynomial.eval₂_eq_eval_map _).symm)
    have hDen : (algebraMap ℂ[X] 𝒢 D) =
        ((fun s : ℂ => r.denom.eval₂ Complex.ofRealHom s) : 𝒢) := by
      rw [hPoly]
      exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => (Polynomial.eval₂_eq_eval_map _).symm)
    have he : rationalEvalLaplaceGerm Complex.ofRealHom r * (algebraMap ℂ[X] 𝒢 D) =
        algebraMap ℂ[X] 𝒢 N := by
      rw [rationalEvalLaplaceGerm_eq_eval, hNum, hDen]
      apply Germ.coe_eq.mpr
      filter_upwards [eventually_evaluate_nonzero Complex.ofRealHom Complex.ofReal_injective r.denom_ne_zero] with s hs
      exact div_mul_cancel₀ _ hs
    rw [← he, mul_assoc, mul_comm (algebraMap ℂ[X] 𝒢 D), hInv, mul_one]
  have hRgl (a : ℂ) (j : Fin (n a)) : IsRegularCausalSignal (fun t => (c a j).coeff 0 * laplacePoleSignal a j t) :=
    (regularCausalSignal_poleSignal _ _).const_mul _
  refine ⟨p, f, regularCausalSignal_sum S _ (fun a _ => regularCausalSignal_sum Finset.univ _ fun j _ => hRgl a j), ?_⟩
  rw [hRats, hpf, regularLaplaceGerm_sum S _ (fun a _ => regularCausalSignal_sum Finset.univ _ fun j _ => hRgl a j)]
  change _ + _ = _ + _
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [regularLaplaceGerm_sum Finset.univ _ (fun j _ => hRgl a j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hconst : c a j = C ((c a j).coeff 0) := by
    have hd := hc a ha j
    rw [show (g a).degree = 1 by exact degree_X_sub_C a] at hd
    apply Polynomial.ext
    intro i
    cases i with
    | zero => simp
    | succ i =>
      have h := (Polynomial.degree_lt_iff_coeff_zero (c a j) 1).mp hd (i + 1) (by omega)
      simpa using h
  have hm : (algebraMap ℂ[X] 𝒢) (c a j) = (↑((c a j).coeff 0) : 𝒢) := by
    conv_lhs => rw [hconst, hPoly]
    exact Germ.coe_eq.mpr (Eventually.of_forall fun s => eval_C)
  rw [hm, regularLaplaceGerm_const_mul (regularCausalSignal_poleSignal _ _), laplaceGerm_poleSignal]

private theorem laplaceTransform_conj_of_integrable {f : ℝ → ℂ} {s : ℂ}
    (hf : IntegrableOn (fun t : ℝ => Complex.exp (-(star s * t)) * f t) (Ioi 0)) :
    LaplaceTransform.laplaceTransform (fun t => star (f t)) s =
      star (LaplaceTransform.laplaceTransform f (star s)) := by
  have he : (fun t : ℝ => Complex.exp (-(s * t)) * star (f t)) =
      fun t : ℝ => star (Complex.exp (-(star s * t)) * f t) := by
    funext t
    simp only [Complex.star_def, map_mul, ← Complex.exp_conj, map_neg,
      starRingEnd_self_apply, Complex.conj_ofReal]
  have hI : IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * star (f t)) (Ioi 0) := by
    rw [he]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
  rw [LaplaceTransform.laplaceTransform_eq_integral hI,
    LaplaceTransform.laplaceTransform_eq_integral hf]
  simp only [smul_eq_mul]
  rw [he]
  exact integral_conj

private noncomputable def complexPolynomialRealPart (p : ℂ[X]) : ℝ[X] :=
  ⟨⟨p.toFinsupp.coeff.mapRange Complex.re (by simp)⟩⟩

private theorem map_complexPolynomialRealPart (p : ℂ[X]) :
    (complexPolynomialRealPart p).map Complex.ofRealHom =
      C ((2 : ℂ)⁻¹) * (p + p.map (starRingEnd ℂ)) := by
  apply Polynomial.ext
  intro k
  rw [coeff_map, coeff_C_mul, coeff_add, coeff_map]
  change ((p.coeff k).re : ℂ) = (2 : ℂ)⁻¹ * (p.coeff k + star (p.coeff k))
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  · simp [Complex.mul_im, Complex.add_re, Complex.add_im]

private theorem eval_conj_map (p : ℂ[X]) (s : ℂ) : (p.map (starRingEnd ℂ)).eval s = star (p.eval (star s)) := by
  rw [← eval₂_eq_eval_map, eval₂_def, eval_eq_sum]
  simp only [Complex.star_def, Polynomial.sum_def, map_sum, map_mul, map_pow, starRingEnd_self_apply]

private theorem realRational_eval_conj (r : RatFunc ℝ) (s : ℂ) :
    star (r.eval Complex.ofRealHom (star s)) = r.eval Complex.ofRealHom s := by
  have hp (p : ℝ[X]) : star (p.eval₂ Complex.ofRealHom (star s)) = p.eval₂ Complex.ofRealHom s := by
    simp only [eval₂_def, Complex.star_def, Polynomial.sum_def, map_sum, map_mul, map_pow,
      Complex.ofRealHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Complex.conj_ofReal,
      starRingEnd_self_apply]
  rw [RatFunc.eval, RatFunc.eval]
  change (starRingEnd ℂ) (_ / _) = _
  rw [map_div₀]
  change star (r.num.eval₂ Complex.ofRealHom (star s)) / star (r.denom.eval₂ Complex.ofRealHom (star s)) = _
  rw [hp, hp]

/-- A causal real signal with impulses at the initial time. Its ordinary
part is the restriction of `regular` to positive time, and the coefficient
of `X^k` in `impulse` multiplies the `k`-th derivative of the Dirac mass. -/
@[ext] structure CausalLaplaceSignal where
  impulse : ℝ[X]
  regular : ℝ → ℂ
  isRegular : IsRegularCausalSignal regular
  isReal : ∀ t, star (regular t) = regular t

/-- The Laplace transform of the causal signal on a right half-plane. -/
noncomputable def causalLaplaceGerm (u : CausalLaplaceSignal) : Germ laplaceRightHalfPlane ℂ :=
  polynomialEvalLaplaceGerm Complex.ofRealHom u.impulse + regularLaplaceGerm u.regular

private theorem causalLaplaceGerm_injective : Function.Injective causalLaplaceGerm := by
  intro u v he
  have h : ∀ᶠ s in laplaceRightHalfPlane,
      u.impulse.eval₂ Complex.ofRealHom s + LaplaceTransform.laplaceTransform u.regular s =
        v.impulse.eval₂ Complex.ofRealHom s + LaplaceTransform.laplaceTransform v.regular s :=
    Germ.coe_eq.mp he
  obtain ⟨a, ha⟩ := eventually_laplaceRightHalfPlane.mp h
  have hr : Tendsto (fun t : ℝ => (u.impulse - v.impulse).eval t) atTop (𝓝 0) := by
    have hlim := (tendsTo_regularLaplace_real_zero v.isRegular).sub (tendsTo_regularLaplace_real_zero u.isRegular)
    have he' := Complex.continuous_re.continuousAt.tendsto.comp hlim
    simp only [Function.comp_def, sub_self, Complex.zero_re] at he'
    apply he'.congr'
    filter_upwards [eventually_gt_atTop a] with t ht
    have h := congrArg Complex.re (ha (t : ℂ) (by simpa using ht))
    have hEval (p : ℝ[X]) : p.eval₂ Complex.ofRealHom (t : ℂ) = Complex.ofReal (p.eval t) :=
      Polynomial.eval₂_at_apply Complex.ofRealHom t
    simp only [hEval, Complex.add_re, Complex.ofReal_re] at h
    rw [eval_sub, Complex.sub_re]
    linarith
  have hp : u.impulse = v.impulse := by
    obtain ⟨h₀, hd⟩ := (Polynomial.tendsto_nhds_iff (u.impulse - v.impulse)).mp hr
    exact sub_eq_zero.mp (leadingCoeff_eq_zero.mp h₀)
  apply CausalLaplaceSignal.ext hp
  apply regularLaplaceGerm_injective u.isRegular v.isRegular
  have hG : polynomialEvalLaplaceGerm Complex.ofRealHom u.impulse + regularLaplaceGerm u.regular =
      polynomialEvalLaplaceGerm Complex.ofRealHom v.impulse + regularLaplaceGerm v.regular := he
  rw [hp] at hG
  exact add_left_cancel hG

private theorem exists_causalLaplaceSignal (r : RatFunc ℝ) :
    ∃ u : CausalLaplaceSignal, causalLaplaceGerm u = rationalEvalLaplaceGerm Complex.ofRealHom r := by
  obtain ⟨p, f, hf, he⟩ := exists_complex_rationalLaplace r
  let fc (t : ℝ) := star (f t)
  let fr (t : ℝ) := (2 : ℂ)⁻¹ * (f t + fc t)
  have hfc : IsRegularCausalSignal fc := hf.conj
  have hfr : IsRegularCausalSignal fr := (hf.add hfc).const_mul _
  have hReal (t : ℝ) : star (fr t) = fr t := by
    simp [fr, fc, add_comm]
  let u : CausalLaplaceSignal := ⟨complexPolynomialRealPart p, fr, hfr, hReal⟩
  refine ⟨u, ?_⟩
  have hL : regularLaplaceGerm fr = (↑((2 : ℂ)⁻¹) : Germ laplaceRightHalfPlane ℂ) *
      (regularLaplaceGerm f + regularLaplaceGerm fc) := by
    change regularLaplaceGerm (fun t => (2 : ℂ)⁻¹ * (f + fc) t) = _
    rw [regularLaplaceGerm_const_mul (hf.add hfc), regularLaplaceGerm_add hf hfc]
  change polynomialEvalLaplaceGerm Complex.ofRealHom (complexPolynomialRealPart p) +
    regularLaplaceGerm fr = rationalEvalLaplaceGerm Complex.ofRealHom r
  rw [hL, rationalEvalLaplaceGerm_eq_eval]
  rw [rationalEvalLaplaceGerm_eq_eval] at he
  have hpf : ∀ᶠ s in laplaceRightHalfPlane,
      r.eval Complex.ofRealHom s = p.eval s + LaplaceTransform.laplaceTransform f s := by
    apply Germ.coe_eq.mp at he
    filter_upwards [he] with s hs
    simpa only [Polynomial.eval₂_id] using hs
  obtain ⟨a, ha⟩ := eventually_laplaceRightHalfPlane.mp (hpf.and hf.integrable_weight)
  apply Germ.coe_eq.mpr
  refine eventually_laplaceRightHalfPlane.mpr ⟨a, fun s hs => ?_⟩
  have hsc : a < (star s).re := by simpa only [Complex.star_def, Complex.conj_re] using hs
  change (complexPolynomialRealPart p).eval₂ Complex.ofRealHom s +
      (2 : ℂ)⁻¹ * (LaplaceTransform.laplaceTransform f s + LaplaceTransform.laplaceTransform fc s) =
    r.eval Complex.ofRealHom s
  rw [eval₂_eq_eval_map, map_complexPolynomialRealPart, eval_mul, eval_C, eval_add, eval_conj_map,
    laplaceTransform_conj_of_integrable (ha _ hsc).2]
  have h₁ := (ha s hs).1
  have h₂ := congrArg star (ha (star s) hsc).1
  rw [realRational_eval_conj, star_add] at h₂
  calc
    _ = (2 : ℂ)⁻¹ * ((p.eval s + LaplaceTransform.laplaceTransform f s) +
        star (p.eval (star s)) + star (LaplaceTransform.laplaceTransform f (star s))) := by ring
    _ = (2 : ℂ)⁻¹ * ((p.eval s + LaplaceTransform.laplaceTransform f s) +
        (star (p.eval (star s)) + star (LaplaceTransform.laplaceTransform f (star s)))) := by ring
    _ = _ := by rw [← h₁, ← h₂]; ring

/-- Causal signals whose analytic Laplace transform is a real rational function. -/
def RationalCausalSignal := {u : CausalLaplaceSignal // ∃ r : RatFunc ℝ,
  causalLaplaceGerm u = rationalEvalLaplaceGerm Complex.ofRealHom r}

/-- The bijective Laplace transform on rational causal signals, including
arbitrary derivatives of the Dirac mass at zero and repeated nonreal poles. -/
noncomputable def rationalLaplaceRepresentation : RationalCausalSignal ≃ RatFunc ℝ := by
  have h : ∀ r : RatFunc ℝ, ∃ u : RationalCausalSignal,
      causalLaplaceGerm u.1 = rationalEvalLaplaceGerm Complex.ofRealHom r := by
    intro r
    obtain ⟨u, h⟩ := exists_causalLaplaceSignal r
    exact ⟨⟨u, r, h⟩, h⟩
  let L (u : RationalCausalSignal) : RatFunc ℝ := Classical.choose u.2
  have hL (u : RationalCausalSignal) : causalLaplaceGerm u.1 = rationalEvalLaplaceGerm Complex.ofRealHom (L u) :=
    Classical.choose_spec u.2
  apply Equiv.ofBijective L
  constructor
  · intro u v he
    apply Subtype.ext
    apply causalLaplaceGerm_injective
    rw [hL u, hL v, he]
  · intro r
    obtain ⟨u, hu⟩ := h r
    exact ⟨u, (rationalEvalLaplaceGerm Complex.ofRealHom).injective ((hL u).symm.trans hu)⟩

/-- The equivalence returns the rational function of the actual causal Laplace integral. -/
theorem causalLaplaceGerm_eq_rationalLaplaceRepresentation (u : RationalCausalSignal) :
    causalLaplaceGerm u.1 = rationalEvalLaplaceGerm Complex.ofRealHom (rationalLaplaceRepresentation u) :=
  Classical.choose_spec u.2

private noncomputable def impulsePairing (p : ℝ[X]) (test : ℝ → ℂ) : ℂ :=
  p.sum fun k c => (c : ℂ) * ((-1 : ℂ) ^ k * iteratedDeriv k test 0)

/-- The linear action of the signal on smooth compactly supported test functions.
The ordinary part acts by integration on positive time and each impulse acts
by the signed derivative of the test function at zero. -/
noncomputable def causalLaplacePairing (u : CausalLaplaceSignal) (test : ℝ → ℂ) : ℂ :=
  (∫ t : ℝ in Ioi 0, u.regular t * test t) + impulsePairing u.impulse test

private theorem impulsePairing_add (p q : ℝ[X]) (test : ℝ → ℂ) :
    impulsePairing (p + q) test = impulsePairing p test + impulsePairing q test := by
  unfold impulsePairing
  exact sum_add_index p q _ (by simp) (by simp [add_mul])

private theorem impulsePairing_C (r : ℝ) (test : ℝ → ℂ) :
    impulsePairing (C r) test = (r : ℂ) * test 0 := by
  simp [impulsePairing, sum_C_index]

private theorem impulsePairing_X_mul (p : ℝ[X]) (test : ℝ → ℂ) :
    impulsePairing (X * p) test = -impulsePairing p (deriv test) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, impulsePairing_add, hp, hq, impulsePairing_add, neg_add]
  | monomial k c =>
    simp only [show (X * monomial k c : ℝ[X]) = monomial (k+1) c by
        rw [mul_comm X, monomial_mul_X]]
    unfold impulsePairing
    rw [sum_monomial_index _ _ (by simp), sum_monomial_index _ _ (by simp), iteratedDeriv_succ', pow_succ]
    ring

/-- The distributional derivative of a causal signal, including the jump
of its ordinary part at the initial time. -/
noncomputable def causalDistributionalDerivative (u : CausalLaplaceSignal) : CausalLaplaceSignal where
  impulse := X * u.impulse + C (u.regular 0).re
  regular := deriv u.regular
  isRegular := u.isRegular.deriv
  isReal t := by
    have hd := (u.isRegular.contDiff (n := 1)).differentiable one_ne_zero t
    have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
    have he : (fun t => Complex.conjCLE.toContinuousLinearMap (u.regular t)) = u.regular := funext u.isReal
    change deriv (fun t => Complex.conjCLE.toContinuousLinearMap (u.regular t)) t = star (deriv u.regular t) at h
    rw [he] at h
    exact h.symm

private theorem real_regular_value (u : CausalLaplaceSignal) (t : ℝ) :
    ((u.regular t).re : ℂ) = u.regular t := by
  exact Complex.conj_eq_iff_re.mp (u.isReal t)

/-- The derivative of the signal is its derivative in the sense of distributions. -/
theorem causalDistributionalDerivative_pairing (u : CausalLaplaceSignal) (test : ℝ → ℂ)
    (hSmooth : ContDiff ℝ 1 test) (hSupport : HasCompactSupport test) :
    causalLaplacePairing (causalDistributionalDerivative u) test = -causalLaplacePairing u (deriv test) := by
  have hreg : ContDiff ℝ 1 u.regular := u.isRegular.contDiff
  have hM : ContDiff ℝ 1 (fun t => u.regular t * test t) := hreg.mul hSmooth
  have hMS : HasCompactSupport (fun t => u.regular t * test t) := hSupport.mul_left
  have hI := HasCompactSupport.integral_Ioi_deriv_eq hM hMS 0
  have h₁ : IntegrableOn (fun t => deriv u.regular t * test t) (Ioi 0) :=
    ((hreg.continuous_deriv le_rfl).mul hSmooth.continuous).integrable_of_hasCompactSupport
      hSupport.mul_left |>.integrableOn
  have h₂ : IntegrableOn (fun t => u.regular t * deriv test t) (Ioi 0) :=
    (hreg.continuous.mul (hSmooth.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hSupport.deriv.mul_left |>.integrableOn
  have he : deriv (fun t => u.regular t * test t) =
      fun t => deriv u.regular t * test t + u.regular t * deriv test t := by
    funext t
    exact ((hreg.differentiable one_ne_zero t).hasDerivAt.fun_mul
      (hSmooth.differentiable one_ne_zero t).hasDerivAt).deriv
  rw [he, integral_add h₁ h₂] at hI
  simp only [causalLaplacePairing, causalDistributionalDerivative, impulsePairing_add,
    impulsePairing_X_mul, impulsePairing_C, real_regular_value]
  linear_combination hI

/-- Applying a polynomial in the Dirac derivatives to the exponential weight
is the polynomial evaluated at its Laplace variable. -/
private theorem impulsePairing_laplace_weight (p : ℝ[X]) (s : ℂ) :
    impulsePairing p (fun t => Complex.exp (-(s * t))) = p.eval₂ Complex.ofRealHom s := by
  have hd (n : ℕ) : iteratedDeriv n (fun t : ℝ => Complex.exp (-(s * t))) =
      fun t : ℝ => (-s)^n * Complex.exp (-(s * t)) := by
    induction n with
    | zero => simp [iteratedDeriv_zero]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hasDerivAt_laplace_weight s t).const_mul ((-s)^n)).deriv, pow_succ, mul_assoc]
  unfold impulsePairing
  rw [eval₂_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hd, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one, ← mul_pow,
    neg_one_mul, neg_neg]
  rfl

/-- The transform agrees with the distributional pairing against the exponential weight
on every sufficiently far right half-plane. -/
theorem causalLaplaceGerm_eq_pairing (u : CausalLaplaceSignal) :
    causalLaplaceGerm u = ((fun s : ℂ => causalLaplacePairing u
      (fun t : ℝ => Complex.exp (-(s * t)))) : Germ laplaceRightHalfPlane ℂ) := by
  apply Germ.coe_eq.mpr
  filter_upwards [u.isRegular.integrable_weight] with s hs
  change u.impulse.eval₂ Complex.ofRealHom s + LaplaceTransform.laplaceTransform u.regular s = _
  rw [LaplaceTransform.laplaceTransform_eq_integral hs, causalLaplacePairing,
    impulsePairing_laplace_weight, add_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => mul_comm _ _

private theorem polynomialEvalLaplaceGerm_X : polynomialEvalLaplaceGerm Complex.ofRealHom X =
    ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) :=
  Germ.coe_eq.mpr (Eventually.of_forall fun _ => Polynomial.eval₂_X _ _)

private theorem polynomialEvalLaplaceGerm_C (r : ℝ) : polynomialEvalLaplaceGerm Complex.ofRealHom (C r) =
    ((r : ℂ) : Germ laplaceRightHalfPlane ℂ) :=
  Germ.coe_eq.mpr (Eventually.of_forall fun _ => Polynomial.eval₂_C _ _)

/-- A distributional time derivative multiplies the Laplace transform by the transform variable. -/
theorem causalLaplaceGerm_derivative (u : CausalLaplaceSignal) :
    causalLaplaceGerm (causalDistributionalDerivative u) =
      ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) * causalLaplaceGerm u := by
  change polynomialEvalLaplaceGerm Complex.ofRealHom (X * u.impulse + C (u.regular 0).re) +
    regularLaplaceGerm (deriv u.regular) = _
  rw [map_add, map_mul, polynomialEvalLaplaceGerm_X, polynomialEvalLaplaceGerm_C,
    regularLaplaceGerm_deriv u.isRegular, real_regular_value]
  unfold causalLaplaceGerm
  rw [mul_add]
  abel

private noncomputable def causalSignalScale (a : ℝ) (u : CausalLaplaceSignal) : CausalLaplaceSignal :=
  ⟨C a * u.impulse, (fun t => (a : ℂ) * u.regular t), u.isRegular.const_mul _, fun t => by
    rw [star_mul, mul_comm, u.isReal]
    simp⟩

private theorem causalSignalScale_germ (a : ℝ) (u : CausalLaplaceSignal) :
    causalLaplaceGerm (causalSignalScale a u) = ((a : ℂ) : Germ laplaceRightHalfPlane ℂ) * causalLaplaceGerm u := by
  unfold causalLaplaceGerm causalSignalScale
  rw [map_mul, polynomialEvalLaplaceGerm_C, regularLaplaceGerm_const_mul u.isRegular, mul_add]

private noncomputable def causalSignalSum {ι : Type*} (S : Finset ι) (f : ι → CausalLaplaceSignal) :
    CausalLaplaceSignal :=
  ⟨∑ i ∈ S, (f i).impulse, ∑ i ∈ S, (f i).regular,
    regularCausalSignal_sum S _ (fun i _ => (f i).isRegular), fun t => by
      simp only [Finset.sum_apply, star_sum, (f _).isReal]⟩

private theorem causalSignalSum_germ {ι : Type*} (S : Finset ι) (f : ι → CausalLaplaceSignal) :
    causalLaplaceGerm (causalSignalSum S f) = ∑ i ∈ S, causalLaplaceGerm (f i) := by
  unfold causalLaplaceGerm causalSignalSum
  rw [map_sum, regularLaplaceGerm_sum S _ (fun i _ => (f i).isRegular), Finset.sum_add_distrib]

private noncomputable def causalInitialCorrection (initial : ℕ → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range k, X ^ (k - 1 - j) * C (initial j)

/-- The `k`-th derivative with prescribed left initial values. Distributional
differentiation of the zero extension introduces the jumps from zero. The
initial correction subtracts the impulse jet of the prescribed prehistory. -/
noncomputable def causalDerivativeWithInitial (u : CausalLaplaceSignal) (initial : ℕ → ℝ) (k : ℕ) :
    CausalLaplaceSignal :=
  let v := causalDistributionalDerivative^[k] u
  {v with impulse := v.impulse - causalInitialCorrection initial k}

private theorem rationalEvalLaplaceGerm_X : rationalEvalLaplaceGerm Complex.ofRealHom RatFunc.X =
    ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) := by
  rw [rationalEvalLaplaceGerm_eq_eval]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => RatFunc.eval_X ..)

private theorem rationalEvalLaplaceGerm_C (r : ℝ) :
    rationalEvalLaplaceGerm Complex.ofRealHom (algebraMap ℝ (RatFunc ℝ) r) =
      ((r : ℂ) : Germ laplaceRightHalfPlane ℂ) := by
  rw [rationalEvalLaplaceGerm_eq_eval]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => RatFunc.eval_C ..)

private theorem causalLaplaceGerm_iterate (u : CausalLaplaceSignal) (k : ℕ) :
    causalLaplaceGerm (causalDistributionalDerivative^[k] u) =
      ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) ^ k * causalLaplaceGerm u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', causalLaplaceGerm_derivative, ih, ← mul_assoc, pow_succ']

/-- The transform law for a causal derivative and an arbitrary left initial jet. -/
theorem causalLaplaceGerm_derivativeWithInitial (u : CausalLaplaceSignal) (initial : ℕ → ℝ) (k : ℕ) :
    causalLaplaceGerm (causalDerivativeWithInitial u initial k) =
      ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) ^ k * causalLaplaceGerm u -
      ∑ j ∈ Finset.range k, ((id : ℂ → ℂ) : Germ laplaceRightHalfPlane ℂ) ^ (k - 1 - j) *
        ((initial j : ℂ) : Germ laplaceRightHalfPlane ℂ) := by
  let v := causalDistributionalDerivative^[k] u
  have h := causalLaplaceGerm_iterate u k
  rw [← h]
  unfold causalDerivativeWithInitial causalLaplaceGerm causalInitialCorrection
  rw [map_sub, map_sum, sub_add_eq_add_sub]
  simp only [map_mul, map_pow, polynomialEvalLaplaceGerm_X, polynomialEvalLaplaceGerm_C]

private noncomputable def rationalCausalZero : RationalCausalSignal := by
  let z : CausalLaplaceSignal := ⟨0, 0, regularCausalSignal_zero, fun _ => star_zero _⟩
  refine ⟨z, 0, ?_⟩
  change polynomialEvalLaplaceGerm Complex.ofRealHom 0 + regularLaplaceGerm 0 = _
  rw [map_zero, regularLaplaceGerm_zero, add_zero, map_zero]

noncomputable instance : Zero RationalCausalSignal := ⟨rationalCausalZero⟩

private theorem rationalLaplaceRepresentation_zero : rationalLaplaceRepresentation 0 = 0 := by
  apply (rationalEvalLaplaceGerm Complex.ofRealHom).injective
  rw [← causalLaplaceGerm_eq_rationalLaplaceRepresentation]
  change polynomialEvalLaplaceGerm Complex.ofRealHom 0 + regularLaplaceGerm 0 = _
  rw [map_zero, regularLaplaceGerm_zero, add_zero, map_zero]

section RationalDifferentialSystem

variable {m n : Type*} [Fintype n] {q : ℕ}

private noncomputable def causalDifferentialApply (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) (x : n → RationalCausalSignal) (i : m) : CausalLaplaceSignal :=
  causalSignalSum Finset.univ fun k => causalSignalSum Finset.univ fun j =>
    causalSignalScale (A k i j) (causalDerivativeWithInitial (x j).1 (fun l => initial l j) k)

private theorem causalLaplaceGerm_differentialApply (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) (x : n → RationalCausalSignal) (i : m) :
    causalLaplaceGerm (causalDifferentialApply A initial x i) =
      rationalEvalLaplaceGerm Complex.ofRealHom
        ((differentialMatrixPolynomial A *ᵥ (fun j => rationalLaplaceRepresentation (x j))) i -
         differentialInitialPolynomial A initial i) := by
  unfold causalDifferentialApply differentialMatrixPolynomial differentialInitialPolynomial
  simp only [causalSignalSum_germ, causalSignalScale_germ, causalLaplaceGerm_derivativeWithInitial,
    causalLaplaceGerm_eq_rationalLaplaceRepresentation, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sub,
    map_sum, map_mul, map_pow, rationalEvalLaplaceGerm_X, rationalEvalLaplaceGerm_C]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The matrix differential operator on rational causal signals with the prescribed left initial jet. -/
noncomputable def rationalCausalDifferentialApply (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) (x : n → RationalCausalSignal) (i : m) : RationalCausalSignal :=
  ⟨causalDifferentialApply A initial x i, _, causalLaplaceGerm_differentialApply A initial x i⟩

/-- Equation (82) for the concrete causal signal class, including the impulse terms. -/
theorem rationalLaplaceRepresentation_differentialApply (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) (x : n → RationalCausalSignal) :
    (fun i => rationalLaplaceRepresentation (rationalCausalDifferentialApply A initial x i)) =
      differentialMatrixPolynomial A *ᵥ (fun j => rationalLaplaceRepresentation (x j)) -
        differentialInitialPolynomial A initial := by
  funext i
  apply (rationalEvalLaplaceGerm Complex.ofRealHom).injective
  rw [← causalLaplaceGerm_eq_rationalLaplaceRepresentation]
  exact causalLaplaceGerm_differentialApply A initial x i

/-- Theorem 6 of [benIsrael2003generalized], Chapter 8, on concrete rational causal signals.
The rational consistency test and inverse-transform solution include impulses and their derivatives. -/
theorem theorem_6_rationalCausal [Fintype m] [DecidableEq n] (A : Fin (q + 1) → Matrix m n ℝ)
    (initial : ℕ → n → ℝ) :
    let M := differentialMatrixPolynomial A
    let b := differentialInitialPolynomial A initial
    ((∃ x, rationalCausalDifferentialApply A initial x = 0) ↔
      M *ᵥ (rationalPseudoinverse M *ᵥ b) = b) ∧
    (M *ᵥ (rationalPseudoinverse M *ᵥ b) = b → ∀ x,
      rationalCausalDifferentialApply A initial x = 0 ↔ ∃ y, x = fun i =>
        rationalLaplaceRepresentation.symm (rationalSystemCandidate M b y i)) := by
  classical
  let L₁ := Equiv.piCongrRight fun _ : n => rationalLaplaceRepresentation
  let L₂ := Equiv.piCongrRight fun _ : m => rationalLaplaceRepresentation
  have h₀ : L₂ 0 = 0 := funext fun _ => rationalLaplaceRepresentation_zero
  exact theorem_6_of_laplace_representation A initial L₁ L₂ h₀
    (rationalCausalDifferentialApply A initial) (rationalLaplaceRepresentation_differentialApply A initial)

end RationalDifferentialSystem

end ConcreteCausalSignals

end BenIsraelGreville.Chapter08
