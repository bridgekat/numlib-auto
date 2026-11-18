/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section04
import Numlib.Analysis.SpecialFunctions.LaplaceTransform
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Matrix differential systems in Laplace coordinates

Section 8.6 of [benIsrael2003generalized] describes solving homogeneous
differential systems with initial data by using a generalized inverse over
the field of real rational functions.
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

end BenIsraelGreville.Chapter08
