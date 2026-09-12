import Numlib.Krylov.CG
import Numlib.Krylov.CR
import Numlib.Krylov.Iterate
import Numlib.Krylov.Monotonicity
import NumlibSurface.FongSaunders.Section02

/-!
# Fong–Saunders §3: normwise relative backward errors and stopping rules

Surface file for D. C.-L. Fong and M. A. Saunders, *CG versus MINRES: an empirical comparison*, SQU
Journal for Science **17** (2012) 44–62 (Report SOL 2011-2R), §3.

§3 measures an approximate solution `x_k` by the smallest perturbation `(A + E) x_k = b + f` it
solves exactly, with `‖E‖/‖A‖ ≤ α ξ` and `‖f‖/‖b‖ ≤ β ξ`; the matrix norm is the Frobenius norm.
Contents: the definition (3.1) of an acceptable solution, the optimal perturbations (3.2)–(3.3)
and the closed form of the normwise relative backward error `ξ_k`, the stopping rule (3.4), the
norms (3.5)–(3.6), the remark that `φ_k` decreases for CG and MINRES, and Theorem 3.1.

The paper's ratios `‖E‖/‖A‖` and `‖f‖/‖b‖` are transcribed literally, so the statements about
the optimal perturbation carry the hypotheses `A ≠ 0` and `b ≠ 0` that the paper leaves implicit:
Lean's `t / 0 = 0` would otherwise make every perturbation of a zero matrix feasible.
-/

namespace FongSaunders

open Krylov Matrix

open scoped Matrix.Norms.Frobenius

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Vec n} {α β : ℝ}

/-! ### Linearity of the product in the matrix, and two Frobenius-norm lemmas

The backbone (`Numlib/LinearSolve/Perturbation.lean`) proves the Rigal–Gaches theorem with the
*operator* norm on `E →L[𝕜] E`.  The paper uses the Frobenius norm, so the surface reproves the
two norm facts the argument needs; everything else is the same computation. -/

/-- The product is additive in the matrix, as needed for the perturbed system `(A + E) x`. -/
theorem add_mulVecE (E F : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    (E + F) ⬝ x = E ⬝ x + F ⬝ x := by
  change Matrix.toEuclideanLin (E + F) x
    = Matrix.toEuclideanLin E x + Matrix.toEuclideanLin F x
  rw [map_add, LinearMap.add_apply]

/-- The product is homogeneous in the matrix. -/
theorem smul_mulVecE (c : ℝ) (E : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    (c • E) ⬝ x = c • (E ⬝ x) := by
  change Matrix.toEuclideanLin (c • E) x = c • Matrix.toEuclideanLin E x
  rw [map_smul, LinearMap.smul_apply]

/-- The Frobenius norm of a rank-one matrix `r xᵀ` is `‖r‖ ‖x‖`. -/
theorem frobenius_norm_vecMulVec {m k : Type*} [Fintype m] [Fintype k] (w : m → ℝ) (v : k → ℝ) :
    ‖Matrix.vecMulVec w v‖
      = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ m)‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ k)‖ := by
  rw [Matrix.frobenius_norm_def, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow]
  congr 1
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.vecMulVec_apply, Real.rpow_two, norm_mul, mul_pow]

/-- The Frobenius norm dominates the Euclidean operator norm: `‖E x‖ ≤ ‖E‖ ‖x‖`. -/
theorem norm_mulVecE_le_frobenius (E : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) :
    ‖E ⬝ x‖ ≤ ‖E‖ * ‖x‖ := by
  have hone : ‖(WithLp.toLp 2 (fun _ : Unit => (1 : ℝ)) : EuclideanSpace ℝ Unit)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp
  have hcol : ∀ u : Vec n, ‖Matrix.vecMulVec (WithLp.ofLp u) fun _ : Unit => (1 : ℝ)‖ = ‖u‖ := by
    intro u
    rw [frobenius_norm_vecMulVec, hone, mul_one]
  have hmul : E * Matrix.vecMulVec (WithLp.ofLp x) (fun _ : Unit => (1 : ℝ))
      = Matrix.vecMulVec (WithLp.ofLp (E ⬝ x)) fun _ : Unit => (1 : ℝ) :=
    Matrix.mul_vecMulVec _ _ _
  calc ‖E ⬝ x‖ = ‖E * Matrix.vecMulVec (WithLp.ofLp x) fun _ : Unit => (1 : ℝ)‖ := by
        rw [hmul, hcol]
    _ ≤ ‖E‖ * ‖Matrix.vecMulVec (WithLp.ofLp x) fun _ : Unit => (1 : ℝ)‖ :=
        Matrix.frobenius_norm_mul _ _
    _ = ‖E‖ * ‖x‖ := by rw [hcol]

/-- A rank-one matrix applied to a vector: `(u vᵀ) w = (vᵀ w) u`. -/
theorem mulVecE_vecMulVec (u v w : Vec n) :
    Matrix.vecMulVec (WithLp.ofLp u) (WithLp.ofLp v) ⬝ w = ⟪v, w⟫_ℝ • u := by
  ext i
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_assoc]
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### D9: acceptable solutions and the normwise relative backward error -/

/-- (3.1): `x` is an *acceptable* solution for the tolerances `α, β` if it solves exactly a
system perturbed by at most those relative amounts. -/
def IsAcceptable (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : Prop :=
  ∃ (E : Matrix (Fin n) (Fin n) ℝ) (f : Vec n),
    (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α ∧ ‖f‖ / ‖b‖ ≤ β

/-- The feasible set of the optimization problem defining the normwise relative backward
error. -/
def nrbeFeasible (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : Set ℝ :=
  {ξ : ℝ | ∃ (E : Matrix (Fin n) (Fin n) ℝ) (f : Vec n),
    (A + E) ⬝ x = b + f ∧ ‖E‖ / ‖A‖ ≤ α * ξ ∧ ‖f‖ / ‖b‖ ≤ β * ξ}

/-- (3.2): the normwise relative backward error `ξ_k = ‖r_k‖ / (α ‖A‖ ‖x_k‖ + β ‖b‖)`. -/
noncomputable def nrbe (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : ℝ :=
  ‖b - A ⬝ x‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)

/-- (3.2): the weight `φ_k = β ‖b‖ / (α ‖A‖ ‖x_k‖ + β ‖b‖)`. -/
noncomputable def nrbePhi (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) : ℝ :=
  β * ‖b‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖)

/-- (3.3): the optimal matrix perturbation `E_k = ((1 − φ_k)/‖x_k‖²) r_k x_kᵀ`. -/
noncomputable def nrbePertA (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((1 - nrbePhi A b α β x) / ‖x‖ ^ 2) •
    Matrix.vecMulVec (WithLp.ofLp (b - A ⬝ x)) (WithLp.ofLp x)

/-- (3.3): the optimal right-hand-side perturbation `f_k = −φ_k r_k`. -/
noncomputable def nrbePertb (A : Matrix (Fin n) (Fin n) ℝ) (b : Vec n) (α β : ℝ) (x : Vec n) :
    Vec n :=
  -nrbePhi A b α β x • (b - A ⬝ x)

/-- `0 ≤ φ_k`. -/
theorem nrbePhi_nonneg (x : Vec n) (hβ : 0 ≤ β) (hden : 0 ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    0 ≤ nrbePhi A b α β x :=
  div_nonneg (mul_nonneg hβ (norm_nonneg b)) hden

/-- `1 − φ_k = α ‖A‖ ‖x_k‖ / (α ‖A‖ ‖x_k‖ + β ‖b‖)`. -/
theorem one_sub_nrbePhi {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    1 - nrbePhi A b α β x = α * ‖A‖ * ‖x‖ / (α * ‖A‖ * ‖x‖ + β * ‖b‖) := by
  rw [nrbePhi, eq_div_iff hden.ne', sub_mul, one_mul, div_mul_cancel₀ _ hden.ne']
  ring

/-- `0 ≤ 1 − φ_k`, the coefficient of the optimal matrix perturbation `E_k`. -/
theorem one_sub_nrbePhi_nonneg (hα : 0 ≤ α) {x : Vec n}
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) : 0 ≤ 1 - nrbePhi A b α β x := by
  rw [one_sub_nrbePhi hden]
  positivity

/-! ### R3.4: (3.5)–(3.6), the norms of the optimal perturbations -/

/-- (3.5): `‖E_k‖ = (1 − φ_k) ‖r_k‖ / ‖x_k‖`. -/
theorem norm_nrbePertA (hα : 0 ≤ α) {x : Vec n} (hx : x ≠ 0)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertA A b α β x‖ = (1 - nrbePhi A b α β x) * ‖b - A ⬝ x‖ / ‖x‖ := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have hnn : (0 : ℝ) ≤ (1 - nrbePhi A b α β x) / ‖x‖ ^ 2 :=
    div_nonneg (one_sub_nrbePhi_nonneg hα hden) (sq_nonneg _)
  rw [nrbePertA, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn, frobenius_norm_vecMulVec]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (b - A ⬝ x)) : Vec n) = b - A ⬝ x := rfl
  have h2 : (WithLp.toLp 2 (WithLp.ofLp x) : Vec n) = x := rfl
  rw [h1, h2]
  field_simp

/-- (3.6): `‖f_k‖ = φ_k ‖r_k‖`. -/
theorem norm_nrbePertb (hβ : 0 ≤ β) {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertb A b α β x‖ = nrbePhi A b α β x * ‖b - A ⬝ x‖ := by
  rw [nrbePertb, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (nrbePhi_nonneg x hβ hden.le)]

/-- (3.6) in relative form: `‖f_k‖/‖b‖ = β ξ_k`, valid for every `x_k` (including `x_k = 0`). -/
theorem norm_nrbePertb_div (hb0 : b ≠ 0) (hβ : 0 ≤ β) {x : Vec n}
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x := by
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb0
  rw [norm_nrbePertb hβ hden, nrbePhi, nrbe]
  field_simp

/-- (3.5) in relative form: `‖E_k‖/‖A‖ = α ξ_k` for `x_k ≠ 0`. -/
theorem norm_nrbePertA_div (hA0 : A ≠ 0) (hα : 0 ≤ α) {x : Vec n} (hx : x ≠ 0)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  have hAn : (0 : ℝ) < ‖A‖ := norm_pos_iff.2 hA0
  rw [norm_nrbePertA hα hx hden, one_sub_nrbePhi hden, nrbe]
  field_simp

/-! ### R3.1: (3.2)–(3.3), the optimal perturbation attains the backward error -/

/-- The optimal perturbations of (3.3) are feasible and attain the value `ξ_k`. -/
theorem nrbePert_attains (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : Vec n}
    (hx : x ≠ 0) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    (A + nrbePertA A b α β x) ⬝ x = b + nrbePertb A b α β x ∧
      ‖nrbePertA A b α β x‖ / ‖A‖ = α * nrbe A b α β x ∧
        ‖nrbePertb A b α β x‖ / ‖b‖ = β * nrbe A b α β x := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨?_, norm_nrbePertA_div hA0 hα hx hden, norm_nrbePertb_div hb0 hβ hden⟩
  have happ : nrbePertA A b α β x ⬝ x = (1 - nrbePhi A b α β x) • (b - A ⬝ x) := by
    rw [nrbePertA, smul_mulVecE, mulVecE_vecMulVec, real_inner_self_eq_norm_sq, smul_smul,
      div_mul_cancel₀ _ (by positivity : (‖x‖ : ℝ) ^ 2 ≠ 0)]
  have hAx : A ⬝ x = b - (b - A ⬝ x) := by abel
  rw [add_mulVecE, happ, nrbePertb, hAx]
  module

/-- R3.1: `ξ_k` is the optimal value of the problem `min ξ` of §3. -/
theorem nrbe_isLeast (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x : Vec n)
    (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    IsLeast (nrbeFeasible A b α β x) (nrbe A b α β x) := by
  have hAn : (0 : ℝ) < ‖A‖ := norm_pos_iff.2 hA0
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb0
  constructor
  · rcases eq_or_ne x 0 with rfl | hx
    · have hβ0 : 0 < β := by
        rcases eq_or_lt_of_le hβ with h | h
        · exfalso
          rw [← h] at hden
          simp at hden
        · exact h
      have hnr : nrbe A b α β 0 = 1 / β := by
        rw [nrbe]
        simp only [mulVecE_zero, sub_zero, norm_zero, mul_zero, zero_add]
        rw [mul_comm β ‖b‖, ← div_div, div_self hbn.ne']
      refine ⟨0, -b, by simp, ?_, ?_⟩
      · rw [norm_zero, zero_div, hnr]
        exact mul_nonneg hα (by positivity)
      · rw [norm_neg, div_self hbn.ne', hnr, mul_one_div, div_self hβ0.ne']
    · obtain ⟨h1, h2, h3⟩ := nrbePert_attains hA0 hb0 hα hβ hx hden
      exact ⟨_, _, h1, h2.le, h3.le⟩
  · rintro ξ ⟨E, f, hEf, hE, hf⟩
    rw [add_mulVecE] at hEf
    have hres : b - A ⬝ x = E ⬝ x - f := by
      have hb' : b = A ⬝ x + E ⬝ x - f := by rw [hEf]; abel
      rw [hb']
      abel
    have hEle : ‖E‖ ≤ α * ξ * ‖A‖ := (div_le_iff₀ hAn).1 hE
    have hfle : ‖f‖ ≤ β * ξ * ‖b‖ := (div_le_iff₀ hbn).1 hf
    rw [nrbe, div_le_iff₀ hden]
    calc ‖b - A ⬝ x‖ = ‖E ⬝ x - f‖ := by rw [hres]
      _ ≤ ‖E ⬝ x‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ ‖E‖ * ‖x‖ + ‖f‖ := by gcongr; exact norm_mulVecE_le_frobenius E x
      _ ≤ α * ξ * ‖A‖ * ‖x‖ + β * ξ * ‖b‖ := by gcongr
      _ = ξ * (α * ‖A‖ * ‖x‖ + β * ‖b‖) := by ring

/-! ### R3.2 and R3.3: acceptability and the stopping rule (3.4) -/

/-- R3.3, the stopping rule (3.4): `ξ_k ≤ 1` iff `‖r_k‖ ≤ α ‖A‖ ‖x_k‖ + β ‖b‖`. -/
theorem nrbe_le_one_iff (α β : ℝ) (x : Vec n) (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    nrbe A b α β x ≤ 1 ↔ ‖b - A ⬝ x‖ ≤ α * ‖A‖ * ‖x‖ + β * ‖b‖ := by
  rw [nrbe, div_le_one hden]

/-- R3.2: `x_k` is an acceptable solution exactly when `ξ_k ≤ 1`. -/
theorem isAcceptable_iff_nrbe_le_one (hA0 : A ≠ 0) (hb0 : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {x : Vec n} (hden : 0 < α * ‖A‖ * ‖x‖ + β * ‖b‖) :
    IsAcceptable A b α β x ↔ nrbe A b α β x ≤ 1 := by
  constructor
  · rintro ⟨E, f, hEf, hE, hf⟩
    exact (nrbe_isLeast hA0 hb0 hα hβ x hden).2
      ⟨E, f, hEf, by rwa [mul_one], by rwa [mul_one]⟩
  · intro h
    obtain ⟨E, f, hEf, hE, hf⟩ := (nrbe_isLeast hA0 hb0 hα hβ x hden).1
    refine ⟨E, f, hEf, hE.trans ?_, hf.trans ?_⟩
    · calc α * nrbe A b α β x ≤ α * 1 := by gcongr
        _ = α := mul_one α
    · calc β * nrbe A b α β x ≤ β * 1 := by gcongr
        _ = β := mul_one β

/-! ### R3.5: `φ_k` decreases for CG and MINRES (§3.2) -/

/-- `φ` is antitone along any sequence of iterates with nondecreasing norms. -/
theorem nrbePhi_antitone_of_monotone (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : ℕ → Vec n}
    (hmono : Monotone fun k => ‖x k‖) : Antitone fun k => nrbePhi A b α β (x k) := by
  intro i j hij
  simp only [nrbePhi]
  have hnum : 0 ≤ β * ‖b‖ := mul_nonneg hβ (norm_nonneg b)
  have haA : 0 ≤ α * ‖A‖ := mul_nonneg hα (norm_nonneg A)
  have hle : ‖x i‖ ≤ ‖x j‖ := hmono hij
  have hd : α * ‖A‖ * ‖x i‖ + β * ‖b‖ ≤ α * ‖A‖ * ‖x j‖ + β * ‖b‖ := by nlinarith
  rcases eq_or_lt_of_le hnum with h0 | h0
  · simp [← h0]
  · have hden : ∀ k : ℕ, 0 < α * ‖A‖ * ‖x k‖ + β * ‖b‖ := fun k => by
      nlinarith [norm_nonneg (x k)]
    rw [div_le_div_iff₀ (hden j) (hden i)]
    exact mul_le_mul_of_nonneg_left hd hnum

/-- R3.5 for CG: `φ_k` decreases monotonically. -/
theorem nrbePhi_cg_antitone (hA : A.PosDef) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Antitone fun k => nrbePhi A b α β (cg A b k).x := by
  refine nrbePhi_antitone_of_monotone hα hβ ?_
  simp only [cg_x]
  exact CG.norm_iterate_monotone b (isSymmetricCoercive_of_posDef hA)

/-- R3.5 for MINRES: `φ_k` decreases monotonically. -/
theorem nrbePhi_minres_antitone (hA : A.PosDef) (hα : 0 ≤ α) (hβ : 0 ≤ β) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) : Antitone fun k => nrbePhi A b α β (x k) :=
  nrbePhi_antitone_of_monotone hα hβ (theorem_2_3_minres hA hx)

/-! ### R3.6: Theorem 3.1 -/

/-- A MINRES iterate is nonzero from step `1` on, so the ratio `‖r_k‖/‖x_k‖` is meaningful
there. -/
theorem minres_iterate_ne_zero (hA : A.PosDef) (hb : b ≠ 0) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) {k : ℕ} (hk : 1 ≤ k) : x k ≠ 0 := by
  have h1 : x 1 ≠ 0 := by
    rw [Krylov.IsMinResidualIterate.eq_CR_iterate (isSymmetricCoercive_of_posDef hA)
      (isMINRESIterate_iff.1 (hx 1))]
    exact CR.iterate_one_x_ne_zero b (isSymmetricCoercive_of_posDef hA) hb
  have hmono := theorem_2_3_minres hA hx hk
  simp only at hmono
  exact norm_pos_iff.1 (lt_of_lt_of_le (norm_pos_iff.2 h1) hmono)

/-- R3.6: the normwise relative backward error decreases monotonically for MINRES (`β > 0`). -/
theorem nrbe_minres_antitone (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 ≤ α) (hβ : 0 < β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    Antitone fun k => nrbe A b α β (x k) :=
  Krylov.IsMinResidualIterate.backwardError_antitone (isSymmetricCoercive_of_posDef hA)
    (fun k => isMINRESIterate_iff.1 (hx k)) hα hβ (norm_nonneg A) hb

/-- R3.6 with `β = 0` allowed: on `k ≥ 1` the backward error is still antitone.  The restriction
to `Set.Ici 1` is necessary in Lean: at `k = 0` the ratio `‖r_0‖/‖x_0‖` is `‖b‖/0 = 0`. -/
theorem nrbe_minres_antitoneOn (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 ≤ β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    AntitoneOn (fun k => nrbe A b α β (x k)) (Set.Ici 1) := by
  rcases eq_or_lt_of_le hβ with hβ0 | hβ0
  · have hkey := Krylov.IsMinResidualIterate.norm_residual_div_norm_antitoneOn
      (isSymmetricCoercive_of_posDef hA) (fun k => isMINRESIterate_iff.1 (hx k)) hb
    have hrw : ∀ y : Vec n, nrbe A b α β y = (α * ‖A‖)⁻¹ * (‖b - A ⬝ y‖ / ‖y‖) := by
      intro y
      rw [nrbe, ← hβ0, zero_mul, add_zero, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
      ring
    intro i hi j hj hij
    have h := hkey hi hj hij
    simp only at h
    simp only [hrw]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  · exact (nrbe_minres_antitone hA hb hα.le hβ0 hx).antitoneOn _

/-- Theorem 3.1 for MINRES: for `α, β > 0` the relative backward errors `‖E_k‖/‖A‖` and
`‖f_k‖/‖b‖` decrease monotonically.  The row for `‖E_k‖/‖A‖` starts at `k = 1`: at `k = 0` the
paper's `E_0` is undefined and Lean's is `0`. -/
theorem theorem_3_1_minres (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 < β)
    {x : ℕ → Vec n} (hx : ∀ k, IsMINRESIterate A b k (x k)) :
    AntitoneOn (fun k => ‖nrbePertA A b α β (x k)‖ / ‖A‖) (Set.Ici 1) ∧
      Antitone fun k => ‖nrbePertb A b α β (x k)‖ / ‖b‖ := by
  have hA0 : A ≠ 0 := ne_zero_of_posDef hA hb
  have hbn : (0 : ℝ) < ‖b‖ := norm_pos_iff.2 hb
  have hden : ∀ y : Vec n, 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖ := fun y => by
    have h1 : 0 ≤ α * ‖A‖ * ‖y‖ := by positivity
    have h2 : 0 < β * ‖b‖ := by positivity
    linarith
  constructor
  · intro i hi j hj hij
    have ei := norm_nrbePertA_div hA0 hα.le
      (minres_iterate_ne_zero hA hb hx (Set.mem_Ici.1 hi)) (hden (x i))
    have ej := norm_nrbePertA_div hA0 hα.le
      (minres_iterate_ne_zero hA hb hx (Set.mem_Ici.1 hj)) (hden (x j))
    simp only [ei, ej]
    exact mul_le_mul_of_nonneg_left (nrbe_minres_antitone hA hb hα.le hβ hx hij) hα.le
  · intro i j hij
    simp only [norm_nrbePertb_div hb hβ.le (hden (x i)), norm_nrbePertb_div hb hβ.le (hden (x j))]
    exact mul_le_mul_of_nonneg_left (nrbe_minres_antitone hA hb hα.le hβ hx hij) hβ.le

/-- Theorem 3.1 for CR. -/
theorem theorem_3_1_cr (hA : A.PosDef) (hb : b ≠ 0) (hα : 0 < α) (hβ : 0 < β) :
    AntitoneOn (fun k => ‖nrbePertA A b α β (cr A b k).x‖ / ‖A‖) (Set.Ici 1) ∧
      Antitone fun k => ‖nrbePertb A b α β (cr A b k).x‖ / ‖b‖ :=
  theorem_3_1_minres hA hb hα hβ (cr_isMINRESIterate hA)

/-! ### R3.7: MINRES stops no later than CG under the rule (3.4) with `α = 0` -/

/-- The MINRES residual never exceeds the CG residual at the same step. -/
theorem minres_norm_residual_le_cg (hA : A.PosDef) (k : ℕ) {x : Vec n}
    (hx : IsMINRESIterate A b k x) : ‖b - A ⬝ x‖ ≤ ‖(cg A b k).r‖ := by
  rw [cg_residual_eq]
  exact hx.2 _ (cg_mem_krylov hA k)

/-- With the stopping rule `‖r_k‖ ≤ β ‖b‖` (rule (3.4) with `α = 0`) MINRES stops no later
than CG. -/
theorem minres_stops_first (hA : A.PosDef) (β : ℝ) {x : ℕ → Vec n}
    (hx : ∀ k, IsMINRESIterate A b k (x k)) (k : ℕ) (hcg : ‖(cg A b k).r‖ ≤ β * ‖b‖) :
    ‖b - A ⬝ x k‖ ≤ β * ‖b‖ :=
  (minres_norm_residual_le_cg hA k (hx k)).trans hcg

end FongSaunders
