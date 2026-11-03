import Mathlib.Analysis.Matrix.PosDef
import Numlib.Eigen.InverseEigenvalue
import Mathlib.Algebra.Order.Star.Real
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Eigen.Sturm
import Numlib.Krylov.Preconditioned
import Numlib.Optimization.Subproblem.Krylov
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Lanczos trust-region subproblem

Section 7.5 of [conn2000trust].
-/

namespace ConnGouldToint.Chapter07

open Matrix

/-- The bottom-left inverse entry is the signed product of the subdiagonal entries
over the determinant. The deleted first row and last column leave an upper
triangular minor. -/
theorem inv_apply_last_zero_of_isUpperHessenberg {k : ℕ}
    (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (hA : A.IsUpperHessenberg) :
    A⁻¹ (Fin.last k) 0 = (-1 : ℝ) ^ k *
      (∏ i : Fin k, A i.succ i.castSucc) / A.det := by
  have hminor : (A.submatrix Fin.succ Fin.castSucc).IsUpperTriangular := by
    intro i j hij
    exact hA i.succ j.castSucc ⟨i.castSucc, by simpa using hij, by simp [Fin.lt_def]⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, Fin.val_last, zero_add, Fin.succAbove_zero,
    Fin.succAbove_last, Matrix.det_of_isUpperTriangular hminor, Matrix.submatrix_apply]
  rw [div_eq_mul_inv, mul_comm]

/-- Lemma 7.5.3. In the Lanczos coordinates the gradient after solving the
leading block has support in its next coordinate. In the sign, the exponent
`k + 1` includes the book's separate case `k = 0`. The vanishing criterion
uses a nonzero initial gradient and nonzero earlier subdiagonal entries. -/
theorem lemma_7_5_3 {k : ℕ}
    (T : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) (hT : T.IsTridiagonal)
    (γ : ℝ) (hγ : γ ≠ 0)
    (hprev : ∀ i : Fin k, T i.succ.castSucc i.castSucc.castSucc ≠ 0)
    (hdet : (T.submatrix Fin.castSucc Fin.castSucc).det ≠ 0) :
    let A := T.submatrix Fin.castSucc Fin.castSucc
    let s := Fin.snoc (-(A⁻¹ *ᵥ Pi.single 0 γ)) 0
    let r := Pi.single 0 γ + T *ᵥ s
    let β := T (Fin.last (k + 1)) (Fin.last k).castSucc
    r = Pi.single (Fin.last (k + 1))
        ((-1 : ℝ) ^ (k + 1) * γ * (∏ i : Fin (k + 1), T i.succ i.castSucc) / A.det) ∧
      ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin (k + 2)))‖ ^ 2 =
        γ ^ 2 * (∏ i : Fin (k + 1), T i.succ i.castSucc ^ 2) / A.det ^ 2 ∧
      (r = 0 ↔ β = 0) := by
  classical
  dsimp only
  let A := T.submatrix Fin.castSucc Fin.castSucc
  let x := A⁻¹ *ᵥ Pi.single 0 γ
  let β := T (Fin.last (k + 1)) (Fin.last k).castSucc
  let r := Pi.single (0 : Fin (k + 2)) γ + T *ᵥ Fin.snoc (-x) 0
  let c := (-1 : ℝ) ^ (k + 1) * γ * (∏ i : Fin (k + 1), T i.succ i.castSucc) / A.det
  change r = Pi.single (Fin.last (k + 1)) c ∧ _ ∧ (r = 0 ↔ β = 0)
  have hA : A.IsUpperHessenberg :=
    hT.isUpperHessenberg.submatrix_of_strictMono (fun _ _ h => Fin.castSucc_lt_castSucc_iff.mpr h)
  have hx : A *ᵥ x = Pi.single 0 γ := by
    let : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hdet)
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hprod : (∏ i : Fin (k + 1), T i.succ i.castSucc) =
      (∏ i : Fin k, A i.succ i.castSucc) * β := by
    rw [Fin.prod_univ_castSucc]
    simp only [A, β, Matrix.submatrix_apply, Fin.succ_castSucc, Fin.succ_last]
  have hc : c = -(β * x (Fin.last k)) := by
    dsimp only [c, x]
    rw [hprod, Matrix.mulVec_single]
    change _ = -(β * ((A⁻¹) (Fin.last k) 0 * γ))
    rw [inv_apply_last_zero_of_isUpperHessenberg A hA, pow_succ]
    ring
  have hr : r = Pi.single (Fin.last (k + 1)) c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hzero (j : Fin k) :
          T (Fin.last (k + 1)) j.castSucc.castSucc = 0 :=
        hT _ _ (Or.inl ⟨(Fin.last k).castSucc,
          Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last j),
          by simp [Fin.lt_def]⟩)
      simp [r, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hzero, hc, β]
    · have hs : (Pi.single (0 : Fin (k + 2)) γ : Fin (k + 2) → ℝ) j.castSucc =
          (Pi.single (0 : Fin (k + 1)) γ : Fin (k + 1) → ℝ) j := by
        by_cases hj : j = 0
        · subst j
          change (Pi.single 0 γ : Fin (k + 2) → ℝ) 0 = _
          simp
        · rw [Pi.single_eq_of_ne (by simpa using hj), Pi.single_eq_of_ne hj]
      have hsingle : (Pi.single (Fin.last (k + 1)) c : Fin (k + 2) → ℝ) j.castSucc = 0 := by
        rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
      have hrestrict : (T *ᵥ Fin.snoc (-x) 0) j.castSucc = -(A *ᵥ x) j := by
        change (∑ i, T j.castSucc i * (Fin.snoc (-x) 0 : Fin (k + 2) → ℝ) i) = -(A *ᵥ x) j
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero, Pi.neg_apply,
          mul_neg, Finset.sum_neg_distrib, Matrix.mulVec, dotProduct, A, Matrix.submatrix_apply]
      change (Pi.single (0 : Fin (k + 2)) γ : Fin (k + 2) → ℝ) j.castSucc +
        (T *ᵥ Fin.snoc (-x) 0) j.castSucc = _
      rw [hs, hrestrict, hsingle, congrFun hx j, add_neg_cancel]
  refine ⟨hr, ?_, ?_⟩
  · rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (r i) ^ 2) = _
    rw [hr, Fintype.sum_eq_single (Fin.last (k + 1))]
    · rw [Pi.single_eq_same]
      dsimp only [c]
      rw [div_pow, mul_pow, mul_pow, ← Finset.prod_pow]
      have hsign : (((-1 : ℝ) ^ (k + 1)) ^ 2) = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      rw [hsign, one_mul]
    · intro i hi
      rw [Pi.single_eq_of_ne hi, zero_pow (by decide)]
  · rw [hr]
    have hsingle : (Pi.single (Fin.last (k + 1)) c : Fin (k + 2) → ℝ) = 0 ↔ c = 0 := by
      constructor
      · intro h
        simpa using congrFun h (Fin.last (k + 1))
      · intro h
        simp [h]
    rw [hsingle]
    dsimp only [c]
    rw [hprod, div_eq_mul_inv]
    have hP : (∏ i : Fin k, A i.succ i.castSucc) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hprev i)
    have hA_det : A.det ≠ 0 := hdet
    simp [mul_eq_zero, hγ, hP, hA_det]

/-- A positive shift increases the determinant of a nonempty positive definite block. -/
theorem det_lt_det_add_smul_one_of_posDef {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.PosDef) {μ : ℝ} (hμ : 0 < μ) :
    A.det < (A + μ • 1).det := by
  have he := hA.isHermitian.det_sub_smul_one_eq_prod (-μ)
  rw [neg_smul, sub_neg_eq_add] at he
  rw [he, hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_lt_prod_of_nonempty₀
    (fun i _ => hA.eigenvalues_pos i) (fun i _ => by linarith) Finset.univ_nonempty

/-- The first two comparisons of Lemma 7.5.6 hold for any nonzero right-hand
side of the reduced system, including the one-dimensional first step. The
vectors here are the negatives of the trial steps. -/
theorem lemma_7_5_6_step {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {b x y : n → ℝ} (hb : b ≠ 0)
    {μ : ℝ} (hμ : 0 < μ) (hx : A *ᵥ x = b) (hy : (A + μ • 1) *ᵥ y = b) :
    b ⬝ᵥ y < b ⬝ᵥ x ∧
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ n)‖ <
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
  have hy₀ : y ≠ 0 := fun hz => hb (by simpa [hz] using hy.symm)
  let d := x - y
  have hy' : A *ᵥ y + μ • y = b := by
    simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hy
  have hd : A *ᵥ d = μ • y := by
    rw [show d = x - y from rfl, Matrix.mulVec_sub, hx, ← hy', add_sub_cancel_left]
  have hd₀ : d ≠ 0 := fun h =>
    hy₀ ((smul_eq_zero.mp (by simpa [h] using hd.symm)).resolve_left hμ.ne')
  have hpos : 0 < d ⬝ᵥ (A *ᵥ d) := by
    simpa using hA.dotProduct_mulVec_pos hd₀
  rw [hd, dotProduct_smul] at hpos
  have hcross : 0 < d ⬝ᵥ y := pos_of_mul_pos_right hpos hμ.le
  have hself (z : n → ℝ) : 0 ≤ z ⬝ᵥ z :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))
  have hypos : 0 < y ⬝ᵥ y :=
    (hself y).lt_of_ne (Ne.symm (mt dotProduct_self_eq_zero.mp hy₀))
  have hsym : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have hlinear := dotProduct_transpose_mulVec A x d
  rw [hsym, hx, hd, dotProduct_smul] at hlinear
  have hxpos : 0 < x ⬝ᵥ y := by
    change 0 < (x - y) ⬝ᵥ y at hcross
    rw [sub_dotProduct] at hcross
    linarith
  refine ⟨?_, ?_⟩
  · have hp : 0 < d ⬝ᵥ b := calc
      0 < μ • (x ⬝ᵥ y) := mul_pos hμ hxpos
      _ = _ := hlinear
    rw [dotProduct_comm d b, show d = x - y from rfl, dotProduct_sub] at hp
    linarith
  · apply (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    change y ⬝ᵥ y < x ⬝ᵥ x
    have he : x = y + d := by dsimp [d]; abel
    conv_rhs => rw [he]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y d]
    linarith [hself d]

private theorem submatrix_castSucc_add_smul_one {k : ℕ}
    (T : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) (μ : ℝ) :
    (T + μ • 1).submatrix Fin.castSucc Fin.castSucc =
      T.submatrix Fin.castSucc Fin.castSucc + μ • 1 := by
  ext i j
  simp [Matrix.one_apply, Fin.castSucc_inj]

/-- Lemma 7.5.6 at positive iterations. The current reduced matrix is `T`;
its leading block produces the preceding Galerkin step. The shifted
preceding residual is the gradient of the shifted model. The exact
determinant ratio also gives (7.5.26). -/
theorem lemma_7_5_6 {k : ℕ} {T : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ}
    (hT : T.IsTridiagonal) (hpos : T.PosDef) {γ μ : ℝ} (hγ : γ ≠ 0) (hμ : 0 < μ)
    (hprev : ∀ i : Fin k, T i.succ.castSucc i.castSucc.castSucc ≠ 0) :
    let Tμ := T + μ • 1
    let A := T.submatrix Fin.castSucc Fin.castSucc
    let Aμ := A + μ • 1
    let b : Fin (k + 2) → ℝ := Pi.single 0 γ
    let b' : Fin (k + 1) → ℝ := Pi.single 0 γ
    let x := T⁻¹ *ᵥ b
    let y := Tμ⁻¹ *ᵥ b
    let r := b + T *ᵥ Fin.snoc (-(A⁻¹ *ᵥ b')) 0
    let rμ := b + Tμ *ᵥ Fin.snoc (-(Aμ⁻¹ *ᵥ b')) 0
    rμ ≠ 0 →
      b ⬝ᵥ y < b ⬝ᵥ x ∧
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (k + 2)))‖ <
        ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (k + 2)))‖ ∧
      ‖(WithLp.toLp 2 rμ : EuclideanSpace ℝ (Fin (k + 2)))‖ =
        (A.det / Aμ.det) * ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin (k + 2)))‖ ∧
      ‖(WithLp.toLp 2 rμ : EuclideanSpace ℝ (Fin (k + 2)))‖ <
        ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin (k + 2)))‖ := by
  classical
  dsimp only
  let Tμ := T + μ • 1
  let A := T.submatrix Fin.castSucc Fin.castSucc
  let Aμ := A + μ • 1
  let b : Fin (k + 2) → ℝ := Pi.single 0 γ
  let b' : Fin (k + 1) → ℝ := Pi.single 0 γ
  let r := b + T *ᵥ Fin.snoc (-(A⁻¹ *ᵥ b')) 0
  let rμ := b + Tμ *ᵥ Fin.snoc (-(Aμ⁻¹ *ᵥ b')) 0
  let rn := ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin (k + 2)))‖
  let rμn := ‖(WithLp.toLp 2 rμ : EuclideanSpace ℝ (Fin (k + 2)))‖
  change rμ ≠ 0 → _ ∧ _ ∧ rμn = (A.det / Aμ.det) * rn ∧ rμn < rn
  intro hrμ
  have hA : A.PosDef := hpos.submatrix (Fin.castSucc_injective _)
  have hTμdet : 0 < Tμ.det := hpos.det_pos.trans (det_lt_det_add_smul_one_of_posDef hpos hμ)
  have hAdet : 0 < A.det := hA.det_pos
  have hdetlt : A.det < Aμ.det := det_lt_det_add_smul_one_of_posDef hA hμ
  have hAμdet : 0 < Aμ.det := hAdet.trans hdetlt
  have hsolve (M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ) (hd : M.det ≠ 0) :
      M *ᵥ (M⁻¹ *ᵥ b) = b := by
    let : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hb : b ≠ 0 := fun hz => hγ (by simpa [b] using congrFun hz (0 : Fin (k + 2)))
  obtain ⟨hlin, hstep⟩ :=
    lemma_7_5_6_step hpos hb hμ (hsolve T hpos.det_pos.ne') (hsolve Tμ hTμdet.ne')
  refine ⟨hlin, hstep, ?_⟩
  have hoff {i j : Fin (k + 2)} (hij : i ≠ j) : Tμ i j = T i j := by
    simp [Tμ, Matrix.one_apply_ne hij]
  have hTμ : Tμ.IsTridiagonal := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      rcases hij with ⟨z, hz, hz'⟩ | ⟨z, hz, hz'⟩ <;> exact (lt_asymm hz hz').elim
    rw [hoff hne, hT i j hij]
  have hsub (i : Fin (k + 1)) : Tμ i.succ i.castSucc = T i.succ i.castSucc :=
    hoff (Fin.ne_of_gt (by simp [Fin.lt_def]))
  have hprevμ (i : Fin k) : Tμ i.succ.castSucc i.castSucc.castSucc ≠ 0 := by
    rw [hoff (Fin.ne_of_gt (by simp [Fin.lt_def]))]
    exact hprev i
  have hprincipal : Tμ.submatrix Fin.castSucc Fin.castSucc = Aμ :=
    submatrix_castSucc_add_smul_one T μ
  obtain ⟨-, hsq, -⟩ := lemma_7_5_3 T hT γ hγ hprev hAdet.ne'
  obtain ⟨-, hsqμ, -⟩ :=
    lemma_7_5_3 Tμ hTμ γ hγ hprevμ (hprincipal.symm ▸ hAμdet.ne')
  rw [hprincipal] at hsqμ
  simp only [hsub] at hsqμ
  change rn ^ 2 = γ ^ 2 * (∏ i : Fin (k + 1), T i.succ i.castSucc ^ 2) / A.det ^ 2 at hsq
  have hratio : rμn = (A.det / Aμ.det) * rn := by
    apply (pow_left_inj₀ (norm_nonneg _)
      (mul_nonneg (div_nonneg hAdet.le hAμdet.le) (norm_nonneg _)) two_ne_zero).mp
    change rμn ^ 2 = _
    rw [mul_pow, div_pow]
    change rμn ^ 2 = A.det ^ 2 / Aμ.det ^ 2 * rn ^ 2
    rw [show rn ^ 2 = _ from hsq, show rμn ^ 2 = _ from hsqμ]
    field_simp
  refine ⟨hratio, ?_⟩
  have hrμpos : 0 < rμn := norm_pos_iff.mpr (fun h => hrμ (WithLp.toLp_eq_zero 2 |>.mp h))
  have hratpos := div_pos hAdet hAμdet
  have hrpos : 0 < rn := by
    rw [hratio] at hrμpos
    exact pos_of_mul_pos_right hrμpos hratpos.le
  rw [hratio]
  exact mul_lt_of_lt_one_left hrpos ((div_lt_one hAμdet).mpr hdetlt)

section TruncatedCG

open Krylov
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem 7.5.1. Starting at zero, PCG iterates grow strictly in the
preconditioner norm for as long as all preceding directional curvatures
are positive. The Hessian need only be symmetric. -/
theorem theorem_7_5_1 {H M Minv : E →ₗ[ℝ] E} (hM : IsPreconditioner M Minv)
    (hH : H.IsSymmetric) (g : E) (k : ℕ)
    (hpos : ∀ i ≤ k, 0 < ⟪(PCG.iterate H Minv (-g) 0 i).p,
      H (PCG.iterate H Minv (-g) 0 i).p⟫) :
    ∀ j < k, energyNorm M (PCG.iterate H Minv (-g) 0 j).x <
      energyNorm M (PCG.iterate H Minv (-g) 0 (j + 1)).x := by
  let A := hM.energyEnd (Minv ∘ₗ H)
  let b := hM.toEnergy (Minv (-g))
  have hA : A.IsSymmetric := by
    intro u v
    obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
    obtain ⟨y, rfl⟩ := hM.toEnergy.surjective v
    change ⟪hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy x), hM.toEnergy y⟫ =
      ⟪hM.toEnergy x, hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy y)⟫
    rw [hM.inner_energyEnd_left H, hM.inner_energyEnd_right H]
    exact hH x y
  have hx (j : ℕ) : hM.toEnergy (PCG.iterate H Minv (-g) 0 j).x =
      (CG.iterate A b 0 j).x := by
    simpa only [map_zero, A, b] using PCG.toEnergy_iterate_x H Minv (-g) 0 hM j
  have hp (j : ℕ) : hM.toEnergy (PCG.iterate H Minv (-g) 0 j).p =
      (CG.iterate A b 0 j).p := by
    simpa only [map_zero, A, b] using
      (PCG.iterate_eq_CG_iterate_withEnergy H Minv (-g) 0 hM j).2.2.1
  have hpos' (j : ℕ) (hj : j < k) :
      0 < RCLike.re (inner ℝ (A (CG.iterate A b 0 j).p) (CG.iterate A b 0 j).p) := by
    rw [← hp j]
    change 0 < ⟪hM.energyEnd (Minv ∘ₗ H) (hM.toEnergy (PCG.iterate H Minv (-g) 0 j).p),
      hM.toEnergy (PCG.iterate H Minv (-g) 0 j).p⟫
    rw [hM.inner_energyEnd_left H, real_inner_comm]
    exact hpos j hj.le
  intro j hj
  have h := CG.norm_iterate_lt_of_re_inner_apply_direction_pos b hA hpos' hj
  rw [← hx j, ← hx (j + 1)] at h
  exact h

private theorem cg_residual_ne_zero_prefix (H : E →ₗ[ℝ] E) (g : E) {k : ℕ}
    (hk : (CG.iterate H (-g) 0 k).r ≠ 0) {j : ℕ} (hj : j ≤ k) :
    (CG.iterate H (-g) 0 j).r ≠ 0 := by
  intro h
  apply hk
  rw [CG.iterate_eq_of_residual_eq_zero' H (-g) 0 h k hj, h]

private theorem cg_direction_eq_residual_sum (H : E →ₗ[ℝ] E) (g : E) (k : ℕ)
    (hk : (CG.iterate H (-g) 0 k).r ≠ 0) :
    (CG.iterate H (-g) 0 k).p = ‖(CG.iterate H (-g) 0 k).r‖ ^ 2 •
      ∑ i ∈ Finset.range (k + 1), (‖(CG.iterate H (-g) 0 i).r‖ ^ 2)⁻¹ •
        (CG.iterate H (-g) 0 i).r := by
  induction k with
  | zero =>
    have hne := pow_ne_zero 2 (norm_ne_zero_iff.mpr hk)
    rw [CG.direction_zero, Finset.sum_range_one, smul_smul, mul_inv_cancel₀ hne, one_smul]
  | succ j ih =>
    have hj := cg_residual_ne_zero_prefix H g hk (Nat.le_succ j)
    have hnj := pow_ne_zero 2 (norm_ne_zero_iff.mpr hj)
    have hnk := pow_ne_zero 2 (norm_ne_zero_iff.mpr hk)
    rw [CG.iterate_succ_p, CG.beta_iterate, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, ih hj, smul_smul, div_mul_cancel₀ _ hnj]
    conv_rhs => rw [Finset.sum_range_succ, smul_add, smul_smul, mul_inv_cancel₀ hnk, one_smul]
    exact add_comm _ _

private theorem cg_iterate_eq_direction_sum (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) :
    (CG.iterate H (-g) 0 k).x =
      ∑ j ∈ Finset.range k, CG.alpha H (CG.iterate H (-g) 0 j) • (CG.iterate H (-g) 0 j).p := by
  induction k with
  | zero => simp [CG.iterate, CG.init]
  | succ j ih => rw [CG.iterate_succ_x, ih, Finset.sum_range_succ]

private theorem smul_sum_triangle (a : ℕ → ℝ) (v : ℕ → E) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), a j • ∑ i ∈ Finset.range (j + 1), v i) =
      ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.Icc i k, a j) • v i := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
        if i ≤ j then a j • v i else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.smul_sum, ← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
      omega
    _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if i ≤ j then a j • v i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter, Finset.sum_smul]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega

/-- Lemma 7.5.2. The untruncated CG trial direction and next step expanded in
the preceding residuals. Lean stores residuals with the opposite sign from the
book's gradients, so both expansions have positive overall signs. -/
theorem lemma_7_5_2 (H : E →ₗ[ℝ] E) (g : E) (k : ℕ)
    (hk : (CG.iterate H (-g) 0 k).r ≠ 0) :
    let r := fun i => (CG.iterate H (-g) 0 i).r
    let α := fun i => CG.alpha H (CG.iterate H (-g) 0 i)
    (CG.iterate H (-g) 0 k).p = ‖r k‖ ^ 2 •
      (∑ i ∈ Finset.range (k + 1), (‖r i‖ ^ 2)⁻¹ • r i) ∧
    (CG.iterate H (-g) 0 (k + 1)).x =
      ∑ i ∈ Finset.range (k + 1), (∑ j ∈ Finset.Icc i k, α j * ‖r j‖ ^ 2) •
        ((‖r i‖ ^ 2)⁻¹ • r i) := by
  refine ⟨cg_direction_eq_residual_sum H g k hk, ?_⟩
  dsimp only
  rw [cg_iterate_eq_direction_sum]
  calc
    _ = ∑ j ∈ Finset.range (k + 1), (CG.alpha H (CG.iterate H (-g) 0 j) *
          ‖(CG.iterate H (-g) 0 j).r‖ ^ 2) •
        ∑ i ∈ Finset.range (j + 1), (‖(CG.iterate H (-g) 0 i).r‖ ^ 2)⁻¹ •
          (CG.iterate H (-g) 0 i).r := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [cg_direction_eq_residual_sum H g j
        (cg_residual_ne_zero_prefix H g hk (Nat.le_of_lt_succ (Finset.mem_range.mp hj))), smul_smul]
    _ = _ := smul_sum_triangle _ _ k

private noncomputable def cgPathWeight (j : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 (t - j))

/-- The linear interpolation of the untruncated CG trial steps through step `k + 1`.
Each path segment uses the full step length before its left endpoint, a fractional
length inside the segment, and zero length for future steps. -/
noncomputable def cgPath (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) (t : ℝ) : E :=
  ∑ j ∈ Finset.range (k + 1), (cgPathWeight j t * CG.alpha H (CG.iterate H (-g) 0 j)) •
    (CG.iterate H (-g) 0 j).p

/-- The residual-direction coefficient (7.5.17) along the interpolated CG path.
The clipped weights express the floor and fractional-part formula without a
separate endpoint convention. -/
noncomputable def cgPathCoefficient (H : E →ₗ[ℝ] E) (g : E) (k i : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc i k, (cgPathWeight j t * CG.alpha H (CG.iterate H (-g) 0 j)) *
    ‖(CG.iterate H (-g) 0 j).r‖ ^ 2) / ‖(CG.iterate H (-g) 0 i).r‖

/-- The interpolated path is the straight segment between the corresponding
consecutive CG iterates. -/
theorem cgPath_eq_segment (H : E →ₗ[ℝ] E) (g : E) {k j : ℕ} (hj : j ≤ k)
    {t : ℝ} (ht : t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1)) :
    cgPath H g k t = (CG.iterate H (-g) 0 j).x +
      (t - j) • ((CG.iterate H (-g) 0 (j + 1)).x - (CG.iterate H (-g) 0 j).x) := by
  have hz (i : ℕ) (hi : j < i) : cgPathWeight i t = 0 := by
    have hji : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hi)
    simp [cgPathWeight, max_eq_left (sub_nonpos.mpr (ht.2.trans hji))]
  have hone (i : ℕ) (hi : i < j) : cgPathWeight i t = 1 := by
    have hij : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hi)
    have hp : 1 ≤ t - i := by linarith [ht.1]
    exact min_eq_left (hp.trans (le_max_right _ _))
  have hfrac : cgPathWeight j t = t - j := by
    rw [cgPathWeight, max_eq_right (sub_nonneg.mpr ht.1), min_eq_right (by linarith [ht.2])]
  unfold cgPath
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj))
    (fun i _ hi => by
      have hij : j < i := by
        simp only [Finset.mem_range, not_lt] at hi
        omega
      simp [hz i hij])]
  rw [Finset.sum_range_succ, hfrac, CG.iterate_succ_x, add_sub_cancel_left, smul_smul]
  congr 1
  rw [cg_iterate_eq_direction_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hone i (Finset.mem_range.mp hi), one_mul]

/-- Lemma 7.5.4. The trial path expands in the normalized residual vectors with
coefficients (7.5.17). These vectors are the negatives of the normalized book
gradients, absorbing the minus sign in (7.5.16). -/
theorem lemma_7_5_4 (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) (t : ℝ)
    (hk : (CG.iterate H (-g) 0 k).r ≠ 0) :
    cgPath H g k t =
      ∑ i ∈ Finset.range (k + 1), cgPathCoefficient H g k i t •
        (‖(CG.iterate H (-g) 0 i).r‖⁻¹ • (CG.iterate H (-g) 0 i).r) := by
  unfold cgPath
  calc
    _ = ∑ j ∈ Finset.range (k + 1), ((cgPathWeight j t * CG.alpha H (CG.iterate H (-g) 0 j)) *
          ‖(CG.iterate H (-g) 0 j).r‖ ^ 2) •
        ∑ i ∈ Finset.range (j + 1), (‖(CG.iterate H (-g) 0 i).r‖ ^ 2)⁻¹ •
          (CG.iterate H (-g) 0 i).r := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [cg_direction_eq_residual_sum H g j
        (cg_residual_ne_zero_prefix H g hk (Nat.le_of_lt_succ (Finset.mem_range.mp hj))), smul_smul]
    _ = _ := by
      rw [smul_sum_triangle]
      apply Finset.sum_congr rfl
      intro i _
      unfold cgPathCoefficient
      rw [smul_smul, smul_smul, div_eq_mul_inv, mul_assoc, ← pow_two, inv_pow]

private theorem cgPathWeight_mono (j : ℕ) : Monotone (cgPathWeight j) :=
  fun _ _ h => min_le_min_left 1 (max_le_max_left 0 (sub_le_sub_right h _))

private theorem cgPathWeight_pos_diff {j : ℕ} {s t : ℝ}
    (hjs : (j : ℝ) ≤ s) (hs : s < (j : ℝ) + 1) (hst : s < t) :
    cgPathWeight j s < cgPathWeight j t := by
  unfold cgPathWeight
  rw [max_eq_right (sub_nonneg.mpr hjs), min_eq_right (by linarith : s - j ≤ 1)]
  exact lt_min (by linarith) ((sub_lt_sub_right hst _).trans_le (le_max_right _ _))

/-- Lemma 7.5.5. Before a nonpositive curvature or zero-residual stop, the path
coefficients grow strictly after their respective start times. The squared norm
is their sum of squares, and the negative linear term is the first coefficient
scaled by the initial gradient norm. Both quantities grow strictly along the path. -/
theorem lemma_7_5_5 (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E) (k : ℕ)
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫) :
    (∀ i ≤ k, StrictMonoOn (cgPathCoefficient H g k i) (Set.Icc (i : ℝ) ((k : ℝ) + 1))) ∧
      (∀ t : ℝ, -⟪g, cgPath H g k t⟫ = ‖g‖ * cgPathCoefficient H g k 0 t ∧
        ‖cgPath H g k t‖ ^ 2 = ∑ i ∈ Finset.range (k + 1), (cgPathCoefficient H g k i t) ^ 2) ∧
      StrictMonoOn (fun t => -⟪g, cgPath H g k t⟫) (Set.Icc 0 ((k : ℝ) + 1)) ∧
      StrictMonoOn (fun t => ‖cgPath H g k t‖) (Set.Icc 0 ((k : ℝ) + 1)) := by
  let r := fun i => (CG.iterate H (-g) 0 i).r
  let ρ := fun i => cgPathCoefficient H g k i
  have hk : r k ≠ 0 := by
    intro hz
    have hp := CG.direction_eq_zero_of_residual_eq_zero H (-g) 0 hz
    simpa only [hp, map_zero, inner_zero_left, lt_self_iff_false] using hpos k le_rfl
  have hn (i : ℕ) (hi : i ≤ k) : 0 < ‖r i‖ :=
    norm_pos_iff.mpr (cg_residual_ne_zero_prefix H g hk hi)
  have hα (i : ℕ) (hi : i ≤ k) : 0 < CG.alpha H (CG.iterate H (-g) 0 i) := by
    rw [CG.alpha, real_inner_self_eq_norm_sq]
    exact div_pos (pow_pos (hn i hi) 2) (hpos i hi)
  have hmono (i : ℕ) : Monotone (ρ i) := by
    intro s t hst
    unfold ρ cgPathCoefficient
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (cgPathWeight_mono j hst)
        (hα j (Finset.mem_Icc.mp hj).2).le) (sq_nonneg _)
  have hρ0 (i : ℕ) (t : ℝ) : 0 ≤ ρ i t := by
    unfold ρ cgPathCoefficient
    apply div_nonneg _ (norm_nonneg _)
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (le_min zero_le_one (le_max_left _ _))
      (hα j (Finset.mem_Icc.mp hj).2).le) (sq_nonneg _)
  have hstrict (i : ℕ) (hi : i ≤ k) :
      StrictMonoOn (ρ i) (Set.Icc (i : ℝ) ((k : ℝ) + 1)) := by
    intro s hs t ht hst
    have hs0 : 0 ≤ s := (Nat.cast_nonneg i).trans hs.1
    let j := ⌊s⌋₊
    have hij : i ≤ j := (Nat.le_floor_iff hs0).mpr hs.1
    have hjk : j ≤ k := Nat.lt_succ_iff.mp ((Nat.floor_lt hs0).mpr (by
      push_cast
      exact hst.trans_le ht.2))
    have hst' := cgPathWeight_pos_diff (j := j) (Nat.floor_le hs0) (Nat.lt_floor_add_one s) hst
    unfold ρ cgPathCoefficient
    apply div_lt_div_of_pos_right _ (hn i hi)
    refine Finset.sum_lt_sum (fun l hl => ?_) ⟨j, Finset.mem_Icc.mpr ⟨hij, hjk⟩, ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (cgPathWeight_mono l hst.le)
          (hα l (Finset.mem_Icc.mp hl).2).le) (sq_nonneg _)
    · exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hst' (hα j hjk))
        (pow_pos (hn j hjk) 2)
  let e : Fin (k + 1) → E := fun i => ‖r i‖⁻¹ • r i
  have he : Orthonormal ℝ e := by
    constructor
    · intro i
      dsimp [e]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hn i (Nat.le_of_lt_succ i.isLt)).ne']
    · intro i j hij
      have hcurv (l : ℕ) (hl : l < k + 1) :
          0 < RCLike.re (inner ℝ (H (CG.iterate H (-g) 0 l).p) (CG.iterate H (-g) 0 l).p) :=
        hpos l (Nat.le_of_lt_succ hl)
      have hord := CG.inner_residual_eq_zero_of_pos_prefix (-g) 0 hH hcurv i.isLt.le j.isLt.le
        (fun he => hij (Fin.ext he))
      dsimp [e, r]
      rw [real_inner_smul_left, real_inner_smul_right, hord, mul_zero, mul_zero]
  have hp (t : ℝ) : cgPath H g k t = ∑ i : Fin (k + 1), ρ i t • e i := by
    rw [lemma_7_5_4 H g k t hk]
    exact (Fin.sum_univ_eq_sum_range (fun i => ρ i t • (‖r i‖⁻¹ • r i)) (k + 1)).symm
  have hr₀ : r 0 = -g := by simp [r, CG.iterate, CG.init]
  have hgpos : 0 < ‖g‖ := by simpa only [hr₀, norm_neg] using hn 0 (Nat.zero_le k)
  have hg : -g = ‖g‖ • e 0 := by
    change -g = ‖g‖ • (‖r 0‖⁻¹ • r 0)
    rw [hr₀, norm_neg, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  have hlin (t : ℝ) : -⟪g, cgPath H g k t⟫ = ‖g‖ * ρ 0 t := by
    rw [← inner_neg_left, hp, hg, real_inner_smul_left, he.inner_right_fintype]
    rfl
  have hnorm (t : ℝ) : ‖cgPath H g k t‖ ^ 2 =
      ∑ i ∈ Finset.range (k + 1), (ρ i t) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hp]
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (ρ i t) ^ 2) (k + 1)]
    simpa only [conj_trivial, ← sq] using
      he.inner_sum (fun i => ρ i t) (fun i => ρ i t) Finset.univ
  refine ⟨hstrict, fun t => ⟨hlin t, hnorm t⟩, ?_, ?_⟩
  · intro s hs t ht hst
    change -⟪g, cgPath H g k s⟫ < -⟪g, cgPath H g k t⟫
    rw [hlin, hlin]
    exact mul_lt_mul_of_pos_left
      (hstrict 0 (Nat.zero_le k) (by simpa only [Nat.cast_zero] using hs)
        (by simpa only [Nat.cast_zero] using ht) hst) hgpos
  · intro s hs t ht hst
    change ‖cgPath H g k s‖ < ‖cgPath H g k t‖
    apply (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [hnorm, hnorm]
    refine Finset.sum_lt_sum (fun i _ => pow_le_pow_left₀ (hρ0 i s) (hmono i hst.le) 2)
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), ?_⟩
    exact (pow_lt_pow_iff_left₀ (hρ0 0 s) (hρ0 0 t) two_ne_zero).mpr
      (hstrict 0 (Nat.zero_le k) (by simpa only [Nat.cast_zero] using hs)
        (by simpa only [Nat.cast_zero] using ht) hst)


private theorem continuous_cgPath (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) :
    Continuous (cgPath H g k) := by
  unfold cgPath
  refine continuous_finsetSum _ fun j _ => ?_
  apply Continuous.smul _ continuous_const
  unfold cgPathWeight
  exact (continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))).mul
    continuous_const

private theorem cgPath_eq_zero (H : E →ₗ[ℝ] E) (g : E) (k : ℕ) :
    cgPath H g k 0 = 0 := by
  have hw (j : ℕ) : cgPathWeight j 0 = 0 := by
    simp [cgPathWeight]
  simp [cgPath, hw]

private theorem cgPath_eq_iterate (H : E →ₗ[ℝ] E) (g : E) {k i : ℕ} (hi : i ≤ k + 1) :
    cgPath H g k (i : ℝ) = (CG.iterate H (-g) 0 i).x := by
  by_cases hik : i ≤ k
  · rw [cgPath_eq_segment H g hik (t := (i : ℝ)) (by simp), sub_self, zero_smul, add_zero]
  · have h : i = k + 1 := by omega
    subst i
    push_cast
    rw [cgPath_eq_segment H g le_rfl (by simp), add_sub_cancel_left, one_smul, add_sub_cancel]

private theorem cgPrefixCurvature (H : E →ₗ[ℝ] E) (g : E) {k : ℕ}
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫) :
    ∀ i ≤ k, 0 < ‖(CG.iterate H (-g) 0 i).r‖ ∧ 0 < CG.alpha H (CG.iterate H (-g) 0 i) := by
  intro i hi
  have hr : (CG.iterate H (-g) 0 i).r ≠ 0 := by
    intro hz
    have hp := CG.direction_eq_zero_of_residual_eq_zero H (-g) 0 hz
    simpa [hp] using hpos i hi
  have hn := norm_pos_iff.mpr hr
  refine ⟨hn, ?_⟩
  rw [CG.alpha, real_inner_self_eq_norm_sq]
  exact div_pos (sq_pos_of_pos hn) (hpos i hi)

private theorem cgPathCoefficient_nonneg (H : E →ₗ[ℝ] E) (g : E) {k : ℕ}
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    (i : ℕ) (t : ℝ) : 0 ≤ cgPathCoefficient H g k i t := by
  unfold cgPathCoefficient
  apply div_nonneg _ (norm_nonneg _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (le_min zero_le_one (le_max_left _ _))
    (cgPrefixCurvature H g hpos j (Finset.mem_Icc.mp hj).2).2.le) (sq_nonneg _)

private theorem cgPathCoefficient_eq_positivePart (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (g : E) {k : ℕ}
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    {i : ℕ} (hi : i ≤ k) (t : ℝ) :
    cgPathCoefficient H g k i t =
      max 0 (-⟪g, cgPath H g k t⟫ - -⟪g, cgPath H g k (i : ℝ)⟫) /
        ‖(CG.iterate H (-g) 0 i).r‖ := by
  let a (j : ℕ) (u : ℝ) := (cgPathWeight j u * CG.alpha H (CG.iterate H (-g) 0 j)) *
    ‖(CG.iterate H (-g) 0 j).r‖ ^ 2
  let F (u : ℝ) := ∑ j ∈ Finset.range (k + 1), a j u
  have hg : 0 < ‖g‖ := by
    simpa [CG.iterate, CG.init] using (cgPrefixCurvature H g hpos 0 (Nat.zero_le _)).1
  have hF (u : ℝ) : -⟪g, cgPath H g k u⟫ = F u := by
    rw [((lemma_7_5_5 H hH g k hpos).2.1 u).1, cgPathCoefficient]
    simp only [← Finset.Ico_add_one_right_eq_Icc, Nat.Ico_zero_eq_range]
    change ‖g‖ * (F u / ‖(CG.iterate H (-g) 0 0).r‖) = F u
    have hr : ‖(CG.iterate H (-g) 0 0).r‖ = ‖g‖ := by simp [CG.iterate, CG.init]
    rw [hr, ← mul_div_assoc, mul_comm ‖g‖, mul_div_cancel_right₀ _ hg.ne']
  have hz (j : ℕ) {u : ℝ} (h : u ≤ j) : a j u = 0 := by
    simp [a, cgPathWeight, max_eq_left (sub_nonpos.mpr h)]
  by_cases ht : t ≤ i
  · rw [cgPathCoefficient, hF, hF]
    have hmono : F t ≤ F i := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (cgPathWeight_mono j ht)
          (cgPrefixCurvature H g hpos j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).2.le)
        (sq_nonneg _)
    rw [max_eq_left (sub_nonpos.mpr hmono)]
    have hs : (∑ j ∈ Finset.Icc i k, a j t) = 0 :=
      Finset.sum_eq_zero fun j hj => hz j (ht.trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hj).1))
    change (∑ j ∈ Finset.Icc i k, a j t) / _ = 0 / _
    rw [hs]
  · have hti : (i : ℝ) ≤ t := le_of_not_ge ht
    have hfull (j : ℕ) (hj : j < i) : a j t = a j i := by
      have hji : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hj
      have hw {u : ℝ} (hu : (j : ℝ) + 1 ≤ u) : cgPathWeight j u = 1 :=
        min_eq_left ((by linarith : 1 ≤ u - j).trans (le_max_right _ _))
      unfold a
      rw [hw (hji.trans hti), hw hji]
    have hFi : F i = ∑ j ∈ Finset.range i, a j i := by
      symm
      exact Finset.sum_subset (Finset.range_mono (Nat.le_succ_of_le hi)) fun j _ hj =>
        hz j (Nat.cast_le.mpr (Nat.le_of_not_lt (fun h => hj (Finset.mem_range.mpr h))))
    have hsplit : (∑ j ∈ Finset.Icc i k, a j t) = F t - F i := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      change (∑ j ∈ Finset.Ico i k.succ, a j t) = F t - F i
      rw [Finset.sum_Ico_eq_sub (fun j => a j t) (Nat.le_succ_of_le hi), hFi]
      congr 1
      exact Finset.sum_congr rfl fun j hj => hfull j (Finset.mem_range.mp hj)
    rw [hF, hF, cgPathCoefficient]
    change (∑ j ∈ Finset.Icc i k, a j t) / _ = max 0 (F t - F i) / _
    have hnn : 0 ≤ ∑ j ∈ Finset.Icc i k, a j t := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (mul_nonneg (le_min zero_le_one (le_max_left _ _))
        (cgPrefixCurvature H g hpos j (Finset.mem_Icc.mp hj).2).2.le) (sq_nonneg _)
    rw [← hsplit, max_eq_right hnn]

/-- Lemma 7.5.7 on the two CG prefixes. The linear and residual comparisons
are the shifted-system estimates (7.5.23) and (7.5.26) at the earlier iterates.
The proof compares cumulative linear terms at each integer breakpoint. -/
theorem lemma_7_5_7 (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E) (k : ℕ) (μ : ℝ)
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    (hshiftPos : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i ≤ k, 0 < ⟪A (CG.iterate A (-g) 0 i).p, (CG.iterate A (-g) 0 i).p⟫)
    (hlinear : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k + 1 →
        -⟪g, (CG.iterate A (-g) 0 i).x⟫ < -⟪g, (CG.iterate H (-g) 0 i).x⟫)
    (hresidual : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k → ‖(CG.iterate A (-g) 0 i).r‖ < ‖(CG.iterate H (-g) 0 i).r‖) :
    let A := H + μ • (1 : E →ₗ[ℝ] E)
    ∃ t ∈ Set.Ico 0 ((k : ℝ) + 1), -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ =
      -⟪g, cgPath H g k t⟫ ∧
      ∀ i ≤ k, cgPathCoefficient H g k i t ≤ cgPathCoefficient A g k i ((k : ℝ) + 1) ∧
        (0 < i → cgPathCoefficient H g k i t < cgPathCoefficient A g k i ((k : ℝ) + 1)) := by
  let A := H + μ • (1 : E →ₗ[ℝ] E)
  have hA : A.IsSymmetric := hH.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one)
  let F (t : ℝ) := -⟪g, cgPath H g k t⟫
  let G (t : ℝ) := -⟪g, cgPath A g k t⟫
  let K : ℝ := (k : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hf0 : F 0 = 0 := by simp [F, cgPath_eq_zero]
  have hg0 : G 0 = 0 := by simp [G, cgPath_eq_zero]
  have hfmono : StrictMonoOn F (Set.Icc 0 K) := (lemma_7_5_5 H hH g k hpos).2.2.1
  have hgmono : StrictMonoOn G (Set.Icc 0 K) := (lemma_7_5_5 A hA g k hshiftPos).2.2.1
  have hgpos : G 0 < G K := hgmono ⟨le_rfl, hK.le⟩ ⟨hK.le, le_rfl⟩ hK
  have hcast (B : E →ₗ[ℝ] E) : cgPath B g k K = (CG.iterate B (-g) 0 (k + 1)).x := by
    simpa [K] using cgPath_eq_iterate B g (k := k) (i := k + 1) le_rfl
  have htop : G K < F K := by
    dsimp only [G, F]
    rw [hcast A, hcast H]
    exact hlinear (k + 1) (Nat.succ_pos _) le_rfl
  have hc : Continuous F := (continuous_const.inner (continuous_cgPath H g k)).neg
  obtain ⟨t, ht, hmatch⟩ := intermediate_value_Icc hK.le hc.continuousOn
    (show G K ∈ Set.Icc (F 0) (F K) from ⟨by linarith, htop.le⟩)
  have htK : t < K := lt_of_le_of_ne ht.2 fun he => htop.ne (by rw [he] at hmatch; exact hmatch.symm)
  refine ⟨t, ⟨ht.1, htK⟩, ?_, ?_⟩
  · change -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ = F t
    rw [hmatch]
    exact congrArg (fun z : E => -⟪g, z⟫) (hcast A).symm
  intro i hi
  rw [cgPathCoefficient_eq_positivePart H hH g hpos hi,
    cgPathCoefficient_eq_positivePart A hA g hshiftPos hi]
  change max 0 (F t - F i) / ‖(CG.iterate H (-g) 0 i).r‖ ≤
    max 0 (G K - G i) / ‖(CG.iterate A (-g) 0 i).r‖ ∧
    (0 < i → max 0 (F t - F i) / ‖(CG.iterate H (-g) 0 i).r‖ <
      max 0 (G K - G i) / ‖(CG.iterate A (-g) 0 i).r‖)
  rw [hmatch]
  by_cases hi0 : i = 0
  · subst i
    simp [hf0, hg0, CG.iterate, CG.init]
  have hip := Nat.pos_of_ne_zero hi0
  have hFi : G i < F i := by
    dsimp only [G, F]
    rw [cgPath_eq_iterate A g (Nat.le_succ_of_le hi),
      cgPath_eq_iterate H g (Nat.le_succ_of_le hi)]
    exact hlinear i hip (Nat.le_succ_of_le hi)
  have hiK : (i : ℝ) < K := by dsimp [K]; exact_mod_cast Nat.lt_succ_of_le hi
  have hGi : G i < G K := hgmono ⟨Nat.cast_nonneg _, hiK.le⟩ ⟨hK.le, le_rfl⟩ hiK
  have hn : 0 < ‖(CG.iterate H (-g) 0 i).r‖ := (cgPrefixCurvature H g hpos i hi).1
  have ha : 0 < ‖(CG.iterate A (-g) 0 i).r‖ := (cgPrefixCurvature A g hshiftPos i hi).1
  have hnum : max 0 (G K - F i) < max 0 (G K - G i) := by
    rw [max_eq_right (sub_nonneg.mpr hGi.le)]
    exact max_lt (sub_pos.mpr hGi) (sub_lt_sub_left hFi _)
  have hd := (div_lt_div_of_pos_right hnum hn).trans_le
    (div_le_div_of_nonneg_left (le_max_left _ _) ha (hresidual i hip hi).le)
  exact ⟨hd.le, fun _ => hd⟩


/-- Lemma 7.5.8 on the two CG prefixes. The endpoint norm comparison is
(7.5.24). Equal step norm identifies a unique unshifted trial, whose linear
decrease is at least as large as the shifted iterate's. -/
theorem lemma_7_5_8 (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E) (k : ℕ) (μ : ℝ)
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    (hshiftPos : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i ≤ k, 0 < ⟪A (CG.iterate A (-g) 0 i).p, (CG.iterate A (-g) 0 i).p⟫)
    (hlinear : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k + 1 →
        -⟪g, (CG.iterate A (-g) 0 i).x⟫ < -⟪g, (CG.iterate H (-g) 0 i).x⟫)
    (hresidual : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k → ‖(CG.iterate A (-g) 0 i).r‖ < ‖(CG.iterate H (-g) 0 i).r‖)
    (hnorm : let A := H + μ • (1 : E →ₗ[ℝ] E)
      ‖(CG.iterate A (-g) 0 (k + 1)).x‖ < ‖(CG.iterate H (-g) 0 (k + 1)).x‖) :
    let A := H + μ • (1 : E →ₗ[ℝ] E)
    ∃! t, t ∈ Set.Ico 0 ((k : ℝ) + 1) ∧
      ‖cgPath H g k t‖ = ‖(CG.iterate A (-g) 0 (k + 1)).x‖ ∧
      -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ ≤ -⟪g, cgPath H g k t⟫ ∧
      (0 < k → -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ < -⟪g, cgPath H g k t⟫) := by
  let A := H + μ • (1 : E →ₗ[ℝ] E)
  let K : ℝ := (k : ℝ) + 1
  have hA : A.IsSymmetric :=
    hH.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one)
  obtain ⟨t, ht, hlin, hcoef⟩ := lemma_7_5_7 H hH g k μ hpos hshiftPos hlinear hresidual
  let F (t : ℝ) := ‖cgPath H g k t‖
  let N := ‖(CG.iterate A (-g) 0 (k + 1)).x‖
  have hcast (B : E →ₗ[ℝ] E) : cgPath B g k K = (CG.iterate B (-g) 0 (k + 1)).x := by
    simpa [K] using cgPath_eq_iterate B g (k := k) (i := k + 1) le_rfl
  have htop : N < F K := by simpa only [F, N, hcast H] using hnorm
  have hF := lemma_7_5_5 H hH g k hpos
  have hG := lemma_7_5_5 A hA g k hshiftPos
  have hsq (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      cgPathCoefficient H g k i t ^ 2 ≤ cgPathCoefficient A g k i K ^ 2 :=
    pow_le_pow_left₀ (cgPathCoefficient_nonneg H g hpos i t)
      (hcoef i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).1 2
  have hsum : F t ^ 2 ≤ N ^ 2 := by
    change ‖cgPath H g k t‖ ^ 2 ≤ ‖(CG.iterate A (-g) 0 (k + 1)).x‖ ^ 2
    rw [← hcast A, (hF.2.1 t).2, (hG.2.1 K).2]
    exact Finset.sum_le_sum hsq
  have hlt (hk : 0 < k) : F t < N := by
    apply (pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    change ‖cgPath H g k t‖ ^ 2 < ‖(CG.iterate A (-g) 0 (k + 1)).x‖ ^ 2
    rw [← hcast A, (hF.2.1 t).2, (hG.2.1 K).2]
    refine Finset.sum_lt_sum hsq ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    exact (pow_lt_pow_iff_left₀ (cgPathCoefficient_nonneg H g hpos 1 t)
      (cgPathCoefficient_nonneg A g hshiftPos 1 K) two_ne_zero).mpr
      ((hcoef 1 hk).2 (by decide))
  have hle : F t ≤ N :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsum
  obtain ⟨u, hu, huN⟩ := intermediate_value_Icc ht.2.le
    (continuous_cgPath H g k).norm.continuousOn
    (show N ∈ Set.Icc (F t) (F K) from ⟨hle, htop.le⟩)
  have huK : u < K := lt_of_le_of_ne hu.2 fun he => htop.ne (by rw [he] at huN; exact huN.symm)
  have htI : t ∈ Set.Icc 0 K := ⟨ht.1, ht.2.le⟩
  have huI : u ∈ Set.Icc 0 K := ⟨ht.1.trans hu.1, hu.2⟩
  have htu (hk : 0 < k) : t < u := lt_of_le_of_ne hu.1 fun he => (hlt hk).ne (he ▸ huN)
  refine ⟨u, ⟨⟨huI.1, huK⟩, huN, ?_, ?_⟩, ?_⟩
  · rw [hlin]
    exact hF.2.2.1.monotoneOn htI huI hu.1
  · intro hk
    rw [hlin]
    exact hF.2.2.1 htI huI (htu hk)
  · intro v hv
    exact hF.2.2.2.injOn ⟨hv.1.1, hv.1.2.le⟩ huI (hv.2.1.trans huN.symm)


private theorem cgInnerResidualIterate (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E)
    {k : ℕ} (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    {i j : ℕ} (hij : j ≤ i) (hi : i ≤ k + 1) :
    ⟪(CG.iterate H (-g) 0 i).r, (CG.iterate H (-g) 0 j).x⟫ = 0 := by
  rw [cg_iterate_eq_direction_sum]
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have hmj := Finset.mem_range.mp hm
  have hmk : m ≤ k := by omega
  have hcurv (l : ℕ) (hl : l < k + 1) :
      0 < RCLike.re (inner ℝ (H (CG.iterate H (-g) 0 l).p) (CG.iterate H (-g) 0 l).p) :=
    hpos l (Nat.le_of_lt_succ hl)
  rw [cg_direction_eq_residual_sum H g m
    (norm_pos_iff.mp (cgPrefixCurvature H g hpos m hmk).1)]
  simp only [real_inner_smul_right, inner_sum]
  have hsum : (∑ l ∈ Finset.range (m + 1), (‖(CG.iterate H (-g) 0 l).r‖ ^ 2)⁻¹ *
      ⟪(CG.iterate H (-g) 0 i).r, (CG.iterate H (-g) 0 l).r⟫) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hlm := Finset.mem_range.mp hl
    rw [CG.inner_residual_eq_zero_of_pos_prefix (-g) 0 hH hcurv hi (by omega) (by omega),
      mul_zero]
  rw [hsum, mul_zero, mul_zero]

private theorem cgInnerResidualDirectionSelf (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E)
    {k : ℕ} (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    {i : ℕ} (hi : i ≤ k) :
    ⟪(CG.iterate H (-g) 0 i).r, (CG.iterate H (-g) 0 i).p⟫ =
      ‖(CG.iterate H (-g) 0 i).r‖ ^ 2 := by
  have hn := (cgPrefixCurvature H g hpos i hi).1
  have hcurv (l : ℕ) (hl : l < k + 1) :
      0 < RCLike.re (inner ℝ (H (CG.iterate H (-g) 0 l).p) (CG.iterate H (-g) 0 l).p) :=
    hpos l (Nat.le_of_lt_succ hl)
  rw [cg_direction_eq_residual_sum H g i (norm_pos_iff.mp hn),
    real_inner_smul_right, inner_sum, Finset.sum_range_succ]
  simp only [real_inner_smul_right]
  have hsum : (∑ l ∈ Finset.range i, (‖(CG.iterate H (-g) 0 l).r‖ ^ 2)⁻¹ *
      ⟪(CG.iterate H (-g) 0 i).r, (CG.iterate H (-g) 0 l).r⟫) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hli := Finset.mem_range.mp hl
    rw [CG.inner_residual_eq_zero_of_pos_prefix (-g) 0 hH hcurv (by omega) (by omega) (by omega),
      mul_zero]
  rw [hsum, zero_add, real_inner_self_eq_norm_sq, inv_mul_cancel₀ (sq_pos_of_pos hn).ne', mul_one]

/-- The radial derivative of the quadratic is nonpositive along the positive
curvature CG prefix, as used in the proof of (7.5.47). -/
theorem cgPath_inner_gradient_nonpos (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (g : E)
    {k : ℕ} (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫)
    {t : ℝ} (ht : t ∈ Set.Ico 0 ((k : ℝ) + 1)) :
    ⟪g + H (cgPath H g k t), cgPath H g k t⟫ ≤ 0 := by
  let j := ⌊t⌋₊
  let u := t - (j : ℝ)
  let x := (CG.iterate H (-g) 0 j).x
  let y := (CG.iterate H (-g) 0 (j + 1)).x
  let r := (CG.iterate H (-g) 0 j).r
  let z := (CG.iterate H (-g) 0 (j + 1)).r
  have hj : j ≤ k := Nat.lt_succ_iff.mp ((Nat.floor_lt ht.1).mpr (by push_cast; exact ht.2))
  have htj : t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) :=
    ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
  have hu : 0 ≤ u := sub_nonneg.mpr htj.1
  have hu₁ : 0 ≤ 1 - u := by dsimp [u]; linarith [htj.2]
  have hx : cgPath H g k t = (1 - u) • x + u • y := by
    rw [cgPath_eq_segment H g hj htj]
    change x + u • (y - x) = (1 - u) • x + u • y
    rw [smul_sub]
    have he : (1 - u) • x = x - u • x := by
      calc
        (1 - u) • x = (1 : ℝ) • x - u • x := sub_smul _ _ _
        _ = _ := by rw [one_smul]
    rw [he]
    abel
  have hr : r = -g - H x := CG.residual_eq H (-g) 0 j
  have hz : z = -g - H y := CG.residual_eq H (-g) 0 (j + 1)
  have hres : -g - H (cgPath H g k t) = (1 - u) • r + u • z := by
    rw [hx, map_add, map_smul, map_smul, hr, hz, smul_sub, smul_sub]
    have hsum : (1 - u) • (-g) + u • (-g) = -g := by rw [← add_smul, sub_add_cancel, one_smul]
    calc
      _ = (1 - u) • (-g) + u • (-g) - ((1 - u) • H x + u • H y) := by rw [hsum]
      _ = _ := by abel
  have hrx : ⟪r, x⟫ = 0 := cgInnerResidualIterate H hH g hpos le_rfl (by omega)
  have hzx : ⟪z, x⟫ = 0 := cgInnerResidualIterate H hH g hpos (by omega) (by omega)
  have hzy : ⟪z, y⟫ = 0 := cgInnerResidualIterate H hH g hpos le_rfl (by omega)
  have hry : 0 ≤ ⟪r, y⟫ := by
    change 0 ≤ ⟪r, (CG.iterate H (-g) 0 (j + 1)).x⟫
    rw [CG.iterate_succ_x, inner_add_right, real_inner_smul_right]
    change 0 ≤ ⟪r, x⟫ + CG.alpha H (CG.iterate H (-g) 0 j) *
      ⟪r, (CG.iterate H (-g) 0 j).p⟫
    rw [hrx, zero_add, cgInnerResidualDirectionSelf H hH g hpos hj]
    exact mul_nonneg (cgPrefixCurvature H g hpos j hj).2.le (sq_nonneg _)
  have hinner : 0 ≤ ⟪-g - H (cgPath H g k t), cgPath H g k t⟫ := by
    calc
      _ ≤ ((1 - u) * u) * ⟪r, y⟫ := mul_nonneg (mul_nonneg hu₁ hu) hry
      _ = _ := by
        nth_rw 1 [hres]
        rw [hx]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hrx, hzx, hzy]
        ring
  rw [inner_sub_left, inner_neg_left] at hinner
  rw [inner_add_left]
  linarith

/-- The boundary case of Theorem 7.5.9 once the positive-curvature prefixes
supply the comparisons from Lemma 7.5.6. The algorithm returns the unique
point on that prefix with the exact minimizer's norm. -/
theorem theorem_7_5_9_boundary (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsPositive) (g : E) (k : ℕ) (μ : ℝ)
    (hpos : ∀ i ≤ k, 0 < ⟪H (CG.iterate H.toLinearMap (-g) 0 i).p,
      (CG.iterate H.toLinearMap (-g) 0 i).p⟫)
    (hshiftPos : let A := H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)
      ∀ i ≤ k, 0 < ⟪A (CG.iterate A (-g) 0 i).p, (CG.iterate A (-g) 0 i).p⟫)
    (hlinear : let A := H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k + 1 →
        -⟪g, (CG.iterate A (-g) 0 i).x⟫ < -⟪g, (CG.iterate H.toLinearMap (-g) 0 i).x⟫)
    (hresidual : let A := H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)
      ∀ i, 0 < i → i ≤ k →
        ‖(CG.iterate A (-g) 0 i).r‖ < ‖(CG.iterate H.toLinearMap (-g) 0 i).r‖)
    (hnorm : let A := H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)
      ‖(CG.iterate A (-g) 0 (k + 1)).x‖ < ‖(CG.iterate H.toLinearMap (-g) 0 (k + 1)).x‖)
    {t : ℝ} (ht : t ∈ Set.Ico 0 ((k : ℝ) + 1))
    (htnorm : ‖cgPath H.toLinearMap g k t‖ =
      ‖(CG.iterate (H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)) (-g) 0 (k + 1)).x‖) :
    Subproblem.quadModel g H (cgPath H.toLinearMap g k t) ≤ (1 / 2) *
      Subproblem.quadModel g H
        (CG.iterate (H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)) (-g) 0 (k + 1)).x := by
  obtain ⟨u, hu, _⟩ := lemma_7_5_8 H.toLinearMap hH.isSymmetric g k μ hpos hshiftPos
    hlinear hresidual hnorm
  have hm := (lemma_7_5_5 H.toLinearMap hH.isSymmetric g k hpos).2.2.2
  have htu := hm.injOn ⟨ht.1, ht.2.le⟩ ⟨hu.1.1, hu.1.2.le⟩ (htnorm.trans hu.2.1.symm)
  let x := cgPath H.toLinearMap g k t
  let y := (CG.iterate (H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)) (-g) 0 (k + 1)).x
  have hlin : ⟪g, x⟫ ≤ ⟪g, y⟫ := by
    apply neg_le_neg_iff.mp
    change -⟪g, y⟫ ≤ -⟪g, cgPath H.toLinearMap g k t⟫
    rw [htu]
    exact hu.2.2.1
  have hrad := cgPath_inner_gradient_nonpos H.toLinearMap hH.isSymmetric g hpos ht
  change ⟪g + H x, x⟫ ≤ 0 at hrad
  rw [inner_add_left, real_inner_comm x (H x)] at hrad
  have hy := hH.inner_nonneg_left y
  change 0 ≤ ⟪H y, y⟫ at hy
  rw [real_inner_comm y (H y)] at hy
  change Subproblem.quadModel g H x ≤ (1 / 2) * Subproblem.quadModel g H y
  unfold Subproblem.quadModel
  linarith

/-- The stationary stop in Theorem 7.5.9. Convexity makes the returned
stationary iterate globally optimal, so its decrease is at least one half
of the decrease at any trust-region minimizer. -/
theorem theorem_7_5_9_stationary (H : E →L[ℝ] E)
    (hH : (H : E →ₗ[ℝ] E).IsPositive) (g x y : E) (hx : H x = -g) :
    Subproblem.quadModel g H x ≤ (1 / 2) * Subproblem.quadModel g H y := by
  have hopt (v : E) : Subproblem.quadModel g H x ≤ Subproblem.quadModel g H v := by
    have h := hH.inner_nonneg_left (v - x)
    change 0 ≤ ⟪H (v - x), v - x⟫ at h
    have hsym : ⟪x, H v⟫ = -⟪g, v⟫ := by
      calc
        _ = ⟪H x, v⟫ := (hH.isSymmetric x v).symm
        _ = _ := by rw [hx, inner_neg_left]
    rw [real_inner_comm (v - x) (H (v - x)), map_sub, inner_sub_left, inner_sub_right,
      inner_sub_right, hsym] at h
    rw [hx, inner_neg_right, inner_neg_right, real_inner_comm g v, real_inner_comm g x] at h
    unfold Subproblem.quadModel
    rw [hx, inner_neg_right, real_inner_comm g x]
    linarith
  have hzero := hopt 0
  rw [Subproblem.quadModel_zero] at hzero
  linarith [hopt y]


private theorem cgShiftSubspace (H : E →ₗ[ℝ] E) (b : E) (μ : ℝ) (m : ℕ) :
    Krylov.subspace (H + μ • (1 : E →ₗ[ℝ] E)) b m = Krylov.subspace H b m := by
  have he : H + μ • (1 : E →ₗ[ℝ] E) = H + algebraMap ℝ (Module.End ℝ E) μ := by
    ext x
    simp [Module.algebraMap_end_apply]
  rw [he, Krylov.subspace_add_algebraMap]

private theorem cgShiftGrade [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (b : E) (μ : ℝ) :
    Krylov.grade (H + μ • (1 : E →ₗ[ℝ] E)) b = Krylov.grade H b := by
  have he : H + μ • (1 : E →ₗ[ℝ] E) = H + algebraMap ℝ (Module.End ℝ E) μ := by
    ext x
    simp [Module.algebraMap_end_apply]
  rw [he, Krylov.grade_add_algebraMap]

private theorem cgShiftArnoldiVec (H : E →ₗ[ℝ] E) (b : E) (μ : ℝ) (j : ℕ) :
    Arnoldi.vec (H + μ • (1 : E →ₗ[ℝ] E)) b j = Arnoldi.vec H b j := by
  induction j with
  | zero =>
    by_cases hb : b = 0
    · have hz (A : E →ₗ[ℝ] E) : Arnoldi.vec A b 0 = 0 := by
        rw [Arnoldi.vec_eq_zero_iff_pow_apply_mem, hb]
        simp
      rw [hz, hz]
    · rw [Arnoldi.vec_zero _ _ hb, Arnoldi.vec_zero _ _ hb]
  | succ j ih =>
    have hp (y : E) :
        ((Krylov.subspace (H + μ • (1 : E →ₗ[ℝ] E)) b (j + 1)).starProjection y : E) =
          (Krylov.subspace H b (j + 1)).starProjection y := by
      let z : E := (Krylov.subspace H b (j + 1)).starProjection y
      have he := cgShiftSubspace H b μ (j + 1)
      apply Submodule.eq_starProjection_of_mem_orthogonal
      · exact Eq.mpr (congrArg (fun K : Submodule ℝ E => z ∈ K) he)
          (Submodule.starProjection_apply_mem _ _)
      · exact Eq.mpr (congrArg (fun K : Submodule ℝ E => y - z ∈ Kᗮ) he)
          (Submodule.sub_starProjection_mem_orthogonal (K := Krylov.subspace H b (j + 1)) y)
    have hv : ((Krylov.subspace H b (j + 1)).starProjection (Arnoldi.vec H b j) : E) =
        Arnoldi.vec H b j :=
      Submodule.starProjection_mem_subspace_eq_self
        ⟨_, Arnoldi.vec_mem_subspace H b j⟩
    have hw : Arnoldi.w (H + μ • (1 : E →ₗ[ℝ] E)) b j = Arnoldi.w H b j := by
      rw [Arnoldi.w_eq_sub_starProjection, Arnoldi.w_eq_sub_starProjection, hp, ih,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_add, map_smul, hv]
      abel
    rw [Arnoldi.vec_succ_eq, Arnoldi.vec_succ_eq, hw]

private theorem cgShiftCoercive (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive)
    (μ : ℝ) (hμ : 0 < μ) : (H + μ • (1 : E →ₗ[ℝ] E)).IsSymmetricCoercive := by
  refine ⟨hH.isSymmetric.add (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.one), ?_⟩
  obtain ⟨C, hC, hbound⟩ := hH.isCoercive
  refine ⟨C, hC, fun x => ?_⟩
  have hx := hbound x
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, inner_add_left,
    real_inner_smul_left, RCLike.re_to_real, real_inner_self_eq_norm_sq] at hx ⊢
  exact hx.trans (le_add_of_nonneg_right (mul_nonneg hμ.le (sq_nonneg _)))

private theorem cgShiftHessenbergSq [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (b : E) (μ : ℝ) {m : ℕ} (hm : m ≤ grade H b) :
    Arnoldi.hessenbergSq (H + μ • (1 : E →ₗ[ℝ] E)) b m =
      Arnoldi.hessenbergSq H b m + μ • 1 := by
  ext i j
  change Arnoldi.coeff (H + μ • (1 : E →ₗ[ℝ] E)) b i j =
    Arnoldi.coeff H b i j + μ * (1 : Matrix (Fin m) (Fin m) ℝ) i j
  unfold Arnoldi.coeff
  rw [cgShiftArnoldiVec, cgShiftArnoldiVec, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, inner_add_right, real_inner_smul_right]
  have he (l : Fin m) : (l : ℕ) < grade H b := l.isLt.trans_le hm
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade H b (he i)]
    simp
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
    rw [Arnoldi.inner_vec_eq_zero H b hne]
    simp [hij]

private theorem cgShiftSubdiag (H : E →ₗ[ℝ] E) (b : E) (μ : ℝ) (j : ℕ) :
    Arnoldi.coeff (H + μ • (1 : E →ₗ[ℝ] E)) b (j + 1) j =
      Arnoldi.coeff H b (j + 1) j := by
  unfold Arnoldi.coeff
  rw [cgShiftArnoldiVec, cgShiftArnoldiVec, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, inner_add_right, real_inner_smul_right,
    Arnoldi.inner_vec_eq_zero H b (Nat.succ_ne_self j), mul_zero, add_zero]

private theorem cgHessenbergPosDef [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetricCoercive) (b : E) {m : ℕ} (hm : m ≤ grade H b) :
    (Arnoldi.hessenbergSq H b m).PosDef := by
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin m),
      ⟪Matrix.toEuclideanLin (Arnoldi.hessenbergSq H b m) x, y⟫ =
        ⟪H (∑ i : Fin m, x i • Arnoldi.vec H b i), ∑ i : Fin m, y i • Arnoldi.vec H b i⟫ := by
    intro x y
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct]
    rw [Matrix.toEuclideanLin]
    change (∑ i : Fin m, y i * ((Arnoldi.hessenbergSq H b m).mulVec x) i) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change y i * (Arnoldi.coeff H b i j * x j) =
      y i * (x j * ⟪H (Arnoldi.vec H b j), Arnoldi.vec H b i⟫)
    rw [Arnoldi.coeff, real_inner_comm (H (Arnoldi.vec H b j)) (Arnoldi.vec H b i)]
    ring
  rw [Matrix.posDef_iff_isSymmetricCoercive]
  refine ⟨fun x y => ?_, ?_⟩
  · calc
      _ = ⟪H (∑ i : Fin m, x i • Arnoldi.vec H b i), ∑ i : Fin m, y i • Arnoldi.vec H b i⟫ :=
        hinner x y
      _ = ⟪H (∑ i : Fin m, y i • Arnoldi.vec H b i), ∑ i : Fin m, x i • Arnoldi.vec H b i⟫ := by
        rw [hH.isSymmetric, real_inner_comm]
      _ = _ := (hinner y x).symm.trans (real_inner_comm _ _)

  rw [LinearMap.isCoercive_iff_forall_pos]
  intro x hx
  rw [RCLike.re_to_real, hinner]
  apply (LinearMap.isCoercive_iff_forall_pos H).mp hH.isCoercive
  intro hz
  apply hx
  ext i
  change x i = 0
  have horth : Orthonormal ℝ (fun i : Fin m => Arnoldi.vec H b i) :=
    ⟨fun i => Arnoldi.norm_vec_eq_one_of_lt_grade H b (i.isLt.trans_le hm),
      fun i j hij => Arnoldi.inner_vec_eq_zero H b (fun he => hij (Fin.ext he))⟩
  have hi := horth.inner_right_fintype (fun j => x j) i
  rw [hz, inner_zero_right] at hi
  exact hi.symm


private theorem cgArnoldiCoordinates [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    (hH : H.IsSymmetricCoercive) (b : E) {m : ℕ} (hm : m ≤ grade H b) :
    ∃ y : Fin m → ℝ, (Arnoldi.hessenbergSq H b m).mulVec y = firstVec ‖b‖ m ∧
      (CG.iterate H b 0 m).x = ∑ j : Fin m, y j • Arnoldi.vec H b j := by
  have hgrade : m ≤ grade H (b - H 0) := by simpa using hm
  obtain ⟨y, hy, hx⟩ := (isGalerkinIterate_iff_exists_mulVec_eq hgrade _).mp
    (CG.isGalerkinIterate b 0 hH m)
  refine ⟨y, ?_, ?_⟩
  · simpa only [map_zero, sub_zero, RCLike.ofReal_real_eq_id, id_eq] using hy
  · simpa only [map_zero, sub_zero, zero_add] using hx

private theorem cgArnoldiCoordinates_dot_norm [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
    {b : E} {m : ℕ} (y : Fin (m + 1) → ℝ)
    (hm' : m + 1 ≤ grade H b) :
    ⟪b, ∑ j : Fin (m + 1), y j • Arnoldi.vec H b j⟫ =
      firstVec ‖b‖ (m + 1) ⬝ᵥ y ∧
    ‖∑ j : Fin (m + 1), y j • Arnoldi.vec H b j‖ =
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  let e (i : Fin (m + 1)) := Arnoldi.vec H b i
  have he : Orthonormal ℝ e :=
    ⟨fun i => Arnoldi.norm_vec_eq_one_of_lt_grade H b (i.isLt.trans_le hm'),
      fun i j hij => Arnoldi.inner_vec_eq_zero H b (fun h => hij (Fin.ext h))⟩
  have hb' : b = ‖b‖ • e 0 := (Arnoldi.smul_vec_zero H b).symm
  have hdot : firstVec ‖b‖ (m + 1) ⬝ᵥ y = ‖b‖ * y 0 := by
    unfold dotProduct
    rw [Finset.sum_eq_single 0]
    · rfl
    · intro i _ hi
      have hne : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [firstVec, hne]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  constructor
  · rw [hdot]
    nth_rw 1 [hb']
    rw [real_inner_smul_left]
    congr 1
    exact he.inner_right_fintype y 0
  · apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    simpa only [conj_trivial, ← sq] using he.inner_sum y y Finset.univ

/-- The shifted CG comparisons on a positive-definite system. This joins
the matrix estimates in Lemma 7.5.6 to CG via the common Arnoldi basis. -/
theorem cg_shift_comparisons_of_coercive [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive) (g : E) (m : ℕ)
    {μ : ℝ} (hμ : 0 < μ) (hm : m + 1 ≤ grade H (-g)) :
    let A := H + μ • (1 : E →ₗ[ℝ] E);
    -⟪g, (CG.iterate A (-g) 0 (m + 1)).x⟫ < -⟪g, (CG.iterate H (-g) 0 (m + 1)).x⟫ ∧
      ‖(CG.iterate A (-g) 0 (m + 1)).x‖ < ‖(CG.iterate H (-g) 0 (m + 1)).x‖ ∧
      (m + 1 < grade H (-g) →
        ‖(CG.iterate A (-g) 0 (m + 1)).r‖ < ‖(CG.iterate H (-g) 0 (m + 1)).r‖) := by
  let A := H + μ • (1 : E →ₗ[ℝ] E)
  let b := -g
  have hb : b ≠ 0 := by
    intro hz
    rw [show -g = b from rfl, hz, grade_zero] at hm
    omega
  have hAm : m + 1 ≤ grade A b := by simpa [A, b, cgShiftGrade] using hm
  obtain ⟨x, hx, hxx⟩ := cgArnoldiCoordinates H hH b hm
  obtain ⟨y, hy, hyy⟩ := cgArnoldiCoordinates A (cgShiftCoercive H hH μ hμ) b hAm
  let T := Arnoldi.hessenbergSq H b (m + 1)
  have hT : T.PosDef := cgHessenbergPosDef H hH b hm
  have hshift : Arnoldi.hessenbergSq A b (m + 1) = T + μ • 1 :=
    cgShiftHessenbergSq H b μ hm
  rw [hshift] at hy
  have hf : firstVec ‖b‖ (m + 1) = Pi.single 0 ‖b‖ := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [firstVec]
    · have hni : (i : ℕ) ≠ 0 := fun e => hi (Fin.ext e)
      simp [firstVec, hni, Pi.single_eq_of_ne hi]
  have hfne : firstVec ‖b‖ (m + 1) ≠ 0 := fun hz =>
    (norm_ne_zero_iff.mpr hb) (by simpa [firstVec] using congrFun hz 0)
  obtain ⟨hl, hn⟩ := lemma_7_5_6_step hT hfne hμ hx hy
  have hxb := cgArnoldiCoordinates_dot_norm H x hm
  have hyb := cgArnoldiCoordinates_dot_norm H y hm
  have hyy' : (CG.iterate A b 0 (m + 1)).x = ∑ j : Fin (m + 1), y j • Arnoldi.vec H b j := by
    simpa only [A, cgShiftArnoldiVec] using hyy
  change -⟪g, (CG.iterate A b 0 (m + 1)).x⟫ < -⟪g, (CG.iterate H b 0 (m + 1)).x⟫ ∧
    ‖(CG.iterate A b 0 (m + 1)).x‖ < ‖(CG.iterate H b 0 (m + 1)).x‖ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← inner_neg_left, ← inner_neg_left, hyy', hxx]
    change ⟪b, _⟫ < ⟪b, _⟫
    rw [hyb.1, hxb.1]
    exact hl
  · rw [hyy', hxx, hyb.2, hxb.2]
    exact hn
  intro hlt
  have hltA : m + 1 < grade A b := by simpa [A, b, cgShiftGrade] using hlt
  have hres (B : E →ₗ[ℝ] E) (hB : m + 1 < grade B b) (z : Fin (m + 1) → ℝ)
      (hz : (Arnoldi.hessenbergSq B b (m + 1)).mulVec z = firstVec ‖b‖ (m + 1))
      (hcoord : (CG.iterate B b 0 (m + 1)).x = ∑ j : Fin (m + 1), z j • Arnoldi.vec B b j) :
      ‖(CG.iterate B b 0 (m + 1)).r‖ =
        |Arnoldi.coeff B b (m + 1) m| * |z (Fin.last m)| := by
    have hr : b - B (0 + ∑ j : Fin (m + 1), z j • Arnoldi.vec B b j) =
        -(Arnoldi.coeff B b (m + 1) m * z (Fin.last m)) • Arnoldi.vec B b (m + 1) := by
      simpa only [map_zero, sub_zero, Nat.succ_sub_one, Fin.last] using
        (residual_galerkin_eq (b := b) (x₀ := 0) (Nat.succ_pos m) z
          (by simpa only [map_zero, sub_zero, RCLike.ofReal_real_eq_id, id_eq] using hz))
    rw [CG.residual_eq, hcoord, ← zero_add (∑ j : Fin (m + 1), z j • Arnoldi.vec B b j), hr,
      norm_smul, Arnoldi.norm_vec_eq_one_of_lt_grade B b hB, mul_one, Real.norm_eq_abs,
      abs_neg, abs_mul]
  have hxres := hres H hlt x hx hxx
  have hyres := hres A hltA y (hshift.symm ▸ hy) hyy
  rw [show Arnoldi.coeff A b (m + 1) m = Arnoldi.coeff H b (m + 1) m from
    cgShiftSubdiag H b μ m] at hyres
  have hdet : T.det ≠ 0 := hT.det_pos.ne'
  have hshiftT : (T + μ • 1).PosDef :=
    (cgHessenbergPosDef A (cgShiftCoercive H hH μ hμ) b hAm) |> (hshift ▸ ·)
  have hdetS : (T + μ • 1).det ≠ 0 := hshiftT.det_pos.ne'
  have hcoord (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hM : M.IsUpperHessenberg)
      (hd : M.det ≠ 0) (z : Fin (m + 1) → ℝ) (hz : M.mulVec z = firstVec ‖b‖ (m + 1)) :
      z (Fin.last m) = ((-1 : ℝ) ^ m * ∏ i : Fin m, M i.succ i.castSucc) * ‖b‖ / M.det := by
    let : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hd)
    have hz' : z = M⁻¹ *ᵥ Pi.single 0 ‖b‖ := by
      rw [← hf, ← hz, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
    rw [hz', Matrix.mulVec_single]
    change (M⁻¹) (Fin.last m) 0 * ‖b‖ = _
    rw [inv_apply_last_zero_of_isUpperHessenberg M hM]
    ring
  have hhu : T.IsUpperHessenberg := Arnoldi.hessenbergSq_isUpperHessenberg H b _
  have hhs : (T + μ • 1).IsUpperHessenberg :=
    hshift ▸ Arnoldi.hessenbergSq_isUpperHessenberg A b _
  have hxlast := hcoord T hhu hdet x hx
  have hylast := hcoord (T + μ • 1) hhs hdetS y hy
  have hprod : (∏ i : Fin m, (T + μ • 1) i.succ i.castSucc) =
      ∏ i : Fin m, T i.succ i.castSucc := by
    apply Finset.prod_congr rfl
    intro i _
    have hi : i.succ ≠ i.castSucc := by
      intro h
      have he := congrArg Fin.val h
      simp at he
    simp [hi]
  have hrpos : 0 < ‖(CG.iterate H b 0 (m + 1)).r‖ := by
    apply norm_pos_iff.mpr
    apply CG.residual_ne_zero_of_lt_grade b 0
    simpa only [map_zero, sub_zero] using hlt
  let c := |Arnoldi.coeff H b (m + 1) m| * |((-1 : ℝ) ^ m * ∏ i : Fin m, T i.succ i.castSucc) * ‖b‖|
  have hx' : ‖(CG.iterate H b 0 (m + 1)).r‖ = c / T.det := by
    rw [hxres, hxlast, abs_div, abs_of_pos hT.det_pos, mul_div_assoc]
  have hy' : ‖(CG.iterate A b 0 (m + 1)).r‖ = c / (T + μ • 1).det := by
    rw [hyres, hylast, hprod, abs_div, abs_of_pos hshiftT.det_pos, mul_div_assoc]
  have hc : 0 < c := by
    rw [hx'] at hrpos
    simpa only [zero_mul] using (lt_div_iff₀ hT.det_pos).mp hrpos
  change ‖(CG.iterate A b 0 (m + 1)).r‖ < ‖(CG.iterate H b 0 (m + 1)).r‖
  rw [hx', hy']
  exact div_lt_div_of_pos_left hc hT.det_pos (det_lt_det_add_smul_one_of_posDef hT hμ)


private theorem cg_positive_prefix_of_coercive [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive) (g : E) {k : ℕ}
    (hk : k < grade H (-g)) :
    ∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫ := by
  intro i hi
  apply CG.re_inner_apply_direction_pos (-g) 0 hH
  apply CG.residual_ne_zero_of_lt_grade (-g) 0
  simpa only [map_zero, sub_zero] using hi.trans_lt hk

private theorem cg_prefix_comparisons_of_coercive [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive) (g : E) {k : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hk : k < grade H (-g)) :
    let A := H + μ • (1 : E →ₗ[ℝ] E)
    (∀ i ≤ k, 0 < ⟪H (CG.iterate H (-g) 0 i).p, (CG.iterate H (-g) 0 i).p⟫) ∧
    (∀ i ≤ k, 0 < ⟪A (CG.iterate A (-g) 0 i).p, (CG.iterate A (-g) 0 i).p⟫) ∧
    (∀ i, 0 < i → i ≤ k + 1 →
      -⟪g, (CG.iterate A (-g) 0 i).x⟫ < -⟪g, (CG.iterate H (-g) 0 i).x⟫) ∧
    (∀ i, 0 < i → i ≤ k → ‖(CG.iterate A (-g) 0 i).r‖ < ‖(CG.iterate H (-g) 0 i).r‖) ∧
    ‖(CG.iterate A (-g) 0 (k + 1)).x‖ < ‖(CG.iterate H (-g) 0 (k + 1)).x‖ := by
  let A := H + μ • (1 : E →ₗ[ℝ] E)
  have hkA : k < grade A (-g) := by simpa only [A, cgShiftGrade] using hk
  refine ⟨cg_positive_prefix_of_coercive H hH g hk,
    cg_positive_prefix_of_coercive A (cgShiftCoercive H hH μ hμ) g hkA, ?_, ?_, ?_⟩
  · intro i hi hik
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact (cg_shift_comparisons_of_coercive H hH g m hμ (by omega)).1
  · intro i hi hik
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact (cg_shift_comparisons_of_coercive H hH g m hμ (by omega)).2.2 (by omega)
  · exact (cg_shift_comparisons_of_coercive H hH g k hμ (by omega)).2.1

/-- Lemma 7.5.7 for a positive-definite Hessian. The nonzero shifted residual
is equivalent to the current index being below the common Krylov grade. -/
theorem lemma_7_5_7_of_coercive [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive) (g : E) (k : ℕ) {μ : ℝ}
    (hμ : 0 < μ) (hk : k < grade H (-g)) :
    let A := H + μ • (1 : E →ₗ[ℝ] E)
    ∃ t ∈ Set.Ico 0 ((k : ℝ) + 1), -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ =
      -⟪g, cgPath H g k t⟫ ∧
      ∀ i ≤ k, cgPathCoefficient H g k i t ≤ cgPathCoefficient A g k i ((k : ℝ) + 1) ∧
        (0 < i → cgPathCoefficient H g k i t < cgPathCoefficient A g k i ((k : ℝ) + 1)) := by
  obtain ⟨hp, hsp, hl, hr, _⟩ := cg_prefix_comparisons_of_coercive H hH g hμ hk
  exact lemma_7_5_7 H hH.isSymmetric g k μ hp hsp hl hr

/-- Lemma 7.5.8 for a positive-definite Hessian. The printed g ≥ 0 is
the condition on the iteration index k. -/
theorem lemma_7_5_8_of_coercive [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetricCoercive) (g : E) (k : ℕ) {μ : ℝ}
    (hμ : 0 < μ) (hk : k < grade H (-g)) :
    let A := H + μ • (1 : E →ₗ[ℝ] E)
    ∃! t, t ∈ Set.Ico 0 ((k : ℝ) + 1) ∧
      ‖cgPath H g k t‖ = ‖(CG.iterate A (-g) 0 (k + 1)).x‖ ∧
      -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ ≤ -⟪g, cgPath H g k t⟫ ∧
      (0 < k → -⟪g, (CG.iterate A (-g) 0 (k + 1)).x⟫ < -⟪g, cgPath H g k t⟫) := by
  obtain ⟨hp, hsp, hl, hr, hn⟩ := cg_prefix_comparisons_of_coercive H hH g hμ hk
  exact lemma_7_5_8 H hH.isSymmetric g k μ hp hsp hl hr hn


/-- Theorem 7.5.9 for a positive-definite Hessian. The truncated output is either
stationary or a boundary point on the interpolated CG path. A zero multiplier
can put the minimizer exactly at the last CG iterate. -/
theorem theorem_7_5_9_of_coercive [FiniteDimensional ℝ E] (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetricCoercive) (g : E) {Δ : ℝ} (hΔ : 0 < Δ)
    {x y : E} (hy : ‖y‖ ≤ Δ)
    (hmin : IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) y)
    (hx : H x = -g ∨ ∃ k : ℕ, k + 1 = grade H.toLinearMap (-g) ∧
      ∃ t ∈ Set.Icc 0 ((k : ℝ) + 1), x = cgPath H.toLinearMap g k t ∧ ‖x‖ = Δ) :
    Subproblem.quadModel g H x ≤ (1 / 2) * Subproblem.quadModel g H y := by
  have hHpos : H.toLinearMap.IsPositive := by
    refine ⟨hH.isSymmetric, ?_⟩
    intro z
    obtain ⟨c, hc, hbound⟩ := hH.isCoercive
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hbound z)
  rcases hx with hs | ⟨k, hk, t, ht, rfl, hn⟩
  · exact theorem_7_5_9_stationary H hHpos g x y hs
  obtain ⟨μ, hμ⟩ := (Subproblem.isMinOn_closedBall_iff hH.isSymmetric hΔ hy).mp hmin
  have hklt : k < grade H.toLinearMap (-g) := by omega
  let A := H.toLinearMap + μ • (1 : E →ₗ[ℝ] E)
  have hEqShift : A y = -g := hμ.shifted
  have hend : cgPath H.toLinearMap g k ((k : ℝ) + 1) =
      (CG.iterate H.toLinearMap (-g) 0 (k + 1)).x := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (cgPath_eq_iterate H.toLinearMap g (k := k) (i := k + 1) le_rfl)
  by_cases hμ₀ : μ = 0
  · have hstat : H y = -g := by simpa [A, hμ₀] using hEqShift
    have hterm : (CG.iterate H.toLinearMap (-g) 0 (k + 1)).r = 0 := by
      apply CG.residual_eq_zero_of_grade_le (-g) 0 hH
      simpa only [map_zero, sub_zero] using hk.ge
    rw [CG.residual_eq, sub_eq_zero] at hterm
    have hy_eq : (CG.iterate H.toLinearMap (-g) 0 (k + 1)).x = y :=
      hH.isCoercive.injective (hterm.symm.trans hstat.symm)
    have hpos := cg_positive_prefix_of_coercive H.toLinearMap hH g hklt
    have hmono := (lemma_7_5_5 H.toLinearMap hH.isSymmetric g k hpos).2.2.2
    have hK : 0 ≤ (k : ℝ) + 1 := by positivity
    have ht_eq : t = (k : ℝ) + 1 := by
      by_contra hne
      have hlt := hmono ht ⟨hK, le_rfl⟩ (lt_of_le_of_ne ht.2 hne)
      change ‖cgPath H.toLinearMap g k t‖ <
        ‖cgPath H.toLinearMap g k ((k : ℝ) + 1)‖ at hlt
      rw [hend, hy_eq, hn] at hlt
      exact hlt.not_ge hy
    rw [ht_eq, hend, hy_eq]
    exact theorem_7_5_9_stationary H hHpos g y y hstat
  · have hμ' : 0 < μ := lt_of_le_of_ne hμ.nonneg (Ne.symm hμ₀)
    have hA := cgShiftCoercive H.toLinearMap hH μ hμ'
    have hterm : (CG.iterate A (-g) 0 (k + 1)).r = 0 := by
      apply CG.residual_eq_zero_of_grade_le (-g) 0 hA
      simpa only [map_zero, sub_zero, A, cgShiftGrade] using hk.ge
    rw [CG.residual_eq, sub_eq_zero] at hterm
    have hy_eq : (CG.iterate A (-g) 0 (k + 1)).x = y :=
      hA.isCoercive.injective (hterm.symm.trans hEqShift.symm)
    obtain ⟨hp, hsp, hl, hr, hn'⟩ :=
      cg_prefix_comparisons_of_coercive H.toLinearMap hH g hμ' hklt
    have htnorm : ‖cgPath H.toLinearMap g k t‖ = ‖(CG.iterate A (-g) 0 (k + 1)).x‖ := by
      rw [hy_eq, hn, hμ.norm_eq_of_pos hμ']
    have ht' : t ∈ Set.Ico 0 ((k : ℝ) + 1) := by
      refine ⟨ht.1, lt_of_le_of_ne ht.2 fun he => ?_⟩
      rw [he, hend] at htnorm
      exact hn'.ne htnorm.symm
    rw [← hy_eq]
    exact theorem_7_5_9_boundary H hHpos g k μ hp hsp hl hr hn' ht' htnorm

end TruncatedCG

/-- Theorem 7.5.10. The preconditioned Lanczos relation and the shifted reduced
system give the full residual and its inverse-preconditioner energy norm. The next
dual Lanczos vector has unit energy norm whenever its coefficient is nonzero. -/
theorem theorem_7_5_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (H M Minv : E →ₗ[ℝ] E) (hMinv : Minv.IsSymmetricCoercive)
    (Q : (Fin (n + 1) → ℝ) →ₗ[ℝ] E) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (g w : E) (γ β μ : ℝ) (hβ : 0 ≤ β)
    (hw : β ≠ 0 → energyNorm Minv w = 1)
    (hgrad : M (Q (Pi.single 0 γ)) = g)
    (hrel : ∀ y : Fin (n + 1) → ℝ,
      H (Q y) = M (Q (T *ᵥ y)) + (β * y (Fin.last n)) • w)
    (y : Fin (n + 1) → ℝ)
    (hsolve : (T + μ • 1) *ᵥ y = -(Pi.single 0 γ : Fin (n + 1) → ℝ)) :
    H (Q y) + μ • M (Q y) + g = (β * y (Fin.last n)) • w ∧
      energyNorm Minv (H (Q y) + μ • M (Q y) + g) = β * |y (Fin.last n)| := by
  have hsys : T *ᵥ y + μ • y = -(Pi.single 0 γ : Fin (n + 1) → ℝ) := by
    simpa only [add_mulVec, smul_mulVec, one_mulVec] using hsolve
  have hres : H (Q y) + μ • M (Q y) + g = (β * y (Fin.last n)) • w := calc
    _ = M (Q (T *ᵥ y + μ • y)) + g + (β * y (Fin.last n)) • w := by
      rw [hrel, map_add, map_smul, map_add, map_smul]
      abel
    _ = _ := by rw [hsys, map_neg, map_neg, hgrad]; abel
  refine ⟨hres, ?_⟩
  rw [hres]
  by_cases hb : β = 0
  · simp [hb, energyNorm]
  · rw [← WithEnergy.norm_equiv Minv hMinv, map_smul, norm_smul,
      WithEnergy.norm_equiv, hw hb, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hβ]

/-- Lemma 7.5.11. An eigenvector of an irreducible tridiagonal matrix has nonzero first
component. Only the nonvanishing of the superdiagonal is needed. -/
theorem lemma_7_5_11 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsTridiagonal) (hsup : ∀ i : Fin n, T i.castSucc i.succ ≠ 0) {θ : ℝ}
    {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    v 0 ≠ 0 :=
  hT.apply_zero_ne_zero_of_superdiag_ne_zero
    (fun i hi => hsup ⟨i, by omega⟩) hv hv₀ (Nat.succ_pos _)

/-- Theorem 7.5.12. The right-hand side of the reduced subproblem has a nonzero pairing
with every eigenvector of the irreducible Lanczos tridiagonal, including those for its
smallest eigenvalue. The Lanczos starting coefficient is nonzero, as in the construction
from a nonzero starting gradient. -/
theorem theorem_7_5_12 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {γ : ℝ} (hγ : γ ≠ 0)
    {θ : ℝ} {v : Fin (n + 1) → ℝ} (hv : T *ᵥ v = θ • v) (hv₀ : v ≠ 0) :
    (Pi.single (0 : Fin (n + 1)) γ) ⬝ᵥ v ≠ 0 := by
  have hfirst : v 0 ≠ 0 :=
    hT.apply_zero_ne_zero_of_isSymm hS hv hv₀ (Nat.succ_pos _)
  rw [single_dotProduct]
  exact mul_ne_zero hγ hfirst

/-- Corollary 7.5.13. An irreducible full Lanczos tridiagonal rules out the hard
case in the original problem. In full coordinates every nonzero generalized
eigenvector has a nonzero pairing with the original gradient. -/
theorem corollary_7_5_13 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (H M : E →ₗ[ℝ] E) (hM : Function.Injective M)
    (Q : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] E) {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm)
    (hrel : ∀ y : Fin (n + 1) → ℝ, H (Q y) = M (Q (T *ᵥ y)))
    {g : E} {γ : ℝ} (hγ : γ ≠ 0)
    (hgrad : ∀ y : Fin (n + 1) → ℝ, inner ℝ g (Q y) = (Pi.single 0 γ) ⬝ᵥ y)
    {θ : ℝ} {v : E} (hv : H v = θ • M v) (hv₀ : v ≠ 0) :
    inner ℝ g v ≠ 0 := by
  obtain ⟨y, rfl⟩ := Q.surjective v
  have hy : T *ᵥ y = θ • y := by
    apply Q.injective
    apply hM
    rwa [← hrel, map_smul, map_smul]
  rw [hgrad]
  exact theorem_7_5_12 hT hS hγ hy (fun hz => hv₀ (by simp [hz]))

/-- Theorem 7.5.14. A positive semidefinite shift of the irreducible Lanczos
tridiagonal is positive definite if the shifted system has the prescribed right-hand
side with a nonzero starting coefficient. -/
theorem theorem_7_5_14 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hT : T.IsUnreducedUpperHessenberg) (hS : T.IsSymm) {γ μ : ℝ} (hγ : γ ≠ 0)
    {h : Fin (n + 1) → ℝ}
    (hh : (T + μ • 1) *ᵥ h = Pi.single 0 (-γ))
    (hpos : (T + μ • 1).PosSemidef) :
    (T + μ • 1).PosDef := by
  let A := T + μ • 1
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.mp hpos.isHermitian
  have hker (v : Fin (n + 1) → ℝ) (hv : A *ᵥ v = 0) : v = 0 := by
    by_contra hv₀
    have hev : T *ᵥ v = (-μ) • v := by
      have heq : T *ᵥ v + μ • v = 0 := by
        simpa only [A, add_mulVec, smul_mulVec, one_mulVec] using hv
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact heq
    have hdot := dotProduct_transpose_mulVec A h v
    rw [hsymm.eq, hv, hh, dotProduct_zero, dotProduct_single] at hdot
    have hfirst := hT.apply_zero_ne_zero_of_isSymm hS hev hv₀ (Nat.succ_pos _)
    exact (mul_ne_zero hfirst (neg_ne_zero.mpr hγ)) hdot.symm
  refine (hpos.posDef_iff_mulVec_injective).mpr fun u v huv => sub_eq_zero.mp ?_
  exact hker (u - v) (by rw [mulVec_sub, huv, sub_self])

/-- Theorem 7.5.15. If the last coordinate of the shifted-system solution vanishes,
a subdiagonal entry of the tridiagonal matrix vanishes. For a symmetric matrix
this means it is reducible. -/
theorem theorem_7_5_15 {n : ℕ} {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (htri : T.IsTridiagonal) {γ μ : ℝ} (hγ : γ ≠ 0) {h : Fin (n + 1) → ℝ}
    (hh : (T + μ • 1) *ᵥ h = Pi.single 0 (-γ)) (hlast : h (Fin.last n) = 0) :
    ∃ i : Fin n, T i.succ i.castSucc = 0 := by
  by_contra! hsub
  have hT : T.IsUnreducedUpperHessenberg := (isUnreducedUpperHessenberg_iff_fin.2
    ⟨htri.isUpperHessenberg, fun i hi => hsub ⟨i, by omega⟩⟩)
  let A := T + μ • 1
  have hoff {i j : Fin (n + 1)} (hij : i ≠ j) : A i j = T i j := by
    simp [A, one_apply_ne hij]
  have hbackward : ∀ j (hj : j ≤ n), h ⟨n - j, by omega⟩ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      cases j with
      | zero => simpa [Fin.last] using hlast
      | succ j =>
        let row : Fin (n + 1) := ⟨n - j, by omega⟩
        let col : Fin (n + 1) := ⟨n - (j + 1), by omega⟩
        have hr : 0 < (row : ℕ) := by dsimp [row]; omega
        have hcr : (col : ℕ) + 1 = (row : ℕ) := by dsimp [row, col]; omega
        have hrc : row ≠ col := fun he => by have := congrArg Fin.val he; omega
        have hrow := congrFun hh row
        change ∑ a, A row a * h a = (Pi.single 0 (-γ) : Fin (n + 1) → ℝ) row at hrow
        have hr₀ : row ≠ 0 := fun he => by have := congrArg Fin.val he; simpa using hr.ne' this
        rw [Pi.single_eq_of_ne hr₀] at hrow
        rw [Finset.sum_eq_single col] at hrow
        · have hne : T row col ≠ 0 := by
            have he : row = ⟨(col : ℕ) + 1, by omega⟩ := Fin.ext hcr.symm
            rw [he]
            exact (isUnreducedUpperHessenberg_iff_fin.1 hT).2 (col : ℕ) (by omega)
          exact (mul_eq_zero.mp hrow).resolve_left (by simpa [hoff hrc] using hne)
        · intro a _ hac
          rcases lt_or_gt_of_ne (fun he => hac (Fin.ext he)) with hal | hla
          · have har : a ≠ row := fun he => by have := congrArg Fin.val he; omega
            rw [hoff har.symm, htri row a (Or.inl ⟨col, Fin.lt_def.2 hal,
              Fin.lt_def.2 (by omega)⟩), zero_mul]
          · have hz := ih (n - (a : ℕ)) (by dsimp [col] at hla; omega) (by omega)
            have he : (⟨n - (n - (a : ℕ)), by omega⟩ : Fin (n + 1)) = a :=
              Fin.ext (by simp; omega)
            rw [he] at hz
            rw [hz, mul_zero]
        · simp
  have hzero : h = 0 := by
    funext a
    change h a = 0
    have hz := hbackward (n - (a : ℕ)) (by omega)
    have he : (⟨n - (n - (a : ℕ)), by omega⟩ : Fin (n + 1)) = a :=
      Fin.ext (by simp; omega)
    rwa [he] at hz
  have hfirst := congrFun hh (0 : Fin (n + 1))
  simp [hzero, hγ] at hfirst

/-- Theorem 7.5.16. In the easy case, a Lanczos breakdown makes the reduced trust-region
solution global. For a preconditioned problem, the ambient space carries the preconditioner
inner product, `H` represents the preconditioned Hessian and `g` the preconditioned gradient. -/
theorem theorem_7_5_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {H : E →L[ℝ] E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    {g : E} {n : ℕ} (hbreak : Lanczos.beta (H : E →ₗ[ℝ] E) g n = 0)
    (heasy : ∃ v, H v = Subproblem.leftmost hH • v ∧ inner ℝ v g ≠ 0)
    {Δ : ℝ} (hΔ : 0 < Δ) {s : E} (hsΔ : ‖s‖ ≤ Δ)
    (hs : s ∈ Krylov.subspace (H : E →ₗ[ℝ] E) g (n + 1))
    (hmin : IsMinOn (Subproblem.quadModel g H)
      ((Krylov.subspace (H : E →ₗ[ℝ] E) g (n + 1) : Set E) ∩ Metric.closedBall 0 Δ) s) :
    IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) s := by
  have hgrade := (Lanczos.beta_eq_zero_iff g n).mp hbreak
  apply Subproblem.isMinOn_closedBall_of_isMinOn_invariant_subspace hH _
    (Subproblem.mem_krylov H g (Nat.succ_pos n)) heasy hΔ hs hsΔ hmin
  rw [Krylov.subspace_eq_of_grade_le _ _ hgrade]
  exact Krylov.subspace_grade_mem_invtSubmodule _ _

/-- Theorem 7.5.17. Work in the preconditioner inner product. The invariant
subspace `V` is the image of the first Lanczos block, and `v` is the lift
of a leftmost eigenvector from the final block. If the first-block multiplier
reaches the global threshold, its step already solves the full problem.
Otherwise the threshold system on the first block has a unique solution,
and an orthogonal eigenvector correction takes it to the boundary. -/
theorem theorem_7_5_17 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {H : E →L[ℝ] E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (V : Submodule ℝ E) (hV : ∀ x ∈ V, H x ∈ V)
    {g s v : E} {Δ μ θ : ℝ}
    (hsV : s ∈ V) (hsΔ : ‖s‖ ≤ Δ) (hμ : 0 ≤ μ)
    (hs : (H + μ • (1 : E →L[ℝ] E)) s = -g) (hc : μ * (‖s‖ - Δ) = 0)
    (hfirst : ∀ x ∈ V, x ≠ 0 → 0 < inner ℝ ((H + μ • (1 : E →L[ℝ] E)) x) x)
    (hθ : θ = -Subproblem.leftmost hH)
    (hv : H v = (-θ) • v) (hv₀ : v ≠ 0) (hvV : v ∈ Vᗮ) :
    (θ ≤ μ → IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) s) ∧
    (μ < θ → ∃ y ∈ V, (H + θ • (1 : E →L[ℝ] E)) y = -g ∧
      (∀ z ∈ V, (H + θ • (1 : E →L[ℝ] E)) z = -g → z = y) ∧
      ∃ α : ℝ, ‖y‖ ^ 2 + α ^ 2 * ‖v‖ ^ 2 = Δ ^ 2 ∧
        IsMinOn (Subproblem.quadModel g H) (Metric.closedBall 0 Δ) (y + α • v)) := by
  open scoped RealInnerProductSpace in
  constructor
  · intro h
    have hpos : ((H + μ • (1 : E →L[ℝ] E) : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive :=
      Subproblem.isPositive_add_smul_of_le (hH := hH) (hθ ▸ h)
    exact (⟨hμ, hs, hpos, hc⟩ : Subproblem.IsTrustRegionMultiplier g H Δ s μ).isMinOn hH
  · intro h
    let A := H + θ • (1 : E →L[ℝ] E)
    let B := H + μ • (1 : E →L[ℝ] E)
    have hA (x : E) : A x = B x + (θ - μ) • x := by
      change H x + θ • x = H x + μ • x + (θ - μ) • x
      rw [add_assoc, ← add_smul, add_sub_cancel]
    have hAV (x : E) (hx : x ∈ V) : A x ∈ V := by
      change H x + θ • x ∈ V
      exact V.add_mem (hV x hx) (V.smul_mem _ hx)
    have hrhs : -g ∈ V := by
      rw [← hs]
      exact V.add_mem (hV s hsV) (V.smul_mem _ hsV)
    let C : V →ₗ[ℝ] V :=
      (((A : E →ₗ[ℝ] E).comp V.subtype).codRestrict V fun x => hAV x x.property)
    have hker (x : V) (hx : C x = 0) : x = 0 := by
      by_contra hn
      have hx₀ : (x : E) ≠ 0 := fun he => hn (Subtype.ext he)
      have he : A (x : E) = 0 := congrArg Subtype.val hx
      rw [hA] at he
      have hpos := hfirst x x.property hx₀
      have hin := congrArg (fun z : E => inner ℝ z (x : E)) he
      simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hin
      linarith [mul_nonneg (sub_nonneg.mpr h.le) (real_inner_self_nonneg (x := (x : E)))]
    have hinj : Function.Injective C := by
      intro x z he
      apply sub_eq_zero.mp
      apply hker
      rw [map_sub, he, sub_self]
    obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨-g, hrhs⟩
    have hys : A (y : E) = -g := congrArg Subtype.val hy
    have hdiff : B (s - (y : E)) = (θ - μ) • (y : E) := by
      have hys' := hys
      rw [hA] at hys'
      rw [map_sub, show B s = -g from hs, ← hys', add_sub_cancel_left]
    have hcross : 0 ≤ inner ℝ (y : E) (s - (y : E)) := by
      have hpos : 0 ≤ inner ℝ (B (s - (y : E))) (s - (y : E)) := by
        by_cases hz : s - (y : E) = 0
        · simp [hz]
        · exact (hfirst _ (V.sub_mem hsV y.property) hz).le
      rw [hdiff, real_inner_smul_left] at hpos
      exact nonneg_of_mul_nonneg_right hpos (sub_pos.mpr h)
    have hyΔ : ‖(y : E)‖ ≤ Δ := by
      have hsq := norm_add_sq_real (y : E) (s - (y : E))
      rw [add_comm (y : E), sub_add_cancel] at hsq
      have hle : ‖(y : E)‖ ^ 2 ≤ ‖s‖ ^ 2 := by
        linarith [sq_nonneg ‖s - (y : E)‖]
      exact ((pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle).trans hsΔ
    have hort : inner ℝ (y : E) v = 0 := hvV y y.property
    have hΔ : 0 ≤ Δ := (norm_nonneg _).trans hsΔ
    obtain ⟨α, hα, -⟩ := Subproblem.exists_norm_particular_add_smul_eq hort hv₀
      (pow_le_pow_left₀ (norm_nonneg _) hyΔ 2)
    have hnorm := (pow_left_inj₀ (norm_nonneg _) hΔ two_ne_zero).mp hα
    have hαsq := norm_add_sq_real (y : E) (α • v)
    rw [hα, inner_smul_right, hort, mul_zero, mul_zero, add_zero,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hαsq
    have hvker : A v = 0 := by
      change H v + θ • v = 0
      rw [hv, neg_smul, neg_add_cancel]
    refine ⟨y, y.property, hys, ?_, α, hαsq.symm, ?_⟩
    · intro z hz hzs
      exact congrArg Subtype.val (hinj (show C ⟨z, hz⟩ = C y from Subtype.ext (hzs.trans hys.symm)))
    · have hpos : (A : E →ₗ[ℝ] E).IsPositive :=
        Subproblem.isPositive_add_smul_of_le (hH := hH) hθ.ge
      have hshift : A ((y : E) + α • v) = -g := by
        rw [map_add, map_smul, hys, hvker, smul_zero, add_zero]
      exact (⟨hμ.trans h.le, hshift, hpos, by rw [hnorm, sub_self, mul_zero]⟩ :
        Subproblem.IsTrustRegionMultiplier g H Δ ((y : E) + α • v) θ).isMinOn hH

end ConnGouldToint.Chapter07
