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
