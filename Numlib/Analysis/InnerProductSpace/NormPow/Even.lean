import Numlib.Analysis.Calculus.TaylorModel.JetBounds
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sharp derivative bounds for even integer norm powers

A product of inner products is a continuous multilinear tensor of norm at most
one whose diagonal is the even norm power. The exact falling-factorial bound
for its diagonal polynomial gives all derivative orders, including the origin.
-/

namespace NormPower
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product as an actual continuous bilinear tensor. -/
noncomputable def innerTensor : E [×2]→L[ℝ] ℝ :=
  let L := (continuousMultilinearCurryFin1 ℝ E ℝ).symm.toContinuousLinearEquiv
  (L.toContinuousLinearMap.comp (innerSL ℝ)).uncurryLeft

/-- Evaluation of the inner-product tensor. -/
theorem innerTensor_apply (v : Fin 2 → E) :
    innerTensor v = inner ℝ (v 0) (v 1) := by
  simp [innerTensor, ContinuousLinearMap.uncurryLeft_apply,
    continuousMultilinearCurryFin1_symm_apply, Fin.tail]

/-- Cauchy-Schwarz gives the sharp unit upper bound for the inner-product tensor. -/
theorem norm_innerTensor_le : ‖innerTensor (E := E)‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  rw [innerTensor_apply]
  simpa [Fin.prod_univ_succ] using norm_inner_le_norm (𝕜 := ℝ) (v 0) (v 1)

/-- The tensor product of k inner products, with its inputs reindexed consecutively. -/
noncomputable def pairedTensor : (k : ℕ) → E [×(2 * k)]→L[ℝ] ℝ
  | 0 => (continuousMultilinearCurryFin0 ℝ E ℝ).symm (1 : ℝ)
  | k + 1 => ContinuousMultilinearMap.domDomCongr
      (finSumFinEquiv.trans (finCongr (by omega : 2 + 2 * k = 2 * (k + 1))))
      ((innerTensor (E := E)).smulRight (pairedTensor k)).uncurrySum

/-- The paired tensor has the even norm power as its genuine diagonal polynomial. -/
theorem pairedTensor_diagonal (k : ℕ) (x : E) :
    pairedTensor k (fun _ => x) = ‖x‖ ^ (2 * k) := by
  induction k with
  | zero => simp [pairedTensor]
  | succ k ih =>
    rw [pairedTensor, ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.smulRight_apply]
    change innerTensor (fun _ => x) * pairedTensor k (fun _ => x) = _
    rw [innerTensor_apply, ih, real_inner_self_eq_norm_sq, ← pow_add]
    congr 1
    omega

/-- Every paired inner-product tensor has operator norm at most one. -/
theorem norm_pairedTensor_le (k : ℕ) : ‖pairedTensor (E := E) k‖ ≤ 1 := by
  induction k with
  | zero => rw [pairedTensor, LinearIsometryEquiv.norm_map]; norm_num
  | succ k ih =>
    rw [pairedTensor, ContinuousMultilinearMap.norm_domDomCongr]
    change ‖(ContinuousMultilinearMap.currySumEquiv ℝ (Fin 2) (Fin (2 * k)) E ℝ).symm
      (innerTensor.smulRight (pairedTensor k))‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map, ContinuousMultilinearMap.norm_smulRight]
    calc _ ≤ 1 * ‖pairedTensor (E := E) k‖ :=
        mul_le_mul_of_nonneg_right norm_innerTensor_le (norm_nonneg _)
      _ ≤ 1 := by simpa using ih

/-- Every finite derivative of an even norm power exists continuously, including at zero. -/
theorem contDiff_norm_pow_even (k n : ℕ) : ContDiff ℝ n (fun x : E => ‖x‖ ^ (2 * k)) := by
  have he : (fun x : E => ‖x‖ ^ (2 * k)) = fun x => pairedTensor k (fun _ => x) :=
    funext (fun x => (pairedTensor_diagonal k x).symm)
  rw [he]
  exact (pairedTensor k).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)

/-- The genuine jth derivative of an even norm power has the exact
falling-factorial operator bound, at every point and for all derivative orders. -/
theorem norm_iteratedFDeriv_norm_pow_even_le (k j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (2 * k)) x‖ ≤
      (Nat.descFactorial (2 * k) j : ℝ) * ‖x‖ ^ (2 * k - j) := by
  have he : (fun y : E => ‖y‖ ^ (2 * k)) = fun y => pairedTensor k (fun _ => y) :=
    funext (fun y => (pairedTensor_diagonal k y).symm)
  rw [he]
  calc _ ≤ (Nat.descFactorial (2 * k) j : ℝ) * ‖pairedTensor (E := E) k‖ *
        ‖x‖ ^ (2 * k - j) := TaylorModel.norm_iteratedFDeriv_diagonal_le _ x
    _ ≤ _ := by
      have hh := norm_pairedTensor_le (E := E) k
      nlinarith [mul_nonneg (Nat.cast_nonneg (Nat.descFactorial (2 * k) j))
        (pow_nonneg (norm_nonneg x) (2 * k - j))]

/-- The same exact derivative estimate with the source's factorial quotient. -/
theorem norm_iteratedFDeriv_norm_pow_even_le_factorial {k j : ℕ} (hj : j ≤ 2 * k)
    (x : E) : ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ (2 * k)) x‖ ≤
      ((2 * k).factorial : ℝ) / (2 * k - j).factorial * ‖x‖ ^ (2 * k - j) := by
  have hc : (Nat.descFactorial (2 * k) j : ℝ) =
      ((2 * k).factorial : ℝ) / (2 * k - j).factorial := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_descFactorial hj)
    push_cast at hh
    apply (eq_div_iff (by positivity : ((2 * k - j).factorial : ℝ) ≠ 0)).mpr
    nlinarith
  rw [← hc]
  exact norm_iteratedFDeriv_norm_pow_even_le k j x

/-- The highest actual derivative of an even norm power is bounded by its degree factorial. -/
theorem norm_iteratedFDeriv_norm_pow_even_top_le (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (2 * k) (fun y : E => ‖y‖ ^ (2 * k)) x‖ ≤
      ((2 * k).factorial : ℝ) := by
  simpa only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] using
    norm_iteratedFDeriv_norm_pow_even_le k (2 * k) x

/-- The actual derivative one order below an even norm power's degree is
Lipschitz with the exact degree-factorial constant. -/
theorem norm_sub_iteratedFDeriv_norm_pow_even_le {k : ℕ} (hk : 0 < k) (x y : E) :
    ‖iteratedFDeriv ℝ (2 * k - 1) (fun z : E => ‖z‖ ^ (2 * k)) x -
      iteratedFDeriv ℝ (2 * k - 1) (fun z : E => ‖z‖ ^ (2 * k)) y‖ ≤
        ((2 * k).factorial : ℝ) * ‖x - y‖ := by
  let g := iteratedFDeriv ℝ (2 * k - 1) (fun z : E => ‖z‖ ^ (2 * k))
  have he : 2 * k - 1 + 1 = 2 * k := by omega
  have hd (z : E) : DifferentiableAt ℝ g z :=
    (contDiff_norm_pow_even k (2 * k)).contDiffAt.differentiableAt_iteratedFDeriv (by
      exact_mod_cast (show 2 * k - 1 < 2 * k by omega))
  have hb (z : E) : ‖fderiv ℝ g z‖ ≤ ((2 * k).factorial : ℝ) := by
    rw [norm_fderiv_iteratedFDeriv, he]
    exact norm_iteratedFDeriv_norm_pow_even_top_le k z
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hd z)
    (fun z _ => hb z) (Set.mem_univ x) (Set.mem_univ y)

/-- The sharp derivative bound for an arbitrary even degree, without exposing
its half-degree representation to callers. -/
theorem norm_iteratedFDeriv_norm_pow_of_even {m j : ℕ} (hm : Even m) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => ‖y‖ ^ m) x‖ ≤
      (Nat.descFactorial m j : ℝ) * ‖x‖ ^ (m - j) := by
  obtain ⟨k, hk⟩ := hm
  rw [show m = 2 * k by omega]
  exact norm_iteratedFDeriv_norm_pow_even_le k j x

/-- The exact factorial Lipschitz estimate in the regularization degree convention. -/
theorem norm_sub_iteratedFDeriv_norm_pow_of_even {p : ℕ} (hp : Even (p + 1)) (x y : E) :
    ‖iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) x -
      iteratedFDeriv ℝ p (fun z : E => ‖z‖ ^ (p + 1)) y‖ ≤
        ((p + 1).factorial : ℝ) * ‖x - y‖ := by
  obtain ⟨k, hk⟩ := hp
  have he : p + 1 = 2 * k := by omega
  have hk0 : 0 < k := by omega
  have hp0 : p = 2 * k - 1 := by omega
  rw [he, hp0]
  exact norm_sub_iteratedFDeriv_norm_pow_even_le hk0 x y

end NormPower
