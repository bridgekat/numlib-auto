import Numlib.Optimization.WeightedSecularResolvent

/-!
# Derivatives of genuine shifted inverse steps

Finite spectral expansions give all actual vector derivatives of the negative shifted
resolvent. The formulas are local to nonsingular shifts and do not assume derivative data.
-/

open scoped BigOperators Topology
open Set Filter
open Optimization.QuadraticSubproblem

namespace Optimization.SecularResolvent

section Spectral
variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite vector-valued spectral expansion of a negative resolvent. -/
noncomputable def spectralStep (e γ : ι → ℝ) (v : ι → F) (t : ℝ) : F :=
  ∑ i, (-γ i / (t + e i)) • v i

/-- Coefficient identity for differentiating an inverse. -/
theorem inverse_derivative_coefficient (k : ℕ) :
    (∏ i ∈ Finset.range k, (-1 - (i : ℝ))) = (-1 : ℝ) ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, pow_succ, Nat.factorial_succ]
    push_cast
    ring

/-- Actual scalar derivatives of a negative shifted inverse. -/
theorem iteratedDeriv_neg_div_add (γ e : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x : ℝ => -γ / (x + e)) t =
      (-1 : ℝ) ^ (k + 1) * k.factorial * γ / (t + e) ^ (k + 1) := by
  have he : (fun x : ℝ => -γ / (x + e)) =
      (fun x : ℝ => -γ * (x + e) ^ (-1 : ℤ)) := by
    ext x
    simp [zpow_neg, div_eq_mul_inv]
  rw [he, iteratedDeriv_const_mul_field]
  have hshift := congrFun (iteratedDeriv_comp_add_const k
    (fun x : ℝ => x ^ (-1 : ℤ)) e) t
  rw [hshift, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp only [Int.cast_neg, Int.cast_one]
  rw [inverse_derivative_coefficient]
  have hz : (-1 : ℤ) - (k : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
  rw [hz, zpow_neg, zpow_natCast, pow_succ]
  ring

/-- Every actual vector derivative of the spectral expansion. -/
theorem iteratedDeriv_spectralStep (e γ : ι → ℝ) (v : ι → F) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + e i ≠ 0) :
    iteratedDeriv k (spectralStep e γ v) t =
      ∑ i, ((-1 : ℝ) ^ (k + 1) * k.factorial * γ i /
        (t + e i) ^ (k + 1)) • v i := by
  have hc (i : ι) : ContDiffAt ℝ k (fun x : ℝ => -γ i / (x + e i)) t :=
    contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) (ht i)
  unfold spectralStep
  rw [iteratedDeriv_fun_sum (f := fun i x => (-γ i / (x + e i)) • v i)
    (fun i _ => (hc i).smul contDiffAt_const)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_smul_const (hc i), iteratedDeriv_neg_div_add]

/-- A generalized eigenvector expansion satisfies the differentiated shifted equation. -/
theorem shift_iteratedDeriv_spectralStep (e γ : ι → ℝ) (v : ι → F)
    (H M : F →ₗ[ℝ] F) (hv : ∀ i, H (v i) = e i • M (v i)) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + e i ≠ 0) :
    (H + t • M) (iteratedDeriv (k + 1) (spectralStep e γ v) t) =
      -((k + 1 : ℕ) : ℝ) • M (iteratedDeriv k (spectralStep e γ v) t) := by
  rw [iteratedDeriv_spectralStep e γ v (k + 1) ht,
    iteratedDeriv_spectralStep e γ v k ht]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.add_apply, LinearMap.smul_apply, hv, ← add_smul, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  have hi := ht i
  field_simp
  rw [pow_succ (-1 : ℝ), pow_succ (t + e i)]
  ring

end Spectral

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)

/-- The genuine negative shifted inverse applied to a fixed vector. -/
noncomputable def resolventStep (H : E →ₗ[ℝ] E) (g : E) (t : ℝ) : E :=
  -Ring.inverse (H + t • (1 : E →ₗ[ℝ] E)) g

/-- The genuine negative resolvent is its spectral expansion away from the poles. -/
theorem resolventStep_eq_spectralStep (g : E) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    resolventStep H g t = spectralStep (hH.eigenvalues rfl)
      (fun i => (hH.eigenvectorBasis rfl).repr g i) (hH.eigenvectorBasis rfl) t := by
  rw [← (hH.eigenvectorBasis rfl).sum_repr (resolventStep H g t)]
  unfold spectralStep
  apply Finset.sum_congr rfl
  intro i _
  rw [resolventStep, map_neg, PiLp.neg_apply, repr_inverse_apply hH g t ht]
  simp only [neg_div]

/-- Equality with the spectral expansion holds on a whole regular neighborhood. -/
theorem eventuallyEq_resolventStep (g : E) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    resolventStep H g =ᶠ[𝓝 t] spectralStep (hH.eigenvalues rfl)
      (fun i => (hH.eigenvectorBasis rfl).repr g i) (hH.eigenvectorBasis rfl) := by
  have he : ∀ᶠ x in 𝓝 t, ∀ i, x + hH.eigenvalues rfl i ≠ 0 := by
    rw [eventually_all]
    exact fun i => (continuousAt_id.add continuousAt_const).eventually_ne (ht i)
  filter_upwards [he] with x hx
  exact resolventStep_eq_spectralStep hH g hx

/-- Exact all-order actual vector derivative formula for the genuine resolvent step. -/
theorem iteratedDeriv_resolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    iteratedDeriv k (resolventStep H g) t =
      ∑ i, ((-1 : ℝ) ^ (k + 1) * k.factorial * (hH.eigenvectorBasis rfl).repr g i /
        (t + hH.eigenvalues rfl i) ^ (k + 1)) • (hH.eigenvectorBasis rfl) i := by
  rw [(eventuallyEq_resolventStep hH g ht).iteratedDeriv_eq k]
  exact iteratedDeriv_spectralStep _ _ _ k ht

/-- Actual vector derivatives solve the recursively differentiated shifted system. -/
theorem shift_iteratedDeriv_resolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    (H + t • (1 : E →ₗ[ℝ] E)) (iteratedDeriv (k + 1) (resolventStep H g) t) =
      -((k + 1 : ℕ) : ℝ) • iteratedDeriv k (resolventStep H g) t := by
  rw [(eventuallyEq_resolventStep hH g ht).iteratedDeriv_eq (k + 1),
    (eventuallyEq_resolventStep hH g ht).iteratedDeriv_eq k]
  exact shift_iteratedDeriv_spectralStep _ _ _ H 1
    (fun i => by simpa only [RCLike.ofReal_real_eq_id, id_eq, Module.End.one_apply]
      using hH.apply_eigenvectorBasis rfl i) k ht

/-- Spectral coordinates of every actual vector derivative. -/
theorem repr_iteratedDeriv_resolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) (i : Fin (Module.finrank ℝ E)) :
    (hH.eigenvectorBasis rfl).repr (iteratedDeriv k (resolventStep H g) t) i =
      (-1 : ℝ) ^ (k + 1) * k.factorial * (hH.eigenvectorBasis rfl).repr g i /
        (t + hH.eigenvalues rfl i) ^ (k + 1) := by
  rw [iteratedDeriv_resolventStep hH g k ht]
  simp [Pi.single_apply]

/-- Inner products of actual vector derivatives in spectral coordinates. -/
theorem inner_iteratedDeriv_resolventStep (g : E) (k l : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    inner ℝ (iteratedDeriv k (resolventStep H g) t)
      (iteratedDeriv l (resolventStep H g) t) =
      (-1 : ℝ) ^ (k + l) * k.factorial * l.factorial *
        ∑ i, ((hH.eigenvectorBasis rfl).repr g i) ^ 2 /
          (t + hH.eigenvalues rfl i) ^ (k + l + 2) := by
  rw [← (hH.eigenvectorBasis rfl).repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, repr_iteratedDeriv_resolventStep hH g k ht,
    repr_iteratedDeriv_resolventStep hH g l ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_mul_div_comm, ← pow_add,
    show (l + 1) + (k + 1) = k + l + 2 by omega]
  rw [← mul_div_assoc]
  congr 1
  simp only [pow_succ, pow_add]
  ring

/-- Coefficients relating derivatives of a squared resolvent to its vector derivatives. -/
noncomputable def secularDerivativeCoefficient (k : ℕ) : ℝ :=
  ((2 * k + 1).factorial : ℝ) / (k.factorial : ℝ) ^ 2

/-- The initial derivative coefficient is one. -/
@[simp] theorem secularDerivativeCoefficient_zero : secularDerivativeCoefficient 0 = 1 := by
  norm_num [secularDerivativeCoefficient]

/-- Recursive form of the secular derivative coefficients. -/
theorem secularDerivativeCoefficient_succ (k : ℕ) :
    secularDerivativeCoefficient (k + 1) =
      2 * (2 * (k : ℝ) + 3) / (k + 1) * secularDerivativeCoefficient k := by
  unfold secularDerivativeCoefficient
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
    Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  simp only [Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Odd derivatives of the squared norm are pairings of consecutive actual step derivatives. -/
theorem iteratedDeriv_normSqResolvent_odd (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    iteratedDeriv (2 * k + 1) (normSqResolvent H g) t =
      2 * secularDerivativeCoefficient k *
        inner ℝ (iteratedDeriv k (resolventStep H g) t)
          (iteratedDeriv (k + 1) (resolventStep H g) t) := by
  rw [iteratedDeriv_normSqResolvent hH g (2 * k + 1) ht,
    inner_iteratedDeriv_resolventStep hH g k (k + 1) ht]
  have hindex : k + (k + 1) + 2 = 2 * k + 1 + 2 := by omega
  rw [hindex]
  have hsign1 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by simp [pow_add, pow_mul]
  have hsign2 : (-1 : ℝ) ^ (k + (k + 1)) = -1 := by
    rw [show k + (k + 1) = 2 * k + 1 by omega, hsign1]
  rw [hsign1, hsign2, secularDerivativeCoefficient,
    show 2 * k + 1 + 1 = (2 * k + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  simp only [Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Even derivatives of the squared norm are squared norms of actual step derivatives. -/
theorem iteratedDeriv_normSqResolvent_even (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + hH.eigenvalues rfl i ≠ 0) :
    iteratedDeriv (2 * k + 2) (normSqResolvent H g) t =
      secularDerivativeCoefficient (k + 1) *
        ‖iteratedDeriv (k + 1) (resolventStep H g) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    inner_iteratedDeriv_resolventStep hH g (k + 1) (k + 1) ht,
    iteratedDeriv_normSqResolvent hH g (2 * k + 2) ht]
  have hindex : k + 1 + (k + 1) + 2 = 2 * k + 2 + 2 := by omega
  rw [hindex]
  have hsign1 : (-1 : ℝ) ^ (2 * k + 2) = 1 := by simp [pow_add, pow_mul]
  have hsign2 : (-1 : ℝ) ^ (k + 1 + (k + 1)) = 1 := by
    rw [show k + 1 + (k + 1) = 2 * k + 2 by omega, hsign1]
  rw [hsign1, hsign2, secularDerivativeCoefficient,
    show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by omega]
  have hk : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Operator
section Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}
  (hM : Krylov.IsPreconditioner M Minv) (H : E →L[ℝ] E) (hH : H.IsSymmetric)

/-- The genuine negative shifted inverse in a positive definite metric. -/
noncomputable def weightedResolventStep (H M : E →ₗ[ℝ] E) (g : E) (t : ℝ) : E :=
  -Ring.inverse (H + t • M) g

/-- The actual metric step has the generalized eigenvector expansion. -/
theorem weightedResolventStep_eq_spectralStep (g : E) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    weightedResolventStep H.toLinearMap M g t =
      spectralStep ((energyHessian_isSymmetric hM H hH).eigenvalues rfl)
        (fun i => ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl).repr
          (hM.toEnergy (Minv g)) i)
        (fun i => hM.toEnergy.symm
          ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl i)) t := by
  apply hM.toEnergy.injective
  simp only [weightedResolventStep, map_neg, spectralStep, map_sum, map_smul,
    LinearEquiv.apply_symm_apply]
  rw [← inverse_energy_shift hM H g (isUnit_shift (energyHessian_isSymmetric hM H hH) t ht)]
  exact resolventStep_eq_spectralStep (energyHessian_isSymmetric hM H hH)
    (hM.toEnergy (Minv g)) ht

/-- Every actual derivative of the metric step, expressed in generalized eigenvectors. -/
theorem iteratedDeriv_weightedResolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    iteratedDeriv k (weightedResolventStep H.toLinearMap M g) t =
      ∑ i, ((-1 : ℝ) ^ (k + 1) * k.factorial *
        ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl).repr
          (hM.toEnergy (Minv g)) i /
        (t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i) ^ (k + 1)) •
        hM.toEnergy.symm ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl i) := by
  have he : weightedResolventStep H.toLinearMap M g =ᶠ[𝓝 t]
      spectralStep ((energyHessian_isSymmetric hM H hH).eigenvalues rfl)
        (fun i => ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl).repr
          (hM.toEnergy (Minv g)) i)
        (fun i => hM.toEnergy.symm
          ((energyHessian_isSymmetric hM H hH).eigenvectorBasis rfl i)) := by
    have ha : ∀ᶠ x in 𝓝 t, ∀ i,
        x + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0 := by
      rw [eventually_all]
      exact fun i => (continuousAt_id.add continuousAt_const).eventually_ne (ht i)
    filter_upwards [ha] with x hx
    exact weightedResolventStep_eq_spectralStep hM H hH g hx
  rw [he.iteratedDeriv_eq k]
  exact iteratedDeriv_spectralStep _ _ _ k ht

/-- Actual vector derivatives commute with the metric change of coordinates. -/
theorem toEnergy_iteratedDeriv_weightedResolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    hM.toEnergy (iteratedDeriv k (weightedResolventStep H.toLinearMap M g) t) =
      iteratedDeriv k (resolventStep (energyHessian hM H).toLinearMap
        (hM.toEnergy (Minv g))) t := by
  rw [iteratedDeriv_weightedResolventStep hM H hH g k ht,
    iteratedDeriv_resolventStep (energyHessian_isSymmetric hM H hH) _ k ht]
  simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]

/-- Actual metric step derivatives solve the original recursively differentiated system. -/
theorem shift_iteratedDeriv_weightedResolventStep (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    (H.toLinearMap + t • M)
      (iteratedDeriv (k + 1) (weightedResolventStep H.toLinearMap M g) t) =
      -((k + 1 : ℕ) : ℝ) • M (iteratedDeriv k
        (weightedResolventStep H.toLinearMap M g) t) := by
  have hs := shift_iteratedDeriv_resolventStep (energyHessian_isSymmetric hM H hH)
    (hM.toEnergy (Minv g)) k ht
  rw [← toEnergy_iteratedDeriv_weightedResolventStep hM H hH g (k + 1) ht,
    ← toEnergy_iteratedDeriv_weightedResolventStep hM H hH g k ht,
    energy_shift_apply] at hs
  have hp : Minv ((H.toLinearMap + t • M)
      (iteratedDeriv (k + 1) (weightedResolventStep H.toLinearMap M g) t)) =
      -((k + 1 : ℕ) : ℝ) • iteratedDeriv k
        (weightedResolventStep H.toLinearMap M g) t := by
    apply hM.toEnergy.injective
    simpa only [map_smul] using hs
  have hm := congrArg M hp
  simpa only [hM.apply_inv, map_smul] using hm

/-- Odd metric secular derivatives are pairings of consecutive actual step derivatives. -/
theorem iteratedDeriv_weightedNormSqResolvent_odd (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    iteratedDeriv (2 * k + 1) (weightedNormSqResolvent H.toLinearMap M g) t =
      2 * secularDerivativeCoefficient k *
        inner ℝ (iteratedDeriv k (weightedResolventStep H.toLinearMap M g) t)
          (M (iteratedDeriv (k + 1) (weightedResolventStep H.toLinearMap M g) t)) := by
  rw [(eventuallyEq_weightedNormSqResolvent hM H hH g ht).iteratedDeriv_eq (2 * k + 1),
    iteratedDeriv_normSqResolvent_odd (energyHessian_isSymmetric hM H hH) _ k ht,
    ← toEnergy_iteratedDeriv_weightedResolventStep hM H hH g k ht,
    ← toEnergy_iteratedDeriv_weightedResolventStep hM H hH g (k + 1) ht]
  congr 1
  simpa only [hM.inv_apply] using hM.inner_toEnergy_inv
    (iteratedDeriv k (weightedResolventStep H.toLinearMap M g) t)
    (M (iteratedDeriv (k + 1) (weightedResolventStep H.toLinearMap M g) t))

/-- Even metric secular derivatives are squared metric norms of actual step derivatives. -/
theorem iteratedDeriv_weightedNormSqResolvent_even (g : E) (k : ℕ) {t : ℝ}
    (ht : ∀ i, t + (energyHessian_isSymmetric hM H hH).eigenvalues rfl i ≠ 0) :
    iteratedDeriv (2 * k + 2) (weightedNormSqResolvent H.toLinearMap M g) t =
      secularDerivativeCoefficient (k + 1) *
        energyNorm M (iteratedDeriv (k + 1) (weightedResolventStep H.toLinearMap M g) t) ^ 2 := by
  rw [(eventuallyEq_weightedNormSqResolvent hM H hH g ht).iteratedDeriv_eq (2 * k + 2),
    iteratedDeriv_normSqResolvent_even (energyHessian_isSymmetric hM H hH) _ k ht,
    ← toEnergy_iteratedDeriv_weightedResolventStep hM H hH g (k + 1) ht]
  rfl

end Metric
end Optimization.SecularResolvent
