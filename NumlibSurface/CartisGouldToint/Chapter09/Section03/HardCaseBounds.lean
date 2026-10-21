import Numlib.Optimization.AdaptiveInverseIterationLocal
import NumlibSurface.CartisGouldToint.Chapter09.Section03.HardCase

/-!
# Chapter 9, Section 3: genuine hard-case spectral error bounds

The actual metric iteration preserves a uniform lowest-eigenspace coordinate on every
positive-shift prefix. Eventual constancy of the actual batch counts gives a finite constant
in the Rayleigh-error bound, even if the allowed count limit is infinite. These are spectral
estimates for Algorithm 9.3.1. The local bootstrap proves genuine convergence and eventual
consecutive power bounds for Theorem 9.3.1.
-/

noncomputable section
open scoped InnerProductSpace Topology
open Filter Optimization.AdaptiveInverseIteration
open CartisGouldToint.Chapter08.Section01 CartisGouldToint.Chapter08.Section02
namespace CartisGouldToint.Chapter09.Section03
variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The Hessian Rayleigh numerator of the actual source state equals its energy-coordinate
Rayleigh numerator, at every outer index and without a spectral regularity assumption. -/
theorem hardCaseIterate_rayleigh_eq_energy (hM : M.PosDef) (lambda : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice) (k : ℕ) :
    inner ℝ (hardCaseIterate (H := H) hM lambda z c k).vector
      (Matrix.toEuclideanLin H (hardCaseIterate (H := H) hM lambda z c k).vector) =
    inner ℝ (iterate (secularHessian H hM)
      ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k).vector
      (secularHessian H hM (iterate (secularHessian H hM)
        ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k).vector) := by
  have he := Krylov.inner_energyHessian_toEnergy hM.isPreconditioner_toEuclideanLin
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H)
      (hardCaseIterate (H := H) hM lambda z c k).vector
  change inner ℝ
    (hM.isPreconditioner_toEuclideanLin.toEnergy
      (hardCaseIterate (H := H) hM lambda z c k).vector)
    (secularHessian H hM (hM.isPreconditioner_toEuclideanLin.toEnergy
      (hardCaseIterate (H := H) hM lambda z c k).vector)) =
    inner ℝ (hardCaseIterate (H := H) hM lambda z c k).vector
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) H).toLinearMap
        (hardCaseIterate (H := H) hM lambda z c k).vector) at he
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at he
  simpa only [hardCaseIterate, LinearEquiv.apply_symm_apply] using he.symm

/-- A nonzero metric lowest-eigenspace component has a fixed absolute coordinate lower
bound on every positive-shift prefix of the actual source iteration. -/
theorem hardCaseIterate_lowestCoordinate_ge (hH : H.IsSymm) (hM : M.PosDef)
    (lambda : ℝ) (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice)
    (hz : weightedNorm M z = 1) {i}
    (hlo : ∀ j, secularEigenvalues hH hM i ≤ secularEigenvalues hH hM j) (k : ℕ)
    (hshift : ∀ j < k, 0 < (hardCaseIterate (H := H) hM lambda z c j).shift +
      secularEigenvalues hH hM i) :
    |((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
      (hM.isPreconditioner_toEuclideanLin.toEnergy z) i| ≤
    |((secularHessian_isSymmetric hH hM).eigenvectorBasis rfl).repr
      (hM.isPreconditioner_toEuclideanLin.toEnergy
        (hardCaseIterate (H := H) hM lambda z c k).vector) i| := by
  have h0 : ‖hM.isPreconditioner_toEuclideanLin.toEnergy z‖ = 1 := by
    simpa only [WithEnergy.norm_equiv, ← weightedNorm_eq_energyNorm] using hz
  simpa only [hardCaseIterate, LinearEquiv.apply_symm_apply] using
    abs_repr_iterate_vector_ge (secularHessian_isSymmetric hH hM)
      ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c h0 hlo k hshift

/-- The nonzero metric projection and the actual eventually constant count stream give
a uniform Rayleigh-error constant, independent of the initial shift, for all positive-shift
prefixes. No Rayleigh estimate,
finite count parameter, or spectral coefficient is supplied as algorithmic data. -/
theorem hardCaseIterate_rayleighError (hH : H.IsSymm) (hM : M.PosDef)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice)
    (hz : weightedNorm M z = 1) (hcomp : hasLowestComponent hH hM z)
    (nbar : ℕ) (hc : ∀ᶠ k in atTop, (c k).count = nbar) :
    ∃ i C, (∀ j, secularEigenvalues hH hM i ≤ secularEigenvalues hH hM j) ∧
      0 < C ∧ ∀ lambda k,
      (∀ j ≤ k, 0 < (hardCaseIterate (H := H) hM lambda z c j).shift +
        secularEigenvalues hH hM i) →
      let r := inner ℝ (hardCaseIterate (H := H) hM lambda z c (k + 1)).vector
        (Matrix.toEuclideanLin H (hardCaseIterate (H := H) hM lambda z c (k + 1)).vector) -
          secularEigenvalues hH hM i;
      0 ≤ r ∧ r ≤ C * ((hardCaseIterate (H := H) hM lambda z c k).shift +
        secularEigenvalues hH hM i) ^ (2 * (c k).count) := by
  obtain ⟨i, hlo, hi⟩ := hcomp
  have h0 : ‖hM.isPreconditioner_toEuclideanLin.toEnergy z‖ = 1 := by
    simpa only [WithEnergy.norm_equiv, ← weightedNorm_eq_energyNorm] using hz
  obtain ⟨C, hC, hbound⟩ := exists_uniform_iterate_rayleighError_constant
    (secularHessian_isSymmetric hH hM)
      (hM.isPreconditioner_toEuclideanLin.toEnergy z) c h0 hi hlo nbar hc
  refine ⟨i, C, hlo, hC, ?_⟩
  intro lambda k hshift
  let s : State hM.isPreconditioner_toEuclideanLin.EnergySpace :=
    ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩
  change ∀ j ≤ k, 0 < (iterate (secularHessian H hM) s c j).shift +
    (secularHessian_isSymmetric hH hM).eigenvalues rfl i at hshift
  change ∀ j, (secularHessian_isSymmetric hH hM).eigenvalues rfl i ≤
    (secularHessian_isSymmetric hH hM).eigenvalues rfl j at hlo
  dsimp only
  rw [hardCaseIterate_rayleigh_eq_energy]
  constructor
  · have hreg : ∀ l, (iterate (secularHessian H hM) s c k).shift +
        (secularHessian_isSymmetric hH hM).eigenvalues rfl l ≠ 0 :=
      fun l => ne_of_gt (by linarith [hshift k le_rfl, hlo l])
    have hn := norm_iterate_vector (secularHessian H hM) s c h0 k
      (fun j hj => Optimization.SecularResolvent.isUnit_shift
        (secularHessian_isSymmetric hH hM) _ (fun l =>
          ne_of_gt (by linarith [hshift j hj.le, hlo l])))
    simpa only [iterate_succ, update_vector, s] using
      sub_nonneg.mpr (Krylov.inner_shiftedInverseBatch_ge
        (secularHessian_isSymmetric hH hM) (iterate (secularHessian H hM) s c k).vector
        (norm_ne_zero_iff.mp (by rw [hn]; norm_num)) hreg hlo (c k).count)
  · exact hbound lambda k hshift

/-- Theorem 9.3.1 for the actual metric adaptive inverse iteration, with repeated lowest
eigenvalues and a genuine nonzero metric lowest-eigenspace projection. The local radius may
depend on the actual eventually constant choice stream, including its finite early prefix.

The bounded `Q`-order conclusion is expressed by eventual two-sided consecutive power
bounds. This is the reading supported by Gould, Robinson and Thorne [196], Theorem 7,
proof (3.42)–(3.47). Bounded damping alone does not require an exact limit of the normalized
order quotient. The actual successive error quotient does tend to zero. -/
theorem theorem_9_3_1 (hH : H.IsSymm) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (target : ℝ → ℝ) (p : Parameters)
    (z : EuclideanSpace ℝ (Fin n)) (c : ℕ → Choice)
    (hz : weightedNorm M z = 1) (hcomp : hasLowestComponent hH hM z)
    (hlegal : ∀ k, (c k).Legal p) (nbar : ℕ) (gammaBar : ℝ)
    (hcount : ∀ᶠ k in atTop, (c k).count = nbar)
    (hexponent : ∀ᶠ k in atTop, (c k).exponent = gammaBar)
    (i) (hlo : ∀ j, secularEigenvalues hH hM i ≤ secularEigenvalues hH hM j) :
    1 < gammaBar ∧ ∃ eta K : ℝ, 0 < eta ∧ 0 < K ∧ ∀ lambda s,
      algorithm_9_3_1 hH hM g target p lambda z c s →
      0 < lambda + secularEigenvalues hH hM i →
      lambda + secularEigenvalues hH hM i ≤ eta →
      let e := fun k => (s k).shift + secularEigenvalues hH hM i;
      Tendsto (fun k => (s k).shift) atTop (𝓝 (-secularEigenvalues hH hM i)) ∧
      (∀ k, 0 < e k ∧ e (k + 1) ≤ e k / 2) ∧
      Tendsto (fun k => e (k + 1) / e k) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, (p.dampingLower / 2) * (e k) ^ gammaBar ≤ e (k + 1) ∧
        e (k + 1) ≤ K * (e k) ^ gammaBar := by
  obtain ⟨k, hk⟩ := hexponent.exists
  have hgamma : 1 < gammaBar := by
    rw [← hk]
    exact p.exponent_lt.trans_le (hlegal k).2.2.2.1
  obtain ⟨j, hj, hzj⟩ := hcomp
  have heig : secularEigenvalues hH hM j = secularEigenvalues hH hM i :=
    le_antisymm (hj i) (hlo j)
  have h0 : ‖hM.isPreconditioner_toEuclideanLin.toEnergy z‖ = 1 := by
    simpa only [WithEnergy.norm_equiv, ← weightedNorm_eq_energyNorm] using hz
  obtain ⟨eta, K, heta, hK, hlocal⟩ := exists_local_iterate_bounds
    (secularHessian_isSymmetric hH hM) (hM.isPreconditioner_toEuclideanLin.toEnergy z)
      c p h0 hzj hj hlegal nbar hcount
  refine ⟨hgamma, eta, K, heta, hK, ?_⟩
  intro lambda s halg ht hte
  rw [algorithm_9_3_1_states halg]
  have htj : 0 < lambda + secularEigenvalues hH hM j := by simpa only [heig] using ht
  have htej : lambda + secularEigenvalues hH hM j ≤ eta := by simpa only [heig] using hte
  obtain ⟨hlim, hquot, hb⟩ := hlocal lambda htj htej
  have hshiftlim := hlim.sub_const (secularEigenvalues hH hM j)
  simp only [add_sub_cancel_right, zero_sub] at hshiftlim
  have horders : ∀ᶠ k in atTop,
      (p.dampingLower / 2) *
        ((iterate (secularHessian H hM)
          ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k).shift +
            secularEigenvalues hH hM j) ^ gammaBar ≤
          (iterate (secularHessian H hM)
            ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c (k + 1)).shift +
              secularEigenvalues hH hM j ∧
      (iterate (secularHessian H hM)
        ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c (k + 1)).shift +
          secularEigenvalues hH hM j ≤ K *
      ((iterate (secularHessian H hM)
        ⟨lambda, hM.isPreconditioner_toEuclideanLin.toEnergy z⟩ c k).shift +
          secularEigenvalues hH hM j) ^ gammaBar := by
    filter_upwards [hexponent] with k hk
    have hpair := And.intro (hb k).2.1 (hb k).2.2.1
    simpa only [hk] using hpair
  have hpositive := fun k => And.intro (hb k).1 (hb k).2.2.2
  have hresult := And.intro hshiftlim (And.intro hpositive (And.intro hquot horders))
  simpa only [hardCaseIterate, heig] using hresult

end CartisGouldToint.Chapter09.Section03
