import Numlib.Optimization.Quadratic.HardCase.Spectral
import Numlib.Analysis.Asymptotics.PositivePower

/-!
# Local convergence of metric-projected generalized inverse iteration

A nonzero least-eigenspace coordinate supplies invariant relative-coordinate
bounds. The actual inverse block then has a higher-order Rayleigh error. A
fixed small initial radius preserves positive shifts and gives geometric decay
and two-sided superlinear power bounds, including arbitrary finite control
prefixes and bounded oscillatory weights.
-/

open Filter Topology
namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι] {H M : E →L[ℝ] E}
  (B : PencilBasis (ι := ι) H M)

omit [Fintype ι] in
/-- Actual normalized generalized inverse iteration converges locally from a
nonzero metric least-eigenspace coordinate, with uniform positive two-sided
power bounds and half-step error decay. -/
theorem exists_pos_radius_hardCase_convergence [Finite ι]
    (hM : M.toLinearMap.IsSymmetricCoercive) (least : ℝ)
    (hmin : ∀ i, least ≤ B.eigenvalue i) {l : ι} (hl : B.eigenvalue l = least)
    (v0 : E) (hv0 : B.basis.repr v0 l ≠ 0)
    (count : ℕ → ℕ) (exponent weight : ℕ → ℝ)
    (ωL ωU γL γU : ℝ) (hωL : 0 < ωL) (hωU : ωL ≤ ωU)
    (hγL : 1 < γL) (hγU : 0 < γU) (N : ℕ) (hN : ∀ k, count k ≤ N) :
    ∃ R > 0, ∀ (shift : ℕ → ℝ) (vector : ℕ → E) (innerVector : ℕ → ℕ → E)
      (nU : WithTop ℕ),
      HardCase.Run H M least shift vector innerVector count exponent weight
        ωL ωU γL γU nU →
      vector 0 = v0 → shift 0 + least ≤ R →
      (∀ k, 0 < shift k + least) ∧ Tendsto shift atTop (𝓝 (-least)) ∧
      (∀ k, shift (k + 1) + least ≤ (shift k + least) / 2) ∧
      ∀ k, ωL / 2 * (shift k + least) ^ exponent k ≤ shift (k + 1) + least ∧
        shift (k + 1) + least ≤ (ωU * 2 ^ (2 * (N : ℝ))) *
          (shift k + least) ^ exponent k := by
  let := Fintype.ofFinite ι
  let ratios : ι → ℝ := fun i => |B.basis.repr v0 i / B.basis.repr v0 l|
  let C := B.rayleighBoundConstant least ratios N
  have hC : 0 < C := B.rayleighBoundConstant_pos least hmin ratios N
  obtain ⟨R, hR, hR1, hsafe⟩ := Real.exists_pos_power_safeguards
    (C := C) (D := ωU * 2 ^ (2 * (N : ℝ))) hωL hγU (sub_pos.mpr hγL)
  refine ⟨R, hR, ?_⟩
  intro shift vector innerVector nU h hvinit hclose
  have hone (k : ℕ) (he : 0 < shift k + least) (heR : shift k + least ≤ R)
      (hne : B.basis.repr (vector k) l ≠ 0)
      (hrat : ∀ i, |B.basis.repr (vector k) i / B.basis.repr (vector k) l| ≤ ratios i) :
      B.basis.repr (vector (k + 1)) l ≠ 0 ∧
      (∀ i, |B.basis.repr (vector (k + 1)) i /
        B.basis.repr (vector (k + 1)) l| ≤ ratios i) ∧
      0 < shift (k + 1) + least ∧
      ωL / 2 * (shift k + least) ^ exponent k ≤ shift (k + 1) + least ∧
      shift (k + 1) + least ≤ (ωU * 2 ^ (2 * (N : ℝ))) *
        (shift k + least) ^ exponent k ∧
      shift (k + 1) + least ≤ (shift k + least) / 2 := by
    have hi := h.inner_initial k
    have hh := B.inverseBlock_rayleigh_bound hM least hmin hl (shift k)
      (by linarith) (h.shifted_invertible k) (innerVector k) (h.count_pos k) (hN k)
      (h.inner_update k) (by simpa only [hi] using hne) ratios
      (by simpa only [hi] using hrat)
    rw [← h.vector_update k] at hh
    obtain ⟨_, hnew, hratnew, hδ0, hδ⟩ := hh
    let δ := HardCase.rayleighValue H (vector (k + 1)) - least
    have hb := Real.positive_power_shift_bounds hC.le hωL hωU hγL hγU
      (h.count_pos k) (hN k) he (heR.trans hR1) hδ0 hδ (h.weight_range k)
      (h.exponent_range k) (hsafe _ he heR)
    have heq : shift (k + 1) + least =
        weight k * ((shift k + least) + δ) ^ exponent k - δ := by
      rw [h.shift_update k]
      dsimp only [δ]
      rw [show shift k + least + (HardCase.rayleighValue H (vector (k + 1)) - least) =
        shift k + HardCase.rayleighValue H (vector (k + 1)) by ring]
      ring
    change 0 < weight k * ((shift k + least) + δ) ^ exponent k - δ ∧ _ at hb
    rw [← heq] at hb
    exact ⟨hnew, hratnew, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hinv (k : ℕ) : 0 < shift k + least ∧ shift k + least ≤ R ∧
      B.basis.repr (vector k) l ≠ 0 ∧
      ∀ i, |B.basis.repr (vector k) i / B.basis.repr (vector k) l| ≤ ratios i := by
    induction k with
    | zero =>
      refine ⟨by linarith [h.initial_shift], hclose, ?_, ?_⟩
      · simpa only [hvinit] using hv0
      · intro i
        rw [hvinit]
    | succ k ih =>
      obtain ⟨hne, hrat, hpos, _, _, hhalf⟩ := hone k ih.1 ih.2.1 ih.2.2.1 ih.2.2.2
      exact ⟨hpos, (hhalf.trans (by linarith [ih.1])).trans ih.2.1, hne, hrat⟩
  have hbounds (k : ℕ) := hone k (hinv k).1 (hinv k).2.1 (hinv k).2.2.1 (hinv k).2.2.2
  have hhalf (k : ℕ) : shift (k + 1) + least ≤ (shift k + least) / 2 :=
    (hbounds k).2.2.2.2.2
  have hlimit := Real.tendsto_zero_of_pos_half_step (fun k => (hinv k).1) hhalf
  refine ⟨fun k => (hinv k).1, ?_, hhalf, fun k => ?_⟩
  · simpa only [add_sub_cancel_right, zero_sub] using hlimit.sub_const least
  · exact ⟨(hbounds k).2.2.2.1, (hbounds k).2.2.2.2.1⟩

omit [Fintype ι] in
/-- Eventual constancy permits arbitrary finite control prefixes and gives
the full eventual two-sided Q-order for the actual metric-projected method.
No limit of the bounded, possibly oscillating, weights is required. -/
theorem exists_pos_radius_hardCase_eventual_order [Finite ι]
    (hM : M.toLinearMap.IsSymmetricCoercive) (least : ℝ)
    (hmin : ∀ i, least ≤ B.eigenvalue i) {l : ι} (hl : B.eigenvalue l = least)
    (v0 : E) (hv0 : B.basis.repr v0 l ≠ 0)
    (count : ℕ → ℕ) (exponent weight : ℕ → ℝ)
    (ωL ωU γL γU : ℝ) (hωL : 0 < ωL) (hωU : ωL ≤ ωU)
    (hγL : 1 < γL) (hγU : 0 < γU) (nbar : ℕ) (γbar : ℝ)
    (hnbar : ∀ᶠ k in atTop, count k = nbar)
    (hγbar : ∀ᶠ k in atTop, exponent k = γbar) :
    ∃ R > 0, ∃ A > 0, ∃ D > 0,
      ∀ (shift : ℕ → ℝ) (vector : ℕ → E) (innerVector : ℕ → ℕ → E)
        (nU : WithTop ℕ),
        HardCase.Run H M least shift vector innerVector count exponent weight
          ωL ωU γL γU nU →
        vector 0 = v0 → shift 0 + least ≤ R →
        (∀ k, 0 < shift k + least) ∧ Tendsto shift atTop (𝓝 (-least)) ∧
        (∀ k, shift (k + 1) + least ≤ (shift k + least) / 2) ∧
        ∀ᶠ k in atTop, A * (shift k + least) ^ γbar ≤ shift (k + 1) + least ∧
          shift (k + 1) + least ≤ D * (shift k + least) ^ γbar := by
  obtain ⟨N, hN⟩ := Real.exists_nat_bound_of_eventually_const hnbar
  obtain ⟨R, hR, hb⟩ := B.exists_pos_radius_hardCase_convergence hM least hmin hl v0 hv0
    count exponent weight ωL ωU γL γU hωL hωU hγL hγU N hN
  refine ⟨R, hR, ωL / 2, half_pos hωL, ωU * 2 ^ (2 * (N : ℝ)), ?_, ?_⟩
  · have hh : 0 < ωU := hωL.trans_le hωU
    positivity
  · intro shift vector innerVector nU h hvinit hclose
    obtain ⟨hpos, hlim, hhalf, hrate⟩ := hb shift vector innerVector nU h hvinit hclose
    refine ⟨hpos, hlim, hhalf, ?_⟩
    filter_upwards [hγbar] with k hk
    simpa only [hk] using hrate k

end QuadraticSecular.PencilBasis
