import Numlib.Optimization.FlatJetChain
import Numlib.Optimization.FiniteChain
import Numlib.Analysis.Calculus.EuclideanOne
import Numlib.Optimization.TrustRegion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Sharp finite trust-region traces

A constant nonzero gradient chain with objective decrement equal to the squared step norm
is a lawful trust-region run for identity model operators. The construction retains the
actual quadratic model, its Cauchy comparison, and the objective-based acceptance ratio.
After the stationary endpoint the trace is held fixed and the radius contracts lawfully.
-/

noncomputable section
namespace Optimization.TrustRegion
open QuadraticSubproblem
open scoped InnerProductSpace NNReal

/-- Fixed admissible parameters used for the sharp trust-region trace. -/
def sharpParameters : Parameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 1 / 2
  gamma3 := 2
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma_le := le_rfl
  gamma2_lt_one := by norm_num
  one_lt_gamma3 := by norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unit radii along the active chain, followed by admissible contractions. -/
def sharpRadius (N k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k - N)

/-- For an identity model the full negative gradient step globally minimizes the quadratic. -/
theorem quadratic_neg_identity_le (g : E) (t : ℝ) :
    quadratic g (ContinuousLinearMap.id ℝ E) (-g) ≤
      quadratic g (ContinuousLinearMap.id ℝ E) (-(t • g)) := by
  rw [show -g = -((1 : ℝ) • g) by simp, quadratic_neg_smul, quadratic_neg_smul]
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg (t - 1), sq_nonneg ‖g‖,
    mul_nonneg (sq_nonneg (t - 1)) (sq_nonneg ‖g‖)]

/-- Along an interpolated constant-gradient chain, every active acceptance ratio equals two. -/
theorem sharp_ratio_active {N k : ℕ} {v : E} {f : E → ℝ} {g : E → E}
    (hv : v ≠ 0) (hk : k < N)
    (hf : ∀ i ≤ N, f ((i : ℝ) • v) = -(i : ℝ) * ‖v‖ ^ 2)
    (hg : ∀ i < N, g ((i : ℝ) • v) = -v) :
    ratio f (g (FiniteChain.point N v k)) (ContinuousLinearMap.id ℝ E)
      (FiniteChain.point N v k) (FiniteChain.step N v k) = 2 := by
  have hx := FiniteChain.point_add_step N v k
  have hkn : k ≤ N := Nat.le_of_lt hk
  have hsucc : k + 1 ≤ N := hk
  unfold ratio
  rw [← hx, FiniteChain.point_of_le v hkn, FiniteChain.point_of_le v hsucc]
  rw [hg k hk, hf k hkn, hf (k + 1) hsucc]
  simp only [FiniteChain.step, hk, ↓reduceIte, quadratic,
    ContinuousLinearMap.id_apply, inner_neg_left, real_inner_self_eq_norm_sq, inner_zero_right,
    Nat.cast_add, Nat.cast_one]
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  field_simp
  ring

/-- Arbitrary fixed active radii, followed by the same stationary contractions. -/
def sharpRadiusWith (R : ℝ) (N k : ℕ) : ℝ := R * sharpRadius N k

/-- A finite chain gives a lawful run for any positive initial radius containing its steps. -/
theorem isRun_sharpChain_with_radius {R : ℝ} {N : ℕ} {v : E} {f : E → ℝ} {g : E → E}
    (hR : 0 < R) (hv : v ≠ 0) (hvn : ‖v‖ ≤ R)
    (hf : ∀ i ≤ N, f ((i : ℝ) • v) = -(i : ℝ) * ‖v‖ ^ 2)
    (hg : ∀ i ≤ N, g ((i : ℝ) • v) = if i < N then -v else 0) :
    IsRun sharpParameters f g (fun _ => ContinuousLinearMap.id ℝ E)
      (FiniteChain.point N v) (FiniteChain.step N v) (sharpRadiusWith R N) := by
  have hgactive : ∀ i < N, g ((i : ℝ) • v) = -v := by
    intro i hi
    simpa [hi] using hg i (Nat.le_of_lt hi)
  have hgterminal : g ((N : ℝ) • v) = 0 := by simpa using hg N le_rfl
  have hractive (k : ℕ) (hk : k < N) := sharp_ratio_active hv hk hf hgactive
  have hrterminal (k : ℕ) (hk : N ≤ k) :
      ratio f (g (FiniteChain.point N v k)) (ContinuousLinearMap.id ℝ E)
        (FiniteChain.point N v k) (FiniteChain.step N v k) = 0 := by
    simp [FiniteChain.point_of_ge v hk, FiniteChain.step, Nat.not_lt.mpr hk, hgterminal, ratio]
  constructor
  · simpa [sharpRadiusWith, sharpRadius] using hR
  · intro k
    by_cases hk : k < N
    · simpa [FiniteChain.step, hk, sharpRadiusWith, sharpRadius,
        Nat.sub_eq_zero_of_le (Nat.le_of_lt hk)] using hvn
    · simp only [FiniteChain.step, hk, ↓reduceIte, norm_zero, sharpRadiusWith, sharpRadius]
      exact mul_nonneg hR.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
  · intro k t ht htf
    by_cases hk : k < N
    · rw [FiniteChain.point_of_le v (Nat.le_of_lt hk), hgactive k hk]
      simpa [FiniteChain.step, hk] using quadratic_neg_identity_le (-v) t
    · simp [FiniteChain.point_of_ge v (Nat.le_of_not_gt hk), hgterminal, FiniteChain.step, hk,
        quadratic]
  · intro k
    by_cases hk : k < N
    · rw [hractive k hk]
      norm_num [sharpParameters]
      exact FiniteChain.point_add_step N v k
    · rw [hrterminal k (Nat.le_of_not_gt hk)]
      norm_num [sharpParameters]
      simp [FiniteChain.point_of_ge v (Nat.le_of_not_gt hk),
        FiniteChain.point_of_ge v ((Nat.le_of_not_gt hk).trans (Nat.le_succ k))]
  · intro k
    by_cases hk : k < N
    · rw [hractive k hk]
      norm_num [sharpParameters, sharpRadiusWith, sharpRadius,
        Nat.sub_eq_zero_of_le (Nat.le_of_lt hk), Nat.sub_eq_zero_of_le hk]
      linarith
    · rw [hrterminal k (Nat.le_of_not_gt hk)]
      norm_num [sharpParameters]
      have hsub : k + 1 - N = k - N + 1 := by omega
      simp [sharpRadiusWith, sharpRadius, hsub, pow_succ, mul_comm, mul_left_comm]

/-- A finite chain with its actual gradient and objective data yields a complete lawful run. -/
theorem isRun_sharpChain {N : ℕ} {v : E} {f : E → ℝ} {g : E → E}
    (hv : v ≠ 0) (hvn : ‖v‖ ≤ 1)
    (hf : ∀ i ≤ N, f ((i : ℝ) • v) = -(i : ℝ) * ‖v‖ ^ 2)
    (hg : ∀ i ≤ N, g ((i : ℝ) • v) = if i < N then -v else 0) :
    IsRun sharpParameters f g (fun _ => ContinuousLinearMap.id ℝ E)
      (FiniteChain.point N v) (FiniteChain.step N v) (sharpRadius N) := by
  have heq : sharpRadiusWith 1 N = sharpRadius N := by
    funext k
    simp [sharpRadiusWith]
  simpa only [heq] using isRun_sharpChain_with_radius zero_lt_one hv hvn hf hg

/-- Ceilings of inverse squared tolerances give a chain of the required length while
keeping the total objective drop uniformly bounded. -/
theorem sharp_chain_length {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    0 < ⌈1 / ε ^ 2⌉₊ ∧ 1 / ε ^ 2 ≤ (⌈1 / ε ^ 2⌉₊ : ℝ) ∧
      (⌈1 / ε ^ 2⌉₊ : ℝ) * (2 * ε) * (2 * ε) ≤ 8 := by
  have hpow : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlower := Nat.le_ceil (1 / ε ^ 2)
  have hupper := Nat.ceil_lt_add_one (show 0 ≤ 1 / ε ^ 2 by positivity)
  have hN : 0 < ⌈1 / ε ^ 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
  refine ⟨hN, hlower, ?_⟩
  have hmul := (mul_lt_mul_of_pos_right hupper hpow).le
  have hid : (1 / ε ^ 2 + 1) * ε ^ 2 = 1 + ε ^ 2 := by field_simp
  rw [hid] at hmul
  nlinarith [sq_nonneg (ε - 1)]

/-- A uniform bounded family of genuinely smooth Euclidean objectives attains the inverse
squared evaluation lower bound for the lawful trust-region method. All smoothness and
objective bounds are chosen before the requested tolerance. The first terminal iterate and
the number of successful iterations both equal the prescribed chain length. -/
theorem exists_sharp_firstOrder_family :
    ∃ L B : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (N : ℕ)
        (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (delta : ℕ → ℝ),
        ContDiff ℝ 1 f ∧ LipschitzWith L (gradient f) ∧
        (∀ y, |f y| ≤ B) ∧ f (x 0) = 0 ∧ x 0 = 0 ∧ delta 0 = 2 ∧
        IsRun sharpParameters f (gradient f) (fun _ => ContinuousLinearMap.id ℝ _)
          x s delta ∧
        (∀ k < N, ε < ‖gradient f (x k)‖) ∧ ‖gradient f (x N)‖ ≤ ε ∧
        (ParameterUpdates.successCount (fun k => sharpParameters.eta1 ≤
          ratio f (gradient f (x k)) (ContinuousLinearMap.id ℝ _) (x k) (s k)) N = N) ∧
        1 / ε ^ 2 ≤ (N : ℝ) := by
  obtain ⟨L, B, hfamily⟩ := LowerBound.exists_flatJet_chain 1 le_rfl 8 (by norm_num)
  refine ⟨L, B, ?_⟩
  intro ε hε hεone
  let N : ℕ := ⌈1 / ε ^ 2⌉₊
  obtain ⟨hN, hNlower, hdrop⟩ := sharp_chain_length hε hεone
  obtain ⟨φ, hφ, hLip, hjet, hbound⟩ := hfamily N hN (2 * ε) (2 * ε)
    (by positivity) (by positivity) (by simp; linarith) hdrop (by linarith) (by linarith)
  let v := EuclideanOne.coord.symm (2 * ε)
  let f := EuclideanOne.lift φ
  have hvnorm : ‖v‖ = 2 * ε := by
    change ‖EuclideanOne.coord.symm (2 * ε)‖ = _
    rw [EuclideanOne.coord.symm.norm_map, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hv : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvnorm]; positivity)
  have hdφ : Differentiable ℝ φ := hφ.differentiable_one
  have hvalues (k : ℕ) (hk : k ≤ N) :
      f ((k : ℝ) • v) = -(k : ℝ) * ‖v‖ ^ 2 := by
    have hh := hjet k hk 0 (by omega)
    simpa [f, v, EuclideanOne.lift, Function.comp_def, hvnorm, LowerBound.flatJet,
      pow_two, mul_assoc] using hh
  have hgrads (k : ℕ) (hk : k ≤ N) :
      gradient f ((k : ℝ) • v) = if k < N then -v else 0 := by
    rw [EuclideanOne.gradient_eq_deriv hdφ]
    have hh := hjet k hk 1 le_rfl
    simp only [iteratedDeriv_one, LowerBound.flatJet, Nat.one_ne_zero, ↓reduceIte] at hh
    simp only [map_smul, smul_eq_mul]
    change EuclideanOne.coord.symm (deriv φ ((k : ℝ) * (2 * ε))) = _
    rw [hh]
    split_ifs <;> simp [v]
  have hrun := isRun_sharpChain_with_radius (by norm_num : (0 : ℝ) < 2)
    hv (by rw [hvnorm]; linarith) hvalues hgrads
  have hcount : ParameterUpdates.successCount
      (fun k => sharpParameters.eta1 ≤ ratio f (gradient f (FiniteChain.point N v k))
        (ContinuousLinearMap.id ℝ _) (FiniteChain.point N v k) (FiniteChain.step N v k)) N = N := by
    classical
    unfold ParameterUpdates.successCount
    have he : (Finset.range N).filter (fun k => sharpParameters.eta1 ≤
        ratio f (gradient f (FiniteChain.point N v k)) (ContinuousLinearMap.id ℝ _)
          (FiniteChain.point N v k) (FiniteChain.step N v k)) = Finset.range N := by
      apply Finset.filter_eq_self.mpr
      intro k hk
      rw [sharp_ratio_active hv (Finset.mem_range.mp hk) hvalues]
      · norm_num [sharpParameters]
      · intro i hi
        simpa [hi] using hgrads i hi.le
    rw [he, Finset.card_range]
  refine ⟨f, N, FiniteChain.point N v, FiniteChain.step N v, sharpRadiusWith 2 N,
    EuclideanOne.contDiff hφ, ?_, ?_, ?_, ?_, ?_, hrun, ?_, ?_, hcount, hNlower⟩
  · exact EuclideanOne.gradient_lipschitz hdφ (by simpa using hLip)
  · intro y
    simpa [f, EuclideanOne.lift, Function.comp_def] using hbound 0 (by omega)
      (EuclideanOne.coord y)
  · simpa [FiniteChain.point] using hvalues 0 (Nat.zero_le N)
  · simp [FiniteChain.point]
  · simp [sharpRadiusWith, sharpRadius]
  · intro k hk
    rw [FiniteChain.point_of_le v hk.le, hgrads k hk.le]
    simp only [hk, ↓reduceIte, norm_neg, hvnorm]
    linarith
  · rw [FiniteChain.point_of_le v le_rfl, hgrads N le_rfl]
    simpa using hε.le

end Optimization.TrustRegion
