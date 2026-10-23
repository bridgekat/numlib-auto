import Numlib.Optimization.SecondOrder.SharpnessData
import Mathlib.Order.Interval.Set.Monotone

/-!
# Actual deterministic second-order adversarial histories

The prescribed value and derivative jets are exposed to a genuine method only
through its finite oracle history. At each query, an actual globally regular
objective realizes the preceding history. Primitive admissibility therefore
forces the next point and its positive, uniformly scaled displacement.
-/

namespace ShiftedNewton.Sharpness

/-- The method itself recursively chooses every new point of the prescribed jet history. -/
noncomputable def history (M : ScalarMethod) (t : ℝ) : ℕ → ScalarEvaluation
  | 0 => ⟨0, value t 0, first t 0, second t 0⟩
  | k + 1 => ⟨M.next k (fun i => history M t i.val), value t (k + 1),
      first t (k + 1), second t (k + 1)⟩
termination_by k => k

/-- The initial prescribed query is exactly the method's initialized origin. -/
@[simp] theorem history_point_zero (M : ScalarMethod) (t : ℝ) :
    (history M t 0).point = 0 := by rw [history]

/-- The new prescribed query is the method's genuine response to its prior oracle history. -/
theorem history_point_succ (M : ScalarMethod) (t : ℝ) (k : ℕ) :
    (history M t (k + 1)).point = M.next k (fun i => history M t i.val) := by rw [history]

/-- The actual oracle value prescribed at every history node. -/
@[simp] theorem history_value (M : ScalarMethod) (t : ℝ) (k : ℕ) :
    (history M t k).value = value t k := by cases k <;> rw [history]

/-- The actual first derivative prescribed at every history node. -/
@[simp] theorem history_first (M : ScalarMethod) (t : ℝ) (k : ℕ) :
    (history M t k).first = first t k := by cases k <;> rw [history]

/-- The actual second derivative prescribed at every history node. -/
@[simp] theorem history_second (M : ScalarMethod) (t : ℝ) (k : ℕ) :
    (history M t k).second = second t k := by cases k <;> rw [history]

/-- Any increasing realized prefix forces the next method-generated step to
satisfy the source's uniform positive displacement bounds. -/
theorem next_history_step_bounds {M : ScalarMethod} {t κrg κrs κlambda : ℝ}
    (ht : 0 < t) (hM : IsScalarMethodClass M (t ^ 2) κrg κrs κlambda)
    {k : ℕ} (hk : k < horizon t)
    (hinc : ∀ i j, i < j → j ≤ k →
      (history M t i).point < (history M t j).point) :
    let s := (history M t (k + 1)).point - (history M t k).point
    0 < s ∧ (1 - κrg) / (2 * κlambda) * t ≤ s ∧ s ≤ (1 + κrg) * t := by
  obtain ⟨f, hf, hm⟩ := exists_objective_matches_scalar_history (history M t) k
    (history_point_zero M t) hinc
  have hx := M.iterates_eq_of_matches (history_point_zero M t)
    (fun i _ => history_point_succ M t i) hm
  have hxnext := M.next_eq_of_matches (history_point_zero M t)
    (fun i _ => history_point_succ M t i) hm
  have hg : deriv f (M.iterates f k) = first t k := by
    rw [hx k le_rfl]
    exact (hm k le_rfl).2.1.trans (history_first M t k)
  obtain ⟨lambda, r, hlambda, hpsd, heq, hres, hspectral⟩ := hM.step f hf k (by
    rw [hg];exact accuracy_lt_first ht hk)
  have hg' : deriv f (history M t k).point = first t k :=
    (hm k le_rfl).2.1.trans (history_first M t k)
  have hH' : iteratedDeriv 2 f (history M t k).point = second t k :=
    (hm k le_rfl).2.2.trans (history_second M t k)
  simp only [hx k le_rfl, hxnext] at heq hres hspectral
  simp only [hg', hH'] at heq hres hspectral
  have hv := half_lt_value ht hk
  have hv1 : value t k ≤ 1 := by
    dsimp only [value]
    have hn : 0 ≤ (k : ℝ) * t ^ 3 := by positivity
    linarith
  have habs : |first t k| = 2 * t ^ 2 * value t k := by
    have hp : 0 ≤ 2 * t ^ 2 * value t k := by positivity
    rw [first, abs_of_nonpos (by nlinarith)]
    ring
  have hr : |r| ≤ κrg * (2 * t ^ 2 * value t k) := by
    simpa only [habs] using hres.trans (min_le_left _ _)
  have hspectral' : 4 * t * (value t k) ^ 2 + lambda ≤ κlambda * (4 * t * (value t k) ^ 2) := by
    change 4 * t * (value t k) ^ 2 + lambda ≤
      κlambda * max |4 * t * (value t k) ^ 2| (Real.sqrt |-2 * t ^ 2 * value t k|) at hspectral
    rwa [spectral_max ht hv.le] at hspectral
  apply shifted_step_bounds ht hv.le hv1 hM.residual_fraction_lt_one hM.spectral_gt_one
    hlambda (r := r) (s := (history M t (k + 1)).point - (history M t k).point) _ hr hspectral'
  dsimp only [first, second] at heq
  nlinarith [heq]

/-- All preterminal prescribed points are chosen by the actual method and
have the uniform positive source step lengths, derived by finite interpolation. -/
theorem history_step_bounds {M : ScalarMethod} {t κrg κrs κlambda : ℝ}
    (ht : 0 < t) (hM : IsScalarMethodClass M (t ^ 2) κrg κrs κlambda) :
    ∀ k < horizon t,
      let s := (history M t (k + 1)).point - (history M t k).point
      0 < s ∧ (1 - κrg) / (2 * κlambda) * t ≤ s ∧ s ≤ (1 + κrg) * t := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    apply next_history_step_bounds ht hM hk
    have hmono := strictMonoOn_Iic_of_lt_succ (n := k)
      (ψ := fun i => (history M t i).point) (fun m hm =>
        sub_pos.mp (ih m hm (hm.trans hk)).1)
    intro i j hij hj
    exact hmono (show i ∈ Set.Iic k from (le_of_lt hij).trans hj) hj hij

end ShiftedNewton.Sharpness
