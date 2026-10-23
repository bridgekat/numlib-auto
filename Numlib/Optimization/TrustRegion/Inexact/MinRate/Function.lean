import Numlib.Approximation.Hermite.HalfLine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A fixed bounded objective with exponentially decaying negative curvature

Matching actual finite jets glues a bounded Hermite extension to a smooth exponential
tail. The resulting single objective is independent of every tolerance and execution
horizon.
-/

namespace OracleSimulation.MinRateCounterexample
open Real
/-- A fixed exponentially decaying trigonometric objective on the right half-line. -/
noncomputable def tail (x : ℝ) : ℝ := exp (-x) * (3 * π + sin (2 * π * x))
/-- The explicit first derivative of the exponential trigonometric tail. -/
noncomputable def first (x : ℝ) : ℝ :=
  exp (-x) * (-3 * π - sin (2 * π * x) + 2 * π * cos (2 * π * x))
/-- The explicit second derivative of the exponential trigonometric tail. -/
noncomputable def second (x : ℝ) : ℝ :=
  exp (-x) * (3 * π + (1 - 4 * π ^ 2) * sin (2 * π * x) - 4 * π * cos (2 * π * x))
/-- The explicit third derivative of the exponential trigonometric tail. -/
noncomputable def third (x : ℝ) : ℝ :=
  exp (-x) * (-3 * π + (12 * π ^ 2 - 1) * sin (2 * π * x) +
    (6 * π - 8 * π ^ 3) * cos (2 * π * x))

/-- The exponential trigonometric tail is smooth to every finite order. -/
theorem tail_smooth (n : ℕ) : ContDiff ℝ n tail := by unfold tail; fun_prop

/-- The explicit first derivative is the actual derivative of the tail. -/
theorem hasDerivAt_tail (x : ℝ) : HasDerivAt tail (first x) x := by
  have he := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hs := (Real.hasDerivAt_sin (2 * π * x)).comp x ((hasDerivAt_id x).const_mul (2 * π))
  unfold tail first
  convert he.mul (hs.const_add (3 * π)) using 1
  all_goals try funext y
  all_goals dsimp [Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  all_goals ring_nf

/-- The explicit second derivative is the actual derivative of the first. -/
theorem hasDerivAt_first (x : ℝ) : HasDerivAt first (second x) x := by
  have he := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hi := (hasDerivAt_id x).const_mul (2 * π)
  have hs := (Real.hasDerivAt_sin (2 * π * x)).comp x hi
  have hc := (Real.hasDerivAt_cos (2 * π * x)).comp x hi
  unfold first second
  convert he.mul (((hs.neg.const_add (-3 * π))).add (hc.const_mul (2 * π))) using 1
  all_goals try funext y
  all_goals dsimp [Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  all_goals ring_nf

/-- The explicit third derivative is the actual derivative of the second. -/
theorem hasDerivAt_second (x : ℝ) : HasDerivAt second (third x) x := by
  have he := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hi := (hasDerivAt_id x).const_mul (2 * π)
  have hs := (Real.hasDerivAt_sin (2 * π * x)).comp x hi
  have hc := (Real.hasDerivAt_cos (2 * π * x)).comp x hi
  unfold second third
  convert he.mul (((hs.const_mul (1 - 4 * π ^ 2)).const_add (3 * π)).sub
    (hc.const_mul (4 * π))) using 1
  all_goals try funext y
  all_goals dsimp [Function.comp_def, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  all_goals ring_nf

/-- All actual tail derivatives through order three have the displayed formulas. -/
theorem tail_derivatives {j : ℕ} (hj : j ≤ 3) (x : ℝ) :
    iteratedDeriv j tail x = if j = 0 then tail x else if j = 1 then first x
      else if j = 2 then second x else third x := by
  have h1 : deriv tail = first := funext fun z => (hasDerivAt_tail z).deriv
  have h2 : deriv first = second := funext fun z => (hasDerivAt_first z).deriv
  have h3 : deriv second = third := funext fun z => (hasDerivAt_second z).deriv
  interval_cases j <;> simp [iteratedDeriv_succ, h1, h2, h3]

/-- A real sine-cosine combination is bounded by the sum of its coefficient magnitudes. -/
theorem trig_combination (a b c x : ℝ) :
    |a + b * sin x + c * cos x| ≤ |a| + |b| + |c| := by
  calc _ ≤ |a| + |b * sin x| + |c * cos x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ |a| + |b| * 1 + |c| * 1 := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact Real.abs_sin_le_one x
      · exact Real.abs_cos_le_one x
    _ = _ := by ring

/-- Every actual tail derivative through order three is uniformly bounded on the closed
right half-line. -/
theorem tail_derivative_bound {j : ℕ} (hj : j ≤ 3) {x : ℝ} (hx : 3 ≤ x) :
    |iteratedDeriv j tail x| ≤ 10000 := by
  rw [tail_derivatives hj]
  have he : |exp (-x)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hπ0 := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hπ2 : π ^ 2 < 16 := by nlinarith
  have hπcub : π ^ 3 < 64 := by nlinarith
  have hcomb : ∀ a b c : ℝ, |a| + |b| + |c| ≤ 10000 →
      |exp (-x) * (a + b * sin (2 * π * x) + c * cos (2 * π * x))| ≤ 10000 := by
    intro a b c h
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) he).trans ((trig_combination _ _ _ _).trans h)
  interval_cases j <;> norm_num only [reduceIte, Nat.reduceEqDiff]
  · convert hcomb (3 * π) 1 0 (by rw [abs_of_pos (by positivity)]; norm_num; linarith) using 1
    simp [tail]
  · convert hcomb (-3 * π) (-1) (2 * π) (by
      rw [abs_of_neg (by linarith), abs_neg, abs_one, abs_of_pos (by positivity)]
      linarith) using 1
    dsimp [first]
    congr 1
    ring
  · convert hcomb (3 * π) (1 - 4 * π ^ 2) (-4 * π) (by
      rw [abs_of_pos (by positivity), abs_of_neg (by nlinarith), abs_of_neg (by linarith)]
      nlinarith) using 1
    dsimp [second]
    congr 1
    ring
  · convert hcomb (-3 * π) (12 * π ^ 2 - 1) (6 * π - 8 * π ^ 3) (by
      rw [abs_of_neg (by linarith), abs_of_pos (by nlinarith), abs_of_neg (by nlinarith)]
      nlinarith) using 1
    rfl

/-- The actual second derivative of the tail has a fixed Lipschitz constant on the closed
right half-line. -/
theorem tail_second_lipschitz : LipschitzOnWith 10000 (iteratedDeriv 2 tail) (Set.Ici 3) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (f := iteratedDeriv 2 tail) (s := Set.Ici 3)
    (fun z _ => (tail_smooth 3).differentiable_iteratedDeriv' 2 z)
    (fun z hz => ?_) (convex_Ici 3) hy hx
  rw [← iteratedDeriv_succ]
  change |iteratedDeriv (2 + 1) tail z| ≤ (10000 : ℝ)
  exact tail_derivative_bound (by omega : 3 ≤ 3) hz

private theorem objective_exists : ∃ f : ℝ → ℝ, ∃ L B : ℝ,
    1 ≤ L ∧ 0 < B ∧ ContDiff ℝ 2 f ∧ (∀ x, |f x| ≤ B) ∧
    (∀ j, j ≤ 2 → ∀ x y,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖) ∧
    (∀ j, j ≤ 2 → ∀ x, 3 ≤ x → iteratedDeriv j f x = iteratedDeriv j tail x) := by
  exact Hermite.exists_bounded_extension_tensor (tail_smooth 2) 3 10000 (by norm_num)
    (fun j hj x hx => tail_derivative_bound (by omega) hx) tail_second_lipschitz

/-- One fixed globally bounded smooth extension of the exponential trigonometric tail,
chosen independently of all tolerances and execution lengths. -/
noncomputable def objective : ℝ → ℝ := Classical.choose objective_exists

/-- The fixed objective has global boundedness and Lipschitz derivatives through order
two, and all actual tail jets are preserved. -/
theorem objective_spec : ∃ L B : ℝ,
    1 ≤ L ∧ 0 < B ∧ ContDiff ℝ 2 objective ∧ (∀ x, |objective x| ≤ B) ∧
    (∀ j, j ≤ 2 → ∀ x y,
      ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤
        L * ‖x - y‖) ∧
    (∀ j, j ≤ 2 → ∀ x, 3 ≤ x →
      iteratedDeriv j objective x = iteratedDeriv j tail x) :=
  Classical.choose_spec objective_exists

/-- The strictly increasing integer trial points beginning at three. -/
def node (k : ℕ) : ℝ := (k + 3 : ℕ)
/-- The common positive scale of the true first and second derivatives at each trial
point. -/
noncomputable def magnitude (k : ℕ) : ℝ := π * exp (-node k)

/-- The derivative magnitude at every trial point is strictly positive. -/
theorem magnitude_pos (k : ℕ) : 0 < magnitude k := by unfold magnitude; positivity

/-- The actual objective, gradient and Hessian at every integer trial point have their
exact exponential values. -/
theorem node_jets {j : ℕ} (hj : j ≤ 2) (k : ℕ) :
    iteratedDeriv j objective (node k) =
      if j = 0 then 3 * magnitude k else -magnitude k := by
  obtain ⟨L, B, hL, hB, hf, hb, hLip, heq⟩ := objective_spec
  rw [heq j hj (node k) (by dsimp [node]; exact_mod_cast (show 3 ≤ k + 3 by omega)),
    tail_derivatives (by omega)]
  have heqAngle : 2 * π * node k = (k + 3 : ℕ) * (2 * π) := by dsimp [node]; ring
  have hs : sin (2 * π * node k) = 0 := by
    rw [heqAngle]
    simpa only [zero_add, sin_zero] using Real.sin_add_nat_mul_two_pi 0 (k + 3)
  have hc : cos (2 * π * node k) = 1 := by
    rw [heqAngle]
    exact Real.cos_nat_mul_two_pi (k + 3)
  interval_cases j <;> norm_num only [Nat.reduceEqDiff, reduceIte] <;>
    dsimp [tail, first, second, magnitude] <;> rw [hs] <;> try rw [hc]
  all_goals ring

end OracleSimulation.MinRateCounterexample
