import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# A bounded objective with independently small gradient and negative cubic jet

A combination of the first two sine harmonics has zero value and Hessian at the origin,
an arbitrarily small positive gradient, and a fixed negative third derivative. All its
first four derivatives are uniformly bounded, so the first three jets are globally Lipschitz.
-/

noncomputable section
open scoped ContDiff
namespace TwoSine

/-- The coefficient of the second sine harmonic. -/
def secondAmplitude (b : ℝ) : ℝ := 1 / 48 - b / 6

/-- The coefficient of the first sine harmonic. -/
def firstAmplitude (b : ℝ) : ℝ := 4 * b / 3 - 1 / 24

/-- A bounded smooth objective with gradient `b` and cubic derivative `-1/8` at zero. -/
def objective (b x : ℝ) : ℝ :=
  secondAmplitude b * Real.sin (2 * x) + firstAmplitude b * Real.sin x

/-- Both harmonics, and therefore their sum, are smooth at every order. -/
theorem contDiff (b : ℝ) (n : ℕ∞ω) : ContDiff ℝ n (objective b) := by
  unfold objective
  fun_prop

/-- All scalar iterated derivatives are the corresponding weighted harmonic derivatives. -/
theorem iteratedDeriv_objective (b x : ℝ) (i : ℕ) :
    iteratedDeriv i (objective b) x =
      secondAmplitude b * (2 ^ i * iteratedDeriv i Real.sin (2 * x)) +
        firstAmplitude b * iteratedDeriv i Real.sin x := by
  unfold objective
  rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (by fun_prop)]

/-- The small nonnegative gradient range keeps the two amplitudes uniformly bounded. -/
theorem amplitudes_bound {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 64) :
    |secondAmplitude b| ≤ 1 / 48 ∧ |firstAmplitude b| ≤ 1 / 24 := by
  constructor <;> apply abs_le.mpr <;> constructor <;>
    dsimp [secondAmplitude, firstAmplitude] <;> linarith

/-- The objective is uniformly bounded, and in particular bounded below. -/
theorem abs_objective_le {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 64) (x : ℝ) :
    |objective b x| ≤ 1 / 16 := by
  have ha := amplitudes_bound hb hb'
  calc
    |objective b x| ≤ |secondAmplitude b| * |Real.sin (2 * x)| +
        |firstAmplitude b| * |Real.sin x| := by
      simpa only [objective, abs_mul] using abs_add_le
        (secondAmplitude b * Real.sin (2 * x)) (firstAmplitude b * Real.sin x)
    _ ≤ 1 / 48 * 1 + 1 / 24 * 1 :=
      add_le_add (mul_le_mul ha.1 (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num))
        (mul_le_mul ha.2 (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num))
    _ = 1 / 16 := by norm_num

/-- The first four derivatives obey the common global norm bound one. -/
theorem norm_iteratedFDeriv_le_one {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 64)
    {i : ℕ} (hi : i ≤ 4) (x : ℝ) : ‖iteratedFDeriv ℝ i (objective b) x‖ ≤ 1 := by
  have ha := amplitudes_bound hb hb'
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    iteratedDeriv_objective]
  have hp : (2 : ℝ) ^ i ≤ 16 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi).trans_eq (by norm_num)
  calc
    |secondAmplitude b * (2 ^ i * iteratedDeriv i Real.sin (2 * x)) +
        firstAmplitude b * iteratedDeriv i Real.sin x| ≤
      |secondAmplitude b| * (2 ^ i * |iteratedDeriv i Real.sin (2 * x)|) +
        |firstAmplitude b| * |iteratedDeriv i Real.sin x| := by
      simpa [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i)]
        using abs_add_le (secondAmplitude b * (2 ^ i * iteratedDeriv i Real.sin (2 * x)))
          (firstAmplitude b * iteratedDeriv i Real.sin x)
    _ ≤ 1 / 48 * (16 * 1) + 1 / 24 * 1 := by
      exact add_le_add (mul_le_mul ha.1
        (mul_le_mul hp (Real.abs_iteratedDeriv_sin_le_one _ _) (abs_nonneg _)
          (by norm_num)) (mul_nonneg (by positivity) (abs_nonneg _)) (by norm_num))
        (mul_le_mul ha.2 (Real.abs_iteratedDeriv_sin_le_one _ _) (abs_nonneg _)
          (by norm_num))
    _ ≤ 1 := by norm_num

/-- The first three derivative tensors are globally Lipschitz with constant one. -/
theorem iteratedFDeriv_sub_le {b : ℝ} (hb : 0 ≤ b) (hb' : b ≤ 1 / 64)
    {i : ℕ} (hi : i ≤ 3) (x y : ℝ) :
    ‖iteratedFDeriv ℝ i (objective b) x - iteratedFDeriv ℝ i (objective b) y‖ ≤
      1 * ‖x - y‖ := by
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun z _ => (contDiff b (i + 1)).differentiable_iteratedFDeriv (by norm_cast; omega) z)
    (fun z _ => ?_) (Set.mem_univ y) (Set.mem_univ x)
  rw [norm_fderiv_iteratedFDeriv]
  exact norm_iteratedFDeriv_le_one hb hb' (by omega) z

/-- The exact value and the first three scalar derivatives at the origin. -/
theorem jets_zero (b : ℝ) :
    objective b 0 = 0 ∧ iteratedDeriv 1 (objective b) 0 = b ∧
      iteratedDeriv 2 (objective b) 0 = 0 ∧
      iteratedDeriv 3 (objective b) 0 = -1 / 8 := by
  norm_num [objective, iteratedDeriv_objective, secondAmplitude, firstAmplitude,
    show (2 : ℕ) = 1 + 1 by rfl, show (3 : ℕ) = 2 + 1 by rfl]
  constructor <;> ring

end TwoSine
