import Numlib.Optimization.LineSearch.Backtracking
import Mathlib.Tactic

/-!
# Sharpness of backtracking steepest descent

A difference of squared positive parts gives a nonnegative `C¹` function with a
linear descent plateau and a short quadratic terminal ramp. Its true gradient is
globally Lipschitz. For each accuracy `0 < ε < 1`, place the ramp midpoint at the
`ceil(ε⁻²)`-th equally spaced iterate. The initial Armijo candidate is accepted at
every step; gradient sizes are `2ε` before that point and `ε` at it. Both the
Lipschitz constant and initial objective budget are independent of the accuracy.

The counts include the initial objective evaluation and terminal gradient test.
-/

open Set Filter Topology
namespace BacktrackingGradient

/-- The square of the positive part, differentiable even at its junction. -/
noncomputable def squaredHinge (u : ℝ) : ℝ := (max 0 u) ^ 2

/-- The squared hinge has continuous derivative `2 max(0,u)`. -/
theorem hasDerivAt_squaredHinge (u : ℝ) :
    HasDerivAt squaredHinge (2 * max 0 u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have heq : squaredHinge =ᶠ[𝓝 u] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hu] with v hv
      simp [squaredHinge,max_eq_left hv.le]
    simpa [max_eq_left hu.le] using
      (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq heq
  · have hl : HasDerivWithinAt squaredHinge 0 (Iic 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
        (fun v hv => by simp [squaredHinge,max_eq_left (show v ≤ 0 from hv)])
        (by simp [squaredHinge])
    have hsq : HasDerivAt (fun v : ℝ => v ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1
      · rfl
      · norm_num
    have hr : HasDerivWithinAt squaredHinge 0 (Ici 0) 0 :=
      hsq.hasDerivWithinAt.congr
        (fun v hv => by simp [squaredHinge,max_eq_right (show 0 ≤ v from hv)])
        (by simp [squaredHinge])
    simpa [Iic_union_Ici] using hl.union hr
  · have heq : squaredHinge =ᶠ[𝓝 u] (fun v => v ^ 2) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      simp [squaredHinge,max_eq_right hv.le]
    simpa [max_eq_right hu.le] using
      ((hasDerivAt_id u).pow 2).congr_of_eventuallyEq heq

/-- A linear descent plateau with a quadratic terminal ramp of width `2rε`. -/
noncomputable def plateauObjective (r ε X x : ℝ) : ℝ :=
  (squaredHinge (X + r * ε - x) - squaredHinge (X - r * ε - x)) / (2 * r)

/-- The actual derivative of the plateau objective. -/
noncomputable def plateauGradient (r ε X x : ℝ) : ℝ :=
  (max 0 (X - r * ε - x) - max 0 (X + r * ε - x)) / r

/-- Derivative formula at every point, including both ramp junctions. -/
theorem hasDerivAt_plateauObjective (r ε X x : ℝ) :
    HasDerivAt (plateauObjective r ε X) (plateauGradient r ε X x) x := by
  have hp := (hasDerivAt_squaredHinge (X + r * ε - x)).comp x
    ((hasDerivAt_const x (X + r * ε)).sub (hasDerivAt_id x))
  have hm := (hasDerivAt_squaredHinge (X - r * ε - x)).comp x
    ((hasDerivAt_const x (X - r * ε)).sub (hasDerivAt_id x))
  have hd := (hp.sub hm).div_const (2 * r)
  convert hd using 1
  · rfl
  · dsimp [plateauGradient]
    simp only [div_eq_mul_inv,mul_inv_rev]
    norm_num
    ring

/-- The plateau objective is globally nonnegative. -/
theorem plateauObjective_nonneg {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (X x : ℝ) :
    0 ≤ plateauObjective r ε X x := by
  have hm : max 0 (X - r * ε - x) ≤ max 0 (X + r * ε - x) := by
    gcongr
    nlinarith [mul_nonneg hr.le hε]
  exact div_nonneg (sub_nonneg.mpr ((sq_le_sq₀ (le_max_left _ _) (le_max_left _ _)).2 hm))
    (by positivity)

/-- The plateau derivative is globally Lipschitz with an accuracy-independent constant. -/
theorem plateauGradient_lipschitz {r : ℝ} (hr : 0 < r) (ε X x y : ℝ) :
    ‖plateauGradient r ε X x - plateauGradient r ε X y‖ ≤ (2 / r) * ‖x - y‖ := by
  have hmax (a : ℝ) : |max 0 (a - x) - max 0 (a - y)| ≤ |x - y| := by
    simpa only [max_comm,show a - x - (a - y) = -(x - y) by ring,abs_neg]
      using abs_max_sub_max_le_abs (a - x) (a - y) 0
  have hsub := abs_sub_le
    (max 0 (X-r*ε-x)-max 0 (X-r*ε-y)) 0
    (max 0 (X+r*ε-x)-max 0 (X+r*ε-y))
  simp only [sub_zero,zero_sub,abs_neg] at hsub
  rw [Real.norm_eq_abs,Real.norm_eq_abs]
  dsimp [plateauGradient]
  rw [← sub_div,abs_div,abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have heq : max 0 (X-r*ε-x)-max 0 (X+r*ε-x) -
      (max 0 (X-r*ε-y)-max 0 (X+r*ε-y)) =
      (max 0 (X-r*ε-x)-max 0 (X-r*ε-y)) -
      (max 0 (X+r*ε-x)-max 0 (X+r*ε-y)) := by ring
  rw [heq]
  have ha := hmax (X-r*ε)
  have hb := hmax (X+r*ε)
  have hc : (2 / r) * |x - y| * r = 2 * |x - y| := by field_simp
  rw [hc]
  linarith

/-- The objective and derivative on the linear part of the plateau. -/
theorem plateau_linear {r ε X x : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hx : x ≤ X - r * ε) :
    plateauObjective r ε X x = 2 * ε * (X - x) ∧
      plateauGradient r ε X x = -2 * ε := by
  have hl : 0 ≤ X - r * ε - x := by linarith
  have hu : 0 ≤ X + r * ε - x := by nlinarith
  constructor <;> simp only [plateauObjective,plateauGradient,squaredHinge,
    max_eq_right hl,max_eq_right hu] <;> field_simp <;> ring

/-- The midpoint of the ramp has derivative exactly `−ε`. -/
theorem plateau_midpoint {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (X : ℝ) :
    plateauObjective r ε X X = r * ε ^ 2 / 2 ∧
      plateauGradient r ε X X = -ε := by
  have hl : X - r * ε - X ≤ 0 := by nlinarith
  have hu : 0 ≤ X + r * ε - X := by nlinarith
  constructor <;> simp only [plateauObjective,plateauGradient,squaredHinge,
    max_eq_left hl,max_eq_right hu,zero_pow (by norm_num : 2 ≠ 0),sub_zero,zero_sub] <;>
    field_simp <;> ring
/-- The actual Fréchet derivative in the inner-product representation used by SDBA. -/
theorem hasFDerivAt_plateauObjective (r ε X x : ℝ) :
    HasFDerivAt (plateauObjective r ε X) (innerSL ℝ (plateauGradient r ε X x)) x := by
  convert (hasDerivAt_plateauObjective r ε X x).hasFDerivAt using 1
  ext
  simp [innerSL_apply_apply,mul_comm]

/-- The plateau objective is continuously differentiable globally. -/
theorem contDiff_plateauObjective (r ε X : ℝ) : ContDiff ℝ 1 (plateauObjective r ε X) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_plateauObjective r ε X x).differentiableAt,?_⟩
  have heq : fderiv ℝ (plateauObjective r ε X) =
      fun x => innerSL ℝ (plateauGradient r ε X x) :=
    funext (fun x => (hasFDerivAt_plateauObjective r ε X x).fderiv)
  rw [heq]
  exact (innerSL ℝ).continuous.comp (by unfold plateauGradient; fun_prop)

/-- A uniform positive-spaced orbit remains on the plateau until its last point. -/
theorem plateau_orbit_linear {α t ε : ℝ} {N : ℕ}
    (hα : 0 ≤ α) (ht : 0 < t) (hε : 0 < ε) {i : ℕ} (hi : i < N) :
    2 * t * ε * (i : ℝ) ≤ 2 * t * ε * (N : ℝ) - (t * (1 - α)) * ε := by
  have hidx : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi
  have hmul := mul_le_mul_of_nonneg_left hidx (show 0 ≤ 2 * t * ε by positivity)
  have hαprod : 0 ≤ t * α * ε := by positivity
  nlinarith

/-- The explicit plateau objective forces every initial candidate to be accepted
for `N` iterations, with preterminal gradient `2ε` and terminal gradient `ε`. -/
theorem plateau_run {α t ε : ℝ} {N : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) (hε : 0 < ε) (hN : 0 < N) :
    let r := t * (1 - α)
    let X := 2 * t * ε * (N : ℝ)
    let x : ℕ → ℝ := fun i => 2 * t * ε * (i : ℝ)
    Run (plateauObjective r ε X) (plateauGradient r ε X) x (fun _ => 0) α t ε N ∧
      ‖plateauGradient r ε X (x N)‖ = ε ∧
      plateauObjective r ε X (x 0) = 4 * t * ε ^ 2 * N := by
  dsimp only
  let r := t * (1 - α)
  let X := 2 * t * ε * (N : ℝ)
  let x : ℕ → ℝ := fun i => 2 * t * ε * (i : ℝ)
  have hr : 0 < r := mul_pos ht (sub_pos.mpr hα1)
  have hlin (i : ℕ) (hi : i < N) :
      plateauObjective r ε X (x i) = 2 * ε * (X - x i) ∧
      plateauGradient r ε X (x i) = -2 * ε :=
    plateau_linear hr hε.le (plateau_orbit_linear hα0.le ht hε hi)
  have hmid : plateauObjective r ε X (x N) = r * ε ^ 2 / 2 ∧
      plateauGradient r ε X (x N) = -ε := plateau_midpoint hr hε.le X
  refine ⟨?_,?_,?_⟩
  · refine ⟨hasFDerivAt_plateauObjective r ε X,hα0,hα1,ht,hε,?_,?_,?_,?_⟩
    · intro i hi
      rw [(hlin i hi).2,Real.norm_eq_abs,abs_mul,abs_of_pos hε]
      norm_num
      linarith
    · intro i hi
      have hgi := (hlin i hi).2
      have hstep : x i - step t 0 • plateauGradient r ε X (x i) = x (i + 1) := by
        simp only [step_zero,hgi,smul_eq_mul,x,Nat.cast_add,Nat.cast_one]
        ring
      change plateauObjective r ε X (x i + step t 0 • (-plateauGradient r ε X (x i))) ≤
        plateauObjective r ε X (x i) + α * step t 0 *
          (innerSL ℝ (plateauGradient r ε X (x i))) (-plateauGradient r ε X (x i))
      simp only [smul_neg,← sub_eq_add_neg]
      rw [hstep,(hlin i hi).1,hgi,step_zero]
      simp only [neg_mul, map_neg, neg_neg, neg_apply, coe_innerSL_apply,
        inner_self_eq_norm_sq_to_K, norm_mul, Real.norm_ofNat, Real.norm_eq_abs,
        RCLike.ofReal_real_eq_id, id_eq, mul_neg, le_add_neg_iff_add_le, abs_of_pos hε]
      by_cases hnext : i + 1 < N
      · rw [(hlin (i + 1) hnext).1]
        dsimp [x]
        push_cast
        have hprod : 0 ≤ (1 - α) * t * ε ^ 2 := by positivity
        nlinarith
      · have hiN : i + 1 = N := by omega
        rw [hiN,hmid.1]
        have hidx : (i : ℝ) + 1 = N := by exact_mod_cast hiN
        dsimp [X,x,r]
        rw [← hidx]
        have hprod : 0 ≤ (1 - α) * t * ε ^ 2 := by positivity
        nlinarith
    · intro i hi m hm
      omega
    · intro i hi
      rw [(hlin i hi).2,step_zero]
      simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one]
      ring
  · rw [hmid.2,Real.norm_eq_abs,abs_neg,abs_of_pos hε]
  · rw [(hlin 0 hN).1]
    simp only [x,Nat.cast_zero,mul_zero,sub_zero,X]
    ring
/-- Gradient evaluations in a run of `N` accepted iterations: one at each
iterate, including the initial point and the terminal stopping test. -/
def Run.gradientEvaluations (N : ℕ) : ℕ := N + 1

/-- The gradient evaluation count includes the terminal stopping test. -/
@[simp]
theorem Run.gradientEvaluations_eq (N : ℕ) : Run.gradientEvaluations N = N + 1 := rfl

/-- For every accuracy below one there is a bounded-below, uniformly smooth objective
whose actual backtracking run needs at least `ε⁻²` steps. The initial budget and the
Lipschitz constant do not depend on the accuracy. -/
theorem exists_slow_run {α t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (f g : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ),
        ContDiff ℝ 1 f ∧ (∀ y, HasFDerivAt f (innerSL ℝ (g y)) y) ∧
        (∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) ∧
        (∀ y, 0 ≤ f y) ∧ f (x 0) ≤ 8 * t ∧ x 0 = 0 ∧
        N = ⌈1 / ε ^ 2⌉₊ ∧ Run f g x (fun _ => 0) α t ε N ∧
        ‖g (x N)‖ = ε ∧ (1 / ε ^ 2 : ℝ) ≤ N ∧
        Run.functionEvaluations (fun _ => 0) N = N + 1 ∧
        (1 / ε ^ 2 : ℝ) ≤ Run.functionEvaluations (fun _ => 0) N ∧
        (1 / ε ^ 2 : ℝ) ≤ Run.gradientEvaluations N := by
  let r := t * (1 - α)
  have hr : 0 < r := mul_pos ht (sub_pos.mpr hα1)
  have hL : 1 ≤ 1 + 2 / r := by
    have hh : 0 < 2 / r := by positivity
    linarith
  refine ⟨1 + 2 / r,hL,?_⟩
  intro ε hε hε1
  let N : ℕ := ⌈1 / ε ^ 2⌉₊
  let X : ℝ := 2 * t * ε * (N : ℝ)
  let x : ℕ → ℝ := fun i => 2 * t * ε * (i : ℝ)
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨hRun,hstop,hbudget⟩ := plateau_run hα0 hα1 ht hε hN
  have hprod : (N : ℝ) * ε ^ 2 ≤ 2 := by
    have hceil : (N : ℝ) < 1 / ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hm := mul_lt_mul_of_pos_right hceil (pow_pos hε 2)
    have heq : (1 / ε ^ 2 + 1) * ε ^ 2 = 1 + ε ^ 2 := by
      field_simp
    rw [heq] at hm
    nlinarith
  refine ⟨plateauObjective r ε X,plateauGradient r ε X,x,N,
    contDiff_plateauObjective r ε X,hasFDerivAt_plateauObjective r ε X,?_,
    plateauObjective_nonneg hr hε.le X,?_,by simp [x],rfl,hRun,hstop,Nat.le_ceil _,?_⟩
  · intro y z
    exact (plateauGradient_lipschitz hr ε X y z).trans
      (mul_le_mul_of_nonneg_right (by linarith : 2 / r ≤ 1 + 2 / r) (norm_nonneg _))
  · rw [hbudget]
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * t by positivity)
    nlinarith
  · have hF : Run.functionEvaluations (fun _ => 0) N = N + 1 := by
      simp [Run.functionEvaluations,Nat.add_comm]
    refine ⟨hF,?_,?_⟩
    · rw [hF]
      exact (Nat.le_ceil _).trans (by simp [N])
    · exact (Nat.le_ceil _).trans (by simp [Run.gradientEvaluations,N])
end BacktrackingGradient
