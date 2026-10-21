import Numlib.Analysis.Calculus.IteratedFDeriv
import Numlib.Analysis.Calculus.CurveTaylor
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Tactic.IntervalCases

/-!
# A quartic obstruction to straight-line descent

The Peano quartic has a strict minimum along each straight line through the origin and
negative values on a parabolic curve. Its actual mixed derivatives exhibit the fourth-order
curve obstruction.
-/

noncomputable section
open scoped ContDiff
namespace Optimization.LineSearchObstruction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Peano quartic in two continuous linear coordinates. -/
def quartic (a b : E →L[ℝ] ℝ) (x : E) : ℝ :=
  (b x)^2 - 3 * (a x)^2 * b x + 2 * (a x)^4

/-- The quartic is smooth of all orders. -/
theorem contDiff_quartic (a b : E →L[ℝ] ℝ) : ContDiff ℝ ∞ (quartic a b) := by
  unfold quartic
  fun_prop

/-- The actual first derivative in a specified direction. -/
theorem fderiv_quartic_apply (a b : E →L[ℝ] ℝ) (x u : E) :
    fderiv ℝ (quartic a b) x u =
      2 * b x * b u - 6 * a x * a u * b x - 3 * (a x)^2 * b u +
        8 * (a x)^3 * a u := by
  unfold quartic
  simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, fderiv_fun_const, smul_eq_mul]
  ring

/-- The actual Hessian in arbitrary directions. -/
theorem iteratedFDeriv_two_quartic_apply (a b : E →L[ℝ] ℝ) (x : E) (v : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (quartic a b) x v =
      2 * b (v 0) * b (v 1) - 6 * a (v 0) * a (v 1) * b x -
        6 * a (v 0) * a x * b (v 1) - 6 * a (v 1) * a x * b (v 0) +
        24 * (a x)^2 * a (v 0) * a (v 1) := by
  rw [iteratedFDeriv_succ_apply_left_of_differentiableAt (n := 1)
      (((contDiff_quartic a b).iteratedFDeriv_right (m := 1) (i := 1)
        (by simp)).differentiable one_ne_zero x)]
  simp_rw [iteratedFDeriv_one_apply, fderiv_quartic_apply]
  simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, fderiv_fun_const, smul_eq_mul, Fin.tail]
  ring

/-- The actual third derivative in arbitrary directions. -/
theorem iteratedFDeriv_three_quartic_apply (a b : E →L[ℝ] ℝ) (x : E) (v : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (quartic a b) x v =
      -6 * (a (v 0) * a (v 1) * b (v 2) + a (v 0) * a (v 2) * b (v 1) +
        a (v 1) * a (v 2) * b (v 0)) +
        48 * a x * a (v 0) * a (v 1) * a (v 2) := by
  rw [iteratedFDeriv_succ_apply_left_of_differentiableAt (n := 2)
      (((contDiff_quartic a b).iteratedFDeriv_right (m := 1) (i := 2)
        (by simp)).differentiable one_ne_zero x)]
  simp_rw [iteratedFDeriv_two_quartic_apply]
  simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, fderiv_fun_const, smul_eq_mul, Fin.tail]
  ring

/-- The actual fourth derivative in arbitrary directions. -/
theorem iteratedFDeriv_four_quartic_apply (a b : E →L[ℝ] ℝ) (x : E) (v : Fin 4 → E) :
    iteratedFDeriv ℝ 4 (quartic a b) x v =
      48 * a (v 0) * a (v 1) * a (v 2) * a (v 3) := by
  rw [iteratedFDeriv_succ_apply_left_of_differentiableAt (n := 3)
      (((contDiff_quartic a b).iteratedFDeriv_right (m := 1) (i := 3)
        (by simp)).differentiable one_ne_zero x)]
  simp_rw [iteratedFDeriv_three_quartic_apply]
  simp (disch := fun_prop) [fderiv_fun_mul,
    fderiv_fun_const, smul_eq_mul, Fin.tail]
  ring

/-- The quartic restricted to a line factors into a square and a scalar quadratic. -/
theorem quartic_smul (a b : E →L[ℝ] ℝ) (d : E) (t : ℝ) :
    quartic a b (t • d) = t^2 * ((b d)^2 - 3*t*(a d)^2*b d + 2*t^2*(a d)^4) := by
  simp only [quartic, map_smul, smul_eq_mul]
  ring

/-- Every line whose coordinates are not both zero has a strict minimum at the origin. -/
theorem quartic_strict_line (a b : E →L[ℝ] ℝ) {d : E} (hd : a d ≠ 0 ∨ b d ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, t ≠ 0 → |t| < r → 0 < quartic a b (t • d) := by
  by_cases hb : b d = 0
  · have ha : a d ≠ 0 := hd.resolve_right (not_not_intro hb)
    refine ⟨1, by norm_num, fun t ht _ => ?_⟩
    simp only [quartic, map_smul, smul_eq_mul, hb, mul_zero, zero_pow (by decide : 2 ≠ 0),
      sub_self, zero_add]
    positivity
  · have hp : 0 < (b d)^2 := sq_pos_of_ne_zero hb
    have hc : Continuous (fun t : ℝ => (b d)^2 - 3*t*(a d)^2*b d + 2*t^2*(a d)^4) := by
      fun_prop
    have he : ∀ᶠ t : ℝ in nhds 0,
        0 < (b d)^2 - 3*t*(a d)^2*b d + 2*t^2*(a d)^4 :=
      hc.continuousAt.eventually (lt_mem_nhds (by simpa using hp))
    obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r, hr, fun t ht htr => ?_⟩
    rw [quartic_smul]
    exact mul_pos (sq_pos_of_ne_zero ht) (he (by simpa [Real.dist_eq] using htr))

/-- A curve jet exhibiting the mixed fourth-order obstruction. -/
def badJet (e₁ e₂ : E) (i : ℕ) : E := if i = 2 then (3 / 2 : ℝ) • e₂ else e₁

/-- The first three actual coefficients vanish along this jet, and the fourth is negative. -/
theorem quartic_badJet_coefficients (a b : E →L[ℝ] ℝ) (e₁ e₂ : E)
    (ha1 : a e₁ = 1) (hb1 : b e₁ = 0) (ha2 : a e₂ = 0) (hb2 : b e₂ = 1) :
    (∀ j, 1 ≤ j → j < 4 → CurveTaylor.coefficient (quartic a b) 0 j (badJet e₁ e₂) = 0) ∧
      CurveTaylor.coefficient (quartic a b) 0 4 (badJet e₁ e₂) = -(1 / 4 : ℝ) := by
  constructor
  · intro j hj hj4
    interval_cases j <;>
      norm_num [CurveTaylor.coefficient_one, CurveTaylor.coefficient_two,
        CurveTaylor.coefficient_three, fderiv_quartic_apply,
        iteratedFDeriv_two_quartic_apply, iteratedFDeriv_three_quartic_apply,
        badJet, ha1, hb1, ha2, hb2, map_smul, smul_eq_mul]
  · norm_num [CurveTaylor.coefficient_four, fderiv_quartic_apply,
      iteratedFDeriv_two_quartic_apply, iteratedFDeriv_three_quartic_apply,
      iteratedFDeriv_four_quartic_apply, badJet, ha1, hb1, ha2, hb2, map_smul, smul_eq_mul]

/-- Straight-line minima do not suffice for the fourth-order curve conditions. -/
theorem quartic_not_isOrderMinimizer (a b : E →L[ℝ] ℝ) (e₁ e₂ : E)
    (ha1 : a e₁ = 1) (hb1 : b e₁ = 0) (ha2 : a e₂ = 0) (hb2 : b e₂ = 1) :
    ¬CurveTaylor.IsOrderMinimizer (quartic a b) 0 4 := by
  intro h
  obtain ⟨hlow, hfour⟩ := quartic_badJet_coefficients a b e₁ e₂ ha1 hb1 ha2 hb2
  have hh := h 4 (by decide) le_rfl (badJet e₁ e₂) hlow
  rw [hfour] at hh
  norm_num at hh

/-- The actual parabolic curve decreases from the origin on both sides. -/
theorem quartic_parabola (a b : E →L[ℝ] ℝ) (e₁ e₂ : E)
    (ha1 : a e₁ = 1) (hb1 : b e₁ = 0) (ha2 : a e₂ = 0) (hb2 : b e₂ = 1) (t : ℝ) :
    quartic a b (t • e₁ + (3/2*t^2) • e₂) = -t^4/4 := by
  simp only [quartic, map_add, map_smul, smul_eq_mul, ha1, hb1, ha2, hb2]
  ring

/-- A direction that strictly decreases the objective for all sufficiently small positive
line parameters. This includes the initial local requirement of a descent linesearch. -/
def LocallyStrictDescent (f : E → ℝ) (x d : E) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t → t < r → f (x + t • d) < f x

/-- A proposed next-iterate function only moves when a local strict descent direction exists. -/
def RequiresLocalDescent (f : E → ℝ) (next : E → Option E) : Prop :=
  ∀ x y, next x = some y → ∃ d, LocallyStrictDescent f x d

/-- The quartic has no local strict descent direction, including directions annihilated
by both coordinates. -/
theorem quartic_no_local_descent (a b : E →L[ℝ] ℝ) (d : E) :
    ¬LocallyStrictDescent (quartic a b) 0 d := by
  rintro ⟨r, hr, h⟩
  by_cases hd : a d = 0 ∧ b d = 0
  · have hh := h (r/2) (by linarith) (by linarith)
    simp [quartic, hd.1, hd.2] at hh
  · have hcoords : a d ≠ 0 ∨ b d ≠ 0 := not_and_or.mp hd
    obtain ⟨s, hs, hp⟩ := quartic_strict_line a b hcoords
    let t := min r s / 2
    have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min hr hs)
    have htr : t < r := by dsimp [t]; have := min_le_left r s; linarith
    have hts : |t| < s := by
      rw [abs_of_pos ht]
      dsimp [t]
      have := min_le_right r s
      linarith
    have hh := h t ht htr
    have hp := hp t ht.ne' hts
    have hzero : quartic a b 0 = 0 := by simp [quartic]
    simp only [zero_add, hzero] at hh
    linarith

/-- Every method requiring an initial local strict descent direction stops at the origin. -/
theorem quartic_next_eq_none (a b : E →L[ℝ] ℝ) (next : E → Option E)
    (hnext : RequiresLocalDescent (quartic a b) next) : next 0 = none := by
  cases h : next 0 with
  | none => rfl
  | some y =>
    obtain ⟨d, hd⟩ := hnext 0 y h
    exact (quartic_no_local_descent a b d hd).elim

/-- The negative parabolic values rule out an actual local minimum. -/
theorem quartic_not_isLocalMin (a b : E →L[ℝ] ℝ) (e₁ e₂ : E)
    (ha1 : a e₁ = 1) (hb1 : b e₁ = 0) (ha2 : a e₂ = 0) (hb2 : b e₂ = 1) :
    ¬IsLocalMin (quartic a b) 0 := by
  intro h
  let c : ℝ → E := fun t => t • e₁ + (3/2*t^2) • e₂
  have hc : ContinuousAt c 0 := by dsimp [c]; fun_prop
  have hc0 : c 0 = 0 := by simp [c]
  have hh : IsLocalMin (quartic a b) (c 0) := by simpa only [hc0] using h
  have hm := hh.comp_continuous hc
  change ∀ᶠ t : ℝ in nhds 0, quartic a b (c 0) ≤ quartic a b (c t) at hm
  simp only [hc0, c, quartic_parabola a b e₁ e₂ ha1 hb1 ha2 hb2] at hm
  obtain ⟨r, hr, hm⟩ := Metric.eventually_nhds_iff.mp hm
  have hdist : dist (r/2) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  have hh := hm hdist
  have hp : 0 < (r/2)^4 := pow_pos (half_pos hr) 4
  norm_num [quartic] at hh
  linarith

end Optimization.LineSearchObstruction
