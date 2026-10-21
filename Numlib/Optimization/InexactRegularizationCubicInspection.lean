import Numlib.Optimization.InexactRegularizationBounds

/-!
# Fractional witnesses in cubic regularization inspections

A computed pass need not occur at the first radius at which it is possible. On a cubic
polynomial, exact maximizers can fail the fractional test while a smaller fractional witness
passes it. A sufficiently large regularizer makes every preceding halving legal. Thus an
all-pass inspection alone does not supply a radius bound independent of the regularizer.
This local fact does not assert reachability from the initialization of an outer execution.
-/

noncomputable section
open scoped Nat
namespace Optimization.InexactRegularization
open InexactTaylorModels TaylorCriticality

/-- A scalar coefficient family with just the negative cubic coefficient of magnitude `a`. -/
def cubicCoefficients (a : ℝ) : Coefficients ℝ
  | 3 => -a • ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ
  | _ => 0

/-- The pure cubic coefficient family in the canonical scalar multilinear isometry. -/
theorem cubicCoefficients_equiv (a : ℝ) (i : ℕ) :
    cubicCoefficients a i = ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) ℝ
      (if i = 3 then -a else 0) := by
  by_cases hi : i = 3
  · subst i
    apply ContinuousMultilinearMap.ext
    intro v
    simp [cubicCoefficients, ContinuousMultilinearMap.piFieldEquiv,
      ContinuousMultilinearMap.mkPiRing, ContinuousMultilinearMap.mkPiAlgebra]
    ring
  · simp [cubicCoefficients, hi]

/-- The cubic coefficient gives its literal scalar cubic on a diagonal. -/
theorem cubicCoefficients_three (a d : ℝ) :
    cubicCoefficients a 3 (fun _ => d) = -a * d ^ 3 := by
  simp [cubicCoefficients, pow_succ]

/-- The degree-three Taylor decrement of the cubic coefficient family. -/
theorem decrement_cubicCoefficients (a d : ℝ) :
    decrement (cubicCoefficients a) 3 d = a * d ^ 3 / 6 := by
  norm_num [decrement, Finset.sum_Icc_succ_top, cubicCoefficients,
    Fin.prod_univ_succ]
  ring

/-- The corresponding regularized polynomial has the actual quartic radial regularizer. -/
theorem regularizedPolynomial_cubicCoefficients (a σ d : ℝ) :
    regularizedPolynomial 0 (cubicCoefficients a) 3 σ d =
      -a * d ^ 3 / 6 + σ * d ^ 4 / 24 := by
  have hd := decrement_eq 0 (cubicCoefficients a) 3 d
  rw [polynomial_zero, decrement_cubicCoefficients] at hd
  have he : |d| ^ 4 = d ^ 4 := by
    calc
      |d| ^ 4 = (|d| ^ 2) ^ 2 := by ring
      _ = (d ^ 2) ^ 2 := by rw [sq_abs]
      _ = d ^ 4 := by ring
  simp only [regularizedPolynomial, Real.norm_eq_abs]
  rw [he]
  norm_num
  linarith

/-- The positive endpoint is an exact gap maximizer on a nonnegative scalar radius. -/
theorem cubicCoefficients_witness {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    CoefficientWitness (cubicCoefficients a) 3 δ 1 δ := by
  have hg : gapOn (decrement (cubicCoefficients a) 3) (Metric.closedBall 0 δ) ≤
      a * δ ^ 3 / 6 := by
    apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    rw [decrement_cubicCoefficients]
    have hb : d ≤ δ := (le_abs_self d).trans (by simpa using hd)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((Odd.strictMono_pow (by decide : Odd 3)).monotone hb) ha) (by norm_num)
  refine ⟨by simp [Real.norm_eq_abs, abs_of_nonneg hδ], ?_⟩
  simpa [decrement_cubicCoefficients] using hg

/-- Halving the positive endpoint gives precisely an eighth of the exact cubic gap. -/
theorem cubicCoefficients_eighth_witness {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    CoefficientWitness (cubicCoefficients a) 3 δ (1 / 8) (δ / 2) := by
  have hw := cubicCoefficients_witness ha hδ
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  · rw [decrement_cubicCoefficients]
    have hg := mul_le_mul_of_nonneg_left hw.fraction_le (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [one_mul, decrement_cubicCoefficients] at hg
    nlinarith

/-- A cubic search can legally halve any prescribed number of times before passing with
an eighth-fraction witness. The last radius only needs `σ * δ ≥ 1`. Earlier trials use the
exact maximizer; the last uses half that displacement. No computed gap oracle is assumed. -/
def cubicPassingSearch (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ * halvedRadius 1 N) :
    RadiusSearch 0 (cubicCoefficients (1 / 8)) 3 3 σ 1 (1 / 8) (1 / 2) N where
  direction := fun k => if k = N then halvedRadius 1 k / 2 else halvedRadius 1 k
  witness := by
    intro k hk
    have hr : 0 ≤ halvedRadius 1 k := (halvedRadius_pos (by norm_num) k).le
    split_ifs
    · exact cubicCoefficients_eighth_witness (by norm_num) hr
    · have hw := cubicCoefficients_witness (by norm_num : (0 : ℝ) ≤ 1 / 8) hr
      refine ⟨hw.feasible, ?_⟩
      have hnonneg : 0 ≤ decrement (cubicCoefficients (1 / 8)) 3 (halvedRadius 1 k) := by
        rw [decrement_cubicCoefficients]
        positivity
      simpa only [one_mul] using (mul_le_mul_of_nonneg_left hw.fraction_le
        (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans
        (by simpa using mul_le_of_le_one_left hnonneg (by norm_num : (1 / 8 : ℝ) ≤ 1))
  failed := by
    intro k hk
    simp only [ite_eq_right (ne_of_lt hk)]
    have hr : 0 < halvedRadius 1 k := halvedRadius_pos (by norm_num) k
    have hσpos : 0 ≤ σ := by nlinarith [halvedRadius_pos (by norm_num : (0 : ℝ) < 1) N]
    have hprod : 1 ≤ σ * halvedRadius 1 k := hσ.trans
      (mul_le_mul_of_nonneg_left (halvedRadius_antitone (by norm_num) hk.le) hσpos)
    rw [decrement_cubicCoefficients, regularizedPolynomial_cubicCoefficients]
    norm_num only [Nat.factorial]
    constructor
    · nlinarith [pow_pos hr 3]
    · have hp := mul_le_mul_of_nonneg_right hprod (pow_nonneg hr.le 3)
      nlinarith [pow_pos hr 3]

/-- The last chosen fractional witness passes the literal non-strict computed test. -/
theorem cubicPassingSearch_passed (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ * halvedRadius 1 N) :
    decrement (cubicCoefficients (1 / 8)) 3 ((cubicPassingSearch N hσ).direction N) ≤
      (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 N ^ 3 / (2 * (3 ! : ℝ)) := by
  simp only [cubicPassingSearch, ite_true, decrement_cubicCoefficients]
  have hr : 0 ≤ halvedRadius 1 N := (halvedRadius_pos (by norm_num) N).le
  norm_num only [Nat.factorial]
  nlinarith [pow_nonneg hr 3]

/-- The first two truncations of the pure cubic vanish. -/
theorem decrement_cubicCoefficients_low (a d : ℝ) {j : ℕ} (hj : j ≤ 2) :
    decrement (cubicCoefficients a) j d = 0 := by
  interval_cases j <;> norm_num [decrement, Finset.sum_Icc_succ_top, cubicCoefficients]

/-- A genuine all-pass inspection can contain any prescribed number of cubic halvings.
Every incoming radius is one. This is an inspection constructor, without a claim that the
large parameter is reachable in an outer run. -/
def cubicPassingInspection (P : Parameters) (hp : P.p = 3) (hq : P.q = 3)
    (hv : P.fraction = 1 / 8) (hε : P.epsilon = fun _ => 1 / 2)
    (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ * halvedRadius 1 N) :
    Inspection P 0 (cubicCoefficients (1 / 8)) σ (fun _ => 1) where
  order := 4
  order_pos := by norm_num
  order_le := by rw [hq]
  halvings := fun j => if j = 3 then N else 0
  search := by
    intro j hj hjq hjo
    have hj3 : j ≤ 3 := hjq.trans_eq hq
    by_cases he : j = 3
    · subst j
      simp only [ite_true]
      exact {
        direction := (cubicPassingSearch N hσ).direction
        witness := by simpa only [hv] using (cubicPassingSearch N hσ).witness
        failed := by simpa only [hp, hv, hε] using (cubicPassingSearch N hσ).failed }
    · have hj2 : j ≤ 2 := by omega
      have hjne : ¬j = 3 := he
      simp only [ite_eq_right hjne]
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro k hk
        have hk0 : k = 0 := by omega
        subst k
        refine ⟨by simp, ?_⟩
        have heq : decrement (cubicCoefficients (1 / 8)) j = fun _ : ℝ => 0 := by
          funext d
          exact decrement_cubicCoefficients_low _ _ hj2
        rw [heq]
        simp [gapOn]
      · intro k hk
        omega
  earlier := by
    intro j hj hjq hjo
    have hj3 : j ≤ 3 := hjq.trans_eq hq
    by_cases he : j = 3
    · subst j
      simpa [hp, hv, hε] using cubicPassingSearch_passed N hσ
    · have hj2 : j ≤ 2 := by omega
      rw [decrement_cubicCoefficients_low _ _ hj2]
      have hεpos := P.epsilon_pos j hj hjq
      have hvpos := P.fraction_pos
      have hr := halvedRadius_pos (by norm_num : (0 : ℝ) < 1)
        ((fun j => if j = 3 then N else 0) j)
      positivity
  failed := by intro h; omega
  retained := by intro h; omega

/-- The constructed complete inspection has the exact requested terminal cubic radius. -/
theorem cubicPassingInspection_radius (P : Parameters) (hp : P.p = 3) (hq : P.q = 3)
    (hv : P.fraction = 1 / 8) (hε : P.epsilon = fun _ => 1 / 2)
    (N : ℕ) {σ : ℝ} (hσ : 1 ≤ σ * halvedRadius 1 N) :
    (cubicPassingInspection P hp hq hv hε N hσ).radii 3 = halvedRadius 1 N := by
  simp [Inspection.radii, cubicPassingInspection]

end Optimization.InexactRegularization
