import Numlib.Analysis.Calculus.CurveTaylor
import Numlib.Optimization.LineSearchObstruction
import Numlib.Optimization.TaylorOptimality
import Numlib.Optimization.TaylorModelRemainder
import Numlib.Analysis.Normed.Multilinear.Diagonal
import Numlib.Analysis.Calculus.Gradient
import NumlibSurface.CartisGouldToint.Chapter01.Section03

/-!
# Chapter 12, Section 1: Taylor gaps and stability

Taylor gaps are actual maxima of Taylor decrements on closed Euclidean balls. Each requested
order has its own positive tolerance and radius. Local Lipschitz control of the highest tensor
gives the source stability bound, including its sharper zero-constant branch.
-/

noncomputable section
open scoped Nat
open Set Metric Optimization
open CartisGouldToint.Chapter01.Section03
namespace CartisGouldToint.Chapter12.Section01

variable {n : ℕ}

/-- The actual factorial-normalized Taylor decrement (12.1.11). -/
abbrev taylorDecrement (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    (x d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  TaylorCriticality.taylorDecrement f j x d

/-- The Taylor criticality measure (12.1.10), as the maximum actual decrement. -/
def taylorCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ) (delta : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  TaylorCriticality.gapOn (taylorDecrement f j x) (closedBall 0 delta)

/-- Every nonnegative-radius Taylor gap is attained by an actual feasible displacement. -/
theorem exists_eq_taylorCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ d, ‖d‖ ≤ delta ∧ taylorDecrement f j x d = taylorCriticality f j delta x := by
  obtain ⟨d, hd, he⟩ := TaylorCriticality.exists_eq_gapOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
    (show (closedBall (0 : EuclideanSpace ℝ (Fin n)) delta).Nonempty from
      ⟨0, by simpa using hd⟩)
    (TaylorCriticality.continuous_taylorDecrement f j x).continuousOn
  exact ⟨d, by simpa using hd, he⟩

/-- The criticality bound is equivalent to bounding every feasible Taylor decrement. -/
theorem taylorCriticality_le_iff (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (x : EuclideanSpace ℝ (Fin n)) (G : ℝ) :
    taylorCriticality f j delta x ≤ G ↔ ∀ d, ‖d‖ ≤ delta → taylorDecrement f j x d ≤ G := by
  exact (TaylorCriticality.gapOn_le_iff
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) delta)
    ⟨0, by simpa using hd⟩
    (TaylorCriticality.continuous_taylorDecrement f j x).continuousOn).trans
      (by simp only [mem_closedBall_zero_iff])

/-- The attained decrement indeed equals the objective value minus the actual model minimum. -/
theorem exists_taylorModel_minimum (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ d, ‖d‖ ≤ delta ∧
      (∀ e, ‖e‖ ≤ delta → taylorModel f j x d ≤ taylorModel f j x e) ∧
      taylorCriticality f j delta x = f x - taylorModel f j x d := by
  obtain ⟨d, hd', he⟩ := exists_eq_taylorCriticality f j hd x
  refine ⟨d, hd', ?_, ?_⟩
  · intro e he'
    have hh := (taylorCriticality_le_iff f j hd x (taylorCriticality f j delta x)).mp le_rfl e he'
    rw [← he] at hh
    simp only [taylorDecrement, TaylorCriticality.taylorDecrement_eq] at hh
    change RegularizedTaylorModel.taylorModel f j x d ≤ RegularizedTaylorModel.taylorModel f j x e
    linarith
  · simpa only [taylorDecrement, TaylorCriticality.taylorDecrement_eq,
      CartisGouldToint.Chapter01.Section03.taylorModel] using he.symm

/-- Zero displacement makes the Taylor gap nonnegative. -/
theorem taylorCriticality_nonneg (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ taylorCriticality f j delta x := by
  exact TaylorCriticality.gapOn_nonneg (isCompact_closedBall 0 delta)
    (TaylorCriticality.continuous_taylorDecrement f j x).continuousOn
    (by simpa using hd) (TaylorCriticality.taylorDecrement_zero f j x)

/-- The first-order measure is exactly radius times actual gradient norm. -/
theorem taylorCriticality_one (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {delta : ℝ} (hd : 0 ≤ delta) (x : EuclideanSpace ℝ (Fin n)) :
    taylorCriticality f 1 delta x = delta * ‖gradient f x‖ := by
  unfold taylorCriticality taylorDecrement
  simp_rw [TaylorCriticality.taylorDecrement_one]
  rw [TaylorCriticality.gapOn_norm_linear _ hd, EuclideanSpace.norm_gradient_eq]

/-- The source's cumulative approximate optimality definition (12.1.25). Upper bounds on
radii and tolerances accompany the canonical compact-set gap criteria. -/
structure IsApproxOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (q : ℕ) (epsilon delta : ℕ → ℝ) : Prop extends
    TaylorCriticality.IsApproxMinimizer f x q epsilon delta (fun j => closedBall 0 (delta j)) where
  order_pos : 1 ≤ q
  epsilon_le_one : ∀ j, 1 ≤ j → j ≤ q → epsilon j ≤ 1
  radius_le_one : ∀ j, 1 ≤ j → j ≤ q → delta j ≤ 1

/-- The surface definition is exactly the source's active-order inequalities; compactness
and displacement feasibility follow from the Euclidean balls rather than new assumptions. -/
theorem isApproxOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {q : ℕ} {epsilon delta : ℕ → ℝ} :
    IsApproxOrderMinimizer f x q epsilon delta ↔ 1 ≤ q ∧
      ∀ j, 1 ≤ j → j ≤ q →
        0 < epsilon j ∧ epsilon j ≤ 1 ∧ 0 < delta j ∧ delta j ≤ 1 ∧
        taylorCriticality f j (delta j) x ≤ epsilon j * delta j ^ j / (j ! : ℝ) := by
  constructor
  · intro h
    exact ⟨h.order_pos, fun j hj hq =>
      ⟨h.epsilon_pos j hj hq, h.epsilon_le_one j hj hq, h.radius_pos j hj hq,
        h.radius_le_one j hj hq, h.gap_le j hj hq⟩⟩
  · rintro ⟨hq, h⟩
    exact {
      epsilon_pos := fun j hj hjq => (h j hj hjq).1
      radius_pos := fun j hj hjq => (h j hj hjq).2.2.1
      compact := fun j _ _ => isCompact_closedBall 0 (delta j)
      zero_mem := fun j hj hjq => by simpa using (h j hj hjq).2.2.1.le
      norm_le := fun _ _ _ _ hd => by simpa using hd
      gap_le := fun j hj hjq => (h j hj hjq).2.2.2.2
      order_pos := hq
      epsilon_le_one := fun j hj hjq => (h j hj hjq).2.1
      radius_le_one := fun j hj hjq => (h j hj hjq).2.2.2.1 }

/-- Local Lipschitz control in the source's diagonal tensor norm, on an actual open ball. -/
def derivativeLipschitzOnBall (f : EuclideanSpace ℝ (Fin n) → ℝ) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R L : ℝ) : Prop :=
  ∀ y ∈ ball x R, ∀ z ∈ ball x R,
    (iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f z).diagonalNorm ≤ L * ‖y - z‖

/-- The local tensor assumption supplies the actual sharp Taylor remainder on the ball. -/
theorem derivativeLipschitzOnBall.remainder {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {j : ℕ} {x d : EuclideanSpace ℝ (Fin n)} {R L delta : ℝ}
    (hj : 1 ≤ j) (hf : ContDiff ℝ j f) (hL : 0 ≤ L) (hR : delta < R)
    (hdelta : 0 ≤ delta) (hd : ‖d‖ ≤ delta) (h : derivativeLipschitzOnBall f j x R L) :
    |f (x + d) - taylorModel f j x d| ≤
      L / ((j + 1)! : ℝ) * ‖d‖ ^ (j + 1) := by
  apply norm_sub_taylorModel_le_of_lipschitz_diagonal hj
    (fun _ _ => hf.contDiffAt)
  intro t ht
  have hx : x ∈ ball x R := by simp only [mem_ball, dist_self]; linarith
  have htd : ‖t • d‖ ≤ delta := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg d) ht.2).trans hd
  have hxt : x + t • d ∈ ball x R := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using htd.trans_lt hR
  simpa only [ContinuousMultilinearMap.diagonal, add_sub_cancel_left] using
    ((iteratedFDeriv ℝ j f (x + t • d) - iteratedFDeriv ℝ j f x).diagonalNorm_le_iff
    (by omega) (mul_nonneg hL (norm_nonneg _))).mp
    (h _ hxt _ hx) d

/-- Theorem 12.1.8: the source stability radius gives twice the Taylor-gap tolerance for a
positive local Lipschitz constant, and the full-radius single tolerance when it is zero. -/
theorem theorem_12_1_8 {f : EuclideanSpace ℝ (Fin n) → ℝ} {j : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} {epsilon delta R L : ℝ}
    (hj : 1 ≤ j) (hf : ContDiff ℝ j f) (he : 0 < epsilon) (_hed : epsilon ≤ 1)
    (hd : 0 < delta) (_hdd : delta ≤ 1) (hL : 0 ≤ L) (hR : delta < R)
    (hLip : derivativeLipschitzOnBall f j x R L)
    (hgap : taylorCriticality f j delta x ≤ epsilon * delta ^ j / (j ! : ℝ)) :
    (0 < L → ∀ d : EuclideanSpace ℝ (Fin n),
      ‖d‖ ≤ min delta (((j + 1 : ℕ) : ℝ) * epsilon / L) →
      f x - 2 * epsilon * delta ^ j / (j ! : ℝ) ≤ f (x + d)) ∧
    (L = 0 → ∀ d : EuclideanSpace ℝ (Fin n), ‖d‖ ≤ delta →
      f x - epsilon * delta ^ j / (j ! : ℝ) ≤ f (x + d)) := by
  constructor
  · intro hLp d hdn
    have hrem := hLip.remainder hj hf hL hR hd.le ((le_min_iff.mp hdn).1)
    have hs : L * ‖d‖ ≤ ((j + 1 : ℕ) : ℝ) * epsilon := by
      have hh := (le_div_iff₀ hLp).mp (le_min_iff.mp hdn).2
      nlinarith
    simpa only [add_zero, sub_zero] using TaylorCriticality.value_lower_bound_of_gap_le
      (eta := 0) (isCompact_closedBall 0 delta)
      (show d ∈ closedBall 0 delta by simpa using (le_min_iff.mp hdn).1)
      he.le (le_min_iff.mp hdn).1
      (by simpa only [add_zero, taylorCriticality, taylorDecrement] using hgap :
        TaylorCriticality.gapOn (TaylorCriticality.taylorDecrement f j x)
          (closedBall 0 delta) ≤ epsilon * delta ^ j / (j ! : ℝ) + 0) hrem hs
  · intro hzero d hdn
    have hrem := hLip.remainder hj hf hL hR hd.le hdn
    rw [hzero, zero_div, zero_mul] at hrem
    have heq : f (x + d) = taylorModel f j x d :=
      sub_eq_zero.mp (abs_nonpos_iff.mp hrem)
    exact TaylorCriticality.value_lower_bound_of_gap_le_of_zero_remainder
      (isCompact_closedBall 0 delta) (by simpa using hdn) hgap heq

/-- A corrected sufficient condition: uniform positive order-j Taylor growth, together
with an actual next-order remainder bound, gives both strict isolated local minima. The
uniform growth hypothesis strengthens the false isolated-minimum premise of Theorem 12.1.5. -/
theorem isLocalMin_of_uniform_taylor_growth {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {j : ℕ} {c C R : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hgrowth : ∀ s, ‖s‖ ≤ R → c * ‖s‖ ^ j ≤ taylorModel f j x s - f x)
    (hrem : ∀ s, ‖s‖ ≤ R → |f (x + s) - taylorModel f j x s| ≤
      C * ‖s‖ ^ (j + 1)) :
    (IsLocalMin f x ∧ ∃ r : ℝ, 0 < r ∧
      ∀ s : EuclideanSpace ℝ (Fin n), ‖s‖ < r → s ≠ 0 → f x < f (x + s)) ∧
    (IsLocalMin (taylorModel f (j + 1) x) 0 ∧ ∃ r : ℝ, 0 < r ∧
      ∀ s : EuclideanSpace ℝ (Fin n), ‖s‖ < r → s ≠ 0 →
        taylorModel f (j + 1) x 0 < taylorModel f (j + 1) x s) :=
  ⟨TaylorCriticality.isLocalMin_of_uniform_growth hc hC hR hgrowth hrem,
    TaylorCriticality.taylorModel_isLocalMin_of_uniform_growth hc hR hgrowth⟩

end CartisGouldToint.Chapter12.Section01

namespace CartisGouldToint.Chapter12.Section01
open Optimization.LineSearchObstruction
open scoped ContDiff

/-- Positive ordered compositions in (12.1.5); each entry lies in `[1,j]`. -/
abbrev curveCompositionIndices (j k : ℕ) := CurveTaylor.compositionIndices j k

/-- The mixed derivative coefficient in (12.1.6) and (12.1.7), with its actual factorial. -/
abbrev curveCoefficient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ℕ → EuclideanSpace ℝ (Fin n)) : ℝ :=
  CurveTaylor.coefficient f x j s

/-- The source's cumulative curve conditions, with every active direction nonzero.
The directions are vectors in Euclidean space, correcting the OCR scalar domain. -/
def IsCurveOrderMinimizer {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (q : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ q → ∀ s : ℕ → EuclideanSpace ℝ (Fin n),
    (∀ i, 1 ≤ i → i ≤ j → s i ≠ 0) →
    (∀ i, 1 ≤ i → i < j → curveCoefficient f x i s = 0) →
    0 ≤ curveCoefficient f x j s

/-- The canonical condition on all jets implies the source condition on nonzero jets. -/
theorem isCurveOrderMinimizer_of_canonical {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {q : ℕ}
    (h : CurveTaylor.IsOrderMinimizer f x q) : IsCurveOrderMinimizer f x q :=
  fun j hj hjq s _ hs => h j hj hjq s hs

/-- Restriction to lower orders preserves the curve-based necessary conditions. -/
theorem IsCurveOrderMinimizer.mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {q r : ℕ}
    (h : IsCurveOrderMinimizer f x q) (hr : r ≤ q) : IsCurveOrderMinimizer f x r :=
  fun j hj hjr s hne hs => h j hj (hjr.trans hr) s hne hs

/-- The Peano quartic (12.1.8) with κ₁=3, κ₂=2. The OCR's κ₁=1 in the later prose is
inconsistent with the displayed curve and figure; κ₁=3 gives the claimed obstruction. -/
def peanoQuartic (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  quartic (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) x

/-- The first coordinate unit vector. -/
def peanoAxis₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- The second coordinate unit vector. -/
def peanoAxis₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]

/-- Every nonzero straight line through the origin initially increases the objective. -/
theorem peanoQuartic_strict_line {d : EuclideanSpace ℝ (Fin 2)} (hd : d ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, t ≠ 0 → |t| < r → peanoQuartic (t • d) > peanoQuartic 0 := by
  have hcoords : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hd
    ext i
    fin_cases i <;> simp [hh.1, hh.2]
  simpa only [peanoQuartic, quartic, map_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    zero_pow (by decide : 4 ≠ 0), sub_zero, add_zero] using
      quartic_strict_line (E := EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) hcoords

/-- An actual fourth-order jet violates the mixed curve condition with all preceding
coefficients zero. -/
theorem peanoQuartic_badJet :
    (∀ j, 1 ≤ j → j < 4 → curveCoefficient peanoQuartic 0 j
      (badJet peanoAxis₁ peanoAxis₂) = 0) ∧
    curveCoefficient peanoQuartic 0 4 (badJet peanoAxis₁ peanoAxis₂) = -(1/4 : ℝ) := by
  exact quartic_badJet_coefficients (E := EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace.proj 0) (EuclideanSpace.proj 1)
    peanoAxis₁ peanoAxis₂ rfl rfl rfl rfl

/-- All the entries in the counterexample jet are nonzero, as in the source's stricter
nonzero-direction convention. -/
theorem peanoQuartic_badJet_ne_zero (j : ℕ) : badJet peanoAxis₁ peanoAxis₂ j ≠ 0 := by
  intro h
  by_cases hj : j = 2
  · have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    norm_num [badJet, hj, peanoAxis₂] at hh
  · have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    norm_num [badJet, hj, peanoAxis₁] at hh

/-- The actual curve from the source strictly decreases on both sides of the origin. -/
theorem peanoQuartic_parabola (t : ℝ) :
    peanoQuartic (t • peanoAxis₁ + (3/2*t^2) • peanoAxis₂) = -t^4/4 :=
  quartic_parabola (E := EuclideanSpace ℝ (Fin 2)) (EuclideanSpace.proj 0) (EuclideanSpace.proj 1)
    peanoAxis₁ peanoAxis₂ rfl rfl rfl rfl t

/-- Theorem 12.1.2: an everywhere smooth objective can be strictly minimal on every line
and fail every curve order at least four. Every next-iterate rule requiring an initial local
strict descent direction must return no step at this point. This is the explicit obstruction
behind the source's informal impossibility assertion. -/
theorem theorem_12_1_2 :
    ContDiff ℝ ∞ peanoQuartic ∧
    (∀ d : EuclideanSpace ℝ (Fin 2), d ≠ 0 →
      ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, t ≠ 0 → |t| < r →
        peanoQuartic 0 < peanoQuartic (t • d)) ∧
    (∀ q : ℕ, 4 ≤ q → ¬IsCurveOrderMinimizer peanoQuartic 0 q) ∧
    ¬IsLocalMin peanoQuartic 0 ∧
    (∀ next : EuclideanSpace ℝ (Fin 2) → Option (EuclideanSpace ℝ (Fin 2)),
      RequiresLocalDescent peanoQuartic next → next 0 = none) := by
  refine ⟨contDiff_quartic (E := EuclideanSpace ℝ (Fin 2)) _ _,
    fun _ hd => peanoQuartic_strict_line hd, ?_, ?_, ?_⟩
  · intro q hq h
    have hh := h 4 (by decide) hq (badJet peanoAxis₁ peanoAxis₂)
      (fun i _ _ => peanoQuartic_badJet_ne_zero i) peanoQuartic_badJet.1
    rw [peanoQuartic_badJet.2] at hh
    norm_num at hh
  · exact quartic_not_isLocalMin (E := EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace.proj 0) (EuclideanSpace.proj 1)
      peanoAxis₁ peanoAxis₂ rfl rfl rfl rfl
  · intro next hnext
    exact quartic_next_eq_none (E := EuclideanSpace ℝ (Fin 2)) _ _ next hnext

end CartisGouldToint.Chapter12.Section01
