import Numlib.Optimization.TaylorCriticality
import Numlib.Optimization.RegularizedTaylorModel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LocalExtr

/-!
# Taylor decrements and quantitative approximate optimality

Actual Taylor polynomials give scalar decrements. Compact displacement sets make their gaps
attained; bounded decrement images suffice for value bounds on arbitrary sets. Order-indexed
radii and tolerances describe approximate minimizers. A controlled
Taylor remainder transfers these gap bounds to objective stability. Uniform positive model
growth, unlike isolated polynomial minimality, also transfers strict local minimality.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.TaylorCriticality
open RegularizedTaylorModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The decrement of the actual factorial-normalized Taylor polynomial. -/
def taylorDecrement (f : E → ℝ) (p : ℕ) (x d : E) : ℝ :=
  taylorModel f p x 0 - taylorModel f p x d

/-- At zero displacement the Taylor decrement vanishes. -/
@[simp] theorem taylorDecrement_zero (f : E → ℝ) (p : ℕ) (x : E) :
    taylorDecrement f p x 0 = 0 := by simp [taylorDecrement]

/-- A constant Taylor model has zero decrement. -/
@[simp] theorem taylorDecrement_zero_degree (f : E → ℝ) (x d : E) :
    taylorDecrement f 0 x d = 0 := by simp [taylorDecrement]

/-- The decrement cancels the constant objective coefficient. -/
theorem taylorDecrement_eq (f : E → ℝ) (p : ℕ) (x d : E) :
    taylorDecrement f p x d = f x - taylorModel f p x d := by simp [taylorDecrement]

/-- Increasing the Taylor order subtracts precisely its new homogeneous term. -/
theorem taylorDecrement_succ (f : E → ℝ) (p : ℕ) (x d : E) :
    taylorDecrement f (p + 1) x d = taylorDecrement f p x d -
      ((p + 1)! : ℝ)⁻¹ * iteratedFDeriv ℝ (p + 1) f x (fun _ => d) := by
  simp only [taylorDecrement_eq, taylorModel_succ, smul_eq_mul]
  ring

/-- Taylor decrements are continuous even without smoothness of the original function. -/
theorem continuous_taylorDecrement (f : E → ℝ) (p : ℕ) (x : E) :
    Continuous (taylorDecrement f p x) :=
  continuous_const.sub (contDiff_taylorModel f p x 0).continuous

/-- On a line the decrement uses the same factorial coefficients and scalar powers as
its underlying Taylor model. -/
theorem taylorDecrement_smul (f : E → ℝ) (p : ℕ) (x d : E) (t : ℝ) :
    taylorDecrement f p x (t • d) = f x -
      ∑ j ∈ Finset.range (p + 1), (t ^ j / (j ! : ℝ)) *
        iteratedFDeriv ℝ j f x (fun _ => d) := by
  simp only [taylorDecrement_eq, taylorModel_smul, smul_eq_mul]

/-- The first-order decrement is minus the actual derivative applied to the displacement. -/
@[simp] theorem taylorDecrement_one (f : E → ℝ) (x d : E) :
    taylorDecrement f 1 x d = -fderiv ℝ f x d := by
  simp only [taylorDecrement_eq, taylorModel_one]
  ring

/-- An order-indexed approximate minimizer on genuine compact displacement sets. Each
active set contains zero and lies within its own positive-radius ball. -/
structure IsApproxMinimizer (f : E → ℝ) (x : E) (q : ℕ)
    (epsilon delta : ℕ → ℝ) (D : ℕ → Set E) : Prop where
  epsilon_pos : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j
  radius_pos : ∀ j, 1 ≤ j → j ≤ q → 0 < delta j
  compact : ∀ j, 1 ≤ j → j ≤ q → IsCompact (D j)
  zero_mem : ∀ j, 1 ≤ j → j ≤ q → (0 : E) ∈ D j
  norm_le : ∀ j, 1 ≤ j → j ≤ q → ∀ d ∈ D j, ‖d‖ ≤ delta j
  gap_le : ∀ j, 1 ≤ j → j ≤ q →
    gapOn (taylorDecrement f j x) (D j) ≤ epsilon j * delta j ^ j / (j ! : ℝ)

/-- Restricting the requested orders preserves approximate optimality. -/
theorem IsApproxMinimizer.mono_order {f : E → ℝ} {x : E} {q r : ℕ}
    {epsilon delta : ℕ → ℝ} {D : ℕ → Set E}
    (h : IsApproxMinimizer f x q epsilon delta D) (hr : r ≤ q) :
    IsApproxMinimizer f x r epsilon delta D :=
  ⟨fun j hj hq => h.epsilon_pos j hj (hq.trans hr),
   fun j hj hq => h.radius_pos j hj (hq.trans hr),
   fun j hj hq => h.compact j hj (hq.trans hr),
   fun j hj hq => h.zero_mem j hj (hq.trans hr),
   fun j hj hq => h.norm_le j hj (hq.trans hr),
   fun j hj hq => h.gap_le j hj (hq.trans hr)⟩

/-- Enlarging every active tolerance preserves the same approximate point and radii. -/
theorem IsApproxMinimizer.mono_tolerances {f : E → ℝ} {x : E} {q : ℕ}
    {epsilon epsilon' delta : ℕ → ℝ} {D : ℕ → Set E}
    (h : IsApproxMinimizer f x q epsilon delta D)
    (he : ∀ j, 1 ≤ j → j ≤ q → epsilon j ≤ epsilon' j) :
    IsApproxMinimizer f x q epsilon' delta D := by
  refine { h with epsilon_pos := ?_, gap_le := ?_ }
  · intro j hj hq
    exact (h.epsilon_pos j hj hq).trans_le (he j hj hq)
  · intro j hj hq
    exact (h.gap_le j hj hq).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (he j hj hq)
          (pow_nonneg (h.radius_pos j hj hq).le _)) (by positivity))

/-- An approximate gap bounds every actual feasible Taylor decrement. -/
theorem IsApproxMinimizer.decrement_le {f : E → ℝ} {x d : E} {q j : ℕ}
    {epsilon delta : ℕ → ℝ} {D : ℕ → Set E}
    (h : IsApproxMinimizer f x q epsilon delta D) (hj : 1 ≤ j) (hjq : j ≤ q)
    (hd : d ∈ D j) :
    taylorDecrement f j x d ≤ epsilon j * delta j ^ j / (j ! : ℝ) :=
  (le_gapOn (h.compact j hj hjq) (continuous_taylorDecrement f j x).continuousOn hd).trans
    (h.gap_le j hj hjq)

/-- A bounded Taylor decrement image and a genuine pointwise remainder control objective
value. The displacement set need not be closed or compact. -/
theorem value_lower_bound_of_gap_and_remainder_of_bddAbove {f : E → ℝ} {x d : E} {p : ℕ}
    {D : Set E} {G R : ℝ} (hb : BddAbove (taylorDecrement f p x '' D)) (hd : d ∈ D)
    (hgap : gapOn (taylorDecrement f p x) D ≤ G)
    (hrem : |f (x + d) - taylorModel f p x d| ≤ R) :
    f x - G - R ≤ f (x + d) := by
  have ht := (le_gapOn_of_bddAbove hb hd).trans hgap
  rw [taylorDecrement_eq] at ht
  have hr := (abs_le.mp hrem).1
  linarith

/-- A Taylor-gap bound and a genuine pointwise remainder control actual objective decrease. -/
theorem value_lower_bound_of_gap_and_remainder {f : E → ℝ} {x d : E} {p : ℕ}
    {D : Set E} {G R : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (hgap : gapOn (taylorDecrement f p x) D ≤ G)
    (hrem : |f (x + d) - taylorModel f p x d| ≤ R) :
    f x - G - R ≤ f (x + d) :=
  value_lower_bound_of_gap_and_remainder_of_bddAbove
    (hD.image_of_continuousOn (continuous_taylorDecrement f p x).continuousOn).bddAbove
    hd hgap hrem

/-- A factorial Taylor remainder is at most the gap tolerance on the stability radius. -/
theorem remainder_le_tolerance {p : ℕ} {L epsilon delta t : ℝ}
    (he : 0 ≤ epsilon) (ht : 0 ≤ t) (htd : t ≤ delta)
    (hsmall : L * t ≤ ((p + 1 : ℕ) : ℝ) * epsilon) :
    L / ((p + 1)! : ℝ) * t ^ (p + 1) ≤ epsilon * delta ^ p / (p ! : ℝ) := by
  have hp : t ^ p ≤ delta ^ p := pow_le_pow_left₀ ht htd p
  have hh := mul_le_mul hsmall hp (pow_nonneg ht _)
    (mul_nonneg (Nat.cast_nonneg _) he)
  have hfac : ((p + 1)! : ℝ) = ((p + 1 : ℕ) : ℝ) * (p ! : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  calc
    _ = (L * t) * t ^ p / ((p + 1)! : ℝ) := by rw [pow_succ]; ring
    _ ≤ (((p + 1 : ℕ) : ℝ) * epsilon) * delta ^ p / ((p + 1)! : ℝ) :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by rw [hfac]; field_simp

/-- A bounded Taylor decrement image gives the stability estimate on arbitrary sets.
The actual Lipschitz remainder must fit within the same tolerance. -/
theorem value_lower_bound_of_gap_le_of_bddAbove {f : E → ℝ} {x d : E} {p : ℕ}
    {D : Set E} {L epsilon delta eta : ℝ}
    (hb : BddAbove (taylorDecrement f p x '' D)) (hd : d ∈ D)
    (he : 0 ≤ epsilon) (hdn : ‖d‖ ≤ delta)
    (hgap : gapOn (taylorDecrement f p x) D ≤ epsilon * delta ^ p / (p ! : ℝ) + eta)
    (hrem : |f (x + d) - taylorModel f p x d| ≤
      L / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1))
    (hsmall : L * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * epsilon) :
    f x - 2 * epsilon * delta ^ p / (p ! : ℝ) - eta ≤ f (x + d) := by
  have hh := value_lower_bound_of_gap_and_remainder_of_bddAbove hb hd hgap hrem
  have hr := remainder_le_tolerance he (norm_nonneg d) hdn hsmall
  have heq : 2 * epsilon * delta ^ p / (p ! : ℝ) =
      epsilon * delta ^ p / (p ! : ℝ) + epsilon * delta ^ p / (p ! : ℝ) := by ring
  rw [heq]
  linarith only [hh, hr]

/-- A small Taylor gap ensures objective stability wherever the actual Lipschitz remainder
fits inside the same tolerance. The displacement set and its own radius remain explicit. -/
theorem value_lower_bound_of_gap_le {f : E → ℝ} {x d : E} {p : ℕ}
    {D : Set E} {L epsilon delta eta : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (he : 0 ≤ epsilon) (hdn : ‖d‖ ≤ delta)
    (hgap : gapOn (taylorDecrement f p x) D ≤ epsilon * delta ^ p / (p ! : ℝ) + eta)
    (hrem : |f (x + d) - taylorModel f p x d| ≤
      L / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1))
    (hsmall : L * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * epsilon) :
    f x - 2 * epsilon * delta ^ p / (p ! : ℝ) - eta ≤ f (x + d) :=
  value_lower_bound_of_gap_le_of_bddAbove
    (hD.image_of_continuousOn (continuous_taylorDecrement f p x).continuousOn).bddAbove
    hd he hdn hgap hrem hsmall

/-- Zero Taylor error gives the sharper single-tolerance bound on the full gap radius. -/
theorem value_lower_bound_of_gap_le_of_zero_remainder {f : E → ℝ} {x d : E} {p : ℕ}
    {D : Set E} {G : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (hgap : gapOn (taylorDecrement f p x) D ≤ G)
    (hrem : f (x + d) = taylorModel f p x d) : f x - G ≤ f (x + d) := by
  have hh := value_lower_bound_of_gap_and_remainder hD hd hgap
    (show |f (x + d) - taylorModel f p x d| ≤ 0 by rw [hrem]; simp)
  simpa only [sub_zero] using hh

omit [NormedSpace ℝ E] in
/-- Uniform positive model growth and a next-order error imply an isolated strict local
minimum of the true objective. No regularity of the model beyond these bounds is needed. -/
theorem isLocalMin_of_uniform_growth {f M : E → ℝ} {x : E} {p : ℕ}
    {c C R : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hmodel : ∀ s, ‖s‖ ≤ R → c * ‖s‖ ^ p ≤ M s - f x)
    (hrem : ∀ s, ‖s‖ ≤ R → |f (x + s) - M s| ≤ C * ‖s‖ ^ (p + 1)) :
    IsLocalMin f x ∧ ∃ r : ℝ, 0 < r ∧
      ∀ s : E, ‖s‖ < r → s ≠ 0 → f x < f (x + s) := by
  let r := min R (c / (C + 1))
  have hr : 0 < r := lt_min hR (div_pos hc (by linarith))
  have hstrict : ∀ s : E, ‖s‖ < r → s ≠ 0 → f x < f (x + s) := by
    intro s hs hs0
    have hsR : ‖s‖ ≤ R := (lt_min_iff.mp hs).1.le
    have hsC := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp (lt_min_iff.mp hs).2
    have hmul : C * ‖s‖ < c := by nlinarith [norm_nonneg s]
    have hpos := mul_pos (sub_pos.mpr hmul) (pow_pos (norm_pos_iff.mpr hs0) p)
    have hm := hmodel s hsR
    have he := (abs_le.mp (hrem s hsR)).1
    rw [pow_succ] at he
    nlinarith
  refine ⟨?_, r, hr, hstrict⟩
  change ∀ᶠ y in nhds x, f x ≤ f y
  apply Filter.mem_of_superset (ball_mem_nhds x hr)
  intro y hy
  change f x ≤ f y
  by_cases hyx : y = x
  · subst y
    exact le_rfl
  · have hd : ‖y - x‖ < r := by simpa only [mem_ball, dist_eq_norm] using hy
    have hh := hstrict (y - x) hd (sub_ne_zero.mpr hyx)
    simpa only [add_sub_cancel] using hh.le

/-- The next Taylor term has the expected homogeneous operator-norm bound. -/
theorem abs_taylorModel_succ_sub_le (f : E → ℝ) (p : ℕ) (x s : E) :
    |taylorModel f (p + 1) x s - taylorModel f p x s| ≤
      ‖iteratedFDeriv ℝ (p + 1) f x‖ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  rw [taylorModel_succ, add_sub_cancel_left, smul_eq_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((p + 1)! : ℝ)⁻¹)]
  have hbound : |iteratedFDeriv ℝ (p + 1) f x (fun _ => s)| ≤
      ‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1) := by
    simpa only [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using (iteratedFDeriv ℝ (p + 1) f x).le_opNorm (fun _ => s)
  calc
    _ ≤ ((p + 1)! : ℝ)⁻¹ *
        (‖iteratedFDeriv ℝ (p + 1) f x‖ * ‖s‖ ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- Uniform growth transfers to the actual next-order Taylor polynomial. -/
theorem taylorModel_isLocalMin_of_uniform_growth {f : E → ℝ} {x : E} {p : ℕ}
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hgrowth : ∀ s, ‖s‖ ≤ R → c * ‖s‖ ^ p ≤ taylorModel f p x s - f x) :
    IsLocalMin (taylorModel f (p + 1) x) 0 ∧ ∃ r : ℝ, 0 < r ∧
      ∀ s : E, ‖s‖ < r → s ≠ 0 →
        taylorModel f (p + 1) x 0 < taylorModel f (p + 1) x s := by
  simpa only [taylorModel_zero, zero_add] using
    isLocalMin_of_uniform_growth (f := taylorModel f (p + 1) x)
      (M := taylorModel f p x) (x := 0) hc
      (show 0 ≤ ‖iteratedFDeriv ℝ (p + 1) f x‖ / ((p + 1)! : ℝ) by positivity)
      hR (by simpa only [taylorModel_zero] using hgrowth)
      (fun s _ => by simpa only [zero_add] using abs_taylorModel_succ_sub_le f p x s)

end Optimization.TaylorCriticality
