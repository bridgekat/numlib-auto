/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.Newton
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.Analysis.Matrix.OperatorNorm
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Newton iteration with outer inverses

Section 8.5 of [benIsrael2003generalized] studies Newton iterations whose
correction uses an outer inverse of a Jacobian or an approximate
Jacobian. The limiting equation is the vanishing of that correction.

## Deviations from the source

* **Theorem 4**, Equation (66), evaluates both the inverse and the
  function at the limit. The proof uses continuity of the correction
  along the iterates, which does not require continuity of the inverse
  family itself.
* **Remark 1(b)** requires a nonzero outer inverse at the point whose
  Jacobian is bounded below.
* **Remark 2** obtains the uniform approximate derivative bound on
  a sufficiently small ball around the starting point.
-/

namespace BenIsraelGreville.Chapter08

open Filter Set
open scoped Topology BigOperators

section Definitions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Equation (64a)** of [benIsrael2003generalized], Chapter 8.
An outer inverse is the continuous linear map satisfying $TAT=T$. -/
def IsNewtonOuterInverse (A : E →L[ℝ] F) (T : F →L[ℝ] E) : Prop :=
  T.comp (A.comp T) = T

/-- An outer inverse followed by the forward map and the outer inverse
again acts as the original outer inverse on each input vector. -/
theorem isNewtonOuterInverse_iff {A : E →L[ℝ] F} {T : F →L[ℝ] E} :
    IsNewtonOuterInverse A T ↔ ∀ y, T (A (T y)) = T y :=
  ⟨fun h y => DFunLike.congr_fun h y, fun h => ContinuousLinearMap.ext h⟩

/-- The range of a continuous linear outer inverse is the closed fixed
space of the corresponding projection. -/
theorem IsNewtonOuterInverse.isClosed_range {A : E →L[ℝ] F} {T : F →L[ℝ] E}
    (hT : IsNewtonOuterInverse A T) : IsClosed (T.toLinearMap.range : Set E) := by
  have h : (T.toLinearMap.range : Set E) = {x | T (A x) = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact isNewtonOuterInverse_iff.mp hT y
    · intro hx
      exact ⟨A x, hx⟩
  rw [h]
  exact isClosed_eq (T.continuous.comp A.continuous) continuous_id

/-- **Equations (58)–(61), (65)** of [benIsrael2003generalized], Chapter 8.
The Newton iteration subtracts the correction supplied by the family
of linear maps. A constant family gives the modified Newton iteration. -/
def newtonIterate (f : E → F) (T : E → F →L[ℝ] E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => let x := newtonIterate f T x₀ k
    x - T x (f x)

/-- The generalized Newton iteration starts at the given point. -/
@[simp]
theorem newtonIterate_zero (f : E → F) (T : E → F →L[ℝ] E) (x₀ : E) :
    newtonIterate f T x₀ 0 = x₀ := rfl

/-- Each generalized Newton step subtracts the current correction. -/
theorem newtonIterate_succ (f : E → F) (T : E → F →L[ℝ] E) (x₀ : E) (k : ℕ) :
    newtonIterate f T x₀ (k + 1) =
      newtonIterate f T x₀ k - T (newtonIterate f T x₀ k) (f (newtonIterate f T x₀ k)) := rfl

/-- **Equations (68), (77)** of [benIsrael2003generalized], Chapter 8.
After a step from $v$ to $u$, the next displacement is controlled by the
linearization remainder at $v$ and by the change of the outer inverse. -/
theorem newtonDisplacement_eq (f : E → F) (A : E → E →L[ℝ] F) (T : E → F →L[ℝ] E)
    {u v : E} (hu : u = v - T v (f v)) (hT : IsNewtonOuterInverse (A v) (T v)) :
    -T u (f u) =
      -T v (f u - f v - A v (u - v)) + (T v - T u) (f u) := by
  have hdiff : u - v = -T v (f v) := by rw [hu]; abel
  have hfix : T v (A v (u - v)) = u - v := by
    rw [hdiff, map_neg, map_neg, isNewtonOuterInverse_iff.mp hT]
  rw [map_sub, map_sub, hfix, hdiff, sub_apply]
  abel

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 8.
A Lipschitz derivative on a convex set gives the quadratic first-order
Taylor remainder with the factor $M/2$. -/
theorem exercise_8_13 {f : E → F} {J : E → E →L[ℝ] F} {C : Set E} {M : ℝ}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, HasFDerivAt f (J x) x)
    (hLip : ∀ u ∈ C, ∀ v ∈ C, ‖J u - J v‖ ≤ M * ‖u - v‖)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C) :
    ‖f u - f v - J v (u - v)‖ ≤ M / 2 * ‖u - v‖ ^ 2 :=
  Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hC hJ hv hu
    (fun z hz => hLip z hz v hv)

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 8.
The same remainder bound holds for derivatives taken within the
convex domain. The proof differentiates along the closed segment. -/
theorem exercise_8_13_within {f : E → F} {J : E → E →L[ℝ] F} {C : Set E} {M : ℝ}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, HasFDerivWithinAt f (J x) C x)
    (hLip : ∀ u ∈ C, ∀ v ∈ C, ‖J u - J v‖ ≤ M * ‖u - v‖)
    {u v : E} (hu : u ∈ C) (hv : v ∈ C) :
    ‖f u - f v - J v (u - v)‖ ≤ M / 2 * ‖u - v‖ ^ 2 := by
  let L (t : ℝ) := v + t • (u - v)
  let g (t : ℝ) := f (L t) - f v - t • J v (u - v)
  let g' (t : ℝ) := (J (L t) - J v) (u - v)
  have hL : MapsTo L (Icc (0 : ℝ) 1) C := by
    intro t ht
    have he : L t = (1 - t) • v + t • u := by dsimp only [L]; module
    rw [he]
    exact hC hv hu (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc 0 1) t := by
    intro t ht
    have hLine : HasDerivAt L (u - v) t := by
      simpa only [L, id_eq, one_smul] using ((hasDerivAt_id t).smul_const (u - v)).const_add v
    have h₁ := (hJ (L t) (hL ht)).comp_hasDerivWithinAt t hLine.hasDerivWithinAt hL
    have h₂ : HasDerivAt (fun a : ℝ => a • J v (u - v)) (J v (u - v)) t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const (J v (u - v))
    have he : ((fun a : ℝ => f (L a) - f v) - fun a : ℝ => a • J v (u - v)) = g := rfl
    simpa only [Function.comp_apply, he, g', sub_apply] using
      (h₁.sub_const (f v)).sub h₂.hasDerivWithinAt
  let c := M * ‖u - v‖ ^ 2
  have hB (t : ℝ) : HasDerivAt (fun a : ℝ => c * (a ^ 2 / 2)) (c * t) t := by
    have h : HasDerivAt (fun a : ℝ => a ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    exact h.const_mul c
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖g' t‖ ≤ c * t := by
    intro t ht
    have hmem : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hdist : ‖L t - v‖ = t * ‖u - v‖ := by
      rw [show L t - v = t • (u - v) by dsimp only [L]; abel,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      _ ≤ ‖J (L t) - J v‖ * ‖u - v‖ := (J (L t) - J v).le_opNorm _
      _ ≤ M * ‖L t - v‖ * ‖u - v‖ :=
        mul_le_mul_of_nonneg_right (hLip _ (hL hmem) _ hv) (norm_nonneg _)
      _ = _ := by rw [hdist]; dsimp only [c]; ring
  have hzero : ‖g 0‖ ≤ c * ((0 : ℝ) ^ 2 / 2) := by simp [g, L]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (f' := g') (a := 0) (b := 1)
    (fun t ht => (hg t ht).continuousWithinAt)
    (fun t ht => by
      apply (hg t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      have hUpper : Iio (1 : ℝ) ∈ 𝓝[Ici t] t := nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
      filter_upwards [self_mem_nhdsWithin, hUpper] with w hw hUp
      exact ⟨ht.1.trans (show t ≤ w from hw), (show w < 1 from hUp).le⟩)
    hzero hB hb (Set.right_mem_Icc.2 zero_le_one)
  have hOne : L 1 = u := by
    dsimp only [L]
    rw [one_smul]
    abel
  calc
    ‖f u - f v - J v (u - v)‖ = ‖g 1‖ := by simp [g, hOne]
    _ ≤ c * ((1 : ℝ) ^ 2 / 2) := h
    _ = _ := by dsimp only [c]; ring

/-- **Equation (61)** of [benIsrael2003generalized], Chapter 8.
Using the ordinary inverse gives the library's classical Newton iterates. -/
theorem newtonIterate_eq_classical (f : E → F) (J : E → E →L[ℝ] F) (x₀ : E) (k : ℕ) :
    newtonIterate f (fun x => (J x).inverse) x₀ k = Newton.iterate f J x₀ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [newtonIterate_succ, Newton.iterate_succ, ih, Newton.step]

/-- **Equations (59), (73)** of [benIsrael2003generalized], Chapter 8.
Freezing an invertible derivative gives the chord method. -/
theorem newtonIterate_eq_chord (f : E → F) (A : E ≃L[ℝ] F) (x₀ : E) (k : ℕ) :
    newtonIterate f (fun _ => A.symm.toContinuousLinearMap) x₀ k =
      Newton.chordIterate f A x₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [newtonIterate_succ, Newton.chordIterate_succ, ih, Newton.chordStep]
    rfl

end Definitions

section Scalar

/-- The inverse of multiplication by a scalar derivative, with the
zero map at a vanishing derivative. -/
noncomputable def scalarNewtonInverse (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a⁻¹ • ContinuousLinearMap.id ℝ ℝ

/-- The scalar inverse used in Newton's method divides by the derivative. -/
@[simp]
theorem scalarNewtonInverse_apply (a y : ℝ) : scalarNewtonInverse a y = y / a := by
  simp [scalarNewtonInverse, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **Equation (58)** of [benIsrael2003generalized], Chapter 8.
In one variable the correction divides by the current derivative. -/
theorem scalarNewtonIterate_succ (f : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    let x := newtonIterate f (fun y => scalarNewtonInverse (deriv f y)) x₀
    x (k + 1) = x k - f (x k) / deriv f (x k) := by
  dsimp only
  rw [newtonIterate_succ, scalarNewtonInverse_apply]

/-- **Equation (59)** of [benIsrael2003generalized], Chapter 8.
Modified Newton divides by the derivative at the starting point. -/
theorem scalarModifiedNewtonIterate_succ (f : ℝ → ℝ) (x₀ : ℝ) (k : ℕ) :
    let x := newtonIterate f (fun _ => scalarNewtonInverse (deriv f x₀)) x₀
    x (k + 1) = x k - f (x k) / deriv f x₀ := by
  dsimp only
  rw [newtonIterate_succ, scalarNewtonInverse_apply]

end Scalar

section Majorants

variable {E : Type*} [NormedAddCommGroup E]

private theorem sum_geom_le {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) (m : ℕ) :
    (∑ i ∈ Finset.range m, a ^ i) ≤ 1 / (1 - a) := by
  calc
    _ ≤ ∑' i : ℕ, a ^ i :=
      (summable_geometric_of_lt_one ha ha₁).sum_le_tsum _ (fun i _ => pow_nonneg ha i)
    _ = _ := by rw [tsum_geometric_of_lt_one ha ha₁, one_div]

private theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ (2 : ℕ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private theorem dyadic_exponent_le (n i : ℕ) :
    (2 : ℕ) ^ n - 1 + 2 ^ n * i ≤ 2 ^ (n + i) - 1 := by
  have h₁ := Nat.mul_le_mul_left (2 ^ n) (succ_le_two_pow i)
  have h₂ : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  rw [pow_add, Nat.mul_add, Nat.mul_one] at *
  omega

private theorem dist_le_majorant_tail {u : ℕ → E} {d : ℕ → ℝ}
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ d j) (n m : ℕ) :
    dist (u (n + m)) (u n) ≤ ∑ i ∈ Finset.range m, d (n + i) := by
  rw [dist_comm]
  refine (dist_le_range_sum_dist (fun i => u (n + i)) m).trans (Finset.sum_le_sum ?_)
  intro i _
  simpa only [dist_eq_norm, norm_sub_rev, Nat.add_assoc] using hstep (n + i)

private theorem norm_sub_limit_le_of_tail {u : ℕ → E} {z : E} {n : ℕ} {R : ℝ}
    (hlim : Tendsto u atTop (𝓝 z)) (hfar : ∀ m, dist (u (n + m)) (u n) ≤ R) :
    ‖u n - z‖ ≤ R := by
  have hshift : Tendsto (fun m : ℕ => n + m) atTop atTop := by
    rw [show (fun m : ℕ => n + m) = (fun m => m + n) from funext (Nat.add_comm n)]
    exact tendsto_add_atTop_nat n
  have hdlim : Tendsto (fun m => dist (u (n + m)) (u n)) atTop (𝓝 (dist z (u n))) :=
    (hlim.comp hshift).dist tendsto_const_nhds
  simpa only [dist_eq_norm, norm_sub_rev] using
    le_of_tendsto hdlim (Eventually.of_forall hfar)

private theorem stay_in_ball_of_majorant {u : ℕ → E} {d : ℕ → ℝ} {r R : ℝ}
    (hR : R < r) (hSum : ∀ n, ∑ j ∈ Finset.range n, d j ≤ R)
    (h₀ : ‖u 1 - u 0‖ ≤ d 0)
    (hNext : ∀ k, u k ∈ Metric.ball (u 0) r → u (k + 1) ∈ Metric.ball (u 0) r →
      ‖u (k + 1) - u k‖ ≤ d k → ‖u (k + 2) - u (k + 1)‖ ≤ d (k + 1)) :
    (∀ k, dist (u k) (u 0) ≤ R) ∧
      (∀ k, u k ∈ Metric.ball (u 0) r) ∧ (∀ k, ‖u (k + 1) - u k‖ ≤ d k) := by
  have h (k : ℕ) : dist (u k) (u 0) ≤ ∑ j ∈ Finset.range k, d j ∧
      ‖u (k + 1) - u k‖ ≤ d k := by
    induction k with
    | zero => exact ⟨by simp, h₀⟩
    | succ k ih =>
      have hdist : dist (u (k + 1)) (u 0) ≤ ∑ j ∈ Finset.range (k + 1), d j := by
        rw [Finset.sum_range_succ, add_comm (∑ j ∈ Finset.range k, d j) (d k)]
        exact (dist_triangle _ (u k) _).trans (add_le_add
          (by simpa only [dist_eq_norm] using ih.2) ih.1)
      exact ⟨hdist, hNext k (Metric.mem_ball.mpr ((ih.1.trans (hSum k)).trans_lt hR))
        (Metric.mem_ball.mpr ((hdist.trans (hSum (k + 1))).trans_lt hR)) ih.2⟩
  refine ⟨fun k => (h k).1.trans (hSum k), fun k => ?_, fun k => (h k).2⟩
  exact Metric.mem_ball.mpr (((h k).1.trans (hSum k)).trans_lt hR)

variable [CompleteSpace E]

private theorem tendsto_of_majorant {u : ℕ → E} {d : ℕ → ℝ} {r R : ℝ}
    (hR : R < r) (hSum : ∀ n, ∑ j ∈ Finset.range n, d j ≤ R)
    (hSummable : Summable d) (h₀ : ‖u 1 - u 0‖ ≤ d 0)
    (hNext : ∀ k, u k ∈ Metric.ball (u 0) r → u (k + 1) ∈ Metric.ball (u 0) r →
      ‖u (k + 1) - u k‖ ≤ d k → ‖u (k + 2) - u (k + 1)‖ ≤ d (k + 1)) :
    ∃ z ∈ Metric.ball (u 0) r, Tendsto u atTop (𝓝 z) ∧
      (∀ k, u k ∈ Metric.ball (u 0) r) ∧ (∀ k, ‖u (k + 1) - u k‖ ≤ d k) := by
  obtain ⟨hdist, hball, hstep⟩ := stay_in_ball_of_majorant hR hSum h₀ hNext
  have hs : Summable fun k => dist (u k) (u (k + 1)) :=
    hSummable.of_nonneg_of_le (fun _ => dist_nonneg)
      (fun k => by simpa only [dist_eq_norm, norm_sub_rev] using hstep k)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hs)
  have hdist' : dist z (u 0) ≤ R :=
    le_of_tendsto (hz.dist tendsto_const_nhds) (Eventually.of_forall hdist)
  exact ⟨z, Metric.mem_ball.mpr (hdist'.trans_lt hR), hz, hball, hstep⟩

private theorem geometric_convergence_of_increment {u : ℕ → E} {r δ a : ℝ}
    (ha : 0 ≤ a) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hR : a / (1 - δ) < r) (h₀ : ‖u 1 - u 0‖ ≤ a)
    (hNext : ∀ k, u k ∈ Metric.ball (u 0) r → u (k + 1) ∈ Metric.ball (u 0) r →
      ‖u (k + 2) - u (k + 1)‖ ≤ δ * ‖u (k + 1) - u k‖) :
    ∃ z ∈ Metric.ball (u 0) r, Tendsto u atTop (𝓝 z) ∧
      (∀ k, u k ∈ Metric.ball (u 0) r) ∧
      (∀ k, ‖u (k + 1) - u k‖ ≤ a * δ ^ k) ∧
      ∀ k, ‖u k - z‖ ≤ a * δ ^ k / (1 - δ) := by
  let d (n : ℕ) := a * δ ^ n
  have hSum (m : ℕ) : ∑ j ∈ Finset.range m, d j ≤ a / (1 - δ) := by
    change (∑ j ∈ Finset.range m, a * δ ^ j) ≤ _
    rw [← Finset.mul_sum, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (sum_geom_le hδ₀ hδ₁ m) ha
  have hSummable : Summable d := (summable_geometric_of_lt_one hδ₀ hδ₁).mul_left a
  have hstart : ‖u 1 - u 0‖ ≤ d 0 := by simpa only [d, pow_zero, mul_one] using h₀
  have hmajor : ∀ k, u k ∈ Metric.ball (u 0) r → u (k + 1) ∈ Metric.ball (u 0) r →
      ‖u (k + 1) - u k‖ ≤ d k → ‖u (k + 2) - u (k + 1)‖ ≤ d (k + 1) := by
    intro k hk hks hs
    calc
      _ ≤ δ * ‖u (k + 1) - u k‖ := hNext k hk hks
      _ ≤ δ * d k := mul_le_mul_of_nonneg_left hs hδ₀
      _ = d (k + 1) := by dsimp only [d]; rw [pow_succ]; ring
  obtain ⟨z, hz, hlim, hball, hstep⟩ :=
    tendsto_of_majorant hR hSum hSummable hstart hmajor
  refine ⟨z, hz, hlim, hball, hstep, fun n => norm_sub_limit_le_of_tail hlim (fun m => ?_)⟩
  calc
    _ ≤ ∑ i ∈ Finset.range m, d (n + i) := dist_le_majorant_tail hstep n m
    _ = d n * ∑ i ∈ Finset.range m, δ ^ i := by
      rw [Finset.mul_sum]
      simp only [d, pow_add, mul_assoc]
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (sum_geom_le hδ₀ hδ₁ m)
        (mul_nonneg ha (pow_nonneg hδ₀ n))

omit [CompleteSpace E] in
/-- **Theorem 4** of [benIsrael2003generalized], Chapter 8.
A convergent sequence whose successive displacements satisfy the
quadratic estimate in (68) also has an eventual quadratic error bound. -/
theorem eventually_error_le_sq_of_quadratic_increments {u : ℕ → E} {z : E} {K : ℝ}
    (hK : 0 ≤ K) (hlim : Tendsto u atTop (𝓝 z))
    (hstep : ∀ k, ‖u (k + 2) - u (k + 1)‖ ≤ K * ‖u (k + 1) - u k‖ ^ 2) :
    ∀ᶠ k in atTop, ‖u (k + 1) - z‖ ≤ (8 * K) * ‖u k - z‖ ^ 2 := by
  let d (k : ℕ) := ‖u (k + 1) - u k‖
  have hd (k : ℕ) : 0 ≤ d k := norm_nonneg _
  have hrec (k : ℕ) : d (k + 1) ≤ K * d k ^ 2 := hstep k
  have hdlim : Tendsto (fun k => K * d k) atTop (𝓝 0) := by
    have h := ((hlim.comp (tendsto_add_atTop_nat 1)).sub hlim).norm.const_mul K
    simpa only [d, Function.comp_apply, sub_self, norm_zero, mul_zero] using h
  filter_upwards [hdlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with n hn
  have hquarter : K * d n ^ 2 ≤ (1 / 4) * d n := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hn (hd n)
  have hd₁ : d (n + 1) ≤ d n := by linarith [hrec n, hquarter, hd n]
  have htail (i : ℕ) : d (n + 1 + i) ≤ d (n + 1) * (1 / 2) ^ i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hib : d (n + 1 + i) ≤ d n := by
        refine (ih.trans ?_).trans hd₁
        calc
          _ ≤ d (n + 1) * 1 := mul_le_mul_of_nonneg_left
            (pow_le_one₀ (by norm_num) (by norm_num)) (hd (n + 1))
          _ = _ := mul_one _
      calc
        _ ≤ K * d (n + 1 + i) ^ 2 := hrec (n + 1 + i)
        _ ≤ (K * d n) * d (n + 1 + i) := by
          rw [pow_two, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hib hK) (hd _)
        _ ≤ (1 / 2) * d (n + 1 + i) :=
          mul_le_mul_of_nonneg_right (hn.trans (by norm_num)) (hd _)
        _ ≤ (1 / 2) * (d (n + 1) * (1 / 2) ^ i) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hsum : ‖u (n + 1) - z‖ ≤ 2 * d (n + 1) := by
    refine norm_sub_limit_le_of_tail hlim (fun m => ?_)
    calc
      _ ≤ ∑ i ∈ Finset.range m, d (n + 1 + i) :=
        dist_le_majorant_tail (fun _ => le_rfl) (n + 1) m
      _ ≤ ∑ i ∈ Finset.range m, d (n + 1) * (1 / 2) ^ i :=
        Finset.sum_le_sum (fun i _ => htail i)
      _ = d (n + 1) * ∑ i ∈ Finset.range m, (1 / 2) ^ i := (Finset.mul_sum ..).symm
      _ ≤ d (n + 1) * (1 / (1 - 1 / 2)) :=
        mul_le_mul_of_nonneg_left (sum_geom_le (by norm_num) (by norm_num) m) (hd _)
      _ = _ := by norm_num; ring
  have herr : ‖u (n + 1) - z‖ ≤ 2 * K * d n ^ 2 := by
    linarith [hsum, hrec n]
  have herr' : ‖u (n + 1) - z‖ ≤ d n / 2 := by
    linarith [hsum, hrec n, hquarter]
  have htri : d n ≤ ‖u (n + 1) - z‖ + ‖u n - z‖ := by
    calc
      d n = ‖(u (n + 1) - z) + (z - u n)‖ := by dsimp only [d]; congr 1; abel
      _ ≤ _ := by rw [norm_sub_rev (u n) z]; exact norm_add_le _ _
  have hde : d n ≤ 2 * ‖u n - z‖ := by linarith
  calc
    _ ≤ 2 * K * d n ^ 2 := herr
    _ ≤ 2 * K * (2 * ‖u n - z‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hd n) hde 2) (mul_nonneg (by norm_num) hK)
    _ = _ := by ring

end Majorants

section Convergence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem correction_zero_of_tendsto {f : E → F} {T : E → F →L[ℝ] E} {s : Set E}
    {u : ℕ → E} {z : E} {N : ℝ} {q : ℕ} (hq : q ≠ 0)
    (hz : z ∈ s) (hu : ∀ k, u k ∈ s)
    (hlim : Tendsto u atTop (𝓝 z)) (hf : Tendsto (fun k => f (u k)) atTop (𝓝 (f z)))
    (hT : ∀ v ∈ s, ∀ w ∈ s, ‖(T v - T w) (f w)‖ ≤ N * ‖v - w‖ ^ q)
    (hrec : ∀ k, u (k + 1) = u k - T (u k) (f (u k))) :
    T z (f z) = 0 := by
  have h₁ := hlim.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun k => T (u k) (f (u k))) atTop (𝓝 0) := by
    have he (k : ℕ) : u k - u (k + 1) = T (u k) (f (u k)) := by rw [hrec, sub_sub_cancel]
    simpa only [he, sub_self, Function.comp_apply] using hlim.sub h₁
  have hcomp₁ :
      Tendsto (fun k => N * ‖z - u k‖ ^ q) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := z)).sub hlim).norm.pow q
    simpa only [sub_self, norm_zero, zero_pow hq, mul_zero] using h.const_mul N
  have hcomp₂ :
      Tendsto (fun k => ‖T z‖ * ‖f (u k) - f z‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (hf.sub (tendsto_const_nhds (x := f z))).norm.const_mul ‖T z‖
  have htail :
      Tendsto (fun k => N * ‖z - u k‖ ^ q + ‖T z‖ * ‖f (u k) - f z‖) atTop (𝓝 0) := by
    simpa only [add_zero] using hcomp₁.add hcomp₂
  have hdiff (k : ℕ) :
      ‖T (u k) (f (u k)) - T z (f z)‖ ≤ N * ‖z - u k‖ ^ q + ‖T z‖ * ‖f (u k) - f z‖ := by
    have he : T (u k) (f (u k)) - T z (f z) =
        T z (f (u k) - f z) - (T z - T (u k)) (f (u k)) := by
      rw [map_sub, sub_apply]
      abel
    rw [he, add_comm]
    exact (norm_sub_le _ _).trans (add_le_add ((T z).le_opNorm _) (hT z hz (u k) (hu k)))
  have hn : Tendsto (fun k => ‖T (u k) (f (u k)) - T z (f z)‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => norm_nonneg _) hdiff
  have ht : Tendsto (fun k => T (u k) (f (u k))) atTop (𝓝 (T z (f z))) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn
  exact tendsto_nhds_unique ht hzero

private theorem norm_newtonIncrement_le {f : E → F} {J : E → E →L[ℝ] F}
    {T : E → F →L[ℝ] E} {u v : E} {M N : ℝ} {q : ℕ}
    (hu : u = v - T v (f v)) (hT : IsNewtonOuterInverse (J v) (T v))
    (hRem : ‖f u - f v - J v (u - v)‖ ≤ M * ‖u - v‖ ^ q)
    (hVar : ‖(T v - T u) (f u)‖ ≤ N * ‖u - v‖ ^ q) :
    ‖u - T u (f u) - u‖ ≤ (M * ‖T v‖ + N) * ‖u - v‖ ^ q := by
  have he : u - T u (f u) - u = -T u (f u) := by abel
  rw [he, newtonDisplacement_eq f J T hu hT]
  calc
    _ ≤ ‖-T v (f u - f v - J v (u - v))‖ + ‖(T v - T u) (f u)‖ :=
      norm_add_le _ _
    _ ≤ ‖T v‖ * (M * ‖u - v‖ ^ q) + N * ‖u - v‖ ^ q := by
      rw [norm_neg]
      exact add_le_add (((T v).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hRem (norm_nonneg _))) hVar
    _ = _ := by ring

variable [CompleteSpace E]

/-- **Theorem 4**, Equations (63)–(69) of [benIsrael2003generalized], Chapter 8.
A Lipschitz Jacobian and the quadratic bound on changes in the outer
inverse give a limit in the open ball, a vanishing correction, and the
dyadic a priori error bound. The initial correction itself may be
bounded by $\alpha$ instead of using the product of its two norms. -/
theorem theorem_4 {f : E → F} {J : E → E →L[ℝ] F} {T : E → F →L[ℝ] E}
    {x₀ : E} {r M N K α : ℝ}
    (hJ : ∀ x ∈ Metric.ball x₀ r, HasFDerivAt f (J x) x)
    (hLip : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r, ‖J u - J v‖ ≤ M * ‖u - v‖)
    (hT : ∀ x ∈ Metric.ball x₀ r, IsNewtonOuterInverse (J x) (T x))
    (h₀ : ‖T x₀ (f x₀)‖ ≤ α)
    (hVar : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖(T u - T v) (f v)‖ ≤ N * ‖u - v‖ ^ 2)
    (hK : ∀ u ∈ Metric.ball x₀ r, M / 2 * ‖T u‖ + N ≤ K)
    (hK₀ : 0 ≤ K) (hh : α * K < 1) (hrad : α / (1 - α * K) < r) :
    let x := newtonIterate f T x₀
    let h := α * K
    ∃ z ∈ Metric.ball x₀ r, Tendsto x atTop (𝓝 z) ∧ T z (f z) = 0 ∧
      (∀ k, x k ∈ Metric.ball x₀ r) ∧
      (∀ k, ‖x (k + 2) - x (k + 1)‖ ≤ K * ‖x (k + 1) - x k‖ ^ 2) ∧
      (∀ k, ‖x (k + 1) - x k‖ ≤ α * h ^ ((2 : ℕ) ^ k - 1)) ∧
      ∀ k, ‖x k - z‖ ≤ α * h ^ ((2 : ℕ) ^ k - 1) / (1 - h ^ ((2 : ℕ) ^ k)) := by
  let x := newtonIterate f T x₀
  let h := α * K
  let d (k : ℕ) := α * h ^ ((2 : ℕ) ^ k - 1)
  have hα : 0 ≤ α := (norm_nonneg _).trans h₀
  have hh₀ : 0 ≤ h := mul_nonneg hα hK₀
  have hd₀ (k : ℕ) : 0 ≤ d k := mul_nonneg hα (pow_nonneg hh₀ _)
  have hGeom (k : ℕ) : d k ≤ α * h ^ k :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh₀ hh.le
      (show k ≤ (2 : ℕ) ^ k - 1 by have := succ_le_two_pow k; omega)) hα
  have hSummable : Summable d :=
    ((summable_geometric_of_lt_one hh₀ hh).mul_left α).of_nonneg_of_le hd₀ hGeom
  have hSum (m : ℕ) : ∑ j ∈ Finset.range m, d j ≤ α / (1 - h) := by
    calc
      _ ≤ ∑ j ∈ Finset.range m, α * h ^ j := Finset.sum_le_sum (fun j _ => hGeom j)
      _ = α * ∑ j ∈ Finset.range m, h ^ j := (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (sum_geom_le hh₀ hh m) hα
  have hrec (k : ℕ) : x (k + 1) = x k - T (x k) (f (x k)) := rfl
  have hstart : ‖x 1 - x 0‖ ≤ d 0 := by
    change ‖x₀ - T x₀ (f x₀) - x₀‖ ≤ d 0
    rw [show x₀ - T x₀ (f x₀) - x₀ = -T x₀ (f x₀) by abel, norm_neg]
    simpa only [d, pow_zero, Nat.sub_self, mul_one] using h₀
  have hdsucc (k : ℕ) : K * d k ^ 2 = d (k + 1) := by
    have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
    have he : (2 : ℕ) ^ (k + 1) - 1 = ((2 : ℕ) ^ k - 1) * 2 + 1 := by
      rw [pow_succ]; omega
    dsimp only [d]
    rw [he, pow_add, pow_mul, pow_one]
    dsimp only [h]
    ring
  have hQuad (k : ℕ) (hk : x k ∈ Metric.ball x₀ r) (hks : x (k + 1) ∈ Metric.ball x₀ r) :
      ‖x (k + 2) - x (k + 1)‖ ≤ K * ‖x (k + 1) - x k‖ ^ 2 := by
    rw [hrec (k + 1)]
    have hRem := exercise_8_13 (convex_ball x₀ r) hJ hLip hks hk
    have hInc := norm_newtonIncrement_le (hrec k) (hT _ hk) hRem
      (by simpa only [norm_sub_rev] using hVar _ hk _ hks)
    exact hInc.trans (mul_le_mul_of_nonneg_right (hK _ hk) (sq_nonneg _))
  have hnext (k : ℕ) (hk : x k ∈ Metric.ball x₀ r) (hks : x (k + 1) ∈ Metric.ball x₀ r)
      (hs : ‖x (k + 1) - x k‖ ≤ d k) : ‖x (k + 2) - x (k + 1)‖ ≤ d (k + 1) := by
    exact (hQuad k hk hks).trans
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) hK₀).trans_eq
        (hdsucc k))
  have hmajor := tendsto_of_majorant (u := x) (d := d) (R := α / (1 - h)) hrad hSum hSummable
    hstart hnext
  obtain ⟨z, hz, hlim, hball, hstep⟩ := hmajor
  have hf := ((hJ z hz).continuousAt.tendsto.comp hlim)
  have hzero := correction_zero_of_tendsto (q := 2) (by decide) hz hball hlim hf hVar hrec
  refine ⟨z, hz, hlim, hzero, hball, fun k => hQuad k (hball k) (hball (k + 1)),
    hstep, fun n => ?_⟩
  have hq : h ^ ((2 : ℕ) ^ n) < 1 :=
    pow_lt_one₀ hh₀ hh (ne_of_gt (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hfar (m : ℕ) : dist (x (n + m)) (x n) ≤ d n / (1 - h ^ ((2 : ℕ) ^ n)) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, d (n + i) := dist_le_majorant_tail hstep n m
      _ ≤ ∑ i ∈ Finset.range m, d n * (h ^ ((2 : ℕ) ^ n)) ^ i := by
        apply Finset.sum_le_sum
        intro i _
        change α * h ^ ((2 : ℕ) ^ (n + i) - 1) ≤
          (α * h ^ ((2 : ℕ) ^ n - 1)) * (h ^ ((2 : ℕ) ^ n)) ^ i
        rw [← pow_mul, mul_assoc, ← pow_add]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hh₀ hh.le
          (dyadic_exponent_le n i)) hα
      _ = d n * ∑ i ∈ Finset.range m, (h ^ ((2 : ℕ) ^ n)) ^ i := (Finset.mul_sum ..).symm
      _ ≤ _ := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (sum_geom_le (pow_nonneg hh₀ _) hq _) (hd₀ n)
  exact norm_sub_limit_le_of_tail hlim hfar

omit [CompleteSpace E] in
private theorem tendsto_f_of_linearization {f : E → F} {u : ℕ → E} {z : E}
    {A : E →L[ℝ] F} {ε : ℝ} (hlim : Tendsto u atTop (𝓝 z))
    (hRem : ∀ k, ‖f (u k) - f z - A (u k - z)‖ ≤ ε * ‖u k - z‖) :
    Tendsto (fun k => f (u k)) atTop (𝓝 (f z)) := by
  have hb (k : ℕ) : ‖f (u k) - f z‖ ≤ (ε + ‖A‖) * ‖u k - z‖ := by
    have he : f (u k) - f z = (f (u k) - f z - A (u k - z)) + A (u k - z) := by
      exact (sub_add_cancel _ _).symm
    rw [he, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hRem k) (A.le_opNorm _))
  have ht : Tendsto (fun k => (ε + ‖A‖) * ‖u k - z‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (hlim.sub (tendsto_const_nhds (x := z))).norm.const_mul (ε + ‖A‖)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => norm_nonneg _) hb)

/-- **Exercise 14**, Equations (78)–(79) of [benIsrael2003generalized],
Chapter 8. Outer inverses of approximate Jacobians give linear
convergence to a point with zero correction. -/
theorem exercise_8_14 {f : E → F} {A : E → E →L[ℝ] F} {T : E → F →L[ℝ] E}
    {x₀ : E} {r ε η δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hRem : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖f u - f v - A v (u - v)‖ ≤ ε * ‖u - v‖)
    (hT : ∀ u ∈ Metric.ball x₀ r, IsNewtonOuterInverse (A u) (T u))
    (hVar : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖(T u - T v) (f v)‖ ≤ η * ‖u - v‖)
    (hNorm : ∀ u ∈ Metric.ball x₀ r, ε * ‖T u‖ + η ≤ δ)
    (h₀ : ‖T x₀‖ * ‖f x₀‖ < (1 - δ) * r) :
    let x := newtonIterate f T x₀
    let a := ‖T x₀‖ * ‖f x₀‖
    ∃ z ∈ Metric.ball x₀ r, Tendsto x atTop (𝓝 z) ∧ T z (f z) = 0 ∧
      (∀ k, x k ∈ Metric.ball x₀ r) ∧
      (∀ k, ‖x (k + 1) - x k‖ ≤ a * δ ^ k) ∧
      ∀ k, ‖x k - z‖ ≤ a * δ ^ k / (1 - δ) := by
  let x := newtonIterate f T x₀
  let a := ‖T x₀‖ * ‖f x₀‖
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hR : a / (1 - δ) < r := (div_lt_iff₀ (by linarith)).mpr (mul_comm r _ ▸ h₀)
  have hrec (k : ℕ) : x (k + 1) = x k - T (x k) (f (x k)) := rfl
  have hstart : ‖x 1 - x 0‖ ≤ a := by
    change ‖x₀ - T x₀ (f x₀) - x₀‖ ≤ a
    rw [show x₀ - T x₀ (f x₀) - x₀ = -T x₀ (f x₀) by abel, norm_neg]
    exact (T x₀).le_opNorm _
  have hNext (k : ℕ) (hk : x k ∈ Metric.ball x₀ r) (hks : x (k + 1) ∈ Metric.ball x₀ r) :
      ‖x (k + 2) - x (k + 1)‖ ≤ δ * ‖x (k + 1) - x k‖ := by
    rw [hrec (k + 1)]
    have hInc := norm_newtonIncrement_le (q := 1) (hrec k) (hT _ hk)
      (by simpa only [pow_one] using hRem _ hks _ hk)
      (by simpa only [pow_one, norm_sub_rev] using hVar _ hk _ hks)
    rw [pow_one] at hInc
    exact hInc.trans (mul_le_mul_of_nonneg_right (hNorm _ hk) (norm_nonneg _))
  obtain ⟨z, hz, hlim, hball, hstep, htail⟩ :=
    geometric_convergence_of_increment ha hδ₀ hδ₁ hR hstart hNext
  have hf := tendsto_f_of_linearization hlim (fun k => hRem _ (hball k) z hz)
  have hzero := correction_zero_of_tendsto (q := 1) (by decide) hz hball hlim hf
    (fun u hu v hv => by simpa only [pow_one] using hVar u hu v hv) hrec
  exact ⟨z, hz, hlim, hzero, hball, hstep, htail⟩

/-- **Theorem 5**, Equations (72)–(77) and Remark 3 of
[benIsrael2003generalized], Chapter 8. With one fixed outer inverse,
the approximate-derivative bound is needed only for differences
in its range. The iterates and the limit lie in the corresponding
affine space, and the increments obey a geometric bound. -/
theorem theorem_5 {f : E → F} {A : E →L[ℝ] F} {T : F →L[ℝ] E}
    {x₀ : E} {r ε δ : ℝ} (hT : IsNewtonOuterInverse A T)
    (hε : 0 ≤ ε) (hδ : ε * ‖T‖ = δ) (hδ₁ : δ < 1)
    (h₀ : ‖T‖ * ‖f x₀‖ < (1 - δ) * r)
    (hRem : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      u - v ∈ T.toLinearMap.range →
      ‖f u - f v - A (u - v)‖ ≤ ε * ‖u - v‖) :
    let x := newtonIterate f (fun _ => T) x₀
    ∃ z ∈ Metric.ball x₀ r, Tendsto x atTop (𝓝 z) ∧ T (f z) = 0 ∧
      z - x₀ ∈ T.toLinearMap.range ∧
      (∀ k, x k ∈ Metric.ball x₀ r ∧ x k - x₀ ∈ T.toLinearMap.range) ∧
      ∀ k, ‖x (k + 1) - x k‖ ≤ δ ^ k * (1 - δ) * r := by
  let x := newtonIterate f (fun _ => T) x₀
  let a := ‖T‖ * ‖f x₀‖
  have ha : 0 ≤ a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hδ₀ : 0 ≤ δ := hδ ▸ mul_nonneg hε (norm_nonneg _)
  have hR : a / (1 - δ) < r := (div_lt_iff₀ (by linarith)).mpr (mul_comm r _ ▸ h₀)
  have hrec (k : ℕ) : x (k + 1) = x k - T (f (x k)) := rfl
  have hstart : ‖x 1 - x 0‖ ≤ a := by
    change ‖x₀ - T (f x₀) - x₀‖ ≤ a
    rw [show x₀ - T (f x₀) - x₀ = -T (f x₀) by abel, norm_neg]
    exact T.le_opNorm _
  have hdiff (k : ℕ) : x (k + 1) - x k = -T (f (x k)) := by
    rw [hrec]
    abel
  have hdiff_range (k : ℕ) : x (k + 1) - x k ∈ T.toLinearMap.range := by
    rw [hdiff]
    exact T.toLinearMap.range.neg_mem ⟨f (x k), rfl⟩
  have hNext (k : ℕ) (hk : x k ∈ Metric.ball x₀ r) (hks : x (k + 1) ∈ Metric.ball x₀ r) :
      ‖x (k + 2) - x (k + 1)‖ ≤ δ * ‖x (k + 1) - x k‖ := by
    rw [hrec (k + 1)]
    have hInc := norm_newtonIncrement_le (f := f) (q := 1) (N := 0) (J := fun _ => A)
      (T := fun _ => T) (hrec k) hT
      (by simpa only [pow_one] using hRem _ hks _ hk (hdiff_range k))
      (by simp)
    simpa only [pow_one, hδ, add_zero] using hInc
  obtain ⟨z, hz, hlim, hball, hstep, _⟩ :=
    geometric_convergence_of_increment ha hδ₀ hδ₁ hR hstart hNext
  have hslice (k : ℕ) : x k - x₀ ∈ T.toLinearMap.range := by
    induction k with
    | zero =>
      change x₀ - x₀ ∈ T.toLinearMap.range
      rw [sub_self]
      exact T.toLinearMap.range.zero_mem
    | succ k ih =>
      have he : x (k + 1) - x₀ = (x (k + 1) - x k) + (x k - x₀) := by abel
      rw [he]
      exact T.toLinearMap.range.add_mem (hdiff_range k) ih
  have hZslice : z - x₀ ∈ T.toLinearMap.range :=
    hT.isClosed_range.mem_of_tendsto (hlim.sub tendsto_const_nhds) (Eventually.of_forall hslice)
  have hdist_range (k : ℕ) : x k - z ∈ T.toLinearMap.range := by
    have he : x k - z = (x k - x₀) - (z - x₀) := by abel
    rw [he]
    exact T.toLinearMap.range.sub_mem (hslice k) hZslice
  have hf := tendsto_f_of_linearization hlim (fun k => hRem _ (hball k) z hz (hdist_range k))
  have hzero : T (f z) = 0 :=
    correction_zero_of_tendsto (T := fun _ => T) (q := 1) (N := 0) (by decide)
      hz hball hlim hf (fun _ _ _ _ => by simp) hrec
  refine ⟨z, hz, hlim, hzero, hZslice, fun k => ⟨hball k, hslice k⟩, fun k => ?_⟩
  calc
    _ ≤ a * δ ^ k := hstep k
    _ ≤ ((1 - δ) * r) * δ ^ k := mul_le_mul_of_nonneg_right h₀.le (pow_nonneg hδ₀ _)
    _ = _ := by ring

end Convergence

section Remarks

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Remark 1(a)** of [benIsrael2003generalized], Chapter 8.
The product bound for a nonzero initial outer inverse controls the
size of the initial function value. -/
theorem initialResidual_norm_lt {T : F →L[ℝ] E} {y : F} {α : ℝ}
    (hT : T ≠ 0) (h : ‖T‖ * ‖y‖ < α) : ‖y‖ < α / ‖T‖ := by
  apply (lt_div_iff₀ (norm_pos_iff.mpr hT)).mpr
  rwa [mul_comm]

/-- **Remark 1(b)** of [benIsrael2003generalized], Chapter 8.
The inverse norm bound gives a lower bound on the Jacobian norm
at every point with a nonzero outer inverse. -/
theorem jacobian_norm_lower_of_outerInverse {A : E →L[ℝ] F} {T : F →L[ℝ] E}
    {M N K : ℝ} (hT : IsNewtonOuterInverse A T) (hT₀ : T ≠ 0) (hM : 0 < M)
    (h : M / 2 * ‖T‖ + N ≤ K) : M / (2 * (K - N)) ≤ ‖A‖ := by
  have hpos : 0 < ‖T‖ := norm_pos_iff.mpr hT₀
  have hcomp : ‖T‖ ≤ ‖T‖ * (‖A‖ * ‖T‖) := by
    calc
      _ = ‖T.comp (A.comp T)‖ := congrArg norm hT.symm
      _ ≤ ‖T‖ * ‖A.comp T‖ := T.opNorm_comp_le _
      _ ≤ _ := mul_le_mul_of_nonneg_left (A.opNorm_comp_le T) hpos.le
  have hAT : 1 ≤ ‖A‖ * ‖T‖ := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    simpa only [mul_one] using hcomp
  have hMN : M * ‖T‖ ≤ 2 * (K - N) := by linarith
  have hgap : 0 < 2 * (K - N) := (mul_pos hM hpos).trans_le hMN
  apply (div_le_iff₀ hgap).mpr
  calc
    M = M * 1 := (mul_one M).symm
    _ ≤ M * (‖A‖ * ‖T‖) := mul_le_mul_of_nonneg_left hAT hM.le
    _ = ‖A‖ * (M * ‖T‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMN (norm_nonneg _)

/-- **Remark 1(c)** of [benIsrael2003generalized], Chapter 8.
If the Jacobian is differentiable at a point of the ball, its
derivative has norm at most the Jacobian's Lipschitz constant. -/
theorem secondDerivative_norm_le_of_jacobian_lipschitz
    {J : E → E →L[ℝ] F} {D : E →L[ℝ] (E →L[ℝ] F)} {x x₀ : E} {r M : ℝ}
    (hx : x ∈ Metric.ball x₀ r) (hM : 0 ≤ M) (hD : HasFDerivAt J D x)
    (hLip : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r, ‖J u - J v‖ ≤ M * ‖u - v‖) :
    ‖D‖ ≤ M := by
  let L : NNReal := ⟨M, hM⟩
  have hL : (L : ℝ) = M := rfl
  have hl : LipschitzOnWith L J (Metric.ball x₀ r) :=
    .of_dist_le_mul (fun u hu v hv => by simpa only [dist_eq_norm, hL] using hLip u hu v hv)
  exact hD.le_of_lipschitzOn (Metric.isOpen_ball.mem_nhds hx) hl

/-- **Remark 2** of [benIsrael2003generalized], Chapter 8.
A derivative that is continuous at the starting point gives an
approximate derivative, with any positive tolerance, on a sufficiently
small ball. -/
theorem exists_ball_approxDerivative_of_continuousAt
    {f : E → F} {J : E → E →L[ℝ] F} {x₀ : E} {ε : ℝ}
    (hDeriv : ∀ᶠ x in 𝓝 x₀, HasFDerivAt f (J x) x)
    (hCont : ContinuousAt J x₀) (hε : 0 < ε) :
    ∃ r > 0, ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖f u - f v - J x₀ (u - v)‖ ≤ ε * ‖u - v‖ := by
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖J x - J x₀‖ < ε := by
    have he : J ⁻¹' Metric.ball (J x₀) ε ∈ 𝓝 x₀ :=
      hCont (Metric.ball_mem_nhds (J x₀) hε)
    filter_upwards [he] with x hx
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hx
  obtain ⟨r, hr, hBall⟩ := Metric.eventually_nhds_iff_ball.mp (hDeriv.and hnear)
  refine ⟨r, hr, fun u hu v hv => ?_⟩
  have hDerivative (x : E) (hx : x ∈ Metric.ball x₀ r) :
      HasFDerivWithinAt (fun y => f y - J x₀ y) (J x - J x₀) (Metric.ball x₀ r) x :=
    ((hBall x hx).1.sub (J x₀).hasFDerivAt).hasFDerivWithinAt
  have h := (convex_ball x₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hDerivative
    (fun x hx => (hBall x hx).2.le) hv hu
  have he : (f u - J x₀ u) - (f v - J x₀ v) = f u - f v - J x₀ (u - v) := by
    rw [map_sub]
    abel
  exact he ▸ h

/-- When the outer inverse is injective, a zero correction is
equivalent to a zero residual. -/
theorem zero_correction_iff_root {T : F →L[ℝ] E} {y : F} (hT : Function.Injective T) :
    T y = 0 ↔ y = 0 := by
  rw [← T.map_zero]
  exact hT.eq_iff

/-- The trivial outer inverse produces the constant sequence. -/
theorem newtonIterate_zero_inverse (f : E → F) (x₀ : E) (k : ℕ) :
    newtonIterate f (fun _ => 0) x₀ k = x₀ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [newtonIterate_succ, ih]

/-- A nonzero outer inverse can give a zero correction even when the
equations are inconsistent. Here the second equation is the constant
one and the first Newton step solves the first equation. -/
theorem outerNewton_nonroot_example (a x₀ : ℝ) :
    let f : ℝ → ℝ × ℝ := fun x => (x - a, 1)
    let A : ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.id ℝ ℝ).prod 0
    let T : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    IsNewtonOuterInverse A T ∧ T ≠ 0 ∧
      (∀ x, f x ≠ 0) ∧ ∀ k, newtonIterate f (fun _ => T) x₀ (k + 1) = a := by
  dsimp only
  refine ⟨isNewtonOuterInverse_iff.mpr (fun _ => rfl), ?_, ?_, ?_⟩
  · intro h
    have he := DFunLike.congr_fun h ((1, 0) : ℝ × ℝ)
    exact one_ne_zero he
  · intro x h
    exact one_ne_zero (congrArg Prod.snd h)
  · intro k
    rw [newtonIterate_succ]
    let u := newtonIterate (fun x : ℝ => (x - a, (1 : ℝ)))
      (fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ) x₀ k
    change u - (u - a) = a
    abel

end Remarks

section LeastSquares

open Matrix
open scoped InnerProductSpace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (62)** of [benIsrael2003generalized], Chapter 8.
The matrix of the Fréchet derivative in the Euclidean coordinate bases. -/
noncomputable def jacobianMatrix (f : EuclideanSpace ℝ n → EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ n) : Matrix m n ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun n ℝ).toBasis (EuclideanSpace.basisFun m ℝ).toBasis
    (fderiv ℝ f x).toLinearMap

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- **Equation (60)** of [benIsrael2003generalized], Chapter 8.
A vector-valued residual vanishes exactly when every equation holds. -/
theorem residual_eq_zero_iff_components (f : EuclideanSpace ℝ n → EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ n) : f x = 0 ↔ ∀ i, f x i = 0 := by
  constructor
  · intro h i
    simp [h]
  · intro h
    ext i
    exact h i

omit [DecidableEq m] in
/-- The Euclidean operator of the Jacobian is the Fréchet derivative. -/
theorem jacobianMatrix_operator (f : EuclideanSpace ℝ n → EuclideanSpace ℝ m)
    (x : EuclideanSpace ℝ n) : lpCLM 2 (jacobianMatrix f x) = fderiv ℝ f x := by
  apply ContinuousLinearMap.ext
  intro y
  change toEuclideanLin (jacobianMatrix f x) y = (fderiv ℝ f x).toLinearMap y
  rw [jacobianMatrix, toEuclideanLin_eq_toLin_orthonormal, toLin_toMatrix]

omit [DecidableEq m] in
/-- **Equation (62)** of [benIsrael2003generalized], Chapter 8.
The Jacobian entry is the derivative of one component along a
coordinate line through the point. -/
theorem jacobianMatrix_apply_eq_partial
    {f : EuclideanSpace ℝ n → EuclideanSpace ℝ m} {x : EuclideanSpace ℝ n}
    (hf : DifferentiableAt ℝ f x) (i : m) (j : n) :
    jacobianMatrix f x i j =
      deriv (fun t : ℝ => f (x + t • EuclideanSpace.single j 1) i) 0 := by
  let e : EuclideanSpace ℝ n := EuclideanSpace.single j 1
  have hLine : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  have hcurve := hf'.comp_hasDerivAt (x := 0) hLine
  have hcoord := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt (x := 0) hcurve
  have hd : HasDerivAt (fun t : ℝ => f (x + t • e) i) ((fderiv ℝ f x) e i) 0 := hcoord
  rw [hd.deriv, jacobianMatrix, LinearMap.toMatrix_apply]
  change (fderiv ℝ f x) ((EuclideanSpace.basisFun n ℝ) j) i = _
  rw [EuclideanSpace.basisFun_apply]

/-- A matrix pseudoinverse induces an outer inverse on Euclidean spaces. -/
theorem isNewtonOuterInverse_pinv (A : Matrix m n ℝ) :
    IsNewtonOuterInverse (lpCLM 2 A) (lpCLM 2 A.pinv) := by
  apply isNewtonOuterInverse_iff.mpr
  intro y
  change A.pinv.toEuclideanLin (A.toEuclideanLin (A.pinv.toEuclideanLin y)) =
    A.pinv.toEuclideanLin y
  rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]

/-- **Equation (71)** of [benIsrael2003generalized], Chapter 8.
The gradient of the squared residual is twice the adjoint Jacobian
applied to the residual. -/
theorem hasGradientAt_norm_sq_of_jacobian
    {f : EuclideanSpace ℝ n → EuclideanSpace ℝ m} {z : EuclideanSpace ℝ n}
    {J : Matrix m n ℝ} (hJ : HasFDerivAt f (lpCLM 2 J) z) :
    HasGradientAt (fun x => ‖f x‖ ^ 2) (2 • Jᴴ.toEuclideanLin (f z)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)
      (Jᴴ.toEuclideanLin (f z)) = (innerSL ℝ (f z)).comp (lpCLM 2 J) := by
    ext x
    change ⟪Jᴴ.toEuclideanLin (f z), x⟫_ℝ = ⟪f z, J.toEuclideanLin x⟫_ℝ
    exact toEuclideanLin_conjTranspose_inner_left J x (f z)
  rw [two_nsmul, map_add, h, ← two_nsmul]
  exact hJ.norm_sq

/-- **Corollary 3**, Equations (70)–(71) of [benIsrael2003generalized],
Chapter 8. A pseudoinverse Newton sequence satisfying the hypotheses
of Theorem 4 converges to a stationary point of the squared residual.
Condition (64c) controls the residual-weighted difference of corrections,
which is the term needed to pass to the limit in the iteration. -/
theorem corollary_3
    {f : EuclideanSpace ℝ n → EuclideanSpace ℝ m} {J : EuclideanSpace ℝ n → Matrix m n ℝ}
    {x₀ : EuclideanSpace ℝ n} {r M N K α : ℝ}
    (hJ : ∀ x ∈ Metric.ball x₀ r, HasFDerivAt f (lpCLM 2 (J x)) x)
    (hLip : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖lpCLM 2 (J u) - lpCLM 2 (J v)‖ ≤ M * ‖u - v‖)
    (h₀ : ‖lpCLM 2 (J x₀).pinv (f x₀)‖ ≤ α)
    (hVar : ∀ u ∈ Metric.ball x₀ r, ∀ v ∈ Metric.ball x₀ r,
      ‖(lpCLM 2 (J u).pinv - lpCLM 2 (J v).pinv) (f v)‖ ≤ N * ‖u - v‖ ^ 2)
    (hK : ∀ u ∈ Metric.ball x₀ r, M / 2 * ‖lpCLM 2 (J u).pinv‖ + N ≤ K)
    (hK₀ : 0 ≤ K) (hh : α * K < 1) (hrad : α / (1 - α * K) < r) :
    ∃ z ∈ Metric.ball x₀ r,
      Tendsto (newtonIterate f (fun x => lpCLM 2 (J x).pinv) x₀) atTop (𝓝 z) ∧
      HasGradientAt (fun x => ‖f x‖ ^ 2) 0 z := by
  obtain ⟨z, hz, hlim, hzero, _⟩ := theorem_4 hJ hLip
    (fun x _ => isNewtonOuterInverse_pinv (J x)) h₀ hVar hK hK₀ hh hrad
  have hZ : (J z).pinv.toEuclideanLin (f z) = 0 := hzero
  have hAdj : (J z)ᴴ.toEuclideanLin (f z) = 0 := by
    calc
      _ = ((J z)ᴴ * ((J z) * (J z).pinv)).toEuclideanLin (f z) := by
        rw [(J z).conjTranspose_mul_mul_pinv]
      _ = _ := by rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, hZ, map_zero, map_zero]
  refine ⟨z, hz, hlim, ?_⟩
  simpa only [hAdj, smul_zero] using hasGradientAt_norm_sq_of_jacobian (hJ z hz)

end LeastSquares

end BenIsraelGreville.Chapter08
