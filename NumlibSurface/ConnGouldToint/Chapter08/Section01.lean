import Mathlib.Analysis.Matrix.Spectrum
import NumlibSurface.ConnGouldToint.Chapter06.Section06
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Dual trust-region norms

[conn2000trust], Section 8.1.5. These definitions specialize to a trust-region norm for
any fixed iteration. Including the zero vector in each supremum gives the usual
zero norm on the zero-dimensional space, since division by zero has value zero.
-/

open Filter
open scoped Topology

namespace ConnGouldToint.Chapter08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dual norm associated with the trust-region norm `p`, as in (8.1.11). -/
noncomputable def dualNorm (p : E → ℝ) (y : E) : ℝ :=
  ⨆ x : E, |inner ℝ y x| / p x

/-- The operator norm from the trust-region norm to its dual, as in (8.1.13). -/
noncomputable def bidualNorm (p : E → ℝ) (H : E →L[ℝ] E) : ℝ :=
  ⨆ x : E, dualNorm p (H x) / p x

omit [InnerProductSpace ℝ E] in
private theorem norm_pos_of_comparison {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) {x : E} (hx : x ≠ 0) : 0 < p x := by
  by_contra! h
  exact (norm_pos_iff.mpr hx).not_ge ((hp x).trans (mul_nonpos_of_nonneg_of_nonpos hκ h))

private theorem inner_ratio_le {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) (x y : E) : |inner ℝ y x| / p x ≤ κ * ‖y‖ := by
  by_cases hx : x = 0
  · simp [hx, mul_nonneg hκ (norm_nonneg y)]
  have hpx := norm_pos_of_comparison hκ hp hx
  apply (div_le_iff₀ hpx).2
  calc
    |inner ℝ y x| ≤ ‖y‖ * ‖x‖ := abs_real_inner_le_norm y x
    _ ≤ ‖y‖ * (κ * p x) := mul_le_mul_of_nonneg_left (hp x) (norm_nonneg y)
    _ = κ * ‖y‖ * p x := by ring

/-- The upper comparison (8.1.17) for the dual norm. -/
theorem dualNorm_le {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hp : ∀ x, ‖x‖ ≤ κ * p x)
    (y : E) : dualNorm p y ≤ κ * ‖y‖ :=
  ciSup_le fun x ↦ inner_ratio_le hκ hp x y

/-- Hölder's inequality (8.1.12) for the trust-region norm and its dual under AN.1b. -/
theorem abs_inner_le_mul_dualNorm {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) (hp0 : p 0 = 0) (x y : E) :
    |inner ℝ y x| ≤ p x * dualNorm p y := by
  by_cases hx : x = 0
  · simp [hx, hp0]
  have hpx := norm_pos_of_comparison hκ hp hx
  have hb : BddAbove (Set.range fun z : E ↦ |inner ℝ y z| / p z) :=
    ⟨κ * ‖y‖, by rintro _ ⟨z, rfl⟩; exact inner_ratio_le hκ hp z y⟩
  have h := (div_le_iff₀ hpx).1 (le_ciSup hb x)
  simpa [dualNorm, mul_comm] using h

/-- Theorem 8.1.7. AN.1b bounds the dual norm by `κ` times the Euclidean norm
and the bidual operator norm by `κ ^ 2` times the Euclidean operator norm.
The operator estimate holds for arbitrary continuous linear maps. -/
theorem theorem_8_1_7 {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hp : ∀ x, ‖x‖ ≤ κ * p x) :
    (∀ x, dualNorm p x ≤ κ * ‖x‖) ∧
      ∀ H : E →L[ℝ] E, bidualNorm p H ≤ κ ^ 2 * ‖H‖ := by
  refine ⟨dualNorm_le hκ hp, fun H ↦ ciSup_le fun x ↦ ?_⟩
  by_cases hx : x = 0
  · have hzero : dualNorm p (0 : E) = 0 := by simp [dualNorm]
    simp [hx, hzero, mul_nonneg (sq_nonneg κ) (norm_nonneg H)]
  have hpx := norm_pos_of_comparison hκ hp hx
  apply (div_le_iff₀ hpx).2
  calc
    dualNorm p (H x) ≤ κ * ‖H x‖ := dualNorm_le hκ hp _
    _ ≤ κ * (‖H‖ * ‖x‖) := mul_le_mul_of_nonneg_left (H.le_opNorm x) hκ
    _ ≤ κ * (‖H‖ * (κ * p x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp x) (norm_nonneg H)) hκ
    _ = κ ^ 2 * ‖H‖ * p x := by ring

/-- The norm equivalence assertion of Theorem 8.1.8, with the same constant as AN.1. -/
theorem dualNorm_equivalent {p : E → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hl : ∀ x, ‖x‖ ≤ κ * p x) (hu : ∀ x, p x ≤ κ * ‖x‖) (y : E) :
    ‖y‖ / κ ≤ dualNorm p y ∧ dualNorm p y ≤ κ * ‖y‖ := by
  refine ⟨?_, dualNorm_le hκ.le hl y⟩
  by_cases hy : y = 0
  · simp [hy, dualNorm]
  have hpy := norm_pos_of_comparison hκ.le hl hy
  have hb : BddAbove (Set.range fun z : E ↦ |inner ℝ y z| / p z) :=
    ⟨κ * ‖y‖, by rintro _ ⟨z, rfl⟩; exact inner_ratio_le hκ.le hl z y⟩
  refine le_trans ?_ (le_ciSup hb y)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  apply (div_le_div_iff₀ hκ hpy).2
  calc
    ‖y‖ * p y ≤ ‖y‖ * (κ * ‖y‖) := mul_le_mul_of_nonneg_left (hu y) (norm_nonneg y)
    _ = ‖y‖ ^ 2 * κ := by ring

private theorem dualNorm_sub_le {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) (hp0 : p 0 = 0) (y z : E) :
    dualNorm p y - dualNorm p z ≤ κ * ‖y - z‖ := by
  apply sub_le_iff_le_add'.2
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · have hn : 0 ≤ dualNorm p z := by
      have hb : BddAbove (Set.range fun w : E ↦ |inner ℝ z w| / p w) :=
        ⟨κ * ‖z‖, by rintro _ ⟨w, rfl⟩; exact inner_ratio_le hκ hp w z⟩
      simpa [dualNorm] using le_ciSup hb 0
    simpa [hx] using add_nonneg hn (mul_nonneg hκ (norm_nonneg (y - z)))
  have hpx := norm_pos_of_comparison hκ hp hx
  have hinner : |inner ℝ y x| ≤ |inner ℝ z x| + |inner ℝ (y - z) x| := by
    calc
      |inner ℝ y x| = |inner ℝ z x + inner ℝ (y - z) x| := by
        rw [inner_sub_left]
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  calc
    |inner ℝ y x| / p x ≤ (|inner ℝ z x| + |inner ℝ (y - z) x|) / p x :=
      div_le_div_of_nonneg_right hinner hpx.le
    _ = |inner ℝ z x| / p x + |inner ℝ (y - z) x| / p x := add_div _ _ _
    _ ≤ dualNorm p z + κ * ‖y - z‖ :=
      add_le_add ((div_le_iff₀ hpx).2 (by
        simpa [mul_comm] using abs_inner_le_mul_dualNorm hκ hp hp0 x z))
        (inner_ratio_le hκ hp x (y - z))

/-- For a fixed trust-region norm, the dual criticality measure changes by at most `κ`
times the change in the gradient. -/
theorem abs_sub_dualNorm_le_of_fixed_norm {p : E → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) (hp0 : p 0 = 0) (y z : E) :
    |dualNorm p y - dualNorm p z| ≤ κ * ‖y - z‖ := by
  refine abs_sub_le_iff.2 ⟨dualNorm_sub_le hκ hp hp0 y z, ?_⟩
  rw [norm_sub_rev y z]
  exact dualNorm_sub_le hκ hp hp0 z y

/-- A corrected form of the AN.3 implication in Theorem 8.1.8. Use a fixed trust-region
norm and assume the gradients are Lipschitz along the iterates, as follows from a uniform
Hessian bound. Continuous differentiability alone does not give this uniform estimate
when the iterates are unbounded. -/
theorem dualNorm_tendsto_difference_zero {p : E → ℝ} {κ L : ℝ} (hκ : 0 ≤ κ)
    (hp : ∀ x, ‖x‖ ≤ κ * p x) (hp0 : p 0 = 0) {x g : ℕ → E}
    (hg : ∀ j k, ‖g j - g k‖ ≤ L * ‖x j - x k‖) {j k : ℕ → ℕ}
    (hx : Tendsto (fun n ↦ ‖x (j n) - x (k n)‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ |dualNorm p (g (j n)) - dualNorm p (g (k n))|) atTop (𝓝 0) := by
  have hb : Tendsto (fun n ↦ κ * L * ‖x (j n) - x (k n)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := κ * L)).mul hx
  apply squeeze_zero (fun _ ↦ abs_nonneg _) _ hb
  intro n
  calc
    _ ≤ κ * ‖g (j n) - g (k n)‖ := abs_sub_dualNorm_le_of_fixed_norm hκ hp hp0 _ _
    _ ≤ κ * (L * ‖x (j n) - x (k n)‖) := mul_le_mul_of_nonneg_left (hg _ _) hκ
    _ = _ := (mul_assoc _ _ _).symm

/-- Uniform equivalence alone permits different dual criticality measures at the same
point, even for the exact gradient of a smooth, bounded-below quadratic.
In Theorem 8.1.8 one must add a restriction on the variation of the norm with the
iteration to deduce AN.3. These two norms may be used on alternating iterations. -/
theorem dualNorm_scaling_counterexample :
    let p : ℝ → ℝ := fun x ↦ ‖x‖
    let q : ℝ → ℝ := fun x ↦ 2 * ‖x‖
    (∀ x, ‖x‖ ≤ 2 * p x ∧ p x ≤ 2 * ‖x‖) ∧
      (∀ x, ‖x‖ ≤ 2 * q x ∧ q x ≤ 2 * ‖x‖) ∧ dualNorm p 1 ≠ dualNorm q 1 := by
  intro p q
  refine ⟨fun x ↦ ⟨?_, ?_⟩, fun x ↦ ⟨?_, le_rfl⟩, ?_⟩
  · dsimp [p]
    linarith [abs_nonneg x]
  · dsimp [p]
    linarith [abs_nonneg x]
  · dsimp [q]
    linarith [abs_nonneg x]
  have hp : ‖(1 : ℝ)‖ / 1 ≤ dualNorm p 1 :=
    (dualNorm_equivalent (p := p) (κ := 1) zero_lt_one
      (fun x ↦ by simp [p]) (fun x ↦ by simp [p]) 1).1
  have hq : dualNorm q 1 ≤ (1 / 2) * ‖(1 : ℝ)‖ :=
    dualNorm_le (p := q) (κ := 1 / 2) (by norm_num)
      (fun x ↦ by dsimp [q]; linarith) 1
  norm_num at hp hq
  exact ne_of_gt (lt_of_le_of_lt hq (lt_of_lt_of_le (by norm_num) hp))

/-- Lemma 8.1.6. A change of variables by a continuous linear equivalence
takes the ellipsoidal dual norm to the norm of the adjoint and the bidual
operator norm to the norm of the congruence-transformed operator. -/
theorem lemma_8_1_6 [CompleteSpace E] (S : E ≃L[ℝ] E) :
    (∀ y, dualNorm (fun x => ‖S.symm x‖) y =
      ‖(S : E →L[ℝ] E).adjoint y‖) ∧
    ∀ H : E →L[ℝ] E, bidualNorm (fun x => ‖S.symm x‖) H =
      ‖((S : E →L[ℝ] E).adjoint.comp H).comp (S : E →L[ℝ] E)‖ := by
  have hdual (y : E) : dualNorm (fun x => ‖S.symm x‖) y =
      ‖(S : E →L[ℝ] E).adjoint y‖ := by
    let z := (S : E →L[ℝ] E).adjoint y
    have he (x : E) : inner ℝ y x = inner ℝ z (S.symm x) := by
      rw [show z = (S : E →L[ℝ] E).adjoint y from rfl,
        ContinuousLinearMap.adjoint_inner_left]
      simp
    have hbound (x : E) : |inner ℝ y x| / ‖S.symm x‖ ≤ ‖z‖ := by
      by_cases hx : S.symm x = 0
      · simp [hx]
      · rw [he]
        exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
          (abs_real_inner_le_norm z (S.symm x))
    apply le_antisymm (ciSup_le hbound)
    have hb : BddAbove (Set.range fun x : E => |inner ℝ y x| / ‖S.symm x‖) :=
      ⟨‖z‖, by rintro _ ⟨x, rfl⟩; exact hbound x⟩
    have hlo := le_ciSup hb (S z)
    rw [he, S.symm_apply_apply, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hlo
    by_cases hz : z = 0
    · simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] using hlo
    · rwa [pow_two, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hz)] at hlo
  refine ⟨hdual, fun H => ?_⟩
  let A := ((S : E →L[ℝ] E).adjoint.comp H).comp (S : E →L[ℝ] E)
  let p := fun x : E => ‖S.symm x‖
  change bidualNorm p H = ‖A‖
  have he (x : E) : dualNorm p (H x) = ‖A (S.symm x)‖ := by
    rw [hdual]
    simp [A]
  have hbound (x : E) : dualNorm p (H x) / p x ≤ ‖A‖ := by
    rw [he]
    by_cases hx : S.symm x = 0
    · simp [p, hx]
    · exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr (A.le_opNorm _)
  apply le_antisymm (ciSup_le hbound)
  have hb : BddAbove (Set.range fun x : E => dualNorm p (H x) / p x) :=
    ⟨‖A‖, by rintro _ ⟨x, rfl⟩; exact hbound x⟩
  have htest (z : E) : ‖A z‖ / ‖z‖ ≤ bidualNorm p H := by
    have h : dualNorm p (H (S z)) / p (S z) ≤ bidualNorm p H := le_ciSup hb (S z)
    rw [he] at h
    simpa only [p, S.symm_apply_apply] using h
  change ‖A‖ ≤ bidualNorm p H
  apply ContinuousLinearMap.opNorm_le_bound _
  · simpa only [map_zero, norm_zero, zero_div] using htest 0
  · intro z
    by_cases hz : z = 0
    · simp [hz]
    · exact (div_le_iff₀ (norm_pos_iff.mpr hz)).mp (htest z)

/-- The scaled curvature constant (8.1.22) for a quadratic model. -/
noncomputable def scaledQuadraticCurvature (p : Seminorm ℝ E) (H : E →L[ℝ] E) : ℝ :=
  1 + ⨆ w : E, |inner ℝ w (H w)| / (p w) ^ 2

/-- Corrected Theorem 8.1.9. The dual norm is the slope along a steepest ray
for the trust-region norm, represented by a unit direction attaining the
dual pairing. Equation (8.1.23) needs this ray for a general norm. -/
theorem theorem_8_1_9 (c : ℝ) (g d : E) (H : E →L[ℝ] E) (p : Seminorm ℝ E)
    {K Δ : ℝ} (hK : 0 ≤ K) (hp : ∀ v, ‖v‖ ≤ K * p v) (hΔ : 0 ≤ Δ)
    (hd : p d = 1) (hsteep : inner ℝ g d = -dualNorm p g) {s : E}
    (hs : IsMinOn (ConnGouldToint.Chapter06.quadraticModel c g H.toLinearMap)
      {u | ∃ t ∈ Set.Icc (0 : ℝ) Δ, u = t • d} s) :
    c - ConnGouldToint.Chapter06.quadraticModel c g H.toLinearMap s ≥
      (1 / 2) * dualNorm p g * min (dualNorm p g / scaledQuadraticCurvature p H) Δ := by
  let a := dualNorm p g
  let β := scaledQuadraticCurvature p H
  have hb (w : E) : |inner ℝ w (H w)| / (p w) ^ 2 ≤ ‖H‖ * K ^ 2 := by
    by_cases hw : p w = 0
    · simp [hw, mul_nonneg (norm_nonneg H) (sq_nonneg K)]
    have hwp : 0 < p w := (apply_nonneg p w).lt_of_ne (Ne.symm hw)
    apply (div_le_iff₀ (sq_pos_of_pos hwp)).mpr
    calc
      _ ≤ ‖w‖ * ‖H w‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖w‖ * (‖H‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (H.le_opNorm w) (norm_nonneg w)
      _ = ‖H‖ * ‖w‖ ^ 2 := by ring
      _ ≤ ‖H‖ * (K * p w) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) (hp w) 2) (norm_nonneg H)
      _ = _ := by ring
  have hB : BddAbove (Set.range fun w : E => |inner ℝ w (H w)| / (p w) ^ 2) :=
    ⟨‖H‖ * K ^ 2, by rintro _ ⟨w, rfl⟩; exact hb w⟩
  have hβ : 0 < β := by
    have hz := le_ciSup hB (0 : E)
    simp at hz
    change 0 < 1 + ⨆ w : E, |inner ℝ w (H w)| / (p w) ^ 2
    linarith
  have ha : 0 ≤ a := by
    have hBa : BddAbove (Set.range fun w : E => |inner ℝ g w| / p w) :=
      ⟨K * ‖g‖, by rintro _ ⟨w, rfl⟩; exact inner_ratio_le hK hp w g⟩
    change 0 ≤ ⨆ w : E, |inner ℝ g w| / p w
    simpa only [inner_zero_right, abs_zero, zero_div] using le_ciSup hBa (0 : E)
  have hcurv : inner ℝ d (H d) ≤ β := by
    have hh := le_ciSup hB d
    rw [hd, one_pow, div_one] at hh
    have h := (le_abs_self _).trans hh
    dsimp [β, scaledQuadraticCurvature]
    linarith
  let t := min (a / β) Δ
  have ht : 0 ≤ t := le_min (div_nonneg ha hβ.le) hΔ
  have htest := isMinOn_iff.mp hs (t • d) ⟨t, ⟨ht, min_le_right _ _⟩, rfl⟩
  have hm : ConnGouldToint.Chapter06.quadraticModel c g H.toLinearMap (t • d) =
      c - t * a + (1 / 2) * t ^ 2 * inner ℝ d (H d) := by
    simp only [ConnGouldToint.Chapter06.quadraticModel, inner_smul_right, map_smul,
      real_inner_smul_left, ContinuousLinearMap.coe_coe, hsteep]
    change c + t * -a + 1 / 2 * (t * (t * inner ℝ d (H d))) = _
    ring
  have htb : t * β ≤ a := (le_div_iff₀ hβ).mp (min_le_left _ _)
  have hquad : t ^ 2 * inner ℝ d (H d) ≤ t * a := calc
    _ ≤ t ^ 2 * β := mul_le_mul_of_nonneg_left hcurv (sq_nonneg t)
    _ = t * (t * β) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htb ht
  rw [hm] at htest
  change (1 / 2) * a * t ≤ _
  nlinarith only [htest, hquad]

private theorem model_le_directional_quadratic {m : E → ℝ} {x d : E} {T B : ℝ}
    (hT : 0 ≤ T)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ m (x + t • d))
    (hDm : ∀ t ∈ Set.Icc (0 : ℝ) T, DifferentiableAt ℝ (fderiv ℝ m) (x + t • d))
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) T, fderiv ℝ (fderiv ℝ m) (x + t • d) d d ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    m (x + t • d) ≤ m x + t * fderiv ℝ m x d + (1 / 2) * B * t ^ 2 := by
  let v (r : ℝ) := B * r - fderiv ℝ m (x + r • d) d
  have hv (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) T) :
      HasDerivAt v (B - fderiv ℝ (fderiv ℝ m) (x + r • d) d d) r := by
    simpa [v] using ((hasDerivAt_id r).const_mul B).fun_sub
      ((hDm r hr).hasDerivAt_comp_add_smul.clm_apply (hasDerivAt_const r d))
  have hvmono : MonotoneOn v (Set.Icc 0 T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
      (fun r hr => (hv r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hv r (interior_subset hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => by rw [(hv r (interior_subset hr)).deriv]; exact sub_nonneg.mpr (hB r (interior_subset hr)))
  let w (r : ℝ) := (r * fderiv ℝ m x d + (1 / 2) * B * r ^ 2) - m (x + r • d)
  have hw (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) T) :
      HasDerivAt w (v r - v 0) r := by
    refine ((((hasDerivAt_id r).mul_const (fderiv ℝ m x d)).add
      (((hasDerivAt_id r).fun_pow 2).const_mul ((1 / 2) * B))).sub
      (hm r hr).hasDerivAt_comp_add_smul).congr_deriv ?_
    simp [v]
    ring
  have hzero : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hwmono : MonotoneOn w (Set.Icc 0 T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
      (fun r hr => (hw r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hw r (interior_subset hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => by
        rw [(hw r (interior_subset hr)).deriv]
        exact sub_nonneg.mpr (hvmono hzero (interior_subset hr) (interior_subset hr).1))
  have h := hwmono hzero ht ht.1
  simp [w] at h
  linarith

/-- The point (8.1.36) at the specified backtracking index. -/
noncomputable def modifiedCauchyTrial (p : Seminorm ℝ E) (x d : E) (Δ q : ℝ) (j : ℕ) : E :=
  x + (q ^ j * Δ / p d) • d

/-- The modified Cauchy Armijo test (8.1.37). -/
def ModifiedCauchyAccepted (m : E → ℝ) (p : Seminorm ℝ E)
    (x d g : E) (Δ q b : ℝ) (j : ℕ) : Prop :=
  m (modifiedCauchyTrial p x d Δ q j) ≤
    m x + b * inner ℝ g (modifiedCauchyTrial p x d Δ q j - x)

/-- Theorem 8.1.10. Backtracking along a descent direction terminates.
The first accepted point achieves the model decrease in (8.1.38), and
its length also has the lower bound used in Corollary 8.1.11. -/
theorem theorem_8_1_10 {m : E → ℝ} (p : Seminorm ℝ E) {x d g : E}
    {Δ q b β : ℝ} (hΔ : 0 < Δ) (hq : 0 < q) (hq₁ : q < 1)
    (hb : 0 < b) (hb₁ : b < 1 / 2) (hβ : 0 < β) (hd : 0 < p d)
    (hdescent : inner ℝ g d < 0) (hgrad : fderiv ℝ m x d = inner ℝ g d)
    (hm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ (fderiv ℝ m) z)
    (hcurv : ∀ z ∈ p.closedBall x Δ, fderiv ℝ (fderiv ℝ m) z d d ≤ β * (p d) ^ 2) :
    let a := |inner ℝ g d| / p d
    let c := b * min (2 * q * (1 - b)) 1
    ∃ j, ModifiedCauchyAccepted m p x d g Δ q b j ∧
      (∀ i < j, ¬ ModifiedCauchyAccepted m p x d g Δ q b i) ∧
      min (2 * q * (1 - b)) 1 * min (a / β) Δ ≤ q ^ j * Δ ∧
      c * a * min (a / β) Δ ≤ m x - m (modifiedCauchyTrial p x d Δ q j) := by
  dsimp only
  let a := |inner ℝ g d| / p d
  let l (j : ℕ) := q ^ j * Δ
  let C := min (2 * q * (1 - b)) 1
  have ha : 0 < a := div_pos (abs_pos.mpr hdescent.ne) hd
  have hb₂ : 0 < 1 - b := by linarith
  have hlen (j : ℕ) : 0 < l j ∧ l j ≤ Δ :=
    ⟨mul_pos (pow_pos hq _) hΔ, mul_le_of_le_one_left hΔ.le (pow_le_one₀ hq.le hq₁.le)⟩
  have hlin (j : ℕ) : (l j / p d) * inner ℝ g d = -(a * l j) := by
    dsimp [a]
    rw [abs_of_neg hdescent]
    ring
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Δ / p d)) : x + t • d ∈ p.closedBall x Δ := by
    rw [Seminorm.mem_closedBall, add_sub_cancel_left, map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    exact (le_div_iff₀ hd).mp ht.2
  have hmodel (j : ℕ) :
      m (modifiedCauchyTrial p x d Δ q j) ≤ m x - a * l j + (1 / 2) * β * (l j) ^ 2 := by
    have ht : l j / p d ∈ Set.Icc (0 : ℝ) (Δ / p d) :=
      ⟨div_nonneg (hlen j).1.le hd.le, div_le_div_of_nonneg_right (hlen j).2 hd.le⟩
    have h := model_le_directional_quadratic (div_nonneg hΔ.le hd.le)
      (fun t ht => hm _ (hpoint t ht)) (fun t ht => hDm _ (hpoint t ht))
      (fun t ht => hcurv _ (hpoint t ht)) ht
    rw [hgrad, hlin] at h
    have he : (1 / 2 : ℝ) * (β * (p d) ^ 2) * (l j / p d) ^ 2 =
        (1 / 2) * β * (l j) ^ 2 := by field_simp
    rwa [he, ← sub_eq_add_neg] at h
  have htest (j : ℕ) : ModifiedCauchyAccepted m p x d g Δ q b j ↔
      m (modifiedCauchyTrial p x d Δ q j) ≤ m x - b * a * l j := by
    unfold ModifiedCauchyAccepted
    conv_lhs => rhs; rw [modifiedCauchyTrial, add_sub_cancel_left, inner_smul_right]
    change (m _ ≤ m x + b * ((l j / p d) * inner ℝ g d)) ↔ _
    rw [hlin]
    ring_nf
  have haccept (j : ℕ) (hj : l j ≤ 2 * (1 - b) * a / β) :
      ModifiedCauchyAccepted m p x d g Δ q b j := by
    have hh := mul_le_mul_of_nonneg_right ((le_div_iff₀ hβ).mp hj) (hlen j).1.le
    exact (htest j).mpr ((hmodel j).trans (by nlinarith only [hh]))
  have hthreshold : 0 < 2 * (1 - b) * a / β := by positivity
  have htend : Tendsto l atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq₁).mul_const Δ
  obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hthreshold)).exists
  have hex : ∃ j, ModifiedCauchyAccepted m p x d g Δ q b j := ⟨k, haccept k hk.le⟩
  classical
  let j := Nat.find hex
  have hj : ModifiedCauchyAccepted m p x d g Δ q b j := Nat.find_spec hex
  have hmin (i : ℕ) (hi : i < j) : ¬ ModifiedCauchyAccepted m p x d g Δ q b i :=
    Nat.find_min hex hi
  have hC : 0 ≤ C := le_min (by positivity) zero_le_one
  have hlength : C * min (a / β) Δ ≤ l j := by
    cases hj' : j with
    | zero =>
      change C * min (a / β) Δ ≤ q ^ 0 * Δ
      rw [pow_zero, one_mul]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hC).trans
        (mul_le_of_le_one_left hΔ.le (min_le_right _ _))
    | succ i =>
      have hfail := hmin i (by rw [hj']; exact Nat.lt_succ_self i)
      have hlarge : 2 * (1 - b) * a / β ≤ l i :=
        (lt_of_not_ge fun h => hfail (haccept i h)).le
      calc
        _ ≤ (2 * q * (1 - b)) * (a / β) := by
          exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hC).trans
            (mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg ha.le hβ.le))
        _ = q * (2 * (1 - b) * a / β) := by ring
        _ ≤ q * l i := mul_le_mul_of_nonneg_left hlarge hq.le
        _ = l (i + 1) := by dsimp [l]; rw [pow_succ]; ring
  refine ⟨j, hj, hmin, hlength, ?_⟩
  have hdrop := (htest j).mp hj
  have hmul := mul_le_mul_of_nonneg_left hlength (mul_nonneg hb.le ha.le)
  change (b * C) * a * min (a / β) Δ ≤ _
  nlinarith only [hdrop, hmul]

/-- Theorem 8.1.12. If the direction attains the dual pairing, the first
acceptable scaled Cauchy step has the dual-norm decrease. -/
theorem theorem_8_1_12 {m : E → ℝ} (p : Seminorm ℝ E) {x d g : E}
    {Δ q b β : ℝ} (hΔ : 0 < Δ) (hq : 0 < q) (hq₁ : q < 1)
    (hb : 0 < b) (hb₁ : b < 1 / 2) (hβ : 0 < β) (hd : 0 < p d)
    (hdescent : inner ℝ g d < 0) (hgrad : fderiv ℝ m x d = inner ℝ g d)
    (hsteep : |inner ℝ g d| / p d = dualNorm p g)
    (hm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ (fderiv ℝ m) z)
    (hcurv : ∀ z ∈ p.closedBall x Δ, fderiv ℝ (fderiv ℝ m) z d d ≤ β * (p d) ^ 2) :
    ∃ j, ModifiedCauchyAccepted m p x d g Δ q b j ∧
      (∀ i < j, ¬ ModifiedCauchyAccepted m p x d g Δ q b i) ∧
      (b * min (2 * q * (1 - b)) 1) * dualNorm p g * min (dualNorm p g / β) Δ ≤
        m x - m (modifiedCauchyTrial p x d Δ q j) := by
  obtain ⟨j, hj, hmin, -, hdec⟩ :=
    theorem_8_1_10 p hΔ hq hq₁ hb hb₁ hβ hd hdescent hgrad hm hDm hcurv
  exact ⟨j, hj, hmin, by simpa only [hsteep] using hdec⟩

/-- The closed cone of directions retaining a positive asymptotic
Euclidean-to-trust-region norm ratio, as in (8.1.6). -/
def curvatureDirections (p : ℕ → Seminorm ℝ E) (ε : ℝ) : Set E :=
  closure {w | ε ≤ liminf (fun k => ‖w‖ / p k w) atTop}

/-- A finite-dimensional norm comparison on the tested cone. Pointwise
eventual bounds suffice because a finite basis of the span converts them to
a uniform bound on that entire span. -/
theorem uniform_norm_comparison_on_curvatureDirections [FiniteDimensional ℝ E]
    (p : ℕ → Seminorm ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ k w, w ∈ curvatureDirections p ε → p k w ≤ C * ‖w‖ := by
  classical
  let S : Set E := {w | ε ≤ liminf (fun k => ‖w‖ / p k w) atTop}
  let W := Submodule.span ℝ S
  have hbounded {w : E} (hw : w ∈ W) : ∃ A ≥ 0, ∀ k, p k w ≤ A := by
    apply Submodule.span_induction (p := fun w _ => ∃ A ≥ 0, ∀ k, p k w ≤ A) ?_ ?_ ?_ ?_ hw
    · intro w hw
      have hlt : ε / 2 < liminf (fun k => ‖w‖ / p k w) atTop :=
        (half_lt_self hε).trans_le hw
      have hb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun k => ‖w‖ / p k w) :=
        ⟨0, show ∀ᶠ k in atTop, 0 ≤ ‖w‖ / p k w from
          Eventually.of_forall fun k => div_nonneg (norm_nonneg _) (apply_nonneg _ _)⟩
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_lt_liminf hlt hb)
      let A := max (‖w‖ / (ε / 2)) (∑ k ∈ Finset.range N, p k w)
      have hA : 0 ≤ A := (div_nonneg (norm_nonneg _) (half_pos hε).le).trans (le_max_left _ _)
      refine ⟨A, hA, fun k => ?_⟩
      by_cases hk : N ≤ k
      · have hpos : 0 < p k w := (apply_nonneg _ _).lt_of_ne (fun h => by
          have hh := hN k hk
          rw [← h, div_zero] at hh
          exact (half_pos hε).not_gt hh)
        have hmul := (lt_div_iff₀ hpos).mp (hN k hk)
        apply le_trans _ (le_max_left _ _)
        exact (le_div_iff₀ (half_pos hε)).mpr (by simpa only [mul_comm] using hmul.le)
      · exact (Finset.single_le_sum (fun i _ => apply_nonneg (p i) w)
          (Finset.mem_range.mpr (lt_of_not_ge hk))).trans (le_max_right _ _)
    · exact ⟨0, le_rfl, by simp⟩
    · rintro v w _ _ ⟨A, hA, hv⟩ ⟨B, hB, hw⟩
      exact ⟨A + B, add_nonneg hA hB, fun k =>
        (map_add_le_add (p k) v w).trans (add_le_add (hv k) (hw k))⟩
    · rintro a w _ ⟨A, hA, hw⟩
      refine ⟨‖a‖ * A, mul_nonneg (norm_nonneg _) hA, fun k => ?_⟩
      rw [map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hw k) (norm_nonneg _)
  let b := Module.finBasis ℝ W
  choose A hA hbound using fun i => hbounded (b i).property
  let B : W →L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) := b.equivFunL
  let C := 1 + ‖B‖ * (∑ i, A i)
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ i, A i := Finset.sum_nonneg fun i _ => hA i
    dsimp [C]
    positivity
  refine ⟨C, hC, fun k w hw => ?_⟩
  have hwW : w ∈ W := (closure_minimal Submodule.subset_span W.closed_of_finiteDimensional) hw
  let u : W := ⟨w, hwW⟩
  have hu : (∑ i, b.repr u i • (b i : E)) = w := by
    have h := congrArg Subtype.val (b.sum_repr u)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have hcoord (i : Fin (Module.finrank ℝ W)) : ‖b.repr u i‖ ≤ ‖B‖ * ‖w‖ :=
    (norm_le_pi_norm (B u) i).trans (B.le_opNorm u)
  calc
    p k w = p k (∑ i, b.repr u i • (b i : E)) := congrArg (p k) hu.symm
    _ ≤ ∑ i, p k (b.repr u i • (b i : E)) :=
      Finset.le_sum_of_subadditive (p k) (by simp) (map_add_le_add (p k)) _ _
    _ ≤ ∑ i, (‖B‖ * ‖w‖) * A i := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul_eq_mul]
      exact mul_le_mul (hcoord i) (hbound i k) (apply_nonneg _ _) (by positivity)
    _ = (‖B‖ * (∑ i, A i)) * ‖w‖ := by rw [← Finset.mul_sum]; ring
    _ ≤ C * ‖w‖ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)

private theorem scaled_curvature_lower {p : Seminorm ℝ E} {H : E →L[ℝ] E →L[ℝ] ℝ}
    {τ ε C : ℝ} {u : E} (hτ : -ε ≤ τ) (hε : 0 ≤ ε)
    (hp : 0 < p u) (hcomp : p u ≤ C) (hcurv : τ ≤ H u u / (p u) ^ 2) :
    -ε * C ^ 2 ≤ H u u := by
  have hpow := pow_le_pow_left₀ hp.le hcomp 2
  calc
    _ ≤ -ε * (p u) ^ 2 := mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hε)
    _ ≤ τ * (p u) ^ 2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg _)
    _ ≤ _ := (le_div_iff₀ (sq_pos_of_pos hp)).mp hcurv

/-- Lemma 8.1.1. On the Euclidean unit directions of the tested cone, uniform
upper comparison of the trust-region norms transfers asymptotic nonnegative
scaled curvature to the Euclidean curvature infimum. A subsequence can be
incorporated directly into the indexing. -/
theorem lemma_8_1_1 {U : Set E} [Nonempty U] {p : ℕ → Seminorm ℝ E}
    {H : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {τ : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hcomp : ∀ᶠ k in atTop, ∀ u ∈ U, 0 < p k u ∧ p k u ≤ C)
    (hcurv : ∀ k u, u ∈ U → τ k ≤ H k u u / (p k u) ^ 2)
    (hτb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) τ)
    (hτ : 0 ≤ liminf τ atTop)
    (hupper : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·)
      (fun k => ⨅ u : U, H k u u)) :
    0 ≤ liminf (fun k => ⨅ u : U, H k u u) atTop := by
  by_contra! hn
  let ε := -liminf (fun k => ⨅ u : U, H k u u) atTop / (2 * C ^ 2)
  have hε : 0 < ε := div_pos (neg_pos.mpr hn) (by positivity)
  have hsmall : -ε < liminf τ atTop := (neg_lt_zero.mpr hε).trans_le hτ
  have hnear : ∀ᶠ k in atTop, -ε * C ^ 2 ≤ ⨅ u : U, H k u u := by
    filter_upwards [eventually_lt_of_lt_liminf hsmall hτb, hcomp] with k hk hc
    apply le_ciInf
    intro u
    exact scaled_curvature_lower hk.le hε.le (hc u u.property).1 (hc u u.property).2
      (hcurv k u u.property)
  have hb := le_liminf_of_le hupper hnear
  have he : -ε * C ^ 2 = liminf (fun k => ⨅ u : U, H k u u) atTop / 2 := by
    dsimp [ε]
    field_simp
  rw [he] at hb
  linarith

/-- The norm comparison needed by Lemma 8.1.1 follows from AN.1b and
finite dimensionality on the unit slice of the cone in (8.1.6). -/
theorem lemma_8_1_1_on_curvatureDirections [FiniteDimensional ℝ E]
    (p : ℕ → Seminorm ℝ E) {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hAN : ∀ k u, ‖u‖ ≤ K * p k u)
    {H : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {τ : ℕ → ℝ}
    (hcurv : ∀ k u, u ≠ 0 → τ k ≤ H k u u / (p k u) ^ 2)
    (hτb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) τ)
    (hτ : 0 ≤ liminf τ atTop) :
    let U := curvatureDirections p ε ∩ {u : E | ‖u‖ = 1}
    U.Nonempty →
    (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) (fun k => ⨅ u : U, H k u u) →
    0 ≤ liminf (fun k => ⨅ u : U, H k u u) atTop := by
  dsimp only
  intro hU hupper
  let : Nonempty (↑(curvatureDirections p ε ∩ {u : E | ‖u‖ = 1}) : Type _) := hU.coe_sort
  obtain ⟨C, hC, hcomp⟩ := uniform_norm_comparison_on_curvatureDirections p hε
  have hneq {u : E} (hu : ‖u‖ = 1) : u ≠ 0 := fun h => by simp [h] at hu
  apply lemma_8_1_1 (p := p) hC _ _ hτb hτ hupper
  · refine Eventually.of_forall fun k u hu => ?_
    exact ⟨norm_pos_of_comparison hK (hAN k) (hneq hu.2),
      (hcomp k u hu.1).trans_eq (by rw [hu.2, mul_one])⟩
  · intro k u hu
    exact hcurv k u (hneq hu.2)

/-- AA.2b, including the fixed length cap on negative-curvature decrease. -/
def HasCappedNegativeCurvatureDecrease (m : E → ℝ) (x s : E) (τ Δ κ cap : ℝ) : Prop :=
  0 < κ ∧ (τ < 0 → κ * |τ| * min (min (τ ^ 2) (Δ ^ 2)) (cap ^ 2) ≤ m x - m (x + s))

omit [InnerProductSpace ℝ E] in
private theorem negativeCurvatureDecrease_clipped {m : E → ℝ} {x s : E}
    {τ Δ κ cap : ℝ}
    (h : HasCappedNegativeCurvatureDecrease m x s τ Δ κ cap) :
    ConnGouldToint.Chapter06.HasNegativeCurvatureDecrease m x s (max (-cap) τ) Δ κ := by
  refine ⟨h.1, fun hτ => ?_⟩
  have hn : τ < 0 := (le_max_right _ _).trans_lt hτ
  have hle : |max (-cap) τ| ≤ |τ| := by
    rw [abs_of_neg hτ, abs_of_neg hn]
    exact neg_le_neg (le_max_right _ _)
  have hle' : |max (-cap) τ| ≤ cap := by
    rw [abs_of_neg hτ]
    simpa only [neg_neg] using neg_le_neg (le_max_left (-cap) τ)
  have hs := pow_le_pow_left₀ (abs_nonneg (max (-cap) τ)) hle 2
  have hs' := pow_le_pow_left₀ (abs_nonneg (max (-cap) τ)) hle' 2
  rw [sq_abs, sq_abs] at hs
  rw [sq_abs] at hs'
  have hmin : min ((max (-cap) τ) ^ 2) (Δ ^ 2) ≤ min (min (τ ^ 2) (Δ ^ 2)) (cap ^ 2) :=
    le_min (min_le_min hs le_rfl) ((min_le_left _ _).trans hs')
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hle h.1.le) hmin
    (le_min (sq_nonneg _) (sq_nonneg _)) (mul_nonneg h.1.le (abs_nonneg _))).trans (h.2 hn)

/-- Theorem 8.1.2. Under the small-radius agreement estimate and AA.2b,
the scaled model curvature cannot stay below a fixed negative threshold. -/
theorem theorem_8_1_2 {P : ConnGouldToint.Chapter06.BTRParams} {f : E → ℝ}
    {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : ConnGouldToint.Chapter06.BTRRun f P sufficient)
    {τ : ℕ → ℝ} {κ cap : ℝ} (hκ : 0 < κ) (hcap : 0 < cap)
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (Set.range f)) (herr : ConnGouldToint.Chapter06.smallRadiusModelAgreement run)
    (hsecond : ∀ k, HasCappedNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ cap)
    (hupper : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) τ) :
    0 ≤ limsup τ atTop := by
  let v (k : ℕ) := max (-cap) (τ k)
  have hfreq := ConnGouldToint.Chapter06.theorem_6_6_4 run (curv := v) (τ := v) hκ hval
    hlower herr (by simp) (fun k => negativeCurvatureDecrease_clipped (hsecond k))
  by_contra! hn
  let ε := min (-limsup τ atTop / 2) (cap / 2)
  have he : 0 < ε := lt_min (half_pos (neg_pos.mpr hn)) (half_pos hcap)
  have hε : ε < cap := (min_le_right _ _).trans_lt (half_lt_self hcap)
  have hf := (hfreq ε he).mono fun k hk => by
    change -ε < max (-cap) (τ k) at hk
    exact ((lt_max_iff.mp hk).resolve_left (not_lt.mpr (neg_le_neg hε.le))).le
  have hb := le_limsup_of_frequently_le hf hupper
  have hhalf : ε ≤ -limsup τ atTop / 2 := min_le_left _ _
  linarith

/-- Theorem 8.1.3. The AM.5b scaled Hessian discrepancy and uniform norm
comparison on the tested directions transfer the model-curvature limsup
to the Euclidean objective-curvature limsup. -/
theorem theorem_8_1_3 {U : Set E} [Nonempty U] {p : ℕ → Seminorm ℝ E}
    {F M : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {τ e : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hcomp : ∀ᶠ k in atTop, ∀ u ∈ U, 0 < p k u ∧ p k u ≤ C)
    (hcurv : ∀ k u, u ∈ U → τ k ≤ M k u u / (p k u) ^ 2)
    (herr : ∀ k u, u ∈ U → |F k u u - M k u u| / (p k u) ^ 2 ≤ e k)
    (he : Tendsto e atTop (𝓝 0)) (hτ : 0 ≤ limsup τ atTop)
    (hτb : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) τ)
    (hupper : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·)
      (fun k => ⨅ u : U, F k u u)) :
    0 ≤ limsup (fun k => ⨅ u : U, F k u u) atTop := by
  by_contra! hn
  let ε := -limsup (fun k => ⨅ u : U, F k u u) atTop / (4 * C ^ 2)
  have hε : 0 < ε := div_pos (neg_pos.mpr hn) (by positivity)
  have hfreq : ∃ᶠ k in atTop, -ε < τ k := by
    by_contra! hf
    have hle := limsup_le_of_le hτb hf
    linarith
  have hnear : ∃ᶠ k in atTop, -(2 * ε) * C ^ 2 ≤ ⨅ u : U, F k u u := by
    refine (hfreq.and_eventually ((he.eventually (gt_mem_nhds hε)).and hcomp)).mono ?_
    rintro k ⟨hk, herror, hc⟩
    apply le_ciInf
    intro u
    have hp := (hc u u.property).1
    have hpow : 0 < (p k u) ^ 2 := sq_pos_of_pos hp
    have hq := (le_div_iff₀ hpow).mp (hcurv k u u.property)
    have hdiff := (div_le_iff₀ hpow).mp (herr k u u.property)
    have ht : -(2 * ε) ≤ τ k - e k := by linarith
    apply scaled_curvature_lower ht (by positivity) hp (hc u u.property).2
    apply (le_div_iff₀ hpow).mpr
    linarith only [hq, hdiff, neg_abs_le (F k u u - M k u u)]
  have hb := le_limsup_of_frequently_le hnear hupper
  have hEq : -(2 * ε) * C ^ 2 = limsup (fun k => ⨅ u : U, F k u u) atTop / 2 := by
    dsimp [ε]
    field_simp
    ring
  rw [hEq] at hb
  linarith

/-- In an anisotropic norm, the Euclidean Cauchy ray can miss the
dual-norm decrease bound in the printed Theorem 8.1.9, even for a linear model. -/
theorem theorem_8_1_9_counterexample :
    ∃ (p : Seminorm ℝ (EuclideanSpace ℝ (Fin 2))) (g s : EuclideanSpace ℝ (Fin 2)),
      (∀ v, ‖v‖ ≤ p v) ∧
      ConnGouldToint.Chapter06.IsCauchyPoint
        (ConnGouldToint.Chapter06.quadraticModel 0 g 0) p g 1 s ∧
      -ConnGouldToint.Chapter06.quadraticModel 0 g 0 s <
        (1 / 2) * dualNorm p g * min (dualNorm p g / scaledQuadraticCurvature p 0) 1 := by
  let V := EuclideanSpace ℝ (Fin 2)
  let g : V := WithLp.toLp 2 (fun _ => 1)
  let z : V := EuclideanSpace.single 0 1
  let p : Seminorm ℝ V := normSeminorm ℝ V +
    (normSeminorm ℝ ℝ).comp ((10 : ℝ) • PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 1)
  have hp (x : V) : p x = ‖x‖ + |10 * x (1 : Fin 2)| := by
    simp [p, Real.norm_eq_abs, smul_eq_mul, PiLp.projₗ]
    rfl
  have hn (x : V) : ‖x‖ ≤ p x := by rw [hp]; exact le_add_of_nonneg_right (abs_nonneg _)
  have hpg : 10 ≤ p g := by
    rw [hp]
    have hg : g (1 : Fin 2) = 1 := rfl
    rw [hg, mul_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hpg₀ : 0 < p g := (by norm_num : (0 : ℝ) < 10).trans_le hpg
  have hgg : inner ℝ g g = 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    change (∑ _ : Fin 2, (1 : ℝ) ^ 2) = _
    norm_num
  have hz : p z = 1 := by
    rw [hp]
    have hzn : ‖z‖ = 1 := by
      change ‖(PiLp.single 2 (0 : Fin 2) 1 : EuclideanSpace ℝ (Fin 2))‖ = 1
      rw [PiLp.norm_single]
      norm_num
    simp [z, hzn]
  have hgz : inner ℝ g z = 1 := by
    rw [EuclideanSpace.inner_single_right]
    simp [g]
  have hdual : 1 ≤ dualNorm p g := by
    have hbound : BddAbove (Set.range fun x : V => |inner ℝ g x| / p x) :=
      ⟨‖g‖, by
        rintro _ ⟨x, rfl⟩
        simpa only [one_mul] using inner_ratio_le zero_le_one
          (fun v => by simpa only [one_mul] using hn v) x g⟩
    have h := le_ciSup hbound z
    rw [hgz, hz, abs_one, div_one] at h
    exact h
  let s := (-(p g)⁻¹) • g
  have hm (t : ℝ) : ConnGouldToint.Chapter06.quadraticModel 0 g 0 ((-t) • g) = -2 * t := by
    simp only [ConnGouldToint.Chapter06.quadraticModel, inner_smul_right, hgg,
      LinearMap.zero_apply, inner_zero_right, mul_zero, add_zero, zero_add]
    ring
  refine ⟨p, g, s, hn, ⟨?_, ?_⟩, ?_⟩
  · apply isMinOn_iff.mpr
    rintro _ ⟨t, ht, rfl, hfeas⟩
    rw [show s = (-(p g)⁻¹) • g from rfl, hm, hm]
    have htp : t * p g ≤ 1 := by
      simpa only [map_smul_eq_mul, norm_neg, Real.norm_of_nonneg ht] using hfeas
    have hh := (le_div_iff₀ hpg₀).mpr htp
    rw [one_div] at hh
    linarith
  · refine ⟨(p g)⁻¹, inv_nonneg.mpr hpg₀.le, rfl, ?_⟩
    rw [show s = (-(p g)⁻¹) • g from rfl, map_smul_eq_mul, norm_neg,
      Real.norm_of_nonneg (inv_nonneg.mpr hpg₀.le), inv_mul_cancel₀ hpg₀.ne']
  · have hβ : scaledQuadraticCurvature p 0 = 1 := by simp [scaledQuadraticCurvature]
    rw [show s = (-(p g)⁻¹) • g from rfl, hm, hβ, div_one, min_eq_right hdual, mul_one]
    have hlim : (p g)⁻¹ ≤ (1 / 10 : ℝ) := by
      rw [← one_div]
      exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hpg
    linarith

/-- The Euclidean-to-trust-region norm ratio (8.1.50) for the
modified Cauchy direction. -/
noncomputable def modifiedCauchyNormFactor (p : Seminorm ℝ E) (d : E) : ℝ :=
  ‖d‖ / p d

/-- Dividing the gradient-angle inequality by the trust-region norm
gives (8.1.49). -/
theorem modifiedCauchyNormFactor_mul_le (p : Seminorm ℝ E) {g d : E} {ε : ℝ}
    (hd : 0 < p d) (hangle : ε * ‖g‖ * ‖d‖ ≤ |inner ℝ g d|) :
    modifiedCauchyNormFactor p d * ε * ‖g‖ ≤ |inner ℝ g d| / p d := by
  apply (le_div_iff₀ hd).mpr
  unfold modifiedCauchyNormFactor
  calc
    ‖d‖ / p d * ε * ‖g‖ * p d = ε * ‖g‖ * ‖d‖ := by
      field_simp
    _ ≤ _ := hangle

/-- Corollary 8.1.11. A gradient-related direction and uniform norm
comparison convert the accepted trust-region length to the Euclidean
parameter bound. The displayed constant is conservative. -/
theorem corollary_8_1_11 {m : E → ℝ} (p : Seminorm ℝ E) {x d g : E}
    {Δ q b β β₀ K ε : ℝ} (hΔ : 0 < Δ) (hq : 0 < q) (hq₁ : q < 1)
    (hb : 0 < b) (hb₁ : b < 1 / 2) (hβ : 0 < β) (hβ₀ : 0 < β₀) (hK : 1 ≤ K)
    (hd : 0 < p d) (hp : p d ≤ K * ‖d‖) (hcomp : β ≤ K ^ 2 * β₀)
    (hangle : ε * ‖g‖ * ‖d‖ ≤ |inner ℝ g d|)
    (hdescent : inner ℝ g d < 0) (hgrad : fderiv ℝ m x d = inner ℝ g d)
    (hm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ m z)
    (hDm : ∀ z ∈ p.closedBall x Δ, DifferentiableAt ℝ (fderiv ℝ m) z)
    (hcurv : ∀ z ∈ p.closedBall x Δ, fderiv ℝ (fderiv ℝ m) z d d ≤ β * (p d) ^ 2) :
    ∃ j, ModifiedCauchyAccepted m p x d g Δ q b j ∧
      (∀ i < j, ¬ ModifiedCauchyAccepted m p x d g Δ q b i) ∧
      (min (2 * q * (1 - b)) 1 / K ^ 4) * min (ε * ‖g‖ / (β₀ * ‖d‖)) (Δ / p d) ≤
        q ^ j * Δ / p d := by
  obtain ⟨j, hj, hmin, hlen, -⟩ :=
    theorem_8_1_10 p hΔ hq hq₁ hb hb₁ hβ hd hdescent hgrad hm hDm hcurv
  let C := min (2 * q * (1 - b)) 1
  have hC : 0 ≤ C := le_min
    (mul_nonneg (mul_nonneg (by norm_num) hq.le) (by linarith)) zero_le_one
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr (fun h => hd.ne' (by simp [h]))
  have hK₄ : 0 < K ^ 4 := pow_pos hK₀ _
  have hcomp' : β * (p d) ^ 2 ≤ K ^ 4 * β₀ * ‖d‖ ^ 2 := calc
    _ ≤ (K ^ 2 * β₀) * (K * ‖d‖) ^ 2 :=
      mul_le_mul hcomp (pow_le_pow_left₀ hd.le hp 2) (sq_nonneg _) (by positivity)
    _ = _ := by ring
  have hfirst : (ε * ‖g‖ / (β₀ * ‖d‖)) / K ^ 4 ≤
      |inner ℝ g d| / p d / β / p d := by
    have hquot := div_le_div₀ (abs_nonneg _) hangle
      (mul_pos hβ (sq_pos_of_pos hd)) hcomp'
    have heq₁ : (ε * ‖g‖ / (β₀ * ‖d‖)) / K ^ 4 =
        ε * ‖g‖ * ‖d‖ / (K ^ 4 * β₀ * ‖d‖ ^ 2) := by
      field_simp [hK₀.ne', hβ₀.ne', hdn.ne']
    have heq₂ : |inner ℝ g d| / p d / β / p d = |inner ℝ g d| / (β * (p d) ^ 2) := by
      field_simp [hd.ne', hβ.ne']
    rwa [heq₁, heq₂]
  have hsecond : (Δ / p d) / K ^ 4 ≤ Δ / p d := by
    apply div_le_self (div_nonneg hΔ.le hd.le)
    exact one_le_pow₀ hK
  have hsmall : min (ε * ‖g‖ / (β₀ * ‖d‖)) (Δ / p d) / K ^ 4 ≤
      min (|inner ℝ g d| / p d / β / p d) (Δ / p d) := by
    apply le_min
    · exact (div_le_div_of_nonneg_right (min_le_left _ _) hK₄.le).trans hfirst
    · exact (div_le_div_of_nonneg_right (min_le_right _ _) hK₄.le).trans hsecond
  refine ⟨j, hj, hmin, ?_⟩
  change C / K ^ 4 * min _ _ ≤ _
  calc
    _ = C * (min (ε * ‖g‖ / (β₀ * ‖d‖)) (Δ / p d) / K ^ 4) := by ring
    _ ≤ C * min (|inner ℝ g d| / p d / β / p d) (Δ / p d) :=
      mul_le_mul_of_nonneg_left hsmall hC
    _ = (C * min (|inner ℝ g d| / p d / β) Δ) / p d := by
      simp only [div_eq_mul_inv]
      rw [← min_mul_of_nonneg _ _ (inv_nonneg.mpr hd.le)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hlen hd.le

private theorem negative_direction_near_limit [FiniteDimensional ℝ E]
    {p : ℕ → Seminorm ℝ E} {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hAN : ∀ k w, ‖w‖ ≤ K * p k w) {x : ℕ → E} {z u : E}
    (hu : u ∈ curvatureDirections p ε) {Q : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hcont : ContinuousAt (fun y => Q y u u) z)
    {M : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {τ e : ℕ → ℝ}
    (hcurv : ∀ k w, w ≠ 0 → τ k ≤ M k w w / (p k w) ^ 2)
    (herr : ∀ k w, w ≠ 0 → |Q (x k) w w - M k w w| / (p k w) ^ 2 ≤ e k)
    (he : Tendsto e atTop (𝓝 0)) (hn : Q z u u < 0) :
    ∃ a > 0, ∃ r > 0, ∀ᶠ k in atTop, dist (x k) z < r → τ k ≤ -a := by
  have hu₀ : u ≠ 0 := fun h => by simp [h] at hn
  obtain ⟨C, hC, hcomp⟩ := uniform_norm_comparison_on_curvatureDirections p hε
  let B := C * ‖u‖
  have hB : 0 < B := mul_pos hC (norm_pos_iff.mpr hu₀)
  let a := -Q z u u / (4 * B ^ 2)
  have ha : 0 < a := div_pos (neg_pos.mpr hn) (by positivity)
  have haeq : (2 * a) * B ^ 2 = -Q z u u / 2 := by
    dsimp [a]
    field_simp [hB.ne']
    ring
  have hlocal : ∀ᶠ y in 𝓝 z, Q y u u < Q z u u / 2 :=
    hcont.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  refine ⟨a, ha, r, hr, ?_⟩
  filter_upwards [he.eventually (gt_mem_nhds ha)] with k hek hk
  have hpu := norm_pos_of_comparison hK (hAN k) hu₀
  have hpow := sq_pos_of_pos hpu
  have hp := pow_le_pow_left₀ hpu.le (hcomp k u hu) 2
  have hF := hnear (x k) hk
  have hFt : Q (x k) u u / (p k u) ^ 2 ≤ -(2 * a) := by
    apply (div_le_iff₀ hpow).mpr
    have hle := mul_le_mul_of_nonpos_left hp (show -(2 * a) ≤ 0 by linarith)
    rw [neg_mul, haeq] at hle
    linarith
  have hq := (le_div_iff₀ hpow).mp (hcurv k u hu₀)
  have hm := (div_le_iff₀ hpow).mp (herr k u hu₀)
  have hf := (div_le_iff₀ hpow).mp hFt
  have hτ : τ k ≤ -(2 * a) + e k := by
    apply le_of_mul_le_mul_right _ hpow
    nlinarith only [hq, hm, hf, neg_abs_le (Q (x k) u u - M k u u)]
  linarith

omit [InnerProductSpace ℝ E] in
private theorem clipped_curvature_eventually_near {x : ℕ → E} {z : E} {τ : ℕ → ℝ}
    {a cap : ℝ} :
    (∃ r > 0, ∀ᶠ k in atTop, dist (x k) z < r → τ k ≤ -a) →
    ∃ r > 0, ∀ᶠ k in atTop, dist (x k) z < r → max (-cap) (τ k) ≤ -min cap a := by
  rintro ⟨r, hr, h⟩
  refine ⟨r, hr, h.mono fun k hk hdist => ?_⟩
  exact max_le (neg_le_neg (min_le_left _ _))
    ((hk hdist).trans (neg_le_neg (min_le_right _ _)))

open ConnGouldToint.Chapter06 in
omit [InnerProductSpace ℝ E] in
private theorem btr_step_norm_le_of_comparison [NormedSpace ℝ E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {K : ℝ} (hK : 0 ≤ K)
    (hAN : ∀ k u, ‖u‖ ≤ K * run.p k u) (k : ℕ) :
    ‖run.s k‖ ≤ K * run.Δ k := by
  have h := run.feasible k
  change run.p k (run.x k + run.s k - run.x k) ≤ run.Δ k at h
  rw [add_sub_cancel_left] at h
  exact (hAN k _).trans (mul_le_mul_of_nonneg_left h hK)

open ConnGouldToint.Chapter06 in
/-- Theorem 8.1.4 in directional form. An isolated limit has nonnegative
objective Hessian on every cone from (8.1.6). The first-order convergence
of the chosen criticality measure is the input from Section 8.1.2. -/
theorem theorem_8_1_4 [FiniteDimensional ℝ E] [ProperSpace E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    (hiso : ∃ r > (0 : ℝ), ∀ y, dist y z < r → ∀ i : ℕ → ℕ,
      StrictMono i → Tendsto (run.x ∘ i) atTop (𝓝 y) → y = z)
    {π τ e : ℕ → ℝ} (hπ : Tendsto π atTop (𝓝 0))
    (hf : ContDiff ℝ 2 f)
    {κ K cap : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hcap : 0 < cap)
    (hAN : ∀ k u, ‖u‖ ≤ K * run.p k u)
    (hcurv : ∀ k u, u ≠ 0 → τ k ≤
      fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u / (run.p k u) ^ 2)
    (herror : ∀ k u, u ≠ 0 →
      |fderiv ℝ (fderiv ℝ f) (run.x k) u u -
       fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u| / (run.p k u) ^ 2 ≤ e k)
    (he : Tendsto e atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (Set.range f)) (herr : smallRadiusModelAgreement run)
    (hsecond : ∀ k, HasCappedNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ cap) :
    Tendsto π atTop (𝓝 0) ∧ ∀ ε > 0, ∀ u ∈ curvatureDirections run.p ε,
      0 ≤ fderiv ℝ (fderiv ℝ f) z u u := by
  refine ⟨hπ, fun ε hε u hu => ?_⟩
  by_contra! hn
  have hC : ContinuousAt (fun y => fderiv ℝ (fderiv ℝ f) y u u) z := by
    have h := ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_right
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous
    fun_prop
  obtain ⟨a, ha, hlocal⟩ := negative_direction_near_limit hε hK.le hAN hu hC
    hcurv herror he hn
  have hstep := btr_step_norm_le_of_comparison run hK.le hAN
  exact not_negative_curvature_near_isolated_limit run hj hz hiso (lt_min hcap ha) hκ hK
    hval hlower herr hstep (fun k => negativeCurvatureDecrease_clipped (hsecond k))
    (clipped_curvature_eventually_near hlocal)

open ConnGouldToint.Chapter06 in
/-- Objective curvature in Theorem 8.1.5. Forced expansion excludes negative
curvature in each cone direction with persistent norm comparison. -/
theorem theorem_8_1_5_directional [FiniteDimensional ℝ E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    {τ e : ℕ → ℝ} (hf : ContDiff ℝ 2 f)
    {κ K cap γ₃ γ₄ capExpand : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hcap : 0 < cap)
    (hAN : ∀ k u, ‖u‖ ≤ K * run.p k u)
    (hcurv : ∀ k u, u ≠ 0 → τ k ≤
      fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u / (run.p k u) ^ 2)
    (herror : ∀ k u, u ≠ 0 →
      |fderiv ℝ (fderiv ℝ f) (run.x k) u u -
       fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u| / (run.p k u) ^ 2 ≤ e k)
    (he : Tendsto e atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (Set.range f)) (herr : smallRadiusModelAgreement run)
    (hsecond : ∀ k, HasCappedNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ cap)
    (hexpand : HasForcedRadiusExpansion run γ₃ γ₄ capExpand) :
    ∀ ε > 0, ∀ u ∈ curvatureDirections run.p ε,
      0 ≤ fderiv ℝ (fderiv ℝ f) z u u := by
  have hstep := btr_step_norm_le_of_comparison run hK.le hAN
  have hexclude (a : ℝ) (ha : 0 < a)
      (hlocal : ∃ r > 0, ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -a) : False :=
    not_negative_curvature_near_limit_of_forced_expansion run hj hz (lt_min hcap ha) hκ hK
      hval hlower herr hstep (fun k => negativeCurvatureDecrease_clipped (hsecond k))
      hexpand (clipped_curvature_eventually_near hlocal)
  intro ε hε u hu
  by_contra! hn
  have hC : ContinuousAt (fun y => fderiv ℝ (fderiv ℝ f) y u u) z := by
    have h := ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).fderiv_right
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuous
    fun_prop
  obtain ⟨a, ha, hlocal⟩ := negative_direction_near_limit hε hK.le hAN hu hC
    hcurv herror he hn
  exact hexclude a ha hlocal


open ConnGouldToint.Chapter06 in
/-- Corrected Theorem 8.1.5 in directional form. Forced expansion excludes
negative objective curvature in every direction with persistent norm
comparison. For the scaled-model liminf, local persistence supplies the
negative-curvature bound at the intervening iterations of the expansion
argument. A bound along the convergent subsequence alone gives no such
bound when the trust-region norms vary. -/
theorem theorem_8_1_5 [FiniteDimensional ℝ E]
    {P : BTRParams} {f : E → ℝ} {sufficient : ℕ → (E → ℝ) → E → E → Prop}
    (run : BTRRun f P sufficient) {z : E}
    {j : ℕ → ℕ} (hj : StrictMono j) (hz : Tendsto (run.x ∘ j) atTop (𝓝 z))
    {τ e : ℕ → ℝ} (hf : ContDiff ℝ 2 f)
    {κ K cap γ₃ γ₄ capExpand : ℝ} (hκ : 0 < κ) (hK : 0 < K) (hcap : 0 < cap)
    (hAN : ∀ k u, ‖u‖ ≤ K * run.p k u)
    (hcurv : ∀ k u, u ≠ 0 → τ k ≤
      fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u / (run.p k u) ^ 2)
    (herror : ∀ k u, u ≠ 0 →
      |fderiv ℝ (fderiv ℝ f) (run.x k) u u -
       fderiv ℝ (fderiv ℝ (run.model k)) (run.x k) u u| / (run.p k u) ^ 2 ≤ e k)
    (he : Tendsto e atTop (𝓝 0))
    (hval : ∀ k, f (run.x k) = run.model k (run.x k))
    (hlower : BddBelow (Set.range f)) (herr : smallRadiusModelAgreement run)
    (hsecond : ∀ k, HasCappedNegativeCurvatureDecrease (run.model k) (run.x k) (run.s k)
      (τ k) (run.Δ k) κ cap)
    (hexpand : HasForcedRadiusExpansion run γ₃ γ₄ capExpand)
    (hτb : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) (τ ∘ j))
    (hpersist : ∀ a > (0 : ℝ), (∃ᶠ i in atTop, τ (j i) ≤ -a) →
      ∃ b > 0, ∃ r > 0, ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -b) :
    0 ≤ liminf (τ ∘ j) atTop ∧ ∀ ε > 0, ∀ u ∈ curvatureDirections run.p ε,
      0 ≤ fderiv ℝ (fderiv ℝ f) z u u := by
  have hstep := btr_step_norm_le_of_comparison run hK.le hAN
  have hexclude (a : ℝ) (ha : 0 < a)
      (hlocal : ∃ r > 0, ∀ᶠ k in atTop, dist (run.x k) z < r → τ k ≤ -a) : False :=
    not_negative_curvature_near_limit_of_forced_expansion run hj hz (lt_min hcap ha) hκ hK
      hval hlower herr hstep (fun k => negativeCurvatureDecrease_clipped (hsecond k))
      hexpand (clipped_curvature_eventually_near hlocal)
  constructor
  · by_contra! hn
    let a := -liminf (τ ∘ j) atTop / 2
    have ha : 0 < a := half_pos (neg_pos.mpr hn)
    have hfreq : ∃ᶠ i in atTop, τ (j i) ≤ -a := by
      by_contra! hfail
      have hl := le_liminf_of_le hτb (hfail.mono fun i hi => hi.le)
      dsimp [a] at hl
      linarith
    obtain ⟨b, hb, hlocal⟩ := hpersist a ha hfreq
    exact hexclude b hb hlocal
  · exact theorem_8_1_5_directional run hj hz hf hκ hK hcap hAN hcurv herror he
      hval hlower herr hsecond hexpand

section ReducedMatrices

open Matrix

/-- The least eigenvalue of a nonempty symmetric matrix. -/
noncomputable def matrixLeastEigenvalue {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℝ :=
  ⨅ i, hA.eigenvalues i

/-- Rayleigh comparison in arbitrary basis coordinates. The factor from the
basis map is needed because its columns need not be orthonormal. -/
theorem matrixLeastEigenvalue_lower_of_unit_directions
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (Z : EuclideanSpace ℝ n →L[ℝ] E) {U : Set E}
    (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    (Q : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ v : EuclideanSpace ℝ n, (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v) =
      Q (Z v) (Z v))
    {a : ℝ} (ha : 0 ≤ a) (hQ : ∀ u ∈ U, -a ≤ Q u u) :
    -a * ‖Z‖ ^ 2 ≤ matrixLeastEigenvalue A hA := by
  apply le_ciInf
  intro i
  let v := hA.eigenvectorBasis i
  have hv : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hval : hA.eigenvalues i = Q (Z v) (Z v) := by
    have he := hA.eigenvalues_eq i
    change hA.eigenvalues i = RCLike.re ((star (WithLp.ofLp v)) ⬝ᵥ (A *ᵥ WithLp.ofLp v)) at he
    simpa only [star_trivial, RCLike.re_to_real, hform] using he
  rw [hval]
  by_cases hz : Z v = 0
  · rw [hz]
    simp only [map_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)
  have hpos := norm_pos_iff.mpr hz
  have hnorm : ‖Z v‖ ≤ ‖Z‖ := by simpa only [hv, mul_one] using Z.le_opNorm v
  have hscaled := mul_le_mul_of_nonneg_right (hQ _ (hZ v hz)) (sq_nonneg ‖Z v‖)
  have he : Q (‖Z v‖⁻¹ • Z v) (‖Z v‖⁻¹ • Z v) * ‖Z v‖ ^ 2 = Q (Z v) (Z v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp [hpos.ne']
  rw [he] at hscaled
  exact (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hpos.le hnorm 2)
    (neg_nonpos.mpr ha)).trans hscaled

private theorem reduced_lower_of_infimum {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Z : EuclideanSpace ℝ n →L[ℝ] E}
    {U : Set E} (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    {Q : E →L[ℝ] E →L[ℝ] ℝ} (hbound : BddBelow (Set.range fun u : U => Q u u))
    (hform : ∀ v : EuclideanSpace ℝ n, (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v) =
      Q (Z v) (Z v))
    {a : ℝ} (ha : 0 ≤ a) (hQ : -a ≤ ⨅ u : U, Q u u) :
    -a * ‖Z‖ ^ 2 ≤ matrixLeastEigenvalue A hA :=
  matrixLeastEigenvalue_lower_of_unit_directions hA Z hZ Q hform ha
    (fun u hu => hQ.trans (ciInf_le hbound ⟨u, hu⟩))

/-- Lemma 8.1.1, basis-matrix formulation. Apply the directional conclusion
to the normalized images of the coordinates of the basis matrix. -/
theorem lemma_8_1_1_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : ℕ → Matrix n n ℝ} (hA : ∀ k, (A k).IsHermitian)
    {Z : EuclideanSpace ℝ n →L[ℝ] E} {U : Set E}
    (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    {Q : ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    (hbound : ∀ k, BddBelow (Set.range fun u : U => Q k u u))
    (hform : ∀ k (v : EuclideanSpace ℝ n), (WithLp.ofLp v) ⬝ᵥ (A k *ᵥ WithLp.ofLp v) =
      Q k (Z v) (Z v))
    (hQb : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun k => ⨅ u : U, Q k u u))
    (hQ : 0 ≤ liminf (fun k => ⨅ u : U, Q k u u) atTop)
    (hEb : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·)
      (fun k => matrixLeastEigenvalue (A k) (hA k))) :
    0 ≤ liminf (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop := by
  by_contra! hn
  let L := liminf (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop
  let a := -L / (2 * (‖Z‖ ^ 2 + 1))
  have ha : 0 < a := div_pos (neg_pos.mpr hn) (by positivity)
  have hev := eventually_lt_of_lt_liminf ((neg_lt_zero.mpr ha).trans_le hQ) hQb
  have hle : ∀ᶠ k in atTop, -a * ‖Z‖ ^ 2 ≤ matrixLeastEigenvalue (A k) (hA k) :=
    hev.mono fun k hk => reduced_lower_of_infimum (hA k) hZ (hbound k) (hform k) ha.le hk.le
  have hL : -a * ‖Z‖ ^ 2 ≤ L := le_liminf_of_le hEb hle
  have hEq : (2 * a) * (‖Z‖ ^ 2 + 1) = -L := by dsimp [a]; field_simp
  nlinarith only [hL, hEq, ha, mul_nonneg ha.le (sq_nonneg ‖Z‖)]

/-- Theorem 8.1.3, basis-matrix formulation. Frequent lower bounds on the
directional infimum transfer to the least reduced eigenvalue. -/
theorem theorem_8_1_3_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : ℕ → Matrix n n ℝ} (hA : ∀ k, (A k).IsHermitian)
    {Z : EuclideanSpace ℝ n →L[ℝ] E} {U : Set E}
    (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    {Q : ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    (hbound : ∀ k, BddBelow (Set.range fun u : U => Q k u u))
    (hform : ∀ k (v : EuclideanSpace ℝ n), (WithLp.ofLp v) ⬝ᵥ (A k *ᵥ WithLp.ofLp v) =
      Q k (Z v) (Z v))
    (hQb : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) (fun k => ⨅ u : U, Q k u u))
    (hQ : 0 ≤ limsup (fun k => ⨅ u : U, Q k u u) atTop)
    (hEb : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·)
      (fun k => matrixLeastEigenvalue (A k) (hA k))) :
    0 ≤ limsup (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop := by
  by_contra! hn
  let L := limsup (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop
  let a := -L / (2 * (‖Z‖ ^ 2 + 1))
  have ha : 0 < a := div_pos (neg_pos.mpr hn) (by positivity)
  have hfreq : ∃ᶠ k in atTop, -a < ⨅ u : U, Q k u u := by
    by_contra! hbad
    exact (neg_lt_zero.mpr ha).not_ge (hQ.trans (limsup_le_of_le hQb hbad))
  have hle : ∃ᶠ k in atTop, -a * ‖Z‖ ^ 2 ≤ matrixLeastEigenvalue (A k) (hA k) :=
    hfreq.mono fun k hk => reduced_lower_of_infimum (hA k) hZ (hbound k) (hform k) ha.le hk.le
  have hL : -a * ‖Z‖ ^ 2 ≤ L := le_limsup_of_frequently_le hle hEb
  have hEq : (2 * a) * (‖Z‖ ^ 2 + 1) = -L := by dsimp [a]; field_simp
  nlinarith only [hL, hEq, ha, mul_nonneg ha.le (sq_nonneg ‖Z‖)]

/-- The matrix conclusion of Theorem 8.1.4 follows from directional
nonnegativity at the isolated limit. -/
theorem theorem_8_1_4_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (Z : EuclideanSpace ℝ n →L[ℝ] E)
    {U : Set E} (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    (Q : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ v : EuclideanSpace ℝ n, (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v) =
      Q (Z v) (Z v))
    (hQ : ∀ u ∈ U, 0 ≤ Q u u) :
    0 ≤ matrixLeastEigenvalue A hA := by
  simpa only [neg_zero, zero_mul] using
    matrixLeastEigenvalue_lower_of_unit_directions hA Z hZ Q hform (a := 0) le_rfl
      (fun u hu => by simpa only [neg_zero] using hQ u hu)

/-- The matrix liminf conclusion of Theorem 8.1.5. Continuity of the
objective Hessian along the convergent subsequence gives uniform convergence
of its quadratic form on the unit directions in the cone. -/
theorem theorem_8_1_5_matrix {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : ℕ → Matrix n n ℝ} (hA : ∀ k, (A k).IsHermitian)
    {Z : EuclideanSpace ℝ n →L[ℝ] E} {U : Set E}
    (hZ : ∀ v, Z v ≠ 0 → ‖Z v‖⁻¹ • Z v ∈ U)
    (hunit : ∀ u ∈ U, ‖u‖ = 1)
    {Q : ℕ → E →L[ℝ] E →L[ℝ] ℝ} {Q₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (ht : Tendsto Q atTop (𝓝 Q₀))
    (hQ₀ : ∀ u ∈ U, 0 ≤ Q₀ u u)
    (hform : ∀ k (v : EuclideanSpace ℝ n), (WithLp.ofLp v) ⬝ᵥ (A k *ᵥ WithLp.ofLp v) =
      Q k (Z v) (Z v))
    (hEb : (atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·)
      (fun k => matrixLeastEigenvalue (A k) (hA k))) :
    0 ≤ liminf (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop := by
  by_contra! hn
  let L := liminf (fun k => matrixLeastEigenvalue (A k) (hA k)) atTop
  let a := -L / (2 * (‖Z‖ ^ 2 + 1))
  have ha : 0 < a := div_pos (neg_pos.mpr hn) (by positivity)
  have hev := (tendsto_iff_norm_sub_tendsto_zero.mp ht).eventually (gt_mem_nhds ha)
  have hle : ∀ᶠ k in atTop, -a * ‖Z‖ ^ 2 ≤ matrixLeastEigenvalue (A k) (hA k) := by
    filter_upwards [hev] with k hk
    apply matrixLeastEigenvalue_lower_of_unit_directions (hA k) Z hZ (Q k) (hform k) ha.le
    intro u hu
    let D := Q k - Q₀
    have hb := ((D u).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg u))
    rw [hunit u hu, mul_one, mul_one, Real.norm_eq_abs] at hb
    have hh : -‖D‖ ≤ D u u := (neg_le_neg hb).trans (neg_abs_le _)
    change -‖Q k - Q₀‖ ≤ Q k u u - Q₀ u u at hh
    linarith [hQ₀ u hu]
  have hL : -a * ‖Z‖ ^ 2 ≤ L := le_liminf_of_le hEb hle
  have hEq : (2 * a) * (‖Z‖ ^ 2 + 1) = -L := by dsimp [a]; field_simp
  nlinarith only [hL, hEq, ha, mul_nonneg ha.le (sq_nonneg ‖Z‖)]

end ReducedMatrices

end ConnGouldToint.Chapter08
