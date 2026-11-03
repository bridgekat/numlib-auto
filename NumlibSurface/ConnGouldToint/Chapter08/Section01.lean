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

end ConnGouldToint.Chapter08
