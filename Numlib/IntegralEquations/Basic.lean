import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Integral operators on a compact interval

The Fredholm, Urysohn and Volterra integral operators on the Banach space `C(Set.Icc a b, ℝ)` of
continuous real functions on a compact interval, and the estimates on which the classical existence
theorems for integral equations of the second kind rest.

* `IntegralOperator.fredholm` is the bounded operator `u ↦ (x ↦ ∫ y in a..b, k (x, y) * u y)`
  attached to a continuous kernel, and `IntegralOperator.norm_fredholm` computes its operator norm
  as `⨆ x, ∫ y in a..b, |k (x, y)|`.
* `IntegralOperator.urysohn` is its nonlinear companion `u ↦ (x ↦ ∫ y in a..b, k (x, y, u y))`,
  Lipschitz with constant `L * (b - a)` when the kernel is `L`-Lipschitz in its last argument
  (`IntegralOperator.lipschitzWith_urysohn`).
* `IntegralOperator.volterra` is the Volterra operator `u ↦ (t ↦ ∫ s in a..t, k (t, s, u s))`, whose
  iterates contract like `(M (b - a)) ^ m / m !` (`IntegralOperator.norm_iterate_volterra_sub_le`),
  so that some power of it is a contraction however large the Lipschitz constant `M` is.
* `IntegralOperator.Bielecki` is the same vector space under the weighted norm
  `‖u‖ = ⨆ t, exp (-(β (t - a))) * |u t|`, in which a Volterra operator is already a contraction,
  with constant `M / β` (`IntegralOperator.contractingWith_volterra_bielecki`).

Every operator here carries a proof `hab : a ≤ b`, which is what lets the real integration variable
be clamped back into `Set.Icc a b` by `Set.projIcc`.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^kress]: Rainer Kress, *Linear Integral Equations*, 3rd edition, Applied Mathematical Sciences 82,
  Springer, 2014.
-/

open MeasureTheory Metric Set

open scoped Interval Nat NNReal

namespace IntegralOperator

variable {a b : ℝ}

/-! ### Clamping the integration variable -/

section Clamp

variable (hab : a ≤ b)

@[fun_prop]
theorem continuous_projIcc : Continuous (projIcc a b hab) :=
  continuous_induced_rng.2 (continuous_const.max (continuous_const.min continuous_id))

/-- A continuous function on `Set.Icc a b` composed with the clamping map is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_apply_projIcc (u : C(Icc a b, ℝ)) :
    Continuous fun y : ℝ => u (projIcc a b hab y) :=
  u.continuous.comp (continuous_projIcc hab)

theorem apply_projIcc_of_mem (u : C(Icc a b, ℝ)) {y : ℝ} (hy : y ∈ Icc a b) :
    u (projIcc a b hab y) = u ⟨y, hy⟩ := by
  rw [projIcc_of_mem]

@[simp]
theorem coe_projIcc_of_mem {y : ℝ} (hy : y ∈ Icc a b) :
    ((projIcc a b hab y : Icc a b) : ℝ) = y := by
  rw [projIcc_of_mem hab hy]

end Clamp

/-! ### The Urysohn and Fredholm operators -/

section Fredholm

variable (hab : a ≤ b)

/-- The Urysohn integral operator of a continuous kernel `k : Icc a b × Icc a b × ℝ → ℝ`, the
nonlinear Fredholm operator `u ↦ (x ↦ ∫ y in a..b, k (x, y, u y))` on `C(Icc a b, ℝ)`
(Atkinson and Han, *Theoretical Numerical Analysis*, (5.2.9)). -/
noncomputable def urysohn (k : C(Icc a b × Icc a b × ℝ, ℝ)) (u : C(Icc a b, ℝ)) :
    C(Icc a b, ℝ) where
  toFun x := ∫ y in a..b, k (x, projIcc a b hab y, u (projIcc a b hab y))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : Icc a b) (y : ℝ) => k (x, projIcc a b hab y, u (projIcc a b hab y)))
    exact k.continuous.comp (by fun_prop)

@[simp]
theorem urysohn_apply (k : C(Icc a b × Icc a b × ℝ, ℝ)) (u : C(Icc a b, ℝ)) (x : Icc a b) :
    urysohn hab k u x = ∫ y in a..b, k (x, projIcc a b hab y, u (projIcc a b hab y)) :=
  rfl

/-- The Fredholm integral operator of a continuous kernel `k : Icc a b × Icc a b → ℝ`, as a bounded
linear operator `u ↦ (x ↦ ∫ y in a..b, k (x, y) * u y)` on `C(Icc a b, ℝ)`
(Atkinson and Han, *Theoretical Numerical Analysis*, (5.2.7)). -/
noncomputable def fredholm (k : C(Icc a b × Icc a b, ℝ)) :
    C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u =>
        { toFun := fun x => ∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y)
          continuous_toFun := by
            apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
              (f := fun (x : Icc a b) (y : ℝ) =>
                k (x, projIcc a b hab y) * u (projIcc a b hab y))
            exact (k.continuous.comp (by fun_prop)).mul (by fun_prop) }
      map_add' := fun u v => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        exact intervalIntegral.integral_congr fun y _ => by ring
      map_smul' := fun c u => by
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun y _ => by ring }
    (‖k‖ * (b - a)) fun u => by
      have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro x
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk]
      have hle : ∀ y ∈ Ι a b, ‖k (x, projIcc a b hab y) * u (projIcc a b hab y)‖ ≤ ‖k‖ * ‖u‖ := by
        intro y _
        rw [norm_mul]
        exact mul_le_mul (k.norm_coe_le_norm _) (u.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _)
      calc ‖∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y)‖
          ≤ ‖k‖ * ‖u‖ * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const hle
        _ = ‖k‖ * (b - a) * ‖u‖ := by rw [abs_of_nonneg hba]; ring

@[simp]
theorem fredholm_apply (k : C(Icc a b × Icc a b, ℝ)) (u : C(Icc a b, ℝ)) (x : Icc a b) :
    fredholm hab k u x = ∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y) :=
  rfl

/-- The Fredholm operator is the Urysohn operator of the kernel `(x, y, z) ↦ k (x, y) * z`. -/
theorem fredholm_eq_urysohn (k : C(Icc a b × Icc a b, ℝ)) (u : C(Icc a b, ℝ)) :
    fredholm hab k u = urysohn hab ⟨fun p => k (p.1, p.2.1) * p.2.2, by fun_prop⟩ u :=
  rfl

/-- Every row integral of the kernel bounds the operator norm of a Fredholm operator from below;
this is the easy half of `IntegralOperator.norm_fredholm`. -/
theorem norm_fredholm_le {k : C(Icc a b × Icc a b, ℝ)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, (∫ y in a..b, |k (x, projIcc a b hab y)|) ≤ C) : ‖fredholm hab k‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  have hint : (∫ y in a..b, |k (x, projIcc a b hab y) * u (projIcc a b hab y)|)
      ≤ ∫ y in a..b, |k (x, projIcc a b hab y)| * ‖u‖ := by
    refine intervalIntegral.integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun y _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (abs_nonneg _)
  calc ‖fredholm hab k u x‖
      = |∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y)| := rfl
    _ ≤ ∫ y in a..b, |k (x, projIcc a b hab y) * u (projIcc a b hab y)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ y in a..b, |k (x, projIcc a b hab y)| * ‖u‖ := hint
    _ = (∫ y in a..b, |k (x, projIcc a b hab y)|) * ‖u‖ := intervalIntegral.integral_mul_const _ _
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right (h x) (norm_nonneg u)

/-- **The operator norm of a Fredholm integral operator** is the largest row integral of its kernel,
`‖K‖ = max_x ∫ |k (x, y)| dy` (Atkinson and Han, *Theoretical Numerical Analysis*, (2.2.8)).

The lower bound comes from testing `K` against `y ↦ k (x₀, y) / (|k (x₀, y)| + ε)`, a continuous
function of norm at most one that approximates the sign of `k (x₀, ·)`. -/
theorem norm_fredholm (k : C(Icc a b × Icc a b, ℝ)) :
    ‖fredholm hab k‖ = ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)| := by
  have hne : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.2 hab⟩⟩
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  -- the row integral, as a continuous function of the row index
  set g : C(Icc a b, ℝ) :=
    { toFun := fun x => ∫ y in a..b, |k (x, projIcc a b hab y)|
      continuous_toFun := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun (x : Icc a b) (y : ℝ) => |k (x, projIcc a b hab y)|)
        exact (k.continuous.comp (by fun_prop)).abs } with hg
  have hgapp : ∀ x, g x = ∫ y in a..b, |k (x, projIcc a b hab y)| := fun _ => rfl
  have hgnonneg : ∀ x, 0 ≤ g x := fun x =>
    intervalIntegral.integral_nonneg hab fun y _ => abs_nonneg _
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty g.continuous.continuousOn
  have hmax : ∀ x, g x ≤ g x₀ := fun x => isMaxOn_iff.1 hx₀ x (mem_univ x)
  have hsup : ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)| = g x₀ :=
    le_antisymm (ciSup_le hmax) (le_ciSup ⟨g x₀, by rintro _ ⟨x, rfl⟩; exact hmax x⟩ x₀)
  rw [hsup]
  refine le_antisymm (norm_fredholm_le hab (hgnonneg x₀) hmax) ?_
  -- the lower bound: test against a continuous approximation of the sign of `k (x₀, ·)`
  have hlow : ∀ δ : ℝ, 0 < δ → g x₀ - δ * (b - a) ≤ ‖fredholm hab k‖ := by
    intro δ hδ
    have hpos : ∀ y : Icc a b, (0 : ℝ) < |k (x₀, y)| + δ := fun y =>
      add_pos_of_nonneg_of_pos (abs_nonneg _) hδ
    set w : C(Icc a b, ℝ) :=
      { toFun := fun y => k (x₀, y) / (|k (x₀, y)| + δ)
        continuous_toFun := Continuous.div (by fun_prop) (by fun_prop) fun y => (hpos y).ne' }
      with hw
    have hwapp : ∀ y : Icc a b, w y = k (x₀, y) / (|k (x₀, y)| + δ) := fun _ => rfl
    have hwnorm : ‖w‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro y
      rw [Real.norm_eq_abs, hwapp, abs_div, abs_of_pos (hpos y), div_le_one (hpos y)]
      linarith [abs_nonneg (k (x₀, y)), (abs_abs (k (x₀, y))).ge, (abs_abs (k (x₀, y))).le]
    have hpt : ∀ y ∈ Icc a b, |k (x₀, projIcc a b hab y)| - δ
        ≤ k (x₀, projIcc a b hab y) * w (projIcc a b hab y) := by
      intro y _
      have hden := hpos (projIcc a b hab y)
      rw [hwapp, ← mul_div_assoc, le_div_iff₀ hden]
      nlinarith [abs_mul_abs_self (k (x₀, projIcc a b hab y)), mul_pos hδ hδ]
    have hval : fredholm hab k w x₀
        = ∫ y in a..b, k (x₀, projIcc a b hab y) * w (projIcc a b hab y) := rfl
    have key : g x₀ - δ * (b - a) ≤ fredholm hab k w x₀ := by
      have h1 : (∫ y in a..b, (|k (x₀, projIcc a b hab y)| - δ))
          ≤ ∫ y in a..b, k (x₀, projIcc a b hab y) * w (projIcc a b hab y) :=
        intervalIntegral.integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
      rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const,
        smul_eq_mul] at h1
      rw [hgapp, hval]
      linarith
    calc g x₀ - δ * (b - a) ≤ fredholm hab k w x₀ := key
      _ ≤ ‖fredholm hab k w‖ := (fredholm hab k w).apply_le_norm x₀
      _ ≤ ‖fredholm hab k‖ * ‖w‖ := (fredholm hab k).le_opNorm w
      _ ≤ ‖fredholm hab k‖ := by nlinarith [norm_nonneg (fredholm hab k), norm_nonneg w]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hb1 : (0 : ℝ) < b - a + 1 := by linarith
  have hd : (0 : ℝ) < η / (b - a + 1) := by positivity
  have hsmall : η / (b - a + 1) * (b - a) ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb1]
    nlinarith
  linarith [hlow _ hd]

/-- **A Urysohn operator is Lipschitz** with constant `L (b - a)` when its kernel is `L`-Lipschitz
in its last argument, uniformly in the other two (Atkinson and Han, *Theoretical Numerical
Analysis*, Theorem 5.2.2). -/
theorem lipschitzWith_urysohn {k : C(Icc a b × Icc a b × ℝ, ℝ)} {L : ℝ≥0}
    (hk : ∀ x y : Icc a b, LipschitzWith L fun z => k (x, y, z)) :
    LipschitzWith (L * (b - a).toNNReal) (urysohn hab k) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have hcoe : ((L * (b - a).toNNReal : ℝ≥0) : ℝ) = L * (b - a) := by
    simp [Real.coe_toNNReal _ hba]
  rw [ContinuousMap.dist_le (by positivity), hcoe]
  intro x
  have hpt : ∀ y ∈ Icc a b,
      |k (x, projIcc a b hab y, u (projIcc a b hab y))
        - k (x, projIcc a b hab y, v (projIcc a b hab y))| ≤ L * dist u v := by
    intro y _
    have := (hk x (projIcc a b hab y)).dist_le_mul (u (projIcc a b hab y)) (v (projIcc a b hab y))
    rw [Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left (u.dist_apply_le_dist _) L.coe_nonneg)
  rw [Real.dist_eq]
  calc |urysohn hab k u x - urysohn hab k v x|
      = |∫ y in a..b, (k (x, projIcc a b hab y, u (projIcc a b hab y))
          - k (x, projIcc a b hab y, v (projIcc a b hab y)))| := by
        rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _)]; rfl
    _ ≤ ∫ y in a..b, |k (x, projIcc a b hab y, u (projIcc a b hab y))
          - k (x, projIcc a b hab y, v (projIcc a b hab y))| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ _y in a..b, (L : ℝ) * dist u v :=
        intervalIntegral.integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
    _ = L * (b - a) * dist u v := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring

end Fredholm

/-! ### The Volterra operator and the factorial estimate -/

section Volterra

variable (hab : a ≤ b)

/-- The kernel `(x, y, z) ↦ k (x, y) * z` of the linear integral operator with kernel `k`, so that
the linear operators are instances of the nonlinear ones. -/
def mulKernel (k : C(Icc a b × Icc a b, ℝ)) : C(Icc a b × Icc a b × ℝ, ℝ) :=
  ⟨fun p => k (p.1, p.2.1) * p.2.2, by fun_prop⟩

@[simp]
theorem mulKernel_apply (k : C(Icc a b × Icc a b, ℝ)) (x y : Icc a b) (z : ℝ) :
    mulKernel k (x, y, z) = k (x, y) * z :=
  rfl

/-- The Volterra integral operator of a continuous kernel `k : Icc a b × Icc a b × ℝ → ℝ`, the map
`u ↦ (t ↦ ∫ s in a..t, k (t, s, u s))` on `C(Icc a b, ℝ)` (Atkinson and Han, *Theoretical
Numerical Analysis*, Section 5.2.3). -/
noncomputable def volterra (k : C(Icc a b × Icc a b × ℝ, ℝ)) (u : C(Icc a b, ℝ)) :
    C(Icc a b, ℝ) where
  toFun t := ∫ s in a..(t : ℝ), k (t, projIcc a b hab s, u (projIcc a b hab s))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (t : Icc a b) (s : ℝ) => k (t, projIcc a b hab s, u (projIcc a b hab s)))
      (s := fun t : Icc a b => (t : ℝ)) (k.continuous.comp (by fun_prop))
    fun_prop

@[simp]
theorem volterra_apply (k : C(Icc a b × Icc a b × ℝ, ℝ)) (u : C(Icc a b, ℝ)) (t : Icc a b) :
    volterra hab k u t = ∫ s in a..(t : ℝ), k (t, projIcc a b hab s, u (projIcc a b hab s)) :=
  rfl

/-- The linear Volterra integral operator of a continuous kernel `k : Icc a b × Icc a b → ℝ`, the
bounded operator `u ↦ (t ↦ ∫ s in a..t, k (t, s) * u s)` on `C(Icc a b, ℝ)`. -/
noncomputable def volterraCLM (k : C(Icc a b × Icc a b, ℝ)) :
    C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => volterra hab (mulKernel k) u
      map_add' := fun u v => by
        ext t
        simp only [volterra_apply, mulKernel_apply, ContinuousMap.add_apply]
        rw [← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _)]
        exact intervalIntegral.integral_congr fun y _ => by ring
      map_smul' := fun c u => by
        ext t
        simp only [volterra_apply, mulKernel_apply, ContinuousMap.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun y _ => by ring }
    (‖k‖ * (b - a)) fun u => by
      have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro t
      simp only [LinearMap.coe_mk, AddHom.coe_mk, volterra_apply, mulKernel_apply]
      have hle : ∀ s ∈ Ι a (t : ℝ),
          ‖k (t, projIcc a b hab s) * u (projIcc a b hab s)‖ ≤ ‖k‖ * ‖u‖ := fun s _ => by
        rw [norm_mul]
        exact mul_le_mul (k.norm_coe_le_norm _) (u.norm_coe_le_norm _) (norm_nonneg _)
          (norm_nonneg _)
      have habs : |(t : ℝ) - a| ≤ b - a := by
        rw [abs_of_nonneg (by linarith [t.2.1])]
        linarith [t.2.2]
      calc ‖∫ s in a..(t : ℝ), k (t, projIcc a b hab s) * u (projIcc a b hab s)‖
          ≤ ‖k‖ * ‖u‖ * |(t : ℝ) - a| := intervalIntegral.norm_integral_le_of_norm_le_const hle
        _ ≤ ‖k‖ * ‖u‖ * (b - a) := mul_le_mul_of_nonneg_left habs (by positivity)
        _ = ‖k‖ * (b - a) * ‖u‖ := by ring

@[simp]
theorem volterraCLM_apply (k : C(Icc a b × Icc a b, ℝ)) (u : C(Icc a b, ℝ)) (t : Icc a b) :
    volterraCLM hab k u t = ∫ s in a..(t : ℝ), k (t, projIcc a b hab s) * u (projIcc a b hab s) :=
  rfl

/-- The linear Volterra operator is the Volterra operator of the kernel
`(t, s, z) ↦ k (t, s) * z`. -/
theorem coe_volterraCLM (k : C(Icc a b × Icc a b, ℝ)) :
    ⇑(volterraCLM hab k) = volterra hab (mulKernel k) :=
  rfl

/-- The factorial estimate of `IntegralOperator.norm_iterate_volterra_sub_le`, pointwise in `t`:
the error of the `m`-th Volterra iterate at `t` is controlled by `(M (t - a)) ^ m / m !`. -/
theorem abs_iterate_volterra_sub_apply_le {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (u v : C(Icc a b, ℝ)) (m : ℕ)
    (t : Icc a b) :
    |(volterra hab k)^[m] u t - (volterra hab k)^[m] v t|
      ≤ ((M : ℝ) * ((t : ℝ) - a)) ^ m / m ! * ‖u - v‖ := by
  induction m generalizing t with
  | zero =>
    have h := (u - v).norm_coe_le_norm t
    rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at h
    simpa using h
  | succ m ih =>
    have ht : a ≤ (t : ℝ) := t.2.1
    set U := (volterra hab k)^[m] u with hU
    set V := (volterra hab k)^[m] v with hV
    have hstep : ∀ s ∈ Icc a (t : ℝ),
        |k (t, projIcc a b hab s, U (projIcc a b hab s))
            - k (t, projIcc a b hab s, V (projIcc a b hab s))|
          ≤ (M : ℝ) ^ (m + 1) * ‖u - v‖ / m ! * (s - a) ^ m := by
      intro s hs
      have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.2.2⟩
      have hlip := (hk t (projIcc a b hab s)).dist_le_mul
        (U (projIcc a b hab s)) (V (projIcc a b hab s))
      rw [Real.dist_eq] at hlip
      have hih := ih (projIcc a b hab s)
      rw [coe_projIcc_of_mem hab hsb] at hih
      calc |k (t, projIcc a b hab s, U (projIcc a b hab s))
              - k (t, projIcc a b hab s, V (projIcc a b hab s))|
          ≤ (M : ℝ) * |U (projIcc a b hab s) - V (projIcc a b hab s)| := hlip
        _ ≤ (M : ℝ) * (((M : ℝ) * (s - a)) ^ m / m ! * ‖u - v‖) :=
            mul_le_mul_of_nonneg_left hih M.coe_nonneg
        _ = (M : ℝ) ^ (m + 1) * ‖u - v‖ / m ! * (s - a) ^ m := by
            rw [mul_pow]; ring
    have hdiff : volterra hab k U t - volterra hab k V t
        = ∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
            - k (t, projIcc a b hab s, V (projIcc a b hab s))) := by
      rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
      rfl
    have hpow : (∫ s in a..(t : ℝ), (s - a) ^ m) = ((t : ℝ) - a) ^ (m + 1) / (m + 1) := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ m) a, integral_pow]
      simp
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hU, ← hV, hdiff]
    calc |∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
              - k (t, projIcc a b hab s, V (projIcc a b hab s)))|
        ≤ ∫ s in a..(t : ℝ), |k (t, projIcc a b hab s, U (projIcc a b hab s))
              - k (t, projIcc a b hab s, V (projIcc a b hab s))| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in a..(t : ℝ), (M : ℝ) ^ (m + 1) * ‖u - v‖ / m ! * (s - a) ^ m :=
          intervalIntegral.integral_mono_on ht (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _) hstep
      _ = (M : ℝ) ^ (m + 1) * ‖u - v‖ / m ! * (((t : ℝ) - a) ^ (m + 1) / (m + 1)) := by
          rw [intervalIntegral.integral_const_mul, hpow]
      _ = ((M : ℝ) * ((t : ℝ) - a)) ^ (m + 1) / (m + 1)! * ‖u - v‖ := by
          rw [Nat.factorial_succ, mul_pow]
          have hm : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
          push_cast
          field_simp

/-- **The factorial estimate for the iterates of a Volterra operator** (Atkinson and Han,
*Theoretical Numerical Analysis*, proof of Theorem 5.2.3): if the kernel is `M`-Lipschitz in its
last argument, then the `m`-th iterate of the Volterra operator is Lipschitz with the constant
`(M (b - a)) ^ m / m !`, which tends to `0`; hence some power of a Volterra operator is a
contraction, whatever `M` is. -/
theorem norm_iterate_volterra_sub_le {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (u v : C(Icc a b, ℝ)) (m : ℕ) :
    ‖(volterra hab k)^[m] u - (volterra hab k)^[m] v‖
      ≤ ((M : ℝ) * (b - a)) ^ m / m ! * ‖u - v‖ := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have hnn : (0 : ℝ) ≤ (M : ℝ) * ((t : ℝ) - a) := by
    have := t.2.1
    have := M.coe_nonneg
    nlinarith
  have hmono : (M : ℝ) * ((t : ℝ) - a) ≤ (M : ℝ) * (b - a) :=
    mul_le_mul_of_nonneg_left (by linarith [t.2.2]) M.coe_nonneg
  have hstep := abs_iterate_volterra_sub_apply_le hab hk u v m t
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
  refine hstep.trans ?_
  gcongr

/-- A Volterra operator is itself Lipschitz, with constant `M (b - a)`. -/
theorem lipschitzWith_volterra {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) :
    LipschitzWith (M * (b - a).toNNReal) (volterra hab k) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have h := norm_iterate_volterra_sub_le hab hk u v 1
  simp only [Function.iterate_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hba]
  exact h

/-- Some power of a Volterra operator is a contraction in the supremum norm, whatever the Lipschitz
constant of its kernel (Atkinson and Han, *Theoretical Numerical Analysis*, Theorem 5.2.3). -/
theorem exists_contractingWith_iterate_volterra {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) :
    ∃ m : ℕ, 0 < m ∧
      ContractingWith (((M : ℝ) * (b - a)) ^ m / m !).toNNReal ((volterra hab k)^[m]) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have htend := FloorSemiring.tendsto_pow_div_factorial_atTop ((M : ℝ) * (b - a))
  obtain ⟨m, hm⟩ := ((htend.eventually_lt_const one_pos).and (Filter.eventually_gt_atTop 0)).exists
  have hnn : (0 : ℝ) ≤ ((M : ℝ) * (b - a)) ^ m / m ! := by positivity
  refine ⟨m, hm.2, ?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ hnn]
    exact hm.1
  · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hnn]
    exact norm_iterate_volterra_sub_le hab hk u v m

private theorem coe_clm_pow (L : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ)) (n : ℕ) :
    ⇑(L ^ n) = (⇑L)^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

/-- The kernel of a linear operator is Lipschitz in its last argument, with constant `‖k‖`. -/
theorem lipschitzWith_mulKernel (k : C(Icc a b × Icc a b, ℝ)) (x y : Icc a b) :
    LipschitzWith ‖k‖₊ fun z => mulKernel k (x, y, z) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, mulKernel_apply, mulKernel_apply,
    ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (k.norm_coe_le_norm _) (abs_nonneg _)

/-- **The factorial estimate for the powers of a linear Volterra operator** (Atkinson and Han,
*Theoretical Numerical Analysis*, Exercise 2.3.4): `‖L ^ m‖ ≤ (‖k‖ (b - a)) ^ m / m !`, so the
powers of `L` tend to `0` in norm and `λ - L` is invertible for every nonzero `λ`. -/
theorem norm_volterraCLM_pow_le (k : C(Icc a b × Icc a b, ℝ)) (m : ℕ) :
    ‖volterraCLM hab k ^ m‖ ≤ (‖k‖ * (b - a)) ^ m / m ! := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have hzero : (volterra hab (mulKernel k))^[m] 0 = 0 := by
    induction m with
    | zero => rfl
    | succ n ihn =>
      rw [Function.iterate_succ_apply', ihn]
      ext t
      simp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have h := norm_iterate_volterra_sub_le hab (lipschitzWith_mulKernel k) u 0 m
  rw [hzero, sub_zero, sub_zero, coe_nnnorm] at h
  have hiter : (volterraCLM hab k ^ m) u = (volterra hab (mulKernel k))^[m] u := by
    rw [coe_clm_pow, coe_volterraCLM]
  rw [hiter]
  exact h

end Volterra

/-! ### The Bielecki norm -/

set_option linter.unusedVariables false in
/-- The **Bielecki space**: the continuous real functions on `Set.Icc a b` under the weighted
supremum norm `‖u‖ = ⨆ t, exp (-(β (t - a))) * |u t|`.

For `0 ≤ β` this norm is equivalent to the supremum norm (`Bielecki.norm_le_norm_equiv` and
`Bielecki.exp_mul_norm_equiv_le_norm`), so the space is again a Banach space and convergence in it
is uniform convergence; what the weight buys is that a Volterra operator becomes a contraction
outright, with constant `M / β` (Atkinson and Han, *Theoretical Numerical Analysis*, proof of
Theorem 5.2.4). -/
def Bielecki (a b β : ℝ) : Type := C(Icc a b, ℝ)

namespace Bielecki

variable {a b β : ℝ}

instance : AddCommGroup (Bielecki a b β) := inferInstanceAs (AddCommGroup C(Icc a b, ℝ))

instance : Module ℝ (Bielecki a b β) := inferInstanceAs (Module ℝ C(Icc a b, ℝ))

/-- The identity linear equivalence between the Bielecki space and `C(Icc a b, ℝ)`.  It is not an
isometry; the two norms are equivalent by `Bielecki.norm_le_norm_equiv` and
`Bielecki.exp_mul_norm_equiv_le_norm`. -/
def equiv : Bielecki a b β ≃ₗ[ℝ] C(Icc a b, ℝ) := LinearEquiv.refl ℝ _

/-- The weighting map `u ↦ (t ↦ exp (-(β (t - a))) * u t)`, whose supremum norm is by definition
the Bielecki norm. -/
noncomputable def weight : Bielecki a b β →ₗ[ℝ] C(Icc a b, ℝ) where
  toFun u := ⟨fun t => Real.exp (-(β * ((t : ℝ) - a))) * equiv u t, by fun_prop⟩
  map_add' u v := by ext t; simp [mul_add]
  map_smul' c u := by ext t; simp; ring

@[simp]
theorem weight_apply (u : Bielecki a b β) (t : Icc a b) :
    weight u t = Real.exp (-(β * ((t : ℝ) - a))) * equiv u t :=
  rfl

theorem weight_injective : Function.Injective (weight : Bielecki a b β → C(Icc a b, ℝ)) := by
  intro u v huv
  refine equiv.injective (ContinuousMap.ext fun t => ?_)
  have h := congrArg (fun f : C(Icc a b, ℝ) => f t) huv
  simp only [weight_apply] at h
  exact mul_left_cancel₀ (Real.exp_ne_zero _) h

noncomputable instance : NormedAddCommGroup (Bielecki a b β) :=
  NormedAddCommGroup.induced (Bielecki a b β) C(Icc a b, ℝ)
    (weight : Bielecki a b β →ₗ[ℝ] C(Icc a b, ℝ)).toAddMonoidHom weight_injective

theorem norm_eq (u : Bielecki a b β) : ‖u‖ = ‖weight u‖ := rfl

instance : NormedSpace ℝ (Bielecki a b β) where
  norm_smul_le c u := le_of_eq (by rw [norm_eq, norm_eq, map_smul, norm_smul])

theorem isometry_weight : Isometry (weight : Bielecki a b β → C(Icc a b, ℝ)) :=
  AddMonoidHomClass.isometry_of_norm _ fun u => (norm_eq u).symm

theorem weight_surjective : Function.Surjective (weight : Bielecki a b β → C(Icc a b, ℝ)) := by
  intro v
  refine ⟨equiv.symm ⟨fun t => Real.exp (β * ((t : ℝ) - a)) * v t, by fun_prop⟩, ?_⟩
  ext t
  simp only [weight_apply, LinearEquiv.apply_symm_apply, ContinuousMap.coe_mk, ← mul_assoc,
    ← Real.exp_add]
  simp

instance : CompleteSpace (Bielecki a b β) :=
  (isometry_weight.isUniformInducing.completeSpace_congr weight_surjective).2 inferInstance

@[simp]
theorem equiv_sub (u v : Bielecki a b β) : equiv (u - v) = equiv u - equiv v :=
  map_sub equiv u v

/-- The Bielecki norm dominates every weighted value of the function. -/
theorem exp_mul_abs_le_norm (u : Bielecki a b β) (t : Icc a b) :
    Real.exp (-(β * ((t : ℝ) - a))) * |equiv u t| ≤ ‖u‖ := by
  have h := (weight u).norm_coe_le_norm t
  rwa [weight_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), ← norm_eq] at h

/-- A uniform bound on the weighted values of the function bounds the Bielecki norm. -/
theorem norm_le {u : Bielecki a b β} {C : ℝ} (hC : 0 ≤ C) :
    ‖u‖ ≤ C ↔ ∀ t : Icc a b, Real.exp (-(β * ((t : ℝ) - a))) * |equiv u t| ≤ C := by
  rw [norm_eq, ContinuousMap.norm_le _ hC]
  exact forall_congr' fun t => by
    rw [weight_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- For a nonnegative weight the Bielecki norm is at most the supremum norm. -/
theorem norm_le_norm_equiv (hβ : 0 ≤ β) (u : Bielecki a b β) : ‖u‖ ≤ ‖equiv u‖ := by
  refine (norm_le (norm_nonneg _)).2 fun t => ?_
  have hexp : Real.exp (-(β * ((t : ℝ) - a))) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hβ (by linarith [t.2.1])))
  have habs := (equiv u).norm_coe_le_norm t
  rw [Real.norm_eq_abs] at habs
  calc Real.exp (-(β * ((t : ℝ) - a))) * |equiv u t| ≤ 1 * |equiv u t| :=
        mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ = |equiv u t| := one_mul _
    _ ≤ ‖equiv u‖ := habs

/-- For a nonnegative weight the supremum norm is at most `exp (β (b - a))` times the Bielecki
norm. -/
theorem norm_equiv_le (hβ : 0 ≤ β) (u : Bielecki a b β) :
    ‖equiv u‖ ≤ Real.exp (β * (b - a)) * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  rw [Real.norm_eq_abs]
  have h2 : Real.exp (β * ((t : ℝ) - a)) ≤ Real.exp (β * (b - a)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [t.2.2]) hβ)
  calc |equiv u t|
      = Real.exp (β * ((t : ℝ) - a)) * (Real.exp (-(β * ((t : ℝ) - a))) * |equiv u t|) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (β * ((t : ℝ) - a)) * ‖u‖ :=
        mul_le_mul_of_nonneg_left (exp_mul_abs_le_norm u t) (Real.exp_pos _).le
    _ ≤ Real.exp (β * (b - a)) * ‖u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg u)

/-- **The two norms are equivalent**: `exp (-(β (b - a))) ‖u‖_∞ ≤ ‖u‖_β ≤ ‖u‖_∞` for `0 ≤ β`, so
convergence in the Bielecki norm is uniform convergence. -/
theorem exp_mul_norm_equiv_le_norm (hβ : 0 ≤ β) (u : Bielecki a b β) :
    Real.exp (-(β * (b - a))) * ‖equiv u‖ ≤ ‖u‖ := by
  calc Real.exp (-(β * (b - a))) * ‖equiv u‖
      ≤ Real.exp (-(β * (b - a))) * (Real.exp (β * (b - a)) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_equiv_le hβ u) (Real.exp_pos _).le
    _ = ‖u‖ := by rw [← mul_assoc, ← Real.exp_add]; simp

end Bielecki

/-- The Volterra operator read on the Bielecki space, where it is a contraction with constant
`M / β` whenever its kernel is `M`-Lipschitz in its last argument. -/
noncomputable def volterraBielecki (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ)) (β : ℝ) :
    Bielecki a b β → Bielecki a b β :=
  fun u => Bielecki.equiv.symm (volterra hab k (Bielecki.equiv u))

@[simp]
theorem equiv_volterraBielecki (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ)) (β : ℝ)
    (u : Bielecki a b β) :
    Bielecki.equiv (volterraBielecki hab k β u) = volterra hab k (Bielecki.equiv u) :=
  rfl

/-- The Volterra operator and its Bielecki avatar have the same iterates. -/
theorem equiv_iterate_volterraBielecki (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ)) (β : ℝ)
    (u : Bielecki a b β) (n : ℕ) :
    Bielecki.equiv ((volterraBielecki hab k β)^[n] u)
      = (volterra hab k)^[n] (Bielecki.equiv u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

/-- The elementary integral behind Bielecki's trick:
`∫_a^t e^{β (s - a)} ds = (e^{β (t - a)} - 1)/β`. -/
theorem integral_exp_mul_sub (hβ : β ≠ 0) (a t : ℝ) :
    (∫ s in a..t, Real.exp (β * (s - a))) = (Real.exp (β * (t - a)) - 1) / β := by
  have hderiv : ∀ x ∈ uIcc a t,
      HasDerivAt (fun s : ℝ => Real.exp (β * (s - a)) / β) (Real.exp (β * (x - a))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => β * (s - a)) β x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul β
    exact ((h1.exp).div_const β).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [sub_div]

/-- **A Volterra operator is a contraction in the Bielecki norm**, with constant `M / β`: this is
Bielecki's proof of the Picard–Lindelöf theorem, in which the weight `e^{-β (t - a)}` absorbs the
Lipschitz constant of the kernel instead of the factorial estimate of
`IntegralOperator.norm_iterate_volterra_sub_le` (Atkinson and Han, *Theoretical Numerical
Analysis*, proof of Theorem 5.2.4). -/
theorem contractingWith_volterra_bielecki (hab : a ≤ b) {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) {β : ℝ} (hβ : (M : ℝ) < β) :
    ContractingWith ((M : ℝ) / β).toNNReal (volterraBielecki hab k β) := by
  have hβ0 : (0 : ℝ) < β := lt_of_le_of_lt M.coe_nonneg hβ
  have hdiv : (0 : ℝ) ≤ (M : ℝ) / β := by positivity
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal _ hdiv, div_lt_one hβ0]
    exact hβ
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hdiv]
  set U := Bielecki.equiv u with hU
  set V := Bielecki.equiv v with hV
  refine (Bielecki.norm_le (by positivity)).2 fun t => ?_
  have ht : a ≤ (t : ℝ) := t.2.1
  -- the pointwise bound on the difference of the two integrands
  have hstep : ∀ s ∈ Icc a (t : ℝ),
      |k (t, projIcc a b hab s, U (projIcc a b hab s))
          - k (t, projIcc a b hab s, V (projIcc a b hab s))|
        ≤ (M : ℝ) * ‖u - v‖ * Real.exp (β * (s - a)) := by
    intro s hs
    have hsb : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.2.2⟩
    have hlip := (hk t (projIcc a b hab s)).dist_le_mul
      (U (projIcc a b hab s)) (V (projIcc a b hab s))
    rw [Real.dist_eq] at hlip
    have hw := Bielecki.exp_mul_abs_le_norm (u - v) (projIcc a b hab s)
    rw [Bielecki.equiv_sub, coe_projIcc_of_mem hab hsb] at hw
    have hval : (Bielecki.equiv u - Bielecki.equiv v) (projIcc a b hab s)
        = U (projIcc a b hab s) - V (projIcc a b hab s) := rfl
    rw [hval] at hw
    have hexp : |U (projIcc a b hab s) - V (projIcc a b hab s)|
        ≤ Real.exp (β * (s - a)) * ‖u - v‖ := by
      have hpos : (0 : ℝ) < Real.exp (β * (s - a)) := Real.exp_pos _
      have hone : Real.exp (β * (s - a)) * Real.exp (-(β * (s - a))) = 1 := by
        rw [← Real.exp_add]; simp
      have h := mul_le_mul_of_nonneg_left hw hpos.le
      rwa [← mul_assoc, hone, one_mul] at h
    calc |k (t, projIcc a b hab s, U (projIcc a b hab s))
            - k (t, projIcc a b hab s, V (projIcc a b hab s))|
        ≤ (M : ℝ) * |U (projIcc a b hab s) - V (projIcc a b hab s)| := hlip
      _ ≤ (M : ℝ) * (Real.exp (β * (s - a)) * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left hexp M.coe_nonneg
      _ = (M : ℝ) * ‖u - v‖ * Real.exp (β * (s - a)) := by ring
  have hdiff : Bielecki.equiv (volterraBielecki hab k β u - volterraBielecki hab k β v) t
      = ∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
          - k (t, projIcc a b hab s, V (projIcc a b hab s))) := by
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rfl
  rw [hdiff]
  have hint : |∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
          - k (t, projIcc a b hab s, V (projIcc a b hab s)))|
      ≤ (M : ℝ) * ‖u - v‖ * ((Real.exp (β * ((t : ℝ) - a)) - 1) / β) := by
    calc |∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
              - k (t, projIcc a b hab s, V (projIcc a b hab s)))|
        ≤ ∫ s in a..(t : ℝ), |k (t, projIcc a b hab s, U (projIcc a b hab s))
              - k (t, projIcc a b hab s, V (projIcc a b hab s))| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in a..(t : ℝ), (M : ℝ) * ‖u - v‖ * Real.exp (β * (s - a)) :=
          intervalIntegral.integral_mono_on ht (Continuous.intervalIntegrable (by fun_prop) _ _)
            (Continuous.intervalIntegrable (by fun_prop) _ _) hstep
      _ = (M : ℝ) * ‖u - v‖ * ((Real.exp (β * ((t : ℝ) - a)) - 1) / β) := by
          rw [intervalIntegral.integral_const_mul, integral_exp_mul_sub hβ0.ne']
  have hMv : (0 : ℝ) ≤ (M : ℝ) * ‖u - v‖ := mul_nonneg M.coe_nonneg (norm_nonneg _)
  have hexpt : (0 : ℝ) < Real.exp (-(β * ((t : ℝ) - a))) := Real.exp_pos _
  have hcancel : Real.exp (-(β * ((t : ℝ) - a))) * Real.exp (β * ((t : ℝ) - a)) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(β * ((t : ℝ) - a)))
        * |∫ s in a..(t : ℝ), (k (t, projIcc a b hab s, U (projIcc a b hab s))
            - k (t, projIcc a b hab s, V (projIcc a b hab s)))|
      ≤ Real.exp (-(β * ((t : ℝ) - a)))
          * ((M : ℝ) * ‖u - v‖ * ((Real.exp (β * ((t : ℝ) - a)) - 1) / β)) :=
        mul_le_mul_of_nonneg_left hint hexpt.le
    _ ≤ (M : ℝ) / β * ‖u - v‖ := by
        have hkey : Real.exp (-(β * ((t : ℝ) - a)))
              * ((M : ℝ) * ‖u - v‖ * ((Real.exp (β * ((t : ℝ) - a)) - 1) / β))
            = (M : ℝ) * ‖u - v‖ / β * (1 - Real.exp (-(β * ((t : ℝ) - a)))) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          linear_combination ((M : ℝ) * ‖u - v‖ * β⁻¹) * hcancel
        rw [hkey]
        have hX : (0 : ℝ) ≤ (M : ℝ) * ‖u - v‖ / β := by positivity
        have h1 : (M : ℝ) * ‖u - v‖ / β * (1 - Real.exp (-(β * ((t : ℝ) - a))))
            ≤ (M : ℝ) * ‖u - v‖ / β * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hX
        refine h1.trans (le_of_eq ?_)
        ring

end IntegralOperator
