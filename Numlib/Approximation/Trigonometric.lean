import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Analysis.Fourier.Dirichlet
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Approximation.BestApprox
import Numlib.IntegralEquations.Basic

/-!
# Trigonometric approximation of continuous periodic functions

The space of continuous `2 π`-periodic real functions is `C(AddCircle (2 π), ℝ)`, and the
`n`-th **Fourier projection** on it is `PeriodicCont.fourierProj n`, the kernel operator of the
Dirichlet kernel `D_n (y - x) / π`. It is the partial-sum operator of a Fourier series
(`PeriodicCont.fourierProj_coe`), a bounded projection onto the trigonometric polynomials of degree
at most `n` (`PeriodicCont.range_fourierProj` and `PeriodicCont.isIdempotentElem_fourierProj`), and
its operator norm is the `n`-th **Lebesgue constant** `L_n = (1/π) ∫_{-π}^{π} |D_n|`
(`PeriodicCont.norm_fourierProj`), which grows at least like `(4/π²) log n`
(`PeriodicCont.log_le_lebesgueConstant`) — so it is unbounded — and at most like `log (2 n + 1)`
(`PeriodicCont.lebesgueConstant_le`).

Nothing here duplicates `Numlib/Analysis/Fourier/Dirichlet`: the Dirichlet kernel and the partial
sums are that module's, and what is added is that the partial sum of a *continuous* periodic
function is again one, that the map is bounded, and that it is the projection onto the subspace
`trigPolyLE (2 π) n` of `Numlib/Analysis/Fourier/TrigonometricBasis`. The norm identity is the
operator-norm formula for a kernel operator on a compact space,
`IntegralOperator.norm_kernelCLM` of `Numlib/IntegralEquations/Basic`, which is stated at exactly
the generality that covers a circle as well as an interval.

The two facts that make everything work are the two forms of the kernel: it is a function of
`y - x` built from the Dirichlet kernel (`PeriodicCont.fourierKernel_apply`), which gives the
partial-sum representation and the norm; and it is the reproducing kernel
`(2 π)⁻¹ ∑_{|m| ≤ n} e_m(x) e_m(y)` of the real trigonometric system
(`PeriodicCont.fourierKernel_eq_sum`), which gives the range and the idempotency with no
orthogonality computation of its own — the orthonormality of the system is
`realFourierCoeff_trigFun`.

## Not done here

Jackson's theorems (Atkinson and Han[^atkinson-han], Theorems 3.7.1 and 3.7.2), which bound the
best uniform trigonometric approximation of a Hölder function by `M_k / n^{k+α}`, are not
formalized; they are independent of the Fourier projection except through the subspace
`trigPolyLE (2 π) n` that they measure the distance to, and their proof is a separate construction
(convolution with the Jackson kernel `(sin (n θ / 2) / sin (θ / 2))⁴`). Of Zygmund's asymptotic
`L_n = (4/π²) log n + O(1)` the two halves are proved with different constants —
`log_le_lebesgueConstant` has the sharp `4/π²` below, `lebesgueConstant_le` the crude `1 + log
(2 n + 1)` above — which is all that the divergence argument and the convergence rate (3.7.12)
consume. What is proved of Atkinson and Han's (3.7.11) is the Lebesgue-lemma half,
`‖f - 𝓕_n f‖ ≤ (1 + L_n) dist (f, 𝕋_n)`, which is what the projection contributes; the rate then
follows from it and Jackson's theorem.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
-/

open MeasureTheory Metric Set

open scoped Real

/-- The circle of circumference `2 π` needs `0 < 2 π` as a `Fact`. -/
instance : Fact (0 < 2 * π) := ⟨by positivity⟩

namespace PeriodicCont

/-! ### The Dirichlet kernel on the circle -/

/-- A sum over the symmetric range `Finset.Icc (-n) n` in `ℤ`, split into its middle term and the
pairs `± j`. -/
private theorem sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (g : ℤ → M) (n : ℕ) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, g m = g 0 + ∑ j ∈ Finset.Icc 1 n, (g j + g (-j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have h3 : (-((n : ℤ) + 1)) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    push_cast
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h3, ih,
      Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
    push_cast
    abel

/-- On the circle of circumference `2 π` the member of index `j > 0` of the real trigonometric
system is `√2 cos (j t)`. -/
theorem trigFun_coe_of_pos {j : ℤ} (hj : 0 < j) (t : ℝ) :
    trigFun (2 * π) j ↑t = √2 * Real.cos (j * t) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : 2 * π * (j : ℝ) * t / (2 * π) = (j : ℝ) * t := by field_simp
  rw [trigFun_coe_apply_of_pos hj, h]

/-- On the circle of circumference `2 π` the member of index `j < 0` of the real trigonometric
system is `√2 sin (-j t)`. -/
theorem trigFun_coe_of_neg {j : ℤ} (hj : j < 0) (t : ℝ) :
    trigFun (2 * π) j ↑t = √2 * Real.sin (-(j : ℝ) * t) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : -(2 * π * (j : ℝ) * t / (2 * π)) = -(j : ℝ) * t := by field_simp
  rw [trigFun_coe_apply_of_neg hj, h]

/-- The Dirichlet kernel as a continuous function on the circle: it is the trigonometric
polynomial `1/2 + ∑_{j = 1}^{n} (√2)⁻¹ e_j`, whose value at `↑t` is `dirichletKernel n t`
(`PeriodicCont.dirichletCM_coe`). -/
noncomputable def dirichletCM (n : ℕ) : C(AddCircle (2 * π), ℝ) :=
  (2 : ℝ)⁻¹ • (1 : C(AddCircle (2 * π), ℝ))
    + ∑ j ∈ Finset.Icc 1 n, ((√2)⁻¹ : ℝ) • trigFun (2 * π) (j : ℤ)

@[simp]
theorem dirichletCM_coe (n : ℕ) (t : ℝ) : dirichletCM n ↑t = dirichletKernel n t := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  simp only [dirichletCM, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul,
    dirichletKernel_apply]
  congr 1
  · norm_num
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℤ) < (j : ℤ) := by
    have := (Finset.mem_Icc.1 hj).1; omega
  rw [trigFun_coe_of_pos hj0, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  push_cast
  ring_nf

/-! ### The Fourier projection -/

/-- The kernel `(x, y) ↦ D_n (y - x) / π` of the Fourier projection (Atkinson and Han,
*Theoretical Numerical Analysis*, (3.7.6)). -/
noncomputable def fourierKernel (n : ℕ) : C(AddCircle (2 * π) × AddCircle (2 * π), ℝ) :=
  (π⁻¹ : ℝ) • (dirichletCM n).comp ⟨fun p => p.2 - p.1, by fun_prop⟩

@[simp]
theorem fourierKernel_apply (n : ℕ) (x y : AddCircle (2 * π)) :
    fourierKernel n (x, y) = π⁻¹ * dirichletCM n (y - x) :=
  rfl

/-- **The Fourier projection** `𝓕_n` on the space `C(AddCircle (2 π), ℝ)` of continuous
`2 π`-periodic functions: the kernel operator of the Dirichlet kernel,
`𝓕_n f (x) = (1/π) ∫ f(y) D_n (y - x) dy` (Atkinson and Han, *Theoretical Numerical Analysis*,
(3.7.6)–(3.7.8)). It is the partial-sum operator of the Fourier series
(`PeriodicCont.fourierProj_coe`) and the projection onto the trigonometric polynomials of degree
at most `n` (`PeriodicCont.range_fourierProj`, `PeriodicCont.isIdempotentElem_fourierProj`). -/
noncomputable def fourierProj (n : ℕ) :
    C(AddCircle (2 * π), ℝ) →L[ℝ] C(AddCircle (2 * π), ℝ) :=
  IntegralOperator.kernelCLM volume (fourierKernel n)

theorem fourierProj_apply (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (x : AddCircle (2 * π)) :
    fourierProj n f x = ∫ y, fourierKernel n (x, y) * f y :=
  rfl

/-- An integral over the circle, recentred as an interval integral around any real point. -/
theorem integral_addCircle_eq (F : AddCircle (2 * π) → ℝ) (s : ℝ) :
    ∫ y : AddCircle (2 * π), F y = ∫ r in -π..π, F ↑(s + r) := by
  have h := AddCircle.intervalIntegral_preimage (2 * π) (s + -π) F
  rw [show s + -π + 2 * π = s + π by ring] at h
  rw [← h, ← intervalIntegral.integral_comp_add_left (fun t : ℝ => F ↑t) s]

/-- **The Fourier projection is the partial-sum operator of the Fourier series** of
`Numlib/Analysis/Fourier/Dirichlet` (Atkinson and Han, *Theoretical Numerical Analysis*,
(3.7.6)). -/
theorem fourierProj_coe (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (s : ℝ) :
    fourierProj n f ↑s = fourierPartialSum (fun t : ℝ => f ↑t) n s := by
  have hcont : Continuous fun t : ℝ => f ↑t :=
    f.continuous.comp (AddCircle.continuous_mk' (2 * π))
  have hper : Function.Periodic (fun t : ℝ => f ↑t) (2 * π) := fun t => by
    simp only []
    rw [AddCircle.coe_add_period]
  rw [fourierPartialSum_eq_integral hper (hcont.intervalIntegrable _ _), fourierProj_apply,
    integral_addCircle_eq (fun y => fourierKernel n (↑s, y) * f y) s,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  have hsub : ((↑(s + r) : AddCircle (2 * π)) - ↑s) = ((r : ℝ) : AddCircle (2 * π)) := by
    have h : ((↑(s + r) : AddCircle (2 * π))) = (↑s : AddCircle (2 * π)) + ↑r := rfl
    rw [h, add_sub_cancel_left]
  simp only [fourierKernel_apply, hsub, dirichletCM_coe]
  field_simp

/-! ### The range: the trigonometric polynomials of degree at most `n` -/

/-- **The kernel of the Fourier projection is the reproducing kernel of the real trigonometric
system** of index at most `n`: `D_n (y - x) / π = (2 π)⁻¹ ∑_{|m| ≤ n} e_m(x) e_m(y)`. This is the
form of the kernel from which the range and the idempotency of the projection are read off. -/
theorem fourierKernel_eq_sum (n : ℕ) (x y : AddCircle (2 * π)) :
    fourierKernel n (x, y)
      = (2 * π)⁻¹ * ∑ m ∈ Finset.Icc (-(n : ℤ)) n, trigFun (2 * π) m x * trigFun (2 * π) m y := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  induction x using QuotientAddGroup.induction_on with
  | _ u =>
    induction y using QuotientAddGroup.induction_on with
    | _ v =>
      have hsub : ((↑v : AddCircle (2 * π)) - ↑u) = ((v - u : ℝ) : AddCircle (2 * π)) := rfl
      rw [fourierKernel_apply, hsub, dirichletCM_coe, dirichletKernel_apply,
        sum_Icc_neg_eq (fun m => trigFun (2 * π) m ↑u * trigFun (2 * π) m ↑v) n, trigFun_zero]
      have hterm : ∀ j ∈ Finset.Icc 1 n,
          trigFun (2 * π) (j : ℤ) ↑u * trigFun (2 * π) (j : ℤ) ↑v
            + trigFun (2 * π) (-(j : ℤ)) ↑u * trigFun (2 * π) (-(j : ℤ)) ↑v
            = 2 * Real.cos (j * (v - u)) := by
        intro j hj
        have hj0 : (0 : ℤ) < (j : ℤ) := by have := (Finset.mem_Icc.1 hj).1; omega
        have hcos : Real.cos ((j : ℝ) * (v - u))
            = Real.cos ((j : ℝ) * v) * Real.cos ((j : ℝ) * u)
              + Real.sin ((j : ℝ) * v) * Real.sin ((j : ℝ) * u) := by
          rw [show (j : ℝ) * (v - u) = (j : ℝ) * v - (j : ℝ) * u by ring, Real.cos_sub]
        rw [trigFun_coe_of_pos hj0, trigFun_coe_of_pos hj0,
          trigFun_coe_of_neg (by omega : (-(j : ℤ)) < 0),
          trigFun_coe_of_neg (by omega : (-(j : ℤ)) < 0), hcos]
        push_cast
        simp only [neg_neg]
        linear_combination (Real.cos ((j : ℝ) * u) * Real.cos ((j : ℝ) * v)
          + Real.sin ((j : ℝ) * u) * Real.sin ((j : ℝ) * v)) * h2
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      simp only [ContinuousMap.one_apply, one_mul, mul_inv]
      ring

/-- The Fourier projection expanded in the real trigonometric system: its coefficients are the
real Fourier coefficients (Atkinson and Han, *Theoretical Numerical Analysis*, (4.1.1)). -/
theorem fourierProj_eq_sum (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    fourierProj n f
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          realFourierCoeff (f : AddCircle (2 * π) → ℝ) m • trigFun (2 * π) m := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  ext x
  have hcoe : ∀ m : ℤ, realFourierCoeff (f : AddCircle (2 * π) → ℝ) m
      = (2 * π)⁻¹ * ∫ y : AddCircle (2 * π), trigFun (2 * π) m y * f y := by
    intro m
    rw [realFourierCoeff_apply, AddCircle.integral_haarAddCircle, smul_eq_mul]
  have hint : ∀ m : ℤ, Integrable
      (fun y : AddCircle (2 * π) =>
        (2 * π)⁻¹ * trigFun (2 * π) m x * (trigFun (2 * π) m y * f y)) volume := fun m =>
    IntegralOperator.integrable_of_continuousMap volume
      ⟨_, continuous_const.mul ((trigFun (2 * π) m).continuous.mul f.continuous)⟩
  rw [fourierProj_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  have hrw : ∀ y : AddCircle (2 * π), fourierKernel n (x, y) * f y
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          (2 * π)⁻¹ * trigFun (2 * π) m x * (trigFun (2 * π) m y * f y) := by
    intro y
    rw [fourierKernel_eq_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, ContinuousMap.smul_apply, smul_eq_mul, hcoe m]
  ring

/-- The Fourier projection lands in the trigonometric polynomials of degree at most `n`. -/
theorem fourierProj_mem (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    fourierProj n f ∈ trigPolyLE (2 * π) n :=
  mem_trigPolyLE_iff.2 ⟨fun m => realFourierCoeff (f : AddCircle (2 * π) → ℝ) m,
    fourierProj_eq_sum n f⟩

/-- The Fourier projection fixes each member of the real trigonometric system of index at most
`n`. -/
theorem fourierProj_trigFun {n : ℕ} {m : ℤ} (hm : m.natAbs ≤ n) :
    fourierProj n (trigFun (2 * π) m) = trigFun (2 * π) m := by
  rw [fourierProj_eq_sum]
  rw [Finset.sum_eq_single m (fun j _ hj => by
      rw [realFourierCoeff_trigFun, ite_eq_right (Ne.symm hj), zero_smul]) fun hm' => ?_]
  · simp
  · exact absurd (Finset.mem_Icc.2 (Set.mem_Icc.1 (mem_Icc_iff_natAbs_le.2 hm))) hm'

/-- **The Fourier projection fixes the trigonometric polynomials of degree at most `n`.** This is
the fact `fourierPartialSum` of `Numlib/Analysis/Fourier/Dirichlet` does not record, and it is what
idempotency needs. -/
theorem fourierProj_eq_self {n : ℕ} {f : C(AddCircle (2 * π), ℝ)}
    (hf : f ∈ trigPolyLE (2 * π) n) : fourierProj n f = f := by
  obtain ⟨c, rfl⟩ := mem_trigPolyLE_iff.1 hf
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_smul, fourierProj_trigFun
    (mem_Icc_iff_natAbs_le.1 (Set.mem_Icc.2 (Finset.mem_Icc.1 hm)))]

/-- **The Fourier projection is a projection.** -/
theorem isIdempotentElem_fourierProj (n : ℕ) : IsIdempotentElem (fourierProj n) := by
  ext f x
  exact congrFun (congrArg _ (fourierProj_eq_self (fourierProj_mem n f))) x

/-- **The range of the Fourier projection is the space of trigonometric polynomials of degree at
most `n`.** -/
theorem range_fourierProj (n : ℕ) :
    LinearMap.range ((fourierProj n : C(AddCircle (2 * π), ℝ) →L[ℝ] C(AddCircle (2 * π), ℝ)) :
        C(AddCircle (2 * π), ℝ) →ₗ[ℝ] C(AddCircle (2 * π), ℝ))
      = trigPolyLE (2 * π) n := by
  refine le_antisymm ?_ fun f hf => ⟨f, fourierProj_eq_self hf⟩
  rintro _ ⟨f, rfl⟩
  exact fourierProj_mem n f

/-! ### The Lebesgue constants -/

/-- The `n`-th **Lebesgue constant** `L_n = (1/π) ∫_{-π}^{π} |D_n(θ)| dθ`, the operator norm of the
`n`-th Fourier projection (Atkinson and Han, *Theoretical Numerical Analysis*, (3.7.9)). -/
noncomputable def lebesgueConstant (n : ℕ) : ℝ :=
  (1 / π) * ∫ t in -π..π, |dirichletKernel n t|

/-- **The operator norm of the Fourier projection is the Lebesgue constant** (Atkinson and Han,
*Theoretical Numerical Analysis*, (3.7.9)): the operator-norm formula
`IntegralOperator.norm_kernelCLM` for a kernel operator on a compact space, whose row integrals are
here independent of the row because the kernel is a function of `y - x`. -/
theorem norm_fourierProj (n : ℕ) : ‖fourierProj n‖ = lebesgueConstant n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hconst : ∀ x : AddCircle (2 * π),
      (∫ y : AddCircle (2 * π), |fourierKernel n (x, y)|) = lebesgueConstant n := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | _ s =>
      rw [integral_addCircle_eq (fun y => |fourierKernel n (↑s, y)|) s, lebesgueConstant,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      have hsub : ((↑(s + r) : AddCircle (2 * π)) - ↑s) = ((r : ℝ) : AddCircle (2 * π)) := by
        have h : ((↑(s + r) : AddCircle (2 * π))) = (↑s : AddCircle (2 * π)) + ↑r := rfl
        rw [h, add_sub_cancel_left]
      simp only [fourierKernel_apply, hsub, dirichletCM_coe, abs_mul,
        abs_of_pos (inv_pos.2 hπ)]
      rw [one_div]
  rw [fourierProj, IntegralOperator.norm_kernelCLM]
  simp only [hconst]
  exact ciSup_const

/-- **The Lebesgue lemma for the Fourier projection** (Atkinson and Han, *Theoretical Numerical
Analysis*, (3.7.11)): the error of the `n`-th partial sum of the Fourier series of a continuous
periodic function is at most `1 + L_n` times its distance to the trigonometric polynomials of
degree at most `n`. Combined with a bound on the best approximation — Jackson's theorem, which is
not formalized here — and with the growth of `L_n`, this is the uniform convergence rate
(3.7.12). -/
theorem norm_sub_fourierProj_le (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    ‖f - fourierProj n f‖
      ≤ (1 + lebesgueConstant n) * infDist f (trigPolyLE (2 * π) n : Set _) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (fourierProj n)
    (isIdempotentElem_fourierProj n) f
  rwa [range_fourierProj, norm_fourierProj] at h

/-! ### Zygmund's lower bound for the Lebesgue constants -/

/-- The Dirichlet kernel is even, so the Lebesgue constant is twice the mean modulus over half a
period. -/
theorem lebesgueConstant_eq (n : ℕ) :
    lebesgueConstant n = 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  have hcont : Continuous fun t => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  have hneg : (∫ t in -π..(0 : ℝ), |dirichletKernel n t|)
      = ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π)
      fun t => |dirichletKernel n t|
    simpa using h.symm
  rw [lebesgueConstant, ← intervalIntegral.integral_add_adjacent_intervals
      (b := (0 : ℝ)) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg]
  ring

/-- The modulus of the sine has mean `2` over every period. -/
private theorem integral_abs_sin (a : ℝ) : ∫ x in a..a + π, |Real.sin x| = 2 := by
  have hper : Function.Periodic (fun x : ℝ => |Real.sin x|) π := fun x => by
    simp only [Real.sin_add_pi, abs_neg]
  rw [hper.intervalIntegral_add_eq a 0, zero_add]
  have hcongr : ∀ x ∈ Set.uIcc (0 : ℝ) π, |Real.sin x| = Real.sin x := by
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)
  rw [intervalIntegral.integral_congr hcongr, integral_sin]
  norm_num

/-- The elementary lower bound `|D_n(t)| ≥ |sin ((n + 1/2) t)| / t` on `(0, π]`, from the closed
form of the Dirichlet kernel and `2 sin (t/2) ≤ t`. -/
private theorem abs_sin_div_le {n : ℕ} {t : ℝ} (ht0 : 0 < t) (htπ : t ≤ π) :
    |Real.sin (((n : ℝ) + 1 / 2) * t)| / t ≤ |dirichletKernel n t| := by
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : 2 * Real.sin (t / 2) ≤ t := by
    have := Real.sin_le (by linarith : (0 : ℝ) ≤ t / 2)
    linarith
  have h2s : (0 : ℝ) < 2 * Real.sin (t / 2) := by linarith
  rw [dirichletKernel_eq_sin_div hs.ne', abs_div, abs_of_pos h2s, div_le_div_iff₀ ht0 h2s]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- The contribution of the `k`-th arch of `sin ((n + 1/2) t)` to the mean modulus of the Dirichlet
kernel is at least `2 / (k π)`. -/
private theorem piece_le (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    2 / ((k : ℝ) * π)
      ≤ ∫ t in (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))..((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
          |dirichletKernel n t| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hc : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hA0 : (0 : ℝ) ≤ ((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2) :=
    div_nonneg (mul_nonneg (by linarith) hπ.le) hc.le
  have hAB : ((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2) ≤ (k : ℝ) * π / ((n : ℝ) + 1 / 2) := by
    rw [div_le_div_iff₀ hc hc]
    nlinarith
  have hBπ : (k : ℝ) * π / ((n : ℝ) + 1 / 2) ≤ π := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hpt : ∀ t ∈ Set.Icc (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))
      ((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
      ((n : ℝ) + 1 / 2) / ((k : ℝ) * π) * |Real.sin (((n : ℝ) + 1 / 2) * t)|
        ≤ |dirichletKernel n t| := by
    intro t ht
    rcases eq_or_lt_of_le (hA0.trans ht.1) with h0 | h0
    · rw [← h0]
      simp
    · have htπ : t ≤ π := ht.2.trans hBπ
      refine le_trans ?_ (abs_sin_div_le h0 htπ)
      have hct : ((n : ℝ) + 1 / 2) * t ≤ (k : ℝ) * π := by
        have := ht.2
        rw [le_div_iff₀ hc] at this
        linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) h0]
      nlinarith [abs_nonneg (Real.sin (((n : ℝ) + 1 / 2) * t))]
  have hI := intervalIntegral.integral_mono_on (μ := volume) hAB
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) hpt
  have hcomp : (∫ t in (((k : ℝ) - 1) * π / ((n : ℝ) + 1 / 2))..((k : ℝ) * π / ((n : ℝ) + 1 / 2)),
        |Real.sin (((n : ℝ) + 1 / 2) * t)|)
      = (((n : ℝ) + 1 / 2))⁻¹ * ∫ s in (((k : ℝ) - 1) * π)..(((k : ℝ) - 1) * π + π),
          |Real.sin s| := by
    rw [intervalIntegral.integral_comp_mul_left (fun s => |Real.sin s|) hc.ne', smul_eq_mul]
    congr 2 <;> field_simp
    ring
  rw [intervalIntegral.integral_const_mul, hcomp, integral_abs_sin] at hI
  refine le_trans (le_of_eq ?_) hI
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  field_simp

/-- The pieces add up: the mean modulus of the Dirichlet kernel over `[0, π]` dominates the partial
harmonic sum `∑_{k = 1}^{n} 2 / (k π)`. -/
private theorem sum_pieces_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, 2 / ((k : ℝ) * π)
      ≤ ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hc : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hcont : Continuous fun t : ℝ => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  have hstep : ∀ m : ℕ, m ≤ n →
      ∑ k ∈ Finset.Icc 1 m, 2 / ((k : ℝ) * π)
        ≤ ∫ t in (0 : ℝ)..((m : ℝ) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t| := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := piece_le n (m + 1) (by omega) hm
      push_cast at h2
      rw [show (m : ℝ) + 1 - 1 = (m : ℝ) by ring] at h2
      have hadj : (∫ t in (0 : ℝ)..((m : ℝ) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t|)
          + (∫ t in ((m : ℝ) * π / ((n : ℝ) + 1 / 2))..(((m : ℝ) + 1) * π / ((n : ℝ) + 1 / 2)),
              |dirichletKernel n t|)
          = ∫ t in (0 : ℝ)..(((m : ℝ) + 1) * π / ((n : ℝ) + 1 / 2)), |dirichletKernel n t| :=
        intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      rw [← hadj]
      exact add_le_add h1 h2
  have hfin := hstep n le_rfl
  have hnπ : (n : ℝ) * π / ((n : ℝ) + 1 / 2) ≤ π := by
    rw [div_le_iff₀ hc]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) * π / ((n : ℝ) + 1 / 2) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) hπ.le) hc.le
  have htail : (0 : ℝ) ≤ ∫ t in ((n : ℝ) * π / ((n : ℝ) + 1 / 2))..π, |dirichletKernel n t| :=
    intervalIntegral.integral_nonneg (μ := volume) hnπ fun _ _ => abs_nonneg _
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := (n : ℝ) * π / ((n : ℝ) + 1 / 2)) (c := π)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  linarith

/-- `log n` is at most the `n`-th partial sum of the harmonic series. -/
private theorem log_le_sum_inv (n : ℕ) :
    Real.log n ≤ ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ := by
  have key : ∀ m : ℕ, Real.log ((m : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 m, ((k : ℝ))⁻¹ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hlog : Real.log ((m : ℝ) + 1 + 1) - Real.log ((m : ℝ) + 1) ≤ ((m : ℝ) + 1)⁻¹ := by
        rw [← Real.log_div (by positivity) (by positivity)]
        have h := Real.log_le_sub_one_of_pos
          (x := ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1)) (by positivity)
        have heq : ((m : ℝ) + 1 + 1) / ((m : ℝ) + 1) - 1 = ((m : ℝ) + 1)⁻¹ := by
          field_simp; ring
        linarith [h, heq.le, heq.ge]
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine le_trans (Real.log_le_log (by exact_mod_cast hn) ?_) (key n)
    linarith

/-- **Zygmund's lower bound for the Lebesgue constants**, `(4/π²) log n ≤ L_n` (Atkinson and Han,
*Theoretical Numerical Analysis*, (3.7.10), the half of the asymptotics
`L_n = (4/π²) log n + O(1)` that the divergence argument needs).

The Lebesgue constants are therefore unbounded, which is why the Fourier series of some continuous
periodic function fails to converge uniformly. -/
theorem log_le_lebesgueConstant (n : ℕ) :
    4 / π ^ 2 * Real.log n ≤ lebesgueConstant n := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsum : ∑ k ∈ Finset.Icc 1 n, 2 / ((k : ℝ) * π)
      = 2 / π * ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℝ) ≠ 0 := by
      have h := (Finset.mem_Icc.1 hk).1
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith
    field_simp
  have hI : 2 / π * Real.log n ≤ ∫ t in (0 : ℝ)..π, |dirichletKernel n t| := by
    refine le_trans ?_ (sum_pieces_le n)
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (log_le_sum_inv n) (by positivity)
  rw [lebesgueConstant_eq, show 4 / π ^ 2 * Real.log n = 2 / π * (2 / π * Real.log n) by
    field_simp; ring]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-! ### An upper bound for the Lebesgue constants -/

/-- The Dirichlet kernel is bounded by its value `n + 1/2` at the origin: it is a sum of `n`
cosines and a half. -/
private theorem abs_dirichletKernel_le (n : ℕ) (t : ℝ) :
    |dirichletKernel n t| ≤ (n : ℝ) + 1 / 2 := by
  rw [dirichletKernel_apply]
  refine (abs_add_le _ _).trans ?_
  have h2 : |∑ j ∈ Finset.Icc 1 n, Real.cos (j * t)| ≤ (n : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.Icc 1 n, |Real.cos (j * t)|
        ≤ ∑ _j ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun j _ => Real.abs_cos_le_one _
      _ = (n : ℝ) := by simp
  have h1 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
  linarith

/-- Away from the origin the Dirichlet kernel is bounded uniformly in `n`, by `π / (2 t)`: the
numerator of the closed form (3.7.8) is at most one and Jordan's inequality
`Real.mul_le_sin` bounds the denominator below by `2 t / π`. -/
private theorem abs_dirichletKernel_le_div (n : ℕ) {t : ℝ} (ht0 : 0 < t) (htp : t ≤ π) :
    |dirichletKernel n t| ≤ π / 2 * t⁻¹ := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hs : t / π ≤ Real.sin (t / 2) := by
    have h := Real.mul_le_sin (x := t / 2) (by positivity) (by linarith)
    calc t / π = 2 / π * (t / 2) := by ring
      _ ≤ Real.sin (t / 2) := h
  have hst : t ≤ π * Real.sin (t / 2) := by
    rw [div_le_iff₀ hπ] at hs
    linarith
  have hs0 : 0 < Real.sin (t / 2) := by nlinarith
  rw [dirichletKernel_eq_sin_div (ne_of_gt hs0), abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sin (t / 2)),
    div_le_iff₀ (by positivity),
    show π / 2 * t⁻¹ * (2 * Real.sin (t / 2)) = π * Real.sin (t / 2) / t by field_simp,
    le_div_iff₀ ht0]
  have h1 : |Real.sin (((n : ℝ) + 1 / 2) * t)| * t ≤ 1 * t :=
    mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) ht0.le
  linarith

/-- **The Lebesgue constants grow no faster than `log n`**: `L_n ≤ 1 + log (2 n + 1)`.

Together with `log_le_lebesgueConstant` this is the two-sided `L_n ≍ log n` that Atkinson and
Han[^atkinson-han] state sharply as `L_n = (4/π²) log n + O(1)` in (3.7.10); the constant here is
not the sharp one, but the upper bound is what the uniform convergence rate (3.7.12) consumes.

The split is at `π / (2 n + 1)`, the first zero of the numerator of the closed form: below it the
kernel is bounded by `n + 1/2`, which contributes `π/2`; above it Jordan's inequality gives the
bound `π / (2 t)`, whose integral is the logarithm. -/
theorem lebesgueConstant_le (n : ℕ) : lebesgueConstant n ≤ 1 + Real.log (2 * (n : ℝ) + 1) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hN : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = π / (2 * (n : ℝ) + 1) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hap : a ≤ π := by
    rw [hadef, div_le_iff₀ hN]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hcont : Continuous fun t : ℝ => |dirichletKernel n t| := (continuous_dirichletKernel n).abs
  -- the piece near the origin, where the kernel is bounded by `n + 1/2`
  have h1 : (∫ t in (0 : ℝ)..a, |dirichletKernel n t|) ≤ π / 2 := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) ha0.le
      (hcont.intervalIntegrable _ _) intervalIntegrable_const
      (fun t _ => abs_dirichletKernel_le n t)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    refine hmono.trans (le_of_eq ?_)
    rw [hadef]
    field_simp
  -- the piece away from the origin, where Jordan's inequality applies
  have hint : IntervalIntegrable (fun t : ℝ => π / 2 * t⁻¹) volume a π := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine continuousOn_const.mul (continuousOn_inv₀.mono ?_)
    intro t ht
    rw [Set.uIcc_of_le hap] at ht
    exact ne_of_gt (lt_of_lt_of_le ha0 ht.1)
  have h2 : (∫ t in a..π, |dirichletKernel n t|) ≤ π / 2 * Real.log (2 * (n : ℝ) + 1) := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hap
      (hcont.intervalIntegrable _ _) hint
      (fun t ht => abs_dirichletKernel_le_div n (lt_of_lt_of_le ha0 ht.1) ht.2)
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hπ, hadef]
    congr 1
    field_simp
  -- and the two pieces together
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (a := (0 : ℝ)) (b := a) (c := π)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [lebesgueConstant_eq]
  have hsum : (∫ t in (0 : ℝ)..π, |dirichletKernel n t|)
      ≤ π / 2 + π / 2 * Real.log (2 * (n : ℝ) + 1) := by
    rw [← hadj]
    linarith
  have hcoef : (0 : ℝ) < 2 / π := by positivity
  calc 2 / π * ∫ t in (0 : ℝ)..π, |dirichletKernel n t|
      ≤ 2 / π * (π / 2 + π / 2 * Real.log (2 * (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum hcoef.le
    _ = 1 + Real.log (2 * (n : ℝ) + 1) := by field_simp

end PeriodicCont
