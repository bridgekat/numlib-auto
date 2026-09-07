import Numlib.Approximation.Interpolation
import Numlib.Approximation.Trigonometric

/-!
# The Dirichlet-kernel form of trigonometric interpolation

`trigInterpCLM T n` (`Numlib.Approximation.Interpolation`) is the projection of `C(ℝ/Tℤ, ℝ)` onto
the trigonometric polynomials of degree at most `n` that interpolates at the `2 n + 1` equispaced
nodes `xⱼ = j T / (2 n + 1)`. On the circle of circumference `2 π` its cardinal functions are
translates of the Dirichlet kernel,

`φⱼ = 2 Dₙ(· - xⱼ) / (2 n + 1)`,

so the interpolant is the discrete analogue of the Fourier partial sum: where the Fourier
projection integrates `f` against `Dₙ(x - y) / π`, the interpolation projection averages it against
`2 Dₙ(x - xⱼ) / (2 n + 1)` over the nodes.

Two facts make the identification work. The recentred kernel `Dₙ(· - a)` is again a trigonometric
polynomial of degree at most `n`, by the addition formula for the cosine
(`PeriodicCont.dirichletShiftCM_mem_trigPolyLE`); and at the node differences the kernel takes the
values `Dₙ(xₖ - xⱼ) = (2 n + 1)/2` for `j = k` and `0` otherwise
(`PeriodicCont.dirichletKernel_node_sub`), because `(n + 1/2)(xₖ - xⱼ)` is an integer multiple of
`π` while `(xₖ - xⱼ)/2` is not.

## Main definitions

* `PeriodicCont.dirichletShiftCM n a` — the recentred Dirichlet kernel `Dₙ(· - a)` on the circle.

## Main statements

* `norm_sub_trigInterpCLM_le` — the Lebesgue lemma for the interpolatory projection.
* `PeriodicCont.dirichletShiftCM_mem_trigPolyLE` — it is a trigonometric polynomial of degree at
  most `n`.
* `PeriodicCont.dirichletKernel_node_sub` — the kernel's values at the differences of the
  equispaced nodes.
* `PeriodicCont.trigInterpCLM_eq_sum_dirichletShiftCM` and
  `PeriodicCont.trigInterpCLM_coe_apply` — the interpolation projection in the Lagrange form built
  from those cardinal functions, as a function on the circle and pointwise on `ℝ`.
* `PeriodicCont.cardinalBasisCM_trigInterpNode` — the cardinal functions are exactly
  `2 Dₙ(· - xⱼ)/(2 n + 1)`, and `PeriodicCont.isGreatest_norm_trigInterpCLM` — the operator norm of
  the projection is therefore the largest value of the Lebesgue function
  `Λₙ(x) = (2/(2 n + 1)) ∑ⱼ |Dₙ(x - xⱼ)|`.
* `norm_trigInterpCLM_le` — a Rivlin-type bound on that supremum,
  `‖𝓘ₙ‖ ≤ 2 + (2/π) log (2 n + 1)`. It carries the sharp coefficient `2/π` of
  [han2009theoretical], (3.7.20) but a larger additive constant; the theorem's own doc comment
  says why the constant printed there is not the one proved here.
* `le_norm_trigInterpCLM_one` — `5/3 ≤ ‖𝓘₁‖`, which is what makes the constant printed in
  [han2009theoretical], (3.7.20) too small.

## References

[han2009theoretical], (3.7.19)–(3.7.20) and Exercise 3.7.5.
-/

open Set

open scoped Real

/-! ### The Lebesgue lemma for the interpolatory projection -/

/-- **The Lebesgue lemma for trigonometric interpolation**: the error of the interpolant of a
continuous periodic function at the `2 n + 1` equispaced nodes is at most `1 + ‖𝓘ₙ‖` times its
distance to the trigonometric polynomials of degree at most `n`.

It is the abstract Lebesgue lemma `norm_sub_apply_le_of_isIdempotentElem` for the projection
`trigInterpCLM`; combined with a bound on the best approximation error — Jackson's theorem — it
gives the uniform convergence rate of trigonometric interpolation. -/
theorem norm_sub_trigInterpCLM_le {T : ℝ} [Fact (0 < T)] (n : ℕ) (f : C(AddCircle T, ℝ)) :
    ‖f - trigInterpCLM T n f‖
      ≤ (1 + ‖trigInterpCLM T n‖) *
        Metric.infDist f (trigPolyLE T n : Set C(AddCircle T, ℝ)) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (trigInterpCLM T n)
    isIdempotentElem_trigInterpCLM f
  rwa [range_trigInterpCLM] at h

namespace PeriodicCont

variable {n : ℕ}

/-! ### The recentred Dirichlet kernel -/

/-- The Dirichlet kernel recentred at `a`, `Dₙ(· - a)`, as a continuous function on the circle of
circumference `2 π`. Its translates by the `2 n + 1` equispaced nodes, scaled by `2/(2 n + 1)`, are
the cardinal functions of trigonometric interpolation. -/
noncomputable def dirichletShiftCM (n : ℕ) (a : ℝ) : C(AddCircle (2 * π), ℝ) :=
  (dirichletCM n).comp ⟨fun x => x - (a : AddCircle (2 * π)), by fun_prop⟩

/-- The recentred kernel evaluates to `dirichletKernel n (t - a)` at the class of `t`. -/
@[simp]
theorem dirichletShiftCM_coe (n : ℕ) (a t : ℝ) :
    dirichletShiftCM n a ↑t = dirichletKernel n (t - a) := by
  have hsub : ((↑t : AddCircle (2 * π)) - ↑a) = ((t - a : ℝ) : AddCircle (2 * π)) := rfl
  rw [dirichletShiftCM]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hsub, dirichletCM_coe]

/-- **The recentred Dirichlet kernel is a trigonometric polynomial of degree at most `n`.** The
addition formula `cos (m (t - a)) = cos (m a) cos (m t) + sin (m a) sin (m t)` expands it in the
real trigonometric system. -/
theorem dirichletShiftCM_mem_trigPolyLE (n : ℕ) (a : ℝ) :
    dirichletShiftCM n a ∈ trigPolyLE (2 * π) n := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  set q : C(AddCircle (2 * π), ℝ) :=
    (2 : ℝ)⁻¹ • trigFun (2 * π) 0
      + (∑ m ∈ Finset.Icc 1 n, ((√2)⁻¹ * Real.cos (m * a)) • trigFun (2 * π) (m : ℤ)
        + ∑ m ∈ Finset.Icc 1 n, ((√2)⁻¹ * Real.sin (m * a)) • trigFun (2 * π) (-(m : ℤ)))
    with hq
  have hmem : q ∈ trigPolyLE (2 * π) n := by
    refine Submodule.add_mem _
      (Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by simp)))
      (Submodule.add_mem _ (Submodule.sum_mem _ fun m hm => ?_)
        (Submodule.sum_mem _ fun m hm => ?_))
    · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by
        simpa using (Finset.mem_Icc.1 hm).2))
    · exact Submodule.smul_mem _ _ (trigFun_mem_trigPolyLE (by
        simpa using (Finset.mem_Icc.1 hm).2))
  have heq : dirichletShiftCM n a = q := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | _ t =>
      have hterm : ∀ m ∈ Finset.Icc 1 n,
          ((√2)⁻¹ * Real.cos (m * a)) * trigFun (2 * π) (m : ℤ) ↑t
            + ((√2)⁻¹ * Real.sin (m * a)) * trigFun (2 * π) (-(m : ℤ)) ↑t
            = Real.cos (m * (t - a)) := by
        intro m hm
        have hm0 : (0 : ℤ) < (m : ℤ) := by
          have := (Finset.mem_Icc.1 hm).1; omega
        rw [trigFun_coe_of_pos hm0, trigFun_coe_of_neg (by omega : (-(m : ℤ)) < 0)]
        push_cast
        rw [neg_neg, mul_sub, Real.cos_sub]
        field_simp
      rw [dirichletShiftCM_coe, dirichletKernel_apply, hq]
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
        Finset.sum_apply, smul_eq_mul, trigFun_zero, ContinuousMap.one_apply, mul_one,
        ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl hterm]
      norm_num
  rw [heq]
  exact hmem

/-! ### The kernel at the differences of the equispaced nodes -/

/-- **The Dirichlet kernel at the differences of the `2 n + 1` equispaced nodes**: it is
`(2 n + 1)/2` at `0` and vanishes at every other difference, because `(n + 1/2)(xₖ - xⱼ)` is an
integer multiple of `π` while `(xₖ - xⱼ)/2` is not. This is what makes `2 Dₙ(· - xⱼ)/(2 n + 1)` the
cardinal functions of trigonometric interpolation. -/
theorem dirichletKernel_node_sub (n : ℕ) (d : ℤ) (hd : d.natAbs ≤ 2 * n) :
    dirichletKernel n (2 * π * d / (2 * n + 1))
      = if d = 0 then (2 * (n : ℝ) + 1) / 2 else 0 := by
  have hN : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  rcases eq_or_ne d 0 with rfl | hd0
  · have h0 : 2 * π * ((0 : ℤ) : ℝ) / (2 * (n : ℝ) + 1) = 0 := by simp
    rw [ite_eq_left rfl, h0, dirichletKernel_apply]
    simp only [mul_zero, Real.cos_zero, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
    ring
  · rw [ite_eq_right hd0]
    have hhalf : 2 * π * (d : ℝ) / (2 * (n : ℝ) + 1) / 2 = π * d / (2 * (n : ℝ) + 1) := by
      field_simp
    have hsin : Real.sin (2 * π * (d : ℝ) / (2 * (n : ℝ) + 1) / 2) ≠ 0 := by
      rw [hhalf]
      intro hzero
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hzero
      have hk' : (k : ℝ) * (2 * (n : ℝ) + 1) = (d : ℝ) := by
        refine mul_left_cancel₀ Real.pi_ne_zero ?_
        rw [show π * ((k : ℝ) * (2 * (n : ℝ) + 1)) = ((k : ℝ) * π) * (2 * (n : ℝ) + 1) by ring,
          hk]
        field_simp
      have hkz : k * (2 * (n : ℤ) + 1) = d := by exact_mod_cast hk'
      have hkne : k ≠ 0 := by
        rintro rfl
        simp at hkz
        exact hd0 hkz.symm
      have hnat : d.natAbs = k.natAbs * (2 * n + 1) := by
        have habs : (2 * (n : ℤ) + 1).natAbs = 2 * n + 1 := by omega
        rw [← hkz, Int.natAbs_mul, habs]
      have hk1 : 1 ≤ k.natAbs := Int.natAbs_pos.2 hkne
      have hbig : 2 * n + 1 ≤ d.natAbs := by
        rw [hnat]
        calc 2 * n + 1 = 1 * (2 * n + 1) := by ring
          _ ≤ k.natAbs * (2 * n + 1) := Nat.mul_le_mul_right _ hk1
      omega
    rw [dirichletKernel_eq_sin_div hsin]
    have harg : ((n : ℝ) + 1 / 2) * (2 * π * (d : ℝ) / (2 * (n : ℝ) + 1)) = (d : ℝ) * π := by
      field_simp
    rw [harg, Real.sin_int_mul_pi, zero_div]

/-! ### The Lagrange formula for the interpolation projection -/

/-- The recentred Dirichlet kernels take the value `(2 n + 1)/2` at their own node and vanish at
the others, so `2 Dₙ(· - xⱼ)/(2 n + 1)` are the cardinal functions of the interpolation problem. -/
theorem dirichletShiftCM_apply_node (n : ℕ) (j k : Fin (2 * n + 1)) :
    dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) (trigInterpNode (2 * π) n k)
      = if j = k then (2 * (n : ℝ) + 1) / 2 else 0 := by
  have hsub : ((k : ℕ) : ℝ) * (2 * π) / (2 * (n : ℝ) + 1)
      - ((j : ℕ) : ℝ) * (2 * π) / (2 * (n : ℝ) + 1)
      = 2 * π * (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) / (2 * (n : ℝ) + 1) := by
    push_cast
    ring
  rw [trigInterpNode, dirichletShiftCM_coe, hsub, dirichletKernel_node_sub n _ ?_]
  · congr 1
    simp only [eq_iff_iff, sub_eq_zero]
    constructor
    · intro h
      exact Fin.ext (by exact_mod_cast h.symm)
    · rintro rfl
      rfl
  · have hj : (j : ℕ) ≤ 2 * n := by omega
    have hk : (k : ℕ) ≤ 2 * n := by omega
    omega


/-- **The Lagrange formula for trigonometric interpolation** ([han2009theoretical], (3.7.19)). The
trigonometric interpolant of `f` at the `2 n + 1` equispaced nodes of a period is `2/(2 n + 1)`
times the sum of the recentred Dirichlet kernels weighted by the nodal values:
`𝓘ₙ f = (2/(2 n + 1)) ∑ⱼ f(xⱼ) Dₙ(· - xⱼ)`. -/
theorem trigInterpCLM_eq_sum_dirichletShiftCM (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    trigInterpCLM (2 * π) n f
      = (2 / (2 * (n : ℝ) + 1)) •
        ∑ j : Fin (2 * n + 1),
          f (trigInterpNode (2 * π) n j) •
            dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) := by
  have hN : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  refine (eq_trigInterpCLM ?_ ?_).symm
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (dirichletShiftCM_mem_trigPolyLE n _))
  · intro k
    simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      smul_eq_mul, dirichletShiftCM_apply_node]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ k) h), ite_eq_left rfl]
    field_simp

/-- The Lagrange formula for trigonometric interpolation ([han2009theoretical], (3.7.19)),
pointwise on `ℝ`: `𝓘ₙ f (x) = (2/(2 n + 1)) ∑ⱼ Dₙ(x - xⱼ) f(xⱼ)`. -/
theorem trigInterpCLM_coe_apply (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) (x : ℝ) :
    trigInterpCLM (2 * π) n f ↑x
      = 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          dirichletKernel n (x - (j : ℕ) * (2 * π) / (2 * n + 1)) *
            f (trigInterpNode (2 * π) n j) := by
  rw [trigInterpCLM_eq_sum_dirichletShiftCM]
  simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul,
    dirichletShiftCM_coe]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)

/-! ### The Lebesgue function of trigonometric interpolation -/

/-- **The cardinal functions of trigonometric interpolation** at the `2 n + 1` equispaced nodes are
the recentred Dirichlet kernels `2 Dₙ(· - xⱼ)/(2 n + 1)` ([han2009theoretical], Exercise 3.7.5).
They are trigonometric polynomials of degree at most `n` taking the value `1` at `xⱼ` and `0` at
the other nodes, and the interpolation problem has only one such solution. -/
theorem cardinalBasisCM_trigInterpNode (n : ℕ) (j : Fin (2 * n + 1)) :
    (isUnisolvent_trigPolyLE (2 * π) (injective_trigInterpNode (2 * π) n)).cardinalBasisCM j
      = (2 / (2 * (n : ℝ) + 1)) • dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) := by
  have hN : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  set h := isUnisolvent_trigPolyLE (2 * π) (injective_trigInterpNode (2 * π) n) with hh
  have hmem : (2 / (2 * (n : ℝ) + 1)) • dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1))
      ∈ trigPolyLE (2 * π) n :=
    Submodule.smul_mem _ _ (dirichletShiftCM_mem_trigPolyLE n _)
  have hval : ∀ k, ((⟨_, hmem⟩ : trigPolyLE (2 * π) n) : C(AddCircle (2 * π), ℝ))
      (trigInterpNode (2 * π) n k)
      = (Pi.single j 1 : Fin (2 * n + 1) → ℝ) k := by
    intro k
    simp only [ContinuousMap.smul_apply, smul_eq_mul, dirichletShiftCM_apply_node, Pi.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceIte]
      field_simp
    · simp [hjk, Ne.symm hjk]
  have hfin := h.eq_interpolate (u := ⟨_, hmem⟩) hval
  rw [Approximation.IsUnisolvent.cardinalBasisCM]
  exact (congrArg Subtype.val hfin).symm

/-- **The Lebesgue constant of trigonometric interpolation.** The operator norm of `𝓘ₙ` is the
largest value of its Lebesgue function

`Λₙ(x) = (2/(2 n + 1)) ∑_{j=0}^{2n} |Dₙ(x - xⱼ)|`.

Rivlin's bound `‖𝓘ₙ‖ ≤ 1 + (2/π) log n` ([han2009theoretical], (3.7.20)) is a bound on this
supremum; it is not proved here. -/
theorem isGreatest_norm_trigInterpCLM (n : ℕ) :
    IsGreatest
      (Set.range fun t : ℝ => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          |dirichletKernel n (t - (j : ℕ) * (2 * π) / (2 * n + 1))|)
      ‖trigInterpCLM (2 * π) n‖ := by
  have hN : (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) := by positivity
  have h := (isUnisolvent_trigPolyLE (2 * π)
    (injective_trigInterpNode (2 * π) n)).isGreatest_norm_interpCLM
  have hfun : ∀ x : AddCircle (2 * π),
      ∑ j : Fin (2 * n + 1),
          |(isUnisolvent_trigPolyLE (2 * π)
            (injective_trigInterpNode (2 * π) n)).cardinalBasisCM j x|
        = 2 / (2 * (n : ℝ) + 1) *
          ∑ j : Fin (2 * n + 1), |dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) x| := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cardinalBasisCM_trigInterpNode, ContinuousMap.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg hN]
  simp only [hfun] at h
  have hrange : (Set.range fun x : AddCircle (2 * π) => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1), |dirichletShiftCM n ((j : ℕ) * (2 * π) / (2 * n + 1)) x|)
      = Set.range fun t : ℝ => 2 / (2 * (n : ℝ) + 1) *
        ∑ j : Fin (2 * n + 1),
          |dirichletKernel n (t - (j : ℕ) * (2 * π) / (2 * n + 1))| := by
    refine Set.ext fun y => ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      induction x using QuotientAddGroup.induction_on with
      | _ t => exact ⟨t, by simp only [dirichletShiftCM_coe]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(t : AddCircle (2 * π)), by simp only [dirichletShiftCM_coe]⟩
  rwa [hrange] at h

end PeriodicCont

/-! ### Rivlin's bound for the Lebesgue constant -/

/-- The power series of `log ((1 + w) / (1 - w))` has nonnegative terms for `0 ≤ w < 1`, so it
dominates the sum of its first two: `2 w + (2/3) w³ ≤ log (1 + w) - log (1 - w)`. -/
private theorem add_le_log_sub_log {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    2 * w + 2 / 3 * w ^ 3 ≤ Real.log (1 + w) - Real.log (1 - w) := by
  have habs : |w| < 1 := by rwa [abs_of_nonneg hw0]
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * w ^ (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) ≤ 1 / (2 * (k : ℝ) + 1) := by positivity
    have : (0 : ℝ) ≤ w ^ (2 * k + 1) := pow_nonneg hw0 _
    positivity
  have h := sum_le_hasSum (Finset.range 2) (fun i _ => hnn i) hsum
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-- The elementary inequality behind the sharp constant of the midpoint bound: for `0 < h ≤ π/6`,
`h ≤ sin h + (sin h)³ / 3`. -/
private theorem le_sin_add_sin_cube_div {h : ℝ} (hh0 : 0 < h) (hh : h ≤ π / 6) :
    h ≤ Real.sin h + Real.sin h ^ 3 / 3 := by
  have hb : h ≤ 2 / 3 := by
    have := Real.pi_le_four
    linarith
  have hs : h - h ^ 3 / 6 ≤ Real.sin h := Real.sin_ge_sub_cube hh0.le
  have hsq : h ^ 2 ≤ 0.45 := by nlinarith
  have hcube : h ^ 3 ≤ 0.45 * h := by nlinarith
  have h1 : 0.925 * h ≤ Real.sin h := by linarith
  have h2 : (0.925 * h) ^ 3 ≤ Real.sin h ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : (0.925 * h) ^ 3 = 0.791453125 * h ^ 3 := by ring
  nlinarith [pow_pos hh0 3]

/-- **The midpoint bound for the cosecant.** For `0 < h ≤ π/6` and `h < φ < π - h`,

`2 h / sin φ ≤ log (tan ((φ + h)/2)) - log (tan ((φ - h)/2))`.

This is the comparison `2h / sin φ ≤ ∫_{φ - h}^{φ + h} dy / sin y` in algebraic form: the
right-hand side is `log ((sin φ + sin h)/(sin φ - sin h))`, and the first two terms of the power
series of that logarithm already dominate the left-hand side. -/
private theorem two_mul_div_sin_le {h φ : ℝ} (hh0 : 0 < h) (hh : h ≤ π / 6)
    (hφ1 : h < φ) (hφ2 : φ < π - h) :
    2 * h / Real.sin φ
      ≤ Real.log (Real.tan ((φ + h) / 2)) - Real.log (Real.tan ((φ - h) / 2)) := by
  have hpi := Real.pi_pos
  set A := (φ + h) / 2 with hA
  set B := (φ - h) / 2 with hB
  have hB0 : 0 < B := by rw [hB]; linarith
  have hA2 : A < π / 2 := by rw [hA]; linarith
  have hAB : B < A := by rw [hA, hB]; linarith
  have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB0 (by linarith)
  have hcosA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith, hA2⟩
  have hcosB : 0 < Real.cos B := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : Real.sin φ = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
    rw [show φ = A + B by rw [hA, hB]; ring, Real.sin_add]
  have he : Real.sin h = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by
    rw [show h = A - B by rw [hA, hB]; ring, Real.sin_sub]
  have hs0 : 0 < Real.sin φ := by rw [hs]; positivity
  have he0 : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith)
  have hes : Real.sin h < Real.sin φ := by
    rw [hs, he]; nlinarith [mul_pos hcosA hsinB]
  set w := Real.sin h / Real.sin φ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw1 : w < 1 := by rw [hw, div_lt_one hs0]; exact hes
  -- the ratio of the two tangents is `(1 + w)/(1 - w)`
  have htanA : 0 < Real.tan A := by rw [Real.tan_eq_sin_div_cos]; positivity
  have htanB : 0 < Real.tan B := by rw [Real.tan_eq_sin_div_cos]; positivity
  have hratio : Real.tan A / Real.tan B = (1 + w) / (1 - w) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, hw, hs, he]
    field_simp
    ring
  have hlog : Real.log (Real.tan A) - Real.log (Real.tan B) = Real.log (1 + w) - Real.log (1 - w) :=
    by rw [← Real.log_div htanA.ne' htanB.ne', hratio,
      Real.log_div (by linarith) (by linarith)]
  rw [hlog]
  refine le_trans ?_ (add_le_log_sub_log hw0 hw1)
  -- and the first two terms of the series already dominate `2 h / sin φ`
  have hle : h ≤ Real.sin h + Real.sin h ^ 3 / 3 := le_sin_add_sin_cube_div hh0 hh
  have hs2 : Real.sin φ ^ 2 ≤ 1 := by nlinarith [Real.sin_le_one φ, Real.neg_one_le_sin φ]
  have hnum : 0 ≤ 2 * Real.sin h * Real.sin φ ^ 2 + 2 / 3 * Real.sin h ^ 3
      - 2 * h * Real.sin φ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sin φ)) (sub_nonneg.2 hle),
      mul_nonneg (sub_nonneg.2 hs2) (pow_pos he0 3).le]
  rw [← sub_nonneg, hw]
  have hid : 2 * (Real.sin h / Real.sin φ) + 2 / 3 * (Real.sin h / Real.sin φ) ^ 3
      - 2 * h / Real.sin φ
      = (2 * Real.sin h * Real.sin φ ^ 2 + 2 / 3 * Real.sin h ^ 3 - 2 * h * Real.sin φ ^ 2)
        / Real.sin φ ^ 3 := by
    field_simp
  rw [hid]
  exact div_nonneg hnum (by positivity)

/-- A single interior term of the Lebesgue function of trigonometric interpolation is bounded by a
telescoping difference. Here `q = π / (2 (2 n + 1))` is half the spacing of the points
`x/2`, and the hypotheses place `x` at distance at least `2 q` from `0` and from `π`. -/
private theorem dirichlet_mid_le {n : ℕ} {q x : ℝ} (hq0 : 0 < q) (hq6 : q ≤ π / 6)
    (hqN : 2 * (2 * (n : ℝ) + 1) * q = π) (hx1 : 2 * q ≤ x) (hx2 : x ≤ π - 2 * q) :
    2 / (2 * (n : ℝ) + 1) * |dirichletKernel n (2 * x)|
      ≤ 1 / π * (Real.log (Real.tan ((x + q) / 2)) - Real.log (Real.tan ((x - q) / 2))) := by
  have hpi := Real.pi_pos
  have hN0 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hkey : 2 * Real.sin x * dirichletKernel n (2 * x)
      = Real.sin (((n : ℝ) + 1 / 2) * (2 * x)) := by
    have := two_mul_sin_half_mul_dirichletKernel n (2 * x)
    rwa [show 2 * x / 2 = x by ring] at this
  have habs : |dirichletKernel n (2 * x)| ≤ 1 / (2 * Real.sin x) := by
    rw [le_div_iff₀ (show (0:ℝ) < 2 * Real.sin x by positivity)]
    have h1 : |dirichletKernel n (2 * x)| * (2 * Real.sin x)
        = |2 * Real.sin x * dirichletKernel n (2 * x)| := by
      rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.sin x by positivity)]
      ring
    rw [h1, hkey]
    exact Real.abs_sin_le_one _
  have hmain := two_mul_div_sin_le (φ := x) hq0 hq6 (by linarith) (by linarith)
  have hrw : 2 / (2 * (n : ℝ) + 1) * (1 / (2 * Real.sin x)) = 1 / π * (2 * q / Real.sin x) := by
    rw [← hqN]
    field_simp
  calc 2 / (2 * (n : ℝ) + 1) * |dirichletKernel n (2 * x)|
      ≤ 2 / (2 * (n : ℝ) + 1) * (1 / (2 * Real.sin x)) := by
        exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = 1 / π * (2 * q / Real.sin x) := hrw
    _ ≤ 1 / π * (Real.log (Real.tan ((x + q) / 2)) - Real.log (Real.tan ((x - q) / 2))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

/-- A sum whose first and last terms are at most `1` and whose interior terms are dominated by a
telescoping difference is at most `2` plus the total difference. -/
private theorem sum_le_of_telescope {M : ℕ} (G Ψ : ℕ → ℝ) (C : ℝ)
    (hend : ∀ c, G c ≤ 1) (hmid : ∀ i, i < M → G (i + 1) ≤ C * (Ψ (i + 1) - Ψ i)) :
    ∑ c ∈ Finset.range (M + 2), G c ≤ 2 + C * (Ψ M - Ψ 0) := by
  have h1 : ∑ c ∈ Finset.range (M + 2), G c
      = (∑ i ∈ Finset.range M, G (i + 1)) + G (M + 1) + G 0 := by
    rw [Finset.sum_range_succ' G (M + 1), Finset.sum_range_succ (fun i => G (i + 1)) M]
  have h2 : ∑ i ∈ Finset.range M, G (i + 1) ≤ ∑ i ∈ Finset.range M, C * (Ψ (i + 1) - Ψ i) :=
    Finset.sum_le_sum fun i hi => hmid i (Finset.mem_range.1 hi)
  have h3 : ∑ i ∈ Finset.range M, C * (Ψ (i + 1) - Ψ i) = C * (Ψ M - Ψ 0) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub Ψ M]
  rw [h1]
  have e1 := hend (M + 1)
  have e2 := hend 0
  linarith [h2.trans_eq h3]

/-- **The Lebesgue function of trigonometric interpolation is at most `2 + (2/π) log (2 n + 1)`.**
The evaluation point is written as `2 π (m + δ) / (2 n + 1)` with `0 ≤ δ < 1`; since the nodes are
`2 π j / (2 n + 1)` and the kernel has period `2 π`, the sum over the nodes is the sum below. -/
private theorem lebesgueFun_shift_le (n : ℕ) (hn : 1 ≤ n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    2 / (2 * (n : ℝ) + 1) * ∑ c ∈ Finset.range (2 * n + 1),
        |dirichletKernel n (2 * π * ((c : ℝ) + δ) / (2 * (n : ℝ) + 1))|
      ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < π := by
    have h := Real.sin_lt (show (0 : ℝ) < π / 6 by positivity)
    rw [Real.sin_pi_div_six] at h
    linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hN3 : (3 : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  have hN0 : (0 : ℝ) < 2 * ((m + 1 : ℕ) : ℝ) + 1 := by linarith
  set N : ℝ := 2 * ((m + 1 : ℕ) : ℝ) + 1 with hNdef
  set q : ℝ := π / (2 * N) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hqN : 2 * N * q = π := by rw [hqdef]; field_simp
  have hq6 : q ≤ π / 6 := by
    rw [hqdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- rewrite the kernel arguments in terms of the half-spacing `q`
  have harg : ∀ c : ℝ, 2 * π * (c + δ) / N = 2 * (2 * q * (c + δ)) := by
    intro c
    rw [hqdef]
    field_simp
  simp only [harg]
  rw [Finset.mul_sum]
  -- the two end terms are at most one, the interior ones telescope
  set G : ℕ → ℝ := fun c => 2 / N * |dirichletKernel (m + 1) (2 * (2 * q * ((c : ℝ) + δ)))|
    with hGdef
  set Ψ : ℕ → ℝ := fun i => Real.log (Real.tan ((2 * q * ((i : ℝ) + 1 + δ) - q) / 2)) with hΨdef
  have hend : ∀ c : ℕ, G c ≤ 1 := by
    intro c
    have hb := abs_dirichletKernel_le (m + 1) (2 * (2 * q * ((c : ℝ) + δ)))
    have hhalf : ((m + 1 : ℕ) : ℝ) + 1 / 2 = N / 2 := by rw [hNdef]; ring
    rw [hhalf] at hb
    rw [hGdef]
    calc 2 / N * |dirichletKernel (m + 1) (2 * (2 * q * ((c : ℝ) + δ)))|
        ≤ 2 / N * (N / 2) := by exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 1 := by field_simp
  have hmid : ∀ i : ℕ, i < 2 * m + 1 → G (i + 1) ≤ 1 / π * (Ψ (i + 1) - Ψ i) := by
    intro i hi
    have hiR : ((i : ℝ) + 1) ≤ 2 * (m : ℝ) + 1 := by
      have : (i : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hi
      linarith
    have hx1 : 2 * q ≤ 2 * q * ((i : ℝ) + 1 + δ) := by nlinarith
    have hx2 : 2 * q * ((i : ℝ) + 1 + δ) ≤ π - 2 * q := by
      have hNv : N = 2 * (m : ℝ) + 3 := by rw [hNdef]; push_cast; ring
      nlinarith
    have hmain := dirichlet_mid_le (n := m + 1) hq0 hq6 (by rw [← hNdef] at *; linarith [hqN])
      hx1 hx2
    have hG : G (i + 1) = 2 / N * |dirichletKernel (m + 1) (2 * (2 * q * ((i : ℝ) + 1 + δ)))| := by
      rw [hGdef]
      push_cast
      ring_nf
    have hΨ1 : Ψ (i + 1) = Real.log (Real.tan ((2 * q * ((i : ℝ) + 1 + δ) + q) / 2)) := by
      rw [hΨdef]
      push_cast
      ring_nf
    have hΨ0 : Ψ i = Real.log (Real.tan ((2 * q * ((i : ℝ) + 1 + δ) - q) / 2)) := by rw [hΨdef]
    rw [hG, hΨ1, hΨ0]
    exact hmain
  refine (sum_le_of_telescope (M := 2 * m + 1) G Ψ (1 / π) hend hmid).trans ?_
  -- the total telescoped difference is at most `2 log N`
  have hb0 : 0 < (3 - 2 * δ) * q / 2 := by nlinarith
  have hbpi : (3 - 2 * δ) * q / 2 < π / 2 := by nlinarith
  have ha0 : 0 < (1 + 2 * δ) * q / 2 := by nlinarith
  have hapi : (1 + 2 * δ) * q / 2 < π / 2 := by nlinarith
  have hΨtop : Ψ (2 * m + 1) = -Real.log (Real.tan ((3 - 2 * δ) * q / 2)) := by
    have harg2 : (2 * q * (((2 * m + 1 : ℕ) : ℝ) + 1 + δ) - q) / 2
        = π / 2 - (3 - 2 * δ) * q / 2 := by
      have hNv : N = 2 * (m : ℝ) + 3 := by rw [hNdef]; push_cast; ring
      push_cast
      nlinarith [hqN]
    rw [hΨdef]
    simp only []
    rw [harg2, Real.tan_pi_div_two_sub, Real.log_inv]
  have hΨbot : Ψ 0 = Real.log (Real.tan ((1 + 2 * δ) * q / 2)) := by
    rw [hΨdef]
    norm_num
    ring_nf
  have hla : Real.log ((1 + 2 * δ) * q / 2) ≤ Real.log (Real.tan ((1 + 2 * δ) * q / 2)) :=
    Real.log_le_log ha0 (Real.lt_tan ha0 hapi).le
  have hlb : Real.log ((3 - 2 * δ) * q / 2) ≤ Real.log (Real.tan ((3 - 2 * δ) * q / 2)) :=
    Real.log_le_log hb0 (Real.lt_tan hb0 hbpi).le
  have hprod : Real.log ((3 - 2 * δ) * q / 2) + Real.log ((1 + 2 * δ) * q / 2)
      = Real.log (((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2)) :=
    (Real.log_mul hb0.ne' ha0.ne').symm
  have hge : 1 / N ^ 2 ≤ ((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2) := by
    have hq2 : q = π / (2 * N) := hqdef
    have h16 : (16 : ℝ) ≤ 3 * π ^ 2 := by nlinarith
    rw [hq2, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg δ, mul_nonneg hδ0 (sub_nonneg.2 hδ1.le)]
  have hlog2 : -(2 * Real.log N) ≤ Real.log (((3 - 2 * δ) * q / 2) * ((1 + 2 * δ) * q / 2)) := by
    have h := Real.log_le_log (by positivity) hge
    rw [one_div, Real.log_inv, Real.log_pow] at h
    push_cast at h
    linarith
  have hfin : Ψ (2 * m + 1) - Ψ 0 ≤ 2 * Real.log N := by
    rw [hΨtop, hΨbot]
    linarith
  have : 1 / π * (Ψ (2 * m + 1) - Ψ 0) ≤ 2 / π * Real.log N := by
    have := mul_le_mul_of_nonneg_left hfin (le_of_lt (by positivity : (0:ℝ) < 1 / π))
    calc 1 / π * (Ψ (2 * m + 1) - Ψ 0) ≤ 1 / π * (2 * Real.log N) := this
      _ = 2 / π * Real.log N := by ring
  linarith

/-- Summing an `N`-periodic function of an integer over `N` consecutive integers, in either
direction, always gives the same value. -/
private theorem sum_range_sub_of_periodic {N : ℕ} (hN : 0 < N) (g : ℤ → ℝ)
    (hg : ∀ c : ℤ, g (c + N) = g c) (M : ℤ) :
    ∑ j ∈ Finset.range N, g (M - j) = ∑ c ∈ Finset.range N, g c := by
  have hstep : ∀ K : ℤ, (∑ j ∈ Finset.range N, g (K + 1 - j))
      = ∑ j ∈ Finset.range N, g (K - j) := by
    intro K
    obtain ⟨L, rfl⟩ : ∃ L, N = L + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun j : ℕ => g (K + 1 - j)) L,
      Finset.sum_range_succ (fun j : ℕ => g (K - j)) L]
    have h1 : ∀ i : ℕ, g (K + 1 - ((i + 1 : ℕ) : ℤ)) = g (K - i) := by
      intro i
      congr 1
      push_cast
      ring
    have h2 : g (K + 1 - ((0 : ℕ) : ℤ)) = g (K - L) := by
      have h3 := hg (K - L)
      rw [show K - (L : ℤ) + ((L + 1 : ℕ) : ℤ) = K + 1 by push_cast; ring] at h3
      rw [show ((0 : ℕ) : ℤ) = 0 by norm_num, sub_zero, ← h3]
    simp only [h1, h2]
  have hall : ∀ K : ℤ, (∑ j ∈ Finset.range N, g (K - j))
      = ∑ j ∈ Finset.range N, g (0 - j) := by
    intro K
    induction K using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [hstep]; exact ih
    | pred i ih =>
      rw [← hstep (-(i : ℤ) - 1), show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
      exact ih
  have hbase : (∑ j ∈ Finset.range N, g ((N : ℤ) - 1 - j)) = ∑ c ∈ Finset.range N, g c := by
    rw [← Finset.sum_range_reflect (fun c : ℕ => g c) N]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < N := Finset.mem_range.1 hj
    congr 1
    have h1 : (1 : ℕ) ≤ N := hN
    push_cast [Nat.cast_sub (by omega : j ≤ N - 1), Nat.cast_sub h1]
    ring
  rw [hall M, ← hall ((N : ℤ) - 1), hbase]

/-- **Rivlin's bound for the Lebesgue constant of trigonometric interpolation**, with the constant
`2` in place of the `1` of [han2009theoretical], (3.7.20):

`‖𝓘ₙ‖ ≤ 2 + (2/π) log (2 n + 1)`.

The book prints `‖𝓘ₙ‖ ≤ 1 + (2/π) log n` for `n ≥ 1`, quoting Rivlin; as printed that is false —
at `n = 1` the Lebesgue function attains `5/3` at the midpoint of two nodes while the right-hand
side is `1`. The `n` of Rivlin's bound is the *number of nodes*, here `2 n + 1`, and the sharp
statement is `‖𝓘ₙ‖ ≤ 1 + (2/π) log (2 n + 1)`, which has no slack to speak of: its two sides
differ by about `0.04` for every `n`. What is proved here keeps the sharp `2/π`, and so gives the
`𝓞(log n)` growth that the convergence rate (3.7.22) consumes, but pays a larger additive
constant, one for each of the two nodes nearest the evaluation point.

The proof bounds the Lebesgue function `(2/(2n+1)) ∑ⱼ |Dₙ(x - xⱼ)|` term by term. Writing
`x = 2π(m + δ)/(2n+1)` with `0 ≤ δ < 1`, the terms are `|Dₙ|` at the points `2π(c + δ)/(2n+1)`,
`0 ≤ c ≤ 2n`. The two extreme ones are bounded by `|Dₙ| ≤ n + 1/2`; each interior one is
`|sin(π(c+δ))| / (2 sin φ_c) ≤ 1/(2 sin φ_c)` with `φ_c = π(c+δ)/(2n+1)`, and
`(1/(2n+1)) / sin φ ≤ (1/π) (log tan ((φ+q)/2) - log tan ((φ-q)/2))` for `q = π/(2(2n+1))` half
the spacing — the midpoint comparison with `∫ dy / sin y`. Those differences telescope to
`log (4/(3 q²)) ≤ 2 log (2n+1)`. -/
theorem norm_trigInterpCLM_le (n : ℕ) :
    ‖trigInterpCLM (2 * π) n‖ ≤ 2 + 2 / π * Real.log (2 * (n : ℝ) + 1) := by
  have hpi := Real.pi_pos
  obtain ⟨t, ht⟩ := (PeriodicCont.isGreatest_norm_trigInterpCLM n).1
  rw [← ht]
  simp only []
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_add, Real.log_one, mul_zero, add_zero,
      dirichletKernel_zero]
    norm_num
  have hN0 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hcongr : ∀ x y : ℝ, x = y → |dirichletKernel n x| = |dirichletKernel n y| :=
    fun x y h => by rw [h]
  -- write the evaluation point as `2 π (M + δ) / (2 n + 1)` with `0 ≤ δ < 1`
  obtain ⟨M, δ, hδ0, hδ1, hMval⟩ :
      ∃ (M : ℤ) (δ : ℝ), 0 ≤ δ ∧ δ < 1 ∧ (M : ℝ) = (2 * (n : ℝ) + 1) * t / (2 * π) - δ :=
    ⟨⌊(2 * (n : ℝ) + 1) * t / (2 * π)⌋, Int.fract _, Int.fract_nonneg _, Int.fract_lt_one _,
      by rw [eq_sub_iff_add_eq]; exact Int.floor_add_fract _⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ → ℝ,
      g = fun c : ℤ => |dirichletKernel n (2 * π * ((c : ℝ) + δ) / (2 * (n : ℝ) + 1))| := ⟨_, rfl⟩
  have hgper : ∀ c : ℤ, g (c + ((2 * n + 1 : ℕ) : ℤ)) = g c := by
    intro c
    rw [hgdef]
    simp only []
    refine (hcongr _ (2 * π * ((c : ℝ) + δ) / (2 * (n : ℝ) + 1) + 2 * π) ?_).trans ?_
    · push_cast
      field_simp
      ring
    · rw [dirichletKernel_periodic n]
  have hterm : ∀ j : ℕ,
      |dirichletKernel n (t - (j : ℝ) * (2 * π) / (2 * (n : ℝ) + 1))| = g (M - j) := by
    intro j
    rw [hgdef]
    simp only []
    refine hcongr _ _ ?_
    push_cast
    rw [hMval]
    field_simp
    ring
  have hfin : ∑ j : Fin (2 * n + 1),
        |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (2 * (n : ℝ) + 1))|
      = ∑ j ∈ Finset.range (2 * n + 1), g (M - (j : ℤ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => g (M - (j : ℤ))) (2 * n + 1)]
    exact Finset.sum_congr rfl fun j _ => hterm j
  rw [hfin, sum_range_sub_of_periodic (by omega) g hgper M]
  simp only [hgdef, Int.cast_natCast]
  exact lebesgueFun_shift_le n hn hδ0 hδ1

/-- **The Lebesgue constant of trigonometric interpolation at three nodes is at least `5/3`.**
The Lebesgue function `Λ₁(x) = (2/3) ∑ⱼ |D₁(x - xⱼ)|` takes the value `5/3` at `x = π/3`, the
midpoint of two of the three nodes.

This is what refutes the bound `1 + (2/π) log n` printed as [han2009theoretical], (3.7.20): at
`n = 1` its right-hand side is `1`. -/
theorem le_norm_trigInterpCLM_one : 5 / 3 ≤ ‖trigInterpCLM (2 * π) 1‖ := by
  have hD : ∀ t : ℝ, dirichletKernel 1 t = 1 / 2 + Real.cos t := by
    intro t
    rw [dirichletKernel_apply]
    norm_num
  have h := (PeriodicCont.isGreatest_norm_trigInterpCLM 1).2 (Set.mem_range_self (π / 3))
  refine le_trans (le_of_eq ?_) h
  rw [Fin.sum_univ_three]
  simp only [hD, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_one]
  rw [show π / 3 - (0 : ℝ) * (2 * π) / (2 * 1 + 1) = π / 3 by norm_num,
    show π / 3 - (1 : ℝ) * (2 * π) / (2 * 1 + 1) = -(π / 3) by ring,
    show π / 3 - (2 : ℝ) * (2 * π) / (2 * 1 + 1) = -π by ring,
    Real.cos_neg, Real.cos_neg, Real.cos_pi, Real.cos_pi_div_three]
  norm_num

