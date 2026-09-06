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
  `Λₙ(x) = (2/(2 n + 1)) ∑ⱼ |Dₙ(x - xⱼ)|`. Rivlin's bound `‖𝓘ₙ‖ ≤ 1 + (2/π) log n` of
  [han2009theoretical], (3.7.20) is a bound on that supremum and is not proved.

## References

[han2009theoretical], (3.7.19) and Exercise 3.7.5.
-/

open Set

open scoped Real

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
