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
  `‖𝓘ₙ‖ ≤ 2 + (2/π) log (2 n + 1)`, read off from `SineSum.sum_term_le` of
  `Numlib/Analysis/SpecialFunctions/SineSum` at `M = 2 n + 1`. It carries the sharp coefficient
  `2/π` of [han2009theoretical], (3.7.20) but a larger additive constant; the theorem's own doc
  comment says why the constant printed there is not the one proved here.
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

The estimate itself is `SineSum.sum_term_le` of `Numlib/Analysis/SpecialFunctions/SineSum`, which
bounds
`∑_{i < M} |sin (π (k + i + δ))| / (M |sin (π (k + i + δ)/M)|)` by `2 + (2/π) log M` for every
`M ≥ 3`. Writing the evaluation point as `x = 2 π (c₀ + δ)/M` with `M = 2 n + 1` and `0 ≤ δ < 1`,
the closed form `2 sin (u/2) Dₙ(u) = sin (M u / 2)` turns each term of the Lebesgue function into
`(2/M) |Dₙ(x - xⱼ)| = |sin (π (c + δ))| / (M |sin (π (c + δ)/M)|)` with `c = c₀ - j`, and those `M`
indices are consecutive. The identification fails only for `δ = 0`, that is when `x` is itself a
node; there every term but one vanishes and the Lebesgue function is `1`. -/
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
  set M : ℕ := 2 * n + 1 with hMdef
  have hM3 : 3 ≤ M := by omega
  have hMr : ((M : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by rw [hMdef]; push_cast; ring
  have hM0 : (0 : ℝ) < (M : ℝ) := by rw [hMr]; positivity
  have hMne : (M : ℝ) ≠ 0 := hM0.ne'
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    refine Real.log_nonneg ?_
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hMr]
    linarith
  rw [← hMr]
  -- write the evaluation point as `2 π (c₀ + δ) / M` with `0 ≤ δ < 1`
  set s : ℝ := (M : ℝ) * t / (2 * π) with hs
  set c0 : ℤ := ⌊s⌋ with hc0
  set δ : ℝ := Int.fract s with hδ
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  have hsval : (c0 : ℝ) + δ = s := Int.floor_add_fract s
  have harg : ∀ j : ℕ, t - (j : ℝ) * (2 * π) / (M : ℝ)
      = 2 * π * (((c0 - (j : ℤ) : ℤ) : ℝ) + δ) / (M : ℝ) := by
    intro j
    have hts : t = 2 * π * s / (M : ℝ) := by rw [hs]; field_simp
    push_cast
    rw [hts, ← hsval]
    field_simp
    ring
  -- the closed form of the kernel in the shifted variable
  have hhalf : ∀ z : ℝ, 2 * π * z / (M : ℝ) / 2 = π * z / (M : ℝ) := fun z => by ring
  have hkernel : ∀ z : ℝ, 2 * Real.sin (π * z / (M : ℝ)) * dirichletKernel n (2 * π * z / (M : ℝ))
      = Real.sin (π * z) := by
    intro z
    have h := two_mul_sin_half_mul_dirichletKernel n (2 * π * z / (M : ℝ))
    rw [hhalf] at h
    rw [h]
    congr 1
    rw [hMr]
    field_simp
  have hsinzero : ∀ z : ℝ, Real.sin (π * z / (M : ℝ)) = 0 → ∃ l : ℤ, z = (l : ℝ) * (M : ℝ) := by
    intro z hz
    rw [Real.sin_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    refine ⟨l, ?_⟩
    have h1 : π * ((l : ℝ) * (M : ℝ)) = π * z := by
      have h2 : (l : ℝ) * π * (M : ℝ) = π * z / (M : ℝ) * (M : ℝ) := by rw [hl]
      rw [div_mul_cancel₀ _ hMne] at h2
      linarith
    exact (mul_left_cancel₀ hpi.ne' h1).symm
  by_cases hd : δ = 0
  · -- the evaluation point is a node: only the term at that node survives
    have hj0 : ((c0 % (M : ℤ)).toNat) < M := by
      have h1 : 0 ≤ c0 % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (by omega : M ≠ 0))
      have h2 : c0 % (M : ℤ) < (M : ℤ) :=
        Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < M))
      omega
    have hzero : ∀ j : Fin M, j ≠ ⟨_, hj0⟩ →
        |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))| = 0 := by
      intro j hj
      rw [harg]
      set c : ℤ := c0 - ((j : ℕ) : ℤ) with hc
      have hnd : ¬ ((M : ℤ) ∣ c) := by
        intro hdvd
        have hmod : ((j : ℕ) : ℤ) % (M : ℤ) = c0 % (M : ℤ) :=
          Int.modEq_iff_dvd.mpr (by rw [← hc]; exact hdvd)
        have hjm : ((j : ℕ) : ℤ) % (M : ℤ) = ((j : ℕ) : ℤ) :=
          Int.emod_eq_of_lt (by positivity) (by exact_mod_cast j.2)
        refine hj (Fin.ext ?_)
        have hv : ((j : ℕ) : ℤ) = c0 % (M : ℤ) := by rw [← hjm, hmod]
        simp only []
        omega
      have hsin : Real.sin (π * ((c : ℝ) + δ) / (M : ℝ)) ≠ 0 := by
        intro h
        obtain ⟨l, hl⟩ := hsinzero _ h
        refine hnd ⟨l, ?_⟩
        have hml : (c : ℝ) = (M : ℝ) * (l : ℝ) := by rw [hd] at hl; linarith [hl]
        exact_mod_cast hml
      have hnum : Real.sin (π * ((c : ℝ) + δ)) = 0 := by
        rw [hd, add_zero, Real.sin_eq_zero_iff]
        exact ⟨c, by ring⟩
      have hval : dirichletKernel n (2 * π * ((c : ℝ) + δ) / (M : ℝ)) = 0 := by
        have h := hkernel ((c : ℝ) + δ)
        rw [hnum] at h
        rcases mul_eq_zero.1 h with h' | h'
        · exact absurd (by rcases mul_eq_zero.1 h' with h'' | h'' <;>
            [norm_num at h''; exact h'']) hsin
        · exact h'
      rw [hval, abs_zero]
    have hone : ∑ j : Fin M, |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))|
        = |dirichletKernel n (t - (((c0 % (M : ℤ)).toNat : ℕ) : ℝ) * (2 * π) / (M : ℝ))| :=
      Finset.sum_eq_single_of_mem (⟨_, hj0⟩ : Fin M) (Finset.mem_univ _)
        (fun j _ hj => hzero j hj)
    rw [hone]
    have hb := abs_dirichletKernel_le n
      (t - (((c0 % (M : ℤ)).toNat : ℕ) : ℝ) * (2 * π) / (M : ℝ))
    have hMhalf : 2 / (M : ℝ) * ((n : ℝ) + 1 / 2) = 1 := by rw [hMr]; field_simp
    have h2M : (0 : ℝ) < 2 / (M : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hb h2M.le
    have h2 : 0 ≤ 2 / π * Real.log (M : ℝ) := mul_nonneg (by positivity) hlogM
    linarith
  · -- a generic point: every term is a `SineSum.term`
    have hterm : ∀ j : ℕ, 2 / (M : ℝ) *
        |dirichletKernel n (t - (j : ℝ) * (2 * π) / (M : ℝ))|
        = SineSum.term M δ (c0 - (j : ℤ)) := by
      intro j
      set c : ℤ := c0 - (j : ℤ) with hc
      have hsin : Real.sin (π * ((c : ℝ) + δ) / (M : ℝ)) ≠ 0 := by
        intro h
        obtain ⟨l, hl⟩ := hsinzero _ h
        have hint : δ = ((l * (M : ℤ) - c : ℤ) : ℝ) := by push_cast; linarith
        rcases lt_trichotomy (l * (M : ℤ) - c) 0 with h1 | h1 | h1
        · have h2 : ((l * (M : ℤ) - c : ℤ) : ℝ) < 0 := by exact_mod_cast h1
          linarith
        · exact hd (by rw [hint, h1]; norm_num)
        · have h2 : (1 : ℝ) ≤ ((l * (M : ℤ) - c : ℤ) : ℝ) := by exact_mod_cast h1
          linarith
      have habs : 2 * |Real.sin (π * ((c : ℝ) + δ) / (M : ℝ))|
          * |dirichletKernel n (2 * π * ((c : ℝ) + δ) / (M : ℝ))|
          = |Real.sin (π * ((c : ℝ) + δ))| := by
        have h := congrArg abs (hkernel ((c : ℝ) + δ))
        rwa [abs_mul, abs_mul, abs_two] at h
      have hpos : 0 < |Real.sin (π * ((c : ℝ) + δ) / (M : ℝ))| := abs_pos.2 hsin
      rw [harg, ← hc, SineSum.term, eq_div_iff (by positivity)]
      field_simp
      nlinarith [habs, hpos]
    rw [Finset.mul_sum]
    have hsum : ∑ j : Fin M, 2 / (M : ℝ) *
        |dirichletKernel n (t - ((j : ℕ) : ℝ) * (2 * π) / (M : ℝ))|
        = ∑ i ∈ Finset.range M, SineSum.term M δ ((c0 - (M : ℤ) + 1) + i) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2 / (M : ℝ) *
        |dirichletKernel n (t - (j : ℝ) * (2 * π) / (M : ℝ))|) M]
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      rw [← Finset.sum_range_reflect (fun j : ℕ => SineSum.term M δ (c0 - (j : ℤ))) M]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjM : j < M := Finset.mem_range.1 hj
      congr 1
      have h1 : ((M - 1 - j : ℕ) : ℤ) = (M : ℤ) - 1 - j := by
        push_cast [Nat.cast_sub (by omega : j ≤ M - 1), Nat.cast_sub (by omega : 1 ≤ M)]
        ring
      rw [h1]
      ring
    rw [hsum]
    exact SineSum.sum_term_le hM3 hδ0 hδ1 _

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

