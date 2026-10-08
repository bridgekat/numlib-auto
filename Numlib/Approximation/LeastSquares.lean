import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Approximation.Trigonometric
import Numlib.IntegralEquations.Basic

/-!
# Truncated expansions in an orthonormal system, as integral operators

Let `p₀, …, p_N` be continuous real functions on a compact space `X` carrying a finite Borel
measure `μ`. The **truncated expansion** `u ↦ ∑ᵢ (u, pᵢ)_{L²(μ)} pᵢ` is then an operator on the
Banach space `C(X, ℝ)`, and it is the integral operator whose kernel is the *reproducing kernel*

`K (x, t) = ∑ᵢ pᵢ(x) pᵢ(t)`

of the system. Consequently its operator norm is the largest row integral of `|K|`, by the norm
formula for a kernel operator. When the system is orthonormal in `L²(μ)` the operator is the
least-squares projection onto the span of `p`: it is idempotent, and its range is that span.

The point of the identification is the norm: the size of a least-squares projection *in the uniform
norm* is a statement about the kernel, and for the orthonormal polynomials of a weight the kernel is
computable from the Christoffel–Darboux identity.

## Main definitions

* `Approximation.reproducingKernel p` — the kernel `K (x, t) = ∑ᵢ pᵢ(x) pᵢ(t)`.
* `Approximation.IsOrthonormal μ p` — `∫ pᵢ pⱼ dμ = δᵢⱼ`.
* `Approximation.expansionCLM μ p` — the truncated expansion, as a bounded operator on `C(X, ℝ)`.
* `Approximation.chebyshevOrthonormal`, `Approximation.chebyshevProj` — the orthonormal Chebyshev
  system on `[-1, 1]` for the weight `(1 - x²)^{-1/2}` (`Approximation.chebyshevMeasureIcc`), and
  the truncated expansion in it.

## Main results

* `Approximation.expansionCLM_eq_sum` — the defining formula `∑ᵢ (u, pᵢ) pᵢ`.
* `Approximation.norm_expansionCLM` — `‖P‖ = ⨆ₓ ∫ |K (x, t)| dμ(t)`.
* `Approximation.IsOrthonormal.isIdempotentElem_expansionCLM`,
  `Approximation.IsOrthonormal.range_expansionCLM` — for an orthonormal system, `P` is a projection
  with range the span of the system.
* `Approximation.norm_chebyshevProj` — `‖chebyshevProj N‖` is exactly the Lebesgue constant
  `PeriodicCont.lebesgueConstant N` of the Fourier projection, through the angle form
  `Approximation.chebyshevKernel_cos` of the Chebyshev reproducing kernel.

## References

The material is [han2009theoretical], §3.7.1, (3.7.13)–(3.7.17), stated there for the orthonormal
polynomials of a weight on `[-1, 1]`; nothing below uses more than continuity of the system, except
the Chebyshev section, which is [han2009theoretical] Example 3.7.4.
-/

open MeasureTheory Set

noncomputable section

namespace Approximation

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- **The reproducing kernel** `K (x, t) = ∑ᵢ pᵢ(x) pᵢ(t)` of a finite family of continuous
functions ([han2009theoretical], (3.7.16)). -/
def reproducingKernel (p : ι → C(X, ℝ)) : C(X × X, ℝ) :=
  ⟨fun q => ∑ i, p i q.1 * p i q.2, continuous_finsetSum _ fun i _ =>
    ((p i).continuous.comp continuous_fst).mul ((p i).continuous.comp continuous_snd)⟩

/-- The defining formula of `Approximation.reproducingKernel`. -/
@[simp]
theorem reproducingKernel_apply (p : ι → C(X, ℝ)) (x t : X) :
    reproducingKernel p (x, t) = ∑ i, p i x * p i t :=
  rfl

variable [MeasurableSpace X]

/-- A finite family of continuous functions is **orthonormal in `L²(μ)`** when `∫ pᵢ pⱼ dμ = δᵢⱼ`.
This is the standing hypothesis of [han2009theoretical], §3.7.1, where the family is the orthonormal
polynomial family of a weight on `[-1, 1]`. -/
structure IsOrthonormal (μ : Measure X) (p : ι → C(X, ℝ)) : Prop where
  /-- Each member has unit `L²(μ)` norm. -/
  integral_mul_self : ∀ i, (∫ t, p i t * p i t ∂μ) = 1
  /-- Distinct members are `L²(μ)`-orthogonal. -/
  integral_mul_of_ne : ∀ ⦃i j⦄, i ≠ j → (∫ t, p i t * p j t ∂μ) = 0

variable [CompactSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- **The truncated expansion** `u ↦ ∑ᵢ (u, pᵢ)_{L²(μ)} pᵢ` in a finite family of continuous
functions, as a bounded operator on `C(X, ℝ)`: the integral operator of the reproducing kernel
([han2009theoretical], (3.7.15)).

For an orthonormal family this is the least-squares projection onto the span of the family — the
orthogonal projection of `L²(μ)`, restricted to the continuous functions
(`Approximation.IsOrthonormal.isIdempotentElem_expansionCLM`,
`Approximation.IsOrthonormal.range_expansionCLM`). -/
def expansionCLM (p : ι → C(X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  IntegralOperator.kernelCLM μ (reproducingKernel p)

/-- The truncated expansion, pointwise ([han2009theoretical], (3.7.13)). -/
theorem expansionCLM_apply (p : ι → C(X, ℝ)) (u : C(X, ℝ)) (x : X) :
    expansionCLM μ p u x = ∑ i, (∫ t, u t * p i t ∂μ) * p i x := by
  have hint : ∀ i : ι, Integrable (fun t : X => p i x * (u t * p i t)) μ := fun i =>
    IntegralOperator.integrable_of_continuousMap μ
      ⟨_, continuous_const.mul (u.continuous.mul (p i).continuous)⟩
  have hrw : ∀ t : X, reproducingKernel p (x, t) * u t = ∑ i, p i x * (u t * p i t) := fun t => by
    rw [reproducingKernel_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [expansionCLM, IntegralOperator.kernelCLM_apply,
    integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring

/-- The truncated expansion as a linear combination of the family ([han2009theoretical],
(3.7.13)). -/
theorem expansionCLM_eq_sum (p : ι → C(X, ℝ)) (u : C(X, ℝ)) :
    expansionCLM μ p u = ∑ i, (∫ t, u t * p i t ∂μ) • p i := by
  ext x
  rw [expansionCLM_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The truncated expansion lands in the span of the family. -/
theorem expansionCLM_mem_span (p : ι → C(X, ℝ)) (u : C(X, ℝ)) :
    expansionCLM μ p u ∈ Submodule.span ℝ (Set.range p) := by
  rw [expansionCLM_eq_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- **The uniform norm of a truncated expansion is the largest row integral of its reproducing
kernel** ([han2009theoretical], (3.7.17)), by the norm formula for a kernel operator on a compact
space. -/
theorem norm_expansionCLM [Nonempty X] (p : ι → C(X, ℝ)) :
    ‖expansionCLM μ p‖ = ⨆ x, ∫ t, |∑ i, p i x * p i t| ∂μ := by
  rw [expansionCLM, IntegralOperator.norm_kernelCLM]
  simp only [reproducingKernel_apply]

variable {μ}

namespace IsOrthonormal

/-- An orthonormal system is fixed by its own truncated expansion. -/
theorem expansionCLM_apply_eq_self {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) (j : ι) :
    expansionCLM μ p (p j) = p j := by
  ext x
  rw [expansionCLM_apply,
    Finset.sum_eq_single j (fun i _ hi => by rw [h.integral_mul_of_ne (Ne.symm hi), zero_mul])
      (fun hj => absurd (Finset.mem_univ j) hj),
    h.integral_mul_self j, one_mul]

/-- The truncated expansion in an orthonormal system fixes the span of that system. -/
theorem expansionCLM_eq_self {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) {u : C(X, ℝ)}
    (hu : u ∈ Submodule.span ℝ (Set.range p)) : expansionCLM μ p u = u := by
  induction hu using Submodule.span_induction with
  | mem v hv => obtain ⟨j, rfl⟩ := hv; exact h.expansionCLM_apply_eq_self j
  | zero => exact map_zero _
  | add v w _ _ hv hw => rw [map_add, hv, hw]
  | smul c v _ hv => rw [map_smul, hv]

/-- **The truncated expansion in an orthonormal system is a projection** ([han2009theoretical],
(3.7.13)). -/
theorem isIdempotentElem_expansionCLM {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) :
    IsIdempotentElem (expansionCLM μ p) := by
  ext u x
  exact congrFun (congrArg _ (h.expansionCLM_eq_self (expansionCLM_mem_span μ p u))) x

/-- **The range of the truncated expansion in an orthonormal system is the span of the system.** -/
theorem range_expansionCLM {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) :
    LinearMap.range ((expansionCLM μ p : C(X, ℝ) →L[ℝ] C(X, ℝ)) : C(X, ℝ) →ₗ[ℝ] C(X, ℝ))
      = Submodule.span ℝ (Set.range p) := by
  refine le_antisymm ?_ fun u hu => ⟨u, h.expansionCLM_eq_self hu⟩
  rintro _ ⟨u, rfl⟩
  exact expansionCLM_mem_span μ p u

/-- **The Lebesgue lemma for a least-squares projection** ([han2009theoretical], (3.7.14)): the
uniform error of the truncated expansion in an orthonormal system is at most `1 + ‖P‖` times the
distance to the span of the system. -/
theorem norm_sub_expansionCLM_le {p : ι → C(X, ℝ)} (h : IsOrthonormal μ p) (u : C(X, ℝ)) :
    ‖u - expansionCLM μ p u‖
      ≤ (1 + ‖expansionCLM μ p‖) *
          Metric.infDist u (Submodule.span ℝ (Set.range p) : Set C(X, ℝ)) := by
  have hle := norm_sub_apply_le_of_isIdempotentElem (expansionCLM μ p)
    h.isIdempotentElem_expansionCLM u
  rwa [h.range_expansionCLM] at hle

end IsOrthonormal

/-! ### The Chebyshev least-squares projection

The orthonormal Chebyshev system on `[-1, 1]` for the weight `(1 - x²)^{-1/2}`, its reproducing
kernel in the angle variables, and the norm of the truncated expansion in it: exactly the Lebesgue
constant `PeriodicCont.lebesgueConstant N` of the Fourier projection ([han2009theoretical]
Example 3.7.4). -/

section Chebyshev

open Real PeriodicCont

open Polynomial.Chebyshev (T measureT)

/-- Mathlib's Chebyshev weight `√(1 - x²)⁻¹ dx` on `(-1, 1]` is a finite measure, of total mass `π`.
An upstreaming candidate: only integrability of the constant function is used. -/
instance : IsFiniteMeasure measureT := by
  rcases integrable_const_iff.1
      (Polynomial.Chebyshev.integrable_measureT (f := fun _ => (1 : ℝ)) continuousOn_const) with
    h | h
  · exact absurd h one_ne_zero
  · exact h

/-- **The Chebyshev weight as a measure on the compact space `[-1, 1]`**: Lebesgue measure scaled by
`(1 - x²)^{-1/2}`, which is the weight of [han2009theoretical], (3.5.8) and Example 3.7.4. -/
noncomputable def chebyshevMeasureIcc : Measure (Set.Icc (-1 : ℝ) 1) :=
  Measure.comap Subtype.val measureT

instance : IsFiniteMeasure chebyshevMeasureIcc := by
  refine ⟨?_⟩
  rw [chebyshevMeasureIcc, comap_subtype_coe_apply measurableSet_Icc]
  exact measure_lt_top _ _

/-- An integral over the space `[-1, 1]` against the Chebyshev weight is the corresponding integral
over the line: the weight gives the two endpoints no mass. -/
theorem integral_chebyshevMeasureIcc (f : ℝ → ℝ) :
    ∫ t : Set.Icc (-1 : ℝ) 1, f t ∂chebyshevMeasureIcc = ∫ x, f x ∂measureT := by
  have hrestrict : measureT.restrict (Set.Icc (-1 : ℝ) 1) = measureT := by
    rw [measureT, Measure.restrict_restrict measurableSet_Icc]
    congr 1
    exact Set.inter_eq_right.2 (Set.Ioc_subset_Icc_self (a := (-1 : ℝ)) (b := 1))
  rw [chebyshevMeasureIcc, integral_subtype_comap measurableSet_Icc, hrestrict]

/-- The normalizing coefficients of the orthonormal Chebyshev system: `√(1/π)` in degree `0` and
`√(2/π)` in every higher degree, from the values `π` and `π/2` of [han2009theoretical] (3.5.9). -/
noncomputable def chebyshevCoeff (n : ℕ) : ℝ := if n = 0 then √(1 / π) else √(2 / π)

theorem chebyshevCoeff_mul_self_zero : chebyshevCoeff 0 * chebyshevCoeff 0 = 1 / π := by
  rw [chebyshevCoeff, ite_eq_left rfl, Real.mul_self_sqrt (by positivity)]

theorem chebyshevCoeff_mul_self_of_ne {n : ℕ} (hn : n ≠ 0) :
    chebyshevCoeff n * chebyshevCoeff n = 2 / π := by
  rw [chebyshevCoeff, ite_eq_right hn, Real.mul_self_sqrt (by positivity)]

/-- **The orthonormal Chebyshev system** on `[-1, 1]` for the weight `(1 - x²)^{-1/2}`:
`p₀ = 1/√π` and `pₙ = √(2/π) Tₙ` for `n ≥ 1` ([han2009theoretical], (3.5.8) and Example 3.7.4). -/
noncomputable def chebyshevOrthonormal (n : ℕ) : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x => chebyshevCoeff n * (T ℝ n).eval (x : ℝ),
    continuous_const.mul ((T ℝ (n : ℤ)).continuous_aeval.comp continuous_subtype_val)⟩

@[simp]
theorem chebyshevOrthonormal_apply (n : ℕ) (x : Set.Icc (-1 : ℝ) 1) :
    chebyshevOrthonormal n x = chebyshevCoeff n * (T ℝ n).eval (x : ℝ) :=
  rfl

/-- The Chebyshev system is orthonormal for the Chebyshev weight: this is [han2009theoretical]
(3.5.9), normalized. -/
theorem integral_chebyshevOrthonormal_mul (m n : ℕ) :
    (∫ t : Set.Icc (-1 : ℝ) 1,
        chebyshevOrthonormal m t * chebyshevOrthonormal n t ∂chebyshevMeasureIcc)
      = if m = n then 1 else 0 := by
  have hπ : (0 : ℝ) < π := pi_pos
  simp only [chebyshevOrthonormal_apply]
  rw [integral_chebyshevMeasureIcc fun y =>
    (chebyshevCoeff m * (T ℝ m).eval y) * (chebyshevCoeff n * (T ℝ n).eval y)]
  have hmul : ∀ y : ℝ,
      (chebyshevCoeff m * (T ℝ m).eval y) * (chebyshevCoeff n * (T ℝ n).eval y)
        = (chebyshevCoeff m * chebyshevCoeff n) *
            ((T ℝ m).eval y * (T ℝ n).eval y) := fun y => by ring
  simp_rw [hmul]
  rw [integral_const_mul]
  rcases eq_or_ne m n with rfl | hmn
  · rcases eq_or_ne m 0 with rfl | hm
    · rw [ite_eq_left rfl, chebyshevCoeff_mul_self_zero]
      rw [show ((0 : ℕ) : ℤ) = 0 from Nat.cast_zero,
        Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      field_simp
    · rw [ite_eq_left rfl, chebyshevCoeff_mul_self_of_ne hm,
        Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hm]
      field_simp
  · rw [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn,
      mul_zero, ite_eq_right hmn]

/-- The orthonormal Chebyshev system, as an orthonormal family in the sense of the backbone. -/
theorem isOrthonormal_chebyshevOrthonormal (N : ℕ) :
    IsOrthonormal chebyshevMeasureIcc fun i : Fin (N + 1) => chebyshevOrthonormal i where
  integral_mul_self i := by rw [integral_chebyshevOrthonormal_mul, ite_eq_left rfl]
  integral_mul_of_ne i j hij := by
    rw [integral_chebyshevOrthonormal_mul, ite_eq_right (fun h => hij (Fin.val_injective h))]

/-- The reproducing kernel of the orthonormal Chebyshev system, as a function of two real
arguments: `K (x, t) = (1/π) T₀(x) T₀(t) + (2/π) ∑_{n=1}^{N} Tₙ(x) Tₙ(t)`
([han2009theoretical], Example 3.7.4). -/
noncomputable def chebyshevKernel (N : ℕ) (x t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (chebyshevCoeff n * chebyshevCoeff n) * ((T ℝ n).eval x * (T ℝ n).eval t)

theorem sum_chebyshevOrthonormal_mul (N : ℕ) (x t : Set.Icc (-1 : ℝ) 1) :
    ∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t
      = chebyshevKernel N x t := by
  rw [chebyshevKernel, ← Fin.sum_univ_eq_sum_range
    (fun n => (chebyshevCoeff n * chebyshevCoeff n) *
      ((T ℝ n).eval (x : ℝ) * (T ℝ n).eval (t : ℝ)))]
  exact Finset.sum_congr rfl fun i _ => by simp only [chebyshevOrthonormal_apply]; ring

/-- **The Chebyshev reproducing kernel in the angle variables** ([han2009theoretical], Example
3.7.4, in the form Rivlin gives): with `x = cos θ` and `t = cos φ`,

`K (x, t) = (1/π) [Dₙ(θ − φ) + Dₙ(θ + φ)]`,

`Dₙ` being the Dirichlet kernel `dirichletKernel`. [han2009theoretical] prints the same identity
with `Dₙ` written out as `sin ((N + 1/2) ·) / (2 sin (·/2))`. -/
theorem chebyshevKernel_cos (N : ℕ) (θ φ : ℝ) :
    chebyshevKernel N (cos θ) (cos φ)
      = (dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)) / π := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have hshift : ∀ (M : ℕ) (g : ℕ → ℝ),
      ∑ j ∈ Finset.Icc 1 M, g j = ∑ i ∈ Finset.range M, g (i + 1) := by
    intro M g
    induction M with
    | zero => simp
    | succ K ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have hterm : ∀ i : ℕ,
      (chebyshevCoeff (i + 1) * chebyshevCoeff (i + 1)) *
          ((T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos θ) * (T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos φ))
        = (Real.cos ((i + 1 : ℕ) * (θ - φ)) + Real.cos ((i + 1 : ℕ) * (θ + φ))) / π := by
    intro i
    have hT : ∀ s : ℝ, (T ℝ ((i + 1 : ℕ) : ℤ)).eval (cos s) = Real.cos ((i + 1 : ℕ) * s) := by
      intro s
      rw [Polynomial.Chebyshev.T_real_cos]
      push_cast
      ring_nf
    rw [chebyshevCoeff_mul_self_of_ne (Nat.succ_ne_zero i), hT, hT,
      show ((i + 1 : ℕ) : ℝ) * (θ - φ) = (i + 1 : ℕ) * θ - (i + 1 : ℕ) * φ by ring,
      show ((i + 1 : ℕ) : ℝ) * (θ + φ) = (i + 1 : ℕ) * θ + (i + 1 : ℕ) * φ by ring,
      Real.cos_sub, Real.cos_add]
    field_simp
    ring
  have hT0 : (T ℝ ((0 : ℕ) : ℤ)).eval (cos θ) * (T ℝ ((0 : ℕ) : ℤ)).eval (cos φ) = 1 := by
    rw [show ((0 : ℕ) : ℤ) = 0 from Nat.cast_zero, Polynomial.Chebyshev.T_zero]
    simp
  rw [chebyshevKernel, Finset.sum_range_succ' _ N]
  simp only [hterm]
  rw [hT0, chebyshevCoeff_mul_self_zero, mul_one, dirichletKernel_apply, dirichletKernel_apply,
    hshift N, hshift N, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- **The Chebyshev least-squares projection** `P_N` of [han2009theoretical], Example 3.7.4: the
truncated expansion of a continuous function on `[-1, 1]` in the orthonormal Chebyshev system, as a
bounded operator on `C[-1, 1]`. -/
noncomputable def chebyshevProj (N : ℕ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  expansionCLM chebyshevMeasureIcc fun i : Fin (N + 1) => chebyshevOrthonormal i

/-- The row integral of the Chebyshev kernel, in the angle variable. -/
theorem integral_abs_chebyshevKernel (N : ℕ) (θ : ℝ) :
    (∫ t : Set.Icc (-1 : ℝ) 1, |chebyshevKernel N (cos θ) t| ∂chebyshevMeasureIcc)
      = 1 / π * ∫ φ in (0 : ℝ)..π,
          |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)| := by
  have hπ : (0 : ℝ) < π := pi_pos
  rw [integral_chebyshevMeasureIcc fun y => |chebyshevKernel N (cos θ) y|,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [chebyshevKernel_cos, abs_div, abs_of_pos hπ]
  ring

/-- The Lebesgue function of the Chebyshev projection never exceeds the Lebesgue constant of the
Fourier projection: `|Dₙ(θ − φ) + Dₙ(θ + φ)|` integrates over half a period to at most what `|Dₙ|`
integrates to over a full one. -/
theorem integral_abs_chebyshevKernel_le (N : ℕ) (θ : ℝ) :
    (1 / π * ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ lebesgueConstant N := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hcont : Continuous fun u : ℝ => |dirichletKernel N u| :=
    (continuous_dirichletKernel N).abs
  have hper : Function.Periodic (fun u : ℝ => |dirichletKernel N u|) (2 * π) := fun u => by
    simp only []
    rw [dirichletKernel_periodic N u]
  have hcont1 : Continuous
      fun φ : ℝ => |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)| :=
    (((continuous_dirichletKernel N).comp (continuous_const.sub continuous_id)).add
      ((continuous_dirichletKernel N).comp (continuous_const.add continuous_id))).abs
  have hcontm : Continuous fun φ : ℝ => |dirichletKernel N (θ - φ)| :=
    ((continuous_dirichletKernel N).comp (continuous_const.sub continuous_id)).abs
  have hcontp : Continuous fun φ : ℝ => |dirichletKernel N (θ + φ)| :=
    ((continuous_dirichletKernel N).comp (continuous_const.add continuous_id)).abs
  have hint1 : IntervalIntegrable
      (fun φ : ℝ => |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|) volume 0 π :=
    hcont1.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun φ : ℝ => |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)|) volume 0 π :=
    (hcontm.add hcontp).intervalIntegrable _ _
  have hmono : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)| :=
    intervalIntegral.integral_mono_on pi_pos.le hint1 hint2 fun φ _ => abs_add_le _ _
  have hsplit : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)| + |dirichletKernel N (θ + φ)|)
      = (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)|)
          + ∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ + φ)| :=
    intervalIntegral.integral_add (hcontm.intervalIntegrable _ _)
      (hcontp.intervalIntegrable _ _)
  have hsub : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ)|)
      = ∫ u in (θ - π)..θ, |dirichletKernel N u| := by
    rw [intervalIntegral.integral_comp_sub_left (fun u => |dirichletKernel N u|) θ, sub_zero]
  have hadd : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ + φ)|)
      = ∫ u in θ..(θ + π), |dirichletKernel N u| := by
    rw [intervalIntegral.integral_comp_add_left (fun u => |dirichletKernel N u|) θ, add_zero]
  have hjoin : (∫ u in (θ - π)..θ, |dirichletKernel N u|)
      + (∫ u in θ..(θ + π), |dirichletKernel N u|)
      = ∫ u in (θ - π)..(θ + π), |dirichletKernel N u| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hshift : (∫ u in (θ - π)..(θ + π), |dirichletKernel N u|)
      = ∫ u in (-π)..π, |dirichletKernel N u| := by
    have h := hper.intervalIntegral_add_eq (θ - π) (-π)
    rw [show θ - π + 2 * π = θ + π by ring, show -π + 2 * π = π by ring] at h
    exact h
  rw [lebesgueConstant]
  have hle : (∫ φ in (0 : ℝ)..π, |dirichletKernel N (θ - φ) + dirichletKernel N (θ + φ)|)
      ≤ ∫ u in (-π)..π, |dirichletKernel N u| := by
    rw [← hshift, ← hjoin, ← hsub, ← hadd, ← hsplit]
    exact hmono
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- At `x = 1`, that is `θ = 0`, the Lebesgue function of the Chebyshev projection attains the
Lebesgue constant. -/
theorem integral_abs_chebyshevKernel_zero (N : ℕ) :
    (1 / π * ∫ φ in (0 : ℝ)..π, |dirichletKernel N (0 - φ) + dirichletKernel N (0 + φ)|)
      = lebesgueConstant N := by
  have hπ : (0 : ℝ) < π := pi_pos
  have hval : ∀ φ : ℝ, |dirichletKernel N (0 - φ) + dirichletKernel N (0 + φ)|
      = 2 * |dirichletKernel N φ| := by
    intro φ
    rw [zero_sub, zero_add, dirichletKernel_neg, ← two_mul, abs_mul]
    norm_num
  rw [intervalIntegral.integral_congr fun φ _ => hval φ, intervalIntegral.integral_const_mul,
    lebesgueConstant_eq]
  ring

/-- **The norm of the Chebyshev least-squares projection** ([han2009theoretical] Example 3.7.4):
the operator norm of `chebyshevProj N` on `C[-1, 1]` is exactly the `N`-th Lebesgue constant of the
Fourier projection.

The change of variables `x = cos θ`, `t = cos φ` turns the kernel into
`(1/π)[D_N(θ − φ) + D_N(θ + φ)]` (`chebyshevKernel_cos`), the row integral into
`(1/π) ∫₀^π |D_N(θ − φ) + D_N(θ + φ)| dφ`, and that is largest at `θ = 0`, where it is
`(2/π) ∫₀^π |D_N| = L_N`. -/
theorem norm_chebyshevProj (N : ℕ) : ‖chebyshevProj N‖ = lebesgueConstant N := by
  have : Nonempty (Set.Icc (-1 : ℝ) 1) := ⟨⟨1, by norm_num⟩⟩
  have hrow : ∀ x : Set.Icc (-1 : ℝ) 1,
      (∫ t, |∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t|
        ∂chebyshevMeasureIcc)
        = 1 / π * ∫ φ in (0 : ℝ)..π,
            |dirichletKernel N (arccos (x : ℝ) - φ) + dirichletKernel N (arccos (x : ℝ) + φ)| := by
    intro x
    have hx : cos (arccos (x : ℝ)) = (x : ℝ) := cos_arccos x.2.1 x.2.2
    simp only [sum_chebyshevOrthonormal_mul]
    rw [← integral_abs_chebyshevKernel N (arccos (x : ℝ))]
    simp only [hx]
  have hle : ∀ x : Set.Icc (-1 : ℝ) 1,
      (∫ t, |∑ i : Fin (N + 1), chebyshevOrthonormal i x * chebyshevOrthonormal i t|
        ∂chebyshevMeasureIcc) ≤ lebesgueConstant N := fun x => by
    rw [hrow x]
    exact integral_abs_chebyshevKernel_le N _
  have hone : (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) ∈ Set.univ := Set.mem_univ _
  have heq : (∫ t, |∑ i : Fin (N + 1),
      chebyshevOrthonormal i (⟨1, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) *
        chebyshevOrthonormal i t| ∂chebyshevMeasureIcc) = lebesgueConstant N := by
    rw [hrow ⟨1, by norm_num⟩]
    simp only [arccos_one]
    exact integral_abs_chebyshevKernel_zero N
  rw [chebyshevProj, norm_expansionCLM]
  refine le_antisymm (ciSup_le hle) ?_
  rw [← heq]
  exact le_ciSup ⟨lebesgueConstant N, by rintro _ ⟨x, rfl⟩; exact hle x⟩ _

end Chebyshev

end Approximation
