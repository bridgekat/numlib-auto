import Numlib.Approximation.BestApprox
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

## Main results

* `Approximation.expansionCLM_eq_sum` — the defining formula `∑ᵢ (u, pᵢ) pᵢ`.
* `Approximation.norm_expansionCLM` — `‖P‖ = ⨆ₓ ∫ |K (x, t)| dμ(t)`.
* `Approximation.IsOrthonormal.isIdempotentElem_expansionCLM`,
  `Approximation.IsOrthonormal.range_expansionCLM` — for an orthonormal system, `P` is a projection
  with range the span of the system.

## References

The material is [han2009theoretical], §3.7.1, (3.7.13)–(3.7.17), stated there for the orthonormal
polynomials of a weight on `[-1, 1]`; nothing below uses more than continuity of the system.
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

end Approximation
