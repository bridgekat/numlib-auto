import Numlib.Approximation.MvPolynomial

/-!
# Hyperinterpolation

Hyperinterpolation is the `L²(μ)` orthogonal projection onto the polynomials of total degree at most
`n`, with the integrals defining the Fourier coefficients replaced by a quadrature rule. It is due
to Sloan, and it needs nothing about the rule beyond exactness on the polynomials of total degree at
most `2n`: a product of two elements of `Π_n^d` has degree at most `2n`, so the discrete inner
product then *is* the continuous one on `Π_n^d`, the discrete coefficients are the true Fourier
coefficients, and the operator reproduces every polynomial of degree at most `n`.

Nothing here is special to a particular domain, so the same statements serve the ball, the sphere
and the simplex. What a concrete instance still has to supply is a rule exact to degree `2n` with
the intended nodes and weights.

## Main definitions

* `Approximation.discreteInner w x p q`: the discrete inner product `Σ_k w_k p(x_k) q(x_k)` induced
  by weights `w` at nodes `x`.
* `Approximation.hyperinterp w x b f`: `Σ_i (f, b_i)_n b_i`, the orthogonal expansion of `f` along
  the family `b` with the discrete inner product in place of the continuous one.
* `Approximation.IsExactOn μ w x m`: the rule integrates every polynomial of total degree at most
  `m` exactly against `μ`.

## Main results

* `Approximation.discreteInner_eq_inner_toL2`: a rule exact to degree `2n` has `(p, q)_n = (p, q)`
  for `p` and `q` of degree at most `n`.
* `Approximation.hyperinterp_eq_self`: for an `L²(μ)`-orthonormal family of polynomials of degree at
  most `n` and a rule exact to degree `2n`, hyperinterpolation reproduces every polynomial in the
  span of the family. With `Approximation.hyperinterp_mem_span` this makes it a projection onto that
  span, and `Approximation.hyperinterp_hyperinterp` is idempotence in the form the definition takes.

## References

The construction and the exactness hypothesis are those of [han2009theoretical], §14.3, which
follows Sloan.
-/

open Finset MeasureTheory

namespace Approximation

variable {ι K : Type*} [Fintype K]

/-- The **discrete inner product** `(p, q)_n = Σ_k w_k p(x_k) q(x_k)` that a quadrature rule with
weights `w` at nodes `x` induces on polynomials. -/
noncomputable def discreteInner (w : K → ℝ) (x : K → (ι → ℝ)) (p q : MvPolynomial ι ℝ) : ℝ :=
  ∑ k, w k * MvPolynomial.eval (x k) p * MvPolynomial.eval (x k) q

/-- The discrete inner product is symmetric. -/
theorem discreteInner_comm (w : K → ℝ) (x : K → (ι → ℝ)) (p q : MvPolynomial ι ℝ) :
    discreteInner w x p q = discreteInner w x q p :=
  Finset.sum_congr rfl fun _ _ => by ring

/-- **Hyperinterpolation**: the expansion `L_n f = Σ_i (f, b_i)_n b_i` of `f` along a family `b` of
polynomials, with the discrete inner product of a quadrature rule in place of the continuous one.
When `b` is an `L²(μ)`-orthonormal basis of `Π_n^d` and the rule is exact to degree `2n`, this is
the orthogonal projection onto `Π_n^d` with its integrals discretized. -/
noncomputable def hyperinterp {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f : (ι → ℝ) → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, (∑ k, w k * f (x k) * MvPolynomial.eval (x k) (b i)) • b i

theorem hyperinterp_eq_sum_discreteInner {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ))
    (b : Fin N → MvPolynomial ι ℝ) (p : MvPolynomial ι ℝ) :
    hyperinterp w x b (fun y => MvPolynomial.eval y p) =
      ∑ i, discreteInner w x p (b i) • b i := rfl

/-- Hyperinterpolation lands in the span of the family, hence in `Π_n^d` when the family is a basis
of it. -/
theorem hyperinterp_mem_span {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f : (ι → ℝ) → ℝ) : hyperinterp w x b f ∈ Submodule.span ℝ (Set.range b) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Hyperinterpolation of a family of polynomials of degree at most `n` has degree at most `n`. -/
theorem totalDegree_hyperinterp_le {N n : ℕ} (w : K → ℝ) (x : K → (ι → ℝ))
    {b : Fin N → MvPolynomial ι ℝ} (hbdeg : ∀ i, (b i).totalDegree ≤ n) (f : (ι → ℝ) → ℝ) :
    (hyperinterp w x b f).totalDegree ≤ n :=
  MvPolynomial.totalDegree_finsetSum_le fun i _ =>
    (MvPolynomial.totalDegree_smul_le _ _).trans (hbdeg i)

/-- Hyperinterpolation is additive in the function it interpolates. -/
theorem hyperinterp_add {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f g : (ι → ℝ) → ℝ) :
    hyperinterp w x b (f + g) = hyperinterp w x b f + hyperinterp w x b g := by
  rw [hyperinterp, hyperinterp, hyperinterp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul, ← Finset.sum_add_distrib]
  exact congrArg (· • b i) (Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply]; ring)

/-- Hyperinterpolation is homogeneous in the function it interpolates. -/
theorem hyperinterp_smul {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (c : ℝ) (f : (ι → ℝ) → ℝ) : hyperinterp w x b (c • f) = c • hyperinterp w x b f := by
  rw [hyperinterp, hyperinterp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, Finset.mul_sum]
  exact congrArg (· • b i)
    (Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

section Measure

variable [MeasurableSpace (ι → ℝ)] {μ : Measure (ι → ℝ)}

/-- A quadrature rule with weights `w` and nodes `x` is **exact to degree `m`** for `μ` when it
integrates every polynomial of total degree at most `m` without error. -/
def IsExactOn (μ : Measure (ι → ℝ)) (w : K → ℝ) (x : K → (ι → ℝ)) (m : ℕ) : Prop :=
  ∀ p : MvPolynomial ι ℝ, p.totalDegree ≤ m →
    ∑ k, w k * MvPolynomial.eval (x k) p = ∫ y, MvPolynomial.eval y p ∂μ

theorem IsExactOn.mono {w : K → ℝ} {x : K → (ι → ℝ)} {m m' : ℕ} (h : IsExactOn μ w x m)
    (hm : m' ≤ m) : IsExactOn μ w x m' := fun p hp => h p (hp.trans hm)

/-- A rule exact to degree `2n` has `(p, q)_n = (p, q)` for all `p` and `q` of total degree at most
`n`, because `p q` then has total degree at most `2n`. This is the identity that makes
hyperinterpolation a projection. -/
theorem discreteInner_eq_inner_toL2 (hw : IsMvWeight μ) {w : K → ℝ} {x : K → (ι → ℝ)} {n : ℕ}
    (hex : IsExactOn μ w x (2 * n)) {p q : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : discreteInner w x p q = inner ℝ (hw.toL2 p) (hw.toL2 q) := by
  have h := hex (p * q) ((MvPolynomial.totalDegree_mul p q).trans (by omega))
  simp only [map_mul] at h
  rw [hw.inner_toL2, ← h, discreteInner]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- **Hyperinterpolation reproduces polynomials.** If `b` is an `L²(μ)`-orthonormal family of
polynomials of total degree at most `n` and the rule is exact to degree `2n`, then `L_n p = p` for
every `p` in the span of `b`. The proof is that on `Π_n^d` the discrete inner product is the
continuous one, so the coefficients the rule computes are the true Fourier coefficients. -/
theorem hyperinterp_eq_self (hw : IsMvWeight μ) {n N : ℕ} {w : K → ℝ} {x : K → (ι → ℝ)}
    (hex : IsExactOn μ w x (2 * n)) {b : Fin N → MvPolynomial ι ℝ}
    (hbdeg : ∀ i, (b i).totalDegree ≤ n) (hb : Orthonormal ℝ fun i => hw.toL2 (b i))
    {p : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ n) (hspan : p ∈ Submodule.span ℝ (Set.range b)) :
    hyperinterp w x b (fun y => MvPolynomial.eval y p) = p := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hspan
  rw [hyperinterp_eq_sum_discreteInner]
  refine Finset.sum_congr rfl fun i _ => congrArg (· • b i) ?_
  rw [discreteInner_eq_inner_toL2 hw hex hp (hbdeg i), map_sum]
  simpa only [map_smul, RCLike.star_def, starRingEnd_apply, star_trivial] using
    hb.inner_left_fintype c i

/-- Hyperinterpolation is idempotent: applying it to the values of its own output returns that
output unchanged. With `Approximation.hyperinterp_mem_span` this says that `L_n` is a projection
onto the span of `b`. -/
theorem hyperinterp_hyperinterp (hw : IsMvWeight μ) {n N : ℕ} {w : K → ℝ} {x : K → (ι → ℝ)}
    (hex : IsExactOn μ w x (2 * n)) {b : Fin N → MvPolynomial ι ℝ}
    (hbdeg : ∀ i, (b i).totalDegree ≤ n) (hb : Orthonormal ℝ fun i => hw.toL2 (b i))
    (f : (ι → ℝ) → ℝ) :
    hyperinterp w x b (fun y => MvPolynomial.eval y (hyperinterp w x b f)) =
      hyperinterp w x b f :=
  hyperinterp_eq_self hw hex hbdeg hb (totalDegree_hyperinterp_le w x hbdeg f)
    (hyperinterp_mem_span w x b f)

end Measure

end Approximation
