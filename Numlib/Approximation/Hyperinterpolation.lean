/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.MvPolynomial

/-!
# Hyperinterpolation

Let $\mu$ be a measure on $\mathbb{R}^d$ and let $\Pi_n^d$ be the space of real polynomials in $d$
variables of total degree at most $n$. **Hyperinterpolation** is the $L^2(\mu)$-orthogonal
projection onto $\Pi_n^d$, with the integrals that define the Fourier coefficients replaced by a
quadrature rule with weights $w_k$ and nodes $x_k$: $$L_n f = \sum_i (f, b_i)_n\, b_i, \qquad (f,
g)_n = \sum_k w_k f(x_k) g(x_k),$$ for an orthonormal basis $b_i$ of $\Pi_n^d$. The construction is
due to Sloan, and the presentation follows [han2009theoretical], §14.3.

The only property of the rule that is needed is exactness on the polynomials of total degree at most
$2n$. The product of two elements of $\Pi_n^d$ has degree at most $2n$, so the discrete inner
product is then the continuous one on $\Pi_n^d$, the discrete coefficients are the true Fourier
coefficients, and $L_n$ reproduces every polynomial of degree at most $n$. Nothing here is special
to a domain, so the same statements serve the ball, the sphere and the simplex. A concrete instance
must still supply a rule that is exact to degree $2n$ with the intended nodes and weights.

## Main definitions

* `Approximation.discreteInner`: the discrete inner product
  $(p, q)_n = \sum_k w_k\, p(x_k)\, q(x_k)$ of a rule.
* `Approximation.hyperinterp`: the hyperinterpolant $\sum_i (f, b_i)_n\, b_i$ of $f$ along a family
  $b$ of polynomials.
* `Approximation.IsExactOn`: the rule integrates every polynomial of total degree at most $m$
  exactly against $\mu$.

## Main results

* `Approximation.isExactOn_iff_forall_monomial`: exactness on polynomials is exactness on monomials.
* `Approximation.discreteInner_eq_inner_toL2`: a rule exact to degree $2n$ has
  $(p, q)_n = (p, q)_{L^2(\mu)}$ for $p$ and $q$ of total degree at most $n$.
* `Approximation.hyperinterp_eq_self`: for an $L^2(\mu)$-orthonormal family of polynomials of total
  degree at most $n$ and a rule exact to degree $2n$, hyperinterpolation reproduces every polynomial
  in the span of the family.
* `Approximation.hyperinterp_mem_span` and `Approximation.hyperinterp_hyperinterp`:
  hyperinterpolation maps into the span of the family and is idempotent, so it is a projection onto
  that span.

## Implementation notes

* The variables are indexed by a type `ι`, so a point is `ι → ℝ` and a polynomial is
  `MvPolynomial ι ℝ`. The nodes and the weights are indexed by a finite type `K`.
* The family $b$ is any finite family `Fin N → MvPolynomial ι ℝ`. The results that need
  orthonormality assume that the images of the $b_i$ in $L^2(\mu)$ under
  `Approximation.IsMvWeight.toL2` are orthonormal.
* The definition of `Approximation.hyperinterp` uses only the values of $f$ at the nodes, so $f$ can
  be any function. For a polynomial $f$ the coefficients are discrete inner products
  (`Approximation.hyperinterp_eq_sum_discreteInner`).
-/

open Finset MeasureTheory

namespace Approximation

variable {ι K : Type*} [Fintype K]

/-- The **discrete inner product** that a quadrature rule with weights $w_k$ at nodes
$x_k \in \mathbb{R}^d$ induces on polynomials: $$(p, q)_n = \sum_k w_k\, p(x_k)\, q(x_k).$$
-/
noncomputable def discreteInner (w : K → ℝ) (x : K → (ι → ℝ)) (p q : MvPolynomial ι ℝ) : ℝ :=
  ∑ k, w k * MvPolynomial.eval (x k) p * MvPolynomial.eval (x k) q

/-- The discrete inner product is symmetric: $(p, q)_n = (q, p)_n$. -/
theorem discreteInner_comm (w : K → ℝ) (x : K → (ι → ℝ)) (p q : MvPolynomial ι ℝ) :
    discreteInner w x p q = discreteInner w x q p :=
  Finset.sum_congr rfl fun _ _ => by ring

/-- **Hyperinterpolation.** Let a quadrature rule have weights $w_k$ at nodes
$x_k \in \mathbb{R}^d$, let $b_1, \dots, b_N$ be polynomials, and let
$f : \mathbb{R}^d \to \mathbb{R}$. The **hyperinterpolant** of $f$ is $$L_n f = \sum_{i=1}^N
\Big( \sum_k w_k\, f(x_k)\, b_i(x_k) \Big) b_i,$$ the expansion of $f$ along $b$ with the
discrete inner product of the rule in place of the continuous one. When $b$ is an
$L^2(\mu)$-orthonormal basis of $\Pi_n^d$ and the rule is exact to degree $2n$, it is the
orthogonal projection onto $\Pi_n^d$ with its integrals discretized. -/
noncomputable def hyperinterp {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f : (ι → ℝ) → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, (∑ k, w k * f (x k) * MvPolynomial.eval (x k) (b i)) • b i

/-- For a polynomial $p$, the hyperinterpolant of the function $y \mapsto p(y)$ is
$\sum_i (p, b_i)_n\, b_i$. -/
theorem hyperinterp_eq_sum_discreteInner {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ))
    (b : Fin N → MvPolynomial ι ℝ) (p : MvPolynomial ι ℝ) :
    hyperinterp w x b (fun y => MvPolynomial.eval y p) =
      ∑ i, discreteInner w x p (b i) • b i := rfl

/-- The hyperinterpolant of every function $f$ lies in the span of the family $b_1, \dots, b_N$; so
it lies in $\Pi_n^d$ when the family is a basis of $\Pi_n^d$. -/
theorem hyperinterp_mem_span {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f : (ι → ℝ) → ℝ) : hyperinterp w x b f ∈ Submodule.span ℝ (Set.range b) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- If every $b_i$ has total degree at most $n$, the hyperinterpolant of every function $f$ has
total degree at most $n$. -/
theorem totalDegree_hyperinterp_le {N n : ℕ} (w : K → ℝ) (x : K → (ι → ℝ))
    {b : Fin N → MvPolynomial ι ℝ} (hbdeg : ∀ i, (b i).totalDegree ≤ n) (f : (ι → ℝ) → ℝ) :
    (hyperinterp w x b f).totalDegree ≤ n :=
  MvPolynomial.totalDegree_finsetSum_le fun i _ =>
    (MvPolynomial.totalDegree_smul_le _ _).trans (hbdeg i)

/-- Hyperinterpolation is additive in the function: $L_n(f + g) = L_n f + L_n g$. -/
theorem hyperinterp_add {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (f g : (ι → ℝ) → ℝ) :
    hyperinterp w x b (f + g) = hyperinterp w x b f + hyperinterp w x b g := by
  rw [hyperinterp, hyperinterp, hyperinterp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul, ← Finset.sum_add_distrib]
  exact congrArg (· • b i) (Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply]; ring)

/-- Hyperinterpolation is homogeneous in the function: $L_n(cf) = c\, L_n f$ for $c \in \mathbb{R}$.
-/
theorem hyperinterp_smul {N : ℕ} (w : K → ℝ) (x : K → (ι → ℝ)) (b : Fin N → MvPolynomial ι ℝ)
    (c : ℝ) (f : (ι → ℝ) → ℝ) : hyperinterp w x b (c • f) = c • hyperinterp w x b f := by
  rw [hyperinterp, hyperinterp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, Finset.mul_sum]
  exact congrArg (· • b i)
    (Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

section Measure

variable [MeasurableSpace (ι → ℝ)] {μ : Measure (ι → ℝ)}

/-- A quadrature rule with weights $w_k$ at nodes $x_k \in \mathbb{R}^d$ is **exact to degree $m$**
for a measure $\mu$ on $\mathbb{R}^d$ if $$\sum_k w_k\, p(x_k) = \int p \, d\mu$$ for every
polynomial $p$ of total degree at most $m$. -/
def IsExactOn (μ : Measure (ι → ℝ)) (w : K → ℝ) (x : K → (ι → ℝ)) (m : ℕ) : Prop :=
  ∀ p : MvPolynomial ι ℝ, p.totalDegree ≤ m →
    ∑ k, w k * MvPolynomial.eval (x k) p = ∫ y, MvPolynomial.eval y p ∂μ

/-- A rule that is exact to degree $m$ is exact to every degree $m' \le m$. -/
theorem IsExactOn.mono {w : K → ℝ} {x : K → (ι → ℝ)} {m m' : ℕ} (h : IsExactOn μ w x m)
    (hm : m' ≤ m) : IsExactOn μ w x m' := fun p hp => h p (hp.trans hm)

/-- **Exactness on polynomials is exactness on monomials.** Let the set of variables be finite, and
let every monomial be integrable for $\mu$. Then a rule is exact to degree $m$ for $\mu$ if and
only if $$\sum_k w_k \prod_i (x_k)_i^{d_i} = \int \prod_i y_i^{d_i} \, d\mu(y)$$ for every
multi-index $d$ with $\sum_i d_i \le m$.

Both sides of the exactness identity are linear in the polynomial, and a polynomial is the sum
of its monomials. -/
theorem isExactOn_iff_forall_monomial [Fintype ι]
    (hμ : ∀ d : ι →₀ ℕ, Integrable (fun y => ∏ i, y i ^ d i) μ) (w : K → ℝ) (x : K → ι → ℝ)
    (m : ℕ) :
    IsExactOn μ w x m ↔
      ∀ d : ι →₀ ℕ, d.degree ≤ m → ∑ k, w k * ∏ i, x k i ^ d i = ∫ y, ∏ i, y i ^ d i ∂μ := by
  have hmono : ∀ (d : ι →₀ ℕ) (y : ι → ℝ),
      MvPolynomial.eval y (MvPolynomial.monomial d (1 : ℝ)) = ∏ i, y i ^ d i := by
    intro d y
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun i => pow_zero _]
  have hdeg : ∀ d : ι →₀ ℕ, (MvPolynomial.monomial d (1 : ℝ)).totalDegree = d.degree := by
    intro d
    rw [MvPolynomial.totalDegree_monomial _ one_ne_zero, Finsupp.degree_eq_sum, Finsupp.sum_fintype]
    intro i; rfl
  constructor
  · intro h d hd
    have := h (MvPolynomial.monomial d 1) (by rw [hdeg]; exact hd)
    simpa only [hmono] using this
  · intro h p hp
    conv_lhs => rw [MvPolynomial.as_sum p]
    conv_rhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun i => pow_zero _]
    rw [integral_finsetSum _ fun d _ => (hμ d).const_mul _]
    simp only [MeasureTheory.integral_const_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← h d ((MvPolynomial.le_totalDegree hd).trans hp |>.trans' ?_), Finset.mul_sum]
    · exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Finsupp.degree_eq_sum, Finsupp.sum_fintype]
      intro i; rfl

/-- Let $\mu$ be a measure on $\mathbb{R}^d$ for which every polynomial is square integrable and
only the zero polynomial vanishes almost everywhere. If a rule is exact to degree $2n$ for
$\mu$, then $$(p, q)_n = (p, q)_{L^2(\mu)}$$ for all polynomials $p$ and $q$ of total degree at
most $n$, because $pq$ has total degree at most $2n$. This identity makes hyperinterpolation a
projection.

The hypothesis on $\mu$ is `Approximation.IsMvWeight μ`, and the polynomials are mapped to
$L^2(\mu)$ by `Approximation.IsMvWeight.toL2`. -/
theorem discreteInner_eq_inner_toL2 (hw : IsMvWeight μ) {w : K → ℝ} {x : K → (ι → ℝ)} {n : ℕ}
    (hex : IsExactOn μ w x (2 * n)) {p q : MvPolynomial ι ℝ} (hp : p.totalDegree ≤ n)
    (hq : q.totalDegree ≤ n) : discreteInner w x p q = inner ℝ (hw.toL2 p) (hw.toL2 q) := by
  have h := hex (p * q) ((MvPolynomial.totalDegree_mul p q).trans (by omega))
  simp only [map_mul] at h
  rw [hw.inner_toL2, ← h, discreteInner]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- **Hyperinterpolation reproduces polynomials.** Let $\mu$ be a measure on $\mathbb{R}^d$ for
which every polynomial is square integrable and only the zero polynomial vanishes almost
everywhere. Let a rule be exact to degree $2n$ for $\mu$, and let $b_1, \dots, b_N$ be
polynomials of total degree at most $n$ that are orthonormal in $L^2(\mu)$. Then for every
polynomial $p$ of total degree at most $n$ in the span of $b_1, \dots, b_N$, $$L_n p = p.$$

On $\Pi_n^d$ the discrete inner product is the continuous one, so the coefficients that the rule
computes are the true Fourier coefficients. The hypothesis on $\mu$ is
`Approximation.IsMvWeight μ`. -/
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

/-- **Hyperinterpolation is idempotent.** Let $\mu$ be a measure on $\mathbb{R}^d$ for which every
polynomial is square integrable and only the zero polynomial vanishes almost everywhere. Let a
rule be exact to degree $2n$ for $\mu$, and let $b_1, \dots, b_N$ be polynomials of total degree
at most $n$ that are orthonormal in $L^2(\mu)$. Then for every function $f$, $$L_n(L_n f) = L_n
f.$$ With `Approximation.hyperinterp_mem_span` this says that $L_n$ is a projection onto the
span of $b$. -/
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
