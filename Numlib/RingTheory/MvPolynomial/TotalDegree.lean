/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.MvPolynomial.Degrees`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Total degree under substitution

Let $R$ be a commutative semiring, let $p \in R[X_i : i \in \sigma]$, and let $f$ assign to each
variable $X_i$ a polynomial $f_i \in R[X_j : j \in \tau]$. Write $p(f)$ for the polynomial
`MvPolynomial.bind₁ f p` obtained by substituting $f_i$ for $X_i$, and $\deg$ for the total degree.
If every $f_i$ has total degree at most $k$, then $\deg p(f) \le k \deg p$, and the same bound holds
when a one-variable polynomial is evaluated at a multivariate polynomial. For $k = 1$ the
substitution is a change of variables by an affine map, and it does not raise the total degree. If
such a substitution has an inverse of the same kind, it preserves the total degree exactly, and it
maps the space $\Pi_n$ of polynomials of total degree at most $n$
(`MvPolynomial.restrictTotalDegree`) onto $\Pi_n$.

The case $k = 1$ shows that an approximation problem on an ellipsoid is the same problem on a ball:
the affine map that carries one onto the other carries the polynomials of degree at most $n$ onto
the polynomials of degree at most $n$.

## Main results

* `MvPolynomial.totalDegree_bind₁_le`: if every $f_i$ has total degree at most $k$, then
  $\deg p(f) \le k \deg p$.
* `MvPolynomial.totalDegree_aeval_le`: if $q$ has total degree at most $k$ and $p$ is a one-variable
  polynomial of degree $d$, then $\deg p(q) \le k d$.
* `MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one`: a substitution by polynomials of total
  degree at most one does not raise the total degree.
* `MvPolynomial.totalDegree_bind₁_eq_of_leftInverse`: a substitution by polynomials of total degree
  at most one that has a left inverse of the same kind preserves the total degree.
* `MvPolynomial.restrictTotalDegree_map_bind₁`: a substitution by polynomials of total degree at
  most one that has a two-sided inverse of the same kind maps $\Pi_n$ onto $\Pi_n$.
-/

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- The **total degree of a substitution**. Let $f$ assign to each $i \in \sigma$ a polynomial
$f_i \in R[X_j : j \in \tau]$ of total degree at most $k$, and let
$p \in R[X_i : i \in \sigma]$. Then the polynomial $p(f)$, obtained from $p$ by substituting
$f_i$ for each variable $X_i$, satisfies
$$\deg p(f) \le k \deg p,$$
where $\deg$ is the total degree.

The polynomial $p(f)$ is `MvPolynomial.bind₁ f p`, and the total degree is
`MvPolynomial.totalDegree`. -/
theorem totalDegree_bind₁_le {k : ℕ} {f : σ → MvPolynomial τ R} (hf : ∀ i, (f i).totalDegree ≤ k)
    (p : MvPolynomial σ R) : (bind₁ f p).totalDegree ≤ k * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have hterm : ∀ i ∈ m.support, (f i ^ m i).totalDegree ≤ k * m i := fun i _ =>
    (totalDegree_pow _ _).trans <| calc
      m i * (f i).totalDegree ≤ m i * k := Nat.mul_le_mul_left _ (hf i)
      _ = k * m i := Nat.mul_comm _ _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ (le_totalDegree hm)

/-- The **total degree of a one-variable polynomial evaluated at a multivariate polynomial**. Let
$q \in R[X_j : j \in \tau]$ have total degree at most $k$, and let $p \in R[X]$ be a
one-variable polynomial of degree $d$. Then
$$\deg p(q) \le k d,$$
where $\deg$ is the total degree.

This is the one-variable counterpart of `MvPolynomial.totalDegree_bind₁_le`. The polynomial
$p(q)$ is `Polynomial.aeval q p`. The degree $d$ is `Polynomial.natDegree p`, which is $0$ for
$p = 0$. The case $k = 1$ says that a ridge polynomial, a one-variable polynomial of a linear
form, has total degree at most the degree of the one-variable polynomial. -/
theorem totalDegree_aeval_le {k : ℕ} {q : MvPolynomial τ R} (hq : q.totalDegree ≤ k)
    (p : Polynomial R) : (Polynomial.aeval q p).totalDegree ≤ k * p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  rw [Finset.mem_range] at hi
  calc i * q.totalDegree ≤ p.natDegree * k := Nat.mul_le_mul (by omega) hq
    _ = k * p.natDegree := Nat.mul_comm _ _

/-- Let each $f_i$, $i \in \sigma$, be a polynomial of total degree at most $1$. Then for every
$p \in R[X_i : i \in \sigma]$ the substitution $p(f)$ satisfies
$$\deg p(f) \le \deg p.$$

This is the case $k = 1$ of `MvPolynomial.totalDegree_bind₁_le`. -/
theorem totalDegree_bind₁_le_of_totalDegree_le_one {f : σ → MvPolynomial τ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree ≤ p.totalDegree := by
  simpa using totalDegree_bind₁_le hf p

/-- An **invertible substitution by polynomials of degree at most one preserves the total degree**.
Let $f_i \in R[X_j : j \in \tau]$ for $i \in \sigma$ and $g_j \in R[X_i : i \in \sigma]$ for
$j \in \tau$ all have total degree at most $1$, and suppose that $(p(f))(g) = p$ for every
$p \in R[X_i : i \in \sigma]$. Then for every such $p$,
$$\deg p(f) = \deg p.$$

The affine changes of variables are substitutions of this kind, so an affine change of
coordinates on the domain neither raises nor lowers the total degree of a polynomial. The
substitution $p(f)$ is `MvPolynomial.bind₁ f p`. -/
theorem totalDegree_bind₁_eq_of_leftInverse {f : σ → MvPolynomial τ R} {g : τ → MvPolynomial σ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (hgf : ∀ p : MvPolynomial σ R, bind₁ g (bind₁ f p) = p) (p : MvPolynomial σ R) :
    (bind₁ f p).totalDegree = p.totalDegree :=
  le_antisymm (totalDegree_bind₁_le_of_totalDegree_le_one hf p)
    (by
      conv_lhs => rw [← hgf p]
      exact totalDegree_bind₁_le_of_totalDegree_le_one hg _)

/-- An **invertible substitution by polynomials of degree at most one maps $\Pi_n$ onto $\Pi_n$**.
Let $f_i \in R[X_j : j \in \tau]$ for $i \in \sigma$ and $g_j \in R[X_i : i \in \sigma]$ for
$j \in \tau$ all have total degree at most $1$, and suppose that $(p(f))(g) = p$ for every
$p \in R[X_i : i \in \sigma]$ and $(q(g))(f) = q$ for every $q \in R[X_j : j \in \tau]$. Then
for every $n \in \mathbb{N}$ the map $p \mapsto p(f)$ carries the polynomials in the variables
$X_i$ of total degree at most $n$ onto the polynomials in the variables $X_j$ of total degree at
most $n$.

The two spaces are `MvPolynomial.restrictTotalDegree σ R n` and
`MvPolynomial.restrictTotalDegree τ R n`, and the statement is an equality of submodules: the
image of the first under the linear map `MvPolynomial.bind₁ f` is the second. -/
theorem restrictTotalDegree_map_bind₁ {f : σ → MvPolynomial τ R} {g : τ → MvPolynomial σ R}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (hgf : ∀ p : MvPolynomial σ R, bind₁ g (bind₁ f p) = p)
    (hfg : ∀ q : MvPolynomial τ R, bind₁ f (bind₁ g q) = q) (n : ℕ) :
    (restrictTotalDegree σ R n).map (bind₁ f).toLinearMap = restrictTotalDegree τ R n := by
  ext q
  simp only [Submodule.mem_map, mem_restrictTotalDegree, AlgHom.toLinearMap_apply]
  refine ⟨?_, fun hq => ⟨bind₁ g q, ?_, hfg q⟩⟩
  · rintro ⟨p, hp, rfl⟩
    exact (totalDegree_bind₁_eq_of_leftInverse hf hg hgf p).trans_le hp
  · rw [totalDegree_bind₁_eq_of_leftInverse hg hf hfg q]
    exact hq

end MvPolynomial
