/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Approximation.MvPolynomial
import Numlib.Geometry.Triangulation

/-!
# The Lagrange element of degree $k$ on a triangle

This file constructs the Lagrange finite element of degree $k \ge 1$ on the reference triangle $\hat
K = \{\hat x : \hat x_1 > 0,\ \hat x_2 > 0,\ \hat x_1 + \hat x_2 < 1\}$. Its nodes are the points of
the **principal lattice** $$\hat N_k = \{(m_1/k, m_2/k) : m_1, m_2 \in \mathbb{N},\ m_1 + m_2 \le
k\},$$ which is (10.2.24) of [han2009theoretical]. Its local space is $\mathbb{P}_k$, the
polynomials in two variables of total degree at most $k$, and its shape functions are
**Silvester's** nodal polynomials $L_m$. The file proves the properties that the finite element
theory on a triangulation (`Numlib.Geometry.Triangulation`) requires of an element: unisolvence of
$\mathbb{P}_k$ on $\hat N_k$ (Proposition 10.2.1 of [han2009theoretical]), so that interpolation at
the nodes reproduces $\mathbb{P}_k$; the shape functions are nodal, smooth and in $\mathbb{P}_k$,
and the nodes lie in the closed reference triangle; the element is conforming on every triangulation
(Example 10.2.3 and Exercise 10.2.4 of [han2009theoretical]); and the element is edge unisolvent.

The interpolation error of this element on a regular family of triangulations is
`LagrangeElement.sobolevNorm_sub_globalInterp_le` in `Numlib.FiniteElement.Interpolation`.

## Main definitions

* `LagrangeElement.latticePoint`: the point $(m_1/k, m_2/k)$ of $\hat N_k$.
* `LagrangeElement.latticeShape`: Silvester's shape polynomial $L_m$.
* `LagrangeElement.latticeEval`: the evaluation map from $\mathbb{P}_k$ to the values on $\hat N_k$.
* `LagrangeElement.LatticeNode`: the index type of the nodes.
* `LagrangeElement.node`, `LagrangeElement.shape`: the nodes and the shape functions of the element
  on $\mathbb{R}^2$, in the form that `Triangulation.localInterp` takes.

## Main results

* `LagrangeElement.bijective_latticeEval`: unisolvence of $\mathbb{P}_k$ on $\hat N_k$.
* `LagrangeElement.eq_zero_of_eval_latticePoint`: a polynomial in $\mathbb{P}_k$ that vanishes on
  $\hat N_k$ is zero.
* `LagrangeElement.isNodalBasis`: the shape functions satisfy $\varphi_i(x_j) = \delta_{ij}$.
* `LagrangeElement.nodalInterp_eval`: the interpolant of a polynomial in $\mathbb{P}_k$ is the
  polynomial.
* `LagrangeElement.isConformingElement`: the local interpolants of two elements agree on their
  common points.
* `LagrangeElement.isEdgeUnisolvent`: an interpolant that vanishes at the nodes of an edge vanishes
  on the edge.

## Proof outline

The nodal basis is given explicitly. For a lattice point with barycentric multi-index
$\alpha = (\alpha_1, \alpha_2, \alpha_3)$, $\sum_c \alpha_c = k$, Silvester's shape function is
$$L_\alpha = \prod_{c=1}^{3} \prod_{r=0}^{\alpha_c - 1} \frac{k \lambda_c - r}{\alpha_c - r},$$
where the $\lambda_c$ are the barycentric coordinates. It has total degree $\sum_c \alpha_c = k$. At
the lattice point with multi-index $\beta$ the scaled coordinate $k \lambda_c$ takes the value
$\beta_c$. So $L_\alpha$ is $1$ at $\beta = \alpha$. At any other $\beta$ some $\beta_c < \alpha_c$,
because the two multi-indices have the same sum, and then the factor with $r = \beta_c$ vanishes.
Thus evaluation on the lattice is surjective. The space $\mathbb{P}_k$ and the lattice have the same
cardinality $\binom{k+2}{2}$, because the lattice is indexed by the exponent vectors that index the
monomial basis. Therefore evaluation is bijective. The proof needs neither the divisibility of a
polynomial by an affine form nor the induction on $k$ of the classical argument.

Conformity and edge unisolvence use the same one-variable argument. Along an edge $P + s(Q - P)$ an
interpolant restricts to a polynomial of degree at most $k$ in $s$, and the edge carries the $k + 1$
lattice nodes $s = j/k$.

## Implementation notes

* Polynomials are `MvPolynomial (Fin 2) ℝ`, and $\mathbb{P}_k$ is
  `MvPolynomial.restrictTotalDegree (Fin 2) ℝ k`. A lattice point is indexed by its exponent vector
  $m = (m_1, m_2)$ as an element of `Fin 2 →₀ ℕ`, whose entries Lean indexes by `0` and `1`.
* The nodes and the shape functions on $\mathbb{R}^2$ are indexed by `Fin (Fintype.card
  (LagrangeElement.LatticeNode k))`, through the enumeration `Fintype.equivFin` of the lattice
  nodes.
-/

namespace LagrangeElement

section PrincipalLattice

open Finset Module MvPolynomial

/-- The **Lagrange factor** of a polynomial $\ell$ in two variables and of $a \in \mathbb{N}$ is the
polynomial $$\prod_{r=0}^{a-1} \frac{\ell - r}{a - r}.$$ For an affine $\ell$ it equals $1$
where $\ell = a$, it vanishes where $\ell$ takes a natural value smaller than $a$, and it has
total degree at most $a$. -/
noncomputable def lagFactor (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ r ∈ Finset.range a, C ((a : ℝ) - r)⁻¹ * (ℓ - C (r : ℝ))

/-- If $\ell$ has total degree at most $1$, its Lagrange factor of index $a$ has total degree at
most $a$. -/
theorem totalDegree_lagFactor_le {ℓ : MvPolynomial (Fin 2) ℝ} (hℓ : ℓ.totalDegree ≤ 1) (a : ℕ) :
    (lagFactor ℓ a).totalDegree ≤ a := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun r _ => ?_) (by simp)
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact le_trans (totalDegree_sub_C_le _ _) hℓ

/-- The value of the Lagrange factor of $\ell$ and $a$ at $x$ is
$\prod_{r=0}^{a-1} (\ell(x) - r)/(a - r)$. -/
theorem eval_lagFactor (x : Fin 2 → ℝ) (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) :
    eval x (lagFactor ℓ a) = ∏ r ∈ Finset.range a, ((a : ℝ) - r)⁻¹ * (eval x ℓ - r) := by
  simp [lagFactor]

/-- If $\ell(x) = a$, then the Lagrange factor of $\ell$ and $a$ takes the value $1$ at $x$. -/
theorem eval_lagFactor_self {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a : ℕ}
    (h : eval x ℓ = (a : ℝ)) : eval x (lagFactor ℓ a) = 1 := by
  rw [eval_lagFactor, h]
  refine Finset.prod_eq_one fun r hr => ?_
  have hne : ((a : ℝ) - r) ≠ 0 := by
    have : (r : ℝ) < a := by exact_mod_cast Finset.mem_range.mp hr
    linarith
  field_simp

/-- If $\ell(x) = b$ for a natural number $b < a$, then the Lagrange factor of $\ell$ and $a$
vanishes at $x$, because its factor with $r = b$ is zero. -/
theorem eval_lagFactor_of_lt {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a b : ℕ} (hb : b < a)
    (h : eval x ℓ = (b : ℝ)) : eval x (lagFactor ℓ a) = 0 := by
  rw [eval_lagFactor, h]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hb) (by simp)

/-- The barycentric coordinates $\hat\lambda_1 = 1 - \hat x_1 - \hat x_2$,
$\hat\lambda_2 = \hat x_1$ and $\hat\lambda_3 = \hat x_2$ of the reference triangle, multiplied
by $k$. Each of them takes an integer value at every point of $\hat N_k$. -/
noncomputable def scaledBary (k : ℕ) : Fin 3 → MvPolynomial (Fin 2) ℝ :=
  ![C (k : ℝ) * (1 - X 0 - X 1), C (k : ℝ) * X 0, C (k : ℝ) * X 1]

/-- The scaled barycentric coordinates have total degree at most $1$. -/
theorem totalDegree_scaledBary_le (k : ℕ) (c : Fin 3) : (scaledBary k c).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 2, (X i : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := fun i =>
    le_of_eq (totalDegree_X i)
  have hmul : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 1 →
      (C (k : ℝ) * q).totalDegree ≤ 1 := fun q hq =>
    le_trans (totalDegree_mul _ _) (by rw [totalDegree_C, zero_add]; exact hq)
  fin_cases c
  · exact hmul _ (le_trans (totalDegree_sub _ _)
      (max_le (le_trans (totalDegree_sub _ _) (max_le (by simp) (hX 0))) (hX 1)))
  · exact hmul _ (hX 0)
  · exact hmul _ (hX 1)

/-- The point $(m_1/k, m_2/k)$ of the **principal lattice** $\hat N_k$ of the reference triangle,
for an exponent vector $m = (m_1, m_2) \in \mathbb{N}^2$. As $m$ ranges over the exponent
vectors with $m_1 + m_2 \le k$, these points form the set $$\hat N_k = \Big\{\sum_i t_i \hat a_i
: \sum_i t_i = 1,\ t_i \in \{0, 1/k, \dots, 1\}\Big\}$$ of (10.2.24) of [han2009theoretical],
where the $\hat a_i$ are the vertices of the reference triangle.

The exponent vector is an element of `Fin 2 →₀ ℕ`, the type that indexes the monomials of
`MvPolynomial (Fin 2) ℝ`. For $k = 0$ the division by zero gives the origin. -/
noncomputable def latticePoint (k : ℕ) (m : Fin 2 →₀ ℕ) (i : Fin 2) : ℝ := (m i : ℝ) / k

/-- The barycentric multi-index $(k - m_1 - m_2, m_1, m_2)$ of the lattice point with exponent
vector $m$: the values of the scaled barycentric coordinates at that point. The subtraction is
truncated at $0$. -/
def latticeMulti (k : ℕ) (m : Fin 2 →₀ ℕ) : Fin 3 → ℕ := ![k - m 0 - m 1, m 0, m 1]

/-- If $m_1 + m_2 \le k$, the barycentric multi-index of $m$ sums to $k$. -/
theorem sum_latticeMulti {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    ∑ c, latticeMulti k m c = k := by
  simp only [Fin.sum_univ_three, latticeMulti, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  omega

/-- Let $k \ge 1$ and $m_1 + m_2 \le k$. At the lattice point of $m$ the scaled barycentric
coordinates take the values of the barycentric multi-index of $m$. -/
theorem eval_scaledBary {k : ℕ} (hk : 0 < k) {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) (c : Fin 3) :
    eval (latticePoint k m) (scaledBary k c) = (latticeMulti k m c : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hcast : ((k - m 0 - m 1 : ℕ) : ℝ) = (k : ℝ) - m 0 - m 1 := by
    have h1 : m 0 ≤ k := by omega
    have h2 : m 1 ≤ k - m 0 := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
  fin_cases c
  · change eval (latticePoint k m) (C (k : ℝ) * (1 - X 0 - X 1)) = ((k - m 0 - m 1 : ℕ) : ℝ)
    rw [hcast]
    simp only [map_mul, map_sub, map_one, eval_C, eval_X, latticePoint]
    field_simp
  · change eval (latticePoint k m) (C (k : ℝ) * X 0) = ((m 0 : ℕ) : ℝ)
    simp only [map_mul, eval_C, eval_X, latticePoint]
    field_simp
  · change eval (latticePoint k m) (C (k : ℝ) * X 1) = ((m 1 : ℕ) : ℝ)
    simp only [map_mul, eval_C, eval_X, latticePoint]
    field_simp

/-- **Silvester's shape function** of the principal lattice at the point with exponent vector $m$.
With $\alpha = (\alpha_1, \alpha_2, \alpha_3)$ the barycentric multi-index of $m$ and
$\lambda_c$ the barycentric coordinates, it is $$L_m = \prod_{c=1}^{3} \prod_{r=0}^{\alpha_c -
1} \frac{k \lambda_c - r}{\alpha_c - r},$$ the product of the Lagrange factors of the three
scaled barycentric coordinates. -/
noncomputable def latticeShape (k : ℕ) (m : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ c, lagFactor (scaledBary k c) (latticeMulti k m c)

/-- If $m_1 + m_2 \le k$, the shape function $L_m$ has total degree at most $k$, so it lies in
$\mathbb{P}_k$. -/
theorem totalDegree_latticeShape_le {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    (latticeShape k m).totalDegree ≤ k := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun c _ =>
    totalDegree_lagFactor_le (totalDegree_scaledBary_le k c) _) ?_
  exact le_of_eq (sum_latticeMulti hm)

/-- Let $m \ne m'$ be exponent vectors with $m_1 + m_2 \le k$ and $m'_1 + m'_2 \le k$, with
barycentric multi-indices $\alpha$ and $\beta$. Then $\beta_c < \alpha_c$ for some $c$, because
both multi-indices sum to $k$. This makes a shape function vanish at every node except its own. -/
theorem exists_latticeMulti_lt {k : ℕ} {m m' : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k)
    (hm' : m' 0 + m' 1 ≤ k) (hne : m ≠ m') :
    ∃ c, latticeMulti k m' c < latticeMulti k m c := by
  have hcoord : m 0 ≠ m' 0 ∨ m 1 ≠ m' 1 := by
    by_contra hcon
    have h0 : m 0 = m' 0 := not_not.mp fun hh => hcon (Or.inl hh)
    have h1 : m 1 = m' 1 := not_not.mp fun hh => hcon (Or.inr hh)
    refine hne (Finsupp.ext fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
  rcases lt_or_ge (m' 0) (m 0) with h0 | h0
  · exact ⟨1, by simpa [latticeMulti] using h0⟩
  · rcases lt_or_ge (m' 1) (m 1) with h1 | h1
    · exact ⟨2, by simpa [latticeMulti] using h1⟩
    · refine ⟨0, ?_⟩
      simp only [latticeMulti, Matrix.cons_val_zero]
      omega

/-- **The shape functions are dual to the lattice points.** Let $k \ge 1$, and let $m$ and $m'$ be
exponent vectors with $m_1 + m_2 \le k$ and $m'_1 + m'_2 \le k$. Then $$L_m(x_{m'}) = \delta_{m
m'},$$ where $x_{m'}$ is the lattice point of $m'$. -/
theorem eval_latticeShape {k : ℕ} (hk : 0 < k) {m m' : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k)
    (hm' : m' 0 + m' 1 ≤ k) :
    eval (latticePoint k m') (latticeShape k m) = if m = m' then 1 else 0 := by
  rw [latticeShape, map_prod]
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun c _ => eval_lagFactor_self (eval_scaledBary hk hm c)
  · obtain ⟨c, hc⟩ := exists_latticeMulti_lt hm hm' (Ne.symm fun hh => h hh.symm)
    exact Finset.prod_eq_zero (Finset.mem_univ c)
      (eval_lagFactor_of_lt hc (eval_scaledBary hk hm' c))

/-- The index set of the principal lattice $\hat N_k$: the exponent vectors $m \in \mathbb{N}^2$
with $m_1 + m_2 \le k$. It is also the index set of the monomial basis of $\mathbb{P}_k$, so the
two sets have the same cardinality without a separate count. -/
def latticeIndex (k : ℕ) : Set (Fin 2 →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ k}

/-- An exponent vector $m$ lies in the lattice index set if and only if $m_1 + m_2 \le k$. -/
theorem mem_latticeIndex_iff {k : ℕ} {m : Fin 2 →₀ ℕ} :
    m ∈ latticeIndex k ↔ m 0 + m 1 ≤ k := by
  change (m.sum fun _ e => e) ≤ k ↔ _
  rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_two]

/-- The **interpolation map** of the principal lattice: the linear map from $\mathbb{P}_k$ to
$\mathbb{R}^{\hat N_k}$ that evaluates a polynomial of total degree at most $k$ at the points of
$\hat N_k$.

$\mathbb{P}_k$ is `MvPolynomial.restrictTotalDegree (Fin 2) ℝ k`, and the points are indexed by
`LagrangeElement.latticeIndex k`. -/
noncomputable def latticeEval (k : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 2) ℝ k) →ₗ[ℝ] (latticeIndex k → ℝ) where
  toFun p m := eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ)
  map_add' p q := by ext m; simp
  map_smul' a p := by ext m; simp

/-- The interpolation map sends $p \in \mathbb{P}_k$ to the family of its values $p(x_m)$ at the
lattice points. -/
@[simp]
theorem latticeEval_apply (k : ℕ) (p : MvPolynomial.restrictTotalDegree (Fin 2) ℝ k)
    (m : latticeIndex k) :
    latticeEval k p m = eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ) := rfl

/-- **Unisolvence of $\mathbb{P}_k$ on the principal lattice.** Let $k \ge 1$. The interpolation map
from $\mathbb{P}_k$ to the values at the $(k+1)(k+2)/2$ points of $\hat N_k$ is bijective. That
is, a polynomial of total degree at most $k$ is uniquely determined by its values on $\hat N_k$,
and all values can be prescribed. This is Proposition 10.2.1 of [han2009theoretical], which the
source states without proof.

Surjectivity comes from Silvester's shape functions `LagrangeElement.latticeShape`, which are
dual to the nodes by `LagrangeElement.eval_latticeShape`. Injectivity follows because
$\mathbb{P}_k$ and the lattice both have $\binom{k+2}{2}$ elements: the lattice is indexed by
the exponent vectors that index the monomial basis. -/
theorem bijective_latticeEval {k : ℕ} (hk : 0 < k) : Function.Bijective (latticeEval k) := by
  classical
  have hfin : Fintype (latticeIndex k) := by
    change Fintype ↑{m : Fin 2 →₀ ℕ | (m.sum fun _ e => e) ≤ k}
    exact Fintype.ofEquiv _ (MvPolynomial.slackEquiv (Fin 2) k).symm
  have hshape : ∀ m : latticeIndex k,
      latticeShape k (m : Fin 2 →₀ ℕ) ∈ MvPolynomial.restrictTotalDegree (Fin 2) ℝ k := fun m => by
    rw [mem_restrictTotalDegree]
    exact totalDegree_latticeShape_le (mem_latticeIndex_iff.mp m.2)
  have hsurj : Function.Surjective (latticeEval k) := by
    intro b
    refine ⟨∑ m : latticeIndex k, b m • ⟨latticeShape k (m : Fin 2 →₀ ℕ), hshape m⟩, ?_⟩
    ext m'
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single m']
    · have h := eval_latticeShape hk (mem_latticeIndex_iff.mp m'.2) (mem_latticeIndex_iff.mp m'.2)
      change b m' * eval (latticePoint k (m' : Fin 2 →₀ ℕ))
        (latticeShape k (m' : Fin 2 →₀ ℕ)) = b m'
      rw [h]
      simp
    · intro m _ hmm
      have h := eval_latticeShape hk (mem_latticeIndex_iff.mp m.2) (mem_latticeIndex_iff.mp m'.2)
      change b m * eval (latticePoint k (m' : Fin 2 →₀ ℕ)) (latticeShape k (m : Fin 2 →₀ ℕ)) = 0
      have hne2 : ¬ ((m : Fin 2 →₀ ℕ) = (m' : Fin 2 →₀ ℕ)) := fun hh => hmm (Subtype.ext hh)
      rw [h]
      simp [hne2]
    · intro h; exact absurd (Finset.mem_univ m') h
  have hcardIdx : Fintype.card (latticeIndex k) = (k + 2).choose k := by
    rw [← Nat.card_eq_fintype_card]
    exact (MvPolynomial.card_setOf_sum_le (Fin 2) k).trans (by simp)
  have hdim : finrank ℝ (MvPolynomial.restrictTotalDegree (Fin 2) ℝ k)
      = finrank ℝ (latticeIndex k → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, hcardIdx,
      MvPolynomial.finrank_restrictTotalDegree (Fin 2) k ℝ]
    simp only [Fintype.card_fin]
    rw [← Nat.choose_symm (by omega : k ≤ k + 2)]
    congr 1
    omega
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- **Unisolvence**, in the form that the finite element proofs use. Let $k \ge 1$ and let $p$ be a
polynomial in two variables of total degree at most $k$. If $p(m_1/k, m_2/k) = 0$ for all
$m_1, m_2 \in \mathbb{N}$ with $m_1 + m_2 \le k$, then $p = 0$. This is Proposition 10.2.1 of
[han2009theoretical]. -/
theorem eq_zero_of_eval_latticePoint {k : ℕ} (hk : 0 < k) {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.totalDegree ≤ k)
    (h : ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 ≤ k → eval (latticePoint k m) p = 0) : p = 0 := by
  have hmem : p ∈ MvPolynomial.restrictTotalDegree (Fin 2) ℝ k := by
    rw [mem_restrictTotalDegree]; exact hp
  have hzero := (bijective_latticeEval hk).1 (a₁ := ⟨p, hmem⟩) (a₂ := 0) ?_
  · exact congrArg Subtype.val hzero
  · ext m
    rw [latticeEval_apply, latticeEval_apply]
    simpa using h (m : Fin 2 →₀ ℕ) (mem_latticeIndex_iff.mp m.2)

end PrincipalLattice

section LatticeElement

open Finset MvPolynomial EuclideanSpace TopologicalSpace

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-- The index type of the nodes of the principal lattice $\hat N_k$: the pairs $(m_1, m_2)$ of
natural numbers with $m_1 + m_2 \le k$.

It is a subtype of `Fin (k + 1) × Fin (k + 1)`, hence finite. -/
def LatticeNode (k : ℕ) : Type := {p : Fin (k + 1) × Fin (k + 1) // (p.1 : ℕ) + p.2 ≤ k}

/-- There are finitely many lattice nodes. -/
instance (k : ℕ) : Fintype (LatticeNode k) := Subtype.fintype _

/-- The exponent vector $(m_1, m_2)$ of a lattice node, as the element of `Fin 2 →₀ ℕ` that indexes
`LagrangeElement.latticePoint` and `LagrangeElement.latticeShape`. -/
noncomputable def LatticeNode.toFinsupp {k : ℕ} (p : LatticeNode k) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (p.1.1 : ℕ) + Finsupp.single 1 (p.1.2 : ℕ)

/-- The first entry of the exponent vector of the lattice node $(m_1, m_2)$ is $m_1$. -/
@[simp]
theorem LatticeNode.toFinsupp_zero {k : ℕ} (p : LatticeNode k) : p.toFinsupp 0 = p.1.1 := by
  simp [LatticeNode.toFinsupp]

/-- The second entry of the exponent vector of the lattice node $(m_1, m_2)$ is $m_2$. -/
@[simp]
theorem LatticeNode.toFinsupp_one {k : ℕ} (p : LatticeNode k) : p.toFinsupp 1 = p.1.2 := by
  simp [LatticeNode.toFinsupp]

/-- The entries of the exponent vector of a lattice node sum to at most $k$. -/
theorem LatticeNode.sum_toFinsupp_le {k : ℕ} (p : LatticeNode k) :
    p.toFinsupp 0 + p.toFinsupp 1 ≤ k := by
  simp only [LatticeNode.toFinsupp_zero, LatticeNode.toFinsupp_one]
  exact p.2

/-- Distinct lattice nodes have distinct exponent vectors. -/
theorem LatticeNode.toFinsupp_injective (k : ℕ) :
    Function.Injective (LatticeNode.toFinsupp (k := k)) := by
  intro p q h
  have h0 := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
  have h1 := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 1) h
  simp only [LatticeNode.toFinsupp_zero, LatticeNode.toFinsupp_one] at h0 h1
  exact Subtype.ext (Prod.ext (Fin.ext h0) (Fin.ext h1))

/-- Every exponent vector $m$ with $m_1 + m_2 \le k$ is the exponent vector of a lattice node. -/
theorem LatticeNode.exists_toFinsupp_eq {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    ∃ p : LatticeNode k, p.toFinsupp = m :=
  ⟨⟨(⟨m 0, by omega⟩, ⟨m 1, by omega⟩), hm⟩, by
    ext i
    fin_cases i <;> simp [LatticeNode.toFinsupp]⟩

/-- The lattice node with exponent vector $(m_1, m_2)$, for natural numbers with $m_1 + m_2 \le k$.
-/
def LatticeNode.mk' {k : ℕ} (m₀ m₁ : ℕ) (h : m₀ + m₁ ≤ k) : LatticeNode k :=
  ⟨(⟨m₀, by omega⟩, ⟨m₁, by omega⟩), h⟩

/-- **The nodes of the $\mathbb{P}_k$ Lagrange element** on the reference triangle: the points
$(m_1/k, m_2/k)$ of the principal lattice $\hat N_k$ ((10.2.24) of [han2009theoretical]), as
points of $\mathbb{R}^2$.

The nodes are indexed by `Fin (Fintype.card (LagrangeElement.LatticeNode k))`, the form that
`Triangulation.localInterp` takes, through the enumeration `Fintype.equivFin` of the lattice
nodes. -/
noncomputable def node (k : ℕ) : Fin (Fintype.card (LatticeNode k)) → 𝔼₂ := fun i ↦
  WithLp.toLp 2 (latticePoint k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp)

/-- **The shape functions of the $\mathbb{P}_k$ Lagrange element**: Silvester's polynomials $L_m$
(`LagrangeElement.latticeShape`), as functions on $\mathbb{R}^2$, indexed like the nodes
`LagrangeElement.node`. -/
noncomputable def shape (k : ℕ) : Fin (Fintype.card (LatticeNode k)) → 𝔼₂ → ℝ :=
  fun i x ↦
    eval (fun j ↦ x j) (latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp)

/-- The node with exponent vector $(m_1, m_2)$ has the coordinates $(m_1/k, m_2/k)$. -/
theorem node_apply (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) (j : Fin 2) :
    node k i j
      = (((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp j : ℝ) / k := rfl

/-- Let $k \ge 1$. The shape functions of the $\mathbb{P}_k$ Lagrange element are nodal for its
nodes: $\varphi_i(x_j) = \delta_{ij}$.

The statement is `Approximation.IsNodalBasis`. It is the duality $L_m(x_{m'}) = \delta_{m m'}$
of `LagrangeElement.eval_latticeShape`. -/
theorem isNodalBasis {k : ℕ} (hk : 0 < k) :
    Approximation.IsNodalBasis (node k) (shape k) where
  eval_self i := by
    simp only [shape, node]
    rw [show (fun j ↦ (WithLp.toLp 2 (latticePoint k _) : 𝔼₂) j) = latticePoint k _ from rfl,
      eval_latticeShape hk (LatticeNode.sum_toFinsupp_le _) (LatticeNode.sum_toFinsupp_le _),
      ite_eq_left rfl]
  eval_of_ne i j hij := by
    simp only [shape, node]
    rw [show (fun j ↦ (WithLp.toLp 2 (latticePoint k _) : 𝔼₂) j) = latticePoint k _ from rfl,
      eval_latticeShape hk (LatticeNode.sum_toFinsupp_le _) (LatticeNode.sum_toFinsupp_le _),
      ite_eq_right]
    intro h
    exact hij ((Fintype.equivFin (LatticeNode k)).symm.injective
      (LatticeNode.toFinsupp_injective k h))

/-- Let $k \ge 1$. Every node of the $\mathbb{P}_k$ Lagrange element lies in the closed reference
triangle $\overline{\hat K}$. -/
theorem node_mem_closure {k : ℕ} (hk : 0 < k) (i : Fin (Fintype.card (LatticeNode k))) :
    node k i ∈ closure (referenceTriangle : Set 𝔼₂) := by
  refine mem_closure_referenceTriangle ?_
  simp only [node_apply]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := LatticeNode.sum_toFinsupp_le ((Fintype.equivFin (LatticeNode k)).symm i)
  refine ⟨by positivity, by positivity, ?_⟩
  rw [← add_div, div_le_one hk']
  exact_mod_cast h

/-- The shape functions of the $\mathbb{P}_k$ Lagrange element are $C^\infty$ on $\mathbb{R}^2$. -/
theorem contDiff_shape (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (shape k i) := by
  have : shape k i = evalBasis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp) := by
    funext x
    exact (MvPolynomial.evalBasis_basisFun _ x).symm
  rw [this]
  exact MvPolynomial.contDiff_evalBasis _ _

/-- **Interpolation on the principal lattice reproduces $\mathbb{P}_k$.** Let $k \ge 1$ and let $q$
be a polynomial in two variables of total degree at most $k$. Then the nodal interpolant of $q$
with the nodes $x_i$ and the shape functions $\varphi_i$ of the $\mathbb{P}_k$ Lagrange element
equals $q$ at every point $x \in \mathbb{R}^2$: $$\sum_i \varphi_i(x)\, q(x_i) = q(x).$$ This is
unisolvence in the form of the polynomial invariance (10.3.4) of [han2009theoretical].

The difference of the interpolant and $q$ is a polynomial of total degree at most $k$ that
vanishes at every lattice node, hence zero by `LagrangeElement.eq_zero_of_eval_latticePoint`. -/
theorem nodalInterp_eval {k : ℕ} (hk : 0 < k) (q : MvPolynomial (Fin 2) ℝ)
    (hq : q.totalDegree ≤ k) (x : 𝔼₂) :
    Approximation.nodalInterp (node k) (shape k)
      (fun y : 𝔼₂ ↦ eval (fun i ↦ y i) q) x = eval (fun i ↦ x i) q := by
  set e := Fintype.equivFin (LatticeNode k) with he
  set r : MvPolynomial (Fin 2) ℝ := q - ∑ i, C (eval (latticePoint k (e.symm i).toFinsupp) q)
    * latticeShape k (e.symm i).toFinsupp with hr
  have hrdeg : r.totalDegree ≤ k := by
    rw [← mem_restrictTotalDegree]
    refine Submodule.sub_mem _ ((mem_restrictTotalDegree _ _ _).2 hq)
      (Submodule.sum_mem _ fun i _ ↦ ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_restrictTotalDegree _ _ _).2
      (totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _)))
  have hrzero : ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 ≤ k → eval (latticePoint k m) r = 0 := by
    intro m hm
    obtain ⟨p, rfl⟩ := LatticeNode.exists_toFinsupp_eq hm
    rw [hr, map_sub, map_sum, Finset.sum_eq_single (e p)]
    · rw [map_mul, eval_C, Equiv.symm_apply_apply,
        eval_latticeShape hk (LatticeNode.sum_toFinsupp_le _) (LatticeNode.sum_toFinsupp_le _),
        ite_eq_left rfl, mul_one, sub_self]
    · intro i _ hi
      rw [map_mul, eval_latticeShape hk (LatticeNode.sum_toFinsupp_le _)
        (LatticeNode.sum_toFinsupp_le _), ite_eq_right, mul_zero]
      intro h
      exact hi (by rw [← e.apply_symm_apply i, LatticeNode.toFinsupp_injective k h])
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  have hr0 : r = 0 := eq_zero_of_eval_latticePoint hk hrdeg hrzero
  have hq' : q = ∑ i, C (eval (latticePoint k (e.symm i).toFinsupp) q)
      * latticeShape k (e.symm i).toFinsupp := by
    rw [← sub_eq_zero]
    exact hr0
  conv_rhs => rw [hq']
  rw [map_sum, Approximation.nodalInterp_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, eval_C, smul_eq_mul, mul_comm]
  rfl

/-- The composition of a polynomial $q$ in two variables with the affine parametrization
$s \mapsto (A_1 + B_1 s, A_2 + B_2 s)$ of a line, as a polynomial in $s$. -/
noncomputable def lineRestrict (q : MvPolynomial (Fin 2) ℝ) (A B : Fin 2 → ℝ) : Polynomial ℝ :=
  aeval (fun j ↦ Polynomial.C (A j) + Polynomial.C (B j) * Polynomial.X) q

/-- The restriction of $q$ to the line through $A$ with direction $B$, evaluated at $s$, is
$q(A + sB)$. -/
theorem eval_lineRestrict (q : MvPolynomial (Fin 2) ℝ) (A B : Fin 2 → ℝ) (s : ℝ) :
    (lineRestrict q A B).eval s = eval (fun j ↦ A j + B j * s) q := by
  rw [lineRestrict, ← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  simp only [map_add, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [MvPolynomial.aeval_eq_eval]

/-- The restriction of $q$ to a line has degree at most the total degree of $q$. -/
theorem natDegree_lineRestrict_le (q : MvPolynomial (Fin 2) ℝ) (A B : Fin 2 → ℝ) :
    (lineRestrict q A B).natDegree ≤ q.totalDegree := by
  rw [lineRestrict, aeval_def, eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd ↦ ?_
  rw [Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  have h1 : ∀ j : Fin 2,
      (Polynomial.C (A j) + Polynomial.C (B j) * Polynomial.X).natDegree ≤ 1 := fun j ↦
    Polynomial.natDegree_add_le_of_degree_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  refine (Finset.sum_le_sum fun j _ ↦ Polynomial.natDegree_pow_le.trans
    (Nat.mul_le_mul_left (d j) (h1 j))).trans ?_
  simp only [mul_one]
  have := le_totalDegree hd
  rwa [Finsupp.sum_fintype _ _ fun _ ↦ rfl] at this

/-- **The lattice nodes on an edge.** Let $k \ge 1$, let $\hat a$ and $\hat b$ be two vertices of
the reference triangle, and let $0 \le j \le k$. Then the point
$\hat a + (j/k)(\hat b - \hat a)$ is a node of the $\mathbb{P}_k$ Lagrange element. -/
theorem exists_node_eq_lineMap {k : ℕ} (hk : 0 < k) (a b : Fin 3) {j : ℕ} (hj : j ≤ k) :
    ∃ i, node k i = referenceTriangleVertex a
      + ((j : ℝ) / k) • (referenceTriangleVertex b - referenceTriangleVertex a) := by
  have hm : (k - j) * (if a = 1 then 1 else 0) + j * (if b = 1 then 1 else 0)
      + ((k - j) * (if a = 2 then 1 else 0) + j * (if b = 2 then 1 else 0)) ≤ k := by
    fin_cases a <;> fin_cases b <;> simp <;> omega
  refine ⟨Fintype.equivFin (LatticeNode k) (LatticeNode.mk' _ _ hm), ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkj : ((k - j : ℕ) : ℝ) = k - j := by rw [Nat.cast_sub hj]
  ext c
  rw [node_apply, Equiv.symm_apply_apply]
  fin_cases c
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [LatticeNode.toFinsupp_zero]
    simp only [LatticeNode.mk', PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul, hkj]
    fin_cases a <;> fin_cases b <;>
      simp [referenceTriangleVertex, sub_eq_add_neg, add_div, neg_div, hk.ne']
  · simp only [Fin.mk_one, Fin.isValue]
    rw [LatticeNode.toFinsupp_one]
    simp only [LatticeNode.mk', PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_mul, hkj]
    fin_cases a <;> fin_cases b <;>
      simp [referenceTriangleVertex, sub_eq_add_neg, add_div, neg_div, hk.ne']

/-- The local interpolant of the $\mathbb{P}_k$ Lagrange element on an element $K$ of a
triangulation, as a polynomial in the reference coordinates: $\sum_i v(F_K \hat x_i)\, L_i$,
where $F_K$ is the affine map from the reference triangle onto $K$. -/
noncomputable def localPoly {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ i, C (v (𝒯.linearPart T (node k i) + T.1 0))
    * latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp

/-- The local polynomial of the $\mathbb{P}_k$ Lagrange element has total degree at most $k$. -/
theorem totalDegree_localPoly_le {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ)
    (T : 𝒯.elems) (v : 𝔼₂ → ℝ) : (localPoly 𝒯 k T v).totalDegree ≤ k := by
  rw [← mem_restrictTotalDegree]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [C_mul']
  exact Submodule.smul_mem _ _ ((mem_restrictTotalDegree _ _ _).2
    (totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _)))

/-- The local interpolant of the $\mathbb{P}_k$ Lagrange element on an element $K$, at a point $y$,
is the local polynomial evaluated at $F_K^{-1}(y)$. -/
theorem localInterp_eq {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) (y : 𝔼₂) :
    𝒯.localInterp (node k) (shape k) T v y
      = eval (fun j ↦ ((𝒯.linearPart T).symm (y - T.1 0)) j) (localPoly 𝒯 k T v) := by
  rw [Triangulation.localInterp_apply, localPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, eval_C, mul_comm]
  rfl

/-- **The $\mathbb{P}_k$ Lagrange element is conforming.** Let $k \ge 1$ and let $\mathcal{T}$ be a
triangulation of an open set $\Omega \subseteq \mathbb{R}^2$. For every function $v$, the local
interpolants of $v$ on any two elements agree at every point common to the two closed elements.
This is Example 10.2.3 of [han2009theoretical], extended to every $k$; the source leaves the
case $k = 2$ to the reader as Exercise 10.2.4.

The statement is `Triangulation.IsConformingElement`. At a common vertex both interpolants take
the value of $v$, because a vertex is a lattice node. Along a common edge $[P, Q]$ both
interpolants restrict to polynomials of degree at most $k$ in the parameter $s$ of
$P + s(Q - P)$. These polynomials agree at the $k + 1$ lattice nodes $s = j/k$ of the edge,
which are nodes of both elements, hence everywhere. -/
theorem isConformingElement {k : ℕ} (hk : 0 < k) {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) :
    𝒯.IsConformingElement (node k) (shape k) := by
  intro v T T' x hx hx'
  dsimp only
  by_cases hTT' : T = T'
  · subst hTT'; rfl
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  -- the interpolant takes the value of `v` at the lattice nodes of every edge
  have hnode : ∀ (S : 𝒯.elems) (a b : Fin 3) {j : ℕ}, j ≤ k →
      𝒯.localInterp (node k) (shape k) S v
          (S.1 a + ((j : ℝ) / k) • (S.1 b - S.1 a))
        = v (S.1 a + ((j : ℝ) / k) • (S.1 b - S.1 a)) := by
    intro S a b j hj
    obtain ⟨i, hi⟩ := exists_node_eq_lineMap hk a b hj
    rw [← 𝒯.affine_vertex_lineMap S a b, ← hi]
    exact 𝒯.localInterp_apply_node _ _ (isNodalBasis hk) S v i
  rcases 𝒯.conforming' hTT' hx hx' with ⟨a, b, rfl, hab⟩ | ⟨a, b, a', b', -, ha, hb, hseg⟩
  · -- a common vertex
    have h0 : ∀ (S : 𝒯.elems) (c : Fin 3),
        S.1 c = S.1 c + (((0 : ℕ) : ℝ) / k) • (S.1 c - S.1 c) := by simp
    rw [h0 T a, hnode T a a (Nat.zero_le k), ← h0, hab, h0 T' b, hnode T' b b (Nat.zero_le k),
      ← h0]
  · -- a common edge
    rw [segment_eq_image'] at hseg
    obtain ⟨s, -, rfl⟩ := hseg
    -- the restrictions of the two interpolants to the edge are polynomials in `s`
    obtain ⟨A, hA⟩ : ∃ A : 𝒯.elems → Fin 2 → ℝ,
        ∀ S, A S = fun j ↦ ((𝒯.linearPart S).symm (T.1 a - S.1 0)) j := ⟨_, fun _ ↦ rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : 𝒯.elems → Fin 2 → ℝ, ∀ S, B S = fun j ↦
        ((𝒯.linearPart S).symm (T.1 b - S.1 0) - (𝒯.linearPart S).symm (T.1 a - S.1 0)) j :=
      ⟨_, fun _ ↦ rfl⟩
    have key : ∀ S : 𝒯.elems, ∀ t : ℝ,
        𝒯.localInterp (node k) (shape k) S v (T.1 a + t • (T.1 b - T.1 a))
          = (lineRestrict (localPoly 𝒯 k S v) (A S) (B S)).eval t := by
      intro S t
      rw [eval_lineRestrict, localInterp_eq, hA, hB]
      refine congrArg (fun g : Fin 2 → ℝ ↦ eval g (localPoly 𝒯 k S v)) (funext fun j ↦ ?_)
      have : (𝒯.linearPart S).symm (T.1 a + t • (T.1 b - T.1 a) - S.1 0)
          = (𝒯.linearPart S).symm (T.1 a - S.1 0)
            + t • ((𝒯.linearPart S).symm (T.1 b - S.1 0)
              - (𝒯.linearPart S).symm (T.1 a - S.1 0)) := by
        simp only [map_add, map_sub, map_smul]
        module
      rw [this]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mul_comm]
    -- they agree at the `k + 1` nodes `j / k` of the edge
    have hagree : ∀ y ∈ (Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k),
        (lineRestrict (localPoly 𝒯 k T v) (A T) (B T)).eval y
          = (lineRestrict (localPoly 𝒯 k T' v) (A T') (B T')).eval y := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [← key T, ← key T', hnode T a b hj', ha, hb, hnode T' a' b' hj']
    have hcard : ((Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k)).card = k + 1 := by
      rw [Finset.card_image_of_injective _ fun j₁ j₂ h ↦ ?_, Finset.card_range]
      exact_mod_cast (div_left_inj' hk').1 h
    have hdeg : ∀ S : 𝒯.elems, (lineRestrict (localPoly 𝒯 k S v) (A S) (B S)).degree
        < ((Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k)).card := by
      intro S
      rw [hcard]
      refine Polynomial.degree_le_natDegree.trans_lt ?_
      exact_mod_cast Nat.lt_succ_of_le
        ((natDegree_lineRestrict_le _ _ _).trans (totalDegree_localPoly_le 𝒯 k S v))
    rw [key T, key T', Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ (hdeg T) (hdeg T') hagree]

/-- Every shape function of the $\mathbb{P}_k$ Lagrange element is a polynomial of total degree at
most $k$: there is such a polynomial $q$ with $\varphi_i(x) = q(x)$ for all
$x \in \mathbb{R}^2$. -/
theorem shape_eq_eval (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) :
    ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧
      ∀ x : 𝔼₂, shape k i x = eval (fun j ↦ x j) q :=
  ⟨_, totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _), fun _ ↦ rfl⟩

/-- **The $\mathbb{P}_k$ Lagrange element is edge unisolvent.** Let $k \ge 1$, let
$\hat a \ne \hat b$ be two vertices of the reference triangle, and let $v$ vanish at every node
on the edge $[\hat a, \hat b]$. Then the interpolant
$\hat\Pi v = \sum_i v(\hat x_i)\, \hat\varphi_i$ vanishes on the whole edge.

The statement is `EuclideanSpace.IsEdgeUnisolvent`. Along the edge the interpolant is a
polynomial of degree at most $k$ in the parameter $s$ of $\hat a + s(\hat b - \hat a)$
(`LagrangeElement.lineRestrict`), and it vanishes at the $k + 1$ lattice nodes $s = j/k$ of the
edge, hence identically. This is the argument of `LagrangeElement.isConformingElement` with the
zero polynomial as the second interpolant. -/
theorem isEdgeUnisolvent {k : ℕ} (hk : 0 < k) :
    IsEdgeUnisolvent (node k) (shape k) := by
  intro a b hab v hv y hy
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [segment_eq_image'] at hy
  obtain ⟨s, -, rfl⟩ := hy
  -- the interpolant, as a polynomial in the reference coordinates
  obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Fin 2) ℝ, P = ∑ i, C (v (node k i))
      * latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp := ⟨_, rfl⟩
  have hPdeg : P.totalDegree ≤ k := by
    rw [hP, ← mem_restrictTotalDegree]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_restrictTotalDegree _ _ _).2
      (totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _)))
  have hPeval : ∀ z : 𝔼₂, Approximation.nodalInterp (node k) (shape k) v z
      = eval (fun j ↦ z j) P := by
    intro z
    rw [hP, map_sum, Approximation.nodalInterp_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, eval_C, smul_eq_mul, mul_comm]
    rfl
  -- its restriction to the edge, as a polynomial in the parameter
  obtain ⟨A, hA⟩ : ∃ A : Fin 2 → ℝ, A = fun j ↦ referenceTriangleVertex a j := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin 2 → ℝ,
      B = fun j ↦ (referenceTriangleVertex b - referenceTriangleVertex a) j := ⟨_, rfl⟩
  have key : ∀ t : ℝ, Approximation.nodalInterp (node k) (shape k) v
      (referenceTriangleVertex a + t • (referenceTriangleVertex b - referenceTriangleVertex a))
      = (lineRestrict P A B).eval t := by
    intro t
    rw [hPeval, eval_lineRestrict, hA, hB]
    refine congrArg (fun g : Fin 2 → ℝ ↦ eval g P) (funext fun j ↦ ?_)
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, mul_comm]
  -- it vanishes at the `k + 1` nodes `j / k` of the edge
  have hzero : ∀ t ∈ (Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k),
      (lineRestrict P A B).eval t = (0 : Polynomial ℝ).eval t := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
    have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨i, hi⟩ := exists_node_eq_lineMap hk a b hj'
    rw [← key, ← hi, (isNodalBasis hk).nodalInterp_apply_node, Polynomial.eval_zero]
    refine hv i ?_
    rw [hi, segment_eq_image']
    refine ⟨(j : ℝ) / k, ⟨by positivity, ?_⟩, rfl⟩
    rw [div_le_one (by exact_mod_cast hk)]
    exact_mod_cast hj'
  have hcard : ((Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k)).card = k + 1 := by
    rw [Finset.card_image_of_injective _ fun j₁ j₂ h ↦ ?_, Finset.card_range]
    exact_mod_cast (div_left_inj' hk').1 h
  have hdeg : (lineRestrict P A B).degree
      < ((Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k)).card := by
    rw [hcard]
    refine Polynomial.degree_le_natDegree.trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le ((natDegree_lineRestrict_le _ _ _).trans hPdeg)
  have hdeg0 : (0 : Polynomial ℝ).degree
      < ((Finset.range (k + 1)).image (fun j : ℕ ↦ (j : ℝ) / k)).card := by
    rw [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  rw [key, Polynomial.eq_of_degrees_lt_of_eval_finset_eq _ hdeg hdeg0 hzero, Polynomial.eval_zero]

end LatticeElement

end LagrangeElement
