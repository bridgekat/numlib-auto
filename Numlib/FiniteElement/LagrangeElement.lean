import Mathlib.LinearAlgebra.Lagrange
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Approximation.MvPolynomial
import Numlib.Geometry.Triangulation

/-!
# The `ℙ_k` Lagrange element on the principal lattice of a triangle

The Lagrange finite element of degree `k` on the reference triangle
`K̂ = {x̂₁, x̂₂ > 0, x̂₁ + x̂₂ < 1}`: its nodes are the points of the **principal lattice**

  `N̂_k = {(m₁/k, m₂/k) : m₁, m₂ ∈ ℕ, m₁ + m₂ ≤ k}`,

its local space is `ℙ_k`, the polynomials of total degree at most `k`, and its shape functions are
**Silvester's** nodal polynomials. The module proves what the finite element theory on a
triangulation (`Numlib/Geometry/Triangulation.lean`) asks of an element:

* **unisolvence** — a polynomial of total degree at most `k` is determined by its values on `N̂_k`
  (`bijective_latticeEval`, `eq_zero_of_eval_latticePoint`), so interpolation at the nodes
  reproduces `ℙ_k` (`nodalInterp_eval`);
* the shape functions are **nodal** (`isNodalBasis`), smooth (`contDiff_shape`) and polynomials of
  degree at most `k` (`shape_eq_eval`), and the nodes lie in the closed reference triangle
  (`node_mem_closure`);
* the element is **conforming** on every triangulation (`isConformingElement`): the local
  interpolants of two elements agree on their common edge, and **edge unisolvent**
  (`isEdgeUnisolvent`): an interpolant vanishing at the nodes of an edge vanishes on the edge.

## The proof of unisolvence

The nodal basis is exhibited explicitly. For a lattice point with barycentric multi-index
`α = (α₁, α₂, α₃)`, `Σ αᵢ = k`, the shape function is Silvester's product

  `L_α = ∏_c ∏_{r < α_c} (k λ_c − r) / (α_c − r)`

(`latticeShape`), of total degree `Σ_c α_c = k`, where the `λ_c` are the barycentric coordinates.
At the lattice point with multi-index `β` the scaled barycentric coordinate `k λ_c` takes the value
`β_c`, so `L_α` there is `∏_c ∏_{r < α_c} (β_c − r)/(α_c − r)`: it is `1` at `β = α`, and at any
other `β` some `β_c < α_c` — the two multi-indices have the same sum — so the factor `r = β_c`
vanishes (`eval_latticeShape`). That makes evaluation on the lattice *surjective*, and since `ℙ_k`
and the lattice have the same cardinality `C(k+2, 2)` — the lattice is indexed by the very
exponent vectors that index the monomial basis (`latticeIndex`) — surjective forces bijective. No
divisibility of a multivariate polynomial by an affine form is needed, and neither is the
induction on `k` of the classical argument.

Conformity and edge unisolvence are the same one-variable argument: along an edge
`P + s (Q − P)` an interpolant restricts to a polynomial of degree at most `k` in `s`
(`lineRestrict`), and the edge carries the `k + 1` lattice nodes `s = j/k`
(`exists_node_eq_lineMap`).

## Main definitions

* `LagrangeElement.latticePoint`, `latticeShape`, `latticeEval` — the principal lattice, Silvester's
  shape polynomials and the evaluation map on `ℙ_k`, in `MvPolynomial (Fin 2) ℝ`.
* `LagrangeElement.LatticeNode k` — the index type of the nodes.
* `LagrangeElement.node k`, `LagrangeElement.shape k` — the nodes and the shape functions of the
  element on `EuclideanSpace ℝ (Fin 2)`, in the form `Triangulation.localInterp` takes them.

## Main results

* `LagrangeElement.bijective_latticeEval` — unisolvence of `ℙ_k` on `N̂_k`.
* `LagrangeElement.nodalInterp_eval` — the interpolant reproduces `ℙ_k`.
* `LagrangeElement.isConformingElement`, `LagrangeElement.isEdgeUnisolvent`.

The interpolation error of the element on a regular family of triangulations is
`LagrangeElement.sobolevNorm_sub_globalInterp_le`
(`Numlib/FiniteElement/Interpolation.lean`).

## References

* [han2009theoretical] Proposition 10.2.1 (unisolvence, quoted there without proof), (10.2.24)
  (the principal lattice), Example 10.2.3 and Exercise 10.2.4 (conformity).
-/

namespace LagrangeElement

section PrincipalLattice

open Finset Module MvPolynomial

/-- The **Lagrange factor** `∏_{r < a} (ℓ − r)/(a − r)` of an affine form `ℓ`: it is `1` where
`ℓ = a` and `0` where `ℓ` takes a natural value smaller than `a`, and its total degree is at
most `a`. -/
noncomputable def lagFactor (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ r ∈ Finset.range a, C ((a : ℝ) - r)⁻¹ * (ℓ - C (r : ℝ))

/-- A Lagrange factor of an affine form has total degree at most its index. -/
theorem totalDegree_lagFactor_le {ℓ : MvPolynomial (Fin 2) ℝ} (hℓ : ℓ.totalDegree ≤ 1) (a : ℕ) :
    (lagFactor ℓ a).totalDegree ≤ a := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1) fun r _ => ?_) (by simp)
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  exact le_trans (totalDegree_sub_C_le _ _) hℓ

/-- The value of a Lagrange factor: `∏_{r < a} (ℓ(x) − r)/(a − r)`. -/
theorem eval_lagFactor (x : Fin 2 → ℝ) (ℓ : MvPolynomial (Fin 2) ℝ) (a : ℕ) :
    eval x (lagFactor ℓ a) = ∏ r ∈ Finset.range a, ((a : ℝ) - r)⁻¹ * (eval x ℓ - r) := by
  simp [lagFactor]

/-- The Lagrange factor is `1` where its form takes the value `a`: every factor is `(a − r)/(a − r)`
and `r < a`. -/
theorem eval_lagFactor_self {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a : ℕ}
    (h : eval x ℓ = (a : ℝ)) : eval x (lagFactor ℓ a) = 1 := by
  rw [eval_lagFactor, h]
  refine Finset.prod_eq_one fun r hr => ?_
  have hne : ((a : ℝ) - r) ≠ 0 := by
    have : (r : ℝ) < a := by exact_mod_cast Finset.mem_range.mp hr
    linarith
  field_simp

/-- The Lagrange factor vanishes where its form takes a natural value below `a`: the factor with
`r = b` is zero. -/
theorem eval_lagFactor_of_lt {x : Fin 2 → ℝ} {ℓ : MvPolynomial (Fin 2) ℝ} {a b : ℕ} (hb : b < a)
    (h : eval x ℓ = (b : ℝ)) : eval x (lagFactor ℓ a) = 0 := by
  rw [eval_lagFactor, h]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hb) (by simp)

/-- The three barycentric coordinates `λ̂₁ = 1 − x̂₁ − x̂₂`, `λ̂₂ = x̂₁` and `λ̂₃ = x̂₂` of the
reference triangle, scaled by `k`, so that each takes an integer value at every point of
`N̂_k`. -/
noncomputable def scaledBary (k : ℕ) : Fin 3 → MvPolynomial (Fin 2) ℝ :=
  ![C (k : ℝ) * (1 - X 0 - X 1), C (k : ℝ) * X 0, C (k : ℝ) * X 1]

/-- The scaled barycentric coordinates are affine. -/
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

/-- The point `(m₁/k, m₂/k)` of the **principal lattice** `N̂_k` of the reference triangle. As `m`
ranges over the exponent vectors with `m₁ + m₂ ≤ k` this is exactly
`N̂_k = {Σ tᵢ âᵢ : Σ tᵢ = 1, tᵢ ∈ {0, 1/k, …, 1}}` of [han2009theoretical] (10.2.24). -/
noncomputable def latticePoint (k : ℕ) (m : Fin 2 →₀ ℕ) (i : Fin 2) : ℝ := (m i : ℝ) / k

/-- The barycentric multi-index `(k − m₁ − m₂, m₁, m₂)` of a lattice point: the values of the
scaled barycentric coordinates there. -/
def latticeMulti (k : ℕ) (m : Fin 2 →₀ ℕ) : Fin 3 → ℕ := ![k - m 0 - m 1, m 0, m 1]

/-- The barycentric multi-index of a lattice point sums to `k`. -/
theorem sum_latticeMulti {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    ∑ c, latticeMulti k m c = k := by
  simp only [Fin.sum_univ_three, latticeMulti, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  omega

/-- At a lattice point the scaled barycentric coordinates take the values of its multi-index. -/
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

/-- **Silvester's shape function** of the principal lattice at the point with exponent vector `m`:
the product over the three barycentric coordinates of the Lagrange factors of their multi-index
entries. -/
noncomputable def latticeShape (k : ℕ) (m : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∏ c, lagFactor (scaledBary k c) (latticeMulti k m c)

/-- The shape functions lie in `ℙ_k`: the three multi-index entries sum to `k`. -/
theorem totalDegree_latticeShape_le {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    (latticeShape k m).totalDegree ≤ k := by
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun c _ =>
    totalDegree_lagFactor_le (totalDegree_scaledBary_le k c) _) ?_
  exact le_of_eq (sum_latticeMulti hm)

/-- Two distinct lattice points have multi-indices of the same sum, so one entry of the second is
strictly below the corresponding entry of the first. This is what makes a shape function vanish at
every node but its own. -/
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

/-- **The shape functions are dual to the lattice points**: `L_m(x_{m'}) = δ_{m m'}`. -/
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

/-- The index set of the principal lattice `N̂_k`, which is also the index set of the monomial basis
of `ℙ_k`: the exponent vectors of total degree at most `k`. Indexing the nodes and the monomials by
one type is what makes the two cardinalities agree without a separate count. -/
def latticeIndex (k : ℕ) : Set (Fin 2 →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ k}

/-- Membership of the lattice index set: `m₀ + m₁ ≤ k`. -/
theorem mem_latticeIndex_iff {k : ℕ} {m : Fin 2 →₀ ℕ} :
    m ∈ latticeIndex k ↔ m 0 + m 1 ≤ k := by
  change (m.sum fun _ e => e) ≤ k ↔ _
  rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fin.sum_univ_two]

/-- The interpolation map of the principal lattice: evaluation of a polynomial of total degree at
most `k` at the points of `N̂_k`. -/
noncomputable def latticeEval (k : ℕ) :
    (MvPolynomial.restrictTotalDegree (Fin 2) ℝ k) →ₗ[ℝ] (latticeIndex k → ℝ) where
  toFun p m := eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ)
  map_add' p q := by ext m; simp
  map_smul' a p := by ext m; simp

@[simp]
theorem latticeEval_apply (k : ℕ) (p : MvPolynomial.restrictTotalDegree (Fin 2) ℝ k)
    (m : latticeIndex k) :
    latticeEval k p m = eval (latticePoint k (m : Fin 2 →₀ ℕ)) (p : MvPolynomial (Fin 2) ℝ) := rfl

/-- **Unisolvence of `ℙ_k` on the principal lattice**: a polynomial of total degree at most `k`
on a triangle is uniquely
determined by its values at the `(k+1)(k+2)/2` points of the principal lattice `N̂_k` — that is,
the interpolation problem there is unisolvent.

The surjectivity is Silvester's shape functions `latticeShape`, which are dual to the nodes by
`eval_latticeShape`; the injectivity then follows because `ℙ_k` and the lattice both have
`C(k + 2, 2)` elements, the lattice by construction, since it is indexed by the very exponent
vectors that index the monomial basis. [han2009theoretical] Proposition 10.2.1, quoted there
without proof. -/
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

/-- **Unisolvence**, in the form the finite element proofs use it: a polynomial of total degree
at most `k` vanishing at every point of the principal lattice is the zero polynomial
([han2009theoretical] Proposition 10.2.1). -/
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

/-- The index type of the nodes of the principal lattice `N̂_k`: the pairs `(m₀, m₁)` of naturals
with `m₀ + m₁ ≤ k`. -/
def LatticeNode (k : ℕ) : Type := {p : Fin (k + 1) × Fin (k + 1) // (p.1 : ℕ) + p.2 ≤ k}

/-- The nodes of the principal lattice are finitely many. -/
instance (k : ℕ) : Fintype (LatticeNode k) := Subtype.fintype _

/-- The exponent vector `(m₀, m₁)` of a lattice node, as the `Fin 2 →₀ ℕ` that indexes
`latticePoint` and `latticeShape`. -/
noncomputable def LatticeNode.toFinsupp {k : ℕ} (p : LatticeNode k) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (p.1.1 : ℕ) + Finsupp.single 1 (p.1.2 : ℕ)

/-- The first entry of the exponent vector of a lattice node. -/
@[simp]
theorem LatticeNode.toFinsupp_zero {k : ℕ} (p : LatticeNode k) : p.toFinsupp 0 = p.1.1 := by
  simp [LatticeNode.toFinsupp]

/-- The second entry of the exponent vector of a lattice node. -/
@[simp]
theorem LatticeNode.toFinsupp_one {k : ℕ} (p : LatticeNode k) : p.toFinsupp 1 = p.1.2 := by
  simp [LatticeNode.toFinsupp]

/-- The exponent vector of a lattice node has entries summing to at most `k`. -/
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

/-- Every exponent vector with `m₀ + m₁ ≤ k` is the exponent vector of a lattice node. -/
theorem LatticeNode.exists_toFinsupp_eq {k : ℕ} {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 ≤ k) :
    ∃ p : LatticeNode k, p.toFinsupp = m :=
  ⟨⟨(⟨m 0, by omega⟩, ⟨m 1, by omega⟩), hm⟩, by
    ext i
    fin_cases i <;> simp [LatticeNode.toFinsupp]⟩

/-- The lattice node with exponent vector `(m₀, m₁)`, given by two naturals with `m₀ + m₁ ≤ k`. -/
def LatticeNode.mk' {k : ℕ} (m₀ m₁ : ℕ) (h : m₀ + m₁ ≤ k) : LatticeNode k :=
  ⟨(⟨m₀, by omega⟩, ⟨m₁, by omega⟩), h⟩

/-- **The nodes of the `ℙ_k` Lagrange element** on the reference triangle: the points of the
principal lattice `N̂_k` ([han2009theoretical] (10.2.24)), as points of
`EuclideanSpace ℝ (Fin 2)`, indexed by
`Fin (card (LatticeNode k))`. -/
noncomputable def node (k : ℕ) : Fin (Fintype.card (LatticeNode k)) → 𝔼₂ := fun i ↦
  WithLp.toLp 2 (latticePoint k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp)

/-- **The shape functions of the `ℙ_k` Lagrange element**: Silvester's `latticeShape`, as
functions on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def shape (k : ℕ) : Fin (Fintype.card (LatticeNode k)) → 𝔼₂ → ℝ :=
  fun i x ↦
    eval (fun j ↦ x j) (latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp)

/-- The coordinates of a lattice node: `(m₀ / k, m₁ / k)`. -/
theorem node_apply (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) (j : Fin 2) :
    node k i j
      = (((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp j : ℝ) / k := rfl

/-- The shape functions of the lattice element are nodal for its nodes (the duality
`L_m(x_{m'}) = δ_{m m'}` of `eval_latticeShape`). -/
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

/-- The lattice nodes lie in the closed reference triangle. -/
theorem node_mem_closure {k : ℕ} (hk : 0 < k) (i : Fin (Fintype.card (LatticeNode k))) :
    node k i ∈ closure (referenceTriangle : Set 𝔼₂) := by
  refine mem_closure_referenceTriangle ?_
  simp only [node_apply]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := LatticeNode.sum_toFinsupp_le ((Fintype.equivFin (LatticeNode k)).symm i)
  refine ⟨by positivity, by positivity, ?_⟩
  rw [← add_div, div_le_one hk']
  exact_mod_cast h

/-- The shape functions of the lattice element are smooth. -/
theorem contDiff_shape (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (shape k i) := by
  have : shape k i = evalBasis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp) := by
    funext x
    exact (MvPolynomial.evalBasis_basisFun _ x).symm
  rw [this]
  exact MvPolynomial.contDiff_evalBasis _ _

/-- **`ℙ_k` interpolation on the principal lattice reproduces `ℙ_k`** (unisolvence in the form of
the polynomial invariance [han2009theoretical] (10.3.4)): interpolating a polynomial of total
degree at most `k` at the lattice nodes with the shape functions `latticeShape` gives it back —
their difference is a polynomial of degree at most `k` vanishing at every lattice node, hence
zero. -/
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

/-- The composition of a polynomial in two variables with an affine parametrization
`s ↦ (A₀ + B₀ s, A₁ + B₁ s)` of a line, as a polynomial in `s`. -/
noncomputable def lineRestrict (q : MvPolynomial (Fin 2) ℝ) (A B : Fin 2 → ℝ) : Polynomial ℝ :=
  aeval (fun j ↦ Polynomial.C (A j) + Polynomial.C (B j) * Polynomial.X) q

/-- The restriction to a line evaluates as the polynomial does along the line. -/
theorem eval_lineRestrict (q : MvPolynomial (Fin 2) ℝ) (A B : Fin 2 → ℝ) (s : ℝ) :
    (lineRestrict q A B).eval s = eval (fun j ↦ A j + B j * s) q := by
  rw [lineRestrict, ← Polynomial.coe_aeval_eq_eval, comp_aeval_apply]
  simp only [map_add, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [MvPolynomial.aeval_eq_eval]

/-- The restriction to a line of a polynomial of total degree at most `k` has degree at most
`k`. -/
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

/-- **The lattice nodes on an edge**: the point `x̂_a + (j/k)(x̂_b − x̂_a)` of the segment from
the vertex `a` to the vertex `b` of the reference triangle, `0 ≤ j ≤ k`, is a lattice node. -/
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

/-- The local interpolant of the lattice element on an element, as a polynomial in the reference
coordinates: `∑ᵢ v(F_K x̂ᵢ) L_i`. -/
noncomputable def localPoly {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ i, C (v (𝒯.linearPart T (node k i) + T.1 0))
    * latticeShape k ((Fintype.equivFin (LatticeNode k)).symm i).toFinsupp

/-- The local polynomial of the lattice element has total degree at most `k`. -/
theorem totalDegree_localPoly_le {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ)
    (T : 𝒯.elems) (v : 𝔼₂ → ℝ) : (localPoly 𝒯 k T v).totalDegree ≤ k := by
  rw [← mem_restrictTotalDegree]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [C_mul']
  exact Submodule.smul_mem _ _ ((mem_restrictTotalDegree _ _ _).2
    (totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _)))

/-- The local interpolant of the lattice element is its local polynomial read through
`F_K⁻¹`. -/
theorem localInterp_eq {Ω : Opens 𝔼₂} (𝒯 : Triangulation Ω) (k : ℕ) (T : 𝒯.elems)
    (v : 𝔼₂ → ℝ) (y : 𝔼₂) :
    𝒯.localInterp (node k) (shape k) T v y
      = eval (fun j ↦ ((𝒯.linearPart T).symm (y - T.1 0)) j) (localPoly 𝒯 k T v) := by
  rw [Triangulation.localInterp_apply, localPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, eval_C, mul_comm]
  rfl

/-- **The `ℙ_k` Lagrange element on the principal lattice is conforming** ([han2009theoretical]
Example 10.2.3 extended to every `k`, which the book leaves to the reader for `k = 2`, its Exercise
10.2.4):
the local interpolants of two elements agree at every point of a common closed element. At a
common vertex both take the value of `v` (a vertex is a lattice node). Along a common edge
`[P, Q]` both restrict to polynomials of degree at most `k` in the parameter `s` of
`P + s (Q − P)`, which agree at the `k + 1` lattice nodes `s = j/k` of the edge — these are nodes
of both elements, where each interpolant takes the value of `v` — hence everywhere. -/
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

/-- The shape functions of the `ℙ_k` Lagrange element are polynomials of total degree at most
`k` (Silvester's `latticeShape`). -/
theorem shape_eq_eval (k : ℕ) (i : Fin (Fintype.card (LatticeNode k))) :
    ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k ∧
      ∀ x : 𝔼₂, shape k i x = eval (fun j ↦ x j) q :=
  ⟨_, totalDegree_latticeShape_le (LatticeNode.sum_toFinsupp_le _), fun _ ↦ rfl⟩

/-- **The `ℙ_k` Lagrange element on the principal lattice is edge unisolvent**: along a
reference edge `[x̂_a, x̂_b]`, the interpolant `Π̂ v` is a polynomial of degree at most `k` in the
parameter `s` of `x̂_a + s (x̂_b − x̂_a)` (`lineRestrict`), and it vanishes at the `k + 1` lattice
nodes `s = j/k` of the edge when `v` does — there `Π̂ v = v` — hence identically. This is the
argument of `isConformingElement` with the zero polynomial as the second interpolant. -/
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
