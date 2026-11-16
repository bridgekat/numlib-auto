/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.PiL2`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Concatenation of coordinates: $\mathbb{R}^m \times \mathbb{R}^n$ and $\mathbb{R}^{m+n}$

The spaces $\mathbb{R}^m \times \mathbb{R}^n$ and $\mathbb{R}^{m+n}$ are different types in Lean
(`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (m + n))`), and a
text written in $\mathbb{R}^n$ identifies them without comment. This module gives the
identification: the concatenation
$$(x, y) \mapsto (x_1, \dots, x_m, y_1, \dots, y_n)$$
as a linear homeomorphism, its coordinates, and its one mathematical property, which is that it adds
the two inner products: $\langle (x, y), (x', y') \rangle = \langle x, x' \rangle + \langle y, y'
\rangle$. A concatenation $\mathbb{R} \times \mathbb{R}^n \times \mathbb{R} \cong \mathbb{R}^{n+2}$
with a scalar factor at each end is assembled from it.

Nothing here is about convexity. The facts that a convexity statement needs in addition, namely that
the concatenation is an adjoint pair for the two pairings and the transport of conjugate functions,
subdifferentials and relative interiors along it, are in `Numlib.Analysis.Convex.EuclideanProd`.

## Main definitions

* `euclideanProdIsometry`: the concatenation as a linear isometry from `WithLp 2 (ℝᵐ × ℝⁿ)` onto
  $\mathbb{R}^{m+n}$.
* `euclideanProdEquiv`: the same map on the plain product, as a continuous linear equivalence
  $\mathbb{R}^m \times \mathbb{R}^n \cong \mathbb{R}^{m+n}$.
* `euclideanOne`: the identification of $\mathbb{R}$ with the one-dimensional Euclidean space
  $\mathbb{R}^1$.
* `euclideanTripleEquiv`: the concatenation $\mathbb{R} \times \mathbb{R}^n \times \mathbb{R} \cong
  \mathbb{R}^{n+2}$, which is what a text means by $(\lambda, x, \mu) \in \mathbb{R}^{n+2}$.

## Main results

* `inner_euclideanProdEquiv`: the concatenation adds the two inner products. The lemma
  `euclideanProdEquiv_apply_castAdd` and the lemmas after it give the coordinates.
* `inner_euclideanTripleEquiv` and `closure_image_euclideanTripleEquiv`: the triple concatenation
  carries the inner product of $\mathbb{R}^{n+2}$ to $\lambda \lambda' + \langle x, x' \rangle + \mu
  \mu'$, and it commutes with the closure. This is all that a user needs; which index of
  `Fin (n + 2)` carries $\lambda$ is a detail of the construction.

## Implementation notes

* The isometry is defined on `WithLp 2 (ℝᵐ × ℝⁿ)` because the norm of Mathlib on a product is the
  supremum norm. All other statements are for the plain product. Its linear structure and its
  topology are all that the transports in other modules need, so that no user has to move a `Convex`
  or an `IsClosed` across a type synonym. The lemma `euclideanProdEquiv_eq_isometry` records that
  the two maps agree.
-/

open Set

/-! ### The concatenation -/

section Defs

variable (m n : ℕ)

/-- The **concatenation of coordinates** $(x, y) \mapsto (x_1, \dots, x_m, y_1, \dots, y_n)$, as a
linear isometry from $\mathbb{R}^m \times \mathbb{R}^n$ with the Euclidean norm
$\sqrt{\|x\|^2 + \|y\|^2}$ onto $\mathbb{R}^{m+n}$.

The domain is `WithLp 2 (ℝᵐ × ℝⁿ)`: the norm of Mathlib on a product is the supremum norm, and
the concatenation is an isometry only for the Euclidean norm. -/
noncomputable def euclideanProdIsometry :
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

/-- The **concatenation of coordinates** $(x, y) \mapsto (x_1, \dots, x_m, y_1, \dots, y_n)$ on the
plain product $\mathbb{R}^m \times \mathbb{R}^n$, as a continuous linear equivalence onto
$\mathbb{R}^{m+n}$.

The plain product carries the supremum norm, so the map is not an isometry. It is still a linear
homeomorphism, which is all that the transports need. -/
noncomputable def euclideanProdEquiv :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin n))).symm.trans (euclideanProdIsometry m n).toContinuousLinearEquiv

variable {m n}

/-- The concatenation `euclideanProdEquiv` on the plain product agrees with the isometry
`euclideanProdIsometry` on `WithLp 2 (ℝᵐ × ℝⁿ)`. -/
theorem euclideanProdEquiv_eq_isometry
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    euclideanProdEquiv m n p = euclideanProdIsometry m n (WithLp.toLp 2 p) := rfl

/-- The first $m$ coordinates of the concatenation of $(x, y) \in \mathbb{R}^m \times \mathbb{R}^n$
are those of $x$: the coordinate with index $i$ of the concatenation is $x_i$ for $i < m$.

The index $i \in \{0, \dots, m - 1\}$ of $\mathbb{R}^{m+n}$ is `Fin.castAdd n i`. -/
@[simp] theorem euclideanProdEquiv_apply_castAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    euclideanProdEquiv m n p (Fin.castAdd n i) = p.1 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

/-- The last $n$ coordinates of the concatenation of $(x, y) \in \mathbb{R}^m \times \mathbb{R}^n$
are those of $y$: the coordinate with index $m + i$ of the concatenation is $y_i$ for $i < n$.

The index $m + i$ of $\mathbb{R}^{m+n}$ is `Fin.natAdd m i`. -/
@[simp] theorem euclideanProdEquiv_apply_natAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanProdEquiv m n p (Fin.natAdd m i) = p.2 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

/-- The inverse of the concatenation splits $z \in \mathbb{R}^{m+n}$ into its first $m$ and its last
$n$ coordinates: $z \mapsto ((z_0, \dots, z_{m-1}), (z_m, \dots, z_{m+n-1}))$. -/
theorem euclideanProdEquiv_symm_apply (z : EuclideanSpace ℝ (Fin (m + n))) :
    (euclideanProdEquiv m n).symm z =
      (WithLp.toLp 2 fun i => z (Fin.castAdd n i), WithLp.toLp 2 fun i => z (Fin.natAdd m i)) := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

/-- The first component of the inverse concatenation of $z \in \mathbb{R}^{m+n}$ has coordinate
$z_i$ at index $i < m$. -/
@[simp] theorem euclideanProdEquiv_symm_apply_fst (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin m) : ((euclideanProdEquiv m n).symm z).1 i = z (Fin.castAdd n i) := by
  rw [euclideanProdEquiv_symm_apply]

/-- The second component of the inverse concatenation of $z \in \mathbb{R}^{m+n}$ has coordinate
$z_{m+i}$ at index $i < n$. -/
@[simp] theorem euclideanProdEquiv_symm_apply_snd (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin n) : ((euclideanProdEquiv m n).symm z).2 i = z (Fin.natAdd m i) := by
  rw [euclideanProdEquiv_symm_apply]

/-- **The concatenation adds the two inner products.** For $p = (x, y)$ and $q = (x', y')$ in
$\mathbb{R}^m \times \mathbb{R}^n$, the inner product of their concatenations in
$\mathbb{R}^{m+n}$ is
$$\langle x, x' \rangle + \langle y, y' \rangle.$$
So the pairing on the product is the inner product of $\mathbb{R}^{m+n}$ read through the
concatenation. -/
theorem inner_euclideanProdEquiv
    (p q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) : ℝ)
      = inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_add]

/-- For $C \subseteq \mathbb{R}^m \times \mathbb{R}^n$, the closure of the image of $C$ under the
concatenation is the image of the closure of $C$, because the concatenation is a homeomorphism. -/
theorem closure_image_euclideanProdEquiv
    (C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    closure (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' closure C :=
  ((euclideanProdEquiv m n).toHomeomorph.image_closure C).symm

end Defs

/-!
### The one-dimensional factor and the triple concatenation

This section identifies $\mathbb{R} \times \mathbb{R}^n \times \mathbb{R}$ with $\mathbb{R}^{n+2}$.
The type `ℝ` is not `EuclideanSpace ℝ (Fin 1)`, so a concatenation with a scalar factor at each end
needs one more identification at the start and one at the end.
-/

section Triple

/-- The identification of $\mathbb{R}$ with the one-dimensional Euclidean space $\mathbb{R}^1$,
$a \mapsto (a)$, as a continuous linear equivalence. -/
noncomputable def euclideanOne : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 => ℝ).symm

/-- The only coordinate of `euclideanOne a` is $a$. -/
@[simp] theorem euclideanOne_apply (a : ℝ) (i : Fin 1) : euclideanOne a i = a := by
  fin_cases i
  rfl

/-- The identification of $\mathbb{R}$ with $\mathbb{R}^1$ preserves the inner product: the inner
product of $(a)$ and $(b)$ in $\mathbb{R}^1$ is $ab$. -/
theorem inner_euclideanOne (a b : ℝ) :
    (inner ℝ (euclideanOne a) (euclideanOne b) : ℝ) = a * b := by
  simp [PiLp.inner_apply, mul_comm]

/-- For $d \in \mathbb{R}^1$, $\|d\| = |d_0|$. -/
theorem EuclideanSpace.norm_eq_abs_fin_one (d : EuclideanSpace ℝ (Fin 1)) : ‖d‖ = |d 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- Let $A$ be a continuous $k$-linear form on $\mathbb{R}^1$, and let $e = (1)$ be the unit vector
of $\mathbb{R}^1$. Then $\|A\| \le |A(e, \dots, e)|$. -/
theorem EuclideanSpace.norm_multilinear_fin_one_le {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin 1)) ℝ) :
    ‖A‖ ≤ |A (fun _ => EuclideanSpace.single 0 1)| := by
  refine ContinuousMultilinearMap.opNorm_le_bound (abs_nonneg _) fun v => ?_
  have hv : v = fun i => v i 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    funext i; ext l; fin_cases l; simp
  rw [hv, A.map_smul_univ]
  simp only [smul_eq_mul, norm_mul, Real.norm_eq_abs, Finset.abs_prod,
    EuclideanSpace.norm_eq_abs_fin_one]
  simp [mul_comm]

/-- Let $L$ be a continuous linear form on $\mathbb{R}^1$, and let $e = (1)$ be the unit vector of
$\mathbb{R}^1$. Then $\|L\| \le |L e|$. -/
theorem EuclideanSpace.norm_clm_fin_one_le (L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (EuclideanSpace.single 0 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun v => ?_
  have hv : v = v 0 • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    ext l; fin_cases l; simp
  rw [hv, L.map_smul]
  simp only [smul_eq_mul, norm_mul, Real.norm_eq_abs, EuclideanSpace.norm_eq_abs_fin_one]
  simp [mul_comm]

variable (n : ℕ)

/-- The **concatenation** $(\lambda, x, \mu) \mapsto (\lambda, x_1, \dots, x_n, \mu)$ from
$\mathbb{R} \times \mathbb{R}^n \times \mathbb{R}$ onto $\mathbb{R}^{n+2}$, as a continuous
linear equivalence.

Its effect on the inner product is `inner_euclideanTripleEquiv`. The domain is the Lean type
`(ℝ × EuclideanSpace ℝ (Fin n)) × ℝ`. -/
noncomputable def euclideanTripleEquiv :
    ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  ((euclideanOne.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))).prodCongr
      euclideanOne).trans <|
    ((euclideanProdEquiv 1 n).prodCongr
        (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)))).trans <|
      (euclideanProdEquiv (1 + n) 1).trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (by omega : 1 + n + 1 = n + 2))).toContinuousLinearEquiv

variable {n}

/-- **The triple concatenation adds the three inner products.** For $p = (\lambda, x, \mu)$ and
$q = (\lambda', x', \mu')$ in $\mathbb{R} \times \mathbb{R}^n \times \mathbb{R}$, the inner
product of their concatenations in $\mathbb{R}^{n+2}$ is
$$\lambda \lambda' + \langle x, x' \rangle + \mu \mu'.$$
-/
theorem inner_euclideanTripleEquiv (p q : (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) :
    (inner ℝ (euclideanTripleEquiv n p) (euclideanTripleEquiv n q) : ℝ)
      = p.1.1 * q.1.1 + inner ℝ p.1.2 q.1.2 + p.2 * q.2 := by
  simp only [euclideanTripleEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl',
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, id_eq]
  rw [LinearIsometryEquiv.inner_map_map, inner_euclideanProdEquiv, inner_euclideanProdEquiv,
    inner_euclideanOne, inner_euclideanOne]

/-- For $S \subseteq \mathbb{R} \times \mathbb{R}^n \times \mathbb{R}$, the closure of the image of
$S$ under the triple concatenation is the image of the closure of $S$, because the concatenation
is a homeomorphism. -/
theorem closure_image_euclideanTripleEquiv (S : Set ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ)) :
    closure (euclideanTripleEquiv n '' S) = euclideanTripleEquiv n '' closure S :=
  ((euclideanTripleEquiv n).toHomeomorph.image_closure S).symm

end Triple
