/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.PiL2`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concatenating coordinates: `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ`

`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (m + n))` are
different types, and a text written in `ℝⁿ` moves between them without comment. This module is that
move: the concatenation `(x, y) ↦ (x₁, …, x_m, y₁, …, y_n)` as a linear homeomorphism, its
coordinates, and its one mathematical property — that it *adds the two inner products*. A
concatenation with a scalar factor at each end, `ℝ × ℝⁿ × ℝ ≃ ℝⁿ⁺²`, is assembled from it.

Nothing here is about convexity. What a convexity statement needs on top of this — that the
concatenation is an adjoint pair for the two pairings, and the transport of `convexConj`,
`subdifferential` and `ri` along it — is `Numlib/Analysis/Convex/EuclideanProd`, which is where the
one consumer of this module reaches it from.

## Main definitions

* `euclideanProdIsometry m n` — the concatenation as a linear isometry
  `WithLp 2 (ℝᵐ × ℝⁿ) ≃ₗᵢ[ℝ] ℝᵐ⁺ⁿ`.
* `euclideanProdEquiv m n` — the same map out of the plain product, `ℝᵐ × ℝⁿ ≃L[ℝ] ℝᵐ⁺ⁿ`.
* `euclideanOne` — `ℝ ≃L[ℝ] ℝ¹`, the scalar read as a one-dimensional Euclidean space.
* `euclideanTripleEquiv n` — `ℝ × ℝⁿ × ℝ ≃L[ℝ] ℝⁿ⁺²`, what a text means by `(λ, x, μ) ∈ ℝⁿ⁺²`.

## Main results

* `inner_euclideanProdEquiv` — concatenation adds the two inner products;
  `euclideanProdEquiv_apply_castAdd` and friends give the coordinates.
* `inner_euclideanTripleEquiv`, `closure_image_euclideanTripleEquiv` — the triple concatenation
  carries the inner product of `ℝⁿ⁺²` to `λ λ* + ⟨x, y⟩ + μ μ*` and commutes with the closure. That
  is all a consumer needs: which `Fin (n + 2)` index carries `λ` is an artefact of the assembly.

## Implementation notes

The isometry is out of `WithLp 2 (ℝᵐ × ℝⁿ)` because Mathlib's norm on a product is the *supremum*
norm. Everything else is stated for the plain product, whose linear structure and topology are all
that the transports downstream need, so that no consumer has to move a `Convex` or an `IsClosed`
across a type synonym; `euclideanProdEquiv_eq_isometry` records that the two agree.
-/

open Set

/-! ### The concatenation -/

section Defs

variable (m n : ℕ)

/-- **Concatenation of coordinates**, `(x, y) ↦ (x₁, …, x_m, y₁, …, y_n)`, as a linear isometry out
of `WithLp 2 (ℝᵐ × ℝⁿ)`: Mathlib's product norm is the supremum norm, and concatenation is an
isometry only for the Euclidean one. -/
noncomputable def euclideanProdIsometry :
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv)

/-- **Concatenation of coordinates** out of the plain product, which carries the supremum norm. No
longer an isometry, but still a linear homeomorphism, which is all the transports below need. -/
noncomputable def euclideanProdEquiv :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin n))).symm.trans (euclideanProdIsometry m n).toContinuousLinearEquiv

variable {m n}

/-- The two concatenations are the same map. -/
theorem euclideanProdEquiv_eq_isometry
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    euclideanProdEquiv m n p = euclideanProdIsometry m n (WithLp.toLp 2 p) := rfl

@[simp] theorem euclideanProdEquiv_apply_castAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    euclideanProdEquiv m n p (Fin.castAdd n i) = p.1 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

@[simp] theorem euclideanProdEquiv_apply_natAdd
    (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanProdEquiv m n p (Fin.natAdd m i) = p.2 i := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

theorem euclideanProdEquiv_symm_apply (z : EuclideanSpace ℝ (Fin (m + n))) :
    (euclideanProdEquiv m n).symm z =
      (WithLp.toLp 2 fun i => z (Fin.castAdd n i), WithLp.toLp 2 fun i => z (Fin.natAdd m i)) := by
  simp [euclideanProdEquiv, euclideanProdIsometry, Equiv.piCongrLeft']

@[simp] theorem euclideanProdEquiv_symm_apply_fst (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin m) : ((euclideanProdEquiv m n).symm z).1 i = z (Fin.castAdd n i) := by
  rw [euclideanProdEquiv_symm_apply]

@[simp] theorem euclideanProdEquiv_symm_apply_snd (z : EuclideanSpace ℝ (Fin (m + n)))
    (i : Fin n) : ((euclideanProdEquiv m n).symm z).2 i = z (Fin.natAdd m i) := by
  rw [euclideanProdEquiv_symm_apply]

/-- **Concatenation adds the two inner products.** So the form a product is paired with is the
inner product of `ℝᵐ⁺ⁿ` read through the concatenation. -/
theorem inner_euclideanProdEquiv
    (p q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) : ℝ)
      = inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_add]

/-- The closure transports along the concatenation, because it is a homeomorphism. -/
theorem closure_image_euclideanProdEquiv
    (C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    closure (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' closure C :=
  ((euclideanProdEquiv m n).toHomeomorph.image_closure C).symm

end Defs

/-! ### The one-dimensional factor, and `ℝ × ℝⁿ × ℝ` as `ℝⁿ⁺²`

`ℝ` is not `EuclideanSpace ℝ (Fin 1)`, so a concatenation with a scalar factor at each end needs one
more transport prepended and one appended. -/

section Triple

/-- **`ℝ` as a one-dimensional Euclidean space**, `a ↦ (a)`. -/
noncomputable def euclideanOne : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 => ℝ).symm

@[simp] theorem euclideanOne_apply (a : ℝ) (i : Fin 1) : euclideanOne a i = a := by
  fin_cases i
  rfl

/-- The one-dimensional transport multiplies: it is an isometry of `ℝ` onto `ℝ¹`. -/
theorem inner_euclideanOne (a b : ℝ) :
    (inner ℝ (euclideanOne a) (euclideanOne b) : ℝ) = a * b := by
  simp [PiLp.inner_apply, mul_comm]

variable (n : ℕ)

/-- **Concatenation of `ℝ × ℝⁿ × ℝ` into `ℝⁿ⁺²`**: `(λ, x, μ) ↦ (λ, x₁, …, xₙ, μ)`, a linear
homeomorphism. Its effect on the inner product is `inner_euclideanTripleEquiv`. -/
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

/-- **The triple concatenation adds the three inner products.** -/
theorem inner_euclideanTripleEquiv (p q : (ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) :
    (inner ℝ (euclideanTripleEquiv n p) (euclideanTripleEquiv n q) : ℝ)
      = p.1.1 * q.1.1 + inner ℝ p.1.2 q.1.2 + p.2 * q.2 := by
  simp only [euclideanTripleEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.coe_refl',
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, id_eq]
  rw [LinearIsometryEquiv.inner_map_map, inner_euclideanProdEquiv, inner_euclideanProdEquiv,
    inner_euclideanOne, inner_euclideanOne]

/-- The closure transports along the triple concatenation, because it is a homeomorphism. -/
theorem closure_image_euclideanTripleEquiv (S : Set ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ)) :
    closure (euclideanTripleEquiv n '' S) = euclideanTripleEquiv n '' closure S :=
  ((euclideanTripleEquiv n).toHomeomorph.image_closure S).symm

end Triple
