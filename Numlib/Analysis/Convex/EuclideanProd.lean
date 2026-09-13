import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.RelativeInterior
import Numlib.Analysis.Convex.Subgradient.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concatenating coordinates: `ℝᵐ × ℝⁿ` and `ℝᵐ⁺ⁿ`

`EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (m + n))` are
different types, and a text written in `ℝⁿ` moves between them without comment. This module is that
move: the concatenation `(x, y) ↦ (x₁, …, x_m, y₁, …, y_n)`, together with the transport along it
of the operations a convexity statement is made of — `conj`, `subgradient`, `ri`, the polar and the
pointed-cone hull.

Everything turns on `inner_euclideanProdEquiv`: concatenation adds the two inner products, so the
form `prodPairing` that a product is paired with *is* the inner product of `ℝᵐ⁺ⁿ` read through the
concatenation. `isAdjointPair_euclideanProdEquiv` packages that as an adjointness datum, and each
transport lemma is one application of a general substitution rule to it.

## Main definitions

* `euclideanProdIsometry m n` — the concatenation as a linear isometry
  `WithLp 2 (ℝᵐ × ℝⁿ) ≃ₗᵢ[ℝ] ℝᵐ⁺ⁿ`.
* `euclideanProdEquiv m n` — the same map out of the plain product, `ℝᵐ × ℝⁿ ≃L[ℝ] ℝᵐ⁺ⁿ`.
* `euclideanOne` — `ℝ ≃L[ℝ] ℝ¹`, the scalar read as a one-dimensional Euclidean space.
* `euclideanTripleEquiv n` — `ℝ × ℝⁿ × ℝ ≃L[ℝ] ℝⁿ⁺²`, what a text means by `(λ, x, μ) ∈ ℝⁿ⁺²`.

## Main results

* `inner_euclideanProdEquiv`, `isAdjointPair_euclideanProdEquiv` — the pairing and its adjointness
  datum; `euclideanProdEquiv_apply_castAdd` and friends give the coordinates.
* `conj_comp_euclideanProdEquiv`, `subgradient_comp_euclideanProdEquiv`,
  `relint_image_euclideanProdEquiv` — conjugate, subdifferential and relative interior transport.
* `polarCone_image_of_pairing_eq`, `coe_hull_image` — the same for the polar of a set and for the
  pointed-cone hull, which is what a statement about *cones* is made of.
* `inner_euclideanTripleEquiv`, `closure_image_euclideanTripleEquiv` — the triple concatenation
  carries the inner product of `ℝⁿ⁺²` to `λ λ* + ⟨x, y⟩ + μ μ*` and commutes with the closure. That
  is all a consumer needs: which `Fin (n + 2)` index carries `λ` is an artefact of the assembly.

## Implementation notes

The isometry is out of `WithLp 2 (ℝᵐ × ℝⁿ)` because Mathlib's norm on a product is the *supremum*
norm. Everything else is stated for the plain product, whose linear structure and topology are all
that `conj`, `subgradient` and `ri` need, so that no consumer has to move a `Convex` or an
`IsClosed` across a type synonym; `euclideanProdEquiv_eq_isometry` records that the two agree.
-/

open Set

namespace ConvexAnalysis

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

/-- **Concatenation adds the two inner products.** So `prodPairing`, the form a product is paired
with, is the inner product of `ℝᵐ⁺ⁿ` read through the concatenation. -/
theorem inner_euclideanProdEquiv
    (p q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) : ℝ)
      = inner ℝ p.1 q.1 + inner ℝ p.2 q.2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_add]

end Defs

/-! ### The adjointness datum -/

section Pairing

variable {m n : ℕ}

/-- The inner product of `ℝᵐ⁺ⁿ` pulled back along the concatenation is `prodPairing`. -/
theorem prodPairing_euclideanProdEquiv_symm (z : EuclideanSpace ℝ (Fin (m + n)))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n)))
        ((euclideanProdEquiv m n).symm z) q
      = innerₗ (EuclideanSpace ℝ (Fin (m + n))) z (euclideanProdEquiv m n q) := by
  have h := inner_euclideanProdEquiv ((euclideanProdEquiv m n).symm z) q
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Concatenation is an adjoint pair for the two pairings.** This is the hypothesis
`conj_comp_linearEquiv` and `subgradient_comp_linearEquiv` take, and the only mathematical input the
transport has. -/
theorem isAdjointPair_euclideanProdEquiv :
    IsAdjointPair (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
      (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m))) (innerₗ (EuclideanSpace ℝ (Fin n))))
      ((euclideanProdEquiv m n).symm.toLinearEquiv : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
      ((euclideanProdEquiv m n).toLinearEquiv :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + n))) :=
  fun z q => prodPairing_euclideanProdEquiv_symm z q

end Pairing

/-! ### Transporting the subdifferential along a linear isomorphism

`conj_comp_linearEquiv` is the substitution rule for the conjugate. The subdifferential
obeys the same rule, in the generality of an arbitrary adjoint pair of isomorphisms. -/

section SubgradientTransport

variable {E F G H : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Precomposing with a linear isomorphism moves the subdifferential along the transpose.**
The companion of `conj_comp_linearEquiv` for `∂f`: if `A` and `A'` are adjoint isomorphisms, then
`∂(g ∘ A)(x) = A' (∂g (A x))`. -/
theorem subgradient_comp_linearEquiv {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (g : G → EReal) (x : E) :
    subgradient B (fun u => g (A u)) x = A' '' subgradient B' g (A x) := by
  ext y
  constructor
  · intro hy
    refine ⟨A'.symm y, fun w => ?_, A'.apply_symm_apply y⟩
    have hw : g (A x) + ((B (A.symm w - x) y : ℝ) : EReal) ≤ g (A (A.symm w)) := hy (A.symm w)
    rw [LinearEquiv.apply_symm_apply] at hw
    have h2 := hA (A.symm w - x) (A'.symm y)
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (A.symm w - x) = w - A x := by simp
    have h3 : A' (A'.symm y) = y := A'.apply_symm_apply y
    rw [h1, h3] at h2
    rw [h2]
    exact hw
  · rintro ⟨v, hv, rfl⟩
    intro w
    have hw : g (A x) + ((B' (A w - A x) v : ℝ) : EReal) ≤ g (A w) := hv (A w)
    have h2 := hA (w - x) v
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (w - x) = A w - A x := map_sub A w x
    rw [h1] at h2
    rw [← h2]
    exact hw

end SubgradientTransport

/-! ### The transport -/

section Transport

variable {m n : ℕ}

/-- **The conjugate transports along the concatenation.** A function `f` on `ℝᵐ × ℝⁿ` read as a
function on `ℝᵐ⁺ⁿ` has, as its conjugate for the inner product of `ℝᵐ⁺ⁿ`, the conjugate of `f` for
`prodPairing` read the same way. -/
theorem conj_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    conj (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = conj (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  conj_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The subdifferential transports along the concatenation.** -/
theorem subgradient_comp_euclideanProdEquiv (f : EuclideanSpace ℝ (Fin m) ×
    EuclideanSpace ℝ (Fin n) → EReal) (z : EuclideanSpace ℝ (Fin (m + n))) :
    subgradient (innerₗ (EuclideanSpace ℝ (Fin (m + n))))
        (fun w => f ((euclideanProdEquiv m n).symm w)) z
      = euclideanProdEquiv m n '' subgradient (prodPairing (innerₗ (EuclideanSpace ℝ (Fin m)))
          (innerₗ (EuclideanSpace ℝ (Fin n)))) f ((euclideanProdEquiv m n).symm z) :=
  subgradient_comp_linearEquiv (euclideanProdEquiv m n).symm.toLinearEquiv
    (euclideanProdEquiv m n).toLinearEquiv isAdjointPair_euclideanProdEquiv f z

/-- **The relative interior transports along the concatenation.** -/
theorem relint_image_euclideanProdEquiv
    {C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C) :
    ri (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' ri C :=
  Convex.relint_image hC (euclideanProdEquiv m n).toLinearEquiv.toLinearMap

/-- **The relative interior transports along the concatenation**, read the other way. -/
theorem relint_image_euclideanProdEquiv_symm {D : Set (EuclideanSpace ℝ (Fin (m + n)))}
    (hD : Convex ℝ D) :
    ri ((euclideanProdEquiv m n).symm '' D) = (euclideanProdEquiv m n).symm '' ri D :=
  Convex.relint_image hD (euclideanProdEquiv m n).symm.toLinearEquiv.toLinearMap

/-- The closure transports along the concatenation, because it is a homeomorphism. -/
theorem closure_image_euclideanProdEquiv
    (C : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    closure (euclideanProdEquiv m n '' C) = euclideanProdEquiv m n '' closure C :=
  ((euclideanProdEquiv m n).toHomeomorph.image_closure C).symm

end Transport

/-! ### Transporting polarity and cone hulls

Both are needed wherever a *cone* in a product is read in `ℝᵏ`: the polar consumes the adjointness
datum, the pointed-cone hull needs only linearity. -/

section PolarTransport

variable {E F G H : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Polarity transports along an adjoint pair of isomorphisms.** If `A` and `A'` carry `B'` back
to `B`, the polar of `A '' S` for `B'` is the image under `A'` of the polar of `S` for `B`. -/
theorem polarCone_image_of_pairing_eq {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : F ≃ₗ[ℝ] H) (hA : ∀ p q, B' (A p) (A' q) = B p q) (S : Set E) :
    polarCone B' (A '' S) = A' '' polarCone B S := by
  ext w
  constructor
  · intro hw
    refine ⟨A'.symm w, fun p hp => ?_, A'.apply_symm_apply w⟩
    have hkey := hA p (A'.symm w)
    rw [A'.apply_symm_apply] at hkey
    rw [← hkey]
    exact hw (A p) ⟨p, hp, rfl⟩
  · rintro ⟨v, hv, rfl⟩ z ⟨p, hp, rfl⟩
    rw [hA p v]
    exact hv p hp

/-- **The pointed-cone hull transports along a linear map**: `hull (A '' S) = A '' hull S`. This is
`Submodule.map_span` over the semiring of non-negative reals, restated on the underlying sets. -/
theorem coe_hull_image (A : E →ₗ[ℝ] G) (S : Set E) :
    (PointedCone.hull ℝ (A '' S) : Set G) = A '' (PointedCone.hull ℝ S : Set E) := by
  have h : PointedCone.hull ℝ (A '' S) = (PointedCone.hull ℝ S).map A :=
    (Submodule.map_span (A : E →ₗ[{c : ℝ // 0 ≤ c}] G) S).symm
  rw [h, PointedCone.coe_map]

end PolarTransport

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

end ConvexAnalysis
