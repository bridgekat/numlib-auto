import Numlib.Optimization.OracleSupport
import Numlib.Analysis.InnerProductSpace.OrthonormalExtension

/-!
# Completing oracle frames under finite orthogonality constraints

An exposed part of an orthonormal frame can be retained while every unexposed column is
chosen orthogonal to a prescribed finite query family. The ambient dimension only needs
the number of frame columns plus the number of queries. The construction chooses actual
vectors from an orthonormal basis of the appropriate orthogonal complement.
-/

noncomputable section
open scoped InnerProductSpace

namespace Optimization.ZeroChains

/-- An actual rectangular isometric frame can keep every exposed column and hide every
other column from a finite query family. `m ≥ n + card κ` is the full dimension budget. -/
theorem exists_embedding_preserving_columns {n m : ℕ} {κ : Type*} [Fintype κ]
    (U : Space n →ₗᵢ[ℝ] Space m) (s : Finset (Fin n)) (Q : κ → Space m)
    (hbudget : n + Fintype.card κ ≤ m) :
    ∃ V : Space n →ₗᵢ[ℝ] Space m,
      (∀ i ∈ s, V (EuclideanSpace.single i 1) = U (EuclideanSpace.single i 1)) ∧
      ∀ j, coordinateSupport (V.toContinuousLinearMap.adjoint (Q j)) ⊆ (s : Set (Fin n)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hU : Orthonormal ℝ (fun i : s => U (b i)) :=
    (b.orthonormal.comp_linearIsometry U).comp Subtype.val Subtype.val_injective
  obtain ⟨w, hw, hws, hwQ⟩ := InnerProductSpace.exists_orthonormal_extension_orthogonal
    s (fun i => U (b i)) hU Q (by simpa [Space] using hbudget)
  let L := b.toBasis.constr ℝ w
  have hLb : L ∘ b.toBasis = w := by
    funext i
    exact b.toBasis.constr_basis ℝ w i
  have hL : Orthonormal ℝ (L ∘ b.toBasis) := by rw [hLb]; exact hw
  let V := L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal hL
  have hV : ∀ i, V (EuclideanSpace.single i 1) = w i := by
    intro i
    change L (EuclideanSpace.single i 1) = w i
    rw [← EuclideanSpace.basisFun_apply]
    exact b.toBasis.constr_basis ℝ w i
  refine ⟨V, ?_, ?_⟩
  · intro i hi
    rw [hV]
    simpa [b, EuclideanSpace.basisFun_apply] using hws i hi
  · intro j i hi
    by_contra his
    apply hi
    rw [adjoint_embedding_apply_coordinate, hV, real_inner_comm]
    exact hwQ i his j

/-- Agreement of exposed columns preserves the projection of any query whose old and new
adjoint coordinates are supported in that exposed set. -/
theorem adjoint_eq_of_columns_of_support {n m : ℕ}
    (U V : Space n →L[ℝ] Space m) (s : Finset (Fin n)) (x : Space m)
    (hUV : ∀ i ∈ s, V (EuclideanSpace.single i 1) = U (EuclideanSpace.single i 1))
    (hU : coordinateSupport (U.adjoint x) ⊆ (s : Set (Fin n)))
    (hV : coordinateSupport (V.adjoint x) ⊆ (s : Set (Fin n))) :
    V.adjoint x = U.adjoint x := by
  classical
  ext i
  by_cases hi : i ∈ s
  · calc
      V.adjoint x i = ⟪V (EuclideanSpace.single i 1), x⟫_ℝ := by
        simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
          V.adjoint_inner_right (EuclideanSpace.single i 1) x
      _ = ⟪U (EuclideanSpace.single i 1), x⟫_ℝ := by rw [hUV i hi]
      _ = U.adjoint x i := by
        simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
          (U.adjoint_inner_right (EuclideanSpace.single i 1) x).symm
  · have hu : U.adjoint x i = 0 := by
      by_contra hne
      exact hi (hU hne)
    have hv : V.adjoint x i = 0 := by
      by_contra hne
      exact hi (hV hne)
    rw [hu, hv]

/-- Extend an exposed frame after one new query: preserve all exposed columns and previous
query projections, while both the old queries and the new query have no unexposed adjoint
coordinates. This is an actual finite-stage extension with budget `n + card κ + 1 ≤ m`. -/
theorem exists_embedding_extension {n m : ℕ} {κ : Type*} [Fintype κ]
    (U : Space n →ₗᵢ[ℝ] Space m) (s : Finset (Fin n)) (Q : κ → Space m) (y : Space m)
    (hQ : ∀ j, coordinateSupport (U.toContinuousLinearMap.adjoint (Q j)) ⊆ (s : Set (Fin n)))
    (hbudget : n + Fintype.card κ + 1 ≤ m) :
    ∃ V : Space n →ₗᵢ[ℝ] Space m,
      (∀ i ∈ s, V (EuclideanSpace.single i 1) = U (EuclideanSpace.single i 1)) ∧
      (∀ j, V.toContinuousLinearMap.adjoint (Q j) = U.toContinuousLinearMap.adjoint (Q j)) ∧
      coordinateSupport (V.toContinuousLinearMap.adjoint y) ⊆ (s : Set (Fin n)) := by
  let queries : Option κ → Space m := fun j => j.elim y Q
  obtain ⟨V, hVs, hVQ⟩ := exists_embedding_preserving_columns U s queries
    (by simpa only [Fintype.card_option, Nat.add_assoc] using hbudget)
  refine ⟨V, hVs, ?_, hVQ none⟩
  intro j
  exact adjoint_eq_of_columns_of_support U.toContinuousLinearMap V.toContinuousLinearMap
    s (Q j) (by simpa only [LinearIsometry.coe_toContinuousLinearMap] using hVs)
    (hQ j) (hVQ (some j))

end Optimization.ZeroChains

namespace Optimization.DerivativeOracle
open ZeroChains

/-- Lift an entire derivative reply along a continuous linear coordinate map. -/
def Reply.pullback {n m p : ℕ} (r : Reply n p) (L : Space m →L[ℝ] Space n) : Reply m p where
  value := r.value
  derivative q := (r.derivative q).compContinuousLinearMap (fun _ => L)

/-- Pulling back a reply retains its value. -/
@[simp] theorem Reply.pullback_value {n m p : ℕ} (r : Reply n p)
    (L : Space m →L[ℝ] Space n) : (r.pullback L).value = r.value := rfl

/-- Pulling back a reply transforms every full derivative tensor. -/
@[simp] theorem Reply.pullback_derivative {n m p : ℕ} (r : Reply n p)
    (L : Space m →L[ℝ] Space n) (q : Fin p) :
    (r.pullback L).derivative q =
      (r.derivative q).compContinuousLinearMap (fun _ => L) := rfl

/-- The pullback of an actual response is the actual response to the pullback objective. -/
theorem oracle_pullback {n m p : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    (L : Space m →L[ℝ] Space n) (x : Space m) :
    oracle p (ZeroChains.pullback L f) x = (oracle p f (L x)).pullback L := by
  apply (Reply.ext_iff _ _).mpr
  refine ⟨rfl, ?_⟩
  intro q
  exact iteratedFDeriv_pullback hf (by omega) L x

/-- Lifts of arbitrary replies agree under frames that retain all columns supporting their
derivative tensors. This result does not select or inspect an objective. -/
theorem Reply.pullback_adjoint_eq {n m p : ℕ} (r : Reply n p)
    (U V : Space n →ₗᵢ[ℝ] Space m) (s : Finset (Fin n))
    (hs : ∀ q, TensorSupportedOn (r.derivative q) s)
    (hUV : ∀ i ∈ s, V (EuclideanSpace.single i 1) = U (EuclideanSpace.single i 1)) :
    r.pullback V.toContinuousLinearMap.adjoint = r.pullback U.toContinuousLinearMap.adjoint := by
  apply (Reply.ext_iff _ _).mpr
  refine ⟨rfl, ?_⟩
  intro q
  exact (hs q).comp_eq _ _ (coordinateProjection_comp_adjoint_eq s V U hUV)

/-- For an arbitrary finite history of replies, extend the frame to hide the method's next
query while preserving every previous projected noninitial query and every lifted response.
The initial query is zero and consumes no dimension. The method and reply history are fixed
before any objective is chosen; at stage `k < K`, dimension `n + K` suffices. -/
theorem Method.exists_frame_extension_next {n m p k : ℕ} (M : Method p)
    (U : Space n →ₗᵢ[ℝ] Space m) (s : Finset (Fin n))
    (Q : Fin k → Space m) (R : Fin (k + 1) → Reply n p)
    (hQ : ∀ j, coordinateSupport (U.toContinuousLinearMap.adjoint (Q j)) ⊆ (s : Set (Fin n)))
    (hR : ∀ j q, TensorSupportedOn ((R j).derivative q) s)
    (hbudget : n + k + 1 ≤ m) :
    ∃ V : Space n →ₗᵢ[ℝ] Space m,
      (∀ i ∈ s, V (EuclideanSpace.single i 1) = U (EuclideanSpace.single i 1)) ∧
      (∀ j, V.toContinuousLinearMap.adjoint (Q j) = U.toContinuousLinearMap.adjoint (Q j)) ∧
      (∀ j, (R j).pullback V.toContinuousLinearMap.adjoint =
        (R j).pullback U.toContinuousLinearMap.adjoint) ∧
      coordinateSupport (V.toContinuousLinearMap.adjoint
        (M.next m k (fun j => (R j).pullback V.toContinuousLinearMap.adjoint))) ⊆
          (s : Set (Fin n)) := by
  let y := M.next m k (fun j => (R j).pullback U.toContinuousLinearMap.adjoint)
  obtain ⟨V, hVs, hVQ, hVy⟩ := exists_embedding_extension U s Q y hQ
    (by simpa only [Fintype.card_fin, Nat.add_assoc] using hbudget)
  have hVR : ∀ j, (R j).pullback V.toContinuousLinearMap.adjoint =
      (R j).pullback U.toContinuousLinearMap.adjoint :=
    fun j => (R j).pullback_adjoint_eq U V s (hR j) hVs
  refine ⟨V, hVs, hVQ, hVR, ?_⟩
  have hy : M.next m k (fun j => (R j).pullback V.toContinuousLinearMap.adjoint) = y := by
    exact congrArg (M.next m k) (funext hVR)
  rw [hy]
  exact hVy

end Optimization.DerivativeOracle
