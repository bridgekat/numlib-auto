import Numlib.Optimization.OracleRotations
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Coordinate support of complete derivative replies

A tensor whose mixed basis entries vanish outside a set factors through the coordinate
projection onto that set. Consequently, two rectangular rotations produce exactly the same
complete derivative reply whenever their adjoints agree on all exposed coordinates and send
the query to the same point. The conclusion is equality of tensors, not just mixed entries.
-/

noncomputable section
open scoped ContDiff InnerProductSpace

namespace InnerProductSpace

/-- Fewer prescribed directions than the ambient dimension leave an actual unit direction
orthogonal to every prescribed vector. No independence assumption on the family is needed. -/
theorem exists_unit_orthogonal_family {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] (v : ι → E)
    (hbudget : Fintype.card ι < Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧ ∀ i, ⟪v i, w⟫_ℝ = 0 := by
  let S := Submodule.span ℝ (Set.range v)
  have hd : Module.finrank ℝ S ≤ Fintype.card ι := finrank_range_le_card v
  have ht := S.finrank_add_finrank_orthogonal
  have : Nontrivial Sᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := (0 : Sᗮ))).mpr zero_le_one
  refine ⟨w, by simpa using hw, ?_⟩
  intro i
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self i)) w.property

end InnerProductSpace

namespace Optimization.ZeroChains

variable {n m p : ℕ}

/-- The continuous linear projection retaining precisely the coordinates in `s`. -/
def coordinateProjection (s : Finset (Fin n)) : Space n →L[ℝ] Space n :=
  ∑ i ∈ s, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (EuclideanSpace.single i 1)

/-- A coordinate projection retains a coordinate exactly when its index belongs to its set. -/
@[simp] theorem coordinateProjection_apply (s : Finset (Fin n)) (x : Space n) (i : Fin n) :
    coordinateProjection s x i = if i ∈ s then x i else 0 := by
  classical
  simp [coordinateProjection, Pi.single_apply, Finset.sum_apply, mul_ite]

/-- The projection fixes a basis direction in its coordinate set and kills every other one. -/
@[simp] theorem coordinateProjection_single (s : Finset (Fin n)) (i : Fin n) :
    coordinateProjection s (EuclideanSpace.single i 1) =
      if i ∈ s then EuclideanSpace.single i 1 else 0 := by
  classical
  ext j
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
    simp [coordinateProjection_apply, hi, hj] <;> aesop

/-- An adjoint coordinate is the inner product with the corresponding embedded basis vector. -/
theorem adjoint_embedding_apply_coordinate (U : Space n →ₗᵢ[ℝ] Space m) (x : Space m)
    (i : Fin n) :
    U.toContinuousLinearMap.adjoint x i = ⟪U (EuclideanSpace.single i 1), x⟫_ℝ := by
  simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul,
    LinearIsometry.coe_toContinuousLinearMap] using
    U.toContinuousLinearMap.adjoint_inner_right (EuclideanSpace.single i 1) x

/-- Agreement of embedded basis vectors on `s` preserves precisely the retained adjoint
coordinates, as a continuous linear operator. -/
theorem coordinateProjection_comp_adjoint_eq (s : Finset (Fin n))
    (U V : Space n →ₗᵢ[ℝ] Space m)
    (h : ∀ i ∈ s, U (EuclideanSpace.single i 1) = V (EuclideanSpace.single i 1)) :
    (coordinateProjection s).comp U.toContinuousLinearMap.adjoint =
      (coordinateProjection s).comp V.toContinuousLinearMap.adjoint := by
  classical
  ext x i
  change coordinateProjection s (U.toContinuousLinearMap.adjoint x) i =
    coordinateProjection s (V.toContinuousLinearMap.adjoint x) i
  by_cases hi : i ∈ s
  · simp only [coordinateProjection_apply, hi, ↓reduceIte,
      adjoint_embedding_apply_coordinate, h i hi]
  · simp only [coordinateProjection_apply, hi, ↓reduceIte]

/-- A vector is fixed by a coordinate projection exactly when its support lies in the set. -/
theorem coordinateProjection_eq_self_iff (s : Finset (Fin n)) (x : Space n) :
    coordinateProjection s x = x ↔ coordinateSupport x ⊆ (s : Set (Fin n)) := by
  classical
  constructor
  · intro h i hi
    by_contra hnot
    change i ∉ s at hnot
    have := congrArg (fun y : Space n => y i) h
    simp only [coordinateProjection_apply, ite_eq_right hnot] at this
    exact hi this.symm
  · intro h
    ext i
    by_cases hi : i ∈ s
    · simp [hi]
    · have hx : x i = 0 := by by_contra hx; exact hi (h hx)
      simp [hi, hx]

/-- A continuous multilinear tensor is supported on `s` when all its mixed basis entries
containing a coordinate outside `s` vanish. All slots are included. -/
def TensorSupportedOn {q : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Space n) ℝ)
    (s : Finset (Fin n)) : Prop :=
  ∀ v : Fin q → Fin n, (∃ a, v a ∉ s) →
    T (fun a => EuclideanSpace.single (v a) 1) = 0

/-- Basis-entry support is equivalent to factorization of the entire tensor through the
coordinate projection, without symmetry or differentiability assumptions. -/
theorem tensorSupportedOn_iff {q : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Space n) ℝ)
    (s : Finset (Fin n)) :
    TensorSupportedOn T s ↔
      T = T.compContinuousLinearMap (fun _ => coordinateProjection s) := by
  classical
  constructor
  · intro h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    intro v
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    change T (fun a => EuclideanSpace.single (v a) 1) =
      T (fun a => coordinateProjection s (EuclideanSpace.single (v a) 1))
    by_cases hv : ∀ a, v a ∈ s
    · simp only [coordinateProjection_single, hv, ↓reduceIte]
    · obtain ⟨a, ha⟩ := not_forall.mp hv
      rw [h v ⟨a, ha⟩]
      symm
      apply T.map_coord_zero a
      simp [ha]
  · intro h v hv
    rw [h]
    obtain ⟨a, ha⟩ := hv
    change T (fun b => coordinateProjection s (EuclideanSpace.single (v b) 1)) = 0
    apply T.map_coord_zero a
    simp [ha]

/-- Two linear pullbacks of a supported tensor coincide when their retained coordinate
projections agree. The equality concerns all argument vectors. -/
theorem TensorSupportedOn.comp_eq {q : ℕ}
    {T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Space n) ℝ}
    {s : Finset (Fin n)} (hT : TensorSupportedOn T s)
    (A B : Space m →L[ℝ] Space n)
    (h : (coordinateProjection s).comp A = (coordinateProjection s).comp B) :
    T.compContinuousLinearMap (fun _ => A) = T.compContinuousLinearMap (fun _ => B) := by
  have hf := (tensorSupportedOn_iff T s).mp hT
  ext v
  change T (fun a => A (v a)) = T (fun a => B (v a))
  conv_lhs => rw [hf]
  conv_rhs => rw [hf]
  change T (fun a => coordinateProjection s (A (v a))) =
    T (fun a => coordinateProjection s (B (v a)))
  congr 1
  funext a
  exact congrArg (fun L : Space m →L[ℝ] Space n => L (v a)) h

/-- Every oracle tensor is supported on any set containing the exposed derivative coordinates. -/
theorem tensorSupportedOn_iteratedFDeriv {q : ℕ} (f : Space n → ℝ) (x : Space n)
    (hq : 1 ≤ q) (hqp : q ≤ p) (s : Finset (Fin n))
    (hs : derivativeSupport p f x ⊆ (s : Set (Fin n))) :
    TensorSupportedOn (iteratedFDeriv ℝ q f x) s := by
  rintro v ⟨a, ha⟩
  apply (not_mem_derivativeSupport_iff f x (v a)).mp _ q hq hqp v ⟨a, rfl⟩
  intro hmem
  exact ha (hs hmem)

end Optimization.ZeroChains

namespace Optimization.DerivativeOracle
open ZeroChains

/-- Complete replies agree when their values and every actual derivative tensor agree. -/
theorem Reply.ext_iff {n p : ℕ} (r t : Reply n p) :
    r = t ↔ r.value = t.value ∧ ∀ q, r.derivative q = t.derivative q := by
  cases r
  cases t
  simp only [Reply.mk.injEq]
  exact and_congr_right fun _ => funext_iff

/-- Actual rectangular pullback replies are unchanged by altering only unexposed adjoint
coordinates, provided the projected query itself is retained. This checks every tensor order. -/
theorem oracle_rotate_eq {n m p : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ p f)
    (U V : Space n →ₗᵢ[ℝ] Space m) (x y : Space m) (s : Finset (Fin n))
    (hxy : U.toContinuousLinearMap.adjoint x = V.toContinuousLinearMap.adjoint y)
    (hs : derivativeSupport p f (U.toContinuousLinearMap.adjoint x) ⊆ (s : Set (Fin n)))
    (hUV : (coordinateProjection s).comp U.toContinuousLinearMap.adjoint =
      (coordinateProjection s).comp V.toContinuousLinearMap.adjoint) :
    oracle p (rotate U f) x = oracle p (rotate V f) y := by
  apply (Reply.ext_iff _ _).mpr
  constructor
  · change f (U.toContinuousLinearMap.adjoint x) = f (V.toContinuousLinearMap.adjoint y)
    rw [hxy]
  · intro q
    simp only [oracle_derivative]
    rw [iteratedFDeriv_rotate hf (by omega), iteratedFDeriv_rotate hf (by omega), ← hxy]
    exact (tensorSupportedOn_iteratedFDeriv f _ (by omega) (by omega) s hs).comp_eq _ _ hUV

/-- Agreement of exposed embedding columns suffices for equality of complete actual replies. -/
theorem oracle_rotate_eq_of_columns {n m p : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ p f) (U V : Space n →ₗᵢ[ℝ] Space m) (x y : Space m)
    (s : Finset (Fin n))
    (hxy : U.toContinuousLinearMap.adjoint x = V.toContinuousLinearMap.adjoint y)
    (hs : derivativeSupport p f (U.toContinuousLinearMap.adjoint x) ⊆ (s : Set (Fin n)))
    (hUV : ∀ i ∈ s, U (EuclideanSpace.single i 1) = V (EuclideanSpace.single i 1)) :
    oracle p (rotate U f) x = oracle p (rotate V f) y :=
  oracle_rotate_eq hf U V x y s hxy hs (coordinateProjection_comp_adjoint_eq s U V hUV)

/-- A change of embedding preserving all previous projected queries and exposed columns
preserves the actual finite method trace, including the next query after that history.
The assumptions are geometric conditions on one actual trace, not an oracle-agreement premise. -/
theorem Method.iterate_rotate_eq {n m p : ℕ} {f : Space n → ℝ}
    (M : Method p) (hf : ContDiff ℝ p f) (U V : Space n →ₗᵢ[ℝ] Space m)
    (N : ℕ) (s : Finset (Fin n))
    (hproj : ∀ j < N, U.toContinuousLinearMap.adjoint (M.iterate (rotate U f) j) =
      V.toContinuousLinearMap.adjoint (M.iterate (rotate U f) j))
    (hs : ∀ j < N, derivativeSupport p f
      (U.toContinuousLinearMap.adjoint (M.iterate (rotate U f) j)) ⊆ (s : Set (Fin n)))
    (hUV : ∀ i ∈ s, U (EuclideanSpace.single i 1) = V (EuclideanSpace.single i 1)) :
    ∀ j ≤ N, M.iterate (rotate U f) j = M.iterate (rotate V f) j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp
    | succ k =>
      apply M.iterate_succ_eq_of_oracle_eq
      intro l hl
      have hlN : l < N := by omega
      rw [← ih l (by omega) (by omega)]
      exact oracle_rotate_eq_of_columns hf U V _ _ s (hproj l hlN) (hs l hlN) hUV

end Optimization.DerivativeOracle
