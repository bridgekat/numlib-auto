import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Approximation.Chebyshev

/-!
# The abstract interpolation problem

Given a subspace `Vₙ` of a normed space `V` and `n` bounded linear functionals `L i`, the
*interpolation problem* asks for a `u ∈ Vₙ` with `L i u = b i` for prescribed data `b`. The
problem is **unisolvent** when it has exactly one solution for every datum. The material is
[Atkinson–Han, *Theoretical Numerical Analysis*][han2009theoretical] §3.2 and §3.3.4.

## Main definitions

* `Approximation.interpMap Vₙ L` is the linear map `u ↦ (L i u)` from `Vₙ` to `Fin n → 𝕜`.
* `Approximation.IsUnisolvent Vₙ L` says that the interpolation problem has exactly one solution
  for every datum, equivalently that `interpMap` is bijective
  (`Approximation.isUnisolvent_iff_bijective`).
* `Approximation.IsUnisolvent.interpolate` is the resulting interpolation operator, a linear
  equivalence from the data to the subspace.

## Main results

* In a basis `v` of `Vₙ` the map is the matrix `(L i (v j))`, so unisolvence is the nonvanishing
  of its determinant, `Approximation.isUnisolvent_iff_det_ne_zero`. Since the left-hand side does
  not mention the basis, the determinant condition does not depend on it.
* `Approximation.isUnisolvent_tfae` collects the four classical forms: unique solvability, linear
  independence of the functionals over `Vₙ`, triviality of the homogeneous problem, and
  solvability for every datum.
* `Approximation.haarCondition_iff_isUnisolvent` is the bridge to the Haar condition of
  `Numlib/Approximation/Chebyshev`: a subspace of `C(X, ℝ)` of dimension `n` satisfies the Haar
  condition in dimension `n` exactly when every family of `n` distinct point evaluations is
  unisolvent over it. Both say that a nonzero element has fewer than `n` zeros.
-/

open scoped Matrix

namespace Approximation

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {n : ℕ}

/-- The **interpolation map** of a family of functionals on a subspace: `u ↦ (L i u)`. The
interpolation problem is the equation `interpMap Vₙ L u = b`. -/
def interpMap (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) : Vₙ →ₗ[𝕜] Fin n → 𝕜 where
  toFun u i := L i (u : V)
  map_add' u u' := by ext i; simp
  map_smul' c u := by ext i; simp

/-- The interpolation map, evaluated at one index. -/
@[simp]
theorem interpMap_apply (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) (u : Vₙ)
    (i : Fin n) : interpMap Vₙ L u i = L i (u : V) := rfl

/-- **The interpolation problem is unisolvent** when, for every datum `b`, there is exactly one
`u` in the subspace `Vₙ` with `L i u = b i` for all `i`.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Definition 3.2.1 and Theorem 3.2.3. -/
def IsUnisolvent (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) : Prop :=
  ∀ b : Fin n → 𝕜, ∃! u : Vₙ, ∀ i, L i (u : V) = b i

variable {Vₙ : Submodule 𝕜 V} {L : Fin n → StrongDual 𝕜 V}

/-- Unisolvence is bijectivity of the interpolation map. -/
theorem isUnisolvent_iff_bijective :
    IsUnisolvent Vₙ L ↔ Function.Bijective (interpMap Vₙ L) := by
  rw [Function.bijective_iff_existsUnique]
  exact forall_congr' fun b => existsUnique_congr fun u => (funext_iff (g := b)).symm

/-! ### The matrix of the problem in a basis -/

section Matrix

variable (v : Module.Basis (Fin n) 𝕜 Vₙ)

include v

/-- In a basis of the subspace, the interpolation map is multiplication by the matrix
`(L i (v j))`. -/
theorem interpMap_eq_mulVec (u : Vₙ) :
    interpMap Vₙ L u = (Matrix.of fun i j => L i (v j : V)) *ᵥ v.equivFun u := by
  have hu : (u : V) = ∑ j, v.equivFun u j • (v j : V) := by
    have h := map_sum Vₙ.subtype (fun j => v.equivFun u j • v j) Finset.univ
    rw [v.sum_equivFun u] at h
    exact h
  funext i
  rw [interpMap_apply, hu, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The interpolation map is the matrix of the problem composed with the coordinate isomorphism
of the basis. -/
private theorem coe_interpMap_eq :
    ⇑(interpMap Vₙ L) = (Matrix.of fun i j => L i (v j : V)).mulVec ∘ v.equivFun :=
  funext fun u => interpMap_eq_mulVec v u

/-- The homogeneous problem has only the trivial solution exactly when the matrix is
invertible. -/
private theorem injective_interpMap_iff_isUnit :
    Function.Injective (interpMap Vₙ L) ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  classical
  rw [coe_interpMap_eq v, Function.Injective.of_comp_iff' _ v.equivFun.bijective,
    Matrix.mulVec_injective_iff_isUnit]

/-- The problem is solvable for every datum exactly when the matrix is invertible. -/
private theorem surjective_interpMap_iff_isUnit :
    Function.Surjective (interpMap Vₙ L) ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  classical
  rw [coe_interpMap_eq v, Function.Surjective.of_comp_iff _ v.equivFun.surjective,
    Matrix.mulVec_surjective_iff_isUnit]

/-- Unisolvence is invertibility of the matrix of the problem. -/
theorem isUnisolvent_iff_isUnit :
    IsUnisolvent Vₙ L ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  rw [isUnisolvent_iff_bijective]
  exact ⟨fun h => (injective_interpMap_iff_isUnit v).1 h.1,
    fun h => ⟨(injective_interpMap_iff_isUnit v).2 h, (surjective_interpMap_iff_isUnit v).2 h⟩⟩

/-- **The determinant criterion.** For a basis `v` of the `n`-dimensional subspace `Vₙ`, the
interpolation problem is unisolvent exactly when `det (L i (v j)) ≠ 0`. The left-hand side does
not mention the basis, so neither does the nonvanishing of the determinant.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Lemma 3.2.2. -/
theorem isUnisolvent_iff_det_ne_zero :
    IsUnisolvent Vₙ L ↔ (Matrix.of fun i j => L i (v j : V)).det ≠ 0 := by
  classical
  rw [isUnisolvent_iff_isUnit v, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **The homogeneous form.** The problem is unisolvent exactly when the only element of `Vₙ`
annihilated by every functional is `0`.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 3.2.3. -/
theorem isUnisolvent_iff_forall_eq_zero :
    IsUnisolvent Vₙ L ↔ ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0 := by
  rw [isUnisolvent_iff_isUnit v, ← injective_interpMap_iff_isUnit v,
    injective_iff_map_eq_zero (interpMap Vₙ L)]
  exact forall_congr' fun u => imp_congr_left (funext_iff (g := (0 : Fin n → 𝕜)))

/-- **The solvability form.** The problem is unisolvent exactly when it is solvable for every
datum; on an `n`-dimensional subspace with `n` functionals, existence already forces uniqueness.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 3.2.3. -/
theorem isUnisolvent_iff_forall_exists :
    IsUnisolvent Vₙ L ↔ ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i := by
  rw [isUnisolvent_iff_isUnit v, ← surjective_interpMap_iff_isUnit v]
  refine ⟨fun h b => ?_, fun h b => ?_⟩
  · obtain ⟨u, hu⟩ := h b
    exact ⟨u, fun i => congrFun hu i⟩
  · obtain ⟨u, hu⟩ := h b
    exact ⟨u, funext hu⟩

/-- **Linear independence of the functionals over the subspace**, the form in which Atkinson–Han
state the definition: the restrictions of `L i` to `Vₙ` are linearly independent in the dual of
`Vₙ`.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Definition 3.2.1 and Theorem 3.2.3. -/
theorem isUnisolvent_iff_linearIndependent :
    IsUnisolvent Vₙ L ↔
      LinearIndependent 𝕜 fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ := by
  classical
  set M : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => L i (v j : V)
  have hrow : (fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ) = fun i => v.constr 𝕜 (M.row i) := by
    funext i
    exact v.ext fun j => (v.constr_basis 𝕜 (M.row i) j).symm
  have hinjc : Function.Injective ⇑(v.constr (M' := 𝕜) 𝕜).toLinearMap :=
    (v.constr (M' := 𝕜) 𝕜).injective
  have hker : LinearMap.ker (v.constr (M' := 𝕜) 𝕜).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hinjc
  rw [isUnisolvent_iff_isUnit v, hrow, ← Matrix.linearIndependent_rows_iff_isUnit]
  exact ⟨fun h => h.map' _ hker, fun h => h.of_comp (v.constr (M' := 𝕜) 𝕜).toLinearMap⟩

/-- **The four equivalent forms of unisolvence**: unique solvability, linear independence of the
functionals over `Vₙ`, triviality of the homogeneous problem, and solvability for every datum.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, Theorem 3.2.3. -/
theorem isUnisolvent_tfae :
    List.TFAE
      [IsUnisolvent Vₙ L,
        LinearIndependent 𝕜 fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ,
        ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0,
        ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i] := by
  tfae_have 1 ↔ 2 := isUnisolvent_iff_linearIndependent v
  tfae_have 1 ↔ 3 := isUnisolvent_iff_forall_eq_zero v
  tfae_have 1 ↔ 4 := isUnisolvent_iff_forall_exists v
  tfae_finish

end Matrix

/-! ### The interpolation operator -/

/-- **The interpolation operator** of a unisolvent problem: the linear equivalence from the data
`b` to the unique element of `Vₙ` interpolating them.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, (3.2.3). -/
noncomputable def IsUnisolvent.interpolate (h : IsUnisolvent Vₙ L) : (Fin n → 𝕜) ≃ₗ[𝕜] Vₙ :=
  (LinearEquiv.ofBijective (interpMap Vₙ L) (isUnisolvent_iff_bijective.mp h)).symm

/-- The interpolant takes the prescribed values. -/
@[simp]
theorem IsUnisolvent.apply_interpolate (h : IsUnisolvent Vₙ L) (b : Fin n → 𝕜) (i : Fin n) :
    L i ((h.interpolate b : Vₙ) : V) = b i := by
  have := (LinearEquiv.ofBijective (interpMap Vₙ L)
    (isUnisolvent_iff_bijective.mp h)).apply_symm_apply b
  exact congrFun this i

/-- The interpolant is the only element of `Vₙ` with the prescribed values. -/
theorem IsUnisolvent.eq_interpolate (h : IsUnisolvent Vₙ L) {b : Fin n → 𝕜} {u : Vₙ}
    (hu : ∀ i, L i (u : V) = b i) : u = h.interpolate b :=
  ((h b).unique hu) fun i => h.apply_interpolate b i

/-! ### The Haar condition -/

/-- **The Haar condition is unisolvence at every family of distinct points.** For a subspace of
`C(X, ℝ)` of dimension `n`, no nonzero element vanishes at `n` distinct points exactly when the
interpolation problem at every `n` distinct points is uniquely solvable.

Reference: Atkinson–Han, *Theoretical Numerical Analysis*, §3.3.4. -/
theorem haarCondition_iff_isUnisolvent {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (Vₙ : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ Vₙ] (hdim : Module.finrank ℝ Vₙ = n) :
    HaarCondition Vₙ n ↔
      ∀ x : Fin n → X, Function.Injective x →
        IsUnisolvent Vₙ fun i => ContinuousMap.evalCLM ℝ (x i) := by
  classical
  set v := Module.finBasisOfFinrankEq ℝ (Vₙ : Submodule ℝ C(X, ℝ)) hdim
  constructor
  · intro hhaar x hx
    refine (isUnisolvent_iff_forall_eq_zero v).mpr fun u hu => ?_
    by_contra hu0
    have hne : (u : C(X, ℝ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hzero : ∀ t ∈ Finset.univ.image x, (u : C(X, ℝ)) t = 0 := by
      rintro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hu i
    have hcard : (Finset.univ.image x).card = n := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    exact absurd (hhaar _ u.2 hne _ hzero) (by omega)
  · intro huni g hg hg0 s hs
    by_contra hcard
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_lt hcard)
    set e := Finset.equivFinOfCardEq htcard
    set x : Fin n → X := fun i => ((e.symm i : t) : X)
    have hx : Function.Injective x := fun i j hij =>
      e.symm.injective (Subtype.ext hij)
    have huz := (isUnisolvent_iff_forall_eq_zero v).mp (huni x hx) ⟨g, hg⟩ fun i => by
      exact hs _ (hts (e.symm i).2)
    exact hg0 (by simpa using congrArg Subtype.val huz)

end Approximation
