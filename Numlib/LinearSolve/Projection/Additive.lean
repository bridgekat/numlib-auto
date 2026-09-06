import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.LinearSolve.Projection.Basic

/-!
# Additive and multiplicative projection processes

A family of Petrov–Galerkin pairs `(K i, L i)` can be combined in two ways
(Saad[^saad-iterative] §5.4).  The *additive* process adds all the corrections at once, with
relaxation weights `ω i` (Saad's Algorithm 5.5); the *multiplicative* process applies them one
after another along a list of indices (Saad's Algorithm 5.6), which is the block Gauss–Seidel
pattern.  Block Jacobi and block Gauss–Seidel are the instances in which the `K i` are coordinate
subspaces.

Everything is governed by the projectors `P i = additiveProjector A K L i`, the projector onto
`A (K i)` along `(L i)ᗮ`, which is Saad's `P_i = A V_i (W_iᴴ A V_i)⁻¹ W_iᴴ` when bases are given:
the correction of the `i`-th pair satisfies `A δ i = P i r`, so the residual of an additive step
is `(1 - ∑ i, ω i • P i) r` and the residual of a multiplicative sweep is the product of the
`1 - P i` in the order of the sweep.  With `L i = A (K i)` each `P i` is an orthogonal projector,
and if the `A (K i)` are mutually orthogonal and their dimensions add up to that of the whole
space, the projectors sum to `1` and one additive sweep with `ω = 1` is exact.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

open Module (finrank)

namespace Projection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### A well-posed Petrov–Galerkin pair -/

/-- The hypotheses under which one Petrov–Galerkin pair `(K, L)` determines a unique correction:
the trial and test spaces have the same dimension, and `A` maps `K` injectively modulo `Lᗮ`.  The
second condition is the nondegeneracy of Saad, *Iterative Methods*, Prop 5.1, in the form used by
`IsPetrovGalerkin.eq_of_forall`; together with the first it gives
`existsUnique_isPetrovGalerkin_of_finrank_eq`. -/
structure IsNondegeneratePair (A : E →ₗ[𝕜] E) (K L : Submodule 𝕜 E) : Prop where
  /-- The trial and test spaces have the same dimension. -/
  finrank_eq : finrank 𝕜 K = finrank 𝕜 L
  /-- `A` maps `K` injectively modulo `Lᗮ`. -/
  eq_zero_of_mem_orthogonal : ∀ z ∈ K, A z ∈ Lᗮ → z = 0

namespace IsNondegeneratePair

variable {A : E →ₗ[𝕜] E} {K L : Submodule 𝕜 E}

/-- A nondegenerate pair has `A` injective on the trial space. -/
theorem injective_domRestrict (h : IsNondegeneratePair A K L) :
    Function.Injective (A.domRestrict K) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  refine Subtype.ext (h.eq_zero_of_mem_orthogonal (z : E) z.2 ?_)
  rw [show A (z : E) = 0 from LinearMap.mem_ker.1 hz]
  exact Submodule.zero_mem _

/-- The image `A K` has the dimension of the test space, so the projector onto `A K` along `Lᗮ`
exists. -/
theorem finrank_map_eq (h : IsNondegeneratePair A K L) [FiniteDimensional 𝕜 K] :
    finrank 𝕜 (K.map A) = finrank 𝕜 L := by
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj h.injective_domRestrict]
  exact h.finrank_eq

/-- The image `A K` meets `Lᗮ` only at zero, the second half of what the projector onto `A K`
along `Lᗮ` needs. -/
theorem map_inf_orthogonal_eq_bot (h : IsNondegeneratePair A K L) : K.map A ⊓ Lᗮ = ⊥ := by
  refine le_antisymm (fun y hy => ?_) bot_le
  obtain ⟨⟨z, hz, rfl⟩, hy2⟩ := hy
  rw [Submodule.mem_bot, h.eq_zero_of_mem_orthogonal z hz hy2, map_zero]

end IsNondegeneratePair

section Pair

variable (A : E →ₗ[𝕜] E) (b : E) (K L : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
  [FiniteDimensional 𝕜 L] (h : IsNondegeneratePair A K L)

/-- The projector onto `A K` along `Lᗮ` attached to one Petrov–Galerkin pair: Saad's
`P = A V (Wᴴ A V)⁻¹ Wᴴ` of *Iterative Methods*, (5.22).  It is the projector through which the
correction of the pair acts on the residual, `A δ = P r` (`apply_pairStep_sub`). -/
noncomputable def pairProjector : E →ₗ[𝕜] E :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot h.finrank_map_eq
    h.map_inf_orthogonal_eq_bot).choose

/-- The defining properties of `pairProjector`: it is idempotent, its range is `A K` and its
kernel is `Lᗮ`. -/
theorem pairProjector_spec :
    IsIdempotentElem (pairProjector A K L h) ∧
      LinearMap.range (pairProjector A K L h) = K.map A ∧
      LinearMap.ker (pairProjector A K L h) = Lᗮ :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot h.finrank_map_eq
    h.map_inf_orthogonal_eq_bot).choose_spec.1

/-- A projector with the range and kernel of `pairProjector` *is* `pairProjector`. -/
theorem eq_pairProjector {P : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    (hr : LinearMap.range P = K.map A) (hk : LinearMap.ker P = Lᗮ) :
    P = pairProjector A K L h :=
  LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq hP (pairProjector_spec A K L h).1
    (hr.trans (pairProjector_spec A K L h).2.1.symm)
    (hk.trans (pairProjector_spec A K L h).2.2.symm)

/-- **Saad, *Iterative Methods*, (5.22)** in matrix form: with a basis `V` of the trial space and
a basis `W` of the test space, the projector of the pair is `A V (Wᴴ A V)⁻¹ Wᴴ`, the matrix
`Wᴴ A V` being the cross Gram matrix of `A ∘ V` and `W`, invertible exactly by the nondegeneracy
of the pair. -/
theorem pairProjector_eq_obliqueProjectionOfBases {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V W : ι → E) (hV : Submodule.span 𝕜 (Set.range V) = K)
    (hW : Submodule.span 𝕜 (Set.range W) = L)
    (hVW : IsUnit (LinearMap.crossGram 𝕜 (fun i => A (V i)) W)) :
    LinearMap.obliqueProjectionOfBases 𝕜 (fun i => A (V i)) W = pairProjector A K L h := by
  refine eq_pairProjector A K L h
    (LinearMap.obliqueProjectionOfBases_isIdempotentElem _ _ hVW) ?_ ?_
  · rw [LinearMap.range_obliqueProjectionOfBases _ _ hVW, ← hV, Submodule.map_span,
      ← Set.range_comp]
    rfl
  · rw [LinearMap.ker_obliqueProjectionOfBases _ _ hVW, hW]

/-- One Petrov–Galerkin step of the pair `(K, L)`, started from `x`: the unique `y` with
`y - x ∈ K` and `b - A y ⟂ L` (`existsUnique_isPetrovGalerkin_of_finrank_eq`).  This is one inner
iteration of Saad, *Iterative Methods*, Algorithms 5.5 and 5.6. -/
noncomputable def pairStep (x : E) : E :=
  (existsUnique_isPetrovGalerkin_of_finrank_eq b x K L h.finrank_eq
    h.eq_zero_of_mem_orthogonal).choose

variable {A b K L}

/-- `pairStep` meets the Petrov–Galerkin specification. -/
theorem pairStep_isPetrovGalerkin (x : E) :
    IsPetrovGalerkin A b x K L (pairStep A b K L h x) :=
  (existsUnique_isPetrovGalerkin_of_finrank_eq b x K L h.finrank_eq
    h.eq_zero_of_mem_orthogonal).choose_spec.1

/-- **Saad, *Iterative Methods*, (5.22)**: the correction of a Petrov–Galerkin pair acts on the
residual through the projector, `A δ = P r`.  This is the identity that turns both the additive
and the multiplicative process into a statement about products of projectors. -/
theorem apply_pairStep_sub (x : E) :
    A (pairStep A b K L h x - x) = pairProjector A K L h (b - A x) := by
  obtain ⟨hmem, horth⟩ := pairStep_isPetrovGalerkin h x
  have hd : A (pairStep A b K L h x - x) = (b - A x) - (b - A (pairStep A b K L h x)) := by
    rw [map_sub]; abel
  refine ((LinearMap.IsIdempotentElem.apply_eq_iff (pairProjector_spec A K L h).1
    (pairProjector_spec A K L h).2.1 (pairProjector_spec A K L h).2.2 _ _).2 ⟨?_, ?_⟩).symm
  · exact ⟨_, hmem, rfl⟩
  · rw [hd, sub_sub_cancel]
    exact horth

/-- The residual of one Petrov–Galerkin step is `(1 - P) r`. -/
theorem residual_pairStep (x : E) :
    b - A (pairStep A b K L h x) = (1 - pairProjector A K L h) (b - A x) := by
  have hd := apply_pairStep_sub (b := b) h x
  rw [map_sub] at hd
  rw [LinearMap.sub_apply, Module.End.one_apply, ← hd]
  abel

end Pair

/-! ### The additive process -/

section Additive

variable {ι : Type*} [Fintype ι]

variable (A : E →ₗ[𝕜] E) (b : E) (K L : ι → Submodule 𝕜 E)
  [∀ i, FiniteDimensional 𝕜 (K i)] [∀ i, FiniteDimensional 𝕜 (L i)]
  (h : ∀ i, IsNondegeneratePair A (K i) (L i))

/-- The projector `P i` of the `i`-th pair, onto `A (K i)` along `(L i)ᗮ`
(Saad, *Iterative Methods*, (5.22)). -/
noncomputable def additiveProjector (i : ι) : E →ₗ[𝕜] E := pairProjector A (K i) (L i) (h i)

/-- **One step of the additive projection process** (Saad, *Iterative Methods*, Algorithm 5.5)
with relaxation weights `ω`: all the Petrov–Galerkin corrections are computed from the same
current iterate `x` and added at once.  With `ω = 1` and coordinate subspaces this is block
Jacobi. -/
noncomputable def additiveStep (ω : ι → 𝕜) (x : E) : E :=
  x + ∑ i, ω i • (pairStep A b (K i) (L i) (h i) x - x)

variable {A b K L}

/-- **Saad, *Iterative Methods*, (5.22)–(5.23)**: the residual of an additive step is obtained
from the current residual by the operator `1 - ∑ i, ω i • P i`. -/
theorem residual_additiveStep (ω : ι → 𝕜) (x : E) :
    b - A (additiveStep A b K L h ω x)
      = (1 - ∑ i, ω i • additiveProjector A K L h i) (b - A x) := by
  have hA : A (additiveStep A b K L h ω x)
      = A x + ∑ i, ω i • additiveProjector A K L h i (b - A x) := by
    rw [additiveStep, map_add, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [additiveProjector, map_smul, apply_pairStep_sub (h i) x]
  rw [hA, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  abel

omit [Fintype ι] in
/-- The family form of `pairProjector_eq_obliqueProjectionOfBases`: Saad's
`P_i = A V_i (W_iᴴ A V_i)⁻¹ W_iᴴ` of *Iterative Methods*, (5.22). -/
theorem additiveProjector_eq_obliqueProjectionOfBases {κ : Type*} [Fintype κ] [DecidableEq κ]
    (i : ι) (V W : κ → E) (hV : Submodule.span 𝕜 (Set.range V) = K i)
    (hW : Submodule.span 𝕜 (Set.range W) = L i)
    (hVW : IsUnit (LinearMap.crossGram 𝕜 (fun j => A (V j)) W)) :
    additiveProjector A K L h i
      = LinearMap.obliqueProjectionOfBases 𝕜 (fun j => A (V j)) W :=
  (pairProjector_eq_obliqueProjectionOfBases A (K i) (L i) (h i) V W hV hW hVW).symm

omit [Fintype ι] in
/-- **The least-squares option** (Saad, *Iterative Methods*, the remark after (5.23)): choosing
the test space `L i = A (K i)` makes every `P i` the *orthogonal* projector onto `A (K i)`, so the
additive step becomes a sum of orthogonal projections of the residual. -/
theorem additiveProjector_eq_starProjection_of_eq_map (hLK : ∀ i, L i = (K i).map A) (i : ι) :
    additiveProjector A K L h i = (((K i).map A).starProjection : E →ₗ[𝕜] E) := by
  refine (eq_pairProjector A (K i) (L i) (h i) ?_ ?_ ?_).symm
  · exact ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (Submodule.isIdempotentElem_starProjection _)
  · exact Submodule.range_starProjection _
  · rw [Submodule.ker_starProjection, hLK i]

end Additive

/-! ### Exactness of the least-squares additive process -/

section Exact

variable {ι : Type*} [Fintype ι] [FiniteDimensional 𝕜 E]

/-- **Saad's exactness criterion** (Saad, *Iterative Methods*, the remark after (5.23)):
orthogonal projectors onto pairwise orthogonal subspaces whose dimensions add up to the dimension
of the whole space sum to the identity.  Applied to `M i = A (K i)` in the least-squares additive
process, it says that one unrelaxed sweep solves the system exactly.

The proof does not go through a direct sum decomposition.  The map `x ↦ (P i x)ᵢ` into
`∀ i, M i` is surjective by orthogonality, hence injective because the dimensions agree, and it
annihilates `x - ∑ i, P i x`. -/
theorem sum_starProjection_eq_one_of_orthogonal (M : ι → Submodule 𝕜 E)
    (horth : ∀ i j, i ≠ j → M i ⟂ M j) (hdim : ∑ i, finrank 𝕜 (M i) = finrank 𝕜 E) :
    ∑ i, (M i).starProjection = 1 := by
  have hzero : ∀ i j, i ≠ j → ∀ x ∈ M i, (M j).orthogonalProjectionOnto x = 0 := fun i j hij x hx =>
    Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (Submodule.isOrtho_iff_le.1 (horth i j hij) hx)
  have hzero' : ∀ i j, i ≠ j → ∀ x ∈ M i, (M j).starProjection x = 0 := by
    intro i j hij x hx
    rw [Submodule.starProjection_apply, hzero i j hij x hx, Submodule.coe_zero]
  -- the map that collects all the projections at once
  set T : E →ₗ[𝕜] ∀ i, M i :=
    { toFun := fun x i => (M i).orthogonalProjectionOnto x
      map_add' := fun x y => by funext i; simp
      map_smul' := fun c x => by funext i; simp } with hT
  have hTapply : ∀ (x : E) (i : ι), T x i = (M i).orthogonalProjectionOnto x := fun _ _ => rfl
  have hTsurj : Function.Surjective T := by
    intro y
    refine ⟨∑ i, ((y i : E)), funext fun j => ?_⟩
    rw [hTapply, map_sum, Finset.sum_eq_single j]
    · exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (y j)
    · exact fun i _ hij => hzero i j hij _ (y i).2
    · exact fun hj => absurd (Finset.mem_univ j) hj
  have hrank : finrank 𝕜 (∀ i, M i) = finrank 𝕜 E := by
    rw [Module.finrank_pi_fintype]
    exact hdim
  have hTinj : Function.Injective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := T) hrank.symm).2 hTsurj
  refine ContinuousLinearMap.ext fun x => ?_
  have hker : T (∑ i, (M i).starProjection x) = T x := by
    funext j
    rw [hTapply, hTapply, map_sum, Finset.sum_eq_single j]
    · exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    · exact fun i _ hij => hzero i j hij _ ((M i).starProjection_apply_mem x)
    · exact fun hj => absurd (Finset.mem_univ j) hj
  rw [sum_apply, one_apply_eq_self]
  exact hTinj hker

end Exact

/-! ### The multiplicative process -/

section Multiplicative

variable {ι : Type*}

variable (A : E →ₗ[𝕜] E) (b : E) (K L : ι → Submodule 𝕜 E)
  [∀ i, FiniteDimensional 𝕜 (K i)] [∀ i, FiniteDimensional 𝕜 (L i)]
  (h : ∀ i, IsNondegeneratePair A (K i) (L i))

/-- **One sweep of the multiplicative projection process** (Saad, *Iterative Methods*,
Algorithm 5.6): the Petrov–Galerkin corrections of the pairs listed in `l` are applied one after
another, each computed from the iterate the previous one produced.  With coordinate subspaces
this is block Gauss–Seidel, as block Jacobi is `additiveStep`. -/
noncomputable def multiplicativeStep (l : List ι) (x : E) : E :=
  l.foldl (fun y i => pairStep A b (K i) (L i) (h i) y) x

variable {A b K L}

/-- The residual of a multiplicative sweep is the product of the `1 - P i`, taken in the order of
the sweep, applied to the current residual (Saad, *Iterative Methods*, §5.4). -/
theorem residual_multiplicativeStep (l : List ι) (x : E) :
    b - A (multiplicativeStep A b K L h l x)
      = (l.foldr (fun i P => P * (1 - additiveProjector A K L h i)) 1) (b - A x) := by
  induction l generalizing x with
  | nil => simp [multiplicativeStep]
  | cons i l ih =>
      have hstep : multiplicativeStep A b K L h (i :: l) x
          = multiplicativeStep A b K L h l (pairStep A b (K i) (L i) (h i) x) := rfl
      rw [hstep, ih, List.foldr_cons, Module.End.mul_apply]
      congr 1
      exact residual_pairStep (b := b) (h i) x

end Multiplicative

end Projection
