/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Projection.Basic

/-!
# Additive and multiplicative projection processes

A family of Petrov–Galerkin pairs $(K_i, L_i)$ for the equation $Ax = b$ can be combined in two ways
([saad2003iterative] §5.4). The *additive* process computes all the corrections from the same
iterate and adds them at once, with relaxation weights $\omega_i$ ([saad2003iterative] Algorithm
5.5). The *multiplicative* process applies the corrections one after another along a list of indices
([saad2003iterative] Algorithm 5.6). When the $K_i$ are coordinate subspaces, the two processes are
block Jacobi and block Gauss–Seidel.

Both processes are described by the projectors $P_i$ onto $AK_i$ along $L_i^\perp$. In bases $V_i$
of $K_i$ and $W_i$ of $L_i$, $P_i = A V_i (W_i^H A V_i)^{-1} W_i^H$. The correction $\delta_i$ of
the $i$-th pair satisfies $A \delta_i = P_i r$ for the current residual $r$. Hence the residual
after an additive step is $(I - \sum_i \omega_i P_i) r$, and the residual after a multiplicative
sweep is the product of the $I - P_i$ in the order of the sweep, applied to $r$. With $L_i = AK_i$
each $P_i$ is an orthogonal projector. If, in addition, the $AK_i$ are mutually orthogonal and their
dimensions add up to the dimension of the space, the projectors sum to $I$, and one additive step
with $\omega = 1$ solves the system.

## Main definitions

* `Projection.IsNondegeneratePair`: $\dim K = \dim L$, and $A$ maps $K$ injectively modulo
  $L^\perp$.
* `Projection.pairProjector`: the projector onto $AK$ along $L^\perp$ of a nondegenerate pair.
* `Projection.pairStep`: one Petrov–Galerkin step for one pair.
* `Projection.additiveProjector`: the projector $P_i$ of the $i$-th pair of a family.
* `Projection.additiveStep`: one step of the additive projection process.
* `Projection.multiplicativeStep`: one sweep of the multiplicative projection process.

## Main results

* `Projection.apply_pairStep_sub`: the correction $\delta$ of one pair satisfies $A\delta = Pr$.
* `Projection.pairProjector_eq_obliqueProjectionOfBases`: in bases, the projector of a pair is
  $AV(W^H A V)^{-1} W^H$.
* `Projection.residual_additiveStep`: the residual after an additive step is
  $(I - \sum_i \omega_i P_i) r$.
* `Projection.additiveProjector_eq_starProjection_of_eq_map`: with $L_i = AK_i$, each $P_i$ is the
  orthogonal projection onto $AK_i$.
* `Projection.sum_starProjection_eq_one_of_orthogonal`: orthogonal projections onto mutually
  orthogonal subspaces whose dimensions add up to $\dim E$ sum to $I$.
* `Projection.residual_multiplicativeStep`: the residual after a multiplicative sweep is the product
  of the $I - P_i$ applied to $r$.

## Implementation notes

* The projector of a pair is defined as the unique idempotent map with range $AK$ and kernel
  $L^\perp$. It does not depend on a choice of bases.
* The multiplicative sweep runs along a list of indices, so an index may occur several times or not
  at all. The additive step sums over a finite index type.
-/

open Module (finrank)

namespace Projection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### A well-posed Petrov–Galerkin pair -/

/-- A **nondegenerate pair** for a linear map $A : E \to E$ is a pair of subspaces $(K, L)$ of $E$
with $\dim K = \dim L$ such that $A$ maps $K$ injectively modulo $L^\perp$: every $z \in K$ with
$Az \in L^\perp$ is $z = 0$.

The second condition is the nondegeneracy condition of [saad2003iterative], Proposition 5.1, in
the form of `IsPetrovGalerkin.eq_of_forall`. For finite-dimensional $K$ and $L$, both conditions
together give a unique Petrov–Galerkin iterate by `existsUnique_isPetrovGalerkin_of_finrank_eq`. -/
structure IsNondegeneratePair (A : E →ₗ[𝕜] E) (K L : Submodule 𝕜 E) : Prop where
  /-- The trial space and the test space have the same dimension. -/
  finrank_eq : finrank 𝕜 K = finrank 𝕜 L
  /-- Every $z \in K$ with $Az \in L^\perp$ is zero. -/
  eq_zero_of_mem_orthogonal : ∀ z ∈ K, A z ∈ Lᗮ → z = 0

namespace IsNondegeneratePair

variable {A : E →ₗ[𝕜] E} {K L : Submodule 𝕜 E}

/-- If $(K, L)$ is a nondegenerate pair for $A$, then $A$ is injective on $K$. -/
theorem injective_domRestrict (h : IsNondegeneratePair A K L) :
    Function.Injective (A.domRestrict K) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  refine Subtype.ext (h.eq_zero_of_mem_orthogonal (z : E) z.2 ?_)
  rw [show A (z : E) = 0 from LinearMap.mem_ker.1 hz]
  exact Submodule.zero_mem _

/-- If $(K, L)$ is a nondegenerate pair for $A$, then $\dim AK = \dim L$. This is one of the two
conditions for the projector onto $AK$ along $L^\perp$ to exist. -/
theorem finrank_map_eq (h : IsNondegeneratePair A K L) :
    finrank 𝕜 (K.map A) = finrank 𝕜 L := by
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj h.injective_domRestrict]
  exact h.finrank_eq

/-- If $(K, L)$ is a nondegenerate pair for $A$, then $AK \cap L^\perp = 0$. This is the second
condition for the projector onto $AK$ along $L^\perp$ to exist. -/
theorem map_inf_orthogonal_eq_bot (h : IsNondegeneratePair A K L) : K.map A ⊓ Lᗮ = ⊥ := by
  refine le_antisymm (fun y hy => ?_) bot_le
  obtain ⟨⟨z, hz, rfl⟩, hy2⟩ := hy
  rw [Submodule.mem_bot, h.eq_zero_of_mem_orthogonal z hz hy2, map_zero]

end IsNondegeneratePair

section Pair

variable (A : E →ₗ[𝕜] E) (b : E) (K L : Submodule 𝕜 E) [FiniteDimensional 𝕜 K]
  [FiniteDimensional 𝕜 L] (h : IsNondegeneratePair A K L)

/-- The **projector of a nondegenerate pair**. Let $(K, L)$ be a nondegenerate pair for
$A : E \to E$, with $K$ and $L$ finite-dimensional. Its projector $P$ is the unique idempotent
linear map of $E$ with range $AK$ and kernel $L^\perp$, the projector onto $AK$ along $L^\perp$.
In bases $V$ of $K$ and $W$ of $L$ it is $P = AV(W^H AV)^{-1} W^H$ ([saad2003iterative],
(5.22)).

The correction of the pair acts on the residual through $P$ (`Projection.apply_pairStep_sub`). -/
noncomputable def pairProjector : E →ₗ[𝕜] E :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot h.finrank_map_eq
    h.map_inf_orthogonal_eq_bot).choose

/-- The projector $P$ of a nondegenerate pair $(K, L)$ for $A$ is idempotent, its range is $AK$, and
its kernel is $L^\perp$. -/
theorem pairProjector_spec :
    IsIdempotentElem (pairProjector A K L h) ∧
      LinearMap.range (pairProjector A K L h) = K.map A ∧
      LinearMap.ker (pairProjector A K L h) = Lᗮ :=
  (LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot h.finrank_map_eq
    h.map_inf_orthogonal_eq_bot).choose_spec.1

/-- Let $(K, L)$ be a nondegenerate pair for $A$. Every idempotent linear map with range $AK$ and
kernel $L^\perp$ is the projector `Projection.pairProjector` of the pair. -/
theorem eq_pairProjector {P : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    (hr : LinearMap.range P = K.map A) (hk : LinearMap.ker P = Lᗮ) :
    P = pairProjector A K L h :=
  LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq hP (pairProjector_spec A K L h).1
    (hr.trans (pairProjector_spec A K L h).2.1.symm)
    (hk.trans (pairProjector_spec A K L h).2.2.symm)

/-- **The projector in bases** ([saad2003iterative], (5.22)). Let $(K, L)$ be a nondegenerate pair
for $A$, with $K$ and $L$ finite-dimensional. Let $V = (v_1, \dots, v_m)$ and
$W = (w_1, \dots, w_m)$ be families in $E$, indexed by the same finite set, that span $K$ and
$L$, and assume that the matrix $W^H A V$, with entries $\langle w_i, A v_j \rangle$, is
invertible. Then the projector of the pair is
$$P = AV (W^H A V)^{-1} W^H.$$

When $V$ and $W$ are bases, $W^H A V$ is invertible because the pair is nondegenerate; the
theorem takes the invertibility as a hypothesis. The matrix $W^H A V$ is `LinearMap.crossGram`
of the families $(Av_j)$ and $(w_i)$, and the right-hand side is
`LinearMap.obliqueProjectionOfBases`. -/
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

/-- **One Petrov–Galerkin step** for a nondegenerate pair $(K, L)$, started from $x$: the unique $y$
with $y - x \in K$ and $b - Ay \perp L$. It exists and is unique by
`existsUnique_isPetrovGalerkin_of_finrank_eq`. This is one inner iteration of
[saad2003iterative], Algorithms 5.5 and 5.6. -/
noncomputable def pairStep (x : E) : E :=
  (existsUnique_isPetrovGalerkin_of_finrank_eq b x K L h.finrank_eq
    h.eq_zero_of_mem_orthogonal).choose

variable {A b K L}

/-- The step `Projection.pairStep` from $x$ satisfies the Petrov–Galerkin condition for
$(A, b, x, K, L)$. -/
theorem pairStep_isPetrovGalerkin (x : E) :
    IsPetrovGalerkin A b x K L (pairStep A b K L h x) :=
  (existsUnique_isPetrovGalerkin_of_finrank_eq b x K L h.finrank_eq
    h.eq_zero_of_mem_orthogonal).choose_spec.1

/-- **The correction acts through the projector** ([saad2003iterative], (5.22)). Let $y$ be the
Petrov–Galerkin step of a nondegenerate pair $(K, L)$ from $x$, and let $P$ be the projector of
the pair. Then
$$A(y - x) = P(b - Ax).$$

This identity turns both the additive and the multiplicative process into statements about
products of projectors. -/
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

/-- Let $y$ be the Petrov–Galerkin step of a nondegenerate pair $(K, L)$ from $x$, and let $P$ be
the projector of the pair. Then the new residual is
$$b - Ay = (I - P)(b - Ax).$$
-/
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

/-- The projector $P_i$ of the $i$-th pair $(K_i, L_i)$ of a family of nondegenerate pairs: the
projector onto $AK_i$ along $L_i^\perp$ ([saad2003iterative], (5.22)). -/
noncomputable def additiveProjector (i : ι) : E →ₗ[𝕜] E := pairProjector A (K i) (L i) (h i)

/-- **One step of the additive projection process** ([saad2003iterative], Algorithm 5.5). Let
$(K_i, L_i)_{i \in I}$ be a finite family of nondegenerate pairs for $A$, with
finite-dimensional spaces, and let $\omega_i$ be relaxation weights. From the iterate $x$, let
$y_i$ be the Petrov–Galerkin step of the $i$-th pair. The new iterate is
$$x + \sum_{i \in I} \omega_i (y_i - x).$$
All the corrections are computed from the same iterate $x$. With $\omega = 1$ and coordinate
subspaces this is block Jacobi. -/
noncomputable def additiveStep (ω : ι → 𝕜) (x : E) : E :=
  x + ∑ i, ω i • (pairStep A b (K i) (L i) (h i) x - x)

variable {A b K L}

/-- **The residual of an additive step** ([saad2003iterative], (5.22)–(5.23)). Let $x'$ be the
additive step from $x$ with weights $\omega$, and let $P_i$ be the projectors of the pairs. Then
$$b - Ax' = \Bigl(I - \sum_{i \in I} \omega_i P_i\Bigr)(b - Ax).$$
-/
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
/-- **The projectors in bases** ([saad2003iterative], (5.22)). Let $V = (v_1, \dots, v_m)$ and
$W = (w_1, \dots, w_m)$ be families in $E$, indexed by the same finite set, that span $K_i$ and
$L_i$, and assume that $W^H A V$ is invertible. Then $P_i = AV(W^H AV)^{-1} W^H$. This is the
family form of `Projection.pairProjector_eq_obliqueProjectionOfBases`. -/
theorem additiveProjector_eq_obliqueProjectionOfBases {κ : Type*} [Fintype κ] [DecidableEq κ]
    (i : ι) (V W : κ → E) (hV : Submodule.span 𝕜 (Set.range V) = K i)
    (hW : Submodule.span 𝕜 (Set.range W) = L i)
    (hVW : IsUnit (LinearMap.crossGram 𝕜 (fun j => A (V j)) W)) :
    additiveProjector A K L h i
      = LinearMap.obliqueProjectionOfBases 𝕜 (fun j => A (V j)) W :=
  (pairProjector_eq_obliqueProjectionOfBases A (K i) (L i) (h i) V W hV hW hVW).symm

omit [Fintype ι] in
/-- **The least-squares choice of test spaces** ([saad2003iterative], the remark after (5.23)). If
$L_i = AK_i$ for every $i$, then each projector $P_i$ is the orthogonal projection onto $AK_i$.
The additive step then adds the orthogonal projections of the residual. -/
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

/-- **Orthogonal projections that sum to the identity** ([saad2003iterative], the remark after
(5.23)). Let $E$ be finite-dimensional, and let $(M_i)_{i \in I}$ be a finite family of
subspaces that are pairwise orthogonal, $M_i \perp M_j$ for $i \neq j$, with
$\sum_i \dim M_i = \dim E$. Then the orthogonal projections $P_{M_i}$ satisfy
$$\sum_{i \in I} P_{M_i} = I.$$
For $M_i = AK_i$ in the least-squares additive process, this says that one step with
$\omega = 1$ solves the system.

The proof does not use a direct sum decomposition. The map $x \mapsto (P_{M_i} x)_i$ into
$\prod_i M_i$ is surjective by the orthogonality, hence injective because the dimensions agree,
and it maps $x - \sum_i P_{M_i} x$ to zero. -/
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

/-- **One sweep of the multiplicative projection process** ([saad2003iterative], Algorithm 5.6). Let
$(K_i, L_i)_{i \in I}$ be a family of nondegenerate pairs for $A$, with finite-dimensional
spaces, and let $l = (i_1, \dots, i_k)$ be a list of indices. Starting from $x$, the sweep
applies the Petrov–Galerkin step of the pair $i_1$, then that of $i_2$, and so on, each from the
iterate that the previous step produced. With coordinate subspaces this is block Gauss–Seidel,
as `Projection.additiveStep` is block Jacobi. -/
noncomputable def multiplicativeStep (l : List ι) (x : E) : E :=
  l.foldl (fun y i => pairStep A b (K i) (L i) (h i) y) x

variable {A b K L}

/-- **The residual of a multiplicative sweep** ([saad2003iterative], §5.4). Let $x'$ be the
multiplicative sweep along $l = (i_1, \dots, i_k)$ from $x$, and let $P_i$ be the projectors of
the pairs. Then
$$b - Ax' = (I - P_{i_k}) \cdots (I - P_{i_1})(b - Ax).$$
-/
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
