/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural homes: `Mathlib.Analysis.Normed.Group.Quotient` (the lift and the uniformly convex
quotient) and `Mathlib.Analysis.Normed.Module.Dual` (the duals of quotients and subspaces).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Module.FiniteCodim

/-!
# The normed quotient of a normed space by a subspace

The quotient `E ⧸ M` of a normed space by a closed subspace `M`, with the quotient norm
`‖[x]‖ = dist (x, M)`, is Mathlib's (`Submodule.Quotient.normedAddCommGroup`, under the
instance argument `[IsClosed (M : Set E)]`; `Submodule.Quotient.normedSpace`,
`Submodule.Quotient.completeSpace`; the projection `Submodule.mkQL` with
`Submodule.Quotient.norm_mk_le`, `QuotientAddGroup.norm_mk` and the near-attained representatives
`Submodule.Quotient.norm_mk_lt`; the lift `Submodule.liftQL`). This module adds what
[brezis2011functional] §11.2 proves about it.

## Main statements

* `Submodule.opNorm_liftQL` — the lift `T̃ : E ⧸ M → F` of `T : E →L[𝕜] F` through a subspace of
  its kernel has the same operator norm, and `Submodule.injective_liftQL_ker`,
  `Submodule.range_liftQL` — through `E ⧸ ker T` it is a bijection onto the range of `T`
  (the factorization `T = T̃ ∘ π`).
* `Submodule.strongDualQuotLIEAnnihilator` — **the dual of a quotient is the annihilator**:
  `(E ⧸ M)* ≃ₗᵢ[𝕜] M^⊥`, `ξ ↦ ξ ∘ π` (Proposition 11.9; the normed version of Mathlib's
  algebraic `Submodule.dualQuotEquivDualAnnihilator`).
* `Submodule.quotAnnihilatorLIEStrongDual` — **the dual of a subspace is the quotient of the dual
  by the annihilator**: `E* ⧸ M^⊥ ≃ₗᵢ[𝕜] M*`, `[f] ↦ f|_M` (Proposition 11.10; the normed
  version of `Subspace.quotAnnihilatorEquiv`). The isometry clause is the distance formula
  `dist (f, M^⊥) = ‖f|_M‖` of `Submodule.infDist_strongDualAnnihilator`.
* `Submodule.Quotient.instIsReflexive` — a quotient of a reflexive space by a closed subspace is
  reflexive (Proposition 11.11), and `Submodule.Quotient.uniformConvexSpace`,
  `Submodule.Quotient.instUniformConvexSpace` — a quotient of a uniformly convex space is
  uniformly convex (Proposition 11.12).
* Propositions 11.13 and 11.14, dimension and codimension: `dim M < ∞ ↔ codim M^⊥ < ∞` with
  `dim M = codim M^⊥` (`finiteDimensional_iff_coFG_strongDualAnnihilator`,
  `finrank_eq_finrank_quotient_strongDualAnnihilator`), `codim M < ∞ ↔ dim M^⊥ < ∞` with
  `codim M = dim M^⊥` for a closed `M` (`coFG_iff_finiteDimensional_strongDualAnnihilator`,
  `finrank_quotient_eq_finrank_strongDualAnnihilator`), and for a subspace `N` of the dual
  `dim N < ∞ ↔ codim N^⊥ < ∞` with `dim N = codim N^⊥`
  (`finiteDimensional_iff_coFG_strongDualCoannihilator`,
  `finrank_eq_finrank_quotient_strongDualCoannihilator`) and `dim N^⊥ ≤ codim N`
  (`finrank_strongDualCoannihilator_le_finrank_quotient`). Finite codimension is Mathlib's
  `Submodule.CoFG` and the codimension is `Module.finrank 𝕜 (E ⧸ M)`; the identity `N^⊥⊥ = N`
  for a finite-dimensional `N ⊆ E*`
  (`strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional`) is the key to 11.14.

## Design

The book's proofs of Propositions 11.11 and 11.12 go through Corollary 3.21 (`E` reflexive iff
`E*` is) and Corollary 3.23 with the Milman–Pettis theorem; both are avoided. Reflexivity of the
quotient is proved directly: a functional on `(E ⧸ M)*` is one on `M^⊥`, extends to `E**` by
Hahn–Banach, is represented by some `x ∈ E` by reflexivity of `E`, and is then evaluation at
`[x]`. Uniform convexity is proved with near-attained representatives of norm `< 1 + η` in place
of the book's exactly attained ones, at the price of a slightly smaller modulus. Uniform
convexity is a statement about the real structure, so the general theorem asks for
`[NormedSpace ℝ E]` and the instance is over `RCLike 𝕜`, where the real structure is
`NormedSpace.restrictScalars`.

Scalars are `RCLike 𝕜` where Hahn–Banach enters (Propositions 11.10, 11.11, 11.13, 11.14) and a
nontrivially normed field elsewhere (the factorization, Proposition 11.9). The quotient
`E ⧸ M` is taken with `[IsClosed (M : Set E)]` wherever it must be a normed (not merely
seminormed) space; the annihilator `M^⊥` is closed, and that closedness is registered as an
instance here so that `E* ⧸ M^⊥` is a normed space by instance search.
-/

open Metric Module

noncomputable section

namespace Submodule

/-! ### The factorization `T = T̃ ∘ π` -/

section Lift

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The projection onto a quotient has operator norm at most one. -/
theorem opNorm_mkQL_le (M : Submodule 𝕜 E) : ‖M.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    simpa using Submodule.Quotient.norm_mk_le M y

/-- A bounded operator vanishing on `M` is bounded by its norm times the quotient norm:
`‖f x‖ ≤ ‖f‖ * ‖[x]‖`, since `f x = f (x - m)` for every `m ∈ M`. -/
theorem norm_apply_le_opNorm_mul_norm_mk {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker)
    (x : E) : ‖f x‖ ≤ ‖f‖ * ‖(Submodule.Quotient.mk x : E ⧸ M)‖ := by
  have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ M)‖ = infDist x (M : Set E) :=
    QuotientAddGroup.norm_mk (S := M.toAddSubgroup) x
  rw [hnorm, infDist_eq_iInf, Real.mul_iInf_of_nonneg (norm_nonneg f)]
  have : Nonempty (M : Set E) := ⟨⟨0, M.zero_mem⟩⟩
  refine le_ciInf fun z => ?_
  have hz : f z = 0 := h z.2
  rw [dist_eq_norm, ← sub_zero (f x), ← hz, ← map_sub]
  exact f.le_opNorm _

/-- **The lift through a quotient keeps the operator norm**: for `f : E →L[𝕜] F` vanishing on
`M`, `‖M.liftQL f h‖ = ‖f‖` ([brezis2011functional] §11.2, the factorization paragraph; the book
prints `‖T‖ = ‖T‖` for `‖T̃‖ = ‖T‖`). `≤` because `‖f x‖ ≤ ‖f‖ ‖[x]‖`, `≥` because
`f = (M.liftQL f h) ∘ π` and `‖π‖ ≤ 1`. -/
theorem opNorm_liftQL {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker) :
    ‖M.liftQL f h‖ = ‖f‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) fun x => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    exact norm_apply_le_opNorm_mul_norm_mk f h y
  · calc ‖f‖ = ‖(M.liftQL f h).comp M.mkQL‖ := congrArg norm (by ext; rfl)
      _ ≤ ‖M.liftQL f h‖ * ‖M.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖M.liftQL f h‖ * 1 := by gcongr; exact opNorm_mkQL_le M
      _ = ‖M.liftQL f h‖ := mul_one _

/-- The lift of `f ∘ π` through `E ⧸ M` is `f` again. -/
theorem liftQL_comp_mkQL (M : Submodule 𝕜 E) (f : E ⧸ M →L[𝕜] F) (h : M ≤ (f.comp M.mkQL).ker) :
    M.liftQL (f.comp M.mkQL) h = f := by
  ext x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
  rfl

/-- The range of the lift is the range of the operator. -/
theorem range_liftQL {M : Submodule 𝕜 E} (f : E →L[𝕜] F) (h : M ≤ f.ker) :
    LinearMap.range (M.liftQL f h : E ⧸ M →ₗ[𝕜] F) = LinearMap.range (f : E →ₗ[𝕜] F) :=
  range_liftQ M (f : E →ₗ[𝕜] F) h

/-- **The lift of `f` through `E ⧸ ker f` is injective**, so `T̃` is a bijection of `E ⧸ N(T)`
onto `R(T)` ([brezis2011functional] §11.2, the factorization paragraph). -/
theorem injective_liftQL_ker (f : E →L[𝕜] F) : Function.Injective (f.ker.liftQL f le_rfl) :=
  LinearMap.ker_eq_bot.1 (ker_liftQ_eq_bot f.ker (f : E →ₗ[𝕜] F) le_rfl le_rfl)

end Lift

/-! ### The dual of a quotient -/

section DualQuotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The composite `ξ ∘ π` of a functional on the quotient with the projection vanishes on `M`. -/
theorem comp_mkQL_mem_strongDualAnnihilator (M : Submodule 𝕜 E) (ξ : StrongDual 𝕜 (E ⧸ M)) :
    ξ.comp M.mkQL ∈ M.strongDualAnnihilator :=
  mem_strongDualAnnihilator.2 fun x hx => by
    rw [ContinuousLinearMap.comp_apply, mkQL_apply, mkQ_apply,
      (Submodule.Quotient.mk_eq_zero M).2 hx, map_zero]

/-- **The dual of a quotient is the annihilator** ([brezis2011functional] Proposition 11.9): for
a closed subspace `M` of a normed space, `ξ ↦ ξ ∘ π` is an isometric isomorphism of `(E ⧸ M)*`
onto `M^⊥`. The inverse descends `f ∈ M^⊥` through the quotient (`Submodule.liftQL`), and the
norm is preserved because `‖ξ ∘ π‖ ≤ ‖ξ‖ ‖π‖ ≤ ‖ξ‖` while `ξ` is the lift of `ξ ∘ π`
(`Submodule.opNorm_liftQL`). No Hahn–Banach is needed. This is the normed version of Mathlib's
`Submodule.dualQuotEquivDualAnnihilator`. -/
def strongDualQuotLIEAnnihilator (M : Submodule 𝕜 E) [IsClosed (M : Set E)] :
    StrongDual 𝕜 (E ⧸ M) ≃ₗᵢ[𝕜] M.strongDualAnnihilator :=
  LinearIsometryEquiv.ofSurjective
    { toFun := fun ξ => ⟨ξ.comp M.mkQL, comp_mkQL_mem_strongDualAnnihilator M ξ⟩
      map_add' := fun ξ η => Subtype.ext (ContinuousLinearMap.add_comp _ _ _)
      map_smul' := fun c ξ => Subtype.ext (ContinuousLinearMap.smul_comp _ _ _)
      norm_map' := fun ξ => by
        change ‖ξ.comp M.mkQL‖ = ‖ξ‖
        refine le_antisymm ?_ ?_
        · calc ‖ξ.comp M.mkQL‖ ≤ ‖ξ‖ * ‖M.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ ‖ξ‖ * 1 := by gcongr; exact opNorm_mkQL_le M
            _ = ‖ξ‖ := mul_one _
        · have h : M ≤ (ξ.comp M.mkQL).ker := fun x hx =>
            comp_mkQL_mem_strongDualAnnihilator M ξ |> mem_strongDualAnnihilator.1 |> (· x hx)
          rw [← opNorm_liftQL (ξ.comp M.mkQL) h, liftQL_comp_mkQL] }
    fun f => ⟨M.liftQL (f : StrongDual 𝕜 E) fun x hx => mem_strongDualAnnihilator.1 f.2 x hx,
      Subtype.ext (by ext; rfl)⟩

/-- `⟨π* ξ, x⟩ = ⟨ξ, π x⟩`: the image of `ξ` under `strongDualQuotLIEAnnihilator` is the
functional `ξ ∘ π` ([brezis2011functional] Proposition 11.9, the defining relation of the
adjoint of the projection; `ContinuousLinearMap.strongDualMap M.mkQL ξ` is the same functional).
-/
@[simp]
theorem strongDualQuotLIEAnnihilator_apply (M : Submodule 𝕜 E) [IsClosed (M : Set E)]
    (ξ : StrongDual 𝕜 (E ⧸ M)) :
    (M.strongDualQuotLIEAnnihilator ξ : StrongDual 𝕜 E) = ξ.comp M.mkQL :=
  rfl

/-- The inverse of `strongDualQuotLIEAnnihilator` is the lift through the quotient. -/
theorem strongDualQuotLIEAnnihilator_symm_apply (M : Submodule 𝕜 E) [IsClosed (M : Set E)]
    (f : M.strongDualAnnihilator) :
    M.strongDualQuotLIEAnnihilator.symm f =
      M.liftQL (f : StrongDual 𝕜 E) fun x hx => mem_strongDualAnnihilator.1 f.2 x hx := by
  apply M.strongDualQuotLIEAnnihilator.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact Subtype.ext (by ext; rfl)

end DualQuotient

/-! ### The dual of a subspace -/

section DualSubspace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The annihilator is closed, as an instance, so that `StrongDual 𝕜 E ⧸ M.strongDualAnnihilator`
is a normed space by instance search. -/
instance instIsClosedStrongDualAnnihilator (M : Submodule 𝕜 E) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) :=
  isClosed_strongDualAnnihilator M

/-- The coannihilator is closed, as an instance, so that `E ⧸ N.strongDualCoannihilator` is a
normed space by instance search. -/
instance instIsClosedStrongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    IsClosed (N.strongDualCoannihilator : Set E) :=
  isClosed_strongDualCoannihilator N

/-- **The kernel of restriction to `M` is the annihilator**: for the restriction map
`f ↦ f ∘ M.subtypeL` (Mathlib's `ContinuousLinearMap.precomp 𝕜 M.subtypeL`),
`N(T) = M^⊥` ([brezis2011functional] §11.2, the paragraph before Proposition 11.10). -/
theorem ker_comp_subtypeL_eq_strongDualAnnihilator (M : Submodule 𝕜 E) :
    (ContinuousLinearMap.precomp 𝕜 M.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 M).ker =
      M.strongDualAnnihilator := by
  ext f
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_strongDualAnnihilator,
    ContinuousLinearMap.ext_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

end DualSubspace

section DualSubspaceRCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Restriction of functionals to a subspace is onto**, "`R(T) = M*` by Hahn–Banach"
([brezis2011functional] §11.2): every functional on `M` is the restriction of one on `E`
(`exists_extension_norm_eq`, with the norm clause dropped). -/
theorem surjective_comp_subtypeL (M : Submodule 𝕜 E) :
    Function.Surjective fun f : StrongDual 𝕜 E => f.comp M.subtypeL := by
  intro g
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq M g
  exact ⟨f, ContinuousLinearMap.ext fun x => hf x⟩

/-- **The dual of a subspace is the quotient of the dual by the annihilator**
([brezis2011functional] Proposition 11.10): restriction of functionals to `M` descends to an
isometric isomorphism `E* ⧸ M^⊥ ≃ₗᵢ[𝕜] M*`, `[f] ↦ f|_M`. It is onto by Hahn–Banach
(`surjective_comp_subtypeL`), and isometric because `‖[f]‖ = dist (f, M^⊥) = ‖f|_M‖`
(`Submodule.infDist_strongDualAnnihilator`). Neither closedness of `M` nor completeness of `E`
is used. This is the normed version of Mathlib's `Subspace.quotAnnihilatorEquiv`. -/
def quotAnnihilatorLIEStrongDual (M : Submodule 𝕜 E) :
    (StrongDual 𝕜 E ⧸ M.strongDualAnnihilator) ≃ₗᵢ[𝕜] StrongDual 𝕜 M :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (M.strongDualAnnihilator.liftQL
        (ContinuousLinearMap.precomp 𝕜 M.subtypeL : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 M)
        (ker_comp_subtypeL_eq_strongDualAnnihilator M).ge).toLinearMap
      norm_map' := fun x => by
        obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective M.strongDualAnnihilator x
        change ‖f.comp M.subtypeL‖ = ‖(Submodule.Quotient.mk f : _ ⧸ M.strongDualAnnihilator)‖
        have hnorm : ‖(Submodule.Quotient.mk f : _ ⧸ M.strongDualAnnihilator)‖ =
            infDist f (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) :=
          QuotientAddGroup.norm_mk (S := M.strongDualAnnihilator.toAddSubgroup) f
        rw [hnorm, infDist_strongDualAnnihilator] }
    fun g => by
      obtain ⟨f, hf⟩ := surjective_comp_subtypeL M g
      exact ⟨Submodule.Quotient.mk f, hf⟩

/-- The isomorphism `E* ⧸ M^⊥ ≃ M*` sends the class of `f` to its restriction `f|_M`. -/
@[simp]
theorem quotAnnihilatorLIEStrongDual_apply_mk (M : Submodule 𝕜 E) (f : StrongDual 𝕜 E) :
    M.quotAnnihilatorLIEStrongDual (Submodule.Quotient.mk f) = f.comp M.subtypeL :=
  rfl

end DualSubspaceRCLike

/-! ### Reflexivity and uniform convexity of a quotient -/

section Reflexive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A quotient of a reflexive space by a closed subspace is reflexive**
([brezis2011functional] Proposition 11.11). Direct proof, without the book's detour through
Corollary 3.21: a functional `Φ` on `(E ⧸ M)*` is a functional on `M^⊥ ⊆ E*` along
`strongDualQuotLIEAnnihilator`, extends to `E**` by Hahn–Banach, is represented by some `x ∈ E`
by reflexivity of `E`, and is then evaluation at `[x]`. -/
instance Quotient.instIsReflexive [NormedSpace.IsReflexive 𝕜 E] (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : NormedSpace.IsReflexive 𝕜 (E ⧸ M) := by
  refine ⟨fun Φ => ?_⟩
  set e := M.strongDualQuotLIEAnnihilator
  obtain ⟨Ψ, hΨ, -⟩ := exists_extension_norm_eq M.strongDualAnnihilator
    (Φ.comp (e.symm.toContinuousLinearEquiv : M.strongDualAnnihilator →L[𝕜] StrongDual 𝕜 (E ⧸ M)))
  obtain ⟨x, hx⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) (V := E) Ψ
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  ext ξ
  have h1 := hΨ (e ξ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply] at h1
  rw [NormedSpace.dual_def, ← h1, ← hx, NormedSpace.dual_def, strongDualQuotLIEAnnihilator_apply]
  rfl

end Reflexive

section UniformConvex

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A quotient of a uniformly convex space is uniformly convex**
([brezis2011functional] Proposition 11.12), for a normed space `E` carrying a real structure
(uniform convexity is a statement about real scalar multiples). The subspace is closed or not;
the quotient is then seminormed.

The book takes representatives of norm exactly `≤ 1` (Corollary 3.23, hence reflexivity of `E`
by Milman–Pettis); here representatives `x'`, `y'` of norm `< 1 + η`
(`Submodule.Quotient.norm_mk_lt`) are rescaled by `(1 + η)⁻¹` and fed to the closed-ball form
of uniform convexity in `E` at `ε / 2`, which gives `‖x' + y'‖ ≤ (1 + η) (2 - δ)`; with
`η = δ / 4` (and `δ ≤ 1`) this is at most `2 - δ / 2`, the modulus of the quotient. -/
theorem Quotient.uniformConvexSpace [NormedSpace ℝ E] [UniformConvexSpace E] (M : Submodule 𝕜 E) :
    UniformConvexSpace (E ⧸ M) := by
  refine ⟨fun ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (half_pos hε)
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  refine ⟨δ' / 2, half_pos hδ'0, fun x hx y hy hxy => ?_⟩
  have hη0 : 0 < δ' / 4 := by positivity
  obtain ⟨x', rfl, hx'⟩ := Submodule.Quotient.norm_mk_lt x hη0
  obtain ⟨y', rfl, hy'⟩ := Submodule.Quotient.norm_mk_lt y hη0
  rw [hx] at hx'
  rw [hy] at hy'
  have hpos : 0 < 1 + δ' / 4 := by linarith
  have hinv : 0 < (1 + δ' / 4)⁻¹ := inv_pos.2 hpos
  have ha : ‖(1 + δ' / 4)⁻¹ • x'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos, mul_one]
    exact hx'.le
  have hb : ‖(1 + δ' / 4)⁻¹ • y'‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos, mul_one]
    exact hy'.le
  have hab : ε / 2 ≤ ‖(1 + δ' / 4)⁻¹ • x' - (1 + δ' / 4)⁻¹ • y'‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    have h1 : ε ≤ ‖x' - y'‖ := by
      refine hxy.trans ?_
      rw [← Submodule.Quotient.mk_sub]
      exact Submodule.Quotient.norm_mk_le M _
    calc ε / 2 = 2⁻¹ * ε := div_eq_inv_mul ε 2
      _ ≤ (1 + δ' / 4)⁻¹ * ε := by gcongr; linarith
      _ ≤ (1 + δ' / 4)⁻¹ * ‖x' - y'‖ := by gcongr
  have hsum := h ha hb hab
  rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos hinv, inv_mul_le_iff₀ hpos] at hsum
  calc ‖(Submodule.Quotient.mk x' : E ⧸ M) + Submodule.Quotient.mk y'‖
      = ‖(Submodule.Quotient.mk (x' + y') : E ⧸ M)‖ := by rw [Submodule.Quotient.mk_add]
    _ ≤ ‖x' + y'‖ := Submodule.Quotient.norm_mk_le M _
    _ ≤ (1 + δ' / 4) * (2 - δ) := hsum
    _ ≤ 2 - δ' / 2 := by nlinarith [mul_nonneg hδ'0.le hδ.le]

/-- **A quotient of a uniformly convex space over `RCLike 𝕜` is uniformly convex**
([brezis2011functional] Proposition 11.12), the instance form of
`Submodule.Quotient.uniformConvexSpace` with the real structure `NormedSpace.restrictScalars`. -/
instance Quotient.instUniformConvexSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [UniformConvexSpace E] (M : Submodule 𝕜 E) :
    UniformConvexSpace (E ⧸ M) :=
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  Quotient.uniformConvexSpace M

end UniformConvex

/-! ### Dimension and codimension -/

section Dimension

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **`dim M < ∞ ⟺ codim M^⊥ < ∞`** ([brezis2011functional] Proposition 11.13 (a), first
clause), for any subspace `M` of a normed space over `RCLike 𝕜`: `E* ⧸ M^⊥ ≅ M*` and
Proposition 11.3. -/
theorem finiteDimensional_iff_coFG_strongDualAnnihilator (M : Submodule 𝕜 E) :
    FiniteDimensional 𝕜 M ↔ M.strongDualAnnihilator.CoFG := by
  constructor
  · intro _
    exact M.quotAnnihilatorLIEStrongDual.toLinearEquiv.symm.finiteDimensional
  · intro _
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 M) :=
      M.quotAnnihilatorLIEStrongDual.toLinearEquiv.finiteDimensional
    exact NormedSpace.finiteDimensional_of_finiteDimensional_strongDual

/-- **`dim M = codim M^⊥`** ([brezis2011functional] Proposition 11.13 (a), second clause), for
any subspace `M` of a normed space over `RCLike 𝕜`; both sides are `0` when infinite. -/
theorem finrank_eq_finrank_quotient_strongDualAnnihilator (M : Submodule 𝕜 E) :
    finrank 𝕜 M = finrank 𝕜 (StrongDual 𝕜 E ⧸ M.strongDualAnnihilator) := by
  by_cases h : FiniteDimensional 𝕜 M
  · rw [← NormedSpace.finrank_strongDual, M.quotAnnihilatorLIEStrongDual.toLinearEquiv.finrank_eq]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (M.finiteDimensional_iff_coFG_strongDualAnnihilator.not.1 h)]

/-- **`codim M < ∞ ⟺ dim M^⊥ < ∞`** ([brezis2011functional] Proposition 11.13 (b), first
clause), for a closed subspace `M` of a normed space over `RCLike 𝕜`: `(E ⧸ M)* ≅ M^⊥` and
Proposition 11.3 for the normed space `E ⧸ M`. -/
theorem coFG_iff_finiteDimensional_strongDualAnnihilator (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : M.CoFG ↔ FiniteDimensional 𝕜 M.strongDualAnnihilator := by
  constructor
  · intro _
    exact M.strongDualQuotLIEAnnihilator.toLinearEquiv.finiteDimensional
  · intro _
    have : FiniteDimensional 𝕜 (StrongDual 𝕜 (E ⧸ M)) :=
      M.strongDualQuotLIEAnnihilator.toLinearEquiv.symm.finiteDimensional
    exact NormedSpace.finiteDimensional_of_finiteDimensional_strongDual

/-- **`codim M = dim M^⊥`** ([brezis2011functional] Proposition 11.13 (b), second clause), for a
closed subspace `M` of a normed space over `RCLike 𝕜`; both sides are `0` when infinite. -/
theorem finrank_quotient_eq_finrank_strongDualAnnihilator (M : Submodule 𝕜 E)
    [IsClosed (M : Set E)] : finrank 𝕜 (E ⧸ M) = finrank 𝕜 M.strongDualAnnihilator := by
  by_cases h : FiniteDimensional 𝕜 (E ⧸ M)
  · rw [← NormedSpace.finrank_strongDual, M.strongDualQuotLIEAnnihilator.toLinearEquiv.finrank_eq]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (M.coFG_iff_finiteDimensional_strongDualAnnihilator.not.1 h)]

/-- **`N^⊥⊥ = N` for a finite-dimensional subspace `N` of the dual** (the claim inside the
proof of [brezis2011functional] Proposition 11.14; in general only the weak-∗ closure of `N`
is recovered). A functional vanishing on `N^⊥ = ⋂ᵢ ker fᵢ`, for a basis `fᵢ` of `N`, is a
linear combination of the `fᵢ` (`mem_span_of_iInf_ker_le_ker`, the book's Lemma 3.2). -/
theorem strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) [FiniteDimensional 𝕜 N] :
    N.strongDualCoannihilator.strongDualAnnihilator = N := by
  refine le_antisymm (fun f hf => ?_) (le_strongDualCoannihilator_strongDualAnnihilator N)
  let b := Module.finBasis 𝕜 N
  -- `N` is spanned by the basis, seen in `E*`
  have hN : N = span 𝕜 (Set.range fun i => (b i : StrongDual 𝕜 E)) := by
    rw [show (fun i => (b i : StrongDual 𝕜 E)) = N.subtype ∘ b from rfl, Set.range_comp,
      ← map_span, b.span_eq, map_subtype_top]
  -- `f` vanishes on `⋂ᵢ ker (b i) = N^⊥`, hence lies in the span of the `b i` as a linear map
  have hker : ⨅ i, LinearMap.ker ((b i : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜) ≤
      LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := by
    intro x hx
    rw [mem_iInf] at hx
    refine mem_strongDualAnnihilator.1 hf x (mem_strongDualCoannihilator.2 fun g hg => ?_)
    have hg' : g ∈ span 𝕜 (Set.range fun i => (b i : StrongDual 𝕜 E)) := hN ▸ hg
    refine span_induction (fun g ⟨i, hi⟩ => ?_) (by simp) (fun g₁ g₂ _ _ h₁ h₂ => ?_)
      (fun c g _ h => ?_) hg'
    · rw [← hi]; exact hx i
    · simp [h₁, h₂]
    · simp [h]
  have hspan := mem_span_of_iInf_ker_le_ker hker
  rw [show (fun i => ((b i : StrongDual 𝕜 E) : E →ₗ[𝕜] 𝕜)) =
      (ContinuousLinearMap.coeLM 𝕜) ∘ fun i => (b i : StrongDual 𝕜 E) from rfl, Set.range_comp,
    ← map_span, mem_map] at hspan
  obtain ⟨g, hg, hgf⟩ := hspan
  rw [hN]
  exact ContinuousLinearMap.coe_injective hgf ▸ hg

/-- **`dim N < ∞ ⟺ codim N^⊥ < ∞`** ([brezis2011functional] Proposition 11.14, first clause)
for a subspace `N` of the dual of a normed space over `RCLike 𝕜` (the book assumes `N` closed
and `E` complete; neither is used). With `M := N^⊥`, closed, `M^⊥ = N` when `N` is
finite-dimensional and `N ≤ M^⊥` always. -/
theorem finiteDimensional_iff_coFG_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    FiniteDimensional 𝕜 N ↔ N.strongDualCoannihilator.CoFG := by
  constructor
  · intro _
    rw [coFG_iff_finiteDimensional_strongDualAnnihilator,
      strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional]
    infer_instance
  · intro h
    have : FiniteDimensional 𝕜 N.strongDualCoannihilator.strongDualAnnihilator :=
      (coFG_iff_finiteDimensional_strongDualAnnihilator _).1 h
    exact finiteDimensional_of_le (le_strongDualCoannihilator_strongDualAnnihilator N)

/-- **`dim N = codim N^⊥`** ([brezis2011functional] Proposition 11.14, second clause) for a
subspace `N` of the dual of a normed space over `RCLike 𝕜`; both sides are `0` when infinite. -/
theorem finrank_eq_finrank_quotient_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    finrank 𝕜 N = finrank 𝕜 (E ⧸ N.strongDualCoannihilator) := by
  by_cases h : FiniteDimensional 𝕜 N
  · rw [finrank_quotient_eq_finrank_strongDualAnnihilator,
      strongDualAnnihilator_strongDualCoannihilator_of_finiteDimensional]
  · rw [finrank_of_infinite_dimensional h, finrank_of_infinite_dimensional
      (N.finiteDimensional_iff_coFG_strongDualCoannihilator.not.1 h)]

/-- The coannihilator of a subspace of finite codimension in the dual is finite-dimensional
([brezis2011functional] Proposition 11.14, third clause, the finiteness): `N ≤ (N^⊥)^⊥`, so
`(N^⊥)^⊥` has finite codimension too, and Proposition 11.13 (a) applies to `N^⊥`. -/
theorem finiteDimensional_strongDualCoannihilator_of_coFG (N : Submodule 𝕜 (StrongDual 𝕜 E))
    [N.CoFG] : FiniteDimensional 𝕜 N.strongDualCoannihilator :=
  (finiteDimensional_iff_coFG_strongDualAnnihilator _).2
    (CoFG.of_le (le_strongDualCoannihilator_strongDualAnnihilator N) ‹N.CoFG›)

/-- **`dim N^⊥ ≤ codim N`** ([brezis2011functional] Proposition 11.14, third clause) for a
subspace `N` of finite codimension in the dual of a normed space over `RCLike 𝕜`. The
inequality can be strict when `E` is not reflexive (a hyperplane `N = ker ξ` for
`ξ ∈ E** ∖ J(E)` has `N^⊥ = 0`). Since `N ≤ (N^⊥)^⊥`, the quotient `E* ⧸ (N^⊥)^⊥` is a quotient
of `E* ⧸ N`, and `dim N^⊥ = codim (N^⊥)^⊥` by Proposition 11.13 (a). -/
theorem finrank_strongDualCoannihilator_le_finrank_quotient (N : Submodule 𝕜 (StrongDual 𝕜 E))
    [N.CoFG] :
    finrank 𝕜 N.strongDualCoannihilator ≤ finrank 𝕜 (StrongDual 𝕜 E ⧸ N) := by
  rw [finrank_eq_finrank_quotient_strongDualAnnihilator]
  exact LinearMap.finrank_le_finrank_of_surjective
    (factor_surjective (le_strongDualCoannihilator_strongDualAnnihilator N))

end Dimension

end Submodule

end
