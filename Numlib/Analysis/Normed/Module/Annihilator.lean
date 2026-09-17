/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Module.Dual`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Numlib.Analysis.Normed.Module.Reflexive

/-!
# Annihilators in the strong dual

For a subspace `M` of a topological vector space `E` over a nontrivially normed field `𝕜`, the
**annihilator** `M^⊥ = {f ∈ E* | f = 0 on M}` is a closed subspace of the strong dual
`E* = StrongDual 𝕜 E`; for a subspace `N` of `E*`, the **coannihilator**
`N^⊥ = {x ∈ E | f x = 0 for all f ∈ N}` is a closed subspace of `E` itself (not of `E**`). These
are the orthogonality relations of [brezis2011functional] §1.3 and §2.5, and the vocabulary in
which the kernel/range relations of Banach adjoints, the closed range theorem, the Fredholm
alternative and the duals of quotients and subspaces are stated.

Mathlib has both objects unnamed: `M^⊥` is `StrongDual.polarSubmodule 𝕜 M` and `N^⊥` is
`(topDualPairing 𝕜 E).polarSubmodule N` (the polar of a set closed under scalars is its
annihilator, `LinearMap.polar_subMulAction`). They are thin definitions here, with the bridges
`strongDualAnnihilator_eq_polarSubmodule` and `strongDualCoannihilator_eq_polarSubmodule`,
because Mathlib's API for `polarSubmodule` stops at membership and everything below is new. The
names follow Mathlib's algebraic pair `Submodule.dualAnnihilator` / `Submodule.dualCoannihilator`
(which live in the algebraic dual `Module.Dual` and are not the same objects); the name
`Submodule.annihilator` is Mathlib's ideal-valued annihilator and is not used.

## Main statements

* `Submodule.strongDualAnnihilator`, `Submodule.strongDualCoannihilator` with `mem_`, `isClosed_`,
  the antitone Galois connection `le_strongDualAnnihilator_iff_le_strongDualCoannihilator`, the
  `_sup`, `_bot`, `_top` identities and the invariance under `topologicalClosure`.
* `Submodule.strongDualCoannihilator_strongDualAnnihilator` — **`(M^⊥)^⊥ = closure M`** for every
  subspace `M` of a normed space over `RCLike 𝕜`, and
  `topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator` — `(N^⊥)^⊥ ⊇ closure N`
  ([brezis2011functional], Proposition 1.9), with equality when `E` is reflexive
  (`strongDualAnnihilator_strongDualCoannihilator`, its Remark 6).
* `Submodule.strongDualAnnihilator_eq_bot_iff` — `M^⊥ = 0` iff `M` is dense (Corollary 1.8).
* `Submodule.strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed`,
  `strongDualAnnihilator_sup`, `topologicalClosure_sup_strongDualAnnihilator_le`,
  `strongDualCoannihilator_inf_strongDualAnnihilator` — the sum and intersection formulas
  `G ∩ L = (G^⊥ + L^⊥)^⊥`, `(G + L)^⊥ = G^⊥ ∩ L^⊥`, `(G ∩ L)^⊥ ⊇ closure (G^⊥ + L^⊥)` and
  `(G^⊥ ∩ L^⊥)^⊥ = closure (G + L)` (Proposition 2.14 and Corollary 2.15; only the first needs
  `G`, `L` closed).
* `Submodule.infDist_strongDualAnnihilator` — `dist (f, M^⊥) = ‖f|_M‖`, and
  `exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist` — `dist (x, M)` is attained as
  `f x` for some `f ∈ M^⊥` with `‖f‖ ≤ 1` (the two distance formulas, by Hahn–Banach).

The characterization of "`G + L` closed" through `G^⊥ + L^⊥` ([brezis2011functional],
Theorem 2.16) is in the child module `Numlib.Analysis.Normed.Module.Annihilator.ClosedSum`, so
that this module imports nothing of the open mapping theorem.
-/

open Metric

namespace Submodule

section Definitions

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- The **annihilator** `M^⊥` of a subspace `M` of a topological vector space `E`: the subspace
`{f : StrongDual 𝕜 E | ∀ x ∈ M, f x = 0}` of the strong dual. It is Mathlib's
`StrongDual.polarSubmodule 𝕜 M`. -/
def strongDualAnnihilator (M : Submodule 𝕜 E) : Submodule 𝕜 (StrongDual 𝕜 E) :=
  StrongDual.polarSubmodule 𝕜 M

/-- A functional lies in `M^⊥` iff it vanishes on `M`. -/
@[simp]
theorem mem_strongDualAnnihilator {M : Submodule 𝕜 E} {f : StrongDual 𝕜 E} :
    f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, f x = 0 :=
  StrongDual.mem_polarSubmodule 𝕜 M f

/-- The annihilator is Mathlib's polar submodule of `M` in the strong dual. -/
theorem strongDualAnnihilator_eq_polarSubmodule (M : Submodule 𝕜 E) :
    M.strongDualAnnihilator = StrongDual.polarSubmodule 𝕜 M :=
  rfl

/-- The **coannihilator** `N^⊥` of a subspace `N` of the strong dual: the subspace
`{x : E | ∀ f ∈ N, f x = 0}` of `E` itself (not of the bidual). It is Mathlib's
`(topDualPairing 𝕜 E).polarSubmodule N`, the polar on the other side of the pairing. -/
def strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) : Submodule 𝕜 E :=
  (topDualPairing 𝕜 E).polarSubmodule N

/-- A vector lies in `N^⊥` iff every functional of `N` vanishes on it. -/
@[simp]
theorem mem_strongDualCoannihilator {N : Submodule 𝕜 (StrongDual 𝕜 E)} {x : E} :
    x ∈ N.strongDualCoannihilator ↔ ∀ f ∈ N, f x = 0 := by
  change x ∈ (topDualPairing 𝕜 E).polarSubmodule N ↔ _
  simp [LinearMap.polarSubmodule, Submodule.copy_eq, Submodule.mem_iInf]

/-- The coannihilator is Mathlib's polar submodule of `N` under the pairing of `E*` with `E`. -/
theorem strongDualCoannihilator_eq_polarSubmodule (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.strongDualCoannihilator = (topDualPairing 𝕜 E).polarSubmodule N :=
  rfl

/-- The coannihilator is the intersection of the kernels of the functionals of `N`. -/
theorem strongDualCoannihilator_eq_iInf_ker (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.strongDualCoannihilator = ⨅ f ∈ N, LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := by
  ext x
  simp [mem_strongDualCoannihilator, Submodule.mem_iInf]

/-- The antitone Galois connection between subspaces of `E` and of `E*`:
`N ≤ M^⊥ ↔ M ≤ N^⊥` (both say that every `f ∈ N` kills every `x ∈ M`). -/
theorem le_strongDualAnnihilator_iff_le_strongDualCoannihilator {M : Submodule 𝕜 E}
    {N : Submodule 𝕜 (StrongDual 𝕜 E)} :
    N ≤ M.strongDualAnnihilator ↔ M ≤ N.strongDualCoannihilator := by
  constructor
  · intro h x hx
    exact mem_strongDualCoannihilator.2 fun f hf => mem_strongDualAnnihilator.1 (h hf) x hx
  · intro h f hf
    exact mem_strongDualAnnihilator.2 fun x hx => mem_strongDualCoannihilator.1 (h hx) f hf

/-- Taking annihilators reverses inclusions: `M₁ ≤ M₂ → M₂^⊥ ≤ M₁^⊥`. -/
theorem strongDualAnnihilator_anti {M₁ M₂ : Submodule 𝕜 E} (h : M₁ ≤ M₂) :
    M₂.strongDualAnnihilator ≤ M₁.strongDualAnnihilator := fun _ hf =>
  mem_strongDualAnnihilator.2 fun x hx => mem_strongDualAnnihilator.1 hf x (h hx)

/-- Taking coannihilators reverses inclusions: `N₁ ≤ N₂ → N₂^⊥ ≤ N₁^⊥`. -/
theorem strongDualCoannihilator_anti {N₁ N₂ : Submodule 𝕜 (StrongDual 𝕜 E)} (h : N₁ ≤ N₂) :
    N₂.strongDualCoannihilator ≤ N₁.strongDualCoannihilator := fun _ hx =>
  mem_strongDualCoannihilator.2 fun f hf => mem_strongDualCoannihilator.1 hx f (h hf)

/-- `M ≤ (M^⊥)^⊥`: the unit of the Galois connection. -/
theorem le_strongDualAnnihilator_strongDualCoannihilator (M : Submodule 𝕜 E) :
    M ≤ M.strongDualAnnihilator.strongDualCoannihilator :=
  le_strongDualAnnihilator_iff_le_strongDualCoannihilator.1 le_rfl

/-- `N ≤ (N^⊥)^⊥`: the counit of the Galois connection. -/
theorem le_strongDualCoannihilator_strongDualAnnihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  le_strongDualAnnihilator_iff_le_strongDualCoannihilator.2 le_rfl

/-- `(M₁ + M₂)^⊥ = M₁^⊥ ∩ M₂^⊥` for arbitrary subspaces ([brezis2011functional],
Proposition 2.14, formula (17); no closedness is needed). -/
theorem strongDualAnnihilator_sup (M₁ M₂ : Submodule 𝕜 E) :
    (M₁ ⊔ M₂).strongDualAnnihilator = M₁.strongDualAnnihilator ⊓ M₂.strongDualAnnihilator := by
  ext f
  simp only [mem_strongDualAnnihilator, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun x hx => h x (mem_sup_left hx), fun x hx => h x (mem_sup_right hx)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hx
    rw [map_add, h₁ y hy, h₂ z hz, add_zero]

/-- `(N₁ + N₂)^⊥ = N₁^⊥ ∩ N₂^⊥` for arbitrary subspaces of the dual. -/
theorem strongDualCoannihilator_sup (N₁ N₂ : Submodule 𝕜 (StrongDual 𝕜 E)) :
    (N₁ ⊔ N₂).strongDualCoannihilator =
      N₁.strongDualCoannihilator ⊓ N₂.strongDualCoannihilator := by
  ext x
  simp only [mem_strongDualCoannihilator, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨fun f hf => h f (mem_sup_left hf), fun f hf => h f (mem_sup_right hf)⟩
  · rintro ⟨h₁, h₂⟩ f hf
    obtain ⟨g, hg, k, hk, rfl⟩ := mem_sup.1 hf
    rw [add_apply, h₁ g hg, h₂ k hk, add_zero]

/-- The annihilator of the zero subspace is the whole dual. -/
@[simp]
theorem strongDualAnnihilator_bot : (⊥ : Submodule 𝕜 E).strongDualAnnihilator = ⊤ := by
  ext f
  simp

/-- A functional vanishing everywhere is zero. -/
@[simp]
theorem strongDualAnnihilator_top : (⊤ : Submodule 𝕜 E).strongDualAnnihilator = ⊥ := by
  ext f
  simp [ContinuousLinearMap.ext_iff]

/-- The coannihilator of the zero subspace of the dual is the whole space. -/
@[simp]
theorem strongDualCoannihilator_bot :
    (⊥ : Submodule 𝕜 (StrongDual 𝕜 E)).strongDualCoannihilator = ⊤ := by
  ext x
  simp

/-- A vector killed by every continuous functional is zero, when the dual separates points (as it
does in every normed space over `RCLike 𝕜`, by Hahn–Banach). -/
@[simp]
theorem strongDualCoannihilator_top [SeparatingDual 𝕜 E] :
    (⊤ : Submodule 𝕜 (StrongDual 𝕜 E)).strongDualCoannihilator = ⊥ := by
  ext x
  simp only [mem_strongDualCoannihilator, mem_top, forall_true_left, mem_bot]
  exact ⟨fun h => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) h, fun h f => by simp [h]⟩

end Definitions

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The annihilator is closed in the norm topology of the dual: it is the intersection over `x ∈ M`
of the closed sets `{f | f x = 0}`, evaluation at `x` being continuous on `StrongDual 𝕜 E`. -/
theorem isClosed_strongDualAnnihilator (M : Submodule 𝕜 E) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) := by
  have : (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) =
      ⋂ x ∈ M, {f : StrongDual 𝕜 E | f x = 0} := by
    ext f
    simp
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous continuous_const

/-- The coannihilator is closed: it is the intersection of the closed kernels `ker f`, `f ∈ N`. -/
theorem isClosed_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    IsClosed (N.strongDualCoannihilator : Set E) := by
  have : (N.strongDualCoannihilator : Set E) = ⋂ f ∈ N, {x : E | f x = 0} := by
    ext x
    simp
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq f.continuous continuous_const

/-- The annihilator does not see the closure: `(closure M)^⊥ = M^⊥`, since a continuous functional
vanishing on `M` vanishes on its closure. -/
theorem strongDualAnnihilator_topologicalClosure (M : Submodule 𝕜 E) :
    M.topologicalClosure.strongDualAnnihilator = M.strongDualAnnihilator := by
  refine le_antisymm (strongDualAnnihilator_anti M.le_topologicalClosure) fun f hf => ?_
  refine mem_strongDualAnnihilator.2 fun x hx => ?_
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hx
  exact closure_minimal (fun y hy => mem_strongDualAnnihilator.1 hf y hy)
    (isClosed_eq f.continuous continuous_const) hx

/-- The coannihilator does not see the closure: `(closure N)^⊥ = N^⊥`, since evaluation at a
point is continuous on the dual. -/
theorem strongDualCoannihilator_topologicalClosure (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.topologicalClosure.strongDualCoannihilator = N.strongDualCoannihilator := by
  refine le_antisymm (strongDualCoannihilator_anti N.le_topologicalClosure) fun x hx => ?_
  refine mem_strongDualCoannihilator.2 fun f hf => ?_
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hf
  exact closure_minimal (fun g hg => mem_strongDualCoannihilator.1 hx g hg)
    (isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous continuous_const) hf

/-- `(N^⊥)^⊥ ⊇ closure N` for every subspace `N` of the dual ([brezis2011functional],
Proposition 1.9, second clause): the counit of the Galois connection and the closedness of the
annihilator. The inclusion can be strict; it is an equality when `E` is reflexive
(`strongDualAnnihilator_strongDualCoannihilator`). -/
theorem topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.topologicalClosure ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  N.topologicalClosure_minimal (le_strongDualCoannihilator_strongDualAnnihilator N)
    (isClosed_strongDualAnnihilator _)

/-- `(G ∩ L)^⊥ ⊇ closure (G^⊥ + L^⊥)` for arbitrary subspaces ([brezis2011functional],
Corollary 2.15, formula (18)): antitonicity gives `G^⊥ + L^⊥ ≤ (G ∩ L)^⊥`, which is closed. -/
theorem topologicalClosure_sup_strongDualAnnihilator_le (G L : Submodule 𝕜 E) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).topologicalClosure ≤
      (G ⊓ L).strongDualAnnihilator :=
  topologicalClosure_minimal _
    (sup_le (strongDualAnnihilator_anti inf_le_left) (strongDualAnnihilator_anti inf_le_right))
    (isClosed_strongDualAnnihilator _)

/-- The easy half of the dual distance formula: a functional of norm at most one vanishing on `M`
satisfies `‖f x‖ ≤ dist (x, M)`, since `f x = f (x - y)` for every `y ∈ M`. -/
theorem norm_apply_le_infDist_of_mem_strongDualAnnihilator {M : Submodule 𝕜 E}
    {f : StrongDual 𝕜 E} (hf : f ∈ M.strongDualAnnihilator) (hf1 : ‖f‖ ≤ 1) (x : E) :
    ‖f x‖ ≤ infDist x (M : Set E) := by
  refine (le_infDist ⟨0, M.zero_mem⟩).2 fun y hy => ?_
  rw [dist_eq_norm]
  calc ‖f x‖ = ‖f (x - y)‖ := by rw [map_sub, mem_strongDualAnnihilator.1 hf y hy, sub_zero]
    _ ≤ ‖f‖ * ‖x - y‖ := f.le_opNorm _
    _ ≤ 1 * ‖x - y‖ := by gcongr
    _ = ‖x - y‖ := one_mul _

end Normed

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **`(M^⊥)^⊥ = closure M`** for every subspace `M` of a normed space over `RCLike 𝕜`
([brezis2011functional], Proposition 1.9, first clause). The inclusion `⊇` is the Galois
connection; for `⊆`, a point outside `closure M` is separated from it by a functional vanishing
on `closure M` (`Submodule.exists_dual_eq_zero_of_notMem`), which lies in `M^⊥`. -/
theorem strongDualCoannihilator_strongDualAnnihilator (M : Submodule 𝕜 E) :
    M.strongDualAnnihilator.strongDualCoannihilator = M.topologicalClosure := by
  refine le_antisymm (fun x hx => ?_)
    (M.topologicalClosure_minimal (le_strongDualAnnihilator_strongDualCoannihilator M)
      (isClosed_strongDualCoannihilator _))
  by_contra hxM
  obtain ⟨f, -, hf0, hfx⟩ :=
    M.topologicalClosure.exists_dual_eq_zero_of_notMem (isClosed_topologicalClosure M) hxM
  have hfM : f ∈ M.strongDualAnnihilator := by
    rw [← strongDualAnnihilator_topologicalClosure]
    exact mem_strongDualAnnihilator.2 hf0
  exact hfx (mem_strongDualCoannihilator.1 hx f hfM)

/-- `(M^⊥)^⊥ = M` for a closed subspace `M`. -/
theorem strongDualCoannihilator_strongDualAnnihilator_of_isClosed {M : Submodule 𝕜 E}
    (hM : IsClosed (M : Set E)) : M.strongDualAnnihilator.strongDualCoannihilator = M := by
  rw [strongDualCoannihilator_strongDualAnnihilator, hM.submodule_topologicalClosure_eq]

/-- **`(N^⊥)^⊥ = closure N` when `E` is reflexive** ([brezis2011functional], Chapter 1,
Remark 6). A functional `f₀ ∉ closure N` is separated from `closure N` by some `ξ ∈ E**`
vanishing on `N`; by reflexivity `ξ` is evaluation at some `x₀ ∈ E`, so `x₀ ∈ N^⊥`, and then
`f₀ ∈ (N^⊥)^⊥` forces `ξ f₀ = f₀ x₀ = 0`. This is exactly where the argument needs `ξ` to come
from `E`. -/
theorem strongDualAnnihilator_strongDualCoannihilator [NormedSpace.IsReflexive 𝕜 E]
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.strongDualCoannihilator.strongDualAnnihilator = N.topologicalClosure := by
  refine le_antisymm (fun f₀ hf₀ => ?_)
    (topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator N)
  by_contra hf₀N
  obtain ⟨ξ, -, hξ0, hξf⟩ :=
    N.topologicalClosure.exists_dual_eq_zero_of_notMem (isClosed_topologicalClosure N) hf₀N
  obtain ⟨x₀, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := 𝕜) ξ
  have hx₀ : x₀ ∈ N.strongDualCoannihilator := mem_strongDualCoannihilator.2 fun f hf => by
    have := hξ0 f (N.le_topologicalClosure hf)
    rwa [NormedSpace.dual_def] at this
  refine hξf ?_
  rw [NormedSpace.dual_def]
  exact mem_strongDualAnnihilator.1 hf₀ x₀ hx₀

/-- **A subspace is dense iff its annihilator is trivial** ([brezis2011functional], Corollary 1.8
with Remark 5): `M` is dense iff every bounded linear functional vanishing on `M` is zero. -/
theorem strongDualAnnihilator_eq_bot_iff (M : Submodule 𝕜 E) :
    M.strongDualAnnihilator = ⊥ ↔ Dense (M : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  constructor
  · intro h
    rw [← strongDualCoannihilator_strongDualAnnihilator, h, strongDualCoannihilator_bot]
  · intro h
    rw [← strongDualAnnihilator_topologicalClosure, h, strongDualAnnihilator_top]

/-- The annihilator determines a subspace up to closure:
`M₂^⊥ ≤ M₁^⊥ ↔ closure M₁ ≤ closure M₂`. -/
theorem strongDualAnnihilator_le_strongDualAnnihilator_iff (M₁ M₂ : Submodule 𝕜 E) :
    M₂.strongDualAnnihilator ≤ M₁.strongDualAnnihilator ↔
      M₁.topologicalClosure ≤ M₂.topologicalClosure := by
  constructor
  · intro h
    rw [← strongDualCoannihilator_strongDualAnnihilator M₁,
      ← strongDualCoannihilator_strongDualAnnihilator M₂]
    exact strongDualCoannihilator_anti h
  · intro h
    rw [← strongDualAnnihilator_topologicalClosure M₁,
      ← strongDualAnnihilator_topologicalClosure M₂]
    exact strongDualAnnihilator_anti h

/-- **`G ∩ L = (G^⊥ + L^⊥)^⊥`** for closed subspaces `G`, `L` ([brezis2011functional],
Proposition 2.14, formula (16)). -/
theorem strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed {G L : Submodule 𝕜 E}
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E)) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).strongDualCoannihilator = G ⊓ L := by
  rw [strongDualCoannihilator_sup, strongDualCoannihilator_strongDualAnnihilator_of_isClosed hG,
    strongDualCoannihilator_strongDualAnnihilator_of_isClosed hL]

/-- **`(G^⊥ ∩ L^⊥)^⊥ = closure (G + L)`** for arbitrary subspaces `G`, `L`
([brezis2011functional], Corollary 2.15, formula (19)). -/
theorem strongDualCoannihilator_inf_strongDualAnnihilator (G L : Submodule 𝕜 E) :
    (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator =
      (G ⊔ L).topologicalClosure := by
  rw [← strongDualAnnihilator_sup, strongDualCoannihilator_strongDualAnnihilator]

/-- **The distance from a functional to an annihilator is the norm of its restriction**:
`dist (f, M^⊥) = ‖f|_M‖` ([brezis2011functional], formula (21) in the proof of Theorem 2.16).
For `g ∈ M^⊥`, `‖f - g‖ ≥ ‖(f - g)|_M‖ = ‖f|_M‖`; conversely a norm-preserving extension `h` of
`f|_M` (`exists_extension_norm_eq`) has `f - h ∈ M^⊥` and `dist (f, f - h) = ‖f|_M‖`. -/
theorem infDist_strongDualAnnihilator (M : Submodule 𝕜 E) (f : StrongDual 𝕜 E) :
    infDist f (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) = ‖f.comp M.subtypeL‖ := by
  apply le_antisymm
  · obtain ⟨h, hh, hnorm⟩ := exists_extension_norm_eq M (f.comp M.subtypeL)
    have hmem : f - h ∈ M.strongDualAnnihilator := mem_strongDualAnnihilator.2 fun x hx => by
      have := hh ⟨x, hx⟩
      rw [ContinuousLinearMap.comp_apply, subtypeL_apply] at this
      rw [sub_apply, this, sub_self]
    calc infDist f (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) ≤ dist f (f - h) :=
          infDist_le_dist_of_mem hmem
      _ = ‖h‖ := by rw [dist_eq_norm, sub_sub_cancel]
      _ = ‖f.comp M.subtypeL‖ := hnorm
  · refine (le_infDist ⟨0, zero_mem _⟩).2 fun g hg => ?_
    rw [dist_eq_norm]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have hx : f x = (f - g) x := by
      rw [sub_apply, mem_strongDualAnnihilator.1 hg x x.2, sub_zero]
    rw [ContinuousLinearMap.comp_apply, subtypeL_apply, hx, ← norm_coe x]
    exact (f - g).le_opNorm x

/-- **The distance from a point to a subspace is attained by a functional in the annihilator**
([brezis2011functional], §1.4, Example 3, the subspace case): there is `f ∈ M^⊥` with `‖f‖ ≤ 1`
and `f x = dist (x, M)`. With `norm_apply_le_infDist_of_mem_strongDualAnnihilator` this says
`dist (x, M) = max {‖f x‖ : f ∈ M^⊥, ‖f‖ ≤ 1}`.

Hahn–Banach in the quotient `E ⧸ closure M`, whose norm is `‖[x]‖ = dist (x, M)`: a norming
functional of `[x]` there, composed with the quotient map, vanishes on `M`. -/
theorem exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist (M : Submodule 𝕜 E)
    (x : E) :
    ∃ f ∈ M.strongDualAnnihilator, ‖f‖ ≤ 1 ∧ f x = (infDist x (M : Set E) : 𝕜) := by
  set M' := M.topologicalClosure with hM'
  have hM'c : IsClosed (M' : Set E) := isClosed_topologicalClosure M
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' 𝕜 (Submodule.Quotient.mk x : E ⧸ M')
  have hq : ‖M'.mkQL‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      simpa using Submodule.Quotient.norm_mk_le M' y
  refine ⟨g.comp M'.mkQL, mem_strongDualAnnihilator.2 fun y hy => ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, mkQL_apply, mkQ_apply,
      (Submodule.Quotient.mk_eq_zero M').2 (M.le_topologicalClosure hy), map_zero]
  · calc ‖g.comp M'.mkQL‖ ≤ ‖g‖ * ‖M'.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  · rw [ContinuousLinearMap.comp_apply, mkQL_apply, mkQ_apply, hgx]
    congr 1
    have hnorm : ‖(Submodule.Quotient.mk x : E ⧸ M')‖ = infDist x (M' : Set E) :=
      QuotientAddGroup.norm_mk (S := M'.toAddSubgroup) x
    rw [hnorm, hM', topologicalClosure_coe, infDist_closure]

end RCLike

end Submodule
