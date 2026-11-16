/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $E$ be a topological vector space over a nontrivially normed field $\mathbb{K}$, and let $E^*$
be its strong dual. The **annihilator** of a subspace $M \subseteq E$ is the subspace
$M^\perp = \{f \in E^* : f = 0 \text{ on } M\}$ of $E^*$. The **coannihilator** of a subspace
$N \subseteq E^*$ is the subspace $N^\perp = \{x \in E : f(x) = 0 \text{ for all } f \in N\}$ of $E$
itself, not of $E^{**}$. Both are closed when $E$ is normed. These are the orthogonality relations
of §1.3 and §2.5 of [brezis2011functional]. They are the language for the kernel and range relations
of adjoint operators, the closed range theorem, the Fredholm alternative, and the duals of quotients
and subspaces.

For a normed space $E$ over $\mathbb{R}$ or $\mathbb{C}$, this module proves
$(M^\perp)^\perp = \overline{M}$ and $\overline{N} \subseteq (N^\perp)^\perp$, with equality when
$E$ is reflexive, and it proves that $M$ is dense if and only if $M^\perp = \{0\}$. For subspaces
$G$ and $L$ of $E$ it proves the formulas $(G + L)^\perp = G^\perp \cap L^\perp$,
$G \cap L = (G^\perp + L^\perp)^\perp$ for closed $G$ and $L$, $\overline{G^\perp + L^\perp}
\subseteq (G \cap L)^\perp$ and $(G^\perp \cap L^\perp)^\perp = \overline{G + L}$. It also proves
the two distance formulas $\operatorname{dist}(f, M^\perp) = \|f|_M\|$ and $\operatorname{dist}(x,
M) = \max \{|f(x)| : f \in M^\perp, \|f\| \le 1\}$.

## Main definitions

* `Submodule.strongDualAnnihilator`: the annihilator $M^\perp \subseteq E^*$ of a subspace $M$ of
  $E$.
* `Submodule.strongDualCoannihilator`: the coannihilator $N^\perp \subseteq E$ of a subspace $N$ of
  $E^*$.

## Main results

* `Submodule.le_strongDualAnnihilator_iff_le_strongDualCoannihilator`: $N \subseteq M^\perp$ if and
  only if $M \subseteq N^\perp$.
* `Submodule.isClosed_strongDualAnnihilator`, `Submodule.isClosed_strongDualCoannihilator`: in a
  normed space, $M^\perp$ and $N^\perp$ are closed.
* `Submodule.strongDualCoannihilator_strongDualAnnihilator`: $(M^\perp)^\perp = \overline{M}$
  (Proposition 1.9 of [brezis2011functional]).
* `Submodule.topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator`:
  $\overline{N} \subseteq (N^\perp)^\perp$ (Proposition 1.9 of [brezis2011functional]).
* `Submodule.strongDualAnnihilator_strongDualCoannihilator`: $(N^\perp)^\perp = \overline{N}$ when
  $E$ is reflexive (Remark 6 of chapter 1 of [brezis2011functional]).
* `Submodule.strongDualAnnihilator_eq_bot_iff`: $M^\perp = \{0\}$ if and only if $M$ is dense
  (Corollary 1.8 of [brezis2011functional]).
* `Submodule.strongDualAnnihilator_sup`: $(G + L)^\perp = G^\perp \cap L^\perp$ (Proposition 2.14 of
  [brezis2011functional]).
* `Submodule.strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed`:
  $G \cap L = (G^\perp + L^\perp)^\perp$ for closed $G$ and $L$ (Proposition 2.14 of
  [brezis2011functional]).
* `Submodule.topologicalClosure_sup_strongDualAnnihilator_le`: $\overline{G^\perp + L^\perp}
  \subseteq (G \cap L)^\perp$ (Corollary 2.15 of [brezis2011functional]).
* `Submodule.strongDualCoannihilator_inf_strongDualAnnihilator`: $(G^\perp \cap L^\perp)^\perp =
  \overline{G + L}$ (Corollary 2.15 of [brezis2011functional]).
* `Submodule.infDist_strongDualAnnihilator`: $\operatorname{dist}(f, M^\perp) = \|f|_M\|$.
* `Submodule.exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist`: there is
  $f \in M^\perp$ with $\|f\| \le 1$ and $f(x) = \operatorname{dist}(x, M)$.

## Implementation notes

* Mathlib has both objects, without a name: $M^\perp$ is `StrongDual.polarSubmodule 𝕜 M`, and
  $N^\perp$ is `(topDualPairing 𝕜 E).polarSubmodule N`, because the polar of a set that is closed
  under scalar multiplication is its annihilator (`LinearMap.polar_subMulAction`). The definitions
  here are thin wrappers with the bridges `Submodule.strongDualAnnihilator_eq_polarSubmodule` and
  `Submodule.strongDualCoannihilator_eq_polarSubmodule`, because Mathlib's API for `polarSubmodule`
  covers only membership.
* The names follow Mathlib's algebraic pair `Submodule.dualAnnihilator` and
  `Submodule.dualCoannihilator`. These live in the algebraic dual `Module.Dual` and are different
  objects. The name `Submodule.annihilator` is Mathlib's ideal-valued annihilator and is not used.
* The closedness of $M^\perp$ and $N^\perp$ is also registered as the instances
  `Submodule.instIsClosedStrongDualAnnihilator` and `Submodule.instIsClosedStrongDualCoannihilator`,
  so that the quotients $E^* / M^\perp$ and $E / N^\perp$ are normed spaces by instance search.
* The characterization of closed sums $G + L$ through $G^\perp + L^\perp$ (Theorem 2.16 of
  [brezis2011functional]) is in `Numlib.Analysis.Normed.Module.Annihilator.ClosedSum`, so that this
  module does not import the open mapping theorem.
-/

open Metric

namespace Submodule

section Definitions

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- The **annihilator** of a subspace $M$ of a topological vector space $E$: the subspace
$$M^\perp = \{f \in E^* : f(x) = 0 \text{ for all } x \in M\}$$
of the strong dual $E^*$.

It is Mathlib's `StrongDual.polarSubmodule 𝕜 M`. -/
def strongDualAnnihilator (M : Submodule 𝕜 E) : Submodule 𝕜 (StrongDual 𝕜 E) :=
  StrongDual.polarSubmodule 𝕜 M

/-- A functional $f \in E^*$ lies in $M^\perp$ if and only if $f(x) = 0$ for every $x \in M$. -/
@[simp]
theorem mem_strongDualAnnihilator {M : Submodule 𝕜 E} {f : StrongDual 𝕜 E} :
    f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, f x = 0 :=
  StrongDual.mem_polarSubmodule 𝕜 M f

/-- The annihilator $M^\perp$ is Mathlib's polar submodule `StrongDual.polarSubmodule 𝕜 M`. -/
theorem strongDualAnnihilator_eq_polarSubmodule (M : Submodule 𝕜 E) :
    M.strongDualAnnihilator = StrongDual.polarSubmodule 𝕜 M :=
  rfl

/-- The **coannihilator** of a subspace $N$ of the strong dual $E^*$: the subspace
$$N^\perp = \{x \in E : f(x) = 0 \text{ for all } f \in N\}$$
of $E$ itself, not of the bidual $E^{**}$.

It is Mathlib's `(topDualPairing 𝕜 E).polarSubmodule N`, the polar on the other side of the
pairing of $E^*$ with $E$. -/
def strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) : Submodule 𝕜 E :=
  (topDualPairing 𝕜 E).polarSubmodule N

/-- A vector $x \in E$ lies in $N^\perp$ if and only if $f(x) = 0$ for every $f \in N$. -/
@[simp]
theorem mem_strongDualCoannihilator {N : Submodule 𝕜 (StrongDual 𝕜 E)} {x : E} :
    x ∈ N.strongDualCoannihilator ↔ ∀ f ∈ N, f x = 0 := by
  change x ∈ (topDualPairing 𝕜 E).polarSubmodule N ↔ _
  simp [LinearMap.polarSubmodule, Submodule.copy_eq, Submodule.mem_iInf]

/-- The coannihilator $N^\perp$ is Mathlib's polar submodule `(topDualPairing 𝕜 E).polarSubmodule N`
for the pairing of $E^*$ with $E$. -/
theorem strongDualCoannihilator_eq_polarSubmodule (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.strongDualCoannihilator = (topDualPairing 𝕜 E).polarSubmodule N :=
  rfl

/-- The coannihilator $N^\perp$ is the intersection of the kernels $\ker f$ over all $f \in N$. -/
theorem strongDualCoannihilator_eq_iInf_ker (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.strongDualCoannihilator = ⨅ f ∈ N, LinearMap.ker (f : E →ₗ[𝕜] 𝕜) := by
  ext x
  simp [mem_strongDualCoannihilator, Submodule.mem_iInf]

/-- For subspaces $M \subseteq E$ and $N \subseteq E^*$, $N \subseteq M^\perp$ if and only if
$M \subseteq N^\perp$. Both conditions say that $f(x) = 0$ for all $f \in N$ and $x \in M$. So
the annihilator and the coannihilator form an antitone Galois connection. -/
theorem le_strongDualAnnihilator_iff_le_strongDualCoannihilator {M : Submodule 𝕜 E}
    {N : Submodule 𝕜 (StrongDual 𝕜 E)} :
    N ≤ M.strongDualAnnihilator ↔ M ≤ N.strongDualCoannihilator := by
  constructor
  · intro h x hx
    exact mem_strongDualCoannihilator.2 fun f hf => mem_strongDualAnnihilator.1 (h hf) x hx
  · intro h f hf
    exact mem_strongDualAnnihilator.2 fun x hx => mem_strongDualCoannihilator.1 (h hx) f hf

/-- Taking annihilators reverses inclusions: if $M_1 \subseteq M_2$, then
$M_2^\perp \subseteq M_1^\perp$. -/
theorem strongDualAnnihilator_anti {M₁ M₂ : Submodule 𝕜 E} (h : M₁ ≤ M₂) :
    M₂.strongDualAnnihilator ≤ M₁.strongDualAnnihilator := fun _ hf =>
  mem_strongDualAnnihilator.2 fun x hx => mem_strongDualAnnihilator.1 hf x (h hx)

/-- Taking coannihilators reverses inclusions: if $N_1 \subseteq N_2$, then
$N_2^\perp \subseteq N_1^\perp$. -/
theorem strongDualCoannihilator_anti {N₁ N₂ : Submodule 𝕜 (StrongDual 𝕜 E)} (h : N₁ ≤ N₂) :
    N₂.strongDualCoannihilator ≤ N₁.strongDualCoannihilator := fun _ hx =>
  mem_strongDualCoannihilator.2 fun f hf => mem_strongDualCoannihilator.1 hx f (h hf)

/-- Every subspace $M$ of $E$ satisfies $M \subseteq (M^\perp)^\perp$. -/
theorem le_strongDualAnnihilator_strongDualCoannihilator (M : Submodule 𝕜 E) :
    M ≤ M.strongDualAnnihilator.strongDualCoannihilator :=
  le_strongDualAnnihilator_iff_le_strongDualCoannihilator.1 le_rfl

/-- Every subspace $N$ of $E^*$ satisfies $N \subseteq (N^\perp)^\perp$. -/
theorem le_strongDualCoannihilator_strongDualAnnihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  le_strongDualAnnihilator_iff_le_strongDualCoannihilator.2 le_rfl

/-- For arbitrary subspaces $M_1$ and $M_2$ of $E$,
$$(M_1 + M_2)^\perp = M_1^\perp \cap M_2^\perp.$$
This is formula (17) of Proposition 2.14 of [brezis2011functional]. No closedness is needed. -/
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

/-- For arbitrary subspaces $N_1$ and $N_2$ of $E^*$,
$(N_1 + N_2)^\perp = N_1^\perp \cap N_2^\perp$. -/
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

/-- The annihilator of the zero subspace of $E$ is the whole dual: $\{0\}^\perp = E^*$. -/
@[simp]
theorem strongDualAnnihilator_bot : (⊥ : Submodule 𝕜 E).strongDualAnnihilator = ⊤ := by
  ext f
  simp

/-- The annihilator of the whole space is zero: $E^\perp = \{0\}$, because a functional that
vanishes everywhere is zero. -/
@[simp]
theorem strongDualAnnihilator_top : (⊤ : Submodule 𝕜 E).strongDualAnnihilator = ⊥ := by
  ext f
  simp [ContinuousLinearMap.ext_iff]

/-- The coannihilator of the zero subspace of $E^*$ is the whole space $E$. -/
@[simp]
theorem strongDualCoannihilator_bot :
    (⊥ : Submodule 𝕜 (StrongDual 𝕜 E)).strongDualCoannihilator = ⊤ := by
  ext x
  simp

/-- If the continuous linear functionals on $E$ separate the points of $E$, then
$(E^*)^\perp = \{0\}$: a vector on which every functional vanishes is zero. This holds in every
normed space over $\mathbb{R}$ or $\mathbb{C}$, by the Hahn–Banach theorem. -/
@[simp]
theorem strongDualCoannihilator_top [SeparatingDual 𝕜 E] :
    (⊤ : Submodule 𝕜 (StrongDual 𝕜 E)).strongDualCoannihilator = ⊥ := by
  ext x
  simp only [mem_strongDualCoannihilator, mem_top, forall_true_left, mem_bot]
  exact ⟨fun h => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) h, fun h f => by simp [h]⟩

end Definitions

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a subspace $M$ of a normed space $E$, the annihilator $M^\perp$ is closed in the norm
topology of $E^*$.

It is the intersection over $x \in M$ of the closed sets $\{f : f(x) = 0\}$, because evaluation
at $x$ is continuous on $E^*$. -/
theorem isClosed_strongDualAnnihilator (M : Submodule 𝕜 E) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) := by
  have : (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) =
      ⋂ x ∈ M, {f : StrongDual 𝕜 E | f x = 0} := by
    ext f
    simp
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous continuous_const

/-- For a subspace $N$ of $E^*$, the coannihilator $N^\perp$ is closed in $E$: it is the
intersection of the closed kernels $\ker f$, $f \in N$. -/
theorem isClosed_strongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    IsClosed (N.strongDualCoannihilator : Set E) := by
  have : (N.strongDualCoannihilator : Set E) = ⋂ f ∈ N, {x : E | f x = 0} := by
    ext x
    simp
  rw [this]
  exact isClosed_biInter fun f _ => isClosed_eq f.continuous continuous_const

/-- The annihilator $M^\perp$ is closed, as an instance, so that the quotient $E^* / M^\perp$ is a
normed space by instance search. -/
instance instIsClosedStrongDualAnnihilator (M : Submodule 𝕜 E) :
    IsClosed (M.strongDualAnnihilator : Set (StrongDual 𝕜 E)) :=
  isClosed_strongDualAnnihilator M

/-- The coannihilator $N^\perp$ is closed, as an instance, so that the quotient $E / N^\perp$ is a
normed space by instance search. -/
instance instIsClosedStrongDualCoannihilator (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    IsClosed (N.strongDualCoannihilator : Set E) :=
  isClosed_strongDualCoannihilator N

/-- The annihilator does not see the closure: $(\overline{M})^\perp = M^\perp$, because a continuous
functional that vanishes on $M$ vanishes on its closure. -/
theorem strongDualAnnihilator_topologicalClosure (M : Submodule 𝕜 E) :
    M.topologicalClosure.strongDualAnnihilator = M.strongDualAnnihilator := by
  refine le_antisymm (strongDualAnnihilator_anti M.le_topologicalClosure) fun f hf => ?_
  refine mem_strongDualAnnihilator.2 fun x hx => ?_
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hx
  exact closure_minimal (fun y hy => mem_strongDualAnnihilator.1 hf y hy)
    (isClosed_eq f.continuous continuous_const) hx

/-- The coannihilator does not see the closure: $(\overline{N})^\perp = N^\perp$, because evaluation
at a point is continuous on $E^*$. -/
theorem strongDualCoannihilator_topologicalClosure (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.topologicalClosure.strongDualCoannihilator = N.strongDualCoannihilator := by
  refine le_antisymm (strongDualCoannihilator_anti N.le_topologicalClosure) fun x hx => ?_
  refine mem_strongDualCoannihilator.2 fun f hf => ?_
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hf
  exact closure_minimal (fun g hg => mem_strongDualCoannihilator.1 hx g hg)
    (isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous continuous_const) hf

/-- Every subspace $N$ of $E^*$ satisfies
$$\overline{N} \subseteq (N^\perp)^\perp.$$
This is the second part of Proposition 1.9 of [brezis2011functional].

The proof combines $N \subseteq (N^\perp)^\perp$ with the closedness of annihilators. The
inclusion can be strict. It is an equality when $E$ is reflexive
(`Submodule.strongDualAnnihilator_strongDualCoannihilator`). -/
theorem topologicalClosure_le_strongDualAnnihilator_strongDualCoannihilator
    (N : Submodule 𝕜 (StrongDual 𝕜 E)) :
    N.topologicalClosure ≤ N.strongDualCoannihilator.strongDualAnnihilator :=
  N.topologicalClosure_minimal (le_strongDualCoannihilator_strongDualAnnihilator N)
    (isClosed_strongDualAnnihilator _)

/-- For arbitrary subspaces $G$ and $L$ of $E$,
$$\overline{G^\perp + L^\perp} \subseteq (G \cap L)^\perp.$$
This is formula (18) of Corollary 2.15 of [brezis2011functional].

Antitonicity gives $G^\perp + L^\perp \subseteq (G \cap L)^\perp$, and $(G \cap L)^\perp$ is
closed. -/
theorem topologicalClosure_sup_strongDualAnnihilator_le (G L : Submodule 𝕜 E) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).topologicalClosure ≤
      (G ⊓ L).strongDualAnnihilator :=
  topologicalClosure_minimal _
    (sup_le (strongDualAnnihilator_anti inf_le_left) (strongDualAnnihilator_anti inf_le_right))
    (isClosed_strongDualAnnihilator _)

/-- Let $M$ be a subspace of $E$, and let $f \in M^\perp$ with $\|f\| \le 1$. Then
$|f(x)| \le \operatorname{dist}(x, M)$ for every $x \in E$. This is the easy half of the
distance formula of `Submodule.exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist`.

The proof uses $f(x) = f(x - y)$ for every $y \in M$. -/
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

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. Every subspace $M$ of $E$ satisfies
$$(M^\perp)^\perp = \overline{M}.$$
This is the first part of Proposition 1.9 of [brezis2011functional].

The inclusion $\supseteq$ follows from $M \subseteq (M^\perp)^\perp$ and the closedness of
coannihilators. For $\subseteq$, a point outside $\overline{M}$ is separated from $\overline{M}$
by a functional that vanishes on $\overline{M}$ (`Submodule.exists_dual_eq_zero_of_notMem`), and
this functional lies in $M^\perp$. -/
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

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. Every closed subspace $M$ of $E$
satisfies $(M^\perp)^\perp = M$. -/
theorem strongDualCoannihilator_strongDualAnnihilator_of_isClosed {M : Submodule 𝕜 E}
    (hM : IsClosed (M : Set E)) : M.strongDualAnnihilator.strongDualCoannihilator = M := by
  rw [strongDualCoannihilator_strongDualAnnihilator, hM.submodule_topologicalClosure_eq]

/-- Let $E$ be a reflexive normed space over $\mathbb{R}$ or $\mathbb{C}$. Every subspace $N$ of
$E^*$ satisfies
$$(N^\perp)^\perp = \overline{N}.$$
This is Remark 6 of chapter 1 of [brezis2011functional].

A functional $f_0 \notin \overline{N}$ is separated from $\overline{N}$ by some $\xi \in E^{**}$
that vanishes on $N$. By reflexivity, $\xi$ is the evaluation at some $x_0 \in E$, so
$x_0 \in N^\perp$. Then $f_0 \in (N^\perp)^\perp$ would give $\xi(f_0) = f_0(x_0) = 0$. The
argument needs reflexivity exactly at the step where $\xi$ must come from $E$. -/
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

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. A subspace $M$ of $E$ is dense if
and only if $M^\perp = \{0\}$, that is, if and only if every bounded linear functional that
vanishes on $M$ is zero. This is Corollary 1.8 of [brezis2011functional], with its Remark 5. -/
theorem strongDualAnnihilator_eq_bot_iff (M : Submodule 𝕜 E) :
    M.strongDualAnnihilator = ⊥ ↔ Dense (M : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  constructor
  · intro h
    rw [← strongDualCoannihilator_strongDualAnnihilator, h, strongDualCoannihilator_bot]
  · intro h
    rw [← strongDualAnnihilator_topologicalClosure, h, strongDualAnnihilator_top]

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. For subspaces $M_1$ and $M_2$ of
$E$, $M_2^\perp \subseteq M_1^\perp$ if and only if $\overline{M_1} \subseteq \overline{M_2}$.
So the annihilator determines a subspace up to closure. -/
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

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. For closed subspaces $G$ and $L$ of
$E$,
$$G \cap L = (G^\perp + L^\perp)^\perp.$$
This is formula (16) of Proposition 2.14 of [brezis2011functional]. -/
theorem strongDualCoannihilator_sup_strongDualAnnihilator_of_isClosed {G L : Submodule 𝕜 E}
    (hG : IsClosed (G : Set E)) (hL : IsClosed (L : Set E)) :
    (G.strongDualAnnihilator ⊔ L.strongDualAnnihilator).strongDualCoannihilator = G ⊓ L := by
  rw [strongDualCoannihilator_sup, strongDualCoannihilator_strongDualAnnihilator_of_isClosed hG,
    strongDualCoannihilator_strongDualAnnihilator_of_isClosed hL]

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. For arbitrary subspaces $G$ and $L$
of $E$,
$$(G^\perp \cap L^\perp)^\perp = \overline{G + L}.$$
This is formula (19) of Corollary 2.15 of [brezis2011functional]. -/
theorem strongDualCoannihilator_inf_strongDualAnnihilator (G L : Submodule 𝕜 E) :
    (G.strongDualAnnihilator ⊓ L.strongDualAnnihilator).strongDualCoannihilator =
      (G ⊔ L).topologicalClosure := by
  rw [← strongDualAnnihilator_sup, strongDualCoannihilator_strongDualAnnihilator]

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. For a subspace $M$ of $E$ and
$f \in E^*$, the distance from $f$ to the annihilator is the norm of the restriction $f|_M$ of
$f$ to $M$:
$$\operatorname{dist}(f, M^\perp) = \|f|_M\|.$$
This is formula (21) in the proof of Theorem 2.16 of [brezis2011functional].

For $g \in M^\perp$, $\|f - g\| \ge \|(f - g)|_M\| = \|f|_M\|$. Conversely, a norm-preserving
extension $h$ of $f|_M$ (`exists_extension_norm_eq`) has $f - h \in M^\perp$ and
$\|f - (f - h)\| = \|f|_M\|$. -/
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

/-- Let $E$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$. For a subspace $M$ of $E$ and
$x \in E$, there is $f \in M^\perp$ with $\|f\| \le 1$ and $f(x) = \operatorname{dist}(x, M)$.
With `Submodule.norm_apply_le_infDist_of_mem_strongDualAnnihilator`, this gives
$$\operatorname{dist}(x, M) = \max \{|f(x)| : f \in M^\perp, \|f\| \le 1\}.$$
This is the subspace case of Example 3 in §1.4 of [brezis2011functional].

The proof applies the Hahn–Banach theorem in the quotient $E / \overline{M}$, whose norm is
$\|[x]\| = \operatorname{dist}(x, M)$. A norming functional of $[x]$, composed with the quotient
map, vanishes on $M$. -/
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
