/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection

/-!
# Spectral subspaces

Let $A$ be an endomorphism of a vector space $V$ over a field $K$, and let $p$ be a predicate on $K$
that selects a set of eigenvalues. For $\mu \in K$, write $G_\mu(A) = \bigcup_{k} \ker (A - \mu)^k$
for the maximal generalized eigenspace of $\mu$; it is $0$ when $\mu$ is not an eigenvalue. The
**spectral subspace** of $A$ for $p$ is the sum of the generalized eigenspaces of the selected
eigenvalues,
$$S_p(A) = \sum_{\mu \,:\, p(\mu)} G_\mu(A).$$
It is the invariant subspace attached to a part of the spectrum. Examples are the stable subspace of
the Hamiltonian–Schur form ($p(\mu)$ is $\operatorname{Re} \mu < 0$), the dominant subspace of
subspace iteration ($p$ selects the $m$ eigenvalues of largest modulus), the generalized eigenspace
of one eigenvalue $l$ ($p(\mu)$ is $\mu = l$), and the invariant subspace of a spectral set
$\Lambda$ ($p(\mu)$ is $\mu \in \Lambda$).

Over an algebraically closed field in finite dimension, $S_p(A)$ and $S_{\neg p}(A)$ are
complementary. The **spectral projector** $P_p$ is the projection onto $S_p(A)$ along
$S_{\neg p}(A)$. It is the Riesz projector of the selected eigenvalues, and in general it is an
oblique projector. An invariant subspace on which every eigenvalue satisfies $p$ lies in $S_p(A)$,
and it is equal to $S_p(A)$ if the dimensions agree. The module also proves that, when the
eigenspaces of an endomorphism span the space, every generalized eigenspace is an eigenspace.

## Main definitions

* `Module.End.spectralSubspace`: the spectral subspace $S_p(A) = \sum_{p(\mu)} G_\mu(A)$.
* `Module.End.spectralProjector`: over an algebraically closed field in finite dimension, the
  projection $P_p$ onto $S_p(A)$ along $S_{\neg p}(A)$.

## Main results

* `Module.End.spectralSubspace_mem_invtSubmodule`: $S_p(A)$ is invariant under $A$.
* `Module.End.isCompl_spectralSubspace`: over an algebraically closed field in finite dimension,
  $S_p(A)$ and $S_{\neg p}(A)$ are complementary subspaces.
* `Module.End.invtSubmodule_le_spectralSubspace`: an invariant subspace on which every eigenvalue
  satisfies $p$ lies in $S_p(A)$.
* `Module.End.invtSubmodule_eq_spectralSubspace`: such a subspace with the dimension of $S_p(A)$ is
  equal to $S_p(A)$.
* `Module.End.maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top`: if the eigenspaces of $f$
  span $V$, then $G_\mu(f) = \ker(f - \mu)$ for every $\mu$.
* `Module.End.ker_spectralProjector`, `Module.End.range_spectralProjector`:
  $\ker P_p = S_{\neg p}(A)$ and $\operatorname{range} P_p = S_p(A)$.
* `Module.End.existsUnique_mem_spectralProjector_eq`: if a subspace $W$ meets $S_{\neg p}(A)$ only
  in $0$ and has the dimension of $S_p(A)$, then $P_p$ maps $W$ bijectively onto $S_p(A)$.

## Implementation notes

* The spectral subspace is `⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ`. The sum runs over all $\mu \in K$
  with $p(\mu)$; the scalars that are not eigenvalues contribute $0$.
* The spectral projector is `Submodule.projection` for the complementary pair of
  `Module.End.isCompl_spectralSubspace`. It is an orthogonal projection only when the two subspaces
  are orthogonal, for example when $A$ is normal.
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The **spectral subspace** of an endomorphism $A$ of $V$ for a predicate $p$ on $K$ is the sum of
the maximal generalized eigenspaces of the scalars that satisfy $p$:
$$S_p(A) = \sum_{\mu \,:\, p(\mu)} G_\mu(A), \qquad G_\mu(A) = \bigcup_k \ker (A - \mu)^k.$$
A scalar $\mu$ that is not an eigenvalue has $G_\mu(A) = 0$, so only the selected eigenvalues
contribute.

The generalized eigenspace $G_\mu(A)$ is `Module.End.maxGenEigenspace A μ`, and the sum is the
supremum of submodules. -/
def spectralSubspace (A : End K V) (p : K → Prop) : Submodule K V :=
  ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ

variable {A : End K V} {p q : K → Prop}

/-- The spectral subspace $S_p(A)$ is the supremum of `A.maxGenEigenspace μ` over the scalars $\mu$
with $p(\mu)$. -/
theorem spectralSubspace_def (A : End K V) (p : K → Prop) :
    A.spectralSubspace p = ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ :=
  rfl

/-- If $p(\mu)$ holds, then $G_\mu(A) \subseteq S_p(A)$. -/
theorem maxGenEigenspace_le_spectralSubspace {μ : K} (hμ : p μ) :
    A.maxGenEigenspace μ ≤ A.spectralSubspace p :=
  le_iSup₂_of_le μ hμ le_rfl

/-- The spectral subspace for the predicate $\mu = l$ is the generalized eigenspace of $l$:
$S_{\mu = l}(A) = G_l(A)$. -/
@[simp]
theorem spectralSubspace_eq (A : End K V) (l : K) :
    A.spectralSubspace (· = l) = A.maxGenEigenspace l :=
  iSup_iSup_eq_left

/-- If $p(\mu)$ implies $q(\mu)$ for every $\mu$, then $S_p(A) \subseteq S_q(A)$. -/
theorem spectralSubspace_mono (h : ∀ μ, p μ → q μ) : A.spectralSubspace p ≤ A.spectralSubspace q :=
  iSup₂_le fun μ hμ => maxGenEigenspace_le_spectralSubspace (h μ hμ)

/-- **Spectral subspaces are invariant.** For every endomorphism $A$ of $V$ and every predicate $p$
on $K$, the spectral subspace $S_p(A)$ is invariant under $A$: $A(S_p(A)) \subseteq S_p(A)$.

The proof uses that each generalized eigenspace $G_\mu(A)$ is invariant under $A$. -/
theorem spectralSubspace_mem_invtSubmodule (A : End K V) (p : K → Prop) :
    A.spectralSubspace p ∈ A.invtSubmodule := by
  rw [mem_invtSubmodule_iff_map_le, spectralSubspace, Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun _ => ?_
  exact Submodule.map_le_iff_le_comap.2 (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) μ)

/-- If $x \in S_p(A)$, then $Ax \in S_p(A)$. This is the elementwise form of
`Module.End.spectralSubspace_mem_invtSubmodule`. -/
theorem apply_mem_spectralSubspace {x : V} (hx : x ∈ A.spectralSubspace p) :
    A x ∈ A.spectralSubspace p :=
  A.spectralSubspace_mem_invtSubmodule p hx

/-- **The spectral splitting of a set of eigenvalues.** Let $K$ be algebraically closed, let $V$ be
finite-dimensional, let $A$ be an endomorphism of $V$, and let $p$ be a predicate on $K$. Then
the spectral subspaces of $p$ and of its negation are complementary:
$$S_p(A) \cap S_{\neg p}(A) = 0, \qquad S_p(A) + S_{\neg p}(A) = V.$$

The intersection is $0$ because the generalized eigenspaces of distinct eigenvalues are
independent. The sum is $V$ because the generalized eigenspaces span $V$ over an algebraically
closed field. -/
theorem isCompl_spectralSubspace [IsAlgClosed K] [FiniteDimensional K V] (A : End K V)
    (p : K → Prop) : IsCompl (A.spectralSubspace p) (A.spectralSubspace fun μ => ¬ p μ) where
  disjoint := (A.independent_maxGenEigenspace).disjoint_biSup_biSup
    (s := {μ | p μ}) (t := {μ | ¬ p μ}) (Set.disjoint_left.mpr fun _ ha ha' => ha' ha)
  codisjoint := by
    rw [codisjoint_iff, spectralSubspace, spectralSubspace, ← iSup_split (A.maxGenEigenspace) p,
      A.iSup_maxGenEigenspace_eq_top]

/-- Let $K$ be algebraically closed, let $V$ be finite-dimensional, and let $A$ be an endomorphism
of $V$. Let $W$ be an $A$-invariant subspace on which every eigenvalue satisfies $p$: if
$\neg p(\mu)$, $x \in W$ and $Ax = \mu x$, then $x = 0$. Then $W \subseteq S_p(A)$.

The proof writes $W$ as the sum of the generalized eigenspaces of the restriction $A|_W$
(`Module.End.iSup_maxGenEigenspace_eq_top`). Each of them lies in the corresponding generalized
eigenspace of $A$, and those of the eigenvalues that fail $p$ are $0$. -/
theorem invtSubmodule_le_spectralSubspace [IsAlgClosed K] [FiniteDimensional K V]
    {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hp : ∀ μ, ¬ p μ → ∀ x ∈ S, A x = μ • x → x = 0) :
    S ≤ A.spectralSubspace p := by
  have hS' : ∀ x ∈ S, A x ∈ S := (A.mem_invtSubmodule_iff_forall_mem_of_mem).1 hS
  have hall : ⨆ μ, A.genEigenspace μ ⊤ = ⊤ := iSup_maxGenEigenspace_eq_top A
  calc S = S ⊓ ⨆ μ, A.genEigenspace μ ⊤ := by rw [hall, inf_top_eq]
    _ = ⨆ μ, S ⊓ A.genEigenspace μ ⊤ := Submodule.inf_iSup_genEigenspace hS' ⊤
    _ ≤ A.spectralSubspace p := iSup_le fun μ => ?_
  by_cases hμ : p μ
  · exact inf_le_right.trans (maxGenEigenspace_le_spectralSubspace hμ)
  rw [Submodule.inf_genEigenspace A S hS']
  have h0 : genEigenspace (A.restrict hS') μ ⊤ = ⊥ := by
    by_contra h
    have h1 : HasUnifEigenvalue (A.restrict hS') μ ⊤ := h
    rw [hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)] at h1
    obtain ⟨x, hx⟩ := HasEigenvalue.exists_hasEigenvector h1
    have hAx : A x = μ • (x : V) := by
      simpa using congrArg Subtype.val hx.apply_eq_smul
    exact hx.2 (Subtype.ext (hp μ hμ x x.2 hAx))
  rw [h0, Submodule.map_bot]
  exact bot_le

/-- **Uniqueness of the invariant subspace of a spectral set.** Let $K$ be algebraically closed, let
$V$ be finite-dimensional, and let $A$ be an endomorphism of $V$. Let $W$ be an $A$-invariant
subspace on which every eigenvalue satisfies $p$: if $\neg p(\mu)$, $x \in W$ and $Ax = \mu x$,
then $x = 0$. If $\dim W = \dim S_p(A)$, then $W = S_p(A)$. See §7.3.2 and §7.6.2 of
[golub2013matrix].

The dimension of $S_p(A)$ is the sum of the algebraic multiplicities of the eigenvalues that
satisfy $p$. The proof combines `Module.End.invtSubmodule_le_spectralSubspace` with the equality
of dimensions. -/
theorem invtSubmodule_eq_spectralSubspace [IsAlgClosed K] [FiniteDimensional K V]
    {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hp : ∀ μ, ¬ p μ → ∀ x ∈ S, A x = μ • x → x = 0)
    (hdim : Module.finrank K S = Module.finrank K (A.spectralSubspace p)) :
    S = A.spectralSubspace p :=
  Submodule.eq_of_le_of_finrank_eq (invtSubmodule_le_spectralSubspace hS hp) hdim

/-! ### Diagonalizable endomorphisms -/

/-- **A diagonalizable endomorphism has no defective eigenvalue.** Let $f$ be an endomorphism of $V$
whose eigenspaces span $V$, that is, $\sum_{\mu \in K} \ker(f - \mu) = V$. Then for every
$\mu \in K$, the maximal generalized eigenspace of $\mu$ is the eigenspace:
$$G_\mu(f) = \ker(f - \mu).$$
This is the direction from diagonalizability in Proposition 1.7 of [saad2003iterative].

The idea of the proof: $f - \mu$ maps every other eigenspace into itself and is $0$ on
$\ker(f - \mu)$, so its range meets $\ker(f - \mu)$ only in $0$. A vector $v$ with
$(f - \mu)^2 v = 0$ therefore has $(f - \mu)v = 0$, and induction gives the result for all
powers. -/
theorem maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top {f : End K V}
    (hf : (⨆ μ : K, f.eigenspace μ) = ⊤) (μ : K) :
    f.maxGenEigenspace μ = f.eigenspace μ := by
  refine le_antisymm ?_ eigenspace_le_maxGenEigenspace
  set g := f - μ • (1 : End K V) with hg
  have hgx : ∀ x : V, g x = f x - μ • x := by
    intro x
    rw [hg]
    simp
  have hker : eigenspace f μ = LinearMap.ker g := by
    rw [hg, eigenspace_def]
  have hmapν : ∀ ν : K,
      Submodule.map g (eigenspace f ν) ≤ eigenspace f ν := by
    rintro ν _ ⟨x, hx, rfl⟩
    have hx' : f x = ν • x := mem_eigenspace_iff.1 hx
    have hgv : g x = (ν - μ) • x := by rw [hgx, hx', sub_smul]
    rw [mem_eigenspace_iff, hgv, map_smul, hx', smul_comm]
  have hmapμ : Submodule.map g (eigenspace f μ) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : f x = μ • x := mem_eigenspace_iff.1 hx
    rw [hgx, hx', sub_self]
  have hrange : LinearMap.range g ≤ ⨆ (ν : K) (_ : ν ≠ μ), eigenspace f ν := by
    have h1 : LinearMap.range g = Submodule.map g (⨆ ν : K, eigenspace f ν) := by
      rw [hf, Submodule.map_top]
    rw [h1, Submodule.map_iSup]
    refine iSup_le fun ν => ?_
    rcases eq_or_ne ν μ with rfl | hν
    · rw [hmapμ]
      exact bot_le
    · exact (hmapν ν).trans (le_iSup_of_le ν (le_iSup_of_le hν le_rfl))
  have hdisj := iSupIndep_def.1 (eigenspaces_iSupIndep f) μ
  have key : ∀ x : V, g (g x) = 0 → g x = 0 := by
    intro x hx
    refine Submodule.disjoint_def.1 hdisj (g x) ?_ (hrange (LinearMap.mem_range_self g x))
    rw [hker, LinearMap.mem_ker]
    exact hx
  have hpow : ∀ (k : ℕ) (x : V), (g ^ k) x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
        intro x hx
        rw [pow_zero, one_apply] at hx
        rw [hx, map_zero]
    | succ k ih =>
        intro x hx
        rw [pow_succ, mul_apply] at hx
        exact key x (ih (g x) hx)
  intro v hv
  rw [mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  rw [hker, LinearMap.mem_ker]
  exact hpow k v (by rw [hg]; exact hk)

/-! ### The spectral projector -/

section SpectralProjector

variable [IsAlgClosed K] [FiniteDimensional K V]

/-- **The spectral projector.** Let $K$ be algebraically closed, let $V$ be finite-dimensional, and
let $A$ be an endomorphism of $V$. The spectral projector $P_p$ of the eigenvalues selected by
$p$ is the projection onto $S_p(A)$ along $S_{\neg p}(A)$: every $x \in V$ is $x = u + w$ with
$u \in S_p(A)$ and $w \in S_{\neg p}(A)$ in exactly one way, and $P_p x = u$.

In general $P_p$ is an oblique projector. It is an orthogonal projection only when the two
subspaces are orthogonal, for example when $A$ is normal. For the predicate $\mu = l$ it is the
projector onto the generalized eigenspace $G_l(A)$. The definition is `Submodule.projection` for
the pair of `Module.End.isCompl_spectralSubspace`. -/
noncomputable def spectralProjector (A : End K V) (p : K → Prop) : End K V :=
  Submodule.projection _ _ (A.isCompl_spectralSubspace p)

/-- For every $x \in V$, $P_p x \in S_p(A)$. -/
@[simp]
theorem spectralProjector_apply_mem (x : V) : A.spectralProjector p x ∈ A.spectralSubspace p :=
  Submodule.projection_apply_mem _ _

/-- For every $x \in V$, $x - P_p x \in S_{\neg p}(A)$. -/
theorem sub_spectralProjector_mem (x : V) :
    x - A.spectralProjector p x ∈ A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.sub_projection_mem _ _

/-- The spectral projector fixes its range: if $x \in S_p(A)$, then $P_p x = x$. -/
theorem spectralProjector_apply_of_mem {x : V} (hx : x ∈ A.spectralSubspace p) :
    A.spectralProjector p x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- For $x \in V$, $P_p x = 0$ if and only if $x \in S_{\neg p}(A)$. -/
@[simp]
theorem spectralProjector_apply_eq_zero_iff {x : V} :
    A.spectralProjector p x = 0 ↔ x ∈ A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.projection_apply_eq_zero_iff _

/-- The kernel of the spectral projector is the spectral subspace of the other eigenvalues:
$\ker P_p = S_{\neg p}(A)$. -/
theorem ker_spectralProjector :
    LinearMap.ker (A.spectralProjector p) = A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.ker_projection _

/-- The range of the spectral projector is the spectral subspace of the selected eigenvalues:
$\operatorname{range} P_p = S_p(A)$. -/
theorem range_spectralProjector : LinearMap.range (A.spectralProjector p) = A.spectralSubspace p :=
  Submodule.range_projection _

/-- The spectral projector is idempotent: $P_p^2 = P_p$. -/
theorem isIdempotentElem_spectralProjector : IsIdempotentElem (A.spectralProjector p) :=
  Submodule.isIdempotentElem_projection _

/-- If $u \in S_p(A)$ and $w \in S_{\neg p}(A)$, then $P_p(u + w) = u$. -/
theorem spectralProjector_add_of_mem {u w : V} (hu : u ∈ A.spectralSubspace p)
    (hw : w ∈ A.spectralSubspace fun μ => ¬ p μ) : A.spectralProjector p (u + w) = u := by
  rw [map_add, spectralProjector_apply_of_mem hu, spectralProjector_apply_eq_zero_iff.mpr hw,
    add_zero]

/-- Let $W$ be a subspace of $V$. The spectral projector $P_p$ is injective on $W$ if and only if
$W \cap S_{\neg p}(A) = 0$. -/
theorem injOn_spectralProjector_iff {S : Submodule K V} :
    Set.InjOn (A.spectralProjector p) S ↔ Disjoint S (A.spectralSubspace fun μ => ¬ p μ) := by
  refine ⟨fun h => disjoint_iff_inf_le.mpr fun x hx => ?_, fun h => ?_⟩
  · have h0 : A.spectralProjector p x = 0 := spectralProjector_apply_eq_zero_iff.mpr hx.2
    simpa using h hx.1 (Submodule.zero_mem S) (by simpa using h0)
  · refine LinearMap.injOn_of_disjoint_ker (le_refl (S : Set V)) ?_
    rwa [ker_spectralProjector]

/-- Let $W$ be a subspace of $V$ with $W \cap S_{\neg p}(A) = 0$ and $\dim W = \dim S_p(A)$. Then
for every $u \in S_p(A)$ there is exactly one $s \in W$ with $P_p s = u$.

By `Module.End.injOn_spectralProjector_iff`, the first hypothesis says that $P_p$ is injective
on $W$. Then $P_p$ maps $W$ bijectively onto its image, and the equality of dimensions makes
this image all of $S_p(A)$. -/
theorem existsUnique_mem_spectralProjector_eq {S : Submodule K V}
    (hdisj : Disjoint S (A.spectralSubspace fun μ => ¬ p μ))
    (hrank : Module.finrank K S = Module.finrank K (A.spectralSubspace p))
    {u : V} (hu : u ∈ A.spectralSubspace p) :
    ∃! s : V, s ∈ S ∧ A.spectralProjector p s = u := by
  have hinj : Set.InjOn (A.spectralProjector p) S := injOn_spectralProjector_iff.mpr hdisj
  have hker : LinearMap.ker (A.spectralProjector p ∘ₗ S.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hx0
    simpa using hinj hx (Submodule.zero_mem S) (by simpa using hx0)
  have hrange : LinearMap.range (A.spectralProjector p ∘ₗ S.subtype) =
      S.map (A.spectralProjector p) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hfin : Module.finrank K ↥(S.map (A.spectralProjector p)) = Module.finrank K S := by
    have h := (A.spectralProjector p ∘ₗ S.subtype).finrank_range_add_finrank_ker
    rw [hker, hrange] at h
    simpa using h
  have hle : S.map (A.spectralProjector p) ≤ A.spectralSubspace p := by
    rw [← range_spectralProjector (A := A) (p := p)]
    exact LinearMap.map_le_range
  have heq : S.map (A.spectralProjector p) = A.spectralSubspace p :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfin, hrank])
  obtain ⟨s, hs, hsu⟩ := Submodule.mem_map.mp (heq.ge hu)
  refine ⟨s, ⟨hs, hsu⟩, ?_⟩
  rintro y ⟨hy, hyu⟩
  exact hinj hy hs (by rw [hyu, hsu])

end SpectralProjector

end Module.End
