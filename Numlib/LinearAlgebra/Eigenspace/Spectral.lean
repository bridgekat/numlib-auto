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

The *spectral subspace* of an endomorphism `A` for the eigenvalues selected by a predicate `p` is
the sum of the corresponding generalized eigenspaces, `⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ`
(`Module.End.spectralSubspace`). It is the invariant subspace attached to a part of the spectrum:
the stable subspace of the Hamiltonian–Schur form (`p μ := μ.re < 0`), the dominant subspace of
subspace iteration (`p` selects the `m` largest moduli), the generalized eigenspace of one
eigenvalue (`p := (· = l)`), the invariant subspace of a spectral set `Λ` (`p := (· ∈ Λ)`).

## Main definitions

* `Module.End.spectralSubspace A p`.
* `Module.End.spectralProjector A p`: over an algebraically closed field in finite dimension, the
  projection onto `A.spectralSubspace p` along `A.spectralSubspace (¬ p ·)`, an *oblique* projector
  (the Riesz projector of the selected eigenvalues).

## Main statements

* `Module.End.spectralSubspace_mem_invtSubmodule`: spectral subspaces are invariant.
* `Module.End.isCompl_spectralSubspace`: over an algebraically closed field in finite dimension
  the spectral subspaces of `p` and of `¬ p` are complementary.
* `Module.End.invtSubmodule_le_spectralSubspace` and `Module.End.invtSubmodule_eq_spectralSubspace`:
  an invariant subspace on which every eigenvalue satisfies `p` lies in `A.spectralSubspace p`, and
  equals it when the dimensions agree — the uniqueness of the invariant subspace of a spectral set.
* `Module.End.maxGenEigenspace_eq_eigenspace_of_iSup_eigenspace_eq_top`: when the eigenspaces span,
  every generalized eigenspace is an eigenspace (a diagonalizable endomorphism has no defective
  eigenvalue).
-/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The *spectral subspace* of `A` for the eigenvalues satisfying `p`: the sum of their generalized
eigenspaces. -/
def spectralSubspace (A : End K V) (p : K → Prop) : Submodule K V :=
  ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ

variable {A : End K V} {p q : K → Prop}

theorem spectralSubspace_def (A : End K V) (p : K → Prop) :
    A.spectralSubspace p = ⨆ μ, ⨆ _ : p μ, A.maxGenEigenspace μ :=
  rfl

/-- The generalized eigenspace of a selected eigenvalue lies in the spectral subspace. -/
theorem maxGenEigenspace_le_spectralSubspace {μ : K} (hμ : p μ) :
    A.maxGenEigenspace μ ≤ A.spectralSubspace p :=
  le_iSup₂_of_le μ hμ le_rfl

/-- The spectral subspace of a single eigenvalue is its generalized eigenspace. -/
@[simp]
theorem spectralSubspace_eq (A : End K V) (l : K) :
    A.spectralSubspace (· = l) = A.maxGenEigenspace l :=
  iSup_iSup_eq_left

/-- Spectral subspaces grow with the set of selected eigenvalues. -/
theorem spectralSubspace_mono (h : ∀ μ, p μ → q μ) : A.spectralSubspace p ≤ A.spectralSubspace q :=
  iSup₂_le fun μ hμ => maxGenEigenspace_le_spectralSubspace (h μ hμ)

/-- **Spectral subspaces are invariant.** -/
theorem spectralSubspace_mem_invtSubmodule (A : End K V) (p : K → Prop) :
    A.spectralSubspace p ∈ A.invtSubmodule := by
  rw [mem_invtSubmodule_iff_map_le, spectralSubspace, Submodule.map_iSup]
  refine iSup_mono fun μ => ?_
  rw [Submodule.map_iSup]
  refine iSup_mono fun _ => ?_
  exact Submodule.map_le_iff_le_comap.2 (A.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) μ)

/-- The elementwise form of `Module.End.spectralSubspace_mem_invtSubmodule`. -/
theorem apply_mem_spectralSubspace {x : V} (hx : x ∈ A.spectralSubspace p) :
    A x ∈ A.spectralSubspace p :=
  A.spectralSubspace_mem_invtSubmodule p hx

/-- **The spectral splitting of a set of eigenvalues.** Over an algebraically closed field in finite
dimension, the spectral subspaces of `p` and of its complement are complementary: disjointness is
the independence of the generalized eigenspaces, split along the two halves of `p`; codisjointness
is `iSup_split` together with the fact that the generalized eigenspaces span. -/
theorem isCompl_spectralSubspace [IsAlgClosed K] [FiniteDimensional K V] (A : End K V)
    (p : K → Prop) : IsCompl (A.spectralSubspace p) (A.spectralSubspace fun μ => ¬ p μ) where
  disjoint := (A.independent_maxGenEigenspace).disjoint_biSup_biSup
    (s := {μ | p μ}) (t := {μ | ¬ p μ}) (Set.disjoint_left.mpr fun _ ha ha' => ha' ha)
  codisjoint := by
    rw [codisjoint_iff, spectralSubspace, spectralSubspace, ← iSup_split (A.maxGenEigenspace) p,
      A.iSup_maxGenEigenspace_eq_top]

/-- An invariant subspace on which every eigenvalue satisfies `p` lies in the spectral subspace of
`p`: over an algebraically closed field, `S` is the sum of the generalized eigenspaces of `A|_S`
(`Module.End.iSup_maxGenEigenspace_eq_top`), each inside the corresponding one of `A`, and those
of eigenvalues outside `p` vanish. -/
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

/-- **Uniqueness of the invariant subspace of a spectral set** ([golub2013matrix] §7.3.2, §7.6.2):
over an algebraically closed field, an `A`-invariant subspace `S` on which every eigenvalue of `A`
satisfies `p` (`A x = μ x`, `x ∈ S`, `¬ p μ` force `x = 0`) and whose dimension is that of
`A.spectralSubspace p` (the sum of the algebraic multiplicities) *is* that subspace. -/
theorem invtSubmodule_eq_spectralSubspace [IsAlgClosed K] [FiniteDimensional K V]
    {S : Submodule K V} (hS : S ∈ A.invtSubmodule)
    (hp : ∀ μ, ¬ p μ → ∀ x ∈ S, A x = μ • x → x = 0)
    (hdim : Module.finrank K S = Module.finrank K (A.spectralSubspace p)) :
    S = A.spectralSubspace p :=
  Submodule.eq_of_le_of_finrank_eq (invtSubmodule_le_spectralSubspace hS hp) hdim

/-! ### Diagonalizable endomorphisms -/

/-- **A diagonalizable endomorphism has no defective eigenvalue**: if the eigenspaces of `f` span
the whole space, the maximal generalized eigenspace of `μ` is already the eigenspace of `μ`
([saad2003iterative] Proposition 1.7, the direction from diagonalizability). The reason is that
`f - μ` maps every *other* eigenspace into itself and annihilates the `μ`-eigenspace, so its range
misses the `μ`-eigenspace; a vector killed by `(f - μ)²` therefore has `(f - μ) v` in both, hence
zero, and the general power follows by induction. -/
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

/-- **The spectral projector** of the eigenvalues picked out by `p`: the projection onto
`A.spectralSubspace p` along the spectral subspace of the remaining eigenvalues. It is *oblique*
— an orthogonal projection only when the two subspaces are orthogonal, as for a normal `A` — and
taking `p := (· = l)` gives the projector onto a single generalized eigenspace. -/
noncomputable def spectralProjector (A : End K V) (p : K → Prop) : End K V :=
  Submodule.projection _ _ (A.isCompl_spectralSubspace p)

/-- The projector lands in the spectral subspace of the selected eigenvalues. -/
@[simp]
theorem spectralProjector_apply_mem (x : V) : A.spectralProjector p x ∈ A.spectralSubspace p :=
  Submodule.projection_apply_mem _ _

/-- The complementary part of `x` lies in the spectral subspace of the discarded eigenvalues. -/
theorem sub_spectralProjector_mem (x : V) :
    x - A.spectralProjector p x ∈ A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.sub_projection_mem _ _

/-- The projector fixes the spectral subspace it projects onto. -/
theorem spectralProjector_apply_of_mem {x : V} (hx : x ∈ A.spectralSubspace p) :
    A.spectralProjector p x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- The projector kills exactly the spectral subspace of the discarded eigenvalues. -/
@[simp]
theorem spectralProjector_apply_eq_zero_iff {x : V} :
    A.spectralProjector p x = 0 ↔ x ∈ A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.projection_apply_eq_zero_iff _

/-- The kernel of the spectral projector is the spectral subspace of the discarded eigenvalues. -/
theorem ker_spectralProjector :
    LinearMap.ker (A.spectralProjector p) = A.spectralSubspace fun μ => ¬ p μ :=
  Submodule.ker_projection _

/-- The range of the spectral projector is the spectral subspace of the selected eigenvalues. -/
theorem range_spectralProjector : LinearMap.range (A.spectralProjector p) = A.spectralSubspace p :=
  Submodule.range_projection _

/-- A projector is idempotent. -/
theorem isIdempotentElem_spectralProjector : IsIdempotentElem (A.spectralProjector p) :=
  Submodule.isIdempotentElem_projection _

/-- The projector reads off the first summand of the spectral splitting. -/
theorem spectralProjector_add_of_mem {u w : V} (hu : u ∈ A.spectralSubspace p)
    (hw : w ∈ A.spectralSubspace fun μ => ¬ p μ) : A.spectralProjector p (u + w) = u := by
  rw [map_add, spectralProjector_apply_of_mem hu, spectralProjector_apply_eq_zero_iff.mpr hw,
    add_zero]

/-- The spectral projector is injective on a subspace exactly when that subspace meets the spectral
subspace of the discarded eigenvalues only in `0`. -/
theorem injOn_spectralProjector_iff {S : Submodule K V} :
    Set.InjOn (A.spectralProjector p) S ↔ Disjoint S (A.spectralSubspace fun μ => ¬ p μ) := by
  refine ⟨fun h => disjoint_iff_inf_le.mpr fun x hx => ?_, fun h => ?_⟩
  · have h0 : A.spectralProjector p x = 0 := spectralProjector_apply_eq_zero_iff.mpr hx.2
    simpa using h hx.1 (Submodule.zero_mem S) (by simpa using h0)
  · refine LinearMap.injOn_of_disjoint_ker (le_refl (S : Set V)) ?_
    rwa [ker_spectralProjector]

/-- **A starting subspace has a unique preimage for each vector of the spectral subspace.** If the
spectral projector is injective on `S` and `S` has the dimension of the spectral subspace, then
every `u` of that subspace is `P s` for exactly one `s ∈ S`: injectivity makes `P` a bijection from
`S` onto its image by rank–nullity, and the equality of dimensions promotes the image to the whole
spectral subspace. -/
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
