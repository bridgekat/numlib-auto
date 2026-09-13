/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.NormalSpectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Lagrange

/-!
# Normal operators in finite dimension

A normal operator on a finite-dimensional inner product space is diagonalizable, its eigenspaces are
pairwise orthogonal, they are the eigenspaces of its adjoint at the conjugate eigenvalues, and its
adjoint is a polynomial in it. This is the spectral theorem for normal operators, and the last
statement is the algebraic form of it that the Faber–Manteuffel theory of short-recurrence Krylov
methods needs ([saad2003iterative], §6.10).

## Main results

The route avoids both Schur triangulation and the Jordan form, neither of which Mathlib has:

* `LinearMap.IsStarNormal.norm_adjoint_apply`: a normal `A` satisfies `‖A† v‖ = ‖A v‖`, hence
  `LinearMap.IsStarNormal.ker_adjoint_eq_ker`, `ker A† = ker A`.
* `LinearMap.IsStarNormal.ker_pow`: a normal `N` satisfies `ker Nᵏ = ker N` for `k ≠ 0`. Indeed if
  `N (N x) = 0` then `N x ∈ ker N = ker N†`, so `0 = ⟪N† (N x), x⟫ = ‖N x‖²`.
* A scalar shift of a normal operator is normal (`LinearMap.IsStarNormal.sub_smul_one`), so the
  previous item applied to `A - μ` says that a normal operator has no generalized eigenvectors:
  `LinearMap.IsStarNormal.maxGenEigenspace_eq_eigenspace`.
* Over an algebraically closed field the maximal generalized eigenspaces span
  (`Module.End.iSup_maxGenEigenspace_eq_top`), so the *eigenspaces* of a normal operator span:
  `LinearMap.IsStarNormal.iSup_eigenspace_eq_top`. That is diagonalizability, with no triangulation
  theorem in sight.
* The same shift argument identifies the eigenspaces of `A` and of `A†`
  (`LinearMap.IsStarNormal.eigenspace_adjoint`); the two operators share their eigenvectors, and
  their eigenvalues are conjugate. Conversely, an operator sharing its eigenvectors with its adjoint
  is normal (`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`), since the same inner product that
  forces the eigenvalues to be conjugate also forbids generalized eigenvectors.
* Distinct eigenvalues give orthogonal eigenspaces (`LinearMap.IsStarNormal.inner_eq_zero_of_ne`,
  `LinearMap.IsStarNormal.orthogonalFamily_eigenspaces`), and with diagonalizability the eigenspaces
  decompose the space orthogonally (`LinearMap.IsStarNormal.direct_sum_isInternal`), exactly as
  `LinearMap.IsSymmetric.direct_sum_isInternal` does in the self-adjoint case.
* Finally, a polynomial taking the value `conj μ` at every eigenvalue `μ` evaluates to `A†`
  (`LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq`), and Lagrange interpolation supplies one
  (`LinearMap.IsStarNormal.exists_aeval_eq_adjoint`).
  `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose` is the matrix form, `Aᴴ = q(A)`.
* Two commuting normal operators have a common orthonormal eigenbasis
  (`LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute`), and two commuting
  normal matrices are simultaneously unitarily diagonalizable
  (`Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute`), which is what makes the
  eigenvalues of `A + B` sums of eigenvalues of `A` and of `B` ([quarteroni2000numerical] §1.8).
  The proof splits each operator into commuting Hermitian parts and uses Mathlib's joint eigenbasis
  of a commuting family of symmetric operators; the four parts commute because the adjoint of a
  normal operator is a polynomial in it.
* `Matrix.IsStarNormal.spectral_theorem` is the unitary diagonalization of a normal matrix, and
  `Matrix.IsStarNormal.eq_sum_smul_vecMulVec` reads it as the sum of rank-one projectors
  `A = ∑ λ_i u_i u_iᴴ` onto the orthonormal eigenvectors.

## Implementation notes

Only the statements that need the eigenspaces to span assume `[IsAlgClosed 𝕜]`. Everything else —
the norm identity, the kernels, the shift, and the eigenspace identity in the direction `A ⟹ A†` —
holds over `ℝ` as well.

Dot notation does not reach these lemmas: they live in the `LinearMap` and `Matrix` namespaces while
the hypothesis `IsStarNormal A` is a root-level structure, so a normality hypothesis `hA` has to be
passed as `LinearMap.IsStarNormal.ker_adjoint_eq_ker hA` and not as `hA.ker_adjoint_eq_ker`. This
follows Mathlib's `ContinuousLinearMap.IsStarNormal` lemmas.
-/

open Module End Polynomial

open scoped ComplexConjugate

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {A N : E →ₗ[𝕜] E}

/-! ### Normality through norms -/

/-- A normal operator and its adjoint have the same norm at every vector: `‖A† v‖ = ‖A v‖`. Both
sides are the quadratic form of a Gram operator, `⟪v, (A† A) v⟫` and `⟪v, (A A†) v⟫`, and normality
says those two operators are equal. -/
theorem IsStarNormal.norm_adjoint_apply (hA : IsStarNormal A) (v : E) :
    ‖A.adjoint v‖ = ‖A v‖ := by
  have hc : A * A.adjoint = A.adjoint * A := by
    simpa only [star_eq_adjoint] using hA.star_comm_self.eq.symm
  have h : (inner 𝕜 (A.adjoint v) (A.adjoint v) : 𝕜) = inner 𝕜 (A v) (A v) := by
    calc (inner 𝕜 (A.adjoint v) (A.adjoint v) : 𝕜)
        = inner 𝕜 v (A (A.adjoint v)) := LinearMap.adjoint_inner_left A _ v
      _ = inner 𝕜 v (A.adjoint (A v)) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, hc]
      _ = inner 𝕜 (A v) (A v) := LinearMap.adjoint_inner_right A v (A v)
  have h2 : ((‖A.adjoint v‖ : 𝕜)) ^ 2 = ((‖A v‖ : 𝕜)) ^ 2 := by
    rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K]
    exact h
  have h3 : ‖A.adjoint v‖ ^ 2 = ‖A v‖ ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

/-- A normal operator and its adjoint kill the same vectors. -/
theorem IsStarNormal.adjoint_apply_eq_zero_iff (hA : IsStarNormal A) (x : E) :
    A.adjoint x = 0 ↔ A x = 0 := by
  rw [← norm_eq_zero (a := A.adjoint x), ← norm_eq_zero (a := A x),
    IsStarNormal.norm_adjoint_apply hA]

/-- A normal operator and its adjoint have the same kernel. -/
theorem IsStarNormal.ker_adjoint_eq_ker (hA : IsStarNormal A) : ker A.adjoint = ker A :=
  Submodule.ext fun x => by
    simp only [mem_ker, IsStarNormal.adjoint_apply_eq_zero_iff hA]

/-- A scalar shift of a normal operator is normal, because a scalar multiple of the identity
commutes with everything. -/
theorem IsStarNormal.sub_smul_one (hA : IsStarNormal A) (μ : 𝕜) :
    IsStarNormal (A - μ • (1 : E →ₗ[𝕜] E)) := by
  have hc : ∀ (c : 𝕜) (X : E →ₗ[𝕜] E), Commute (c • (1 : E →ₗ[𝕜] E)) X := by
    intro c X
    have h : Commute (algebraMap 𝕜 (E →ₗ[𝕜] E) c) X := Algebra.commutes c X
    rwa [Algebra.algebraMap_eq_smul_one] at h
  refine ⟨?_⟩
  have hstar : star (A - μ • (1 : E →ₗ[𝕜] E)) = star A - conj μ • (1 : E →ₗ[𝕜] E) := by
    rw [star_sub, star_smul, star_one, starRingEnd_apply]
  rw [hstar]
  exact Commute.sub_left (hA.star_comm_self.sub_right (hc μ (star A)).symm) (hc _ _)

/-- The adjoint of a scalar shift is the conjugate scalar shift of the adjoint. -/
theorem adjoint_sub_smul_one (A : E →ₗ[𝕜] E) (μ : 𝕜) :
    (A - μ • (1 : E →ₗ[𝕜] E)).adjoint = A.adjoint - conj μ • (1 : E →ₗ[𝕜] E) := by
  rw [← star_eq_adjoint, ← star_eq_adjoint, star_sub, star_smul, star_one, starRingEnd_apply]

/-! ### No generalized eigenvectors

The three lemmas below take as hypothesis only that the shifted operator kills a vector whenever it
does, `ker N ≤ ker N†`, which is what both a normality hypothesis and a shared-eigenvector
hypothesis supply. -/

private theorem apply_eq_zero_of_ker_le {N : E →ₗ[𝕜] E}
    (h : ∀ y : E, N y = 0 → N.adjoint y = 0) {x : E} (hx : N (N x) = 0) : N x = 0 := by
  have h1 : N.adjoint (N x) = 0 := h (N x) hx
  have h2 : (inner 𝕜 (N x) (N x) : 𝕜) = 0 := by
    rw [← LinearMap.adjoint_inner_right N x (N x), h1, inner_zero_right]
  exact inner_self_eq_zero.1 h2

private theorem ker_pow_succ_of_ker_le {N : E →ₗ[𝕜] E}
    (h : ∀ y : E, N y = 0 → N.adjoint y = 0) (j : ℕ) : ker (N ^ (j + 1)) = ker N := by
  induction j with
  | zero => rw [zero_add, pow_one]
  | succ j ih =>
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_ker] at hx ⊢
      have h1 : N x ∈ ker (N ^ (j + 1)) := by
        rw [mem_ker, ← Module.End.mul_apply, ← pow_succ]
        exact hx
      rw [ih, mem_ker] at h1
      exact apply_eq_zero_of_ker_le h h1
    · rw [mem_ker] at hx ⊢
      rw [pow_succ, Module.End.mul_apply, hx, map_zero]

private theorem maxGenEigenspace_eq_eigenspace_of_ker_le {A : E →ₗ[𝕜] E} {μ : 𝕜}
    (h : ∀ y : E, (A - μ • (1 : E →ₗ[𝕜] E)) y = 0 →
      (A - μ • (1 : E →ₗ[𝕜] E)).adjoint y = 0) :
    maxGenEigenspace A μ = eigenspace A μ := by
  refine le_antisymm (fun x hx => ?_) (by simpa using genEigenspace_le_maximal A μ 1)
  obtain ⟨k, hk⟩ := (mem_maxGenEigenspace A μ x).1 hx
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero, Module.End.one_apply] at hk
    rw [hk]
    exact Submodule.zero_mem _
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hmem : x ∈ ker ((A - μ • (1 : E →ₗ[𝕜] E)) ^ (j + 1)) := hk
    rw [ker_pow_succ_of_ker_le h j, ← eigenspace_def] at hmem
    exact hmem

/-- For a normal `N`, `N (N x) = 0` forces `N x = 0`: the vector `N x` lies in `ker N = ker N†`, so
`‖N x‖² = ⟪N† (N x), x⟫ = 0`. -/
theorem IsStarNormal.apply_eq_zero_of_apply_apply_eq_zero (hN : IsStarNormal N) {x : E}
    (h : N (N x) = 0) : N x = 0 :=
  apply_eq_zero_of_ker_le (fun y hy => (IsStarNormal.adjoint_apply_eq_zero_iff hN y).2 hy) h

/-- All powers of a normal operator have the same kernel: `ker Nᵏ = ker N` for `k ≠ 0`. -/
theorem IsStarNormal.ker_pow (hN : IsStarNormal N) {k : ℕ} (hk : k ≠ 0) :
    ker (N ^ k) = ker N := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact ker_pow_succ_of_ker_le (fun y hy => (IsStarNormal.adjoint_apply_eq_zero_iff hN y).2 hy) j

/-- A normal operator has no generalized eigenvectors: every maximal generalized eigenspace is
already an eigenspace. This is `LinearMap.IsStarNormal.ker_pow` applied to the normal operator `A -
μ`. -/
theorem IsStarNormal.maxGenEigenspace_eq_eigenspace (hA : IsStarNormal A) (μ : 𝕜) :
    maxGenEigenspace A μ = eigenspace A μ :=
  maxGenEigenspace_eq_eigenspace_of_ker_le fun y hy =>
    (IsStarNormal.adjoint_apply_eq_zero_iff (IsStarNormal.sub_smul_one hA μ) y).2 hy

private theorem iSup_eigenspace_eq_top_of_maxGen [IsAlgClosed 𝕜] {A : E →ₗ[𝕜] E}
    (h : ∀ μ : 𝕜, maxGenEigenspace A μ = eigenspace A μ) : ⨆ μ : 𝕜, eigenspace A μ = ⊤ := by
  simp_rw [← h]
  exact iSup_maxGenEigenspace_eq_top A

omit [FiniteDimensional 𝕜 E] in
/-- Two operators that agree on every eigenspace of a diagonalizable `A` are equal. -/
private theorem eq_of_forall_eigenspace {A : E →ₗ[𝕜] E} (hsup : ⨆ μ : 𝕜, eigenspace A μ = ⊤)
    {f g : E →ₗ[𝕜] E} (h : ∀ (μ : 𝕜) (x : E), x ∈ eigenspace A μ → f x = g x) : f = g := by
  have hker : (⨆ μ : 𝕜, eigenspace A μ) ≤ ker (f - g) :=
    iSup_le fun μ x hx => by
      rw [mem_ker, sub_apply, sub_eq_zero]
      exact h μ x hx
  rw [hsup, top_le_iff, ker_eq_top] at hker
  exact sub_eq_zero.1 hker

/-- **A normal operator on a finite-dimensional inner product space over an algebraically closed
field is diagonalizable**: its eigenspaces span. Over such a field the maximal generalized
eigenspaces always span, and for a normal operator they are the eigenspaces. -/
theorem IsStarNormal.iSup_eigenspace_eq_top [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    ⨆ μ : 𝕜, eigenspace A μ = ⊤ :=
  iSup_eigenspace_eq_top_of_maxGen (IsStarNormal.maxGenEigenspace_eq_eigenspace hA)

/-! ### A normal operator and its adjoint share their eigenvectors -/

/-- **A normal operator and its adjoint have the same eigenvectors**, with conjugate eigenvalues
([saad2003iterative], Lemma 1.15, the easy direction): `ker (A† - conj μ)` equals `ker (A - μ)`,
because `A - μ` is normal and a normal operator has the same kernel as its adjoint. -/
theorem IsStarNormal.eigenspace_adjoint (hA : IsStarNormal A) (μ : 𝕜) :
    eigenspace A.adjoint (conj μ) = eigenspace A μ := by
  rw [eigenspace_def, eigenspace_def, ← adjoint_sub_smul_one A μ]
  exact IsStarNormal.ker_adjoint_eq_ker (IsStarNormal.sub_smul_one hA μ)

/-- The eigenvalue of `A†` at a shared eigenvector is forced to be the conjugate one: `⟪x, A† x⟫ =
⟪A x, x⟫` reads as `ν ‖x‖² = conj μ ‖x‖²`. -/
private theorem adjoint_apply_eq_conj_smul {A : E →ₗ[𝕜] E} {μ ν : 𝕜} {x : E} (hx : A x = μ • x)
    (hν : A.adjoint x = ν • x) : A.adjoint x = conj μ • x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have h : (inner 𝕜 x (A.adjoint x) : 𝕜) = inner 𝕜 (A x) x := LinearMap.adjoint_inner_right A x x
    rw [hν, hx, inner_smul_right, inner_smul_left] at h
    have hxx : (inner 𝕜 x x : 𝕜) ≠ 0 := fun hc => hx0 (inner_self_eq_zero.1 hc)
    rw [hν, mul_right_cancel₀ hxx h]

/-- **An operator that shares its eigenvectors with its adjoint is normal** ([saad2003iterative],
Lemma 1.15, the substantial direction). The inner product `⟪x, A† x⟫ = ⟪A x, x⟫` forces the adjoint
eigenvalue to be `conj μ`; the same identity applied to `(A - μ) u = x` forces `‖x‖² = 0`, so there
are no generalized eigenvectors and `A` is diagonalizable; and on each eigenspace `A† A` and `A A†`
both act as `|μ|²`. -/
theorem isStarNormal_of_adjoint_apply_eq_smul [IsAlgClosed 𝕜] {A : E →ₗ[𝕜] E}
    (h : ∀ (μ : 𝕜) (x : E), A x = μ • x → ∃ ν : 𝕜, A.adjoint x = ν • x) : IsStarNormal A := by
  have hconj : ∀ (μ : 𝕜) (x : E), x ∈ eigenspace A μ → A.adjoint x = conj μ • x := by
    intro μ x hx
    obtain ⟨ν, hν⟩ := h μ x (mem_eigenspace_iff.1 hx)
    exact adjoint_apply_eq_conj_smul (mem_eigenspace_iff.1 hx) hν
  have hker : ∀ μ : 𝕜, ∀ y : E, (A - μ • (1 : E →ₗ[𝕜] E)) y = 0 →
      (A - μ • (1 : E →ₗ[𝕜] E)).adjoint y = 0 := by
    intro μ y hy
    have hy' : y ∈ eigenspace A μ := by rwa [eigenspace_def, mem_ker]
    rw [adjoint_sub_smul_one, sub_apply, smul_apply, Module.End.one_apply, hconj μ y hy',
      sub_self]
  have hsup : ⨆ μ : 𝕜, eigenspace A μ = ⊤ :=
    iSup_eigenspace_eq_top_of_maxGen fun μ =>
      maxGenEigenspace_eq_eigenspace_of_ker_le (hker μ)
  refine ⟨?_⟩
  change star A * A = A * star A
  rw [star_eq_adjoint]
  refine eq_of_forall_eigenspace hsup fun μ x hx => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, mem_eigenspace_iff.1 hx, hconj μ x hx,
    map_smul, map_smul, mem_eigenspace_iff.1 hx, hconj μ x hx, smul_smul, smul_smul, mul_comm]

/-! ### The spectral theorem for normal operators -/

/-- **The eigenspaces of a normal operator are mutually orthogonal.** If `A x = μ x` and `A y = ν y`
then `conj μ ⟪x, y⟫ = ⟪A x, y⟫ = ⟪x, A† y⟫ = conj ν ⟪x, y⟫`, using that `y` is an eigenvector of
`A†` for `conj ν`. -/
theorem IsStarNormal.inner_eq_zero_of_ne (hA : IsStarNormal A) {μ ν : 𝕜} (hμν : μ ≠ ν) {x y : E}
    (hx : x ∈ eigenspace A μ) (hy : y ∈ eigenspace A ν) : (inner 𝕜 x y : 𝕜) = 0 := by
  have hy' : A.adjoint y = conj ν • y :=
    mem_eigenspace_iff.1 (by rw [IsStarNormal.eigenspace_adjoint hA ν]; exact hy)
  have hx' : A x = μ • x := mem_eigenspace_iff.1 hx
  have key : conj μ * (inner 𝕜 x y : 𝕜) = conj ν * inner 𝕜 x y := by
    calc conj μ * (inner 𝕜 x y : 𝕜)
        = inner 𝕜 (A x) y := by rw [hx', inner_smul_left]
      _ = inner 𝕜 x (A.adjoint y) := (LinearMap.adjoint_inner_right A x y).symm
      _ = conj ν * inner 𝕜 x y := by rw [hy', inner_smul_right]
  have hne : conj μ - conj ν ≠ 0 :=
    sub_ne_zero.2 fun hc => hμν ((starRingEnd 𝕜).injective hc)
  have hzero : (conj μ - conj ν) * (inner 𝕜 x y : 𝕜) = 0 := by rw [sub_mul, key, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left hne

/-- The eigenspaces of a normal operator form an orthogonal family. -/
theorem IsStarNormal.orthogonalFamily_eigenspaces (hA : IsStarNormal A) :
    OrthogonalFamily 𝕜 (fun μ : 𝕜 => eigenspace A μ) fun μ => (eigenspace A μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨x, hx⟩ ⟨y, hy⟩
  exact IsStarNormal.inner_eq_zero_of_ne hA hμν hx hy

/-- The orthogonal family of eigenspaces, indexed by the eigenvalues rather than by all scalars;
this is the form `OrthogonalFamily.isInternal_iff` consumes. -/
theorem IsStarNormal.orthogonalFamily_eigenspaces' (hA : IsStarNormal A) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues A => eigenspace A μ) fun μ =>
      (eigenspace A μ).subtypeₗᵢ :=
  (IsStarNormal.orthogonalFamily_eigenspaces hA).comp Subtype.coe_injective

/-- **The spectral theorem for normal operators.** The eigenspaces of a normal operator on a
finite-dimensional inner product space over an algebraically closed field give an internal direct
sum decomposition of the space; by `LinearMap.IsStarNormal.orthogonalFamily_eigenspaces` that
decomposition is orthogonal. This is the counterpart of
`LinearMap.IsSymmetric.direct_sum_isInternal` for normal rather than self-adjoint operators. -/
theorem IsStarNormal.direct_sum_isInternal [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    DirectSum.IsInternal fun μ : Eigenvalues A => eigenspace A μ := by
  refine (IsStarNormal.orthogonalFamily_eigenspaces' hA).isInternal_iff.mpr ?_
  change (⨆ μ : { μ : 𝕜 // eigenspace A μ ≠ ⊥ }, eigenspace A μ)ᗮ = ⊥
  rw [iSup_ne_bot_subtype, IsStarNormal.iSup_eigenspace_eq_top hA,
    Submodule.top_orthogonal_eq_bot]

/-! ### The adjoint of a normal operator is a polynomial in it -/

/-- A polynomial that takes the value `conj μ` at every eigenvalue `μ` of a normal operator
evaluates to its adjoint: the two operators act as `conj μ` on the eigenspace at `μ`, and the
eigenspaces span. -/
theorem IsStarNormal.aeval_eq_adjoint_of_eval_eq [IsAlgClosed 𝕜] (hA : IsStarNormal A) {q : 𝕜[X]}
    (hq : ∀ μ : 𝕜, HasEigenvalue A μ → q.eval μ = conj μ) : aeval A q = A.adjoint := by
  refine eq_of_forall_eigenspace (IsStarNormal.iSup_eigenspace_eq_top hA) fun μ x hx => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have h2 : A.adjoint x = conj μ • x :=
      mem_eigenspace_iff.1 (by rw [IsStarNormal.eigenspace_adjoint hA μ]; exact hx)
    rw [aeval_apply_of_mem_apply_eq_smul (mem_eigenspace_iff.1 hx), h2,
      hq μ (hasEigenvalue_of_hasEigenvector ⟨hx, hx0⟩)]

/-- **The adjoint of a normal operator is a polynomial in it.** Take `q` interpolating `z ↦ conj z`
at the finitely many eigenvalues and apply `LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq`.

No degree bound is asserted, since a caller can reduce any such `q` modulo an annihilating
polynomial of `A`. -/
theorem IsStarNormal.exists_aeval_eq_adjoint [IsAlgClosed 𝕜] (hA : IsStarNormal A) :
    ∃ q : 𝕜[X], aeval A q = A.adjoint := by
  classical
  obtain ⟨s, hsmem⟩ : ∃ s : Finset 𝕜, ∀ μ : 𝕜, HasEigenvalue A μ → μ ∈ s :=
    ⟨(finite_hasEigenvalue A).toFinset, fun _ h => (Set.Finite.mem_toFinset _).2 h⟩
  obtain ⟨q, hq⟩ : ∃ q : 𝕜[X], ∀ μ ∈ s, q.eval μ = conj μ :=
    ⟨Lagrange.interpolate (ι := 𝕜) (F := 𝕜) s _root_.id (fun z => conj z),
      fun _ hμ => Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hμ⟩
  exact ⟨q, IsStarNormal.aeval_eq_adjoint_of_eval_eq hA fun μ hμ => hq μ (hsmem μ hμ)⟩

/-! ### The orthonormal eigenbasis of a normal operator -/

section EigenvectorBasis

variable {n : ℕ} [IsAlgClosed 𝕜]

/-- **An orthonormal basis of eigenvectors of a normal operator** on an `n`-dimensional inner
product space over an algebraically closed field.  The eigenspaces are mutually orthogonal and
decompose the space (`LinearMap.IsStarNormal.direct_sum_isInternal`), so an orthonormal basis of
each assembles into one of the whole space, subordinate to the decomposition.  This is the
counterpart of `LinearMap.IsSymmetric.eigenvectorBasis` for normal rather than self-adjoint
operators; unlike there the eigenvalues are not real, so `LinearMap.IsStarNormal.eigenvalues` takes
values in `𝕜` and no ordering is imposed. -/
noncomputable def IsStarNormal.eigenvectorBasis (hA : IsStarNormal A)
    (hn : Module.finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E :=
  (IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasis hn
    (IsStarNormal.orthogonalFamily_eigenspaces' hA)

/-- The eigenvalue of a normal operator at the `i`-th vector of
`LinearMap.IsStarNormal.eigenvectorBasis`. -/
noncomputable def IsStarNormal.eigenvalues (hA : IsStarNormal A) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : 𝕜 :=
  (((IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasisIndex hn i
    (IsStarNormal.orthogonalFamily_eigenspaces' hA) : Eigenvalues A) : 𝕜)

/-- `LinearMap.IsStarNormal.eigenvectorBasis` really is a basis of eigenvectors, with
`LinearMap.IsStarNormal.eigenvalues` naming the eigenvalues. -/
theorem IsStarNormal.apply_eigenvectorBasis (hA : IsStarNormal A) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) :
    A (IsStarNormal.eigenvectorBasis hA hn i) =
      IsStarNormal.eigenvalues hA hn i • IsStarNormal.eigenvectorBasis hA hn i :=
  mem_eigenspace_iff.1
    ((IsStarNormal.direct_sum_isInternal hA).subordinateOrthonormalBasis_subordinate hn i
      (IsStarNormal.orthogonalFamily_eigenspaces' hA))

end EigenvectorBasis

/-! ### Commuting normal operators -/

/-- In an algebraically closed `RCLike` field the imaginary unit is nonzero: `-1` is a square, and
if `I = 0` every scalar is real. -/
theorem _root_.RCLike.I_ne_zero_of_isAlgClosed [IsAlgClosed 𝕜] : (RCLike.I : 𝕜) ≠ 0 := by
  intro hI
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : 𝕜) two_pos
  have hzr := RCLike.re_add_im z
  rw [hI, mul_zero, add_zero] at hzr
  rw [← hzr, ← RCLike.ofReal_pow] at hz
  have h : (RCLike.re z) ^ 2 = -1 := by exact_mod_cast hz
  nlinarith [sq_nonneg (RCLike.re z)]

/-- The Hermitian part `(X + X†)/2` of an operator. -/
private noncomputable def hermPart (X : E →ₗ[𝕜] E) : E →ₗ[𝕜] E := (2⁻¹ : 𝕜) • (X + X.adjoint)

/-- The Hermitian matrix `(X - X†)/(2i)`, so that `X = hermPart X + i • skewPart X`. -/
private noncomputable def skewPart (X : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (2 * RCLike.I : 𝕜)⁻¹ • (X - X.adjoint)

private theorem hermPart_isSymmetric (X : E →ₗ[𝕜] E) : (hermPart X).IsSymmetric := by
  intro x y
  simp only [hermPart, smul_apply, add_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, adjoint_inner_left, adjoint_inner_right, map_inv₀, RCLike.conj_ofNat]
  ring

private theorem skewPart_isSymmetric (X : E →ₗ[𝕜] E) : (skewPart X).IsSymmetric := by
  intro x y
  simp only [skewPart, smul_apply, sub_apply, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, adjoint_inner_left, adjoint_inner_right, map_inv₀, map_mul, RCLike.conj_ofNat,
    RCLike.conj_I]
  rw [mul_neg, inv_neg]
  ring

private theorem hermPart_add_I_smul_skewPart (hI : (RCLike.I : 𝕜) ≠ 0) (X : E →ₗ[𝕜] E) :
    hermPart X + (RCLike.I : 𝕜) • skewPart X = X := by
  rw [hermPart, skewPart, smul_smul, mul_inv, ← mul_assoc, mul_comm (RCLike.I : 𝕜),
    mul_assoc, mul_inv_cancel₀ hI, mul_one, ← smul_add,
    show X + X.adjoint + (X - X.adjoint) = (2 : 𝕜) • X by module, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

private theorem commute_parts {X Y : E →ₗ[𝕜] E} (h₁ : Commute X Y) (h₂ : Commute X Y.adjoint)
    (h₃ : Commute X.adjoint Y) (h₄ : Commute X.adjoint Y.adjoint) :
    Commute (hermPart X) (hermPart Y) ∧ Commute (hermPart X) (skewPart Y) ∧
      Commute (skewPart X) (hermPart Y) ∧ Commute (skewPart X) (skewPart Y) := by
  simp only [hermPart, skewPart]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Commute.smul_left (Commute.smul_right ?_ _) _
  · exact (h₁.add_right h₂).add_left (h₃.add_right h₄)
  · exact (h₁.sub_right h₂).add_left (h₃.sub_right h₄)
  · exact (h₁.add_right h₂).sub_left (h₃.add_right h₄)
  · exact (h₁.sub_right h₂).sub_left (h₃.sub_right h₄)

omit [FiniteDimensional 𝕜 E] in
/-- A polynomial in `X` commutes with everything `X` commutes with. -/
private theorem commute_aeval_of_commute {X Y : E →ₗ[𝕜] E} (h : Commute Y X) (q : 𝕜[X]) :
    Commute Y (aeval X q) :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton 𝕜 X) h

/-- **Commuting normal operators have a common orthonormal eigenbasis** ([quarteroni2000numerical]
§1.8; the finite-dimensional case of the spectral theorem for commuting normal operators): over an
algebraically closed `RCLike` field, two normal operators that commute are simultaneously
diagonalized by an orthonormal basis.

The proof avoids restrictions to eigenspaces: write `X = H(X) + i S(X)` with `H(X) = (X + X†)/2`
and `S(X) = (X - X†)/(2i)` both symmetric, note that all four of `A, A†, B, B†` commute — `A` with
`A†` by normality, `A` with `B` by hypothesis, `A` with `B†` because `B† = q(B)` is a polynomial in
`B` (`LinearMap.IsStarNormal.exists_aeval_eq_adjoint`), and the rest by adjunction — so that the
four symmetric parts commute pairwise, and take the joint eigenbasis Mathlib provides for a
commuting family of symmetric operators
(`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`). -/
theorem IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute [IsAlgClosed 𝕜]
    {A B : E →ₗ[𝕜] E} (hA : IsStarNormal A) (hB : IsStarNormal B) (hAB : Commute A B) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) :
    ∃ (b : OrthonormalBasis (Fin n) 𝕜 E) (d e : Fin n → 𝕜),
      (∀ i, A (b i) = d i • b i) ∧ ∀ i, B (b i) = e i • b i := by
  classical
  have hI : (RCLike.I : 𝕜) ≠ 0 := RCLike.I_ne_zero_of_isAlgClosed
  -- the four operators commute pairwise
  obtain ⟨qA, hqA⟩ := IsStarNormal.exists_aeval_eq_adjoint hA
  obtain ⟨qB, hqB⟩ := IsStarNormal.exists_aeval_eq_adjoint hB
  have hAA' : Commute A A.adjoint := by
    have := hA.star_comm_self.symm
    rwa [star_eq_adjoint] at this
  have hBB' : Commute B B.adjoint := by
    have := hB.star_comm_self.symm
    rwa [star_eq_adjoint] at this
  have hAB' : Commute A B.adjoint := by
    have := commute_aeval_of_commute hAB qB
    rwa [hqB] at this
  have hA'B : Commute A.adjoint B := by
    have := commute_aeval_of_commute hAB.symm qA
    rw [hqA] at this
    exact this.symm
  have hA'B' : Commute A.adjoint B.adjoint := by
    have h := congrArg LinearMap.adjoint hAB.eq
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, adjoint_comp, adjoint_comp] at h
    exact h.symm
  obtain ⟨-, cAA₂, -, -⟩ := commute_parts (Commute.refl A) hAA' hAA'.symm (Commute.refl _)
  obtain ⟨cAB₁, cAB₂, cAB₃, cAB₄⟩ := commute_parts hAB hAB' hA'B hA'B'
  obtain ⟨-, cBB₂, -, -⟩ := commute_parts (Commute.refl B) hBB' hBB'.symm (Commute.refl _)
  -- the commuting family of symmetric parts
  set T : Fin 4 → E →ₗ[𝕜] E := ![hermPart A, skewPart A, hermPart B, skewPart B] with hT
  have hTsymm : ∀ i, (T i).IsSymmetric := by
    intro i
    fin_cases i
    · exact hermPart_isSymmetric A
    · exact skewPart_isSymmetric A
    · exact hermPart_isSymmetric B
    · exact skewPart_isSymmetric B
  have cAA₂' := cAA₂.symm
  have cAB₁' := cAB₁.symm
  have cAB₂' := cAB₂.symm
  have cAB₃' := cAB₃.symm
  have cAB₄' := cAB₄.symm
  have cBB₂' := cBB₂.symm
  have hTcomm : Pairwise (Function.onFun Commute T) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [hT, Function.onFun] <;>
      first | exact absurd rfl hij | assumption
  -- the joint eigenspaces, indexed by the finitely many nonzero ones
  set V : (Fin 4 → 𝕜) → Submodule 𝕜 E := fun α => ⨅ j, Module.End.eigenspace (T j) (α j)
    with hVdef
  have hVfam := IsSymmetric.orthogonalFamily_iInf_eigenspaces hTsymm
  have htop : ⨆ α, V α = ⊤ := IsSymmetric.iSup_iInf_eq_top_of_commute hTsymm hTcomm
  have hfin : {α | V α ≠ ⊥}.Finite := by
    refine (Set.Finite.pi fun j => Module.End.finite_hasEigenvalue (T j)).subset fun α hα => ?_
    refine Set.mem_univ_pi.mpr fun j => Module.End.hasEigenvalue_iff.mpr fun hbot => hα ?_
    exact le_bot_iff.mp ((iInf_le _ j).trans hbot.le)
  let _ : Fintype {α // V α ≠ ⊥} := hfin.fintype
  have hVfam' : OrthogonalFamily 𝕜 (fun α : {α // V α ≠ ⊥} => V α)
      fun α => (V α).subtypeₗᵢ := hVfam.comp Subtype.coe_injective
  have hV : DirectSum.IsInternal fun α : {α // V α ≠ ⊥} => V α := by
    refine hVfam'.isInternal_iff.mpr ?_
    rw [iSup_ne_bot_subtype, htop, Submodule.top_orthogonal_eq_bot]
  set b := hV.subordinateOrthonormalBasis hn hVfam' with hb
  set idx : Fin n → Fin 4 → 𝕜 := fun a => (hV.subordinateOrthonormalBasisIndex hn a hVfam').val
    with hidx
  have hmem : ∀ a j, T j (b a) = idx a j • b a := fun a j =>
    Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf _).mp (hV.subordinateOrthonormalBasis_subordinate hn a hVfam') j)
  refine ⟨b, fun a => idx a 0 + RCLike.I * idx a 1, fun a => idx a 2 + RCLike.I * idx a 3,
    fun a => ?_, fun a => ?_⟩
  · have h0 := hmem a 0
    have h1 := hmem a 1
    simp only [hT, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [← hermPart_add_I_smul_skewPart hI A, add_apply, smul_apply, h0, h1, smul_smul, add_smul]
  · have h2 := hmem a 2
    have h3 := hmem a 3
    simp only [hT, Matrix.cons_val] at h2 h3
    rw [← hermPart_add_I_smul_skewPart hI B, add_apply, smul_apply, h2, h3, smul_smul, add_smul]

end LinearMap

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private theorem toEuclideanLin_mul' (X Y : Matrix n n 𝕜) :
    toEuclideanLin (X * Y) = toEuclideanLin X * toEuclideanLin Y :=
  map_mul (toLpLinAlgEquiv (R := 𝕜) (n := n) 2) X Y

private theorem star_toEuclideanLin (A : Matrix n n 𝕜) :
    star (toEuclideanLin A) = toEuclideanLin (star A) := by
  rw [LinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- A matrix is normal exactly when the operator it defines on Euclidean space is: `toEuclideanLin`
is an algebra equivalence carrying the conjugate transpose to the adjoint. -/
theorem isStarNormal_toEuclideanLin_iff {A : Matrix n n 𝕜} :
    IsStarNormal (toEuclideanLin A) ↔ IsStarNormal A := by
  constructor
  · intro h
    refine ⟨?_⟩
    refine toEuclideanLin.injective ?_
    rw [toEuclideanLin_mul', toEuclideanLin_mul', ← star_toEuclideanLin]
    exact h.star_comm_self.eq
  · intro h
    refine ⟨?_⟩
    rw [star_toEuclideanLin]
    exact h.star_comm_self.map (toLpLinAlgEquiv (R := 𝕜) (n := n) 2)

/-- `q(A) = Aᴴ` for a matrix is `q(op A) = (op A)†` for the operator it defines. -/
theorem aeval_eq_conjTranspose_iff {A : Matrix n n 𝕜} {q : 𝕜[X]} :
    aeval (toEuclideanLin A) q = LinearMap.adjoint (toEuclideanLin A) ↔ aeval A q = Aᴴ := by
  have halg : aeval (toEuclideanLin A) q = toEuclideanLin (aeval A q) :=
    aeval_algHom_apply (toLpLinAlgEquiv (R := 𝕜) (n := n) 2) A q
  rw [halg, ← toEuclideanLin_conjTranspose_eq_adjoint]
  exact toEuclideanLin.injective.eq_iff

/-- **The conjugate transpose of a normal matrix is a polynomial in the matrix**: over an
algebraically closed field a normal `A` satisfies `Aᴴ = q(A)` for some `q`. This is
`LinearMap.IsStarNormal.exists_aeval_eq_adjoint` transported along the algebra equivalence between
matrices and operators on Euclidean space, under which the conjugate transpose is the adjoint. -/
theorem IsStarNormal.exists_aeval_eq_conjTranspose [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) : ∃ q : 𝕜[X], aeval A q = Aᴴ := by
  obtain ⟨q, hq⟩ :=
    LinearMap.IsStarNormal.exists_aeval_eq_adjoint (isStarNormal_toEuclideanLin_iff.2 hA)
  exact ⟨q, aeval_eq_conjTranspose_iff.1 hq⟩

omit [DecidableEq n] in
/-- A normal matrix over an algebraically closed field has an orthonormal basis of eigenvectors,
indexed by the index type of the matrix. -/
private theorem exists_orthonormalBasis_eigenvector [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) :
    ∃ (c : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) (d : n → 𝕜),
      ∀ j, A *ᵥ ⇑(c j) = d j • ⇑(c j) := by
  classical
  have hT : IsStarNormal (toEuclideanLin A) := isStarNormal_toEuclideanLin_iff.2 hA
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  refine ⟨(LinearMap.IsStarNormal.eigenvectorBasis hT finrank_euclideanSpace).reindex e,
    fun j => LinearMap.IsStarNormal.eigenvalues hT finrank_euclideanSpace (e.symm j),
    fun j => ?_⟩
  have h := LinearMap.IsStarNormal.apply_eigenvectorBasis hT finrank_euclideanSpace (e.symm j)
  rw [OrthonormalBasis.reindex_apply]
  simpa [toLpLin_apply] using congrArg WithLp.ofLp h

/-- The change-of-basis matrix `U` from the standard basis to an orthonormal basis of eigenvectors
diagonalizes: `Uᴴ A U = diagonal d`. This is the step from an eigenbasis to a unitary
diagonalization, shared by the spectral theorems for one normal matrix and for a commuting pair. -/
theorem conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal
    (c : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)) {A : Matrix n n 𝕜} {d : n → 𝕜}
    (hcd : ∀ j, A *ᵥ ⇑(c j) = d j • ⇑(c j)) :
    ((EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis)ᴴ * A
      * (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis = diagonal d := by
  set U : Matrix n n 𝕜 := (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix c.toBasis with hU
  have hUmem : U ∈ Matrix.unitaryGroup n 𝕜 :=
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c
  have hentry : ∀ i j, U i j = ⇑(c j) i := fun _ _ => rfl
  have hAU : A * U = U * diagonal d := by
    ext i j
    have h1 : (A *ᵥ ⇑(c j)) i = d j * ⇑(c j) i := by rw [hcd j]; rfl
    calc (A * U) i j = (A *ᵥ ⇑(c j)) i := by
          rw [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hentry k j]
      _ = d j * ⇑(c j) i := h1
      _ = U i j * d j := by rw [hentry i j, mul_comm]
      _ = (U * diagonal d) i j := (Matrix.mul_diagonal _ _ _ _).symm
  rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    (Unitary.mem_iff.1 hUmem).1, Matrix.one_mul]

/-- **The spectral theorem for normal matrices**: a square matrix over an algebraically closed field
is normal exactly when it is unitarily similar to a diagonal matrix.  The forward direction
assembles the orthonormal eigenbasis `LinearMap.IsStarNormal.eigenvectorBasis` into the
change-of-basis matrix; the converse is a computation with diagonal matrices, which commute with
their conjugate transposes.  This is the counterpart of `Matrix.IsHermitian.spectral_theorem` for
normal rather than Hermitian matrices ([saad2003iterative], Thm 1.14). -/
theorem IsStarNormal.spectral_theorem [IsAlgClosed 𝕜] {A : Matrix n n 𝕜} :
    IsStarNormal A ↔
      ∃ U ∈ Matrix.unitaryGroup n 𝕜, ∃ d : n → 𝕜, Uᴴ * A * U = Matrix.diagonal d := by
  constructor
  · intro hA
    obtain ⟨c, d, hcd⟩ := exists_orthonormalBasis_eigenvector hA
    exact ⟨_, (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c, d,
      conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c hcd⟩
  · rintro ⟨U, hUmem, d, hd⟩
    have hstar : star U * U = 1 := (Unitary.mem_iff.1 hUmem).1
    have hstar' : U * star U = 1 := (Unitary.mem_iff.1 hUmem).2
    have hA : A = U * Matrix.diagonal d * Uᴴ := by
      rw [← hd, ← Matrix.star_eq_conjTranspose]
      calc A = U * star U * A * (U * star U) := by
            rw [hstar', Matrix.one_mul, Matrix.mul_one]
        _ = U * (star U * A * U) * star U := by simp only [Matrix.mul_assoc]
    have hAH : Aᴴ = U * Matrix.diagonal (star d) * Uᴴ := by
      rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    have hdiag : Matrix.diagonal (star d) * Matrix.diagonal d =
        Matrix.diagonal d * Matrix.diagonal (star d) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
    have key : ∀ X Y : Matrix n n 𝕜, U * X * Uᴴ * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
      intro X Y
      rw [← Matrix.star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hstar, Matrix.one_mul]
    refine ⟨?_⟩
    rw [Matrix.star_eq_conjTranspose]
    calc Aᴴ * A
        = U * Matrix.diagonal (star d) * Uᴴ * (U * Matrix.diagonal d * Uᴴ) := by
          rw [← hAH, ← hA]
      _ = U * (Matrix.diagonal (star d) * Matrix.diagonal d) * Uᴴ := key _ _
      _ = U * (Matrix.diagonal d * Matrix.diagonal (star d)) * Uᴴ := by rw [hdiag]
      _ = U * Matrix.diagonal d * Uᴴ * (U * Matrix.diagonal (star d) * Uᴴ) := (key _ _).symm
      _ = A * Aᴴ := by rw [← hAH, ← hA]

/-- **Commuting normal matrices are simultaneously unitarily diagonalizable**
([quarteroni2000numerical] §1.8, the third consequence of the Schur decomposition): for normal
`A`, `B` with `A * B = B * A` there is a unitary `U` with `Uᴴ A U = diagonal d` and
`Uᴴ B U = diagonal e`; then `Uᴴ (A + B) U = diagonal (d + e)`, so the eigenvalues of `A + B` are
the sums `d i + e i` of eigenvalues of `A` and `B` sharing the eigenvector `U e_i`. The matrix
form of `LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute`. -/
theorem IsStarNormal.exists_unitary_conj_diagonal_of_commute [IsAlgClosed 𝕜] {A B : Matrix n n 𝕜}
    (hA : IsStarNormal A) (hB : IsStarNormal B) (hAB : Commute A B) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d e : n → 𝕜,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e := by
  have hTA := isStarNormal_toEuclideanLin_iff.2 hA
  have hTB := isStarNormal_toEuclideanLin_iff.2 hB
  have hTAB : Commute (toEuclideanLin A) (toEuclideanLin B) := by
    change toEuclideanLin A * toEuclideanLin B = toEuclideanLin B * toEuclideanLin A
    rw [← toEuclideanLin_mul', ← toEuclideanLin_mul', hAB.eq]
  obtain ⟨b, d, e, hd, he⟩ :=
    LinearMap.IsStarNormal.exists_orthonormalBasis_eigenvector_of_commute hTA hTB hTAB
      finrank_euclideanSpace
  set eq : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with heq
  set c := b.reindex eq with hc
  refine ⟨_, (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary c,
    fun j => d (eq.symm j), fun j => e (eq.symm j), ?_, ?_⟩
  · rw [star_eq_conjTranspose]
    refine conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c fun j => ?_
    have h := hd (eq.symm j)
    rw [hc, OrthonormalBasis.reindex_apply]
    simpa [toLpLin_apply] using congrArg WithLp.ofLp h
  · rw [star_eq_conjTranspose]
    refine conjTranspose_toMatrix_mul_mul_toMatrix_eq_diagonal c fun j => ?_
    have h := he (eq.symm j)
    rw [hc, OrthonormalBasis.reindex_apply]
    simpa [toLpLin_apply] using congrArg WithLp.ofLp h

/-- A unitary diagonalization `Uᴴ A U = diagonal d` written as a sum of rank-one projectors onto
the columns of `U`: `A = ∑ i, d i • u_i u_iᴴ` ([quarteroni2000numerical] §1.8, display after
Property 1.5). -/
theorem eq_sum_smul_vecMulVec_of_conj_eq_diagonal {U A : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) {d : n → 𝕜} (hd : star U * A * U = diagonal d) :
    A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i)) := by
  have hstar : star U * U = 1 := (Unitary.mem_iff.1 hU).1
  have hstar' : U * star U = 1 := (Unitary.mem_iff.1 hU).2
  have hA : A = U * diagonal d * star U := by
    rw [← hd]
    calc A = U * star U * A * (U * star U) := by rw [hstar', Matrix.one_mul, Matrix.mul_one]
      _ = U * (star U * A * U) * star U := by simp only [Matrix.mul_assoc]
  rw [hA]
  ext i j
  rw [Matrix.sum_apply, Matrix.mul_apply]
  simp only [mul_diagonal, smul_apply, vecMulVec_apply, transpose_apply, Pi.star_apply,
    star_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The spectral decomposition of a normal matrix** as a sum of rank-one projectors
([quarteroni2000numerical] §1.8, second consequence of the Schur decomposition): a normal matrix
over an algebraically closed field is `A = U Λ Uᴴ = ∑ i, λ_i u_i u_iᴴ` for the unitary `U` of
`Matrix.IsStarNormal.spectral_theorem`, whose columns `u_i = Uᵀ i` are an orthonormal eigenbasis. -/
theorem IsStarNormal.eq_sum_smul_vecMulVec [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) :
    ∃ U ∈ unitaryGroup n 𝕜, ∃ d : n → 𝕜, star U * A * U = diagonal d ∧
      A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i)) := by
  obtain ⟨U, hU, d, hd⟩ := IsStarNormal.spectral_theorem.mp hA
  rw [← star_eq_conjTranspose] at hd
  exact ⟨U, hU, d, hd, eq_sum_smul_vecMulVec_of_conj_eq_diagonal hU hd⟩

end Matrix
