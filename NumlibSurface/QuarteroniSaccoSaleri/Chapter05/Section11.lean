import Numlib.Eigen.KrylovEigen
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section10

/-!
# Quarteroni–Sacco–Saleri §5.11: the Lanczos method

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.11, over the backbone `Numlib/Eigen/MinMax` (Courant–Fischer),
`Numlib/Krylov/Lanczos` (the tridiagonal matrices `H_m` of the Lanczos process),
`Numlib/Eigen/RayleighRitz` (the Ritz values as the eigenvalues of the compression of `A` to the
Krylov subspace, and their interlacing with the eigenvalues of `A`) and `Numlib/Eigen/KrylovEigen`
(the Kaniel–Paige–Saad bound and the identification of the eigenvalues of `H_m` with the Ritz
values).

## Conventions

The symmetric `A ∈ ℝ^{n×n}` is `Matrix (Fin n) (Fin n) ℝ` with `hA : A.IsSymm`, acting on
`EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin`; its eigenvalues in the order (5.66),
`λ_1 ≥ … ≥ λ_n`, are `(hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin :
Fin n → ℝ` (`0`-based, so `λ_i` is the value at `i − 1`) with the orthonormal eigenvectors
`u_i = (hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin (i − 1)`. The
Rayleigh quotient `r(x) = xᵀ A x / xᵀ x` is `rayleigh A x` for `x ∈ ℝⁿ`, the backbone's
`LinearMap.rayleighQuotient (toEuclideanLin A)`. The Lanczos matrices `H_m = V_mᵀ A V_m` of §4.4.3
generated from `q^(1)` are `lanczosTridiag A q₁ m`, the backbone's `Lanczos.tridiag`, whose
entries are `⟪v_i, A v_j⟫` for the Lanczos vectors `v_i = Arnoldi.vec (toEuclideanLin A) q₁ i`
(`lanczosTridiag_apply`); their eigenvalues `η_1 ≥ … ≥ η_m` are `lanczosEigenvalues A q₁ m`, and,
as long as the process has not broken down (`finrank 𝒦_m(A, q₁) = m`), they are the eigenvalues
of the compression of `A` to `𝒦_m(A, q₁)`, the Ritz values (`lanczosEigenvalues_eq`).

## Contents

* `rayleigh`, `rayleigh_eq_rayleighQuotient`, `courantFischer` — the Rayleigh quotient and the
  Courant–Fischer theorem as displayed in §5.11.
* `lanczosTridiag`, `lanczosTridiag_apply`, `lanczosEigenvalues`, `lanczosEigenvalues_eq` — the
  Lanczos matrices and their eigenvalues.
* `equation_5_67` — `λ_1(H_m) = max r ≤ λ_1(A)`, `λ_m(H_m) = min r ≥ λ_n(A)` over `𝒦_m`.
* `property_5_12` — the Kaniel–Paige bound for `η_1`, and `property_5_12_min` the mirror bound
  for `η_m`.

## Not formalized

Example 5.18 is numerical; Program 45 is not a node; the reorthogonalization remarks are prose.
-/

open Filter Finset Matrix Polynomial Topology Krylov

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### The Rayleigh quotient and Courant–Fischer -/

/-- The **Rayleigh quotient** `r(x) = xᵀ A x / xᵀ x` of a nonnull `x ∈ ℝⁿ` (§5.11). -/
noncomputable def rayleigh (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

/-- The book's `r(x)` is the backbone's `LinearMap.rayleighQuotient` of `toEuclideanLin A`:
`⟪A x, x⟫ = xᵀ A x` and `‖x‖² = xᵀ x` on `ℝⁿ`. -/
theorem rayleigh_eq_rayleighQuotient (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    rayleigh A (WithLp.ofLp x) = (toEuclideanLin A).rayleighQuotient x := by
  rw [LinearMap.rayleighQuotient, rayleigh, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    ofLp_toEuclideanLin]
  simp

/-- **The Courant–Fischer theorem** as displayed in §5.11: for a symmetric `A ∈ ℝ^{n×n}` with
eigenvalues ordered as in (5.66), `λ_1(A) = max_{x ≠ 0} r(x)` and `λ_n(A) = min_{x ≠ 0} r(x)`.
Backbone `LinearMap.IsSymmetric.rayleighQuotient_mem_Icc` for the bounds and
`LinearMap.IsSymmetric.rayleighQuotient_eigenvectorBasis` for their attainment (the extreme cases
of `LinearMap.IsSymmetric.isGreatest_eigenvalues` and `isLeast_eigenvalues`). -/
theorem courantFischer {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hA : A.IsSymm) :
    IsGreatest {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x}
        ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin 0) ∧
      IsLeast {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x}
        ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin (Fin.last N)) := by
  set hA' := hA.isSymmetric_toEuclideanLin
  have hne : ∀ x : Fin (N + 1) → ℝ, x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (N + 1))) ≠ 0 :=
    fun x hx h => hx (by simpa using congrArg WithLp.ofLp h)
  have hmem : ∀ i, hA'.eigenvalues finrank_euclideanSpace_fin i ∈
      {c | ∃ x : Fin (N + 1) → ℝ, x ≠ 0 ∧ c = rayleigh A x} := fun i =>
    ⟨WithLp.ofLp (hA'.eigenvectorBasis finrank_euclideanSpace_fin i),
      fun h => hA'.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin i (by
        simpa using congrArg (WithLp.toLp 2) h),
      by rw [rayleigh_eq_rayleighQuotient, hA'.rayleighQuotient_eigenvectorBasis]⟩
  refine ⟨⟨hmem 0, ?_⟩, ⟨hmem (Fin.last N), ?_⟩⟩
  · rintro c ⟨x, hx, rfl⟩
    have h := hA'.rayleighQuotient_mem_Icc finrank_euclideanSpace_fin (hne x hx)
    rw [← rayleigh_eq_rayleighQuotient] at h
    exact h.2
  · rintro c ⟨x, hx, rfl⟩
    have h := hA'.rayleighQuotient_mem_Icc finrank_euclideanSpace_fin (hne x hx)
    rw [← rayleigh_eq_rayleighQuotient] at h
    exact h.1

/-! ### The Lanczos matrices -/

/-- **The Lanczos matrices** `H_m = V_mᵀ A V_m` of §4.4.3 (the tridiagonalization of `A` from the
starting vector `q^(1)`): the backbone's `Lanczos.tridiag`, the real symmetric tridiagonal matrix
of the coefficients `α_j`, `β_j` of the Lanczos recurrence. -/
noncomputable def lanczosTridiag (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Lanczos.tridiag (toEuclideanLin A) q₁ m

/-- `H_m = V_mᵀ A V_m` entrywise: `(H_m)_ij = v_iᵀ A v_j` for the Lanczos vectors `v_i`
(`Arnoldi.vec`), which vanishes off the three diagonals. Backbone
`Lanczos.hessenbergSq_eq_map_tridiag`. -/
theorem lanczosTridiag_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (i j : Fin m) :
    lanczosTridiag A q₁ m i j = inner ℝ (Arnoldi.vec (toEuclideanLin A) q₁ i)
      (toEuclideanLin A (Arnoldi.vec (toEuclideanLin A) q₁ j)) := by
  have h := congrFun (congrFun (Lanczos.hessenbergSq_eq_map_tridiag q₁
    hA.isSymmetric_toEuclideanLin m) i) j
  rw [Arnoldi.hessenbergSq, Matrix.of_apply, Matrix.map_apply, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  exact h.symm

/-- The eigenvalues `η_1 ≥ η_2 ≥ … ≥ η_m` of `H_m`, sorted decreasingly and indexed by `Fin m`
(Mathlib's `Matrix.IsHermitian.eigenvalues₀` reindexed along `Fintype.card_fin`). -/
noncomputable def lanczosEigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    (m : ℕ) : Fin m → ℝ :=
  (isHermitian_iff_isSymm.mpr (Lanczos.tridiag_isSymm (toEuclideanLin A) q₁ m)).eigenvalues₀ ∘
    Fin.cast (Fintype.card_fin m).symm

/-- **The eigenvalues of `H_m` are the Ritz values**: as long as the Lanczos process has not broken
down (`finrank 𝒦_m(A, q^(1)) = m`), the sorted eigenvalues of `H_m` are the sorted eigenvalues of
the compression of `A` to the Krylov subspace `𝒦_m(A, q^(1))`. Backbone
`Lanczos.eigenvalues_tridiag_eq_eigenvalues_compression`. -/
theorem lanczosEigenvalues_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ}
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) :
    lanczosEigenvalues A q₁ m =
      (compression.isSymmetric (toEuclideanLin A) (Krylov.subspace (toEuclideanLin A) q₁ m)
        hA.isSymmetric_toEuclideanLin).eigenvalues hm := by
  rw [lanczosEigenvalues, Lanczos.eigenvalues_tridiag_eq_eigenvalues_compression q₁
    hA.isSymmetric_toEuclideanLin hm]
  ext i
  simp [Fin.cast]

/-- A Krylov subspace of dimension `m` in `ℝⁿ` has `m ≤ n`: the index bookkeeping of (5.67). -/
theorem le_of_finrank_krylov_eq (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n))
    {m : ℕ} (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) : m ≤ n :=
  hm ▸ (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin

/-- **(5.67).** For the Lanczos matrices `H_m = V_mᵀ A V_m` of a symmetric `A` (before breakdown),
`λ_1(H_m) = max_{y ∈ 𝒦_m, y ≠ 0} r(y) ≤ λ_1(A)` and `λ_m(H_m) = min_{y ∈ 𝒦_m, y ≠ 0} r(y) ≥ λ_n(A)`,
where `y = V_m x` runs over the Krylov subspace `𝒦_m(A, q^(1)) = range V_m` as `x ≠ 0` runs over
`ℝ^m` (and `r(V_m x) = (V_m x)ᵀ A (V_m x) / xᵀ x`, the columns of `V_m` being orthonormal). At
each step the extremal eigenvalues of `H_m` are thus a lower and an upper bound for those of `A`.
Backbone `Krylov.rayleighQuotient_compression` with
`LinearMap.IsSymmetric.rayleighQuotient_mem_Icc` and `rayleighQuotient_eigenvectorBasis` for the
compression (the variational identities), `LinearMap.IsSymmetric.eigenvalues_compression_le` and
`LinearMap.IsSymmetric.eigenvalues_le_eigenvalues_compression` (Cauchy interlacing) for the
bounds. -/
theorem equation_5_67 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (q₁ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m) :
    IsGreatest {c | ∃ y ∈ Krylov.subspace (toEuclideanLin A) q₁ m, y ≠ 0 ∧
        c = rayleigh A (WithLp.ofLp y)} (lanczosEigenvalues A q₁ m ⟨0, hm0⟩) ∧
      lanczosEigenvalues A q₁ m ⟨0, hm0⟩ ≤
        (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
          ⟨0, lt_of_lt_of_le hm0 (le_of_finrank_krylov_eq A q₁ hm)⟩ ∧
      IsLeast {c | ∃ y ∈ Krylov.subspace (toEuclideanLin A) q₁ m, y ≠ 0 ∧
        c = rayleigh A (WithLp.ofLp y)} (lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩) ∧
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
          ⟨n - 1, by have := le_of_finrank_krylov_eq A q₁ hm; omega⟩ ≤
        lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ := by
  set hA' := hA.isSymmetric_toEuclideanLin
  set K := Krylov.subspace (toEuclideanLin A) q₁ m with hK
  set hC := compression.isSymmetric (toEuclideanLin A) K hA'
  have hmn : m ≤ n := le_of_finrank_krylov_eq A q₁ hm
  rw [lanczosEigenvalues_eq hA q₁ hm]
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0.ne'
  have hlast : (⟨m' + 1 - 1, by omega⟩ : Fin (m' + 1)) = Fin.last m' := Fin.ext (by simp)
  -- the variational identities
  have hmem : ∀ i, hC.eigenvalues hm i ∈
      {c | ∃ y ∈ K, y ≠ 0 ∧ c = rayleigh A (WithLp.ofLp y)} := fun i =>
    ⟨(hC.eigenvectorBasis hm i : EuclideanSpace ℝ (Fin n)), (hC.eigenvectorBasis hm i).2,
      fun h => hC.eigenvectorBasis_ne_zero hm i (Subtype.ext h),
      by rw [rayleigh_eq_rayleighQuotient, ← rayleighQuotient_compression,
        hC.rayleighQuotient_eigenvectorBasis]⟩
  have hbound : ∀ y ∈ K, y ≠ 0 → rayleigh A (WithLp.ofLp y) ∈
      Set.Icc (hC.eigenvalues hm (Fin.last m')) (hC.eigenvalues hm 0) := fun y hy hy0 => by
    have h := hC.rayleighQuotient_mem_Icc hm (x := ⟨y, hy⟩) fun h => hy0 (congrArg Subtype.val h)
    rw [rayleighQuotient_compression] at h
    rwa [rayleigh_eq_rayleighQuotient]
  refine ⟨⟨hmem 0, ?_⟩, ?_, ?_, ?_⟩
  · rintro c ⟨y, hy, hy0, rfl⟩
    exact (hbound y hy hy0).2
  · exact hA'.eigenvalues_compression_le K finrank_euclideanSpace_fin hm hmn 0
  · rw [hlast]
    refine ⟨hmem (Fin.last m'), ?_⟩
    rintro c ⟨y, hy, hy0, rfl⟩
    exact (hbound y hy hy0).1
  · rw [hlast]
    have h := hA'.eigenvalues_le_eigenvalues_compression K finrank_euclideanSpace_fin hm hmn
      (Fin.last m')
    convert h using 3
    simp
    omega

/-! ### Property 5.12 -/

/-- **Property 5.12 (Kaniel–Paige).** Let `A ∈ ℝ^{n×n}` be symmetric with eigenvalues ordered as
in (5.66) and orthonormal eigenvectors `u_1, …, u_n`, and let `η_1 ≥ … ≥ η_m` be the eigenvalues
of `H_m` (before breakdown). With `cos φ_1 = |(q^(1))ᵀ u_1|` — `φ_1` the angle between `q^(1)`
and `u_1`, `Submodule.angle` of the line through `q^(1)` — `ρ_1 = (λ_1 − λ_2)/(λ_2 − λ_n)` and
`T_{m−1}` the Chebyshev polynomial of degree `m − 1`,

`λ_1 ≥ η_1 ≥ λ_1 − (λ_1 − λ_n) tan²φ_1 / T_{m−1}(1 + 2ρ_1)²`.

Backbone `Lanczos.kaniel_paige_saad` at the first index (the deflation product is empty) through
`lanczosEigenvalues_eq`, with `RayleighRitz`'s `cosAngle_span_singleton` for `cos φ_1`. The
strict inequalities `λ_1 > λ_2 > λ_n` keep `ρ_1` finite; `(q^(1))ᵀ u_1 ≠ 0` keeps `tan φ_1`
finite, and `q^(1)` is a unit vector. -/
theorem property_5_12 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hn : 2 ≤ n)
    {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m)
    (hgap : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨0, by omega⟩)
    (hspread : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨1, by omega⟩)
    (hc : inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
      ⟨0, by omega⟩) ≠ 0) :
    let lam := (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
    let φ₁ := (ℝ ∙ q₁).angle
      ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin ⟨0, by omega⟩)
    let ρ₁ := (lam ⟨0, by omega⟩ - lam ⟨1, by omega⟩) / (lam ⟨1, by omega⟩ - lam ⟨n - 1, by omega⟩)
    Real.cos φ₁ = |inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis
        finrank_euclideanSpace_fin ⟨0, by omega⟩)| ∧
      lanczosEigenvalues A q₁ m ⟨0, hm0⟩ ≤ lam ⟨0, by omega⟩ ∧
      lam ⟨0, by omega⟩ - (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) * Real.tan φ₁ ^ 2 /
          ((Chebyshev.T ℝ (m - 1 : ℕ)).eval (1 + 2 * ρ₁)) ^ 2 ≤
        lanczosEigenvalues A q₁ m ⟨0, hm0⟩ := by
  intro lam φ₁ ρ₁
  set hA' := hA.isSymmetric_toEuclideanLin
  set u := hA'.eigenvectorBasis finrank_euclideanSpace_fin
  have hq₁0 : q₁ ≠ 0 := by simp [← norm_pos_iff, hq₁]
  have hu0 : u ⟨0, by omega⟩ ≠ 0 := hA'.eigenvectorBasis_ne_zero finrank_euclideanSpace_fin _
  have hcos : Real.cos φ₁ = |inner ℝ q₁ (u ⟨0, by omega⟩)| := by
    rw [Submodule.cos_angle, Submodule.cosAngle_span_singleton hq₁0, hq₁, u.norm_eq_one, mul_one,
      div_one, Real.norm_eq_abs]
  have htan : Real.tan φ₁ = (ℝ ∙ q₁).tanAngle (u ⟨0, by omega⟩) := Submodule.tan_angle _ hu0
  rw [lanczosEigenvalues_eq hA q₁ hm]
  have hkps := Lanczos.kaniel_paige_saad hA' finrank_euclideanSpace_fin hm ⟨0, hm0⟩ ⟨0, by omega⟩
    ⟨1, by omega⟩ ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl rfl
    (fun j => Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    (fun j => Fin.le_iff_val_le_val.mpr (by simp; omega))
    (by rwa [real_inner_comm]) hgap hspread
    (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _))
    (k := m - 1) (by simp; omega)
  have hmin : IsMin (⟨0, hm0⟩ : Fin m) := fun j _ => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  simp only [Finset.Iio_eq_empty.mpr hmin, Finset.prod_empty, one_mul, Set.mem_Icc,
    div_pow] at hkps
  refine ⟨hcos, by linarith [hkps.1], ?_⟩
  simp only [lam, ρ₁]
  rw [htan, mul_div_assoc]
  linarith [hkps.2]

/-! ### Auxiliary facts about `-A`

Property 5.12 for the smallest Ritz value is Property 5.12 for `-A`, whose Krylov subspaces are
those of `A` and whose eigenvalues and Ritz values are the negatives of those of `A`, in reversed
order. The lemmas of this section are the general facts that reduction needs; they are stated here
for want of a home in the backbone, and each says in its doc comment where it belongs.
-/

section Helpers

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The negative of a symmetric operator is symmetric.

Belongs in `Numlib/Eigen/MinMax.lean`; written here because this round's task did not own that
module. -/
theorem isSymmetric_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (-T).IsSymmetric := fun x y => by
  simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, hT x y]

/-- The Rayleigh quotient of `-T` is the negative of that of `T`.

Belongs in `Numlib/Eigen/MinMax.lean`. -/
theorem rayleighQuotient_neg (T : E →ₗ[𝕜] E) (x : E) :
    (-T).rayleighQuotient x = -T.rayleighQuotient x := by
  simp [LinearMap.rayleighQuotient, inner_neg_left, neg_div]

variable [FiniteDimensional 𝕜 E] {n : ℕ}

/-- The sorted eigenvalues depend on the operator only, not on the proof that it is symmetric.

Belongs in `Numlib/Eigen/MinMax.lean`. -/
theorem eigenvalues_congr {T T' : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hT' : T'.IsSymmetric)
    (h : T = T') (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i = hT'.eigenvalues hn i := by
  subst h; rfl

/-- **The eigenvalues of `-T` are the negatives of those of `T`, in reversed order**: with both
lists sorted decreasingly, the `i`-th eigenvalue of `-T` is minus the `(n - 1 - i)`-th of `T`. The
proof is Courant–Fischer: negating the Rayleigh quotient exchanges the max–min characterization of
`hT.eigenvalues hn i` (`isGreatest_eigenvalues`, over subspaces of dimension `i + 1`) with the
min–max characterization of `hT.eigenvalues hn i.rev` (`isLeast_eigenvalues`, over subspaces of
dimension `n - i.rev = i + 1`), so the two sets of bounds coincide.

Belongs in `Numlib/Eigen/MinMax.lean`. -/
theorem eigenvalues_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : (isSymmetric_neg hT).eigenvalues hn i = -hT.eigenvalues hn i.rev := by
  have hrev : n - ((i.rev : Fin n) : ℕ) = (i : ℕ) + 1 := by
    have := i.isLt
    simp only [Fin.val_rev]
    omega
  refine ((isSymmetric_neg hT).isGreatest_eigenvalues hn i).unique ⟨?_, ?_⟩
  · obtain ⟨⟨S, hS, hbd⟩, -⟩ := hT.isLeast_eigenvalues hn i.rev
    refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
    rw [rayleighQuotient_neg]
    linarith [hbd x hx hx0]
  · rintro c ⟨S, hS, hc⟩
    have hmem : -c ∈ {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - ((i.rev : Fin n) : ℕ) ∧
        ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} := by
      refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
      have := hc x hx hx0
      rw [rayleighQuotient_neg] at this
      linarith
    have := (hT.isLeast_eigenvalues hn i.rev).2 hmem
    linarith


omit [FiniteDimensional 𝕜 E] in
/-- The compression of `-T` to a subspace is the negative of the compression of `T`.

Belongs in `Numlib/Analysis/InnerProductSpace/Projection/Compression.lean`. -/
theorem compression_neg (T : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    compression (-T) K = -compression T K :=
  LinearMap.ext fun x => by simp [compression]

/-- The eigenvalues of the compressions to two equal subspaces agree. The subspaces are variables,
so that `subst` can do the transport that a `rw` inside a dependent type cannot.

Belongs in `Numlib/Eigen/MinMax.lean`. -/
theorem eigenvalues_compression_congr {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {K L : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K = L) {m : ℕ}
    (hK : Module.finrank 𝕜 K = m) (hL : Module.finrank 𝕜 L = m) (i : Fin m) :
    (compression.isSymmetric T K hT).eigenvalues hK i
      = (compression.isSymmetric T L hT).eigenvalues hL i := by
  subst hKL; rfl

omit [FiniteDimensional 𝕜 E] in
/-- `(-T)^i v = (-1)^i (T^i v)`.

Belongs in `Numlib/Krylov/Subspace.lean`. -/
theorem apply_pow_neg (T : E →ₗ[𝕜] E) (v : E) (i : ℕ) :
    ((-T) ^ i) v = (-1 : 𝕜) ^ i • (T ^ i) v := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hsplit : ((-T) ^ (i + 1)) v = (-T) (((-T) ^ i) v) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hsplit, ih, LinearMap.neg_apply, map_smul, ← Module.End.mul_apply, ← pow_succ',
      pow_succ']
    module

omit [FiniteDimensional 𝕜 E] in
/-- **The Krylov subspaces of `-T` are those of `T`**: the generators differ by the signs
`(-1)^i`, which do not change a span.

Belongs in `Numlib/Krylov/Subspace.lean`. -/
theorem krylovSubspace_neg (T : E →ₗ[𝕜] E) (v : E) (m : ℕ) :
    Krylov.subspace (-T) v m = Krylov.subspace T v m := by
  refine le_antisymm ?_ ?_ <;> rw [Krylov.subspace, Krylov.subspace, Submodule.span_le] <;>
    rintro _ ⟨i, rfl⟩ <;> simp only [SetLike.mem_coe]
  · change ((-T) ^ (i : ℕ)) v ∈ _
    rw [apply_pow_neg]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · change (T ^ (i : ℕ)) v ∈ _
    have h := apply_pow_neg (-T) v (i : ℕ)
    rw [neg_neg] at h
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


omit [FiniteDimensional 𝕜 E] in
/-- The angle between a subspace and a vector does not change when the vector is rescaled.

Belongs in `Numlib/Analysis/InnerProductSpace/Projection/Angle.lean`. -/
theorem tanAngle_smul (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {c : 𝕜} (hc : c ≠ 0)
    (u : E) : K.tanAngle (c • u) = K.tanAngle u := by
  rw [Submodule.tanAngle, Submodule.tanAngle, map_smul, ← smul_sub, norm_smul, norm_smul,
    mul_div_mul_left _ _ (norm_ne_zero_iff.2 hc)]

/-- **A simple extreme eigenvalue of `-T` has the same eigenvector line as its partner for `T`**:
if the `i.rev`-th eigenvalue of `T` is simple, the `i`-th eigenvector of `-T` is a nonzero multiple
of the `i.rev`-th eigenvector of `T`. Expanding the eigenvector of `-T` in the eigenbasis of `T`,
the coefficients at the other indices carry the factor `λ_j - λ_{i.rev} ≠ 0` and vanish.

Belongs in `Numlib/Eigen/MinMax.lean`. -/
theorem exists_smul_eigenvectorBasis_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n)
    (hsimple : ∀ j : Fin n, j ≠ i.rev → hT.eigenvalues hn j ≠ hT.eigenvalues hn i.rev) :
    ∃ c : 𝕜, c ≠ 0 ∧
      (isSymmetric_neg hT).eigenvectorBasis hn i = c • hT.eigenvectorBasis hn i.rev := by
  set b := hT.eigenvectorBasis hn with hb
  set w := (isSymmetric_neg hT).eigenvectorBasis hn i with hw
  have hTw : T w = (hT.eigenvalues hn i.rev : 𝕜) • w := by
    have h := (isSymmetric_neg hT).apply_eigenvectorBasis hn i
    rw [eigenvalues_neg hT hn i, LinearMap.neg_apply] at h
    have h' := congrArg Neg.neg h
    rwa [neg_neg, RCLike.ofReal_neg, neg_smul, neg_neg] at h'
  have hzero : ∀ j : Fin n, j ≠ i.rev → b.repr w j = 0 := by
    intro j hj
    have h1 := hT.eigenvectorBasis_apply_self_apply hn w j
    rw [hTw, map_smul] at h1
    simp only [PiLp.smul_apply, smul_eq_mul] at h1
    have h2 : ((hT.eigenvalues hn j : 𝕜) - (hT.eigenvalues hn i.rev : 𝕜)) * b.repr w j = 0 := by
      rw [sub_mul]
      rw [← h1]
      ring
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) (hsimple j hj)
    · exact h3
  have hsum : ∑ j, b.repr w j • b j = w := b.sum_repr w
  rw [Finset.sum_eq_single i.rev (fun j _ hj => by rw [hzero j hj, zero_smul])
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  refine ⟨b.repr w i.rev, ?_, hsum.symm⟩
  intro h0
  rw [h0, zero_smul] at hsum
  exact (isSymmetric_neg hT).eigenvectorBasis_ne_zero hn i hsum.symm

end Helpers

variable {n : ℕ}

/-- **Property 5.12, the smallest eigenvalue** (the display after Property 5.12). In the setting of
`property_5_12` — `A` symmetric with eigenvalues `λ_1 ≥ … ≥ λ_n` and orthonormal eigenvectors
`u_1, …, u_n`, `η_1 ≥ … ≥ η_m` the eigenvalues of `H_m` — with `cos φ_n = |(q^(1))ᵀ u_n|` and
`ρ_n = (λ_{n-1} - λ_n)/(λ_1 - λ_{n-1})`,

`λ_n ≤ η_m ≤ λ_n + (λ_1 - λ_n) tan²φ_n / T_{m-1}(1 + 2ρ_n)²`.

This is `property_5_12` for `-A`: the Krylov subspaces are the same (`krylovSubspace_neg`), the
compression is negated (`compression_neg`), and sorted eigenvalues are negated and reversed
(`eigenvalues_neg`), so the largest Ritz value of `-A` is `-η_m` and the largest eigenvalue of `-A`
is `-λ_n`. The strict inequalities `λ_n < λ_{n-1} < λ_1` keep `ρ_n` finite and make `λ_n` simple,
which is what identifies the eigenvector of `-A` for `-λ_n` with `u_n` up to a scalar
(`exists_smul_eigenvectorBasis_neg`); `(q^(1))ᵀ u_n ≠ 0` keeps `tan φ_n` finite. -/
theorem property_5_12_min {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (hn : 2 ≤ n)
    {q₁ : EuclideanSpace ℝ (Fin n)} (hq₁ : ‖q₁‖ = 1) {m : ℕ} (hm0 : 0 < m)
    (hm : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) q₁ m) = m)
    (hgap : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨n - 2, by omega⟩)
    (hspread : (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
        ⟨n - 2, by omega⟩ <
      (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin ⟨0, by omega⟩)
    (hc : inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
      ⟨n - 1, by omega⟩) ≠ 0) :
    let lam := (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace_fin
    let φₙ := (ℝ ∙ q₁).angle
      ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace_fin
        ⟨n - 1, by omega⟩)
    let ρₙ := (lam ⟨n - 2, by omega⟩ - lam ⟨n - 1, by omega⟩) /
      (lam ⟨0, by omega⟩ - lam ⟨n - 2, by omega⟩)
    Real.cos φₙ = |inner ℝ q₁ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis
        finrank_euclideanSpace_fin ⟨n - 1, by omega⟩)| ∧
      lam ⟨n - 1, by omega⟩ ≤ lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ ∧
      lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ ≤
        lam ⟨n - 1, by omega⟩ + (lam ⟨0, by omega⟩ - lam ⟨n - 1, by omega⟩) * Real.tan φₙ ^ 2 /
          ((Chebyshev.T ℝ (m - 1 : ℕ)).eval (1 + 2 * ρₙ)) ^ 2 := by
  intro lam φₙ ρₙ
  set T := toEuclideanLin A with hTd
  set hT := hA.isSymmetric_toEuclideanLin with hTdef
  set hnE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
    with hnEdef
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set il : Fin n := ⟨n - 1, by omega⟩ with hil
  set il1 : Fin n := ⟨n - 2, by omega⟩ with hil1
  have hrev0 : (i0.rev : Fin n) = il := by
    apply Fin.ext; simp [Fin.val_rev, hi0, hil]
  have hrev1 : (i1.rev : Fin n) = il1 := by
    apply Fin.ext; simp [Fin.val_rev, hi1, hil1]
  have hrevl : (il.rev : Fin n) = i0 := by
    apply Fin.ext; simp only [Fin.val_rev, hi0, hil]; omega
  -- the eigenvector of `-T` for its largest eigenvalue is a multiple of `u_n`
  have hsimple : ∀ j : Fin n, j ≠ i0.rev →
      hT.eigenvalues hnE j ≠ hT.eigenvalues hnE i0.rev := by
    intro j hj
    rw [hrev0] at hj ⊢
    have hjl : j ≤ il1 := by
      have := j.isLt
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      exact Fin.le_def.2 (by simp only [hil1]; omega)
    have hanti := hT.eigenvalues_antitone hnE hjl
    intro h
    rw [h] at hanti
    exact absurd hanti (not_le.2 hgap)
  obtain ⟨c, hc0, hcw⟩ := exists_smul_eigenvectorBasis_neg hT hnE i0 hsimple
  rw [hrev0] at hcw
  -- the Krylov subspace and the compression
  have hmneg : Module.finrank ℝ (Krylov.subspace (-T) q₁ m) = m := by
    rw [krylovSubspace_neg]; exact hm
  have hkps := Lanczos.kaniel_paige_saad (isSymmetric_neg hT) hnE hmneg ⟨0, hm0⟩ i0 i1 i0 il
    rfl (by simp [hi0, hi1]) (fun j => Fin.le_def.2 (Nat.zero_le _))
    (fun j => Fin.le_def.2 (by simp only [hil]; omega))
    (by rw [hcw, real_inner_smul_left]
        exact mul_ne_zero hc0 (fun h => hc (by rw [real_inner_comm]; exact h)))
    (by rw [eigenvalues_neg hT hnE i0, eigenvalues_neg hT hnE i1, hrev0, hrev1]; linarith)
    (by rw [eigenvalues_neg hT hnE i1, eigenvalues_neg hT hnE il, hrev1, hrevl]; linarith)
    (fun j hj => absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _))
    (k := m - 1) (by simp; omega)
  -- rewrite the three quantities of the conclusion
  have hrevm : ((⟨0, hm0⟩ : Fin m).rev) = ⟨m - 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
  have hηm : (compression.isSymmetric (-T) (Krylov.subspace (-T) q₁ m)
      (isSymmetric_neg hT)).eigenvalues hmneg ⟨0, hm0⟩
      = -lanczosEigenvalues A q₁ m ⟨m - 1, by omega⟩ := by
    rw [eigenvalues_compression_congr (isSymmetric_neg hT) (krylovSubspace_neg T q₁ m) hmneg hm,
      eigenvalues_congr _ (isSymmetric_neg (compression.isSymmetric T (Krylov.subspace T q₁ m) hT))
        (compression_neg T (Krylov.subspace T q₁ m)) hm,
      eigenvalues_neg (compression.isSymmetric T (Krylov.subspace T q₁ m) hT) hm,
      hrevm, lanczosEigenvalues_eq hA q₁ hm]
  rw [hηm, eigenvalues_neg hT hnE i0, eigenvalues_neg hT hnE i1, eigenvalues_neg hT hnE il,
    hrev0, hrev1, hrevl, hcw, tanAngle_smul _ hc0] at hkps
  have hmin : IsMin (⟨0, hm0⟩ : Fin m) := fun j _ => Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  simp only [Finset.Iio_eq_empty.mpr hmin, Finset.prod_empty, one_mul, Set.mem_Icc,
    div_pow] at hkps
  have harg : (1 : ℝ) + 2 * ((-hT.eigenvalues hnE il - -hT.eigenvalues hnE il1) /
      (-hT.eigenvalues hnE il1 - -hT.eigenvalues hnE i0))
      = 1 + 2 * ((hT.eigenvalues hnE il1 - hT.eigenvalues hnE il) /
        (hT.eigenvalues hnE i0 - hT.eigenvalues hnE il1)) := by ring
  rw [harg] at hkps
  have hcos : Real.cos φₙ = |inner ℝ q₁ (hT.eigenvectorBasis hnE il)| := by
    rw [Submodule.cos_angle, Submodule.cosAngle_span_singleton (by simp [← norm_pos_iff, hq₁]),
      hq₁, (hT.eigenvectorBasis hnE).norm_eq_one, mul_one, div_one, Real.norm_eq_abs]
  have htan : Real.tan φₙ = (ℝ ∙ q₁).tanAngle (hT.eigenvectorBasis hnE il) :=
    Submodule.tan_angle _ (hT.eigenvectorBasis_ne_zero hnE il)
  refine ⟨hcos, by linarith [hkps.1], ?_⟩
  simp only [lam, ρₙ]
  rw [htan, mul_div_assoc]
  linarith [hkps.2]

end QuarteroniSaccoSaleri.Chapter05
