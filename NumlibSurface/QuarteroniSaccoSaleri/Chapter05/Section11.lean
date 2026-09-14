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
* `property_5_12` — the Kaniel–Paige bound for `η_1`.

## Not formalized

The display after Property 5.12, the mirror bound for `η_m` (`property_5_12_min`), stays open: it
is Property 5.12 for `−A`, and the backbone lacks the three facts that reduction needs (the Krylov
subspace and the compression are unchanged and negated under `A ↦ −A`, and the sorted eigenvalues
of `−T` are the reversed negatives of those of `T`). Example 5.18 is numerical; Program 45 is not a
node; the reorthogonalization remarks are prose.
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

end QuarteroniSaccoSaleri.Chapter05
