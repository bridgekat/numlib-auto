import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos

/-!
# Krylov methods on singular and incompatible symmetric systems

The behaviour of the minimal-residual iteration when `A` is symmetric but singular, and when `A x =
b` has no solution at all, following [choi2006iterative] Ch. 2–3.

* **Termination.** The full Krylov space of `b` misses the range of `A` only in the direction of `b`
  itself (`Krylov.fullSubspace_le_span_sup_range`), so the grade is at most `rank A + 1`, and at
  most `rank A` when `b ∈ range A` (`Krylov.grade_le_finrank_range_add_one`,
  `Krylov.grade_le_finrank_range`).  Counting distinct eigenvalues instead of dimensions, a vector
  lying in the span of the eigenspaces of `t` scalars has grade at most `t`
  (`Krylov.grade_le_card_of_mem_iSup_eigenspace`); for symmetric `A` in finite dimension the
  eigenspaces span, which turns this into a bound by the number of *nonzero* eigenvalues
  (`Lanczos.grade_le_card_eigenvalues`, `Lanczos.grade_le_card_eigenvalues_of_mem_range`).
* **Compatible singular systems.** For `b ∈ range A` the minimal-residual iterate from `x₀ = 0` at
  `m ≥ grade` solves `A x = b` and is the minimum-norm solution, that is `A⁺ b`
  (`Krylov.IsMinResIterate.isLeast_norm_of_grade_le`).
* **Incompatible systems.** At `m ≥ grade` the residual of *any* minimal-residual iterate is
  annihilated by `A`, hence orthogonal to `range A`
  (`Krylov.IsMinResIterate.residual_mem_orthogonal_range_of_grade_le`), so the iterate already
  solves the least-squares problem over the whole space.  The minimum-norm minimal-residual iterate
  — the MINRES-QLP specification — is in addition orthogonal to `ker A`, so it is the minimum-norm
  least-squares solution `A⁺ b` (`Krylov.IsMinNormMinResIterate.isLeast_norm_of_grade_le`).  Every
  minimal-residual iterate is `X b` for a `{2,3}`-inverse `X` of `A`
  (`Krylov.IsMinResIterate.exists_generalizedInverse`).
* **Residual norms and the tridiagonal matrix.** The Lanczos reading of the Givens layer of
  `Numlib/Krylov/Hessenberg`: `‖r_m‖ = ‖r₀‖ ∏_{k<m} |s_k|`
  (`Krylov.IsMinResIterate.norm_residual_eq_prod_givensS`), and every bound on `A` is inherited by
  the tridiagonal matrices `T̄_m` and `T_m` (`Lanczos.norm_toEuclideanLin_tridiagExt_le`,
  `Lanczos.norm_toEuclideanLin_tridiag_le`).
* **The residual recurrence.** `Lanczos.residual_minRes_succ_eq` is [choi2006iterative] Lemma 2.18,
  `r_{m+1} = |s_m|² r_m - (s_m g_m) v_{m+1}`, the *vector* refinement of the norm identity above.
  It reads both residuals off the last row of the accumulated rotation
  (`Krylov.IsMinResIterate.residual_eq_gamma_smul_sum`) and steps that row with
  `Krylov.givensQ_last_row_castSucc`; nothing in it is symmetry-specific.

Everything about the specification level (`Krylov.IsMinResIterate`, `Krylov.IsMinNormMinResIterate`
of `Numlib/Krylov/Iterate`) needs only symmetry of `A` and finite grade; the eigenvalue counts and
the `T̄_m` bounds are where finite dimension enters.
-/

open Polynomial Krylov

namespace Krylov

/-! ### Termination of the Krylov sequence -/

section Grade

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `A (Aⁱ v) = Aⁱ⁺¹ v`, in the form the Krylov generating set needs. -/
private theorem apply_pow_apply (A : Module.End K V) (v : V) (i : ℕ) :
    A ((A ^ i) v) = (A ^ (i + 1)) v := by rw [pow_succ']; rfl

/-- The full Krylov space of `v` lies in `K ∙ v ⊔ range A`: only the zeroth power `A⁰ v = v` escapes
the range of `A`. -/
theorem fullSubspace_le_span_sup_range (A : Module.End K V) (v : V) :
    fullSubspace A v ≤ (K ∙ v) ⊔ LinearMap.range A := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  cases i with
  | zero => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  | succ i => exact Submodule.mem_sup_right ⟨(A ^ i) v, apply_pow_apply A v i⟩

/-- A starting vector in the range of `A` keeps the whole Krylov sequence there. -/
theorem fullSubspace_le_range (A : Module.End K V) {v : V} (hv : v ∈ LinearMap.range A) :
    fullSubspace A v ≤ LinearMap.range A := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  cases i with
  | zero => exact hv
  | succ i => exact ⟨(A ^ i) v, apply_pow_apply A v i⟩

/-- [choi2006iterative], Proposition 2.2 and Corollary 2.3, compatible case: a Krylov method started
at a right-hand side in the range of `A` terminates within `rank A` steps. -/
theorem grade_le_finrank_range [FiniteDimensional K V] (A : Module.End K V) {v : V}
    (hv : v ∈ LinearMap.range A) : grade A v ≤ Module.finrank K (LinearMap.range A) :=
  Submodule.finrank_mono (fullSubspace_le_range A hv)

/-- [choi2006iterative], Corollary 2.3: the Krylov sequence of any starting vector terminates within
`rank A + 1` steps, one more than the compatible bound of `Krylov.grade_le_finrank_range` because
the starting vector itself need not lie in the range. -/
theorem grade_le_finrank_range_add_one [FiniteDimensional K V] (A : Module.End K V) (v : V) :
    grade A v ≤ Module.finrank K (LinearMap.range A) + 1 := by
  have h1 : grade A v ≤ Module.finrank K ((K ∙ v) ⊔ LinearMap.range A : Submodule K V) :=
    Submodule.finrank_mono (fullSubspace_le_span_sup_range A v)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (K ∙ v) (LinearMap.range A)
  have h3 : Module.finrank K (K ∙ v : Submodule K V) ≤ 1 := by
    rcases eq_or_ne v 0 with rfl | hv
    · rw [Submodule.span_zero_singleton K, finrank_bot]
      omega
    · exact le_of_eq (finrank_span_singleton hv)
  omega

/-- If `v` lies in the span of the eigenspaces of the `S.card` scalars of `S`, then the monic
polynomial `∏_{μ ∈ S} (X - μ)` annihilates `v`, so the Krylov sequence of `v` terminates within
`S.card` steps.  This is the algebraic core of [choi2006iterative], Theorem 2.4; the symmetry of `A`
enters only through the spectral decomposition that puts `v` in such a span. -/
theorem grade_le_card_of_mem_iSup_eigenspace {A : Module.End K V} {v : V}
    [FiniteDimensional K (fullSubspace A v)] {S : Finset K}
    (hv : v ∈ ⨆ μ ∈ S, Module.End.eigenspace A μ) : grade A v ≤ S.card := by
  have hmonic : (∏ μ ∈ S, (X - C μ) : K[X]).Monic :=
    monic_prod_of_monic _ _ fun μ _ => monic_X_sub_C μ
  have hdeg : (∏ μ ∈ S, (X - C μ) : K[X]).natDegree = S.card := by
    rw [natDegree_prod _ _ fun μ _ => X_sub_C_ne_zero μ]
    simp
  have hker : (⨆ μ ∈ S, Module.End.eigenspace A μ) ≤
      LinearMap.ker (aeval A (∏ μ ∈ S, (X - C μ))) := by
    refine iSup_le fun μ => iSup_le fun hμ z hz => ?_
    obtain ⟨q, hq⟩ : (X - C μ) ∣ (∏ μ ∈ S, (X - C μ) : K[X]) := Finset.dvd_prod_of_mem _ hμ
    have hq' : (∏ μ ∈ S, (X - C μ) : K[X]) = q * (X - C μ) := by rw [hq]; ring
    have hz0 : aeval A (X - C μ) z = 0 := by
      have hev : A z = μ • z := Module.End.mem_eigenspace_iff.1 hz
      simp [hev]
    rw [LinearMap.mem_ker, hq', map_mul, Module.End.mul_apply, hz0, map_zero]
  refine (grade_le_iff A v).2 ((pow_apply_mem_subspace_iff_exists_monic A v _).2
    ⟨∏ μ ∈ S, (X - C μ), hmonic, hdeg, ?_⟩)
  exact LinearMap.mem_ker.1 (hker hv)

end Grade

/-! ### The minimal-residual iterate at termination

The specifications of `Numlib/Krylov/Iterate` are stated over `x₀ + 𝒦_m(A, b - A x₀)`;
[choi2006iterative] minimum-norm results are about the start `x₀ = 0`, where the search space is
`𝒦_m(A, b)` itself. The three lemmas below only remove the `b - A 0` that the general form leaves
behind. -/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x : E} {m : ℕ}

private theorem finiteDimensional_sub_apply_zero (A : E →ₗ[𝕜] E) (b : E)
    [FiniteDimensional 𝕜 (fullSubspace A b)] : FiniteDimensional 𝕜 (fullSubspace A (b - A 0)) := by
  rw [map_zero, sub_zero]
  infer_instance

private theorem isMinRes_of_isMinResIterate_zero (hx : IsMinResIterate A b 0 m x) :
    IsMinRes A b 0 (subspace A b m) x := by
  have h : IsMinRes A b 0 (subspace A (b - A 0) m) x := hx
  rwa [map_zero, sub_zero] at h

private theorem isMinResIterate_zero_iff_sub_mem (hx : IsMinResIterate A b 0 m x) {y : E} :
    IsMinResIterate A b 0 m y ↔ y - x ∈ subspace A b m ⊓ LinearMap.ker A := by
  have h := isMinResIterate_iff_sub_mem (A := A) (b := b) (x₀ := 0) (m := m) (x := y) hx
  rwa [map_zero, sub_zero] at h

/-- The `≤` form of `LinearMap.IsSymmetric.orthogonal_range`: for symmetric `A` the range is
orthogonal to the kernel. -/
private theorem range_le_orthogonal_ker (hA : A.IsSymmetric) :
    LinearMap.range A ≤ (LinearMap.ker A)ᗮ := by
  rw [← hA.orthogonal_range]
  exact Submodule.le_orthogonal_orthogonal _

/-- For symmetric `A` and a compatible right-hand side, `A` is injective on every Krylov subspace of
`b`: those subspaces avoid `ker A` because they lie in `(ker A)ᗮ`. -/
theorem injOn_subspace_of_mem_range (hA : A.IsSymmetric) (hb : b ∈ LinearMap.range A) (m : ℕ) :
    Set.InjOn A (subspace A b m : Set E) := by
  intro z hz w hw hzw
  have hker : z - w ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, map_sub, hzw, sub_self]
  have horth : z - w ∈ (LinearMap.ker A)ᗮ :=
    subspace_le_orthogonal_ker hA hb m (Submodule.sub_mem _ hz hw)
  exact sub_eq_zero.1 ((inner_self_eq_zero (𝕜 := 𝕜)).1
    (Submodule.inner_right_of_mem_orthogonal hker horth))

namespace IsMinResIterate

/-- [choi2006iterative], Theorem 2.25, exactness half: a compatible singular system is solved
exactly at termination. Symmetry supplies the injectivity of `A` on `𝒦_grade` that
`Krylov.IsMinResIterate.apply_eq_of_grade_le` asks for, because `b ∈ range A` puts the whole Krylov
space in `(ker A)ᗮ`. -/
theorem apply_eq_of_mem_range_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hb : b ∈ LinearMap.range A) (hm : grade A b ≤ m)
    (hx : IsMinResIterate A b 0 m x) : A x = b := by
  have := finiteDimensional_sub_apply_zero A b
  refine hx.apply_eq_of_grade_le ?_ ?_
  · rw [map_zero, sub_zero]
    exact hm
  · rw [map_zero, sub_zero]
    exact injOn_subspace_of_mem_range hA hb _

/-- **[choi2006iterative], Theorem 2.25.** On a compatible system with symmetric `A`, the
minimal-residual iterate from `x₀ = 0` at `m ≥ grade` is the minimum-norm solution of `A x = b`,
that is, the pseudoinverse solution `A⁺ b`.  Exactness is
`Krylov.IsMinResIterate.apply_eq_of_mem_range_of_grade_le` and minimality is
`Krylov.norm_le_of_apply_eq`, which only needs `𝒦_m(A, b) ≤ (ker A)ᗮ`. -/
theorem isLeast_norm_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hb : b ∈ LinearMap.range A) (hm : grade A b ≤ m) (hx : IsMinResIterate A b 0 m x) :
    IsLeast (norm '' {y : E | A y = b}) ‖x‖ := by
  have hAx : A x = b := apply_eq_of_mem_range_of_grade_le hA hb hm hx
  have hxm : x ∈ subspace A b m := by
    simpa using (isMinRes_of_isMinResIterate_zero hx).mem
  refine ⟨⟨x, hAx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact norm_le_of_apply_eq hA hxm hAx y hy

/-- At termination the minimal-residual residual is annihilated by `A`.  The Krylov space `𝒦_m =
𝒦_grade` is `A`-invariant and contains both `b` and `x`, so it contains the residual; symmetry turns
the Petrov–Galerkin condition `r ⟂ A 𝒦_m` into `A r ⟂ 𝒦_m`, and a vector of `𝒦_m ⊓ 𝒦_mᗮ` vanishes.
-/
theorem apply_residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinResIterate A b 0 m x) :
    A (b - A x) = 0 := by
  have hx' := isMinRes_of_isMinResIterate_zero hx
  have hKg : subspace A b m = fullSubspace A b := by
    rw [subspace_eq_of_grade_le A b hm, subspace_grade_eq_fullSubspace]
  have hinvt : ∀ z ∈ subspace A b m, A z ∈ subspace A b m := by
    rw [hKg]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1
      (fullSubspace_mem_invtSubmodule A b)
  have hxm : x ∈ subspace A b m := by simpa using hx'.mem
  have hbm : b ∈ subspace A b m := by
    rw [hKg]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hres : b - A x ∈ subspace A b m := Submodule.sub_mem _ hbm (hinvt x hxm)
  have horth : b - A x ∈ ((subspace A b m).map A)ᗮ := by
    have h := hx.residual_mem_orthogonal
    rwa [map_zero, sub_zero] at h
  have hAr : A (b - A x) ∈ (subspace A b m)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    rw [← hA w (b - A x)]
    exact (Submodule.mem_orthogonal _ _).1 horth (A w) (Submodule.mem_map_of_mem hw)
  exact (inner_self_eq_zero (𝕜 := 𝕜)).1
    (Submodule.inner_right_of_mem_orthogonal (hinvt _ hres) hAr)

/-- At termination the residual is orthogonal to `range A`: the normal equations of the
least-squares problem `min ‖b - A y‖` hold, whether or not the system is compatible. -/
theorem residual_mem_orthogonal_range_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinResIterate A b 0 m x) :
    b - A x ∈ (LinearMap.range A)ᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 ?_
  rintro _ ⟨u, rfl⟩
  rw [hA u (b - A x), apply_residual_eq_zero_of_grade_le hA hm hx, inner_zero_right]

/-- At termination the minimal-residual iterate minimizes the residual over the **whole** space, not
merely over `𝒦_m`: the Krylov space has grown large enough to contain the least-squares solution.
This is the first half of [choi2006iterative], Theorem 3.1. -/
theorem norm_residual_le_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hm : grade A b ≤ m) (hx : IsMinResIterate A b 0 m x) (y : E) : ‖b - A x‖ ≤ ‖b - A y‖ := by
  have h0 : inner 𝕜 (b - A x) (A x - A y) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1
      (residual_mem_orthogonal_range_of_grade_le hA hm hx) _ ⟨x - y, by rw [map_sub]⟩
  have hsplit : b - A y = (b - A x) + (A x - A y) := by abel
  have hsq : ‖b - A y‖ * ‖b - A y‖ = ‖b - A x‖ * ‖b - A x‖ + ‖A x - A y‖ * ‖A x - A y‖ := by
    rw [hsplit, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
  nlinarith [norm_nonneg (b - A x), norm_nonneg (b - A y), norm_nonneg (A x - A y)]

/-- **[choi2006iterative], Theorem 2.27**, `{2,3}` half: every minimal-residual iterate is `X b` for
a `{2,3}`-inverse `X` of `A`, that is, for an `X` with `X A X = X` and `A X` self-adjoint.

The witness is the rank-one map `z ↦ ⟪A x, z⟫ / ⟪A x, A x⟫ • x`, for which `A X` is the orthogonal
projection onto `𝕜 ∙ A x`; the only input is the Petrov–Galerkin condition `⟪A x, b - A x⟫ = 0`,
which every minimal-residual iterate satisfies.  So no termination hypothesis is needed, and — this
being the flip side — the statement is weak: what carries the content of [choi2006iterative] theorem
is the *particular* `X` read off the QLP factorization, and the strengthening to a `{1,2,3}`-inverse
(`A X A = A`) when `𝒦_m` contains `range A`, neither of which is formalized here.  The hypothesis `A
x ≠ 0` cannot be dropped: for `A = 0` the only `{2,3}`-inverse is `0`, so no nonzero `x` is of the
form `X b`. -/
theorem exists_generalizedInverse (hx : IsMinResIterate A b 0 m x) (hAx : A x ≠ 0) :
    ∃ X : E →ₗ[𝕜] E, X ∘ₗ A ∘ₗ X = X ∧ (A ∘ₗ X).IsSymmetric ∧ X b = x := by
  have hne : inner 𝕜 (A x) (A x) ≠ (0 : 𝕜) := fun h => hAx (inner_self_eq_zero.1 h)
  obtain ⟨c, hcinv, hcconj⟩ :
      ∃ c : 𝕜, c * inner 𝕜 (A x) (A x) = 1 ∧ starRingEnd 𝕜 c = c :=
    ⟨(inner 𝕜 (A x) (A x))⁻¹, inv_mul_cancel₀ hne, by rw [map_inv₀, inner_self_conj]⟩
  have hAxb : inner 𝕜 (A x) b = inner 𝕜 (A x) (A x) := by
    have hxm : x ∈ subspace A (b - A 0) m := by simpa using hx.mem
    have h0 : inner 𝕜 (A x) (b - A x) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal _ _).1 hx.residual_mem_orthogonal (A x)
        (Submodule.mem_map_of_mem hxm)
    have hb : b = A x + (b - A x) := by abel
    rw [hb, inner_add_right, h0, add_zero]
  obtain ⟨X, hX⟩ : ∃ X : E →ₗ[𝕜] E, ∀ z, X z = (c * inner 𝕜 (A x) z) • x :=
    ⟨c • (LinearMap.toSpanSingleton 𝕜 E x ∘ₗ (innerSL 𝕜 (A x)).toLinearMap), fun z => by
      simp [LinearMap.toSpanSingleton_apply, smul_smul]⟩
  refine ⟨X, LinearMap.ext fun z => ?_, fun u v => ?_, ?_⟩
  · have hkey : c * ((c * inner 𝕜 (A x) z) * inner 𝕜 (A x) (A x))
        = c * inner 𝕜 (A x) z := by
      linear_combination (c * inner 𝕜 (A x) z) * hcinv
    simp only [LinearMap.comp_apply, hX, map_smul, inner_smul_right, hkey]
  · simp only [LinearMap.comp_apply, hX, map_smul, inner_smul_left, inner_smul_right, map_mul,
      hcconj, inner_conj_symm]
    ring
  · rw [hX, hAxb, hcinv, one_smul]

/-- [choi2006iterative], (2.21): the minimal-residual norm after `m` steps is `‖r₀‖` times the
moduli of the Givens sines.  For symmetric `A` the coefficient function `Arnoldi.coeff A r₀` is the
tridiagonal `T̄` (`Lanczos.hessenberg_eq_map_tridiagExt`), so these are the sines of
[choi2006iterative] Lanczos rotations; the identity itself needs no symmetry. -/
theorem norm_residual_eq_prod_givensS {x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m < grade A (b - A x₀)) (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ =
      (∏ k ∈ Finset.range m, ‖givensS (Arnoldi.coeff A (b - A x₀)) k‖) * ‖b - A x₀‖ := by
  rw [hx.norm_residual_eq_norm_gamma hm, norm_gamma_eq_prod]
  simp

end IsMinResIterate

namespace IsMinNormMinResIterate

/-- The minimum-norm minimal-residual iterate is orthogonal to `𝒦_m ⊓ ker A`, the subspace along
which the minimal-residual iterates vary (`Krylov.isMinResIterate_iff_sub_mem`). -/
theorem inner_eq_zero_of_mem (hx : IsMinNormMinResIterate A b 0 m x) {z : E}
    (hz : z ∈ subspace A b m ⊓ LinearMap.ker A) : inner 𝕜 x z = (0 : 𝕜) := by
  have hmin : ∀ w ∈ subspace A b m ⊓ LinearMap.ker A, ‖x - (0 : E)‖ ≤ ‖x - w‖ := by
    intro w hw
    rw [sub_zero]
    refine hx.norm_le _ ((isMinResIterate_zero_iff_sub_mem hx.isMinResIterate).2 ?_)
    rw [sub_sub_cancel_left]
    exact Submodule.neg_mem _ hw
  have h := Submodule.inner_eq_zero_of_forall_norm_sub_le
    (Submodule.zero_mem (subspace A b m ⊓ LinearMap.ker A)) hmin hz
  rwa [sub_zero] at h

/-- At termination the minimum-norm minimal-residual iterate is orthogonal to `ker A`.  The Krylov
space sits in `𝕜 ∙ r ⊔ (ker A)ᗮ` with `r = b - A x` the residual, which at termination lies in `ker
A` (`Krylov.IsMinResIterate.apply_residual_eq_zero_of_grade_le`) and in `𝒦_m`; the minimum-norm
condition kills the `r`-component. -/
theorem mem_orthogonal_ker_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinNormMinResIterate A b 0 m x) :
    x ∈ (LinearMap.ker A)ᗮ := by
  have hx' := hx.isMinResIterate
  have hKg : subspace A b m = fullSubspace A b := by
    rw [subspace_eq_of_grade_le A b hm, subspace_grade_eq_fullSubspace]
  have hker : b - A x ∈ LinearMap.ker A :=
    LinearMap.mem_ker.2 (IsMinResIterate.apply_residual_eq_zero_of_grade_le hA hm hx')
  have hxm : x ∈ subspace A b m := by
    simpa using (isMinRes_of_isMinResIterate_zero hx').mem
  have hinvt : ∀ z ∈ subspace A b m, A z ∈ subspace A b m := by
    rw [hKg]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1
      (fullSubspace_mem_invtSubmodule A b)
  have hbm : b ∈ subspace A b m := by
    rw [hKg]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hresm : b - A x ∈ subspace A b m := Submodule.sub_mem _ hbm (hinvt x hxm)
  have hxr : inner 𝕜 x (b - A x) = (0 : 𝕜) := inner_eq_zero_of_mem hx ⟨hresm, hker⟩
  -- the Krylov space is spanned by the residual together with `(ker A)ᗮ`
  have hle : subspace A b m ≤ (𝕜 ∙ (b - A x)) ⊔ (LinearMap.ker A)ᗮ := by
    rw [hKg]
    refine le_trans (fullSubspace_le_span_sup_range A b) (sup_le ?_ ?_)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_sup.2 ⟨b - A x, Submodule.mem_span_singleton_self _, A x,
        range_le_orthogonal_ker hA ⟨x, rfl⟩, by abel⟩
    · exact le_trans (range_le_orthogonal_ker hA) le_sup_right
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle hxm)
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hp
  have hnq : inner 𝕜 (b - A x) q = (0 : 𝕜) :=
    Submodule.inner_right_of_mem_orthogonal hker hq
  have hα : α * inner 𝕜 (b - A x) (b - A x) = 0 := by
    have h := congrArg (fun w => inner 𝕜 (b - A x) w) hpq
    simp only [inner_add_right, inner_smul_right, hnq, add_zero] at h
    rw [h, ← inner_conj_symm, hxr, map_zero]
  have hαzero : α • (b - A x) = 0 := by
    rcases eq_or_ne α 0 with rfl | hα0
    · rw [zero_smul]
    · rw [inner_self_eq_zero.1 ((mul_eq_zero.1 hα).resolve_left hα0), smul_zero]
  rw [← hpq, hαzero, zero_add]
  exact hq

/-- **[choi2006iterative], Theorem 3.1.** For symmetric `A` and `m ≥ grade`, the minimum-norm
minimal-residual iterate from `x₀ = 0` — the MINRES-QLP specification — is the minimum-norm
least-squares solution `A⁺ b`: it minimizes `‖b - A y‖` over the whole space, and has least norm
among the minimizers.  No compatibility of the system and no injectivity of `A` is assumed; that is
exactly what the minimum-norm clause of `Krylov.IsMinNormMinResIterate` buys over
`Krylov.IsMinResIterate.isLeast_norm_of_grade_le`. -/
theorem isLeast_norm_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hm : grade A b ≤ m) (hx : IsMinNormMinResIterate A b 0 m x) :
    IsLeast (norm '' {y : E | ∀ z : E, ‖b - A y‖ ≤ ‖b - A z‖}) ‖x‖ := by
  have hx' := hx.isMinResIterate
  have hlsq : ∀ z : E, ‖b - A x‖ ≤ ‖b - A z‖ :=
    IsMinResIterate.norm_residual_le_of_grade_le hA hm hx'
  refine ⟨⟨x, hlsq, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h0 : inner 𝕜 (b - A x) (A x - A y) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1
      (IsMinResIterate.residual_mem_orthogonal_range_of_grade_le hA hm hx') _
      ⟨x - y, by rw [map_sub]⟩
  have hsplit : b - A y = (b - A x) + (A x - A y) := by abel
  have hsq : ‖b - A y‖ * ‖b - A y‖ = ‖b - A x‖ * ‖b - A x‖ + ‖A x - A y‖ * ‖A x - A y‖ := by
    rw [hsplit, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
  have hAeq : A y = A x := by
    have h1 : ‖b - A y‖ = ‖b - A x‖ := le_antisymm (hy x) (hlsq y)
    rw [h1] at hsq
    have hz2 : ‖A x - A y‖ * ‖A x - A y‖ = 0 := by linarith
    exact (sub_eq_zero.1 (norm_eq_zero.1 (mul_self_eq_zero.1 hz2))).symm
  have hyx : y - x ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, map_sub, hAeq, sub_self]
  have hxk : inner 𝕜 x (y - x) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1 (mem_orthogonal_ker_of_grade_le hA hm hx) _ hyx
  have hsq' : ‖y‖ * ‖y‖ = ‖x‖ * ‖x‖ + ‖y - x‖ * ‖y - x‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x (y - x) hxk
    rwa [show x + (y - x) = y from by abel] at h
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (y - x)]

end IsMinNormMinResIterate

end Krylov

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Termination against the number of distinct eigenvalues -/

section Eigenvalues

variable {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]

private theorem iSup_eigenspace_eq_top (hA : A.IsSymmetric) :
    (⨆ μ : 𝕜, Module.End.eigenspace A μ) = ⊤ :=
  Submodule.orthogonal_eq_bot_iff.1
    (LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot hA)

private theorem le_iSup_eigenspace_of_forall (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, Module.End.eigenspace A μ ≠ ⊥ → μ ∈ S) :
    (⊤ : Submodule 𝕜 E) ≤ ⨆ μ ∈ S, Module.End.eigenspace A μ := by
  rw [← iSup_eigenspace_eq_top hA]
  refine iSup_le fun μ => ?_
  rcases eq_or_ne (Module.End.eigenspace A μ) ⊥ with h0 | h0
  · rw [h0]
    exact bot_le
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ S) => Module.End.eigenspace A μ) μ (hS μ h0)

/-- For symmetric `A` the range is spanned by the eigenspaces of the nonzero eigenvalues. -/
private theorem range_le_iSup_eigenspace (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.eigenspace A μ ≠ ⊥ → μ ∈ S) :
    LinearMap.range A ≤ ⨆ μ ∈ S, Module.End.eigenspace A μ := by
  rw [LinearMap.range_eq_map, ← iSup_eigenspace_eq_top hA, Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [Module.End.eigenspace_zero]
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearMap.mem_ker.1 hz]
    exact Submodule.zero_mem _
  · rcases eq_or_ne (Module.End.eigenspace A μ) ⊥ with h0 | h0
    · rw [h0, Submodule.map_bot]
      exact bot_le
    · refine le_trans ?_
        (le_iSup₂ (f := fun μ (_ : μ ∈ S) => Module.End.eigenspace A μ) μ (hS μ hμ h0))
      rintro _ ⟨z, hz, rfl⟩
      have hev : A z = μ • z := Module.End.mem_eigenspace_iff.1 hz
      rw [Module.End.mem_eigenspace_iff, hev, map_smul, hev]

/-- [choi2006iterative], Theorem 2.4, compatible case: if `b` lies in the range of the symmetric `A`
and `S` collects the nonzero eigenvalues of `A`, then the Lanczos process on `b` terminates within
`S.card` steps.

[choi2006iterative] counts only the eigenvalues along which `b` has a nonzero component; that
sharper form is `Krylov.grade_le_card_of_mem_iSup_eigenspace` applied to the smaller `S`, of which
this is the corollary that needs no knowledge of the components. -/
theorem grade_le_card_eigenvalues_of_mem_range (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.HasEigenvalue A μ → μ ∈ S) {b : E}
    (hb : b ∈ LinearMap.range A) : grade A b ≤ S.card :=
  grade_le_card_of_mem_iSup_eigenspace (range_le_iSup_eigenspace hA hS hb)

/-- **[choi2006iterative], Theorem 2.4.** If `S` collects the nonzero eigenvalues of the symmetric
`A`, then the Lanczos process on any `b` terminates within `S.card + 1` steps — one more than the
compatible bound of `Lanczos.grade_le_card_eigenvalues_of_mem_range`, the extra step paying for the
component of `b` in `ker A`.  As there, [choi2006iterative] sharper count over the eigenvalues along
which `b` actually has a component is `Krylov.grade_le_card_of_mem_iSup_eigenspace`. -/
theorem grade_le_card_eigenvalues (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.HasEigenvalue A μ → μ ∈ S) (b : E) :
    grade A b ≤ S.card + 1 := by
  have hins : ∀ μ : 𝕜, Module.End.eigenspace A μ ≠ ⊥ → μ ∈ insert (0 : 𝕜) S := by
    intro μ hμ
    rcases eq_or_ne μ 0 with rfl | h0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hS μ h0 hμ)
  exact le_trans
    (grade_le_card_of_mem_iSup_eigenspace
      (le_iSup_eigenspace_of_forall hA hins Submodule.mem_top))
    (Finset.card_insert_le _ _)

end Eigenvalues

/-! ### Bounds on the tridiagonal matrices -/

section Tridiag

variable {A : E →ₗ[𝕜] E} {b : E} [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Pythagoras in the Arnoldi basis: below the grade the Arnoldi vectors are orthonormal, so the
norm of a combination is the Euclidean norm of its coefficient vector. -/
private theorem norm_sum_smul_vec {N : ℕ} (hN : N ≤ grade A b) (c : Fin N → 𝕜) :
    ‖∑ i, c i • Arnoldi.vec A b (i : ℕ)‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))‖ := by
  have hinner : ∀ j : Fin N,
      inner 𝕜 (Arnoldi.vec A b (j : ℕ)) (∑ i, c i • Arnoldi.vec A b (i : ℕ)) = c j := by
    intro j
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
        Arnoldi.norm_vec_eq_one_of_lt_grade A b (lt_of_lt_of_le j.isLt hN)]
      norm_num
    · intro i _ hij
      rw [inner_smul_right, Arnoldi.inner_vec_eq_zero A b (fun hc => hij (Fin.ext hc.symm)),
        mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have hK : ((‖∑ i, c i • Arnoldi.vec A b (i : ℕ)‖ : ℝ) : 𝕜) ^ 2 = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, sum_inner]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      rw [inner_smul_left, hinner i, RCLike.conj_mul]
  have hsq : ‖∑ i, c i • Arnoldi.vec A b (i : ℕ)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast hK
  have hrhs : ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [← Real.sqrt_sq (norm_nonneg (∑ i, c i • Arnoldi.vec A b (i : ℕ))),
    ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))), hsq, hrhs]

/-- [choi2006iterative], Lemma 2.31, `‖T̄_m‖ ≤ ‖A‖`, in the form that needs no norm on the space of
operators: every bound `C` for `A` is a bound for the extended tridiagonal matrix `T̄_m`.  The
reason is `A V_m = V_{m+1} T̄_m` with `V_{m+1}` an isometry on coordinates, which holds up to the
grade. -/
theorem norm_toEuclideanLin_tridiagExt_le (hA : A.IsSymmetric) {C : ℝ}
    (hC : ∀ z : E, ‖A z‖ ≤ C * ‖z‖) {m : ℕ} (hm : m + 1 ≤ grade A b)
    (y : EuclideanSpace 𝕜 (Fin m)) :
    ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ ≤ C * ‖y‖ := by
  have hAsum : A (∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ)) =
      ∑ i : Fin (m + 1),
        ((tridiagExt A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i •
          Arnoldi.vec A b (i : ℕ) := by
    rw [Arnoldi.apply_sum A b m (WithLp.ofLp y), hessenberg_eq_map_tridiagExt b hA m]
  have hlhs : ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖
      = ‖A (∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ))‖ := by
    rw [hAsum, norm_sum_smul_vec hm, Matrix.toLpLin_apply]
  have hrhs : ‖∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ)‖ = ‖y‖ := by
    rw [norm_sum_smul_vec (by omega)]
  rw [hlhs, ← hrhs]
  exact hC _

/-- [choi2006iterative], Lemma 2.31, `‖T_m‖ ≤ ‖T̄_m‖ ≤ ‖A‖`: the square Lanczos matrix is the
leading block of the extended one, so it inherits every bound on `A`. -/
theorem norm_toEuclideanLin_tridiag_le (hA : A.IsSymmetric) {C : ℝ}
    (hC : ∀ z : E, ‖A z‖ ≤ C * ‖z‖) {m : ℕ} (hm : m + 1 ≤ grade A b)
    (y : EuclideanSpace 𝕜 (Fin m)) :
    ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ≤ C * ‖y‖ := by
  have hcast : ∀ i : Fin m,
      ((tridiag A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i =
        ((tridiagExt A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i.castSucc := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tridiagExt, tridiag, Matrix.of_apply,
      Fin.val_castSucc]
  have hsq : ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    have hterm : ∀ i : Fin m,
        ‖(Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i‖ ^ 2 =
          ‖(Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc‖ ^ 2 := by
      intro i
      have h : (Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i =
          (Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc := hcast i
      rw [h]
    have hsum : ∑ i : Fin m,
          ‖(Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i‖ ^ 2 =
        ∑ i : Fin m,
          ‖(Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hsum]
    exact le_add_of_nonneg_right (by positivity)
  have hle : ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ≤
      ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact hle.trans (norm_toEuclideanLin_tridiagExt_le hA hC hm y)

end Tridiag

/-! ### The residual recurrence of MINRES -/

section Residual

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- **[choi2006iterative], Lemma 2.18** (also [saad2003iterative], (6.55) for DQGMRES): the vector
recurrence between consecutive minimal-residual residuals,

`r_{m+1} = |s_m|² r_m - (s_m g_m) v_{m+1}`,

with `g_m = c̄_m γ_m` the `m`-th entry of the rotated right-hand side.  Choi's real form
`r_k = s_k² r_{k-1} - φ_k c_k v_{k+1}` is this with `γ_m = ±φ_m`.

Both residuals are read off the last row of the accumulated rotation
(`Krylov.IsMinResIterate.residual_eq_gamma_smul_sum`), and one step of that row is
`Krylov.givensQ_last_row_castSucc` and `Krylov.givensQ_last_row_last`; the `|s_m|²` is `s_m` from
`γ_{m+1} = -s_m γ_m` times `conj s_m` from the row.  Nothing here is symmetry-specific — the same
identity holds for GMRES — but this is where [choi2006iterative] uses it. -/
theorem residual_minRes_succ_eq {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀))
    (hρ : ∀ k < m + 1, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x x' : E}
    (hx : IsMinResIterate A b x₀ m x) (hx' : IsMinResIterate A b x₀ (m + 1) x') :
    b - A x' =
      ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) • (b - A x) -
        (givensS (Arnoldi.coeff A (b - A x₀)) m *
            gvec (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m) •
          Arnoldi.vec A (b - A x₀) (m + 1) := by
  have hr := hx.residual_eq_gamma_smul_sum (by omega) fun k hk => hρ k (by omega)
  have hr' := hx'.residual_eq_gamma_smul_sum hm hρ
  have h1 : ∀ j : Fin (m + 1),
      (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) (m + 1) *
          (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) (m + 1)
            (Fin.last (m + 1)) j.castSucc)) •
          Arnoldi.vec A (b - A x₀) ((j.castSucc : Fin (m + 2)) : ℕ)
        = ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) •
          ((gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m *
              (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) j)) •
            Arnoldi.vec A (b - A x₀) (j : ℕ)) := by
    intro j
    have hval : ((j.castSucc : Fin (m + 2)) : ℕ) = (j : ℕ) := rfl
    rw [hval, givensQ_last_row_castSucc, gamma_succ, map_mul, map_neg, smul_smul]
    congr 1
    have hc : givensS (Arnoldi.coeff A (b - A x₀)) m *
        (starRingEnd 𝕜) (givensS (Arnoldi.coeff A (b - A x₀)) m)
        = ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.mul_conj]
      push_cast
      ring
    linear_combination (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m *
      (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) j)) * hc
  have h2 : (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) (m + 1) *
        (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) (m + 1)
          (Fin.last (m + 1)) (Fin.last (m + 1)))) •
        Arnoldi.vec A (b - A x₀) ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)
      = -((givensS (Arnoldi.coeff A (b - A x₀)) m *
          gvec (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m) •
        Arnoldi.vec A (b - A x₀) (m + 1)) := by
    have hval : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = m + 1 := rfl
    rw [hval, givensQ_last_row_last, gamma_succ, gvec, ← neg_smul]
    congr 1
    ring
  rw [hr', Fin.sum_univ_castSucc, Finset.sum_congr rfl fun j _ => h1 j, ← Finset.smul_sum, ← hr,
    h2, ← sub_eq_add_neg]

end Residual

end Lanczos
