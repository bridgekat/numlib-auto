import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The least curvature `λ_min` of a bilinear form

For a continuous bilinear form `A : E [×2]→L[ℝ] ℝ` on a real normed space (typically a second
derivative `iteratedFDeriv ℝ 2 f x`), `minCurvature A = ⨅_{‖d‖ = 1} A[d, d]` is the least value of
the quadratic form on the unit sphere. On a finite-dimensional inner product space and for a
symmetric form it is the leftmost eigenvalue `λ_min` of the associated self-adjoint operator
([cartis2022evaluation], Section A.5), and the Rayleigh-quotient inequality (A.3) holds by
definition. Here `A[d, d]` is `A (fun _ => d)`.

`minCurvature A` is the book's `λ_min` (an eigenvalue, attained on the sphere) only on a nonzero
finite-dimensional space; in infinite dimension it is just the infimum of the quadratic form on
the unit sphere. On the zero space the sphere is empty and `minCurvature A = 0`; characterizations
that need a unit vector assume `[Nontrivial E]`.

## Main definitions

* `minCurvature A`: the infimum of `A[d, d]` over the unit sphere;
* `innerForm`: the bilinear form `(v, w) ↦ ⟪v, w⟫`, the "identity matrix".

## Main results

* `minCurvature_le_apply`, `minCurvature_mul_norm_sq_le`: the Rayleigh bound (A.3);
* `le_minCurvature_iff`: `c ≤ λ_min[A] ↔ ∀ d, c ‖d‖² ≤ A[d, d]` (so `-ε ≤ λ_min[A]` is the book's
  approximate second-order condition (3.2.6));
* `abs_minCurvature_le_norm`, `abs_minCurvature_sub_le`: (A.4) and (A.5);
* `minCurvature_add_smul_inner`: shifting by `λ I` shifts `λ_min` by `λ` ((3.4.33));
* `minCurvature_ge_of_add_smul`: `λ_min[A] ≥ λ_min[T + c N] - ‖A - T‖ - c K` when `N[d, d] ≤ K ‖d‖²`
  (the step bounds (4.1.27), (5.5.15));
* `exists_eq_minCurvature`, `apply_eq_minCurvature_mul_inner`, `exists_eigenvector_minCurvature`:
  in finite dimension `λ_min` is attained at a unit vector, which for a symmetric form is an
  eigenvector and may be chosen with `⟪u, g⟫ ≤ 0` for a given `g` ((3.2.3));
* for `A[v, w] = ⟪v, T w⟫` with `T` symmetric: `minCurvature_eq_iInf_eigenvalues`,
  `hasEigenvalue_minCurvature`, `minCurvature_le_of_hasEigenvalue` (`λ_min` is the least eigenvalue
  of `T`), `minCurvature_eq_iInf_rayleigh` (the least Rayleigh quotient `H.rayleighQuotient`), and
  `minCurvature_eq_iInf_isHermitian_eigenvalues` (the least eigenvalue of a symmetric matrix).
  The bridge to `Subproblem.leftmost` is in `Numlib.Optimization.Subproblem.MinCurvature`.
-/

open Metric Set
open scoped RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The least curvature `λ_min[A] = inf_{‖d‖ = 1} A[d, d]` of a continuous bilinear form
([cartis2022evaluation], Section A.5: the leftmost eigenvalue when `A` is a symmetric matrix).
It is `0` on the zero space. -/
noncomputable def minCurvature (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) : ℝ :=
  ⨅ d : sphere (0 : E) 1, A (fun _ => (d : E))

variable (A B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)

theorem minCurvature_def : minCurvature A = ⨅ d : sphere (0 : E) 1, A (fun _ => (d : E)) := rfl

/-- `|A[d, d]| ≤ ‖A‖ ‖d‖²`. -/
theorem abs_apply_diag_le (d : E) : |A (fun _ => d)| ≤ ‖A‖ * ‖d‖ ^ 2 := by
  simpa [Fin.prod_univ_two, sq] using A.le_opNorm (fun _ => d)

theorem bddBelow_apply_sphere :
    BddBelow (range fun d : sphere (0 : E) 1 => A (fun _ => (d : E))) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨d, rfl⟩
  have h := neg_abs_le (A (fun _ => (d : E)))
  have hd : ‖(d : E)‖ = 1 := by simp
  have := abs_apply_diag_le A d
  rw [hd] at this
  linarith

/-- The Rayleigh bound on the unit sphere ([cartis2022evaluation], (A.3)). -/
theorem minCurvature_le_apply {d : E} (hd : ‖d‖ = 1) : minCurvature A ≤ A (fun _ => d) :=
  ciInf_le (bddBelow_apply_sphere A) (⟨d, by simpa using hd⟩ : sphere (0 : E) 1)

/-- The homogeneous Rayleigh bound `λ_min[A] ‖d‖² ≤ A[d, d]` ([cartis2022evaluation], (A.3)). -/
theorem minCurvature_mul_norm_sq_le (d : E) : minCurvature A * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp [A.map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
  have hn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have h := minCurvature_le_apply A (d := ‖d‖⁻¹ • d) (by simp [norm_smul, hn.ne'])
  have hs : A (fun _ => ‖d‖⁻¹ • d) = (‖d‖⁻¹) ^ 2 * A (fun _ => d) := by
    simpa [Fin.prod_univ_two, sq] using A.map_smul_univ (fun _ => ‖d‖⁻¹) (fun _ => d)
  rw [hs] at h
  have h2 : 0 < ‖d‖ ^ 2 := by positivity
  calc minCurvature A * ‖d‖ ^ 2 ≤ (‖d‖⁻¹) ^ 2 * A (fun _ => d) * ‖d‖ ^ 2 := by gcongr
    _ = A (fun _ => d) := by field_simp

/-- On the zero space the unit sphere is empty and `λ_min[A] = 0`. -/
theorem minCurvature_of_subsingleton [Subsingleton E] : minCurvature A = 0 := by
  have : IsEmpty (sphere (0 : E) 1) := ⟨fun d => by
    have := d.2
    simp [Subsingleton.elim (d : E) 0] at this⟩
  rw [minCurvature_def, Real.iInf_of_isEmpty]

variable {A B}

/-- **Characterization of `λ_min`** ([cartis2022evaluation], (3.2.6)): on a nonzero space,
`c ≤ λ_min[A]` iff `c ‖d‖² ≤ A[d, d]` for all `d`. -/
theorem le_minCurvature_iff [Nontrivial E] {c : ℝ} :
    c ≤ minCurvature A ↔ ∀ d, c * ‖d‖ ^ 2 ≤ A (fun _ => d) := by
  constructor
  · intro hc d
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (minCurvature_mul_norm_sq_le A d)
  · intro h
    have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
    refine le_ciInf fun d => ?_
    have hd : ‖(d : E)‖ = 1 := by simp
    simpa [hd] using h d

/-- `λ_min[A] ≥ 0` iff `A` is positive semidefinite. -/
theorem minCurvature_nonneg_iff : 0 ≤ minCurvature A ↔ ∀ d, 0 ≤ A (fun _ => d) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [minCurvature_of_subsingleton, le_refl, true_iff]
    intro d
    rw [Subsingleton.elim d 0, A.map_coord_zero (m := fun _ => (0 : E)) 0 rfl]
  · simp [le_minCurvature_iff]

/-- On a nonzero space the infimum is attained along a minimizing sequence: for every `c >
λ_min[A]` there is a unit vector `d` with `A[d, d] < c`. -/
theorem exists_apply_lt_of_minCurvature_lt [Nontrivial E] {c : ℝ} (hc : minCurvature A < c) :
    ∃ d, ‖d‖ = 1 ∧ A (fun _ => d) < c := by
  have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨d, hd⟩ := exists_lt_of_ciInf_lt hc
  exact ⟨d, by simp, hd⟩

/-- (A.4) of [cartis2022evaluation]: `-‖A‖ ≤ λ_min[A] ≤ ‖A‖`. -/
theorem abs_minCurvature_le_norm : |minCurvature A| ≤ ‖A‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [minCurvature_of_subsingleton]
  rw [abs_le]
  constructor
  · refine le_minCurvature_iff.2 fun d => ?_
    have := neg_abs_le (A (fun _ => d))
    have := abs_apply_diag_le A d
    linarith
  · obtain ⟨d, hd⟩ := exists_norm_eq E zero_le_one
    have h1 := minCurvature_le_apply A hd
    have h2 := le_abs_self (A (fun _ => d))
    have h3 := abs_apply_diag_le A d
    rw [hd] at h3
    linarith

/-- (A.5) of [cartis2022evaluation]: `λ_min` is `1`-Lipschitz,
`|λ_min[A] - λ_min[B]| ≤ ‖A - B‖`. -/
theorem abs_minCurvature_sub_le : |minCurvature A - minCurvature B| ≤ ‖A - B‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [minCurvature_of_subsingleton]
  have key : ∀ A B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ,
      minCurvature B - ‖A - B‖ ≤ minCurvature A := by
    intro A B
    refine le_minCurvature_iff.2 fun d => ?_
    have h1 := minCurvature_mul_norm_sq_le B d
    have h2 := neg_abs_le ((A - B) (fun _ => d))
    have h3 := abs_apply_diag_le (A - B) d
    have h4 : (A - B) (fun _ => d) = A (fun _ => d) - B (fun _ => d) := rfl
    nlinarith
  rw [abs_sub_le_iff]
  have := key A B
  have := key B A
  rw [norm_sub_rev] at this
  constructor <;> linarith

variable (A)

/-- In finite dimension `λ_min[A]` is attained at a unit vector. -/
theorem exists_eq_minCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    ∃ u, ‖u‖ = 1 ∧ A (fun _ => u) = minCurvature A := by
  have := FiniteDimensional.proper_real E
  have hcont : Continuous fun d : E => A (fun _ => d) :=
    A.coe_continuous.comp (continuous_pi fun _ => continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hcont.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm ?_ (minCurvature_le_apply A hu1)⟩
  have : Nonempty (sphere (0 : E) 1) := ⟨⟨u, hu⟩⟩
  exact le_ciInf fun d => hmin d.2

/-! ### Bilinear-form calculus on `![v, w]` -/

/-- The diagonal tuple `fun _ => d` is `![d, d]`. -/
theorem apply_diag_eq_vec (d : E) : A (fun _ => d) = A ![d, d] := by
  congr 1
  funext i
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem update_vec_zero (x z v : E) : Function.update ![x, z] 0 v = ![v, z] := by
  ext i
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem update_vec_one (x z v : E) : Function.update ![z, x] 1 v = ![z, v] := by
  ext i
  fin_cases i <;> rfl

theorem apply_vec_add_left (x y z : E) : A ![x + y, z] = A ![x, z] + A ![y, z] := by
  simpa only [update_vec_zero] using A.map_update_add ![x, z] 0 x y

theorem apply_vec_smul_left (c : ℝ) (x z : E) : A ![c • x, z] = c * A ![x, z] := by
  simpa only [update_vec_zero, smul_eq_mul] using A.map_update_smul ![x, z] 0 c x

theorem apply_vec_add_right (x y z : E) : A ![z, x + y] = A ![z, x] + A ![z, y] := by
  simpa only [update_vec_one] using A.map_update_add ![z, x] 1 x y

theorem apply_vec_smul_right (c : ℝ) (x z : E) : A ![z, c • x] = c * A ![z, x] := by
  simpa only [update_vec_one, smul_eq_mul] using A.map_update_smul ![z, x] 1 c x

variable {A}

/-- **Lower bound on the least curvature of a perturbed form.** If the bilinear form `M = T + c N`
is a model of `A` (`c ≥ 0`, `N[d, d] ≤ K ‖d‖²` for all `d`, `K ≥ 0`), then
`λ_min[A] ≥ λ_min[M] - ‖A - T‖ - c K`. (This is the computation (4.1.27)–(4.1.29), (5.5.15)–(5.5.17)
of [cartis2022evaluation]: `min (a + b) ≥ min a + min b`.) -/
theorem minCurvature_ge_of_add_smul
    (A T N : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) {c K : ℝ} (hc : 0 ≤ c)
    (hK : 0 ≤ K) (hN : ∀ d, N (fun _ => d) ≤ K * ‖d‖ ^ 2) :
    minCurvature (T + c • N) - ‖A - T‖ - c * K ≤ minCurvature A := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [minCurvature_of_subsingleton]
    have := norm_nonneg (A - T)
    nlinarith [mul_nonneg hc hK]
  refine le_minCurvature_iff.2 fun d => ?_
  have h1 := minCurvature_mul_norm_sq_le (T + c • N) d
  have h2 : -(‖A - T‖ * ‖d‖ ^ 2) ≤ (A - T) (fun _ => d) :=
    neg_le_of_abs_le (abs_apply_diag_le (A - T) d)
  have h3 : c * N (fun _ => d) ≤ c * (K * ‖d‖ ^ 2) := mul_le_mul_of_nonneg_left (hN d) hc
  have hsplit : A (fun _ => d) = (A - T) (fun _ => d) + (T + c • N) (fun _ => d) -
      c * N (fun _ => d) := by
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hsplit]
  nlinarith

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product as a continuous bilinear form, `innerForm (v, w) = ⟪v, w⟫` (the identity
matrix `I` of [cartis2022evaluation]). -/
noncomputable def innerForm : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  @ContinuousLinearMap.uncurryLeft ℝ 1 (fun _ => E) ℝ _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 ℝ E ℝ).symm : (E →L[ℝ] ℝ) →L[ℝ] _).comp (innerSL ℝ)

@[simp]
theorem innerForm_apply (v : Fin 2 → E) : innerForm v = ⟪v 0, v 1⟫ := rfl

theorem innerForm_apply_diag (d : E) : innerForm (fun _ => d) = ‖d‖ ^ 2 := by
  simp

/-- `λ_min[I] = 1` on a nonzero space. -/
theorem minCurvature_innerForm [Nontrivial E] : minCurvature (innerForm : E [×2]→L[ℝ] ℝ) = 1 := by
  refine le_antisymm ?_ (le_minCurvature_iff.2 fun d => by simp)
  obtain ⟨d, hd⟩ := exists_norm_eq E zero_le_one
  simpa [innerForm_apply_diag, hd] using minCurvature_le_apply innerForm hd

/-- **Shifted forms** ([cartis2022evaluation], (3.4.33)): `λ_min[A + λ I] = λ_min[A] + λ`. -/
theorem minCurvature_add_smul_inner [Nontrivial E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (lam : ℝ) :
    minCurvature (A + lam • innerForm) = minCurvature A + lam := by
  have happ : ∀ d : E, (A + lam • (innerForm : E [×2]→L[ℝ] ℝ)) (fun _ => d) =
      A (fun _ => d) + lam * ‖d‖ ^ 2 :=
    fun d => by simp
  refine le_antisymm ?_ ?_
  · have h : minCurvature (A + lam • innerForm) - lam ≤ minCurvature A := by
      refine le_minCurvature_iff.2 fun d => ?_
      have := minCurvature_mul_norm_sq_le (A + lam • innerForm) d
      rw [happ] at this
      linarith
    linarith
  · refine le_minCurvature_iff.2 fun d => ?_
    have := minCurvature_mul_norm_sq_le A d
    rw [happ]
    linarith

variable {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}

/-- A symmetric form on a sum: `A[x + t y, x + t y] = A[x, x] + 2t A[x, y] + t² A[y, y]`. -/
theorem apply_diag_add_smul (hA : ∀ v w, A ![v, w] = A ![w, v]) (x y : E) (t : ℝ) :
    A (fun _ => x + t • y) = A (fun _ => x) + 2 * t * A ![x, y] + t ^ 2 * A (fun _ => y) := by
  rw [apply_diag_eq_vec, apply_diag_eq_vec, apply_diag_eq_vec, apply_vec_add_left,
    apply_vec_add_right, apply_vec_add_right, apply_vec_smul_left, apply_vec_smul_left,
    apply_vec_smul_right, apply_vec_smul_right, hA y x]
  ring

/-- **Minimizers are eigenvectors** ([cartis2022evaluation], (3.2.3)). If `A` is symmetric and the
unit vector `u` attains `λ_min[A]`, then `A[u, w] = λ_min[A] ⟪u, w⟫` for all `w`. This is the
bilinear-form version of Mathlib's `IsSelfAdjoint.hasEigenvector_of_isMinOn`; it needs neither
completeness nor an associated operator. -/
theorem apply_eq_minCurvature_mul_inner (hA : ∀ v w, A ![v, w] = A ![w, v]) {u : E}
    (hu : ‖u‖ = 1) (hmin : A (fun _ => u) = minCurvature A) (w : E) :
    A ![u, w] = minCurvature A * ⟪u, w⟫ := by
  set μ := minCurvature A
  set a := A ![u, w] - μ * ⟪u, w⟫
  set b := A (fun _ => w) - μ * ‖w‖ ^ 2
  have hb : 0 ≤ b := by have := minCurvature_mul_norm_sq_le A w; simp only [b]; linarith
  have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b := by
    intro t
    have h := minCurvature_mul_norm_sq_le A (u + t • w)
    rw [apply_diag_add_smul hA, hmin, norm_add_sq_real, norm_smul, inner_smul_right, hu,
      Real.norm_eq_abs, mul_pow, sq_abs] at h
    simp only [a, b]
    nlinarith
  have h := key (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have h2 : 0 ≤ -a ^ 2 * (b + 2) := by
    have := mul_nonneg h (sq_nonneg (b + 1))
    field_simp at this
    nlinarith
  have : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
  have : a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  simp only [a] at this
  linarith

/-- **Eigenvector of `λ_min`** ([cartis2022evaluation], (3.2.3)). In finite dimension, for a
symmetric form `A` and any `g`, there is a unit vector `u` with `A[u, u] = λ_min[A]`,
`A[u, w] = λ_min[A] ⟪u, w⟫` for all `w`, and `⟪u, g⟫ ≤ 0`. -/
theorem exists_eigenvector_minCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    (hA : ∀ v w, A ![v, w] = A ![w, v]) (g : E) :
    ∃ u, ‖u‖ = 1 ∧ A (fun _ => u) = minCurvature A ∧
      (∀ w, A ![u, w] = minCurvature A * ⟪u, w⟫) ∧ ⟪u, g⟫ ≤ 0 := by
  obtain ⟨u, hu, hmin⟩ := exists_eq_minCurvature A
  by_cases hg : ⟪u, g⟫ ≤ 0
  · exact ⟨u, hu, hmin, apply_eq_minCurvature_mul_inner hA hu hmin, hg⟩
  · have hu' : ‖-u‖ = 1 := by rw [norm_neg, hu]
    have hmin' : A (fun _ => -u) = minCurvature A := by
      rw [← hmin, apply_diag_eq_vec, apply_diag_eq_vec, ← neg_one_smul ℝ u, apply_vec_smul_left,
        apply_vec_smul_right]
      ring
    refine ⟨-u, hu', hmin', apply_eq_minCurvature_mul_inner hA hu' hmin', ?_⟩
    rw [inner_neg_left]
    linarith

section Operator

variable {T : E →ₗ[ℝ] E}

/-- `λ_min[A]` lies below every eigenvalue of `T` when `A[v, w] = ⟪v, T w⟫`. -/
theorem minCurvature_le_of_hasEigenvalue (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue T μ) : minCurvature A ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hv0 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv.2; positivity
  have h := minCurvature_mul_norm_sq_le A v
  rw [apply_diag_eq_vec, hAT, hTv, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  exact le_of_mul_le_mul_right h hv0

/-- A form `A[v, w] = ⟪v, T w⟫` with `T` symmetric is symmetric. -/
theorem apply_vec_comm_of_isSymmetric (hT : T.IsSymmetric) (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫)
    (v w : E) : A ![v, w] = A ![w, v] := by
  rw [hAT, hAT, ← hT, real_inner_comm]

/-- `λ_min[A]` is an eigenvalue of `T` when `A[v, w] = ⟪v, T w⟫`, `T` symmetric, on a nonzero
finite-dimensional space. -/
theorem hasEigenvalue_minCurvature [FiniteDimensional ℝ E] [Nontrivial E] (hT : T.IsSymmetric)
    (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) : Module.End.HasEigenvalue T (minCurvature A) := by
  obtain ⟨u, hu, -, heig, -⟩ :=
    exists_eigenvector_minCurvature (apply_vec_comm_of_isSymmetric hT hAT) (0 : E)
  have hTu : T u = minCurvature A • u := ext_inner_right ℝ fun w => by
    rw [hT, ← hAT, heig, real_inner_smul_left]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 hTu, hu0⟩

/-- **`λ_min` is the least eigenvalue** ([cartis2022evaluation], Section A.5). If
`A[v, w] = ⟪v, T w⟫` with `T` symmetric on a finite-dimensional space, `λ_min[A]` is the least of
the eigenvalues of `T` (both sides are `0` on the zero space). -/
theorem minCurvature_eq_iInf_eigenvalues [FiniteDimensional ℝ E] (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (hAT : ∀ v w, A ![v, w] = ⟪v, T w⟫) :
    minCurvature A = ⨅ i, hT.eigenvalues hn i := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have h2 : IsEmpty (Fin n) := by
      rw [← hn, Module.finrank_zero_of_subsingleton]; infer_instance
    rw [minCurvature_of_subsingleton, Real.iInf_of_isEmpty]
  have : Nonempty (Fin n) := ⟨⟨0, hn ▸ Module.finrank_pos⟩⟩
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn (hasEigenvalue_minCurvature hT hAT)
  refine le_antisymm (le_ciInf fun j => minCurvature_le_of_hasEigenvalue hAT
    (hT.hasEigenvalue_eigenvalues hn j)) ?_
  rw [← hi]
  exact ciInf_le (Set.finite_range _).bddBelow i

/-- `λ_min[A]` is the least Rayleigh quotient `H.rayleighQuotient x = ⟪H x, x⟫ / ‖x‖²` when
`A[v, w] = ⟪v, H w⟫` ([cartis2022evaluation], (A.2)–(A.3)); compare Mathlib's
`IsSelfAdjoint.hasEigenvalue_iInf_of_finiteDimensional`. -/
theorem minCurvature_eq_iInf_rayleigh [FiniteDimensional ℝ E] [Nontrivial E] {H : E →L[ℝ] E}
    (hAH : ∀ v w, A ![v, w] = ⟪v, H w⟫) :
    minCurvature A = ⨅ x : {x : E // x ≠ 0}, H.rayleighQuotient x := by
  have hR : ∀ x : E, H.rayleighQuotient x = ⟪H x, x⟫ / ‖x‖ ^ 2 := fun x => by
    rfl
  simp_rw [hR]
  have hq : ∀ x : {x : E // x ≠ 0}, minCurvature A ≤ ⟪H x, x⟫ / ‖(x : E)‖ ^ 2 := by
    intro x
    have hx : 0 < ‖(x : E)‖ ^ 2 := by have := norm_pos_iff.2 x.2; positivity
    rw [le_div_iff₀ hx, real_inner_comm, ← hAH, ← apply_diag_eq_vec]
    exact minCurvature_mul_norm_sq_le A x
  obtain ⟨u, hu, hmin⟩ := exists_eq_minCurvature A
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have : Nonempty {x : E // x ≠ 0} := ⟨⟨u, hu0⟩⟩
  refine le_antisymm (le_ciInf hq) ?_
  refine (ciInf_le ⟨minCurvature A, ?_⟩ (⟨u, hu0⟩ : {x : E // x ≠ 0})).trans ?_
  · rintro _ ⟨x, rfl⟩
    exact hq x
  · simp only [hu, one_pow, div_one]
    rw [real_inner_comm, ← hAH, ← apply_diag_eq_vec, hmin]

end Operator

/-- **`λ_min` of a symmetric matrix** ([cartis2022evaluation], Section A.5). If `M` is a real
symmetric matrix and `A[v, w] = ⟪v, M w⟫` on `EuclideanSpace ℝ ι`, then `λ_min[A]` is the least
of the eigenvalues `M.IsHermitian.eigenvalues`. -/
theorem minCurvature_eq_iInf_isHermitian_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    {A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ ι) ℝ}
    (hAM : ∀ v w, A ![v, w] = ⟪v, Matrix.toEuclideanLin M w⟫) :
    minCurvature A = ⨅ i, hM.eigenvalues i := by
  rw [minCurvature_eq_iInf_eigenvalues (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM)
    finrank_euclideanSpace hAM]
  exact (Equiv.iInf_comp (g := fun j => (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM).eigenvalues
    finrank_euclideanSpace j) (Fintype.equivOfCardEq (Fintype.card_fin _)).symm).symm

end Inner
