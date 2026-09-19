import Numlib.Variational.EllipticInterval.SturmLiouville
import NumlibSurface.Brezis.Chapter08.Section05

/-!
# Brezis §8.6: eigenfunctions and spectral decomposition

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §8.6: Theorem 8.22 (the Sturm–Liouville operator
`A u = −(p u')' + q u` with Dirichlet conditions on `I = (0, 1)` has a sequence of eigenvalues
`λₙ → +∞` and a Hilbert basis of `L²(I)` of `C²` eigenfunctions), the properties of the solution
operator `T : f ↦ u` established in its proof, its Example (`p ≡ 1`, `q ≡ 0`: `√2 sin(nπx)`,
`n²π²`) and Remark 30. Over `Numlib/Variational/EllipticInterval/SturmLiouville` and the compact
self-adjoint spectral theorem of chapter 6
(`ContinuousLinearMap.IsSymmetric.eigenvectorHilbertBasis`).

## Correspondence

* The book's hypotheses `p ∈ C¹(Ī)`, `p ≥ α > 0`, `q ∈ C(Ī)` — and, for the operator `T`, the
  reduction `q ≥ 0` — are the backbone's `EllipticInterval.SturmLiouville.Hypotheses 0 1 p q α`.
  Theorem 8.22 is stated for an arbitrary continuous `q`: the book's reduction ("replace `q` by
  `q + C`, which amounts to replacing `λₙ` by `λₙ + C`") is carried out in the proof.
* `L²(I)` is `Lp ℝ 2 (volume.restrict (Ioo 0 1))`; "a Hilbert basis `(eₙ)`" is
  `HilbertBasis ℕ ℝ (L²(I))`; "`eₙ ∈ C²(Ī)`" is a `ContDiffMapIcc zero_le_one 2` agreeing a.e.
  with `eₙ`; the equation (37) is stated on `(0, 1)` with `deriv` of the `C(ℝ)` extension of
  `eₙ'` (`e.shift.extend`), as in §8.4.
* The sine example: `√2 sin(nπx)`, `n ≥ 1`, is `sinUnitFun (n − 1)` and the Hilbert basis
  `sinBasisUnit` of `Numlib/Analysis/Fourier/SineBasis` (indexed from `0`).

## Main results

* `theorem_8_22`, `theorem_8_22_basis`, `theorem_8_22_eigen`, `theorem_8_22_tendsto` — Theorem
  8.22 and its three conclusions.
* `theorem_8_22_operator` — the solution operator `T` of the proof is bounded, compact,
  self-adjoint, positive and injective.
* `sineEigenfunctions`, `sineEigenfunctions_eigen`, `sineEigenfunctions_hilbertBasis`,
  `sineEigenfunctions_eigenvalue` — the Example.
* `remark_8_30_bounded_selfAdjoint`, `remark_8_30_not_compact` — the operator `T` of Example 8
  on `ℝ` is bounded and self-adjoint, and not compact.

Remark 29 (the eigenvalues of `−u''` under the boundary conditions of Examples 3, 5, 6, 7, "as
an exercise") is not formalized (chapter plan).
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval EllipticInterval.SturmLiouville
open scoped InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

/-! ### Theorem 8.22 -/

/-- The hypotheses of Theorem 8.22 for `q + C`, `C ≥ 0` a bound for `−q` on `[0, 1]`: the
book's reduction to `q ≥ 0`. -/
private theorem hypotheses_add_const {p q : ℝ → ℝ} {α : ℝ} (hp : ContDiffOn ℝ 1 p (Icc 0 1))
    (hα : 0 < α) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α ≤ p x) (hq : ContinuousOn q (Icc 0 1)) :
    ∃ C : ℝ, Hypotheses 0 1 p (fun x ↦ q x + C) α := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hq
  refine ⟨max 0 (-q x₀), ⟨zero_lt_one, hp, hα, hpα, hq.add continuousOn_const, fun x hx ↦ ?_⟩⟩
  have := isMinOn_iff.1 hmin x hx
  have := le_max_right 0 (-q x₀)
  linarith

/-- **Theorem 8.22, existence of the eigenvalues and eigenfunctions.** Let `p ∈ C¹(Ī)`, `p ≥ α > 0`
on `I = (0, 1)`, and `q ∈ C(Ī)`. Then there are a sequence `(λₙ)` of real numbers and a Hilbert
basis `(eₙ)` of `L²(I)` such that every `eₙ` agrees a.e. with an `e ∈ C²(Ī)` satisfying (37):
`−(p e')' + q e = λₙ e` on `I` and `e(0) = e(1) = 0`; furthermore `λₙ → +∞`. The book's
reduction to `q ≥ 0` (replace `q` by `q + C` and `λₙ` by `λₙ + C`) and the backbone's
`SturmLiouville.eigenfunction`, `eigenvalue`, `exists_contDiffMapIcc_eigenfunction`,
`tendsto_eigenvalue_atTop` (the spectral theorem for the compact self-adjoint solution
operator, Theorem 6.11). -/
theorem theorem_8_22 {p q : ℝ → ℝ} {α : ℝ} (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hα : 0 < α)
    (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α ≤ p x) (hq : ContinuousOn q (Icc 0 1)) :
    ∃ (l : ℕ → ℝ) (e : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))),
      (∀ n, ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
        ((e n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v.extend) ∧
        v.extend 0 = 0 ∧ v.extend 1 = 0 ∧
        ∀ x ∈ Ioo (0 : ℝ) 1,
          -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = l n * v.extend x) ∧
      Tendsto l atTop atTop := by
  obtain ⟨C, h⟩ := hypotheses_add_const hp hα hpα hq
  refine ⟨fun n ↦ eigenvalue h n - C, eigenfunction h, fun n ↦ ?_, ?_⟩
  · obtain ⟨v, hv, hv0, hv1, hode⟩ := exists_contDiffMapIcc_eigenfunction h n
    refine ⟨v, hv, hv0, hv1, fun x hx ↦ ?_⟩
    have := hode x hx
    linarith
  · exact tendsto_atTop_add_const_right _ (-C) (tendsto_eigenvalue_atTop h)

/-- **Theorem 8.22, the Hilbert basis clause**, for `q ≥ 0` (the backbone's normalization):
the eigenfunctions `eₙ = SturmLiouville.eigenfunction h n` form a Hilbert basis of `L²(I)`
consisting of eigenvectors of the solution operator `T`, `T eₙ = μₙ eₙ` with `μₙ = 1/λₙ > 0`. -/
theorem theorem_8_22_basis {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) (n : ℕ) :
    solutionOperator h (eigenfunction h n) = (eigenvalue h n)⁻¹ • eigenfunction h n ∧
      0 < eigenvalue h n := by
  refine ⟨?_, eigenvalue_pos h n⟩
  rw [eigenvalue, inv_inv]
  exact solutionOperator_eigenfunction h n

/-- **Theorem 8.22, the eigenfunction equation (37)**, for `q ≥ 0`: `eₙ ∈ C²(Ī)` with
`−(p eₙ')' + q eₙ = λₙ eₙ` on `I` and `eₙ(0) = eₙ(1) = 0`. The backbone's
`SturmLiouville.exists_contDiffMapIcc_eigenfunction`. -/
theorem theorem_8_22_eigen {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) (n : ℕ) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ((eigenfunction h n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v.extend) ∧
      v.extend 0 = 0 ∧ v.extend 1 = 0 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1,
        -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x
          = eigenvalue h n * v.extend x :=
  exists_contDiffMapIcc_eigenfunction h n

/-- **Theorem 8.22, "`λₙ → +∞`"**, for `q ≥ 0`: `λₙ = 1/μₙ` with `μₙ → 0`, `μₙ > 0`. -/
theorem theorem_8_22_tendsto {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) :
    Tendsto (eigenvalue h) atTop atTop :=
  tendsto_eigenvalue_atTop h

/-- **The solution operator `T : L²(I) → L²(I)`, `f ↦ u`, of the proof of Theorem 8.22** (with
`q ≥ 0`), where `u ∈ H²(I) ∩ H_0^1(I)` is the unique solution of `−(p u')' + q u = f`,
`u(0) = u(1) = 0` (38): `T` is a bounded operator (`SturmLiouville.solutionOperator`; the
estimate `‖T f‖_{H¹} ≤ C ‖f‖_{L²}` is `norm_solution_le`), it is compact (the injection
`H¹(I) ⊆ L²(I)` being compact since `I` is bounded), self-adjoint (`∫ (T f) g = ∫ f (T g)`),
positive (`∫ (T f) f ≥ 0`), and `N(T) = {0}`; Theorem 6.11 then applies. -/
theorem theorem_8_22_operator {p q : ℝ → ℝ} {α : ℝ} (h : Hypotheses 0 1 p q α) :
    (∀ f, solutionOperator h f = SobolevInterval.deriv (solution h f) 0) ∧
    IsCompactOperator (solutionOperator h) ∧
    (∀ f g, ⟪solutionOperator h f, g⟫_ℝ = ⟪f, solutionOperator h g⟫_ℝ) ∧
    (∀ f, 0 ≤ ⟪solutionOperator h f, f⟫_ℝ) ∧
    LinearMap.ker (solutionOperator h : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) = ⊥ :=
  ⟨solutionOperator_apply h, isCompactOperator_solutionOperator h,
    fun f g ↦ isSymmetric_solutionOperator h f g, inner_solutionOperator_nonneg h,
    ker_solutionOperator h⟩

/-! ### The Example: `p ≡ 1`, `q ≡ 0` -/

/-- **The Example of §8.6, the functions.** For `p ≡ 1` and `q ≡ 0`, `eₙ(x) = √2 sin(nπx)` and
`λₙ = n²π²`, `n = 1, 2, …`: the function `√2 sin((n+1)πx)` (`sinUnitFun n`, `n ≥ 0`) is `C²`,
vanishes at `0` and `1`, and satisfies `−eₙ'' = (n+1)²π² eₙ`. -/
theorem sineEigenfunctions_eigen (n : ℕ) :
    ContDiff ℝ 2 (sinUnitFun n) ∧ sinUnitFun n 0 = 0 ∧ sinUnitFun n 1 = 0 ∧
      ∀ x, -deriv (deriv (sinUnitFun n)) x = ((n + 1) * Real.pi) ^ 2 * sinUnitFun n x :=
  ⟨(contDiff_sinUnitFun n).of_le (by simp), sinUnitFun_zero n, sinUnitFun_one n, fun x ↦ by
    rw [deriv_deriv_sinUnitFun]; ring⟩

/-- **The Example of §8.6, the Hilbert basis.** The functions `√2 sin((n+1)πx)`, `n ≥ 0`, form
a Hilbert basis of `L²(0, 1)` (`sinBasisUnit`, from the cosine basis of
`Numlib/Analysis/Fourier/CosineBasis` by the multiply-by-`sin` trick rather than from the abstract
spectral theorem), and they are eigenvectors of the solution operator of `−u''` with Dirichlet
conditions, `T sₙ = ((n+1)²π²)⁻¹ sₙ`. -/
theorem sineEigenfunctions_hilbertBasis :
    (∀ n, (sinBasisUnit n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ √2 * Real.sin ((n + 1) * Real.pi * x)) ∧
    ∀ n, solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n :=
  ⟨coeFn_sinBasisUnit, solutionOperator_sinBasisUnit⟩

/-- **The Example of §8.6, the eigenvalues.** The eigenvalues `λₙ` of Theorem 8.22 for
`p ≡ 1`, `q ≡ 0` are exactly the numbers `n²π²`, `n = 1, 2, …`, each simple: the range of
`SturmLiouville.eigenvalue hypotheses_one_zero` is `{(n+1)²π² : n ∈ ℕ}` and the map is
injective. The backbone's `SturmLiouville.eigenvalue_eq_sq_pi_sq` (by expanding an eigenvector
of `T` in the sine basis). -/
theorem sineEigenfunctions_eigenvalue :
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
      Function.Injective (eigenvalue hypotheses_one_zero) :=
  eigenvalue_eq_sq_pi_sq

/-- **The Example of §8.6, the classical form.** Every `C²` Dirichlet eigenfunction of `−u''` on
`[0, 1]` is a multiple of some `sin((n+1)πx)`, with eigenvalue `(n+1)²π²`: if `e ∈ C²[0, 1]`,
`e ≠ 0`, `−e'' = λ e` on `[0, 1]` and `e(0) = e(1) = 0`, then `λ = (n+1)²π²` for some `n` and
`e = c sin((n+1)πx)` for some `c ≠ 0`. The backbone's
`SturmLiouville.eq_smul_sin_of_dirichlet`. -/
theorem sineEigenfunctions_classical (e : ContDiffMapIcc (zero_le_one' ℝ) 2) {l : ℝ}
    (hode : ∀ x : Icc (0 : ℝ) 1, -e.deriv 2 x = l * e x)
    (h0 : e ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0) (h1 : e ⟨1, right_mem_Icc.2 zero_le_one⟩ = 0)
    (hne : e ≠ 0) :
    ∃ n : ℕ, l = ((n + 1) * Real.pi) ^ 2 ∧
      ∃ c : ℝ, c ≠ 0 ∧ ∀ x ∈ Icc (0 : ℝ) 1, e.extend x = c * Real.sin ((n + 1) * Real.pi * x) :=
  eq_smul_sin_of_dirichlet e hode h0 h1 hne

/-- **The Example of §8.6.** If `p ≡ 1` and `q ≡ 0`, then `eₙ(x) = √2 sin(nπx)` and
`λₙ = n²π²`, `n = 1, 2, …`: the sines are `C²` eigenfunctions (`sineEigenfunctions_eigen`), they
form a Hilbert basis of `L²(0, 1)` of eigenvectors of the solution operator
(`sineEigenfunctions_hilbertBasis`), and the eigenvalues of Theorem 8.22 are exactly the
`n²π²`, each simple (`sineEigenfunctions_eigenvalue`). -/
theorem sineEigenfunctions :
    (∀ n : ℕ, ContDiff ℝ 2 (sinUnitFun n) ∧ sinUnitFun n 0 = 0 ∧ sinUnitFun n 1 = 0 ∧
      ∀ x, -deriv (deriv (sinUnitFun n)) x = ((n + 1) * Real.pi) ^ 2 * sinUnitFun n x) ∧
    (∀ n, (sinBasisUnit n : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] sinUnitFun n) ∧
    (∀ n, solutionOperator hypotheses_one_zero (sinBasisUnit n)
      = (((n + 1) * Real.pi) ^ 2)⁻¹ • sinBasisUnit n) ∧
    range (eigenvalue hypotheses_one_zero) = range (fun n : ℕ ↦ ((n + 1) * Real.pi) ^ 2) ∧
    Function.Injective (eigenvalue hypotheses_one_zero) :=
  ⟨sineEigenfunctions_eigen, coeFn_sinBasisUnit, solutionOperator_sinBasisUnit,
    eigenvalue_eq_sq_pi_sq.1, eigenvalue_eq_sq_pi_sq.2⟩

/-! ### Remark 30 -/

/-- **Remark 30, the bounded self-adjoint part.** The operator `T : L²(ℝ) → L²(ℝ)`, `f ↦ u`,
where `u ∈ H²(ℝ)` is the solution of problem (30) of Example 8 (`Line.solution f`, read in
`L²(ℝ)` through the inclusion `H¹(ℝ) ⊆ L²(ℝ)`), is a bounded linear operator with
`⟨T f, g⟩ = ⟨f, T g⟩`: `⟨T f, g⟩ = (T f, T g)_{H¹}` by the weak equation of `T g` tested
against `T f`, which is symmetric. -/
theorem remark_8_30_bounded_selfAdjoint :
    ∃ T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ]
        Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)),
      (∀ f, T f = SobolevIntervalLp.deriv (Line.solution f) 0) ∧
      ∀ f g, ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ := by
  -- the weak solution depends linearly on `f`
  have hadd : ∀ f g, Line.solution (f + g) = Line.solution f + Line.solution g := fun f g ↦
    (Line.eq_solution_of_forall fun v ↦ by
      rw [map_add, add_apply, Line.form_solution, Line.form_solution,
        Line.load_apply_inner, Line.load_apply_inner, Line.load_apply_inner, inner_add_left]).symm
  have hsmul : ∀ (c : ℝ) f, Line.solution (c • f) = c • Line.solution f := fun c f ↦
    (Line.eq_solution_of_forall fun v ↦ by
      rw [map_smulₛₗ, smul_apply, Line.form_solution, Line.load_apply_inner,
        Line.load_apply_inner, real_inner_smul_left, RCLike.conj_to_real, smul_eq_mul]).symm
  -- and is bounded by `‖f‖`
  have hbound : ∀ f, ‖SobolevIntervalLp.deriv (Line.solution f) 0‖ ≤ 1 * ‖f‖ := fun f ↦ by
    rw [one_mul]
    refine (SobolevIntervalLp.norm_deriv_le _ 0).trans ?_
    rw [Line.solution, LinearIsometryEquiv.norm_map, Line.load]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [innerSL_apply_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) (SobolevIntervalLp.norm_derivL_le _)
  let Tₗ : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    { toFun := fun f ↦ SobolevIntervalLp.deriv (Line.solution f) 0
      map_add' := fun f g ↦ by simp only [hadd, SobolevIntervalLp.deriv_add]
      map_smul' := fun c f ↦ by simp only [hsmul, SobolevIntervalLp.deriv_smul, RingHom.id_apply] }
  refine ⟨Tₗ.mkContinuous 1 hbound, fun f ↦ rfl, fun f g ↦ ?_⟩
  -- `⟪T f, g⟫ = (T f, T g)_{H¹} = ⟪f, T g⟫`
  have e1 : ⟪SobolevIntervalLp.deriv (Line.solution f) 0, g⟫_ℝ
      = ⟪Line.solution g, Line.solution f⟫_ℝ := by
    rw [real_inner_comm, ← Line.load_apply_inner, ← Line.form_solution, Line.form_apply]
  have e2 : ⟪f, SobolevIntervalLp.deriv (Line.solution g) 0⟫_ℝ
      = ⟪Line.solution f, Line.solution g⟫_ℝ := by
    rw [← Line.load_apply_inner, ← Line.form_solution, Line.form_apply]
  change ⟪SobolevIntervalLp.deriv (Line.solution f) 0, g⟫_ℝ
    = ⟪f, SobolevIntervalLp.deriv (Line.solution g) 0⟫_ℝ
  rw [e1, e2, real_inner_comm]

/-- **Remark 30, the negative half.** The operator `T : L²(ℝ) → L²(ℝ)`, `f ↦ u` of
`remark_8_30_bounded_selfAdjoint` (any bounded operator with `T f = u(f)`, the weak solution of
problem (30) of Example 8), is *not* compact. `T` commutes with the translations `τ_n`
(`Line.solution_translateLp`), so for `f ≠ 0` the translates `f_n = τ_n f`, bounded in `L²(ℝ)`
by `‖f‖`, are mapped to the translates `τ_n (T f)` of the nonzero `T f` (`T` is injective,
`Line.solution_eq_zero_iff`), which have no convergent subsequence
(`Line.not_tendsto_translateLp`) — the argument of Remark 10 (c). The eigenvalues and the
spectrum of `T` (Exercise 8.38) are not stated. -/
theorem remark_8_30_not_compact
    (T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →L[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hT : ∀ f, T f = SobolevIntervalLp.deriv (Line.solution f) 0) : ¬ IsCompactOperator T := by
  intro hc
  -- a nonzero `f ∈ L²(ℝ)`: the indicator of `[0, 1]`
  obtain ⟨f, hf⟩ : ∃ f : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)), f ≠ 0 := by
    have hμs : volume.restrict ((⊤ : Opens ℝ) : Set ℝ) (Icc (0 : ℝ) 1) ≠ ⊤ := by
      rw [Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono inter_subset_left).trans_lt measure_Icc_lt_top |>.ne
    refine ⟨indicatorConstLp 2 measurableSet_Icc hμs (1 : ℝ), fun h0 ↦ ?_⟩
    have := congrArg norm h0
    rw [norm_zero, norm_indicatorConstLp two_ne_zero (by simp), norm_one, one_mul,
      measureReal_def, Measure.restrict_apply measurableSet_Icc, Opens.coe_top, inter_univ,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal zero_le_one, Real.one_rpow] at this
    exact one_ne_zero this
  -- `T f ≠ 0`
  have hg : T f ≠ 0 := fun h0 ↦ by
    rw [hT] at h0
    refine hf ((Line.solution_eq_zero_iff f).1 (SobolevMultiIndex.ext_of_fn_ae_eq ?_))
    change ⇑(SobolevIntervalLp.deriv (Line.solution f) 0) =ᵐ[_] _
    rw [h0]
    exact (Lp.coeFn_zero ℝ 2 _).trans SobolevMultiIndex.fn_zero.symm
  -- `T` commutes with the translations
  have hTn : ∀ n : ℕ, T (Line.translateLp n f) = Line.translateLp n (T f) := fun n ↦ by
    rw [hT, hT, Line.solution_translateLp, Line.deriv_translate]
  -- the translates `τ_n (T f)` lie in a compact set, so a subsequence converges
  have hc' : IsCompactOperator (T : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ]
      Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) := by rwa [ContinuousLinearMap.coe_coe]
  have hK := hc'.isCompact_closure_image_closedBall ‖f‖
  have hmem : ∀ n : ℕ, Line.translateLp n (T f) ∈ closure ((T : Lp ℝ 2 (volume.restrict
      ((⊤ : Opens ℝ) : Set ℝ)) →ₗ[ℝ] Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) ''
        Metric.closedBall 0 ‖f‖) := fun n ↦
    subset_closure ⟨Line.translateLp n f, by simp, hTn n⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact Line.not_tendsto_translateLp hg hφ a hlim

end Brezis.Chapter08
