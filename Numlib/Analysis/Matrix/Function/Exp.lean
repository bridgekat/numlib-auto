import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Numlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Analysis.Normed.Algebra.Exponential
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic
import Numlib.Analysis.Normed.Algebra.SpectralRadius

/-!
# The matrix exponential: norms and perturbation

The matrix statements of [golub2013matrix] §9.3.2–9.3.3 about `e^{At}` in the spectral norm, on
top of the Banach-algebra layer `Numlib/Analysis/Normed/Algebra/Exponential` (variation of
constants, Van Loan's condition number `ν(A, t)` and its equality criterion):

* `Matrix.exp_spectralAbscissa_mul_le_l2_opNorm_exp_smul`: `e^{α(A) t} ≤ ‖e^{At}‖₂`, the spectral
  radius of `e^{At}` being at least `e^{α(A) t}` (`α` the spectral abscissa);
* `Matrix.l2_opNorm_exp_smul_of_isStarNormal`: `‖e^{At}‖₂ = e^{α(A) t}` for normal `A` and `t ≥ 0`
  ([golub2013matrix] (9.3.4));
* `Matrix.expCondNumber_eq_of_isStarNormal`: `ν(A, t) = t ‖A‖₂` for normal `A`, the true direction
  of [golub2013matrix] §9.3.2's "iff" (the other direction is false: see
  `NormedSpace.expCondNumber_eq_of_norm_exp_smul_eq`).

The exponential is Mathlib's `NormedSpace.exp`, which needs no norm on matrices; the norms are the
spectral norm of `open scoped Matrix.Norms.L2Operator`. The spectrum of `e^{At}` is computed by the
primary functional calculus (`pfc_exp_eq_normedSpace_exp`, `spectrum_pfc`).
-/

open NormedSpace Polynomial

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectrum of `e^{tA}` is `{e^{tλ} : λ ∈ σ(A)}` (spectral mapping through `pfc`). -/
theorem spectrum_exp_smul (A : Matrix n n ℂ) (t : ℝ) :
    spectrum ℂ (exp (t • A)) = (fun z => Complex.exp (t * z)) '' spectrum ℂ A := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral _
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  have hf : pfc (fun z : ℂ => (t : ℂ) * z) A = t • A := by
    rw [show (fun z : ℂ => (t : ℂ) * z) = fun z => (Polynomial.C (t : ℂ) * Polynomial.X).eval z by
      funext z; simp, pfc_polynomial hI hs, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      ← Algebra.smul_def, Complex.coe_smul]
  rw [← hf, ← pfc_exp_eq_normedSpace_exp (Algebra.IsIntegral.isIntegral _),
    ← pfc_comp (f := fun z : ℂ => (t : ℂ) * z) (g := Complex.exp) hI hs
      (fun μ _ => (contDiff_const.mul contDiff_id).contDiffAt)
      (fun μ _ => Complex.contDiff_exp.contDiffAt), spectrum_pfc hI hs]
  rfl

/-- The exponential is continuous on matrices with the spectral norm. -/
private theorem continuous_exp_matrix : Continuous (exp : Matrix n n ℂ → Matrix n n ℂ) :=
  continuous_iff_continuousAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

/-! ### Van Loan's iterated variation of constants

For `e^{t(D + N)}`, one step `F ↦ (t ↦ ∫₀ᵗ e^{(t - s)D} N F(s) ds)` of the variation-of-constants
identity `e^{t(D+N)} = e^{tD} + ∫₀ᵗ e^{(t-s)D} N e^{s(D+N)} ds`, iterated:
`e^{t(D+N)} = ∑_{k<m} stepᵏ(e^{·D})(t) + stepᵐ(e^{·(D+N)})(t)`. -/

section VariationOfConstants

variable (D N : Matrix n n ℂ)

/-- One step of Van Loan's iteration for `e^{t(D + N)}`: `F ↦ (t ↦ ∫₀ᵗ e^{(t - s)D} N F(s) ds)`. -/
private noncomputable def vocStep (F : ℝ → Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  ∫ s in (0 : ℝ)..t, exp ((t - s) • D) * N * F s

private theorem continuous_exp_smul (B : Matrix n n ℂ) : Continuous fun s : ℝ => exp (s • B) :=
  continuous_exp_matrix.comp (continuous_id.smul continuous_const)

private theorem exp_add_smul (s u : ℝ) : exp ((s + u) • D) = exp (s • D) * exp (u • D) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl D).smul_left s).smul_right u)

private theorem continuous_vocStep {F : ℝ → Matrix n n ℂ} (hF : Continuous F) :
    Continuous (vocStep D N F) := by
  have hE := continuous_exp_smul D
  have hc : Continuous fun s : ℝ => exp ((-s) • D) * N * F s :=
    ((hE.comp continuous_neg).mul continuous_const).mul hF
  have heq : vocStep D N F =
      fun t => exp (t • D) * ∫ s in (0 : ℝ)..t, exp ((-s) • D) * N * F s := by
    funext t
    change _ = (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (exp (t • D)))
      (∫ s in (0 : ℝ)..t, exp ((-s) • D) * N * F s)
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ContinuousLinearMap.mul_apply']
    rw [← mul_assoc, ← mul_assoc, ← exp_add_smul, sub_eq_add_neg]
  rw [heq]
  exact hE.mul (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0)

private theorem continuous_vocStep_iterate {F : ℝ → Matrix n n ℂ} (hF : Continuous F) (k : ℕ) :
    Continuous ((vocStep D N)^[k] F) := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact continuous_vocStep D N ih

private theorem vocStep_add {F G : ℝ → Matrix n n ℂ} (hF : Continuous F) (hG : Continuous G) :
    vocStep D N (F + G) = vocStep D N F + vocStep D N G := by
  have hE : Continuous fun s : ℝ => exp (s • D) := continuous_exp_smul D
  funext t
  simp only [vocStep, Pi.add_apply, mul_add]
  exact intervalIntegral.integral_add
    ((((hE.comp (continuous_const.sub continuous_id)).mul continuous_const).mul
      hF).intervalIntegrable _ _)
    ((((hE.comp (continuous_const.sub continuous_id)).mul continuous_const).mul
      hG).intervalIntegrable _ _)

/-- **Van Loan's expansion** of `e^{t(D + N)}` after `m` steps of variation of constants. -/
private theorem exp_smul_eq_sum_vocStep_add (m : ℕ) :
    (fun s : ℝ => exp (s • (D + N))) =
      (∑ k ∈ Finset.range m, (vocStep D N)^[k] fun s => exp (s • D)) +
        (vocStep D N)^[m] fun s => exp (s • (D + N)) := by
  have hJ := continuous_vocStep_iterate D N (continuous_exp_smul D)
  have hK := continuous_vocStep_iterate D N (continuous_exp_smul (D + N))
  have hsucc : ∀ m, (vocStep D N)^[m] (fun s => exp (s • (D + N))) =
      (vocStep D N)^[m] (fun s => exp (s • D)) +
        (vocStep D N)^[m + 1] (fun s => exp (s • (D + N))) := fun m => by
    induction m with
    | zero =>
      funext t
      have h := NormedSpace.exp_smul_add_sub_exp_smul D N t
      simp only [zero_add, Function.iterate_zero, Function.iterate_one, id_eq, Pi.add_apply]
      change _ = _ + ∫ s in (0 : ℝ)..t, exp ((t - s) • D) * N * exp (s • (D + N))
      rw [← h]
      abel
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply' _ (m + 1), ih, vocStep_add D N (hJ m) (hK (m + 1))]
  induction m with
  | zero => simp
  | succ m ih =>
    conv_lhs => rw [ih]
    rw [hsucc m, Finset.sum_range_succ, add_assoc]

/-- The `k`-th term of Van Loan's expansion is at most `e^{αs} ‖N‖ᵏ sᵏ / k!` when
`‖e^{sD}‖ ≤ e^{αs}` for `s ≥ 0`. -/
private theorem norm_vocStep_iterate_le {α : ℝ}
    (hD : ∀ s : ℝ, 0 ≤ s → ‖exp (s • D)‖ ≤ Real.exp (α * s)) (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖(vocStep D N)^[k] (fun u => exp (u • D)) s‖ ≤
      Real.exp (α * s) * ‖N‖ ^ k * s ^ k / k.factorial := by
  induction k generalizing s with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      div_one]
    exact hD s hs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ‖∫ u in (0 : ℝ)..s, exp ((s - u) • D) * N * (vocStep D N)^[k] (fun u => exp (u • D)) u‖
      ≤ _
    have hbound : ∀ u ∈ Set.Ioc (0 : ℝ) s,
        ‖exp ((s - u) • D) * N * (vocStep D N)^[k] (fun u => exp (u • D)) u‖ ≤
          Real.exp (α * s) * ‖N‖ ^ (k + 1) / k.factorial * u ^ k := by
      intro u hu
      have h1 := hD (s - u) (by linarith [hu.2])
      have h2 := ih hu.1.le
      calc ‖exp ((s - u) • D) * N * (vocStep D N)^[k] (fun u => exp (u • D)) u‖
          ≤ ‖exp ((s - u) • D)‖ * ‖N‖ * ‖(vocStep D N)^[k] (fun u => exp (u • D)) u‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _))
        _ ≤ Real.exp (α * (s - u)) * ‖N‖ *
              (Real.exp (α * u) * ‖N‖ ^ k * u ^ k / k.factorial) := by gcongr
        _ = Real.exp (α * s) * ‖N‖ ^ (k + 1) / k.factorial * u ^ k := by
              rw [show α * s = α * (s - u) + α * u by ring, Real.exp_add]
              ring
    refine (intervalIntegral.norm_integral_le_of_norm_le hs
      (Filter.Eventually.of_forall hbound) (Continuous.intervalIntegrable (by fun_prop) _ _)).trans
      (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring

end VariationOfConstants

/-! ### The factor `M_S(t)` of the Schur bound -/

/-- The factor `M_S(t) = ∑_{k<n} ‖t N‖₂ᵏ / k!` of the Schur bound (9.3.2) of [golub2013matrix]
§9.3.2, for `N` the strictly upper triangular part of `T = Qᴴ A Q` (a Schur form of `A` when `Q` is
unitary and `T` upper triangular). -/
noncomputable def schurExpFactor (Q A : Matrix n n ℂ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card n),
    ‖t • (star Q * A * Q - diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k.factorial

theorem schurExpFactor_nonneg (Q A : Matrix n n ℂ) (t : ℝ) : 0 ≤ schurExpFactor Q A t :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- `M_S` is monotone on `[0, ∞)`. -/
theorem schurExpFactor_mono (Q A : Matrix n n ℂ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    schurExpFactor Q A s ≤ schurExpFactor Q A t :=
  Finset.sum_le_sum fun k _ => by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg (hs.trans hst)]
    gcongr

variable [Nonempty n]

/-- **The spectral radius bound** `e^{α(A) t} ≤ ‖e^{At}‖₂` ([golub2013matrix] §9.3.2), for every
real `t`: an eigenvalue `λ` of `A` with `Re λ = α(A)` gives the eigenvalue `e^{tλ}` of `e^{At}`,
of modulus `e^{α(A) t}`. -/
theorem exp_spectralAbscissa_mul_le_l2_opNorm_exp_smul (A : Matrix n n ℂ) (t : ℝ) :
    Real.exp (spectralAbscissa A * t) ≤ ‖exp (t • A)‖ := by
  obtain ⟨z, hz, hre⟩ := exists_mem_spectrum_re_eq_spectralAbscissa
    (Matrix.finite_spectrum A).isCompact
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)
  have hmem : Complex.exp (t * z) ∈ spectrum ℂ (exp (t • A)) := by
    rw [spectrum_exp_smul]
    exact ⟨z, hz, rfl⟩
  have h := spectrum.norm_le_norm_of_mem hmem
  rwa [Complex.norm_exp, Complex.re_ofReal_mul, hre, mul_comm] at h

omit [Nonempty n] in
/-- The exponential of a normal matrix is normal. -/
theorem isStarNormal_exp_smul {A : Matrix n n ℂ} (hA : IsStarNormal A) (t : ℝ) :
    IsStarNormal (exp (t • A)) := by
  refine ⟨?_⟩
  rw [star_exp, star_smul, star_trivial]
  exact ((hA.star_comm_self.symm.smul_left t).smul_right t).exp.symm

/-- **[golub2013matrix] (9.3.4)**: for a normal matrix and `t ≥ 0`, `‖e^{At}‖₂ = e^{α(A) t}`. The
exponential is normal, so its spectral norm is its spectral radius, the largest `|e^{tλ}|`. -/
theorem l2_opNorm_exp_smul_of_isStarNormal {A : Matrix n n ℂ} (hA : IsStarNormal A) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp (t • A)‖ = Real.exp (spectralAbscissa A * t) := by
  refine le_antisymm ?_ (exp_spectralAbscissa_mul_le_l2_opNorm_exp_smul A t)
  have := isStarNormal_exp_smul hA t
  obtain ⟨k, hk, hkr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (exp (t • A)))
  have hnorm : ‖exp (t • A)‖ = ‖k‖ := by
    have h := l2_opNorm_eq_spectralRadius_of_isStarNormal (exp (t • A))
    rw [← hkr] at h
    exact congrArg NNReal.toReal (ENNReal.coe_injective h)
  rw [hnorm]
  rw [spectrum_exp_smul] at hk
  obtain ⟨z, hz, rfl⟩ := hk
  rw [Complex.norm_exp, Complex.re_ofReal_mul, mul_comm]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hz) ht)

/-- **Van Loan's condition number of a normal matrix** ([golub2013matrix] §9.3.2): for normal `A`
and `t ≥ 0`, `ν(A, t) = t ‖A‖₂`. The book states "iff `A` is normal"; the converse is false
(`[1] ⊕ [[0, 1], [0, 0]]` has `‖e^{sA}‖₂ = e^s` for all `s ≥ 0`, hence `ν(A, t) = t ‖A‖₂` by the
same criterion `NormedSpace.expCondNumber_eq_of_norm_exp_smul_eq`). -/
theorem expCondNumber_eq_of_isStarNormal {A : Matrix n n ℂ} (hA : IsStarNormal A) {t : ℝ}
    (ht : 0 ≤ t) : expCondNumber A t = t * ‖A‖ :=
  expCondNumber_eq_of_norm_exp_smul_eq A ht fun s hs =>
    (l2_opNorm_exp_smul_of_isStarNormal hA hs.1).trans (by rw [mul_comm])

/-! ### The Schur bound (9.3.2) -/

section Schur

variable [LinearOrder n] [LocallyFiniteOrder n]

/-- A matrix whose nonzero entries lie at least `m` steps above the diagonal. -/
private def IsBand (m : ℕ) (M : Matrix n n ℂ) : Prop :=
  ∀ i j, M i j ≠ 0 → i ≤ j ∧ m ≤ (Finset.Ico i j).card

omit [DecidableEq n] [Nonempty n] in
private theorem IsBand.mul {a b : ℕ} {M N : Matrix n n ℂ} (hM : IsBand a M) (hN : IsBand b N) :
    IsBand (a + b) (M * N) := by
  intro i j hij
  rw [mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  have hM' := hM i k (left_ne_zero_of_mul hk)
  have hN' := hN k j (right_ne_zero_of_mul hk)
  refine ⟨hM'.1.trans hN'.1, ?_⟩
  have : (Finset.Ico i j).card = (Finset.Ico i k).card + (Finset.Ico k j).card := by
    have hu := Finset.card_union_of_disjoint (Finset.Ico_disjoint_Ico_consecutive i k j)
    convert hu using 2
    convert (Finset.Ico_union_Ico_eq_Ico hM'.1 hN'.1).symm
  omega

omit [Fintype n] [DecidableEq n] [Nonempty n] in
private theorem isBand_zero_of_isUpperTriangular {M : Matrix n n ℂ} (hM : M.IsUpperTriangular) :
    IsBand 0 M := fun _ _ hij => ⟨not_lt.mp fun h => hij (hM h), Nat.zero_le _⟩

omit [DecidableEq n] [Nonempty n] in
private theorem IsBand.eq_zero {M : Matrix n n ℂ} (hM : IsBand (Fintype.card n) M) : M = 0 := by
  ext i j
  by_contra h
  have h1 := (hM i j h).2
  have h2 : (Finset.Ico i j).card ≤ (Finset.univ.erase j).card :=
    Finset.card_le_card fun x hx => Finset.mem_erase.mpr
      ⟨(Finset.mem_Ico.mp hx).2.ne, Finset.mem_univ x⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ] at h2
  have : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

/-- The entry `M ↦ M i j` as a continuous `ℝ`-linear map. -/
private noncomputable def entryCLM (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

omit [Nonempty n] in
private theorem IsBand.intervalIntegral {m : ℕ} {f : ℝ → Matrix n n ℂ} (hf : ∀ s, IsBand m (f s))
    (a b : ℝ) : IsBand m (∫ s in a..b, f s) := by
  intro i j hij
  by_contra h
  apply hij
  have h0 : ∀ s, f s i j = 0 := fun s => by
    by_contra h'
    exact h (hf s i j h')
  by_cases hint : IntervalIntegrable f MeasureTheory.volume a b
  · have := (entryCLM i j).intervalIntegral_comp_comm hint
    have h0' : (fun s => entryCLM i j (f s)) = fun _ => 0 := funext fun s => h0 s
    change entryCLM i j (∫ s in a..b, f s) = 0
    rw [← this, h0', intervalIntegral.integral_zero]
  · rw [intervalIntegral.integral_undef hint]
    rfl

omit [Nonempty n] in
private theorem isBand_vocStep {m : ℕ} {D N : Matrix n n ℂ} (hD : ∀ s : ℝ, IsBand 0 (exp (s • D)))
    (hN : IsBand 1 N) {F : ℝ → Matrix n n ℂ} (hF : ∀ s, IsBand m (F s)) (t : ℝ) :
    IsBand (m + 1) (vocStep D N F t) := by
  refine IsBand.intervalIntegral (fun u => ?_) _ _
  have := ((hD (t - u)).mul hN).mul (hF u)
  rwa [zero_add, add_comm] at this

variable {A Q : Matrix n n ℂ}

omit [Nonempty n] in
/-- **[golub2013matrix] (9.3.2)**, read as `‖e^{At}‖₂ ≤ e^{α(A) t} M_S(t)` (the printed
`e^{α(A) t M_S(t)}` is a typesetting slip): if `Q` is unitary and `T = Qᴴ A Q` is upper triangular
with strictly upper part `N`, then for `t ≥ 0`, `‖e^{tA}‖₂ ≤ e^{α(A) t} ∑_{k<n} ‖tN‖₂^k / k!`
(`Matrix.schurExpFactor`). Van Loan's proof: iterate the variation-of-constants identity
`e^{tT} = e^{tD} + ∫₀ᵗ e^{(t-s)D} N e^{sT} ds`, `D` the diagonal of `T`; the `k`-th term is bounded
by `e^{αt} ‖N‖^k t^k/k!` because `‖e^{sD}‖₂ = e^{s max Re t_ii} ≤ e^{αs}`, and the remainder after
`n` steps carries `n` strictly upper triangular factors and vanishes. -/
theorem l2_opNorm_exp_smul_le_of_schur (hQ : Q ∈ unitaryGroup n ℂ)
    (hT : (star Q * A * Q).IsUpperTriangular) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (spectralAbscissa A * t) * schurExpFactor Q A t := by
  classical
  unfold schurExpFactor
  set T := star Q * A * Q
  set D : Matrix n n ℂ := diagonal fun i => T i i
  set N := T - D
  set α := spectralAbscissa A
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  -- the diagonal entries of `T` are eigenvalues of `A`
  have hdiag : ∀ i, (T i i).re ≤ α := fun i => by
    have hmem : T i i ∈ spectrum ℂ T := by
      rw [hT.spectrum_eq]
      exact Set.mem_range_self i
    have hTA : spectrum ℂ T = spectrum ℂ A := spectrum_conjTranspose_mul_mul hQ
    rw [hTA] at hmem
    exact re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hmem
  -- the exponential of the diagonal part
  have hE : ∀ s : ℝ, exp (s • D) = diagonal fun i => Complex.exp (s * T i i) := fun s => by
    simp only [D, ← diagonal_smul, Matrix.exp_diagonal]
    congr 1
    rw [Pi.exp_def]
    funext i
    rw [Pi.smul_apply, Complex.real_smul, ← Complex.exp_eq_exp_ℂ]
  have hEnorm : ∀ s : ℝ, 0 ≤ s → ‖exp (s • D)‖ ≤ Real.exp (α * s) := fun s hs => by
    rw [hE, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun i => ?_
    rw [Complex.norm_exp, Complex.re_ofReal_mul, mul_comm α]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdiag i) hs)
  have hEband : ∀ s : ℝ, IsBand 0 (exp (s • D)) := fun s => by
    rw [hE]
    exact isBand_zero_of_isUpperTriangular (blockTriangular_diagonal _)
  have hNband : IsBand 1 N := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      simp [N, D] at hij
    have hTij : T i j ≠ 0 := by simpa [N, D, diagonal_apply_ne _ hne] using hij
    have hle : i ≤ j := not_lt.mp fun h => hTij (hT h)
    exact ⟨hle, Finset.card_pos.mpr ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, lt_of_le_of_ne hle hne⟩⟩⟩
  have hTDN : T = D + N := by simp [N]
  -- the remainder vanishes after `card n` steps
  have hKband : ∀ m s, IsBand m ((vocStep D N)^[m] (fun u => exp (u • (D + N))) s) := fun m => by
    induction m with
    | zero =>
      intro s
      simp only [Function.iterate_zero, id_eq]
      rw [← hTDN]
      exact isBand_zero_of_isUpperTriangular (Matrix.BlockTriangular.exp
        (fun i j h => by rw [smul_apply, hT h, smul_zero]))
    | succ m ih =>
      intro s
      rw [Function.iterate_succ_apply']
      exact isBand_vocStep hEband hNband ih s
  -- assemble
  have hconj : exp (t • A) = Q * exp (t • T) * star Q := by
    have hU : IsUnit Q := ⟨⟨Q, star Q, hQQ', hQQ⟩, rfl⟩
    have hA : t • A = Q * (t • T) * star Q := by
      simp only [T, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hQQ', one_mul]
      rw [mul_assoc, hQQ', mul_one]
    rw [hA, show star Q = Q⁻¹ from (inv_eq_left_inv hQQ).symm, Matrix.exp_conj _ _ hU]
  rw [hconj, l2_opNorm_unitary_mul_mul_unitary hQ _ (Unitary.star_mem hQ), hTDN,
    show exp (t • (D + N)) = (fun s : ℝ => exp (s • (D + N))) t from rfl,
    exp_smul_eq_sum_vocStep_add D N (Fintype.card n), Pi.add_apply, (hKband _ t).eq_zero,
    add_zero, Finset.sum_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
    (norm_vocStep_iterate_le D N hEnorm k ht).trans ?_)
  rw [norm_smul, Real.norm_of_nonneg ht, mul_pow]
  apply le_of_eq
  ring

/-! ### The relative perturbation bound -/

/-- **The relative perturbation bound** of [golub2013matrix] §9.3.2: with `T = Qᴴ A Q` upper
triangular with strictly upper part `N` and `M(t) = ∑_{k<n} ‖tN‖₂^k/k!` (`Matrix.schurExpFactor`),
for `t ≥ 0`,
`‖e^{t(A+E)} - e^{tA}‖₂ / ‖e^{tA}‖₂ ≤ t ‖E‖₂ M(t)² e^{t M(t) ‖E‖₂}`. The variation-of-constants
bound, the Schur bound (9.3.2) on `e^{(t-s)A}`, Gronwall's inequality on `e^{-αs} ‖e^{s(A+E)}‖`, and
`‖e^{tA}‖₂ ≥ e^{αt}`. -/
theorem l2_opNorm_exp_smul_add_sub_le {A Q : Matrix n n ℂ}
    (hQ : Q ∈ unitaryGroup n ℂ) (hT : (star Q * A * Q).IsUpperTriangular) (E : Matrix n n ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      t * ‖E‖ * schurExpFactor Q A t ^ 2 * Real.exp (t * schurExpFactor Q A t * ‖E‖) := by
  set M := schurExpFactor Q A
  set α := spectralAbscissa A
  have hM0 : ∀ s, 0 ≤ M s := schurExpFactor_nonneg Q A
  have hMmono : ∀ s, 0 ≤ s → s ≤ t → M s ≤ M t := fun s hs hst => schurExpFactor_mono Q A hs hst
  have hschur : ∀ s, 0 ≤ s → s ≤ t → ‖exp (s • A)‖ ≤ Real.exp (α * s) * M t := fun s hs hst =>
    (l2_opNorm_exp_smul_le_of_schur hQ hT hs).trans
      (mul_le_mul_of_nonneg_left (hMmono s hs hst) (Real.exp_pos _).le)
  have hcont : ∀ B : Matrix n n ℂ, Continuous fun s : ℝ => exp (s • B) := continuous_exp_smul
  -- Gronwall for `φ(s) = e^{-αs} ‖e^{s(A+E)}‖`
  set φ : ℝ → ℝ := fun s => Real.exp (-(α * s)) * ‖exp (s • (A + E))‖
  have hφc : Continuous φ := by
    have := (hcont (A + E)).norm
    fun_prop
  have hφ : ∀ s ∈ Set.Icc 0 t, φ s ≤ M t + M t * ‖E‖ * ∫ r in (0 : ℝ)..s, φ r := by
    intro s hs
    have hint := norm_exp_smul_add_sub_exp_smul_le A E hs.1
    have h1 : ‖exp (s • (A + E))‖ ≤ ‖exp (s • A)‖ +
        ‖E‖ * ∫ r in (0 : ℝ)..s, ‖exp ((s - r) • A)‖ * ‖exp (r • (A + E))‖ := by
      have := norm_sub_norm_le (exp (s • (A + E))) (exp (s • A))
      linarith
    have h2 : ∫ r in (0 : ℝ)..s, ‖exp ((s - r) • A)‖ * ‖exp (r • (A + E))‖ ≤
        ∫ r in (0 : ℝ)..s, Real.exp (α * s) * M t * φ r := by
      refine intervalIntegral.integral_mono_on hs.1 (Continuous.intervalIntegrable
        (((hcont A).comp (continuous_const.sub continuous_id)).norm.mul (hcont (A + E)).norm) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) fun r hr => ?_
      have h5 := hschur (s - r) (by linarith [hr.2]) (by linarith [hr.1, hs.2])
      calc ‖exp ((s - r) • A)‖ * ‖exp (r • (A + E))‖
          ≤ Real.exp (α * (s - r)) * M t * ‖exp (r • (A + E))‖ :=
            mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
        _ = Real.exp (α * s) * M t * φ r := by
            simp only [φ]
            rw [show α * (s - r) = α * s + -(α * r) by ring, Real.exp_add]
            ring
    rw [intervalIntegral.integral_const_mul] at h2
    have h6 := hschur s hs.1 hs.2
    have hexp : Real.exp (-(α * s)) * Real.exp (α * s) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc φ s = Real.exp (-(α * s)) * ‖exp (s • (A + E))‖ := rfl
      _ ≤ Real.exp (-(α * s)) * (Real.exp (α * s) * M t +
            ‖E‖ * (Real.exp (α * s) * M t * ∫ r in (0 : ℝ)..s, φ r)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (Real.exp_pos _).le
          gcongr
      _ = M t + M t * ‖E‖ * ∫ r in (0 : ℝ)..s, φ r := by
          rw [mul_add, ← mul_assoc, hexp]
          linear_combination (M t * ‖E‖ * ∫ r in (0 : ℝ)..s, φ r) * hexp
  have hgron : ∀ s ∈ Set.Icc 0 t, φ s ≤ M t * Real.exp (M t * ‖E‖ * s) := fun s hs => by
    simpa using Gronwall.le_mul_exp_of_le_add_integral (g := fun _ => M t)
      (mul_nonneg (hM0 t) (norm_nonneg E)) monotoneOn_const hφc.continuousOn hφ hs
  -- bound the difference
  have hdiff : ‖exp (t • (A + E)) - exp (t • A)‖ ≤
      ‖E‖ * (Real.exp (α * t) * M t ^ 2 * (t * Real.exp (M t * ‖E‖ * t))) := by
    refine (norm_exp_smul_add_sub_exp_smul_le A E ht).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • A)‖ * ‖exp (s • (A + E))‖
        ≤ ∫ s in (0 : ℝ)..t, Real.exp (α * t) * M t ^ 2 * Real.exp (M t * ‖E‖ * t) := by
          refine intervalIntegral.integral_mono_on ht (Continuous.intervalIntegrable
            (((hcont A).comp (continuous_const.sub continuous_id)).norm.mul
              (hcont (A + E)).norm) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
            fun s hs => ?_
          have h5 := hschur (t - s) (by linarith [hs.2]) (by linarith [hs.1])
          have h6 := hgron s hs
          have h7 : ‖exp (s • (A + E))‖ ≤ Real.exp (α * s) * (M t * Real.exp (M t * ‖E‖ * s)) := by
            have : ‖exp (s • (A + E))‖ = Real.exp (α * s) * φ s := by
              simp only [φ]
              rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
            rw [this]
            exact mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
          have h8 : Real.exp (M t * ‖E‖ * s) ≤ Real.exp (M t * ‖E‖ * t) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2
              (mul_nonneg (hM0 t) (norm_nonneg E)))
          calc ‖exp ((t - s) • A)‖ * ‖exp (s • (A + E))‖
              ≤ (Real.exp (α * (t - s)) * M t) *
                  (Real.exp (α * s) * (M t * Real.exp (M t * ‖E‖ * s))) :=
                mul_le_mul h5 h7 (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (hM0 t))
            _ = Real.exp (α * t) * M t ^ 2 * Real.exp (M t * ‖E‖ * s) := by
                rw [show α * t = α * (t - s) + α * s by ring, Real.exp_add]
                ring
            _ ≤ Real.exp (α * t) * M t ^ 2 * Real.exp (M t * ‖E‖ * t) := by gcongr
      _ = Real.exp (α * t) * M t ^ 2 * (t * Real.exp (M t * ‖E‖ * t)) := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
          ring
  have hlow := exp_spectralAbscissa_mul_le_l2_opNorm_exp_smul A t
  have hpos : 0 < ‖exp (t • A)‖ := (Real.exp_pos _).trans_le hlow
  rw [div_le_iff₀ hpos]
  calc ‖exp (t • (A + E)) - exp (t • A)‖
      ≤ ‖E‖ * (Real.exp (α * t) * M t ^ 2 * (t * Real.exp (M t * ‖E‖ * t))) := hdiff
    _ = t * ‖E‖ * M t ^ 2 * Real.exp (t * M t * ‖E‖) * Real.exp (α * t) := by ring_nf
    _ ≤ t * ‖E‖ * M t ^ 2 * Real.exp (t * M t * ‖E‖) * ‖exp (t • A)‖ := by
        gcongr

end Schur

end Matrix
