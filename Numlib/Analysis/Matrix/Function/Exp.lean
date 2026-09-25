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

variable {A Q : Matrix n n ℂ}

omit [Nonempty n] in
/-- **[golub2013matrix] (9.3.2)**, read as `‖e^{At}‖₂ ≤ e^{α(A) t} M_S(t)` (the printed
`e^{α(A) t M_S(t)}` is a typesetting slip): if `Q` is unitary and `T = Qᴴ A Q` is upper triangular
with strictly upper part `N`, then for `t ≥ 0`, `‖e^{tA}‖₂ ≤ e^{α(A) t} ∑_{k<n} ‖tN‖₂^k / k!`.
Van Loan's proof: iterate the variation-of-constants identity
`e^{tT} = e^{tD} + ∫₀ᵗ e^{(t-s)D} N e^{sT} ds`, `D` the diagonal of `T`; the `k`-th term is bounded
by `e^{αt} ‖N‖^k t^k/k!` because `‖e^{sD}‖₂ = e^{s max Re t_ii} ≤ e^{αs}`, and the remainder after
`n` steps carries `n` strictly upper triangular factors and vanishes. -/
theorem l2_opNorm_exp_smul_le_of_schur (hQ : Q ∈ unitaryGroup n ℂ)
    (hT : (star Q * A * Q).IsUpperTriangular) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (spectralAbscissa A * t) *
      ∑ k ∈ Finset.range (Fintype.card n),
        ‖t • (star Q * A * Q - diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k.factorial := by
  classical
  set T := star Q * A * Q
  set D : Matrix n n ℂ := diagonal fun i => T i i
  set N := T - D
  set α := spectralAbscissa A
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hQQ' : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  -- the diagonal entries of `T` are eigenvalues of `A`
  have hdiag : ∀ i, (T i i).re ≤ α := fun i => by
    have hmem : T i i ∈ spectrum ℂ T := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_of_isUpperTriangular _ hT,
        Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hTA : spectrum ℂ T = spectrum ℂ A := by
      have hu : IsUnit Q := ⟨⟨Q, star Q, hQQ', hQQ⟩, rfl⟩
      have := spectrum.units_conjugate (R := ℂ) (a := A) (u := (⟨star Q, Q, hQQ, hQQ'⟩ :
        (Matrix n n ℂ)ˣ))
      simpa [T] using this
    rw [hTA] at hmem
    exact re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hmem
  -- the exponential of the diagonal part
  set E : ℝ → Matrix n n ℂ := fun s => exp (s • D)
  have hE : ∀ s : ℝ, E s = diagonal fun i => Complex.exp (s * T i i) := fun s => by
    simp only [E, D, ← diagonal_smul, Matrix.exp_diagonal]
    congr 1
    rw [Pi.exp_def]
    funext i
    rw [Pi.smul_apply, Complex.real_smul, ← Complex.exp_eq_exp_ℂ]
  have hEnorm : ∀ s : ℝ, 0 ≤ s → ‖E s‖ ≤ Real.exp (α * s) := fun s hs => by
    rw [hE, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun i => ?_
    rw [Complex.norm_exp, Complex.re_ofReal_mul, mul_comm α]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdiag i) hs)
  have hEcont : Continuous E := by
    simp only [E]
    exact continuous_exp_matrix.comp (continuous_id.smul continuous_const)
  have hEadd : ∀ s u : ℝ, E (s + u) = E s * E u := fun s u => by
    simp only [E, add_smul]
    exact Matrix.exp_add_of_commute _ _ ((Commute.refl D).smul_left s |>.smul_right u)
  have hEband : ∀ s, IsBand 0 (E s) := fun s => by
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
  -- the iterated variation-of-constants terms and remainders
  let step : (ℝ → Matrix n n ℂ) → ℝ → Matrix n n ℂ := fun F t =>
    ∫ s in (0 : ℝ)..t, E (t - s) * N * F s
  let J : ℕ → ℝ → Matrix n n ℂ := fun k => step^[k] E
  let K : ℕ → ℝ → Matrix n n ℂ := fun k => step^[k] fun s => exp (s • T)
  have hstep_cont : ∀ F : ℝ → Matrix n n ℂ, Continuous F → Continuous (step F) := by
    intro F hF
    have hc : Continuous fun s => E (-s) * N * F s :=
      ((hEcont.comp continuous_neg).mul continuous_const).mul hF
    have heq : step F = fun t => E t * ∫ s in (0 : ℝ)..t, E (-s) * N * F s := by
      funext t
      change _ = (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (E t))
        (∫ s in (0 : ℝ)..t, E (-s) * N * F s)
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hc.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [ContinuousLinearMap.mul_apply']
      rw [← mul_assoc, ← mul_assoc, ← hEadd, sub_eq_add_neg]
    rw [heq]
    exact hEcont.mul
      (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0)
  have hJcont : ∀ k, Continuous (J k) := fun k => by
    induction k with
    | zero => exact hEcont
    | succ k ih =>
      simp only [J, Function.iterate_succ_apply']
      exact hstep_cont _ ih
  have hexpcont : Continuous fun s : ℝ => exp (s • T) :=
    continuous_exp_matrix.comp (continuous_id.smul continuous_const)
  have hKcont : ∀ k, Continuous (K k) := fun k => by
    induction k with
    | zero => exact hexpcont
    | succ k ih =>
      simp only [K, Function.iterate_succ_apply']
      exact hstep_cont _ ih
  have hstep_add : ∀ F G : ℝ → Matrix n n ℂ, Continuous F → Continuous G →
      step (F + G) = step F + step G := by
    intro F G hF hG
    funext t
    simp only [step, Pi.add_apply, mul_add]
    exact intervalIntegral.integral_add
      ((((hEcont.comp (continuous_const.sub continuous_id)).mul continuous_const).mul
        hF).intervalIntegrable _ _)
      ((((hEcont.comp (continuous_const.sub continuous_id)).mul continuous_const).mul
        hG).intervalIntegrable _ _)
  -- `K m = J m + K (m + 1)`
  have hTDN : T = D + N := by simp [N]
  have hK0 : (fun s : ℝ => exp (s • T)) = E + step fun s => exp (s • T) := by
    funext t
    have h := NormedSpace.exp_smul_add_sub_exp_smul D N t
    rw [← hTDN] at h
    simp only [Pi.add_apply, step, E]
    rw [← h]
    abel
  have hJs : ∀ m, J (m + 1) = step (J m) := fun m => Function.iterate_succ_apply' _ _ _
  have hKs : ∀ m, K (m + 1) = step (K m) := fun m => Function.iterate_succ_apply' _ _ _
  have hKsucc : ∀ m, K m = J m + K (m + 1) := fun m => by
    induction m with
    | zero => exact hK0
    | succ m ih =>
      rw [hKs m, hJs m, hKs (m + 1), ih, hstep_add _ _ (hJcont m) (hKcont (m + 1))]
  have hsum : ∀ m, (fun s : ℝ => exp (s • T)) = (∑ k ∈ Finset.range m, J k) + K m := fun m => by
    induction m with
    | zero => simp [K]
    | succ m ih => rw [ih, hKsucc m, Finset.sum_range_succ, add_assoc]
  -- the remainder vanishes after `card n` steps
  have hKband : ∀ m s, IsBand m (K m s) := fun m => by
    induction m with
    | zero =>
      intro s
      exact isBand_zero_of_isUpperTriangular (Matrix.BlockTriangular.exp
        (fun i j h => by rw [smul_apply, hT h, smul_zero]))
    | succ m ih =>
      intro s
      simp only [K, Function.iterate_succ_apply']
      refine IsBand.intervalIntegral (fun u => ?_) _ _
      have := ((hEband (s - u)).mul hNband).mul (ih u)
      rwa [zero_add, add_comm] at this
  have hKn : K (Fintype.card n) t = 0 := (hKband _ t).eq_zero
  -- the bound on each term
  have hJbound : ∀ k s, 0 ≤ s → ‖J k s‖ ≤ Real.exp (α * s) * ‖N‖ ^ k * s ^ k / k.factorial := by
    intro k
    induction k with
    | zero =>
      intro s hs
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      exact hEnorm s hs
    | succ k ih =>
      intro s hs
      simp only [J, Function.iterate_succ_apply']
      change ‖∫ u in (0 : ℝ)..s, E (s - u) * N * J k u‖ ≤ _
      have hbound : ∀ u ∈ Set.Ioc (0 : ℝ) s, ‖E (s - u) * N * J k u‖ ≤
          Real.exp (α * s) * ‖N‖ ^ (k + 1) / k.factorial * u ^ k := by
        intro u hu
        have h1 := hEnorm (s - u) (by linarith [hu.2])
        have h2 := ih u hu.1.le
        calc ‖E (s - u) * N * J k u‖ ≤ ‖E (s - u)‖ * ‖N‖ * ‖J k u‖ :=
              (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (norm_nonneg _))
          _ ≤ Real.exp (α * (s - u)) * ‖N‖ *
                (Real.exp (α * u) * ‖N‖ ^ k * u ^ k / k.factorial) := by gcongr
          _ = Real.exp (α * s) * ‖N‖ ^ (k + 1) / k.factorial * u ^ k := by
                rw [show α * s = α * (s - u) + α * u by ring, Real.exp_add]
                ring
      refine (intervalIntegral.norm_integral_le_of_norm_le hs
        (Filter.Eventually.of_forall hbound)
        (Continuous.intervalIntegrable (by fun_prop) _ _)).trans
        (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
      push_cast
      field_simp
      ring
  -- assemble
  have hconj : exp (t • A) = Q * exp (t • T) * star Q := by
    have hU : IsUnit Q := ⟨⟨Q, star Q, hQQ', hQQ⟩, rfl⟩
    have hA : t • A = Q * (t • T) * star Q := by
      simp only [T, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hQQ', one_mul]
      rw [mul_assoc, hQQ', mul_one]
    rw [hA, show star Q = Q⁻¹ from (inv_eq_left_inv hQQ).symm, Matrix.exp_conj _ _ hU]
  rw [hconj, l2_opNorm_unitary_mul_mul_unitary hQ _ (Unitary.star_mem hQ),
    show exp (t • T) = (fun s : ℝ => exp (s • T)) t from rfl, hsum (Fintype.card n),
    Pi.add_apply, hKn, add_zero, Finset.sum_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (hJbound k t ht).trans ?_)
  rw [norm_smul, Real.norm_of_nonneg ht, mul_pow]
  apply le_of_eq
  ring


/-! ### The relative perturbation bound -/

/-- **The relative perturbation bound** of [golub2013matrix] §9.3.2: with `T = Qᴴ A Q` upper
triangular with strictly upper part `N` and `M(t) = ∑_{k<n} ‖tN‖₂^k/k!`, for `t ≥ 0`,
`‖e^{t(A+E)} - e^{tA}‖₂ / ‖e^{tA}‖₂ ≤ t ‖E‖₂ M(t)² e^{t M(t) ‖E‖₂}`. The variation-of-constants
bound, the Schur bound (9.3.2) on `e^{(t-s)A}`, Gronwall's inequality on `e^{-αs} ‖e^{s(A+E)}‖`, and
`‖e^{tA}‖₂ ≥ e^{αt}`. -/
theorem l2_opNorm_exp_smul_add_sub_le {A Q : Matrix n n ℂ}
    (hQ : Q ∈ unitaryGroup n ℂ) (hT : (star Q * A * Q).IsUpperTriangular) (E : Matrix n n ℂ)
    {t : ℝ} (ht : 0 ≤ t) :
    let M : ℝ → ℝ := fun s => ∑ k ∈ Finset.range (Fintype.card n),
      ‖s • (star Q * A * Q - diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k.factorial
    ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      t * ‖E‖ * M t ^ 2 * Real.exp (t * M t * ‖E‖) := by
  intro M
  set α := spectralAbscissa A
  set N := star Q * A * Q - diagonal fun i => (star Q * A * Q) i i
  have hM0 : ∀ s, 0 ≤ M s := fun s => Finset.sum_nonneg fun k _ => by positivity
  have hMmono : ∀ s, 0 ≤ s → s ≤ t → M s ≤ M t := fun s hs hst =>
    Finset.sum_le_sum fun k _ => by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
      gcongr
  have hschur : ∀ s, 0 ≤ s → s ≤ t → ‖exp (s • A)‖ ≤ Real.exp (α * s) * M t := fun s hs hst =>
    (l2_opNorm_exp_smul_le_of_schur hQ hT hs).trans
      (mul_le_mul_of_nonneg_left (hMmono s hs hst) (Real.exp_pos _).le)
  have hcont : ∀ B : Matrix n n ℂ, Continuous fun s : ℝ => exp (s • B) := fun B =>
    continuous_exp_matrix.comp (continuous_id.smul continuous_const)
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
                mul_le_mul h5 h7 (norm_nonneg _) (by positivity)
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
