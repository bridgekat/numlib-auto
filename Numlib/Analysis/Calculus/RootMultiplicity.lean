import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Roots of multiplicity `m` of a real function

`IsRootOfMultiplicity f α m` says that the first `m` derivatives `f, f', …, f^{(m-1)}` vanish at `α`
and `f^{(m)}(α) ≠ 0`. Mathlib has the notion for polynomials (`Polynomial.rootMultiplicity`) and for
analytic functions (`analyticOrderAt`) but not for merely `C^m` functions, which is what the
rootfinding chapters of [quarteroni2000numerical] work with.

The one theorem is the **Taylor factorization** `f x = (x - α)^m h x` with `h` continuous — `C^n`
when `f` is `C^{m+n}` — and `h α = f^{(m)}(α) / m!` (`IsRootOfMultiplicity.exists_eq_pow_mul`).
Everything about multiple roots follows from it: the error-versus-residual asymptotics
`|x - α| / |f x|^{1/m} → (m! / |f^{(m)}(α)|)^{1/m}` behind the conditioning estimates (6.4)–(6.7)
of [quarteroni2000numerical] §6.1 and the residual stopping test of §6.5
(`IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow`, `eventually_abs_sub_le_mul_abs_rpow`), the
linear convergence of Newton's method with factor `1 - 1/m` (`Numlib/Nonlinear/ScalarNewton`), and
the identification with `Polynomial.rootMultiplicity` (`Polynomial.isRootOfMultiplicity_eval_iff`).

The factor `h` is the `m`-fold iterate of Mathlib's `dslope`, so the factorization identity holds
everywhere (`pow_sub_smul_iterate_dslope_of_zero`) and its regularity reduces to **Hadamard's
lemma** in one variable, `ContDiffAt.dslope_same`: if `f` is `C^{n+1}` at `a` then
`dslope f a` is `C^n` at `a`, with `iteratedDeriv n (dslope f a) a = f^{(n+1)}(a) / (n + 1)`. That
lemma is proved from the integral representation
`dslope f a b = ∫₀¹ f'(a + t (b - a)) dt`, whose `k`-th derivative in `b` is
`∫₀¹ tᵏ f^{(k+1)}(a + t (b - a)) dt`, differentiated under the integral sign. Hadamard's lemma and
the two helpers on iterated derivatives over an open set are upstreaming candidates (natural home:
`Mathlib.Analysis.Calculus.DSlope`).
-/

open Filter Topology Set Nat
open scoped Interval

section OpenSet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {U : Set 𝕜}

/-- On an open set where `f` is `C^N`, the `j`-th derivative (`j < N`) is differentiable with the
`(j + 1)`-st derivative as its derivative. -/
theorem ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j < N) {b : 𝕜} (hb : b ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f b) b := by
  have hd : DifferentiableOn 𝕜 (iteratedDerivWithin j f U) U :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn
  have hd' : DifferentiableOn 𝕜 (iteratedDeriv j f) U :=
    hd.congr (iteratedDerivWithin_of_isOpen hU).symm
  rw [iteratedDeriv_succ]
  exact (hd'.differentiableAt (hU.mem_nhds hb)).hasDerivAt

/-- On an open set where `f` is `C^N`, the `j`-th derivative (`j ≤ N`) is continuous. -/
theorem ContDiffOn.continuousOn_iteratedDeriv_of_isOpen (hU : IsOpen U) {N : ℕ}
    (hf : ContDiffOn 𝕜 N f U) {j : ℕ} (hj : j ≤ N) : ContinuousOn (iteratedDeriv j f) U :=
  (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hU).symm

/-- A chain `G 0, G 1, …, G n` of functions on an open set, each the derivative of the previous
one and the last continuous, makes `G 0` a `C^n` function whose iterated derivatives are the
`G k`. -/
theorem contDiffOn_of_hasDerivAt_chain {G : ℕ → 𝕜 → F} (hU : IsOpen U) {n : ℕ}
    (hd : ∀ k < n, ∀ b ∈ U, HasDerivAt (G k) (G (k + 1) b) b) (hc : ContinuousOn (G n) U) :
    ContDiffOn 𝕜 n (G 0) U ∧ ∀ k ≤ n, Set.EqOn (iteratedDeriv k (G 0)) (G k) U := by
  induction n generalizing G with
  | zero =>
    refine ⟨contDiffOn_zero.2 hc, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp [Set.EqOn]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (G := fun k => G (k + 1))
      (fun k hk b hb => hd (k + 1) (by omega) b hb) hc
    have hderiv : Set.EqOn (deriv (G 0)) (G 1) U := fun b hb => (hd 0 (by omega) b hb).deriv
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun b hb => (hd 0 (by omega) b hb).differentiableAt.differentiableWithinAt, ?_,
        h1.congr hderiv⟩
      simp
    · cases k with
      | zero => simp [Set.EqOn]
      | succ k =>
        intro b hb
        rw [iteratedDeriv_succ', ← iteratedDerivWithin_of_isOpen hU hb,
          iteratedDerivWithin_congr hderiv hb, iteratedDerivWithin_of_isOpen hU hb]
        exact h2 k (by omega) hb

/-- **A `C^N` function is `N` times differentiable on a ball**: around a point where `f` is `C^N`
there is a ball on which each iterated derivative up to order `N - 1` has the next one as its
derivative, and the `N`-th is continuous. -/
theorem ContDiffAt.exists_ball_hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hf : ContDiffAt ℝ N f a) :
    ∃ δ > 0, (∀ j < N, ∀ x ∈ Metric.ball a δ,
        HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x) ∧
      ContinuousOn (iteratedDeriv N f) (Metric.ball a δ) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact ⟨r, hr, fun j hj x hx =>
    (hfu.mono hru).hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball hj hx,
    (hfu.mono hru).continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball le_rfl⟩

end OpenSet

section Hadamard

variable {f : ℝ → ℝ} {a : ℝ}

/-- `∫₀¹ tᵏ f^{(k+1)}(a + t (b - a)) dt`: the `k`-th derivative of `dslope f a` at `b`. -/
private noncomputable def dslopeDeriv (f : ℝ → ℝ) (a : ℝ) (k : ℕ) (b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) f ((b - a) * t + a)

/-- Points of the segment from `a` to `b` stay in `closedBall a |b - a|`. -/
private theorem segment_mem_closedBall {b t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (b - a) * t + a ∈ Metric.closedBall a (dist b a) := by
  rw [Metric.mem_closedBall, Real.dist_eq, Real.dist_eq, add_sub_cancel_right, abs_mul,
    abs_of_nonneg ht.1]
  exact mul_le_of_le_one_right (abs_nonneg _) ht.2

/-- `Ι 0 1 ⊆ Icc 0 1`. -/
private theorem uIoc_zero_one_subset : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
  rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self

/-- The integrand of `dslopeDeriv` is continuous on `[0, 1]` for `b` in the ball. -/
private theorem continuousOn_dslopeDeriv_integrand {r : ℝ} {N : ℕ}
    (hf : ContDiffOn ℝ N f (Metric.ball a r)) {k : ℕ} (hk : k + 1 ≤ N) {b : ℝ}
    (hb : b ∈ Metric.ball a r) :
    ContinuousOn (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) f ((b - a) * t + a)) (Icc 0 1) := by
  refine (continuousOn_pow k).mul ?_
  refine (hf.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball hk).comp
    (by fun_prop) fun t ht => ?_
  exact Metric.closedBall_subset_ball (Metric.mem_ball.1 hb) (segment_mem_closedBall ht)

/-- Differentiation under the integral sign: `dslopeDeriv f a k` has derivative
`dslopeDeriv f a (k + 1)` on the ball. -/
private theorem hasDerivAt_dslopeDeriv {r : ℝ} {N : ℕ} (hf : ContDiffOn ℝ N f (Metric.ball a r))
    {k : ℕ} (hk : k + 2 ≤ N) {b : ℝ} (hb : b ∈ Metric.ball a r) :
    HasDerivAt (dslopeDeriv f a k) (dslopeDeriv f a (k + 1) b) b := by
  obtain ⟨r', hbr', hr'r⟩ := exists_between (Metric.mem_ball.1 hb)
  have hK : Metric.closedBall a r' ⊆ Metric.ball a r := Metric.closedBall_subset_ball hr'r
  obtain ⟨M, hM⟩ := (isCompact_closedBall a r').exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball hk).mono hK)
  have hs : Metric.ball a r' ∈ 𝓝 b := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.2 hbr')
  have hsub : Metric.ball a r' ⊆ Metric.ball a r := Metric.ball_subset_ball hr'r.le
  have hmeas : ∀ x ∈ Metric.ball a r, ∀ j, j + 1 ≤ N → MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => t ^ j * iteratedDeriv (j + 1) f ((x - a) * t + a))
      (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := fun x hx j hj =>
    ((continuousOn_dslopeDeriv_integrand hf hj hx).mono uIoc_zero_one_subset).aestronglyMeasurable
      measurableSet_uIoc
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (F := fun x t => t ^ k * iteratedDeriv (k + 1) f ((x - a) * t + a))
    (F' := fun x t => t ^ (k + 1) * iteratedDeriv (k + 2) f ((x - a) * t + a))
    (bound := fun _ => M) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact (Metric.isOpen_ball.eventually_mem hb).mono fun x hx => hmeas x hx k (by omega)
  · exact ((continuousOn_dslopeDeriv_integrand hf (by omega) hb).mono
      (by simp)).intervalIntegrable
  · exact hmeas b hb (k + 1) hk
  · refine Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := uIoc_zero_one_subset ht
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht'.1]
    rw [← one_mul M]
    refine mul_le_mul (pow_le_one₀ ht'.1 ht'.2) ?_ (abs_nonneg _) zero_le_one
    exact hM _ (Metric.closedBall_subset_closedBall (Metric.mem_ball.1 hx).le
      (segment_mem_closedBall ht'))
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht x hx => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := uIoc_zero_one_subset ht
    have hy : (x - a) * t + a ∈ Metric.ball a r :=
      hsub (Metric.closedBall_subset_ball (Metric.mem_ball.1 hx) (segment_mem_closedBall ht'))
    have hg := hf.hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball (j := k + 1) (by omega) hy
    have hl : HasDerivAt (fun x : ℝ => (x - a) * t + a) t x := by
      simpa using (((hasDerivAt_id x).sub_const a).mul_const t).add_const a
    refine ((hg.comp x hl).const_mul (t ^ k)).congr_deriv ?_
    ring

/-- `dslopeDeriv f a k` is continuous on the ball. -/
private theorem continuousOn_dslopeDeriv {r : ℝ} {N : ℕ} (hf : ContDiffOn ℝ N f (Metric.ball a r))
    {k : ℕ} (hk : k + 1 ≤ N) : ContinuousOn (dslopeDeriv f a k) (Metric.ball a r) := by
  intro b hb
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨r', hbr', hr'r⟩ := exists_between (Metric.mem_ball.1 hb)
  have hK : Metric.closedBall a r' ⊆ Metric.ball a r := Metric.closedBall_subset_ball hr'r
  obtain ⟨M, hM⟩ := (isCompact_closedBall a r').exists_bound_of_continuousOn
    ((hf.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball hk).mono hK)
  have hs : Metric.ball a r' ∈ 𝓝 b := Metric.isOpen_ball.mem_nhds (Metric.mem_ball.2 hbr')
  refine intervalIntegral.continuousAt_of_dominated_interval (μ := MeasureTheory.volume)
    (F := fun x t => t ^ k * iteratedDeriv (k + 1) f ((x - a) * t + a)) (bound := fun _ => M)
    ?_ ?_ intervalIntegrable_const ?_
  · refine (Metric.isOpen_ball.eventually_mem hb).mono fun x hx => ?_
    exact ((continuousOn_dslopeDeriv_integrand hf hk hx).mono
      uIoc_zero_one_subset).aestronglyMeasurable measurableSet_uIoc
  · refine eventually_of_mem hs fun x hx => Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := uIoc_zero_one_subset ht
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht'.1]
    rw [← one_mul M]
    refine mul_le_mul (pow_le_one₀ ht'.1 ht'.2) ?_ (abs_nonneg _) zero_le_one
    exact hM _ (Metric.closedBall_subset_closedBall (Metric.mem_ball.1 hx).le
      (segment_mem_closedBall ht'))
  · refine Eventually.of_forall fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := uIoc_zero_one_subset ht
    have hy : (b - a) * t + a ∈ Metric.ball a r :=
      Metric.closedBall_subset_ball (Metric.mem_ball.1 hb) (segment_mem_closedBall ht')
    have hg : ContinuousAt (iteratedDeriv (k + 1) f) ((b - a) * t + a) :=
      (hf.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball hk).continuousAt
        (Metric.isOpen_ball.mem_nhds hy)
    exact continuousAt_const.mul (hg.comp (f := fun x : ℝ => (x - a) * t + a) (by fun_prop))

/-- The integral representation `dslope f a b = ∫₀¹ f'(a + t (b - a)) dt` on the ball. -/
private theorem dslopeDeriv_zero {r : ℝ} {N : ℕ} (hf : ContDiffOn ℝ N f (Metric.ball a r))
    (hN : 1 ≤ N) {b : ℝ} (hb : b ∈ Metric.ball a r) : dslopeDeriv f a 0 b = dslope f a b := by
  simp only [dslopeDeriv, pow_zero, one_mul, zero_add, iteratedDeriv_one]
  rcases eq_or_ne b a with rfl | hba
  · simp
  · have hne : b - a ≠ 0 := sub_ne_zero.2 hba
    rw [intervalIntegral.integral_comp_mul_add (fun x => deriv f x) hne a]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul]
    have hsub : uIcc a b ⊆ Metric.ball a r := fun x hx => by
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_le_of_lt (abs_sub_left_of_mem_uIcc hx) (by simpa [Real.dist_eq] using hb)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := f) (fun x hx => ?_)
      (((hf.continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball hN).mono hsub).congr
        (fun x _ => (iteratedDeriv_one (f := f)).symm ▸ rfl)).intervalIntegrable,
      dslope_of_ne _ hba, slope_def_field, div_eq_inv_mul]
    simpa using hf.hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball (j := 0) hN (hsub hx)

/-- The value at the base point: `dslopeDeriv f a k a = f^{(k+1)}(a) / (k + 1)`. -/
private theorem dslopeDeriv_same (f : ℝ → ℝ) (a : ℝ) (k : ℕ) :
    dslopeDeriv f a k a = iteratedDeriv (k + 1) f a / (k + 1) := by
  simp [dslopeDeriv, integral_pow, div_eq_inv_mul]

/-- The two conclusions of Hadamard's lemma on a ball where `f` is `C^{n+1}`. -/
private theorem contDiffOn_dslope_ball {r : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Metric.ball a r)) :
    ContDiffOn ℝ n (dslope f a) (Metric.ball a r) ∧
      ∀ k ≤ n, Set.EqOn (iteratedDeriv k (dslope f a)) (dslopeDeriv f a k) (Metric.ball a r) := by
  obtain ⟨h1, h2⟩ := contDiffOn_of_hasDerivAt_chain (G := dslopeDeriv f a) Metric.isOpen_ball
    (fun k hk b hb => hasDerivAt_dslopeDeriv hf (by omega) hb)
    (continuousOn_dslopeDeriv hf le_rfl)
  have h0 : Set.EqOn (dslope f a) (dslopeDeriv f a 0) (Metric.ball a r) := fun b hb =>
    (dslopeDeriv_zero hf (by omega) hb).symm
  refine ⟨h1.congr h0, fun k hk b hb => ?_⟩
  rw [← iteratedDerivWithin_of_isOpen Metric.isOpen_ball hb, iteratedDerivWithin_congr h0 hb,
    iteratedDerivWithin_of_isOpen Metric.isOpen_ball hb]
  exact h2 k hk hb

/-- **Hadamard's lemma** in one variable: if `f` is `C^{n+1}` at `a`, the difference quotient
`dslope f a` (which is `(f x - f a) / (x - a)` off `a` and `f'(a)` at `a`) is `C^n` at `a`. -/
theorem ContDiffAt.dslope_same {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f a) :
    ContDiffAt ℝ n (dslope f a) a := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact (contDiffOn_dslope_ball (hfu.mono hru)).1.contDiffAt (Metric.ball_mem_nhds a hr)

/-- The `n`-th derivative of `dslope f a` at the base point is `f^{(n+1)}(a) / (n + 1)`. -/
theorem iteratedDeriv_dslope_same {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f a) :
    iteratedDeriv n (dslope f a) a = iteratedDeriv (n + 1) f a / (n + 1) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  rw [(contDiffOn_dslope_ball (hfu.mono hru)).2 n le_rfl (Metric.mem_ball_self hr),
    dslopeDeriv_same]

/-- The `m`-fold iterate of `dslope` at `a` is `C^n` at `a` when `f` is `C^{m+n}` there. -/
theorem ContDiffAt.iterate_dslope_same {m n : ℕ} (hf : ContDiffAt ℝ (m + n : ℕ) f a) :
    ContDiffAt ℝ n ((Function.swap dslope a)^[m] f) a := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (f := dslope f a)
      (ContDiffAt.dslope_same (n := m + n) (by rwa [show m + n + 1 = m + 1 + n by omega]))

/-- The `n`-th derivative of the `m`-fold iterate of `dslope` at `a`:
`n! / (m + n)! · f^{(m+n)}(a)`. -/
theorem iteratedDeriv_iterate_dslope_same {m n : ℕ} (hf : ContDiffAt ℝ (m + n : ℕ) f a) :
    iteratedDeriv n ((Function.swap dslope a)^[m] f) a =
      (n ! : ℝ) / (m + n)! * iteratedDeriv (m + n) f a := by
  induction m generalizing f with
  | zero => simp [Nat.factorial_ne_zero]
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hf' : ContDiffAt ℝ (m + n + 1 : ℕ) f a := by
      rwa [show m + n + 1 = m + 1 + n by omega]
    rw [ih (f := dslope f a) (hf'.dslope_same), iteratedDeriv_dslope_same hf',
      show m + 1 + n = m + n + 1 by omega, Nat.factorial_succ]
    push_cast
    field_simp

/-- The value of the `m`-fold iterate of `dslope` at the base point: `f^{(m)}(a) / m!`. -/
theorem iterate_dslope_same_apply {m : ℕ} (hf : ContDiffAt ℝ m f a) :
    (Function.swap dslope a)^[m] f a = iteratedDeriv m f a / m ! := by
  have := iteratedDeriv_iterate_dslope_same (m := m) (n := 0) (by simpa using hf)
  simpa [div_eq_inv_mul] using this

end Hadamard

section Multiplicity

variable {f : ℝ → ℝ} {α : ℝ} {m : ℕ}

/-- `α` is a root of `f` of multiplicity `m`: the derivatives `f^{(i)}(α)`, `i < m`, vanish and
`f^{(m)}(α) ≠ 0` ([quarteroni2000numerical] §6.1; [isaacson1994analysis] §3.2). `m = 1` is a
simple root (`f α = 0`, `f'(α) ≠ 0`); `m = 0` says `f α ≠ 0`. The smoothness `ContDiffAt ℝ n f α`,
`n ≥ m`, that makes the derivatives meaningful accompanies the predicate in every theorem, as
Mathlib does with `iteratedDeriv`. -/
def IsRootOfMultiplicity (f : ℝ → ℝ) (α : ℝ) (m : ℕ) : Prop :=
  (∀ i < m, iteratedDeriv i f α = 0) ∧ iteratedDeriv m f α ≠ 0

/-- A root of positive multiplicity is a root. -/
theorem IsRootOfMultiplicity.eq_zero (hα : IsRootOfMultiplicity f α m) (hm : 1 ≤ m) :
    f α = 0 := by
  simpa using hα.1 0 hm

/-- Multiplicity `1` is a simple root: `f α = 0` and `f'(α) ≠ 0`. -/
theorem isRootOfMultiplicity_one_iff :
    IsRootOfMultiplicity f α 1 ↔ f α = 0 ∧ deriv f α ≠ 0 := by
  simp [IsRootOfMultiplicity]

/-- The derivative of a function with a root of multiplicity `m + 1` at `α` has a root of
multiplicity `m` there. -/
theorem IsRootOfMultiplicity.deriv (hα : IsRootOfMultiplicity f α (m + 1)) :
    IsRootOfMultiplicity (deriv f) α m := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← iteratedDeriv_succ']
    exact hα.1 (i + 1) (by omega)
  · rw [← iteratedDeriv_succ']
    exact hα.2

/-- **Taylor factorization at a multiple root.** If `f` is `C^{m+n}` at `α` and `α` is a root of
multiplicity `m`, then `f x = (x - α)^m h x` for *all* `x`, where `h` is `C^n` at `α` with
`h α = f^{(m)}(α) / m!` (so `h α ≠ 0`). The factor is the `m`-fold iterate of `dslope` at `α`, i.e.
`f x / (x - α)^m` away from `α`; its regularity is Hadamard's lemma `ContDiffAt.dslope_same`
applied `m` times. The book's Exercise 6.2 ([quarteroni2000numerical]) takes this factorization as
its hint. -/
theorem IsRootOfMultiplicity.exists_eq_pow_mul {n : ℕ} (hf : ContDiffAt ℝ (m + n : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ n h α ∧ h α = iteratedDeriv m f α / m ! ∧
      ∀ x, f x = (x - α) ^ m * h x := by
  refine ⟨(Function.swap dslope α)^[m] f, hf.iterate_dslope_same,
    iterate_dslope_same_apply (hf.of_le (by exact_mod_cast Nat.le_add_right m n)), fun x => ?_⟩
  rw [← smul_eq_mul, pow_sub_smul_iterate_dslope_of_zero m fun k hk => ?_]
  rw [iterate_dslope_same_apply (hf.of_le (by exact_mod_cast (by omega : k ≤ m + n))),
    hα.1 k hk, zero_div]

/-- **The `C¹` Taylor factorization with the derivative of the factor**: if `f` is `C^{m+1}` at
`α` and `α` is a root of multiplicity `m`, then `f x = (x - α)^m h x` for all `x` with `h` `C¹` at
`α`, `h α = f^{(m)}(α) / m!` and `h'(α) = f^{(m+1)}(α) / (m + 1)!`. This is what the multiple-root
analysis of Newton's method consumes (`Numlib/Nonlinear/ScalarNewton`). -/
theorem IsRootOfMultiplicity.exists_eq_pow_mul_deriv (hf : ContDiffAt ℝ (m + 1 : ℕ) f α)
    (hα : IsRootOfMultiplicity f α m) :
    ∃ h : ℝ → ℝ, ContDiffAt ℝ 1 h α ∧ h α = iteratedDeriv m f α / m ! ∧
      _root_.deriv h α = iteratedDeriv (m + 1) f α / (m + 1)! ∧ ∀ x, f x = (x - α) ^ m * h x := by
  refine ⟨(Function.swap dslope α)^[m] f, hf.iterate_dslope_same,
    iterate_dslope_same_apply (hf.of_le (by exact_mod_cast Nat.le_succ m)), ?_, fun x => ?_⟩
  · rw [← iteratedDeriv_one, iteratedDeriv_iterate_dslope_same hf, Nat.factorial_one,
      Nat.cast_one, one_div, inv_mul_eq_div]
  · rw [← smul_eq_mul, pow_sub_smul_iterate_dslope_of_zero m fun k hk => ?_]
    rw [iterate_dslope_same_apply (hf.of_le (by exact_mod_cast (by omega : k ≤ m + 1))),
      hα.1 k hk, zero_div]

/-- The value `h α = f^{(m)}(α) / m!` of the factor is nonzero. -/
theorem IsRootOfMultiplicity.iteratedDeriv_div_factorial_ne_zero
    (hα : IsRootOfMultiplicity f α m) : iteratedDeriv m f α / m ! ≠ 0 :=
  div_ne_zero hα.2 (by exact_mod_cast Nat.factorial_ne_zero m)

/-- Near a root of multiplicity `m` (any `m`, including `0`), `f` does not vanish away from `α`. -/
theorem IsRootOfMultiplicity.eventually_ne_zero (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) : ∀ᶠ x in 𝓝[≠] α, f x ≠ 0 := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 0) (by simpa using hf)
  have hne : ∀ᶠ x in 𝓝 α, h x ≠ 0 :=
    hh.continuousAt.eventually_ne (hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero)
  filter_upwards [nhdsWithin_le_nhds hne, self_mem_nhdsWithin] with x hx hxα
  rw [hfh x]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hxα)) hx

/-- **Error versus residual at a root of multiplicity `m`**, the rigorous content of
[quarteroni2000numerical] (6.4) and (6.6): as `x → α`,
`|x - α| / |f x|^{1/m} → (m! / |f^{(m)}(α)|)^{1/m}`. For `m = 1` this is
`|x - α| / |f x| → 1 / |f'(α)|`, the statement behind `K_abs ≃ 1 / |f'(α)|` in (6.3) and the
residual stopping test of §6.5. -/
theorem IsRootOfMultiplicity.tendsto_abs_sub_div_abs_rpow (hm : 1 ≤ m) (hf : ContDiffAt ℝ m f α)
    (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => |x - α| / |f x| ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((m ! / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)))) := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 0) (by simpa using hf)
  have hc : (1 / |h α|) = m ! / |iteratedDeriv m f α| := by
    rw [hhα, abs_div, Nat.abs_cast, one_div_div]
  rw [← hc]
  have hlim : Tendsto (fun x => (1 / |h x|) ^ (1 / (m : ℝ))) (𝓝[≠] α)
      (𝓝 ((1 / |h α|) ^ (1 / (m : ℝ)))) := by
    refine Tendsto.rpow_const ?_ (Or.inr (by positivity))
    exact (tendsto_const_nhds.div (hh.continuousAt.abs.tendsto.mono_left nhdsWithin_le_nhds)
      (abs_ne_zero.2 (hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero)))
  refine hlim.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hxα : |x - α| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hx)
  change _ = |x - α| / |f x| ^ (1 / (m : ℝ))
  rw [hfh x, abs_mul, abs_pow, Real.mul_rpow (pow_nonneg (abs_nonneg _) _) (abs_nonneg _),
    one_div (m : ℝ), Real.pow_rpow_inv_natCast (abs_nonneg _) (by omega),
    div_mul_cancel_left₀ hxα, one_div, Real.inv_rpow (abs_nonneg _)]

/-- **The residual bound** [quarteroni2000numerical] (6.5)/(6.6) as an inequality: for every
constant `c` above the asymptotic one, `|x - α| ≤ c |f x|^{1/m}` for all `x` near `α`. The book's
`≲` is exactly this reading. For `m = 1`: `∀ c > 1 / |f'(α)|, |x - α| ≤ c |f x|` near `α`. -/
theorem IsRootOfMultiplicity.eventually_abs_sub_le_mul_abs_rpow (hm : 1 ≤ m)
    (hf : ContDiffAt ℝ m f α) (hα : IsRootOfMultiplicity f α m) {c : ℝ}
    (hc : (m ! / |iteratedDeriv m f α|) ^ (1 / (m : ℝ)) < c) :
    ∀ᶠ x in 𝓝 α, |x - α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
  have h1 : ∀ᶠ x in 𝓝[≠] α, |x - α| ≤ c * |f x| ^ (1 / (m : ℝ)) := by
    filter_upwards [(hα.tendsto_abs_sub_div_abs_rpow hm hf).eventually_lt_const hc,
      hα.eventually_ne_zero hf] with x hx hfx
    have hpos : 0 < |f x| ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos (abs_pos.2 hfx) _
    exact (div_le_iff₀ hpos).1 hx.le
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with x hx
  by_cases hxα : x = α
  · subst hxα
    have hm0 : ((m : ℝ)⁻¹) ≠ 0 := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      positivity
    simp [hα.eq_zero hm, Real.zero_rpow hm0]
  · exact hx hxα

end Multiplicity

namespace Polynomial

/-- The iterated derivative of a polynomial function is the function of the iterated
`derivative`. -/
theorem iteratedDeriv_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    ext x
    exact Polynomial.deriv _

/-- For a nonzero real polynomial, `IsRootOfMultiplicity` of its evaluation map is Mathlib's
`Polynomial.rootMultiplicity`. This lets [quarteroni2000numerical] (6.7) speak of the multiplicity
of a polynomial root in Mathlib's vocabulary. -/
theorem isRootOfMultiplicity_eval_iff {p : ℝ[X]} (hp : p ≠ 0) {α : ℝ} {m : ℕ} :
    IsRootOfMultiplicity (fun x => p.eval x) α m ↔ p.rootMultiplicity α = m := by
  simp only [IsRootOfMultiplicity, iteratedDeriv_eval]
  have hlt : ∀ n, n < p.rootMultiplicity α ↔ ∀ i ≤ n, (derivative^[i] p).eval α = 0 :=
    fun n => lt_rootMultiplicity_iff_isRoot_iterate_derivative hp
  constructor
  · rintro ⟨hz, hnz⟩
    refine le_antisymm ?_ ?_
    · by_contra hlt'
      exact hnz ((hlt m).1 (lt_of_not_ge hlt') m le_rfl)
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Nat.zero_le _
      · have := (hlt (m - 1)).2 (fun i hi => hz i (by omega))
        omega
  · intro hm
    refine ⟨fun i hi => (hlt i).1 (hm ▸ hi) i le_rfl, ?_⟩
    rw [← hm, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
      (eval_divByMonic_pow_rootMultiplicity_ne_zero α hp)

end Polynomial
