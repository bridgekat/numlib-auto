import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor expansions with explicit remainder bounds

Taylor's theorem in the forms the numerical estimates of this library need: not the asymptotic
`IsLittleO` statement, but an inequality with a named constant, valid on a named set, and written
with the *two-sided* derivatives `iteratedDeriv` rather than with `iteratedDerivWithin`.

## Scalar expansions

For `f : ℝ → ℝ` the remainder comes from Mathlib's `taylor_mean_remainder_lagrange`, whose
intermediate point lies in the *open* interval; that is what lets
`exists_taylorWithinEval_add_iteratedDeriv_mul` state the remainder with `iteratedDeriv` and
`taylorWithinEval_eq_sum_of_contDiffAt` rewrite the Taylor polynomial as
`∑_{k ≤ n} (x - x₀)^k / k! f^{(k)}(x₀)`. The uniform bound is stated on an *open ball*
(`abs_sub_sum_taylor_le`): `iteratedDeriv` is determined by `f` only on an open set, so a
`ContDiffOn` hypothesis over a closed interval does not determine the coefficients of the
expansion, and a `uIcc` formulation of the primitive would not do. For a function that is `C^{n+1}`
on all of `ℝ` the ball disappears (`abs_sub_sum_taylor_le_of_contDiff`), and `abs_taylor_one`,
`abs_taylor_two`, `abs_taylor_three` are its first three orders written out.

## Expansions of a curve in a normed space

For a curve `y : ℝ → E` the hypotheses are a chain of *derivative functions* rather than a
`ContDiffOn` hypothesis: `HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s` for `k ≤ n`. This is
what the truncation errors of one-step methods and the order conditions of Runge–Kutta methods
have to hand, and it avoids `iteratedDerivWithin` at the endpoints entirely. The general bound is
`norm_sub_sum_smul_le`, which expands at an arbitrary point `c` of the interval and evaluates at
an arbitrary `x` on either side of it; forwards it is `norm_sub_sum_smul_le_of_le`, proved by
induction on the order from `image_norm_le_of_norm_deriv_right_le_deriv_boundary`, and backwards it
is the forward case for the reflected tower. Expanding at the left endpoint gives
`norm_sub_taylorSum_le`, of which `norm_sub_sub_smul_le_mul_sq_div_two` (`n = 1`) and
`norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six` (`n = 2`) are the low-order cases,
`norm_sub_sub_smul_le_mul_sq_div_two'` is the second-order bound expanded at the right endpoint,
and `norm_sub_sub_smul_add_le_mul_pow_three_div_twelve` is the Peano-kernel bound of the
trapezoidal rule, obtained without integrals.

Along a segment of a normed space the same bounds are read off the curve `s ↦ G (p + s • w)`,
whose `k`-th derivative is the `k`-th Fréchet derivative of `G` applied to `w` that many times:
`norm_sub_sub_smul_apply_le_of_hasFDerivAt` at order two and `norm_sub_taylor_segment_le` at
order four.

These are all Mathlib-shaped statements; the module is an upstreaming candidate whose natural home
is `Mathlib.Analysis.Calculus.Taylor`.
-/

open Set Topology
open Finset (range)
open scoped Nat

/-! ### Scalar expansions with two-sided iterated derivatives -/

section Scalar

variable {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ}

/-- Taylor's theorem with the Lagrange remainder, the derivative in the remainder being the
two-sided `iteratedDeriv` (the intermediate point is interior to the interval). -/
theorem exists_taylorWithinEval_add_iteratedDeriv_mul (hne : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) :
    ∃ ξ ∈ uIoo x₀ x, f x = taylorWithinEval f n (uIcc x₀ x) x₀ x
      + iteratedDeriv (n + 1) f ξ * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hs : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc hne
  have hsub : uIoo x₀ x ⊆ uIcc x₀ x := Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange hne (hf.of_le (by exact_mod_cast n.le_succ))
    ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast n.lt_succ_self) hs).mono hsub)
  refine ⟨ξ, hξ, ?_⟩
  have hξ' : uIcc x₀ x ∈ 𝓝 ξ := mem_nhds_iff.2 ⟨uIoo x₀ x, hsub, isOpen_Ioo, hξ⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt hξ') (hsub hξ)] at h
  linarith

/-- The Taylor polynomial of `f` at an interior point `x₀` of a set on which `f` is `C^n`, written
with the two-sided iterated derivatives. -/
theorem taylorWithinEval_eq_sum_of_contDiffAt (hne : x₀ ≠ x) (hf : ContDiffAt ℝ n f x₀) :
    taylorWithinEval f n (uIcc x₀ x) x₀ x
      = ∑ k ∈ range (n + 1), (x - x₀) ^ k / k ! * iteratedDeriv k f x₀ := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
    (hf.of_le (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) left_mem_uIcc,
    smul_eq_mul]
  ring

/-- **Taylor's theorem with a uniform remainder bound between two points**: if `f` is `C^{n+1}` on
the closed interval between `x₀` and `x`, is `C^n` near `x₀`, and its `(n+1)`-st derivative is
bounded by `M` on that interval, then
`|f x - ∑_{k ≤ n} (x - x₀)^k / k! f^{(k)}(x₀)| ≤ M |x - x₀|^{n+1} / (n + 1)!`.

The hypothesis `ContDiffAt ℝ n f x₀` is not implied by the `ContDiffOn` one and cannot be dropped:
the coefficients of the expansion are the *two-sided* `iteratedDeriv`, which smoothness on a closed
interval does not determine at an endpoint of it. The two forms below supply it in the two ways
that occur in practice — from an open set around `x₀`, and from smoothness on all of `ℝ`. -/
theorem abs_sub_sum_taylor_le_of_contDiffOn {M : ℝ}
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) (hx₀ : ContDiffAt ℝ n f x₀)
    (hM : ∀ t ∈ uIcc x₀ x, |iteratedDeriv (n + 1) f t| ≤ M) :
    |f x - ∑ k ∈ range (n + 1), (x - x₀) ^ k / k ! * iteratedDeriv k f x₀|
      ≤ M * |x - x₀| ^ (n + 1) / (n + 1)! := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ left_mem_uIcc)
  rcases eq_or_ne x₀ x with rfl | hne
  · rw [Finset.sum_range_succ', sub_self]
    simp
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hne hf
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne hx₀] at hT
  rw [hT, add_sub_cancel_left, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hM ξ (Ioo_subset_Icc_self hξ)

/-- **Taylor's theorem with a uniform remainder bound on a ball**: if `f` is `C^{n+1}` on
`ball x ε` with `|f^{(n+1)}| ≤ M` there, then for every `y` in the ball
`|f y - ∑_{k ≤ n} (y - x)^k / k! f^{(k)}(x)| ≤ M |y - x|^{n+1} / (n + 1)!`. -/
theorem abs_sub_sum_taylor_le {ε M : ℝ} (hf : ContDiffOn ℝ (n + 1) f (Metric.ball x₀ ε))
    (hM : ∀ t ∈ Metric.ball x₀ ε, |iteratedDeriv (n + 1) f t| ≤ M) {y : ℝ}
    (hy : y ∈ Metric.ball x₀ ε) :
    |f y - ∑ k ∈ range (n + 1), (y - x₀) ^ k / k ! * iteratedDeriv k f x₀|
      ≤ M * |y - x₀| ^ (n + 1) / (n + 1)! := by
  have hx₀ : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self (Metric.pos_of_mem_ball hy)
  have hsub : uIcc x₀ y ⊆ Metric.ball x₀ ε := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_sub_left_of_mem_uIcc ht).trans_lt (by rwa [Metric.mem_ball, Real.dist_eq] at hy)
  exact abs_sub_sum_taylor_le_of_contDiffOn (hf.mono hsub)
    ((hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx₀)).of_le (by exact_mod_cast n.le_succ))
    fun t ht => hM t (hsub ht)

/-- **Taylor's theorem with a uniform remainder bound on a convex set**: if `f` is `C^{n+1}` on all
of `ℝ` and `|f^{(n+1)}| ≤ M` on a convex set `s`, then the `n`-th Taylor polynomial of `f` at
`x₀ ∈ s` approximates `f` at `x ∈ s` to within `M |x - x₀|^{n+1} / (n + 1)!`. The set need not be
open here, unlike in `abs_sub_sum_taylor_le`: the iterated derivatives come from the global
smoothness, and only the bound is local. -/
theorem abs_sub_sum_taylor_le_of_convex {s : Set ℝ} {M : ℝ} (hs : Convex ℝ s)
    (hf : ContDiff ℝ (n + 1) f) (hx₀ : x₀ ∈ s) (hx : x ∈ s)
    (hM : ∀ t ∈ s, |iteratedDeriv (n + 1) f t| ≤ M) :
    |f x - ∑ k ∈ range (n + 1), (x - x₀) ^ k / k ! * iteratedDeriv k f x₀|
      ≤ M * |x - x₀| ^ (n + 1) / (n + 1)! :=
  abs_sub_sum_taylor_le_of_contDiffOn (hf.contDiffOn.mono (hs.ordConnected.uIcc_subset hx₀ hx))
    (hf.contDiffAt.of_le (by exact_mod_cast n.le_succ))
    fun t ht => hM t (hs.ordConnected.uIcc_subset hx₀ hx ht)

/-- **Taylor's theorem with a uniform remainder bound on the whole line**: for `g` of class
`C^{n+1}` with `|g^{(n+1)}| ≤ M` everywhere,
`|g (ξ + h) - ∑_{k ≤ n} h^k/k! g^{(k)}(ξ)| ≤ M |h|^{n+1}/(n+1)!`. -/
theorem abs_sub_sum_taylor_le_of_contDiff {g : ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hg : ContDiff ℝ (n + 1) g) (hM : ∀ y, |iteratedDeriv (n + 1) g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - ∑ k ∈ Finset.range (n + 1), h ^ k / k ! * iteratedDeriv k g ξ|
      ≤ M * |h| ^ (n + 1) / (n + 1)! := by
  have hmem : ξ + h ∈ Metric.ball ξ (|h| + 1) := by
    have hd : dist (ξ + h) ξ = |h| := by rw [Real.dist_eq]; ring_nf
    rw [Metric.mem_ball, hd]
    linarith
  have h1 := abs_sub_sum_taylor_le (f := g) (x₀ := ξ) (n := n) (ε := |h| + 1)
    hg.contDiffOn (fun t _ => hM t) hmem
  simpa using h1

/-- **First-order Taylor**: `|g (ξ + h) - g ξ - h g'(ξ)| ≤ M h²/2` for `|g''| ≤ M`. -/
theorem abs_taylor_one {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 2 g)
    (hM : ∀ y, |iteratedDeriv 2 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ| ≤ M * h ^ 2 / 2 := by
  have hg' : ContDiff ℝ ((1 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((1 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((1 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ| ≤ M * |h| ^ ((1 : ℕ) + 1) / ((1 : ℕ) + 1)! := h1
    _ = M * h ^ 2 / 2 := by norm_num [sq_abs]

/-- **Second-order Taylor**: `|g (ξ + h) - g ξ - h g' - h²/2 g''| ≤ M |h|³/6` for `|g'''| ≤ M`. -/
theorem abs_taylor_two {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 3 g)
    (hM : ∀ y, |iteratedDeriv 3 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ| ≤ M * |h| ^ 3 / 6 := by
  have hg' : ContDiff ℝ ((2 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((2 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((2 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ + h ^ 2 / 2 * iteratedDeriv 2 g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero,
      iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum, ← sub_sub, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ|
      ≤ M * |h| ^ ((2 : ℕ) + 1) / ((2 : ℕ) + 1)! := h1
    _ = M * |h| ^ 3 / 6 := by norm_num

/-- **Third-order Taylor**: `|g (ξ + h) - g ξ - h g' - h²/2 g'' - h³/6 g'''| ≤ M h⁴/24` for a
fourth derivative bounded by `M`. -/
theorem abs_taylor_three {g : ℝ → ℝ} {M : ℝ} (hg : ContDiff ℝ 4 g)
    (hM : ∀ y, |iteratedDeriv 4 g y| ≤ M) (ξ h : ℝ) :
    |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ
      - h ^ 3 / 6 * iteratedDeriv 3 g ξ| ≤ M * h ^ 4 / 24 := by
  have hg' : ContDiff ℝ ((3 : ℕ) + 1) g := by norm_num; exact hg
  have hM' : ∀ y, |iteratedDeriv ((3 : ℕ) + 1) g y| ≤ M := by norm_num; exact hM
  have h1 := abs_sub_sum_taylor_le_of_contDiff hg' hM' ξ h
  have hsum : ∑ k ∈ Finset.range ((3 : ℕ) + 1), h ^ k / k ! * iteratedDeriv k g ξ
      = g ξ + h * deriv g ξ + h ^ 2 / 2 * iteratedDeriv 2 g ξ
        + h ^ 3 / 6 * iteratedDeriv 3 g ξ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
    try ring
  rw [hsum, ← sub_sub, ← sub_sub, ← sub_sub] at h1
  calc |g (ξ + h) - g ξ - h * deriv g ξ - h ^ 2 / 2 * iteratedDeriv 2 g ξ
        - h ^ 3 / 6 * iteratedDeriv 3 g ξ|
      ≤ M * |h| ^ ((3 : ℕ) + 1) / ((3 : ℕ) + 1)! := h1
    _ = M * h ^ 4 / 24 := by
        rw [show |h| ^ ((3 : ℕ) + 1) = h ^ 4 by
          rw [show (3 : ℕ) + 1 = 4 from rfl, ← abs_pow,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 4)]]
        norm_num

end Scalar

/-! ### Expansions of a curve given by a chain of derivative functions -/

section Curve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b M : ℝ} {y y' y'' y''' : ℝ → E}

/-- Reflecting a curve with derivative `y'` on `Icc a b` through the midpoint gives a curve with
derivative `-y' (a + b - s)` on `Icc a b`. -/
theorem hasDerivWithinAt_comp_const_sub_Icc
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt (fun s => y (a + b - s)) (-y' (a + b - s)) (Icc a b) s := by
  have hmem : a + b - s ∈ Icc a b := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : HasDerivWithinAt (fun s : ℝ => a + b - s) (-1) (Icc a b) s :=
    (hasDerivWithinAt_id s (Icc a b)).const_sub (a + b)
  have hmaps : MapsTo (fun s : ℝ => a + b - s) (Icc a b) (Icc a b) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have := (hy _ hmem).scomp s h1 hmaps
  simpa [Function.comp_def, neg_one_smul] using this

/-! #### The expansion at an arbitrary point of the interval

The Taylor remainder bound for a tower of derivative functions `y 0, y 1, …, y n` with
`HasDerivWithinAt (y m) (y (m+1) s) (Icc a b) s`, at an arbitrary expansion point `c ∈ [a, b]`
and evaluation point `x ∈ [a, b]` on either side of it. It extends the second- and third-order
bounds below and is proved the same way, by the comparison lemma
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` and induction on the order; the backward
case is the forward case for the reflected tower `s ↦ (-1)^m • y m (a + b - s)`. Mathlib's
`taylor_mean_remainder_bound` expands at the left endpoint of the interval only. -/

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b K : ℝ} {y : ℕ → ℝ → E}

/-- The Taylor bound in the forward direction: for a tower `y` of derivatives on `Icc a b` with
`‖y n‖ ≤ K` there, `‖y 0 b - ∑_{m < n} ((b - a)^m / m!) y m a‖ ≤ K (b - a)^n / n!`. -/
theorem norm_sub_sum_smul_le_of_le (hab : a ≤ b) (n : ℕ)
    (hy : ∀ m < n, ∀ s ∈ Icc a b, HasDerivWithinAt (y m) (y (m + 1) s) (Icc a b) s)
    (hK : ∀ s ∈ Icc a b, ‖y n s‖ ≤ K) :
    ‖y 0 b - ∑ m ∈ range n, ((b - a) ^ m / m.factorial) • y m a‖ ≤
      K * (b - a) ^ n / n.factorial := by
  induction n generalizing y b with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one,
      Nat.factorial_zero, Nat.cast_one, div_one]
    exact hK b (right_mem_Icc.2 hab)
  | succ n ih =>
    -- the residual and its derivative
    set g : ℝ → E := fun s => y 0 s - ∑ m ∈ range (n + 1), ((s - a) ^ m / m.factorial) • y m a
    have hg : ∀ s ∈ Icc a b, HasDerivWithinAt g
        (y 1 s - ∑ m ∈ range n, ((s - a) ^ m / m.factorial) • y (m + 1) a) (Icc a b) s := by
      intro s hs
      have h1 : HasDerivWithinAt (fun s => ∑ m ∈ range (n + 1), ((s - a) ^ m / m.factorial) • y m a)
          (∑ m ∈ range n, ((s - a) ^ m / m.factorial) • y (m + 1) a) (Icc a b) s := by
        have e : (fun s => ∑ m ∈ range (n + 1), ((s - a) ^ m / m.factorial) • y m a) =
            fun s => (∑ m ∈ range n, ((s - a) ^ (m + 1) / (m + 1).factorial) • y (m + 1) a) +
              ((s - a) ^ 0 / (0 : ℕ).factorial) • y 0 a := by
          funext s
          rw [Finset.sum_range_succ']
        rw [e]
        have h0 : HasDerivWithinAt (fun s : ℝ => ((s - a) ^ 0 / (0 : ℕ).factorial) • y 0 a) 0
            (Icc a b) s := by
          simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
          exact hasDerivWithinAt_const _ _ _
        have hsum : HasDerivWithinAt
            (fun s => ∑ m ∈ range n, ((s - a) ^ (m + 1) / (m + 1).factorial) • y (m + 1) a)
            (∑ m ∈ range n, ((s - a) ^ m / m.factorial) • y (m + 1) a) (Icc a b) s := by
          refine HasDerivWithinAt.fun_sum
            (A := fun m s => ((s - a) ^ (m + 1) / (m + 1).factorial) • y (m + 1) a)
            (A' := fun m => ((s - a) ^ m / m.factorial) • y (m + 1) a) fun m _ => ?_
          have : HasDerivWithinAt (fun s : ℝ => (s - a) ^ (m + 1) / (m + 1).factorial)
              ((s - a) ^ m / m.factorial) (Icc a b) s := by
            have := (((hasDerivAt_id' s).hasDerivWithinAt (s := Icc a b)).sub_const a).pow (m + 1)
              |>.div_const ((m + 1).factorial : ℝ)
            refine this.congr_deriv ?_
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
            field_simp
          exact this.smul_const (y (m + 1) a)
        exact (hsum.add h0).congr_deriv (add_zero _)
      exact (hy 0 (Nat.succ_pos n) s hs).sub h1
    have hbound : ∀ s ∈ Icc a b,
        ‖y 1 s - ∑ m ∈ range n, ((s - a) ^ m / m.factorial) • y (m + 1) a‖ ≤
          K * (s - a) ^ n / n.factorial := by
      intro s hs
      have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
      exact ih (y := fun m => y (m + 1)) hs.1
        (fun m hm u hu => (hy (m + 1) (by omega) u (hsub hu)).mono hsub)
        (fun u hu => hK u (hsub hu))
    have hB : ∀ s, HasDerivAt (fun s => K * (s - a) ^ (n + 1) / (n + 1).factorial)
        (K * (s - a) ^ n / n.factorial) s := by
      intro s
      have := (((hasDerivAt_id' s).sub_const a).pow (n + 1)).const_mul K |>.div_const
        ((n + 1).factorial : ℝ)
      refine this.congr_deriv ?_
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f' := fun s => y 1 s - ∑ m ∈ range n, ((s - a) ^ m / m.factorial) • y (m + 1) a)
      (HasDerivWithinAt.continuousOn hg)
      (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (B := fun s => K * (s - a) ^ (n + 1) / (n + 1).factorial)
      (B' := fun s => K * (s - a) ^ n / n.factorial) (by simp [g, Finset.sum_range_succ', pow_succ])
      hB
      (fun s hs => hbound s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
    simpa [g] using key

/-- The reflected tower `s ↦ (-1)^m • y m (a + b - s)` is a tower of derivatives on `Icc a b`. -/
theorem hasDerivWithinAt_reflect (m : ℕ)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt (y m) (y (m + 1) s) (Icc a b) s) {s : ℝ}
    (hs : s ∈ Icc a b) :
    HasDerivWithinAt (fun s => ((-1 : ℝ) ^ m) • y m (a + b - s))
      (((-1 : ℝ) ^ (m + 1)) • y (m + 1) (a + b - s)) (Icc a b) s := by
  have := (hasDerivWithinAt_comp_const_sub_Icc hy hs).const_smul ((-1 : ℝ) ^ m)
  refine this.congr_deriv ?_
  rw [pow_succ, smul_neg, mul_neg_one, neg_smul]

/-- **The Taylor bound at an arbitrary expansion point**: for a tower `y` of derivatives on
`Icc a b` with `‖y n‖ ≤ K` there, and `c, x ∈ Icc a b`,
`‖y 0 x - ∑_{m < n} ((x - c)^m / m!) y m c‖ ≤ K |x - c|^n / n!`. With `n = 0` it reads
`‖y 0 x‖ ≤ K`, with `n = 1` it is the mean value inequality. -/
theorem norm_sub_sum_smul_le (n : ℕ)
    (hy : ∀ m < n, ∀ s ∈ Icc a b, HasDerivWithinAt (y m) (y (m + 1) s) (Icc a b) s)
    (hK : ∀ s ∈ Icc a b, ‖y n s‖ ≤ K) {c x : ℝ} (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    ‖y 0 x - ∑ m ∈ range n, ((x - c) ^ m / m.factorial) • y m c‖ ≤
      K * |x - c| ^ n / n.factorial := by
  rcases le_total c x with hcx | hxc
  · have hsub : Icc c x ⊆ Icc a b := Icc_subset_Icc hc.1 hx.2
    have := norm_sub_sum_smul_le_of_le hcx n
      (fun m hm s hs => (hy m hm s (hsub hs)).mono hsub) (fun s hs => hK s (hsub hs))
    rwa [abs_of_nonneg (sub_nonneg.2 hcx)]
  · have hsub : Icc x c ⊆ Icc a b := Icc_subset_Icc hx.1 hc.2
    -- reflect through the midpoint of `[x, c]`
    have hy' : ∀ m < n, ∀ s ∈ Icc x c, HasDerivWithinAt (fun s => ((-1 : ℝ) ^ m) • y m (x + c - s))
        (((-1 : ℝ) ^ (m + 1)) • y (m + 1) (x + c - s)) (Icc x c) s := fun m hm s hs =>
      hasDerivWithinAt_reflect m (fun u hu => (hy m hm u (hsub hu)).mono hsub) hs
    have hK' : ∀ s ∈ Icc x c, ‖((-1 : ℝ) ^ n) • y n (x + c - s)‖ ≤ K := fun s hs => by
      rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hK _ (hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    have key := norm_sub_sum_smul_le_of_le (y := fun m s => ((-1 : ℝ) ^ m) • y m (x + c - s)) hxc n
      hy' hK'
    simp only [pow_zero, one_smul, add_sub_cancel_right, add_sub_cancel_left] at key
    rw [abs_of_nonpos (sub_nonpos.2 hxc), neg_sub]
    convert key using 3
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← neg_sub c x, neg_pow]
    congr 1
    ring

end Taylor

/-- **Taylor's theorem with a bound on the top derivative**, for a curve in a normed space over a
closed interval: if `Y 0, …, Y (n + 1)` is a chain of successive derivatives on `Icc a b` and
`‖Y (n + 1)‖ ≤ M` there, then `Y 0 b` differs from its Taylor polynomial at `a` by at most
`M (b - a)^{n+1} / (n+1)!`. This is `norm_sub_sum_smul_le_of_le` expanded at the left endpoint;
it subsumes `norm_sub_sub_smul_le_mul_sq_div_two` (`n = 1`) and
`norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six` (`n = 2`). -/
theorem norm_sub_taylorSum_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M a b : ℝ} {Y : ℕ → ℝ → X} {n : ℕ} (hab : a ≤ b)
    (hY : ∀ k ≤ n, ∀ s ∈ Icc a b, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖Y (n + 1) s‖ ≤ M) :
    ‖Y 0 b - ∑ k ∈ range (n + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a‖ ≤
      M * (b - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) :=
  norm_sub_sum_smul_le_of_le hab (n + 1) (fun m hm => hY m (by omega)) hM

/-- **Second-order Taylor bound, forward form**: if `y'` is the derivative of `y` and `y''` that
of `y'` on `Icc a b`, with `‖y''‖ ≤ M` there, then
`‖y b - y a - (b - a) • y' a‖ ≤ M (b - a)² / 2`. The case `n = 1` of
`norm_sub_taylorSum_le`. -/
theorem norm_sub_sub_smul_le_mul_sq_div_two (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y'' s‖ ≤ M) :
    ‖y b - y a - (b - a) • y' a‖ ≤ M * (b - a) ^ 2 / 2 := by
  obtain ⟨Y, e0, e1, e2⟩ : ∃ Y : ℕ → ℝ → E, Y 0 = y ∧ Y 1 = y' ∧ Y 2 = y'' :=
    ⟨fun k => match k with
      | 0 => y
      | 1 => y'
      | _ => y'', rfl, rfl, rfl⟩
  have hY : ∀ k ≤ 1, ∀ s ∈ Icc a b, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s := by
    intro k hk s hs
    rcases k with _ | _ | k
    · rw [e0, e1]; exact hy s hs
    · rw [e1, e2]; exact hy' s hs
    · omega
  have key := norm_sub_taylorSum_le (Y := Y) (n := 1) hab hY (by rw [e2]; exact hM)
  have hsum : ∑ k ∈ range (1 + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a
      = y a + (b - a) • y' a := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e0, e1]
    norm_num
  rw [e0, hsum] at key
  have he : y b - y a - (b - a) • y' a = y b - (y a + (b - a) • y' a) := by abel
  rw [he]
  refine key.trans (le_of_eq ?_)
  norm_num

/-- **Second-order Taylor bound, backward form**: under the hypotheses of
`norm_sub_sub_smul_le_mul_sq_div_two`, `‖y a - y b - (a - b) • y' b‖ ≤ M (b - a)² / 2`. -/
theorem norm_sub_sub_smul_le_mul_sq_div_two' (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y'' s‖ ≤ M) :
    ‖y a - y b - (a - b) • y' b‖ ≤ M * (b - a) ^ 2 / 2 := by
  have hy1 : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => y (a + b - s)) (-y' (a + b - s))
      (Icc a b) s := fun s hs => hasDerivWithinAt_comp_const_sub_Icc hy hs
  have hy2 : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => -y' (a + b - s)) (y'' (a + b - s))
      (Icc a b) s := fun s hs =>
    (hasDerivWithinAt_comp_const_sub_Icc hy' hs).neg.congr_deriv (neg_neg _)
  have hM2 : ∀ s ∈ Icc a b, ‖y'' (a + b - s)‖ ≤ M := fun s hs =>
    hM _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := norm_sub_sub_smul_le_mul_sq_div_two hab hy1 hy2 hM2
  simp only [add_sub_cancel_right, add_sub_cancel_left, smul_neg, ← neg_smul, neg_sub] at this
  exact this

/-- **Third-order Taylor bound for the trapezoidal rule**: if `y'`, `y''`, `y'''` are the
successive derivatives of `y` on `Icc a b` with `‖y'''‖ ≤ M` there, then
`‖y b - y a - ((b - a) / 2) • (y' a + y' b)‖ ≤ M (b - a)³ / 12`. This is the Peano-kernel
bound of the trapezoidal rule for `∫_a^b y' = y b - y a`, obtained here without integrals: the
residual `g s = y s - y a - ((s - a)/2) (y' a + y' s)` has derivative
`(1/2) (y' s - y' a - (s - a) y'' s)`, a backward second-order remainder of `y'` bounded by
`M (s - a)² / 4`, and the comparison with `M (s - a)³ / 12` concludes. -/
theorem norm_sub_sub_smul_add_le_mul_pow_three_div_twelve (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hy'' : ∀ s ∈ Icc a b, HasDerivWithinAt y'' (y''' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y''' s‖ ≤ M) :
    ‖y b - y a - ((b - a) / 2) • (y' a + y' b)‖ ≤ M * (b - a) ^ 3 / 12 := by
  have hg : ∀ s ∈ Icc a b, HasDerivWithinAt (fun s => y s - y a - ((s - a) / 2) • (y' a + y' s))
      ((1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s)) (Icc a b) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun s : ℝ => (s - a) / 2) (1 / 2) (Icc a b) s :=
      ((hasDerivWithinAt_id s (Icc a b)).sub_const a).div_const 2
    have := ((hy s hs).sub_const (y a)).sub (h1.smul ((hy' s hs).const_add (y' a)))
    refine this.congr_deriv ?_
    module
  have hbound : ∀ s ∈ Icc a b, ‖(1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s)‖ ≤
      M * (s - a) ^ 2 / 4 := by
    intro s hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
    have := norm_sub_sub_smul_le_mul_sq_div_two' (y := y') (y' := y'') (y'' := y''') hs.1
      (fun u hu => (hy' u (hsub hu)).mono hsub) (fun u hu => (hy'' u (hsub hu)).mono hsub)
      (fun u hu => hM u (hsub hu))
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have e : y' s - y' a - (s - a) • y'' s = -(y' a - y' s - (a - s) • y'' s) := by
      rw [← neg_sub s a, neg_smul]; abel
    rw [e, norm_neg]
    linarith
  have hB : ∀ s, HasDerivAt (fun s => M * (s - a) ^ 3 / 12) (M * (s - a) ^ 2 / 4) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s - a) ^ 3) (3 * (s - a) ^ 2) s := by
      have := (hasDerivAt_pow 3 (s - a)).comp s ((hasDerivAt_id s).sub_const a)
      simpa [Function.comp_def] using this
    exact ((h1.const_mul M).div_const 12).congr_deriv (by ring)
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f' := fun s => (1 / 2 : ℝ) • (y' s - y' a - (s - a) • y'' s))
    (HasDerivWithinAt.continuousOn hg)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs))
    (B := fun s => M * (s - a) ^ 3 / 12) (B' := fun s => M * (s - a) ^ 2 / 4) (by simp) hB
    (fun s hs => hbound s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
  simpa using key

/-- **Third-order Taylor bound**: if `y'`, `y''`, `y'''` are the successive derivatives of `y`
on `Icc a b` with `‖y'''‖ ≤ M` there, then
`‖y b - y a - (b - a) • y' a - ((b - a)² / 2) • y'' a‖ ≤ M (b - a)³ / 6`. The case `n = 2` of
`norm_sub_taylorSum_le`. -/
theorem norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hy'' : ∀ s ∈ Icc a b, HasDerivWithinAt y'' (y''' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y''' s‖ ≤ M) :
    ‖y b - y a - (b - a) • y' a - ((b - a) ^ 2 / 2) • y'' a‖ ≤ M * (b - a) ^ 3 / 6 := by
  obtain ⟨Y, e0, e1, e2, e3⟩ : ∃ Y : ℕ → ℝ → E, Y 0 = y ∧ Y 1 = y' ∧ Y 2 = y'' ∧ Y 3 = y''' :=
    ⟨fun k => match k with
      | 0 => y
      | 1 => y'
      | 2 => y''
      | _ => y''', rfl, rfl, rfl, rfl⟩
  have hY : ∀ k ≤ 2, ∀ s ∈ Icc a b, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s := by
    intro k hk s hs
    rcases k with _ | _ | _ | k
    · rw [e0, e1]; exact hy s hs
    · rw [e1, e2]; exact hy' s hs
    · rw [e2, e3]; exact hy'' s hs
    · omega
  have key := norm_sub_taylorSum_le (Y := Y) (n := 2) hab hY (by rw [e3]; exact hM)
  have hsum : ∑ k ∈ range (2 + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a
      = y a + (b - a) • y' a + ((b - a) ^ 2 / 2) • y'' a := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e0, e1, e2]
    norm_num
  rw [e0, hsum] at key
  have he : y b - y a - (b - a) • y' a - ((b - a) ^ 2 / 2) • y'' a
      = y b - (y a + (b - a) • y' a + ((b - a) ^ 2 / 2) • y'' a) := by abel
  rw [he]
  refine key.trans (le_of_eq ?_)
  norm_num

/-- **Fourth-order Taylor bound along a segment** for a map `G` on a normed space with Fréchet
derivatives `G₁, G₂, G₃, G₄` and `‖G₄‖ ≤ M`:
`‖G(p + w) - G p - G₁ p w - (1/2) G₂ p w w - (1/6) G₃ p w w w‖ ≤ M ‖w‖⁴ / 24`. It is
`norm_sub_taylorSum_le` for `s ↦ G (p + s • w)` on `[0, 1]`, whose `k`-th derivative is
`G_k (p + s • w)` applied to `w` `k` times (`HasFDerivAt.comp_hasDerivAt` and
`HasFDerivAt.clm_apply`); it is the order-four analogue of
`norm_sub_sub_smul_apply_le_of_hasFDerivAt`. -/
theorem norm_sub_taylor_segment_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → X} {G₁ : X → X →L[ℝ] X} {G₂ : X → X →L[ℝ] X →L[ℝ] X}
    {G₃ : X → X →L[ℝ] X →L[ℝ] X →L[ℝ] X} {G₄ : X → X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] X} {M : ℝ}
    (h1 : ∀ p, HasFDerivAt G (G₁ p) p) (h2 : ∀ p, HasFDerivAt G₁ (G₂ p) p)
    (h3 : ∀ p, HasFDerivAt G₂ (G₃ p) p) (h4 : ∀ p, HasFDerivAt G₃ (G₄ p) p)
    (hM : ∀ p, ‖G₄ p‖ ≤ M) (p w : X) :
    ‖G (p + w) - G p - G₁ p w - (2⁻¹ : ℝ) • G₂ p w w - (6⁻¹ : ℝ) • G₃ p w w w‖
      ≤ M * ‖w‖ ^ 4 / 24 := by
  have hseg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p + s • w) w s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const w).const_add p
  obtain ⟨Y, e0, e1, e2, e3, e4⟩ :
      ∃ Y : ℕ → ℝ → X, Y 0 = (fun s => G (p + s • w)) ∧ Y 1 = (fun s => G₁ (p + s • w) w) ∧
        Y 2 = (fun s => G₂ (p + s • w) w w) ∧ Y 3 = (fun s => G₃ (p + s • w) w w w) ∧
        Y 4 = (fun s => G₄ (p + s • w) w w w w) :=
    ⟨fun k => match k with
      | 0 => fun s => G (p + s • w)
      | 1 => fun s => G₁ (p + s • w) w
      | 2 => fun s => G₂ (p + s • w) w w
      | 3 => fun s => G₃ (p + s • w) w w w
      | _ => fun s => G₄ (p + s • w) w w w w,
     rfl, rfl, rfl, rfl, rfl⟩
  have hd0 : ∀ s : ℝ, HasDerivAt (Y 0) (Y 1 s) s := by
    intro s
    rw [e0, e1]
    exact (h1 _).comp_hasDerivAt s (hseg s)
  have hd1 : ∀ s : ℝ, HasDerivAt (Y 1) (Y 2 s) s := by
    intro s
    rw [e1, e2]
    have hc : HasDerivAt (fun s : ℝ => G₁ (p + s • w)) (G₂ (p + s • w) w) s :=
      (h2 _).comp_hasDerivAt s (hseg s)
    simpa using hc.clm_apply (hasDerivAt_const s w)
  have hd2 : ∀ s : ℝ, HasDerivAt (Y 2) (Y 3 s) s := by
    intro s
    rw [e2, e3]
    have hc : HasDerivAt (fun s : ℝ => G₂ (p + s • w)) (G₃ (p + s • w) w) s :=
      (h3 _).comp_hasDerivAt s (hseg s)
    have hc2 : HasDerivAt (fun s : ℝ => G₂ (p + s • w) w) (G₃ (p + s • w) w w) s := by
      simpa using hc.clm_apply (hasDerivAt_const s w)
    simpa using hc2.clm_apply (hasDerivAt_const s w)
  have hd3 : ∀ s : ℝ, HasDerivAt (Y 3) (Y 4 s) s := by
    intro s
    rw [e3, e4]
    have hc : HasDerivAt (fun s : ℝ => G₃ (p + s • w)) (G₄ (p + s • w) w) s :=
      (h4 _).comp_hasDerivAt s (hseg s)
    have hc2 : HasDerivAt (fun s : ℝ => G₃ (p + s • w) w) (G₄ (p + s • w) w w) s := by
      simpa using hc.clm_apply (hasDerivAt_const s w)
    have hc3 : HasDerivAt (fun s : ℝ => G₃ (p + s • w) w w) (G₄ (p + s • w) w w w) s := by
      simpa using hc2.clm_apply (hasDerivAt_const s w)
    simpa using hc3.clm_apply (hasDerivAt_const s w)
  have hY : ∀ k ≤ 3, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc 0 1) s := by
    intro k hk s _
    rcases k with _ | _ | _ | _ | k
    · exact (hd0 s).hasDerivWithinAt
    · exact (hd1 s).hasDerivWithinAt
    · exact (hd2 s).hasDerivWithinAt
    · exact (hd3 s).hasDerivWithinAt
    · omega
  have hMY : ∀ s ∈ Icc (0 : ℝ) 1, ‖Y 4 s‖ ≤ M * ‖w‖ ^ 4 := by
    intro s _
    rw [e4]
    calc ‖G₄ (p + s • w) w w w w‖ ≤ ‖G₄ (p + s • w) w w w‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w) w w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w) w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w)‖ * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by gcongr; exact hM _
      _ = M * ‖w‖ ^ 4 := by ring
  have key := norm_sub_taylorSum_le (Y := Y) (n := 3) (M := M * ‖w‖ ^ 4) zero_le_one hY hMY
  have hgoal : G (p + w) - G p - G₁ p w - (2⁻¹ : ℝ) • G₂ p w w - (6⁻¹ : ℝ) • G₃ p w w w
      = Y 0 1 - ∑ k ∈ range 4, (((1 : ℝ) - 0) ^ k / (Nat.factorial k : ℝ)) • Y k 0 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e0, e1, e2, e3]
    norm_num
    abel
  rw [hgoal]
  refine key.trans (le_of_eq ?_)
  norm_num

variable {F : ℝ × E → E} {F' : ℝ × E → ℝ × E →L[ℝ] E} {F'' : ℝ × E → ℝ × E →L[ℝ] ℝ × E →L[ℝ] E}

/-- The segment bound `norm_sub_sub_smul_apply_le_of_hasFDerivAt` for `σ ≥ 0`. -/
theorem norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg
    (hF : ∀ p, HasFDerivAt F (F' p) p) (hF' : ∀ p, HasFDerivAt F' (F'' p) p)
    (hM : ∀ p, ‖F'' p‖ ≤ M) (p v : ℝ × E) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M * ‖v‖ ^ 2 * σ ^ 2 / 2 := by
  have hseg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add p
  have hφ : ∀ s : ℝ, HasDerivAt (fun s => F (p + s • v)) (F' (p + s • v) v) s := fun s =>
    (hF _).comp_hasDerivAt s (hseg s)
  have hφ' : ∀ s : ℝ, HasDerivAt (fun s => F' (p + s • v) v) (F'' (p + s • v) v v) s := by
    intro s
    have := ((hF' _).comp_hasDerivAt s (hseg s)).clm_apply (hasDerivAt_const s v)
    simpa using this
  have hbound : ∀ s ∈ Icc 0 σ, ‖F'' (p + s • v) v v‖ ≤ M * ‖v‖ ^ 2 := fun s _ => by
    calc ‖F'' (p + s • v) v v‖ ≤ ‖F'' (p + s • v) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖F'' (p + s • v)‖ * ‖v‖ * ‖v‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hM _
      _ = M * ‖v‖ ^ 2 := by ring
  have key := norm_sub_sub_smul_le_mul_sq_div_two (a := 0) (b := σ) hσ
    (fun s _ => (hφ s).hasDerivWithinAt) (fun s _ => (hφ' s).hasDerivWithinAt) hbound
  simpa using key

/-- **Second-order Taylor bound along a segment** for a map `F : ℝ × E → E` with Fréchet
derivatives `F'` and `F''`, `‖F''‖ ≤ M`:
`‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M ‖v‖² σ² / 2` for every real `σ`. This is the
one-variable bound `norm_sub_sub_smul_le_mul_sq_div_two` for `s ↦ F (p + s • v)`, whose second
derivative is `F'' (p + s • v) v v`; a negative `σ` is the case of `-v`. -/
theorem norm_sub_sub_smul_apply_le_of_hasFDerivAt (hF : ∀ p, HasFDerivAt F (F' p) p)
    (hF' : ∀ p, HasFDerivAt F' (F'' p) p) (hM : ∀ p, ‖F'' p‖ ≤ M) (p v : ℝ × E) (σ : ℝ) :
    ‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M * ‖v‖ ^ 2 * σ ^ 2 / 2 := by
  rcases le_or_gt 0 σ with hσ | hσ
  · exact norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg hF hF' hM p v hσ
  · have := norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg hF hF' hM p (-v)
      (neg_nonneg.2 hσ.le)
    simpa [smul_neg, neg_smul] using this

end Curve
