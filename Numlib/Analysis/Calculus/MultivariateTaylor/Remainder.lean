import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Calculus.MultivariateTaylor.Basic
import Numlib.Analysis.Calculus.TaylorSegment

/-!
# Taylor's theorem with Hölder or Lipschitz continuous top derivative

Remainder bounds for the Taylor polynomial `T_{f,p}(x, s)` of `f : E → F` (`E`, `F` real normed
spaces; real-valued objectives and vector-valued constraint maps alike) when `∇^p f` is Hölder
or Lipschitz continuous on a convex set `C` ([cartis2022evaluation], Appendix A.8). They drive
every evaluation-complexity proof of the book: overestimation of
regularized models and "add-and-subtract" lower bounds on step lengths.

Tensor norms are Mathlib's operator norms on `ContinuousMultilinearMap` (the book's (A.7)).
Instead of requiring `f` to be `C^p` on an open set `D ⊇ C`, the results assume
`∀ y ∈ C, ContDiffAt ℝ p f y`, which is equivalent for finite `p`; for global assumptions take
`C = univ`.

## Main definitions

* `holderFactorial k β`: the generalized factorial `(k + β)! = ∏_{ℓ=1}^{k} (ℓ + β)`;
* `IteratedFDerivHolderOn f p H β C`, `IteratedFDerivLipschitzOn f p L C`: Hölder / Lipschitz
  continuity of `∇^p f` on `C` with real constants ((A.13), (A.18)).

## Main results

* `taylor_integral_remainder_sub`: Theorem A.8.1 (integral form of the remainder, (A.9));
* `integral_rpow_mul_one_sub_pow`: the Beta integral (A.16);
* `norm_sub_taylorSum_le_of_holder_of_le`: Taylor's theorem for curves on `[a, b]` with Hölder
  top derivative (the Hölder analogue of `norm_sub_taylorSum_le`), and its `[0, 1]` form
  `norm_sub_taylorSum_le_of_holder`;
* `norm_sub_taylorPolynomial_le_of_holder`, `norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder`:
  Theorem A.8.3, (A.14) and (A.15);
* `norm_sub_taylorPolynomial_le_of_lipschitz`,
  `norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz`: Corollary A.8.4, (A.19)–(A.20);
* for real-valued `f`: `abs_sub_taylorPolynomial_le_of_holder`/`_of_lipschitz`, and
  `le_taylorPolynomial_add_of_lipschitz`, `taylorPolynomial_sub_le_of_lipschitz`: the regularized
  Taylor model over- and under-estimates `f`.

## Implementation notes

The book proves (A.14)–(A.15) from the integral remainder and the Beta integral. Here the bounds
follow from a curve version (`norm_sub_taylorSum_le_of_holder`) proved by induction on the order
with the mean value inequality, applied to `t ↦ (∇^{j+i} f(x + t s) - ∇^{j+i}_s T_{f,p}(x, t s))
[v, s, …, s]`; this uses the symmetry of iterated derivatives and formula (A.11) from
`Numlib.Analysis.Calculus.MultivariateTaylor.Basic`.
-/

open Finset Set
open scoped Nat

section HolderFactorial

/-- The generalized factorial `(k + β)! = ∏_{ℓ=1}^{k} (ℓ + β)` of [cartis2022evaluation]
(Section A.8), defined as the rising factorial `(1 + β)(2 + β)⋯(k + β)`. It coincides with
`(k+1)!` for `β = 1`
(`holderFactorial_one_right`) and with `k!` for `β = 0` (`holderFactorial_zero_right`). -/
noncomputable def holderFactorial (k : ℕ) (β : ℝ) : ℝ :=
  (ascPochhammer ℝ k).eval (1 + β)

@[simp]
theorem holderFactorial_zero (β : ℝ) : holderFactorial 0 β = 1 := by
  simp [holderFactorial]

theorem holderFactorial_succ (k : ℕ) (β : ℝ) :
    holderFactorial (k + 1) β = holderFactorial k β * (k + 1 + β) := by
  rw [holderFactorial, ascPochhammer_succ_eval, ← holderFactorial]
  ring

/-- `(k + 1 + β)! = (1 + β) · (k + (1 + β))!`. -/
theorem holderFactorial_succ' (k : ℕ) (β : ℝ) :
    holderFactorial (k + 1) β = (1 + β) * holderFactorial k (β + 1) := by
  induction k with
  | zero => simp [holderFactorial_succ]
  | succ k ih =>
    rw [holderFactorial_succ, ih, holderFactorial_succ]
    push_cast
    ring

theorem holderFactorial_pos (k : ℕ) {β : ℝ} (hβ : -1 < β) : 0 < holderFactorial k β := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [holderFactorial_succ]
    exact mul_pos ih (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)

@[simp]
theorem holderFactorial_one_right (k : ℕ) : holderFactorial k 1 = ((k + 1)! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [holderFactorial_succ, ih, Nat.factorial_succ (k + 1)]
    push_cast
    ring

@[simp]
theorem holderFactorial_zero_right (k : ℕ) : holderFactorial k 0 = (k ! : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [holderFactorial_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- `∫_0^1 ξ^β (1 - ξ)^m dξ = m! / (m + 1 + β)!`, by induction on `m` integrating by parts. -/
private theorem integral_rpow_mul_one_sub_pow_aux (m : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ∫ ξ in (0 : ℝ)..1, ξ ^ β * (1 - ξ) ^ m = (m ! : ℝ) / holderFactorial (m + 1) β := by
  induction m generalizing β with
  | zero =>
    simp only [pow_zero, mul_one, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < β)),
      Real.one_rpow, Real.zero_rpow (by linarith : β + 1 ≠ 0), holderFactorial_succ,
      holderFactorial_zero]
    norm_num
    ring
  | succ m ih =>
    have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ (β + 1) / (β + 1)) (x ^ β) x := by
      intro x _
      have h := (Real.hasDerivAt_rpow_const (x := x) (p := β + 1) (Or.inr (by linarith))).div_const
        (β + 1)
      convert h using 1
      rw [add_sub_cancel_right]
      field_simp
    have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1))
        (-(((m + 1 : ℕ) : ℝ) * (1 - x) ^ m)) x := by
      intro x _
      have h := ((hasDerivAt_id x).const_sub 1).fun_pow (m + 1)
      convert h using 1
      · rfl
      · simp only [id, Nat.add_sub_cancel, mul_neg, mul_one]
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((continuous_id.rpow_const fun _ => Or.inr hβ).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun x : ℝ => -(((m + 1 : ℕ) : ℝ) * (1 - x) ^ m)).intervalIntegrable
        0 1)
    simp only [sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, mul_zero, Real.zero_rpow (by linarith : β + 1 ≠ 0),
      zero_div, zero_mul, sub_zero, zero_sub] at hparts
    have e : ∫ x in (0 : ℝ)..1, x ^ (β + 1) / (β + 1) * -(((m + 1 : ℕ) : ℝ) * (1 - x) ^ m) =
        -(((m + 1 : ℕ) : ℝ) / (β + 1)) * ∫ x in (0 : ℝ)..1, x ^ (β + 1) * (1 - x) ^ m := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      ring
    rw [e, ih (by linarith)] at hparts
    rw [neg_eq_iff_eq_neg.1 hparts.symm, holderFactorial_succ' (m + 1), Nat.factorial_succ]
    have h1 : (1 + β) ≠ 0 := by linarith
    have h2 : holderFactorial (m + 1) (β + 1) ≠ 0 := (holderFactorial_pos _ (by linarith)).ne'
    push_cast
    field_simp
    ring

/-- **The Beta integral** ([cartis2022evaluation], (A.16)): for `k ≥ 1` and `β ≥ 0`,
`∫_0^1 ξ^β (1 - ξ)^{k-1} dξ = (k - 1)! / (k + β)!`. -/
theorem integral_rpow_mul_one_sub_pow {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ : 0 ≤ β) :
    ∫ ξ in (0 : ℝ)..1, ξ ^ β * (1 - ξ) ^ (k - 1) = ((k - 1)! : ℝ) / holderFactorial k β := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simpa using integral_rpow_mul_one_sub_pow_aux m hβ

end HolderFactorial

section Univariate

/-- **Taylor's theorem for a univariate function, integral form** ([cartis2022evaluation],
Theorem A.8.1, (A.9)). If `k ≥ 1`, `h ≥ 0` and `ψ` is `C^k` on `[t, t + h]`, then with
`τ_k = ∑_{i ≤ k} ψ^{(i)}(t) h^i / i!` (derivatives within the interval),
`ψ(t + h) - τ_k = 1/(k-1)! ∫_0^h (h - ξ)^{k-1} (ψ^{(k)}(t + ξ) - ψ^{(k)}(t)) dξ`. -/
theorem taylor_integral_remainder_sub {ψ : ℝ → ℝ} {t h : ℝ} {k : ℕ} (hk : 1 ≤ k) (hh : 0 ≤ h)
    (hψ : ContDiffOn ℝ k ψ (Icc t (t + h))) :
    ψ (t + h) - taylorWithinEval ψ k (Icc t (t + h)) t (t + h) =
      ((k - 1)! : ℝ)⁻¹ * ∫ ξ in (0 : ℝ)..h, (h - ξ) ^ (k - 1) *
        (iteratedDerivWithin k ψ (Icc t (t + h)) (t + ξ) -
          iteratedDerivWithin k ψ (Icc t (t + h)) t) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.add_sub_cancel]
  rcases hh.eq_or_lt with rfl | hpos
  · simp [taylorWithinEval_self]
  set I := Icc t (t + h)
  set g := iteratedDerivWithin (m + 1) ψ I
  have hI : uIcc t (t + h) = I := uIcc_of_le (by linarith)
  have hR := taylor_integral_remainder (f := ψ) (x₀ := t) (x := t + h) (n := m) (by rwa [hI])
  rw [hI] at hR
  have hg : ContinuousOn g I := hψ.continuousOn_iteratedDerivWithin le_rfl
    (uniqueDiffOn_Icc (by linarith))
  -- move the integral to `[t, t + h]`
  have e1 : ∫ ξ in (0 : ℝ)..h, (h - ξ) ^ m * (g (t + ξ) - g t) =
      ∫ u in t..t + h, (t + h - u) ^ m * (g u - g t) := by
    have := intervalIntegral.integral_comp_add_left
      (fun u => (t + h - u) ^ m * (g u - g t)) t (a := 0) (b := h)
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext ξ
    ring_nf
  have hint1 : IntervalIntegrable (fun u => (t + h - u) ^ m * g u) MeasureTheory.volume t
      (t + h) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    fun_prop
  have hint2 : IntervalIntegrable (fun u => (t + h - u) ^ m * g t) MeasureTheory.volume t
      (t + h) := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have e2 : ∫ u in t..t + h, (t + h - u) ^ m * (g u - g t) =
      (∫ u in t..t + h, (t + h - u) ^ m * g u) - h ^ (m + 1) / (m + 1) * g t := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hint1 hint2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_left (fun u => u ^ m), integral_pow]
    simp
  have e3 : ∫ u in t..t + h, ((t + h - u) ^ m / (m ! : ℝ)) • g u =
      (m ! : ℝ)⁻¹ * ∫ u in t..t + h, (t + h - u) ^ m * g u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [smul_eq_mul]
    ring
  rw [taylorWithinEval_succ, ← sub_sub, hR, e1, e2, e3, smul_eq_mul]
  have : (m ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Univariate

section Curve

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a polynomial curve `s ↦ ∑_{i ≤ n} ((s - a)^i/i!) c_i` is
`s ↦ ∑_{i < n} ((s - a)^i/i!) c_{i+1}`. -/
theorem hasDerivAt_sum_sub_pow_div_factorial_smul (a : ℝ) (c : ℕ → F) (n : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i ∈ range (n + 1), ((s - a) ^ i / (i ! : ℝ)) • c i)
      (∑ i ∈ range n, ((s - a) ^ i / (i ! : ℝ)) • c (i + 1)) s := by
  have e : (fun s : ℝ => ∑ i ∈ range (n + 1), ((s - a) ^ i / (i ! : ℝ)) • c i) =
      fun s => (∑ i ∈ range n, ((s - a) ^ (i + 1) / ((i + 1)! : ℝ)) • c (i + 1)) + c 0 := by
    funext s
    simp [sum_range_succ']
  rw [e]
  refine (HasDerivAt.fun_sum fun i _ => ?_).add_const (c 0)
  have h := ((((hasDerivAt_id' s).sub_const a).fun_pow (i + 1)).div_const
    ((i + 1)! : ℝ)).smul_const (c (i + 1))
  refine h.congr_deriv ?_
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
  have : (i ! : ℝ) ≠ 0 := by positivity
  congr 1
  push_cast
  field_simp

/-- **Taylor's theorem for a curve with Hölder continuous top derivative.** Let `F` be a real
normed space and `Y 0, …, Y p : ℝ → F` a chain of successive derivatives on `[a, b]`
(`(Y i)' = Y (i + 1)`) with `‖Y p t - Y p a‖ ≤ H (t - a)^β` on `[a, b]`, `β ≥ 0`. Then
`‖Y 0 b - ∑_{i ≤ p} ((b - a)^i/i!) Y i a‖ ≤ H (b - a)^{p+β} / (p+β)!`.
This is the Hölder analogue of `norm_sub_taylorSum_le` (same normal form), which assumes instead a
bound `‖Y (p + 1)‖ ≤ M` on one more derivative: the case `β = 1`, `H = M` of the present statement
follows from that one by the mean value inequality. Proved by induction on `p` with the mean value
inequality (`image_norm_le_of_norm_deriv_right_le_deriv_boundary`). -/
theorem norm_sub_taylorSum_le_of_holder_of_le {Y : ℕ → ℝ → F} {p : ℕ} {H β a b : ℝ}
    (hβ : 0 ≤ β) (hab : a ≤ b)
    (hY : ∀ i < p, ∀ t ∈ Icc a b, HasDerivWithinAt (Y i) (Y (i + 1) t) (Icc a b) t)
    (hH : ∀ t ∈ Icc a b, ‖Y p t - Y p a‖ ≤ H * (t - a) ^ β) :
    ‖Y 0 b - ∑ i ∈ range (p + 1), ((b - a) ^ i / (i ! : ℝ)) • Y i a‖ ≤
      H * (b - a) ^ ((p : ℝ) + β) / holderFactorial p β := by
  induction p generalizing Y b with
  | zero => simpa using hH b (right_mem_Icc.2 hab)
  | succ p ih =>
    have ih' : ∀ s ∈ Icc a b,
        ‖Y 1 s - ∑ i ∈ range (p + 1), ((s - a) ^ i / (i ! : ℝ)) • Y (i + 1) a‖ ≤
          H * (s - a) ^ ((p : ℝ) + β) / holderFactorial p β := by
      intro s hs
      have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
      exact ih (Y := fun i => Y (i + 1)) hs.1
        (fun i hi u hu => (hY (i + 1) (by omega) u (hsub hu)).mono hsub)
        (fun u hu => hH u (hsub hu))
    set g : ℝ → F := fun s => Y 0 s - ∑ i ∈ range (p + 1 + 1), ((s - a) ^ i / (i ! : ℝ)) • Y i a
      with hg_def
    have hg : ∀ s ∈ Icc a b, HasDerivWithinAt g
        (Y 1 s - ∑ i ∈ range (p + 1), ((s - a) ^ i / (i ! : ℝ)) • Y (i + 1) a) (Icc a b) s :=
      fun s hs => (hY 0 (by omega) s hs).sub
        (hasDerivAt_sum_sub_pow_div_factorial_smul a (fun i => Y i a) (p + 1) s).hasDerivWithinAt
    set r : ℝ := ((p + 1 : ℕ) : ℝ) + β with hr
    have hr1 : 1 ≤ r := by rw [hr]; push_cast; linarith [(p.cast_nonneg : (0 : ℝ) ≤ p)]
    have hB : ∀ s, HasDerivAt (fun s => H * (s - a) ^ r / holderFactorial (p + 1) β)
        (H * (s - a) ^ ((p : ℝ) + β) / holderFactorial p β) s := by
      intro s
      have h := (((Real.hasDerivAt_rpow_const (x := s - a) (Or.inr hr1)).comp s
        ((hasDerivAt_id' s).sub_const a)).const_mul H).div_const (holderFactorial (p + 1) β)
      refine h.congr_deriv ?_
      rw [holderFactorial_succ, show r - 1 = (p : ℝ) + β by rw [hr]; push_cast; ring]
      have : (p : ℝ) + 1 + β ≠ 0 := by linarith [(p.cast_nonneg : (0 : ℝ) ≤ p)]
      have : holderFactorial p β ≠ 0 := (holderFactorial_pos p (by linarith)).ne'
      rw [hr]; push_cast
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (HasDerivWithinAt.continuousOn hg)
      (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (B := fun s => H * (s - a) ^ r / holderFactorial (p + 1) β) (by
        have : (0 : ℝ) ^ r = 0 := Real.zero_rpow (by linarith)
        simp [g, sum_range_succ', this])
      hB (fun s hs => ih' s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
    simpa [g, hr] using key

/-- **Taylor's theorem for a curve with Hölder continuous top derivative**, on `[0, 1]`
(the form used in the proof of [cartis2022evaluation], Theorem A.8.3): if `Y 0, …, Y p` is a chain
of successive derivatives on `[0, 1]` with `‖Y p t - Y p 0‖ ≤ H t^β`, `β ≥ 0`, then
`‖Y 0 1 - ∑_{i ≤ p} (1/i!) Y i 0‖ ≤ H / (p+β)!`. -/
theorem norm_sub_taylorSum_le_of_holder {Y : ℕ → ℝ → F} {p : ℕ} {H β : ℝ} (hβ : 0 ≤ β)
    (hY : ∀ i < p, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Y i) (Y (i + 1) t) (Icc 0 1) t)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ‖Y p t - Y p 0‖ ≤ H * t ^ β) :
    ‖Y 0 1 - ∑ i ∈ range (p + 1), (i ! : ℝ)⁻¹ • Y i 0‖ ≤ H / holderFactorial p β := by
  simpa using norm_sub_taylorSum_le_of_holder_of_le hβ zero_le_one hY
    (fun t ht => by simpa using hH t ht)

end Curve

section Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The `p`-th derivative of `f` is Hölder continuous on `C` with constant `H` and exponent `β`:
`‖∇^p f(x) - ∇^p f(y)‖ ≤ H ‖x - y‖^β` for `x, y ∈ C` ([cartis2022evaluation], (A.13)), with
Mathlib's operator norm on multilinear maps and a real power. Real constants are used (rather than
`HolderOnWith` with `ℝ≥0` constants) since they enter explicit complexity bounds; for nonnegative
constants the two agree (`iteratedFDerivHolderOn_iff_holderOnWith`). -/
def IteratedFDerivHolderOn (f : E → F) (p : ℕ) (H β : ℝ) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ H * ‖x - y‖ ^ β

/-- The `p`-th derivative of `f` is Lipschitz continuous on `C` with constant `L`:
`‖∇^p f(x) - ∇^p f(y)‖ ≤ L ‖x - y‖` for `x, y ∈ C` ([cartis2022evaluation], (A.18)); the Hölder
condition with exponent `1`. -/
def IteratedFDerivLipschitzOn (f : E → F) (p : ℕ) (L : ℝ) (C : Set E) : Prop :=
  IteratedFDerivHolderOn f p L 1 C

variable {f : E → F} {p : ℕ} {H β L : ℝ} {C : Set E}

theorem iteratedFDerivHolderOn_iff : IteratedFDerivHolderOn f p H β C ↔
    ∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ H * ‖x - y‖ ^ β :=
  Iff.rfl

theorem iteratedFDerivLipschitzOn_iff : IteratedFDerivLipschitzOn f p L C ↔
    ∀ x ∈ C, ∀ y ∈ C, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖ := by
  simp [IteratedFDerivLipschitzOn, IteratedFDerivHolderOn]

theorem IteratedFDerivLipschitzOn.holderOn (h : IteratedFDerivLipschitzOn f p L C) :
    IteratedFDerivHolderOn f p L 1 C :=
  h

theorem IteratedFDerivHolderOn.mono {C' : Set E} (h : IteratedFDerivHolderOn f p H β C)
    (hC : C' ⊆ C) : IteratedFDerivHolderOn f p H β C' :=
  fun x hx y hy => h x (hC hx) y (hC hy)

theorem IteratedFDerivLipschitzOn.mono {C' : Set E} (h : IteratedFDerivLipschitzOn f p L C)
    (hC : C' ⊆ C) : IteratedFDerivLipschitzOn f p L C' :=
  IteratedFDerivHolderOn.mono h hC

/-- With nonnegative constants, the Hölder condition on the `p`-th derivative is Mathlib's
`HolderOnWith`. -/
theorem iteratedFDerivHolderOn_iff_holderOnWith {H r : NNReal} :
    IteratedFDerivHolderOn f p H r C ↔ HolderOnWith H r (iteratedFDeriv ℝ p f) C := by
  constructor
  · intro h x hx y hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul H.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm] using h x hx y hy)
  · intro h x hx y hy
    simpa [dist_eq_norm] using h.dist_le hx hy

/-- With a nonnegative constant, the Lipschitz condition on the `p`-th derivative is Mathlib's
`LipschitzOnWith`. -/
theorem iteratedFDerivLipschitzOn_iff_lipschitzOnWith {L : NNReal} :
    IteratedFDerivLipschitzOn f p L C ↔ LipschitzOnWith L (iteratedFDeriv ℝ p f) C := by
  rw [iteratedFDerivLipschitzOn_iff, lipschitzOnWith_iff_norm_sub_le]

/-- For a function `C^{n+1}` at `y`, prepending or appending an argument to the
`(n+1)`-st derivative gives the same value. -/
theorem ContDiffAt.iteratedFDeriv_cons_eq_snoc {g : E → F} {n : ℕ} {y : E}
    (hg : ContDiffAt ℝ (n + 1) g y) (s : E) (u : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g y (Fin.cons s u) = iteratedFDeriv ℝ (n + 1) g y (Fin.snoc u s) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact (hg.iteratedFDeriv_comp_perm_of_le le_rfl (finRotate (n + 1)) _).symm

end Holder

section Remainder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {p : ℕ} {H β L : ℝ} {C : Set E}

/-- **Taylor's theorem with Hölder `p`-th derivative, derivative bounds** ([cartis2022evaluation],
Theorem A.8.3, (A.15)). Let `C` be convex, `f` be `C^p` at every point of `C` (e.g. `C^p` on an
open set containing `C`) and `∇^p f` be `(H, β)`-Hölder on `C`, `β ≥ 0`. Then for `x, x + s ∈ C`
and `j ≤ p`,
`‖∇^j f(x + s) - ∇^j_s T_{f,p}(x, s)‖ ≤ H / (p - j + β)! · ‖s‖^{p - j + β}`.
(The book states it for `1 ≤ j ≤ p` and `β ∈ [0, 1]`; its proof displays the constant
`(p-j+1)!/(p-j+β)!`, the bound being `1/(p-j+β)!` as stated in (A.15).) The case `j = 0` is
`norm_sub_taylorPolynomial_le_of_holder`. -/
theorem norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hβ : 0 ≤ β) (hH : IteratedFDerivHolderOn f p H β C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) {j : ℕ} (hj : j ≤ p) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
      H / holderFactorial (p - j) β * ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  set T := taylorPolynomial f (j + m) x with hT
  have hTc : ∀ (k : ℕ) (y : E), ContDiffAt ℝ k T y :=
    fun k y => (contDiff_taylorPolynomial f (j + m) x).contDiffAt
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ C := fun t ht => hC.add_smul_mem hx hxs ht
  have hfx : ContDiffAt ℝ (j + m : ℕ) f x := hf x hx
  have hhF : 0 < holderFactorial m β := holderFactorial_pos m (by linarith)
  -- the Hölder constant times `‖s‖^β` is nonnegative
  have hHs : 0 ≤ H * ‖s‖ ^ β := by
    have := hH (x + s) hxs x hx
    rw [add_sub_cancel_left] at this
    exact (norm_nonneg _).trans this
  have hpow : ‖s‖ ^ ((m : ℝ) + β) = ‖s‖ ^ m * ‖s‖ ^ β := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg _) m.cast_nonneg hβ, Real.rpow_natCast]
  have hM : 0 ≤ H / holderFactorial m β * ‖s‖ ^ ((m : ℝ) + β) := by
    rw [hpow, show H / holderFactorial m β * (‖s‖ ^ m * ‖s‖ ^ β) =
      H * ‖s‖ ^ β * ‖s‖ ^ m / holderFactorial m β by ring]
    exact div_nonneg (mul_nonneg hHs (by positivity)) hhF.le
  refine ContinuousMultilinearMap.opNorm_le_bound hM fun v => ?_
  -- the curve `t ↦ (∇^{j+i} f(x + t s) - ∇^{j+i} T(t s))[v, s, …, s]`
  set u : ∀ i : ℕ, Fin (j + i) → E := fun i k => if h : (k : ℕ) < j then v ⟨k, h⟩ else s
    with hu
  set Y : ℕ → ℝ → F := fun i t => iteratedFDeriv ℝ (j + i) f (x + t • s) (u i) -
    iteratedFDeriv ℝ (j + i) T (t • s) (u i) with hY
  have hsnoc : ∀ i, (Fin.snoc (u i) s : Fin (j + i + 1) → E) = u (i + 1) := by
    intro i
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [hu]
    · simp [hu]
  have hchain : ∀ i < m, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (Y i) (Y (i + 1) t) (Icc 0 1) t := by
    intro i hi t ht
    have hft : ContDiffAt ℝ ((j + i : ℕ) + 1) f (x + t • s) :=
      (hf _ (hseg t ht)).of_le (by norm_cast; omega)
    have h1 := hasDerivAt_iteratedFDeriv_line_apply hft (u i)
    have h2 := hasDerivAt_iteratedFDeriv_line_apply (a := 0) (s := s) (t := t)
      (hTc (j + i + 1) _) (u i)
    rw [hft.iteratedFDeriv_cons_eq_snoc, hsnoc] at h1
    rw [(hTc (j + i + 1) _).iteratedFDeriv_cons_eq_snoc, hsnoc] at h2
    simp only [zero_add] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hY0 : ∀ i ≤ m, Y i 0 = 0 := by
    intro i hi
    simp only [hY, zero_smul, add_zero]
    rw [hT, iteratedFDeriv_taylorPolynomial_zero hfx (by omega), sub_self]
  have hHol : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Y m t - Y m 0‖ ≤ (H * ‖s‖ ^ β * ∏ k, ‖u m k‖) * t ^ β := by
    intro t ht
    rw [hY0 m le_rfl, sub_zero]
    simp only [hY]
    rw [hT, iteratedFDeriv_taylorPolynomial_self hfx, ← _root_.sub_apply]
    calc ‖(iteratedFDeriv ℝ (j + m) f (x + t • s) - iteratedFDeriv ℝ (j + m) f x) (u m)‖
        ≤ ‖iteratedFDeriv ℝ (j + m) f (x + t • s) - iteratedFDeriv ℝ (j + m) f x‖ *
            ∏ k, ‖u m k‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (H * ‖t • s‖ ^ β) * ∏ k, ‖u m k‖ := by
          gcongr
          simpa using hH _ (hseg t ht) x hx
      _ = (H * ‖s‖ ^ β * ∏ k, ‖u m k‖) * t ^ β := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, Real.mul_rpow ht.1 (norm_nonneg _)]
          ring
  have key := norm_sub_taylorSum_le_of_holder hβ hchain hHol
  rw [sum_eq_zero fun i hi => by rw [hY0 i (Nat.lt_succ_iff.1 (mem_range.1 hi)), smul_zero],
    sub_zero] at key
  have hu0 : u 0 = v := funext fun k => by simp [hu]
  have hY01 : Y 0 1 = (iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j T s) v := by
    simp only [hY, one_smul, hu0]
    rfl
  have hprod : ∏ k, ‖u m k‖ = (∏ k, ‖v k‖) * ‖s‖ ^ m := by
    rw [Fin.prod_univ_add]
    simp [hu]
  rw [hY01, hprod] at key
  calc ‖(iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j T s) v‖
      ≤ H * ‖s‖ ^ β * ((∏ k, ‖v k‖) * ‖s‖ ^ m) / holderFactorial m β := key
    _ = H / holderFactorial m β * ‖s‖ ^ ((m : ℝ) + β) * ∏ k, ‖v k‖ := by
        rw [hpow]; ring

/-- **Taylor's theorem with Hölder `p`-th derivative** ([cartis2022evaluation], Theorem A.8.3,
(A.14)). Let `C` be convex, `f : E → F` be `C^p` at every point of `C` and `∇^p f` be
`(H, β)`-Hölder on `C`, `β ≥ 0`. Then for `x, x + s ∈ C`,
`‖f(x + s) - T_{f,p}(x, s)‖ ≤ H / (p + β)! · ‖s‖^{p + β}`. For `p = 0` this is the Hölder condition
itself. -/
theorem norm_sub_taylorPolynomial_le_of_holder (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hβ : 0 ≤ β) (hH : IteratedFDerivHolderOn f p H β C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖f (x + s) - taylorPolynomial f p x s‖ ≤ H / holderFactorial p β * ‖s‖ ^ ((p : ℝ) + β) := by
  have h := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs
    (Nat.zero_le p)
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, Function.comp_apply,
    Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map, Nat.sub_zero] at h
  exact h

/-- **Taylor's theorem with Lipschitz `p`-th derivative** ([cartis2022evaluation],
Corollary A.8.4, (A.19)): if `f : E → F` is `C^p` at every point of the convex set `C` and
`∇^p f` is `L`-Lipschitz on `C`, then for `x, x + s ∈ C`,
`‖f(x + s) - T_{f,p}(x, s)‖ ≤ L / (p + 1)! · ‖s‖^{p+1}`. -/
theorem norm_sub_taylorPolynomial_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    ‖f (x + s) - taylorPolynomial f p x s‖ ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have h := norm_sub_taylorPolynomial_le_of_holder hC hf zero_le_one hL.holderOn hx hxs
  rwa [holderFactorial_one_right, show (p : ℝ) + 1 = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast] at h

/-- **Derivative bounds with Lipschitz `p`-th derivative** ([cartis2022evaluation],
Corollary A.8.4, (A.20)): under the hypotheses of `norm_sub_taylorPolynomial_le_of_lipschitz`,
for `j ≤ p`, `‖∇^j f(x + s) - ∇^j_s T_{f,p}(x, s)‖ ≤ L / (p - j + 1)! · ‖s‖^{p-j+1}`. For `j = 1`
this is the gradient bound `‖∇f(x + s) - ∇_s T_{f,p}(x, s)‖ ≤ L ‖s‖^p / p!`. -/
theorem norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) {j : ℕ} (hj : j ≤ p) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorPolynomial f p x) s‖ ≤
      L / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have h := norm_iteratedFDeriv_sub_taylorPolynomial_le_of_holder hC hf zero_le_one hL.holderOn
    hx hxs hj
  rwa [holderFactorial_one_right,
    show ((p - j : ℕ) : ℝ) + 1 = ((p - j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h

end Remainder

section RealValued

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {p : ℕ} {H β L : ℝ}
  {C : Set E}

/-- (A.14) for a real-valued `f` ([cartis2022evaluation], Theorem A.8.3):
`|f(x + s) - T_{f,p}(x, s)| ≤ H / (p + β)! · ‖s‖^{p + β}`. -/
theorem abs_sub_taylorPolynomial_le_of_holder (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hβ : 0 ≤ β) (hH : IteratedFDerivHolderOn f p H β C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ H / holderFactorial p β * ‖s‖ ^ ((p : ℝ) + β) :=
  norm_sub_taylorPolynomial_le_of_holder hC hf hβ hH hx hxs

/-- (A.19) for a real-valued `f` ([cartis2022evaluation], Corollary A.8.4):
`|f(x + s) - T_{f,p}(x, s)| ≤ L / (p + 1)! · ‖s‖^{p+1}`. -/
theorem abs_sub_taylorPolynomial_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - taylorPolynomial f p x s| ≤ L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) :=
  norm_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs

/-- **Overestimation property** ([cartis2022evaluation], Corollary A.8.4): under the hypotheses of
`abs_sub_taylorPolynomial_le_of_lipschitz`, for every `σ ≥ L` the regularized Taylor model
majorizes `f`: `f(x + s) ≤ T_{f,p}(x, s) + σ / (p + 1)! · ‖s‖^{p+1}`. -/
theorem le_taylorPolynomial_add_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) {σ : ℝ} (hσ : L ≤ σ) :
    f (x + s) ≤ taylorPolynomial f p x s + σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have h := (le_abs_self _).trans (abs_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs)
  have : L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by gcongr
  linarith

/-- The lower counterpart of `le_taylorPolynomial_add_of_lipschitz`: for every `σ ≥ L`,
`T_{f,p}(x, s) - σ / (p + 1)! · ‖s‖^{p+1} ≤ f(x + s)`. -/
theorem taylorPolynomial_sub_le_of_lipschitz (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hL : IteratedFDerivLipschitzOn f p L C)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) {σ : ℝ} (hσ : L ≤ σ) :
    taylorPolynomial f p x s - σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ f (x + s) := by
  have h := (neg_abs_le _).trans' (neg_le_neg
    (abs_sub_taylorPolynomial_le_of_lipschitz hC hf hL hx hxs))
  have : L / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by gcongr
  linarith

end RealValued

section LipschitzAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f g : E → F} {j : ℕ} {L L' : ℝ} {C : Set E}

/-- Lipschitz constants of `j`-th derivatives add under subtraction of `C^j` functions. -/
theorem IteratedFDerivLipschitzOn.sub (hf : IteratedFDerivLipschitzOn f j L C)
    (hg : IteratedFDerivLipschitzOn g j L' C) (hfC : ∀ y ∈ C, ContDiffAt ℝ j f y)
    (hgC : ∀ y ∈ C, ContDiffAt ℝ j g y) : IteratedFDerivLipschitzOn (f - g) j (L + L') C := by
  rw [iteratedFDerivLipschitzOn_iff] at *
  intro y hy z hz
  rw [iteratedFDeriv_sub_apply (hfC y hy) (hgC y hy), iteratedFDeriv_sub_apply (hfC z hz)
    (hgC z hz), sub_sub_sub_comm, add_mul]
  exact (norm_sub_le _ _).trans (add_le_add (hf y hy z hz) (hg y hy z hz))

/-- Lipschitz constants of `j`-th derivatives add under addition of `C^j` functions. -/
theorem IteratedFDerivLipschitzOn.add (hf : IteratedFDerivLipschitzOn f j L C)
    (hg : IteratedFDerivLipschitzOn g j L' C) (hfC : ∀ y ∈ C, ContDiffAt ℝ j f y)
    (hgC : ∀ y ∈ C, ContDiffAt ℝ j g y) : IteratedFDerivLipschitzOn (f + g) j (L + L') C := by
  rw [iteratedFDerivLipschitzOn_iff] at *
  intro y hy z hz
  rw [iteratedFDeriv_add_apply (hfC y hy) (hgC y hy), iteratedFDeriv_add_apply (hfC z hz)
    (hgC z hz), add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf y hy z hz) (hg y hy z hz))

/-- Composition with a continuous linear map on the left multiplies the Lipschitz constant of
the `j`-th derivative by `‖A‖`. -/
theorem IteratedFDerivLipschitzOn.continuousLinearMap_comp (A : F →L[ℝ] G)
    (hf : IteratedFDerivLipschitzOn f j L C) (hfC : ∀ y ∈ C, ContDiffAt ℝ j f y) :
    IteratedFDerivLipschitzOn (A ∘ f) j (‖A‖ * L) C := by
  rw [iteratedFDerivLipschitzOn_iff] at *
  intro y hy z hz
  have hsub : ∀ X Y : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F,
      A.compContinuousMultilinearMap X - A.compContinuousMultilinearMap Y =
        A.compContinuousMultilinearMap (X - Y) := fun X Y => by ext; simp
  rw [A.iteratedFDeriv_comp_left (hfC y hy) le_rfl, A.iteratedFDeriv_comp_left (hfC z hz) le_rfl,
    hsub, mul_assoc]
  exact (A.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (hf y hy z hz) (norm_nonneg A))

/-- A larger constant is still a Hölder constant. -/
theorem IteratedFDerivHolderOn.mono_const {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} {p : ℕ} {H H' β : ℝ} {C : Set E}
    (h : IteratedFDerivHolderOn g p H β C) (hH : H ≤ H') : IteratedFDerivHolderOn g p H' β C :=
  fun x hx y hy => (h x hx y hy).trans
    (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg _) _))

/-- Hölder constants of `p`-th derivatives (`p ≥ 1`) of `C^p` functions combine linearly under
nonnegative combinations, and adding a constant does not change them: if `∇^p g₁`, `∇^p g₂` are
`(H₁, β)`- and `(H₂, β)`-Hölder on `C`, then `∇^p (a g₁ + b g₂ + e)` is `(a H₁ + b H₂, β)`-Hölder
for `a, b ≥ 0`. -/
theorem IteratedFDerivHolderOn.smul_add_smul_add_const {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g₁ g₂ : E → G} {p : ℕ} {H₁ H₂ β a b : ℝ} {C : Set E} (hp : p ≠ 0)
    (hg₁ : ∀ x ∈ C, ContDiffAt ℝ p g₁ x) (hg₂ : ∀ x ∈ C, ContDiffAt ℝ p g₂ x)
    (h₁ : IteratedFDerivHolderOn g₁ p H₁ β C) (h₂ : IteratedFDerivHolderOn g₂ p H₂ β C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (e : G) :
    IteratedFDerivHolderOn (fun x => a • g₁ x + b • g₂ x + e) p (a * H₁ + b * H₂) β C := by
  have hD : ∀ x ∈ C, iteratedFDeriv ℝ p (fun x => a • g₁ x + b • g₂ x + e) x =
      a • iteratedFDeriv ℝ p g₁ x + b • iteratedFDeriv ℝ p g₂ x := by
    intro x hx
    have k₁ : ContDiffAt ℝ p (a • g₁) x := (hg₁ x hx).const_smul a
    have k₂ : ContDiffAt ℝ p (b • g₂) x := (hg₂ x hx).const_smul b
    have k₃ : ContDiffAt ℝ p (a • g₁ + b • g₂) x := k₁.add k₂
    have hfun : (fun x => a • g₁ x + b • g₂ x + e) = (a • g₁ + b • g₂) + fun _ => e := rfl
    rw [hfun, iteratedFDeriv_add_apply k₃ contDiffAt_const,
      iteratedFDeriv_add_apply k₁ k₂, iteratedFDeriv_const_smul_apply (hg₁ x hx),
      iteratedFDeriv_const_smul_apply (hg₂ x hx), iteratedFDeriv_const_of_ne hp, Pi.zero_apply,
      add_zero]
  intro x hx y hy
  rw [hD x hx, hD y hy, add_sub_add_comm, ← smul_sub, ← smul_sub, add_mul, mul_assoc, mul_assoc]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h₁ x hx y hy) ha
  · rw [norm_smul, Real.norm_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (h₂ x hx y hy) hb

end LipschitzAlgebra
