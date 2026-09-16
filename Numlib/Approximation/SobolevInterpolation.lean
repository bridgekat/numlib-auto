import Numlib.Approximation.Interpolation
import Numlib.Analysis.Sobolev.Interval

/-!
# Piecewise Lagrange interpolation in `L²` and `H^m` seminorms

The error of piecewise polynomial interpolation of degree `k` on a partition of mesh `h`, measured
in the `L²` norms of the derivatives of order `m ≤ k` rather than in the supremum norm:
`‖(f - Π_h^k f)^{(m)}‖_{L²(a,b)} ≤ h^{k+1-m} ‖f^{(k+1)}‖_{L²(a,b)}`. This is
[quarteroni2000numerical] Theorem 8.3 (proved there for `k = 1`, (8.27)), the approximation
estimate behind the convergence of the `P_k` finite element method in one dimension. The constant is
`1` for every `k` and `m`, sharper than the book's unspecified `C`.

## The proof, and why no Sobolev space appears in the core statements

On one panel `[u, v]` of length at most `h`, let `e = f - p` with `p` the interpolant at `k + 1`
distinct nodes of the panel. The generalized Rolle theorem
(`exists_iteratedDeriv_eq_zero_of_forall_eq_zero`, `Numlib/Approximation/Interpolation`) gives zeros
`ξ_j` of `e^{(j)}` in the panel for every `j ≤ k`. Since `p^{(k+1)} = 0`, `e^{(k)}(t) = ∫_{ξ_k}^t g`
where `g` is the `(k+1)`-st derivative of `f`, so by Cauchy–Schwarz
`|e^{(k)}(t)| ≤ √h ‖g‖_{L²(u,v)}`, and each of the `k - m` integrations `e^{(j)}(t) = ∫_{ξ_j}^t
e^{(j+1)}` gains a factor `h`. Squaring and integrating over the panel gives
`∫_u^v |e^{(m)}|² ≤ h^{2(k+1-m)} ∫_u^v g²`, and summing over the panels gives the theorem. Nothing
in this uses more of `f` than: `f` is `C^k` and `f^{(k)}(t) - f^{(k)}(s) = ∫_s^t g` for a square
integrable `g` — the *absolutely continuous representative* of an `H^{k+1}(a, b)` function. The core
statements (`abs_iteratedDeriv_sub_le`, `integral_sq_iteratedDeriv_sub_le`,
`sum_integral_sq_sub_panelPoly_le`, `integral_sq_sub_piecewisePolyInterpCLM_le`,
`integral_sq_deriv_sub_piecewisePolyInterpCLM_le`, `integral_sq_sub_piecewiseLinearInterpCLM_le`,
`integral_sq_deriv_sub_piecewiseLinearInterpCLM_le`) take exactly that hypothesis;
`SobolevInterval.exists_contDiff_ae_eq` produces it from an element of `H^{k+1}(a, b)` of
`Numlib/Analysis/Sobolev/Interval`, and `sobolevSeminorm_sub_piecewisePolyInterp_le`,
`integral_sq_sub_piecewisePolyInterpCLM_le_seminorm` restate the theorem for such an element, with
the `H^{k+1}` seminorm `SobolevInterval.seminorm` on the right.

## Conventions

The interpolant on the panel `j` is `panelPoly node j F : ℝ[X]` from
`Numlib/Approximation/Interpolation`, where `F : C(Icc a b, ℝ)` is the restriction of `f`; the
broken-norm sum `∑_j ∫_{x_j}^{x_{j+1}} |f^{(m)} - (panelPoly node j F)^{(m)}|²` is the statement for
all `m ≤ k`, and for `m = 0, 1` it is the honest `L²(a, b)` norm of `(f - Π_h^k f)^{(m)}`, which
`integral_sq_sub_piecewisePolyInterpCLM_le` and `integral_sq_deriv_sub_piecewisePolyInterpCLM_le`
state through `piecewisePolyInterpCLM`. The square integrability of `g` is carried as the two
hypotheses `IntervalIntegrable g` and `IntervalIntegrable (g ^ 2)`: with the first alone the
right-hand side `∫ g²` could be the junk value `0` of a non-integrable function.
-/

open Polynomial MeasureTheory intervalIntegral Set
open scoped Interval Topology

/-! ### The panel estimates -/

/-- **The pointwise panel estimate** ([quarteroni2000numerical] (8.30)–(8.31) for general `k`): on a
panel `[u, v]` of length at most `h`, if `p` of degree `≤ k` interpolates `f` at `k + 1` distinct
points of the panel, `f` is `C^k` and `f^{(k)}(t) - f^{(k)}(s) = ∫_s^t g` on the panel with `g`
square integrable, then for `m ≤ k` and `t` in the panel
`|f^{(m)}(t) - p^{(m)}(t)| ≤ h^{k-m} √h ‖g‖_{L²(u,v)}`. Downward induction on `m` from `m = k`:
the generalized Rolle theorem gives a zero `ξ_j` of `e^{(j)} = (f - p)^{(j)}` in the panel for every
`j ≤ k`; `e^{(k)}(t) = ∫_{ξ_k}^t g` since `p^{(k)}` is constant, which Cauchy–Schwarz bounds by
`√h ‖g‖_{L²(u,v)}`, and `e^{(m)}(t) = ∫_{ξ_m}^t e^{(m+1)}` gains a factor `h` each time. -/
theorem abs_iteratedDeriv_sub_le {k m : ℕ} {u v h : ℝ} (huv : u < v) (hh : v - u ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ k f) (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume u v)
    (hfg : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {p : ℝ[X]} (hp : p.degree ≤ k) {y : Fin (k + 1) → ℝ} (hy : Function.Injective y)
    (hymem : ∀ i, y i ∈ Icc u v) (hpy : ∀ i, p.eval (y i) = f (y i)) (hm : m ≤ k) {t : ℝ}
    (ht : t ∈ Icc u v) :
    |iteratedDeriv m f t - (derivative^[m] p).eval t|
      ≤ h ^ (k - m) * √h * √(∫ t in u..v, g t ^ 2) := by
  have h0 : 0 ≤ h := (sub_pos.2 huv).le.trans hh
  set e : ℝ → ℝ := fun t => f t - p.eval t with he_def
  have he : ContDiff ℝ k e := hf.sub (contDiff_eval p k)
  have heval : ∀ j ≤ k, ∀ t,
      iteratedDeriv j e t = iteratedDeriv j f t - (derivative^[j] p).eval t := by
    intro j hj t
    rw [he_def, iteratedDeriv_fun_sub (hf.contDiffAt.of_le (by exact_mod_cast hj))
      ((contDiff_eval p k).contDiffAt.of_le (by exact_mod_cast hj)), iteratedDeriv_eval]
  -- the zeros of the derivatives of the error, by the generalized Rolle theorem
  have hzero : ∀ j ≤ k, ∃ ξ ∈ Icc u v, iteratedDeriv j e ξ = 0 := by
    intro j hj
    cases j with
    | zero => exact ⟨y 0, hymem 0, by simp [he_def, hpy]⟩
    | succ i =>
      obtain ⟨c, hc, hc0⟩ := exists_iteratedDeriv_eq_zero_of_forall_eq_zero
        (he.of_le (by exact_mod_cast hj)) (s := Finset.univ.image y)
        (by rw [Finset.card_image_of_injective _ hy, Finset.card_univ, Fintype.card_fin]; omega)
        (fun t ht => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; exact hymem i)
        (fun t ht => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; simp [he_def, hpy])
      exact ⟨c, Ioo_subset_Icc_self hc, hc0⟩
  -- the top derivative of `p` is constant
  have hpk : ∀ s t, (derivative^[k] p).eval s = (derivative^[k] p).eval t := by
    intro s t
    have : (derivative^[k] p).natDegree ≤ 0 :=
      (natDegree_iterate_derivative p k).trans (by
        have := natDegree_le_of_degree_le hp; omega)
    rw [eq_C_of_natDegree_le_zero this, eval_C, eval_C]
  -- downward induction
  suffices H : ∀ d j, j + d = k → ∀ t ∈ Icc u v,
      |iteratedDeriv j e t| ≤ h ^ (k - j) * √h * √(∫ t in u..v, g t ^ 2) by
    rw [← heval m hm]
    exact H (k - m) m (by omega) t ht
  intro d
  induction d with
  | zero =>
    intro j hj t ht
    obtain rfl : k = j := by omega
    obtain ⟨ξ, hξ, hξ0⟩ := hzero k le_rfl
    have : iteratedDeriv k e t = ∫ r in ξ..t, g r := by
      rw [← sub_zero (iteratedDeriv k e t), ← hξ0, heval k le_rfl, heval k le_rfl, hpk ξ t,
        ← hfg ξ hξ t ht]
      ring
    rw [this, Nat.sub_self, pow_zero, one_mul]
    exact (abs_intervalIntegral_le_sqrt_mul_sqrt huv.le hg hg2 hξ ht).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _))
  | succ d ih =>
    intro j hj t ht
    have hjk : j < k := by omega
    have ih' := ih (j + 1) (by omega)
    obtain ⟨ξ, hξ, hξ0⟩ := hzero j hjk.le
    -- the fundamental theorem of calculus for `e^{(j)}`
    have hderiv : ∀ x, HasDerivAt (iteratedDeriv j e) (iteratedDeriv (j + 1) e x) x := fun x => by
      rw [iteratedDeriv_succ]
      exact (he.differentiable_iteratedDeriv j (by exact_mod_cast hjk) x).hasDerivAt
    have hcont : Continuous (iteratedDeriv (j + 1) e) :=
      he.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hjk)
    have hftc : iteratedDeriv j e t = ∫ r in ξ..t, iteratedDeriv (j + 1) e r := by
      rw [integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont.intervalIntegrable _ _), hξ0,
        sub_zero]
    -- the bound on the integrand, over an interval of length at most `h`
    have hbound : ∀ x ∈ Ι ξ t, ‖iteratedDeriv (j + 1) e x‖
        ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) := fun x hx =>
      ih' x (Icc_subset_Icc (le_min hξ.1 ht.1) (max_le hξ.2 ht.2) (Ioc_subset_Icc_self hx))
    have hlen : |t - ξ| ≤ h := by
      rw [abs_sub_le_iff]; constructor <;> linarith [hξ.1, hξ.2, ht.1, ht.2]
    calc |iteratedDeriv j e t| = ‖∫ r in ξ..t, iteratedDeriv (j + 1) e r‖ := by
          rw [hftc, Real.norm_eq_abs]
      _ ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) * |t - ξ| :=
          norm_integral_le_of_norm_le_const hbound
      _ ≤ h ^ (k - (j + 1)) * √h * √(∫ t in u..v, g t ^ 2) * h :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = h ^ (k - j) * √h * √(∫ t in u..v, g t ^ 2) := by
          rw [show k - j = k - (j + 1) + 1 by omega, pow_succ]; ring

/-- **The panel estimate** ([quarteroni2000numerical] Theorem 8.3 on one panel, constant `1`): under
the hypotheses of `abs_iteratedDeriv_sub_le`,
`∫_u^v |f^{(m)} - p^{(m)}|² ≤ h^{2(k+1-m)} ∫_u^v g²` for every `m ≤ k`. (For `m = k + 1` the
statement would be the trivial `∫ g² ≤ ∫ g²`.) -/
theorem integral_sq_iteratedDeriv_sub_le {k m : ℕ} {u v h : ℝ} (huv : u < v) (hh : v - u ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ k f) (hg : IntervalIntegrable g volume u v)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume u v)
    (hfg : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {p : ℝ[X]} (hp : p.degree ≤ k) {y : Fin (k + 1) → ℝ} (hy : Function.Injective y)
    (hymem : ∀ i, y i ∈ Icc u v) (hpy : ∀ i, p.eval (y i) = f (y i)) (hm : m ≤ k) :
    ∫ t in u..v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * ∫ t in u..v, g t ^ 2 := by
  have h0 : 0 ≤ h := (sub_pos.2 huv).le.trans hh
  have hI : 0 ≤ ∫ t in u..v, g t ^ 2 := integral_nonneg huv.le fun _ _ => sq_nonneg _
  set C := h ^ (k - m) * √h * √(∫ t in u..v, g t ^ 2) with hC
  have hpt : ∀ t ∈ Icc u v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2 ≤ C ^ 2 :=
    fun t ht => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_iteratedDeriv_sub_le huv hh hf hg hg2 hfg hp hy hymem hpy hm ht) 2
  have hcont : Continuous fun t => (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2 :=
    ((hf.continuous_iteratedDeriv m (by exact_mod_cast hm)).sub
      (Polynomial.continuous _)).pow 2
  calc ∫ t in u..v, (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ ∫ _ in u..v, C ^ 2 :=
        integral_mono_on huv.le (hcont.intervalIntegrable _ _) intervalIntegrable_const hpt
    _ = (v - u) * C ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ h * C ^ 2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _ = h ^ (2 * (k + 1 - m)) * ∫ t in u..v, g t ^ 2 := by
        rw [hC, mul_pow, mul_pow, Real.sq_sqrt h0, Real.sq_sqrt hI, ← pow_mul,
          show 2 * (k + 1 - m) = 2 * (k - m) + 1 + 1 by omega, pow_succ, pow_succ]
        ring

/-! ### Theorem 8.3 -/

/-- **Theorem 8.3 in broken form, constant `1`** ([quarteroni2000numerical] Theorem 8.3): for a
panel node system of degree `k` on `a = x 0 < ⋯ < x (n + 1) = b` whose panels have length at most
`h`,
`f` of class `C^k` with `f^{(k)}(t) - f^{(k)}(s) = ∫_s^t g` on `[a, b]`, `g` square integrable, `F`
the restriction of `f` to `[a, b]`, and `m ≤ k`:
`∑_j ∫_{x_j}^{x_{j+1}} |f^{(m)} - (Π_h^k f)^{(m)}|² ≤ h^{2(k+1-m)} ∫_a^b g²`, where on the panel `j`
the interpolant `Π_h^k f` is the polynomial `panelPoly node j F`. The panel estimate
`integral_sq_iteratedDeriv_sub_le`, summed over the panels. -/
theorem sum_integral_sq_sub_panelPoly_le {a b : ℝ} {n k m : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) (hm : m ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * ∫ t in a..b, g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- the right-hand side over the whole interval is the sum over the panels
  have hsplit : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ =>
      hg2.mono_set (hsub' j)]
    simp only [hnode.first, hnode.last]
  rw [hsplit, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine integral_sq_iteratedDeriv_sub_le (hnode.step j hj) (hmesh j hj) hf (hg.mono_set (hsub' j))
    (hg2.mono_set (hsub' j)) (fun s hs t ht => hfg s (hsub j s hs) t (hsub j t ht)) ?_
    (hnode.injective j hj) (hnode.mem j hj) (fun i => ?_) hm
  · refine (Lagrange.degree_interpolate_le _ (hnode.injective j hj).injOn).trans ?_
    simp
  · rw [panelPoly, Lagrange.eval_interpolate_at_node _ (hnode.injective j hj).injOn
      (Finset.mem_univ i), hF]

section PiecewisePolynomial

variable {a b : ℝ} {n k : ℕ} {x : ℕ → Icc a b} {node : ℕ → Fin (k + 1) → Icc a b}

/-- **Theorem 8.3 for `m = 0`, in `L²(a, b)`** ([quarteroni2000numerical] (8.26) with `m = 0` and
`C = 1`): under the hypotheses of `sum_integral_sq_sub_panelPoly_le`, for any function `G` agreeing
on `[a, b]` with the piecewise polynomial interpolant
`Π_h^k f = piecewisePolyInterpCLM n k x node F`, `∫_a^b |f - G|² ≤ h^{2(k+1)} ∫_a^b g²`. -/
theorem integral_sq_sub_piecewisePolyInterpCLM_le (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewisePolyInterpCLM n k x node F t) :
    ∫ t in a..b, (f t - G t) ^ 2 ≤ h ^ (2 * (k + 1)) * ∫ t in a..b, g t ^ 2 := by
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  -- on a panel, `G` is the panel polynomial
  have hpanel : ∀ j ≤ n, EqOn (fun t => (f t - G t) ^ 2)
      (fun t => (iteratedDeriv 0 f t - (derivative^[0] (panelPoly node j F)).eval t) ^ 2)
      (Icc (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
    rw [hG ⟨t, hsub j t ht⟩, piecewisePolyInterpCLM_apply_of_mem hnode F hj ht.1 ht.2]
  have hint : ∀ j ≤ n, IntervalIntegrable (fun t => (f t - G t) ^ 2) volume (x j) (x (j + 1)) :=
    fun j hj => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hnode.step j hj).le]
      refine ContinuousOn.integrableOn_Icc ?_
      exact ((((hf.continuous.sub (Polynomial.continuous _)).pow 2).continuousOn).congr
        (hpanel j hj))
  have hsplit : ∫ t in a..b, (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j hj =>
      hint j (Nat.lt_succ_iff.1 hj)]
    simp only [hnode.first, hnode.last]
  rw [hsplit]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv 0 f t - (derivative^[0] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr ((uIcc_of_le
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le).symm ▸
          hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ h ^ (2 * (k + 1 - 0)) * ∫ t in a..b, g t ^ 2 :=
        sum_integral_sq_sub_panelPoly_le hnode hmesh hf hg hg2 hfg hF (Nat.zero_le k)
    _ = h ^ (2 * (k + 1)) * ∫ t in a..b, g t ^ 2 := by rw [Nat.sub_zero]

/-- **Theorem 8.3 for `m = 1`** ([quarteroni2000numerical] (8.26) with `m = 1` and `C = 1`): under
the hypotheses of `sum_integral_sq_sub_panelPoly_le` with `1 ≤ k`, for any function `G` agreeing on
`[a, b]` with the piecewise polynomial interpolant, the panelwise `L²` norms of `f' - G'` satisfy
`∑_j ∫_{x_j}^{x_{j+1}} |f' - G'|² ≤ h^{2k} ∫_a^b g²`. Inside a panel `G` is the panel polynomial, so
`G'` is its derivative there; the values of `G'` at the breakpoints do not affect the integrals. -/
theorem integral_sq_deriv_sub_piecewisePolyInterpCLM_le (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ k f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewisePolyInterpCLM n k x node F t) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (deriv f t - deriv G t) ^ 2
      ≤ h ^ (2 * k) * ∫ t in a..b, g t ^ 2 := by
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  -- inside a panel, `G'` is the derivative of the panel polynomial
  have hpanel : ∀ j ≤ n, EqOn (fun t => (deriv f t - deriv G t) ^ 2)
      (fun t => (iteratedDeriv 1 f t - (derivative^[1] (panelPoly node j F)).eval t) ^ 2)
      (Ioo (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    have hev : G =ᶠ[𝓝 t] fun s => (panelPoly node j F).eval s := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      rw [hG ⟨s, hsub j s hs⟩, piecewisePolyInterpCLM_apply_of_mem hnode F hj hs.1 hs.2]
    simp only [iteratedDeriv_one, Function.iterate_one]
    rw [hev.deriv_eq, Polynomial.deriv]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (deriv f t - deriv G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv 1 f t - (derivative^[1] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr_Ioo
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le
          (hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ h ^ (2 * (k + 1 - 1)) * ∫ t in a..b, g t ^ 2 :=
        sum_integral_sq_sub_panelPoly_le hnode hmesh hf hg hg2 hfg hF hk
    _ = h ^ (2 * k) * ∫ t in a..b, g t ^ 2 := by rw [Nat.add_sub_cancel]

end PiecewisePolynomial

section PiecewiseLinear

variable {a b : ℝ} {n : ℕ} {x : ℕ → Icc a b}

/-- The affine interpolant of `f` on `[u, v]`, as a polynomial: its degree, its values, and its
derivative. -/
private theorem exists_linear_interp {u v : ℝ} (huv : u < v) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], p.degree ≤ 1 ∧ (∀ t, p.eval t = f u + (f v - f u) * ((t - u) / (v - u))) ∧
      (∀ t, (derivative p).eval t = (f v - f u) / (v - u)) ∧ p.eval u = f u ∧ p.eval v = f v := by
  have hne : v - u ≠ 0 := sub_ne_zero.2 huv.ne'
  set β := (f v - f u) / (v - u) with hβ
  have heval : ∀ t,
      (C β * X + C (f u - β * u)).eval t = f u + (f v - f u) * ((t - u) / (v - u)) := by
    intro t
    simp only [eval_add, eval_mul, eval_C, eval_X, hβ]
    field_simp
    ring
  refine ⟨C β * X + C (f u - β * u), degree_linear_le, heval, fun t => ?_, ?_, ?_⟩
  · simp [derivative_mul]
  · rw [heval, sub_self, zero_div, mul_zero, add_zero]
  · rw [heval, div_self hne, mul_one, add_sub_cancel]

/-- The panel estimate for the piecewise linear interpolant: on the panel `j`, the affine
interpolant `p` through `(x j, f (x j))` and `(x (j+1), f (x (j+1)))` satisfies
`∫ |f^{(m)} - p^{(m)}|² ≤ h^{2(2-m)} ∫ g²` for `m ≤ 1`. -/
private theorem integral_sq_sub_linear_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r) {j : ℕ}
    (hj : j ≤ n) {p : ℝ[X]} (hp : p.degree ≤ 1) (hpu : p.eval (x j : ℝ) = f (x j))
    (hpv : p.eval (x (j + 1) : ℝ) = f (x (j + 1))) {m : ℕ} (hm : m ≤ 1) :
    ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (iteratedDeriv m f t - (derivative^[m] p).eval t) ^ 2
      ≤ h ^ (2 * (1 + 1 - m)) * ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  have hlt := hstep j hj
  refine integral_sq_iteratedDeriv_sub_le (k := 1) hlt (hmesh j hj) hf (hg.mono_set hsub')
    (hg2.mono_set hsub') (fun s hs t ht => by
      simpa only [iteratedDeriv_one] using hfg s (hsub s hs) t (hsub t ht))
    (by exact_mod_cast hp) (y := ![(x j : ℝ), (x (j + 1) : ℝ)]) ?_ ?_ ?_ hm
  · intro i i' hii'
    fin_cases i <;> fin_cases i' <;> simp_all [hlt.ne, hlt.ne']
  · intro i
    fin_cases i
    · exact left_mem_Icc.2 hlt.le
    · exact right_mem_Icc.2 hlt.le
  · intro i
    fin_cases i
    · exact hpu
    · exact hpv

/-- **(8.27) of [quarteroni2000numerical] with `C₁ = 1`**: on a partition
`a = x 0 < ⋯ < x (n+1) = b` of mesh at most `h`, for `f` of class `C¹` with
`f'(t) - f'(s) = ∫_s^t g` on `[a, b]` and `g` square integrable, `F` the restriction of `f` and `G`
any function agreeing on `[a, b]` with the piecewise linear interpolant
`Π_h^1 f = piecewiseLinearInterpCLM n x F`: `∫_a^b |f - G|² ≤ h⁴ ∫_a^b g²`. -/
theorem integral_sq_sub_piecewiseLinearInterpCLM_le (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r)
    {F : C(Icc a b, ℝ)} (hF : ∀ t, F t = f t) {G : ℝ → ℝ}
    (hG : ∀ t : Icc a b, G t = piecewiseLinearInterpCLM n x F t) :
    ∫ t in a..b, (f t - G t) ^ 2 ≤ h ^ 4 * ∫ t in a..b, g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub : ∀ j, ∀ s ∈ Icc (x j : ℝ) (x (j + 1) : ℝ), s ∈ Icc a b := fun j s hs =>
    ⟨(x j).2.1.trans hs.1, hs.2.trans (x (j + 1)).2.2⟩
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  -- the affine interpolants of the panels
  choose p hp hpeval _hpderiv hpu hpv using fun j (hj : j ≤ n) =>
    exists_linear_interp (hstep j hj) f
  have hpanel : ∀ j (hj : j ≤ n), EqOn (fun t => (f t - G t) ^ 2)
      (fun t => (iteratedDeriv 0 f t - (derivative^[0] (p j hj)).eval t) ^ 2)
      (Icc (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
    rw [hG ⟨t, hsub j t ht⟩, piecewiseLinearInterpCLM_apply_of_mem hstep F hj ht.1 ht.2, hpeval,
      hF, hF]
  have hint : ∀ j ≤ n, IntervalIntegrable (fun t => (f t - G t) ^ 2) volume (x j) (x (j + 1)) :=
    fun j hj => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hstep j hj).le]
      exact ContinuousOn.integrableOn_Icc
        ((((hf.continuous.sub (Polynomial.continuous _)).pow 2).continuousOn).congr (hpanel j hj))
  have hsplit : ∫ t in a..b, (f t - G t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), (f t - G t) ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j hj =>
      hint j (Nat.lt_succ_iff.1 hj)]
    simp only [hfirst, hlast]
  have hsplit' : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ => hg2.mono_set (hsub' j)]
    simp only [hfirst, hlast]
  rw [hsplit, hsplit', Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [integral_congr ((uIcc_of_le (hstep j hj).le).symm ▸ hpanel j hj)]
  exact integral_sq_sub_linear_le hstep hmesh hf hg hg2 hfg hj (hp j hj) (hpu j hj) (hpv j hj)
    (Nat.zero_le 1)

/-- **(8.27) of [quarteroni2000numerical] with `C₂ = 1`**: under the hypotheses of
`integral_sq_sub_piecewiseLinearInterpCLM_le`, the panelwise `L²` norms of `f' - (Π_h^1 f)'`, the
derivative of the interpolant on the panel `j` being the difference quotient
`(f (x (j+1)) - f (x j))/(x (j+1) - x j)`, satisfy
`∑_j ∫_{x_j}^{x_{j+1}} |f' - (Π_h^1 f)'|² ≤ h² ∫_a^b g²`. -/
theorem integral_sq_deriv_sub_piecewiseLinearInterpCLM_le
    (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) {h : ℝ} (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, deriv f t - deriv f s = ∫ r in s..t, g r) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (deriv f t - (f (x (j + 1)) - f (x j)) / ((x (j + 1) : ℝ) - (x j : ℝ))) ^ 2
      ≤ h ^ 2 * ∫ t in a..b, g t ^ 2 := by
  have hab : a ≤ b := (x 0).2.1.trans (x 0).2.2
  have hsub' : ∀ j, [[(x j : ℝ), (x (j + 1) : ℝ)]] ⊆ [[a, b]] := fun j => by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc (x j).2 (x (j + 1)).2
  choose p hp _hpeval hpderiv hpu hpv using fun j (hj : j ≤ n) =>
    exists_linear_interp (hstep j hj) f
  have hsplit' : ∫ t in a..b, g t ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ), g t ^ 2 := by
    rw [sum_integral_adjacent_intervals (a := fun j => (x j : ℝ)) fun j _ => hg2.mono_set (hsub' j)]
    simp only [hfirst, hlast]
  rw [hsplit', Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := integral_sq_sub_linear_le hstep hmesh hf hg hg2 hfg hj (hp j hj) (hpu j hj) (hpv j hj)
    le_rfl
  simpa only [iteratedDeriv_one, Function.iterate_one, hpderiv] using this

end PiecewiseLinear

/-! ### Theorem 8.3 over `H^{k+1}(a, b)` -/

section Sobolev

variable {a b : ℝ}

open SobolevInterval in
/-- **Theorem 8.3 over `H^{k+1}(a, b)`, broken form** ([quarteroni2000numerical] (8.26) with
`C = 1`): for `u ∈ H^{k+1}(a, b)` with continuous representative `F` (any `F : C([a, b], ℝ)`
agreeing with `u` almost everywhere), a panel node system of degree `k` of mesh at most `h`, and
`m ≤ k`, the panelwise `L²` norms of `(F - Π_h^k F)^{(m)}` satisfy
`∑_j ∫_{x_j}^{x_{j+1}} |F^{(m)} - (Π_h^k F)^{(m)}|² ≤ h^{2(k+1-m)} |u|²_{H^{k+1}(a, b)}`, where
`F^{(m)}` is the `m`-th derivative of `F` extended by its endpoint values — inside `(a, b)` it is
the `m`-th derivative of the `C^k` representative of `u`, `SobolevInterval.exists_contDiff_ae_eq` —
and
on the panel `j` the interpolant is `panelPoly node j F`. For `m = 0, 1` the left side is the
`L²(a, b)` norm of `(F - Π_h^k F)^{(m)}`, i.e. the `H^m(a, b)` seminorm of the error;
`integral_sq_sub_piecewisePolyInterpCLM_le_seminorm` states the case `m = 0` on `[a, b]`. -/
theorem sobolevSeminorm_sub_piecewisePolyInterp_le (hab : a < b) {k : ℕ}
    (u : SobolevInterval (k + 1) a b) {n : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {F : C(Icc a b, ℝ)}
    (hF : fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le F) {m : ℕ} (hm : m ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m (IccExtend hab.le F) t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      ≤ h ^ (2 * (k + 1 - m)) * seminorm (k + 1) a b u ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := exists_contDiff_ae_eq hab u
  have hf0 : fn u =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [← deriv_zero u]; simpa using hae 0
  -- the continuous representative is the `C^k` representative on `[a, b]`
  have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
    eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
      (hF.symm.trans hf0)
  have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
  have hpanel : ∀ j ≤ n, EqOn
      (fun t => (iteratedDeriv m (IccExtend hab.le F) t
        - (derivative^[m] (panelPoly node j F)).eval t) ^ 2)
      (fun t => (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2)
      (Ioo (x j : ℝ) (x (j + 1) : ℝ)) := by
    intro j hj t ht
    have hev : IccExtend hab.le F =ᶠ[𝓝 t] f := by
      filter_upwards [Icc_mem_nhds ((x j).2.1.trans_lt ht.1) (ht.2.trans_le (x (j + 1)).2.2)]
        with s hs using hFf hs
    simp only [hev.iteratedDeriv_eq m]
  rw [seminorm_sq_eq_integral hab.le]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
        (iteratedDeriv m (IccExtend hab.le F) t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (x j : ℝ)..(x (j + 1) : ℝ),
          (iteratedDeriv m f t - (derivative^[m] (panelPoly node j F)).eval t) ^ 2 :=
        Finset.sum_congr rfl fun j hj => integral_congr_Ioo
          (hnode.step j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).le
          (hpanel j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    _ ≤ _ := sum_integral_sq_sub_panelPoly_le hnode hmesh hf (intervalIntegrable_deriv hab.le u _)
        (intervalIntegrable_deriv_sq hab.le u _) hftc hF' hm

open SobolevInterval in
/-- **Theorem 8.3 over `H^{k+1}(a, b)` in `L²(a, b)`** ([quarteroni2000numerical] (8.26) with
`m = 0` and `C = 1`): for `u ∈ H^{k+1}(a, b)` with continuous representative `F` and a panel node
system of degree `k` of mesh at most `h`,
`‖F - Π_h^k F‖²_{L²(a, b)} ≤ h^{2(k+1)} |u|²_{H^{k+1}(a, b)}`. -/
theorem integral_sq_sub_piecewisePolyInterpCLM_le_seminorm (hab : a < b) {k : ℕ}
    (u : SobolevInterval (k + 1) a b) {n : ℕ} {x : ℕ → Icc a b}
    {node : ℕ → Fin (k + 1) → Icc a b} (hnode : IsPanelNodes n k x node) {h : ℝ}
    (hmesh : ∀ j ≤ n, (x (j + 1) : ℝ) - (x j : ℝ) ≤ h) {F : C(Icc a b, ℝ)}
    (hF : fn u =ᵐ[volume.restrict (Ioo a b)] IccExtend hab.le F) :
    ∫ t in a..b,
        (IccExtend hab.le F t - IccExtend hab.le (piecewisePolyInterpCLM n k x node F) t) ^ 2
      ≤ h ^ (2 * (k + 1)) * seminorm (k + 1) a b u ^ 2 := by
  obtain ⟨f, hf, hae, hftc⟩ := exists_contDiff_ae_eq hab u
  have hf0 : fn u =ᵐ[volume.restrict (Ioo a b)] f := by
    rw [← deriv_zero u]; simpa using hae 0
  have hFf : EqOn (IccExtend hab.le F) f (Icc a b) :=
    eqOn_Icc_of_ae_eq hab F.continuous.Icc_extend'.continuousOn hf.continuous.continuousOn
      (hF.symm.trans hf0)
  have hF' : ∀ t, F t = f t := fun t => by rw [← IccExtend_val hab.le F t, hFf t.2]
  rw [seminorm_sq_eq_integral hab.le, integral_congr_Ioo hab.le
    (h := fun t => (f t - IccExtend hab.le (piecewisePolyInterpCLM n k x node F) t) ^ 2)
    (fun t ht => by simp only [hFf (Ioo_subset_Icc_self ht)])]
  exact integral_sq_sub_piecewisePolyInterpCLM_le hnode hmesh hf
    (intervalIntegrable_deriv hab.le u _) (intervalIntegrable_deriv_sq hab.le u _) hftc hF'
    fun t => IccExtend_val hab.le _ t

end Sobolev
