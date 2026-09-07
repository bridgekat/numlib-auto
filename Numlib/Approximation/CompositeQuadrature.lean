import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Numlib.Approximation.Quadrature

/-!
# Composite quadrature rules

A *composite* rule applies one fixed rule to each panel of a partition of an interval. Unlike the
rules of `Numlib/Approximation/Quadrature`, whose degree of exactness has to grow for the
Szegő–Pólya criterion to apply, a composite rule keeps a fixed panel rule and converges because the
mesh tends to zero. This file has the rule, the convergence theorem with its explicit modulus of
continuity bound, and the mean value form of the composite trapezoidal error.

## Main definitions

* `Quadrature.composite` is a rule of `N` panels of `m` nodes, as one `Fin (N * m)`-indexed
  `Quadrature.functional`.
* `Quadrature.trapezoidSum g a h N` is the composite trapezoidal sum
  `h (g(x₀)/2 + g(x₁) + ⋯ + g(x_{N-1}) + g(x_N)/2)` on the uniform mesh `x_j = a + j h`, and
  `Quadrature.simpsonSum` the composite Simpson sum on the same mesh.
* `Quadrature.circleTrapezoid T n` is the periodic trapezoidal rule on `AddCircle T`, as a
  `Quadrature.functional`.

## Main results

* `Quadrature.abs_sub_compositeSum_le`, the **Riemann sum bound**: a panel rule with nonnegative
  weights summing to one, applied on a partition of mesh at most `h`, differs from the integral by
  at most `(b - a) ε`, where `ε` bounds the oscillation of the integrand over distances `h`. This
  is the reason a composite rule converges for *every* continuous integrand, and it is what
  `Quadrature.tendsto_compositeSum` turns into a limit.
* `Quadrature.tendsto_trapezoidSum` and `Quadrature.tendsto_simpsonSum`, the convergence of the
  two classical composite rules on a uniform mesh, and `Quadrature.tendsto_circleTrapezoid`, the
  convergence of the periodic trapezoidal rule for every continuous integrand on `AddCircle T` —
  the hypothesis a Nyström method for a boundary integral equation asks of its quadrature rules.
* `Quadrature.sub_trapezoid_eq_integral_peanoKernel`, the one-panel Peano identity
  `∫_α^β g - (β - α)(g(α) + g(β))/2 = ∫_α^β (t - α)(t - β) g''(t)/2 dt`, and
  `Quadrature.sub_composite_trapezoid_eq`, the composite mean value form
  `∫_a^b g - h(g(x₀)/2 + ⋯ + g(x_N)/2) = -h² (b - a) g''(ξ)/12`.
* `Quadrature.abs_sub_trapezoidSum_add_le`, the Euler–Maclaurin form of the same error:
  `-(h²/12) [g'(b) - g'(a)]` up to `(b - a) h⁴ ‖g⁗‖_∞ / 720`.  Two further integrations by parts
  of the Peano identity give it, `Quadrature.integral_peanoKernel_mul_eq`, and it is the form that
  justifies Richardson extrapolation.
* `Quadrature.sub_simpson_eq_integral_peanoKernel`, the one-panel Peano identity for Simpson's
  rule, whose kernel is the *piecewise* cubic `(t - α)³(3t - α - 2β)/72` on the left half of the
  panel and its mirror image on the right, and `Quadrature.sub_composite_simpson_eq`, the
  composite mean value form `∫_a^b g - simpsonSum g a h N = -h⁴ (b - a) g⁗(ξ)/2880`.

## References

The composite rules and the trapezoidal error are [han2009theoretical] Example 12.4.5 and
[kress1998numerical] §9.4; Simpson's error is [kress1998numerical] §9.4.
-/

open Filter MeasureTheory Set Topology

namespace Quadrature

section Composite

variable {X : Type*} [TopologicalSpace X] {N m : ℕ}

/-- **A composite quadrature rule**: `N` panels carrying `m` nodes each, assembled into one
quadrature rule on `Fin (N * m)` nodes. The weights `w j i` of a composite rule of an interval
partition are the panel weights scaled by the panel length, and its nodes `x j i` are the panel
nodes; nothing but the bookkeeping is in the definition. -/
noncomputable def composite (w : Fin N → Fin m → ℝ) (x : Fin N → Fin m → X) : C(X, ℝ) →L[ℝ] ℝ :=
  functional (fun p => Function.uncurry w (finProdFinEquiv.symm p))
    (fun p => Function.uncurry x (finProdFinEquiv.symm p))

/-- A composite rule is the sum over the panels of the panel rules. -/
@[simp]
theorem composite_apply (w : Fin N → Fin m → ℝ) (x : Fin N → Fin m → X) (f : C(X, ℝ)) :
    composite w x f = ∑ j, ∑ i, w j i * f (x j i) := by
  rw [composite, functional_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    simp [Equiv.symm_apply_apply]

/-- The absolute weight sum of a composite rule is the sum of the panels' absolute weight sums,
so a composite rule is bounded on `C(X, ℝ)` by that sum. -/
theorem norm_composite_le [CompactSpace X] (w : Fin N → Fin m → ℝ) (x : Fin N → Fin m → X) :
    ‖composite w x‖ ≤ ∑ j, ∑ i, |w j i| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun f => ?_
  rw [composite_apply, Real.norm_eq_abs]
  calc |∑ j, ∑ i, w j i * f (x j i)| ≤ ∑ j, |∑ i, w j i * f (x j i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, |w j i| * ‖f‖ := by
        refine Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using f.norm_coe_le_norm (x j i)) (abs_nonneg _)
    _ = (∑ j, ∑ i, |w j i|) * ‖f‖ := by rw [Finset.sum_mul]; simp [Finset.sum_mul]

end Composite

section RiemannSum

variable {a b h ε : ℝ} {g : ℝ → ℝ}

/-- **The one panel bound.** A rule with nonnegative weights summing to one and nodes inside the
panel differs from the panel integral by at most the panel length times a bound `ε` for the
oscillation of the integrand on the panel. -/
theorem abs_sub_panelSum_le {α β : ℝ} (hαβ : α ≤ β) (hg : ContinuousOn g (Icc α β)) {m : ℕ}
    {ω : Fin m → ℝ} (hω : ∀ i, 0 ≤ ω i) (hωsum : ∑ i, ω i = 1) {y : Fin m → ℝ}
    (hy : ∀ i, y i ∈ Icc α β)
    (hosc : ∀ u ∈ Icc α β, ∀ v ∈ Icc α β, |g u - g v| ≤ ε) :
    |(∫ x in α..β, g x) - (β - α) * ∑ i, ω i * g (y i)| ≤ (β - α) * ε := by
  have huIcc : uIcc α β = Icc α β := uIcc_of_le hαβ
  have hint : IntervalIntegrable g volume α β :=
    (hg.mono (by rw [huIcc])).intervalIntegrable
  have h1 : ∀ i : Fin m, (∫ x in α..β, (g x - g (y i)))
      = (∫ x in α..β, g x) - (β - α) * g (y i) := fun i => by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have key : ∑ i, ω i * ∫ x in α..β, (g x - g (y i))
      = (∫ x in α..β, g x) - (β - α) * ∑ i, ω i * g (y i) := by
    calc ∑ i, ω i * ∫ x in α..β, (g x - g (y i))
        = ∑ i, (ω i * (∫ x in α..β, g x) - ω i * ((β - α) * g (y i))) :=
          Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
      _ = (∑ i, ω i) * (∫ x in α..β, g x) - (β - α) * ∑ i, ω i * g (y i) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (∫ x in α..β, g x) - (β - α) * ∑ i, ω i * g (y i) := by rw [hωsum, one_mul]
  rw [← key]
  have hbound : ∀ i : Fin m, |∫ x in α..β, (g x - g (y i))| ≤ (β - α) * ε := by
    intro i
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := α) (b := β)
      (f := fun x => g x - g (y i)) (C := ε) fun x hx => by
        rw [Real.norm_eq_abs]
        have hxmem : x ∈ Icc α β := huIcc ▸ Set.uIoc_subset_uIcc hx
        exact hosc x hxmem (y i) (hy i)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ β - α)] at this
    linarith [this]
  calc |∑ i, ω i * ∫ x in α..β, (g x - g (y i))|
      ≤ ∑ i, |ω i * ∫ x in α..β, (g x - g (y i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ω i * ((β - α) * ε) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hω i)]
        exact mul_le_mul_of_nonneg_left (hbound i) (hω i)
    _ = (β - α) * ε := by rw [← Finset.sum_mul, hωsum, one_mul]

/-- The breakpoints of a partition of `[a, b]` lie in `[a, b]`. -/
private theorem mem_Icc_of_partition {N : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = a) (htN : t N = b)
    (htmono : ∀ j < N, t j ≤ t (j + 1)) {j : ℕ} (hj : j ≤ N) : t j ∈ Icc a b := by
  have hmono : ∀ q, q ≤ N → ∀ p, p ≤ q → t p ≤ t q := by
    intro q
    induction q with
    | zero => intro _ p hp; rw [Nat.le_zero.mp hp]
    | succ k ih =>
      intro hk p hp
      rcases Nat.eq_or_lt_of_le hp with hpk | hpk
      · rw [hpk]
      · exact (ih (by omega) p (by omega)).trans (htmono k (by omega))
  exact ⟨ht0 ▸ hmono j hj 0 (Nat.zero_le _), htN ▸ hmono N le_rfl j hj⟩

/-- **The Riemann sum bound for a composite rule.** The panel rule has nonnegative weights summing
to one and nodes inside its panel; the partition `t` of `[a, b]` has `N` panels of length at most
`h`; and `ε` bounds the oscillation of the integrand over distances at most `h`. Then the composite
rule differs from `∫_a^b g` by at most `(b - a) ε`.

The bound involves no degree of exactness, only the modulus of continuity, which is why a composite
rule converges for *every* continuous integrand as the mesh tends to zero
(`Quadrature.tendsto_compositeSum`). -/
theorem abs_sub_compositeSum_le {N : ℕ} {t : ℕ → ℝ} (hg : ContinuousOn g (Icc a b))
    (ht0 : t 0 = a) (htN : t N = b) (htmono : ∀ j < N, t j ≤ t (j + 1))
    (htmesh : ∀ j < N, t (j + 1) - t j ≤ h) {m : ℕ} {ω : Fin m → ℝ} (hω : ∀ i, 0 ≤ ω i)
    (hωsum : ∑ i, ω i = 1) {y : ℕ → Fin m → ℝ}
    (hy : ∀ j < N, ∀ i, y j i ∈ Icc (t j) (t (j + 1)))
    (hosc : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |u - v| ≤ h → |g u - g v| ≤ ε) :
    |(∫ x in a..b, g x) - ∑ j ∈ Finset.range N, (t (j + 1) - t j) * ∑ i, ω i * g (y j i)|
      ≤ (b - a) * ε := by
  have hmem : ∀ j ≤ N, t j ∈ Icc a b := fun j hj => mem_Icc_of_partition ht0 htN htmono hj
  have hsub : ∀ j < N, Icc (t j) (t (j + 1)) ⊆ Icc a b := fun j hj =>
    Icc_subset_Icc (hmem j hj.le).1 (hmem (j + 1) hj).2
  have hsplit : (∫ x in a..b, g x) = ∑ j ∈ Finset.range N, ∫ x in (t j)..(t (j + 1)), g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk => ?_), ht0, htN]
    exact (hg.mono (by rw [uIcc_of_le (htmono k hk)]; exact hsub k hk)).intervalIntegrable
  rw [hsplit, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range N,
          ((∫ x in (t j)..(t (j + 1)), g x) - (t (j + 1) - t j) * ∑ i, ω i * g (y j i))|
      ≤ ∑ j ∈ Finset.range N,
          |(∫ x in (t j)..(t (j + 1)), g x) - (t (j + 1) - t j) * ∑ i, ω i * g (y j i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (t (j + 1) - t j) * ε := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjN := Finset.mem_range.mp hj
        refine abs_sub_panelSum_le (htmono j hjN) (hg.mono (hsub j hjN)) hω hωsum (hy j hjN)
          fun u hu v hv => ?_
        refine hosc u (hsub j hjN hu) v (hsub j hjN hv) ?_
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hu.2, hv.1, htmesh j hjN], by linarith [hv.2, hu.1, htmesh j hjN]⟩
    _ = (b - a) * ε := by rw [← Finset.sum_mul, Finset.sum_range_sub, ht0, htN]

/-- **The Riemann sum theorem.** A composite rule whose panel weights are nonnegative and sum to
one converges to the integral for *every* continuous integrand, as soon as the mesh of the
partitions tends to zero. The panel rule is fixed and its degree of exactness never grows, so this
is not an instance of the Szegő–Pólya criterion `Quadrature.tendsto_iff_bddAbove_sum_abs`; it is
`Quadrature.abs_sub_compositeSum_le` together with the uniform continuity of the integrand. -/
theorem tendsto_compositeSum (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) {N : ℕ → ℕ}
    {t : ℕ → ℕ → ℝ} {hs : ℕ → ℝ} (ht0 : ∀ n, t n 0 = a) (htN : ∀ n, t n (N n) = b)
    (htmono : ∀ n, ∀ j < N n, t n j ≤ t n (j + 1))
    (htmesh : ∀ n, ∀ j < N n, t n (j + 1) - t n j ≤ hs n) (hh : Tendsto hs atTop (𝓝 0))
    {m : ℕ} {ω : Fin m → ℝ} (hω : ∀ i, 0 ≤ ω i) (hωsum : ∑ i, ω i = 1) {y : ℕ → ℕ → Fin m → ℝ}
    (hy : ∀ n, ∀ j < N n, ∀ i, y n j i ∈ Icc (t n j) (t n (j + 1))) :
    Tendsto (fun n => ∑ j ∈ Finset.range (N n), (t n (j + 1) - t n j) * ∑ i, ω i * g (y n j i))
      atTop (𝓝 (∫ x in a..b, g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (b - a + 1) with hε'def
  have hba : 0 ≤ b - a := by linarith
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := a) (b := b)).uniformContinuousOn_of_continuous hg) ε' hε'
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hh δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  have hhn : hs n < δ := by
    have := hn₀ n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hosc : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |u - v| ≤ hs n → |g u - g v| ≤ ε' := by
    intro u hu v hv huv
    have := hδg u hu v hv (by rw [Real.dist_eq]; exact huv.trans_lt hhn)
    rw [Real.dist_eq] at this
    exact this.le
  have hbound := abs_sub_compositeSum_le hg (ht0 n) (htN n) (htmono n) (htmesh n) hω hωsum
    (hy n) hosc
  rw [Real.dist_eq, abs_sub_comm]
  refine hbound.trans_lt ?_
  have hpos : (0 : ℝ) < b - a + 1 := by linarith
  rw [hε'def, mul_div_assoc', div_lt_iff₀ hpos]
  have : ε * (b - a + 1) = (b - a) * ε + ε := by ring
  linarith

end RiemannSum

section Trapezoid

variable {a b h : ℝ} {g g' g'' : ℝ → ℝ}

/-- **The composite trapezoidal sum** on the uniform mesh `x_j = a + j h` with `N` panels,
`∑_{j < N} (h/2) (g(x_j) + g(x_{j+1}))`.  In the book's display it is
`h (g(x_0)/2 + g(x_1) + ⋯ + g(x_{N-1}) + g(x_N)/2)`, which is `Quadrature.trapezoidSum_eq`. -/
noncomputable def trapezoidSum (g : ℝ → ℝ) (a h : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, h / 2 * (g (a + j * h) + g (a + (j + 1) * h))

/-- The composite trapezoidal sum in the form in which it is usually displayed: the interior nodes
carry the weight `h` and the two endpoints the weight `h / 2`. -/
theorem trapezoidSum_eq {N : ℕ} (hN : 0 < N) :
    trapezoidSum g a h N
      = h * ((g a + g (a + N * h)) / 2 + ∑ j ∈ Finset.Ico 1 N, g (a + j * h)) := by
  set f : ℕ → ℝ := fun j => g (a + j * h) with hf
  have hbot : ∑ j ∈ Finset.range N, f j = f 0 + ∑ j ∈ Finset.Ico 1 N, f j := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
  have htop : ∑ j ∈ Finset.range N, f (j + 1)
      = (∑ j ∈ Finset.range N, f j) + f N - f 0 := by
    have := Finset.sum_range_succ' f N
    rw [Finset.sum_range_succ (f := f) (n := N)] at this
    linarith
  have hsplit : trapezoidSum g a h N
      = h / 2 * ((∑ j ∈ Finset.range N, f j) + ∑ j ∈ Finset.range N, f (j + 1)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, trapezoidSum]
    exact Finset.sum_congr rfl fun j _ => by simp only [hf]; push_cast; ring
  rw [hsplit, htop, hbot, hf]
  push_cast
  ring_nf

/-- **The Peano identity for the trapezoidal rule on one panel**: the error of the two point
trapezoidal rule is the integral of the second derivative against the kernel
`(t - α)(t - β)/2`, which is nonpositive on the panel.  Two integrations by parts. -/
theorem sub_trapezoid_eq_integral_peanoKernel {α β : ℝ}
    (hg : ∀ x ∈ Set.uIcc α β, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc α β, HasDerivAt g' (g'' x) x)
    (hg'' : IntervalIntegrable g'' volume α β) :
    (∫ t in α..β, g t) - (β - α) / 2 * (g α + g β)
      = ∫ t in α..β, (t - α) * (t - β) / 2 * g'' t := by
  have hcg' : ContinuousOn g' (Set.uIcc α β) := fun x hx =>
    (hg' x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (Set.uIcc α β) := fun x hx =>
    (hg x hx).continuousAt.continuousWithinAt
  have hφ : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t => (t - α) * (t - β) / 2) (x - (α + β) / 2) x := by
    intro x _
    have hx : HasDerivAt (fun t : ℝ => (t - α) * (t - β) / 2)
        ((1 * (x - β) + (x - α) * 1) / 2) x :=
      (((hasDerivAt_id x).sub_const α).mul ((hasDerivAt_id x).sub_const β)).div_const 2
    convert hx using 1
    ring
  have hψ : ∀ x ∈ Set.uIcc α β, HasDerivAt (fun t : ℝ => t - (α + β) / 2) 1 x := fun x _ =>
    (hasDerivAt_id x).sub_const _
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ hg'
    ((continuous_id.sub continuous_const).intervalIntegrable _ _) hg''
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hψ hg
    (intervalIntegrable_const (c := (1 : ℝ))) (hcg'.intervalIntegrable)
  simp only [sub_self, zero_mul, zero_div, one_mul] at h1 h2
  rw [h2] at h1
  rw [h1]
  ring

/-- The Peano kernel of the trapezoidal rule integrates to `-(β - α)³/12` over the panel. -/
theorem integral_peanoKernel {α β : ℝ} :
    (∫ t in α..β, (t - α) * (t - β) / 2) = -(β - α) ^ 3 / 12 := by
  have hF : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => t ^ 3 / 6 - (α + β) * t ^ 2 / 4 + α * β * t / 2)
        ((x - α) * (x - β) / 2) x := by
    intro x _
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3 / 6 - (α + β) * t ^ 2 / 4 + α * β * t / 2)
        ((3 : ℕ) * x ^ 2 / 6 - (α + β) * ((2 : ℕ) * x ^ 1) / 4 + α * β * 1 / 2) x :=
      (((hasDerivAt_pow 3 x).div_const 6).sub
          (((hasDerivAt_pow 2 x).const_mul (α + β)).div_const 4)).add
        (((hasDerivAt_id x).const_mul (α * β)).div_const 2)
    convert h3 using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((continuous_id.sub continuous_const).mul (continuous_id.sub continuous_const)
      |>.div_const 2 |>.intervalIntegrable _ _)]
  ring

/-- **The composite trapezoidal rule error in mean value form.**  For `g` twice differentiable with
continuous second derivative on `[a, b]` and the uniform mesh `h = (b - a)/N`,

`∫_a^b g - h (g(x_0)/2 + g(x_1) + ⋯ + g(x_{N-1}) + g(x_N)/2) = -h² (b - a) g''(ξ)/12`

for some `ξ` in `[a, b]`.  The panel error is the Peano integral
`Quadrature.sub_trapezoid_eq_integral_peanoKernel`; the kernel does not change sign, so each panel
error lies between `-h³ M/12` and `-h³ m/12` with `m` and `M` the extreme values of `g''`, and the
intermediate value theorem collects the `N` panels into one value of `g''`. -/
theorem sub_composite_trapezoid_eq (hab : a < b) {N : ℕ} (hN : 0 < N) (hh : h = (b - a) / N)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Icc a b, HasDerivAt g' (g'' x) x) (hg'' : ContinuousOn g'' (Set.Icc a b)) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ t in a..b, g t) - trapezoidSum g a h N = -(h ^ 2 * (b - a) / 12) * g'' ξ := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hhpos : 0 < h := by rw [hh]; positivity
  set x : ℕ → ℝ := fun j => a + j * h with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxN : x N = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    simp only [hxdef, hh, hc]
    ring
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = h := by
    intro j; rw [hxdef]; push_cast; ring
  have hxmono : ∀ j : ℕ, x j ≤ x (j + 1) := fun j => by linarith [hxstep j, hhpos]
  have hxmem : ∀ j ≤ N, x j ∈ Set.Icc a b := fun j hj =>
    mem_Icc_of_partition hx0 hxN (fun j _ => hxmono j) hj
  have hxsub : ∀ j < N, Set.Icc (x j) (x (j + 1)) ⊆ Set.Icc a b := fun j hj =>
    Set.Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  have huIcc : ∀ j : ℕ, Set.uIcc (x j) (x (j + 1)) = Set.Icc (x j) (x (j + 1)) := fun j =>
    Set.uIcc_of_le (hxmono j)
  -- the panel identity
  have hpanel : ∀ j < N, (∫ t in (x j)..(x (j + 1)), g t) - h / 2 * (g (x j) + g (x (j + 1)))
      = ∫ t in (x j)..(x (j + 1)), (t - x j) * (t - x (j + 1)) / 2 * g'' t := by
    intro j hj
    have hsub : Set.uIcc (x j) (x (j + 1)) ⊆ Set.Icc a b := by
      rw [huIcc j]; exact hxsub j hj
    rw [← hxstep j]
    exact sub_trapezoid_eq_integral_peanoKernel (fun y hy => hg y (hsub hy))
      (fun y hy => hg' y (hsub hy))
      ((hg''.mono hsub).intervalIntegrable)
  -- the error as a sum of panel integrals
  have hint : ∀ j < N, IntervalIntegrable g volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (hg y (hxsub j hj (by rwa [huIcc j] at hy))).continuousAt.continuousWithinAt
  have htrap : trapezoidSum g a h N
      = ∑ j ∈ Finset.range N, h / 2 * (g (x j) + g (x (j + 1))) := by
    rw [trapezoidSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef]
    push_cast
    ring
  have hsplit : (∫ t in a..b, g t) - trapezoidSum g a h N
      = ∑ j ∈ Finset.range N,
          ∫ t in (x j)..(x (j + 1)), (t - x j) * (t - x (j + 1)) / 2 * g'' t := by
    rw [htrap, ← hx0, ← hxN, ← intervalIntegral.sum_integral_adjacent_intervals hint,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j hj => hpanel j (Finset.mem_range.mp hj)
  -- the extreme values of the second derivative
  obtain ⟨u, hu, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    ⟨a, Set.left_mem_Icc.2 hab.le⟩ hg''
  obtain ⟨v, hv, hmax⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    ⟨a, Set.left_mem_Icc.2 hab.le⟩ hg''
  set S : ℝ := -(h ^ 2 * (b - a) / 12) with hS
  have hSneg : S < 0 := by
    have h2 : 0 < h ^ 2 := pow_pos hhpos 2
    have hba : 0 < b - a := by linarith
    rw [hS]
    nlinarith
  have hpanelint : ∀ j < N, IntervalIntegrable
      (fun t => (t - x j) * (t - x (j + 1)) / 2 * g'' t) volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable (ContinuousOn.mul ?_ ?_)
    · exact (((continuous_id.sub continuous_const).mul
        (continuous_id.sub continuous_const)).div_const 2).continuousOn
    · exact hg''.mono (by rw [huIcc j]; exact hxsub j hj)
  have hkerint : ∀ j : ℕ, IntervalIntegrable
      (fun t => (t - x j) * (t - x (j + 1)) / 2) volume (x j) (x (j + 1)) :=
    fun j => (((continuous_id.sub continuous_const).mul
      (continuous_id.sub continuous_const)).div_const 2).intervalIntegrable _ _
  have hkerneg : ∀ j : ℕ, ∀ t ∈ Set.Icc (x j) (x (j + 1)),
      (t - x j) * (t - x (j + 1)) / 2 ≤ 0 := by
    intro j t ht
    have h1 : 0 ≤ t - x j := by linarith [ht.1]
    have h2 : t - x (j + 1) ≤ 0 := by linarith [ht.2]
    nlinarith
  have hkerval : ∀ j : ℕ, (∫ t in (x j)..(x (j + 1)), (t - x j) * (t - x (j + 1)) / 2)
      = -h ^ 3 / 12 := by
    intro j
    rw [integral_peanoKernel, hxstep j]
  -- the two sided bound on one panel
  have hbound : ∀ j < N, g'' v * (-h ^ 3 / 12)
      ≤ (∫ t in (x j)..(x (j + 1)), (t - x j) * (t - x (j + 1)) / 2 * g'' t)
      ∧ (∫ t in (x j)..(x (j + 1)), (t - x j) * (t - x (j + 1)) / 2 * g'' t)
        ≤ g'' u * (-h ^ 3 / 12) := by
    intro j hj
    have hle := hxmono j
    constructor
    · have := intervalIntegral.integral_mono_on (μ := volume) (a := x j) (b := x (j + 1))
        (f := fun t => (t - x j) * (t - x (j + 1)) / 2 * g'' v)
        (g := fun t => (t - x j) * (t - x (j + 1)) / 2 * g'' t) hle
        ((hkerint j).mul_const _) (hpanelint j hj) fun t ht =>
          mul_le_mul_of_nonpos_left (hmax (hxsub j hj ht)) (hkerneg j t ht)
      rw [intervalIntegral.integral_mul_const, hkerval j] at this
      linarith
    · have := intervalIntegral.integral_mono_on (μ := volume) (a := x j) (b := x (j + 1))
        (f := fun t => (t - x j) * (t - x (j + 1)) / 2 * g'' t)
        (g := fun t => (t - x j) * (t - x (j + 1)) / 2 * g'' u) hle
        (hpanelint j hj) ((hkerint j).mul_const _) fun t ht =>
          mul_le_mul_of_nonpos_left (hmin (hxsub j hj ht)) (hkerneg j t ht)
      rw [intervalIntegral.integral_mul_const, hkerval j] at this
      linarith
  -- sum the bounds
  have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hsumS : ∑ _j ∈ Finset.range N, (-h ^ 3 / 12) = S := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hS, ← hNh]
    ring
  set E : ℝ := (∫ t in a..b, g t) - trapezoidSum g a h N with hE
  have hlow : g'' v * S ≤ E := by
    rw [hsplit, ← hsumS, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (hbound j (Finset.mem_range.mp hj)).1
  have hhigh : E ≤ g'' u * S := by
    rw [hsplit, ← hsumS, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (hbound j (Finset.mem_range.mp hj)).2
  -- the intermediate value theorem
  have hcmem : E / S ∈ Set.uIcc (g'' u) (g'' v) := by
    have h1 : g'' u ≤ E / S := by
      rw [le_div_iff_of_neg hSneg]
      linarith [hhigh]
    have h2 : E / S ≤ g'' v := by
      rw [div_le_iff_of_neg hSneg]
      linarith [hlow]
    exact Set.mem_uIcc_of_le h1 h2
  have huv : Set.uIcc u v ⊆ Set.Icc a b := Set.uIcc_subset_Icc hu hv
  obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_uIcc (hg''.mono huv) hcmem
  refine ⟨ξ, huv hξ, ?_⟩
  have hSne : S ≠ 0 := ne_of_lt hSneg
  rw [hξval, mul_comm]
  exact (div_mul_cancel₀ E hSne).symm

end Trapezoid

/-! ### Convergence of the composite trapezoidal and Simpson rules -/

section UniformMesh

variable {a b : ℝ} {g : ℝ → ℝ}

/-- **The composite Simpson sum** on the uniform mesh `x_j = a + j h`,
`∑_{j < N} (h/6) (g(x_j) + 4 g(x_j + h/2) + g(x_{j+1}))`: the panel rule is Simpson's, with the
weights `(1/6, 4/6, 1/6)` at the two endpoints and the midpoint of the panel. -/
noncomputable def simpsonSum (g : ℝ → ℝ) (a h : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, h / 6 * (g (a + j * h) + 4 * g (a + j * h + h / 2) + g (a + (j + 1) * h))

/-- The shape shared by the uniform mesh convergence proofs: the partition `x_j = a + j h_n` of
`[a, b]` into `N n` panels satisfies the hypotheses of `tendsto_compositeSum`. -/
private theorem tendsto_uniformMesh {N : ℕ → ℕ} {hs : ℕ → ℝ} {m : ℕ} {ω : Fin m → ℝ}
    {c : Fin m → ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) (hN : ∀ n, 0 < N n)
    (hhs : ∀ n, hs n = (b - a) / N n) (hlim : Tendsto hs atTop (𝓝 0)) (hω : ∀ i, 0 ≤ ω i)
    (hωsum : ∑ i, ω i = 1) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∑ j ∈ Finset.range (N n),
        hs n * ∑ i, ω i * g (a + j * hs n + c i * hs n)) atTop (𝓝 (∫ t in a..b, g t)) := by
  have hsnn : ∀ n, 0 ≤ hs n := fun n => by
    rw [hhs n]
    have : (0 : ℝ) ≤ (N n : ℝ) := Nat.cast_nonneg _
    have hba : 0 ≤ b - a := by linarith
    positivity
  have hmain := tendsto_compositeSum (a := a) (b := b) hab hg (N := N)
    (t := fun n j => a + j * hs n) (hs := hs) (fun n => by simp)
    (fun n => by
      have hNR : ((N n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (hN n).ne'
      rw [hhs n]
      field_simp
      ring)
    (fun n j _ => by push_cast; nlinarith [hsnn n])
    (fun n j _ => by push_cast; nlinarith [hsnn n]) hlim hω hωsum
    (y := fun n j i => a + j * hs n + c i * hs n)
    (fun n j _ i => by
      constructor
      · nlinarith [hsnn n, (hc i).1]
      · push_cast
        nlinarith [hsnn n, (hc i).2])
  refine hmain.congr fun n => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring_nf

/-- **The composite trapezoidal rule converges** for every continuous integrand, as soon as the
mesh of the uniform partitions tends to zero. -/
theorem tendsto_trapezoidSum {N : ℕ → ℕ} {hs : ℕ → ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (hN : ∀ n, 0 < N n) (hhs : ∀ n, hs n = (b - a) / N n)
    (hlim : Tendsto hs atTop (𝓝 0)) :
    Tendsto (fun n => trapezoidSum g a (hs n) (N n)) atTop (𝓝 (∫ t in a..b, g t)) := by
  have h := tendsto_uniformMesh (g := g) (ω := ![1 / 2, 1 / 2]) (c := ![0, 1]) hab hg hN hhs hlim
    (by intro i; fin_cases i <;> norm_num) (by simp [Fin.sum_univ_two]; norm_num)
    (by intro i; fin_cases i <;> norm_num)
  refine h.congr fun n => ?_
  rw [trapezoidSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

/-- **The composite Simpson rule converges** for every continuous integrand, as soon as the mesh of
the uniform partitions tends to zero.  Simpson's weights are nonnegative and sum to one, so this is
the same Riemann sum theorem as for the trapezoidal rule; the higher order of Simpson's rule shows
only in the error formula for a smooth integrand, not in its convergence. -/
theorem tendsto_simpsonSum {N : ℕ → ℕ} {hs : ℕ → ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (hN : ∀ n, 0 < N n) (hhs : ∀ n, hs n = (b - a) / N n)
    (hlim : Tendsto hs atTop (𝓝 0)) :
    Tendsto (fun n => simpsonSum g a (hs n) (N n)) atTop (𝓝 (∫ t in a..b, g t)) := by
  have h := tendsto_uniformMesh (g := g) (ω := ![1 / 6, 4 / 6, 1 / 6]) (c := ![0, 1 / 2, 1])
    hab hg hN hhs hlim (by intro i; fin_cases i <;> norm_num)
    (by simp [Fin.sum_univ_three]; norm_num) (by intro i; fin_cases i <;> norm_num)
  refine h.congr fun n => ?_
  rw [simpsonSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring_nf

end UniformMesh

/-! ### The Euler–Maclaurin form of the trapezoidal error -/

section EulerMaclaurin

variable {a b h : ℝ} {g g' g'' g₃ g₄ : ℝ → ℝ}

/-- The **second Peano kernel** of the trapezoidal rule, `(t - α)²(t - β)²/24`, integrates to
`(β - α)⁵/720` over the panel. It is nonnegative there, which is what makes the remainder of the
Euler–Maclaurin expansion easy to bound. -/
theorem integral_peanoKernel_sq {α β : ℝ} :
    (∫ t in α..β, (t - α) ^ 2 * (t - β) ^ 2 / 24) = (β - α) ^ 5 / 720 := by
  have hF : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => (t ^ 5 / 5 - (α + β) * t ^ 4 / 2
          + ((α + β) ^ 2 + 2 * (α * β)) * t ^ 3 / 3 - (α + β) * (α * β) * t ^ 2
          + (α * β) ^ 2 * t) / 24)
        ((x - α) ^ 2 * (x - β) ^ 2 / 24) x := by
    intro x _
    have hd : HasDerivAt (fun t : ℝ => t ^ 5 / 5 - (α + β) * t ^ 4 / 2
        + ((α + β) ^ 2 + 2 * (α * β)) * t ^ 3 / 3 - (α + β) * (α * β) * t ^ 2
        + (α * β) ^ 2 * t)
        ((5 : ℕ) * x ^ 4 / 5 - (α + β) * ((4 : ℕ) * x ^ 3) / 2
          + ((α + β) ^ 2 + 2 * (α * β)) * ((3 : ℕ) * x ^ 2) / 3
          - (α + β) * (α * β) * ((2 : ℕ) * x ^ 1) + (α * β) ^ 2 * 1) x :=
      ((((hasDerivAt_pow 5 x).div_const 5).sub
        (((hasDerivAt_pow 4 x).const_mul (α + β)).div_const 2)).add
          (((hasDerivAt_pow 3 x).const_mul ((α + β) ^ 2 + 2 * (α * β))).div_const 3)).sub
        ((hasDerivAt_pow 2 x).const_mul ((α + β) * (α * β))) |>.add
        ((hasDerivAt_id x).const_mul ((α * β) ^ 2))
    have heq : (x - α) ^ 2 * (x - β) ^ 2 / 24
        = ((5 : ℕ) * x ^ 4 / 5 - (α + β) * ((4 : ℕ) * x ^ 3) / 2
          + ((α + β) ^ 2 + 2 * (α * β)) * ((3 : ℕ) * x ^ 2) / 3
          - (α + β) * (α * β) * ((2 : ℕ) * x ^ 1) + (α * β) ^ 2 * 1) / 24 := by
      push_cast
      ring
    rw [heq]
    exact hd.div_const 24
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- **Two more integrations by parts of the Peano identity.**  The Peano kernel `(t - α)(t - β)/2`
of the trapezoidal rule differs from the mean-zero kernel `Q` of the Euler–Maclaurin expansion by
the constant `(β - α)²/12`, and `Q` has two successive antiderivatives vanishing at both endpoints.
Hence, for `g` of class `C⁴`,

`∫_α^β (t - α)(t - β) g''(t)/2 dt`
` = -((β - α)²/12) (g'(β) - g'(α)) + ∫_α^β (t - α)²(t - β)² g⁗(t)/24 dt`,

the second term being `O((β - α)⁵)`. -/
theorem integral_peanoKernel_mul_eq {α β : ℝ}
    (h2 : ∀ x ∈ Set.uIcc α β, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x ∈ Set.uIcc α β, HasDerivAt g'' (g₃ x) x)
    (h4 : ∀ x ∈ Set.uIcc α β, HasDerivAt g₃ (g₄ x) x)
    (hc4 : IntervalIntegrable g₄ volume α β) :
    (∫ t in α..β, (t - α) * (t - β) / 2 * g'' t)
      = -((β - α) ^ 2 / 12) * (g' β - g' α)
        + ∫ t in α..β, (t - α) ^ 2 * (t - β) ^ 2 / 24 * g₄ t := by
  have hcg'' : ContinuousOn g'' (Set.uIcc α β) := fun x hx =>
    (h3 x hx).continuousAt.continuousWithinAt
  have hcg₃ : ContinuousOn g₃ (Set.uIcc α β) := fun x hx =>
    (h4 x hx).continuousAt.continuousWithinAt
  -- the two antiderivatives of the mean-zero kernel
  have hS : ∀ x ∈ Set.uIcc α β, HasDerivAt (fun t : ℝ => (t - α) ^ 2 * (t - β) ^ 2 / 24)
      ((x - α) * (x - β) * (2 * x - α - β) / 12) x := by
    intro x _
    have hd : HasDerivAt (fun t : ℝ => (t - α) ^ 2 * (t - β) ^ 2 / 24)
        ((2 * (x - α) ^ 1 * 1 * (x - β) ^ 2 + (x - α) ^ 2 * (2 * (x - β) ^ 1 * 1)) / 24) x := by
      have h1 : HasDerivAt (fun t : ℝ => (t - α) ^ 2) (2 * (x - α) ^ 1 * 1) x :=
        (((hasDerivAt_id x).sub_const α).pow 2)
      have h2' : HasDerivAt (fun t : ℝ => (t - β) ^ 2) (2 * (x - β) ^ 1 * 1) x :=
        (((hasDerivAt_id x).sub_const β).pow 2)
      exact (h1.mul h2').div_const 24
    have heq : (x - α) * (x - β) * (2 * x - α - β) / 12
        = (2 * (x - α) ^ 1 * 1 * (x - β) ^ 2 + (x - α) ^ 2 * (2 * (x - β) ^ 1 * 1)) / 24 := by
      ring
    rw [heq]
    exact hd
  have hR : ∀ x ∈ Set.uIcc α β,
      HasDerivAt (fun t : ℝ => (t - α) * (t - β) * (2 * t - α - β) / 12)
        ((x - α) * (x - β) / 2 + (β - α) ^ 2 / 12) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t - α) * (t - β)) (1 * (x - β) + (x - α) * 1) x :=
      ((hasDerivAt_id x).sub_const α).mul ((hasDerivAt_id x).sub_const β)
    have h2' : HasDerivAt (fun t : ℝ => 2 * t - α - β) (2 * 1 - 0) x := by
      simpa using (((hasDerivAt_id x).const_mul 2).sub_const α).sub_const β
    have hd := (h1.mul h2').div_const 12
    have heq : (x - α) * (x - β) / 2 + (β - α) ^ 2 / 12
        = ((1 * (x - β) + (x - α) * 1) * (2 * x - α - β)
          + (x - α) * (x - β) * (2 * 1 - 0)) / 12 := by
      ring
    rw [heq]
    exact hd
  have hRint : IntervalIntegrable
      (fun t : ℝ => (t - α) * (t - β) / 2 + (β - α) ^ 2 / 12) volume α β :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hSint : IntervalIntegrable
      (fun t : ℝ => (t - α) * (t - β) * (2 * t - α - β) / 12) volume α β :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hib1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hS h4 hSint hc4
  have hib2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hR h3 hRint
    hcg₃.intervalIntegrable
  simp only [sub_self, mul_zero, zero_mul, zero_div, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true] at hib1 hib2
  -- split the mean-zero kernel into the Peano kernel and a constant
  have hsplit : (∫ t in α..β, ((t - α) * (t - β) / 2 + (β - α) ^ 2 / 12) * g'' t)
      = (∫ t in α..β, (t - α) * (t - β) / 2 * g'' t)
        + (β - α) ^ 2 / 12 * (g' β - g' α) := by
    have hfti : (∫ t in α..β, g'' t) = g' β - g' α :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt h2 hcg''.intervalIntegrable
    rw [← hfti, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact (ContinuousOn.mul
        ((by fun_prop : Continuous fun t : ℝ => (t - α) * (t - β) / 2).continuousOn)
        hcg'').intervalIntegrable
    · exact hcg''.intervalIntegrable.const_mul _
  rw [hsplit] at hib2
  linarith [hib1, hib2]

/-- **The Euler–Maclaurin form of the composite trapezoidal error.**  For `g` of class `C⁴` on
`[a, b]` with `|g⁗| ≤ M` there, and the uniform mesh `h = (b - a)/N`,

`∫_a^b g - h (g(x₀)/2 + ⋯ + g(x_N)/2) = -(h²/12) [g'(b) - g'(a)] + R`, `|R| ≤ (b - a) h⁴ M/720`.

This is the asymptotic form of the trapezoidal error, and it is a *different* statement from the
mean value form `sub_composite_trapezoid_eq`: it names the leading term, which is what makes
Richardson extrapolation raise the order.  The boundary terms of the panels telescope, and the
remainder is the second Peano kernel `(t - x_j)²(t - x_{j+1})²/24`, which is nonnegative and
integrates to `h⁵/720` on each of the `N` panels. -/
theorem abs_sub_trapezoidSum_add_le (hab : a < b) {N : ℕ} (hN : 0 < N) (hh : h = (b - a) / N)
    {M : ℝ} (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Icc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Set.Icc a b, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.Icc a b, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Set.Icc a b))
    (hM : ∀ t ∈ Set.Icc a b, |g₄ t| ≤ M) :
    |(∫ t in a..b, g t) - trapezoidSum g a h N + h ^ 2 / 12 * (g' b - g' a)|
      ≤ (b - a) * h ^ 4 * M / 720 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hhpos : 0 < h := by rw [hh]; positivity
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a (Set.left_mem_Icc.2 hab.le))
  have hcg'' : ContinuousOn g'' (Set.Icc a b) := fun y hy =>
    (hg'' y hy).continuousAt.continuousWithinAt
  set x : ℕ → ℝ := fun j => a + j * h with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxN : x N = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    simp only [hxdef, hh, hc]
    ring
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = h := by
    intro j; rw [hxdef]; push_cast; ring
  have hxsucc : ∀ j : ℕ, x (j + 1) = x j + h := fun j => by linarith [hxstep j]
  have hxmono : ∀ j : ℕ, x j ≤ x (j + 1) := fun j => by linarith [hxstep j, hhpos]
  have hxmem : ∀ j ≤ N, x j ∈ Set.Icc a b := fun j hj =>
    mem_Icc_of_partition hx0 hxN (fun j _ => hxmono j) hj
  have hxsub : ∀ j < N, Set.Icc (x j) (x (j + 1)) ⊆ Set.Icc a b := fun j hj =>
    Set.Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  have huIcc : ∀ j : ℕ, Set.uIcc (x j) (x (j + 1)) = Set.Icc (x j) (x (j + 1)) := fun j =>
    Set.uIcc_of_le (hxmono j)
  have hsubu : ∀ j < N, Set.uIcc (x j) (x (j + 1)) ⊆ Set.Icc a b := fun j hj => by
    rw [huIcc j]; exact hxsub j hj
  -- the panel identity, with the leading term separated
  have hpanel : ∀ j < N, (∫ t in (x j)..(x (j + 1)), g t) - h / 2 * (g (x j) + g (x (j + 1)))
      = -(h ^ 2 / 12) * (g' (x (j + 1)) - g' (x j))
        + ∫ t in (x j)..(x (j + 1)), (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t := by
    intro j hj
    have hpe := sub_trapezoid_eq_integral_peanoKernel (g := g) (g' := g') (g'' := g'')
      (fun y hy => hg y (hsubu j hj hy)) (fun y hy => hg' y (hsubu j hj hy))
      ((hcg''.mono (hsubu j hj)).intervalIntegrable)
    have hem := integral_peanoKernel_mul_eq (α := x j) (β := x (j + 1)) (g' := g') (g'' := g'')
      (g₃ := g₃) (g₄ := g₄) (fun y hy => hg' y (hsubu j hj hy))
      (fun y hy => hg'' y (hsubu j hj hy)) (fun y hy => hg₃ y (hsubu j hj hy))
      ((hc₄.mono (hsubu j hj)).intervalIntegrable)
    rw [hxstep j] at hpe hem
    rw [hpe, hem]
  -- integrability of the remainder integrand
  have hint : ∀ j < N, IntervalIntegrable g volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (hg y (hsubu j hj hy)).continuousAt.continuousWithinAt
  have hremint : ∀ j < N, IntervalIntegrable
      (fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t) volume (x j) (x (j + 1)) := by
    intro j hj
    exact (ContinuousOn.mul (by fun_prop) (hc₄.mono (hsubu j hj))).intervalIntegrable
  have hkerint : ∀ j : ℕ, IntervalIntegrable
      (fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * M) volume (x j) (x (j + 1)) :=
    fun j => Continuous.intervalIntegrable (by fun_prop) _ _
  have hkerint' : ∀ j : ℕ, IntervalIntegrable
      (fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * (-M)) volume (x j) (x (j + 1)) :=
    fun j => Continuous.intervalIntegrable (by fun_prop) _ _
  -- each panel remainder is at most `M h⁵ / 720` in absolute value
  have hrem : ∀ j < N, |∫ t in (x j)..(x (j + 1)),
      (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t| ≤ M * h ^ 5 / 720 := by
    intro j hj
    have hval : (∫ t in (x j)..(x (j + 1)), (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24)
        = h ^ 5 / 720 := by
      rw [integral_peanoKernel_sq, hxstep j]
    have hup : (∫ t in (x j)..(x (j + 1)),
        (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t) ≤ M * h ^ 5 / 720 := by
      have := intervalIntegral.integral_mono_on (μ := volume) (a := x j) (b := x (j + 1))
        (f := fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t)
        (g := fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * M) (hxmono j)
        (hremint j hj) (hkerint j) fun t ht => by
          have hnn : (0 : ℝ) ≤ (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 := by positivity
          have := (abs_le.1 (hM t (hxsub j hj ht))).2
          exact mul_le_mul_of_nonneg_left this hnn
      rw [intervalIntegral.integral_mul_const, hval] at this
      linarith
    have hlow : -(M * h ^ 5 / 720) ≤ ∫ t in (x j)..(x (j + 1)),
        (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t := by
      have := intervalIntegral.integral_mono_on (μ := volume) (a := x j) (b := x (j + 1))
        (f := fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * (-M))
        (g := fun t => (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t) (hxmono j)
        (hkerint' j) (hremint j hj) fun t ht => by
          have hnn : (0 : ℝ) ≤ (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 := by positivity
          have := (abs_le.1 (hM t (hxsub j hj ht))).1
          exact mul_le_mul_of_nonneg_left this hnn
      rw [intervalIntegral.integral_mul_const, hval] at this
      linarith
    exact abs_le.2 ⟨hlow, hup⟩
  -- the composite identity
  have htrap : trapezoidSum g a h N
      = ∑ j ∈ Finset.range N, h / 2 * (g (x j) + g (x (j + 1))) := by
    rw [trapezoidSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef]
    push_cast
    ring
  have htel : ∑ j ∈ Finset.range N, -(h ^ 2 / 12) * (g' (x (j + 1)) - g' (x j))
      = -(h ^ 2 / 12) * (g' b - g' a) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j => g' (x j)), hx0, hxN]
  have hsplit : (∫ t in a..b, g t) - trapezoidSum g a h N + h ^ 2 / 12 * (g' b - g' a)
      = ∑ j ∈ Finset.range N,
          ∫ t in (x j)..(x (j + 1)), (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t := by
    have hadj : (∫ t in a..b, g t) - trapezoidSum g a h N
        = ∑ j ∈ Finset.range N, ((∫ t in (x j)..(x (j + 1)), g t)
          - h / 2 * (g (x j) + g (x (j + 1)))) := by
      rw [htrap, ← hx0, ← hxN, ← intervalIntegral.sum_integral_adjacent_intervals hint,
        ← Finset.sum_sub_distrib]
    rw [hadj, Finset.sum_congr rfl fun j hj => hpanel j (Finset.mem_range.mp hj),
      Finset.sum_add_distrib, htel]
    ring
  -- sum the panel bounds
  have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  rw [hsplit]
  calc |∑ j ∈ Finset.range N,
        ∫ t in (x j)..(x (j + 1)), (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t|
      ≤ ∑ j ∈ Finset.range N,
        |∫ t in (x j)..(x (j + 1)), (t - x j) ^ 2 * (t - x (j + 1)) ^ 2 / 24 * g₄ t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range N, M * h ^ 5 / 720 :=
        Finset.sum_le_sum fun j hj => hrem j (Finset.mem_range.mp hj)
    _ = (b - a) * h ^ 4 * M / 720 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hNh]
        ring

end EulerMaclaurin

/-! ### The composite Simpson error -/

section SimpsonError

variable {a b h : ℝ} {g g' g'' g₃ g₄ : ℝ → ℝ}

/-- **The telescoping identity behind a fourth order Peano kernel.**  If `p` has four derivatives
and the fourth one is `1`, then `p g⁗ - g` is the derivative of `p g''' - p' g'' + p'' g' - p''' g`,
so integrating it over a panel is a single application of the fundamental theorem of calculus in
place of the four integrations by parts it replaces. -/
private theorem integral_quartic_kernel_sub {p p₁ p₂ p₃ : ℝ → ℝ} {u v : ℝ}
    (hp : ∀ x : ℝ, HasDerivAt p (p₁ x) x) (hp₁ : ∀ x : ℝ, HasDerivAt p₁ (p₂ x) x)
    (hp₂ : ∀ x : ℝ, HasDerivAt p₂ (p₃ x) x) (hp₃ : ∀ x : ℝ, HasDerivAt p₃ 1 x)
    (hg : ∀ x ∈ Set.uIcc u v, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc u v, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Set.uIcc u v, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.uIcc u v, HasDerivAt g₃ (g₄ x) x)
    (hg₄ : IntervalIntegrable g₄ volume u v) :
    (∫ t in u..v, p t * g₄ t) - ∫ t in u..v, g t
      = (p v * g₃ v - p₁ v * g'' v + p₂ v * g' v - p₃ v * g v)
        - (p u * g₃ u - p₁ u * g'' u + p₂ u * g' u - p₃ u * g u) := by
  have hdp : Differentiable ℝ p := fun y => (hp y).differentiableAt
  have hcg : ContinuousOn g (Set.uIcc u v) := fun y hy =>
    (hg y hy).continuousAt.continuousWithinAt
  have hpg : IntervalIntegrable (fun t => p t * g₄ t) volume u v :=
    hg₄.continuousOn_mul hdp.continuous.continuousOn
  have hgi : IntervalIntegrable g volume u v := hcg.intervalIntegrable
  have hΦ : ∀ y ∈ Set.uIcc u v,
      HasDerivAt (fun t => p t * g₃ t - p₁ t * g'' t + p₂ t * g' t - p₃ t * g t)
        (p y * g₄ y - g y) y := by
    intro y hy
    have h1 := (hp y).mul (hg₃ y hy)
    have h2 := (hp₁ y).mul (hg'' y hy)
    have h3 := (hp₂ y).mul (hg' y hy)
    have h4 := (hp₃ y).mul (hg y hy)
    have h : HasDerivAt (fun t => p t * g₃ t - p₁ t * g'' t + p₂ t * g' t - p₃ t * g t)
        (p₁ y * g₃ y + p y * g₄ y - (p₂ y * g'' y + p₁ y * g₃ y)
          + (p₃ y * g' y + p₂ y * g'' y) - (1 * g y + p₃ y * g' y)) y :=
      ((h1.sub h2).add h3).sub h4
    convert h using 1
    ring
  rw [← intervalIntegral.integral_sub hpg hgi]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ (hpg.sub hgi)

/-- **The Peano identity for Simpson's rule on one panel.**  Simpson's kernel is *piecewise*
cubic: `(t - α)³(3t - α - 2β)/72` on the left half of the panel and its mirror image
`(t - β)³(3t - β - 2α)/72` on the right.  Each half is a quartic whose fourth derivative is `1`,
so `Quadrature.integral_quartic_kernel_sub` applies on each half; the boundary terms at the
midpoint cancel, because the two halves agree there to second order and their third derivatives
are opposite, and what survives is exactly Simpson's weights `(1, 4, 1)/6`. -/
theorem sub_simpson_eq_integral_peanoKernel {α β : ℝ}
    (hg : ∀ x ∈ Set.uIcc α β, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc α β, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Set.uIcc α β, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.uIcc α β, HasDerivAt g₃ (g₄ x) x)
    (hg₄ : IntervalIntegrable g₄ volume α β) :
    (∫ t in α..β, g t) - (β - α) / 6 * (g α + 4 * g ((α + β) / 2) + g β)
      = (∫ t in α..(α + β) / 2, (t - α) ^ 3 * (3 * t - α - 2 * β) / 72 * g₄ t)
        + ∫ t in (α + β) / 2..β, (t - β) ^ 3 * (3 * t - β - 2 * α) / 72 * g₄ t := by
  have hmem : (α + β) / 2 ∈ Set.uIcc α β := by
    rcases le_total α β with hle | hle
    · rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩
    · rw [Set.uIcc_of_ge hle]; exact ⟨by linarith, by linarith⟩
  have hsubL : Set.uIcc α ((α + β) / 2) ⊆ Set.uIcc α β :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc hmem
  have hsubR : Set.uIcc ((α + β) / 2) β ⊆ Set.uIcc α β :=
    Set.uIcc_subset_uIcc hmem Set.right_mem_uIcc
  -- the four derivatives of the half kernel, in a form symmetric in the two endpoints
  have hd3 : ∀ γ δ y : ℝ, HasDerivAt (fun t : ℝ => (6 * t - 5 * γ - δ) / 6) 1 y := by
    intro γ δ y
    have h : HasDerivAt (fun t : ℝ => (6 * t - 5 * γ - δ) / 6) (6 * 1 / 6) y :=
      ((((hasDerivAt_id y).const_mul 6).sub_const (5 * γ)).sub_const δ).div_const 6
    convert h using 1
    norm_num
  have hd2 : ∀ γ δ y : ℝ, HasDerivAt (fun t : ℝ => (t - γ) * (3 * t - 2 * γ - δ) / 6)
      ((6 * y - 5 * γ - δ) / 6) y := by
    intro γ δ y
    have h : HasDerivAt (fun t : ℝ => (t - γ) * (3 * t - 2 * γ - δ) / 6)
        ((1 * (3 * y - 2 * γ - δ) + (y - γ) * (3 * 1)) / 6) y :=
      (((hasDerivAt_id y).sub_const γ).mul
        ((((hasDerivAt_id y).const_mul 3).sub_const (2 * γ)).sub_const δ)).div_const 6
    convert h using 1
    ring
  have hd1 : ∀ γ δ y : ℝ, HasDerivAt (fun t : ℝ => (t - γ) ^ 2 * (2 * t - γ - δ) / 12)
      ((y - γ) * (3 * y - 2 * γ - δ) / 6) y := by
    intro γ δ y
    have h : HasDerivAt (fun t : ℝ => (t - γ) ^ 2 * (2 * t - γ - δ) / 12)
        ((2 * (y - γ) ^ 1 * 1 * (2 * y - γ - δ) + (y - γ) ^ 2 * (2 * 1)) / 12) y :=
      ((((hasDerivAt_id y).sub_const γ).pow 2).mul
        ((((hasDerivAt_id y).const_mul 2).sub_const γ).sub_const δ)).div_const 12
    convert h using 1
    ring
  have hd0 : ∀ γ δ y : ℝ, HasDerivAt (fun t : ℝ => (t - γ) ^ 3 * (3 * t - γ - 2 * δ) / 72)
      ((y - γ) ^ 2 * (2 * y - γ - δ) / 12) y := by
    intro γ δ y
    have h : HasDerivAt (fun t : ℝ => (t - γ) ^ 3 * (3 * t - γ - 2 * δ) / 72)
        ((3 * (y - γ) ^ 2 * 1 * (3 * y - γ - 2 * δ) + (y - γ) ^ 3 * (3 * 1)) / 72) y :=
      ((((hasDerivAt_id y).sub_const γ).pow 3).mul
        ((((hasDerivAt_id y).const_mul 3).sub_const γ).sub_const (2 * δ))).div_const 72
    convert h using 1
    ring
  have hL := integral_quartic_kernel_sub (u := α) (v := (α + β) / 2)
    (g := g) (g' := g') (g'' := g'') (g₃ := g₃) (g₄ := g₄)
    (p := fun t : ℝ => (t - α) ^ 3 * (3 * t - α - 2 * β) / 72)
    (p₁ := fun t : ℝ => (t - α) ^ 2 * (2 * t - α - β) / 12)
    (p₂ := fun t : ℝ => (t - α) * (3 * t - 2 * α - β) / 6)
    (p₃ := fun t : ℝ => (6 * t - 5 * α - β) / 6)
    (hd0 α β) (hd1 α β) (hd2 α β) (hd3 α β)
    (fun y hy => hg y (hsubL hy)) (fun y hy => hg' y (hsubL hy))
    (fun y hy => hg'' y (hsubL hy)) (fun y hy => hg₃ y (hsubL hy)) (hg₄.mono_set hsubL)
  have hR := integral_quartic_kernel_sub (u := (α + β) / 2) (v := β)
    (g := g) (g' := g') (g'' := g'') (g₃ := g₃) (g₄ := g₄)
    (p := fun t : ℝ => (t - β) ^ 3 * (3 * t - β - 2 * α) / 72)
    (p₁ := fun t : ℝ => (t - β) ^ 2 * (2 * t - β - α) / 12)
    (p₂ := fun t : ℝ => (t - β) * (3 * t - 2 * β - α) / 6)
    (p₃ := fun t : ℝ => (6 * t - 5 * β - α) / 6)
    (hd0 β α) (hd1 β α) (hd2 β α) (hd3 β α)
    (fun y hy => hg y (hsubR hy)) (fun y hy => hg' y (hsubR hy))
    (fun y hy => hg'' y (hsubR hy)) (fun y hy => hg₃ y (hsubR hy)) (hg₄.mono_set hsubR)
  have hgL : IntervalIntegrable g volume α ((α + β) / 2) :=
    ContinuousOn.intervalIntegrable fun y hy =>
      (hg y (hsubL hy)).continuousAt.continuousWithinAt
  have hgR : IntervalIntegrable g volume ((α + β) / 2) β :=
    ContinuousOn.intervalIntegrable fun y hy =>
      (hg y (hsubR hy)).continuousAt.continuousWithinAt
  have hadd : (∫ t in α..(α + β) / 2, g t) + (∫ t in (α + β) / 2..β, g t) = ∫ t in α..β, g t :=
    intervalIntegral.integral_add_adjacent_intervals hgL hgR
  linarith [hL, hR, hadd]

/-- The left half of Simpson's Peano kernel integrates to `-(β - α)⁵/5760` over the left half
panel. -/
theorem integral_simpsonKernel_left {α β : ℝ} :
    (∫ t in α..(α + β) / 2, (t - α) ^ 3 * (3 * t - α - 2 * β) / 72) = -(β - α) ^ 5 / 5760 := by
  have hF : ∀ y ∈ Set.uIcc α ((α + β) / 2),
      HasDerivAt (fun t : ℝ => (t - α) ^ 5 / 120 - (β - α) * (t - α) ^ 4 / 144)
        ((y - α) ^ 3 * (3 * y - α - 2 * β) / 72) y := by
    intro y _
    have h : HasDerivAt (fun t : ℝ => (t - α) ^ 5 / 120 - (β - α) * (t - α) ^ 4 / 144)
        (5 * (y - α) ^ 4 * 1 / 120 - (β - α) * (4 * (y - α) ^ 3 * 1) / 144) y :=
      ((((hasDerivAt_id y).sub_const α).pow 5).div_const 120).sub
        (((((hasDerivAt_id y).sub_const α).pow 4).const_mul (β - α)).div_const 144)
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- The right half of Simpson's Peano kernel integrates to `-(β - α)⁵/5760` over the right half
panel, so the whole kernel integrates to `-(β - α)⁵/2880`. -/
theorem integral_simpsonKernel_right {α β : ℝ} :
    (∫ t in (α + β) / 2..β, (t - β) ^ 3 * (3 * t - β - 2 * α) / 72) = -(β - α) ^ 5 / 5760 := by
  have hF : ∀ y ∈ Set.uIcc ((α + β) / 2) β,
      HasDerivAt (fun t : ℝ => (t - β) ^ 5 / 120 - (α - β) * (t - β) ^ 4 / 144)
        ((y - β) ^ 3 * (3 * y - β - 2 * α) / 72) y := by
    intro y _
    have h : HasDerivAt (fun t : ℝ => (t - β) ^ 5 / 120 - (α - β) * (t - β) ^ 4 / 144)
        (5 * (y - β) ^ 4 * 1 / 120 - (α - β) * (4 * (y - β) ^ 3 * 1) / 144) y :=
      ((((hasDerivAt_id y).sub_const β).pow 5).div_const 120).sub
        (((((hasDerivAt_id y).sub_const β).pow 4).const_mul (α - β)).div_const 144)
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

/-- An integral against a nonpositive kernel is bounded above by the kernel's integral times a
lower bound for the other factor. -/
private theorem integral_nonpos_kernel_mul_le {f k : ℝ → ℝ} {u v c : ℝ} (huv : u ≤ v)
    (hk : ContinuousOn k (Set.Icc u v)) (hf : ContinuousOn f (Set.Icc u v))
    (hknp : ∀ t ∈ Set.Icc u v, k t ≤ 0) (hc : ∀ t ∈ Set.Icc u v, c ≤ f t) :
    (∫ t in u..v, k t * f t) ≤ c * ∫ t in u..v, k t := by
  have huIcc : Set.uIcc u v = Set.Icc u v := Set.uIcc_of_le huv
  have h1 : IntervalIntegrable (fun t => k t * f t) volume u v :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hk.mul hf)
  have h2 : IntervalIntegrable (fun t => k t * c) volume u v :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hk.mul continuousOn_const)
  have h := intervalIntegral.integral_mono_on huv h1 h2 fun t ht =>
    mul_le_mul_of_nonpos_left (hc t ht) (hknp t ht)
  rw [intervalIntegral.integral_mul_const] at h
  linarith

/-- An integral against a nonpositive kernel is bounded below by the kernel's integral times an
upper bound for the other factor. -/
private theorem le_integral_nonpos_kernel_mul {f k : ℝ → ℝ} {u v c : ℝ} (huv : u ≤ v)
    (hk : ContinuousOn k (Set.Icc u v)) (hf : ContinuousOn f (Set.Icc u v))
    (hknp : ∀ t ∈ Set.Icc u v, k t ≤ 0) (hc : ∀ t ∈ Set.Icc u v, f t ≤ c) :
    (c * ∫ t in u..v, k t) ≤ ∫ t in u..v, k t * f t := by
  have huIcc : Set.uIcc u v = Set.Icc u v := Set.uIcc_of_le huv
  have h1 : IntervalIntegrable (fun t => k t * f t) volume u v :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hk.mul hf)
  have h2 : IntervalIntegrable (fun t => k t * c) volume u v :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hk.mul continuousOn_const)
  have h := intervalIntegral.integral_mono_on huv h2 h1 fun t ht =>
    mul_le_mul_of_nonpos_left (hc t ht) (hknp t ht)
  rw [intervalIntegral.integral_mul_const] at h
  linarith

/-- **One Simpson panel, bounded by the extreme values of `g⁗`.**  Simpson's Peano kernel is
nonpositive on both halves of the panel and integrates to `-(β - α)⁵/2880`, so for
`c ≤ g⁗ ≤ M` on the panel the error lies between `M (-(β - α)⁵/2880)` and `c (-(β - α)⁵/2880)`.
This sign definiteness is what lets the intermediate value theorem collect the panels of a
composite rule into one value of `g⁗`. -/
theorem sub_simpson_mem_Icc {α β c M : ℝ} (hαβ : α ≤ β)
    (hg : ∀ x ∈ Set.Icc α β, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Icc α β, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Set.Icc α β, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.Icc α β, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Set.Icc α β))
    (hlo : ∀ t ∈ Set.Icc α β, c ≤ g₄ t) (hhi : ∀ t ∈ Set.Icc α β, g₄ t ≤ M) :
    (∫ t in α..β, g t) - (β - α) / 6 * (g α + 4 * g ((α + β) / 2) + g β)
      ∈ Set.Icc (M * (-(β - α) ^ 5 / 2880)) (c * (-(β - α) ^ 5 / 2880)) := by
  have huIcc : Set.uIcc α β = Set.Icc α β := Set.uIcc_of_le hαβ
  have hαm : α ≤ (α + β) / 2 := by linarith
  have hmβ : (α + β) / 2 ≤ β := by linarith
  have hsubL : Set.Icc α ((α + β) / 2) ⊆ Set.Icc α β := Set.Icc_subset_Icc le_rfl hmβ
  have hsubR : Set.Icc ((α + β) / 2) β ⊆ Set.Icc α β := Set.Icc_subset_Icc hαm le_rfl
  have hkey := sub_simpson_eq_integral_peanoKernel (g := g) (g' := g') (g'' := g'') (g₃ := g₃)
    (g₄ := g₄) (by rw [huIcc]; exact hg) (by rw [huIcc]; exact hg')
    (by rw [huIcc]; exact hg'') (by rw [huIcc]; exact hg₃)
    (ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hc₄))
  -- the two halves of the kernel are nonpositive
  have hkL : ∀ t ∈ Set.Icc α ((α + β) / 2), (t - α) ^ 3 * (3 * t - α - 2 * β) / 72 ≤ 0 := by
    intro t ht
    have h1 : (0 : ℝ) ≤ (t - α) ^ 3 := pow_nonneg (by linarith [ht.1]) 3
    have h2 : 3 * t - α - 2 * β ≤ 0 := by linarith [ht.2]
    have := mul_nonpos_of_nonneg_of_nonpos h1 h2
    linarith
  have hkR : ∀ t ∈ Set.Icc ((α + β) / 2) β, (t - β) ^ 3 * (3 * t - β - 2 * α) / 72 ≤ 0 := by
    intro t ht
    have h0 : t - β ≤ 0 := by linarith [ht.2]
    have h1 : (t - β) ^ 3 ≤ 0 := by
      have hcube : (t - β) ^ 3 = (t - β) * (t - β) ^ 2 := by ring
      rw [hcube]
      exact mul_nonpos_of_nonpos_of_nonneg h0 (sq_nonneg _)
    have h2 : (0 : ℝ) ≤ 3 * t - β - 2 * α := by linarith [ht.1]
    have := mul_nonpos_of_nonpos_of_nonneg h1 h2
    linarith
  have hcL : ContinuousOn (fun t : ℝ => (t - α) ^ 3 * (3 * t - α - 2 * β) / 72)
      (Set.Icc α ((α + β) / 2)) := by fun_prop
  have hcR : ContinuousOn (fun t : ℝ => (t - β) ^ 3 * (3 * t - β - 2 * α) / 72)
      (Set.Icc ((α + β) / 2) β) := by fun_prop
  have hupL := integral_nonpos_kernel_mul_le hαm hcL (hc₄.mono hsubL) hkL
    fun t ht => hlo t (hsubL ht)
  have hupR := integral_nonpos_kernel_mul_le hmβ hcR (hc₄.mono hsubR) hkR
    fun t ht => hlo t (hsubR ht)
  have hloL := le_integral_nonpos_kernel_mul hαm hcL (hc₄.mono hsubL) hkL
    fun t ht => hhi t (hsubL ht)
  have hloR := le_integral_nonpos_kernel_mul hmβ hcR (hc₄.mono hsubR) hkR
    fun t ht => hhi t (hsubR ht)
  rw [integral_simpsonKernel_left] at hupL hloL
  rw [integral_simpsonKernel_right] at hupR hloR
  rw [Set.mem_Icc, hkey]
  constructor <;> linarith

/-- **The composite Simpson rule error in mean value form.**  For `g` of class `C⁴` on `[a, b]`
and the uniform mesh `h = (b - a)/N`,

`∫_a^b g - (h/6) ∑_j (g(x_j) + 4 g(x_j + h/2) + g(x_{j+1})) = -(h⁴ (b - a)/2880) g⁗(ξ)`

for some `ξ` in `[a, b]`.  This is the extra order that a smooth integrand buys over the mere
convergence of `Quadrature.tendsto_simpsonSum`.  The panel error is
`Quadrature.sub_simpson_mem_Icc`; Simpson's Peano kernel does not change sign, so each panel error
lies between `-h⁵ M/2880` and `-h⁵ m/2880` with `m` and `M` the extreme values of `g⁗`, and the
intermediate value theorem collects the `N` panels into one value of `g⁗`. -/
theorem sub_composite_simpson_eq (hab : a < b) {N : ℕ} (hN : 0 < N) (hh : h = (b - a) / N)
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Icc a b, HasDerivAt g' (g'' x) x)
    (hg'' : ∀ x ∈ Set.Icc a b, HasDerivAt g'' (g₃ x) x)
    (hg₃ : ∀ x ∈ Set.Icc a b, HasDerivAt g₃ (g₄ x) x) (hc₄ : ContinuousOn g₄ (Set.Icc a b)) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ t in a..b, g t) - simpsonSum g a h N = -(h ^ 4 * (b - a) / 2880) * g₄ ξ := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hhpos : 0 < h := by rw [hh]; positivity
  set x : ℕ → ℝ := fun j => a + j * h with hxdef
  have hx0 : x 0 = a := by simp [hxdef]
  have hxN : x N = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    simp only [hxdef, hh, hc]
    ring
  have hxstep : ∀ j : ℕ, x (j + 1) - x j = h := by
    intro j; rw [hxdef]; push_cast; ring
  have hxmono : ∀ j : ℕ, x j ≤ x (j + 1) := fun j => by linarith [hxstep j, hhpos]
  have hxmem : ∀ j ≤ N, x j ∈ Set.Icc a b := fun j hj =>
    mem_Icc_of_partition hx0 hxN (fun j _ => hxmono j) hj
  have hxsub : ∀ j < N, Set.Icc (x j) (x (j + 1)) ⊆ Set.Icc a b := fun j hj =>
    Set.Icc_subset_Icc (hxmem j hj.le).1 (hxmem (j + 1) hj).2
  -- the extreme values of the fourth derivative
  obtain ⟨u, hu, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    ⟨a, Set.left_mem_Icc.2 hab.le⟩ hc₄
  obtain ⟨v, hv, hmax⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    ⟨a, Set.left_mem_Icc.2 hab.le⟩ hc₄
  set S : ℝ := -(h ^ 4 * (b - a) / 2880) with hS
  have hSneg : S < 0 := by
    have h4 : 0 < h ^ 4 := pow_pos hhpos 4
    have hba : 0 < b - a := by linarith
    rw [hS]
    nlinarith
  -- the two sided bound on one panel
  have hbound : ∀ j < N,
      g₄ v * (-h ^ 5 / 2880) ≤ (∫ t in (x j)..(x (j + 1)), g t)
          - h / 6 * (g (x j) + 4 * g (x j + h / 2) + g (x (j + 1)))
      ∧ (∫ t in (x j)..(x (j + 1)), g t)
          - h / 6 * (g (x j) + 4 * g (x j + h / 2) + g (x (j + 1)))
        ≤ g₄ u * (-h ^ 5 / 2880) := by
    intro j hj
    have hsub := hxsub j hj
    have hmid : (x j + x (j + 1)) / 2 = x j + h / 2 := by linarith [hxstep j]
    have hlen : x (j + 1) - x j = h := hxstep j
    have hmem := sub_simpson_mem_Icc (g := g) (g' := g') (g'' := g'') (g₃ := g₃) (g₄ := g₄)
      (c := g₄ u) (M := g₄ v) (hxmono j) (fun y hy => hg y (hsub hy))
      (fun y hy => hg' y (hsub hy)) (fun y hy => hg'' y (hsub hy))
      (fun y hy => hg₃ y (hsub hy)) (hc₄.mono hsub) (fun t ht => hmin (hsub ht))
      (fun t ht => hmax (hsub ht))
    rw [Set.mem_Icc, hmid, hlen] at hmem
    exact ⟨hmem.1, hmem.2⟩
  -- the error as a sum of panel errors
  have hint : ∀ j < N, IntervalIntegrable g volume (x j) (x (j + 1)) := by
    intro j hj
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    exact (hg y (hxsub j hj (by rwa [Set.uIcc_of_le (hxmono j)] at hy))).continuousAt
      |>.continuousWithinAt
  have hsimp : simpsonSum g a h N
      = ∑ j ∈ Finset.range N, h / 6 * (g (x j) + 4 * g (x j + h / 2) + g (x (j + 1))) := by
    rw [simpsonSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hxdef]
    push_cast
    ring
  have hsplit : (∫ t in a..b, g t) - simpsonSum g a h N
      = ∑ j ∈ Finset.range N, ((∫ t in (x j)..(x (j + 1)), g t)
          - h / 6 * (g (x j) + 4 * g (x j + h / 2) + g (x (j + 1)))) := by
    rw [hsimp, ← hx0, ← hxN, ← intervalIntegral.sum_integral_adjacent_intervals hint,
      ← Finset.sum_sub_distrib]
  -- sum the panel bounds
  have hNh : (N : ℝ) * h = b - a := by rw [hh]; field_simp
  have hsumS : ∑ _j ∈ Finset.range N, (-h ^ 5 / 2880) = S := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hS, ← hNh]
    ring
  set E : ℝ := (∫ t in a..b, g t) - simpsonSum g a h N with hE
  have hlow : g₄ v * S ≤ E := by
    rw [hsplit, ← hsumS, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (hbound j (Finset.mem_range.mp hj)).1
  have hhigh : E ≤ g₄ u * S := by
    rw [hsplit, ← hsumS, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (hbound j (Finset.mem_range.mp hj)).2
  -- the intermediate value theorem
  have hcmem : E / S ∈ Set.uIcc (g₄ u) (g₄ v) := by
    have h1 : g₄ u ≤ E / S := by
      rw [le_div_iff_of_neg hSneg]
      linarith [hhigh]
    have h2 : E / S ≤ g₄ v := by
      rw [div_le_iff_of_neg hSneg]
      linarith [hlow]
    exact Set.mem_uIcc_of_le h1 h2
  have huv : Set.uIcc u v ⊆ Set.Icc a b := Set.uIcc_subset_Icc hu hv
  obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_uIcc (hc₄.mono huv) hcmem
  refine ⟨ξ, huv hξ, ?_⟩
  have hSne : S ≠ 0 := ne_of_lt hSneg
  rw [hξval, mul_comm]
  exact (div_mul_cancel₀ E hSne).symm

end SimpsonError

section Circle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **The periodic trapezoidal rule** on the circle `AddCircle T`: the `n` equally spaced nodes
`j T / n` with the equal weights `T / n`.

On a periodic integrand the composite trapezoidal rule and the composite rectangle rule are the
same rule, because the two endpoints of the parameter interval are one and the same node of the
circle; that is why the periodic trapezoidal rule has no half weights. -/
noncomputable def circleTrapezoid (T : ℝ) [Fact (0 < T)] (n : ℕ) : C(AddCircle T, ℝ) →L[ℝ] ℝ :=
  functional (fun _ : Fin n => T / n) fun j : Fin n => (((j : ℕ) * (T / n) : ℝ) : AddCircle T)

/-- The periodic trapezoidal rule at an integrand, `h ∑_{j < n} v (j h)` with `h = T / n`. -/
theorem circleTrapezoid_apply (n : ℕ) (v : C(AddCircle T, ℝ)) :
    circleTrapezoid T n v
      = ∑ j ∈ Finset.range n, T / n * v (((j * (T / n) : ℝ) : AddCircle T)) := by
  rw [circleTrapezoid, functional_apply]
  exact Fin.sum_univ_eq_sum_range (fun j => T / n * v (((j * (T / n) : ℝ) : AddCircle T))) n

/-- The absolute weight sum of the periodic trapezoidal rule is the length of the circle, uniformly
in `n`: this is the hypothesis (12.4.3) of the Nyström theory. -/
theorem sum_abs_circleTrapezoid (n : ℕ) : ∑ _j : Fin n, |T / (n : ℝ)| ≤ T := by
  have hT0 : 0 < T := hT.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hT0.le
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ T / n)]
    rw [mul_div_cancel₀ _ hn0.ne']

/-- **The periodic trapezoidal rule converges for every continuous integrand.**  This is the
Riemann sum theorem `tendsto_compositeSum` transported to the circle by
`AddCircle.intervalIntegral_preimage`, and it is the hypothesis that the Nyström method for a
boundary integral equation asks of its quadrature rules. -/
theorem tendsto_circleTrapezoid (v : C(AddCircle T, ℝ)) :
    Tendsto (fun n => circleTrapezoid T n v) atTop (𝓝 (∫ x, v x ∂MeasureTheory.volume)) := by
  have hT0 : 0 < T := hT.out
  have hgc : Continuous fun x : ℝ => v ((x : AddCircle T)) :=
    v.continuous.comp (AddCircle.continuous_mk' T)
  have hint : (∫ x in (0 : ℝ)..T, v ((x : AddCircle T))) = ∫ x, v x ∂MeasureTheory.volume := by
    have h := AddCircle.intervalIntegral_preimage T 0 v
    rwa [zero_add] at h
  rw [← hint, ← Filter.tendsto_add_atTop_iff_nat 1]
  have hstep : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hmesh : ∀ n j : ℕ,
      ((j : ℝ) + 1) * (T / ((n : ℝ) + 1)) - (j : ℝ) * (T / ((n : ℝ) + 1)) = T / ((n : ℝ) + 1) :=
    fun n j => by ring
  have hh : Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
  have hmain := tendsto_compositeSum (a := 0) (b := T) hT0.le hgc.continuousOn
    (N := fun n => n + 1) (t := fun n j => (j : ℝ) * (T / ((n : ℝ) + 1)))
    (hs := fun n => T / ((n : ℝ) + 1)) (fun n => by simp)
    (fun n => by push_cast; field_simp) (fun n j _ => by
      have : (0 : ℝ) ≤ T / ((n : ℝ) + 1) := by positivity
      push_cast
      nlinarith [this])
    (fun n j _ => by push_cast; rw [hmesh n j]) hh (ω := fun _ : Fin 1 => (1 : ℝ))
    (fun _ => zero_le_one) (by simp)
    (y := fun n j _ => (j : ℝ) * (T / ((n : ℝ) + 1)))
    (fun n j hj _ => by
      refine ⟨le_rfl, ?_⟩
      have : (0 : ℝ) ≤ T / ((n : ℝ) + 1) := by positivity
      push_cast
      nlinarith [this])
  refine hmain.congr fun n => ?_
  rw [circleTrapezoid_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [hmesh n j]
  simp

end Circle

end Quadrature
