import Mathlib.Analysis.Convex.Exposed
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Subgradient.Bounded

/-!
# Convergence of directional derivatives and of subgradients

Convex functions `f i`, finite on an open convex set `U` and converging pointwise there to `g`,
converge uniformly on compact subsets, hence *continuously*: `f i (x i) → g x` along any `x i → x`
in `U`. Differentiation does **not** pass to the limit; only the one-sided `limsup` inequality
survives. For `x i → x` in `U` and `y i → y`,

```
limsup_i (f i)'(x i; y i)  ≤  g'(x; y),        ∂(f i)(x i)  ⊆  ∂g(x) + ε B  eventually.
```

Equality can fail: for `f i x = |x|^{p i}` with `p i ↓ 1` on `U = ℝ`, every `(f i)'(0; 1)` is `0`
while `g'(0; 1) = 1`. Taking the family constant turns the two statements into upper semicontinuity
of `f'(x; y)` in `(x, y)` and of `∂f` in `x`.

## Main results

* `tendsto_eval_of_tendsto` — continuous convergence: `f i (x i) → g x`.
* `eventually_dirDeriv_lt`, `eventually_subgradient_subset_add_closedBall` — the two displayed
  statements (Theorem 24.5 in [^1]). The first is spelled without junk values: every real `μ` above
  `g'(x; y)` eventually bounds `(f i)'(x i; y i)`.
* `upperSemicontinuousAt_dirDeriv`, `eventually_nhds_subgradient_subset_add_closedBall` — the
  constant-family case: upper semicontinuity of `f'(x; y)` and of `∂f`.
* `eventually_dirDeriv_lt_of_tendsto_dir`, `eventually_subgradient_subset_exposed_add_closedBall` —
  the same two statements (Theorem 24.6 in [^1]) for an approach to a point of `dom f` that need
  not be interior, along a fixed limiting direction `y`, with the face of `∂f x` exposed by `y` in
  place of `∂f x`.
* `subgradient_dirDeriv` — the identification `∂(f'(x; ·))(y) = ∂f(x)_y`.

## Implementation notes

The convergence theory is stated for real-valued `ConvexOn ℝ U (f i)` while subgradients are
`EReal`-valued; the bridge is `ConvexFn.convexOn_toReal_dom`. `ε B` needs a norm on the dual side,
so the subgradient statements are for a real inner-product space paired with itself.

Two classical hypotheses are absent: the sequence need not lie in `U`, only converge to a point of
it, and the approach to a boundary point needs neither closedness of `f` nor the usual simplex
construction — monotonicity of the difference quotient in its step replaces the vanishing step
`‖x i - x‖` by a fixed larger one, after which only continuity at *interior* points is used.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §24.
-/

open Set Filter Topology
open scoped NNReal Pointwise RealInnerProductSpace

namespace ConvexAnalysis

/-! ### Support function of a ball -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function of the ball of radius `ε` about the origin is `ε ‖·‖`. -/
theorem supportFn_closedBall {ε : ℝ} (hε : 0 ≤ ε) (y : E) :
    supportFn (innerₗ E) (Metric.closedBall (0 : E) ε) y = ((ε * ‖y‖ : ℝ) : EReal) := by
  refine le_antisymm (supportFn_le_coe_iff.2 fun z hz => ?_) ?_
  · rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hcs : (innerₗ E) z y ≤ ‖z‖ * ‖y‖ := by
      rw [innerₗ_apply_apply]; exact real_inner_le_norm z y
    exact hcs.trans (by gcongr)
  · rcases eq_or_ne y 0 with rfl | hy
    · have h0 : (0 : E) ∈ Metric.closedBall (0 : E) ε := Metric.mem_closedBall_self hε
      have h := le_supportFn (B := innerₗ E) h0 (0 : E)
      simpa using h
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hmem : (ε / ‖y‖) • y ∈ Metric.closedBall (0 : E) ε := by
      have hpos : (0 : ℝ) ≤ ε / ‖y‖ := by positivity
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpos]
      field_simp
      exact le_rfl
    have h := le_supportFn (B := innerₗ E) hmem y
    have hval : (innerₗ E) ((ε / ‖y‖) • y) y = ε * ‖y‖ := by
      rw [innerₗ_apply_apply, real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      field_simp
    rwa [hval] at h

end Ball

/-! ### The directional derivative at an interior point -/

section Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → EReal} {x : E}

/-- At an interior point of `dom f` the directional derivative is finite in every direction, so it
is the coercion of its own real value. -/
theorem dirDeriv_eq_coe_toReal_of_mem_interior_dom (hg : ConvexFn g) (hgp : Proper g)
    (hx : x ∈ interior (dom g)) (z : E) :
    dirDeriv g x z = (((dirDeriv g x z).toReal : ℝ) : EReal) := by
  have hri : x ∈ ri (dom g) := Convex.interior_subset_relint hg.convex_dom ⟨x, hx⟩ hx
  have hbot : dirDeriv g x z ≠ ⊥ := (proper_dirDeriv_of_mem_relint_dom hg hgp hri).ne_bot z
  have hdom := (dom_dirDeriv_eq_univ_iff_mem_interior_dom hg hgp hri).2 hx
  have htop : dirDeriv g x z ≠ ⊤ := (mem_dom.1 (hdom ▸ Set.mem_univ z)).ne
  exact (_root_.EReal.coe_toReal htop hbot).symm

/-- At an interior point of `dom f` the directional derivative is a *finite* convex function on the
whole space. -/
theorem convexOn_toReal_dirDeriv (hg : ConvexFn g) (hgp : Proper g)
    (hx : x ∈ interior (dom g)) :
    ConvexOn ℝ (univ : Set E) fun z => (dirDeriv g x z).toReal := by
  have hri : x ∈ ri (dom g) := Convex.interior_subset_relint hg.convex_dom ⟨x, hx⟩ hx
  have hdom := (dom_dirDeriv_eq_univ_iff_mem_interior_dom hg hgp hri).2 hx
  have hxdom : x ∈ dom g := interior_subset hx
  have h := (convexFn_dirDeriv hg (mem_dom.1 hxdom).ne (hgp.ne_bot x)).convexOn_toReal_dom
    (proper_dirDeriv_of_mem_relint_dom hg hgp hri)
  rwa [hdom] at h

/-- Positive homogeneity of the directional derivative, read on real values. -/
theorem toReal_dirDeriv_smul (hg : ConvexFn g) (hgp : Proper g) (hx : x ∈ interior (dom g))
    {c : ℝ} (hc : 0 < c) (z : E) :
    (dirDeriv g x (c • z)).toReal = c * (dirDeriv g x z).toReal := by
  have h := posHomogeneous_dirDeriv g x c hc z
  rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom hg hgp hx z, ← _root_.EReal.coe_mul] at h
  rw [h, _root_.EReal.toReal_coe]

end Interior

/-! ### Continuous convergence -/

section Eval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → ℝ} {g : E → ℝ}

/-- Convex functions converging pointwise on an open convex set converge *continuously* there:
the values `f i (x i)` along any sequence `x i → x` converge to `g x`. This is the practical form of
the fact that pointwise convergence of convex functions is uniform on compact subsets. -/
theorem tendsto_eval_of_tendsto (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexOn ℝ U (f i)) (hg : ConvexOn ℝ U g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun i => f i (xs i)) atTop (𝓝 (g x)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hhalf : 0 < r / 2 := by linarith
  have hSU : Metric.closedBall x (r / 2) ⊆ U := fun z hz =>
    hball (Metric.closedBall_subset_ball (by linarith) hz)
  have huc := tendstoUniformlyOn_of_tendsto hU hUc hf hconv
    (isCompact_closedBall x (r / 2)) hSU
  have hcont : ContinuousWithinAt g (Metric.closedBall x (r / 2)) x := by
    have hgU : ContinuousOn g U := by
      rw [← hU.interior_eq]; exact hg.continuousOn_interior
    exact ((hgU.continuousAt (hU.mem_nhds hx)).continuousWithinAt)
  have hnw : Tendsto xs atTop (𝓝[Metric.closedBall x (r / 2)] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hxs, hxs.eventually_mem (Metric.closedBall_mem_nhds x hhalf)⟩
  exact huc.tendsto_comp hcont hnw

end Eval

/-! ### Upper semicontinuity of the directional derivative -/

section DirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal}

/-- **Directional derivatives are upper semicontinuous under pointwise convergence.** If convex
functions `f i`, finite on an open convex `U`, converge pointwise there to `g`, and if
`x i → x ∈ U` and `y i → y`, then

```
limsup_i (f i)'(x i; y i) ≤ g'(x; y).
```

The `limsup` is spelled without junk values: every real `μ` above `g'(x; y)` eventually bounds
`(f i)'(x i; y i)`. -/
theorem eventually_dirDeriv_lt (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i))
    (hg : ConvexFn g) (hgp : Proper g) (hgU : U ⊆ dom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    {x : E} (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x))
    {y : E} {ys : ℕ → E} (hys : Tendsto ys atTop (𝓝 y))
    {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  set F : ℕ → E → ℝ := fun i z => (f i z).toReal with hFdef
  set G : E → ℝ := fun z => (g z).toReal with hGdef
  have hgeq : ∀ z ∈ U, g z = ((G z : ℝ) : EReal) := fun z hz =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hgU hz)).ne (hgp.ne_bot z)).symm
  have hfeq : ∀ i, ∀ z ∈ U, f i z = ((F i z : ℝ) : EReal) := fun i z hz =>
    (_root_.EReal.coe_toReal (mem_dom.1 (hfU i hz)).ne ((hfp i).ne_bot z)).symm
  have hFconv : ∀ i, ConvexOn ℝ U (F i) := fun i =>
    ((hf i).convexOn_toReal_dom (hfp i)).subset (hfU i) hUc
  have hGconv : ConvexOn ℝ U G := (hg.convexOn_toReal_dom hgp).subset hgU hUc
  have hconvR : ∀ z ∈ U, Tendsto (fun i => F i z) atTop (𝓝 (G z)) := by
    intro z hz
    rw [← _root_.EReal.tendsto_coe]
    have hfun : (fun i => ((F i z : ℝ) : EReal)) = fun i => f i z := by
      funext i; exact (hfeq i z hz).symm
    rw [hfun, ← hgeq z hz]
    exact hconv z hz
  -- A step `a > 0` small enough to stay in `U` and to realise a quotient below `μ`.
  obtain ⟨a₀, ha₀, hlt0⟩ := dirDeriv_lt_iff.1 hμ
  have hmemU : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • y ∈ U := by
    have hc : Continuous fun t : ℝ => x + t • y := by fun_prop
    have hc0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at hc0
    exact hc0.eventually_mem (hU.mem_nhds hx)
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.1 hmemU
  set a : ℝ := min a₀ (δ / 2) with hadef
  have ha : 0 < a := lt_min ha₀ (by linarith)
  have haU : x + a • y ∈ U := by
    refine hδU ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hq : (g (x + a • y) - g x) / (a : EReal) < (μ : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hg (hgeq x hx) y (mem_Ioi.2 ha) (mem_Ioi.2 ha₀)
      (min_le_left _ _)) hlt0
  have hquotR : (G (x + a • y) - G x) / a < μ := by
    rw [hgeq _ haU, hgeq x hx, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div,
      _root_.EReal.coe_lt_coe_iff] at hq
    exact hq
  -- Continuous convergence at the two moving points.
  have hzs : Tendsto (fun i => xs i + a • ys i) atTop (𝓝 (x + a • y)) := hxs.add (hys.const_smul a)
  have hev1 : Tendsto (fun i => F i (xs i)) atTop (𝓝 (G x)) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR hx hxs
  have hev2 : Tendsto (fun i => F i (xs i + a • ys i)) atTop (𝓝 (G (x + a • y))) :=
    tendsto_eval_of_tendsto hU hUc hFconv hGconv hconvR haU hzs
  have hevlt : ∀ᶠ i in atTop, (F i (xs i + a • ys i) - F i (xs i)) / a < μ :=
    ((hev2.sub hev1).div_const a).eventually_lt_const hquotR
  filter_upwards [hevlt, hxs.eventually_mem (hU.mem_nhds hx),
    hzs.eventually_mem (hU.mem_nhds haU)] with i hi hiU hiU'
  calc dirDeriv (f i) (xs i) (ys i)
      ≤ (f i (xs i + a • ys i) - f i (xs i)) / (a : EReal) := dirDeriv_le _ _ _ ha
    _ = (((F i (xs i + a • ys i) - F i (xs i)) / a : ℝ) : EReal) := by
        rw [hfeq i _ hiU', hfeq i _ hiU, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div]
    _ < (μ : EReal) := by exact_mod_cast hi

end DirDeriv

/-! ### The local form, for a single function -/

section LocalDirDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- `f'(x; y)` is upper semicontinuous in `(x, y)` on `int (dom f) × E`. This
is the previous theorem for the constant sequence `f, f, f, …`, transported from sequences to the
neighbourhood filter. -/
theorem upperSemicontinuousAt_dirDeriv (hf : ConvexFn f) (hfp : Proper f)
    (hx : x ∈ interior (dom f)) (y : E) :
    UpperSemicontinuousAt (fun p : E × E => dirDeriv f p.1 p.2) (x, y) := by
  intro c hc
  obtain ⟨μ, hμ₁, hμ₂⟩ := _root_.EReal.lt_iff_exists_real_btwn.1 hc
  have h : ∀ᶠ p : E × E in 𝓝 (x, y), dirDeriv f p.1 p.2 < (μ : EReal) := by
    rw [Filter.eventually_iff_seq_eventually]
    intro ps hps
    rw [nhds_prod_eq] at hps
    exact eventually_dirDeriv_lt isOpen_interior hf.convex_dom.interior (fun _ => hf)
      (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
      (fun z _ => tendsto_const_nhds) hx hps.fst hps.snd hμ₁
  exact h.mono fun p hp => hp.trans hμ₂

end LocalDirDeriv

/-! ### Upper semicontinuity of the subdifferential -/

section Subgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : Set E} {f : ℕ → E → EReal} {g : E → EReal} {x : E}

/-- The support function of `∂f x` is `f'(x; ·)`, for a real inner-product space paired with
itself, a special case of the same identity for an arbitrary pairing. -/
theorem supportFn_subgradient (hg : ConvexFn g) (hgp : Proper g) (hx : x ∈ ri (dom g)) :
    supportFn (innerₗ E) (subgradient (innerₗ E) g x) = dirDeriv g x := by
  rw [dirDeriv_eq_supportFn_of_mem_relint_dom (B := innerₗ E) hg hgp hx, flip_innerₗ]

/-- The support-function endgame shared by the two subgradient statements below. If the directional
derivative of `p` at an interior point `u` of `dom p` is dominated on the unit ball by that of `q`
at an interior point `v` of `dom q`, up to `ε`, then `∂p u ⊆ ∂q v + ε B`. Positive homogeneity
spreads the bound to every direction, and support functions order closed convex sets. -/
theorem subgradient_subset_add_closedBall_of_forall_dirDeriv_le {p q : E → EReal} {u v : E}
    (hp : ConvexFn p) (hpp : Proper p) (hu : u ∈ interior (dom p))
    (hq : ConvexFn q) (hqp : Proper q) (hv : v ∈ interior (dom q)) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv p u z).toReal ≤ (dirDeriv q v z).toReal + ε) :
    subgradient (innerₗ E) p u ⊆ subgradient (innerₗ E) q v + Metric.closedBall (0 : E) ε := by
  have huri : u ∈ ri (dom p) := Convex.interior_subset_relint hp.convex_dom ⟨u, hu⟩ hu
  have hvri : v ∈ ri (dom q) := Convex.interior_subset_relint hq.convex_dom ⟨v, hv⟩ hv
  have hhom : ∀ z : E, dirDeriv p u z ≤ (((dirDeriv q v z).toReal + ε * ‖z‖ : ℝ) : EReal) := by
    intro z
    have hreal : (dirDeriv p u z).toReal ≤ (dirDeriv q v z).toReal + ε * ‖z‖ := by
      rcases eq_or_ne z 0 with rfl | hz
      · have h1 : dirDeriv p u 0 = 0 :=
          dirDeriv_zero (mem_dom.1 (interior_subset hu)).ne (hpp.ne_bot u)
        have h2 : dirDeriv q v 0 = 0 :=
          dirDeriv_zero (mem_dom.1 (interior_subset hv)).ne (hqp.ne_bot v)
        simp [h1, h2]
      have hc : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
      have hwz : ‖z‖ • (‖z‖⁻¹ • z) = z := by
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      have hwnorm : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_cancel₀ hc.ne']
      have hbz := hb ((‖z‖⁻¹ : ℝ) • z) (by rw [Metric.mem_closedBall, dist_zero_right, hwnorm])
      have hpz := toReal_dirDeriv_smul hp hpp hu hc ((‖z‖⁻¹ : ℝ) • z)
      have hqz := toReal_dirDeriv_smul hq hqp hv hc ((‖z‖⁻¹ : ℝ) • z)
      rw [hwz] at hpz hqz
      calc (dirDeriv p u z).toReal
          = ‖z‖ * (dirDeriv p u ((‖z‖⁻¹ : ℝ) • z)).toReal := hpz
        _ ≤ ‖z‖ * ((dirDeriv q v ((‖z‖⁻¹ : ℝ) • z)).toReal + ε) :=
            mul_le_mul_of_nonneg_left hbz (norm_nonneg z)
        _ = ‖z‖ * (dirDeriv q v ((‖z‖⁻¹ : ℝ) • z)).toReal + ε * ‖z‖ := by ring
        _ = (dirDeriv q v z).toReal + ε * ‖z‖ := by rw [← hqz]
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom hp hpp hu z]
    exact_mod_cast hreal
  have hcpt : IsCompact (subgradient (innerₗ E) q v) := isCompact_subgradient hq hqp hv
  have hcvx : Convex ℝ (subgradient (innerₗ E) q v + Metric.closedBall (0 : E) ε) :=
    (convex_subgradient _ _ _).add (convex_closedBall _ _)
  have hcptsum : IsCompact (subgradient (innerₗ E) q v + Metric.closedBall (0 : E) ε) :=
    hcpt.add (isCompact_closedBall _ _)
  have hsupple : supportFn (innerₗ E) (subgradient (innerₗ E) p u)
      ≤ supportFn (innerₗ E) (subgradient (innerₗ E) q v + Metric.closedBall (0 : E) ε) := by
    intro z
    rw [supportFn_add, Pi.add_apply, supportFn_subgradient hp hpp huri,
      supportFn_subgradient hq hqp hvri, supportFn_closedBall hε.le]
    calc dirDeriv p u z ≤ (((dirDeriv q v z).toReal + ε * ‖z‖ : ℝ) : EReal) := hhom z
      _ = dirDeriv q v z + ((ε * ‖z‖ : ℝ) : EReal) := by
          rw [_root_.EReal.coe_add, ← dirDeriv_eq_coe_toReal_of_mem_interior_dom hq hqp hv z]
  have hincl := (closure_convexHull_subset_iff_supportFn_le (B := innerₗ E) _ _).2 hsupple
  rw [hcvx.convexHull_eq, hcptsum.isClosed.closure_eq] at hincl
  exact fun w hw => hincl (subset_closure (subset_convexHull ℝ _ hw))

/-- **Subdifferentials are upper semicontinuous under pointwise convergence.** If convex functions
`f i`, finite on an open convex `U`, converge pointwise there to `g`, and `x i → x` inside `U`,
then for every `ε > 0`

```
∂(f i)(x i) ⊆ ∂g(x) + ε B
```

for all large `i`, where `B` is the closed unit ball. The subdifferentials are the support sets of
the directional derivatives, and the previous theorem bounds those pointwise; the bound is made
uniform on the compact unit ball and then spread by positive homogeneity. -/
theorem eventually_subgradient_subset_add_closedBall (hU : IsOpen U) (hUc : Convex ℝ U)
    (hf : ∀ i, ConvexFn (f i)) (hfp : ∀ i, Proper (f i)) (hfU : ∀ i, U ⊆ dom (f i))
    (hg : ConvexFn g) (hgp : Proper g) (hgU : U ⊆ dom g)
    (hconv : ∀ z ∈ U, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hx : x ∈ U) {xs : ℕ → E} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradient (innerₗ E) (f i) (xs i)
      ⊆ subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε := by
  classical
  -- Replace `xs` by a sequence lying in `U` for *every* index; the two agree eventually.
  have hxsU : ∀ᶠ i in atTop, xs i ∈ U := hxs.eventually_mem (hU.mem_nhds hx)
  set xs' : ℕ → E := fun i => if xs i ∈ U then xs i else x with hxs'def
  have hxs'eq : ∀ᶠ i in atTop, xs' i = xs i :=
    hxsU.mono fun i hi => by simp only [hxs'def, hi, ite_true]
  have hxsU' : ∀ i, xs' i ∈ U := fun i => by
    simp only [hxs'def]
    split
    · assumption
    · exact hx
  have hxs' : Tendsto xs' atTop (𝓝 x) := hxs.congr' (hxs'eq.mono fun i hi => hi.symm)
  suffices h : ∀ᶠ i in atTop, subgradient (innerₗ E) (f i) (xs' i)
      ⊆ subgradient (innerₗ E) g x + Metric.closedBall (0 : E) ε by
    filter_upwards [h, hxs'eq] with i hi hieq
    rwa [hieq] at hi
  have hxint : x ∈ interior (dom g) := interior_maximal hgU hU hx
  have hxsint : ∀ i, xs' i ∈ interior (dom (f i)) := fun i => interior_maximal (hfU i) hU (hxsU' i)
  -- The pointwise bound of the previous theorem, in real form.
  have hle : ∀ z ∈ (univ : Set E), ∀ δ > 0, ∀ᶠ i in atTop,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + δ := by
    intro z _ δ hδ
    have hlt : dirDeriv g x z < (((dirDeriv g x z).toReal + δ : ℝ) : EReal) :=
      lt_of_eq_of_lt (dirDeriv_eq_coe_toReal_of_mem_interior_dom hg hgp hxint z)
        (_root_.EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_dirDeriv_lt hU hUc hf hfp hfU hg hgp hgU hconv hx hxs'
      (ys := fun _ => z) tendsto_const_nhds hlt] with i hi
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom (hf i) (hfp i) (hxsint i) z] at hi
    exact (_root_.EReal.coe_lt_coe_iff.1 hi).le
  -- Made uniform on the unit ball.
  have hunif : ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv (f i) (xs' i) z).toReal ≤ (dirDeriv g x z).toReal + ε :=
    eventually_forall_le_add_of_eventually_le isOpen_univ convex_univ
      (fun i => convexOn_toReal_dirDeriv (hf i) (hfp i) (hxsint i))
      (convexOn_toReal_dirDeriv hg hgp hxint) hle (isCompact_closedBall (0 : E) 1)
      (subset_univ _) hε
  filter_upwards [hunif] with i hi
  exact subgradient_subset_add_closedBall_of_forall_dirDeriv_le (hf i) (hfp i) (hxsint i)
    hg hgp hxint hε hi

end Subgradient

/-! ### The local form of the subgradient statement -/

section LocalSubgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- `∂f` is upper semicontinuous at every interior point of `dom f`, so that
`∂f z ⊆ ∂f x + ε B` for all `z` in a neighbourhood of `x`. -/
theorem eventually_nhds_subgradient_subset_add_closedBall (hf : ConvexFn f) (hfp : Proper f)
    (hx : x ∈ interior (dom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 x, subgradient (innerₗ E) f z
      ⊆ subgradient (innerₗ E) f x + Metric.closedBall (0 : E) ε := by
  rw [Filter.eventually_iff_seq_eventually]
  intro zs hzs
  exact eventually_subgradient_subset_add_closedBall isOpen_interior hf.convex_dom.interior
    (fun _ => hf) (fun _ => hfp) (fun _ => interior_subset) hf hfp interior_subset
    (fun z _ => tendsto_const_nhds) hx hzs hε

end LocalSubgradient

/-! ### Approach to a point of the domain along a direction -/

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x y : E}

omit [FiniteDimensional ℝ E] in
/-- **The segment principle for effective domains**: if `x ∈ dom f` and `x + α • u` is interior to
`dom f`, then so is `x + t • u` for every `t` in `(0, α]`. -/
theorem mem_interior_dom_smul (hf : ConvexFn f) (hx : x ∈ dom f) {u : E} {α t : ℝ} (hα : 0 < α)
    (hu : x + α • u ∈ interior (dom f)) (ht : 0 < t) (htα : t ≤ α) :
    x + t • u ∈ interior (dom f) := by
  have hle : (0 : ℝ) ≤ 1 - t / α := by
    rw [sub_nonneg]
    exact (div_le_one hα).2 htα
  have h := hf.convex_dom.combo_interior_self_mem_interior hu hx (a := t / α) (b := 1 - t / α)
    (by positivity) hle (by ring)
  have heq : (t / α) • (x + α • u) + (1 - t / α) • x = x + t • u := by
    match_scalars <;> (field_simp; try ring)
  rwa [heq] at h

omit [FiniteDimensional ℝ E] in
/-- An approach with a limiting direction that points into the interior is eventually interior: if
`x i → x ∈ dom f` with `x i ≠ x`, the unit vectors `‖x i - x‖⁻¹ (x i - x)` converge to `y`, and
`x + α y` is interior to `dom f` for some `α > 0`, then `x i ∈ int (dom f)` for all large `i`. This
is what makes the subgradient half of the boundary statement reachable: the sublinear functions
`f'(x i; ·)` are then finite everywhere, so the uniform-convergence theory applies to them. -/
theorem eventually_mem_interior_dom_of_tendsto_dir (hf : ConvexFn f) (hx : x ∈ dom f)
    {xs : ℕ → E} (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) :
    ∀ᶠ i in atTop, xs i ∈ interior (dom f) := by
  have heten : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 0) := by
    have h : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 ‖x - x‖) := (hxs.sub_const x).norm
    rwa [sub_self, norm_zero] at h
  have hmem : ∀ᶠ i in atTop, x + α • (‖xs i - x‖⁻¹ • (xs i - x)) ∈ interior (dom f) :=
    (((by fun_prop : Continuous fun v : E => x + α • v).tendsto _).comp hdir).eventually_mem
      (isOpen_interior.mem_nhds hαy)
  filter_upwards [hmem, heten.eventually_le_const hα] with i hi hie
  have hpos : 0 < ‖xs i - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (hxsne i))
  have h := mem_interior_dom_smul hf hx hα hi hpos hie
  rwa [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul,
    show x + (xs i - x) = xs i from by abel] at h

omit [FiniteDimensional ℝ E] in
/-- **A ray into the interior makes the direction interior to the domain of `f'(x; ·)`**: if
`x + α • y` is interior to `dom f` for some `α > 0`, then `y` is interior to `dom f'(x; ·)`,
because a single difference quotient bounds `f'(x; ·)` above near `y`. -/
theorem mem_interior_dom_dirDeriv (hfp : Proper f) (hx : x ∈ dom f) {α : ℝ}
    (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f)) :
    y ∈ interior (dom (dirDeriv f x)) := by
  have hcont : Continuous fun v : E => x + α • v := by fun_prop
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot x) (mem_dom.1 hx)
  refine interior_maximal (fun v hv => ?_) (hcont.isOpen_preimage _ isOpen_interior)
    (show y ∈ (fun v : E => x + α • v) ⁻¹' interior (dom f) from hαy)
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + α • v))
    (mem_dom.1 (interior_subset hv))
  refine mem_dom.2 (lt_of_le_of_lt (dirDeriv_le f x v hα) ?_)
  rw [hs, hr, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div]
  exact _root_.EReal.coe_lt_top _

/-- **`f'(x; ·)` is proper once it is finite at one interior point of its effective domain.** A
convex function that takes the value `-∞` takes it throughout the relative interior of its domain,
so a single finite interior value rules `-∞` out everywhere. -/
theorem proper_dirDeriv_of_ne_bot (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f)
    (hy : y ∈ interior (dom (dirDeriv f x))) (hne : dirDeriv f x y ≠ ⊥) :
    Proper (dirDeriv f x) := by
  have hconv : ConvexFn (dirDeriv f x) := convexFn_dirDeriv hf (mem_dom.1 hx).ne (hfp.ne_bot x)
  by_contra h
  exact hne (ConvexFn.eq_bot_of_mem_relint_dom hconv h
    (Convex.interior_subset_relint hconv.convex_dom ⟨y, hy⟩ hy))

/-- **The directional-derivative half**: directional derivatives are upper
semicontinuous along an approach to a point of `dom f` that need not be interior, provided the
approach has a limiting direction `y` and the second-order derivative in that direction is the
bound.

If `x i → x` inside `dom f` with `x i ≠ x` and the unit vectors `|x i - x|⁻¹ (x i - x)` converge to
`y`, and if `f'(x; y) > -∞` while the ray `x + ℝ₊ y` meets `int (dom f)`, then

```
limsup_i f'(x i; z) ≤ f'(x; y; z) := (f'(x; ·))'(y; z),        ∀ z.
```

As in `eventually_dirDeriv_lt` the `limsup` is spelled without junk values: every real `μ` above
`f'(x; y; z)` eventually bounds `f'(x i; z)`. -/
theorem eventually_dirDeriv_lt_of_tendsto_dir (hf : ConvexFn f) (hfp : Proper f) (hx : x ∈ dom f)
    {xs : ℕ → E} (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    (hy : dirDeriv f x y ≠ ⊥) {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f))
    {z : E} {μ : ℝ} (hμ : dirDeriv (dirDeriv f x) y z < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv f (xs i) z < (μ : EReal) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot x) (mem_dom.1 hx)
  have hgconv : ConvexFn (dirDeriv f x) :=
    convexFn_dirDeriv hf (mem_dom.1 hx).ne (hfp.ne_bot x)
  have hyint : y ∈ interior (dom (dirDeriv f x)) := mem_interior_dom_dirDeriv hfp hx hα hαy
  have hgp : Proper (dirDeriv f x) := proper_dirDeriv_of_ne_bot hf hfp hx hyint hy
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hgp.ne_bot y)
    (mem_dom.1 (interior_subset hyint))
  -- A step `lam > 0` realising a quotient of `f'(x; ·)` below `μ` and keeping the ray interior.
  obtain ⟨lam0, hlam0, hq0⟩ := dirDeriv_lt_iff.1 hμ
  have hmemW : ∀ᶠ t in 𝓝 (0 : ℝ), x + α • (y + t • z) ∈ interior (dom f) := by
    have hcont : Continuous fun t : ℝ => x + α • (y + t • z) := by fun_prop
    have h0 := hcont.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.eventually_mem (isOpen_interior.mem_nhds hαy)
  obtain ⟨δ, hδ, hδW⟩ := Metric.eventually_nhds_iff.1 hmemW
  set lam : ℝ := min lam0 (δ / 2) with hlamdef
  have hlampos : 0 < lam := lt_min hlam0 (by linarith)
  have hlamle : lam ≤ lam0 := min_le_left _ _
  have hlamW : x + α • (y + lam • z) ∈ interior (dom f) := by
    refine hδW ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos hlampos]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hqlam : (dirDeriv f x (y + lam • z) - dirDeriv f x y) / (lam : EReal) < (μ : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hgconv hc z (mem_Ioi.2 hlampos) (mem_Ioi.2 hlam0) hlamle)
      hq0
  have hgu : dirDeriv f x (y + lam • z) < ((c + μ * lam : ℝ) : EReal) := by
    rw [hc] at hqlam
    by_contra hcon
    push Not at hcon
    exact absurd ((EReal.coe_le_sub_div_iff hlampos _).2 hcon) (not_le.2 hqlam)
  -- A step `b > 0`, at most `α / 2`, realising a quotient of `f` below `c + μ lam`.
  obtain ⟨b0, hb0, hqb0⟩ := dirDeriv_lt_iff.1 hgu
  set b : ℝ := min b0 (α / 2) with hbdef
  have hbpos : 0 < b := lt_min hb0 (by linarith)
  have hble : b ≤ b0 := min_le_left _ _
  have hbα : b ≤ α / 2 := min_le_right _ _
  have hqb : (f (x + b • (y + lam • z)) - f x) / (b : EReal) < ((c + μ * lam : ℝ) : EReal) :=
    lt_of_le_of_lt (monotoneOn_sub_div hf hr (y + lam • z) (mem_Ioi.2 hbpos) (mem_Ioi.2 hb0) hble)
      hqb0
  have hbu : x + b • (y + lam • z) ∈ interior (dom f) :=
    mem_interior_dom_smul hf hx hα hlamW hbpos (by linarith)
  -- The three sequences.
  obtain ⟨e, Y, U, hedef, hYdef, hUdef⟩ :
      ∃ (e : ℕ → ℝ) (Y U : ℕ → E), (∀ i, e i = ‖xs i - x‖) ∧
        (∀ i, Y i = (e i)⁻¹ • (xs i - x)) ∧ (∀ i, U i = Y i + lam • z) :=
    ⟨_, _, fun i => ‖xs i - x‖⁻¹ • (xs i - x) + lam • z, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hepos : ∀ i, 0 < e i := fun i => by
    rw [hedef]
    exact norm_pos_iff.2 (sub_ne_zero.2 (hxsne i))
  have heten : Tendsto e atTop (𝓝 0) := by
    have h : Tendsto (fun i => ‖xs i - x‖) atTop (𝓝 ‖x - x‖) := (hxs.sub_const x).norm
    rw [sub_self, norm_zero] at h
    exact h.congr fun i => (hedef i).symm
  have hYten : Tendsto Y atTop (𝓝 y) := hdir.congr fun i => by rw [hYdef, hedef]
  have hUten : Tendsto U atTop (𝓝 (y + lam • z)) :=
    (hYten.add_const (lam • z)).congr fun i => (hUdef i).symm
  -- The two limits, on the two sides of the inequality.
  have hScont : ContinuousAt (fun v => (dirDeriv f x v).toReal) y :=
    (hgconv.continuousOn_toReal_relint_dom hgp).continuousAt (mem_nhds_iff.2
      ⟨interior (dom (dirDeriv f x)),
        Convex.interior_subset_relint hgconv.convex_dom ⟨y, hyint⟩, isOpen_interior, hyint⟩)
  have hSten : Tendsto (fun i => (dirDeriv f x (Y i)).toReal) atTop (𝓝 c) := by
    have h := hScont.tendsto.comp hYten
    rwa [hc, _root_.EReal.toReal_coe] at h
  have hFcont : ContinuousAt (fun v => (f v).toReal) (x + b • (y + lam • z)) :=
    (hf.continuousOn_toReal_relint_dom hfp).continuousAt (mem_nhds_iff.2
      ⟨interior (dom f), Convex.interior_subset_relint hf.convex_dom ⟨_, hbu⟩,
        isOpen_interior, hbu⟩)
  have hpt : Tendsto (fun i => x + (e i + b) • U i) atTop (𝓝 (x + b • (y + lam • z))) := by
    have h : Tendsto (fun i => x + (e i + b) • U i) atTop
        (𝓝 (x + ((0 : ℝ) + b) • (y + lam • z))) :=
      tendsto_const_nhds.add ((heten.add tendsto_const_nhds).smul hUten)
    simpa using h
  have hQten : Tendsto (fun i => ((f (x + (e i + b) • U i)).toReal - r) / (e i + b)) atTop
      (𝓝 (((f (x + b • (y + lam • z))).toReal - r) / b)) :=
    ((hFcont.tendsto.comp hpt).sub tendsto_const_nhds).div
      (by simpa using heten.add (tendsto_const_nhds (x := b))) hbpos.ne'
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot _)
    (mem_dom.1 (interior_subset hbu))
  have hQlt : ((f (x + b • (y + lam • z))).toReal - r) / b - c < μ * lam := by
    rw [hq, hr, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div, _root_.EReal.coe_lt_coe_iff] at hqb
    rw [hq, _root_.EReal.toReal_coe]
    linarith
  -- Everything that has to hold only for large indices.
  filter_upwards [heten.eventually_le_const (show (0 : ℝ) < α / 2 by linarith),
    (((by fun_prop : Continuous fun v : E => x + α • v).tendsto _).comp hUten).eventually_mem
      (isOpen_interior.mem_nhds hlamW),
    hYten.eventually_mem (isOpen_interior.mem_nhds hyint),
    (hQten.sub hSten).eventually_lt_const hQlt] with i hei heU heY hQS
  have hei0 : 0 < e i := hepos i
  have hxeq : x + e i • Y i = xs i := by
    rw [hYdef i, smul_smul, mul_inv_cancel₀ hei0.ne', one_smul]
    abel
  have hxeq2 : x + e i • U i = xs i + e i • (lam • z) := by
    rw [hUdef i, smul_add, ← hxeq]
    abel
  have hmem1 : x + e i • U i ∈ interior (dom f) :=
    mem_interior_dom_smul hf hx hα heU hei0 (by linarith)
  have hmem2 : x + (e i + b) • U i ∈ interior (dom f) :=
    mem_interior_dom_smul hf hx hα heU (by linarith) (by linarith)
  obtain ⟨a1, ha1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (xs i))
    (mem_dom.1 (hxsdom i))
  obtain ⟨m1, hm1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + e i • U i))
    (mem_dom.1 (interior_subset hmem1))
  obtain ⟨m2, hm2⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hfp.ne_bot (x + (e i + b) • U i))
    (mem_dom.1 (interior_subset hmem2))
  obtain ⟨s1, hs1⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hgp.ne_bot (Y i))
    (mem_dom.1 (interior_subset heY))
  have step1 : dirDeriv f x (Y i) ≤ (((a1 - r) / e i : ℝ) : EReal) := by
    have h := dirDeriv_le f x (Y i) hei0
    rwa [hxeq, ha1, hr, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div] at h
  have step2 : (lam : EReal) * dirDeriv f (xs i) z ≤ (((m1 - a1) / e i : ℝ) : EReal) := by
    have h := dirDeriv_le f (xs i) (lam • z) hei0
    rw [posHomogeneous_dirDeriv f (xs i) lam hlampos z, ← hxeq2, hm1, ha1,
      ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div] at h
    exact h
  have step3 : dirDeriv f x (Y i) + (lam : EReal) * dirDeriv f (xs i) z
      ≤ (((m1 - r) / e i : ℝ) : EReal) := by
    have h := add_le_add step1 step2
    rwa [← _root_.EReal.coe_add,
      show (a1 - r) / e i + (m1 - a1) / e i = (m1 - r) / e i from by field_simp; ring] at h
  have step4 : (((m1 - r) / e i : ℝ) : EReal) ≤ (((m2 - r) / (e i + b) : ℝ) : EReal) := by
    have h : (f (x + e i • U i) - f x) / ((e i : ℝ) : EReal)
        ≤ (f (x + (e i + b) • U i) - f x) / ((e i + b : ℝ) : EReal) :=
      monotoneOn_sub_div hf hr (U i) (mem_Ioi.2 hei0)
        (mem_Ioi.2 (by linarith : (0 : ℝ) < e i + b)) (by linarith)
    rwa [hm1, hm2, hr, ← _root_.EReal.coe_sub, ← _root_.EReal.coe_div, ← _root_.EReal.coe_sub,
      ← _root_.EReal.coe_div] at h
  rw [hm2, hs1, _root_.EReal.toReal_coe, _root_.EReal.toReal_coe] at hQS
  by_contra hcon
  push Not at hcon
  have h5 : ((lam * μ : ℝ) : EReal) ≤ (lam : EReal) * dirDeriv f (xs i) z := by
    rw [← EReal.coe_mul_coe]
    exact (EReal.coe_mul_le_coe_mul_iff hlampos).2 hcon
  have h6 : ((s1 + lam * μ : ℝ) : EReal) ≤ (((m2 - r) / (e i + b) : ℝ) : EReal) := by
    rw [_root_.EReal.coe_add]
    refine le_trans (add_le_add ?_ h5) (step3.trans step4)
    rw [hs1]
  rw [_root_.EReal.coe_le_coe_iff] at h6
  linarith [mul_comm lam μ]

end Boundary

/-! ### The face of `∂f x` exposed by a direction -/

section ExposedFace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x y : E}

/-- The subdifferential of `f'(x; ·)` at `y` is the face `∂f(x)_y` of `∂f x` exposed by `y` — the
set of subgradients at which `⟨y, ·⟩` attains its maximum over `∂f x`. This is the set appearing in
the subgradient half of the boundary statement below, and it composes the support-function
description of `f'(x; ·)` with the conjugacy characterisation of `∂`. Properness of `f'(x; ·)` is
what makes `∂f x` non-empty, so it is not a separate hypothesis. -/
theorem subgradient_dirDeriv [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hgp : Proper (dirDeriv f x))
    (hy : y ∈ ri (dom (dirDeriv f x))) :
    subgradient B (dirDeriv f x) y
      = {v ∈ subgradient B f x | ∀ w ∈ subgradient B f x, B y w ≤ B y v} := by
  have hgc : ConvexFn (dirDeriv f x) := convexFn_dirDeriv hf ht hb
  obtain ⟨v₀, hv₀⟩ := subgradient_nonempty_of_mem_relint_dom (B := B) hgc hgp hy
  have hCne : (subgradient B f x).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    obtain ⟨z, hz⟩ := (subgradient_eq_empty_iff_exists_dirDeriv_eq_bot (B := B) hf ht hb).1 hemp
    exact hgp.ne_bot z hz
  have hsupp := subgradient_supportFn (B := B.flip) (isClosed_subgradient (B := B) f x)
    (convex_subgradient B f x) hCne y
  rw [LinearMap.flip_flip] at hsupp
  rw [← subgradient_clFn (B := B) hgc hv₀, clFn_dirDeriv (B := B) hf ht hb, hsupp]
  simp only [LinearMap.flip_apply]

/-- **`∂f(x)_y` as a normal-cone condition**: the subgradients at which `y` is *normal* to
`∂f x`. This is `subgradient_dirDeriv` read through the definition of the normal cone. -/
theorem subgradient_dirDeriv_eq_sep_normalCone [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hgp : Proper (dirDeriv f x))
    (hy : y ∈ ri (dom (dirDeriv f x))) :
    subgradient B (dirDeriv f x) y
      = {v ∈ subgradient B f x | y ∈ normalCone B.flip (subgradient B f x) v} := by
  rw [subgradient_dirDeriv (B := B) hf ht hb hgp hy]
  ext v
  simp only [Set.mem_sep_iff, mem_normalCone, map_sub, LinearMap.sub_apply, LinearMap.flip_apply,
    sub_nonpos]

/-- **`∂(f'(x; ·))(y)` is an exposed face of `∂f x`**, in Mathlib's sense: it is cut out of `∂f x`
by maximising the continuous linear functional `⟨y, ·⟩`. Composing with `IsExposed.isFace` makes it
a face of `∂f x` in the convex-geometry sense. -/
theorem isExposed_subgradient_dirDeriv [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (hgp : Proper (dirDeriv f x))
    (hy : y ∈ ri (dom (dirDeriv f x))) :
    IsExposed ℝ (subgradient B f x) (subgradient B (dirDeriv f x) y) := by
  have hcont : Continuous fun v : F => B y v := by
    simpa only [LinearMap.flip_apply] using continuous_pairing B.flip y
  exact fun _ => ⟨⟨B y, hcont⟩, subgradient_dirDeriv (B := B) hf ht hb hgp hy⟩

end ExposedFace

/-! ### The subgradient half of the boundary statement -/

section BoundarySubgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x y : E}

/-- **The subgradient half**: along an approach to a point of `dom f` with a limiting
direction `y` pointing into `int (dom f)`, the subdifferentials collapse onto the face of `∂f x`
exposed by `y`,

```
∂f(x i) ⊆ ∂f(x)_y + ε B        eventually,
```

where `∂f(x)_y = {v ∈ ∂f x | ⟨y, ·⟩ is maximised over ∂f x at v}`, identified with `∂(f'(x; ·))(y)`
by `subgradient_dirDeriv`. The argument is that of the interior subgradient statement with
`f'(x; ·)` replaced by `f'(x; y; ·)`; the step usually left implicit is
`eventually_mem_interior_dom_of_tendsto_dir`, which makes the `f'(x i; ·)` finite everywhere. -/
theorem eventually_subgradient_subset_exposed_add_closedBall (hf : ConvexFn f) (hfp : Proper f)
    (hx : x ∈ dom f) {xs : ℕ → E} (hxsdom : ∀ i, xs i ∈ dom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y))
    (hy : dirDeriv f x y ≠ ⊥) {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (dom f))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subgradient (innerₗ E) f (xs i)
      ⊆ {v ∈ subgradient (innerₗ E) f x | ∀ w ∈ subgradient (innerₗ E) f x, ⟪y, w⟫ ≤ ⟪y, v⟫}
        + Metric.closedBall (0 : E) ε := by
  classical
  have hgc : ConvexFn (dirDeriv f x) := convexFn_dirDeriv hf (mem_dom.1 hx).ne (hfp.ne_bot x)
  have hyint : y ∈ interior (dom (dirDeriv f x)) := mem_interior_dom_dirDeriv hfp hx hα hαy
  have hgp : Proper (dirDeriv f x) := proper_dirDeriv_of_ne_bot hf hfp hx hyint hy
  have hyri : y ∈ ri (dom (dirDeriv f x)) :=
    Convex.interior_subset_relint hgc.convex_dom ⟨y, hyint⟩ hyint
  -- The exposed face is `∂(f'(x; ·))(y)`.
  have hflip : IsCompatiblePairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  have hface : subgradient (innerₗ E) (dirDeriv f x) y
      = {v ∈ subgradient (innerₗ E) f x | ∀ w ∈ subgradient (innerₗ E) f x, ⟪y, w⟫ ≤ ⟪y, v⟫} := by
    have h := subgradient_dirDeriv (B := innerₗ E) hf (mem_dom.1 hx).ne (hfp.ne_bot x) hgp hyri
    simpa only [innerₗ_apply_apply] using h
  rw [← hface]
  -- The approaching points are eventually interior, so `f'(x i; ·)` is finite everywhere.
  have hint : ∀ᶠ i in atTop, xs i ∈ interior (dom f) :=
    eventually_mem_interior_dom_of_tendsto_dir hf hx hxsne hxs hdir hα hαy
  set xs' : ℕ → E := fun i => if xs i ∈ interior (dom f) then xs i else x + α • y with hxs'def
  have hxs'int : ∀ i, xs' i ∈ interior (dom f) := fun i => by
    simp only [hxs'def]
    split
    · assumption
    · exact hαy
  have hxs'eq : ∀ᶠ i in atTop, xs' i = xs i :=
    hint.mono fun i hi => by simp only [hxs'def, hi, ite_true]
  -- The pointwise bound of the first assertion, in real form.
  have hle : ∀ z ∈ (univ : Set E), ∀ δ > 0, ∀ᶠ i in atTop,
      (dirDeriv f (xs' i) z).toReal ≤ (dirDeriv (dirDeriv f x) y z).toReal + δ := by
    intro z _ δ hδ
    have hlt : dirDeriv (dirDeriv f x) y z
        < (((dirDeriv (dirDeriv f x) y z).toReal + δ : ℝ) : EReal) :=
      lt_of_eq_of_lt (dirDeriv_eq_coe_toReal_of_mem_interior_dom hgc hgp hyint z)
        (_root_.EReal.coe_lt_coe_iff.2 (by linarith))
    filter_upwards [eventually_dirDeriv_lt_of_tendsto_dir hf hfp hx hxsdom hxsne hxs hdir hy
      hα hαy hlt, hxs'eq, hint] with i hi hieq hiint
    rw [hieq]
    rw [dirDeriv_eq_coe_toReal_of_mem_interior_dom hf hfp hiint z] at hi
    exact (_root_.EReal.coe_lt_coe_iff.1 hi).le
  -- Made uniform on the unit ball.
  have hunif : ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall (0 : E) 1,
      (dirDeriv f (xs' i) z).toReal ≤ (dirDeriv (dirDeriv f x) y z).toReal + ε :=
    eventually_forall_le_add_of_eventually_le isOpen_univ convex_univ
      (fun i => convexOn_toReal_dirDeriv hf hfp (hxs'int i))
      (convexOn_toReal_dirDeriv hgc hgp hyint) hle (isCompact_closedBall (0 : E) 1)
      (subset_univ _) hε
  filter_upwards [hunif, hxs'eq] with i hi hieq
  rw [← hieq]
  exact subgradient_subset_add_closedBall_of_forall_dirDeriv_le hf hfp (hxs'int i) hgc hgp
    hyint hε hi

end BoundarySubgradient

end ConvexAnalysis
