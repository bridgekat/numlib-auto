/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.PiL2
import Numlib.Data.Nat.SeqAppend
import Numlib.Optimization.Complexity.SlowExample.DynamicAccuracy
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqEDA

/-!
# Slow runs of the dynamic-accuracy trust-region methods

The slow trust-region example of Theorem 12.2.6 of [cartis2022evaluation] gives slow runs of the
dynamic-accuracy trust-region methods TRqIDA and TRqEDA (Algorithms 13.1.1 and 13.3.1 of
[cartis2022evaluation]) with exact derivatives, and for TRqEDA also exact function values. The
example is lifted to $\mathbb{R}^1$ as the ridge function
$x \mapsto \lambda g(\langle e_1, x \rangle)$ along the coordinate unit vector $e_1$, with
$\lambda \in (0, 1]$. The first approximately optimal iterate of these runs is $x_{k_\varepsilon}$
with $k_\varepsilon = \lceil \varepsilon^{-(q+1)} \rceil$. The constants of the function class, the
lower bound $f_{\mathrm{low}}$ and the Lipschitz constant $L$, do not depend on $\varepsilon$.

The iterates are $x_k = k \varepsilon e_1$, with the radii $\Delta_k = \vartheta = \varepsilon$, the
ratios $\rho_k = 1$ and no accuracy-improving iteration, as long as the initial accuracies pass the
accuracy test (13.1.9) along steps of length $\varepsilon$. The tests (13.1.14) and (13.3.7) have
half the threshold of the TRq test, so TRqEDA is run on $f/2$, which makes it terminate at
$k_\varepsilon$. TRqIDA has no termination rule. After $k_\varepsilon$ its run continues as any
TRqIDA run from $x_{k_\varepsilon}$ (`Optimization.exists_trqDA_run`), joined to the explicit
iterations by `Optimization.TRqDAStep.seqAppend`.

## Main results

* `Optimization.exists_isTRqIDARun_slow`: a TRqIDA run on $\mathbb{R}^1$ whose first approximately
  optimal iterate is $x_{k_\varepsilon}$, after at least $\varepsilon^{-(q+1)} + 1$ evaluations of
  the function and of the derivatives.
* `Optimization.exists_isTRqEDARun_slow`: a TRqEDA run on $\mathbb{R}^1$ that first terminates at
  $k_\varepsilon$, after at least $2 \varepsilon^{-(q+1)}$ function evaluations and at least
  $\varepsilon^{-(q+1)} + 1$ derivative evaluations.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Optimization

open EuclideanSpace (norm_single_one inner_single_smul_self)

/-- The coordinate unit vector $e_1$ of $\mathbb{R}^1$. -/
local notation "e₀" => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

private theorem smul_e₀_succ (k : ℕ) (ε : ℝ) :
    ((k : ℝ) * ε) • e₀ + ε • e₀ = (((k : ℝ) + 1) * ε) • e₀ := by
  rw [← add_smul]; ring_nf

/-- The slow trust-region example of Theorem 12.2.6 of [cartis2022evaluation] on $\mathbb{R}^1$,
lifted along $e_1$ and scaled by $\lambda \in (0, 1]$: for $q \ge 1$ there are
$f_{\mathrm{low}}$ and $L \ge 1$ such that for all $\varepsilon, \lambda \in (0, 1]$, with
$k_\varepsilon = \lceil \varepsilon^{-(q+1)} \rceil$, $c_k = 2 - k/k_\varepsilon$ and
$x_k = k \varepsilon e_1$, some $f \ge f_{\mathrm{low}}$ with $L$-Lipschitz derivatives of
orders $0, \dots, q$ has the Taylor decrements $\Delta T_{f,j}(x_k, d) = 0$ for $j < q$ and
$\lambda \varepsilon c_k \langle e_1, d \rangle^q$ for $j = q$ ($k \le k_\varepsilon$), and the
values $f(x_{k+1}) = f(x_k) - \lambda \varepsilon^{q+1} c_k$ ($k < k_\varepsilon$). -/
private theorem exists_slowTRq_ridge {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 q (fun _ => L) ∧
        (∀ k ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊, ∀ j ≤ q, ∀ d,
          (ftaylorSeries ℝ f (((k : ℝ) * ε) • e₀)).taylorDecrement j d =
            (if j = q then lam * ε * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) else 0) * ⟪e₀, d⟫ ^ q) ∧
        ∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, f ((((k : ℝ) + 1) * ε) • e₀) =
          f (((k : ℝ) * ε) • e₀) - lam * ε ^ (q + 1) * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) := by
  obtain ⟨L, B, hL, hB, hG⟩ := exists_slowTRq_interpolant hq
  refine ⟨-B, max 1 (max L B), le_max_left _ _, fun ε hε hε1 lam hlam hlam1 => ?_⟩
  obtain ⟨G, hGc, hGL, hGB, hGd, hGf⟩ := hG ε (fun k => k * ε) hε hε1 fun k _ => by
    push_cast; ring
  set g : ℝ → ℝ := fun t => lam * G t with hg
  have hgc : ContDiff ℝ q g := contDiff_const.mul hGc
  obtain ⟨hfc, hfb, hfl⟩ := ridge_const_mul_slow_bounds (G := G) (lam := lam) (e := e₀) hGc hB
    hGL hGB hlam hlam1 (norm_single_one 0).le
  refine ⟨ridge g e₀, hfb, .of_contDiff hfc (fun j hj => hfl j (Finset.mem_Icc.1 hj).2) univ,
    fun k hk j hj d => ?_, fun k hk => ?_⟩
  · have hspike : IsSpikeJetOf q g q ⟪e₀, ((k : ℝ) * ε) • e₀⟫
        (lam * (ε * (2 - k / ⌈(ε ^ (q + 1))⁻¹⌉₊) * q !)) := by
      rw [inner_single_smul_self]
      exact IsSpikeJetOf.const_mul ⟨by rw [(hGd k hk).2]; ring,
        fun i hi1 hiq hne => (hGd k hk).1 i hi1 (lt_of_le_of_ne hiq hne)⟩ lam
    by_cases hjq : j = q
    · subst hjq
      rw [taylorDecrement_ridge_spike hgc hq le_rfl hspike, ite_eq_left rfl]
      field_simp
    · rw [ite_eq_right hjq, zero_mul]
      exact taylorDecrement_ridge_of_lt hgc (lt_of_le_of_ne hj hjq) hspike d
  · simp only [ridge_apply, inner_single_smul_self, hg]
    have := hGf k hk
    push_cast at this
    rw [this]; ring

/-- For $q \ge 1$ and $\varepsilon \in (0, 1/q!]$, with $k_\varepsilon = \lceil \varepsilon^{-(q+1)}
\rceil$ and $c_k = 2 - k/k_\varepsilon$: $\varepsilon \le 1$, $k_\varepsilon \ge \max\{1,
\varepsilon^{-(q+1)}\}$, $c_k > 1$ for $k < k_\varepsilon$, $c_k \ge 0$ for
$k \le k_\varepsilon$, $c_{k_\varepsilon} = 1$, the tolerances $\varepsilon_j = j! \varepsilon$
lie in $(0, 1]$ for $j \in [1, q]$, and $\min_j \varepsilon_j = \varepsilon$. -/
private theorem slowTRq_setup {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) (hεq : ε ≤ 1 / q !) :
    ε ≤ 1 ∧ 1 ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧ (ε ^ (q + 1))⁻¹ ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
      (∀ k < ⌈(ε ^ (q + 1))⁻¹⌉₊, 1 < 2 - (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊) ∧
      (∀ k ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊, 0 ≤ 2 - (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊) ∧
      2 - (⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ = 1 ∧
      (∀ j ∈ Finset.Icc 1 q, (j ! : ℝ) * ε ∈ Set.Ioc 0 1) ∧
      epsMin q (fun j : ℕ => (j ! : ℝ) * ε) = ε := by
  have hqf : (0 : ℝ) < q ! := by positivity
  have hκ1 : 1 ≤ ⌈(ε ^ (q + 1))⁻¹⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hκpos : (0 : ℝ) < ⌈(ε ^ (q + 1))⁻¹⌉₊ := by exact_mod_cast hκ1
  refine ⟨hεq.trans (by
      rw [div_le_one hqf]; exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)),
    hκ1, Nat.le_ceil _, fun k hk => ?_, fun k hk => ?_, by rw [div_self hκpos.ne']; ring,
    fun j hj => ⟨by positivity, ?_⟩, ?_⟩
  · have : (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ < 1 := (div_lt_one hκpos).2 (by exact_mod_cast hk)
    linarith
  · have : (k : ℝ) / ⌈(ε ^ (q + 1))⁻¹⌉₊ ≤ 1 := (div_le_one hκpos).2 (by exact_mod_cast hk)
    linarith
  · have hjq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le (Finset.mem_Icc.1 hj).2
    calc (j ! : ℝ) * ε ≤ q ! * (1 / q !) := mul_le_mul hjq hεq hε.le hqf.le
      _ = 1 := by field_simp
  · have h1 := epsMin_le (ε := fun j : ℕ => (j ! : ℝ) * ε) (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)
    refine le_antisymm (by simpa using h1) ((le_epsMin_iff hq).2 fun j _ => ?_)
    have h2 : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    exact le_mul_of_one_le_left hε.le h2

/-- **A slow TRqIDA run** on $X = \mathbb{R}^1$ with exact derivatives. Let $q \ge 1$. There are
$f_{\mathrm{low}} \in \mathbb{R}$ and $L \ge 1$ with the following property. Let
$0 < \varepsilon \le 1/q!$, and let $P$ be TRqIDA parameters with the order $q$, the radii
$\Delta_0 = \vartheta = \varepsilon$, and initial accuracies
$h_{0,i} \le \kappa_s \varepsilon^{q-i+1}$ for $i \in [1, q]$; these pass the accuracy test
(13.1.9) along steps of length $\varepsilon$. Then there are a function
$f \colon \mathbb{R}^1 \to \mathbb{R}$ of class $C^q$ with $f \ge f_{\mathrm{low}}$ whose
derivatives of orders $0, \dots, q$ are $L$-Lipschitz on $\mathbb{R}^1$, and a TRqIDA run for
$f$ with the tolerances $\varepsilon_j = j! \varepsilon$, the oracle constants
$\kappa_{\nabla,i} = 0$ and the starting point $x_0 = 0$, such that:

* the data are exact: $D_k$ is the jet of $f$ at $x_k$ for every $k$;
* the first iterate $x_k$ that is an $(\varepsilon, \delta_k)$-approximate $q$-th order
  minimizer is $x_{k_\varepsilon}$, with $k_\varepsilon = \lceil \varepsilon^{-(q+1)} \rceil$;
* up to iteration $k_\varepsilon$, the number of function evaluations (one at $x_0$ and one per
  iteration that is not accuracy-improving) is at least $\varepsilon^{-(q+1)} + 1$;
* up to iteration $k_\varepsilon$, the number of derivative evaluations (one at $x_0$ and one
  per accuracy-improving or successful iteration) is at least $\varepsilon^{-(q+1)} + 1$.

The oracle constants $\kappa_{\nabla,i} = 0$ make the accuracy requirement (13.1.2) ask for zero
error. The smoothness and the Lipschitz condition are `LipschitzDerivsAnchored f univ univ 0 q
(fun _ => L)`, the run is `Optimization.IsTRqIDARun`, the test of approximate optimality is
`Optimization.trqIDATest`, and the counts are `Optimization.derivEvalCount`. Up to
$k_\varepsilon$ the run follows the slow example of Theorem 12.2.6 of [cartis2022evaluation]:
$x_k = k \varepsilon e_1$, $\Delta_k = \varepsilon$, $\rho_k = 1$, and no iteration is
accuracy-improving, so both counts are $k_\varepsilon + 1$. After $k_\varepsilon$ it continues
as any run from $x_{k_\varepsilon}$ (`Optimization.exists_trqDA_run`). -/
theorem exists_isTRqIDARun_slow {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop),
          IsTRqIDARun f univ (fun _ => 0) P (fun j => j ! * ε) 0 x Δ h D dd jk s
            acc ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
          IsFirstHit (trqIDATest f univ P (fun j => j ! * ε) x Δ) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => ¬ acc i) ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount
            (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowTRq_ridge hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hh₀ => ?_⟩
  subst hPq
  obtain ⟨hε1, hκ1, hκge, hc1, hc0, hcκ, hεv, hεmin⟩ := slowTRq_setup P.one_le_q hε hεq
  obtain ⟨f, hb, hf, hdec, hfdec⟩ := H ε hε hε1 1 one_pos le_rfl
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈(ε ^ (P.q + 1))⁻¹⌉₊ with hκ
  clear_value κ
  have hϑε : epsMin P.q (fun j : ℕ => (j ! : ℝ) * ε) ≤ P.ϑ := by rw [hεmin, hϑ]
  set xp : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => ((k : ℝ) * ε) • e₀ with hxp
  have hxp1 : ∀ k : ℕ, xp k + ε • e₀ = (((k : ℝ) + 1) * ε) • e₀ := fun k => smul_e₀_succ k ε
  obtain ⟨x', Δ', h', dd', jk', s', acc', hx'0, hΔ'0, hh'0, hr⟩ :=
    exists_trqDA_run f P (fun j => j ! * ε) (fun y _ => ftaylorSeries ℝ f y) (xp κ)
  have hw : ∀ k j, ∃ e, IsApproxMeasureStep ((ftaylorSeries ℝ f (xp k)).taylorDecrement j) ε univ
      P.ς e ∧ (ftaylorSeries ℝ f (xp k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ f (xp k)) j ε univ :=
    fun k j => exists_isApproxMeasureStep_eq_mul_taylorMeasure _ j hε.le ⟨P.ς_pos.le, P.ς_le_one⟩
  choose ddp hddp using hw
  have hdecp : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ d,
      (ftaylorSeries ℝ f (xp k)).taylorDecrement j d =
        (if j = P.q then 1 * ε * (2 - k / κ) else 0) * ⟪e₀, d⟫ ^ P.q := fun k hk j hj d =>
    hdec k hk j (Finset.mem_Icc.1 hj).2 d
  have hρp : ∀ k < κ, trqRatio f (fun i => ftaylorSeries ℝ f (xp i)) xp (fun _ => ε • e₀)
      (fun _ => P.q) k = 1 := fun k hk =>
    slowTRq_trqRatio_eq_one hε one_pos (zero_lt_one.trans (hc1 k hk)) rfl rfl
      (by rw [hdecp k hk.le P.q (Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩), inner_single_smul_self,
        ite_eq_left rfl])
      (by rw [hxp1, hfdec k hk])
  have hpre : ∀ k < κ, TRqDAStep univ P (fun j => j ! * ε) xp (fun _ => ε) (fun _ => P.h₀)
      (fun i => ftaylorSeries ℝ f (xp i)) ddp (fun _ => P.q) (fun _ => ε • e₀) (fun _ => False)
      (trqRatio f (fun i => ftaylorSeries ℝ f (xp i)) xp (fun _ => ε • e₀) (fun _ => P.q)) k :=
    fun k hk => slowTRq_trqDAStep (lam := 1) (c := 2 - k / κ) (norm_single_one 0) hε hϑ
      (hΔ₀ ▸ P.Δ₀_le_Δmax) (by linarith [hc1 k hk]) (by nlinarith [hc1 k hk]) (hdecp k hk.le)
      (fun j _ => hddp k j) rfl rfl rfl hh₀ rfl rfl not_false
      (by rw [hxp1]; simp only [hxp, Nat.cast_add, Nat.cast_one]) (hρp k hk)
  -- the run: the slow example up to `κ`, then the run from `x_κ`
  set X := Nat.seqAppend κ xp x' with hX
  set Δv := Nat.seqAppend κ (fun _ => ε) Δ' with hΔv
  set hv := Nat.seqAppend κ (fun _ => P.h₀) h' with hhv
  set ddv := Nat.seqAppend κ ddp dd' with hddv
  set jkv := Nat.seqAppend κ (fun _ => P.q) jk' with hjkv
  set sv := Nat.seqAppend κ (fun _ => ε • e₀) s' with hsv
  set accv := Nat.seqAppend κ (fun _ => False) acc' with haccv
  set Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ :=
    fun i => ftaylorSeries ℝ f (X i) with hDvdef
  have hDv : ∀ k, Dv k = ftaylorSeries ℝ f (X k) := fun _ => rfl
  have hstep : ∀ k, TRqDAStep univ P (fun j => j ! * ε) X Δv hv Dv ddv jkv sv accv
      (trqRatio f Dv X sv jkv) k :=
    TRqDAStep.seqAppend hpre hr hx'0 (hΔ'0.trans hΔ₀) hh'0
  have hXle : ∀ k ≤ κ, X k = xp k := fun k hk => Nat.seqAppend_eq_of_le hx'0 hk
  have hΔle : ∀ k ≤ κ, Δv k = ε := fun k hk => Nat.seqAppend_eq_of_le (hΔ'0.trans hΔ₀) hk
  have hhle : ∀ k ≤ κ, hv k = P.h₀ := fun k hk => Nat.seqAppend_eq_of_le hh'0 hk
  have hmeas : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, taylorMeasure (Dv k) j ε univ =
      (if j = P.q then 1 * ε * (2 - k / κ) else 0) * ε ^ P.q := fun k hk j hj => by
    refine taylorMeasure_eq_mul_pow_of_inner_pow (norm_single_one 0) ?_ hε.le ?_
    · split_ifs
      · have := hc0 k hk
        positivity
      · exact le_rfl
    · rw [hDv, hXle k hk]; exact hdecp k hk j hj
  have hρ1 : ∀ k < κ, trqRatio f Dv X sv jkv k = 1 := fun k hk => by
    rw [← hρp k hk]
    simp only [trqRatio_eq, hDv, hXle k hk.le, hsv, hjkv, Nat.seqAppend_of_lt hk]
  have hrun : IsTRqIDARun f univ (fun _ => 0) P (fun j => j ! * ε) 0 X Δv hv Dv
      ddv jkv sv accv :=
    ⟨hεv, hϑε, fun _ _ => le_rfl, by rw [hXle 0 (Nat.zero_le _)]; simp [hxp], mem_univ _,
      by rw [hΔle 0 (Nat.zero_le _), hΔ₀], hhle 0 (Nat.zero_le _),
      fun k => by rw [hDv]; exact (jetApprox_self _ _).mono_err fun i _ => by simp, hstep⟩
  have hnacc : ∀ i < κ, ¬ accv i := fun i hi => by
    rw [haccv, Nat.seqAppend_of_lt hi]; exact not_false
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have htest : ∀ k ≤ κ, (trqIDATest f univ P (fun j => j ! * ε) X Δv k ↔ k = κ) := by
    intro k hk
    have hrad : trqDARadius P Δv k = ε := by simp only [trqDARadius, hΔle k hk, hϑ, min_self]
    rw [trqIDATest, hrad, Set.setOf_add_mem_univ, isEpsDeltaApprox_iff, ← hDv k]
    constructor
    · intro ht
      by_contra hne
      have h1 := ht P.q hqm
      rw [hmeas k hk _ hqm, ite_eq_left rfl] at h1
      have h2 := hc1 k (lt_of_le_of_ne hk hne)
      have e : (P.q ! : ℝ) * ε * ε ^ P.q / P.q ! = ε * ε ^ P.q := by field_simp
      rw [e] at h1
      have : 0 < ε * ε ^ P.q := by positivity
      nlinarith
    · rintro rfl j hj
      rw [hmeas _ le_rfl j hj]
      by_cases hjq : j = P.q
      · subst hjq
        rw [ite_eq_left rfl, hcκ]
        apply le_of_eq
        field_simp
      · rw [ite_eq_right hjq, zero_mul]
        positivity
  refine ⟨X, Δv, hv, Dv, ddv, jkv, sv, accv, hrun, hDv,
    ⟨(htest κ le_rfl).2 rfl, fun i hi => fun ht => hi.ne ((htest i hi.le).1 ht)⟩, ?_, ?_⟩
  · rw [derivEvalCount_of_forall hnacc]; push_cast; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨hnacc i hi, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast; linarith

/-- **A slow TRqEDA run** on $X = \mathbb{R}^1$ with exact function values and exact derivatives.
Let $q \ge 1$. There are $f_{\mathrm{low}} \in \mathbb{R}$ and $L \ge 1$ with the following
property. Let $0 < \varepsilon \le 1/q!$, and let $P$ be TRqIDA parameters with the order $q$,
the radii $\Delta_0 = \vartheta = \varepsilon$, the condition (13.3.5)
$\kappa_s \le \min\{\eta_1, 1 - \eta_2\}/4$, and initial accuracies that pass the accuracy test
(13.1.9) along steps of length $\varepsilon$ and the termination test (13.3.8) at the radius
$\varepsilon$:
$$h_{0,i} \le \kappa_s \varepsilon^{q-i+1} \quad (i \in [1, q]), \qquad \sum_{i=1}^q
  \frac{h_{0,i} \varepsilon^i}{i!} \le \frac{1}{2} \varsigma \varepsilon
  \frac{\varepsilon^q}{q!}.$$
Then there are a function $f \colon \mathbb{R}^1 \to \mathbb{R}$ of class $C^q$ with
$f \ge f_{\mathrm{low}}$ whose derivatives of orders $0, \dots, q$ are $L$-Lipschitz on
$\mathbb{R}^1$, and a TRqEDA run for $f$ with the tolerances $\varepsilon_j = j! \varepsilon$
and the starting point $x_0 = 0$, such that:

* the data are exact: $D_k$ is the jet of $f$ at $x_k$, and the computed values are $f(x_k)$ and
  $f(x_k + s_k)$, for every $k$;
* the run first terminates at $k_\varepsilon = \lceil \varepsilon^{-(q+1)} \rceil$;
* up to iteration $k_\varepsilon$, the number of function evaluations is at least
  $2 \varepsilon^{-(q+1)}$;
* up to iteration $k_\varepsilon$, the number of derivative evaluations (one at $x_0$ and one
  per accuracy-improving or successful iteration) is at least $\varepsilon^{-(q+1)} + 1$.

The smoothness and the Lipschitz condition are `LipschitzDerivsAnchored f univ univ 0 q (fun
_ => L)`, the run is `Optimization.IsTRqEDARun`, the termination test is
`Optimization.edaStopTR`, and the counts are `Optimization.edaFunEvalCount` and
`Optimization.derivEvalCount`. The run is the slow example of Theorem 12.2.6 of
[cartis2022evaluation] with $f$ halved: $x_k = k \varepsilon e_1$, $\Delta_k = \varepsilon$,
$\rho_k = 1$, and no iteration is accuracy-improving. Each function value is computed again, so
the function evaluations number $2 k_\varepsilon$, and the derivative evaluations number
$k_\varepsilon + 1$. The halving makes the test (13.3.7), whose threshold is half that of TRq,
pass exactly at $k_\varepsilon$. -/
theorem exists_isTRqEDARun_slow {q : ℕ} (hq : 1 ≤ q) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / q ! → ∀ P : TRqIDAParams, P.q = q →
      P.Δ₀ = ε → P.ϑ = ε → P.κs ≤ min P.η₁ (1 - P.η₂) / 4 →
      (∀ i ∈ Finset.Icc 1 q, P.h₀ i ≤ P.κs * ε ^ (q - i + 1)) →
      ∑ i ∈ Finset.Icc 1 q, P.h₀ i * ε ^ i / i ! ≤ P.ς * ε * ε ^ q / q ! / 2 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, (∀ y, flow ≤ f y) ∧
        LipschitzDerivsAnchored f univ univ 0 q (fun _ => L) ∧
        ∃ (x : ℕ → EuclideanSpace ℝ (Fin 1)) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
          (D : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (dd : ℕ → ℕ → EuclideanSpace ℝ (Fin 1)) (jk : ℕ → ℕ)
          (s : ℕ → EuclideanSpace ℝ (Fin 1)) (acc : ℕ → Prop) (fx fxs h₀ : ℕ → ℝ)
          (R : ℕ → Prop),
          IsTRqEDARun f univ P (fun j => j ! * ε) 0 x Δ h D dd jk s acc fx fxs h₀
            R ∧
          (∀ k, D k = ftaylorSeries ℝ f (x k) ∧ fx k = f (x k) ∧ fxs k = f (x k + s k)) ∧
          IsFirstHit (edaStopTR P (fun j => j ! * ε) D Δ h dd) ⌈(ε ^ (q + 1))⁻¹⌉₊ ∧
          2 * (ε ^ (q + 1))⁻¹ ≤ (edaFunEvalCount acc R ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) ∧
          (ε ^ (q + 1))⁻¹ + 1 ≤ (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧
            P.η₁ ≤ edaRatio fx fxs (fun i => (D i).taylorDecrement (jk i) (s i)) i))
              ⌈(ε ^ (q + 1))⁻¹⌉₊ : ℝ) := by
  obtain ⟨flow, L, hL, H⟩ := exists_slowTRq_ridge hq
  refine ⟨flow, L, hL, fun ε hε hεq P hPq hΔ₀ hϑ hκs hh₀ hsum => ?_⟩
  subst hPq
  obtain ⟨hε1, hκ1, hκge, hc1, hc0', hcκ, hεv, hεmin⟩ := slowTRq_setup P.one_le_q hε hεq
  obtain ⟨f, hb, hf, hdec, hfdec⟩ := H ε hε hε1 (1 / 2) (by norm_num) (by norm_num)
  refine ⟨f, hb, hf, ?_⟩
  set κ := ⌈(ε ^ (P.q + 1))⁻¹⌉₊ with hκ
  clear_value κ
  have hc0 : ∀ k ≤ κ, 0 ≤ 1 / 2 * ε * (2 - (k : ℝ) / κ) := fun k hk => by
    have := hc0' k hk
    positivity
  set xp : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => ((k : ℝ) * ε) • e₀ with hxp
  have hxp1 : ∀ k : ℕ, xp k + ε • e₀ = (((k : ℝ) + 1) * ε) • e₀ := fun k => smul_e₀_succ k ε
  have hw : ∀ k j, ∃ e, IsApproxMeasureStep ((ftaylorSeries ℝ f (xp k)).taylorDecrement j) ε univ
      P.ς e ∧ (ftaylorSeries ℝ f (xp k)).taylorDecrement j e =
        P.ς * taylorMeasure (ftaylorSeries ℝ f (xp k)) j ε univ :=
    fun k j => exists_isApproxMeasureStep_eq_mul_taylorMeasure _ j hε.le ⟨P.ς_pos.le, P.ς_le_one⟩
  choose ddp hddp using hw
  obtain ⟨Dv, hDv⟩ : ∃ Dv : ℕ → FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin 1)) ℝ,
      ∀ k, Dv k = ftaylorSeries ℝ f (xp k) := ⟨_, fun _ => rfl⟩
  have hqm : P.q ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨P.one_le_q, le_rfl⟩
  have hdecX : ∀ k ≤ κ, ∀ j ∈ Finset.Icc 1 P.q, ∀ d, (Dv k).taylorDecrement j d =
      (if j = P.q then 1 / 2 * ε * (2 - k / κ) else 0) * ⟪e₀, d⟫ ^ P.q := fun k hk j hj d => by
    rw [hDv]; exact hdec k hk j (Finset.mem_Icc.1 hj).2 d
  have hddX : ∀ k, ∀ j ∈ Finset.Icc 1 P.q,
      IsApproxMeasureStep ((Dv k).taylorDecrement j) ε univ P.ς (ddp k j) ∧
        (Dv k).taylorDecrement j (ddp k j) = P.ς * taylorMeasure (Dv k) j ε univ :=
    fun k j _ => by rw [hDv]; exact hddp k j
  set sv : ℕ → EuclideanSpace ℝ (Fin 1) := fun _ => ε • e₀ with hsv
  set jkv : ℕ → ℕ := fun _ => P.q with hjkv
  set fx : ℕ → ℝ := fun k => f (xp k) with hfx
  set fxs : ℕ → ℝ := fun k => f (xp k + sv k) with hfxs
  have hdecs : ∀ k ≤ κ, (Dv k).taylorDecrement (jkv k) (sv k) =
      1 / 2 * ε * (2 - k / κ) * ε ^ P.q := fun k hk => by
    rw [hdecX k hk _ hqm, inner_single_smul_self, ite_eq_left rfl]
  have hρ1 : ∀ k < κ, edaRatio fx fxs (fun i => (Dv i).taylorDecrement (jkv i) (sv i)) k = 1 :=
    fun k hk => slowTRq_trqRatio_eq_one (D := Dv) (x := xp) (f := f) (lam := 1 / 2)
        (c := 2 - k / κ) hε
      (by norm_num)
      (zero_lt_one.trans (hc1 k hk)) rfl rfl (by rw [hdecX k hk.le _ hqm, inner_single_smul_self,
        ite_eq_left rfl]) (by rw [hxp1, hfdec k hk])
  have hstop : ∀ k ≤ κ, (edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε) (fun _ => P.h₀) ddp k ↔
      k = κ) := by
    intro k hk
    constructor
    · rintro ⟨hp, -⟩
      by_contra hne
      exact hp _ hqm (slowTRq_trqDAFail (lam := 1 / 2) (c := 2 - k / κ) (norm_single_one 0) hε hϑ
        (by linarith [hc1 k (lt_of_le_of_ne hk hne)]) (hdecX k hk) (hddX k) rfl)
    · rintro rfl
      refine ⟨fun j hj hfj => ?_, ?_⟩
      · rw [trqDAFail, trqDARadius, hϑ, min_self, slowTRq_taylorDecrement_eq (norm_single_one 0) hε
          (hc0 _ le_rfl) (hdecX _ le_rfl)
          (hddX _) hj] at hfj
        by_cases hjq : j = P.q
        · subst hjq
          rw [ite_eq_left rfl, hcκ] at hfj
          have e : P.ς * (P.q ! * ε) * ε ^ P.q / P.q ! / 2 =
              P.ς * (1 / 2 * ε * 1 * ε ^ P.q) := by field_simp
          rw [e] at hfj
          exact lt_irrefl _ hfj
        · rw [ite_eq_right hjq, zero_mul, mul_zero] at hfj
          have : 0 ≤ P.ς * (j ! * ε) * ε ^ j / j ! / 2 := by
            have := P.ς_pos; positivity
          linarith
      · simp only [trqDARadius, hϑ, min_self, hεmin]
        exact hsum
  have hnstop : ∀ k < κ, ¬ edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε) (fun _ => P.h₀) ddp k :=
    fun k hk hs => hk.ne ((hstop k hk.le).1 hs)
  have hreach : ∀ k, (∀ j ≤ k, ¬ edaStopTR P (fun j => j ! * ε) Dv (fun _ => ε)
      (fun _ => P.h₀) ddp j) → k < κ := fun k hk => by
    by_contra hge
    exact hk κ (not_lt.1 hge) ((hstop κ le_rfl).2 rfl)
  have hrun : IsTRqEDARun f univ P (fun j => j ! * ε) 0 xp (fun _ => ε)
      (fun _ => P.h₀) Dv ddp jkv sv (fun _ => False) fx fxs
      (fun k => P.κs * (Dv k).taylorDecrement (jkv k) (sv k)) (fun _ => True) := by
    refine ⟨hκs, hεv, hεmin.trans hϑ.symm |>.le, by simp [hxp], mem_univ _, hΔ₀.symm, rfl,
      fun k _ => ?_, fun k _ j hj => ?_, fun k hk => ?_⟩
    · rw [hDv]
      exact (jetApprox_self _ _).mono_err fun i hi => (P.h₀_pos i hi).le
    · rw [trqDARadius, hϑ, min_self, Set.setOf_add_mem_univ]
      exact (hddX k j hj).1
    · have hkκ := hreach k hk
      have hpos : 0 < P.κs * (Dv k).taylorDecrement (jkv k) (sv k) := by
        rw [hdecs k hkκ.le]
        have := P.κs_pos
        have := hc1 k hkκ
        have : 0 < 2 - (k : ℝ) / κ := by linarith
        positivity
      refine ⟨slowTRq_trqDAStep (lam := 1 / 2) (c := 2 - k / κ) (norm_single_one 0) hε hϑ
        (hΔ₀ ▸ P.Δ₀_le_Δmax) (by linarith [hc1 k hkκ]) (hc0 k hkκ.le) (hdecX k hkκ.le) (hddX k)
        rfl rfl rfl hh₀ rfl rfl not_false
        (by rw [hxp1]; simp only [hxp, Nat.cast_add, Nat.cast_one]) (hρ1 k hkκ),
        fun _ => ⟨hpos, le_rfl, by simp [hfxs, hpos.le], by simp [hfx, hpos.le],
          fun h => absurd trivial h⟩⟩
  refine ⟨xp, fun _ => ε, fun _ => P.h₀, Dv, ddp, jkv, sv, fun _ => False, fx, fxs,
    fun k => P.κs * (Dv k).taylorDecrement (jkv k) (sv k), fun _ => True, hrun,
    fun k => ⟨hDv k, rfl, rfl⟩, ⟨(hstop κ le_rfl).2 rfl, hnstop⟩, ?_, ?_⟩
  · rw [edaFunEvalCount, card_filter_range_of_forall fun _ _ => not_false,
      card_filter_range_of_forall fun _ _ => ⟨not_false, trivial⟩]
    push_cast; linarith
  · rw [derivEvalCount_of_forall fun i hi => Or.inr ⟨not_false, by
      rw [hρ1 i hi]; exact P.η₁_le_η₂.trans P.η₂_lt_one.le⟩]
    push_cast; linarith


end Optimization
