import Numlib.Analysis.ODE.Cauchy
import Numlib.Analysis.ODE.HilleYosida
import NumlibSurface.Brezis.Chapter07.Section01

/-!
# Brezis §7.2: the evolution problem `du/dt + A u = 0` on `[0, +∞)`, `u(0) = u₀`

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §7.2: the Cauchy–Lipschitz–Picard theorem on the
half-line, the Hille–Yosida theorem for a maximal monotone operator `A` on a real Hilbert space
`H` with its two lemmas, and Remarks 4–6. Functions of time are `u : ℝ → H`; the book's
`C¹([0, +∞); H)` is `ContDiffOn ℝ 1 u (Ici 0)`, and `C([0, +∞); D(A))` is the backbone's
`A.ContDiffOnPowDomain 0 1 u (Ici 0)` — `u` lifts continuously into the Hilbert space
`A.PowDomain 1`, which is `D(A)` with the Hilbert graph norm `(|v|² + |A v|²)^{1/2}` of
footnote 2 (`Numlib/Analysis/InnerProductSpace/MaximalMonotone`). The equation with its initial
condition is the backbone's `A.IsSolutionOn u₀ (Ici 0) u` (`Numlib/Analysis/ODE/HilleYosida`),
whose derivative at `t = 0` is the one-sided derivative within `[0, +∞)`.

## Main definitions and results

* `theorem_7_3` — Cauchy, Lipschitz, Picard: the Cauchy problem `du/dt = F u` on `[0, +∞)` for a
  Lipschitz `F : E → E` on a Banach space has a unique `C¹` solution
  (`Numlib/Analysis/ODE/Cauchy`, by gluing compact-interval solutions instead of the book's
  weighted-norm contraction).
* `IsSolution A u₀ u` — the solution class of problem (6):
  `u ∈ C¹([0, +∞); H) ∩ C([0, +∞); D(A))`, `du/dt + A u = 0` on `[0, +∞)`, `u(0) = u₀`.
* `theorem_7_4` — Hille–Yosida: for `u₀ ∈ D(A)` there is a unique solution, with
  `|u(t)| ≤ |u₀|` and `|du/dt (t)| = |A u(t)| ≤ |A u₀|`.
* `lemma_7_1` — for a solution `w` of `dw/dt + A_λ w = 0`, `|w(t)|` and `|dw/dt (t)| = |A_λ w(t)|`
  are nonincreasing.
* `lemma_7_2` — `D(A²)` is dense in `D(A)` for the graph norm.
* `remark_7_4_a`, `remark_7_4_b` — the approximate solutions `u_λ(t) = exp(−t A_λ) u₀` converge
  as `λ → 0`, uniformly on bounded intervals to the solution of Theorem 7.4 when `u₀ ∈ D(A)`,
  and pointwise for every `u₀ ∈ H`.
* `remark_7_5` — the contraction semigroup `S_A(t)`: its properties (a), (b), (c).
* `remark_7_6` — the problem `du/dt + A u + λ u = 0` reduces to (6) through `v(t) = e^{λt} u(t)`.

## The route

The backbone solves the approximate problem (7) in closed form, `u_λ(t) = A.expYosida λ t u₀ =
exp(−t A_λ) u₀`, and defines the semigroup `A.semigroup t = S_A(t)` as the limit of `exp(−t A_λ)`
as `λ → 0⁺` for every datum in `H` (Remark 4 (b), footnote 4); the solution of Theorem 7.4 is
`t ↦ S_A(t) u₀`. The book's Steps 1–5 are the backbone nodes named in the docstrings; Step 6 and
the use of Lemma 7.2 in the existence proof are not needed on that route, and Lemma 7.2 is stated
and proved here on its own, exactly as in the book (`ū₀ = J_λ u₀` for small `λ`). Remark 3 is
discussion; Remark 4 (b)'s counterexample sentences and the converse in Remark 5 (the Hille–Yosida
generation theorem, quoted from the literature) are not formalized.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

/-! ### Theorem 7.3: Cauchy, Lipschitz, Picard -/

section CauchyLipschitzPicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Theorem 7.3 (Cauchy, Lipschitz, Picard).** Let `E` be a Banach space and `F : E → E` a
Lipschitz map, `‖F u − F v‖ ≤ L ‖u − v‖`. Then for every initial datum `u₀ ∈ E` there is a unique
`u ∈ C¹([0, +∞); E)` with `du/dt (t) = F (u t)` on `[0, +∞)` and `u 0 = u₀` (the derivative at
`t = 0` being one-sided). -/
theorem theorem_7_3 {F : E → E} {L : ℝ} (hF : ∀ u v, ‖F u - F v‖ ≤ L * ‖u - v‖) (u₀ : E) :
    ∃ u : ℝ → E, ODE.IsSolutionOn (fun _ v => F v) 0 u₀ (Ici 0) u ∧ ContDiffOn ℝ 1 u (Ici 0) ∧
      ∀ v : ℝ → E, ODE.IsSolutionOn (fun _ v => F v) 0 u₀ (Ici 0) v →
        ContDiffOn ℝ 1 v (Ici 0) → EqOn v u (Ici 0) := by
  have hlip : LipschitzWith (Real.toNNReal L) F :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hF x y).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  have hlip' : ∀ t ∈ Ici (0 : ℝ), LipschitzWith (Real.toNNReal L) ((fun _ v => F v) t) :=
    fun _ _ => hlip
  have hcont : ContinuousOn (Function.uncurry fun _ v => F v) (Ici (0 : ℝ) ×ˢ univ) :=
    (hlip.continuous.comp continuous_snd).continuousOn
  obtain ⟨u, ⟨hu, -⟩, -⟩ := ODE.existsUnique_isSolutionOn_Ici_of_lipschitz hcont hlip' u₀
  refine ⟨u, hu, ?_, fun v hv _ => ODE.isSolutionOn_unique_of_lipschitz_Ici hlip' hv hu⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht => (hu.hasDerivWithinAt ht).differentiableWithinAt, fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  exact (hlip.continuous.comp_continuousOn hu.continuousOn).congr fun t ht =>
    (hu.hasDerivWithinAt ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

end CauchyLipschitzPicard

/-! ### Theorem 7.4: the Hille–Yosida theorem -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {A : H →ₗ.[ℝ] H}

/-- **The solution class of problem (6).** `u` is a solution of `du/dt + A u = 0` on `[0, +∞)`,
`u(0) = u₀`, in the class `C¹([0, +∞); H) ∩ C([0, +∞); D(A))`: the backbone's
`A.IsSolutionOn u₀ (Ici 0) u` (values in `D(A)`, the equation with the one-sided derivative at
`0`, the initial condition), `u ∈ C¹([0, +∞); H)`, and `u ∈ C([0, +∞); D(A))` as
`A.ContDiffOnPowDomain 0 1 u (Ici 0)` — `u` lifts continuously into `D(A)` with the Hilbert
graph norm `(|v|² + |A v|²)^{1/2}` of footnote 2, i.e. `t ↦ A u(t)` is continuous as well. -/
def IsSolution (A : H →ₗ.[ℝ] H) (u₀ : H) (u : ℝ → H) : Prop :=
  A.IsSolutionOn u₀ (Ici 0) u ∧ ContDiffOn ℝ 1 u (Ici 0) ∧ A.ContDiffOnPowDomain 0 1 u (Ici 0)

/-- The class `C^n(s; D(A^j))` only depends on the values of `u` on `s`. (Belongs beside
`LinearPMap.ContDiffOnPowDomain.mono` in the backbone.) -/
theorem contDiffOnPowDomain_congr {n : WithTop ℕ∞} {j : ℕ} {u v : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (huv : EqOn u v s) : A.ContDiffOnPowDomain n j v s :=
  let ⟨w, hw0, hw⟩ := h
  ⟨w, fun t ht => (hw0 t ht).trans (huv ht), hw⟩

/-- The element `(u₀, A u₀)` of `D(A)` with the graph norm, for `u₀ ∈ D(A)`. -/
private def toPowDomainOne (A : H →ₗ.[ℝ] H) (u₀ : A.domain) : A.PowDomain 1 :=
  LinearPMap.PowDomain.mk A ![(u₀ : H), A u₀] fun i => by
    refine ⟨?_, ?_⟩ <;> simp [Fin.fin_one_eq_zero i]

variable [CompleteSpace H]

/-- **The solution of Theorem 7.4 is the semigroup**: for `u₀ ∈ D(A)`, `t ↦ S_A(t) u₀` is a
solution of (6) in the class of `IsSolution`. The `C([0, +∞); D(A))` clause is Theorem 7.5 at
`k = j = 1`. -/
theorem isSolution_semigroup (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    IsSolution A u₀ fun t => A.semigroup t u₀ := by
  refine ⟨hA.isMaximalMonotone.isSolutionOn_semigroup u₀,
    hA.isMaximalMonotone.contDiffOn_semigroup_apply u₀, ?_⟩
  have h := hA.isMaximalMonotone.contDiffOnPowDomain_semigroup (toPowDomainOne A u₀) le_rfl
  simpa [toPowDomainOne] using h

/-- **Theorem 7.4 (Hille–Yosida).** Let `A` be maximal monotone. For every `u₀ ∈ D(A)` there is
a unique `u ∈ C¹([0, +∞); H) ∩ C([0, +∞); D(A))` with `du/dt + A u = 0` on `[0, +∞)` and
`u(0) = u₀`; moreover `|u(t)| ≤ |u₀|` and `|du/dt (t)| = |A u(t)| ≤ |A u₀|` for all `t ≥ 0`.
The solution is `t ↦ S_A(t) u₀`; the book's Steps 1–5 are the backbone nodes
`IsMonotone.norm_sub_le_of_isSolutionOn`, `antitoneOn_norm_exp_neg_smul_apply`,
`norm_expYosida_sub_expYosida_le`, `tendstoUniformlyOn_deriv_expYosida` and
`hasDerivWithinAt_semigroup_apply` of `Numlib/Analysis/ODE/HilleYosida`; Step 6 is not needed
on that route. -/
theorem theorem_7_4 (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    ∃ u : ℝ → H, ∃ hu : IsSolution A u₀ u, (∀ v, IsSolution A u₀ v → EqOn v u (Ici 0)) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖(u₀ : H)‖) ∧
      ∀ t (ht : 0 ≤ t), ‖derivWithin u (Ici 0) t‖ = ‖A ⟨u t, hu.1.mem_domain t ht⟩‖ ∧
        ‖A ⟨u t, hu.1.mem_domain t ht⟩‖ ≤ ‖A u₀‖ := by
  refine ⟨fun t => A.semigroup t u₀, isSolution_semigroup hA u₀,
    fun v hv => hv.1.eq_semigroup hA.isMaximalMonotone,
    fun _ ht => hA.isMaximalMonotone.norm_semigroup_apply_le ht u₀, fun t ht => ⟨?_, ?_⟩⟩
  · rw [((hA.isMaximalMonotone.isSolutionOn_semigroup u₀).hasDerivWithinAt t ht).derivWithin
      (uniqueDiffOn_Ici 0 t ht), norm_neg]
  · exact hA.isMaximalMonotone.norm_apply_semigroup_apply_le u₀ ht

/-- **Lemma 7.1.** Let `w ∈ C¹([0, +∞); H)` satisfy `dw/dt + A_λ w = 0` on `[0, +∞)`. Then the
functions `t ↦ |w(t)|` and `t ↦ |dw/dt (t)| = |A_λ w(t)|` are nonincreasing on `[0, +∞)`. (The
book's `C¹` hypothesis is implied by the equation, `A_λ` being bounded, and is not assumed.)
By uniqueness for the bounded monotone operator `A_λ` (Proposition 7.2 (e)),
`w(t) = exp(−t A_λ) w(0)`, and both claims are the backbone's
`antitoneOn_norm_exp_neg_smul_apply`, the second for the datum `A_λ w(0)`, since `A_λ` commutes
with `exp(−t A_λ)`. -/
theorem lemma_7_1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) {w : ℝ → H}
    (hw' : ∀ t, 0 ≤ t → HasDerivWithinAt w (-(yosidaApprox hA hl (w t))) (Ici 0) t) :
    AntitoneOn (fun t => ‖w t‖) (Ici 0) ∧
      (∀ t, 0 ≤ t → ‖derivWithin w (Ici 0) t‖ = ‖yosidaApprox hA hl (w t)‖) ∧
      AntitoneOn (fun t => ‖yosidaApprox hA hl (w t)‖) (Ici 0) := by
  simp only [yosidaApprox_eq] at hw' ⊢
  -- `A_λ` as an everywhere-defined monotone unbounded operator
  have hBm : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsMonotone := fun v => by
    change 0 ≤ RCLike.re ⟪A.yosida l (v : H), (v : H)⟫_ℝ
    simpa using hA.isMaximalMonotone.inner_yosida_nonneg hl (v : H)
  have hsol : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsSolutionOn (w 0) (Ici 0) w :=
    ⟨rfl, fun _ _ => Submodule.mem_top, fun t ht => hw' t ht⟩
  have hexp : ((A.yosida l : H →ₗ[ℝ] H).toPMap ⊤).IsSolutionOn (w 0) (Ici 0)
      fun t => A.expYosida l t (w 0) :=
    ⟨by simp [LinearPMap.expYosida_zero], fun _ _ => Submodule.mem_top, fun t _ =>
      (LinearPMap.hasDerivAt_expYosida_apply (A := A) l (w 0) t).hasDerivWithinAt⟩
  have hEq : EqOn w (fun t => A.expYosida l t (w 0)) (Ici 0) :=
    hBm.eqOn_of_isSolutionOn hsol hexp
  refine ⟨(hA.isMaximalMonotone.antitoneOn_norm_expYosida_apply hl (w 0)).congr fun t ht =>
    by simp only [hEq ht], fun t ht => ?_, ?_⟩
  · rw [(hw' t ht).derivWithin (uniqueDiffOn_Ici 0 t ht), norm_neg]
  · refine (hA.isMaximalMonotone.antitoneOn_norm_expYosida_apply hl (A.yosida l (w 0))).congr
      fun t ht => ?_
    simp only [hEq ht, LinearPMap.yosida_expYosida_comm]

/-- **Lemma 7.2.** Let `u₀ ∈ D(A)`. Then for every `ε > 0` there is `ū₀ ∈ D(A²)` — that is,
`ū₀ ∈ D(A)` with `A ū₀ ∈ D(A)` — such that `|u₀ − ū₀| < ε` and `|A u₀ − A ū₀| < ε`: `D(A²)` is
dense in `D(A)` for the graph norm. The witness is `ū₀ = J_λ u₀` for `λ > 0` small, by
Proposition 7.2 (c) applied to `u₀` and to `A u₀`, since `J_λ (A u₀) = A (J_λ u₀)`. -/
theorem lemma_7_2 (hA : IsMaximalMonotone A) (u₀ : A.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : A.domain, A v ∈ A.domain ∧ ‖(u₀ : H) - v‖ < ε ∧ ‖A u₀ - A v‖ < ε := by
  have h1 := (hA.isMaximalMonotone.tendsto_resolvent_apply (u₀ : H)).eventually
    (Metric.ball_mem_nhds _ hε)
  have h2 := (hA.isMaximalMonotone.tendsto_resolvent_apply (A u₀)).eventually
    (Metric.ball_mem_nhds _ hε)
  obtain ⟨l, ⟨hl1, hl2⟩, hl⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  have hl' : (0 : ℝ) < l := hl
  refine ⟨⟨A.resolvent l u₀, hA.isMaximalMonotone.resolvent_apply_mem_domain hl' u₀⟩, ?_, ?_, ?_⟩
  · rw [← hA.isMaximalMonotone.resolvent_apply_comm hl' u₀]
    exact hA.isMaximalMonotone.resolvent_apply_mem_domain hl' _
  · have h := Metric.mem_ball.1 hl1
    rw [dist_eq_norm] at h
    rw [norm_sub_rev]
    exact h
  · have h := Metric.mem_ball.1 hl2
    rw [dist_eq_norm] at h
    rw [← hA.isMaximalMonotone.resolvent_apply_comm hl' u₀, norm_sub_rev]
    exact h

/-! ### Remarks 4–6 -/

/-- **Remark 4 (a).** Let `u₀ ∈ D(A)` and let `u_λ` be the solution of the approximate problem
(7), `du_λ/dt + A_λ u_λ = 0`, `u_λ(0) = u₀` — here `u_λ(t) = exp(−t A_λ) u₀`, the backbone's
`A.expYosida λ t u₀`, which solves (7) on all of `ℝ`. Then as `λ → 0⁺`, `u_λ(t)` converges for
every `t ≥ 0`, uniformly on every bounded interval `[0, T]`, and the limit is the solution `u`
of Theorem 7.4 (one can prove directly that the limit lies in `C¹ ∩ C(D(A))` and satisfies (6):
this is the route the backbone takes). -/
theorem remark_7_4_a (hA : IsMaximalMonotone A) (u₀ : A.domain) :
    (∀ (l : ℝ) (hl : 0 < l), A.expYosida l 0 u₀ = u₀ ∧
      ∀ t, HasDerivAt (fun t => A.expYosida l t u₀)
        (-(yosidaApprox hA hl (A.expYosida l t u₀))) t) ∧
    ∀ u, IsSolution A u₀ u → ∀ T : ℝ,
      TendstoUniformlyOn (fun (l : ℝ) t => A.expYosida l t u₀) u (𝓝[>] 0) (Icc 0 T) := by
  refine ⟨fun l hl => ⟨by simp [LinearPMap.expYosida_zero], fun t => ?_⟩, fun u hu T => ?_⟩
  · rw [yosidaApprox_eq]
    exact LinearPMap.hasDerivAt_expYosida_apply (A := A) l u₀ t
  · exact (hA.isMaximalMonotone.tendstoUniformlyOn_expYosida_semigroup u₀).congr_right
      fun t ht => (hu.1.eq_semigroup hA.isMaximalMonotone ht.1).symm

/-- **Remark 4 (b), the convergence clause.** Assume only `u₀ ∈ H`. Still, as `λ → 0⁺`,
`u_λ(t) = exp(−t A_λ) u₀` converges for every `t ≥ 0` to some limit `u(t)` — the backbone's
`S_A(t) u₀` — a "generalized" solution of (6). (That this limit may lie outside `D(A)` for every
`t > 0` and be nowhere differentiable is a counterexample claim and is not formalized; the
self-adjoint case, where it cannot happen, is Theorem 7.7.) -/
theorem remark_7_4_b (hA : IsMaximalMonotone A) (u₀ : H) {t : ℝ} (ht : 0 ≤ t) :
    ∃ w : H, Tendsto (fun l : ℝ => A.expYosida l t u₀) (𝓝[>] 0) (𝓝 w) :=
  ⟨A.semigroup t u₀, hA.isMaximalMonotone.tendsto_expYosida_semigroup ht u₀⟩

/-- **Remark 5 (contraction semigroups).** For `t ≥ 0`, the map `u₀ ∈ D(A) ↦ u(t) ∈ D(A)`, `u`
the solution of (6) given by Theorem 7.4, extends by continuity (since `|u(t)| ≤ |u₀|` and `D(A)`
is dense) to a bounded operator `S_A(t)` on `H` — the backbone's `A.semigroup t`, defined on all of
`H` directly as in footnote 4 — which satisfies: `S_A(t) u₀ = u(t)` for `u₀ ∈ D(A)`;
(a) `‖S_A(t)‖ ≤ 1` for `t ≥ 0`; (b) `S_A(t₁ + t₂) = S_A(t₁) ∘ S_A(t₂)` for `t₁, t₂ ≥ 0` and
`S_A(0) = I`; (c) `|S_A(t) u₀ − u₀| → 0` as `t → 0⁺`, for every `u₀ ∈ H`. Such a family is a
continuous semigroup of contractions. (The converse — every continuous semigroup of contractions
is `S_A` for a unique maximal monotone `A` — is quoted from the literature and is not
formalized.) -/
theorem remark_7_5 (hA : IsMaximalMonotone A) :
    (∀ (u₀ : A.domain) (u : ℝ → H), IsSolution A u₀ u → ∀ t, 0 ≤ t → A.semigroup t u₀ = u t) ∧
      (∀ t : ℝ, 0 ≤ t → ‖A.semigroup t‖ ≤ 1) ∧
      ((∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
        A.semigroup (t₁ + t₂) = (A.semigroup t₁).comp (A.semigroup t₂)) ∧ A.semigroup 0 = 1) ∧
      ∀ u₀ : H, Tendsto (fun t => ‖A.semigroup t u₀ - u₀‖) (𝓝[>] 0) (𝓝 0) :=
  ⟨fun _ _ hu _ ht => (hu.1.eq_semigroup hA.isMaximalMonotone ht).symm,
    fun _ ht => hA.isMaximalMonotone.norm_semigroup_le_one ht,
    ⟨fun _ _ h₁ h₂ => hA.isMaximalMonotone.semigroup_add h₁ h₂,
      hA.isMaximalMonotone.semigroup_zero⟩,
    fun u₀ => tendsto_iff_norm_sub_tendsto_zero.1
      (hA.isMaximalMonotone.tendsto_semigroup_apply_zero u₀)⟩

/-- **Remark 6.** Let `A` be maximal monotone and `λ ∈ ℝ`. The problem `du/dt + A u + λ u = 0` on
`[0, +∞)`, `u(0) = u₀`, reduces to problem (6) through `v(t) = e^{λt} u(t)`: `u` solves the
perturbed problem iff `v` solves (6) with the same datum (the operator `A + λI` is
`(λ • LinearMap.id) +ᵥ A`, with domain `D(A)`, and the equivalence needs no hypothesis on `A`).
Consequently, for `u₀ ∈ D(A)` the perturbed problem has the solution `u(t) = e^{−λt} S_A(t) u₀`,
which is `C¹` on `[0, +∞)`, and every solution of the perturbed problem agrees with it on
`[0, +∞)`. -/
theorem remark_7_6 (hA : IsMaximalMonotone A) (l : ℝ) :
    (∀ (u₀ : H) (u : ℝ → H),
      ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0) u ↔
        A.IsSolutionOn u₀ (Ici 0) fun t => Real.exp (l * t) • u t) ∧
    ∀ u₀ : A.domain,
      ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0)
          (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) ∧
        ContDiffOn ℝ 1 (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) (Ici 0) ∧
        ∀ v, ((l • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ (Ici 0) v →
          EqOn v (fun t => Real.exp (-(l * t)) • A.semigroup t u₀) (Ici 0) := by
  refine ⟨fun _ _ => LinearPMap.isSolutionOn_smul_id_vadd_iff, fun u₀ => ⟨?_, ?_, fun v hv => ?_⟩⟩
  · rw [LinearPMap.isSolutionOn_smul_id_vadd_iff]
    convert hA.isMaximalMonotone.isSolutionOn_semigroup u₀ using 1
    funext t
    simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  · exact (by fun_prop : ContDiff ℝ 1 fun t : ℝ => Real.exp (-(l * t))).contDiffOn.smul
      (hA.isMaximalMonotone.contDiffOn_semigroup_apply u₀)
  · rw [LinearPMap.isSolutionOn_smul_id_vadd_iff] at hv
    intro t ht
    have h := hv.eq_semigroup hA.isMaximalMonotone ht
    simp only at h
    change v t = Real.exp (-(l * t)) • A.semigroup t u₀
    rw [← h, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

end Brezis.Chapter07

end
