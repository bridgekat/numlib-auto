import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Antilipschitz
import Numlib.Conditioning.Problem

/-!
# Consistency, stability and convergence of a numerical method

The vocabulary of [quarteroni2000numerical] §2.2–2.3, on top of `Numlib/Conditioning/Problem`.
The problem is `F x d = 0` on the admissible data `S` with resolvent `G`; a *numerical method*
for it is a family `Fn : ℕ → X → D → Y` of approximate problems with resolvents `Gn : ℕ → D → X`,
indexed by the discretization parameter `n` (a method indexed by a mesh size `h → 0` is written
with `n ↦ h n`). Everything is a `Prop`-valued predicate or an `ℝ≥0∞`-valued quantity on these
plain functions.

* *Consistency* (`Conditioning.IsConsistent`, the book's (2.13)) and *strong consistency*
  (`IsStronglyConsistent`, with the multistep form `IsStronglyConsistentMultistep` of (2.14)) are
  stated for the solution relation `F x d = 0`, not the resolvent, so that they make sense without
  uniqueness: Newton's method approximates *a* root.
* *Stability* (`Conditioning.IsStable`) is equicontinuity of the tail of the numerical resolvents
  at the datum. The book's Lipschitz form (2.16)–(2.17) with a constant uniform in `n` is
  `IsLipschitzStable`, which is finiteness of the *asymptotic condition number*
  `K^num_abs = limsup_n K_{abs,n}` (`asymptoticAbsCondNumber`, `asymptoticRelCondNumber`). The
  per-`n` condition numbers `K_n`, `K_{abs,n}` of (2.17) and their first-order formulas (2.19) are
  `Conditioning.relCondNumberWithin (Gn n)` and `Conditioning.relCondNumber_eq_enorm_fderiv` applied
  to `Gn n`; there is no new definition.
* *Convergence* (`Conditioning.IsConvergent`) is Definition 2.2 of the book verbatim.

The relations of the book's §2.2.1 are stated with honest hypotheses. Convergence implies the
equicontinuity stability, not a Lipschitz one (`Gn n d = √|d| / n` at `d = 0` is convergent and
consistent for the problem `G d = 0`, yet no `Gn n` is Lipschitz at `0`): `IsConvergent.isStable`.
Stability plus pointwise convergence gives convergence (`isConvergent_of_isStable`), and
consistency gives pointwise convergence when the approximate problems admit a uniform inverse
bound `‖x - y‖ ≤ M ‖Fn n x d - Fn n y d‖` (`AntilipschitzWith`, in `tendsto_of_isConsistent`) —
the rigorous content of the book's "`∂Fn/∂x` invertible" mean-value argument (2.25), which fails as
an equality in a normed space. Together they are the abstract equivalence theorem
`isStable_iff_isConvergent`. The evolution-scheme Lax–Richtmyer theorem is
`FiniteDifference.isStable_iff_isConvergent` in `Numlib/FiniteDifference/LaxEquivalence`; its
stability is a bound on the powers of an operator, and neither theorem is an instance of the other.

The *backward error* of §2.3 (`Conditioning.backwardError`) is the infimum size of a perturbation
of the datum for which a computed `x̂` is an exact solution, and the module ends with "forward error
≤ condition number × backward error" (`enorm_sub_le_absCondNumberWithin_mul_backwardError`). The
normwise, weighted backward error of a linear system (Rigal–Gaches) is the root-namespace
`backwardError` of `Numlib/Conditioning/LinearSystem`; the two are different quantities.

That last bound carries the hypothesis that the resolvent is continuous at the datum within the
admissible data — the well-posedness the book assumes of the problem in §2.1 — and the hypothesis
is not a convenience. Without it the inequality is **false**, because `ℝ≥0∞` has `⊤ * 0 = 0` and
the multiplication does not commute with the infimum defining the backward error. Take
`D = X = Y = ℝ`, `S = univ`, `G 0 = 0` and `G y = 1` for `y ≠ 0`, `F x y = x - G y` (so that
`IsResolvent F univ G` holds), `d = 0` and `x̂ = 1`. Every `δd ≠ 0` satisfies `F x̂ (d + δd) = 0`,
so `backwardError F univ 0 1 = 0`, an infimum that is not attained; and
`absCondNumberWithin G univ 0 η = ⊤`, since `‖G δd - G 0‖ₑ / ‖δd‖ₑ = 1/|δd|` is unbounded on the
perturbations. The right-hand side is `⊤ * 0 = 0` while the left-hand side is `‖x̂ - G 0‖ₑ = 1`.
The pointwise bound for a single perturbation, `enorm_sub_le_absCondNumberWithin_mul_enorm`, needs
no hypothesis; only the passage to the infimum does, and continuity is exactly what makes a zero
backward error force `x̂ = G d` (`IsResolvent.eq_of_backwardError_eq_zero`).

The datum `d` is fixed here and does not vary with `n` (the book's `d_n`); a data approximation is
composed into `Gn n` when needed.
-/

open Filter Topology Set
open scoped ENNReal NNReal

namespace Conditioning

variable {D X Y : Type*}

/-! ### Consistency -/

section Consistency

variable [Zero Y]

/-- **Consistency** ([quarteroni2000numerical] (2.13)): every exact solution `x` of `F x d = 0`
makes the residual `Fn n x d` of the approximate problems tend to zero. Stated for the solution
relation, not the resolvent, so that no uniqueness is needed. -/
def IsConsistent [TopologicalSpace Y] (F : X → D → Y) (Fn : ℕ → X → D → Y) (S : Set D) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 → Tendsto (fun n => Fn n x d) atTop (𝓝 0)

/-- **Strong consistency** ([quarteroni2000numerical] §2.2): every exact solution solves every
approximate problem, `Fn n x d = 0` for all `n`, not only in the limit. -/
def IsStronglyConsistent (F : X → D → Y) (Fn : ℕ → X → D → Y) (S : Set D) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 → ∀ n, Fn n x d = 0

/-- **Strong consistency of a multistep scheme** ([quarteroni2000numerical] (2.14)), whose `n`-th
problem `Fn n (x_n, …, x_{n-q}) d = 0` involves `q + 1` consecutive iterates: the constant
sequence at an exact solution solves it. -/
def IsStronglyConsistentMultistep {q : ℕ} (F : X → D → Y)
    (Fn : ℕ → (Fin (q + 1) → X) → D → Y) (S : Set D) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 → ∀ n, Fn n (fun _ => x) d = 0

/-- Strong consistency implies consistency. -/
theorem IsStronglyConsistent.isConsistent [TopologicalSpace Y] {F : X → D → Y}
    {Fn : ℕ → X → D → Y} {S : Set D} (h : IsStronglyConsistent F Fn S) : IsConsistent F Fn S :=
  fun d hd x hx => by simp only [h d hd x hx]; exact tendsto_const_nhds

end Consistency

/-! ### Stability and convergence of the numerical resolvents -/

variable [NormedAddCommGroup D] [NormedAddCommGroup X]

/-- **Stability** of a numerical method at the datum `d`: for `n` large, the numerical solutions
depend continuously on the datum *uniformly* in `n` (equicontinuity of the tail of `Gn` at `d`
within the admissible data). This is the notion for which "convergent ⟹ stable"
([quarteroni2000numerical] §2.2.1, (2.24)) is true; the book's Lipschitz form (2.16) is
`IsLipschitzStable`. -/
def IsStable (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n ≥ n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
    ‖Gn n (d + δd) - Gn n d‖ ≤ ε

/-- **Lipschitz stability**, the book's (2.16)–(2.17) with the constant `K_n(η, d)` uniform in
`n`: over some neighbourhood of the datum, the condition numbers `K_{abs,n}` of the approximate
problems are eventually bounded. -/
def IsLipschitzStable (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∃ η > (0 : ℝ), ∃ n₀ : ℕ, ∃ K : ℝ≥0, ∀ n ≥ n₀, absCondNumberWithin (Gn n) S d η ≤ K

/-- **The absolute asymptotic condition number** `K^num_abs = lim_k sup_{n ≥ k} K_{abs,n}` of
[quarteroni2000numerical] §2.2 (the display after (2.17)), over the admissible perturbations of
size `< η`. -/
noncomputable def asymptoticAbsCondNumber (Gn : ℕ → D → X) (S : Set D) (d : D) (η : ℝ) :
    ℝ≥0∞ :=
  limsup (fun n => absCondNumberWithin (Gn n) S d η) atTop

/-- **The relative asymptotic condition number** `K^num = lim_k sup_{n ≥ k} K_n` of
[quarteroni2000numerical] §2.2, over the admissible perturbations of size `< η`. -/
noncomputable def asymptoticRelCondNumber (Gn : ℕ → D → X) (S : Set D) (d : D) (η : ℝ) :
    ℝ≥0∞ :=
  limsup (fun n => relCondNumberWithin (Gn n) S d η) atTop

/-- **Convergence** of a numerical method ([quarteroni2000numerical] Definition 2.2, (2.20)):
for every `ε > 0` there are `n₀` and `δ > 0` such that for `n > n₀` and every admissible
perturbation `‖δd‖ < δ`, the numerical solution with datum `d + δd` is within `ε` of the exact
solution with datum `d`. -/
def IsConvergent (G : D → X) (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n > n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
    ‖G d - Gn n (d + δd)‖ ≤ ε

variable {G : D → X} {Gn : ℕ → D → X} {S : Set D} {d : D}

/-- A uniform Lipschitz bound is a uniform modulus of continuity: Lipschitz stability implies
stability. -/
theorem IsLipschitzStable.isStable (h : IsLipschitzStable Gn S d) : IsStable Gn S d := by
  obtain ⟨η, hη, n₀, K, hK⟩ := h
  intro ε hε
  refine ⟨n₀, min η (ε / (K + 1)), lt_min hη (by positivity), fun n hn δd hδd hS => ?_⟩
  have h1 : ‖Gn n (d + δd) - Gn n d‖ ≤ K * ‖δd‖ :=
    norm_sub_le_of_absCondNumberOn_le (hK n hn) ⟨hδd.trans_le (min_le_left _ _), hS⟩
  have h2 : ‖δd‖ ≤ ε / (K + 1) := hδd.le.trans (min_le_right _ _)
  calc ‖Gn n (d + δd) - Gn n d‖ ≤ K * (ε / (K + 1)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 K.coe_nonneg)
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [K.coe_nonneg]

/-- A method is Lipschitz stable iff its absolute asymptotic condition number over some
neighbourhood of the datum is finite. -/
theorem isLipschitzStable_iff_asymptoticAbsCondNumber_ne_top :
    IsLipschitzStable Gn S d ↔ ∃ η > (0 : ℝ), asymptoticAbsCondNumber Gn S d η ≠ ⊤ := by
  simp only [IsLipschitzStable, asymptoticAbsCondNumber, limsup_eq_iInf_iSup_of_nat, ne_eq,
    iInf_eq_top, not_forall]
  refine exists_congr fun η => and_congr_right fun _ => exists_congr fun n₀ => ⟨?_, ?_⟩
  · rintro ⟨K, hK⟩
    exact ((iSup₂_le hK).trans_lt ENNReal.coe_lt_top).ne
  · intro h
    refine ⟨(⨆ n ≥ n₀, absCondNumberWithin (Gn n) S d η).toNNReal, fun n hn => ?_⟩
    rw [ENNReal.coe_toNNReal h]
    exact le_iSup₂ (f := fun n _ => absCondNumberWithin (Gn n) S d η) n hn

/-- The case `δd = 0` of convergence: the numerical solutions with the exact datum converge to
the exact solution. -/
theorem IsConvergent.tendsto (h : IsConvergent G Gn S d) (hd : d ∈ S) :
    Tendsto (fun n => Gn n d) atTop (𝓝 (G d)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨n₀, δ, hδ, hn⟩ := h (ε / 2) (by positivity)
  refine ⟨n₀ + 1, fun n hn' => ?_⟩
  have := hn n (by omega) 0 (by simpa using hδ) (by simpa using hd)
  rw [add_zero] at this
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  linarith

/-- **The sufficient criterion (2.21) of [quarteroni2000numerical]**: if the resolvent is
continuous at `d` within the admissible data and the numerical solutions are eventually
uniformly close to the exact solutions for the same perturbed data, the method is convergent.
The book uses the Lipschitz condition (2.3) here; continuity is all that is needed. -/
theorem isConvergent_of_forall_norm_sub_le (hG : ContinuousWithinAt G S d)
    (h : ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n > n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
      ‖G (d + δd) - Gn n (d + δd)‖ ≤ ε) :
    IsConvergent G Gn S d := by
  intro ε hε
  obtain ⟨n₀, δ₁, hδ₁, h₁⟩ := h (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.1 hG (ε / 2) (by positivity)
  refine ⟨n₀, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n hn δd hδd hS => ?_⟩
  have e₁ := h₁ n hn δd (hδd.trans_le (min_le_left _ _)) hS
  have e₂ := h₂ hS (by simpa [dist_eq_norm] using hδd.trans_le (min_le_right _ _))
  rw [dist_eq_norm, ← norm_neg, neg_sub] at e₂
  calc ‖G d - Gn n (d + δd)‖ = ‖(G d - G (d + δd)) + (G (d + δd) - Gn n (d + δd))‖ := by
        congr 1; abel
    _ ≤ ‖G d - G (d + δd)‖ + ‖G (d + δd) - Gn n (d + δd)‖ := norm_add_le _ _
    _ ≤ ε := by linarith

/-- **Convergence implies stability** ([quarteroni2000numerical] §2.2.1, the necessary condition
(2.24)): a convergent method is stable at every admissible datum. From (2.20) at `δd` and at
`0`, `‖Gn n (d + δd) - Gn n d‖ ≤ ‖Gn n (d + δd) - G d‖ + ‖G d - Gn n d‖ ≤ 2ε`. The book's
conclusion, a bound "of the order of `K(δ, d)`" times `‖δd‖`, is a Lipschitz bound that does not
follow (see the module description); equicontinuity does. -/
theorem IsConvergent.isStable (h : IsConvergent G Gn S d) (hd : d ∈ S) : IsStable Gn S d := by
  intro ε hε
  obtain ⟨n₀, δ, hδ, hn⟩ := h (ε / 2) (by positivity)
  refine ⟨n₀ + 1, δ, hδ, fun n hn' δd hδd hS => ?_⟩
  have e₁ := hn n (by omega) δd hδd hS
  have e₂ := hn n (by omega) 0 (by simpa using hδ) (by simpa using hd)
  rw [add_zero] at e₂
  calc ‖Gn n (d + δd) - Gn n d‖ = ‖-(G d - Gn n (d + δd)) + (G d - Gn n d)‖ := by
        congr 1; abel
    _ ≤ ‖G d - Gn n (d + δd)‖ + ‖G d - Gn n d‖ := by
        rw [← norm_neg (G d - Gn n (d + δd))]; exact norm_add_le _ _
    _ ≤ ε := by linarith

omit [NormedAddCommGroup D] in
/-- **Consistency plus a uniform inverse bound gives pointwise convergence**
([quarteroni2000numerical] §2.2.1, (2.25)): if the approximate problems are uniformly
antilipschitz in the unknown, `‖x - y‖ ≤ M ‖Fn n x d - Fn n y d‖`, then the numerical solutions
with the exact datum converge to the exact solution, since
`‖G d - Gn n d‖ ≤ M ‖Fn n (G d) d - Fn n (Gn n d) d‖ = M ‖Fn n (G d) d‖ → 0`. The antilipschitz
hypothesis is the rigorous content of the book's "`∂Fn/∂x` invertible" mean-value argument. -/
theorem tendsto_of_isConsistent [NormedAddCommGroup Y] {F : X → D → Y} {Fn : ℕ → X → D → Y}
    (hd : d ∈ S) (hF : F (G d) d = 0) (hFn : ∀ n, Fn n (Gn n d) d = 0)
    (hcons : IsConsistent F Fn S) {M : ℝ≥0} (hanti : ∀ n, AntilipschitzWith M fun x => Fn n x d) :
    Tendsto (fun n => Gn n d) atTop (𝓝 (G d)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have h0 : Tendsto (fun n => (M : ℝ) * ‖Fn n (G d) d‖) atTop (𝓝 0) := by
    simpa using ((hcons d hd (G d) hF).norm).const_mul (M : ℝ)
  refine squeeze_zero_norm (fun n => ?_) h0
  have := (hanti n).le_mul_dist (Gn n d) (G d)
  simpa [dist_eq_norm, hFn n] using this

/-- **Stability plus pointwise convergence gives convergence** ([quarteroni2000numerical] §2.2.1,
the sufficient condition): `‖G d - Gn n (d + δd)‖ ≤ ‖G d - Gn n d‖ + ‖Gn n d - Gn n (d + δd)‖`,
the first term small for `n` large and the second by stability. -/
theorem isConvergent_of_isStable (hst : IsStable Gn S d)
    (hpt : Tendsto (fun n => Gn n d) atTop (𝓝 (G d))) : IsConvergent G Gn S d := by
  intro ε hε
  obtain ⟨n₁, δ, hδ, h₁⟩ := hst (ε / 2) (by positivity)
  obtain ⟨n₂, h₂⟩ := Metric.tendsto_atTop.1 hpt (ε / 2) (by positivity)
  refine ⟨max n₁ n₂, δ, hδ, fun n hn δd hδd hS => ?_⟩
  have e₁ := h₁ n (le_of_max_le_left hn.le) δd hδd hS
  have e₂ := h₂ n (le_of_max_le_right hn.le)
  rw [dist_eq_norm, ← norm_neg, neg_sub] at e₂
  calc ‖G d - Gn n (d + δd)‖ = ‖(G d - Gn n d) + -(Gn n (d + δd) - Gn n d)‖ := by
        congr 1; abel
    _ ≤ ‖G d - Gn n d‖ + ‖Gn n (d + δd) - Gn n d‖ := by
        rw [← norm_neg (Gn n (d + δd) - Gn n d)]; exact norm_add_le _ _
    _ ≤ ε := by linarith

/-- **The equivalence theorem in the abstract setting** ("for a consistent numerical method,
stability is equivalent to convergence", [quarteroni2000numerical] §2.2.1): for a consistent
method whose approximate problems admit a uniform inverse bound at the admissible datum `d`,
stability at `d` and convergence at `d` are the same. The evolution-scheme form of Lax and
Richtmyer is `FiniteDifference.isStable_iff_isConvergent`. -/
theorem isStable_iff_isConvergent [NormedAddCommGroup Y] {F : X → D → Y} {Fn : ℕ → X → D → Y}
    (hd : d ∈ S) (hF : F (G d) d = 0) (hFn : ∀ n, Fn n (Gn n d) d = 0)
    (hcons : IsConsistent F Fn S) {M : ℝ≥0} (hanti : ∀ n, AntilipschitzWith M fun x => Fn n x d) :
    IsStable Gn S d ↔ IsConvergent G Gn S d :=
  ⟨fun h => isConvergent_of_isStable h (tendsto_of_isConsistent hd hF hFn hcons hanti),
    fun h => h.isStable hd⟩

/-! ### Backward error -/

section BackwardError

variable [Zero Y] {F : X → D → Y} {xhat : X}

/-- **The backward error** of a computed solution `x̂` ([quarteroni2000numerical] §2.3, "backward
analysis"): the infimum of the sizes of the admissible perturbations `δd` of the datum for which
`x̂` solves the perturbed problem `F x̂ (d + δd) = 0` exactly; `⊤` when there is none. -/
noncomputable def backwardError (F : X → D → Y) (S : Set D) (d : D) (xhat : X) : ℝ≥0∞ :=
  ⨅ (δd : D) (_ : d + δd ∈ S) (_ : F xhat (d + δd) = 0), ‖δd‖ₑ

omit [NormedAddCommGroup X] in
/-- The backward error is at most the size of any admissible perturbation that `x̂` solves. -/
theorem backwardError_le {δd : D} (hS : d + δd ∈ S) (hF : F xhat (d + δd) = 0) :
    backwardError F S d xhat ≤ ‖δd‖ₑ :=
  iInf₂_le_of_le δd hS (iInf_le_of_le hF le_rfl)

omit [NormedAddCommGroup X] in
/-- An exact solution of an admissible problem has backward error zero. -/
theorem backwardError_eq_zero_of_eq (hd : d ∈ S) (hF : F xhat d = 0) :
    backwardError F S d xhat = 0 :=
  nonpos_iff_eq_zero.1 <| by
    simpa using backwardError_le (F := F) (δd := 0) (by simpa using hd) (by simpa using hF)

/-- The pointwise form of "forward error ≤ condition number × backward error": if `x̂` is the
exact solution for the admissible datum `d + δd` with `‖δd‖ < η`, its distance to the exact
solution for `d` is at most `absCondNumberWithin G S d η * ‖δd‖ₑ`. -/
theorem enorm_sub_le_absCondNumberWithin_mul_enorm (hG : IsResolvent F S G) {δd : D} {η : ℝ}
    (hδd : ‖δd‖ < η) (hS : d + δd ∈ S) (hF : F xhat (d + δd) = 0) :
    ‖xhat - G d‖ₑ ≤ absCondNumberWithin G S d η * ‖δd‖ₑ := by
  rw [hG.eq_of hS hF]
  exact enorm_sub_le_absCondNumberOn_mul ⟨hδd, hS⟩

/-- A well-posed problem (continuous resolvent) identifies its solution by backward error: if
`x̂` is the exact solution for admissible data arbitrarily close to `d`, then `x̂ = G d`. -/
theorem IsResolvent.eq_of_backwardError_eq_zero (hG : IsResolvent F S G)
    (hc : ContinuousWithinAt G S d) (h : backwardError F S d xhat = 0) : xhat = G d := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 hc ε hε
  have : backwardError F S d xhat < ENNReal.ofReal δ := by
    rw [h]; exact ENNReal.ofReal_pos.2 hδ
  simp only [backwardError, iInf_lt_iff] at this
  obtain ⟨δd, hS, hF, hlt⟩ := this
  rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hδ] at hlt
  rw [hG.eq_of hS hF]
  exact (hcont hS (by simpa [dist_eq_norm] using hlt)).le

/-- **Forward error ≤ condition number × backward error** ([quarteroni2000numerical] §2.3): for
a well-posed problem (a resolvent continuous at `d` within the admissible data) and a computed
`x̂` whose backward error is `< η`, `‖x̂ - G d‖ₑ ≤ absCondNumberWithin G S d η * backwardError F S
d x̂`.

The continuity hypothesis is the book's standing well-posedness (§2.1) and cannot be dropped: with
`D = X = Y = ℝ`, `S = univ`, `G 0 = 0`, `G y = 1` for `y ≠ 0`, `F x y = x - G y`, `d = 0` and
`x̂ = 1`, the backward error is `0` (every `δd ≠ 0` is an exact perturbation) and the condition
number is `⊤`, so the right-hand side is `⊤ * 0 = 0` and the left-hand side is `1`. Continuity is
needed only in that case — the condition number `⊤` and the backward error `0` without being
attained — and in every other case the bound is the infimum of the pointwise bounds
`enorm_sub_le_absCondNumberWithin_mul_enorm`, which need no hypothesis. -/
theorem enorm_sub_le_absCondNumberWithin_mul_backwardError
    (hG : IsResolvent F S G) (hc : ContinuousWithinAt G S d) {η : ℝ}
    (hη : backwardError F S d xhat < ENNReal.ofReal η) :
    ‖xhat - G d‖ₑ ≤ absCondNumberWithin G S d η * backwardError F S d xhat := by
  -- the perturbations of size `< η` for which `x̂` is exact
  set T := {δd : D | d + δd ∈ S ∧ F xhat (d + δd) = 0 ∧ ‖δd‖ < η}
  have hne : ∃ δd, δd ∈ T := by
    simp only [backwardError, iInf_lt_iff] at hη
    obtain ⟨δd, hS, hF, hlt⟩ := hη
    have hη0 : 0 < η := ENNReal.ofReal_pos.1 (pos_of_gt hlt)
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hη0] at hlt
    exact ⟨δd, hS, hF, hlt⟩
  have hB : backwardError F S d xhat = ⨅ δd : T, ‖(δd : D)‖ₑ := by
    refine le_antisymm (le_iInf fun δd => backwardError_le δd.2.1 δd.2.2.1) ?_
    refine le_iInf fun δd => le_iInf fun hS => le_iInf fun hF => ?_
    by_cases hlt : ‖δd‖ < η
    · exact iInf_le_of_le ⟨δd, hS, hF, hlt⟩ le_rfl
    · obtain ⟨δd', hδd'⟩ := hne
      refine (iInf_le_of_le ⟨δd', hδd'⟩ le_rfl).trans ?_
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hδd'.2.2.le.trans (not_lt.1 hlt))
  have : Nonempty T := let ⟨δd, hδd⟩ := hne; ⟨⟨δd, hδd⟩⟩
  by_cases hA : absCondNumberWithin G S d η = ⊤
  · by_cases hB0 : backwardError F S d xhat = 0
    · rw [hG.eq_of_backwardError_eq_zero hc hB0]; simp
    · rw [hA, ENNReal.top_mul hB0]; exact le_top
  rw [hB, ENNReal.mul_iInf fun h => absurd h hA]
  exact le_iInf fun δd =>
    enorm_sub_le_absCondNumberWithin_mul_enorm hG δd.2.2.2 δd.2.1 δd.2.2.1

end BackwardError

end Conditioning
