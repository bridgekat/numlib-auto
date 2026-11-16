/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Antilipschitz
import Numlib.Conditioning.Problem

/-!
# Consistency, stability and convergence of a numerical method

Let $F(x, d) = 0$ be a problem on the admissible data $S$ with resolvent $G$, as in
`Numlib.Conditioning.Problem`. A *numerical method* for it is a family of approximate problems
$F_n(x, d) = 0$, $n \in \mathbb{N}$, with resolvents $G_n$. The method is *consistent* if every
exact solution makes the residual $F_n(x, d)$ tend to $0$, *stable* at $d$ if the numerical
solutions $G_n$ depend continuously on the datum uniformly in $n$ for large $n$, and *convergent* at
$d$ if $G_n(d + \delta d)$ is close to $G(d)$ for large $n$ and small admissible $\delta d$. The
module proves the relations of §2.2.1 of [quarteroni2000numerical] between these notions, up to the
abstract equivalence theorem: for a consistent method whose approximate problems have a uniform
inverse bound, stability and convergence are equivalent. The presentation follows
[quarteroni2000numerical], §2.2–2.3.

The *backward error* of a computed solution $\hat x$ is the infimum of the sizes of the admissible
perturbations $\delta d$ of the datum for which $\hat x$ solves $F(\hat x, d + \delta d) = 0$
exactly, as in §2.3 of the source. The module ends with the bound "forward error $\le$ condition
number $\times$ backward error" for a well-posed problem.

## Main definitions

* `Conditioning.IsConsistent`, `Conditioning.IsStronglyConsistent`,
  `Conditioning.IsStronglyConsistentMultistep`: consistency (2.13) and strong consistency (2.14).
* `Conditioning.IsStable`: equicontinuity of the tail of the numerical resolvents at the datum.
* `Conditioning.IsLipschitzStable`: the condition numbers of the approximate problems are eventually
  bounded, the Lipschitz form (2.16)–(2.17) of stability.
* `Conditioning.asymptoticAbsCondNumber`, `Conditioning.asymptoticRelCondNumber`: the asymptotic
  condition numbers $K^{\mathrm{num}}_{\mathrm{abs}}$ and $K^{\mathrm{num}}$.
* `Conditioning.IsConvergent`: convergence, Definition 2.2.
* `Conditioning.backwardError`: the backward error of a computed solution.

## Main results

* `Conditioning.isLipschitzStable_iff_asymptoticAbsCondNumber_ne_top`: Lipschitz stability is the
  finiteness of the asymptotic condition number.
* `Conditioning.IsConvergent.isStable`: a convergent method is stable.
* `Conditioning.isConvergent_of_isStable`: stability and pointwise convergence give convergence.
* `Conditioning.tendsto_of_isConsistent`: consistency and a uniform inverse bound give pointwise
  convergence.
* `Conditioning.isStable_iff_isConvergent`: the abstract equivalence theorem.
* `Conditioning.enorm_sub_le_absCondNumberWithin_mul_backwardError`: forward error $\le$ condition
  number $\times$ backward error, for a resolvent continuous at the datum.

## Implementation notes

* A method indexed by a mesh size $h \to 0$ is written with $n \mapsto h_n$. All notions are
  `Prop`-valued predicates or $[0, \infty]$-valued quantities on plain functions.
* Consistency and strong consistency are stated for the solution relation $F(x, d) = 0$, not for the
  resolvent, so that they make sense without uniqueness: Newton's method approximates *a* root.
* The condition numbers $K_n$ and $K_{\mathrm{abs}, n}$ of (2.17) and their first-order formulas
  (2.19) are `Conditioning.relCondNumberWithin` and `Conditioning.relCondNumber_eq_enorm_fderiv`
  applied to $G_n$; there is no new definition.
* Convergence implies the equicontinuity form of stability, not a Lipschitz form. For the problem
  $G(d) = 0$ on $\mathbb{R}$, the method $G_n(d) = \sqrt{|d|} / n$ is convergent and consistent at
  $d = 0$, but no $G_n$ is Lipschitz at $0$.
* The uniform inverse bound $\|x - y\| \le M \|F_n(x, d) - F_n(y, d)\|$ (`AntilipschitzWith`) in
  `Conditioning.tendsto_of_isConsistent` is the rigorous content of the mean-value argument (2.25)
  of the source, which assumes that $\partial F_n / \partial x$ is invertible; that argument fails
  as an equality in a normed space.
* The Lax–Richtmyer theorem for evolution schemes is `FiniteDifference.isStable_iff_isConvergent`.
  Its stability is a bound on the powers of an operator, and neither theorem is an instance of the
  other.
* The bound "forward error $\le$ condition number $\times$ backward error" needs the resolvent to be
  continuous at the datum within the admissible data, which is the well-posedness that the source
  assumes in §2.1. Without it the bound is false, because $\infty \cdot 0 = 0$ in $[0, \infty]$ and
  the multiplication does not commute with the infimum that defines the backward error. The
  counterexample is in the doc comment of
  `Conditioning.enorm_sub_le_absCondNumberWithin_mul_backwardError`. The bound for a single
  perturbation, `Conditioning.enorm_sub_le_absCondNumberWithin_mul_enorm`, needs no hypothesis, and
  continuity is exactly what makes a zero backward error force $\hat x = G(d)$
  (`Conditioning.IsResolvent.eq_of_backwardError_eq_zero`).
* The backward error here is a $[0, \infty]$-valued absolute quantity for a single datum. The
  root-namespace `backwardError` of `Numlib.Conditioning.LinearSystem` is the normwise, weighted
  backward error of a linear system (Rigal–Gaches), a different quantity.
* The datum $d$ is fixed and does not depend on $n$ (the $d_n$ of the source). An approximation of
  the data is composed into $G_n$ when needed.
-/

open Filter Topology Set
open scoped ENNReal NNReal

namespace Conditioning

variable {D X Y : Type*}

/-! ### Consistency -/

section Consistency

variable [Zero Y]

/-- **Consistency** of the approximate problems $F_n(x, d) = 0$ with the problem $F(x, d) = 0$ on
the admissible data $S$: for every $d \in S$ and every $x$ with $F(x, d) = 0$, $$F_n(x, d) \to 0
\quad \text{as } n \to \infty.$$ This is (2.13) of [quarteroni2000numerical].

The definition uses the solution relation $F(x, d) = 0$, not the resolvent, so that no
uniqueness is needed. -/
def IsConsistent [TopologicalSpace Y] (F : X → D → Y) (Fn : ℕ → X → D → Y) (S : Set D) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 → Tendsto (fun n => Fn n x d) atTop (𝓝 0)

/-- **Strong consistency** of the approximate problems $F_n(x, d) = 0$ with the problem
$F(x, d) = 0$ on the admissible data $S$: for every $d \in S$ and every $x$ with $F(x, d) = 0$,
$F_n(x, d) = 0$ for all $n$, not only in the limit. This is the strong consistency of §2.2 of
[quarteroni2000numerical]. -/
def IsStronglyConsistent (F : X → D → Y) (Fn : ℕ → X → D → Y) (S : Set D) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 → ∀ n, Fn n x d = 0

/-- **Strong consistency of a multistep scheme**, (2.14) of [quarteroni2000numerical]. The $n$-th
approximate problem $F_n(x_n, \dots, x_{n-q}; d) = 0$ involves $q + 1$ consecutive iterates. The
scheme is strongly consistent with $F(x, d) = 0$ on $S$ if, for every $d \in S$ and every $x$
with $F(x, d) = 0$, the constant tuple $(x, \dots, x)$ solves $F_n(x, \dots, x; d) = 0$ for all
$n$.

The $q + 1$ iterates are a function `Fin (q + 1) → X`. -/
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

/-- **Stability** of the numerical resolvents $G_n$ at the datum $d$ on the admissible data $S$: for
every $\varepsilon > 0$ there are $n_0$ and $\delta > 0$ such that $$\|G_n(d + \delta d) -
G_n(d)\| \le \varepsilon$$ for all $n \ge n_0$ and all $\delta d$ with $\|\delta d\| < \delta$
and $d + \delta d \in S$. So for large $n$ the numerical solutions depend continuously on the
datum, uniformly in $n$: the tail of $(G_n)$ is equicontinuous at $d$ within $S$.

This is the notion for which "convergent implies stable" (§2.2.1 of [quarteroni2000numerical],
(2.24)) is true. The Lipschitz form (2.16) of the source is `Conditioning.IsLipschitzStable`. -/
def IsStable (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n ≥ n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
    ‖Gn n (d + δd) - Gn n d‖ ≤ ε

/-- **Lipschitz stability** of the numerical resolvents $G_n$ at the datum $d$ on the admissible
data $S$: there are $\eta > 0$, $n_0$ and a real $K \ge 0$ such that $$K_{\mathrm{abs}, n}(d,
\eta) \le K \quad \text{for all } n \ge n_0,$$ where $K_{\mathrm{abs}, n}(d, \eta)$ is the
absolute condition number `Conditioning.absCondNumberWithin` of $G_n$ over the admissible
perturbations of size less than $\eta$.

This is (2.16)–(2.17) of [quarteroni2000numerical] with the constant $K_n(\eta, d)$ uniform in
$n$. -/
def IsLipschitzStable (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∃ η > (0 : ℝ), ∃ n₀ : ℕ, ∃ K : ℝ≥0, ∀ n ≥ n₀, absCondNumberWithin (Gn n) S d η ≤ K

/-- The **absolute asymptotic condition number** of the numerical resolvents $G_n$ at $d$, over the
admissible perturbations of size less than $\eta$: $$K^{\mathrm{num}}_{\mathrm{abs}}(d, \eta) =
\limsup_{n \to \infty} K_{\mathrm{abs}, n}(d, \eta) = \lim_{k \to \infty} \sup_{n \ge k}
K_{\mathrm{abs}, n}(d, \eta) \in [0, \infty],$$ with $K_{\mathrm{abs}, n}(d, \eta)$ the absolute
condition number `Conditioning.absCondNumberWithin` of $G_n$. This is the display after (2.17)
in §2.2 of [quarteroni2000numerical]. -/
noncomputable def asymptoticAbsCondNumber (Gn : ℕ → D → X) (S : Set D) (d : D) (η : ℝ) :
    ℝ≥0∞ :=
  limsup (fun n => absCondNumberWithin (Gn n) S d η) atTop

/-- The **relative asymptotic condition number** of the numerical resolvents $G_n$ at $d$, over the
admissible perturbations of size less than $\eta$: $$K^{\mathrm{num}}(d, \eta) = \limsup_{n \to
\infty} K_n(d, \eta) \in [0, \infty],$$ with $K_n(d, \eta)$ the relative condition number
`Conditioning.relCondNumberWithin` of $G_n$. This is the relative number of §2.2 of
[quarteroni2000numerical]. -/
noncomputable def asymptoticRelCondNumber (Gn : ℕ → D → X) (S : Set D) (d : D) (η : ℝ) :
    ℝ≥0∞ :=
  limsup (fun n => relCondNumberWithin (Gn n) S d η) atTop

/-- **Convergence** of the numerical resolvents $G_n$ to the resolvent $G$ at the datum $d$ on the
admissible data $S$: for every $\varepsilon > 0$ there are $n_0$ and $\delta > 0$ such that
$$\|G(d) - G_n(d + \delta d)\| \le \varepsilon$$ for all $n > n_0$ and all $\delta d$ with
$\|\delta d\| < \delta$ and $d + \delta d \in S$. This is (2.20) of Definition 2.2 of
[quarteroni2000numerical]. -/
def IsConvergent (G : D → X) (Gn : ℕ → D → X) (S : Set D) (d : D) : Prop :=
  ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∃ δ > (0 : ℝ), ∀ n > n₀, ∀ δd, ‖δd‖ < δ → d + δd ∈ S →
    ‖G d - Gn n (d + δd)‖ ≤ ε

variable {G : D → X} {Gn : ℕ → D → X} {S : Set D} {d : D}

/-- Lipschitz stability implies stability: a uniform Lipschitz bound is a uniform modulus of
continuity. -/
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

/-- The numerical resolvents $G_n$ are Lipschitz stable at $d$ if and only if there is $\eta > 0$
with $K^{\mathrm{num}}_{\mathrm{abs}}(d, \eta) \neq \infty$. -/
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

/-- If the method is convergent at $d$ and $d \in S$, then $G_n(d) \to G(d)$ as $n \to \infty$. This
is the case $\delta d = 0$ of convergence. -/
theorem IsConvergent.tendsto (h : IsConvergent G Gn S d) (hd : d ∈ S) :
    Tendsto (fun n => Gn n d) atTop (𝓝 (G d)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨n₀, δ, hδ, hn⟩ := h (ε / 2) (by positivity)
  refine ⟨n₀ + 1, fun n hn' => ?_⟩
  have := hn n (by omega) 0 (by simpa using hδ) (by simpa using hd)
  rw [add_zero] at this
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  linarith

/-- **The sufficient criterion (2.21)** of [quarteroni2000numerical]. Suppose that $G$ is continuous
at $d$ within $S$, and that for every $\varepsilon > 0$ there are $n_0$ and $\delta > 0$ such
that $$\|G(d + \delta d) - G_n(d + \delta d)\| \le \varepsilon$$ for all $n > n_0$ and all
$\delta d$ with $\|\delta d\| < \delta$ and $d + \delta d \in S$. Then the method is convergent
at $d$.

The source uses the Lipschitz condition (2.3) here; continuity is enough. -/
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

/-- **Convergence implies stability**, the necessary condition (2.24) of §2.2.1 of
[quarteroni2000numerical]. If the method is convergent at $d$ and $d \in S$, then it is stable
at $d$.

The source concludes a bound "of the order of $K(\delta, d)$" times $\|\delta d\|$. This
Lipschitz bound does not follow (see the module doc comment); equicontinuity does, from
$\|G_n(d + \delta d) - G_n(d)\| \le \|G_n(d + \delta d) - G(d)\| + \|G(d) - G_n(d)\| \le 2
\varepsilon$. -/
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
/-- **Consistency and a uniform inverse bound give pointwise convergence**, after (2.25) of §2.2.1
of [quarteroni2000numerical]. Let $Y$ be a normed group, let $d \in S$, and suppose that
$F(G(d), d) = 0$, that $F_n(G_n(d), d) = 0$ for all $n$, and that the approximate problems are
consistent with $F$ on $S$. Suppose that there is a real $M \ge 0$ with $$\|x - y\| \le M
\|F_n(x, d) - F_n(y, d)\| \quad \text{for all } n, x, y.$$ Then $G_n(d) \to G(d)$ as
$n \to \infty$.

The proof is $\|G(d) - G_n(d)\| \le M \|F_n(G(d), d) - F_n(G_n(d), d)\| = M \|F_n(G(d), d)\| \to
0$. The inverse bound is `AntilipschitzWith M` for each $x \mapsto F_n(x, d)$; it is the
rigorous content of the mean-value argument of the source, which assumes that
$\partial F_n / \partial x$ is invertible. The datum space $D$ needs no norm here. -/
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

/-- **Stability and pointwise convergence give convergence**, the sufficient condition of §2.2.1 of
[quarteroni2000numerical]. If the method is stable at $d$ and $G_n(d) \to G(d)$ as
$n \to \infty$, then it is convergent at $d$.

The proof splits $\|G(d) - G_n(d + \delta d)\| \le \|G(d) - G_n(d)\| + \|G_n(d) - G_n(d + \delta
d)\|$; the first term is small for large $n$ and the second by stability. -/
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

/-- **The equivalence theorem in the abstract setting**: "for a consistent numerical method,
stability is equivalent to convergence" (§2.2.1 of [quarteroni2000numerical]). Under the
hypotheses of `Conditioning.tendsto_of_isConsistent` (the datum $d \in S$, $F(G(d), d) = 0$,
$F_n(G_n(d), d) = 0$ for all $n$, consistency, and the uniform inverse bound
$\|x - y\| \le M \|F_n(x, d) - F_n(y, d)\|$), the method is stable at $d$ if and only if it is
convergent at $d$.

The evolution-scheme form of Lax and Richtmyer is `FiniteDifference.isStable_iff_isConvergent`. -/
theorem isStable_iff_isConvergent [NormedAddCommGroup Y] {F : X → D → Y} {Fn : ℕ → X → D → Y}
    (hd : d ∈ S) (hF : F (G d) d = 0) (hFn : ∀ n, Fn n (Gn n d) d = 0)
    (hcons : IsConsistent F Fn S) {M : ℝ≥0} (hanti : ∀ n, AntilipschitzWith M fun x => Fn n x d) :
    IsStable Gn S d ↔ IsConvergent G Gn S d :=
  ⟨fun h => isConvergent_of_isStable h (tendsto_of_isConsistent hd hF hFn hcons hanti),
    fun h => h.isStable hd⟩

/-! ### Backward error -/

section BackwardError

variable [Zero Y] {F : X → D → Y} {xhat : X}

/-- The **backward error** of a computed solution $\hat x$ of $F(x, d) = 0$ on the admissible data
$S$: $$\beta(\hat x) = \inf \{ \|\delta d\| : d + \delta d \in S,\ F(\hat x, d + \delta d) = 0
\} \in [0, \infty],$$ the infimum of the sizes of the admissible perturbations of the datum for
which $\hat x$ solves the perturbed problem exactly. It is $\infty$ when there is no such
perturbation. This is the backward analysis of §2.3 of [quarteroni2000numerical]. -/
noncomputable def backwardError (F : X → D → Y) (S : Set D) (d : D) (xhat : X) : ℝ≥0∞ :=
  ⨅ (δd : D) (_ : d + δd ∈ S) (_ : F xhat (d + δd) = 0), ‖δd‖ₑ

omit [NormedAddCommGroup X] in
/-- If $d + \delta d \in S$ and $F(\hat x, d + \delta d) = 0$, then the backward error of $\hat x$
is at most $\|\delta d\|$. -/
theorem backwardError_le {δd : D} (hS : d + δd ∈ S) (hF : F xhat (d + δd) = 0) :
    backwardError F S d xhat ≤ ‖δd‖ₑ :=
  iInf₂_le_of_le δd hS (iInf_le_of_le hF le_rfl)

omit [NormedAddCommGroup X] in
/-- If $d \in S$ and $F(\hat x, d) = 0$, then the backward error of $\hat x$ is $0$. -/
theorem backwardError_eq_zero_of_eq (hd : d ∈ S) (hF : F xhat d = 0) :
    backwardError F S d xhat = 0 :=
  nonpos_iff_eq_zero.1 <| by
    simpa using backwardError_le (F := F) (δd := 0) (by simpa using hd) (by simpa using hF)

/-- The bound "forward error $\le$ condition number $\times$ backward error" for a single
perturbation. Let $G$ be a resolvent of $F(x, d) = 0$ on $S$. If $\|\delta d\| < \eta$,
$d + \delta d \in S$ and $F(\hat x, d + \delta d) = 0$, then $$\|\hat x - G(d)\| \le
K_{\mathrm{abs}}(d, \eta) \, \|\delta d\|$$ in $[0, \infty]$, where $K_{\mathrm{abs}}(d, \eta)$
is `Conditioning.absCondNumberWithin G S d η`. -/
theorem enorm_sub_le_absCondNumberWithin_mul_enorm (hG : IsResolvent F S G) {δd : D} {η : ℝ}
    (hδd : ‖δd‖ < η) (hS : d + δd ∈ S) (hF : F xhat (d + δd) = 0) :
    ‖xhat - G d‖ₑ ≤ absCondNumberWithin G S d η * ‖δd‖ₑ := by
  rw [hG.eq_of hS hF]
  exact enorm_sub_le_absCondNumberOn_mul ⟨hδd, hS⟩

/-- Let $G$ be a resolvent of $F(x, d) = 0$ on $S$ that is continuous at $d$ within $S$. If the
backward error of $\hat x$ is $0$, then $\hat x = G(d)$. So a well-posed problem identifies its
solution by the backward error. -/
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

/-- **Forward error $\le$ condition number $\times$ backward error**, §2.3 of
[quarteroni2000numerical]. Let $G$ be a resolvent of $F(x, d) = 0$ on $S$ that is continuous at
$d$ within $S$. If the backward error $\beta(\hat x)$ of $\hat x$ is less than $\eta$, then
$$\|\hat x - G(d)\| \le K_{\mathrm{abs}}(d, \eta) \, \beta(\hat x)$$ in $[0, \infty]$, where
$K_{\mathrm{abs}}(d, \eta)$ is `Conditioning.absCondNumberWithin G S d η`.

The continuity hypothesis is the well-posedness that the source assumes in §2.1, and it cannot
be dropped. Take $D = X = Y = \mathbb{R}$, $S = \mathbb{R}$, $G(0) = 0$ and $G(y) = 1$ for
$y \neq 0$, $F(x, y) = x - G(y)$, $d = 0$ and $\hat x = 1$. Every $\delta d \neq 0$ satisfies
$F(\hat x, \delta d) = 0$, so the backward error is $0$ and is not attained. The condition
number is $\infty$, because $|G(\delta d) - G(0)| / |\delta d| = 1 / |\delta d|$ is unbounded.
The right-hand side is $\infty \cdot 0 = 0$, and the left-hand side is $1$. Continuity is needed
only in this case, where the condition number is $\infty$ and the backward error is $0$ without
being attained; in every other case the bound is the infimum of the bounds
`Conditioning.enorm_sub_le_absCondNumberWithin_mul_enorm`, which need no hypothesis. -/
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
