/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.RCLike.Basic
import Numlib.Analysis.Normed.Ring.CondNumber

/-!
# Well-posedness and condition numbers of a problem

A *problem* is an equation $F(x, d) = 0$ with a datum $d \in D$ and an unknown $x \in X$. A
*resolvent* of the problem on a set $S$ of admissible data is a map $G : D \to X$ such that, for
every $d \in S$, the solutions of $F(x, d) = 0$ are exactly $x = G(d)$. The problem is *well posed*
(in the sense of Hadamard) when it has a continuous resolvent. The *condition numbers* measure how
much a perturbation $\delta d$ of the datum is amplified in the solution. The absolute condition
number over a set $N$ of perturbations is $$K_{\mathrm{abs}}^N(d) = \sup_{\delta d \in N,\ \delta d
\neq 0} \frac{\|G(d + \delta d) - G(d)\|}{\|\delta d\|} \in [0, \infty],$$ the relative one divides
by $\|G(d)\| / \|d\|$ inside the supremum, and the first-order condition numbers are the limits of
these numbers as the size $\eta$ of the admissible perturbations tends to $0^+$. The presentation
follows [quarteroni2000numerical], §2.1.

The main theorem is the first-order formula (2.7) of [quarteroni2000numerical]: if the resolvent has
the Fréchet derivative $G'$ at an interior point $d$ of $S$, then the first-order absolute condition
number is $\|G'\|$. Its instances are a bounded linear resolvent, a linear system perturbed in its
right-hand side (Example 2.3 of the source, with the bound $K(b) \le \kappa(A)$), and the root of
$\varphi(x) = d$, whose absolute condition number is $\|\varphi'\|^{-1}$ (Example 2.4 of the
source); a multiple root has condition number $\infty$. The module also defines the scaled relative
condition number of [golub2013matrix], §9.1.6, and shows that it equals the first-order relative
condition number wherever the resolvent is differentiable.

## Main definitions

* `Conditioning.IsResolvent`: $G$ gives the unique solution of $F(x, d) = 0$ for every $d \in S$.
* `Conditioning.IsWellPosed`: the problem has a resolvent on $S$ that is continuous on $S$.
* `Conditioning.absCondNumberOn`: the supremum of $\|G(d + \delta d) - G(d)\| / \|\delta d\|$ over
  the nonzero $\delta d \in N$.
* `Conditioning.perturbations`: the perturbations $\delta d$ with $\|\delta d\| < \eta$ and
  $d + \delta d \in S$.
* `Conditioning.absCondNumberWithin`, `Conditioning.absCondNumber`: the absolute condition number
  over the admissible perturbations of size less than $\eta$, and its limit as $\eta \to 0^+$.
* `Conditioning.relCondNumberOn`, `Conditioning.relCondNumberWithin`, `Conditioning.relCondNumber`:
  the relative counterparts.
* `Conditioning.scaledRelCondNumber`: the relative condition number of [golub2013matrix], §9.1.6,
  normalized by the radius of the ball of relative perturbations.

## Main results

* `Conditioning.absCondNumberWithin_ne_top_iff`: the Lipschitz condition (2.3) of
  [quarteroni2000numerical] holds if and only if the condition number is finite.
* `Conditioning.continuousWithinAt_of_absCondNumberWithin_ne_top`: a finite condition number makes
  the resolvent continuous at the datum.
* `Conditioning.absCondNumber_eq_enorm_fderiv`, `Conditioning.relCondNumber_eq_enorm_fderiv`: the
  first-order formula (2.7), $K_{\mathrm{abs}}(d) = \|G'\|$ and $K(d) = \|G'\| \|d\| / \|G(d)\|$.
* `Conditioning.relCondNumber_symm_le_condNumber`: for $Ax = b$ perturbed in $b$, the relative
  condition number is at most $\kappa(A)$.
* `Conditioning.scaledRelCondNumber_eq_relCondNumber`: the two relative condition numbers agree at a
  point of differentiability.
* `Conditioning.absCondNumber_of_local_left_inverse`, `Conditioning.absCondNumber_localInverse`: a
  simple root has absolute condition number $\|\varphi'^{-1}\|$.
* `Conditioning.absCondNumber_eq_top_of_fderiv_eq_zero`: a multiple root has condition number
  $\infty$.

## Implementation notes

* All condition numbers take values in $[0, \infty]$ (`ℝ≥0∞`), and the norms in their definitions
  are the extended norms `‖·‖ₑ`. So "the condition number is infinite" (Remark 2.1 of
  [quarteroni2000numerical]) is the value $\infty$, every supremum and infimum is defined, and the
  Lipschitz condition (2.3) of the source is the finiteness of the condition number.
* The neighbourhood of admissible perturbations in Definition 2.1 of [quarteroni2000numerical] is
  the parameter $N$ of `Conditioning.absCondNumberOn`. `Conditioning.absCondNumberWithin` takes for
  $N$ the set `Conditioning.perturbations S d η`. `Conditioning.absCondNumber` is the infimum over
  $\eta > 0$, which is the limit as $\eta \to 0^+$ because the condition number is monotone in
  $\eta$.
* The relative condition numbers divide by $\|G(d)\| / \|d\|$ inside the supremum, as (2.4) of the
  source does. They equal the absolute ones times $\|d\| / \|G(d)\|$, and they are meaningful only
  for $d \neq 0$ and $G(d) \neq 0$.
* The infinite conditioning of a multiple root is stated within the admissible set $S$, so that it
  covers roots that exist only on one side of the datum.
* The finite-difference stability and convergence of `Numlib.FiniteDifference.LaxEquivalence` are
  different notions from the ones here, and neither is stated through the other.
-/

open Asymptotics Filter Topology Set
open scoped ENNReal NNReal

namespace Conditioning

variable {D X Y : Type*}

/-! ### Problems and resolvents -/

section Resolvent

variable [Zero Y]

/-- Let $F : X \times D \to Y$ and $S \subseteq D$. The map $G : D \to X$ is a **resolvent** of the
problem $F(x, d) = 0$ on the admissible data $S$ if, for every $d \in S$ and every $x \in X$,
$$F(x, d) = 0 \iff x = G(d).$$

This is the map $d \mapsto x$ of (2.6) of [quarteroni2000numerical]. -/
def IsResolvent (F : X → D → Y) (S : Set D) (G : D → X) : Prop :=
  ∀ d ∈ S, ∀ x, F x d = 0 ↔ x = G d

/-- The problem $F(x, d) = 0$ is **well posed** on the admissible data $S$ if it has a resolvent $G$
on $S$ (a unique solution for every $d \in S$) that is continuous on $S$. This is well-posedness
in the sense of Hadamard, as in §2.1 of [quarteroni2000numerical].

The definition asks for continuity, not for the Lipschitz condition (2.3) of the source. A
well-posed problem can have an infinite condition number (Remark 2.1 of the source), and the
condition (2.3) is `Conditioning.absCondNumberWithin_ne_top_iff`. -/
def IsWellPosed [TopologicalSpace D] [TopologicalSpace X] (F : X → D → Y) (S : Set D) : Prop :=
  ∃ G, IsResolvent F S G ∧ ContinuousOn G S

variable {F : X → D → Y} {S : Set D} {G : D → X}

/-- Let $G$ be a resolvent of $F(x, d) = 0$ on $S$. If $d \in S$ and $F(x, d) = 0$, then $x = G(d)$.
-/
theorem IsResolvent.eq_of (h : IsResolvent F S G) {d : D} (hd : d ∈ S) {x : X} (hx : F x d = 0) :
    x = G d :=
  (h d hd x).1 hx

/-- Let $G$ be a resolvent of $F(x, d) = 0$ on $S$. Then $F(G(d), d) = 0$ for every $d \in S$. -/
theorem IsResolvent.apply (h : IsResolvent F S G) {d : D} (hd : d ∈ S) : F (G d) d = 0 :=
  (h d hd (G d)).2 rfl

/-- If $G$ is a resolvent of $F(x, d) = 0$ on $S$ and $G$ is continuous on $S$, then the problem is
well posed on $S$. -/
theorem IsResolvent.isWellPosed [TopologicalSpace D] [TopologicalSpace X] (h : IsResolvent F S G)
    (hG : ContinuousOn G S) : IsWellPosed F S :=
  ⟨G, h, hG⟩

end Resolvent

/-! ### Condition numbers -/

variable [NormedAddCommGroup D] [NormedAddCommGroup X]

/-- The **absolute condition number** of $G : D \to X$ at the datum $d$ over a set $N \subseteq D$
of perturbations is $$K_{\mathrm{abs}}^N(d) = \sup_{\delta d \in N,\ \delta d \neq 0}
\frac{\|G(d + \delta d) - G(d)\|}{\|\delta d\|} \in [0, \infty].$$ It is $0$ if $N$ contains no
nonzero perturbation.

This is (2.5) of Definition 2.1 of [quarteroni2000numerical], with the neighbourhood of
admissible perturbations of the source as the parameter $N$. The norms are the extended norms
`‖·‖ₑ`. -/
noncomputable def absCondNumberOn (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ

/-- The **admissible perturbations of size less than $\eta$** of the datum $d$ in the admissible set
$S$: the set of $\delta d \in D$ with $\|\delta d\| < \eta$ and $d + \delta d \in S$. -/
def perturbations (S : Set D) (d : D) (η : ℝ) : Set D :=
  {δd | ‖δd‖ < η ∧ d + δd ∈ S}

/-- The absolute condition number of $G$ at $d$ over the admissible perturbations of size less than
$\eta$: $$K_{\mathrm{abs}}(d, \eta) = \sup \left\{ \frac{\|G(d + \delta d) - G(d)\|}{\|\delta
d\|} : 0 < \|\delta d\| < \eta,\ d + \delta d \in S \right\} \in [0, \infty].$$

This is $K_{\mathrm{abs}}(d)$ of (2.5) of [quarteroni2000numerical], with the neighbourhood of
the source taken to be the ball of radius $\eta$ intersected with the admissible data. It is
`Conditioning.absCondNumberOn` for `Conditioning.perturbations S d η`. -/
noncomputable def absCondNumberWithin (G : D → X) (S : Set D) (d : D) (η : ℝ) : ℝ≥0∞ :=
  absCondNumberOn G (perturbations S d η) d

/-- The **first-order absolute condition number** of $G$ at $d$ on the admissible data $S$:
$$K_{\mathrm{abs}}(d) = \inf_{\eta > 0} K_{\mathrm{abs}}(d, \eta),$$ where
$K_{\mathrm{abs}}(d, \eta)$ is `Conditioning.absCondNumberWithin G S d η`.

Because $K_{\mathrm{abs}}(d, \eta)$ is monotone in $\eta$, the infimum is the limit as
$\eta \to 0^+$ (`Conditioning.tendsto_absCondNumberWithin`): the source describes this number as
"the limit of the Lipschitz constant of $G$ as the perturbation on the data tends to zero". The
first-order formula (2.7) of [quarteroni2000numerical] computes it. -/
noncomputable def absCondNumber (G : D → X) (S : Set D) (d : D) : ℝ≥0∞ :=
  ⨅ (η : ℝ) (_ : 0 < η), absCondNumberWithin G S d η

/-- The **relative condition number** of $G : D \to X$ at the datum $d$ over a set $N \subseteq D$
of perturbations is $$K^N(d) = \sup_{\delta d \in N,\ \delta d \neq 0} \frac{\|G(d + \delta d) -
G(d)\| / \|G(d)\|}{\|\delta d\| / \|d\|} \in [0, \infty].$$

This is (2.4) of Definition 2.1 of [quarteroni2000numerical]. The quotients are those of
$[0, \infty]$, with the extended norms `‖·‖ₑ`. The number is meaningful only for $d \neq 0$ and
$G(d) \neq 0$; otherwise the absolute condition number is the one to use, as the source says. -/
noncomputable def relCondNumberOn (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), (‖G (d + δd) - G d‖ₑ / ‖G d‖ₑ) / (‖δd‖ₑ / ‖d‖ₑ)

/-- The relative condition number of $G$ at $d$ over the admissible perturbations of size less than
$\eta$: `Conditioning.relCondNumberOn` for the set `Conditioning.perturbations S d η` of the
$\delta d$ with $\|\delta d\| < \eta$ and $d + \delta d \in S$. -/
noncomputable def relCondNumberWithin (G : D → X) (S : Set D) (d : D) (η : ℝ) : ℝ≥0∞ :=
  relCondNumberOn G (perturbations S d η) d

/-- The **first-order relative condition number** of $G$ at $d$ on the admissible data $S$: the
infimum over $\eta > 0$ of `Conditioning.relCondNumberWithin G S d η`, which is its limit as
$\eta \to 0^+$. -/
noncomputable def relCondNumber (G : D → X) (S : Set D) (d : D) : ℝ≥0∞ :=
  ⨅ (η : ℝ) (_ : 0 < η), relCondNumberWithin G S d η

variable {G : D → X} {N S : Set D} {d δd : D}

/-- If $\delta d \in N$ and $\delta d \neq 0$, then $$\frac{\|G(d + \delta d) - G(d)\|}{\|\delta
d\|} \le K_{\mathrm{abs}}^N(d).$$
-/
theorem le_absCondNumberOn (hN : δd ∈ N) (h0 : δd ≠ 0) :
    ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ ≤ absCondNumberOn G N d :=
  le_iSup₂_of_le δd hN (le_iSup_of_le h0 le_rfl)

/-- Let $M \in [0, \infty]$. If $\|G(d + \delta d) - G(d)\| / \|\delta d\| \le M$ for every nonzero
$\delta d \in N$, then $K_{\mathrm{abs}}^N(d) \le M$. -/
theorem absCondNumberOn_le {M : ℝ≥0∞}
    (h : ∀ δd ∈ N, δd ≠ 0 → ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ ≤ M) : absCondNumberOn G N d ≤ M :=
  iSup₂_le fun δd hN => iSup_le fun h0 => h δd hN h0

/-- For every $\delta d \in N$, $$\|G(d + \delta d) - G(d)\| \le K_{\mathrm{abs}}^N(d) \, \|\delta
d\|$$ in $[0, \infty]$. This is the defining inequality of the condition number in product form;
the case $\delta d = 0$ is included. -/
theorem enorm_sub_le_absCondNumberOn_mul (hN : δd ∈ N) :
    ‖G (d + δd) - G d‖ₑ ≤ absCondNumberOn G N d * ‖δd‖ₑ := by
  by_cases h0 : δd = 0
  · simp [h0]
  · exact (ENNReal.div_le_iff (enorm_ne_zero.2 h0) enorm_ne_top).1 (le_absCondNumberOn hN h0)

/-- Let $K \ge 0$ be real. If $K_{\mathrm{abs}}^N(d) \le K$, then
$\|G(d + \delta d) - G(d)\| \le K \|\delta d\|$ for every $\delta d \in N$. So a finite bound on
the condition number is a Lipschitz bound on $G$ along the perturbations $N$ of $d$. -/
theorem norm_sub_le_of_absCondNumberOn_le {K : ℝ≥0} (hK : absCondNumberOn G N d ≤ K)
    (hN : δd ∈ N) : ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ := by
  have h := (enorm_sub_le_absCondNumberOn_mul hN).trans (mul_le_mul_left hK _)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul K.coe_nonneg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- Let $K \ge 0$ be real. If $\|G(d + \delta d) - G(d)\| \le K \|\delta d\|$ for every nonzero
$\delta d \in N$, then $K_{\mathrm{abs}}^N(d) \le K$. -/
theorem absCondNumberOn_le_of_forall_norm_sub_le {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ δd ∈ N, δd ≠ 0 → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖) :
    absCondNumberOn G N d ≤ ENNReal.ofReal K := by
  refine absCondNumberOn_le fun δd hN h0 => ?_
  rw [ENNReal.div_le_iff (enorm_ne_zero.2 h0) enorm_ne_top, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal (h δd hN h0)

/-- Let $K \ge 0$ be real. Then $K_{\mathrm{abs}}^N(d) \le K$ if and only if
$\|G(d + \delta d) - G(d)\| \le K \|\delta d\|$ for every $\delta d \in N$. -/
theorem absCondNumberOn_le_coe_iff {K : ℝ≥0} :
    absCondNumberOn G N d ≤ K ↔ ∀ δd ∈ N, ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ :=
  ⟨fun hK _ hN => norm_sub_le_of_absCondNumberOn_le hK hN, fun h =>
    ENNReal.ofReal_coe_nnreal ▸
      absCondNumberOn_le_of_forall_norm_sub_le K.coe_nonneg fun δd hN _ => h δd hN⟩

/-- The absolute condition number is monotone in the set of perturbations: if $N \subseteq N'$, then
$K_{\mathrm{abs}}^N(d) \le K_{\mathrm{abs}}^{N'}(d)$. -/
theorem absCondNumberOn_mono (G : D → X) (d : D) {N N' : Set D} (h : N ⊆ N') :
    absCondNumberOn G N d ≤ absCondNumberOn G N' d :=
  absCondNumberOn_le fun _ hN h0 => le_absCondNumberOn (h hN) h0

/-- The absolute condition number $K_{\mathrm{abs}}(d, \eta)$ over the admissible perturbations of
size less than $\eta$ is a monotone function of $\eta$. -/
theorem monotone_absCondNumberWithin (G : D → X) (S : Set D) (d : D) :
    Monotone (absCondNumberWithin G S d) := fun _ _ hη =>
  absCondNumberOn_mono G d fun _ ⟨h1, h2⟩ => ⟨h1.trans_le hη, h2⟩

/-- For every $\eta > 0$, the first-order absolute condition number is at most the condition number
over the perturbations of size less than $\eta$: $K_{\mathrm{abs}}(d) \le K_{\mathrm{abs}}(d,
\eta)$. -/
theorem absCondNumber_le_absCondNumberWithin (G : D → X) (S : Set D) (d : D) {η : ℝ} (hη : 0 < η) :
    absCondNumber G S d ≤ absCondNumberWithin G S d η :=
  iInf₂_le η hη

/-- The first-order absolute condition number is the limit of the condition numbers over shrinking
radii: $$K_{\mathrm{abs}}(d, \eta) \to K_{\mathrm{abs}}(d) \quad \text{as } \eta \to 0^+.$$
-/
theorem tendsto_absCondNumberWithin (G : D → X) (S : Set D) (d : D) :
    Tendsto (absCondNumberWithin G S d) (𝓝[>] 0) (𝓝 (absCondNumber G S d)) := by
  have h := (monotone_absCondNumberWithin G S d).tendsto_nhdsGT 0
  rw [sInf_image] at h
  exact h

/-- The **Lipschitz condition (2.3) of [quarteroni2000numerical] is the finiteness of the condition
number**. For every real $\eta$, $K_{\mathrm{abs}}(d, \eta) \neq \infty$ if and only if there is
a real $K$ such that $$\|G(d + \delta d) - G(d)\| \le K \|\delta d\|$$ for every $\delta d$ with
$\|\delta d\| < \eta$ and $d + \delta d \in S$. -/
theorem absCondNumberWithin_ne_top_iff (G : D → X) (S : Set D) (d : D) (η : ℝ) :
    absCondNumberWithin G S d η ≠ ⊤ ↔
      ∃ K : ℝ, ∀ δd, ‖δd‖ < η → d + δd ∈ S → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖ := by
  constructor
  · intro h
    refine ⟨(absCondNumberWithin G S d η).toNNReal, fun δd h1 h2 => ?_⟩
    exact norm_sub_le_of_absCondNumberOn_le (ENNReal.coe_toNNReal h).ge ⟨h1, h2⟩
  · rintro ⟨K, hK⟩
    refine ne_top_of_le_ne_top ENNReal.coe_ne_top
      ((absCondNumberOn_le_coe_iff (K := K.toNNReal)).2 fun δd hδd => ?_)
    exact (hK δd hδd.1 hδd.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _))

/-- Let $\eta > 0$. If $K_{\mathrm{abs}}(d, \eta) \neq \infty$, then $G$ is continuous at $d$ within
the admissible data $S$. -/
theorem continuousWithinAt_of_absCondNumberWithin_ne_top {η : ℝ} (hη : 0 < η)
    (h : absCondNumberWithin G S d η ≠ ⊤) : ContinuousWithinAt G S d := by
  obtain ⟨K, hK⟩ := (absCondNumberWithin_ne_top_iff G S d η).1 h
  refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨min η (ε / (max K 0 + 1)), by positivity,
    fun y hy hyd => ?_⟩
  have h1 : ‖y - d‖ < η := (dist_eq_norm y d ▸ hyd).trans_le (min_le_left _ _)
  have h2 : ‖y - d‖ ≤ ε / (max K 0 + 1) := (dist_eq_norm y d ▸ hyd).le.trans (min_le_right _ _)
  have h3 := hK (y - d) h1 (by simpa using hy)
  rw [add_sub_cancel] at h3
  rw [dist_eq_norm]
  calc ‖G y - G d‖ ≤ max K 0 * ‖y - d‖ :=
        h3.trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))
    _ ≤ max K 0 * (ε / (max K 0 + 1)) := mul_le_mul_of_nonneg_left h2 (le_max_right K 0)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [le_max_right K 0]

/-- For every set $N$ of perturbations, the relative condition number is the absolute one rescaled:
$$K^N(d) = K_{\mathrm{abs}}^N(d) \cdot \frac{\|d\|}{\|G(d)\|},$$ with the arithmetic of
$[0, \infty]$. No hypothesis on $d$ or $G(d)$ is needed. -/
theorem relCondNumberOn_eq (G : D → X) (N : Set D) (d : D) :
    relCondNumberOn G N d = absCondNumberOn G N d * (‖d‖ₑ / ‖G d‖ₑ) := by
  simp only [relCondNumberOn, absCondNumberOn, ENNReal.iSup_mul]
  refine iSup_congr fun δd => iSup_congr fun _ => iSup_congr fun h0 => ?_
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (enorm_ne_zero.2 h0)) (Or.inl enorm_ne_top), inv_inv]
  ring

/-- Let $d \neq 0$ and $G(d) \neq 0$. Then the first-order relative condition number is the
first-order absolute one rescaled: $$K(d) = K_{\mathrm{abs}}(d) \cdot \frac{\|d\|}{\|G(d)\|}.$$
-/
theorem relCondNumber_eq (G : D → X) (S : Set D) {d : D} (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = absCondNumber G S d * (‖d‖ₑ / ‖G d‖ₑ) := by
  have h0 : ‖d‖ₑ / ‖G d‖ₑ ≠ 0 := (ENNReal.div_pos (enorm_ne_zero.2 hd) enorm_ne_top).ne'
  have ht : ‖d‖ₑ / ‖G d‖ₑ ≠ ⊤ := (ENNReal.div_lt_top enorm_ne_top (enorm_ne_zero.2 hx)).ne
  simp only [relCondNumber, absCondNumber, relCondNumberWithin, absCondNumberWithin,
    relCondNumberOn_eq, ENNReal.iInf_mul_of_ne h0 ht]

/-! ### The first-order formula -/

section FirstOrder

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 D] [NormedSpace 𝕜 X]

/-- Let $D$ and $X$ be normed spaces over a nontrivially normed field. If $G$ has the Fréchet
derivative $G'$ at $d$, $S$ is a neighbourhood of $d$ and $\eta > 0$, then $$\|G'\| \le
K_{\mathrm{abs}}(d, \eta).$$

So the first-order number of (2.7) in [quarteroni2000numerical] can underestimate the condition
number over a fixed radius, as the example $G(d) = \cos d - 1$ of the source shows. -/
theorem enorm_fderiv_le_absCondNumberWithin {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) {η : ℝ} (hη : 0 < η) : ‖G'‖ₑ ≤ absCondNumberWithin G S d η := by
  by_cases hA : absCondNumberWithin G S d η = ⊤
  · exact hA ▸ le_top
  have hAK : absCondNumberWithin G S d η ≤ (absCondNumberWithin G S d η).toNNReal :=
    (ENNReal.coe_toNNReal hA).ge
  have hlip : ∀ᶠ x in 𝓝 d,
      ‖G x - G d‖ ≤ (absCondNumberWithin G S d η).toNNReal * ‖x - d‖ := by
    filter_upwards [hS, Metric.ball_mem_nhds d hη] with x hxS hxd
    have h := norm_sub_le_of_absCondNumberOn_le hAK (δd := x - d)
      ⟨by simpa [dist_eq_norm] using hxd, by simpa using hxS⟩
    rwa [add_sub_cancel] at h
  calc ‖G'‖ₑ = ENNReal.ofReal ‖G'‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ((absCondNumberWithin G S d η).toNNReal : ℝ) :=
        ENNReal.ofReal_le_ofReal (hG.le_of_lip' (NNReal.coe_nonneg _) hlip)
    _ = absCondNumberWithin G S d η := by rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal hA]

/-- The **first-order formula** (2.7) of [quarteroni2000numerical], absolute form. Let $D$ and $X$
be normed spaces over a nontrivially normed field. If the resolvent $G$ has the Fréchet
derivative $G'$ at $d$ and the admissible set $S$ is a neighbourhood of $d$, then the
first-order absolute condition number is the operator norm of the derivative:
$$K_{\mathrm{abs}}(d) = \|G'\|.$$
-/
theorem absCondNumber_eq_enorm_fderiv {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) : absCondNumber G S d = ‖G'‖ₑ := by
  refine le_antisymm ?_ (le_iInf₂ fun η hη => enorm_fderiv_le_absCondNumberWithin hG hS hη)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlo := isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hG) (NNReal.coe_pos.2 hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hlo
  calc absCondNumber G S d ≤ absCondNumberWithin G S d δ :=
        absCondNumber_le_absCondNumberWithin G S d hδ
    _ ≤ ENNReal.ofReal (‖G'‖ + ε) := by
        refine absCondNumberOn_le_of_forall_norm_sub_le (by positivity) fun δd hδd _ => ?_
        have h1 := hball (y := δd) (by simpa [dist_eq_norm] using hδd.1)
        calc ‖G (d + δd) - G d‖ = ‖G' δd + (G (d + δd) - G d - G' δd)‖ := by congr 1; abel
          _ ≤ ‖G' δd‖ + ‖G (d + δd) - G d - G' δd‖ := norm_add_le _ _
          _ ≤ ‖G'‖ * ‖δd‖ + ε * ‖δd‖ := add_le_add (G'.le_opNorm δd) h1
          _ = (‖G'‖ + ε) * ‖δd‖ := by ring
    _ = ‖G'‖ₑ + ε := by
        rw [ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg, ofReal_norm,
          ENNReal.ofReal_coe_nnreal]

/-- The **first-order formula** (2.7) of [quarteroni2000numerical], relative form. Let $D$ and $X$
be normed spaces over a nontrivially normed field. If $G$ has the Fréchet derivative $G'$ at
$d$, $S$ is a neighbourhood of $d$, $d \neq 0$ and $G(d) \neq 0$, then $$K(d) = \|G'\| \,
\frac{\|d\|}{\|G(d)\|}.$$
-/
theorem relCondNumber_eq_enorm_fderiv {G' : D →L[𝕜] X} (hG : HasFDerivAt G G' d)
    (hS : S ∈ 𝓝 d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = ‖G'‖ₑ * (‖d‖ₑ / ‖G d‖ₑ) := by
  rw [relCondNumber_eq G S hd hx, absCondNumber_eq_enorm_fderiv hG hS]

/-! ### Instance: linear problems -/

/-- Let $L : D \to X$ be a bounded linear map. If $S$ is a neighbourhood of $d$ and $\eta > 0$, then
$K_{\mathrm{abs}}(d, \eta) = \|L\|$ for the resolvent $L$.

The quotient $\|L \delta d\| / \|\delta d\|$ does not change when $\delta d$ is scaled, so its
supremum over any ball is the operator norm. -/
theorem absCondNumberWithin_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) {η : ℝ}
    (hη : 0 < η) : absCondNumberWithin L S d η = ‖L‖ₑ := by
  refine le_antisymm ?_ (enorm_fderiv_le_absCondNumberWithin L.hasFDerivAt hS hη)
  rw [← ofReal_norm]
  exact absCondNumberOn_le_of_forall_norm_sub_le (norm_nonneg L) fun δd _ _ => by
    simpa using L.le_opNorm δd

/-- Let $L : D \to X$ be a bounded linear map. If $S$ is a neighbourhood of $d$, then the
first-order absolute condition number of the resolvent $L$ at $d$ is $\|L\|$. -/
theorem absCondNumber_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) :
    absCondNumber L S d = ‖L‖ₑ :=
  absCondNumber_eq_enorm_fderiv L.hasFDerivAt hS

/-- Let $L : D \to X$ be a bounded linear map. If $S$ is a neighbourhood of $d$ and $\eta > 0$, then
the relative condition number of the resolvent $L$ over the perturbations of size less than
$\eta$ is $$K(d, \eta) = \|L\| \, \frac{\|d\|}{\|L d\|}.$$
-/
theorem relCondNumberWithin_continuousLinearMap (L : D →L[𝕜] X) (hS : S ∈ 𝓝 d) {η : ℝ}
    (hη : 0 < η) : relCondNumberWithin L S d η = ‖L‖ₑ * (‖d‖ₑ / ‖L d‖ₑ) := by
  rw [relCondNumberWithin, relCondNumberOn_eq, ← absCondNumberWithin,
    absCondNumberWithin_continuousLinearMap L hS hη]

/-- **Conditioning of a linear system with respect to its right-hand side.** Let $A : E \to F$ be an
isomorphism of normed spaces over a nontrivially normed field, and let $b \in F$ with
$b \neq 0$. The problem $Ax = b$, perturbed in $b$ only, has the resolvent $A^{-1}$, and its
first-order relative condition number on the admissible data $F$ satisfies $$K(b) = \|A^{-1}\|
\, \frac{\|b\|}{\|A^{-1} b\|} \le \|A\| \|A^{-1}\| = \kappa(A).$$ This is (2.9) of Example 2.3
of [quarteroni2000numerical].

The Lean statement is the inequality $K(b) \le \kappa(A)$. The condition number $\kappa(A)$ is
`ContinuousLinearEquiv.condNumber`. -/
theorem relCondNumber_symm_le_condNumber {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (A : E ≃L[𝕜] F) {b : F} (hb : b ≠ 0) :
    relCondNumber A.symm univ b ≤ ENNReal.ofReal A.condNumber := by
  have hAb : A.symm b ≠ 0 := by simpa using hb
  have hle : ‖b‖ₑ / ‖A.symm b‖ₑ ≤ ‖(A : E →L[𝕜] F)‖ₑ := by
    rw [ENNReal.div_le_iff (enorm_ne_zero.2 hAb) enorm_ne_top, ← ofReal_norm, ← ofReal_norm,
      ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by simpa using (A : E →L[𝕜] F).le_opNorm (A.symm b))
  calc relCondNumber A.symm univ b = ‖(A.symm : F →L[𝕜] E)‖ₑ * (‖b‖ₑ / ‖A.symm b‖ₑ) := by
        rw [relCondNumber_eq _ _ hb hAb, absCondNumber_eq_enorm_fderiv A.symm.hasFDerivAt univ_mem]
    _ ≤ ‖(A.symm : F →L[𝕜] E)‖ₑ * ‖(A : E →L[𝕜] F)‖ₑ := mul_le_mul_right hle _
    _ = ENNReal.ofReal A.condNumber := by
        rw [ContinuousLinearEquiv.condNumber, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ofReal_norm, mul_comm]

end FirstOrder

/-! ### The scaled relative condition number -/

section Scaled

/-- The **scaled relative condition number** of $G$ at $d$, after
$\operatorname{cond}_{\mathrm{rel}}$ of [golub2013matrix], §9.1.6: $$\limsup_{\varepsilon \to
0^+} \ \sup_{\|\delta d\| \le \varepsilon \|d\|} \frac{\|G(d + \delta d) - G(d)\|}{\varepsilon
\|G(d)\|} \in [0, \infty].$$

The source writes a limit; the definition uses the upper limit in $[0, \infty]$, which always
exists. The number is normalized by the radius $\varepsilon$ of the ball of relative
perturbations, not by the size of each perturbation as in `Conditioning.relCondNumber`. For a
resolvent that is differentiable at $d$ the two agree
(`Conditioning.scaledRelCondNumber_eq_relCondNumber`). -/
noncomputable def scaledRelCondNumber (G : D → X) (d : D) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => ⨆ (δd : D) (_ : ‖δd‖ ≤ ε * ‖d‖),
    ‖G (d + δd) - G d‖ₑ / (ENNReal.ofReal ε * ‖G d‖ₑ)) (𝓝[>] 0)

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 D] [NormedSpace 𝕜 X] {G' : D →L[𝕜] X}

/-- If $G$ has the Fréchet derivative $G'$ at $d$ and $c > 0$, then for all small $\varepsilon > 0$
every $\delta d$ with $\|\delta d\| \le \varepsilon \|d\|$ satisfies $\|G(d + \delta d) - G(d) -
G' \delta d\| \le c \|\delta d\|$. -/
private theorem eventually_norm_remainder_le (hG : HasFDerivAt G G' d) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ δd : D, ‖δd‖ ≤ ε * ‖d‖ →
      ‖G (d + δd) - G d - G' δd‖ ≤ c * ‖δd‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hG).def hc
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp h
  have hd' : 0 < ‖d‖ + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / (‖d‖ + 1) by positivity)] with ε hε δd hδd
  refine hball ?_
  rw [dist_zero_right]
  calc ‖δd‖ ≤ ε * ‖d‖ := hδd
    _ ≤ ε * (‖d‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.1.le
    _ < ρ := (lt_div_iff₀ hd').mp hε.2

/-- If $G$ has the Fréchet derivative $G'$ at $d$, $G(d) \neq 0$ and $c > 0$, then for all small
$\varepsilon > 0$ the supremum in `Conditioning.scaledRelCondNumber` is at most
$(\|G'\| + c) \|d\| / \|G(d)\|$. -/
private theorem eventually_scaledRelCondNumber_le (hG : HasFDerivAt G G' d) (hGd : G d ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ (δd : D) (_ : ‖δd‖ ≤ ε * ‖d‖),
      ‖G (d + δd) - G d‖ₑ / (ENNReal.ofReal ε * ‖G d‖ₑ)) ≤
        ENNReal.ofReal ((‖G'‖ + c) * ‖d‖ / ‖G d‖) := by
  filter_upwards [eventually_norm_remainder_le hG hc, self_mem_nhdsWithin] with ε hR hε
  have hε0 : 0 < ε := hε
  refine iSup₂_le fun δd hδd => ENNReal.div_le_of_le_mul ?_
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hε0.le,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖G (d + δd) - G d‖ = ‖G' δd + (G (d + δd) - G d - G' δd)‖ := by congr 1; abel
    _ ≤ ‖G' δd‖ + ‖G (d + δd) - G d - G' δd‖ := norm_add_le _ _
    _ ≤ ‖G'‖ * ‖δd‖ + c * ‖δd‖ := add_le_add (G'.le_opNorm δd) (hR δd hδd)
    _ = (‖G'‖ + c) * ‖δd‖ := by ring
    _ ≤ (‖G'‖ + c) * (ε * ‖d‖) := by gcongr
    _ = (‖G'‖ + c) * ‖d‖ / ‖G d‖ * (ε * ‖G d‖) := by field_simp

/-- If $G$ has the Fréchet derivative $G'$ at $d$, $G(d) \neq 0$ and $c > 0$, then for all small
$\varepsilon > 0$ the supremum in `Conditioning.scaledRelCondNumber` is at least
$(\|G'\| - c) \|d\| / \|G(d)\|$; the proof scales a direction that nearly attains $\|G'\|$ to
the radius $\varepsilon \|d\|$. -/
private theorem eventually_le_scaledRelCondNumber (hG : HasFDerivAt G G' d) (hGd : G d ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((‖G'‖ - c) * ‖d‖ / ‖G d‖) ≤
      ⨆ (δd : D) (_ : ‖δd‖ ≤ ε * ‖d‖), ‖G (d + δd) - G d‖ₑ / (ENNReal.ofReal ε * ‖G d‖ₑ) := by
  have hφ : 0 < ‖G d‖ := norm_pos_iff.mpr hGd
  rcases le_or_gt ‖G'‖ c with hLc | hLc
  · refine Eventually.of_forall fun ε => ?_
    rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (norm_nonneg _)) (norm_nonneg _))]
    exact zero_le
  obtain ⟨x, hx1, hx⟩ := G'.exists_lt_apply_of_lt_opNorm (show ‖G'‖ - c / 2 < ‖G'‖ by linarith)
  filter_upwards [eventually_norm_remainder_le hG (half_pos hc), self_mem_nhdsWithin]
    with ε hR hε
  have hε0 : 0 < ε := hε
  have hεd : 0 ≤ ε * ‖d‖ := by positivity
  set δd : D := ((ε * ‖d‖ : ℝ) : 𝕜) • x with hδdef
  have hδn : ‖δd‖ = ε * ‖d‖ * ‖x‖ := by
    rw [hδdef, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hεd]
  have hδ : ‖δd‖ ≤ ε * ‖d‖ := by
    rw [hδn]
    exact mul_le_of_le_one_right hεd hx1.le
  have hLδ : ‖G' δd‖ = ε * ‖d‖ * ‖G' x‖ := by
    rw [hδdef, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hεd]
  have hsub : ‖G' δd‖ ≤ ‖G (d + δd) - G d‖ + ‖G (d + δd) - G d - G' δd‖ := by
    calc ‖G' δd‖ = ‖(G (d + δd) - G d) - (G (d + δd) - G d - G' δd)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h3 : ε * ‖d‖ * (‖G'‖ - c / 2) ≤ ε * ‖d‖ * ‖G' x‖ := mul_le_mul_of_nonneg_left hx.le hεd
  have h4 : c / 2 * ‖δd‖ ≤ c / 2 * (ε * ‖d‖) := mul_le_mul_of_nonneg_left hδ (by positivity)
  have hmain : (‖G'‖ - c) * ‖d‖ / ‖G d‖ * (ε * ‖G d‖) ≤ ‖G (d + δd) - G d‖ := by
    have : (‖G'‖ - c) * ‖d‖ / ‖G d‖ * (ε * ‖G d‖) = ε * ‖d‖ * (‖G'‖ - c) := by
      field_simp
    rw [this]
    nlinarith [hR δd hδ]
  refine le_iSup₂_of_le δd hδ ?_
  have hden0 : ENNReal.ofReal ε * ‖G d‖ₑ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hε0).ne' (enorm_ne_zero.mpr hGd)
  have hdent : ENNReal.ofReal ε * ‖G d‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent), ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul hε0.le,
    ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) hφ.le)]
  exact ENNReal.ofReal_le_ofReal hmain

/-- **The scaled relative condition number is a normalized Fréchet derivative.** Let $D$ and $X$ be
normed spaces over $\mathbb{R}$ or $\mathbb{C}$. If $G$ has the Fréchet derivative $G'$ at $d$,
$d \neq 0$ and $G(d) \neq 0$, then $$\operatorname{cond}_{\mathrm{rel}}(G, d) = \frac{\|G'\|
\|d\|}{\|G(d)\|}.$$ Here $\operatorname{cond}_{\mathrm{rel}}$ is
`Conditioning.scaledRelCondNumber`.

This makes precise the remark of [golub2013matrix], §9.1.6, that the relative condition number
is "essentially a normalized Fréchet derivative". -/
theorem scaledRelCondNumber_eq_of_hasFDerivAt (hG : HasFDerivAt G G' d) (hd : d ≠ 0)
    (hGd : G d ≠ 0) : scaledRelCondNumber G d = ‖G'‖ₑ * ‖d‖ₑ / ‖G d‖ₑ := by
  have hφ : 0 < ‖G d‖ := norm_pos_iff.mpr hGd
  have hC : ‖G'‖ₑ * ‖d‖ₑ / ‖G d‖ₑ = ENNReal.ofReal (‖G'‖ * ‖d‖ / ‖G d‖) := by
    rw [ENNReal.ofReal_div_of_pos hφ, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
      ofReal_norm, ofReal_norm]
  rw [hC]
  refine Tendsto.limsup_eq (tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩)
  · have hbt : b ≠ ⊤ := ne_top_of_lt hb
    have hb' : b.toReal < ‖G'‖ * ‖d‖ / ‖G d‖ := (ENNReal.lt_ofReal_iff_toReal_lt hbt).mp hb
    have hc : 0 < (‖G'‖ * ‖d‖ / ‖G d‖ - b.toReal) * ‖G d‖ / (2 * ‖d‖) :=
      div_pos (mul_pos (sub_pos.mpr hb') hφ) (by positivity)
    filter_upwards [eventually_le_scaledRelCondNumber hG hGd hc] with ε hε
    refine lt_of_lt_of_le ?_ hε
    rw [ENNReal.lt_ofReal_iff_toReal_lt hbt]
    have : (‖G'‖ - (‖G'‖ * ‖d‖ / ‖G d‖ - b.toReal) * ‖G d‖ / (2 * ‖d‖)) * ‖d‖ / ‖G d‖ =
        ‖G'‖ * ‖d‖ / ‖G d‖ - (‖G'‖ * ‖d‖ / ‖G d‖ - b.toReal) / 2 := by
      field_simp
    rw [this]
    linarith
  · by_cases hbt : b = ⊤
    · filter_upwards [eventually_scaledRelCondNumber_le hG hGd one_pos] with ε hε
      exact lt_of_le_of_lt hε (hbt ▸ ENNReal.ofReal_lt_top)
    · have hb' : ‖G'‖ * ‖d‖ / ‖G d‖ < b.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbt).mp hb
      have hc : 0 < (b.toReal - ‖G'‖ * ‖d‖ / ‖G d‖) * ‖G d‖ / (2 * ‖d‖) :=
        div_pos (mul_pos (sub_pos.mpr hb') hφ) (by positivity)
      filter_upwards [eventually_scaledRelCondNumber_le hG hGd hc] with ε hε
      refine lt_of_le_of_lt hε ?_
      rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hbt]
      have : (‖G'‖ + (b.toReal - ‖G'‖ * ‖d‖ / ‖G d‖) * ‖G d‖ / (2 * ‖d‖)) * ‖d‖ / ‖G d‖ =
          ‖G'‖ * ‖d‖ / ‖G d‖ + (b.toReal - ‖G'‖ * ‖d‖ / ‖G d‖) / 2 := by
        field_simp
      rw [this]
      linarith

/-- **The two relative condition numbers agree at a point of differentiability.** Let $D$ and $X$ be
normed spaces over $\mathbb{R}$ or $\mathbb{C}$. If $G$ has the Fréchet derivative $G'$ at $d$,
the admissible set $S$ is a neighbourhood of $d$, $d \neq 0$ and $G(d) \neq 0$, then the scaled
relative condition number $\operatorname{cond}_{\mathrm{rel}}$ of [golub2013matrix], §9.1.6,
equals the first-order relative condition number $K(d)$ of (2.7) of [quarteroni2000numerical].

Both are equal to $\|G'\| \|d\| / \|G(d)\|$, by
`Conditioning.scaledRelCondNumber_eq_of_hasFDerivAt` and
`Conditioning.relCondNumber_eq_enorm_fderiv`. -/
theorem scaledRelCondNumber_eq_relCondNumber (hG : HasFDerivAt G G' d) (hS : S ∈ 𝓝 d)
    (hd : d ≠ 0) (hGd : G d ≠ 0) : scaledRelCondNumber G d = relCondNumber G S d := by
  rw [scaledRelCondNumber_eq_of_hasFDerivAt hG hd hGd, relCondNumber_eq_enorm_fderiv hG hS hd hGd,
    mul_div_assoc]

end Scaled

/-! ### Instance: roots of functions -/

section Roots

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **Conditioning of a simple root.** Let $\varphi, G : \mathbb{K} \to \mathbb{K}$ for a
nontrivially normed field $\mathbb{K}$, and let $d \in \mathbb{K}$. Suppose that $G$ is
continuous at $d$, that $\varphi(G(y)) = y$ for all $y$ near $d$ (so $G(y)$ is a root of
$\varphi(x) = y$), and that $\varphi$ has the strict derivative $\varphi' \neq 0$ at $G(d)$.
Then the root depends on the datum with first-order absolute condition number
$$K_{\mathrm{abs}}(d) = \|\varphi'\|^{-1},$$ on the admissible data $\mathbb{K}$.

This is (2.11) of Example 2.4 of [quarteroni2000numerical], the example behind §6.1 of the
source. -/
theorem absCondNumber_of_local_left_inverse {φ G : 𝕜 → 𝕜} {φ' d : 𝕜} (hG : ContinuousAt G d)
    (hφ : HasStrictDerivAt φ φ' (G d)) (hφ' : φ' ≠ 0) (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) :
    absCondNumber G univ d = ‖φ'‖ₑ⁻¹ := by
  rw [absCondNumber_eq_enorm_fderiv
    (HasStrictDerivAt.of_local_left_inverse hG hφ hφ' hinv).hasDerivAt.hasFDerivAt univ_mem,
    ← enorm_inv hφ', ← ofReal_norm, ← ofReal_norm]
  simp

/-- **Relative conditioning of a simple root.** Under the hypotheses of
`Conditioning.absCondNumber_of_local_left_inverse`, if moreover $d \neq 0$ and $G(d) \neq 0$,
then the first-order relative condition number on the admissible data $\mathbb{K}$ is $$K(d) =
\|\varphi'\|^{-1} \, \frac{\|d\|}{\|G(d)\|}.$$ This is (2.10) of Example 2.4 of
[quarteroni2000numerical]. -/
theorem relCondNumber_of_local_left_inverse {φ G : 𝕜 → 𝕜} {φ' d : 𝕜} (hG : ContinuousAt G d)
    (hφ : HasStrictDerivAt φ φ' (G d)) (hφ' : φ' ≠ 0) (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y)
    (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ‖φ'‖ₑ⁻¹ * (‖d‖ₑ / ‖G d‖ₑ) := by
  rw [relCondNumber_eq G univ hd hx, absCondNumber_of_local_left_inverse hG hφ hφ' hinv]

variable [NormedSpace 𝕜 D] [NormedSpace 𝕜 X]

/-- **A multiple root is infinitely ill conditioned**, Fréchet form. Let $D$ and $X$ be normed
spaces over a nontrivially normed field, let $\varphi : X \to D$, $S \subseteq D$ and $d \in D$,
and suppose that $d$ is an accumulation point of $S$. Suppose that $G$ is continuous at $d$
within $S$, that $\varphi(G(y)) = y$ for all $y \in S$ near $d$, and that $\varphi$ has the
Fréchet derivative $0$ at $G(d)$. Then $K_{\mathrm{abs}}(d) = \infty$ on the admissible data
$S$.

The reason is that $\|y - d\| = \|\varphi(G(y)) - \varphi(G(d))\| = o(\|G(y) - G(d)\|)$, so the
amplification quotient is unbounded on every ball. The theorem is stated within $S$, not on the
whole space, so that it covers one-sided roots, such as the double root at $p = 1$ of
$x^2 - 2px + 1$, whose resolvent exists only for $p \ge 1$ (Remark 2.1 of
[quarteroni2000numerical]). The source calls such a root "ill posed"; the problem can still be
well posed (have a continuous resolvent), and the statement here is infinite conditioning. -/
theorem absCondNumber_eq_top_of_fderiv_eq_zero {φ : X → D} [NeBot (𝓝[S \ {d}] d)]
    (hG : ContinuousWithinAt G S d) (hφ : HasFDerivAt φ (0 : X →L[𝕜] D) (G d))
    (hinv : ∀ᶠ y in 𝓝[S] d, φ (G y) = y) : absCondNumber G S d = ⊤ := by
  have hle : 𝓝[S \ {d}] d ≤ 𝓝[S] d := nhdsWithin_mono _ sdiff_subset
  have hinv' : ∀ᶠ y in 𝓝[S \ {d}] d, φ (G y) = y := hinv.filter_mono hle
  have hT : Tendsto G (𝓝[S \ {d}] d) (𝓝 (G d)) := hG.tendsto.mono_left hle
  have hφd : φ (G d) = d :=
    tendsto_nhds_unique (hφ.continuousAt.tendsto.comp hT)
      ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (hinv'.mono fun _ hy => hy.symm))
  simp only [absCondNumber, iInf_eq_top]
  intro η hη
  refine ENNReal.eq_top_of_forall_nnreal_le fun M => ?_
  have hε : (0 : ℝ) < ((M : ℝ) + 1)⁻¹ := by positivity
  have h1 : ∀ᶠ x in 𝓝 (G d), ‖φ x - φ (G d)‖ ≤ ((M : ℝ) + 1)⁻¹ * ‖x - G d‖ := by
    simpa using isLittleO_iff.1 (hasFDerivAt_iff_isLittleO.1 hφ) hε
  have h2 : ∀ᶠ y in 𝓝[S \ {d}] d, ‖y - d‖ ≤ ((M : ℝ) + 1)⁻¹ * ‖G y - G d‖ := by
    filter_upwards [hT.eventually h1, hinv'] with y hy hy'
    rwa [hy', hφd] at hy
  have h3 : ∀ᶠ y in 𝓝[S \ {d}] d, ‖y - d‖ < η :=
    (Metric.eventually_nhds_iff.2 ⟨η, hη, fun y hy => dist_eq_norm y d ▸ hy⟩).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨y, hyS, hy1, hy2⟩ := (eventually_mem_nhdsWithin.and (h2.and h3)).exists
  have hyd : y - d ≠ 0 := sub_ne_zero.2 hyS.2
  have h4 := le_absCondNumberOn (G := G) (N := perturbations S d η) (d := d) (δd := y - d)
    ⟨hy2, by simpa using hyS.1⟩ hyd
  rw [add_sub_cancel] at h4
  refine le_trans ?_ h4
  rw [ENNReal.le_div_iff_mul_le (Or.inl (enorm_ne_zero.2 hyd)) (Or.inl enorm_ne_top),
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul M.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hy1
  nlinarith [norm_nonneg (y - d)]

/-- **A multiple root is infinitely ill conditioned.** Let $\varphi, G : \mathbb{K} \to \mathbb{K}$
for a nontrivially normed field $\mathbb{K}$, let $S \subseteq \mathbb{K}$, and let $d$ be an
accumulation point of $S$. Suppose that $G$ is continuous at $d$ within $S$, that
$\varphi(G(y)) = y$ for all $y \in S$ near $d$, and that $\varphi'(G(d)) = 0$. Then
$K_{\mathrm{abs}}(d) = \infty$ on the admissible data $S$.

This is the statement of Example 2.4 of [quarteroni2000numerical] that the root problem is "ill
posed if $x$ is a multiple root", which §6.1 of the source uses. It is the scalar case of
`Conditioning.absCondNumber_eq_top_of_fderiv_eq_zero`. -/
theorem absCondNumber_eq_top_of_deriv_eq_zero {φ G : 𝕜 → 𝕜} {S : Set 𝕜} {d : 𝕜}
    [NeBot (𝓝[S \ {d}] d)] (hG : ContinuousWithinAt G S d) (hφ : HasDerivAt φ 0 (G d))
    (hinv : ∀ᶠ y in 𝓝[S] d, φ (G y) = y) : absCondNumber G S d = ⊤ :=
  absCondNumber_eq_top_of_fderiv_eq_zero hG (by simpa using hφ.hasFDerivAt) hinv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Conditioning of a root in Banach spaces.** Let $E$ be a Banach space and $F$ a normed space
over a nontrivially normed field, and let $\varphi : E \to F$ have at $x$ a strict Fréchet
derivative $\varphi'$ that is an isomorphism $E \to F$. Then the local inverse of $\varphi$ at
$x$ given by the inverse function theorem has, at the datum $\varphi(x)$ and on the admissible
data $F$, the first-order absolute condition number $$K_{\mathrm{abs}}(\varphi(x)) =
\|\varphi'^{-1}\|.$$

The local inverse is `HasStrictFDerivAt.localInverse`. -/
theorem absCondNumber_localInverse {φ : E → F} {φ' : E ≃L[𝕜] F} {x : E}
    (hφ : HasStrictFDerivAt φ (φ' : E →L[𝕜] F) x) :
    absCondNumber (hφ.localInverse φ φ' x) univ (φ x) = ‖(φ'.symm : F →L[𝕜] E)‖ₑ :=
  absCondNumber_eq_enorm_fderiv hφ.to_localInverse.hasFDerivAt univ_mem

end Roots

end Conditioning
