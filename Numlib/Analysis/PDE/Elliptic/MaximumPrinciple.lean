/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Calculus.DerivativeTest.Laplacian
import Numlib.Analysis.PDE.Elliptic.Dirichlet

/-!
# The maximum principle for second-order elliptic equations

This file proves the weak maximum principle of [brezis2011functional], §9.7, by Stampacchia's
truncation method. Let $\Omega \subseteq \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, and let
$u \in H^1(\Omega)$ be a weak solution of $-\Delta u + u = f$, that is, $\int_\Omega \nabla u \cdot
\nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi$ for every $\varphi$ in a test space
$V$. For the Dirichlet problem $V = H^1_0(\Omega)$, and for the Neumann problem $V = H^1(\Omega)$.
Theorem 9.27 states that if $u$ is continuous on $\bar\Omega$, then $\min\{\inf_\Gamma u,
\inf_\Omega f\} \le u \le \max\{\sup_\Gamma u, \sup_\Omega f\}$ on $\Omega$, where $\Gamma$ is the
boundary of $\Omega$, both for $|\Omega| < \infty$ and for $|\Omega| = \infty$. The file also proves
Corollary 9.28, Proposition 9.30 (the Neumann problem), and Proposition 9.29 for the general
operator $-\sum_{i,j} \partial_j(a_{ij} \partial_i u) + \sum_i a_i \partial_i u + a_0 u$ with
$a_0 \ge 0$: in the drift-free case $a_i = 0$ for every $N \ge 1$, and with a drift term for
$N \ge 3$.

The general case of Proposition 9.29 is quoted in the source from Gilbarg and Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Theorem 8.1, and the proof here follows that
theorem, with its Lemmas 7.6 and 7.7. Remark 27 of [brezis2011functional], the classical maximum
principle for solutions in $C(\bar\Omega) \cap C^2(\Omega)$ on a bounded $\Omega$, is also proved,
for the Laplacian and for a general operator. The forms and the weak solutions are those of
`Numlib.Analysis.PDE.Elliptic.Dirichlet`.

## Main definitions

* `Elliptic.levelGradSet`: the set $\{u > l\} \cap \{\nabla u \neq 0\}$ for $u \in H^1(\Omega)$ and
  $l \in \mathbb{R}$.

## Main results

* `Elliptic.le_of_forall_truncation_mem`: if $u$ solves the weak equation of $-\Delta + 1$ on a test
  space $V$, $f \le K$ almost everywhere, and $V$ contains the truncations $G(u - K')$ for $K' > K$,
  then $u \le K$ almost everywhere.
* `Elliptic.le_of_le_frontier`, `Elliptic.ge_of_ge_frontier`, `Elliptic.le_max_of_isWeakSolution`:
  Theorem 9.27 for the Dirichlet problem.
* `Elliptic.le_of_mem_zero`, `Elliptic.ge_of_mem_zero`: Theorem 9.27 for $u \in H^1_0(\Omega)$
  without a continuity hypothesis.
* `Elliptic.nonneg_of_nonneg_frontier`, `Elliptic.abs_le_max_of_isWeakSolution`: Corollary 9.28.
* `Elliptic.le_of_neumann`, `Elliptic.ge_of_neumann`: Proposition 9.30 for the Neumann problem.
* `Elliptic.nonneg_of_nonneg_frontier_general_zero_drift`,
  `Elliptic.mem_Icc_of_frontier_general_zero_drift`: Proposition 9.29 without a drift term, for
  $N \ge 1$.
* `Elliptic.nonneg_of_nonneg_frontier_general`, `Elliptic.mem_Icc_of_frontier_general`: Proposition
  9.29 with a drift term, for $N \ge 3$.
* `SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq`: the weak gradient of a $W^{1,p}$
  function vanishes almost everywhere on each level set.
* `Elliptic.le_of_classical_laplacian`, `Elliptic.le_of_classical`: the classical maximum principle
  of Remark 27.

## Proof outline

The proofs of Theorem 9.27, Corollary 9.28 and Proposition 9.30 use one argument,
`Elliptic.le_of_forall_truncation_mem`. Let $G$ be a Stampacchia truncation:
$G \in C^1(\mathbb{R})$, $|G'| \le M$, $G' \ge 0$, $G = 0$ on $(-\infty, 0]$ and $G > 0$ on
$(0, \infty)$. For $K' > K$ the function $v = G(u - K')$ lies in $H^1(\Omega)$ by the chain rule
(Proposition 9.5). If $v \in V$, the equation tested with $v$ gives $\sum_i \int (\partial_i u)^2
G'(u - K') + \int (u - f) G(u - K') = 0$. Since $f \le K < K'$, pointwise
$0 \le (u - K') G(u - K') \le (u - f) G(u - K')$, so $(u - K') G(u - K') = 0$ almost everywhere and
$u \le K'$; then $K' \downarrow K$. For the Dirichlet problem, $v \in H^1_0(\Omega)$ by Theorem
9.17, (i) implies (ii), which holds on every open set, because the continuous representative
$G(\tilde u - K')$ of $v$ vanishes on the boundary.

In the drift-free case of Proposition 9.29 the form has no term $\int uv$. The equation tested with
$G(u)$ gives $|\nabla u|^2 G'(u) = 0$, and then the function $H(t) = \int_0^t \sqrt{G'(s)}\,ds$
gives $H(u) \in H^1_0(\Omega)$ with $\nabla H(u) = 0$. Hence $H(u) = 0$ by footnote 39, and
$u \le 0$.

With a drift term $a_i$, the argument of Gilbarg and Trudinger tests the equation with
$v = (u - l)^+$ for a level $l \ge 0$ with $u \le l$ on $\Gamma$. This gives $\alpha \|\nabla
v\|_2^2 \le (\sum_i \|a_i\|_\infty) \|\nabla v\|_2 \|1_E v\|_2$ with
$E = \{u > l\} \cap \{\nabla u \neq 0\}$. The Sobolev inequality of Remark 20 and Hölder's
inequality on $E$ give $\|1_E v\|_2 \le C \|\nabla v\|_2 |E|^{1/N}$. So either $\nabla v = 0$, and
then $u \le l$, or $|E| \ge c$ for a $c > 0$ that does not depend on $l$. As $l$ rises to the least
almost-everywhere bound $M$ of $u$, the sets $E$ decrease to $\{u = M\} \cap \{\nabla u \neq 0\}$,
which is a null set. Hence $M \le 0$.

## Implementation notes

* The space $H^1(\Omega)$ is `SobolevEuclidean N 1 2 Ω`.
* The space $H^1_0(\Omega)$ is `SobolevEuclideanZero N 1 2 Ω`.
* A weak solution on the test space `V` is `Elliptic.IsWeakSolution (Elliptic.laplaceForm Ω) V u f`.
* The hypothesis $u \in C(\bar\Omega)$ is a function $\tilde u : \mathbb{R}^N \to \mathbb{R}$,
  continuous on `closure Ω`, with `SobolevMultiIndex.fn u =ᵐ[volume.restrict Ω] ũ`. The boundary
  values of $u$ are the values of $\tilde u$ on `frontier Ω`.
* The quantities $\sup_\Gamma u$ and $\sup_\Omega f$ of the source are not formed. A number $K$ with
  $\tilde u \le K$ on `frontier Ω` and $f \le K$ almost everywhere on $\Omega$ is the hypothesis,
  and $\tilde u \le K$ on $\Omega$ is the conclusion. The lower bounds are the upper bounds for
  $-u$, $-f$ and $-K$. Almost-everywhere bounds become bounds at every point of $\Omega$ by
  continuity (`Elliptic.forall_le_of_ae_le_of_continuousOn`).
* The concrete truncation is `stampacchiaTruncation`,
  $s \mapsto \int_0^s \min\{\max\{t, 0\}, 1\}\,dt$, and the class of truncations is
  `IsStampacchiaTruncation`. When $|\Omega| < \infty$, the element $G(u - K')$ of $H^1(\Omega)$ is
  built from $t \mapsto G(t - K') - G(-K')$ and the constant $G(-K')$. When $|\Omega| = \infty$, the
  bound $f \le K$ forces $K \ge 0$, and $t \mapsto G(t - K')$ vanishes at $0$.
* The proof compares $\int (u - K') G(u - K')$ with $\int (u - f) G(u - K')$, instead of subtracting
  $K' \int G(u - K')$. This avoids the integrability argument of footnote 36 of
  [brezis2011functional], §9.7.
* Footnotes 35, 37 and 38 of [brezis2011functional], §9.7, say that the hypothesis
  $u \in C(\bar\Omega)$ can be dropped for $u \in H^1_0(\Omega)$. These are the variants whose names
  end in `_of_mem_zero`, proved through `SobolevMultiIndexZero.contDiff_comp_mem`. The maximum
  principle for the heat equation in Chapter 10 of [brezis2011functional] uses them.
* In Proposition 9.29 the drift-free statements hold for every $N \ge 1$ and keep their own names
  (ending in `_zero_drift`). The statements with a drift term need $N \ge 3$. In the source, the
  reference "proceed as in the proof of Theorem 8.18" means Theorem 8.19.
* In the drift case, $(u - l)^+ \in H^1(\Omega)$ is `MemSobolevMultiIndex.posPart_sub_const`, the
  positive part after the shift $t \mapsto t - l$ (Lemma 7.6 of Gilbarg and Trudinger). The
  vanishing of the gradient on level sets is
  `SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq` (their Lemma 7.7).
* The classical proof of Remark 27 for a general operator needs $\sum_{i,j} a_{ij}(x_0) \partial_i
  \partial_j \tilde u(x_0) \le 0$. The source gets this by a change of coordinates that diagonalizes
  $(a_{ij}(x_0))$. Here `Matrix.PosSemidef.sum_mul_apply_single_nonpos` gets it from the positive
  semidefinite square root (`CFC.sqrt`).
* Proposition 9.29 and its consequences (79), (80), (81) with a drift term $a_i \neq 0$ in dimension
  $N \le 2$ are not formalized. The statements would be those of this file with $N \ge 3$ replaced
  by $N \ge 1$. The only step that fails is the Sobolev inequality $\|v\|_{L^{2^*}(\Omega)} \le C
  \|\nabla v\|_{L^2(\Omega)}$ on $H^1_0(\Omega)$ (Remark 20,
  `SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq`), which needs $N > 2$. The argument uses only
  the bound $\|v\|_{L^2(\Omega)} \le C_N \|\nabla v\|_{L^2(\Omega)} |\{v \neq 0\}|^{1/N}$ for
  $v \in H^1_0(\Omega)$. For $N = 2$ this would follow from the Sobolev inequality at the exponent
  $q = 3/2$ applied to the extension by zero, which needs the embedding
  $W^{1,2}_0(\Omega) \to W^{1,3/2}_0(\Omega)$ on a set of finite measure and a form of Remark 21
  (`SobolevEuclideanZero.exists_eLpNorm_fn_le_sum_of_measure_ne_top`) with an explicit constant. For
  $N = 1$ it would need $\|v\|_\infty \le \|v'\|_{L^1}$ on $W^{1,1}_0$ of an open subset of
  $\mathbb{R}$, which the library has only for a different model of $\mathbb{R}^1$. Gilbarg and
  Trudinger state Theorem 8.1 for a bounded domain and treat $n = 2$ by replacing $2^*$ with an
  arbitrary $q < \infty$. [brezis2011functional] gives no proof of the case with a drift term.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal NNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

/-! ### Almost everywhere bounds of continuous functions, and the negation of the data -/

section Aux

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be
continuous on $\Omega$. If $\tilde u \le K$ almost everywhere on $\Omega$, then
$\tilde u(x) \le K$ for every $x \in \Omega$.

The functions $\max\{\tilde u, K\}$ and $K$ are continuous on $\Omega$ and agree almost
everywhere, so they agree on $\Omega$ (`MeasureTheory.Measure.eqOn_open_of_ae_eq`). -/
theorem forall_le_of_ae_le_of_continuousOn {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hc : ContinuousOn ũ Ω) {K : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), ũ x ≤ K) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have e := Measure.eqOn_open_of_ae_eq (μ := volume) (f := fun x ↦ max (ũ x) K) (g := fun _ ↦ K)
    (by filter_upwards [h] with x hx; exact max_eq_right hx) Ω.isOpen
    (continuous_max.comp_continuousOn (hc.prodMk continuousOn_const)) continuousOn_const
  intro x hx
  have : max (ũ x) K = K := e hx
  rw [← this]
  exact le_max_left _ _

/-- For $u \in H^1(\Omega)$, the function of $-u$ is $-u$: `SobolevMultiIndex.fn (-u)` equals
`-SobolevMultiIndex.fn u` almost everywhere on $\Omega$. -/
theorem _root_.SobolevMultiIndex.fn_neg (u : SobolevEuclidean N 1 2 Ω) :
    fn (-u) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] -fn u :=
  Lp.coeFn_neg (weakDeriv u 0)

/-- The form $a(u, \varphi) = \int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi$ of
$-\Delta + 1$ satisfies $a(-u, \varphi) = -a(u, \varphi)$ for $u, \varphi \in H^1(\Omega)$. -/
theorem laplaceForm_neg_apply (u φ : SobolevEuclidean N 1 2 Ω) :
    laplaceForm Ω (-u) φ = -laplaceForm Ω u φ :=
  ContinuousLinearMap.map_neg₂ _ u φ

/-- The load functional of $-f$ is the negative of that of $f$: $\int_\Omega (-f) \varphi =
-\int_\Omega f \varphi$ for $f \in L^2(\Omega)$ and $\varphi \in H^1(\Omega)$. -/
theorem load_neg_apply (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (φ : SobolevEuclidean N 1 2 Ω) : load Ω (-f) φ = -load Ω f φ := by
  rw [load_apply_inner, load_apply_inner, inner_neg_left]

/-- If $u \in H^1(\Omega)$ is a weak solution of $-\Delta u + u = f$ with test space $V$, then $-u$
is a weak solution of $-\Delta(-u) + (-u) = -f$ with the same test space. -/
theorem forall_laplaceForm_neg_eq_load_neg (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) V u f) :
    IsWeakSolution (laplaceForm Ω) V (-u) (-f) := fun φ hφ ↦ by
  rw [laplaceForm_neg_apply, load_neg_apply, heq φ hφ]

/-- If $K \le f$ almost everywhere on $\Omega$, then $-f \le -K$ almost everywhere on $\Omega$. -/
theorem ae_neg_le_neg {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), (-f) x ≤ -K := by
  filter_upwards [hf, Lp.coeFn_neg f] with x hx hx'
  rw [hx', Pi.neg_apply]
  linarith

/-- If $f \le K$ almost everywhere on $\Omega$, then $-K \le -f$ almost everywhere on $\Omega$. -/
theorem ae_neg_ge_neg {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), -K ≤ (-f) x := by
  filter_upwards [hf, Lp.coeFn_neg f] with x hx hx'
  rw [hx', Pi.neg_apply]
  linarith

end Aux

/-! ### Constants and truncations as elements of $H^1(\Omega)$ -/

section Engine

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| < \infty$ and let $K \in \mathbb{R}$.
There is $c \in H^1(\Omega)$ whose function is the constant $K$ almost everywhere on $\Omega$
and whose weak partial derivatives $\partial_i c$ all vanish. -/
theorem exists_const_of_measure_ne_top (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    (K : ℝ) :
    ∃ c : SobolevEuclidean N 1 2 Ω,
      fn c =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun _ ↦ K) ∧
      ∀ i, weakDeriv c (MultiIndexLE.single i) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    isFiniteMeasure_restrict.2 hΩ
  have hmem : MemSobolev (fun _ : EuclideanSpace ℝ (Fin N) ↦ K) 1 2 Ω volume := by
    refine ⟨memLp_const K, fun m hm ↦ ⟨_, ContDiffOn.hasWeakIteratedFDerivOn (μ := volume)
      (Ω := Ω) (contDiffOn_const (n := 1)) (by exact_mod_cast hm), ?_⟩⟩
    rcases m with _ | m
    · rw [iteratedFDeriv_zero_eq_comp]
      exact memLp_const _
    · rw [iteratedFDeriv_succ_const]
      exact memLp_const _
  obtain ⟨c, hc⟩ := (hmem.memSobolevMultiIndex
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)).exists_sobolevMultiIndex
  refine ⟨c, hc, fun i ↦ ?_⟩
  refine Lp.ext ?_
  have h1 := ((hasWeakIteratedLineDerivOn c (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis : Fin N → _) i)
    ).congr_ae hc (EventuallyEq.refl _ _)
  have h2 : HasWeakIteratedLineDerivOn ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
      (fun _ : EuclideanSpace ℝ (Fin N) ↦ K) 0 Ω volume := by
    have := (ContDiffOn.hasWeakIteratedFDerivOn (μ := volume) (Ω := Ω)
      (contDiffOn_const (c := K) (n := 1)) (m := 1) le_rfl).lineDeriv
        ![(EuclideanSpace.basisFun (Fin N) ℝ).toBasis i]
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    simp [iteratedFDeriv_succ_const]
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2),
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx0
  rw [hx0]
  exact hx

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $G$ be a Stampacchia truncation with bound $M$
(`IsStampacchiaTruncation G M`), let $u \in H^1(\Omega)$, and let $K' \in \mathbb{R}$. If
$|\Omega| < \infty$ or $K' \ge 0$, then there is $v \in H^1(\Omega)$ whose function is
$G(u - K')$ almost everywhere on $\Omega$.

These are the cases (a) and (b) of the proof of Theorem 9.27 of [brezis2011functional]. If
$K' \ge 0$, the function $t \mapsto G(t - K')$ vanishes at $0$ and the chain rule (Proposition
9.5, `MemSobolevMultiIndex.contDiff_comp`) applies directly. If $|\Omega| < \infty$, the chain
rule applies to $t \mapsto G(t - K') - G(-K')$, and the constant $G(-K')$ lies in $H^1(\Omega)$
by `Elliptic.exists_const_of_measure_ne_top`. -/
theorem exists_truncation_elem {G : ℝ → ℝ} {M : ℝ} (hG : IsStampacchiaTruncation G M)
    (u : SobolevEuclidean N 1 2 Ω) {K' : ℝ}
    (h : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ ∨ 0 ≤ K') :
    ∃ v : SobolevEuclidean N 1 2 Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ G (fn u x - K') := by
  have hmem : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      (fun x ↦ G (fn u x - K') - G (-K')) 1 2 Ω volume := by
    have := (memSobolevMultiIndex u).contDiff_comp (G := fun t ↦ G (t - K') - G (-K')) one_le_two
      ((hG.contDiff_sub K').sub contDiff_const) (by simp) (M := M) fun t ↦ by
        rw [deriv_sub_const]; exact hG.abs_deriv_sub_le K' t
    exact this
  rcases h with hΩ | hK'
  · obtain ⟨v₁, hv₁⟩ := hmem.exists_sobolevMultiIndex
    obtain ⟨c, hc, -⟩ := exists_const_of_measure_ne_top hΩ (G (-K'))
    refine ⟨v₁ + c, ?_⟩
    filter_upwards [fn_add v₁ c, hv₁, hc] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    ring
  · obtain ⟨v, hv⟩ := hmem.exists_sobolevMultiIndex
    refine ⟨v, hv.trans (Eventually.of_forall fun x ↦ ?_)⟩
    simp [hG.eq_zero_of_nonpos (-K') (by linarith)]

/-- Let $G$ be a Stampacchia truncation, let $u, v \in H^1(\Omega)$, and let $K' \in \mathbb{R}$. If
the function of $v$ is $G(u - K')$ almost everywhere on $\Omega$, then for each $i$
$$\partial_i v = G'(u - K')\, \partial_i u$$
almost everywhere on $\Omega$.

This is the chain rule, Proposition 9.5 of [brezis2011functional], together with the uniqueness
of weak derivatives. -/
theorem weakDeriv_single_ae_eq_of_fn_ae_eq_truncation {G : ℝ → ℝ} {M : ℝ}
    (hG : IsStampacchiaTruncation G M) {u v : SobolevEuclidean N 1 2 Ω} {K' : ℝ}
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ G (fn u x - K')) (i : Fin N) :
    (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn u x - K') * weakDeriv u (MultiIndexLE.single i) x := by
  have := weakDeriv_single_ae_eq_of_fn_ae_eq_comp (u := u) (v := v) (hG.contDiff_sub K')
    (hG.abs_deriv_sub_le K') hv i
  refine this.trans (Eventually.of_forall fun x ↦ ?_)
  simp only [deriv_comp_sub_const]

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| = \infty$ and let
$f \in L^2(\Omega)$. If $f \le K$ almost everywhere on $\Omega$, then $K \ge 0$.

This is the remark at the start of case (b) of the proof of Theorem 9.27 of
[brezis2011functional]. If $K < 0$, then $|f| \ge |K| > 0$ almost everywhere on a set of
infinite measure, and $f \notin L^2(\Omega)$. -/
theorem nonneg_of_ae_le_of_measure_eq_top
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) = ⊤)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) : 0 ≤ K := by
  by_contra hK
  push Not at hK
  have hne : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ 0 := by
    intro h
    rw [← Measure.restrict_apply_univ, h] at hΩ
    simp at hΩ
  have h1 : eLpNorm (fun _ ↦ K) 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ eLpNorm f 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
    refine eLpNorm_mono_ae aestronglyMeasurable_const ?_
    filter_upwards [hf] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hK, abs_of_neg (hx.trans_lt hK)]
    linarith
  rw [eLpNorm_const K two_ne_zero hne, Measure.restrict_apply_univ, hΩ,
    ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (by simpa using hK.ne)] at h1
  exact (Lp.eLpNorm_ne_top f) (top_le_iff.1 h1)

/-- The truncation argument of **Stampacchia's method**. Let $\Omega \subseteq \mathbb{R}^N$ be
open, let $V$ be a subspace of $H^1(\Omega)$, let $f \in L^2(\Omega)$, and let
$u \in H^1(\Omega)$ satisfy
$$\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f \varphi
  \qquad \text{for all } \varphi \in V.$$
Let $f \le K$ almost everywhere on $\Omega$. Suppose that for every $K' > K$, every Stampacchia
truncation $G$ and every $v \in H^1(\Omega)$ whose function is $G(u - K')$ almost everywhere,
$v \in V$. Then $u \le K$ almost everywhere on $\Omega$.

This is the common argument of the proofs of Theorem 9.27 of [brezis2011functional], for both
$|\Omega| < \infty$ and $|\Omega| = \infty$. Fix $K' > K$. The element $v$ with function
$G(u - K')$ exists by `Elliptic.exists_truncation_elem`, because $|\Omega| < \infty$, or else
$K' > K \ge 0$ by `Elliptic.nonneg_of_ae_le_of_measure_eq_top`. The equation tested with $v$
gives $\sum_i \int (\partial_i u)^2 G'(u - K') + \int (u - f) G(u - K') = 0$, so
$\int (u - f) G(u - K') \le 0$. Pointwise $0 \le (u - K') G(u - K') \le (u - f) G(u - K')$, so
$(u - K') G(u - K') = 0$ and $u \le K'$ almost everywhere. Then let $K' \downarrow K$. -/
theorem le_of_forall_truncation_mem (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω))
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) V u f) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K)
    (hV : ∀ K', K < K' → ∀ (G : ℝ → ℝ) (M : ℝ), IsStampacchiaTruncation G M →
      ∀ v : SobolevEuclidean N 1 2 Ω,
        fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
          (fun x ↦ G (fn u x - K')) → v ∈ V) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K := by
  obtain ⟨G, hG, -, -⟩ := exists_stampacchiaTruncation
  -- for every `K' > K`, `u ≤ K'` almost everywhere
  have key : ∀ K', K < K' →
      ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K' := by
    intro K' hK'
    have hcase : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ ∨ 0 ≤ K' := by
      by_cases hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) = ⊤
      · exact Or.inr ((nonneg_of_ae_le_of_measure_eq_top hΩ f hf).trans hK'.le)
      · exact Or.inl hΩ
    obtain ⟨v, hv⟩ := exists_truncation_elem hG u hcase
    have hvV : v ∈ V := hV K' hK' G _ hG v hv
    have hvm : AEStronglyMeasurable (fun x ↦ G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
      (memLp v).aestronglyMeasurable.congr hv
    have hum : AEStronglyMeasurable (fn u)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := (memLp u).aestronglyMeasurable
    -- the equation tested with `v`
    have e := heq v hvV
    rw [laplaceForm_apply_inner, load_apply_inner] at e
    -- the gradient term is nonnegative
    have hgrad : 0 ≤ ∑ i : Fin N, ⟪weakDeriv u (MultiIndexLE.single i),
        weakDeriv v (MultiIndexLE.single i)⟫_ℝ := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      rw [L2.inner_eq_integral_mul]
      refine integral_nonneg_of_ae ?_
      filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_truncation hG hv i] with x hx
      rw [hx, show weakDeriv u (MultiIndexLE.single i) x
          * (deriv G (fn u x - K') * weakDeriv u (MultiIndexLE.single i) x)
          = deriv G (fn u x - K') * (weakDeriv u (MultiIndexLE.single i) x
            * weakDeriv u (MultiIndexLE.single i) x) by ring]
      exact mul_nonneg (hG.deriv_nonneg _) (mul_self_nonneg _)
    have hv' : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        (weakDeriv v 0 : EuclideanSpace ℝ (Fin N) → ℝ) x = G (fn u x - K') := hv
    -- hence `∫ (u − f) G(u − K') ≤ 0`
    have hI : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (fn u x - f x) * G (fn u x - K') ≤ 0 := by
      have h1 : ⟪weakDeriv u 0, weakDeriv v 0⟫_ℝ - ⟪f, weakDeriv v 0⟫_ℝ
          = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))), (fn u x - f x) * G (fn u x - K') := by
        rw [← inner_sub_left, L2.inner_eq_integral_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (weakDeriv u 0) f, hv'] with x hx hx'
        rw [hx, Pi.sub_apply, hx']
        rfl
      linarith
    -- the integrand dominates the nonnegative `(u − K') G(u − K')`
    have hint : Integrable (fun x ↦ (fn u x - f x) * G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine (L2.integrable_inner (𝕜 := ℝ) (weakDeriv u 0 - f) (weakDeriv v 0)).congr ?_
      filter_upwards [Lp.coeFn_sub (weakDeriv u 0) f, hv'] with x hx hx'
      simp only [hx, Pi.sub_apply, RCLike.inner_apply, conj_trivial, hx']
      rw [mul_comm]
      rfl
    have hle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
        (fn u x - K') * G (fn u x - K') ≤ (fn u x - f x) * G (fn u x - K') := by
      filter_upwards [hf] with x hx
      exact mul_le_mul_of_nonneg_right (sub_le_sub_left (hx.trans hK'.le) _) (hG.nonneg _)
    have hint' : Integrable (fun x ↦ (fn u x - K') * G (fn u x - K'))
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := by
      refine hint.mono' ((hum.sub aestronglyMeasurable_const).mul hvm) ?_
      filter_upwards [hle] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hG.mul_nonneg _)]
      exact hx
    have hzero : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (fn u x - K') * G (fn u x - K') = 0 := by
      refine le_antisymm ((integral_mono_ae hint' hint hle).trans hI) ?_
      exact integral_nonneg fun x ↦ hG.mul_nonneg _
    have := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x ↦ hG.mul_nonneg _)
      hint').1 hzero
    filter_upwards [this] with x hx
    have := hG.mul_eq_zero_iff.1 hx
    linarith
  -- `K' = K + 1/(n+1)` for every `n`
  have hall : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ n : ℕ, fn u x ≤ K + 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun n ↦ key _ (lt_add_of_pos_right K (by positivity))
  filter_upwards [hall] with x hx
  have ht : Tendsto (fun n : ℕ ↦ K + 1 / ((n : ℝ) + 1)) atTop (𝓝 K) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto ht (Eventually.of_forall hx)

end Engine

/-! ### Theorem 9.27: the maximum principle for the Dirichlet problem -/

section Dirichlet

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The **weak maximum principle for the Dirichlet problem**, upper bound. Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, and let $u \in H^1(\Omega)$
satisfy $\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f
\varphi$ for all $\varphi \in H^1_0(\Omega)$. Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be
continuous on $\bar\Omega$ and equal to $u$ almost everywhere on $\Omega$. If $\tilde u \le K$
on $\partial\Omega$ and $f \le K$ almost everywhere on $\Omega$, then $\tilde u \le K$ on
$\Omega$. This is the upper bound in (70) of Theorem 9.27 of [brezis2011functional], for both
$|\Omega| < \infty$ and $|\Omega| = \infty$.

The proof applies `Elliptic.le_of_forall_truncation_mem` with $V = H^1_0(\Omega)$. The function
$G(\tilde u - K')$ is continuous on $\bar\Omega$ and vanishes on $\partial\Omega$, so its class
lies in $H^1_0(\Omega)$ by Theorem 9.17, (i) implies (ii), which needs no regularity of $\Omega$
(`SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier`). -/
theorem le_of_le_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have hae := le_of_forall_truncation_mem (SobolevEuclideanZero N 1 2 Ω) heq hf
    fun K' hK' G M hG v hv ↦ ?_
  · refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
    filter_upwards [hae, hu] with x hx hx'
    rw [← hx']
    exact hx
  · refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
      v (ũ := fun x ↦ G (ũ x - K')) ?_ (hG.contDiff.continuous.comp_continuousOn
        (hc.sub continuousOn_const)) fun x hx ↦ ?_
    · filter_upwards [hv, hu] with x hx hx'
      rw [hx, hx']
    · exact hG.eq_zero_of_nonpos _ (by linarith [hΓ x hx])

/-- The weak maximum principle for the Dirichlet problem, lower bound. Under the hypotheses of
`Elliptic.le_of_le_frontier` on $\Omega$, $f$, $u$ and $\tilde u$: if $K \le \tilde u$ on
$\partial\Omega$ and $K \le f$ almost everywhere on $\Omega$, then $K \le \tilde u$ on $\Omega$.
This is the lower bound in (70) of Theorem 9.27 of [brezis2011functional].

The proof applies the upper bound to $-u$, $-f$ and $-K$. -/
theorem ge_of_ge_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  have h := le_of_le_frontier (forall_laplaceForm_neg_eq_load_neg _ heq) (ũ := -ũ)
    ((fn_neg u).trans (hu.neg)) hc.neg (K := -K) (fun x hx ↦ by simpa using hΓ x hx)
    (ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- Under the hypotheses of `Elliptic.le_of_le_frontier` on $\Omega$, $f$, $u$ and $\tilde u$: if
$\tilde u \le K_1$ on $\partial\Omega$ and $f \le K_2$ almost everywhere on $\Omega$, then
$\tilde u \le \max\{K_1, K_2\}$ on $\Omega$. This is the upper half
$u \le \max\{\sup_\Gamma u, \sup_\Omega f\}$ of (70) in Theorem 9.27 of [brezis2011functional]. -/
theorem le_max_of_isWeakSolution {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K₂) :
    ∀ x ∈ Ω, ũ x ≤ max K₁ K₂ :=
  le_of_le_frontier heq hu hc (fun x hx ↦ (hΓ x hx).trans (le_max_left _ _))
    (hf.mono fun _ hx ↦ hx.trans (le_max_right _ _))

/-- The weak maximum principle for the Dirichlet problem without a continuity hypothesis, upper
bound. Let $\Omega \subseteq \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, and let
$u \in H^1_0(\Omega)$ satisfy $\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u
\varphi = \int_\Omega f \varphi$ for all $\varphi \in H^1_0(\Omega)$. If $K \ge 0$ and $f \le K$
almost everywhere on $\Omega$, then $u \le K$ almost everywhere on $\Omega$. This is footnote 35
of [brezis2011functional], §9.7.

The boundary value $0$ of $u$ replaces $\sup_\Gamma u$, which is why $K \ge 0$ is assumed. Then
$t \mapsto G(t - K')$ vanishes at $0$, and `SobolevMultiIndexZero.contDiff_comp_mem` places
$G(u - K')$ in $H^1_0(\Omega)$. The maximum principle for the heat equation in Chapter 10 of
[brezis2011functional] uses this form. -/
theorem le_of_mem_zero {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K := by
  refine le_of_forall_truncation_mem (SobolevEuclideanZero N 1 2 Ω) heq hf
    fun K' hK' G M hG v hv ↦ ?_
  exact SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hu (hG.contDiff_sub K')
    (hG.eq_zero_of_nonpos _ (by linarith)) (hG.abs_deriv_sub_le K') hv

/-- The weak maximum principle for the Dirichlet problem without a continuity hypothesis, lower
bound. Under the hypotheses of `Elliptic.le_of_mem_zero` on $\Omega$, $f$ and
$u \in H^1_0(\Omega)$: if $K \le 0$ and $K \le f$ almost everywhere on $\Omega$, then $K \le u$
almost everywhere on $\Omega$. -/
theorem ge_of_mem_zero {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f) {K : ℝ}
    (hK : K ≤ 0) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ fn u x := by
  have h := le_of_mem_zero (neg_mem hu) (forall_laplaceForm_neg_eq_load_neg _ heq) (K := -K)
    (by linarith) (ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

/-- Under the hypotheses of `Elliptic.le_of_le_frontier` on $\Omega$, $f$, $u$ and $\tilde u$: if
$\tilde u \ge 0$ on $\partial\Omega$ and $f \ge 0$ almost everywhere on $\Omega$, then
$\tilde u \ge 0$ on $\Omega$. This is (73), the first assertion of Corollary 9.28 of
[brezis2011functional]. -/
theorem nonneg_of_nonneg_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x :=
  ge_of_ge_frontier heq hu hc hΓ hf

/-- Under the hypotheses of `Elliptic.le_of_le_frontier` on $\Omega$, $f$, $u$ and $\tilde u$: if
$|\tilde u| \le K_1$ on $\partial\Omega$ and $|f| \le K_2$ almost everywhere on $\Omega$, then
$|\tilde u| \le \max\{K_1, K_2\}$ on $\Omega$. This is (74) of Corollary 9.28 of
[brezis2011functional], $\|u\|_{L^\infty(\Omega)} \le \max\{\|u\|_{L^\infty(\Gamma)},
\|f\|_{L^\infty(\Omega)}\}$. -/
theorem abs_le_max_of_isWeakSolution {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), |ũ x| ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |f x| ≤ K₂) :
    ∀ x ∈ Ω, |ũ x| ≤ max K₁ K₂ := by
  intro x hx
  rw [abs_le]
  constructor
  · have := ge_of_ge_frontier heq hu hc (K := -max K₁ K₂)
      (fun y hy ↦ by linarith [(abs_le.1 (hΓ y hy)).1, le_max_left K₁ K₂])
      (hf.mono fun y hy ↦ by linarith [(abs_le.1 hy).1, le_max_right K₁ K₂]) x hx
    exact this
  · exact le_of_le_frontier heq hu hc (fun y hy ↦ (le_abs_self _).trans
      ((hΓ y hy).trans (le_max_left _ _)))
      (hf.mono fun y hy ↦ (le_abs_self _).trans (hy.trans (le_max_right _ _))) x hx

/-- Let $\Omega$, $u$ and $\tilde u$ be as in `Elliptic.le_of_le_frontier` with $f = 0$. If
$K \ge 0$ and $|\tilde u| \le K$ on $\partial\Omega$, then $|\tilde u| \le K$ on $\Omega$. This
is the case $f = 0$ of Corollary 9.28 of [brezis2011functional], $\|u\|_{L^\infty(\Omega)} \le
\|u\|_{L^\infty(\Gamma)}$. -/
theorem abs_le_of_load_eq_zero {u : SobolevEuclidean N 1 2 Ω}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u 0)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hK : 0 ≤ K)
    (hΓ : ∀ x ∈ frontier (Ω : Set _), |ũ x| ≤ K) :
    ∀ x ∈ Ω, |ũ x| ≤ K := by
  have h := abs_le_max_of_isWeakSolution heq hu hc hΓ (K₂ := K) ?_
  · simpa using h
  · filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx
    rw [hx, Pi.zero_apply, abs_zero]
    exact hK

/-- Under the hypotheses of `Elliptic.le_of_le_frontier` on $\Omega$, $f$, $u$ and $\tilde u$: if
$\tilde u = 0$ on $\partial\Omega$, $K \ge 0$ and $|f| \le K$ almost everywhere on $\Omega$,
then $|\tilde u| \le K$ on $\Omega$. This is the case $u = 0$ on $\Gamma$ of Corollary 9.28 of
[brezis2011functional], $\|u\|_{L^\infty(\Omega)} \le \|f\|_{L^\infty(\Omega)}$. -/
theorem abs_le_of_eqOn_zero_frontier {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : IsWeakSolution (laplaceForm Ω) (SobolevEuclideanZero N 1 2 Ω) u f)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : EqOn ũ 0 (frontier Ω)) {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), |f x| ≤ K) :
    ∀ x ∈ Ω, |ũ x| ≤ K := by
  have h := abs_le_max_of_isWeakSolution heq hu hc (K₁ := K)
    (fun x hx ↦ by rw [hΓ hx, Pi.zero_apply, abs_zero]; exact hK) hf
  simpa using h

end Dirichlet

/-! ### Proposition 9.30: the maximum principle for the Neumann problem -/

section Neumann

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- The **weak maximum principle for the Neumann problem**, upper bound. Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $f \in L^2(\Omega)$, and let $u \in H^1(\Omega)$
satisfy $\int_\Omega \nabla u \cdot \nabla \varphi + \int_\Omega u \varphi = \int_\Omega f
\varphi$ for all $\varphi \in H^1(\Omega)$. If $f \le K$ almost everywhere on $\Omega$, then
$u \le K$ almost everywhere on $\Omega$. This is the upper half of (82) in Proposition 9.30 of
[brezis2011functional].

The proof applies `Elliptic.le_of_forall_truncation_mem` with $V = H^1(\Omega)$, where every
truncation $G(u - K')$ is admissible. No boundary values enter, so no continuity of $u$ is
assumed. -/
theorem le_of_neumann {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ K) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ K :=
  le_of_forall_truncation_mem ⊤ (fun φ _ ↦ heq φ) hf fun _ _ _ _ _ _ _ ↦ Submodule.mem_top

/-- The weak maximum principle for the Neumann problem, lower bound. Under the hypotheses of
`Elliptic.le_of_neumann` on $\Omega$, $f$ and $u$: if $K \le f$ almost everywhere on $\Omega$,
then $K \le u$ almost everywhere on $\Omega$. This is the lower half of (82) in Proposition 9.30
of [brezis2011functional]. -/
theorem ge_of_neumann {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ, laplaceForm Ω u φ = load Ω f φ) {K : ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), K ≤ fn u x := by
  have h := le_of_neumann (u := -u) (f := -f)
    (fun φ ↦ forall_laplaceForm_neg_eq_load_neg ⊤ (fun φ _ ↦ heq φ) φ Submodule.mem_top)
    (ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

end Neumann

/-! ### Proposition 9.29: the maximum principle for general elliptic operators (no drift) -/

section General

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- Let $N \ge 1$ and let $\Omega \subseteq \mathbb{R}^N$ be open. Let $a_{ij} \in L^\infty(\Omega)$
be uniformly elliptic with constant $\alpha$, let $a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$
almost everywhere, and let $f \in L^2(\Omega)$ with $f \le 0$ almost everywhere. Let
$u \in H^1(\Omega)$ satisfy
$$\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi + \int_\Omega a_0 u \varphi =
  \int_\Omega f \varphi \qquad \text{for all } \varphi \in H^1_0(\Omega).$$
Suppose that for every Stampacchia truncation $G$, every $v \in H^1(\Omega)$ whose function is
$G(u)$ almost everywhere lies in $H^1_0(\Omega)$. Then $u \le 0$ almost everywhere on $\Omega$.
This is the core of the proof of (79') in Proposition 9.29 of [brezis2011functional].

The equation tested with $G(u)$ gives $|\nabla u|^2 G'(u) = 0$. The function $H(u)$ with
$H(t) = \int_0^t \sqrt{G'(s)}\,ds$ (`stampacchiaTruncationSqrt`) lies in $H^1_0(\Omega)$ and has
$\nabla H(u) = 0$, so $H(u) = 0$ by footnote 39
(`SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero`), which needs $N \ge 1$. The form is
`Elliptic.generalForm Ω A 0 a₀`, and uniform ellipticity is `Elliptic.IsUniformlyElliptic`. -/
theorem nonpos_ae_of_general_zero_drift_of_forall_mem (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    (hadm : ∀ (G : ℝ → ℝ) (M : ℝ), IsStampacchiaTruncation G M → ∀ v : SobolevEuclidean N 1 2 Ω,
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] (fun x ↦ G (fn u x)) →
        v ∈ SobolevEuclideanZero N 1 2 Ω) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 := by
  classical
  have hα : 0 < α := hA.1
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = stampacchiaTruncation := ⟨_, rfl⟩
  have hG : IsStampacchiaTruncation G 1 := hGdef ▸ isStampacchiaTruncation_stampacchiaTruncation
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℝ, H = stampacchiaTruncationSqrt := ⟨_, rfl⟩
  have hH : IsStampacchiaTruncation H 1 := hHdef ▸ isStampacchiaTruncation_stampacchiaTruncationSqrt
  have hHG : ∀ s, deriv H s ^ 2 = deriv G s := fun s ↦ by
    rw [hHdef, hGdef]; exact sq_deriv_stampacchiaTruncationSqrt s
  have hum : AEStronglyMeasurable (fn u) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (memLp u).aestronglyMeasurable
  -- the test function `v = G(u) ∈ H^1_0(Ω)`
  obtain ⟨v, hv⟩ := ((memSobolevMultiIndex u).contDiff_comp one_le_two hG.contDiff hG.zero
    hG.abs_deriv_le).exists_sobolevMultiIndex
  have hvV := hadm G 1 hG v hv
  have hv' : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (weakDeriv v 0 : EuclideanSpace ℝ (Fin N) → ℝ) x = G (fn u x) := hv
  have hvi : ∀ i, (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ deriv G (fn u x) * weakDeriv u (MultiIndexLE.single i) x := fun i ↦
    weakDeriv_single_ae_eq_of_fn_ae_eq_comp hG.contDiff hG.abs_deriv_le hv i
  -- the equation tested with `v`
  have e := heq v hvV
  rw [generalForm_apply_inner, load_apply_inner] at e
  have hmid : ∑ i : Fin N, ⟪mulL Ω ((0 : Fin N → Lp ℝ ⊤ (volume.restrict
      (Ω : Set (EuclideanSpace ℝ (Fin N))))) i) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v 0⟫_ℝ = 0 := by
    simp [mulL_zero]
  have hthird : 0 ≤ ⟪mulL Ω a₀ (weakDeriv u 0), weakDeriv v 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha₀, hv'] with x hx hx'
    rw [hx', mul_assoc]
    exact mul_nonneg hx (hG.mul_nonneg _)
  have hrhs : ⟪f, weakDeriv v 0⟫_ℝ ≤ 0 := by
    rw [L2.inner_eq_integral_mul]
    refine integral_nonpos_of_ae ?_
    filter_upwards [hf, hv'] with x hx hx'
    rw [hx']
    exact mul_nonpos_of_nonpos_of_nonneg hx (hG.nonneg _)
  -- the principal term dominates `α ∫ |∇u|² G'(u)`
  have hint : ∀ i j, Integrable (fun x ↦ A i j x * weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv v (MultiIndexLE.single j) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i j ↦
    integrable_mul_mul Ω _ _ _
  have hsq : ∀ i, Integrable (fun x ↦ weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv u (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) := fun i ↦
    (L2.integrable_inner (𝕜 := ℝ) (weakDeriv u (MultiIndexLE.single i))
      (weakDeriv u (MultiIndexLE.single i))).congr
      (Eventually.of_forall fun x ↦ by simp [sq])
  have hGm : AEStronglyMeasurable (fun x ↦ deriv G (fn u x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (hG.contDiff.continuous_deriv le_rfl).comp_aestronglyMeasurable hum
  have hGb : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ‖deriv G (fn u x)‖ ≤ 1 := Eventually.of_forall fun x ↦ hG.abs_deriv_le _
  have hDint : Integrable (fun x ↦ (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
      * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x))
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (integrable_finsetSum _ fun i _ ↦ hsq i).mul_bdd hGm hGb
  have hprin : α * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
        * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x)
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
          weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    simp only [inner_mulL_eq_integral]
    simp only [← integral_finsetSum _ fun j _ ↦ hint _ j]
    rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j,
      ← integral_const_mul]
    refine integral_mono_ae (hDint.const_mul α)
      (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j) ?_
    filter_upwards [hA.2, ae_all_iff.2 hvi] with x hx hxv
    have h := hx (WithLp.toLp 2 fun i ↦ weakDeriv u (MultiIndexLE.single i) x)
    rw [EuclideanSpace.real_norm_sq_eq] at h
    simp only [hxv]
    have hd : 0 ≤ deriv G (fn u x) := hG.deriv_nonneg _
    calc α * ((∑ i, weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x)
          * deriv G (fn u x))
        = (α * ∑ i, weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x)
          * deriv G (fn u x) := by ring
      _ ≤ (∑ i, ∑ j, A i j x * weakDeriv u (MultiIndexLE.single i) x
          * weakDeriv u (MultiIndexLE.single j) x) * deriv G (fn u x) := by
          refine mul_le_mul_of_nonneg_right ?_ hd
          simpa [sq] using h
      _ = ∑ i, ∑ j, A i j x * weakDeriv u (MultiIndexLE.single i) x
          * (deriv G (fn u x) * weakDeriv u (MultiIndexLE.single j) x) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  -- hence `∫ |∇u|² G'(u) = 0`, so `|∇u|² G'(u) = 0` almost everywhere
  have hzero : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
      (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
        * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x) = 0 := by
    have hnn : 0 ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin N))),
        (∑ i : Fin N, weakDeriv u (MultiIndexLE.single i) x
          * weakDeriv u (MultiIndexLE.single i) x) * deriv G (fn u x) :=
      integral_nonneg fun x ↦ mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
        (hG.deriv_nonneg _)
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x ↦
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (hG.deriv_nonneg _)) hDint).1 hzero
  -- the element `h = H(u) ∈ H^1_0(Ω)` has vanishing gradient
  obtain ⟨h, hh⟩ := ((memSobolevMultiIndex u).contDiff_comp one_le_two hH.contDiff hH.zero
    hH.abs_deriv_le).exists_sobolevMultiIndex
  have hhV := hadm H 1 hH h hh
  have hhi : ∀ i, weakDeriv h (MultiIndexLE.single i) = 0 := fun i ↦ by
    refine Lp.ext ?_
    filter_upwards [weakDeriv_single_ae_eq_of_fn_ae_eq_comp hH.contDiff hH.abs_deriv_le hh i, hae,
      Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))] with x hx hx' hx0
    rw [hx, hx0, Pi.zero_apply]
    have hi : weakDeriv u (MultiIndexLE.single i) x * weakDeriv u (MultiIndexLE.single i) x
        * deriv G (fn u x) = 0 := by
      have hsum : (∑ j : Fin N, weakDeriv u (MultiIndexLE.single j) x
          * weakDeriv u (MultiIndexLE.single j) x) * deriv G (fn u x) = 0 := hx'
      rw [Finset.sum_mul] at hsum
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
        mul_nonneg (mul_self_nonneg _) (hG.deriv_nonneg _)).1 hsum i (Finset.mem_univ i)
    have : (deriv H (fn u x) * weakDeriv u (MultiIndexLE.single i) x) ^ 2 = 0 := by
      rw [mul_pow, hHG]
      linear_combination hi
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have hh0 : (⟨h, hhV⟩ : SobolevEuclideanZero N 1 2 Ω) = 0 :=
    SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero hN ENNReal.ofNat_ne_top _ hhi
  have hh0' : h = 0 := congrArg Subtype.val hh0
  -- `H(u) = 0` almost everywhere, so `u ≤ 0`
  have hz : fn (0 : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] 0 := fn_zero
  filter_upwards [hh, hz] with x hx hx0
  rw [hh0', hx0, Pi.zero_apply] at hx
  by_contra hpos
  push Not at hpos
  exact (hH.pos_of_pos _ hpos).ne hx

end General

section General

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- The general form (41) of [brezis2011functional], $a(u, \varphi) = \sum_{i,j} \int_\Omega a_{ij}
\partial_i u\, \partial_j \varphi + \sum_i \int_\Omega a_i \partial_i u\, \varphi + \int_\Omega
a_0 u \varphi$, satisfies $a(-u, \varphi) = -a(u, \varphi)$. -/
theorem generalForm_neg_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ a₀ (-u) φ = -generalForm Ω A a₁ a₀ u φ :=
  ContinuousLinearMap.map_neg₂ _ u φ

/-- If $u \in H^1(\Omega)$ satisfies $a(u, \varphi) = \int_\Omega f \varphi$ for all
$\varphi \in V$, for the general form $a$ of (41), then
$a(-u, \varphi) = \int_\Omega (-f) \varphi$ for all $\varphi \in V$. -/
theorem forall_generalForm_neg_eq_load_neg
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)) {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ V, generalForm Ω A a₁ a₀ u φ = load Ω f φ) :
    ∀ φ ∈ V, generalForm Ω A a₁ a₀ (-u) φ = load Ω (-f) φ := fun φ hφ ↦ by
  rw [generalForm_neg_apply, load_neg_apply, heq φ hφ]

/-- Let $N \ge 1$ and let $\Omega \subseteq \mathbb{R}^N$ be open. Let $a_{ij} \in L^\infty(\Omega)$
be uniformly elliptic with constant $\alpha$, let $a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$
almost everywhere, let $f \in L^2(\Omega)$, and let $u \in H^1(\Omega)$ satisfy
$$\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi + \int_\Omega a_0 u \varphi =
  \int_\Omega f \varphi \qquad \text{for all } \varphi \in H^1_0(\Omega).$$
Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ and equal to $u$
almost everywhere on $\Omega$. If $\tilde u \le 0$ on $\partial\Omega$ and $f \le 0$ almost
everywhere on $\Omega$, then $\tilde u \le 0$ on $\Omega$. This is the form (79') that the proof
of Proposition 9.29 of [brezis2011functional] establishes, without a drift term.

The truncations $G(\tilde u)$ are continuous on $\bar\Omega$ and vanish on $\partial\Omega$, so
their classes lie in $H^1_0(\Omega)$ by Theorem 9.17, (i) implies (ii), and
`Elliptic.nonpos_ae_of_general_zero_drift_of_forall_mem` applies. -/
theorem nonpos_of_nonpos_frontier_general_zero_drift (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ 0 := by
  have hae := nonpos_ae_of_general_zero_drift_of_forall_mem hN hA ha₀ heq hf
    fun G M hG v hv ↦ ?_
  · refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
    filter_upwards [hae, hu] with x hx hx'
    rw [← hx']
    exact hx
  · refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
      v (ũ := fun x ↦ G (ũ x)) ?_ (hG.contDiff.continuous.comp_continuousOn hc) fun x hx ↦ ?_
    · filter_upwards [hv, hu] with x hx hx'
      rw [hx, hx']
    · exact hG.eq_zero_of_nonpos _ (hΓ x hx)

/-- Under the hypotheses of `Elliptic.nonpos_of_nonpos_frontier_general_zero_drift` on $N \ge 1$,
$\Omega$, $a_{ij}$, $a_0 \ge 0$, $f$, $u$ and $\tilde u$: if $\tilde u \ge 0$ on
$\partial\Omega$ and $f \ge 0$ almost everywhere on $\Omega$, then $\tilde u \ge 0$ on $\Omega$.
This is (79) of Proposition 9.29 of [brezis2011functional] with $a_i = 0$, the case that the
source proves.

The source quotes the general case with a drift term from Gilbarg and Trudinger, Theorem 8.1;
that case is `Elliptic.nonneg_of_nonneg_frontier_general`, for $N \ge 3$. The proof applies the
form (79'), `Elliptic.nonpos_of_nonpos_frontier_general_zero_drift`, to $-u$ and $-f$. -/
theorem nonneg_of_nonneg_frontier_general_zero_drift (hN : N ≠ 0)
    (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x := by
  have h := nonpos_of_nonpos_frontier_general_zero_drift hN hA ha₀
    (forall_generalForm_neg_eq_load_neg A 0 a₀ _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- Let $N \ge 1$, let $\Omega \subseteq \mathbb{R}^N$ be open, let $a_{ij} \in L^\infty(\Omega)$ be
uniformly elliptic, let $a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$ almost everywhere, and let
$f \in L^2(\Omega)$. Let $u \in H^1_0(\Omega)$ satisfy $\sum_{i,j} \int_\Omega a_{ij} \partial_i
u\, \partial_j \varphi + \int_\Omega a_0 u \varphi = \int_\Omega f \varphi$ for all
$\varphi \in H^1_0(\Omega)$. If $f \le 0$ almost everywhere on $\Omega$, then $u \le 0$ almost
everywhere on $\Omega$. This is (79') of Proposition 9.29 of [brezis2011functional] for
$u \in H^1_0(\Omega)$ without a continuity hypothesis, as in footnote 38 of §9.7.

The truncations $G(u)$ lie in $H^1_0(\Omega)$ by `SobolevMultiIndexZero.contDiff_comp_mem`. -/
theorem nonpos_of_mem_zero_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 :=
  nonpos_ae_of_general_zero_drift_of_forall_mem hN hA ha₀ heq hf fun _ _ hG _ hv ↦
    SobolevMultiIndexZero.contDiff_comp_mem ENNReal.ofNat_ne_top hu hG.contDiff hG.zero
      hG.abs_deriv_le hv

/-- Under the hypotheses of `Elliptic.nonpos_of_mem_zero_general_zero_drift` on $N \ge 1$, $\Omega$,
$a_{ij}$, $a_0 \ge 0$, $f$ and $u \in H^1_0(\Omega)$: if $f \ge 0$ almost everywhere on
$\Omega$, then $u \ge 0$ almost everywhere on $\Omega$. This is (79) of Proposition 9.29 of
[brezis2011functional] for $u \in H^1_0(\Omega)$, as in footnote 38 of §9.7.

This is the drift-free case of the second clause of Remark 23: for $f = 0$ it gives $u \ge 0$
and $u \le 0$, so the form $\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi +
\int_\Omega a_0 u \varphi$ has only the trivial homogeneous solution in $H^1_0(\Omega)$. -/
theorem nonneg_of_mem_zero_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω} (hu : u ∈ SobolevEuclideanZero N 1 2 Ω)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ fn u x := by
  have h := nonpos_of_mem_zero_general_zero_drift hN hA ha₀ (neg_mem hu)
    (forall_generalForm_neg_eq_load_neg A 0 a₀ _ heq) (by simpa using ae_neg_le_neg hf)
  filter_upwards [h, fn_neg u] with x hx hx'
  rw [hx', Pi.neg_apply] at hx
  linarith

/-- Let $c \in H^1(\Omega)$ have $\partial_i c = 0$ for every $i$. Then the form $a(u, \varphi) =
\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi$, the case $a_i = 0$, $a_0 = 0$
of (41), satisfies $a(u - c, \varphi) = a(u, \varphi)$ for all $u, \varphi \in H^1(\Omega)$. -/
theorem generalForm_zero_zero_sub_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {u c : SobolevEuclidean N 1 2 Ω} (hc : ∀ i, weakDeriv c (MultiIndexLE.single i) = 0)
    (φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A 0 0 (u - c) φ = generalForm Ω A 0 0 u φ := by
  have e : ∀ i, weakDeriv (u - c) (MultiIndexLE.single i) = weakDeriv u (MultiIndexLE.single i) :=
    fun i ↦ by
      rw [show weakDeriv (u - c) (MultiIndexLE.single i)
        = weakDeriv u (MultiIndexLE.single i) - weakDeriv c (MultiIndexLE.single i) from rfl, hc i,
        sub_zero]
  rw [generalForm_apply_inner, generalForm_apply_inner]
  simp only [e, Pi.zero_apply, mulL_zero, zero_apply, inner_zero_left, Finset.sum_const_zero,
    add_zero]

/-- Let $N \ge 1$, let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| < \infty$, let
$a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic, let $f \in L^2(\Omega)$, and let
$u \in H^1(\Omega)$ satisfy $\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi =
\int_\Omega f \varphi$ for all $\varphi \in H^1_0(\Omega)$. Let
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ and equal to $u$ almost
everywhere on $\Omega$. If $f \ge 0$ almost everywhere on $\Omega$ and $K \le \tilde u$ on
$\partial\Omega$, then $K \le \tilde u$ on $\Omega$. This is $u \ge \inf_\Gamma u$, (80) of
Proposition 9.29 of [brezis2011functional], with $a_i = 0$ and $a_0 = 0$.

The source assumes $\Omega$ bounded; here $|\Omega| < \infty$ suffices. The constant $K$ lies in
$H^1(\Omega)$ with zero gradient (`Elliptic.exists_const_of_measure_ne_top`). Then $u - K$
satisfies the same equation, because the form has no zeroth-order term
(`Elliptic.generalForm_zero_zero_sub_apply`), and (79) applies to $u - K$. -/
theorem ge_of_ge_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  obtain ⟨c, hcK, hc0⟩ := exists_const_of_measure_ne_top hΩ K
  have h := nonneg_of_nonneg_frontier_general_zero_drift hN hA (a₀ := 0)
    (by filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx; rw [hx]; exact le_rfl)
    (u := u - c) (fun φ hφ ↦ by rw [generalForm_zero_zero_sub_apply A hc0, heq φ hφ])
    (ũ := fun x ↦ ũ x - K) ?_ (hc.sub continuousOn_const)
    (fun x hx ↦ by linarith [hΓ x hx]) hf
  · intro x hx
    linarith [h x hx]
  · filter_upwards [fn_sub u c, hu, hcK] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'']

/-- Under the hypotheses of `Elliptic.ge_of_ge_frontier_general_zero_drift` on $N \ge 1$, $\Omega$
with $|\Omega| < \infty$, $a_{ij}$, $a_0 = 0$, $f$, $u$ and $\tilde u$: if $f \le 0$ almost
everywhere on $\Omega$ and $\tilde u \le K$ on $\partial\Omega$, then $\tilde u \le K$ on
$\Omega$. This is $u \le \sup_\Gamma u$, which appears in the proof of (80) in Proposition 9.29
of [brezis2011functional]. -/
theorem le_of_le_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have h := ge_of_ge_frontier_general_zero_drift hN hA hΩ
    (forall_generalForm_neg_eq_load_neg A 0 0 _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (K := -K) (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_ge_neg hf)
  intro x hx
  simpa using h x hx

/-- Let $N \ge 1$, let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| < \infty$, let
$a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic, and let $u \in H^1(\Omega)$ satisfy
$\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi = 0$ for all
$\varphi \in H^1_0(\Omega)$. Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on
$\bar\Omega$ and equal to $u$ almost everywhere on $\Omega$. If $K_1 \le \tilde u \le K_2$ on
$\partial\Omega$, then $K_1 \le \tilde u \le K_2$ on $\Omega$. This is
$\inf_\Gamma u \le u \le \sup_\Gamma u$, (81) of Proposition 9.29 of [brezis2011functional],
with $a_i = 0$, $a_0 = 0$ and $f = 0$. -/
theorem mem_Icc_of_frontier_general_zero_drift (hN : N ≠ 0) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {u : SobolevEuclidean N 1 2 Ω}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A 0 0 u φ = load Ω 0 φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ∈ Icc K₁ K₂) :
    ∀ x ∈ Ω, ũ x ∈ Icc K₁ K₂ := by
  have h0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (0 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) x = 0 :=
    Lp.coeFn_zero ℝ 2 _
  intro x hx
  exact ⟨ge_of_ge_frontier_general_zero_drift hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).1)
      (h0.mono fun y hy ↦ hy.symm.le) x hx,
    le_of_le_frontier_general_zero_drift hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).2)
      (h0.mono fun y hy ↦ hy.le) x hx⟩

end General

/-!
### The truncation $(u - l)^+$ and the level sets of a $W^{1,p}$ function

The proof of Theorem 8.1 of Gilbarg and Trudinger tests the equation with $v = (u - l)^+$ for a
constant $l \ge 0$. This is a Lipschitz function of $u$, but not a $C^1$ function, so the chain rule
of Proposition 9.5 of [brezis2011functional] does not apply to it directly. The positive part of
`Numlib.Analysis.Sobolev.Calculus` (`HasWeakIteratedLineDerivOn.posPart`, through the $C^1$
approximations $G_\varepsilon(s) = \sqrt{(\max\{s, 0\})^2 + \varepsilon^2} - \varepsilon$) applies
after the affine shift $t \mapsto t - l$, which the chain rule covers. The same two shifts show that
the weak gradient vanishes on a level set (Lemma 7.7 of Gilbarg and Trudinger). Because of this, the
set $\{u > l\} \cap \{\nabla u \neq 0\}$ shrinks to a null set as $l$ rises to the essential
supremum of $u$.
-/

section PosPartSubConst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {y : E}

/-- Let $\Omega$ be an open subset of a finite-dimensional real normed space $E$ with an additive
Haar measure $\mu$, and let $w$ be the weak derivative of $u$ along $y$ on $\Omega$. Then for
every constant $l$, $w$ is also the weak derivative of $u - l$ along $y$ on $\Omega$.

This is the chain rule `HasWeakIteratedLineDerivOn.contDiff_comp'` for the $C^1$ function
$t \mapsto t - l$, whose derivative is $1$. -/
theorem _root_.HasWeakIteratedLineDerivOn.sub_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x - l) w Ω μ := by
  have hd : ∀ t : ℝ, deriv (fun s : ℝ ↦ s - l) t = 1 := fun t ↦ by simp
  refine (h.contDiff_comp' (f := fun s : ℝ ↦ s - l) (contDiff_id.sub contDiff_const)
      (M := 1) fun t ↦ by rw [hd]; norm_num).congr_ae (Eventually.of_forall fun x ↦ rfl) ?_
  filter_upwards with x
  rw [hd, one_mul]

/-- Let $w$ be the weak derivative of $u$ along $y$ on $\Omega$. Then for every constant $l$, $-w$
is the weak derivative of $l - u$ along $y$ on $\Omega$.

This is the chain rule for the $C^1$ function $t \mapsto l - t$, whose derivative is $-1$. -/
theorem _root_.HasWeakIteratedLineDerivOn.const_sub {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ l - u x) (fun x ↦ -w x) Ω μ := by
  have hd : ∀ t : ℝ, deriv (fun s : ℝ ↦ l - s) t = -1 := fun t ↦ by simp
  refine (h.contDiff_comp' (f := fun s : ℝ ↦ l - s) (contDiff_const.sub contDiff_id)
      (M := 1) fun t ↦ by rw [hd]; norm_num).congr_ae (Eventually.of_forall fun x ↦ rfl) ?_
  filter_upwards with x
  rw [hd, neg_one_mul]

/-- Let $w$ be the weak derivative of $u$ along $y$ on $\Omega$, and let $l$ be a constant. Then
$1_{\{u > l\}} w$ is the weak derivative of $(u - l)^+ = \max\{u - l, 0\}$ along $y$ on
$\Omega$.

The proof applies `HasWeakIteratedLineDerivOn.posPart` to $u - l$
(`HasWeakIteratedLineDerivOn.sub_const`). -/
theorem _root_.HasWeakIteratedLineDerivOn.posPart_sub_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (l : ℝ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ max (u x - l) 0)
      ({x | l < u x}.indicator w) Ω μ := by
  have h2 := (h.sub_const l).posPart
  have hset : {x : E | 0 < u x - l} = {x : E | l < u x} := by
    ext x; simp [sub_pos]
  rwa [hset] at h2

/-- Let $w$ be the weak derivative of $u$ along $y$ on $\Omega$, and let $c$ be a constant. Then
$w = 0$ almost everywhere on the level set $\{u = c\} \cap \Omega$. This is Lemma 7.7 of Gilbarg
and Trudinger, *Elliptic Partial Differential Equations of Second Order*.

The function $u - c$ is $(u - c)^+ - (c - u)^+$, and the weak derivatives of the two positive
parts are $1_{\{u > c\}} w$ and $-1_{\{u < c\}} w$. Hence
$w = 1_{\{u > c\}} w + 1_{\{u < c\}} w$ almost everywhere, and $w$ vanishes where $u = c$. -/
theorem _root_.HasWeakIteratedLineDerivOn.ae_eq_zero_of_eq_const {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) (c : ℝ) :
    ∀ᵐ x ∂(μ.restrict (Ω : Set E)), u x = c → w x = 0 := by
  classical
  have h1 := h.posPart_sub_const c
  have h2 := (h.const_sub c).posPart
  have hset : {x : E | 0 < c - u x} = {x : E | u x < c} := by ext x; simp [sub_pos]
  rw [hset] at h2
  have h4 : HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x - c)
      (({x : E | c < u x}.indicator w) - ({x : E | u x < c}.indicator fun x ↦ -w x)) Ω μ := by
    refine (h1.sub h2).congr_ae (Eventually.of_forall fun x ↦ ?_) (EventuallyEq.refl _ _)
    simp only [Pi.sub_apply]
    rcases le_total (u x) c with hx | hx
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h6 : ∀ᵐ x ∂(μ.restrict (Ω : Set E)),
      w x = ({x : E | c < u x}.indicator w) x - ({x : E | u x < c}.indicator fun x ↦ -w x) x :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2
      (by filter_upwards [(h.sub_const c).ae_eq h4] with x hx using hx)
  filter_upwards [h6] with x hx hxc
  rw [hx, Set.indicator_of_notMem (by simp [hxc]), Set.indicator_of_notMem (by simp [hxc]),
    sub_zero]

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}

/-- Let $1 \le p \le \infty$, let $u \in W^{1,p}(\Omega)$, and let $l \ge 0$. Then $(u - l)^+ =
\max\{u - l, 0\} \in W^{1,p}(\Omega)$.

The hypothesis $l \ge 0$ gives the bound $|(u - l)^+| \le |u|$, which keeps the truncation in
$L^p$ on an open set of infinite measure. The partial derivatives are $\partial_i (u - l)^+ =
1_{\{u > l\}} \partial_i u$; this formula is
`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart_sub_const`. -/
theorem _root_.MemSobolevMultiIndex.posPart_sub_const {u : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) {l : ℝ} (hl : 0 ≤ l) :
    MemSobolevMultiIndex b (fun x ↦ max (u x - l) 0) 1 p Ω μ := by
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hpos : MemLp (fun x ↦ max (u x - l) 0) p (μ.restrict (Ω : Set E)) :=
    hu.memLp.of_le (((continuous_id.sub continuous_const).max
        continuous_const).comp_aestronglyMeasurable hum)
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        rcases le_total (u x) l with hx | hx
        · rw [max_eq_right (by linarith), abs_zero]
          exact abs_nonneg _
        · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith)]
          exact (by linarith : u x - l ≤ u x).trans (le_abs_self _))
  refine ⟨hpos, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hpos.locallyIntegrableOn hp), hpos⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    have hset : {x : E | l < u x} = {x : E | 0 < u x - l} := by ext x; simp [sub_pos]
    refine ⟨_, (hw'.posPart_sub_const l).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      hwp.of_le ?_ (Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)⟩
    rw [hset]
    exact aestronglyMeasurable_indicator_pos
      ((continuous_id.sub continuous_const).comp_aestronglyMeasurable hum)
      hwp.aestronglyMeasurable

/-- Let $u, v \in W^{1,p}(\Omega)$ and let $l$ be a constant. If the function of $v$ is $(u - l)^+$
almost everywhere on $\Omega$, then $\partial_i v = 1_{\{u > l\}} \partial_i u$ almost
everywhere on $\Omega$, for each $i$.

The proof uses `HasWeakIteratedLineDerivOn.posPart_sub_const` and the uniqueness of the weak
derivative. -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart_sub_const
    {u v : SobolevMultiIndex ℝ b 1 p Ω μ} {l : ℝ}
    (hv : SobolevMultiIndex.fn v =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ max (SobolevMultiIndex.fn u x - l) 0) (i : ι) :
    (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : E → ℝ)
      =ᵐ[μ.restrict (Ω : Set E)] {x | l < SobolevMultiIndex.fn u x}.indicator
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)) := by
  have h2 := ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).posPart_sub_const l
  exact SobolevMultiIndex.weakDeriv_single_ae_eq_of_hasWeakIteratedLineDerivOn hv i h2

/-- Let $u \in W^{1,p}(\Omega)$ and let $c$ be a constant. Then each partial derivative
$\partial_i u$ vanishes almost everywhere on the level set $\{u = c\} \cap \Omega$
(`HasWeakIteratedLineDerivOn.ae_eq_zero_of_eq_const`). -/
theorem _root_.SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq
    (u : SobolevMultiIndex ℝ b 1 p Ω μ) (c : ℝ) (i : ι) :
    ∀ᵐ x ∂(μ.restrict (Ω : Set E)), SobolevMultiIndex.fn u x = c →
      (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : E → ℝ) x = 0 :=
  ((SobolevMultiIndex.hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)).ae_eq_zero_of_eq_const c

end PosPartSubConst

/-!
### Proposition 9.29 with a drift term: Theorem 8.1 of Gilbarg and Trudinger

The source proves (79) only for $a_i = 0$, and cites Gilbarg and Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Theorem 8.1, for the general case. That proof is formalized
here, for $N \ge 3$. For $\sup_\Gamma u \le l < \sup_\Omega u$ the truncation $v = (u - l)^+$ lies
in $H^1_0(\Omega)$. The equation tested with $v$ gives $\alpha \int |\nabla v|^2 \le \int \sum_i a_i
\partial_i u\, v \le (\sum_i \|a_i\|_\infty) \|\nabla v\|_2 \|1_E v\|_2$, where
$E = \{u > l\} \cap \{\nabla u \neq 0\}$ carries all of $\nabla v$. The Sobolev inequality
$\|v\|_{2^*} \le C \|\nabla v\|_2$ of Remark 20 on an arbitrary open set and Hölder's inequality on
$E$ turn this into $\alpha \le C' |E|^{1/N}$. So $|E| \ge c > 0$ for a $c$ independent of $l$,
unless $\nabla v = 0$; in that case $v = 0$ and $u \le l$. As $l$ rises to the essential supremum
$M$ of $u$, the sets $E$ decrease to $\{u = M\} \cap \{\nabla u \neq 0\}$. This set is null because
the weak gradient vanishes on level sets. Hence $M \le 0$.

The restriction $N \ge 3$ comes from the Sobolev inequality $\|v\|_{2^*} \le C \|\nabla v\|_2$. The
implementation notes of the module say what the cases $N \le 2$ would need.
-/

section GeneralDrift

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}
  {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

open SobolevMultiIndex

/-- Let $N \ge 3$ and let $\Omega \subseteq \mathbb{R}^N$ be open. There is $C \ge 0$ such that for
every $v \in H^1_0(\Omega)$ and every measurable set $s$ with $|s \cap \Omega| < \infty$,
$$\|1_s v\|_{L^2(\Omega)} \le C \|\nabla v\|_{L^2(\Omega)} |s \cap \Omega|^{1/N}.$$
This is the Sobolev inequality on $H^1_0(\Omega)$, localized to a set of small measure.

The proof uses Hölder's inequality with the exponents $2$ and $2^*$ on $s$, where
$1/2 = 1/2^* + 1/N$, and the inequality $\|v\|_{2^*} \le C(2, N) \|\nabla v\|_2$ of Remark 20 of
[brezis2011functional] on an arbitrary open set
(`SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq`). The norm $\|\nabla v\|_{L^2(\Omega)}$ is
`SobolevMultiIndex.gradNorm v`. -/
theorem exists_norm_indicator_bound (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω →
      ∀ s : Set (EuclideanSpace ℝ (Fin N)), MeasurableSet s →
      volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s ≠ ⊤ →
      (eLpNorm (s.indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ C * gradNorm v
          * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s).toReal ^ ((N : ℝ)⁻¹) := by
  have hN0 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : (N : ℝ)⁻¹ ≤ (3 : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 3 by norm_num) hN0
  have hd : (0 : ℝ) < (2 : ℝ)⁻¹ - (N : ℝ)⁻¹ := by norm_num at h1 ⊢; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = ((2 : ℝ)⁻¹ - (N : ℝ)⁻¹)⁻¹ :=
    ⟨Real.toNNReal _, Real.coe_toNNReal _ (by positivity)⟩
  have hqinv2 : ((q : ℝ))⁻¹ = (2 : ℝ)⁻¹ - (N : ℝ)⁻¹ := by rw [hq, inv_inv]
  have hqinv : ((q : ℝ))⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (N : ℝ)⁻¹ := by rw [hqinv2]; norm_num
  have hqN : (2 : ℝ≥0) < (N : ℝ≥0) := by
    have : (2 : ℕ) < N := by omega
    exact_mod_cast this
  have : Fact ((1 : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclideanZero N 1 2 Ω,
      eLpNorm (fn (v : SobolevEuclidean N 1 2 Ω)) (q : ℝ≥0∞)
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
        ≤ ENNReal.ofReal (C * gradNorm (v : SobolevEuclidean N 1 2 Ω)) :=
    ⟨(SobolevEuclidean.gnsConst N ((2 : ℝ≥0) : ℝ) : ℝ) * N, by positivity, fun v ↦ by
      simpa [mul_assoc] using
        SobolevEuclideanZero.eLpNorm_fn_le_gradNorm_of_eq (p := (2 : ℝ≥0)) (p' := q) hqN hqinv v⟩
  refine ⟨C, hC0, fun v hvmem s hs hfin ↦ ?_⟩
  have hCv := hC ⟨v, hvmem⟩
  have hgrad : 0 ≤ C * gradNorm v := mul_nonneg hC0 (gradNorm_nonneg _)
  have hqval : (2 : ℝ) ≤ (q : ℝ) := by
    rw [hq, le_inv_comm₀ (by norm_num) hd]
    norm_num
  have h2q : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    have h : ((2 : ℝ≥0)) ≤ q := by rwa [← NNReal.coe_le_coe, NNReal.coe_ofNat]
    calc (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := by norm_num
      _ ≤ (q : ℝ≥0∞) := ENNReal.coe_le_coe.2 h
  have hexp : 1 / (2 : ℝ≥0∞).toReal - 1 / ((q : ℝ≥0∞)).toReal = (N : ℝ)⁻¹ := by
    rw [ENNReal.coe_toReal, ENNReal.toReal_ofNat, one_div, one_div, hqinv2]
    ring
  have key : eLpNorm (s.indicator (fn v)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      ≤ ENNReal.ofReal (C * gradNorm v)
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s) ^ ((N : ℝ)⁻¹) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    have hmeas : AEStronglyMeasurable (fn v)
        ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))).restrict s) :=
      (SobolevMultiIndex.memLp _).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))).restrict s) h2q hmeas
    rw [Measure.restrict_apply_univ, hexp] at hh
    exact hh.trans (mul_le_mul' ((eLpNorm_restrict_le _ _ _ _).trans hCv) le_rfl)
  have hfin2 : ENNReal.ofReal (C * gradNorm v)
      * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) s) ^ ((N : ℝ)⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin)
  refine (ENNReal.toReal_mono hfin2 key).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hgrad, ← ENNReal.toReal_rpow]

/-- For $u \in H^1(\Omega)$ and $l \in \mathbb{R}$, the set $\{x : u(x) > l\} \cap \{x : \partial_i
u(x) \neq 0 \text{ for some } i\}$, where $u$ and $\partial_i u$ are the chosen representatives
(`SobolevMultiIndex.fn u` and the weak derivatives). -/
def levelGradSet (u : SobolevEuclidean N 1 2 Ω) (l : ℝ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | l < fn u x} ∩ {x | ∃ i, (weakDeriv u (MultiIndexLE.single i) :
    EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0}

/-- The set `Elliptic.levelGradSet u l` is measurable. It is the superlevel set of a strongly
measurable representative of $u$, intersected with the union over $i$ of the sets where
$\partial_i u$ does not vanish. -/
theorem measurableSet_levelGradSet (u : SobolevEuclidean N 1 2 Ω) (l : ℝ) :
    MeasurableSet (levelGradSet u l) := by
  refine MeasurableSet.inter (measurableSet_lt measurable_const ?_) ?_
  · exact (Lp.stronglyMeasurable (weakDeriv u 0)).measurable
  · rw [show {x | ∃ i, (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0}
      = ⋃ i : Fin N, {x | (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0} from by ext x; simp]
    exact MeasurableSet.iUnion fun i ↦
      (Lp.stronglyMeasurable (weakDeriv u (MultiIndexLE.single i))).measurable
        (measurableSet_singleton (0 : ℝ)).compl

/-- A point $x$ lies in `Elliptic.levelGradSet u l` if and only if $u(x) > l$ and
$\partial_i u(x) \neq 0$ for some $i$. -/
theorem mem_levelGradSet_iff {u : SobolevEuclidean N 1 2 Ω} {l : ℝ}
    {x : EuclideanSpace ℝ (Fin N)} :
    x ∈ levelGradSet u l ↔ l < fn u x ∧ ∃ i,
      (weakDeriv u (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0 := Iff.rfl

/-- The energy estimate in the proof of Theorem 8.1 of Gilbarg and Trudinger. Let
$\Omega \subseteq \mathbb{R}^N$ be open, let $a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic
with constant $\alpha$, let $a_i, a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$ almost everywhere,
and let $f \in L^2(\Omega)$ with $f \le 0$ almost everywhere. Let $u \in H^1(\Omega)$ satisfy
$a(u, \varphi) = \int_\Omega f \varphi$ for all $\varphi \in H^1_0(\Omega)$, where $a$ is the
form (41). Let $l \ge 0$, and let $v \in H^1_0(\Omega)$ have the function $(u - l)^+$. Then
$$\alpha \|\nabla v\|_2^2 \le \Big(\sum_i \|a_i\|_\infty\Big) \|\nabla v\|_2 \|1_E v\|_2,$$
where $E = \{u > l\} \cap \{\nabla u \neq 0\}$ is `Elliptic.levelGradSet u l`.

The estimate comes from the equation tested with $v$, after the nonnegative zeroth-order term
and the nonpositive load are dropped. The set $E$ is the only part of $\Omega$ on which
$\nabla v$ does not vanish. -/
theorem gradNorm_sq_le_of_posPart (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    {l : ℝ} (hl : 0 ≤ l) {v : SobolevEuclidean N 1 2 Ω}
    (hvmem : v ∈ SobolevEuclideanZero N 1 2 Ω)
    (hv : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
      fun x ↦ max (fn u x - l) 0) :
    α * gradNorm v ^ 2 ≤ (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
      * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
  classical
  have hEm := measurableSet_levelGradSet u l
  have hgLp : MemLp ((levelGradSet u l).indicator (fn v)) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
    (SobolevMultiIndex.memLp v).indicator hEm.nullMeasurableSet
  have hvi : ∀ i, (weakDeriv v (MultiIndexLE.single i) : EuclideanSpace ℝ (Fin N) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        {x | l < fn u x}.indicator (weakDeriv u (MultiIndexLE.single i)) := fun i ↦
    SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart_sub_const hv i
  have hall := ae_all_iff.2 hvi
  -- the principal part
  have hP : ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ
      = ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv v (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_mulL_eq_integral, inner_mulL_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hall] with x hx
    by_cases hxl : l < fn u x
    · rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl)]
    · rw [hx j, Set.indicator_of_notMem (show x ∉ {y | l < fn u y} from hxl), mul_zero, mul_zero]
  have hPge : α * gradNorm v ^ 2
      ≤ ∑ i : Fin N, ∑ j : Fin N, ⟪mulL Ω (A i j) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v (MultiIndexLE.single j)⟫_ℝ := by
    rw [hP, gradNorm_eq_sqrt, Real.sq_sqrt (by positivity)]
    exact sum_inner_mulL_ge Ω hA v
  -- the zeroth-order term
  have hZ : 0 ≤ ⟪mulL Ω a₀ (weakDeriv u 0), weakDeriv v 0⟫_ℝ := by
    rw [inner_mulL_eq_integral]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ha₀, hv] with x hx hxv
    change 0 ≤ a₀ x * fn u x * fn v x
    rw [hxv]
    rcases le_total (fn u x) l with h | h
    · rw [max_eq_right (by linarith), mul_zero]
    · rw [max_eq_left (by linarith)]
      have : 0 ≤ fn u x := le_trans hl h
      positivity
  -- the load
  have hR : ⟪f, weakDeriv v 0⟫_ℝ ≤ 0 := by
    rw [L2.inner_eq_integral_mul]
    refine integral_nonpos_of_ae ?_
    filter_upwards [hf, hv] with x hx hxv
    change f x * fn v x ≤ 0
    rw [hxv]
    exact mul_nonpos_of_nonpos_of_nonneg hx (le_max_right _ _)
  -- the drift term
  have hgnorm : ‖hgLp.toLp ((levelGradSet u l).indicator (fn v))‖
      = (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hgLp.coeFn_toLp]
  have hDeq : ∀ i, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)), weakDeriv v 0⟫_ℝ
      = ⟪mulL Ω (a₁ i) (weakDeriv v (MultiIndexLE.single i)),
        hgLp.toLp ((levelGradSet u l).indicator (fn v))⟫_ℝ := by
    intro i
    rw [inner_mulL_eq_integral, inner_mulL_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hall, hv, hgLp.coeFn_toLp] with x hx hxv hxg
    simp only [SobolevMultiIndex.weakDeriv_zero]
    rw [hxg]
    by_cases hxl : l < fn u x
    · by_cases hxD : ∃ j, (weakDeriv u (MultiIndexLE.single j) :
          EuclideanSpace ℝ (Fin N) → ℝ) x ≠ 0
      · rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl),
          Set.indicator_of_mem (show x ∈ levelGradSet u l from ⟨hxl, hxD⟩)]
      · push Not at hxD
        rw [hx i, Set.indicator_of_mem (show x ∈ {y | l < fn u y} from hxl), hxD i,
          mul_zero, zero_mul, zero_mul]
    · have hnot : x ∉ levelGradSet u l := fun hx' ↦ hxl hx'.1
      rw [hx i, Set.indicator_of_notMem (show x ∉ {y | l < fn u y} from hxl),
        Set.indicator_of_notMem hnot, hxv,
        max_eq_right (by linarith [not_lt.1 hxl]), mul_zero, mul_zero]
  have hDbd : |∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
        weakDeriv v 0⟫_ℝ|
      ≤ (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
        * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal := by
    rw [← hgnorm, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [hDeq i]
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (norm_mulL_apply_le Ω _ _).trans
      (mul_le_mul_of_nonneg_left (norm_weakDeriv_single_le_gradNorm v i) (norm_nonneg _))
  -- put the pieces together
  have e := heq v hvmem
  rw [generalForm_apply_inner, load_apply_inner] at e
  have hle : -∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
      weakDeriv v 0⟫_ℝ ≤ |∑ i : Fin N, ⟪mulL Ω (a₁ i) (weakDeriv u (MultiIndexLE.single i)),
      weakDeriv v 0⟫_ℝ| := neg_le_abs _
  linarith [hPge, hZ, hR, hDbd, hle]

/-- Let $u \in H^1(\Omega)$, and let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on
$\bar\Omega$ and equal to $u$ almost everywhere on $\Omega$, with $\tilde u \le 0$ on
$\partial\Omega$. Then for every $l \ge 0$ there is $v \in H^1_0(\Omega)$ whose function is
$(u - l)^+$ almost everywhere on $\Omega$.

The function $(u - l)^+$ lies in $H^1(\Omega)$ by `MemSobolevMultiIndex.posPart_sub_const`. Its
continuous representative $(\tilde u - l)^+$ vanishes on $\partial\Omega$, so Theorem 9.17, (i)
implies (ii), of [brezis2011functional] applies. -/
theorem exists_posPart_mem_zero {u : SobolevEuclidean N 1 2 Ω}
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hcont : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    {l : ℝ} (hl : 0 ≤ l) :
    ∃ v : SobolevEuclidean N 1 2 Ω, v ∈ SobolevEuclideanZero N 1 2 Ω ∧
      fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))]
        fun x ↦ max (fn u x - l) 0 := by
  obtain ⟨v, hv⟩ := ((memSobolevMultiIndex u).posPart_sub_const
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hl).exists_sobolevMultiIndex
  refine ⟨v, ?_, hv⟩
  refine SobolevEuclideanZero.mem_of_continuousOn_closure_of_eqOn_frontier ENNReal.ofNat_ne_top
    v (ũ := fun x ↦ max (ũ x - l) 0) ?_ ?_ fun x hx ↦ ?_
  · filter_upwards [hv, hu] with x hx hx'
    rw [hx, hx']
  · exact ((continuous_id.sub continuous_const).max continuous_const).comp_continuousOn hcont
  · exact max_eq_right (by linarith [hΓ x hx])

/-- The key dichotomy in the proof of Theorem 8.1 of Gilbarg and Trudinger. Let $N \ge 3$ and let
$\Omega \subseteq \mathbb{R}^N$ be open. Let $a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic
with constant $\alpha$, let $a_i, a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$ almost everywhere,
and let $f \in L^2(\Omega)$ with $f \le 0$ almost everywhere. Let $u \in H^1(\Omega)$ satisfy
$a(u, \varphi) = \int_\Omega f \varphi$ for all $\varphi \in H^1_0(\Omega)$, where $a$ is the
form (41). Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ and equal
to $u$ almost everywhere on $\Omega$, with $\tilde u \le 0$ on $\partial\Omega$. Then there is
$c > 0$ such that for every $l \ge 0$, either $u \le l$ almost everywhere on $\Omega$, or
$$|\{u > l\} \cap \{\nabla u \neq 0\} \cap \Omega| \ge c.$$

The statement says only that $c$ does not depend on $l$; the proof gives a $c$ that depends only
on $\alpha$, the norms $\|a_i\|_\infty$, $N$ and the Sobolev constant. The proof combines the
energy estimate of `Elliptic.gradNorm_sq_le_of_posPart` for $v = (u - l)^+$ with
$\|1_E v\|_2 \le C \|\nabla v\|_2 |E|^{1/N}$ (`Elliptic.exists_norm_indicator_bound`). When
$\nabla v = 0$, the truncation $v$ itself vanishes, because $v \in H^1_0(\Omega)$. -/
theorem exists_measure_levelGradSet_ge (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hcont : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ l : ℝ, 0 ≤ l →
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l) ∨
        ENNReal.ofReal c
          ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) := by
  have hN0 : N ≠ 0 := by omega
  have hα : 0 < α := hA.1
  obtain ⟨C, hC0, hC⟩ := exists_norm_indicator_bound (Ω := Ω) hN
  have hΛ : 0 ≤ ∑ i : Fin N, ‖a₁ i‖ := Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  have hden : 0 < (∑ i : Fin N, ‖a₁ i‖) * C + 1 := by positivity
  refine ⟨(α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ), Real.rpow_pos_of_pos (by positivity) _,
    fun l hl ↦ ?_⟩
  obtain ⟨v, hvmem, hv⟩ := exists_posPart_mem_zero hu hcont hΓ hl
  rcases eq_or_lt_of_le (gradNorm_nonneg v) with hG | hG
  · -- the gradient of the truncation vanishes, hence so does the truncation
    left
    have hgi : ∀ i, weakDeriv v (MultiIndexLE.single i) = 0 := fun i ↦ by
      have := norm_weakDeriv_single_le_gradNorm v i
      rw [← hG] at this
      exact norm_le_zero_iff.1 this
    have h0 : (⟨v, hvmem⟩ : SobolevEuclideanZero N 1 2 Ω) = 0 :=
      SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero hN0 ENNReal.ofNat_ne_top _ hgi
    have h0' : v = 0 := congrArg Subtype.val h0
    filter_upwards [hv, show fn (0 : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] 0 from fn_zero] with x hx hx0
    rw [h0', hx0, Pi.zero_apply] at hx
    have := le_max_left (fn u x - l) 0
    rw [← hx] at this
    linarith
  · right
    by_cases hfin : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) = ⊤
    · rw [hfin]; exact le_top
    have key1 := gradNorm_sq_le_of_posPart hA ha₀ heq hf hl hvmem hv
    have key2 := hC v hvmem (levelGradSet u l) (measurableSet_levelGradSet u l) hfin
    have htnn : (0 : ℝ) ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
        (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h3 : (∑ i : Fin N, ‖a₁ i‖) * gradNorm v
        * (eLpNorm ((levelGradSet u l).indicator (fn v)) 2
          (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))).toReal
        ≤ ((∑ i : Fin N, ‖a₁ i‖) * C
            * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
              (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹)) * gradNorm v ^ 2 := by
      have := mul_le_mul_of_nonneg_left key2 (mul_nonneg hΛ hG.le)
      nlinarith [this]
    have h4 : α * gradNorm v ^ 2
        ≤ ((∑ i : Fin N, ‖a₁ i‖) * C
            * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
              (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹)) * gradNorm v ^ 2 := by linarith
    have h5 : α ≤ (∑ i : Fin N, ‖a₁ i‖) * C
        * (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
          (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) :=
      le_of_mul_le_mul_right h4 (pow_pos hG 2)
    have h6 : α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)
        ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
          (levelGradSet u l)).toReal ^ ((N : ℝ)⁻¹) := by
      rw [div_le_iff₀ hden]
      nlinarith [htnn, h5]
    have h7 : (α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ)
        ≤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l)).toReal := by
      refine (Real.rpow_le_rpow (by positivity) h6 (by positivity)).trans_eq ?_
      rw [← Real.rpow_mul ENNReal.toReal_nonneg, inv_mul_cancel₀ (by positivity : (N : ℝ) ≠ 0),
        Real.rpow_one]
    calc ENNReal.ofReal ((α / ((∑ i : Fin N, ‖a₁ i‖) * C + 1)) ^ (N : ℝ))
        ≤ ENNReal.ofReal ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
            (levelGradSet u l)).toReal) := ENNReal.ofReal_le_ofReal h7
      _ = volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l) :=
          ENNReal.ofReal_toReal hfin


/-- For $u \in H^1(\Omega)$ and $t > 0$, the superlevel set $\{u > t\} \cap \Omega$ has finite
measure. This is Chebyshev's inequality for the $L^2$ function $u$. -/
theorem measure_lt_fn_ne_top (u : SobolevEuclidean N 1 2 Ω) {t : ℝ} (ht : 0 < t) :
    volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) {x | t < fn u x} ≠ ⊤ := by
  have hsub : {x | t < fn u x} ⊆ {x | t.toNNReal ≤ ‖fn u x‖₊} := by
    intro x hx
    have hx' : t < fn u x := hx
    have : t ≤ ‖fn u x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    simpa [← NNReal.coe_le_coe, Real.coe_toNNReal t ht.le] using this
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  exact ((SobolevMultiIndex.memLp u).meas_ge_lt_top (by norm_num) ENNReal.ofNat_ne_top
    (by simpa using ht)).ne

/-- Let $u \in H^1(\Omega)$ and $c > 0$. Suppose that for every $l \ge 0$, either $u \le l$ almost
everywhere on $\Omega$, or $|\{u > l\} \cap \{\nabla u \neq 0\} \cap \Omega| \ge c$. Then
$u \le 0$ almost everywhere on $\Omega$.

The infimum $M$ of the almost-everywhere bounds of $u$ is attained. If $M$ were positive, the
sets $\{u > M - M/(n+2)\} \cap \{\nabla u \neq 0\}$ would all have measure at least $c$, while
they decrease to $\{u = M\} \cap \{\nabla u \neq 0\}$. That set is null because the weak
gradient vanishes on level sets (`SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq`). -/
theorem nonpos_ae_of_forall_le_measure_levelGradSet {u : SobolevEuclidean N 1 2 Ω} {c : ℝ}
    (hc0 : 0 < c)
    (hdich : ∀ l : ℝ, 0 ≤ l →
      (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l) ∨
        ENNReal.ofReal c
          ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))) (levelGradSet u l)) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ 0 := by
  classical
  have hcE : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.2 hc0
  have hmeas : ∀ t : ℝ, MeasurableSet {x | t < fn u x} := fun t ↦
    measurableSet_lt measurable_const (Lp.stronglyMeasurable (weakDeriv u 0)).measurable
  have hsubset : ∀ t : ℝ, levelGradSet u t ⊆ {x | t < fn u x} := fun _ ↦ inter_subset_left
  obtain ⟨L, hLdef⟩ : ∃ L : Set ℝ, L = {l : ℝ | 0 ≤ l ∧
    ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l} := ⟨_, rfl⟩
  have hLmem : ∀ l : ℝ, l ∈ L ↔ 0 ≤ l ∧
      ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ l := by
    rw [hLdef]; exact fun l ↦ Iff.rfl
  -- `L` is nonempty: `u ∈ L²(Ω)`, so `|{u > n}| → 0`
  have hLne : L.Nonempty := by
    have hanti : Antitone fun n : ℕ ↦ {x | ((n : ℝ) + 1) < fn u x} := by
      intro m n hmn x hx
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hx' : (n : ℝ) + 1 < fn u x := hx
      exact show (m : ℝ) + 1 < fn u x from by linarith
    have hempty : ⋂ n : ℕ, {x | ((n : ℝ) + 1) < fn u x} = ∅ := by
      ext x
      simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (fn u x)
      exact ⟨n, fun hcon ↦ absurd (show (n : ℝ) + 1 < fn u x from hcon) (by linarith)⟩
    have htend := tendsto_measure_iInter_atTop
      (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
      (fun n : ℕ ↦ (hmeas ((n : ℝ) + 1)).nullMeasurableSet) hanti
      ⟨0, by simpa using measure_lt_fn_ne_top u (t := ((0 : ℕ) : ℝ) + 1) (by norm_num)⟩
    rw [hempty, measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (eventually_lt_nhds hcE)).exists
    refine ⟨(n : ℝ) + 1, (hLmem _).2 ⟨by positivity, ?_⟩⟩
    rcases hdich ((n : ℝ) + 1) (by positivity) with h | h
    · exact h
    · exact absurd (h.trans (measure_mono (hsubset _))) (by simpa using hn.not_ge)
  have hLbdd : BddBelow L := ⟨0, fun a ha ↦ ((hLmem a).1 ha).1⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = sInf L := ⟨_, rfl⟩
  have hMle : ∀ l ∈ L, M ≤ l := fun l hl ↦ hMdef ▸ csInf_le hLbdd hl
  -- the infimum is attained
  have hML : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn u x ≤ M := by
    have hex : ∀ k : ℕ, ∃ a ∈ L, a < M + 1 / ((k : ℝ) + 1) := fun k ↦
      exists_lt_of_csInf_lt hLne (by
        have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        rw [← hMdef]; linarith)
    choose a haL haM using hex
    have htendM : Tendsto (fun k : ℕ ↦ M + 1 / ((k : ℝ) + 1)) atTop (𝓝 M) := by
      have h0 : Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ M) atTop (𝓝 M)).add h0
    filter_upwards [ae_all_iff.2 fun k ↦ ((hLmem _).1 (haL k)).2] with x hx
    exact ge_of_tendsto htendM (Eventually.of_forall fun k ↦ (hx k).trans (haM k).le)
  -- the infimum is `0`
  refine hML.mono fun x hx ↦ hx.trans ?_
  by_contra hMpos
  push Not at hMpos
  have hlpos : ∀ n : ℕ, 0 < M - M / ((n : ℝ) + 2) := fun n ↦ by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : M / ((n : ℝ) + 2) < M := by
      rw [div_lt_iff₀ h2]; nlinarith
    linarith
  have hlt : ∀ n : ℕ, M - M / ((n : ℝ) + 2) < M := fun n ↦ by
    have : (0 : ℝ) < M / ((n : ℝ) + 2) := by positivity
    linarith
  have hmono : Monotone fun n : ℕ ↦ M - M / ((n : ℝ) + 2) := by
    intro m n hmn
    have hm : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have : M / ((n : ℝ) + 2) ≤ M / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hMpos.le (by positivity) hm
    simp only
    linarith
  have hlim : Tendsto (fun n : ℕ ↦ M - M / ((n : ℝ) + 2)) atTop (𝓝 M) := by
    have h1 : Tendsto (fun n : ℕ ↦ M / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa using h2.const_div_atTop M
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ M) atTop (𝓝 M)).sub h1
  have hge : ∀ n : ℕ, ENNReal.ofReal c ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
      (levelGradSet u (M - M / ((n : ℝ) + 2))) := fun n ↦ by
    rcases hdich _ (hlpos n).le with h | h
    · exact absurd (hMle _ ((hLmem _).2 ⟨(hlpos n).le, h⟩)) (not_le.2 (hlt n))
    · exact h
  -- the sets shrink to a null set
  have hlevel : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      ∀ i, fn u x = M → (weakDeriv u (MultiIndexLE.single i) :
        EuclideanSpace ℝ (Fin N) → ℝ) x = 0 :=
    ae_all_iff.2 fun i ↦ SobolevMultiIndex.weakDeriv_single_ae_eq_zero_of_fn_eq u M i
  have hnull : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))
      (⋂ n : ℕ, levelGradSet u (M - M / ((n : ℝ) + 2))) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hML, hlevel] with x h1 h2 hmem
    rw [mem_iInter] at hmem
    have hev : ∀ n : ℕ, M - M / ((n : ℝ) + 2) ≤ fn u x := fun n ↦ le_of_lt (hmem n).1
    obtain ⟨i, hi⟩ := (hmem 0).2
    exact hi (h2 i (le_antisymm h1 (le_of_tendsto hlim (Eventually.of_forall hev))))
  have hanti2 : Antitone fun n : ℕ ↦ levelGradSet u (M - M / ((n : ℝ) + 2)) :=
    fun m n hmn x hx ↦ ⟨lt_of_le_of_lt (hmono hmn) hx.1, hx.2⟩
  have htend2 := tendsto_measure_iInter_atTop
    (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))
    (fun n : ℕ ↦ (measurableSet_levelGradSet u _).nullMeasurableSet) hanti2
    ⟨0, ne_top_of_le_ne_top (measure_lt_fn_ne_top u (hlpos 0)) (measure_mono (hsubset _))⟩
  rw [hnull] at htend2
  exact absurd (ge_of_tendsto htend2 (Eventually.of_forall hge)) (by simpa using hcE.ne')


/-- Let $N \ge 3$ and let $\Omega \subseteq \mathbb{R}^N$ be open. Let $a_{ij} \in L^\infty(\Omega)$
be uniformly elliptic with constant $\alpha$, let $a_i \in L^\infty(\Omega)$ be arbitrary, let
$a_0 \in L^\infty(\Omega)$ with $a_0 \ge 0$ almost everywhere, and let $f \in L^2(\Omega)$. Let
$u \in H^1(\Omega)$ satisfy
$$\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi + \sum_i \int_\Omega a_i
  \partial_i u\, \varphi + \int_\Omega a_0 u \varphi = \int_\Omega f \varphi \qquad \text{for
  all } \varphi \in H^1_0(\Omega).$$
Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ and equal to $u$
almost everywhere on $\Omega$. If $\tilde u \le 0$ on $\partial\Omega$ and $f \le 0$ almost
everywhere on $\Omega$, then $\tilde u \le 0$ on $\Omega$. This is (79') of Proposition 9.29 of
[brezis2011functional] in the generality that the source states, proved as Theorem 8.1 of
Gilbarg and Trudinger, *Elliptic Partial Differential Equations of Second Order*.

The proof combines `Elliptic.exists_measure_levelGradSet_ge` and
`Elliptic.nonpos_ae_of_forall_le_measure_levelGradSet`. -/
theorem nonpos_of_nonpos_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ 0)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ 0 := by
  obtain ⟨c, hc0, hdich⟩ := exists_measure_levelGradSet_ge hN hA ha₀ heq hf hu hc hΓ
  have hae := nonpos_ae_of_forall_le_measure_levelGradSet hc0 hdich
  refine forall_le_of_ae_le_of_continuousOn (hc.mono subset_closure) ?_
  filter_upwards [hae, hu] with x hx hx'
  rw [← hx']
  exact hx

/-- Under the hypotheses of `Elliptic.nonpos_of_nonpos_frontier_general` on $N \ge 3$, $\Omega$,
$a_{ij}$, $a_i$, $a_0 \ge 0$, $f$, $u$ and $\tilde u$: if $\tilde u \ge 0$ on $\partial\Omega$
and $f \ge 0$ almost everywhere on $\Omega$, then $\tilde u \ge 0$ on $\Omega$. This is (79) of
Proposition 9.29 of [brezis2011functional] for a solution $u \in H^1(\Omega) \cap C(\bar\Omega)$
of (78), proved as Theorem 8.1 of Gilbarg and Trudinger.

The proof applies the form (79'), `Elliptic.nonpos_of_nonpos_frontier_general`, to $-u$ and
$-f$. -/
theorem nonneg_of_nonneg_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ a₀ x)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ a₀ u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) (hΓ : ∀ x ∈ frontier (Ω : Set _), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, 0 ≤ ũ x := by
  have h := nonpos_of_nonpos_frontier_general hN hA ha₀
    (forall_generalForm_neg_eq_load_neg A a₁ a₀ _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_le_neg hf)
  intro x hx
  simpa using h x hx

/-- Let $c \in H^1(\Omega)$ have $\partial_i c = 0$ for every $i$. Then the form $a(u, \varphi) =
\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi + \sum_i \int_\Omega a_i
\partial_i u\, \varphi$, the case $a_0 = 0$ of (41), satisfies
$a(u - c, \varphi) = a(u, \varphi)$ for all $u, \varphi \in H^1(\Omega)$. Neither the principal
part nor the drift term depends on the function itself. -/
theorem generalForm_zero_sub_apply
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (a₁ : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    {u c : SobolevEuclidean N 1 2 Ω} (hc : ∀ i, weakDeriv c (MultiIndexLE.single i) = 0)
    (φ : SobolevEuclidean N 1 2 Ω) :
    generalForm Ω A a₁ 0 (u - c) φ = generalForm Ω A a₁ 0 u φ := by
  have e : ∀ i, weakDeriv (u - c) (MultiIndexLE.single i) = weakDeriv u (MultiIndexLE.single i) :=
    fun i ↦ by
      rw [show weakDeriv (u - c) (MultiIndexLE.single i)
        = weakDeriv u (MultiIndexLE.single i) - weakDeriv c (MultiIndexLE.single i) from rfl, hc i,
        sub_zero]
  rw [generalForm_apply_inner, generalForm_apply_inner]
  simp only [e, mulL_zero, zero_apply, inner_zero_left, add_zero]

/-- Let $N \ge 3$, let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| < \infty$, let
$a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic, let $a_i \in L^\infty(\Omega)$, let
$f \in L^2(\Omega)$, and let $u \in H^1(\Omega)$ satisfy $\sum_{i,j} \int_\Omega a_{ij}
\partial_i u\, \partial_j \varphi + \sum_i \int_\Omega a_i \partial_i u\, \varphi = \int_\Omega
f \varphi$ for all $\varphi \in H^1_0(\Omega)$. Let $\tilde u : \mathbb{R}^N \to \mathbb{R}$ be
continuous on $\bar\Omega$ and equal to $u$ almost everywhere on $\Omega$. If $f \ge 0$ almost
everywhere on $\Omega$ and $K \le \tilde u$ on $\partial\Omega$, then $K \le \tilde u$ on
$\Omega$. This is $u \ge \inf_\Gamma u$, (80) of Proposition 9.29 of [brezis2011functional],
with $a_0 = 0$.

The source assumes $\Omega$ bounded; here $|\Omega| < \infty$ suffices. The constant $K$ lies in
$H^1(\Omega)$ with zero gradient (`Elliptic.exists_const_of_measure_ne_top`). Then $u - K$
satisfies the same equation, because the form has no zeroth-order term
(`Elliptic.generalForm_zero_sub_apply`), and (79) applies to $u - K$. -/
theorem ge_iInf_frontier_of_nonneg (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ f x) :
    ∀ x ∈ Ω, K ≤ ũ x := by
  obtain ⟨cK, hcK, hc0⟩ := exists_const_of_measure_ne_top hΩ K
  have h := nonneg_of_nonneg_frontier_general hN hA (a₀ := 0)
    (by filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))]
      with x hx; rw [hx]; exact le_rfl)
    (u := u - cK) (fun φ hφ ↦ by rw [generalForm_zero_sub_apply A a₁ hc0, heq φ hφ])
    (ũ := fun x ↦ ũ x - K) ?_ (hc.sub continuousOn_const)
    (fun x hx ↦ by linarith [hΓ x hx]) hf
  · intro x hx
    linarith [h x hx]
  · filter_upwards [fn_sub u cK, hu, hcK] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'']

/-- Under the hypotheses of `Elliptic.ge_iInf_frontier_of_nonneg` on $N \ge 3$, $\Omega$ with
$|\Omega| < \infty$, $a_{ij}$, $a_i$, $a_0 = 0$, $f$, $u$ and $\tilde u$: if $f \le 0$ almost
everywhere on $\Omega$ and $\tilde u \le K$ on $\partial\Omega$, then $\tilde u \le K$ on
$\Omega$. This is $u \le \sup_\Gamma u$, which appears in the proof of (80) in Proposition 9.29
of [brezis2011functional]. -/
theorem le_iSup_frontier_of_nonpos (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤)
    {u : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω f φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ≤ K)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), f x ≤ 0) :
    ∀ x ∈ Ω, ũ x ≤ K := by
  have h := ge_iInf_frontier_of_nonneg hN hA hΩ
    (forall_generalForm_neg_eq_load_neg A a₁ 0 _ heq) (ũ := -ũ) ((fn_neg u).trans hu.neg) hc.neg
    (K := -K) (fun x hx ↦ by simpa using hΓ x hx) (by simpa using ae_neg_ge_neg hf)
  intro x hx
  simpa using h x hx

/-- Let $N \ge 3$, let $\Omega \subseteq \mathbb{R}^N$ be open with $|\Omega| < \infty$, let
$a_{ij} \in L^\infty(\Omega)$ be uniformly elliptic, let $a_i \in L^\infty(\Omega)$, and let
$u \in H^1(\Omega)$ satisfy $\sum_{i,j} \int_\Omega a_{ij} \partial_i u\, \partial_j \varphi +
\sum_i \int_\Omega a_i \partial_i u\, \varphi = 0$ for all $\varphi \in H^1_0(\Omega)$. Let
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\bar\Omega$ and equal to $u$ almost
everywhere on $\Omega$. If $K_1 \le \tilde u \le K_2$ on $\partial\Omega$, then
$K_1 \le \tilde u \le K_2$ on $\Omega$. This is $\inf_\Gamma u \le u \le \sup_\Gamma u$, (81) of
Proposition 9.29 of [brezis2011functional], with $a_0 = 0$ and $f = 0$.

The proof combines the lower bound $u \ge \inf_\Gamma u$ of (80),
`Elliptic.ge_iInf_frontier_of_nonneg`, and the upper bound $u \le \sup_\Gamma u$,
`Elliptic.le_iSup_frontier_of_nonpos`, both with $f = 0$. -/
theorem mem_Icc_of_frontier_general (hN : 3 ≤ N) (hA : IsUniformlyElliptic Ω A α)
    (hΩ : volume (Ω : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤) {u : SobolevEuclidean N 1 2 Ω}
    (heq : ∀ φ ∈ SobolevEuclideanZero N 1 2 Ω, generalForm Ω A a₁ 0 u φ = load Ω 0 φ)
    {ũ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hu : fn u =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] ũ)
    (hc : ContinuousOn ũ (closure Ω)) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set _), ũ x ∈ Icc K₁ K₂) :
    ∀ x ∈ Ω, ũ x ∈ Icc K₁ K₂ := by
  have h0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))),
      (0 : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) x = 0 :=
    Lp.coeFn_zero ℝ 2 _
  intro x hx
  exact ⟨ge_iInf_frontier_of_nonneg hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).1)
      (h0.mono fun y hy ↦ hy.symm.le) x hx,
    le_iSup_frontier_of_nonpos hN hA hΩ heq hu hc (fun y hy ↦ (hΓ y hy).2)
      (h0.mono fun y hy ↦ hy.le) x hx⟩


end GeneralDrift

/-! ### Remark 27: the classical maximum principle for the Laplacian -/

section Classical

open Laplacian

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The **classical maximum principle for the Laplacian**. Let $\Omega \subseteq \mathbb{R}^N$ be
open and bounded, and let $\tilde u, f : \mathbb{R}^N \to \mathbb{R}$, with $\tilde u$
continuous on $\bar\Omega$ and of class $C^2$ on $\Omega$, satisfy
$-\Delta \tilde u + \tilde u = f$ on $\Omega$. If $\tilde u \le K$ on $\partial\Omega$ and
$f \le K$ on $\Omega$, then $\tilde u \le K$ on $\Omega$. This is the classical proof of Theorem
9.27 in Remark 27 of [brezis2011functional], Chapter 9, for the Laplacian.

The maximum of $\tilde u$ on the compact set $\bar\Omega$ is attained at some $x_0$. If
$x_0 \in \partial\Omega$ there is nothing to prove. If $x_0 \in \Omega$, then
$\Delta \tilde u(x_0) \le 0$ (`IsLocalMax.laplacian_nonpos`), so $\tilde u(x_0) = f(x_0) +
\Delta \tilde u(x_0) \le f(x_0) \le K$. -/
theorem le_of_classical_laplacian (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {ũ f : EuclideanSpace ℝ (Fin N) → ℝ} (hc : ContinuousOn ũ (closure Ω))
    (hu : ContDiffOn ℝ 2 ũ Ω) (heq : ∀ x ∈ Ω, -Δ ũ x + ũ x = f x) {K : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), ũ x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, ũ x ≤ K := by
  intro x hx
  obtain ⟨x₀, hx₀, hmax⟩ := hΩ.isCompact_closure.exists_isMaxOn ⟨x, subset_closure hx⟩ hc
  refine (hmax (subset_closure hx)).trans ?_
  rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hx₀
  rcases hx₀ with hx₀ | hx₀
  · have hloc : IsLocalMax ũ x₀ :=
      hmax.isLocalMax (mem_of_superset (Ω.isOpen.mem_nhds hx₀) subset_closure)
    have hΔ := hloc.laplacian_nonpos (hu.contDiffAt (Ω.isOpen.mem_nhds hx₀))
    have := heq x₀ hx₀
    linarith [hf x₀ hx₀]
  · exact hΓ x₀ hx₀

end Classical

/-! ### Remark 27: the classical maximum principle for a general elliptic operator -/

section ClassicalGeneral

open scoped MatrixOrder ComplexOrder

/-- Let $A \in \mathbb{R}^{N \times N}$ be positive semidefinite, and let $D$ be a continuous
bilinear form on $\mathbb{R}^N$ with $D(v, v) \le 0$ for every $v$. Then
$$\sum_{i,j} A_{ij} D(e_i, e_j) \le 0.$$

Write $A = S S$ with the positive semidefinite square root $S$ of $A$ (`CFC.sqrt`), which is
symmetric. Then the sum is $\sum_k D(S e_k, S e_k)$. -/
theorem _root_.Matrix.PosSemidef.sum_mul_apply_single_nonpos {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosSemidef)
    (D : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
    (hD : ∀ v, D v v ≤ 0) :
    ∑ i, ∑ j, A i j * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ 0 := by
  obtain ⟨S, hS⟩ : ∃ S, S = CFC.sqrt A := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact CFC.sqrt_nonneg A
  have hSS : S * S = A := by rw [hS]; exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hSsymm : ∀ i j, S i j = S j i := fun i j ↦ by
    have h := (Matrix.nonneg_iff_posSemidef.1 hS0).1
    have := congrFun (congrFun h j) i
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w : Fin N → EuclideanSpace ℝ (Fin N),
      ∀ k, w k = ∑ i, S k i • EuclideanSpace.single i (1 : ℝ) := ⟨_, fun _ ↦ rfl⟩
  have key : ∀ k, D (w k) (w k) = ∑ i, ∑ j, S k i * S k j
      * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun k ↦ by
    simp only [hw, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  calc ∑ i, ∑ j, A i j * D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
      = ∑ k, D (w k) (w k) := by
        simp only [key, ← hSS, Matrix.mul_apply, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hSsymm i k]
    _ ≤ 0 := Finset.sum_nonpos fun k _ ↦ hD (w k)

/-- Let $(a_{ij}) \in \mathbb{R}^{N \times N}$ be symmetric with
$\sum_{i,j} a_{ij} \xi_i \xi_j \ge 0$ for every $\xi \in \mathbb{R}^N$. Then the matrix
$(a_{ij})$ is positive semidefinite. -/
theorem _root_.Matrix.posSemidef_of_of_symm_of_nonneg {N : ℕ} {a : Fin N → Fin N → ℝ}
    (hsymm : ∀ i j, a i j = a j i)
    (hnn : ∀ ξ : EuclideanSpace ℝ (Fin N), 0 ≤ ∑ i, ∑ j, a i j * ξ i * ξ j) :
    (Matrix.of a).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun i j ↦ ?_)
    fun x ↦ ?_
  · simp [hsymm i j]
  · have h := hnn (WithLp.toLp 2 x)
    simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply, Finset.mul_sum]
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- The **classical maximum principle for a general second-order elliptic operator**. Let
$\Omega \subseteq \mathbb{R}^N$ be open and bounded. Let $a_{ij} : \mathbb{R}^N \to \mathbb{R}$
be differentiable on $\Omega$, with $a_{ij} = a_{ji}$ and
$\sum_{i,j} a_{ij}(x) \xi_i \xi_j \ge 0$ for every $x \in \Omega$ and $\xi \in \mathbb{R}^N$,
and let $b_i : \mathbb{R}^N \to \mathbb{R}$ be arbitrary. Let
$\tilde u, f : \mathbb{R}^N \to \mathbb{R}$, with $\tilde u$ continuous on $\bar\Omega$ and of
class $C^2$ on $\Omega$, satisfy
$$-\sum_{i,j} \partial_j (a_{ij} \partial_i \tilde u) + \sum_i b_i \partial_i \tilde u + \tilde
  u = f \qquad \text{on } \Omega.$$
If $\tilde u \le K$ on $\partial\Omega$ and $f \le K$ on $\Omega$, then $\tilde u \le K$ on
$\Omega$. This is Remark 27 of [brezis2011functional], Chapter 9. The Laplacian is the case
$a_{ij} = \delta_{ij}$, $b = 0$ (`Elliptic.le_of_classical_laplacian`).

Of the ellipticity condition, only $\sum_{i,j} a_{ij}(x) \xi_i \xi_j \ge 0$ is used. The maximum
of $\tilde u$ on the compact set $\bar\Omega$ is attained at some $x_0$; if
$x_0 \in \partial\Omega$ there is nothing to prove. If $x_0 \in \Omega$, then
$\nabla \tilde u(x_0) = 0$ (`IsLocalMax.fderiv_eq_zero`) and the Hessian is nonpositive
(`IsLocalMax.fderiv_fderiv_apply_self_nonpos`). By the product rule, $\partial_j (a_{ij}
\partial_i \tilde u)(x_0) = a_{ij}(x_0) \partial_i \partial_j \tilde u(x_0)$, and the
first-order term vanishes. The source gets $\sum_{i,j} a_{ij}(x_0) \partial_i \partial_j \tilde
u(x_0) \le 0$ by a change of coordinates that diagonalizes $(a_{ij}(x_0))$; here it is
`Matrix.PosSemidef.sum_mul_apply_single_nonpos`, through the square root of $(a_{ij}(x_0))$.
Hence $\tilde u(x_0) = f(x_0) + \sum_{i,j} a_{ij}(x_0) \partial_i \partial_j \tilde u(x_0) \le
f(x_0) \le K$. -/
theorem le_of_classical (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin N))))
    {ũ f : EuclideanSpace ℝ (Fin N) → ℝ} (hc : ContinuousOn ũ (closure Ω))
    (hu : ContDiffOn ℝ 2 ũ Ω) {a : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (ha : ∀ i j, DifferentiableOn ℝ (a i j) Ω) (hsymm : ∀ i j, a i j = a j i)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin N), 0 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j)
    {b : Fin N → EuclideanSpace ℝ (Fin N) → ℝ}
    (heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ ũ y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, b i x * fderiv ℝ ũ x (EuclideanSpace.single i 1)) + ũ x = f x)
    {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin N))), ũ x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, ũ x ≤ K := by
  intro x hx
  obtain ⟨x₀, hx₀, hmax⟩ := hΩ.isCompact_closure.exists_isMaxOn ⟨x, subset_closure hx⟩ hc
  refine (hmax (subset_closure hx)).trans ?_
  rw [closure_eq_interior_union_frontier, Ω.isOpen.interior_eq] at hx₀
  rcases hx₀ with hx₀ | hx₀
  · have hnhds := Ω.isOpen.mem_nhds hx₀
    have hloc : IsLocalMax ũ x₀ := hmax.isLocalMax (mem_of_superset hnhds subset_closure)
    have hu2 : ContDiffAt ℝ 2 ũ x₀ := hu.contDiffAt hnhds
    have hgrad : fderiv ℝ ũ x₀ = 0 := hloc.fderiv_eq_zero
    have hD : ∀ v, (fderiv ℝ (fderiv ℝ ũ) x₀).flip v v ≤ 0 := fun v ↦
      hloc.fderiv_fderiv_apply_self_nonpos hu2 v
    -- the product rule at the critical point `x₀`
    have hprod : ∀ i j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ ũ y (EuclideanSpace.single i 1)) x₀
          (EuclideanSpace.single j 1)
        = a i j x₀ * (fderiv ℝ (fderiv ℝ ũ) x₀).flip (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) := by
      intro i j
      have hai : DifferentiableAt ℝ (a i j) x₀ := (ha i j).differentiableAt hnhds
      have hd2 : DifferentiableAt ℝ (fderiv ℝ ũ) x₀ :=
        (hu2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have hg : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ũ y (EuclideanSpace.single i 1)) x₀ :=
        hd2.clm_apply (differentiableAt_const _)
      rw [fderiv_fun_mul hai hg, fderiv_clm_apply hd2 (differentiableAt_const _)]
      simp [hgrad]
    have hsum := (Matrix.posSemidef_of_of_symm_of_nonneg (fun i j ↦ congrFun (hsymm i j) x₀)
      (hell x₀ hx₀)).sum_mul_apply_single_nonpos _ hD
    simp only [Matrix.of_apply] at hsum
    have h := heq x₀ hx₀
    simp only [hprod, hgrad, zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h
    linarith [hf x₀ hx₀]
  · exact hΓ x₀ hx₀

end ClassicalGeneral

end Elliptic
