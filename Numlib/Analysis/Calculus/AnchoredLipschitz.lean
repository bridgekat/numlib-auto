/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Analysis.Calculus.LipschitzIteratedFDeriv

/-!
# Anchored Lipschitz continuity of iterated derivatives

Let $E$ and $F$ be real normed spaces, let $A$ and $D$ be subsets of $E$, and write $\nabla^j f(x)$
for the $j$-th derivative of $f : E \to F$ at $x$. The $j$-th derivative of $f$ is **$L$-Lipschitz
anchored in $A$ with respect to $D$** if
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L \|x - y\| \qquad \text{for all } x \in A \text{ and } y
  \in D.$$
In applications $A$ is a sublevel set. This is the condition (14.2.9) of the assumption f.D1qLaB.X
of [cartis2022evaluation]. With $A = D$ it is the Lipschitz condition on $D$.

Products inherit the anchored condition, with constants that are affine in the bounds of the two
factors on the anchor set only. This is Lemma 14.3.6 of [cartis2022evaluation], whose proof is
(B.14.9)–(B.14.18). Let $D$ be open and convex with $A \subseteq D$. Let $u, v : E \to \mathbb{R}$
be $C^p$ on $D$, let their derivatives of orders $1, \dots, p$ be anchored Lipschitz with constants
$L^u_i$ and $L^v_i$ and bounded on $D$ by $B^u_i$ and $B^v_i$, and let $|u| \le U$ and $|v| \le V$
on $A$. Then for $1 \le j \le p$, the derivative $\nabla^j (uv)$ is anchored Lipschitz with constant
$K_0 + L^v_j U + L^u_j V$ and bounded on $A$ by $K_2 + B^v_j U + B^u_j V$, where $K_0$ and $K_2$
depend only on the constants $L^u_i$, $L^v_i$, $B^u_i$ and $B^v_i$. Applied to $\frac12 (f - t)^2$,
this gives constants that do not depend on the target $t$.

## Main definitions

* `IteratedFDerivLipschitzAnchored`: the condition that $\nabla^j f$ is $L$-Lipschitz anchored in
  $A$ with respect to $D$.
* `AnchoredJetBounds`: the hypotheses on one factor $u$ of a product: $u$ is $C^p$ on $D$, its
  derivatives of orders $1 \le i \le p$ are anchored Lipschitz with constants $L_i$ and bounded on
  $D$ by $B_i$, and $|u| \le U$ on $A$.
* `anchoredMulLipConst`, `anchoredMulBoundConst`: the constants $K_0$ and $K_2$.

## Main results

* `IteratedFDerivLipschitzOn.anchored`: a derivative that is $L$-Lipschitz on $D$ is $L$-Lipschitz
  anchored in every $A \subseteq D$.
* `IteratedFDerivLipschitzAnchored.add`, `IteratedFDerivLipschitzAnchored.const_smul`,
  `IteratedFDerivLipschitzAnchored.sum`: the condition is stable under sums and scalar multiples,
  with the constants added or scaled.
* `AnchoredJetBounds.norm_iteratedFDeriv_mul_le`: $\|\nabla^j (uv)(x)\| \le K_2 + B^v_j U + B^u_j V$
  for $x \in A$.
* `IteratedFDerivLipschitzAnchored.mul`: $\nabla^j (uv)$ is anchored Lipschitz with constant
  $K_0 + L^v_j U + L^u_j V$.
* `AnchoredJetBounds.lipschitzAnchored_half_sq`, `AnchoredJetBounds.norm_iteratedFDeriv_half_sq_le`:
  the same two bounds for $u^2 / 2$.
* `AnchoredJetBounds.lipschitzAnchored_half_norm_sq`,
  `AnchoredJetBounds.norm_iteratedFDeriv_half_norm_sq_le`: the same two bounds for
  $\frac12 \|c\|^2$, where $c$ takes values in $\mathbb{R}^m$ (Lemma 14.3.6(i) of
  [cartis2022evaluation]).

## Proof outline

The product bounds do not expand $\nabla^j (uv)$ by the Leibniz rule. They use only the Leibniz
bound of Mathlib, `norm_iteratedFDerivWithin_mul_le`. Fix $x \in A$, put $a = u(x)$ and $b = v(x)$,
and write $uv = (u - a)(v - b) + a v + b u - a b$. For $y = x + t$, the difference of the $j$-th
derivatives of $w = (u - a)(v - b)$ at $x$ and at $y$ is the $j$-th derivative at $x$ of
$$z \mapsto w(z) - w(z + t) = \bigl(u(z) - u(z + t)\bigr)\bigl(v(z) - b\bigr) + \bigl(u(z + t) -
  a\bigr)\bigl(v(z) - v(z + t)\bigr).$$
The Leibniz bound applies to each product, because $v - b$ vanishes at $x$ and the increments are
$O(\|t\|)$.

## Implementation notes

* The derivative $\nabla^j f(x)$ is `iteratedFDeriv ℝ j f x`, a continuous $j$-linear map with the
  operator norm. At a point where $f$ is not $j$ times differentiable, it takes Mathlib's default
  value.
* The constants are real numbers, and sequences of constants are functions `ℕ → ℝ`.
-/

open Finset
open scoped Nat

section Basic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Let $f : E \to F$, $j \in \mathbb{N}$, $L \in \mathbb{R}$ and $A, D \subseteq E$. The $j$-th
derivative of $f$ is **$L$-Lipschitz anchored in $A$ with respect to $D$** if
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L \|x - y\| \qquad \text{for all } x \in A \text{ and }
  y \in D.$$
This is the condition (14.2.9) of [cartis2022evaluation].

The derivative $\nabla^j f$ is `iteratedFDeriv ℝ j f`. The definition requires neither
$A \subseteq D$ nor any differentiability of $f$. -/
def IteratedFDerivLipschitzAnchored (f : E → F) (j : ℕ) (L : ℝ) (A D : Set E) : Prop :=
  ∀ x ∈ A, ∀ y ∈ D, ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖

variable {f g : E → F} {j : ℕ} {L L' : ℝ} {A A' D D' : Set E}

/-- The condition `IteratedFDerivLipschitzAnchored f j L A D` holds if and only if $\|\nabla^j
f(x) - \nabla^j f(y)\| \le L \|x - y\|$ for all $x \in A$ and $y \in D$. -/
theorem iteratedFDerivLipschitzAnchored_iff : IteratedFDerivLipschitzAnchored f j L A D ↔
    ∀ x ∈ A, ∀ y ∈ D, ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ L * ‖x - y‖ :=
  Iff.rfl

namespace IteratedFDerivLipschitzAnchored

/-- If $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$, and $A' \subseteq A$,
$D' \subseteq D$ and $L \le L'$, then $\nabla^j f$ is $L'$-Lipschitz anchored in $A'$ with
respect to $D'$. -/
theorem mono (h : IteratedFDerivLipschitzAnchored f j L A D) (hA : A' ⊆ A) (hD : D' ⊆ D)
    (hL : L ≤ L') : IteratedFDerivLipschitzAnchored f j L' A' D' :=
  fun x hx y hy => (h x (hA hx) y (hD hy)).trans (by gcongr)

/-- If $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$ and $A' \subseteq A$, then
$\nabla^j f$ is $L$-Lipschitz anchored in $A'$ with respect to $D$. -/
theorem mono_left (h : IteratedFDerivLipschitzAnchored f j L A D) (hA : A' ⊆ A) :
    IteratedFDerivLipschitzAnchored f j L A' D :=
  h.mono hA subset_rfl le_rfl

/-- If $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$ and $D' \subseteq D$, then
$\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D'$. -/
theorem mono_right (h : IteratedFDerivLipschitzAnchored f j L A D) (hD : D' ⊆ D) :
    IteratedFDerivLipschitzAnchored f j L A D' :=
  h.mono subset_rfl hD le_rfl

/-- If $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$ and $L \le L'$, then
$\nabla^j f$ is $L'$-Lipschitz anchored in $A$ with respect to $D$. -/
theorem mono_const (h : IteratedFDerivLipschitzAnchored f j L A D) (hL : L ≤ L') :
    IteratedFDerivLipschitzAnchored f j L' A D :=
  h.mono subset_rfl subset_rfl hL

/-- Let $\nabla^j f$ be $L$-Lipschitz anchored in $A$ with respect to $D$, and let $x \in A$. Then
$$\|\nabla^j f(y) - \nabla^j f(x)\| \le L \|y - x\| \qquad \text{for all } y \in D.$$

This is the form of the condition at one anchor that the anchored Taylor bounds use, such as
`norm_iteratedFDeriv_sub_taylorPolynomial_le_of_lipschitzAnchored`. -/
theorem lipschitzAt (h : IteratedFDerivLipschitzAnchored f j L A D) {x : E} (hx : x ∈ A) :
    ∀ y ∈ D, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L * ‖y - x‖ := fun y hy => by
  rw [norm_sub_rev, norm_sub_rev y]
  exact h x hx y hy

/-- Let $f, g : E \to F$ be $C^j$ at every point of $D$, and let $A \subseteq D$. If $\nabla^j f$ is
$L$-Lipschitz and $\nabla^j g$ is $L'$-Lipschitz anchored in $A$ with respect to $D$, then
$\nabla^j (f + g)$ is $(L + L')$-Lipschitz anchored in $A$ with respect to $D$.

The smoothness hypotheses give $\nabla^j (f + g) = \nabla^j f + \nabla^j g$ at the points of
$D$. -/
theorem add (hf : IteratedFDerivLipschitzAnchored f j L A D)
    (hg : IteratedFDerivLipschitzAnchored g j L' A D) (hfd : ∀ y ∈ D, ContDiffAt ℝ j f y)
    (hgd : ∀ y ∈ D, ContDiffAt ℝ j g y) (hAD : A ⊆ D) :
    IteratedFDerivLipschitzAnchored (f + g) j (L + L') A D := by
  intro x hx y hy
  rw [iteratedFDeriv_add_apply (hfd x (hAD hx)) (hgd x (hAD hx)),
    iteratedFDeriv_add_apply (hfd y hy) (hgd y hy), add_sub_add_comm, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf x hx y hy) (hg x hx y hy))

/-- Let $f : E \to F$ be $C^j$ at every point of $D$, let $A \subseteq D$ and let
$c \in \mathbb{R}$. If $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$, then
$\nabla^j (c f)$ is $|c| L$-Lipschitz anchored in $A$ with respect to $D$. -/
theorem const_smul (hf : IteratedFDerivLipschitzAnchored f j L A D)
    (hfd : ∀ y ∈ D, ContDiffAt ℝ j f y) (hAD : A ⊆ D) (c : ℝ) :
    IteratedFDerivLipschitzAnchored (fun z => c • f z) j (|c| * L) A D := by
  intro x hx y hy
  rw [iteratedFDeriv_const_smul_apply' (hfd x (hAD hx)),
    iteratedFDeriv_const_smul_apply' (hfd y hy), ← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx y hy) (abs_nonneg c)

/-- Let $(f_i)_{i \in t}$ be a finite family of functions $E \to F$ that are $C^j$ at every point of
$D$, and let $A \subseteq D$. If each $\nabla^j f_i$ is $L_i$-Lipschitz anchored in $A$ with
respect to $D$, then $\nabla^j \sum_{i \in t} f_i$ is $\bigl(\sum_{i \in t} L_i\bigr)$-Lipschitz
anchored in $A$ with respect to $D$. -/
theorem sum {ι : Type*} {t : Finset ι} {f : ι → E → F} {L : ι → ℝ}
    (hf : ∀ i ∈ t, IteratedFDerivLipschitzAnchored (f i) j (L i) A D)
    (hfd : ∀ i ∈ t, ∀ y ∈ D, ContDiffAt ℝ j (f i) y) (hAD : A ⊆ D) :
    IteratedFDerivLipschitzAnchored (fun z => ∑ i ∈ t, f i z) j (∑ i ∈ t, L i) A D := by
  intro x hx y hy
  rw [iteratedFDeriv_fun_sum_apply fun i hi => hfd i hi x (hAD hx),
    iteratedFDeriv_fun_sum_apply fun i hi => hfd i hi y hy, ← sum_sub_distrib, sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun i hi => hf i hi x hx y hy)

end IteratedFDerivLipschitzAnchored

/-- Let $A \subseteq D$. If $\nabla^j f$ is $L$-Lipschitz on $D$, that is
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L \|x - y\| \qquad \text{for all } x, y \in D,$$
then $\nabla^j f$ is $L$-Lipschitz anchored in $A$ with respect to $D$.

The Lipschitz condition on $D$ is `IteratedFDerivLipschitzOn`. -/
theorem IteratedFDerivLipschitzOn.anchored (h : IteratedFDerivLipschitzOn f j L D)
    (hAD : A ⊆ D) : IteratedFDerivLipschitzAnchored f j L A D :=
  fun x hx y hy => iteratedFDerivLipschitzOn_iff.1 h x (hAD hx) y hy

/-- The derivative $\nabla^j f$ is $L$-Lipschitz anchored in $D$ with respect to $D$ if and only if
it is $L$-Lipschitz on $D$, in the sense of `IteratedFDerivLipschitzOn`. -/
theorem iteratedFDerivLipschitzAnchored_self_iff :
    IteratedFDerivLipschitzAnchored f j L D D ↔ IteratedFDerivLipschitzOn f j L D := by
  rw [iteratedFDerivLipschitzOn_iff]
  rfl

end Basic

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Leibniz bound** on an open set. Let $S \subseteq E$ be open, let $f, g : E \to \mathbb{R}$
be $C^n$ on $S$, and let $x \in S$. Then $\|\nabla^n (fg)(x)\| \le \sum_{i=0}^{n} \binom{n}{i}
\|\nabla^i f(x)\| \, \|\nabla^{n-i} g(x)\|$. -/
theorem norm_iteratedFDeriv_mul_le_of_isOpen {f g : E → ℝ} {S : Set E} (hS : IsOpen S) {n : ℕ}
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {x : E} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ ∑ i ∈ range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hS.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hS hx] at h
  refine h.trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  rw [iteratedFDerivWithin_of_isOpen i hS hx, iteratedFDerivWithin_of_isOpen (n - i) hS hx]

/-- Let $S \subseteq E$ be open, let $f, g : E \to \mathbb{R}$ be $C^n$ on $S$, and let $x \in S$.
If $\|\nabla^i f(x)\| \le \alpha_i$ and $\|\nabla^i g(x)\| \le \beta_i$ for all $i \le n$, then
$\|\nabla^n (fg)(x)\| \le \sum_{i=0}^{n} \binom{n}{i} \alpha_i \beta_{n-i}$. -/
theorem norm_iteratedFDeriv_mul_le_of_le {f g : E → ℝ} {S : Set E} (hS : IsOpen S) {n : ℕ}
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {x : E} (hx : x ∈ S) {α β : ℕ → ℝ}
    (hα : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ α i) (hβ : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ β i) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (α i * β (n - i)) := by
  refine (norm_iteratedFDeriv_mul_le_of_isOpen hS hf hg hx).trans (sum_le_sum fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hα i hi') (hβ _ (Nat.sub_le n i)) (norm_nonneg _)
    ((norm_nonneg _).trans (hα i hi'))) (Nat.cast_nonneg _)

/-- For real sequences $B$ and $L$, the **increment constant** $\lambda_i$ of the $i$-th derivative
is $L_i$ for $i \ge 1$ and $B_1$ for $i = 0$. For $i = 0$ it is the constant that the mean value
theorem gives for $|u(x) - u(y)|$ when $\|\nabla u\| \le B_1$. -/
def anchoredIncr (B L : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then B 1 else L i

/-- For a real sequence $B$, the **jet bound** $\beta_k$ is $B_k$ for $k \ge 1$ and $0$ for $k = 0$.
-/
def anchoredJet (B : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then 0 else B k

/-- The constant $K_0$ in the anchored Lipschitz constant of $\nabla^j (uv)$: the part that does not
involve the anchor bounds $U$ and $V$. For real sequences $L^u$, $L^v$, $B^u$ and $B^v$,
$$K_0 = \sum_{i=0}^{j} \binom{j}{i} \bigl(\lambda^u_i \beta^v_{j-i} + \gamma_i\bigr),$$
where $\lambda^u$ and $\lambda^v$ are the increment constants of $(B^u, L^u)$ and of
$(B^v, L^v)$, $\beta^v$ is the jet bound of $B^v$, $\gamma_0 = 2 B^u_1 B^v_j$, and
$\gamma_i = B^u_i \lambda^v_{j-i}$ for $i \ge 1$.

The increment constants are `anchoredIncr Bu Lu` and `anchoredIncr Bv Lv`, and the jet bound is
`anchoredJet Bv`. -/
noncomputable def anchoredMulLipConst (Lu Lv Bu Bv : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℝ) *
    (anchoredIncr Bu Lu i * anchoredJet Bv (j - i) +
      if i = 0 then 2 * Bu 1 * Bv j else Bu i * anchoredIncr Bv Lv (j - i))

/-- The constant $K_2 = \sum_{0 < i < j} \binom{j}{i} B^u_i B^v_{j-i}$ in the bound on
$\nabla^j (uv)$: the part that does not involve the anchor bounds $U$ and $V$.

The sum runs over $0 \le i \le j$ with the jet bounds `anchoredJet`, so that the terms $i = 0$
and $i = j$ vanish. -/
noncomputable def anchoredMulBoundConst (Bu Bv : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℝ) * (anchoredJet Bu i * anchoredJet Bv (j - i))

/-- Let $u : E \to \mathbb{R}$, $p \in \mathbb{N}$, let $L$ and $B$ be real sequences, let
$U \in \mathbb{R}$ and let $A, D \subseteq E$. The **anchored jet bounds** of $u$ hold if $u$ is
$C^p$ on $D$, if for each $1 \le i \le p$ the derivative $\nabla^i u$ is $L_i$-Lipschitz
anchored in $A$ with respect to $D$ and satisfies $\|\nabla^i u(y)\| \le B_i$ for all $y \in D$,
and if $|u(x)| \le U$ for all $x \in A$.

These are the hypotheses on one factor of a product. The conditions on $D$ are the assumption
f.D1pLaB.X of [cartis2022evaluation]; the bound on the anchor set $A$ is added. -/
structure AnchoredJetBounds (u : E → ℝ) (p : ℕ) (L B : ℕ → ℝ) (U : ℝ) (A D : Set E) : Prop where
  /-- The function $u$ is $C^p$ on $D$. -/
  contDiffOn : ContDiffOn ℝ p u D
  /-- For $1 \le i \le p$, the derivative $\nabla^i u$ is $L_i$-Lipschitz anchored in $A$ with
  respect to $D$. -/
  lipschitzAnchored : ∀ i ∈ Icc 1 p, IteratedFDerivLipschitzAnchored u i (L i) A D
  /-- For $1 \le i \le p$ and $y \in D$, $\|\nabla^i u(y)\| \le B_i$. -/
  norm_le : ∀ i ∈ Icc 1 p, ∀ y ∈ D, ‖iteratedFDeriv ℝ i u y‖ ≤ B i
  /-- For $x \in A$, $|u(x)| \le U$. -/
  abs_le : ∀ x ∈ A, |u x| ≤ U

/-- For $w : E \to \mathbb{R}$ and $x, y \in E$, $\|\nabla^0 w(x) - \nabla^0 w(y)\| = |w(x) -
w(y)|$. -/
theorem norm_iteratedFDeriv_zero_sub (w : E → ℝ) (x y : E) :
    ‖iteratedFDeriv ℝ 0 w x - iteratedFDeriv ℝ 0 w y‖ = ‖w x - w y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
    LinearIsometryEquiv.norm_map]

/-- Let $w : E \to \mathbb{R}$ be $C^i$ at $x$ and at $x + t$. Then the $i$-th derivative at $x$ of
the increment $z \mapsto w(z) - w(z + t)$ is $\nabla^i w(x) - \nabla^i w(x + t)$. -/
theorem iteratedFDeriv_sub_comp_add_right {w : E → ℝ} {i : ℕ} {x t : E}
    (hw : ContDiffAt ℝ i w x) (hwt : ContDiffAt ℝ i w (x + t)) :
    iteratedFDeriv ℝ i (fun z => w z - w (z + t)) x =
      iteratedFDeriv ℝ i w x - iteratedFDeriv ℝ i w (x + t) := by
  have hwt' : ContDiffAt ℝ i (fun z => w (z + t)) x :=
    hwt.comp x (contDiffAt_id.add contDiffAt_const)
  change iteratedFDeriv ℝ i (w - fun z => w (z + t)) x = _
  rw [iteratedFDeriv_sub_apply hw hwt', iteratedFDeriv_comp_add_right]

/-- Let $u, v : E \to \mathbb{R}$ be $C^j$ at $z$ with $j \ge 1$, and let $a, b \in \mathbb{R}$.
Then
$$\nabla^j (uv)(z) = a \nabla^j v(z) + b \nabla^j u(z) + \nabla^j \bigl((u - a)(v -
  b)\bigr)(z).$$
This is the decomposition $uv = (u - a)(v - b) + a v + b u - a b$ at the level of the $j$-th
derivative; the constant $ab$ drops out because $j \ge 1$. -/
theorem iteratedFDeriv_mul_eq_add {u v : E → ℝ} {j : ℕ} {z : E} (hu : ContDiffAt ℝ j u z)
    (hv : ContDiffAt ℝ j v z) (hj : j ≠ 0) (a b : ℝ) :
    iteratedFDeriv ℝ j (fun y => u y * v y) z =
      a • iteratedFDeriv ℝ j v z + b • iteratedFDeriv ℝ j u z +
        iteratedFDeriv ℝ j (fun y => (u y - a) * (v y - b)) z := by
  have hw : ContDiffAt ℝ j (fun y => (u y - a) * (v y - b)) z :=
    (hu.sub contDiffAt_const).mul (hv.sub contDiffAt_const)
  have hfun : (fun y => u y * v y) =
      (fun y => (u y - a) * (v y - b)) + ((fun y => a • v y) + fun y => b • u y) -
        fun _ => a * b := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hsum : ContDiffAt ℝ j ((fun y => (u y - a) * (v y - b)) +
      ((fun y => a • v y) + fun y => b • u y)) z :=
    hw.add ((hv.const_smul a).add (hu.const_smul b))
  rw [hfun, iteratedFDeriv_sub_apply hsum (contDiffAt_const (c := a * b)),
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    iteratedFDeriv_add_apply (f := fun y => (u y - a) * (v y - b))
      (g := (fun y => a • v y) + fun y => b • u y) hw ((hv.const_smul a).add (hu.const_smul b)),
    iteratedFDeriv_add_apply (f := fun y => a • v y) (g := fun y => b • u y) (hv.const_smul a)
      (hu.const_smul b),
    iteratedFDeriv_const_smul_apply' hv, iteratedFDeriv_const_smul_apply' hu]
  abel

namespace AnchoredJetBounds

variable {u v : E → ℝ} {p : ℕ} {Lu Lv Bu Bv : ℕ → ℝ} {U V : ℝ} {A D : Set E}

/-- If $u$ has the anchored jet bounds of order $p$ and $D$ is open, then $u$ is $C^i$ at every
point of $D$ for every $i \le p$. -/
theorem contDiffAt (h : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) {y : E} (hy : y ∈ D)
    {i : ℕ} (hi : i ≤ p) : ContDiffAt ℝ i u y :=
  (h.contDiffOn.contDiffAt (hD.mem_nhds hy)).of_le (by exact_mod_cast hi)

/-- Let $D$ be open and convex with $A \subseteq D$, let $p \ge 1$, and let $u$ have the anchored
jet bounds of order $p$ with constants $L$, $B$ and $U$. Then for $x \in A$, $y \in D$ and
$0 \le i \le p$,
$$\|\nabla^i u(x) - \nabla^i u(y)\| \le \lambda_i \|x - y\|,$$
where $\lambda_i$ is the increment constant `anchoredIncr B L i`: $L_i$ for $i \ge 1$, and $B_1$
for $i = 0$. The case $i = 0$ is the mean value theorem on the convex set $D$. -/
theorem norm_sub_le (h : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) (hDc : Convex ℝ D)
    (hAD : A ⊆ D) (hp : 1 ≤ p) {x y : E} (hx : x ∈ A) (hy : y ∈ D) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i u x - iteratedFDeriv ℝ i u y‖ ≤ anchoredIncr Bu Lu i * ‖x - y‖ := by
  unfold anchoredIncr
  split_ifs with h0
  · subst h0
    have hlip : IteratedFDerivLipschitzOn u 0 (Bu 1) D :=
      iteratedFDerivLipschitzOn_of_norm_le hDc (fun z hz => h.contDiffAt hD hz hp)
        fun z hz => h.norm_le 1 (mem_Icc.2 ⟨le_rfl, hp⟩) z hz
    exact iteratedFDerivLipschitzOn_iff.1 hlip x (hAD hx) y hy
  · exact h.lipschitzAnchored i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi⟩) x hx y hy

/-- Let $A \subseteq D$ and let $u$ have the anchored jet bounds of order $p$ with constants $L$,
$B$ and $U$. Then for $x \in A$ and $i \le p$, $\|\nabla^i u(x)\|$ is at most $U$ if $i = 0$,
and at most $B_i$ if $i \ge 1$. -/
theorem norm_iteratedFDeriv_le (h : AnchoredJetBounds u p Lu Bu U A D) (hAD : A ⊆ D) {x : E}
    (hx : x ∈ A) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i u x‖ ≤ if i = 0 then U else Bu i := by
  split_ifs with h0
  · subst h0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact h.abs_le x hx
  · exact h.norm_le i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi⟩) x (hAD hx)

/-- Let $w : E \to \mathbb{R}$ be $C^i$ at $z$ with $i \ge 1$, and let $c \in \mathbb{R}$. Then
$\nabla^i (w - c)(z) = \nabla^i w(z)$. -/
theorem iteratedFDeriv_sub_const {w : E → ℝ} {i : ℕ} {z : E} (hw : ContDiffAt ℝ i w z) (c : ℝ)
    (hi : i ≠ 0) : iteratedFDeriv ℝ i (fun y => w y - c) z = iteratedFDeriv ℝ i w z := by
  change iteratedFDeriv ℝ i (w - fun _ => c) z = _
  rw [iteratedFDeriv_sub_apply hw contDiffAt_const, iteratedFDeriv_const_of_ne hi,
    Pi.zero_apply, sub_zero]

/-- The **derivative bound for products on the anchor set**. Let $D \subseteq E$ be open with
$A \subseteq D$, and let $u, v : E \to \mathbb{R}$ have the anchored jet bounds of order $p$,
with constants $L^u$, $B^u$, $U$ for $u$ and $L^v$, $B^v$, $V$ for $v$. Then for $1 \le j \le p$
and $x \in A$,
$$\|\nabla^j (uv)(x)\| \le K_2 + B^v_j U + B^u_j V,$$
where $K_2 = \sum_{0 < i < j} \binom{j}{i} B^u_i B^v_{j-i}$. This is (14.3.61) and (14.3.63) of
[cartis2022evaluation].

The constant $K_2$ is `anchoredMulBoundConst Bu Bv j`, and the anchored jet bounds are
`AnchoredJetBounds`. -/
theorem norm_iteratedFDeriv_mul_le (hu : AnchoredJetBounds u p Lu Bu U A D)
    (hv : AnchoredJetBounds v p Lv Bv V A D) (hD : IsOpen D) (hAD : A ⊆ D) {j : ℕ}
    (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => u y * v y) x‖ ≤
      anchoredMulBoundConst Bu Bv j + Bv j * U + Bu j * V := by
  obtain ⟨hj1, hjp⟩ := mem_Icc.1 hj
  have hcd : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j w D :=
    fun hw => hw.of_le (by exact_mod_cast hjp)
  refine (norm_iteratedFDeriv_mul_le_of_le hD (hcd hu.contDiffOn) (hcd hv.contDiffOn) (hAD hx)
    (fun i hi => hu.norm_iteratedFDeriv_le hAD hx (hi.trans hjp))
    (fun i hi => hv.norm_iteratedFDeriv_le hAD hx (hi.trans hjp))).trans ?_
  have hU : 0 ≤ U := (abs_nonneg _).trans (hu.abs_le x hx)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hv.abs_le x hx)
  have hterm : ∀ i ∈ range (j + 1),
      (j.choose i : ℝ) * ((if i = 0 then U else Bu i) * (if j - i = 0 then V else Bv (j - i))) =
        (j.choose i : ℝ) * (anchoredJet Bu i * anchoredJet Bv (j - i)) +
          ((if i = 0 then Bv j * U else 0) + if i = j then Bu j * V else 0) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    unfold anchoredJet
    by_cases h0 : i = 0
    · subst h0
      have h1 : j ≠ 0 := by omega
      have h2 : (0 : ℕ) ≠ j := by omega
      simp [h1, h2, mul_comm]
    · by_cases hij : i = j
      · subst hij
        simp [h0]
      · have : j - i ≠ 0 := by omega
        simp [h0, hij, this]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, sum_ite_eq' (range (j + 1)) 0,
    sum_ite_eq' (range (j + 1)) j]
  simp only [anchoredMulBoundConst, mem_range, Nat.lt_succ_iff, zero_le, le_rfl, ite_true]
  linarith




/-- Let $D$ be open with $A \subseteq D$, let $c \in \mathbb{R}$, and let $u$ have the anchored jet
bounds of order $p$ with constants $L$, $B$ and $U$. If $|u(x) - c| \le U'$ for all $x \in A$,
then $u - c$ has the anchored jet bounds of order $p$ with constants $L$, $B$ and $U'$. Thus a
shift by a constant changes only the anchor bound. -/
theorem sub_const (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D) (hAD : A ⊆ D) (c : ℝ)
    {U' : ℝ} (hU' : ∀ x ∈ A, |u x - c| ≤ U') :
    AnchoredJetBounds (fun y => u y - c) p Lu Bu U' A D where
  contDiffOn := hu.contDiffOn.sub contDiffOn_const
  lipschitzAnchored i hi x hx y hy := by
    obtain ⟨hi1, hip⟩ := mem_Icc.1 hi
    have hi0 : i ≠ 0 := by omega
    rw [iteratedFDeriv_sub_const (hu.contDiffAt hD (hAD hx) hip) c hi0,
      iteratedFDeriv_sub_const (hu.contDiffAt hD hy hip) c hi0]
    exact hu.lipschitzAnchored i hi x hx y hy
  norm_le i hi y hy := by
    obtain ⟨hi1, hip⟩ := mem_Icc.1 hi
    rw [iteratedFDeriv_sub_const (hu.contDiffAt hD hy hip) c (by omega)]
    exact hu.norm_le i hi y hy
  abs_le := hU'

/-- The **anchored Lipschitz bound for products**. Let $D \subseteq E$ be open and convex with
$A \subseteq D$, and let $u, v : E \to \mathbb{R}$ have the anchored jet bounds of order $p$,
with constants $L^u$, $B^u$, $U$ for $u$ and $L^v$, $B^v$, $V$ for $v$. Then for
$1 \le j \le p$, the derivative $\nabla^j (uv)$ is Lipschitz anchored in $A$ with respect to
$D$, with constant
$$K_0 + L^v_j U + L^u_j V,$$
where $K_0$ does not depend on $U$ and $V$. This is Lemma 14.3.6 of [cartis2022evaluation], with
(14.3.60) and (14.3.62); the proof in the source is (B.14.9)–(B.14.18).

The constant $K_0$ is `anchoredMulLipConst Lu Lv Bu Bv j`, and the anchored jet bounds are
`AnchoredJetBounds`. The proof splits the product with `iteratedFDeriv_mul_eq_add` and bounds
each part with the Leibniz bound, as the module documentation describes. -/
theorem _root_.IteratedFDerivLipschitzAnchored.mul (hu : AnchoredJetBounds u p Lu Bu U A D)
    (hv : AnchoredJetBounds v p Lv Bv V A D)
    (hD : IsOpen D) (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => u y * v y) j
      (anchoredMulLipConst Lu Lv Bu Bv j + Lv j * U + Lu j * V) A D := by
  obtain ⟨hj1, hjp⟩ := mem_Icc.1 hj
  have hp : 1 ≤ p := hj1.trans hjp
  have hj0 : j ≠ 0 := by omega
  intro x hx y hy
  have hxD := hAD hx
  set t := y - x with ht
  have hxt : x + t = y := by rw [ht]; abel
  set a := u x
  set b := v x
  set r := ‖x - y‖
  have hr : 0 ≤ r := norm_nonneg _
  have hU : 0 ≤ U := (abs_nonneg _).trans (hu.abs_le x hx)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hv.abs_le x hx)
  -- smoothness on the open set `S = D ∩ (D - t)` containing `x`
  set S := D ∩ (fun z => z + t) ⁻¹' D with hS
  have hSo : IsOpen S := hD.inter (hD.preimage (continuous_id.add continuous_const))
  have hxS : x ∈ S := ⟨hxD, by simp [hxt, hy]⟩
  have hcd : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j w S := fun hw =>
    (hw.of_le (by exact_mod_cast hjp)).mono Set.inter_subset_left
  have hcdt : ∀ {w : E → ℝ}, ContDiffOn ℝ p w D → ContDiffOn ℝ j (fun z => w (z + t)) S :=
    fun hw => (hw.of_le (by exact_mod_cast hjp)).comp
      (contDiff_id.add contDiff_const).contDiffOn fun _ hz => hz.2
  have hδu : ContDiffOn ℝ j (fun z => u z - u (z + t)) S :=
    (hcd hu.contDiffOn).sub (hcdt hu.contDiffOn)
  have hvb : ContDiffOn ℝ j (fun z => v z - b) S := (hcd hv.contDiffOn).sub contDiffOn_const
  have hua : ContDiffOn ℝ j (fun z => u (z + t) - a) S :=
    (hcdt hu.contDiffOn).sub contDiffOn_const
  have hδv : ContDiffOn ℝ j (fun z => v z - v (z + t)) S :=
    (hcd hv.contDiffOn).sub (hcdt hv.contDiffOn)
  have hSn : S ∈ nhds x := hSo.mem_nhds hxS
  -- bounds on the derivatives of the four factors at `x`
  have B1 : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => u z - u (z + t)) x‖ ≤
      anchoredIncr Bu Lu i * r := by
    intro i hi
    rw [iteratedFDeriv_sub_comp_add_right (hu.contDiffAt hD hxD (hi.trans hjp))
      (hxt ▸ hu.contDiffAt hD hy (hi.trans hjp)), hxt]
    exact hu.norm_sub_le hD hDc hAD hp hx hy (hi.trans hjp)
  have B2 : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun z => v z - b) x‖ ≤ anchoredJet Bv k := by
    intro k hk
    unfold anchoredJet
    split_ifs with h0
    · subst h0
      simp [norm_iteratedFDeriv_zero, b]
    · rw [iteratedFDeriv_sub_const (hv.contDiffAt hD hxD (hk.trans hjp)) b h0]
      exact hv.norm_le k (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hk.trans hjp⟩) x hxD
  have B3 : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z => u (z + t) - a) x‖ ≤
      if i = 0 then Bu 1 * r else Bu i := by
    intro i hi
    split_ifs with h0
    · subst h0
      rw [norm_iteratedFDeriv_zero, hxt, norm_sub_rev, ← norm_iteratedFDeriv_zero_sub]
      simpa [anchoredIncr] using hu.norm_sub_le hD hDc hAD hp hx hy (Nat.zero_le p)
    · have hc : ContDiffAt ℝ i (fun z => u (z + t)) x :=
        (hxt ▸ hu.contDiffAt hD hy (hi.trans hjp)).comp x (contDiffAt_id.add contDiffAt_const)
      rw [iteratedFDeriv_sub_const hc a h0, iteratedFDeriv_comp_add_right, hxt]
      exact hu.norm_le i (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h0, hi.trans hjp⟩) y hy
  have B4 : ∀ k ≤ j, ‖iteratedFDeriv ℝ k (fun z => v z - v (z + t)) x‖ ≤
      if k = j then 2 * Bv j else anchoredIncr Bv Lv k * r := by
    intro k hk
    rw [iteratedFDeriv_sub_comp_add_right (hv.contDiffAt hD hxD (hk.trans hjp))
      (hxt ▸ hv.contDiffAt hD hy (hk.trans hjp)), hxt]
    split_ifs with hkj
    · subst hkj
      have hjI : k ∈ Icc 1 p := mem_Icc.2 ⟨hj1, hjp⟩
      have h1 := hv.norm_le k hjI x hxD
      have h2 := hv.norm_le k hjI y hy
      exact (_root_.norm_sub_le _ _).trans (by linarith)
    · exact hv.norm_sub_le hD hDc hAD hp hx hy (hk.trans hjp)
  -- the product part
  have hw : iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) x -
      iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) y =
      iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x +
        iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x := by
    have hwx : ContDiffAt ℝ j (fun z => (u z - a) * (v z - b)) x :=
      ((hu.contDiffAt hD hxD hjp).sub contDiffAt_const).mul
        ((hv.contDiffAt hD hxD hjp).sub contDiffAt_const)
    have hwy : ContDiffAt ℝ j (fun z => (u z - a) * (v z - b)) (x + t) := by
      rw [hxt]
      exact ((hu.contDiffAt hD hy hjp).sub contDiffAt_const).mul
        ((hv.contDiffAt hD hy hjp).sub contDiffAt_const)
    rw [← hxt, ← iteratedFDeriv_sub_comp_add_right hwx hwy]
    have hfun : (fun z => (u z - a) * (v z - b) - (u (z + t) - a) * (v (z + t) - b)) =
        (fun z => (u z - u (z + t)) * (v z - b)) +
          fun z => (u (z + t) - a) * (v z - v (z + t)) := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [hfun, iteratedFDeriv_add_apply ((hδu.mul hvb).contDiffAt hSn)
      ((hua.mul hδv).contDiffAt hSn)]
  have hT1 := norm_iteratedFDeriv_mul_le_of_le hSo hδu hvb hxS B1 B2
  have hT2 := norm_iteratedFDeriv_mul_le_of_le hSo hua hδv hxS B3 B4
  have hsum : (∑ i ∈ range (j + 1), (j.choose i : ℝ) *
      (anchoredIncr Bu Lu i * r * anchoredJet Bv (j - i))) +
      (∑ i ∈ range (j + 1), (j.choose i : ℝ) * ((if i = 0 then Bu 1 * r else Bu i) *
        (if j - i = j then 2 * Bv j else anchoredIncr Bv Lv (j - i) * r))) =
      anchoredMulLipConst Lu Lv Bu Bv j * r := by
    rw [← sum_add_distrib, anchoredMulLipConst, sum_mul]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.sub_zero, ite_true]
      ring
    · have : j - i ≠ j := by omega
      simp only [h0, this, ite_false]
      ring
  -- assemble
  have hdx := iteratedFDeriv_mul_eq_add (hu.contDiffAt hD hxD hjp) (hv.contDiffAt hD hxD hjp) hj0
    a b
  have hdy := iteratedFDeriv_mul_eq_add (hu.contDiffAt hD hy hjp) (hv.contDiffAt hD hy hjp) hj0
    a b
  have hjI : j ∈ Icc 1 p := mem_Icc.2 ⟨hj1, hjp⟩
  have hLv := hv.lipschitzAnchored j hjI x hx y hy
  have hLu := hu.lipschitzAnchored j hjI x hx y hy
  have ha : |a| ≤ U := hu.abs_le x hx
  have hb : |b| ≤ V := hv.abs_le x hx
  rw [hdx, hdy]
  calc ‖a • iteratedFDeriv ℝ j v x + b • iteratedFDeriv ℝ j u x +
        iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) x -
        (a • iteratedFDeriv ℝ j v y + b • iteratedFDeriv ℝ j u y +
          iteratedFDeriv ℝ j (fun z => (u z - a) * (v z - b)) y)‖
      = ‖a • (iteratedFDeriv ℝ j v x - iteratedFDeriv ℝ j v y) +
          b • (iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y) +
          (iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x +
            iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x)‖ := by
        rw [← hw, smul_sub, smul_sub]
        congr 1
        abel
    _ ≤ |a| * ‖iteratedFDeriv ℝ j v x - iteratedFDeriv ℝ j v y‖ +
          |b| * ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ +
          (‖iteratedFDeriv ℝ j (fun z => (u z - u (z + t)) * (v z - b)) x‖ +
            ‖iteratedFDeriv ℝ j (fun z => (u (z + t) - a) * (v z - v (z + t))) x‖) := by
        refine (norm_add₃_le).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        exact norm_add_le _ _
    _ ≤ U * (Lv j * r) + V * (Lu j * r) + anchoredMulLipConst Lu Lv Bu Bv j * r := by
        rw [← hsum]
        gcongr
    _ = (anchoredMulLipConst Lu Lv Bu Bv j + Lv j * U + Lu j * V) * r := by ring

/-- The **anchored Lipschitz bound for half squares**. Let $D \subseteq E$ be open and convex with
$A \subseteq D$, and let $u$ have the anchored jet bounds of order $p$ with constants $L$, $B$
and $U$. Then for $1 \le j \le p$, the derivative $\nabla^j (u^2 / 2)$ is Lipschitz anchored in
$A$ with respect to $D$, with constant $K_0 / 2 + L_j U$, where $K_0$ is
`anchoredMulLipConst L L B B j`. This is the Lipschitz part of Lemma 14.3.6(ii) of
[cartis2022evaluation], for $u = f - t$. -/
theorem lipschitzAnchored_half_sq (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D)
    (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => u y ^ 2 / 2) j
      (anchoredMulLipConst Lu Lu Bu Bu j / 2 + Lu j * U) A D := by
  have hjp := (mem_Icc.1 hj).2
  have h := (IteratedFDerivLipschitzAnchored.mul hu hu hD hDc hAD hj).const_smul
    (fun y hy => (hu.contDiffAt hD hy hjp).mul (hu.contDiffAt hD hy hjp)) hAD (1 / 2)
  have hfun : (fun y => u y ^ 2 / 2) = fun y => (1 / 2 : ℝ) • (u y * u y) := by
    funext y
    rw [smul_eq_mul]
    ring
  rw [hfun]
  refine h.mono_const (le_of_eq ?_)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

/-- The **derivative bound for half squares**. Let $D \subseteq E$ be open with $A \subseteq D$, and
let $u$ have the anchored jet bounds of order $p$ with constants $L$, $B$ and $U$. Then for
$1 \le j \le p$ and $x \in A$,
$$\|\nabla^j (u^2 / 2)(x)\| \le K_2 / 2 + B_j U,$$
where $K_2$ is `anchoredMulBoundConst B B j`. This is (14.3.63) of [cartis2022evaluation]. -/
theorem norm_iteratedFDeriv_half_sq_le (hu : AnchoredJetBounds u p Lu Bu U A D) (hD : IsOpen D)
    (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => u y ^ 2 / 2) x‖ ≤
      anchoredMulBoundConst Bu Bu j / 2 + Bu j * U := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => u y ^ 2 / 2) = fun y => (1 / 2 : ℝ) • (u y * u y) := by
    funext y
    rw [smul_eq_mul]
    ring
  have hc := (hu.contDiffAt hD (hAD hx) hjp).mul (hu.contDiffAt hD (hAD hx) hjp)
  rw [hfun, iteratedFDeriv_const_smul_apply' hc, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := hu.norm_iteratedFDeriv_mul_le hu hD hAD hj hx
  linarith

/-- The **anchored Lipschitz bound for half squared norms**. Let $D \subseteq E$ be open and convex
with $A \subseteq D$, and let $c : E \to \mathbb{R}^m$ be a function whose components
$c_1, \dots, c_m$ all have the anchored jet bounds of order $p$ with the same constants $L$, $B$
and $U$. Then for $1 \le j \le p$, the derivative $\nabla^j (\frac12 \|c\|^2)$ is Lipschitz
anchored in $A$ with respect to $D$, with constant
$$m \bigl(K_0 / 2 + L_j U\bigr),$$
where $K_0$ is `anchoredMulLipConst L L B B j`. This is Lemma 14.3.6(i) of
[cartis2022evaluation], with (14.3.60).

The space $\mathbb{R}^m$ is `EuclideanSpace ℝ (Fin m)`. -/
theorem lipschitzAnchored_half_norm_sq {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)}
    {L B : ℕ → ℝ} (hc : ∀ i, AnchoredJetBounds (fun y => c y i) p L B U A D) (hD : IsOpen D)
    (hDc : Convex ℝ D) (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) :
    IteratedFDerivLipschitzAnchored (fun y => ‖c y‖ ^ 2 / 2) j
      (m * (anchoredMulLipConst L L B B j / 2 + L j * U)) A D := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => ‖c y‖ ^ 2 / 2) = fun y => ∑ i : Fin m, c y i ^ 2 / 2 := by
    funext y
    rw [EuclideanSpace.norm_sq_eq, sum_div]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun]
  have h := IteratedFDerivLipschitzAnchored.sum (t := univ)
    (fun i _ => (hc i).lipschitzAnchored_half_sq hD hDc hAD hj)
    (fun i _ y hy => (((hc i).contDiffAt hD hy hjp).pow 2).div_const 2) hAD
  simpa [mul_add] using h

/-- The **derivative bound for half squared norms**. Let $D \subseteq E$ be open with
$A \subseteq D$, and let $c : E \to \mathbb{R}^m$ be a function whose components all have the
anchored jet bounds of order $p$ with the same constants $L$, $B$ and $U$. Then for
$1 \le j \le p$ and $x \in A$,
$$\|\nabla^j (\tfrac12 \|c\|^2)(x)\| \le m \bigl(K_2 / 2 + B_j U\bigr),$$
where $K_2$ is `anchoredMulBoundConst B B j`. This is (14.3.61) of [cartis2022evaluation].

The space $\mathbb{R}^m$ is `EuclideanSpace ℝ (Fin m)`. Unlike
`AnchoredJetBounds.lipschitzAnchored_half_norm_sq`, this bound does not need $D$ to be convex. -/
theorem norm_iteratedFDeriv_half_norm_sq_le {m : ℕ} {c : E → EuclideanSpace ℝ (Fin m)}
    {L B : ℕ → ℝ} (hc : ∀ i, AnchoredJetBounds (fun y => c y i) p L B U A D) (hD : IsOpen D)
    (hAD : A ⊆ D) {j : ℕ} (hj : j ∈ Icc 1 p) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ j (fun y => ‖c y‖ ^ 2 / 2) x‖ ≤
      m * (anchoredMulBoundConst B B j / 2 + B j * U) := by
  have hjp := (mem_Icc.1 hj).2
  have hfun : (fun y => ‖c y‖ ^ 2 / 2) = fun y => ∑ i : Fin m, c y i ^ 2 / 2 := by
    funext y
    rw [EuclideanSpace.norm_sq_eq, sum_div]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hfun, iteratedFDeriv_fun_sum_apply fun i _ =>
    (((hc i).contDiffAt hD (hAD hx) hjp).pow 2).div_const 2]
  refine (norm_sum_le _ _).trans ?_
  have := sum_le_sum fun i (_ : i ∈ univ) => (hc i).norm_iteratedFDeriv_half_sq_le hD hAD hj hx
  simpa [mul_add] using this

end AnchoredJetBounds

end Product
