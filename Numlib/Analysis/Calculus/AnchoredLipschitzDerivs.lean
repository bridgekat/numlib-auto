/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Analysis.Calculus.MultivariateTaylor.Basic

/-!
# Anchored Lipschitz continuity of the derivatives of several orders

Let $E$ and $F$ be real normed spaces, let $C \subseteq E$ be open and convex, and let
$A \subseteq C$ be a set of anchors. A function $f : E \to F$ has **anchored Lipschitz derivatives
of orders $j_0$ to $p$** if $f$ is $C^p$ near every point of $C$ and, for every order
$j_0 \le j \le p$,
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\| \qquad \text{for all } x \in A \text{ and } y
  \in C.$$
This bundles the smoothness hypothesis of the high-order model-based methods of
[cartis2022evaluation], Chapters 12–14. The lowest order $j_0$ is $1$ for the conditions on the
derivatives only (f.D1pL), and $0$ when the function itself is Lipschitz as well (f.D0pL).

The usual assumptions are special cases. Globally Lipschitz derivatives on the whole space are the
case $C = A = E$. Lipschitz derivatives on an open convex set $C$ are the case $A = C$. The
assumptions anchored on a sublevel set ([cartis2022evaluation], f.D1qLaB.X, (14.2.9)) take for $A$ a
set that contains the sublevel set $\{y \in X : f(y) \le f(x_0)\}$ of the source. The sublevel set
contains the iterates of a monotone method, so that the models built at the iterates are related to
the trial points by Taylor's theorem anchored at the iterate.

## Main definitions

* `LipschitzDerivsAnchored`: $f$ is $C^p$ near every point of the open convex set $C$, and
  $\nabla^j f$ is $L_j$-Lipschitz anchored in $A \subseteq C$ with respect to $C$ for
  $j_0 \le j \le p$.

## Main results

* `LipschitzDerivsAnchored.of_lipschitzOn`, `lipschitzDerivsAnchored_self_iff`: Lipschitz
  derivatives on $C$ are the case $A = C$.
* `LipschitzDerivsAnchored.of_contDiff`, `lipschitzDerivsAnchored_univ_iff`,
  `lipschitzDerivsAnchored_univ_top_iff`: on the whole space, the condition is the global Lipschitz
  continuity of the derivatives of a $C^p$ function.
* `LipschitzDerivsAnchored.mono_left`, `LipschitzDerivsAnchored.mono`,
  `LipschitzDerivsAnchored.mono_const`: the condition is monotone in the anchor set, the range of
  orders and the constants.
* `LipschitzDerivsAnchored.norm_iteratedFDeriv_le`: at an anchor, $\|\nabla^{j+1} f(x)\| \le L_j$.
* `LipschitzDerivsAnchored.abs_sub_taylorDecrement_le`: Taylor's theorem anchored at an anchor $x$,
  $|f(x + s) - T_{f,j}(x, s)| \le \frac{L_j}{(j+1)!} \|s\|^{j+1}$.

## Notation

* $T_{f,j}(x, s) = \sum_{i=0}^{j} \frac{1}{i!} \nabla^i f(x)[s]^i$ is the Taylor polynomial of order
  $j$ of $f$ at $x$, and $\Delta T_{f,j}(x, s) = T_{f,j}(x, 0) - T_{f,j}(x, s)$ is its decrease
  along $s$, `(ftaylorSeries ℝ f x).taylorDecrement j s`.

## Implementation notes

* The anchored condition on one order is `IteratedFDerivLipschitzAnchored` of
  `Numlib.Analysis.Calculus.AnchoredLipschitz`, and the Lipschitz condition on a set is
  `IteratedFDerivLipschitzOn`.
* The constants form a sequence `L : ℕ → ℝ`. Only the values $L_j$ for $j_0 \le j \le p$ matter
  (`LipschitzDerivsAnchored.congr_const`).
-/

open Finset
open scoped Nat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Let $f : E \to F$, let $C, A \subseteq E$, let $j_0, p \in \mathbb{N}$ and let $L$ be a real
sequence. The function $f$ has **anchored Lipschitz derivatives of orders $j_0$ to $p$** on $C$
with anchors $A$ if $C$ is open and convex, $A \subseteq C$, $f$ is $C^p$ at every point of $C$,
and for every $j_0 \le j \le p$
$$\|\nabla^j f(x) - \nabla^j f(y)\| \le L_j \|x - y\| \qquad \text{for all } x \in A \text{ and
  } y \in C.$$
This is the condition (14.2.9) of [cartis2022evaluation].

The anchored condition on each order is `IteratedFDerivLipschitzAnchored f j (L j) A C`. The
condition "$C^p$ at every point of $C$" is `ContDiffAt ℝ p f y` for $y \in C$. -/
structure LipschitzDerivsAnchored (f : E → F) (C A : Set E) (j₀ p : ℕ) (L : ℕ → ℝ) : Prop where
  /-- The set $C$ is open. -/
  isOpen : IsOpen C
  /-- The set $C$ is convex. -/
  convex : Convex ℝ C
  /-- The anchors lie in $C$: $A \subseteq C$. -/
  subset : A ⊆ C
  /-- The function $f$ is $C^p$ at every point of $C$. -/
  contDiffAt : ∀ y ∈ C, ContDiffAt ℝ p f y
  /-- For $j_0 \le j \le p$, the derivative $\nabla^j f$ is $L_j$-Lipschitz anchored in $A$ with
  respect to $C$. -/
  lipschitzAnchored : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzAnchored f j (L j) A C

namespace LipschitzDerivsAnchored

variable {f : E → F} {C A A' : Set E} {j₀ p : ℕ} {L L' : ℕ → ℝ}

/-- Let $C \subseteq E$ be open and convex, let $A \subseteq C$, and let $f : E \to F$ be $C^p$ at
every point of $C$. If $\nabla^j f$ is $L_j$-Lipschitz on $C$ for every $j_0 \le j \le p$, then
$f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$ and
constants $L$.

The Lipschitz condition on $C$ is `IteratedFDerivLipschitzOn`. -/
theorem of_lipschitzOn (hC : IsOpen C) (hCc : Convex ℝ C) (hA : A ⊆ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hL : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) C) :
    LipschitzDerivsAnchored f C A j₀ p L :=
  ⟨hC, hCc, hA, hf, fun j hj => (hL j hj).anchored hA⟩

/-- Let $f : E \to F$ be $C^p$, and let $\nabla^j f$ be $L_j$-Lipschitz on all of $E$ for every
$j_0 \le j \le p$. Then for every set $A \subseteq E$, $f$ has anchored Lipschitz derivatives of
orders $j_0$ to $p$ on $E$ with anchors $A$ and constants $L$.

The whole space is `Set.univ`. -/
theorem of_contDiff (hf : ContDiff ℝ p f)
    (hL : ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) Set.univ) (A : Set E) :
    LipschitzDerivsAnchored f Set.univ A j₀ p L :=
  of_lipschitzOn isOpen_univ convex_univ (Set.subset_univ A) (fun _ _ => hf.contDiffAt) hL

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $C$, then
$\nabla^j f$ is $L_j$-Lipschitz on $C$ for every $j_0 \le j \le p$. -/
theorem lipschitzOn (h : LipschitzDerivsAnchored f C C j₀ p L) {j : ℕ} (hj : j ∈ Icc j₀ p) :
    IteratedFDerivLipschitzOn f j (L j) C :=
  iteratedFDerivLipschitzAnchored_self_iff.1 (h.lipschitzAnchored j hj)

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on the whole space $E$, with
any anchors, then $f$ is $C^p$. -/
theorem contDiff (h : LipschitzDerivsAnchored f Set.univ A j₀ p L) : ContDiff ℝ p f :=
  contDiff_iff_contDiffAt.2 fun y => h.contDiffAt y (Set.mem_univ y)

/-- Let $C$ be open and convex and let $A \subseteq C$. The zero function has anchored Lipschitz
derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, with all constants $0$. -/
theorem zero_fun (hC : IsOpen C) (hCc : Convex ℝ C) (hA : A ⊆ C) :
    LipschitzDerivsAnchored (0 : E → F) C A j₀ p (fun _ => 0) :=
  of_lipschitzOn hC hCc hA (fun _ _ => contDiffAt_const) fun j _ =>
    iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => by
      have h0 : iteratedFDeriv ℝ j (0 : E → F) = 0 := iteratedFDeriv_fun_zero
      simp [h0]

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, and
$A' \subseteq A$, then the same holds with anchors $A'$. -/
theorem mono_left (h : LipschitzDerivsAnchored f C A j₀ p L) (hA : A' ⊆ A) :
    LipschitzDerivsAnchored f C A' j₀ p L :=
  ⟨h.isOpen, h.convex, hA.trans h.subset, h.contDiffAt,
    fun j hj => (h.lipschitzAnchored j hj).mono_left hA⟩

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, and
$j_0 \le j_1$ and $q \le p$, then $f$ has anchored Lipschitz derivatives of orders $j_1$ to $q$,
with the same constants. -/
theorem mono {j₁ q : ℕ} (h : LipschitzDerivsAnchored f C A j₀ p L) (hj : j₀ ≤ j₁) (hq : q ≤ p) :
    LipschitzDerivsAnchored f C A j₁ q L :=
  ⟨h.isOpen, h.convex, h.subset, fun y hy => (h.contDiffAt y hy).of_le (by exact_mod_cast hq),
    fun j hj' => h.lipschitzAnchored j (Icc_subset_Icc hj hq hj')⟩

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ with constants $L$, and
$L_j \le L'_j$ for every $j_0 \le j \le p$, then the same holds with constants $L'$. -/
theorem mono_const (h : LipschitzDerivsAnchored f C A j₀ p L)
    (hL : ∀ j ∈ Icc j₀ p, L j ≤ L' j) : LipschitzDerivsAnchored f C A j₀ p L' :=
  ⟨h.isOpen, h.convex, h.subset, h.contDiffAt,
    fun j hj => (h.lipschitzAnchored j hj).mono_const (hL j hj)⟩

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ with constants $L$, and
$L_j = L'_j$ for every $j_0 \le j \le p$, then the same holds with constants $L'$. Thus only the
constants of the orders $j_0$ to $p$ matter. -/
theorem congr_const (h : LipschitzDerivsAnchored f C A j₀ p L)
    (hL : ∀ j ∈ Icc j₀ p, L j = L' j) : LipschitzDerivsAnchored f C A j₀ p L' :=
  h.mono_const fun j hj => (hL j hj).le

/-- If $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$, then $f$ is $C^j$ at
every point of $C$ for every $j \le p$. -/
theorem contDiffAt_of_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ} (hj : j ≤ p) {y : E}
    (hy : y ∈ C) : ContDiffAt ℝ j f y :=
  (h.contDiffAt y hy).of_le (by exact_mod_cast hj)

/-- Let $f$ have anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, let
$j_0 \le j \le p$, and let $x \in A$. Then $\|\nabla^j f(y) - \nabla^j f(x)\| \le L_j \|y - x\|$
for all $y \in C$. -/
theorem lipschitzAt (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ} (hj : j ∈ Icc j₀ p)
    {x : E} (hx : x ∈ A) :
    ∀ y ∈ C, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ :=
  (h.lipschitzAnchored j hj).lipschitzAt hx

/-- Let $f$ have anchored Lipschitz derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, let
$j_0 \le j \le p$ with $L_j \ge 0$, and let $x \in A$. Then
$$\|\nabla^{j+1} f(x)\| \le L_j.$$
This is Theorem A.8.5 of [cartis2022evaluation].

For $j = p$ the derivative $\nabla^{p+1} f(x)$ need not exist. Then `iteratedFDeriv` takes
Mathlib's default value $0$, and the bound holds because $L_p \ge 0$. -/
theorem norm_iteratedFDeriv_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ}
    (hj : j ∈ Icc j₀ p) (hL : 0 ≤ L j) {x : E} (hx : x ∈ A) :
    ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L j := by
  rw [← norm_fderiv_iteratedFDeriv]
  refine norm_fderiv_le_of_lip' ℝ hL ?_
  filter_upwards [h.isOpen.mem_nhds (h.subset hx)] with y hy
  exact h.lipschitzAt hj hx y hy

end LipschitzDerivsAnchored

/-- Let $f : E \to F$. Then $f$ has anchored Lipschitz derivatives of orders $j_0$ to $p$ on the
whole space $E$ with anchors $E$ and constants $L$ if and only if $f$ is $C^p$ and $\nabla^j f$
is $L_j$-Lipschitz on $E$ for every $j_0 \le j \le p$. -/
theorem lipschitzDerivsAnchored_univ_iff {f : E → F} {j₀ p : ℕ} {L : ℕ → ℝ} :
    LipschitzDerivsAnchored f Set.univ Set.univ j₀ p L ↔
      ContDiff ℝ p f ∧ ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) Set.univ :=
  ⟨fun h => ⟨h.contDiff, fun _ hj => h.lipschitzOn hj⟩, fun ⟨hf, hL⟩ => .of_contDiff hf hL _⟩

/-- Let $f : E \to F$ and $L \in \mathbb{R}$. Then $f$ has anchored Lipschitz derivatives of the
single order $p$ on the whole space $E$, with anchors $E$ and constant $L$, if and only if $f$
is $C^p$ and $\nabla^p f$ is $L$-Lipschitz on $E$.

The constant sequence is `fun _ => L`. -/
theorem lipschitzDerivsAnchored_univ_top_iff {f : E → F} {p : ℕ} {L : ℝ} :
    LipschitzDerivsAnchored f Set.univ Set.univ p p (fun _ => L) ↔
      ContDiff ℝ p f ∧ IteratedFDerivLipschitzOn f p L Set.univ := by
  rw [lipschitzDerivsAnchored_univ_iff, Icc_self]
  simp

/-- Let $f : E \to F$ and $C \subseteq E$. Then $f$ has anchored Lipschitz derivatives of orders
$j_0$ to $p$ on $C$ with anchors $C$ and constants $L$ if and only if $C$ is open and convex,
$f$ is $C^p$ at every point of $C$, and $\nabla^j f$ is $L_j$-Lipschitz on $C$ for every
$j_0 \le j \le p$. -/
theorem lipschitzDerivsAnchored_self_iff {f : E → F} {C : Set E} {j₀ p : ℕ} {L : ℕ → ℝ} :
    LipschitzDerivsAnchored f C C j₀ p L ↔ IsOpen C ∧ Convex ℝ C ∧
      (∀ y ∈ C, ContDiffAt ℝ p f y) ∧ ∀ j ∈ Icc j₀ p, IteratedFDerivLipschitzOn f j (L j) C :=
  ⟨fun h => ⟨h.isOpen, h.convex, h.contDiffAt, fun _ hj => h.lipschitzOn hj⟩,
    fun ⟨hC, hCc, hf, hL⟩ => .of_lipschitzOn hC hCc Set.Subset.rfl hf hL⟩

namespace LipschitzDerivsAnchored

variable {f : E → ℝ} {C A : Set E} {j₀ p : ℕ} {L : ℕ → ℝ}

/-- **Taylor's theorem anchored at an anchor.** Let $f : E \to \mathbb{R}$ have anchored Lipschitz
derivatives of orders $j_0$ to $p$ on $C$ with anchors $A$, let $j_0 \le j \le p$, and let
$x \in A$ and $s \in E$ with $x + s \in C$. Then
$$\bigl|f(x + s) - \bigl(f(x) - \Delta T_{f,j}(x, s)\bigr)\bigr| \le \frac{L_j}{(j+1)!}
  \|s\|^{j+1},$$
where $\Delta T_{f,j}(x, s) = T_{f,j}(x, 0) - T_{f,j}(x, s)$ is the decrease of the Taylor
polynomial $T_{f,j}(x, s) = \sum_{i=0}^{j} \frac{1}{i!} \nabla^i f(x)[s]^i$. Since
$T_{f,j}(x, 0) = f(x)$, the left-hand side is $|f(x + s) - T_{f,j}(x, s)|$. This is (A.19) of
[cartis2022evaluation] under the condition (14.2.9).

The decrease $\Delta T_{f,j}(x, s)$ is `(ftaylorSeries ℝ f x).taylorDecrement j s`, see
`FormalMultilinearSeries.taylorDecrement`. -/
theorem abs_sub_taylorDecrement_le (h : LipschitzDerivsAnchored f C A j₀ p L) {j : ℕ}
    (hj : j ∈ Icc j₀ p) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) := by
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel, ← Real.norm_eq_abs]
  exact norm_sub_taylorPolynomial_le_of_lipschitzAnchored h.convex
    (fun y hy => h.contDiffAt_of_le (Finset.mem_Icc.1 hj).2 hy) (h.lipschitzAt hj hx)
    (h.subset hx) hxs

end LipschitzDerivsAnchored
