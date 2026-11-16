/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.ARqpCComplexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpDetailedStep
import Numlib.Optimization.ModelBased.HighOrder.TRqCall

/-!
# ARqpC runs as inner solvers

The two-phase method TPqp-GC of [cartis2022evaluation], §14.3, calls an inner solver INNER. Its
inner solver of adaptive-regularization type is ARqp-SC: the high-order regularization method for
$f : E \to \mathbb{R}$ on a closed feasible set $X$, whose Step 2 is the detailed Step 2 of
Algorithm 14.1.2. This file realizes ARqp-SC as an ARqpC run (`Optimization.IsARqpCRun`) with zero
composite part $c = 0 : E \to G$ and $h = 0$, where any normed space $G$ can be the codomain of $c$,
and with the halving set `compositeHalvingSet 0 X` of the source. This halving set contains the
orders $j \ge 2$, and also $j = 1$ when $X$ is not convex. Each call starts afresh from the radii
$1$ at a point that the outer method gives. It stops at its own termination, or earlier at a test of
the outer method. The file collects what an outer analysis needs about one call. The constants
depend on $f$ only through the constants $L_j$ of its derivatives on a set that contains the
sublevel set of the start of the call, so they are uniform over all calls. The trust-region inner
solver of `Numlib.Optimization.ModelBased.HighOrder.TRqCall` has the same form.

For $c = 0$ and $h = 0$ the model data are those of exact ARqp (`Optimization.arqpcData_zero`), so
such a run is an ARqp run with exact data (`Optimization.IsARqpCRun.isARqpRun_zero`). Both analyses
apply: the composite analysis gives decreases of order $\varepsilon_j^{j+1}$, the ARqpC-SC row of
(14.2.12), and the ARqp analysis gives decreases of order $\varepsilon_j^{\pi_j}$, the ARqp-SC row.
Here the exponents $\pi_j$ are those of `Optimization.arqpPiOf` in a radii mode $u$, as in
`Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity`. Below, $\bar L = \max(1, L_1, \dots,
L_p)$ (`finMax 1 L p`), $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p / (1 - \eta_2))$, and
$\kappa_\delta(\sigma_{\max}) = \varsigma \theta / (8 (3 \bar L + \sigma_{\max}))$
(`Optimization.arqpKappaDelta`). The usual hypotheses on $f$ are: $X \subseteq C$; $\nabla^p f$ is
$L_p$-Lipschitz anchored at the points of a set $A$ with respect to $C$ (`LipschitzDerivsAnchored f
C A p p L`); the jet bounds $\|\nabla^i f(y)\| \le \bar L$ hold for $i \in [2, p]$ and $y \in A$;
and $A$ contains the sublevel set $\{y \in X : f(y) \le f(x_0)\}$ of the start $x_0$.

## Main definitions

* `Optimization.arqpCallKappaDecr`, `Optimization.arqpCallKappaUnc`,
  `Optimization.arqpCallKappaRad`: the constants of Lemmas 14.2.2 and 14.2.3 and of the radius
  policy for a call. The constant `Optimization.arqpKappaUns` is defined in
  `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity`.
* `Optimization.arqpJetBound`: the jet bound $\max(1, \max_{i \in [2, p]} \|\nabla^i f(y)\|)$.
* `Optimization.IsARqpOutput`, `Optimization.IsARqpOutputCost`: a terminating call, without and with
  its evaluation counts.
* `Optimization.IsARqpCallOut`: a call stopped at any iteration up to its termination, with its
  iterates, its successful iterations and its returned radii.

## Main results

* `Optimization.IsARqpCRun.isARqpRun_zero`, `Optimization.arqpcStop_zero_iff`,
  `Optimization.arqpRatio_zero`: the reduction of the case $c = 0$, $h = 0$ to ARqp.
* `Optimization.IsARqpCRun.radii_zero`, `Optimization.IsARqpCRun.decrease_zero`,
  `Optimization.IsARqpCRun.decrease_composite_zero`, `Optimization.IsARqpCRun.radius_ge_zero`,
  `Optimization.IsARqpCRun.exists_cert_zero`: the radii, the decreases and the certificates of such
  runs.
* `Optimization.exists_isARqpOutputCost`, `Optimization.IsARqpOutputCost.cost_le`,
  `Optimization.IsARqpOutputCost.cost_le_arqp`: terminating calls exist, and their cost is bounded
  in both rows of (14.2.12).
* `Optimization.IsARqpCallOut.eq_of_not_succ`, `Optimization.IsARqpCallOut.le_count`,
  `Optimization.IsARqpCallOut.decrease`, `Optimization.IsARqpCallOut.decrease_arqp`,
  `Optimization.IsARqpCallOut.radius_ge`, and their bundle `Optimization.IsARqpCallOut.contract`:
  the contract of one call (Lemmas 14.2.2–14.2.3 and the radius policy).
* `Optimization.exists_isARqpRun_unit`, `Optimization.IsARqpUnitOutputCost.cost_le`,
  `Optimization.IsARqpUnitCallOut.contract`, `Optimization.exists_isARqpUnitCallOut_of_stop`: the
  calls of ARqp on the whole space with unit radii, for $q \le 2$.
* `Optimization.exists_isARqpCallOut_of_stop`: there are calls that stop at the first iterate that
  satisfies an external test, or at termination.

## Implementation notes

* The call predicates `Optimization.IsARqpOutput`, `Optimization.IsARqpOutputCost` and
  `Optimization.IsARqpCallOut` take the codomain $G$ of the zero constraint map as an explicit
  argument. They are then literally the predicates of the ARqpC runs with $c = 0 : E \to G$. In
  applications $G$ is the codomain of the constraints of the composite problem, for example
  $\mathbb{R}^0$. Every result holds for every $G$.
* The detailed Step 2 of such a run is that of the ARqp model `Optimization.regularizedModel`
  (`Optimization.isARqpCDetailedStep_zero_iff`). The runs are the ARqp runs with that Step 2
  (`Optimization.IsARqpCRun.isARqpRun_zero`, `Optimization.IsARqpCRun.of_isARqpRun_zero`).
* An ARqpC run (`Optimization.IsARqpCRun`) includes the conditions $1 \le q \le p$,
  $\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. The notions "iteration $k$ is reached",
  "does not terminate" and "successful", and the evaluation counts, are those of
  `Numlib.Optimization.ModelBased.HighOrder.ARqpComplexity`.
* The expression `finMin 1 u q` is $\min(1, u_1, \dots, u_q)$. For $u_j = \varepsilon_j^{\pi_j}$
  with $\varepsilon_j \in (0, 1]$ it is $\min_j \varepsilon_j^{\pi_j}$.
-/

open Set Metric
open scoped Nat

namespace Optimization

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-! ### ARqpC with $c = 0$ and $h = 0$ -/

section Zero

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℝ G] in
/-- The objective $y \mapsto f(y) + 0(0(y))$ of ARqpC with $c = 0$ and $h = 0$ is $f$. -/
theorem add_zero_comp_zero (f : E → ℝ) :
    (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) = f :=
  funext fun _ => by simp

/-- For $c = 0$ and $h = 0$, the model data of ARqpC are those of exact ARqp:
`arqpcData f 0 0 p x σ = arqpData f p x σ`. -/
@[simp] theorem arqpcData_zero (f : E → ℝ) (p : ℕ) (x : ℕ → E) (σ : ℕ → ℝ) :
    arqpcData f (0 : E → G) (0 : G → ℝ) p x σ = arqpData f p x σ :=
  funext fun _ => ARqpData.ofComposite_zero_fun _ _ _ _

/-- For $c = 0$ and $h = 0$, the termination test of ARqpC at iteration $k$ holds if and only if the
termination test of exact ARqp holds at $k$. -/
theorem arqpcStop_zero_iff {k : ℕ} :
    arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d k ↔ arqpStop f P p q ε x s σ δ d k := by
  rw [arqpcStop_iff, arqpcData_zero]

/-- For $c = 0$ and $h = 0$, the Step-1 test of ARqpC at iteration $k$ holds if and only if the
Step-1 test of exact ARqp holds at $k$. -/
theorem arqpStop₁_arqpcData_zero_iff {k : ℕ} :
    arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d k ↔
      arqpStop₁ P q ε (arqpData f p x σ) δ d k := by
  rw [arqpcData_zero]

/-- For $c = 0$ and $h = 0$, the ratio of ARqpC for the objective $f + 0 \circ 0$ at iteration $k$
equals the ratio $\rho_k$ of exact ARqp. -/
theorem arqpRatio_zero {k : ℕ} :
    arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) (arqpcData f (0 : E → G) 0 p x σ) x s k =
      arqpRho f p x s σ k := by
  rw [add_zero_comp_zero, arqpcData_zero]

/-- If $X$ is convex, then the order $1$ is not in the halving set `compositeHalvingSet 0 X` for
$h = 0$. So for convex $X$ this halving set contains only the orders $j \ge 2$. -/
theorem one_notMem_compositeHalvingSet_zero (hX : Convex ℝ X) :
    1 ∉ compositeHalvingSet (0 : G → ℝ) X :=
  one_notMem_compositeHalvingSet (convexOn_const 0 convex_univ) hX

/-- For $c = 0$ and $h = 0$, a pair $(s, \delta_s)$ is an output of the detailed Step 2 of ARqpC at
$x$ with weight $\sigma$ if and only if it is an output of the detailed Step 2
(`Optimization.IsDetailedStepOutput`) for the ARqp model $m(s) = T_{f,p}(x, s) + \sigma
\|s\|^{p+1} / (p+1)!$ over the feasible steps $\{s : x + s \in X\}$, with the displacements
$\{d : x + s + d \in X\}$ and the Taylor decrements of $m$.

The model is `regularizedModel (ftaylorSeries ℝ f x) p σ`, and its decrements are
`Optimization.arqpDetailedModelDec`. -/
theorem isARqpCDetailedStep_zero_iff {σ : ℝ} {x s : E} {δs : ℕ → ℝ} :
    IsARqpCDetailedStep f (0 : E → G) 0 X p q P ε J σ x s δs ↔
      IsDetailedStepOutput (regularizedModel (ftaylorSeries ℝ f x) p σ) {s | x + s ∈ X}
        (fun s => {d | x + s + d ∈ X}) (arqpDetailedModelDec (ftaylorSeries ℝ f x) p σ) q P.ς
        P.θ ε J s δs := by
  have em := compositeRegularizedModel_zero_fun (ftaylorSeries ℝ f x)
    (ftaylorSeries ℝ (0 : E → G) x) p σ
  have eΔ : (fun j s d => compositeModelDecrement (ftaylorSeries ℝ f x)
      (ftaylorSeries ℝ (0 : E → G) x) (0 : G → ℝ) p σ j s d) =
      arqpDetailedModelDec (ftaylorSeries ℝ f x) p σ := by
    funext j s d
    exact congrFun (compositeModelDecrement_zero_fun _ _ _ _ j s) d
  change IsDetailedStepOutput _ _ _ _ _ _ _ _ _ _ _ ↔ _
  rw [em, eΔ]

/-- **ARqp runs with the detailed Step 2 are ARqpC runs with $c = 0$, $h = 0$.** Let
$1 \le q \le p$, $\varepsilon \in (0, 1]^q$ and $\delta_0 \in (0, 1]^q$. Consider an ARqp run
with exact data on $X$ and initial radii $\delta_0$ whose Step-2 pair $(s_k, \delta_{s_k})$ is
an output of the detailed Step 2 for the ARqp model at $x_k$ with weight $\sigma_k$ and halving
set $J$, at every iteration $k$ that is reached and at which the Step-1 test fails. Then the
same sequences form an ARqpC run with $c = 0 : E \to G$, $h = 0$ and halving set $J$. -/
theorem IsARqpCRun.of_isARqpRun_zero (hq : 1 ≤ q) (hqp : q ≤ p)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hδ₀ : ∀ j ∈ Finset.Icc 1 q, 0 < δ₀ j ∧ δ₀ j ≤ 1)
    (hrun : IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm)
    (hdet : ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) →
      ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k →
      IsDetailedStepOutput (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k))
        {t | x k + t ∈ X} (fun t => {e | x k + t + e ∈ X})
        (arqpDetailedModelDec (ftaylorSeries ℝ f (x k)) p (σ k)) q P.ς P.θ ε J (s k) (δs k)) :
    IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm := by
  refine ⟨hq, hqp, hε, hδ₀, ?_, fun k hk h1 => isARqpCDetailedStep_zero_iff.2
    (hdet k (fun i hi => arqpcStop_zero_iff.not.1 (hk i hi))
      (arqpStop₁_arqpcData_zero_iff.not.1 h1))⟩
  rwa [add_zero_comp_zero, arqpcData_zero]

namespace IsARqpCRun

variable {C A : Set E} {L : ℕ → ℝ}

/-- **ARqpC with $c = 0$, $h = 0$ is ARqp.** An ARqpC run with $c = 0$ and $h = 0$ on $X$ is an ARqp
run with exact data on $X$, with the same sequences. -/
theorem isARqpRun_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm) :
    IsARqpRun f X P q ε δ₀ (arqpData f p x σ) x s σ δ δs d dm := by
  have h := hr.run
  rwa [add_zero_comp_zero, arqpcData_zero] at h

/-- Let an ARqpC run with $c = 0$ and $h = 0$ terminate at $k_\varepsilon$. Then $f$ does not
increase along the run up to $k_\varepsilon$: $f(x_j) \le f(x_i)$ for all
$i \le j \le k_\varepsilon$. -/
theorem antitone_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    {kε : ℕ} (hhit : IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε) :
    ∀ i j, i ≤ j → j ≤ kε → f (x j) ≤ f (x i) := by
  intro i j hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    exact (hr.isARqpRun_zero.objective_le fun l hl =>
      arqpcStop_zero_iff.not.1 (hhit.2 l (by omega))).trans (ih (by omega))

/-- The radius policy for $c = 0$. Consider an ARqpC run with $c = 0$ and $h = 0$, let
$X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect
to $C$, let $\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and $y \in A$, and let $A$ contain
$\{y \in X : f(y) \le f(x_0)\}$. Then at every iteration $k$ that is reached and at which the
Step-1 test fails, $$\delta_{s_k, j} \ge \kappa_\delta(\sigma_{\max}) \varepsilon_j \quad
\text{for all } j \in [1, q].$$

Here $\sigma_{\max}$ is `arSigmaMax P.toARParams (L p)` and $\kappa_\delta$ is
`Optimization.arqpKappaDelta` with the jet bound $\bar L$. -/
theorem arqpKappaDelta_mul_le_radius_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) :
    ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δs k j :=
  hr.arqpKappaDelta_mul_le_radius (Lw := L p) (Kw := finMax 1 L p) (Kf := finMax 1 L p)
    (Kc := 0) hf (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl (by simp) (zero_le_one.trans one_le_finMax)
    le_rfl (by simp) one_le_finMax hjet (fun _ _ _ _ => by simp) hXC
    (fun y hy hy' => hA y hy (by simpa using hy'))
    (fun i hi => arqpcStop_zero_iff.not.2 (hk i hi)) (arqpStop₁_arqpcData_zero_iff.not.2 h1)

/-- **The radii after a successful iteration in either radii mode.** Consider an ARqpC run with
$c = 0$, $h = 0$ and halving set $J$, and assume the hypotheses on $f$ of
`Optimization.IsARqpCRun.arqpKappaDelta_mul_le_radius_zero`. Let $u$ be a proposition such that
$u$ implies $q = 1$ and $1 \notin J$. Let iteration $k$ be reached, not terminate, and be
successful. Then

* if $u$ holds, then $\delta_{k+1, j} = 1$ for all $j \in [1, q]$;
* if $u$ fails, then $\|s_k\| \ge 1$, or $\delta_{k+1, j} \ge \kappa_\delta(\sigma_{\max})
  \varepsilon_j$ for all $j \in [1, q]$.

This is the radii hypothesis of `Optimization.IsARqpRun.decrease`. -/
theorem radii_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {u : Prop}
    (hu : u → q = 1 ∧ 1 ∉ J) {k : ℕ} (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i)
    (hs : P.η₁ ≤ arqpRho f p x s σ k) :
    (u → ∀ j ∈ Finset.Icc 1 q, δ (k + 1) j = 1) ∧
      (¬ u → 1 ≤ ‖s k‖ ∨ ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ (k + 1) j) := by
  have hrad : δ (k + 1) = δs k := (hr.isARqpRun_zero.radii k hk).1 hs
  have hk' : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i hi.le
  have h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k := fun h' => hk k le_rfl (Or.inl h')
  refine ⟨fun hu' j hj => ?_, fun _ => Or.inr fun j hj => ?_⟩
  · obtain ⟨hq1, h1J⟩ := hu hu'
    obtain rfl : j = 1 := by have := Finset.mem_Icc.1 hj; omega
    rw [hrad]
    exact hr.radius_eq_one (fun i hi => arqpcStop_zero_iff.not.2 (hk' i hi))
      (arqpStop₁_arqpcData_zero_iff.not.2 h1) h1J
  · rw [hrad]
    exact hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA hk' h1 j hj

/-- **Decrease with the exponents of the ARqp-SC row of (14.2.12)** ([cartis2022evaluation], Lemma
14.2.2). Assume the hypotheses of `Optimization.IsARqpCRun.radii_zero`, so that iteration $k$ is
reached, does not terminate and is successful. Assume also $L_p \ge 1$ and $\theta < \varsigma$,
and that the Step-1 test fails at $k + 1$. Then $$f(x_k) - f(x_{k+1}) \ge \eta_1 \kappa_{\Delta
m} \min_{j \in [1, q]} \varepsilon_j^{\pi_j},$$ where $\kappa_{\Delta m}$ and $\pi_j$ are the
constant and the exponents of the radii mode $u$ (`arqpKappaDmOf u P L p q` and
`arqpPiOf u p j`). -/
theorem decrease_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hθς : P.θ < P.ς) {u : Prop}
    [Decidable u] (hu : u → q = 1 ∧ 1 ∉ J) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    P.η₁ * (arqpKappaDmOf u P L p q * finMin 1 (fun j => ε j ^ arqpPiOf u p j) q) ≤
      f (x k) - f (x (k + 1)) :=
  (IsARqpRun.decrease hf hL hXC hA hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.isARqpRun_zero hk hs h1
    (hr.radii_zero hf hjet hXC hA hu hk hs)).2

/-- The radii of a run stay bounded below if they start so. Consider an ARqpC run with $c = 0$ and
$h = 0$, and assume the hypotheses on $f$ of
`Optimization.IsARqpCRun.arqpKappaDelta_mul_le_radius_zero`. If the initial radii satisfy
$\delta_{0,j} \ge \kappa_\delta(\sigma_{\max}) \varepsilon_j$ for $j \in [1, q]$, for example
$\delta_0 = 1$, then $\delta_{k,j} \ge \kappa_\delta(\sigma_{\max}) \varepsilon_j$ for
$j \in [1, q]$ at every iteration $k$ that is reached. -/
theorem radius_ge_zero (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A)
    (hδ₀ : ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ₀ j) :
    ∀ k, (∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i) → ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ δ k j := by
  have hrun := hr.isARqpRun_zero
  intro k
  induction k with
  | zero => intro _ j hj; rw [hrun.delta_zero]; exact hδ₀ j hj
  | succ k ih =>
    intro hk j hj
    have hk' : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
    obtain ⟨hs, hu⟩ := hrun.radii k hk'
    by_cases hρ : P.η₁ ≤ arqpRho f p x s σ k
    · rw [hs hρ]
      exact hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA (fun i hi => hk' i hi.le)
        (fun h' => hk' k le_rfl (Or.inl h')) j hj
    · rw [(hu hρ).1]
      exact ih (fun i hi => hk' i hi.le) j hj

end IsARqpCRun

end Zero

/-! ### The constants of a call -/

section Constants

variable (P : ARqpParams) (L : ℕ → ℝ) (p q : ℕ)

/-- The decrease constant of a call, $$\kappa_{\mathrm{decr}} = \eta_1 \kappa_{\Delta m},$$ of Lemma
14.2.2 of [cartis2022evaluation] in the ARqpC-SC row with $c = 0$, $h = 0$ and the exponents
$\pi_j = j + 1$. Here $L_j$ are the constants of the derivatives of the objective, and
$\kappa_{\Delta m}$ is `arqpcKappaDm P (L p) (finMax 1 L p) p q`, that is,
`Optimization.arqpcKappaDm` with $L_w = L_p$ and $K_w = \bar L$. -/
noncomputable def arqpCallKappaDecr : ℝ :=
  P.η₁ * arqpcKappaDm P (L p) (finMax 1 L p) p q

/-- The constant $$\kappa_{\mathrm{unc}} = \kappa_{\mathrm{uns}} + \frac{\log(\sigma_{\max} /
\sigma_0)}{\log \gamma_2}$$ of a call, with $\sigma_{\max} = \max(\sigma_0, \gamma_3 L_p / (1 -
\eta_2))$. It bounds the number of iterations of a call in excess of $\kappa_{\mathrm{uns}}$
times its number of successful iterations (Lemma 14.2.3 of [cartis2022evaluation]).

The first term $\kappa_{\mathrm{uns}}$ accounts for the last iteration of a call. -/
noncomputable def arqpCallKappaUnc : ℝ :=
  arqpKappaUns P + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂

/-- The radius constant of a call, $$\kappa_\rho = \min\left(\kappa_\delta(\sigma_{\max}),
\frac{1}{4 (3 \bar L + \sigma_{\max})}\right),$$ where $\kappa_\delta$ is computed with
$\bar L = \max(1, L_1, \dots, L_p)$. The radii that certify the output of a call are at least
$\kappa_\rho \varepsilon_j$. -/
noncomputable def arqpCallKappaRad : ℝ :=
  min (arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)))
    (1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))))

variable {P L p q}

/-- $\kappa_{\mathrm{unc}} \ge 0$. -/
theorem arqpCallKappaUnc_nonneg (P : ARqpParams) (L : ℕ → ℝ) (p : ℕ) :
    0 ≤ arqpCallKappaUnc P L p := by
  unfold arqpCallKappaUnc
  have := arqpKappaUns_nonneg (P := P)
  have := P.log_γ₂_pos
  have : 0 ≤ Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) :=
    Real.log_nonneg ((one_le_div P.σ₀_pos).2 (σ₀_le_arSigmaMax _ _))
  positivity

/-- If $\sigma_{\min} > 0$, $\theta < \varsigma$ and $L_p \ge 1$, then $\kappa_{\mathrm{decr}} > 0$.
-/
theorem arqpCallKappaDecr_pos (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hL : 1 ≤ L p) :
    0 < arqpCallKappaDecr P L p q := by
  have hσ := arSigmaMax_pos P.toARParams (L p)
  have hκ : 0 < arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
    arqpKappaDelta_pos P (zero_le_one.trans one_le_finMax) hσ
  have hb : 0 < (P.ς - P.θ) / ((q ! : ℝ) * (L p + arSigmaMax P.toARParams (L p))) *
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) ^ q / 3 := by
    have : 0 < P.ς - P.θ := by linarith
    have : 0 < L p + arSigmaMax P.toARParams (L p) := by linarith
    positivity
  rw [arqpCallKappaDecr, arqpcKappaDm_def]
  have := P.η₁_pos
  have := Real.rpow_pos_of_pos hb (((p : ℝ) + 1) / ((p : ℝ) - q + 1))
  positivity

/-- $\kappa_\rho > 0$. -/
theorem arqpCallKappaRad_pos : 0 < arqpCallKappaRad P L p := by
  have hσ := arSigmaMax_pos P.toARParams (L p)
  have hL1 : 1 ≤ finMax 1 L p := one_le_finMax
  refine lt_min (arqpKappaDelta_pos P (by linarith) hσ) ?_
  have : 0 < 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by positivity
  positivity

/-- $\kappa_\rho \le \kappa_\delta(\sigma_{\max})$, with $\kappa_\delta$ computed with $\bar L$. -/
theorem arqpCallKappaRad_le_arqpKappaDelta :
    arqpCallKappaRad P L p ≤ arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) :=
  min_le_left _ _

/-- Let $\varepsilon_j \in (0, 1]$, $1 \le K \le \bar L$ and $0 < \sigma \le \sigma_{\max}$. Then
$\kappa_\rho \varepsilon_j \le \min(1, \varepsilon_j / (4 (3 K + \sigma)))$. -/
theorem arqpCallKappaRad_mul_le_min {εj J σ : ℝ} (hε : εj ∈ Ioc 0 1) (hJ1 : 1 ≤ J)
    (hJ : J ≤ finMax 1 L p) (hσ0 : 0 < σ) (hσ : σ ≤ arSigmaMax P.toARParams (L p)) :
    arqpCallKappaRad P L p * εj ≤ min 1 (εj / (4 * (3 * J + σ))) := by
  obtain ⟨hε0, hε1⟩ := hε
  have hrad1 : arqpCallKappaRad P L p ≤
      1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) := min_le_right _ _
  have hK : 0 < 4 * (3 * J + σ) := by linarith
  have hK' : 4 * (3 * J + σ) ≤ 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by
    linarith
  have hKm : 0 < 4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p)) := by linarith
  refine le_min ?_ ?_
  · calc arqpCallKappaRad P L p * εj
        ≤ 1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) * 1 :=
          mul_le_mul hrad1 hε1 hε0.le (div_pos one_pos hKm).le
      _ ≤ 1 := by rw [mul_one, div_le_one hKm]; linarith
  · calc arqpCallKappaRad P L p * εj
        ≤ 1 / (4 * (3 * finMax 1 L p + arSigmaMax P.toARParams (L p))) * εj :=
          mul_le_mul_of_nonneg_right hrad1 hε0.le
      _ ≤ εj / (4 * (3 * J + σ)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hε0.le hK hK'

/-- $\kappa_{\mathrm{unc}} = \kappa_{\mathrm{uns}} + \log(\sigma_{\max} / \sigma_0) / \log
\gamma_2$. -/
theorem arqpCallKappaUnc_eq :
    arqpCallKappaUnc P L p =
      arqpKappaUns P + Real.log (arSigmaMax P.toARParams (L p) / P.σ₀) / Real.log P.γ₂ := rfl

end Constants

section Zero

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {C A : Set E} {L : ℕ → ℝ}

/-- **Decrease with the exponents of the ARqpC-SC row of (14.2.12)** ([cartis2022evaluation], Lemma
14.2.2 with $c = 0$, $h = 0$). Consider an ARqpC run with $c = 0$ and $h = 0$, let
$X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect
to $C$, with $L_p \ge 1$, let $\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and $y \in A$,
let $A$ contain $\{y \in X : f(y) \le f(x_0)\}$, and let $\theta < \varsigma$. Let iteration $k$
be reached, not terminate, and be successful, and let the Step-1 test fail at $k + 1$. Then for
some $j \in [1, q]$ $$f(x_k) - f(x_{k+1}) \ge \kappa_{\mathrm{decr}} \varepsilon_j^{j+1},$$
where $\kappa_{\mathrm{decr}}$ is `Optimization.arqpCallKappaDecr`. -/
theorem IsARqpCRun.decrease_composite_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hθς : P.θ < P.ς) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δ d i) (hs : P.η₁ ≤ arqpRho f p x s σ k)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (k + 1)) :
    ∃ j ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε j ^ (j + 1) ≤ f (x k) - f (x (k + 1)) := by
  have hpol := (hr.radii_zero hf hjet hXC hA (u := False) (fun h => h.elim) hk hs).2 not_false
  obtain ⟨j, hj, -, hdec⟩ := hr.run.composite_decrease (Lw := L p) (Kw := finMax 1 L p) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset) hasLipschitzConst_zero hL
    le_rfl (by simp) one_le_finMax hXC (fun z hz hz' => hA z hz (by simpa using hz'))
    hr.one_le_q hr.q_le_p hθς hr.ε_mem hr.δ₀_mem (fun i hi => arqpcStop_zero_iff.not.2 (hk i hi))
    (by rw [arqpRatio_zero]; exact hs) (arqpStop₁_arqpcData_zero_iff.not.2 h1) hpol
  refine ⟨j, hj, ?_⟩
  unfold arqpCallKappaDecr
  rw [mul_assoc]
  simpa using hdec

end Zero

/-- The **jet bound** $$J(y) = \max\left(1, \max_{i \in [2, p]} \|\nabla^i f(y)\|\right)$$ of $f$ at
$y$. It can be computed from the derivatives that Step 1 of ARqp evaluates at $y$.

The definition is `finMax 1 (fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) f y‖ else 0) p`,
in which the term of index $p$ is $0$. -/
noncomputable def arqpJetBound (f : E → ℝ) (p : ℕ) (y : E) : ℝ :=
  finMax 1 (fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) f y‖ else 0) p

/-- The jet bound is at least $1$. -/
theorem one_le_arqpJetBound (f : E → ℝ) (p : ℕ) (y : E) : 1 ≤ arqpJetBound f p y :=
  le_finMax_left

/-- If $M \ge 1$ and $\|\nabla^i f(y)\| \le M$ for $i \in [2, p]$, then the jet bound satisfies
$J(y) \le M$. -/
theorem arqpJetBound_le {f : E → ℝ} {p : ℕ} {y : E} {M : ℝ} (hM : 1 ≤ M)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖ ≤ M) : arqpJetBound f p y ≤ M := by
  refine finMax_le hM fun i hi => ?_
  split_ifs with hip
  · exact hjet (i + 1) (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by omega⟩)
  · exact zero_le_one.trans hM

/-- The jet bound bounds the derivatives: $\|\nabla^i f(y)\| \le J(y)$ for $i \in [2, p]$. -/
theorem norm_iteratedFDeriv_le_arqpJetBound (f : E → ℝ) {p : ℕ} (y : E) {i : ℕ}
    (hi : i ∈ Finset.Icc 2 p) : ‖iteratedFDeriv ℝ i f y‖ ≤ arqpJetBound f p y := by
  have hi' : i - 1 ∈ Finset.Icc 1 p := Finset.mem_Icc.2
    ⟨by have := (Finset.mem_Icc.1 hi).1; omega, by have := (Finset.mem_Icc.1 hi).2; omega⟩
  refine le_trans (le_of_eq ?_) (le_finMax hi')
  have hlt : i - 1 < p := by have := (Finset.mem_Icc.1 hi); omega
  simp only [hlt, ite_true]
  rw [Nat.sub_add_cancel (by have := (Finset.mem_Icc.1 hi).1; omega : 1 ≤ i)]

/-! ### Certificates at termination -/

section Certificate

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {J : Set ℕ} {ε δ₀ : ℕ → ℝ}
  {x s : ℕ → E} {σ : ℕ → ℝ} {δ δs : ℕ → ℕ → ℝ} {d dm : ℕ → ℕ → E} {C A : Set E} {L : ℕ → ℝ}

/-- **The certificate at a termination in Step 2.** Consider an ARqpC run with $c = 0$ and $h = 0$,
and an iteration $k$ that is reached, at which the Step-1 test fails and the Step-2 test
$m_k(s_k) = m_k(0)$ holds. Let $f$ be of class $C^p$ at $x_k$, and let $J = J(x_k)$ be the jet
bound. Then the radii $$r_j = \min\left(1, \frac{\varepsilon_j}{4 (3 J + \sigma_k)}\right)$$ lie
in $(0, 1]$ for $j \in [1, q]$, and $x_k$ is an $(\varepsilon, r)$-approximate $q$-th order
minimizer over $\{e : x_k + e \in X\}$.

The reason is that $0$ minimizes the model at $x_k$. The proof specializes
`Optimization.isEpsDeltaApprox_of_isMinOn_zero_of_jet`. -/
theorem IsARqpCRun.isEpsDeltaApprox_of_stop₂_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε δ₀ x s σ δ δs d dm) {k : ℕ}
    (hk : ∀ i < k, ¬ arqpStop f P p q ε x s σ δ d i)
    (h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d k) (h2 : arqpStop₂ (arqpData f p x σ) s k)
    (hcd : ContDiffAt ℝ p f (x k)) :
    (∀ j ∈ Finset.Icc 1 q, min 1 (ε j / (4 * (3 * arqpJetBound f p (x k) + σ k))) ∈ Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} q ε
        (fun j => min 1 (ε j / (4 * (3 * arqpJetBound f p (x k) + σ k)))) := by
  have hrun := hr.isARqpRun_zero
  exact isEpsDeltaApprox_of_isMinOn_zero_of_jet (hrun.mem k hk) hcd
    (L := fun i => if i < p then ‖iteratedFDeriv ℝ (i + 1) f (x k)‖ else 0)
    (fun i hi => norm_iteratedFDeriv_le_arqpJetBound f (x k) hi) hr.q_le_p hr.ε_mem
    (hrun.toIsARRun.sigma_pos hk k le_rfl) ((hrun.step hk h1).isMinOn_of_eq h2)

/-- **The certificate of a terminating run with explicit radii.** Consider an ARqpC run with
$c = 0$, $h = 0$ and initial radii $\delta_0 = 1$, and assume the hypotheses on $f$ of
`Optimization.IsARqpCRun.arqpKappaDelta_mul_le_radius_zero`. Let the run terminate at
$k_\varepsilon$. Then there are radii $\delta_\varepsilon \in (0, 1]^q$ with
$\delta_{\varepsilon, j} \ge \kappa_\rho \varepsilon_j$ for $j \in [1, q]$ such that
$x_{k_\varepsilon}$ is an $(\varepsilon, \delta_\varepsilon)$-approximate $q$-th order minimizer
over $\{e : x_{k_\varepsilon} + e \in X\}$.

Here $\kappa_\rho$ is `Optimization.arqpCallKappaRad`. -/
theorem IsARqpCRun.exists_cert_zero
    (hr : IsARqpCRun f (0 : E → G) 0 X p q P J ε (fun _ => 1) x s σ δ δs d dm)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) {kε : ℕ}
    (hhit : IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε) :
    ∃ δε : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δε j ∧ δε j ≤ 1) ∧
      (∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δε j) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε δε := by
  have hrun := hr.isARqpRun_zero
  have hk : ∀ i < kε, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i hi)
  have hstop : arqpStop f P p q ε x s σ δ d kε := arqpcStop_zero_iff.1 hhit.1
  have hε := hr.ε_mem
  have hσ := hrun.sigma_le_of_anchored hf hXC hA kε hk
  have hσ0 : 0 < σ kε := hrun.toIsARRun.sigma_pos hk kε le_rfl
  have hxA : x kε ∈ A := hA _ (hrun.mem kε hk) (hrun.mem_sublevel kε hk).2
  by_cases h1 : arqpStop₁ P q ε (arqpData f p x σ) δ d kε
  · refine ⟨δ kε, fun j hj => hrun.delta_mem hr.δ₀_mem kε hk j hj, fun j hj => ?_,
      MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness kε hk) h1⟩
    have hδ₀ : ∀ j ∈ Finset.Icc 1 q,
        arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ 1 :=
      fun j hj => by
        have h1 := arqpKappaDelta_lt_one P (one_le_finMax (L := L) (p := p))
          (arSigmaMax_pos P.toARParams (L p)).le
        have h2 := hε j hj
        have h3 := arqpKappaDelta_pos P (zero_le_one.trans (one_le_finMax (L := L) (p := p)))
          (arSigmaMax_pos P.toARParams (L p))
        nlinarith [h2.1, h2.2]
    exact (mul_le_mul_of_nonneg_right arqpCallKappaRad_le_arqpKappaDelta (hε j hj).1.le).trans
      (hr.radius_ge_zero hf hjet hXC hA hδ₀ kε hk j hj)
  · obtain ⟨hδ, hcert⟩ := hr.isEpsDeltaApprox_of_stop₂_zero hk h1 (hstop.resolve_left h1)
      (hf.contDiffAt _ (hf.subset hxA))
    exact ⟨_, hδ, fun j hj => arqpCallKappaRad_mul_le_min (hε j hj) (one_le_arqpJetBound f p _)
      (arqpJetBound_le one_le_finMax fun i hi => hjet i hi _ hxA) hσ0 hσ.2, hcert⟩

end Certificate

/-! ### Terminating calls and their cost -/

section Output

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {C A : Set E}
  {L : ℕ → ℝ}

variable (G) in
/-- **The output of a call** $\mathrm{INNER}(f, X, q, x^S, \varepsilon)$ realized by ARqp-SC. A pair
$(y, \delta)$ is such an output if

* there is an ARqpC run with $c = 0 : E \to G$, $h = 0$, the halving set
  `compositeHalvingSet 0 X` and initial radii $1$ on $f$, which starts at $x_0 = x^S$,
  terminates at some $k_\varepsilon$, and has $x_{k_\varepsilon} = y$;
* the radii satisfy $\delta \in (0, 1]^q$;
* $y$ is an $(\varepsilon, \delta)$-approximate $q$-th order minimizer over
  $\{e : y + e \in X\}$. -/
def IsARqpOutput (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xS y : E)
    (δ : ℕ → ℝ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧ x 0 = xS ∧ x kε = y) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ

variable (G) in
/-- **The output of a call with its cost.** A pair $(y, \delta)$ is the output of a call from $x^S$
as in `Optimization.IsARqpOutput`, whose run uses $n_F$ evaluations of $f$ and $n_D$ evaluations
of its derivatives. That is, $n_F = k_\varepsilon + 1$ (`Optimization.funEvalCount`) and $n_D$
is one plus the number of successful iterations before $k_\varepsilon$
(`Optimization.derivEvalCount`), where $k_\varepsilon$ is the termination index of the run. -/
def IsARqpOutputCost (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ)
    (xS y : E) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ

namespace IsARqpOutput

variable {xS y : E} {δ : ℕ → ℝ}

/-- The output of a call is feasible: $y \in X$. -/
theorem mem (h : IsARqpOutput G f X p q P ε xS y δ) : y ∈ X := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, -, rfl⟩, -⟩ := h
  exact hr.mem hhit.2

/-- A call does not increase $f$: $f(y) \le f(x^S)$. -/
theorem le (h : IsARqpOutput G f X p q P ε xS y δ) : f y ≤ f xS := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, rfl, rfl⟩, -⟩ := h
  exact hr.antitone_zero hhit 0 kε (Nat.zero_le _) le_rfl

/-- The output radii lie in $(0, 1]$. -/
theorem radius_mem (h : IsARqpOutput G f X p q P ε xS y δ) :
    ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1 := h.2.1

/-- The output $y$ is an $(\varepsilon, \delta)$-approximate $q$-th order minimizer over
$\{e : y + e \in X\}$, with the output radii $\delta$. -/
theorem isEpsDeltaApprox (h : IsARqpOutput G f X p q P ε xS y δ) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ X} q ε δ := h.2.2

end IsARqpOutput

namespace IsARqpOutputCost

variable {xS y : E} {δ : ℕ → ℝ} {nF nD : ℕ}

/-- The output of a call with its cost is the output of a call. -/
theorem isARqpOutput (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) :
    IsARqpOutput G f X p q P ε xS y δ := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy, -, -⟩, hδ, happ⟩ := h
  exact ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, h0, hy⟩, hδ, happ⟩

/-- The tolerances of a call lie in $(0, 1]$: $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$. -/
theorem ε_mem (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) :
    ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.ε_mem

/-- A call has $q \ge 1$. -/
theorem one_le_q (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : 1 ≤ q := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.one_le_q

/-- A call has $q \le p$. -/
theorem q_le_p (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : q ≤ p := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, -⟩, -⟩ := h
  exact hr.q_le_p

/-- A call evaluates $f$ and its derivatives at least once: $n_F \ge 1$ and $n_D \ge 1$. -/
theorem one_le (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD) : 1 ≤ nF ∧ 1 ≤ nD := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, -, -, -, -, rfl, rfl⟩, -, -⟩ := h
  simp [derivEvalCount, funEvalCount]

/-- **The cost of a terminating call, ARqpC-SC row** ([cartis2022evaluation], Theorem 14.2.4 with
$c = 0$, $h = 0$ and $\pi_j = j + 1$). Let $(y, \delta)$ be the output of a call from $x^S$ with
the costs $n_F$ and $n_D$. Let $f \ge f_{\mathrm{low}}$ on $X$, let $X \subseteq C$, let
$\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect to $C$, with
$L_p \ge 1$, let $\|\nabla^i f(z)\| \le \bar L$ for $i \in [2, p]$ and $z \in A$, let $A$
contain $\{z \in X : f(z) \le f(x^S)\}$, and let $\sigma_{\min} > 0$ and $\theta < \varsigma$.
Then, with $m_\varepsilon = \min_{j \in [1, q]} \varepsilon_j^{j+1}$, $$n_F \le
\kappa_{\mathrm{uns}} \frac{f(x^S) - f_{\mathrm{low}}}{\kappa_{\mathrm{decr}} m_\varepsilon} +
\kappa^c \quad\text{and}\quad n_D \le \frac{f(x^S) - f_{\mathrm{low}}}{\kappa_{\mathrm{decr}}
m_\varepsilon} + 2,$$ where $\kappa_{\mathrm{decr}}$ is `Optimization.arqpCallKappaDecr` and
$\kappa^c$ is `Optimization.kappaCARqp`. -/
theorem cost_le {flow : ℝ} (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD)
    (hb : ∀ z ∈ X, flow ≤ f z) (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ z ∈ A, ‖iteratedFDeriv ℝ i f z‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ z ∈ X, f z ≤ f xS → z ∈ A) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) :
    (nF : ℝ) ≤ arqpKappaUns P * ((f xS - flow) /
        (arqpCallKappaDecr P L p q * finMin 1 (fun j => ε j ^ (j + 1)) q)) + kappaCARqp P L p ∧
      (nD : ℝ) ≤ (f xS - flow) /
        (arqpCallKappaDecr P L p q * finMin 1 (fun j => ε j ^ (j + 1)) q) + 2 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  have hε := hr.ε_mem
  set mε := finMin 1 (fun j => ε j ^ (j + 1)) q
  have hmε0 : 0 < mε := finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε', hhit', -, hF', hD'⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  obtain rfl := hhit'.unique hhit
  have e0 : f (x 0) + (0 : G → ℝ) ((0 : E → G) (x 0)) - flow = f (x 0) - flow := by simp
  have e1 : P.η₁ * (arqpcKappaDm P (L p) (finMax 1 L p) p q * mε) =
      arqpCallKappaDecr P L p q * mε := by
    unfold arqpCallKappaDecr; ring
  rw [e0, e1] at hF' hD'
  exact ⟨hF', hD'⟩

/-- **The cost of a terminating call, ARqp-SC row** ([cartis2022evaluation], Theorem 14.2.4 for
ARqp-SC). Assume the hypotheses of `Optimization.IsARqpOutputCost.cost_le`, and let $u$ be a
radii mode such that $u$ implies $q = 1$ and the convexity of $X$. Then, with $m_\varepsilon =
\min_{j \in [1, q]} \varepsilon_j^{\pi_j}$ and the exponents $\pi_j$ of the radii mode $u$
(`arqpPiOf u p j`), $$n_F \le \frac{\kappa^a (f(x^S) - f_{\mathrm{low}})}{m_\varepsilon} +
\kappa^c \quad\text{and}\quad n_D \le \frac{\kappa^s (f(x^S) -
f_{\mathrm{low}})}{m_\varepsilon} + 2,$$ where $\kappa^a$ and $\kappa^s$ are the constants of
the radii mode $u$ (`kappaAARqpOf u P L p q` and `kappaSARqpOf u P L p q`) and $\kappa^c$ is
`Optimization.kappaCARqp`. -/
theorem cost_le_arqp {flow : ℝ} (h : IsARqpOutputCost G f X p q P ε xS y δ nF nD)
    (hb : ∀ z ∈ X, flow ≤ f z) (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ z ∈ A, ‖iteratedFDeriv ℝ i f z‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ z ∈ X, f z ≤ f xS → z ∈ A) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) :
    (nF : ℝ) ≤ kappaAARqpOf u P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + kappaCARqp P L p ∧
      (nD : ℝ) ≤ kappaSARqpOf u P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf u p j) q + 2 := by
  obtain ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  have hrun := hr.isARqpRun_zero
  obtain ⟨kε', hhit', hF', hD'⟩ := hrun.exists_isFirstHit_of_anchored hb hf hL hXC hA
    hr.one_le_q hr.q_le_p hσmin hθς hr.ε_mem (u := u) fun k hk hs =>
      hr.radii_zero hf hjet hXC hA
        (fun hu' => ⟨(hu hu').1, one_notMem_compositeHalvingSet_zero (hu hu').2⟩)
        (fun i hi => hk i (by omega)) hs
  have hhit'' : IsFirstHit (arqpStop f P p q ε x s σ δ d) kε :=
    ⟨arqpcStop_zero_iff.1 hhit.1, fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i hi)⟩
  obtain rfl := hhit'.unique hhit''
  have e : (fun k => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s k) = fun k => P.η₁ ≤ arqpRho f p x s σ k :=
    funext fun k => by rw [arqpRatio_zero]
  rw [e]
  exact ⟨hF', hD'⟩

end IsARqpOutputCost

variable (G) in
/-- **Terminating calls exist.** Let $E$ be finite-dimensional, let $X$ be closed and $x^S \in X$,
and let $f \ge f_{\mathrm{low}}$ on $X$. Let $X \subseteq C$, let $\nabla^p f$ be
$L_p$-Lipschitz anchored at the points of $A$ with respect to $C$, with $L_p \ge 1$, let
$\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and $y \in A$, and let $A$ contain
$\{y \in X : f(y) \le f(x^S)\}$. Let $\sigma_{\min} > 0$, $\theta < \varsigma$, $1 \le q \le p$
and $\varepsilon \in (0, 1]^q$. Then there is a terminating call from $x^S$ with some output
$(y, \delta)$ and costs $n_F$, $n_D$ (`Optimization.IsARqpOutputCost`), whose radii satisfy
$\delta_j \ge \kappa_\rho \varepsilon_j$ for $j \in [1, q]$.

Here $\kappa_\rho$ is `Optimization.arqpCallKappaRad`. -/
theorem exists_isARqpOutputCost [FiniteDimensional ℝ E] {flow : ℝ} (hX : IsClosed X) {xS : E}
    (hxS : xS ∈ X) (hb : ∀ y ∈ X, flow ≤ f y) (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f xS → y ∈ A) (P : ARqpParams) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (y : E) (δ : ℕ → ℝ) (nF nD : ℕ), IsARqpOutputCost G f X p q P ε xS y δ nF nD ∧
      ∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δ j := by
  obtain ⟨x, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_compositeHalvingSet
    (f := f) (c := (0 : E → G)) (p := p) hasLipschitzConst_zero isSubadditive_zero rfl P hq hqp
    hε (δ₀ := fun _ => 1) (fun _ _ => ⟨one_pos, le_rfl⟩) hX hxS
  subst hx0
  have hmε0 : 0 < finMin 1 (fun j => ε j ^ (j + 1)) q :=
    finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε, hhit, -, -, -⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  obtain ⟨δε, hδε, hrad, happ⟩ := hr.exists_cert_zero hf hjet hXC hA hhit
  exact ⟨x kε, δε, _, _, ⟨⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, rfl, rfl, rfl, rfl⟩, hδε, happ⟩,
    hrad⟩

end Output

/-! ### Calls stopped by the outer method -/

section CallOut

variable {f : E → ℝ} {X : Set E} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {C A : Set E}
  {L : ℕ → ℝ}

variable (G) in
/-- **A call of ARqp-SC with its returned radii** ([cartis2022evaluation], Algorithm 14.1.1 with
$c = 0$, $h = 0$ used as INNER, for example in Algorithm 14.3.2). The points
$x^i_0, \dots, x^i_e$, the predicate $\mathrm{succ}$ and the radii $\delta^o$ form such a call
if there is an ARqpC run with $c = 0 : E \to G$, $h = 0$, the halving set
`compositeHalvingSet 0 X` and initial radii $1$ on $f$ with the following properties.

* The run terminates at some $k_\varepsilon \ge e$, so the call may be stopped before
  termination.
* The points $x^i_0, \dots, x^i_e$ are the first $e + 1$ iterates of the run.
* For $i < e$, $\mathrm{succ}(i)$ holds if and only if iteration $i$ of the run is successful.
* The returned radii $\delta^o$ are, at the orders $j \in [1, q]$, one of the following: the
  current radii $\delta_e$ (at a termination in Step 1 these certify the output); or, if the
  Step-1 test fails at $e$, the Step-2 radii $\delta_{s_e}$; or, if $e = k_\varepsilon$ and the
  Step-1 test fails at $e$ (a termination in Step 2), the radii
  $\min(1, \varepsilon_j / (4 (3 J + \sigma_e)))$ with the jet bound $J = J(x_e)$.

In the last case the radii certify $(\varepsilon, \delta^o)$-approximate optimality at $x_e$, by
`Optimization.IsARqpCRun.isEpsDeltaApprox_of_stop₂_zero`. In Lean the points are `xi`, the
predicate is `succ` and the radii are `δo`. -/
def IsARqpCallOut (f : E → ℝ) (X : Set E) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ)
    (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δ δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpCRun f (0 : E → G) 0 X p q P (compositeHalvingSet (0 : G → ℝ) X) ε (fun _ => 1) x s σ
      δ δs d dm ∧
    IsFirstHit (arqpcStop f (0 : E → G) 0 P p q ε x s σ δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i)) ∧
    ((∀ j ∈ Finset.Icc 1 q, δo j = δ e j) ∨
      (¬ arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = δs e j) ∨
      (e = kε ∧ ¬ arqpStop₁ P q ε (arqpcData f (0 : E → G) 0 p x σ) δ d e ∧
        ∀ j ∈ Finset.Icc 1 q, δo j = min 1 (ε j / (4 * (3 * arqpJetBound f p (x e) + σ e)))))

namespace IsARqpCallOut

variable {xi : ℕ → E} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- A call does not increase $f$: $f(x^i_{i+1}) \le f(x^i_i)$ for all $i < e$. -/
theorem antitone (h : IsARqpCallOut G f X p q P ε xi e succ δo) :
    ∀ i < e, f (xi (i + 1)) ≤ f (xi i) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, -, -⟩ := h
  intro i hi
  rw [hxi i (by omega), hxi (i + 1) (by omega)]
  exact hr.antitone_zero hhit i (i + 1) (by omega) (by omega)

/-- The unsuccessful iterations of a call do not move: if $i < e$ and $\mathrm{succ}(i)$ fails, then
$x^i_{i+1} = x^i_i$. -/
theorem eq_of_not_succ (h : IsARqpCallOut G f X p q P ε xi e succ δo) :
    ∀ i < e, ¬ succ i → xi (i + 1) = xi i := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  intro i hi hs
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hrun.toIsARRun.eq_of_not_succ (fun l hl => hnot l (by omega))
    (not_le.1 ((hsucc' i hi).not.1 hs))

open Classical in
/-- **The number of iterations of a call** ([cartis2022evaluation], Lemma 14.2.3). Let
$X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect
to $C$, and let $A$ contain the sublevel set $\{y \in X : f(y) \le f(x^i_0)\}$ of the start of
the call. Then $$e \le \kappa_{\mathrm{uns}} |\mathcal{S}| + \kappa_{\mathrm{unc}},$$ where
$\mathcal{S} = \{i < e : \mathrm{succ}(i)\}$ is the set of successful iterations of the call and
$\kappa_{\mathrm{unc}}$ is `Optimization.arqpCallKappaUnc`. -/
theorem le_count (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) :
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have h3 := hrun.toIsARRun.le_succ_count (k := e) hnot
    (hrun.sigma_le_of_anchored hf hXC hA e hnot).2
  set ρ := fun i => P.η₁ ≤ arqpRho f p x s σ i
  have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
    Finset.filter_congr fun i hi => hsucc' i (Finset.mem_range.1 hi)
  have hcard' := card_successSet_le_card_filter_add_one ρ e
  have hκ := arqpKappaUns_nonneg (P := P)
  rw [hS', arqpCallKappaUnc_eq]
  rw [arqpKappaUns_eq] at hκ ⊢
  nlinarith

/-- **The decrease of a call, ARqpC-SC row** ([cartis2022evaluation], Lemma 14.2.2). Let
$X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect
to $C$, with $L_p \ge 1$, let $\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and $y \in A$,
let $A$ contain $\{y \in X : f(y) \le f(x^i_0)\}$, and let $\theta < \varsigma$. Let $i < e$ be
a successful iteration of the call. Assume that $i$ is not the last iteration ($i + 1 < e$), or
that the last point $x^i_e$ is not an $(\varepsilon, \delta^o)$-approximate $q$-th order
minimizer over $\{d : x^i_e + d \in X\}$. Then for some $l \in [1, q]$ $$f(x^i_i) - f(x^i_{i+1})
\ge \kappa_{\mathrm{decr}} \varepsilon_l^{l+1},$$ where $\kappa_{\mathrm{decr}}$ is
`Optimization.arqpCallKappaDecr`. -/
theorem decrease (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) :
    ∀ i < e, succ i → (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε l ^ (l + 1) ≤
        f (xi i) - f (xi (i + 1)) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hns : ∀ i < e, (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
      {d | xi e + d ∈ X} q ε δo) → ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (i + 1) := by
    intro i hi hcont h1
    by_cases hlt : i + 1 < e
    · exact hnot (i + 1) hlt (Or.inl h1)
    · have htest := hcont.resolve_left hlt
      have hie : i + 1 = e := by omega
      rw [hie] at h1
      rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
      · refine htest fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj]
        exact happ j hj
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
  intro i hi hs hcont
  obtain ⟨l, hl, hdec⟩ := hr.decrease_composite_zero hf hL hjet hXC hA hθς
    (fun l hl => hnot l (by omega)) ((hsucc' i hi).1 hs) (hns i hi hcont)
  refine ⟨l, hl, ?_⟩
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hdec

/-- **The decrease of a call, ARqp-SC row** ([cartis2022evaluation], Lemma 14.2.2). Assume the
hypotheses of `Optimization.IsARqpCallOut.decrease`, and let $u$ be a radii mode such that $u$
implies $q = 1$ and the convexity of $X$. Let $i < e$ be a successful iteration of the call that
is not the last one, or let the last point fail the certificate as in
`Optimization.IsARqpCallOut.decrease`. Then for some $l \in [1, q]$ $$f(x^i_i) - f(x^i_{i+1})
\ge \eta_1 \kappa_{\Delta m} \varepsilon_l^{\pi_l},$$ where $\kappa_{\Delta m}$ and $\pi_l$ are
the constant and the exponents of the radii mode $u$ (`arqpKappaDmOf u P L p q` and
`arqpPiOf u p l`). -/
theorem decrease_arqp (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) {u : Prop} [Decidable u]
    (hu : u → q = 1 ∧ Convex ℝ X) :
    ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf u P L p q * ε l ^ arqpPiOf u p l ≤
        f (xi i) - f (xi (i + 1)) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hq := hr.one_le_q
  have hε := hr.ε_mem
  have hns : ∀ i < e, (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
      {d | xi e + d ∈ X} q ε δo) → ¬ arqpStop₁ P q ε (arqpData f p x σ) δ d (i + 1) := by
    intro i hi hcont h1
    by_cases hlt : i + 1 < e
    · exact hnot (i + 1) hlt (Or.inl h1)
    · have htest := hcont.resolve_left hlt
      have hie : i + 1 = e := by omega
      rw [hie] at h1
      rcases hδo with hδo | ⟨hn, -⟩ | ⟨-, hn, -⟩
      · refine htest fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj]
        exact happ j hj
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
      · exact hn (arqpStop₁_arqpcData_zero_iff.2 h1)
  intro i hi hs hcont
  have hdec := hr.decrease_zero hf hL hjet hXC hA hθς
    (fun hu' => ⟨(hu hu').1, one_notMem_compositeHalvingSet_zero (hu hu').2⟩)
    (fun l hl => hnot l (by omega)) ((hsucc' i hi).1 hs) (hns i hi hcont)
  obtain ⟨l, hl, hmin⟩ := exists_finMin_eq hq
    (u := fun j => ε j ^ arqpPiOf u p j) (b := 1) fun j hj =>
      Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (arqpPiOf_nonneg u p j)
  refine ⟨l, hl, ?_⟩
  rw [hmin] at hdec
  rw [hxi i hi.le, hxi (i + 1) hi, mul_assoc]
  exact hdec

/-- **The returned radii of a call** (the radius policy of Algorithm 14.1.2 of
[cartis2022evaluation]). Let $X \subseteq C$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at
the points of $A$ with respect to $C$, let $\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and
$y \in A$, and let $A$ contain $\{y \in X : f(y) \le f(x^i_0)\}$. Then the returned radii
satisfy $\delta^o_j \ge \kappa_\rho \varepsilon_j$ for $j \in [1, q]$, where $\kappa_\rho$ is
`Optimization.arqpCallKappaRad`. -/
theorem radius_ge (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) :
    ∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δo j := by
  obtain ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hrun := hr.isARqpRun_zero
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hsucc' : ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i) := fun i hi => by
    rw [hsucc i hi, arqpRatio_zero]
  rw [hxi 0 (Nat.zero_le _)] at hA
  have hε := hr.ε_mem
  intro j hj
  have hκε := mul_le_mul_of_nonneg_right (arqpCallKappaRad_le_arqpKappaDelta (P := P) (L := L)
    (p := p)) (hε j hj).1.le
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q,
      arqpKappaDelta P (finMax 1 L p) (arSigmaMax P.toARParams (L p)) * ε j ≤ 1 :=
    fun j hj => by
      have h1 := arqpKappaDelta_lt_one P (one_le_finMax (L := L) (p := p))
        (arSigmaMax_pos P.toARParams (L p)).le
      have h2 := hε j hj
      have h3 := arqpKappaDelta_pos P (zero_le_one.trans (one_le_finMax (L := L) (p := p)))
        (arSigmaMax_pos P.toARParams (L p))
      nlinarith [h2.1, h2.2]
  rcases hδo with hδo | ⟨hn, hδo⟩ | ⟨-, -, hδo⟩
  · rw [hδo j hj]
    exact hκε.trans (hr.radius_ge_zero hf hjet hXC hA hδ₀ e hnot j hj)
  · rw [hδo j hj]
    exact hκε.trans (hr.arqpKappaDelta_mul_le_radius_zero hf hjet hXC hA hnot
      (arqpStop₁_arqpcData_zero_iff.not.1 hn) j hj)
  · rw [hδo j hj]
    have hxA : x e ∈ A := hA _ (hrun.mem e hnot) (hrun.mem_sublevel e hnot).2
    exact arqpCallKappaRad_mul_le_min (hε j hj) (one_le_arqpJetBound f p _)
      (arqpJetBound_le one_le_finMax fun i hi => hjet i hi _ hxA)
      (hrun.toIsARRun.sigma_pos hnot e le_rfl) (hrun.sigma_le_of_anchored hf hXC hA e hnot).2

open Classical in
/-- **The contract of one call** ([cartis2022evaluation], Lemmas 14.2.2 and 14.2.3 for ARqp-SC, and
the radius policy of Algorithm 14.1.2). Assume the hypotheses of
`Optimization.IsARqpCallOut.decrease`. Then

* the unsuccessful iterations do not move (`Optimization.IsARqpCallOut.eq_of_not_succ`);
* $e \le \kappa_{\mathrm{uns}} |\mathcal{S}| + \kappa_{\mathrm{unc}}$
  (`Optimization.IsARqpCallOut.le_count`);
* the successful iterations decrease $f$ as in `Optimization.IsARqpCallOut.decrease`;
* for every radii mode $u$ that implies $q = 1$ and the convexity of $X$, the successful
  iterations decrease $f$ as in `Optimization.IsARqpCallOut.decrease_arqp`;
* the returned radii satisfy $\delta^o_j \ge \kappa_\rho \varepsilon_j$ for $j \in [1, q]$
  (`Optimization.IsARqpCallOut.radius_ge`).

This is the form that the two-phase analysis uses. -/
theorem contract (h : IsARqpCallOut G f X p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p ∧
    (∀ i < e, succ i → (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, arqpCallKappaDecr P L p q * ε l ^ (l + 1) ≤
        f (xi i) - f (xi (i + 1))) ∧
    (∀ (u : Prop) [Decidable u], (u → q = 1 ∧ Convex ℝ X) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf u P L p q * ε l ^ arqpPiOf u p l ≤
        f (xi i) - f (xi (i + 1))) ∧
    (∀ j ∈ Finset.Icc 1 q, arqpCallKappaRad P L p * ε j ≤ δo j) :=
  ⟨h.eq_of_not_succ, h.le_count hf hXC hA, h.decrease hf hL hjet hXC hA hθς,
    fun _ _ hu => h.decrease_arqp hf hL hjet hXC hA hθς hu, h.radius_ge hf hjet hXC hA⟩

end IsARqpCallOut

variable (G) in
open Classical in
/-- **Calls stopped by an external test exist.** Let $E$ be finite-dimensional, let $X$ be closed
and $x_0 \in X$, and let $f \ge f_{\mathrm{low}}$ on $X$. Let $X \subseteq C$, let $\nabla^p f$
be $L_p$-Lipschitz anchored at the points of $A$ with respect to $C$, with $L_p \ge 1$, let
$\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$ and $y \in A$, and let $A$ contain
$\{y \in X : f(y) \le f(x_0)\}$. Let $\sigma_{\min} > 0$, $\theta < \varsigma$, $1 \le q \le p$
and $\varepsilon \in (0, 1]^q$, and let $\mathrm{stop}$ be any predicate on points. Then there
is a call $(x^i_0, \dots, x^i_e, \mathrm{succ}, \delta^o)$ in the sense of
`Optimization.IsARqpCallOut` with $x^i_0 = x_0$ that is stopped at the first iterate that
satisfies $\mathrm{stop}$ or at the termination of the run, whichever comes first. More
precisely:

* $x^i_e \in X$, and $\delta^o_j \in (0, 1]$ for $j \in [1, q]$;
* $f(x^i_{i+1}) \le f(x^i_i)$ for $i < e$, and $f(x^i_i) \le f(x_0)$ for $i \le e$;
* $\mathrm{stop}(x^i_i)$ fails for $i < e$;
* $\mathrm{stop}(x^i_e)$ holds, or $x^i_e$ is an $(\varepsilon, \delta^o)$-approximate $q$-th
  order minimizer over $\{d : x^i_e + d \in X\}$. -/
theorem exists_isARqpCallOut_of_stop [FiniteDimensional ℝ E] {flow : ℝ} (hX : IsClosed X)
    {x₀ : E} (hx₀ : x₀ ∈ X) (hb : ∀ y ∈ X, flow ≤ f y) (hf : LipschitzDerivsAnchored f C A p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (P : ARqpParams) (hσmin : 0 < P.σmin)
    (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (stop : E → Prop) :
    ∃ (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ),
      IsARqpCallOut G f X p q P ε xi e succ δo ∧ xi 0 = x₀ ∧ xi e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < δo j ∧ δo j ≤ 1) ∧
      (∀ i < e, f (xi (i + 1)) ≤ f (xi i)) ∧ (∀ i ≤ e, f (xi i) ≤ f x₀) ∧
      (∀ i < e, ¬ stop (xi i)) ∧
      (stop (xi e) ∨ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε δo) := by
  obtain ⟨x, s, σ, δ, δs, d, dm, hx0, hr⟩ := exists_isARqpCRun_compositeHalvingSet
    (f := f) (c := (0 : E → G)) (p := p) hasLipschitzConst_zero isSubadditive_zero rfl P hq hqp
    hε (δ₀ := fun _ => 1) (fun _ _ => ⟨one_pos, le_rfl⟩) hX hx₀
  have hA' : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A := by rw [hx0]; exact hA
  have hmε0 : 0 < finMin 1 (fun j => ε j ^ (j + 1)) q :=
    finMin_pos one_pos fun j hj => pow_pos (hε j hj).1 _
  obtain ⟨kε, hhit, -, -, -⟩ := hr.complexity (Lw := L p) (Kw := finMax 1 L p)
    (Kf := finMax 1 L p) (Kc := 0) hf
    (LipschitzDerivsAnchored.zero_fun hf.isOpen hf.convex hf.subset)
    hasLipschitzConst_zero isSubadditive_zero rfl hL le_rfl (by simp)
    (zero_le_one.trans one_le_finMax) le_rfl (by simp) one_le_finMax hjet
    (fun _ _ _ _ => by simp) hXC
    (fun z hz hz' => hA' z hz (by simpa using hz')) hθς hσmin (wlow := flow)
    (fun z hz => by simpa using hb z hz) hmε0 (fun j hj => finMin_le hj)
  have hrun := hr.isARqpRun_zero
  have hmono := hr.antitone_zero hhit
  have hmem : ∀ i ≤ kε, x i ∈ X := fun i hi => hr.mem fun l hl => hhit.2 l (hl.trans_le hi)
  have hex : ∃ i, i = kε ∨ stop (x i) := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δ d i :=
    fun i hi => arqpcStop_zero_iff.not.1 (hhit.2 i (by omega))
  have hstop : ∀ i < e, ¬ stop (x i) := fun i hi => (not_or.1 (Nat.find_min hex hi)).2
  have hmono' : ∀ i < e, f (x (i + 1)) ≤ f (x i) := fun i hi =>
    hmono i (i + 1) (by omega) (by omega)
  have hle : ∀ i ≤ e, f (x i) ≤ f x₀ := fun i hi => hx0 ▸ hmono 0 i (Nat.zero_le _) (by omega)
  have hsucc : ∀ i < e, ((fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i) i ↔ P.η₁ ≤ arqpRatio
        (fun y => f y + (0 : G → ℝ) ((0 : E → G) y)) (arqpcData f (0 : E → G) 0 p x σ) x s i) :=
    fun _ _ => Iff.rfl
  by_cases hcase : e < kε ∨ arqpStop₁ P q ε (arqpData f p x σ) δ d e
  · -- the current radii
    refine ⟨x, e, fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i, δ e,
      ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inl fun _ _ => rfl⟩, hx0, hmem e he_le,
      fun j hj => hrun.delta_mem hr.δ₀_mem e hnot j hj, hmono', hle, hstop, ?_⟩
    rcases hcase with hlt | h1
    · rcases Nat.find_spec hex with hek | hst
      · exact absurd hek (by omega)
      · exact Or.inl hst
    · exact Or.inr (MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hrun.witness e hnot) h1)
  · -- a Step-2 termination: the radii certified by the minimality of the model at `0`
    push Not at hcase
    obtain ⟨hke, h1⟩ := hcase
    have hek : e = kε := le_antisymm he_le hke
    have hstopk : arqpStop f P p q ε x s σ δ d e := arqpcStop_zero_iff.1 (hek ▸ hhit.1)
    have hxA : x e ∈ A := hA' _ (hrun.mem e hnot) (hrun.mem_sublevel e hnot).2
    obtain ⟨hδ, hcert⟩ := hr.isEpsDeltaApprox_of_stop₂_zero hnot h1 (hstopk.resolve_left h1)
      (hf.contDiffAt _ (hf.subset hxA))
    exact ⟨x, e, fun i => P.η₁ ≤ arqpRatio (fun y => f y + (0 : G → ℝ) ((0 : E → G) y))
      (arqpcData f (0 : E → G) 0 p x σ) x s i,
      fun j => min 1 (ε j / (4 * (3 * arqpJetBound f p (x e) + σ e))),
      ⟨x, s, σ, δ, δs, d, dm, kε, hr, hhit, he_le, fun _ _ => rfl, hsucc,
        Or.inr (Or.inr ⟨hek, arqpStop₁_arqpcData_zero_iff.not.2 h1, fun _ _ => rfl⟩)⟩, hx0,
      hmem e he_le, hδ, hmono', hle, hstop, Or.inr hcert⟩

end CallOut

/-!
### Calls of ARqp with unit radii on the whole space

For $X = E$ and $q \le 2$, the detailed Step 2 of Algorithm 12.2.3 of [cartis2022evaluation] keeps
the radii $1$ at the orders $j \le 2$ (`Optimization.exists_isARqpRun`), and an ARqp run never
terminates in Step 2 (`Optimization.IsARqpRun.arqpStop₁_of_isFirstHit_of_le_two`). So the radii $1$
certify the output of a call. The analysis is that of the unit-radius mode of ARqp, with the
exponents $\pi_j = (p+1)/(p-j+1)$.
-/

section Unit

variable {f : E → ℝ} {p q : ℕ} {P : ARqpParams} {ε : ℕ → ℝ} {A : Set E} {L : ℕ → ℝ}

/-- **ARqp runs on the whole space with unit radii terminate.** Let $E$ be finite-dimensional, let
$f \ge f_{\mathrm{low}}$ on $E$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of
$A$ with respect to $E$, with $L_p \ge 1$, let $\|\nabla^i f(y)\| \le \bar L$ for $i \in [2, p]$
and $y \in A$, and let $A$ contain $\{y : f(y) \le f(x^S)\}$. Let $\sigma_{\min} > 0$,
$\theta < \varsigma$, $1 \le q \le \min(2, p)$ and $\varepsilon \in (0, 1]^q$. Then there is an
unconstrained ARqp run with exact data and initial radii $1$ from $x_0 = x^S$ with the following
properties.

* At every iteration $k$ that is reached and does not terminate, the Step-2 radii are
  $\delta_{s_k, j} = 1$ for $j \in [1, q]$.
* The run terminates at some $k_\varepsilon$.
* $f(x_j) \le f(x_i)$ for all $i \le j \le k_\varepsilon$.
* $x_{k_\varepsilon}$ is an $(\varepsilon, 1)$-approximate $q$-th order minimizer, with all
  radii equal to $1$. -/
theorem exists_isARqpRun_unit [FiniteDimensional ℝ E] {flow : ℝ} (hb : ∀ y, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (xS : E) (hA : ∀ y, f y ≤ f xS → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
      IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
      (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) →
        ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
      IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
      x 0 = xS ∧ (∀ i j, i ≤ j → j ≤ kε → f (x j) ≤ f (x i)) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ (univ : Set E)} q ε
        (fun _ => 1) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hδ₀ : ∀ j ∈ Finset.Icc 1 q, (0 : ℝ) < (fun _ => (1 : ℝ)) j ∧ (fun _ => (1 : ℝ)) j ≤ 1 :=
    fun _ _ => ⟨one_pos, le_rfl⟩
  obtain ⟨x, s, σ, δr, δs, d, dm, h0, h, hrad⟩ := exists_isARqpRun f P hp hqp
    (fun j hj => (hε j hj).1) hδ₀ (fun y => ∑ i ∈ Finset.Icc 2 p, ‖iteratedFDeriv ℝ i f y‖)
    (fun _ => by positivity) (fun y i hi => Finset.single_le_sum
      (f := fun i => ‖iteratedFDeriv ℝ i f y‖) (fun _ _ => norm_nonneg _) hi) xS
  have hδs : ∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) →
      ∀ j ∈ Finset.Icc 1 q, δs k j = 1 := fun k hk j hj =>
    (hrad k (fun i hi => hk i hi.le)).1 j hj ((Finset.mem_Icc.1 hj).2.trans hq2)
  obtain ⟨kε, hhit, -, -, -, -⟩ := IsARqpRun.complexity (X := univ) (C := univ)
    (fun y _ => hb y) hf hL hjet (subset_univ _) (fun y _ hy => hA y (h0 ▸ hy)) hq hqp hσmin hθς
    hε hδ₀ h (u := True) ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  have h1 : arqpStop₁ P q ε (arqpData f p x σ) δr d kε :=
    h.arqpStop₁_of_isFirstHit_of_le_two (hf.contDiffAt _ (mem_univ _)) hqp hε hδ₀ hhit hq2
  have hone := h.delta_eq_one (fun _ _ => rfl) hδs kε hhit.2
  have hcert := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hhit.2) h1
  refine ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, ?_, fun j hj => ?_⟩
  · intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      exact (h.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  · have := hcert j hj
    rwa [hone j hj] at this

/-- **The output of a unit-radius call** $\mathrm{INNER}(f, E, q, x^S, \varepsilon)$ realized by
ARqp on the whole space, with its cost. A pair $(y, \delta)$ is such an output with $n_F$
evaluations of $f$ and $n_D$ evaluations of its derivatives if

* there is an unconstrained ARqp run with exact data and initial radii $1$ from $x_0 = x^S$,
  whose Step-2 radii are $1$ at the orders $j \in [1, q]$ at every iteration that is reached and
  does not terminate;
* the run terminates at some $k_\varepsilon$ with $x_{k_\varepsilon} = y$,
  $n_F = k_\varepsilon + 1$, and $n_D$ one plus the number of successful iterations before
  $k_\varepsilon$;
* $\delta_j = 1$ for $j \in [1, q]$;
* $y$ is an $(\varepsilon, \delta)$-approximate $q$-th order minimizer. -/
def IsARqpUnitOutputCost (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xS y : E)
    (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  (∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
    x 0 = xS ∧ x kε = y ∧ nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ arqpRho f p x s σ k) kε) ∧
  (∀ j ∈ Finset.Icc 1 q, δ j = 1) ∧
  IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ (univ : Set E)} q ε δ

/-- **Terminating unit-radius calls exist.** Under the hypotheses of
`Optimization.exists_isARqpRun_unit`, there is an output $y$ of a unit-radius call from $x^S$
with the radii $1$ and some costs $n_F$, $n_D$ (`Optimization.IsARqpUnitOutputCost`). -/
theorem exists_isARqpUnitOutputCost [FiniteDimensional ℝ E] {flow : ℝ} (hb : ∀ y, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (xS : E) (hA : ∀ y, f y ≤ f xS → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    ∃ (y : E) (nF nD : ℕ), IsARqpUnitOutputCost f p q P ε xS y (fun _ => 1) nF nD := by
  obtain ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, -, hcert⟩ :=
    exists_isARqpRun_unit hb hf hL hjet P hσmin hθς hq hq2 hqp xS hA hε
  exact ⟨x kε, _, _, ⟨x, s, σ, δr, δs, d, dm, kε, h, hδs, hhit, h0, rfl, rfl, rfl⟩,
    fun _ _ => rfl, hcert⟩

namespace IsARqpUnitOutputCost

variable {xS y : E} {δ : ℕ → ℝ} {nF nD : ℕ}

/-- A unit-radius call does not increase $f$: $f(y) \le f(x^S)$. -/
theorem le (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) : f y ≤ f xS := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, -, hhit, rfl, rfl, -, -⟩, -⟩ := h
  have : ∀ j ≤ kε, f (x j) ≤ f (x 0) := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      exact (hr.objective_le fun l hl => hhit.2 l (by omega)).trans (ih (by omega))
  exact this kε le_rfl

/-- The output radii of a unit-radius call are $1$ at the orders $j \in [1, q]$. -/
theorem radius_eq_one (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) :
    ∀ j ∈ Finset.Icc 1 q, δ j = 1 := h.2.1

/-- The output $y$ of a unit-radius call is an $(\varepsilon, \delta)$-approximate $q$-th order
minimizer, with the output radii $\delta$. -/
theorem isEpsDeltaApprox (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD) :
    IsEpsDeltaApprox (ftaylorSeries ℝ f y) {e | y + e ∈ (univ : Set E)} q ε δ := h.2.2

/-- **The cost of a unit-radius call** ([cartis2022evaluation], Theorem 12.2.14 in the unit-radius
mode). Let $(y, \delta)$ be the output of a unit-radius call from $x^S$ with the costs $n_F$ and
$n_D$. Let $f \ge f_{\mathrm{low}}$ on $E$, let $\nabla^p f$ be $L_p$-Lipschitz anchored at the
points of $A$ with respect to $E$, with $L_p \ge 1$, let $\|\nabla^i f(y')\| \le \bar L$ for
$i \in [2, p]$ and $y' \in A$, and let $A$ contain $\{y' : f(y') \le f(x^S)\}$. Let
$\sigma_{\min} > 0$, $\theta < \varsigma$, $1 \le q \le p$ and $\varepsilon \in (0, 1]^q$. Then,
with $m_\varepsilon = \min_{j \in [1, q]} \varepsilon_j^{\pi_j}$ and the unit-radius exponents
$\pi_j = (p+1)/(p-j+1)$, $$n_F \le \frac{\kappa^a (f(x^S) - f_{\mathrm{low}})}{m_\varepsilon} +
\kappa^c \quad\text{and}\quad n_D \le \frac{\kappa^s (f(x^S) -
f_{\mathrm{low}})}{m_\varepsilon} + 2,$$ where $\kappa^a$ and $\kappa^s$ are
`kappaAARqpOf True P L p q` and `kappaSARqpOf True P L p q`, and $\kappa^c$ is
`Optimization.kappaCARqp`. -/
theorem cost_le {flow : ℝ} (h : IsARqpUnitOutputCost f p q P ε xS y δ nF nD)
    (hb : ∀ y, flow ≤ f y) (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (hA : ∀ y, f y ≤ f xS → y ∈ A) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q)
    (hqp : q ≤ p) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) :
    (nF : ℝ) ≤ kappaAARqpOf True P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf True p j) q + kappaCARqp P L p ∧
      (nD : ℝ) ≤ kappaSARqpOf True P L p q * (f xS - flow) /
        finMin 1 (fun j => ε j ^ arqpPiOf True p j) q + 2 := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, -, rfl, rfl⟩, -, -⟩ := h
  subst hx0
  obtain ⟨kε', hhit', -, -, hF', hD'⟩ := IsARqpRun.complexity (X := univ) (C := univ)
    (fun y _ => hb y) hf hL hjet (subset_univ _) (fun y _ hy => hA y hy) hq hqp hσmin hθς hε
    (fun _ _ => ⟨one_pos, le_rfl⟩) hr (u := True)
    ⟨fun _ => ⟨fun _ _ => rfl, hδs⟩, fun h' => absurd trivial h'⟩
  obtain rfl := hhit'.unique hhit
  exact ⟨hF', hD'⟩

end IsARqpUnitOutputCost

/-- **A unit-radius call of ARqp on the whole space.** The points $x^i_0, \dots, x^i_e$ and the
predicate $\mathrm{succ}$ form such a call if there is an unconstrained ARqp run with exact data
and initial radii $1$, whose Step-2 radii are $1$ at the orders $j \in [1, q]$ at every
iteration that is reached and does not terminate, such that the run terminates at some
$k_\varepsilon \ge e$, the points $x^i_0, \dots, x^i_e$ are its first $e + 1$ iterates, and for
$i < e$, $\mathrm{succ}(i)$ holds if and only if iteration $i$ of the run is successful. -/
def IsARqpUnitCall (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xi : ℕ → E) (e : ℕ)
    (succ : ℕ → Prop) : Prop :=
  ∃ (x s : ℕ → E) (σ : ℕ → ℝ) (δr δs : ℕ → ℕ → ℝ) (d dm : ℕ → ℕ → E) (kε : ℕ),
    IsARqpRun f univ P q ε (fun _ => 1) (arqpData f p x σ) x s σ δr δs d dm ∧
    (∀ k, (∀ i ≤ k, ¬ arqpStop f P p q ε x s σ δr d i) → ∀ j ∈ Finset.Icc 1 q, δs k j = 1) ∧
    IsFirstHit (arqpStop f P p q ε x s σ δr d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    ∀ i < e, (succ i ↔ P.η₁ ≤ arqpRho f p x s σ i)

/-- **A unit-radius call with its returned radii**: a unit-radius call
(`Optimization.IsARqpUnitCall`) whose returned radii $\delta^o$ are $1$ at the orders
$j \in [1, q]$. -/
def IsARqpUnitCallOut (f : E → ℝ) (p q : ℕ) (P : ARqpParams) (ε : ℕ → ℝ) (xi : ℕ → E) (e : ℕ)
    (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  IsARqpUnitCall f p q P ε xi e succ ∧ ∀ j ∈ Finset.Icc 1 q, δo j = 1

namespace IsARqpUnitCallOut

variable {xi : ℕ → E} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- The returned radii of a unit-radius call are $1$ at the orders $j \in [1, q]$. -/
theorem radius_eq_one (h : IsARqpUnitCallOut f p q P ε xi e succ δo) :
    ∀ j ∈ Finset.Icc 1 q, δo j = 1 := h.2

/-- A unit-radius call does not increase $f$: $f(x^i_{i+1}) \le f(x^i_i)$ for all $i < e$. -/
theorem antitone (h : IsARqpUnitCallOut f p q P ε xi e succ δo) :
    ∀ i < e, f (xi (i + 1)) ≤ f (xi i) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, -, hhit, he, hxi, -⟩, -⟩ := h
  intro i hi
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hr.objective_le fun l hl => hhit.2 l (by omega)

open Classical in
/-- **The contract of one unit-radius call** ([cartis2022evaluation], Lemmas 12.2.13 and 14.2.3 with
unit radii). Let $\nabla^p f$ be $L_p$-Lipschitz anchored at the points of $A$ with respect to
$E$, with $L_p \ge 1$, let $A$ contain the sublevel set $\{y : f(y) \le f(x^i_0)\}$ of the start
of the call, and let $\theta < \varsigma$ and $1 \le q \le p$. Then

* the unsuccessful iterations do not move: $x^i_{i+1} = x^i_i$ if $i < e$ and $\mathrm{succ}(i)$
  fails;
* $e \le \kappa_{\mathrm{uns}} |\mathcal{S}| + \kappa_{\mathrm{unc}}$, where
  $\mathcal{S} = \{i < e : \mathrm{succ}(i)\}$;
* if $\varepsilon \in (0, 1]^q$, then every successful iteration $i < e$ that is not the last
  one, or that is the last one of a call whose last point $x^i_e$ is not an
  $(\varepsilon, \delta^o)$-approximate $q$-th order minimizer, satisfies $f(x^i_i) -
  f(x^i_{i+1}) \ge \eta_1 \kappa_{\Delta m} \varepsilon_l^{\pi_l}$ for some $l \in [1, q]$.

Here $\kappa_{\Delta m}$ is `arqpKappaDmOf True P L p q` and $\pi_l = (p+1)/(p-l+1)$ are the
unit-radius constant and exponents, and $\kappa_{\mathrm{unc}}$ is
`Optimization.arqpCallKappaUnc`. -/
theorem contract (h : IsARqpUnitCallOut f p q P ε xi e succ δo)
    (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hA : ∀ y, f y ≤ f (xi 0) → y ∈ A) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ arqpKappaUns P * ((Finset.range e).filter succ).card + arqpCallKappaUnc P L p ∧
    ((∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) → ∀ i < e, succ i →
      (i + 1 < e ∨ ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e))
        {d | xi e + d ∈ (univ : Set E)} q ε δo) →
      ∃ l ∈ Finset.Icc 1 q, P.η₁ * arqpKappaDmOf True P L p q * ε l ^ arqpPiOf True p l ≤
        f (xi i) - f (xi (i + 1))) := by
  obtain ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he, hxi, hsucc⟩, hδo⟩ := h
  have hAμ : ∀ y ∈ (univ : Set E), f y ≤ f (x 0) → y ∈ A := fun y _ hy =>
    hA y (by rwa [hxi 0 (Nat.zero_le _)])
  have hone := hr.delta_eq_one (fun _ _ => rfl) hδs
  have hnot : ∀ i < e, ¬ arqpStop f P p q ε x s σ δr d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  refine ⟨fun i hi hs => ?_, ?_, fun hε i hi hs hcont => ?_⟩
  · rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.toIsARRun.eq_of_not_succ (fun l hl => hnot l (lt_of_le_of_lt hl hi))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · have h3 := hr.toIsARRun.le_succ_count (k := e) hnot
      (hr.sigma_le_of_anchored hf (subset_univ _) hAμ e hnot).2
    set ρ := fun i => P.η₁ ≤ arqpRho f p x s σ i
    have hS' : (Finset.range e).filter succ = (Finset.range e).filter ρ :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard' := card_successSet_le_card_filter_add_one ρ e
    have hκ := arqpKappaUns_nonneg (P := P)
    rw [hS', arqpCallKappaUnc_eq]
    rw [arqpKappaUns_eq] at hκ ⊢
    nlinarith
  · have h1 : ¬ arqpStop₁ P q ε (arqpData f p x σ) δr d (i + 1) := by
      intro h1
      by_cases hlt : i + 1 < e
      · exact hnot (i + 1) hlt (Or.inl h1)
      · have hie : i + 1 = e := by omega
        rw [hie] at h1
        refine (hcont.resolve_left hlt) fun j hj => ?_
        have happ := MeasureTestPasses.isEpsDeltaApprox P.ς_pos (hr.witness e hnot) h1
        rw [hxi e le_rfl, hδo j hj, ← hone e hnot j hj]
        exact happ j hj
    have hdec := (IsARqpRun.decrease hf hL (subset_univ _) hAμ hq hqp hθς hε hr
      (k := i) (fun l hl => hnot l (by omega)) ((hsucc i hi).1 hs) h1 (u := True)
      ⟨fun _ => hone (i + 1) (fun l hl => hnot l (by omega)), fun h' => absurd trivial h'⟩).2
    obtain ⟨l, hl, hmin⟩ := exists_finMin_eq hq
      (u := fun j => ε j ^ arqpPiOf True p j) (b := 1) fun j hj =>
        Real.rpow_le_one (hε j hj).1.le (hε j hj).2 (arqpPiOf_nonneg True p j)
    refine ⟨l, hl, ?_⟩
    rw [hmin] at hdec
    rw [hxi i hi.le, hxi (i + 1) hi, mul_assoc]
    exact hdec

end IsARqpUnitCallOut

open Classical in
/-- **Unit-radius calls stopped by an external test exist.** Under the hypotheses of
`Optimization.exists_isARqpRun_unit` with $x_0$ in place of $x^S$, and for any predicate
$\mathrm{stop}$ on points, there is a unit-radius call $(x^i_0, \dots, x^i_e, \mathrm{succ})$
with returned radii $1$ and $x^i_0 = x_0$ that is stopped at the first iterate that satisfies
$\mathrm{stop}$ or at the termination of the run. More precisely:

* $f(x^i_{i+1}) \le f(x^i_i)$ for $i < e$, and $f(x^i_i) \le f(x_0)$ for $i \le e$;
* $\mathrm{stop}(x^i_i)$ fails for $i < e$;
* $\mathrm{stop}(x^i_e)$ holds, or $x^i_e$ is an $(\varepsilon, 1)$-approximate $q$-th order
  minimizer. -/
theorem exists_isARqpUnitCallOut_of_stop [FiniteDimensional ℝ E] {flow : ℝ}
    (hb : ∀ y, flow ≤ f y) (hf : LipschitzDerivsAnchored f univ A p p L) (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ A, ‖iteratedFDeriv ℝ i f y‖ ≤ finMax 1 L p)
    (P : ARqpParams) (hσmin : 0 < P.σmin) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqp : q ≤ p) (x₀ : E) (hA : ∀ y, f y ≤ f x₀ → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (stop : E → Prop) :
    ∃ (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop),
      IsARqpUnitCallOut f p q P ε xi e succ (fun _ => 1) ∧ xi 0 = x₀ ∧
      (∀ i < e, f (xi (i + 1)) ≤ f (xi i)) ∧ (∀ i ≤ e, f (xi i) ≤ f x₀) ∧
      (∀ i < e, ¬ stop (xi i)) ∧
      (stop (xi e) ∨ IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ (univ : Set E)}
        q ε (fun _ => 1)) := by
  obtain ⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, hx0, hmono, hcert⟩ :=
    exists_isARqpRun_unit hb hf hL hjet P hσmin hθς hq hq2 hqp x₀ hA hε
  have hex : ∃ i, i = kε ∨ stop (x i) := ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  refine ⟨x, e, fun i => P.η₁ ≤ arqpRho f p x s σ i,
    ⟨⟨x, s, σ, δr, δs, d, dm, kε, hr, hδs, hhit, he_le, fun _ _ => rfl, fun _ _ => Iff.rfl⟩,
      fun _ _ => rfl⟩, hx0, fun i hi => hmono i (i + 1) (by omega) (by omega),
    fun i hi => hx0 ▸ hmono 0 i (Nat.zero_le _) (by omega),
    fun i hi => (not_or.1 (Nat.find_min hex hi)).2, ?_⟩
  rcases Nat.find_spec hex with hek | hst
  · right
    rw [show e = kε from hek]
    exact hcert
  · exact Or.inl hst

end Unit

end Optimization
