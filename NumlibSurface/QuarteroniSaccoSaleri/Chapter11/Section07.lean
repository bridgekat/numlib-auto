/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.FixedPoint
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section06

/-!
# Quarteroni, Sacco and Saleri, Section 11.7: Predictor–Corrector Methods

This module formalizes Section 11.7 of [quarteroni2000numerical]. The step of an implicit linear
multistep method solves $u_{n+1} = G + h b_{-1} f(t_{n+1}, u_{n+1})$, where $G$ collects the known
terms. The fixed-point iteration (11.67) for this equation converges if $h |b_{-1}| L < 1$, where
$L$ is the Lipschitz constant of $f$ in $y$ (11.68). A predictor–corrector scheme replaces the
iteration by a fixed number $m$ of corrections: an explicit predictor computes $u^{(0)}_{n+1}$, and
$m$ times an evaluation of $f$ and a correction by the implicit corrector follow. This is the scheme
$P(EC)^m$ of (11.69), and $P(EC)^mE$ adds a final evaluation. Heun's method and the pair of the
two-step Adams–Bashforth and Adams–Moulton methods are examples (Example 11.8). If the predictor has
order $\tilde q$ and the corrector order $q$, the scheme $P(EC)^mE$ has order
$\min(q, \tilde q + m)$ (Property 11.3). Example 11.10 gives the characteristic polynomials of the
Adams–Bashforth–Moulton pairs.

The proofs specialize the backbone module `Numlib.ODE.Multistep` at $E = \mathbb{R}$, through
`ODE.PredictorCorrector`, with Mathlib's contraction mapping theorem for (11.68).

## Main definitions

* Equation (11.69), `QuarteroniSaccoSaleri.Chapter11.equation_11_69`: the sequences computed by the
  scheme $P(EC)^m$.
* Section 11.7, `QuarteroniSaccoSaleri.Chapter11.equation_11_69_pece`: the sequences computed by the
  scheme $P(EC)^mE$.
* Example 11.8, `QuarteroniSaccoSaleri.Chapter11.example_11_8_abm_pair`: the pair of the two-step
  Adams–Bashforth and Adams–Moulton methods with one correction.
* Property 11.3, `QuarteroniSaccoSaleri.Chapter11.pecOrder`: the scheme $P(EC)^mE$ has order $q$
  along a curve.

## Main results

* Equation (11.68), `QuarteroniSaccoSaleri.Chapter11.equation_11_68`: if $h |b_{-1}| L < 1$, the
  implicit step has a unique solution, and the fixed-point iteration (11.67) converges to it.
* Equation (11.69), `QuarteroniSaccoSaleri.Chapter11.equation_11_69_iff`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_69_pece_iff`: the two schemes in explicit form.
* Example 11.8, `QuarteroniSaccoSaleri.Chapter11.example_11_8`: Heun's method is the scheme $P(EC)E$
  with forward Euler as predictor and Crank–Nicolson as corrector.
* Example 11.8, `QuarteroniSaccoSaleri.Chapter11.example_11_8_abm`: the Adams–Bashforth–Moulton pair
  and its $PEC$ recursion.
* Property 11.3, `QuarteroniSaccoSaleri.Chapter11.property_11_3`: the scheme $P(EC)^mE$ has order
  $\min(q, \tilde q + m)$.
* Example 11.10, `QuarteroniSaccoSaleri.Chapter11.example_11_10`: the characteristic polynomials of
  the Adams–Bashforth–Moulton pairs.

## Conventions

* A pair `PC : ODE.PredictorCorrector` stores the explicit predictor $(\tilde a, \tilde b)$, the
  corrector $(a, b, b_{-1})$ and the number $m$ of corrections. The corrector is padded by zeros to
  the $p + 1$ steps of the predictor. The two methods are `ODE.PredictorCorrector.toPredictor` and
  `ODE.PredictorCorrector.toCorrector`.
* The scheme $P(EC)^m$ computes two sequences, $u = u^{(m)}$ and the stored function values
  $f^{(m-1)}$, which the Lean code calls `fv`. The scheme $P(EC)^mE$ computes only $u$, and its
  function values are evaluated at the corrected values.

## Deviations from the source

* **Equations (11.67)–(11.69) and Example 11.8** (reading). `equation_11_68` uses the product
  condition $h|b_{-1}|L<1$, so zero Lipschitz constant or zero step is allowed. The orbit
  relations pad both histories to a common length and also accept $m=0$. Initial field
  evaluations for the PEC orbit, including the ABM example, are left to the caller.
* **Property 11.3 and Example 11.10** (partial). `property_11_3` gives the guaranteed order of
  the PECE variant along the exact curve. It does not specify a principal error term or show
  equality with the PEC variant. `example_11_10` gives the characteristic polynomials for $p\geq
  2$ and leaves the numerical stability region comparison out.

## Not formalized

* **Example 11.9.** It is a numerical experiment.
* **The characteristic polynomials $\Pi_{P(EC)^m}$ and $\Pi_{P(EC)^mE}$ of the schemes.**
* **Milne's device.**
* **Property 11.3 for the scheme $P(EC)^m$**, whose truncation error is not defined in the backbone,
  and **the clauses of Property 11.3 on the principal local truncation error**.
-/

open Set Filter Topology Asymptotics ODE Polynomial
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### (11.67)–(11.68): the fixed-point iteration for the implicit step -/

/-- **Equation (11.68)** of [quarteroni2000numerical], the convergence condition of the fixed-point
iteration (11.67). Let $M$ be a linear multistep method, let $L \ge 0$, $t \in \mathbb{R}$ and
$h \ge 0$, and let $|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all
$y_1, y_2 \in \mathbb{R}$. Let $G \in \mathbb{R}$, and put $\Psi(v) = G + h b_{-1} f(t, v)$. If
$$h |b_{-1}| L < 1,$$
then the equation $v = \Psi(v)$ has a unique solution $v$, and for every starting value $v_0$
the iterates $\Psi^k(v_0)$ converge to $v$ as $k \to \infty$.

In the book, $t = t_{n+1}$, $G = \sum_{j=0}^{p} a_j u_{n-j} + h \sum_{j=0}^{p} b_j f_{n-j}$, the
iteration (11.67) is $u_{n+1}^{(k+1)} = \Psi(u_{n+1}^{(k)})$, and the condition is written
$h < 1/(|b_{-1}| L)$. The map $\Psi$ is a contraction, and the proof uses Mathlib's
`ContractingWith.fixedPoint` and `ContractingWith.tendsto_iterate_fixedPoint`, the contraction
mapping theorem (Theorem 6.1 of the book).

**Reading.** Uses the contraction condition $h|b_{-1}|L<1$, including the case $|b_{-1}|L=0$.
The limit is the unique fixed point from any start. -/
theorem equation_11_68 (M : LinearMultistep) {L : ℝ} (hL : 0 ≤ L) (t : ℝ)
    (hf : ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) (hh : 0 ≤ h)
    (hcond : h * |M.bm1| * L < 1) (G : ℝ) :
    ∃ v : ℝ, v = G + h * M.bm1 * f t v ∧ (∀ w : ℝ, w = G + h * M.bm1 * f t w → w = v) ∧
      ∀ v₀ : ℝ, Tendsto (fun k => (fun w => G + h * M.bm1 * f t w)^[k] v₀) atTop (𝓝 v) := by
  set Ψ : ℝ → ℝ := fun w => G + h * M.bm1 * f t w with hΨ
  set K : NNReal := ⟨h * |M.bm1| * L, by positivity⟩ with hKdef
  have hK1 : (K : ℝ) = h * |M.bm1| * L := rfl
  have hK : ContractingWith K Ψ := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_⟩
    · rw [← NNReal.coe_lt_coe, hK1, NNReal.coe_one]
      exact hcond
    · simp only [hΨ, Real.dist_eq, hK1]
      rw [show G + h * M.bm1 * f t y₁ - (G + h * M.bm1 * f t y₂) =
        h * M.bm1 * (f t y₁ - f t y₂) by ring, abs_mul, abs_mul, abs_of_nonneg hh, mul_assoc,
        mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf y₁ y₂) (abs_nonneg _)) hh
  refine ⟨ContractingWith.fixedPoint Ψ hK, hK.fixedPoint_isFixedPt.symm,
    fun w hw => ?_, fun v₀ => hK.tendsto_iterate_fixedPoint v₀⟩
  exact hK.fixedPoint_unique hw.symm

/-! ### (11.69): the `P(EC)^m` and `P(EC)^mE` schemes -/

/-- **Equation (11.69)** of [quarteroni2000numerical], the scheme $P(EC)^m$. Let `PC` be a
predictor–corrector pair with $p + 1$ steps and $m$ corrections, $f : \mathbb{R} \times
\mathbb{R} \to \mathbb{R}$ and $h, t_0 \in \mathbb{R}$. Two sequences $u = u^{(m)}$ and
$f^{(m-1)}$ **are computed by the scheme $P(EC)^m$** if at every step $n \ge p$:

* [P] $u^{(0)}_{n+1} = \sum_{j=0}^{p} \tilde a_j u^{(m)}_{n-j} + h \sum_{j=0}^{p} \tilde b_j
  f^{(m-1)}_{n-j}$;
* for $k = 0, \dots, m - 1$: [E] $f^{(k)}_{n+1} = f(t_{n+1}, u^{(k)}_{n+1})$, and [C]
  $u^{(k+1)}_{n+1} = \sum_{j=0}^{p} a_j u^{(m)}_{n-j} + h \sum_{j=0}^{p} b_j f^{(m-1)}_{n-j} + h
  b_{-1} f^{(k)}_{n+1}$.

The scheme $PEC$ is the case $m = 1$. The definition is `ODE.PredictorCorrector.IsOrbitPEC`, and
the sequence $f^{(m-1)}$ is the argument `fv`.

**Generalization.** Pads histories to a common index set and uses a natural correction count
that can be zero. The recurrence leaves the starting values free. -/
def equation_11_69 (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u fv : ℕ → ℝ) : Prop :=
  PC.IsOrbitPEC f h t₀ u fv

/-- **Section 11.7** of [quarteroni2000numerical], the scheme $P(EC)^mE$. A sequence $u = u^{(m)}$
is computed by the scheme $P(EC)^mE$ if it follows the steps of $P(EC)^m$, followed by the final
evaluation $f^{(m)}_{n+1} = f(t_{n+1}, u^{(m)}_{n+1})$. So the stored function values are those
of the corrected values.

The definition is `ODE.PredictorCorrector.IsOrbitPECE`.

**Generalization.** Pads histories to a common index set and uses a natural correction count
that can be zero. The recurrence leaves the starting values free. -/
def equation_11_69_pece (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  PC.IsOrbitPECE f h t₀ u

/-- **Equation (11.69)** of [quarteroni2000numerical], in explicit form. For $n \ge p$ put
$$\Psi_n(v) = \sum_{j=0}^{p} a_j u_{n-j} + h \sum_{j=0}^{p} b_j f^{(m-1)}_{n-j} + h b_{-1}
  f(t_{n+1}, v), \qquad u^{(0)}_{n+1} = \sum_{j=0}^{p} \tilde a_j u_{n-j} + h \sum_{j=0}^{p}
  \tilde b_j f^{(m-1)}_{n-j}.$$
Then $u$ and $f^{(m-1)}$ are computed by the scheme $P(EC)^m$ if and only if for every $n \ge p$
$$u_{n+1} = \Psi_n^m\bigl(u^{(0)}_{n+1}\bigr), \qquad f^{(m-1)}_{n+1} = f\bigl(t_{n+1},
  \Psi_n^{m-1}(u^{(0)}_{n+1})\bigr).$$

For $m = 0$, the exponent $m - 1$ is $0$, by truncated subtraction.

**Generalization.** Pads histories to a common index set and uses a natural correction count
that can be zero. The recurrence leaves the starting values free. -/
theorem equation_11_69_iff (PC : PredictorCorrector) (u fv : ℕ → ℝ) :
    equation_11_69 PC f h t₀ u fv ↔ ∀ n, PC.p ≤ n →
      u (n + 1) = (fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * fv (n - j)) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * fv (n - j)) ∧
      fv (n + 1) = f (grid t₀ h (n + 1)) ((fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * fv (n - j)) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m - 1]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * fv (n - j))) := by
  unfold equation_11_69 PredictorCorrector.IsOrbitPEC PredictorCorrector.pecStep
    PredictorCorrector.correct PredictorCorrector.historySum PredictorCorrector.predict
  simp only [smul_eq_mul, Prod.mk.injEq, ← node_succ, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + PC.p) (Nat.le_add_left _ _)

/-- **Section 11.7** of [quarteroni2000numerical], the scheme $P(EC)^mE$ in explicit form. A
sequence $u$ is computed by the scheme $P(EC)^mE$ if and only if for every $n \ge p$
$$u_{n+1} = \Psi_n^m\bigl(u^{(0)}_{n+1}\bigr),$$
where $\Psi_n$ and $u^{(0)}_{n+1}$ are as in
`QuarteroniSaccoSaleri.Chapter11.equation_11_69_iff`, with the stored function values
$f(t_{n-j}, u_{n-j})$ in place of $f^{(m-1)}_{n-j}$.

**Generalization.** Pads histories to a common index set and uses a natural correction count
that can be zero. The recurrence leaves the starting values free. -/
theorem equation_11_69_pece_iff (PC : PredictorCorrector) (u : ℕ → ℝ) :
    equation_11_69_pece PC f h t₀ u ↔ ∀ n, PC.p ≤ n →
      u (n + 1) = (fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * f (grid t₀ h (n - j)) (u (n - j))) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * f (grid t₀ h (n - j)) (u (n - j))) := by
  have e : ∀ (m : ℕ) (j : Fin (PC.p + 1)),
      node t₀ h (m + PC.p) - j * h = node t₀ h (m + PC.p - j) :=
    fun m j => LinearMultistep.node_sub_mul (by have := j.is_lt; omega)
  unfold equation_11_69_pece PredictorCorrector.IsOrbitPECE PredictorCorrector.peceStep
    PredictorCorrector.correct PredictorCorrector.historySum PredictorCorrector.predict
  simp only [smul_eq_mul, ← node_succ, grid, e]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + PC.p) (Nat.le_add_left _ _)

/-- **Example 11.8** of [quarteroni2000numerical], Heun's method. A sequence $u$ is computed by
Heun's method (11.10) if and only if it is computed by the scheme $P(EC)E$ with forward Euler as
predictor, Crank–Nicolson as corrector and one correction.

With $P(EC)$ instead, the stored function values would be those of the predicted values, and the
scheme would not be Heun's method. Forward Euler is `ODE.LinearMultistep.ofOneStep 1 1 0`, and
Crank–Nicolson is `ODE.LinearMultistep.ofOneStep 1 (1 / 2) (1 / 2)`. The proof specializes
`ODE.PredictorCorrector.heun_eq_pece`. -/
theorem example_11_8 (u : ℕ → ℝ) :
    equation_11_69_pece (PredictorCorrector.ofPair (LinearMultistep.ofOneStep 1 1 0)
      (LinearMultistep.ofOneStep 1 (1 / 2) (1 / 2)) le_rfl 1) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_10 f)) h t₀ u :=
  PredictorCorrector.heun_eq_pece

/-- **Example 11.8** of [quarteroni2000numerical], the second pair: the two-step Adams–Bashforth
method (11.50) as predictor, the two-step Adams–Moulton method (11.51) of order $3$ as
corrector, and one correction. The predictor has $\tilde a = (1, 0)$ and
$\tilde b = (3/2, -1/2)$; the corrector has $a = (1, 0)$, $b = (8/12, -1/12)$ and
$b_{-1} = 5/12$. -/
noncomputable def example_11_8_abm_pair : PredictorCorrector :=
  ⟨1, ![1, 0], ![3 / 2, -1 / 2], ![1, 0], ![8 / 12, -1 / 12], 5 / 12, 1⟩

/-- **Example 11.8** of [quarteroni2000numerical], the Adams–Bashforth–Moulton pair. The predictor
of the pair is `ODE.LinearMultistep.adamsBashforth 1`, and its corrector is
`ODE.LinearMultistep.adamsMoulton 2`. Two sequences $u = u^{(1)}$ and $f^{(0)}$ are computed by
its scheme $PEC$ if and only if for every $n \ge 1$
$$\begin{aligned} u^{(0)}_{n+1} &= u_n + \tfrac{h}{2} \bigl(3 f^{(0)}_n - f^{(0)}_{n-1}\bigr),
  \\ f^{(0)}_{n+1} &= f\bigl(t_{n+1}, u^{(0)}_{n+1}\bigr), \\ u_{n+1} &= u_n + \tfrac{h}{12}
  \bigl(5 f^{(0)}_{n+1} + 8 f^{(0)}_n - f^{(0)}_{n-1}\bigr). \end{aligned}$$

In the Lean statement the predicted value $u^{(0)}_{n+1}$ is substituted into the other two
equations.

**Reading.** The recurrence leaves the initial stored field values arbitrary. The printed
algorithm initializes them with evaluations of $f$ at the starting nodes and states. -/
theorem example_11_8_abm (u fv : ℕ → ℝ) :
    example_11_8_abm_pair.toPredictor = LinearMultistep.adamsBashforth 1 ∧
    example_11_8_abm_pair.toCorrector = LinearMultistep.adamsMoulton 2 ∧
    (equation_11_69 example_11_8_abm_pair f h t₀ u fv ↔ ∀ n, 1 ≤ n →
      u (n + 1) = u n + h / 12 *
        (5 * f (grid t₀ h (n + 1)) (u n + h / 2 * (3 * fv n - fv (n - 1))) +
          8 * fv n - fv (n - 1)) ∧
      fv (n + 1) = f (grid t₀ h (n + 1)) (u n + h / 2 * (3 * fv n - fv (n - 1)))) := by
  refine ⟨LinearMultistep.adamsBashforth_one_eq.symm,
    LinearMultistep.adamsMoulton_two_eq.symm, ?_⟩
  rw [equation_11_69_iff]
  change (∀ n, 1 ≤ n → u (n + 1) = (fun v => (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v)^[1]
      (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
        h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j)) ∧
    fv (n + 1) = f (grid t₀ h (n + 1)) ((fun v => (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v)^[1 - 1]
      (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
        h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j)))) ↔ _
  have e1 : ∀ n, ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j) =
      u n + h / 2 * (3 * fv n - fv (n - 1)) := fun n => by
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have e2 : ∀ n v, (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v =
      u n + h / 12 * (5 * f (grid t₀ h (n + 1)) v + 8 * fv n - fv (n - 1)) := fun n v => by
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  simp only [e1, e2, Function.iterate_one, Nat.sub_self, Function.iterate_zero, id]

/-! ### Property 11.3: the order of a predictor–corrector pair -/

/-- **Property 11.3** of [quarteroni2000numerical], the order of the scheme $P(EC)^mE$. Let `PC` be
a predictor–corrector pair, $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$,
$t_0, T \in \mathbb{R}$, $y : \mathbb{R} \to \mathbb{R}$ and $q \in \mathbb{N}$. The scheme
$P(EC)^mE$ **has order $q$** along $y$ on $[t_0, t_0 + T]$ if its global truncation error is
$O(h^q)$ as $h \to 0^+$. The global truncation error is the maximum over the steps
$p \le n < N_h$ of $|y_{n+1} - \Phi_h(y_n, \dots, y_{n-p})|/h$, where $\Phi_h$ is one step of
the scheme applied to the exact values.

The definition is `ODE.PredictorCorrector.HasOrderFor`.

**Partial.** The order predicate and theorem concern the PECE method along the supplied curve.
The theorem gives the guaranteed order, without the principal-error comparison between
correction counts or between PEC and PECE.

**Reading.** Defines order of the PECE variant by global LTE, on a supplied solution.
-/
def pecOrder (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (q : ℕ) : Prop :=
  PC.HasOrderFor f t₀ T y q

/-- **Property 11.3** of [quarteroni2000numerical] (the order of a predictor–corrector pair). Let
$|f(t, y_1) - f(t, y_2)| \le L |y_1 - y_2|$ for all $t \in [t_0, t_0 + T]$ and
$y_1, y_2 \in \mathbb{R}$, and let $y'(t) = f(t, y(t))$ for every $t \in [t_0, t_0 + T]$. Let
the predictor have order $\tilde q$ and the corrector order $q$ along $y$ on $[t_0, t_0 + T]$.
Then the scheme $P(EC)^mE$ has order $\min(q, \tilde q + m)$ along $y$. In particular:

* if $\tilde q \ge q$, the scheme has the order $q$ of the corrector;
* if $\tilde q < q$ and $m \ge q - \tilde q$, the scheme has order $q$;
* if $\tilde q < q$ and $m \le q - \tilde q$, the scheme has order $\tilde q + m$.

The book states the property for the scheme $P(EC)^m$ and adds that $P(EC)^mE$ has the same
order. The scheme $P(EC)^m$, whose truncation error is not defined in the backbone, and the
clauses on the principal local truncation error (the same as that of the corrector if
$m > q - \tilde q$, a different one if $m = q - \tilde q$) are not formalized. The book quotes
the property without proof. The proof specializes `ODE.PredictorCorrector.hasOrderFor_of`.

**Partial.** The order predicate and theorem concern the PECE method along the supplied curve.
The theorem gives the guaranteed order, without the principal-error comparison between
correction counts or between PEC and PECE.

**Reading.** Lower bound on PECE order under Lipschitz and exact-curve assumptions; no sharp PLTE or
comparison with PEC.
-/
theorem property_11_3 (PC : PredictorCorrector) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {qp q : ℕ}
    (hP : definition_11_9_order PC.toPredictor t₀ T y qp)
    (hC : definition_11_9_order PC.toCorrector t₀ T y q) :
    pecOrder PC f t₀ T y (min q (qp + PC.m)) ∧
      (q ≤ qp → pecOrder PC f t₀ T y q) ∧
      (qp < q → q - qp ≤ PC.m → pecOrder PC f t₀ T y q) ∧
      (qp < q → PC.m ≤ q - qp → pecOrder PC f t₀ T y (qp + PC.m)) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have key : pecOrder PC f t₀ T y (min q (qp + PC.m)) := PC.hasOrderFor_of hf' hy hP hC
  refine ⟨key, fun hq => ?_, fun _ hm => ?_, fun _ hm => ?_⟩
  · rwa [min_eq_left (by omega)] at key
  · rwa [min_eq_left (by omega)] at key
  · rwa [min_eq_right (by omega)] at key

/-! ### Example 11.10: the ABM characteristic polynomials -/

/-- **Example 11.10** of [quarteroni2000numerical]. Let $p \ge 2$ and $m \in \mathbb{N}$, and
consider the Adams–Bashforth–Moulton pair with $p$ steps: the $p$-step Adams–Bashforth method as
predictor, the $(p-1)$-step Adams–Moulton method as corrector, padded to $p$ steps, and $m$
corrections. Then the padded corrector and the predictor have the same first characteristic
polynomial,
$$\hat\rho(r) = \tilde\rho(r) = r\,(r^{p-1} - r^{p-2}),$$
and the second characteristic polynomial of the padded corrector is
$\hat\sigma(r) = r\,\sigma(r)$, where $\sigma$ is that of the Adams–Moulton corrector.

The pair is `ODE.PredictorCorrector.abm p m`. The proof specializes
`ODE.PredictorCorrector.abm_charPoly`.

**Partial.** States the polynomial identities for $p\geq 2$ and arbitrary correction count. The
printed example also compares computed stability regions.

**Reading.** Same padded polynomials for p≥2 and arbitrary m, without stability-region plots or size
comparison.
-/
theorem example_11_10 (p m : ℕ) (hp : 2 ≤ p) :
    (characteristicPolynomials (PredictorCorrector.abm p m).toCorrector).1 =
        X * (X ^ (p - 1) - X ^ (p - 2)) ∧
      (characteristicPolynomials (PredictorCorrector.abm p m).toPredictor).1 =
        X * (X ^ (p - 1) - X ^ (p - 2)) ∧
      (characteristicPolynomials (PredictorCorrector.abm p m).toCorrector).2 =
        X * (characteristicPolynomials (LinearMultistep.adamsMoulton (p - 1))).2 := by
  obtain ⟨h1, h2, h3⟩ := PredictorCorrector.abm_charPoly p m hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have e : X ^ (k + 2) - X ^ (k + 2 - 1) = (X : ℝ[X]) * (X ^ (k + 2 - 1) - X ^ (k + 2 - 2)) := by
    rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl]
    ring
  exact ⟨by rw [characteristicPolynomials, h1, e], by rw [characteristicPolynomials, h2, e], h3⟩

end QuarteroniSaccoSaleri.Chapter11
