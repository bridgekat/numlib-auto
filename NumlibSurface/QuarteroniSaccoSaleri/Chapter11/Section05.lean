/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.ODE.Multistep
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section04

/-!
# Quarteroni, Sacco and Saleri, Section 11.5: Multistep Methods

This module formalizes Section 11.5 of [quarteroni2000numerical]. A $q$-step method computes
$u_{n+1}$ from $u_n, \dots, u_{n+1-q}$ (Definition 11.7); the midpoint method (11.43) and the
Simpson method (11.44) are two-step methods. A linear multistep method with $p + 1$ steps is
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h \sum_{j=0}^{p} b_j f_{n-j} + h b_{-1} f_{n+1}, \qquad n
  \ge p,$$
which is (11.45), with $f_k = f(t_k, u_k)$. It is implicit if $b_{-1} \neq 0$, and it is a linear
difference equation (11.28) of order $p + 1$ (11.46). Along a curve $y$ the local truncation error
is $\tau_{n+1}(h) = L[y; h](t_n)/h$ (Definition 11.8, (11.47)), with the linear operator
$$L[w; h](t) = w(t + h) - \sum_{j=0}^{p} a_j w(t - jh) - h \sum_{j=-1}^{p} b_j w'(t - jh)$$
of (11.48). Consistency and order (Definition 11.9) are defined by the global truncation error
$\tau(h)$ as for one-step methods. A method of order $q$ has the principal local truncation error
$C_{q+1} h^{q+1} y^{(q+1)}$, with the error constant $C_{q+1}$.

The second half treats two families. The Adams methods (11.49) have $a_0 = 1$ and
$a_1 = \dots = a_p = 0$; their weights are the integrals of the Lagrange basis of the nodes. The
module gives the Adams–Bashforth methods (11.50) and the Adams–Moulton methods (11.51), their
orders, and their error constants (Table 11.1). The backward differentiation formulae of Table 11.2
(Section 11.5.2) have $b_0 = \dots = b_p = 0$, and the BDF method with $p + 1$ steps has order
$p + 1$. The proofs specialize the backbone module `Numlib.ODE.Multistep` at $E = \mathbb{R}$.

## Main definitions

* Definition 11.7, `QuarteroniSaccoSaleri.Chapter11.definition_11_7`: a linear multistep method is a
  $q$-step method.
* Equation (11.43), `QuarteroniSaccoSaleri.Chapter11.equation_11_43`: the midpoint method.
* Equation (11.44), `QuarteroniSaccoSaleri.Chapter11.equation_11_44`: the Simpson method.
* Equation (11.45), `QuarteroniSaccoSaleri.Chapter11.equation_11_45`: $u$ is a sequence computed by
  the linear multistep method.
* Equation (11.46), `QuarteroniSaccoSaleri.Chapter11.equation_11_46_beta`: the coefficients
  $\beta_s$ of the difference-equation form.
* Definition 11.8, `QuarteroniSaccoSaleri.Chapter11.definition_11_8`: the local truncation error
  $\tau_{n+1}(h)$ (11.47).
* Definition 11.8, `QuarteroniSaccoSaleri.Chapter11.definition_11_8_global`: the global truncation
  error $\tau(h)$.
* Definition 11.9, `QuarteroniSaccoSaleri.Chapter11.definition_11_9`,
  `QuarteroniSaccoSaleri.Chapter11.definition_11_9_method`: consistency along a curve, and
  consistency of the method.
* Definition 11.9, `QuarteroniSaccoSaleri.Chapter11.definition_11_9_order`,
  `QuarteroniSaccoSaleri.Chapter11.definition_11_9_order_method`: order $q$ along a curve, and order
  $q$ of the method.
* Equation (11.48), `QuarteroniSaccoSaleri.Chapter11.equation_11_48`: the linear operator $L$.
* Section 11.5, `QuarteroniSaccoSaleri.Chapter11.errorConstant`: the error constant $C_{q+1}$.
* Equation (11.49), `QuarteroniSaccoSaleri.Chapter11.equation_11_49`: the method is an Adams method.
* Table 11.2, `QuarteroniSaccoSaleri.Chapter11.bdf`: the backward differentiation formulae.

## Main results

* Definition 11.7, `QuarteroniSaccoSaleri.Chapter11.definition_11_7_ofOneStep`: the one-step methods
  are the case $q = 1$.
* Equations (11.43) and (11.44), `QuarteroniSaccoSaleri.Chapter11.equation_11_43_twoStep`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_44_twoStep`: the midpoint method is an explicit
  two-step method, and the Simpson method is an implicit two-step method.
* Equation (11.45), `QuarteroniSaccoSaleri.Chapter11.equation_11_45_implicit_iff`: the method is
  implicit if and only if $b_{-1} \neq 0$.
* Equation (11.46), `QuarteroniSaccoSaleri.Chapter11.equation_11_46`: the method (11.45) is the
  difference equation (11.28) with the coefficients $\alpha_s = -a_{p-s}$.
* Equation (11.48), `QuarteroniSaccoSaleri.Chapter11.equation_11_48_lte`:
  $\tau_{n+1}(h) = L[y; h](t_n)/h$.
* Section 11.5, `QuarteroniSaccoSaleri.Chapter11.equation_11_48_principal`: for a method of order
  $q$, $L[y; h](t) = C_{q+1} h^{q+1} y^{(q+1)}(t) + O(h^{q+2})$.
* Equation (11.49), `QuarteroniSaccoSaleri.Chapter11.equation_11_49_adamsBashforth`,
  `QuarteroniSaccoSaleri.Chapter11.equation_11_49_adamsMoulton`: the Adams–Bashforth and
  Adams–Moulton methods are Adams methods with interpolatory weights.
* Equation (11.50), `QuarteroniSaccoSaleri.Chapter11.equation_11_50`: the Adams–Bashforth methods
  with one to four steps.
* Section 11.5.1, `QuarteroniSaccoSaleri.Chapter11.adamsBashforth_order`: the $q$-step
  Adams–Bashforth method has order $q$.
* Equation (11.51), `QuarteroniSaccoSaleri.Chapter11.equation_11_51`: the Adams–Moulton methods with
  one to four steps.
* Section 11.5.1, `QuarteroniSaccoSaleri.Chapter11.adamsMoulton_order`: the $q$-step Adams–Moulton
  method has order $q + 1$.
* Table 11.1, `QuarteroniSaccoSaleri.Chapter11.adamsErrorConstants`: the error constants of the
  Adams methods of orders $1$ to $4$.
* Table 11.2, `QuarteroniSaccoSaleri.Chapter11.bdf_table`: the coefficients of the BDF methods.
* Section 11.5.2, `QuarteroniSaccoSaleri.Chapter11.bdf_order`: the BDF method with $p + 1$ steps has
  order $p + 1$.

## Conventions

* A linear multistep method is `M : ODE.LinearMultistep`. The field `M.p` is $p$, and the fields
  `M.a`, `M.b` and `M.bm1` hold the coefficients $a_0, \dots, a_p$, $b_0, \dots, b_p$ and $b_{-1}$.
  The method has $p + 1$ steps.
* The $q$-step Adams–Moulton method, with the index $p = q - 1$ of the book, is
  `ODE.LinearMultistep.adamsMoulton q`. The $(p+1)$-step Adams–Bashforth method is
  `ODE.LinearMultistep.adamsBashforth p`.
* Sequences are indexed by $\mathbb{N}$. The recursion (11.45) is imposed for every $n \ge p$, and
  the starting values $u_0, \dots, u_p$ are free.
* The node $t_n$ is `QuarteroniSaccoSaleri.Chapter11.grid t₀ h n`, and the derivative $y'$ is
  `deriv y`.

## Deviations from the source

* **Definition 11.7 and equations (11.43)–(11.46)** (reading). The definition of a $q$-step
  method uses the oldest coefficients of a linear multistep record. Orbit formulas apply to any
  such record and leave initial values free. `equation_11_46` uses the sum of all weighted field
  terms as the forcing at $n+p+1$. The source's description after (11.46) writes one term at a
  time.
* **Definitions 11.8 and 11.9** (reading). The truncation error uses the total derivative and a
  finite global supremum that allows grids with no admissible steps. Consistency and order use
  positive-step limits. The method properties quantify over all sufficiently smooth curves on
  positive finite horizons, and the order predicate allows $q=0$.
* **Equation (11.48) and the principal error term** (correction). The residual $\mathcal L$ is
  $h$ times the local truncation error, as in (11.47). The prose after (11.48) calls it the
  local error itself. The principal expansion in `equation_11_48_principal` is for the residual,
  about $t$ with explicit $C^{q+2}$ regularity and a derivative bound, while the printed
  expansion uses $t-ph$ and attributes the remainder to the normalized error.
* **Section 11.5.1, Adams–Moulton indexing** (reading). Lean indexes
  `LinearMultistep.adamsMoulton` by the interpolating degree. The backward Euler row has index
  $0$, Crank–Nicolson has index $1$, and degree $p$ gives order $p+1$. The source refers to a
  history index taking $-1$ for backward Euler and $0$ for Crank–Nicolson, then labels the
  higher rows by interpolating degree.
* **Table 11.2** (reading). `bdf_order` adds the order $p+1$ for each of the six tabulated BDF
  methods.
* **Table 11.1** (reading). The index $q$ is read as the order in both columns. The caption "having
  order $q + 1$" for the Adams–Moulton column would place $-1/2$ at Crank–Nicolson, whose error
  constant is $-1/12$. See `QuarteroniSaccoSaleri.Chapter11.adamsErrorConstants`.
* **Table 11.2** (typo). The book prints $b_{-1} = 60/137$ in the row $p = 5$; the coefficient is
  $60/147$. See `QuarteroniSaccoSaleri.Chapter11.bdf`.
-/

open Set Filter Topology Asymptotics ODE
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Definition 11.7 and the two classical two-step methods -/

/-- **Definition 11.7** of [quarteroni2000numerical] ($q$-step methods). A numerical method for the
Cauchy problem is a **$q$-step method**, $q \ge 1$, if for $n \ge q - 1$ the value $u_{n+1}$
depends on $u_{n+1-q}$ but not on the values $u_k$ with $k < n + 1 - q$. For a linear multistep
method with $p + 1$ steps this means $p + 1 = q$ together with
$$a_p \neq 0 \quad \text{or} \quad b_p \neq 0.$$

The definition is stated for linear multistep methods. The condition $a_p \neq 0$ or
$b_p \neq 0$ is `ODE.LinearMultistep.IsGenuine`.

**Reading.** Tests the oldest coefficients of a linear formula. The source defines history
dependence for arbitrary methods, and a particular field may make a term with nonzero field
coefficient constant in the old state. -/
def definition_11_7 (M : LinearMultistep) (q : ℕ) : Prop :=
  M.p + 1 = q ∧ M.IsGenuine

/-- **Definition 11.7** of [quarteroni2000numerical]. A linear multistep method is a $q$-step method
if and only if $p + 1 = q$ and ($a_p \neq 0$ or $b_p \neq 0$).

**Reading.** Tests the oldest coefficients of a linear formula. The source defines history
dependence for arbitrary methods, and a particular field may make a term with nonzero field
coefficient constant in the old state. -/
theorem definition_11_7_iff (M : LinearMultistep) (q : ℕ) :
    definition_11_7 M q ↔
      M.p + 1 = q ∧ (M.a (Fin.last M.p) ≠ 0 ∨ M.b (Fin.last M.p) ≠ 0) :=
  Iff.rfl

/-- **Definition 11.7** of [quarteroni2000numerical], the case $q = 1$. For
$a_0, b_0, b_{-1} \in \mathbb{R}$, the method
$$u_{n+1} = a_0 u_n + h (b_0 f_n + b_{-1} f_{n+1})$$
is a one-step method if and only if $a_0 \neq 0$ or $b_0 \neq 0$.

The method is `ODE.LinearMultistep.ofOneStep a₀ b₀ bm1`. The one-step methods of Section 11.2
are of this form.

**Reading.** Tests the oldest coefficients of a linear formula. The source defines history
dependence for arbitrary methods, and a particular field may make a term with nonzero field
coefficient constant in the old state. -/
theorem definition_11_7_ofOneStep (a₀ b₀ bm1 : ℝ) :
    definition_11_7 (LinearMultistep.ofOneStep a₀ b₀ bm1) 1 ↔ a₀ ≠ 0 ∨ b₀ ≠ 0 := by
  simp [definition_11_7, LinearMultistep.IsGenuine, LinearMultistep.ofOneStep]

/-- **Equation (11.43)** of [quarteroni2000numerical], the **midpoint method**:
$$u_{n+1} = u_{n-1} + 2h f_n, \qquad n \ge 1.$$

The method is `ODE.LinearMultistep.midpoint`. -/
noncomputable def equation_11_43 : LinearMultistep := LinearMultistep.midpoint

/-- **Equation (11.43)** of [quarteroni2000numerical]. A sequence $u$ is computed by the midpoint
method if and only if $u_{n+2} = u_n + 2h f(t_{n+1}, u_{n+1})$ for every $n$.

**Generalization.** The recurrence permits any real step and places no constraint on the
starting values. The orbit definition does not require the oldest coefficients to be nonzero. -/
theorem equation_11_43_isOrbit_iff (u : ℕ → ℝ) :
    equation_11_43.IsOrbit f h t₀ u ↔
      ∀ n, u (n + 2) = u n + 2 * h * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_43, LinearMultistep.isOrbit_midpoint_iff]
  simp only [smul_eq_mul, grid]

/-- **Equation (11.43)** of [quarteroni2000numerical]. The midpoint method is a two-step method
(Definition 11.7), and it is explicit. -/
theorem equation_11_43_twoStep :
    definition_11_7 equation_11_43 2 ∧ ¬ equation_11_43.IsImplicit := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ?_⟩
  · change (![(0 : ℝ), 1] : Fin 2 → ℝ) 1 ≠ 0
    simp
  · change ¬ (0 : ℝ) ≠ 0
    simp

/-- **Equation (11.44)** of [quarteroni2000numerical], the **Simpson method**:
$$u_{n+1} = u_{n-1} + \frac{h}{3} (f_{n-1} + 4f_n + f_{n+1}), \qquad n \ge 1.$$

The method is `ODE.LinearMultistep.simpson`. -/
noncomputable def equation_11_44 : LinearMultistep := LinearMultistep.simpson

/-- **Equation (11.44)** of [quarteroni2000numerical]. A sequence $u$ is computed by the Simpson
method if and only if for every $n$
$$u_{n+2} = u_n + \frac{h}{3} \bigl(f(t_n, u_n) + 4 f(t_{n+1}, u_{n+1}) + f(t_{n+2},
  u_{n+2})\bigr).$$

**Generalization.** The recurrence permits any real step and places no constraint on the
starting values. The orbit definition does not require the oldest coefficients to be nonzero. -/
theorem equation_11_44_isOrbit_iff (u : ℕ → ℝ) :
    equation_11_44.IsOrbit f h t₀ u ↔ ∀ n, u (n + 2) = u n + h / 3 *
      (f (grid t₀ h n) (u n) + 4 * f (grid t₀ h (n + 1)) (u (n + 1)) +
        f (grid t₀ h (n + 2)) (u (n + 2))) := by
  rw [equation_11_44, LinearMultistep.isOrbit_simpson_iff]
  simp only [smul_eq_mul, grid]

/-- **Equation (11.44)** of [quarteroni2000numerical]. The Simpson method is a two-step method
(Definition 11.7), and it is implicit. -/
theorem equation_11_44_twoStep : definition_11_7 equation_11_44 2 ∧ equation_11_44.IsImplicit := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ?_⟩
  · change (![(0 : ℝ), 1] : Fin 2 → ℝ) 1 ≠ 0
    simp
  · change (1 / 3 : ℝ) ≠ 0
    norm_num

/-! ### (11.45)–(11.46): the linear multistep method and its difference-equation form -/

/-- **Equation (11.45)** of [quarteroni2000numerical], the linear multistep method. Let $M$ be a
linear multistep method with $p + 1$ steps, let $f : \mathbb{R} \times \mathbb{R} \to
\mathbb{R}$ and $h, t_0 \in \mathbb{R}$. A sequence $u$ **is computed by the method** if
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h \sum_{j=0}^{p} b_j f_{n-j} + h b_{-1} f_{n+1}, \qquad
  n \ge p,$$
where $f_k = f(t_k, u_k)$.

The sequence is an orbit `ODE.LinearMultistep.IsOrbit` of $M$ for the field $f$, the step $h$
and the initial time $t_0$. The starting values $u_0, \dots, u_p$ are free.

**Generalization.** The recurrence permits any real step and places no constraint on the
starting values. The orbit definition does not require the oldest coefficients to be nonzero. -/
def equation_11_45 (M : LinearMultistep) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  M.IsOrbit f h t₀ u

/-- **Equation (11.45)** of [quarteroni2000numerical]. A sequence $u$ is computed by the method $M$
if and only if for every $n \ge p$
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h \sum_{j=0}^{p} b_j f(t_{n-j}, u_{n-j}) + h b_{-1}
  f(t_{n+1}, u_{n+1}).$$

**Generalization.** The recurrence permits any real step and places no constraint on the
starting values. The orbit definition does not require the oldest coefficients to be nonzero. -/
theorem equation_11_45_iff (M : LinearMultistep) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔ ∀ n, M.p ≤ n → u (n + 1) =
      ∑ j : Fin (M.p + 1), M.a j * u (n - j) +
        h * ∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (u (n - j)) +
        h * M.bm1 * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_45, LinearMultistep.isOrbit_iff]
  simp only [smul_eq_mul, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + M.p) (Nat.le_add_left _ _)

/-- **Section 11.5** of [quarteroni2000numerical]. A linear multistep method is **implicit** if and
only if $b_{-1} \neq 0$.

Implicitness is `ODE.LinearMultistep.IsImplicit`. -/
theorem equation_11_45_implicit_iff (M : LinearMultistep) : M.IsImplicit ↔ M.bm1 ≠ 0 :=
  Iff.rfl

/-- **Equation (11.46)** of [quarteroni2000numerical], the coefficients $\beta_s$. For a linear
multistep method with $p + 1$ steps,
$$\beta_s = b_{p-s}, \quad s = 0, \dots, p, \qquad \beta_{p+1} = b_{-1}.$$
-/
noncomputable def equation_11_46_beta (M : LinearMultistep) : Fin (M.p + 1 + 1) → ℝ :=
  Fin.snoc (fun s : Fin (M.p + 1) => M.b (Fin.rev s)) M.bm1

/-- **Equation (11.46)** of [quarteroni2000numerical]. Let $M$ be a linear multistep method with
$p + 1$ steps. Put $\alpha_{p+1} = 1$, $\alpha_s = -a_{p-s}$ and $\beta_s = b_{p-s}$ for
$s = 0, \dots, p$, and $\beta_{p+1} = b_{-1}$. Then a sequence $u$ is computed by the method
(11.45) if and only if it solves the difference equation of order $k = p + 1$
$$\sum_{s=0}^{p+1} \alpha_s u_{n+s} = h \sum_{s=0}^{p+1} \beta_s f(t_{n+s}, u_{n+s}), \qquad n
  \ge 0.$$

The statement uses the form (11.28) of Section 11.4, with the coefficients
$\alpha_0, \dots, \alpha_p$ and the right-hand side $\varphi_{n+p+1} = h \sum_s \beta_s
f(t_{n+s}, u_{n+s})$. The values of $\varphi$ below the index $p + 1$ are never read.

**Reading.** Uses the entire sum on the right of (11.46) as the forcing at index $n+p+1$. It
applies to the full orbit. -/
theorem equation_11_46 (M : LinearMultistep) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔
      (equation_11_28 fun s : Fin (M.p + 1) => -M.a (Fin.rev s)).IsSolutionWith
        (fun n => h * ∑ s : Fin (M.p + 1 + 1), equation_11_46_beta M s *
          f (grid t₀ h (n - (M.p + 1) + s)) (u (n - (M.p + 1) + s))) u := by
  rw [equation_11_45, LinearMultistep.isOrbit_iff, equation_11_28_iff]
  refine forall_congr' fun n => ?_
  rw [Fin.sum_univ_castSucc (n := M.p + 1)]
  simp only [neg_mul, Finset.sum_neg_distrib, Nat.add_sub_cancel, equation_11_46_beta,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, smul_eq_mul, grid]
  rw [show ∑ i : Fin (M.p + 1), M.a (Fin.rev i) * u (n + i) =
      ∑ j : Fin (M.p + 1), M.a j * u (n + M.p - j) from M.sum_rev_smul M.a u n,
    show ∑ s : Fin (M.p + 1), M.b (Fin.rev s) * f (node t₀ h (n + s)) (u (n + s)) =
      ∑ j : Fin (M.p + 1), M.b j * f (node t₀ h (n + M.p - j)) (u (n + M.p - j)) from
      M.sum_rev_smul M.b (fun m => f (node t₀ h m) (u m)) n, ← add_assoc]
  constructor <;> intro H <;> linear_combination H

/-- **Equation (11.46)** of [quarteroni2000numerical]. The difference equation (11.28) with the
coefficients $\alpha_s = -a_{p-s}$ is the real recurrence
`ODE.LinearMultistep.toLinearRecurrenceZero` of the method, whose characteristic polynomial is
the first characteristic polynomial $\rho$ (`ODE.LinearMultistep.rho`). -/
theorem equation_11_46_eq (M : LinearMultistep) :
    (equation_11_28 fun s : Fin (M.p + 1) => -M.a (Fin.rev s)) = M.toLinearRecurrenceZero := by
  simp [equation_11_28, LinearMultistep.toLinearRecurrenceZero]

/-! ### Definitions 11.8–11.9: the truncation error, consistency and order -/

/-- **Definition 11.8** of [quarteroni2000numerical], the local truncation error (11.47). Let $M$ be
a linear multistep method with $p + 1$ steps, $h, t_0 \in \mathbb{R}$ and
$y : \mathbb{R} \to \mathbb{R}$. The **local truncation error** at the node $t_{n+1}$,
$n \ge p$, is the number $\tau_{n+1}(h)$ with
$$h \tau_{n+1}(h) = y_{n+1} - \Bigl[\sum_{j=0}^{p} a_j y_{n-j} + h \sum_{j=-1}^{p} b_j
  y'_{n-j}\Bigr],$$
where $y_k = y(t_k)$ and $y'_k = y'(t_k)$.

The definition is `ODE.LinearMultistep.lte` at the node $t_n$, which is $L[y; h](t_n)/h$. For
$h = 0$ its value is $0$, by the convention $0^{-1} = 0$.

**Generalization.** The truncation error uses the total derivative of the supplied function.
The specification of its product with $h$ assumes a nonzero step and a valid history index. -/
noncomputable def definition_11_8 (M : LinearMultistep) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    ℝ :=
  M.lte h y (grid t₀ h n)

/-- **Equation (11.47)** of [quarteroni2000numerical]. Let $h \neq 0$ and $n \ge p$. For every
function $y$,
$$h \tau_{n+1}(h) = y_{n+1} - \Bigl[\sum_{j=0}^{p} a_j y_{n-j} + h \Bigl(b_{-1} y'_{n+1} +
  \sum_{j=0}^{p} b_j y'_{n-j}\Bigr)\Bigr],$$
with $y' = $ `deriv y`.

**Generalization.** The truncation error uses the total derivative of the supplied function.
The specification of its product with $h$ assumes a nonzero step and a valid history index. -/
theorem definition_11_8_spec (M : LinearMultistep) (hh : h ≠ 0) (y : ℝ → ℝ) (hn : M.p ≤ n) :
    h * definition_11_8 M h y t₀ n = y (grid t₀ h (n + 1)) -
      (∑ j : Fin (M.p + 1), M.a j * y (grid t₀ h (n - j)) +
        h * (M.bm1 * deriv y (grid t₀ h (n + 1)) +
          ∑ j : Fin (M.p + 1), M.b j * deriv y (grid t₀ h (n - j)))) := by
  have e : ∀ j : Fin (M.p + 1), node t₀ h n - j * h = node t₀ h (n - j) := fun j =>
    LinearMultistep.node_sub_mul (by have := j.is_lt; omega)
  rw [definition_11_8, LinearMultistep.lte, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh, one_mul,
    LinearMultistep.opL]
  simp only [grid, smul_eq_mul, e, node_succ, sub_sub]

/-- **Definition 11.8** of [quarteroni2000numerical], the global truncation error. Let $M$ be a
linear multistep method with $p + 1$ steps, $t_0, T \in \mathbb{R}$,
$y : \mathbb{R} \to \mathbb{R}$ and $h \in \mathbb{R}$. The **global truncation error** is
$$\tau(h) = \max_{p \le n \le N_h - 1} |\tau_{n+1}(h)|.$$

The definition is `ODE.LinearMultistep.globalLte`. If the method takes no step on
$[t_0, t_0 + T]$, that is $N_h \le p$, then $\tau(h) = 0$.

**Generalization.** Extends the supremum to grids without admissible steps by inserting zero at
disabled indices. -/
noncomputable def definition_11_8_global (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    ℝ :=
  M.globalLte t₀ T y h

/-- **Definition 11.8** of [quarteroni2000numerical]. The global truncation error $\tau(h)$ is the
supremum over $0 \le n < N_h$ of $|\tau_{n+1}(h)|$ for $n \ge p$ and of $0$ for $n < p$.

**Generalization.** Extends the supremum to grids without admissible steps by inserting zero at
disabled indices. -/
theorem definition_11_8_global_eq (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (h : ℝ) :
    definition_11_8_global M t₀ T y h =
      ⨆ n : Fin (gridCount T h), if M.p ≤ (n : ℕ) then |definition_11_8 M h y t₀ n| else 0 :=
  rfl

/-- **Definition 11.9** of [quarteroni2000numerical], consistency along a curve. A linear multistep
method is **consistent** along $y$ on $[t_0, t_0 + T]$ if $\tau(h) \to 0$ as $h \to 0^+$.

The definition is `ODE.LinearMultistep.IsConsistentFor`.

**Reading.** Uses the limit through positive steps for the supplied curve. The order property
allows order zero. -/
def definition_11_9 (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) : Prop :=
  M.IsConsistentFor t₀ T y

/-- **Definition 11.9** of [quarteroni2000numerical]. A linear multistep method is consistent along
$y$ on $[t_0, t_0 + T]$ if and only if $\tau(h) \to 0$ as $h \to 0^+$.

**Reading.** Uses the limit through positive steps for the supplied curve. The order property
allows order zero. -/
theorem definition_11_9_iff (M : LinearMultistep) :
    definition_11_9 M t₀ T y ↔ Tendsto (definition_11_8_global M t₀ T y) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- **Definition 11.9** of [quarteroni2000numerical], consistency of the method. A linear multistep
method is **consistent** if it is consistent along every $y \in C^1(\mathbb{R})$ on every
interval $[t_0, t_0 + T]$ with $T > 0$.

Every $C^1$ curve $y$ solves a Cauchy problem, for the field $f(t, v) = y'(t)$, so this is
consistency for every scalar problem with a $C^1$ solution. The definition is
`ODE.LinearMultistep.IsConsistent`.

**Reading.** Quantifies over smooth curves on all positive horizons so that the property
describes the method. The order property allows order zero. -/
def definition_11_9_method (M : LinearMultistep) : Prop :=
  M.IsConsistent

/-- **Definition 11.9** of [quarteroni2000numerical]. A linear multistep method is consistent if and
only if for all $t_0 \in \mathbb{R}$, all $T > 0$ and all $y \in C^1(\mathbb{R})$ it is
consistent along $y$ on $[t_0, t_0 + T]$.

**Reading.** Quantifies over smooth curves on all positive horizons so that the property
describes the method. The order property allows order zero. -/
theorem definition_11_9_method_iff (M : LinearMultistep) :
    definition_11_9_method M ↔
      ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ 1 y → definition_11_9 M t₀ T y :=
  Iff.rfl

/-- **Definition 11.9** of [quarteroni2000numerical], order along a curve. A linear multistep method
**has order $q$** along $y$ on $[t_0, t_0 + T]$ if $\tau(h) = O(h^q)$ as $h \to 0^+$.

The definition is `ODE.LinearMultistep.HasOrderFor`.

**Reading.** Uses the limit through positive steps for the supplied curve. The order property
allows order zero. -/
def definition_11_9_order (M : LinearMultistep) (t₀ T : ℝ) (y : ℝ → ℝ) (q : ℕ) : Prop :=
  M.HasOrderFor t₀ T y q

/-- **Definition 11.9** of [quarteroni2000numerical]. A linear multistep method has order $q$ along
$y$ on $[t_0, t_0 + T]$ if and only if $\tau(h) = O(h^q)$ as $h \to 0^+$.

**Reading.** Uses the limit through positive steps for the supplied curve. The order property
allows order zero. -/
theorem definition_11_9_order_iff (M : LinearMultistep) {q : ℕ} :
    definition_11_9_order M t₀ T y q ↔
      definition_11_8_global M t₀ T y =O[𝓝[>] 0] fun h => h ^ q :=
  Iff.rfl

/-- **Definition 11.9** of [quarteroni2000numerical], order of the method. A linear multistep method
**has order $q$** if it has order $q$ along every $y \in C^{q+1}(\mathbb{R})$ on every interval
$[t_0, t_0 + T]$ with $T > 0$.

The definition is `ODE.LinearMultistep.HasOrder`.

**Reading.** Quantifies over smooth curves on all positive horizons so that the property
describes the method. The order property allows order zero. -/
def definition_11_9_order_method (M : LinearMultistep) (q : ℕ) : Prop :=
  M.HasOrder q

/-- **Definition 11.9** of [quarteroni2000numerical]. A linear multistep method has order $q$ if and
only if for all $t_0 \in \mathbb{R}$, all $T > 0$ and all $y \in C^{q+1}(\mathbb{R})$ it has
order $q$ along $y$ on $[t_0, t_0 + T]$.

**Reading.** Quantifies over smooth curves on all positive horizons so that the property
describes the method. The order property allows order zero. -/
theorem definition_11_9_order_method_iff (M : LinearMultistep) (q : ℕ) :
    definition_11_9_order_method M q ↔
      ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ (q + 1) y → definition_11_9_order M t₀ T y q :=
  Iff.rfl

/-- **Definition 11.9** of [quarteroni2000numerical]. A linear multistep method of order $q \ge 1$
is consistent. -/
theorem definition_11_9_of_order (M : LinearMultistep) {q : ℕ} (hq : 1 ≤ q)
    (H : definition_11_9_order_method M q) : definition_11_9_method M :=
  LinearMultistep.HasOrder.isConsistent M hq H

/-! ### (11.48): the operator `L`, the principal truncation error and the error constant -/

/-- **Equation (11.48)** of [quarteroni2000numerical]. For a linear multistep method with $p + 1$
steps, $h \in \mathbb{R}$ and $w : \mathbb{R} \to \mathbb{R}$, the **linear operator** $L$
associated with the method is
$$L[w; h](t) = w(t + h) - \sum_{j=0}^{p} a_j w(t - jh) - h \sum_{j=-1}^{p} b_j w'(t - jh).$$

The operator is `ODE.LinearMultistep.opL`. The derivative is `deriv w`, which is $0$ where $w$
is not differentiable.

**Reading.** The operator uses the total derivative for any supplied curve. Its linearity
theorem assumes differentiability. -/
noncomputable def equation_11_48 (M : LinearMultistep) (h : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  M.opL h w t

/-- **Equation (11.48)** of [quarteroni2000numerical]. For every $w : \mathbb{R} \to \mathbb{R}$ and
$t \in \mathbb{R}$,
$$L[w; h](t) = w(t + h) - \sum_{j=0}^{p} a_j w(t - jh) - h \Bigl(b_{-1} w'(t + h) +
  \sum_{j=0}^{p} b_j w'(t - jh)\Bigr),$$
with $w' = $ `deriv w`.

**Reading.** The operator uses the total derivative for any supplied curve. Its linearity
theorem assumes differentiability. -/
theorem equation_11_48_eq (M : LinearMultistep) (h : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    equation_11_48 M h w t = w (t + h) - ∑ j : Fin (M.p + 1), M.a j * w (t - j * h) -
      h * (M.bm1 * deriv w (t + h) + ∑ j : Fin (M.p + 1), M.b j * deriv w (t - j * h)) :=
  rfl

/-- **Equation (11.48)** of [quarteroni2000numerical]. The local truncation error is
$\tau_{n+1}(h) = L[y; h](t_n)/h$.

**Correction.** By (11.47) the local error is the residual $\mathcal L$ divided by $h$. The
description immediately after (11.48) omits this division. -/
theorem equation_11_48_lte (M : LinearMultistep) (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    definition_11_8 M h y t₀ n = equation_11_48 M h y (grid t₀ h n) / h := by
  rw [definition_11_8, LinearMultistep.lte, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- **Equation (11.48)** of [quarteroni2000numerical], linearity of $L$. Let
$w, v : \mathbb{R} \to \mathbb{R}$ be differentiable and $c \in \mathbb{R}$. Then
$L[w + v; h](t) = L[w; h](t) + L[v; h](t)$ and $L[cw; h](t) = c \, L[w; h](t)$.

**Reading.** The operator uses the total derivative for any supplied curve. Its linearity
theorem assumes differentiability. -/
theorem equation_11_48_linear (M : LinearMultistep) (h : ℝ) (w v : ℝ → ℝ) (t c : ℝ)
    (hw : Differentiable ℝ w) (hv : Differentiable ℝ v) :
    equation_11_48 M h (w + v) t = equation_11_48 M h w t + equation_11_48 M h v t ∧
      equation_11_48 M h (c • w) t = c * equation_11_48 M h w t :=
  ⟨M.opL_add h w v t (fun s => hw s) (fun s => hv s), M.opL_smul h c w t (fun s => hw s)⟩

/-- **Section 11.5** of [quarteroni2000numerical], the error constant. For a linear multistep method
with $p + 1$ steps and $q \in \mathbb{N}$, the **error constant** is
$$C_{q+1} = \frac{1}{(q + 1)!} \Bigl(1 - \sum_{j=0}^{p} (-j)^{q+1} a_j - (q + 1) \sum_{j=-1}^{p}
  (-j)^q b_j\Bigr).$$
For a method of order $q$, it is the coefficient of $h^{q+1} y^{(q+1)}(t_n)$ in the principal
local truncation error.

The definition is `ODE.LinearMultistep.errorConstant`.

**Reading.** The principal coefficient multiplies $h^{q+1}y^{(q+1)}$ for the residual $h\tau$,
expressed about $t$. The text expands about $t-ph$ and writes the residual's leading power for
$\tau$. -/
noncomputable def errorConstant (M : LinearMultistep) (q : ℕ) : ℝ :=
  M.errorConstant q

/-- **Section 11.5** of [quarteroni2000numerical]. The error constant is
$$C_{q+1} = \frac{1}{(q + 1)!} \Bigl(1 - \sum_{j=0}^{p} (-j)^{q+1} a_j - (q + 1) \Bigl(b_{-1} +
  \sum_{j=0}^{p} (-j)^q b_j\Bigr)\Bigr).$$

**Reading.** The principal coefficient multiplies $h^{q+1}y^{(q+1)}$ for the residual $h\tau$,
expressed about $t$. The text expands about $t-ph$ and writes the residual's leading power for
$\tau$. -/
theorem errorConstant_eq (M : LinearMultistep) (q : ℕ) :
    errorConstant M q =
      (1 - ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (q + 1) * M.a j -
        (q + 1 : ℕ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ q * M.b j)) /
        (q + 1).factorial := by
  rw [errorConstant, LinearMultistep.errorConstant, LinearMultistep.taylorCoeff,
    Nat.add_sub_cancel]

/-- **Section 11.5** of [quarteroni2000numerical], the principal local truncation error. Let a
linear multistep method with $p + 1$ steps have order $q$, and let $y \in C^{q+2}(\mathbb{R})$.
Let $a, b, K \in \mathbb{R}$ with $|y^{(q+2)}(s)| \le K$ for all $s \in [a, b]$, let $h > 0$,
and let $t - ph$ and $t + h$ lie in $[a, b]$. Then
$$\bigl|L[y; h](t) - C_{q+1} h^{q+1} y^{(q+1)}(t)\bigr| \le K R h^{q+2},$$
where $R$ is a constant of the method. So $L[y; h](t) = C_{q+1} h^{q+1} y^{(q+1)}(t) +
O(h^{q+2})$.

The constant is $R = $ `ODE.LinearMultistep.remainderConst M (q + 1)`. The coefficients
$C_0, \dots, C_q$ of the Taylor expansion of $L$ vanish by Theorem 11.3
(`ODE.LinearMultistep.hasOrder_iff`), and `ODE.LinearMultistep.opL_eq_sum_add_remainder` bounds
the remainder.

**Reading.** The principal coefficient multiplies $h^{q+1}y^{(q+1)}$ for the residual $h\tau$,
expressed about $t$. The text expands about $t-ph$ and writes the residual's leading power for
$\tau$. -/
theorem equation_11_48_principal (M : LinearMultistep) {q : ℕ}
    (hq : definition_11_9_order_method M q) (hy : ContDiff ℝ (q + 2) y) {a b K : ℝ}
    (hK : ∀ s ∈ Icc a b, |iteratedDeriv (q + 2) y s| ≤ K) (hh : 0 < h)
    (ht : t - M.p * h ∈ Icc a b) (hth : t + h ∈ Icc a b) :
    |equation_11_48 M h y t - errorConstant M q * h ^ (q + 1) * iteratedDeriv (q + 1) y t| ≤
      K * M.remainderConst (q + 1) * h ^ (q + 2) := by
  have hder : ∀ m ≤ q + 1, ∀ s, HasDerivAt (iteratedDeriv m y) (iteratedDeriv (m + 1) y s) s := by
    intro m hm s
    have hdiff : Differentiable ℝ (iteratedDeriv m y) :=
      hy.differentiable_iteratedDeriv m (by exact_mod_cast Nat.lt_succ_of_le hm)
    rw [iteratedDeriv_succ]
    exact (hdiff s).hasDerivAt
  have hexp := M.opL_eq_sum_add_remainder (q := q + 1) (y := fun m => iteratedDeriv m y)
    (fun m hm s _ => (hder m hm s).hasDerivWithinAt)
    (fun s _ => (hder 0 (Nat.zero_le _) s).deriv) hK hh ht hth
  have hzero : ∀ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) •
      iteratedDeriv m y t = 0 := fun m hm => by
    rw [Finset.mem_range] at hm
    rw [(M.orderCondition_iff_taylorCoeff_eq_zero m).1
      (M.hasOrder_iff.1 hq m (Nat.lt_succ_iff.1 hm)), mul_zero, zero_smul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero hzero, zero_add, iteratedDeriv_zero,
    Real.norm_eq_abs] at hexp
  rw [equation_11_48, errorConstant, LinearMultistep.errorConstant]
  convert hexp using 3
  rw [smul_eq_mul]
  ring

/-! ### (11.49)–(11.51): the Adams methods -/

/-- **Equation (11.49)** of [quarteroni2000numerical], the Adams methods. A linear multistep method
with $p + 1$ steps is an **Adams method** if $a_0 = 1$ and $a_1 = \dots = a_p = 0$, so that it
reads
$$u_{n+1} = u_n + h \sum_{j=-1}^{p} b_j f_{n-j}.$$

The definition constrains only the coefficients $a_j$. In the book the weights $b_j$ come from
the integration over $[t_n, t_{n+1}]$ of the polynomial that interpolates $f$ at the nodes
$t_{n+1}, t_n, \dots, t_{n-p}$ (the implicit Adams–Moulton methods) or $t_n, \dots, t_{n-p}$
(the explicit Adams–Bashforth methods, $b_{-1} = 0$). These weights are stated in
`QuarteroniSaccoSaleri.Chapter11.equation_11_49_adamsBashforth` and
`QuarteroniSaccoSaleri.Chapter11.equation_11_49_adamsMoulton`. -/
def equation_11_49 (M : LinearMultistep) : Prop :=
  M.a = Pi.single 0 1

/-- **Equation (11.49)** of [quarteroni2000numerical]. Let $M$ be an Adams method with $p + 1$
steps. A sequence $u$ is computed by $M$ if and only if for every $n \ge p$
$$u_{n+1} = u_n + h \Bigl(\sum_{j=0}^{p} b_j f(t_{n-j}, u_{n-j}) + b_{-1} f(t_{n+1},
  u_{n+1})\Bigr).$$

**Generalization.** The recurrence permits any real step and places no constraint on the
starting values. The orbit definition does not require the oldest coefficients to be nonzero. -/
theorem equation_11_49_iff {M : LinearMultistep} (hM : equation_11_49 M) (u : ℕ → ℝ) :
    equation_11_45 M f h t₀ u ↔ ∀ n, M.p ≤ n → u (n + 1) = u n +
      h * (∑ j : Fin (M.p + 1), M.b j * f (grid t₀ h (n - j)) (u (n - j)) +
        M.bm1 * f (grid t₀ h (n + 1)) (u (n + 1))) := by
  rw [equation_11_45_iff]
  refine forall₂_congr fun n _ => ?_
  rw [equation_11_49] at hM
  rw [hM, Fin.sum_univ_succ, Pi.single_eq_same, Finset.sum_eq_zero fun j _ =>
    by rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j), zero_mul]]
  simp only [Fin.val_zero, Nat.sub_zero, one_mul, add_zero]
  constructor <;> intro H <;> linear_combination H

/-- **Equation (11.49)** of [quarteroni2000numerical], the Adams–Bashforth methods. For
$p \in \mathbb{N}$, the Adams–Bashforth method with $p + 1$ steps and the nodes
$t_n, \dots, t_{n-p}$ is an explicit Adams method: $a = (1, 0, \dots, 0)$, $b_{-1} = 0$, and
$$b_j = \int_0^1 \ell_j(s) \, ds, \qquad j = 0, \dots, p,$$
where $\ell_0, \dots, \ell_p$ is the Lagrange basis of the normalized nodes $s_i = -i$,
$i = 0, \dots, p$.

The method is `ODE.LinearMultistep.adamsBashforth p`. -/
theorem equation_11_49_adamsBashforth (p : ℕ) :
    equation_11_49 (LinearMultistep.adamsBashforth p) ∧
      (LinearMultistep.adamsBashforth p).bm1 = 0 ∧
      ∀ j : Fin (p + 1), (LinearMultistep.adamsBashforth p).b j = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 1) => -(i : ℝ)) j).eval s :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- **Equation (11.49)** of [quarteroni2000numerical], the Adams–Moulton methods. For
$p \in \mathbb{N}$, the Adams–Moulton method with $p + 1$ steps and the nodes
$t_{n+1}, t_n, \dots, t_{n-p}$ is an Adams method: $a = (1, 0, \dots, 0)$, and
$$b_{-1} = \int_0^1 \ell_0(s) \, ds, \qquad b_k = \int_0^1 \ell_{k+1}(s) \, ds, \quad k = 0,
  \dots, p,$$
where $\ell_0, \dots, \ell_{p+1}$ is the Lagrange basis of the normalized nodes $s_i = 1 - i$,
$i = 0, \dots, p + 1$.

The method is `ODE.LinearMultistep.adamsMoulton (p + 1)`, and $p$ is the index of the book.

**Reading.** Lean's Adams–Moulton index is the degree of the field interpolation polynomial. In
particular, backward Euler and Crank–Nicolson have indices $0$ and $1$. -/
theorem equation_11_49_adamsMoulton (p : ℕ) :
    equation_11_49 (LinearMultistep.adamsMoulton (p + 1)) ∧
      (LinearMultistep.adamsMoulton (p + 1)).bm1 = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 2) => 1 - (i : ℝ)) 0).eval s ∧
      ∀ k : Fin (p + 1), (LinearMultistep.adamsMoulton (p + 1)).b k = ∫ s in (0 : ℝ)..1,
        (Lagrange.basis Finset.univ (fun i : Fin (p + 2) => 1 - (i : ℝ)) k.succ).eval s := by
  refine ⟨rfl, ?_, fun k => ?_⟩
  · have h0 : 0 < p + 1 + 1 := Nat.succ_pos _
    change LinearMultistep.adamsMoultonWeight (p + 1) 0 = _
    simp only [LinearMultistep.adamsMoultonWeight, h0, ↓reduceDIte]
    rfl
  · have hk : (k : ℕ) + 1 < p + 1 + 1 := by have := k.is_lt; omega
    change LinearMultistep.adamsMoultonWeight (p + 1) ((k : ℕ) + 1) = _
    simp only [LinearMultistep.adamsMoultonWeight, hk, ↓reduceDIte]
    rfl

/-- **Equation (11.50)** of [quarteroni2000numerical], the Adams–Bashforth methods.

* A sequence $u$ is computed by the two-step Adams–Bashforth method if and only if for every
  $n \ge 1$
$$u_{n+1} = u_n + \frac{h}{2} (3f_n - f_{n-1}).$$
* The one-step Adams–Bashforth method is forward Euler: its sequences are those of (11.7).
* The two-, three- and four-step methods have $b_{-1} = 0$, $a = (1, 0, \dots, 0)$ and the
  weights $b = (3/2, -1/2)$, $b = (23/12, -16/12, 5/12)$ and
  $b = (55/24, -59/24, 37/24, -9/24)$.

The $(p+1)$-step method is `ODE.LinearMultistep.adamsBashforth p`. -/
theorem equation_11_50 :
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsBashforth 1) f h t₀ u ↔
      ∀ n, 1 ≤ n → u (n + 1) = u n +
        h / 2 * (3 * f (grid t₀ h n) (u n) - f (grid t₀ h (n - 1)) (u (n - 1)))) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsBashforth 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_7 f)) h t₀ u) ∧
    LinearMultistep.adamsBashforth 1 = ⟨1, ![1, 0], ![3 / 2, -1 / 2], 0⟩ ∧
    LinearMultistep.adamsBashforth 2 = ⟨2, ![1, 0, 0], ![23 / 12, -16 / 12, 5 / 12], 0⟩ ∧
    LinearMultistep.adamsBashforth 3 =
      ⟨3, ![1, 0, 0, 0], ![55 / 24, -59 / 24, 37 / 24, -9 / 24], 0⟩ := by
  refine ⟨fun u => ?_, fun u => ?_, LinearMultistep.adamsBashforth_one_eq,
    LinearMultistep.adamsBashforth_two_eq, LinearMultistep.adamsBashforth_three_eq⟩
  · rw [equation_11_45_iff, LinearMultistep.adamsBashforth_one_eq]
    change (∀ n, 1 ≤ n → u (n + 1) = ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * f (grid t₀ h (n - j)) (u (n - j)) +
      h * 0 * f (grid t₀ h (n + 1)) (u (n + 1))) ↔ _
    refine forall₂_congr fun n _ => ?_
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, mul_zero]
    constructor <;> intro H <;> linear_combination H
  · rw [equation_11_45, LinearMultistep.adamsBashforth_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_forwardEuler_iff]
    rfl

/-- **Section 11.5.1** of [quarteroni2000numerical]. For every $p \in \mathbb{N}$, the
Adams–Bashforth method with $q = p + 1$ steps has order $q$.

The proof specializes `ODE.LinearMultistep.adamsBashforth_hasOrder`. -/
theorem adamsBashforth_order (p : ℕ) :
    definition_11_9_order_method (LinearMultistep.adamsBashforth p) (p + 1) :=
  LinearMultistep.adamsBashforth_hasOrder p

/-- **Equation (11.51)** of [quarteroni2000numerical], the Adams–Moulton methods.

* A sequence $u$ is computed by the two-step Adams–Moulton method if and only if for every
  $n \ge 1$
$$u_{n+1} = u_n + \frac{h}{12} (5f_{n+1} + 8f_n - f_{n-1}).$$
* The methods `ODE.LinearMultistep.adamsMoulton 0` and `ODE.LinearMultistep.adamsMoulton 1` are
  backward Euler (11.8) and Crank–Nicolson (11.9): their sequences are those of the one-step
  methods.
* The two-, three- and four-step methods have $a = (1, 0, \dots, 0)$ and the coefficients
  $(b_{-1}; b) = (5/12; 8/12, -1/12)$, $(9/24; 19/24, -5/24, 1/24)$ and
  $(251/720; 646/720, -264/720, 106/720, -19/720)$.

**Reading.** Lean's Adams–Moulton index is the degree of the field interpolation polynomial. In
particular, backward Euler and Crank–Nicolson have indices $0$ and $1$. -/
theorem equation_11_51 :
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 2) f h t₀ u ↔
      ∀ n, 1 ≤ n → u (n + 1) = u n + h / 12 * (5 * f (grid t₀ h (n + 1)) (u (n + 1)) +
        8 * f (grid t₀ h n) (u n) - f (grid t₀ h (n - 1)) (u (n - 1)))) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_8 f)) h t₀ u) ∧
    (∀ u : ℕ → ℝ, equation_11_45 (LinearMultistep.adamsMoulton 1) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_9 f)) h t₀ u) ∧
    LinearMultistep.adamsMoulton 2 = ⟨1, ![1, 0], ![8 / 12, -1 / 12], 5 / 12⟩ ∧
    LinearMultistep.adamsMoulton 3 = ⟨2, ![1, 0, 0], ![19 / 24, -5 / 24, 1 / 24], 9 / 24⟩ ∧
    LinearMultistep.adamsMoulton 4 =
      ⟨3, ![1, 0, 0, 0], ![646 / 720, -264 / 720, 106 / 720, -19 / 720], 251 / 720⟩ := by
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, LinearMultistep.adamsMoulton_two_eq,
    LinearMultistep.adamsMoulton_three_eq, LinearMultistep.adamsMoulton_four_eq⟩
  · rw [equation_11_45_iff, LinearMultistep.adamsMoulton_two_eq]
    change (∀ n, 1 ≤ n → u (n + 1) = ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * f (grid t₀ h (n - j)) (u (n - j)) +
      h * (5 / 12) * f (grid t₀ h (n + 1)) (u (n + 1))) ↔ _
    refine forall₂_congr fun n _ => ?_
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero]
    constructor <;> intro H <;> linear_combination H
  · rw [equation_11_45, LinearMultistep.adamsMoulton_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_backwardEuler_iff]
    rfl
  · rw [equation_11_45, LinearMultistep.adamsMoulton_one_eq,
      LinearMultistep.isOrbit_ofOneStep_crankNicolson_iff]
    rfl

/-- **Section 11.5.1** of [quarteroni2000numerical]. For every $p \in \mathbb{N}$, the method
`ODE.LinearMultistep.adamsMoulton p` has order $p + 1$. So the $q$-step Adams–Moulton method has
order $q + 1$ for $q \ge 1$, and for $p = 0$ the method is backward Euler, of order $1$.

The proof specializes `ODE.LinearMultistep.adamsMoulton_hasOrder`.

**Reading.** Lean's Adams–Moulton index is the degree of the field interpolation polynomial. In
particular, backward Euler and Crank–Nicolson have indices $0$ and $1$. -/
theorem adamsMoulton_order (p : ℕ) :
    definition_11_9_order_method (LinearMultistep.adamsMoulton p) (p + 1) :=
  LinearMultistep.adamsMoulton_hasOrder p

/-- **Table 11.1** of [quarteroni2000numerical]. The error constants $C^*_{q+1}$ of the
Adams–Bashforth methods of order $q = 1, 2, 3, 4$ are
$$\frac{1}{2}, \quad \frac{5}{12}, \quad \frac{3}{8}, \quad \frac{251}{720},$$
and the error constants $C_{q+1}$ of the Adams–Moulton methods of order $q = 1, 2, 3, 4$ are
$$-\frac{1}{2}, \quad -\frac{1}{12}, \quad -\frac{1}{24}, \quad -\frac{19}{720}.$$

**Reading.** The index $q$ of the table is read as the order in both columns. The caption
"having order $q + 1$" for the Adams–Moulton column would place $-1/2$ at Crank–Nicolson, whose
error constant is $-1/12$.

The Adams–Bashforth method of order $q$ is `ODE.LinearMultistep.adamsBashforth (q - 1)`, and the
Adams–Moulton method of order $q$ is `ODE.LinearMultistep.adamsMoulton (q - 1)`. The proofs
specialize `ODE.LinearMultistep.adamsBashforth_errorConstant` and
`ODE.LinearMultistep.adamsMoulton_errorConstant`. -/
theorem adamsErrorConstants :
    (errorConstant (LinearMultistep.adamsBashforth 0) 1 = 1 / 2 ∧
      errorConstant (LinearMultistep.adamsBashforth 1) 2 = 5 / 12 ∧
      errorConstant (LinearMultistep.adamsBashforth 2) 3 = 3 / 8 ∧
      errorConstant (LinearMultistep.adamsBashforth 3) 4 = 251 / 720) ∧
    (errorConstant (LinearMultistep.adamsMoulton 0) 1 = -1 / 2 ∧
      errorConstant (LinearMultistep.adamsMoulton 1) 2 = -1 / 12 ∧
      errorConstant (LinearMultistep.adamsMoulton 2) 3 = -1 / 24 ∧
      errorConstant (LinearMultistep.adamsMoulton 3) 4 = -19 / 720) :=
  ⟨LinearMultistep.adamsBashforth_errorConstant, LinearMultistep.adamsMoulton_errorConstant⟩

/-! ### §11.5.2, Table 11.2: the BDF methods -/

/-- **Table 11.2** of [quarteroni2000numerical], the **backward differentiation formulae**. For
$p = 0, \dots, 5$, the BDF method with $p + 1$ steps is the implicit method
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h b_{-1} f_{n+1},$$
with $b_0 = \dots = b_p = 0$, obtained by differentiation of the polynomial that interpolates
$u$ at $t_{n+1}, \dots, t_{n-p}$. The method for $p = 0$ is backward Euler.

**Typo.** The book prints $b_{-1} = 60/137$ in the row $p = 5$. The coefficient is $60/147$:
with $60/137$ the first-order condition fails.

The family is `ODE.LinearMultistep.bdf`; the coefficients are listed in
`QuarteroniSaccoSaleri.Chapter11.bdf_table`. -/
noncomputable def bdf : Fin 6 → LinearMultistep := LinearMultistep.bdf

/-- **Table 11.2** of [quarteroni2000numerical]. For $p = 0, \dots, 5$, the BDF method of the row
$p$ has $p + 1$ steps and $b_0 = \dots = b_p = 0$. -/
theorem bdf_p_b (k : Fin 6) : (bdf k).p = k ∧ (bdf k).b = 0 := by
  fin_cases k <;> refine ⟨rfl, ?_⟩ <;> funext j <;> fin_cases j <;> rfl

/-- **Table 11.2** of [quarteroni2000numerical]. For $p = 0, \dots, 5$, a sequence $u$ is computed
by the BDF method of the row $p$ if and only if for every $n \ge p$
$$u_{n+1} = \sum_{j=0}^{p} a_j u_{n-j} + h b_{-1} f(t_{n+1}, u_{n+1}).$$
-/
theorem bdf_isOrbit_iff (k : Fin 6) (u : ℕ → ℝ) :
    equation_11_45 (bdf k) f h t₀ u ↔ ∀ n, (bdf k).p ≤ n → u (n + 1) =
      ∑ j : Fin ((bdf k).p + 1), (bdf k).a j * u (n - j) +
        h * (bdf k).bm1 * f (grid t₀ h (n + 1)) (u (n + 1)) := by
  rw [equation_11_45_iff]
  refine forall₂_congr fun n _ => ?_
  rw [(bdf_p_b k).2]
  simp

/-- **Table 11.2** of [quarteroni2000numerical], the coefficients. The BDF method of the row $p = 0$
is backward Euler: its sequences are those of (11.8). The rows $p = 1, \dots, 5$ have the
coefficients $(a_0, \dots, a_p; b_{-1})$:

* $p = 1$: $(4/3, -1/3; 2/3)$;
* $p = 2$: $(18/11, -9/11, 2/11; 6/11)$;
* $p = 3$: $(48/25, -36/25, 16/25, -3/25; 12/25)$;
* $p = 4$: $(300/137, -300/137, 200/137, -75/137, 12/137; 60/137)$;
* $p = 5$: $(360/147, -450/147, 400/147, -225/147, 72/147, -10/147; 60/147)$.

The last coefficient of the row $p = 5$ corrects a typo of the book; see
`QuarteroniSaccoSaleri.Chapter11.bdf`.

**Correction.** The $p=5$ row uses $b_{-1}=60/147$, whereas the printed denominator is $137$. -/
theorem bdf_table :
    (∀ u : ℕ → ℝ, equation_11_45 (bdf 0) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_8 f)) h t₀ u) ∧
    bdf 1 = ⟨1, ![4 / 3, -1 / 3], 0, 2 / 3⟩ ∧
    bdf 2 = ⟨2, ![18 / 11, -9 / 11, 2 / 11], 0, 6 / 11⟩ ∧
    bdf 3 = ⟨3, ![48 / 25, -36 / 25, 16 / 25, -3 / 25], 0, 12 / 25⟩ ∧
    bdf 4 = ⟨4, ![300 / 137, -300 / 137, 200 / 137, -75 / 137, 12 / 137], 0, 60 / 137⟩ ∧
    bdf 5 = ⟨5, ![360 / 147, -450 / 147, 400 / 147, -225 / 147, 72 / 147, -10 / 147], 0,
      60 / 147⟩ :=
  ⟨fun u => by
    rw [equation_11_45, bdf, LinearMultistep.bdf_zero_eq,
      LinearMultistep.isOrbit_ofOneStep_backwardEuler_iff]
    rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Section 11.5.2** of [quarteroni2000numerical]. For $p = 0, \dots, 5$, the BDF method with
$p + 1$ steps has order $p + 1$.

The proof specializes `ODE.LinearMultistep.bdf_hasOrder`.

**Reading.** The statement establishes order $p+1$ for the six coefficient rows in Table 11.2. -/
theorem bdf_order (k : Fin 6) : definition_11_9_order_method (bdf k) (k + 1) :=
  LinearMultistep.bdf_hasOrder k

end QuarteroniSaccoSaleri.Chapter11
