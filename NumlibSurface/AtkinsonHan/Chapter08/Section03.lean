/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Nonlinear.FixedPoint
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram
import NumlibSurface.AtkinsonHan.Chapter08.Section02

/-!
# Atkinson and Han, Section 8.3: The Lax–Milgram lemma

This module formalizes Section 8.3 of [han2009theoretical]. The data is a real bilinear form
$a : V \times V \to \mathbb{R}$ on a real normed space $V$, later a Hilbert space, together with
$\ell \in V'$. The section defines bounded, positive, strictly positive, strongly positive
($V$-elliptic) and symmetric forms. Theorem 8.3.1 identifies the bounded forms with the operators
$A \in \mathcal{L}(V, V')$ through $\langle Au, v \rangle = a(u, v)$. Theorems 8.3.2 and 8.3.3 show
that the energy $E(v) = \frac12 \|v\|^2 - \ell(v)$, and more generally
$E(v) = \frac12 a(v, v) - \ell(v)$ for a symmetric $V$-elliptic form, has a unique minimizer on a
nonempty closed convex set $K$, characterized by a variational inequality, and on a subspace by a
variational equation. Theorem 8.3.4, the Lax–Milgram lemma, states that for a bounded $V$-elliptic
form on a Hilbert space the problem (8.3.5), to find $u \in V$ with $a(u, v) = \ell(v)$ for all
$v \in V$, has exactly one solution, with $\|u\| \le \|\ell\|/\alpha$. Example 8.3.5 applies it to
the Dirichlet problem for $-\Delta u = f$.

Chapter 9 and Section 8.7 use the same vocabulary, so this module also contains the facts that the
source records only later as (9.1.3), (9.1.7) and (9.4.2)–(9.4.7). The second proof of Theorem 8.3.4
in the source already uses the operator $A : V \to V$ of (9.4.5). The proofs specialize the backbone
modules `Numlib.Variational.Forms` and `Numlib.Variational.LaxMilgram`, and Exercise 8.3.1 uses the
strongly monotone operators of `Numlib.Nonlinear.FixedPoint`.

## Main definitions

* Section 8.3, `AtkinsonHan.BilinForm`: a real bilinear form on $V$.
* Section 8.3, `AtkinsonHan.BilinForm.IsBoundedWith` and `AtkinsonHan.BilinForm.IsBounded`:
  $|a(u, v)| \le M \|u\| \|v\|$, for a given $M$ or for some $M > 0$.
* Section 8.3, `AtkinsonHan.BilinForm.IsPositive` and `AtkinsonHan.BilinForm.IsStrictlyPositive`:
  $a(v, v) \ge 0$ for all $v$, and $a(v, v) > 0$ for all $v \ne 0$.
* Section 8.3, `AtkinsonHan.BilinForm.IsEllipticWith` and `AtkinsonHan.BilinForm.IsElliptic`:
  $a(v, v) \ge \alpha \|v\|^2$, for a given $\alpha$ or for some $\alpha > 0$.
* Theorem 8.3.1, `AtkinsonHan.BilinForm.toCLM` and `AtkinsonHan.BilinForm.ofCLM`: a bounded form as
  an operator $A \in \mathcal{L}(V, V')$, and the form $\langle Au, v \rangle$ of an operator.
* Theorem 8.3.1, `AtkinsonHan.BilinForm.theorem_8_3_1`: the one-to-one correspondence between
  $\mathcal{L}(V, V')$ and the bounded bilinear forms on $V$.
* Equation (8.3.2), `AtkinsonHan.BilinForm.energy`: the energy $E(v) = \frac12 a(v, v) - \ell(v)$.
* Section 8.3, `AtkinsonHan.BilinForm.energyNorm`: the energy norm $\|v\|_a = \sqrt{a(v, v)}$.
* Equation (9.4.5), `AtkinsonHan.BilinForm.toOperator`: the operator $A : V \to V$ with
  $(Au, v) = a(u, v)$ on a Hilbert space.

## Main results

* Theorem 8.3.1, `AtkinsonHan.BilinForm.isBoundedWith_opNorm` and
  `AtkinsonHan.BilinForm.norm_toCLM_le`: $|a(u, v)| \le \|A\| \|u\| \|v\|$, and $\|A\| \le M$.
* Theorem 8.3.2, `AtkinsonHan.Chapter08.theorem_8_3_2`: $\frac12 \|v\|^2 - \ell(v)$ has a unique
  minimizer on a nonempty closed convex set.
* Theorem 8.3.2, `AtkinsonHan.Chapter08.theorem_8_3_2_iff` and
  `AtkinsonHan.Chapter08.theorem_8_3_2_subspace`: the minimizer is characterized by
  $(u, v - u) \ge \ell(v - u)$ on $K$, and by $(u, v) = \ell(v)$ on a subspace.
* Theorem 8.3.3, `AtkinsonHan.Chapter08.theorem_8_3_3`: the energy of a bounded symmetric
  $V$-elliptic form has a unique minimizer on a nonempty closed convex set.
* Theorem 8.3.3, `AtkinsonHan.Chapter08.theorem_8_3_3_iff` and
  `AtkinsonHan.Chapter08.theorem_8_3_3_subspace`: the minimizer is characterized by the variational
  inequality (8.3.3), and on a subspace by the variational equation (8.3.4).
* Theorem 8.3.4, `AtkinsonHan.Chapter08.theorem_8_3_4`: the Lax–Milgram lemma, unique solvability of
  (8.3.5).
* Theorem 8.3.4, `AtkinsonHan.Chapter08.theorem_8_3_4_norm_le` and
  `AtkinsonHan.Chapter08.theorem_8_3_4_norm_sub_le`: $\|u\| \le \|\ell\|/\alpha$, and
  $\|u_1 - u_2\| \le \|\ell_1 - \ell_2\|/\alpha$.
* Example 8.3.5, `AtkinsonHan.Chapter08.example_8_3_5`: the weak Dirichlet problem for
  $-\Delta u = f$ on a bounded open set has exactly one solution in $H^1_0(\Omega)$.
* Exercise 8.3.1, `AtkinsonHan.Chapter08.exercise_8_3_1`: the Lax–Milgram lemma from the theory of
  strongly monotone Lipschitz operators of Section 5.1.

## Proof outline

The source gives two proofs of Theorem 8.3.4, and both are here. The first shows that
$P_\theta u = u - \theta (Au - f)$ is a contraction for $0 < \theta < 2\alpha/M^2$, where $f$ is the
Riesz representative of $\ell$ (`AtkinsonHan.Chapter08.contractingWith_damped_sub_smul`). The second
shows that $A$ is bounded below, so that its range is closed, and that the orthogonal complement of
the range is $\{0\}$, so that $A$ is a bijection (`AtkinsonHan.Chapter08.bijective_toOperator`). The
theorem itself specializes `SesqForm.laxMilgram`.

## Implementation notes

* A form is `AtkinsonHan.BilinForm V`, that is Mathlib's `LinearMap.BilinForm ℝ V`, and the
  properties of §8.3 are unbundled predicates on it. Symmetry is Mathlib's
  `LinearMap.BilinForm.IsSymm`.
* `AtkinsonHan.BilinForm.toCLM` bundles a bounded form as `V →L[ℝ] V →L[ℝ] ℝ`. This type is the
  backbone's `SesqForm ℝ V`, so the API of `Numlib.Variational` applies with no conversion. The
  lemmas under "Bridges to the backbone predicates" erase the `RCLike.re` and `starRingEnd`
  decorations of the general theory over $\mathbb{R}$.
* On a Hilbert space, `AtkinsonHan.BilinForm.toOperator` is the Riesz representation of the operator
  of Theorem 8.3.1. The Riesz representative $f$ of $\ell$ in (9.4.6) is `SesqForm.rieszRep ℓ`.
* A minimizer is stated with Mathlib's `IsMinOn`. `AtkinsonHan.Chapter08.isMinOn_iff_eq_ciInf`
  converts it to the form $E(u) = \inf_K E$ of the source.

## Deviations from the source

* **Example 8.3.5** (generalization). The source assumes a Lipschitz boundary. The example here
  holds on every bounded open set. See `AtkinsonHan.Chapter08.example_8_3_5`.
-/

open Filter Metric MeasureTheory Set TopologicalSpace Topology
open scoped InnerProductSpace

namespace AtkinsonHan

/-! ### The bilinear forms of Section 8.3 and the operators they represent -/

/-- **Section 8.3** of [han2009theoretical], bilinear forms. A **real bilinear form** on a real
vector space $V$ is a map $a : V \times V \to \mathbb{R}$ that is linear in each argument.

It is Mathlib's `LinearMap.BilinForm ℝ V`, a linear map from $V$ to the linear functionals on
$V$. -/
abbrev BilinForm (V : Type*) [AddCommGroup V] [Module ℝ V] := LinearMap.BilinForm ℝ V

namespace BilinForm

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Section 8.3** of [han2009theoretical], boundedness with a constant. Let $V$ be a real normed
space. A bilinear form $a$ on $V$ is **bounded with constant** $M$ if
$$|a(u, v)| \le M \|u\| \|v\| \quad \text{for all } u, v \in V.$$

The constant is explicit, and no sign condition on $M$ is part of the definition. -/
def IsBoundedWith (a : BilinForm V) (M : ℝ) : Prop := ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖

/-- **Section 8.3** of [han2009theoretical], definition of a bounded form. A bilinear form $a$ on a
real normed space $V$ is **bounded** if there is $M > 0$ with $|a(u, v)| \le M \|u\| \|v\|$ for
all $u, v \in V$. -/
def IsBounded (a : BilinForm V) : Prop := ∃ M > 0, a.IsBoundedWith M

/-- **Section 8.3** of [han2009theoretical], definition of a positive form. A bilinear form $a$ on a
real normed space $V$ is **positive** if $a(v, v) \ge 0$ for all $v \in V$.

Unlike Mathlib's `LinearMap.IsPositive`, this does not include symmetry. -/
def IsPositive (a : BilinForm V) : Prop := ∀ v, 0 ≤ a v v

/-- **Section 8.3** of [han2009theoretical], definition of a strictly positive form. A bilinear form
$a$ on a real normed space $V$ is **strictly positive** if $a(v, v) > 0$ for all $v \in V$ with
$v \ne 0$. -/
def IsStrictlyPositive (a : BilinForm V) : Prop := ∀ v, v ≠ 0 → 0 < a v v

/-- **Section 8.3** of [han2009theoretical], strong positivity with a constant. A bilinear form $a$
on a real normed space $V$ is **$V$-elliptic** (strongly positive) **with constant** $\alpha$ if
$$a(v, v) \ge \alpha \|v\|^2 \quad \text{for all } v \in V.$$

This is also (9.1.3) with $\alpha = c_0$. No sign condition on $\alpha$ is part of the
definition. -/
def IsEllipticWith (a : BilinForm V) (α : ℝ) : Prop := ∀ v, α * ‖v‖ ^ 2 ≤ a v v

/-- **Section 8.3** of [han2009theoretical], definition of a strongly positive form. A bilinear form
$a$ on a real normed space $V$ is **$V$-elliptic** (strongly positive) if there is $\alpha > 0$
with $a(v, v) \ge \alpha \|v\|^2$ for all $v \in V$. -/
def IsElliptic (a : BilinForm V) : Prop := ∃ α > 0, a.IsEllipticWith α

variable {a : BilinForm V} {M α : ℝ}

/-- A bilinear form that is bounded with a constant $M > 0$ is bounded. -/
theorem IsBoundedWith.isBounded (hM : a.IsBoundedWith M) (hM0 : 0 < M) : a.IsBounded :=
  ⟨M, hM0, hM⟩

/-- A bilinear form that is $V$-elliptic with a constant $\alpha > 0$ is $V$-elliptic. -/
theorem IsEllipticWith.isElliptic (ha : a.IsEllipticWith α) (hα : 0 < α) : a.IsElliptic :=
  ⟨α, hα, ha⟩

/-- A bilinear form that is $V$-elliptic with a constant $\alpha \ge 0$ is positive. The source
notes that strong positivity implies positivity. -/
theorem IsEllipticWith.isPositive (ha : a.IsEllipticWith α) (hα : 0 ≤ α) : a.IsPositive :=
  fun v => le_trans (by positivity) (ha v)

/-- A bilinear form that is $V$-elliptic with a constant $\alpha > 0$ is strictly positive. The
source notes that strong positivity implies strict positivity. -/
theorem IsEllipticWith.isStrictlyPositive (ha : a.IsEllipticWith α) (hα : 0 < α) :
    a.IsStrictlyPositive := fun v hv => lt_of_lt_of_le (by positivity) (ha v)

/-- A bilinear form $a$ is symmetric in Mathlib's sense `LinearMap.BilinForm.IsSymm` if and only if
$a(u, v) = a(v, u)$ for all $u, v \in V$, which is the symmetry of the source. -/
theorem isSymm_iff : LinearMap.BilinForm.IsSymm a ↔ ∀ u v, a u v = a v u :=
  LinearMap.BilinForm.isSymm_def

/-! ### The correspondence $A \leftrightarrow a$ of Theorem 8.3.1 -/

/-- **Theorem 8.3.1** of [han2009theoretical], from forms to operators. Let $V$ be a real normed
space, and let $a$ be a bilinear form on $V$ that is bounded with constant $M$. The **operator
of** $a$ is $A \in \mathcal{L}(V, V')$ with $\langle Au, v \rangle = a(u, v)$, that is $a$ as a
bounded bilinear map `V →L[ℝ] V →L[ℝ] ℝ`.

Over $\mathbb{R}$ this type is the backbone's `SesqForm ℝ V`, so every result on bounded
sesquilinear forms applies to `a.toCLM hM`. The map is built with `LinearMap.mkContinuous₂` and
the bound $M$. -/
noncomputable def toCLM (a : BilinForm V) (hM : a.IsBoundedWith M) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ a M fun u v => by rw [Real.norm_eq_abs]; exact hM u v

/-- **Theorem 8.3.1** of [han2009theoretical], the defining relation. Let $a$ be a bilinear form on
a real normed space $V$ that is bounded with constant $M$, and let $A$ be its operator. Then
$\langle Au, v \rangle = a(u, v)$ for all $u, v \in V$. -/
@[simp]
theorem toCLM_apply (hM : a.IsBoundedWith M) (u v : V) : a.toCLM hM u v = a u v := rfl

/-- **Theorem 8.3.1** of [han2009theoretical], the bound on the operator. Let $a$ be a bilinear form
on a real normed space $V$ that is bounded with constant $M \ge 0$, and let $A$ be its operator.
Then $\|A\| \le M$. -/
theorem norm_toCLM_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖a.toCLM hM‖ ≤ M :=
  LinearMap.mkContinuous₂_norm_le _ hM0 _

/-- **Theorem 8.3.1** of [han2009theoretical], from operators to forms. Let $V$ be a real normed
space and $A \in \mathcal{L}(V, V')$. The **form of** $A$ is the bilinear form
$a(u, v) = \langle Au, v \rangle$ on $V$. -/
noncomputable def ofCLM (A : V →L[ℝ] StrongDual ℝ V) : BilinForm V :=
  (ContinuousLinearMap.coeLM ℝ).comp (A : V →ₗ[ℝ] StrongDual ℝ V)

/-- **Theorem 8.3.1** of [han2009theoretical], the defining relation. For
$A \in \mathcal{L}(V, V')$, the form of $A$ satisfies $a(u, v) = \langle Au, v \rangle$ for all
$u, v \in V$. -/
@[simp]
theorem ofCLM_apply (A : V →L[ℝ] StrongDual ℝ V) (u v : V) : ofCLM A u v = A u v := rfl

/-- **Theorem 8.3.1** of [han2009theoretical], the bound on the form. For
$A \in \mathcal{L}(V, V')$, the form of $A$ is bounded with constant $\|A\|$:
$$|a(u, v)| \le \|A\| \|u\| \|v\| \quad \text{for all } u, v \in V.$$
-/
theorem isBoundedWith_opNorm (A : V →L[ℝ] StrongDual ℝ V) : (ofCLM A).IsBoundedWith ‖A‖ :=
  fun u v => by rw [ofCLM_apply, ← Real.norm_eq_abs]; exact A.le_opNorm₂ u v

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is bounded.

The proof uses the constant $\|A\| + 1$ instead of $\|A\|$, so that the constant is positive
also for $A = 0$, as `AtkinsonHan.BilinForm.IsBounded` requires. -/
theorem isBounded_ofCLM (A : V →L[ℝ] StrongDual ℝ V) : (ofCLM A).IsBounded :=
  ⟨‖A‖ + 1, by positivity, fun u v =>
    (isBoundedWith_opNorm A u v).trans
      (by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)])⟩

/-- **Theorem 8.3.1** of [han2009theoretical], one half of the correspondence. Let $a$ be a bilinear
form on a real normed space $V$ that is bounded with constant $M$. Then the form of the operator
of $a$ is $a$.

Together with `AtkinsonHan.BilinForm.toCLM_ofCLM`, this is the one-to-one correspondence of
Theorem 8.3.1. The recovered form does not depend on the bound $M$ that was used to build the
operator. -/
theorem ofCLM_toCLM (hM : a.IsBoundedWith M) : ofCLM (a.toCLM hM) = a := by
  ext u v
  rfl

/-- For $A \in \mathcal{L}(V, V')$ and any constant $M$ that bounds the form of $A$, the operator of
the form of $A$ is $A$. This is the other half of the correspondence of Theorem 8.3.1. -/
theorem toCLM_ofCLM (A : V →L[ℝ] StrongDual ℝ V) {M : ℝ} (hM : (ofCLM A).IsBoundedWith M) :
    (ofCLM A).toCLM hM = A := by
  ext u v
  rfl

/-- **Theorem 8.3.1** of [han2009theoretical]. Let $V$ be a real normed space. The relation
$\langle Au, v \rangle = a(u, v)$ is a one-to-one correspondence between the operators
$A \in \mathcal{L}(V, V')$ and the bounded bilinear forms $a$ on $V$.

The quantitative part of the theorem is `AtkinsonHan.BilinForm.isBoundedWith_opNorm`,
$|a(u, v)| \le \|A\| \|u\| \|v\|$, together with `AtkinsonHan.BilinForm.norm_toCLM_le`,
$\|A\| \le M$. The correspondence is a Lean equivalence from `V →L[ℝ] StrongDual ℝ V` to the
subtype of bounded forms. -/
noncomputable def theorem_8_3_1 : (V →L[ℝ] StrongDual ℝ V) ≃ {a : BilinForm V // a.IsBounded} where
  toFun A := ⟨ofCLM A, isBounded_ofCLM A⟩
  invFun a := a.1.toCLM a.2.choose_spec.2
  left_inv A := toCLM_ofCLM A _
  right_inv _ := Subtype.ext (ofCLM_toCLM _)

/-!
### The properties of a form and of its operator

Each property of the form $a$ of an operator $A$ is the corresponding property of $A$, read through
$\langle Av, v \rangle = a(v, v)$. All of them except the first hold by definition.
-/

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is bounded with constant $M$ if and only if
$\|Av\| \le M \|v\|$ for all $v \in V$. -/
theorem isBoundedWith_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsBoundedWith M ↔ ∀ v, ‖A v‖ ≤ M * ‖v‖ := by
  constructor
  · intro h v
    have hMv : 0 ≤ M * ‖v‖ := by
      rcases eq_or_lt_of_le (norm_nonneg v) with hv | hv
      · simp [← hv]
      · refine le_of_mul_le_mul_right ?_ hv
        simpa using le_trans (abs_nonneg _) (h v v)
    refine (A v).opNorm_le_bound hMv fun w => ?_
    calc ‖A v w‖ = |A v w| := Real.norm_eq_abs _
      _ ≤ M * ‖v‖ * ‖w‖ := h v w
  · intro h u v
    rw [ofCLM_apply, ← Real.norm_eq_abs]
    calc ‖A u v‖ ≤ ‖A u‖ * ‖v‖ := (A u).le_opNorm v
      _ ≤ M * ‖u‖ * ‖v‖ := by gcongr; exact h u

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is positive if and only if
$\langle Av, v \rangle \ge 0$ for all $v \in V$. -/
theorem isPositive_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsPositive ↔ ∀ v, 0 ≤ A v v := Iff.rfl

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is strictly positive if and only if
$\langle Av, v \rangle > 0$ for all $v \ne 0$. -/
theorem isStrictlyPositive_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsStrictlyPositive ↔ ∀ v, v ≠ 0 → 0 < A v v := Iff.rfl

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is $V$-elliptic with constant $\alpha$ if and
only if $A$ is strongly monotone with that constant: $\langle Av, v \rangle \ge \alpha \|v\|^2$
for all $v \in V$. -/
theorem isEllipticWith_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    (ofCLM A).IsEllipticWith α ↔ ∀ v, α * ‖v‖ ^ 2 ≤ A v v := Iff.rfl

/-- For $A \in \mathcal{L}(V, V')$, the form of $A$ is symmetric if and only if
$\langle Au, v \rangle = \langle Av, u \rangle$ for all $u, v \in V$. -/
theorem isSymm_ofCLM_iff (A : V →L[ℝ] StrongDual ℝ V) :
    LinearMap.BilinForm.IsSymm (ofCLM A) ↔ ∀ u v, A u v = A v u := isSymm_iff

/-! ### The energy functional and the energy norm (Theorem 8.3.3, (9.1.7)) -/

/-- **Equation (8.3.2)** of [han2009theoretical], also (9.1.7). Let $a$ be a bilinear form on a real
normed space $V$, and let $\ell \in V'$. The **energy functional** is
$$E(v) = \frac12 a(v, v) - \ell(v), \qquad v \in V.$$
-/
noncomputable def energy (a : BilinForm V) (ℓ : StrongDual ℝ V) (v : V) : ℝ :=
  (1 / 2 : ℝ) * a v v - ℓ v

/-- **Section 8.3** of [han2009theoretical], also Section 9.4. The **energy norm** of a bilinear
form $a$ on a real normed space $V$ is $\|v\|_a = \sqrt{a(v, v)}$.

It is a norm when $a$ is symmetric and $V$-elliptic. For other forms the definition takes the
real square root, which is $0$ where $a(v, v) < 0$. -/
noncomputable def energyNorm (a : BilinForm V) (v : V) : ℝ := Real.sqrt (a v v)

/-- The energy norm is nonnegative: $\|v\|_a \ge 0$ for every $v$. -/
theorem energyNorm_nonneg (a : BilinForm V) (v : V) : 0 ≤ a.energyNorm v := Real.sqrt_nonneg _

end Normed

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {a : BilinForm V} {M α : ℝ}

/-!
### Bridges to the backbone predicates

The operator `a.toCLM hM` of a bounded form is a `SesqForm ℝ V` of the backbone. The results below
show that the predicates of the source are those of the backbone, with the `RCLike.re` and
`starRingEnd` decorations of the general theory erased over $\mathbb{R}$
(`SesqForm.isCoerciveWith_real_iff`, `SesqForm.isHermitian_real_iff`).
-/

/-- Let $V$ be a real inner product space and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$. For every constant $M'$, $a$ is bounded with constant $M'$ if and only if its
operator is bounded with constant $M'$ in the sense of `SesqForm.IsBoundedWith`. -/
theorem isBoundedWith_iff_toCLM {M' : ℝ} (hM : a.IsBoundedWith M) :
    a.IsBoundedWith M' ↔ SesqForm.IsBoundedWith (𝕜 := ℝ) (a.toCLM hM) M' := Iff.rfl

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$. Then
its operator is bounded with constant $M$ in the sense of `SesqForm.IsBoundedWith`. -/
theorem isBoundedWith_toCLM (hM : a.IsBoundedWith M) :
    SesqForm.IsBoundedWith (𝕜 := ℝ) (a.toCLM hM) M :=
  (isBoundedWith_iff_toCLM hM).mp hM

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$. Then
$a$ is $V$-elliptic with constant $\alpha$ if and only if its operator is coercive with constant
$\alpha$ in the sense of `SesqForm.IsCoerciveWith`. -/
theorem isEllipticWith_iff_isCoerciveWith (hM : a.IsBoundedWith M) :
    a.IsEllipticWith α ↔ SesqForm.IsCoerciveWith (𝕜 := ℝ) (a.toCLM hM) α := Iff.rfl

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$. Then
$a$ is $V$-elliptic if and only if its operator is coercive in the sense of Mathlib's
`IsCoercive`, that is $a(v, v) \ge C \|v\| \|v\|$ for some $C > 0$. -/
theorem isElliptic_iff_isCoercive (hM : a.IsBoundedWith M) :
    a.IsElliptic ↔ IsCoercive (a.toCLM hM) := by
  constructor
  · rintro ⟨α', hα', ha⟩
    exact ⟨α', hα', fun u => by simpa [sq, mul_assoc] using ha u⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun v => by simpa [sq, mul_assoc] using h v⟩

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$. Then
$a$ is symmetric if and only if its operator is Hermitian in the sense of
`SesqForm.IsHermitian`, since complex conjugation is the identity over $\mathbb{R}$. -/
theorem isSymm_iff_isHermitian (hM : a.IsBoundedWith M) :
    LinearMap.BilinForm.IsSymm a ↔ SesqForm.IsHermitian (𝕜 := ℝ) (a.toCLM hM) := isSymm_iff

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$, and
let $\ell \in V'$. Then the energy $E(v)$ of $a$ is the backbone's energy `SesqForm.energy` of
the operator of $a$, for every $v$. -/
theorem energy_eq (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (v : V) :
    a.energy ℓ v = SesqForm.energy (a.toCLM hM) ℓ v := rfl

/-- Let $a$ be a bilinear form on a real inner product space that is bounded with constant $M$. Then
the energy norm $\|v\|_a$ is the backbone's energy norm `SesqForm.energyNorm` of the operator of
$a$, for every $v$. -/
theorem energyNorm_eq (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v = SesqForm.energyNorm (a.toCLM hM) v := rfl

/-- **Theorem 8.3.3** of [han2009theoretical], the lower half of the norm equivalence
$c_1 \|v\| \le \|v\|_a \le c_2 \|v\|$. Let $a$ be a bilinear form on a real inner product space
that is bounded with constant $M$ and $V$-elliptic with constant $\alpha \ge 0$. Then for every
$v$,
$$\sqrt{\alpha} \, \|v\| \le \|v\|_a.$$
-/
theorem sqrt_mul_norm_le_energyNorm (hM : a.IsBoundedWith M) (hα : 0 ≤ α)
    (ha : a.IsEllipticWith α) (v : V) : Real.sqrt α * ‖v‖ ≤ a.energyNorm v := by
  rw [energyNorm_eq hM]
  exact SesqForm.sqrt_mul_norm_le_energyNorm (a.toCLM hM) hα ha v

/-- **Theorem 8.3.3** of [han2009theoretical], the upper half of the norm equivalence. Let $a$ be a
bilinear form on a real inner product space that is bounded with constant $M$. Then for every
$v$,
$$\|v\|_a \le \sqrt{M} \, \|v\|.$$
-/
theorem energyNorm_le_sqrt_mul_norm (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v ≤ Real.sqrt M * ‖v‖ := by
  rw [energyNorm_eq hM]
  exact SesqForm.energyNorm_le_sqrt_mul_norm (a.toCLM hM) (isBoundedWith_toCLM hM) v

end Inner

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {a : BilinForm V} {M α : ℝ}

/-- **Equation (9.4.5)** of [han2009theoretical]. Let $V$ be a real Hilbert space and let $a$ be a
bilinear form on $V$ that is bounded with constant $M$. The **operator** $A : V \to V$ of $a$ is
the bounded linear operator with
$$(Au, v) = a(u, v) \quad \text{for all } u, v \in V.$$

It is the Riesz representation of the operator $A \in \mathcal{L}(V, V')$ of Theorem 8.3.1, and
it is the backbone's `SesqForm.toOperator`. -/
noncomputable abbrev toOperator (a : BilinForm V) (hM : a.IsBoundedWith M) : V →L[ℝ] V :=
  SesqForm.toOperator (a.toCLM hM)

/-- **Equation (9.4.5)** of [han2009theoretical]. Let $a$ be a bilinear form on a real Hilbert space
$V$ that is bounded with constant $M$, and let $A$ be its operator. Then $(Au, v) = a(u, v)$ for
all $u, v \in V$. -/
theorem inner_toOperator (hM : a.IsBoundedWith M) (u v : V) :
    ⟪toOperator a hM u, v⟫_ℝ = a u v :=
  SesqForm.inner_toOperator _ u v

/-- Equation (9.4.3) of [han2009theoretical]: if $a$ is bounded with constant $M \ge 0$, then its
operator $A : V \to V$ satisfies $\|A\| \le M$. -/
theorem norm_toOperator_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖toOperator a hM‖ ≤ M := by
  rw [SesqForm.norm_toOperator]
  exact norm_toCLM_le hM0 hM

/-- Equation (9.4.2) of [han2009theoretical]: if $a$ is bounded and symmetric, then its operator
$A : V \to V$ is self-adjoint. -/
theorem isSelfAdjoint_toOperator (hM : a.IsBoundedWith M) (hs : LinearMap.BilinForm.IsSymm a) :
    IsSelfAdjoint (toOperator a hM) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    ((SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp ((isSymm_iff_isHermitian hM).mp hs))

/-- Equation (9.4.3) of [han2009theoretical]: if $a$ is bounded and $V$-elliptic with constant
$\alpha$, then its operator $A : V \to V$ is coercive with constant $\alpha$, that is
$(Av, v) \ge \alpha \|v\|^2$ for all $v$. -/
theorem isCoerciveWith_toOperator (hM : a.IsBoundedWith M) (ha : a.IsEllipticWith α) :
    (toOperator a hM : V →ₗ[ℝ] V).IsCoerciveWith α :=
  (SesqForm.isCoerciveWith_iff_toOperator _ α).mp ha

/-- Let $a$ be a bilinear form on a real Hilbert space that is bounded, symmetric and $V$-elliptic
with a constant $\alpha > 0$. Then its operator $A : V \to V$ is symmetric and coercive. So the
energy inner product $(u, v)_a = a(u, v)$ of Section 9.4 is an inner product. -/
theorem isSymmetricCoercive_toOperator (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) :
    (toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive where
  isSymmetric :=
    (SesqForm.isHermitian_iff_toOperator_isSymmetric _).mp ((isSymm_iff_isHermitian hM).mp hs)
  isCoercive := ⟨α, hα, isCoerciveWith_toOperator hM ha⟩

/-- Let $a$ be a bilinear form on a real Hilbert space that is bounded with constant $M$. Then the
energy norm $\|v\|_a$ of $a$ is the energy norm $\sqrt{(Av, v)}$ of its operator $A$ (the
root-namespace `energyNorm`), for every $v$. -/
theorem energyNorm_eq_energyNorm_toOperator (hM : a.IsBoundedWith M) (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a hM : V →ₗ[ℝ] V) v := by
  rw [energyNorm_eq hM]
  exact SesqForm.energyNorm_eq_energyNorm_toOperator _ v

/-- Equation (9.4.6) of [han2009theoretical]: for $\ell \in V'$ on a real Hilbert space $V$, the
Riesz representative $f$ of $\ell$ satisfies $(f, v) = \ell(v)$ for all $v \in V$. -/
theorem inner_rieszRep (ℓ : StrongDual ℝ V) (v : V) : ⟪SesqForm.rieszRep ℓ, v⟫_ℝ = ℓ v :=
  SesqForm.inner_rieszRep ℓ v

/-- Section 9.4 of [han2009theoretical]: for $\ell \in V'$ on a real Hilbert space $V$, the Riesz
representative $f$ of $\ell$ satisfies $\|f\| = \|\ell\|$. -/
theorem norm_rieszRep (ℓ : StrongDual ℝ V) : ‖SesqForm.rieszRep (𝕜 := ℝ) (V := V) ℓ‖ = ‖ℓ‖ :=
  SesqForm.norm_rieszRep ℓ

/-- **Equations (9.4.4) and (9.4.7)** of [han2009theoretical]. Let $a$ be a bilinear form on a real
Hilbert space $V$ that is bounded with constant $M$, let $A$ be its operator, let $\ell \in V'$
and let $f$ be the Riesz representative of $\ell$. Then for every $u \in V$,
$$Au = f \iff a(u, v) = \ell(v) \text{ for all } v \in V.$$
-/
theorem toOperator_eq_rieszRep_iff (hM : a.IsBoundedWith M) (ℓ : StrongDual ℝ V) (u : V) :
    toOperator a hM u = SesqForm.rieszRep ℓ ↔ ∀ v, a u v = ℓ v :=
  (SesqForm.forall_apply_eq_iff_toOperator_eq _ ℓ u).symm

end Hilbert

end BilinForm

namespace Chapter08

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Let $K$ be a set in a type $X$, let $f : X \to \mathbb{R}$ be bounded below on $K$, and let
$u \in K$. Then $u$ minimizes $f$ on $K$ if and only if $f(u) = \inf_{v \in K} f(v)$.

This converts between the form $E(u) = \inf_K E$ of the source and Mathlib's `IsMinOn`. The
forward direction is Mathlib's `IsMinOn.iInf_eq`, and only the converse needs $f$ bounded below. -/
theorem isMinOn_iff_eq_ciInf {X : Type*} {K : Set X} {f : X → ℝ} {u : X} (hu : u ∈ K)
    (hbdd : BddBelow (Set.range fun v : K => f v)) :
    IsMinOn f K u ↔ f u = ⨅ v : K, f v :=
  ⟨fun h => (h.iInf_eq hu).symm,
    fun h => isMinOn_iff.mpr fun v hv => h.trans_le (ciInf_le hbdd ⟨v, hv⟩)⟩

/-! ### Theorem 8.3.2: the energy $E(v) = \frac12 \|v\|^2 - \ell(v)$ -/

/-- For $\ell \in V'$ on a real inner product space $V$, the backbone's energy of the inner product
form is $E(v) = \frac12 \|v\|^2 - \ell(v)$, the functional of Theorem 8.3.2. -/
theorem energy_innerSL (ℓ : StrongDual ℝ V) (v : V) :
    SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ v = (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v := by
  simp [SesqForm.energy]

private theorem energy_innerSL_eq (ℓ : StrongDual ℝ V) :
    (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) = SesqForm.energy (innerSL ℝ : SesqForm ℝ V) ℓ := by
  funext v
  rw [energy_innerSL]

private theorem innerSL_hermitian : SesqForm.IsHermitian (innerSL ℝ : SesqForm ℝ V) :=
  SesqForm.innerSL_isHermitian

private theorem innerSL_coercive : SesqForm.IsCoerciveWith (innerSL ℝ : SesqForm ℝ V) 1 :=
  SesqForm.innerSL_isCoerciveWith

/-- **Theorem 8.3.2** of [han2009theoretical], existence and uniqueness. Let $V$ be a real Hilbert
space, let $K \subseteq V$ be nonempty, closed and convex, and let $\ell \in V'$. Then there is
exactly one $u \in K$ that minimizes
$$E(v) = \frac12 \|v\|^2 - \ell(v)$$
on $K$.

The proof specializes `SesqForm.existsUnique_isMinOn_energy` to the inner product. -/
theorem theorem_8_3_2 [CompleteSpace V] {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (ℓ : StrongDual ℝ V) :
    ∃! u, u ∈ K ∧ IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u := by
  rw [energy_innerSL_eq]
  exact SesqForm.existsUnique_isMinOn_energy (innerSL_hermitian (V := V)) ℓ
    one_pos innerSL_coercive hconv hcl hne

/-- **Theorem 8.3.2** of [han2009theoretical], the characterization. Let $V$ be a real Hilbert
space, let $K \subseteq V$ be convex, let $\ell \in V'$ and let $u \in K$. Then $u$ minimizes
$E(v) = \frac12 \|v\|^2 - \ell(v)$ on $K$ if and only if
$$(u, v - u) \ge \ell(v - u) \quad \text{for all } v \in K.$$
-/
theorem theorem_8_3_2_iff [CompleteSpace V] {K : Set V} (hconv : Convex ℝ K)
    (ℓ : StrongDual ℝ V) {u : V} (hu : u ∈ K) :
    IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ := by
  rw [energy_innerSL_eq]
  exact SesqForm.isMinOn_energy_iff_forall_le (innerSL_hermitian (V := V)) ℓ
    one_pos innerSL_coercive hconv hu

/-- **Theorem 8.3.2** of [han2009theoretical], the subspace case. Let $V$ be a real Hilbert space,
let $K$ be a subspace of $V$, let $\ell \in V'$ and let $u \in K$. Then $u$ minimizes
$E(v) = \frac12 \|v\|^2 - \ell(v)$ on $K$ if and only if
$$(u, v) = \ell(v) \quad \text{for all } v \in K.$$
-/
theorem theorem_8_3_2_subspace [CompleteSpace V] (K : Submodule ℝ V) (ℓ : StrongDual ℝ V) {u : V}
    (hu : u ∈ K) :
    IsMinOn (fun v => (1 / 2 : ℝ) * ‖v‖ ^ 2 - ℓ v) (K : Set V) u ↔ ∀ v ∈ K, ⟪u, v⟫_ℝ = ℓ v := by
  rw [energy_innerSL_eq]
  exact SesqForm.isMinOn_energy_iff ℓ innerSL_hermitian one_pos innerSL_coercive K hu

/-! ### Theorem 8.3.3: the energy of a symmetric $V$-elliptic form -/

variable {a : BilinForm V} {M α : ℝ}

/-- **Theorem 8.3.3** of [han2009theoretical], existence and uniqueness. Let $V$ be a real Hilbert
space, let $a$ be a bilinear form on $V$ that is bounded with constant $M$, symmetric, and
$V$-elliptic with a constant $\alpha > 0$, and let $\ell \in V'$. Let $K \subseteq V$ be
nonempty, closed and convex. Then there is exactly one $u \in K$ that minimizes the energy
$$E(v) = \frac12 a(v, v) - \ell(v)$$
on $K$.

The proof specializes `SesqForm.existsUnique_isMinOn_energy`. -/
theorem theorem_8_3_3 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K) :
    ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.existsUnique_isMinOn_energy (a := a.toCLM hM) hh ℓ hα ha hconv hcl hne

/-- **Theorem 8.3.3** of [han2009theoretical], the characterization (8.3.3). Let $V$ be a real
Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant $M$, symmetric,
and $V$-elliptic with a constant $\alpha > 0$, and let $\ell \in V'$. Let $K \subseteq V$ be
convex and $u \in K$. Then $u$ minimizes the energy $E(v) = \frac12 a(v, v) - \ell(v)$ on $K$ if
and only if $u$ solves the variational inequality
$$a(u, v - u) \ge \ell(v - u) \quad \text{for all } v \in K.$$
-/
theorem theorem_8_3_3_iff [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hconv : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff_forall_le (a := a.toCLM hM) hh ℓ hα ha hconv hu

/-- **Theorem 8.3.3** of [han2009theoretical], the characterization (8.3.4). Let $V$ be a real
Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant $M$, symmetric,
and $V$-elliptic with a constant $\alpha > 0$, and let $\ell \in V'$. Let $K$ be a subspace of
$V$ and $u \in K$. Then $u$ minimizes the energy $E(v) = \frac12 a(v, v) - \ell(v)$ on $K$ if
and only if $u$ solves the variational equation
$$a(u, v) = \ell(v) \quad \text{for all } v \in K.$$

The subspace $K$ need not be closed or finite-dimensional. -/
theorem theorem_8_3_3_subspace [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    (K : Submodule ℝ V) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) (K : Set V) u ↔ ∀ v ∈ K, a u v = ℓ v := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  exact SesqForm.isMinOn_energy_iff ℓ hh hα ha K hu

/-- Let $V$ be a real Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant
$M$, symmetric, and $V$-elliptic with a constant $\alpha > 0$, and let $\ell \in V'$. If
$a(u, v) = \ell(v)$ for all $v \in V$, then for every $v \in V$,
$$E(v) - E(u) = \frac12 \|v - u\|_a^2.$$

This is the computation in the proof of Theorem 8.3.3 of [han2009theoretical], and it is
(9.1.9). -/
theorem energy_sub_energy_eq [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V) {u : V}
    (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  have hh := (BilinForm.isSymm_iff_isHermitian hM).mp hs
  have hpos : SesqForm.IsCoerciveWith (a.toCLM hM) 0 :=
    SesqForm.IsCoerciveWith.mono (a.toCLM hM) ha hα.le
  exact SesqForm.energy_sub_energy_eq ℓ hh hpos hu v

/-! ### Theorem 8.3.4: the Lax–Milgram lemma -/

/-- **Theorem 8.3.4** of [han2009theoretical] (the Lax–Milgram lemma). Let $V$ be a real Hilbert
space, let $a$ be a bilinear form on $V$ that is bounded with constant $M$ and $V$-elliptic with
a constant $\alpha > 0$, and let $\ell \in V'$. Then the problem (8.3.5) has exactly one
solution: there is exactly one $u \in V$ with
$$a(u, v) = \ell(v) \quad \text{for all } v \in V.$$

The form need not be symmetric. The proof specializes `SesqForm.laxMilgram`. The stability
estimate is `AtkinsonHan.Chapter08.theorem_8_3_4_norm_le`. -/
theorem theorem_8_3_4 [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm.laxMilgram (a.toCLM hM) ℓ hα ha

/-- **Theorem 8.3.4** of [han2009theoretical], the stability estimate. Let $V$ be a real Hilbert
space, let $a$ be a bilinear form on $V$ that is bounded with constant $M$ and $V$-elliptic with
a constant $\alpha > 0$, and let $\ell \in V'$. If $u \in V$ satisfies $a(u, v) = \ell(v)$ for
all $v \in V$, then
$$\|u\| \le \frac{\|\ell\|}{\alpha}.$$

This is the case $U = V$ of (8.7.5). The proof specializes
`SesqForm.norm_le_of_forall_apply_eq`. -/
theorem theorem_8_3_4_norm_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {u : V} (hu : ∀ v, a u v = ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ / α :=
  SesqForm.norm_le_of_forall_apply_eq (a.toCLM hM) ℓ hα ha hu

/-- **Theorem 8.3.4** of [han2009theoretical], continuous dependence on the data. Let $V$ be a real
Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with constant $M$ and
$V$-elliptic with a constant $\alpha > 0$. If $\ell_1, \ell_2 \in V'$ and $u_1, u_2 \in V$
satisfy $a(u_i, v) = \ell_i(v)$ for all $v \in V$ and $i = 1, 2$, then
$$\|u_1 - u_2\| \le \frac{\|\ell_1 - \ell_2\|}{\alpha}.$$
-/
theorem theorem_8_3_4_norm_sub_le [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) {ℓ₁ ℓ₂ : StrongDual ℝ V} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v)
    (h₂ : ∀ v, a u₂ v = ℓ₂ v) : ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / α :=
  SesqForm.norm_sub_le_of_forall_apply_eq (a.toCLM hM) hα ha h₁ h₂

/-! ### First proof of Theorem 8.3.4: the iteration $P_\theta$ -/

/-- Let $V$ be a real Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant
$M \ge 0$ and $V$-elliptic with constant $\alpha$, and let $A$ be its operator. Then for every
$\theta \ge 0$ and $w \in V$,
$$\|w - \theta A w\|^2 \le (1 - 2\theta\alpha + \theta^2 M^2) \|w\|^2.$$

This is the estimate in the first proof of Theorem 8.3.4 of [han2009theoretical]. -/
theorem norm_sub_smul_toOperator_sq_le [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) {θ : ℝ} (hθ : 0 ≤ θ) (w : V) :
    ‖w - θ • BilinForm.toOperator a hM w‖ ^ 2 ≤ (1 - 2 * θ * α + θ ^ 2 * M ^ 2) * ‖w‖ ^ 2 := by
  have hcoer := BilinForm.isCoerciveWith_toOperator hM ha
  have hbase := ContinuousLinearMap.norm_sub_smul_apply_sq_le (𝕜 := ℝ) hcoer hθ w
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hA : ‖BilinForm.toOperator a hM‖ ≤ M := BilinForm.norm_toOperator_le hM0 hM
  have hA0 : 0 ≤ ‖BilinForm.toOperator a hM‖ := norm_nonneg _
  have hsq : ‖BilinForm.toOperator a hM‖ ^ 2 ≤ M ^ 2 := by nlinarith
  nlinarith [sq_nonneg θ, hsq]

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$ and $V$-elliptic with constant $\alpha$. Then its operator $A$ is strongly monotone
(5.1.8) with constant $\alpha$: $(Au - Av, u - v) \ge \alpha \|u - v\|^2$ for all $u, v$.

This is the hypothesis of the theory of Section 5.1 (`zarantonello`, `contractingWith_damped`). -/
theorem stronglyMonotone_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) : IsStronglyMonotoneWith ℝ (BilinForm.toOperator a hM) α := by
  intro x y
  rw [← map_sub]
  exact BilinForm.isCoerciveWith_toOperator hM ha (x - y)

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M \ge 0$. Then its operator $A$ is Lipschitz continuous with constant $M$, the
constant of (9.4.3). -/
theorem lipschitzWith_toOperator [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) :
    LipschitzWith (Real.toNNReal M) (BilinForm.toOperator a hM) := by
  refine (BilinForm.toOperator a hM).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
  exact BilinForm.norm_toOperator_le hM0 hM

/-- Let $V$ be a real Hilbert space, let $a$ be a bilinear form on $V$ that is bounded with constant
$M > 0$ and $V$-elliptic with constant $\alpha$, let $A$ be its operator, let $\ell \in V'$ and
let $f$ be the Riesz representative of $\ell$. If $0 < \theta < 2\alpha/M^2$, then the map
$$P_\theta u = u - \theta (Au - f)$$
is a contraction with constant $\sqrt{1 - 2\theta\alpha + \theta^2 M^2}$.

The condition on $\theta$ forces $\alpha > 0$. This is the first proof of Theorem 8.3.4 of
[han2009theoretical]: the Banach fixed-point theorem gives the solution of (8.3.5). -/
theorem contractingWith_damped_sub_smul [CompleteSpace V] (hM0 : 0 < M) (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * α / M ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * α + θ ^ 2 * M ^ 2)))
      (fun u => u - θ • (BilinForm.toOperator a hM u - SesqForm.rieszRep ℓ)) :=
  contractingWith_damped (𝕜 := ℝ) hM0 (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0.le hM) (SesqForm.rieszRep ℓ) hθ hθ'

/-! ### Second proof of Theorem 8.3.4: closed range and dense range -/

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$ and $V$-elliptic with constant $\alpha$. Then its operator $A$ satisfies
$\alpha \|u\| \le \|Au\|$ for every $u \in V$.

This is the stability estimate (8.2.2) on which the second proof of Theorem 8.3.4 of
[han2009theoretical] rests. -/
theorem norm_le_norm_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M)
    (ha : a.IsEllipticWith α) (u : V) : α * ‖u‖ ≤ ‖BilinForm.toOperator a hM u‖ := by
  rw [SesqForm.toOperator_apply_eq_rieszRep, SesqForm.norm_rieszRep]
  exact SesqForm.IsCoerciveWith.norm_le_norm_apply (a.toCLM hM) ha u

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$ and $V$-elliptic with a constant $\alpha > 0$. Then the range of its operator $A$
is closed.

The proof uses `AtkinsonHan.Chapter08.norm_le_norm_toOperator` and Theorem 8.2.4. -/
theorem isClosed_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    IsClosed (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V) : Set V) :=
  ContinuousLinearMap.isClosed_range_of_le_norm _ hα (norm_le_norm_toOperator hM ha)

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$ and $V$-elliptic with a constant $\alpha > 0$. Then the orthogonal complement of
the range of its operator $A$ is $\{0\}$.

A vector $w$ orthogonal to the range is orthogonal to $Aw$, so $\alpha \|w\|^2 \le (Aw, w) = 0$. -/
theorem orthogonal_range_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) :
    (LinearMap.range (BilinForm.toOperator a hM : V →ₗ[ℝ] V))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hz : ⟪BilinForm.toOperator a hM v, v⟫_ℝ = 0 := hv _ ⟨v, rfl⟩
  rw [BilinForm.inner_toOperator] at hz
  have h1 : α * ‖v‖ ^ 2 ≤ 0 := (ha v).trans_eq hz
  have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _)))

/-- Let $V$ be a real Hilbert space, and let $a$ be a bilinear form on $V$ that is bounded with
constant $M$ and $V$-elliptic with a constant $\alpha > 0$. Then its operator $A : V \to V$ is a
bijection.

This is the second proof of Theorem 8.3.4 of [han2009theoretical]: $A$ is bounded below, so its
range is closed, and the range is dense, so $A$ is a bijection (Theorem 8.2.1). -/
theorem bijective_toOperator [CompleteSpace V] (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) : Function.Bijective (BilinForm.toOperator a hM) :=
  ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot _ hα
    (norm_le_norm_toOperator hM ha) (orthogonal_range_toOperator hM hα ha)

/-! ### Exercise 8.3.1 -/

/-- **Exercise 8.3.1** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $a$ be a
bilinear form on $V$ that is bounded with constant $M \ge 0$ and $V$-elliptic with a constant
$\alpha > 0$, and let $\ell \in V'$. Then there is exactly one $u \in V$ with
$a(u, v) = \ell(v)$ for all $v \in V$.

The proof derives the Lax–Milgram lemma from the theory of strongly monotone Lipschitz operators
of Section 5.1, the backbone's `zarantonello`, applied to the operator $A$ of $a$ with constants
$\alpha$ and $M$ and right side the Riesz representative of $\ell$. -/
theorem exercise_8_3_1 [CompleteSpace V] (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v := by
  obtain ⟨u, hu, huniq⟩ := zarantonello (𝕜 := ℝ) hα (stronglyMonotone_toOperator hM ha)
    (lipschitzWith_toOperator hM0 hM) (SesqForm.rieszRep ℓ)
  refine ⟨u, (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).mp hu, fun y hy => ?_⟩
  exact huniq y ((BilinForm.toOperator_eq_rieszRep_iff hM ℓ y).mpr hy)

/-! ### Example 8.3.5: the model Dirichlet problem -/

/-- **Example 8.3.5** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and
contained in the ball $B(0, R)$ with $R \ge 0$. For every
$\ell \in H^{-1}(\Omega) = H^1_0(\Omega)'$ there is exactly one $u \in H^1_0(\Omega)$ with
$$\int_\Omega \nabla u \cdot \nabla v \, dx = \ell(v) \quad \text{for all } v \in
  H^1_0(\Omega).$$
This $u$ is the unique weak solution of the boundary value problem (8.2.3), $-\Delta u = f$ in
$\Omega$ and $u = 0$ on $\partial\Omega$.

**Generalization.** The source assumes that $\Omega$ has a Lipschitz boundary. The example here
holds for every bounded open $\Omega$.

The form $a(u, v) = \int_\Omega \nabla u \cdot \nabla v \, dx = \sum_i \int_\Omega \partial_i u
\, \partial_i v \, dx$ is `AtkinsonHan.BilinForm.ofCLM (AtkinsonHan.Chapter08.modelOperator Ω)`,
the Dirichlet form of Example 8.2.6 on $V = H^1_0(\Omega)$, which is
`SobolevEuclideanZero (d + 1) 1 2 Ω`. It is bounded with $M = 1$
(`Elliptic.dirichletForm_isBoundedWith`) and $V$-elliptic with $\alpha = (1 + (2R)^2)^{-1}$ by
the Poincaré inequality (`Elliptic.dirichletForm_restrict_isCoerciveWith`), so
`AtkinsonHan.Chapter08.theorem_8_3_4` applies. A datum $f \in L^2(\Omega)$ enters as
$\ell(v) = \int_\Omega f v \, dx$, that is `(Elliptic.load Ω f).comp V.subtypeL`. The spaces
$H^1_0(\Omega)$ and $H^{-1}(\Omega)$ of Chapter 7 (`AtkinsonHan.Chapter07.definition_7_2_9`,
`AtkinsonHan.Chapter07.definition_7_2_12_hMinusOne`) are the same spaces in the tensor form of
$W^{1,2}(\Omega)$; see `AtkinsonHan.Chapter08.modelOperator`. -/
theorem example_8_3_5 {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (ℓ : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 2 Ω)) :
    ∃! u : SobolevEuclideanZero (d + 1) 1 2 Ω, ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x = ℓ v := by
  have hcoer := Elliptic.dirichletForm_restrict_isCoerciveWith Ω hR hΩ
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have hM : (BilinForm.ofCLM (modelOperator Ω)).IsBoundedWith 1 := fun u v ↦ by
    rw [BilinForm.ofCLM_apply, modelOperator_apply, one_mul, ← Real.norm_eq_abs]
    have h := Elliptic.dirichletForm_isBoundedWith Ω u v
    rwa [one_mul] at h
  have hα : (BilinForm.ofCLM (modelOperator Ω)).IsEllipticWith (1 + (2 * R) ^ 2)⁻¹ := fun v ↦ by
    rw [BilinForm.ofCLM_apply, modelOperator_apply]
    exact hcoer v
  have key := theorem_8_3_4 hM hpos hα ℓ
  have e : ∀ u v : SobolevEuclideanZero (d + 1) 1 2 Ω, BilinForm.ofCLM (modelOperator Ω) u v
      = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        ∑ i, SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 2 Ω)
          (MultiIndexLE.single i) x
          * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 2 Ω)
            (MultiIndexLE.single i) x := fun u v ↦
    Elliptic.dirichletForm_apply Ω u v
  simp only [e] at key
  exact key

end Chapter08

end AtkinsonHan
