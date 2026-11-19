/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Variational.Forms
import Numlib.Variational.Galerkin
import NumlibSurface.AtkinsonHan.Chapter08.Section07

/-!
# Atkinson and Han, Section 9.2: The Petrov–Galerkin method

This module formalizes Section 9.2 of [han2009theoretical]. Let $U$ and $V$ be real inner product
spaces, $a : U \times V \to \mathbb{R}$ a bilinear form with $|a(u, v)| \le M \|u\| \|v\|$, and
$\ell \in V'$. The Petrov–Galerkin method (9.2.5) chooses a trial space $U_N \subseteq U$ and a test
space $V_N \subseteq V$ of the same finite dimension, and asks for $u_N \in U_N$ with
$a(u_N, v_N) = \ell(v_N)$ for all $v_N \in V_N$. Under the discrete inf–sup condition (9.2.6) with
constant $\alpha_N > 0$, Babuška's theorem (Theorem 9.2.1) gives a unique $u_N$ and the error bound
(9.2.7) $$\|u - u_N\| \le \Big(1 + \frac{M}{\alpha_N}\Big) \inf_{w_N \in U_N} \|u - w_N\|.$$ Remark
9.2.2 improves the constant to $M / \alpha_N$ (Xu and Zikatanov), and Corollary 9.2.3 gives
convergence under the uniform inf–sup condition (9.2.13). The proofs specialize
`IsPetrovGalerkinSolution` of `Numlib.Variational.Galerkin`.

## Main definitions

* Equation (9.2.5), `AtkinsonHan.PetrovGalerkinProblem`: $u_N \in U_N$ and $a(u_N, v_N) = \ell(v_N)$
  for all $v_N \in V_N$.
* Equation (9.2.6), `AtkinsonHan.DiscreteInfSup`: $\alpha_N \|u_N\| \le \sup_{0 \ne v_N \in V_N}
  a(u_N, v_N) / \|v_N\|$ for all $u_N \in U_N$.
* Equation (9.2.13), `AtkinsonHan.InfSupCondition`: the discrete inf–sup condition for every $N$
  with one constant $\alpha_0$.
* Equation (9.2.14), `AtkinsonHan.infSupValue`: the number $\inf_{0 \ne u_N} \sup_{0 \ne v_N} a(u_N,
  v_N) / (\|u_N\| \|v_N\|)$.

## Main results

* Equation (9.2.8), `AtkinsonHan.Chapter09.petrovGalerkin_orthogonality`: $a(u - u_N, v_N) = 0$ for
  all $v_N \in V_N$.
* Theorem 9.2.1, `AtkinsonHan.Chapter09.theorem_9_2_1_existsUnique`: the Petrov–Galerkin problem has
  a unique solution.
* Theorem 9.2.1, `AtkinsonHan.Chapter09.theorem_9_2_1_le`:
  $\|u - u_N\| \le (1 + M / \alpha_N) \|u - w_N\|$ for every $w_N \in U_N$.
* Theorem 9.2.1, `AtkinsonHan.Chapter09.theorem_9_2_1`: the quasi-optimal error bound (9.2.7).
* Remark 9.2.2, `AtkinsonHan.Chapter09.remark_9_2_2`: for $U_N \ne \{0\}$, the error bound holds
  with the constant $M / \alpha_N$.
* Corollary 9.2.3, `AtkinsonHan.Chapter09.corollary_9_2_3`: under a uniform inf–sup condition and
  for increasing trial spaces with dense union, $u_N \to u$.
* Equations (9.2.13) and (9.2.14), `AtkinsonHan.Chapter09.discreteInfSup_iff_le_infSupValue`: the
  discrete inf–sup condition with constant $\alpha_0$ holds if and only if $\alpha_0$ is at most the
  value (9.2.14).

## Implementation notes

* The form is `AtkinsonHan.BilinForm₂ U V` with the predicate
  `AtkinsonHan.BilinForm₂.IsBoundedWith`. The spaces $U$ and $V$ need not be complete.
* The source writes the supremum in (9.2.6) without absolute values, and
  `AtkinsonHan.DiscreteInfSup` follows it. By `AtkinsonHan.Chapter09.iSup_div_eq_norm_comp`, this
  supremum is the norm of the functional $a(u_N, \cdot)$ restricted to $V_N$, as in Section 8.7. So
  the condition is equivalent to the backbone condition `IsPetrovGalerkinSolution.DiscreteInfSup`.
* The suprema and the infima are `iSup` and `iInf` on $\mathbb{R}$, which take the value $0$ on an
  empty or unbounded set.

## Deviations from the source

* **Theorem 9.2.1** (scope). The discrete existence result uses the discrete
  inf–sup bound and equal dimensions. The estimates assume a solution of the
  continuous problem directly. The source obtains that solution first from its
  continuous inf–sup and nondegeneracy hypotheses.
* **Remark 9.2.2** (correction). The bound $\|u - u_N\| \le (M / \alpha_N) \inf_{w_N \in U_N} \|u -
  w_N\|$ needs $U_N \ne \{0\}$, which the source does not state. See
  `AtkinsonHan.Chapter09.remark_9_2_2`.
-/

open Filter Topology
open scoped InnerProductSpace

namespace AtkinsonHan

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- **Equation (9.2.5)** of [han2009theoretical]. Let $a : U \times V \to \mathbb{R}$ be bilinear,
let $\ell \in V'$, and let $U_N \subseteq U$ and $V_N \subseteq V$ be subspaces. An element
$u_N \in U$ **solves the Petrov–Galerkin problem** if $u_N \in U_N$ and $$a(u_N, v_N) =
\ell(v_N) \quad \text{for all } v_N \in V_N.$$

The trial space $U_N$ and the test space $V_N$ can be different. -/
def PetrovGalerkinProblem (a : BilinForm₂ U V) (ℓ : StrongDual ℝ V) (UN : Submodule ℝ U)
    (VN : Submodule ℝ V) (uN : U) : Prop :=
  uN ∈ UN ∧ ∀ v ∈ VN, a uN v = ℓ v

/-- **Equation (9.2.6)** of [han2009theoretical]. The form $a$ satisfies the **discrete inf–sup
condition** on $U_N \times V_N$ with constant $\alpha_N$ if $$\alpha_N \|u_N\| \le \sup_{0 \ne
v_N \in V_N} \frac{a(u_N, v_N)}{\|v_N\|} \quad \text{for all } u_N \in U_N.$$

The supremum is `iSup` on $\mathbb{R}$. It is $0$ when $V_N = \{0\}$ or when the quotients are
unbounded above; for a bounded form they are bounded. -/
def DiscreteInfSup (a : BilinForm₂ U V) (UN : Submodule ℝ U) (VN : Submodule ℝ V) (αN : ℝ) :
    Prop :=
  ∀ uN ∈ UN, αN * ‖uN‖ ≤ ⨆ vN : {v : VN // v ≠ 0}, a uN ((vN : VN) : V) / ‖((vN : VN) : V)‖

/-- **Equation (9.2.13)** of [han2009theoretical]. For sequences of subspaces $U_N \subseteq U$ and
$V_N \subseteq V$, the form $a$ satisfies the **uniform inf–sup condition** (Babuška–Brezzi
condition) with constant $\alpha_0$ if, for every $N$, it satisfies the discrete inf–sup
condition (9.2.6) on $U_N \times V_N$ with the constant $\alpha_0$. -/
def InfSupCondition (a : BilinForm₂ U V) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V)
    (α₀ : ℝ) : Prop :=
  ∀ N, DiscreteInfSup a (UN N) (VN N) α₀

/-- **Equation (9.2.14)** of [han2009theoretical]. The **inf–sup value** of $a$ on $U_N \times V_N$
is $$\inf_{0 \ne u_N \in U_N} \sup_{0 \ne v_N \in V_N} \frac{a(u_N, v_N)}{\|u_N\| \|v_N\|}.$$

The infimum and the supremum are `iInf` and `iSup` on $\mathbb{R}$; in particular the value is
$0$ when $U_N = \{0\}$. -/
noncomputable def infSupValue (a : BilinForm₂ U V) (UN : Submodule ℝ U) (VN : Submodule ℝ V) :
    ℝ :=
  ⨅ uN : {u : UN // u ≠ 0}, ⨆ vN : {v : VN // v ≠ 0},
    a ((uN : UN) : U) ((vN : VN) : V) / (‖((uN : UN) : U)‖ * ‖((vN : VN) : V)‖)

/-- If $a$ satisfies the discrete inf–sup condition on $U_N \times V_N$ with constant $\alpha_N$ and
$\alpha_0 \le \alpha_N$, then it satisfies it with constant $\alpha_0$. -/
theorem DiscreteInfSup.mono {a : BilinForm₂ U V} {UN : Submodule ℝ U} {VN : Submodule ℝ V}
    {αN α₀ : ℝ} (h : DiscreteInfSup a UN VN αN) (hα : α₀ ≤ αN) : DiscreteInfSup a UN VN α₀ :=
  fun w hw => le_trans (mul_le_mul_of_nonneg_right hα (norm_nonneg _)) (h w hw)

/-- Equation (9.2.13). If, for every $i$, the form $a$ satisfies the discrete inf–sup condition on
$U_i \times V_i$ with a constant $\alpha_i \ge \alpha_0$, then it satisfies the uniform inf–sup
condition with constant $\alpha_0$.

This reduces the varying constants $\alpha_N \ge \alpha_0$ of the source to
`AtkinsonHan.InfSupCondition`. -/
theorem infSupCondition_of_forall_le {a : BilinForm₂ U V} {UN : ℕ → Submodule ℝ U}
    {VN : ℕ → Submodule ℝ V} {αN : ℕ → ℝ} {α₀ : ℝ}
    (h : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i)) (hα : ∀ i, α₀ ≤ αN i) :
    InfSupCondition a UN VN α₀ := fun i => (h i).mono (hα i)

namespace Chapter09

variable {a : BilinForm₂ U V} {ℓ : StrongDual ℝ V} {M αN α₀ : ℝ} {UN : Submodule ℝ U}
  {VN : Submodule ℝ V} {u uN : U}

/-- Let $a$ be bounded with constant $M$. Then $u_N$ solves the Petrov–Galerkin problem
`AtkinsonHan.PetrovGalerkinProblem` if and only if it satisfies the backbone predicate
`IsPetrovGalerkinSolution` for the bundled form `AtkinsonHan.BilinForm₂.toCLM a hM`. -/
theorem petrovGalerkinProblem_iff (hM : a.IsBoundedWith M) :
    PetrovGalerkinProblem a ℓ UN VN uN ↔
      IsPetrovGalerkinSolution (a.toCLM hM) ℓ UN VN uN := Iff.rfl

/-- Let $a$ be bounded with constant $M$, let $w \in U$, and let $V_N \subseteq V$ be a subspace.
Then the supremum of (9.2.6) is the norm of the functional $a(w, \cdot)$ restricted to $V_N$:
$$\sup_{0 \ne v_N \in V_N} \frac{a(w, v_N)}{\|v_N\|} = \big\| a(w, \cdot)|_{V_N} \big\|.$$

The supremum has no absolute values, as in the source; it equals the norm because $v_N$ and
$-v_N$ both lie in $V_N$. -/
theorem iSup_div_eq_norm_comp (hM : a.IsBoundedWith M) (w : U) (VN : Submodule ℝ V) :
    (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖)
      = ‖(a.toCLM hM w).comp VN.subtypeL‖ :=
  ((a.toCLM hM w).comp VN.subtypeL).iSup_apply_div_eq_opNorm

/-- Let $a$ be bounded with constant $M$. Then the discrete inf–sup condition (9.2.6) with constant
$\alpha_N$ is equivalent to the backbone condition `IsPetrovGalerkinSolution.DiscreteInfSup` for
the bundled form. -/
theorem discreteInfSup_iff (hM : a.IsBoundedWith M) :
    DiscreteInfSup a UN VN αN ↔
      IsPetrovGalerkinSolution.DiscreteInfSup (a.toCLM hM) UN VN αN := by
  refine forall_congr' fun w => forall_congr' fun _ => ?_
  rw [iSup_div_eq_norm_comp hM w VN]

/-- **Equation (9.2.8)** of [han2009theoretical] (Galerkin orthogonality). Let $u \in U$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$, and let $u_N$ solve the Petrov–Galerkin problem (9.2.5).
Then $a(u - u_N, v_N) = 0$ for all $v_N \in V_N$. -/
theorem petrovGalerkin_orthogonality (hu : ∀ v, a u v = ℓ v)
    (huN : PetrovGalerkinProblem a ℓ UN VN uN) {v : V} (hv : v ∈ VN) : a (u - uN) v = 0 := by
  rw [map_sub, LinearMap.sub_apply, hu v, huN.2 v hv, sub_self]

/-- **Theorem 9.2.1** of [han2009theoretical] (Babuška), existence and uniqueness. Let $a$ be
bounded with constant $M$, let $U_N \subseteq U$ and $V_N \subseteq V$ be finite-dimensional
with $\dim U_N = \dim V_N$, and let $a$ satisfy the discrete inf–sup condition (9.2.6) with a
constant $\alpha_N > 0$. Then for every $\ell \in V'$ the Petrov–Galerkin problem (9.2.5) has
exactly one solution $u_N$.

The proof does not use the completeness of $U$ and $V$, nor the conditions (9.2.3) and (9.2.4)
on $a$ over the whole spaces.

**Reading.** Discrete-only existence hypotheses isolate the equal-dimensional finite problem.
-/
theorem theorem_9_2_1_existsUnique [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN]
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (ℓ : StrongDual ℝ V) :
    ∃! uN, PetrovGalerkinProblem a ℓ UN VN uN :=
  IsPetrovGalerkinSolution.existsUnique (a := a.toCLM hM) (ℓ := ℓ) hdim hαN
    ((discreteInfSup_iff hM).mp hinfsup)

/-- **Theorem 9.2.1** of [han2009theoretical] (Babuška), pointwise form of (9.2.7). Let $a$ be
bounded with constant $M \ge 0$, let $U_N \subseteq U$ and $V_N \subseteq V$ be
finite-dimensional with $\dim U_N = \dim V_N$, and let $a$ satisfy the discrete inf–sup
condition (9.2.6) with a constant $\alpha_N > 0$. Let $u_N$ solve the Petrov–Galerkin problem
(9.2.5), and let $u \in U$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$. Then $$\|u - u_N\| \le
\Big(1 + \frac{M}{\alpha_N}\Big) \|u - w_N\| \quad \text{for every } w_N \in U_N.$$

**Reading.** Pointwise estimate takes exact solution as a hypothesis.
-/
theorem theorem_9_2_1_le [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (huN : PetrovGalerkinProblem a ℓ UN VN uN)
    (hu : ∀ v, a u v = ℓ v) {w : U} (hw : w ∈ UN) :
    ‖u - uN‖ ≤ (1 + M / αN) * ‖u - w‖ :=
  IsPetrovGalerkinSolution.norm_sub_le hdim hαN hM0 (a.isBoundedWith_toCLM hM)
    ((discreteInfSup_iff hM).mp hinfsup) huN hu hw

/-- **Theorem 9.2.1** of [han2009theoretical] (Babuška), the error bound (9.2.7). Let $a$ be bounded
with constant $M \ge 0$, let $U_N \subseteq U$ and $V_N \subseteq V$ be finite-dimensional with
$\dim U_N = \dim V_N$, and let $a$ satisfy the discrete inf–sup condition (9.2.6) with a
constant $\alpha_N > 0$. Let $u_N$ solve the Petrov–Galerkin problem (9.2.5), and let $u \in U$
satisfy $a(u, v) = \ell(v)$ for all $v \in V$. Then $$\|u - u_N\| \le \Big(1 +
\frac{M}{\alpha_N}\Big) \inf_{w_N \in U_N} \|u - w_N\|.$$

The unique solvability of (9.2.5) is `AtkinsonHan.Chapter09.theorem_9_2_1_existsUnique`, and
`AtkinsonHan.Chapter09.theorem_9_2_1_le` is the bound for a single $w_N \in U_N$.

**Reading.** Same error constant under the supplied continuous solution hypothesis.
-/
theorem theorem_9_2_1 [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (huN : PetrovGalerkinProblem a ℓ UN VN uN)
    (hu : ∀ v, a u v = ℓ v) : ‖u - uN‖ ≤ (1 + M / αN) * ⨅ wN : UN, ‖u - (wN : U)‖ := by
  have hC : 0 < 1 + M / αN := by
    have : 0 ≤ M / αN := div_nonneg hM0 hαN.le
    linarith
  have hkey : ∀ w : UN, ‖u - uN‖ / (1 + M / αN) ≤ ‖u - (w : U)‖ := fun w => by
    rw [div_le_iff₀ hC, mul_comm]
    exact theorem_9_2_1_le hM0 hM hdim hαN hinfsup huN hu w.2
  have hle := le_ciInf hkey
  rw [div_le_iff₀ hC] at hle
  linarith [hle]

/-- The remark after Corollary 9.2.3. For $M \ge 0$ and every real $\alpha_N$, $$1 +
\frac{M}{\alpha_N} \le (1 + M) \max\{1, \alpha_N^{-1}\}.$$ So the Petrov–Galerkin solutions
converge as soon as $\max\{1, \alpha_N^{-1}\} \inf_{w_N \in U_N} \|u - w_N\| \to 0$.

For $\alpha_N = 0$ the inequality uses the Lean values $M / 0 = 0$ and $0^{-1} = 0$. -/
theorem one_add_div_le (hM0 : 0 ≤ M) :
    1 + M / αN ≤ (1 + M) * max 1 αN⁻¹ := by
  have h1 : (1 : ℝ) ≤ max 1 αN⁻¹ := le_max_left _ _
  have h2 : αN⁻¹ ≤ max 1 αN⁻¹ := le_max_right _ _
  have h3 : M / αN = M * αN⁻¹ := div_eq_mul_inv M αN
  nlinarith

/-- **Corollary 9.2.3** of [han2009theoretical]. Let $a$ be bounded with constant $M \ge 0$, and let
$\alpha_0 > 0$. For $i \in \mathbb{N}$ let $U_i \subseteq U$ and $V_i \subseteq V$ be
finite-dimensional with $\dim U_i = \dim V_i$, and let $a$ satisfy the discrete inf–sup
condition (9.2.6) on $U_i \times V_i$ with a constant $\alpha_i \ge \alpha_0$. Let
$U_0 \subseteq U_1 \subseteq \cdots$ have dense union in $U$. Let $u \in U$ satisfy
$a(u, v) = \ell(v)$ for all $v \in V$, and let $u_i$ solve the Petrov–Galerkin problem (9.2.5)
on $U_i \times V_i$. Then $$\|u - u_i\| \to 0 \quad \text{as } i \to \infty.$$

The hypotheses are (9.2.11), and the conclusion is (9.2.12). The test spaces $V_i$ need not
increase. -/
theorem corollary_9_2_3 (a : BilinForm₂ U V) (ℓ : StrongDual ℝ V) {M α₀ : ℝ} (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hα₀ : 0 < α₀) (UN : ℕ → Submodule ℝ U) (VN : ℕ → Submodule ℝ V)
    [∀ i, FiniteDimensional ℝ (UN i)] [∀ i, FiniteDimensional ℝ (VN i)]
    (hdim : ∀ i, Module.finrank ℝ (UN i) = Module.finrank ℝ (VN i)) (αN : ℕ → ℝ)
    (hαN : ∀ i, α₀ ≤ αN i) (hinfsup : ∀ i, DiscreteInfSup a (UN i) (VN i) (αN i))
    (hmono : Monotone UN) (hdense : Dense (⋃ i, (UN i : Set U))) {u : U}
    (hu : ∀ v, a u v = ℓ v) (uN : ℕ → U)
    (huN : ∀ i, PetrovGalerkinProblem a ℓ (UN i) (VN i) (uN i)) :
    Tendsto (fun i => ‖u - uN i‖) atTop (𝓝 0) := by
  have huniform : InfSupCondition a UN VN α₀ := infSupCondition_of_forall_le hinfsup hαN
  have hunif : ∀ i, IsPetrovGalerkinSolution.DiscreteInfSup (a.toCLM hM) (UN i) (VN i) α₀ :=
    fun i => (discreteInfSup_iff hM).mp (huniform i)
  have h := IsPetrovGalerkinSolution.tendsto (a := a.toCLM hM) (ℓ := ℓ) hdim hα₀ hM0
    (a.isBoundedWith_toCLM hM) hunif hmono hdense huN hu
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  simpa only [norm_sub_rev] using h

/-! ### The equivalence of (9.2.13) and (9.2.14) -/

private theorem iSup_div_mul_eq (a : BilinForm₂ U V) (VN : Submodule ℝ V) {w : U}
    (hw : w ≠ 0) :
    (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / (‖w‖ * ‖((vN : VN) : V)‖))
      = (⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖) / ‖w‖ := by
  have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rw [div_eq_mul_inv, Real.iSup_mul_of_nonneg (by positivity)]
  refine iSup_congr fun v => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_comm ‖w‖⁻¹, ← mul_assoc]

/-- Equations (9.2.13) and (9.2.14). Let $a$ be bounded with constant $M$, and let $U_N \ne \{0\}$.
Then $a$ satisfies the discrete inf–sup condition (9.2.6) on $U_N \times V_N$ with constant
$\alpha_0$ if and only if $\alpha_0$ is at most the inf–sup value (9.2.14) of $U_N \times V_N$.

Applied to each $N$, this says that the uniform inf–sup condition (9.2.13) with constant
$\alpha_0$ holds if and only if all the values (9.2.14) are at least $\alpha_0$.

**Reading.** Makes the nontrivial trial space and bounded form assumptions explicit.
-/
theorem discreteInfSup_iff_le_infSupValue (hM : a.IsBoundedWith M) (hUN : UN ≠ ⊥) :
    DiscreteInfSup a UN VN α₀ ↔ α₀ ≤ infSupValue a UN VN := by
  have hnn : ∀ w : U, 0 ≤ ⨆ vN : {v : VN // v ≠ 0}, a w ((vN : VN) : V) / ‖((vN : VN) : V)‖ :=
    fun w => by
      rw [iSup_div_eq_norm_comp hM w VN]
      exact norm_nonneg ((a.toCLM hM w).comp VN.subtypeL)
  have hne : Nonempty {x : UN // x ≠ 0} := by
    obtain ⟨w, hw, hw0⟩ := UN.ne_bot_iff.mp hUN
    exact ⟨⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  have hbdd : BddBelow (Set.range fun uN : {x : UN // x ≠ 0} =>
      ⨆ vN : {v : VN // v ≠ 0}, a ((uN : UN) : U) ((vN : VN) : V) /
        (‖((uN : UN) : U)‖ * ‖((vN : VN) : V)‖)) := by
    refine ⟨0, Set.forall_mem_range.2 fun x => ?_⟩
    have hx : ((x : UN) : U) ≠ 0 := fun h => x.2 (Subtype.ext h)
    rw [iSup_div_mul_eq a VN hx]
    exact div_nonneg (hnn _) (norm_nonneg _)
  rw [infSupValue, le_ciInf_iff hbdd]
  constructor
  · intro h x
    have hx : ((x : UN) : U) ≠ 0 := fun hz => x.2 (Subtype.ext hz)
    rw [iSup_div_mul_eq a VN hx, le_div_iff₀ (norm_pos_iff.mpr hx)]
    exact h _ (x : UN).2
  · intro h w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hx := h ⟨⟨w, hw⟩, fun hz => hw0 (congrArg Subtype.val hz)⟩
      rw [iSup_div_mul_eq a VN hw0, le_div_iff₀ (norm_pos_iff.mpr hw0)] at hx
      exact hx

/-- **Remark 9.2.2** of [han2009theoretical], the sharpening (9.2.10) of (9.2.7) by Xu and
Zikatanov. Let $a$ be bounded with constant $M \ge 0$, let $U_N \subseteq U$ and
$V_N \subseteq V$ be finite-dimensional with $\dim U_N = \dim V_N$ and $U_N \ne \{0\}$, and let
$a$ satisfy the discrete inf–sup condition (9.2.6) with a constant $\alpha_N > 0$. Let $u_N$
solve the Petrov–Galerkin problem (9.2.5), and let $u \in U$ satisfy $a(u, v) = \ell(v)$ for all
$v \in V$. Then $$\|u - u_N\| \le \frac{M}{\alpha_N} \inf_{w_N \in U_N} \|u - w_N\|.$$

**Correction.** The source does not require $U_N \ne \{0\}$, but the bound needs it. For
$U_N = \{0\}$ the Petrov–Galerkin map $P_N : u \mapsto u_N$ is $0$, so $\|I - P_N\| = 1$ differs
from $\|P_N\| = 0$, and every other hypothesis can hold while the bound fails: for $a = 0$,
$M = 0$ and $\alpha_N = 1$ the bound reads $\|u\| \le 0$. The bound (9.2.7) of Theorem 9.2.1
still holds in this case.

The proof regards $P_N$ as a bounded idempotent operator and applies Kato's lemma
`AtkinsonHan.Chapter09.kato` to it. It specializes
`IsPetrovGalerkinSolution.norm_sub_le_div_mul_infDist`. -/
theorem remark_9_2_2 [FiniteDimensional ℝ UN] [FiniteDimensional ℝ VN] (hM0 : 0 ≤ M)
    (hM : a.IsBoundedWith M) (hdim : Module.finrank ℝ UN = Module.finrank ℝ VN) (hαN : 0 < αN)
    (hinfsup : DiscreteInfSup a UN VN αN) (hUN : UN ≠ ⊥)
    (huN : PetrovGalerkinProblem a ℓ UN VN uN) (hu : ∀ v, a u v = ℓ v) :
    ‖u - uN‖ ≤ M / αN * ⨅ wN : UN, ‖u - (wN : U)‖ := by
  have hdist : Metric.infDist u (UN : Set U) = ⨅ wN : UN, ‖u - (wN : U)‖ := by
    rw [Metric.infDist_eq_iInf]
    exact iInf_congr fun w => dist_eq_norm u (w : U)
  have h := IsPetrovGalerkinSolution.norm_sub_le_div_mul_infDist (a := a.toCLM hM) (ℓ := ℓ)
    hdim hαN ((discreteInfSup_iff hM).mp hinfsup) hUN hM0 (a.isBoundedWith_toCLM hM) huN hu
  rwa [hdist] at h

/-! ### Kato's lemma -/

/-- **Kato's lemma**, the analytic tool of Remark 9.2.2. Let $H$ be a real Hilbert space, and let
$P$ be a bounded linear operator on $H$ with $P^2 = P$, $P \ne 0$ and $P \ne I$. Then
$\|P\| = \|I - P\|$. -/
theorem kato {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : H →L[ℝ] H} (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖P‖ = ‖1 - P‖ :=
  (ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq hP h0 h1).symm

end Chapter09

end AtkinsonHan
