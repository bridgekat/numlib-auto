/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Numlib.Algebra.LinearRecurrence
import Numlib.RingTheory.Polynomial.SchurCohn

/-!
# Linear recurrences: the root condition and bounded solutions

A linear recurrence of order $k$ with coefficients $\alpha_0, \dots, \alpha_{k-1}$ and source
$(\varphi_n)$ is the equation
$$u_{n+k} = \sum_{i=0}^{k-1} \alpha_i u_{n+i} + \varphi_{n+k} \qquad (n \ge 0),$$
and its characteristic polynomial is $\Pi(X) = X^k - \sum_{i<k} \alpha_i X^i$. A polynomial
satisfies the **root condition** if all its roots lie in the closed unit disc and the roots of
modulus one are simple. This file proves the analytic part of the theory of linear recurrences with
constant coefficients, as [quarteroni2000numerical], §11.4 and §11.6, present it for the analysis of
multistep methods. The main result is Lemma 11.3 of [quarteroni2000numerical]: if $k > 0$, there is
$M > 0$ with
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for every
  solution } u \text{ and every } n$$
if and only if $\Pi$ satisfies the root condition. The file also shows that all solutions of the
homogeneous recurrence ($\varphi = 0$) are bounded if and only if $\Pi$ satisfies the root
condition, and that they all tend to zero if and only if all roots of $\Pi$ lie in the open unit
disc.

The algebraic part is in `Numlib.Algebra.LinearRecurrence`: Mathlib's `LinearRecurrence`, the
Kronecker fundamental solutions $\psi_j$ (the homogeneous solutions with $\psi_j(i) = \delta_{ij}$
for $i < k$), the discrete Duhamel formula, and the fundamental system of binomial sequences
$\binom{n}{s} r^{n-s}$ for the roots $r$ of $\Pi$ and $s$ less than the multiplicity of $r$. This
file adds the bounds.

## Main definitions

* `Polynomial.SatisfiesRootCondition`: every root lies in the closed unit disc, and the roots of
  modulus one are simple (Definition 11.10 of [quarteroni2000numerical]).
* `Polynomial.SatisfiesStrongRootCondition`: the root condition holds, and $1$ is the only possible
  root of modulus one (Definition 11.11 of [quarteroni2000numerical]).

## Main results

* `Polynomial.satisfiesRootCondition_iff_derivative`: the root condition with simplicity written as
  $P'(r) \neq 0$, as in [quarteroni2000numerical].
* `Polynomial.satisfiesRootCondition_of_roots`: the root condition read off the multiset of roots.
* `Polynomial.satisfiesRootCondition_of_isSchurStable`: $c (X - 1) Q$ with $c \neq 0$ and $Q$ Schur
  stable satisfies the root condition. This is the form of the first characteristic polynomial of a
  consistent multistep method.
* `Polynomial.satisfiesRootCondition_C_mul_iff`: the root condition does not change under
  multiplication by a nonzero constant.
* `LinearRecurrence.bddAbove_range_norm_of_satisfiesRootCondition_of_splits`: under the root
  condition, every solution of the homogeneous recurrence is bounded.
* `LinearRecurrence.norm_le_of_satisfiesRootCondition`: Lemma 11.3 of [quarteroni2000numerical],
  sufficiency, the bound (11.63).
* `LinearRecurrence.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition`: Lemma 11.3,
  necessity: if the root condition fails, the homogeneous recurrence has an unbounded solution.
* `LinearRecurrence.exists_forall_norm_le_iff_satisfiesRootCondition` and
  `LinearRecurrence.forall_bddAbove_iff_satisfiesRootCondition`: Lemma 11.3 as an equivalence, and
  its homogeneous form.
* `LinearRecurrence.forall_tendsto_zero_iff`: every solution of the homogeneous recurrence tends to
  zero if and only if every root of $\Pi$ lies in the open unit disc.
* `LinearRecurrence.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition`: a real
  recurrence whose characteristic polynomial violates the root condition in $\mathbb{C}$ has an
  unbounded real solution.
* `LinearRecurrence.norm_le_of_satisfiesRootCondition_of_le` and
  `LinearRecurrence.norm_le_of_satisfiesRootCondition_smul_of_le`: the bound (11.63) for a sequence
  that satisfies the recurrence only for $n + k \le N$, and for a sequence in a real normed space.
* `LinearRecurrence.exists_isSolution_norm_ge_of_not_satisfiesRootCondition` and
  `LinearRecurrence.exists_isSolution_real_frequently_le`: if the root condition fails, there are a
  complex solution with $|w_n| \ge cn$ for all $n$ and a real solution with $|u_n| \ge cn$ for
  infinitely many $n$, for some $c > 0$.

## Proof outline

Under the root condition every fundamental solution $\binom{n}{s} r^{n-s}$ is bounded: it tends to
zero for $|r| < 1$, and for $|r| = 1$ the root is simple, so $s = 0$ and the sequence is $r^n$ of
modulus one. Every homogeneous solution is a finite combination of these, and the Duhamel formula
with a uniform bound on the $\psi_j$ gives (11.63). If the root condition fails, $r^n$ for a root
with $|r| > 1$, or $n r^n$ for a multiple root with $|r| = 1$, is an unbounded solution.

## Implementation notes

* The root conditions are defined for a polynomial over any normed field. For a real polynomial the
  condition of interest is that of its image in $\mathbb{C}[X]$. This is how `Numlib.ODE.Multistep`
  reads the first characteristic polynomial $\rho$ of a real multistep method.
* The results on bounded and decaying solutions are stated over $\mathbb{K} = \mathbb{R}$ or
  $\mathbb{C}$ (`RCLike`), because the necessity directions use $|n| = n$ in $\mathbb{K}$ to see
  that $n r^n$ is unbounded. Where the fundamental system is used, the splitting of $\Pi$ is an
  explicit hypothesis. The forms over $\mathbb{C}$, where the splitting is automatic, carry the
  names of the statements of [quarteroni2000numerical].
* The term $\max_{j<k} |u_j|$ is the supremum `⨆ j : Fin E.order, ‖u j‖`.
* The quantitative necessity results are needed by a convergence proof that scales the unbounded
  solution by a step size $h \approx T/n$; unboundedness alone is not sufficient there.
* `Numlib.ODE.Multistep` uses these results for the zero-stability, the convergence and the absolute
  stability of linear multistep methods.
-/

open Filter Finset Polynomial Topology

namespace Polynomial

variable {K : Type*} [NormedField K]

/-- The **root condition** for a polynomial $P$ over a normed field: every root $r$ of $P$ satisfies
$|r| \le 1$, and every root with $|r| = 1$ is simple. This is Definition 11.10, (11.56), of
[quarteroni2000numerical].

Simplicity is stated as `Polynomial.rootMultiplicity r = 1`. The zero polynomial does not
satisfy the condition, because every element is a root of it. -/
def SatisfiesRootCondition (P : K[X]) : Prop :=
  ∀ r : K, P.IsRoot r → ‖r‖ ≤ 1 ∧ (‖r‖ = 1 → P.rootMultiplicity r = 1)

/-- Let $P \neq 0$. Then $P$ satisfies the root condition if and only if every root $r$ of $P$
satisfies $|r| \le 1$, and every root with $|r| = 1$ is not a root of the derivative $P'$. This
is the formulation of [quarteroni2000numerical]. -/
theorem satisfiesRootCondition_iff_derivative {P : K[X]} (hP : P ≠ 0) :
    P.SatisfiesRootCondition ↔
      ∀ r : K, P.IsRoot r → ‖r‖ ≤ 1 ∧ (‖r‖ = 1 → ¬ (derivative P).IsRoot r) := by
  refine forall_congr' fun r => forall_congr' fun hr => and_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  have h1 : 0 < P.rootMultiplicity r := (rootMultiplicity_pos hP).2 hr
  have h2 := one_lt_rootMultiplicity_iff_isRoot (t := r) hP
  constructor
  · intro h hd
    have := h2.2 ⟨hr, hd⟩
    omega
  · intro hd
    by_contra hne
    exact hd (h2.1 (by omega)).2

/-- Let $c \neq 0$. Then $cP$ satisfies the root condition if and only if $P$ does.

This is how the root condition is read off the polynomial $\Pi(z)$ of the absolute stability
region. -/
theorem satisfiesRootCondition_C_mul_iff {c : K} (hc : c ≠ 0) (P : K[X]) :
    (C c * P).SatisfiesRootCondition ↔ P.SatisfiesRootCondition := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp
  · have hne : C c * P ≠ 0 := mul_ne_zero (C_ne_zero.2 hc) hP
    simp only [Polynomial.SatisfiesRootCondition, IsRoot, eval_mul, eval_C, mul_eq_zero, hc,
      false_or, rootMultiplicity_mul hne, rootMultiplicity_C, zero_add]

/-- The **strong root condition** for a polynomial $P$ over a normed field: $P$ satisfies the root
condition, and every root $r \neq 1$ of $P$ satisfies $|r| < 1$. This is Definition 11.11,
(11.57), of [quarteroni2000numerical]. -/
def SatisfiesStrongRootCondition (P : K[X]) : Prop :=
  P.SatisfiesRootCondition ∧ ∀ r : K, P.IsRoot r → r ≠ 1 → ‖r‖ < 1

/-- The strong root condition implies the root condition. -/
theorem SatisfiesStrongRootCondition.satisfiesRootCondition {P : K[X]}
    (h : P.SatisfiesStrongRootCondition) : P.SatisfiesRootCondition :=
  h.1

section Roots

variable [DecidableEq K]

/-- Let $P \neq 0$. If every root $r$ in the multiset of roots of $P$ satisfies $|r| \le 1$, and
every such root with $|r| = 1$ occurs exactly once in the multiset, then $P$ satisfies the root
condition. -/
theorem satisfiesRootCondition_of_roots {P : K[X]} (hP : P ≠ 0) (h1 : ∀ r ∈ P.roots, ‖r‖ ≤ 1)
    (h2 : ∀ r ∈ P.roots, ‖r‖ = 1 → P.roots.count r = 1) : P.SatisfiesRootCondition := by
  intro r hr
  have hmem : r ∈ P.roots := (mem_roots hP).2 hr
  exact ⟨h1 r hmem, fun h => by rw [← count_roots]; exact h2 r hmem h⟩

end Roots

/-- Let $a \neq b$ with $|a| \le 1$ and $|b| \le 1$. Then $(X - a)(X - b)$ satisfies the root
condition. -/
theorem satisfiesRootCondition_X_sub_C_mul_X_sub_C {a b : K} (hab : a ≠ b) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) : ((X - C a) * (X - C b)).SatisfiesRootCondition := by
  classical
  have hne : ((X - C a) * (X - C b) : K[X]) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  refine satisfiesRootCondition_of_roots hne ?_ ?_
  · intro r hr
    rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hr
    rcases hr with rfl | rfl
    exacts [ha, hb]
  · intro r hr _
    rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hr
    rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.count_add, Multiset.count_singleton,
      Multiset.count_singleton]
    rcases hr with rfl | rfl <;> simp [hab, hab.symm]

/-- **From Schur stability to the root condition.** Let $P, Q \in \mathbb{R}[X]$ and
$c \in \mathbb{R}$ with $c \neq 0$ and
$$P = c (X - 1) Q,$$
and let $Q$ be Schur stable: every complex root of $Q$ has modulus less than $1$. Then $P$, as a
polynomial in $\mathbb{C}[X]$, satisfies the root condition.

The roots of $P$ lie in the closed unit disc, and the only one of modulus one is the simple root
$1$. Schur stability is `Polynomial.IsSchurStable`. -/
theorem satisfiesRootCondition_of_isSchurStable {P Q : ℝ[X]} {c : ℝ} (hc : c ≠ 0)
    (hQ : Q.IsSchurStable) (hP : P = C c * ((X - C 1) * Q)) :
    (P.map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  classical
  set Qc : ℂ[X] := Q.map (algebraMap ℝ ℂ) with hQc
  have hQeval : ∀ z : ℂ, Qc.eval z = aeval z Q := fun z => by rw [hQc, eval_map, aeval_def]
  have hQ1 : Qc.eval 1 ≠ 0 := by
    rw [hQeval]
    exact hQ.aeval_ne_zero (by simp)
  have hQ0 : Qc ≠ 0 := fun h0 => hQ1 (by rw [h0]; simp)
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hmap : P.map (algebraMap ℝ ℂ) = C (c : ℂ) * ((X - C 1) * Qc) := by
    rw [hP, hQc]
    simp [Polynomial.map_mul, Polynomial.map_sub]
  have hXne : (X - C 1 : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hprod : (X - C 1 : ℂ[X]) * Qc ≠ 0 := mul_ne_zero hXne hQ0
  have hall : C (c : ℂ) * ((X - C 1) * Qc) ≠ 0 := mul_ne_zero (by simpa using hcne) hprod
  rw [hmap]
  intro r hr
  have hfac : (r - 1) * Qc.eval r = 0 := by
    have h := hr
    simp only [IsRoot, eval_mul, eval_C, eval_sub, eval_X] at h
    exact (mul_eq_zero.1 h).resolve_left hcne
  rcases mul_eq_zero.1 hfac with h1 | h2
  · have hr1 : r = 1 := by linear_combination h1
    subst hr1
    refine ⟨by simp, fun _ => ?_⟩
    have hc1 : ¬ (C (c : ℂ)).IsRoot 1 := by simp [IsRoot, hcne]
    have hq1 : ¬ Qc.IsRoot 1 := hQ1
    rw [rootMultiplicity_mul hall, rootMultiplicity_mul hprod,
      rootMultiplicity_eq_zero hc1, rootMultiplicity_eq_zero hq1,
      rootMultiplicity_X_sub_C_self]
  · rw [hQeval] at h2
    have hlt : ‖r‖ < 1 := hQ r h2
    exact ⟨hlt.le, fun h => absurd h hlt.ne⟩

/-! ### The root condition for particular polynomials, and a bound on the unit disc -/

/-- The polynomial $X^2 - 1 = (X - 1)(X + 1)$, as a polynomial in $\mathbb{C}[X]$, satisfies the
root condition: its roots $\pm 1$ are simple. -/
theorem satisfiesRootCondition_X_sq_sub_one :
    ((X ^ 2 - 1 : ℝ[X]).map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  classical
  have hfac : ((X ^ 2 - 1 : ℝ[X]).map (algebraMap ℝ ℂ)) = (X - C 1) * (X - C (-1)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, map_neg, map_one]
    ring
  rw [hfac]
  exact satisfiesRootCondition_X_sub_C_mul_X_sub_C (by norm_num) (by simp) (by simp)

/-- For every $p \in \mathbb{N}$, the polynomial $X^p (X - 1)$, as a polynomial in $\mathbb{C}[X]$,
satisfies the root condition: its roots are $0$, of multiplicity $p$, and the simple root $1$. -/
theorem satisfiesRootCondition_X_pow_mul_X_sub_one (p : ℕ) :
    ((X ^ p * (X - C 1) : ℝ[X]).map (algebraMap ℝ ℂ)).SatisfiesRootCondition := by
  classical
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, Polynomial.map_sub, map_X, map_C, map_one]
  have hne : (X : ℂ[X]) ^ p * (X - C 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero 1)
  have hroots : ((X : ℂ[X]) ^ p * (X - C 1)).roots = p • {0} + {1} := by
    rw [roots_mul hne, roots_X_pow, roots_X_sub_C]
  refine satisfiesRootCondition_of_roots hne ?_ ?_
  · intro r hr
    rw [hroots, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_nsmul,
      Multiset.mem_singleton] at hr
    rcases hr with ⟨-, rfl⟩ | rfl <;> simp
  · intro r hr h1
    rw [hroots, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_nsmul,
      Multiset.mem_singleton] at hr
    rcases hr with ⟨-, rfl⟩ | rfl
    · simp at h1
    · rw [hroots, Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self,
        Multiset.count_singleton]
      simp

/-- Let $P \in \mathbb{C}[X]$ be monic, with every root in the open unit disc. Then for every
$x \in \mathbb{C}$ with $|x| \le 1$,
$$|P(x)| \le 2^{\deg P}.$$
-/
theorem norm_eval_le_two_pow_natDegree {P : ℂ[X]} (hP : P.Monic)
    (hroots : ∀ r, P.IsRoot r → ‖r‖ < 1) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖P.eval x‖ ≤ 2 ^ P.natDegree := by
  have hs := IsAlgClosed.splits P
  rw [hs.eval_eq_prod_roots, hP.leadingCoeff, one_mul, ← splits_iff_card_roots.1 hs]
  have key : ∀ s : Multiset ℂ, (∀ a ∈ s, ‖x - a‖ ≤ 2) →
      ‖(s.map fun a => x - a).prod‖ ≤ 2 ^ Multiset.card s := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro hs'
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ', norm_mul]
      exact mul_le_mul (hs' a (Multiset.mem_cons_self a s))
        (ih fun b hb => hs' b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _) (by norm_num)
  refine key _ fun a ha => ?_
  have := hroots a ((mem_roots hP.ne_zero).1 ha)
  calc ‖x - a‖ ≤ ‖x‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

end Polynomial

namespace LinearRecurrence

/-! ### Solutions on a finite horizon -/

/-- Let $u$ satisfy the recurrence $u_{n+k} = \sum_{i<k} \alpha_i u_{n+i} + \varphi_{n+k}$ for all
$n$ with $n + k \le N$. Then $u_n = v_n$ for all $n \le N$, where $v$ is the solution of the
recurrence on all of $\mathbb{N}$ with the source $\varphi_l$ for $l \le N$ and $0$ for $l > N$,
and with the initial values $v_j = u_j$ for $j < k$.

The solution $v$ is `LinearRecurrence.mkSolWith`. -/
theorem eq_mkSolWith_of_le {R : Type*} [CommSemiring R] (E : LinearRecurrence R) {φ u : ℕ → R}
    {N : ℕ}
    (hu : ∀ n, n + E.order ≤ N →
      u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)) :
    ∀ n ≤ N, u n = E.mkSolWith (fun l => if l ≤ N then φ l else 0) (fun j => u j) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h' : n < E.order
    · exact (E.mkSolWith_eq_init (fun l => if l ≤ N then φ l else 0) (fun j => u j) ⟨n, h'⟩).symm
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + E.order := ⟨n - E.order, by omega⟩
      rw [hu m hn, E.isSolutionWith_mkSolWith _ _ m]
      simp only [hn, ite_true]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ih (m + k) (by have := k.is_lt; omega) (by have := k.is_lt; omega)]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The fundamental solutions -/

/-- Let $|r| < 1$ and $s \in \mathbb{N}$. Then the binomial sequence $\binom{n}{s} r^{n-s}$ tends to
$0$ as $n \to \infty$.

The sequence is `LinearRecurrence.chooseMulPow r s`. -/
theorem tendsto_chooseMulPow_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) (s : ℕ) :
    Tendsto (chooseMulPow r s) atTop (𝓝 0) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [chooseMulPow_zero_left]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop s] with n hn
    rw [Pi.single_eq_of_ne hn.ne']
  · have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one s
      (by rwa [abs_of_nonneg (norm_nonneg r)])).div_const (‖r‖ ^ s)
    rw [zero_div] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h
    filter_upwards [eventually_ge_atTop s] with n hn
    rw [chooseMulPow_apply, norm_mul, norm_pow, RCLike.norm_natCast, le_div_iff₀ (by positivity),
      mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
    gcongr
    exact_mod_cast Nat.choose_le_pow n s

/-- Let $|r| < 1$ and $s \in \mathbb{N}$. Then the binomial sequence $\binom{n}{s} r^{n-s}$ is
bounded. -/
theorem bddAbove_range_norm_chooseMulPow_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) (s : ℕ) :
    BddAbove (Set.range fun n => ‖chooseMulPow r s n‖) :=
  ((tendsto_chooseMulPow_of_norm_lt_one hr s).norm).bddAbove_range

/-- If $|r| = 1$, the binomial sequence with $s = 0$, which is $r^n$, has modulus $1$ for every $n$.
-/
theorem norm_chooseMulPow_zero_of_norm_eq_one {r : 𝕜} (hr : ‖r‖ = 1) (n : ℕ) :
    ‖chooseMulPow r 0 n‖ = 1 := by
  simp [hr]

/-- A finite linear combination $\sum_i c_i v_i$ of bounded sequences
$v_i : \mathbb{N} \to \mathbb{K}$ is bounded. -/
theorem bddAbove_range_norm_sum_smul {ι : Type*} [Fintype ι] {c : ι → 𝕜} {v : ι → ℕ → 𝕜}
    (hv : ∀ i, BddAbove (Set.range fun n => ‖v i n‖)) :
    BddAbove (Set.range fun n => ‖(∑ i, c i • v i) n‖) := by
  choose M hM using hv
  refine ⟨∑ i, ‖c i‖ * M i, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(∑ i, c i • v i) n‖ ≤ _
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hM i ⟨n, rfl⟩) (norm_nonneg _)

variable (E : LinearRecurrence 𝕜)

/-- If the characteristic polynomial of a recurrence satisfies the root condition, every fundamental
solution $\binom{n}{s} r^{n-s}$ is bounded. Here $r$ is a root and $s$ is less than the
multiplicity of $r$.

For $|r| < 1$ the sequence tends to zero. For $|r| = 1$ the root is simple, so $s = 0$ and the
sequence is $r^n$, of modulus one. The fundamental solutions are
`LinearRecurrence.fundamentalSol`, indexed by `LinearRecurrence.RootIndex`. -/
theorem bddAbove_range_norm_fundamentalSol_of_satisfiesRootCondition [DecidableEq 𝕜]
    (hE : E.charPoly.SatisfiesRootCondition) (p : E.RootIndex) :
    BddAbove (Set.range fun n => ‖E.fundamentalSol p n‖) := by
  obtain ⟨r, s⟩ := p
  have hroot : E.charPoly.IsRoot r := by
    have hr := r.2
    rwa [Multiset.mem_toFinset, mem_roots E.charPoly_monic.ne_zero] at hr
  obtain ⟨hle, heq⟩ := hE r hroot
  rcases hle.lt_or_eq with hlt | h1
  · exact bddAbove_range_norm_chooseMulPow_of_norm_lt_one hlt _
  · have hs : (s : ℕ) = 0 := by have := s.is_lt; have := heq h1; omega
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp only [fundamentalSol, hs]
    exact (norm_chooseMulPow_zero_of_norm_eq_one h1 n).le

/-- Let the characteristic polynomial of a recurrence split over $\mathbb{K}$ and satisfy the root
condition. Then every solution of the homogeneous recurrence is bounded. This is the homogeneous
case of Lemma 11.3 of [quarteroni2000numerical].

Every solution is a finite combination of the fundamental solutions, which are bounded. -/
theorem bddAbove_range_norm_of_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) {u : ℕ → 𝕜} (hu : E.IsSolution u) :
    BddAbove (Set.range fun n => ‖u n‖) := by
  classical
  obtain ⟨c, rfl⟩ := E.exists_eq_sum_smul_fundamentalSol hs hu
  exact bddAbove_range_norm_sum_smul fun p =>
    E.bddAbove_range_norm_fundamentalSol_of_satisfiesRootCondition hE p

/-- Let the characteristic polynomial of a recurrence of order $k$ split over $\mathbb{K}$ and
satisfy the root condition. Then the Kronecker fundamental solutions are uniformly bounded:
there is $M$ with $|\psi_j(n)| \le M$ for all $j < k$ and all $n$.

The solution $\psi_j$ is `LinearRecurrence.kroneckerSol j`: the homogeneous solution with
$\psi_j(i) = \delta_{ij}$ for $i < k$. -/
theorem norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, ∀ (j : Fin E.order) (n : ℕ), ‖E.kroneckerSol j n‖ ≤ M := by
  have h : ∀ j : Fin E.order, ∃ M : ℝ, ∀ n, ‖E.kroneckerSol j n‖ ≤ M := fun j => by
    obtain ⟨M, hM⟩ := E.bddAbove_range_norm_of_satisfiesRootCondition_of_splits hs hE
      (E.isSolution_kroneckerSol j)
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
  choose M hM using h
  refine ⟨∑ j, max (M j) 0, fun j n => (hM j n).trans ((le_max_left (M j) 0).trans ?_)⟩
  exact single_le_sum (f := fun j => max (M j) 0) (fun j _ => le_max_right _ _) (mem_univ j)

/-! ### Lemma 11.3 -/

/-- **Lemma 11.3, sufficiency.** Let the recurrence have order $k > 0$, and let its characteristic
polynomial split over $\mathbb{K}$ and satisfy the root condition. Then there is $M > 0$ such
that every solution $u$ of the recurrence $u_{n+k} = \sum_{i<k} \alpha_i u_{n+i} +
\varphi_{n+k}$ with source $\varphi$ satisfies, for every $n$,
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr).$$
This is the bound (11.63) of [quarteroni2000numerical].

The proof is the Duhamel formula `LinearRecurrence.eq_sum_kroneckerSol_add_sum` with the uniform
bound $M_0$ on the Kronecker solutions; $M = k M_0 + 1$ works. The sum is empty for $n < k$. -/
theorem norm_le_of_satisfiesRootCondition_of_splits (hk : 0 < E.order) (hs : E.charPoly.Splits)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
  obtain ⟨M₀, hM₀⟩ := E.norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits hs hE
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ ⟨0, hk⟩ 0)
  have : Nonempty (Fin E.order) := ⟨⟨0, hk⟩⟩
  refine ⟨E.order * M₀ + 1, by positivity, fun φ u hu n => ?_⟩
  have hsup : ∀ j : Fin E.order, ‖u j‖ ≤ ⨆ j : Fin E.order, ‖u j‖ := fun j =>
    le_ciSup (f := fun j : Fin E.order => ‖u j‖) (Set.finite_range _).bddAbove j
  have hsup0 : 0 ≤ ⨆ j : Fin E.order, ‖u j‖ := (norm_nonneg _).trans (hsup ⟨0, hk⟩)
  have hφ0 : 0 ≤ ∑ l ∈ Icc E.order n, ‖φ l‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc ‖u n‖ = ‖(∑ j : Fin E.order, u j * E.kroneckerSol j n) + ∑ l ∈ Icc E.order n,
        φ l * E.kroneckerSol ⟨E.order - 1, by omega⟩ (n - l + (E.order - 1))‖ := by
        rw [← eq_sum_kroneckerSol_add_sum hk hu n]
    _ ≤ ∑ j : Fin E.order, ‖u j‖ * M₀ + ∑ l ∈ Icc E.order n, ‖φ l‖ * M₀ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (sum_le_sum
          fun j _ => ?_)) ((norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)))
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM₀ j n) (norm_nonneg _)
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM₀ _ _) (norm_nonneg _)
    _ ≤ (E.order * ⨆ j : Fin E.order, ‖u j‖) * M₀ + (∑ l ∈ Icc E.order n, ‖φ l‖) * M₀ := by
        rw [← sum_mul, ← sum_mul]
        gcongr
        refine (sum_le_sum fun j _ => hsup j).trans ?_
        simp
    _ = E.order * M₀ * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) -
        (E.order - 1) * M₀ * ∑ l ∈ Icc E.order n, ‖φ l‖ := by ring
    _ ≤ E.order * M₀ * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
        have : (1 : ℝ) ≤ E.order := by exact_mod_cast hk
        nlinarith [mul_nonneg hM₀0 hφ0]
    _ ≤ (E.order * M₀ + 1) * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) := by
        nlinarith

/-- **Lemma 11.3, necessity.** If the characteristic polynomial of a recurrence over $\mathbb{K}$
does not satisfy the root condition, the homogeneous recurrence has an unbounded solution.

The solution is $r^n$ for a root $r$ with $|r| > 1$, and $n r^n$ for a multiple root with
$|r| = 1$. The characteristic polynomial need not split. -/
theorem exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition
    (h : ¬ E.charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → 𝕜, E.IsSolution u ∧ ¬ BddAbove (Set.range fun n => ‖u n‖) := by
  simp only [Polynomial.SatisfiesRootCondition, not_forall, not_and] at h
  obtain ⟨r, hr, hr'⟩ := h
  by_cases h1 : 1 < ‖r‖
  · refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, ?_⟩
    simp only [norm_pow]
    exact not_bddAbove_of_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt h1)
  · obtain ⟨hle, hmult⟩ := hr' (not_lt.1 h1)
    have hpos : 0 < E.charPoly.rootMultiplicity r :=
      (rootMultiplicity_pos E.charPoly_monic.ne_zero).2 hr
    refine ⟨fun n => (n : 𝕜) * r ^ n,
      E.isSolution_mul_pow_of_one_lt_rootMultiplicity (by omega), ?_⟩
    simp only [norm_mul, norm_pow, hle, one_pow, mul_one, RCLike.norm_natCast]
    exact not_bddAbove_of_tendsto_atTop tendsto_natCast_atTop_atTop

/-- If there is $M$ such that every solution $u$ of the recurrence with every source $\varphi$
satisfies
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for all }
  n,$$
then the characteristic polynomial satisfies the root condition.

This is the direction of Lemma 11.3 of [quarteroni2000numerical] that applies the bound (11.63)
to the unbounded homogeneous solution of
`LinearRecurrence.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition`. -/
theorem satisfiesRootCondition_of_forall_norm_le {M : ℝ}
    (hM : ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) :
    E.charPoly.SatisfiesRootCondition := by
  by_contra h
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition h
  refine hu' ⟨M * ⨆ j : Fin E.order, ‖u j‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  simpa using hM 0 u ((E.isSolutionWith_zero_iff u).2 hu) n

/-- **Lemma 11.3** of [quarteroni2000numerical], as an equivalence. Let the recurrence have order
$k > 0$, and let its characteristic polynomial split over $\mathbb{K}$. Then the characteristic
polynomial satisfies the root condition if and only if there is $M > 0$ such that every solution
$u$ with every source $\varphi$ satisfies
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for all }
  n.$$
-/
theorem exists_forall_norm_le_iff_satisfiesRootCondition_of_splits (hk : 0 < E.order)
    (hs : E.charPoly.Splits) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → 𝕜, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  ⟨fun ⟨_, _, hM⟩ => E.satisfiesRootCondition_of_forall_norm_le hM,
    E.norm_le_of_satisfiesRootCondition_of_splits hk hs⟩

/-- The homogeneous form of Lemma 11.3 of [quarteroni2000numerical]. Let the characteristic
polynomial of a recurrence split over $\mathbb{K}$. Then every solution of the homogeneous
recurrence is bounded if and only if the characteristic polynomial satisfies the root condition.

This describes the region $\mathcal{A}^*$ of Remark 11.3 of [quarteroni2000numerical]. -/
theorem forall_bddAbove_iff_satisfiesRootCondition_of_splits (hs : E.charPoly.Splits) :
    (∀ u : ℕ → 𝕜, E.IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔
      E.charPoly.SatisfiesRootCondition := by
  refine ⟨fun h => by_contra fun hE => ?_,
    fun hE u hu => E.bddAbove_range_norm_of_satisfiesRootCondition_of_splits hs hE hu⟩
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition hE
  exact hu' (h u hu)

/-! ### Decay -/

/-- Let the characteristic polynomial of a recurrence split over $\mathbb{K}$, with every root $r$
satisfying $|r| < 1$. Then every solution of the homogeneous recurrence tends to $0$.

Each fundamental solution tends to $0$. -/
theorem tendsto_zero_of_forall_norm_lt_one_of_splits (hs : E.charPoly.Splits)
    (hE : ∀ r : 𝕜, E.charPoly.IsRoot r → ‖r‖ < 1) {u : ℕ → 𝕜} (hu : E.IsSolution u) :
    Tendsto u atTop (𝓝 0) := by
  classical
  obtain ⟨c, rfl⟩ := E.exists_eq_sum_smul_fundamentalSol hs hu
  have : Tendsto (fun n => ∑ p : E.RootIndex, c p • E.fundamentalSol p n) atTop (𝓝 0) := by
    rw [show (0 : 𝕜) = ∑ p : E.RootIndex, c p • (0 : 𝕜) by simp]
    refine tendsto_finsetSum _ fun p _ => (tendsto_chooseMulPow_of_norm_lt_one ?_ _).const_smul _
    obtain ⟨⟨r, hr⟩, s⟩ := p
    rw [Multiset.mem_toFinset, mem_roots E.charPoly_monic.ne_zero] at hr
    exact hE r hr
  refine this.congr fun n => ?_
  simp [Finset.sum_apply]

/-- If $r$ is a root of the characteristic polynomial with $|r| \ge 1$, the homogeneous recurrence
has a solution that does not tend to $0$, namely $r^n$. -/
theorem exists_isSolution_not_tendsto_zero_of_one_le_norm {r : 𝕜} (hr : E.charPoly.IsRoot r)
    (h1 : 1 ≤ ‖r‖) : ∃ u : ℕ → 𝕜, E.IsSolution u ∧ ¬ Tendsto u atTop (𝓝 0) := by
  refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, fun h => ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds one_pos)).exists
  simp only [norm_pow] at hn
  exact hn.not_ge (one_le_pow₀ h1)

/-- **The decay criterion.** Let the characteristic polynomial of a recurrence split over
$\mathbb{K}$. Then every solution of the homogeneous recurrence tends to $0$ if and only if
every root $r$ of the characteristic polynomial satisfies $|r| < 1$. -/
theorem forall_tendsto_zero_iff_of_splits (hs : E.charPoly.Splits) :
    (∀ u : ℕ → 𝕜, E.IsSolution u → Tendsto u atTop (𝓝 0)) ↔
      ∀ r : 𝕜, E.charPoly.IsRoot r → ‖r‖ < 1 := by
  refine ⟨fun h r hr => by_contra fun h1 => ?_,
    fun hE u hu => E.tendsto_zero_of_forall_norm_lt_one_of_splits hs hE hu⟩
  obtain ⟨u, hu, hu'⟩ := E.exists_isSolution_not_tendsto_zero_of_one_le_norm hr (not_lt.1 h1)
  exact hu' (h u hu)

end RCLike

/-! ### Over the complex numbers -/

section Complex

variable (E : LinearRecurrence ℂ)

/-- If the characteristic polynomial of a complex recurrence of order $k$ satisfies the root
condition, the Kronecker fundamental solutions are uniformly bounded: there is $M$ with
$|\psi_j(n)| \le M$ for all $j < k$ and all $n$. -/
theorem norm_kroneckerSol_le_of_satisfiesRootCondition (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, ∀ (j : Fin E.order) (n : ℕ), ‖E.kroneckerSol j n‖ ≤ M :=
  E.norm_kroneckerSol_le_of_satisfiesRootCondition_of_splits (IsAlgClosed.splits _) hE

/-- **Lemma 11.3, sufficiency**, over $\mathbb{C}$. Let a complex recurrence have order $k > 0$, and
let its characteristic polynomial satisfy the root condition. Then there is $M > 0$ such that
every solution $u$ of the recurrence with source $\varphi$ satisfies, for every $n$,
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr).$$
This is the bound (11.63) of [quarteroni2000numerical]. -/
theorem norm_le_of_satisfiesRootCondition (hk : 0 < E.order)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖) :=
  E.norm_le_of_satisfiesRootCondition_of_splits hk (IsAlgClosed.splits _) hE

/-- **Lemma 11.3 on a finite horizon**, over $\mathbb{C}$. Let a complex recurrence have order
$k > 0$, and let its characteristic polynomial satisfy the root condition. Then there is $M > 0$
with the following property. Let $N \in \mathbb{N}$, and let $u$ satisfy $u_{n+k} = \sum_{i<k}
\alpha_i u_{n+i} + \varphi_{n+k}$ for all $n$ with $n + k \le N$. Then for every $n \le N$,
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr).$$
This is the bound (11.63) of [quarteroni2000numerical] for a sequence that satisfies the
recurrence only up to $N$.

The constant $M$ does not depend on $N$. A perturbed orbit of a multistep method satisfies its
recurrence only while its nodes stay inside the time interval, and this form covers it. The
proof extends $u$ by `LinearRecurrence.mkSolWith` (`LinearRecurrence.eq_mkSolWith_of_le`). -/
theorem norm_le_of_satisfiesRootCondition_of_le (hk : 0 < E.order)
    (hE : E.charPoly.SatisfiesRootCondition) :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (φ u : ℕ → ℂ),
      (∀ n, n + E.order ≤ N → u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + φ (n + E.order)) →
      ∀ n ≤ N, ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Finset.Icc E.order n, ‖φ l‖) := by
  obtain ⟨M, hM0, hM⟩ := E.norm_le_of_satisfiesRootCondition hk hE
  refine ⟨M, hM0, fun N φ u hu n hn => ?_⟩
  set φ' : ℕ → ℂ := fun l => if l ≤ N then φ l else 0
  have key := hM φ' (E.mkSolWith φ' fun j => u j) (E.isSolutionWith_mkSolWith φ' _) n
  rw [← E.eq_mkSolWith_of_le hu n hn] at key
  refine key.trans (le_of_eq ?_)
  congr 2
  · exact iSup_congr fun j => by rw [E.mkSolWith_eq_init]
  · refine Finset.sum_congr rfl fun l hl => ?_
    simp only [φ', (Finset.mem_Icc.1 hl).2.trans hn, ite_true]

/-- **Lemma 11.3** of [quarteroni2000numerical], over $\mathbb{C}$. Let a complex recurrence have
order $k > 0$. Then its characteristic polynomial satisfies the root condition if and only if
there is $M > 0$ such that every solution $u$ with every source $\varphi$ satisfies
$$|u_n| \le M \Bigl(\max_{j < k} |u_j| + \sum_{l=k}^{n} |\varphi_l|\Bigr) \qquad \text{for all }
  n.$$
-/
theorem exists_forall_norm_le_iff_satisfiesRootCondition (hk : 0 < E.order) :
    (∃ M : ℝ, 0 < M ∧ ∀ φ u : ℕ → ℂ, E.IsSolutionWith φ u → ∀ n,
      ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Icc E.order n, ‖φ l‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  E.exists_forall_norm_le_iff_satisfiesRootCondition_of_splits hk (IsAlgClosed.splits _)

/-- The homogeneous form of Lemma 11.3 of [quarteroni2000numerical], over $\mathbb{C}$: every
solution of a homogeneous complex recurrence is bounded if and only if its characteristic
polynomial satisfies the root condition.

This describes the region $\mathcal{A}^*$ of Remark 11.3 of [quarteroni2000numerical]. -/
theorem forall_bddAbove_iff_satisfiesRootCondition :
    (∀ u : ℕ → ℂ, E.IsSolution u → BddAbove (Set.range fun n => ‖u n‖)) ↔
      E.charPoly.SatisfiesRootCondition :=
  E.forall_bddAbove_iff_satisfiesRootCondition_of_splits (IsAlgClosed.splits _)

/-- **The decay criterion**, over $\mathbb{C}$: every solution of a homogeneous complex recurrence
tends to $0$ if and only if every root $r$ of its characteristic polynomial satisfies $|r| < 1$.

This criterion is behind the absolute root condition of [quarteroni2000numerical], §11.6.4. -/
theorem forall_tendsto_zero_iff :
    (∀ u : ℕ → ℂ, E.IsSolution u → Tendsto u atTop (𝓝 0)) ↔
      ∀ r : ℂ, E.charPoly.IsRoot r → ‖r‖ < 1 :=
  E.forall_tendsto_zero_iff_of_splits (IsAlgClosed.splits _)

/-- If the characteristic polynomial of a complex recurrence does not satisfy the root condition,
there are a solution $w$ of the homogeneous recurrence and $c > 0$ with $|w_n| \ge cn$ for all
$n$. -/
theorem exists_isSolution_norm_ge_of_not_satisfiesRootCondition
    (h : ¬ E.charPoly.SatisfiesRootCondition) :
    ∃ w : ℕ → ℂ, E.IsSolution w ∧ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * n ≤ ‖w n‖ := by
  simp only [Polynomial.SatisfiesRootCondition, not_forall, not_and] at h
  obtain ⟨r, hr, hr'⟩ := h
  by_cases h1 : 1 < ‖r‖
  · refine ⟨fun n => r ^ n, (E.geom_sol_iff_root_charPoly r).2 hr, ‖r‖ - 1, by linarith,
      fun n => ?_⟩
    rw [norm_pow]
    have := one_add_mul_le_pow (a := ‖r‖ - 1) (by linarith) n
    rw [add_sub_cancel] at this
    linarith
  · obtain ⟨hle, hmult⟩ := hr' (not_lt.1 h1)
    have hpos : 0 < E.charPoly.rootMultiplicity r :=
      (rootMultiplicity_pos E.charPoly_monic.ne_zero).2 hr
    refine ⟨fun n => (n : ℂ) * r ^ n,
      E.isSolution_mul_pow_of_one_lt_rootMultiplicity (by omega), 1, one_pos, fun n => ?_⟩
    simp [norm_pow, hle]

end Complex

/-! ### Real recurrences -/

section Real

variable (E : LinearRecurrence ℝ)

/-- Let $w : \mathbb{N} \to \mathbb{C}$ solve the homogeneous recurrence of a real recurrence, with
its coefficients mapped to $\mathbb{C}$. Then the real part $(\operatorname{Re} w_n)$ is a
solution of the real recurrence. -/
theorem isSolution_re_of_map {w : ℕ → ℂ} (hw : (E.map (algebraMap ℝ ℂ)).IsSolution w) :
    E.IsSolution fun n => (w n).re := by
  intro n
  have := congrArg Complex.re (hw n)
  simp only [map, Complex.coe_algebraMap, Complex.re_sum, Complex.re_ofReal_mul] at this
  exact this

/-- Let $w : \mathbb{N} \to \mathbb{C}$ solve the homogeneous recurrence of a real recurrence, with
its coefficients mapped to $\mathbb{C}$. Then the imaginary part $(\operatorname{Im} w_n)$ is a
solution of the real recurrence. -/
theorem isSolution_im_of_map {w : ℕ → ℂ} (hw : (E.map (algebraMap ℝ ℂ)).IsSolution w) :
    E.IsSolution fun n => (w n).im := by
  intro n
  have := congrArg Complex.im (hw n)
  simp only [map, Complex.coe_algebraMap, Complex.im_sum, Complex.im_ofReal_mul] at this
  exact this

/-- **Lemma 11.3, necessity, real form.** Let a real recurrence have a characteristic polynomial
that, as a polynomial in $\mathbb{C}[X]$, does not satisfy the root condition. Then the
homogeneous real recurrence has an unbounded real solution.

The solution is the real or the imaginary part of the unbounded complex solution, because $|w_n|
\le |\operatorname{Re} w_n| + |\operatorname{Im} w_n|$. The necessity parts of Theorems 11.4 and
11.5 of [quarteroni2000numerical] need this real solution. The sequence
$\varepsilon (r + \bar{r})^n$ that [quarteroni2000numerical] gives for a complex root $r$ is not
a solution. -/
theorem exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition
    (h : ¬ (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → ℝ, E.IsSolution u ∧ ¬ BddAbove (Set.range fun n => |u n|) := by
  obtain ⟨w, hw, hw'⟩ :=
    (E.map (algebraMap ℝ ℂ)).exists_isSolution_not_bddAbove_of_not_satisfiesRootCondition h
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  obtain ⟨A, hA⟩ := hcon _ (E.isSolution_re_of_map hw)
  obtain ⟨B, hB⟩ := hcon _ (E.isSolution_im_of_map hw)
  refine hw' ⟨A + B, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))

/-- **A real solution that grows at least linearly along a subsequence.** Let a real recurrence have
a characteristic polynomial that, as a polynomial in $\mathbb{C}[X]$, does not satisfy the root
condition. Then there are a real solution $u$ of the homogeneous recurrence and $c > 0$ with
$|u_n| \ge cn$ for infinitely many $n$. -/
theorem exists_isSolution_real_frequently_le
    (h : ¬ (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition) :
    ∃ u : ℕ → ℝ, E.IsSolution u ∧ ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c * n ≤ |u n| := by
  obtain ⟨w, hw, c, hc, hcw⟩ :=
    (E.map (algebraMap ℝ ℂ)).exists_isSolution_norm_ge_of_not_satisfiesRootCondition h
  have hor : ∃ᶠ n in atTop, c / 2 * n ≤ |(w n).re| ∨ c / 2 * n ≤ |(w n).im| := by
    refine Eventually.frequently (Eventually.of_forall fun n => ?_)
    have := (hcw n).trans (Complex.norm_le_abs_re_add_abs_im (w n))
    by_contra hcon
    push Not at hcon
    linarith [hcon.1, hcon.2]
  rcases Filter.frequently_or_distrib.1 hor with H | H
  · exact ⟨_, E.isSolution_re_of_map hw, c / 2, by positivity, H⟩
  · exact ⟨_, E.isSolution_im_of_map hw, c / 2, by positivity, H⟩

/-- **Lemma 11.3 on a finite horizon, for sequences in a normed space.** Let a real recurrence have
order $k > 0$, and let its characteristic polynomial, as a polynomial in $\mathbb{C}[X]$,
satisfy the root condition. Let $V$ be a real normed space. Then there is $M > 0$ with the
following property. Let $N \in \mathbb{N}$, and let $u, \varphi : \mathbb{N} \to V$ satisfy
$u_{n+k} = \sum_{i<k} \alpha_i u_{n+i} + \varphi_{n+k}$ for all $n$ with $n + k \le N$. Then for
every $n \le N$,
$$\|u_n\| \le M \Bigl(\max_{j < k} \|u_j\| + \sum_{l=k}^{n} \|\varphi_l\|\Bigr).$$

The difference of two orbits of a multistep method is such a sequence. The proof applies the
complex scalar case `LinearRecurrence.norm_le_of_satisfiesRootCondition_of_le` to $g \circ u$,
where $g$ is a norming functional of $u_n$ from the Hahn–Banach theorem
(`exists_dual_vector''`). -/
theorem norm_le_of_satisfiesRootCondition_smul_of_le (hk : 0 < E.order)
    (hE : (E.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ M : ℝ, 0 < M ∧ ∀ (N : ℕ) (φ u : ℕ → V),
      (∀ n, n + E.order ≤ N → u (n + E.order) = ∑ i, E.coeffs i • u (n + i) + φ (n + E.order)) →
      ∀ n ≤ N, ‖u n‖ ≤ M * ((⨆ j : Fin E.order, ‖u j‖) + ∑ l ∈ Finset.Icc E.order n, ‖φ l‖) := by
  obtain ⟨M, hM0, hM⟩ := (E.map (algebraMap ℝ ℂ)).norm_le_of_satisfiesRootCondition_of_le hk hE
  refine ⟨M, hM0, fun N φ u hu n hn => ?_⟩
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ (u n)
  set v : ℕ → ℂ := fun l => ((g (u l) : ℝ) : ℂ)
  set ψ : ℕ → ℂ := fun l => ((g (φ l) : ℝ) : ℂ)
  have hv : ∀ m, m + (E.map (algebraMap ℝ ℂ)).order ≤ N →
      v (m + (E.map (algebraMap ℝ ℂ)).order) =
        ∑ i, (E.map (algebraMap ℝ ℂ)).coeffs i * v (m + i) +
          ψ (m + (E.map (algebraMap ℝ ℂ)).order) := by
    intro m hm
    simp only [v, ψ, map_order, hu m hm, map_add, map_sum, map_smul, smul_eq_mul]
    push_cast
    rfl
  have key := hM N ψ v hv n hn
  have hvn : ‖v n‖ = ‖u n‖ := by
    simp only [v, hgx, Complex.norm_real, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs,
      abs_norm]
  have hle : ∀ x : V, ‖((g x : ℝ) : ℂ)‖ ≤ ‖x‖ := fun x => by
    rw [Complex.norm_real]
    exact (g.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hg1)
  rw [hvn] at key
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hM0.le)
  · exact ciSup_mono (Finite.bddAbove_range _) fun j => hle (u j)
  · exact Finset.sum_le_sum fun l _ => hle (φ l)

end Real

end LinearRecurrence
