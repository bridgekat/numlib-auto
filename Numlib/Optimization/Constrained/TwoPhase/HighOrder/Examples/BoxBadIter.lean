/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Box

/-!
# A slow Phase-2 run on the square that satisfies the inner-test contract

This module gives runs of Phase 2 of the two-phase method TPqp-GC of [cartis2022evaluation],
Algorithm 14.3.2 (`Constrained.IsHighOrderTargetRun`), whose inner calls make one successful
iteration each and satisfy the inner-test contract
`Constrained.HighOrderTargetSeq.IsInnerTestContract`, and which nevertheless need
$N \sim (\varepsilon_0 \varepsilon_1)^{-1}$ outer iterations. The problem is that of
`Numlib.Optimization.Constrained.TwoPhase.HighOrder.Examples.Box` with the objective
$f(x) = x_1 - x_2$, the set $X = [-1, 1]^2$ and the constraint $c(x) = x_1^2/2$, with $\theta = 3/4$
and $q = 1$. Every outer iteration but the last is a case-(b) iteration whose call ends at a point
that passes the inner test (14.3.19). The run refutes Theorem 14.3.9 of [cartis2022evaluation] as
printed, for a nonspecific inner method (`CartisGouldToint.Chapter14.theorem_14_3_9_false`), and its
first call shows that the cost hypothesis of that theorem cannot be met for $\pi_1 < 2$
(`CartisGouldToint.Chapter14.theorem_14_3_9_cost_hypothesis_unsatisfiable`).

Let $u \in (0, 1/7]$ and $N \ge 1$ with $u^3 N \le 1$. The tolerances are
$\varepsilon_0 = u^2/2 + u^3/2$ and $\varepsilon_j = 3u/2$ for $j \ge 1$. Phase 2 starts at
$x_1 = (0, -1)$ with $t_1 = 1 - \varepsilon_0$. For $k < N$, the $k$-th call moves to a point
$x_{k+1} = (u, \cdot)$ with $f(x_{k+1}) = t_k - E_{k+1}$, where $E_j = \tfrac{u^3}{2} (1 - j/(4(N +
1))) \in [3u^3/8, u^3/2]$. At $x_{k+1}$ the gradient $\nabla \mu(x_{k+1}, t_k) = (u^3/2 - E_{k+1},
E_{k+1})$ has norm at most $u^3/2 \le \beta \|r(x_k, t_k)\| \varepsilon_1$, since
$\|r(x_k, t_k)\| \ge u^2/2$; this is the inner test. After the reflection (14.3.35) of the target,
the decrease along $-e_1$ is $u^3/2 + E_{k+1} \ge 7u^3/8 > \varepsilon_1 \|r(x_{k+1}, t_{k+1})\|$,
so the criticality test (14.3.34) fails. The targets drop by $2 E_{k+1} \approx u^3$, so about
$u^{-3}$ such iterations fit in $X$. The last call lands on its target, $f(x_{N+1}) = t_N$, where
the criticality test holds, and Phase 2 stops at $N$ in case (c).

## Main definitions

* `Constrained.TwoPhaseExample.BoxBadIter.tol`, `Constrained.TwoPhaseExample.BoxBadIter.target`,
  `Constrained.TwoPhaseExample.BoxBadIter.iter`: the tolerances, the targets and the outer iterates.
* `Constrained.TwoPhaseExample.BoxBadIter.seq`: the Phase-2 data, with one-step inner calls
  (`Constrained.HighOrderTargetSeq.oneStep`).

## Main results

* `Constrained.TwoPhaseExample.BoxBadIter.innerTest`: every call ends at a point that passes the
  inner test (14.3.19).
* `Constrained.TwoPhaseExample.BoxBadIter.isEnd`: Phase 2 terminates at the outer iteration $N$.
* `Constrained.TwoPhaseExample.BoxBadIter.isHighOrderTargetRun`: the data form a run of Phase 2.
* `Constrained.TwoPhaseExample.BoxBadIter.isInnerTestContract`: the calls satisfy the inner-test
  contract for $\beta \ge 2/3$ and all constants with $\kappa_{\mathrm{uns}} + \kappa_{\mathrm{unc}}
  \ge 1$ and $\rho_1 \le 1$.
* `Constrained.TwoPhaseExample.BoxBadIter.lt_taylorMeasure_start`: the inner test fails at the start
  of every call.
* `Constrained.TwoPhaseExample.BoxBadIter.two_le_costBound`: the cost bound of every call is at
  least $2$ for $\pi_1 \ge 4/3$.
* `Constrained.TwoPhaseExample.BoxBadIter.exists_params`: for every $C$ there are $u$ and $N$ with
  $N > C \max(\varepsilon_0^{-1}, \varepsilon_0^{1-\pi} \varepsilon_1^{-\pi})$ for all
  $\pi \le 3/2$.
* `Constrained.TwoPhaseExample.BoxBadIter.exists_seq`: the run for a given $C$, with its counts and
  its properties.
* `Constrained.TwoPhaseExample.BoxBadIter.exists_tol_start_lt_taylorMeasure`: tolerances for which
  the first call costs at least one evaluation, while a cost bound of order
  $\varepsilon_0^{2-\pi_1}$ is smaller than $1$.

## Implementation notes

* The coordinates $x_1$ and $x_2$ of $x \in \mathbb{R}^2$ are `x 0` and `x 1`. The objective is
  `Constrained.TwoPhaseExample.Box.obj 1`.
* The results take $q = 1$, $\theta = 3/4$ and all optimality radii $1$.
-/

open Set Metric
open scoped Nat RealInnerProductSpace

namespace Constrained.TwoPhaseExample.BoxBadIter

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ### The parameters and the run -/

section Run

variable (u : ℝ) (N : ℕ)

/-- The **tolerances** $\varepsilon_0 = u^2/2 + u^3/2$ and $\varepsilon_j = 3u/2$ for $j \ge 1$, for
a parameter $u \in \mathbb{R}$. -/
noncomputable def tol : ℕ → ℝ := fun j => if j = 0 then u ^ 2 / 2 + u ^ 3 / 2 else 3 * u / 2

/-- The overshoot $E_j = \tfrac{u^3}{2} \bigl(1 - j/(4(N + 1))\bigr)$: the $(j - 1)$-th inner call
ends this far below its target. -/
noncomputable def overshoot (j : ℕ) : ℝ := u ^ 3 / 2 * (1 - j / (4 * (N + 1)))

/-- The **targets**
$$t_k = 1 - \varepsilon_0 - u^3 (k - 1) + \frac{u^3 (k (k + 1) - 2)}{8 (N + 1)}, \qquad
  \varepsilon_0 = u^2/2 + u^3/2.$$

They satisfy $t_{k+1} = t_k - 2 E_{k+1}$ (`Constrained.TwoPhaseExample.BoxBadIter.target_succ`). -/
noncomputable def target (k : ℕ) : ℝ :=
  1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * ((k : ℝ) - 1) +
    u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1))

open Classical in
/-- The amount $t_k - f(x_{k+1})$ by which the $k$-th call ends below its target: $E_{k+1}$ for
$k < N$, and $0$ for $k \ge N$. -/
noncomputable def gap (k : ℕ) : ℝ := if k < N then overshoot u N (k + 1) else 0

/-- The **outer iterates**: $x_1 = (0, -1)$, and $x_{k+1} = (u, u - t_k + g_k)$ for $k \ge 1$, where
$g_k$ is `Constrained.TwoPhaseExample.BoxBadIter.gap`. Then $f(x_{k+1}) = t_k - g_k$.

The unused value at $k = 0$ is also $(0, -1)$. -/
noncomputable def iter : ℕ → ℝ²
  | 0 => pt 0 (-1)
  | k + 1 => if k = 0 then pt 0 (-1) else pt u (u - (target u N k - gap u N k))

/-- The **Phase-2 data** of the run: the outer iterates of
`Constrained.TwoPhaseExample.BoxBadIter.iter`, the targets of
`Constrained.TwoPhaseExample.BoxBadIter.target`, all optimality radii equal to $1$, and for each
$k$ an inner call that makes one successful iteration, from $x_k$ to $x_{k+1}$.

It is `Constrained.HighOrderTargetSeq.oneStep`. -/
noncomputable def seq : HighOrderTargetSeq ℝ² :=
  HighOrderTargetSeq.oneStep (iter u N) (target u N)

end Run

section Facts

variable {u : ℝ} {N : ℕ}

/-- $\varepsilon_0 = u^2/2 + u^3/2$. -/
theorem tol_zero : tol u 0 = u ^ 2 / 2 + u ^ 3 / 2 := by simp [tol]

/-- $\varepsilon_1 = 3u/2$. -/
theorem tol_one : tol u 1 = 3 * u / 2 := by simp [tol]

/-- $t_1 = 1 - \varepsilon_0$. -/
theorem target_one : target u N 1 = 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by simp [target]; norm_num

/-- The target update of case (b): $t_{k+1} = t_k - 2 E_{k+1}$ for every $k$. -/
theorem target_succ (k : ℕ) : target u N (k + 1) = target u N k - 2 * overshoot u N (k + 1) := by
  unfold target overshoot
  have : (8 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- $x_1 = (0, -1)$. -/
theorem iter_one : iter u N 1 = pt 0 (-1) := by simp [iter]

/-- $x_{k+1} = (u, u - t_k + g_k)$ for $k \ge 1$, where $g_k$ is
`Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem iter_succ {k : ℕ} (hk : 1 ≤ k) :
    iter u N (k + 1) = pt u (u - (target u N k - gap u N k)) := by
  simp [iter, show k ≠ 0 by omega]

/-- The first coordinate of $x_{k+1}$ is $u$ for $k \ge 1$. -/
theorem iter_succ_zero {k : ℕ} (hk : 1 ≤ k) : iter u N (k + 1) 0 = u := by
  rw [iter_succ hk, pt_zero]

/-- $f(x_{k+1}) = t_k - g_k$ for $k \ge 1$, where $g_k$ is
`Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem obj_iter_succ {k : ℕ} (hk : 1 ≤ k) :
    Box.obj 1 (iter u N (k + 1)) = target u N k - gap u N k := by
  rw [iter_succ hk, Box.obj_one_pt]; ring

/-- $g_k = E_{k+1}$ for $k < N$, where $g_k$ is `Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem gap_of_lt {k : ℕ} (hk : k < N) : gap u N k = overshoot u N (k + 1) := by simp [gap, hk]

/-- $g_N = 0$: the last call lands on its target. -/
theorem gap_self : gap u N N = 0 := by simp [gap]

variable (hu : 0 < u)
include hu

/-- For $u > 0$, $E_j \le u^3/2$ for every $j$. -/
theorem overshoot_le (j : ℕ) : overshoot u N j ≤ u ^ 3 / 2 := by
  unfold overshoot
  have : 0 ≤ (j : ℝ) / (4 * (N + 1)) := by positivity
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $E_j \ge 3u^3/8$ for $j \le N + 1$. -/
theorem le_overshoot {j : ℕ} (hj : j ≤ N + 1) : 3 / 4 * (u ^ 3 / 2) ≤ overshoot u N j := by
  unfold overshoot
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ 1 / 4 := by
    rw [div_le_iff₀ hN]
    have : (j : ℝ) ≤ N + 1 := by exact_mod_cast hj
    linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $E_{j+1} \le E_j$ for every $j$. -/
theorem overshoot_succ_le (j : ℕ) : overshoot u N (j + 1) ≤ overshoot u N j := by
  unfold overshoot
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) ≤ ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $E_{j+1} < E_j$ for every $j$. -/
theorem overshoot_succ_lt (j : ℕ) : overshoot u N (j + 1) < overshoot u N j := by
  unfold overshoot
  have hN : (0 : ℝ) < 4 * (N + 1) := by positivity
  have : (j : ℝ) / (4 * (N + 1)) < ((j + 1 : ℕ) : ℝ) / (4 * (N + 1)) := by
    gcongr; linarith
  have : 0 < u ^ 3 / 2 := by positivity
  nlinarith

/-- For $u > 0$, $g_k < E_k$ for $k \le N$, where $g_k$ is
`Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem gap_lt_overshoot {k : ℕ} (hk : k ≤ N) : gap u N k < overshoot u N k := by
  unfold gap
  split_ifs with h
  · exact overshoot_succ_lt hu k
  · exact (by positivity : (0 : ℝ) < 3 / 4 * (u ^ 3 / 2)).trans_le (le_overshoot hu (by omega))

/-- For $u > 0$, $g_k \ge 0$ for every $k$. -/
theorem gap_nonneg (k : ℕ) : 0 ≤ gap u N k := by
  unfold gap
  split_ifs with h
  · exact (by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans (le_overshoot hu (by omega))
  · exact le_rfl

/-- For $u > 0$, $g_k \le u^3/2$ for every $k$. -/
theorem gap_le (k : ℕ) : gap u N k ≤ u ^ 3 / 2 := by
  unfold gap
  split_ifs
  · exact overshoot_le hu _
  · positivity

/-- For $u > 0$ and $k \in [1, N]$, $1 - \varepsilon_0 - u^3 N \le t_k \le 1 - \varepsilon_0$. -/
theorem target_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    1 - (u ^ 2 / 2 + u ^ 3 / 2) - u ^ 3 * N ≤ target u N k ∧
      target u N k ≤ 1 - (u ^ 2 / 2 + u ^ 3 / 2) := by
  unfold target
  have hN : (0 : ℝ) < 8 * (N + 1) := by positivity
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hKN : (k : ℝ) ≤ N := by exact_mod_cast hkN
  have hu3 : 0 < u ^ 3 := by positivity
  have h0 : 0 ≤ u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) := by
    apply div_nonneg _ hN.le
    apply mul_nonneg hu3.le
    nlinarith
  have h1 : u ^ 3 * ((k : ℝ) * (k + 1) - 2) / (8 * (N + 1)) ≤ u ^ 3 * ((k : ℝ) - 1) := by
    rw [div_le_iff₀ hN]
    have : ((k : ℝ) * (k + 1) - 2) ≤ ((k : ℝ) - 1) * (8 * (N + 1)) := by nlinarith
    nlinarith
  constructor <;> nlinarith

end Facts

section Run2

variable {u : ℝ} {N : ℕ} (hu : 0 < u) (hu7 : u ≤ 1 / 7) (hNu : u ^ 3 * N ≤ 1)
include hu

omit hu in
/-- For $k \in [1, N)$, $f(x_{k+1}) - t_{k+1} = E_{k+1}$. -/
theorem obj_iter_succ_sub_target_succ {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    Box.obj 1 (iter u N (k + 1)) - target u N (k + 1) = overshoot u N (k + 1) := by
  rw [obj_iter_succ hk1, gap_of_lt hkN, target_succ]; ring

omit hu in
/-- For $k \ge 1$, $f(x_{k+1}) - t_k = -g_k$, where $g_k$ is
`Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem obj_iter_succ_sub_target {k : ℕ} (hk1 : 1 ≤ k) :
    Box.obj 1 (iter u N (k + 1)) - target u N k = -gap u N k := by
  rw [obj_iter_succ hk1]; ring

include hu7 hNu in
/-- Let $0 < u \le 1/7$ and $u^3 N \le 1$. The iterates $x_k$ with $k \in [1, N + 1]$ lie in $X$. -/
theorem iter_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N + 1) : iter u N k ∈ Box.square := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [iter_one]; simp [Box.square]
  · rw [iter_succ hj]
    obtain ⟨h1, h2⟩ := target_mem hu hj (by omega : j ≤ N)
    have hg0 := gap_nonneg hu (N := N) j
    have hg1 := gap_le hu (N := N) j
    have hu2 : u ^ 2 ≤ u / 7 := by nlinarith
    have hu3 : u ^ 3 ≤ u ^ 2 / 7 := by nlinarith
    simp only [Box.square, mem_ofPred_eq, pt_zero, pt_one]
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

omit hu in
/-- At a point $y$ with first coordinate $u$, $\|r(y, t)\|^2 = (u^2/2)^2 + (f(y) - t)^2$ for every
target $t$. -/
theorem targetResidual_sq_of_apply_zero {y : ℝ²} (hy : y 0 = u) (t : ℝ) :
    targetResidual (Box.obj 1) Box.con t y ^ 2 = (u ^ 2 / 2) ^ 2 + (Box.obj 1 y - t) ^ 2 := by
  rw [Box.targetResidual_sq, hy]

omit hu in
/-- For $k \ge 1$, $\|r(x_{k+1}, t_k)\|^2 = (u^2/2)^2 + g_k^2$, where $g_k$ is
`Constrained.TwoPhaseExample.BoxBadIter.gap`. -/
theorem targetResidual_end_sq {k : ℕ} (hk1 : 1 ≤ k) :
    targetResidual (Box.obj 1) Box.con (target u N k) (iter u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + gap u N k ^ 2 := by
  rw [targetResidual_sq_of_apply_zero (iter_succ_zero hk1), obj_iter_succ_sub_target hk1]; ring

omit hu in
/-- For $k \in [1, N)$, $\|r(x_{k+1}, t_{k+1})\|^2 = (u^2/2)^2 + E_{k+1}^2$. -/
theorem targetResidual_new_sq {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    targetResidual (Box.obj 1) Box.con (target u N (k + 1)) (iter u N (k + 1)) ^ 2 =
      (u ^ 2 / 2) ^ 2 + overshoot u N (k + 1) ^ 2 := by
  rw [targetResidual_sq_of_apply_zero (iter_succ_zero hk1), obj_iter_succ_sub_target_succ hk1 hkN]

/-- For $u > 0$ and $k \in [1, N]$, $\|r(x_k, t_k)\|^2 \ge (u^2/2)^2 + E_k^2$. -/
theorem le_targetResidual_sq {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (u ^ 2 / 2) ^ 2 + overshoot u N k ^ 2 ≤
      targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Box.targetResidual_sq, iter_one, target_one, Box.obj_one_pt]
    simp only [pt_zero]
    have h0 := le_overshoot hu (N := N) (j := 1) (by omega)
    have h1 := overshoot_le hu (N := N) 1
    have : 0 < u ^ 2 / 2 := by positivity
    nlinarith
  · rw [targetResidual_new_sq hj (by omega)]

omit hu in
/-- For $u > 0$, $\|r(x_1, t_1)\| = \varepsilon_0 = u^2/2 + u^3/2$. -/
theorem targetResidual_one (hu : 0 < u) :
    targetResidual (Box.obj 1) Box.con (target u N 1) (iter u N 1) = u ^ 2 / 2 + u ^ 3 / 2 := by
  rw [Constrained.targetResidual_def, iter_one, Box.norm_con, target_one, Box.obj_one_pt]
  simp only [pt_zero]
  rw [show ((0 : ℝ) ^ 2 / 2) ^ 2 + (0 - -1 - (1 - (u ^ 2 / 2 + u ^ 3 / 2))) ^ 2 =
    (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

/-- For $u > 0$ and $k \in [1, N]$, $u^2/2 \le \|r(x_k, t_k)\| \le u^2/2 + u^3/2 = \varepsilon_0$.
-/
theorem targetResidual_mem {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    u ^ 2 / 2 ≤ targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) ∧
      targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) ≤
        u ^ 2 / 2 + u ^ 3 / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [targetResidual_one hu]; constructor <;> nlinarith [pow_pos hu 3]
  · have h := Real.le_and_le_add_of_sq_eq_add_sq targetResidual_nonneg
      (targetResidual_new_sq hj (by omega))
      (by positivity) ((by positivity : (0 : ℝ) ≤ 3 / 4 * (u ^ 3 / 2)).trans
        (le_overshoot hu (N := N) (j := j + 1) (by omega)))
    exact ⟨h.1, h.2.trans (by linarith [overshoot_le hu (N := N) (j + 1)])⟩

/-- For $u > 0$ and $k \in [1, N]$, $\|r(x_k, t_k)\| \ge u^2/2$. -/
theorem le_targetResidual {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    u ^ 2 / 2 ≤ targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) :=
  (targetResidual_mem hu hk1 hkN).1

/-- For $u > 0$ and $k \in [1, N]$, $\|r(x_k, t_k)\| \le u^2/2 + u^3/2 = \varepsilon_0$. -/
theorem targetResidual_le {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) ≤ u ^ 2 / 2 + u ^ 3 / 2 :=
  (targetResidual_mem hu hk1 hkN).2

omit hu in
/-- For $k \ge 1$, $\|r(x_{k+1}, t_k)\| \ge u^2/2$. -/
theorem le_targetResidual_end {k : ℕ} (hk1 : 1 ≤ k) :
    u ^ 2 / 2 ≤ targetResidual (Box.obj 1) Box.con (target u N k) (iter u N (k + 1)) := by
  have h := targetResidual_end_sq (u := u) (N := N) hk1
  have := Constrained.targetResidual_nonneg (f := Box.obj 1) (c := Box.con) (t := target u N k)
    (x := iter u N (k + 1))
  nlinarith [sq_nonneg (gap u N k)]

include hu7 hNu in
/-- **The inner test holds at the end of every call.** Let $0 < u \le 1/7$, $u^3 N \le 1$ and
$\beta \ge 2/3$. For every $k \in [1, N]$, the inner test (14.3.19) holds at the end $x_{k+1}$
of the $k$-th call, with $q = 1$ and the radius $1$:
$$\phi^1_{\mu, X(x_{k+1}), 1}(x_{k+1}, t_k) \le \beta\, \|r(x_k, t_k)\|\, \varepsilon_1.$$

The left side is the first-order measure of $\mu(\cdot, t_k)$ at $x_{k+1}$ with radius $1$ on
$X(x_{k+1}) = \{d : x_{k+1} + d \in X\}$. It is at most
$\|\nabla \mu(x_{k+1}, t_k)\| \le u^3/2$, and $u^3/2 \le \beta \|r(x_k, t_k)\| \varepsilon_1$.
The test is `Constrained.HighOrderTargetSeq.InnerTest`. -/
theorem innerTest {β : ℝ} (hβ : 2 / 3 ≤ β) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (seq u N).InnerTest (Box.obj 1) Box.con Box.square 1 β (tol u) k := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  change Optimization.taylorMeasure
      (ftaylorSeries ℝ (targetMerit (Box.obj 1) Box.con (target u N k)) (iter u N (k + 1))) 1 1
      {d | iter u N (k + 1) + d ∈ Box.square} ≤
    β * targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) * tol u 1 * 1 ^ 1 / (1 : ℕ)!
  have h0 : (0 : ℝ²) ∈ {d | iter u N (k + 1) + d ∈ Box.square} := by
    simpa using iter_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  refine (Box.taylorMeasure_le _ _ h0).trans ?_
  rw [iter_succ_zero hk1, obj_iter_succ_sub_target hk1, tol_one]
  have hg0 := gap_nonneg hu (N := N) k
  have hg1 := gap_le hu (N := N) k
  have hR := le_targetResidual hu hk1 hkN
  have hs : √((u ^ 3 / 2 + -gap u N k) ^ 2 + (-gap u N k) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have : β * (u ^ 2 / 2) * (3 * u / 2) ≤
      β * targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) * (3 * u / 2) := by
    gcongr
  nlinarith

include hu7 hNu in
/-- Let $0 < u \le 1/7$ and $u^3 N \le 1$. For $k \in [1, N)$, the criticality test (14.3.34) fails
at $(x_{k+1}, t_{k+1})$ with $q = 1$ and the radius $1$: along $d = -e_1$ the decrease is
$u^3/2 + E_{k+1} \ge 7u^3/8 > \varepsilon_1 \|r(x_{k+1}, t_{k+1})\|$. -/
theorem not_targetCrit_new {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ targetCrit (Box.obj 1) Box.con Box.square 1 (tol u) (target u N (k + 1)) (iter u N (k + 1))
      (fun _ => 1) := by
  intro h
  have h1 := h 1 (by simp)
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  have hmem := iter_mem hu hu7 hNu (k := k + 1) (by omega) (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | iter u N (k + 1) + d ∈ Box.square} := by
    simp only [Box.square, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero, iter_succ_zero hk1]
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  have hlow := Box.le_taylorMeasure (iter u N (k + 1)) (target u N (k + 1)) hS
  rw [iter_succ_zero hk1, obj_iter_succ_sub_target_succ hk1 hkN] at hlow
  rw [tol_one] at h1
  have hov := le_overshoot hu (N := N) (j := k + 1) (by omega)
  have hR := targetResidual_le hu (N := N) (k := k + 1) (by omega) (by omega)
  have : 3 * u / 2 * targetResidual (Box.obj 1) Box.con (target u N (k + 1)) (iter u N (k + 1)) ≤
      3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) := by gcongr
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  have e : 3 * u / 2 * (u ^ 2 / 2 + u ^ 3 / 2) = 3 / 4 * u ^ 3 + 3 / 4 * u ^ 4 := by ring
  linarith

include hu7 hNu in
/-- Let $0 < u \le 1/7$, $u^3 N \le 1$ and $N \ge 1$. The criticality test (14.3.34), the third test
of (14.3.32), holds at $(x_{N+1}, t_N)$ with $q = 1$ and the radius $1$: $\|\nabla \mu(x_{N+1},
t_N)\| = u^3/2 \le \varepsilon_1 \|r(x_{N+1}, t_N)\| = 3u^3/4$. -/
theorem targetCrit_end (hN : 1 ≤ N) :
    targetCrit (Box.obj 1) Box.con Box.square 1 (tol u) (target u N N) (iter u N (N + 1))
      (fun _ => 1) := by
  intro j hj
  obtain rfl : j = 1 := by simpa using hj
  simp only [one_pow, mul_one, Nat.factorial_one, Nat.cast_one, div_one]
  have h0 : (0 : ℝ²) ∈ {d | iter u N (N + 1) + d ∈ Box.square} := by
    simpa using iter_mem hu hu7 hNu (k := N + 1) (by omega) le_rfl
  refine (Box.taylorMeasure_le _ _ h0).trans ?_
  rw [iter_succ_zero hN, obj_iter_succ_sub_target hN, gap_self, tol_one]
  have hR := le_targetResidual_end (u := u) (N := N) hN
  have hs : √((u ^ 3 / 2 + -0) ^ 2 + (-0) ^ 2) ≤ u ^ 3 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  refine hs.trans ?_
  have : 3 * u / 2 * (u ^ 2 / 2) ≤
      3 * u / 2 * targetResidual (Box.obj 1) Box.con (target u N N) (iter u N (N + 1)) := by
    gcongr
  nlinarith

/-- For $u > 0$, the merit function $\mu(\cdot, t_k)$ decreases strictly along every call
$k \in [1, N]$: $\mu(x_{k+1}, t_k) < \mu(x_k, t_k)$. -/
theorem targetMerit_lt {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    targetMerit (Box.obj 1) Box.con (target u N k) (iter u N (k + 1)) <
      targetMerit (Box.obj 1) Box.con (target u N k) (iter u N k) := by
  rw [Constrained.targetMerit_eq, Constrained.targetMerit_eq, targetResidual_end_sq hk1]
  have h1 := le_targetResidual_sq hu hk1 hkN
  have h2 := gap_nonneg hu (N := N) k
  have h3 := gap_lt_overshoot hu (N := N) hkN
  nlinarith

include hu7 in
/-- For $0 < u \le 1/7$, $\theta \varepsilon_0 \le u^2/2$ with $\theta = 3/4$. -/
theorem three_quarters_mul_tol_le : 3 / 4 * tol u 0 ≤ u ^ 2 / 2 := by
  rw [tol_zero]; nlinarith [pow_pos hu 2]

omit hu in
/-- For $u > 0$, the tolerances are positive: $\varepsilon_j > 0$ for every $j$. -/
theorem tol_pos (hu : 0 < u) (j : ℕ) : 0 < tol u j := by
  unfold tol; split_ifs <;> positivity

include hu7 in
/-- For $0 < u \le 1/7$, the tolerances are at most $1$: $\varepsilon_j \le 1$ for every $j$. -/
theorem tol_le_one (j : ℕ) : tol u j ≤ 1 := by
  unfold tol; split_ifs <;> nlinarith [pow_pos hu 2, pow_pos hu 3]

include hu7 in
/-- For $0 < u \le 1/7$, no outer iteration $k \ge 1$ is in $\mathcal{K}_a$ for $\theta = 3/4$. -/
theorem not_isKa {k : ℕ} (hk1 : 1 ≤ k) :
    ¬ (seq u N).IsKa (Box.obj 1) Box.con (3 / 4) (tol u) k := by
  rw [Constrained.HighOrderTargetSeq.isKa_iff]
  rw [not_lt]
  exact (three_quarters_mul_tol_le hu hu7).trans (le_targetResidual_end hk1)

include hu7 in
/-- For $0 < u \le 1/7$, the outer iterations $k \in [1, N)$ are in $\mathcal{K}_b$ for
$\theta = 3/4$. -/
theorem isKb {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    (seq u N).IsKb (Box.obj 1) Box.con (3 / 4) (tol u) k := by
  refine ⟨(three_quarters_mul_tol_le hu hu7).trans (le_targetResidual_end hk1), ?_⟩
  change Box.obj 1 (iter u N (k + 1)) < target u N k
  rw [obj_iter_succ hk1, gap_of_lt hkN]
  have := le_overshoot hu (N := N) (j := k + 1) (by omega)
  have : 0 < u ^ 3 := by positivity
  linarith

omit hu in
/-- For $N \ge 1$, the outer iteration $N$ is not in $\mathcal{K}_b$ for $\theta = 3/4$, since
$f(x_{N+1}) = t_N$. -/
theorem not_isKb_self (hN : 1 ≤ N) : ¬ (seq u N).IsKb (Box.obj 1) Box.con (3 / 4) (tol u) N := by
  intro h
  have h2 := h.2
  change Box.obj 1 (iter u N (N + 1)) < target u N N at h2
  rw [obj_iter_succ hN, gap_self] at h2
  linarith

include hu7 in
/-- For $0 < u \le 1/7$ and $N \ge 1$, Phase 2 stops at the outer iteration $N$, in case (c), for
$q = 1$ and $\theta = 3/4$. -/
theorem stop_self (hN : 1 ≤ N) :
    (seq u N).Stop (Box.obj 1) Box.con Box.square 1 (3 / 4) (tol u) N :=
  Or.inl ⟨not_isKa hu hu7 hN, not_isKb_self hN⟩

include hu7 hNu in
/-- Let $0 < u \le 1/7$ and $u^3 N \le 1$. Phase 2 does not stop at the outer iterations
$k \in [1, N)$, for $q = 1$ and $\theta = 3/4$. -/
theorem not_stop {k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    ¬ (seq u N).Stop (Box.obj 1) Box.con Box.square 1 (3 / 4) (tol u) k := by
  rintro (⟨-, hb⟩ | ⟨-, hm⟩)
  · exact hb (isKb hu hu7 hk1 hkN)
  · exact not_targetCrit_new hu hu7 hNu hk1 hkN hm

include hu7 hNu in
/-- Let $0 < u \le 1/7$ and $u^3 N \le 1$. No outer iteration $j \in [1, N)$ terminates Phase 2, for
$q = 1$ and $\theta = 3/4$. -/
theorem before_self : (seq u N).Before (Box.obj 1) Box.con Box.square 1 (3 / 4) (tol u) N :=
  fun _ hj1 hjN => not_stop hu hu7 hNu hj1 hjN

include hu7 in
/-- Let $0 < u \le 1/7$ and $N \ge 1$. Every outer iteration $k$ that is reached, for $q = 1$ and
$\theta = 3/4$, satisfies $k \le N$. -/
theorem le_of_before (hN : 1 ≤ N) {k : ℕ}
    (h : (seq u N).Before (Box.obj 1) Box.con Box.square 1 (3 / 4) (tol u) k) : k ≤ N := by
  by_contra hk
  exact h N hN (by omega) (stop_self hu hu7 hN)

include hu7 hNu in
/-- **Phase 2 terminates at $N$.** Let $0 < u \le 1/7$, $N \ge 1$ and $u^3 N \le 1$. For the data
`Constrained.TwoPhaseExample.BoxBadIter.seq u N` with $q = 1$, $\theta = 3/4$ and the tolerances
`Constrained.TwoPhaseExample.BoxBadIter.tol u`, Phase 2 terminates at the outer iteration $N$
(`Constrained.HighOrderTargetSeq.IsEnd`). -/
theorem isEnd (hN : 1 ≤ N) : (seq u N).IsEnd (Box.obj 1) Box.con Box.square 1 (3 / 4) (tol u) N :=
  ⟨hN, stop_self hu hu7 hN, before_self hu hu7 hNu⟩

include hu7 hNu in
/-- **The data form a run of Phase 2.** Let $0 < u \le 1/7$, $N \ge 1$ and $u^3 N \le 1$, and let
$0 < \beta \le 3/4$. The data `Constrained.TwoPhaseExample.BoxBadIter.seq u N` form a run of
Phase 2 (`Constrained.IsHighOrderTargetRun`) for the objective $f(x) = x_1 - x_2$, the
constraint $c$ and the set $X$, from $x_1 = (0, -1)$, with $q = 1$, $\theta = 3/4$, the constant
$\beta$ and the tolerances `Constrained.TwoPhaseExample.BoxBadIter.tol u`. -/
theorem isHighOrderTargetRun (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) :
    IsHighOrderTargetRun (Box.obj 1) Box.con Box.square 1 (3 / 4) β (tol u) (pt 0 (-1))
      (seq u N) := by
  have hc1 : ‖Box.con (pt 0 (-1))‖ = 0 := by rw [Box.norm_con]; simp
  rw [← iter_one (u := u) (N := N)]
  refine isHighOrderTargetRun_oneStep (by norm_num) (by norm_num) hβ hβθ (fun j _ => tol_pos hu j)
    (fun j _ => tol_le_one hu hu7 j) (by rw [iter_one]; simp [Box.square]) ?_ ?_
    (fun k hk1 hk => iter_mem hu hu7 hNu (by omega) (by have := le_of_before hu hu7 hN hk; omega))
    (fun k hk1 hk => ?_) (fun k hk1 hk => targetMerit_lt hu hk1 (le_of_before hu hu7 hN hk) |>.le)
    (fun k hk1 hk => (three_quarters_mul_tol_le hu hu7).trans
      (le_targetResidual hu hk1 (le_of_before hu hu7 hN hk)))
    (fun k hk1 _ ha => absurd ha (not_isKa hu hu7 hk1)) fun k hk1 hk hb => ?_
  · rw [iter_one, hc1]; exact (mul_pos (by norm_num) (tol_pos hu 0)).le
  · rw [iter_one, hc1, target_one, Box.obj_one_pt, tol_zero]
    rw [show (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 - (0 : ℝ) ^ 2 = (u ^ 2 / 2 + u ^ 3 / 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    ring
  · rcases Nat.lt_or_ge k N with hlt | hge
    · exact Or.inr (Or.inl (isKb hu hu7 hk1 hlt).2)
    · obtain rfl : k = N := by have := le_of_before hu hu7 hN hk; omega
      exact Or.inr (Or.inr (targetCrit_end hu hu7 hNu hN))
  · have hlt : k < N :=
      lt_of_le_of_ne (le_of_before hu hu7 hN hk) fun h => not_isKb_self hN (h ▸ hb)
    rw [obj_iter_succ hk1, gap_of_lt hlt, target_succ]
    ring

include hu7 hNu in
/-- **The inner calls satisfy the inner-test contract.** Let $0 < u \le 1/7$, $N \ge 1$ and
$u^3 N \le 1$. Let $\beta \ge 2/3$, let $\kappa_{\mathrm{decr}}$ be any constant, let $\pi_j$ be
any exponents, let $\kappa_{\mathrm{uns}} + \kappa_{\mathrm{unc}} \ge 1$, and let the radii
$\rho_j$ satisfy $\rho_1 \le 1$. Then the inner calls of
`Constrained.TwoPhaseExample.BoxBadIter.seq u N` satisfy the inner-test contract
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with these constants, for $q = 1$ and
$\theta = 3/4$.

Each call makes one successful iteration and ends at a point that passes the inner test
(`Constrained.TwoPhaseExample.BoxBadIter.innerTest`), so no decrease is required, and the
returned radii are $1 \ge \rho_1$. -/
theorem isInnerTestContract (hN : 1 ≤ N) {β : ℝ} (hβ : 2 / 3 ≤ β) {κdecr κuns κunc : ℝ}
    {π ρ : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc) (hρ : ρ 1 ≤ 1) :
    (seq u N).IsInnerTestContract (Box.obj 1) Box.con Box.square 1 (3 / 4) β (tol u) κdecr κuns
      κunc π ρ :=
  HighOrderTargetSeq.isInnerTestContract_oneStep hκ
    (fun j hj => by obtain rfl : j = 1 := by simpa using hj
                    exact hρ)
    fun k hk1 hk => innerTest hu hu7 hNu hβ hk1 (le_of_before hu hu7 hN hk)

include hu7 hNu in
/-- **The inner test fails at the start of every call.** Let $0 < u \le 1/7$, $u^3 N \le 1$ and
$\beta \le 3/4$. For every $k \in [1, N]$,
$$\beta\, \|r(x_k, t_k)\|\, \varepsilon_1 < \phi^1_{\mu, X(x_k), 1}(x_k, t_k),$$
the first-order measure of $\mu(\cdot, t_k)$ at $x_k$ with radius $1$ on
$X(x_k) = \{d : x_k + d \in X\}$.

The bound is the decrease of the linear model of $\mu(\cdot, t_k)$ at $x_k$ along $-e_1$. So an
inner method that terminates only at points that pass its test moves in every call. -/
theorem lt_taylorMeasure_start {β : ℝ} (hβ : β ≤ 3 / 4) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    β * targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) * tol u 1 <
      Optimization.taylorMeasure
        (ftaylorSeries ℝ (targetMerit (Box.obj 1) Box.con (target u N k)) (iter u N k)) 1 1
        {d | iter u N k + d ∈ Box.square} := by
  have hmem := iter_mem hu hu7 hNu (k := k) hk1 (by omega)
  have hS : EuclideanSpace.single 0 (-1) ∈ {d | iter u N k + d ∈ Box.square} := by
    simp only [Box.square, mem_ofPred_eq] at hmem ⊢
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 0 = -1 := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)) 1 = 0 := by simp
    simp only [PiLp.add_apply, e0, e1, add_zero]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [iter_one]; simp
    · rw [iter_succ_zero hj]
      exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, hmem.2⟩
  refine lt_of_lt_of_le ?_ (Box.le_taylorMeasure (iter u N k) (target u N k) hS)
  rw [tol_one]
  have hb : β * targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) * (3 * u / 2) ≤
      3 / 4 * (u ^ 2 / 2 + u ^ 3 / 2) * (3 * u / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hβ (targetResidual_le hu hk1 hkN)
      Constrained.targetResidual_nonneg (by norm_num)) (by positivity)
  refine hb.trans_lt ?_
  have hu3 : 0 < u ^ 3 := by positivity
  have hu4 : u ^ 4 ≤ u ^ 3 / 7 := by nlinarith
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `x₁ = (0, -1)`: the decrease is `ε₀`
    rw [iter_one, Box.obj_one_pt, target_one]
    simp only [pt_zero]
    nlinarith [pow_pos hu 2]
  · -- `x_k = (u, ·)` with `f(x_k) - t_k = E_k ≥ 3u³/8`
    rw [iter_succ_zero hj, obj_iter_succ_sub_target_succ hj (by omega)]
    nlinarith [le_overshoot hu (N := N) (j := j + 1) (by omega)]

include hu7 in
/-- **The cost bound of every call is at least $2$.** Let $0 < u \le 1/7$, $0 < \beta \le 3/4$,
$\kappa \ge 8$, and let the exponents $\pi_j$ satisfy $\pi_1 \ge 4/3$. For every $k \in [1, N]$,
$$2 \le \kappa\, \mu(x_k, t_k)\, \bigl(\beta \|r(x_k, t_k)\| \varepsilon_1\bigr)^{-\pi_1}.$$

The right side is the cost bound of an inner method on $\mu(\cdot, t_k)$ from $x_k$ with the
tolerance $\beta \|r(x_k, t_k)\| \varepsilon_1$ and the lower bound $0$ of $\mu$. With
$R = \|r(x_k, t_k)\| \ge u^2/2$ and $w = \beta R \varepsilon_1$, one has $w \le 1$ and
$w^4 \le (2R^2)^3$, so $w^{\pi_1} \le w^{4/3} \le 2R^2$ and the bound is at least $\kappa/4$. -/
theorem two_le_costBound {β : ℝ} (hβ : 0 < β) (hβθ : β ≤ 3 / 4) {κ : ℝ} (hκ : 8 ≤ κ)
    {π : ℕ → ℝ} (hπ : 4 / 3 ≤ π 1) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    2 ≤ κ * targetMerit (Box.obj 1) Box.con (target u N k) (iter u N k) *
      (β * targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) * tol u 1) ^ (-π 1) := by
  simp only [Constrained.targetMerit_eq, tol_one]
  set R := targetResidual (Box.obj 1) Box.con (target u N k) (iter u N k) with hR_def
  have hRlo := le_targetResidual hu hk1 hkN
  have hRhi := targetResidual_le hu hk1 hkN
  have hR : 0 < R := lt_of_lt_of_le (by positivity) hRlo
  have hu2 : u ^ 2 ≤ 2 * R := by linarith
  set w := β * R * (3 * u / 2) with hw_def
  have hw0 : 0 < w := by positivity
  have hwle : w ≤ 9 / 8 * R * u := by
    rw [hw_def]
    have : β * R ≤ 3 / 4 * R := by gcongr
    nlinarith
  have hw1 : w ≤ 1 := by
    have : R ≤ 1 := by nlinarith [pow_pos hu 2, pow_pos hu 3]
    nlinarith
  have hw4 : w ^ 4 ≤ (2 * R ^ 2) ^ 3 := by
    calc w ^ 4 ≤ (9 / 8 * R * u) ^ 4 := by gcongr
      _ = (9 / 8) ^ 4 * R ^ 4 * (u ^ 2) ^ 2 := by ring
      _ ≤ (9 / 8) ^ 4 * R ^ 4 * (2 * R) ^ 2 := by gcongr
      _ ≤ (2 * R ^ 2) ^ 3 := by nlinarith [pow_pos hR 6]
  have hw43 : w ^ (4 / 3 : ℝ) ≤ 2 * R ^ 2 := by
    have e : w ^ (4 / 3 : ℝ) = (w ^ (4 : ℕ)) ^ (((3 : ℕ) : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]; norm_num
    rw [e, ← Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ 2 * R ^ 2) (by norm_num : 3 ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hw4 (by positivity)
  have hwπ : w ^ π 1 ≤ 2 * R ^ 2 := (Real.rpow_le_rpow_of_exponent_ge hw0 hw1 hπ).trans hw43
  have hwπ0 : 0 < w ^ π 1 := Real.rpow_pos_of_pos hw0 _
  rw [Real.rpow_neg hw0.le, ← div_eq_mul_inv, le_div_iff₀ hwπ0]
  nlinarith [sq_nonneg R]

end Run2

/-! ### The order of the number of outer iterations -/

/-- Let $u = 1/m$ with $m \ge 7$, and let $\pi \le 3/2$. Then $\max(\varepsilon_0^{-1},
\varepsilon_0^{1-\pi} \varepsilon_1^{-\pi}) \le 2 m^2 \sqrt m$. -/
theorem order_le {m : ℕ} (hm : 7 ≤ m) {π : ℝ} (hπ : π ≤ 3 / 2) :
    max (tol (1 / m) 0)⁻¹ (tol (1 / m) 0 ^ (1 - π) * tol (1 / m) 1 ^ (-π)) ≤
      2 * (m : ℝ) ^ 2 * √m := by
  have hm1 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hum : u * m = 1 := by rw [hu_def]; field_simp
  rw [tol_zero, tol_one]
  set e0 := u ^ 2 / 2 + u ^ 3 / 2 with he0
  have he0pos : 0 < e0 := by positivity
  have he0inv : e0⁻¹ ≤ 2 * (m : ℝ) ^ 2 := by
    rw [inv_le_comm₀ he0pos (by positivity)]
    have : (2 * (m : ℝ) ^ 2)⁻¹ = u ^ 2 / 2 := by rw [hu_def]; field_simp
    rw [this]
    have : 0 < u ^ 3 := by positivity
    linarith
  have he0le : e0 ≤ 1 := by
    have : u ≤ 1 / 7 := by
      rw [hu_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  have hsq1 : 1 ≤ √(m : ℝ) := by rw [Real.one_le_sqrt]; linarith
  -- `ε₀^{1-π} ≤ 2m`
  have hA : e0 ^ (1 - π) ≤ 2 * m := by
    rcases le_or_gt π 1 with h1 | h1
    · exact (Real.rpow_le_one he0pos.le he0le (by linarith)).trans (by linarith)
    · have hinv1 : 1 ≤ e0⁻¹ := one_le_inv_iff₀.2 ⟨he0pos, he0le⟩
      rw [show 1 - π = -(π - 1) by ring, Real.rpow_neg he0pos.le, ← Real.inv_rpow he0pos.le]
      calc e0⁻¹ ^ (π - 1) ≤ e0⁻¹ ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hinv1 (by linarith)
        _ = √(e0⁻¹) := (Real.sqrt_eq_rpow _).symm
        _ ≤ √((2 * m) ^ 2) := Real.sqrt_le_sqrt (he0inv.trans (by nlinarith))
        _ = 2 * m := Real.sqrt_sq (by positivity)
  -- `ε₁^{-π} ≤ m √m`
  have hB : (3 * u / 2) ^ (-π) ≤ m * √m := by
    have h3 : (3 * u / 2)⁻¹ = 2 * m / 3 := by rw [hu_def]; field_simp
    have h31 : 1 ≤ 2 * (m : ℝ) / 3 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), h3]
    calc (2 * (m : ℝ) / 3) ^ π ≤ (2 * m / 3) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h31 hπ
      _ ≤ (m : ℝ) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = m * √m := by
          rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hm0, Real.rpow_one,
            ← Real.sqrt_eq_rpow]
  refine max_le (he0inv.trans (le_mul_of_one_le_right (by positivity) hsq1)) ?_
  calc e0 ^ (1 - π) * (3 * u / 2) ^ (-π) ≤ (2 * m) * (m * √m) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 2 * (m : ℝ) ^ 2 * √m := by ring

/-- Let $m \ge 7$ and $C \in \mathbb{R}$ with $4C^2 < m$. Every $x$ with $0 \le x \le 2 m^2 \sqrt m$
satisfies $C x < m^3$. -/
theorem lt_cube {m : ℕ} {C : ℝ} (hm : 7 ≤ m) (hC : 4 * C ^ 2 < m) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ 2 * (m : ℝ) ^ 2 * √m) : C * x < ((m ^ 3 : ℕ) : ℝ) := by
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  push_cast
  rcases le_or_gt C 0 with h | h
  · nlinarith [pow_pos hm0 3, mul_nonpos_of_nonpos_of_nonneg h hx0]
  · have hs : 2 * C < √m := by
      rw [Real.lt_sqrt (by positivity)]; nlinarith
    have hsq : √(m : ℝ) * √m = m := Real.mul_self_sqrt hm0.le
    calc C * x ≤ C * (2 * (m : ℝ) ^ 2 * √m) := by gcongr
      _ = (2 * C) * √m * m ^ 2 := by ring
      _ < √m * √m * m ^ 2 := by
          have : 0 < √(m : ℝ) := Real.sqrt_pos.2 hm0
          gcongr
      _ = (m : ℝ) ^ 3 := by rw [hsq]; ring

/-- **The parameters for a constant $C$.** For every $C \in \mathbb{R}$ there are $u \in \mathbb{R}$
and $N \in \mathbb{N}$ with $0 < u \le 1/7$, $u^3 N \le 1$ and $N \ge 1$ such that, for the
tolerances `Constrained.TwoPhaseExample.BoxBadIter.tol u`:

* if $C \ge 1$, then $\varepsilon_0 \le C^{-1}$ and $\varepsilon_1 \le C^{-1}$;
* for every $\pi \le 3/2$, $C \max(\varepsilon_0^{-1}, \varepsilon_0^{1-\pi}
  \varepsilon_1^{-\pi}) < N$.

The proof takes $u = 1/m$ and $N = m^3$ with $m = \lceil 4C^2 \rceil + 7$. -/
theorem exists_params (C : ℝ) : ∃ (u : ℝ) (N : ℕ), 0 < u ∧ u ≤ 1 / 7 ∧ u ^ 3 * N ≤ 1 ∧ 1 ≤ N ∧
    (1 ≤ C → tol u 0 ≤ C⁻¹ ∧ tol u 1 ≤ C⁻¹) ∧
    ∀ π : ℝ, π ≤ 3 / 2 → C * max (tol u 0)⁻¹ (tol u 0 ^ (1 - π) * tol u 1 ^ (-π)) < N := by
  set m : ℕ := ⌈4 * C ^ 2⌉₊ + 7 with hm_def
  have hm : 7 ≤ m := by omega
  have hm7 : (7 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hC : 4 * C ^ 2 < m := by
    have := Nat.le_ceil (4 * C ^ 2)
    rw [hm_def]; push_cast; linarith
  set u : ℝ := 1 / m with hu_def
  have hu : 0 < u := by positivity
  have hu7 : u ≤ 1 / 7 := by rw [hu_def, div_le_div_iff₀ hmR (by norm_num)]; linarith
  refine ⟨u, m ^ 3, hu, hu7, ?_, Nat.one_le_pow _ _ (by omega), fun hC1 => ?_, fun π hπ => ?_⟩
  · rw [hu_def]; push_cast; field_simp; exact le_rfl
  · have hmC : 2 * C ≤ m := by nlinarith
    have hε1 : tol u 1 ≤ C⁻¹ := by
      rw [tol_one, hu_def, le_inv_comm₀ (by positivity) (by linarith)]
      rw [show (3 * (1 / (m : ℝ)) / 2)⁻¹ = 2 * m / 3 by field_simp]
      linarith
    refine ⟨le_trans ?_ hε1, hε1⟩
    rw [tol_zero, tol_one]
    nlinarith [pow_pos hu 2, pow_pos hu 3]
  · have hx0 : 0 ≤ max (tol u 0)⁻¹ (tol u 0 ^ (1 - π) * tol u 1 ^ (-π)) :=
      (inv_pos.2 (tol_pos hu 0)).le.trans (le_max_left _ _)
    exact lt_cube hm hC hx0 (order_le hm hπ)

/-- **The run for a constant $C$.** For every $C \in \mathbb{R}$ there are tolerances $\varepsilon$,
Phase-2 data $D$ on $\mathbb{R}^2$ and an outer iteration $k_\varepsilon$ with the following
properties, where $q = 1$ and $\theta = 3/4$ throughout.

* $0 < \varepsilon_j \le 1$ for every $j$, and if $C \ge 1$, then $\varepsilon_0 \le C^{-1}$ and
  $\varepsilon_1 \le C^{-1}$.
* For every $\pi \le 3/2$, $C \max(\varepsilon_0^{-1}, \varepsilon_0^{1-\pi}
  \varepsilon_1^{-\pi}) < k_\varepsilon$.
* Phase 2 with the data $D$ terminates at $k_\varepsilon$, and the numbers of evaluations of
  $(f, c)$ and of their derivatives up to $k_\varepsilon$ are both $k_\varepsilon + 1$.
* All optimality radii are $1$, and every inner call has one iteration, which is successful.
* For every $k \in [1, k_\varepsilon]$, $x_{k+1} \in X$, $\delta_{k+1, 1} = 1$ and
  $\mu(x_{k+1}, t_k) < \mu(x_k, t_k)$.
* For every $\beta \in (0, 3/4]$, $D$ is a run of Phase 2 from $x_1 = (0, -1)$ with the constant
  $\beta$.
* For every $\beta \in [2/3, 3/4]$: every call $k \in [1, k_\varepsilon]$ ends at a point that
  passes the inner test (14.3.19); every $k \in [1, k_\varepsilon)$ is in $\mathcal{K}_b$; every
  $k \in [1, k_\varepsilon]$ satisfies $\beta \|r(x_k, t_k)\| \varepsilon_1 < \phi^1_{\mu,
  X(x_k), 1}(x_k, t_k)$; and the calls satisfy the inner-test contract for every
  $\kappa_{\mathrm{decr}}$, all exponents $\pi_j$, all
  $\kappa_{\mathrm{uns}}, \kappa_{\mathrm{unc}}$ with $\kappa_{\mathrm{uns}} +
  \kappa_{\mathrm{unc}} \ge 1$, and all radii $\rho_j$ with $\rho_1 \le 1$.
* For every $\beta \in (0, 3/4]$, every $\kappa \ge 8$, all exponents $\pi_j$ with
  $\pi_1 \ge 4/3$ and every $k \in [1, k_\varepsilon]$, $2 \le \kappa\, \mu(x_k, t_k) (\beta
  \|r(x_k, t_k)\| \varepsilon_1)^{-\pi_1}$.

The objects are `Constrained.TwoPhaseExample.BoxBadIter.tol u`,
`Constrained.TwoPhaseExample.BoxBadIter.seq u N` and $k_\varepsilon = N$ for the parameters $u$
and $N$ of `Constrained.TwoPhaseExample.BoxBadIter.exists_params`. -/
theorem exists_seq (C : ℝ) :
    ∃ (ε : ℕ → ℝ) (D : HighOrderTargetSeq ℝ²) (kε : ℕ),
      (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ (1 ≤ C → ε 0 ≤ C⁻¹ ∧ ε 1 ≤ C⁻¹) ∧
      (∀ π : ℝ, π ≤ 3 / 2 → C * max (ε 0)⁻¹ (ε 0 ^ (1 - π) * ε 1 ^ (-π)) < kε) ∧
      D.IsEnd (Box.obj 1) Box.con Box.square 1 (3 / 4) ε kε ∧
      D.funEvals kε = kε + 1 ∧ D.derivEvals kε = kε + 1 ∧
      (∀ k j, D.δ k j = 1) ∧ (∀ k, D.e k = 1) ∧ (∀ k, D.succCount k = 1) ∧
      (∀ k ∈ Finset.Icc 1 kε, D.x (k + 1) ∈ Box.square ∧ D.δ (k + 1) 1 = 1 ∧
        targetMerit (Box.obj 1) Box.con (D.t k) (D.x (k + 1)) <
          targetMerit (Box.obj 1) Box.con (D.t k) (D.x k)) ∧
      (∀ β : ℝ, 0 < β → β ≤ 3 / 4 →
        IsHighOrderTargetRun (Box.obj 1) Box.con Box.square 1 (3 / 4) β ε (pt 0 (-1)) D) ∧
      (∀ β : ℝ, 2 / 3 ≤ β → β ≤ 3 / 4 →
        (∀ k ∈ Finset.Icc 1 kε, D.InnerTest (Box.obj 1) Box.con Box.square 1 β ε k) ∧
        (∀ k ∈ Finset.Ico 1 kε, D.IsKb (Box.obj 1) Box.con (3 / 4) ε k) ∧
        (∀ k ∈ Finset.Icc 1 kε,
          β * targetResidual (Box.obj 1) Box.con (D.t k) (D.x k) * ε 1 <
            Optimization.taylorMeasure
              (ftaylorSeries ℝ (targetMerit (Box.obj 1) Box.con (D.t k)) (D.x k)) 1 1
              {d | D.x k + d ∈ Box.square}) ∧
        ∀ (κdecr κuns κunc : ℝ) (π ρ : ℕ → ℝ), 1 ≤ κuns + κunc → ρ 1 ≤ 1 →
          D.IsInnerTestContract (Box.obj 1) Box.con Box.square 1 (3 / 4) β ε κdecr κuns κunc
            π ρ) ∧
      ∀ β : ℝ, 0 < β → β ≤ 3 / 4 → ∀ κ : ℝ, 8 ≤ κ → ∀ π : ℕ → ℝ, 4 / 3 ≤ π 1 →
        ∀ k ∈ Finset.Icc 1 kε,
          2 ≤ κ * targetMerit (Box.obj 1) Box.con (D.t k) (D.x k) *
            (β * targetResidual (Box.obj 1) Box.con (D.t k) (D.x k) * ε 1) ^ (-π 1) := by
  obtain ⟨u, N, hu, hu7, hNu, hN, hCε, hord⟩ := exists_params C
  refine ⟨tol u, seq u N, N, fun j => ⟨tol_pos hu j, tol_le_one hu hu7 j⟩, hCε, hord,
    isEnd hu hu7 hNu hN, HighOrderTargetSeq.funEvals_oneStep _ _ _,
    HighOrderTargetSeq.derivEvals_oneStep _ _ _, fun _ _ => rfl, fun _ => rfl,
    fun k => HighOrderTargetSeq.succCount_oneStep _ _ k, fun k hk => ?_,
    fun β hβ hβθ => isHighOrderTargetRun hu hu7 hNu hN hβ hβθ, fun β hβ hβθ => ⟨fun k hk => ?_,
      fun k hk => isKb hu hu7 (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2, fun k hk => ?_,
      fun κdecr κuns κunc π ρ hκ hρ => isInnerTestContract hu hu7 hNu hN hβ hκ hρ⟩,
    fun β hβ hβθ κ hκ π hπ k hk => ?_⟩
  · obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    exact ⟨iter_mem hu hu7 hNu (k := k + 1) (by omega) (by omega), rfl,
      targetMerit_lt hu hk1 hkN⟩
  · exact innerTest hu hu7 hNu hβ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2
  · exact lt_taylorMeasure_start hu hu7 hNu hβθ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2
  · exact two_le_costBound hu hu7 hβ hβθ hκ hπ (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2

/-- **Cheap first calls.** Let the exponents $\pi_j$ satisfy $\pi_1 < 2$, let $0 < \beta < 1$, and
let $\kappa \in \mathbb{R}$. Write $x_1 = (0, -1)$ and $t_1 = f(x_1) - \sqrt{\varepsilon_0^2 -
\|c(x_1)\|^2}$. There are tolerances $\varepsilon$ with $0 < \varepsilon_j \le 1$ for every $j$
such that:

* $x_1 \in X$ and $\|c(x_1)\| = 0$;
* for every radius $\delta \in (0, 1]$, the first-order test with the tolerance
  $\beta \|r(x_1, t_1)\| \varepsilon_1$ fails at $x_1$: $\beta \|r(x_1, t_1)\| \varepsilon_1
  \delta / 1! < \phi^\delta_{\mu, X(x_1), 1}(x_1, t_1)$;
* $\kappa\, \mu(x_1, t_1) \bigl(\beta \|r(x_1, t_1)\| \varepsilon_1\bigr)^{-\pi_1} < 1$.

The proof takes $\varepsilon_1 = 1$ and $\varepsilon_0$ small. The decrease along $-\delta e_1$
is $\varepsilon_0 \delta$, and the cost bound equals $(\kappa/2) \beta^{-\pi_1}
\varepsilon_0^{2-\pi_1}$, which tends to $0$ with $\varepsilon_0$. -/
theorem exists_tol_start_lt_taylorMeasure (π : ℕ → ℝ) (hπ : π 1 < 2) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (κ : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧ pt 0 (-1) ∈ Box.square ∧ ‖Box.con (pt 0 (-1))‖ = 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        β * targetResidual (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
            ε 1 * δ ^ 1 / (1 : ℕ)! <
          Optimization.taylorMeasure
            (ftaylorSeries ℝ (targetMerit (Box.obj 1) Box.con
              (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2))) (pt 0 (-1))) 1 δ
            {d | pt 0 (-1) + d ∈ Box.square}) ∧
      κ * targetMerit (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
          (β * targetResidual (Box.obj 1) Box.con
            (Box.obj 1 (pt 0 (-1)) - √(ε 0 ^ 2 - ‖Box.con (pt 0 (-1))‖ ^ 2)) (pt 0 (-1)) *
              ε 1) ^ (-π 1) < 1 := by
  have hc0 : ‖Box.con (pt 0 (-1))‖ = 0 := by rw [Box.norm_con]; simp
  set a : ℝ := 2 - π 1 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set K : ℝ := |κ| / 2 * β ^ (-π 1) + 1 with hK_def
  have hK : 0 < K := by rw [hK_def]; positivity
  set e : ℝ := min 1 ((2 * K) ^ (-1 / a)) with he_def
  have he0 : 0 < e := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have he1 : e ≤ 1 := min_le_left _ _
  have hea : e ^ a ≤ (2 * K)⁻¹ := by
    calc e ^ a ≤ ((2 * K) ^ (-1 / a)) ^ a :=
          Real.rpow_le_rpow he0.le (min_le_right _ _) ha.le
      _ = (2 * K)⁻¹ := by
          rw [← Real.rpow_mul (by positivity), show -1 / a * a = -1 by field_simp,
            Real.rpow_neg_one]
  refine ⟨fun j => if j = 0 then e else 1, fun j => ?_, by simp [Box.square], hc0, ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨he0, he1⟩
    · exact ⟨one_pos, le_rfl⟩
  simp only [↓reduceIte, one_ne_zero, hc0]
  have ht : Box.obj 1 (pt 0 (-1)) - √(e ^ 2 - 0 ^ 2) = Box.obj 1 (pt 0 (-1)) - e := by
    rw [show e ^ 2 - (0 : ℝ) ^ 2 = e ^ 2 by ring, Real.sqrt_sq he0.le]
  rw [ht]
  have hR : targetResidual (Box.obj 1) Box.con (Box.obj 1 (pt 0 (-1)) - e) (pt 0 (-1)) = e := by
    rw [Constrained.targetResidual_def, hc0,
      show (0 : ℝ) ^ 2 + (Box.obj 1 (pt 0 (-1)) - (Box.obj 1 (pt 0 (-1)) - e)) ^ 2 = e ^ 2 by ring,
      Real.sqrt_sq he0.le]
  refine ⟨fun δ hδ hδ1 => ?_, ?_⟩
  · rw [hR]
    have hmem : EuclideanSpace.single (0 : Fin 2) (-δ) ∈
        closedBall (0 : ℝ²) δ ∩ {d | pt 0 (-1) + d ∈ Box.square} := by
      refine ⟨by simp [abs_of_pos hδ], ?_⟩
      simp only [Box.square, mem_ofPred_eq, PiLp.add_apply, pt_zero, pt_one]
      have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
      have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
      rw [e0, e1]
      exact ⟨by rw [abs_le]; constructor <;> linarith, by norm_num⟩
    have h := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (targetMerit (Box.obj 1) Box.con (Box.obj 1 (pt 0 (-1)) - e))
        (pt 0 (-1))) 1
      hmem
    rw [Box.taylorDecrement_one] at h
    simp only [pt_zero] at h
    have e0 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 0 = -δ := by simp
    have e1 : (EuclideanSpace.single (0 : Fin 2) (-δ : ℝ)) 1 = 0 := by simp
    rw [e0, e1] at h
    refine lt_of_lt_of_le ?_ h
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, mul_one]
    have : β * e * δ < e * δ := by
      have := mul_pos he0 hδ
      nlinarith
    nlinarith
  · rw [Constrained.targetMerit_eq, hR]
    simp only [mul_one]
    rw [Real.mul_rpow hβ.le he0.le]
    have hsplit : e ^ 2 / 2 * (β ^ (-π 1) * e ^ (-π 1)) = β ^ (-π 1) / 2 * e ^ a := by
      rw [ha_def, show 2 - π 1 = (2 : ℝ) + -π 1 by ring, Real.rpow_add he0,
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [mul_assoc, hsplit]
    have hb : 0 ≤ β ^ (-π 1) := (Real.rpow_pos_of_pos hβ _).le
    have hea0 : 0 ≤ e ^ a := (Real.rpow_pos_of_pos he0 _).le
    have h1 : κ * (β ^ (-π 1) / 2 * e ^ a) ≤ K * e ^ a := by
      rw [hK_def]
      have := le_abs_self κ
      nlinarith [mul_nonneg hb hea0, abs_nonneg κ]
    have h2 : K * e ^ a ≤ K * (2 * K)⁻¹ := mul_le_mul_of_nonneg_left hea hK.le
    have h3 : K * (2 * K)⁻¹ = 1 / 2 := by field_simp
    linarith

end Constrained.TwoPhaseExample.BoxBadIter
