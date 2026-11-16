/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Numlib.Stationary.Basic

/-!
# Fixed-point iterations

This module studies the iteration $x_{k+1} = T(x_k)$ for a self-map $T$ of a metric or normed space.
It extends `ContractingWith` of Mathlib for the **Banach fixed-point theorem** with the a priori
bound, the a posteriori bound and the linear rate: Theorem 5.1.3 and the estimates (5.1.4)–(5.1.6)
of [han2009theoretical], and Theorems 3.45 and 3.46 of [kress1998numerical]. It proves the variant
where only a power $T^m$ is a contraction (Exercise 5.1.2 of [han2009theoretical], Problem 3.17 of
[kress1998numerical]), and the derivative criterion $\sup \|T'\| < 1$ (Theorem 6.8 of
[kress1998numerical]; [han2009theoretical] give the scalar case in the remark after their Theorem
5.2.1). It also proves the theorem of Zarantonello for strongly monotone Lipschitz maps on a Hilbert
space, which is the nonlinear Lax–Milgram lemma (Theorem 5.1.4 of [han2009theoretical]).

The scalar and local theory of §6.3 of [quarteroni2000numerical] is in two sections. The first gives
the fixed-point theorem on $[a, b]$ from a derivative bound $|\varphi'| \le K < 1$ (Theorem 6.1).
The second gives the theorem of Ostrowski: local convergence from $\|\varphi'(\alpha)\| < 1$ at the
fixed point $\alpha$ alone, in a normed space and on $\mathbb{R}$ (Property 6.3). It also gives the
converse, no convergence when $|\varphi'(\alpha)| > 1$ (Remark 6.2), and the form with a power,
$\|\varphi'(\alpha)^m\| < 1$ for some $m$, together with the clause that a neighbourhood of $\alpha$
is invariant. Property 7.3 of [quarteroni2000numerical], the condition $\rho(\varphi'(\alpha)) < 1$
in $\mathbb{R}^n$, reduces to this form. The order of convergence of these iterations is the subject
of `Numlib.Nonlinear.Order`.

## Main definitions

* `IsStronglyMonotoneWith`: $c \|x - y\|^2 \le \operatorname{Re} \langle A x - A y, x - y \rangle$
  for all $x, y$.
* `IsStronglyMonotoneOnWith`: the same inequality for $x, y$ in a set $s$.

## Main results

* `exists_unique_fixedPoint_of_mapsTo`: a contraction of a nonempty closed set into itself has
  exactly one fixed point in the set.
* `dist_iterate_le_of_mapsTo`: the a priori bound $d(f^n(x_0), x^*) \le K^n/(1 - K)\, d(f(x_0),
  x_0)$.
* `exists_unique_fixedPoint_of_iterate_contractingWith`: if a power $T^m$ is a contraction, then $T$
  has a unique fixed point.
* `lipschitzOnWith_of_hasFDerivWithinAt`: a derivative bound $\|T'\| \le q$ on a convex set makes
  $T$ $q$-Lipschitz there.
* `exists_unique_fixedPoint_Icc_of_abs_deriv_le`: a self-map of $[a, b]$ with $|\varphi'| \le K < 1$
  has exactly one fixed point there.
* `tendsto_iterate_of_norm_fderiv_lt_one`: the theorem of Ostrowski in a normed space.
* `tendsto_iterate_of_exists_norm_pow_fderiv_lt_one`: the theorem of Ostrowski with a power
  $\|\varphi'(\alpha)^m\| < 1$.
* `not_tendsto_iterate_of_one_lt_abs_deriv`: no orbit that avoids $\alpha$ converges to $\alpha$
  when $|\varphi'(\alpha)| > 1$.
* `contractingWith_damped`: the damped map $x \mapsto x - \theta (T x - b)$ is a contraction for
  $0 < \theta < 2c/L^2$.
* `zarantonello`: a strongly monotone Lipschitz map on a Hilbert space is bijective.
* `norm_sub_le_of_strongly_monotone`: the inverse of a strongly monotone map with constant $c > 0$
  is $1/c$-Lipschitz.

## Implementation notes

* The existence theory for variational inequalities in `Numlib.Variational.Inequality.Basic` also
  uses `IsStronglyMonotoneWith` and `IsStronglyMonotoneOnWith`.
-/

open Filter Topology

section Metric

variable {α : Type*} [MetricSpace α]

namespace ContractingWith

variable {K : NNReal} {f : α → α}

/-- **Linear rate of convergence.** Let $X$ be a nonempty complete metric space and let $f$ be a
contraction with constant $K$, with fixed point $x^*$. Then for every $x$ and $n$,
$$d(f^{n+1}(x), x^*) \le K\, d(f^n(x), x^*),$$
so every step reduces the error by the factor $K$. This is (5.1.6) of [han2009theoretical]. -/
theorem dist_iterate_succ_fixedPoint_le [Nonempty α] [CompleteSpace α] (hf : ContractingWith K f)
    (x : α) (n : ℕ) :
    dist (f^[n + 1] x) (fixedPoint f hf) ≤ K * dist (f^[n] x) (fixedPoint f hf) := by
  rw [Function.iterate_succ_apply']
  have h := hf.dist_le_mul (f^[n] x) (fixedPoint f hf)
  rwa [hf.fixedPoint_isFixedPt] at h

/-- Let $X$ be a nonempty complete metric space and let $f$ be a contraction. Then $f(x) = x$ has
exactly one solution $x$, the fixed point of $f$. -/
theorem existsUnique_eq_self [Nonempty α] [CompleteSpace α] (hf : ContractingWith K f) :
    ∃! x, f x = x :=
  ⟨fixedPoint f hf, hf.fixedPoint_isFixedPt, fun _ hy => hf.fixedPoint_unique hy⟩

end ContractingWith

/-- Geometric decay towards a point. Let $s$ be a set with $f(s) \subseteq s$, let $K \ge 0$, and
let $x'$ be a point with $d(f(x), x') \le K\, d(x, x')$ for every $x \in s$. Then for every
$x_0 \in s$ and every $n$,
$$d(f^n(x_0), x') \le K^n d(x_0, x').$$

Neither $x' \in s$ nor $f(x') = x'$ is assumed. This estimate is behind the a priori bound of
the Banach fixed-point theorem, and behind the theorem of Ostrowski, where the contraction is
known only towards the fixed point. -/
theorem dist_iterate_le_pow_mul_of_mapsTo {f : α → α} {s : Set α} (hmaps : Set.MapsTo f s s)
    {K : ℝ} (hK0 : 0 ≤ K) {x' : α} (hf : ∀ x ∈ s, dist (f x) x' ≤ K * dist x x') {x₀ : α}
    (hx₀ : x₀ ∈ s) (n : ℕ) : dist (f^[n] x₀) x' ≤ K ^ n * dist x₀ x' := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc dist (f^[n + 1] x₀) x' = dist (f (f^[n] x₀)) x' := by rw [Function.iterate_succ_apply']
      _ ≤ K * dist (f^[n] x₀) x' := hf _ (hmaps.iterate n hx₀)
      _ ≤ K * (K ^ n * dist x₀ x') := by gcongr
      _ = K ^ (n + 1) * dist x₀ x' := by ring

/-- If $f$ is $K$-Lipschitz on $s$ and $x' \in s$ is a fixed point of $f$, then
$(1 - K)\, d(x_0, x') \le d(f(x_0), x_0)$ for every $x_0 \in s$. -/
private theorem one_sub_mul_dist_le {f : α → α} {s : Set α} {K : ℝ}
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) :
    (1 - K) * dist x₀ x' ≤ dist (f x₀) x₀ := by
  have hstep := hf x₀ hx₀ x' hx'
  rw [hfix] at hstep
  have htri : dist x₀ x' ≤ dist x₀ (f x₀) + dist (f x₀) x' := dist_triangle _ _ _
  rw [dist_comm x₀ (f x₀)] at htri
  linarith

/-- **The Banach fixed-point theorem on a closed set.** Let $X$ be a complete metric space, and let
$s \subseteq X$ be closed and nonempty with $f(s) \subseteq s$. Let $0 \le K < 1$ and let
$d(f(x), f(y)) \le K\, d(x, y)$ for all $x, y \in s$. Then $f$ has exactly one fixed point in
$s$.

This is the setting of Theorem 5.1.3 of [han2009theoretical] and of Theorem 3.45 of
[kress1998numerical]. The contraction hypothesis is required on $s$ only. -/
theorem exists_unique_fixedPoint_of_mapsTo [CompleteSpace α] {f : α → α} {s : Set α}
    (hs : IsClosed s) (hne : s.Nonempty) (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K < 1) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    ∃! x, x ∈ s ∧ f x = x := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcon : ContractingWith K.toNNReal (hmaps.restrict f s s) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ hK0]; exact hK
    · rw [Real.coe_toNNReal _ hK0]; exact hf x x.2 y y.2
  obtain ⟨y, hys, hfy, -, -⟩ :=
    hcon.exists_fixedPoint' hs.isComplete hmaps hx₀ (edist_ne_top _ _)
  refine ⟨y, ⟨hys, hfy⟩, ?_⟩
  rintro z ⟨hzs, hfz⟩
  have hzy : dist z y ≤ K * dist z y := by
    have h := hf z hzs y hys
    rwa [hfz, hfy] at h
  have : dist z y = 0 := le_antisymm (by nlinarith [dist_nonneg (x := z) (y := y)]) dist_nonneg
  exact dist_eq_zero.mp this

-- `hs` is unnecessary once a fixed point `x'` in `s` is supplied: the bound follows from the
-- contraction inequality on `s` alone. It is kept to match the companion existence statement.
set_option linter.unusedVariables false in
/-- **The a priori bound.** Let $s$ be a closed set with $f(s) \subseteq s$, let $0 \le K < 1$, and
let $d(f(x), f(y)) \le K\, d(x, y)$ for all $x, y \in s$. Let $x' \in s$ be a fixed point of
$f$. Then for every $x_0 \in s$ and every $n$,
$$d(f^n(x_0), x') \le \frac{K^n}{1 - K}\, d(f(x_0), x_0).$$
So the number of iterations for a given accuracy is known before the iteration starts. This is
(5.1.4) of [han2009theoretical] and Theorem 3.46 of [kress1998numerical].

The proof does not use that $s$ is closed. The hypothesis is kept so that the statement matches
`exists_unique_fixedPoint_of_mapsTo`. -/
theorem dist_iterate_le_of_mapsTo {f : α → α} {s : Set α} (hs : IsClosed s)
    (hmaps : Set.MapsTo f s s) {K : ℝ} (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) {x' : α} (hx' : x' ∈ s)
    (hfix : f x' = x') {x₀ : α} (hx₀ : x₀ ∈ s) (n : ℕ) :
    dist (f^[n] x₀) x' ≤ K ^ n / (1 - K) * dist (f x₀) x₀ := by
  have h1K : 0 < 1 - K := by linarith
  calc dist (f^[n] x₀) x' ≤ K ^ n * dist x₀ x' :=
        dist_iterate_le_pow_mul_of_mapsTo hmaps hK0
          (fun x hx => by simpa only [hfix] using hf x hx x' hx') hx₀ n
    _ ≤ K ^ n * (dist (f x₀) x₀ / (1 - K)) := by
        gcongr
        rw [le_div_iff₀ h1K, mul_comm]
        exact one_sub_mul_dist_le hf hx' hfix hx₀
    _ = K ^ n / (1 - K) * dist (f x₀) x₀ := by ring

/-- Interleaving of subsequences. Let $X$ be a topological space, $T : X \to X$, and $m > 0$. If for
every residue $j < m$ the subsequence $k \mapsto T^{mk + j}(x)$ converges to $x'$, then the
whole orbit $n \mapsto T^n(x)$ converges to $x'$. -/
theorem tendsto_iterate_of_forall_tendsto_iterate_mul_add {X : Type*} [TopologicalSpace X]
    {T : X → X} {x x' : X} {m : ℕ} (hm : 0 < m)
    (h : ∀ j < m, Tendsto (fun k => T^[m * k + j] x) atTop (𝓝 x')) :
    Tendsto (fun n => T^[n] x) atTop (𝓝 x') := by
  rw [Filter.tendsto_def]
  intro U hU
  have hall : ∀ᶠ k in atTop, ∀ j ∈ Set.Iio m, T^[m * k + j] x ∈ U :=
    (Filter.eventually_all_finite (Set.finite_Iio m)).2 fun j hj => h j hj hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hall
  refine Filter.eventually_atTop.2 ⟨m * N, fun n hn => ?_⟩
  have hdiv : N ≤ n / m := (Nat.le_div_iff_mul_le hm).2 (by rwa [mul_comm])
  have := hN (n / m) hdiv (n % m) (Nat.mod_lt n hm)
  rwa [Nat.div_add_mod] at this

-- Neither the continuity of `T` nor `0 < m` is needed for the conclusion; both are kept because
-- they belong to the textbook statement (Atkinson–Han, *Theoretical Numerical Analysis*,
-- Exercise 5.1.2).
set_option linter.unusedVariables false in
/-- **Contraction of a power.** Let $X$ be a nonempty complete metric space, let $T : X \to X$ be
continuous, let $m > 0$, and let $T^m$ be a contraction. Then $T$ has exactly one fixed point.
The map $T$ itself need not be a contraction in any metric. This is Exercise 5.1.2 of
[han2009theoretical] and Problem 3.17 of [kress1998numerical].

The hypothesis that $X$ is nonempty is added to the statement. The empty metric space is
complete, and every self-map of it is a contraction, so without this hypothesis the conclusion
is false. The proof does not use the continuity of $T$ or $m > 0$. Both are kept because they
belong to the statement of [han2009theoretical]. -/
theorem exists_unique_fixedPoint_of_iterate_contractingWith [Nonempty α] [CompleteSpace α]
    {T : α → α} (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal}
    (hK : ContractingWith K T^[m]) : ∃! x, T x = x :=
  ⟨hK.fixedPoint T^[m], hK.isFixedPt_fixedPoint_iterate,
    fun _ hy => hK.fixedPoint_unique (Function.IsFixedPt.iterate hy m)⟩

-- Continuity of `T` is again not needed: `T^[m]` already pins the limit down.
set_option linter.unusedVariables false in
/-- **Convergence for a contraction of a power.** Let $X$ be a complete metric space, let
$T : X \to X$ be continuous, let $m > 0$, and let $T^m$ be a contraction. Then for every $x$
there is a fixed point $x'$ of $T$ such that $T^n(x) \to x'$. This is Exercise 5.1.2 of
[han2009theoretical] and Problem 3.17 of [kress1998numerical].

The orbit splits into the $m$ subsequences $k \mapsto T^{mk + j}(x)$. Each of them is an orbit
of the contraction $T^m$, so it converges to the fixed point of $T^m$. The proof does not use
the continuity of $T$, because $T^m$ already determines the limit. -/
theorem tendsto_iterate_of_iterate_contractingWith [CompleteSpace α] {T : α → α}
    (hT : Continuous T) {m : ℕ} (hm : 0 < m) {K : NNReal} (hK : ContractingWith K T^[m]) (x : α) :
    ∃ x', T x' = x' ∧ Tendsto (fun n => T^[n] x) atTop (𝓝 x') := by
  have : Nonempty α := ⟨x⟩
  refine ⟨hK.fixedPoint T^[m], hK.isFixedPt_fixedPoint_iterate, ?_⟩
  -- each of the `m` interleaved subsequences `k ↦ T^[m k + j] x` iterates the contraction `T^[m]`
  refine tendsto_iterate_of_forall_tendsto_iterate_mul_add hm fun j _ => ?_
  refine (hK.tendsto_iterate_fixedPoint (T^[j] x)).congr fun k => ?_
  rw [← Function.iterate_mul, ← Function.iterate_add_apply, add_comm]

end Metric

section Derivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The derivative criterion for contractivity.** Let $E$ be a real normed space, let
$s \subseteq E$ be convex, and let $T : E \to E$ have the derivative $T'(x)$ within $s$ at every
$x \in s$, with $\|T'(x)\| \le q$ for every $x \in s$. Then $T$ is $q$-Lipschitz on $s$, and so
$T$ is a contraction on $s$ when $q < 1$. This is Theorem 6.8 of [kress1998numerical];
[han2009theoretical] give the scalar case in the remark after their Theorem 5.2.1.

The proof is `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` of Mathlib. -/
theorem lipschitzOnWith_of_hasFDerivWithinAt {T : E → E} {T' : E → E →L[ℝ] E} {s : Set E}
    (hs : Convex ℝ s) (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) {q : NNReal}
    (hT' : ∀ x ∈ s, ‖T' x‖₊ ≤ q) : LipschitzOnWith q T s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hT hT'

end Derivative

section Interval

/-!
### Scalar fixed-point iterations on an interval

Theorem 6.1 of [quarteroni2000numerical]: a map of $[a, b]$ into itself whose derivative is bounded
by $K < 1$ on $[a, b]$ has a unique fixed point there, and every orbit that starts in the interval
converges to it geometrically. The source assumes $\varphi \in C^1[a, b]$. The proof uses only the
bound on the derivative in the interval, so the hypotheses are a derivative within $[a, b]$ and
$|\varphi'| \le K$. The limit (6.18) of the error ratios is `tendsto_sub_div_sub_of_hasDerivAt` in
`Numlib.Nonlinear.Order`, which needs only differentiability at the fixed point.
-/

variable {φ φ' : ℝ → ℝ} {a b K : ℝ}

/-- Let $\varphi : \mathbb{R} \to \mathbb{R}$ have the derivative $\varphi'(x)$ within $[a, b]$ at
every $x \in [a, b]$, with $|\varphi'(x)| \le K$ there. Then
$|\varphi(x) - \varphi(y)| \le K |x - y|$ for all $x, y \in [a, b]$. This is the mean value
inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`. -/
theorem dist_le_mul_dist_Icc_of_abs_deriv_le
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, dist (φ x) (φ y) ≤ K * dist x y := by
  intro x hx y hy
  rw [dist_comm, dist_comm x, Real.dist_eq, Real.dist_eq, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hφ
    (fun z hz => by simpa [Real.norm_eq_abs] using hK z hz) hx hy

/-- **Existence and uniqueness of the fixed point.** Let $a \le b$, let
$\varphi : \mathbb{R} \to \mathbb{R}$ map $[a, b]$ into itself, and let $\varphi$ have the
derivative $\varphi'(x)$ within $[a, b]$ at every $x \in [a, b]$, with $|\varphi'(x)| \le K$
there and $K < 1$. Then $\varphi$ has exactly one fixed point $\alpha \in [a, b]$. This is
Theorem 6.1 of [quarteroni2000numerical].

The proof is the Banach fixed-point theorem on the closed interval,
`exists_unique_fixedPoint_of_mapsTo`. -/
theorem exists_unique_fixedPoint_Icc_of_abs_deriv_le (hab : a ≤ b)
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) (hK1 : K < 1) :
    ∃! α, α ∈ Set.Icc a b ∧ φ α = α :=
  exists_unique_fixedPoint_of_mapsTo isClosed_Icc (Set.nonempty_Icc.2 hab) hmaps
    (le_trans (abs_nonneg _) (hK a (Set.left_mem_Icc.2 hab))) hK1
    (dist_le_mul_dist_Icc_of_abs_deriv_le hφ hK)

/-- **Geometric convergence on the interval.** Let $\varphi : \mathbb{R} \to \mathbb{R}$ map
$[a, b]$ into itself, and let $\varphi$ have the derivative $\varphi'(x)$ within $[a, b]$ at
every $x \in [a, b]$, with $|\varphi'(x)| \le K$ there. Let $\alpha \in [a, b]$ be a fixed point
of $\varphi$. Then for every $x_0 \in [a, b]$ and every $k$, the iterate $\varphi^k(x_0)$ lies
in $[a, b]$ and
$$|\varphi^k(x_0) - \alpha| \le K^k |x_0 - \alpha|.$$
This is the estimate $|x^{(k)} - \alpha| \le K^k |x^{(0)} - \alpha|$ in the proof of Theorem 6.1
of [quarteroni2000numerical]. The bound $K < 1$ is not necessary for this estimate. -/
theorem abs_iterate_sub_le_Icc_of_abs_deriv_le
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) {α : ℝ} (hα : α ∈ Set.Icc a b) (hfix : φ α = α)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (k : ℕ) :
    φ^[k] x₀ ∈ Set.Icc a b ∧ |φ^[k] x₀ - α| ≤ K ^ k * |x₀ - α| := by
  refine ⟨hmaps.iterate k hx₀, ?_⟩
  rw [← Real.dist_eq, ← Real.dist_eq]
  exact dist_iterate_le_pow_mul_of_mapsTo hmaps (le_trans (abs_nonneg _) (hK α hα))
    (fun x hx => by simpa only [hfix] using dist_le_mul_dist_Icc_of_abs_deriv_le hφ hK x hx α hα)
    hx₀ k

/-- **Global convergence on the interval.** Let $\varphi : \mathbb{R} \to \mathbb{R}$ map $[a, b]$
into itself, and let $\varphi$ have the derivative $\varphi'(x)$ within $[a, b]$ at every
$x \in [a, b]$, with $|\varphi'(x)| \le K$ there and $K < 1$. Let $\alpha \in [a, b]$ be a fixed
point of $\varphi$. Then $\varphi^k(x_0) \to \alpha$ for every $x_0 \in [a, b]$. This is Theorem
6.1 of [quarteroni2000numerical]. -/
theorem tendsto_iterate_Icc_of_abs_deriv_le
    (hmaps : Set.MapsTo φ (Set.Icc a b) (Set.Icc a b))
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hK : ∀ x ∈ Set.Icc a b, |φ' x| ≤ K) (hK1 : K < 1) {α : ℝ} (hα : α ∈ Set.Icc a b)
    (hfix : φ α = α) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK α hα)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => (abs_iterate_sub_le_Icc_of_abs_deriv_le hmaps hφ hK hα hfix hx₀ k).2) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const |x₀ - α|

end Interval

section Ostrowski

/-!
### The theorem of Ostrowski

This section proves local convergence of a fixed-point iteration from the derivative at the fixed
point alone (Property 6.3 of [quarteroni2000numerical]; 10.1.3 of [ortega2000iterative]). If
$\|\varphi'(\alpha)\| < 1$, then every orbit that starts close enough to $\alpha$ converges to
$\alpha$, geometrically with every rate $q \in (\|\varphi'(\alpha)\|, 1)$. Only differentiability at
$\alpha$ is used. The hypothesis of the source, that $\varphi$ is continuous and differentiable in a
neighbourhood, is stronger than necessary. The estimate is one-sided,
$\|\varphi(x) - \alpha\| \le q \|x - \alpha\|$, so the geometric decay comes from
`dist_iterate_le_pow_mul_of_mapsTo` and not from a contraction.

The form with a power, `tendsto_iterate_of_exists_norm_pow_fderiv_lt_one`, with
$\|\varphi'(\alpha)^m\| < 1$ for some $m$, is how Property 7.3 of [quarteroni2000numerical], with
the condition $\rho(\varphi'(\alpha)) < 1$ in $\mathbb{R}^n$, is reached. In finite dimension,
$\rho(A) < 1$ is equivalent to $\|A^m\| < 1$ for some $m$. The theorem for $\varphi^m$, whose
derivative at $\alpha$ is $\varphi'(\alpha)^m$ by `HasFDerivAt.iterate`, is applied to the $m$
residues, and the subsequences are interleaved. This avoids a change of the norm of $\mathbb{R}^n$
to the $\varepsilon$-norm, which is only a seminorm and not a structure that the mean value
inequality can use.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {φ : E → E} {φ' : E →L[𝕜] E} {α : E}

/-- Let $E$ be a normed space and let $\alpha$ be a fixed point of $\varphi : E \to E$, at which
$\varphi$ has the derivative $\varphi'$. Then for every $q > \|\varphi'\|$, the inequality
$\|\varphi(x) - \alpha\| \le q \|x - \alpha\|$ holds for all $x$ in a neighbourhood of $\alpha$.
The remainder $o(\|x - \alpha\|)$ of the derivative is absorbed into the gap $q - \|\varphi'\|$. -/
theorem eventually_norm_sub_le_mul_of_hasFDerivAt (hα : φ α = α) (hφ : HasFDerivAt φ φ' α)
    {q : ℝ} (hq : ‖φ'‖ < q) : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ q * ‖x - α‖ := by
  have hlittle := (hasFDerivAt_iff_isLittleO.1 hφ).def (sub_pos.2 hq)
  filter_upwards [hlittle] with x hx
  calc ‖φ x - α‖ = ‖(φ x - φ α - φ' (x - α)) + φ' (x - α)‖ := by rw [hα]; congr 1; abel
    _ ≤ ‖φ x - φ α - φ' (x - α)‖ + ‖φ' (x - α)‖ := norm_add_le _ _
    _ ≤ (q - ‖φ'‖) * ‖x - α‖ + ‖φ'‖ * ‖x - α‖ := add_le_add hx (φ'.le_opNorm _)
    _ = q * ‖x - α‖ := by ring

/-- Let $0 \le q \le 1$ and $\delta \in \mathbb{R}$, and let
$\|\varphi(x) - \alpha\| \le q \|x - \alpha\|$ for every $x$ in the open ball
$B(\alpha, \delta)$. Then for every $x_0 \in B(\alpha, \delta)$ and every $k$, the iterate
$\varphi^k(x_0)$ lies in $B(\alpha, \delta)$ and $\|\varphi^k(x_0) - \alpha\| \le q^k \|x_0 -
\alpha\|$. -/
theorem norm_iterate_sub_le_pow_mul_of_ball {δ q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ x ∈ Metric.ball α δ, ‖φ x - α‖ ≤ q * ‖x - α‖) {x₀ : E} (hx₀ : x₀ ∈ Metric.ball α δ)
    (k : ℕ) : φ^[k] x₀ ∈ Metric.ball α δ ∧ ‖φ^[k] x₀ - α‖ ≤ q ^ k * ‖x₀ - α‖ := by
  have hmaps : Set.MapsTo φ (Metric.ball α δ) (Metric.ball α δ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖φ x - α‖ ≤ q * ‖x - α‖ := h x hx
      _ ≤ 1 * ‖x - α‖ := by gcongr
      _ < δ := by rw [one_mul, ← dist_eq_norm]; exact Metric.mem_ball.1 hx
  refine ⟨hmaps.iterate k hx₀, ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact dist_iterate_le_pow_mul_of_mapsTo hmaps hq0
    (fun x hx => by rw [dist_eq_norm, dist_eq_norm]; exact h x hx) hx₀ k

/-- **The theorem of Ostrowski, with the rate.** Let $E$ be a normed space and let $\alpha$ be a
fixed point of $\varphi : E \to E$, at which $\varphi$ has the derivative $\varphi'$. Let
$\|\varphi'\| < q < 1$. Then there is $\delta > 0$ such that for every
$x_0 \in B(\alpha, \delta)$ and every $k$, the iterate $\varphi^k(x_0)$ lies in
$B(\alpha, \delta)$ and
$$\|\varphi^k(x_0) - \alpha\| \le q^k \|x_0 - \alpha\|.$$
-/
theorem exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) {q : ℝ} (hq : ‖φ'‖ < q) (hq1 : q < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, ∀ k,
      φ^[k] x₀ ∈ Metric.ball α δ ∧ ‖φ^[k] x₀ - α‖ ≤ q ^ k * ‖x₀ - α‖ := by
  obtain ⟨δ, hδ, h⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_norm_sub_le_mul_of_hasFDerivAt hα hφ hq)
  exact ⟨δ, hδ, fun x₀ hx₀ k => norm_iterate_sub_le_pow_mul_of_ball
    (le_trans (norm_nonneg _) hq.le) hq1.le (fun x hx => h (Metric.mem_ball.1 hx)) hx₀ k⟩

/-- **The theorem of Ostrowski.** Let $E$ be a normed space and let $\alpha$ be a fixed point of
$\varphi : E \to E$, at which $\varphi$ has the derivative $\varphi'$ with $\|\varphi'\| < 1$.
Then there is $\delta > 0$ such that $\varphi^k(x_0) \to \alpha$ for every
$x_0 \in B(\alpha, \delta)$. This is Property 6.3 of [quarteroni2000numerical] and 10.1.3 of
[ortega2000iterative].

Nothing is assumed about $\varphi$ away from $\alpha$. -/
theorem tendsto_iterate_of_norm_fderiv_lt_one (hα : φ α = α) (hφ : HasFDerivAt φ φ' α)
    (h : ‖φ'‖ < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨q, hq, hq1⟩ := exists_between h
  obtain ⟨δ, hδ, hball⟩ := exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hα hφ hq hq1
  refine ⟨δ, hδ, fun x₀ hx₀ => ?_⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => (hball x₀ hx₀ k).2) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (le_trans (norm_nonneg _) hq.le)
    hq1).mul_const ‖x₀ - α‖

/-- **The theorem of Ostrowski with a power of the derivative.** Let $E$ be a normed space and let
$\alpha$ be a fixed point of $\varphi : E \to E$, at which $\varphi$ has the derivative
$\varphi'$. If $\|(\varphi')^m\| < 1$ for some $m \in \mathbb{N}$, then there is $\delta > 0$
such that $\varphi^k(x_0) \to \alpha$ for every $x_0 \in B(\alpha, \delta)$. In finite
dimension, the condition that $\|A^m\| < 1$ for some $m$ is equivalent to $\rho(A) < 1$, so this
is Property 7.3 of [quarteroni2000numerical].

The theorem of Ostrowski for $\varphi^m$, whose derivative at $\alpha$ is $(\varphi')^m$, gives
the convergence of the $m$ subsequences $k \mapsto \varphi^{mk + j}(x_0) =
\varphi^j((\varphi^m)^k(x_0))$, by the continuity of $\varphi^j$ at $\alpha$. These subsequences
are then interleaved. -/
theorem tendsto_iterate_of_exists_norm_pow_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) (h : ∃ m : ℕ, ‖φ' ^ m‖ < 1) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨m, hm⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · -- `‖1‖ < 1` forces `E` to be trivial, where every orbit is constant
    by_cases hE : Nontrivial E
    · rw [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at hm
      exact absurd hm (lt_irrefl 1)
    · have : Subsingleton E := not_nontrivial_iff_subsingleton.1 hE
      refine ⟨1, one_pos, fun x₀ _ => ?_⟩
      rw [show (fun k => φ^[k] x₀) = fun _ => α from funext fun k => Subsingleton.elim _ _]
      exact tendsto_const_nhds
  have hαm : φ^[m] α = α := Function.iterate_fixed hα m
  obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_norm_fderiv_lt_one hαm (hφ.iterate hα m) hm
  refine ⟨δ, hδ, fun x₀ hx₀ => tendsto_iterate_of_forall_tendsto_iterate_mul_add hm0
    fun j _ => ?_⟩
  have hcont : ContinuousAt φ^[j] α := hφ.continuousAt.iterate hα j
  have := hcont.tendsto.comp (hconv x₀ hx₀)
  rw [Function.iterate_fixed hα j] at this
  refine this.congr fun k => ?_
  simp only [Function.comp_apply, ← Function.iterate_mul, ← Function.iterate_add_apply,
    add_comm j]

/-- **The invariance clause of Property 7.3** of [quarteroni2000numerical]. Let $E$ be a normed
space and let $\alpha$ be a fixed point of $\varphi : E \to E$, at which $\varphi$ has the
derivative $\varphi'$, with $\|(\varphi')^m\| < 1$ for some $m \in \mathbb{N}$. Then every
neighbourhood $D$ of $\alpha$ contains a neighbourhood $S$ of $\alpha$ such that
$\varphi^k(x_0) \in D$ for every $x_0 \in S$ and every $k$.

The orbit of $\varphi^m$ stays in a small ball by the theorem of Ostrowski, and the finitely
many maps $\varphi^j$ with $j < m$ carry a smaller ball into $D$ by continuity at $\alpha$. -/
theorem exists_ball_mapsTo_iterate_of_exists_norm_pow_fderiv_lt_one (hα : φ α = α)
    (hφ : HasFDerivAt φ φ' α) (h : ∃ m : ℕ, ‖φ' ^ m‖ < 1) {D : Set E} (hD : D ∈ 𝓝 α) :
    ∃ S ∈ 𝓝 α, S ⊆ D ∧ ∀ x₀ ∈ S, ∀ k, φ^[k] x₀ ∈ D := by
  obtain ⟨m, hm⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · by_cases hE : Nontrivial E
    · rw [pow_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.norm_id] at hm
      exact absurd hm (lt_irrefl 1)
    · have : Subsingleton E := not_nontrivial_iff_subsingleton.1 hE
      exact ⟨D, hD, subset_rfl, fun x₀ hx₀ k => by rwa [Subsingleton.elim (φ^[k] x₀) x₀]⟩
  have hαm : φ^[m] α = α := Function.iterate_fixed hα m
  -- a neighbourhood of `α` carried into `D` by every `φ^[j]`, `j < m`
  have hV : ∀ᶠ y in 𝓝 α, ∀ j ∈ Set.Iio m, φ^[j] y ∈ D :=
    (Filter.eventually_all_finite (Set.finite_Iio m)).2 fun j _ =>
      (hφ.continuousAt.iterate hα j).preimage_mem_nhds ((Function.iterate_fixed hα j).symm ▸ hD)
  obtain ⟨ρ, hρ, hρV⟩ := Metric.eventually_nhds_iff.1 hV
  -- the ball in which the `φ^[m]`-orbits stay
  obtain ⟨q, hq, hq1⟩ := exists_between hm
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_norm_sub_le_mul_of_hasFDerivAt hαm (hφ.iterate hα m) hq)
  refine ⟨Metric.ball α (min ρ δ), Metric.ball_mem_nhds α (lt_min hρ hδ), fun y hy => ?_,
    fun x₀ hx₀ k => ?_⟩
  · simpa using hρV (lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _)) 0 hm0
  · have hstay := (norm_iterate_sub_le_pow_mul_of_ball (le_trans (norm_nonneg _) hq.le) hq1.le
      (fun x hx => hball (lt_of_lt_of_le (Metric.mem_ball.1 hx) (min_le_right _ _))) hx₀
      (k / m)).1
    have := hρV (lt_of_lt_of_le (Metric.mem_ball.1 hstay) (min_le_left _ _)) (k % m)
      (Nat.mod_lt k hm0)
    rwa [← Function.iterate_mul, ← Function.iterate_add_apply, add_comm, Nat.div_add_mod] at this

end Ostrowski

section ScalarOstrowski

variable {φ : ℝ → ℝ} {φ' α : ℝ}

/-- Let $\alpha$ be a fixed point of $\varphi : \mathbb{R} \to \mathbb{R}$, at which $\varphi$ has
the derivative $\varphi'$. Then for every $q > |\varphi'|$, the inequality
$|\varphi(x) - \alpha| \le q |x - \alpha|$ holds for all $x$ in a neighbourhood of $\alpha$. -/
theorem eventually_abs_sub_le_mul_of_hasDerivAt (hα : φ α = α) (hφ : HasDerivAt φ φ' α) {q : ℝ}
    (hq : |φ'| < q) : ∀ᶠ x in 𝓝 α, |φ x - α| ≤ q * |x - α| := by
  have := eventually_norm_sub_le_mul_of_hasFDerivAt hα hφ.hasFDerivAt
    (q := q) (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs])
  simpa [Real.norm_eq_abs] using this

/-- **The theorem of Ostrowski, scalar form, with the rate.** Let $\alpha$ be a fixed point of
$\varphi : \mathbb{R} \to \mathbb{R}$, at which $\varphi$ has the derivative $\varphi'$, and let
$|\varphi'| < q < 1$. Then there is $\delta > 0$ such that for every $x_0$ with
$|x_0 - \alpha| < \delta$ and every $k$,
$$|\varphi^k(x_0) - \alpha| < \delta \quad \text{and} \quad |\varphi^k(x_0) - \alpha| \le q^k
  |x_0 - \alpha|.$$
-/
theorem exists_ball_abs_iterate_sub_le_of_abs_deriv_lt_one (hα : φ α = α)
    (hφ : HasDerivAt φ φ' α) {q : ℝ} (hq : |φ'| < q) (hq1 : q < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → ∀ k,
      |φ^[k] x₀ - α| < δ ∧ |φ^[k] x₀ - α| ≤ q ^ k * |x₀ - α| := by
  obtain ⟨δ, hδ, h⟩ := exists_ball_norm_iterate_sub_le_of_norm_fderiv_lt_one hα hφ.hasFDerivAt
    (q := q) (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]) hq1
  refine ⟨δ, hδ, fun x₀ hx₀ k => ?_⟩
  have := h x₀ (by rwa [Metric.mem_ball, Real.dist_eq]) k
  simpa [Metric.mem_ball, Real.dist_eq, Real.norm_eq_abs] using this

/-- **The theorem of Ostrowski**, as printed in Property 6.3 of [quarteroni2000numerical]. Let
$\alpha$ be a fixed point of $\varphi : \mathbb{R} \to \mathbb{R}$, at which $\varphi$ has the
derivative $\varphi'$ with $|\varphi'| < 1$. Then there is $\delta > 0$ such that
$\varphi^k(x_0) \to \alpha$ for every $x_0$ with $|x_0 - \alpha| < \delta$.

This is the local convergence theorem to which every one-step scalar method (chord, Newton,
Aitken, Steffensen) is reduced. -/
theorem tendsto_iterate_of_abs_deriv_lt_one (hα : φ α = α) (hφ : HasDerivAt φ φ' α)
    (h : |φ'| < 1) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α) := by
  obtain ⟨δ, hδ, h⟩ := tendsto_iterate_of_norm_fderiv_lt_one hα hφ.hasFDerivAt
    (by rwa [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs])
  exact ⟨δ, hδ, fun x₀ hx₀ => h x₀ (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- **The repulsion estimate.** Let $\alpha$ be a fixed point of
$\varphi : \mathbb{R} \to \mathbb{R}$, at which $\varphi$ has the derivative $\varphi'$. Then
for every $q < |\varphi'|$, the inequality $q |x - \alpha| \le |\varphi(x) - \alpha|$ holds for
all $x$ in a neighbourhood of $\alpha$. -/
theorem eventually_mul_abs_sub_le_of_hasDerivAt (hα : φ α = α) (hφ : HasDerivAt φ φ' α) {q : ℝ}
    (hq : q < |φ'|) : ∀ᶠ x in 𝓝 α, q * |x - α| ≤ |φ x - α| := by
  have hslope : ∀ᶠ x in 𝓝[≠] α, q < |slope φ α x| :=
    ((hasDerivAt_iff_tendsto_slope.1 hφ).abs).eventually (eventually_gt_nhds hq)
  rw [eventually_nhdsWithin_iff] at hslope
  filter_upwards [hslope] with x hx
  by_cases hxα : x = α
  · simp [hxα, hα]
  · have h := (hx hxα).le
    rw [slope_def_field, hα, abs_div] at h
    have hpos : 0 < |x - α| := abs_pos.2 (sub_ne_zero.2 hxα)
    rwa [le_div_iff₀ hpos] at h

/-- **Repulsion**, Remark 6.2 of [quarteroni2000numerical]. Let $\alpha$ be a fixed point of
$\varphi : \mathbb{R} \to \mathbb{R}$, at which $\varphi$ has the derivative $\varphi'$ with
$|\varphi'| > 1$. Let $(x_k)$ be a sequence with $x_{k+1} = \varphi(x_k)$ and $x_k \neq \alpha$
for every $k$. Then $x_k$ does not converge to $\alpha$.

Near $\alpha$ the error grows, $|x_{k+1} - \alpha| \ge q |x_k - \alpha|$ with $q > 1$, so a
convergent orbit would have a positive error that eventually increases. For
$|\varphi'(\alpha)| = 1$ nothing can be said; Example 6.6 of [quarteroni2000numerical] shows
both behaviours. The hypothesis $x_k \neq \alpha$ is necessary, because an orbit that lands on
$\alpha$ converges. -/
theorem not_tendsto_iterate_of_one_lt_abs_deriv (hα : φ α = α) (hφ : HasDerivAt φ φ' α)
    (h : 1 < |φ'|) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α) :
    ¬ Tendsto x atTop (𝓝 α) := by
  intro hlim
  obtain ⟨q, hq1, hq⟩ := exists_between h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hlim.eventually (eventually_mul_abs_sub_le_of_hasDerivAt hα hφ hq))
  have hmono : ∀ k, |x N - α| ≤ |x (N + k) - α| := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc |x N - α| ≤ |x (N + k) - α| := ih
        _ ≤ q * |x (N + k) - α| := le_mul_of_one_le_left (abs_nonneg _) hq1.le
        _ ≤ |φ (x (N + k)) - α| := hN _ (Nat.le_add_right N k)
        _ = |x (N + k + 1) - α| := by rw [hx]
  have hpos : 0 < |x N - α| := abs_pos.2 (sub_ne_zero.2 (hne N))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1
    ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (gt_mem_nhds hpos))
  have := hM (N + M) (Nat.le_add_left M N)
  rw [Real.norm_eq_abs] at this
  exact absurd (hmono M) (not_le.2 this)

end ScalarOstrowski

section StronglyMonotone

/-- **Strong monotonicity.** Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$. A map $A : E \to E$ is **strongly monotone with constant $c$** if for all
$x, y \in E$
$$c \|x - y\|^2 \le \operatorname{Re} \langle A x - A y, x - y \rangle.$$
This is the nonlinear counterpart of the coercivity of an operator, and the hypothesis of the
theorem of Zarantonello and of the existence theory for variational inequalities. For a linear
$A$ it follows from `LinearMap.IsCoerciveWith` by
`LinearMap.IsCoerciveWith.isStronglyMonotoneWith` in `Numlib.Variational.Inequality.Basic`.

The scalar field is an explicit argument, as in `inner 𝕜 x y`, because the type `E → E` of $A$
does not determine it. -/
def IsStronglyMonotoneWith (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E → E) (c : ℝ) : Prop :=
  ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x - A y) (x - y))

/-- **Strong monotonicity on a set.** A map $A : E \to E$ is **strongly monotone on $s$ with
constant $c$** if $c \|x - y\|^2 \le \operatorname{Re} \langle A x - A y, x - y \rangle$ for all
$x, y \in s$.

The existence theory for a variational inequality over a set $K$ never evaluates $A$ outside
$K$. So this is the hypothesis that it really uses (Remark 11.3.2 of [han2009theoretical]), and
the locally Lipschitz form of that theory needs it, because there the global condition is not
available. -/
def IsStronglyMonotoneOnWith (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (A : E → E) (s : Set E) (c : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x - A y) (x - y))

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If $A$ is strongly monotone with constant $c$ and $c' \le c$, then $A$ is strongly monotone with
constant $c'$. -/
theorem IsStronglyMonotoneWith.mono {A : E → E} {c c' : ℝ} (h : IsStronglyMonotoneWith 𝕜 A c)
    (hc : c' ≤ c) : IsStronglyMonotoneWith 𝕜 A c' := fun x y =>
  (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h x y)

/-- If $A$ is strongly monotone with constant $c$, then $A$ is strongly monotone with constant $c$
on every set $s$. -/
theorem IsStronglyMonotoneWith.isStronglyMonotoneOnWith {A : E → E} {c : ℝ}
    (h : IsStronglyMonotoneWith 𝕜 A c) (s : Set E) : IsStronglyMonotoneOnWith 𝕜 A s c :=
  fun x _ y _ => h x y

/-- If $A$ is strongly monotone on $s$ with constant $c$ and $c' \le c$, then $A$ is strongly
monotone on $s$ with constant $c'$. -/
theorem IsStronglyMonotoneOnWith.mono {A : E → E} {s : Set E} {c c' : ℝ}
    (h : IsStronglyMonotoneOnWith 𝕜 A s c) (hc : c' ≤ c) : IsStronglyMonotoneOnWith 𝕜 A s c' :=
  fun x hx y hy => (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans (h x hx y hy)

/-- On a real inner product space, $A$ is strongly monotone on $s$ with constant $c$ if and only if
$c \|x - y\|^2 \le \langle A x - A y, x - y \rangle$ for all $x, y \in s$. -/
theorem isStronglyMonotoneOnWith_real_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F → F) (s : Set F) (c : ℝ) :
    IsStronglyMonotoneOnWith ℝ A s c ↔
      ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y) := Iff.rfl

/-- On a real inner product space, $A$ is strongly monotone with constant $c$ if and only if $c
\|x - y\|^2 \le \langle A x - A y, x - y \rangle$ for all $x, y$. -/
theorem isStronglyMonotoneWith_real_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : F → F) (c : ℝ) :
    IsStronglyMonotoneWith ℝ A c ↔ ∀ x y, c * ‖x - y‖ ^ 2 ≤ inner ℝ (A x - A y) (x - y) :=
  Iff.rfl

/-- The identity map is strongly monotone with constant $1$. -/
theorem isStronglyMonotoneWith_id : IsStronglyMonotoneWith 𝕜 (fun x : E => x) 1 := fun x y => by
  rw [one_mul, inner_self_eq_norm_sq]

end StronglyMonotone

section Zarantonello

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- If $\theta \ge 0$, $c \|u\|^2 \le \operatorname{Re} \langle w, u \rangle$ and
$\|w\| \le L \|u\|$, then $\|u - \theta w\|^2 \le (1 - 2\theta c + \theta^2 L^2) \|u\|^2$. -/
private theorem norm_sub_smul_sq_le {u w : E} {c L θ : ℝ} (hθ : 0 ≤ θ)
    (hmono : c * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 w u)) (hw : ‖w‖ ≤ L * ‖u‖) :
    ‖u - (θ : 𝕜) • w‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖u‖ ^ 2 := by
  have hre : RCLike.re (inner 𝕜 u w) = RCLike.re (inner 𝕜 w u) := by
    rw [← inner_conj_symm w u, RCLike.conj_re]
  have hexp : ‖u - (θ : 𝕜) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * θ * RCLike.re (inner 𝕜 w u) + θ ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, RCLike.re_ofReal_mul, hre, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hθ, mul_pow]
    ring
  have hw2 : ‖w‖ ^ 2 ≤ L ^ 2 * ‖u‖ ^ 2 := by nlinarith [norm_nonneg w, norm_nonneg u]
  have h1 : 2 * θ * (c * ‖u‖ ^ 2) ≤ 2 * θ * RCLike.re (inner 𝕜 w u) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have h2 : θ ^ 2 * ‖w‖ ^ 2 ≤ θ ^ 2 * (L ^ 2 * ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hw2 (sq_nonneg θ)
  rw [hexp]
  nlinarith [h1, h2]

omit [CompleteSpace E] in
/-- **The damped iteration on a set.** Let $E$ be an inner product space, let $T : E \to E$ be
strongly monotone on $s$ with constant $c$, and let $\|T x - T y\| \le L \|x - y\|$ for all
$x, y \in s$. Let $\theta \ge 0$ and $b \in E$. Then for all $x, y \in s$
$$\bigl\|x - \theta (T x - b) - \bigl(y - \theta (T y - b)\bigr)\bigr\| \le \sqrt{1 - 2\theta
  c + \theta^2 L^2}\, \|x - y\|.$$

This is the estimate that `contractingWith_damped` makes on the whole space. A fixed-point
argument on a closed convex set needs it in this form: the iterates never leave the set, so the
hypotheses on $T$ are only used there. See `existsUnique_isVariationalInequalitySolution_on`. -/
theorem norm_sub_damped_le {T : E → E} {s : Set E} {c L θ : ℝ} (hθ : 0 ≤ θ)
    (hmono : IsStronglyMonotoneOnWith 𝕜 T s c)
    (hlip : ∀ x ∈ s, ∀ y ∈ s, ‖T x - T y‖ ≤ L * ‖x - y‖) (b : E) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) :
    ‖x - (θ : 𝕜) • (T x - b) - (y - (θ : 𝕜) • (T y - b))‖
      ≤ Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ := by
  have hsub : x - (θ : 𝕜) • (T x - b) - (y - (θ : 𝕜) • (T y - b))
      = (x - y) - (θ : 𝕜) • (T x - T y) := by
    rw [smul_sub, smul_sub, smul_sub]
    abel
  rw [hsub]
  calc ‖(x - y) - (θ : 𝕜) • (T x - T y)‖
      = Real.sqrt (‖(x - y) - (θ : 𝕜) • (T x - T y)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ ^ 2) :=
        Real.sqrt_le_sqrt (norm_sub_smul_sq_le hθ (hmono x hx y hy) (hlip x hx y hy))
    _ = Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2) * ‖x - y‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace E] in
/-- Let $E$ be an inner product space, let $T : E \to E$ be strongly monotone with constant $c$ and
$L$-Lipschitz with $L > 0$, and let $b \in E$. If $0 < \theta < 2c/L^2$, then the damped map
$x \mapsto x - \theta (T x - b)$ is a contraction with constant
$\sqrt{1 - 2\theta c + \theta^2 L^2}$.

The fixed points of the damped map are the solutions of $T x = b$. So this result converts
strong monotonicity into an application of the Banach fixed-point theorem. It is the proof of
Theorem 5.1.4 of [han2009theoretical], and also their first proof of the Lax–Milgram lemma. -/
theorem contractingWith_damped {T : E → E} {c L : ℝ} (hL : 0 < L)
    (hmono : IsStronglyMonotoneWith 𝕜 T c) (hlip : LipschitzWith (Real.toNNReal L) T) (b : E)
    {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * c / L ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2)))
      (fun x => x - (θ : 𝕜) • (T x - b)) := by
  have hfac : 1 - 2 * θ * c + θ ^ 2 * L ^ 2 < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hθ'
    nlinarith
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · rw [← NNReal.coe_lt_one, Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.sqrt_lt' one_pos]
    simpa using hfac
  · have hw : ∀ u ∈ (Set.univ : Set E), ∀ v ∈ (Set.univ : Set E), ‖T u - T v‖ ≤ L * ‖u - v‖ := by
      intro u _ v _
      have h := hlip.dist_le_mul u v
      rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le] at h
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), dist_eq_norm, dist_eq_norm]
    exact norm_sub_damped_le (𝕜 := 𝕜) hθ.le (hmono.isStronglyMonotoneOnWith _) hw b
      (Set.mem_univ x) (Set.mem_univ y)

/-- **The theorem of Zarantonello.** Let $E$ be a Hilbert space, and let $T : E \to E$ be strongly
monotone with a constant $c > 0$ and Lipschitz with constant $L$. Then for every $b \in E$ the
equation $T x = b$ has exactly one solution $x$. So $T$ is bijective. This is Theorem 5.1.4 of
[han2009theoretical].

It is the nonlinear counterpart of the Lax–Milgram lemma: strong monotonicity takes the role of
coercivity. The Lipschitz bound $\|x_1 - x_2\| \le \|T x_1 - T x_2\|/c$ on the inverse is
`norm_sub_le_of_strongly_monotone`. -/
theorem zarantonello {T : E → E} {c L : ℝ} (hc : 0 < c) (hmono : IsStronglyMonotoneWith 𝕜 T c)
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) : ∃! x, T x = b := by
  -- replace `L` by `L' = max L 1 > 0` so that the damping parameter `θ = c / L'²` makes sense
  have hL' : (0 : ℝ) < max L 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlip' : LipschitzWith (Real.toNNReal (max L 1)) T :=
    hlip.weaken (Real.toNNReal_mono (le_max_left _ _))
  have hθ : 0 < c / max L 1 ^ 2 := by positivity
  have hθ' : c / max L 1 ^ 2 < 2 * c / max L 1 ^ 2 := by
    have h2 : 2 * c / max L 1 ^ 2 = c / max L 1 ^ 2 + c / max L 1 ^ 2 := by ring
    linarith
  have hcon := contractingWith_damped (𝕜 := 𝕜) hL' hmono hlip' b hθ hθ'
  have : Nonempty E := ⟨0⟩
  have hiff : ∀ y : E,
      (fun x => x - ((c / max L 1 ^ 2 : ℝ) : 𝕜) • (T x - b)) y = y ↔ T y = b := by
    intro y
    simp only [sub_eq_self, smul_eq_zero, sub_eq_zero]
    exact or_iff_right (by simpa using hθ.ne')
  obtain ⟨xstar, hfix, huniq⟩ := hcon.existsUnique_eq_self
  exact ⟨xstar, (hiff _).mp hfix, fun y hy => huniq y ((hiff y).mpr hy)⟩

omit [CompleteSpace E] in
/-- **Lipschitz dependence on the right-hand side.** Let $E$ be an inner product space and let
$T : E \to E$ be strongly monotone with a constant $c > 0$. If $T x_1 = b_1$ and $T x_2 = b_2$,
then
$$\|x_1 - x_2\| \le \frac{\|b_1 - b_2\|}{c}.$$
So the inverse of $T$ is $1/c$-Lipschitz. This is (5.1.11) of [han2009theoretical]. -/
theorem norm_sub_le_of_strongly_monotone {T : E → E} {c : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith 𝕜 T c) {x₁ x₂ b₁ b₂ : E} (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) :
    ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c := by
  have hkey : c * ‖x₁ - x₂‖ ^ 2 ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := by
    calc c * ‖x₁ - x₂‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x₁ - T x₂) (x₁ - x₂)) := hmono x₁ x₂
      _ ≤ ‖inner 𝕜 (b₁ - b₂) (x₁ - x₂)‖ := by rw [h₁, h₂]; exact RCLike.re_le_norm _
      _ ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := norm_inner_le_norm _ _
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg (x₁ - x₂)) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖x₁ - x₂‖ * c * ‖x₁ - x₂‖ = c * ‖x₁ - x₂‖ ^ 2 := by ring
      _ ≤ ‖b₁ - b₂‖ * ‖x₁ - x₂‖ := hkey

end Zarantonello
