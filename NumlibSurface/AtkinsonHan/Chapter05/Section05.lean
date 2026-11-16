/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Numlib.Nonlinear.CompletelyContinuous

/-!
# Atkinson and Han, Section 5.5: Completely Continuous Vector Fields

This module formalizes part of Section 5.5 of [han2009theoretical]. An operator $T$ is completely
continuous on a set $K$ if it is continuous on $K$ and maps every bounded subset of $K$ to a
relatively compact set. The section is a summary: it quotes Brouwer's fixed-point theorem (Theorem
5.5.1), Schauder's fixed-point theorem (Theorem 5.5.4), Proposition 5.5.5 and the properties P1–P5
of the rotation of a completely continuous vector field without proof, from Krasnosel'skii,
*Topological Methods in the Theory of Nonlinear Integral Equations*, Krasnosel'skii and Zabreyko,
*Geometric Methods of Nonlinear Analysis*, Berger, *Nonlinearity and Functional Analysis*, and
Kantorovich and Akilov, *Functional Analysis in Normed Spaces*. This module states Definition 5.5.3
and Proposition 5.5.5, which later chapters use, and the counterexample of Example 5.5.2: a
Lipschitz map of the closed unit ball of a Hilbert space into itself that has no fixed point. The
proofs specialize the backbone module `Numlib.Nonlinear.CompletelyContinuous`.

## Main definitions

* Example 5.5.2, `AtkinsonHan.Chapter05.prepend`, `AtkinsonHan.Chapter05.prependLp` and
  `AtkinsonHan.Chapter05.shiftMap`: the map $T(v) = t(1 - \|v\|) \varphi_0 + \sum_j (v, \varphi_j)
  \varphi_{j+1}$ of the example, first in coordinates on $\ell^2$ and then on a Hilbert space.
* Definition 5.5.3, `AtkinsonHan.Chapter05.IsCompletelyContinuousOn`: a completely continuous
  operator.

## Main results

* Example 5.5.2, `AtkinsonHan.Chapter05.example_5_5_2`: for $k > 1$ and
  $0 < t \le \min(1, \sqrt{k^2 - 1})$, the map $T$ sends the closed unit ball into itself, is
  Lipschitz with the constant $k$, and has no fixed point.
* Proposition 5.5.5, `AtkinsonHan.Chapter05.proposition_5_5_5`: the Fréchet derivative of a
  completely continuous operator at an interior point is a compact linear operator.

## Implementation notes

* Compactness and continuity are separate conditions in
  `AtkinsonHan.Chapter05.IsCompletelyContinuousOn`. For a nonlinear map, compactness does not imply
  continuity, unlike for a linear map, where the notion is Mathlib's `IsCompactOperator`. The
  compactness half is the backbone's `IsCompactMap`.
* Proposition 5.5.5 lets Section 12.7 linearize a nonlinear fixed-point problem into a linear
  equation of the second kind, to which the Fredholm alternative applies.
* Half of the standard proof of Schauder's theorem exists in the backbone:
  `Continuous.exists_finset_mem_convexHull_norm_sub_lt` approximates a continuous map with totally
  bounded range, to within any $\varepsilon$, by a continuous map with values in the convex hull of
  a finite $\varepsilon$-net of its range (the Schauder projection). Schauder's theorem would follow
  from Brouwer's theorem on that finite-dimensional convex set by the usual limit argument.

## Deviations from the source

* **Example 5.5.2** (correction). The book's condition $0 < t \le \sqrt{k^2 - 1}$ does not give
  $T(K) \subseteq K$; the statement adds $t \le 1$. See `AtkinsonHan.Chapter05.example_5_5_2`.

## Not formalized

* **Theorem 5.5.1** (Brouwer's fixed-point theorem: a continuous map of a bounded, closed and convex
  set $K \subseteq \mathbb{R}^d$ into itself has a fixed point). Mathlib has neither Brouwer's
  theorem nor the means to prove it: simplicial approximation, Sperner's lemma, topological degree
  or the no-retraction theorem.
* **Theorem 5.5.4** (Schauder's fixed-point theorem: a completely continuous map of a bounded,
  closed and convex subset $K$ of a Banach space into itself has a fixed point). Its only missing
  input is Theorem 5.5.1.
* **Section 5.5.1**, the rotation of a completely continuous vector field and its properties P1–P5.
  This is degree theory, which Mathlib does not have.
-/

namespace AtkinsonHan.Chapter05

/-- **Definition 5.5.3** of [han2009theoretical]. Let $V$ be a normed space, $W$ a topological
space, $T : V \to W$ and $K \subseteq V$. Then $T$ is **completely continuous** on $K$ if $T$ is
a compact map on $K$, which means that the closure of $T(B)$ is compact for every bounded set
$B \subseteq K$, and $T$ is continuous on $K$.

The compactness condition is the backbone's `IsCompactMap T K`. -/
def IsCompletelyContinuousOn {V W : Type*} [SeminormedAddCommGroup V] [TopologicalSpace W]
    (T : V → W) (K : Set V) : Prop :=
  IsCompactMap T K ∧ ContinuousOn T K

/-- **Proposition 5.5.5** of [han2009theoretical]. Let $V$ and $W$ be real normed spaces with $W$
complete, let $K \subseteq V$ be open, and let $T : V \to W$ be completely continuous on $K$. If
$T$ has the Fréchet derivative $A$ at a point $v_0 \in K$, then $A$ is a compact linear
operator. So the Fredholm alternative applies to $I - T'(v_0)$.

The space $V$ need not be complete. The proof does not use the continuity of $T$: the backbone
proves the result from differentiability at $v_0$ and compactness on bounded sets alone. -/
theorem proposition_5_5_5 {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {T : V → W} {K : Set V}
    (hT : IsCompletelyContinuousOn T K) (hK : IsOpen K) {v₀ : V} (hv₀ : v₀ ∈ K) {A : V →L[ℝ] W}
    (hA : HasFDerivAt T A v₀) : IsCompactOperator A :=
  hT.1.isCompactOperator_hasFDerivAt (hK.mem_nhds hv₀) hA

/-! ### Example 5.5.2: a Lipschitz self-map of the unit ball with no fixed point -/

section Example552

open Filter Metric Topology Set
open scoped ENNReal

/-- Prepending a real number $c$ to a sequence $f$ gives the sequence $(c, f_0, f_1, \dots)$. On
$\ell^2(\mathbb{N}, \mathbb{R})$ this is the **unilateral shift** followed by placing $c$ in the
first coordinate. It is the map of Example 5.5.2 of [han2009theoretical] in the coordinates of
an orthonormal basis. -/
def prepend (c : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => c
  | n + 1 => f n

/-- The first term of $(c, f_0, f_1, \dots)$ is $c$. -/
@[simp] theorem prepend_zero (c : ℝ) (f : ℕ → ℝ) : prepend c f 0 = c := rfl

/-- The term $n + 1$ of $(c, f_0, f_1, \dots)$ is $f_n$. -/
@[simp] theorem prepend_succ (c : ℝ) (f : ℕ → ℝ) (n : ℕ) : prepend c f (n + 1) = f n := rfl

/-- Prepending commutes with subtraction: $(c, f_0, f_1, \dots) - (d, g_0, g_1, \dots) = (c - d,
f_0 - g_0, f_1 - g_1, \dots)$. -/
theorem prepend_sub (c d : ℝ) (f g : ℕ → ℝ) :
    prepend c f - prepend d g = prepend (c - d) (f - g) := by
  funext n
  cases n <;> simp

/-- If $f$ is square summable, then so is $(c, f_0, f_1, \dots)$. -/
theorem memℓp_prepend (c : ℝ) {f : ℕ → ℝ} (hf : Memℓp f 2) : Memℓp (prepend c f) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (summable_nat_add_iff 1).mp (by simpa using hf)

/-- The map of Example 5.5.2 of [han2009theoretical] in coordinates: for $c \in \mathbb{R}$ and
$f \in \ell^2(\mathbb{N}, \mathbb{R})$, the sequence $(c, f_0, f_1, \dots) \in
\ell^2(\mathbb{N}, \mathbb{R})$. -/
noncomputable def prependLp (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨prepend c f, memℓp_prepend c f.2⟩

/-- As a sequence, `AtkinsonHan.Chapter05.prependLp c f` is `AtkinsonHan.Chapter05.prepend c f`. -/
@[simp] theorem prependLp_coe (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) :
    ⇑(prependLp c f) = prepend c ⇑f := rfl

/-- For $c \in \mathbb{R}$ and $f \in \ell^2(\mathbb{N}, \mathbb{R})$,
$\|(c, f_0, f_1, \dots)\|^2 = c^2 + \|f\|^2$. -/
theorem norm_prependLp_sq (c : ℝ) (f : lp (fun _ : ℕ => ℝ) 2) :
    ‖prependLp c f‖ ^ 2 = c ^ 2 + ‖f‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsq : ∀ g : lp (fun _ : ℕ => ℝ) 2, ‖g‖ ^ 2 = ∑' n, ‖g n‖ ^ 2 := by
    intro g
    have h := lp.norm_rpow_eq_tsum hp g
    simpa using h
  have hsum : Summable fun n => ‖prepend c (f : ℕ → ℝ) n‖ ^ 2 := by
    have h := memℓp_prepend c (lp.memℓp f)
    rw [memℓp_gen_iff hp] at h
    simpa using h
  rw [hsq, hsq]
  simp only [prependLp_coe]
  rw [hsum.tsum_eq_zero_add]
  simp [Real.norm_eq_abs, sq_abs]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The map of **Example 5.5.2** of [han2009theoretical]. Let $V$ be a real Hilbert space with the
orthonormal basis $\{\varphi_j\}_{j \ge 0}$ and let $t \in \mathbb{R}$. The map is
$$T(v) = t(1 - \|v\|) \varphi_0 + \sum_{j \ge 0} (v, \varphi_j) \varphi_{j+1}.$$

The map is defined through the coordinate isomorphism `HilbertBasis.repr` of the basis, as
`AtkinsonHan.Chapter05.prependLp` in coordinates. -/
noncomputable def shiftMap (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v : V) : V :=
  b.repr.symm (prependLp (t * (1 - ‖v‖)) (b.repr v))

/-- The map $T$ of Example 5.5.2 satisfies $\|T(v)\|^2 = t^2 (1 - \|v\|)^2 + \|v\|^2$. -/
theorem norm_shiftMap_sq (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v : V) :
    ‖shiftMap b t v‖ ^ 2 = (t * (1 - ‖v‖)) ^ 2 + ‖v‖ ^ 2 := by
  rw [shiftMap, LinearIsometryEquiv.norm_map, norm_prependLp_sq, LinearIsometryEquiv.norm_map]

/-- The map $T$ of Example 5.5.2 satisfies $\|T(v) - T(w)\|^2 = t^2 (\|w\| - \|v\|)^2 + \|v -
w\|^2$, because the shift is an isometry. -/
theorem norm_shiftMap_sub_sq (b : HilbertBasis ℕ ℝ V) (t : ℝ) (v w : V) :
    ‖shiftMap b t v - shiftMap b t w‖ ^ 2 = (t * (‖w‖ - ‖v‖)) ^ 2 + ‖v - w‖ ^ 2 := by
  have hsub : prependLp (t * (1 - ‖v‖)) (b.repr v) - prependLp (t * (1 - ‖w‖)) (b.repr w)
      = prependLp (t * (‖w‖ - ‖v‖)) (b.repr v - b.repr w) := by
    refine Subtype.ext ?_
    have h : ⇑(prependLp (t * (1 - ‖v‖)) (b.repr v) - prependLp (t * (1 - ‖w‖)) (b.repr w))
        = prepend (t * (1 - ‖v‖)) (b.repr v) - prepend (t * (1 - ‖w‖)) (b.repr w) :=
      lp.coeFn_sub _ _
    rw [h, prepend_sub]
    have hc : t * (1 - ‖v‖) - t * (1 - ‖w‖) = t * (‖w‖ - ‖v‖) := by ring
    rw [hc]
    rfl
  rw [shiftMap, shiftMap, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map, hsub,
    norm_prependLp_sq, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]

/-- **Example 5.5.2** of [han2009theoretical]. Let $V$ be a real Hilbert space with the orthonormal
basis $\{\varphi_j\}_{j \ge 0}$, let $K$ be the closed unit ball, and let $T(v) = t(1 - \|v\|)
\varphi_0 + \sum_j (v, \varphi_j) \varphi_{j+1}$. Let $k > 1$ and
$$0 < t \le \min\bigl(1, \sqrt{k^2 - 1}\bigr).$$
Then $T$ maps $K$ into $K$, $\|T(v) - T(w)\| \le k \|v - w\|$ for all $v, w \in V$, and
$T(v) \neq v$ for every $v \in V$. So the hypotheses of Schauder's theorem cannot be weakened to
a Lipschitz condition, and Theorem 5.1.3 needs a contraction constant less than $1$.

**Correction.** The book assumes only $0 < t \le \sqrt{k^2 - 1}$. This does not give
$T(K) \subseteq K$: for $k = 2$ and $t = \sqrt 3$ the condition holds, but
$\|T(0)\|^2 = t^2 = 3 > 1$. The condition $t \le 1$ is what
$\|T(v)\|^2 = t^2 (1 - \|v\|)^2 + \|v\|^2 \le 1$ for all $\|v\| \le 1$ requires, as $v = 0$
shows. The condition $t \le \sqrt{k^2 - 1}$ is the separate condition that gives
$\sqrt{1 + t^2} \le k$. Neither condition implies the other, and the example survives: $t = 1$
gives a $\sqrt 2$-Lipschitz map of the ball into itself with no fixed point.

The map is `AtkinsonHan.Chapter05.shiftMap`. There is no fixed point in all of $V$, not only in
$K$. -/
theorem example_5_5_2 (b : HilbertBasis ℕ ℝ V) {t k : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hk : 1 < k)
    (htk : t ≤ Real.sqrt (k ^ 2 - 1)) :
    MapsTo (shiftMap b t) (closedBall 0 1) (closedBall 0 1) ∧
      (∀ v w : V, ‖shiftMap b t v - shiftMap b t w‖ ≤ k * ‖v - w‖) ∧
      ∀ v : V, shiftMap b t v ≠ v := by
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have htk2 : t ^ 2 ≤ k ^ 2 - 1 := by
    have h := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ k ^ 2 - 1)
    nlinarith [Real.sqrt_nonneg (k ^ 2 - 1)]
  refine ⟨fun v hv => ?_, fun v w => ?_, fun v hfix => ?_⟩
  · -- `T` maps the closed unit ball into itself
    simp only [mem_closedBall, dist_zero_right] at hv ⊢
    have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hsq : ‖shiftMap b t v‖ ^ 2 ≤ 1 := by
      rw [norm_shiftMap_sq]
      nlinarith [mul_nonneg hv0 (sub_nonneg.2 hv), sq_nonneg (1 - ‖v‖),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t ^ 2) (sq_nonneg (1 - ‖v‖))]
    nlinarith [norm_nonneg (shiftMap b t v)]
  · -- `T` is `k`-Lipschitz, since `√(1 + t²) ≤ k`
    have hsq : ‖shiftMap b t v - shiftMap b t w‖ ^ 2 ≤ (k * ‖v - w‖) ^ 2 := by
      rw [norm_shiftMap_sub_sq]
      have h1 : (‖w‖ - ‖v‖) ^ 2 ≤ ‖v - w‖ ^ 2 := by
        have h2 : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
          rw [abs_sub_comm]; exact abs_norm_sub_norm_le v w
        nlinarith [abs_nonneg (‖w‖ - ‖v‖), sq_abs (‖w‖ - ‖v‖)]
      nlinarith [sq_nonneg t, norm_nonneg (v - w)]
    nlinarith [norm_nonneg (shiftMap b t v - shiftMap b t w),
      mul_nonneg hk0 (norm_nonneg (v - w))]
  · -- a fixed point would have all its coordinates equal, hence zero
    set f : lp (fun _ : ℕ => ℝ) 2 := b.repr v with hfdef
    have hcoord : prepend (t * (1 - ‖v‖)) ⇑f = ⇑f := by
      have h : prependLp (t * (1 - ‖v‖)) f = f := by
        have h1 := congrArg b.repr hfix
        rw [shiftMap, LinearIsometryEquiv.apply_symm_apply] at h1
        exact h1
      exact congrArg (fun g : lp (fun _ : ℕ => ℝ) 2 => ⇑g) h
    have hconst : ∀ n : ℕ, (f : ℕ → ℝ) n = (f : ℕ → ℝ) 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [← ih, ← congrFun hcoord (n + 1), prepend_succ]
    have hsum : Summable fun n => ‖(f : ℕ → ℝ) n‖ ^ 2 := by
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have h := lp.memℓp f
      rw [memℓp_gen_iff hp] at h
      simpa using h
    have hzero : ‖(f : ℕ → ℝ) 0‖ ^ 2 = 0 := by
      have htend := hsum.tendsto_atTop_zero
      have hcongr : (fun n => ‖(f : ℕ → ℝ) n‖ ^ 2) = fun _ : ℕ => ‖(f : ℕ → ℝ) 0‖ ^ 2 :=
        funext fun n => by rw [hconst n]
      rw [hcongr] at htend
      exact tendsto_nhds_unique tendsto_const_nhds htend
    have hf0 : (f : ℕ → ℝ) 0 = 0 := by
      have h : ‖(f : ℕ → ℝ) 0‖ = 0 := by nlinarith [norm_nonneg ((f : ℕ → ℝ) 0)]
      simpa using h
    have hv0 : ‖v‖ = 0 := by
      have hz : v = 0 := by
        have hfzero : f = 0 := by
          refine Subtype.ext (funext fun n => ?_)
          rw [hconst n, hf0]
          rfl
        rw [← b.repr.symm_apply_apply v, ← hfdef, hfzero, map_zero]
      rw [hz, norm_zero]
    have hend := congrFun hcoord 0
    rw [prepend_zero, hf0, hv0] at hend
    simp only [sub_zero, mul_one] at hend
    exact ht.ne' hend

end Example552

end AtkinsonHan.Chapter05
