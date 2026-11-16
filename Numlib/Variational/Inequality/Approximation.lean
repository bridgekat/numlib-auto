/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.WeakCompactness
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.WeakMinimization

/-!
# Numerical approximation of elliptic variational inequalities

Let $V$ be a real inner product space, let $A \colon V \to V$ be strongly monotone with constant
$c > 0$ and Lipschitz with constant $L$, let $f \in V$, and let $j \colon V \to \mathbb{R}$. A
solution of the variational inequality over a set $K$ is a $u \in K$ with $\langle f, v - u \rangle
\le \langle Au, v - u \rangle + j(v) - j(u)$ for all $v \in K$. An approximation of this inequality
is the same inequality over another set $K_h$, which need not be contained in $K$. So no new notion
of discrete solution is needed, and unique solvability of the discrete problem is
`existsUnique_isVariationalInequalitySolution` again. The presentation follows §11.4 of
[han2009theoretical]: Theorems 11.4.1, 11.4.2 and 11.4.7 and Exercises 11.4.2 and 11.4.3. The error
bound is due to [falk1974error].

All results rest on one inequality. Write $R(v, w) = \langle Au, v - w \rangle + j(v) - j(w) -
\langle f, v - w \rangle$ for the residual of the continuous solution $u$. If $u$ solves the
inequality over $K$ and $u_h$ solves it over $K_h$, then the sum of the two inequalities and the
strong monotonicity inequality gives, for every $v \in K$ and $v_h \in K_h$,
$$c \|u - u_h\|^2 \le R(v, u_h) + R(v_h, u) + \langle Au - Au_h, u - v_h \rangle.$$
The same computation applies when the discrete problem has another functional $j_h$: then $j(u_h)$
in the first residual and $j(v_h)$ in the second residual are replaced by $j_h(u_h)$ and $j_h(v_h)$.
The Cauchy–Schwarz inequality, Lipschitz continuity and Young's inequality bound the last term, and
give Falk's generalized Céa lemma
$$\frac{c}{2} \|u - u_h\|^2 \le R(v, u_h) + R(v_h, u) + \frac{L^2}{2c} \|u - v_h\|^2.$$
This is pure algebra: it uses no closedness, no convexity, no topology and no limit. Every other
result of the module is a special case or a consequence.

## Main results

* `norm_sub_le_of_isVariationalInequalitySolution`: Falk's generalized Céa lemma
  ([han2009theoretical], Theorem 11.4.2).
* `norm_sub_le_of_isVariationalInequalitySolution_of_subset`: for an internal approximation,
  $K_h \subseteq K$, the choice $v = u_h$ removes the first residual.
* `norm_sub_le_of_isVariationalInequalitySolution_of_le`: replacing $j$ on the discrete set by a
  larger $j_h$ costs one use of $j(u_h) \le j_h(u_h)$ (Theorem 11.4.7).
* `norm_sub_le_of_regularization`: two problems on the whole space whose functionals differ by at
  most $c_1 \varepsilon$ have solutions within $\sqrt{2 c_1 \varepsilon / c}$ (Exercise 11.4.3).
* `tendsto_of_isVariationalInequalitySolution_of_subset`: internal approximations converge when the
  constraint sets approximate the solution and $j$ is continuous on $K$ (Exercise 11.4.2). No weak
  compactness is used, so a finite element analysis should cite this result and not the external
  one.
* `tendsto_of_isVariationalInequalitySolution`: the convergence theorem for discrete sets that need
  not lie in $K$ in the book (Theorem 11.4.1). As stated here, its hypothesis on weak limits forces
  $K_n \subseteq K$; the theorem explains why. It uses weak compactness: a bounded sequence has a
  weakly convergent subsequence, whose limit lies in $K$ by hypothesis and solves the continuous
  inequality by Minty's lemma. Minty's form is stable under weak limits because it evaluates the
  operator at the test point.
* `tendsto_of_isVariationalInequalitySolution_of_mosco`: convergence of an internal approximation
  whose discrete functional varies with the discretization, as a quadrature approximation of $j$
  does. The hypotheses that replace the single $j$ are Mosco convergence of the family, that is, a
  weak lower limit bound and recovery sequences over a dense set, and one affine minorant for the
  whole family.

## Implementation notes

* The bounds are stated squared, as the proofs give them, and not in the form $\|u - u_h\| \le C
  \inf (\|u - v_h\| + |R(v_h, u)|^{1/2})$ of the book. The infima follow by `le_ciInf`, and the
  square root by `Real.sqrt_le_sqrt` and $\sqrt{x + y} \le \sqrt{x} + \sqrt{y}$; neither step
  belongs in the statement of the estimate.
* Lipschitz continuity is `LipschitzWith L.toNNReal A` for a real $L$. A negative $L$ is read as
  $0$, and the bounds with $L^2$ hold in either case.
* In `tendsto_of_isVariationalInequalitySolution` and
  `tendsto_of_isVariationalInequalitySolution_of_mosco`, the hypotheses on weak limits quantify over
  every map $\sigma \colon \mathbb{N} \to \mathbb{N}$, not only over maps with
  $\sigma(k) \to \infty$. Constant maps then make these hypotheses stronger than in the book; each
  theorem says how.
-/

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For every real $L$, $(\max\{L, 0\})^2 \le L^2$; this lets a bound with $L^2$ be proved from a
Lipschitz constant `L.toNNReal`. -/
private theorem coe_toNNReal_sq_le (L : ℝ) : ((L.toNNReal : ℝ)) ^ 2 ≤ L ^ 2 := by
  rcases le_or_gt 0 L with hL | hL
  · rw [Real.coe_toNNReal L hL]
  · rw [Real.toNNReal_of_nonpos hL.le]
    simpa using sq_nonneg L

/-! ### The algebraic core -/

section Core

variable {A : V → V} {j jh : V → ℝ} {f : V} {K Kh : Set V} {c L : ℝ} {u uh v vh : V}

/-- Let $u$ solve the variational inequality with $j$ over $K$, and let $u_h$ solve it with $j_h$
over $K_h$. Then the sum of the continuous inequality at $v \in K$, the discrete inequality at
$v_h \in K_h$ and the strong monotonicity inequality gives $c \|u - u_h\|^2 \le \big(\langle Au,
v - u_h \rangle + j(v) - j_h(u_h) - \langle f, v - u_h \rangle\big) + \big(\langle Au, v_h - u
\rangle + j_h(v_h) - j(u) - \langle f, v_h - u \rangle\big) + \langle Au - Au_h, u - v_h
\rangle$. -/
private theorem varIneq_core (hmono : IsStronglyMonotoneWith ℝ A c)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (hv : v ∈ K) (hvh : vh ∈ Kh) :
    c * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (v - uh) + j v - jh uh - inner ℝ f (v - uh))
        + (inner ℝ (A u) (vh - u) + jh vh - j u - inner ℝ f (vh - u))
        + inner ℝ (A u - A uh) (u - vh) := by
  have hm := hmono u uh
  have h1 := hu.2 v hv
  have h2 := huh.2 vh hvh
  simp only [RCLike.re_to_real, inner_sub_left, inner_sub_right] at hm h1 h2 ⊢
  linarith

/-- Young's inequality for Falk's lemma: if $c > 0$, $M^2 \le L^2$ and $c p^2 \le R + M p q$, then
$\frac{c}{2} p^2 \le R + \frac{L^2}{2c} q^2$. -/
private theorem sq_le_of_le_add_mul {c M Lr p q R : ℝ} (hc : 0 < c) (hML : M ^ 2 ≤ Lr ^ 2)
    (h : c * p ^ 2 ≤ R + M * p * q) : c / 2 * p ^ 2 ≤ R + Lr ^ 2 / (2 * c) * q ^ 2 := by
  have h2c : (0 : ℝ) < 2 * c := by linarith
  rw [← sub_nonneg]
  have hid : R + Lr ^ 2 / (2 * c) * q ^ 2 - c / 2 * p ^ 2
      = (2 * c * R + Lr ^ 2 * q ^ 2 - c ^ 2 * p ^ 2) / (2 * c) := by
    field_simp
  rw [hid]
  refine div_nonneg ?_ h2c.le
  nlinarith [sq_nonneg (c * p - M * q), mul_le_mul_of_nonneg_left h h2c.le,
    mul_le_mul_of_nonneg_right hML (sq_nonneg q)]

/-- If $A$ is Lipschitz with constant $L$, then $\langle Ax - Ay, z \rangle \le \max\{L, 0\} \|x -
y\| \|z\|$. -/
private theorem inner_sub_apply_le (hlip : LipschitzWith L.toNNReal A) (x y z : V) :
    inner ℝ (A x - A y) z ≤ (L.toNNReal : ℝ) * ‖x - y‖ * ‖z‖ := by
  refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa only [dist_eq_norm] using hlip.dist_le_mul x y

/-- **Falk's generalized Céa lemma** ([falk1974error]; [han2009theoretical], Theorem 11.4.2 and
(11.4.7)). Let $V$ be a real inner product space, let $A \colon V \to V$ be strongly monotone
with a constant $c > 0$ and Lipschitz with constant $L$, let $f \in V$ and
$j \colon V \to \mathbb{R}$, and let $K$ and $K_h$ be subsets of $V$. Let $u$ solve the
variational inequality over $K$, and let $u_h$ solve the variational inequality with the same
$A$, $j$ and $f$ over $K_h$. Then for every $v \in K$ and every $v_h \in K_h$,
$$\frac{c}{2} \|u - u_h\|^2 \le R(v, u_h) + R(v_h, u) + \frac{L^2}{2c} \|u - v_h\|^2,$$
where $R(v, w) = \langle Au, v - w \rangle + j(v) - j(w) - \langle f, v - w \rangle$ is the
residual of the continuous solution.

The proof is pure algebra: it uses no closedness, convexity, topology or limit, and $K_h$ need
not meet $K$. For a variational equation, with $K$ a subspace, $j = 0$ and $K_h \subseteq K$,
both residuals vanish and this is Céa's lemma. A negative $L$ is read as $0$. -/
theorem norm_sub_le_of_isVariationalInequalitySolution (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) (hv : v ∈ K) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (v - uh) + j v - j uh - inner ℝ f (v - uh))
        + (inner ℝ (A u) (vh - u) + j vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 :=
  sq_le_of_le_add_mul (M := (L.toNNReal : ℝ)) hc (coe_toNNReal_sq_le L)
    ((varIneq_core hmono hu huh hv hvh).trans
      (by linarith [inner_sub_apply_le hlip u uh (u - vh)]))

/-- **Falk's lemma for internal approximations** ([han2009theoretical], the display after Theorem
11.4.2). Let $A$, $c$, $L$, $f$, $j$, $K$, $K_h$, $u$ and $u_h$ be as in
`norm_sub_le_of_isVariationalInequalitySolution`, and let $u_h \in K$, as in particular when
$K_h \subseteq K$. Then for every $v_h \in K_h$,
$$\frac{c}{2} \|u - u_h\|^2 \le R(v_h, u) + \frac{L^2}{2c} \|u - v_h\|^2.$$

The first residual of `norm_sub_le_of_isVariationalInequalitySolution` vanishes at $v = u_h$. -/
theorem norm_sub_le_of_isVariationalInequalitySolution_of_subset (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A j f Kh uh) (huhK : uh ∈ K) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (vh - u) + j vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := by
  have h := norm_sub_le_of_isVariationalInequalitySolution hc hmono hlip hu huh huhK hvh
  simpa using h

/-- **Theorem 11.4.7** of [han2009theoretical]. Let $A$, $c$, $L$, $f$, $j$, $K$ and $u$ be as in
`norm_sub_le_of_isVariationalInequalitySolution`, let $j_h \colon V \to \mathbb{R}$, and let
$u_h$ solve the variational inequality with $A$, $j_h$ and $f$ over $K_h$. Assume $u_h \in K$
and $j(u_h) \le j_h(u_h)$. Then for every $v_h \in K_h$,
$$\frac{c}{2} \|u - u_h\|^2 \le R_h(v_h, u) + \frac{L^2}{2c} \|u - v_h\|^2, \qquad R_h(v_h, u) =
  \langle Au, v_h - u \rangle + j_h(v_h) - j(u) - \langle f, v_h - u \rangle.$$

This covers a method that replaces $j$ on the discrete set by a larger functional $j_h$, as the
construction of (11.4.28) of the book by numerical integration does. The proof is Falk's
computation, with the inequality $j(u_h) \le j_h(u_h)$ at $v = u_h$. -/
theorem norm_sub_le_of_isVariationalInequalitySolution_of_le (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : IsVariationalInequalitySolution A jh f Kh uh) (huhK : uh ∈ K)
    (hjle : j uh ≤ jh uh) (hvh : vh ∈ Kh) :
    c / 2 * ‖u - uh‖ ^ 2 ≤
      (inner ℝ (A u) (vh - u) + jh vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := by
  refine sq_le_of_le_add_mul (M := (L.toNNReal : ℝ)) hc (coe_toNNReal_sq_le L) ?_
  have hcore := varIneq_core hmono hu huh huhK hvh
  simp only [sub_self, inner_zero_right] at hcore
  linarith [inner_sub_apply_le hlip u uh (u - vh)]

/-- **Exercise 11.4.3 and (11.4.20)** of [han2009theoretical]. Let $A$ be strongly monotone with a
constant $c > 0$, let $j, j_\varepsilon \colon V \to \mathbb{R}$ satisfy
$|j_\varepsilon(w) - j(w)| \le c_1 \varepsilon$ for all $w \in V$, let $u$ solve the variational
inequality with $j$ over $V$, and let $u_\varepsilon$ solve it with $j_\varepsilon$ over $V$.
Then
$$\|u - u_\varepsilon\| \le \sqrt{\frac{2 c_1 \varepsilon}{c}}.$$

This is the a priori bound with exponent $\beta = \frac12$. At $v = u_\varepsilon$ and
$v_h = u$, both residuals of the core estimate are at most $c_1 \varepsilon$ and the cross term
vanishes. So neither Lipschitz continuity nor Young's inequality is used, and the constant is
the sharp one. -/
theorem norm_sub_le_of_regularization {jeps : V → ℝ} {c₁ ε : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c)
    (hu : IsVariationalInequalitySolution A j f univ u)
    (hueps : IsVariationalInequalitySolution A jeps f univ uh)
    (hreg : ∀ w, |jeps w - j w| ≤ c₁ * ε) : ‖u - uh‖ ≤ Real.sqrt (2 * c₁ * ε / c) := by
  have hcore := varIneq_core hmono hu hueps (mem_univ uh) (mem_univ u)
  simp only [sub_self, inner_zero_right] at hcore
  have h1 : j uh - jeps uh ≤ c₁ * ε := by
    have := abs_le.1 (hreg uh)
    linarith [this.1]
  have h2 : jeps u - j u ≤ c₁ * ε := by
    have := abs_le.1 (hreg u)
    linarith [this.2]
  have hsq : ‖u - uh‖ ^ 2 ≤ 2 * c₁ * ε / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  calc ‖u - uh‖ = Real.sqrt (‖u - uh‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * c₁ * ε / c) := Real.sqrt_le_sqrt hsq

end Core

/-- If $w_n \to v$ and $j_n(w_n) \to j(v)$, then $R_{j_n}(w_n, u) + \frac{L^2}{2c} \|u - w_n\|^2$
tends to $R_j(v, u) + \frac{L^2}{2c} \|u - v\|^2$, the part of Falk's bound that does not depend
on the discrete solution. -/
private theorem tendsto_falk_majorant_of_tendsto {A : V → V} {j : V → ℝ} {jh : ℕ → V → ℝ}
    {f u v : V} {c L : ℝ} {w : ℕ → V} (hw : Tendsto w atTop (𝓝 v))
    (hjw : Tendsto (fun n => jh n (w n)) atTop (𝓝 (j v))) :
    Tendsto (fun n => (inner ℝ (A u) (w n - u) + jh n (w n) - j u - inner ℝ f (w n - u))
        + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2) atTop
      (𝓝 ((inner ℝ (A u) (v - u) + j v - j u - inner ℝ f (v - u))
        + L ^ 2 / (2 * c) * ‖u - v‖ ^ 2)) := by
  have hwu : Tendsto (fun n => w n - u) atTop (𝓝 (v - u)) :=
    hw.sub (tendsto_const_nhds (x := u))
  have hinner : ∀ y : V, Tendsto (fun n => inner ℝ y (w n - u)) atTop (𝓝 (inner ℝ y (v - u))) :=
    fun y => by
      have hcont : Continuous fun x : V => inner ℝ y x :=
        continuous_inner.comp (continuous_const.prodMk continuous_id)
      simpa [Function.comp_def] using (hcont.tendsto (v - u)).comp hwu
  have hnormw : Tendsto (fun n => ‖u - w n‖ ^ 2) atTop (𝓝 (‖u - v‖ ^ 2)) := by
    have h1 : Tendsto (fun n => ‖u - w n‖) atTop (𝓝 ‖u - v‖) :=
      ((tendsto_const_nhds (x := u) (f := atTop (α := ℕ))).sub hw).norm
    exact h1.pow 2
  have h := (((hinner (A u)).add hjw).sub (tendsto_const_nhds (x := j u))).sub (hinner f)
  exact h.add (hnormw.const_mul (L ^ 2 / (2 * c)))

/-- If $w_n \to u$ and $j(w_n) \to j(u)$, then $R_j(w_n, u) + \frac{L^2}{2c} \|u - w_n\|^2 \to 0$.
-/
private theorem tendsto_falk_majorant {A : V → V} {j : V → ℝ} {f u : V} {c L : ℝ} {w : ℕ → V}
    (hw : Tendsto w atTop (𝓝 u)) (hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u))) :
    Tendsto (fun n => (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
      + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2) atTop (𝓝 0) := by
  simpa using tendsto_falk_majorant_of_tendsto (A := A) (jh := fun _ => j) (f := f) (u := u)
    (c := c) (L := L) hw hjw

/-! ### Convergence of internal approximations -/

section Internal

variable {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {Kh : ℕ → Set V} {c L : ℝ} {u : V}
  {uh : ℕ → V}

/-- **Convergence of internal approximations** ([han2009theoretical], Exercise 11.4.2). Let $V$ be a
real inner product space, let $A$ be strongly monotone with a constant $c > 0$ and Lipschitz
with constant $L$, let $f \in V$, and let $j$ be continuous on $K$. Let $K_n \subseteq K$ for
every $n$, let $u$ solve the variational inequality over $K$, and let $u_n$ solve it over $K_n$.
Assume that there are $w_n \in K_n$ with $w_n \to u$. Then $u_n \to u$ in norm.

The proof applies `norm_sub_le_of_isVariationalInequalitySolution_of_subset` at $v_h = w_n$: the
residual $R(w_n, u)$ and $\|u - w_n\|$ tend to $0$. No weak compactness is used, and this is why
a finite element analysis should cite this result and not the external Theorem 11.4.1. -/
theorem tendsto_of_isVariationalInequalitySolution_of_subset (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hsub : ∀ n, Kh n ⊆ K) (hjc : ContinuousOn j K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n))
    {w : ℕ → V} (hwmem : ∀ n, w n ∈ Kh n) (hw : Tendsto w atTop (𝓝 u)) :
    Tendsto uh atTop (𝓝 u) := by
  set B : ℕ → ℝ := fun n => (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
    + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2 with hB
  have hbound : ∀ n, c / 2 * ‖u - uh n‖ ^ 2 ≤ B n := fun n =>
    norm_sub_le_of_isVariationalInequalitySolution_of_subset hc hmono hlip hu (huh n)
      (hsub n (huh n).1) (hwmem n)
  -- the majorant tends to zero
  have hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u)) := by
    have hwK : Tendsto w atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hw
        (Eventually.of_forall fun n => hsub n (hwmem n))
    simpa [Function.comp_def] using (hjc u hu.1).tendsto.comp hwK
  have hBzero : Tendsto B atTop (𝓝 0) := by
    rw [hB]
    exact tendsto_falk_majorant hw hjw
  -- hence so does the error
  have hzero : Tendsto (fun n => ‖u - uh n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
      (by simpa using hBzero.const_mul (2 / c))
    have h := hbound n
    have hcpos : (0 : ℝ) ≤ 2 / c := (div_pos two_pos hc).le
    calc ‖u - uh n‖ ^ 2 = 2 / c * (c / 2 * ‖u - uh n‖ ^ 2) := by field_simp
      _ ≤ 2 / c * B n := mul_le_mul_of_nonneg_left h hcpos
  have hnorm : Tendsto (fun n => ‖u - uh n‖) atTop (𝓝 0) := by
    have h := hzero.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using h
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hrev : (fun n => ‖uh n - u‖) = fun n => ‖u - uh n‖ := funext fun n => norm_sub_rev _ _
  rw [hrev]
  exact hnorm

end Internal

/-! ### Weak convergence in inner-product form -/

/-- If $\langle v_k, y \rangle \to \langle z, y \rangle$ for every $y$, then $\langle y, v_k \rangle
\to \langle y, z \rangle$ for every $y$. -/
private theorem tendsto_inner_of_weak {v : ℕ → V} {z : V}
    (hw : ∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) (y : V) :
    Tendsto (fun k => inner ℝ y (v k)) atTop (𝓝 (inner ℝ y z)) := by
  rw [real_inner_comm z y]
  exact Filter.Tendsto.congr (fun k => real_inner_comm y (v k)) (hw y)

/-! ### The steps shared by the external convergence theorems -/

/-- If $c > 0$, $g$ is bounded above and $\frac{c}{2} x_n^2 \le a x_n + g_n$ for all $n$, then the
sequence $(x_n)$ is bounded above. -/
private theorem exists_forall_le_of_half_mul_sq_le {c a : ℝ} (hc : 0 < c) {x g : ℕ → ℝ}
    (hg : BddAbove (Set.range g)) (h : ∀ n, c / 2 * x n ^ 2 ≤ a * x n + g n) :
    ∃ D, ∀ n, x n ≤ D := by
  obtain ⟨C₂, hC₂⟩ := hg
  have hGle : ∀ n, g n ≤ max C₂ 0 := fun n => le_trans (hC₂ ⟨n, rfl⟩) (le_max_left _ _)
  have hC₂0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
  refine ⟨max 1 (2 * (a + max C₂ 0) / c), fun n => ?_⟩
  rcases le_or_gt (x n) 1 with hx | hx
  · exact hx.trans (le_max_left _ _)
  · refine le_max_of_le_right ?_
    rw [le_div_iff₀ hc]
    have hd0 : (0 : ℝ) < x n := lt_trans zero_lt_one hx
    have hkey := h n
    have hG := hGle n
    have hstep : x n * (c / 2 * x n) ≤ x n * (a + max C₂ 0) := by
      nlinarith [mul_nonneg hC₂0 (le_of_lt (sub_pos.2 hx))]
    have hfin := le_of_mul_le_mul_left hstep hd0
    linarith

/-- Minty's form of the limit step: along a reindexing on which the discrete solutions converge
weakly to $z$, and with test points $p_n \in K_n$ converging to $v$ with $j_{n}(p_n) \to j_v$,
every $\alpha > \langle Av, v - z \rangle - \langle f, v - z \rangle + j_v$ eventually bounds
$j_n(u_n)$ from above. -/
private theorem eventually_lt_of_tendsto_minty {A : V → V} {jh : ℕ → V → ℝ} {f : V}
    {Kh : ℕ → Set V} {L D jv : ℝ} {uh p : ℕ → V} {u v z : V} {s : ℕ → ℕ}
    (hmono : ∀ x y : V, (0 : ℝ) ≤ inner ℝ (A x - A y) (x - y)) (hlip : LipschitzWith L.toNNReal A)
    (huh : ∀ n, IsVariationalInequalitySolution A (jh n) f (Kh n) (uh n))
    (hD : ∀ n, ‖u - uh n‖ ≤ D) (hs : Tendsto s atTop atTop)
    (hweak : ∀ y : V, Tendsto (fun k => inner ℝ (uh (s k)) y) atTop (𝓝 (inner ℝ z y)))
    (hpmem : ∀ n, p n ∈ Kh n) (hp : Tendsto p atTop (𝓝 v))
    (hjp : Tendsto (fun k => jh (s k) (p (s k))) atTop (𝓝 jv)) {α : ℝ}
    (hα : inner ℝ (A v) (v - z) - inner ℝ f (v - z) + jv < α) :
    ∀ᶠ k in atTop, jh (s k) (uh (s k)) < α := by
  have hAlip : ∀ x y : V, ‖A x - A y‖ ≤ (L.toNNReal : ℝ) * ‖x - y‖ := fun x y => by
    simpa only [dist_eq_norm] using hlip.dist_le_mul x y
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → ℝ, ∀ n, E n =
      inner ℝ (A v) (p n - uh n) - inner ℝ f (p n - uh n) + jh n (p n)
        + ‖A (p n) - A v‖ * ‖p n - uh n‖ := ⟨_, fun _ => rfl⟩
  have hjle : ∀ n, jh n (uh n) ≤ E n := by
    intro n
    have h1 := (huh n).2 (p n) (hpmem n)
    have h2 := hmono (p n) (uh n)
    have h3 : inner ℝ (A (p n) - A v) (p n - uh n) ≤ ‖A (p n) - A v‖ * ‖p n - uh n‖ :=
      real_inner_le_norm _ _
    rw [inner_sub_left] at h2 h3
    rw [hEdef]
    linarith
  have hpm : Tendsto (fun k => p (s k)) atTop (𝓝 v) := hp.comp hs
  have hpair : ∀ y : V, Tendsto (fun k => inner ℝ y (p (s k) - uh (s k))) atTop
      (𝓝 (inner ℝ y (v - z))) := by
    intro y
    have hcont : Continuous fun x : V => inner ℝ y x :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    have h1 : Tendsto (fun k => inner ℝ y (p (s k))) atTop (𝓝 (inner ℝ y v)) := by
      simpa [Function.comp_def] using (hcont.tendsto v).comp hpm
    have h2 := tendsto_inner_of_weak hweak y
    have h3 : (fun k => inner ℝ y (p (s k) - uh (s k)))
        = fun k => inner ℝ y (p (s k)) - inner ℝ y (uh (s k)) := by
      funext k
      rw [inner_sub_right]
    have h4 : inner ℝ y (v - z) = inner ℝ y v - inner ℝ y z := inner_sub_right _ _ _
    rw [h3, h4]
    exact h1.sub h2
  have hq : Tendsto (fun k => ‖p (s k) - v‖) atTop (𝓝 0) := by
    have h := hpm.sub (tendsto_const_nhds (x := v))
    simpa using h.norm
  have herr : Tendsto (fun k => ‖A (p (s k)) - A v‖ * ‖p (s k) - uh (s k)‖) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun k => (L.toNNReal : ℝ) * ‖p (s k) - v‖
        * (‖p (s k) - v‖ + (‖v - u‖ + D))) atTop (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := ((L.toNNReal : ℝ)))).mul hq).mul
        (hq.add (tendsto_const_nhds (x := ‖v - u‖ + D)))
      simpa using h
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hmaj
    have hb1 : ‖A (p (s k)) - A v‖ ≤ (L.toNNReal : ℝ) * ‖p (s k) - v‖ := hAlip _ _
    have ht1 : ‖p (s k) - uh (s k)‖ ≤ ‖p (s k) - v‖ + ‖v - uh (s k)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (p (s k)) v (uh (s k))
    have ht2 : ‖v - uh (s k)‖ ≤ ‖v - u‖ + ‖u - uh (s k)‖ := by
      simpa only [dist_eq_norm] using dist_triangle v u (uh (s k))
    have hb2 : ‖p (s k) - uh (s k)‖ ≤ ‖p (s k) - v‖ + (‖v - u‖ + D) := by
      have hdb := hD (s k)
      linarith
    exact mul_le_mul hb1 hb2 (norm_nonneg _)
      (mul_nonneg (L.toNNReal).coe_nonneg (norm_nonneg _))
  have hE : Tendsto (fun k => E (s k)) atTop
      (𝓝 (inner ℝ (A v) (v - z) - inner ℝ f (v - z) + jv)) := by
    have h := (((hpair (A v)).sub (hpair f)).add hjp).add herr
    simpa [hEdef] using h
  filter_upwards [hE.eventually (eventually_lt_nhds hα)] with k hk
  exact (hjle (s k)).trans_lt hk

/-- If the discrete solutions converge weakly to $u$, then $\langle a, u - u_k \rangle - \langle f,
u - u_k \rangle \to 0$. -/
private theorem tendsto_inner_sub_sub_inner_sub_of_weak {uh : ℕ → V} {u a f : V}
    (hweak : ∀ y : V, Tendsto (fun k => inner ℝ (uh k) y) atTop (𝓝 (inner ℝ u y))) :
    Tendsto (fun k => inner ℝ a (u - uh k) - inner ℝ f (u - uh k)) atTop (𝓝 0) := by
  have h : ∀ y : V, Tendsto (fun k => inner ℝ y (u - uh k)) atTop (𝓝 0) := by
    intro y
    have h1 : Tendsto (fun k => inner ℝ y (uh k)) atTop (𝓝 (inner ℝ y u)) :=
      tendsto_inner_of_weak hweak y
    have h3 : (fun k => inner ℝ y (u - uh k)) = fun k => inner ℝ y u - inner ℝ y (uh k) := by
      funext k
      rw [inner_sub_right]
    rw [h3]
    simpa using (tendsto_const_nhds (x := inner ℝ y u)).sub h1
  simpa using (h a).sub (h f)

/-! ### Convergence of external approximations -/

section External

variable [CompleteSpace V] {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {Kh : ℕ → Set V}
  {c L : ℝ} {u : V} {uh : ℕ → V}

/-- **Theorem 11.4.1** of [han2009theoretical]. Let $V$ be a real Hilbert space, let $A$ be strongly
monotone with a constant $c > 0$ and Lipschitz with constant $L$, let $f \in V$, let $K$ be
convex, and let $j$ be convex and continuous on $V$. Assume:

* every $v \in K$ is the limit of a sequence $w_n \in K_n$;
* for every map $\sigma \colon \mathbb{N} \to \mathbb{N}$ and every sequence
  $v_k \in K_{\sigma(k)}$ that converges weakly to some $z$, the limit $z$ lies in $K$.

Let $u$ solve the variational inequality over $K$, and let $u_n$ solve it over $K_n$. Then
$u_n \to u$ in norm.

The proof has three steps. First, the discrete solutions are bounded: test at an approximation
of $u$, and use an affine minorant of $j$. Second, a weakly convergent subsequence has its limit
$z$ in $K$, and $z$ solves the continuous inequality: the discrete inequalities in Minty's form
pass to the weak limit, because Minty's form evaluates the operator at the test point, and $j$
is weakly sequentially lower semicontinuous, because it is convex and continuous. So $z = u$.
Third, the same estimate turns weak convergence into norm convergence.

Because $\sigma$ can be constant, the second hypothesis applied to constant sequences gives
$K_n \subseteq K$ for every $n$. So, as stated, the theorem applies only to internal
approximations. A hypothesis restricted to maps with $\sigma(k) \to \infty$ would not have this
consequence. For internal approximations with $K$ convex and closed, the second hypothesis
follows from `mem_of_weak_tendsto_of_convex`, and
`tendsto_of_isVariationalInequalitySolution_of_subset` gives the conclusion without weak
compactness. -/
theorem tendsto_of_isVariationalInequalitySolution (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hKcv : Convex ℝ K) (hjcv : ConvexOn ℝ univ j) (hjc : Continuous j)
    (happrox : ∀ v ∈ K, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧ Tendsto w atTop (𝓝 v))
    (hweak : ∀ (σ : ℕ → ℕ) (v : ℕ → V) (z : V), (∀ k, v k ∈ Kh (σ k)) →
      (∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) → z ∈ K)
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A j f (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) := by
  have hAcont : Continuous A := hlip.continuous
  have hjK : ConvexOn ℝ K j := hjcv.subset (subset_univ K) hKcv
  have hjwlsc : WeakSeqLowerSemicontinuousOn j univ :=
    hjcv.weakSeqLowerSemicontinuousOn (hjc.lowerSemicontinuous.lowerSemicontinuousOn _)
  have hmono0 : IsStronglyMonotoneWith ℝ A 0 := IsStronglyMonotoneWith.mono hmono hc.le
  have hmono0' : ∀ x y : V, (0 : ℝ) ≤ inner ℝ (A x - A y) (x - y) := fun x y => by
    simpa using hmono0 x y
  -- an affine minorant of the convex continuous `j`
  obtain ⟨lin, bb, hminor⟩ : ∃ (lin : V →L[ℝ] ℝ) (bb : ℝ), ∀ x : V, lin x + bb ≤ j x := by
    obtain ⟨l0, c0, hle, -⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j 0 - 1)
      (mem_univ (0 : V)) (by linarith) isClosed_univ
      (hjc.lowerSemicontinuous.lowerSemicontinuousOn univ) hjcv
    exact ⟨l0, c0, fun x => by simpa using hle ⟨x, mem_univ x⟩⟩
  -- an approximating sequence for `u`, and the part of Falk's bound that does not see `u_h`
  obtain ⟨w, hwmem, hw⟩ := happrox u hu.1
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n =
      (inner ℝ (A u) (w n - u) + j (w n) - j u - inner ℝ f (w n - u))
        + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hjw : Tendsto (fun n => j (w n)) atTop (𝓝 (j u)) := by
    simpa [Function.comp_def] using (hjc.tendsto u).comp hw
  have hΨ0 : Tendsto Ψ atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun n => (hΨdef n).symm) (tendsto_falk_majorant hw hjw)
  -- Falk's bound at `v = u` and `v_h = w n`
  have hfalk : ∀ n, c / 2 * ‖u - uh n‖ ^ 2
      ≤ (inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n)) + (j u - j (uh n)) + Ψ n := by
    intro n
    have h := norm_sub_le_of_isVariationalInequalitySolution hc hmono hlip hu (huh n) hu.1
      (hwmem n)
    rw [hΨdef]
    linarith
  -- the discrete solutions are bounded
  have hbnd : ∀ n, c / 2 * ‖u - uh n‖ ^ 2
      ≤ (‖A u - f‖ + ‖lin‖) * ‖u - uh n‖ + ((j u - lin u - bb) + Ψ n) := by
    intro n
    have h := hfalk n
    have h1 : inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n) ≤ ‖A u - f‖ * ‖u - uh n‖ := by
      rw [← inner_sub_left]
      exact real_inner_le_norm _ _
    have h2 : -j (uh n) ≤ lin (u - uh n) - lin u - bb := by
      have h3 := hminor (uh n)
      rw [map_sub]
      linarith
    have h4 : lin (u - uh n) ≤ ‖lin‖ * ‖u - uh n‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using lin.le_opNorm (u - uh n))
    linarith
  obtain ⟨D, hDbnd⟩ := exists_forall_le_of_half_mul_sq_le hc (x := fun n => ‖u - uh n‖)
    (Filter.Tendsto.const_add (j u - lin u - bb) hΨ0).bddAbove_range hbnd
  have hUB : ∀ n, ‖uh n‖ ≤ ‖u‖ + D := by
    intro n
    have h : ‖uh n‖ = ‖u - (u - uh n)‖ := by congr 1; abel
    rw [h]
    exact le_trans (norm_sub_le _ _) (by linarith [hDbnd n])
  -- every subsequence has a further subsequence converging in norm
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨σ, z, hσ, hweakconv⟩ :=
    exists_subseq_weak_tendsto (𝕜 := ℝ) (u := fun k => uh (ns k)) (C := ‖u‖ + D)
      (fun k => hUB (ns k))
  refine ⟨σ, ?_⟩
  have hmtop : Tendsto (fun k => ns (σ k)) atTop atTop := by
    simpa [Function.comp_def] using hns.comp hσ.tendsto_atTop
  have hzK : z ∈ K := hweak (fun k => ns (σ k)) (fun k => uh (ns (σ k))) z
    (fun k => (huh (ns (σ k))).1) hweakconv
  -- the weak limit satisfies the Minty form of the inequality
  have hzminty : ∀ v ∈ K, inner ℝ f (v - z) ≤ inner ℝ (A v) (v - z) + j v - j z := by
    intro v hv
    obtain ⟨p, hpmem, hp⟩ := happrox v hv
    have hjp : Tendsto (fun k => j (p (ns (σ k)))) atTop (𝓝 (j v)) := by
      simpa [Function.comp_def] using (hjc.tendsto v).comp (hp.comp hmtop)
    have hkey : j z ≤ inner ℝ (A v) (v - z) - inner ℝ f (v - z) + j v := by
      by_contra hcon
      push Not at hcon
      obtain ⟨α, hα1, hα2⟩ := exists_between hcon
      have h1 : ∀ᶠ k in atTop, α < j (uh (ns (σ k))) :=
        hjwlsc _ _ (fun _ => mem_univ _) (mem_univ _)
          (weakSeqTendsto_iff_forall_tendsto_inner.2 hweakconv) _ hα2
      have h2 : ∀ᶠ k in atTop, j (uh (ns (σ k))) < α :=
        eventually_lt_of_tendsto_minty (jh := fun _ => j) hmono0' hlip huh hDbnd hmtop hweakconv
          hpmem hp hjp hα1
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      exact absurd hk1 (not_lt.2 hk2.le)
    linarith
  have hzsol : IsVariationalInequalitySolution A j f K z := by
    refine (IsVariationalInequalitySolution.iff_minty hKcv hjK hmono0 hzK ?_).2 hzminty
    intro y _
    exact (hAcont.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt
  have hzu : z = u := IsVariationalInequalitySolution.unique hc hmono hzsol hu
  rw [hzu] at hweakconv
  -- and then the error tends to zero along that subsequence
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hrev : (fun k => ‖uh (ns (σ k)) - u‖) = fun k => ‖u - uh (ns (σ k))‖ :=
    funext fun k => norm_sub_rev _ _
  rw [hrev]
  refine tendsto_order.2
    ⟨fun b hb => Eventually.of_forall fun k => lt_of_lt_of_le hb (norm_nonneg _), fun b hb => ?_⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = c / 2 * b ^ 2 / 3 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hP1 : Tendsto (fun k => inner ℝ (A u) (u - uh (ns (σ k)))
      - inner ℝ f (u - uh (ns (σ k)))) atTop (𝓝 0) :=
    tendsto_inner_sub_sub_inner_sub_of_weak (uh := fun k => uh (ns (σ k))) hweakconv
  have hP2 : ∀ᶠ k in atTop, j u - j (uh (ns (σ k))) < ε := by
    have h := hjwlsc _ _ (fun _ => mem_univ _) (mem_univ _)
      (weakSeqTendsto_iff_forall_tendsto_inner.2 hweakconv) (j u - ε) (by linarith)
    filter_upwards [h] with k hk
    linarith
  have hP3 : ∀ᶠ k in atTop, Ψ (ns (σ k)) < ε := by
    have hΨm : Tendsto (fun k => Ψ (ns (σ k))) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hΨ0.comp hmtop
    exact hΨm.eventually (eventually_lt_nhds hε)
  filter_upwards [hP1.eventually (eventually_lt_nhds hε), hP2, hP3] with k h1 h2 h3
  have hf := hfalk (ns (σ k))
  have h3ε : (3 : ℝ) * ε = c / 2 * b ^ 2 := by rw [hεdef]; ring
  have hd2 : ‖u - uh (ns (σ k))‖ ^ 2 < b ^ 2 := by
    nlinarith
  have hsq := Real.sqrt_lt_sqrt (sq_nonneg _) hd2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb.le] at hsq

end External

/-! ### Convergence when the discrete functional varies -/

section Varying

variable [CompleteSpace V] {A : V → V} {j : V → ℝ} {jh : ℕ → V → ℝ} {f : V} {K U : Set V}
  {Kh : ℕ → Set V} {c L : ℝ} {u : V} {uh : ℕ → V}

/-- **Convergence of an internal approximation whose functional varies with the discretization.** In
the theorems above, one functional $j$ is shared by the continuous problem and all discrete
problems. Here the discrete problem number $n$ has its own functional $j_n$, as when the
functional of the continuous problem is computed by a quadrature rule. Let $V$ be a real Hilbert
space, let $A$ be strongly monotone with a constant $c > 0$ and Lipschitz with constant $L$, let
$f \in V$, let $K$ be convex and closed, and let $j$ be continuous on $V$ and convex on $K$.
Assume:

* the approximation is internal: $K_n \subseteq K$ for every $n$;
* the family $(j_n)$ is uniformly proper: there are a bounded linear functional $\lambda$ and
  $b \in \mathbb{R}$ with $\lambda(v) + b \le j_n(v)$ for all $n$ and all $v \in K_n$;
* the family is weakly sequentially lower semicontinuous: for every map
  $\sigma \colon \mathbb{N} \to \mathbb{N}$ and every sequence $v_k \in K_{\sigma(k)}$ that
  converges weakly to some $z$, every $\alpha < j(z)$ satisfies $\alpha < j_{\sigma(k)}(v_k)$
  for all large $k$;
* there are recovery sequences over a set $U$ with $K \subseteq \overline{U}$: for every
  $v \in U$ there are $w_n \in K_n$ with $w_n \to v$ and $j_n(w_n) \to j(v)$.

Let $u$ solve the variational inequality with $j$ over $K$, and let $u_n$ solve it with $j_n$
over $K_n$. Then $u_n \to u$ in norm.

The last two hypotheses are Mosco convergence of the family to $j$ [mosco1969convergence]: a
weak lower limit bound and a strong recovery sequence. The lower limit is written as an eventual
strict inequality, which is what the proof uses and which needs no boundedness of the values;
over $\mathbb{R}$, `Filter.liminf` has no meaningful value for a sequence that is unbounded
below. Because $\sigma$ can be constant, this hypothesis applied to constant sequences gives
$j(v) \le j_n(v)$ for all $n$ and $v \in K_n$. The choice $j_n = j$ and $U = K$ gives
`tendsto_of_isVariationalInequalitySolution` for an internal approximation, since a convex
continuous functional is weakly sequentially lower semicontinuous.

The proof is that of `tendsto_of_isVariationalInequalitySolution`, with three changes. The lower
bound on $j_n(u_n)$ in the boundedness step comes from the uniform minorant of the family, not
from an affine minorant of $j$. The weak lower semicontinuity is the hypothesis on the family,
not `ConvexOn.weakSeqLowerSemicontinuousOn` for $j$. A recovery sequence exists only over $U$,
and $u$ need not lie in $U$, so the two steps that approximate the continuous solution pass
through $U$ by a limit: Minty's inequality for the weak limit is proved on $U$ and extended to
$K$ by continuity of $A$ and $j$, and the final estimate is applied at a point of $U$ where the
residual of $u$ is below a given $\varepsilon$. So continuity of $j$ is used, and only for these
two limits. On a complete space, a real-valued convex lower semicontinuous functional on the
whole space is continuous, so continuity is no extra assumption in that case. -/
theorem tendsto_of_isVariationalInequalitySolution_of_mosco (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith L.toNNReal A)
    (hKcv : Convex ℝ K) (hKcl : IsClosed K) (hjcv : ConvexOn ℝ K j) (hjc : Continuous j)
    (hsub : ∀ n, Kh n ⊆ K)
    (hproper : ∃ (lin : V →L[ℝ] ℝ) (b : ℝ), ∀ n, ∀ v ∈ Kh n, lin v + b ≤ jh n v)
    (hjlsc : ∀ (σ : ℕ → ℕ) (v : ℕ → V) (z : V), (∀ k, v k ∈ Kh (σ k)) →
      (∀ y : V, Tendsto (fun k => inner ℝ (v k) y) atTop (𝓝 (inner ℝ z y))) →
      ∀ α < j z, ∀ᶠ k in atTop, α < jh (σ k) (v k))
    (hU : K ⊆ closure U)
    (happrox : ∀ v ∈ U, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧ Tendsto w atTop (𝓝 v) ∧
      Tendsto (fun n => jh n (w n)) atTop (𝓝 (j v)))
    (hu : IsVariationalInequalitySolution A j f K u)
    (huh : ∀ n, IsVariationalInequalitySolution A (jh n) f (Kh n) (uh n)) :
    Tendsto uh atTop (𝓝 u) := by
  have hAcont : Continuous A := hlip.continuous
  have hmono0 : IsStronglyMonotoneWith ℝ A 0 := IsStronglyMonotoneWith.mono hmono hc.le
  have hmono0' : ∀ x y : V, (0 : ℝ) ≤ inner ℝ (A x - A y) (x - y) := fun x y => by
    simpa using hmono0 x y
  obtain ⟨lin, bb, hminor⟩ := hproper
  -- [falk1974error] bound, the continuous inequality tested at `v = u`
  have hfalk : ∀ (n : ℕ) (vh : V), vh ∈ Kh n → c / 2 * ‖u - uh n‖ ^ 2 ≤
      (inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n)) + (j u - jh n (uh n))
        + (inner ℝ (A u) (vh - u) + jh n vh - j u - inner ℝ f (vh - u))
        + L ^ 2 / (2 * c) * ‖u - vh‖ ^ 2 := fun n vh hvh =>
    sq_le_of_le_add_mul (M := (L.toNNReal : ℝ)) hc (coe_toNNReal_sq_le L)
      ((varIneq_core hmono hu (huh n) hu.1 hvh).trans
        (by linarith [inner_sub_apply_le hlip u (uh n) (u - vh)]))
  -- the residual of the continuous solution at a test point, together with the Young term
  obtain ⟨G, hGdef⟩ : ∃ G : V → ℝ, ∀ x, G x =
      (inner ℝ (A u) (x - u) + j x - j u - inner ℝ f (x - u))
        + L ^ 2 / (2 * c) * ‖u - x‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hGu : G u = 0 := by simp [hGdef]
  have hGcont : Continuous G := by
    have hin : ∀ y : V, Continuous fun x : V => inner ℝ y (x - u) := fun y =>
      continuous_inner.comp (continuous_const.prodMk (continuous_id.sub continuous_const))
    have hG : G = fun x : V => (inner ℝ (A u) (x - u) + j x - j u - inner ℝ f (x - u))
        + L ^ 2 / (2 * c) * ‖u - x‖ ^ 2 := funext hGdef
    rw [hG]
    exact ((((hin (A u)).add hjc).sub continuous_const).sub (hin f)).add
      (((continuous_const.sub continuous_id).norm.pow 2).const_mul _)
  -- along a recovery sequence the majorant converges to the residual at its limit point
  have hmaj : ∀ v ∈ U, ∃ w : ℕ → V, (∀ n, w n ∈ Kh n) ∧
      Tendsto (fun n => (inner ℝ (A u) (w n - u) + jh n (w n) - j u - inner ℝ f (w n - u))
        + L ^ 2 / (2 * c) * ‖u - w n‖ ^ 2) atTop (𝓝 (G v)) := by
    intro v hv
    obtain ⟨w, hwmem, hw, hjw⟩ := happrox v hv
    refine ⟨w, hwmem, ?_⟩
    rw [hGdef v]
    exact tendsto_falk_majorant_of_tendsto hw hjw
  -- the discrete solutions are bounded, by one recovery sequence and the uniform minorant
  obtain ⟨v₀, hv₀⟩ : U.Nonempty := closure_nonempty_iff.1 ⟨u, hU hu.1⟩
  obtain ⟨w₀, hw₀mem, hw₀⟩ := hmaj v₀ hv₀
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, Ψ n =
      (inner ℝ (A u) (w₀ n - u) + jh n (w₀ n) - j u - inner ℝ f (w₀ n - u))
        + L ^ 2 / (2 * c) * ‖u - w₀ n‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hΨlim : Tendsto Ψ atTop (𝓝 (G v₀)) :=
    Filter.Tendsto.congr (fun n => (hΨdef n).symm) hw₀
  have hbnd : ∀ n, c / 2 * ‖u - uh n‖ ^ 2
      ≤ (‖A u - f‖ + ‖lin‖) * ‖u - uh n‖ + ((j u - lin u - bb) + Ψ n) := by
    intro n
    have h := hfalk n (w₀ n) (hw₀mem n)
    have h1 : inner ℝ (A u) (u - uh n) - inner ℝ f (u - uh n) ≤ ‖A u - f‖ * ‖u - uh n‖ := by
      rw [← inner_sub_left]
      exact real_inner_le_norm _ _
    have h2 : -jh n (uh n) ≤ lin (u - uh n) - lin u - bb := by
      have h3 := hminor n (uh n) (huh n).1
      rw [map_sub]
      linarith
    have h4 : lin (u - uh n) ≤ ‖lin‖ * ‖u - uh n‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using lin.le_opNorm (u - uh n))
    rw [hΨdef]
    linarith
  obtain ⟨D, hDbnd⟩ := exists_forall_le_of_half_mul_sq_le hc (x := fun n => ‖u - uh n‖)
    (Filter.Tendsto.const_add (j u - lin u - bb) hΨlim).bddAbove_range hbnd
  have hUB : ∀ n, ‖uh n‖ ≤ ‖u‖ + D := by
    intro n
    have h : ‖uh n‖ = ‖u - (u - uh n)‖ := by congr 1; abel
    rw [h]
    exact le_trans (norm_sub_le _ _) (by linarith [hDbnd n])
  -- every subsequence has a further subsequence converging in norm
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨σ, z, hσ, hweakconv⟩ :=
    exists_subseq_weak_tendsto (𝕜 := ℝ) (u := fun k => uh (ns k)) (C := ‖u‖ + D)
      (fun k => hUB (ns k))
  refine ⟨σ, ?_⟩
  have hmtop : Tendsto (fun k => ns (σ k)) atTop atTop := by
    simpa [Function.comp_def] using hns.comp hσ.tendsto_atTop
  have hzK : z ∈ K :=
    hKcv.isWeakSeqClosed hKcl _ _ (fun k => hsub _ (huh (ns (σ k))).1)
      (weakSeqTendsto_iff_forall_tendsto_inner.2 hweakconv)
  -- the weak limit satisfies Minty's form of the inequality, first at the points of `U`
  have hzmintyU : ∀ v ∈ U, inner ℝ f (v - z) ≤ inner ℝ (A v) (v - z) + j v - j z := by
    intro v hv
    obtain ⟨p, hpmem, hp, hjp0⟩ := happrox v hv
    have hjp : Tendsto (fun k => jh (ns (σ k)) (p (ns (σ k)))) atTop (𝓝 (j v)) := by
      simpa [Function.comp_def] using hjp0.comp hmtop
    have hkey : j z ≤ inner ℝ (A v) (v - z) - inner ℝ f (v - z) + j v := by
      by_contra hcon
      push Not at hcon
      obtain ⟨α, hα1, hα2⟩ := exists_between hcon
      have h1 : ∀ᶠ k in atTop, α < jh (ns (σ k)) (uh (ns (σ k))) :=
        hjlsc (fun k => ns (σ k)) (fun k => uh (ns (σ k))) z
          (fun k => (huh (ns (σ k))).1) hweakconv α hα2
      have h2 : ∀ᶠ k in atTop, jh (ns (σ k)) (uh (ns (σ k))) < α :=
        eventually_lt_of_tendsto_minty hmono0' hlip huh hDbnd hmtop hweakconv hpmem hp hjp hα1
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      exact absurd hk1 (not_lt.2 hk2.le)
    linarith
  -- and then at every point of `K`, by density and the continuity of `A` and `j`
  have hzminty : ∀ v ∈ K, inner ℝ f (v - z) ≤ inner ℝ (A v) (v - z) + j v - j z := by
    intro v hv
    obtain ⟨q, hqU, hq⟩ := mem_closure_iff_seq_limit.1 (hU hv)
    have hqz : Tendsto (fun k => q k - z) atTop (𝓝 (v - z)) :=
      hq.sub (tendsto_const_nhds (x := z))
    have h1 : Tendsto (fun k => inner ℝ f (q k - z)) atTop (𝓝 (inner ℝ f (v - z))) := by
      have hcont : Continuous fun x : V => inner ℝ f x :=
        continuous_inner.comp (continuous_const.prodMk continuous_id)
      simpa [Function.comp_def] using (hcont.tendsto (v - z)).comp hqz
    have h2 : Tendsto (fun k => inner ℝ (A (q k)) (q k - z) + j (q k) - j z) atTop
        (𝓝 (inner ℝ (A v) (v - z) + j v - j z)) := by
      have hAq : Tendsto (fun k => A (q k)) atTop (𝓝 (A v)) := by
        simpa [Function.comp_def] using (hAcont.tendsto v).comp hq
      have hin : Tendsto (fun k => inner ℝ (A (q k)) (q k - z)) atTop
          (𝓝 (inner ℝ (A v) (v - z))) := by
        simpa [Function.comp_def] using
          (continuous_inner.tendsto ((A v, v - z) : V × V)).comp (hAq.prodMk_nhds hqz)
      have hjq : Tendsto (fun k => j (q k)) atTop (𝓝 (j v)) := by
        simpa [Function.comp_def] using (hjc.tendsto v).comp hq
      exact (hin.add hjq).sub tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' h1 h2 fun k => hzmintyU (q k) (hqU k)
  have hzsol : IsVariationalInequalitySolution A j f K z := by
    refine (IsVariationalInequalitySolution.iff_minty hKcv hjcv hmono0 hzK ?_).2 hzminty
    intro y _
    exact (hAcont.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt
  have hzu : z = u := IsVariationalInequalitySolution.unique hc hmono hzsol hu
  rw [hzu] at hweakconv
  -- and then the error tends to zero along that subsequence
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hrev : (fun k => ‖uh (ns (σ k)) - u‖) = fun k => ‖u - uh (ns (σ k))‖ :=
    funext fun k => norm_sub_rev _ _
  rw [hrev]
  refine tendsto_order.2
    ⟨fun b hb => Eventually.of_forall fun k => lt_of_lt_of_le hb (norm_nonneg _), fun b hb => ?_⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = c / 2 * b ^ 2 / 3 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  -- a point of `U` at which the residual of the continuous solution is below `ε`
  obtain ⟨v, hvU, hvG⟩ : ∃ v ∈ U, G v < ε := by
    have hnhd : G ⁻¹' Iio ε ∈ 𝓝 u :=
      hGcont.continuousAt (Iio_mem_nhds (by rw [hGu]; exact hε))
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 (hU hu.1) _ hnhd
    exact ⟨y, hy2, hy1⟩
  obtain ⟨w, hwmem, hwlim⟩ := hmaj v hvU
  have hP1 : Tendsto (fun k => inner ℝ (A u) (u - uh (ns (σ k)))
      - inner ℝ f (u - uh (ns (σ k)))) atTop (𝓝 0) :=
    tendsto_inner_sub_sub_inner_sub_of_weak (uh := fun k => uh (ns (σ k))) hweakconv
  have hP2 : ∀ᶠ k in atTop, j u - jh (ns (σ k)) (uh (ns (σ k))) < ε := by
    have h := hjlsc (fun k => ns (σ k)) (fun k => uh (ns (σ k))) u
      (fun k => (huh (ns (σ k))).1) hweakconv (j u - ε) (by linarith)
    filter_upwards [h] with k hk
    linarith
  have hP3 : ∀ᶠ k in atTop, (inner ℝ (A u) (w (ns (σ k)) - u)
      + jh (ns (σ k)) (w (ns (σ k))) - j u - inner ℝ f (w (ns (σ k)) - u))
        + L ^ 2 / (2 * c) * ‖u - w (ns (σ k))‖ ^ 2 < ε := by
    have hm : Tendsto (fun k => (inner ℝ (A u) (w (ns (σ k)) - u)
        + jh (ns (σ k)) (w (ns (σ k))) - j u - inner ℝ f (w (ns (σ k)) - u))
          + L ^ 2 / (2 * c) * ‖u - w (ns (σ k))‖ ^ 2) atTop (𝓝 (G v)) := by
      simpa [Function.comp_def] using hwlim.comp hmtop
    exact hm.eventually (eventually_lt_nhds hvG)
  filter_upwards [hP1.eventually (eventually_lt_nhds hε), hP2, hP3] with k h1 h2 h3
  have hfk := hfalk (ns (σ k)) (w (ns (σ k))) (hwmem (ns (σ k)))
  have h3ε : (3 : ℝ) * ε = c / 2 * b ^ 2 := by rw [hεdef]; ring
  have hd2 : ‖u - uh (ns (σ k))‖ ^ 2 < b ^ 2 := by
    nlinarith
  have hsq := Real.sqrt_lt_sqrt (sq_nonneg _) hd2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb.le] at hsq

end Varying
