/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.Taylor` (the segment expansion) and
`Mathlib.Algebra.MvPolynomial.Basic` (the polynomial nature of a diagonal multilinear form).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Numlib.Analysis.Calculus.Taylor
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Taylor's theorem along a segment, with the Lagrange bound

Let $E$ and $F$ be real normed spaces, $f : E \to F$, and $a, w \in E$. Restricting $f$ to the
segment $s \mapsto a + s w$, $s \in [0, 1]$, gives a curve whose $k$-th derivative is the $k$-th
Fréchet derivative of $f$ applied to $w$ in every argument. The one-dimensional Lagrange bound
`norm_sub_taylorSum_le` of `Numlib.Analysis.Calculus.Taylor`, applied to this curve, gives the
multivariate Taylor expansion
$$\Bigl\| f(a + w) - \sum_{k=0}^{n} \frac{1}{k!} D^k f(a)[w, \dots, w] \Bigr\|
  \le \frac{M \|w\|^{n+1}}{(n+1)!}$$
when $f$ is of class $C^{n+1}$ at each point of the segment and $\|D^{n+1} f\| \le M$ along it.

For $f$ real-valued and $w = \sum_i c_i w_i$ a linear combination of fixed vectors, the Taylor
polynomial is a polynomial of total degree at most $n$ in the coefficients $c$. On
$\mathbb{R}^\iota$ itself, the Taylor polynomial at $a$ is a polynomial of total degree at most $n$
in the point. This identifies the Taylor polynomial of $f$ composed with an affine parametrization
of a simplex as a polynomial of degree at most $n$, on which the sup-norm interpolation and
quadrature error estimates on a triangle rest.

## Main results

* `hasDerivAt_iteratedFDeriv_segment`: the derivative of $s \mapsto D^n f(a + s w)[w, \dots, w]$ is
  $D^{n+1} f(a + s w)[w, \dots, w]$.
* `norm_sub_taylorSum_segment_le`: Taylor's theorem along a segment, with the Lagrange bound.
* `ContinuousMultilinearMap.exists_mvPolynomial_apply_sum_smul`: a multilinear form on the diagonal
  of a linear combination is a polynomial in the coefficients.
* `exists_mvPolynomial_taylorSum` and `exists_mvPolynomial_taylorSum_pi`: the Taylor polynomial is a
  polynomial in the coefficients of the direction, and on $\mathbb{R}^\iota$ in the point.

## Implementation notes

* $D^k f(a)$ is `iteratedFDeriv ℝ k f a`, the two-sided iterated Fréchet derivative. The smoothness
  hypothesis is `ContDiffAt` at each point of the segment, so the statement applies to a function of
  class $C^{n+1}$ on any open set that contains the segment.
* A polynomial in the variables $\iota$ is an `MvPolynomial ι ℝ`, and its value at $c$ is
  `MvPolynomial.eval c`.
-/

open Set
open scoped Nat

section Segment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The derivative along a line of an iterated derivative applied to fixed vectors.** Let $E$ and
$F$ be real normed spaces, $f : E \to F$, $a, s \in E$ and $t \in \mathbb{R}$, and let $f$ be of
class $C^{n+1}$ at $a + t s$. Then for every $u = (u_1, \dots, u_n) \in E^n$ the function
$t \mapsto D^n f(a + t s)[u_1, \dots, u_n]$ has the derivative
$D^{n+1} f(a + t s)[s, u_1, \dots, u_n]$ at $t$, with the direction $s$ put before $u$.

The family $(s, u_1, \dots, u_n)$ is `Fin.cons s u`, and $D^n f(z)$ is
`iteratedFDeriv ℝ n f z`. -/
theorem hasDerivAt_iteratedFDeriv_line_apply {f : E → F} {n : ℕ} {a s : E} {t : ℝ}
    (hf : ContDiffAt ℝ (n + 1) f (a + t • s)) (u : Fin n → E) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ n f (a + t • s) u)
      (iteratedFDeriv ℝ (n + 1) f (a + t • s) (Fin.cons s u)) t := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) (a + t • s) :=
    hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
  have hline : HasDerivAt (fun t : ℝ => a + t • s) s t := by
    simpa using ((hasDerivAt_id t).smul_const s).const_add a
  have h : HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ n f (a + t • s) u)
      (fderiv ℝ (iteratedFDeriv ℝ n f) (a + t • s) s u) t :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F u).hasFDerivAt.comp_hasDerivAt
      t (hd.hasFDerivAt.comp_hasDerivAt t hline)
  convert h using 1
  rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]

/-- **The derivative along a segment of an iterated derivative applied to the direction.** Let $E$
and $F$ be real normed spaces, $f : E \to F$, $a, w \in E$ and $s \in \mathbb{R}$, and let $f$
be of class $C^{n+1}$ at $a + s w$. Then the function $s \mapsto D^n f(a + s w)[w, \dots, w]$
has the derivative $D^{n+1} f(a + s w)[w, \dots, w]$ at $s$.

The constant family $[w, \dots, w]$ is `fun _ => w`, and $D^n f(z)$ is
`iteratedFDeriv ℝ n f z`. This is the case $u = (w, \dots, w)$ of
`hasDerivAt_iteratedFDeriv_line_apply`. -/
theorem hasDerivAt_iteratedFDeriv_segment {f : E → F} {n : ℕ} {a w : E} {s : ℝ}
    (hf : ContDiffAt ℝ (n + 1) f (a + s • w)) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n f (a + s • w) (fun _ => w))
      (iteratedFDeriv ℝ (n + 1) f (a + s • w) (fun _ => w)) s := by
  convert hasDerivAt_iteratedFDeriv_line_apply hf (fun _ => w) using 2
  exact (Fin.cons_self_tail (fun _ : Fin (n + 1) => w)).symm

/-- **Taylor's theorem along a segment, with the Lagrange bound.** Let $E$ and $F$ be real normed
spaces, $f : E \to F$, $n \in \mathbb{N}$ and $a, w \in E$. Let $f$ be of class $C^{n+1}$ at
every point $a + s w$ with $s \in [0, 1]$, and let $\|D^{n+1} f(a + s w)\| \le M$ for all
$s \in [0, 1]$. Then
$$\Bigl\| f(a + w) - \sum_{k=0}^{n} \frac{1}{k!} D^k f(a)[w, \dots, w] \Bigr\|
  \le \frac{M \|w\|^{n+1}}{(n+1)!}.$$

The constant family $[w, \dots, w]$ is `fun _ => w`, and $D^k f(a)$ is
`iteratedFDeriv ℝ k f a`. The curve $s \mapsto f(a + s w)$ has the chain of derivatives
$s \mapsto D^k f(a + s w)[w, \dots, w]$ (`hasDerivAt_iteratedFDeriv_segment`), and
`norm_sub_taylorSum_le` bounds its expansion on $[0, 1]$. -/
theorem norm_sub_taylorSum_segment_le {f : E → F} {n : ℕ} {a w : E} {M : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) f (a + s • w))
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ ≤ M) :
    ‖f (a + w) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => w)‖
      ≤ M * ‖w‖ ^ (n + 1) / (n + 1)! := by
  set Y : ℕ → ℝ → F := fun k s => iteratedFDeriv ℝ k f (a + s • w) (fun _ => w) with hY
  have hchain : ∀ k ≤ n, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc 0 1) s :=
    fun k hk s hs => (hasDerivAt_iteratedFDeriv_segment
      ((hf s hs).of_le (by exact_mod_cast Nat.succ_le_succ hk))).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖Y (n + 1) s‖ ≤ M * ‖w‖ ^ (n + 1) := by
    intro s hs
    calc ‖Y (n + 1) s‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ * ∏ _i : Fin (n + 1), ‖w‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ * ‖w‖ ^ (n + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ M * ‖w‖ ^ (n + 1) := by gcongr; exact hM s hs
  have key := norm_sub_taylorSum_le zero_le_one hchain hbound
  have e0 : Y 0 1 = f (a + w) := by simp [hY]
  have e1 : ∀ k, Y k 0 = iteratedFDeriv ℝ k f a (fun _ => w) := fun k => by simp [hY]
  simp only [e0, e1, sub_zero, one_pow, one_div] at key
  simpa [div_eq_mul_inv] using key

/-- Taylor's theorem along a segment for a function of class $C^{n+1}$ on the whole space. Let $E$
and $F$ be real normed spaces, let $f : E \to F$ be of class $C^{n+1}$, let $a, w \in E$, and
let $\|D^{n+1} f(a + s w)\| \le M$ for all $s \in [0, 1]$. Then
$$\Bigl\| f(a + w) - \sum_{k=0}^{n} \frac{1}{k!} D^k f(a)[w, \dots, w] \Bigr\|
  \le \frac{M \|w\|^{n+1}}{(n+1)!}.$$

The bound $M$ is required along the segment only. This is `norm_sub_taylorSum_segment_le`. -/
theorem ContDiff.norm_sub_taylorSum_segment_le {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    {a w : E} {M : ℝ} (hM : ∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (a + s • w)‖ ≤ M) :
    ‖f (a + w) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => w)‖
      ≤ M * ‖w‖ ^ (n + 1) / (n + 1)! :=
  _root_.norm_sub_taylorSum_segment_le (fun _ _ => hf.contDiffAt) hM

end Segment

section Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- **A multilinear form on the diagonal of a linear combination is a polynomial in the
coefficients.** Let $E$ be a real normed space, $\iota$ a finite type, $A$ a continuous
$j$-linear form on $E$, and $w_i \in E$ for $i \in \iota$. Then there is a real polynomial $q$
in the variables $(X_i)_{i \in \iota}$, of total degree at most $j$, such that for all
$c \in \mathbb{R}^\iota$
$$A\Bigl( \sum_i c_i w_i, \dots, \sum_i c_i w_i \Bigr) = q(c).$$

By multilinear expansion, $q = \sum_{r} A(w_{r(0)}, \dots, w_{r(j-1)}) \prod_{l} X_{r(l)}$,
where $r$ runs over the maps $\{0, \dots, j - 1\} \to \iota$. The value $q(c)$ is
`MvPolynomial.eval c q`. -/
theorem ContinuousMultilinearMap.exists_mvPolynomial_apply_sum_smul {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) (w : ι → E) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ j ∧
      ∀ c : ι → ℝ, A (fun _ => ∑ i, c i • w i) = MvPolynomial.eval c q := by
  classical
  refine ⟨∑ r : Fin j → ι, MvPolynomial.C (A fun l => w (r l)) * ∏ l, MvPolynomial.X (r l),
    ?_, fun c => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun r _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp only [MvPolynomial.totalDegree_X, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, le_refl]
  · rw [ContinuousMultilinearMap.map_sum (f := A) (g := fun _ i => c i • w i), _root_.map_sum]
    simp only [_root_.map_mul, MvPolynomial.eval_C, _root_.map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

/-- **The Taylor polynomial along a linear parametrization is a polynomial.** Let $E$ be a real
normed space, $f : E \to \mathbb{R}$, $a \in E$, $n \in \mathbb{N}$, $\iota$ a finite type, and
$w_i \in E$ for $i \in \iota$. Then there is a real polynomial $q$ in the variables
$(X_i)_{i \in \iota}$, of total degree at most $n$, such that for all $c \in \mathbb{R}^\iota$
$$\sum_{k=0}^{n} \frac{1}{k!} D^k f(a)\Bigl[ \sum_i c_i w_i, \dots, \sum_i c_i w_i \Bigr]
  = q(c).$$

No smoothness of $f$ is needed: each $D^k f(a)$ is a continuous multilinear form, possibly zero.
$D^k f(a)$ is `iteratedFDeriv ℝ k f a`, and $q(c)$ is `MvPolynomial.eval c q`. -/
theorem exists_mvPolynomial_taylorSum {f : E → ℝ} (a : E) (n : ℕ) (w : ι → E) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ n ∧ ∀ c : ι → ℝ,
      ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => ∑ i, c i • w i)
        = MvPolynomial.eval c q := by
  classical
  have h : ∀ k, ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ k ∧
      ∀ c : ι → ℝ, iteratedFDeriv ℝ k f a (fun _ => ∑ i, c i • w i) = MvPolynomial.eval c q :=
    fun k => (iteratedFDeriv ℝ k f a).exists_mvPolynomial_apply_sum_smul w
  choose q hq using h
  refine ⟨∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) • q k, ?_, fun c => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
    exact (MvPolynomial.totalDegree_smul_le _ _).trans
      ((hq k).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  · simp only [map_sum, MvPolynomial.smul_eval, (hq _).2, smul_eq_mul]

/-- **The Taylor polynomial of a function on $\mathbb{R}^\iota$ is a polynomial in the point.** Let
$\iota$ be a finite type, $f : \mathbb{R}^\iota \to \mathbb{R}$, $a \in \mathbb{R}^\iota$ and
$n \in \mathbb{N}$. Then there is a real polynomial $q$ in the variables $(X_i)_{i \in \iota}$,
of total degree at most $n$, such that for all $y \in \mathbb{R}^\iota$
$$\sum_{k=0}^{n} \frac{1}{k!} D^k f(a)[y - a, \dots, y - a] = q(y).$$

The proof is `exists_mvPolynomial_taylorSum` along the standard basis, followed by the
substitution $X_i \mapsto X_i - a_i$, which does not raise the total degree. $D^k f(a)$ is
`iteratedFDeriv ℝ k f a`, and $q(y)$ is `MvPolynomial.eval y q`. -/
theorem exists_mvPolynomial_taylorSum_pi {f : (ι → ℝ) → ℝ} (a : ι → ℝ) (n : ℕ) :
    ∃ q : MvPolynomial ι ℝ, q.totalDegree ≤ n ∧ ∀ y : ι → ℝ,
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f a (fun _ => y - a)
        = MvPolynomial.eval y q := by
  classical
  obtain ⟨q, hqdeg, hq⟩ :=
    exists_mvPolynomial_taylorSum (f := f) a n fun i : ι => (Pi.single i 1 : ι → ℝ)
  refine ⟨MvPolynomial.bind₁ (fun i => MvPolynomial.X i - MvPolynomial.C (a i)) q, ?_, fun y => ?_⟩
  · refine (MvPolynomial.totalDegree_bind₁_le_of_totalDegree_le_one (fun i => ?_) q).trans hqdeg
    exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (MvPolynomial.totalDegree_X i).le
  · have e : (∑ i, (y - a) i • (Pi.single i 1 : ι → ℝ)) = y - a := by
      simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]
    rw [← e, hq]
    change MvPolynomial.eval₂Hom (RingHom.id ℝ) _ q
      = MvPolynomial.eval₂Hom (RingHom.id ℝ) y (MvPolynomial.bind₁ _ q)
    rw [MvPolynomial.eval₂Hom_bind₁]
    congr 2
    funext i
    simp

end Polynomial
