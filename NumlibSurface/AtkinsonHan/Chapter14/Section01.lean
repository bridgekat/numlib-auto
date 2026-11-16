/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.MvPolynomial
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.RingTheory.MvPolynomial.TotalDegree

/-!
# Atkinson and Han, Section 14.1: Multivariable polynomials and best approximation

This module formalizes the definitions of Section 14.1 of [han2009theoretical], which fix the
notation of Chapter 14. The space $\Pi_n^d$ consists of the real polynomials in $d$ variables of
total degree at most $n$, and its dimension is $\binom{n + d}{d}$. For a continuous function $f$ on
a compact set $D \subseteq \mathbb{R}^d$, the minimax error is $E_n(f) = \inf \{\|f - p\|_\infty : p
\in \Pi_n^d\}$. Exercise 14.1.1 shows that an invertible affine change of variables maps $\Pi_n^d$
onto $\Pi_n^d$, which carries the results from the unit disk to an ellipse.

The space $\Pi_n^d$ is Mathlib's `MvPolynomial.restrictTotalDegree`, and its dimension is the
backbone `MvPolynomial.finrank_restrictTotalDegree` of `Numlib.Approximation.MvPolynomial`. The
minimax error is the distance to the copy `Approximation.mvPolyLE` of $\Pi_n^d$ inside $C(D)$.

## Main definitions

* `AtkinsonHan.Chapter14.polySpace`: the space $\Pi_n^d$.
* `AtkinsonHan.Chapter14.minimaxError`: the minimax error $E_n(f)$.
* Exercise 14.1.1, `AtkinsonHan.Chapter14.affineSubst`: the substitution $p(x) \mapsto p(M x + v)$.
* Exercise 14.1.1, `AtkinsonHan.Chapter14.ellipsoid`: the solid ellipsoid
  $\{x : \sum_i (x_i / a_i)^2 \le 1\}$.

## Main results

* `AtkinsonHan.Chapter14.finrank_polySpace`: $\dim \Pi_n^d = \binom{n + d}{d}$.
* `AtkinsonHan.Chapter14.finrank_polySpace_two`: $\dim \Pi_n^2 = (n + 1)(n + 2)/2$.
* `AtkinsonHan.Chapter14.minimaxError_antitone`: $E_n(f)$ decreases as $n$ increases.
* Exercise 14.1.1, `AtkinsonHan.Chapter14.exercise_14_1_1`: an invertible affine change of variables
  maps $\Pi_n^d$ onto $\Pi_n^d$.
* Exercise 14.1.1, `AtkinsonHan.Chapter14.image_mulVec_diagonal_ellipsoid`: the diagonal map
  $x \mapsto (a_i x_i)_i$ maps the unit ball onto the ellipsoid with semi-axes $a_i$.

## Conventions

* Exercise 14.1.1 (`AtkinsonHan.Chapter14.exercise_14_1_1`), on the affine change of variables, is
  unrelated to Theorem 14.1.1, Ragozin's theorem.
* A point of $\mathbb{R}^d$ is a function `Fin d → ℝ`, and a polynomial in $d$ variables is an
  element of `MvPolynomial (Fin d) ℝ`.

## Implementation notes

* The vocabulary of best approximation is that of the backbone, `IsBestApprox` and `Metric.infDist`,
  so `AtkinsonHan.Chapter14.minimaxError` is a distance and not a new notion.

## Not formalized

* **Theorem 14.1.1** (Ragozin's multivariate Jackson theorem). For $f \in C^k(\mathbb{B}_d)$ there
  are polynomials $p_n \in \Pi_n^d$ with $\|f - p_n\|_\infty \le (c(k, d) / n^k) [\|f\|_{*,k} / n +
  \omega_k(f, 1/n)]$ (14.1.2), with a constant that depends only on $k$ and $d$. It is the
  multivariate form of Jackson's Theorem 3.7.2. The book quotes it from D. L. Ragozin, *Constructive
  polynomial approximation on spheres and projective spaces*, Trans. Amer. Math. Soc. 162 (1971),
  Theorem 3.4, and says that the proof is too complicated to give. The proof goes through
  approximation on the sphere $S^d$, and needs spherical harmonics, a surface measure on $S^d$ with
  an integration formula, and a convolution structure on the sphere; Mathlib has none of the three.
  Within the part of the book that this library covers, only Theorem 14.2.5 depends on Theorem
  14.1.1, and Theorem 14.2.5 is not formalized either.
* **The higher moduli of continuity** $\omega_n(f, h) = \sum_{|\alpha| = n} \omega(\partial^\alpha
  f, h)$ **and the norm** $\|f\|_{*,n} = \max_{|\alpha| \le n} \|\partial^\alpha f\|_\infty$, with
  which Theorem 14.1.1 is stated. Without Theorem 14.1.1, Chapter 14 does not use them. The modulus
  of continuity $\omega(f, h) = \sup_{|x - y| \le h} |f(x) - f(y)|$ itself is the backbone
  `ContinuousMap.modulusOfContinuity`.
-/

open Module
open scoped Matrix

namespace AtkinsonHan.Chapter14

/-- For $d, n \in \mathbb{N}$, the space $\Pi_n^d$ of the real polynomials in $d$ variables of total
degree at most $n$.

It is `MvPolynomial.restrictTotalDegree (Fin d) ℝ n`. -/
noncomputable abbrev polySpace (d n : ℕ) : Submodule ℝ (MvPolynomial (Fin d) ℝ) :=
  MvPolynomial.restrictTotalDegree (Fin d) ℝ n

/-- A polynomial $p$ in $d$ variables is in $\Pi_n^d$ if and only if its total degree is at most
$n$. -/
theorem mem_polySpace_iff {d n : ℕ} {p : MvPolynomial (Fin d) ℝ} :
    p ∈ polySpace d n ↔ p.totalDegree ≤ n := by
  rw [polySpace, MvPolynomial.mem_restrictTotalDegree]

/-- The spaces $\Pi_n^d$ increase with $n$: $\Pi_n^d \subseteq \Pi_m^d$ for $n \le m$. -/
theorem polySpace_mono {d : ℕ} : Monotone (polySpace d) := fun _ _ h =>
  MvPolynomial.restrictTotalDegree_mono _ _ h

/-- **Section 14.1** of [han2009theoretical], the dimension of $\Pi_n^d$. For all
$d, n \in \mathbb{N}$, $$\dim \Pi_n^d = \binom{n + d}{d},$$ the number of monomials $x^\alpha$
with $|\alpha| \le n$.

The proof is the backbone `MvPolynomial.finrank_restrictTotalDegree`. -/
theorem finrank_polySpace (d n : ℕ) : finrank ℝ (polySpace d n) = (n + d).choose d := by
  simpa using MvPolynomial.finrank_restrictTotalDegree (Fin d) n ℝ

/-- **Section 14.1** of [han2009theoretical], the dimension of $\Pi_n^2$. For every
$n \in \mathbb{N}$, $$\dim \Pi_n^2 = \frac{(n + 1)(n + 2)}{2}.$$

The division is the division of natural numbers, which is exact here because $(n + 1)(n + 2)$ is
even. -/
theorem finrank_polySpace_two (n : ℕ) : finrank ℝ (polySpace 2 n) = (n + 1) * (n + 2) / 2 := by
  rw [finrank_polySpace, Nat.choose_two_right, show n + 2 - 1 = n + 1 from rfl, Nat.mul_comm]

/-- **Section 14.1** of [han2009theoretical], the minimax error. Let $D \subseteq \mathbb{R}^d$ be
compact and $f \in C(D)$. The **minimax error** of $f$ is $$E_n(f) = \inf \{\|f - p\|_\infty : p
\in \Pi_n^d\},$$ the distance from $f$ to the restrictions to $D$ of the polynomials in
$\Pi_n^d$.

The definition is `Metric.infDist` from $f$ to `Approximation.mvPolyLE D n`, the copy of
$\Pi_n^d$ inside $C(D)$. -/
noncomputable def minimaxError {d : ℕ} {D : Set (Fin d → ℝ)} [CompactSpace D] (n : ℕ)
    (f : C(D, ℝ)) : ℝ :=
  Metric.infDist f (Approximation.mvPolyLE D n : Set C(D, ℝ))

/-- **Section 14.1** of [han2009theoretical]. For a compact $D \subseteq \mathbb{R}^d$ and
$f \in C(D)$, the minimax error $E_n(f)$ is a decreasing function of $n$, because the spaces
$\Pi_n^d$ increase. -/
theorem minimaxError_antitone {d : ℕ} {D : Set (Fin d → ℝ)} [CompactSpace D] (f : C(D, ℝ)) :
    Antitone fun n => minimaxError n f := fun _ _ h =>
  Metric.infDist_le_infDist_of_subset (Approximation.mvPolyLE_mono h) ⟨0, Submodule.zero_mem _⟩

/-! ### Exercise 14.1.1: An affine change of variables -/

/-- Let $M$ be a real $d \times d$ matrix and $v \in \mathbb{R}^d$. For $1 \le i \le d$, the $i$-th
coordinate polynomial of the affine map $x \mapsto M x + v$ is $v_i + \sum_j M_{ij} X_j$. It
supports Exercise 14.1.1. -/
noncomputable def affineForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin d) :
    MvPolynomial (Fin d) ℝ :=
  MvPolynomial.C (v i) + ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

/-- The coordinate polynomial $v_i + \sum_j M_{ij} X_j$ evaluated at $x$ is the $i$-th coordinate of
$M x + v$. -/
@[simp]
theorem eval_affineForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (i : Fin d)
    (x : Fin d → ℝ) : MvPolynomial.eval x (affineForm M v i) = (M *ᵥ x + v) i := by
  simp [affineForm, Matrix.mulVec, dotProduct, add_comm]

/-- The coordinate polynomial $v_i + \sum_j M_{ij} X_j$ has total degree at most $1$. -/
theorem totalDegree_affineForm_le {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (i : Fin d) : (affineForm M v i).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le (by simp) ?_)
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- **Exercise 14.1.1** of [han2009theoretical], the substitution. Let $M$ be a real $d \times d$
matrix and $v \in \mathbb{R}^d$. The **affine change of variables** is the algebra homomorphism
on the polynomials in $d$ variables that maps $p$ to the polynomial $x \mapsto p(M x + v)$.

It is `MvPolynomial.bind₁` of the coordinate polynomials `AtkinsonHan.Chapter14.affineForm M v`. -/
noncomputable def affineSubst {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ :=
  MvPolynomial.bind₁ (affineForm M v)

/-- The affine change of variables evaluates as $(p \circ (M \cdot + v))(x) = p(M x + v)$ for every
polynomial $p$ and every $x \in \mathbb{R}^d$. -/
theorem eval_affineSubst {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) :
    MvPolynomial.eval x (affineSubst M v p) = MvPolynomial.eval (M *ᵥ x + v) p := by
  rw [affineSubst, ← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval,
    MvPolynomial.aeval_bind₁]
  exact congrArg (fun w => MvPolynomial.aeval w p) (funext fun i => eval_affineForm M v i x)

/-- Let $M$ be an invertible real $d \times d$ matrix and $v \in \mathbb{R}^d$. The affine map
$x \mapsto M^{-1} x - M^{-1} v$ is inverse to $x \mapsto M x + v$, so for every polynomial $q$,
substituting first $M^{-1} x - M^{-1} v$ and then $M x + v$ gives $q$ back. -/
theorem affineSubst_affineSubst_inv {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) (q : MvPolynomial (Fin d) ℝ) :
    affineSubst M v (affineSubst M⁻¹ (-(M⁻¹ *ᵥ v)) q) = q := by
  refine MvPolynomial.funext fun x => ?_
  rw [eval_affineSubst, eval_affineSubst]
  congr 1
  simp only [Matrix.mulVec_add,
    Matrix.nonsing_inv_mulVec_mulVec ((Matrix.isUnit_iff_isUnit_det M).2 hM)]
  abel_nf

/-- Let $M$ be an invertible real $d \times d$ matrix and $v \in \mathbb{R}^d$. For every polynomial
$p$, substituting first $M x + v$ and then $M^{-1} x - M^{-1} v$ gives $p$ back. -/
theorem affineSubst_inv_affineSubst {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) (p : MvPolynomial (Fin d) ℝ) :
    affineSubst M⁻¹ (-(M⁻¹ *ᵥ v)) (affineSubst M v p) = p := by
  refine MvPolynomial.funext fun x => ?_
  rw [eval_affineSubst, eval_affineSubst]
  congr 1
  simp only [Matrix.mulVec_add, Matrix.mulVec_neg,
    Matrix.mulVec_nonsing_inv_mulVec ((Matrix.isUnit_iff_isUnit_det M).2 hM)]
  abel_nf

/-- **Exercise 14.1.1** of [han2009theoretical]. Let $M$ be a real $d \times d$ matrix with $\det M$
invertible, and let $v \in \mathbb{R}^d$. Then the affine change of variables
$p(x) \mapsto p(M x + v)$ maps $\Pi_n^d$ onto $\Pi_n^d$.

This makes the results of Section 14.1 on the unit disk the same results on an ellipse: the
linear map that takes the disk onto the ellipse takes the polynomials of degree at most $n$ on
the one to the polynomials of degree at most $n$ on the other. The bound on the degree is
`MvPolynomial.totalDegree_bind₁_le` for the coordinate polynomials, each of total degree at most
$1$; the surjectivity is the same bound for the inverse substitution. -/
theorem exercise_14_1_1 {d n : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : IsUnit M.det)
    (v : Fin d → ℝ) :
    (polySpace d n).map (affineSubst M v).toLinearMap = polySpace d n :=
  MvPolynomial.restrictTotalDegree_map_bind₁ (totalDegree_affineForm_le M v)
    (totalDegree_affineForm_le M⁻¹ (-(M⁻¹ *ᵥ v))) (affineSubst_inv_affineSubst hM v)
    (affineSubst_affineSubst_inv hM v) n

/-- **Exercise 14.1.1** of [han2009theoretical], the ellipse. For $a \in \mathbb{R}^d$, the **solid
ellipsoid** with semi-axes $a_i$ is $$\Bigl\{x \in \mathbb{R}^d : \sum_i (x_i / a_i)^2 \le
1\Bigr\}.$$ For $d = 2$ and $a = (\alpha, \beta)$ it is the ellipse
$(x/\alpha)^2 + (y/\beta)^2 \le 1$ of Exercise 14.1.1, and for $a = (1, \dots, 1)$ it is the
closed unit ball.

If some $a_i = 0$, Lean's division gives $x_i / a_i = 0$, so the coordinate $x_i$ is not
constrained. -/
def ellipsoid {d : ℕ} (a : Fin d → ℝ) : Set (Fin d → ℝ) := {x | ∑ i, (x i / a i) ^ 2 ≤ 1}

/-- **Exercise 14.1.1** of [han2009theoretical], the change of variables. Let $a \in \mathbb{R}^d$
with $a_i \neq 0$ for all $i$. Then the diagonal linear map $x \mapsto (a_i x_i)_i$ maps the
closed unit ball onto the solid ellipsoid with semi-axes $a_i$. The map is invertible, so
`AtkinsonHan.Chapter14.exercise_14_1_1` applies to it. -/
theorem image_mulVec_diagonal_ellipsoid {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) :
    (fun x => Matrix.diagonal a *ᵥ x) '' ellipsoid 1 = ellipsoid a := by
  ext y
  simp only [Set.mem_image, ellipsoid, Set.mem_ofPred_eq, Pi.one_apply, div_one]
  refine ⟨?_, fun hy => ⟨fun i => y i / a i, ?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have hcoord : ∀ i, (Matrix.diagonal a *ᵥ x) i / a i = x i := fun i => by
      rw [Matrix.mulVec_diagonal, mul_comm, mul_div_assoc, div_self (ha i), mul_one]
    simpa only [hcoord] using hx
  · exact hy
  · funext i
    rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (ha i)]

/-- If $a_i \neq 0$ for all $i$, then the determinant of the diagonal matrix
$\operatorname{diag}(a)$ is invertible. -/
theorem isUnit_det_diagonal {d : ℕ} {a : Fin d → ℝ} (ha : ∀ i, a i ≠ 0) :
    IsUnit (Matrix.diagonal a).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i

end AtkinsonHan.Chapter14
