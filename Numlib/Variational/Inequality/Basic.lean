/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Approximation
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Normed.Module.BestApprox
import Numlib.Variational.LaxMilgram

/-!
# Elliptic variational inequalities

Let $V$ be a real Hilbert space, $K \subseteq V$ a nonempty closed convex set, $A : V \to V$ an
operator, $j : V \to \mathbb{R}$ a functional and $f \in V$. The **elliptic variational inequality**
asks for
$$u \in K, \qquad \langle f, v - u \rangle \le \langle Au, v - u \rangle + j(v) - j(u)
  \quad \text{for all } v \in K.$$
The inequality of the first kind is the case $j = 0$, the inequality of the second kind is the case
$K = V$, and the problems given by a bilinear form $a$ are the case where $A$ is the operator with
$\langle Au, v \rangle = a(u, v)$. The presentation follows Chapter 11 of [han2009theoretical].

The module proves that a solution is unique and depends Lipschitz continuously on $f$ when $A$ is
strongly monotone, and that it exists when $A$ is also Lipschitz continuous and $j$ is convex and
lower semicontinuous. For a symmetric elliptic bilinear form $a$ and $\ell \in V'$, the solution is
the minimizer over $K$ of the energy $E(v) = \tfrac12 a(v, v) + j(v) - \ell(v)$. The module also
proves Minty's lemma and the special forms of the inequality on a cone and for a positively
homogeneous $j$.

## Main definitions

* `IsVariationalInequalitySolution`: $u$ solves the elliptic variational inequality with operator
  $A$, functional $j$, datum $f$ and set $K$.

## Main results

* `IsVariationalInequalitySolution.norm_sub_le`, `IsVariationalInequalitySolution.unique`: for a
  $c$-strongly monotone $A$, solutions with data $f_1$ and $f_2$ satisfy
  $\|u_1 - u_2\| \le \|f_1 - f_2\| / c$, so the solution is unique.
* `existsUnique_isMinOn_energy_add`: for a symmetric elliptic form $a$ and a convex lower
  semicontinuous $j$, the energy $E$ has exactly one minimizer over a nonempty closed convex set
  $K$.
* `isMinOn_energy_add_iff`: a point minimizes $E$ over $K$ if and only if it solves the variational
  inequality with the operator of $a$ and the Riesz representative of $\ell$.
* `existsUnique_isVariationalInequalitySolution_on`: if $A$ is strongly monotone and Lipschitz
  continuous on $K$ and $j$ is convex and lower semicontinuous on $K$, the variational inequality
  has exactly one solution.
* `existsUnique_isVariationalInequalitySolution`: the same theorem with the hypotheses on $A$ on all
  of $V$.
* `stampacchia`: Stampacchia's theorem, the case $j = 0$.
* `existsUnique_isVariationalInequalitySolution_of_isCoercive`: unique solvability for a bounded
  elliptic bilinear form that need not be symmetric.
* `IsVariationalInequalitySolution.iff_minty`: Minty's lemma, the equivalent form with $A$ evaluated
  at the test point.
* `IsVariationalInequalitySolution.isBestApprox_energy`: for a symmetric coercive linear $A$ and
  $j = 0$, the solution is the best approximation from $K$, in the energy norm of $A$, to the
  solution of $Aw = f$.
* `IsVariationalInequalitySolution.iff_of_isCone`,
  `IsVariationalInequalitySolution.iff_of_isPositiveHomogeneous`: the equivalent forms on a convex
  cone and for a positively homogeneous $j$.

## Proof outline

The minimizer of $E$ is found in the Hilbert space directly, without the direct method in a
reflexive space. The functional $j$ has a continuous affine minorant, so $E$ is bounded below.
Ellipticity and convexity of $j$ give $E(x) + E(y) - 2E(\tfrac12(x + y)) \ge \tfrac{c}{4}\|x -
y\|^2$, so every minimizing sequence is a Cauchy sequence. For a general $A$, the map that sends $u$
to the solution of the inequality with the identity operator and datum $u - \theta(Au - f)$ is a
contraction with factor $\sqrt{1 - 2c\theta + L^2\theta^2}$ for $0 < \theta < 2c/L^2$, and its fixed
point is the solution. All iterates stay in $K$, so the hypotheses on $A$ are needed on $K$ only.

## Implementation notes

* The datum is a vector $f \in V$ and not a functional. The two are interchangeable by the Riesz
  representation `SesqForm.rieszRep`.
* Strong monotonicity is `IsStronglyMonotoneWith` of `Numlib.Nonlinear.FixedPoint`, which is also
  the hypothesis of `zarantonello` and `contractingWith_damped`, so these results compose with no
  translation lemma. `LinearMap.IsCoerciveWith.isStronglyMonotoneWith` connects it to the coercivity
  of a linear operator.
* `IsVariationalInequalitySolution` unfolds to `And` and `IsStronglyMonotoneWith` unfolds to a
  universal statement, so dot notation on a hypothesis of either type can resolve in the wrong
  namespace. Write the lemma names in full.
-/

open Filter Set Topology

section StronglyMonotone

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A coercive linear operator is strongly monotone with the same constant: if $A : E \to E$ is
linear and $\operatorname{Re} \langle Ax, x \rangle \ge c \|x\|^2$ for all $x$, then
$\operatorname{Re} \langle Ax - Ay, x - y \rangle \ge c \|x - y\|^2$ for all $x, y \in E$. -/
theorem LinearMap.IsCoerciveWith.isStronglyMonotoneWith {A : E →ₗ[𝕜] E} {c : ℝ}
    (h : A.IsCoerciveWith c) : IsStronglyMonotoneWith 𝕜 (A : E → E) c := fun x y => by
  simpa only [map_sub] using h (x - y)

end StronglyMonotone

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **elliptic variational inequality**. Let $V$ be a real inner product space, $A : V \to V$,
$j : V \to \mathbb{R}$, $f \in V$ and $K \subseteq V$. A point $u$ **solves the variational
inequality** if $u \in K$ and
$$\langle f, v - u \rangle \le \langle Au, v - u \rangle + j(v) - j(u) \quad \text{for all } v
  \in K.$$
This is the problem of (11.3.3), (11.3.8), (11.3.9) and (11.3.12)–(11.3.14) of
[han2009theoretical].

The inequality of the first kind is the case $j = 0$, and the inequality of the second kind is
the case `K = Set.univ`. The problems with a bilinear form $a$ are the case
`A = SesqForm.toOperator a`. The datum is a vector $f$, which the Riesz representation makes
interchangeable with a functional. The definition puts no hypothesis on $A$, $j$ or $K$. -/
def IsVariationalInequalitySolution (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, inner ℝ f (v - u) ≤ inner ℝ (A u) (v - u) + j v - j u

section Uniqueness

variable {A : V → V} {j : V → ℝ} {K : Set V} {c : ℝ}

/-- Let $V$ be a real inner product space, $K \subseteq V$ and $j : V \to \mathbb{R}$, and let
$A : V \to V$ be strongly monotone on $K$ with constant $c > 0$. If $u_1$ and $u_2$ solve the
variational inequality with data $f_1$ and $f_2$, then $\|u_1 - u_2\| \le \|f_1 - f_2\| / c$.

Both solutions lie in $K$, so strong monotonicity on $K$ is enough. Lipschitz continuity of $A$,
convexity of $j$ and closedness of $K$ are not used. This is the last clause of Theorem 11.3.1
of [han2009theoretical]. The case of an equation $Au = f$ is `norm_sub_le_of_strongly_monotone`. -/
theorem IsVariationalInequalitySolution.norm_sub_le_on (hc : 0 < c)
    (hmono : IsStronglyMonotoneOnWith ℝ A K c) {f₁ f₂ u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f₁ K u₁)
    (h₂ : IsVariationalInequalitySolution A j f₂ K u₂) : ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c := by
  have e₁ := h₁.2 u₂ h₂.1
  have e₂ := h₂.2 u₁ h₁.1
  have hneg₁ : inner ℝ f₁ (u₂ - u₁) = -inner ℝ f₁ (u₁ - u₂) := by
    rw [← inner_neg_right]; congr 1; abel
  have hneg₂ : inner ℝ (A u₁) (u₂ - u₁) = -inner ℝ (A u₁) (u₁ - u₂) := by
    rw [← inner_neg_right]; congr 1; abel
  rw [hneg₁, hneg₂] at e₁
  -- adding the two inequalities, each tested at the other solution, cancels the values of `j`
  have hkey : inner ℝ (A u₁ - A u₂) (u₁ - u₂) ≤ inner ℝ (f₁ - f₂) (u₁ - u₂) := by
    rw [inner_sub_left, inner_sub_left]
    linarith
  have hmono' : c * ‖u₁ - u₂‖ ^ 2 ≤ inner ℝ (f₁ - f₂) (u₁ - u₂) :=
    (hmono u₁ h₁.1 u₂ h₂.1).trans hkey
  have hcs : inner ℝ (f₁ - f₂) (u₁ - u₂) ≤ ‖f₁ - f₂‖ * ‖u₁ - u₂‖ := real_inner_le_norm _ _
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg (u₁ - u₂)) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖u₁ - u₂‖ * c * ‖u₁ - u₂‖ = c * ‖u₁ - u₂‖ ^ 2 := by ring
      _ ≤ ‖f₁ - f₂‖ * ‖u₁ - u₂‖ := hmono'.trans hcs

/-- **Lipschitz dependence on the datum.** Let $V$ be a real inner product space, $K \subseteq V$
and $j : V \to \mathbb{R}$, and let $A : V \to V$ be strongly monotone with constant $c > 0$,
that is, $\langle Ax - Ay, x - y \rangle \ge c \|x - y\|^2$ for all $x, y \in V$. If $u_1$ and
$u_2$ solve the variational inequality with data $f_1$ and $f_2$, then
$$\|u_1 - u_2\| \le \frac{\|f_1 - f_2\|}{c}.$$
This is the last clause of Theorem 11.3.1 of [han2009theoretical].

This is the case of `IsVariationalInequalitySolution.norm_sub_le_on` in which $A$ is strongly
monotone on all of $V$. -/
theorem IsVariationalInequalitySolution.norm_sub_le (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) {f₁ f₂ u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f₁ K u₁)
    (h₂ : IsVariationalInequalitySolution A j f₂ K u₂) : ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / c :=
  norm_sub_le_on hc (hmono.isStronglyMonotoneOnWith K) h₁ h₂

/-- Let $A$ be strongly monotone on $K$ with constant $c > 0$. Then two solutions of the same
variational inequality, with the same $j$, $f$ and $K$, are equal. -/
theorem IsVariationalInequalitySolution.unique_on (hc : 0 < c)
    (hmono : IsStronglyMonotoneOnWith ℝ A K c) {f u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f K u₁)
    (h₂ : IsVariationalInequalitySolution A j f K u₂) : u₁ = u₂ := by
  have h := IsVariationalInequalitySolution.norm_sub_le_on hc hmono h₁ h₂
  simp only [sub_self, norm_zero, zero_div] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- **Uniqueness.** Let $V$ be a real inner product space, $K \subseteq V$, $j : V \to \mathbb{R}$
and $f \in V$, and let $A : V \to V$ be strongly monotone with constant $c > 0$. Then two
solutions $u_1$ and $u_2$ of the variational inequality are equal. This is the uniqueness clause
of Theorem 11.3.1 of [han2009theoretical]. -/
theorem IsVariationalInequalitySolution.unique (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) {f u₁ u₂ : V}
    (h₁ : IsVariationalInequalitySolution A j f K u₁)
    (h₂ : IsVariationalInequalitySolution A j f K u₂) : u₁ = u₂ :=
  unique_on hc (hmono.isStronglyMonotoneOnWith K) h₁ h₂

end Uniqueness

/-! ### The energy functional of a symmetric form -/

section Energy

/-- For a symmetric real form $a$, the energy $E(v) = \tfrac12 a(v, v) - \ell(v)$ satisfies $E(u +
w) = E(u) + (a(u, w) - \ell(w)) + \tfrac12 a(w, w)$; this is `SesqForm.energy_add_sub_energy`
with the real scalars written without real parts. -/
private theorem energy_add (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) (u w : V) :
    a.energy ℓ (u + w) = a.energy ℓ u + (a u w - ℓ w) + 1 / 2 * a w w := by
  have h := a.energy_add_sub_energy ℓ ha u w
  simp only [RCLike.re_to_real] at h
  linarith

/-- For a symmetric real form $a$, the energy $E(v) = \tfrac12 a(v, v) - \ell(v)$ has at $u$ the
directional derivative $a(u, h) - \ell(h)$ in every direction $h$. -/
private theorem hasLineDerivAt_energy (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (u h : V) : HasLineDerivAt ℝ (a.energy ℓ) ((a u - ℓ) h) u h := by
  have hfun : (fun t : ℝ => a.energy ℓ (u + t • h))
      = fun t : ℝ => a.energy ℓ u + t * (a u h - ℓ h) + 1 / 2 * t ^ 2 * a h h := by
    funext t
    rw [energy_add a ha ℓ u (t • h)]
    simp only [map_smulₛₗ, smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply,
      star_trivial]
    ring
  have hd : HasDerivAt (fun t : ℝ => a.energy ℓ (u + t • h)) ((a u - ℓ) h) 0 := by
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => a.energy ℓ u + t * (a u h - ℓ h)) (a u h - ℓ h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (a u h - ℓ h)).const_add (a.energy ℓ u)
    have h2 : HasDerivAt (fun t : ℝ => 1 / 2 * t ^ 2 * a h h) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (1 / 2 : ℝ)).mul_const (a h h)
    have h3 := h1.add h2
    have hval : (a u - ℓ) h = (a u h - ℓ h) + 0 := by simp
    rw [hval]
    exact h3
  exact hd

/-- For a symmetric real form $a$ with $a(w, w) \ge 0$ for all $w$, the energy
$E(v) = \tfrac12 a(v, v) - \ell(v)$ is convex on every convex set. -/
private theorem convexOn_energy (a : SesqForm ℝ V) (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (hpos : ∀ w : V, 0 ≤ a w w) {K : Set V} (hK : Convex ℝ K) : ConvexOn ℝ K (a.energy ℓ) := by
  refine convexOn_of_add_lineDeriv_le (f' := fun w => a w - ℓ) hK fun u _ v _ => ?_
  have hexp := energy_add a ha ℓ u (v - u)
  rw [show u + (v - u) = v by abel] at hexp
  have hq := hpos (v - u)
  simp only [sub_apply]
  linarith

end Energy

/-! ### Existence and characterization of the constrained minimizer -/

section Minimization

variable [CompleteSpace V]

/-- **Existence and uniqueness of the constrained minimizer.** Let $V$ be a real Hilbert space, and
let $a$ be a bounded symmetric bilinear form on $V$ that is elliptic with constant $c > 0$, that
is, $a(v, v) \ge c \|v\|^2$ for all $v$. Let $\ell \in V'$, let $K \subseteq V$ be nonempty,
closed and convex, and let $j : V \to \mathbb{R}$ be convex and lower semicontinuous on $K$.
Then the functional
$$E(v) = \tfrac12 a(v, v) + j(v) - \ell(v)$$
has exactly one minimizer over $K$. This is the existence clause of Theorem 11.2.2 of
[han2009theoretical].

The form $a$ is a `SesqForm ℝ V`, which is bounded by its type, and $E$ is `a.energy ℓ + j`. The
proof does not use the direct method in a reflexive space. The functional $j$ has a continuous
affine minorant (`ConvexOn.exists_affine_le_of_lt`, Lemma 11.3.5 of [han2009theoretical]), so
$E$ is bounded below. Ellipticity and convexity of $j$ give $E(v) + E(w) - 2E(\tfrac12(v + w))
\ge \tfrac{c}{4}\|v - w\|^2$, so every minimizing sequence is a Cauchy sequence. Mathlib's
`exists_norm_eq_iInf_of_complete_convex` is the case where $a$ is the inner product and $j = 0$. -/
theorem existsUnique_isMinOn_energy_add {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) {j : V → ℝ} {K : Set V}
    (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ + j) K u := by
  obtain ⟨x₀, hx₀⟩ := hKne
  -- a continuous affine minorant of `j` on `K`
  obtain ⟨lin, cc, hle, -⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j x₀ - 1) hx₀
    (by linarith) hKcl hjlsc hj
  have hminor : ∀ z ∈ K, lin z + cc ≤ j z := fun z hz => by simpa using hle ⟨z, hz⟩
  set E : V → ℝ := a.energy ℓ + j with hEdef
  have hEapply : ∀ v : V, E v = 1 / 2 * a v v - ℓ v + j v := by
    intro v
    simp [hEdef, SesqForm.energy]
  -- `E` is bounded below on `K` by a quadratic in `‖v‖`
  have hbelow : ∀ v ∈ K, cc - (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c) ≤ E v := by
    intro v hv
    have h1 : c * ‖v‖ ^ 2 ≤ a v v := hcoer v
    have h2 : ℓ v ≤ ‖ℓ‖ * ‖v‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using ℓ.le_opNorm v)
    have h3 : -(‖lin‖ * ‖v‖) ≤ lin v :=
      neg_le_of_neg_le (le_trans (neg_le_abs _) (by simpa [Real.norm_eq_abs] using lin.le_opNorm v))
    have h4 := hminor v hv
    have hsq : 0 ≤ (c * ‖v‖ - (‖ℓ‖ + ‖lin‖)) ^ 2 / (2 * c) := by positivity
    have hid : (c * ‖v‖ - (‖ℓ‖ + ‖lin‖)) ^ 2 / (2 * c)
        = c / 2 * ‖v‖ ^ 2 - (‖ℓ‖ + ‖lin‖) * ‖v‖ + (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c) := by
      field_simp
      ring
    rw [hEapply v]
    nlinarith [norm_nonneg v]
  have hSne : (E '' K).Nonempty := ⟨E x₀, x₀, hx₀, rfl⟩
  have hSbdd : BddBelow (E '' K) :=
    ⟨cc - (‖ℓ‖ + ‖lin‖) ^ 2 / (2 * c), by rintro _ ⟨v, hv, rfl⟩; exact hbelow v hv⟩
  set d : ℝ := sInf (E '' K) with hddef
  have hdle : ∀ v ∈ K, d ≤ E v := fun v hv => csInf_le hSbdd ⟨v, hv, rfl⟩
  -- the parallelogram estimate: `E` is uniformly convex along `K`
  have hpara : ∀ x ∈ K, ∀ y ∈ K, c / 4 * ‖x - y‖ ^ 2 ≤ E x + E y - 2 * d := by
    intro x hx y hy
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hKcv hx hy (by norm_num) (by norm_num) (by norm_num)
    have hjm : j ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤ 1 / 2 * j x + 1 / 2 * j y := by
      simpa using hj.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
    have hpar := SesqForm.energy_parallelogram ha ℓ x y
    have hq : c * ‖x - y‖ ^ 2 ≤ a (x - y) (x - y) := hcoer (x - y)
    have hd := hdle _ hm
    simp only [hEdef, Pi.add_apply] at hd ⊢
    linarith
  -- a minimizing sequence, which the estimate makes Cauchy
  have hex : ∀ n : ℕ, ∃ v, v ∈ K ∧ E v < d + 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne (by linarith : d < d + 1 / (n + 1))
    exact ⟨v, hv, hlt⟩
  choose w hwK hwlt using hex
  have hbnd : ∀ n m N : ℕ, N ≤ n → N ≤ m →
      dist (w n) (w m) ≤ Real.sqrt (8 / c * (1 / (N + 1))) := by
    intro n m N hn hm
    have h1 := hpara _ (hwK n) _ (hwK m)
    have h2 : E (w n) < d + 1 / (n + 1) := hwlt n
    have h3 : E (w m) < d + 1 / (m + 1) := hwlt m
    have h4 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have h5 : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    have hsq : ‖w n - w m‖ ^ 2 ≤ 8 / c * (1 / (N + 1)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    rw [dist_eq_norm]
    calc ‖w n - w m‖ = Real.sqrt (‖w n - w m‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (8 / c * (1 / (N + 1))) := Real.sqrt_le_sqrt hsq
  have hb0 : Tendsto (fun N : ℕ => Real.sqrt (8 / c * (1 / (N + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 8 / c * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using Filter.Tendsto.const_mul (8 / c) tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.sqrt
  obtain ⟨u, htend⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0 _ hbnd hb0)
  have huK : u ∈ K := hKcl.mem_of_tendsto htend (Eventually.of_forall hwK)
  -- the limit attains the infimum, by continuity of the energy and semicontinuity of `j`
  have henergy : Tendsto (fun n => a.energy ℓ (w n)) atTop (𝓝 (a.energy ℓ u)) :=
    ((SesqForm.continuous_energy a ℓ).tendsto u).comp htend
  have hEtend : Tendsto (fun n => E (w n)) atTop (𝓝 d) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => hdle _ (hwK n)) (fun n => (hwlt n).le)
    have hlim : Tendsto (fun n : ℕ => d + 1 / ((n : ℝ) + 1)) atTop (𝓝 (d + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using hlim
  have hjtend : Tendsto (fun n => j (w n)) atTop (𝓝 (d - a.energy ℓ u)) := by
    have heq : (fun n => j (w n)) = fun n => E (w n) - a.energy ℓ (w n) := by
      funext n
      simp [hEdef]
    rw [heq]
    exact hEtend.sub henergy
  have hju : j u ≤ d - a.energy ℓ u := by
    by_contra hcon
    push Not at hcon
    have hy1 : d - a.energy ℓ u < (d - a.energy ℓ u + j u) / 2 := by linarith
    have hy2 : (d - a.energy ℓ u + j u) / 2 < j u := by linarith
    have hwithin : Tendsto w atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w htend (Eventually.of_forall hwK)
    have hev : ∀ᶠ n in atTop, (d - a.energy ℓ u + j u) / 2 ≤ j (w n) :=
      (hwithin.eventually (hjlsc u huK _ hy2)).mono fun n hn => hn.le
    exact absurd (ge_of_tendsto hjtend hev) (not_le.2 hy1)
  have hEu : E u ≤ d := by
    simp only [hEdef, Pi.add_apply]
    linarith
  have hminon : IsMinOn E K u := isMinOn_iff.2 fun x hx => hEu.trans (hdle x hx)
  -- uniqueness, from the same estimate
  have huniq : ∀ u₁ ∈ K, IsMinOn E K u₁ → ∀ u₂ ∈ K, IsMinOn E K u₂ → u₁ = u₂ := by
    intro u₁ h1 hm1 u₂ h2 hm2
    have hd1 : E u₁ = d :=
      le_antisymm (le_csInf hSne (by rintro _ ⟨v, hv, rfl⟩; exact isMinOn_iff.1 hm1 v hv))
        (hdle _ h1)
    have hd2 : E u₂ = d :=
      le_antisymm (le_csInf hSne (by rintro _ ⟨v, hv, rfl⟩; exact isMinOn_iff.1 hm2 v hv))
        (hdle _ h2)
    have hp := hpara _ h1 _ h2
    rw [hd1, hd2] at hp
    have hp0 : ‖u₁ - u₂‖ ^ 2 ≤ 0 := by nlinarith
    have hz : ‖u₁ - u₂‖ = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hp0 (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact ⟨u, ⟨huK, hminon⟩, fun z hz => huniq z hz.1 hz.2 u huK hminon⟩

/-- **Characterization of the constrained minimizer.** Let $V$ be a real Hilbert space, and let $a$
be a bounded symmetric bilinear form on $V$ with $a(v, v) \ge c \|v\|^2$ for all $v$, for some
$c \ge 0$. Let $\ell \in V'$, let $K \subseteq V$ be convex, and let $j : V \to \mathbb{R}$ be
convex on $K$. Then a point $u \in K$ minimizes $E(v) = \tfrac12 a(v, v) + j(v) - \ell(v)$ over
$K$ if and only if
$$\ell(v - u) \le a(u, v - u) + j(v) - j(u) \quad \text{for all } v \in K.$$
This is the characterization clause of Theorem 11.2.2 of [han2009theoretical].

The right-hand side is the variational inequality with operator `SesqForm.toOperator a` and
datum `SesqForm.rieszRep ℓ`. The proof specializes `isMinOn_add_iff_forall_le` to the quadratic
functional, whose directional derivative at $u$ is $v \mapsto a(u, v) - \ell(v)$. The case
$j = 0$ with $K$ a subspace is `SesqForm.isMinOn_energy_iff`. -/
theorem isMinOn_energy_add_iff {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hcoer : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) {j : V → ℝ} {K : Set V} (hKcv : Convex ℝ K)
    (hj : ConvexOn ℝ K j) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ + j) K u ↔
      IsVariationalInequalitySolution a.toOperator j (SesqForm.rieszRep ℓ) K u := by
  have hpos : ∀ w : V, 0 ≤ a w w := fun w => le_trans (mul_nonneg hc (sq_nonneg _)) (hcoer w)
  have hG : ∀ z ∈ K, ∀ h : V, HasLineDerivAt ℝ (a.energy ℓ) ((fun z => a z - ℓ) z h) z h :=
    fun z _ h => hasLineDerivAt_energy a ha ℓ z h
  rw [isMinOn_add_iff_forall_le (convexOn_energy a ha ℓ hpos hKcv) hj hG hu]
  constructor
  · refine fun h => ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [SesqForm.inner_rieszRep, SesqForm.inner_toOperator]
    simp only [sub_apply] at hv'
    linarith
  · rintro ⟨-, h⟩ v hv
    have hv' := h v hv
    rw [SesqForm.inner_rieszRep, SesqForm.inner_toOperator] at hv'
    simp only [sub_apply]
    linarith

end Minimization

/-! ### Unique solvability -/

section Existence

/-- For $\theta > 0$, a point $u$ solves the variational inequality with operator $A$, functional
$j$ and datum $f$ if and only if it solves the one with the identity operator, functional
$\theta j$ and datum $u - \theta(Au - f)$. -/
private theorem isVarIneq_aux_iff {A : V → V} {j : V → ℝ} {f : V} {K : Set V} {θ : ℝ}
    (hθ : 0 < θ) {u : V} :
    IsVariationalInequalitySolution (fun w => w) (fun v => θ * j v) (u - θ • (A u - f)) K u ↔
      IsVariationalInequalitySolution A j f K u := by
  have hexp : ∀ v : V, inner ℝ (u - θ • (A u - f)) (v - u)
      = inner ℝ u (v - u) - θ * (inner ℝ (A u) (v - u) - inner ℝ f (v - u)) := by
    intro v
    rw [inner_sub_left, real_inner_smul_left, inner_sub_left]
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [hexp v] at hv'
    have hmul : θ * (inner ℝ f (v - u) - inner ℝ (A u) (v - u)) ≤ θ * (j v - j u) := by linarith
    have := le_of_mul_le_mul_left hmul hθ
    linarith
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := h v hv
    rw [hexp v]
    nlinarith [hv']

variable [CompleteSpace V]

/-- The operator of the inner product form $(u, v) \mapsto \langle u, v \rangle$ is the identity. -/
private theorem coe_toOperator_innerSL :
    ⇑(SesqForm.toOperator (innerSL ℝ : SesqForm ℝ V)) = fun w : V => w := by
  funext y
  refine ext_inner_right ℝ fun v => ?_
  rw [SesqForm.inner_toOperator]
  rfl

/-- The Riesz representative of the functional $\langle y, \cdot \rangle$ is $y$. -/
private theorem rieszRep_innerSL (y : V) : SesqForm.rieszRep (innerSL ℝ y : V →L[ℝ] ℝ) = y := by
  refine ext_inner_right ℝ fun v => ?_
  rw [SesqForm.inner_rieszRep]
  rfl

/-- For $K$ nonempty, closed and convex and $j$ convex and lower semicontinuous on $K$, the
variational inequality with the identity operator has exactly one solution for every datum $y$,
namely the minimizer of $\tfrac12 \|w\|^2 + j(w) - \langle y, w \rangle$ over $K$. -/
private theorem existsUnique_id {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K)
    (y : V) : ∃! z, IsVariationalInequalitySolution (fun w => w) j y K z := by
  have hiff : ∀ z ∈ K,
      (IsMinOn (SesqForm.energy (innerSL ℝ : SesqForm ℝ V) (innerSL ℝ y) + j) K z ↔
        IsVariationalInequalitySolution (fun w : V => w) j y K z) := by
    intro z hz
    have h := isMinOn_energy_add_iff (a := (innerSL ℝ : SesqForm ℝ V))
      SesqForm.innerSL_isHermitian zero_le_one SesqForm.innerSL_isCoerciveWith
      (innerSL ℝ y) hKcv hj hz
    rwa [coe_toOperator_innerSL, rieszRep_innerSL] at h
  obtain ⟨z, ⟨hzK, hzmin⟩, huniq⟩ := existsUnique_isMinOn_energy_add
    (a := (innerSL ℝ : SesqForm ℝ V)) SesqForm.innerSL_isHermitian one_pos
    SesqForm.innerSL_isCoerciveWith (innerSL ℝ y) hKne hKcl hKcv hj hjlsc
  exact ⟨z, (hiff z hzK).mp hzmin, fun x hx => huniq x ⟨hx.1, (hiff x hx.1).mpr hx⟩⟩

/-- **Unique solvability with the hypotheses on $K$ only.** Let $V$ be a real Hilbert space and let
$K \subseteq V$ be nonempty, closed and convex. Let $A : V \to V$ be strongly monotone on $K$
with constant $c > 0$ and Lipschitz continuous on $K$ with constant $L$:
$$\langle Ax - Ay, x - y \rangle \ge c \|x - y\|^2, \qquad \|Ax - Ay\| \le L \|x - y\|
  \qquad (x, y \in K).$$
Let $j : V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. Then for every $f \in V$
the variational inequality has exactly one solution.

The map that sends $u$ to the solution of the inequality with the identity operator and datum
$u - \theta(Au - f)$ is nonexpansive in the datum, and the step $u \mapsto u - \theta(Au - f)$
contracts on $K$ with factor $\sqrt{1 - 2c\theta + L^2\theta^2}$ for $0 < \theta < 2c/L^2$
(`norm_sub_damped_le`). The Banach fixed-point theorem on the closed set $K$ gives the solution,
and `IsVariationalInequalitySolution.unique_on` gives uniqueness. Every step of this argument
stays in $K$, which is why the hypotheses are needed on $K$ only. This is the content of Remark
11.3.2 of [han2009theoretical], and it makes the locally Lipschitz case of Exercise 11.3.1 of
[han2009theoretical] a corollary, because a locally Lipschitz operator is Lipschitz on a bounded
part of $K$. -/
theorem existsUnique_isVariationalInequalitySolution_on {K : Set V} (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) {A : V → V} {c L : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneOnWith ℝ A K c)
    (hlip : ∀ x ∈ K, ∀ y ∈ K, ‖A x - A y‖ ≤ L * ‖x - y‖)
    {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) (f : V) :
    ∃! u, IsVariationalInequalitySolution A j f K u := by
  -- replace `L` by `L' = max L 1 > 0`, so that the damping parameter `θ = c / L'²` makes sense
  have hlip' : ∀ x ∈ K, ∀ y ∈ K, ‖A x - A y‖ ≤ max L 1 * ‖x - y‖ := fun x hx y hy =>
    (hlip x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hθ : 0 < c / max L 1 ^ 2 := by positivity
  have hk0 : 0 ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c
      + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2) := Real.sqrt_nonneg _
  have hk1 : Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c
      + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2) < 1 := by
    have heq : 1 - 2 * (c / max L 1 ^ 2) * c + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2
        = 1 - c ^ 2 / max L 1 ^ 2 := by field_simp; ring
    have hpos : (0 : ℝ) < c ^ 2 / max L 1 ^ 2 := by positivity
    rw [Real.sqrt_lt' one_pos, heq, one_pow]
    linarith
  -- the damping step contracts on `K`, where the two hypotheses on `A` hold
  have hdamp : ∀ x ∈ K, ∀ y ∈ K, ‖x - (c / max L 1 ^ 2) • (A x - f)
      - (y - (c / max L 1 ^ 2) • (A y - f))‖
      ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2)
        * ‖x - y‖ := by
    intro x hx y hy
    have h := norm_sub_damped_le (𝕜 := ℝ) hθ.le hmono hlip' f hx hy
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using h
  -- the auxiliary problem is uniquely solvable for every datum
  have hjθ : ConvexOn ℝ K (fun v => c / max L 1 ^ 2 * j v) := by
    simpa only [smul_eq_mul] using ConvexOn.smul hθ.le hj
  have hjθlsc : LowerSemicontinuousOn (fun v => c / max L 1 ^ 2 * j v) K :=
    (continuous_const_mul _).comp_lowerSemicontinuousOn hjlsc
      fun _ _ h => mul_le_mul_of_nonneg_left h hθ.le
  choose P hP _ using fun y : V => existsUnique_id hKne hKcl hKcv hjθ hjθlsc y
  have hmaps : Set.MapsTo (fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) K K :=
    fun u _ => (hP _).1
  have hcontr : ∀ x ∈ K, ∀ y ∈ K,
      dist ((fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) x)
        ((fun u => P (u - (c / max L 1 ^ 2) • (A u - f))) y)
      ≤ Real.sqrt (1 - 2 * (c / max L 1 ^ 2) * c + (c / max L 1 ^ 2) ^ 2 * max L 1 ^ 2)
        * dist x y := by
    intro x hx y hy
    have hne := IsVariationalInequalitySolution.norm_sub_le one_pos
      (isStronglyMonotoneWith_id (𝕜 := ℝ) (E := V)) (hP (x - (c / max L 1 ^ 2) • (A x - f)))
      (hP (y - (c / max L 1 ^ 2) • (A y - f)))
    rw [div_one] at hne
    rw [dist_eq_norm, dist_eq_norm]
    exact hne.trans (hdamp x hx y hy)
  obtain ⟨x, ⟨hxK, hxfix⟩, -⟩ :=
    exists_unique_fixedPoint_of_mapsTo hKcl hKne hmaps hk0 hk1 hcontr
  have hsol : IsVariationalInequalitySolution A j f K x := by
    refine (isVarIneq_aux_iff hθ).mp ?_
    have h := hP (x - (c / max L 1 ^ 2) • (A x - f))
    rwa [hxfix] at h
  exact ⟨x, hsol, fun y hy => IsVariationalInequalitySolution.unique_on hc hmono hy hsol⟩

/-- **Unique solvability of the elliptic variational inequality.** Let $V$ be a real Hilbert space
and let $K \subseteq V$ be nonempty, closed and convex. Let $A : V \to V$ be strongly monotone
with constant $c > 0$ and Lipschitz continuous with constant $L$, and let $j : V \to \mathbb{R}$
be convex and lower semicontinuous on $K$. Then for every $f \in V$ the variational inequality
has exactly one solution. This is Theorem 11.3.1 of [han2009theoretical].

The Lipschitz constant is `Real.toNNReal L`, so a negative $L$ stands for $0$. This is the case
of `existsUnique_isVariationalInequalitySolution_on` in which the two hypotheses on $A$ hold on
all of $V$. -/
theorem existsUnique_isVariationalInequalitySolution {K : Set V} (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) {A : V → V} {c L : ℝ} (hc : 0 < c)
    (hmono : IsStronglyMonotoneWith ℝ A c) (hlip : LipschitzWith (Real.toNNReal L) A)
    {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) (f : V) :
    ∃! u, IsVariationalInequalitySolution A j f K u :=
  existsUnique_isVariationalInequalitySolution_on (L := max L 0) hKne hKcl hKcv hc
    (hmono.isStronglyMonotoneOnWith K)
    (fun x _ y _ => by
      have h := hlip.dist_le_mul x y
      rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal'] at h)
    hj hjlsc f

/-- **Stampacchia's theorem.** Let $V$ be a real Hilbert space, let $K \subseteq V$ be nonempty,
closed and convex, and let $A : V \to V$ be strongly monotone with constant $c > 0$ and
Lipschitz continuous with constant $L$. Then for every $f \in V$ the variational inequality of
the first kind
$$u \in K, \qquad \langle f, v - u \rangle \le \langle Au, v - u \rangle \quad \text{for all } v
  \in K$$
has exactly one solution. This is Theorem 11.3.6 of [han2009theoretical].

The solution depends Lipschitz continuously on $f$ by
`IsVariationalInequalitySolution.norm_sub_le`. The theorem generalizes the Lax–Milgram lemma
`SesqForm.laxMilgram`, which is the case where $K = V$ and $A$ is linear. The declaration keeps
the classical name of the theorem. -/
theorem stampacchia {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    {A : V → V} {c L : ℝ} (hc : 0 < c) (hmono : IsStronglyMonotoneWith ℝ A c)
    (hlip : LipschitzWith (Real.toNNReal L) A) (f : V) :
    ∃! u, IsVariationalInequalitySolution A 0 f K u :=
  existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc hmono hlip
    (convexOn_const 0 hKcv) lowerSemicontinuousOn_const f

/-- **Unique solvability for a bilinear form.** Let $V$ be a real Hilbert space, and let $a$ be a
bounded bilinear form on $V$, not necessarily symmetric, that is elliptic with constant $c > 0$.
Let $\ell \in V'$, let $K \subseteq V$ be nonempty, closed and convex, and let
$j : V \to \mathbb{R}$ be convex and lower semicontinuous on $K$. Then there is exactly one $u$
with
$$u \in K, \qquad \ell(v - u) \le a(u, v - u) + j(v) - j(u) \quad \text{for all } v \in K.$$
This is Theorem 11.3.9 of [han2009theoretical].

The problem is the variational inequality with operator `SesqForm.toOperator a` and datum
`SesqForm.rieszRep ℓ`. The case $j = 0$ is the inequality of the first kind and the case $K = V$
the inequality of the second kind. The solution depends Lipschitz continuously on $\ell$ by
`IsVariationalInequalitySolution.norm_sub_le`. The proof applies
`existsUnique_isVariationalInequalitySolution` to the operator of $a$, whose strong monotonicity
is `SesqForm.isCoerciveWith_iff_toOperator` and whose Lipschitz constant is
`SesqForm.norm_toOperator`. -/
theorem existsUnique_isVariationalInequalitySolution_of_isCoercive {a : SesqForm ℝ V} {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) {j : V → ℝ} (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K)
    (ℓ : V →L[ℝ] ℝ) :
    ∃! u, IsVariationalInequalitySolution a.toOperator j (SesqForm.rieszRep ℓ) K u := by
  have hmono : IsStronglyMonotoneWith ℝ (SesqForm.toOperator a : V → V) c :=
    LinearMap.IsCoerciveWith.isStronglyMonotoneWith
      ((SesqForm.isCoerciveWith_iff_toOperator a c).mp hcoer)
  have hlip : LipschitzWith (Real.toNNReal ‖a‖) (SesqForm.toOperator a : V → V) := by
    rw [← SesqForm.norm_toOperator a, ← coe_nnnorm, Real.toNNReal_coe]
    exact (SesqForm.toOperator a).lipschitzWith
  exact existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc hmono hlip hj hjlsc _

end Existence

/-! ### Minty's lemma and the special forms -/

/-- **Minty's lemma.** Let $V$ be a real inner product space, let $K \subseteq V$ be convex, let
$j : V \to \mathbb{R}$ be convex on $K$, and let $A : V \to V$ be monotone, that is,
$\langle Ax - Ay, x - y \rangle \ge 0$ for all $x, y$. Let $u \in K$, and assume that for every
$v \in K$ the map $t \mapsto A(u + t(v - u))$ is continuous from the right at $t = 0$. Then $u$
solves the variational inequality if and only if
$$\langle f, v - u \rangle \le \langle Av, v - u \rangle + j(v) - j(u) \quad \text{for all } v
  \in K,$$
that is, the inequality with $A$ evaluated at the test point $v$ instead of at $u$. This is
Lemma 11.3.8 of [han2009theoretical].

Monotonicity is `IsStronglyMonotoneWith ℝ A 0`, and no Lipschitz continuity of $A$ is used. One
direction follows from monotonicity. For the other, substitute $u + t(v - u)$, use the convexity
of $j$ and let $t$ tend to $0$. The Minty form is useful because it is stable under weak limits. -/
theorem IsVariationalInequalitySolution.iff_minty {A : V → V} {j : V → ℝ} {f : V} {K : Set V}
    (hKcv : Convex ℝ K) (hj : ConvexOn ℝ K j) (hmono : IsStronglyMonotoneWith ℝ A 0) {u : V}
    (hu : u ∈ K)
    (hA : ∀ v ∈ K, ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0) :
    IsVariationalInequalitySolution A j f K u ↔
      ∀ v ∈ K, inner ℝ f (v - u) ≤ inner ℝ (A v) (v - u) + j v - j u := by
  constructor
  · rintro ⟨-, h⟩ v hv
    have h1 := h v hv
    have h2 : 0 ≤ inner ℝ (A v - A u) (v - u) := by simpa using hmono v u
    rw [inner_sub_left] at h2
    linarith
  · intro h
    refine ⟨hu, fun v hv => ?_⟩
    -- the test inequality along the segment `[u, v]`, after dividing by `t`
    have hseg : ∀ t ∈ Ioo (0 : ℝ) 1,
        inner ℝ f (v - u) ≤ inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u := by
      intro t ht
      have hmem : u + t • (v - u) ∈ K := Convex.add_smul_sub_mem hKcv hu hv ⟨ht.1.le, ht.2.le⟩
      have h1 := h _ hmem
      rw [show u + t • (v - u) - u = t • (v - u) by abel, real_inner_smul_right,
        real_inner_smul_right] at h1
      have hjc : j (u + t • (v - u)) ≤ (1 - t) * j u + t * j v := by
        have hcv := hj.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
        rw [show (1 - t) • u + t • v = u + t • (v - u) by module] at hcv
        simpa using hcv
      have ht0 := ht.1
      nlinarith
    have hcont : ContinuousWithinAt
        (fun t : ℝ => inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u) (Ioi 0) 0 := by
      have hin : Continuous fun x : V => inner ℝ x (v - u) :=
        continuous_inner.comp (continuous_id.prodMk continuous_const)
      exact ((hin.continuousAt.comp_continuousWithinAt (hA v hv)).add
        continuousWithinAt_const).sub continuousWithinAt_const
    have hlim : Tendsto (fun t : ℝ => inner ℝ (A (u + t • (v - u))) (v - u) + j v - j u)
        (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (A u) (v - u) + j v - j u)) := by
      have hc := hcont
      simp only [ContinuousWithinAt, zero_smul, add_zero] at hc
      exact hc
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hseg t ht

/-- **The variational inequality as an energy projection.** Let $V$ be a real inner product space,
let $A : V \to V$ be linear, symmetric and coercive, let $K \subseteq V$ be convex, and let
$f, w \in V$ with $Aw = f$. If $u$ solves the variational inequality with $j = 0$, then $u$ is
the best approximation to $w$ from $K$ in the energy norm
$\|v\|_A = \langle Av, v \rangle^{1/2}$:
$$u \in K, \qquad \|w - u\|_A \le \|w - v\|_A \quad \text{for all } v \in K.$$
So the inequality is solved by solving the equation $Aw = f$ and projecting onto $K$ in the
energy inner product. This is the remark after Example 11.3.11 of [han2009theoretical].

The energy norm is the norm of `WithEnergy A hA`, and the conclusion is `IsBestApprox` for the
images of $K$, $w$ and $u$ under `WithEnergy.equiv A hA`. -/
theorem IsVariationalInequalitySolution.isBestApprox_energy {A : V →ₗ[ℝ] V}
    (hA : A.IsSymmetricCoercive) {K : Set V} (hKcv : Convex ℝ K) {f w u : V} (hw : A w = f)
    (hsol : IsVariationalInequalitySolution A 0 f K u) :
    IsBestApprox (WithEnergy.equiv A hA '' K) (WithEnergy.equiv A hA w)
      (WithEnergy.equiv A hA u) := by
  have hK' : Convex ℝ (WithEnergy.equiv A hA '' K) := by
    simpa using Convex.linear_image hKcv (WithEnergy.equiv A hA).toLinearMap
  have hmem : WithEnergy.equiv A hA u ∈ WithEnergy.equiv A hA '' K := ⟨u, hsol.1, rfl⟩
  refine (isBestApprox_iff_inner_le_zero hK' hmem).2 ?_
  rintro _ ⟨v, hv, rfl⟩
  have hvi := hsol.2 v hv
  simp only [Pi.zero_apply, sub_zero, add_zero] at hvi
  rw [← map_sub, ← map_sub, WithEnergy.inner_equiv, energyInner, map_sub, hw, inner_sub_left]
  linarith

/-- **The cone form.** Let $V$ be a real inner product space, let $A : V \to V$ and $f \in V$, and
let $K \subseteq V$ be a convex cone: $K$ is convex and $tx \in K$ for all $t \ge 0$ and
$x \in K$. Then $u \in K$ solves the variational inequality with $j = 0$ if and only if
$$\langle f, v \rangle \le \langle Au, v \rangle \text{ for all } v \in K
  \qquad \text{and} \qquad \langle Au, u \rangle = \langle f, u \rangle.$$
This is Exercise 11.3.3 of [han2009theoretical].

Testing at $2u$ and at $0$ gives the equality, and testing at $u + v$ gives the inequality.
Conversely, the inequality at $v$ minus the equality is the variational inequality. -/
theorem IsVariationalInequalitySolution.iff_of_isCone {A : V → V} {f : V} {K : Set V}
    (hKcv : Convex ℝ K) (hKcone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K) {u : V} (hu : u ∈ K) :
    IsVariationalInequalitySolution A 0 f K u ↔
      (∀ v ∈ K, inner ℝ f v ≤ inner ℝ (A u) v) ∧ inner ℝ (A u) u = inner ℝ f u := by
  have hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    have hm : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hKcv hx hy (by norm_num) (by norm_num) (by norm_num)
    have h2 := hKcone 2 (by norm_num) _ hm
    rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
      one_smul] at h2
  constructor
  · rintro ⟨-, h⟩
    have h2u := h ((2 : ℝ) • u) (hKcone 2 (by norm_num) _ hu)
    have h0 := h 0 (by simpa using hKcone 0 le_rfl _ hu)
    rw [show (2 : ℝ) • u - u = u by module] at h2u
    rw [zero_sub, inner_neg_right, inner_neg_right] at h0
    simp only [Pi.zero_apply, sub_zero, add_zero] at h2u h0
    have heq : inner ℝ (A u) u = inner ℝ f u := le_antisymm (by linarith) h2u
    refine ⟨fun v hv => ?_, heq⟩
    have hv' := h (u + v) (hadd u hu v hv)
    rw [show u + v - u = v by abel] at hv'
    simpa using hv'
  · rintro ⟨hle, heq⟩
    refine ⟨hu, fun v hv => ?_⟩
    have hv' := hle v hv
    rw [inner_sub_right, inner_sub_right]
    simp only [Pi.zero_apply, sub_zero, add_zero]
    linarith

/-- **The positively homogeneous form.** Let $V$ be a real inner product space, let $A : V \to V$
and $f \in V$, and let $j : V \to \mathbb{R}$ be convex and positively homogeneous:
$j(tv) = t\,j(v)$ for all $t > 0$ and $v \in V$. Then $u$ solves the variational inequality of
the second kind, with $K = V$, if and only if
$$\langle f, v \rangle \le \langle Au, v \rangle + j(v) \text{ for all } v \in V
  \qquad \text{and} \qquad \langle Au, u \rangle + j(u) = \langle f, u \rangle.$$
This is Exercise 11.3.10 of [han2009theoretical].

Convexity and positive homogeneity make $j$ subadditive, and this turns the test at $u + v$ into
the inequality at $v$. The equivalence is the basis of the Lagrange multiplier form of a
friction problem. -/
theorem IsVariationalInequalitySolution.iff_of_isPositiveHomogeneous {A : V → V} {j : V → ℝ}
    {f : V} (hj : ConvexOn ℝ univ j) (hhom : ∀ t : ℝ, 0 < t → ∀ v, j (t • v) = t * j v) {u : V} :
    IsVariationalInequalitySolution A j f univ u ↔
      (∀ v, inner ℝ f v ≤ inner ℝ (A u) v + j v) ∧ inner ℝ (A u) u + j u = inner ℝ f u := by
  have hj0 : j 0 = 0 := by
    have h := hhom 2 (by norm_num) 0
    rw [smul_zero] at h
    linarith
  have hsub : ∀ x y : V, j (x + y) ≤ j x + j y := by
    intro x y
    have hm := hj.2 (mem_univ x) (mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = (1 / 2 : ℝ) • (x + y) by module,
      hhom _ (by norm_num) _] at hm
    simp only [smul_eq_mul] at hm
    linarith
  constructor
  · rintro ⟨-, h⟩
    have h2u := h ((2 : ℝ) • u) (mem_univ _)
    have h0 := h 0 (mem_univ _)
    rw [show (2 : ℝ) • u - u = u by module, hhom 2 (by norm_num) u] at h2u
    rw [zero_sub, inner_neg_right, inner_neg_right, hj0] at h0
    have heq : inner ℝ (A u) u + j u = inner ℝ f u := le_antisymm (by linarith) (by linarith)
    refine ⟨fun v => ?_, heq⟩
    have hv' := h (u + v) (mem_univ _)
    rw [show u + v - u = v by abel] at hv'
    have hs := hsub u v
    linarith
  · rintro ⟨hle, heq⟩
    refine ⟨mem_univ _, fun v _ => ?_⟩
    have hv' := hle v
    rw [inner_sub_right, inner_sub_right]
    linarith
