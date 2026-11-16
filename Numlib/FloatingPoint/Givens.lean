/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Data.Matrix.Mul
import Numlib.FloatingPoint.Householder

/-!
# Rounding errors of Givens rotations

This module analyzes the rounding errors of Givens rotations over $\mathbb{R}$, in the rounding
model of `Numlib.FloatingPoint.Model`: the computation of the cosine–sine pair $(c, s)$ from
$(a, b)$, and the application of a rotation to a vector, to two rows of a matrix or to two columns
of a matrix. It follows [higham2002accuracy], §19.6, Lemmas 19.7 and 19.8, and [golub2013matrix],
§5.1.8–§5.1.12. A value $\hat x$ is a relative perturbation of order $k$ of $x$ if
$\hat x = x (1 + \theta)$ with $|\theta| \le \gamma_k = ku / (1 - ku)$, where $u$ is the unit
roundoff. The computed pair is a relative perturbation of an exact rotation that annihilates $b$. A
computed update with such data differs from the exact rotation by at most
$\sqrt{2}\, \gamma_{n+2} \|x\|_2$ in the Euclidean norm, where $n$ is the order of the perturbation
of the pair; the matrix updates satisfy the same bound columnwise, rowwise and in the Frobenius
norm. The computed rotation matrix is within $\gamma_n$ of the exact one in the spectral norm, so it
is orthogonal to working precision.

The numerical sources ([golub2013matrix] (5.1.7), [higham2002accuracy] §19.6,
[quarteroni2000numerical] (5.43)) write the rotation as $G(i, k, \theta)$, with
$g_{ii} = g_{kk} = c$, $g_{ik} = s$ and $g_{ki} = -s$, and apply $G(i, k, \theta)^T$:
$y_i = c x_i - s x_k$ and $y_k = s x_i + c x_k$. Below, $G(j, k)$ denotes this matrix for given $c$
and $s$.

## Main definitions

* `FloatingPoint.RoundsGivensPair`: the computed pair $(\hat c, \hat s)$ of the $\tau$-formula of
  [golub2013matrix], Algorithm 5.1.3.
* `FloatingPoint.RoundsGivensPairDirect`: the computed pair of the direct formula
  $c = a / \sqrt{a^2 + b^2}$, $s = -b / \sqrt{a^2 + b^2}$ of [golub2013matrix] (5.1.8).
* `FloatingPoint.RoundsGivensApply`: the computed rotation $y_j = \mathrm{fl}(\mathrm{fl}(c x_j) -
  \mathrm{fl}(s x_k))$, $y_k = \mathrm{fl}(\mathrm{fl}(s x_j) + \mathrm{fl}(c x_k))$ of two entries
  of a vector.
* `FloatingPoint.RoundsGivensRowUpdate` and `FloatingPoint.RoundsGivensColUpdate`: the computed
  updates $G^T A$ of two rows and $A G$ of two columns of a matrix.

## Main results

* `FloatingPoint.RoundsGivensPair.exists_isRelPert`: the computed pair of the $\tau$-formula is a
  relative perturbation of order $13$ of an exact rotation with $sa + cb = 0$.
* `FloatingPoint.RoundsGivensPairDirect.isRelPert`: the computed pair of the direct formula is a
  relative perturbation of order $7$ of the exact pair.
* `FloatingPoint.abs_sub_le_of_roundsGivensApply`: the componentwise form of Lemma 19.8 of
  [higham2002accuracy].
* `FloatingPoint.norm_sub_le_of_roundsGivensApply`: $\|y - G(j, k)^T x\|_2 \le \sqrt{2}\,
  \gamma_{n+2} \|x\|_2$.
* `FloatingPoint.RoundsGivensRowUpdate.frobenius_norm_sub_le` and
  `FloatingPoint.RoundsGivensColUpdate.frobenius_norm_sub_le`: the same bound for the matrix updates
  in the Frobenius norm.
* `FloatingPoint.l2_opNorm_planeRotation_sub_le`: the computed rotation matrix is within $\gamma_n$
  of the exact one in the spectral norm.
* `FloatingPoint.l2_opNorm_transpose_mul_self_sub_one_le`: if $\|\hat Q - Q\|_2 \le \varepsilon$ for
  an orthogonal $Q$, then $\|\hat Q^T \hat Q - I\|_2 \le 2 \varepsilon + \varepsilon^2$.

## Implementation notes

* `Matrix.planeRotation j k c s` has the rows $(c, -s)$ and $(s, c)$ in the columns $j, k$ (the
  Jacobi convention). Therefore the exact rotation $G(j, k)$ of the numerical sources is
  `Matrix.planeRotation j k c (-s)`. The relations keep the signs of the numerical convention inside
  the rounded expressions, for example `Rounds (-a / b) τ` and `Rounds (p - q) y`. The rounding
  model does not assume that rounding commutes with negation, so a relation in the Jacobi convention
  would not describe a run of the algorithms of the sources.
* The rounding relation is not a function. Every statement holds for all admissible roundings at
  once.
* The constants come from the calculus of relative perturbations of `Numlib.FloatingPoint.Model`.
  They are larger than the constants $\gamma_4$ and $\gamma_6$ of [higham2002accuracy], but they are
  proved without approximation.
* Sequences of rotations are covered by the accumulation lemmas of
  `Numlib.FloatingPoint.Householder` (Lemma 19.3 of [higham2002accuracy]),
  `FloatingPoint.exists_eq_prodRev_mul_add` and
  `FloatingPoint.exists_eq_prodRev_mul_add_mul_prodFwd_rect`. The loop of a Givens QR factorization
  is an algorithm of the sources, so it is not stated in this module.
-/

open Matrix WithLp

namespace FloatingPoint

/-! ### The computed cosine–sine pair -/

/-- The computed cosine–sine pair of the $\tau$-formula of [golub2013matrix], Algorithm 5.1.3. For
$a, b \in \mathbb{R}$, a pair $(\hat c, \hat s)$ is a computed pair if one of three cases holds:

* $b = 0$, $\hat c = 1$ and $\hat s = 0$;
* $|a| < |b|$, $\hat\tau = \mathrm{fl}(-a / b)$, $\hat s = \mathrm{fl}\bigl(1 /
  \mathrm{fl}(\sqrt{\mathrm{fl}(1 + \mathrm{fl}(\hat\tau^2))})\bigr)$ and
  $\hat c = \mathrm{fl}(\hat s \hat\tau)$;
* $b \neq 0$, $|b| \le |a|$, $\hat\tau = \mathrm{fl}(-b / a)$, $\hat c = \mathrm{fl}\bigl(1 /
  \mathrm{fl}(\sqrt{\mathrm{fl}(1 + \mathrm{fl}(\hat\tau^2))})\bigr)$ and
  $\hat s = \mathrm{fl}(\hat c \hat\tau)$.

The comparisons act on the exact inputs $a$ and $b$. -/
def RoundsGivensPair (m : RoundingModel ℝ) (a b chat shat : ℝ) : Prop :=
  (b = 0 ∧ chat = 1 ∧ shat = 0) ∨
  (|a| < |b| ∧ ∃ τ t₁ t₂ r : ℝ, m.Rounds (-a / b) τ ∧ m.Rounds (τ * τ) t₁ ∧
      m.Rounds (1 + t₁) t₂ ∧ m.Rounds (√t₂) r ∧ m.Rounds (1 / r) shat ∧ m.Rounds (shat * τ) chat) ∨
  (b ≠ 0 ∧ |b| ≤ |a| ∧ ∃ τ t₁ t₂ r : ℝ, m.Rounds (-b / a) τ ∧ m.Rounds (τ * τ) t₁ ∧
      m.Rounds (1 + t₁) t₂ ∧ m.Rounds (√t₂) r ∧ m.Rounds (1 / r) chat ∧ m.Rounds (chat * τ) shat)

/-- The common part of the two branches of the $\tau$-formula: if $\hat\tau$ is a relative
perturbation of order $1$ of $\tau$ and $13u < 1$, then $\mathrm{fl}(1 /
\mathrm{fl}(\sqrt{\mathrm{fl}(1 + \mathrm{fl}(\hat\tau^2))}))$ is a relative perturbation of
order $13$ of $1 / \sqrt{1 + \tau^2}$, and its rounded product with $\hat\tau$ is one of order
$13$ of $\tau / \sqrt{1 + \tau^2}$. -/
private theorem isRelPert_givens_branch {m : RoundingModel ℝ} (hu : ((13 : ℕ) : ℝ) * m.u < 1)
    {τ τh t₁ t₂ r x y : ℝ} (hτ : IsRelPert m.u 1 τ τh) (h₁ : m.Rounds (τh * τh) t₁)
    (h₂ : m.Rounds (1 + t₁) t₂) (hr : m.Rounds (√t₂) r) (hx : m.Rounds (1 / r) x)
    (hy : m.Rounds (x * τh) y) :
    IsRelPert m.u 13 (1 / √(1 + τ * τ)) x ∧ IsRelPert m.u 13 (1 / √(1 + τ * τ) * τ) y := by
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ 13 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hu
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have ht₁ : IsRelPert m.u 3 (τ * τ) t₁ :=
    (hτ.mul hu0 (k := 1) (j := 1) (hlt 2 (by omega)) hτ).rounds (hlt 3 (by omega)) h₁
  have h1 : IsRelPert m.u 3 (1 : ℝ) 1 :=
    (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) (hlt 3 (by omega))
  have ht₂ : IsRelPert m.u 4 (1 + τ * τ) t₂ :=
    (IsRelPert.add_of_nonneg zero_le_one (mul_self_nonneg τ) h1 ht₁).rounds
      (hlt 4 (by omega)) h₂
  have hg : gamma m.u 4 ≤ 1 := (gamma_lt_one (by
    have := hlt 8 (by omega)
    push_cast at this ⊢
    linarith)).le
  have hsq : IsRelPert m.u 4 (√(1 + τ * τ)) (√t₂) :=
    ht₂.sqrt hg (add_nonneg zero_le_one (mul_self_nonneg τ))
  have hr' : IsRelPert m.u 5 (√(1 + τ * τ)) r := hsq.rounds (hlt 5 (by omega)) hr
  have hx' : IsRelPert m.u 11 (1 / √(1 + τ * τ)) x :=
    ((IsRelPert.refl m.u (1 : ℝ)).div hu0 (k := 0) (j := 5) (hlt 10 (by omega)) hr').rounds
      (hlt 11 (by omega)) hx
  have hy' : IsRelPert m.u 13 (1 / √(1 + τ * τ) * τ) y :=
    (hx'.mul hu0 (k := 11) (j := 1) (hlt 12 (by omega)) hτ).rounds (hlt 13 le_rfl) hy
  exact ⟨hx'.mono hu0 (by omega) hu, hy'⟩

/-- $(1 / \sqrt{1 + \tau^2})^2 (1 + \tau^2) = 1$. -/
private theorem one_div_sqrt_one_add_mul_self_sq (τ : ℝ) :
    (1 / √(1 + τ * τ)) ^ 2 * (1 + τ * τ) = 1 := by
  have h : 0 < 1 + τ * τ := add_pos_of_pos_of_nonneg one_pos (mul_self_nonneg τ)
  rw [div_pow, Real.sq_sqrt h.le]
  field_simp

/-- Let $13u < 1$, and let $(\hat c, \hat s)$ be a computed pair of the $\tau$-formula for $(a, b)$.
Then there are $c, s \in \mathbb{R}$ with
$$c^2 + s^2 = 1, \qquad sa + cb = 0,$$
such that $\hat c$ and $\hat s$ are relative perturbations of order $13$ of $c$ and $s$. The
condition $sa + cb = 0$ says that the second entry of $\begin{bmatrix} c & s \\ -s & c
\end{bmatrix}^T \begin{bmatrix} a \\ b \end{bmatrix}$ is $0$. This is Lemma 19.7 of
[higham2002accuracy] for the $\tau$-formula of [golub2013matrix], Algorithm 5.1.3.

The exact pair $(c, s)$ is the exact output of the same branch of the formula. -/
theorem RoundsGivensPair.exists_isRelPert {m : RoundingModel ℝ}
    (hu : ((13 : ℕ) : ℝ) * m.u < 1) {a b chat shat : ℝ} (h : RoundsGivensPair m a b chat shat) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ s * a + c * b = 0 ∧
      IsRelPert m.u 13 c chat ∧ IsRelPert m.u 13 s shat := by
  have hu0 := m.u_nonneg
  have hu1 : m.u < 1 := by
    have := (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega : 1 ≤ 13)) hu0).trans_lt hu
    simpa using this
  rcases h with ⟨hb, hc, hs⟩ | ⟨hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hs, hc⟩ |
      ⟨hb, hab, τ, t₁, t₂, r, hτ, h₁, h₂, hr, hc, hs⟩
  · refine ⟨1, 0, by norm_num, by rw [hb]; ring, ?_, ?_⟩
    · rw [hc]; exact (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) hu
    · rw [hs]; exact (IsRelPert.refl _ _).mono hu0 (Nat.zero_le _) hu
  · have hb : b ≠ 0 := fun h => by rw [h, abs_zero] at hab; exact (abs_nonneg a).not_gt hab
    obtain ⟨hs', hc'⟩ := isRelPert_givens_branch hu (hτ.isRelPert hu1) h₁ h₂ hr hs hc
    refine ⟨1 / √(1 + -a / b * (-a / b)) * (-a / b), 1 / √(1 + -a / b * (-a / b)), ?_, ?_,
      hc', hs'⟩
    · linear_combination one_div_sqrt_one_add_mul_self_sq (-a / b)
    · have : -a / b * b = -a := div_mul_cancel₀ _ hb
      linear_combination (1 / √(1 + -a / b * (-a / b))) * this
  · have ha : a ≠ 0 := fun h => by
      rw [h, abs_zero] at hab
      exact hb (abs_nonpos_iff.1 hab)
    obtain ⟨hc', hs'⟩ := isRelPert_givens_branch hu (hτ.isRelPert hu1) h₁ h₂ hr hc hs
    refine ⟨1 / √(1 + -b / a * (-b / a)), 1 / √(1 + -b / a * (-b / a)) * (-b / a), ?_, ?_,
      hc', hs'⟩
    · linear_combination one_div_sqrt_one_add_mul_self_sq (-b / a)
    · have : -b / a * a = -b := div_mul_cancel₀ _ ha
      linear_combination (1 / √(1 + -b / a * (-b / a))) * this

/-- The computed pair of the direct formula (5.1.8) of [golub2013matrix], $c = a / \sqrt{a^2 + b^2}$
and $s = -b / \sqrt{a^2 + b^2}$. For $a, b \in \mathbb{R}$, a pair $(\hat c, \hat s)$ is a
computed pair if
$$\hat r = \mathrm{fl}\bigl(\sqrt{\mathrm{fl}(\mathrm{fl}(a^2) + \mathrm{fl}(b^2))}\bigr),
  \qquad \hat c = \mathrm{fl}(a / \hat r), \qquad \hat s = \mathrm{fl}(-b / \hat r).$$
[quarteroni2000numerical] (5.51) and [higham2002accuracy], §19.6, use the same formula. -/
def RoundsGivensPairDirect (m : RoundingModel ℝ) (a b chat shat : ℝ) : Prop :=
  ∃ p q t r : ℝ, m.Rounds (a * a) p ∧ m.Rounds (b * b) q ∧ m.Rounds (p + q) t ∧
    m.Rounds (√t) r ∧ m.Rounds (a / r) chat ∧ m.Rounds (-b / r) shat

/-- Let $7u < 1$. If $(\hat c, \hat s)$ is a computed pair of the direct formula for $(a, b)$, then
$\hat c$ and $\hat s$ are relative perturbations of order $7$ of
$$\frac{a}{\sqrt{a^2 + b^2}} \quad \text{and} \quad \frac{-b}{\sqrt{a^2 + b^2}}.$$
The hypothesis $(a, b) \neq 0$ is not needed.

At $(a, b) = (0, 0)$, both exact values are $0$ by the Lean convention $x / 0 = 0$. The order
$7$ counts the roundings: the rounded square root of the rounded sum of squares has order $3$,
the quotients have order $6$, and their roundings order $7$. -/
theorem RoundsGivensPairDirect.isRelPert {m : RoundingModel ℝ} (hu : ((7 : ℕ) : ℝ) * m.u < 1)
    {a b chat shat : ℝ} (h : RoundsGivensPairDirect m a b chat shat) :
    IsRelPert m.u 7 (a / √(a ^ 2 + b ^ 2)) chat ∧ IsRelPert m.u 7 (-b / √(a ^ 2 + b ^ 2)) shat := by
  obtain ⟨p, q, t, r, hp, hq, ht, hr, hc, hs⟩ := h
  have hu0 := m.u_nonneg
  have hlt : ∀ j : ℕ, j ≤ 7 → ((j : ℕ) : ℝ) * m.u < 1 := fun j hj =>
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hj) hu0).trans_lt hu
  have hu1 : m.u < 1 := by simpa using hlt 1 (by omega)
  have ht' : IsRelPert m.u 2 (a * a + b * b) t :=
    (IsRelPert.add_of_nonneg (mul_self_nonneg a) (mul_self_nonneg b) (hp.isRelPert hu1)
      (hq.isRelPert hu1)).rounds (hlt 2 (by omega)) ht
  have hg : gamma m.u 2 ≤ 1 := (gamma_lt_one (by
    have := hlt 4 (by omega)
    push_cast at this ⊢
    linarith)).le
  have hsq := ht'.sqrt hg (add_nonneg (mul_self_nonneg a) (mul_self_nonneg b))
  have hr' : IsRelPert m.u 3 (√(a ^ 2 + b ^ 2)) r := by
    rw [sq, sq]
    exact hsq.rounds (hlt 3 (by omega)) hr
  have hdiv : ∀ {x z : ℝ}, m.Rounds (x / r) z → IsRelPert m.u 7 (x / √(a ^ 2 + b ^ 2)) z :=
    fun hz => ((IsRelPert.refl _ _).div hu0 (k := 0) (j := 3) (hlt 6 (by omega)) hr').rounds
      (hlt 7 le_rfl) hz
  exact ⟨hdiv hc, hdiv hs⟩

/-! ### Applying a computed rotation -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One computed rotation of the coordinates $j, k$ of a vector ([golub2013matrix] §5.1.9,
[higham2002accuracy] §19.6). For $c, s \in \mathbb{R}$ and $x \in \mathbb{R}^\iota$, a vector
$y$ is a computed rotation of $x$ if
$$y_j = \mathrm{fl}\bigl(\mathrm{fl}(c x_j) - \mathrm{fl}(s x_k)\bigr), \qquad y_k =
  \mathrm{fl}\bigl(\mathrm{fl}(s x_j) + \mathrm{fl}(c x_k)\bigr),$$
and $y_i = x_i$ for every $i \neq j, k$.

The exact counterpart is $G(j, k)^T x$, that is `(Matrix.planeRotation j k c (-s))ᵀ *ᵥ x`. -/
def RoundsGivensApply (m : RoundingModel ℝ) (c s : ℝ) (j k : ι) (x y : ι → ℝ) : Prop :=
  (∃ p q : ℝ, m.Rounds (c * x j) p ∧ m.Rounds (s * x k) q ∧ m.Rounds (p - q) (y j)) ∧
  (∃ p q : ℝ, m.Rounds (s * x j) p ∧ m.Rounds (c * x k) q ∧ m.Rounds (p + q) (y k)) ∧
  ∀ i, i ≠ j → i ≠ k → y i = x i

/-- If $(n + 2) u < 1$ and $p$ and $q$ are relative perturbations of order $n + 1$ of $X$ and $Y$,
then $|\mathrm{fl}(p + q) - (X + Y)| \le \gamma_{n+2} (|X| + |Y|)$. -/
private theorem abs_rounds_add_sub_le {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {X Y p q y : ℝ} (hp : IsRelPert m.u (n + 1) X p)
    (hq : IsRelPert m.u (n + 1) Y q) (hy : m.Rounds (p + q) y) :
    |y - (X + Y)| ≤ gamma m.u (n + 2) * (|X| + |Y|) := by
  have hu0 := m.u_nonneg
  have hn1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hn
  have hu1 : m.u < 1 := by
    have := (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega : 1 ≤ n + 2)) hu0).trans_lt hn
    simpa using this
  have hγ : 0 ≤ gamma m.u (n + 1) := gamma_nonneg hu0 hn1
  obtain ⟨θ₁, hθ₁, rfl⟩ := hp
  obtain ⟨θ₂, hθ₂, rfl⟩ := hq
  obtain ⟨δ, hδ, rfl⟩ := hy.exists_delta
  have hstep : gamma m.u (n + 1) * (1 + m.u) + m.u ≤ gamma m.u (n + 2) :=
    gamma_mul_one_add_add_le hu0 hu1 hn
  rw [show (X * (1 + θ₁) + Y * (1 + θ₂)) * (1 + δ) - (X + Y) =
      X * θ₁ + Y * θ₂ + (X * (1 + θ₁) + Y * (1 + θ₂)) * δ by ring]
  have h1 : |X * θ₁ + Y * θ₂| ≤ gamma m.u (n + 1) * (|X| + |Y|) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg X, abs_nonneg Y]
  have h2 : |X * (1 + θ₁) + Y * (1 + θ₂)| ≤ (1 + gamma m.u (n + 1)) * (|X| + |Y|) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 : |1 + θ₁| ≤ 1 + gamma m.u (n + 1) :=
      (abs_add_le 1 θ₁).trans (by rw [abs_one]; linarith)
    have e2 : |1 + θ₂| ≤ 1 + gamma m.u (n + 1) :=
      (abs_add_le 1 θ₂).trans (by rw [abs_one]; linarith)
    nlinarith [abs_nonneg X, abs_nonneg Y, mul_le_mul_of_nonneg_left e1 (abs_nonneg X),
      mul_le_mul_of_nonneg_left e2 (abs_nonneg Y)]
  have h3 : |(X * (1 + θ₁) + Y * (1 + θ₂)) * δ| ≤ (1 + gamma m.u (n + 1)) * (|X| + |Y|) * m.u := by
    rw [abs_mul]
    exact mul_le_mul h2 hδ (abs_nonneg _) (by positivity)
  have hXY : 0 ≤ |X| + |Y| := by positivity
  calc |X * θ₁ + Y * θ₂ + (X * (1 + θ₁) + Y * (1 + θ₂)) * δ|
      ≤ gamma m.u (n + 1) * (|X| + |Y|) + (1 + gamma m.u (n + 1)) * (|X| + |Y|) * m.u :=
        (abs_add_le _ _).trans (add_le_add h1 h3)
    _ = (gamma m.u (n + 1) * (1 + m.u) + m.u) * (|X| + |Y|) := by ring
    _ ≤ gamma m.u (n + 2) * (|X| + |Y|) := mul_le_mul_of_nonneg_right hstep hXY

omit [Fintype ι] [DecidableEq ι] in
/-- Let $(n + 2) u < 1$, and let $\hat c$ and $\hat s$ be relative perturbations of order $n$ of $c$
and $s$. If $y$ is a computed rotation of the coordinates $j, k$ of $x$ with the data
$(\hat c, \hat s)$, then
$$|y_j - (c x_j - s x_k)| \le \gamma_{n+2} (|c| |x_j| + |s| |x_k|), \qquad |y_k - (s x_j + c
  x_k)| \le \gamma_{n+2} (|s| |x_j| + |c| |x_k|),$$
and $y_i = x_i$ for every $i \neq j, k$. This is the componentwise form of Lemma 19.8 of
[higham2002accuracy]. -/
theorem abs_sub_le_of_roundsGivensApply {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {c s chat shat : ℝ} (hc : IsRelPert m.u n c chat)
    (hs : IsRelPert m.u n s shat) {j k : ι} {x y : ι → ℝ}
    (h : RoundsGivensApply m chat shat j k x y) :
    |y j - (c * x j - s * x k)| ≤ gamma m.u (n + 2) * (|c| * |x j| + |s| * |x k|) ∧
    |y k - (s * x j + c * x k)| ≤ gamma m.u (n + 2) * (|s| * |x j| + |c| * |x k|) ∧
    ∀ i, i ≠ j → i ≠ k → y i = x i := by
  obtain ⟨⟨p₁, q₁, hp₁, hq₁, hy₁⟩, ⟨p₂, q₂, hp₂, hq₂, hy₂⟩, hrest⟩ := h
  have hu0 := m.u_nonneg
  have hn1 : ((n + 1 : ℕ) : ℝ) * m.u < 1 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega)) hu0).trans_lt hn
  have hu1 : m.u < 1 := by
    have := (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (by omega : 1 ≤ n + 2)) hu0).trans_lt hn
    simpa using this
  have hprod : ∀ {a ah z w : ℝ}, IsRelPert m.u n a ah → m.Rounds (ah * z) w →
      IsRelPert m.u (n + 1) (a * z) w := fun {a ah z w} ha hw => by
    have : IsRelPert m.u n (a * z) (ah * z) := by
      obtain ⟨θ, hθ, rfl⟩ := ha
      exact ⟨θ, hθ, by ring⟩
    exact this.rounds hn1 hw
  refine ⟨?_, ?_, hrest⟩
  · have hq' : IsRelPert m.u (n + 1) (-(s * x k)) (-q₁) := by
      simpa using (hprod hs hq₁).const_mul (-1)
    have := abs_rounds_add_sub_le hn (hprod hc hp₁) hq' (by rwa [← sub_eq_add_neg])
    rwa [← sub_eq_add_neg, abs_neg, abs_mul, abs_mul] at this
  · have := abs_rounds_add_sub_le hn (hprod hs hp₂) (hprod hc hq₂) hy₂
    rwa [abs_mul, abs_mul] at this

omit [DecidableEq ι] in
/-- A vector $d$ that vanishes off two distinct coordinates $j, k$ has the squared Euclidean norm
$d_j^2 + d_k^2$. -/
private theorem norm_toLp_sq_of_eq_zero {j k : ι} (hjk : j ≠ k) {d : ι → ℝ}
    (h : ∀ i, i ≠ j → i ≠ k → d i = 0) :
    ‖(toLp 2 d : EuclideanSpace ℝ ι)‖ ^ 2 = d j ^ 2 + d k ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i, d i ^ 2 = ∑ i ∈ {j, k}, d i ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [h i hi.1 hi.2]
      ring).symm
  rw [hsum, Finset.sum_pair hjk]

omit [DecidableEq ι] in
/-- For two distinct coordinates $j \neq k$ of $x \in \mathbb{R}^\iota$,
$x_j^2 + x_k^2 \le \|x\|_2^2$. -/
theorem sq_add_sq_le_norm_toLp_sq {j k : ι} (hjk : j ≠ k) (x : ι → ℝ) :
    x j ^ 2 + x k ^ 2 ≤ ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_pair (f := fun i => x i ^ 2) hjk]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

/-- Let $(n + 2) u < 1$, let $j \neq k$, let $c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be
relative perturbations of order $n$ of $c$ and $s$. If $y$ is a computed rotation of the
coordinates $j, k$ of $x$ with the data $(\hat c, \hat s)$, then
$$\|y - G(j, k)^T x\|_2 \le \sqrt{2}\, \gamma_{n+2} \|x\|_2,$$
where $G(j, k)$ is the exact rotation `Matrix.planeRotation j k c (-s)`. This is the normwise
form of Lemma 19.8 of [higham2002accuracy], and the analysis of [golub2013matrix], §5.1.10.

Each of the two changed entries has an error of at most $\gamma_{n+2} (|c| |x_j| + |s| |x_k|)$
or $\gamma_{n+2} (|s| |x_j| + |c| |x_k|)$, and the Cauchy–Schwarz inequality bounds both by
$\gamma_{n+2} \sqrt{x_j^2 + x_k^2}$. -/
theorem norm_sub_le_of_roundsGivensApply {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {j k : ι} (hjk : j ≠ k) {c s chat shat : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert m.u n c chat) (hs : IsRelPert m.u n s shat)
    {x y : ι → ℝ} (h : RoundsGivensApply m chat shat j k x y) :
    ‖(toLp 2 (y - (planeRotation j k c (-s))ᵀ *ᵥ x) : EuclideanSpace ℝ ι)‖ ≤
      √2 * gamma m.u (n + 2) * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  obtain ⟨hj, hk, hrest⟩ := abs_sub_le_of_roundsGivensApply hn hc hs h
  set γ := gamma m.u (n + 2)
  have hγ : 0 ≤ γ := gamma_nonneg m.u_nonneg hn
  set d := y - (planeRotation j k c (-s))ᵀ *ᵥ x with hd_def
  have hdj : d j = y j - (c * x j - s * x k) := by
    rw [hd_def, Pi.sub_apply, transpose_planeRotation_mulVec_apply hjk, ite_eq_left rfl]
    ring
  have hdk : d k = y k - (s * x j + c * x k) := by
    rw [hd_def, Pi.sub_apply, transpose_planeRotation_mulVec_apply hjk, ite_eq_right hjk.symm,
      ite_eq_left rfl]
    ring
  have hd0 : ∀ i, i ≠ j → i ≠ k → d i = 0 := fun i hij hik => by
    rw [hd_def, Pi.sub_apply, transpose_planeRotation_mulVec_apply hjk, ite_eq_right hij,
      ite_eq_right hik,
      hrest i hij hik, sub_self]
  -- Cauchy–Schwarz for the two rows
  have hcs1 : (|c| * |x j| + |s| * |x k|) ^ 2 ≤ x j ^ 2 + x k ^ 2 := by
    have := sq_abs c; have := sq_abs s; have := sq_abs (x j); have := sq_abs (x k)
    nlinarith [sq_nonneg (|c| * |x k| - |s| * |x j|)]
  have hcs2 : (|s| * |x j| + |c| * |x k|) ^ 2 ≤ x j ^ 2 + x k ^ 2 := by
    have := sq_abs c; have := sq_abs s; have := sq_abs (x j); have := sq_abs (x k)
    nlinarith [sq_nonneg (|s| * |x k| - |c| * |x j|)]
  have hsq : ‖(toLp 2 d : EuclideanSpace ℝ ι)‖ ^ 2 ≤
      (√2 * γ * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖) ^ 2 := by
    rw [norm_toLp_sq_of_eq_zero hjk hd0, hdj, hdk, mul_pow, mul_pow, Real.sq_sqrt zero_le_two]
    have e1 : (y j - (c * x j - s * x k)) ^ 2 ≤ γ ^ 2 * (x j ^ 2 + x k ^ 2) := by
      rw [← sq_abs]
      calc |y j - (c * x j - s * x k)| ^ 2 ≤ (γ * (|c| * |x j| + |s| * |x k|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hj 2
        _ ≤ γ ^ 2 * (x j ^ 2 + x k ^ 2) := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hcs1 (sq_nonneg _)
    have e2 : (y k - (s * x j + c * x k)) ^ 2 ≤ γ ^ 2 * (x j ^ 2 + x k ^ 2) := by
      rw [← sq_abs]
      calc |y k - (s * x j + c * x k)| ^ 2 ≤ (γ * (|s| * |x j| + |c| * |x k|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hk 2
        _ ≤ γ ^ 2 * (x j ^ 2 + x k ^ 2) := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left hcs2 (sq_nonneg _)
    have e3 := mul_le_mul_of_nonneg_left (sq_add_sq_le_norm_toLp_sq hjk x) (sq_nonneg γ)
    nlinarith
  exact le_of_sq_le_sq hsq (by positivity)

variable {κ : Type*} [Fintype κ]

/-- The computed row update $A([j, k], :) = \begin{bmatrix} c & s \\ -s & c \end{bmatrix}^T A([j,
k], :)$ of [golub2013matrix], §5.1.9. A matrix $B$ is a computed row update of $A$ if every
column of $B$ is a computed rotation (`FloatingPoint.RoundsGivensApply`) of the corresponding
column of $A$.

The exact counterpart is $G(j, k)^T A$, that is `(Matrix.planeRotation j k c (-s))ᵀ * A`. -/
def RoundsGivensRowUpdate (m : RoundingModel ℝ) (c s : ℝ) (j k : ι) (A B : Matrix ι κ ℝ) :
    Prop :=
  ∀ q, RoundsGivensApply m c s j k (fun i => A i q) (fun i => B i q)

/-- The computed column update $A(:, [j, k]) = A(:, [j, k]) \begin{bmatrix} c & s \\ -s & c
\end{bmatrix}$ of [golub2013matrix], §5.1.9. A matrix $B$ is a computed column update of $A$ if
every row of $B$ is a computed rotation (`FloatingPoint.RoundsGivensApply`) of the corresponding
row of $A$. In the loop of the source, this is $A(r, j) = c \tau_1 - s \tau_2$ and
$A(r, k) = s \tau_1 + c \tau_2$.

The exact counterpart is $A G(j, k)$, that is `A * Matrix.planeRotation j k c (-s)`. -/
def RoundsGivensColUpdate (m : RoundingModel ℝ) (c s : ℝ) (j k : ι) (A B : Matrix κ ι ℝ) :
    Prop :=
  ∀ r, RoundsGivensApply m c s j k (A r) (B r)

omit [Fintype κ] in
/-- Let $(n + 2) u < 1$, let $j \neq k$, let $c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be
relative perturbations of order $n$ of $c$ and $s$. If $B$ is a computed row update of $A$ with
the data $(\hat c, \hat s)$, then every column $q$ satisfies
$$\|(B - G(j, k)^T A)_{:, q}\|_2 \le \sqrt{2}\, \gamma_{n+2} \|A_{:, q}\|_2.$$
This is the hypothesis of the columnwise accumulation lemma
`FloatingPoint.exists_eq_prodRev_mul_add` (Lemma 19.3 of [higham2002accuracy]). -/
theorem RoundsGivensRowUpdate.col_norm_sub_le {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {j k : ι} (hjk : j ≠ k) {c s chat shat : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert m.u n c chat) (hs : IsRelPert m.u n s shat)
    {A B : Matrix ι κ ℝ} (h : RoundsGivensRowUpdate m chat shat j k A B) (q : κ) :
    ‖(toLp 2 ((B - (planeRotation j k c (-s))ᵀ * A).col q) : EuclideanSpace ℝ ι)‖ ≤
      √2 * gamma m.u (n + 2) * ‖(toLp 2 (A.col q) : EuclideanSpace ℝ ι)‖ := by
  rw [col_sub_mul]
  exact norm_sub_le_of_roundsGivensApply hn hjk hcs hc hs (h q)

omit [Fintype κ] in
/-- Let $(n + 2) u < 1$, let $j \neq k$, let $c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be
relative perturbations of order $n$ of $c$ and $s$. If $B$ is a computed column update of $A$
with the data $(\hat c, \hat s)$, then every row $r$ satisfies
$$\|(B - A G(j, k))_{r, :}\|_2 \le \sqrt{2}\, \gamma_{n+2} \|A_{r, :}\|_2.$$
Row $r$ of $A G(j, k)$ is $G(j, k)^T$ applied to row $r$ of $A$. -/
theorem RoundsGivensColUpdate.row_norm_sub_le {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {j k : ι} (hjk : j ≠ k) {c s chat shat : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert m.u n c chat) (hs : IsRelPert m.u n s shat)
    {A B : Matrix κ ι ℝ} (h : RoundsGivensColUpdate m chat shat j k A B) (r : κ) :
    ‖(toLp 2 ((B - A * planeRotation j k c (-s)).row r) : EuclideanSpace ℝ ι)‖ ≤
      √2 * gamma m.u (n + 2) * ‖(toLp 2 (A.row r) : EuclideanSpace ℝ ι)‖ := by
  rw [row_sub_mul]
  exact norm_sub_le_of_roundsGivensApply hn hjk hcs hc hs (h r)

open scoped Matrix.Norms.Frobenius in
/-- Let $(n + 2) u < 1$, let $j \neq k$, let $c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be
relative perturbations of order $n$ of $c$ and $s$. If $B$ is a computed row update of $A$ with
the data $(\hat c, \hat s)$, then
$$\|B - G(j, k)^T A\|_F \le \sqrt{2}\, \gamma_{n+2} \|A\|_F.$$
This is the hypothesis on one step of the two-sided accumulation lemma
`FloatingPoint.exists_eq_prodRev_mul_add_mul_prodFwd_rect`, with the right factor $I$. -/
theorem RoundsGivensRowUpdate.frobenius_norm_sub_le {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {j k : ι} (hjk : j ≠ k) {c s chat shat : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert m.u n c chat) (hs : IsRelPert m.u n s shat)
    {A B : Matrix ι κ ℝ} (h : RoundsGivensRowUpdate m chat shat j k A B) :
    ‖B - (planeRotation j k c (-s))ᵀ * A‖ ≤ √2 * gamma m.u (n + 2) * ‖A‖ :=
  frobenius_norm_le_of_forall_col_le (by have := gamma_nonneg m.u_nonneg hn; positivity)
    (h.col_norm_sub_le hn hjk hcs hc hs)

open scoped Matrix.Norms.Frobenius in
/-- Let $(n + 2) u < 1$, let $j \neq k$, let $c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be
relative perturbations of order $n$ of $c$ and $s$. If $B$ is a computed column update of $A$
with the data $(\hat c, \hat s)$, then
$$\|B - A G(j, k)\|_F \le \sqrt{2}\, \gamma_{n+2} \|A\|_F.$$
This is the hypothesis on the right factor of one step of the two-sided accumulation lemma
`FloatingPoint.exists_eq_prodRev_mul_add_mul_prodFwd_rect`. -/
theorem RoundsGivensColUpdate.frobenius_norm_sub_le {m : RoundingModel ℝ} {n : ℕ}
    (hn : ((n + 2 : ℕ) : ℝ) * m.u < 1) {j k : ι} (hjk : j ≠ k) {c s chat shat : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert m.u n c chat) (hs : IsRelPert m.u n s shat)
    {A B : Matrix κ ι ℝ} (h : RoundsGivensColUpdate m chat shat j k A B) :
    ‖B - A * planeRotation j k c (-s)‖ ≤ √2 * gamma m.u (n + 2) * ‖A‖ :=
  frobenius_norm_le_of_forall_row_le (by have := gamma_nonneg m.u_nonneg hn; positivity)
    (h.row_norm_sub_le hn hjk hcs hc hs)

/-! ### The computed rotation matrix is orthogonal to working precision -/

section L2

open scoped Matrix.Norms.L2Operator

/-- Let $u \in \mathbb{R}$ and $n \in \mathbb{N}$ with $\gamma_n \ge 0$, let $j \neq k$, let
$c^2 + s^2 = 1$, and let $\hat c$ and $\hat s$ be relative perturbations of order $n$ of $c$ and
$s$. Then
$$\|G(\hat c, \hat s) - G(c, s)\|_2 \le \gamma_n,$$
where $G(c, s)$ is the rotation `Matrix.planeRotation j k c (-s)` of the $(j, k)$-plane and
$\|\cdot\|_2$ is the spectral norm. This is the part of [golub2013matrix], §5.1.12, about Givens
rotations: the computed rotation matrix is orthogonal to working precision.

On the $(j, k)$-plane, the difference is $\sqrt{(\hat c - c)^2 + (\hat s - s)^2}$ times a
rotation, and it vanishes off the plane. -/
theorem l2_opNorm_planeRotation_sub_le {u : ℝ} {n : ℕ} (hγ : 0 ≤ gamma u n) {j k : ι}
    (hjk : j ≠ k) {c s chat shat : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : IsRelPert u n c chat)
    (hs : IsRelPert u n s shat) :
    ‖planeRotation j k chat (-shat) - planeRotation j k c (-s)‖ ≤ gamma u n := by
  refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ hγ fun z => ?_
  set x : ι → ℝ := ofLp z with hx
  have hz : z = toLp 2 x := rfl
  rw [toEuclideanLin_apply, hz, ← hx]
  set d := (planeRotation j k chat (-shat) - planeRotation j k c (-s)) *ᵥ x with hd_def
  have happ : ∀ (a b : ℝ) (i : ι), (planeRotation j k a (-b) *ᵥ x) i =
      if i = j then a * x j + b * x k else if i = k then -b * x j + a * x k else x i :=
    fun a b i => by
    rw [← planeRotation_transpose hjk, transpose_planeRotation_mulVec_apply hjk]
  have hdj : d j = (chat - c) * x j + (shat - s) * x k := by
    rw [hd_def, sub_mulVec, Pi.sub_apply, happ, happ, ite_eq_left rfl, ite_eq_left rfl]
    ring
  have hdk : d k = -(shat - s) * x j + (chat - c) * x k := by
    rw [hd_def, sub_mulVec, Pi.sub_apply, happ, happ, ite_eq_right hjk.symm, ite_eq_left rfl,
      ite_eq_right hjk.symm, ite_eq_left rfl]
    ring
  have hd0 : ∀ i, i ≠ j → i ≠ k → d i = 0 := fun i hij hik => by
    rw [hd_def, sub_mulVec, Pi.sub_apply, happ, happ, ite_eq_right hij, ite_eq_right hik,
      ite_eq_right hij,
      ite_eq_right hik, sub_self]
  have hδc : (chat - c) ^ 2 ≤ gamma u n ^ 2 * c ^ 2 := by
    rw [← sq_abs (chat - c), ← sq_abs c, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hc.abs_sub_le 2
  have hδs : (shat - s) ^ 2 ≤ gamma u n ^ 2 * s ^ 2 := by
    rw [← sq_abs (shat - s), ← sq_abs s, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hs.abs_sub_le 2
  have hsq : ‖(toLp 2 d : EuclideanSpace ℝ ι)‖ ^ 2 ≤
      (gamma u n * ‖(toLp 2 x : EuclideanSpace ℝ ι)‖) ^ 2 := by
    rw [norm_toLp_sq_of_eq_zero hjk hd0, hdj, hdk, mul_pow]
    have h1 : ((chat - c) * x j + (shat - s) * x k) ^ 2 + (-(shat - s) * x j + (chat - c) * x k) ^ 2
        = ((chat - c) ^ 2 + (shat - s) ^ 2) * (x j ^ 2 + x k ^ 2) := by ring
    rw [h1]
    have h2 : (chat - c) ^ 2 + (shat - s) ^ 2 ≤ gamma u n ^ 2 := by nlinarith
    have h3 := sq_add_sq_le_norm_toLp_sq hjk x
    exact mul_le_mul h2 h3 (by positivity) (sq_nonneg _)
  exact le_of_sq_le_sq hsq (by positivity)

/-- Let $Q$ be an orthogonal matrix, and let $\hat Q$ be a matrix with
$\|\hat Q - Q\|_2 \le \varepsilon$ in the spectral norm. Then
$$\|\hat Q^T \hat Q - I\|_2 \le 2 \varepsilon + \varepsilon^2.$$
This is how [golub2013matrix], §5.1.12, passes from "orthogonal to working precision" to
near-orthogonality.

With $\hat Q = Q + E$, the identity $\hat Q^T \hat Q - I = Q^T E + E^T Q + E^T E$ and the
invariance of the spectral norm under orthogonal transformations give the bound. -/
theorem l2_opNorm_transpose_mul_self_sub_one_le {Q Qhat : Matrix ι ι ℝ}
    (hQ : Q ∈ Matrix.orthogonalGroup ι ℝ) {ε : ℝ} (h : ‖Qhat - Q‖ ≤ ε) :
    ‖Qhatᵀ * Qhat - 1‖ ≤ 2 * ε + ε ^ 2 := by
  set E := Qhat - Q with hE
  have hQE : Qhat = Q + E := by rw [hE]; abel
  have hQQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' _ _).1 hQ
  have hQT : Qᵀ ∈ Matrix.orthogonalGroup ι ℝ := transpose_mem_unitaryGroup_iff.2 hQ
  have hEt : ‖Eᵀ‖ = ‖E‖ := by
    have := l2_opNorm_conjTranspose E
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hsplit : Qhatᵀ * Qhat - 1 = Qᵀ * E + Eᵀ * Q + Eᵀ * E := by
    rw [hQE, transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hQQ]
    abel
  have h1 : ‖Qᵀ * E‖ = ‖E‖ := l2_opNorm_unitary_mul hQT E
  have h2 : ‖Eᵀ * Q‖ = ‖E‖ := by rw [l2_opNorm_mul_unitary _ hQ, hEt]
  have h3 : ‖Eᵀ * E‖ ≤ ‖E‖ * ‖E‖ := by
    have := l2_opNorm_mul Eᵀ E
    rwa [hEt] at this
  have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
  rw [hsplit]
  calc ‖Qᵀ * E + Eᵀ * Q + Eᵀ * E‖ ≤ ‖Qᵀ * E‖ + ‖Eᵀ * Q‖ + ‖Eᵀ * E‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖E‖ + ‖E‖ + ‖E‖ * ‖E‖ := by rw [h1, h2]; linarith
    _ ≤ 2 * ε + ε ^ 2 := by nlinarith

end L2

end FloatingPoint
