/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Operator.Scaling
import Numlib.Variational.Forms
import Numlib.Variational.LaxMilgram
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson and Han, Section 8.7: The generalized Lax–Milgram lemma

This module formalizes Section 8.7 of [han2009theoretical]. Let $U$ and $V$ be real Hilbert spaces,
let $a : U \times V \to \mathbb{R}$ be a bilinear form and let $\ell \in V'$. Theorem 8.7.1, which
the source attributes to Nečas, states the following. If $a$ is bounded (8.7.1), satisfies the
inf–sup condition (8.7.2)
$$\sup_{0 \ne v \in V} \frac{a(u, v)}{\|v\|_V} \ge \alpha \|u\|_U \quad \text{for all } u \in U$$
with $\alpha > 0$, and satisfies the nondegeneracy condition (8.7.3) in its second argument, then
the problem (8.7.4), to find $u \in U$ with $a(u, v) = \ell(v)$ for all $v \in V$, has exactly one
solution, and the solution satisfies the stability estimate (8.7.5)
$\|u\|_U \le \|\ell\|_{V'}/\alpha$. Exercise 8.7.1 shows that the theorem contains the Lax–Milgram
lemma, Theorem 8.3.4.

The proofs specialize `SesqForm₂.babuska_necas` and `SesqForm₂.norm_le_of_infSupWith` of
`Numlib.Variational.LaxMilgram`. The two-space bilinear forms defined here are also the data of
Section 9.2.

## Main definitions

* Equation (8.7.1), `AtkinsonHan.BilinForm₂.IsBoundedWith`: $|a(u, v)| \le M \|u\|_U \|v\|_V$.
* Equation (8.7.2), `AtkinsonHan.BilinForm₂.InfSup`: the inf–sup condition with constant $\alpha$,
  with the supremum as the source prints it.

## Main results

* Theorem 8.7.1, `AtkinsonHan.Chapter08.theorem_8_7_1`: under (8.7.1)–(8.7.3) the problem (8.7.4)
  has exactly one solution.
* Theorem 8.7.1, `AtkinsonHan.Chapter08.theorem_8_7_1_norm_le`: the stability estimate (8.7.5)
  $\|u\|_U \le \|\ell\|_{V'}/\alpha$.
* Exercise 8.7.1, `AtkinsonHan.BilinForm.IsEllipticWith.infSup` and
  `AtkinsonHan.BilinForm.IsEllipticWith.exists_pos`: a bounded $V$-elliptic form satisfies (8.7.2)
  and (8.7.3).
* Exercise 8.7.1, `AtkinsonHan.Chapter08.exercise_8_7_1` and
  `AtkinsonHan.Chapter08.exercise_8_7_1_norm_le`: Theorem 8.7.1 gives the Lax–Milgram lemma and its
  stability estimate.

## Implementation notes

* A two-space bilinear form is `AtkinsonHan.BilinForm₂ U V`, that is `U →ₗ[ℝ] V →ₗ[ℝ] ℝ`. Bundled by
  `AtkinsonHan.BilinForm₂.toCLM`, it is the backbone's `SesqForm₂ ℝ U V`.
* The source writes (8.7.2) without absolute values. `AtkinsonHan.BilinForm₂.iSup_div_eq_norm_apply`
  shows that this supremum is the operator norm $\|a(u, \cdot)\|_{V'}$, which is the form of the
  backbone's `SesqForm₂.InfSupWith`.
* As in Section 8.3, the unique solvability (8.7.4) and the stability estimate (8.7.5) are separate
  declarations.

## Deviations from the source

* **Equation (8.7.3)** (reading). The source prints $\sup_{u \in U} a(u, v) > 0$ for $v \ne 0$. Read
  literally, this says nothing: the supremum of a nonzero linear functional is $+\infty$. It is
  formalized as: for every $v \ne 0$ there is $u$ with $a(u, v) > 0$. See
  `AtkinsonHan.Chapter08.theorem_8_7_1`.
-/

open scoped InnerProductSpace

namespace AtkinsonHan

/-! ### Two-space bilinear forms -/

/-- A **real bilinear form** $a : U \times V \to \mathbb{R}$ on a pair of real vector spaces, the
data of Section 8.7 and Section 9.2 of [han2009theoretical]. It is a linear map from $U$ to the
linear maps from $V$ to $\mathbb{R}$. -/
abbrev BilinForm₂ (U V : Type*) [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] :=
  U →ₗ[ℝ] V →ₗ[ℝ] ℝ

namespace BilinForm₂

section Normed

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- **Equation (8.7.1)** of [han2009theoretical], also (9.2.2). Let $U$ and $V$ be real normed
spaces. A bilinear form $a : U \times V \to \mathbb{R}$ is **bounded with constant** $M$ if
$$|a(u, v)| \le M \|u\|_U \|v\|_V \quad \text{for all } u \in U,\ v \in V.$$

No sign condition on $M$ is part of the definition. -/
def IsBoundedWith (a : BilinForm₂ U V) (M : ℝ) : Prop := ∀ u v, |a u v| ≤ M * ‖u‖ * ‖v‖

variable {a : BilinForm₂ U V} {M α : ℝ}

/-- A bilinear form on $V \times V$ that is bounded with constant $M$ in the sense of
`AtkinsonHan.BilinForm.IsBoundedWith` is bounded with constant $M$ as a two-space form with
$U = V$. -/
theorem isBoundedWith_of_isBoundedWith {b : BilinForm V} (h : b.IsBoundedWith M) :
    IsBoundedWith (U := V) (V := V) b M := h

/-- Let $U$ and $V$ be real normed spaces, and let $a : U \times V \to \mathbb{R}$ be bilinear and
bounded with constant $M$. The **bundled form** of $a$ is $a$ seen as a bounded bilinear map in
$\mathcal{L}(U, V')$, that is `U →L[ℝ] V →L[ℝ] ℝ`.

Over $\mathbb{R}$ this type is the backbone's `SesqForm₂ ℝ U V`, so the backbone results on
two-space forms apply to `a.toCLM hM`. -/
noncomputable def toCLM (a : BilinForm₂ U V) (hM : a.IsBoundedWith M) : U →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ a M fun u v => by rw [Real.norm_eq_abs]; exact hM u v

/-- The bundled form of a bounded two-space bilinear form has the same values as the form:
$(a.\mathrm{toCLM})(u)(v) = a(u, v)$ for all $u \in U$, $v \in V$. -/
@[simp]
theorem toCLM_apply (hM : a.IsBoundedWith M) (u : U) (v : V) : a.toCLM hM u v = a u v := rfl

/-- Let $a : U \times V \to \mathbb{R}$ be bilinear and bounded with constant $M \ge 0$. Then the
operator norm of the bundled form is at most $M$.

So the boundedness constant of (8.7.1) can be used wherever the backbone asks for $\|a\|$. -/
theorem norm_toCLM_le (hM0 : 0 ≤ M) (hM : a.IsBoundedWith M) : ‖a.toCLM hM‖ ≤ M :=
  LinearMap.mkContinuous₂_norm_le _ hM0 _

/-- The bundled form of a two-space form that is bounded with constant $M$ satisfies
$|a(u, v)| \le M \|u\|_U \|v\|_V$ for all $u$ and $v$. -/
theorem isBoundedWith_toCLM (hM : a.IsBoundedWith M) :
    ∀ u v, ‖a.toCLM hM u v‖ ≤ M * ‖u‖ * ‖v‖ := hM

/-- **Equation (8.7.2)** of [han2009theoretical], also (9.2.3). A bilinear form
$a : U \times V \to \mathbb{R}$ satisfies the **inf–sup condition** with constant $\alpha$ if
$$\alpha \|u\|_U \le \sup_{0 \ne v \in V} \frac{a(u, v)}{\|v\|_V} \quad \text{for all } u \in
  U.$$

The supremum is written as in the source, without absolute values. It is the real supremum
`iSup`, which is $0$ when $V = \{0\}$ and also when the quotients are unbounded above. For a
bounded form it is finite, and `AtkinsonHan.BilinForm₂.iSup_div_eq_norm_apply` identifies it
with $\|a(u, \cdot)\|_{V'}$. -/
def InfSup (a : BilinForm₂ U V) (α : ℝ) : Prop :=
  ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖

/-- Let $a : U \times V \to \mathbb{R}$ be bilinear and bounded with constant $M$. Then for every
$u \in U$ the supremum in (8.7.2) is the operator norm of the functional $a(u, \cdot)$:
$$\sup_{0 \ne v \in V} \frac{a(u, v)}{\|v\|_V} = \|a(u, \cdot)\|_{V'}.$$

The proof is `ContinuousLinearMap.iSup_apply_div_eq_opNorm`. The sign flip $v \mapsto -v$ makes
the absolute value unnecessary. -/
theorem iSup_div_eq_norm_apply (hM : a.IsBoundedWith M) (u : U) :
    (⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖) = ‖a.toCLM hM u‖ :=
  (a.toCLM hM u).iSup_apply_div_eq_opNorm

/-- Let $a : U \times V \to \mathbb{R}$ be bilinear and let $v \in V$. There is $u \in U$ with
$a(u, v) > 0$ if and only if there is $u \in U$ with $a(u, v) \ne 0$.

The left side is the reading of the nondegeneracy condition (8.7.3), also (9.2.4), which the
source prints as $\sup_{u \in U} a(u, v) > 0$. The right side is the backbone's
`SesqForm₂.IsNondegenerate`. The proof uses the sign flip $u \mapsto -u$. -/
theorem exists_pos_iff_exists_ne_zero (a : BilinForm₂ U V) (v : V) :
    (∃ u, 0 < a u v) ↔ ∃ u, a u v ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, ne_of_gt hu⟩
  · rintro ⟨u, hu⟩
    rcases lt_or_gt_of_ne hu with h | h
    · exact ⟨-u, by simpa using h⟩
    · exact ⟨u, h⟩

end Normed

section Inner

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
variable {a : BilinForm₂ U V} {M α : ℝ}

/-- Let $U$ and $V$ be real inner product spaces, and let $a : U \times V \to \mathbb{R}$ be
bilinear and bounded with constant $M$. Then $a$ satisfies the inf–sup condition (8.7.2) with
constant $\alpha$ if and only if its bundled form satisfies the backbone's
`SesqForm₂.InfSupWith` with constant $\alpha$, that is $\alpha \|u\|_U \le \|a(u, \cdot)\|_{V'}$
for all $u$. -/
theorem infSup_iff_infSupWith (hM : a.IsBoundedWith M) :
    a.InfSup α ↔ SesqForm₂.InfSupWith (𝕜 := ℝ) (U := U) (V := V) (a.toCLM hM) α := by
  refine forall_congr' fun u => ?_
  rw [iSup_div_eq_norm_apply hM u]

/-- Let $U$ and $V$ be real inner product spaces, and let $a : U \times V \to \mathbb{R}$ be
bilinear and bounded with constant $M$. If for every $v \ne 0$ there is $u$ with $a(u, v) > 0$,
as in (8.7.3), then the bundled form is nondegenerate in the sense of the backbone's
`SesqForm₂.IsNondegenerate`. -/
theorem isNondegenerate_toCLM (hM : a.IsBoundedWith M) (h : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
    SesqForm₂.IsNondegenerate (𝕜 := ℝ) (U := U) (V := V) (a.toCLM hM) :=
  fun v hv => (exists_pos_iff_exists_ne_zero a v).mp (h v hv)

end Inner

end BilinForm₂

/-!
### Exercise 8.7.1: a $V$-elliptic form satisfies (8.7.2) and (8.7.3)

The two results are in the namespace `AtkinsonHan.BilinForm.IsEllipticWith`, so that dot notation
reaches them from an ellipticity hypothesis.
-/

section Elliptic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a : BilinForm V} {M α : ℝ}

/-- **Exercise 8.7.1** of [han2009theoretical], the inf–sup condition. Let $V$ be a real inner
product space, and let $a : V \times V \to \mathbb{R}$ be bilinear, bounded with constant $M$,
and $V$-elliptic with constant $\alpha$. Then $a$ satisfies the inf–sup condition (8.7.2) with
the same constant: for every $u \in V$,
$$\alpha \|u\| \le \sup_{0 \ne v \in V} \frac{a(u, v)}{\|v\|}.$$

The choice $v = u$ already gives the bound. Boundedness is used only to make the supremum
finite. -/
theorem BilinForm.IsEllipticWith.infSup (ha : a.IsEllipticWith α) (hM : a.IsBoundedWith M)
    (u : V) : α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖ := by
  rw [BilinForm₂.iSup_div_eq_norm_apply (BilinForm₂.isBoundedWith_of_isBoundedWith hM) u]
  exact SesqForm.IsCoerciveWith.norm_le_norm_apply (a.toCLM hM) ha u

/-- **Exercise 8.7.1** of [han2009theoretical], the nondegeneracy condition. Let $V$ be a real inner
product space, and let $a : V \times V \to \mathbb{R}$ be bilinear and $V$-elliptic with
constant $\alpha > 0$. Then $a$ satisfies the nondegeneracy condition (8.7.3): for every
$v \ne 0$ there is $u$ with $a(u, v) > 0$.

The choice $u = v$ gives $a(v, v) \ge \alpha \|v\|^2 > 0$. -/
theorem BilinForm.IsEllipticWith.exists_pos (ha : a.IsEllipticWith α) (hα : 0 < α) (v : V)
    (hv : v ≠ 0) : ∃ u, 0 < a u v :=
  ⟨v, lt_of_lt_of_le (by positivity) (ha v)⟩

end Elliptic

namespace Chapter08

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

/-- **Theorem 8.7.1** of [han2009theoretical] (the generalized Lax–Milgram lemma, due to Nečas). Let
$U$ and $V$ be real Hilbert spaces, let $a : U \times V \to \mathbb{R}$ be bilinear and let
$\ell \in V'$. Let $M$ be a constant and $\alpha > 0$, and assume:

* (8.7.1) $|a(u, v)| \le M \|u\|_U \|v\|_V$ for all $u \in U$, $v \in V$;
* (8.7.2) $\alpha \|u\|_U \le \sup_{0 \ne v \in V} a(u, v)/\|v\|_V$ for all $u \in U$;
* (8.7.3) for every $v \in V$ with $v \ne 0$ there is $u \in U$ with $a(u, v) > 0$.

Then there is exactly one $u \in U$ such that (8.7.4)
$$a(u, v) = \ell(v) \quad \text{for all } v \in V.$$

**Reading.** The source prints (8.7.3) as $\sup_{u \in U} a(u, v) > 0$. Read literally this says
nothing, since the supremum of a nonzero linear functional is $+\infty$. The condition is
formalized as the existence of $u$ with $a(u, v) > 0$, which is equivalent to
$a(\cdot, v) \ne 0$ by `AtkinsonHan.BilinForm₂.exists_pos_iff_exists_ne_zero`.

The supremum in (8.7.2) is the real supremum `iSup`, and is finite by (8.7.1). The stability
estimate (8.7.5) is `AtkinsonHan.Chapter08.theorem_8_7_1_norm_le`. The proof specializes the
backbone's `SesqForm₂.babuska_necas`. -/
theorem theorem_8_7_1 [CompleteSpace U] [CompleteSpace V] (a : BilinForm₂ U V)
    (ℓ : StrongDual ℝ V) {M α : ℝ} (hα : 0 < α)
    (h871 : a.IsBoundedWith M)
    (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖)
    (h873 : ∀ v, v ≠ 0 → ∃ u, 0 < a u v) :
    ∃! u, ∀ v, a u v = ℓ v :=
  SesqForm₂.babuska_necas (a.toCLM h871) ℓ hα ((BilinForm₂.infSup_iff_infSupWith h871).mp h872)
    (BilinForm₂.isNondegenerate_toCLM h871 h873)

/-- **Theorem 8.7.1** of [han2009theoretical], the stability estimate (8.7.5). Let $U$ and $V$ be
real Hilbert spaces, let $a : U \times V \to \mathbb{R}$ be bilinear and bounded with constant
$M$ (8.7.1), let $\ell \in V'$, and let $a$ satisfy the inf–sup condition (8.7.2) with constant
$\alpha > 0$. If $u \in U$ satisfies $a(u, v) = \ell(v)$ for all $v \in V$, then
$$\|u\|_U \le \frac{\|\ell\|_{V'}}{\alpha}.$$

Only the inf–sup condition is used: the nondegeneracy condition (8.7.3) gives the existence of a
solution, not the bound. The proof specializes the backbone's `SesqForm₂.norm_le_of_infSupWith`. -/
theorem theorem_8_7_1_norm_le [CompleteSpace U] [CompleteSpace V] (a : BilinForm₂ U V)
    (ℓ : StrongDual ℝ V) {M α : ℝ} (hα : 0 < α) (h871 : a.IsBoundedWith M)
    (h872 : ∀ u, α * ‖u‖ ≤ ⨆ v : {v : V // v ≠ 0}, a u v / ‖(v : V)‖) {u : U}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α :=
  SesqForm₂.norm_le_of_infSupWith (a.toCLM h871) ℓ hα
    ((BilinForm₂.infSup_iff_infSupWith h871).mp h872) hu

/-- **Exercise 8.7.1** of [han2009theoretical], unique solvability. Let $V$ be a real Hilbert space,
let $a : V \times V \to \mathbb{R}$ be bilinear, bounded with constant $M$ and $V$-elliptic with
constant $\alpha > 0$, and let $\ell \in V'$. Then there is exactly one $u \in V$ with
$a(u, v) = \ell(v)$ for all $v \in V$.

This is the Lax–Milgram lemma `AtkinsonHan.Chapter08.theorem_8_3_4`, derived here from Theorem
8.7.1 with $U = V$ through `AtkinsonHan.BilinForm.IsEllipticWith.infSup` and
`AtkinsonHan.BilinForm.IsEllipticWith.exists_pos`. -/
theorem exercise_8_7_1 [CompleteSpace V] (a : BilinForm V) (ℓ : StrongDual ℝ V) {M α : ℝ}
    (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α) : ∃! u, ∀ v, a u v = ℓ v :=
  theorem_8_7_1 a ℓ hα (BilinForm₂.isBoundedWith_of_isBoundedWith hM) (ha.infSup hM)
    fun v hv => ha.exists_pos hα v hv

/-- **Exercise 8.7.1** of [han2009theoretical], the stability estimate. Let $V$ be a real Hilbert
space, let $a : V \times V \to \mathbb{R}$ be bilinear, bounded with constant $M$ and
$V$-elliptic with constant $\alpha > 0$, and let $\ell \in V'$. If $u \in V$ satisfies
$a(u, v) = \ell(v)$ for all $v \in V$, then $\|u\| \le \|\ell\|/\alpha$.

This is the stability estimate `AtkinsonHan.Chapter08.theorem_8_3_4_norm_le` of the Lax–Milgram
lemma, derived here from (8.7.5). -/
theorem exercise_8_7_1_norm_le [CompleteSpace V] (a : BilinForm V) (ℓ : StrongDual ℝ V)
    {M α : ℝ} (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α) {u : V}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α :=
  theorem_8_7_1_norm_le a ℓ hα (BilinForm₂.isBoundedWith_of_isBoundedWith hM) (ha.infSup hM) hu

end Chapter08

end AtkinsonHan
