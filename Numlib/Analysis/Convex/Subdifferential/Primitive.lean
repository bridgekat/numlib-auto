/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.OneDim

/-!
# The convex primitive of a nondecreasing function on the line

Let $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some point.
Then there is a closed proper convex function $f$ on $\mathbb{R}$ with $f'_- \le \varphi \le f'_+$,
and $f$ is unique up to an additive constant. This is Theorem 24.2 of [rockafellar1970convex]. The
uniqueness part is in `Numlib.Analysis.Convex.Subdifferential.OneDim`, and this module proves the
existence part.

The construction uses the region
$$\Gamma(\varphi) = \{(x, y) \in \mathbb{R} \times \mathbb{R} \mid \varphi_-(x) \le y \le
  \varphi_+(x)\}, \qquad \varphi_-(x) = \sup_{z < x} \varphi(z), \quad \varphi_+(x) = \inf_{z > x}
  \varphi(z),$$
a **complete non-decreasing curve**. It is a chain for the coordinatewise order, and it meets every
antidiagonal $\{(u, v) \mid u + v = s\}$. This makes it a maximal chain. A maximal monotone relation
on the line is a subdifferential, so there is a closed proper convex $f$ with
$\partial f = \Gamma(\varphi)$. The endpoints of the fibres of $\Gamma(\varphi)$ and of $\partial f$
then give $f'_- = \varphi_- \le \varphi \le \varphi_+ = f'_+$. No integral is used: the classical
formula $f(x) = \int_a^x \varphi(t) \, dt$ is replaced by the subdifferential.

## Main definitions

* `ConvexAnalysis.monotoneCurve`: the region $\Gamma(\varphi)$.

## Main results

* `ConvexAnalysis.isMaximalMonotoneRel_monotoneCurve`: for a nondecreasing $\varphi$ that is finite
  at a point, $\Gamma(\varphi)$ is maximal monotone.
* `ConvexAnalysis.subgradientRel_eq_monotoneCurve_rightDeriv`: conversely, every $\partial f$ on the
  line is the curve $\Gamma(f'_+)$.
* `ConvexAnalysis.exists_monotone_ne_bot_ne_top_monotoneCurve_eq`: every $\partial f$ on the line is
  $\Gamma(\varphi)$ for a nondecreasing $\varphi$ that is finite at a point. A change of $\varphi$
  at one point changes neither its monotonicity nor $\Gamma(\varphi)$.
* `ConvexAnalysis.exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq`: the existence part, with
  $f'_- = \varphi_-$ and $f'_+ = \varphi_+$.
* `ConvexAnalysis.exists_closedProperConvexFn_forall_le_le`: existence and uniqueness
  ([rockafellar1970convex], Theorem 24.2).

## Implementation notes

* The maximality of $\Gamma(\varphi)$ is proved from the antidiagonal statement, not by a case
  analysis on the points where $\varphi = \pm\infty$. If a pair $p$ is comparable with every element
  of $\Gamma(\varphi)$, then $p$ equals the element of $\Gamma(\varphi)$ with the same coordinate
  sum.
* The fibre $\{y \mid (x, y) \in \Gamma(\varphi)\}$ can be empty, for example to the left of a point
  where $\varphi = -\infty$. There the identity $\Gamma(\varphi) = \partial f$ gives no information
  at $x$. What decides the endpoints is that an extended-real interval with no real point has both
  endpoints $-\infty$ or both $+\infty$. A comparison with a fibre that is not empty decides between
  the two cases.
-/

open Set Filter Topology

namespace ConvexAnalysis

/-! ### Extended-real intervals -/

section Interval

/-- Let $A_1, B_1, A_2, B_2 \in [-\infty, +\infty]$, and let some real $y$ satisfy
$A_1 \le y \le B_1$. If the intervals $[A_1, B_1]$ and $[A_2, B_2]$ contain the same real
numbers, then $A_1 = A_2$ and $B_1 = B_2$. -/
theorem eq_and_eq_of_forall_coe_mem_iff {A₁ B₁ A₂ B₂ : EReal}
    (hne : ∃ y : ℝ, A₁ ≤ (y : EReal) ∧ (y : EReal) ≤ B₁)
    (h : ∀ y : ℝ, (A₁ ≤ (y : EReal) ∧ (y : EReal) ≤ B₁) ↔
      (A₂ ≤ (y : EReal) ∧ (y : EReal) ≤ B₂)) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  obtain ⟨y₀, hy₁, hy₂⟩ := hne
  obtain ⟨hy₃, hy₄⟩ := (h y₀).1 ⟨hy₁, hy₂⟩
  constructor
  · refine le_antisymm ?_ ?_
    · by_contra hcon
      push Not at hcon
      obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      exact absurd ((h r).2 ⟨hr₁.le, ((hr₂.trans_le hy₁).le).trans hy₄⟩).1 (not_le.2 hr₂)
    · by_contra hcon
      push Not at hcon
      obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      exact absurd ((h r).1 ⟨hr₁.le, ((hr₂.trans_le hy₃).le).trans hy₂⟩).1 (not_le.2 hr₂)
  · refine le_antisymm ?_ ?_
    · by_contra hcon
      push Not at hcon
      obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      exact absurd ((h r).1 ⟨hy₁.trans (hy₄.trans hr₁.le), hr₂.le⟩).2 (not_le.2 hr₁)
    · by_contra hcon
      push Not at hcon
      obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      exact absurd ((h r).2 ⟨hy₃.trans (hy₂.trans hr₁.le), hr₂.le⟩).2 (not_le.2 hr₁)

/-- Let $A \le B$ in $[-\infty, +\infty]$, and let no real $y$ satisfy $A \le y \le B$. Then
$A = B = -\infty$ or $A = B = +\infty$.

A finite $A$ would be such a $y$, and $A = -\infty$ with $B \neq -\infty$ leaves room for one. -/
theorem eq_bot_or_eq_top_of_forall_not_coe_mem {A B : EReal} (hAB : A ≤ B)
    (h : ∀ y : ℝ, ¬(A ≤ (y : EReal) ∧ (y : EReal) ≤ B)) :
    (A = ⊥ ∧ B = ⊥) ∨ (A = ⊤ ∧ B = ⊤) := by
  induction A with
  | bot =>
    refine Or.inl ⟨rfl, ?_⟩
    by_contra hB
    obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 hB)
    exact h r ⟨bot_le, hr.le⟩
  | coe c => exact absurd ⟨le_rfl, hAB⟩ (h c)
  | top => exact Or.inr ⟨rfl, top_le_iff.1 hAB⟩

end Interval

/-! ### The complete non-decreasing curve of a function -/

section Curve

variable {φ : ℝ → EReal}

/-- The region between the two one-sided limits of $\varphi \colon \mathbb{R} \to [-\infty,
+\infty]$:
$$\Gamma(\varphi) = \{(x, y) \in \mathbb{R} \times \mathbb{R} \mid \sup_{z < x} \varphi(z) \le y
  \le \inf_{z > x} \varphi(z)\}.$$

For a nondecreasing $\varphi$ that is finite at a point, it is a **complete non-decreasing
curve**: a maximal chain for the coordinatewise order on $\mathbb{R} \times \mathbb{R}$, and the
graph of $\partial f$ for a closed proper convex $f$. -/
def monotoneCurve (φ : ℝ → EReal) : SetRel ℝ ℝ :=
  {p : ℝ × ℝ | (⨆ z ∈ Iio p.1, φ z) ≤ (p.2 : EReal) ∧ (p.2 : EReal) ≤ ⨅ z ∈ Ioi p.1, φ z}

/-- A pair $(x, y)$ is in $\Gamma(\varphi)$ if and only if $\sup_{z < x} \varphi(z) \le y \le
\inf_{z > x} \varphi(z)$. -/
@[simp] theorem mem_monotoneCurve {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ monotoneCurve φ ↔
      (⨆ z ∈ Iio x, φ z) ≤ (y : EReal) ∧ (y : EReal) ≤ ⨅ z ∈ Ioi x, φ z :=
  Iff.rfl

/-- For every $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$, monotone or not, the region
$\Gamma(\varphi)$ is a monotone relation.

Between two of its points with different first coordinates lies a value of $\varphi$. This value
bounds the second coordinate of the left point from above and that of the right point from
below. -/
theorem isMonotoneRel_monotoneCurve (φ : ℝ → EReal) :
    IsMonotoneRel (innerₗ ℝ) (monotoneCurve φ) := by
  have key : ∀ p ∈ monotoneCurve φ, ∀ q ∈ monotoneCurve φ, p.1 < q.1 → p.2 ≤ q.2 := by
    intro p hp q hq hlt
    have h₁ : p.1 < (p.1 + q.1) / 2 := by linarith
    have h₂ : (p.1 + q.1) / 2 < q.1 := by linarith
    have hA : ((p.2 : ℝ) : EReal) ≤ φ ((p.1 + q.1) / 2) :=
      hp.2.trans (iInf₂_le _ h₁)
    have hB : φ ((p.1 + q.1) / 2) ≤ ((q.2 : ℝ) : EReal) :=
      (le_iSup₂ (f := fun z (_ : z ∈ Iio q.1) => φ z) _ h₂).trans hq.1
    exact_mod_cast hA.trans hB
  rw [isMonotoneRel_iff_forall_le_or_le]
  intro p hp q hq
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · exact Or.inl (Prod.le_def.2 ⟨hlt.le, key p hp q hq hlt⟩)
  · rcases le_total p.2 q.2 with hle | hle
    · exact Or.inl (Prod.le_def.2 ⟨heq.le, hle⟩)
    · exact Or.inr (Prod.le_def.2 ⟨heq.ge, hle⟩)
  · exact Or.inr (Prod.le_def.2 ⟨hgt.le, key q hq p hp hgt⟩)

/-- Let $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some point
$a$. Then $\Gamma(\varphi)$ meets every antidiagonal: for each $s \in \mathbb{R}$ there is $u$
with $(u, s - u) \in \Gamma(\varphi)$.

Equivalently, $(x, y) \mapsto x + y$ maps $\Gamma(\varphi)$ onto $\mathbb{R}$. This makes
$\Gamma(\varphi)$ a maximal chain. The point is $u = \sup \{t \mid \varphi(t) \le s - t\}$. -/
theorem exists_mem_monotoneCurve_sub (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤)
    (s : ℝ) : ∃ u : ℝ, ((u, s - u) : ℝ × ℝ) ∈ monotoneCurve φ := by
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  set T : Set ℝ := {t : ℝ | φ t ≤ ((s - t : ℝ) : EReal)}
  have hTdown : ∀ t t' : ℝ, t ≤ t' → t' ∈ T → t ∈ T := fun t t' hle hmem =>
    (hφ hle).trans (hmem.trans (by exact_mod_cast (by linarith : s - t' ≤ s - t)))
  have hTne : T.Nonempty := by
    refine ⟨min a (s - c), ?_⟩
    have h₁ : φ (min a (s - c)) ≤ (c : EReal) := hc ▸ hφ (min_le_left _ _)
    have h₂ : c ≤ s - min a (s - c) := by linarith [min_le_right a (s - c)]
    exact h₁.trans (by exact_mod_cast h₂)
  have hTbdd : BddAbove T := by
    refine ⟨max a (s - c), fun t htT => ?_⟩
    by_contra hcon
    push Not at hcon
    have h₁ : (c : EReal) ≤ φ t := hc ▸ hφ (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hcon))
    have h₂ : ((s - t : ℝ) : EReal) < (c : EReal) := by
      have := lt_of_le_of_lt (le_max_right a (s - c)) hcon
      exact_mod_cast (by linarith : s - t < c)
    exact absurd (h₁.trans htT) (not_le.2 h₂)
  refine ⟨sSup T, iSup₂_le fun z hz => ?_, le_iInf₂ fun z hz => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr₁' : s - sSup T < r := by exact_mod_cast hr₁
    have hw : max z (s - r) < sSup T := max_lt hz (by linarith)
    obtain ⟨t', ht'T, hlt'⟩ := exists_lt_of_lt_csSup hTne hw
    have hwT : max z (s - r) ∈ T := hTdown _ _ hlt'.le ht'T
    have h₁ : (r : EReal) < φ (max z (s - r)) := hr₂.trans_le (hφ (le_max_left _ _))
    have h₂ : ((s - max z (s - r) : ℝ) : EReal) ≤ (r : EReal) := by
      exact_mod_cast (by linarith [le_max_right z (s - r)] : s - max z (s - r) ≤ r)
    exact absurd (hwT.trans h₂) (not_le.2 h₁)
  · by_contra hcon
    push Not at hcon
    obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr₂' : r < s - sSup T := by exact_mod_cast hr₂
    have hw : sSup T < min z (s - r) := lt_min hz (by linarith)
    have hwT : min z (s - r) ∉ T := fun hmem => absurd (le_csSup hTbdd hmem) (not_le.2 hw)
    have h₁ : φ (min z (s - r)) < (r : EReal) := (hφ (min_le_left _ _)).trans_lt hr₁
    have h₂ : (r : EReal) ≤ ((s - min z (s - r) : ℝ) : EReal) := by
      exact_mod_cast (by linarith [min_le_right z (s - r)] : r ≤ s - min z (s - r))
    exact hwT (h₁.le.trans h₂)

/-- Let $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some
point. Then $\Gamma(\varphi)$ is a maximal monotone relation on $\mathbb{R}$.

A pair $p$ that is comparable with every point of $\Gamma(\varphi)$ equals the point of
$\Gamma(\varphi)$ with the same coordinate sum. -/
theorem isMaximalMonotoneRel_monotoneCurve (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥)
    (ht : φ a ≠ ⊤) : IsMaximalMonotoneRel (innerₗ ℝ) (monotoneCurve φ) := by
  refine ⟨isMonotoneRel_monotoneCurve φ, fun σ hσ hsub p hp => ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_monotoneCurve_sub hφ hb ht (p.1 + p.2)
  have heq : p = ((u, p.1 + p.2 - u) : ℝ × ℝ) := by
    rcases isMonotoneRel_iff_forall_le_or_le.1 hσ p hp _ (hsub hu) with hle | hle <;>
      rw [Prod.le_def] at hle <;>
      exact Prod.ext (by simp only []; linarith [hle.1, hle.2])
        (by simp only []; linarith [hle.1, hle.2])
  rw [heq]
  exact hu

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper convex function. Then the
graph of $\partial f$ is the curve of its own right derivative:
$$\partial f = \Gamma(f'_+).$$

This is the two crossed one-sided limit formulas `ConvexAnalysis.iInf_leftDeriv_Ioi` and
`ConvexAnalysis.iSup_rightDeriv_Iio`, read through `ConvexAnalysis.mem_subgradientRel_iff`. -/
theorem subgradientRel_eq_monotoneCurve_rightDeriv {f : ℝ → EReal} (hf : ClosedProperConvexFn f) :
    subgradientRel (innerₗ ℝ) f = monotoneCurve (rightDeriv f) := by
  ext p
  rw [show p = ((p.1, p.2) : ℝ × ℝ) from rfl, mem_subgradientRel_iff hf.proper,
    mem_monotoneCurve, iSup_rightDeriv_Iio hf, iInf_rightDeriv_Ioi hf]

/-!
### Perturbation of a function at a single point

The region $\Gamma(\varphi)$ depends on $\varphi$ only through its two one-sided limits. So it does
not see the value of $\varphi$ at one point, provided that the new value stays between these limits,
so that monotonicity is kept. This lets a $\varphi$ that is $\pm\infty$ everywhere be replaced by
one that is finite at a point.
-/

section Perturb

variable {φ ψ : ℝ → EReal} {a : ℝ}

/-- Let $\varphi$ be nondecreasing, and let $\psi$ agree with $\varphi$ except at $a$, with
$$\sup_{z < a} \varphi(z) \le \psi(a) \le \inf_{z > a} \varphi(z).$$
Then $\psi$ is nondecreasing. -/
theorem monotone_of_forall_ne_of_le_of_le (hφ : Monotone φ) (heq : ∀ z, z ≠ a → ψ z = φ z)
    (h₁ : (⨆ z ∈ Iio a, φ z) ≤ ψ a) (h₂ : ψ a ≤ ⨅ z ∈ Ioi a, φ z) : Monotone ψ := by
  intro s t hst
  by_cases hs : s = a
  · subst hs
    by_cases ht : t = s
    · rw [ht]
    · rw [heq t ht]
      exact h₂.trans (iInf₂_le t (lt_of_le_of_ne hst (Ne.symm ht)))
  · rw [heq s hs]
    by_cases ht : t = a
    · subst ht
      exact (le_iSup₂ (f := fun z (_ : z ∈ Iio t) => φ z) s
        (lt_of_le_of_ne hst hs)).trans h₁
    · rw [heq t ht]
      exact hφ hst

/-- Let $\varphi$ be nondecreasing, and let $\psi$ agree with $\varphi$ except at $a$, with $\sup_{z
< a} \varphi(z) \le \psi(a) \le \inf_{z > a} \varphi(z)$. Then $\Gamma(\psi) = \Gamma(\varphi)$.

For $x \neq a$, neither $\sup_{z < x}$ nor $\inf_{z > x}$ sees the value at $a$, because
$\psi(a)$ lies between values of $\varphi$ at points strictly between $a$ and $x$, and these
points are in the range of the supremum or infimum. This is what turns
`ConvexAnalysis.subgradientRel_eq_monotoneCurve_rightDeriv` into a statement about a $\varphi$
that is finite at a point. -/
theorem monotoneCurve_eq_of_forall_ne (hφ : Monotone φ) (heq : ∀ z, z ≠ a → ψ z = φ z)
    (h₁ : (⨆ z ∈ Iio a, φ z) ≤ ψ a) (h₂ : ψ a ≤ ⨅ z ∈ Ioi a, φ z) :
    monotoneCurve ψ = monotoneCurve φ := by
  have hsup : ∀ x : ℝ, (⨆ z ∈ Iio x, ψ z) = ⨆ z ∈ Iio x, φ z := by
    intro x
    refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup₂_le fun z hz => ?_)
    · by_cases hza : z = a
      · subst hza
        have hz' : z < x := hz
        have hm₁ : z < (z + x) / 2 := by linarith
        have hm₂ : (z + x) / 2 ∈ Iio x := by simp only [mem_Iio]; linarith
        exact h₂.trans ((iInf₂_le _ hm₁).trans
          (le_iSup₂ (f := fun w (_ : w ∈ Iio x) => φ w) _ hm₂))
      · rw [heq z hza]
        exact le_iSup₂ (f := fun w (_ : w ∈ Iio x) => φ w) z hz
    · by_cases hza : z = a
      · subst hza
        have hz' : z < x := hz
        have hm₁ : z < (z + x) / 2 := by linarith
        have hm₂ : (z + x) / 2 ∈ Iio x := by simp only [mem_Iio]; linarith
        have hmne : (z + x) / 2 ≠ z := by intro h; rw [div_eq_iff] at h <;> linarith
        have hstep : φ z ≤ ⨅ w ∈ Ioi z, φ w := le_iInf₂ fun w hw => hφ (le_of_lt hw)
        refine hstep.trans ((iInf₂_le _ hm₁).trans ?_)
        rw [← heq _ hmne]
        exact le_iSup₂ (f := fun w (_ : w ∈ Iio x) => ψ w) _ hm₂
      · rw [← heq z hza]
        exact le_iSup₂ (f := fun w (_ : w ∈ Iio x) => ψ w) z hz
  have hinf : ∀ x : ℝ, (⨅ z ∈ Ioi x, ψ z) = ⨅ z ∈ Ioi x, φ z := by
    intro x
    refine le_antisymm (le_iInf₂ fun z hz => ?_) (le_iInf₂ fun z hz => ?_)
    · by_cases hza : z = a
      · subst hza
        have hz' : x < z := hz
        have hm₁ : (x + z) / 2 < z := by linarith
        have hm₂ : (x + z) / 2 ∈ Ioi x := by simp only [mem_Ioi]; linarith
        have hmne : (x + z) / 2 ≠ z := by intro h; rw [div_eq_iff] at h <;> linarith
        refine (iInf₂_le _ hm₂).trans ?_
        rw [heq _ hmne]
        exact hφ hm₁.le
      · rw [← heq z hza]
        exact iInf₂_le z hz
    · by_cases hza : z = a
      · subst hza
        have hz' : x < z := hz
        have hm₁ : (x + z) / 2 < z := by linarith
        have hm₂ : (x + z) / 2 ∈ Ioi x := by simp only [mem_Ioi]; linarith
        exact (iInf₂_le _ hm₂).trans
          ((le_iSup₂ (f := fun w (_ : w ∈ Iio z) => φ w) _ hm₁).trans h₁)
      · rw [heq z hza]
        exact iInf₂_le z hz
  ext p
  rw [show p = ((p.1, p.2) : ℝ × ℝ) from rfl, mem_monotoneCurve, mem_monotoneCurve,
    hsup p.1, hinf p.1]

/-- Let $f \colon \mathbb{R} \to [-\infty, +\infty]$ be a closed proper convex function. Then there
is a nondecreasing $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$, finite at some point,
with
$$\partial f = \Gamma(\varphi).$$
This is the passage from the order-theoretic characterization of a complete non-decreasing curve
back to its usual definition.

`ConvexAnalysis.subgradientRel_eq_monotoneCurve_rightDeriv` gives $\partial f = \Gamma(f'_+)$
with $f'_+$ nondecreasing, so only finiteness at a point is missing. $f'_+$ is finite on
$\operatorname{int}(\operatorname{dom} f)$. The case that this does not cover is
$\operatorname{dom} f = \{a\}$, a single point. There $f'_+$ is replaced at $a$ by a
subgradient, and the curve does not change. -/
theorem exists_monotone_ne_bot_ne_top_monotoneCurve_eq {f : ℝ → EReal}
    (hf : ClosedProperConvexFn f) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧
      subgradientRel (innerₗ ℝ) f = monotoneCurve φ := by
  obtain ⟨a, ha⟩ := Convex.relint_nonempty hf.convex.convex_convexDom hf.proper.convexDom_nonempty
  obtain ⟨y₀, hy₀⟩ :=
    subdifferential_nonempty_of_mem_relint_convexDom (B := innerₗ ℝ) hf.convex hf.proper ha
  have hmem : ((a, y₀) : ℝ × ℝ) ∈ monotoneCurve (rightDeriv f) := by
    rw [← subgradientRel_eq_monotoneCurve_rightDeriv hf]
    exact hy₀
  rw [mem_monotoneCurve] at hmem
  have hval : Function.update (rightDeriv f) a ((y₀ : ℝ) : EReal) a = ((y₀ : ℝ) : EReal) :=
    Function.update_self _ _ _
  have hoff : ∀ z, z ≠ a → Function.update (rightDeriv f) a ((y₀ : ℝ) : EReal) z = rightDeriv f z :=
    fun z hz => Function.update_of_ne hz _ _
  have h₁ : (⨆ z ∈ Iio a, rightDeriv f z)
      ≤ Function.update (rightDeriv f) a ((y₀ : ℝ) : EReal) a := by rw [hval]; exact hmem.1
  have h₂ : Function.update (rightDeriv f) a ((y₀ : ℝ) : EReal) a
      ≤ ⨅ z ∈ Ioi a, rightDeriv f z := by rw [hval]; exact hmem.2
  refine ⟨Function.update (rightDeriv f) a ((y₀ : ℝ) : EReal),
    monotone_of_forall_ne_of_le_of_le (monotone_rightDeriv hf.convex hf.proper) hoff h₁ h₂,
    ⟨a, by rw [hval]; exact EReal.coe_ne_bot _,
      by rw [hval]; exact EReal.coe_ne_top _⟩, ?_⟩
  rw [subgradientRel_eq_monotoneCurve_rightDeriv hf]
  exact (monotoneCurve_eq_of_forall_ne (monotone_rightDeriv hf.convex hf.proper) hoff h₁ h₂).symm

end Perturb

end Curve

/-! ### The convex primitive -/

section Primitive

variable {φ : ℝ → EReal}

/-- Let $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some
point. Then there is a closed proper convex function
$f \colon \mathbb{R} \to [-\infty, +\infty]$ whose one-sided derivatives are the one-sided
limits of $\varphi$:
$$f'_-(x) = \sup_{z < x} \varphi(z), \qquad f'_+(x) = \inf_{z > x} \varphi(z) \qquad \text{for
  every } x \in \mathbb{R}.$$

The maximality of $\Gamma(\varphi)$ gives an $f$ with $\partial f = \Gamma(\varphi)$. At a fixed
$x$ this says that the intervals $[\varphi_-(x), \varphi_+(x)]$ and $[f'_-(x), f'_+(x)]$ contain
the same real numbers, so they have the same endpoints if one of them contains a real number. If
neither does, both are $\{-\infty\}$ or both are $\{+\infty\}$, and a comparison across the
point where $\varphi$ is finite decides which. -/
theorem exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq (hφ : Monotone φ) {a : ℝ}
    (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧
      (∀ x, leftDeriv f x = ⨆ z ∈ Iio x, φ z) ∧ (∀ x, rightDeriv f x = ⨅ z ∈ Ioi x, φ z) := by
  obtain ⟨f, hf, hΓ⟩ := isMaximalMonotoneRel_iff_exists_closedProperConvexFn.1
    (isMaximalMonotoneRel_monotoneCurve hφ hb ht)
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  have hiff : ∀ x y : ℝ, ((⨆ z ∈ Iio x, φ z) ≤ (y : EReal) ∧ (y : EReal) ≤ ⨅ z ∈ Ioi x, φ z) ↔
      (leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x) := fun x y => by
    rw [← mem_subgradientRel_iff hf.proper, ← hΓ]
    exact Iff.rfl
  have hsuple : ∀ x : ℝ, (⨆ z ∈ Iio x, φ z) ≤ φ x := fun x => iSup₂_le fun _ hz => hφ hz.le
  have hleinf : ∀ x : ℝ, φ x ≤ ⨅ z ∈ Ioi x, φ z := fun x => le_iInf₂ fun _ hz => hφ hz.le
  have hφle : ∀ x : ℝ, (⨆ z ∈ Iio x, φ z) ≤ ⨅ z ∈ Ioi x, φ z :=
    fun x => (hsuple x).trans (hleinf x)
  have hfle : ∀ x : ℝ, leftDeriv f x ≤ rightDeriv f x :=
    fun x => leftDeriv_le_rightDeriv hf.convex hf.proper x
  -- The fibre over `a` is non-empty, so both endpoints are pinned there.
  obtain ⟨hLa, hRa⟩ := eq_and_eq_of_forall_coe_mem_iff
    (A₁ := ⨆ z ∈ Iio a, φ z) (B₁ := ⨅ z ∈ Ioi a, φ z)
    ⟨c, hc ▸ hsuple a, hc ▸ hleinf a⟩ (hiff a)
  have hLalt : leftDeriv f a < ⊤ :=
    lt_of_le_of_lt (hLa ▸ (hc ▸ hsuple a : (⨆ z ∈ Iio a, φ z) ≤ (c : EReal)))
      (EReal.coe_lt_top c)
  have hRagt : ⊥ < rightDeriv f a :=
    lt_of_lt_of_le (EReal.bot_lt_coe c) (hRa ▸ (hc ▸ hleinf a : (c : EReal) ≤ _))
  suffices key : ∀ x : ℝ,
      leftDeriv f x = ⨆ z ∈ Iio x, φ z ∧ rightDeriv f x = ⨅ z ∈ Ioi x, φ z from
    ⟨f, hf, fun x => (key x).1, fun x => (key x).2⟩
  intro x
  by_cases hex : ∃ y : ℝ, (⨆ z ∈ Iio x, φ z) ≤ (y : EReal) ∧ (y : EReal) ≤ ⨅ z ∈ Ioi x, φ z
  · obtain ⟨hL, hR⟩ := eq_and_eq_of_forall_coe_mem_iff hex (hiff x)
    exact ⟨hL.symm, hR.symm⟩
  have hex₁ : ∀ y : ℝ, ¬((⨆ z ∈ Iio x, φ z) ≤ (y : EReal) ∧ (y : EReal) ≤ ⨅ z ∈ Ioi x, φ z) :=
    fun y hy => hex ⟨y, hy⟩
  have hex₂ : ∀ y : ℝ, ¬(leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x) :=
    fun y hy => hex₁ y ((hiff x y).2 hy)
  rcases eq_bot_or_eq_top_of_forall_not_coe_mem (hφle x) hex₁ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- `φ` is `-∞` at and below `x`, so `x < a` and `f'₊(x) ≤ f'₋(a) < +∞`.
    have hφx : φ x = ⊥ := le_bot_iff.1 (h₂ ▸ hleinf x)
    have hxa : x < a := by
      by_contra hcon
      exact hb (le_bot_iff.1 (hφx ▸ hφ (not_lt.1 hcon)))
    rcases eq_bot_or_eq_top_of_forall_not_coe_mem (hfle x) hex₂ with ⟨g₁, g₂⟩ | ⟨-, g₂⟩
    · exact ⟨g₁.trans h₁.symm, g₂.trans h₂.symm⟩
    · exact absurd (lt_of_le_of_lt (g₂ ▸ rightDeriv_le_leftDeriv hf.proper hxa) hLalt)
        (lt_irrefl ⊤)
  · -- `φ` is `+∞` at and above `x`, so `a < x` and `-∞ < f'₊(a) ≤ f'₋(x)`.
    have hφx : φ x = ⊤ := top_le_iff.1 (h₁ ▸ hsuple x)
    have hax : a < x := by
      by_contra hcon
      exact ht (top_le_iff.1 (hφx ▸ hφ (not_lt.1 hcon)))
    rcases eq_bot_or_eq_top_of_forall_not_coe_mem (hfle x) hex₂ with ⟨g₁, -⟩ | ⟨g₁, g₂⟩
    · exact absurd (lt_of_lt_of_le hRagt (g₁ ▸ rightDeriv_le_leftDeriv hf.proper hax))
        (lt_irrefl ⊥)
    · exact ⟨g₁.trans h₁.symm, g₂.trans h₂.symm⟩

/-- Let $\varphi \colon \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some
point. Then there is a closed proper convex function
$f \colon \mathbb{R} \to [-\infty, +\infty]$ with
$$f'_-(x) \le \varphi(x) \le f'_+(x) \qquad \text{for every } x \in \mathbb{R},$$
and every closed proper convex $g$ with $g'_- \le \varphi \le g'_+$ is $g = f + \alpha$ for some
$\alpha \in \mathbb{R}$. This is Theorem 24.2 of [rockafellar1970convex].

Existence is `ConvexAnalysis.exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq`, and
uniqueness is `ConvexAnalysis.exists_eq_add_coe_of_le_le`. -/
theorem exists_closedProperConvexFn_forall_le_le (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥)
    (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ (∀ x, leftDeriv f x ≤ φ x) ∧
      (∀ x, φ x ≤ rightDeriv f x) ∧
      ∀ g : ℝ → EReal, ClosedProperConvexFn g → (∀ x, leftDeriv g x ≤ φ x) →
        (∀ x, φ x ≤ rightDeriv g x) → ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  obtain ⟨f, hf, hL, hR⟩ := exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq hφ hb ht
  have hf₁ : ∀ x, leftDeriv f x ≤ φ x := fun x => by
    rw [hL x]; exact iSup₂_le fun _ hz => hφ hz.le
  have hf₂ : ∀ x, φ x ≤ rightDeriv f x := fun x => by
    rw [hR x]; exact le_iInf₂ fun _ hz => hφ hz.le
  exact ⟨f, hf, hf₁, hf₂, fun g hg hg₁ hg₂ => exists_eq_add_coe_of_le_le hf hg hf₁ hf₂ hg₁ hg₂⟩

end Primitive

end ConvexAnalysis
