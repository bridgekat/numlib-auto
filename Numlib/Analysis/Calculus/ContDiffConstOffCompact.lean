/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.ContDiff.Operations`, beside the closure properties of
`ContDiff` and `HasCompactSupport`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Smooth functions constant off a compact set

Let $E$ be a real normed space and $n \in \mathbb{N}$. A function $c : E \to \mathbb{R}$ is a
**multiplier of class $C^n$** here if $c$ is $C^n$ on $E$ and agrees with a constant off a compact
set. The multipliers include the $C^n$ functions with compact support and the constants. They are
closed under sums, products, scalar multiples and finite sums, under partial derivatives (with the
order lowered by one), and under inversion of a member that is bounded below by a positive constant.
Every multiplier is bounded, and so is its derivative. Consequently every derivative of every order
of a multiplier is bounded.

This is what makes multipliers act on the Sobolev spaces $H^k$ in the higher-order regularity theory
of elliptic equations ([brezis2011functional], §9.6). An example is the extended coefficient
$\chi a + (1 - \chi) \delta$ in the proof of Theorem 9.25 of [brezis2011functional].

## Main definitions

* `IsContDiffConstOffCompact`: $c$ is $C^n$ and agrees with a constant off a compact set.

## Main results

* `IsContDiffConstOffCompact.of_hasCompactSupport`, `IsContDiffConstOffCompact.const`: $C^n$
  functions with compact support and constants are multipliers.
* `IsContDiffConstOffCompact.add`, `IsContDiffConstOffCompact.mul`,
  `IsContDiffConstOffCompact.finset_sum`: sums, products and finite sums of multipliers are
  multipliers.
* `IsContDiffConstOffCompact.fderiv_apply`: a partial derivative of a multiplier of class $C^{n+1}$
  is a multiplier of class $C^n$.
* `IsContDiffConstOffCompact.inv`: $1/c$ is a multiplier if $c$ is one and $c \ge \alpha > 0$.
* `IsContDiffConstOffCompact.exists_bound`, `IsContDiffConstOffCompact.exists_bound_fderiv`: a
  multiplier and its derivative are bounded.
* `HasCompactSupport.iteratedDeriv`: the iterated derivatives of a compactly supported function of
  one variable have compact support.
-/

open scoped ContDiff

section ConstOffCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $E$ be a real normed space and $n \in \mathbb{N}$. A function $c : E \to \mathbb{R}$ is a
**multiplier of class $C^n$** if $c$ is $C^n$ on $E$ and there is a constant
$\kappa \in \mathbb{R}$ such that $c - \kappa$ has compact support.

This is the class of multipliers of the higher-order regularity theory. It contains the smooth
compactly supported functions, the constants and the extended coefficients
$\chi a + (1 - \chi) \delta$. It is closed under partial derivatives, products and inversion of
positive members, so that every derivative of every order of a member is bounded. -/
structure IsContDiffConstOffCompact (n : ℕ) (c : E → ℝ) : Prop where
  /-- A multiplier is $C^n$ on $E$. -/
  contDiff : ContDiff ℝ n c
  /-- There is a constant $\kappa$ such that $c - \kappa$ has compact support. -/
  exists_hasCompactSupport_sub : ∃ κ : ℝ, HasCompactSupport fun x ↦ c x - κ

namespace IsContDiffConstOffCompact

variable {n : ℕ} {c : E → ℝ}

/-- A $C^n$ function $c : E \to \mathbb{R}$ with compact support is a multiplier of class $C^n$. -/
theorem of_hasCompactSupport (hc : ContDiff ℝ n c) (hcs : HasCompactSupport c) :
    IsContDiffConstOffCompact n c :=
  ⟨hc, 0, by simpa using hcs⟩

/-- For every $\kappa \in \mathbb{R}$, the constant function $\kappa$ is a multiplier of class
$C^n$. -/
theorem const (κ : ℝ) : IsContDiffConstOffCompact n fun _ : E ↦ κ :=
  ⟨contDiff_const, κ, by simp [HasCompactSupport, tsupport]⟩

/-- A multiplier of class $C^n$ is a multiplier of class $C^m$ for every $m \le n$. -/
theorem of_le {m : ℕ} (h : IsContDiffConstOffCompact n c) (hmn : m ≤ n) :
    IsContDiffConstOffCompact m c :=
  ⟨h.contDiff.of_le (by exact_mod_cast hmn), h.exists_hasCompactSupport_sub⟩

/-- A multiplier is continuous. -/
theorem continuous (h : IsContDiffConstOffCompact n c) : Continuous c := h.contDiff.continuous

/-- A multiplier $c$ is bounded: there is $C$ with $|c(x)| \le C$ for all $x \in E$. -/
theorem exists_bound (h : IsContDiffConstOffCompact n c) : ∃ C, ∀ x, |c x| ≤ C := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨C, hC⟩ := hκ.exists_bound_of_continuous (h.continuous.sub continuous_const)
  refine ⟨C + |κ|, fun x ↦ ?_⟩
  have := hC x
  rw [Real.norm_eq_abs] at this
  calc |c x| = |(c x - κ) + κ| := by ring_nf
    _ ≤ |c x - κ| + |κ| := abs_add_le _ _
    _ ≤ C + |κ| := by linarith

/-- The sum $c + c'$ of two multipliers of class $C^n$ is a multiplier of class $C^n$. -/
theorem add {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x + c' x := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨κ', hκ'⟩ := h'.exists_hasCompactSupport_sub
  refine ⟨h.contDiff.add h'.contDiff, κ + κ', ?_⟩
  have e : (fun x ↦ c x + c' x - (κ + κ')) = (fun x ↦ c x - κ) + fun x ↦ c' x - κ' := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact hκ.add hκ'

/-- The product $c c'$ of two multipliers of class $C^n$ is a multiplier of class $C^n$. -/
theorem mul {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x * c' x := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨κ', hκ'⟩ := h'.exists_hasCompactSupport_sub
  refine ⟨h.contDiff.mul h'.contDiff, κ * κ', ?_⟩
  have h1 : HasCompactSupport fun x ↦ (c x - κ) * c' x := hκ.mul_right
  have h2 : HasCompactSupport fun x ↦ κ * (c' x - κ') := hκ'.mul_left
  have e : (fun x ↦ c x * c' x - κ * κ')
      = (fun x ↦ (c x - κ) * c' x) + fun x ↦ κ * (c' x - κ') := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h1.add h2

/-- For a multiplier $c$ of class $C^n$ and $r \in \mathbb{R}$, the function $r c$ is a multiplier
of class $C^n$. -/
theorem const_mul (h : IsContDiffConstOffCompact n c) (r : ℝ) :
    IsContDiffConstOffCompact n fun x ↦ r * c x :=
  (const r).mul h

/-- The negative $-c$ of a multiplier of class $C^n$ is a multiplier of class $C^n$. -/
theorem neg (h : IsContDiffConstOffCompact n c) : IsContDiffConstOffCompact n fun x ↦ -c x := by
  have := h.const_mul (-1)
  simpa using this

/-- The difference $c - c'$ of two multipliers of class $C^n$ is a multiplier of class $C^n$. -/
theorem sub {c' : E → ℝ} (h : IsContDiffConstOffCompact n c)
    (h' : IsContDiffConstOffCompact n c') : IsContDiffConstOffCompact n fun x ↦ c x - c' x := by
  have := h.add h'.neg
  simpa [sub_eq_add_neg] using this

/-- Let $s$ be a finite set and let $c_i$ be a multiplier of class $C^n$ for every $i \in s$. Then
$\sum_{i \in s} c_i$ is a multiplier of class $C^n$. -/
theorem finset_sum {κ : Type*} (s : Finset κ) {c : κ → E → ℝ}
    (h : ∀ i ∈ s, IsContDiffConstOffCompact n (c i)) :
    IsContDiffConstOffCompact n fun x ↦ ∑ i ∈ s, c i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (E := E) (n := n) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Let $c$ be a multiplier of class $C^{n+1}$ and let $y \in E$. Then the partial derivative
$x \mapsto Dc(x)\, y$ in the direction $y$ is a multiplier of class $C^n$.

Since $c$ is constant off a compact set, the partial derivative vanishes off that set; the
statement records only that it is a multiplier. -/
theorem fderiv_apply (h : IsContDiffConstOffCompact (n + 1) c) (y : E) :
    IsContDiffConstOffCompact n fun x ↦ fderiv ℝ c x y := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  refine of_hasCompactSupport ?_ ?_
  · exact (h.contDiff.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const
  · have := hκ.fderiv_apply (𝕜 := ℝ) y
    have e : (fun x ↦ fderiv ℝ c x y) = fun x ↦ fderiv ℝ (fun x ↦ c x - κ) x y := by
      funext x
      simp only [fderiv_sub_const]
    rw [e]
    exact this

/-- Let $c$ be a multiplier of class $C^n$, and let $\alpha > 0$ with $c(x) \ge \alpha$ for all
$x \in E$. Then $1/c$ is a multiplier of class $C^n$. -/
theorem inv (h : IsContDiffConstOffCompact n c) {α : ℝ} (hα : 0 < α) (hc : ∀ x, α ≤ c x) :
    IsContDiffConstOffCompact n fun x ↦ (c x)⁻¹ := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  have hne : ∀ x, c x ≠ 0 := fun x ↦ (hα.trans_le (hc x)).ne'
  refine ⟨h.contDiff.inv hne, κ⁻¹, ?_⟩
  refine hκ.mono fun x hx ↦ ?_
  simp only [Function.mem_support, ne_eq] at hx ⊢
  intro hcx
  apply hx
  have : c x = κ := by linarith
  rw [this, sub_self]

/-- Let $c$ be a multiplier of class $C^{n+1}$. Then its derivative is bounded: there is $C$ with
$\|Dc(x)\| \le C$ for all $x \in E$, in the operator norm. -/
theorem exists_bound_fderiv (h : IsContDiffConstOffCompact (n + 1) c) :
    ∃ C, ∀ x, ‖fderiv ℝ c x‖ ≤ C := by
  obtain ⟨κ, hκ⟩ := h.exists_hasCompactSupport_sub
  obtain ⟨C, hC⟩ := (hκ.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((h.contDiff.sub contDiff_const).continuous_fderiv (by simp))
  refine ⟨C, fun x ↦ ?_⟩
  have := hC x
  rwa [fderiv_sub_const] at this

end IsContDiffConstOffCompact

/-- Let $n \in \mathbb{N} \cup \{\infty, \omega\}$, let $Q \subseteq E$ be open, let
$\chi : E \to \mathbb{R}$ be $C^n$ on $E$ with the closure of its support in $Q$, and let
$f : E \to \mathbb{R}$ be $C^n$ on $Q$. Then $\chi f$ is $C^n$ on all of $E$.

The order $n$ is a term of `WithTop ℕ∞`, and the closed support is `tsupport χ`. -/
theorem ContDiff.mul_contDiffOn_of_tsupport_subset {n : WithTop ℕ∞} {χ f : E → ℝ}
    (hχ : ContDiff ℝ n χ) {Q : Set E} (hQ : IsOpen Q) (hf : ContDiffOn ℝ n f Q)
    (hχQ : tsupport χ ⊆ Q) : ContDiff ℝ n fun y ↦ χ y * f y := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ Q
  · exact hχ.contDiffAt.mul ((hf y hy).contDiffAt (hQ.mem_nhds hy))
  · have hy' : y ∉ tsupport χ := fun h ↦ hy (hχQ h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

end ConstOffCompact

/-! ### Iterated derivatives of compactly supported functions of one variable -/

/-- Let $f : \mathbb{R} \to \mathbb{R}$ have compact support. Then for every $k \in \mathbb{N}$, the
$k$-th derivative $f^{(k)}$ has compact support.

The derivative is `iteratedDeriv k f`, which is defined for every $f$; no differentiability is
assumed. -/
theorem HasCompactSupport.iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
