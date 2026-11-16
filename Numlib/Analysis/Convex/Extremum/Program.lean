/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Helly
import Numlib.Analysis.Convex.Extremum.Minimum

/-!
# Ordinary convex programs and Lagrange multipliers

An **ordinary convex program** minimizes a proper convex function
$f_0 \colon E \to (-\infty, +\infty]$ over $C = \operatorname{dom} f_0$, subject to finitely many
convex inequality constraints $f_i(x) \le 0$, $i \in \iota$, and finitely many affine constraints
$b_j(x) \le 0$, $j \in \kappa$. The **Lagrangian** at multipliers $(\lambda, \mu)$ is
$$L(x) = f_0(x) + \sum_i \lambda_i f_i(x) + \sum_j \mu_j b_j(x),$$
and $(\lambda, \mu)$ is a **Kuhn–Tucker vector** if $\lambda, \mu \ge 0$ and $\inf_x L(x)$ is finite
and equal to the optimal value of the program. The main result is the existence of Kuhn–Tucker
vectors under **Slater's condition** ([rockafellar1970convex], Theorem 28.2): if the optimal value
is not $-\infty$ and some feasible point of $\operatorname{ri} C$ satisfies every constraint
$f_i(x) \le 0$ strictly, then a Kuhn–Tucker vector exists. The module also proves the sufficiency
half of the Kuhn–Tucker conditions ([rockafellar1970convex], Theorem 28.3). The presentation follows
[rockafellar1970convex], §28.

The two families of constraints are separated by their role. The constraints indexed by $\iota$ are
those of which Slater's condition asks a strict inequality, that is, the constraints with $f_i$ not
affine. They are convex functions with values in $[-\infty, +\infty]$. The constraints indexed by
$\kappa$ are affine maps $E \to \mathbb{R}$, of which only a weak inequality is asked. The theorem
of the alternative is stated for this split, so the existence theorem applies it directly, and the
case with only affine constraints is $\iota = \emptyset$.

## Main definitions

* `ConvexAnalysis.feasibleSet`: the set of points that satisfy all constraints.
* `ConvexAnalysis.programLagrangian`: the Lagrangian
  $f_0 + \sum_i \lambda_i f_i + \sum_j \mu_j b_j$.
* `ConvexAnalysis.optimalValue`: the infimum of $f_0$ over the feasible set.
* `ConvexAnalysis.IsKuhnTuckerVector`: nonnegative multipliers for which the infimum of the
  Lagrangian is finite and equal to the optimal value.
* `ConvexAnalysis.IsLagrangeSummand`: a summand $\lambda g$ of a Lagrange function that is either
  convex with $\lambda \ge 0$ or affine with $\lambda$ arbitrary.

## Main results

* `ConvexAnalysis.exists_isKuhnTuckerVector_of_slater`: under Slater's condition, a Kuhn–Tucker
  vector exists.
* `ConvexAnalysis.exists_isKuhnTuckerVector_of_affine`: with only affine constraints, a feasible
  point in $\operatorname{ri} C$ suffices.
* `ConvexAnalysis.exists_isKuhnTuckerVector_of_mem_convexDom`: if every constraint holds strictly at
  some point of $C$, this point need not lie in $\operatorname{ri} C$.
* `ConvexAnalysis.exists_multipliers_of_slater_eq`: the same existence for affine equality
  constraints, whose multipliers have arbitrary sign.
* `ConvexAnalysis.subdifferential_add_sum_coe_mul`: the subdifferential of $h = f_0 + \lambda_1
  f_1 + \dots + \lambda_m f_m$ is $\partial f_0 + \sum_{\lambda_i \neq 0} \lambda_i \partial f_i$.
* `ConvexAnalysis.mem_argmin_add_sum_coe_mul_of_zero_mem`: if $0 \in \partial f_0(x) +
  \sum_{\lambda_i \neq 0} \lambda_i \partial f_i(x)$, then $x$ minimizes $h$.
* `ConvexAnalysis.isKuhnTuckerVector_of_kuhnTucker`: the Kuhn–Tucker conditions at $x$ make
  $(\lambda, \mu)$ a Kuhn–Tucker vector and $x$ an optimal solution.

## Implementation notes

* The existence theorems assume $\operatorname{dom} f_0 \subseteq \operatorname{dom} f_i$ for every
  $i$. This makes every $f_i$ finite on $C$, so the inequality for the multipliers is an inequality
  between real numbers, which can be divided by the multiplier of the objective.
* Products in $[-\infty, +\infty]$ follow Mathlib's convention $0 \cdot (\pm\infty) = 0$.
-/

namespace ConvexAnalysis

open Set Filter Topology

section Defs

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The **feasible set** of the constraint system $f_i(x) \le 0$ for all $i \in \iota$ and
$b_j(x) \le 0$ for all $j \in \kappa$, where each $f_i \colon E \to [-\infty, +\infty]$ and each
$b_j \colon E \to \mathbb{R}$ is affine. -/
def feasibleSet (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0}

omit [Fintype ι] [Fintype κ] in
/-- A point $x$ is feasible if and only if $f_i(x) \le 0$ for all $i$ and $b_j(x) \le 0$ for all
$j$. -/
@[simp] theorem mem_feasibleSet {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E} :
    x ∈ feasibleSet f b ↔ (∀ i, f i x ≤ 0) ∧ ∀ j, b j x ≤ 0 := Iff.rfl

/-- The **Lagrangian** of an ordinary convex program at the multipliers
$\lambda \in \mathbb{R}^\iota$ and $\mu \in \mathbb{R}^\kappa$:
$$L(x) = f_0(x) + \sum_{i \in \iota} \lambda_i f_i(x) + \sum_{j \in \kappa} \mu_j b_j(x).$$

The sum over $i$ is taken in $[-\infty, +\infty]$, and the affine sum is a real number. The
Lagrangian of a bifunction, defined through perturbations, is `ConvexAnalysis.lagrangian`. -/
noncomputable def programLagrangian (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : E → EReal :=
  fun x => f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal)

/-- The value of the Lagrangian at $x$ is $f_0(x) + \sum_i \lambda_i f_i(x) + \sum_j \mu_j b_j(x)$.
-/
theorem programLagrangian_apply (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) (x : E) :
    programLagrangian f₀ f b l μ x
      = f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * b j x : ℝ) : EReal) := rfl

/-- The **optimal value** of the program: the infimum of $f_0$ over the feasible set,
$$\inf \{ f_0(x) \mid f_i(x) \le 0 \text{ for all } i,\ b_j(x) \le 0 \text{ for all } j \}.$$
It is $+\infty$ when the feasible set is empty. -/
noncomputable def optimalValue (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ) : EReal :=
  ⨅ x ∈ feasibleSet f b, f₀ x

omit [Fintype ι] [Fintype κ] in
/-- The optimal value is at most $f_0(x)$ for every feasible point $x$. -/
theorem optimalValue_le {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {x : E}
    (hx : x ∈ feasibleSet f b) : optimalValue f₀ f b ≤ f₀ x :=
  iInf₂_le x hx

/-- A pair of multipliers $(\lambda, \mu)$ is a **Kuhn–Tucker vector** of the program if
$\lambda_i \ge 0$ for all $i$, $\mu_j \ge 0$ for all $j$, and the infimum of the Lagrangian over
$E$ is finite and equal to the optimal value:
$$\inf_{x \in E} \Bigl(f_0(x) + \sum_i \lambda_i f_i(x) + \sum_j \mu_j b_j(x)\Bigr) = \inf \{
  f_0(x) \mid x \text{ feasible} \} \in \mathbb{R}.$$

This is the direct definition. It is not the equivalent inequality
$p(u) + \langle \lambda, u \rangle \ge p(0)$ for the perturbation function $p$. -/
structure IsKuhnTuckerVector (f₀ : E → EReal) (f : ι → E → EReal) (b : κ → E →ᵃ[ℝ] ℝ)
    (l : ι → ℝ) (μ : κ → ℝ) : Prop where
  /-- The multipliers of the convex constraints are nonnegative. -/
  nonneg : ∀ i, 0 ≤ l i
  /-- The multipliers of the affine inequality constraints are nonnegative. -/
  nonneg_affine : ∀ j, 0 ≤ μ j
  /-- The infimum of the Lagrangian is not $-\infty$. -/
  ne_bot : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊥
  /-- The infimum of the Lagrangian is not $+\infty$. -/
  ne_top : (⨅ x, programLagrangian f₀ f b l μ x) ≠ ⊤
  /-- The infimum of the Lagrangian is the optimal value of the program. -/
  iInf_eq : (⨅ x, programLagrangian f₀ f b l μ x) = optimalValue f₀ f b

end Defs

section Elementary

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {l : ι → ℝ} {μ : κ → ℝ}

/-- If $c \ge 0$ is real and $z \le 0$ in $[-\infty, +\infty]$, then $cz \le 0$. The coefficient
$c = 0$ is allowed because of the convention $0 \cdot (\pm\infty) = 0$. -/
theorem coe_mul_nonpos {c : ℝ} (hc : 0 ≤ c) {z : EReal} (hz : z ≤ 0) : (c : EReal) * z ≤ 0 := by
  rcases eq_or_lt_of_le hc with h | h
  · rw [← h]; simp
  · calc (c : EReal) * z ≤ (c : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left hz ?_
          exact_mod_cast hc
      _ = 0 := by simp

/-- Let $\lambda_i \ge 0$ for all $i$ in a finite index set, let $v_i < 0$ in $[-\infty, +\infty]$
for all $i$, and let $\lambda_{i_0} \neq 0$ for some $i_0$. Then $\sum_i \lambda_i v_i < 0$.
This excludes a vanishing multiplier of the objective. -/
theorem sum_coe_mul_neg (hl : ∀ i, 0 ≤ l i) {v : ι → EReal} (hv : ∀ i, v i < 0) {i₀ : ι}
    (hi₀ : l i₀ ≠ 0) : (∑ i, (l i : EReal) * v i) < 0 := by
  classical
  have hpos : 0 < l i₀ := lt_of_le_of_ne (hl i₀) (Ne.symm hi₀)
  have hterm : (l i₀ : EReal) * v i₀ < 0 := by
    have hlt : ¬ ((l i₀ : EReal) * 0 ≤ (l i₀ : EReal) * v i₀) := by
      rw [EReal.coe_mul_le_coe_mul_iff hpos]
      exact not_le.2 (hv i₀)
    simpa using not_le.1 hlt
  have hrest : ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hv i).le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  calc (l i₀ : EReal) * v i₀ + ∑ i ∈ Finset.univ.erase i₀, (l i : EReal) * v i
      ≤ (l i₀ : EReal) * v i₀ + 0 := add_le_add (le_refl _) hrest
    _ = (l i₀ : EReal) * v i₀ := add_zero _
    _ < 0 := hterm

/-- If $\lambda, \mu \ge 0$ and $x$ is feasible, then $L(x) \le f_0(x)$, because every constraint
term is nonpositive. -/
theorem programLagrangian_le_of_mem_feasibleSet (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j)
    {x : E} (hx : x ∈ feasibleSet f b) : programLagrangian f₀ f b l μ x ≤ f₀ x := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≤ 0 :=
    Finset.sum_nonpos fun i _ => coe_mul_nonpos (hl i) (hx.1 i)
  have haff : ((∑ j, μ j * b j x : ℝ) : EReal) ≤ 0 := by
    have h : (∑ j, μ j * b j x) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμ j) (hx.2 j)
    exact_mod_cast h
  calc programLagrangian f₀ f b l μ x
      ≤ f₀ x + (∑ i, (l i : EReal) * f i x) + 0 := add_le_add (le_refl _) haff
    _ = f₀ x + (∑ i, (l i : EReal) * f i x) := add_zero _
    _ ≤ f₀ x + 0 := add_le_add (le_refl _) hsum
    _ = f₀ x := add_zero _

/-- If $\lambda \ge 0$, no $f_i$ takes the value $-\infty$, and $f_0(x) = +\infty$, then
$L(x) = +\infty$. Thus the Lagrangian is $+\infty$ off $\operatorname{dom} f_0$. -/
theorem programLagrangian_eq_top (hl : ∀ i, 0 ≤ l i) (hbot : ∀ i x, f i x ≠ ⊥) {x : E}
    (hx : f₀ x = ⊤) : programLagrangian f₀ f b l μ x = ⊤ := by
  have hsum : (∑ i, (l i : EReal) * f i x) ≠ ⊥ :=
    EReal.sum_ne_bot fun i _ => EReal.coe_mul_ne_bot (hl i) (hbot i x)
  rw [programLagrangian_apply, hx, EReal.top_add_of_ne_bot hsum,
    EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-- If $f_0(x) = r_0$ and $f_i(x) = r_i$ are real, then $L(x)$ is the real number $r_0 + \sum_i
\lambda_i r_i + \sum_j \mu_j b_j(x)$. -/
theorem programLagrangian_eq_coe {x : E} {r₀ : ℝ} (h₀ : f₀ x = (r₀ : EReal)) {r : ι → ℝ}
    (hr : ∀ i, f i x = (r i : EReal)) :
    programLagrangian f₀ f b l μ x
      = ((r₀ + (∑ i, l i * r i) + ∑ j, μ j * b j x : ℝ) : EReal) := by
  have hterm : ∀ i, (l i : EReal) * f i x = ((l i * r i : ℝ) : EReal) := fun i => by
    rw [hr i, ← EReal.coe_mul]
  rw [programLagrangian_apply, h₀, Finset.sum_congr rfl (fun i _ => hterm i),
    ← EReal.coe_sum, ← EReal.coe_add, ← EReal.coe_add]

end Elementary

section Slater

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ}

/-- **Existence of Kuhn–Tucker vectors under Slater's condition.** Let $E$ be a finite-dimensional
real normed space, let $f_0$ and $f_i$, $i \in \iota$, be proper convex functions from $E$ to
$[-\infty, +\infty]$, and let $b_j \colon E \to \mathbb{R}$, $j \in \kappa$, be affine, with
$\iota$ and $\kappa$ finite. Let $C = \operatorname{dom} f_0$, and assume that
$C \subseteq \operatorname{dom} f_i$ for every $i$. Suppose that the optimal value is not
$-\infty$, and that there is $x \in \operatorname{ri} C$ with
$$f_i(x) < 0 \text{ for all } i \quad \text{and} \quad b_j(x) \le 0 \text{ for all } j.$$
Then there is a Kuhn–Tucker vector $(\lambda, \mu)$.

This is Theorem 28.2 of [rockafellar1970convex]. The proof applies the theorem of the
alternative of `Numlib.Analysis.Convex.Helly` to the system $f_0(x) - \alpha < 0$, $f_i(x) < 0$,
$b_j(x) \le 0$, where $\alpha$ is the optimal value. -/
theorem exists_isKuhnTuckerVector_of_slater (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, ProperConvex (f i))
        (hsub : ∀ i, convexDom f₀ ⊆ convexDom (f i))
    (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ ri (convexDom f₀), (∀ i, f i x < 0) ∧ ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hzri, hzf, hzb⟩ := hslater
  have hzC : z ∈ convexDom f₀ := intrinsicInterior_subset hzri
  have hzfeas : z ∈ feasibleSet f b := ⟨fun i => (hzf i).le, hzb⟩
  -- the optimal value is a real number
  have htop : optimalValue f₀ f b < ⊤ :=
    lt_of_le_of_lt (optimalValue_le hzfeas) (mem_convexDom.1 hzC)
  obtain ⟨α, hα⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot htop
  -- the shifted system, indexed by `Option ι`
  set g : Option ι → E → EReal := fun i' x => i'.elim (f₀ x + ((-α : ℝ) : EReal)) (fun i => f i x)
    with hgdef
  have hgnone : g none = fun x => f₀ x + ((-α : ℝ) : EReal) := rfl
  have hgsome : ∀ i, g (some i) = f i := fun _ => rfl
  have hgconv : ∀ i', ConvexFn (g i') := by
    rintro (_ | i)
    · have : ConvexFn (f₀ + fun _ : E => ((-α : ℝ) : EReal)) :=
        hf₀.add (convexFn_const _) hp₀.ne_bot (fun _ => EReal.coe_ne_bot _)
      exact this
    · exact hf i
  have hgproper : ∀ i', ProperConvex (g i') := by
    rintro (_ | i)
    · refine ⟨⟨z, ?_⟩, fun x => ?_⟩
      · exact mem_convexDom.2 (EReal.add_lt_top (mem_convexDom.1 hzC).ne (EReal.coe_ne_top _))
      · exact EReal.add_ne_bot_iff.2 ⟨hp₀.ne_bot x, EReal.coe_ne_bot _⟩
    · exact hp i
  have hgdom : ∀ i', ri (convexDom f₀) ⊆ convexDom (g i') := by
    rintro (_ | i) x hx
    · exact mem_convexDom.2
        (EReal.add_lt_top (mem_convexDom.1 (intrinsicInterior_subset hx)).ne (EReal.coe_ne_top _))
    · exact hsub i (intrinsicInterior_subset hx)
  -- the strict system is unsolvable, so the theorem of the alternative produces multipliers
  have hnoalt : ¬ ∃ x ∈ convexDom f₀, (∀ i', g i' x < 0) ∧ ∀ j, b j x ≤ 0 := by
    rintro ⟨x, _, hxg, hxb⟩
    have hx0 : f₀ x < (α : EReal) := by
      have h : f₀ x + ((-α : ℝ) : EReal) < 0 := hxg none
      rwa [EReal.coe_neg, ← sub_eq_add_neg,
        EReal.sub_lt_iff (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)), zero_add] at h
    have hxfeas : x ∈ feasibleSet f b := ⟨fun i => (hxg (some i)).le, hxb⟩
    have hle : (α : EReal) ≤ f₀ x := hα ▸ optimalValue_le (f₀ := f₀) hxfeas
    exact absurd (lt_of_le_of_lt hle hx0) (lt_irrefl _)
  obtain ⟨c, μ, hcnonneg, hμnonneg, hcne, hkey⟩ :=
    (alternative_of_convex_system_affine (C := convexDom f₀) (f := g)
        (a := b) hf₀.convex_convexDom hgconv
      hgproper hgdom ⟨z, hzri, hzb⟩).resolve_left hnoalt
  -- the multiplier of the objective is positive
  have hcpos : 0 < c none := by
    rcases eq_or_lt_of_le (hcnonneg none) with h0 | h0
    · exfalso
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, c (some i₀) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hcne (funext fun i' => by
          cases i' with
          | none => exact h0.symm
          | some i => exact hcon i)
      have hz' := hkey z hzC
      rw [Fintype.sum_option] at hz'
      have hfirst : (c none : EReal) * g none z = 0 := by
        rw [← h0]; simp
      have hsecond : (∑ i, (c (some i) : EReal) * g (some i) z) < 0 := by
        refine sum_coe_mul_neg (l := fun i => c (some i)) (fun i => hcnonneg (some i))
          (v := fun i => g (some i) z) (fun i => ?_) hi₀
        rw [hgsome i]; exact hzf i
      have hthird : ((∑ j, μ j * b j z : ℝ) : EReal) ≤ 0 := by
        have h : (∑ j, μ j * b j z) ≤ 0 :=
          Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hμnonneg j) (hzb j)
        exact_mod_cast h
      rw [hfirst, zero_add] at hz'
      have : (∑ i, (c (some i) : EReal) * g (some i) z) + ((∑ j, μ j * b j z : ℝ) : EReal) < 0 :=
        lt_of_le_of_lt (add_le_add (le_refl _) hthird) (by simpa using hsecond)
      exact absurd hz' (not_le.2 this)
    · exact h0
  -- normalise: divide every multiplier by the one on the objective
  set l : ι → ℝ := fun i => c (some i) / c none with hldef
  set ν : κ → ℝ := fun j => μ j / c none with hνdef
  have hlnonneg : ∀ i, 0 ≤ l i := fun i => div_nonneg (hcnonneg (some i)) hcpos.le
  have hνnonneg : ∀ j, 0 ≤ ν j := fun j => div_nonneg (hμnonneg j) hcpos.le
  have hL : ∀ x, (α : EReal) ≤ programLagrangian f₀ f b l ν x := by
    intro x
    by_cases hxC : x ∈ convexDom f₀
    · obtain ⟨r₀, hr₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp₀.ne_bot x) (mem_convexDom.1 hxC)
      have hrfin : ∀ i, ∃ r : ℝ, f i x = (r : EReal) := fun i =>
        EReal.exists_coe_of_ne_bot_of_lt_top ((hp i).ne_bot x) (mem_convexDom.1 (hsub i hxC))
      choose r hr using hrfin
      have hx' := hkey x hxC
      rw [Fintype.sum_option] at hx'
      have hnone : (c none : EReal) * g none x = ((c none * (r₀ + -α) : ℝ) : EReal) := by
        change (c none : EReal) * (f₀ x + ((-α : ℝ) : EReal)) = _
        rw [hr₀, ← EReal.coe_add, ← EReal.coe_mul]
      have hsome : ∀ i, (c (some i) : EReal) * g (some i) x = ((c (some i) * r i : ℝ) : EReal) := by
        intro i; rw [hgsome i, hr i, ← EReal.coe_mul]
      rw [hnone, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsome i),
        ← EReal.coe_sum, ← EReal.coe_add, ← EReal.coe_add,
        ← EReal.coe_zero, EReal.coe_le_coe_iff] at hx'
      rw [programLagrangian_eq_coe hr₀ hr, EReal.coe_le_coe_iff]
      refine le_of_mul_le_mul_left ?_ hcpos
      have hsumfield : c none * (∑ i, l i * r i) = ∑ i, c (some i) * r i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hldef]
        field_simp
      have haffield : c none * (∑ j, ν j * b j x) = ∑ j, μ j * b j x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hνdef]
        field_simp
      have hexp : c none * (r₀ + (∑ i, l i * r i) + ∑ j, ν j * b j x)
          = c none * r₀ + c none * (∑ i, l i * r i) + c none * (∑ j, ν j * b j x) := by ring
      have hshift : c none * (r₀ + -α) = c none * r₀ - c none * α := by ring
      rw [hexp, hsumfield, haffield]
      rw [hshift] at hx'
      linarith
    · have htopx : f₀ x = ⊤ := by
        rcases lt_or_eq_of_le (le_top : f₀ x ≤ ⊤) with h | h
        · exact absurd (mem_convexDom.2 h) hxC
        · exact h
      rw [programLagrangian_eq_top hlnonneg (fun i y => (hp i).ne_bot y) htopx]
      exact le_top
  have hiInf : (⨅ x, programLagrangian f₀ f b l ν x) = (α : EReal) := by
    refine le_antisymm ?_ (le_iInf hL)
    rw [← hα]
    exact le_iInf₂ fun x hx =>
      (iInf_le _ x).trans (programLagrangian_le_of_mem_feasibleSet hlnonneg hνnonneg hx)
  exact ⟨l, ν, hlnonneg, hνnonneg, by rw [hiInf]; exact EReal.coe_ne_bot _,
    by rw [hiInf]; exact EReal.coe_ne_top _, by rw [hiInf, hα]⟩

/-- **Only affine constraints.** Let $E$ be finite-dimensional, let $f_0$ be proper convex, and let
there be no convex constraints ($\iota$ empty). If the optimal value is not $-\infty$ and some
$x \in \operatorname{ri}(\operatorname{dom} f_0)$ satisfies $b_j(x) \le 0$ for all $j$, then
there is a Kuhn–Tucker vector.

This is `ConvexAnalysis.exists_isKuhnTuckerVector_of_slater` with an empty family of strict
constraints. -/
theorem exists_isKuhnTuckerVector_of_affine [IsEmpty ι] (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀)
    (hbot : optimalValue f₀ f b ≠ ⊥) (hfeas : ∃ x ∈ ri (convexDom f₀), ∀ j, b j x ≤ 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  obtain ⟨x, hx, hxb⟩ := hfeas
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ (fun i => isEmptyElim i)
    (fun i => isEmptyElim i) (fun i => isEmptyElim i) hbot ⟨x, hx, fun i => isEmptyElim i, hxb⟩

omit [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- An affine map $g \colon E \to \mathbb{R}$ along the segment from $y$ to $z$:
$g((1 - a)y + az) = (1 - a)g(y) + a g(z)$ for every real $a$. -/
theorem affineMap_segment (g : E →ᵃ[ℝ] ℝ) (y z : E) (a : ℝ) :
    g ((1 - a) • y + a • z) = (1 - a) * g y + a * g z := by
  have hseg : (1 - a) • y + a • z = AffineMap.lineMap y z a := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  rw [hseg, AffineMap.apply_lineMap, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

/-- **Slater's condition at a point of the domain.** Let $E$ be finite-dimensional, let $f_0$ and
the $f_i$ be proper convex, and let $C = \operatorname{dom} f_0$, with
$C \subseteq \operatorname{dom} f_i$ and $\operatorname{ri} C \subseteq
\operatorname{ri}(\operatorname{dom} f_i)$ for every $i$. Suppose that the optimal value is not
$-\infty$ and that there is $x \in C$ with
$$f_i(x) < 0 \text{ for all } i \quad \text{and} \quad b_j(x) < 0 \text{ for all } j.$$
Then there is a Kuhn–Tucker vector.

The point $x$ need not lie in $\operatorname{ri} C$: moving it a little towards a relative
interior point gives a point that satisfies Slater's condition. Rockafellar states this for a
program without affine constraints. Affine constraints are allowed here, but they too must hold
strictly, because only the strict inequalities survive the move. The hypothesis
$\operatorname{ri} C \subseteq \operatorname{ri}(\operatorname{dom} f_i)$ is needed to follow
$f_i$ along the segment. -/
theorem exists_isKuhnTuckerVector_of_mem_convexDom (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, ProperConvex (f i))
        (hsub : ∀ i, convexDom f₀ ⊆ convexDom (f i))
    (hri : ∀ i, ri (convexDom f₀) ⊆ ri (convexDom (f i))) (hbot : optimalValue f₀ f b ≠ ⊥)
    (hslater : ∃ x ∈ convexDom f₀, (∀ i, f i x < 0) ∧ ∀ j, b j x < 0) :
    ∃ (l : ι → ℝ) (μ : κ → ℝ), IsKuhnTuckerVector f₀ f b l μ := by
  classical
  obtain ⟨z, hz, hzf, hzb⟩ := hslater
  obtain ⟨y, hy⟩ := Convex.relint_nonempty hf₀.convex_convexDom ⟨z, hz⟩
  -- along the segment from `y` to `z`, every constraint stays strict near the far end
  have hmem : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), (1 - a) • y + a • z ∈ ri (convexDom f₀) := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with a ha ha'
    exact Convex.segment_mem_relint hf₀.convex_convexDom hy (subset_closure hz) ha.le ha'
  have hcon : ∀ i, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), f i ((1 - a) • y + a • z) < 0 := by
    intro i
    have hlim := (hf i).tendsto_lscHull_along_segment_relint (hri i hy) z
    exact hlim.eventually_lt_const (lt_of_le_of_lt (lscHull_le (f i) z) (hzf i))
  have haff : ∀ j, ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), b j ((1 - a) • y + a • z) < 0 := by
    intro j
    have hlim : Filter.Tendsto (fun a : ℝ => b j ((1 - a) • y + a • z)) (𝓝[<] (1 : ℝ))
        (𝓝 (b j z)) := by
      have : Filter.Tendsto (fun a : ℝ => (1 - a) * b j y + a * b j z) (𝓝 (1 : ℝ))
          (𝓝 ((1 - 1) * b j y + 1 * b j z)) :=
        (((tendsto_const_nhds.sub tendsto_id).mul tendsto_const_nhds).add
          (tendsto_id.mul tendsto_const_nhds))
      simp only [sub_self, zero_mul, one_mul, zero_add] at this
      exact (this.mono_left nhdsWithin_le_nhds).congr fun a => (affineMap_segment (b j) y z a).symm
    exact hlim.eventually_lt_const (hzb j)
  obtain ⟨a, hamem, hafeas⟩ :=
    ((hmem.and ((Filter.eventually_all).2 hcon)).and ((Filter.eventually_all).2 haff)).exists
  exact exists_isKuhnTuckerVector_of_slater hf₀ hp₀ hf hp hsub hbot
    ⟨_, hamem.1, hamem.2, fun j => (hafeas j).le⟩

/-- **Affine equality constraints.** Let $E$ be finite-dimensional, let $f_0$ and the $f_i$ be
proper convex with $\operatorname{dom} f_0 \subseteq \operatorname{dom} f_i$, and let
$a_k \colon E \to \mathbb{R}$, $k \in \sigma$, be finitely many affine maps. Suppose that the
infimum of $f_0$ subject to $f_i(x) \le 0$ and $a_k(x) = 0$ is not $-\infty$, and that some $x
\in \operatorname{ri}(\operatorname{dom} f_0)$ satisfies $f_i(x) < 0$ for all $i$ and
$a_k(x) = 0$ for all $k$. Then there are $\lambda \ge 0$ and $\rho \in \mathbb{R}^\sigma$ with
$$\inf_{x \in E} \Bigl(f_0(x) + \sum_i \lambda_i f_i(x) + \sum_k \rho_k a_k(x)\Bigr) = \inf \{
  f_0(x) \mid f_i(x) \le 0 \text{ for all } i,\ a_k(x) = 0 \text{ for all } k \}.$$

The multipliers $\rho_k$ have arbitrary sign. They are $\rho = \mu' - \mu''$, where $\mu'$ and
$\mu''$ are the multipliers of the two inequalities $a_k(x) \le 0$ and $-a_k(x) \le 0$ into
which each equation splits. -/
theorem exists_multipliers_of_slater_eq {σ : Type*} [Fintype σ] {a : σ → E →ᵃ[ℝ] ℝ}
    (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀) (hf : ∀ i, ConvexFn (f i))
        (hp : ∀ i, ProperConvex (f i))
    (hsub : ∀ i, convexDom f₀ ⊆ convexDom (f i))
    (hbot : optimalValue f₀ f (Sum.elim a fun k => -(a k)) ≠ ⊥)
    (hslater : ∃ x ∈ ri (convexDom f₀), (∀ i, f i x < 0) ∧ ∀ k, a k x = 0) :
    ∃ (l : ι → ℝ) (ρ : σ → ℝ), (∀ i, 0 ≤ l i) ∧
      (⨅ x, f₀ x + (∑ i, (l i : EReal) * f i x) + ((∑ k, ρ k * a k x : ℝ) : EReal))
        = ⨅ x ∈ {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0}, f₀ x := by
  classical
  set b' : σ ⊕ σ → E →ᵃ[ℝ] ℝ := Sum.elim a fun k => -(a k) with hb'
  have hinl : ∀ (k : σ) (x : E), b' (Sum.inl k) x = a k x := fun _ _ => rfl
  have hinr : ∀ (k : σ) (x : E), b' (Sum.inr k) x = -(a k x) := fun _ _ => rfl
  have hsplit : ∀ (x : E), (∀ j, b' j x ≤ 0) ↔ ∀ k, a k x = 0 := by
    intro x
    constructor
    · intro h k
      have h₁ := h (Sum.inl k)
      have h₂ := h (Sum.inr k)
      rw [hinl k x] at h₁
      rw [hinr k x] at h₂
      linarith
    · rintro h (k | k)
      · rw [hinl k x, h k]
      · rw [hinr k x, h k, neg_zero]
  have hfeasEq : feasibleSet f b' = {x | (∀ i, f i x ≤ 0) ∧ ∀ k, a k x = 0} := by
    ext x
    exact and_congr_right fun _ => hsplit x
  obtain ⟨x₀, hx₀, hx₀f, hx₀a⟩ := hslater
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_slater (b := b') hf₀ hp₀ hf hp hsub hbot
    ⟨x₀, hx₀, hx₀f, (hsplit x₀).2 hx₀a⟩
  refine ⟨l, fun k => μ (Sum.inl k) - μ (Sum.inr k), hkt.nonneg, ?_⟩
  have hlag : ∀ x, f₀ x + (∑ i, (l i : EReal) * f i x)
      + ((∑ k, (μ (Sum.inl k) - μ (Sum.inr k)) * a k x : ℝ) : EReal)
      = programLagrangian f₀ f b' l μ x := by
    intro x
    rw [programLagrangian_apply]
    congr 2
    rw [Fintype.sum_sum_type]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb', Sum.elim_inl, Sum.elim_inr, AffineMap.coe_neg, Pi.neg_apply]
    ring
  rw [iInf_congr hlag, hkt.iInf_eq, optimalValue, hfeasEq]

end Slater

/-!
### The Kuhn–Tucker conditions

Theorem 28.3 of [rockafellar1970convex] characterizes the pairs of a Kuhn–Tucker vector and an
optimal solution of an ordinary convex program by three conditions on the point $\bar x$ and the
multipliers $\lambda_i$: (a) $\lambda_i \ge 0$, $f_i(\bar x) \le 0$ and $\lambda_i f_i(\bar x) = 0$
for the inequality constraints; (b) $f_i(\bar x) = 0$ for the affine equality constraints; (c) $0
\in \partial f_0(\bar x) + \lambda_1 \partial f_1(\bar x) + \dots + \lambda_m \partial f_m(\bar x)$,
where the terms with $\lambda_i = 0$ are omitted. Its general content is two statements about the
function $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$, the objective plus the weighted
constraints at fixed multipliers.

* `ConvexAnalysis.subdifferential_add_sum_coe_mul`: the subdifferential of $h$ decomposes as in (c).
  This is the sum rule for subgradients ([rockafellar1970convex], Theorem 23.8), under the
  constraint qualification that the effective domains have a common relative interior point.
* `ConvexAnalysis.mem_argmin_add_sum_coe_mul_of_zero_mem` and
  `ConvexAnalysis.add_sum_coe_mul_eq_of_forall_mul_eq_zero`: condition (c) makes $\bar x$ a
  minimizer of $h$, and complementary slackness gives $h(\bar x) = f_0(\bar x)$. Together these are
  the sufficiency half of Theorem 28.3, for every program whose Lagrange function has this form.

Both are stated for one finite family of summands $\lambda_i f_i$, each **admissible** in the sense
of `ConvexAnalysis.IsLagrangeSummand`: either $f_i$ is proper convex and $\lambda_i \ge 0$, or $f_i$
is affine and $\lambda_i$ has any sign. These are the two kinds of constraint of an ordinary convex
program. The statements hold for any dual pair of spaces.
`ConvexAnalysis.isKuhnTuckerVector_of_kuhnTucker` is the same sufficiency in the terms of this
module, where the affine constraints form the separate family $b$.
-/

section LagrangeSummand

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {x₀ : E}

/-- The summand $\lambda g$ of a Lagrange function is **admissible** at the reference point $x_0$ if
one of two conditions holds:

* $\lambda \ge 0$, $g$ is proper convex, and $x_0 \in \operatorname{ri}(\operatorname{dom} g)$;
* $g$ is an affine function $a \colon E \to \mathbb{R}$ whose linear part is represented through
  the pairing by some $v \in F$, that is, $\langle w, v \rangle = a_{\mathrm{lin}}(w)$ for all
  $w$, and $\lambda$ is arbitrary.

These are the inequality and the equality constraints of an ordinary convex program. In both
cases $\lambda g$ is a proper convex function with $x_0$ in the relative interior of its
effective domain. -/
def IsLagrangeSummand (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x₀ : E) (l : ℝ) (g : E → EReal) : Prop :=
  (0 ≤ l ∧ ConvexFn g ∧ ProperConvex g ∧ x₀ ∈ ri (convexDom g)) ∨
    ∃ (a : E →ᵃ[ℝ] ℝ) (v : F), (∀ y, g y = a y) ∧ ∀ w, B w v = a.linear w

/-- For every real $c$ and every affine $a \colon E \to \mathbb{R}$, the function
$y \mapsto c\, a(y)$ is convex, proper, and finite everywhere. -/
theorem convexFn_properConvex_coe_mul_affineMap (c : ℝ) (a : E →ᵃ[ℝ] ℝ) :
    ConvexFn (fun y => (c : EReal) * ((a y : ℝ) : EReal)) ∧
      ProperConvex (fun y => (c : EReal) * ((a y : ℝ) : EReal)) ∧
      convexDom (fun y => (c : EReal) * ((a y : ℝ) : EReal)) = univ := by
  have hrw : (fun y => (c : EReal) * ((a y : ℝ) : EReal))
      = fun y => (((c • a) y : ℝ) : EReal) := by
    funext y
    rw [← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hrw]
  refine ⟨?_, properConvex_coe _, convexDom_coe _⟩
  refine ConvexOn.convexFn_coe ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  rw [Convex.combo_affine_apply hpq]

/-- If the summand $cg$ is admissible at $x_0$, then $y \mapsto c\, g(y)$ is proper convex and $x_0
\in \operatorname{ri}(\operatorname{dom}(cg))$. These are the hypotheses of the sum rule for
subgradients. -/
theorem IsLagrangeSummand.convexFn_properConvex_mem_relint {c : ℝ} {g : E → EReal}
    (h : IsLagrangeSummand B x₀ c g) :
    ConvexFn (fun y => (c : EReal) * g y) ∧ ProperConvex (fun y => (c : EReal) * g y) ∧
      x₀ ∈ ri (convexDom fun y => (c : EReal) * g y) := by
  rcases h with ⟨hc, hg, hp, hx₀⟩ | ⟨a, v, hga, -⟩
  · refine ⟨convexFn_coe_mul hc hg, properConvex_coe_mul hc hp, ?_⟩
    rcases hc.eq_or_lt with rfl | hpos
    · have hdom : convexDom (fun y => ((0 : ℝ) : EReal) * g y) = univ :=
        eq_univ_of_forall fun y => by simp
      rw [hdom, intrinsicInterior_univ]
      exact mem_univ _
    · rwa [convexDom_coe_mul hpos]
  · have hg : g = fun y => ((a y : ℝ) : EReal) := funext hga
    subst hg
    obtain ⟨h₁, h₂, h₃⟩ := convexFn_properConvex_coe_mul_affineMap c a
    refine ⟨h₁, h₂, ?_⟩
    rw [h₃, intrinsicInterior_univ]
    exact mem_univ _

/-- Let the pairing $\langle \cdot, \cdot \rangle \colon E \times F \to \mathbb{R}$ separate the
points of $F$. If the summand $cg$ is admissible and $c \neq 0$, then for every $x$
$$\partial(cg)(x) = c\, \partial g(x).$$
For a convex $g$ this means $c > 0$, and for an affine $g$ the sign of $c$ is arbitrary. -/
theorem IsLagrangeSummand.subdifferential_coe_mul (hsep : Function.Injective B.flip) {c : ℝ}
    {g : E → EReal} (h : IsLagrangeSummand B x₀ c g) (hc : c ≠ 0) (x : E) :
    subdifferential B (fun y => (c : EReal) * g y) x = c • subdifferential B g x := by
  rcases h with ⟨hc0, -, -, -⟩ | ⟨a, v, hga, hv⟩
  · exact ConvexAnalysis.subdifferential_coe_mul (lt_of_le_of_ne hc0 (Ne.symm hc)) g x
  · have hg : g = fun y => ((a y : ℝ) : EReal) := funext hga
    subst hg
    exact subdifferential_coe_mul_affineMap hsep c a hv x

end LagrangeSummand

section KuhnTucker

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι : Type*} {s : Finset ι} {f₀ : E → EReal} {f : ι → E → EReal}
  {l : ι → ℝ} {x₀ : E}

/-- **The subdifferential of $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$.** Let $E$ and $F$ be
finite-dimensional real normed spaces with a pairing $\langle \cdot, \cdot \rangle \colon E
\times F \to \mathbb{R}$ that is compatible in both directions and separates the points of $F$.
Let $f_0$ be proper convex with $x_0 \in \operatorname{ri}(\operatorname{dom} f_0)$, and let
each summand $\lambda_i f_i$, $i \in s$, be admissible at $x_0$. Then for every $x \in E$,
$$\partial h(x) = \partial f_0(x) + \sum_{i \in s,\ \lambda_i \neq 0} \lambda_i\, \partial
  f_i(x).$$

This is Theorem 23.8 of [rockafellar1970convex] applied to the summands of the Lagrange
function. The omission of the terms with $\lambda_i = 0$ matters: $\partial f_i(x)$ can be empty
at a boundary point of $\operatorname{dom} f_i$, and then $0 \cdot \partial f_i(x)$ would be
empty and not $\{0\}$. Compatibility of the pairing is `ConvexAnalysis.IsCompatiblePairing` for
`B` and `B.flip`, and separation is the injectivity of `B.flip`. -/
theorem subdifferential_add_sum_coe_mul [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀)
    (hx₀ : x₀ ∈ ri (convexDom f₀)) (hf : ∀ i ∈ s, IsLagrangeSummand B x₀ (l i) (f i)) (x : E) :
    subdifferential B (fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y) x
      = subdifferential B f₀ x + ∑ i ∈ s with l i ≠ 0, l i • subdifferential B (f i) x := by
  classical
  set g : Option ι → E → EReal := fun o => o.elim f₀ fun i y => (l i : EReal) * f i y with hg
  have hsum : (fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y) = ∑ o ∈ s.insertNone, g o := by
    funext y
    rw [Finset.sum_apply, Finset.sum_insertNone]
    rfl
  have hprop : ∀ o ∈ s.insertNone,
      ConvexFn (g o) ∧ ProperConvex (g o) ∧ x₀ ∈ ri (convexDom (g o)) := by
    intro o ho
    cases o with
    | none => exact ⟨hf₀, hp₀, hx₀⟩
    | some i => exact (hf i (Finset.some_mem_insertNone.1 ho)).convexFn_properConvex_mem_relint
  have hex : IsExactFinsetSum B s.insertNone g :=
    IsExactFinsetSum.of_relint ⟨none, Finset.mem_insertNone.2 (by simp)⟩
      (fun o ho => (hprop o ho).1) (fun o ho => (hprop o ho).2.1) fun o ho => (hprop o ho).2.2
  rw [hsum, hex.subdifferential_finsetSum x, Finset.sum_insertNone, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs with hli
  · exact (hf i hi).subdifferential_coe_mul hsep hli x
  · push Not at hli
    change subdifferential B (fun y => (l i : EReal) * f i y) x = 0
    rw [hli, subdifferential_zero_mul hsep, Set.singleton_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- **Complementary slackness.** If $\lambda_i f_i(x) = 0$ for every $i \in s$, then $f_0(x) +
\sum_{i \in s} \lambda_i f_i(x) = f_0(x)$. -/
theorem add_sum_coe_mul_eq_of_forall_mul_eq_zero {x : E}
    (h : ∀ i ∈ s, (l i : EReal) * f i x = 0) :
    f₀ x + ∑ i ∈ s, (l i : EReal) * f i x = f₀ x := by
  rw [Finset.sum_eq_zero h, add_zero]

/-- **Condition (c) of the Kuhn–Tucker conditions makes $x$ a minimizer of $h$.** Let $E$, $F$, the
pairing, $f_0$, $x_0$ and the admissible summands $\lambda_i f_i$, $i \in s$, be as in
`ConvexAnalysis.subdifferential_add_sum_coe_mul`. If
$$0 \in \partial f_0(x) + \sum_{i \in s,\ \lambda_i \neq 0} \lambda_i\, \partial f_i(x),$$
then $x$ minimizes $h = f_0 + \sum_{i \in s} \lambda_i f_i$ over $E$. -/
theorem mem_argmin_add_sum_coe_mul_of_zero_mem [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀)
    (hp₀ : ProperConvex f₀) (hx₀ : x₀ ∈ ri (convexDom f₀))
        (hf : ∀ i ∈ s, IsLagrangeSummand B x₀ (l i) (f i))
    {x : E}
    (h : (0 : F) ∈ subdifferential B f₀ x + ∑ i ∈ s with l i ≠ 0, l i • subdifferential B (f i) x) :
    x ∈ argmin fun y => f₀ y + ∑ i ∈ s, (l i : EReal) * f i y := by
  rw [mem_argmin_iff_zero_mem_subdifferential B,
    subdifferential_add_sum_coe_mul hsep hf₀ hp₀ hx₀ hf]
  exact h

end KuhnTucker

section KuhnTuckerProgram

open scoped Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {f₀ : E → EReal} {f : ι → E → EReal} {b : κ → E →ᵃ[ℝ] ℝ} {l : ι → ℝ} {μ : κ → ℝ}

/-- The affine part $x \mapsto \sum_j \mu_j b_j(x)$ of the Lagrangian, as one affine map, with
linear part $\sum_j \mu_j (b_j)_{\mathrm{lin}}$. -/
def affineSum (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) : E →ᵃ[ℝ] ℝ where
  toFun y := ∑ j, μ j * b j y
  linear := ∑ j, μ j • (b j).linear
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      ← Finset.sum_add_distrib, ← mul_add]
    exact Finset.sum_congr rfl fun j _ => by rw [← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add]

omit [FiniteDimensional ℝ E] in
/-- The value of `ConvexAnalysis.affineSum b μ` at $y$ is $\sum_j \mu_j b_j(y)$. -/
@[simp] theorem affineSum_apply (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) (y : E) :
    affineSum b μ y = ∑ j, μ j * b j y := rfl

omit [FiniteDimensional ℝ E] in
/-- The linear part of `ConvexAnalysis.affineSum b μ` is $\sum_j \mu_j (b_j)_{\mathrm{lin}}$. -/
@[simp] theorem affineSum_linear (b : κ → E →ᵃ[ℝ] ℝ) (μ : κ → ℝ) :
    (affineSum b μ).linear = ∑ j, μ j • (b j).linear := rfl

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The Lagrangian `ConvexAnalysis.programLagrangian` is the function $h$ for the family $f$
together with the single affine summand `ConvexAnalysis.affineSum b μ` with multiplier $1$. The
family is indexed by `Option ι`, and the affine summand is at `none`. -/
theorem programLagrangian_eq_add_sum_option (f₀ : E → EReal) (f : ι → E → EReal)
    (b : κ → E →ᵃ[ℝ] ℝ) (l : ι → ℝ) (μ : κ → ℝ) :
    programLagrangian f₀ f b l μ = fun x => f₀ x + ∑ o : Option ι,
      ((o.elim (1 : ℝ) l : ℝ) : EReal) *
        o.elim (fun y => ((affineSum b μ y : ℝ) : EReal)) f x := by
  funext x
  rw [programLagrangian_apply, Fintype.sum_option]
  simp only [Option.elim, EReal.coe_one, one_mul]
  rw [affineSum_apply, add_assoc, add_comm (∑ i, (l i : EReal) * f i x)]

/-- **Sufficiency of the Kuhn–Tucker conditions.** Let $E$ and $F$ be finite-dimensional real normed
spaces with a pairing $\langle \cdot, \cdot \rangle \colon E \times F \to \mathbb{R}$ that is
compatible in both directions and separates the points of $F$. Let $f_0$ and the $f_i$ be proper
convex, and let $x_0 \in \operatorname{ri}(\operatorname{dom} f_0)$ with $x_0 \in
\operatorname{ri}(\operatorname{dom} f_i)$ for every $i$. For each $j$, let $a_j \in F$
represent the linear part of $b_j$: $\langle w, a_j \rangle = (b_j)_{\mathrm{lin}}(w)$ for all
$w$. Let $x \in E$ satisfy

* $\lambda_i \ge 0$, $f_i(x) \le 0$ and $\lambda_i f_i(x) = 0$ for every $i$;
* $\mu_j \ge 0$, $b_j(x) \le 0$ and $\mu_j b_j(x) = 0$ for every $j$;
* $0 \in \partial f_0(x) + \sum_{\lambda_i \neq 0} \lambda_i\, \partial f_i(x) + \bigl\{\sum_j
  \mu_j a_j\bigr\}$.

Then $(\lambda, \mu)$ is a Kuhn–Tucker vector, $x$ is feasible, and $f_0(x)$ is the optimal
value, so $x$ is an optimal solution.

This is the "if" half of Theorem 28.3 of [rockafellar1970convex]. It needs no constraint
qualification beyond the common relative interior point $x_0$. -/
theorem isKuhnTuckerVector_of_kuhnTucker [IsCompatiblePairing B] [IsCompatiblePairing B.flip]
    (hsep : Function.Injective B.flip) (hf₀ : ConvexFn f₀) (hp₀ : ProperConvex f₀)
    (hf : ∀ i, ConvexFn (f i)) (hpf : ∀ i, ProperConvex (f i)) {x₀ : E}
        (hx₀ : x₀ ∈ ri (convexDom f₀))
    (hri : ∀ i, x₀ ∈ ri (convexDom (f i))) {a : κ → F}
        (ha : ∀ j w, B w (a j) = (b j).linear w) {x : E}
    (hl : ∀ i, 0 ≤ l i ∧ f i x ≤ 0 ∧ (l i : EReal) * f i x = 0)
    (hμ : ∀ j, 0 ≤ μ j ∧ b j x ≤ 0 ∧ μ j * b j x = 0)
    (hc : (0 : F) ∈ subdifferential B f₀ x + ∑ i with l i ≠ 0, l i • subdifferential B (f i) x
      + {∑ j, μ j • a j}) :
    IsKuhnTuckerVector f₀ f b l μ ∧ x ∈ feasibleSet f b ∧ f₀ x = optimalValue f₀ f b := by
  classical
  -- the Lagrangian as `h` over `Option ι`
  set l' : Option ι → ℝ := fun o => o.elim 1 l with hl'
  set g : Option ι → E → EReal := fun o => o.elim (fun y => ((affineSum b μ y : ℝ) : EReal)) f
    with hg
  have hlag : programLagrangian f₀ f b l μ = fun y => f₀ y + ∑ o, (l' o : EReal) * g o y :=
    programLagrangian_eq_add_sum_option f₀ f b l μ
  have hlin : ∀ w, B w (∑ j, μ j • a j) = (affineSum b μ).linear w := fun w => by
    simp only [map_sum, map_smul, smul_eq_mul, affineSum_linear, LinearMap.sum_apply,
      LinearMap.smul_apply, ha]
  have hadm : ∀ o ∈ (Finset.univ : Finset (Option ι)), IsLagrangeSummand B x₀ (l' o) (g o) := by
    intro o _
    cases o with
    | none => exact Or.inr ⟨affineSum b μ, ∑ j, μ j • a j, fun y => rfl, hlin⟩
    | some i => exact Or.inl ⟨(hl i).1, hf i, hpf i, hri i⟩
  -- condition (c) in the `Option ι` shape
  have hfilter : (Finset.univ.filter fun o : Option ι => l' o ≠ 0)
      = insert none ((Finset.univ.filter fun i => l i ≠ 0).map Function.Embedding.some) := by
    ext o
    cases o <;> simp [hl']
  have hc' : (0 : F) ∈
      subdifferential B f₀ x + ∑ o with l' o ≠ 0, l' o • subdifferential B (g o) x := by
    rw [hfilter, Finset.sum_insert (by simp), Finset.sum_map]
    have hnone :
        subdifferential B (fun y => ((affineSum b μ y : ℝ) : EReal)) x = {∑ j, μ j • a j} :=
      subdifferential_coe_affineMap hsep (affineSum b μ) hlin x
    simp only [hl', hg, Option.elim, Function.Embedding.some_apply, one_smul]
    rw [hnone, add_comm ({∑ j, μ j • a j} : Set F), ← add_assoc]
    exact hc
  have hmin : x ∈ argmin (programLagrangian f₀ f b l μ) := by
    rw [hlag]
    exact mem_argmin_add_sum_coe_mul_of_zero_mem hsep hf₀ hp₀ hx₀ hadm hc'
  -- complementary slackness: `L x = f₀ x`
  have hslack : ∀ o ∈ (Finset.univ : Finset (Option ι)), (l' o : EReal) * g o x = 0 := by
    intro o _
    cases o with
    | none =>
      have : affineSum b μ x = 0 := by
        rw [affineSum_apply]
        exact Finset.sum_eq_zero fun j _ => (hμ j).2.2
      simp only [hl', hg, Option.elim, this, EReal.coe_zero, mul_zero]
    | some i => exact (hl i).2.2
  have hLx : programLagrangian f₀ f b l μ x = f₀ x := by
    rw [hlag]
    exact add_sum_coe_mul_eq_of_forall_mul_eq_zero hslack
  -- `x` is feasible and in `dom f₀`
  have hfeas : x ∈ feasibleSet f b := ⟨fun i => (hl i).2.1, fun j => (hμ j).2.1⟩
  have hxdom : x ∈ convexDom f₀ := by
    obtain ⟨w, hw, -, -, -⟩ := Set.mem_add.1 hc
    obtain ⟨v₀, hv₀, -, -, -⟩ := Set.mem_add.1 hw
    exact mem_convexDom_of_mem_subdifferential hp₀ hv₀
  have hinf : (⨅ y, programLagrangian f₀ f b l μ y) = f₀ x := by
    rw [iInf_eq_of_mem_argmin hmin, hLx]
  have hopt : f₀ x = optimalValue f₀ f b := by
    refine le_antisymm ?_ (optimalValue_le hfeas)
    refine le_iInf₂ fun y hy => ?_
    calc f₀ x = programLagrangian f₀ f b l μ x := hLx.symm
      _ ≤ programLagrangian f₀ f b l μ y := hmin y
      _ ≤ f₀ y :=
        programLagrangian_le_of_mem_feasibleSet (fun i => (hl i).1) (fun j => (hμ j).1) hy
  refine ⟨⟨fun i => (hl i).1, fun j => (hμ j).1, ?_, ?_, ?_⟩, hfeas, hopt⟩
  · rw [hinf]; exact hp₀.ne_bot x
  · rw [hinf]; exact (mem_convexDom.1 hxdom).ne
  · rw [hinf, hopt]

end KuhnTuckerProgram

end ConvexAnalysis

