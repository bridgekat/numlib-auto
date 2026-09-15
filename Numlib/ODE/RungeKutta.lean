import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Algebra.Polynomial
import Numlib.ODE.OneStep

/-!
# Runge–Kutta methods

Runge–Kutta methods for the Cauchy problem `y' = f(t, y)` on a real normed space `E`
([quarteroni2000numerical] §11.8; [kress1998numerical] §10.2 has the same two-stage derivation;
[hairer1993solving] is the reference for what the book quotes without proof).

**Tableaux.** `ButcherTableau s` is the Butcher array `A : Matrix (Fin s) (Fin s) ℝ`,
`b c : Fin s → ℝ` of an `s`-stage method ((11.70)–(11.71)); `IsExplicit` (`a_ij = 0` for `j ≥ i`),
`IsSemiImplicit`
(`a_ij = 0` for `j > i`, the DIRK methods) and `IsRowSum` (`c_i = ∑_j a_ij`, (11.72)) are its
shapes. The stage relation `IsStages f h t u K` is (11.71),
`K_i = f(t + c_i h, u + h ∑_j a_ij K_j)`, and the step relation `stepRel f h t u v` says that
`v = u + h ∑_i b_i K_i` for some stages `K` — a `OneStep.Method`, so the whole one-step theory
of `Numlib/ODE/OneStep` (zero-stability, convergence, absolute stability, A-stability) applies to
every Runge–Kutta method by instantiation and is not re-proved here. For an explicit tableau the
stages are computed by strong recursion on the stage index (`explicitStages`), are the unique
stages (`eq_explicitStages_of_isStages`), and the step relation is the increment function
`explicitIncrement f t u _ h = ∑_i b_i K_i` (`stepRel_eq_ofIncrement`), whose Lipschitz constant
`(∑_i |b_i|) L (1 + h₀ L α)^s`, `α = ∑_{i,j} |a_ij|`, is `lipschitzIncrement_explicit`; hence
every explicit Runge–Kutta method is zero-stable and, when consistent along the solution,
convergent (`isZeroStable_explicit`, `isConvergentFor_explicit`) — the book's "since RK methods are
one-step methods, consistency implies stability and, in turn, convergence".

**Consistency and order.** Consistency is `∑_i b_i = 1` in both directions: along every `C¹`
solution of a problem with a Lipschitz field, the stages converge to `f(t, y t)` uniformly in `t`
as `h → 0⁺` (`isConsistentFor_of_sum_b_eq_one`); conversely on `y' = 1` the truncation error is
the constant `1 - ∑ b_i` (`sum_b_eq_one_of_isConsistentFor`). The two-stage order-two conditions
`b₁ + b₂ = 1`, `c₂ b₂ = 1/2` of §11.8.1 are derived by the Taylor expansion of the second stage in
the pair `(t, y)` (`hasOrderFor_two_of`), and are necessary on the test problems `y' = 1` and
`y' = 2t` (`sum_b_mul_c_eq_half_of_hasOrderFor`, `orderTwoConditions_of_hasOrderFor`). Heun's
method and the modified Euler method are the two-stage instances (`heun`, `modifiedEuler`); the
classical fourth-order method (11.73) is `rk4`, with its algebraic order conditions
(`rk4_orderConditions`). Property 11.4 (Butcher's barriers) is quoted, not formalized.
A tableau satisfying the row-sum condition sees a non-autonomous problem as the autonomous
problem `Y' = (1, f(Y))` on `ℝ × E` and has the same order along the two (`autonomize`,
`hasOrderFor_autonomize_iff`), which is the reduction an order-four proof starts from.

**Adaptivity** (§11.8.2). `EmbeddedPair s` is a tableau with a second weight vector `b̂`; the
error indicator `h ∑_i (b_i - b̂_i) K_i` is the difference of the two solutions sharing the stages
(`errorIndicator_eq_sub`), and the Runge–Kutta–Fehlberg 4(5) pair is `rkf45` (standard
coefficients; the book's table is damaged in the source).

**Implicit families** (§11.8.3): the implicit midpoint rule `implicitMidpoint` (the one-stage
Gauss–Legendre method, whose step is `u_{n+1} = u_n + h f(t_n + h/2, (u_n + u_{n+1})/2)`,
`stepRel_implicitMidpoint_iff`), the two-stage Gauss–Legendre tableau `gaussLegendre2` with the
collocation identities `gaussLegendre2_collocation`, the Radau IIA tableaux `radauIIA1`
(backward Euler) and `radauIIA2`, the Lobatto IIIA tableau `lobattoIIIA2` (Crank–Nicolson), and
the three-stage DIRK family `dirk3 μ`; the maximal orders `2s`, `2s - 1`, `2s - 2` are quoted, not
proved.

**Stability function** (§11.8.4). `stabilityFunction z = 1 + z bᵀ (I - z A)⁻¹ 𝟙` with Mathlib's
`Matrix.inv` (zero on a singular matrix). On the test equation `y' = λ y` one step multiplies by
`R(hλ)` when `I - hλ A` is invertible (`stepRel_testField_iff`), so that
`z ∈ absStabilityRegion ↔ ‖R z‖ < 1` under that invertibility
(`mem_absStabilityRegion_iff_of_isUnit`). For an explicit tableau `A` is nilpotent, so
`I - zA` is always invertible with determinant `1`, and `R` is the polynomial
`1 + ∑_{k<s} z^{k+1} bᵀ A^k 𝟙 = det (I - zA + z 𝟙 bᵀ)` (`stabilityFunction_eq_sum_of_isExplicit`,
`stabilityFunction_eq_det_of_isExplicit`, the matrix determinant lemma); a consistent explicit
method therefore has a bounded region and is never A-stable (`not_isAStable_of_isExplicit`,
Remark 11.2 for Runge–Kutta methods), and an explicit `s`-stage method of order `s` has
`R(z) = ∑_{k ≤ s} z^k / k!` (`stabilityFunction_eq_truncExp_of_hasOrder`, proved from the
real problem `y' = y` alone). `stabilityFunction_rk4` is the truncated exponential of degree `4`.

## Conventions

The vector field is `f : ℝ → E → E`; the stages `K : Fin s → E`. The book indexes stages from
`1`; here `Fin s` starts at `0`, so the two-stage conditions read `b 0 + b 1 = 1`,
`c 1 * b 1 = 1/2`. Complex versions of the real data are `complexA`, `complexB`. The step size `h`
is real; on the test equation `E = ℂ` and `h • x = (h : ℂ) * x`.
-/

open Set Filter Topology Asymptotics Matrix
open Finset (range)

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A Butcher tableau** with `s` stages ([quarteroni2000numerical] (11.70)–(11.71)): the
coefficient matrix `A = (a_ij)`, the weights `b` and the nodes `c` of an `s`-stage Runge–Kutta
method. -/
structure ButcherTableau (s : ℕ) where
  /-- The coefficient matrix `A = (a_ij)`. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- The weights `b = (b_i)`. -/
  b : Fin s → ℝ
  /-- The nodes `c = (c_i)`. -/
  c : Fin s → ℝ

namespace ButcherTableau

variable {s : ℕ} (tab : ButcherTableau s) {f : ℝ → E → E} {h t t₀ T h₀ : ℝ} {u : E}

/-! ### Shapes of tableaux -/

/-- An **explicit** tableau: `a_ij = 0` for `j ≥ i`, so that each stage is computed from the
previous ones ([quarteroni2000numerical] §11.8). -/
def IsExplicit : Prop := ∀ i j : Fin s, i ≤ j → tab.A i j = 0

/-- A **semi-implicit** (diagonally implicit, DIRK) tableau: `a_ij = 0` for `j > i`, so that each
stage solves one equation in itself. -/
def IsSemiImplicit : Prop := ∀ i j : Fin s, i < j → tab.A i j = 0

/-- The **row-sum condition** `c_i = ∑_j a_ij` ([quarteroni2000numerical] (11.72)). -/
def IsRowSum : Prop := ∀ i, tab.c i = ∑ j, tab.A i j

/-- An explicit tableau is semi-implicit. -/
theorem IsExplicit.isSemiImplicit (hex : tab.IsExplicit) : tab.IsSemiImplicit :=
  fun i j hij => hex i j hij.le

/-- **The consistency condition** `∑_i b_i = 1` ([quarteroni2000numerical] §11.8). -/
def IsConsistent : Prop := ∑ i, tab.b i = 1

/-! ### Stages and the step relation -/

/-- **The stage relation** ([quarteroni2000numerical] (11.71)): `K` are the stages of the
method at `(t, u)` with step `h` when `K_i = f(t + c_i h, u + h ∑_j a_ij K_j)` for every `i`. -/
def IsStages (f : ℝ → E → E) (h t : ℝ) (u : E) (K : Fin s → E) : Prop :=
  ∀ i, K i = f (t + tab.c i * h) (u + h • ∑ j, tab.A i j • K j)

/-- **The step relation** of the Runge–Kutta method ([quarteroni2000numerical] (11.70)):
`v` is admissible at `t + h` from `u` at `t` when `v = u + h ∑_i b_i K_i` for some stages `K`.
This is a `OneStep.Method`, so the one-step theory applies. -/
def stepRel : OneStep.Method E := fun f h t u v =>
  ∃ K : Fin s → E, tab.IsStages f h t u K ∧ v = u + h • ∑ i, tab.b i • K i

/-- The step relation, unfolded. -/
theorem stepRel_apply {v : E} :
    tab.stepRel f h t u v ↔
      ∃ K : Fin s → E, tab.IsStages f h t u K ∧ v = u + h • ∑ i, tab.b i • K i :=
  Iff.rfl

/-- **The stages of an explicit method**, by strong recursion on the stage index:
`K_i = f(t + c_i h, u + h ∑_{j < i} a_ij K_j)`. -/
noncomputable def explicitStages (f : ℝ → E → E) (h t : ℝ) (u : E) (i : Fin s) : E :=
  f (t + tab.c i * h)
    (u + h • ∑ j, if _ : j < i then tab.A i j • explicitStages f h t u j else 0)
termination_by i.1
decreasing_by exact ‹j < i›

/-- The recursion defining the explicit stages. -/
theorem explicitStages_apply (i : Fin s) :
    tab.explicitStages f h t u i = f (t + tab.c i * h)
      (u + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0) := by
  rw [explicitStages]
  simp only [dite_eq_ite]

/-- For an explicit tableau the sum over all stages reduces to the sum over the earlier ones. -/
theorem sum_smul_eq_sum_ite_of_isExplicit (hex : tab.IsExplicit) (K : Fin s → E) (i : Fin s) :
    ∑ j, tab.A i j • K j = ∑ j, if j < i then tab.A i j • K j else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · rw [hex i j (not_lt.1 hj), zero_smul]

/-- The explicit stages are stages. -/
theorem isStages_explicitStages (hex : tab.IsExplicit) (f : ℝ → E → E) (h t : ℝ) (u : E) :
    tab.IsStages f h t u (tab.explicitStages f h t u) := fun i => by
  rw [explicitStages_apply, sum_smul_eq_sum_ite_of_isExplicit tab hex]

/-- For an explicit tableau the stages are unique: any stages are the explicit ones. -/
theorem eq_explicitStages_of_isStages (hex : tab.IsExplicit) {K : Fin s → E}
    (hK : tab.IsStages f h t u K) : K = tab.explicitStages f h t u := by
  have key : ∀ m, ∀ i : Fin s, i.1 < m → K i = tab.explicitStages f h t u i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [hK i, explicitStages_apply, sum_smul_eq_sum_ite_of_isExplicit tab hex]
      congr 3
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rw [ih j (by omega)]
      · rfl
  funext i
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/-- **The increment function of an explicit method** ([quarteroni2000numerical] (11.71)):
`F(t, u, h; f) = ∑_i b_i K_i` with the explicit stages. -/
noncomputable def explicitIncrement (f : ℝ → E → E) : OneStep.Increment E :=
  fun t u _ h => ∑ i, tab.b i • tab.explicitStages f h t u i

/-- The explicit increment, unfolded. -/
theorem explicitIncrement_apply (v : E) :
    tab.explicitIncrement f t u v h = ∑ i, tab.b i • tab.explicitStages f h t u i :=
  rfl

/-- The explicit increment is explicit in the sense of `OneStep.IsExplicit`. -/
theorem isExplicit_explicitIncrement (f : ℝ → E → E) :
    OneStep.IsExplicit (tab.explicitIncrement f) :=
  fun _ _ _ _ _ => rfl

/-- For an explicit tableau the step relation is the step relation of the explicit
increment: `v = u + h ∑_i b_i K_i` with the explicit stages. -/
theorem stepRel_eq_ofIncrement (hex : tab.IsExplicit) (f : ℝ → E → E) :
    tab.stepRel f = OneStep.ofIncrement (tab.explicitIncrement f) := by
  ext h t u v
  rw [stepRel_apply, OneStep.ofIncrement_apply, explicitIncrement_apply]
  constructor
  · rintro ⟨K, hK, rfl⟩
    rw [tab.eq_explicitStages_of_isStages hex hK]
  · intro hv
    exact ⟨_, tab.isStages_explicitStages hex f h t u, hv⟩

/-! ### The Lipschitz constant of an explicit increment -/

section Lipschitz

variable {L : NNReal}

/-- The entry sum `α = ∑_{i, j} |a_ij|` of the coefficient matrix, the crude bound on `A` that
enters the Lipschitz constants below. -/
noncomputable def entrySum : ℝ := ∑ i, ∑ j, |tab.A i j|

/-- The entry sum is nonnegative. -/
theorem entrySum_nonneg : 0 ≤ tab.entrySum :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every row sum of `|A|` is bounded by the entry sum. -/
theorem sum_abs_le_entrySum (i : Fin s) : ∑ j, |tab.A i j| ≤ tab.entrySum :=
  Finset.single_le_sum (f := fun i => ∑ j, |tab.A i j|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **The stages of an explicit method are Lipschitz in the state**: if `f t'` is `L`-Lipschitz
for every `t' ∈ [t₀, t₀ + T + h₀]`, the nodes satisfy `0 ≤ c_i ≤ 1`, `t ∈ [t₀, t₀ + T]` and
`0 < h ≤ h₀`, then `‖K_i(u) - K_i(v)‖ ≤ L (1 + h₀ L α)^{i+1} ‖u - v‖`, by strong induction on
the stage index. -/
theorem norm_explicitStages_sub_le (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith L (f t)) (hh : h ∈ Ioc 0 h₀)
    (ht : t ∈ Icc t₀ (t₀ + T)) (u v : E) (i : Fin s) :
    ‖tab.explicitStages f h t u i - tab.explicitStages f h t v i‖ ≤
      L * (1 + h₀ * L * tab.entrySum) ^ (i.1 + 1) * ‖u - v‖ := by
  set x : ℝ := h₀ * L * tab.entrySum with hx
  have hx0 : 0 ≤ x := by
    have := tab.entrySum_nonneg
    have := L.coe_nonneg
    have := hh.1.le.trans hh.2
    positivity
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hnode : ∀ i : Fin s, t + tab.c i * h ∈ Icc t₀ (t₀ + T + h₀) := fun i =>
    ⟨by nlinarith [ht.1, (hc i).1, hh.1], by nlinarith [ht.2, (hc i).2, hh.1, hh.2]⟩
  have key : ∀ m, ∀ i : Fin s, i.1 < m →
      ‖tab.explicitStages f h t u i - tab.explicitStages f h t v i‖ ≤
        L * (1 + x) ^ (i.1 + 1) * ‖u - v‖ := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [explicitStages_apply, explicitStages_apply]
      refine ((hf _ (hnode i)).norm_sub_le _ _).trans ?_
      have e : u + h • (∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0) -
          (v + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t v j else 0) =
          (u - v) + h • ∑ j, if j < i then
            tab.A i j • (tab.explicitStages f h t u j - tab.explicitStages f h t v j) else 0 := by
        have e' : (∑ j, if j < i then
            tab.A i j • (tab.explicitStages f h t u j - tab.explicitStages f h t v j) else 0) =
            (∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0) -
              ∑ j, if j < i then tab.A i j • tab.explicitStages f h t v j else 0 := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs
          · rw [smul_sub]
          · rw [sub_zero]
        rw [e', smul_sub]
        abel
      rw [e]
      -- the earlier stages are bounded by the induction hypothesis
      have hsum : ‖∑ j, if j < i then
          tab.A i j • (tab.explicitStages f h t u j - tab.explicitStages f h t v j) else 0‖ ≤
          tab.entrySum * (L * (1 + x) ^ i.1 * ‖u - v‖) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖if j < i then
              tab.A i j • (tab.explicitStages f h t u j - tab.explicitStages f h t v j) else 0‖
            ≤ ∑ j, |tab.A i j| * (L * (1 + x) ^ i.1 * ‖u - v‖) := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs with hj
              · rw [norm_smul, Real.norm_eq_abs]
                refine mul_le_mul_of_nonneg_left ((ih j (by omega)).trans ?_) (abs_nonneg _)
                have : (1 + x) ^ (j.1 + 1) ≤ (1 + x) ^ i.1 :=
                  pow_le_pow_right₀ (by linarith) (by omega)
                gcongr
              · rw [norm_zero]; positivity
          _ = (∑ j, |tab.A i j|) * (L * (1 + x) ^ i.1 * ‖u - v‖) := by rw [Finset.sum_mul]
          _ ≤ tab.entrySum * (L * (1 + x) ^ i.1 * ‖u - v‖) := by
              gcongr
              exact tab.sum_abs_le_entrySum i
      calc L * ‖(u - v) + h • ∑ j, if j < i then
            tab.A i j • (tab.explicitStages f h t u j - tab.explicitStages f h t v j) else 0‖
          ≤ L * (‖u - v‖ + h * (tab.entrySum * (L * (1 + x) ^ i.1 * ‖u - v‖))) := by
            gcongr
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, Real.norm_of_nonneg hh.1.le]
            gcongr
            exact hh.1.le
        _ ≤ L * (‖u - v‖ + x * ((1 + x) ^ i.1 * ‖u - v‖)) := by
            have h1 : h * (tab.entrySum * (L * (1 + x) ^ i.1 * ‖u - v‖)) =
                (h * L * tab.entrySum) * ((1 + x) ^ i.1 * ‖u - v‖) := by ring
            have h2 : h * L * tab.entrySum ≤ x := by
              rw [hx]
              have := tab.entrySum_nonneg
              gcongr
              exact hh.2
            rw [h1]
            gcongr
        _ = L * (1 + x * (1 + x) ^ i.1) * ‖u - v‖ := by ring
        _ ≤ L * (1 + x) ^ (i.1 + 1) * ‖u - v‖ := by
            have h1 : 1 ≤ (1 + x) ^ i.1 := one_le_pow₀ (by linarith)
            have h2 : 1 + x * (1 + x) ^ i.1 ≤ (1 + x) ^ (i.1 + 1) := by
              rw [pow_succ]; nlinarith
            gcongr
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/-- **The Lipschitz constant of an explicit Runge–Kutta increment** (the hypothesis (11.18) of
[quarteroni2000numerical] Theorem 11.1 for an explicit tableau): if `f t'` is `L`-Lipschitz for
`t' ∈ [t₀, t₀ + T + h₀]` and the nodes satisfy `0 ≤ c_i ≤ 1`, the explicit increment is
`Λ`-Lipschitz in the sense of `OneStep.LipschitzIncrement` with
`Λ = (∑_i |b_i|) L (1 + h₀ L α)^s`, `α = ∑_{i,j} |a_ij|`. -/
theorem lipschitzIncrement_explicit (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith L (f t)) :
    OneStep.LipschitzIncrement (tab.explicitIncrement f) t₀ T h₀
      ((∑ i, |tab.b i|) * L * (1 + h₀ * L * tab.entrySum) ^ s) := by
  intro h hh t ht u v _ _
  simp only [explicitIncrement_apply]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  refine (norm_sum_le _ _).trans ?_
  have hx0 : 0 ≤ h₀ * L * tab.entrySum := by
    have := tab.entrySum_nonneg
    have := L.coe_nonneg
    have := hh.1.le.trans hh.2
    positivity
  calc ∑ i, ‖tab.b i • (tab.explicitStages f h t u i - tab.explicitStages f h t v i)‖
      ≤ ∑ i, |tab.b i| * (L * (1 + h₀ * L * tab.entrySum) ^ s * ‖u - v‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left
          ((tab.norm_explicitStages_sub_le hc hf hh ht u v i).trans ?_) (abs_nonneg _)
        have : (1 + h₀ * L * tab.entrySum) ^ (i.1 + 1) ≤ (1 + h₀ * L * tab.entrySum) ^ s :=
          pow_le_pow_right₀ (by linarith) i.2
        gcongr
    _ = (∑ i, |tab.b i|) * L * (1 + h₀ * L * tab.entrySum) ^ s * ‖u - v‖ := by
        rw [← Finset.sum_mul]; ring

/-- **Every explicit Runge–Kutta method is zero-stable** on a horizon `T ≥ 0` with a Lipschitz
field ([quarteroni2000numerical] §11.8, "consistency implies stability"): `OneStep.IsZeroStable`
from `lipschitzIncrement_explicit` and `OneStep.isZeroStable_of_lipschitzIncrement`. -/
theorem isZeroStable_explicit (hex : tab.IsExplicit) (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith L (f t)) (hT : 0 ≤ T) (hh₀ : 0 < h₀)
    (y₀ : E) : OneStep.IsZeroStable (tab.stepRel f) t₀ T y₀ := by
  rw [tab.stepRel_eq_ofIncrement hex]
  refine OneStep.isZeroStable_of_lipschitzIncrement hT hh₀
    (tab.lipschitzIncrement_explicit hc hf) ?_ y₀
  have := tab.entrySum_nonneg
  have := L.coe_nonneg
  positivity

/-- **A consistent explicit Runge–Kutta method is convergent** ([quarteroni2000numerical] §11.8,
"consistency implies stability and, in turn, convergence"): along a curve `y` for which the
explicit increment is consistent, the orbits from `y t₀` converge, by
`OneStep.isConvergentFor_of_isConsistentFor`. -/
theorem isConvergentFor_explicit (hex : tab.IsExplicit) (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T + h₀), LipschitzWith L (f t)) (hT : 0 ≤ T) (hh₀ : 0 < h₀)
    {y : ℝ → E} (hcons : OneStep.IsConsistentFor (tab.explicitIncrement f) t₀ T y) :
    OneStep.IsConvergentFor (tab.stepRel f) t₀ T (y t₀) y := by
  rw [tab.stepRel_eq_ofIncrement hex]
  refine OneStep.isConvergentFor_of_isConsistentFor hT hh₀
    (tab.lipschitzIncrement_explicit hc hf) ?_ hcons
  have := tab.entrySum_nonneg
  have := L.coe_nonneg
  positivity

end Lipschitz

/-! ### Consistency: `∑ bᵢ = 1` -/

section Consistency

variable {L : NNReal} {y : ℝ → E}

/-- **The stages of an explicit method are bounded**: if `‖f s u‖ ≤ M` for `s ∈ [t₀, t₀ + T + 1]`,
`f s` is `L`-Lipschitz there, the nodes satisfy `0 ≤ c_i ≤ 1`, `t ∈ [t₀, t₀ + T]` and `0 < h ≤ 1`,
then `‖K_i‖ ≤ M (1 + L α)^{i+1}`, by the same induction as `norm_explicitStages_sub_le`. -/
theorem norm_explicitStages_le (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ∀ s ∈ Icc t₀ (t₀ + T + 1), LipschitzWith L (f s)) {M : ℝ}
    (hM : ∀ s ∈ Icc t₀ (t₀ + T + 1), ‖f s u‖ ≤ M) (hh : h ∈ Ioc 0 1) (ht : t ∈ Icc t₀ (t₀ + T))
    (i : Fin s) : ‖tab.explicitStages f h t u i‖ ≤ M * (1 + L * tab.entrySum) ^ (i.1 + 1) := by
  set x : ℝ := L * tab.entrySum with hx
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hx0 : 0 ≤ x := by
    have := tab.entrySum_nonneg
    positivity
  have hnode : ∀ i : Fin s, t + tab.c i * h ∈ Icc t₀ (t₀ + T + 1) := fun i =>
    ⟨by nlinarith [ht.1, (hc i).1, hh.1], by nlinarith [ht.2, (hc i).2, hh.1, hh.2]⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, by linarith [ht.1, ht.2]⟩)
  have key : ∀ m, ∀ i : Fin s, i.1 < m →
      ‖tab.explicitStages f h t u i‖ ≤ M * (1 + x) ^ (i.1 + 1) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [explicitStages_apply]
      have hsum : ‖∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0‖ ≤
          tab.entrySum * (M * (1 + x) ^ i.1) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ j, ‖if j < i then tab.A i j • tab.explicitStages f h t u j else 0‖
            ≤ ∑ j, |tab.A i j| * (M * (1 + x) ^ i.1) := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs with hj
              · rw [norm_smul, Real.norm_eq_abs]
                refine mul_le_mul_of_nonneg_left ((ih j (by omega)).trans ?_) (abs_nonneg _)
                have : (1 + x) ^ (j.1 + 1) ≤ (1 + x) ^ i.1 :=
                  pow_le_pow_right₀ (by linarith) (by omega)
                gcongr
              · rw [norm_zero]; positivity
          _ = (∑ j, |tab.A i j|) * (M * (1 + x) ^ i.1) := by rw [Finset.sum_mul]
          _ ≤ tab.entrySum * (M * (1 + x) ^ i.1) := by
              gcongr
              exact tab.sum_abs_le_entrySum i
      calc ‖f (t + tab.c i * h)
            (u + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0)‖
          ≤ ‖f (t + tab.c i * h) u‖ + ‖f (t + tab.c i * h)
              (u + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t u j else 0) -
              f (t + tab.c i * h) u‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ M + L * (h * (tab.entrySum * (M * (1 + x) ^ i.1))) := by
            gcongr
            · exact hM _ (hnode i)
            · refine ((hf _ (hnode i)).norm_sub_le _ _).trans ?_
              rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.1.le]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hh.1.le) hL
        _ ≤ M + x * (M * (1 + x) ^ i.1) := by
            have h1 : L * (h * (tab.entrySum * (M * (1 + x) ^ i.1))) =
                (h * x) * (M * (1 + x) ^ i.1) := by rw [hx]; ring
            have h2 : h * x ≤ x := mul_le_of_le_one_left hx0 hh.2
            rw [h1]
            gcongr
        _ = M * (1 + x * (1 + x) ^ i.1) := by ring
        _ ≤ M * (1 + x) ^ (i.1 + 1) := by
            have h1 : 1 ≤ (1 + x) ^ i.1 := one_le_pow₀ (by linarith)
            have h2 : 1 + x * (1 + x) ^ i.1 ≤ (1 + x) ^ (i.1 + 1) := by
              rw [pow_succ]; nlinarith
            gcongr
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/-- The stages of an explicit method converge to the field along the solution, uniformly in
the time: if `f` is continuous on `[t₀, t₀ + T + 1] × E` and `L`-Lipschitz in the state there,
`y` is continuous on `[t₀, t₀ + T]` and the nodes satisfy `0 ≤ c_i ≤ 1`, then for every `ε > 0`
there is `η > 0` such that `‖K_i(t, y t; h) - f(t, y t)‖ ≤ ε` for all `i`, all `0 < h ≤ η` and all
`t ∈ [t₀, t₀ + T]`. The stage `K_i = f(t + c_i h, y t + h w_i)` differs from `f(t + c_i h, y t)` by
at most `L h ‖w_i‖`, with `‖w_i‖` bounded through `norm_explicitStages_le`, and from `f(t, y t)`
by the uniform continuity of `f` on the compact set `[t₀, t₀ + T + 1] × y([t₀, t₀ + T])`. -/
theorem exists_forall_norm_explicitStages_sub_le (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T + 1) ×ˢ univ))
    (hlip : ∀ s ∈ Icc t₀ (t₀ + T + 1), LipschitzWith L (f s))
    (hy : ContinuousOn y (Icc t₀ (t₀ + T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ h ∈ Ioc 0 η, ∀ t ∈ Icc t₀ (t₀ + T), ∀ i,
      ‖tab.explicitStages f h t (y t) i - f t (y t)‖ ≤ ε := by
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have hα := tab.entrySum_nonneg
  -- the compact set on which `f` is uniformly continuous and bounded
  set S : Set (ℝ × E) := Icc t₀ (t₀ + T + 1) ×ˢ (y '' Icc t₀ (t₀ + T)) with hS
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_Icc.image_of_continuousOn hy)
  have hfS : ContinuousOn (Function.uncurry f) S :=
    hf.mono (prod_mono subset_rfl (subset_univ _))
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn hfS
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hfS) (ε / 2) (half_pos hε)
  set B : ℝ := max M 0 * (1 + L * tab.entrySum) ^ s with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨min (min (1 : ℝ) (δ / 2)) (ε / (2 * (L * tab.entrySum * B + 1))), by positivity,
    fun h hh t ht i => ?_⟩
  have hh1 : h ≤ 1 := hh.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhδ : h ≤ δ / 2 := hh.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhε : h ≤ ε / (2 * (L * tab.entrySum * B + 1)) := hh.2.trans (min_le_right _ _)
  have hnode : t + tab.c i * h ∈ Icc t₀ (t₀ + T + 1) :=
    ⟨by nlinarith [ht.1, (hc i).1, hh.1], by nlinarith [ht.2, (hc i).2, hh.1, hh1]⟩
  have hmem : ∀ s ∈ Icc t₀ (t₀ + T + 1), (s, y t) ∈ S := fun s hs => ⟨hs, mem_image_of_mem y ht⟩
  -- the stages are bounded by `B`
  have hstage : ∀ j, ‖tab.explicitStages f h t (y t) j‖ ≤ B := fun j => by
    refine (tab.norm_explicitStages_le hc hlip (M := max M 0)
      (fun s hs => (hM _ (hmem s hs)).trans (le_max_left _ _)) ⟨hh.1, hh1⟩ ht j).trans ?_
    rw [hB]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [mul_nonneg hL hα]) j.2) (le_max_right _ _)
  have hw : ‖∑ j, if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0‖ ≤
      tab.entrySum * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0‖
        ≤ ∑ j, |tab.A i j| * B := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hstage j) (abs_nonneg _)
          · rw [norm_zero]; positivity
      _ = (∑ j, |tab.A i j|) * B := by rw [Finset.sum_mul]
      _ ≤ tab.entrySum * B := mul_le_mul_of_nonneg_right (tab.sum_abs_le_entrySum i) hB0
  -- the two halves of the estimate
  have h1 : ‖f (t + tab.c i * h)
      (y t + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0) -
      f (t + tab.c i * h) (y t)‖ ≤ L * tab.entrySum * B * h := by
    refine ((hlip _ hnode).norm_sub_le _ _).trans ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.1.le]
    calc (L : ℝ) * (h * ‖∑ j, if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0‖)
        ≤ L * (h * (tab.entrySum * B)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hh.1.le) hL
      _ = L * tab.entrySum * B * h := by ring
  have h2 : ‖f (t + tab.c i * h) (y t) - f t (y t)‖ ≤ ε / 2 := by
    have := hunif (t + tab.c i * h, y t) (hmem _ hnode) (t, y t)
      (hmem t ⟨ht.1, by linarith [ht.2]⟩) (by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, add_sub_cancel_left,
          abs_of_nonneg (mul_nonneg (hc i).1 hh.1.le), max_eq_left (mul_nonneg (hc i).1 hh.1.le)]
        nlinarith [(hc i).2, hh.1, hhδ])
    rw [dist_eq_norm] at this
    exact this.le
  have h3 : L * tab.entrySum * B * h ≤ ε / 2 := by
    have hpos : 0 < 2 * (L * tab.entrySum * B + 1) := by positivity
    calc L * tab.entrySum * B * h
        ≤ L * tab.entrySum * B * (ε / (2 * (L * tab.entrySum * B + 1))) := by gcongr
      _ ≤ (L * tab.entrySum * B + 1) * (ε / (2 * (L * tab.entrySum * B + 1))) := by
          gcongr; linarith
      _ = ε / 2 := by field_simp
  rw [explicitStages_apply]
  calc ‖f (t + tab.c i * h)
        (y t + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0) -
        f t (y t)‖
      ≤ ‖f (t + tab.c i * h)
          (y t + h • ∑ j, if j < i then tab.A i j • tab.explicitStages f h t (y t) j else 0) -
          f (t + tab.c i * h) (y t)‖ + ‖f (t + tab.c i * h) (y t) - f t (y t)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1.trans h3) h2
    _ = ε := add_halves ε

/-- **`∑ bᵢ = 1` gives consistency** ([quarteroni2000numerical] §11.8): an explicit tableau with
`∑_i b_i = 1` and nodes in `[0, 1]` is consistent along every `C¹` solution `y` of `y' = f(t, y)`
on `[t₀, t₀ + T]` of a field continuous on `[t₀, t₀ + T + 1] × E` and Lipschitz in the state
there: the increment `∑_i b_i K_i` converges to `f(t, y t)` uniformly in `t`
(`exists_forall_norm_explicitStages_sub_le`), and `OneStep.isConsistentFor_of_tendsto_increment`
concludes. -/
theorem isConsistentFor_of_sum_b_eq_one (hc : ∀ i, tab.c i ∈ Icc (0 : ℝ) 1)
    (hb : ∑ i, tab.b i = 1) (hf : ContinuousOn (Function.uncurry f) (Icc t₀ (t₀ + T + 1) ×ˢ univ))
    (hlip : ∀ s ∈ Icc t₀ (t₀ + T + 1), LipschitzWith L (f s))
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s) :
    OneStep.IsConsistentFor (tab.explicitIncrement f) t₀ T y := by
  have hyc : ContinuousOn y (Icc t₀ (t₀ + T)) := HasDerivWithinAt.continuousOn hy
  refine OneStep.isConsistentFor_of_tendsto_increment hy
    (hf.comp (continuousOn_id.prodMk hyc) fun s hs =>
      ⟨⟨hs.1, show s ≤ t₀ + T + 1 by linarith [hs.2]⟩, mem_univ _⟩)
    fun ε hε => ?_
  have hβ : (0 : ℝ) < ∑ i, |tab.b i| + 1 := by positivity
  obtain ⟨η, hη, hstage⟩ := tab.exists_forall_norm_explicitStages_sub_le hc hf hlip hyc
    (div_pos hε hβ)
  refine ⟨η, hη, fun h hh t ht _ => ?_⟩
  rw [explicitIncrement_apply]
  have e : ∑ i, tab.b i • tab.explicitStages f h t (y t) i - f t (y t) =
      ∑ i, tab.b i • (tab.explicitStages f h t (y t) i - f t (y t)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hb, one_smul]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖tab.b i • (tab.explicitStages f h t (y t) i - f t (y t))‖
      ≤ ∑ i, |tab.b i| * (ε / (∑ i, |tab.b i| + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hstage h hh t ht i) (abs_nonneg _)
    _ = (∑ i, |tab.b i|) * (ε / (∑ i, |tab.b i| + 1)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, |tab.b i| + 1) * (ε / (∑ i, |tab.b i| + 1)) := by gcongr; linarith
    _ = ε := by field_simp

/-- On a constant field every explicit stage is that constant. -/
theorem explicitStages_const (c : E) (h t : ℝ) (u : E) (i : Fin s) :
    tab.explicitStages (fun _ _ => c) h t u i = c := by
  rw [explicitStages_apply]

/-- **Consistency forces `∑ bᵢ = 1`** ([quarteroni2000numerical] §11.8, the converse): if the
explicit method is consistent along the solution `y t = t` of `y' = 1` on some `[t₀, t₀ + T]`,
`T > 0`, then `∑_i b_i = 1`. There every stage is `1` and the truncation error is the constant
`1 - ∑_i b_i`, which must tend to zero. -/
theorem sum_b_eq_one_of_isConsistentFor {t₀ T : ℝ} (hT : 0 < T)
    (hcons : OneStep.IsConsistentFor (tab.explicitIncrement fun _ _ => (1 : ℝ)) t₀ T id) :
    ∑ i, tab.b i = 1 := by
  have hlte : ∀ h : ℝ, h ≠ 0 → ∀ t,
      OneStep.lte (tab.explicitIncrement fun _ _ => (1 : ℝ)) h id t = 1 - ∑ i, tab.b i := by
    intro h hh t
    simp [OneStep.lte, explicitIncrement_apply, explicitStages_const, hh]
  have hglob : ∀ h ∈ Ioc 0 T,
      OneStep.globalLte (tab.explicitIncrement fun _ _ => (1 : ℝ)) t₀ T id h =
        |1 - ∑ i, tab.b i| := by
    intro h hh
    have hN : 1 ≤ gridCount T h := (le_gridCount_iff hT.le hh.1).2 (by simpa using hh.2)
    have : Nonempty (Fin (gridCount T h)) := ⟨⟨0, hN⟩⟩
    simp only [OneStep.globalLte, hlte h hh.1.ne', Real.norm_eq_abs, ciSup_const]
  have hev : OneStep.globalLte (tab.explicitIncrement fun _ _ => (1 : ℝ)) t₀ T id =ᶠ[𝓝[>] 0]
      fun _ => |1 - ∑ i, tab.b i| := by
    filter_upwards [Ioc_mem_nhdsGT hT] with h hh using hglob h hh
  have h0 : |1 - ∑ i, tab.b i| = 0 :=
    (tendsto_nhds_unique (hcons.congr' hev) tendsto_const_nhds).symm
  rw [abs_eq_zero, sub_eq_zero] at h0
  exact h0.symm

end Consistency

end ButcherTableau

/-! ### Autonomization

A non-autonomous problem `y' = f(t, y)` on `E` is the autonomous problem `Y' = G(Y)` on `ℝ × E`
for `G(t, v) = (1, f t v)` and `Y s = (s, y s)`. A Runge–Kutta method satisfying the row-sum
condition does not see the difference: its stages for `G` are `L_i = (1, K_i)`, its increment is
`(1, Φ)` when the tableau is consistent, and its local truncation error along `Y` is
`(0, τ)` — so the order along `y` and the order along `Y` are the same
(`hasOrderFor_autonomize_iff`). This is the reduction that makes the order conditions of a
non-autonomous problem those of an autonomous one: the elementary differentials of `G` on `ℝ × E`
replace the mixed partial derivatives of `f` in `(t, v)`. -/

section Autonomization

/-- **The autonomized field** of `f : ℝ → E → E`: the field `G(t, v) = (1, f t v)` on `ℝ × E`,
whose integral curves are `s ↦ (s, y s)` with `y' = f(·, y)`. It is constant in its own time
argument, so it is a field on `ℝ × E` in the sense of `ODE` and an autonomous one. -/
def autonomize (f : ℝ → E → E) : ℝ → ℝ × E → ℝ × E := fun _ p => (1, f p.1 p.2)

namespace ButcherTableau

variable {s : ℕ} (tab : ButcherTableau s) {f : ℝ → E → E} {h t t₀ T : ℝ} {u : E}

/-- **The stages of the autonomized field are the stages of `f` with the time appended**:
`L_i = (1, K_i)`, for an explicit tableau satisfying the row-sum condition `c_i = ∑_j a_ij`. The
time component of `(t₀, u) + h ∑_{j<i} a_ij L_j` is `t₀ + h ∑_{j<i} a_ij = t₀ + c_i h`, which is
exactly the time at which `K_i` evaluates `f`. -/
theorem explicitStages_autonomize (hex : tab.IsExplicit) (hrow : tab.IsRowSum) (i : Fin s) :
    tab.explicitStages (autonomize f) h t (t₀, u) i = (1, tab.explicitStages f h t₀ u i) := by
  have key : ∀ m, ∀ i : Fin s, i.1 < m →
      tab.explicitStages (autonomize f) h t (t₀, u) i = (1, tab.explicitStages f h t₀ u i) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [explicitStages_apply, explicitStages_apply, autonomize]
      have hsum : ∀ j : Fin s, (if j < i then tab.A i j • tab.explicitStages (autonomize f) h t
          (t₀, u) j else 0) = (if j < i then tab.A i j else 0,
            if j < i then tab.A i j • tab.explicitStages f h t₀ u j else 0) := by
        intro j
        split_ifs with hj
        · rw [ih j (by omega)]
          simp [Prod.smul_mk]
        · rfl
      rw [Finset.sum_congr rfl fun j _ => hsum j]
      have hfst : (∑ j : Fin s, ((if j < i then tab.A i j else 0 : ℝ),
          (if j < i then tab.A i j • tab.explicitStages f h t₀ u j else 0 : E))) =
          (∑ j : Fin s, (if j < i then tab.A i j else 0 : ℝ),
            ∑ j : Fin s, (if j < i then tab.A i j • tab.explicitStages f h t₀ u j else 0 : E)) := by
        rw [Prod.mk.injEq]
        exact ⟨by rw [Prod.fst_sum], by rw [Prod.snd_sum]⟩
      rw [hfst]
      have hc : ∑ j : Fin s, (if j < i then tab.A i j else 0 : ℝ) = tab.c i := by
        rw [hrow i]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hj
        · rfl
        · exact (hex i j (not_lt.1 hj)).symm
      simp only [Prod.smul_mk, Prod.mk_add_mk, hc]
      rw [smul_eq_mul, mul_comm h (tab.c i)]
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/-- **The increment of the autonomized field** is `(1, Φ)`: the time component is `∑_i b_i = 1`
by consistency of the tableau. -/
theorem explicitIncrement_autonomize (hex : tab.IsExplicit) (hrow : tab.IsRowSum)
    (hcons : tab.IsConsistent) (w : ℝ × E) :
    tab.explicitIncrement (autonomize f) t (t₀, u) w h = (1, tab.explicitIncrement f t₀ u u h) := by
  rw [explicitIncrement_apply, explicitIncrement_apply]
  have hterm : ∀ i : Fin s, tab.b i • tab.explicitStages (autonomize f) h t (t₀, u) i
      = ((tab.b i : ℝ), tab.b i • tab.explicitStages f h t₀ u i) := by
    intro i
    rw [tab.explicitStages_autonomize hex hrow]
    simp [Prod.smul_mk]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Prod.mk.injEq]
  exact ⟨by rw [Prod.fst_sum]; exact hcons, by rw [Prod.snd_sum]⟩

/-- **The local truncation error of the autonomized method along `Y s = (s, y s)`** is
`(0, τ)`: the time components of `h⁻¹ (Y(t+h) - Y(t))` and of the increment are both `1`. -/
theorem lte_autonomize (hex : tab.IsExplicit) (hrow : tab.IsRowSum) (hcons : tab.IsConsistent)
    (y : ℝ → E) (hh : h ≠ 0) :
    OneStep.lte (tab.explicitIncrement (autonomize f)) h (fun s => (s, y s)) t
      = (0, OneStep.lte (tab.explicitIncrement f) h y t) := by
  rw [OneStep.lte, OneStep.lte, tab.explicitIncrement_autonomize hex hrow hcons]
  have hsub : ((t + h, y (t + h)) : ℝ × E) - (t, y t) = (h, y (t + h) - y t) := by
    rw [Prod.mk_sub_mk]
    simp
  rw [hsub, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul, inv_mul_cancel₀ hh]
  simp
  rfl

/-- **The global truncation errors agree** for a nonzero step, since `‖(0, τ)‖ = ‖τ‖` in the
product norm. -/
theorem globalLte_autonomize (hex : tab.IsExplicit) (hrow : tab.IsRowSum)
    (hcons : tab.IsConsistent) (y : ℝ → E) (hh : h ≠ 0) :
    OneStep.globalLte (tab.explicitIncrement (autonomize f)) t₀ T (fun s => (s, y s)) h
      = OneStep.globalLte (tab.explicitIncrement f) t₀ T y h := by
  rw [OneStep.globalLte, OneStep.globalLte]
  refine congrArg _ (funext fun n => ?_)
  rw [tab.lte_autonomize hex hrow hcons y hh, Prod.norm_mk, norm_zero]
  exact max_eq_right (norm_nonneg _)

/-- **Order is invariant under autonomization**: an explicit tableau satisfying the row-sum
condition and consistent has order `p` along `y` for `f` exactly when it has order `p` along
`s ↦ (s, y s)` for the autonomized field. This is what reduces the order conditions of a
non-autonomous problem to those of an autonomous one. -/
theorem hasOrderFor_autonomize_iff (hex : tab.IsExplicit) (hrow : tab.IsRowSum)
    (hcons : tab.IsConsistent) (y : ℝ → E) (p : ℕ) :
    OneStep.HasOrderFor (tab.explicitIncrement (autonomize f)) t₀ T (fun s => (s, y s)) p ↔
      OneStep.HasOrderFor (tab.explicitIncrement f) t₀ T y p := by
  have heq : OneStep.globalLte (tab.explicitIncrement (autonomize f)) t₀ T (fun s => (s, y s))
      =ᶠ[𝓝[>] (0 : ℝ)] OneStep.globalLte (tab.explicitIncrement f) t₀ T y := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact tab.globalLte_autonomize hex hrow hcons y (ne_of_gt hh)
  exact ⟨fun hb => hb.congr' heq EventuallyEq.rfl, fun hb => hb.congr' heq.symm EventuallyEq.rfl⟩

end ButcherTableau

end Autonomization

/-! ### The named explicit tableaux -/

namespace ButcherTableau

/-- **Heun's method as a tableau** ([quarteroni2000numerical] Exercise 11.12): the two-stage
explicit method with `A = !![0, 0; 1, 0]`, `b = (1/2, 1/2)`, `c = (0, 1)`. -/
noncomputable def heun : ButcherTableau 2 := ⟨!![0, 0; 1, 0], ![1 / 2, 1 / 2], ![0, 1]⟩

/-- **The modified Euler method as a tableau** ([quarteroni2000numerical] (11.91), Exercise
11.12): `A = !![0, 0; 1/2, 0]`, `b = (0, 1)`, `c = (0, 1/2)`. -/
noncomputable def modifiedEuler : ButcherTableau 2 := ⟨!![0, 0; 1 / 2, 0], ![0, 1], ![0, 1 / 2]⟩

/-- Heun's tableau is explicit. -/
theorem heun_isExplicit : heun.IsExplicit := by
  intro i j hij
  rw [Fin.le_def] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [heun]

/-- The first stage of Heun's tableau. -/
theorem explicitStages_heun_zero (f : ℝ → E → E) (h t : ℝ) (u : E) :
    heun.explicitStages f h t u 0 = f t u := by
  rw [explicitStages_apply]; simp [heun]

/-- The second stage of Heun's tableau. -/
theorem explicitStages_heun_one (f : ℝ → E → E) (h t : ℝ) (u : E) :
    heun.explicitStages f h t u 1 = f (t + h) (u + h • f t u) := by
  rw [explicitStages_apply, Fin.sum_univ_two, explicitStages_heun_zero]; simp [heun]

/-- Heun's tableau satisfies the row-sum condition. -/
theorem heun_isRowSum : heun.IsRowSum := by
  intro i; fin_cases i <;> simp [heun, Fin.sum_univ_two]

/-- Heun's tableau is consistent. -/
theorem heun_isConsistent : heun.IsConsistent := by
  simp [IsConsistent, heun, Fin.sum_univ_two]; norm_num

/-- The explicit increment of Heun's tableau is Heun's method `OneStep.heun`. -/
theorem explicitIncrement_heun (f : ℝ → E → E) : heun.explicitIncrement f = OneStep.heun f := by
  ext t u v h
  rw [explicitIncrement_apply, Fin.sum_univ_two, explicitStages_heun_zero,
    explicitStages_heun_one]
  simp [heun, OneStep.heun, smul_add]

/-- The modified Euler tableau is explicit. -/
theorem modifiedEuler_isExplicit : modifiedEuler.IsExplicit := by
  intro i j hij
  rw [Fin.le_def] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [modifiedEuler]

/-- The first stage of the modified Euler tableau. -/
theorem explicitStages_modifiedEuler_zero (f : ℝ → E → E) (h t : ℝ) (u : E) :
    modifiedEuler.explicitStages f h t u 0 = f t u := by
  rw [explicitStages_apply]; simp [modifiedEuler]

/-- The second stage of the modified Euler tableau. -/
theorem explicitStages_modifiedEuler_one (f : ℝ → E → E) (h t : ℝ) (u : E) :
    modifiedEuler.explicitStages f h t u 1 = f (t + h / 2) (u + (h / 2) • f t u) := by
  rw [explicitStages_apply, Fin.sum_univ_two, explicitStages_modifiedEuler_zero]
  simp [modifiedEuler, smul_smul]
  ring_nf

/-- The modified Euler tableau satisfies the row-sum condition. -/
theorem modifiedEuler_isRowSum : modifiedEuler.IsRowSum := by
  intro i; fin_cases i <;> simp [modifiedEuler, Fin.sum_univ_two]

/-- **The modified Euler method** ([quarteroni2000numerical] (11.91)):
`u_{n+1} = u_n + h f(t_n + h/2, u_n + (h/2) f(t_n, u_n))`. -/
theorem explicitIncrement_modifiedEuler (f : ℝ → E → E) (t : ℝ) (u v : E) (h : ℝ) :
    modifiedEuler.explicitIncrement f t u v h = f (t + h / 2) (u + (h / 2) • f t u) := by
  rw [explicitIncrement_apply, Fin.sum_univ_two, explicitStages_modifiedEuler_one]
  simp [modifiedEuler]

end ButcherTableau

/-- **The classical fourth-order Runge–Kutta method** ([quarteroni2000numerical] (11.73),
Exercise 11.13): `A = !![0,0,0,0; 1/2,0,0,0; 0,1/2,0,0; 0,0,1,0]`, `b = (1/6, 1/3, 1/3, 1/6)`,
`c = (0, 1/2, 1/2, 1)`. -/
noncomputable def rk4 : ButcherTableau 4 where
  A := !![0, 0, 0, 0; 1 / 2, 0, 0, 0; 0, 1 / 2, 0, 0; 0, 0, 1, 0]
  b := ![1 / 6, 1 / 3, 1 / 3, 1 / 6]
  c := ![0, 1 / 2, 1 / 2, 1]

/-- The classical tableau is explicit. -/
theorem rk4_isExplicit : rk4.IsExplicit := by
  intro i j hij
  rw [Fin.le_def] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [rk4]

/-- The classical tableau satisfies the row-sum condition. -/
theorem rk4_isRowSum : rk4.IsRowSum := by
  intro i; fin_cases i <;> simp [rk4, Fin.sum_univ_four]

/-- The classical tableau is consistent. -/
theorem rk4_isConsistent : rk4.IsConsistent := by
  simp [ButcherTableau.IsConsistent, rk4, Fin.sum_univ_four]; norm_num

/-- The nodes of the classical tableau lie in `[0, 1]`. -/
theorem rk4_c_mem_Icc (i : Fin 4) : rk4.c i ∈ Icc (0 : ℝ) 1 := by
  fin_cases i <;> simp [rk4] <;> norm_num

/-- **The classical method, written out** ([quarteroni2000numerical] (11.73)):
`u_{n+1} = u_n + (h/6)(K₁ + 2K₂ + 2K₃ + K₄)` with `K₁ = f(t, u)`, `K₂ = f(t + h/2, u + (h/2)K₁)`,
`K₃ = f(t + h/2, u + (h/2)K₂)`, `K₄ = f(t + h, u + hK₃)`. -/
theorem explicitIncrement_rk4 (f : ℝ → E → E) (t : ℝ) (u v : E) (h : ℝ) :
    rk4.explicitIncrement f t u v h =
      (1 / 6 : ℝ) • (f t u + (2 : ℝ) • f (t + h / 2) (u + (h / 2) • f t u) +
        (2 : ℝ) • f (t + h / 2) (u + (h / 2) • f (t + h / 2) (u + (h / 2) • f t u)) +
        f (t + h) (u + h • f (t + h / 2) (u + (h / 2) • f (t + h / 2) (u + (h / 2) • f t u)))) := by
  have h0 : rk4.explicitStages f h t u 0 = f t u := by
    rw [ButcherTableau.explicitStages_apply]; simp [rk4]
  have h1 : rk4.explicitStages f h t u 1 = f (t + h / 2) (u + (h / 2) • f t u) := by
    rw [ButcherTableau.explicitStages_apply, Fin.sum_univ_four, h0]
    simp [rk4, smul_smul]
    ring_nf
  have h2 : rk4.explicitStages f h t u 2 =
      f (t + h / 2) (u + (h / 2) • f (t + h / 2) (u + (h / 2) • f t u)) := by
    rw [ButcherTableau.explicitStages_apply, Fin.sum_univ_four, h1]
    simp [rk4, smul_smul]
    ring_nf
  have h3 : rk4.explicitStages f h t u 3 =
      f (t + h) (u + h • f (t + h / 2) (u + (h / 2) • f (t + h / 2) (u + (h / 2) • f t u))) := by
    rw [ButcherTableau.explicitStages_apply, Fin.sum_univ_four, h2]
    simp [rk4]
  rw [ButcherTableau.explicitIncrement_apply, Fin.sum_univ_four, h0, h1, h2, h3]
  simp [rk4]
  module

/-- **The eight order-four conditions** of the classical tableau, `∑ b_i = 1`, `∑ b_i c_i = 1/2`,
`∑ b_i c_i² = 1/3`, `∑ b_i a_ij c_j = 1/6`, `∑ b_i c_i³ = 1/4`, `∑ b_i c_i a_ij c_j = 1/8`,
`∑ b_i a_ij c_j² = 1/12`, `∑ b_i a_ij a_jk c_k = 1/24` — the algebraic content of its fourth
order ([hairer1993solving] Table II.2.2). -/
theorem rk4_orderConditions :
    ∑ i, rk4.b i = 1 ∧ ∑ i, rk4.b i * rk4.c i = 1 / 2 ∧ ∑ i, rk4.b i * rk4.c i ^ 2 = 1 / 3 ∧
      ∑ i, ∑ j, rk4.b i * rk4.A i j * rk4.c j = 1 / 6 ∧ ∑ i, rk4.b i * rk4.c i ^ 3 = 1 / 4 ∧
      ∑ i, ∑ j, rk4.b i * rk4.c i * rk4.A i j * rk4.c j = 1 / 8 ∧
      ∑ i, ∑ j, rk4.b i * rk4.A i j * rk4.c j ^ 2 = 1 / 12 ∧
      ∑ i, ∑ j, ∑ k, rk4.b i * rk4.A i j * rk4.A j k * rk4.c k = 1 / 24 := by
  simp [rk4, Fin.sum_univ_four]
  norm_num

/-! ### Embedded pairs -/

/-- **An embedded pair** ([quarteroni2000numerical] (11.76)): a tableau with a second weight
vector `b̂`; the two methods `(c, A, b)` and `(c, A, b̂)` share their stages. -/
structure EmbeddedPair (s : ℕ) extends ButcherTableau s where
  /-- The second weight vector `b̂`. -/
  bhat : Fin s → ℝ

namespace EmbeddedPair

variable {s : ℕ} (P : EmbeddedPair s)

/-- The tableau `(c, A, b̂)` of the second method of the pair. -/
def toTableauHat : ButcherTableau s := ⟨P.A, P.bhat, P.c⟩

/-- The explicit stages only depend on `A` and `c`. -/
theorem _root_.ODE.ButcherTableau.explicitStages_congr {tab tab' : ButcherTableau s}
    (hA : tab.A = tab'.A) (hc : tab.c = tab'.c) (f : ℝ → E → E) (h t : ℝ) (u : E) :
    tab.explicitStages f h t u = tab'.explicitStages f h t u := by
  have key : ∀ m, ∀ i : Fin s, i.1 < m →
      tab.explicitStages f h t u i = tab'.explicitStages f h t u i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rw [ButcherTableau.explicitStages_apply, ButcherTableau.explicitStages_apply, hA, hc]
      congr 3
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · rw [ih j (by omega)]
      · rfl
  funext i
  exact key (i.1 + 1) i (Nat.lt_succ_self _)

/-- The two tableaux of a pair have the same explicit stages. -/
theorem explicitStages_toTableauHat (f : ℝ → E → E) (h t : ℝ) (u : E) :
    P.toTableauHat.explicitStages f h t u = P.toButcherTableau.explicitStages f h t u :=
  ButcherTableau.explicitStages_congr (tab := P.toTableauHat) (tab' := P.toButcherTableau) rfl rfl
    f h t u

/-- **The error indicator** ([quarteroni2000numerical] §11.8.2): `h ∑_i (b_i - b̂_i) K_i`, the
difference of the two solutions of the pair, computed from the shared stages. -/
noncomputable def errorIndicator (f : ℝ → E → E) (h t : ℝ) (u : E) : E :=
  h • ∑ i, (P.b i - P.bhat i) • P.toButcherTableau.explicitStages f h t u i

/-- The error indicator is the difference `u_{n+1} - û_{n+1}` of the two solutions of the pair
sharing the stages, so it needs no extra evaluation of the field. -/
theorem errorIndicator_eq_sub (f : ℝ → E → E) (h t : ℝ) (u : E) :
    P.errorIndicator f h t u =
      (u + h • P.toButcherTableau.explicitIncrement f t u u h) -
        (u + h • P.toTableauHat.explicitIncrement f t u u h) := by
  simp only [errorIndicator, ButcherTableau.explicitIncrement_apply, explicitStages_toTableauHat,
    sub_smul, Finset.sum_sub_distrib, smul_sub]
  abel

end EmbeddedPair

/-- **The Runge–Kutta–Fehlberg 4(5) pair** ([quarteroni2000numerical] §11.8.2), with the
standard coefficients: `b` is the fourth-order method, `b̂` the fifth-order one, and
`E = b - b̂ = (1/360, 0, -128/4275, -2197/75240, 1/50, 2/55)`. The book's table is damaged in the
source (missing denominators); the standard values are used. -/
noncomputable def rkf45 : EmbeddedPair 6 where
  A := !![0, 0, 0, 0, 0, 0;
    1 / 4, 0, 0, 0, 0, 0;
    3 / 32, 9 / 32, 0, 0, 0, 0;
    1932 / 2197, -7200 / 2197, 7296 / 2197, 0, 0, 0;
    439 / 216, -8, 3680 / 513, -845 / 4104, 0, 0;
    -8 / 27, 2, -3544 / 2565, 1859 / 4104, -11 / 40, 0]
  b := ![25 / 216, 0, 1408 / 2565, 2197 / 4104, -1 / 5, 0]
  c := ![0, 1 / 4, 3 / 8, 12 / 13, 1, 1 / 2]
  bhat := ![16 / 135, 0, 6656 / 12825, 28561 / 56430, -9 / 50, 2 / 55]

/-- The Fehlberg tableau is explicit. -/
theorem rkf45_isExplicit : rkf45.toButcherTableau.IsExplicit := by
  intro i j hij
  rw [Fin.le_def] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [rkf45]

/-- The Fehlberg tableau satisfies the row-sum condition. -/
theorem rkf45_isRowSum : rkf45.toButcherTableau.IsRowSum := by
  intro i; fin_cases i <;> simp [rkf45, Fin.sum_univ_succ] <;> norm_num

/-- Both weight vectors of the Fehlberg pair sum to `1`. -/
theorem rkf45_sum_b : ∑ i, rkf45.b i = 1 ∧ ∑ i, rkf45.bhat i = 1 := by
  simp [rkf45, Fin.sum_univ_succ]; norm_num

/-- The error coefficients of the Fehlberg pair as the book prints them,
`(1/360, 0, -128/4275, -2197/75240, 1/50, 2/55)`: they are `b̂ - b` (the book writes `E = b - b̂`,
which has the opposite sign for its `b` of order `4` and `b̂` of order `5`). -/
theorem rkf45_bhat_sub_b :
    (fun i => rkf45.bhat i - rkf45.b i) =
      ![1 / 360, 0, -128 / 4275, -2197 / 75240, 1 / 50, 2 / 55] := by
  funext i; fin_cases i <;> simp [rkf45] <;> norm_num

/-! ### The implicit tableaux of §11.8.3 -/

namespace ButcherTableau

/-- **The implicit midpoint rule** ([quarteroni2000numerical] §11.8.3), the one-stage
Gauss–Legendre method: `A = !![1/2]`, `b = (1)`, `c = (1/2)`. -/
noncomputable def implicitMidpoint : ButcherTableau 1 := ⟨!![1 / 2], ![1], ![1 / 2]⟩

/-- **The step of the implicit midpoint rule**:
`u_{n+1} = u_n + h f(t_n + h/2, (u_n + u_{n+1})/2)` ([quarteroni2000numerical] §11.8.3). -/
theorem stepRel_implicitMidpoint_iff (f : ℝ → E → E) (h t : ℝ) (u v : E) :
    implicitMidpoint.stepRel f h t u v ↔ v = u + h • f (t + h / 2) ((2 : ℝ)⁻¹ • (u + v)) := by
  simp only [stepRel_apply, IsStages, implicitMidpoint, Fin.forall_fin_one, Fin.sum_univ_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, one_smul]
  constructor
  · rintro ⟨K, hK, rfl⟩
    have e : u + h • ((1 / 2 : ℝ) • K 0) = (2 : ℝ)⁻¹ • (u + (u + h • K 0)) := by module
    rw [← e, show t + h / 2 = t + 1 / 2 * h by ring, ← hK]
  · intro hv
    refine ⟨fun _ => f (t + h / 2) ((2 : ℝ)⁻¹ • (u + v)), ?_, hv⟩
    have e : u + h • ((1 / 2 : ℝ) • f (t + h / 2) ((2 : ℝ)⁻¹ • (u + v))) =
        (2 : ℝ)⁻¹ • (u + v) := by
      conv_rhs => rw [hv]
      module
    rw [e, show t + 1 / 2 * h = t + h / 2 by ring]

/-- The order conditions `∑ b = 1`, `∑ b c = 1/2` of the implicit midpoint rule. -/
theorem implicitMidpoint_orderConditions :
    ∑ i, implicitMidpoint.b i = 1 ∧ ∑ i, implicitMidpoint.b i * implicitMidpoint.c i = 1 / 2 := by
  simp [implicitMidpoint]

/-- **The two-stage Gauss–Legendre tableau** of order `4` ([quarteroni2000numerical] §11.8.3):
`c = (1/2 - √3/6, 1/2 + √3/6)`, `A = !![1/4, 1/4 - √3/6; 1/4 + √3/6, 1/4]`, `b = (1/2, 1/2)`; the
nodes are the roots of the Legendre polynomial `L₂` in `x = 2c - 1`. -/
noncomputable def gaussLegendre2 : ButcherTableau 2 :=
  ⟨!![1 / 4, 1 / 4 - Real.sqrt 3 / 6; 1 / 4 + Real.sqrt 3 / 6, 1 / 4], ![1 / 2, 1 / 2],
    ![1 / 2 - Real.sqrt 3 / 6, 1 / 2 + Real.sqrt 3 / 6]⟩

/-- **The collocation identities of the two-stage Gauss–Legendre tableau**
([quarteroni2000numerical] §11.8.3): `∑_j c_j^{k-1} a_ij = c_i^k / k` and
`∑_j c_j^{k-1} b_j = 1/k` for `k = 1, 2`. -/
theorem gaussLegendre2_collocation :
    (∀ i, ∑ j, gaussLegendre2.A i j = gaussLegendre2.c i) ∧
      (∀ i, ∑ j, gaussLegendre2.c j * gaussLegendre2.A i j = gaussLegendre2.c i ^ 2 / 2) ∧
      ∑ j, gaussLegendre2.b j = 1 ∧ ∑ j, gaussLegendre2.c j * gaussLegendre2.b j = 1 / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp [gaussLegendre2, Fin.sum_univ_two] <;> ring
  · fin_cases i <;> simp [gaussLegendre2, Fin.sum_univ_two] <;> linear_combination (-1 / 24) * h3
  · simp [gaussLegendre2, Fin.sum_univ_two]; norm_num
  · simp [gaussLegendre2, Fin.sum_univ_two]; ring

/-- The two-stage Gauss–Legendre tableau satisfies the row-sum condition. -/
theorem gaussLegendre2_isRowSum : gaussLegendre2.IsRowSum := fun i =>
  (gaussLegendre2_collocation.1 i).symm

/-- **The one-stage Radau IIA tableau**, `A = !![1]`, `b = (1)`, `c = (1)`: backward Euler
([quarteroni2000numerical] §11.8.3). -/
noncomputable def radauIIA1 : ButcherTableau 1 := ⟨!![1], ![1], ![1]⟩

/-- **The two-stage Radau IIA tableau** of order `3` ([quarteroni2000numerical] §11.8.3):
`c = (1/3, 1)`, `A = !![5/12, -1/12; 3/4, 1/4]`, `b = (3/4, 1/4)`. -/
noncomputable def radauIIA2 : ButcherTableau 2 :=
  ⟨!![5 / 12, -1 / 12; 3 / 4, 1 / 4], ![3 / 4, 1 / 4], ![1 / 3, 1]⟩

/-- **The two-stage Lobatto IIIA tableau**, `c = (0, 1)`, `A = !![0, 0; 1/2, 1/2]`,
`b = (1/2, 1/2)`: Crank–Nicolson ([quarteroni2000numerical] §11.8.3). -/
noncomputable def lobattoIIIA2 : ButcherTableau 2 :=
  ⟨!![0, 0; 1 / 2, 1 / 2], ![1 / 2, 1 / 2], ![0, 1]⟩

/-- **The three-stage DIRK tableau** with parameter `μ`, a root of `3μ³ - 3μ - 1 = 0`
([quarteroni2000numerical] §11.8.3): `c = ((1+μ)/2, 1/2, (1-μ)/2)`,
`A = !![(1+μ)/2, 0, 0; -μ/2, (1+μ)/2, 0; 1+μ, -1-2μ, (1+μ)/2]`,
`b = (1/(6μ²), 1 - 1/(3μ²), 1/(6μ²))`. -/
noncomputable def dirk3 (μ : ℝ) : ButcherTableau 3 :=
  ⟨!![(1 + μ) / 2, 0, 0; -μ / 2, (1 + μ) / 2, 0; 1 + μ, -1 - 2 * μ, (1 + μ) / 2],
    ![1 / (6 * μ ^ 2), 1 - 1 / (3 * μ ^ 2), 1 / (6 * μ ^ 2)], ![(1 + μ) / 2, 1 / 2, (1 - μ) / 2]⟩

/-- The DIRK tableau is semi-implicit. -/
theorem dirk3_isSemiImplicit (μ : ℝ) : (dirk3 μ).IsSemiImplicit := by
  intro i j hij
  rw [Fin.lt_def] at hij
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp [dirk3]

/-- The one-stage Radau IIA method is backward Euler. -/
theorem stepRel_radauIIA1 (f : ℝ → E → E) :
    radauIIA1.stepRel f = OneStep.ofIncrement (OneStep.backwardEuler f) := by
  ext h t u v
  simp only [stepRel_apply, IsStages, radauIIA1, Fin.forall_fin_one, Fin.sum_univ_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, one_smul, one_mul,
    OneStep.ofIncrement_apply, OneStep.backwardEuler]
  constructor
  · rintro ⟨K, hK, rfl⟩
    rw [← hK]
  · intro hv
    exact ⟨fun _ => f (t + h) v, by rw [← hv], hv⟩

/-- The two-stage Lobatto IIIA method is Crank–Nicolson. -/
theorem stepRel_lobattoIIIA2 (f : ℝ → E → E) :
    lobattoIIIA2.stepRel f = OneStep.ofIncrement (OneStep.crankNicolson f) := by
  ext h t u v
  simp only [stepRel_apply, IsStages, lobattoIIIA2, Fin.forall_fin_two, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, OneStep.ofIncrement_apply, OneStep.crankNicolson, zero_smul,
    add_zero, smul_zero, zero_mul, one_mul, smul_add]
  constructor
  · rintro ⟨K, ⟨hK0, hK1⟩, rfl⟩
    rw [← hK0, ← hK1]
    module
  · intro hv
    refine ⟨![f t u, f (t + h) v], ⟨by simp, ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      congr 1
      conv_lhs => rw [hv]
      module
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      conv_lhs => rw [hv]
      module

end ButcherTableau

/-! ### The stability function -/

namespace ButcherTableau

variable {s : ℕ} (tab : ButcherTableau s)

/-- The coefficient matrix `A` read in `ℂ`. -/
def complexA : Matrix (Fin s) (Fin s) ℂ := tab.A.map ((↑) : ℝ → ℂ)

/-- The weights `b` read in `ℂ`. -/
def complexB : Fin s → ℂ := fun i => (tab.b i : ℂ)

/-- The entries of the complexified coefficient matrix. -/
@[simp] theorem complexA_apply (i j : Fin s) : tab.complexA i j = (tab.A i j : ℂ) := rfl

/-- The entries of the complexified weights. -/
@[simp] theorem complexB_apply (i : Fin s) : tab.complexB i = (tab.b i : ℂ) := rfl

/-- **The stability function** ([quarteroni2000numerical] §11.8.4):
`R(z) = 1 + z bᵀ (I - z A)⁻¹ 𝟙`, with Mathlib's `Matrix.inv` (which is `0` on a singular
matrix, so the formula is meaningful when `I - z A` is invertible). -/
noncomputable def stabilityFunction (z : ℂ) : ℂ :=
  1 + z * (tab.complexB ⬝ᵥ ((1 - z • tab.complexA)⁻¹ *ᵥ fun _ => 1))

/-- The sum `∑_i b_i K_i` of complex stages is the dot product with the complexified weights. -/
theorem sum_smul_eq_dotProduct (K : Fin s → ℂ) : ∑ i, tab.b i • K i = tab.complexB ⬝ᵥ K := by
  simp [dotProduct, Complex.real_smul]

/-- **The stage system on the test equation** ([quarteroni2000numerical] (11.77)):
`K` are stages of the method on `y' = λ y` at `u` iff `(I - hλ A) K = λ u 𝟙`. -/
theorem isStages_testField_iff {lam : ℂ} {h t : ℝ} {u : ℂ} (K : Fin s → ℂ) :
    tab.IsStages (testField lam) h t u K ↔
      (1 - (h * lam) • tab.complexA) *ᵥ K = (lam * u) • fun _ => (1 : ℂ) := by
  simp only [IsStages, testField, Complex.real_smul, funext_iff, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, complexA_apply, mul_one]
  refine forall_congr' fun i => ?_
  constructor <;> intro H <;> linear_combination H

/-- **One step on the test equation multiplies by `R(hλ)`** ([quarteroni2000numerical]
§11.8.4): if `I - hλ A` is invertible, `v` is admissible from `u` iff `v = R(hλ) u`. -/
theorem stepRel_testField_iff {lam : ℂ} {h : ℝ}
    (hinv : IsUnit (1 - (h * lam) • tab.complexA)) (t : ℝ) (u v : ℂ) :
    tab.stepRel (testField lam) h t u v ↔ v = tab.stabilityFunction (h * lam) * u := by
  set M := 1 - (h * lam) • tab.complexA with hM
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hinv
  have hval : ∀ K : Fin s → ℂ, M *ᵥ K = (lam * u) • (fun _ => (1 : ℂ)) →
      u + h • ∑ i, tab.b i • K i = tab.stabilityFunction (h * lam) * u := by
    intro K hK
    have hK' : K = (lam * u) • (M⁻¹ *ᵥ fun _ => (1 : ℂ)) := by
      rw [← Matrix.mulVec_smul, ← hK, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    rw [sum_smul_eq_dotProduct, hK', dotProduct_smul, stabilityFunction, Complex.real_smul,
      smul_eq_mul]
    ring
  have hsol : M *ᵥ ((lam * u) • (M⁻¹ *ᵥ fun _ => (1 : ℂ))) = (lam * u) • fun _ => (1 : ℂ) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  rw [stepRel_apply]
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact hval K ((tab.isStages_testField_iff K).1 hK)
  · intro hv
    exact ⟨_, (tab.isStages_testField_iff _).2 hsol, hv.trans (hval _ hsol).symm⟩

/-- The orbits of the method on the test equation are geometric: `u_n = R(hλ)^n u_0` when
`I - hλ A` is invertible. -/
theorem testField_orbit {lam : ℂ} {h : ℝ} (hinv : IsUnit (1 - (h * lam) • tab.complexA))
    {u : ℕ → ℂ} (hu : OneStep.IsOrbit (tab.stepRel (testField lam)) h 0 u) (n : ℕ) :
    u n = tab.stabilityFunction (h * lam) ^ n * u 0 := by
  rw [OneStep.isOrbit_iff] at hu
  induction n with
  | zero => simp
  | succ n ih =>
    rw [(tab.stepRel_testField_iff hinv _ _ _).1 (hu n), ih, pow_succ]
    ring

/-- On the test equation with `I - hλ A` invertible, every datum has an orbit, the geometric
sequence `R(hλ)^n u₀`. -/
theorem isOrbit_testField {lam : ℂ} {h : ℝ} (hinv : IsUnit (1 - (h * lam) • tab.complexA))
    (u₀ : ℂ) :
    OneStep.IsOrbit (tab.stepRel (testField lam)) h 0 fun n =>
      tab.stabilityFunction (h * lam) ^ n * u₀ := by
  rw [OneStep.isOrbit_iff]
  intro n
  rw [tab.stepRel_testField_iff hinv, pow_succ]
  ring

/-- On the test equation the step relation depends on `(h, λ)` only through `hλ`: the stages
scale by `h`. -/
theorem stepRel_testField_smul_iff {lam : ℂ} {h : ℝ} (hh : h ≠ 0) (t t' : ℝ) (u v : ℂ) :
    tab.stepRel (testField lam) h t u v ↔ tab.stepRel (testField (h * lam)) 1 t' u v := by
  simp only [stepRel_apply, isStages_testField_iff, Complex.ofReal_one, one_mul, one_smul]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh
  constructor
  · rintro ⟨K, hK, rfl⟩
    refine ⟨(h : ℂ) • K, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hK, smul_smul]
      congr 1
      ring
    · rw [sum_smul_eq_dotProduct, sum_smul_eq_dotProduct, dotProduct_smul, Complex.real_smul,
        smul_eq_mul]
  · rintro ⟨K, hK, rfl⟩
    refine ⟨(h : ℂ)⁻¹ • K, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hK, smul_smul]
      congr 1
      field_simp
    · rw [sum_smul_eq_dotProduct, sum_smul_eq_dotProduct, dotProduct_smul, Complex.real_smul,
        smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hh', one_mul]

/-- The orbits of the method on the test equation depend on `(h, λ)` only through `hλ`. -/
theorem testField_scaleInvariant (h : ℝ) (hh : 0 < h) (lam : ℂ) (u : ℕ → ℂ) :
    OneStep.IsOrbit (tab.stepRel (testField lam)) h 0 u ↔
      OneStep.IsOrbit (tab.stepRel (testField (h * lam))) 1 0 u := by
  simp only [OneStep.isOrbit_iff]
  exact forall_congr' fun n => tab.stepRel_testField_smul_iff hh.ne' _ _ _ _

/-- **The region of absolute stability of a Runge–Kutta method** ([quarteroni2000numerical]
§11.8.4): when `I - z A` is invertible, `z ∈ 𝒜 ↔ ‖R(z)‖ < 1`. (When `I - z A` is singular the
method may still be absolutely stable in the sense of `OneStep.IsAbsStable` — the stage system
can be solvable for every datum with a forced step, e.g. `A = !![0, 1; 1, 0]`, `b = (1/2, 1/2)`
at `z = -1` — so the invertibility is a genuine hypothesis; see
`not_mem_absStabilityRegion_of_forall_ne` for the singular case in which the stage system has no
solution.) -/
theorem mem_absStabilityRegion_iff_of_isUnit {z : ℂ} (hz : IsUnit (1 - z • tab.complexA)) :
    z ∈ OneStep.absStabilityRegion tab.stepRel ↔ ‖tab.stabilityFunction z‖ < 1 := by
  rw [OneStep.absStabilityRegion_eq_of_scaleInvariant tab.testField_scaleInvariant, mem_ofPred_eq]
  have hz' : IsUnit (1 - ((1 : ℝ) * z) • tab.complexA) := by simpa using hz
  refine OneStep.isAbsStable_iff_norm_lt_one (r := tab.stabilityFunction z) (fun u₀ => ?_)
    (fun u hu n => ?_)
  · simpa using tab.isOrbit_testField hz' u₀
  · simpa using tab.testField_orbit hz' hu n

/-- When `𝟙 ∉ range (I - z A)` (so `I - z A` is singular), some datum has no step on the test
equation, so `z ∉ 𝒜`. -/
theorem not_mem_absStabilityRegion_of_forall_ne {z : ℂ}
    (hz : ∀ K : Fin s → ℂ, (1 - z • tab.complexA) *ᵥ K ≠ fun _ => 1) (hz0 : z ≠ 0) :
    z ∉ OneStep.absStabilityRegion tab.stepRel := by
  rw [OneStep.absStabilityRegion_eq_of_scaleInvariant tab.testField_scaleInvariant, mem_ofPred_eq]
  rintro ⟨hex, -⟩
  obtain ⟨u, hu, hu0⟩ := hex z⁻¹
  rw [OneStep.isOrbit_iff] at hu
  obtain ⟨K, hK, -⟩ := hu 0
  rw [isStages_testField_iff, hu0, mul_inv_cancel₀ hz0, one_smul, Complex.ofReal_one, one_mul]
    at hK
  exact hz K hK

/-! ### Explicit tableaux: `R` is a polynomial -/

section Explicit

variable (hex : tab.IsExplicit)
include hex

/-- For an explicit tableau the powers of `A` are strictly lower triangular of increasing
depth: `(A^k)_ij = 0` whenever `i < j + k`. -/
theorem complexA_pow_apply_eq_zero (k : ℕ) (i j : Fin s) (hij : i.1 < j.1 + k) :
    (tab.complexA ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply_ne]
    intro hij'
    rw [hij'] at hij
    omega
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : i.1 < l.1 + k
    · rw [ih i l hl, zero_mul]
    · rw [complexA_apply, hex l j (by omega), Complex.ofReal_zero, mul_zero]

/-- For an explicit tableau `A` is nilpotent: `A^s = 0`. -/
theorem complexA_pow_eq_zero : tab.complexA ^ s = 0 := by
  ext i j
  rw [tab.complexA_pow_apply_eq_zero hex s i j (by omega), Matrix.zero_apply]

/-- For an explicit tableau `(I - z A)⁻¹ = ∑_{k<s} (z A)^k`, the Neumann series of the nilpotent
matrix `z A`. -/
theorem inv_one_sub_smul_complexA (z : ℂ) :
    (1 - z • tab.complexA)⁻¹ = ∑ k ∈ range s, (z • tab.complexA) ^ k := by
  refine Matrix.inv_eq_right_inv ?_
  rw [mul_neg_geom_sum, smul_pow, tab.complexA_pow_eq_zero hex, smul_zero, sub_zero]

/-- For an explicit tableau `I - z A` is invertible for every `z`. -/
theorem isUnit_one_sub_smul_complexA (z : ℂ) : IsUnit (1 - z • tab.complexA) :=
  (Matrix.isUnit_iff_isUnit_det _).2 <| Matrix.isUnit_det_of_right_inverse (by
    rw [mul_neg_geom_sum, smul_pow, tab.complexA_pow_eq_zero hex, smul_zero, sub_zero])

/-- For an explicit tableau `det (I - z A) = 1`: the matrix is lower triangular with unit
diagonal. -/
theorem det_one_sub_smul_complexA (z : ℂ) : (1 - z • tab.complexA).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [hex i i le_rfl]
  · intro i j hij
    have hij' : i < j := hij
    simp [Matrix.one_apply_ne hij'.ne, hex i j hij'.le]

/-- **The nilpotent expansion of the stability function** of an explicit tableau:
`R(z) = 1 + ∑_{k<s} z^{k+1} bᵀ A^k 𝟙`, a polynomial of degree at most `s`. -/
theorem stabilityFunction_eq_sum_of_isExplicit (z : ℂ) :
    tab.stabilityFunction z =
      1 + ∑ k ∈ range s, z ^ (k + 1) * (tab.complexB ⬝ᵥ (tab.complexA ^ k *ᵥ fun _ => 1)) := by
  rw [stabilityFunction, tab.inv_one_sub_smul_complexA hex, Matrix.sum_mulVec, dotProduct_sum,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pow_succ]
  ring

/-- **The determinant formula for the stability function** of an explicit tableau
([quarteroni2000numerical] §11.8.4): `R(z) = det (I - z A + z 𝟙 bᵀ) / det (I - z A)` with
`det (I - z A) = 1`, from the matrix determinant lemma. -/
theorem stabilityFunction_eq_det_of_isExplicit (z : ℂ) :
    tab.stabilityFunction z =
      (1 - z • tab.complexA +
        z • (replicateCol Unit (fun _ => (1 : ℂ)) * replicateRow Unit tab.complexB)).det := by
  set M := 1 - z • tab.complexA with hM
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (tab.isUnit_one_sub_smul_complexA hex z)
  have e : M + z • (replicateCol Unit (fun _ => (1 : ℂ)) * replicateRow Unit tab.complexB) =
      M * (1 + replicateCol Unit (z • (M⁻¹ *ᵥ fun _ => (1 : ℂ))) *
        replicateRow Unit tab.complexB) := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.replicateCol_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec,
      Matrix.replicateCol_smul, Matrix.smul_mul]
  rw [e, Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow, hM,
    tab.det_one_sub_smul_complexA hex, one_mul, dotProduct_smul, smul_eq_mul, stabilityFunction]

/-- For an explicit tableau the region of absolute stability is `{z | ‖R(z)‖ < 1}` without any
invertibility clause. -/
theorem mem_absStabilityRegion_iff_of_isExplicit (z : ℂ) :
    z ∈ OneStep.absStabilityRegion tab.stepRel ↔ ‖tab.stabilityFunction z‖ < 1 :=
  tab.mem_absStabilityRegion_iff_of_isUnit (tab.isUnit_one_sub_smul_complexA hex z)

omit hex in
/-- **The stability polynomial** of a tableau: `1 + ∑_{k<s} (bᵀ A^k 𝟙) X^{k+1}`, whose evaluation
is the stability function when the tableau is explicit. -/
noncomputable def stabilityPolynomial : Polynomial ℂ :=
  1 + ∑ k ∈ range s, Polynomial.C (tab.complexB ⬝ᵥ (tab.complexA ^ k *ᵥ fun _ => 1)) *
    Polynomial.X ^ (k + 1)

/-- The stability function of an explicit tableau is the evaluation of its stability
polynomial. -/
theorem stabilityFunction_eq_eval (z : ℂ) :
    tab.stabilityFunction z = (tab.stabilityPolynomial).eval z := by
  rw [tab.stabilityFunction_eq_sum_of_isExplicit hex, stabilityPolynomial, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]

omit hex in
/-- The coefficient of `X` in the stability polynomial is `∑_i b_i`. -/
theorem stabilityPolynomial_coeff_one (hs : 0 < s) :
    (tab.stabilityPolynomial).coeff 1 = ((∑ i, tab.b i : ℝ) : ℂ) := by
  rw [stabilityPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single 0]
  · simp [dotProduct, Polynomial.coeff_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right]
    omega
  · intro h
    exact absurd (Finset.mem_range.2 hs) h

omit hex in
/-- The stability polynomial of a consistent tableau has positive degree. -/
theorem degree_stabilityPolynomial_pos (hb : ∑ i, tab.b i = 1) :
    0 < (tab.stabilityPolynomial).degree := by
  have hs : 0 < s := by
    by_contra h
    have : (∑ i, tab.b i) = 0 := by
      rw [Finset.sum_eq_zero]
      intro i _
      exact absurd i.2 (by omega)
    rw [this] at hb
    exact zero_ne_one hb
  have h1 : (tab.stabilityPolynomial).coeff 1 ≠ 0 := by
    rw [tab.stabilityPolynomial_coeff_one hs, hb]
    exact one_ne_zero
  exact lt_of_lt_of_le (by norm_num) (Polynomial.le_degree_of_ne_zero h1)

/-- **The region of absolute stability of an explicit consistent method is bounded**
([quarteroni2000numerical] §11.8.4): `R` is a nonconstant polynomial, so `‖R(z)‖ ≥ 1` outside a
bounded set. -/
theorem isBounded_absStabilityRegion (hb : ∑ i, tab.b i = 1) :
    Bornology.IsBounded (OneStep.absStabilityRegion tab.stepRel) := by
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, 1 ≤ ‖tab.stabilityFunction z‖ := by
    have := (Polynomial.tendsto_norm_atTop tab.stabilityPolynomial
      (tab.degree_stabilityPolynomial_pos hb) tendsto_norm_cobounded_atTop).eventually_ge_atTop 1
    filter_upwards [this] with z hz
    rwa [tab.stabilityFunction_eq_eval hex]
  rw [Bornology.isBounded_def]
  refine Filter.mem_of_superset hev fun z hz => ?_
  rw [mem_compl_iff, tab.mem_absStabilityRegion_iff_of_isExplicit hex]
  exact not_lt.2 hz

/-- **No explicit consistent Runge–Kutta method is A-stable** ([quarteroni2000numerical]
Remark 11.2 for Runge–Kutta methods, §11.8.4): its region of absolute stability is bounded,
while the left half-plane is not. -/
theorem not_isAStable_of_isExplicit (hb : ∑ i, tab.b i = 1) : ¬ OneStep.IsAStable tab.stepRel := by
  intro hA
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (tab.isBounded_absStabilityRegion hex hb)
  have hmem : (-(max C 0 + 1) : ℂ) ∈ OneStep.absStabilityRegion tab.stepRel :=
    hA _ (by simp)
  have := hC _ hmem
  rw [norm_neg, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at this
  linarith [le_max_left C 0]

end Explicit

end ButcherTableau

/-! ### The stability functions of the named tableaux -/

/-- **The stability function of the classical method** ([quarteroni2000numerical] §11.8.4):
`R(z) = 1 + z + z²/2 + z³/6 + z⁴/24`, the truncated exponential of degree `4`. -/
theorem stabilityFunction_rk4 (z : ℂ) :
    rk4.stabilityFunction z = 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 := by
  rw [rk4.stabilityFunction_eq_sum_of_isExplicit rk4_isExplicit]
  simp [Finset.sum_range_succ, dotProduct, Matrix.mulVec, Fin.sum_univ_four, pow_succ,
    Matrix.mul_apply, rk4]
  ring

/-- The region of absolute stability of the classical method:
`‖1 + z + z²/2 + z³/6 + z⁴/24‖ < 1` ([quarteroni2000numerical] Figure 11.10, `s = 4`). -/
theorem mem_absStabilityRegion_rk4_iff (z : ℂ) :
    z ∈ OneStep.absStabilityRegion rk4.stepRel ↔
      ‖1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24‖ < 1 := by
  rw [rk4.mem_absStabilityRegion_iff_of_isExplicit rk4_isExplicit, stabilityFunction_rk4]

namespace ButcherTableau

/-- The stability function of Heun's tableau is `1 + z + z²/2`, in agreement with
`OneStep.mem_absStabilityRegion_heun_iff`. -/
theorem stabilityFunction_heun (z : ℂ) : heun.stabilityFunction z = 1 + z + z ^ 2 / 2 := by
  rw [heun.stabilityFunction_eq_sum_of_isExplicit heun_isExplicit]
  simp [Finset.sum_range_succ, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_succ,
    Matrix.mul_apply, heun]
  ring

/-- The stability function of the implicit midpoint rule is `(1 + z/2) / (1 - z/2)` for `z ≠ 2`,
the stability function of Crank–Nicolson. -/
theorem stabilityFunction_implicitMidpoint {z : ℂ} (hz : z ≠ 2) :
    implicitMidpoint.stabilityFunction z = (1 + z / 2) / (1 - z / 2) := by
  have hne : (1 : ℂ) - z / 2 ≠ 0 := by
    intro h0
    apply hz
    linear_combination (-2 : ℂ) * h0
  have hinv : (1 - z • implicitMidpoint.complexA)⁻¹ = !![(1 - z / 2)⁻¹] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i; fin_cases j
    simp [implicitMidpoint, Matrix.mul_apply]
    field_simp
  rw [stabilityFunction, hinv]
  simp [implicitMidpoint, Matrix.mulVec, dotProduct]
  field_simp
  ring

end ButcherTableau

/-! ### Order conditions on test problems -/

/-- A coefficient `c` with `c h^m = O(h^{m+1})` as `h → 0⁺` vanishes. -/
theorem _root_.eq_zero_of_isBigO_pow_succ {c : ℝ} {m : ℕ}
    (h : (fun h : ℝ => c * h ^ m) =O[𝓝[>] 0] fun h => h ^ (m + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |c| ≤ C * h := by
    filter_upwards [hC, eventually_mem_nhdsWithin] with h hh (hpos : 0 < h)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hpos m),
      abs_of_pos (pow_pos hpos _), pow_succ, ← mul_assoc] at hh
    have hm : 0 < h ^ m := pow_pos hpos m
    have : |c| * h ^ m ≤ (C * h) * h ^ m := by linarith [hh]
    exact le_of_mul_le_mul_right this hm
  have hlim : Tendsto (fun h : ℝ => C * h) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ => C * h) (𝓝 0) (𝓝 (C * 0)) :=
      (by fun_prop : Continuous fun h : ℝ => C * h).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact abs_nonpos_iff.1 (ge_of_tendsto hlim hev)

/-- **A complex polynomial of degree at most `n` that is `O(h^{n+1})` along real `h → 0⁺`
vanishes.** By induction on `n`: the constant term is the limit at `0`, and `p / X` is `O(h^n)`.
-/
theorem _root_.Polynomial.eq_zero_of_isBigO_pow_succ :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.natDegree ≤ n →
      (fun h : ℝ => p.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) → p = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp h
    rw [Polynomial.eq_C_of_natDegree_le_zero hp] at h ⊢
    simp only [Polynomial.eval_C, zero_add, pow_one] at h
    obtain ⟨C, hC⟩ := h.bound
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖p.coeff 0‖ ≤ C * h := by
      filter_upwards [hC, eventually_mem_nhdsWithin] with h hh (hpos : 0 < h)
      rwa [Real.norm_of_nonneg hpos.le] at hh
    have hlim : Tendsto (fun h : ℝ => C * h) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => C * h) (𝓝 0) (𝓝 (C * 0)) :=
        (by fun_prop : Continuous fun h : ℝ => C * h).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    rw [norm_le_zero_iff.1 (ge_of_tendsto hlim hev), map_zero]
  | succ n ih =>
    intro p hp h
    -- the constant term vanishes
    have h0 : p.coeff 0 = 0 := by
      have hlim : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 (p.eval 0)) := by
        have : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝 0) (𝓝 (p.eval ((0 : ℝ) : ℂ))) :=
          (p.continuous.comp Complex.continuous_ofReal).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hzero : Tendsto (fun h : ℝ => p.eval (h : ℂ)) (𝓝[>] 0) (𝓝 0) :=
        h.trans_tendsto <| ((continuous_pow (n + 1 + 1)).tendsto' 0 0 (by simp)).mono_left
          nhdsWithin_le_nhds
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact tendsto_nhds_unique hlim hzero
    -- so `p = divX p * X` and `divX p` is `O(h^{n+1})`
    have hpX : p = p.divX * Polynomial.X := by
      conv_lhs => rw [← p.divX_mul_X_add]
      rw [h0, map_zero, add_zero]
    have hdiv : (fun h : ℝ => p.divX.eval (h : ℂ)) =O[𝓝[>] 0] (fun h => h ^ (n + 1)) := by
      obtain ⟨C, hC⟩ := h.bound
      refine IsBigO.of_bound C ?_
      filter_upwards [hC, eventually_mem_nhdsWithin] with h hh (hpos : 0 < h)
      rw [hpX, Polynomial.eval_mul, Polynomial.eval_X, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (pow_pos hpos _).le, pow_succ,
        ← mul_assoc] at hh
      rw [Real.norm_of_nonneg (pow_pos hpos _).le]
      exact le_of_mul_le_mul_right hh hpos
    have := ih p.divX (by
      have := p.natDegree_divX_eq_natDegree_tsub_one
      omega) hdiv
    rw [hpX, this, zero_mul]

namespace ButcherTableau

variable {s : ℕ} (tab : ButcherTableau s)

/-- On a field that ignores the state, every explicit stage is the field at the node. -/
theorem explicitStages_of_forall_eq {f : ℝ → E → E} (hf : ∀ t u v, f t u = f t v) (h t : ℝ)
    (u : E) (i : Fin s) : tab.explicitStages f h t u i = f (t + tab.c i * h) u := by
  rw [explicitStages_apply]
  exact hf _ _ _

/-- **The order-two condition `∑ bᵢ cᵢ = 1/2` is necessary** ([quarteroni2000numerical]
§11.8.1): if an explicit method has order `2` along the solution `y t = t²` of `y' = 2t` on
`[0, 1]`, then `∑_i b_i c_i = 1/2`. There the stages are `2 (t + c_i h)` and the truncation error
at `t = 0` is `h (1 - 2 ∑ b_i c_i)`. -/
theorem sum_b_mul_c_eq_half_of_hasOrderFor
    (hord : OneStep.HasOrderFor (tab.explicitIncrement fun t _ => 2 * t) 0 1 (fun t => t ^ 2) 2) :
    ∑ i, tab.b i * tab.c i = 1 / 2 := by
  have hlte : ∀ h : ℝ, h ≠ 0 →
      OneStep.lte (tab.explicitIncrement fun t _ => 2 * t) h (fun t => t ^ 2) 0 =
        (1 - 2 * ∑ i, tab.b i * tab.c i) * h := by
    intro h hh
    simp only [OneStep.lte, explicitIncrement_apply,
      tab.explicitStages_of_forall_eq (f := fun t _ => 2 * t) (fun _ _ _ => rfl), smul_eq_mul,
      zero_add]
    have e : ∑ i, tab.b i * (2 * (tab.c i * h)) = 2 * h * ∑ i, tab.b i * tab.c i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    field_simp
    ring
  have hglob : ∀ h ∈ Ioc (0 : ℝ) 1, |1 - 2 * ∑ i, tab.b i * tab.c i| * h ≤
      OneStep.globalLte (tab.explicitIncrement fun t _ => 2 * t) 0 1 (fun t => t ^ 2) h := by
    intro h hh
    have hN : 0 < gridCount 1 h := (le_gridCount_iff zero_le_one hh.1).2 (by simpa using hh.2)
    have := OneStep.norm_lte_le_globalLte (Φ := tab.explicitIncrement fun t _ => 2 * t) (t₀ := 0)
      (T := 1) (y := fun t => t ^ 2) hN
    rwa [node_zero, hlte h hh.1.ne', Real.norm_eq_abs, abs_mul, abs_of_pos hh.1] at this
  have hbig : (fun h : ℝ => (1 - 2 * ∑ i, tab.b i * tab.c i) * h ^ 1) =O[𝓝[>] 0]
      fun h => h ^ (1 + 1) := by
    refine (IsBigO.of_bound 1 ?_).trans hord
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
    rw [pow_one, one_mul, Real.norm_eq_abs, abs_mul, abs_of_pos hh.1,
      Real.norm_of_nonneg (OneStep.globalLte_nonneg _)]
    exact hglob h hh
  have := eq_zero_of_isBigO_pow_succ hbig
  linarith

/-- **The two-stage order-two conditions are necessary** ([quarteroni2000numerical] §11.8.1):
if the explicit two-stage tableau with `c 0 = 0` has order `2` along the solutions of `y' = 1`
(on some `[t₀, t₀ + T]`, `T > 0`) and of `y' = 2t` (on `[0, 1]`), then `b 0 + b 1 = 1` and
`c 1 * b 1 = 1/2`. -/
theorem orderTwoConditions_of_hasOrderFor (tab : ButcherTableau 2) (hc0 : tab.c 0 = 0) {t₀ T : ℝ}
    (hT : 0 < T)
    (hord₁ : OneStep.HasOrderFor (tab.explicitIncrement fun _ _ => (1 : ℝ)) t₀ T id 2)
    (hord₂ : OneStep.HasOrderFor (tab.explicitIncrement fun t _ => 2 * t) 0 1 (fun t => t ^ 2) 2) :
    tab.b 0 + tab.b 1 = 1 ∧ tab.c 1 * tab.b 1 = 1 / 2 := by
  have h1 := tab.sum_b_eq_one_of_isConsistentFor hT (hord₁.isConsistentFor one_le_two)
  have h2 := tab.sum_b_mul_c_eq_half_of_hasOrderFor hord₂
  rw [Fin.sum_univ_two] at h1 h2
  rw [hc0] at h2
  exact ⟨h1, by linarith⟩

/-! ### The stability function of a method of order `s` -/

section TruncExp

variable (hex : tab.IsExplicit)
include hex

/-- The real explicit stages on `y' = y`, read in `ℂ`, are stages of the test equation with
`λ = 1`. -/
theorem isStages_testField_one_ofReal (h t u : ℝ) :
    tab.IsStages (testField 1) h t (u : ℂ)
      fun i => ((tab.explicitStages (fun _ (y : ℝ) => y) h t u i : ℝ) : ℂ) := by
  intro i
  have := tab.isStages_explicitStages hex (fun _ (y : ℝ) => y) h t u i
  simp only [testField, one_mul]
  conv_lhs => rw [this]
  push_cast
  simp [Complex.real_smul]

/-- On the real problem `y' = y`, one step of an explicit method from `1` is `R(h)`:
`R(h) = 1 + h ∑_i b_i K_i(0, 1; h)`. -/
theorem stabilityFunction_ofReal (h : ℝ) :
    tab.stabilityFunction h =
      ((1 + h * tab.explicitIncrement (fun _ y => y) 0 1 1 h : ℝ) : ℂ) := by
  have hinv := tab.isUnit_one_sub_smul_complexA hex ((h : ℂ) * 1)
  have hst := tab.isStages_testField_one_ofReal hex h 0 1
  have := (tab.stepRel_testField_iff hinv 0 ((1 : ℝ) : ℂ) _).1 ⟨_, hst, rfl⟩
  rw [mul_one, Complex.ofReal_one, mul_one] at this
  rw [← this, explicitIncrement_apply]
  push_cast
  simp [Complex.real_smul]

/-- **The stability function of an explicit method of order `s`** ([quarteroni2000numerical]
§11.8.4): if the explicit `s`-stage method has order `s` along the solution `e^t` of the real
problem `y' = y` on `[0, 1]`, then `R(z) = ∑_{k ≤ s} z^k / k!`. On `y' = y` the step from `1`
is `R(h)`, so `e^h - R(h) = h τ(h) = O(h^{s+1})`; the polynomial `R - ∑_{k ≤ s} X^k / k!` of
degree at most `s` is then `O(h^{s+1})` at `0⁺`, hence zero. (The book states this for
`s ≤ 4`, where such methods exist; the implication needs no bound on `s`.) -/
theorem stabilityFunction_eq_truncExp_of_hasOrder
    (hord : OneStep.HasOrderFor (tab.explicitIncrement fun _ y => y) 0 1 Real.exp s) (z : ℂ) :
    tab.stabilityFunction z = ∑ k ∈ range (s + 1), z ^ k / k.factorial := by
  set S : Polynomial ℂ :=
    ∑ k ∈ range (s + 1), Polynomial.C ((k.factorial : ℂ)⁻¹) * Polynomial.X ^ k with hS
  have hSeval : ∀ w : ℂ, S.eval w = ∑ k ∈ range (s + 1), w ^ k / k.factorial := by
    intro w
    rw [hS, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      div_eq_mul_inv, mul_comm]
  have hQeval : ∀ w : ℂ, (tab.stabilityPolynomial - S).eval w =
      tab.stabilityFunction w - ∑ k ∈ range (s + 1), w ^ k / k.factorial := by
    intro w
    rw [Polynomial.eval_sub, hSeval, tab.stabilityFunction_eq_eval hex]
  -- degree bound
  have hQdeg : (tab.stabilityPolynomial - S).natDegree ≤ s := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine Polynomial.natDegree_add_le_of_degree_le (by simp) ?_
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.1 hk)
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  -- the `O`-estimate: `R(h) - e^h = -h τ(h)` and Taylor's bound for `e^h`
  have h1 : (fun h : ℝ => tab.stabilityFunction h - Complex.exp h) =O[𝓝[>] 0]
      fun h => h ^ (s + 1) := by
    have hmul : (fun h : ℝ => h * OneStep.globalLte (tab.explicitIncrement fun _ y => y)
        0 1 Real.exp h) =O[𝓝[>] 0] fun h => h ^ (s + 1) := by
      have := (isBigO_refl (fun h : ℝ => h) (𝓝[>] 0)).mul hord
      refine this.congr' EventuallyEq.rfl (Eventually.of_forall fun h => ?_)
      simp [pow_succ']
    refine (IsBigO.of_bound 1 ?_).trans hmul
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
    have hN : 0 < gridCount 1 h := (le_gridCount_iff zero_le_one hh.1).2 (by simpa using hh.2)
    have hle := OneStep.norm_lte_le_globalLte (Φ := tab.explicitIncrement fun _ y => y) (t₀ := 0)
      (T := 1) (y := Real.exp) hN
    rw [node_zero] at hle
    have e : tab.stabilityFunction h - Complex.exp h =
        -((h * OneStep.lte (tab.explicitIncrement fun _ y => y) h Real.exp 0 : ℝ) : ℂ) := by
      rw [tab.stabilityFunction_ofReal hex, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
        ← Complex.ofReal_neg]
      congr 1
      simp only [OneStep.lte, smul_eq_mul, zero_add, Real.exp_zero]
      have : tab.explicitIncrement (fun _ y => y) 0 1 (Real.exp h) h =
          tab.explicitIncrement (fun _ y => y) 0 1 1 h := rfl
      rw [this]
      have hne : h ≠ 0 := hh.1.ne'
      field_simp
      ring
    rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hh.1, one_mul,
      Real.norm_eq_abs, abs_mul, abs_of_pos hh.1, abs_of_nonneg (OneStep.globalLte_nonneg _)]
    exact mul_le_mul_of_nonneg_left hle hh.1.le
  have h2 : (fun h : ℝ => Complex.exp h - ∑ k ∈ range (s + 1), (h : ℂ) ^ k / k.factorial)
      =O[𝓝[>] 0] fun h => h ^ (s + 1) := by
    refine IsBigO.of_bound ((s.succ.succ : ℝ) * ((s.succ.factorial : ℝ) * (s.succ : ℝ))⁻¹) ?_
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with h hh
    have hx : ‖(h : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hh.1.le]
      exact hh.2
    have := Complex.exp_bound hx (Nat.succ_pos s)
    rw [Complex.norm_real, Real.norm_of_nonneg hh.1.le] at this
    rw [Real.norm_of_nonneg (pow_pos hh.1 _).le, mul_comm]
    exact this
  have hQ : tab.stabilityPolynomial - S = 0 := by
    refine Polynomial.eq_zero_of_isBigO_pow_succ s _ hQdeg ?_
    refine (h1.add h2).congr' (Eventually.of_forall fun h => ?_) EventuallyEq.rfl
    change tab.stabilityFunction h - Complex.exp h +
      (Complex.exp h - ∑ k ∈ range (s + 1), (h : ℂ) ^ k / k.factorial) =
        (tab.stabilityPolynomial - S).eval (h : ℂ)
    rw [hQeval, sub_add_sub_cancel]
  have := hQeval z
  rw [hQ, Polynomial.eval_zero] at this
  exact (sub_eq_zero.1 this.symm)

end TruncExp

end ButcherTableau

/-! ### Taylor bounds, and the two-stage order-two conditions

Taylor bounds first: for a curve with explicit derivatives on a closed interval,
`norm_sub_taylorSum_le` at an arbitrary order and its third-order case
`norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six`; and along a segment for a map with named
Fréchet derivatives, `norm_sub_sub_smul_apply_le_of_hasFDerivAt` at order two and
`norm_sub_taylor_segment_le` at order four. All are Mathlib-shaped and live here until a calculus
module takes them. -/

section Taylor

variable {a b M : ℝ} {y y' y'' y''' : ℝ → E}

/-- **Taylor's theorem with a bound on the top derivative**, for a curve in a normed space over a
closed interval: if `Y 0, …, Y (n + 1)` is a chain of successive derivatives on `Icc a b` and
`‖Y (n + 1)‖ ≤ M` there, then `Y 0 b` differs from its Taylor polynomial at `a` by at most
`M (b - a)^{n+1} / (n+1)!`. The proof is induction on `n`: the residual has derivative the residual
of the shifted family, which the induction hypothesis bounds on `[a, s]`, and
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` compares it with
`M (s - a)^{n+2} / (n+2)!`. Mathlib-shaped and lives here until a calculus module takes it; it
subsumes `norm_sub_sub_smul_le_mul_sq_div_two` (`n = 1`) and
`norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six` (`n = 2`). -/
theorem _root_.norm_sub_taylorSum_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M a b : ℝ} {Y : ℕ → ℝ → X} {n : ℕ} (hab : a ≤ b)
    (hY : ∀ k ≤ n, ∀ s ∈ Icc a b, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖Y (n + 1) s‖ ≤ M) :
    ‖Y 0 b - ∑ k ∈ range (n + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a‖ ≤
      M * (b - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  induction n generalizing Y b with
  | zero =>
    have key := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Y 0) (f' := Y 1) (fun s hs => hY 0 le_rfl s hs) (fun s hs => hM s hs)
      (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)] at key
    have e1 : ∑ k ∈ range (0 + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a = Y 0 a := by
      simp
    have e2 : M * (b - a) ^ (0 + 1) / (Nat.factorial (0 + 1) : ℝ) = M * (b - a) := by
      simp
    rw [e1, e2]
    exact key
  | succ n ih =>
    set G : ℝ → X := fun s => Y 0 s - Y 0 a -
      ∑ k ∈ range (n + 1), ((s - a) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • Y (k + 1) a
      with hGdef
    set G' : ℝ → X := fun s => Y 1 s -
      ∑ k ∈ range (n + 1), ((s - a) ^ k / (Nat.factorial k : ℝ)) • Y (k + 1) a with hG'def
    have hpoly : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s - a) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • Y (k + 1) a)
        (((s - a) ^ k / (Nat.factorial k : ℝ)) • Y (k + 1) a) s := by
      intro k s
      have h1 : HasDerivAt (fun s : ℝ => (s - a) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))
          ((s - a) ^ k / (Nat.factorial k : ℝ)) s := by
        have h2 := (((hasDerivAt_id s).sub_const a).fun_pow (k + 1)).div_const
          ((Nat.factorial (k + 1) : ℝ))
        refine h2.congr_deriv ?_
        simp only [id_eq, Nat.add_sub_cancel]
        rw [Nat.factorial_succ]
        have hf : ((Nat.factorial k : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
        push_cast
        field_simp
      simpa using h1.smul_const (Y (k + 1) a)
    have hGder : ∀ s ∈ Icc a b, HasDerivWithinAt G (G' s) (Icc a b) s := by
      intro s hs
      have hsum : HasDerivWithinAt
          (fun s : ℝ => ∑ k ∈ range (n + 1),
            ((s - a) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) • Y (k + 1) a)
          (∑ k ∈ range (n + 1), ((s - a) ^ k / (Nat.factorial k : ℝ)) • Y (k + 1) a)
          (Icc a b) s :=
        HasDerivWithinAt.fun_sum fun k _ => (hpoly k s).hasDerivWithinAt
      exact ((hY 0 (by omega) s hs).sub_const (Y 0 a)).sub hsum
    have hG'bound : ∀ s ∈ Icc a b,
        ‖G' s‖ ≤ M * (s - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
      intro s hs
      have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
      exact ih (Y := fun k => Y (k + 1)) (b := s) hs.1
        (fun k _ s' hs' => ((hY (k + 1) (by omega) s' (hsub hs')).mono hsub))
        (fun s' hs' => hM s' (hsub hs'))
    have hB : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => M * (s - a) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        (M * (s - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) s := by
      intro s
      have h1 := (((hasDerivAt_id s).sub_const a).fun_pow (n + 2)).const_mul M
      have h2 := h1.div_const ((Nat.factorial (n + 2) : ℝ))
      refine h2.congr_deriv ?_
      simp only [id_eq]
      rw [Nat.factorial_succ (n + 1)]
      have hf : ((Nat.factorial (n + 1) : ℝ)) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (n + 1))
      push_cast
      field_simp
      ring
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := G) (f' := G') (HasDerivWithinAt.continuousOn hGder)
      (fun s hs => (hGder s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (B := fun s => M * (s - a) ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
      (B' := fun s => M * (s - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ))
      (by simp [hGdef]) hB
      (fun s hs => hG'bound s (Ico_subset_Icc_self hs)) (right_mem_Icc.2 hab)
    have heq : Y 0 b - ∑ k ∈ range (n + 1 + 1),
        ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a = G b := by
      rw [hGdef, Finset.sum_range_succ']
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
      abel
    rw [heq]
    exact key

/-- **Third-order Taylor bound**: if `y'`, `y''`, `y'''` are the successive derivatives of `y`
on `Icc a b` with `‖y'''‖ ≤ M` there, then
`‖y b - y a - (b - a) • y' a - ((b - a)² / 2) • y'' a‖ ≤ M (b - a)³ / 6`. The case `n = 2` of
`norm_sub_taylorSum_le`. -/
theorem _root_.norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six (hab : a ≤ b)
    (hy : ∀ s ∈ Icc a b, HasDerivWithinAt y (y' s) (Icc a b) s)
    (hy' : ∀ s ∈ Icc a b, HasDerivWithinAt y' (y'' s) (Icc a b) s)
    (hy'' : ∀ s ∈ Icc a b, HasDerivWithinAt y'' (y''' s) (Icc a b) s)
    (hM : ∀ s ∈ Icc a b, ‖y''' s‖ ≤ M) :
    ‖y b - y a - (b - a) • y' a - ((b - a) ^ 2 / 2) • y'' a‖ ≤ M * (b - a) ^ 3 / 6 := by
  obtain ⟨Y, e0, e1, e2, e3⟩ : ∃ Y : ℕ → ℝ → E, Y 0 = y ∧ Y 1 = y' ∧ Y 2 = y'' ∧ Y 3 = y''' :=
    ⟨fun k => match k with
      | 0 => y
      | 1 => y'
      | 2 => y''
      | _ => y''', rfl, rfl, rfl, rfl⟩
  have hY : ∀ k ≤ 2, ∀ s ∈ Icc a b, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc a b) s := by
    intro k hk s hs
    rcases k with _ | _ | _ | k
    · rw [e0, e1]; exact hy s hs
    · rw [e1, e2]; exact hy' s hs
    · rw [e2, e3]; exact hy'' s hs
    · omega
  have key := norm_sub_taylorSum_le (Y := Y) (n := 2) hab hY (by rw [e3]; exact hM)
  have hsum : ∑ k ∈ range (2 + 1), ((b - a) ^ k / (Nat.factorial k : ℝ)) • Y k a
      = y a + (b - a) • y' a + ((b - a) ^ 2 / 2) • y'' a := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e0, e1, e2]
    norm_num
  rw [e0, hsum] at key
  have he : y b - y a - (b - a) • y' a - ((b - a) ^ 2 / 2) • y'' a
      = y b - (y a + (b - a) • y' a + ((b - a) ^ 2 / 2) • y'' a) := by abel
  rw [he]
  refine key.trans (le_of_eq ?_)
  norm_num

/-- **Fourth-order Taylor bound along a segment** for a map `G` on a normed space with Fréchet
derivatives `G₁, G₂, G₃, G₄` and `‖G₄‖ ≤ M`:
`‖G(p + w) - G p - G₁ p w - (1/2) G₂ p w w - (1/6) G₃ p w w w‖ ≤ M ‖w‖⁴ / 24`. It is
`norm_sub_taylorSum_le` for `s ↦ G (p + s • w)` on `[0, 1]`, whose `k`-th derivative is
`G_k (p + s • w)` applied to `w` `k` times (`HasFDerivAt.comp_hasDerivAt` and
`HasFDerivAt.clm_apply`); it is the order-four analogue of
`norm_sub_sub_smul_apply_le_of_hasFDerivAt`. -/
theorem _root_.norm_sub_taylor_segment_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : X → X} {G₁ : X → X →L[ℝ] X} {G₂ : X → X →L[ℝ] X →L[ℝ] X}
    {G₃ : X → X →L[ℝ] X →L[ℝ] X →L[ℝ] X} {G₄ : X → X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] X} {M : ℝ}
    (h1 : ∀ p, HasFDerivAt G (G₁ p) p) (h2 : ∀ p, HasFDerivAt G₁ (G₂ p) p)
    (h3 : ∀ p, HasFDerivAt G₂ (G₃ p) p) (h4 : ∀ p, HasFDerivAt G₃ (G₄ p) p)
    (hM : ∀ p, ‖G₄ p‖ ≤ M) (p w : X) :
    ‖G (p + w) - G p - G₁ p w - (2⁻¹ : ℝ) • G₂ p w w - (6⁻¹ : ℝ) • G₃ p w w w‖
      ≤ M * ‖w‖ ^ 4 / 24 := by
  have hseg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p + s • w) w s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const w).const_add p
  obtain ⟨Y, e0, e1, e2, e3, e4⟩ :
      ∃ Y : ℕ → ℝ → X, Y 0 = (fun s => G (p + s • w)) ∧ Y 1 = (fun s => G₁ (p + s • w) w) ∧
        Y 2 = (fun s => G₂ (p + s • w) w w) ∧ Y 3 = (fun s => G₃ (p + s • w) w w w) ∧
        Y 4 = (fun s => G₄ (p + s • w) w w w w) :=
    ⟨fun k => match k with
      | 0 => fun s => G (p + s • w)
      | 1 => fun s => G₁ (p + s • w) w
      | 2 => fun s => G₂ (p + s • w) w w
      | 3 => fun s => G₃ (p + s • w) w w w
      | _ => fun s => G₄ (p + s • w) w w w w,
     rfl, rfl, rfl, rfl, rfl⟩
  have hd0 : ∀ s : ℝ, HasDerivAt (Y 0) (Y 1 s) s := by
    intro s
    rw [e0, e1]
    exact (h1 _).comp_hasDerivAt s (hseg s)
  have hd1 : ∀ s : ℝ, HasDerivAt (Y 1) (Y 2 s) s := by
    intro s
    rw [e1, e2]
    have hc : HasDerivAt (fun s : ℝ => G₁ (p + s • w)) (G₂ (p + s • w) w) s :=
      (h2 _).comp_hasDerivAt s (hseg s)
    simpa using hc.clm_apply (hasDerivAt_const s w)
  have hd2 : ∀ s : ℝ, HasDerivAt (Y 2) (Y 3 s) s := by
    intro s
    rw [e2, e3]
    have hc : HasDerivAt (fun s : ℝ => G₂ (p + s • w)) (G₃ (p + s • w) w) s :=
      (h3 _).comp_hasDerivAt s (hseg s)
    have hc2 : HasDerivAt (fun s : ℝ => G₂ (p + s • w) w) (G₃ (p + s • w) w w) s := by
      simpa using hc.clm_apply (hasDerivAt_const s w)
    simpa using hc2.clm_apply (hasDerivAt_const s w)
  have hd3 : ∀ s : ℝ, HasDerivAt (Y 3) (Y 4 s) s := by
    intro s
    rw [e3, e4]
    have hc : HasDerivAt (fun s : ℝ => G₃ (p + s • w)) (G₄ (p + s • w) w) s :=
      (h4 _).comp_hasDerivAt s (hseg s)
    have hc2 : HasDerivAt (fun s : ℝ => G₃ (p + s • w) w) (G₄ (p + s • w) w w) s := by
      simpa using hc.clm_apply (hasDerivAt_const s w)
    have hc3 : HasDerivAt (fun s : ℝ => G₃ (p + s • w) w w) (G₄ (p + s • w) w w w) s := by
      simpa using hc2.clm_apply (hasDerivAt_const s w)
    simpa using hc3.clm_apply (hasDerivAt_const s w)
  have hY : ∀ k ≤ 3, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (Y k) (Y (k + 1) s) (Icc 0 1) s := by
    intro k hk s _
    rcases k with _ | _ | _ | _ | k
    · exact (hd0 s).hasDerivWithinAt
    · exact (hd1 s).hasDerivWithinAt
    · exact (hd2 s).hasDerivWithinAt
    · exact (hd3 s).hasDerivWithinAt
    · omega
  have hMY : ∀ s ∈ Icc (0 : ℝ) 1, ‖Y 4 s‖ ≤ M * ‖w‖ ^ 4 := by
    intro s _
    rw [e4]
    calc ‖G₄ (p + s • w) w w w w‖ ≤ ‖G₄ (p + s • w) w w w‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w) w w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w) w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖G₄ (p + s • w)‖ * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖w‖ * ‖w‖ * ‖w‖ * ‖w‖ := by gcongr; exact hM _
      _ = M * ‖w‖ ^ 4 := by ring
  have key := norm_sub_taylorSum_le (Y := Y) (n := 3) (M := M * ‖w‖ ^ 4) zero_le_one hY hMY
  have hgoal : G (p + w) - G p - G₁ p w - (2⁻¹ : ℝ) • G₂ p w w - (6⁻¹ : ℝ) • G₃ p w w w
      = Y 0 1 - ∑ k ∈ range 4, (((1 : ℝ) - 0) ^ k / (Nat.factorial k : ℝ)) • Y k 0 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e0, e1, e2, e3]
    norm_num
    abel
  rw [hgoal]
  refine key.trans (le_of_eq ?_)
  norm_num

variable {F : ℝ × E → E} {F' : ℝ × E → ℝ × E →L[ℝ] E} {F'' : ℝ × E → ℝ × E →L[ℝ] ℝ × E →L[ℝ] E}

/-- The segment bound `norm_sub_sub_smul_apply_le_of_hasFDerivAt` for `σ ≥ 0`. -/
theorem _root_.norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg
    (hF : ∀ p, HasFDerivAt F (F' p) p) (hF' : ∀ p, HasFDerivAt F' (F'' p) p)
    (hM : ∀ p, ‖F'' p‖ ≤ M) (p v : ℝ × E) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M * ‖v‖ ^ 2 * σ ^ 2 / 2 := by
  have hseg : ∀ s : ℝ, HasDerivAt (fun s : ℝ => p + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add p
  have hφ : ∀ s : ℝ, HasDerivAt (fun s => F (p + s • v)) (F' (p + s • v) v) s := fun s =>
    (hF _).comp_hasDerivAt s (hseg s)
  have hφ' : ∀ s : ℝ, HasDerivAt (fun s => F' (p + s • v) v) (F'' (p + s • v) v v) s := by
    intro s
    have := ((hF' _).comp_hasDerivAt s (hseg s)).clm_apply (hasDerivAt_const s v)
    simpa using this
  have hbound : ∀ s ∈ Icc 0 σ, ‖F'' (p + s • v) v v‖ ≤ M * ‖v‖ ^ 2 := fun s _ => by
    calc ‖F'' (p + s • v) v v‖ ≤ ‖F'' (p + s • v) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖F'' (p + s • v)‖ * ‖v‖ * ‖v‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖v‖ * ‖v‖ := by gcongr; exact hM _
      _ = M * ‖v‖ ^ 2 := by ring
  have key := norm_sub_sub_smul_le_mul_sq_div_two (a := 0) (b := σ) hσ
    (fun s _ => (hφ s).hasDerivWithinAt) (fun s _ => (hφ' s).hasDerivWithinAt) hbound
  simpa using key

/-- **Second-order Taylor bound along a segment** for a map `F : ℝ × E → E` with Fréchet
derivatives `F'` and `F''`, `‖F''‖ ≤ M`:
`‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M ‖v‖² σ² / 2` for every real `σ`. This is the
one-variable bound `norm_sub_sub_smul_le_mul_sq_div_two` for `s ↦ F (p + s • v)`, whose second
derivative is `F'' (p + s • v) v v`; a negative `σ` is the case of `-v`. -/
theorem _root_.norm_sub_sub_smul_apply_le_of_hasFDerivAt (hF : ∀ p, HasFDerivAt F (F' p) p)
    (hF' : ∀ p, HasFDerivAt F' (F'' p) p) (hM : ∀ p, ‖F'' p‖ ≤ M) (p v : ℝ × E) (σ : ℝ) :
    ‖F (p + σ • v) - F p - σ • F' p v‖ ≤ M * ‖v‖ ^ 2 * σ ^ 2 / 2 := by
  rcases le_or_gt 0 σ with hσ | hσ
  · exact norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg hF hF' hM p v hσ
  · have := norm_sub_sub_smul_apply_le_of_hasFDerivAt_of_nonneg hF hF' hM p (-v)
      (neg_nonneg.2 hσ.le)
    simpa [smul_neg, neg_smul] using this

end Taylor

namespace ButcherTableau

/-- **The two-stage order-two conditions are sufficient** ([quarteroni2000numerical] §11.8.1):
an explicit two-stage tableau satisfying the row-sum condition, `b₁ + b₂ = 1` and `c₂ b₂ = 1/2`
(here `b 0 + b 1 = 1`, `c 1 * b 1 = 1/2`) has order `2` along every solution `y` of `y' = f(t, y)`
on `[t₀, t₀ + T]` whose field `F(t, v) = f t v` has Fréchet derivatives `F'`, `F''` on `ℝ × E`
with `‖F''‖ ≤ M₂`, and whose derivatives `y'' = (f(·, y ·))'` and `y'''` exist on the interval
with `‖y'''‖ ≤ M₃`. The second stage `K₂ = F((t, y t) + c₂ h (1, K₁))` is `y' + c₂ h y'' + O(h²)`
by the Taylor bound along the segment, `y'' = F'(t, y t)(1, y')` by the chain rule, and the
conditions cancel the `h` and `h²` terms against the Taylor expansion of `y(t + h)`; the
constant is `M₃ / 6 + |b₂| M₂ (1 + M₁)² c₂² / 2` with `M₁` a bound of `‖y'‖`. -/
theorem hasOrderFor_two_of (tab : ButcherTableau 2) (hex : tab.IsExplicit) (hrow : tab.IsRowSum)
    (hb : tab.b 0 + tab.b 1 = 1) (hcb : tab.c 1 * tab.b 1 = 1 / 2) {t₀ T : ℝ} {f : ℝ → E → E}
    {F' : ℝ × E → ℝ × E →L[ℝ] E} {F'' : ℝ × E → ℝ × E →L[ℝ] ℝ × E →L[ℝ] E} {M₂ M₃ : ℝ}
    (hF : ∀ p, HasFDerivAt (Function.uncurry f) (F' p) p) (hF' : ∀ p, HasFDerivAt F' (F'' p) p)
    (hM₂ : ∀ p, ‖F'' p‖ ≤ M₂) {y y'' y''' : ℝ → E}
    (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y (f s (y s)) (Icc t₀ (t₀ + T)) s)
    (hy' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s)) (y'' s) (Icc t₀ (t₀ + T)) s)
    (hy'' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt y'' (y''' s) (Icc t₀ (t₀ + T)) s)
    (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), ‖y''' s‖ ≤ M₃) :
    OneStep.HasOrderFor (tab.explicitIncrement f) t₀ T y 2 := by
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (HasDerivWithinAt.continuousOn hy')
  have hc0 : tab.c 0 = 0 := by
    rw [hrow 0, Fin.sum_univ_two, hex 0 0 le_rfl, hex 0 1 (by decide), add_zero]
  have hc1 : tab.c 1 = tab.A 1 0 := by rw [hrow 1, Fin.sum_univ_two, hex 1 1 le_rfl, add_zero]
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  refine OneStep.hasOrderFor_of_forall_norm_lte_le
    (C := M₃ / 6 + |tab.b 1| * M₂ * (1 + max M₁ 0) ^ 2 * tab.c 1 ^ 2 / 2) fun h hh n hn => ?_
  have ht := node_mem_Icc_of_lt (t₀ := t₀) hh hn
  have hth := node_add_mem_Icc_of_lt (t₀ := t₀) hh hn
  set t := node t₀ h n with htdef
  have hsub : Icc t (t + h) ⊆ Icc t₀ (t₀ + T) := Icc_subset_Icc ht.1 hth.2
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg _).trans (hM₃ t ht)
  have hne : h ≠ 0 := hh.ne'
  set σ : ℝ := tab.c 1 * h with hσdef
  -- the stages
  have hK0 : tab.explicitStages f h t (y t) 0 = f t (y t) := by
    rw [explicitStages_apply]; simp [hc0]
  have hK1 : tab.explicitStages f h t (y t) 1 = f (t + σ) (y t + σ • f t (y t)) := by
    rw [explicitStages_apply, Fin.sum_univ_two, hK0]
    simp only [Fin.zero_lt_one, ite_true, lt_self_iff_false, ite_false, add_zero, smul_smul, hσdef,
      hc1, mul_comm h]
  -- the chain rule: `y'' t = F'(t, y t)(1, y' t)`
  have hT : t₀ < t₀ + T := by linarith [ht.1, hth.2, hh]
  have hy''eq : y'' t = F' (t, y t) (1, f t (y t)) := by
    have h1 : HasDerivWithinAt (fun s => Function.uncurry f (s, y s)) (F' (t, y t) (1, f t (y t)))
        (Icc t₀ (t₀ + T)) t :=
      (hF _).comp_hasDerivWithinAt t ((hasDerivWithinAt_id t _).prodMk (hy t ht))
    exact (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hy' t ht) h1
  -- Taylor for `y` on `[t, t + h]`
  have k3 := norm_sub_sub_smul_sub_smul_le_mul_pow_three_div_six (y' := fun s => f s (y s))
    (by linarith [hh] : t ≤ t + h) (fun s hs => (hy s (hsub hs)).mono hsub)
    (fun s hs => (hy' s (hsub hs)).mono hsub) (fun s hs => (hy'' s (hsub hs)).mono hsub)
    (fun s hs => hM₃ s (hsub hs))
  rw [add_sub_cancel_left] at k3
  -- Taylor for the second stage along the segment
  set r : E := tab.explicitStages f h t (y t) 1 - f t (y t) - σ • y'' t with hr
  have hr_bound : ‖r‖ ≤ M₂ * (1 + max M₁ 0) ^ 2 * σ ^ 2 / 2 := by
    have k2 := norm_sub_sub_smul_apply_le_of_hasFDerivAt hF hF' hM₂ (t, y t) (1, f t (y t)) σ
    have hpt : ((t, y t) : ℝ × E) + σ • (1, f t (y t)) = (t + σ, y t + σ • f t (y t)) := by
      simp [Prod.smul_mk]
    rw [hpt, Function.uncurry_apply_pair, Function.uncurry_apply_pair] at k2
    have hv : ‖((1 : ℝ), f t (y t))‖ ≤ 1 + max M₁ 0 := by
      rw [Prod.norm_def]
      refine max_le (by simp) ?_
      calc ‖((1 : ℝ), f t (y t)).2‖ = ‖f t (y t)‖ := rfl
        _ ≤ M₁ := hM₁ t ht
        _ ≤ 1 + max M₁ 0 := by linarith [le_max_left M₁ 0]
    rw [hr, hK1, hy''eq]
    refine k2.trans ?_
    gcongr
  have hK1r : tab.explicitStages f h t (y t) 1 = f t (y t) + σ • y'' t + r := by rw [hr]; abel
  -- the residual: the order conditions cancel the `h` and `h²` terms
  have key : y (t + h) - y t - h • tab.explicitIncrement f t (y t) (y (t + h)) h =
      (y (t + h) - y t - h • f t (y t) - (h ^ 2 / 2) • y'' t) - (h * tab.b 1) • r := by
    have e1 : 1 - (tab.b 0 + tab.b 1) = 0 := by linarith
    have e2 : 1 / 2 - tab.c 1 * tab.b 1 = 0 := by linarith
    have : y (t + h) - y t - h • tab.explicitIncrement f t (y t) (y (t + h)) h -
        ((y (t + h) - y t - h • f t (y t) - (h ^ 2 / 2) • y'' t) - (h * tab.b 1) • r) =
        (h * (1 - (tab.b 0 + tab.b 1))) • f t (y t) +
          (h ^ 2 * (1 / 2 - tab.c 1 * tab.b 1)) • y'' t := by
      rw [explicitIncrement_apply, Fin.sum_univ_two, hK0, hK1r, hσdef]
      module
    rw [e1, e2, mul_zero, mul_zero, zero_smul, zero_smul, add_zero, sub_eq_zero] at this
    exact this
  rw [OneStep.lte_eq_inv_smul hne, key, norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have hres : ‖(y (t + h) - y t - h • f t (y t) - (h ^ 2 / 2) • y'' t) - (h * tab.b 1) • r‖ ≤
      M₃ * h ^ 3 / 6 + h * |tab.b 1| * (M₂ * (1 + max M₁ 0) ^ 2 * σ ^ 2 / 2) := by
    refine (norm_sub_le _ _).trans (add_le_add k3 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hr_bound (by positivity)
  calc h⁻¹ * ‖(y (t + h) - y t - h • f t (y t) - (h ^ 2 / 2) • y'' t) - (h * tab.b 1) • r‖
      ≤ h⁻¹ * (M₃ * h ^ 3 / 6 + h * |tab.b 1| * (M₂ * (1 + max M₁ 0) ^ 2 * σ ^ 2 / 2)) := by
        gcongr
    _ = (M₃ / 6 + |tab.b 1| * M₂ * (1 + max M₁ 0) ^ 2 * tab.c 1 ^ 2 / 2) * h ^ 2 := by
        rw [hσdef]
        field_simp

end ButcherTableau

end ODE
