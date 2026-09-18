import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Numlib.Analysis.InnerProductSpace.MaximalMonotone

/-!
# The Hille–Yosida theorem on a real Hilbert space

The evolution problem `u' + A u = 0` on `[0, ∞)`, `u(0) = u₀`, for a maximal monotone operator
`A` on a real Hilbert space `H`: its contraction semigroup `S_A(t)`, existence and uniqueness of
the solution for `u₀ ∈ D(A)` (the Hille–Yosida theorem, [brezis2011functional] Theorem 7.4), the
regularity `u ∈ C^{k-j}([0, ∞); D(A^j))` for `u₀ ∈ D(A^k)` (Theorem 7.5), and the self-adjoint
case, in which every `u₀ ∈ H` gives a solution that is smooth for `t > 0` (Theorem 7.7). Builds
on `Numlib/Analysis/InnerProductSpace/MaximalMonotone` (`IsMaximalMonotone`, `resolvent`,
`yosida`, `PowDomain`, `powPart`).

## Scalars

The module is over `ℝ`. Time derivatives of `u : ℝ → H` need `NormedSpace ℝ H`, and the energy
identity `d/dt ‖u‖² = 2 ⟪u', u⟫` used in every step (`HasDerivAt.norm_sq`) is stated for real
inner product spaces; each of the graph spaces `D(A^k)` would need the real structure too. The
proofs are generic in the real part; a complex version is a restatement, not a new proof.

## The solution concept

`LinearPMap.IsSolutionOn A u₀ s u` says `u 0 = u₀`, `u t ∈ D(A)` for `t ∈ s`, and
`HasDerivWithinAt u (-A (u t)) s t` for `t ∈ s` (one-sided at `t = 0` when `s = Ici 0`). The
book's `C¹([0, ∞); H)` is `ContDiffOn ℝ 1 u (Ici 0)`; `u ∈ C^n(s; D(A^j))` is
`LinearPMap.ContDiffOnPowDomain A n j u s`, "`u` lifts on `s` to a `C^n` map into the Hilbert
space `D(A^j)`", read componentwise by `contDiffOnPowDomain_iff`.

## The proof route

The approximate problem `u_λ' + A_λ u_λ = 0` is solved in closed form by `u_λ(t) = exp(-t A_λ) u₀`
with Mathlib's `NormedSpace.exp` (`LinearPMap.expYosida`), not by the Cauchy–Lipschitz theorem.
Two consequences shorten the book's six steps: the derivatives `u_λ' = -exp(-t A_λ) A_λ u₀`
converge as soon as `exp(-t A_λ) w → S(t) w` for every `w` and `A_λ u₀ → A u₀`, so the book's
Step 4, Step 6 and Lemma 7.2 are not needed and existence holds for every `u₀ ∈ D(A)` at once;
and the limit `S(t) u₀ = lim exp(-t A_λ) u₀` exists for every `u₀ ∈ H`, so the contraction
semigroup `LinearPMap.semigroup A t : H →L[ℝ] H` is defined first (as a total, junk-valued
function like `resolvent`) and the solution of the evolution problem is `t ↦ S(t) u₀`.

The steps that survive: Step 1, uniqueness by monotonicity
(`IsMonotone.norm_sub_le_of_isSolutionOn`); Step 2, Lemma 7.1 for a bounded monotone operator
(`antitoneOn_norm_exp_neg_smul_apply`); Step 3, the Cauchy estimate
`‖u_λ(t) - u_μ(t)‖² ≤ ‖w₀ - w₁‖² + 4 (λ + μ) t M²` (`norm_expYosida_sub_expYosida_le`) and the
limit (`tendsto_expYosida_semigroup`, uniform on bounded intervals); Step 5, the derivative of
the uniform limit (`hasDerivWithinAt_Icc_of_tendstoUniformlyOn`, a closed-interval version of
Mathlib's `hasDerivAt_of_tendstoUniformlyOn`, proved through the fundamental theorem of
calculus) and the closed graph (`hasDerivWithinAt_semigroup_apply`). Theorems 7.5 and 7.7 are
inductions over the level `j` applying the theory to the part `A.powPart j` on the Hilbert space
`A.PowDomain j`; every statement about `semigroup` is therefore made for an arbitrary real Hilbert
space. Theorem 7.7's smoothing estimate `‖A S(t) u₀‖ ≤ ‖u₀‖ / t` comes from a Lyapunov function
(`norm_exp_neg_smul_apply_le_div`), the book's integrations by parts replaced by one derivative.

## References

[brezis2011functional], Chapter 7, §7.2–§7.4.
-/

open Filter Topology Set Metric WithLp
open scoped InnerProductSpace

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Solutions of the evolution equation -/

variable (A : H →ₗ.[ℝ] H) in
/-- `u` **solves the evolution problem** `u' + A u = 0` on the set of times `s`, with the initial
value `u 0 = u₀` ([brezis2011functional] §7.2, problem (6)): `u t ∈ D(A)` for `t ∈ s`, and the
derivative of `u` within `s` at `t ∈ s` is `-A (u t)` (one-sided at `t = 0` when `s = Ici 0`).
The `C¹` requirement of the book is a separate conjunct in the theorems. -/
structure IsSolutionOn (u₀ : H) (s : Set ℝ) (u : ℝ → H) : Prop where
  /-- The initial condition. -/
  apply_zero : u 0 = u₀
  /-- The solution takes its values in `D(A)`. -/
  mem_domain : ∀ t ∈ s, u t ∈ A.domain
  /-- The equation `u' = -A u` within `s`. -/
  hasDerivWithinAt : ∀ t (ht : t ∈ s), HasDerivWithinAt u (-A ⟨u t, mem_domain t ht⟩) s t

variable {A : H →ₗ.[ℝ] H} {u₀ v₀ : H} {s : Set ℝ} {u v : ℝ → H}

/-- A solution is continuous on its set of times. -/
theorem IsSolutionOn.continuousOn (h : A.IsSolutionOn u₀ s u) : ContinuousOn u s :=
  fun t ht => (h.hasDerivWithinAt t ht).continuousWithinAt

/-- A solution on `s` is a solution on every subset of `s`. -/
theorem IsSolutionOn.mono (h : A.IsSolutionOn u₀ s u) {t : Set ℝ} (hts : t ⊆ s) :
    A.IsSolutionOn u₀ t u where
  apply_zero := h.apply_zero
  mem_domain x hx := h.mem_domain x (hts hx)
  hasDerivWithinAt x hx := (h.hasDerivWithinAt x (hts hx)).mono hts

/-- **Time shift**: if `u` solves the problem on `[0, ∞)` and `a ≥ 0`, then `t ↦ u (t + a)` solves
it with the initial value `u a` ([brezis2011functional] Chapter 7, Remark 5). -/
theorem IsSolutionOn.comp_add (h : A.IsSolutionOn u₀ (Ici 0) u) {a : ℝ} (ha : 0 ≤ a) :
    A.IsSolutionOn (u a) (Ici 0) fun t => u (t + a) where
  apply_zero := by simp
  mem_domain t ht := h.mem_domain (t + a) (add_nonneg ht ha)
  hasDerivWithinAt t ht := by
    have h1 := h.hasDerivWithinAt (t + a) (add_nonneg ht ha)
    have h2 : HasDerivWithinAt (fun t : ℝ => t + a) 1 (Ici 0) t :=
      (hasDerivWithinAt_id _ _).add_const a
    have := h1.scomp t h2 fun x hx => add_nonneg hx ha
    simpa [Function.comp_def] using this

/-- **Remark 6, the forward direction**: if `u` solves `u' + A u + c u = 0` then
`v(t) = e^{c t} u(t)` solves `v' + A v = 0`, with the same initial value
([brezis2011functional] Chapter 7, Remark 6). The operator `A + c I` is
`(c • LinearMap.id) +ᵥ A`, with domain `D(A)`. -/
theorem IsSolutionOn.exp_smul {c : ℝ}
    (h : ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ s u) :
    A.IsSolutionOn u₀ s fun t => Real.exp (c * t) • u t := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * t) * c) t :=
    fun t => by simpa using ((hasDerivAt_id t).const_mul c).exp
  refine ⟨by simpa using h.apply_zero, fun t ht => Submodule.smul_mem _ _ (h.mem_domain t ht),
    fun t ht => ?_⟩
  have h2 := HasDerivWithinAt.smul (hexp t).hasDerivWithinAt (h.hasDerivWithinAt t ht)
  convert h2 using 1
  change -A (Real.exp (c * t) • ⟨u t, h.mem_domain t ht⟩) = _
  rw [map_smul, vadd_apply, LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- **Remark 6**: `u` solves `u' + A u + c u = 0` iff `v(t) = e^{c t} u(t)` solves `v' + A v = 0`,
with the same initial value ([brezis2011functional] Chapter 7, Remark 6). -/
theorem isSolutionOn_smul_id_vadd_iff {c : ℝ} :
    ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).IsSolutionOn u₀ s u ↔
      A.IsSolutionOn u₀ s fun t => Real.exp (c * t) • u t := by
  refine ⟨IsSolutionOn.exp_smul, fun h => ?_⟩
  have hA : ((-c) • LinearMap.id : H →ₗ[ℝ] H) +ᵥ ((c • LinearMap.id : H →ₗ[ℝ] H) +ᵥ A) = A := by
    rw [← add_vadd, ← add_smul, neg_add_cancel, zero_smul, zero_vadd]
  rw [← hA] at h
  have h' := h.exp_smul
  convert h' using 1
  funext t
  rw [smul_smul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_smul]

/-! ### Step 1: uniqueness by monotonicity -/

/-- **Step 1 of the proof of the Hille–Yosida theorem, in its quantitative form**, for solutions
on `(0, ∞)` that are continuous on `[0, ∞)`: for a monotone `A`, `t ↦ ‖u t - v t‖` is antitone on
`[0, ∞)`, since `½ d/dt ‖u - v‖² = -⟪A (u - v), u - v⟫ ≤ 0` on `(0, ∞)`
([brezis2011functional], proof of Theorem 7.4, Step 1, and proof of Theorem 7.7, uniqueness). -/
theorem IsMonotone.antitoneOn_norm_sub_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn v₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) :
    AntitoneOn (fun t => ‖u t - v t‖) (Ici 0) := by
  have key : ∀ x (hx : x ∈ Ioi (0 : ℝ)), HasDerivAt (fun t => ‖u t - v t‖ ^ 2)
      (2 * ⟪u x - v x, -A ⟨u x, hu.mem_domain x hx⟩ - -A ⟨v x, hv.mem_domain x hx⟩⟫_ℝ) x :=
    fun x hx => (((hu.hasDerivWithinAt x hx).sub (hv.hasDerivWithinAt x hx)).hasDerivAt
      (Ioi_mem_nhds hx)).norm_sq
  have hφ : AntitoneOn (fun t => ‖u t - v t‖ ^ 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ((hu'.sub hv').norm.pow 2) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx => (key x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(key x hx).deriv]
      have hm := hA (⟨u x, hu.mem_domain x hx⟩ - ⟨v x, hv.mem_domain x hx⟩)
      rw [map_sub, Submodule.coe_sub, RCLike.re_to_real] at hm
      rw [neg_sub_neg, ← neg_sub (A ⟨u x, hu.mem_domain x hx⟩), inner_neg_right, real_inner_comm]
      linarith
  intro a ha b hb hab
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hφ ha hb hab)

/-- **Step 1, the contraction estimate on `(0, ∞)`**: `‖u t - v t‖ ≤ ‖u₀ - v₀‖` for `t ≥ 0`, for
two solutions on `(0, ∞)` continuous on `[0, ∞)` of a monotone `A`. -/
theorem IsMonotone.norm_sub_le_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn v₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u₀ - v₀‖ := by
  have := hA.antitoneOn_norm_sub_of_isSolutionOn_Ioi hu hv hu' hv' self_mem_Ici ht ht
  simp only [hu.apply_zero, hv.apply_zero] at this
  exact this

/-- **Step 1 of the proof of the Hille–Yosida theorem**: for a monotone `A` and two solutions on
`[0, ∞)`, `t ↦ ‖u t - v t‖` is antitone on `[0, ∞)` and `‖u t - v t‖ ≤ ‖u₀ - v₀‖`
([brezis2011functional], proof of Theorem 7.4, Step 1). -/
theorem IsMonotone.norm_sub_le_of_isSolutionOn (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ici 0) u) (hv : A.IsSolutionOn v₀ (Ici 0) v) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u₀ - v₀‖ :=
  hA.norm_sub_le_of_isSolutionOn_Ioi (hu.mono Ioi_subset_Ici_self) (hv.mono Ioi_subset_Ici_self)
    hu.continuousOn hv.continuousOn ht

/-- **Uniqueness in the Hille–Yosida theorem**: two solutions on `[0, ∞)` with the same initial
value agree on `[0, ∞)`; monotonicity alone suffices ([brezis2011functional] Theorem 7.4). -/
theorem IsMonotone.eqOn_of_isSolutionOn (hA : A.IsMonotone) (hu : A.IsSolutionOn u₀ (Ici 0) u)
    (hv : A.IsSolutionOn u₀ (Ici 0) v) : EqOn u v (Ici 0) := fun t ht => by
  have := hA.norm_sub_le_of_isSolutionOn hu hv ht
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- **Uniqueness in Theorem 7.7**: two solutions on `(0, ∞)`, continuous on `[0, ∞)`, with the
same initial value agree on `[0, ∞)` ([brezis2011functional], proof of Theorem 7.7). -/
theorem IsMonotone.eqOn_of_isSolutionOn_Ioi (hA : A.IsMonotone)
    (hu : A.IsSolutionOn u₀ (Ioi 0) u) (hv : A.IsSolutionOn u₀ (Ioi 0) v)
    (hu' : ContinuousOn u (Ici 0)) (hv' : ContinuousOn v (Ici 0)) : EqOn u v (Ici 0) :=
  fun t ht => by
  have := hA.norm_sub_le_of_isSolutionOn_Ioi hu hv hu' hv' ht
  rw [sub_self, norm_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end LinearPMap

/-! ### The exponential of a bounded operator, and Lemma 7.1 -/

section Exp

open NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `t ↦ exp(-t B) w` has derivative `-B (exp(-t B) w)`: it solves `w' + B w = 0`. -/
theorem hasDerivAt_exp_neg_smul_apply (B : E →L[ℝ] E) (w : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => exp ((-t) • B) w) (-(B (exp ((-t) • B) w))) t := by
  have h1 : HasDerivAt (fun t : ℝ => exp ((-t) • B)) ((-B) * exp ((-t) • B)) t := by
    have := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-B) t
    simpa only [smul_neg, neg_smul] using this
  have h3 := h1.clm_apply (hasDerivAt_const t w)
  simpa using h3

omit [CompleteSpace E] in
/-- `exp(-t B)` commutes with `B`. -/
theorem exp_neg_smul_apply_comm (B : E →L[ℝ] E) (w : E) (t : ℝ) :
    B (exp ((-t) • B) w) = exp ((-t) • B) (B w) := by
  have h : Commute B (exp ((-t) • B)) := ((Commute.refl B).smul_right (-t)).exp_right
  exact DFunLike.congr_fun h w

omit [CompleteSpace E] in
/-- `exp(-0 B) = 1`. -/
theorem exp_neg_smul_zero_apply (B : E →L[ℝ] E) (w : E) : exp ((-(0 : ℝ)) • B) w = w := by
  simp [exp_zero]

/-- `t ↦ exp(-t B) w` is continuous. -/
theorem continuous_exp_neg_smul_apply (B : E →L[ℝ] E) (w : E) :
    Continuous fun t : ℝ => exp ((-t) • B) w :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_neg_smul_apply B w t).continuousAt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lemma 7.1** for a bounded monotone operator: if `0 ≤ ⟪B v, v⟫` for all `v`, then
`t ↦ ‖exp(-t B) w‖` is antitone on `[0, ∞)`, because `½ d/dt ‖exp(-t B) w‖² = -⟪B u, u⟫ ≤ 0`
([brezis2011functional] Lemma 7.1; the book's second clause, about `‖w'(t)‖`, is this lemma
applied to `w' = exp(-t B) (-B w)`). -/
theorem antitoneOn_norm_exp_neg_smul_apply (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) :
    AntitoneOn (fun t : ℝ => ‖exp ((-t) • B) w‖) (Ici 0) := by
  have key : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ‖exp ((-t) • B) w‖ ^ 2)
      (2 * ⟪exp ((-t) • B) w, -(B (exp ((-t) • B) w))⟫_ℝ) t :=
    fun t => (hasDerivAt_exp_neg_smul_apply B w t).norm_sq
  have hφ : AntitoneOn (fun t : ℝ => ‖exp ((-t) • B) w‖ ^ 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (key t).continuousAt.continuousWithinAt)
      (fun t _ => (key t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(key t).deriv, inner_neg_right, real_inner_comm]
    linarith [hB (exp ((-t) • B) w)]
  intro a ha b hb hab
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (hφ ha hb hab)

/-- For a bounded monotone `B` and `t ≥ 0`, `‖exp(-t B) w‖ ≤ ‖w‖`. -/
theorem norm_exp_neg_smul_apply_le (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp ((-t) • B) w‖ ≤ ‖w‖ := by
  have := antitoneOn_norm_exp_neg_smul_apply B hB w self_mem_Ici ht ht
  simp only [exp_neg_smul_zero_apply] at this
  exact this

/-- For a bounded monotone `B` and `t ≥ 0`, `‖exp(-t B)‖ ≤ 1`. -/
theorem norm_exp_neg_smul_le_one (B : H →L[ℝ] H) (hB : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp ((-t) • B)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    exact norm_exp_neg_smul_apply_le B hB w ht

end Exp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : H →ₗ.[ℝ] H}

/-! ### The approximate problem: `u_λ(t) = exp(-t A_λ) u₀` -/

variable (A) in
/-- The solution operator `exp(-t A_c)` of the approximate problem `u' + A_c u = 0`
([brezis2011functional] §7.2, problem (7)): `u_c(t) = A.expYosida c t u₀`. -/
def expYosida (c t : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp ((-t) • A.yosida c)

variable [CompleteSpace H]

/-- `t ↦ u_c(t) w` solves `u' + A_c u = 0`. -/
theorem hasDerivAt_expYosida_apply (c : ℝ) (w : H) (t : ℝ) :
    HasDerivAt (fun t => A.expYosida c t w) (-(A.yosida c (A.expYosida c t w))) t :=
  hasDerivAt_exp_neg_smul_apply _ w t

omit [CompleteSpace H] in
/-- `u_c(0) = I`. -/
theorem expYosida_zero (c : ℝ) : A.expYosida c 0 = 1 := by
  simp [expYosida, NormedSpace.exp_zero]

omit [CompleteSpace H] in
/-- `A_c` commutes with `u_c(t)`. -/
theorem yosida_expYosida_comm (c t : ℝ) (w : H) :
    A.yosida c (A.expYosida c t w) = A.expYosida c t (A.yosida c w) :=
  exp_neg_smul_apply_comm _ w t

/-- `t ↦ u_c(t) w` is continuous. -/
theorem continuous_expYosida_apply (c : ℝ) (w : H) : Continuous fun t => A.expYosida c t w :=
  continuous_exp_neg_smul_apply _ w

/-- The Yosida approximation of a maximal monotone operator is a bounded monotone operator, in
the real form used by the exponential lemmas. -/
theorem IsMaximalMonotone.inner_yosida_nonneg (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c)
    (v : H) : 0 ≤ ⟪A.yosida c v, v⟫_ℝ := by
  simpa using hA.re_inner_yosida_nonneg hc v

/-- **Estimate (8) of Step 2**: `‖u_c(t) w‖ ≤ ‖w‖` for `t ≥ 0` — Lemma 7.1 for `B = A_c`,
monotone by Proposition 7.2 (e) ([brezis2011functional], proof of Theorem 7.4, Step 2). -/
theorem IsMaximalMonotone.norm_expYosida_apply_le (hA : A.IsMaximalMonotone) {c : ℝ} (hc : 0 < c)
    {t : ℝ} (ht : 0 ≤ t) (w : H) : ‖A.expYosida c t w‖ ≤ ‖w‖ :=
  norm_exp_neg_smul_apply_le _ (hA.inner_yosida_nonneg hc) w ht

/-- `t ↦ ‖u_c(t) w‖` is antitone on `[0, ∞)` ([brezis2011functional] Lemma 7.1). -/
theorem IsMaximalMonotone.antitoneOn_norm_expYosida_apply (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) (w : H) : AntitoneOn (fun t => ‖A.expYosida c t w‖) (Ici 0) :=
  antitoneOn_norm_exp_neg_smul_apply _ (hA.inner_yosida_nonneg hc) w

/-- **Estimate (9) of Step 2**: `‖A_c u_c(t) w‖ ≤ ‖A_c w‖` for `t ≥ 0`, i.e. `‖u_c'(t)‖` is bounded
by its value at `0` ([brezis2011functional], proof of Theorem 7.4, Step 2). -/
theorem IsMaximalMonotone.norm_yosida_expYosida_apply_le (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (w : H) :
    ‖A.yosida c (A.expYosida c t w)‖ ≤ ‖A.yosida c w‖ := by
  rw [yosida_expYosida_comm]
  exact hA.norm_expYosida_apply_le hc ht _

/-- **Estimate (9) of Step 2 on the domain**: `‖u_c'(t)‖ = ‖A_c u_c(t) u₀‖ ≤ ‖A u₀‖` for
`u₀ ∈ D(A)`, by Proposition 7.2 (b) ([brezis2011functional], proof of Theorem 7.4, (9)). -/
theorem IsMaximalMonotone.norm_yosida_expYosida_apply_le_norm_apply (hA : A.IsMaximalMonotone)
    {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (u₀ : A.domain) :
    ‖A.yosida c (A.expYosida c t u₀)‖ ≤ ‖A u₀‖ :=
  (hA.norm_yosida_expYosida_apply_le hc ht u₀).trans (hA.norm_yosida_apply_le_norm_apply hc u₀)

/-- **Step 3, the Cauchy estimate (13)**, for two data so that it also serves the derivatives:
if `‖A_c w₀‖ ≤ M` and `‖A_d w₁‖ ≤ M`, then for `t ≥ 0`
`‖u_c(t) w₀ - u_d(t) w₁‖² ≤ ‖w₀ - w₁‖² + 4 (c + d) t M²`. The function `φ = ‖u_c - u_d‖²` has
derivative `-2 ⟪A_c u_c - A_d u_d, u_c - u_d⟫ ≤ -2 ⟪A_c u_c - A_d u_d, c A_c u_c - d A_d u_d⟫`
by the inequality (12), which is at most `4 (c + d) M²` by (9)
([brezis2011functional], proof of Theorem 7.4, Step 3). -/
theorem IsMaximalMonotone.norm_expYosida_sub_expYosida_le (hA : A.IsMaximalMonotone) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) {w₀ w₁ : H} {M : ℝ}
    (h₀ : ‖A.yosida c w₀‖ ≤ M) (h₁ : ‖A.yosida d w₁‖ ≤ M) :
    ‖A.expYosida c t w₀ - A.expYosida d t w₁‖ ^ 2 ≤ ‖w₀ - w₁‖ ^ 2 + 4 * (c + d) * t * M ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans h₀
  set φ : ℝ → ℝ := fun s => ‖A.expYosida c s w₀ - A.expYosida d s w₁‖ ^ 2 with hφ
  set φ' : ℝ → ℝ := fun s => 2 * ⟪A.expYosida c s w₀ - A.expYosida d s w₁,
    -(A.yosida c (A.expYosida c s w₀)) - -(A.yosida d (A.expYosida d s w₁))⟫_ℝ with hφ'
  have hderiv : ∀ s, HasDerivAt φ (φ' s) s := fun s =>
    ((hasDerivAt_expYosida_apply c w₀ s).sub (hasDerivAt_expYosida_apply d w₁ s)).norm_sq
  have hbound : ∀ s ∈ Ico 0 t, φ' s ≤ 4 * (c + d) * M ^ 2 := by
    intro s hs
    set x := A.expYosida c s w₀
    set y := A.expYosida d s w₁
    set a := A.yosida c x
    set b := A.yosida d y
    have ha : ‖a‖ ≤ M := (hA.norm_yosida_expYosida_apply_le hc hs.1 w₀).trans h₀
    have hb : ‖b‖ ≤ M := (hA.norm_yosida_expYosida_apply_le hd hs.1 w₁).trans h₁
    have h12 := hA.re_inner_yosida_sub_yosida_ge hc hd x y
    simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id] at h12
    have h2 : -(‖a - b‖ * ‖c • a - d • b‖) ≤ ⟪a - b, c • a - d • b⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have h3 : ‖a - b‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith)
    have h4 : ‖c • a - d • b‖ ≤ (c + d) * M := by
      calc ‖c • a - d • b‖ ≤ ‖c • a‖ + ‖d • b‖ := norm_sub_le _ _
        _ = c * ‖a‖ + d * ‖b‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
        _ ≤ c * M + d * M := by gcongr
        _ = (c + d) * M := by ring
    have h5 : ‖a - b‖ * ‖c • a - d • b‖ ≤ 2 * M * ((c + d) * M) :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    simp only [hφ']
    rw [neg_sub_neg, ← neg_sub a b, inner_neg_right, real_inner_comm]
    nlinarith [h12, h2, h5]
  have hφ0 : φ 0 = ‖w₀ - w₁‖ ^ 2 := by simp [hφ, expYosida_zero]
  have := image_le_of_deriv_right_le_deriv_boundary (f := φ) (f' := φ') (a := 0) (b := t)
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (B := fun s => φ 0 + 4 * (c + d) * M ^ 2 * s) (B' := fun _ => 4 * (c + d) * M ^ 2)
    (by simp) (by fun_prop)
    (fun s _ => by
      simpa using (((hasDerivAt_id s).const_mul (4 * (c + d) * M ^ 2)).const_add
        (φ 0)).hasDerivWithinAt (s := Ici s)) hbound
    (right_mem_Icc.2 ht)
  rw [hφ0] at this
  linarith

/-! ### The semigroup `S_A(t) = lim exp(-t A_λ)` -/

/-- **The Cauchy estimate on the domain, in `ε`–`δ` form**: for `v₀ ∈ D(A)` and `t ≥ 0`, the
family `u_c(t) v₀` is Cauchy as `c → 0⁺`. -/
theorem IsMaximalMonotone.exists_forall_norm_expYosida_sub_lt (hA : A.IsMaximalMonotone)
    {t : ℝ} (ht : 0 ≤ t) (v₀ : A.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ c d : ℝ, 0 < c → c < δ → 0 < d → d < δ →
      ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ < ε := by
  set M := ‖A v₀‖
  refine ⟨ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1)), by positivity, fun c d hc hcδ hd hdδ => ?_⟩
  have h := hA.norm_expYosida_sub_expYosida_le hc hd ht (hA.norm_yosida_apply_le_norm_apply hc v₀)
    (hA.norm_yosida_apply_le_norm_apply hd v₀)
  rw [sub_self, norm_zero, zero_pow two_ne_zero, zero_add] at h
  refine lt_of_pow_lt_pow_left₀ 2 hε.le (h.trans_lt ?_)
  have hM : 0 ≤ M := norm_nonneg _
  have key : (c + d) * (t * M ^ 2) < 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) *
      (M ^ 2 + 1)) := by
    have h1 : t * M ^ 2 ≤ (t + 1) * (M ^ 2 + 1) := by nlinarith
    have h2 : 0 < (t + 1) * (M ^ 2 + 1) := by positivity
    calc (c + d) * (t * M ^ 2) ≤ (c + d) * ((t + 1) * (M ^ 2 + 1)) := by gcongr
      _ < 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) * (M ^ 2 + 1)) := by
          gcongr
          linarith
  have : 2 * (ε ^ 2 / (8 * (t + 1) * (M ^ 2 + 1))) * ((t + 1) * (M ^ 2 + 1)) = ε ^ 2 / 4 := by
    field_simp
    ring
  rw [this] at key
  nlinarith [key, sq_nonneg ε]

/-- **The family `u_c(t) u₀` is Cauchy as `c → 0⁺`, for every `u₀ ∈ H`**: by the Cauchy
estimate on the dense domain and `‖u_c(t)‖ ≤ 1` ([brezis2011functional], proof of Theorem 7.4,
Step 3, and Chapter 7, Remark 4 (b)). -/
theorem IsMaximalMonotone.cauchy_map_expYosida (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t)
    (u₀ : H) : Cauchy (map (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0)) := by
  rw [cauchy_map_iff', Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  obtain ⟨v₀, hv₀, hd⟩ := hA.dense_domain.exists_dist_lt u₀ (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  obtain ⟨δ, hδ0, hδ⟩ := hA.exists_forall_norm_expYosida_sub_lt ht ⟨v₀, hv₀⟩
    (by positivity : 0 < ε / 3)
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c ∧ c < δ := by
    filter_upwards [Ioo_mem_nhdsGT hδ0] with c hc
    exact hc
  rw [eventually_prod_iff]
  refine ⟨_, hev, _, hev, fun {c} hc {d} hd' => ?_⟩
  simp only [dist_eq_norm]
  calc ‖A.expYosida c t u₀ - A.expYosida d t u₀‖
      = ‖A.expYosida c t (u₀ - v₀) + (A.expYosida c t v₀ - A.expYosida d t v₀) +
          A.expYosida d t (v₀ - u₀)‖ := by
        rw [_root_.map_sub, _root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.expYosida c t (u₀ - v₀)‖ + ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ +
          ‖A.expYosida d t (v₀ - u₀)‖ := norm_add₃_le
    _ ≤ ‖u₀ - v₀‖ + ‖A.expYosida c t v₀ - A.expYosida d t v₀‖ + ‖v₀ - u₀‖ := by
        gcongr
        · exact hA.norm_expYosida_apply_le hc.1 ht _
        · exact hA.norm_expYosida_apply_le hd'.1 ht _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev v₀ u₀]
        gcongr
        exact hδ c d hc.1 hc.2 hd'.1 hd'.2
    _ = ε := by ring

variable (A) in
open scoped Classical in
/-- **The contraction semigroup `S_A(t)`** generated by `-A` ([brezis2011functional] Chapter 7,
Remark 5 and Remark 4 (b)): the limit `S_A(t) u₀ = lim_{c → 0⁺} exp(-t A_c) u₀`, as a total
function of `(A, t)` by the junk-value pattern of `resolvent` — some bounded `S` with
`exp(-t A_c) u₀ → S u₀` for every `u₀` when one exists (it is then unique), and `0` otherwise.
No completeness is assumed in the definition, so that `(A.powPart j).semigroup` on `D(A^j)` is
well-formed before completeness is supplied; the properties are stated under
`hA : A.IsMaximalMonotone` and `0 ≤ t`. -/
def semigroup (t : ℝ) : H →L[ℝ] H :=
  if h : ∃ S : H →L[ℝ] H, ∀ u₀, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (S u₀))
  then h.choose else 0

/-- The limit `lim_{c → 0⁺} exp(-t A_c) u₀` exists for every `u₀` and defines a bounded operator
of norm at most `1`. -/
theorem IsMaximalMonotone.exists_semigroup (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t) :
    ∃ S : H →L[ℝ] H, ∀ u₀, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (S u₀)) := by
  have hlim : ∀ u₀ : H, ∃ L : H, Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 L) :=
    fun u₀ => CompleteSpace.complete (hA.cauchy_map_expYosida ht u₀)
  choose L hL using hlim
  let Lₗ : H →ₗ[ℝ] H :=
    { toFun := L
      map_add' := fun x y => tendsto_nhds_unique (hL (x + y))
        (by simpa [_root_.map_add] using (hL x).add (hL y))
      map_smul' := fun a x => tendsto_nhds_unique (hL (a • x))
        (by simpa [_root_.map_smul] using (hL x).const_smul a) }
  refine ⟨Lₗ.mkContinuous 1 fun u₀ => ?_, hL⟩
  rw [one_mul]
  refine le_of_tendsto (hL u₀).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.norm_expYosida_apply_le hc ht u₀

/-- **The specification of the semigroup** ([brezis2011functional] Chapter 7, Remark 4 (b)):
for `t ≥ 0` and every `u₀ ∈ H`, `exp(-t A_c) u₀ → S_A(t) u₀` as `c → 0⁺`. -/
theorem IsMaximalMonotone.tendsto_expYosida_semigroup (hA : A.IsMaximalMonotone) {t : ℝ}
    (ht : 0 ≤ t) (u₀ : H) :
    Tendsto (fun c : ℝ => A.expYosida c t u₀) (𝓝[>] 0) (𝓝 (A.semigroup t u₀)) := by
  have h := hA.exists_semigroup ht
  unfold semigroup
  rw [dite_eq_left h]
  exact h.choose_spec u₀

/-- **Remark 5 (a), pointwise**: `‖S_A(t) u₀‖ ≤ ‖u₀‖` for `t ≥ 0`. -/
theorem IsMaximalMonotone.norm_semigroup_apply_le (hA : A.IsMaximalMonotone) {t : ℝ}
    (ht : 0 ≤ t) (u₀ : H) : ‖A.semigroup t u₀‖ ≤ ‖u₀‖ := by
  refine le_of_tendsto (hA.tendsto_expYosida_semigroup ht u₀).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.norm_expYosida_apply_le hc ht u₀

/-- **Remark 5 (a)**: `S_A(t)` is a contraction, `‖S_A(t)‖ ≤ 1` for `t ≥ 0`
([brezis2011functional] Chapter 7, Remark 5 (a)); this is the estimate `‖u(t)‖ ≤ ‖u₀‖` of
Theorem 7.4. -/
theorem IsMaximalMonotone.norm_semigroup_le_one (hA : A.IsMaximalMonotone) {t : ℝ} (ht : 0 ≤ t) :
    ‖A.semigroup t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u₀ => by
    rw [one_mul]
    exact hA.norm_semigroup_apply_le ht u₀

/-- **Remark 5 (b), second clause**: `S_A(0) = I` ([brezis2011functional] Chapter 7,
Remark 5 (b)). -/
theorem IsMaximalMonotone.semigroup_zero (hA : A.IsMaximalMonotone) : A.semigroup 0 = 1 := by
  ext u₀
  refine tendsto_nhds_unique (hA.tendsto_expYosida_semigroup le_rfl u₀) ?_
  simp only [expYosida_zero, one_apply_eq_self]
  exact tendsto_const_nhds

/-- `t ↦ ‖S_A(t) w‖` is antitone on `[0, ∞)`, as a pointwise limit of the antitone functions
`t ↦ ‖exp(-t A_c) w‖` ([brezis2011functional] Lemma 7.1, in the limit). -/
theorem IsMaximalMonotone.antitoneOn_norm_semigroup_apply (hA : A.IsMaximalMonotone) (w : H) :
    AntitoneOn (fun t => ‖A.semigroup t w‖) (Ici 0) := by
  intro a ha b hb hab
  refine le_of_tendsto_of_tendsto (hA.tendsto_expYosida_semigroup hb w).norm
    (hA.tendsto_expYosida_semigroup ha w).norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact hA.antitoneOn_norm_expYosida_apply hc w ha hb hab

/-- **Estimate (13') of Step 3**: for `u₀ ∈ D(A)`, `c > 0` and `t ≥ 0`,
`‖u_c(t) u₀ - S_A(t) u₀‖ ≤ 2 √(c t) ‖A u₀‖` — let `d → 0⁺` in the Cauchy estimate (13)
([brezis2011functional], proof of Theorem 7.4, Step 3). -/
theorem IsMaximalMonotone.norm_expYosida_sub_semigroup_le (hA : A.IsMaximalMonotone) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (u₀ : A.domain) :
    ‖A.expYosida c t u₀ - A.semigroup t u₀‖ ≤ 2 * Real.sqrt (c * t) * ‖A u₀‖ := by
  have hsq : ‖A.expYosida c t u₀ - A.semigroup t u₀‖ ^ 2 ≤ 4 * c * t * ‖A u₀‖ ^ 2 := by
    have h1 : Tendsto (fun d : ℝ => ‖A.expYosida c t u₀ - A.expYosida d t u₀‖ ^ 2) (𝓝[>] 0)
        (𝓝 (‖A.expYosida c t u₀ - A.semigroup t u₀‖ ^ 2)) :=
      ((tendsto_const_nhds.sub (hA.tendsto_expYosida_semigroup ht u₀)).norm).pow 2
    have h2 : Tendsto (fun d : ℝ => ‖(u₀ : H) - u₀‖ ^ 2 + 4 * (c + d) * t * ‖A u₀‖ ^ 2)
        (𝓝[>] 0) (𝓝 (‖(u₀ : H) - u₀‖ ^ 2 + 4 * (c + 0) * t * ‖A u₀‖ ^ 2)) :=
      ((Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds)
    have := le_of_tendsto_of_tendsto h1 h2 (by
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact hA.norm_expYosida_sub_expYosida_le hc hd ht
        (hA.norm_yosida_apply_le_norm_apply hc u₀) (hA.norm_yosida_apply_le_norm_apply hd u₀))
    simpa using this
  have h4 : (2 * Real.sqrt (c * t) * ‖A u₀‖) ^ 2 = 4 * c * t * ‖A u₀‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), h4]
  exact hsq

/-- **Step 3, uniform convergence on bounded intervals**: for every `w ∈ H` and `T ≥ 0`,
`exp(-t A_c) w → S_A(t) w` uniformly on `[0, T]` as `c → 0⁺`; on `D(A)` by (13'), in general
by density and the contraction property ([brezis2011functional], proof of Theorem 7.4,
Step 3). -/
theorem IsMaximalMonotone.tendstoUniformlyOn_expYosida_semigroup (hA : A.IsMaximalMonotone)
    (w : H) {T : ℝ} :
    TendstoUniformlyOn (fun (c : ℝ) t => A.expYosida c t w) (fun t => A.semigroup t w)
      (𝓝[>] 0) (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨w₁, hw₁, hd⟩ := hA.dense_domain.exists_dist_lt w (by positivity : 0 < ε / 3)
  rw [dist_eq_norm] at hd
  have hlim : Tendsto (fun c : ℝ => 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun c : ℝ => 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖) (𝓝 0)
        (𝓝 (2 * Real.sqrt (0 * T) * ‖A ⟨w₁, hw₁⟩‖)) := Continuous.tendsto (by fun_prop) 0
    simpa using this.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)),
    self_mem_nhdsWithin] with c hc hc0
  intro t ht
  have hc' : (0 : ℝ) < c := hc0
  rw [dist_eq_norm]
  calc ‖A.semigroup t w - A.expYosida c t w‖
      = ‖A.semigroup t (w - w₁) + (A.semigroup t w₁ - A.expYosida c t w₁) +
          A.expYosida c t (w₁ - w)‖ := by
        rw [_root_.map_sub, _root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.semigroup t (w - w₁)‖ + ‖A.semigroup t w₁ - A.expYosida c t w₁‖ +
          ‖A.expYosida c t (w₁ - w)‖ := norm_add₃_le
    _ ≤ ‖w - w₁‖ + 2 * Real.sqrt (c * T) * ‖A ⟨w₁, hw₁⟩‖ + ‖w₁ - w‖ := by
        gcongr
        · exact hA.norm_semigroup_apply_le ht.1 _
        · rw [norm_sub_rev]
          refine (hA.norm_expYosida_sub_semigroup_le hc' ht.1 ⟨w₁, hw₁⟩).trans ?_
          gcongr
          exact ht.2
        · exact hA.norm_expYosida_apply_le hc' ht.1 _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [norm_sub_rev w₁ w]
        gcongr
    _ = ε := by ring

/-- **The semigroup is strongly continuous on `[0, ∞)`**: `t ↦ S_A(t) w` is continuous on
`[0, ∞)`, as a locally uniform limit of the continuous `t ↦ exp(-t A_c) w`
([brezis2011functional], proof of Theorem 7.4, Step 3, "`u ∈ C([0, ∞); H)`"). -/
theorem IsMaximalMonotone.continuousOn_semigroup_apply (hA : A.IsMaximalMonotone) (w : H) :
    ContinuousOn (fun t => A.semigroup t w) (Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have h1 : ContinuousOn (fun t => A.semigroup t w) (Icc 0 (t + 1)) :=
    (hA.tendstoUniformlyOn_expYosida_semigroup w).continuousOn
      (Eventually.of_forall fun c => (continuous_expYosida_apply c w).continuousOn).frequently
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h1 t ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Remark 5 (c)**: `S_A(t) w → w` as `t → 0⁺` ([brezis2011functional] Chapter 7,
Remark 5 (c)). -/
theorem IsMaximalMonotone.tendsto_semigroup_apply_zero (hA : A.IsMaximalMonotone) (w : H) :
    Tendsto (fun t => A.semigroup t w) (𝓝[>] 0) (𝓝 w) := by
  have := (hA.continuousOn_semigroup_apply w 0 self_mem_Ici).tendsto
  rw [hA.semigroup_zero, one_apply_eq_self] at this
  exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- **Step 4, collapsed**: for `u₀ ∈ D(A)` and `T ≥ 0`, the derivatives
`u_c'(t) = -exp(-t A_c) A_c u₀` converge uniformly on `[0, T]` to `-S_A(t) (A u₀)`, because
`‖exp(-t A_c) A_c u₀ - S_A(t) A u₀‖ ≤ ‖A_c u₀ - A u₀‖ + ‖exp(-t A_c) (A u₀) - S_A(t) (A u₀)‖`
and Proposition 7.2 (d). The book proves this for `u₀ ∈ D(A²)` and needs its Step 6 to remove
the assumption ([brezis2011functional], proof of Theorem 7.4, Step 4). -/
theorem IsMaximalMonotone.tendstoUniformlyOn_deriv_expYosida (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {T : ℝ} :
    TendstoUniformlyOn (fun (c : ℝ) t => A.expYosida c t (A.yosida c u₀))
      (fun t => A.semigroup t (A u₀)) (𝓝[>] 0) (Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_yosida_apply u₀)
  have h2 := Metric.tendstoUniformlyOn_iff.1
    (hA.tendstoUniformlyOn_expYosida_semigroup (A u₀) (T := T)) (ε / 2) (by positivity)
  filter_upwards [h1.eventually (gt_mem_nhds (half_pos hε)), h2, self_mem_nhdsWithin] with c hc1
    hc2 hc0
  intro t ht
  have hc' : (0 : ℝ) < c := hc0
  rw [dist_eq_norm]
  calc ‖A.semigroup t (A u₀) - A.expYosida c t (A.yosida c u₀)‖
      = ‖(A.semigroup t (A u₀) - A.expYosida c t (A u₀)) +
          A.expYosida c t (A u₀ - A.yosida c u₀)‖ := by
        rw [_root_.map_sub]
        congr 1
        abel
    _ ≤ ‖A.semigroup t (A u₀) - A.expYosida c t (A u₀)‖ +
          ‖A.expYosida c t (A u₀ - A.yosida c u₀)‖ := norm_add_le _ _
    _ ≤ dist (A.semigroup t (A u₀)) (A.expYosida c t (A u₀)) + ‖A u₀ - A.yosida c u₀‖ := by
        rw [dist_eq_norm]
        gcongr
        exact hA.norm_expYosida_apply_le hc' ht.1 _
    _ < ε / 2 + ε / 2 := by
        rw [norm_sub_rev]
        exact add_lt_add (hc2 t ht) hc1
    _ = ε := by ring

end LinearPMap

/-! ### The derivative of a uniform limit on a closed interval -/

section UniformLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The derivative of a uniform limit, on a closed interval.** If `F i → f` pointwise on
`[a, b]`, the `F i` have derivatives `F' i` within `[a, b]` that are continuous on `[a, b]` and
converge uniformly to `g`, then `f` has derivative `g t` within `[a, b]` at every `t ∈ [a, b]`,
the endpoints included. This is a closed-interval version of Mathlib's
`hasDerivAt_of_tendstoUniformlyOn` (which needs an open set), proved through the fundamental
theorem of calculus: `F i t = F i a + ∫_a^t F' i`, the integrals converge, so
`f t = f a + ∫_a^t g`, which is differentiated within `[a, b]`. -/
theorem hasDerivWithinAt_Icc_of_tendstoUniformlyOn {ι : Type*} {l : Filter ι} [NeBot l]
    {a b : ℝ} (hab : a ≤ b) {F F' : ι → ℝ → E} {f g : ℝ → E}
    (hF : ∀ᶠ i in l, ∀ t ∈ Icc a b, HasDerivWithinAt (F i) (F' i t) (Icc a b) t)
    (hF' : ∀ᶠ i in l, ContinuousOn (F' i) (Icc a b))
    (hg : TendstoUniformlyOn F' g l (Icc a b))
    (hf : ∀ t ∈ Icc a b, Tendsto (fun i => F i t) l (𝓝 (f t))) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  have hgc : ContinuousOn g (Icc a b) := hg.continuousOn hF'.frequently
  -- the integral representation of each `F i`
  have hint : ∀ᶠ i in l, ∀ t ∈ Icc a b, F i t = F i a + ∫ s in a..t, F' i s := by
    filter_upwards [hF, hF'] with i hFi hF'i
    intro t ht
    have hderiv : ∀ x ∈ Ioo a t, HasDerivWithinAt (F i) (F' i x) (Ioi x) x := fun x hx =>
      ((hFi x ⟨hx.1.le, hx.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (hx.2.trans_le ht.2))).hasDerivWithinAt
    have hcont : ContinuousOn (F i) (Icc a t) :=
      (HasDerivWithinAt.continuousOn hFi).mono (Icc_subset_Icc_right ht.2)
    have hii : IntervalIntegrable (F' i) MeasureTheory.volume a t :=
      (hF'i.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hii]
    abel
  -- the integrals converge
  have hlim : ∀ t ∈ Icc a b,
      Tendsto (fun i => ∫ s in a..t, F' i s) l (𝓝 (∫ s in a..t, g s)) := by
    intro t ht
    have hgi : IntervalIntegrable g MeasureTheory.volume a t :=
      (hgc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (b - a + 1) := by
      have : 0 ≤ b - a := by linarith
      positivity
    filter_upwards [hF', Metric.tendstoUniformlyOn_iff.1 hg _ hε'] with i hF'i hi
    have hii : IntervalIntegrable (F' i) MeasureTheory.volume a t :=
      (hF'i.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [dist_eq_norm, ← intervalIntegral.integral_sub hii hgi]
    have hb : ∀ s ∈ uIoc a t, ‖F' i s - g s‖ ≤ ε / (b - a + 1) := by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      have := hi s ⟨hs.1.le, hs.2.trans ht.2⟩
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this.le
    calc ‖∫ s in a..t, (F' i s - g s)‖ ≤ ε / (b - a + 1) * |t - a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ ≤ ε / (b - a + 1) * (b - a) := by
          gcongr
          rw [abs_of_nonneg (by linarith [ht.1])]
          linarith [ht.2]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
  -- the limit `f` has the integral representation
  have hrep : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, g s := fun t ht =>
    tendsto_nhds_unique (hf t ht) (by
      refine ((hf a (left_mem_Icc.2 hab)).add (hlim t ht)).congr' ?_
      filter_upwards [hint] with i hi
      exact (hi t ht).symm)
  -- differentiate the representation
  intro t ht
  have : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hgi : IntervalIntegrable g MeasureTheory.volume a t :=
    (hgc.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hd : HasDerivWithinAt (fun u => ∫ s in a..u, g s) (g t) (Icc a b) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hgi
      (hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hgc t ht)
  exact (hd.const_add (f a)).congr hrep (hrep t ht)

end UniformLimit

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : H →ₗ.[ℝ] H}

/-! ### Step 5: the limit solves the equation -/

/-- **Step 5 (iii)**: for `u₀ ∈ D(A)`, `t ↦ S_A(t) u₀` has derivative `-S_A(t) (A u₀)` within
`[0, ∞)` at every `t ≥ 0` — the uniform-limit lemma applied to `u_c(·) u₀` on `[0, t + 1]`, the
derivatives `-exp(-· A_c) A_c u₀` converging uniformly by Step 4
([brezis2011functional], proof of Theorem 7.4, Step 5). -/
theorem IsMaximalMonotone.hasDerivWithinAt_semigroup_apply (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => A.semigroup t u₀) (-(A.semigroup t (A u₀))) (Ici 0) t := by
  have hT : (0 : ℝ) ≤ t + 1 := by linarith
  have key := hasDerivWithinAt_Icc_of_tendstoUniformlyOn (l := 𝓝[>] (0 : ℝ)) hT
    (F := fun c t => A.expYosida c t u₀)
    (F' := fun c t => -(A.expYosida c t (A.yosida c u₀)))
    (f := fun t => A.semigroup t u₀) (g := fun t => -(A.semigroup t (A u₀)))
    (Eventually.of_forall fun c τ _ => by
      have := (hasDerivAt_expYosida_apply (A := A) c u₀ τ).hasDerivWithinAt (s := Icc 0 (t + 1))
      rwa [yosida_expYosida_comm] at this)
    (Eventually.of_forall fun c => (continuous_expYosida_apply c _).neg.continuousOn)
    (uniformContinuous_neg.comp_tendstoUniformlyOn
      (hA.tendstoUniformlyOn_deriv_expYosida u₀))
    (fun s hs => hA.tendsto_expYosida_semigroup hs.1 u₀)
  refine (key t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- **Step 5 (i)–(ii)**: for `u₀ ∈ D(A)` and `t ≥ 0`, `S_A(t) u₀ ∈ D(A)` and
`A (S_A(t) u₀) = S_A(t) (A u₀)`: the pairs `(J_c u_c(t) u₀, A_c u_c(t) u₀)` lie on the graph of `A`
and converge to `(S_A(t) u₀, S_A(t) (A u₀))`, and the graph is closed
([brezis2011functional], proof of Theorem 7.4, Step 5). -/
theorem IsMaximalMonotone.exists_semigroup_apply_mem_domain (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : A.semigroup t u₀ ∈ A.domain, A ⟨A.semigroup t u₀, h⟩ = A.semigroup t (A u₀) := by
  have hcl : _root_.IsClosed (A.graph : Set (H × H)) := hA.isClosed
  have h1 : Tendsto (fun c : ℝ => A.resolvent c (A.expYosida c t u₀)) (𝓝[>] 0)
      (𝓝 (A.semigroup t u₀)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h2 : Tendsto (fun c : ℝ => ‖A.expYosida c t u₀ - A.semigroup t u₀‖ +
        ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖) (𝓝[>] 0) (𝓝 (0 + 0)) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_expYosida_semigroup ht u₀)).add
        (tendsto_iff_norm_sub_tendsto_zero.1 (hA.tendsto_resolvent_apply _))
    rw [add_zero] at h2
    refine squeeze_zero' (Eventually.of_forall fun c => norm_nonneg _) ?_ h2
    filter_upwards [self_mem_nhdsWithin] with c hc
    calc ‖A.resolvent c (A.expYosida c t u₀) - A.semigroup t u₀‖
        = ‖A.resolvent c (A.expYosida c t u₀ - A.semigroup t u₀) +
            (A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀)‖ := by
          rw [_root_.map_sub]
          congr 1
          abel
      _ ≤ ‖A.resolvent c (A.expYosida c t u₀ - A.semigroup t u₀)‖ +
            ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖ := norm_add_le _ _
      _ ≤ ‖A.expYosida c t u₀ - A.semigroup t u₀‖ +
            ‖A.resolvent c (A.semigroup t u₀) - A.semigroup t u₀‖ := by
          gcongr
          exact hA.norm_resolvent_apply_le hc _
  have h2 : Tendsto (fun c : ℝ => A.expYosida c t (A.yosida c u₀)) (𝓝[>] 0)
      (𝓝 (A.semigroup t (A u₀))) :=
    (hA.tendstoUniformlyOn_deriv_expYosida u₀).tendsto_at ⟨ht, le_rfl⟩
  have hmem : (A.semigroup t u₀, A.semigroup t (A u₀)) ∈ A.graph := by
    refine hcl.mem_of_tendsto (h1.prodMk_nhds h2) ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    rw [← yosida_expYosida_comm, hA.yosida_apply_eq_apply_resolvent hc]
    exact A.mem_graph ⟨_, hA.resolvent_apply_mem_domain hc _⟩
  rw [mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  change (y : H) = A.semigroup t u₀ at hy1
  change A y = A.semigroup t (A u₀) at hy2
  refine ⟨hy1 ▸ y.2, ?_⟩
  rw [show (⟨A.semigroup t u₀, hy1 ▸ y.2⟩ : A.domain) = y from Subtype.ext hy1.symm]
  exact hy2

/-- **Step 5 (i)**: `S_A(t) u₀ ∈ D(A)` for `u₀ ∈ D(A)` and `t ≥ 0`. -/
theorem IsMaximalMonotone.semigroup_apply_mem_domain (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) : A.semigroup t u₀ ∈ A.domain :=
  (hA.exists_semigroup_apply_mem_domain u₀ ht).fst

/-- **Step 5 (ii)**: `S_A(t)` commutes with `A` on `D(A)`, `A (S_A(t) u₀) = S_A(t) (A u₀)`. -/
theorem IsMaximalMonotone.semigroup_apply_apply (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) :
    A ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain u₀ ht⟩ = A.semigroup t (A u₀) :=
  (hA.exists_semigroup_apply_mem_domain u₀ ht).snd

/-! ### Theorem 7.4 (Hille–Yosida) -/

/-- **Theorem 7.4, existence**: for `u₀ ∈ D(A)`, `t ↦ S_A(t) u₀` solves `u' + A u = 0` on
`[0, ∞)` with `u(0) = u₀` ([brezis2011functional] Theorem 7.4). -/
theorem IsMaximalMonotone.isSolutionOn_semigroup (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    A.IsSolutionOn u₀ (Ici 0) fun t => A.semigroup t u₀ where
  apply_zero := by simp [hA.semigroup_zero]
  mem_domain t ht := hA.semigroup_apply_mem_domain u₀ ht
  hasDerivWithinAt t ht := by
    have := hA.hasDerivWithinAt_semigroup_apply u₀ ht
    rwa [← hA.semigroup_apply_apply u₀ ht] at this

/-- Every solution of the evolution problem on `[0, ∞)` is the semigroup applied to the datum:
how every statement about "the solution `u` of (6)" is transported to `S_A`. -/
theorem IsSolutionOn.eq_semigroup (hA : A.IsMaximalMonotone) {u₀ : A.domain} {u : ℝ → H}
    (hu : A.IsSolutionOn u₀ (Ici 0) u) : EqOn u (fun t => A.semigroup t u₀) (Ici 0) :=
  hA.isMonotone.eqOn_of_isSolutionOn hu (hA.isSolutionOn_semigroup u₀)

/-- **Theorem 7.4, the class `C¹([0, ∞); H)`**: for `u₀ ∈ D(A)`, `t ↦ S_A(t) u₀` is `C¹` on
`[0, ∞)`, its derivative `-S_A(t) (A u₀)` being continuous ([brezis2011functional]
Theorem 7.4). -/
theorem IsMaximalMonotone.contDiffOn_semigroup_apply (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    ContDiffOn ℝ 1 (fun t => A.semigroup t u₀) (Ici 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht => (hA.hasDerivWithinAt_semigroup_apply u₀ ht).differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  refine (hA.continuousOn_semigroup_apply (A u₀)).neg.congr fun t ht => ?_
  exact (hA.hasDerivWithinAt_semigroup_apply u₀ ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **Theorem 7.4, the estimate on the derivative**: `‖u'(t)‖ = ‖A u(t)‖ = ‖S_A(t) (A u₀)‖ ≤ ‖A u₀‖`
for `t ≥ 0` ([brezis2011functional] Theorem 7.4). -/
theorem IsMaximalMonotone.norm_apply_semigroup_apply_le (hA : A.IsMaximalMonotone)
    (u₀ : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖A ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain u₀ ht⟩‖ ≤ ‖A u₀‖ := by
  rw [hA.semigroup_apply_apply u₀ ht]
  exact hA.norm_semigroup_apply_le ht _

/-- **The Lipschitz estimate in time**: `‖S_A(t) u₀ - u₀‖ ≤ t ‖A u₀‖` for `u₀ ∈ D(A)`, `t ≥ 0`. -/
theorem IsMaximalMonotone.norm_semigroup_apply_sub_le (hA : A.IsMaximalMonotone) (u₀ : A.domain)
    {t : ℝ} (ht : 0 ≤ t) : ‖A.semigroup t u₀ - u₀‖ ≤ t * ‖A u₀‖ := by
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => A.semigroup t u₀)
    (f' := fun t => -(A.semigroup t (A u₀))) (a := 0) (b := t) (C := ‖A u₀‖)
    ((hA.continuousOn_semigroup_apply u₀).mono Icc_subset_Ici_self)
    (fun x hx => (hA.hasDerivWithinAt_semigroup_apply u₀ hx.1).mono (Ici_subset_Ici.2 hx.1))
    (fun x hx => by
      rw [norm_neg]
      exact hA.norm_semigroup_apply_le hx.1 _) t (right_mem_Icc.2 ht)
  simpa [hA.semigroup_zero, mul_comm] using this

/-- **Theorem 7.4 (Hille–Yosida)**, packaged: for a maximal monotone `A` and `u₀ ∈ D(A)`, the
evolution problem `u' + A u = 0`, `u(0) = u₀` has a solution `u ∈ C¹([0, ∞); H)` with
`‖u(t)‖ ≤ ‖u₀‖` and `‖u'(t)‖ = ‖A u(t)‖ ≤ ‖A u₀‖` for `t ≥ 0`; it is `t ↦ S_A(t) u₀`, and
uniqueness is `IsMonotone.eqOn_of_isSolutionOn` ([brezis2011functional] Theorem 7.4). -/
theorem IsMaximalMonotone.exists_isSolutionOn (hA : A.IsMaximalMonotone) (u₀ : A.domain) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ici 0) u, ContDiffOn ℝ 1 u (Ici 0) ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖(u₀ : H)‖) ∧
      ∀ t (ht : 0 ≤ t), ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖A u₀‖ :=
  ⟨fun t => A.semigroup t u₀, hA.isSolutionOn_semigroup u₀, hA.contDiffOn_semigroup_apply u₀,
    fun _ ht => hA.norm_semigroup_apply_le ht u₀,
    fun _ ht => hA.norm_apply_semigroup_apply_le u₀ ht⟩

/-- **Remark 5 (b), the semigroup law**: `S_A(s + t) = S_A(s) ∘ S_A(t)` for `s, t ≥ 0`. Both sides
applied to `u₀ ∈ D(A)` solve the problem with the datum `S_A(t) u₀ ∈ D(A)`, so they agree on the
dense `D(A)`, hence everywhere ([brezis2011functional] Chapter 7, Remark 5 (b)). -/
theorem IsMaximalMonotone.semigroup_add (hA : A.IsMaximalMonotone) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) : A.semigroup (s + t) = (A.semigroup s).comp (A.semigroup t) := by
  have h : ⇑(A.semigroup (s + t)) = ⇑((A.semigroup s).comp (A.semigroup t)) := by
    refine Continuous.ext_on hA.dense_domain (A.semigroup (s + t)).continuous
      ((A.semigroup s).comp (A.semigroup t)).continuous fun u₀ hu₀ => ?_
    have h1 : A.IsSolutionOn (A.semigroup t u₀) (Ici 0) fun τ => A.semigroup (τ + t) u₀ :=
      (hA.isSolutionOn_semigroup ⟨u₀, hu₀⟩).comp_add ht
    have h2 : A.IsSolutionOn (A.semigroup t u₀) (Ici 0)
        fun τ => A.semigroup τ (A.semigroup t u₀) :=
      hA.isSolutionOn_semigroup ⟨A.semigroup t u₀, hA.semigroup_apply_mem_domain ⟨u₀, hu₀⟩ ht⟩
    exact hA.isMonotone.eqOn_of_isSolutionOn h1 h2 hs
  exact ContinuousLinearMap.ext fun x => congrFun h x

/-! ### The classes `C^n(s; D(A^j))` -/

open PowDomain

variable (A) in
/-- **The class `C^n(s; D(A^j))`** ([brezis2011functional] Theorems 7.5 and 7.7): `u` lifts on
`s` to a `C^n` map into the Hilbert space `D(A^j)`, i.e. there is `v : ℝ → A.PowDomain j`, `C^n`
on `s`, whose `0`-th coordinate is `u` on `s`. The lift is unique on `s` (its coordinates are
`A^i u`); `contDiffOnPowDomain_iff` reads the condition coordinatewise. Consumers compose the
lift with bounded operators out of `A.PowDomain j`. -/
def ContDiffOnPowDomain (n : WithTop ℕ∞) (j : ℕ) (u : ℝ → H) (s : Set ℝ) : Prop :=
  ∃ v : ℝ → A.PowDomain j, (∀ t ∈ s, applyL A j 0 (v t) = u t) ∧ ContDiffOn ℝ n v s

omit [CompleteSpace H] in
/-- The class is monotone in the set of times. -/
theorem ContDiffOnPowDomain.mono {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s t : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (hts : t ⊆ s) : A.ContDiffOnPowDomain n j u t :=
  let ⟨v, hv0, hv⟩ := h
  ⟨v, fun x hx => hv0 x (hts hx), hv.mono hts⟩

omit [CompleteSpace H] in
/-- The class is antitone in the order of differentiability. -/
theorem ContDiffOnPowDomain.of_le {n m : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (hmn : m ≤ n) : A.ContDiffOnPowDomain m j u s :=
  let ⟨v, hv0, hv⟩ := h
  ⟨v, hv0, hv.of_le hmn⟩

omit [CompleteSpace H] in
/-- The class only depends on the values of `u` on `s`. -/
theorem ContDiffOnPowDomain.congr {n : WithTop ℕ∞} {j : ℕ} {u v : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n j u s) (huv : Set.EqOn u v s) :
    A.ContDiffOnPowDomain n j v s :=
  let ⟨w, hw0, hw⟩ := h
  ⟨w, fun t ht => (hw0 t ht).trans (huv ht), hw⟩

omit [CompleteSpace H] in
/-- `C^n(s; D(A^{j+1})) ⊆ C^n(s; D(A^j))`, through the inclusion `castL`. -/
theorem ContDiffOnPowDomain.castSucc {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H} {s : Set ℝ}
    (h : A.ContDiffOnPowDomain n (j + 1) u s) : A.ContDiffOnPowDomain n j u s :=
  let ⟨v, hv0, hv⟩ := h
  ⟨fun t => castL A j (v t), fun t ht => by rw [applyL_castL]; exact hv0 t ht,
    (castL A j).contDiff.comp_contDiffOn hv⟩

/-- **The coordinatewise reading of `C^n(s; D(A^j))`**, for a closed `A`: `u ∈ C^n(s; D(A^j))`
iff there are functions `w_0 = u, w_1, …, w_j`, each `C^n` on `s`, with `w_{i+1} = A w_i` on `s`
("`t ↦ A^i u(t)` is `C^n` for every `i ≤ j`"). The lift is recovered from the coordinates by the
orthogonal projection onto the closed submodule `powGraph A j`, which is a left inverse of the
inclusion and makes the lift `C^n`. -/
theorem contDiffOnPowDomain_iff (hA : A.IsClosed) {n : WithTop ℕ∞} {j : ℕ} {u : ℝ → H}
    {s : Set ℝ} :
    A.ContDiffOnPowDomain n j u s ↔ ∃ w : Fin (j + 1) → ℝ → H, (∀ t ∈ s, w 0 t = u t) ∧
      (∀ i, ContDiffOn ℝ n (w i) s) ∧ ∀ t ∈ s, ∀ i : Fin j,
        ∃ h : w i.castSucc t ∈ A.domain, A ⟨w i.castSucc t, h⟩ = w i.succ t := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    exact ⟨fun i t => applyL A j i (v t), hv0, fun i => (applyL A j i).contDiff.comp_contDiffOn hv,
      fun t _ i => ⟨applyL_mem_domain (v t) i, apply_applyL (v t) i⟩⟩
  · rintro ⟨w, hw0, hw, hwA⟩
    have := hA.completeSpace_powDomain j
    let P := (A.powGraph j).orthogonalProjectionOnto
    let W : ℝ → PiLp 2 (fun _ : Fin (j + 1) => H) := fun t => toLp 2 fun i => w i t
    have hW : ContDiffOn ℝ n W s := (contDiffOn_piLp 2).2 fun i => hw i
    refine ⟨fun t => P (W t), fun t ht => ?_, P.contDiff.comp_contDiffOn hW⟩
    have hmem : W t ∈ A.powGraph j := fun i => hwA t ht i
    change ((P (W t) : A.PowDomain j) : PiLp 2 fun _ : Fin (j + 1) => H) 0 = u t
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_eq_self_iff.2 hmem]
    exact hw0 t ht

/-! ### The regularity ladder: the semigroup of the part of `A` -/

/-- **The semigroup of the part is the restriction of the semigroup**: for `x ∈ D(A^j)`, `t ≥ 0`
and `i ≤ j`, `A^i (S_{A_j}(t) x) = S_A(t) (A^i x)`, where `S_{A_j}` is the semigroup of the part
`A_j = A.powPart j` on the Hilbert space `D(A^j)`. Both sides are continuous in `x` and agree on
the dense subspace `D(A^{j+1})`, where `t ↦ A^i (S_{A_j}(t) x)` solves the problem in `H` with the
datum `A^i x ∈ D(A)` ([brezis2011functional], proof of Theorem 7.5). -/
theorem IsMaximalMonotone.applyL_semigroup_powPart (hA : A.IsMaximalMonotone) (j : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (x : A.PowDomain j) (i : Fin (j + 1)) :
    applyL A j i ((A.powPart j).semigroup t x) = A.semigroup t (applyL A j i x) := by
  have := hA.isClosed.completeSpace_powDomain j
  have hAj := hA.powPart j
  have hcont : ⇑((applyL A j i).comp ((A.powPart j).semigroup t)) =
      ⇑((A.semigroup t).comp (applyL A j i)) := by
    refine Continuous.ext_on (hA.dense_range_castL j) (by fun_prop) (by fun_prop) ?_
    rintro _ ⟨y, rfl⟩
    set x := castL A j y with hx
    have hxd : x ∈ (A.powPart j).domain := castL_mem_powPart_domain y
    have hsol1 : A.IsSolutionOn (applyL A j i x) (Ici 0)
        fun τ => applyL A j i ((A.powPart j).semigroup τ x) := by
      have hs := hAj.isSolutionOn_semigroup ⟨x, hxd⟩
      refine ⟨by rw [hs.apply_zero],
        fun τ hτ => applyL_mem_domain_of_mem_powPartDomain (hs.mem_domain τ hτ) i,
        fun τ hτ => ?_⟩
      have h1 := (applyL A j i).hasFDerivAt.comp_hasDerivWithinAt τ (hs.hasDerivWithinAt τ hτ)
      simpa [Function.comp_def, _root_.map_neg] using h1
    have hsol2 : A.IsSolutionOn (applyL A j i x) (Ici 0)
        fun τ => A.semigroup τ (applyL A j i x) :=
      hA.isSolutionOn_semigroup ⟨applyL A j i x, applyL_mem_domain_of_mem_powPartDomain hxd i⟩
    exact hA.isMonotone.eqOn_of_isSolutionOn hsol1 hsol2 ht
  exact congrFun hcont x

omit [CompleteSpace H] in
/-- The datum of the regularity ladder: `castLE x ∈ D(A^j)` lies in `D(A.powPart j)` when
`x ∈ D(A^m)` with `j < m`. -/
theorem castLE_mem_powPart_domain {j m : ℕ} (h : j < m) (x : A.PowDomain m) :
    castLE A h.le x ∈ (A.powPart j).domain := by
  rw [mem_powPart_domain_iff, applyL_castLE]
  exact applyL_mem_domain x ⟨j, h⟩

omit [CompleteSpace H] in
/-- The part of `A` on the datum `castLE x`, read one level up: `A (castLE x) = shiftL (castLE x)`
in `D(A^j)`, for `x ∈ D(A^m)` with `j + 1 ≤ m`. -/
theorem powPart_castLE {j m : ℕ} (h : j + 1 ≤ m) (x : A.PowDomain m) :
    A.powPart j ⟨castLE A (by omega) x, castLE_mem_powPart_domain (by omega) x⟩ =
      shiftL A j (castLE A h x) :=
  PowDomain.ext fun i => apply_applyL x ⟨i, by omega⟩

/-- **The regularity ladder behind Theorem 7.5**: for all `n j m` with `j + n ≤ m` and every
`x ∈ D(A^m)`, the solution `t ↦ S_{A_j}(t) (castLE x)` in `D(A^j)` is `C^n` on `[0, ∞)`. Induction
on `n`, for all `j` at once: the derivative `-S_{A_j}(t) (A_j (castLE x))` is `-shiftL` of the
solution one level up, `C^n` by the induction hypothesis at `j + 1`
([brezis2011functional], proof of Theorem 7.5, "`d/dt (A u) = A (du/dt)`"). -/
theorem IsMaximalMonotone.contDiffOn_semigroup_powPart (hA : A.IsMaximalMonotone) (n : ℕ) :
    ∀ (j m : ℕ) (h : j + n ≤ m) (x : A.PowDomain m),
      ContDiffOn ℝ n (fun t => (A.powPart j).semigroup t (castLE A (by omega) x)) (Ici 0) := by
  induction n with
  | zero =>
    intro j m _ x
    have := hA.isClosed.completeSpace_powDomain j
    rw [Nat.cast_zero, contDiffOn_zero]
    exact (hA.powPart j).continuousOn_semigroup_apply _
  | succ n ih =>
    intro j m h x
    have := hA.isClosed.completeSpace_powDomain j
    have hAj := hA.powPart j
    have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
        (fun t => (A.powPart j).semigroup t (castLE A (by omega) x))
        (-(shiftL A j ((A.powPart (j + 1)).semigroup t (castLE A (by omega) x)))) (Ici 0) t := by
      intro t ht
      have h1 := hAj.hasDerivWithinAt_semigroup_apply
        ⟨castLE A (by omega) x, castLE_mem_powPart_domain (by omega) x⟩ ht
      convert h1 using 2
      rw [powPart_castLE (by omega) x]
      refine PowDomain.ext fun i => ?_
      rw [applyL_shiftL, hA.applyL_semigroup_powPart (j + 1) ht,
        hA.applyL_semigroup_powPart j ht, applyL_shiftL]
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨fun t ht => (hderiv t ht).differentiableWithinAt, fun h => by simp at h, ?_⟩
    have hih := ih (j + 1) m (by omega) x
    refine (((shiftL A j).contDiff.comp_contDiffOn hih).neg).congr fun t ht => ?_
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- **Theorem 7.5 (regularity)**: for a maximal monotone `A`, `u₀ ∈ D(A^k)` and `j ≤ k`, the
solution `u(t) = S_A(t) u₀` of the evolution problem lies in `C^{k-j}([0, ∞); D(A^j))`. The lift
is `t ↦ S_{A_j}(t) (castLE x)`, `C^{k-j}` by the ladder, and its `0`-th coordinate is `S_A(t) u₀`
([brezis2011functional] Theorem 7.5; the book states it for `k ≥ 2`, the cases `k = 0, 1` being
Theorem 7.4). -/
theorem IsMaximalMonotone.contDiffOnPowDomain_semigroup (hA : A.IsMaximalMonotone) {k : ℕ}
    (x : A.PowDomain k) {j : ℕ} (hj : j ≤ k) :
    A.ContDiffOnPowDomain (k - j : ℕ) j (fun t => A.semigroup t (applyL A k 0 x)) (Ici 0) := by
  refine ⟨fun t => (A.powPart j).semigroup t (castLE A hj x), fun t ht => ?_,
    hA.contDiffOn_semigroup_powPart (k - j) j k (by omega) x⟩
  rw [hA.applyL_semigroup_powPart j ht, applyL_castLE]
  rfl

end LinearPMap

/-! ### The self-adjoint case: the smoothing estimate for a bounded operator -/

section SelfAdjointExp

open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The smoothing estimate for a bounded self-adjoint monotone operator**: for `T > 0`,
`‖B exp(-T B) w‖ ≤ ‖w‖ / T`. With `u(t) = exp(-t B) w`, the function
`Φ(t) = ½ ‖u‖² + t ⟪B u, u⟫ + t² ‖B u‖²` has derivative `Φ' = -2 t² ⟪B (B u), B u⟫ ≤ 0`, so
`T² ‖B u(T)‖² ≤ Φ(T) ≤ Φ(0) = ½ ‖w‖²`. This is the chain (29)–(33) of the proof of
[brezis2011functional] Theorem 7.7, its integrations by parts replaced by one derivative; it
gives the sharper `‖w‖ / (√2 T)`. -/
theorem norm_exp_neg_smul_apply_le_div (B : H →L[ℝ] H) (hB : IsSelfAdjoint B)
    (hB' : ∀ v, 0 ≤ ⟪B v, v⟫_ℝ) (w : H) {T : ℝ} (hT : 0 < T) :
    ‖B (exp ((-T) • B) w)‖ ≤ ‖w‖ / T := by
  have hsym : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ := fun x y => hB.isSymmetric x y
  set u : ℝ → H := fun t => exp ((-t) • B) w with hu
  have hu' : ∀ t, HasDerivAt u (-(B (u t))) t := fun t => hasDerivAt_exp_neg_smul_apply B w t
  have hBu' : ∀ t, HasDerivAt (fun t => B (u t)) (B (-(B (u t)))) t := fun t =>
    B.hasFDerivAt.comp_hasDerivAt t (hu' t)
  set Φ : ℝ → ℝ := fun t => (1 / 2) * ‖u t‖ ^ 2 + t * ⟪B (u t), u t⟫_ℝ + t ^ 2 * ‖B (u t)‖ ^ 2
    with hΦ
  have hΦ' : ∀ t, HasDerivAt Φ (-2 * t ^ 2 * ⟪B (B (u t)), B (u t)⟫_ℝ) t := fun t => by
    have e1 := (hu' t).norm_sq.const_mul (1 / 2 : ℝ)
    have e2 := (hasDerivAt_id t).mul (HasDerivAt.inner ℝ (hBu' t) (hu' t))
    have e3 := (hasDerivAt_pow 2 t).mul (hBu' t).norm_sq
    convert (e1.add e2).add e3 using 1
    · funext x
      simp only [hΦ, Pi.add_apply, Pi.mul_apply, id]
    · simp only [inner_neg_right, inner_neg_left, map_neg, real_inner_self_eq_norm_sq, id,
        Nat.cast_ofNat]
      rw [hsym (B (u t)) (u t), real_inner_self_eq_norm_sq,
        real_inner_comm (B (B (u t))) (B (u t)), real_inner_comm (u t) (B (u t))]
      ring
  have hΦa : AntitoneOn Φ (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hΦ' t).continuousAt.continuousWithinAt)
      (fun t _ => (hΦ' t).differentiableAt.differentiableWithinAt) fun t _ => ?_
    rw [(hΦ' t).deriv]
    have := hB' (B (u t))
    nlinarith [sq_nonneg t]
  have h1 : Φ T ≤ Φ 0 := hΦa self_mem_Ici hT.le hT.le
  have h0 : Φ 0 = (1 / 2) * ‖w‖ ^ 2 := by simp [hΦ, hu]
  have h2 : T ^ 2 * ‖B (u T)‖ ^ 2 ≤ Φ T := by
    simp only [hΦ]
    have := hB' (u T)
    nlinarith [sq_nonneg ‖u T‖, hT.le]
  have h3 : (T * ‖B (u T)‖) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [mul_pow]
    nlinarith [h1, h2, h0, sq_nonneg ‖w‖]
  have h4 : T * ‖B (u T)‖ ≤ ‖w‖ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h3
  rw [le_div_iff₀ hT]
  linarith

end SelfAdjointExp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {A : H →ₗ.[ℝ] H}

open PowDomain

/-! ### The self-adjoint case: Theorem 7.7 -/

/-- **Step 1 of the proof of Theorem 7.7, for the approximations**: for a symmetric maximal
monotone `A`, `c > 0`, `T > 0` and every `u₀ ∈ H`, `‖u_c'(T)‖ = ‖A_c u_c(T) u₀‖ ≤ ‖u₀‖ / T` — the
book's (33)/(34), from the smoothing estimate for the self-adjoint monotone `A_c`
([brezis2011functional], proof of Theorem 7.7, Step 1). -/
theorem norm_yosida_expYosida_apply_le_div (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 < T) (u₀ : H) :
    ‖A.yosida c (A.expYosida c T u₀)‖ ≤ ‖u₀‖ / T :=
  norm_exp_neg_smul_apply_le_div _ (hA.isSelfAdjoint_yosida hs hc) (hA.inner_yosida_nonneg hc)
    u₀ hT

/-- **Estimate (27) of Theorem 7.7 on the domain**: for a symmetric maximal monotone `A`,
`u₀ ∈ D(A)` and `T > 0`, `‖A (S_A(T) u₀)‖ = ‖S_A(T) (A u₀)‖ ≤ ‖u₀‖ / T`, the limit of the estimate
for the approximations along `c → 0⁺` ([brezis2011functional], proof of Theorem 7.7, Step 1). -/
theorem norm_semigroup_apply_apply_le_div (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : A.domain) {T : ℝ} (hT : 0 < T) :
    ‖A.semigroup T (A u₀)‖ ≤ ‖(u₀ : H)‖ / T := by
  have h := (hA.tendstoUniformlyOn_deriv_expYosida u₀ (T := T)).tendsto_at
    (right_mem_Icc.2 hT.le)
  refine le_of_tendsto h.norm ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [← yosida_expYosida_comm]
  exact norm_yosida_expYosida_apply_le_div hA hs hc hT u₀

/-- **Step 2 of the proof of Theorem 7.7, the smoothing**: for a symmetric maximal monotone `A`,
**every** `u₀ ∈ H` and `t > 0`, `S_A(t) u₀ ∈ D(A)` and `‖A (S_A(t) u₀)‖ ≤ ‖u₀‖ / t`. Approximate
`u₀` by `v_n ∈ D(A)`; then `A (S_A(t) v_n) = S_A(t) (A v_n)` is Cauchy by (27), and the closed
graph identifies the limit ([brezis2011functional], proof of Theorem 7.7, Step 2, with `D(A)`
in place of `D(A²)`). -/
theorem semigroup_apply_mem_domain_of_isFormalAdjoint
    (hA : A.IsMaximalMonotone) (hs : A.IsFormalAdjoint A) (u₀ : H) {t : ℝ} (ht : 0 < t) :
    ∃ h : A.semigroup t u₀ ∈ A.domain, ‖A ⟨A.semigroup t u₀, h⟩‖ ≤ ‖u₀‖ / t := by
  have hcl : _root_.IsClosed (A.graph : Set (H × H)) := hA.isClosed
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.1 (hA.dense_domain u₀)
  -- the images `S(t) (A v_n)` form a Cauchy sequence
  have hcauchy : CauchySeq fun n => A.semigroup t (A ⟨v n, hv n⟩) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hvlim.cauchySeq (ε * t) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have := norm_semigroup_apply_apply_le_div hA hs (⟨v m, hv m⟩ - ⟨v n, hv n⟩) ht
    rw [map_sub, _root_.map_sub, Submodule.coe_sub, ← dist_eq_norm, ← dist_eq_norm,
      le_div_iff₀ ht] at this
    exact lt_of_mul_lt_mul_right (this.trans_lt (hN m hm n hn)) ht.le
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto (fun n => A.semigroup t (v n)) atTop (𝓝 (A.semigroup t u₀)) :=
    ((A.semigroup t).continuous.tendsto u₀).comp hvlim
  have hmem : (A.semigroup t u₀, f) ∈ A.graph := by
    refine hcl.mem_of_tendsto (hlim.prodMk_nhds hf) (Eventually.of_forall fun n => ?_)
    rw [← hA.semigroup_apply_apply ⟨v n, hv n⟩ ht.le]
    exact A.mem_graph ⟨A.semigroup t (v n), hA.semigroup_apply_mem_domain ⟨v n, hv n⟩ ht.le⟩
  rw [mem_graph_iff] at hmem
  obtain ⟨y, hy1, hy2⟩ := hmem
  change (y : H) = A.semigroup t u₀ at hy1
  change A y = f at hy2
  refine ⟨hy1 ▸ y.2, ?_⟩
  rw [show (⟨A.semigroup t u₀, hy1 ▸ y.2⟩ : A.domain) = y from Subtype.ext hy1.symm, hy2]
  refine le_of_tendsto_of_tendsto hf.norm (hvlim.norm.div_const t)
    (Eventually.of_forall fun n => ?_)
  exact norm_semigroup_apply_apply_le_div hA hs ⟨v n, hv n⟩ ht

/-- **Theorem 7.7, the equation for `t > 0` and every datum**: for a symmetric maximal monotone
`A`, `u₀ ∈ H` and `t > 0`, `t ↦ S_A(t) u₀` has derivative `-A (S_A(t) u₀)` at `t`. On `[δ, ∞)`
with `0 < δ < t`, `S_A(τ) u₀ = S_A(τ - δ) (S_A(δ) u₀)` with `S_A(δ) u₀ ∈ D(A)`, and the semigroup
route gives the derivative of the latter ([brezis2011functional], proof of Theorem 7.7,
Step 2). -/
theorem hasDerivAt_semigroup_apply_of_isFormalAdjoint (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => A.semigroup t u₀)
      (-A ⟨A.semigroup t u₀, (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).fst⟩)
      t := by
  set δ := t / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδt : δ < t := by linarith
  set w : A.domain := ⟨A.semigroup δ u₀,
    (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hδ0).fst⟩ with hw
  have hEq : ∀ τ ∈ Ici δ, A.semigroup τ u₀ = A.semigroup (τ - δ) w := fun τ hτ => by
    have hτ' : 0 ≤ τ - δ := by simp only [mem_Ici] at hτ; linarith
    have := congrArg (fun T : H →L[ℝ] H => T u₀) (hA.semigroup_add hτ' hδ0.le)
    simpa using this
  have h1 : HasDerivWithinAt (fun τ => A.semigroup (τ - δ) w) (-(A.semigroup (t - δ) (A w)))
      (Ici δ) t := by
    have := (hA.hasDerivWithinAt_semigroup_apply w (by linarith : 0 ≤ t - δ)).scomp t
      ((hasDerivWithinAt_id t (Ici δ)).sub_const δ)
      (fun τ hτ => by simp only [mem_Ici, id] at hτ ⊢; linarith)
    simpa [Function.comp_def] using this
  have h2 : HasDerivWithinAt (fun τ => A.semigroup τ u₀) (-(A.semigroup (t - δ) (A w))) (Ici δ) t :=
    h1.congr hEq (hEq t hδt.le)
  have h3 := h2.hasDerivAt (Ici_mem_nhds hδt)
  convert h3 using 2
  rw [← hA.semigroup_apply_apply w (by linarith : 0 ≤ t - δ)]
  congr 1
  exact Subtype.ext (hEq t hδt.le)

/-- **Theorem 7.7, existence and the classes**: for a symmetric maximal monotone `A` and every
`u₀ ∈ H`, `u(t) = S_A(t) u₀` solves the evolution problem on `(0, ∞)`, is continuous on `[0, ∞)`
and `C¹` on `(0, ∞)`, and satisfies `‖u(t)‖ ≤ ‖u₀‖` for `t ≥ 0`
([brezis2011functional] Theorem 7.7). -/
theorem isSolutionOn_semigroup_Ioi (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) :
    A.IsSolutionOn u₀ (Ioi 0) (fun t => A.semigroup t u₀) ∧
      ContinuousOn (fun t => A.semigroup t u₀) (Ici 0) ∧
      ContDiffOn ℝ 1 (fun t => A.semigroup t u₀) (Ioi 0) ∧
      ∀ t, 0 ≤ t → ‖A.semigroup t u₀‖ ≤ ‖u₀‖ := by
  refine ⟨⟨by simp [hA.semigroup_zero],
    fun t ht => (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).fst,
    fun t ht => (hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀ ht).hasDerivWithinAt⟩,
    hA.continuousOn_semigroup_apply u₀, ?_, fun t ht => hA.norm_semigroup_apply_le ht u₀⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht => (hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀
    ht).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
  rw [contDiffOn_zero]
  -- the derivative is continuous on `(0, ∞)`: on each `(δ, ∞)` it is `τ ↦ -S(τ - δ) (A (S(δ) u₀))`
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  set δ := t / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδt : δ < t := by linarith
  set w : A.domain := ⟨A.semigroup δ u₀,
    (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ hδ0).fst⟩ with hw
  have hEq : ∀ τ ∈ Ioi δ, deriv (fun t => A.semigroup t u₀) τ =
      -(A.semigroup (τ - δ) (A w)) := fun τ hτ => by
    have hτ' : (0 : ℝ) < τ := by simp only [mem_Ioi] at hτ; linarith
    have hτ'' : (0 : ℝ) ≤ τ - δ := by simp only [mem_Ioi] at hτ; linarith
    rw [(hasDerivAt_semigroup_apply_of_isFormalAdjoint hA hs u₀ hτ').deriv,
      ← hA.semigroup_apply_apply w hτ'']
    have := congrArg (fun T : H →L[ℝ] H => T u₀) (hA.semigroup_add hτ'' hδ0.le)
    simp only [ContinuousLinearMap.comp_apply, sub_add_cancel] at this
    congr 1
    exact congrArg (fun z : A.domain => A z) (Subtype.ext this)
  have hcont : ContinuousOn (fun τ => -(A.semigroup (τ - δ) (A w))) (Ioi δ) := by
    refine ((hA.continuousOn_semigroup_apply (A w)).comp (continuousOn_id.sub continuousOn_const)
      fun τ hτ => ?_).neg
    simp only [mem_Ioi] at hτ
    simp only [mem_Ici, Pi.sub_apply, id]
    linarith
  exact ((hcont.congr hEq) t hδt).mono_of_mem_nhdsWithin (nhdsWithin_le_nhds (Ioi_mem_nhds hδt))

/-- **The smoothing at every order**: for a symmetric maximal monotone `A`, `u₀ ∈ H`, `l : ℕ` and
`ε > 0`, `S_A(ε) u₀ ∈ D(A^l)`. Induction on `l`, applying the smoothing of Step 2 to the part
`A.powPart l` on the Hilbert space `D(A^l)` and the datum `S_A(ε/2) u₀`
([brezis2011functional], proof of Theorem 7.7, (26)). -/
theorem exists_powDomain_semigroup_apply_of_isFormalAdjoint
    (hA : A.IsMaximalMonotone) (hs : A.IsFormalAdjoint A) (u₀ : H) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : A.PowDomain l, applyL A l 0 x = A.semigroup ε u₀ := by
  induction l generalizing u₀ ε with
  | zero => exact ⟨PowDomain.mk A (fun _ => A.semigroup ε u₀) (fun i => i.elim0), rfl⟩
  | succ l ih =>
    have := hA.isClosed.completeSpace_powDomain l
    obtain ⟨y, hy⟩ := ih u₀ (half_pos hε)
    have hAl := hA.powPart l
    have hsl := hs.powPart l
    obtain ⟨hmem, -⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint hAl hsl y (half_pos hε)
    refine ⟨snoc ((A.powPart l).semigroup (ε / 2) y) (mem_powPart_domain_iff.1 hmem), ?_⟩
    rw [show (0 : Fin (l + 2)) = (0 : Fin (l + 1)).castSucc from rfl, applyL_snoc_castSucc,
      hA.applyL_semigroup_powPart l (half_pos hε).le, hy, ← ContinuousLinearMap.comp_apply,
      ← hA.semigroup_add (half_pos hε).le (half_pos hε).le, add_halves]

/-- **Theorem 7.7, (26)**: for a symmetric maximal monotone `A` and every `u₀ ∈ H`,
`u(t) = S_A(t) u₀` lies in `C^k((0, ∞); D(A^l))` for all `k, l`. The lift is the unique element of
`D(A^l)` over `S_A(t) u₀`; near `t > 0` it is the lift of Theorem 7.5 for the datum
`S_A(t/2) u₀ ∈ D(A^{l+k})`, shifted in time ([brezis2011functional] Theorem 7.7, (26)). -/
theorem contDiffOnPowDomain_semigroup_Ioi (hA : A.IsMaximalMonotone)
    (hs : A.IsFormalAdjoint A) (u₀ : H) (k l : ℕ) :
    A.ContDiffOnPowDomain k l (fun t => A.semigroup t u₀) (Ioi 0) := by
  have hex : ∀ t : ℝ, 0 < t → ∃ x : A.PowDomain l, applyL A l 0 x = A.semigroup t u₀ :=
    fun t ht => exists_powDomain_semigroup_apply_of_isFormalAdjoint hA hs u₀ l ht
  choose! v hv using hex
  refine ⟨v, fun t ht => hv t ht, fun t ht => ?_⟩
  have ht' : (0 : ℝ) < t := ht
  set ε := t / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεt : ε < t := by linarith
  obtain ⟨x, hx⟩ := exists_powDomain_semigroup_apply_of_isFormalAdjoint hA hs u₀ (l + k) hε0
  have h75 := hA.contDiffOnPowDomain_semigroup x (j := l) (by omega)
  rw [Nat.add_sub_cancel_left] at h75
  obtain ⟨v', hv'0, hv'⟩ := h75
  have hw : ContDiffOn ℝ k (fun τ => v' (τ - ε)) (Ici ε) :=
    hv'.comp (contDiffOn_id.sub contDiffOn_const) fun τ hτ => by
      simp only [mem_Ici] at hτ ⊢
      linarith
  have hagree : EqOn v (fun τ => v' (τ - ε)) (Ici ε) := fun τ hτ => by
    have hτ' : 0 ≤ τ - ε := by simp only [mem_Ici] at hτ; linarith
    apply applyL_zero_injective
    rw [hv τ (by linarith), hv'0 (τ - ε) hτ']
    simp only [hx]
    rw [← ContinuousLinearMap.comp_apply, ← hA.semigroup_add hτ' hε0.le, sub_add_cancel]
  have : ContDiffAt ℝ k v t :=
    (hw.contDiffAt (Ici_mem_nhds hεt)).congr_of_eventuallyEq
      (eventuallyEq_of_mem (Ici_mem_nhds hεt) hagree)
  exact this.contDiffWithinAt

/-- **Theorem 7.7**, packaged with the book's hypothesis: for a self-adjoint maximal monotone `A`
and **every** `u₀ ∈ H`, the evolution problem `u' + A u = 0` on `(0, ∞)`, `u(0) = u₀`, has a
solution `u ∈ C([0, ∞); H) ∩ C¹((0, ∞); H)` with `‖u(t)‖ ≤ ‖u₀‖`, `‖u'(t)‖ = ‖A u(t)‖ ≤ ‖u₀‖ / t`
for `t > 0`, and `u ∈ C^k((0, ∞); D(A^l))` for all `k, l`; it is `t ↦ S_A(t) u₀`, and uniqueness
among solutions on `(0, ∞)` continuous on `[0, ∞)` is `IsMonotone.eqOn_of_isSolutionOn_Ioi`
([brezis2011functional] Theorem 7.7). -/
theorem exists_isSolutionOn_Ioi_of_isSelfAdjoint (hA : A.IsMaximalMonotone)
    (hsa : IsSelfAdjoint A) (u₀ : H) :
    ∃ u : ℝ → H, ∃ hu : A.IsSolutionOn u₀ (Ioi 0) u, ContinuousOn u (Ici 0) ∧
      ContDiffOn ℝ 1 u (Ioi 0) ∧ (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖u₀‖) ∧
      (∀ t (ht : 0 < t), ‖A ⟨u t, hu.mem_domain t ht⟩‖ ≤ ‖u₀‖ / t) ∧
      ∀ k l : ℕ, A.ContDiffOnPowDomain k l u (Ioi 0) := by
  have hs := hsa.isFormalAdjoint_self
  obtain ⟨h1, h2, h3, h4⟩ := isSolutionOn_semigroup_Ioi hA hs u₀
  exact ⟨fun t => A.semigroup t u₀, h1, h2, h3, h4,
    fun t ht => (semigroup_apply_mem_domain_of_isFormalAdjoint hA hs u₀ ht).snd,
    fun k l => contDiffOnPowDomain_semigroup_Ioi hA hs u₀ k l⟩

end LinearPMap
