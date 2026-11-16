/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap
import Numlib.Nonlinear.FixedPoint
import Numlib.Variational.Forms

/-!
# The Lax–Milgram lemma and existence theory for variational problems

Let $V$ be a Hilbert space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $a$ be a bounded
sesquilinear form on $V$, conjugate-linear in the first argument. The form is **coercive** with
constant $c > 0$ if $\operatorname{Re} a(v, v) \ge c \|v\|^2$ for all $v$. The **Lax–Milgram lemma**
states that then for every $\ell \in V'$ there is exactly one $u \in V$ with
$$a(u, v) = \ell(v) \quad \text{for all } v \in V,$$
and that $\|u\| \le \|\ell\| / c$. This is Theorem 8.3.4 of [han2009theoretical], and Theorem 11.13
(operator form) and Corollary 11.16 (forms) of [kress1998numerical].

For a Hermitian coercive form, the solution is the unique minimizer of the energy $E(v) = \tfrac12
\operatorname{Re} a(v, v) - \operatorname{Re} \ell(v)$, on the whole space, on a subspace, and on a
closed convex set, where it is characterized by a variational inequality (Theorem 8.3.3 and (8.3.3)
of [han2009theoretical], Proposition 5.2 of [saad2003iterative] in operator form). The module also
proves the generalized Lax–Milgram lemma of Babuška and Nečas for a form on two spaces under the
inf–sup condition (Theorem 8.7.1 of [han2009theoretical]), and existence results from a priori
estimates $c \|v\| \le \|Lv\|$ for bounded and closed operators (§8.2 of [han2009theoretical]).

## Main results

* `SesqForm.laxMilgram`: a bounded coercive form on a Hilbert space gives a uniquely solvable
  variational problem.
* `SesqForm.norm_le_of_forall_apply_eq`, `SesqForm.norm_sub_le_of_forall_apply_eq`: the solution
  satisfies $\|u\| \le \|\ell\| / c$ and depends on $\ell$ with Lipschitz constant $1/c$.
* `SesqForm.exists_solutionEquiv`: the solution map $\ell \mapsto u$ is a continuous
  conjugate-linear equivalence $V' \to V$ of norm at most $1/c$.
* `SesqForm.contractingWith_damped_toOperator`: the damped iteration $u \mapsto u - \theta(Au - f)$
  is a contraction.
* `SesqForm.isMinOn_energy_iff`: for a Hermitian coercive form, $u$ solves the problem on a subspace
  if and only if $u$ minimizes the energy on that subspace.
* `SesqForm.isMinOn_energy_iff_forall_le`, `SesqForm.existsUnique_isMinOn_energy`: on a closed
  convex set, the energy has exactly one minimizer, characterized by a variational inequality.
* `SesqForm.convexOn_energy`, `SesqForm.strongConvexOn_energy`, `SesqForm.hasFDerivAt_energy`:
  convexity, strong convexity and the Fréchet derivative of the energy.
* `SesqForm₂.babuska_necas`: the generalized Lax–Milgram lemma under the inf–sup condition and
  nondegeneracy, with the estimate `SesqForm₂.norm_le_of_infSupWith`.
* `SesqForm₂.infSupWith_of_forall_exists`: the inf–sup condition is also necessary for unique
  solvability with a bounded solution map.
* `ContinuousLinearMap.isClosed_range_of_le_norm`,
  `ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot`,
  `LinearPMap.isClosed_range_of_isClosed_of_le_norm`: a bounded-below operator has closed range, and
  it is bijective if its range is also dense.

## Implementation notes

* A form on $V$ is a `SesqForm 𝕜 V`, that is, `V →L⋆[𝕜] V →L[𝕜] 𝕜`, and a form on two spaces is a
  `SesqForm₂ 𝕜 U V`. Both are bounded by their type.
* The Lax–Milgram lemma has two proofs in [han2009theoretical], Theorem 8.3.4. The second one,
  through the Riesz representation and `ContinuousLinearMap.exists_equiv_of_isCoerciveWith`, proves
  `SesqForm.laxMilgram`. The first one, the damped fixed-point iteration, is
  `SesqForm.contractingWith_damped_toOperator`. Mathlib's `IsCoercive.continuousLinearEquivOfBilin`
  is the real case.
-/

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

section BoundedBelow

/-!
### Bounded-below operators

The two main tools of §8.2 of [han2009theoretical]: an operator with $c \|v\| \le \|Lv\|$ has closed
range, and if its range is also dense, it is bijective. They are stated here for operators between
two different spaces, because `SesqForm₂.babuska_necas` uses them in that generality. The rest of
§8.2 is at the end of the module.
-/

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

omit [CompleteSpace U] [CompleteSpace W] in
/-- Let $L : U \to W$ be a bounded linear operator between inner product spaces, and let $c > 0$
with $c \|v\| \le \|Lv\|$ for all $v$. Then $L$ is antilipschitz with constant $c^{-1}$:
$\|u - v\| \le c^{-1} \|Lu - Lv\|$ for all $u, v$.

Injectivity, a closed range and a bounded inverse on the range all follow from this one
property. -/
theorem ContinuousLinearMap.antilipschitzWith_of_le_norm (L : U →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : AntilipschitzWith (Real.toNNReal c⁻¹) L := by
  refine L.antilipschitz_of_bound fun v => ?_
  rw [Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
  exact h v

omit [CompleteSpace W] in
/-- Let $U$ be a Hilbert space, $W$ an inner product space, and $L : U \to W$ a bounded linear
operator with $c \|v\| \le \|Lv\|$ for all $v$, for some $c > 0$. Then the range of $L$ is
closed. This is Theorem 8.2.1 of [han2009theoretical]. -/
theorem ContinuousLinearMap.isClosed_range_of_le_norm (L : U →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : IsClosed (LinearMap.range (L : U →ₗ[𝕜] W) : Set W) := by
  rw [LinearMap.coe_range]
  exact (L.antilipschitzWith_of_le_norm hc h).isClosed_range L.uniformContinuous

/-- Let $U$ and $W$ be Hilbert spaces and $L : U \to W$ a bounded linear operator with
$c \|v\| \le \|Lv\|$ for all $v$, for some $c > 0$. If the orthogonal complement of the range of
$L$ is $\{0\}$, then $L$ is bijective. This is Theorem 8.2.4 of [han2009theoretical].

The lower bound gives injectivity and a closed range, and a closed range with trivial orthogonal
complement is all of $W$. This is the closed-range route to the Lax–Milgram lemma and to
`SesqForm₂.babuska_necas`, where the two hypotheses are coercivity and nondegeneracy. -/
theorem ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (L : U →L[𝕜] W)
    {c : ℝ} (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖)
    (hdense : (LinearMap.range (L : U →ₗ[𝕜] W))ᗮ = ⊥) : Function.Bijective L := by
  refine ⟨(L.antilipschitzWith_of_le_norm hc h).injective, ?_⟩
  have hcs : CompleteSpace (LinearMap.range (L : U →ₗ[𝕜] W)) :=
    (L.isClosed_range_of_le_norm hc h).completeSpace_coe
  have hrange : LinearMap.range (L : U →ₗ[𝕜] W) = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range (L : U →ₗ[𝕜] W)), hdense,
      Submodule.bot_orthogonal_eq_top]
  intro w
  have hw : w ∈ LinearMap.range (L : U →ₗ[𝕜] W) := by rw [hrange]; trivial
  obtain ⟨y, hy⟩ := hw
  exact ⟨y, hy⟩

end BoundedBelow

namespace SesqForm

variable (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)

/-- The operator of a coercive form is a continuous linear equivalence $e$ with
$\|e^{-1}\| \le 1/c$. -/
private theorem exists_equiv_toOperator {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ e : V ≃L[𝕜] V, (∀ u, toOperator a u = e u) ∧ ‖(e.symm : V →L[𝕜] V)‖ ≤ 1 / c := by
  obtain ⟨e, he, he'⟩ := ContinuousLinearMap.exists_equiv_of_isCoerciveWith hc
    ((a.isCoerciveWith_iff_toOperator c).mp ha)
  exact ⟨e, fun u => by rw [← he]; rfl, he'⟩

/-- **The Lax–Milgram lemma.** Let $V$ be a Hilbert space over $\mathbb{K}$, and let $a$ be a
bounded sesquilinear form on $V$ that is coercive with constant $c > 0$:
$\operatorname{Re} a(v, v) \ge c \|v\|^2$ for all $v$. Then for every $\ell \in V'$ there is
exactly one $u \in V$ with
$$a(u, v) = \ell(v) \quad \text{for all } v \in V.$$
This is Theorem 8.3.4 of [han2009theoretical]. -/
theorem laxMilgram {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) : ∃! u, ∀ v, a u v = ℓ v := by
  obtain ⟨e, hEq, -⟩ := a.exists_equiv_toOperator hc ha
  refine ⟨e.symm (rieszRep ℓ), ?_, ?_⟩
  · change ∀ v, a (e.symm (rieszRep ℓ)) v = ℓ v
    rw [a.forall_apply_eq_iff_toOperator_eq, hEq, e.apply_symm_apply]
  · intro y hy
    rw [a.forall_apply_eq_iff_toOperator_eq, hEq] at hy
    rw [← hy, e.symm_apply_apply]

omit [CompleteSpace V] in
/-- **The stability estimate.** Let $V$ be an inner product space, let $a$ be a bounded sesquilinear
form on $V$ that is coercive with constant $c > 0$, and let $\ell \in V'$. If
$a(u, v) = \ell(v)$ for all $v$, then $\|u\| \le \|\ell\| / c$. -/
theorem norm_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) {u : V}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / c := by
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg u) with h | h
  · simp [← h]
  · refine le_of_mul_le_mul_right ?_ h
    calc ‖u‖ * c * ‖u‖ = c * ‖u‖ ^ 2 := by ring
      _ ≤ RCLike.re (a u u) := ha u
      _ = RCLike.re (ℓ u) := by rw [hu]
      _ ≤ ‖ℓ u‖ := RCLike.re_le_norm _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u

omit [CompleteSpace V] in
/-- **Lipschitz dependence on the data.** Let $V$ be an inner product space and let $a$ be a bounded
sesquilinear form on $V$ that is coercive with constant $c > 0$. If $a(u_1, v) = \ell_1(v)$ and
$a(u_2, v) = \ell_2(v)$ for all $v$, then
$$\|u_1 - u_2\| \le \frac{\|\ell_1 - \ell_2\|}{c}.$$
This is (5.1.11) of [han2009theoretical], which is stated there for strongly monotone maps. -/
theorem norm_sub_le_of_forall_apply_eq {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c)
    {ℓ₁ ℓ₂ : V →L[𝕜] 𝕜} {u₁ u₂ : V} (h₁ : ∀ v, a u₁ v = ℓ₁ v) (h₂ : ∀ v, a u₂ v = ℓ₂ v) :
    ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / c :=
  a.norm_le_of_forall_apply_eq (ℓ₁ - ℓ₂) hc ha fun v => by
    simp [map_sub, h₁, h₂]

/-- **The solution operator.** Let $V$ be a Hilbert space and let $a$ be a bounded sesquilinear form
on $V$ that is coercive with constant $c > 0$. Then there is a continuous conjugate-linear
equivalence $S : V' \to V$ with $a(S\ell, v) = \ell(v)$ for all $\ell \in V'$ and $v \in V$, and
$\|S\| \le 1/c$. This is the solution operator of problem (8.3.5) of [han2009theoretical].

The solution map is conjugate-linear and not linear: $a$ is conjugate-linear in its first
argument, so $a(\mu u, v) = \bar\mu \, a(u, v)$ and $S(\mu \ell) = \bar\mu \, S\ell$. Over
$\mathbb{R}$ the two notions agree. -/
theorem exists_solutionEquiv {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ S : (V →L[𝕜] 𝕜) ≃L⋆[𝕜] V, (∀ ℓ v, a (S ℓ) v = ℓ v) ∧
      ‖(S : (V →L[𝕜] 𝕜) →L⋆[𝕜] V)‖ ≤ 1 / c := by
  obtain ⟨e, hEq, he'⟩ := a.exists_equiv_toOperator hc ha
  refine ⟨(InnerProductSpace.toDual 𝕜 V).symm.toContinuousLinearEquiv.trans e.symm, ?_, ?_⟩
  · intro ℓ' v
    revert v
    rw [a.forall_apply_eq_iff_toOperator_eq]
    change toOperator a (e.symm (rieszRep ℓ')) = rieszRep ℓ'
    rw [hEq, e.apply_symm_apply]
  · refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one hc.le) fun ℓ' => ?_
    change ‖e.symm (rieszRep ℓ')‖ ≤ 1 / c * ‖ℓ'‖
    calc ‖e.symm (rieszRep ℓ')‖ ≤ ‖(e.symm : V →L[𝕜] V)‖ * ‖rieszRep ℓ'‖ :=
          (e.symm : V →L[𝕜] V).le_opNorm _
      _ = ‖(e.symm : V →L[𝕜] V)‖ * ‖ℓ'‖ := by rw [norm_rieszRep]
      _ ≤ 1 / c * ‖ℓ'‖ := by gcongr

/-- **The damped iteration is a contraction.** Let $V$ be a Hilbert space and let $a$ be a bounded
sesquilinear form on $V$ with $\|a\| > 0$ that is coercive with constant $c$. Let $A$ be the
operator of $a$, with $\langle Au, v \rangle = a(u, v)$, let $f$ be the Riesz representative of
$\ell \in V'$, and let $0 < \theta < 2c / \|a\|^2$. Then the map $u \mapsto u - \theta(Au - f)$
is a contraction with constant
$$\sqrt{1 - 2\theta c + \theta^2 \|a\|^2}.$$
The Banach fixed-point theorem then gives the solution of $a(u, v) = \ell(v)$. This is the first
of the two proofs of Theorem 8.3.4 of [han2009theoretical].

The operator is `SesqForm.toOperator a` and $f$ is `SesqForm.rieszRep ℓ`. The estimate is
`contractingWith_damped` together with `ContinuousLinearMap.norm_sub_smul_apply_sq_le`. -/
theorem contractingWith_damped_toOperator {c : ℝ} (ha : a.IsCoerciveWith c)
    (ha0 : 0 < ‖a‖) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 2 * c / ‖a‖ ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * ‖a‖ ^ 2)))
      (fun u => u - (θ : 𝕜) • (toOperator a u - rieszRep ℓ)) := by
  have hcoer := (a.isCoerciveWith_iff_toOperator c).mp ha
  have hmono : IsStronglyMonotoneWith 𝕜 (toOperator a) c := by
    intro x y
    rw [← map_sub]
    exact hcoer (x - y)
  have hlip : LipschitzWith (Real.toNNReal ‖a‖) (toOperator a) := by
    rw [← a.norm_toOperator, ← coe_nnnorm, Real.toNNReal_coe]
    exact (toOperator a).lipschitzWith
  exact contractingWith_damped (𝕜 := 𝕜) ha0 hmono hlip (rieszRep ℓ) hθ hθ'

omit [CompleteSpace V] in
/-- For a Hermitian form $a$ and $E(v) = \tfrac12 \operatorname{Re} a(v, v) - \operatorname{Re}
\ell(v)$,
$$E(u + w) - E(u) = \operatorname{Re} a(u, w) - \operatorname{Re} \ell(w) + \tfrac12
  \operatorname{Re} a(w, w).$$

The linear term is the Gâteaux derivative and coercivity controls the quadratic term, so this
identity gives both directions of the equivalence between the variational problem and the
minimization of $E$. -/
theorem energy_add_sub_energy (ha : a.IsHermitian) (u w : V) :
    a.energy ℓ (u + w) - a.energy ℓ u
      = RCLike.re (a u w) - RCLike.re (ℓ w) + (1 / 2 : ℝ) * RCLike.re (a w w) := by
  have hsym : RCLike.re (a w u) = RCLike.re (a u w) := by rw [ha w u, RCLike.conj_re]
  simp only [energy, map_add, add_apply]
  rw [hsym]
  ring

omit [CompleteSpace V] in
/-- For a Hermitian form $a$, the energy on the real line through $u$ in direction $v$ is a
quadratic polynomial in $t \in \mathbb{R}$:
$$E(u + tv) - E(u) = t\,(\operatorname{Re} a(u, v) - \operatorname{Re} \ell(v)) + \tfrac12 t^2
  \operatorname{Re} a(v, v).$$
-/
theorem energy_smul_sub_energy (ha : a.IsHermitian) (u v : V) (t : ℝ) :
    a.energy ℓ (u + (t : 𝕜) • v) - a.energy ℓ u
      = t * (RCLike.re (a u v) - RCLike.re (ℓ v))
        + (1 / 2 : ℝ) * t ^ 2 * RCLike.re (a v v) := by
  rw [a.energy_add_sub_energy ℓ ha u ((t : 𝕜) • v)]
  simp only [map_smulₛₗ, smul_apply, smul_eq_mul, RCLike.conj_ofReal,
    RingHom.id_apply, RCLike.re_ofReal_mul]
  ring

/-- If $q \ge 0$ and $t\delta + \tfrac12 t^2 q \ge 0$ for every real $t$, then $\delta = 0$. -/
private theorem eq_zero_of_forall_quadratic_nonneg {δ q : ℝ} (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 ≤ t * δ + (1 / 2 : ℝ) * t ^ 2 * q) : δ = 0 := by
  by_contra hδ
  have hq1 : (0 : ℝ) < q + 1 := by linarith
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, δ = s * (q + 1) := ⟨δ / (q + 1), (div_mul_cancel₀ _ hq1.ne').symm⟩
  have hs0 : s ≠ 0 := fun h0 => hδ (by rw [h0, zero_mul])
  have h1 : 0 < s ^ 2 := (sq_nonneg s).lt_of_ne' (pow_ne_zero 2 hs0)
  nlinarith [h (-s), mul_nonneg h1.le hq]

/-- For a bounded bilinear form $a$ on a real inner product space and $\ell \in V'$, the energy
$E(v) = \tfrac12 a(v, v) - \ell(v)$ is continuous. -/
theorem continuous_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) : Continuous (a.energy ℓ) := by
  have h1 : Continuous fun v : V => ((a v : V →L[ℝ] ℝ), v) := a.continuous.prodMk continuous_id
  have h2 : Continuous fun p : (V →L[ℝ] ℝ) × V => p.1 p.2 := isBoundedBilinearMap_apply.continuous
  have hq : Continuous fun v : V => a v v := h2.comp h1
  have hE : a.energy ℓ = fun v : V => (1 / 2 : ℝ) * a v v - ℓ v := by
    funext v
    simp [energy]
  rw [hE]
  exact (continuous_const.mul hq).sub ℓ.continuous

/-- For a symmetric bilinear form $a$ on a real inner product space and $\ell \in V'$, the energy
$E(v) = \tfrac12 a(v, v) - \ell(v)$ satisfies the parallelogram identity
$$E(x) + E(y) - 2E\bigl(\tfrac12 x + \tfrac12 y\bigr) = \tfrac14 a(x - y, x - y).$$

For a coercive form the right-hand side is at least $\tfrac{c}{4} \|x - y\|^2$, which makes
every minimizing sequence a Cauchy sequence. The midpoint is written as a convex combination, so
that the convexity of a constraint set applies to it directly. -/
theorem energy_parallelogram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) (x y : V) :
    a.energy ℓ x + a.energy ℓ y - 2 * a.energy ℓ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
      = (1 / 4 : ℝ) * a (x - y) (x - y) := by
  have hsym : a y x = a x y := by simpa using ha y x
  simp only [energy, RCLike.re_to_real, map_smulₛₗ, map_add, map_sub, add_apply, sub_apply,
    smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, star_trivial]
  rw [hsym]
  ring

/-- **The energy of a positive semidefinite form is convex.** Let $a$ be a bounded bilinear form on
a real inner product space $V$ with $a(v, v) \ge 0$ for all $v$, and let $\ell \in V'$. Then
$E(v) = \tfrac12 a(v, v) - \ell(v)$ is convex on $V$. This is Remark 6 of Chapter 5 of
[brezis2011functional].

No symmetry is needed. For $s + t = 1$, $a(su + tv, su + tv) = s\,a(u, u) + t\,a(v, v) -
st\,a(u - v, u - v)$, and the cross terms $a(u, v) + a(v, u)$ match without being exchanged. -/
theorem convexOn_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : SesqForm ℝ V) (ℓ : V →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ a v v) :
    ConvexOn ℝ Set.univ (a.energy ℓ) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have hsub : a (x - y) (x - y) = a x x - (a x y + a y x) + a y y := by
    simp only [map_sub, sub_apply]
    ring
  have h := hpos (x - y)
  rw [hsub] at h
  simp only [energy, RCLike.re_to_real, map_smulₛₗ, map_add, add_apply, smul_apply, smul_eq_mul,
    RingHom.id_apply, starRingEnd_apply, star_trivial]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_nonneg (mul_nonneg hs ht) h]

/-- **The energy of a coercive symmetric form is strongly convex.** Let $a$ be a bounded symmetric
bilinear form on a real inner product space $V$ with $a(v, v) \ge c \|v\|^2$ for all $v$, and
let $\ell \in V'$. Then $E(v) = \tfrac12 a(v, v) - \ell(v)$ is $c$-strongly convex on $V$: for
$s, t \ge 0$ with $s + t = 1$,
$$E(sx + ty) \le s\,E(x) + t\,E(y) - \tfrac{c}{2}\,st\,\|x - y\|^2.$$

The conclusion is Mathlib's `StrongConvexOn Set.univ c`. It follows from the identity $E(sx +
ty) = s\,E(x) + t\,E(y) - \tfrac12 st\,a(x - y, x - y)$. -/
theorem strongConvexOn_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : SesqForm ℝ V} (ha : a.IsHermitian) {c : ℝ}
    (hc : a.IsCoerciveWith c) (ℓ : V →L[ℝ] ℝ) : StrongConvexOn Set.univ c (a.energy ℓ) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst ↦ ?_⟩
  have hsym : a y x = a x y := by simpa using ha y x
  have hcoer := hc (x - y)
  have hsub : a (x - y) (x - y) = a x x - (a x y + a y x) + a y y := by
    simp only [map_sub, sub_apply]
    ring
  rw [RCLike.re_to_real, hsub, hsym] at hcoer
  simp only [SesqForm.energy, RCLike.re_to_real, map_smulₛₗ, map_add, add_apply, smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, star_trivial, hsym]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcoer (mul_nonneg hs ht)]

/-- **The Fréchet derivative of the energy.** Let $a$ be a bounded symmetric bilinear form on a real
inner product space $V$ and let $\ell \in V'$. Then $E(v) = \tfrac12 a(v, v) - \ell(v)$ is
Fréchet differentiable at every $u \in V$, with derivative
$$E'(u) = a(u, \cdot) - \ell.$$
So the variational equation $a(u, v) = \ell(v)$ for all $v$ is the Euler equation $E'(u) = 0$.
This is Remark 7 of Chapter 5 of [brezis2011functional].

The directional form of the derivative is the expansion `SesqForm.energy_add_sub_energy`. -/
theorem hasFDerivAt_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) (u : V) :
    HasFDerivAt (a.energy ℓ) (a u - ℓ) u := by
  have hE : a.energy ℓ = fun v => (1 / 2 : ℝ) * a v v - ℓ v := by
    funext v
    simp [energy]
  set A : V →L[ℝ] V →L[ℝ] ℝ := a with hA
  have h1 : HasFDerivAt (fun v : V => (A v, v)) (A.prod (ContinuousLinearMap.id ℝ V)) u :=
    A.hasFDerivAt.prodMk (hasFDerivAt_id u)
  have h2 : HasFDerivAt (fun v : V => A v v) (2 • A u) u := by
    have h3 := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).hasFDerivAt (A u, u)
    refine (h3.comp (f := fun v : V => (A v, v)) u h1).congr_fderiv ?_
    ext w
    have hsym : A w u = A u w := by simpa using ha w u
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_id', id_eq, IsBoundedBilinearMap.deriv_apply, smul_apply,
      nsmul_eq_mul, hsym]
    ring
  rw [hE]
  refine ((h2.const_mul (1 / 2 : ℝ)).sub ℓ.hasFDerivAt).congr_fderiv ?_
  ext w
  simp only [smul_apply, nsmul_eq_mul, smul_eq_mul, sub_apply]
  ring

section Energy

variable {a} (ha : a.IsHermitian)
include ha

omit [CompleteSpace V] in
/-- **The variational problem on a subspace as a minimization.** Let $V$ be an inner product space
over $\mathbb{K}$, let $a$ be a bounded Hermitian sesquilinear form on $V$ that is coercive with
constant $c > 0$, let $\ell \in V'$, and let $K$ be a subspace of $V$. Then $u \in K$ minimizes
$E(v) = \tfrac12 \operatorname{Re} a(v, v) - \operatorname{Re} \ell(v)$ over $K$ if and only if
$$a(u, v) = \ell(v) \quad \text{for all } v \in K.$$
This is Theorem 8.3.3 of [han2009theoretical], for a subspace.

The case `K = ⊤` gives the equivalence of the variational problem on all of $V$ with the
minimization of $E$ over $V$. -/
theorem isMinOn_energy_iff {c : ℝ} (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (K : Submodule 𝕜 V)
    {u : V} (hu : u ∈ K) : IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v := by
  constructor
  · intro hmin
    -- the real part of the residual vanishes on `K` ...
    have hre : ∀ w ∈ K, RCLike.re (a u w) - RCLike.re (ℓ w) = 0 := by
      intro w hw
      refine eq_zero_of_forall_quadratic_nonneg
        (le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer w)) fun t => ?_
      have hmem : u + (t : 𝕜) • w ∈ K := K.add_mem hu (K.smul_mem _ hw)
      have hle := isMinOn_iff.mp hmin _ hmem
      have heq := a.energy_smul_sub_energy ℓ ha u w t
      linarith
    -- ... and applying it to `conj (a u v - ℓ v) • v` kills the residual itself
    intro v hv
    have hexp : ∀ (w : V) (μ : 𝕜), RCLike.re (a u (μ • w)) - RCLike.re (ℓ (μ • w))
        = RCLike.re (μ * (a u w - ℓ w)) := by
      intro w μ
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        mul_sub, map_sub]
    have hz := hre ((starRingEnd 𝕜) (a u v - ℓ v) • v) (K.smul_mem _ hv)
    rw [hexp, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hz
    rw [← sub_eq_zero]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (a u v - ℓ v)])
  · intro h
    rw [isMinOn_iff]
    intro v hv
    have huv : u + (v - u) = v := by abel
    have heq := a.energy_add_sub_energy ℓ ha u (v - u)
    rw [huv, h _ (K.sub_mem hv hu)] at heq
    have hnn : 0 ≤ RCLike.re (a (v - u) (v - u)) :=
      le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    linarith

omit ha in
/-- **The minimizer on a convex set is characterized by a variational inequality.** Let $a$ be a
bounded symmetric bilinear form on a real inner product space $V$ that is coercive with constant
$c > 0$, let $\ell \in V'$, and let $K \subseteq V$ be convex. Then $u \in K$ minimizes
$E(v) = \tfrac12 a(v, v) - \ell(v)$ over $K$ if and only if
$$\ell(v - u) \le a(u, v - u) \quad \text{for all } v \in K.$$
This is (8.3.3) of [han2009theoretical].

On a subspace the inequality applies to both $v$ and $2u - v$, and so it becomes the equality of
`SesqForm.isMinOn_energy_iff`. -/
theorem isMinOn_energy_iff_forall_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) {u : V} (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u) := by
  constructor
  · intro hmin v hv
    by_contra hlt
    push Not at hlt
    set δ : ℝ := a u (v - u) - ℓ (v - u) with hδdef
    have hδ : δ < 0 := by simp only [hδdef]; linarith
    set q : ℝ := a (v - u) (v - u) with hqdef
    have hq : 0 ≤ q := le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    set t : ℝ := min 1 (-δ / (q + 1)) with htdef
    have hq1 : (0 : ℝ) < q + 1 := by linarith
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hq1)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htq : t * (q + 1) ≤ -δ := by
      have := min_le_right (1 : ℝ) (-δ / (q + 1))
      rw [← htdef] at this
      calc t * (q + 1) ≤ (-δ / (q + 1)) * (q + 1) := by nlinarith
        _ = -δ := div_mul_cancel₀ _ hq1.ne'
    have hmem : u + t • (v - u) ∈ K := by
      have := hK hu hv (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      module
    have hle := isMinOn_iff.mp hmin _ hmem
    have heq := a.energy_smul_sub_energy ℓ ha u (v - u) t
    simp only [RCLike.ofReal_real_eq_id, id_eq] at heq
    rw [show RCLike.re (a u (v - u)) - RCLike.re (ℓ (v - u)) = δ from rfl,
      show RCLike.re (a (v - u) (v - u)) = q from rfl] at heq
    nlinarith
  · intro h
    rw [isMinOn_iff]
    intro v hv
    have huv : u + (v - u) = v := by abel
    have heq := a.energy_add_sub_energy ℓ ha u (v - u)
    rw [huv] at heq
    have hq : 0 ≤ a (v - u) (v - u) := le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcoer (v - u))
    have hδ := h v hv
    simp only [RCLike.re_to_real] at heq
    linarith

omit ha in
/-- **Existence and uniqueness of the minimizer on a closed convex set.** Let $V$ be a real Hilbert
space, let $a$ be a bounded symmetric bilinear form on $V$ that is coercive with constant
$c > 0$, let $\ell \in V'$, and let $K \subseteq V$ be nonempty, closed and convex. Then
$E(v) = \tfrac12 a(v, v) - \ell(v)$ has exactly one minimizer over $K$. This is Theorem 8.3.3 of
[han2009theoretical].

The source proves this through its Theorem 3.3.12 on the minimization of a coercive, convex,
lower semicontinuous functional. The proof here is a direct minimizing-sequence argument, with
the Cauchy estimate from the parallelogram identity `SesqForm.energy_parallelogram`. Compare
Mathlib's `exists_norm_eq_iInf_of_complete_convex`. -/
theorem existsUnique_isMinOn_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) {K : Set V} (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u := by
  have hcoer' : ∀ v : V, c * ‖v‖ ^ 2 ≤ a v v := fun v => by simpa using hcoer v
  have henergy : ∀ v : V, a.energy ℓ v = (1 / 2 : ℝ) * a v v - ℓ v := by
    intro v
    simp [SesqForm.energy]
  -- the energy is bounded below on all of `V`
  have hbelow : ∀ v : V, -(‖ℓ‖ ^ 2 / (2 * c)) ≤ a.energy ℓ v := by
    intro v
    have h1 : c * ‖v‖ ^ 2 ≤ a v v := hcoer' v
    have h2 : ℓ v ≤ ‖ℓ‖ * ‖v‖ := le_trans (le_abs_self _) (by simpa using ℓ.le_opNorm v)
    have h3 : c * (c * ‖v‖ ^ 2) ≤ c * (a v v) := mul_le_mul_of_nonneg_left h1 hc.le
    have key : -(‖ℓ‖ ^ 2) ≤ ((1 / 2 : ℝ) * a v v - ℓ v) * (2 * c) := by
      nlinarith [sq_nonneg (c * ‖v‖ - ‖ℓ‖), norm_nonneg v, mul_le_mul_of_nonneg_left h2 hc.le]
    rw [henergy v]
    calc -(‖ℓ‖ ^ 2 / (2 * c)) = -(‖ℓ‖ ^ 2) / (2 * c) := by ring
      _ ≤ (1 / 2 : ℝ) * a v v - ℓ v := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * c)]
          exact key
  set m : ℝ := sInf (a.energy ℓ '' K) with hmdef
  have hSne : (a.energy ℓ '' K).Nonempty := hne.image _
  have hSbdd : BddBelow (a.energy ℓ '' K) :=
    ⟨-(‖ℓ‖ ^ 2 / (2 * c)), by rintro _ ⟨v, -, rfl⟩; exact hbelow v⟩
  have hmle : ∀ v ∈ K, m ≤ a.energy ℓ v := fun v hv => csInf_le hSbdd ⟨v, hv, rfl⟩
  -- a minimizing sequence
  have hex : ∀ n : ℕ, ∃ v, v ∈ K ∧ a.energy ℓ v < m + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, hyS, hy⟩ := Real.lt_sInf_add_pos hSne (by positivity : (0:ℝ) < 1 / ((n:ℝ) + 1))
    obtain ⟨v, hv, rfl⟩ := hyS
    exact ⟨v, hv, hy⟩
  choose u hu hlt using hex
  -- the parallelogram identity turns the minimizing property into a Cauchy estimate
  have hpara : ∀ x ∈ K, ∀ y ∈ K,
      c / 4 * ‖x - y‖ ^ 2 ≤ a.energy ℓ x + a.energy ℓ y - 2 * m := by
    intro x hx y hy
    have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
      hK hx hy (by norm_num) (by norm_num) (by norm_num)
    have hid := energy_parallelogram ha ℓ x y
    have h1 := hmle _ hmid
    have h2 : c * ‖x - y‖ ^ 2 ≤ a (x - y) (x - y) := hcoer' (x - y)
    linarith
  have hdist : ∀ n N : ℕ, N ≤ n → c / 4 * ‖u n - u N‖ ^ 2 < 2 / ((N : ℝ) + 1) := by
    intro n N hnN
    have h1 := hpara (u n) (hu n) (u N) (hu N)
    have h4 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hnN
      linarith
    have h5 : (2 : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
    linarith [hlt n, hlt N]
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / (c * ε ^ 2))
    refine ⟨N, fun n hn => ?_⟩
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hcε : (0 : ℝ) < c * ε ^ 2 := by positivity
    have h2 : 8 < ((N : ℝ) + 1) * (c * ε ^ 2) := by
      have h6 : 8 / (c * ε ^ 2) < (N : ℝ) + 1 := by linarith
      calc (8 : ℝ) = 8 / (c * ε ^ 2) * (c * ε ^ 2) := by field_simp
        _ < ((N : ℝ) + 1) * (c * ε ^ 2) := by
            exact mul_lt_mul_of_pos_right h6 hcε
    have h3 : 2 / ((N : ℝ) + 1) < c / 4 * ε ^ 2 := by
      rw [div_lt_iff₀ hNpos]
      nlinarith
    have h7 : c / 4 * ‖u n - u N‖ ^ 2 < c / 4 * ε ^ 2 :=
      lt_trans (hdist n N hn) h3
    have h8 : ‖u n - u N‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h7 (by positivity)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u n - u N)]
  obtain ⟨ustar, hustar⟩ := cauchySeq_tendsto_of_complete hcau
  have hmemK : ustar ∈ K := hKc.mem_of_tendsto hustar (Filter.Eventually.of_forall hu)
  have hElim : Filter.Tendsto (fun n => a.energy ℓ (u n)) Filter.atTop
      (nhds (a.energy ℓ ustar)) :=
    ((continuous_energy a ℓ).tendsto ustar).comp hustar
  have hmlim : Filter.Tendsto (fun n : ℕ => m + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds m) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.const_add m
  have hEm : a.energy ℓ ustar = m :=
    le_antisymm (le_of_tendsto_of_tendsto' hElim hmlim fun n => (hlt n).le) (hmle _ hmemK)
  refine ⟨ustar, ⟨hmemK, ?_⟩, ?_⟩
  · rw [isMinOn_iff]
    intro v hv
    rw [hEm]
    exact hmle v hv
  · rintro y ⟨hyK, hymin⟩
    have hEy : a.energy ℓ y = m :=
      le_antisymm (by rw [← hEm]; exact isMinOn_iff.mp hymin _ hmemK) (hmle _ hyK)
    have hp := hpara y hyK ustar hmemK
    rw [hEy, hEm] at hp
    have h1 : ‖y - ustar‖ ^ 2 ≤ 0 := by nlinarith
    have h2 : ‖y - ustar‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))

omit [CompleteSpace V] in
/-- **The energy identity at the solution.** Let $V$ be an inner product space over $\mathbb{K}$,
let $a$ be a bounded Hermitian sesquilinear form on $V$ with $\operatorname{Re} a(v, v) \ge 0$
for all $v$, and let $\ell \in V'$. If $a(u, v) = \ell(v)$ for all $v$, then for every $v \in V$
$$E(v) - E(u) = \tfrac12 \|v - u\|_a^2, \qquad \|w\|_a = \sqrt{\operatorname{Re} a(w, w)}.$$
Completing the square turns the minimization of $E$ into the minimization of the energy distance
to $u$. This identity is the computation in the proof of Theorem 8.3.3 of [han2009theoretical]
and in the proof of Proposition 5.2 of [saad2003iterative], in operator form.

The positivity hypothesis `hpos`, which is `a.IsCoerciveWith 0`, is necessary. The energy norm
`SesqForm.energyNorm` is a real square root, so without it the right-hand side is $0$ whenever
$\operatorname{Re} a(w, w) < 0$, while the left-hand side need not be: take
$a = -\langle \cdot, \cdot \rangle$, $\ell = 0$ and $u = 0$. -/
theorem energy_sub_energy_eq (hpos : a.IsCoerciveWith 0) {u : V} (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2 := by
  have huv : u + (v - u) = v := by abel
  have heq := a.energy_add_sub_energy ℓ ha u (v - u)
  rw [huv, hu (v - u)] at heq
  rw [heq, energyNorm, Real.sq_sqrt (by simpa using hpos (v - u))]
  ring

end Energy

end SesqForm

namespace SesqForm₂

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜)

/-- The operator $B : U \to V$ of a form on two spaces, with $\langle Bu, v \rangle = a(u, v)$. It
is the composite of $a$ with the inverse Riesz map, and it is linear because both factors are
conjugate-linear. -/
private noncomputable def toOperator₂ : U →L[𝕜] V :=
  (InnerProductSpace.toDual 𝕜 V).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp a

omit [CompleteSpace U] in
/-- The operator $B$ of a form $a$ on two spaces satisfies $\langle Bu, v \rangle = a(u, v)$. -/
private theorem inner_toOperator₂ (u : U) (v : V) : inner 𝕜 (toOperator₂ a u) v = a u v := by
  simp [toOperator₂]

omit [CompleteSpace U] in
/-- The operator $B$ of a form $a$ on two spaces satisfies $\|Bu\| = \|a(u, \cdot)\|$, because the
Riesz representation is an isometry. -/
private theorem norm_toOperator₂_apply (u : U) : ‖toOperator₂ a u‖ = ‖a u‖ :=
  (InnerProductSpace.toDual 𝕜 V).symm.norm_map (a u)

omit [CompleteSpace U] in
/-- The problem $a(u, v) = \ell(v)$ for all $v$ is the operator equation $Bu = f$, where $f$ is the
Riesz representative of $\ell$. -/
private theorem forall_apply_eq_iff_toOperator₂_eq (u : U) :
    (∀ v, a u v = ℓ v) ↔ toOperator₂ a u = SesqForm.rieszRep ℓ := by
  constructor
  · intro h
    exact ext_inner_right 𝕜 fun v => by
      rw [inner_toOperator₂, SesqForm.inner_rieszRep, h]
  · intro h v
    rw [← inner_toOperator₂, h, SesqForm.inner_rieszRep]

/-- **The generalized Lax–Milgram lemma** (Babuška–Nečas). Let $U$ and $V$ be Hilbert spaces over
$\mathbb{K}$ and let $a$ be a bounded sesquilinear form on $U \times V$. Assume the inf–sup
condition with a constant $\alpha > 0$,
$$\alpha \|u\| \le \sup_{v \neq 0} \frac{|a(u, v)|}{\|v\|} \quad \text{for all } u \in U,$$
and the nondegeneracy condition: for every $v \neq 0$ there is $u$ with $a(u, v) \neq 0$. Then
for every $\ell \in V'$ there is exactly one $u \in U$ with $a(u, v) = \ell(v)$ for all
$v \in V$. This is Theorem 8.7.1 of [han2009theoretical], which attributes the result to Nečas.

The inf–sup condition is `SesqForm₂.InfSupWith`, and the nondegeneracy condition is
`SesqForm₂.IsNondegenerate`. The inf–sup condition gives injectivity and a closed range of the
operator of $a$, and nondegeneracy gives a dense range. -/
theorem babuska_necas {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) (hnd : a.IsNondegenerate) :
    ∃! u, ∀ v, a u v = ℓ v := by
  have hbound : ∀ u : U, α * ‖u‖ ≤ ‖toOperator₂ a u‖ := fun u => by
    rw [norm_toOperator₂_apply]; exact hinf u
  have hperp : (LinearMap.range (toOperator₂ a : U →ₗ[𝕜] V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    obtain ⟨u, hu⟩ := hnd v hv0
    exact hu (by rw [← inner_toOperator₂ a u v]; exact hv _ ⟨u, rfl⟩)
  obtain ⟨hinj, hsurj⟩ :=
    ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (toOperator₂ a) hα hbound
      hperp
  obtain ⟨u, hu⟩ := hsurj (SesqForm.rieszRep ℓ)
  refine ⟨u, (forall_apply_eq_iff_toOperator₂_eq a ℓ u).mpr hu, fun y hy => ?_⟩
  exact hinj (((forall_apply_eq_iff_toOperator₂_eq a ℓ y).mp hy).trans hu.symm)

omit [CompleteSpace V] [CompleteSpace U] in
/-- **The stability estimate on two spaces.** Let $U$ and $V$ be inner product spaces and let $a$ be
a bounded sesquilinear form on $U \times V$ that satisfies the inf–sup condition with constant
$\alpha > 0$. If $a(u, v) = \ell(v)$ for all $v \in V$, then $\|u\| \le \|\ell\| / \alpha$. This
is (8.7.5) of [han2009theoretical]. -/
theorem norm_le_of_infSupWith {α : ℝ} (hα : 0 < α) (hinf : a.InfSupWith α) {u : U}
    (hu : ∀ v, a u v = ℓ v) : ‖u‖ ≤ ‖ℓ‖ / α := by
  rw [le_div_iff₀ hα, mul_comm]
  calc α * ‖u‖ ≤ ‖a u‖ := hinf u
    _ = ‖ℓ‖ := by rw [ContinuousLinearMap.ext hu]

omit [CompleteSpace V] [CompleteSpace U] in
/-- **The inf–sup condition is necessary.** Let $U$ and $V$ be inner product spaces, let $a$ be a
bounded sesquilinear form on $U \times V$, and let $C > 0$. Assume that $u = 0$ is the only $u$
with $a(u, v) = 0$ for all $v$, and that for every $\ell \in V'$ there is $u$ with
$a(u, v) = \ell(v)$ for all $v$ and $\|u\| \le C \|\ell\|$. Then $a$ satisfies the inf–sup
condition with constant $1/C$. This is the converse of Theorem 8.7.1 of [han2009theoretical],
which states only the forward direction.

The injectivity hypothesis `hinj` is necessary: "well posed" means unique solvability, and the
existence of a bounded solution alone is not enough. For $V = 0$ and $U \neq 0$, every $\ell$ is
$0$ and $u = 0$ is a solution with $\|u\| \le C \|\ell\|$, but $\|a(u, \cdot)\| = 0$ for all
$u$, so no inf–sup constant exists. -/
theorem infSupWith_of_forall_exists {C : ℝ} (hC : 0 < C) (hinj : ∀ u : U, (∀ v, a u v = 0) → u = 0)
    (h : ∀ ℓ : V →L[𝕜] 𝕜, ∃ u, (∀ v, a u v = ℓ v) ∧ ‖u‖ ≤ C * ‖ℓ‖) :
    a.InfSupWith (1 / C) := by
  intro u₀
  obtain ⟨u, hu, hnorm⟩ := h (a u₀)
  have : u = u₀ := by
    have := hinj (u - u₀) fun v => by
      rw [map_sub, sub_apply, hu, sub_self]
    rwa [sub_eq_zero] at this
  rw [this] at hnorm
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC, mul_comm]
  exact hnorm

end SesqForm₂

section APriori

/-!
### Existence from a priori estimates

This section follows §8.2 of [han2009theoretical]. A lower bound $c \|v\| \le \|Lv\|$, which in
applications comes from an a priori estimate for the problem, gives injectivity and a closed range,
and therefore solvability when the range is also dense. The bounded case is
`ContinuousLinearMap.isClosed_range_of_le_norm` and
`ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot` at the start of the module.
This section gives the closed-operator version and the quantitative estimate.
-/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

omit [CompleteSpace W] in
/-- **A closed bounded-below operator has closed range.** Let $V$ be a Hilbert space, $W$ an inner
product space, and $L$ a closed linear operator from $V$ to $W$ with domain $D(L) \subseteq V$.
If $c \|v\| \le \|Lv\|$ for all $v \in D(L)$, for some $c > 0$, then the range of $L$ is closed.
This is Theorem 8.2.4 of [han2009theoretical], closed-operator version.

The operator is a `LinearPMap`, and no density of the domain is assumed. Closedness of the graph
replaces continuity: it identifies the limit of a convergent sequence of images as an image. -/
theorem LinearPMap.isClosed_range_of_isClosed_of_le_norm (L : V →ₗ.[𝕜] W) (hL : L.IsClosed)
    {c : ℝ} (hc : 0 < c) (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) :
    _root_.IsClosed (LinearMap.range L.toFun : Set W) := by
  refine IsSeqClosed.isClosed fun u w hu hconv => ?_
  choose v hv using hu
  have hv' : ∀ n, L (v n) = u n := hv
  -- the preimages form a Cauchy sequence, by the lower bound
  have hcauchy : CauchySeq fun n => ((v n : V)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq (c * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd := h (v m - v n)
    rw [map_sub, hv', hv'] at hd
    rw [dist_eq_norm]
    have h₁ : dist (u m) (u n) < c * ε := hN m hm n hn
    rw [dist_eq_norm] at h₁
    have h₂ : c * ‖(v m : V) - (v n : V)‖ ≤ ‖u m - u n‖ := by
      simpa using hd
    nlinarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the graph is closed, so `(x, w)` lies on it
  have hgraph : (x, w) ∈ L.graph :=
    hL.mem_of_tendsto (hx.prodMk_nhds hconv) (.of_forall fun n => by
      have hn := L.mem_graph (v n)
      rwa [hv' n] at hn)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨y, -, hy⟩ := hgraph
  exact ⟨y, hy⟩

omit [CompleteSpace V] [CompleteSpace W] in
/-- **The a priori estimate.** Let $L : V \to W$ be a bounded linear operator between inner product
spaces with $c \|v\| \le \|Lv\|$ for all $v$, for some $c > 0$. If $Lv = w$, then
$\|v\| \le \|w\| / c$. This is the quantitative form $\|L^{-1} w\| \le C \|w\|$ of the a priori
estimate (8.2.2) of [han2009theoretical], with $C = 1/c$.

The estimate (8.2.2) is equivalent to injectivity of $L$ with a continuous inverse on the range. -/
theorem ContinuousLinearMap.norm_le_of_le_norm (L : V →L[𝕜] W) {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) {v : V} {w : W} (hv : L v = w) : ‖v‖ ≤ ‖w‖ / c := by
  rw [le_div_iff₀ hc, mul_comm, ← hv]
  exact h v

end APriori
