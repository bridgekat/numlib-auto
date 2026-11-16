/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Multigrid.Basic

/-!
# Convergence of the two-grid cycle

Let $A$ be a symmetric coercive operator on an inner product space $E$, let $P \colon F \to E$ be a
prolongation from a finite-dimensional coarse space, let $T = I - Q$ be the coarse-grid correction
of `Numlib.Multigrid.Basic`, and let $S$ be the error propagation operator of a smoother. Write
$\|x\|_A = \sqrt{\operatorname{Re} \langle Ax, x \rangle}$ for the energy norm. This module proves
that the two-grid error propagation operator $S^{\nu_2} T S^{\nu_1}$ contracts the energy norm when
two constants $\alpha$ and $\beta$ are available ([saad2003iterative], §13.5.2):

* a **smoothing property** $\|Se\|_A^2 \le \|e\|_A^2 - \alpha\, q(Ae)^2$ for all $e$, where $q$ is a
  seminorm of the residual;
* an **approximation property**: for every $e$ there is a $c \in \operatorname{range} P$ with
  $p(e - c)^2 \le \beta \|e\|_A^2$, where $p$ is a second seminorm.

The two seminorms only need to be dual: $|\langle u, w \rangle| \le q(u)\, p(w)$. Under these
assumptions, one coarse-grid correction followed by one smoothing step contracts the energy norm by
the factor $\sqrt{1 - \alpha/\beta}$, and $\alpha \le \beta$ when $T$ has a nonzero range. The one
concrete smoothing property proved here is that of the damped preconditioned Richardson iteration
$S = I - \omega D^{-1} A$, which includes weighted Jacobi.

## Main definitions

* `Multigrid.IsDualSeminormPair`: two nonnegative functions $p, q$ on $E$ with
  $|\langle u, w \rangle| \le q(u)\, p(w)$.
* `Multigrid.IsSmootherWith`: the smoothing property with the seminorm $q$ and the constant
  $\alpha$.
* `Multigrid.IsApproximationWith`: the approximation property of a coarse space with the seminorm
  $p$ and the constant $\beta$.

## Main results

* `Multigrid.isDualSeminormPair_norm`: the norm is dual to itself.
* `Multigrid.isDualSeminormPair_energy`: for symmetric coercive $D$, the energy norms of $D$ and of
  $D^{-1}$ are dual.
* `Multigrid.energyNorm_le_of_isApproximationWith`: an error $e$ in the range of $T$ has
  $\|e\|_A \le \sqrt{\beta}\, q(Ae)$.
* `Multigrid.IsSmootherWith.le_of_isApproximationWith`: if $T$ has a nonzero range, then
  $\alpha \le \beta$.
* `Multigrid.energyNorm_twoGrid_le`: $\|STv\|_A \le \sqrt{1 - \alpha/\beta}\, \|v\|_A$.
* `Multigrid.energyNorm_twoGridOperator_le`: the same bound for the full two-grid cycle with at
  least one post-smoothing step.
* `Multigrid.isSmootherWith_richardson`: the smoothing property of $S = I - \omega D^{-1} A$ with
  $\alpha = \omega (2 - \omega \gamma)$.

## Proof outline

An error $e$ in the range of $T$ is $A$-orthogonal to the coarse space, so
$\|e\|_A^2 = \langle Ae, e - c \rangle$ for every $c \in \operatorname{range} P$. The duality of the
seminorms and the approximation property turn this into $\|e\|_A \le \sqrt{\beta}\, q(Ae)$. Put into
the smoothing property, this bound gives the rate $\sqrt{1 - \alpha/\beta}$. The comparison of the
two bounds on one nonzero error gives $\alpha \le \beta$.

## Implementation notes

* The smoothing and approximation properties are assumed, not proved, except for the Richardson
  smoother. They are estimates about a discretization and cannot be proved by linear algebra. A
  source that proves them for its own finite element spaces gets the convergence theorems of this
  module.
* The two-grid theorems assume only the duality `Multigrid.IsDualSeminormPair` of the two seminorms.
  The classical pair $p = \|\cdot\|_D$, $q = \|\cdot\|_{D^{-1}}$ for a symmetric positive definite
  $D$ is `Multigrid.isDualSeminormPair_energy`, and the Cauchy–Schwarz pair $p = q = \|\cdot\|$ is
  `Multigrid.isDualSeminormPair_norm`.
* For the Richardson smoother, $\alpha = \omega (2 - \omega \gamma)$ is positive exactly on the
  classical range $0 < \omega < 2/\gamma$, but the smoothing inequality holds for every real
  $\omega$.
-/

namespace Multigrid

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-! ### A dual pair of seminorms -/

/-- Let $p, q \colon E \to \mathbb{R}$. The pair $(p, q)$ is a **dual seminorm pair** if $p$ and $q$
are nonnegative and
$$|\langle u, w \rangle| \le q(u)\, p(w) \quad \text{for all } u, w \in E.$$

This is the only relation between the seminorm $q$ of the smoothing property and the seminorm
$p$ of the approximation property that the two-grid theorem uses, so the theorem assumes only
this. In (13.62)–(13.63) of [saad2003iterative], $q = \|\cdot\|_{D^{-1}}$ and $p = \|\cdot\|_D$.
The functions $p$ and $q$ need not be seminorms. -/
structure IsDualSeminormPair (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (p q : E → ℝ) : Prop where
  /-- The function $p$, which measures the second argument, is nonnegative. -/
  p_nonneg : ∀ w, 0 ≤ p w
  /-- The function $q$, which measures the first argument, is nonnegative. -/
  q_nonneg : ∀ u, 0 ≤ q u
  /-- The duality: $|\langle u, w \rangle| \le q(u)\, p(w)$ for all $u, w \in E$. -/
  norm_inner_le : ∀ u w, ‖inner 𝕜 u w‖ ≤ q u * p w

/-- The norm is dual to itself: $(\|\cdot\|, \|\cdot\|)$ is a dual seminorm pair, by the
Cauchy–Schwarz inequality. -/
theorem isDualSeminormPair_norm : IsDualSeminormPair 𝕜 (norm : E → ℝ) (norm : E → ℝ) :=
  ⟨fun _ => norm_nonneg _, fun _ => norm_nonneg _, fun _ _ => norm_inner_le_norm _ _⟩

/-- Let $D \colon E \to E$ be symmetric coercive, and let $D^{-1} \colon E \to E$ be a right inverse
of $D$, that is, $D(D^{-1} u) = u$ for all $u$. Then the energy norms of $D$ and of $D^{-1}$ are
dual:
$$|\langle u, w \rangle| \le \|u\|_{D^{-1}}\, \|w\|_D \quad \text{for all } u, w \in E.$$

With $D$ the diagonal part of $A$, this is the pair of seminorms with which [saad2003iterative]
states the smoothing and approximation properties. The right inverse $D^{-1}$ is the Lean
variable `Dinv`. -/
theorem isDualSeminormPair_energy {D Dinv : E →ₗ[𝕜] E} (hD : D.IsSymmetricCoercive)
    (hinv : ∀ u, D (Dinv u) = u) :
    IsDualSeminormPair 𝕜 (energyNorm D) (energyNorm Dinv) := by
  have hnorm : ∀ u : E, energyNorm D (Dinv u) = energyNorm Dinv u := fun u => by
    have h : RCLike.re (inner 𝕜 (D (Dinv u)) (Dinv u)) = RCLike.re (inner 𝕜 (Dinv u) u) := by
      rw [hinv, ← inner_conj_symm (Dinv u) u, RCLike.conj_re]
    exact congrArg Real.sqrt h
  refine ⟨fun _ => energyNorm_nonneg _ _, fun _ => energyNorm_nonneg _ _, fun u w => ?_⟩
  have h : inner 𝕜 u w = energyInner D (Dinv u) w := by rw [energyInner, hinv]
  rw [h]
  exact (hD.abs_energyInner_le (Dinv u) w).trans_eq (by rw [hnorm])

/-! ### The two named hypotheses -/

/-- Let $A, S \colon E \to E$ be linear, let $q \colon E \to \mathbb{R}$, and let
$\alpha \in \mathbb{R}$. The operator $S$ has the **smoothing property** with the seminorm $q$
and the constant $\alpha$ if
$$\|Se\|_A^2 \le \|e\|_A^2 - \alpha\, q(Ae)^2 \quad \text{for all } e \in E.$$

This is (13.62) of [saad2003iterative]. The operator $S$ is the error propagation operator of
the smoother, and the inequality says that $S$ reduces the energy norm of the error by an amount
measured by the seminorm of the residual. The property cannot be proved by linear algebra alone.
`Multigrid.isSmootherWith_richardson` is the one case that this library proves. -/
def IsSmootherWith (A : E →ₗ[𝕜] E) (q : E → ℝ) (S : E →ₗ[𝕜] E) (α : ℝ) : Prop :=
  ∀ e, energyNorm A (S e) ^ 2 ≤ energyNorm A e ^ 2 - α * q (A e) ^ 2

/-- Let $A \colon E \to E$ be linear, let $p \colon E \to \mathbb{R}$, let $V_c \le E$ be a
subspace, and let $\beta \in \mathbb{R}$. The coarse space $V_c$ has the **approximation
property** with the seminorm $p$ and the constant $\beta$ if for every $e \in E$ there is a
$c \in V_c$ with
$$p(e - c)^2 \le \beta \|e\|_A^2.$$

This is (13.63) of [saad2003iterative]. The property is stated with an existential quantifier
and not with an infimum, because an interpolation estimate provides this form and the
convergence proof uses this form. -/
def IsApproximationWith (A : E →ₗ[𝕜] E) (p : E → ℝ) (Vc : Submodule 𝕜 E) (β : ℝ) : Prop :=
  ∀ e, ∃ c ∈ Vc, p (e - c) ^ 2 ≤ β * energyNorm A e ^ 2

namespace IsSmootherWith

variable {A : E →ₗ[𝕜] E} {q : E → ℝ} {S : E →ₗ[𝕜] E} {α : ℝ}

/-- If $S$ has the smoothing property with a constant $\alpha \ge 0$, then $S$ does not increase the
energy norm: $\|Se\|_A \le \|e\|_A$ for all $e \in E$. -/
theorem energyNorm_le (h : IsSmootherWith A q S α) (hα : 0 ≤ α) (e : E) :
    energyNorm A (S e) ≤ energyNorm A e := by
  refine energyNorm_le_of_sq_le ((h e).trans ?_)
  have : 0 ≤ α * q (A e) ^ 2 := mul_nonneg hα (sq_nonneg _)
  linarith

/-- If $S$ has the smoothing property with a constant $\alpha \ge 0$, then every power of $S$ does
not increase the energy norm: $\|S^n e\|_A \le \|e\|_A$ for all $n \in \mathbb{N}$ and
$e \in E$. -/
theorem energyNorm_pow_le (h : IsSmootherWith A q S α) (hα : 0 ≤ α) (n : ℕ) (e : E) :
    energyNorm A ((S ^ n) e) ≤ energyNorm A e := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact (ih (S e)).trans (h.energyNorm_le hα e)

end IsSmootherWith

/-! ### The geometry of the coarse-grid correction -/

section Geometry

variable (A : E →ₗ[𝕜] E) (hA : A.IsSymmetricCoercive) (Pr : F →ₗ[𝕜] E)

/-- Let $A \colon E \to E$ be symmetric coercive and let $P \colon F \to E$ be a prolongation. Then
the coarse-grid correction $T$ does not increase the energy norm: $\|Tv\|_A \le \|v\|_A$ for all
$v \in E$.

The coarse-grid correction is the $A$-orthogonal projection onto the $A$-orthogonal complement
of the coarse space. This bound allows the convergence proof to treat the smoothing steps of a
cycle separately from the correction. -/
theorem energyNorm_coarseCorrection_le (v : E) :
    energyNorm A (coarseCorrection A hA Pr v) ≤ energyNorm A v := by
  refine energyNorm_le_of_sq_le ?_
  set K := WithEnergy.submoduleMap A hA (LinearMap.range Pr) with hK
  have hval : WithEnergy.equiv A hA (coarseCorrection A hA Pr v)
      = Kᗮ.starProjection (WithEnergy.equiv A hA v) := by
    rw [coarseCorrection_apply, map_sub, equiv_coarseProjection,
      Submodule.starProjection_orthogonal_val]
  have h := K.norm_sq_eq_add_norm_sq_starProjection (WithEnergy.equiv A hA v)
  rw [← WithEnergy.norm_equiv A hA (coarseCorrection A hA Pr v), ← WithEnergy.norm_equiv A hA v,
    hval, h]
  have := sq_nonneg ‖K.starProjection (WithEnergy.equiv A hA v)‖
  linarith

end Geometry

section Convergence

variable {A : E →ₗ[𝕜] E} {hA : A.IsSymmetricCoercive} {Pr : F →ₗ[𝕜] E}
  {p q : E → ℝ} {α β : ℝ} [FiniteDimensional 𝕜 E]

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation with coarse-grid correction $T$. Let $(p, q)$ be a dual
seminorm pair, and let $\operatorname{range} P$ have the approximation property with the
seminorm $p$ and the constant $\beta$. Then every $e \in \operatorname{range} T$ satisfies
$$\|e\|_A \le \sqrt{\beta}\, q(Ae).$$

This is the geometric half of the proof of Theorem 13.3 of [saad2003iterative]: an error left by
the coarse-grid correction is $A$-orthogonal to the coarse space. The rate of the two-grid cycle
and the inequality $\alpha \le \beta$ both come from this bound. The square root is `Real.sqrt`,
which is $0$ for $\beta < 0$. -/
theorem energyNorm_le_of_isApproximationWith (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) {e : E}
    (he : e ∈ LinearMap.range (coarseCorrection A hA Pr)) :
    energyNorm A e ≤ Real.sqrt β * q (A e) := by
  rw [range_coarseCorrection] at he
  have hPr : LinearMap.adjoint Pr (A e) = 0 := he
  obtain ⟨c, hc, hcb⟩ := happ e
  obtain ⟨y, rfl⟩ := hc
  have hq : 0 ≤ q (A e) := hpq.q_nonneg _
  have hzero : inner 𝕜 (A e) (Pr y) = (0 : 𝕜) := by
    rw [← LinearMap.adjoint_inner_left, hPr, inner_zero_left]
  have h1 : energyNorm A e ^ 2 = RCLike.re (inner 𝕜 (A e) (e - Pr y)) := by
    rw [hA.energyNorm_sq, inner_sub_right, hzero, sub_zero]
  have h2 : RCLike.re (inner 𝕜 (A e) (e - Pr y)) ≤ q (A e) * p (e - Pr y) :=
    (RCLike.re_le_norm _).trans (hpq.norm_inner_le _ _)
  have h3 : p (e - Pr y) ≤ Real.sqrt β * energyNorm A e := by
    calc p (e - Pr y) ≤ |p (e - Pr y)| := le_abs_self _
      _ = Real.sqrt (p (e - Pr y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (β * energyNorm A e ^ 2) := Real.sqrt_le_sqrt hcb
      _ = Real.sqrt β * energyNorm A e := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (energyNorm_nonneg A e)]
  have hkey : energyNorm A e * energyNorm A e
      ≤ Real.sqrt β * q (A e) * energyNorm A e := by
    calc energyNorm A e * energyNorm A e = energyNorm A e ^ 2 := (sq _).symm
      _ ≤ q (A e) * p (e - Pr y) := h1.trans_le h2
      _ ≤ q (A e) * (Real.sqrt β * energyNorm A e) := by gcongr
      _ = Real.sqrt β * q (A e) * energyNorm A e := by ring
  rcases (energyNorm_nonneg A e).lt_or_eq with hpos | hzero'
  · exact le_of_mul_le_mul_right hkey hpos
  · rw [← hzero']
    exact mul_nonneg (Real.sqrt_nonneg β) hq

/-- The square of `Multigrid.energyNorm_le_of_isApproximationWith`: for $\beta \ge 0$, every
$e \in \operatorname{range} T$ satisfies $\|e\|_A^2 \le \beta\, q(Ae)^2$. -/
private theorem energyNorm_sq_le_of_isApproximationWith (hβ : 0 ≤ β)
    (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) {e : E}
    (he : e ∈ LinearMap.range (coarseCorrection A hA Pr)) :
    energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 := by
  have hgeo := energyNorm_le_of_isApproximationWith (hA := hA) hpq happ he
  calc energyNorm A e ^ 2 = energyNorm A e * energyNorm A e := sq _
    _ ≤ Real.sqrt β * q (A e) * (Real.sqrt β * q (A e)) :=
        mul_self_le_mul_self (energyNorm_nonneg A e) hgeo
    _ = Real.sqrt β ^ 2 * q (A e) ^ 2 := by ring
    _ = β * q (A e) ^ 2 := by rw [Real.sq_sqrt hβ]

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation with coarse-grid correction $T$. Let $(p, q)$ be a dual
seminorm pair, let $S$ have the smoothing property with the seminorm $q$ and the constant
$\alpha$, and let $\operatorname{range} P$ have the approximation property with the seminorm $p$
and the constant $\beta$. If some $e \in \operatorname{range} T$ is nonzero, then
$$\alpha \le \beta.$$

This is the relation between the constants in Theorem 13.3 of [saad2003iterative]. The
hypothesis $e \neq 0$ is necessary: on the zero space, with $p = q = 0$, every pair of constants
satisfies both properties. -/
theorem IsSmootherWith.le_of_isApproximationWith {S : E →ₗ[𝕜] E}
    (hsm : IsSmootherWith A q S α) (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β)
    {e : E} (he : e ∈ LinearMap.range (coarseCorrection A hA Pr)) (he0 : e ≠ 0) :
    α ≤ β := by
  have hgeo := energyNorm_le_of_isApproximationWith (hA := hA) hpq happ he
  have hpos : 0 < energyNorm A e := hA.energyNorm_pos he0
  have hb : 0 ≤ β := by
    by_contra hb
    push Not at hb
    rw [Real.sqrt_eq_zero_of_nonpos hb.le, zero_mul] at hgeo
    exact absurd hgeo (not_le.2 hpos)
  have hqpos : 0 < q (A e) := by
    by_contra h
    push Not at h
    exact absurd (hgeo.trans (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg β) h))
      (not_le.2 hpos)
  have hbsq : energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 :=
    energyNorm_sq_le_of_isApproximationWith (hA := hA) hb hpq happ he
  have hsm' := hsm e
  have hnn : 0 ≤ energyNorm A (S e) ^ 2 := sq_nonneg _
  exact le_of_mul_le_mul_right (by linarith) (pow_pos hqpos 2)

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation with coarse-grid correction $T$. Let $(p, q)$ be a dual
seminorm pair, let $S$ have the smoothing property with the seminorm $q$ and a constant
$\alpha \ge 0$, and let $\operatorname{range} P$ have the approximation property with the
seminorm $p$ and a constant $\beta > 0$. Then one coarse-grid correction followed by one
smoothing step contracts the energy norm of the error:
$$\|S T v\|_A \le \sqrt{1 - \alpha/\beta}\, \|v\|_A \quad \text{for all } v \in E.$$

This is Theorem 13.3 of [saad2003iterative]. The factor depends only on the two constants. The
square root is `Real.sqrt`, which is $0$ for a negative argument. -/
theorem energyNorm_twoGrid_le {S : E →ₗ[𝕜] E} (hsm : IsSmootherWith A q S α)
    (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) (hα : 0 ≤ α) (hβ : 0 < β) (v : E) :
    energyNorm A (S (coarseCorrection A hA Pr v))
      ≤ Real.sqrt (1 - α / β) * energyNorm A v := by
  have hmem : coarseCorrection A hA Pr v ∈ LinearMap.range (coarseCorrection A hA Pr) := ⟨v, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : E, coarseCorrection A hA Pr v = e := ⟨_, rfl⟩
  rw [he] at hmem ⊢
  have hnex : energyNorm A e ≤ energyNorm A v := by
    rw [← he]; exact energyNorm_coarseCorrection_le A hA Pr v
  have hsq : energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 :=
    energyNorm_sq_le_of_isApproximationWith (hA := hA) hβ.le hpq happ hmem
  have h1 := hsm e
  rcases (energyNorm_nonneg A e).lt_or_eq with hpos | hzero
  · -- the substantial case: the coarse-grid error is nonzero
    have hqpos : 0 < q (A e) ^ 2 := by
      rcases (sq_nonneg (q (A e))).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hsq
        exact absurd hsq (not_le.2 (pow_pos hpos 2))
    have hab : α ≤ β :=
      le_of_mul_le_mul_right (by linarith [sq_nonneg (energyNorm A (S e))]) hqpos
    have hcoef : 0 ≤ 1 - α / β := by rw [sub_nonneg, div_le_one hβ]; exact hab
    have h2 : α * (energyNorm A e ^ 2 / β) ≤ α * q (A e) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hα
      rw [div_le_iff₀ hβ]
      calc energyNorm A e ^ 2 ≤ β * q (A e) ^ 2 := hsq
        _ = q (A e) ^ 2 * β := by ring
    have hid : (1 - α / β) * energyNorm A e ^ 2
        = energyNorm A e ^ 2 - α * (energyNorm A e ^ 2 / β) := by field_simp
    have h3 : energyNorm A (S e) ^ 2 ≤ (1 - α / β) * energyNorm A e ^ 2 := by
      rw [hid]; linarith
    have hmono : energyNorm A e ^ 2 ≤ energyNorm A v ^ 2 := by
      nlinarith [energyNorm_nonneg A e]
    have hbound : energyNorm A (S e) ^ 2 ≤ (1 - α / β) * energyNorm A v ^ 2 :=
      h3.trans (by gcongr)
    calc energyNorm A (S e) = Real.sqrt (energyNorm A (S e) ^ 2) :=
          (Real.sqrt_sq (energyNorm_nonneg A _)).symm
      _ ≤ Real.sqrt ((1 - α / β) * energyNorm A v ^ 2) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (1 - α / β) * energyNorm A v := by
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (energyNorm_nonneg A v)]
  · -- a degenerate error: the smoothed error vanishes too
    have hnn : 0 ≤ α * q (A e) ^ 2 := mul_nonneg hα (sq_nonneg _)
    have h2 : energyNorm A (S e) ^ 2 ≤ 0 := by rw [← hzero] at h1; nlinarith
    have h3 : energyNorm A (S e) = 0 := by
      have := energyNorm_nonneg A (S e)
      nlinarith
    rw [h3]
    exact mul_nonneg (Real.sqrt_nonneg _) (energyNorm_nonneg A v)

/-- Let $E$ be finite-dimensional, let $A \colon E \to E$ be symmetric coercive, and let
$P \colon F \to E$ be a prolongation. Let $(p, q)$ be a dual seminorm pair, let $S$ have the
smoothing property with the seminorm $q$ and a constant $\alpha \ge 0$, and let
$\operatorname{range} P$ have the approximation property with the seminorm $p$ and a constant
$\beta > 0$. Then for $\nu_1 \ge 0$ pre-smoothing steps and $\nu_2 \ge 1$ post-smoothing steps,
the two-grid error propagation operator $M_H^h = S^{\nu_2} (I - Q) S^{\nu_1}$ satisfies
$$\|M_H^h v\|_A \le \sqrt{1 - \alpha/\beta}\, \|v\|_A \quad \text{for all } v \in E.$$

This is Theorem 13.3 of [saad2003iterative] for the full cycle. The additional smoothing steps
do not increase the energy norm. The operator $M_H^h$ is `Multigrid.twoGridOperator`. -/
theorem energyNorm_twoGridOperator_le {S : E →ₗ[𝕜] E} (hsm : IsSmootherWith A q S α)
    (hpq : IsDualSeminormPair 𝕜 p q)
    (happ : IsApproximationWith A p (LinearMap.range Pr) β) (hα : 0 ≤ α) (hβ : 0 < β)
    {nu1 nu2 : ℕ} (hnu : 1 ≤ nu2) (v : E) :
    energyNorm A (twoGridOperator A hA Pr S nu1 nu2 v)
      ≤ Real.sqrt (1 - α / β) * energyNorm A v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnu
  rw [twoGridOperator_apply, Nat.add_comm 1 k, pow_succ, Module.End.mul_apply]
  calc energyNorm A ((S ^ k) (S (coarseCorrection A hA Pr ((S ^ nu1) v))))
      ≤ energyNorm A (S (coarseCorrection A hA Pr ((S ^ nu1) v))) :=
        hsm.energyNorm_pow_le hα k _
    _ ≤ Real.sqrt (1 - α / β) * energyNorm A ((S ^ nu1) v) :=
        energyNorm_twoGrid_le hsm hpq happ hα hβ _
    _ ≤ Real.sqrt (1 - α / β) * energyNorm A v :=
        mul_le_mul_of_nonneg_left (hsm.energyNorm_pow_le hα nu1 v) (Real.sqrt_nonneg _)

end Convergence

/-! ### The one smoothing property that is a theorem -/

/-- Let $A, D \colon E \to E$ be symmetric coercive, let $D^{-1}$ be a right inverse of $D$, that
is, $D(D^{-1} u) = u$ for all $u$, and let $\gamma \in \mathbb{R}$ with
$$\operatorname{Re} \langle Ax, x \rangle \le \gamma \operatorname{Re} \langle Dx, x \rangle
  \quad \text{for all } x \in E.$$
Then for every $\omega \in \mathbb{R}$, the error propagation operator $S = I - \omega D^{-1} A$
of the damped preconditioned Richardson iteration has the smoothing property with the seminorm
$q = \|\cdot\|_{D^{-1}}$ and the constant
$$\alpha = \omega (2 - \omega \gamma).$$

This is Example 13.8 and Exercise 13.15 of [saad2003iterative]. The constant $\alpha$ is
positive exactly for $0 < \omega < 2/\gamma$ when $\gamma > 0$. The Richardson iteration is the
case $D = I$, and weighted Jacobi is the case where $D$ is the diagonal part of $A$. The right
inverse $D^{-1}$ is the Lean variable `Dinv`. -/
theorem isSmootherWith_richardson {A D Dinv : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive)
    (hD : D.IsSymmetricCoercive) (hinv : ∀ u, D (Dinv u) = u) {γ : ℝ}
    (hγ : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ γ * RCLike.re (inner 𝕜 (D x) x)) (ω : ℝ) :
    IsSmootherWith A (energyNorm Dinv) (1 - (ω : 𝕜) • (Dinv ∘ₗ A)) (ω * (2 - ω * γ)) := by
  intro e
  obtain ⟨z, hz⟩ : ∃ z : E, Dinv (A e) = z := ⟨_, rfl⟩
  have hDz : D z = A e := by rw [← hz]; exact hinv (A e)
  have hSe : (1 - (ω : 𝕜) • (Dinv ∘ₗ A)) e = e - (ω : 𝕜) • z := by rw [← hz]; rfl
  -- the dual seminorm of the residual is the `D`-norm of the correction
  have hqnn : 0 ≤ RCLike.re (inner 𝕜 (Dinv (A e)) (A e)) := by
    rw [hz, ← hDz, ← inner_conj_symm z (D z), RCLike.conj_re]
    exact hD.isPositive.re_inner_nonneg_left z
  have hq : energyNorm Dinv (A e) ^ 2 = RCLike.re (inner 𝕜 (D z) z) := by
    have h : energyNorm Dinv (A e) ^ 2 = RCLike.re (inner 𝕜 (Dinv (A e)) (A e)) :=
      Real.sq_sqrt hqnn
    rw [h, hz, ← hDz, ← inner_conj_symm z (D z), RCLike.conj_re]
  -- expand the energy norm of the smoothed error
  have hexp : energyNorm A (e - (ω : 𝕜) • z) ^ 2
      = energyNorm A e ^ 2 - 2 * ω * RCLike.re (inner 𝕜 (A e) z)
        + ω ^ 2 * RCLike.re (inner 𝕜 (A z) z) := by
    have h1 : energyNorm A (e - (ω : 𝕜) • z)
        = ‖WithEnergy.equiv A hA e - (ω : 𝕜) • WithEnergy.equiv A hA z‖ := by
      rw [← WithEnergy.norm_equiv A hA (e - (ω : 𝕜) • z), map_sub, map_smul]
    have h2 : RCLike.re ((ω : 𝕜) * inner 𝕜 (WithEnergy.equiv A hA e) (WithEnergy.equiv A hA z))
        = ω * RCLike.re (inner 𝕜 (A e) z) := by
      rw [RCLike.re_ofReal_mul, WithEnergy.inner_equiv]
      rfl
    rw [h1, norm_sub_sq (𝕜 := 𝕜), inner_smul_right, h2, norm_smul, RCLike.norm_ofReal, mul_pow,
      sq_abs, WithEnergy.norm_equiv, WithEnergy.norm_equiv, hA.energyNorm_sq, hA.energyNorm_sq]
    ring
  have hAez : RCLike.re (inner 𝕜 (A e) z) = RCLike.re (inner 𝕜 (D z) z) := by rw [hDz]
  have hAzz : RCLike.re (inner 𝕜 (A z) z) ≤ γ * RCLike.re (inner 𝕜 (D z) z) := hγ z
  rw [hSe, hexp, hq, hAez]
  nlinarith [sq_nonneg ω]

end Multigrid
