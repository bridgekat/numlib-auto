/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.Inequality.Basic
import Numlib.Variational.LaxMilgram

/-!
# Brezis, Section 5.3: The theorems of Stampacchia and Lax–Milgram

This module formalizes Section 5.3 of [brezis2011functional] for a real Hilbert space $H$. A
bilinear form $a : H \times H \to \mathbb{R}$ is continuous if $|a(u, v)| \le C |u| |v|$ for all
$u, v$, and coercive if $a(v, v) \ge \alpha |v|^2$ for all $v$ with some $\alpha > 0$. Stampacchia's
theorem states that for a continuous coercive form $a$, a nonempty closed convex set $K \subseteq H$
and $\varphi \in H^\star$, there is a unique $u \in K$ with
$$a(u, v - u) \ge \langle \varphi, v - u \rangle \quad \text{for all } v \in K, \qquad (10)$$
and that for symmetric $a$ this $u$ minimizes $\frac12 a(v, v) - \langle \varphi, v \rangle$ on $K$
(Theorem 5.6). The proof uses the Banach fixed-point theorem (Theorem 5.7). For $K = H$ this is the
Lax–Milgram theorem: there is a unique $u \in H$ with $a(u, v) = \langle \varphi, v \rangle$ for all
$v \in H$ (Corollary 5.8).

Each theorem bundles the continuous form as the backbone's `SesqForm ℝ H` from
`Numlib.Variational.Forms`, by `Brezis.Chapter05.BilinForm.toSesqForm`, and applies the backbone.
Stampacchia's theorem uses `existsUnique_isVariationalInequalitySolution_of_isCoercive` and
`SesqForm.isMinOn_energy_iff_forall_le`, the Lax–Milgram theorem uses `SesqForm.laxMilgram` and
`SesqForm.isMinOn_energy_iff`, and the Banach fixed-point theorem is Mathlib's `ContractingWith`.

## Main definitions

* Section 5.3, `Brezis.Chapter05.BilinForm`: the bilinear forms on $H$, Mathlib's
  `LinearMap.BilinForm ℝ H`.
* Section 5.3, definition (i), `Brezis.Chapter05.BilinForm.IsContinuousWith`:
  $|a(u, v)| \le C |u| |v|$.
* Section 5.3, definition (ii), `Brezis.Chapter05.BilinForm.IsCoerciveWith`:
  $a(v, v) \ge \alpha |v|^2$.
* Section 5.3, `Brezis.Chapter05.BilinForm.toSesqForm`: a continuous bilinear form as a bounded
  sesquilinear form of the backbone.

## Main results

* Section 5.3, `Brezis.Chapter05.BilinForm.toSesqForm_apply`,
  `Brezis.Chapter05.BilinForm.isCoerciveWith_toSesqForm` and
  `Brezis.Chapter05.BilinForm.isHermitian_toSesqForm_of_isSymm`: the bundled form has the same
  values, coercivity and symmetry.
* Theorem 5.6 (Stampacchia), `Brezis.Chapter05.theorem_5_6`: the variational inequality (10) has a
  unique solution in $K$.
* Theorem 5.6, `Brezis.Chapter05.theorem_5_6_symm`: for symmetric $a$, the solutions of (10) are the
  minimizers of $\frac12 a(v, v) - \langle \varphi, v \rangle$ on $K$, and the minimizer is unique.
* Theorem 5.7 (Banach fixed-point theorem), `Brezis.Chapter05.theorem_5_7`: a strict contraction of
  a nonempty complete metric space has a unique fixed point.
* Corollary 5.8 (Lax–Milgram), `Brezis.Chapter05.corollary_5_8`: there is a unique $u \in H$ with
  $a(u, v) = \langle \varphi, v \rangle$ for all $v$.
* Corollary 5.8, `Brezis.Chapter05.corollary_5_8_symm`: for symmetric $a$, $u$ solves (17) if and
  only if it minimizes $\frac12 a(v, v) - \langle \varphi, v \rangle$ on $H$.
* Remark 6, `Brezis.Chapter05.remark_5_6`: if $a(v, v) \ge 0$ for all $v$, then $v \mapsto a(v, v)$
  is convex.
* Remark 7, `Brezis.Chapter05.remark_5_7`: (17) is the Euler equation $F'(u) = 0$ of the energy $F$.
* Remark 8, `Brezis.Chapter05.remark_5_8`: the operator $A$ with $(Au, v) = a(u, v)$ is injective
  with closed dense range, so it is a bijection.

## Conventions

* A symmetric form, $a(u, v) = a(v, u)$, is Mathlib's `LinearMap.BilinForm.IsSymm a`.
* The coercivity constant $\alpha$ is a separate hypothesis `0 < α` of the theorems; the predicate
  `Brezis.Chapter05.BilinForm.IsCoerciveWith` does not include it.

## Implementation notes

* `Brezis.Chapter05.BilinForm` is an abbreviation, so that the predicates on it can be used with dot
  notation.

## Not formalized

* **Theorem 5.16 (Minty–Browder), from the Comments on Chapter 5.**
-/

open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter05

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ### The definition: continuous and coercive bilinear forms -/

/-- **Section 5.3** of [brezis2011functional]. The bilinear forms $a : H \times H \to \mathbb{R}$ of
the source are Mathlib's `LinearMap.BilinForm ℝ H`.

This is an abbreviation, so that the predicates below can be used with dot notation. -/
abbrev BilinForm (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  LinearMap.BilinForm ℝ H

namespace BilinForm

omit [CompleteSpace H] in
/-- **Section 5.3** of [brezis2011functional], definition (i). A bilinear form $a$ on $H$ is
**continuous** with constant $C$ if
$$|a(u, v)| \le C |u| |v| \quad \text{for all } u, v \in H.$$
-/
def IsContinuousWith (a : BilinForm H) (C : ℝ) : Prop :=
  ∀ u v, |a u v| ≤ C * ‖u‖ * ‖v‖

omit [CompleteSpace H] in
/-- **Section 5.3** of [brezis2011functional], definition (ii). A bilinear form $a$ on $H$ is
**coercive** with constant $\alpha$ if
$$a(v, v) \ge \alpha |v|^2 \quad \text{for all } v \in H.$$

The source requires $\alpha > 0$. Here $0 < \alpha$ is a separate hypothesis of the theorems. -/
def IsCoerciveWith (a : BilinForm H) (α : ℝ) : Prop :=
  ∀ v, α * ‖v‖ ^ 2 ≤ a v v

omit [CompleteSpace H] in
/-- A bilinear form $a$ on $H$ that is continuous with constant $C$, bundled as the backbone's
`SesqForm ℝ H`. Over $\mathbb{R}$ a bounded bilinear map $H \to H \to \mathbb{R}$ is a
sesquilinear form. -/
def toSesqForm (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C) : SesqForm ℝ H :=
  LinearMap.mkContinuous₂ a C fun u v => by simpa [Real.norm_eq_abs] using hC u v

omit [CompleteSpace H] in
/-- The bundled form `Brezis.Chapter05.BilinForm.toSesqForm` has the same values as $a$: its value
at $(u, v)$ is $a(u, v)$. -/
@[simp]
theorem toSesqForm_apply (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C) (u v : H) :
    a.toSesqForm hC u v = a u v := rfl

omit [CompleteSpace H] in
/-- If a continuous bilinear form $a$ is coercive with constant $\alpha$, then the bundled form
`Brezis.Chapter05.BilinForm.toSesqForm` is coercive with constant $\alpha$ in the sense of the
backbone's `SesqForm.IsCoerciveWith`. -/
theorem isCoerciveWith_toSesqForm (a : BilinForm H) {C α : ℝ} (hC : a.IsContinuousWith C)
    (hα : a.IsCoerciveWith α) : SesqForm.IsCoerciveWith (a.toSesqForm hC) α := by
  rw [SesqForm.isCoerciveWith_real_iff]
  exact hα

omit [CompleteSpace H] in
/-- If a continuous bilinear form $a$ is symmetric, $a(u, v) = a(v, u)$ for all $u, v$, then the
bundled form `Brezis.Chapter05.BilinForm.toSesqForm` is Hermitian in the sense of the backbone's
`SesqForm.IsHermitian`. -/
theorem isHermitian_toSesqForm_of_isSymm (a : BilinForm H) {C : ℝ} (hC : a.IsContinuousWith C)
    (hs : LinearMap.BilinForm.IsSymm a) : (a.toSesqForm hC).IsHermitian := by
  rw [SesqForm.isHermitian_real_iff]
  intro u v
  rw [toSesqForm_apply, toSesqForm_apply]
  exact LinearMap.BilinForm.isSymm_def.1 hs u v

end BilinForm

open BilinForm

/-! ### Stampacchia's theorem -/

/-- **Theorem 5.6** of [brezis2011functional] (Stampacchia), existence and uniqueness. Let $a$ be a
continuous coercive bilinear form on $H$, with constants $C$ and $\alpha > 0$. Let
$K \subseteq H$ be a nonempty closed convex set and $\varphi \in H^\star$. Then there is a
unique $u \in K$ such that
$$a(u, v - u) \ge \langle \varphi, v - u \rangle \quad \text{for all } v \in K. \qquad (10)$$

The backbone's proof is the proof of the source. Let $f \in H$ represent $\varphi$, and let
$A : H \to H$ satisfy $(Au, v) = a(u, v)$. Then $u$ is a fixed point of
$v \mapsto P_K(\rho f - \rho A v + v)$ for small $\rho > 0$, by Theorem 5.7, because $P_K$ does
not increase distances. -/
theorem theorem_5_6 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (φ : StrongDual ℝ H) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, φ (v - u) ≤ a u (v - u) := by
  have h := existsUnique_isVariationalInequalitySolution_of_isCoercive hα
    (isCoerciveWith_toSesqForm a hC ha) hne hcl hK (convexOn_const 0 hK)
    lowerSemicontinuousOn_const φ
  simpa [IsVariationalInequalitySolution, SesqForm.inner_rieszRep, SesqForm.inner_toOperator,
    toSesqForm_apply] using h

/-- **Theorem 5.6** of [brezis2011functional] (Stampacchia), the symmetric case. Let $a$ be a
continuous coercive bilinear form on $H$, with constants $C$ and $\alpha > 0$, that is moreover
symmetric. Let $K \subseteq H$ be a nonempty closed convex set and $\varphi \in H^\star$. Then:

1. an element $u$ satisfies $u \in K$ and (10) if and only if $u \in K$ and
$$\frac12 a(u, u) - \langle \varphi, u \rangle = \min_{v \in K} \Bigl\{\frac12 a(v, v) - \langle
  \varphi, v \rangle\Bigr\}; \qquad (11)$$
2. there is a unique $u \in K$ that satisfies (11).

The source proves this by showing that $u$ is the projection onto $K$, for the scalar product
$a$, of the element $g$ that represents $\varphi$. This argument is the backbone's
`IsVariationalInequalitySolution.isBestApprox_energy`. -/
theorem theorem_5_6_symm {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : LinearMap.BilinForm.IsSymm a) {K : Set H}
    (hne : K.Nonempty) (hcl : IsClosed K) (hK : Convex ℝ K) (φ : StrongDual ℝ H) :
    (∀ u, (u ∈ K ∧ ∀ v ∈ K, φ (v - u) ≤ a u (v - u)) ↔
        (u ∈ K ∧ IsMinOn (fun v => 1 / 2 * a v v - φ v) K u)) ∧
      ∃! u, u ∈ K ∧ IsMinOn (fun v => 1 / 2 * a v v - φ v) K u := by
  have hh := isHermitian_toSesqForm_of_isSymm a hC hs
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  refine ⟨fun u => ?_, ?_⟩
  · constructor
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      rw [← hE]
      exact (SesqForm.isMinOn_energy_iff_forall_le hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK
        hu).2 h
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      rw [← hE] at h
      exact (SesqForm.isMinOn_energy_iff_forall_le hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK
        hu).1 h
  · rw [← hE]
    exact SesqForm.existsUnique_isMinOn_energy hh φ hα (isCoerciveWith_toSesqForm a hC ha) hK hcl
      hne

/-- **Theorem 5.7** of [brezis2011functional] (Banach fixed-point theorem, contraction mapping
principle). Let $X$ be a nonempty complete metric space and let $S : X \to X$ be a strict
contraction: there is $k < 1$ with
$$d(Sv_1, Sv_2) \le k \, d(v_1, v_2) \quad \text{for all } v_1, v_2 \in X.$$
Then $S$ has a unique fixed point $u = Su$.

The proof is Mathlib's `ContractingWith`, with the constant $\max(k, 0)$. If $k < 0$, the
hypothesis forces $S$ to be constant. -/
theorem theorem_5_7 {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X] (S : X → X)
    {k : ℝ} (hk : k < 1) (hS : ∀ v₁ v₂, dist (S v₁) (S v₂) ≤ k * dist v₁ v₂) :
    ∃! u, S u = u := by
  refine ContractingWith.existsUnique_eq_self (K := Real.toNNReal k) ⟨?_, ?_⟩
  · exact_mod_cast Real.toNNReal_lt_one.2 hk
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    calc dist (S x) (S y) ≤ k * dist x y := hS x y
      _ ≤ Real.toNNReal k * dist x y :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal k) dist_nonneg

/-! ### The Lax–Milgram theorem -/

/-- **Corollary 5.8** of [brezis2011functional] (Lax–Milgram). Let $a$ be a continuous coercive
bilinear form on $H$, with constants $C$ and $\alpha > 0$, and let $\varphi \in H^\star$. Then
there is a unique $u \in H$ such that
$$a(u, v) = \langle \varphi, v \rangle \quad \text{for all } v \in H. \qquad (17)$$
-/
theorem corollary_5_8 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (φ : StrongDual ℝ H) : ∃! u, ∀ v, a u v = φ v :=
  SesqForm.laxMilgram (a.toSesqForm hC) φ hα (isCoerciveWith_toSesqForm a hC ha)

omit [CompleteSpace H] in
/-- **Corollary 5.8** of [brezis2011functional], the symmetric case. Let $a$ be a continuous
coercive bilinear form on a real inner product space $H$, with constants $C$ and $\alpha > 0$,
that is moreover symmetric, and let $\varphi \in H^\star$. Then $u \in H$ satisfies (17) if and
only if
$$\frac12 a(u, u) - \langle \varphi, u \rangle = \min_{v \in H} \Bigl\{\frac12 a(v, v) - \langle
  \varphi, v \rangle\Bigr\}. \qquad (18)$$

Completeness of $H$ is not needed for this equivalence. -/
theorem corollary_5_8_symm {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : LinearMap.BilinForm.IsSymm a) (φ : StrongDual ℝ H) (u : H) :
    (∀ v, a u v = φ v) ↔ IsMinOn (fun v => 1 / 2 * a v v - φ v) Set.univ u := by
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  have h := SesqForm.isMinOn_energy_iff φ (isHermitian_toSesqForm_of_isSymm a hC hs) hα
    (isCoerciveWith_toSesqForm a hC ha) ⊤ (Submodule.mem_top (x := u))
  rw [hE, Submodule.top_coe] at h
  rw [h]
  simp only [Submodule.mem_top, true_implies, toSesqForm_apply]

/-! ### Remarks 6 to 8 -/

omit [CompleteSpace H] in
/-- **Remark 6** in Chapter 5 of [brezis2011functional]. Let $a$ be a bilinear form on $H$ with
$a(v, v) \ge 0$ for all $v \in H$. Then the function $v \mapsto a(v, v)$ is convex on $H$.

Neither symmetry nor continuity is needed. For $s + t = 1$ one has $a(su + tv, su + tv) =
s\,a(u, u) + t\,a(v, v) - st\,a(u - v, u - v)$. -/
theorem remark_5_6 (a : BilinForm H) (hpos : ∀ v, 0 ≤ a v v) :
    ConvexOn ℝ Set.univ fun v => a v v := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  have hsub : a (x - y) (x - y) = a x x - (a x y + a y x) + a y y := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have h := hpos (x - y)
  rw [hsub] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain rfl : t = 1 - s := by linarith
  nlinarith [mul_nonneg (mul_nonneg hs ht) h]

omit [CompleteSpace H] in
/-- **Remark 7** in Chapter 5 of [brezis2011functional], the precise content of "(17) says that
$F'(u) = 0$". Let $a$ be a continuous symmetric bilinear form on $H$, let $\varphi \in H^\star$,
and let
$$F(v) = \frac12 a(v, v) - \langle \varphi, v \rangle.$$
Then for every $u \in H$, $F$ is Fréchet differentiable at $u$ with derivative the functional
$v \mapsto a(u, v) - \langle \varphi, v \rangle$. Moreover $u$ satisfies (17) if and only if
$F'(u) = 0$. So (17) is the Euler equation of the minimization problem (18).

The derivative is written `a.toSesqForm hC u - φ`. -/
theorem remark_5_7 {a : BilinForm H} {C : ℝ} (hC : a.IsContinuousWith C)
    (hs : LinearMap.BilinForm.IsSymm a) (φ : StrongDual ℝ H) (u : H) :
    HasFDerivAt (fun v => 1 / 2 * a v v - φ v) (a.toSesqForm hC u - φ) u ∧
      ((∀ v, a u v = φ v) ↔ fderiv ℝ (fun v => 1 / 2 * a v v - φ v) u = 0) := by
  have hE : (a.toSesqForm hC).energy φ = fun v => 1 / 2 * a v v - φ v := by
    funext v
    simp [SesqForm.energy, toSesqForm_apply]
  have hd := SesqForm.hasFDerivAt_energy (isHermitian_toSesqForm_of_isSymm a hC hs) φ u
  rw [hE] at hd
  refine ⟨hd, ?_⟩
  rw [hd.fderiv, sub_eq_zero]
  constructor
  · intro h
    ext v
    exact h v
  · intro h v
    exact congrArg (fun ψ : StrongDual ℝ H => ψ v) h

/-- **Remark 8** in Chapter 5 of [brezis2011functional], the direct proof of the Lax–Milgram
theorem. Let $a$ be a continuous coercive bilinear form on $H$, with constants $C$ and
$\alpha > 0$, and let $A : H \to H$ be the operator of (13), with $(Au, v) = a(u, v)$. Then:

1. $A$ is injective, because $a$ is coercive;
2. the range $R(A)$ is closed, because $\alpha |v| \le |Av|$;
3. $R(A)$ is dense, because $(Au, v) = 0$ for all $u$ forces $v = 0$;
4. so $A$ is a bijection of $H$ onto $H$, which is (17).

The operator $A$ is the backbone's `SesqForm.toOperator` of the bundled form. -/
theorem remark_5_8 {a : BilinForm H} {C α : ℝ} (hC : a.IsContinuousWith C) (hα : 0 < α)
    (ha : a.IsCoerciveWith α) :
    Function.Injective (a.toSesqForm hC).toOperator ∧
      IsClosed (Set.range (a.toSesqForm hC).toOperator) ∧
      Dense (Set.range (a.toSesqForm hC).toOperator) ∧
      Function.Bijective (a.toSesqForm hC).toOperator := by
  have hcoer : ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H).IsCoerciveWith α :=
    (SesqForm.isCoerciveWith_iff_toOperator _ α).1 (isCoerciveWith_toSesqForm a hC ha)
  have hle : ∀ v, α * ‖v‖ ≤ ‖(a.toSesqForm hC).toOperator v‖ := hcoer.norm_le_norm_apply
  have hrange : Set.range (a.toSesqForm hC).toOperator =
      (LinearMap.range ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H) : Set H) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  have horth : (LinearMap.range ((a.toSesqForm hC).toOperator : H →ₗ[ℝ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hz : ⟪(a.toSesqForm hC).toOperator v, v⟫_ℝ = 0 := hv _ ⟨v, rfl⟩
    rw [SesqForm.inner_toOperator, toSesqForm_apply] at hz
    have h1 : α * ‖v‖ ^ 2 ≤ 0 := (ha v).trans_eq hz
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))
  refine ⟨LinearMap.IsCoercive.injective ⟨α, hα, hcoer⟩, ?_, ?_, ?_⟩
  · rw [hrange]
    exact ContinuousLinearMap.isClosed_range_of_le_norm _ hα hle
  · rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    exact horth
  · exact ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot _ hα hle horth

end Brezis.Chapter05

end
