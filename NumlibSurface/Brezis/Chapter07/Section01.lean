/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.MaximalMonotone

/-!
# Brezis, Section 7.1: Definition and elementary properties of maximal monotone operators

This module formalizes Section 7.1 of [brezis2011functional] for a linear unbounded operator
$A : D(A) \subseteq H \to H$ on a real Hilbert space $H$ with scalar product $(u, v)$ and norm
$|u|$. The operator $A$ is monotone if $(Av, v) \ge 0$ for all $v \in D(A)$, and maximal monotone if
moreover $R(I + A) = H$. A maximal monotone operator has a dense domain and is closed, and for every
$\lambda > 0$ the operator $I + \lambda A$ is a bijection of $D(A)$ onto $H$ whose inverse has norm
at most $1$ (Proposition 7.1). This inverse is the resolvent $J_\lambda = (I + \lambda A)^{-1}$, and
the Yosida approximation is the bounded operator $A_\lambda = \lambda^{-1}(I - J_\lambda)$.
Proposition 7.2 lists its properties: $A_\lambda v = A J_\lambda v$, $|A_\lambda v| \le |Av|$,
$J_\lambda v \to v$ and $A_\lambda v \to Av$ as $\lambda \to 0$, $(A_\lambda v, v) \ge 0$, and
$|A_\lambda v| \le |v|/\lambda$.

All results specialize the backbone module `Numlib.Analysis.InnerProductSpace.MaximalMonotone`,
which states them over `RCLike 𝕜` with the real part of $(Av, v)$; over `ℝ` the real part is the
identity.

## Main definitions

* Section 7.1, definition of a monotone operator, `Brezis.Chapter07.IsMonotone`: $(Av, v) \ge 0$ for
  all $v \in D(A)$.
* Section 7.1, definition of a maximal monotone operator, `Brezis.Chapter07.IsMaximalMonotone`: $A$
  is monotone and $R(I + A) = H$.
* Section 7.1, definition of the resolvent, `Brezis.Chapter07.resolvent`:
  $J_\lambda = (I + \lambda A)^{-1}$ for $\lambda > 0$.
* Section 7.1, definition of the Yosida approximation, `Brezis.Chapter07.yosidaApprox`:
  $A_\lambda = \lambda^{-1}(I - J_\lambda)$ for $\lambda > 0$.

## Main results

* Proposition 7.1, `Brezis.Chapter07.proposition_7_1` with its parts
  `Brezis.Chapter07.proposition_7_1_a`, `Brezis.Chapter07.proposition_7_1_b` and
  `Brezis.Chapter07.proposition_7_1_c`: $D(A)$ is dense, $A$ is closed, and $I + \lambda A$ is a
  bijection of $D(A)$ onto $H$ with a bounded inverse of norm at most $1$.
* Remark 1, `Brezis.Chapter07.remark_7_1`: if $A$ is maximal monotone, then so is $\lambda A$ for
  every $\lambda > 0$.
* `Brezis.Chapter07.norm_resolvent_le`: $|J_\lambda f| \le |f|$.
* Proposition 7.2, `Brezis.Chapter07.proposition_7_2` with its parts
  `Brezis.Chapter07.proposition_7_2_a1`, `Brezis.Chapter07.proposition_7_2_a2`,
  `Brezis.Chapter07.proposition_7_2_b`, `Brezis.Chapter07.proposition_7_2_c`,
  `Brezis.Chapter07.proposition_7_2_d`, `Brezis.Chapter07.proposition_7_2_e` and
  `Brezis.Chapter07.proposition_7_2_f`: the six properties of the Yosida approximation; part (e)
  also gives the inequality (3) of the proof.

## Conventions

* A linear unbounded operator $A : D(A) \subseteq H \to H$ is Mathlib's `LinearPMap`,
  `A : H →ₗ.[ℝ] H`, and $D(A)$ is `A.domain`.
* The parameter $\lambda$ is written `l` in Lean.

## Implementation notes

* The definitions of the source are stated in its words, with equivalences to the backbone
  predicates: `Brezis.Chapter07.isMonotone_iff` and `Brezis.Chapter07.isMaximalMonotone_iff`. The
  resolvent and the Yosida approximation agree with the backbone's bounded operators
  `LinearPMap.resolvent` and `LinearPMap.yosida` by `Brezis.Chapter07.resolvent_eq` and
  `Brezis.Chapter07.yosidaApprox_eq`.
* The resolvent and the Yosida approximation of the source exist only for $\lambda > 0$, so they
  take a proof of $0 < \lambda$ as an argument. The limits of Proposition 7.2(c) and (d) as
  $\lambda \to 0^+$ are therefore stated with the backbone's operators `LinearPMap.resolvent` and
  `LinearPMap.yosida`, which are defined for every $\lambda$ and agree with the source's for
  $\lambda > 0$.

## Deviations from the source

* **Definitions of monotonicity and maximal monotonicity** (generalization). The predicates and
  the range characterization apply to incomplete inner product spaces. See
  `Brezis.Chapter07.IsMonotone`, `Brezis.Chapter07.IsMaximalMonotone` and
  `Brezis.Chapter07.isMaximalMonotone_iff_range`.

## Not formalized

* **Remark 1, second sentence.** The claim that $A + B$ on $D(A) \cap D(B)$ need not be maximal
  monotone is a claim about a counterexample, which is not constructed.
* **Remark 2.** It is a discussion and makes no precise statement.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Brezis.Chapter07

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The definitions -/

/-- **Section 7.1** of [brezis2011functional], definition of a monotone operator. A linear unbounded
operator $A : D(A) \subseteq H \to H$ is **monotone** if
$$(Av, v) \ge 0 \quad \text{for all } v \in D(A).$$

Footnote 1 of the source says that some authors call such an operator accretive, or say that
$-A$ is dissipative.

**Generalization.** The predicate applies to incomplete inner product spaces. -/
def IsMonotone (A : H →ₗ.[ℝ] H) : Prop :=
  ∀ v : A.domain, 0 ≤ ⟪A v, (v : H)⟫_ℝ

/-- The monotonicity of the source is the backbone's `LinearPMap.IsMonotone`, which reads
$0 \le \operatorname{Re}(Av, v)$; over `ℝ` the real part is the identity. -/
theorem isMonotone_iff (A : H →ₗ.[ℝ] H) : IsMonotone A ↔ A.IsMonotone := by
  simp only [IsMonotone, LinearPMap.IsMonotone, RCLike.re_to_real]

/-- **Section 7.1** of [brezis2011functional], definition of a maximal monotone operator. A linear
unbounded operator $A : D(A) \subseteq H \to H$ is **maximal monotone** if it is monotone and
$R(I + A) = H$, that is, for every $f \in H$ there is $u \in D(A)$ with $u + Au = f$.

**Generalization.** The predicate applies to incomplete inner product spaces. -/
def IsMaximalMonotone (A : H →ₗ.[ℝ] H) : Prop :=
  IsMonotone A ∧ ∀ f : H, ∃ u : A.domain, (u : H) + A u = f

/-- The maximal monotonicity of the source is the backbone's `LinearPMap.IsMaximalMonotone`. -/
theorem isMaximalMonotone_iff (A : H →ₗ.[ℝ] H) : IsMaximalMonotone A ↔ A.IsMaximalMonotone :=
  ⟨fun h => ⟨(isMonotone_iff A).1 h.1, h.2⟩,
    fun h => ⟨(isMonotone_iff A).2 h.isMonotone, h.exists_add_apply_eq⟩⟩

/-- A maximal monotone operator in the sense of `Brezis.Chapter07.IsMaximalMonotone` is maximal
monotone in the sense of the backbone's `LinearPMap.IsMaximalMonotone`. -/
theorem IsMaximalMonotone.isMaximalMonotone {A : H →ₗ.[ℝ] H} (hA : IsMaximalMonotone A) :
    A.IsMaximalMonotone :=
  (isMaximalMonotone_iff A).1 hA

/-- A linear unbounded operator $A$ is maximal monotone if and only if it is monotone and the
operator $I + A$, defined on $D(A)$, has range $H$.

The operator $I + A$ is Mathlib's `LinearMap.id +ᵥ A`.

**Generalization.** The characterization applies to incomplete inner product spaces. -/
theorem isMaximalMonotone_iff_range (A : H →ₗ.[ℝ] H) :
    IsMaximalMonotone A ↔
      IsMonotone A ∧ LinearMap.range ((LinearMap.id : H →ₗ[ℝ] H) +ᵥ A).toFun = ⊤ := by
  rw [isMaximalMonotone_iff]
  refine ⟨fun h => ⟨(isMonotone_iff A).2 h.isMonotone, h.range_id_vadd_eq_top⟩, fun h => ?_⟩
  exact LinearPMap.IsMaximalMonotone.of_range_id_vadd_eq_top ((isMonotone_iff A).1 h.1) h.2

/-! ### Proposition 7.1 -/

variable [CompleteSpace H] {A : H →ₗ.[ℝ] H}

/-- **Proposition 7.1(a)** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be
maximal monotone. Then $D(A)$ is dense in $H$. -/
theorem proposition_7_1_a (hA : IsMaximalMonotone A) : Dense (A.domain : Set H) :=
  hA.isMaximalMonotone.dense_domain

/-- **Proposition 7.1(b)** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be
maximal monotone. Then $A$ is closed: its graph is closed in $H \times H$.

The sequential form of closedness, as in the source, is `Brezis.Chapter02.remark_2_11`. -/
theorem proposition_7_1_b (hA : IsMaximalMonotone A) : A.IsClosed :=
  hA.isMaximalMonotone.isClosed

/-- **Proposition 7.1(c)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $\lambda > 0$. Then $I + \lambda A$ is a bijection of $D(A)$ onto $H$. Its
inverse is a bounded operator of norm at most $1$: there is $J \in \mathcal{L}(H)$ with
$\|J\| \le 1$ such that, for every $f \in H$, $Jf \in D(A)$ and $Jf + \lambda A(Jf) = f$.

The operator $J$ of the proof is the backbone's `LinearPMap.resolvent`. -/
theorem proposition_7_1_c (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) :
    Function.Bijective (fun u : A.domain => (u : H) + l • A u) ∧
      ∃ J : H →L[ℝ] H, (∀ f : H, ∃ hf : J f ∈ A.domain, J f + l • A ⟨J f, hf⟩ = f) ∧ ‖J‖ ≤ 1 :=
  ⟨⟨hA.isMaximalMonotone.isMonotone.injective_add_smul hl.le, fun f => by
      obtain ⟨u, hu⟩ := hA.isMaximalMonotone.exists_add_smul_eq hl f
      exact ⟨u, hu⟩⟩,
    A.resolvent l, hA.isMaximalMonotone.resolvent_spec hl,
    hA.isMaximalMonotone.norm_resolvent_le_one hl⟩

/-- **Proposition 7.1** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be maximal
monotone. Then:

* (a) $D(A)$ is dense in $H$;
* (b) $A$ is closed;
* (c) for every $\lambda > 0$, $I + \lambda A$ is a bijection of $D(A)$ onto $H$, and there is
  $J \in \mathcal{L}(H)$ with $\|J\| \le 1$, $Jf \in D(A)$ and $Jf + \lambda A(Jf) = f$ for
  every $f \in H$. -/
theorem proposition_7_1 (hA : IsMaximalMonotone A) :
    Dense (A.domain : Set H) ∧ A.IsClosed ∧ ∀ l : ℝ, 0 < l →
      Function.Bijective (fun u : A.domain => (u : H) + l • A u) ∧
        ∃ J : H →L[ℝ] H, (∀ f : H, ∃ hf : J f ∈ A.domain, J f + l • A ⟨J f, hf⟩ = f) ∧
          ‖J‖ ≤ 1 :=
  ⟨proposition_7_1_a hA, proposition_7_1_b hA, fun _ hl => proposition_7_1_c hA hl⟩

/-- **Remark 1** in Chapter 7 of [brezis2011functional], first sentence. Let $H$ be a Hilbert space
and let $A$ be maximal monotone. Then $\lambda A$ is maximal monotone for every $\lambda > 0$.

The second sentence of the remark, that $A + B$ on $D(A) \cap D(B)$ need not be maximal
monotone, is a claim about a counterexample and is not formalized. -/
theorem remark_7_1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) :
    IsMaximalMonotone (l • A) :=
  (isMaximalMonotone_iff _).2 (hA.isMaximalMonotone.smul hl)

/-! ### The resolvent and the Yosida approximation -/

/-- **Section 7.1** of [brezis2011functional], definition of the resolvent. Let $H$ be a Hilbert
space, let $A$ be maximal monotone, and let $\lambda > 0$. The **resolvent** of $A$ is the map
$$J_\lambda = (I + \lambda A)^{-1} : H \to H,$$
the inverse of the bijection $I + \lambda A : D(A) \to H$ of Proposition 7.1(c), followed by the
inclusion $D(A) \subseteq H$. -/
def resolvent (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) : H → H :=
  fun f => ((Equiv.ofBijective _ (proposition_7_1_c hA hl).1).symm f : H)

/-- The resolvent takes values in the domain: $J_\lambda f \in D(A)$ for every $f \in H$ and
$\lambda > 0$. -/
theorem resolvent_mem_domain (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f ∈ A.domain :=
  ((Equiv.ofBijective _ (proposition_7_1_c hA hl).1).symm f).2

/-- The resolvent satisfies $J_\lambda f + \lambda A(J_\lambda f) = f$ for every $f \in H$ and
$\lambda > 0$. -/
theorem resolvent_add_smul_apply (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f + l • A ⟨resolvent hA hl f, resolvent_mem_domain hA hl f⟩ = f :=
  Equiv.ofBijective_apply_symm_apply _ (proposition_7_1_c hA hl).1 f

/-- For $\lambda > 0$, the resolvent $J_\lambda$ of the source is the backbone's bounded operator
`LinearPMap.resolvent` at $\lambda$. -/
theorem resolvent_eq (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    resolvent hA hl f = A.resolvent l f :=
  ((hA.isMaximalMonotone.resolvent_eq_iff hl ⟨resolvent hA hl f, resolvent_mem_domain hA hl f⟩
    f).2 (resolvent_add_smul_apply hA hl f)).symm

/-- Let $H$ be a Hilbert space, let $A$ be maximal monotone, and let $\lambda > 0$. Then
$|J_\lambda f| \le |f|$ for every $f \in H$.

The source says "keep in mind that $\|J_\lambda\|_{\mathcal{L}(H)} \le 1$". -/
theorem norm_resolvent_le (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (f : H) :
    ‖resolvent hA hl f‖ ≤ ‖f‖ := by
  rw [resolvent_eq]
  exact hA.isMaximalMonotone.norm_resolvent_apply_le hl f

/-- **Section 7.1** of [brezis2011functional], definition of the Yosida approximation. Let $H$ be a
Hilbert space, let $A$ be maximal monotone, and let $\lambda > 0$. The **Yosida approximation**
(or regularization) of $A$ is the map
$$A_\lambda = \frac{1}{\lambda}(I - J_\lambda) : H \to H.$$
-/
def yosidaApprox (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) : H → H :=
  fun v => l⁻¹ • (v - resolvent hA hl v)

/-- For $\lambda > 0$, the Yosida approximation $A_\lambda$ of the source is the backbone's bounded
operator `LinearPMap.yosida` at $\lambda$. -/
theorem yosidaApprox_eq (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    yosidaApprox hA hl v = A.yosida l v := by
  rw [yosidaApprox, LinearPMap.yosida_apply, resolvent_eq]
  rfl

/-! ### Proposition 7.2 -/

/-- **Proposition 7.2(a₁)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be
maximal monotone, and let $\lambda > 0$. Then $A_\lambda v = A(J_\lambda v)$ for all $v \in H$. -/
theorem proposition_7_2_a1 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    yosidaApprox hA hl v = A ⟨resolvent hA hl v, resolvent_mem_domain hA hl v⟩ := by
  rw [yosidaApprox_eq, hA.isMaximalMonotone.yosida_apply_eq_apply_resolvent hl]
  congr 1
  exact Subtype.ext (resolvent_eq hA hl v).symm

/-- **Proposition 7.2(a₂)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be
maximal monotone, and let $\lambda > 0$. Then $A_\lambda v = J_\lambda(Av)$ for all
$v \in D(A)$. -/
theorem proposition_7_2_a2 (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : A.domain) :
    yosidaApprox hA hl v = resolvent hA hl (A v) := by
  rw [yosidaApprox_eq, resolvent_eq]
  exact hA.isMaximalMonotone.yosida_apply_eq_resolvent_apply hl v

/-- **Proposition 7.2(b)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $\lambda > 0$. Then $|A_\lambda v| \le |Av|$ for all $v \in D(A)$. -/
theorem proposition_7_2_b (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : A.domain) :
    ‖yosidaApprox hA hl v‖ ≤ ‖A v‖ := by
  rw [yosidaApprox_eq]
  exact hA.isMaximalMonotone.norm_yosida_apply_le_norm_apply hl v

/-- **Proposition 7.2(c)** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be
maximal monotone. Then for every $v \in H$,
$$\lim_{\lambda \to 0^+} J_\lambda v = v.$$

The function of $\lambda$ is the backbone's `LinearPMap.resolvent`, which equals $J_\lambda$ for
every $\lambda > 0$ by `Brezis.Chapter07.resolvent_eq`. -/
theorem proposition_7_2_c (hA : IsMaximalMonotone A) (v : H) :
    Tendsto (fun l : ℝ => A.resolvent l v) (𝓝[>] 0) (𝓝 v) :=
  hA.isMaximalMonotone.tendsto_resolvent_apply v

/-- **Proposition 7.2(d)** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be
maximal monotone. Then for every $v \in D(A)$,
$$\lim_{\lambda \to 0^+} A_\lambda v = Av.$$

The function of $\lambda$ is the backbone's `LinearPMap.yosida`, which equals $A_\lambda$ for
every $\lambda > 0$ by `Brezis.Chapter07.yosidaApprox_eq`. -/
theorem proposition_7_2_d (hA : IsMaximalMonotone A) (v : A.domain) :
    Tendsto (fun l : ℝ => A.yosida l v) (𝓝[>] 0) (𝓝 (A v)) :=
  hA.isMaximalMonotone.tendsto_yosida_apply v

/-- **Proposition 7.2(e)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $\lambda > 0$. Then for all $v \in H$,
$$(A_\lambda v, v) \ge 0 \quad \text{and} \quad (A_\lambda v, v) \ge \lambda |A_\lambda v|^2.$$

The second inequality is the inequality (3) of the proof in the source. -/
theorem proposition_7_2_e (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    0 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ ∧
      l * ‖yosidaApprox hA hl v‖ ^ 2 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ := by
  rw [yosidaApprox_eq]
  exact ⟨by simpa using hA.isMaximalMonotone.re_inner_yosida_nonneg hl v,
    by simpa using hA.isMaximalMonotone.smul_norm_sq_yosida_le_re_inner hl v⟩

/-- **Proposition 7.2(f)** of [brezis2011functional]. Let $H$ be a Hilbert space, let $A$ be maximal
monotone, and let $\lambda > 0$. Then $|A_\lambda v| \le \frac{1}{\lambda} |v|$ for all
$v \in H$. -/
theorem proposition_7_2_f (hA : IsMaximalMonotone A) {l : ℝ} (hl : 0 < l) (v : H) :
    ‖yosidaApprox hA hl v‖ ≤ (1 / l) * ‖v‖ := by
  rw [yosidaApprox_eq, one_div]
  exact hA.isMaximalMonotone.norm_yosida_apply_le hl v

/-- **Proposition 7.2** of [brezis2011functional]. Let $H$ be a Hilbert space and let $A$ be maximal
monotone. Then:

* (a₁) $A_\lambda v = A(J_\lambda v)$ for all $\lambda > 0$ and $v \in H$;
* (a₂) $A_\lambda v = J_\lambda(Av)$ for all $\lambda > 0$ and $v \in D(A)$;
* (b) $|A_\lambda v| \le |Av|$ for all $\lambda > 0$ and $v \in D(A)$;
* (c) $J_\lambda v \to v$ as $\lambda \to 0^+$, for all $v \in H$;
* (d) $A_\lambda v \to Av$ as $\lambda \to 0^+$, for all $v \in D(A)$;
* (e) $(A_\lambda v, v) \ge 0$ for all $\lambda > 0$ and $v \in H$;
* (f) $|A_\lambda v| \le \frac{1}{\lambda} |v|$ for all $\lambda > 0$ and $v \in H$.

The limits in (c) and (d) are stated with the backbone's `LinearPMap.resolvent` and
`LinearPMap.yosida`, as in `Brezis.Chapter07.proposition_7_2_c` and
`Brezis.Chapter07.proposition_7_2_d`. -/
theorem proposition_7_2 (hA : IsMaximalMonotone A) :
    (∀ (l : ℝ) (hl : 0 < l) (v : H),
        yosidaApprox hA hl v = A ⟨resolvent hA hl v, resolvent_mem_domain hA hl v⟩) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : A.domain), yosidaApprox hA hl v = resolvent hA hl (A v)) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : A.domain), ‖yosidaApprox hA hl v‖ ≤ ‖A v‖) ∧
      (∀ v : H, Tendsto (fun l : ℝ => A.resolvent l v) (𝓝[>] 0) (𝓝 v)) ∧
      (∀ v : A.domain, Tendsto (fun l : ℝ => A.yosida l v) (𝓝[>] 0) (𝓝 (A v))) ∧
      (∀ (l : ℝ) (hl : 0 < l) (v : H), 0 ≤ ⟪yosidaApprox hA hl v, v⟫_ℝ) ∧
      ∀ (l : ℝ) (hl : 0 < l) (v : H), ‖yosidaApprox hA hl v‖ ≤ (1 / l) * ‖v‖ :=
  ⟨fun _ hl v => proposition_7_2_a1 hA hl v, fun _ hl v => proposition_7_2_a2 hA hl v,
    fun _ hl v => proposition_7_2_b hA hl v, proposition_7_2_c hA, proposition_7_2_d hA,
    fun _ hl v => (proposition_7_2_e hA hl v).1, fun _ hl v => proposition_7_2_f hA hl v⟩

end Brezis.Chapter07

end
