/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Ring.Inverse
import NumlibSurface.AtkinsonHan.Chapter02.Section03

/-!
# Atkinson and Han, Section 2.9: The resolvent operator

This module formalizes Section 2.9 of [han2009theoretical]. Let $L$ be a bounded linear operator on
a normed space $V$. A scalar $\lambda$ is in the resolvent set $\rho(L)$ if $\lambda - L$ has a
bounded inverse $R(\lambda) = (\lambda - L)^{-1}$, the resolvent operator, and the spectrum
$\sigma(L)$ is the complement of $\rho(L)$. On a Banach space, $\rho(L)$ is open: if
$\lambda_0 \in \rho(L)$ and $|\lambda - \lambda_0| \|R(\lambda_0)\| < 1$, then
$\lambda \in \rho(L)$, the difference $R(\lambda) - R(\lambda_0)$ obeys the bound (2.9.2), and
$R(\lambda)$ is the sum of the Neumann series (2.9.3) in powers of $\lambda - \lambda_0$. The
spectrum lies in the closed disc of radius $\|L\|$.

Definition 2.9.1 is Mathlib's `resolventSet`, `spectrum` and `resolvent`, restated under the number
of the source. The quantitative results, the radius $1/\|R(\lambda_0)\|$, the bound (2.9.2) and the
series (2.9.3), come from the perturbation theorems for inverses in the backbone module
`Numlib.Analysis.Normed.Ring.Inverse`, as the source derives them from its Theorem 2.3.5.

## Main definitions

* Definition 2.9.1(a), `AtkinsonHan.Chapter02.definition_2_9_1`: $\lambda \in \rho(L)$ if
  $\lambda - L$ has a bounded inverse.
* Definition 2.9.1(b), `AtkinsonHan.Chapter02.definition_2_9_1_spectrum`: the spectrum $\sigma(L)$,
  the complement of $\rho(L)$.

## Main results

* Definition 2.9.1(a), `AtkinsonHan.Chapter02.definition_2_9_1_iff` and
  `AtkinsonHan.Chapter02.definition_2_9_1_resolvent`: the resolvent set is Mathlib's `resolventSet`,
  and `resolvent L λ` is the inverse of $\lambda - L$.
* Definition 2.9.1(b), `AtkinsonHan.Chapter02.definition_2_9_1_spectrum_eq`: the spectrum is
  Mathlib's `spectrum`.
* Section 2.9, `AtkinsonHan.Chapter02.spectrum_subset_closedBall`: every $\lambda$ with
  $|\lambda| > \|L\|$ is in $\rho(L)$, so $\sigma(L)$ lies in the closed disc of radius $\|L\|$.
* Lemma 2.9.2, `AtkinsonHan.Chapter02.lemma_2_9_2`: $\rho(L)$ is open, $\sigma(L)$ is closed, and
  the perturbation bound (2.9.2) holds.
* Equation (2.9.3), `AtkinsonHan.Chapter02.equation_2_9_3`: $R(\lambda) = \sum_{k \ge 0} (-1)^k
  (\lambda - \lambda_0)^k R(\lambda_0)^{k+1}$.

## Conventions

* The scalar $\lambda$ is written `lam`. The space $\mathcal{L}(V)$ of bounded operators is the
  Banach algebra `V →L[𝕜] V`.
* The resolvent $R(\lambda) = (\lambda I - L)^{-1}$ of the source is `resolvent L λ`, defined as
  `Ring.inverse (algebraMap 𝕜 _ λ - L)`.
* As in Chapter 1, Definition 2.9.1 is a `def … : Prop` in the words of the source, with a companion
  `…_iff`, and its second clause has a descriptive suffix instead of a letter.
* "$(\lambda - L)^{-1}$ exists as a bounded linear operator" is written as in §2.3: there is a
  continuous linear equivalence whose underlying map is $\lambda - L$. The lemma
  `AtkinsonHan.Chapter02.isUnit_iff_exists_continuousLinearEquiv` of §2.3 is the bridge to
  `IsUnit`.
* `AtkinsonHan.Chapter02.lemma_2_9_2` and `AtkinsonHan.Chapter02.spectrum_subset_closedBall` assume
  `[Nontrivial V]`, which the source assumes implicitly. On the zero space, $\mathcal{L}(V)$ is the
  zero ring, $\|I\| = 0$, and the radius $1/\|R(\lambda_0)\|$ has no meaning.
  `AtkinsonHan.Chapter02.equation_2_9_3` and Definition 2.9.1 do not need this hypothesis.

## Implementation notes

* The analyticity of $\lambda \mapsto R(\lambda)$, which the source reads off (2.9.3), is Mathlib's
  `spectrum.hasDerivAt_resolvent_const_left`. The series of `AtkinsonHan.Chapter02.equation_2_9_3`
  is the Taylor expansion of $R$ at $\lambda_0$.
* `AtkinsonHan.Chapter02.equation_2_9_3` is the displayed formula (2.9.3), the Neumann expansion of
  the resolvent. It is not Theorem 2.9.3: the source uses the number for two different items, and no
  declaration here states the theorem.

## Deviations from the source

* **Definition 2.9.1** (generalization). The source works on a complex Banach space. The definition
  here allows real or complex scalars and any normed space. See
  `AtkinsonHan.Chapter02.definition_2_9_1`.
* **Lemma 2.9.2, equation (2.9.3), and the spectral radius bound** (generalization and reading).
  These statements also apply over the reals. The local estimates use the product form of
  (2.9.1). The perturbation bound explicitly assumes a nonzero space.
* **Continuity of the resolvent** (reading). The text describes continuity on $\mathbb C$ after
  (2.9.2). The local bound has domain $\rho(L)$, where the inverse exists.

## Not formalized

* **The classification of the spectrum** into point, continuous and residual spectrum, a definition
  with no theorem attached to it in the source.
* **Theorem 2.9.3** (the Riesz–Dunford functional calculus). For $f$ analytic on a neighbourhood of
  $\sigma(L)$ the source defines $f_\Gamma(L) = \frac{1}{2\pi i} \oint_\Gamma f(\lambda) (\lambda -
  L)^{-1} \, d\lambda$ (2.9.4) over a contour $\Gamma$ that winds once around $\sigma(L)$ inside the
  domain of analyticity. It states that $f_\Gamma(L) g_\Gamma(L) = (f g)_\Gamma(L)$, and that
  $f_\Gamma(L) = \sum_n a_n L^n$ if $f(\lambda) = \sum_n a_n \lambda^n$ on a disc that contains
  $\sigma(L)$. The source gives no proof and cites Dunford and Schwartz. The theorem needs contour
  integrals of functions with values in $\mathcal{L}(V)$, which Mathlib does not have: its Cauchy
  integral formula is for functions with values in $\mathbb{C}$, and it has no holomorphic
  functional calculus.
* **Theorem 2.9.4** (the Riesz spectral projection). For a compact $L$ and a nonzero eigenvalue
  $\lambda_0$, the operator $E(\lambda_0, L) = \frac{1}{2\pi i} \oint_{|\lambda - \lambda_0| =
  \varepsilon} (\lambda - L)^{-1} \, d\lambda$ (2.9.5), with $\varepsilon$ smaller than the distance
  from $\lambda_0$ to the rest of $\sigma(L)$, is a projection whose range is
  $\mathcal{N}((\lambda_0 - L)^{\nu(\lambda_0)})$, the space of the generalized eigenvectors at the
  index $\nu(\lambda_0)$. The source gives no proof. It needs the same contour integrals as Theorem
  2.9.3; the index and the generalized eigenspaces are in `Numlib.Analysis.Normed.Operator.Riesz`
  and in `AtkinsonHan.Chapter02.theorem_2_8_12_3`.
-/

namespace AtkinsonHan.Chapter02

/-! ### Definition 2.9.1: the resolvent set, the resolvent operator and the spectrum -/

section Resolvent

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 2.9.1(a)** of [han2009theoretical]. Let $L$ be a bounded linear operator on a
normed space $V$ over $\mathbb{K}$. A scalar $\lambda$ is in the **resolvent set** $\rho(L)$ of
$L$ if $(\lambda - L)^{-1}$ exists as a bounded linear operator from $V$ to $V$, that is, if
there is a continuous linear equivalence $e : V \to V$ with $e = \lambda - L$. This inverse is
the **resolvent operator**.

**Generalization.** The source takes a complex Banach space. Here the scalars are real or
complex and $V$ need not be complete.

By `AtkinsonHan.Chapter02.definition_2_9_1_iff` this is Mathlib's `resolventSet`, and by
`AtkinsonHan.Chapter02.definition_2_9_1_resolvent` the resolvent operator is Mathlib's
`resolvent`. -/
def definition_2_9_1 (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (L : V →L[𝕜] V) (lam : 𝕜) : Prop :=
  ∃ e : V ≃L[𝕜] V, (e : V →L[𝕜] V) = lam • (1 : V →L[𝕜] V) - L

/-- **Definition 2.9.1(a)** of [han2009theoretical], identification. A scalar $\lambda$ is in the
resolvent set of $L$ in the sense of Definition 2.9.1 if and only if `lam ∈ resolventSet 𝕜 L`. -/
theorem definition_2_9_1_iff (L : V →L[𝕜] V) (lam : 𝕜) :
    definition_2_9_1 𝕜 L lam ↔ lam ∈ resolventSet 𝕜 L := by
  rw [definition_2_9_1, ← isUnit_iff_exists_continuousLinearEquiv,
    spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]

/-- **Definition 2.9.1(a)** of [han2009theoretical], the resolvent operator. If $\lambda$ is in the
resolvent set of $L$, then `resolvent L lam` is a two-sided inverse of $\lambda - L$:
$$(\lambda - L) R(\lambda) = I, \qquad R(\lambda) (\lambda - L) = I.$$

**Generalization.** These identities also apply to real normed spaces and to incomplete spaces. -/
theorem definition_2_9_1_resolvent (L : V →L[𝕜] V) {lam : 𝕜} (h : definition_2_9_1 𝕜 L lam) :
    (lam • (1 : V →L[𝕜] V) - L) * resolvent L lam = 1 ∧
      resolvent L lam * (lam • (1 : V →L[𝕜] V) - L) = 1 := by
  have hu : IsUnit (algebraMap 𝕜 (V →L[𝕜] V) lam - L) :=
    spectrum.mem_resolventSet_iff.mp ((definition_2_9_1_iff L lam).mp h)
  have hres : resolvent L lam = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam - L) := rfl
  have halg : algebraMap 𝕜 (V →L[𝕜] V) lam = lam • (1 : V →L[𝕜] V) :=
    Algebra.algebraMap_eq_smul_one lam
  rw [hres, ← halg]
  exact ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu⟩

/-- **Definition 2.9.1(b)** of [han2009theoretical]. The **spectrum** $\sigma(L)$ of a bounded
linear operator $L$ on $V$ is the set of the scalars $\lambda$ that are not in the resolvent set
$\rho(L)$.

The source writes $\sigma(L) = \mathbb{C} \setminus \rho(L)$; here the scalars are those of $V$.
By `AtkinsonHan.Chapter02.definition_2_9_1_spectrum_eq` this is Mathlib's `spectrum`.

**Reading.** The spectrum complement is defined for real or complex normed spaces, including
incomplete ones.
-/
def definition_2_9_1_spectrum (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] (L : V →L[𝕜] V) : Set 𝕜 :=
  {lam | ¬ definition_2_9_1 𝕜 L lam}

/-- **Definition 2.9.1(b)** of [han2009theoretical], identification. The spectrum of $L$ in the
sense of Definition 2.9.1 is `spectrum 𝕜 L`. -/
theorem definition_2_9_1_spectrum_eq (L : V →L[𝕜] V) :
    definition_2_9_1_spectrum 𝕜 L = spectrum 𝕜 L := by
  ext lam
  simp only [definition_2_9_1_spectrum, Set.mem_ofPred_eq, definition_2_9_1_iff, spectrum,
    Set.mem_compl_iff]

end Resolvent

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  [Nontrivial V]

/-- **Lemma 2.9.2** of [han2009theoretical], with (2.9.1) and (2.9.2). Let $V$ be a nonzero Banach
space and let $L$ be a bounded linear operator on $V$. Then the resolvent set $\rho(L)$ is open
and the spectrum $\sigma(L)$ is closed. Moreover, if $\lambda_0 \in \rho(L)$ and
$$\|R(\lambda_0)\| \, |\lambda - \lambda_0| < 1,$$
then $\lambda \in \rho(L)$ and
$$\|R(\lambda) - R(\lambda_0)\| \le \frac{\|R(\lambda_0)\|^2 \, |\lambda - \lambda_0|}{1 -
  \|R(\lambda_0)\| \, |\lambda - \lambda_0|}.$$

$R(\lambda)$ is `resolvent L lam`. The hypothesis that $V$ is nonzero is `[Nontrivial V]`; see
the module doc comment.

**Reading.** The estimate controls the inverse on the resolvent set. It is stated over real
or complex scalars and assumes that the space is nonzero. -/
theorem lemma_2_9_2 (L : V →L[𝕜] V) :
    IsOpen (resolventSet 𝕜 L) ∧ IsClosed (spectrum 𝕜 L) ∧
      ∀ lam₀ ∈ resolventSet 𝕜 L, ∀ lam : 𝕜,
        ‖resolvent L lam₀‖ * ‖lam - lam₀‖ < 1 →
          lam ∈ resolventSet 𝕜 L ∧
            ‖resolvent L lam - resolvent L lam₀‖ ≤
              ‖resolvent L lam₀‖ ^ 2 * ‖lam - lam₀‖ /
                (1 - ‖resolvent L lam₀‖ * ‖lam - lam₀‖) := by
  refine ⟨spectrum.isOpen_resolventSet L, spectrum.isClosed L, fun lam₀ h₀ lam hlt => ?_⟩
  obtain ⟨x, hxval⟩ := spectrum.mem_resolventSet_iff.mp h₀
  have hxinv : resolvent L lam₀ = ((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V) := by
    rw [show resolvent L lam₀ = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) from rfl,
      ← hxval, Ring.inverse_unit]
  have htnorm : ‖algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)‖ = ‖lam - lam₀‖ :=
    norm_algebraMap' (V →L[𝕜] V) _
  have hpos : 0 < ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ := Units.norm_pos x⁻¹
  rw [hxinv] at hlt ⊢
  have hlt' : ‖algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)‖ <
      ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖⁻¹ := by
    rw [htnorm]
    refine lt_of_not_ge fun hc => absurd hlt (not_lt.mpr ?_)
    calc (1 : ℝ) = ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖⁻¹ *
            ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ ‖((x⁻¹ : (V →L[𝕜] V)ˣ) : V →L[𝕜] V)‖ * ‖lam - lam₀‖ := by rw [mul_comm]; gcongr
  have hsum : (x : V →L[𝕜] V) + algebraMap 𝕜 (V →L[𝕜] V) (lam - lam₀)
      = algebraMap 𝕜 (V →L[𝕜] V) lam - L := by
    rw [hxval, map_sub]
    abel
  have hunit : IsUnit (algebraMap 𝕜 (V →L[𝕜] V) lam - L) := by
    rw [← hsum]
    exact Units.isUnit_add_of_norm_lt x _ hlt'
  refine ⟨spectrum.mem_resolventSet_iff.mpr hunit, ?_⟩
  have hbound := Units.norm_inverse_add_sub_le x _ hlt'
  rw [hsum, htnorm] at hbound
  exact hbound

omit [Nontrivial V] in
/-- **Equation (2.9.3)** of [han2009theoretical]. Let $V$ be a Banach space, let $L$ be a bounded
linear operator on $V$ and let $\lambda_0 \in \rho(L)$. If
$\|R(\lambda_0)\| \, |\lambda - \lambda_0| < 1$, then
$$R(\lambda) = \sum_{k=0}^\infty (-1)^k (\lambda - \lambda_0)^k R(\lambda_0)^{k+1},$$
with the series convergent in $\mathcal{L}(V)$.

The series is the Taylor expansion of $R$ at $\lambda_0$. The sum is Mathlib's `HasSum`.

**Generalization.** The expansion also holds over the reals. -/
theorem equation_2_9_3 (L : V →L[𝕜] V) {lam₀ : 𝕜} (h₀ : lam₀ ∈ resolventSet 𝕜 L) (lam : 𝕜)
    (hlt : ‖resolvent L lam₀‖ * ‖lam - lam₀‖ < 1) :
    HasSum (fun k : ℕ =>
        ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • resolvent L lam₀ ^ (k + 1)) (resolvent L lam) := by
  set S := resolvent L lam₀ with hS
  set T := -((lam - lam₀) • S) with hT
  have hTnorm : ‖T‖ < 1 := by
    rw [hT, norm_neg, norm_smul]
    calc ‖lam - lam₀‖ * ‖S‖ = ‖S‖ * ‖lam - lam₀‖ := mul_comm _ _
      _ < 1 := hlt
  have hxS : (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) * S = 1 :=
    Ring.mul_inverse_cancel _ (spectrum.mem_resolventSet_iff.mp h₀)
  have hfac : algebraMap 𝕜 (V →L[𝕜] V) lam - L = (algebraMap 𝕜 (V →L[𝕜] V) lam₀ - L) * (1 - T) := by
    rw [hT, sub_neg_eq_add, mul_add, mul_one, mul_smul_comm, hxS, ← Algebra.algebraMap_eq_smul_one,
      map_sub]
    abel
  have hone : IsUnit (1 - T) := isUnit_one_sub_of_norm_lt_one hTnorm
  -- The resolvent at `lam` factors as `(1 - T)⁻¹ R(λ₀)`.
  have hres : resolvent L lam = Ring.inverse (1 - T) * S := by
    have hz : IsUnit (algebraMap 𝕜 (V →L[𝕜] V) lam - L) := by
      rw [hfac]
      exact (spectrum.mem_resolventSet_iff.mp h₀).mul hone
    have hzy : (algebraMap 𝕜 (V →L[𝕜] V) lam - L) * (Ring.inverse (1 - T) * S) = 1 := by
      rw [hfac, mul_assoc, ← mul_assoc (1 - T), Ring.mul_inverse_cancel _ hone, one_mul, hxS]
    calc resolvent L lam
        = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam - L) * 1 := by rw [mul_one]; rfl
      _ = Ring.inverse (algebraMap 𝕜 (V →L[𝕜] V) lam - L) *
            ((algebraMap 𝕜 (V →L[𝕜] V) lam - L) * (Ring.inverse (1 - T) * S)) := by rw [hzy]
      _ = Ring.inverse (1 - T) * S := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hz, one_mul]
  rw [hres]
  have heq : (fun k : ℕ => ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • S ^ (k + 1))
      = fun k : ℕ => T ^ k * S := by
    funext k
    calc ((-1 : 𝕜) ^ k * (lam - lam₀) ^ k) • S ^ (k + 1)
        = ((-1 : 𝕜) * (lam - lam₀)) ^ k • (S ^ k * S) := by rw [mul_pow, pow_succ]
      _ = ((-(lam - lam₀)) ^ k • S ^ k) * S := by rw [neg_one_mul, ← smul_mul_assoc]
      _ = T ^ k * S := by rw [hT, ← neg_smul, smul_pow]
  rw [heq]
  exact (hasSum_geom_series_inverse T hTnorm).mul_right S

/-- **Section 2.9** of [han2009theoretical], the remark before Definition 2.9.1. Let $V$ be a
nonzero Banach space and let $L$ be a bounded linear operator on $V$. Then every $\lambda$ with
$|\lambda| > \|L\|$ is in the resolvent set $\rho(L)$, and the spectrum lies in the closed disc
$$\sigma(L) \subseteq \{\lambda : |\lambda| \le \|L\|\}.$$
So the resolvent is defined near infinity, which §2.9 and Chapter 6 use.

**Generalization.** The radius bound also holds over the reals. -/
theorem spectrum_subset_closedBall (L : V →L[𝕜] V) :
    {lam : 𝕜 | ‖L‖ < ‖lam‖} ⊆ resolventSet 𝕜 L ∧
      spectrum 𝕜 L ⊆ Metric.closedBall (0 : 𝕜) ‖L‖ :=
  ⟨fun _ h => spectrum.mem_resolventSet_of_norm_lt h, spectrum.subset_closedBall_norm L⟩

end AtkinsonHan.Chapter02
